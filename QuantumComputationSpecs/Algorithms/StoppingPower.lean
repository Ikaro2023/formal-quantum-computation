/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stopping Power: First-Quantized Electron–Projectile Dynamics

Specification of the time evolution in the stopping-power protocol of Rubin et al. (PNAS 2024)
for its α + hydrogen system: `η = 218` electrons and an α-particle projectile in a periodic cell
of volume `Ω = 2419.68282 a₀³` holding `216` classical protons, in the first-quantized plane-wave
representation (PNAS Eqs. 1–7 and Tables 1–3, atomic units).

The protocol prepares a Slater determinant and a projectile wave packet, evolves for time `t` and
measures the projectile momentum, `N_s = 50` times at each of `t = 1, …, 10` a.u. State
preparation is a negligible additive cost (arXiv:2308.12352v1, Sec. II B), so the specification
costs the time evolutions; it does not target an estimate of the stopping power to a given
relative accuracy.

* `stoppingPower_correctness`: for every `Configuration` and spin assignment, the program for time
  `t` acts on fermionic grid states with clean ancillas as `e^{-iHt}` up to a global phase, within
  spectral-norm error `0.01`.
* `stoppingPower_const_cost`: the program is over Clifford + `T` with measurements, and the
  spacetime volume (qubits × `T` count) of the `50 × 10` runs is at most `stoppingPowerConstCost`.
  It has no `TOFF` gates, so each Toffoli is built from Clifford + `T` gates and the correctness
  proof covers that construction.

Baseline (QSP, PNAS Eq. 12 with Table 2), charging `4` `T` gates per Toffoli, the Toffoli of
Jones (2013) from `4` `T` gates, an ancilla, a measurement and a classically controlled `CZ`:
`1.199 × 10^14` Toffolis, so `4.795 × 10^14` `T` gates, on `5650` qubits, spacetime
`2.709 × 10^18`.

References:
* N. C. Rubin et al., *Quantum computation of stopping power for inertial fusion target design*,
  PNAS 121(23), e2317772121 (2024), https://arxiv.org/abs/2308.12352.
* Y. Su et al., *Fault-Tolerant Quantum Simulations of Chemistry in First Quantization*,
  PRX Quantum 2, 040332 (2021), https://arxiv.org/abs/2105.12767.
* C. Jones, *Low-overhead constructions for the fault-tolerant Toffoli gate*, Phys. Rev. A 87,
  022328 (2013).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator
open scoped Real

open scoped Matrix.Norms.L2Operator in
/-- `W` acts on the range of the operator `P` (a projector here) with clean ancillas as `e^{-iHt}`,
up to a global phase, within spectral-norm error `ε`; in particular it returns the ancillas to
`|0⟩` within `ε`. -/
def ApproximatesTimeEvolution {k m : ℕ} (H : Operator (2 ^ k)) (t ε : ℝ) (P : Operator (2 ^ k))
    (W : Unitary (2 ^ (k + m))) : Prop :=
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  let target := sys.embedMatrix (NormedSpace.exp ((-Complex.I * t) • H))
  let input := sys.embedMatrix P * anc.basisOutcomeProjector 0
  ∃ φ : ℝ, ‖(W.1 - Complex.exp (φ * Complex.I) • target) * input‖ ≤ ε

/-! ## α + Hydrogen Instance -/

namespace StoppingPower

/-- Number of electrons `η` (PNAS Table 1). -/
abbrev numElectrons : ℕ := 218

/-- Qubits per electron momentum component, `n_p` (PNAS Table 1). -/
abbrev electronBits : ℕ := 6

/-- Qubits per projectile momentum component, `n_n` (PNAS Table 2). -/
abbrev projectileBits : ℕ := 8

/-- Width `3 (η n_p + n_n) = 3948` of the system register. -/
abbrev systemQubits : ℕ := 3 * (numElectrons * electronBits + projectileBits)

/-- Cell volume `Ω` in `a₀³` (PNAS Table 1). -/
noncomputable abbrev cellVolume : ℝ := 2419.68282

/-- α-particle mass `m_α / m_e` (CODATA 2022; PNAS Table 2 gives `3.9726` proton masses). -/
noncomputable abbrev projectileMass : ℝ := 7294.29954171

/-- A quantum particle: one of the `η` electrons or the α projectile. -/
inductive Particle where
  | electron (i : Fin numElectrons)
  | projectile
  deriving DecidableEq, Fintype

/-- Qubits per momentum component of a particle. -/
def componentBits : Particle → ℕ
  | .electron _ => electronBits
  | .projectile => projectileBits

/-- Charge in units of `e`: `-1` for electrons, `ζ_proj = 2` for the α particle. -/
def charge : Particle → ℤ
  | .electron _ => -1
  | .projectile => 2

/-- First qubit of the field holding momentum component `w` of a particle: three consecutive
fields per electron, in order, followed by the three projectile fields (as in Su et al., Eq. 28). -/
def bitOffset : Particle → Fin 3 → ℕ
  | .electron i, w => electronBits * (3 * i.val + w.val)
  | .projectile, w => 3 * electronBits * numElectrons + projectileBits * w.val

/-- Sign bit and magnitude of momentum component `w` of particle `a` in basis state `x`: the
little-endian field of `componentBits a` qubits at `bitOffset a w` holds a signed integer with the
sign in its top qubit (Su et al., Eq. 29). -/
def signMagnitude (x : Fin (2 ^ systemQubits)) (a : Particle) (w : Fin 3) : ℕ × ℕ :=
  let f := x.val / 2 ^ bitOffset a w
  (f / 2 ^ (componentBits a - 1) % 2, f % 2 ^ (componentBits a - 1))

/-- Integer momentum component `p_{a,w}` of basis state `x`. -/
def momentum (x : Fin (2 ^ systemQubits)) (a : Particle) (w : Fin 3) : ℤ :=
  (-1) ^ (signMagnitude x a w).1 * ((signMagnitude x a w).2 : ℤ)

/-- `x` has no negative zero. The momenta of such states fill the grids `G = [-31, 31]³` and
`G̃ = [-127, 127]³` of `n_p`- and `n_n`-bit signed integers (`N^{1/3} = 2^{n_p} - 1`, Su et al.,
after Eq. 28); PNAS Table 1's `N^{1/3} = 53` is the classical TDDFT grid that `n_p = 6` covers. -/
def IsGridState (x : Fin (2 ^ systemQubits)) : Prop :=
  ∀ a w, signMagnitude x a w ≠ (1, 0)

open Classical in
/-- The grid states, as the `Finset` of valid inputs. -/
noncomputable def gridStates : Finset (Fin (2 ^ systemQubits)) :=
  {x | IsGridState x}

open Classical in
/-- Projector `|S|⁻¹ Σ_{g ∈ S} sgn(g) g` onto grid states antisymmetric under exchange of
same-spin electrons, where `S` is the group of electron permutations preserving the spin-up
registers `spinUp`, acting on electron momenta, and `|S| = |spinUp|! (η - |spinUp|)!`. Over all
`spinUp`, these states represent the `η`-electron fermionic sector. -/
noncomputable def fermionicProjector (spinUp : Finset (Fin numElectrons)) :
    Operator (2 ^ systemQubits) :=
  Matrix.of fun x y ↦
    if IsGridState x ∧ IsGridState y then
      (∑ g : Equiv.Perm (Fin numElectrons), if (∀ i, g i ∈ spinUp ↔ i ∈ spinUp) ∧
          momentum x .projectile = momentum y .projectile ∧
          ∀ i, momentum x (.electron i) = momentum y (.electron (g i)) then
        ((Equiv.Perm.sign g : ℤ) : ℂ) else 0) /
        ((spinUp.card.factorial * (numElectrons - spinUp.card).factorial : ℕ) : ℂ)
    else 0

/-- Plane-wave wavevector `k_ν = 2π ν / Ω^{1/3}`. -/
noncomputable def waveVector (ν : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun w ↦ 2 * π * ν w / cellVolume ^ (1 / 3 : ℝ)

/-- Squared wavenumber `‖k_ν‖²`. -/
noncomputable def waveNumberSq (ν : Fin 3 → ℤ) : ℝ :=
  waveVector ν ⬝ᵥ waveVector ν

/-- Classical inputs: host-proton positions, and the frame offset `k_proj = k_P` of the projectile
register (PNAS Eq. 3), with `P ∈ ℤ³` for compatibility with the periodic cell. -/
structure Configuration where
  /-- Positions `R_ℓ` of the `216 = η - ζ_proj` host protons, which make the cell neutral and match
  the paper's hydrogen density `1 g/cm³` in volume `Ω` to 1%. -/
  nuclei : Fin 216 → Fin 3 → ℝ
  /-- Integer label `P` of the projectile frame offset. -/
  projectileMomentum : Fin 3 → ℤ
  /-- `‖k_proj‖ ≤ 29376`, PNAS Table 2's `k_proj` (`M ≈ 4 m_p` at `v = 4` a.u.). -/
  momentum_le : waveNumberSq projectileMomentum ≤ 29376 ^ 2

/-- Coulomb kernel `4π / (Ω ‖k_ν‖²)`. It vanishes at `ν = 0` (as `x / 0 = 0`), which drops the
`ν = 0` term. -/
noncomputable def coulombKernel (ν : Fin 3 → ℤ) : ℝ :=
  4 * π / (cellVolume * waveNumberSq ν)

/-- Structure factor `Σ_ℓ e^{-i k_ν · R_ℓ}` of the host protons. -/
noncomputable def structureFactor (c : Configuration) (ν : Fin 3 → ℤ) : ℂ :=
  ∑ l, Complex.exp (-(waveVector ν ⬝ᵥ c.nuclei l) * Complex.I)

/-- Kinetic energy `Σᵢ ‖k_{pᵢ}‖² / 2 + ‖k_{p_proj} - k_proj‖² / (2 m_α)` (PNAS Eqs. 2–3). -/
noncomputable def kineticEnergy (c : Configuration) (p : Particle → Fin 3 → ℤ) : ℝ :=
  ∑ i, waveNumberSq (p (.electron i)) / 2 +
    waveNumberSq (p .projectile - c.projectileMomentum) / (2 * projectileMass)

open Classical in
/-- The Hamiltonian `T_elec + T_proj + U_elec + U_proj + V_elec + V_proj` of PNAS Eqs. 1–7 on grid
states, zero elsewhere. With `p = momentum x`, `q = momentum y` and `ν = p a - q a`: kinetic energy
on the diagonal; `ζ_a S(ν) K(ν)` if `x`, `y` differ only in particle `a` (`U`); `ζ_a ζ_b K(ν) / 2`
per ordered pair `a ≠ b` if they differ only in `a`, `b` with `p a + p b = q a + q b` (`V`). -/
noncomputable def hamiltonian (c : Configuration) : Operator (2 ^ systemQubits) :=
  Matrix.of fun x y ↦
    if IsGridState x ∧ IsGridState y then
      let p := momentum x
      let q := momentum y
      (if x = y then (kineticEnergy c p : ℂ) else 0) +
        (∑ a, if ∀ b ≠ a, p b = q b then
          charge a * structureFactor c (p a - q a) * coulombKernel (p a - q a) else 0) +
        ∑ a, ∑ b, if a ≠ b ∧ (∀ d, d ≠ a → d ≠ b → p d = q d) ∧ p a + p b = q a + q b then
          charge a * charge b * coulombKernel (p a - q a) / 2 else 0
    else 0

end StoppingPower

open StoppingPower

/-! ## Candidate Program & Correctness / Cost Theorems -/

/-- By default we allow only a single variable. -/
inductive StoppingPower.Var where | v deriving DecidableEq, Inhabited

open StoppingPower (Var)
open StoppingPower.Var (v)

/-- Number of clean ancilla qubits `stoppingPowerProgram` uses. -/
def stoppingPowerAncillas : ℕ := sorry

/-- Circuit for `e^{-iHt}` at `t = j + 1` a.u. and configuration `c`, on system wires `rSys` and
clean ancilla wires `rAnc`. -/
noncomputable def stoppingPowerProgram {n : ℕ} (c : Configuration) (j : Fin 10)
    (rSys : QRegister systemQubits n) (rAnc : QRegister stoppingPowerAncillas n) :
    DynamicCircuit Var n :=
  sorry

/-- For every configuration, time `t = j + 1 ∈ {1, …, 10}` a.u. and spin assignment `spinUp`,
`stoppingPowerProgram` realizes a unitary that acts on fermionic grid states with clean ancillas as
`e^{-iHt}`, up to a global phase, within error `ε = 0.01` (PNAS Table 3).

`ε` is read in spectral norm, which is stricter than the infidelity of Table 3. In the paper it is
the error of the QSP propagator (PNAS Eq. 12), bounded on the whole register; the product-formula
analogue (PNAS Eqs. 28–29) bounds it on the fixed-particle sector. With no catalyst, phase-gradient
states are prepared within each run, and a single unitary `W` excludes randomized compilers such as
qDRIFT. -/
theorem stoppingPower_correctness {n : ℕ}
    (c : Configuration) (j : Fin 10)
    (rSys : QRegister systemQubits n) (rAnc : QRegister stoppingPowerAncillas n)
    (hdisj : rSys.DisjointWires rAnc) :
    ∃ W, (∀ spinUp, ApproximatesTimeEvolution (hamiltonian c) (j.val + 1 : ℝ) 0.01
        (fermionicProjector spinUp) W) ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys gridStates rAnc hdisj W
        (stoppingPowerProgram c j rSys rAnc).compile := by sorry

/-- Claimed spacetime volume of the protocol. -/
def stoppingPowerConstCost : ℕ := sorry

/-- Over Clifford + `T` with measurements, the spacetime volume of the protocol (qubits times the
`T` count of `N_s = 50` runs at each of the ten times, PNAS Table 3) is at most
`stoppingPowerConstCost`. `TOFF` gates are excluded, so each Toffoli is costed by the
Clifford + `T` construction the program uses, such as `4` `T` gates with an ancilla and a
measurement; measurements cost `0` and a `qIf` costs its worse branch. -/
theorem stoppingPower_const_cost {n : ℕ} (c : Configuration)
    (rSys : QRegister systemQubits n) (rAnc : QRegister stoppingPowerAncillas n) :
    (∀ j, (stoppingPowerProgram c j rSys rAnc).count PrimitiveGate.TOFF = 0) ∧
      (systemQubits + stoppingPowerAncillas) *
          (50 * ∑ j, (stoppingPowerProgram c j rSys rAnc).count PrimitiveGate.T) ≤
        stoppingPowerConstCost := by sorry

end QuantumComputation.Specs
