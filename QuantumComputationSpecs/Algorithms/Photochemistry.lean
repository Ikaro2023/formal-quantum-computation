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

public import QuantumComputation.Algorithms.QFT.Operators
public import QuantumComputationSpecs.Algorithms.StoppingPower

/-!
# Photochemistry: Photoactivated Double Proton-Coupled Electron Transfer

Specification of `1 fs` of time evolution under the pre-Born–Oppenheimer molecular Hamiltonian of
Pocrnic et al. (arXiv:2602.11272v1) for its reaction 5, C₂₃H₂₀N₃O: `η = 234` particles (`47`
nuclei and `187` electrons) on a first-quantized real-space grid with `n_g = 8` qubits per
Cartesian coordinate, in a box of width `L = 44 Å` (paper Eqs. 2–10 and 23–25, Tables I and IV,
atomic units). The specification costs the time evolution, not an estimate of an observable such
as a proton-transfer yield. The photoexcited initial state is arbitrary; its preparation, which the
paper expects to be subdominant and leaves to future work (Sec. V), is not costed:

* `photochemistry_correctness`: the program acts on the system register with clean ancillas
  as `e^{-iHt}`, `t = 1 fs`, up to a global phase, within spectral-norm error `0.01`.
* `photochemistry_const_cost`: the program is over Clifford + `T` with measurements, and its
  spacetime volume (qubits × `T` count) is at most `photochemistryConstCost`. It has no `TOFF`
  gates, so each Toffoli is built from Clifford + `T` gates and the correctness proof covers that
  construction.

Two baselines, both for the paper's qubitization with generalized QSP at block-encoding error
`ε = 10^-2` on `6198` qubits (Table I), which `photochemistry_correctness` implies. Both charge `4`
`T` gates per Toffoli, the Toffoli of Jones (2013) from `4` `T` gates, an ancilla, a measurement
and a classically controlled `CZ`.
* Paper: `2.73 × 10^11` Toffolis (`1.09 × 10^12` `T` gates), spacetime `6.77 × 10^15` (Table I).
* QSP-rescaled: `2.01 × 10^11` Toffolis (`8.04 × 10^11` `T` gates), spacetime `4.98 × 10^15`,
  rescaling the `1.21 × 10^7` walk steps of Eq. C4 to `8.93 × 10^6` via the Jacobi–Anger degree
  bound of Pocrnic and Motlagh (2026, Theorem 2) at `ε_exp = ε / 12.95` (Table IV).

References:
* M. Pocrnic, I. Loaiza, J. M. Arrazola, N. Wiebe, D. Motlagh, *Efficient Simulation of
  Pre-Born-Oppenheimer Dynamics on a Quantum Computer*, https://arxiv.org/abs/2602.11272 (2026).
* M. Pocrnic, D. Motlagh, *Improved constant factors for qubitized Hamiltonian simulation*,
  https://arxiv.org/abs/2608.02734 (2026).
* C. Jones, *Low-overhead constructions for the fault-tolerant Toffoli gate*, Phys. Rev. A 87,
  022328 (2013).
* B. Şahinoğlu, R. D. Somma, *Hamiltonian simulation in the low-energy subspace*, npj Quantum Inf.
  7, 119 (2021), https://arxiv.org/abs/2006.02660.
* P. J. Mohr, D. B. Newell, B. N. Taylor, E. Tiesinga, *CODATA recommended values of the
  fundamental physical constants: 2022*, Rev. Mod. Phys. 97, 025002 (2025).
* M. Wang, W. J. Huang, F. G. Kondev, G. Audi, S. Naimi, *The AME 2020 atomic mass evaluation
  (II). Tables, graphs and references*, Chinese Phys. C 45, 030003 (2021).
-/

@[expose] public section

namespace QuantumComputation.Specs

open Operator
open scoped Matrix Real

/-! ## C₂₃H₂₀N₃O Instance -/

namespace Photochemistry

/-- Qubits per Cartesian coordinate, `n_g` (paper Table IV). -/
abbrev gridBits : ℕ := 8

/-- The `η = 234` particles: the nuclei `0–46`, then the electrons (the paper's order, Fig. 8). -/
abbrev Particle := Fin 234

/-- Width `3 η n_g = 5616` of the system register. -/
abbrev systemQubits : ℕ := 3 * 234 * gridBits

/-- Box width `L = 44 Å` (paper Table IV) in Bohr radii, with `a₀ = 0.529177210544 Å`
(CODATA 2022). -/
noncomputable abbrev boxWidth : ℝ := 44 / 0.529177210544

/-- Grid spacing `Δ = L / (2^{n_g} - 1)` (paper Eq. 5). -/
noncomputable abbrev gridSpacing : ℝ := boxWidth / (2 ^ gridBits - 1)

/-- Evolution time `t = 1 fs` in units of `ħ / E_h = 2.4188843265864 × 10⁻¹⁷ s` (CODATA 2022). -/
noncomputable abbrev evolutionTime : ℝ := 100 / 2.4188843265864

/-- Atomic number of nucleus `i < 47`: nuclei `0–22` are C, `23–42` H, `43–45` N and `46` O. -/
def atomicNumber (i : Particle) : ℕ :=
  if i < 23 then 6 else if i < 43 then 1 else if i < 46 then 7 else 8

/-- Signed charge `(-1)^{σ_i} ζ_i`: `Z` for a nucleus, `-1` for an electron (paper Eqs. 2–3). -/
def charge (i : Particle) : ℤ := if i < 47 then atomicNumber i else -1

/-- AME2020 atomic mass, in daltons, of the most abundant isotope with atomic number
`Z = 1, 6, 7, 8`: ¹H, ¹²C, ¹⁴N, ¹⁶O. -/
noncomputable def atomicMass : ℕ → ℝ
  | 1 => 1.007825031898
  | 6 => 12
  | 7 => 14.00307400425
  | _ => 15.99491461926

/-- Mass `m_i` in units of `m_e`: `1` for an electron; for a nucleus, the atomic mass over
`m_e = 5.485799090441 × 10⁻⁴ u` (CODATA 2022) less `Z` electrons. Electron binding energies,
below `2 × 10⁻⁷` of the mass, are neglected. -/
noncomputable def mass (i : Particle) : ℝ :=
  if i < 47 then atomicMass (atomicNumber i) / 5.485799090441e-4 - atomicNumber i else 1

/-- Register of coordinate `w` of particle `i`: three consecutive `n_g`-qubit registers per
particle, in particle order. -/
def coordinateRegister (i : Particle) (w : Fin 3) : QRegister gridBits systemQubits :=
  .block (gridBits * (3 * i + w)) gridBits (by unfold systemQubits gridBits; omega)

/-- Two's-complement value in `[-2^{n_g-1}, 2^{n_g-1} - 1]` of an `n_g`-qubit basis index
(paper Eq. 4). -/
def twosComplement (k : Fin (2 ^ gridBits)) : ℤ := (k.val : ℤ).bmod (2 ^ gridBits)

/-- Grid position `q_w` of particle `i` in basis state `x`, at `r = q Δ` (paper Eq. 6). -/
def position (x : Fin (2 ^ systemQubits)) (i : Particle) (w : Fin 3) : ℤ :=
  twosComplement ((coordinateRegister i w).extractIndex x)

/-- Kinetic energy `T = (2π² / L²) Σ_i Σ_q (‖q‖² / m_i) QFT_i† |q⟩⟨q|_i QFT_i` (paper Eq. 10).
`QFT_i` is the QFT on each coordinate register of particle `i` and `‖q‖² = Σ_w q_w²`, so `T` is a
sum of terms on single coordinate registers. -/
noncomputable def kineticEnergy : Operator (2 ^ systemQubits) :=
  let F := QFT.qftMatrix gridBits
  ∑ i, ∑ w, ((2 * π ^ 2 / (boxWidth ^ 2 * mass i) : ℝ) : ℂ) •
    (coordinateRegister i w).embedMatrix
      (Fᴴ * Matrix.diagonal (fun k ↦ (twosComplement k ^ 2 : ℂ)) * F)

/-- Squared saturation distance in units of `Δ²`: `Γ̃² = 2^{n_Γ} = 8` (`n_Γ = 3`, paper Table IV and
Eq. E7) for a nucleus–nucleus pair, `1` otherwise. -/
def saturationSq (i j : Particle) : ℕ := if i < 47 ∧ j < 47 then 8 else 1

/-- Potential energy `Σ_{i ≠ j} c_i c_j / (2 max(r_ij, Γ̃_ij Δ))`, diagonal in the position basis,
with `r_ij = Δ ‖q_i - q_j‖` and `Γ̃_ij² = saturationSq i j`: Coulomb terms capped at `1 / Δ`
(paper Eqs. 8–9) and nucleus–nucleus terms at `1 / (Γ̃ Δ)` (Sec. III A 1, Eqs. 23–25). -/
noncomputable def potentialEnergy : Operator (2 ^ systemQubits) :=
  Matrix.diagonal fun x ↦ ∑ i, ∑ j, if i = j then 0 else
    (charge i * charge j / (2 * gridSpacing *
      √((max (∑ w, (position x i w - position x j w) ^ 2) (saturationSq i j) : ℤ) : ℝ)) : ℝ)

/-- The Hamiltonian `H = T + V` (paper Eq. 2, discretized as in Eqs. 8–10 and 23–25). -/
noncomputable def hamiltonian : Operator (2 ^ systemQubits) := kineticEnergy + potentialEnergy

end Photochemistry

open Photochemistry

/-! ## Candidate Program & Correctness / Cost Theorems -/

/-- By default we allow only a single variable. -/
inductive Photochemistry.Var where | v deriving DecidableEq, Inhabited

open Photochemistry (Var)
open Photochemistry.Var (v)

/-- Number of clean ancilla qubits `photochemistryProgram` uses. -/
def photochemistryAncillas : ℕ := sorry

/-- Circuit for `e^{-iHt}`, `t = 1 fs`, on system wires `rSys` and clean ancilla wires `rAnc`. -/
noncomputable def photochemistryProgram {n : ℕ} (rSys : QRegister systemQubits n)
    (rAnc : QRegister photochemistryAncillas n) : DynamicCircuit Var n :=
  sorry

/-- `photochemistryProgram` realizes a unitary that maps every `|Ψ₀⟩ ⊗ |0⟩` to within
Euclidean distance `ε = 0.01` of `e^{-iHt} |Ψ₀⟩ ⊗ |0⟩`, `t = 1 fs`, up to a global phase. This
implies the paper's requirement, a block encoding of `e^{-iHt}` within `ε = 10^-2` (Table IV).
The bound holds on every input state (`P = 1`), as does the paper's operator-norm guarantee
(Theorems 1–2); it is not restricted to antisymmetric states or to a low-energy subspace, on which
product-formula error can depend on an effective low-energy norm instead of `‖H‖` (Şahinoğlu and
Somma 2021). With no catalyst, phase-gradient states are prepared within the run, and a single
unitary `W` excludes randomized compilers such as qDRIFT. -/
theorem photochemistry_correctness {n : ℕ}
    (rSys : QRegister systemQubits n) (rAnc : QRegister photochemistryAncillas n)
    (hdisj : rSys.DisjointWires rAnc) :
    ∃ W, ApproximatesTimeEvolution hamiltonian evolutionTime 0.01 1 W ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W
        (photochemistryProgram rSys rAnc).compile := by sorry

/-- Claimed spacetime volume of `1 fs` of evolution. -/
def photochemistryConstCost : ℕ := sorry

/-- Over Clifford + `T` with measurements, the spacetime volume (qubits times `T` count) of `1 fs`
of evolution is at most `photochemistryConstCost`. `TOFF` gates are excluded, so each Toffoli is
costed by the Clifford + `T` construction the program uses, such as `4` `T` gates with an ancilla
and a measurement; measurements cost `0` and a `qIf` costs its worse branch. -/
theorem photochemistry_const_cost {n : ℕ} (rSys : QRegister systemQubits n)
    (rAnc : QRegister photochemistryAncillas n) :
    (photochemistryProgram rSys rAnc).count PrimitiveGate.TOFF = 0 ∧
      (systemQubits + photochemistryAncillas) *
          (photochemistryProgram rSys rAnc).count PrimitiveGate.T ≤
        photochemistryConstCost := by sorry

end QuantumComputation.Specs
