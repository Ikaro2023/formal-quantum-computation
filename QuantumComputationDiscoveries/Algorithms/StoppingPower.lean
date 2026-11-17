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
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Gf8Code18Guard
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosMomKrylovPres
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GuardMasterWaist
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.TightCoins135598
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SkewRank2PauliCap
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Bell18StageABrg
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.StageBOneWireOpen
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SharedBank114Tw
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80BhmtCert
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot1Pwu24Stitch
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Bell18StreamOff

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

open QuantumComputation.Specs.StoppingPowerSolution
attribute [-instance]
  instFactOneLtTwoCompat
  SpecsAux.PhaseGradCatalystCore.instHPowComplexRealCompat
  ModWrapCoarse8PureMomentum.modWrapNeZeroPow2
  PosSlots24BranchConcrete.instNeZeroTwoPow
  PosSlots24PartnerMux288.instNeZeroTwoPowPartnerMux
  DyadicQft64WalkCircuit288.instNeZeroTwoPowQft288
  HoistedSwapSelectBridge.instNeZeroTwoPowHoisted
  PosSlots24CompactHead123.instNeZeroTwoPowHead123
  PosSlots24CompactPhase288.instNeZeroTwoPowMid254
  SinglePassNuclearTwist288.instNeZeroTwoPowSinglePass
  MomSlots35Slot3ProjNuclear.instNeZeroTwoPowSlot3
  ZeroAncillaUSP.instNeZeroTwoPowUSP
  PosSlots24PartnerMuxZeroT123.instNeZeroTwoPowZeroT123
  PosSlots24PartnerMuxZeroT123.instNeZeroTwoPowPartnerMuxZeroT
  BiGqspSegmentSpine.instNeZeroTwoPowSpine
  OraAndPrepBundle.instNeZeroTwoPowOra
  CoinDispatchedBarrel288.instNeZeroTwoPowCoinBarrel
  CoinDispatchedBarrel288.instNeZeroCorePlusBarrel
  FullSysHoistedSelectStitch.instNeZeroTwoPowHoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow48HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow3948HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow3951HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4031HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4034HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4066HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4067HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4109HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4112HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4121HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4144HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4145HoistedStitch
  FullSysHoistedSelectStitch.instNeZeroTwoPow4199HoistedStitch
  SegmentAndTopClosure.instNeZeroTwoPowClosure
  PolymorphicTopClosure.instNeZeroTwoPowPolyClosure
  GeneralBetaAndAlphaTopEndpoint.instNeZeroTwoPowGeneral
  ProjZ512QftAndTwist288.instNeZeroTwoPowVepClosure
  ProjZ512QftAndTwist288.instNeZeroTwoPowVepTop
  CoherentEndpoint.instNeZeroTwoPowCoherent80
  PosPostPrep80MergedVep.instNeZeroTwoPowPosPost80
  PosSlots24Semantic80Physics.instNeZeroTwoPowSem80
  WindowedSlot2MulKick288.instNeZeroTwoPowWin
  PosHeadRev18CacheAux.instNeZeroTwoPowHeadRev18
  PosHeadMod4_15476.instNeZeroTwoPowHeadMod4

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

section Bridge
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
set_option exponentiation.threshold 8192

/-- Equivalence between `Specs.StoppingPower.Particle` and
  `StoppingPowerSolution.SpecMirror.Particle`. -/
def particleEquiv :
    StoppingPower.Particle ≃ StoppingPowerSolution.SpecsAux.SpecMirror.Particle where
  toFun
    | .electron i => .electron i
    | .projectile => .projectile
  invFun
    | .electron i => .electron i
    | .projectile => .projectile
  left_inv a := by
    match a with
    | .electron _ => rfl
    | .projectile => rfl
  right_inv a := by
    match a with
    | .electron _ => rfl
    | .projectile => rfl

/-- Translates `Specs.StoppingPower.Configuration` to
  `StoppingPowerSolution.SpecMirror.Configuration`. -/
def toCopyCfg (c : StoppingPower.Configuration) :
    StoppingPowerSolution.SpecsAux.SpecMirror.Configuration :=
  ⟨c.nuclei, c.projectileMomentum, c.momentum_le⟩

@[simp] theorem componentBits_copy_apply (a : StoppingPower.Particle) :
    StoppingPowerSolution.SpecsAux.SpecMirror.componentBits (particleEquiv a) =
      StoppingPower.componentBits a := by
  match a with
  | .electron _ => rfl
  | .projectile => rfl

@[simp] theorem charge_copy_apply (a : StoppingPower.Particle) :
    StoppingPowerSolution.SpecsAux.SpecMirror.charge (particleEquiv a) =
      StoppingPower.charge a := by
  match a with
  | .electron _ => rfl
  | .projectile => rfl

@[simp] theorem bitOffset_copy_apply (a : StoppingPower.Particle) (w : Fin 3) :
    StoppingPowerSolution.SpecsAux.SpecMirror.bitOffset (particleEquiv a) w =
      StoppingPower.bitOffset a w := by
  match a with
  | .electron _ => rfl
  | .projectile => rfl

@[simp] theorem signMagnitude_copy_apply (x : Fin (2 ^ StoppingPower.systemQubits))
    (a : StoppingPower.Particle) (w : Fin 3) :
    StoppingPowerSolution.SpecsAux.SpecMirror.signMagnitude x (particleEquiv a) w =
      StoppingPower.signMagnitude x a w := by
  match a with
  | .electron _ => rfl
  | .projectile => rfl

@[simp] theorem signMagnitude_symm_apply (x : Fin (2 ^ StoppingPower.systemQubits))
    (a : StoppingPowerSolution.SpecsAux.SpecMirror.Particle) (w : Fin 3) :
    StoppingPower.signMagnitude x (particleEquiv.symm a) w =
      StoppingPowerSolution.SpecsAux.SpecMirror.signMagnitude x a w := by
  match a with
  | .electron _ => rfl
  | .projectile => rfl

@[simp] theorem momentum_copy_apply (x : Fin (2 ^ StoppingPower.systemQubits))
    (a : StoppingPower.Particle) :
    StoppingPowerSolution.SpecsAux.SpecMirror.momentum x (particleEquiv a) =
      StoppingPower.momentum x a := by
  funext w
  match a with
  | .electron _ => rfl
  | .projectile => rfl

@[simp] theorem momentum_symm_apply (x : Fin (2 ^ StoppingPower.systemQubits))
    (a : StoppingPowerSolution.SpecsAux.SpecMirror.Particle) :
    StoppingPower.momentum x (particleEquiv.symm a) =
      StoppingPowerSolution.SpecsAux.SpecMirror.momentum x a := by
  funext w
  match a with
  | .electron _ => rfl
  | .projectile => rfl

theorem isGridState_eq_copy (x : Fin (2 ^ StoppingPower.systemQubits)) :
    StoppingPower.IsGridState x =
      StoppingPowerSolution.SpecsAux.SpecMirror.IsGridState x := propext <| by
  unfold StoppingPower.IsGridState StoppingPowerSolution.SpecsAux.SpecMirror.IsGridState
  exact ⟨fun h a w ↦ by simpa using h (particleEquiv.symm a) w,
         fun h a w ↦ by simpa using h (particleEquiv a) w⟩

theorem gridStates_eq_copy :
    StoppingPower.gridStates = StoppingPowerSolution.SpecsAux.SpecMirror.gridStates := by
  ext x
  simp [StoppingPower.gridStates, StoppingPowerSolution.SpecsAux.SpecMirror.gridStates,
    isGridState_eq_copy]

theorem fermionicProjector_eq_copy (spinUp : Finset (Fin StoppingPower.numElectrons)) :
    StoppingPower.fermionicProjector spinUp =
      StoppingPowerSolution.SpecsAux.SpecMirror.fermionicProjector spinUp := by
  ext x y
  dsimp only [StoppingPower.fermionicProjector,
    StoppingPowerSolution.SpecsAux.SpecMirror.fermionicProjector, Matrix.of_apply]
  rw [isGridState_eq_copy x, isGridState_eq_copy y]
  rfl

theorem hamiltonian_eq_copy (c : StoppingPower.Configuration) :
    StoppingPower.hamiltonian c =
      StoppingPowerSolution.SpecsAux.SpecMirror.hamiltonian (toCopyCfg c) := by
  ext x y
  dsimp only [StoppingPower.hamiltonian,
    StoppingPowerSolution.SpecsAux.SpecMirror.hamiltonian, Matrix.of_apply]
  rw [isGridState_eq_copy x, isGridState_eq_copy y]
  have h1 :
      (∑ a : StoppingPower.Particle,
        if ∀ b ≠ a, StoppingPower.momentum x b = StoppingPower.momentum y b then
          (StoppingPower.charge a : ℂ) *
            StoppingPower.structureFactor c
              (StoppingPower.momentum x a - StoppingPower.momentum y a) *
            StoppingPower.coulombKernel
              (StoppingPower.momentum x a - StoppingPower.momentum y a)
        else 0) =
      (∑ a : StoppingPowerSolution.SpecsAux.SpecMirror.Particle,
        if ∀ b ≠ a,
            StoppingPowerSolution.SpecsAux.SpecMirror.momentum x b =
              StoppingPowerSolution.SpecsAux.SpecMirror.momentum y b then
          (StoppingPowerSolution.SpecsAux.SpecMirror.charge a : ℂ) *
            StoppingPowerSolution.SpecsAux.SpecMirror.structureFactor (toCopyCfg c)
              (StoppingPowerSolution.SpecsAux.SpecMirror.momentum x a -
                StoppingPowerSolution.SpecsAux.SpecMirror.momentum y a) *
            StoppingPowerSolution.SpecsAux.SpecMirror.coulombKernel
              (StoppingPowerSolution.SpecsAux.SpecMirror.momentum x a -
                StoppingPowerSolution.SpecsAux.SpecMirror.momentum y a)
        else 0) := by
    rw [← Equiv.sum_comp particleEquiv]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    refine if_congr ?_ ?_ rfl
    · constructor
      · intro h b hb
        have := h (particleEquiv.symm b) (by
            intro heq
            apply hb
            simp [← heq])
        rwa [momentum_symm_apply, momentum_symm_apply] at this
      · intro h b hb
        have := h (particleEquiv b) (particleEquiv.injective.ne hb)
        rwa [momentum_copy_apply, momentum_copy_apply] at this
    · rw [charge_copy_apply, momentum_copy_apply, momentum_copy_apply]
      rfl
  have h2 :
      (∑ a : StoppingPower.Particle, ∑ b : StoppingPower.Particle,
        if a ≠ b ∧
            (∀ d, d ≠ a → d ≠ b → StoppingPower.momentum x d = StoppingPower.momentum y d) ∧
            StoppingPower.momentum x a + StoppingPower.momentum x b =
              StoppingPower.momentum y a + StoppingPower.momentum y b then
          (StoppingPower.charge a : ℝ) * StoppingPower.charge b *
            StoppingPower.coulombKernel
              (StoppingPower.momentum x a - StoppingPower.momentum y a) / 2
        else 0) =
      (∑ a : StoppingPowerSolution.SpecsAux.SpecMirror.Particle,
        ∑ b : StoppingPowerSolution.SpecsAux.SpecMirror.Particle,
        if a ≠ b ∧
            (∀ d, d ≠ a → d ≠ b →
              StoppingPowerSolution.SpecsAux.SpecMirror.momentum x d =
                StoppingPowerSolution.SpecsAux.SpecMirror.momentum y d) ∧
            StoppingPowerSolution.SpecsAux.SpecMirror.momentum x a +
              StoppingPowerSolution.SpecsAux.SpecMirror.momentum x b =
              StoppingPowerSolution.SpecsAux.SpecMirror.momentum y a +
                StoppingPowerSolution.SpecsAux.SpecMirror.momentum y b then
          (StoppingPowerSolution.SpecsAux.SpecMirror.charge a : ℝ) *
            StoppingPowerSolution.SpecsAux.SpecMirror.charge b *
            StoppingPowerSolution.SpecsAux.SpecMirror.coulombKernel
              (StoppingPowerSolution.SpecsAux.SpecMirror.momentum x a -
                StoppingPowerSolution.SpecsAux.SpecMirror.momentum y a) / 2
        else 0) := by
    rw [← Equiv.sum_comp particleEquiv]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Equiv.sum_comp particleEquiv]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    refine if_congr ?_ ?_ rfl
    · refine and_congr particleEquiv.injective.ne_iff.symm (and_congr ?_ ?_)
      · constructor
        · intro h d hda hdb
          have := h (particleEquiv.symm d)
            (by
            intro heq
            apply hda
            simp [← heq])
            (by
            intro heq
            apply hdb
            simp [← heq])
          rwa [momentum_symm_apply, momentum_symm_apply] at this
        · intro h d hda hdb
          have := h (particleEquiv d)
            (particleEquiv.injective.ne hda) (particleEquiv.injective.ne hdb)
          rwa [momentum_copy_apply, momentum_copy_apply] at this
      · rw [momentum_copy_apply, momentum_copy_apply, momentum_copy_apply, momentum_copy_apply]
    · rw [charge_copy_apply a, charge_copy_apply b,
        momentum_copy_apply x a, momentum_copy_apply y a]
      rfl
  rw [h1, h2]
  rfl

theorem approximatesTimeEvolution_eq_copy {k m : ℕ} (H : Operator (2 ^ k)) (t ε : ℝ)
    (P : Operator (2 ^ k)) (W : Unitary (2 ^ (k + m))) :
    ApproximatesTimeEvolution H t ε P W =
      StoppingPowerSolution.SpecsAux.ApproximatesTimeEvolution H t ε P W := rfl

end Bridge

set_option allowUnsafeReducibility true in
attribute [local reducible]
  StoppingPower.numElectrons StoppingPowerSolution.SpecsAux.SpecMirror.numElectrons
  StoppingPower.systemQubits StoppingPowerSolution.SpecsAux.SpecMirror.systemQubits

set_option allowUnsafeReducibility true in
attribute [local irreducible]
  StoppingPower.gridStates StoppingPowerSolution.SpecsAux.SpecMirror.gridStates
  StoppingPower.fermionicProjector StoppingPowerSolution.SpecsAux.SpecMirror.fermionicProjector
  StoppingPower.hamiltonian StoppingPowerSolution.SpecsAux.SpecMirror.hamiltonian
  ApproximatesTimeEvolution StoppingPowerSolution.SpecsAux.ApproximatesTimeEvolution

set_option exponentiation.threshold 8192

namespace StoppingPowerSolution.ComposableBell18Endpoint

open StoppingPowerSolution.FullSysCatSegmentBridge (fullSysRawBEUnitary)
open StoppingPowerSolution.CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open StoppingPowerSolution.ZeroSubwireCoinPrep80 (wIdealRat)
open StoppingPowerSolution.Pos512AlphaBundle (wIdealRat_slot5)
open StoppingPowerSolution.Slot3Norm1s36_161w (Norm1sTier)
open StoppingPowerSolution.GqspSlot3UltraBkAnd8TierCert
  (IsCertifiedNorm1sTier6 s3EpsUltraBkNano s3Swap3OracleNorm1sUltraBk
   s3Swap3OracleNorm1sUltraBk_wSlot s3Swap3OracleNorm1sUltraBk_epsIntr_le
   s3Swap3OracleNorm1sUltraBk_fixesLowEff)
open StoppingPowerSolution.GqspCleanCoinAndGuardBridge
  (Coin3CleanProgSpecOfWeights GenBetaExtHkSelAndPertSpec)
open StoppingPowerSolution.ConstructiveAlpha124052Bundle
  (prepBundleOfPostCertAndCoin prepBundleOfPostCertAndCoin_uPrep_eq_gen hqftFactor_coreQftPruned128)
open StoppingPowerSolution.Pos512FastPrepAndCoin (truncChiralPos512OfW)
open StoppingPowerSolution.FermionicKrylovSegBridge
  (RawBEMapsFermToKrylov3 RawBEBlockCommutesFerm)
open StoppingPowerSolution.NucMatADipSexticCap
  (eps2ChiralPos512OptOfW tierBB2IdMod4_truncChiralPos512OfW_opt_intrinsic_agr
   nonS3ChiralPos512OptNano eps2ChiralPos512Opt_nonS3_base_le)
open StoppingPowerSolution.PosPostBhmtPrep (pos80BhmtPostPrepCert)
open StoppingPowerSolution.KrylovS1
  (rawBEMapsFermToKrylov3_pruned128_of_oraHypPwu24_step)
open StoppingPowerSolution.BhmtBlockComm (step_rawBEBlockCommutesFerm_Bhmt_pwu24)
open StoppingPowerSolution.ParetoSelectStitch
  (Pos512ChiralBhmtPwu24HorizonSelPkg ChiralCoinCapBhmtPwu24GenOnHorizon
   mkSlimChiralBhmtPwu24GenBetaSelAndPertSpecOfEps2AndN)

/-- Instantiation via `nonS3ChiralPos512OptNano`. -/
noncomputable def spCombinedPos512Opt
    {mWork : ℕ} (hm128 : 128 ≤ mWork)
    {B W bSub bk tCoin coinNano t2Ctrl t2Cat tSelCtrl tSelCat epsCapNano : Fin 10 → ℕ}
    {tier : Fin 10 → Norm1sTier}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    {hbLo : ∀ j, 18 ≤ bSub j} {hbHi : ∀ j, bSub j ≤ 24}
    (hW28 : ∀ j, 28 ≤ W j) (hW36 : ∀ j, W j ≤ 36)
    (ht : ∀ j, IsCertifiedNorm1sTier6 (tier j))
    (hbk : ∀ j, 21 ≤ bk j ∧ bk j ≤ 36)
    (hBCases : ∀ j, B j = 22 ∨ B j = 23 ∨ B j = 24 ∨ B j = 25 ∨ B j = 26 ∨ B j = 27)
    (coinSched : ∀ j, Coin3CleanProgSpecOfWeights wIdealRat (135598 : ℝ)
      (tCoin j) (((coinNano j : ℕ) : ℝ) / 1000000000))
    (pkg : ∀ j, Pos512ChiralBhmtPwu24HorizonSelPkg mWork 11 (by decide)
      (W j) (B j) (bSub j) (t2Ctrl j) (t2Cat j) (tSelCtrl j) (tSelCat j)
      (hB6 j) (hB27 j) (hbLo j) (hbHi j)
      (s3Swap3OracleNorm1sUltraBk (tier j) (ht j) (bk j) (hbk j)))
    (hCap : ∀ j, ChiralCoinCapBhmtPwu24GenOnHorizon nonS3ChiralPos512OptNano
      (coinNano j) (B j) (W j) (bSub j)
      (s3EpsUltraBkNano (tier j) (bk j)) (epsCapNano j)) :
    GenBetaExtHkSelAndPertSpec mWork 11 (by decide) (135598 : ℝ)
      (fun j ↦ tCoin j + 1130) tSelCtrl tSelCat
      (fun j ↦ (epsCapNano j : ℝ) / 1000000000) :=
  mkSlimChiralBhmtPwu24GenBetaSelAndPertSpecOfEps2AndN
    eps2ChiralPos512OptOfW
    tierBB2IdMod4_truncChiralPos512OfW_opt_intrinsic_agr
    nonS3ChiralPos512OptNano
    (fun W _ _ ↦ eps2ChiralPos512Opt_nonS3_base_le W)
    (by omega : 100 ≤ mWork) (by norm_num : (0 : ℝ) < 135598)
    hW28 hW36 (fun _ ↦ wIdealRat)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ wIdealRat_slot5)
    coinSched hBCases
    (fun j ↦ s3Swap3OracleNorm1sUltraBk (tier j) (ht j) (bk j) (hbk j))
    (fun j cfg ↦ s3Swap3OracleNorm1sUltraBk_wSlot (tier j) (ht j) (bk j) (hbk j) cfg)
    (fun j ↦ s3Swap3OracleNorm1sUltraBk_epsIntr_le (tier j) (ht j) (bk j) (hbk j))
    pkg hCap

theorem spCombinedPos512Opt_hKrylovFerm
    {mWork : ℕ}
    {B W bSub bk tCoin coinNano t2Ctrl t2Cat tSelCtrl tSelCat : Fin 10 → ℕ}
    {tier : Fin 10 → Norm1sTier}
    {hB6 : ∀ j, 6 ≤ B j} {hB27 : ∀ j, B j ≤ 27}
    {hbLo : ∀ j, 18 ≤ bSub j} {hbHi : ∀ j, bSub j ≤ 24}
    (ht : ∀ j, IsCertifiedNorm1sTier6 (tier j))
    (hbk : ∀ j, 21 ≤ bk j ∧ bk j ≤ 36)
    (coinSched : ∀ j, Coin3CleanProgSpecOfWeights wIdealRat (135598 : ℝ)
      (tCoin j) (((coinNano j : ℕ) : ℝ) / 1000000000))
    (pkg : ∀ j, Pos512ChiralBhmtPwu24HorizonSelPkg mWork 11 (by decide)
      (W j) (B j) (bSub j) (t2Ctrl j) (t2Cat j) (tSelCtrl j) (tSelCat j)
      (hB6 j) (hB27 j) (hbLo j) (hbHi j)
      (s3Swap3OracleNorm1sUltraBk (tier j) (ht j) (bk j) (hbk j)))
    (j : Fin 10)
    (c : StoppingPowerSolution.SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin StoppingPowerSolution.SpecsAux.SpecMirror.numElectrons)) :
    RawBEMapsFermToKrylov3 spinUp
      (fullSysRawBEUnitary coreQftHadamardPrunedBundle128
        (prepBundleOfPostCertAndCoin pos80BhmtPostPrepCert (coinSched j))
        (pkg j).selOra c) :=
  rawBEMapsFermToKrylov3_pruned128_of_oraHypPwu24_step spinUp
    ⟨pos80BhmtPostPrepCert, (coinSched j).uCoin, ⟨_, rfl⟩,
      prepBundleOfPostCertAndCoin_uPrep_eq_gen pos80BhmtPostPrepCert (coinSched j) c⟩
    (pkg j).hOra
    (pkg j).hLeaf2Pos
    (s3Swap3OracleNorm1sUltraBk_fixesLowEff (tier j) (ht j) (bk j) (hbk j) c)

theorem spCombinedPos512Opt_hBlockComm
    {mWork : ℕ}
    {B W bSub bk tCoin coinNano t2Ctrl t2Cat tSelCtrl tSelCat : Fin 10 → ℕ}
    {tier : Fin 10 → Norm1sTier}
    (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27)
    {hbLo : ∀ j, 18 ≤ bSub j} {hbHi : ∀ j, bSub j ≤ 24}
    (ht : ∀ j, IsCertifiedNorm1sTier6 (tier j))
    (hbk : ∀ j, 21 ≤ bk j ∧ bk j ≤ 36)
    (coinSched : ∀ j, Coin3CleanProgSpecOfWeights wIdealRat (135598 : ℝ)
      (tCoin j) (((coinNano j : ℕ) : ℝ) / 1000000000))
    (pkg : ∀ j, Pos512ChiralBhmtPwu24HorizonSelPkg mWork 11 (by decide)
      (W j) (B j) (bSub j) (t2Ctrl j) (t2Cat j) (tSelCtrl j) (tSelCat j)
      (hB6 j) (hB27 j) (hbLo j) (hbHi j)
      (s3Swap3OracleNorm1sUltraBk (tier j) (ht j) (bk j) (hbk j)))
    (j : Fin 10)
    (c : StoppingPowerSolution.SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin StoppingPowerSolution.SpecsAux.SpecMirror.numElectrons)) :
    RawBEBlockCommutesFerm spinUp
      (fullSysRawBEUnitary coreQftHadamardPrunedBundle128
        (prepBundleOfPostCertAndCoin pos80BhmtPostPrepCert (coinSched j))
        (pkg j).selOra c) :=
  step_rawBEBlockCommutesFerm_Bhmt_pwu24
    (hB6 j) (hB27 j)
    (truncChiralPos512OfW (W j))
    coreQftHadamardPrunedBundle128 hqftFactor_coreQftPruned128
    (prepBundleOfPostCertAndCoin pos80BhmtPostPrepCert (coinSched j))
    (coinSched j).uCoin
    (prepBundleOfPostCertAndCoin_uPrep_eq_gen pos80BhmtPostPrepCert (coinSched j))
    (pkg j).selOra
    (pkg j).leaf2
    (pkg j).hLeaf2Pos
    (s3Swap3OracleNorm1sUltraBk (tier j) (ht j) (bk j) (hbk j))
    (pkg j).hOra
    c spinUp

end StoppingPowerSolution.ComposableBell18Endpoint

namespace StoppingPowerSolution.ComposableLiveEndpoint
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn Unitary.instCommGroupSubtypeMemSubmonoidUnitary
open StoppingPowerSolution.ComposableBell18Endpoint
open StoppingPowerSolution.Slot3Norm1s36_161w (Norm1sTier)
open StoppingPowerSolution.Leaf3Slot3Norm1sWidth204 (IsCertifiedNorm1sTier)
open StoppingPowerSolution.ZeroSubwireCoinPrep80 (wIdealRat)
open StoppingPowerSolution.GqspCatPrepSub600Nano (catPrepErrUltra1q)
open StoppingPowerSolution.GqspSlot3UltraBkAnd8TierCert
  (IsCertifiedNorm1sTier6 s3EpsUltraBkNano s3Swap3OracleNorm1sUltraBk)
open StoppingPowerSolution.GqspCleanCoinAndGuardBridge
  (OneAngleExtHkHorizonCertTable Coin3CleanProgSpecOfWeights)
open StoppingPowerSolution.GqspTiersA135598
  (gqsp_Tier1Pkg gqsp_Tier2Pkg gqsp_Tier3Pkg)
open StoppingPowerSolution.GqspTiersB135598
  (gqsp_Tier6Pkg gqsp_Tier9Pkg)
open StoppingPowerSolution.TierTightSpine
  (gqsp_ScheduleK1_135598
   coinCleanWIdealA135598_c79_za
   coinCleanWIdealA135598_c84
   coinCleanWIdealA135598_c88
   coinCleanWIdealA135598_c90
   coinCleanWIdealA135598_c96_ultra)
open StoppingPowerSolution.SlimStageBAnchorInput
  (slimFoldedBundle179_Borrow48054)
open StoppingPowerSolution.SlimNorm1sWideSelect
  (t2CtrlSlot3InnerOfB t2CatSlot3InnerOfB truncChiralPos512OfW_eq_truncWCfg
   mkNorm1sSlot3InnerSlot3InnerSpec)
open StoppingPowerSolution.Twist114HoistCore
  (tTw114ZeroUnc54 mkSlot3InnerGenAsymHeldTwSpec114ZeroUnc54_11_14_mWor)
open StoppingPowerSolution.StageBOneWireBridge (stageBOneWireBoothOptAnchorT)
open StoppingPowerSolution.StageBOneWireOpenAdd0
  (foldedCircuitSpec_Bell18OpenQft_OneWire_mWork_ofStageA)
open StoppingPowerSolution.TruncWAsymHeldTwShell
  (Slot3InnerSlot3InnerCircuitSpec_mWork)
open StoppingPowerSolution.Pos512FastPrepAndCoin (truncChiralPos512OfW)
open StoppingPowerSolution.Held210
  (tLeaf3Held210 stepLeaf3HeldU54WideSpec_ultra)
open StoppingPowerSolution.SelectS1
  (tSelSlot3Inner_HeldTw_S1 mkComposable_Pwu24HorizonSelPkg_mWork)
open StoppingPowerSolution.ParetoSelectStitch
  (Pos512ChiralBhmtPwu24HorizonSelPkg ChiralCoinCapBhmtPwu24GenOnHorizon)
open StoppingPowerSolution.NucMatADipSexticCap (nonS3ChiralPos512OptNano)
open StoppingPowerSolution.Bell18StageABridge (stageABell18Witness)

/-- Per-horizon `OneAngleExtHkHorizonCertTable 135598 135867 11` dispatch. -/
noncomputable def gqsp_HorizonCertTable11 :
    OneAngleExtHkHorizonCertTable 135598 135867 11 where
  nSeg
  | ⟨0, _⟩ => 66799036557 | ⟨1, _⟩ => 66799036557
  | ⟨2, _⟩ => 36779135851 | ⟨3, _⟩ => 46743288956
  | ⟨4, _⟩ => 30399124305 | ⟨5, _⟩ => 36779135851
  | ⟨6, _⟩ => 28741578748 | ⟨7, _⟩ => 36779135851
  | ⟨8, _⟩ => 30399124305 | ⟨9, _⟩ => 30399124305
  rotToffSum
  | ⟨0, _⟩ => 7382644 | ⟨1, _⟩ => 7382644
  | ⟨2, _⟩ => 7943064 | ⟨3, _⟩ => 7660474
  | ⟨4, _⟩ => 8383844 | ⟨5, _⟩ => 7943064
  | ⟨6, _⟩ => 8690980 | ⟨7, _⟩ => 7943064
  | ⟨8, _⟩ => 8383844 | ⟨9, _⟩ => 8383844
  cert
  | ⟨0, _⟩ => gqsp_Tier9Pkg.cert | ⟨1, _⟩ => gqsp_Tier9Pkg.cert
  | ⟨2, _⟩ => gqsp_Tier3Pkg.cert | ⟨3, _⟩ => gqsp_Tier6Pkg.cert
  | ⟨4, _⟩ => gqsp_Tier2Pkg.cert | ⟨5, _⟩ => gqsp_Tier3Pkg.cert
  | ⟨6, _⟩ => gqsp_Tier1Pkg.cert | ⟨7, _⟩ => gqsp_Tier3Pkg.cert
  | ⟨8, _⟩ => gqsp_Tier2Pkg.cert | ⟨9, _⟩ => gqsp_Tier2Pkg.cert
  hDiv
  | ⟨0, _⟩ => gqsp_Tier9Pkg.hDiv11 | ⟨1, _⟩ => gqsp_Tier9Pkg.hDiv11
  | ⟨2, _⟩ => gqsp_Tier3Pkg.hDiv11 | ⟨3, _⟩ => gqsp_Tier6Pkg.hDiv11
  | ⟨4, _⟩ => gqsp_Tier2Pkg.hDiv11 | ⟨5, _⟩ => gqsp_Tier3Pkg.hDiv11
  | ⟨6, _⟩ => gqsp_Tier1Pkg.hDiv11 | ⟨7, _⟩ => gqsp_Tier3Pkg.hDiv11
  | ⟨8, _⟩ => gqsp_Tier2Pkg.hDiv11 | ⟨9, _⟩ => gqsp_Tier2Pkg.hDiv11
  hRot
  | ⟨0, _⟩ => le_of_eq gqsp_Tier9Pkg.hRotEq | ⟨1, _⟩ => le_of_eq gqsp_Tier9Pkg.hRotEq
  | ⟨2, _⟩ => le_of_eq gqsp_Tier3Pkg.hRotEq | ⟨3, _⟩ => le_of_eq gqsp_Tier6Pkg.hRotEq
  | ⟨4, _⟩ => le_of_eq gqsp_Tier2Pkg.hRotEq | ⟨5, _⟩ => le_of_eq gqsp_Tier3Pkg.hRotEq
  | ⟨6, _⟩ => le_of_eq gqsp_Tier1Pkg.hRotEq | ⟨7, _⟩ => le_of_eq gqsp_Tier3Pkg.hRotEq
  | ⟨8, _⟩ => le_of_eq gqsp_Tier2Pkg.hRotEq | ⟨9, _⟩ => le_of_eq gqsp_Tier2Pkg.hRotEq

/-- Per-horizon block-encoding error cap (`nHa`). -/
def coEpsCapNano : Fin 10 → ℕ
  | ⟨0, _⟩ => 9762677 | ⟨1, _⟩ => 4762679
  | ⟨2, _⟩ => 3202666 | ⟨3, _⟩ => 2333933
  | ⟨4, _⟩ => 1891999 | ⟨5, _⟩ => 1536000
  | ⟨6, _⟩ => 1326460 | ⟨7, _⟩ => 1119333
  | ⟨8, _⟩ => 1003111 | ⟨9, _⟩ => 892000
/-- Per-horizon Stage-B bit-precision parameter `B_j`. -/
def coBSched : Fin 10 → ℕ
  | ⟨0, _⟩ => 24 | ⟨1, _⟩ => 25 | ⟨2, _⟩ => 25 | ⟨3, _⟩ => 26 | ⟨4, _⟩ => 26
  | ⟨5, _⟩ => 26 | ⟨6, _⟩ => 26 | ⟨7, _⟩ => 27 | ⟨8, _⟩ => 27 | ⟨9, _⟩ => 27
/-- Per-horizon chiral truncation width `W_j`. -/
def coWSched : Fin 10 → ℕ
  | ⟨0, _⟩ => 29 | ⟨1, _⟩ => 30 | ⟨2, _⟩ => 31 | ⟨3, _⟩ => 31 | ⟨4, _⟩ => 31
  | ⟨5, _⟩ => 32 | ⟨6, _⟩ => 32 | ⟨7, _⟩ => 32 | ⟨8, _⟩ => 32 | ⟨9, _⟩ => 33
/-- Per-horizon sub-bit precision `bSub_j`. -/
def coBSubSched : Fin 10 → ℕ
  | ⟨0, _⟩ => 18 | ⟨1, _⟩ => 21 | ⟨2, _⟩ => 24 | ⟨3, _⟩ => 23 | ⟨4, _⟩ => 23
  | ⟨5, _⟩ => 23 | ⟨6, _⟩ => 24 | ⟨7, _⟩ => 23 | ⟨8, _⟩ => 23 | ⟨9, _⟩ => 23
/-- Per-horizon Slot-3 phase bit-precision `bk_j`. -/
def coBkSched : Fin 10 → ℕ
  | ⟨0, _⟩ => 32 | ⟨1, _⟩ => 33 | ⟨2, _⟩ => 33 | ⟨3, _⟩ => 34 | ⟨4, _⟩ => 35
  | ⟨5, _⟩ => 35 | ⟨6, _⟩ => 35 | ⟨7, _⟩ => 36 | ⟨8, _⟩ => 36 | ⟨9, _⟩ => 36
/-- Per-horizon Slot-3 `Norm1sTier` selection. -/
def coTierSched : Fin 10 → Norm1sTier
  | ⟨0, _⟩ => .t26_18 | ⟨1, _⟩ => .t26_17 | ⟨2, _⟩ => .t27_17
  | ⟨3, _⟩ => .t27_17 | ⟨4, _⟩ => .t29_18 | ⟨5, _⟩ => .t29_18
  | ⟨6, _⟩ => .t30_18 | ⟨7, _⟩ => .t29_18 | ⟨8, _⟩ => .t30_18
  | ⟨9, _⟩ => .t29_18
/-- Per-horizon coin-preparation T-count. -/
def coTCoinSched : Fin 10 → ℕ
  | ⟨0, _⟩ => 79 | ⟨1, _⟩ => 79 | ⟨2, _⟩ => 88 | ⟨3, _⟩ => 90 | ⟨4, _⟩ => 90
  | ⟨5, _⟩ => 84 | ⟨6, _⟩ => 96 | ⟨7, _⟩ => 90 | ⟨8, _⟩ => 90 | ⟨9, _⟩ => 96
/-- Per-horizon coin-preparation error cap (`nHa`). -/
def coCoinNanoSched : Fin 10 → ℕ
  | ⟨0, _⟩ => 182860 | ⟨1, _⟩ => 182860 | ⟨2, _⟩ => 41830
  | ⟨3, _⟩ => 19747 | ⟨4, _⟩ => 19747 | ⟨5, _⟩ => 84573
  | ⟨6, _⟩ => 3817 | ⟨7, _⟩ => 19747 | ⟨8, _⟩ => 19747
  | ⟨9, _⟩ => 3817

theorem coBSched_six_le (j : Fin 10) : 6 ≤ coBSched j := by
  revert j
  decide
theorem coBSched_le_27 (j : Fin 10) : coBSched j ≤ 27 := by
  revert j
  decide
theorem coBSched_cases (j : Fin 10) :
    coBSched j = 22 ∨ coBSched j = 23 ∨ coBSched j = 24 ∨
      coBSched j = 25 ∨ coBSched j = 26 ∨ coBSched j = 27 := by
  revert j
  decide
theorem coWSched_28_le (j : Fin 10) : 28 ≤ coWSched j := by
  revert j
  decide
theorem coWSched_le_36 (j : Fin 10) : coWSched j ≤ 36 := by
  revert j
  decide
theorem coBSubSched_18_le (j : Fin 10) : 18 ≤ coBSubSched j := by
  revert j
  decide
theorem coBSubSched_le_24 (j : Fin 10) : coBSubSched j ≤ 24 := by
  revert j
  decide
theorem coBkSched_bounds (j : Fin 10) :
    21 ≤ coBkSched j ∧ coBkSched j ≤ 36 := by
  revert j
  decide
theorem coTierSched_cert6 (j : Fin 10) : IsCertifiedNorm1sTier6 (coTierSched j) := by
  fin_cases j <;> simp [IsCertifiedNorm1sTier6, IsCertifiedNorm1sTier, coTierSched]

/-- Per-horizon clean `135,598` coin-preparation specification. -/
noncomputable def coCoinSched : ∀ j : Fin 10,
    Coin3CleanProgSpecOfWeights wIdealRat (135598 : ℝ)
      (coTCoinSched j) (((coCoinNanoSched j : ℕ) : ℝ) / 1000000000)
  | ⟨0, _⟩ => coinCleanWIdealA135598_c79_za
  | ⟨1, _⟩ => coinCleanWIdealA135598_c79_za
  | ⟨2, _⟩ => coinCleanWIdealA135598_c88
  | ⟨3, _⟩ => coinCleanWIdealA135598_c90
  | ⟨4, _⟩ => coinCleanWIdealA135598_c90
  | ⟨5, _⟩ => coinCleanWIdealA135598_c84
  | ⟨6, _⟩ => coinCleanWIdealA135598_c96_ultra
  | ⟨7, _⟩ => coinCleanWIdealA135598_c90
  | ⟨8, _⟩ => coinCleanWIdealA135598_c90
  | ⟨9, _⟩ => coinCleanWIdealA135598_c96_ultra

theorem coChiralCap (j : Fin 10) :
    ChiralCoinCapBhmtPwu24GenOnHorizon nonS3ChiralPos512OptNano
      (coCoinNanoSched j) (coBSched j) (coWSched j) (coBSubSched j)
      (s3EpsUltraBkNano (coTierSched j) (coBkSched j)) (coEpsCapNano j) := by
  revert j
  decide

private theorem gqsp_Sched_val_eq (j : Fin 10) : gqsp_ScheduleK1_135598 j = j.val + 1 := by
  revert j
  decide
theorem gqsp_Sched_ne_zero (j : Fin 10) : gqsp_ScheduleK1_135598 j ≠ 0 := by
  revert j
  decide
theorem gqsp_Sched_beta_eq (j : Fin 10) :
    (135598 : ℝ) * ((j.val + 1 : ℝ) / (gqsp_ScheduleK1_135598 j : ℝ)) = (135598 : ℝ) := by
  rw [gqsp_Sched_val_eq j]
  push_cast
  rw [div_self (by positivity), mul_one]
theorem gqsp_hTotErr11 (j : Fin 10) :
    ((gqsp_ScheduleK1_135598 j : ℝ) *
          ((gqsp_HorizonCertTable11.nSeg j : ℝ) / (2 : ℝ) ^ 48) +
        2 * catPrepErrUltra1q) +
      (j.val + 1 : ℝ) * ((coEpsCapNano j : ℝ) / 1000000000) ≤ 0.01 := by
  rw [gqsp_Sched_val_eq j]
  fin_cases j <;> norm_num [gqsp_HorizonCertTable11, coEpsCapNano, catPrepErrUltra1q]

/-- Slot-3 `Ctrl` T-count per horizon (`wCtrl = 221`). -/
def coS3CtrlT (j : Fin 10) : ℕ :=
  tLeaf3Held210 221 (coBkSched j) (coTierSched j)

/-- Slot-3 `Cat` T-count per horizon (`wCat = 224`). -/
def coS3CatT (j : Fin 10) : ℕ :=
  tLeaf3Held210 224 (coBkSched j) (coTierSched j)

/-- `HeldU54` wide Slot-3 inner circuit bundle at `mWork = 210`. -/
noncomputable def slot3InnerSpecWide (i : Fin 10) :
    Slot3InnerSlot3InnerCircuitSpec_mWork 210
      (mkNorm1sSlot3InnerSlot3InnerSpec (truncChiralPos512OfW (coWSched i))
        (coWSched i) (coBkSched i) (coTierSched i)
        (coWSched_28_le i) (coWSched_le_36 i)
        (truncChiralPos512OfW_eq_truncWCfg (coWSched i)
          (coWSched_28_le i) (coWSched_le_36 i))
        (coBkSched_bounds i) (coTierSched_cert6 i)).uInnerCatSub
      (coS3CtrlT i) (coS3CatT i) :=
  let L := stepLeaf3HeldU54WideSpec_ultra
    (210 + 11) (210 + 14) (coBkSched i) (by decide) (by decide)
    (coBkSched_bounds i) (coTierSched i) (coTierSched_cert6 i)
  { dInnerCtrl := L.dSlot3Ctrl, dInnerCat := L.dSlot3Cat,
    hToffCtrl := L.hToffCtrl, hToffCat := L.hToffCat,
    hTCtrl := L.hTCtrl, hTCat := L.hTCat,
    hRealCtrl := L.hRealCtrl, hRealCat := L.hRealCat }

/-- Per-horizon `Pos512ChiralBhmtPwu24HorizonSelPkg` assembly at `mWork = 210`. -/
noncomputable def composableTierPkg (j : Fin 10) :
    Pos512ChiralBhmtPwu24HorizonSelPkg 210 11 (by decide)
      (coWSched j) (coBSched j) (coBSubSched j)
      (t2CtrlSlot3InnerOfB (coBSched j)) (t2CatSlot3InnerOfB (coBSched j))
      (tSelSlot3Inner_HeldTw_S1
        (17260 + 724 + 47493 +
          (stageBOneWireBoothOptAnchorT (coBSched j) (210 - 56)))
        (4 * (coBSubSched j + 51)) (coS3CtrlT j) (tTw114ZeroUnc54 (coWSched j)))
      (tSelSlot3Inner_HeldTw_S1
        (17260 + 724 + 47493 +
          (stageBOneWireBoothOptAnchorT (coBSched j) (210 - 53)))
        (4 * (coBSubSched j + 51)) (coS3CatT j) (tTw114ZeroUnc54 (coWSched j)))
      (coBSched_six_le j) (coBSched_le_27 j) (coBSubSched_18_le j) (coBSubSched_le_24 j)
      (s3Swap3OracleNorm1sUltraBk (coTierSched j) (coTierSched_cert6 j)
        (coBkSched j) (coBkSched_bounds j)) :=
  let b := slimFoldedBundle179_Borrow48054 coBSched coBSched_six_le coBSched_le_27
  let c := foldedCircuitSpec_Bell18OpenQft_OneWire_mWork_ofStageA
    stageABell18Witness (by decide : 197 ≤ 210) coBSched coBSched_six_le coBSched_le_27
  mkComposable_Pwu24HorizonSelPkg_mWork (by decide : 128 ≤ 210)
    coWSched_28_le coWSched_le_36 coBkSched_bounds coTierSched_cert6
    coBSubSched_18_le coBSubSched_le_24
    { uFoldedCtrlFull := b.uFoldedCtrlFull, uFoldedCatFull := b.uFoldedCatFull,
      uFoldedSeg := b.uFoldedSeg, hInterRawCtrl := b.hInterRawCtrl,
      hInterRawCat := b.hInterRawCat, hCtrl3Seg := b.hCtrl3Seg,
      hIdle11Seg := b.hIdle11Seg, hSlackSeg := b.hSlackSeg, hCat48 := b.hCat48 }
    { dFoldedCtrl := c.dFoldedCtrl, dFoldedCat := c.dFoldedCat,
      hToffCtrl := c.hToffCtrl, hToffCat := c.hToffCat,
      hTCtrl := c.hTCtrl, hTCat := c.hTCat,
      hRealRawCtrl := c.hRealRawCtrl, hRealRawCat := c.hRealRawCat }
    (fun i ↦ mkSlot3InnerGenAsymHeldTwSpec114ZeroUnc54_11_14_mWor
      (coWSched i) 210 (coWSched_28_le i) (coWSched_le_36 i)
      (by
        have := coWSched_le_36 i
        omega))
    slot3InnerSpecWide j

/-- Assembled `GenBetaExtHkSelAndPertSpec` across all `10` horizons. -/
noncomputable def spLiveTierSpec :=
  spCombinedPos512Opt (by decide : 128 ≤ 210)
    coWSched_28_le coWSched_le_36 coTierSched_cert6 coBkSched_bounds
    coBSched_cases coCoinSched composableTierPkg coChiralCap

/-- `GF8Code18` `(13, 363)` unheld 1-angle reflection guard bundle at `mWork = 210`. -/
noncomputable def proj1GuardBundle210 :=
  StoppingPowerSolution.GF8Code18Guard19300.gf8GuardOneAngleExtHkPoly
    (mWork := 210) (k_idle := 11)
    StoppingPowerSolution.GF8Code18Guard19300.validGF8HeldPair_13_363
    (by decide : 11 ≤ 48) 227 (by decide) (by decide)
end StoppingPowerSolution.ComposableLiveEndpoint

/-- Number of clean ancilla qubits `stoppingPowerProgram` uses. -/
def stoppingPowerAncillas : ℕ := 390

set_option allowUnsafeReducibility true in
attribute [local reducible] stoppingPowerAncillas

/-- Circuit for `e^{-iHt}` at `t = j + 1` a.u. and configuration `c`, on system wires `rSys` and
clean ancilla wires `rAnc`. -/
noncomputable def stoppingPowerProgram {n : ℕ} (c : Configuration) (j : Fin 10)
    (rSys : QRegister systemQubits n) (rAnc : QRegister stoppingPowerAncillas n) :
    DynamicCircuit Var n :=
  StoppingPowerSolution.Master_ComposableStack.composableGuardMasterProgram
    (by decide : 194 ≤ 210)
    StoppingPowerSolution.ComposableLiveEndpoint.proj1GuardBundle210
    StoppingPowerSolution.ComposableLiveEndpoint.spLiveTierSpec
    StoppingPowerSolution.ComposableLiveEndpoint.gqsp_HorizonCertTable11
    StoppingPowerSolution.TierTightSpine.gqsp_ScheduleK1_135598
    (toCopyCfg c) j v rSys rAnc (by decide)

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
        (stoppingPowerProgram c j rSys rAnc).compile := by
  obtain ⟨W, h1, h2⟩ :=
    StoppingPowerSolution.Master_ComposableStack.composableGuardMaster_correctness
      StoppingPowerSolution.GF8Code18Guard19300.hbValidGF8Code18
      (by decide : 11 ≤ 17) (by decide : 194 ≤ 210)
      StoppingPowerSolution.ComposableLiveEndpoint.proj1GuardBundle210
      StoppingPowerSolution.ComposableLiveEndpoint.spLiveTierSpec
      StoppingPowerSolution.ComposableLiveEndpoint.gqsp_HorizonCertTable11
      StoppingPowerSolution.TierTightSpine.gqsp_ScheduleK1_135598
      StoppingPowerSolution.ComposableLiveEndpoint.gqsp_Sched_ne_zero
      StoppingPowerSolution.ComposableLiveEndpoint.gqsp_Sched_beta_eq
      StoppingPowerSolution.ComposableLiveEndpoint.gqsp_hTotErr11
      (StoppingPowerSolution.ComposableBell18Endpoint.spCombinedPos512Opt_hKrylovFerm
        StoppingPowerSolution.ComposableLiveEndpoint.coTierSched_cert6
        StoppingPowerSolution.ComposableLiveEndpoint.coBkSched_bounds
        StoppingPowerSolution.ComposableLiveEndpoint.coCoinSched
        StoppingPowerSolution.ComposableLiveEndpoint.composableTierPkg)
      (StoppingPowerSolution.ComposableBell18Endpoint.spCombinedPos512Opt_hBlockComm
        StoppingPowerSolution.ComposableLiveEndpoint.coBSched_six_le
        StoppingPowerSolution.ComposableLiveEndpoint.coBSched_le_27
        StoppingPowerSolution.ComposableLiveEndpoint.coTierSched_cert6
        StoppingPowerSolution.ComposableLiveEndpoint.coBkSched_bounds
        StoppingPowerSolution.ComposableLiveEndpoint.coCoinSched
        StoppingPowerSolution.ComposableLiveEndpoint.composableTierPkg)
      (toCopyCfg c) j v rSys rAnc (by decide) hdisj
  refine ⟨W, fun spinUp ↦ ?_, ?_⟩
  · rw [approximatesTimeEvolution_eq_copy, hamiltonian_eq_copy, fermionicProjector_eq_copy]
    exact h1 spinUp
  · rw [stoppingPowerProgram, gridStates_eq_copy]
    exact h2

/-- Claimed spacetime volume of the protocol. -/
def stoppingPowerConstCost : ℕ := 229357900876653900

set_option maxRecDepth 262144 in
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
        stoppingPowerConstCost := by
  exact StoppingPowerSolution.Master_ComposableStack.composableGuardMaster_const_cost
    (costCap := 229357900876653900) (by decide : 194 ≤ 210)
    StoppingPowerSolution.ComposableLiveEndpoint.proj1GuardBundle210
    StoppingPowerSolution.ComposableLiveEndpoint.spLiveTierSpec
    StoppingPowerSolution.ComposableLiveEndpoint.gqsp_HorizonCertTable11
    StoppingPowerSolution.TierTightSpine.gqsp_ScheduleK1_135598
    (by decide) (toCopyCfg c) v rSys rAnc (by decide)

set_option exponentiation.threshold 256
end QuantumComputation.Specs
