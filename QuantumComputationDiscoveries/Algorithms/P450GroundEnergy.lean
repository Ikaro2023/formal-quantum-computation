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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TightGapDeep63Cert
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SevenGearWalk333

/-!
# Ground-State Energy of Cytochrome P450 Compound I

Specification of estimating the ground-state energy of compound I of cytochrome P450 to
`ε = 1` mHa, together with every other energy within `Δ = 0.1` Ha of it, for the rounded DFTHC
Hamiltonian `P450.dfthc` of Low et al. (Phys. Rev. X 2025) of active space `X` of Goings et al.
(PNAS 2022): `63` electrons in `58` spatial orbitals, i.e. `116` Jordan–Wigner qubits.
Energies are eigenvalues of `thcHamiltonian dfthc`. Its factorization error (about `0.28` mHa in
CCSD(T); Low et al., Table V) is a property of the instance and is not part of `ε`.

* `p450GroundEnergy_correctness`: the program, started with clean ancillas, realizes a unitary
  whose phase register, measured and decoded by `p450GroundEnergyDecoder`, gives the energy of
  every `63`-electron eigenstate within `Δ` of the ground state with root-mean-square error at most
  `ε`, the error measure behind the `⌈πλ / (2ε)⌉` walk steps of Babbush et al. (2018,
  Eqs. 21–23), and does not place a higher eigenstate below the top of that window by more than
  `ε`.
* `p450GroundEnergy_const_cost`: the program is over Clifford + `T` with measurements, and its
  spacetime volume (qubits × `T` count) is at most `p450GroundEnergyConstCost`. It has no `TOFF`
  gates, so each Toffoli is built from Clifford + `T` gates and the correctness proof covers that
  construction.

The program, its decoder, its ancilla count and its cost are computable `def`s, so none of them can
be defined from the eigenvalues being estimated. The decoder has the fixed phase-estimation form
`PhaseDecoder`, with the solution choosing the register and two coefficients.

The window `Δ` keeps the statement quantum: with `scale = 0` the decoder is a constant, which would
have to be within `ε` of the ground energy and, for the eigenstates above the window, at most `ε`
below its top, which needs `Δ ≤ 2ε`. The window also covers the low-lying spin states: CCSD(T)
places the quartet `73` mHa below the sextet. As in the literature, one run on an eigenstate is
costed; preparing it is not.

Baselines. Both use the circuit of Low et al. (2025), which block-encodes the sum-of-squares
form with spectral amplification, for `⌈πλ_eff / (2ε)⌉` walk steps, `λ_eff = √(E_gap (2Λ - E_gap))`
(their Eq. 11), where `E_gap` is the largest energy to be measured minus the sum-of-squares lower
bound. With `Λ = 97.3864` Ha, the lower bound `-134.887` Ha and the quartet ROHF energy
`-129.844` Ha bounding the ground energy from above (both for `thcHamiltonian dfthc`, which omits
a constant), `E_gap ≤ 5.143` Ha, `λ_eff ≤ 31.23` Ha and `49,056` steps. Reaching this step count
requires proving the upper bound on the ground energy in Lean, for example as the energy of an
explicit `63`-electron state. Both charge `4` `T` gates per Toffoli, the Toffoli of Jones (2013)
from `4` `T` gates, an ancilla, a measurement and a classically controlled `CZ`.

* Low et al. (2025), Table V: `9,535` Toffolis per walk step on `1150` qubits. Storing `13`
  instead of `15` bits for each of the `57` angles (the angle indices of `dfthc` are below `2¹³`)
  and adding a `16`-qubit phase-estimation register gives `1052` qubits, so `4.68 × 10⁸`
  Toffolis, `1.87 × 10⁹` `T` gates and spacetime `1.97 × 10¹²`. They quote `4.91 × 10⁸` Toffolis
  with their one-body term and a Hartree–Fock bound.
* The same circuit with the logical-circuit options of Low et al., *A Denser Planar Surface Code*
  (2026, App. E), minimising qubits × `T` count over those options. The `G`, `r`, `c`, spin and
  `b = B` registers are recomputed from `x_o` by comparators, and `19` of the `57` Givens angles
  (`13` bits each) are held at a time, loaded in `3` batches with `5` lookups per `SELECT` (both
  Givens networks need every angle). Three exact refinements are also applied: that paper's
  minimum-Toffoli comparator, controlled adders that skip the two always-zero addend bits (`27`
  Toffolis), and padding `C` rather than `R` in the `x_o` index. That gives `11,517` Toffolis per
  walk step on `481` qubits (`116` system, `16` phase estimation, `15` phase gradient, `247`
  angles, `87` other), including `32` Toffolis per step for controlling the walk from the phase
  register by comparing it with the step index around both reflections, so `2.26 × 10⁹` `T`
  gates and spacetime `1.09 × 10¹²`. Improvements are quoted against this baseline.

References:
* G. H. Low et al., *Fast quantum simulation of electronic structure by spectral amplification*,
  Phys. Rev. X 15, 041016 (2025), https://doi.org/10.1103/pb2g-j9cw,
  https://arxiv.org/abs/2502.15882; factors at https://doi.org/10.5281/zenodo.17066718.
* G. H. Low et al., *A Denser Planar Surface Code* (2026), https://arxiv.org/abs/2605.30455.
* J. J. Goings et al., *Reliably assessing the electronic structure of cytochrome P450 on today's
  classical computers and tomorrow's quantum computers*, PNAS 119(38), e2203533119 (2022),
  https://arxiv.org/abs/2202.01244.
* R. Babbush et al., *Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity*,
  Phys. Rev. X 8, 041015 (2018), https://arxiv.org/abs/1805.03662.
* C. Jones, *Low-overhead constructions for the fault-tolerant Toffoli gate*, Phys. Rev. A 87,
  022328 (2013).
-/

@[expose] public section

attribute [-instance] ZMod.instField

namespace QuantumComputation.Specs

open Operator
open scoped Matrix

/-- Phase-estimation decoder of `m` ancillas, for a walk with eigenphases `±φ` that is applied
forwards or backwards depending on the phase register, so that the register `register` holds `y`,
an estimate of `±2φ`. With `θ = 2π y / 2 ^ bits` the decoded energy is
`offset + scale * |cos (θ / 2)|`. For the spectral-amplification walk of Low et al. (2025), with
`E = E_LB + Λ (1 + cos φ)` and `φ ∈ [π/2, π]` at low energy, `offset = E_LB + Λ` and
`scale = -Λ`. -/
structure PhaseDecoder (m : ℕ) where
  /-- Number of qubits of the phase register. -/
  bits : ℕ
  /-- The phase register, within the ancillas. -/
  register : QRegister bits m
  /-- Energy where the cosine is `0`. -/
  offset : ℝ
  /-- Energy per unit of the cosine. -/
  scale : ℝ

open Real in
/-- Energy that `d` decodes from the ancilla outcome `a`. -/
noncomputable def PhaseDecoder.energy {m : ℕ} (d : PhaseDecoder m) (a : Fin (2 ^ m)) : ℝ :=
  let θ := 2 * π * (d.register.extractIndex a).val / 2 ^ d.bits
  d.offset + d.scale * |cos (θ / 2)|

/-- `W` measures the energies of `H` within `Δ` of its ground-state energy on the `η`-electron
sector with root-mean-square error `ε`, decoded by `decoder`: for every `T` at most `Δ` above that
ground-state energy and every unit eigenvector `ψ` of `H` with `η` electrons and eigenvalue `E`,
measuring the ancillas of `W (ψ ⊗ |0⟩)` and decoding the outcome estimates `min E T` with mean
squared error at most `ε²` once the estimate is capped at `T`. For `E ≤ T` this bounds the error in
`E`; for `E > T` the estimate may not fall below `T` by more than `ε` in root mean square. -/
def MeasuresLowEnergies {k m : ℕ} (H : Operator (2 ^ k)) (η : ℕ) (Δ ε : ℝ)
    (decoder : PhaseDecoder m) (W : Unitary (2 ^ (k + m))) : Prop :=
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  -- `ψ ≠ 0` is needed: without it every `E'` is an eigenvalue of `0`, no `T` qualifies and the
  -- predicate holds vacuously.
  let IsEigen (E : ℝ) (ψ : Fin (2 ^ k) → ℂ) :=
    H *ᵥ ψ = (E : ℂ) • ψ ∧ electronSectorProjector k η *ᵥ ψ = ψ ∧ ψ ≠ 0
  ∀ T : ℝ, (∀ E' φ, IsEigen E' φ → T ≤ E' + Δ) →
    ∀ E ψ, IsEigen E ψ → ∑ i, Complex.normSq (ψ i) = 1 →
    let out := W.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)
    ∑ a, anc.basisOutcomeProbability a out * (min (decoder.energy a) T - min E T) ^ 2 ≤ ε ^ 2

/-- Width `2N = 116` of the system register; wire `2p + σ` holds spin orbital `(p, σ)`. -/
abbrev P450.systemQubits : ℕ := 2 * 58

open P450

/-! ## Candidate Program & Correctness / Cost Theorems -/

/-- By default we allow only a single variable. -/
inductive P450GroundEnergy.Var where | v deriving DecidableEq, Inhabited

open P450GroundEnergy (Var)
open P450GroundEnergy.Var (v)

local instance : Fintype P450GroundEnergy.Var := ⟨{.v}, fun | .v => Finset.mem_singleton_self _⟩

local instance (priority := 1000000) instNeZeroTwoPowP450Top (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

namespace P450GroundEnergy.TopBridge

open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution

open QProg Matrix Real CleanDyn
open BlockEncodingCore BlockEncodingCircuit
open TopIntegrationBridge ReordOuter13Bridge MobiusOptSubcube163Walk
open Pi145SOSPermBridge
open Inner18Symp14Walk QuantizedFactoredMag30 HadWMux23SOSBridge
open HadWStateMux25CompactA Pi145CompactSelect24 NoNegDNegSOSAndSuperWalk
open Outer8Pi145Compact2RotDyn Outer8Pi145Compact2RotOuter
open StepOuter8Pi145Outer StepOuter8Pi145L1
open Cat11CompactPhase2Bridge DihedralWalkQPE ApproxIqft16
open TailShiftWindow46847 TailShiftBox TwoGearQPEPhase5
open TailShiftThreeGear SevenGearWalk333 TightGapDeep63
open SevenGearBondDefer
open StepKeep9Symp14Data StepAnfAndCoin14Core

/-- Effective quantized spin-blocked P450 sum-of-squares Hamiltonian. -/
noncomputable abbrev mainHeff : Operator (2 ^ (2 * 58)) :=
  fullQuantP450HBlocked
    (outer8PrepOutWordImpl mag8To23Word17)
    (genPi128PrepMid18Of mux9AltBit keep9SliceTargetFn14 pi128Equiv
      factoredMag30T72Circuit.eval)
    (idealPi145Branch 8 18)

theorem mainHeff_isHermitian : mainHeff.IsHermitian := by
  unfold mainHeff fullQuantP450HBlocked
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, RCLike.star_def, Complex.conj_ofReal]

theorem pi145Perm_ok :
    allPow2 8 0 (fun x ↦
      decide (∀ hx : x < 2 ^ 8,
        (pi145Perm ⟨x, hx⟩).val = (pi145XoEquiv ⟨x, hx⟩).val)) = true := by
  decide

theorem pi145Perm_eq_pi145XoEquiv : pi145Perm = pi145XoEquiv := by
  ext x
  exact (of_decide_eq_true (allPow2_zero_true pi145Perm_ok x.val x.isLt)) x.isLt

theorem mainUB_sos :
    PulledSOSBlockEncoding (mOutUB 8) (mMidUB 18) mainHeff dfthcLowerBound 97.3864 mainUB :=
  pulledSOSBlockEncodingIdealPi145_fullQuant
    (outer8PrepOutWordImpl mag8To23Word17)
    (prepMid18FromSlice mux9AltBit keep9SliceTargetFn14 factoredMag30T72Circuit.eval)

theorem mainHeff_agree :
    AgreesOnElectronSector 58 63 mainHeff BlockEncodingCore.p450HBlocked dh4000 := by
  have hOutIdeal : PrepOutValidPerm256 pi145XoEquiv outer8PrepOutIdeal :=
    pi145Perm_eq_pi145XoEquiv ▸ prepOutValidPerseOuter8PrepOutIdeal
  have hSOS₁ :=
    pulledSOSBlockEncoding_pi145PrepMid18Mux9AltBit_quantInner hOutIdeal
      factoredMag30T72Circuit_vanish (idealPi145SelectPure 8 18)
      (fun ψ o' m hx _ ↦ selectOnLt184IdealPi145SelectPure 8 18 ψ o' m hx)
  have hL1 :
      (∑ o' : Fin (2 ^ mOutUB 8),
        |Complex.normSq ((outer8PrepOutWordImpl mag8To23Word17).1 o' 0) -
          Complex.normSq (outer8PrepOutIdeal.1 o' 0)|) ≤ 24 / 10 ^ 11 := by
    rw [sum_abs_normSqOuter8PrepOutWordImpl_sub_eq mag8To23Word17 _
      FastCleanUnif184.normSqMag8To23IdealUnitary_zero_zero]
    exact (Pi145Fast2RotCore.checkOrthGrover184L1Word_sound
      checkOrthGrover184L1Word_word17).2.trans (by norm_num)
  exact agreesOnElectronSectorIdealPi145_fullQuant
    (quantJointP450HBlocked_conjTranspose p450ExactOuterProb keep9T72Prob)
    outer8PrepOutIdeal (outer8PrepOutWordImpl mag8To23Word17)
    (prepMid18FromSlice mux9AltBit keep9SliceTargetFn14 factoredMag30T72Circuit.eval)
    hSOS₁ hL1 (agreesOnElectronSectorKeep9T72_inner 63)
    (by
      unfold dh4000
      norm_num)

theorem weighted_sum_basisOutcomeProbability_ts {k n : ℕ}
    (r : QRegister k n) (out : Fin (2 ^ n) → ℂ) (f : Fin (2 ^ k) → ℝ) :
    ∑ a : Fin (2 ^ k), r.basisOutcomeProbability a out * f a =
      ∑ g : Fin (2 ^ n), Complex.normSq (out g) * f (r.extractIndex g) := by
  simp only [QRegister.basisOutcomeProbability, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  have hterm (a : Fin (2 ^ k)) :
      Complex.normSq ((r.basisOutcomeProjector a).mulVec out g) * f a =
        if r.extractIndex g = a then Complex.normSq (out g) * f a else 0 := by
    rw [r.basisOutcomeProjector_mulVec]
    by_cases h : r.extractIndex g = a
    · simp [h]
    · simp [h]
  simp_rw [hterm]
  simp

theorem measuresLowEnergiesFG_of_unitary_conj {k m : ℕ}
    (H : Operator (2 ^ k)) (η : ℕ) (Δ ε : ℝ)
    (estimate : Fin (2 ^ m) → ℝ)
    (U_sys : Unitary (2 ^ k))
    (hsec : U_sys.1 * electronSectorProjector k η * U_sys.1ᴴ = electronSectorProjector k η)
    (W_blk : Unitary (2 ^ (k + m)))
    (hblk : MeasuresLowEnergiesFG (U_sys.1 * H * U_sys.1ᴴ) η Δ ε estimate W_blk) :
    let sys : QRegister k (k + m) := .block 0 k (by omega)
    MeasuresLowEnergiesFG H η Δ ε estimate
      (sys.embedUnitary U_sys⁻¹ * W_blk * sys.embedUnitary U_sys) := by
  intro sys T hT E ψ hEigen hnorm
  let anc : QRegister m (k + m) := .block k m le_rfl
  have hdisj : sys.DisjointWires anc :=
    QRegister.block_disjoint_of_le 0 k k m (by omega) le_rfl (by omega)
  have hU_mul : U_sys.1ᴴ * U_sys.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U_sys.2.1
  have hU_mul' : U_sys.1 * U_sys.1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U_sys.2.2
  have heig_fwd {E' : ℝ} {φ : Fin (2 ^ k) → ℂ}
      (he : H *ᵥ φ = (E' : ℂ) • φ ∧ electronSectorProjector k η *ᵥ φ = φ ∧ φ ≠ 0) :
      (U_sys.1 * H * U_sys.1ᴴ) *ᵥ (U_sys.1 *ᵥ φ) = (E' : ℂ) • (U_sys.1 *ᵥ φ) ∧
        electronSectorProjector k η *ᵥ (U_sys.1 *ᵥ φ) = U_sys.1 *ᵥ φ ∧ U_sys.1 *ᵥ φ ≠ 0 := by
    refine ⟨?_, ?_, ?_⟩
    · calc (U_sys.1 * H * U_sys.1ᴴ) *ᵥ (U_sys.1 *ᵥ φ)
          = U_sys.1 *ᵥ (H *ᵥ ((U_sys.1ᴴ * U_sys.1) *ᵥ φ)) := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = (E' : ℂ) • (U_sys.1 *ᵥ φ) := by
            rw [hU_mul, Matrix.one_mulVec, he.1, Matrix.mulVec_smul]
    · calc electronSectorProjector k η *ᵥ (U_sys.1 *ᵥ φ)
          = (U_sys.1 * electronSectorProjector k η * U_sys.1ᴴ) *ᵥ (U_sys.1 *ᵥ φ) := by
            rw [hsec]
        _ = U_sys.1 *ᵥ (electronSectorProjector k η *ᵥ ((U_sys.1ᴴ * U_sys.1) *ᵥ φ)) := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = U_sys.1 *ᵥ φ := by
            rw [hU_mul, Matrix.one_mulVec, he.2.1]
    · intro hz
      apply he.2.2
      calc φ = (U_sys.1ᴴ * U_sys.1) *ᵥ φ := by
            rw [hU_mul, Matrix.one_mulVec]
        _ = U_sys.1ᴴ *ᵥ (U_sys.1 *ᵥ φ) := (Matrix.mulVec_mulVec φ U_sys.1ᴴ U_sys.1).symm
        _ = 0 := by
            rw [hz, Matrix.mulVec_zero]
  have heig_bwd {E' : ℝ} {φ' : Fin (2 ^ k) → ℂ}
      (he : (U_sys.1 * H * U_sys.1ᴴ) *ᵥ φ' = (E' : ℂ) • φ' ∧
        electronSectorProjector k η *ᵥ φ' = φ' ∧ φ' ≠ 0) :
      H *ᵥ (U_sys.1ᴴ *ᵥ φ') = (E' : ℂ) • (U_sys.1ᴴ *ᵥ φ') ∧
        electronSectorProjector k η *ᵥ (U_sys.1ᴴ *ᵥ φ') = U_sys.1ᴴ *ᵥ φ' ∧
          U_sys.1ᴴ *ᵥ φ' ≠ 0 := by
    refine ⟨?_, ?_, ?_⟩
    · calc H *ᵥ (U_sys.1ᴴ *ᵥ φ')
          = (U_sys.1ᴴ * U_sys.1) *ᵥ (H *ᵥ (U_sys.1ᴴ *ᵥ φ')) := by
            rw [hU_mul, Matrix.one_mulVec]
        _ = U_sys.1ᴴ *ᵥ ((U_sys.1 * H * U_sys.1ᴴ) *ᵥ φ') := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = (E' : ℂ) • (U_sys.1ᴴ *ᵥ φ') := by
            rw [he.1, Matrix.mulVec_smul]
    · have hsec_inv : U_sys.1ᴴ * electronSectorProjector k η * U_sys.1 =
          electronSectorProjector k η := by
        calc U_sys.1ᴴ * electronSectorProjector k η * U_sys.1
            = U_sys.1ᴴ * (U_sys.1 * electronSectorProjector k η * U_sys.1ᴴ) * U_sys.1 := by
              rw [hsec]
          _ = (U_sys.1ᴴ * U_sys.1) * electronSectorProjector k η * (U_sys.1ᴴ * U_sys.1) := by
              simp only [Matrix.mul_assoc]
          _ = electronSectorProjector k η := by
              rw [hU_mul, one_mul, mul_one]
      calc electronSectorProjector k η *ᵥ (U_sys.1ᴴ *ᵥ φ')
          = (U_sys.1ᴴ * electronSectorProjector k η * U_sys.1) *ᵥ (U_sys.1ᴴ *ᵥ φ') := by
            rw [hsec_inv]
        _ = U_sys.1ᴴ *ᵥ (electronSectorProjector k η *ᵥ ((U_sys.1 * U_sys.1ᴴ) *ᵥ φ')) := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = U_sys.1ᴴ *ᵥ φ' := by
            rw [hU_mul', Matrix.one_mulVec, he.2.1]
    · intro hz
      apply he.2.2
      calc φ' = (U_sys.1 * U_sys.1ᴴ) *ᵥ φ' := by
            rw [hU_mul', Matrix.one_mulVec]
        _ = U_sys.1 *ᵥ (U_sys.1ᴴ *ᵥ φ') := (Matrix.mulVec_mulVec φ' U_sys.1 U_sys.1ᴴ).symm
        _ = 0 := by
            rw [hz, Matrix.mulVec_zero]
  have hT_blk : ∀ (E' : ℝ) (φ' : Fin (2 ^ k) → ℂ),
      ((U_sys.1 * H * U_sys.1ᴴ) *ᵥ φ' = (E' : ℂ) • φ' ∧
        electronSectorProjector k η *ᵥ φ' = φ' ∧ φ' ≠ 0) → T ≤ E' + Δ :=
    fun E' φ' he' ↦ hT E' (U_sys.1ᴴ *ᵥ φ') (heig_bwd he')
  have hnorm_fwd : ∑ i, Complex.normSq ((U_sys.1 *ᵥ ψ) i) = 1 := by
    let v : EuclideanSpace ℂ (Fin (2 ^ k)) := WithLp.toLp 2 ψ
    let u : EuclideanSpace ℂ (Fin (2 ^ k)) := WithLp.toLp 2 (U_sys.1 *ᵥ ψ)
    have h1 : ∑ i, Complex.normSq ((U_sys.1 *ᵥ ψ) i) = ‖u‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [u, Complex.normSq_eq_norm_sq]
    have h2 : ∑ i, Complex.normSq (ψ i) = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [v, Complex.normSq_eq_norm_sq]
    have hu_sq : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      have hdot : star (U_sys.1 *ᵥ ψ) ⬝ᵥ (U_sys.1 *ᵥ ψ) = star ψ ⬝ᵥ ψ := by
        rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
          hU_mul, Matrix.vecMul_one]
      have hre := congrArg Complex.re hdot
      have hsum_eq : ∀ w : Fin (2 ^ k) → ℂ,
          (star w ⬝ᵥ w).re = ∑ i, ‖w i‖ ^ 2 := fun w ↦ by
        simp only [dotProduct, Pi.star_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
          Complex.normSq_eq_norm_sq]
      rwa [hsum_eq, hsum_eq] at hre
    rw [h1, hu_sq, ← h2, hnorm]
  have hinit_fwd : (sys.embedUnitary U_sys).1 *ᵥ sys.tensorState ψ (Pi.single 0 1) =
      sys.tensorState (U_sys.1 *ᵥ ψ) (Pi.single 0 1) :=
    sys.embedMatrix_mulVec_tensorState U_sys.1 ψ (Pi.single 0 1)
  let u_blk := W_blk.1 *ᵥ sys.tensorState (U_sys.1 *ᵥ ψ) (Pi.single 0 1)
  have hprob_eq (a : Fin (2 ^ m)) :
      anc.basisOutcomeProbability a
        (((sys.embedUnitary U_sys⁻¹ * W_blk * sys.embedUnitary U_sys).1) *ᵥ
          sys.tensorState ψ (Pi.single 0 1)) =
      anc.basisOutcomeProbability a u_blk := by
    have hvec : ((sys.embedUnitary U_sys⁻¹ * W_blk * sys.embedUnitary U_sys).1) *ᵥ
        sys.tensorState ψ (Pi.single 0 1) =
        (sys.embedUnitary U_sys⁻¹).1 *ᵥ u_blk := by
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hinit_fwd, u_blk]
    rw [hvec]
    unfold QRegister.basisOutcomeProbability
    have hcomm : anc.basisOutcomeProjector a * (sys.embedUnitary U_sys⁻¹).1 =
        (sys.embedUnitary U_sys⁻¹).1 * anc.basisOutcomeProjector a :=
      (sys.embedMatrix_comm_of_disjoint anc hdisj (U_sys⁻¹).1 (compProj a)).symm
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    let w := anc.basisOutcomeProjector a *ᵥ u_blk
    let V := sys.embedUnitary U_sys⁻¹
    have hV_mul : V.1ᴴ * V.1 = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact V.2.1
    have hdot : star (V.1 *ᵥ w) ⬝ᵥ (V.1 *ᵥ w) = star w ⬝ᵥ w := by
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        hV_mul, Matrix.vecMul_one]
    have hre := congrArg Complex.re hdot
    have hsum_normSq : ∀ z : Fin (2 ^ (k + m)) → ℂ,
        ∑ g, Complex.normSq (z g) = (star z ⬝ᵥ z).re := fun z ↦ by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    rw [hsum_normSq, hsum_normSq, hre]
  have hgoal := hblk T hT_blk E (U_sys.1 *ᵥ ψ) (heig_fwd hEigen) hnorm_fwd
  dsimp only at hgoal ⊢
  have hsum_eq :
      (∑ a : Fin (2 ^ m),
        anc.basisOutcomeProbability a
          (((sys.embedUnitary U_sys⁻¹ * W_blk * sys.embedUnitary U_sys).1) *ᵥ
            sys.tensorState ψ (Pi.single 0 1)) *
          (min (estimate a) T - min E T) ^ 2) =
      ∑ a : Fin (2 ^ m),
        anc.basisOutcomeProbability a u_blk * (min (estimate a) T - min E T) ^ 2 :=
    Finset.sum_congr rfl fun a _ ↦ by
      rw [hprob_eq a]
  exact hsum_eq.le.trans hgoal

theorem measuresLowEnergiesFG_dfthc_of_p450HBlocked {m : ℕ} {Δ ε : ℝ}
    {estimate : Fin (2 ^ m) → ℝ}
    (W_blk : Unitary (2 ^ (2 * 58 + m)))
    (hblk : MeasuresLowEnergiesFG BlockEncodingCore.p450HBlocked 63 Δ ε estimate W_blk) :
    let sys : QRegister (2 * 58) (2 * 58 + m) := .block 0 (2 * 58) (by omega)
    MeasuresLowEnergiesFG (thcHamiltonian dfthc) 63 Δ ε estimate
      (sys.embedUnitary p450FswapUninterleave.eval⁻¹ * W_blk *
        sys.embedUnitary p450FswapUninterleave.eval) :=
  measuresLowEnergiesFG_of_unitary_conj (thcHamiltonian dfthc) 63 Δ ε estimate
    p450FswapUninterleave.eval (p450FswapUninterleave_conj_electronSectorProjector 63)
    W_blk hblk

theorem measuresLowEnergiesFG_embed_block {k m_act m_scr : ℕ}
    (H : Operator (2 ^ k)) (η : ℕ) (Δ ε : ℝ)
    (estimate₀ : Fin (2 ^ m_act) → ℝ)
    (U_act : Unitary (2 ^ (k + m_act)))
    (hest : MeasuresLowEnergiesFG H η Δ ε estimate₀ U_act) :
    let sub_act : QRegister m_act (m_act + m_scr) := .block 0 m_act (by omega)
    MeasuresLowEnergiesFG H η Δ ε (fun a ↦ estimate₀ (sub_act.extractIndex a))
      ((QRegister.block 0 (k + m_act)
          (by omega : 0 + (k + m_act) ≤ k + (m_act + m_scr))).embedUnitary U_act) := by
  intro sub_act T hT E ψ hEigen hnorm
  let rAct_loc : QRegister (k + m_act) (k + (m_act + m_scr)) := .block 0 (k + m_act) (by omega)
  have hbase := hest T hT E ψ hEigen hnorm
  let sys_act : QRegister k (k + m_act) := .block 0 k (by omega)
  let anc_act : QRegister m_act (k + m_act) := .block k m_act le_rfl
  let sys_big : QRegister k (k + (m_act + m_scr)) := .block 0 k (by omega)
  let anc_big : QRegister (m_act + m_scr) (k + (m_act + m_scr)) := .block k (m_act + m_scr) le_rfl
  let out_act := U_act.1 *ᵥ sys_act.tensorState ψ (Pi.single 0 1)
  let out_big := (rAct_loc.embedUnitary U_act).1 *ᵥ sys_big.tensorState ψ (Pi.single 0 1)
  have htensor : sys_big.tensorState ψ (Pi.single 0 1) =
      rAct_loc.tensorState (sys_act.tensorState ψ (Pi.single 0 1)) (Pi.single 0 1) := by
    funext g
    have hextr : sys_big.extractIndex g = sys_act.extractIndex (rAct_loc.extractIndex g) := by
      rw [← QRegister.extractIndex_compose]
      congr 1
      ext i
      simp [sys_big, rAct_loc, sys_act]
    have henv : ((sys_big.basisSplitEquiv g).2 = 0) ↔
        ((sys_act.basisSplitEquiv (rAct_loc.extractIndex g)).2 = 0 ∧
          (rAct_loc.basisSplitEquiv g).2 = 0) := by
      constructor
      · intro h
        have hbits : ∀ w : Wire (k + (m_act + m_scr)), k ≤ w.val →
            basisBits (k + (m_act + m_scr)) g w = 0 := by
          intro w hw
          have hnotin : w ∉ Set.range sys_big.wires := by
            rintro ⟨i, hi⟩
            have hval := congrArg Fin.val hi
            simp [sys_big] at hval
            omega
          exact congrFun h ⟨w, hnotin⟩
        refine ⟨?_, ?_⟩
        · funext ⟨w, hw⟩
          have hwk : k ≤ w.val := by
            by_contra hlt
            exact hw ⟨⟨w.val, Nat.lt_of_not_ge hlt⟩, by
              ext
              simp [sys_act]⟩
          simp only [QRegister.basisSplitEquiv_apply_snd, QRegister.basisBits_extractIndex,
            Pi.zero_apply]
          exact hbits (rAct_loc w) (by
            simp [rAct_loc]
            omega)
        · funext ⟨w, hw⟩
          have hwm : k ≤ w.val := by
            by_contra hlt
            exact hw ⟨⟨w.val, by omega⟩, by
              ext
              simp [rAct_loc]⟩
          exact hbits w hwm
      · rintro ⟨h₁, h₂⟩
        funext ⟨w, hw⟩
        have hwk : k ≤ w.val := by
          by_contra hlt
          exact hw ⟨⟨w.val, Nat.lt_of_not_ge hlt⟩, by
            ext
            simp [sys_big]⟩
        by_cases hlt : w.val < k + m_act
        · let w' : Wire (k + m_act) := ⟨w.val, hlt⟩
          have hw' : w' ∉ Set.range sys_act.wires := by
            rintro ⟨i, hi⟩
            have hval := congrArg Fin.val hi
            simp [sys_act, w'] at hval
            omega
          have hbit := congrFun h₁ ⟨w', hw'⟩
          simp only [QRegister.basisSplitEquiv_apply_snd, QRegister.basisBits_extractIndex,
            Pi.zero_apply] at hbit
          have hrw : rAct_loc w' = w := by
            ext
            simp [rAct_loc, w']
          rwa [hrw] at hbit
        · have hw₂ : w ∉ Set.range rAct_loc.wires := by
            rintro ⟨i, hi⟩
            have hval := congrArg Fin.val hi
            simp [rAct_loc] at hval
            omega
          exact congrFun h₂ ⟨w, hw₂⟩
    dsimp [QRegister.tensorState]
    rw [hextr]
    by_cases h : (sys_big.basisSplitEquiv g).2 = 0
    · obtain ⟨h₁, h₂⟩ := henv.mp h
      simp [h, h₁, h₂]
    · have hnot := mt henv.mpr h
      rcases not_and_or.mp hnot with h₁ | h₂
      · simp [Pi.single_apply, h, h₁]
      · simp [Pi.single_apply, h, h₂]
  have hout : out_big = rAct_loc.tensorState out_act (Pi.single 0 1) := by
    dsimp [out_big, out_act]
    rw [htensor, rAct_loc.embedMatrix_mulVec_tensorState]
  let f : Fin (2 ^ m_act) → ℝ := fun a₀ ↦ (min (estimate₀ a₀) T - min E T) ^ 2
  suffices hsum_eq :
      (∑ a : Fin (2 ^ (m_act + m_scr)),
        anc_big.basisOutcomeProbability a out_big * f (sub_act.extractIndex a)) =
      ∑ a₀ : Fin (2 ^ m_act), anc_act.basisOutcomeProbability a₀ out_act * f a₀ by
    exact hsum_eq.le.trans hbase
  rw [weighted_sum_basisOutcomeProbability_ts anc_big out_big (fun a ↦ f (sub_act.extractIndex a)),
    weighted_sum_basisOutcomeProbability_ts anc_act out_act f, hout]
  have hextr_anc (g : Fin (2 ^ (k + (m_act + m_scr)))) :
      sub_act.extractIndex (anc_big.extractIndex g) =
        anc_act.extractIndex (rAct_loc.extractIndex g) := by
    rw [← QRegister.extractIndex_compose, ← QRegister.extractIndex_compose]
    congr 1
    ext i
    simp [anc_big, sub_act, rAct_loc, anc_act]
  simp_rw [hextr_anc]
  let term : Fin (2 ^ (k + (m_act + m_scr))) → ℝ := fun g ↦
    Complex.normSq (rAct_loc.tensorState out_act (Pi.single 0 1) g) *
      f (anc_act.extractIndex (rAct_loc.extractIndex g))
  change ∑ g, term g = _
  rw [← rAct_loc.basisSplitEquiv.symm.sum_comp term, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g₀ _
  rw [Finset.sum_eq_single (0 : rAct_loc.Environment → ZMod 2)]
  · have hg₀ : rAct_loc.extractIndex (rAct_loc.basisSplitEquiv.symm (g₀, 0)) = g₀ := by
      rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    simp [term, QRegister.tensorState, hg₀]
  · intro e _ he
    simp [term, QRegister.tensorState, Pi.single_apply, he]
  · simp

/-- Ancilla energy estimator for multi-gear quantum phase estimation. -/
noncomputable abbrev p450FourGearEst (wOuter wInner2 ko km sRem : ℕ) :
    Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ :=
  fun a ↦ qpeEstimate dfthcLowerBound 97.3864 16
    (rQPEInAnc 16 11 (mOutUB wOuter) (mMidUB wInner2)).extractIndex
    ((QRegister.block 0 (actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2)) (by
      dsimp [combAncillasB, MultiGearQPE.combAncillas, cat11TotalAncillas, totalAncillas]
      omega)).extractIndex a)

theorem qpeDecodeEnergy_p450_fg_eq (y : Fin (2 ^ 16)) :
    qpeDecodeEnergy dfthcLowerBound 97.3864 16 y =
      ((-5788300336462799 / 154350387200000 : ℚ) : ℝ) +
        ((-121733 / 1250 : ℚ) : ℝ) * |cos ((2 * π * (y.val : ℝ) / 2 ^ 16) / 2)| := by
  unfold qpeDecodeEnergy qpeHalfPhase
  rw [cos_foldAngle_div_two (qpeAngle_nonneg 16 y) (qpeAngle_le_two_pi 16 y),
    dfthcLowerBound_eq_rat]
  unfold qpeAngle
  have hOff : ((-5788300336462799 / 154350387200000 : ℚ) : ℝ) =
      -20819928884476879 / 154350387200000 + 97.3864 := by norm_num
  have hSc : ((-121733 / 1250 : ℚ) : ℝ) = -97.3864 := by norm_num
  rw [hOff, hSc]
  ring

theorem fast7g_estTransferHyp (sRem : ℕ) :
    TailShiftEstTransferHyp 8 18 4 14 47487 sRem mainUB
      threeGearWin_47487_10_7.base.uIdeal dh4000
      (-130.1526) g_deep63 kp487
      (p450FourGearEst 8 18 4 14 sRem) := by
  intro ζ hζ wBlk δWUb hδWUb0 hVbox hGap hgH11 hδH0 hBud hPert
  have hRef : MultiGearQPE.P450RefVarBound (-130.1526) :=
    TightGapDeep63.p450RefVarBound_tightGapDeep63
  have hBlk :
      MeasuresLowEnergiesFG BlockEncodingCore.p450HBlocked 63 0.1 0.001
        (p450TwoGearEst 8 18) wBlk :=
    capped_perturbed_measuresLowEnergiesAt_box_tg 8 18 47487 mainHeff
      MultiGearQPE.exactPhaseGrad11RayUnitary threeGearWin_47487_10_7.base.uIdeal ζ hζ
      mainUB wBlk hVbox mainHeff_isHermitian hδH0 mainHeff_agree mainUB_sos
      threeGearWin_47487_10_7.base.ideal_mulVec_zero hPert
      hRef hδWUb0 hGap hgH11 hBud
  exact measuresLowEnergiesFG_embed_block
    (m_scr := scrAncillas 16 0 (MultiGearQPE.combARem 8 18 4 14) (midRemWidth 18 14) sRem)
    (thcHamiltonian P450.dfthc) 63 0.1 0.001
    (p450TwoGearEst 8 18) _ (measuresLowEnergiesFG_dfthc_of_p450HBlocked wBlk hBlk)

variable {Var : Type}

/-- Polymorphic `{Var : Type}` realization bundle. -/
def RealizesFGVar [Fintype Var] [DecidableEq Var] {n m : ℕ} [NeZero (2 ^ n)]
    (rSys : QRegister systemQubits n) (rAnc : QRegister m n)
    (hdisj : rSys.DisjointWires rAnc) (estimate : Fin (2 ^ m) → ℝ)
    (prog : DynamicCircuit Var n) : Prop :=
  ∃ W : Unitary (2 ^ (systemQubits_local + m)),
    MeasuresLowEnergiesFG (thcHamiltonian dfthc) 63 0.1 0.001 estimate W ∧
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W
      prog.compile

theorem fg_to_measuresLowEnergies [Fintype Var] [DecidableEq Var] {n m : ℕ} [NeZero (2 ^ n)]
    (rSys : QRegister systemQubits n) (rAnc : QRegister m n)
    (hdisj : rSys.DisjointWires rAnc) (dec : PhaseDecoder m)
    (prog : DynamicCircuit Var n)
    (hFG : RealizesFGVar rSys rAnc hdisj dec.energy prog) :
    ∃ W, MeasuresLowEnergies (thcHamiltonian dfthc) 63 0.1 0.001 dec W ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W
        prog.compile :=
  hFG

/-- Clean ancilla count (`217`, giving `116 + 217 = 333` total qubits). -/
def solutionAncillas : ℕ := SevenGearWalk333.mainAncillas

/-- Energy estimation circuit on `rSys` and `rAnc`. -/
def solutionProgram {n : ℕ} (v₀ : Var) (rSys : QRegister systemQubits n)
    (rAnc : QRegister solutionAncillas n) : DynamicCircuit Var n :=
  SevenGearWalk333.fast7gProg v₀ rSys rAnc

/-- Phase-estimation decoder on `solutionAncillas`. -/
def solutionDecoder : PhaseDecoder solutionAncillas where
  bits := 16
  register :=
    (QRegister.block 0
      (TopIntegrationBridge.actAncillas 16 11
        (BlockEncodingCore.mOutUB 8) (BlockEncodingCore.mMidUB 18))
      (by decide)).compose
      (TopIntegrationBridge.rQPEInAnc 16 11
        (BlockEncodingCore.mOutUB 8) (BlockEncodingCore.mMidUB 18))
  offset := ((-5788300336462799 / 154350387200000 : ℚ) : ℝ)
  scale := ((-121733 / 1250 : ℚ) : ℝ)

theorem solutionDecoder_energy_eq :
    solutionDecoder.energy = p450FourGearEst 8 18 4 14 149 := by
  funext a
  dsimp only [PhaseDecoder.energy, solutionDecoder, p450FourGearEst, qpeEstimate]
  rw [QRegister.extractIndex_compose, ← qpeDecodeEnergy_p450_fg_eq]
  rfl

theorem solution_fg_correctness [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v₀ : Var) (rSys : QRegister systemQubits n)
    (rAnc : QRegister solutionAncillas n) (hdisj : rSys.DisjointWires rAnc) :
    RealizesFGVar rSys rAnc hdisj solutionDecoder.energy (solutionProgram v₀ rSys rAnc) := by
  let rSys' : SevenGearBondDefer.FGSysReg n := rSys
  let rAnc' : SevenGearBondDefer.FGAncReg 8 18 4 14 149 n := rAnc
  have hdisj' : rSys'.DisjointWires rAnc' := hdisj
  obtain ⟨W, hMeas, hReal⟩ :=
    SevenGearBondDefer.realizesEst_p450SymbolicSevenGear_of_box
      8 18 4 14 149 160 160 160 160 159 156
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      TwoGearQPEPhase5.regData_47487_7
      TailShiftWindow46847.threeGearWinCirc_47487_10_7
      TailShiftWindow46847.threeGearWin_47487_10_7
      TailShiftWindow46847.threeGearWin_47487_10_7_toCirc
      TailShiftWindow46847.threeGearWin_47487_10_7_cWinC
      (TailShiftThreeGear.tailShiftParams_47487_10 7) ()
      ApproxIqft16.fastIqft16Circuit ApproxIqft16.fastIqft16Circuit_count_toff
      (δIqft := 36 / 10 ^ 9) (ci := TwoGearBox.cFa) (wUb := TwoGearBox.w5)
      (by norm_num)
      (by
        unfold TwoGearBox.cFa
        norm_num)
      (by
        unfold TwoGearBox.w5
        exact TailShiftWindow46847.threeGearWin_47487_10_7_δWin.le)
      TailShiftBox.eRef_deep63_le
      ApproxIqft16.norm_fastIqft16Circuit_sub_le
      solutionDecoder.energy rSys' rAnc' hdisj'
      SevenGearWalk333.fast7gSevenGearCert
      (by norm_num)
      (TailShiftBox.tailShiftBox_fast_47487_10_7_deep63_dh5700
        (dh := TailShiftBox.dh4000)
        TailShiftBox.dhBounds_4000.1
        (by
          unfold TailShiftBox.dh4000
          norm_num))
      (solutionDecoder_energy_eq.symm ▸ fast7g_estTransferHyp 149)
  have hReal0 : RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys' Finset.univ rAnc' hdisj' W
      (SevenGearWalk333.fast7gUnitProg rSys' rAnc').compile := hReal
  exact (show RealizesFGVar rSys rAnc' hdisj' solutionDecoder.energy
      (SevenGearWalk333.fast7gProg v₀ rSys' rAnc') from
    ⟨W, hMeas, SevenGearWalk333.realizes_instUnitVar v₀ rSys' Finset.univ rAnc' hdisj' W
      (SevenGearWalk333.fast7gUnitProg rSys' rAnc') hReal0⟩)

theorem solution_const_cost {n : ℕ} (v₀ : Var) (rSys : QRegister systemQubits n)
    (rAnc : QRegister solutionAncillas n) :
    (solutionProgram v₀ rSys rAnc).count PrimitiveGate.TOFF = 0 ∧
      (systemQubits + solutionAncillas) * (solutionProgram v₀ rSys rAnc).count PrimitiveGate.T ≤
        436509499221 :=
  SevenGearWalk333.fast7gProg_const_cost v₀ rSys rAnc

attribute [irreducible] solutionAncillas solutionProgram solutionDecoder

end P450GroundEnergy.TopBridge

/-- Number of clean ancilla qubits `p450GroundEnergyProgram` uses, including the
phase-estimation register. -/
def p450GroundEnergyAncillas : ℕ := P450GroundEnergy.TopBridge.solutionAncillas

/-- Energy estimation circuit on system wires `rSys` and clean ancilla wires `rAnc`. -/
def p450GroundEnergyProgram {n : ℕ} (rSys : QRegister systemQubits n)
    (rAnc : QRegister p450GroundEnergyAncillas n) : DynamicCircuit Var n :=
  P450GroundEnergy.TopBridge.solutionProgram v rSys rAnc

/-- Decoder of the ancillas of `p450GroundEnergyProgram`. Fractions in it are written as
`((a / b : ℚ) : ℝ)`, since division in `ℝ` is noncomputable. -/
def p450GroundEnergyDecoder : PhaseDecoder p450GroundEnergyAncillas :=
  P450GroundEnergy.TopBridge.solutionDecoder

/-- `p450GroundEnergyProgram`, started with clean ancillas, realizes a unitary from which
`p450GroundEnergyDecoder` decodes the energy of every `63`-electron eigenstate of
`thcHamiltonian dfthc` within `0.1` Ha of the ground state with root-mean-square error `10⁻³` Ha,
and places no higher eigenstate below that window. With no catalyst, phase-gradient states are
prepared within the run. -/
theorem p450GroundEnergy_correctness {n : ℕ}
    (rSys : QRegister systemQubits n) (rAnc : QRegister p450GroundEnergyAncillas n)
    (hdisj : rSys.DisjointWires rAnc) :
    ∃ W, MeasuresLowEnergies (thcHamiltonian dfthc) 63 0.1 0.001 p450GroundEnergyDecoder W ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W
        (p450GroundEnergyProgram rSys rAnc).compile :=
  P450GroundEnergy.TopBridge.fg_to_measuresLowEnergies rSys rAnc hdisj p450GroundEnergyDecoder
    (p450GroundEnergyProgram rSys rAnc)
    (P450GroundEnergy.TopBridge.solution_fg_correctness v rSys rAnc hdisj)

/-- Claimed spacetime volume of `p450GroundEnergyProgram`. -/
def p450GroundEnergyConstCost : ℕ := 436509499221

/-- Over Clifford + `T` with measurements, the spacetime volume (qubits times `T` count) of
`p450GroundEnergyProgram` is at most `p450GroundEnergyConstCost`. `TOFF` gates are excluded, so
each Toffoli is costed by the Clifford + `T` construction the program uses, such as `4` `T` gates
with an ancilla and a measurement; measurements cost `0` and a `qIf` costs its worse branch. -/
theorem p450GroundEnergy_const_cost {n : ℕ} (rSys : QRegister systemQubits n)
    (rAnc : QRegister p450GroundEnergyAncillas n) :
    (p450GroundEnergyProgram rSys rAnc).count PrimitiveGate.TOFF = 0 ∧
      (systemQubits + p450GroundEnergyAncillas) *
          (p450GroundEnergyProgram rSys rAnc).count PrimitiveGate.T ≤
        p450GroundEnergyConstCost := by
  unfold p450GroundEnergyProgram p450GroundEnergyAncillas p450GroundEnergyConstCost
  exact P450GroundEnergy.TopBridge.solution_const_cost v rSys rAnc

end QuantumComputation.Specs
