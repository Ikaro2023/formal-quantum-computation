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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhaseGradRaySliceBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CatalystCleanBridge

/-!
# 11-Qubit Catalyst + Reduced-Reflection Master QPE Closure
Constructs the `11`-wire persistent phase-gradient catalyst register
(`CircuitModular.phaseGradientLowFactor 11 3`, `1,130 T`, `87 + sUb` ancillas at
`wOuter = 19, wInner2 = 26` for `sUb ≥ 74`) together with `16`-wire/step and `44`-wire reduced
Toffoli reflections:

1. **`preparePhaseGrad11` (`1,130 T`, `0 TOFF`):** Prepares `CircuitModular.phaseGradientLowFactor`
   at `(11, 3)` to `L2Operator` norm error `≤ 1e-8` (`≤ 1000 / 10 ^ 11`) by projecting the low `11`
   wires of `CliffordT.approxPhaseGrad14` and `CliffordT.exactPhaseGrad14Unitary`.
2. **Reduced-Reflection `11`-Cat Master Program & Gate Counts:** `p450MasterProgCat11ReducedFlex`
   with unconditional `.count .TOFF = 0` and `.count .T ≤ p450MasterCat11ReducedTCountFlex`.
3. **Stage-2 `11`-Cat Wrappers:** Inner-sandwich and forward/backward `11`-catalyst `U_B`
   wrappers (`3,692 + tSel` and `4,478 + tSel` `T` gates, `0 TOFF`).
4. **End-to-End Correctness & Rational RMSE Budgets:** `MeasuresLowEnergies_local` +
   `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace` for general and Stage-2 pulled `11`-catalyst
   walk pairs (plus `pulled_cat11_of_cat14`), together with pre-proved rational budget lemmas for
   `M = 48,895`, `M = 48,127`, and `M = 48,063`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge
open scoped Matrix

local instance (priority := 100) instNeZeroTwoPow (n : ℕ) : NeZero (2 ^ n) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n)⟩

/-! ## Section 1: 11-Catalyst-Qubit Layout & Subregisters -/

/-- Exact `11`-qubit target unitary whose action on `|0^11⟩` is
`CircuitModular.phaseGradientLowFactor 11 3` with zero global phase. -/
noncomputable def exactPhaseGrad11Unitary : Unitary (2 ^ 11) :=
  CliffordT.seqUnitary ((List.finRange 11).map fun r ↦
    (QRegister.singleton r).embedUnitary (CliffordT.pgWireLocalExact (Fin.castAdd 3 r)))

private noncomputable def exactPhaseGradHi3Unitary : Unitary (2 ^ 3) :=
  CliffordT.seqUnitary ((List.finRange 3).map fun j ↦
    (QRegister.singleton j).embedUnitary (CliffordT.pgWireLocalExact (Fin.natAdd 11 j)))

private theorem seqUnitary_append {d : ℕ} (xs ys : List (Unitary d)) :
    CliffordT.seqUnitary (xs ++ ys) = CliffordT.seqUnitary ys * CliffordT.seqUnitary xs := by
  induction xs with
  | nil => simp [CliffordT.seqUnitary]
  | cons u xs ih => simp [CliffordT.seqUnitary, ih, mul_assoc]

private theorem seqUnitary_embedUnitary {k n : ℕ} (r : QRegister k n)
    (us : List (Unitary (2 ^ k))) :
    CliffordT.seqUnitary (us.map r.embedUnitary) = r.embedUnitary (CliffordT.seqUnitary us) := by
  induction us with
  | nil => simp [CliffordT.seqUnitary]
  | cons u us ih => simp [CliffordT.seqUnitary, ih, ← QRegister.embedUnitary_mul]

private theorem exactPhaseGrad14_eq_split :
    CliffordT.exactPhaseGrad14Unitary =
      (Solution.CircuitModular.locRight 11 3).embedUnitary exactPhaseGradHi3Unitary *
        (Solution.CircuitModular.locLeft 11 3).embedUnitary exactPhaseGrad11Unitary := by
  have hfr : List.finRange 14 =
      (List.finRange 11).map (Fin.castAdd 3) ++ (List.finRange 3).map (Fin.natAdd 11) := by decide
  have hlo (r : Fin 11) :
      QRegister.singleton (Fin.castAdd 3 r) =
        (Solution.CircuitModular.locLeft 11 3).compose (QRegister.singleton r) :=
    CoherentAlias.qreg_ext fun i ↦ by
      fin_cases i; simp [Solution.CircuitModular.locLeft, Solution.CircuitModular.locLeftOf]
  have hhi (j : Fin 3) :
      QRegister.singleton (Fin.natAdd 11 j) =
        (Solution.CircuitModular.locRight 11 3).compose (QRegister.singleton j) :=
    CoherentAlias.qreg_ext fun i ↦ by
      fin_cases i; simp [Solution.CircuitModular.locRight, Solution.CircuitModular.locRightOf]
  unfold CliffordT.exactPhaseGrad14Unitary exactPhaseGradHi3Unitary exactPhaseGrad11Unitary
  rw [hfr, List.map_append, List.map_map, List.map_map, seqUnitary_append]
  have hm1 : ((List.finRange 11).map
      ((fun r ↦ (QRegister.singleton r).embedUnitary (CliffordT.pgWireLocalExact r)) ∘
        Fin.castAdd 3)) =
      ((List.finRange 11).map fun r ↦
        (QRegister.singleton r).embedUnitary (CliffordT.pgWireLocalExact (Fin.castAdd 3 r))).map
          (Solution.CircuitModular.locLeft 11 3).embedUnitary := by
    rw [List.map_map]; refine List.map_congr_left fun r _ ↦ ?_
    dsimp only [Function.comp_apply]; rw [hlo r, QRegister.embedUnitary_compose]
  have hm2 : ((List.finRange 3).map
      ((fun r ↦ (QRegister.singleton r).embedUnitary (CliffordT.pgWireLocalExact r)) ∘
        Fin.natAdd 11)) =
      ((List.finRange 3).map fun j ↦
        (QRegister.singleton j).embedUnitary (CliffordT.pgWireLocalExact (Fin.natAdd 11 j))).map
          (Solution.CircuitModular.locRight 11 3).embedUnitary := by
    rw [List.map_map]; refine List.map_congr_left fun j _ ↦ ?_
    dsimp only [Function.comp_apply]; rw [hhi j, QRegister.embedUnitary_compose]
  rw [hm1, hm2, seqUnitary_embedUnitary, seqUnitary_embedUnitary]

private theorem basisState_zero_eq_prodState (k b : ℕ) :
    basisState (0 : Fin (2 ^ (k + b))) =
      Solution.CircuitModular.prodState (basisState (0 : Fin (2 ^ k)))
        (basisState (0 : Fin (2 ^ b))) := by
  rw [← Solution.CircuitModular.tensorState_single_zero_eq_prodState]
  funext g
  have hiff : g = 0 ↔
      (Solution.CircuitModular.locLeft k b).extractIndex g = 0 ∧
        ((Solution.CircuitModular.locLeft k b).basisSplitEquiv g).2 = 0 := by
    constructor
    · rintro rfl
      refine ⟨(QRegister.extractIndex_eq_zero_iff _ _).mpr fun j ↦ basisBits_zero_at _ _, ?_⟩
      funext e; rw [QRegister.basisSplitEquiv_apply_snd, basisBits_zero_at]; rfl
    · rintro ⟨h1, h2⟩
      apply (Solution.CircuitModular.locLeft k b).basisSplitEquiv.injective
      apply Prod.ext
      · simpa [QRegister.basisSplitEquiv_apply_fst] using
          h1.trans ((QRegister.extractIndex_eq_zero_iff _ _).mpr fun j ↦ basisBits_zero_at _ _).symm
      · exact h2.trans (by
          funext e; rw [QRegister.basisSplitEquiv_apply_snd, basisBits_zero_at]; rfl)
  dsimp only [basisState, QRegister.tensorState]
  by_cases hg : g = 0
  · obtain ⟨h1, h2⟩ := hiff.mp hg
    subst hg
    rw [h1, h2]
    simp
  · have hnot := mt hiff.mpr hg
    by_cases h1 : (Solution.CircuitModular.locLeft k b).extractIndex g = 0
    · have h2 : ((Solution.CircuitModular.locLeft k b).basisSplitEquiv g).2 ≠ 0 :=
        fun hc ↦ hnot ⟨h1, hc⟩
      simp [Pi.single_apply, hg, h2]
    · simp [Pi.single_apply, hg, h1]

private theorem exactPhaseGradHi3Unitary_mulVec_zero_zero :
    (exactPhaseGradHi3Unitary.1 *ᵥ basisState 0) 0 =
      QuantumComputation.Specs.phaseGradientState 3 0 := by
  have hs0 : QRegister.singleton (0 : Fin 3) = Solution.CircuitModular.locLeft 1 2 :=
    CoherentAlias.qreg_ext fun i ↦ by fin_cases i; rfl
  have hs1 : QRegister.singleton (1 : Fin 3) =
      (Solution.CircuitModular.locRight 1 2).compose (Solution.CircuitModular.locLeft 1 1) :=
    CoherentAlias.qreg_ext fun i ↦ by fin_cases i; rfl
  have hs2 : QRegister.singleton (2 : Fin 3) =
      (Solution.CircuitModular.locRight 1 2).compose (Solution.CircuitModular.locRight 1 1) :=
    CoherentAlias.qreg_ext fun i ↦ by fin_cases i; rfl
  let w0 := (CliffordT.pgWireLocalExact ⟨11, by decide⟩).1 *ᵥ basisState (0 : Fin 2)
  let w1 := (CliffordT.pgWireLocalExact ⟨12, by decide⟩).1 *ᵥ basisState (0 : Fin 2)
  let w2 := (CliffordT.pgWireLocalExact ⟨13, by decide⟩).1 *ᵥ basisState (0 : Fin 2)
  have hfMain : List.finRange 3 = [0, 1, 2] := by decide
  have hb3 : basisState (0 : Fin (2 ^ 3)) =
      Solution.CircuitModular.prodState (k := 1) (b := 2) (basisState 0)
        (Solution.CircuitModular.prodState (k := 1) (b := 1) (basisState 0) (basisState 0)) := by
    rw [← basisState_zero_eq_prodState 1 1]
    exact basisState_zero_eq_prodState 1 2
  have hvec : exactPhaseGradHi3Unitary.1 *ᵥ basisState (0 : Fin (2 ^ 3)) =
      Solution.CircuitModular.prodState (k := 1) (b := 2) w0
        (Solution.CircuitModular.prodState (k := 1) (b := 1) w1 w2) := by
    unfold exactPhaseGradHi3Unitary
    rw [hfMain, hb3]
    simp only [List.map, CliffordT.seqUnitary, one_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [show Fin.natAdd 11 (0 : Fin 3) = ⟨11, by decide⟩ from rfl,
      show Fin.natAdd 11 (1 : Fin 3) = ⟨12, by decide⟩ from rfl,
      show Fin.natAdd 11 (2 : Fin 3) = ⟨13, by decide⟩ from rfl, hs0, hs1, hs2]
    simp only [QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
    rw [Solution.CircuitModular.embedMatrix_locLeft_mulVec_prodState,
      Solution.CircuitModular.embedMatrix_locRight_mulVec_prodState,
      Solution.CircuitModular.embedMatrix_locLeft_mulVec_prodState,
      Solution.CircuitModular.embedMatrix_locRight_mulVec_prodState,
      Solution.CircuitModular.embedMatrix_locRight_mulVec_prodState]
  rw [hvec]
  have hex0 {k b : ℕ} (r : QRegister k b) : r.extractIndex (0 : Fin (2 ^ b)) = 0 :=
    (QRegister.extractIndex_eq_zero_iff _ _).mpr fun _ ↦ basisBits_zero_at _ _
  dsimp only [Solution.CircuitModular.prodState, Solution.CircuitModular.prodStateOf]
  rw [hex0, hex0, hex0, hex0]
  have hw0 : w0 0 = (√2 : ℂ)⁻¹ := by
    simp [w0, CliffordT.pgWireLocalExact, Qubit.T, Qubit.H, Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hw1 : w1 0 = (√2 : ℂ)⁻¹ := by
    simp [w1, CliffordT.pgWireLocalExact, Qubit.S, Qubit.H, Matrix.star_eq_conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hw2 : w2 0 = (√2 : ℂ)⁻¹ := by
    simp [w2, CliffordT.pgWireLocalExact, Qubit.Z, Qubit.H]
  rw [hw0, hw1, hw2]
  unfold QuantumComputation.Specs.phaseGradientState
  simp only [Fin.val_zero, CharP.cast_eq_zero, mul_zero, neg_zero, zero_div, Complex.exp_zero,
    mul_one]
  have h8 : √(2 ^ 3 : ℝ) = √2 * (√2 * √2) := by
    rw [show (2 ^ 3 : ℝ) = 2 * (2 * 2) by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  rw [h8]
  push_cast
  ring

/-- `exactPhaseGrad11Unitary` maps `|0^11⟩` to `CircuitModular.phaseGradientLowFactor 11 3` with
  zero
global phase. -/
theorem exactPhaseGrad11Unitary_mulVec_zero :
    exactPhaseGrad11Unitary.1 *ᵥ basisState 0 =
        Solution.CircuitModular.phaseGradientLowFactor 11 3 := by
  let v11 := exactPhaseGrad11Unitary.1 *ᵥ basisState (0 : Fin (2 ^ 11))
  let v3 := exactPhaseGradHi3Unitary.1 *ᵥ basisState (0 : Fin (2 ^ 3))
  have hsplit14 :
      Solution.CircuitModular.prodState (k := 11) (b := 3) v11 v3 =
        Solution.CircuitModular.prodState (Solution.CircuitModular.phaseGradientLowFactor 11 3)
          (QuantumComputation.Specs.phaseGradientState 3) := by
    change _ =
      Solution.CircuitModular.prodState (Solution.CircuitModular.phaseGradientFineLow 11 3) _
    rw [← Solution.CircuitModular.phaseGradientState_eq_prodState_top 11 3]
    change _ = QuantumComputation.Specs.phaseGradientState 14
    rw [← CliffordT.exactPhaseGrad14Unitary_mulVec_zero, exactPhaseGrad14_eq_split]
    change _ = ((Solution.CircuitModular.locRight 11 3).embedMatrix exactPhaseGradHi3Unitary.1 *
      (Solution.CircuitModular.locLeft 11 3).embedMatrix exactPhaseGrad11Unitary.1) *ᵥ
      basisState (0 : Fin (2 ^ (11 + 3)))
    rw [← Matrix.mulVec_mulVec, basisState_zero_eq_prodState 11 3,
      Solution.CircuitModular.embedMatrix_locLeft_mulVec_prodState,
      Solution.CircuitModular.embedMatrix_locRight_mulVec_prodState]
  have h30_ne : QuantumComputation.Specs.phaseGradientState 3 0 ≠ 0 := by
    unfold QuantumComputation.Specs.phaseGradientState
    simp only [Fin.val_zero, CharP.cast_eq_zero, mul_zero, neg_zero, zero_div, Complex.exp_zero,
      mul_one, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero]
    positivity
  funext k
  have hz := congrFun hsplit14 ((Solution.CircuitModular.blockSplitEquiv 11 3).symm (k, 0))
  dsimp only [Solution.CircuitModular.prodState, Solution.CircuitModular.prodStateOf] at hz
  rw [Solution.CircuitModular.extractIndex_locLeft_symm,
    Solution.CircuitModular.extractIndex_locRight_symm] at hz
  dsimp only [v3] at hz
  rw [exactPhaseGradHi3Unitary_mulVec_zero_zero] at hz
  exact mul_right_cancel₀ h30_ne hz

section Phase2Cat11Wrappers

open QProg HermitianMat
open scoped ComplexOrder MatrixOrder

end Phase2Cat11Wrappers

/-! ## Section 4: Clean-Zero & Reduced-Reflection `CleanRealizes` Lifting on `Cat11` -/

section CleanZeroLiftingCat11

open QProg HermitianMat
open scoped ComplexOrder MatrixOrder

end CleanZeroLiftingCat11

/-! ## Section 5: 11-Catalyst Pulled-Reflection Correctness & Rational RMSE Budgets -/

section SpectralCat11

open Matrix Real
open scoped BigOperators Matrix.Norms.L2Operator

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound
  exactPhaseGrad11Unitary

end SpectralCat11

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
