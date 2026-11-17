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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WindowedCsaStageA
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BadElecSyndrome


@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section FermionicKrylovSegBridge

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
namespace FermionicKrylovSegBridge
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowK2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open PhaseGradSignalRot hiding IntertwinesCat
open TFreeLaurentGQSP hiding norm_mul_le_of_left_le_one norm_mul_le_of_right_le_one
open CatalyzedLaurentGQSP BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open PosMomSelectDynamic (unitaryConj_conjTranspose)
open PosMomSelectSandwich (slotBitProj)
open TwosCompAndWire0Cancel
  (smToTwosSysUnitary smToTwosSysUnitary_conjTranspose smToTwosSys_comm_fermionicProjector)
open SingleRBEGridGuardWalk
open GridGuard654ReflAux (electronFieldLinearIdx ctrlLocalUnitary)
open Slots01AndGridGuardBridge
  (ctrlInvolutionMatrix elecAxisWord6 elecAxisWord6_ne_32_of_isGridState)
open SixSlotEndpointJunctionBridge
  (gridValidBool gridValidBool_eq_true_iff diagProj_gridValidBool_eq_specsGridProjector)
open FullSysCatSegmentBridge
open BiGqspSegmentSpine
open PolymorphicTopClosure
open GeneralBetaAndAlphaTopEndpoint
open SingleCatClosure
open GidneySignalRotPart1
open HarmonicTwoAngleBridge hiding gidneyTwoAngleRotToffEquiv biPrefixTwoAngleRotToffSum
  biPrefixTwoAngleRotToffSum_eq_univ_sum uSignalRotTwoAngle43 uSignalRotTwoAngleSingleCat
open HoistBorrow42TwoAngleBridge
  (gidneyTwoAngleRotToffEquiv biPrefixTwoAngleRotToffSum biPrefixTwoAngleRotToffSum_eq_univ_sum
  uSignalRotTwoAngleSingleCat fixesLow3924_uSignalRotTwoAngleSingleCat80)
open InterWalkRSum42Hoist
  (qreg_ext qreg_block_apply kActOrig mActHoist kFull80 rAct0 rBEOrig rSegOrig FixesLow3924
  low3924Bits h3924_be h3924_actOrig embedUnitary_inv_symm E_stream42
  embedAct0_fixesLow3924_comm_E_stream42 fixesLow3924_optXSingleCat PreservesFeature)
open GhostGuardCircuitBridge (singleRBEReflNegMatrix_eq_phaseOp_neg_one)
open HoistBorrow42ProjBridge
  (RealizesOnProj pow_mul_intertwine embedUnitary_pow basisOutcomeProjector_concat_zero
  cleanBasisSchedule_correctness_onProj_gen)
open HarmonicScheduleBridge (hoAncillasM)
open FullSysWalkStepEndpoint
  (fullSys_zero_add_le cleanBasisScheduleProgram cleanBasisSchedule_perHorizon_const_cost)
open Leaf4Ext48TopStitch
open GqspCatPrepSub600Nano
  (catPrepErrUltra1q cInitUltraSingleCat_T vPrepUltraSingleCat vInvUltraSingleCat
  catalyst_sandwich_ultra_singleCat)
open GqspCleanCoinAndGuardBridge
  (sum_gidneyTwoAngleRotToffEquiv_zero_left cPreOneAngle cPostOneAngle cPreOneAngle_counts
  cPostOneAngle_counts cPost_mul_physBiTwoAngleSegment_zero_mul_cPre cPreOneAngle_comm_E_segExt
  cPostOneAngle_comm_E_segExt vPrepUltraExtHk vInvUltraExtHk mkInitUltraExtHkDyn
  mkUninitUltraExtHkDyn count_toff_mkInitUltraExtHkDyn count_toff_mkUninitUltraExtHkDyn
  count_t_mkInitUltraExtHk_add_uninit_le vPrepUltraExtHk_mul_pZeroInitExt
  uHadIdleFull_mul_vPrepUltra_comm_pZeroInitExt mkInitUltraExtHkDyn_realizesOnProj
  mkUninitUltraExtHkDyn_realizesOnProj OneAngleExtHkHorizonCertTable GenBetaExtHkSelAndPertSpec)
open Guard_SlimGuardIdleBeAndOneAngleSeg
  (wSegSingleCatExt48_TwoRot_T gidneyRotToffEquiv_le_twoAngle_zero_left biCode_zero_eq)
open SyndromeUncomp
  (badElecCount elecFieldBadBits elecFieldBadBits_eq_true_iff
  elecAxisWord6_val_eq_32_iff_signMagnitude fullSysGuardReflUnitaryGen guardPolSingleCatGen
  uGuardWrapTwoAngleSingleCatGen)
theorem ite_true_eq {α : Sort _} {c : Prop} [Decidable c] {a b : α} (hc : c) :
    (if c then a else b) = a := by
  simp [hc]
-- ============================================================================
-- Section 0: Generalized `bValid` Guard Bundles, Projections & Structural Constructors
-- ============================================================================
set_option exponentiation.threshold 5000 in
/-- Generalized 1-angle unheld-syndrome (`tGuard + 2 * gidneyRotToffEquiv D_d.val`) `ExtHk` guard
  bundle
for an arbitrary syndrome predicate `bValid : Fin (2 ^ systemQubits) → Bool`. -/
structure OneAngleUnheldExtHkGuardSpecBundleGen
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (mWork k_idle : ℕ) (hk : k_idle ≤ 48) (tGuard : ℕ) where
  dGuard1 : ∀ {Var : Type} {n : ℕ}, Bool → Bool → Fin (2 ^ 42) → Var →
    ∀ (rAct : QRegister kFull80 n) (rWork : QRegister mWork n),
      rAct.DisjointWires rWork → DynamicCircuit Var n
  hToff : ∀ {Var : Type} {n : ℕ} (bPre bPost : Bool) (D_d : Fin (2 ^ 42)) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dGuard1 bPre bPost D_d v rAct rWork hDisj).count TOFF = 0
  hT : ∀ {Var : Type} {n : ℕ} (bPre bPost : Bool) (D_d : Fin (2 ^ 42)) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dGuard1 bPre bPost D_d v rAct rWork hDisj).count T ≤
      tGuard + 2 * gidneyRotToffEquiv D_d.val
  hRealizes : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (bPre bPost : Bool) (D_d : Fin (2 ^ 42)) (_hD : 2 ^ (k_idle - 6) ∣ D_d.val) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    RealizesOnProj (pHoistExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary
        (rAct0.embedUnitary
          (uGuardWrapTwoAngleSingleCatGen bValid (by decide : 42 ≤ 48) bPre bPost 0 D_d)))
      (dGuard1 bPre bPost D_d v rAct rWork hDisj)
set_option exponentiation.threshold 5000 in
/-- Generalized 2-kick clean-carry (`tGuard + 2 * gidneyRotToffEquiv C_d.val + 2 *
  gidneyRotToffEquiv D_d.val`)
`ExtHk` guard bundle for an arbitrary syndrome predicate `bValid`. -/
structure GidneyTwoKickExtHkGuardSpecBundleGen
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (mWork k_idle : ℕ) (hk : k_idle ≤ 48) (tGuard : ℕ) where
  dGuardWrap : ∀ {Var : Type} {n : ℕ},
    Bool → Bool → Fin (2 ^ 42) → Fin (2 ^ 42) → Var →
    (rAct : QRegister kFull80 n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  hToff : ∀ {Var : Type} {n : ℕ} (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42)) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dGuardWrap bPre bPost C_d D_d v rAct rWork hDisj).count TOFF = 0
  hT : ∀ {Var : Type} {n : ℕ} (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42)) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dGuardWrap bPre bPost C_d D_d v rAct rWork hDisj).count T ≤
      tGuard + 2 * gidneyRotToffEquiv C_d.val + 2 * gidneyRotToffEquiv D_d.val
  hRealizes : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (_hC : 2 ^ (k_idle - 6) ∣ C_d.val) (_hD : 2 ^ (k_idle - 6) ∣ D_d.val) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    RealizesOnProj (pHoistExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary
        (rAct0.embedUnitary
          (uGuardWrapTwoAngleSingleCatGen bValid (by decide : 42 ≤ 48) bPre bPost C_d D_d)))
      (dGuardWrap bPre bPost C_d D_d v rAct rWork hDisj)
set_option exponentiation.threshold 5000 in
/-- Setting `C_d = 0` on `GidneyTwoKickExtHkGuardSpecBundleGen` yields a zero-overhead
`OneAngleUnheldExtHkGuardSpecBundleGen` (`tGuard + 2 * gidneyRotToffEquiv D_d.val`). -/
def GidneyTwoKickExtHkGuardSpecBundleGen.toOneAngleUnheld
    {bValid : Fin (2 ^ systemQubits) → Bool}
    {mWork k_idle tGuard : ℕ} {hk : k_idle ≤ 48}
    (B : GidneyTwoKickExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard) :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard where
  dGuard1 bPre bPost D_d v rAct rWork hDisj :=
    B.dGuardWrap bPre bPost 0 D_d v rAct rWork hDisj
  hToff bPre bPost D_d v rAct rWork hDisj :=
    B.hToff bPre bPost 0 D_d v rAct rWork hDisj
  hT bPre bPost D_d v rAct rWork hDisj := by
    have hr0 : gidneyRotToffEquiv ((0 : Fin (2 ^ 42))).val = 0 := by rw [Fin.val_zero]; decide
    have h := B.hT bPre bPost 0 D_d v rAct rWork hDisj
    rw [hr0] at h
    omega
  hRealizes bPre bPost D_d hD v rAct rWork hDisj :=
    B.hRealizes bPre bPost 0 D_d (Nat.dvd_zero _) hD v rAct rWork hDisj
/-- `fullSysRawBEUnitary` is Hermitian (`U_raw.1ᴴ = U_raw.1`) for every configuration `c`. -/
theorem fullSysRawBEUnitary_conjTranspose {mPayload mPGTwist : ℕ}
    (qft : FullSysQft654Bundle) (prep : FullSysPrepareBundle mPayload)
    (sel : FullSysSelectOracleBundle mPayload mPGTwist) (c : Configuration) :
    (fullSysRawBEUnitary qft prep sel c).1ᴴ = (fullSysRawBEUnitary qft prep sel c).1 := by
  have hSelSA : (fullSysSelectEffUnitary qft sel c).1ᴴ =
      (fullSysSelectEffUnitary qft sel c).1 :=
    (fullSysSelectEffUnitary_conjTranspose_and_split qft sel c).2
  have hEmbSA : ((beCoreBlock mPayload).embedUnitary (fullSysSelectEffUnitary qft sel c)).1ᴴ =
      ((beCoreBlock mPayload).embedUnitary (fullSysSelectEffUnitary qft sel c)).1 := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_conjTranspose, hSelSA]
  exact unitaryConj_conjTranspose hEmbSA
/-- `fullSysRawBEUnitary` is an exact unitary involution (`U_raw * U_raw = 1`). -/
theorem fullSysRawBEUnitary_mul_self {mPayload mPGTwist : ℕ} (qft : FullSysQft654Bundle)
    (prep : FullSysPrepareBundle mPayload)
    (sel : FullSysSelectOracleBundle mPayload mPGTwist) (c : Configuration) :
    fullSysRawBEUnitary qft prep sel c * fullSysRawBEUnitary qft prep sel c = 1 := by
  have hInv : (fullSysRawBEUnitary qft prep sel c)⁻¹ = fullSysRawBEUnitary qft prep sel c :=
    Subtype.ext (fullSysRawBEUnitary_conjTranspose qft prep sel c)
  calc fullSysRawBEUnitary qft prep sel c * fullSysRawBEUnitary qft prep sel c
    _ = fullSysRawBEUnitary qft prep sel c * (fullSysRawBEUnitary qft prep sel c)⁻¹ := by
          nth_rw 2 [← hInv]
    _ = 1 := mul_inv_cancel _
theorem fullSysRawBEUnitary_val_mul_self {mPayload mPGTwist : ℕ} (qft : FullSysQft654Bundle)
    (prep : FullSysPrepareBundle mPayload)
    (sel : FullSysSelectOracleBundle mPayload mPGTwist) (c : Configuration) :
    (fullSysRawBEUnitary qft prep sel c).1 * (fullSysRawBEUnitary qft prep sel c).1 = 1 :=
    congrArg Subtype.val (fullSysRawBEUnitary_mul_self qft prep sel c)
/-- Boolean predicate on `systemQubits` asserting at most `K` electrons carry `-0` (`100000₂`). -/
def badElecLeBool (K : ℕ) (x : Fin (2 ^ systemQubits)) : Bool := decide (badElecCount x ≤ K)
/-- `≤ 3`-bad-electron Krylov subspace indicator on `systemQubits`. -/
abbrev krylov3Bool : Fin (2 ^ systemQubits) → Bool := badElecLeBool 3
/-- Diagonal projector onto `badElecCount x ≤ 3` on `systemQubits`. -/
noncomputable abbrev krylov3Proj : Operator (2 ^ systemQubits) :=
  diagProj systemQubits krylov3Bool
/-- Diagonal projector onto `badElecCount x = 0` (`badElecCount x ≤ 0`) on `systemQubits`. -/
noncomputable abbrev bad0Proj : Operator (2 ^ systemQubits) :=
  diagProj systemQubits (badElecLeBool 0)
theorem h3924_sys : 3924 ≤ systemQubits := by
  dsimp [systemQubits, numElectrons, electronBits, projectileBits]
  omega
theorem gridValidBool_imp_badElecCount_eq_zero {x : Fin (2 ^ systemQubits)}
    (hx : gridValidBool x = true) : badElecCount x = 0 := by
  have hg : IsGridState x := (gridValidBool_eq_true_iff x).mp hx
  unfold badElecCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  simp only [decide_eq_true_iff, not_or]
  exact ⟨elecAxisWord6_ne_32_of_isGridState hg i 0, elecAxisWord6_ne_32_of_isGridState hg i 1,
    elecAxisWord6_ne_32_of_isGridState hg i 2⟩
theorem diagProj_mul_eq_right_of_imp {k : ℕ} {p q : Fin (2 ^ k) → Bool}
    (h : ∀ x, q x = true → p x = true) : diagProj k p * diagProj k q = diagProj k q := by
  unfold diagProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  by_cases hq : q x = true
  · rw [hq, h x hq]; simp
  · simp [hq]
theorem bad0Proj_mul_diagProj_gridValidBool : bad0Proj * diagProj systemQubits gridValidBool =
    diagProj systemQubits gridValidBool := diagProj_mul_eq_right_of_imp fun _ hx ↦
    decide_eq_true (Nat.le_zero.mpr (gridValidBool_imp_badElecCount_eq_zero hx))
theorem krylov3Proj_mul_diagProj_gridValidBool :
    krylov3Proj * diagProj systemQubits gridValidBool = diagProj systemQubits gridValidBool :=
  diagProj_mul_eq_right_of_imp fun _ hx ↦
    decide_eq_true (by rw [gridValidBool_imp_badElecCount_eq_zero hx]; decide)
theorem diagProj_eq_on_krylov3 {bValid : Fin (2 ^ systemQubits) → Bool}
    (hb : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x) : diagProj systemQubits bValid
    * krylov3Proj = diagProj systemQubits gridValidBool * krylov3Proj := by
  unfold krylov3Proj krylov3Bool badElecLeBool diagProj
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  by_cases hk : badElecCount x ≤ 3
  · rw [hb x hk]
  · simp [hk]
theorem embedMatrix_diagProj_eq_diagonal {k n : ℕ} (r : QRegister k n) (p : Fin (2 ^ k) → Bool) :
    r.embedMatrix (diagProj k p) =
      Matrix.diagonal (fun z : Fin (2 ^ n) ↦ if p (r.extractIndex z) then (1 : ℂ) else 0) := by
  ext i j
  rw [QRegister.embedMatrix_apply, diagProj]
  by_cases hij : i = j
  · subst hij; simp
  · by_cases hAg : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2
    · have hne_ex : r.extractIndex i ≠ r.extractIndex j := fun hex ↦
        hij (r.basisSplitEquiv.injective (Prod.ext hex hAg))
      simp [hij, hAg, Matrix.diagonal_apply_ne _ hne_ex]
    · simp [hij, hAg]
theorem embedMatrix_diagProj_apply_eq {k n : ℕ} (r : QRegister k n) (p : Fin (2 ^ k) → Bool)
    (i : Fin (2 ^ n)) :
    r.embedMatrix (diagProj k p) i i = if p (r.extractIndex i) then (1 : ℂ) else 0 := by
  rw [embedMatrix_diagProj_eq_diagonal, Matrix.diagonal_apply_eq]
theorem embedMatrix_diagProj_apply_ne {k n : ℕ} (r : QRegister k n) (p : Fin (2 ^ k) → Bool)
    {i j : Fin (2 ^ n)} (h : i ≠ j) : r.embedMatrix (diagProj k p) i j = 0 := by
  rw [embedMatrix_diagProj_eq_diagonal, Matrix.diagonal_apply_ne _ h]
theorem mul_embedMatrix_diagProj_apply {k n : ℕ} (M : Operator (2 ^ n)) (r : QRegister k n)
    (p : Fin (2 ^ k) → Bool) (i j : Fin (2 ^ n)) : (M * r.embedMatrix (diagProj k p)) i j = M
    i j * (if p (r.extractIndex j) then (1 : ℂ) else 0) := by
  change (∑ z : Fin (2 ^ n), M i z * r.embedMatrix (diagProj k p) z j) = _
  exact (Finset.sum_eq_single j
    (fun z _ hzj ↦ by rw [embedMatrix_diagProj_apply_ne r p hzj, mul_zero])
    (fun hj ↦ absurd (Finset.mem_univ j) hj)).trans
    (by rw [embedMatrix_diagProj_apply_eq])
theorem embedMatrix_diagProj_mul_apply {k n : ℕ} (r : QRegister k n) (p : Fin (2 ^ k) → Bool)
    (M : Operator (2 ^ n)) (i j : Fin (2 ^ n)) : (r.embedMatrix (diagProj k p) * M) i j =
    (if p (r.extractIndex i) then (1 : ℂ) else 0) * M i j := by
  change (∑ z : Fin (2 ^ n), r.embedMatrix (diagProj k p) i z * M z j) = _
  exact (Finset.sum_eq_single i
    (fun z _ hzi ↦ by rw [embedMatrix_diagProj_apply_ne r p hzi.symm, zero_mul])
    (fun hi ↦ absurd (Finset.mem_univ i) hi)).trans
    (by rw [embedMatrix_diagProj_apply_eq])
theorem projGridAncZero_eq_on_krylov3 {m : ℕ} {bValid : Fin (2 ^ systemQubits) → Bool}
    (hb : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x)
    {Y : Operator (2 ^ (systemQubits + m))}
    (hY : (QRegister.block 0 systemQubits (by omega)).embedMatrix krylov3Proj * Y = Y) :
    projGridAncZero systemQubits m (diagProj systemQubits bValid) * Y =
      projGridAncZero systemQubits m (diagProj systemQubits gridValidBool) * Y := by
  let rSys : QRegister systemQubits (systemQubits + m) := QRegister.block 0 systemQubits (by omega)
  let rAnc : QRegister m (systemQubits + m) := QRegister.block systemQubits m le_rfl
  have hDisj : rSys.DisjointWires rAnc := disj_of_val_ne fun i j ↦ by
    simp only [rSys, rAnc, qreg_block_apply]; have := i.isLt; omega
  have hComm : rAnc.basisOutcomeProjector 0 * rSys.embedMatrix krylov3Proj =
      rSys.embedMatrix krylov3Proj * rAnc.basisOutcomeProjector 0 :=
    ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rSys) rAnc hDisj krylov3Proj
      0).symm
  have hAbsorb (p : Fin (2 ^ systemQubits) → Bool) :
      projGridAncZero systemQubits m (diagProj systemQubits p) * Y =
        rSys.embedMatrix (diagProj systemQubits p * krylov3Proj) *
          (rAnc.basisOutcomeProjector 0 * Y) := by
    change (rSys.embedMatrix (diagProj systemQubits p) * rAnc.basisOutcomeProjector 0) * Y = _
    calc (rSys.embedMatrix (diagProj systemQubits p) * rAnc.basisOutcomeProjector 0) * Y
      _ = rSys.embedMatrix (diagProj systemQubits p) *
            ((rAnc.basisOutcomeProjector 0 * rSys.embedMatrix krylov3Proj) * Y) := by
            rw [Matrix.mul_assoc (rAnc.basisOutcomeProjector 0), hY, Matrix.mul_assoc]
      _ = rSys.embedMatrix (diagProj systemQubits p * krylov3Proj) *
            (rAnc.basisOutcomeProjector 0 * Y) := by
            rw [hComm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rSys.embedMatrix_mul,
              Matrix.mul_assoc]
  rw [hAbsorb bValid, diagProj_eq_on_krylov3 hb, ← hAbsorb gridValidBool]
theorem physGridReflGen_eq_on_krylov3 {m : ℕ} {bValid : Fin (2 ^ systemQubits) → Bool}
    (hb : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x)
    {Y : Operator (2 ^ (systemQubits + m))} (hY : (QRegister.block 0 systemQubits
    (by omega)).embedMatrix krylov3Proj * Y = Y) : physGridReflGen systemQubits m bValid * Y =
    physGridReflGen systemQubits m gridValidBool * Y := by
  unfold physGridReflGen singleRBEReflMatrix reflOfProj
  rw [Matrix.sub_mul, Matrix.sub_mul, smul_mul_assoc, smul_mul_assoc,
    projGridAncZero_eq_on_krylov3 hb hY]
theorem badElecCount_eq_of_low3924Bits_eq {x y : Fin (2 ^ systemQubits)}
    (hlow : low3924Bits h3924_sys x = low3924Bits h3924_sys y) :
    badElecCount x = badElecCount y := by
  have hbad (f : Fin 654) :
      elecFieldBadBits (basisBits systemQubits x) f =
        elecFieldBadBits (basisBits systemQubits y) f := by
    have hbit (u : Fin 6) :
        basisBits systemQubits x (electronFieldLinearIdx f u) =
          basisBits systemQubits y (electronFieldLinearIdx f u) :=
      congrFun hlow ⟨6 * f.val + u.val, by
        have := f.isLt
        have := u.isLt
        omega⟩
    unfold elecFieldBadBits
    simp only [fun u : Fin 5 ↦ hbit u.castSucc, hbit 5]
  have h32 (i : Fin numElectrons) (w : Fin 3) :
      ((elecAxisWord6 x i w).val = 32) ↔ ((elecAxisWord6 y i w).val = 32) := by
    let f : Fin 654 := ⟨3 * i.val + w.val, by
      have hi_lt : i.val < numElectrons := i.isLt
      have hw_lt : w.val < 3 := w.isLt
      dsimp [numElectrons] at hi_lt
      omega⟩
    have hi : (⟨f.val / 3, by dsimp [numElectrons]; omega⟩ : Fin numElectrons) = i :=
      Fin.ext (by dsimp [f]; omega)
    have hw : (⟨f.val % 3, by omega⟩ : Fin 3) = w := Fin.ext (by dsimp [f]; omega)
    have hfx := elecFieldBadBits_eq_true_iff x f
    have hfy := elecFieldBadBits_eq_true_iff y f
    rw [hi, hw] at hfx hfy
    rw [elecAxisWord6_val_eq_32_iff_signMagnitude, elecAxisWord6_val_eq_32_iff_signMagnitude,
      ← hfx, ← hfy, hbad f]
  unfold badElecCount
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_iff,
    h32 i 0, h32 i 1, h32 i 2]
/-- Canonical grid-valid `|0⟩_anc` projector on `systemQubits + m`. -/
noncomputable abbrev pgBE (m : ℕ) : Operator (2 ^ (systemQubits + m)) :=
  projGridAncZero systemQubits m (diagProj systemQubits gridValidBool)
/-- Core-level (`systemQubits + 3` wires) sufficient condition: `M` maps `badElecCount = 0` states
into `badElecCount ≤ 3` states on the `systemQubits` prefix. -/
def CoreOpMapsZeroBadToKrylov3 {mPayload : ℕ}
    (M : Operator (2 ^ (fullSysCoreWires mPayload))) : Prop :=
  let rSysCore : QRegister systemQubits (fullSysCoreWires mPayload) :=
    QRegister.block 0 systemQubits (by
      dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]; omega)
  rSysCore.embedMatrix krylov3Proj * (M * rSysCore.embedMatrix bad0Proj) =
    M * rSysCore.embedMatrix bad0Proj
/-- Pointwise matrix-entry constructor for `CoreOpMapsZeroBadToKrylov3`: whenever `M y x ≠ 0` and
`x` has `0` bad electrons, `y` has at most `3` bad electrons. -/
theorem coreOpMapsZeroBadToKrylov3_of_entry {mPayload : ℕ}
    {M : Operator (2 ^ (fullSysCoreWires mPayload))}
    (hEntry : ∀ y x : Fin (2 ^ (fullSysCoreWires mPayload)),
      let rSysCore : QRegister systemQubits (fullSysCoreWires mPayload) :=
        QRegister.block 0 systemQubits (by
          dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]; omega)
      M y x ≠ 0 → badElecCount (rSysCore.extractIndex x) = 0 →
        badElecCount (rSysCore.extractIndex y) ≤ 3) :
    CoreOpMapsZeroBadToKrylov3 M := by
  let rSysCore : QRegister systemQubits (fullSysCoreWires mPayload) :=
    QRegister.block 0 systemQubits (by
      dsimp [fullSysCoreWires, systemQubits, numElectrons, electronBits, projectileBits]; omega)
  change rSysCore.embedMatrix krylov3Proj * (M * rSysCore.embedMatrix bad0Proj) =
    M * rSysCore.embedMatrix bad0Proj
  ext y x
  rw [embedMatrix_diagProj_mul_apply, mul_embedMatrix_diagProj_apply]
  rcases eq_or_ne (M y x) 0 with h0 | h0
  · rw [h0, zero_mul, mul_zero]
  · by_cases hb0 : badElecLeBool 0 (rSysCore.extractIndex x) = true
    · have hk3 : krylov3Bool (rSysCore.extractIndex y) = true :=
        decide_eq_true (hEntry y x h0 (Nat.le_zero.mp (of_decide_eq_true hb0)))
      rw [hb0, hk3]
      simp
    · rw [Bool.eq_false_iff.mpr hb0]
      simp only [Bool.false_eq_true, ↓reduceIte, mul_zero]
/-- Abstract Bi-GQSP loop congruence on any invariant operator family `S : Operator (2 ^ n) →
  Prop`. -/
theorem biGqspGenLoopOp_congr_of_invariant {n : ℕ} (q_sig : Wire n)
    {W₁ Winv₁ W₂ Winv₂ : Operator (2 ^ n)} (G : ℕ → Operator 2)
    (S : Operator (2 ^ n) → Prop)
    (hAdd : ∀ {X Y}, S X → S Y → S (X + Y))
    (hSig : ∀ (M2 : Operator 2) {X}, S X → S ((QRegister.singleton q_sig).embedMatrix M2 * X))
    (hW : ∀ {X}, S X → W₁ * X = W₂ * X ∧ S (W₂ * X))
    (hWinv : ∀ {X}, S X → Winv₁ * X = Winv₂ * X ∧ S (Winv₂ * X)) :
    ∀ (t : ℕ) {X : Operator (2 ^ n)}, S X →
      biGqspGenLoopOp q_sig W₁ Winv₁ G t * X = biGqspGenLoopOp q_sig W₂ Winv₂ G t * X ∧
      S (biGqspGenLoopOp q_sig W₂ Winv₂ G t * X)
  | 0, X, hX => ⟨rfl, hSig (G 0) hX⟩
  | t + 1, X, hX => by
      obtain ⟨hEq_t, hS_t⟩ :=
        biGqspGenLoopOp_congr_of_invariant q_sig G S hAdd hSig hW hWinv t hX
      set Y := biGqspGenLoopOp q_sig W₂ Winv₂ G t * X
      have hP0 : S ((QRegister.singleton q_sig).basisOutcomeProjector 0 * Y) :=
        hSig (compProj 0) hS_t
      have hP1 : S ((QRegister.singleton q_sig).basisOutcomeProjector 1 * Y) :=
        hSig (compProj 1) hS_t
      obtain ⟨hW_eq, hW_S⟩ := hW hP0
      obtain ⟨hWinv_eq, hWinv_S⟩ := hWinv hP1
      have hStepEq : biWalkStepOp q_sig W₁ Winv₁ * Y = biWalkStepOp q_sig W₂ Winv₂ * Y := by
        unfold biWalkStepOp
        simp only [Matrix.add_mul, Matrix.mul_assoc, hW_eq, hWinv_eq]
      have hStepS : S (biWalkStepOp q_sig W₂ Winv₂ * Y) := by
        unfold biWalkStepOp
        rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
        exact hAdd hW_S hWinv_S
      dsimp only [biGqspGenLoopOp]
      refine ⟨?_, ?_⟩
      · simp only [Matrix.mul_assoc]
        rw [hEq_t]
        change (QRegister.singleton q_sig).embedMatrix (G (t + 1)) *
          (biWalkStepOp q_sig W₁ Winv₁ * Y) =
          (QRegister.singleton q_sig).embedMatrix (G (t + 1)) * (biWalkStepOp q_sig W₂ Winv₂ * Y)
        rw [hStepEq]
      · simp only [Matrix.mul_assoc]
        exact hSig (G (t + 1)) hStepS
private theorem seg_op_assoc {d : ℕ} (H A B C X : Operator d) :
    ((H * A * B * C) * H) * X = H * (A * (B * (C * (H * X)))) := by
  simp only [Matrix.mul_assoc]

/-- Abstract Bi-GQSP full segment congruence on any invariant operator family `S`. -/
theorem biGqspGenSegmentOp_congr_of_invariant {n : ℕ} (q_sig : Wire n)
    {W₁ Winv₁ W₂ Winv₂ : Operator (2 ^ n)} (G : ℕ → Operator 2) (M : ℕ)
    (S : Operator (2 ^ n) → Prop) (hAdd : ∀ {X Y}, S X → S Y → S (X + Y)) (hSig : ∀ (M2 :
    Operator 2) {X}, S X → S ((QRegister.singleton q_sig).embedMatrix M2 * X))
    (hW : ∀ {X}, S X → W₁ * X = W₂ * X ∧ S (W₂ * X))
    (hWinv : ∀ {X}, S X → Winv₁ * X = Winv₂ * X ∧ S (Winv₂ * X)) {X : Operator (2 ^ n)}
    (hX : S X) : biGqspGenSegmentOp q_sig W₁ Winv₁ G M * X = biGqspGenSegmentOp q_sig W₂ Winv₂
    G M * X ∧ S (biGqspGenSegmentOp q_sig W₂ Winv₂ G M * X) := by
  have hH_emb : (Circuit.H q_sig).eval.1 =
      (QRegister.singleton q_sig).embedMatrix (PrimitiveGate.H.eval).1 := by
    rw [Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val]
  let X₁ := (Circuit.H q_sig).eval.1 * X
  have hS₁ : S X₁ := by dsimp only [X₁]; rw [hH_emb]; exact hSig _ hX
  have hP0_1 : S ((QRegister.singleton q_sig).basisOutcomeProjector 0 * X₁) :=
    hSig (compProj 0) hS₁
  have hP1_1 : S ((QRegister.singleton q_sig).basisOutcomeProjector 1 * X₁) :=
    hSig (compProj 1) hS₁
  obtain ⟨hC1_W, hC1_WS⟩ := hW hP1_1
  let P0 := (QRegister.singleton q_sig).basisOutcomeProjector 0
  let P1 := (QRegister.singleton q_sig).basisOutcomeProjector 1
  have hC1_eq : (P0 + W₁ * P1) * X₁ = (P0 + W₂ * P1) * X₁ := by
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hC1_W]
  let X₂ := (P0 + W₂ * P1) * X₁
  have hS₂ : S X₂ := by
    dsimp only [X₂]; rw [Matrix.add_mul, Matrix.mul_assoc]; exact hAdd hP0_1 hC1_WS
  obtain ⟨hLoop_eq, hS₃⟩ :=
    biGqspGenLoopOp_congr_of_invariant q_sig G S hAdd hSig hW hWinv M hS₂
  let X₃ := biGqspGenLoopOp q_sig W₂ Winv₂ G M * X₂
  have hP0_3 : S (P0 * X₃) := hSig (compProj 0) hS₃
  have hP1_3 : S (P1 * X₃) := hSig (compProj 1) hS₃
  obtain ⟨hC0_Winv, hC0_WinvS⟩ := hWinv hP0_3
  have hC0_eq : (Winv₁ * P0 + P1) * X₃ = (Winv₂ * P0 + P1) * X₃ := by
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hC0_Winv]
  let X₄ := (Winv₂ * P0 + P1) * X₃
  have hS₄ : S X₄ := by
    dsimp only [X₄]; rw [Matrix.add_mul, Matrix.mul_assoc]; exact hAdd hC0_WinvS hP1_3
  unfold biGqspGenSegmentOp
  dsimp only
  refine ⟨?_, ?_⟩
  · dsimp only [X₁, X₂, X₃] at hC1_eq hLoop_eq hC0_eq
    rw [seg_op_assoc, seg_op_assoc, hC1_eq, hLoop_eq, hC0_eq]
  · change S ((((Circuit.H q_sig).eval.1 * (Winv₂ * P0 + P1) *
        biGqspGenLoopOp q_sig W₂ Winv₂ G M * (P0 + W₂ * P1)) * (Circuit.H q_sig).eval.1) * X)
    rw [seg_op_assoc, hH_emb]
    exact hSig _ hS₄
/-- Congruence for `ApproximatesTimeEvolution` when two unitaries agree on `P ⊗ |0⟩⟨0|_anc`. -/
theorem approximatesTimeEvolution_congr_mul_gridAncZero
    {m : ℕ} {H P : Operator (2 ^ systemQubits)} {t ε : ℝ}
    {W₁ W₂ : Unitary (2 ^ (systemQubits + m))}
    (hEq :
      let sys : QRegister systemQubits (systemQubits + m) :=
        QRegister.block 0 systemQubits (fullSys_zero_add_le systemQubits m)
      let anc : QRegister m (systemQubits + m) := QRegister.block systemQubits m le_rfl
      W₁.1 * (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
        W₂.1 * (sys.embedMatrix P * anc.basisOutcomeProjector 0))
    (h₂ : ApproximatesTimeEvolution (m := m) H t ε P W₂) :
    ApproximatesTimeEvolution (m := m) H t ε P W₁ := by
  rcases h₂ with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  let sys : QRegister systemQubits (systemQubits + m) :=
    QRegister.block 0 systemQubits (fullSys_zero_add_le systemQubits m)
  let anc : QRegister m (systemQubits + m) := QRegister.block systemQubits m le_rfl
  let E_exp : Operator (2 ^ systemQubits) := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
  change ‖(W₁.1 - Complex.exp (φ * Complex.I) • sys.embedMatrix E_exp) *
    (sys.embedMatrix P * anc.basisOutcomeProjector 0)‖ ≤ ε
  change ‖(W₂.1 - Complex.exp (φ * Complex.I) • sys.embedMatrix E_exp) *
    (sys.embedMatrix P * anc.basisOutcomeProjector 0)‖ ≤ ε at hφ
  rw [sub_mul, hEq, ← sub_mul]
  exact hφ
-- ============================================================================
-- Section 2: Generalized `bValid` `SingleCat` Intertwining & `ExtHk` Lift
-- ============================================================================
theorem guardPolSingleCatGen_true_eq_ctrlNegRefl
    (bValid : Fin (2 ^ systemQubits) → Bool) (mPayload B_tot kWorkConst : ℕ) :
    let R0_emb := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
      (physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid)
    (guardPolSingleCatGen bValid mPayload B_tot kWorkConst true).1 =
      ctrlNegRefl true (qSigInSingleCat mPayload B_tot kWorkConst) R0_emb := by
  intro R0_emb
  let kBE := fullSysBEWires mPayload
  let rBESig := (rBEInSingleCat mPayload B_tot kWorkConst).concat
    (QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst))
    (rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst)
  let rLocSys : QRegister kBE (kBE + 1) := QRegister.block 0 kBE (by omega)
  let qLocSig : Wire (kBE + 1) := ⟨kBE, by omega⟩
  have hCompSys : rBESig.compose rLocSys = rBEInSingleCat mPayload B_tot kWorkConst := by
    apply qreg_ext; intro i
    have h1 : rLocSys i = Fin.castAdd 1 i := by ext; simp [rLocSys]
    change rBESig (rLocSys i) = rBEInSingleCat mPayload B_tot kWorkConst i
    rw [h1, QRegister.concat_apply_left]
  have hCompSig : rBESig.compose (QRegister.singleton qLocSig) =
      QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst) := by
    apply qreg_ext; intro i; fin_cases i
    have h1 : qLocSig = Fin.natAdd kBE (0 : Fin 1) := by ext; simp [qLocSig]
    change rBESig qLocSig = qSigInSingleCat mPayload B_tot kWorkConst
    rw [h1, QRegister.concat_apply_right]; rfl
  have hG_eq : (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
      (fullSysGuardReflUnitaryGen mPayload bValid).1 = -R0_emb := by
    have hNeg : (fullSysGuardReflUnitaryGen mPayload bValid).1 =
        -physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid := by
      change singleRBEReflNegMatrix systemQubits (fullSysRawAncWires mPayload)
          (diagProj systemQubits bValid) =
        -physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid
      unfold physGridReflGen singleRBEReflMatrix singleRBEReflNegMatrix reflOfProj
      abel
    rw [hNeg, embedMatrix_neg_poly]
  have hComm : (QRegister.singleton (qSigInSingleCat mPayload B_tot
      kWorkConst)).basisOutcomeProjector 1 * (-R0_emb) = (-R0_emb) * (QRegister.singleton
      (qSigInSingleCat mPayload B_tot kWorkConst)).basisOutcomeProjector 1 := by
    rw [mul_neg, neg_mul]
    exact congrArg Neg.neg
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
        (rBEInSingleCat mPayload B_tot kWorkConst))
        _ (rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst) _ 1).symm
  unfold guardPolSingleCatGen
  simp only [↓reduceIte, QRegister.embedUnitary_val]
  change rBESig.embedMatrix
      (ctrlInvolutionMatrix qLocSig rLocSys (fullSysGuardReflUnitaryGen mPayload bValid).1) = _
  unfold ctrlInvolutionMatrix
  rw[QRegister.embedMatrix_add, QRegister.embedMatrix_mul, QRegister.basisOutcomeProjector,
      QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose,
      ← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose, hCompSig, hCompSys,
      ← QRegister.basisOutcomeProjector, ← QRegister.basisOutcomeProjector, hG_eq, hComm,
      ctrlNegRefl_true_eq, Matrix.one_mul]
theorem intertwinesCat_guardPolSingleCatGen_true
    (bValid : Fin (2 ^ systemQubits) → Bool) (mPayload B_tot kWorkConst : ℕ) :
    let R0_emb := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
      (physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid)
    IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      (guardPolSingleCatGen bValid mPayload B_tot kWorkConst true).1
      (ctrlNegRefl true (qSigInSingleCat mPayload B_tot kWorkConst) R0_emb) := by
  intro R0_emb
  have hSigDisjTot : (QRegister.singleton (qSigInSingleCat mPayload B_tot
      kWorkConst)).DisjointWires (rCatTotInSingleCat mPayload B_tot kWorkConst) :=
    (qSigInSingleCat_disj_catScratch mPayload B_tot kWorkConst).compose_right _
  let rSig := QRegister.singleton (qSigInSingleCat mPayload B_tot kWorkConst)
  have hP_U (b : Fin 2) :
      rSig.basisOutcomeProjector b * (uCatNormSingleCat mPayload B_tot kWorkConst).1 =
        (uCatNormSingleCat mPayload B_tot kWorkConst).1 * rSig.basisOutcomeProjector b := by
    unfold uCatNormSingleCat
    rw [QRegister.embedUnitary_val]
    exact
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (rCatTotInSingleCat mPayload B_tot
      kWorkConst))
      _ (QRegExt.disjointWires_symm hSigDisjTot) _ b).symm
  have hP_int (b : Fin 2) := intertwinesCat_refl_of_comm_gen (hP_U b)
    (BidirectionalCatalyzedGQSP.basisOutcomeProjector_comm rSig
      (rCatScratchInSingleCat mPayload B_tot kWorkConst) b 0)
  have hR_U : (-R0_emb) * (uCatNormSingleCat mPayload B_tot kWorkConst).1 =
      (uCatNormSingleCat mPayload B_tot kWorkConst).1 * (-R0_emb) := by
    rw [neg_mul, mul_neg]
    unfold uCatNormSingleCat
    rw [QRegister.embedUnitary_val]
    exact congrArg Neg.neg ((rBEInSingleCat mPayload B_tot
      kWorkConst).embedMatrix_comm_of_disjoint (rCatTotInSingleCat mPayload B_tot kWorkConst)
      (rBEInSingleCat_disj_catTot mPayload B_tot kWorkConst) _ _)
  have hR_P : (-R0_emb) * pCat0SingleCat mPayload B_tot kWorkConst =
      pCat0SingleCat mPayload B_tot kWorkConst * (-R0_emb) := by
    rw [neg_mul, mul_neg]
    exact congrArg Neg.neg
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
        (rBEInSingleCat mPayload B_tot kWorkConst))
        (rCatScratchInSingleCat mPayload B_tot kWorkConst)
        (rBEInSingleCat_disj_catScratch mPayload B_tot kWorkConst) _ 0)
  rw [guardPolSingleCatGen_true_eq_ctrlNegRefl bValid mPayload B_tot kWorkConst,
    ctrlNegRefl_true_eq, Matrix.one_mul]
  exact intertwinesCat_add_gen (hP_int 0)
    (intertwinesCat_mul_gen (intertwinesCat_refl_of_comm_gen hR_U hR_P) (hP_int 1))
set_option exponentiation.threshold 5000 in
theorem intertwinesCat_uGuardWrapTwoAngleSingleCatGen {mPayload B_tot kWorkConst : ℕ}
    (bValid : Fin (2 ^ systemQubits) → Bool) (hB42 : 42 ≤ B_tot) (preX postX : Bool)
    (C_d D_d : Fin (2 ^ 42)) : IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
    (pCat0SingleCat mPayload B_tot kWorkConst)
    (uGuardWrapTwoAngleSingleCatGen bValid hB42 preX postX C_d D_d).1 (ctrlNegRefl true
    (qSigInSingleCat mPayload B_tot kWorkConst) ((rBEInSingleCat mPayload B_tot
    kWorkConst).embedMatrix (physGridReflGen systemQubits (fullSysRawAncWires mPayload)
    bValid)) * ((optXSingleCat mPayload B_tot kWorkConst postX).1 * ((QRegister.singleton
    (qSigInSingleCat mPayload B_tot kWorkConst)).embedMatrix (twoAngleDiagHMatrix C_d D_d) *
    ((optXSingleCat mPayload B_tot kWorkConst preX).1 * ctrlNegRefl true (qSigInSingleCat
    mPayload B_tot kWorkConst) ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
    (physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid)))))) := by
  have hRotEq :
      HarmonicTwoAngleBridge.uSignalRotTwoAngleSingleCat
        (mPayload := mPayload) (kWorkConst := kWorkConst) hB42 C_d D_d =
      uSignalRotTwoAngleSingleCat hB42 C_d D_d := rfl
  have h1 :=
    intertwinesCat_mul_gen
    (intertwinesCat_guardPolSingleCatGen_true bValid mPayload B_tot kWorkConst)
    (intertwinesCat_mul_gen (intertwinesCat_optXSingleCat mPayload B_tot kWorkConst postX)
      (intertwinesCat_mul_gen (intertwinesCat_signalRotTwoAngleSingleCat hB42 C_d D_d)
        (intertwinesCat_mul_gen (intertwinesCat_optXSingleCat mPayload B_tot kWorkConst preX)
          (intertwinesCat_guardPolSingleCatGen_true bValid mPayload B_tot kWorkConst))))
  simpa only [uGuardWrapTwoAngleSingleCatGen, hRotEq, Submonoid.coe_mul] using h1
set_option exponentiation.threshold 5000 in
/-- Generalized single-catalyst 2-angle Bi-GQSP prefix loop unitary for arbitrary `bValid`. -/
noncomputable def uSingleGuardPrefixTwoAngleSingleCatGen
    {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle} {sel : FullSysSelectOracleBundle mPayload 48}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (hB42 : 42 ≤ B_tot)
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel)
    (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (postLast : Bool) : ℕ → Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst))
  | 0 => uGuardWrapTwoAngleSingleCatGen bValid hB42 false postLast (biCode M C 0) (biCode M D 0)
  | t + 1 =>
      uGuardWrapTwoAngleSingleCatGen bValid hB42 true postLast
          (biCode M C (t + 1)) (biCode M D (t + 1)) *
        (((diagNegIPosICircuit (qSigInSingleCat mPayload B_tot kWorkConst)).seq
            (Circuit.X (qSigInSingleCat mPayload B_tot kWorkConst))).eval *
          (uCatRawBESingleCat prep selImpl c *
            uSingleGuardPrefixTwoAngleSingleCatGen bValid hB42 prep selImpl M C D c false t))
set_option exponentiation.threshold 5000 in
/-- Generalized single-catalyst 2-angle Bi-GQSP segment unitary for arbitrary `bValid`. -/
noncomputable def uSegTwoAngleSingleCatGen {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle} {sel : FullSysSelectOracleBundle mPayload 48}
    (bValid : Fin (2 ^ systemQubits) → Bool) (hB42 : 42 ≤ B_tot)
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel) (M : ℕ)
    (C D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration) : Unitary
    (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
    (Circuit.H (qSigInSingleCat mPayload B_tot kWorkConst)).eval * (((Circuit.S
    (qSigInSingleCat mPayload B_tot kWorkConst)).seq (Circuit.X (qSigInSingleCat mPayload
    B_tot kWorkConst))).eval * (uCtrlRawBESingleCat prep selImpl c *
    (uSingleGuardPrefixTwoAngleSingleCatGen bValid hB42 prep selImpl M C D c true M *
    (((Circuit.S (qSigInSingleCat mPayload B_tot kWorkConst)).seq (Circuit.Z (qSigInSingleCat
    mPayload B_tot kWorkConst))).eval * (uCtrlRawBESingleCat prep selImpl c * (Circuit.H
    (qSigInSingleCat mPayload B_tot kWorkConst)).eval)))))
set_option exponentiation.threshold 5000 in
/-- Generalized single-catalyst 1-angle Bi-GQSP segment unitary for arbitrary `bValid`. -/
noncomputable def uSegOneAngleSingleCatGen {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle} {sel : FullSysSelectOracleBundle mPayload 48}
    (bValid : Fin (2 ^ systemQubits) → Bool) (hB42 : 42 ≤ B_tot)
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel) (M : ℕ)
    (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration) : Unitary
    (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
    (cPostOneAngle (qSigInSingleCat mPayload B_tot kWorkConst)).eval *
    (uSegTwoAngleSingleCatGen bValid hB42 prep selImpl M (fun _ ↦ 0) D c * (cPreOneAngle
    (qSigInSingleCat mPayload B_tot kWorkConst)).eval)
set_option exponentiation.threshold 5000 in
/-- Catalyst intertwining for the `t`-step 2-angle SingleGuard prefix loop with general `bValid`. -/
private theorem guard_loop_step_assoc {d : ℕ} (K Opt D X XP U L W L' : Operator d)
    (hStep : X * (K * (XP * (U * K))) = W) (hLoop : D * (W * L) = L') :
    (K * (Opt * (D * (X * K)))) * (XP * (U * (K * (L * K)))) = K * (Opt * (L' * K)) := by
  calc (K * (Opt * (D * (X * K)))) * (XP * (U * (K * (L * K))))
    _ = K * (Opt * (D * ((X * (K * (XP * (U * K)))) * (L * K)))) := by
          simp only [Matrix.mul_assoc]
    _ = K * (Opt * (L' * K)) := by
          rw [hStep, ← Matrix.mul_assoc W L K, ← Matrix.mul_assoc D (W * L) K, hLoop]

theorem intertwinesCat_uSingleGuardPrefixTwoAngleSingleCatGen
    {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle} {sel : FullSysSelectOracleBundle mPayload 48}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (hB42 : 42 ≤ B_tot)
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel)
    (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (t : ℕ) (postLast : Bool) :
    IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      (uSingleGuardPrefixTwoAngleSingleCatGen (kWorkConst := kWorkConst) bValid hB42 prep selImpl
        M C D c postLast t).1
      (ctrlNegRefl true (qSigInSingleCat mPayload B_tot kWorkConst)
          ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
            (physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid)) *
        ((optXSingleCat mPayload B_tot kWorkConst postLast).1 *
          (biGqspTwoAngleLoopOp (qSigInSingleCat mPayload B_tot kWorkConst)
              ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
                (physLaurentWalkGen bValid (fullSysRawBEUnitary qft prep sel c)))
              ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
                (physLaurentWalkInvGen bValid (fullSysRawBEUnitary qft prep sel c)))
              M C D t *
            ctrlNegRefl true (qSigInSingleCat mPayload B_tot kWorkConst)
              ((rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
                (physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid))))) := by
  set qSig := qSigInSingleCat mPayload B_tot kWorkConst
  set R0_emb := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
    (physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid)
  set U_raw_emb := ((rBEInSingleCat mPayload B_tot kWorkConst).embedUnitary
    (fullSysRawBEUnitary qft prep sel c)).1
  set W_emb := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
    (physLaurentWalkGen bValid (fullSysRawBEUnitary qft prep sel c))
  set W_inv_emb := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
    (physLaurentWalkInvGen bValid (fullSysRawBEUnitary qft prep sel c))
  have hW_eq : W_emb = Complex.I • (R0_emb * U_raw_emb) := by
    dsimp only [W_emb, R0_emb, U_raw_emb, physLaurentWalkGen]
    rw [(rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_smul,
      (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_mul, QRegister.embedUnitary_val]
  have hWinv_eq : W_inv_emb = (-Complex.I) • (U_raw_emb * R0_emb) := by
    dsimp only [W_inv_emb, R0_emb, U_raw_emb, physLaurentWalkInvGen]
    rw [(rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_smul,
      (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_mul, QRegister.embedUnitary_val]
  have hBEP (M_be : Operator (2 ^ (fullSysBEWires mPayload))) (b : Fin 2) :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (rBEInSingleCat mPayload B_tot kWorkConst))
      (QRegister.singleton qSig) (rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst) M_be b
  have hRX : R0_emb * (Circuit.X qSig).eval.1 = (Circuit.X qSig).eval.1 * R0_emb := by
    rw [Circuit.X, Circuit.eval_single, QRegister.embedUnitary_val]
    exact (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_comm_of_disjoint _
      (rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst) _ _
  have hStepAlg := biWalkStepOp_eq_ctrlNegRefl_mul qSig R0_emb U_raw_emb W_emb W_inv_emb
    hW_eq hWinv_eq
    (by simpa only [U_raw_emb, QRegister.embedUnitary_val] using hBEP _ 0)
    (by simpa only [U_raw_emb, QRegister.embedUnitary_val] using hBEP _ 1)
    (hBEP _ 0) (hBEP _ 1) hRX
  have iDiagX := intertwinesCat_diagNegIPosIX_singleCat mPayload B_tot kWorkConst
  have iRaw := intertwinesCat_catRawBESingleCat (kWorkConst := kWorkConst) prep selImpl c
  induction t generalizing postLast with
  | zero =>
      have hw := intertwinesCat_uGuardWrapTwoAngleSingleCatGen (mPayload := mPayload)
        (kWorkConst := kWorkConst) bValid hB42 false postLast (biCode M C 0) (biCode M D 0)
      rw [optXSingleCat_false_mul] at hw
      exact hw
  | succ t ih =>
      have hw := intertwinesCat_uGuardWrapTwoAngleSingleCatGen (mPayload := mPayload)
        (kWorkConst := kWorkConst) bValid hB42 true postLast
        (biCode M C (t + 1)) (biCode M D (t + 1))
      rw [optXSingleCat_true_val] at hw
      have ihF := ih false
      rw [optXSingleCat_false_mul] at ihF
      have hStep := intertwinesCat_mul_gen hw
        (intertwinesCat_mul_gen iDiagX (intertwinesCat_mul_gen iRaw ihF))
      have hL : (uSingleGuardPrefixTwoAngleSingleCatGen bValid hB42 prep selImpl M C D c
          postLast (t + 1)).1 = (uGuardWrapTwoAngleSingleCatGen bValid hB42 true postLast
          (biCode M C (t + 1)) (biCode M D (t + 1))).1 * (((diagNegIPosICircuit qSig).seq
          (Circuit.X qSig)).eval.1 * ((uCatRawBESingleCat prep selImpl c).1 *
          (uSingleGuardPrefixTwoAngleSingleCatGen bValid hB42 prep selImpl M C D c false
          t).1)) := rfl
      have hLoopSucc : (QRegister.singleton qSig).embedMatrix
          (twoAngleDiagHMatrix (biCode M C (t + 1)) (biCode M D (t + 1))) * (biWalkStepOp qSig
          W_emb W_inv_emb * biGqspTwoAngleLoopOp qSig W_emb W_inv_emb M C D t) =
          biGqspTwoAngleLoopOp qSig W_emb W_inv_emb M C D (t + 1) := by
        change _ = _ * _ * _
        exact (Matrix.mul_assoc _ _ _).symm
      exact intertwinesCat_congr_ops hStep hL.symm
        (guard_loop_step_assoc _ _ _ _ _ _ _ _ _ hStepAlg hLoopSucc)
private theorem seg_two_angle_assoc {d : ℕ} (XS C K X L Z H L0 R0 : Operator d)
    (h0 : XS * (C * (K * X)) = L0) (h1 : K * (Z * C) = R0) :
    XS * (C * ((K * (X * (L * K))) * (Z * (C * H)))) = L0 * (L * (R0 * H)) := by
  calc XS * (C * ((K * (X * (L * K))) * (Z * (C * H))))
    _ = (XS * (C * (K * X))) * (L * ((K * (Z * C)) * H)) := by simp only [Matrix.mul_assoc]
    _ = L0 * (L * (R0 * H)) := by rw [h0, h1]

/-- Full segment catalyst-intertwining theorem for `uSegTwoAngleSingleCatGen` with general
  `bValid`. -/
theorem uSegTwoAngleSingleCatGen_intertwinesCat
    {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle}
    {sel : FullSysSelectOracleBundle mPayload 48}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (hB42 : 42 ≤ B_tot)
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel)
    (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42))
    (c : Configuration)
    (hTwist_s2 : (sel.uTwist c).1 * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * (sel.uTwist c).1)
    (hTwist_s1 : (sel.uTwist c).1 * slotBitProj (iSlot1 mPayload) 1 =
      slotBitProj (iSlot1 mPayload) 1 * (sel.uTwist c).1)
    (hTwist_s0 : (sel.uTwist c).1 * slotBitProj (iSlot0 mPayload) 0 =
      slotBitProj (iSlot0 mPayload) 0 * (sel.uTwist c).1)
    (hPos_slack :
      let P_slack := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
          slotBitProj (iSlot0 mPayload) 0
      (sel.uPosPhase c).1 * P_slack = P_slack) :
    IntertwinesCat
      (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      (uSegTwoAngleSingleCatGen (kWorkConst := kWorkConst) bValid hB42 prep selImpl M C D c).1
      ((rPhysSegInSingleCat mPayload B_tot kWorkConst).embedUnitary
        (physBiTwoAngleSegmentUnitaryGen bValid M C D
          (fullSysRawBEUnitary qft prep sel c))).1 := by
  set qSig := qSigInSingleCat mPayload B_tot kWorkConst
  set P0 := (QRegister.singleton qSig).basisOutcomeProjector 0
  set P1 := (QRegister.singleton qSig).basisOutcomeProjector 1
  set U_raw_emb := ((rBEInSingleCat mPayload B_tot kWorkConst).embedUnitary
    (fullSysRawBEUnitary qft prep sel c)).1
  set R0_emb := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
    (physGridReflGen systemQubits (fullSysRawAncWires mPayload) bValid)
  set W_emb := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
    (physLaurentWalkGen bValid (fullSysRawBEUnitary qft prep sel c))
  set W_inv_emb := (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix
    (physLaurentWalkInvGen bValid (fullSysRawBEUnitary qft prep sel c))
  have hW_eq : W_emb = Complex.I • (R0_emb * U_raw_emb) := by
    dsimp only [W_emb, R0_emb, U_raw_emb, physLaurentWalkGen]
    rw [(rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_smul,
      (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_mul, QRegister.embedUnitary_val]
  have hWinv_eq : W_inv_emb = (-Complex.I) • (U_raw_emb * R0_emb) := by
    dsimp only [W_inv_emb, R0_emb, U_raw_emb, physLaurentWalkInvGen]
    rw [(rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_smul,
      (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_mul, QRegister.embedUnitary_val]
  have hBEP (M_be : Operator (2 ^ (fullSysBEWires mPayload))) (b : Fin 2) :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (rBEInSingleCat mPayload B_tot kWorkConst))
      (QRegister.singleton qSig) (rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst) M_be b
  have hBEX (M_be : Operator (2 ^ (fullSysBEWires mPayload))) :
      (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix M_be * (Circuit.X qSig).eval.1 =
        (Circuit.X qSig).eval.1 * (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix M_be := by
    rw [Circuit.X, Circuit.eval_single, QRegister.embedUnitary_val]
    exact (rBEInSingleCat mPayload B_tot kWorkConst).embedMatrix_comm_of_disjoint _
      (rBEInSingleCat_disj_qSig mPayload B_tot kWorkConst) _ _
  have hU0 : U_raw_emb * P0 = P0 * U_raw_emb := by
    simpa only [U_raw_emb, P0, QRegister.embedUnitary_val] using hBEP _ 0
  have hU1 : U_raw_emb * P1 = P1 * U_raw_emb := by
    simpa only [U_raw_emb, P1, QRegister.embedUnitary_val] using hBEP _ 1
  have hR0 : R0_emb * P0 = P0 * R0_emb := hBEP _ 0
  have hR1 : R0_emb * P1 = P1 * R0_emb := hBEP _ 1
  have hUX : U_raw_emb * (Circuit.X qSig).eval.1 = (Circuit.X qSig).eval.1 * U_raw_emb := by
    simpa only [U_raw_emb, QRegister.embedUnitary_val] using hBEX _
  have hRX : R0_emb * (Circuit.X qSig).eval.1 = (Circuit.X qSig).eval.1 * R0_emb := hBEX _
  have iH := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.H
  have iX := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.X
  have iS := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.S
  have iZ := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.Z
  have iCtrl := intertwinesCat_ctrlRawBESingleCat (kWorkConst := kWorkConst) prep selImpl c
    hTwist_s2 hTwist_s1 hTwist_s0 hPos_slack
  have iSZ : IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      ((Circuit.S qSig).seq (Circuit.Z qSig)).eval.1
      ((1 : Operator _) * P0 + ((-Complex.I) • (1 : Operator _)) * P1) := by
    have h1 := intertwinesCat_mul_gen iZ iS
    have hE : (Circuit.Z qSig).eval.1 * (Circuit.S qSig).eval.1 =
        (1 : Operator _) * P0 + ((-Complex.I) • (1 : Operator _)) * P1 := by
      rw [← Submonoid.coe_mul, ← Circuit.eval_seq, eval_SZ_eq_proj]
    exact ⟨by rw [Circuit.eval_seq, Submonoid.coe_mul, ← hE]; exact h1.1,
           by rw [← hE]; exact h1.2.1,
           by rw [← hE]; exact h1.2.2⟩
  have iSX : IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      ((Circuit.S qSig).seq (Circuit.X qSig)).eval.1
      ((Circuit.X qSig).eval.1 * (Circuit.S qSig).eval.1) := by
    simpa only [Circuit.eval_seq, Submonoid.coe_mul] using intertwinesCat_mul_gen iX iS
  have iC1Alg := biRightBoundary_ctrlNegRefl_mul_eq qSig R0_emb U_raw_emb W_emb hW_eq hU0 hU1
  have iC0Alg := biLeftBoundary_ctrlNegRefl_mul_eq qSig R0_emb U_raw_emb W_inv_emb
    hWinv_eq hU0 hU1 hR0 hR1 hUX hRX
  have iPrefM := intertwinesCat_uSingleGuardPrefixTwoAngleSingleCatGen (kWorkConst := kWorkConst)
    bValid hB42 prep selImpl M C D c M true
  rw [optXSingleCat_true_val] at iPrefM
  have iSeg := intertwinesCat_mul_gen iH (intertwinesCat_mul_gen iSX (intertwinesCat_mul_gen
      iCtrl (intertwinesCat_mul_gen iPrefM (intertwinesCat_mul_gen iSZ (intertwinesCat_mul_gen
      iCtrl iH)))))
  have hSegVal : (uSegTwoAngleSingleCatGen (kWorkConst :=
    kWorkConst) bValid hB42 prep selImpl M C D c).1 =
      (Circuit.H qSig).eval.1 *
        (((Circuit.S qSig).seq (Circuit.X qSig)).eval.1 *
          ((uCtrlRawBESingleCat prep selImpl c).1 *
            ((uSingleGuardPrefixTwoAngleSingleCatGen bValid hB42 prep selImpl M C D c true M).1 *
              (((Circuit.S qSig).seq (Circuit.Z qSig)).eval.1 *
                ((uCtrlRawBESingleCat prep selImpl c).1 *
                  (Circuit.H qSig).eval.1))))) := by
    unfold uSegTwoAngleSingleCatGen
    simp only [qSig, Submonoid.coe_mul]
  let rP := rPhysSegInSingleCat mPayload B_tot kWorkConst
  let rBE_p : QRegister (fullSysBEWires mPayload)
      (systemQubits + (fullSysRawAncWires mPayload + 1)) :=
    QRegister.block 0 (fullSysBEWires mPayload) (by dsimp [fullSysBEWires]; omega)
  let qSig_p : Wire (systemQubits + (fullSysRawAncWires mPayload + 1)) :=
    ⟨fullSysBEWires mPayload, by dsimp [fullSysBEWires]; omega⟩
  have hCompBE : rP.compose rBE_p = rBEInSingleCat mPayload B_tot kWorkConst := by
    apply qreg_ext; intro i; ext
    simp [rP, rBE_p, rBEInSingleCat]
  have hSigEq : rP qSig_p = qSig := by
    ext; simp [rP, qSig_p, qSig]
  have hEmbW : rP.embedMatrix (rBE_p.embedMatrix
      (physLaurentWalkGen bValid (fullSysRawBEUnitary qft prep sel c))) =
      W_emb := by rw [← QRegister.embedMatrix_compose, hCompBE]
  have hEmbWinv : rP.embedMatrix (rBE_p.embedMatrix
      (physLaurentWalkInvGen bValid (fullSysRawBEUnitary qft prep sel c))) =
      W_inv_emb := by rw [← QRegister.embedMatrix_compose, hCompBE]
  have hEmbSeg : ((rPhysSegInSingleCat mPayload B_tot kWorkConst).embedUnitary
      (physBiTwoAngleSegmentUnitaryGen bValid M C D (fullSysRawBEUnitary qft prep sel c))).1
      = (Circuit.H qSig).eval.1 * ((W_inv_emb * P0 + P1) * (biGqspTwoAngleLoopOp qSig W_emb
      W_inv_emb M C D M * ((P0 + W_emb * P1) * (Circuit.H qSig).eval.1))) := by
    rw [QRegister.embedUnitary_val]
    change rP.embedMatrix (biGqspGenSegmentOp qSig_p (rBE_p.embedMatrix (physLaurentWalkGen
      bValid (fullSysRawBEUnitary qft prep sel c))) (rBE_p.embedMatrix (physLaurentWalkInvGen
      bValid (fullSysRawBEUnitary qft prep sel c))) (biTwoAngleGate M C D) M) = _
    rw [embedMatrix_biGqspGenSegmentOp, hSigEq, hEmbW, hEmbWinv]
    unfold biGqspGenSegmentOp biGqspTwoAngleLoopOp
    dsimp only [P0, P1]
    simp only [Matrix.mul_assoc]
  exact intertwinesCat_congr_ops iSeg hSegVal.symm
    ((congrArg (HMul.hMul (Circuit.H qSig).eval.1)
      (seg_two_angle_assoc _ _ _ _ _ _ _ _ _ iC0Alg iC1Alg)).trans hEmbSeg.symm)
/-- Catalyst intertwining for `uSegOneAngleSingleCatGen` onto `physBiSegmentUnitaryGen bValid`. -/
theorem uSegOneAngleSingleCatGen_intertwinesCat
    {mPayload B_tot kWorkConst : ℕ}
    {qft : FullSysQft654Bundle}
    {sel : FullSysSelectOracleBundle mPayload 48}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (hB42 : 42 ≤ B_tot)
    (prep : FullSysPrepareBundle mPayload)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42))
    (c : Configuration)
    (hTwist_s2 : (sel.uTwist c).1 * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * (sel.uTwist c).1)
    (hTwist_s1 : (sel.uTwist c).1 * slotBitProj (iSlot1 mPayload) 1 =
      slotBitProj (iSlot1 mPayload) 1 * (sel.uTwist c).1)
    (hTwist_s0 : (sel.uTwist c).1 * slotBitProj (iSlot0 mPayload) 0 =
      slotBitProj (iSlot0 mPayload) 0 * (sel.uTwist c).1)
    (hPos_slack :
      let P_slack := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
          slotBitProj (iSlot0 mPayload) 0
      (sel.uPosPhase c).1 * P_slack = P_slack) :
    IntertwinesCat
      (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      (uSegOneAngleSingleCatGen (kWorkConst := kWorkConst) bValid hB42 prep selImpl M D c).1
      ((rPhysSegInSingleCat mPayload B_tot kWorkConst).embedUnitary
        (physBiSegmentUnitaryGen bValid M D
          (fullSysRawBEUnitary qft prep sel c))).1 := by
  let qSig := qSigInSingleCat mPayload B_tot kWorkConst
  have iH := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.H
  have iS := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.S
  have iZ := single_qSig_gate_intertwines_singleCat mPayload B_tot kWorkConst PrimitiveGate.Z
  have iPost : IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      (cPostOneAngle qSig).eval.1 (cPostOneAngle qSig).eval.1 := by
    simpa only [cPostOneAngle, Circuit.eval_seq, Submonoid.coe_mul] using
      intertwinesCat_mul_gen iH (intertwinesCat_mul_gen iS iH)
  have iPre : IntertwinesCat (uCatNormSingleCat mPayload B_tot kWorkConst).1
      (pCat0SingleCat mPayload B_tot kWorkConst)
      (cPreOneAngle qSig).eval.1 (cPreOneAngle qSig).eval.1 := by
    simpa only [cPreOneAngle, Circuit.eval_seq, Submonoid.coe_mul] using
      intertwinesCat_mul_gen iH (intertwinesCat_mul_gen iZ (intertwinesCat_mul_gen iS iH))
  have iSeg2 := uSegTwoAngleSingleCatGen_intertwinesCat (kWorkConst := kWorkConst)
    bValid hB42 prep selImpl M (fun _ ↦ 0) D c hTwist_s2 hTwist_s1 hTwist_s0 hPos_slack
  have iComb := intertwinesCat_mul_gen iPost (intertwinesCat_mul_gen iSeg2 iPre)
  let rP := rPhysSegInSingleCat mPayload B_tot kWorkConst
  let qSig_p : Wire (systemQubits + (fullSysRawAncWires mPayload + 1)) :=
    ⟨fullSysBEWires mPayload, by dsimp [fullSysBEWires]; omega⟩
  have hCompSig : rP.compose (QRegister.singleton qSig_p) = QRegister.singleton qSig := by
    apply qreg_ext; intro i; fin_cases i; ext; simp [rP, qSig_p, qSig]
  have hGateEmb : ∀ g : PrimitiveGate 1,
      rP.embedUnitary (Circuit.single g qSig_p).eval = (Circuit.single g qSig).eval := by
    intro g
    rw [Circuit.eval_single, Circuit.eval_single, ← QRegister.embedUnitary_compose, hCompSig]
  have hPostEmb : rP.embedUnitary (cPostOneAngle qSig_p).eval = (cPostOneAngle qSig).eval := by
    unfold cPostOneAngle Circuit.H Circuit.S
    simp only [Circuit.eval_seq, QRegister.embedUnitary_mul, hGateEmb]
  have hPreEmb : rP.embedUnitary (cPreOneAngle qSig_p).eval = (cPreOneAngle qSig).eval := by
    unfold cPreOneAngle Circuit.H Circuit.S Circuit.Z
    simp only [Circuit.eval_seq, QRegister.embedUnitary_mul, hGateEmb]
  have hEffEq : (cPostOneAngle qSig).eval.1 * ((rP.embedUnitary
      (physBiTwoAngleSegmentUnitaryGen bValid M (fun _ ↦ 0) D (fullSysRawBEUnitary qft prep
      sel c))).1 * (cPreOneAngle qSig).eval.1) = (rP.embedUnitary (physBiSegmentUnitaryGen
      bValid M D (fullSysRawBEUnitary qft prep sel c))).1 := by
    rw [← hPostEmb, ← hPreEmb, ← Submonoid.coe_mul, ← Submonoid.coe_mul,
      ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
      cPost_mul_physBiTwoAngleSegment_zero_mul_cPre]
  exact intertwinesCat_congr_ops iComb rfl hEffEq
section ExtHkGenLift
attribute [local reducible] InterWalkRSum42Hoist.kActOrig
theorem qSigInSingleCat80_val_eq : (qSigInSingleCat 80 48 40).val = 4034 := by
  dsimp [qSigInSingleCat, fullSysBEWires, fullSysRawAncWires, systemQubits,
    numElectrons, electronBits, projectileBits]
set_option exponentiation.threshold 5000 in
theorem preservesId_guardPolSingleCatGen (bValid : Fin (2 ^ systemQubits) → Bool) (b : Bool) :
    PreservesFeature id (guardPolSingleCatGen bValid 80 48 40 b).1 := by
  cases b
  · change PreservesFeature id (1 : Unitary _).1
    exact PreservesFeature.one id
  · have hGrid : PreservesFeature id (diagProj systemQubits bValid) := by
      unfold diagProj
      exact PreservesFeature.diagonal id _
    have hProjGA : PreservesFeature id
        (projGridAncZero systemQubits (fullSysRawAncWires 80) (diagProj systemQubits bValid)) := by
      unfold projGridAncZero
      exact (hGrid.embedMatrix_id _).mul (PreservesFeature.basisOutcomeProjector _ 0)
    have hRefl : PreservesFeature id (fullSysGuardReflUnitaryGen 80 bValid).1 := by
      change PreservesFeature id
        (singleRBEReflNegMatrix systemQubits (fullSysRawAncWires 80) (diagProj systemQubits bValid))
      rw [singleRBEReflNegMatrix_eq_phaseOp_neg_one]
      unfold phaseOp
      exact (PreservesFeature.one id).add (hProjGA.smul _)
    have hCtrl : PreservesFeature id (ctrlLocalUnitary (fullSysGuardReflUnitaryGen 80 bValid)).1 :=
      by
      change PreservesFeature id (ctrlInvolutionMatrix _ _ (fullSysGuardReflUnitaryGen 80 bValid).1)
      unfold ctrlInvolutionMatrix
      exact (PreservesFeature.basisOutcomeProjector _ 0).add
        ((PreservesFeature.basisOutcomeProjector _ 1).mul (hRefl.embedMatrix_id _))
    unfold guardPolSingleCatGen
    rw [ite_true_eq rfl, QRegister.embedUnitary_val]
    exact hCtrl.embedMatrix_id _
set_option exponentiation.threshold 5000 in
theorem fixesLow3924_uGuardWrapTwoAngleSingleCatGen80
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (preX postX : Bool) (C_d D_d : Fin (2 ^ 42)) :
    FixesLow3924 h3924_actOrig
      (uGuardWrapTwoAngleSingleCatGen (mPayload := 80) (kWorkConst := 40) bValid
        (by decide : 42 ≤ 48) preX postX C_d D_d).1 := by
  have hPol : FixesLow3924 h3924_actOrig (guardPolSingleCatGen bValid 80 48 40 true).1 :=
    (preservesId_guardPolSingleCatGen bValid true).id_imp _
  unfold uGuardWrapTwoAngleSingleCatGen
  simp only [Submonoid.coe_mul]
  exact hPol.mul ((fixesLow3924_optXSingleCat postX).mul
    ((fixesLow3924_uSignalRotTwoAngleSingleCat80 C_d D_d).mul
      ((fixesLow3924_optXSingleCat preX).mul hPol)))
set_option exponentiation.threshold 5000 in
theorem fixesCtrl3_uGuardWrapTwoAngleSingleCatGen80
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42)) :
    FixesCtrl3 h3954_actOrig
      (uGuardWrapTwoAngleSingleCatGen (mPayload := 80) (kWorkConst := 40) bValid
        (by decide : 42 ≤ 48) bPre bPost C_d D_d).1 := by
  have hPol : FixesCtrl3 h3954_actOrig (guardPolSingleCatGen bValid 80 48 40 true).1 :=
    (preservesId_guardPolSingleCatGen bValid true).id_imp _
  have hOpt : ∀ b : Bool, FixesCtrl3 h3954_actOrig (optXSingleCat 80 48 40 b).1 := fun b ↦ by
    cases b
    · exact PreservesFeature.one _
    · dsimp only [optXSingleCat]; rw [ite_true_eq rfl, Circuit.X, Circuit.eval_single,
        QRegister.embedUnitary_val]
      refine fixesCtrl3_embedMatrix_disj h3954_actOrig (fun i ↦ Or.inr ?_) _
      fin_cases i; rw [QRegister.singleton_apply, qSigInSingleCat80_val_eq]; omega
  have hRot : FixesCtrl3 h3954_actOrig
      (uSignalRotTwoAngleSingleCat (mPayload := 80) (kWorkConst := 40)
        (by decide : 42 ≤ 48) C_d D_d).1 := by
    unfold uSignalRotTwoAngleSingleCat
    rw [QRegister.embedUnitary_val]
    exact fixesCtrl3_embedMatrix_disj h3954_actOrig
      (fun j ↦ Or.inr (le_trans (by decide : 3954 ≤ 4034) (rMid43Orig_val_ge_4034 j))) _
  unfold uGuardWrapTwoAngleSingleCatGen
  simp only [Submonoid.coe_mul]
  exact hPol.mul ((hOpt bPost).mul (hRot.mul ((hOpt bPre).mul hPol)))
set_option exponentiation.threshold 5000 in
set_option exponentiation.threshold 5000 in
private theorem guardPol_optX_comm_of_gt4034 {k : ℕ}
    (r : QRegister k kActOrig) (hr : ∀ q, 4034 < (r q).val)
    (bValid : Fin (2 ^ systemQubits) → Bool) :
    CommutesWithReg r (guardPolSingleCatGen bValid 80 48 40 true).1 ∧
      ∀ b : Bool, CommutesWithReg r (optXSingleCat 80 48 40 b).1 := by
  refine ⟨?_, fun b ↦ ?_⟩
  · unfold guardPolSingleCatGen
    rw [ite_true_eq rfl, QRegister.embedUnitary_val]
    refine CommutesWithReg.of_disjoint (disj_of_val_ne fun i q ↦ ?_) _
    have hq := hr q
    refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
    · rw [QRegister.concat_apply_left]
      have ha := a.isLt
      dsimp [rBEInSingleCat, qreg_block_apply, fullSysBEWires, fullSysRawAncWires,
        systemQubits, numElectrons, electronBits, projectileBits] at ha ⊢
      omega
    · fin_cases b
      rw [QRegister.concat_apply_right, QRegister.singleton_apply, qSigInSingleCat80_val_eq]
      omega
  · cases b
    · exact CommutesWithReg.one _
    · dsimp only [optXSingleCat]
      rw [ite_true_eq rfl, Circuit.X, Circuit.eval_single, QRegister.embedUnitary_val]
      refine CommutesWithReg.of_disjoint (disj_of_val_ne fun i q ↦ ?_) _
      fin_cases i
      rw [QRegister.singleton_apply, qSigInSingleCat80_val_eq]
      have := hr q
      omega

set_option exponentiation.threshold 5000 in
theorem commutesWithReg_rPGIdleOrig_uGuardWrapTwoAngleGen
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (k_idle : ℕ) (hk : k_idle ≤ 48) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (hC : 2 ^ (k_idle - 6) ∣ C_d.val) (hD : 2 ^ (k_idle - 6) ∣ D_d.val) :
    CommutesWithReg (rPGIdleOrig k_idle hk)
      (uGuardWrapTwoAngleSingleCatGen (mPayload := 80) (kWorkConst := 40) bValid
        (by decide : 42 ≤ 48) bPre bPost C_d D_d).1 := by
  obtain ⟨hPol, hOpt⟩ := guardPol_optX_comm_of_gt4034 (rPGIdleOrig k_idle hk)
    (fun q ↦ by rw [rPGIdleOrig_val_eq]; omega) bValid
  have hRot : CommutesWithReg (rPGIdleOrig k_idle hk)
      (uSignalRotTwoAngleSingleCat (mPayload := 80) (kWorkConst := 40)
        (by decide : 42 ≤ 48) C_d D_d).1 := by
    refine commutesWithReg_of_forall_singleton (rPGIdleOrig k_idle hk) fun q ↦ ?_
    unfold uSignalRotTwoAngleSingleCat
    rw [QRegister.embedUnitary_val]
    by_cases hq6 : q.val < 6
    · refine CommutesWithReg.of_disjoint (disj_of_val_ne fun idx j ↦ ?_) _
      fin_cases j; rw [QRegister.singleton_apply, rPGIdleOrig_val_eq]
      by_cases h0 : idx.val = 0
      · have hidx : idx = ⟨0, by decide⟩ := Fin.ext h0
        rw [hidx, rMid43Orig_zero_val]; omega
      · rw [rMid43Orig_pos_val idx h0]; omega
    · have ht_lt : q.val - 6 < k_idle - 6 := by omega
      have hLow := (commutesWithReg_low_uSignalRotTwoAngle43 (by omega : k_idle - 6 ≤ 42)
        C_d D_d hC hD).compose (QRegister.singleton ⟨q.val - 6, ht_lt⟩)
      have hPush := hLow.embedMatrix rMid43Orig
      have hSingEq : rMid43Orig.compose ((QRegister.block 1 (k_idle - 6) (by omega)).compose
          (QRegister.singleton ⟨q.val - 6, ht_lt⟩)) = QRegister.singleton
          (rPGIdleOrig k_idle hk q) := by
        apply qreg_ext; intro j; fin_cases j
        apply Fin.ext
        rw [QRegister.singleton_apply, rPGIdleOrig_val_eq]
        change (rMid43Orig ⟨1 + (q.val - 6), by omega⟩).val = 4035 + q.val
        rw [rMid43Orig_pos_val ⟨1 + (q.val - 6), by omega⟩ (by change 1 + (q.val - 6) ≠ 0; omega)]
        change 4041 + ((1 + (q.val - 6)) - 1) = 4035 + q.val
        omega
      rwa [hSingEq] at hPush
  unfold uGuardWrapTwoAngleSingleCatGen
  simp only [Submonoid.coe_mul]
  exact hPol.mul ((hOpt bPost).mul (hRot.mul ((hOpt bPre).mul hPol)))
set_option exponentiation.threshold 5000 in
theorem uGuardWrapTwoAngleGen_comm_E_segExt (bValid : Fin (2 ^ systemQubits) → Bool)
    (k_idle : ℕ) (hk : k_idle ≤ 48) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (hC : 2 ^ (k_idle - 6) ∣ C_d.val) (hD : 2 ^ (k_idle - 6) ∣ D_d.val) : (rAct0.embedUnitary
    (uGuardWrapTwoAngleSingleCatGen bValid (by decide : 42 ≤ 48) bPre bPost C_d D_d)).1 *
    E_segExt k_idle hk = E_segExt k_idle hk * (rAct0.embedUnitary
    (uGuardWrapTwoAngleSingleCatGen bValid (by decide : 42 ≤ 48) bPre bPost C_d D_d)).1 := by
  let U0 := uGuardWrapTwoAngleSingleCatGen (mPayload := 80) (kWorkConst := 40) bValid
    (by decide : 42 ≤ 48) bPre bPost C_d D_d
  have hStream : (rAct0.embedUnitary U0).1 * E_stream42 = E_stream42 * (rAct0.embedUnitary U0).1 :=
    embedAct0_fixesLow3924_comm_E_stream42
      (fixesLow3924_uGuardWrapTwoAngleSingleCatGen80 bValid bPre bPost C_d D_d)
  have hCtrl3 : (rAct0.embedUnitary U0).1 * pCtrl3Zero = pCtrl3Zero * (rAct0.embedUnitary U0).1 :=
    by
    rw [QRegister.embedUnitary_val, ← embedAct0_pCtrl3ZeroOrig,
      ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul,
      (fixesCtrl3_uGuardWrapTwoAngleSingleCatGen80 bValid bPre bPost C_d D_d).comm_pCtrl3ZeroOrig]
  have hSlackOrig : CommutesWithReg rSlack3Orig U0.1 := by
    obtain ⟨hPol, hOpt⟩ := guardPol_optX_comm_of_gt4034 rSlack3Orig
      (fun t ↦ by
        rw [rSlack3Orig_val_eq]
        have := t.isLt
        omega) bValid
    have hRot : CommutesWithReg rSlack3Orig
        (uSignalRotTwoAngleSingleCat (by decide : 42 ≤ 48) C_d D_d).1 := by
      unfold uSignalRotTwoAngleSingleCat; rw [QRegister.embedUnitary_val]
      refine CommutesWithReg.of_disjoint (disj_of_val_ne fun idx t ↦ ?_) _
      rw [rSlack3Orig_val_eq]; have := t.isLt
      by_cases h0 : idx.val = 0
      · have hidx : idx = ⟨0, by decide⟩ := Fin.ext h0
        rw [hidx, rMid43Orig_zero_val]; omega
      · rw [rMid43Orig_pos_val idx h0]; omega
    unfold U0 uGuardWrapTwoAngleSingleCatGen; simp only [Submonoid.coe_mul]
    exact hPol.mul ((hOpt bPost).mul (hRot.mul ((hOpt bPre).mul hPol)))
  have hSlack3 : (rAct0.embedUnitary U0).1 * pSlack3Zero = pSlack3Zero *
    (rAct0.embedUnitary U0).1 := by
    rw [QRegister.embedUnitary_val]
    exact (hSlackOrig.embedMatrix rAct0).comm_basisOutcomeProjector 0
  have hIdle : (rAct0.embedUnitary U0).1 * pPGIdleZero k_idle hk =
      pPGIdleZero k_idle hk * (rAct0.embedUnitary U0).1 := by
    rw [QRegister.embedUnitary_val]
    exact ((commutesWithReg_rPGIdleOrig_uGuardWrapTwoAngleGen bValid k_idle hk bPre bPost
      C_d D_d hC hD).embedMatrix rAct0).comm_basisOutcomeProjector 0
  change (rAct0.embedUnitary U0).1 * E_segExt k_idle hk =
    E_segExt k_idle hk * (rAct0.embedUnitary U0).1
  unfold E_segExt
  rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hStream, Matrix.mul_assoc E_stream42, hCtrl3,
    ← Matrix.mul_assoc E_stream42, Matrix.mul_assoc (E_stream42 * pCtrl3Zero), hSlack3,
    ← Matrix.mul_assoc (E_stream42 * pCtrl3Zero),
    Matrix.mul_assoc (E_stream42 * pCtrl3Zero * pSlack3Zero), hIdle]
  simp only [Matrix.mul_assoc]
set_option exponentiation.threshold 5000 in
/-- Hoisted 2-angle Gidney guard prefix unitary on `kFull80` for general `bValid`. -/
noncomputable def uSingleGuardPrefixExtHkTwoAngleGen
    {mWork k_idle tSelCtrl tSelCat : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (prep : FullSysPrepareBundle 80)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42))
    (c : Configuration) (postLast : Bool) : ℕ → Unitary (2 ^ kFull80)
  | 0 =>
      rAct0.embedUnitary
        (uGuardWrapTwoAngleSingleCatGen (mPayload := 80) (kWorkConst := 40) bValid
          (by decide : 42 ≤ 48) false postLast (biCode M C 0) (biCode M D 0))
  | t + 1 =>
      rAct0.embedUnitary
        (uGuardWrapTwoAngleSingleCatGen (mPayload := 80) (kWorkConst := 40) bValid
          (by decide : 42 ≤ 48) true postLast (biCode M C (t + 1)) (biCode M D (t + 1))) *
        (rAct0.embedUnitary (((diagNegIPosICircuit (qSigInSingleCat 80 48 40)).seq
            (Circuit.X (qSigInSingleCat 80 48 40))).eval) *
          (uCatRawBEExtHk prep sel c *
            uSingleGuardPrefixExtHkTwoAngleGen bValid prep sel M C D c false t))
set_option exponentiation.threshold 5000 in
/-- Hoisted 2-angle Bi-GQSP Gidney segment unitary on `kFull80` for general `bValid`. -/
noncomputable def uSegExtHkTwoAngleGen {mWork k_idle tSelCtrl tSelCat : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (bValid : Fin (2 ^ systemQubits) → Bool)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    : Unitary (2 ^ kFull80) := rAct0.embedUnitary (Circuit.H (qSigInSingleCat 80 48 40)).eval
    * (rAct0.embedUnitary (((Circuit.S (qSigInSingleCat 80 48 40)).seq (Circuit.X
    (qSigInSingleCat 80 48 40))).eval) * (uCtrlRawBEExtHk prep sel c *
    (uSingleGuardPrefixExtHkTwoAngleGen bValid prep sel M C D c true M * (rAct0.embedUnitary
    (((Circuit.S (qSigInSingleCat 80 48 40)).seq (Circuit.Z (qSigInSingleCat 80 48 40))).eval)
    * (uCtrlRawBEExtHk prep sel c * rAct0.embedUnitary (Circuit.H (qSigInSingleCat 80 48
    40)).eval)))))
set_option exponentiation.threshold 5000 in
/-- Hoisted 1-angle Bi-GQSP Gidney segment unitary on `kFull80` for general `bValid`. -/
noncomputable def uSegOneAngleExtHkGen {mWork k_idle tSelCtrl tSelCat : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (bValid : Fin (2 ^ systemQubits) → Bool)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration) :
    Unitary (2 ^ kFull80) := rAct0.embedUnitary
    (cPostOneAngle (qSigInSingleCat 80 48 40)).eval * (uSegExtHkTwoAngleGen bValid prep
    sel M (fun _ ↦ 0) D c * rAct0.embedUnitary (cPreOneAngle (qSigInSingleCat 80 48 40)).eval)
set_option exponentiation.threshold 5000 in
theorem uSingleGuardPrefixExtHkTwoAngleGen_mul_E_segExt
    {mWork k_idle tSelCtrl tSelCat : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (prep : FullSysPrepareBundle 80)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (hDivC : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (C i).val)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) :
    ∀ (t : ℕ) (postLast : Bool),
      (uSingleGuardPrefixExtHkTwoAngleGen bValid prep sel M C D c postLast t).1 *
          E_segExt k_idle hk =
        E_segExt k_idle hk *
          (rAct0.embedUnitary
            (uSingleGuardPrefixTwoAngleSingleCatGen (kWorkConst := 40) bValid
              (by decide : 42 ≤ 48) prep selImpl M C D c postLast t)).1
  | 0, postLast =>
      uGuardWrapTwoAngleGen_comm_E_segExt bValid k_idle hk false postLast (biCode M C 0)
        (biCode M D 0) (dvd_biCode_of_forall_dvd hDivC 0) (dvd_biCode_of_forall_dvd hDivD 0)
  | t + 1, postLast => by
      have ih := uSingleGuardPrefixExtHkTwoAngleGen_mul_E_segExt bValid prep sel M C D c
        hDivC hDivD hPrepLow hPrepCtrl3 t false
      have hCat := uCatRawBEExtHk_mul_E_segExt prep sel c hPrepLow hPrepCtrl3
      have h1q := qSig_diagSeqX_comm_E_segExt k_idle hk
      have hGw := uGuardWrapTwoAngleGen_comm_E_segExt bValid k_idle hk true postLast
        (biCode M C (t + 1)) (biCode M D (t + 1))
        (dvd_biCode_of_forall_dvd hDivC (t + 1)) (dvd_biCode_of_forall_dvd hDivD (t + 1))
      dsimp only [uSingleGuardPrefixExtHkTwoAngleGen, uSingleGuardPrefixTwoAngleSingleCatGen]
      simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
      exact comm_op_mul hGw (comm_op_mul h1q (comm_op_mul hCat ih))
set_option exponentiation.threshold 5000 in
private theorem qSig_seq_comm_E_segExt (k_idle : ℕ) (hk : k_idle ≤ 48)
    (g₁ g₂ : PrimitiveGate 1) :
    (rAct0.embedUnitary (((Circuit.single g₁ (qSigInSingleCat 80 48 40)).seq
      (Circuit.single g₂ (qSigInSingleCat 80 48 40))).eval)).1 * E_segExt k_idle hk =
    E_segExt k_idle hk * (rAct0.embedUnitary (((Circuit.single g₁ (qSigInSingleCat 80 48 40)).seq
      (Circuit.single g₂ (qSigInSingleCat 80 48 40))).eval)).1 := by
  simp only [Circuit.eval_seq, QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact comm_op_mul (qSig_single_comm_E_segExt k_idle hk g₂)
    (qSig_single_comm_E_segExt k_idle hk g₁)

set_option exponentiation.threshold 5000 in
theorem uSegExtHkTwoAngleGen_mul_E_segExt
    {mWork k_idle tSelCtrl tSelCat : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (prep : FullSysPrepareBundle 80)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (hDivC : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (C i).val)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) :
    (uSegExtHkTwoAngleGen bValid prep sel M C D c).1 * E_segExt k_idle hk =
      E_segExt k_idle hk *
        (rAct0.embedUnitary
          (uSegTwoAngleSingleCatGen (kWorkConst := 40) bValid (by decide : 42 ≤ 48) prep
            selImpl M C D c)).1 := by
  have hH := qSig_single_comm_E_segExt k_idle hk .H
  have hSZ := qSig_seq_comm_E_segExt k_idle hk .S .Z
  have hSX := qSig_seq_comm_E_segExt k_idle hk .S .X
  have hCtrl := uCtrlRawBEExtHk_mul_E_segExt prep sel c hPrepLow hPrepCtrl3
  have hPref := uSingleGuardPrefixExtHkTwoAngleGen_mul_E_segExt bValid prep sel M C D c hDivC hDivD
    hPrepLow hPrepCtrl3 M true
  unfold uSegExtHkTwoAngleGen uSegTwoAngleSingleCatGen
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact comm_op_mul hH (comm_op_mul hSX (comm_op_mul hCtrl (comm_op_mul hPref (comm_op_mul hSZ
    (comm_op_mul hCtrl hH)))))
set_option exponentiation.threshold 5000 in
theorem uSegOneAngleExtHkGen_mul_E_segExt
    {mWork k_idle tSelCtrl tSelCat : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (prep : FullSysPrepareBundle 80)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) :
    (uSegOneAngleExtHkGen bValid prep sel M D c).1 * E_segExt k_idle hk =
      E_segExt k_idle hk *
        (rAct0.embedUnitary
          (uSegOneAngleSingleCatGen (kWorkConst := 40) bValid (by decide : 42 ≤ 48) prep
            selImpl M D c)).1 := by
  have hDiv0 : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣
      ((fun _ : Fin (M + 1) ↦ (0 : Fin (2 ^ 42))) i).val := fun _ ↦ Nat.dvd_zero _
  have hInner := uSegExtHkTwoAngleGen_mul_E_segExt bValid prep sel M (fun _ ↦ 0) D c
    hDiv0 hDivD hPrepLow hPrepCtrl3
  unfold uSegOneAngleExtHkGen uSegOneAngleSingleCatGen
  rw[QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, Submonoid.coe_mul,
      Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, cPreOneAngle_comm_E_segExt k_idle hk,
      ← Matrix.mul_assoc (uSegExtHkTwoAngleGen bValid prep sel M (fun _ ↦ 0) D c).1,
      hInner, Matrix.mul_assoc (E_segExt k_idle hk),
      ← Matrix.mul_assoc _ (E_segExt k_idle hk), cPostOneAngle_comm_E_segExt k_idle hk]
  simp only [Matrix.mul_assoc]
set_option exponentiation.threshold 5000 in
private theorem qSig80_single_comm_rPGIdleOrig (k_idle : ℕ) (hk : k_idle ≤ 48)
    (g : PrimitiveGate 1) :
    CommutesWithReg (rPGIdleOrig k_idle hk)
      (Circuit.single g (qSigInSingleCat 80 48 40)).eval.1 := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val]
  refine CommutesWithReg.of_disjoint (disj_of_val_ne fun i q ↦ ?_) _
  fin_cases i
  rw [QRegister.singleton_apply, rPGIdleOrig_val_eq, qSigInSingleCat80_val_eq]
  omega

set_option exponentiation.threshold 5000 in
theorem commutesWithReg_rPGIdleOrig_uSegTwoAngleSingleCatGen
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (k_idle : ℕ) (hk : k_idle ≤ 48)
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    (prep : FullSysPrepareBundle 80) (selImpl : SingleCatSelectImpl 80 48 qft selOra)
    (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (hSelIdle : CommutesWithReg (rPGIdleOrig k_idle hk)
      (rSegOrig.embedUnitary (selImpl.uSelCat c)).1)
    (hDivC : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (C i).val)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val) :
    CommutesWithReg (rPGIdleOrig k_idle hk)
      (uSegTwoAngleSingleCatGen (kWorkConst := 40) bValid (by decide : 42 ≤ 48) prep
        selImpl M C D c).1 := by
  have h1q := qSig80_single_comm_rPGIdleOrig k_idle hk
  have hBE : ∀ U : Unitary (2 ^ (fullSysBEWires 80)),
      CommutesWithReg (rPGIdleOrig k_idle hk) (rBEOrig.embedUnitary U).1 := fun U ↦ by
    rw [QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint (disj_of_val_ne fun i q ↦ by
      rw [rPGIdleOrig_val_eq]; have := rBEOrig_val_lt_4034 i; have := q.isLt; omega) _
  have hCat : CommutesWithReg (rPGIdleOrig k_idle hk)
      (uCatRawBESingleCat prep selImpl c).1 := by
    unfold uCatRawBESingleCat
    simp only [Submonoid.coe_mul]
    exact (hBE _).mul (hSelIdle.mul (hBE _))
  have hPk : CommutesWithReg (rPGIdleOrig k_idle hk) (cSlackParkSingleCat 80 48 40).eval.1 :=
      compileRevList_commutesWithReg_rPGIdleOrig k_idle hk _ slackParkSteps80_allAvoidPG48
  have hUnpk : CommutesWithReg (rPGIdleOrig k_idle hk) (cSlackUnparkSingleCat 80 48 40).eval.1
      := compileRevList_commutesWithReg_rPGIdleOrig k_idle hk _ (fun s hs ↦
      slackParkSteps80_allAvoidPG48 s (List.mem_reverse.mp hs))
  have hCtrl : CommutesWithReg (rPGIdleOrig k_idle hk)
      (uCtrlRawBESingleCat prep selImpl c).1 := by
    unfold uCtrlRawBESingleCat
    simp only [Submonoid.coe_mul]
    exact (hBE _).mul (hUnpk.mul (hSelIdle.mul (hPk.mul (hBE _))))
  have hDiagX : CommutesWithReg (rPGIdleOrig k_idle hk) (((diagNegIPosICircuit
      (qSigInSingleCat 80 48 40)).seq (Circuit.X (qSigInSingleCat 80 48 40))).eval).1 := by
    unfold diagNegIPosICircuit Circuit.X Circuit.S Circuit.Z
    simp only [Circuit.eval_seq, Submonoid.coe_mul]
    exact (h1q .X).mul ((h1q .S).mul (((h1q .X).mul ((h1q .Z).mul (h1q .S))).mul (h1q .X)))
  have hPref : ∀ (t : ℕ) (postLast : Bool),
      CommutesWithReg (rPGIdleOrig k_idle hk)
        (uSingleGuardPrefixTwoAngleSingleCatGen (kWorkConst := 40) bValid (by decide : 42 ≤ 48) prep
          selImpl M C D c postLast t).1 := by
    intro t
    induction t with
    | zero =>
        intro postLast
        exact commutesWithReg_rPGIdleOrig_uGuardWrapTwoAngleGen bValid k_idle hk false postLast
          (biCode M C 0) (biCode M D 0)
          (dvd_biCode_of_forall_dvd hDivC 0) (dvd_biCode_of_forall_dvd hDivD 0)
    | succ t ih =>
        intro postLast
        unfold uSingleGuardPrefixTwoAngleSingleCatGen
        simp only [Submonoid.coe_mul]
        exact (commutesWithReg_rPGIdleOrig_uGuardWrapTwoAngleGen bValid k_idle hk true postLast
          (biCode M C (t + 1)) (biCode M D (t + 1))
          (dvd_biCode_of_forall_dvd hDivC (t + 1)) (dvd_biCode_of_forall_dvd hDivD (t + 1))).mul
          (hDiagX.mul (hCat.mul (ih false)))
  unfold uSegTwoAngleSingleCatGen Circuit.H Circuit.S Circuit.X Circuit.Z
  simp only [Circuit.eval_seq, Submonoid.coe_mul]
  exact (h1q .H).mul (((h1q .X).mul (h1q .S)).mul (hCtrl.mul ((hPref M true).mul (((h1q
    .Z).mul (h1q .S)).mul (hCtrl.mul (h1q .H))))))
set_option exponentiation.threshold 5000 in
theorem commutesWithReg_rPGIdleOrig_uSegOneAngleSingleCatGen
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (k_idle : ℕ) (hk : k_idle ≤ 48)
    (prep : FullSysPrepareBundle 80)
    (selImpl : SingleCatSelectImpl 80 48 qft selOra)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (hSelIdle : CommutesWithReg (rPGIdleOrig k_idle hk)
      (rSegOrig.embedUnitary (selImpl.uSelCat c)).1)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val) :
    CommutesWithReg (rPGIdleOrig k_idle hk)
      (uSegOneAngleSingleCatGen (kWorkConst := 40) bValid (by decide : 42 ≤ 48) prep
        selImpl M D c).1 := by
  let qSig := qSigInSingleCat 80 48 40
  have h1q := qSig80_single_comm_rPGIdleOrig k_idle hk
  have hPost : CommutesWithReg (rPGIdleOrig k_idle hk) (cPostOneAngle qSig).eval.1 := by
    unfold cPostOneAngle Circuit.H Circuit.S
    simp only [Circuit.eval_seq, Submonoid.coe_mul]
    exact (h1q .H).mul ((h1q .S).mul (h1q .H))
  have hPre : CommutesWithReg (rPGIdleOrig k_idle hk) (cPreOneAngle qSig).eval.1 := by
    unfold cPreOneAngle Circuit.H Circuit.S Circuit.Z
    simp only [Circuit.eval_seq, Submonoid.coe_mul]
    exact (h1q .H).mul ((h1q .Z).mul ((h1q .S).mul (h1q .H)))
  have hInner : CommutesWithReg (rPGIdleOrig k_idle hk)
      (uSegTwoAngleSingleCatGen (kWorkConst := 40) bValid (by decide : 42 ≤ 48) prep selImpl M
        (fun _ ↦ 0) D c).1 :=
    commutesWithReg_rPGIdleOrig_uSegTwoAngleSingleCatGen bValid k_idle hk prep selImpl M
      (fun _ ↦ 0) D c hSelIdle (fun _ ↦ Nat.dvd_zero _) hDivD
  unfold uSegOneAngleSingleCatGen
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  exact hPost.mul (hInner.mul hPre)
private theorem unitary_inv_comm_of_comm {d : ℕ} (U : Unitary d) (P : Operator d)
    (h : U.1 * P = P * U.1) : (U⁻¹).1 * P = P * (U⁻¹).1 := by
  have hL : (U⁻¹).1 * U.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  have hR : U.1 * (U⁻¹).1 = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  calc (U⁻¹).1 * P = (U⁻¹).1 * (P * (U.1 * (U⁻¹).1)) := by rw [hR, Matrix.mul_one]
    _ = ((U⁻¹).1 * U.1) * P * (U⁻¹).1 := by
          rw [← Matrix.mul_assoc P, ← h]
          simp only [Matrix.mul_assoc]
    _ = P * (U⁻¹).1 := by rw [hL, Matrix.one_mul]

private theorem unitary_mul_inv_conj_pow {d : ℕ} (H V W : Unitary d) (h : W * H = H * W)
    (r : ℕ) : (H * V)⁻¹ * (W ^ r * (H * V)) = V⁻¹ * W ^ r * V := by
  have hPow (t : ℕ) : W ^ t * H = H * W ^ t := by
    induction t with
    | zero => rw [_root_.pow_zero, one_mul, mul_one]
    | succ t ih => rw [_root_.pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← _root_.pow_succ]
  calc (H * V)⁻¹ * (W ^ r * (H * V))
    _ = (V⁻¹ * H⁻¹) * ((H * W ^ r) * V) := by
          rw [_root_.mul_inv_rev, ← mul_assoc (W ^ r), hPow r]
    _ = V⁻¹ * ((H⁻¹ * H) * (W ^ r * V)) := by simp only [mul_assoc]
    _ = V⁻¹ * W ^ r * V := by rw [inv_mul_cancel, one_mul, mul_assoc]

private theorem sandwich_intertwine_proj {d : ℕ} (Vi Wh Vp P E Up W0 Up_inv : Operator d) (r : ℕ)
    (hVp : Vp * P = E * Up) (hPow : Wh ^ r * E = E * W0 ^ r) (hVi : Vi * E = P * Up_inv) :
    (Vi * Wh ^ r * Vp) * P = P * (Up_inv * (W0 ^ r * Up)) := by
  calc (Vi * Wh ^ r * Vp) * P = Vi * ((Wh ^ r * E) * Up) := by
        rw [Matrix.mul_assoc (Vi * Wh ^ r), hVp]
        simp only [Matrix.mul_assoc]
    _ = (Vi * E) * (W0 ^ r * Up) := by
        rw [hPow]
        simp only [Matrix.mul_assoc]
    _ = P * (Up_inv * (W0 ^ r * Up)) := by rw [hVi, Matrix.mul_assoc]

set_option exponentiation.threshold 5000 in
private theorem vInvUltraExtHk_mul_E_segExt {mWork k_idle tStreamPair : ℕ}
    (hk : k_idle ≤ 48) (hk17 : k_idle ≤ 17)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) :
    (vInvUltraExtHk k_idle hk initSpec.uStreamInit).1 * E_segExt k_idle hk =
      pZeroInitExt k_idle hk *
        ((uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40))⁻¹).1 := by
  have hInvEq : (uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40))⁻¹ =
      rAct0.embedUnitary (vInvUltraSingleCat 80 48 40) * (uHadIdleFull k_idle hk)⁻¹ := by
    dsimp only [vPrepUltraSingleCat, vInvUltraSingleCat]
    rw [_root_.mul_inv_rev, embedUnitary_inv_symm]
  unfold vInvUltraExtHk
  rw [← hInvEq, Submonoid.coe_mul, Matrix.mul_assoc, uStreamInit_inv_mul_E_segExt hk initSpec,
    unitary_inv_comm_of_comm _ _ (uHadIdleFull_mul_vPrepUltra_comm_pZeroInitExt k_idle hk hk17)]

set_option exponentiation.threshold 5000 in
theorem unitarySandwichPow_ultra_extHk_oneAngleGen_mul_pZeroInitExt
    {mWork k_idle tStreamPair tSelCtrl tSelCat : ℕ}
    (bValid : Fin (2 ^ systemQubits) → Bool)
    (hk : k_idle ≤ 48) (hk17 : k_idle ≤ 17)
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra}
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair)
    (prep : FullSysPrepareBundle 80)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration) (r : ℕ)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) :
    (unitarySandwichPow (vInvUltraExtHk k_idle hk initSpec.uStreamInit)
        (uSegOneAngleExtHkGen bValid prep sel M D c)
        (vPrepUltraExtHk k_idle hk initSpec.uStreamInit) r).1 *
      pZeroInitExt k_idle hk =
      (rAct0.embedUnitary
        (unitarySandwichPow (vInvUltraSingleCat 80 48 40)
          (uSegOneAngleSingleCatGen (kWorkConst := 40) bValid (by decide : 42 ≤ 48) prep
            selImpl M D c)
          (vPrepUltraSingleCat 80 48 40) r)).1 *
        pZeroInitExt k_idle hk := by
  let W_h := uSegOneAngleExtHkGen bValid prep sel M D c
  let W_0 := uSegOneAngleSingleCatGen (kWorkConst := 40) bValid (by decide : 42 ≤ 48) prep
    selImpl M D c
  let U_pre : Unitary (2 ^ kFull80) :=
    uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)
  have hPow : W_h.1 ^ r * E_segExt k_idle hk = E_segExt k_idle hk * (rAct0.embedUnitary W_0).1
      ^ r := pow_mul_intertwine (uSegOneAngleExtHkGen_mul_E_segExt bValid prep sel M D c
      hDivD hPrepLow hPrepCtrl3) r
  have hVp : (vPrepUltraExtHk k_idle hk initSpec.uStreamInit).1 * pZeroInitExt k_idle hk =
      E_segExt k_idle hk * U_pre.1 := vPrepUltraExtHk_mul_pZeroInitExt hk hk17 initSpec
  have hVi : (vInvUltraExtHk k_idle hk initSpec.uStreamInit).1 * E_segExt k_idle hk =
      pZeroInitExt k_idle hk * (U_pre⁻¹).1 := vInvUltraExtHk_mul_E_segExt hk hk17 initSpec
  have hHadW0 : rAct0.embedUnitary W_0 * uHadIdleFull k_idle hk =
      uHadIdleFull k_idle hk * rAct0.embedUnitary W_0 := by
    apply Subtype.ext
    unfold uHadIdleFull
    simp only [Submonoid.coe_mul, QRegister.embedUnitary_val, ← rAct0.embedMatrix_mul]
    exact congrArg rAct0.embedMatrix (uHadIdleOrig_comm_of_commutesWithReg_rPGIdleOrig k_idle
      hk (commutesWithReg_rPGIdleOrig_uSegOneAngleSingleCatGen bValid k_idle hk prep
      selImpl M D c (sel.hSelIdle c) hDivD))
  have hCancelHad : U_pre⁻¹ * ((rAct0.embedUnitary W_0) ^ r * U_pre) =
      rAct0.embedUnitary
        (unitarySandwichPow (vInvUltraSingleCat 80 48 40) W_0 (vPrepUltraSingleCat 80 48 40) r) :=
          by
    dsimp only [U_pre, unitarySandwichPow]
    rw [unitary_mul_inv_conj_pow (uHadIdleFull k_idle hk)
        (rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)) (rAct0.embedUnitary W_0) hHadW0 r,
      embedUnitary_pow]
    dsimp only [vPrepUltraSingleCat, vInvUltraSingleCat]
    rw [embedUnitary_inv_symm, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
  have hCancelVal := congrArg Subtype.val hCancelHad
  rw [Submonoid.coe_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow] at hCancelVal
  have hEqProjMul : (unitarySandwichPow (vInvUltraExtHk k_idle hk initSpec.uStreamInit) W_h
      (vPrepUltraExtHk k_idle hk initSpec.uStreamInit) r).1 * pZeroInitExt k_idle hk =
      pZeroInitExt k_idle hk * (rAct0.embedUnitary (unitarySandwichPow (vInvUltraSingleCat 80
      48 40) W_0 (vPrepUltraSingleCat 80 48 40) r)).1 := by
    dsimp only [unitarySandwichPow] at hCancelVal ⊢
    rw [Submonoid.coe_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow,
      sandwich_intertwine_proj _ _ _ _ _ _ _ _ r hVp hPow hVi, hCancelVal]
  exact unitary_mul_proj_eq_of_eq_proj_mul _ _ (pZeroInitExt k_idle hk)
    ((rExt48IdleFull k_idle hk).basisOutcomeProjector_conjTranspose 0)
    (SingleRBEGridGuardWalk.basisOutcomeProjector_idem (rExt48IdleFull k_idle hk) 0)
    hEqProjMul
/-- Hoisted 1-angle unheld-syndrome Gidney guard prefix dynamic circuit on `(kFull80, mWork)` for
  general `bValid`. -/
noncomputable def dSingleGuardPrefixOneAngleUnheldGenDyn
    {Var : Type} {bValid : Fin (2 ^ systemQubits) → Bool}
    {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra}
    (hm1 : 1 ≤ mWork)
    (guard : OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (hmPrep : prep.mWorkPrep ≤ mWork)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42))
    (c : Configuration) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork)
    (postLast : Bool) : ℕ → DynamicCircuit Var n
  | 0 =>
      guard.dGuard1 false postLast (biCode M D 0) v rAct rWork hDisj
  | t + 1 =>
      DynCircuitExt.sequenceList [
        dSingleGuardPrefixOneAngleUnheldGenDyn hm1 guard prep sel hmPrep M D c v
          rAct rWork hDisj false t,
        catRawBEExtHkDyn prep sel hmPrep c v rAct rWork hDisj,
        substActiveSingleCat hm1 v (rAct.compose rAct0) rWork
          ((diagNegIPosICircuit (qSigInSingleCat 80 48 40)).seq
            (Circuit.X (qSigInSingleCat 80 48 40))),
        guard.dGuard1 true postLast (biCode M D (t + 1)) v rAct rWork hDisj
      ]
/-- Inner `(0, D)` Bi-GQSP segment dynamic circuit on `(kFull80, mWork)` for
  `OneAngleUnheldExtHkGuardSpecBundleGen`. -/
noncomputable def mkSegInnerOneAngleUnheldGenDyn {Var : Type}
    {bValid : Fin (2 ^ systemQubits) → Bool} {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork) (guard :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (M : ℕ)
    (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  let rAct170 := rAct.compose rAct0
  DynCircuitExt.sequenceList [
    substActiveSingleCat hm1 v rAct170 rWork (Circuit.H (qSigInSingleCat 80 48 40)),
    ctrlRawBEExtHkDyn hm1 prep sel hmPrep c v rAct rWork hDisj,
    substActiveSingleCat hm1 v rAct170 rWork
      ((Circuit.S (qSigInSingleCat 80 48 40)).seq (Circuit.Z (qSigInSingleCat 80 48 40))),
    dSingleGuardPrefixOneAngleUnheldGenDyn hm1 guard prep sel hmPrep M D c v
      rAct rWork hDisj true M,
    ctrlRawBEExtHkDyn hm1 prep sel hmPrep c v rAct rWork hDisj,
    substActiveSingleCat hm1 v rAct170 rWork
      ((Circuit.S (qSigInSingleCat 80 48 40)).seq (Circuit.X (qSigInSingleCat 80 48 40))),
    substActiveSingleCat hm1 v rAct170 rWork (Circuit.H (qSigInSingleCat 80 48 40))
  ]
/-- Hoisted 1-angle unheld-syndrome Bi-GQSP Gidney segment dynamic circuit on `(kFull80, mWork)`
for general `bValid`, achieving `wSegSingleCatExt48_TwoRot_T` (`2 * rotToffSum`). -/
noncomputable def mkSegOneAngleUnheldExtHkGenDyn {Var : Type}
    {bValid : Fin (2 ^ systemQubits) → Bool} {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork) (guard :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (M : ℕ)
    (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  let rAct170 := rAct.compose rAct0
  DynCircuitExt.sequenceList [
    substActiveSingleCat hm1 v rAct170 rWork (cPreOneAngle (qSigInSingleCat 80 48 40)),
    mkSegInnerOneAngleUnheldGenDyn hm1 guard prep sel hmPrep M D c v rAct rWork hDisj,
    substActiveSingleCat hm1 v rAct170 rWork (cPostOneAngle (qSigInSingleCat 80 48 40))
  ]
private theorem substActiveSingleCat_count_T_le_zero {Var : Type} {mWork n : ℕ}
    (hm1 : 1 ≤ mWork) (v : Var) (rA : QRegister kActOrig n)
    (rW : QRegister mWork n) (c : Circuit kActOrig)
    (hT : c.count T = 0) (hToff : c.count TOFF = 0) :
    (substActiveSingleCat hm1 v rA rW c).count T ≤ 0 :=
  (substActiveSingleCat_count_T_le hm1 v rA rW c).trans (by simp [hT, hToff])

theorem dSingleGuardPrefixOneAngleUnheldGenDyn_counts
    {Var : Type} {bValid : Fin (2 ^ systemQubits) → Bool}
    {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra}
    (hm1 : 1 ≤ mWork)
    (guard : OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (hmPrep : prep.mWorkPrep ≤ mWork)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42))
    (c : Configuration) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    ∀ (t : ℕ) (postLast : Bool),
      (dSingleGuardPrefixOneAngleUnheldGenDyn hm1 guard prep sel hmPrep M D c v
        rAct rWork hDisj postLast t).count TOFF = 0 ∧
      (dSingleGuardPrefixOneAngleUnheldGenDyn hm1 guard prep sel hmPrep M D c v
        rAct rWork hDisj postLast t).count T ≤
        t * (2 * prep.tPrep + tSelCat) +
          (t + 1) * tGuard +
          2 * biPrefixTwoAngleRotToffSum M (fun _ ↦ 0) D t
  | 0, postLast => by
      dsimp only [dSingleGuardPrefixOneAngleUnheldGenDyn]
      refine ⟨guard.hToff false postLast (biCode M D 0) v rAct rWork hDisj, ?_⟩
      have h0 : biPrefixTwoAngleRotToffSum M (fun _ ↦ 0) D 0 =
          gidneyTwoAngleRotToffEquiv 0 (biCode M D 0).val := by
        simp [biPrefixTwoAngleRotToffSum, biCode_zero_eq]
      have hg := guard.hT false postLast (biCode M D 0) v rAct rWork hDisj
      have hr := gidneyRotToffEquiv_le_twoAngle_zero_left (biCode M D 0).val
      rw [h0]; omega
  | t + 1, postLast => by
      have ih := dSingleGuardPrefixOneAngleUnheldGenDyn_counts hm1 guard prep sel hmPrep M D c v
        rAct rWork hDisj t false
      have hc := catRawBEExtHkDyn_counts prep sel hmPrep c v rAct rWork hDisj
      have h1q := substActiveSingleCat_count_T_le_zero hm1 v (rAct.compose rAct0) rWork
        ((diagNegIPosICircuit (qSigInSingleCat 80 48 40)).seq
          (Circuit.X (qSigInSingleCat 80 48 40)))
        (by simp [Circuit.count_seq, diagNegIPosICircuit_count_T, Circuit.X, Circuit.single])
        (by simp [Circuit.count_seq, diagNegIPosICircuit_count_TOFF, Circuit.X, Circuit.single])
      have hgToff := guard.hToff true postLast (biCode M D (t + 1)) v rAct rWork hDisj
      have hg := guard.hT true postLast (biCode M D (t + 1)) v rAct rWork hDisj
      have hr := gidneyRotToffEquiv_le_twoAngle_zero_left (biCode M D (t + 1)).val
      have hsum : biPrefixTwoAngleRotToffSum M (fun _ ↦ 0) D (t + 1) =
          biPrefixTwoAngleRotToffSum M (fun _ ↦ 0) D t +
            gidneyTwoAngleRotToffEquiv 0 (biCode M D (t + 1)).val := by
        unfold biPrefixTwoAngleRotToffSum
        rw [Finset.sum_range_succ, biCode_zero_eq]
        rfl
      dsimp only [dSingleGuardPrefixOneAngleUnheldGenDyn]
      simp only [DynCircuitExt.count_sequenceList, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, substActiveSingleCat_count_TOFF]
      refine ⟨by rw [ih.1, hc.1, hgToff]; rfl, ?_⟩
      refine (Nat.add_le_add ih.2 (Nat.add_le_add hc.2
        (Nat.add_le_add h1q (Nat.add_le_add hg (le_refl 0))))).trans ?_
      rw [hsum]
      have hArith : ∀ a b d e₁ e₂ : ℕ, e₁ ≤ e₂ → (t * a + (t + 1) * b + 2 * d) +
          (a + (0 + ((b + 2 * e₁) + 0))) ≤ (t + 1) * a + (t + 1 + 1) * b + 2 * (d + e₂) := by
        intros; simp only [Nat.add_mul, one_mul]; omega
      exact hArith (2 * prep.tPrep + tSelCat) tGuard
        (biPrefixTwoAngleRotToffSum M (fun _ ↦ 0) D t)
        (gidneyRotToffEquiv (biCode M D (t + 1)).val)
        (gidneyTwoAngleRotToffEquiv 0 (biCode M D (t + 1)).val) hr
theorem mkSegInnerOneAngleUnheldGenDyn_counts {Var : Type}
    {bValid : Fin (2 ^ systemQubits) → Bool} {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork) (guard :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (M rotToffSum : ℕ)
    (D : Fin (M + 1) → Fin (2 ^ 42)) (hRot : ∑ t : Fin (M + 1), gidneyRotToffEquiv (D t).val ≤
    rotToffSum) (c : Configuration) (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (mkSegInnerOneAngleUnheldGenDyn hm1 guard prep sel hmPrep M D c v rAct rWork
    hDisj).count TOFF = 0 ∧ (mkSegInnerOneAngleUnheldGenDyn hm1 guard prep sel hmPrep M D
    c v rAct rWork hDisj).count T ≤ wSegSingleCatExt48_TwoRot_T prep.tPrep tSelCtrl tSelCat
    tGuard rotToffSum M := by
  let rAct170 := rAct.compose rAct0
  have hh := substActiveSingleCat_count_T_le_zero hm1 v rAct170 rWork
    (Circuit.H (qSigInSingleCat 80 48 40))
    (by simp [Circuit.H, Circuit.single]) (by simp [Circuit.H, Circuit.single])
  have hsz := substActiveSingleCat_count_T_le_zero hm1 v rAct170 rWork
    ((Circuit.S (qSigInSingleCat 80 48 40)).seq (Circuit.Z (qSigInSingleCat 80 48 40)))
    (by simp [Circuit.count_seq, Circuit.S, Circuit.Z, Circuit.single])
    (by simp [Circuit.count_seq, Circuit.S, Circuit.Z, Circuit.single])
  have hsx := substActiveSingleCat_count_T_le_zero hm1 v rAct170 rWork
    ((Circuit.S (qSigInSingleCat 80 48 40)).seq (Circuit.X (qSigInSingleCat 80 48 40)))
    (by simp [Circuit.count_seq, Circuit.S, Circuit.X, Circuit.single])
    (by simp [Circuit.count_seq, Circuit.S, Circuit.X, Circuit.single])
  have hc := ctrlRawBEExtHkDyn_counts hm1 prep sel hmPrep c v rAct rWork hDisj
  have hpref := dSingleGuardPrefixOneAngleUnheldGenDyn_counts hm1 guard prep sel hmPrep M D c v
    rAct rWork hDisj M true
  rw [biPrefixTwoAngleRotToffSum_eq_univ_sum, sum_gidneyTwoAngleRotToffEquiv_zero_left] at hpref
  dsimp only [mkSegInnerOneAngleUnheldGenDyn, wSegSingleCatExt48_TwoRot_T]
  simp only [DynCircuitExt.count_sequenceList, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, substActiveSingleCat_count_TOFF]
  refine ⟨by rw [hc.1, hpref.1]; rfl, ?_⟩
  refine (Nat.add_le_add hh (Nat.add_le_add hc.2 (Nat.add_le_add hsz (Nat.add_le_add hpref.2
    (Nat.add_le_add hc.2 (Nat.add_le_add hsx (Nat.add_le_add hh (le_refl 0)))))))).trans ?_
  have hArith : ∀ {aCtrl aCat b d e : ℕ}, d ≤ e → 0 + ((aCtrl + 24) + (0 + ((M * aCat + (M +
      1) * b + 2 * d) + ((aCtrl + 24) + (0 + (0 + 0)))))) ≤ 2 * aCtrl + M * aCat + (M + 1) * b
      + 2 * e + 48 := by
    intros; omega
  exact hArith hRot
theorem mkSegOneAngleUnheldExtHkGenDyn_counts {Var : Type}
    {bValid : Fin (2 ^ systemQubits) → Bool} {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork) (guard :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (M rotToffSum : ℕ)
    (D : Fin (M + 1) → Fin (2 ^ 42)) (hRot : ∑ t : Fin (M + 1), gidneyRotToffEquiv (D t).val ≤
    rotToffSum) (c : Configuration) (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (mkSegOneAngleUnheldExtHkGenDyn hm1 guard prep sel hmPrep M D c v rAct rWork
    hDisj).count TOFF = 0 ∧ (mkSegOneAngleUnheldExtHkGenDyn hm1 guard prep sel hmPrep M D
    c v rAct rWork hDisj).count T ≤ wSegSingleCatExt48_TwoRot_T prep.tPrep tSelCtrl tSelCat
    tGuard rotToffSum M := by
  let rAct170 := rAct.compose rAct0
  have hPreT := substActiveSingleCat_count_T_le_zero hm1 v rAct170 rWork
    (cPreOneAngle (qSigInSingleCat 80 48 40)) (cPreOneAngle_counts _).2 (cPreOneAngle_counts _).1
  have hPostT := substActiveSingleCat_count_T_le_zero hm1 v rAct170 rWork
    (cPostOneAngle (qSigInSingleCat 80 48 40))
    (cPostOneAngle_counts _).2 (cPostOneAngle_counts _).1
  have hInner := mkSegInnerOneAngleUnheldGenDyn_counts hm1 guard prep sel hmPrep M rotToffSum
    D hRot c v rAct rWork hDisj
  dsimp only [mkSegOneAngleUnheldExtHkGenDyn]
  simp only [DynCircuitExt.count_sequenceList, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, substActiveSingleCat_count_TOFF]
  refine ⟨by rw [hInner.1]; rfl, ?_⟩
  dsimp only [rAct170] at hPreT hPostT
  exact (Nat.add_le_add hPreT (Nat.add_le_add hInner.2 (Nat.add_le_add hPostT (le_refl 0)))).trans
    (by omega)
set_option exponentiation.threshold 5000 in
theorem dSingleGuardPrefixOneAngleUnheldGenDyn_realizesOnProj
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {bValid : Fin (2 ^ systemQubits) → Bool}
    {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ} [NeZero (2 ^ n)] {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra}
    (hm1 : 1 ≤ mWork)
    (guard : OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80)
    (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (hmPrep : prep.mWorkPrep ≤ mWork)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1)
    (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    ∀ (t : ℕ) (postLast : Bool),
      RealizesOnProj (pHoistExtOn k_idle hk rAct rWork)
        (rAct.embedUnitary (uSingleGuardPrefixExtHkTwoAngleGen bValid prep sel M (fun _ ↦
          0) D c postLast t))
        (dSingleGuardPrefixOneAngleUnheldGenDyn hm1 guard prep sel hmPrep M D c v
          rAct rWork hDisj postLast t)
  | 0, postLast => by
      dsimp only [uSingleGuardPrefixExtHkTwoAngleGen, dSingleGuardPrefixOneAngleUnheldGenDyn]
      rw [biCode_zero_eq]
      exact guard.hRealizes false postLast (biCode M D 0)
        (dvd_biCode_of_forall_dvd hDivD 0) v rAct rWork hDisj
  | t + 1, postLast => by
      have hDiv0 : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣
          ((fun _ : Fin (M + 1) ↦ (0 : Fin (2 ^ 42))) i).val := fun _ ↦ Nat.dvd_zero _
      have p1 := dSingleGuardPrefixOneAngleUnheldGenDyn_realizesOnProj hm1 guard prep sel hmPrep
        M D c hDivD hPrepLow hPrepCtrl3 v rAct rWork hDisj t false
      have p2 := catRawBEExtHkDyn_realizesOnProj prep sel hmPrep c hPrepLow hPrepCtrl3 v
        rAct rWork hDisj
      have p3 := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
          ((realizesCleanWorkspace_substActiveSingleCat hm1 v (rAct.compose rAct0) rWork
          (hDisj.compose_left rAct0) ((diagNegIPosICircuit (qSigInSingleCat 80 48 40)).seq
          (Circuit.X (qSigInSingleCat 80 48 40)))).widenActive)
      have p4 := guard.hRealizes true postLast (biCode M D (t + 1))
        (dvd_biCode_of_forall_dvd hDivD (t + 1)) v rAct rWork hDisj
      rw [← biCode_zero_eq M (t + 1)] at p4
      have hPrefE :=
        uSingleGuardPrefixExtHkTwoAngleGen_mul_E_segExt bValid prep sel M (fun _ ↦ 0) D c
        hDiv0 hDivD hPrepLow hPrepCtrl3 t false
      have hCatE := uCatRawBEExtHk_mul_E_segExt prep sel c hPrepLow hPrepCtrl3
      have h1qE := qSig_diagSeqX_comm_E_segExt k_idle hk
      have hGwE := uGuardWrapTwoAngleGen_comm_E_segExt bValid k_idle hk true postLast
        (biCode M (fun _ ↦ 0) (t + 1)) (biCode M D (t + 1))
        (dvd_biCode_of_forall_dvd hDiv0 (t + 1)) (dvd_biCode_of_forall_dvd hDivD (t + 1))
      have hChain := p1.seq_intertwine (embedIntertwine2 hDisj hPrefE) (p2.seq_intertwine
          (embedIntertwine2 hDisj hCatE) (p3.seq_intertwine (embedIntertwine2 hDisj h1qE)
          (p4.seq_intertwine (embedIntertwine2 hDisj hGwE) (RealizesOnProj.identity
          (pHoistExtOn k_idle hk rAct rWork)))))
      simpa only [pHoistExtOn, dSingleGuardPrefixOneAngleUnheldGenDyn,
        uSingleGuardPrefixExtHkTwoAngleGen,
        DynCircuitExt.sequenceList_cons, DynCircuitExt.sequenceList_nil,
        QRegister.embedUnitary_mul, one_mul, mul_assoc] using hChain
set_option exponentiation.threshold 5000 in
theorem mkSegInnerOneAngleUnheldGenDyn_realizesOnProj {Var : Type} [Fintype Var]
    [DecidableEq Var] {bValid : Fin (2 ^ systemQubits) → Bool}
    {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ} [NeZero (2 ^ n)] {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork) (guard :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (M : ℕ)
    (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : RealizesOnProj
    (pHoistExtOn k_idle hk rAct rWork) (rAct.embedUnitary (uSegExtHkTwoAngleGen bValid
    prep sel M (fun _ ↦ 0) D c)) (mkSegInnerOneAngleUnheldGenDyn hm1 guard prep sel
    hmPrep M D c v rAct rWork hDisj) := by
  let rAct170 := rAct.compose rAct0
  have hDiv0 : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣
      ((fun _ : Fin (M + 1) ↦ (0 : Fin (2 ^ 42))) i).val := fun _ ↦ Nat.dvd_zero _
  have pH := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    ((realizesCleanWorkspace_substActiveSingleCat hm1 v rAct170 rWork
      (hDisj.compose_left rAct0) (Circuit.H (qSigInSingleCat 80 48 40))).widenActive)
  have pCtrl := ctrlRawBEExtHkDyn_realizesOnProj hm1 prep sel hmPrep c hPrepLow hPrepCtrl3 v
    rAct rWork hDisj
  have pSZ := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    ((realizesCleanWorkspace_substActiveSingleCat hm1 v rAct170 rWork
      (hDisj.compose_left rAct0)
      ((Circuit.S (qSigInSingleCat 80 48 40)).seq
        (Circuit.Z (qSigInSingleCat 80 48 40)))).widenActive)
  have pPref := dSingleGuardPrefixOneAngleUnheldGenDyn_realizesOnProj hm1 guard prep sel hmPrep
    M D c hDivD hPrepLow hPrepCtrl3 v rAct rWork hDisj M true
  have pSX := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    ((realizesCleanWorkspace_substActiveSingleCat hm1 v rAct170 rWork
      (hDisj.compose_left rAct0)
      ((Circuit.S (qSigInSingleCat 80 48 40)).seq
        (Circuit.X (qSigInSingleCat 80 48 40)))).widenActive)
  have hHE := qSig_single_comm_E_segExt k_idle hk .H
  have hCtrlE := uCtrlRawBEExtHk_mul_E_segExt prep sel c hPrepLow hPrepCtrl3
  have hPrefE := uSingleGuardPrefixExtHkTwoAngleGen_mul_E_segExt bValid prep sel M (fun _ ↦ 0) D c
    hDiv0 hDivD hPrepLow hPrepCtrl3 M true
  have hSZE := qSig_seq_comm_E_segExt k_idle hk .S .Z
  have hSXE := qSig_seq_comm_E_segExt k_idle hk .S .X
  have hChain := pH.seq_intertwine (embedIntertwine2 hDisj hHE) (pCtrl.seq_intertwine
      (embedIntertwine2 hDisj hCtrlE) (pSZ.seq_intertwine (embedIntertwine2 hDisj hSZE)
      (pPref.seq_intertwine (embedIntertwine2 hDisj hPrefE) (pCtrl.seq_intertwine
      (embedIntertwine2 hDisj hCtrlE) (pSX.seq_intertwine (embedIntertwine2 hDisj hSXE)
      (pH.seq_intertwine (embedIntertwine2 hDisj hHE) (RealizesOnProj.identity (pHoistExtOn
      k_idle hk rAct rWork))))))))
  simpa only [pHoistExtOn, mkSegInnerOneAngleUnheldGenDyn, uSegExtHkTwoAngleGen,
    DynCircuitExt.sequenceList_cons, DynCircuitExt.sequenceList_nil,
    QRegister.embedUnitary_mul, one_mul, mul_assoc] using hChain
set_option exponentiation.threshold 5000 in
theorem mkSegOneAngleUnheldExtHkGenDyn_realizesOnProj {Var : Type} [Fintype Var]
    [DecidableEq Var] {bValid : Fin (2 ^ systemQubits) → Bool}
    {mWork k_idle tGuard tSelCtrl tSelCat n : ℕ} [NeZero (2 ^ n)] {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork) (guard :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (M : ℕ)
    (D : Fin (M + 1) → Fin (2 ^ 42)) (c : Configuration)
    (hDivD : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣ (D i).val)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : RealizesOnProj
    (pHoistExtOn k_idle hk rAct rWork) (rAct.embedUnitary (uSegOneAngleExtHkGen bValid
    prep sel M D c)) (mkSegOneAngleUnheldExtHkGenDyn hm1 guard prep sel hmPrep M D c v
    rAct rWork hDisj) := by
  let rAct170 := rAct.compose rAct0
  have hDiv0 : ∀ i : Fin (M + 1), 2 ^ (k_idle - 6) ∣
      ((fun _ : Fin (M + 1) ↦ (0 : Fin (2 ^ 42))) i).val := fun _ ↦ Nat.dvd_zero _
  have pPre := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    ((realizesCleanWorkspace_substActiveSingleCat hm1 v rAct170 rWork
      (hDisj.compose_left rAct0) (cPreOneAngle (qSigInSingleCat 80 48 40))).widenActive)
  have pSeg := mkSegInnerOneAngleUnheldGenDyn_realizesOnProj hm1 guard prep sel hmPrep M
    D c hDivD hPrepLow hPrepCtrl3 v rAct rWork hDisj
  have pPost := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    ((realizesCleanWorkspace_substActiveSingleCat hm1 v rAct170 rWork
      (hDisj.compose_left rAct0) (cPostOneAngle (qSigInSingleCat 80 48 40))).widenActive)
  have hPreE := cPreOneAngle_comm_E_segExt k_idle hk
  have hSegE := uSegExtHkTwoAngleGen_mul_E_segExt bValid prep sel M (fun _ ↦ 0) D c
    hDiv0 hDivD hPrepLow hPrepCtrl3
  have hPostE := cPostOneAngle_comm_E_segExt k_idle hk
  have hChain := pPre.seq_intertwine (embedIntertwine2 hDisj hPreE) (pSeg.seq_intertwine
      (embedIntertwine2 hDisj hSegE) (pPost.seq_intertwine (embedIntertwine2 hDisj hPostE)
      (RealizesOnProj.identity (pHoistExtOn k_idle hk rAct rWork))))
  simpa only [pHoistExtOn, mkSegOneAngleUnheldExtHkGenDyn, uSegOneAngleExtHkGen,
    DynCircuitExt.sequenceList_cons, DynCircuitExt.sequenceList_nil,
    QRegister.embedUnitary_mul, one_mul, mul_assoc] using hChain
/-- Canonical fermionic `|0⟩_anc` projector `fermionicProjector spinUp ⊗ |0⟩⟨0|_anc` on
  `systemQubits + m`. -/
noncomputable abbrev pFermBE (spinUp : Finset (Fin numElectrons)) (m : ℕ) : Operator
    (2 ^ (systemQubits + m)) := projGridAncZero systemQubits m (fermionicProjector spinUp)
/-- Single-step fermionic Krylov invariance condition: applying `U_raw` once to a valid fermionic
  state
(`pFermBE spinUp m`) produces a state supported strictly within the `badElecCount ≤ 3` Krylov
subspace. -/
def RawBEMapsFermToKrylov3 (spinUp : Finset (Fin numElectrons)) {m : ℕ}
    (U_raw : Unitary (2 ^ (systemQubits + m))) : Prop :=
    (QRegister.block 0 systemQubits (by omega)).embedMatrix krylov3Proj *
    (U_raw.1 * pFermBE spinUp m) = U_raw.1 * pFermBE spinUp m
/-- Top-left grid-valid block `pgBE m * U_raw.1 * pgBE m` commutes with `fermionicProjector
  spinUp`. -/
def RawBEBlockCommutesFerm (spinUp : Finset (Fin numElectrons)) {m : ℕ}
    (U_raw : Unitary (2 ^ (systemQubits + m))) : Prop :=
  let rSysBE : QRegister systemQubits (systemQubits + m) :=
    QRegister.block 0 systemQubits (by omega)
  Commute (pgBE m * U_raw.1 * pgBE m) (rSysBE.embedMatrix (fermionicProjector spinUp))
theorem fermionicProjector_mul_specsGridProjector (spinUp : Finset (Fin numElectrons)) :
    fermionicProjector spinUp * SpecsAux.gridProjector =
      fermionicProjector spinUp := by
  have h := congrArg Matrix.conjTranspose
    (SpecsAux.gridProjector_mul_fermionicProjector spinUp)
  rwa [Matrix.conjTranspose_mul, (SpecsAux.fermionicProjector_isHermitian
    spinUp).eq, SpecsAux.gridProjector_isHermitian.eq] at h
theorem pFermBE_eq_pgBE_mul (spinUp : Finset (Fin numElectrons)) (m : ℕ) :
    let rSysBE : QRegister systemQubits (systemQubits + m) :=
      QRegister.block 0 systemQubits (by omega)
    pgBE m * rSysBE.embedMatrix (fermionicProjector spinUp) = pFermBE spinUp m := by
  intro rSysBE
  let rAncBE : QRegister m (systemQubits + m) := QRegister.block systemQubits m le_rfl
  have hDisj : rSysBE.DisjointWires rAncBE :=
    QRegister.block_disjoint_of_le 0 systemQubits systemQubits m (by omega) le_rfl (by omega)
  have hcF := embedMatrix_comm_basisOutcomeProjector_disjoint rSysBE rAncBE hDisj
    (fermionicProjector spinUp) 0
  unfold pgBE pFermBE projGridAncZero
  dsimp only [rSysBE, rAncBE] at hcF ⊢
  rw [Matrix.mul_assoc, ← hcF, ← Matrix.mul_assoc, ← QRegister.embedMatrix_mul,
    diagProj_gridValidBool_eq_specsGridProjector,
    SpecsAux.gridProjector_mul_fermionicProjector]
theorem pFermBE_eq_mul_pgBE (spinUp : Finset (Fin numElectrons)) (m : ℕ) :
    let rSysBE : QRegister systemQubits (systemQubits + m) :=
      QRegister.block 0 systemQubits (by omega)
    rSysBE.embedMatrix (fermionicProjector spinUp) * pgBE m = pFermBE spinUp m := by
  intro rSysBE
  unfold pgBE pFermBE projGridAncZero
  dsimp only [rSysBE]
  rw[← Matrix.mul_assoc, ← QRegister.embedMatrix_mul,
      diagProj_gridValidBool_eq_specsGridProjector, fermionicProjector_mul_specsGridProjector]
theorem pgBE_mul_pFermBE (spinUp : Finset (Fin numElectrons)) (m : ℕ) :
    pgBE m * pFermBE spinUp m = pFermBE spinUp m := by
  rw [← pFermBE_eq_pgBE_mul spinUp m, ← Matrix.mul_assoc,
    projGridAncZero_idem systemQubits m (diagProj_idem systemQubits gridValidBool)]
theorem pgBE_mul_raw_mul_pFermBE {spinUp : Finset (Fin numElectrons)} {m : ℕ}
    {U_raw : Unitary (2 ^ (systemQubits + m))}
    (hBlockComm : RawBEBlockCommutesFerm spinUp U_raw) :
    pgBE m * (U_raw.1 * pFermBE spinUp m) = pFermBE spinUp m * (U_raw.1 * pgBE m) := by
  let rSysBE : QRegister systemQubits (systemQubits + m) :=
    QRegister.block 0 systemQubits (by omega)
  have hc : (pgBE m * U_raw.1 * pgBE m) * rSysBE.embedMatrix (fermionicProjector spinUp) =
      rSysBE.embedMatrix (fermionicProjector spinUp) * (pgBE m * U_raw.1 * pgBE m) := hBlockComm.eq
  calc pgBE m * (U_raw.1 * pFermBE spinUp m)
    _ = pgBE m * (U_raw.1 * (pgBE m * rSysBE.embedMatrix (fermionicProjector spinUp))) := by
          rw [pFermBE_eq_pgBE_mul spinUp m]
    _ = (pgBE m * U_raw.1 * pgBE m) * rSysBE.embedMatrix (fermionicProjector spinUp) := by
          simp only [Matrix.mul_assoc]
    _ = rSysBE.embedMatrix (fermionicProjector spinUp) * (pgBE m * U_raw.1 * pgBE m) := hc
    _ = (rSysBE.embedMatrix (fermionicProjector spinUp) * pgBE m) * (U_raw.1 * pgBE m) := by
          simp only [Matrix.mul_assoc]
    _ = pFermBE spinUp m * (U_raw.1 * pgBE m) := by
          rw [pFermBE_eq_mul_pgBE spinUp m]
/-- Lifted 2D fermionic Involutive Krylov right-ideal `E₀ * A + E₁ * B` on `systemQubits + (m +
  1)`. -/
def InLiftedKrylovSpanFerm (spinUp : Finset (Fin numElectrons)) {m : ℕ}
    (U_raw : Unitary (2 ^ (systemQubits + m)))
    (X : Operator (2 ^ (systemQubits + (m + 1)))) : Prop :=
  let rBE : QRegister (systemQubits + m) (systemQubits + (m + 1)) :=
    QRegister.block 0 (systemQubits + m) (by omega)
  ∃ A B : Operator (2 ^ (systemQubits + (m + 1))),
    X = rBE.embedMatrix (pFermBE spinUp m) * A + rBE.embedMatrix (U_raw.1 * pFermBE spinUp m) * B
/-- Exact 2-angle segment equality on `fermionicProjector spinUp ⊗ |0⟩_{m+1}` (and any
`InLiftedKrylovSpanFerm` state) whenever `bValid` agrees with `gridValidBool` on `badElecCount ≤ 3`,
`U_raw² = 1`, `RawBEMapsFermToKrylov3 spinUp U_raw`, and `RawBEBlockCommutesFerm spinUp U_raw`. -/
private theorem inLiftedKrylovSpanFerm_sig_mul (spinUp : Finset (Fin numElectrons)) {m : ℕ}
    (U_raw : Unitary (2 ^ (systemQubits + m))) (M2 : Operator 2)
    {Y : Operator (2 ^ (systemQubits + (m + 1)))} (hY : InLiftedKrylovSpanFerm spinUp U_raw Y) :
    InLiftedKrylovSpanFerm spinUp U_raw
      ((QRegister.singleton ⟨systemQubits + m, by omega⟩).embedMatrix M2 * Y) := by
  let rBE : QRegister (systemQubits + m) (systemQubits + (m + 1)) :=
    QRegister.block 0 (systemQubits + m) (by omega)
  have hDisj : rBE.DisjointWires (QRegister.singleton ⟨systemQubits + m, by omega⟩) := by
    rw [QRegister.disjoint_iff]
    intro i j h
    fin_cases j
    have hv := congrArg Fin.val h
    simp [rBE, QRegister.singleton] at hv
    omega
  rcases hY with ⟨A, B, rfl⟩
  have hc0 := (rBE.embedMatrix_comm_of_disjoint _ hDisj (pFermBE spinUp m) M2).symm
  have hc1 := (rBE.embedMatrix_comm_of_disjoint _ hDisj (U_raw.1 * pFermBE spinUp m) M2).symm
  refine ⟨(QRegister.singleton ⟨systemQubits + m, by omega⟩).embedMatrix M2 * A,
    (QRegister.singleton ⟨systemQubits + m, by omega⟩).embedMatrix M2 * B, ?_⟩
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hc0, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (rBE.embedMatrix (U_raw.1 * pFermBE spinUp m)), hc1, Matrix.mul_assoc]

theorem physBiTwoAngleSegmentUnitaryGen_mul_inLiftedKrylovSpanFerm_eq
    {spinUp : Finset (Fin numElectrons)} {m : ℕ} {bValid : Fin (2 ^ systemQubits) → Bool}
    (hbValid : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x) (M : ℕ)
    (C D : Fin (M + 1) → Fin (2 ^ 42)) (U_raw : Unitary (2 ^ (systemQubits + m)))
    (hU2 : U_raw.1 * U_raw.1 = 1) (hKrylovFerm : RawBEMapsFermToKrylov3 spinUp U_raw)
    (hBlockComm : RawBEBlockCommutesFerm spinUp U_raw)
    {X : Operator (2 ^ (systemQubits + (m + 1)))} (hX : InLiftedKrylovSpanFerm spinUp U_raw X)
    : (physBiTwoAngleSegmentUnitaryGen bValid M C D U_raw).1 * X =
    (physBiTwoAngleSegmentUnitaryGen gridValidBool M C D U_raw).1 * X ∧ InLiftedKrylovSpanFerm
    spinUp U_raw ((physBiTwoAngleSegmentUnitaryGen gridValidBool M C D U_raw).1 * X) := by
  let rBE : QRegister (systemQubits + m) (systemQubits + (m + 1)) :=
    QRegister.block 0 (systemQubits + m) (by omega)
  let q_sig : Wire (systemQubits + (m + 1)) := ⟨systemQubits + m, by omega⟩
  let E₀ := rBE.embedMatrix (pFermBE spinUp m)
  let E₁ := rBE.embedMatrix (U_raw.1 * pFermBE spinUp m)
  have hAdd {Y Z} : InLiftedKrylovSpanFerm spinUp U_raw Y →
      InLiftedKrylovSpanFerm spinUp U_raw Z → InLiftedKrylovSpanFerm spinUp U_raw (Y + Z) := by
    rintro ⟨A₁, B₁, rfl⟩ ⟨A₂, B₂, rfl⟩
    refine ⟨A₁ + A₂, B₁ + B₂, ?_⟩
    change (E₀ * A₁ + E₁ * B₁) + (E₀ * A₂ + E₁ * B₂) = E₀ * (A₁ + A₂) + E₁ * (B₁ + B₂)
    rw [Matrix.mul_add, Matrix.mul_add]
    abel
  have hSmul (z : ℂ) {Y} : InLiftedKrylovSpanFerm spinUp U_raw Y →
      InLiftedKrylovSpanFerm spinUp U_raw (z • Y) := by
    rintro ⟨A, B, rfl⟩
    refine ⟨z • A, z • B, ?_⟩
    change z • (E₀ * A + E₁ * B) = E₀ * (z • A) + E₁ * (z • B)
    rw [smul_add, mul_smul_comm, mul_smul_comm]
  have hSig (M2 : Operator 2) {Y} := inLiftedKrylovSpanFerm_sig_mul spinUp U_raw M2 (Y := Y)
  have hK_PG : (QRegister.block 0 systemQubits (by omega)).embedMatrix krylov3Proj * pgBE m =
      pgBE m := by
    unfold pgBE projGridAncZero; dsimp only
    rw [← Matrix.mul_assoc, ← QRegister.embedMatrix_mul, krylov3Proj_mul_diagProj_gridValidBool]
  have hK_PF : (QRegister.block 0 systemQubits (by omega)).embedMatrix krylov3Proj *
      pFermBE spinUp m = pFermBE spinUp m := by
    rw [← pFermBE_eq_pgBE_mul spinUp m, ← Matrix.mul_assoc, hK_PG]
  have hR_PF_eq : physGridReflGen systemQubits m bValid * pFermBE spinUp m =
      physGridReflGen systemQubits m gridValidBool * pFermBE spinUp m :=
    physGridReflGen_eq_on_krylov3 hbValid hK_PF
  have hR_UPF_eq : physGridReflGen systemQubits m bValid * (U_raw.1 * pFermBE spinUp m) =
      physGridReflGen systemQubits m gridValidBool * (U_raw.1 * pFermBE spinUp m) :=
    physGridReflGen_eq_on_krylov3 hbValid hKrylovFerm
  have hR_PF_val : physGridReflGen systemQubits m gridValidBool * pFermBE spinUp m =
      pFermBE spinUp m := by
    change ((2 : ℂ) • pgBE m - 1) * pFermBE spinUp m = pFermBE spinUp m
    rw [Matrix.sub_mul, smul_mul_assoc, pgBE_mul_pFermBE spinUp m,
      Matrix.one_mul, two_smul, add_sub_cancel_left]
  have hR_UPF_val : physGridReflGen systemQubits m gridValidBool * (U_raw.1 * pFermBE spinUp m) =
      pFermBE spinUp m * ((2 : ℂ) • (U_raw.1 * pgBE m)) - U_raw.1 * pFermBE spinUp m := by
    change ((2 : ℂ) • pgBE m - 1) * (U_raw.1 * pFermBE spinUp m) = _
    rw [Matrix.sub_mul, smul_mul_assoc, pgBE_mul_raw_mul_pFermBE hBlockComm,
      ← mul_smul_comm, Matrix.one_mul]
  let R_b := rBE.embedMatrix (physGridReflGen systemQubits m bValid)
  let R_g := rBE.embedMatrix (physGridReflGen systemQubits m gridValidBool)
  let U_emb := rBE.embedMatrix U_raw.1
  have hRefl : ∀ {Y}, InLiftedKrylovSpanFerm spinUp U_raw Y →
      R_b * Y = R_g * Y ∧ InLiftedKrylovSpanFerm spinUp U_raw (R_g * Y) := by
    rintro Y ⟨A, B, rfl⟩
    have hRb0 : R_b * E₀ = R_g * E₀ := by
      dsimp only [R_b, R_g, E₀]; rw [← rBE.embedMatrix_mul, ← rBE.embedMatrix_mul, hR_PF_eq]
    have hRb1 : R_b * E₁ = R_g * E₁ := by
      dsimp only [R_b, R_g, E₁]; rw [← rBE.embedMatrix_mul, ← rBE.embedMatrix_mul, hR_UPF_eq]
    have hRg0 : R_g * E₀ = E₀ := by
      dsimp only [R_g, E₀]; rw [← rBE.embedMatrix_mul, hR_PF_val]
    have hRg1 : R_g * E₁ = E₀ * rBE.embedMatrix ((2 : ℂ) • (U_raw.1 * pgBE m)) + E₁ * (-1) := by
      dsimp only [R_g, E₀, E₁]
      rw [← rBE.embedMatrix_mul, hR_UPF_val, sub_eq_add_neg, rBE.embedMatrix_add,
        rBE.embedMatrix_mul, embedMatrix_neg_poly, Matrix.mul_neg, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · change R_b * (E₀ * A + E₁ * B) = R_g * (E₀ * A + E₁ * B)
      rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, hRb0, Matrix.mul_assoc,
        ← Matrix.mul_assoc R_b, hRb1, Matrix.mul_assoc]
    · refine ⟨A + rBE.embedMatrix ((2 : ℂ) • (U_raw.1 * pgBE m)) * B, -B, ?_⟩
      change R_g * (E₀ * A + E₁ * B) = _
      rw [Matrix.mul_add, ← Matrix.mul_assoc, hRg0, ← Matrix.mul_assoc R_g, hRg1,
        Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_one, neg_mul,
        Matrix.mul_add, Matrix.mul_neg]
      abel
  have hUemb : ∀ {Y}, InLiftedKrylovSpanFerm spinUp U_raw Y →
      InLiftedKrylovSpanFerm spinUp U_raw (U_emb * Y) := by
    rintro Y ⟨A, B, rfl⟩
    have hU0 : U_emb * E₀ = E₁ := by dsimp only [U_emb, E₀, E₁]; rw [← rBE.embedMatrix_mul]
    have hU1 : U_emb * E₁ = E₀ := by
      dsimp only [U_emb, E₀, E₁]; rw [← rBE.embedMatrix_mul, ← Matrix.mul_assoc, hU2,
        Matrix.one_mul]
    refine ⟨B, A, ?_⟩
    change U_emb * (E₀ * A + E₁ * B) = E₀ * B + E₁ * A
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hU0, ← Matrix.mul_assoc U_emb, hU1]; abel
  have hW_split : ∀ b : Fin (2 ^ systemQubits) → Bool,
      rBE.embedMatrix (physLaurentWalkGen b U_raw) =
        Complex.I • (rBE.embedMatrix (physGridReflGen systemQubits m b) * U_emb) := fun b ↦ by
    unfold physLaurentWalkGen; rw [rBE.embedMatrix_smul, rBE.embedMatrix_mul]
  have hWinv_split : ∀ b : Fin (2 ^ systemQubits) → Bool,
      rBE.embedMatrix (physLaurentWalkInvGen b U_raw) =
        (-Complex.I) • (U_emb * rBE.embedMatrix (physGridReflGen systemQubits m b)) := fun b ↦ by
    unfold physLaurentWalkInvGen; rw [rBE.embedMatrix_smul, rBE.embedMatrix_mul]
  exact biGqspGenSegmentOp_congr_of_invariant q_sig (biTwoAngleGate M C D) M
    (InLiftedKrylovSpanFerm spinUp U_raw) hAdd hSig
    (fun {Y} hY ↦ by
      rw [hW_split bValid, hW_split gridValidBool]
      obtain ⟨heq, hS⟩ := hRefl (hUemb hY)
      exact ⟨by rw [smul_mul_assoc, smul_mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, heq],
             by rw [smul_mul_assoc, Matrix.mul_assoc]; exact hSmul _ hS⟩)
    (fun {Y} hY ↦ by
      rw [hWinv_split bValid, hWinv_split gridValidBool]
      obtain ⟨heq, hS⟩ := hRefl hY
      exact ⟨by rw [smul_mul_assoc, smul_mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, heq],
             by rw [smul_mul_assoc, Matrix.mul_assoc]; exact hSmul _ (hUemb hS)⟩)
    hX
theorem inLiftedKrylovSpanFerm_fermAncZero (spinUp : Finset (Fin numElectrons)) {m : ℕ}
    (U_raw : Unitary (2 ^ (systemQubits + m))) :
    let sys : QRegister systemQubits (systemQubits + (m + 1)) :=
      QRegister.block 0 systemQubits (by omega)
    let anc : QRegister (m + 1) (systemQubits + (m + 1)) :=
      QRegister.block systemQubits (m + 1) le_rfl
    InLiftedKrylovSpanFerm spinUp U_raw
      (sys.embedMatrix (fermionicProjector spinUp) * anc.basisOutcomeProjector 0) := by
  intro sys anc
  let rBE : QRegister (systemQubits + m) (systemQubits + (m + 1)) :=
    QRegister.block 0 (systemQubits + m) (by omega)
  let q_sig : Wire (systemQubits + (m + 1)) := ⟨systemQubits + m, by omega⟩
  let rSysBE : QRegister systemQubits (systemQubits + m) :=
    QRegister.block 0 systemQubits (by omega)
  let rAncBE : QRegister m (systemQubits + m) := QRegister.block systemQubits m le_rfl
  have hDisjAnc : (rBE.compose rAncBE).DisjointWires (QRegister.singleton q_sig) := by
    rw [QRegister.disjoint_iff]; intro i j h; fin_cases j
    have hv := congrArg Fin.val h; simp [rBE, rAncBE, q_sig] at hv; omega
  have hConcatAnc : (rBE.compose rAncBE).concat (QRegister.singleton q_sig) hDisjAnc = anc := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]; ext; simp [rBE, rAncBE, anc]
    · fin_cases j; rw [QRegister.concat_apply_right]; ext
      simp [q_sig, anc]
  have hAncSplit : anc.basisOutcomeProjector 0 =
      rBE.embedMatrix (rAncBE.basisOutcomeProjector 0) *
        (QRegister.singleton q_sig).basisOutcomeProjector 0 := by
    rw [← hConcatAnc, basisOutcomeProjector_concat_zero]
    congr 1
    rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
      QRegister.embedMatrix_compose]
  have hSysComp : rBE.compose rSysBE = sys := by
    apply qreg_ext; intro i; ext; simp [rBE, rSysBE, sys]
  refine ⟨(QRegister.singleton q_sig).basisOutcomeProjector 0, 0, ?_⟩
  rw [Matrix.mul_zero, add_zero, hAncSplit, ← hSysComp, QRegister.embedMatrix_compose,
    ← Matrix.mul_assoc, ← rBE.embedMatrix_mul]
  rfl
/-- Exact 1-angle physical segment equality on `fermionicProjector spinUp ⊗ |0⟩_{m+1}` (`0.0`
  extra error). -/
theorem physBiSegmentUnitaryGen_mul_fermAncZero_eq
    {spinUp : Finset (Fin numElectrons)} {m : ℕ} {bValid : Fin (2 ^ systemQubits) → Bool}
    (hbValid : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x)
    (M : ℕ) (D : Fin (M + 1) → Fin (2 ^ 42))
    (U_raw : Unitary (2 ^ (systemQubits + m)))
    (hU2 : U_raw.1 * U_raw.1 = 1)
    (hKrylovFerm : RawBEMapsFermToKrylov3 spinUp U_raw)
    (hBlockComm : RawBEBlockCommutesFerm spinUp U_raw) :
    let sys : QRegister systemQubits (systemQubits + (m + 1)) :=
      QRegister.block 0 systemQubits (by omega)
    let anc : QRegister (m + 1) (systemQubits + (m + 1)) :=
      QRegister.block systemQubits (m + 1) le_rfl
    (physBiSegmentUnitaryGen bValid M D U_raw).1 *
        (sys.embedMatrix (fermionicProjector spinUp) * anc.basisOutcomeProjector 0) =
      (physBiSegmentUnitaryGen gridValidBool M D U_raw).1 *
        (sys.embedMatrix (fermionicProjector spinUp) * anc.basisOutcomeProjector 0) := by
  intro sys anc
  let q_sig : Wire (systemQubits + (m + 1)) := ⟨systemQubits + m, by omega⟩
  have hSigSpan (g : PrimitiveGate 1) {Y} (hY : InLiftedKrylovSpanFerm spinUp U_raw Y) :
      InLiftedKrylovSpanFerm spinUp U_raw ((Circuit.single g q_sig).eval.1 * Y) := by
    rw [Circuit.eval_single, QRegister.embedUnitary_val]
    exact inLiftedKrylovSpanFerm_sig_mul spinUp U_raw g.eval.1 hY
  have hPreSpan : InLiftedKrylovSpanFerm spinUp U_raw ((cPreOneAngle q_sig).eval.1 *
      (sys.embedMatrix (fermionicProjector spinUp) * anc.basisOutcomeProjector 0)) := by
    unfold cPreOneAngle Circuit.H Circuit.S Circuit.Z
    simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]
    exact hSigSpan .H (hSigSpan .Z (hSigSpan .S (hSigSpan .H
      (inLiftedKrylovSpanFerm_fermAncZero spinUp U_raw))))
  have hTwo := (physBiTwoAngleSegmentUnitaryGen_mul_inLiftedKrylovSpanFerm_eq
    hbValid M (fun _ ↦ 0) D U_raw hU2 hKrylovFerm hBlockComm hPreSpan).1
  rw [← cPost_mul_physBiTwoAngleSegment_zero_mul_cPre bValid M D U_raw,
    ← cPost_mul_physBiTwoAngleSegment_zero_mul_cPre gridValidBool M D U_raw]
  simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hTwo]
theorem block0_embedMatrix_mul_blockHigh_zero_inj {k m : ℕ} {A B : Operator (2 ^ k)} (h :
    (QRegister.block 0 k (by omega)).embedMatrix A * (QRegister.block k m
    le_rfl).basisOutcomeProjector 0 = (QRegister.block 0 k (by omega)).embedMatrix B *
    (QRegister.block k m le_rfl).basisOutcomeProjector 0) : A = B := by
  apply embedMatrix_sandwich_zero_inj (m := m) A B
  dsimp only
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]
theorem pgBE_mul_raw_mul_pgBE_eq_of_isQubitizedBE_ghostZeroedBE
    {m : ℕ} (hm : 0 < m) {α : ℝ} {A : Operator (2 ^ systemQubits)}
    {U_raw : Unitary (2 ^ (systemQubits + m))}
    (hBE : IsQubitizedBlockEncodingUnitary α A
      (ghostZeroedBE systemQubits m hm gridValidBool U_raw)) :
    let rSysBE : QRegister systemQubits (systemQubits + m) :=
      QRegister.block 0 systemQubits (by omega)
    pgBE m * U_raw.1 * pgBE m = (α : ℂ)⁻¹ • (pgBE m * rSysBE.embedMatrix A * pgBE m) := by
  intro rSysBE
  let rAncBE : QRegister m (systemQubits + m) := QRegister.block systemQubits m le_rfl
  let P_ag := ancGhostZeroProj systemQubits m
  let D_sys := (sysReg systemQubits m).embedMatrix (diagProj systemQubits gridValidBool)
  let F_in := P_ag * D_sys
  let E_pg := (baseReg systemQubits m).embedMatrix (pgBE m)
  let Z_gh := ghostZeroProj systemQubits m
  have hFin_comm : P_ag * D_sys = D_sys * P_ag :=
      (embedMatrix_comm_basisOutcomeProjector_disjoint (sysReg systemQubits m) (ancGhostReg
      systemQubits m) (QRegister.block_disjoint_of_le 0 systemQubits systemQubits (m + 1)
      (by omega) le_rfl (by omega)) (diagProj systemQubits gridValidBool) 0).symm
  have hDisjAnc : ((baseReg systemQubits m).compose rAncBE).DisjointWires (ghostReg systemQubits m)
    := by
    rw [QRegister.disjoint_iff]; intro i j h; fin_cases j
    have hv := congrArg Fin.val h
    simp [baseReg, rAncBE, ghostReg, ghostWire] at hv; omega
  have hConcatAnc : ((baseReg systemQubits m).compose rAncBE).concat (ghostReg systemQubits m)
    hDisjAnc =
      ancGhostReg systemQubits m := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]; ext; simp [baseReg, rAncBE, ancGhostReg]
    · fin_cases j; rw [QRegister.concat_apply_right]; ext
      simp [ghostReg, ghostWire, ancGhostReg]
  have hAncSplit : P_ag = (baseReg systemQubits m).embedMatrix (rAncBE.basisOutcomeProjector 0) *
    Z_gh := by
    dsimp only [P_ag, Z_gh]; unfold ancGhostZeroProj ghostZeroProj
    rw [← hConcatAnc, basisOutcomeProjector_concat_zero]; congr 1
    rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
      QRegister.embedMatrix_compose]
  have hSysComp : (baseReg systemQubits m).compose rSysBE = sysReg systemQubits m := by
    apply qreg_ext; intro i; ext; simp [baseReg, rSysBE, sysReg]
  have hFin_eq : F_in = E_pg * Z_gh := by
    dsimp only [F_in]
    rw [hFin_comm]; dsimp only [D_sys, E_pg]
    rw [hAncSplit, ← hSysComp, QRegister.embedMatrix_compose,
      ← Matrix.mul_assoc, ← (baseReg systemQubits m).embedMatrix_mul]
    rfl
  have hFin_herm : F_inᴴ = F_in := by
    have hAgH : P_agᴴ = P_ag := QRegister.basisOutcomeProjector_conjTranspose _ _
    dsimp only [F_in, D_sys]
    rw [Matrix.conjTranspose_mul, ← (sysReg systemQubits m).embedMatrix_conjTranspose,
      (diagProj_isHermitian systemQubits gridValidBool).eq, hAgH, ← hFin_comm]
  have hG_L : ghostGuardMatrix systemQubits m gridValidBool * F_in = F_in :=
    ghostGuard_mul_inGrid_eq systemQubits m gridValidBool
  have hG_R : F_in * ghostGuardMatrix systemQubits m gridValidBool = F_in := by
    have h := congrArg Matrix.conjTranspose hG_L
    rwa [Matrix.conjTranspose_mul, ghostGuardMatrix_conjTranspose, hFin_herm] at h
  let M_mux := ghostMuxOp systemQubits m U_raw.1 (ancFlipMatrix systemQubits m hm)
  have hZZ : Z_gh * Z_gh = Z_gh :=
    SingleRBEGridGuardWalk.basisOutcomeProjector_idem (ghostReg systemQubits m) 0
  have hCommP : Z_gh * E_pg = E_pg * Z_gh :=
    (baseReg_embedMatrix_comm_ghostZeroProj systemQubits m (pgBE m)).symm
  have hCommU : Z_gh * (baseReg systemQubits m).embedMatrix U_raw.1 =
      (baseReg systemQubits m).embedMatrix U_raw.1 * Z_gh :=
    (baseReg_embedMatrix_comm_ghostZeroProj systemQubits m U_raw.1).symm
  have hLHS : F_in * (ghostZeroedBE systemQubits m hm gridValidBool U_raw).1 * F_in =
      (baseReg systemQubits m).embedMatrix (pgBE m * U_raw.1 * pgBE m) * Z_gh := by
    calc F_in * (ghostZeroedBE systemQubits m hm gridValidBool U_raw).1 * F_in
      _ = (F_in * ghostGuardMatrix systemQubits m gridValidBool) * M_mux *
            (ghostGuardMatrix systemQubits m gridValidBool * F_in) := by
            change F_in * (ghostGuardMatrix _ _ _ * M_mux * ghostGuardMatrix _ _ _) * F_in = _
            simp only [Matrix.mul_assoc]
      _ = E_pg * (Z_gh * (M_mux * Z_gh)) * E_pg := by
            rw [hG_R, hG_L, hFin_eq]
            nth_rw 2 [← hCommP]
            simp only [Matrix.mul_assoc]
      _ = E_pg * (baseReg systemQubits m).embedMatrix U_raw.1 * (Z_gh * Z_gh) * E_pg := by
            rw [ghostMuxOp_mul_ghostZeroProj, show ghostZeroProj systemQubits m = Z_gh from rfl,
              ← Matrix.mul_assoc Z_gh, hCommU]
            simp only [Matrix.mul_assoc]
      _ = (E_pg * (baseReg systemQubits m).embedMatrix U_raw.1 * E_pg) * Z_gh := by
            rw [hZZ, Matrix.mul_assoc _ Z_gh E_pg, hCommP]
            simp only [Matrix.mul_assoc]
      _ = (baseReg systemQubits m).embedMatrix (pgBE m * U_raw.1 * pgBE m) * Z_gh := by
            dsimp only [E_pg]
            rw [← (baseReg systemQubits m).embedMatrix_mul,
              ← (baseReg systemQubits m).embedMatrix_mul]
  have hBE_top : P_ag * (ghostZeroedBE systemQubits m hm gridValidBool U_raw).1 * P_ag =
      (α : ℂ)⁻¹ • (P_ag * (sysReg systemQubits m).embedMatrix A * P_ag) := hBE.2.2
  have hCommA : Z_gh * (baseReg systemQubits m).embedMatrix (rSysBE.embedMatrix A) =
      (baseReg systemQubits m).embedMatrix (rSysBE.embedMatrix A) * Z_gh :=
    (baseReg_embedMatrix_comm_ghostZeroProj systemQubits m (rSysBE.embedMatrix A)).symm
  have hRHS : F_in * (ghostZeroedBE systemQubits m hm gridValidBool U_raw).1 * F_in =
      (baseReg systemQubits m).embedMatrix ((α : ℂ)⁻¹ • (pgBE m * rSysBE.embedMatrix A * pgBE m)) *
        Z_gh := by
    calc F_in * (ghostZeroedBE systemQubits m hm gridValidBool U_raw).1 * F_in
      _ = D_sys * (P_ag * (ghostZeroedBE systemQubits m hm gridValidBool U_raw).1 * P_ag) * D_sys :=
        by
            dsimp only [F_in]; nth_rw 1 [hFin_comm]; simp only [Matrix.mul_assoc]
      _ = (α : ℂ)⁻¹ • ((D_sys * P_ag) * (sysReg systemQubits m).embedMatrix A * F_in) := by
            dsimp only [F_in]
            rw [hBE_top, mul_smul_comm, smul_mul_assoc]; simp only [Matrix.mul_assoc]
      _ =
        (α : ℂ)⁻¹ • ((E_pg * (Z_gh * (baseReg systemQubits m).embedMatrix (rSysBE.embedMatrix A)) *
        E_pg) * Z_gh) := by
            rw [← hFin_comm]; change (α : ℂ)⁻¹ • (F_in * _ * F_in) = _
            rw [hFin_eq, ← hSysComp, QRegister.embedMatrix_compose]; simp only [Matrix.mul_assoc]
      _ =
        (α : ℂ)⁻¹ • ((E_pg * (baseReg systemQubits m).embedMatrix (rSysBE.embedMatrix A) * E_pg) *
        Z_gh) := by
            rw [hCommA, ← Matrix.mul_assoc E_pg _ Z_gh, Matrix.mul_assoc _ Z_gh E_pg, hCommP,
              ← Matrix.mul_assoc _ E_pg Z_gh, Matrix.mul_assoc _ Z_gh Z_gh, hZZ]
      _ =
        (baseReg systemQubits m).embedMatrix ((α : ℂ)⁻¹ • (pgBE m * rSysBE.embedMatrix A *
        pgBE m)) * Z_gh := by
            dsimp only [E_pg]
            rw [← (baseReg systemQubits m).embedMatrix_mul,
              ← (baseReg systemQubits m).embedMatrix_mul,
              ← smul_mul_assoc, ← (baseReg systemQubits m).embedMatrix_smul]
  have hGhostEq : ghostReg systemQubits m = QRegister.block (systemQubits + m) 1 le_rfl := by
    apply qreg_ext; intro idx; fin_cases idx; ext
    simp [ghostReg, ghostWire]
  have hBaseEq : baseReg systemQubits m = QRegister.block 0 (systemQubits + m) (by omega) := by
    apply qreg_ext; intro idx; ext; simp [baseReg]
  have hEqZ : (QRegister.block 0 (systemQubits + m) (by omega)).embedMatrix (pgBE m * U_raw.1 *
    pgBE m) *
        (QRegister.block (systemQubits + m) 1 le_rfl).basisOutcomeProjector 0 =
      (QRegister.block 0 (systemQubits + m) (by omega)).embedMatrix
        ((α : ℂ)⁻¹ • (pgBE m * rSysBE.embedMatrix A * pgBE m)) *
        (QRegister.block (systemQubits + m) 1 le_rfl).basisOutcomeProjector 0 := by
    simpa only [Z_gh, ghostZeroProj, hGhostEq, hBaseEq] using hLHS.symm.trans hRHS
  exact block0_embedMatrix_mul_blockHigh_zero_inj hEqZ
theorem op_eq_of_inv_smul_eq {d : ℕ} {c : ℂ} (hc : c ≠ 0) {X Y : Operator d}
    (h : c⁻¹ • X = c⁻¹ • Y) : X = Y := by
  simpa [smul_smul, mul_inv_cancel₀ hc] using congrArg (c • ·) h
theorem op_norm_sandwich_le {d : ℕ} (P M : Operator d) {δ : ℝ}
    (hP : ‖P‖ ≤ 1) (hM : ‖M‖ ≤ δ) : ‖P * M * P‖ ≤ δ :=
  (norm_mul_le (P * M) P).trans
    ((mul_le_mul_of_nonneg_right (norm_mul_le P M) (norm_nonneg P)).trans
    ((mul_le_mul (mul_le_mul hP hM (norm_nonneg M) zero_le_one) hP (norm_nonneg P)
      (by linarith [norm_nonneg M])).trans_eq (by ring)))
theorem commute_ferm_of_isQubitizedBE_ghostZeroedBE_and_blockComm
    {spinUp : Finset (Fin numElectrons)} {m : ℕ} (hm : 0 < m) {α : ℝ}
    {A : Operator (2 ^ systemQubits)} {U_raw : Unitary (2 ^ (systemQubits + m))}
    (hAGrid : Commute A SpecsAux.gridProjector) (hBE :
    IsQubitizedBlockEncodingUnitary α A (ghostZeroedBE systemQubits m hm gridValidBool U_raw))
    (hBlockComm : RawBEBlockCommutesFerm spinUp U_raw) : Commute A (fermionicProjector spinUp)
    := by
  let rSysBE : QRegister systemQubits (systemQubits + m) :=
    QRegister.block 0 systemQubits (by omega)
  let rAncBE : QRegister m (systemQubits + m) := QRegister.block systemQubits m le_rfl
  let G := SpecsAux.gridProjector
  let F := fermionicProjector spinUp
  have hDisj : rSysBE.DisjointWires rAncBE :=
    QRegister.block_disjoint_of_le 0 systemQubits systemQubits m (by omega) le_rfl (by omega)
  have hPg : pgBE m = rSysBE.embedMatrix G * rAncBE.basisOutcomeProjector 0 := by
    unfold pgBE projGridAncZero; rw [diagProj_gridValidBool_eq_specsGridProjector]
  have hGAG : pgBE m * rSysBE.embedMatrix A * pgBE m =
      rSysBE.embedMatrix (G * A) * rAncBE.basisOutcomeProjector 0 := by
    rw [hPg, Matrix.mul_assoc (rSysBE.embedMatrix G),
      ← embedMatrix_comm_basisOutcomeProjector_disjoint rSysBE rAncBE hDisj A 0]
    calc rSysBE.embedMatrix G * (rSysBE.embedMatrix A * rAncBE.basisOutcomeProjector 0) *
          (rSysBE.embedMatrix G * rAncBE.basisOutcomeProjector 0)
      _ = rSysBE.embedMatrix (G * A * G) *
            (rAncBE.basisOutcomeProjector 0 * rAncBE.basisOutcomeProjector 0) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc,
            ← Matrix.mul_assoc (rAncBE.basisOutcomeProjector 0),
            ← embedMatrix_comm_basisOutcomeProjector_disjoint rSysBE rAncBE hDisj G 0]
          simp only [← Matrix.mul_assoc, ← rSysBE.embedMatrix_mul]
      _ = rSysBE.embedMatrix (G * A) * rAncBE.basisOutcomeProjector 0 := by
          rw [SingleRBEGridGuardWalk.basisOutcomeProjector_idem rAncBE 0, Matrix.mul_assoc G A G,
            hAGrid.eq, ← Matrix.mul_assoc G G A,
            SpecsAux.gridProjector_mul_self]
  have hGAF : (G * A) * F = A * F := by
    rw [← hAGrid.eq, Matrix.mul_assoc, SpecsAux.gridProjector_mul_fermionicProjector]
  have hFGA : F * (G * A) = F * A := by
    rw [← Matrix.mul_assoc, fermionicProjector_mul_specsGridProjector]
  have hCommEq : (pgBE m * U_raw.1 * pgBE m) * rSysBE.embedMatrix F =
      rSysBE.embedMatrix F * (pgBE m * U_raw.1 * pgBE m) := hBlockComm.eq
  rw [pgBE_mul_raw_mul_pgBE_eq_of_isQubitizedBE_ghostZeroedBE hm hBE, hGAG] at hCommEq
  have hL : ((α : ℂ)⁻¹ • (rSysBE.embedMatrix (G * A) * rAncBE.basisOutcomeProjector 0)) *
      rSysBE.embedMatrix F =
      rSysBE.embedMatrix ((α : ℂ)⁻¹ • (A * F)) * rAncBE.basisOutcomeProjector 0 := by
    rw [smul_mul_assoc, Matrix.mul_assoc,
      ← embedMatrix_comm_basisOutcomeProjector_disjoint rSysBE rAncBE hDisj F 0,
      ← Matrix.mul_assoc, ← rSysBE.embedMatrix_mul, hGAF,
      ← smul_mul_assoc, ← rSysBE.embedMatrix_smul]
  have hR : rSysBE.embedMatrix F *
      ((α : ℂ)⁻¹ • (rSysBE.embedMatrix (G * A) * rAncBE.basisOutcomeProjector 0)) =
      rSysBE.embedMatrix ((α : ℂ)⁻¹ • (F * A)) * rAncBE.basisOutcomeProjector 0 := by
    rw [mul_smul_comm, ← Matrix.mul_assoc, ← rSysBE.embedMatrix_mul, hFGA,
      ← smul_mul_assoc, ← rSysBE.embedMatrix_smul]
  rw [hL, hR] at hCommEq
  have hSmulEq : (α : ℂ)⁻¹ • (A * F) = (α : ℂ)⁻¹ • (F * A) :=
    block0_embedMatrix_mul_blockHigh_zero_inj hCommEq
  have hαNe : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hBE.1.ne'
  exact op_eq_of_inv_smul_eq hαNe hSmulEq
theorem stepa_perturbation_via_fermProjector_gen {mAnc R_j N_seg : ℕ} (c : Configuration)
    (j : Fin 10) (spinUp : Finset (Fin numElectrons)) {catErr E₀ δ_prep ε_id ε_BE : ℝ}
    (hTotErr : ((R_j : ℝ) * ((N_seg : ℝ) / (2 : ℝ) ^ 48) + 2 * catErr) + (j.val + 1 : ℝ) *
    ε_BE ≤ 0.01) (hSumCap : δ_prep + ε_id ≤ ε_BE)
    {Heff_act Heff_id : Operator (2 ^ systemQubits)} (hActHerm : Heff_act.IsHermitian)
    (hActFerm : Commute Heff_act (fermionicProjector spinUp)) (hIdHerm : Heff_id.IsHermitian)
    (hDiffGrid : ‖SpecsAux.gridProjector * (Heff_act - Heff_id) *
    SpecsAux.gridProjector‖ ≤ δ_prep) (hAgreeId : AgreesOnFermionicSector
    spinUp Heff_id (smToTwosSysUnitary.1 * hamiltonian c * smToTwosSysUnitary.1ᴴ) ε_id)
    (W : Unitary (2 ^ (systemQubits + mAnc))) (hSandFerm : ApproximatesTimeEvolution (Heff_act
    - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits))) (j.val + 1 : ℝ) ((R_j : ℝ) * ((N_seg : ℝ)
    / (2 : ℝ) ^ 48) + 2 * catErr) (fermionicProjector spinUp) W) : ApproximatesTimeEvolution
    (smToTwosSysUnitary.1 * hamiltonian c * smToTwosSysUnitary.1ᴴ) (j.val + 1 : ℝ) 0.01
    (fermionicProjector spinUp) W := by
  let G := SpecsAux.gridProjector
  let P_ferm := fermionicProjector spinUp
  let H_twos := smToTwosSysUnitary.1 * hamiltonian c * smToTwosSysUnitary.1ᴴ
  let ε₀ : ℝ := (R_j : ℝ) * ((N_seg : ℝ) / (2 : ℝ) ^ 48) + 2 * catErr
  have hP_herm := SpecsAux.fermionicProjector_isHermitian spinUp
  have hP_idem := SpecsAux.BridgeFermionicComm.SpecInner.fermionicProjector_idem spinUp
  have hPnorm : ‖P_ferm‖ ≤ 1 :=
    SpecsAux.SpecMirror.SixChannelHamiltonianSplit.norm_projector_le_one
      P_ferm hP_herm hP_idem
  have hSubEq : P_ferm * (Heff_act - Heff_id) * P_ferm =
      P_ferm * (G * (Heff_act - Heff_id) * G) * P_ferm := by
    calc P_ferm * (Heff_act - Heff_id) * P_ferm
      _ = (P_ferm * G) * (Heff_act - Heff_id) * (G * P_ferm) := by
            rw [fermionicProjector_mul_specsGridProjector spinUp,
              SpecsAux.gridProjector_mul_fermionicProjector spinUp]
      _ = P_ferm * (G * (Heff_act - Heff_id) * G) * P_ferm := by simp only [Matrix.mul_assoc]
  have hDiffFerm : ‖P_ferm * (Heff_act - Heff_id) * P_ferm‖ ≤ δ_prep := by
    rw [hSubEq]
    exact op_norm_sandwich_le P_ferm (G * (Heff_act - Heff_id) * G) hPnorm hDiffGrid
  have hShift : ApproximatesTimeEvolution Heff_act (j.val + 1 : ℝ) ε₀ P_ferm W :=
    ApproximatesTimeEvolution.of_scalar_shift Heff_act E₀ (j.val + 1 : ℝ) ε₀ P_ferm W hSandFerm
  let ε₁ : ℝ := ε₀ + (j.val + 1 : ℝ) * δ_prep
  have hSub1 : ε₁ - (j.val + 1 : ℝ) * δ_prep = ε₀ := by dsimp only [ε₁]; ring
  have hOnIdFerm : ApproximatesTimeEvolution Heff_id (j.val + 1 : ℝ) ε₁ P_ferm W :=
      ApproximatesTimeEvolution.of_perturbation_direct Heff_act Heff_id P_ferm (j.val + 1 : ℝ)
      ε₁ δ_prep W (by positivity) hActHerm hIdHerm hP_herm hP_idem hActFerm.eq hAgreeId.1
      hDiffFerm (hSub1.symm ▸ hShift)
  rcases SingleCatClosure.op_conj_herm_and_comm
    smToTwosSysUnitary.1 (hamiltonian c) P_ferm
    smToTwosSysUnitary_conjTranspose (SpecsAux.hamiltonian_isHermitian c)
    (smToTwosSys_comm_fermionicProjector spinUp)
    (SpecsAux.BridgeFermionicComm.SpecInner.hamiltonian_comm_fermionicProjector c spinUp)
    with ⟨hHtwosHerm, hHtwosComm⟩
  let ε_tot : ℝ := ε₀ + (j.val + 1 : ℝ) * (δ_prep + ε_id)
  have hSub2 : ε_tot - (j.val + 1 : ℝ) * ε_id = ε₁ := by dsimp only [ε_tot, ε₁]; ring
  rcases ApproximatesTimeEvolution.of_perturbation_direct Heff_id H_twos P_ferm
    (j.val + 1 : ℝ) ε_tot ε_id W (by positivity)
    hIdHerm hHtwosHerm hP_herm hP_idem hAgreeId.1 hHtwosComm hAgreeId.2
    (hSub2.symm ▸ hOnIdFerm) with ⟨φ, hφ⟩
  have hMul : (j.val + 1 : ℝ) * (δ_prep + ε_id) ≤ (j.val + 1 : ℝ) * ε_BE :=
    mul_le_mul_of_nonneg_left hSumCap (by positivity)
  exact ⟨φ, le_trans hφ (by dsimp only [ε_tot, ε₀] at *; linarith)⟩
/-- Fermionic-Krylov `SingleCat` time-evolution step theorem (`0.0` extra error overhead). -/
theorem stepa_oneAngleUltraSingleCatFermGen_of_gridPerturbat
    {mPayload B_tot kWorkConst β_nat M N_seg R_j : ℕ}
    {bValid : Fin (2 ^ systemQubits) → Bool}
    (hbValid : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x)
    {qft : FullSysQft654Bundle}
    {prep : FullSysPrepareBundle mPayload}
    {sel : FullSysSelectOracleBundle mPayload 48}
    (hB42 : 42 ≤ B_tot)
    (selImpl : SingleCatSelectImpl mPayload B_tot qft sel)
    (cert : GeneralBetaSegmentCert β_nat M N_seg)
    (c : Configuration) (j : Fin 10)
    (hRPos : R_j ≠ 0)
    (spinUp : Finset (Fin numElectrons))
    (hKrylovFerm : RawBEMapsFermToKrylov3 spinUp (fullSysRawBEUnitary qft prep sel c))
    (hBlockComm : RawBEBlockCommutesFerm spinUp (fullSysRawBEUnitary qft prep sel c))
    (hTwist_s2 : (sel.uTwist c).1 * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * (sel.uTwist c).1)
    (hTwist_s1 : (sel.uTwist c).1 * slotBitProj (iSlot1 mPayload) 1 =
      slotBitProj (iSlot1 mPayload) 1 * (sel.uTwist c).1)
    (hTwist_s0 : (sel.uTwist c).1 * slotBitProj (iSlot0 mPayload) 0 =
      slotBitProj (iSlot0 mPayload) 0 * (sel.uTwist c).1)
    (hPos_slack :
      let P_slack := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
          slotBitProj (iSlot0 mPayload) 0
      (sel.uPosPhase c).1 * P_slack = P_slack)
    {ε_BE : ℝ}
    (hTotErr : ((R_j : ℝ) * ((N_seg : ℝ) / (2 : ℝ) ^ 48) + 2 * catPrepErrUltra1q) +
      (j.val + 1 : ℝ) * ε_BE ≤ 0.01)
    {α E₀ δ_prep ε_id : ℝ} (hα : 0 < α)
    (hβ : α * ((j.val + 1 : ℝ) / (R_j : ℝ)) = (β_nat : ℝ))
    (hSumCap : δ_prep + ε_id ≤ ε_BE)
    {Heff_act Heff_id : Operator (2 ^ systemQubits)}
    (hAGridAct : Commute (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
      SpecsAux.gridProjector)
    (hBEAct : IsQubitizedBlockEncodingUnitary α
      (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
      (ghostZeroedBE systemQubits (fullSysRawAncWires mPayload)
        (by dsimp [fullSysRawAncWires]; omega) gridValidBool
        (fullSysRawBEUnitary qft prep sel c)))
    (hIdHerm : Heff_id.IsHermitian)
    (hDiffGrid : ‖SpecsAux.gridProjector * (Heff_act - Heff_id) *
        SpecsAux.gridProjector‖ ≤ δ_prep)
    (hAgreeId : AgreesOnFermionicSector spinUp Heff_id
      (smToTwosSysUnitary.1 * hamiltonian c * smToTwosSysUnitary.1ᴴ) ε_id) :
    ApproximatesTimeEvolution
      (smToTwosSysUnitary.1 * hamiltonian c * smToTwosSysUnitary.1ᴴ)
      (j.val + 1 : ℝ) 0.01 (fermionicProjector spinUp)
      (unitarySandwichPow
        (vInvUltraSingleCat mPayload B_tot kWorkConst)
        (uSegOneAngleSingleCatGen (kWorkConst := kWorkConst) bValid hB42 prep selImpl M cert.C c)
        (vPrepUltraSingleCat mPayload B_tot kWorkConst) R_j) := by
  have hmPos : 0 < fullSysRawAncWires mPayload := by dsimp [fullSysRawAncWires]; omega
  have hActHerm : Heff_act.IsHermitian :=
    isHermitian_of_isQubitizedBlockEncodingUnitary hBEAct
  have hE : ((E₀ : ℂ) • (1 : Operator (2 ^ systemQubits))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      RCLike.star_def, Complex.conj_ofReal]
  have hActShiftHerm : (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits))).IsHermitian :=
    hActHerm.sub hE
  have hAFermShift : Commute (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
      (fermionicProjector spinUp) :=
    commute_ferm_of_isQubitizedBE_ghostZeroedBE_and_blockComm hmPos hAGridAct hBEAct hBlockComm
  have hActCommFerm : Commute Heff_act (fermionicProjector spinUp) := by
    rw [(sub_add_cancel Heff_act ((E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))).symm]
    exact hAFermShift.add_left (Commute.smul_left (Commute.one_left _) _)
  have hP_herm := SpecsAux.fermionicProjector_isHermitian spinUp
  have hP_idem := SpecsAux.BridgeFermionicComm.SpecInner.fermionicProjector_idem spinUp
  have hStep0Grid := physBiSegmentUnitaryGen_approx_exp_beta hmPos gridValidBool
      SpecsAux.gridProjector (fermionicProjector spinUp)
      diagProj_gridValidBool_eq_specsGridProjector
      (SpecsAux.gridProjector_mul_fermionicProjector spinUp) hP_herm
      hP_idem cert hα (div_nonneg (by positivity) (by positivity)) hβ hAGridAct
      (fullSysRawBEUnitary qft prep sel c) hBEAct
  have hStep0 := approximatesTimeEvolution_congr_mul_gridAncZero
      (physBiSegmentUnitaryGen_mul_fermAncZero_eq hbValid M cert.C (fullSysRawBEUnitary qft
      prep sel c) (fullSysRawBEUnitary_val_mul_self qft prep sel c) hKrylovFerm hBlockComm)
      hStep0Grid
  let sub : QRegister (fullSysRawAncWires mPayload + 1)
      (mActSingleCatClosure mPayload B_tot kWorkConst) :=
    QRegister.block 0 (fullSysRawAncWires mPayload + 1)
      (by dsimp [mActSingleCatClosure, mSegAncPoly, fullSysRawAncWires,
        mCatScratchSingleCat]; omega)
  have hStepAct := approximatesTimeEvolution_embed_block0
    (rPhysSegInSingleCat mPayload B_tot kWorkConst) sub
    (by apply qreg_ext; intro i; ext; simp [rPhysSegInSingleCat])
    (by apply qreg_ext; intro i; ext; simp [sub, rPhysSegInSingleCat])
    hStep0
  have hPowFerm := approximatesTimeEvolution_pow_of_div
    hActShiftHerm hAFermShift hRPos hStepAct (le_refl _)
  have hInter := uSegOneAngleSingleCatGen_intertwinesCat (kWorkConst := kWorkConst)
    bValid hB42 prep selImpl M cert.C c hTwist_s2 hTwist_s1 hTwist_s0 hPos_slack
  exact stepa_perturbation_via_fermProjector_gen
    (mAnc := mActSingleCatClosure mPayload B_tot kWorkConst)
    c j spinUp hTotErr hSumCap hActHerm hActCommFerm hIdHerm hDiffGrid hAgreeId
    (unitarySandwichPow
      (vInvUltraSingleCat mPayload B_tot kWorkConst)
      (uSegOneAngleSingleCatGen (kWorkConst := kWorkConst) bValid hB42 prep selImpl M cert.C c)
      (vPrepUltraSingleCat mPayload B_tot kWorkConst) R_j)
    (catalyst_sandwich_ultra_singleCat
      (Heff_act - (E₀ : ℂ) • (1 : Operator (2 ^ systemQubits)))
      (fermionicProjector spinUp)
      (j.val + 1 : ℝ) ((R_j : ℝ) * ((N_seg : ℝ) / (2 : ℝ) ^ 48)) R_j
      (uSegOneAngleSingleCatGen (kWorkConst := kWorkConst) bValid hB42 prep selImpl M cert.C c)
      ((rPhysSegInSingleCat mPayload B_tot kWorkConst).embedUnitary
        (physBiSegmentUnitaryGen bValid M cert.C (fullSysRawBEUnitary qft prep sel c)))
      hActShiftHerm hP_herm hP_idem hInter.1 hInter.2.2 hPowFerm)
/-- Symbolic-dimension core for `CustomOneAngleSegExtHkGenSpec`. -/
structure CustomOneAngleSegExtHkSpecCoreGen (kAct mWork : ℕ)
    (pHoist : ∀ {n : ℕ}, QRegister kAct n → QRegister mWork n → Operator (2 ^ n))
    (uSeg : Configuration → Fin 10 → Unitary (2 ^ kAct))
    (tSeg : Fin 10 → ℕ) where
  dSeg : ∀ (_ : Configuration) (_ : Fin 10) {Var : Type} {n : ℕ}, Var →
    ∀ (rAct : QRegister kAct n) (rWork : QRegister mWork n),
      rAct.DisjointWires rWork → DynamicCircuit Var n
  hToff : ∀ (c : Configuration) (j : Fin 10) {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dSeg c j v rAct rWork hD).count TOFF = 0
  hT : ∀ (c : Configuration) (j : Fin 10) {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dSeg c j v rAct rWork hD).count T ≤ tSeg j
  hReal : ∀ (c : Configuration) (j : Fin 10) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    RealizesOnProj (pHoist rAct rWork) (rAct.embedUnitary (uSeg c j)) (dSeg c j v rAct rWork hD)
/-- Custom per-horizon 1-angle Bi-GQSP `ExtHk` segment circuit specification for general
  `bValid`. -/
abbrev CustomOneAngleSegExtHkGenSpec (bValid : Fin (2 ^ systemQubits) → Bool)
    {mWork k_idle β_nat M : ℕ} {hk : k_idle ≤ 48} {α : ℝ}
    {tPrep tSelCtrl tSelCat : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ} (sp : GenBetaExtHkSelAndPertSpec
    mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle) (tSeg : Fin 10 → ℕ) : Type 1 :=
    CustomOneAngleSegExtHkSpecCoreGen kFull80 mWork (fun rA rW ↦ pHoistExtOn k_idle hk rA rW)
    (fun c j ↦ uSegOneAngleExtHkGen bValid (sp.prep j) (sp.sel j) M (tbl.cert j).C c)
    tSeg
/-- Packages any `OneAngleUnheldExtHkGuardSpecBundleGen` into `CustomOneAngleSegExtHkGenSpec`
with `wSegSingleCatExt48_TwoRot_T` (`2 * rotToffSum`). -/
noncomputable def mkCustomOneAngleSegGenOfUnheldGuard
    {bValid : Fin (2 ^ systemQubits) → Bool}
    {mWork k_idle tGuard β_nat M : ℕ} {hk : k_idle ≤ 48}
    {α : ℝ} {tPrep tSelCtrl tSelCat : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ}
    (hm1 : 1 ≤ mWork)
    (guard : OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (sp : GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle) :
    CustomOneAngleSegExtHkGenSpec bValid sp tbl
      (fun j ↦ wSegSingleCatExt48_TwoRot_T (tPrep j) (tSelCtrl j) (tSelCat j) tGuard
        (tbl.rotToffSum j) M) where
  dSeg c j {_ _} v rAct rWork hD :=
    mkSegOneAngleUnheldExtHkGenDyn hm1 guard (sp.prep j) (sp.sel j) (sp.hmPrep j)
      M (tbl.cert j).C c v rAct rWork hD
  hToff c j {_ _} v rAct rWork hD :=
    (mkSegOneAngleUnheldExtHkGenDyn_counts hm1 guard (sp.prep j) (sp.sel j) (sp.hmPrep j)
      M (tbl.rotToffSum j) (tbl.cert j).C (tbl.hRot j) c v rAct rWork hD).1
  hT c j {_ _} v rAct rWork hD :=
    (mkSegOneAngleUnheldExtHkGenDyn_counts hm1 guard (sp.prep j) (sp.sel j) (sp.hmPrep j)
      M (tbl.rotToffSum j) (tbl.cert j).C (tbl.hRot j) c v rAct rWork hD).2.trans
      (by
        dsimp only [wSegSingleCatExt48_TwoRot_T]
        have hp := sp.hTPrep j
        exact Nat.add_le_add_right
          (Nat.add_le_add_right
            (Nat.add_le_add_right
              (Nat.add_le_add
                (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) _))
                (Nat.mul_le_mul_left M (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) _)))
              _)
            _)
          48)
  hReal c j {_ _ _ _ _} v rAct rWork hD :=
    mkSegOneAngleUnheldExtHkGenDyn_realizesOnProj hm1 guard (sp.prep j) (sp.sel j)
      (sp.hmPrep j) M (tbl.cert j).C c (tbl.hDiv j) (sp.hPrepLow j c) (sp.hPrepCtrl3 j c)
      v rAct rWork hD
/-- Master `{mAnc}`-polymorphic program accepting any `CustomOneAngleSegExtHkGenSpec`. -/
noncomputable def slot3InnerCustomSegMasterProgramGen_mAnc {Var : Type}
    {bValid : Fin (2 ^ systemQubits) → Bool} {mAnc mWork k_idle tStreamPair β_nat M n : ℕ}
    {hk : k_idle ≤ 48} {α : ℝ} {tPrep tSelCtrl tSelCat tSeg : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ}
    (hm28 : 28 ≤ mWork) (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (sp
    : GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle)
    (segSpec : CustomOneAngleSegExtHkGenSpec bValid sp tbl tSeg) (schedule : Fin 10 → ℕ)
    (c : Configuration) (j : Fin 10) (v : Var) (rSys : QRegister systemQubits n)
    (rAnc : QRegister mAnc n) (hmAnc : mAnc = hoAncillasM mWork) : DynamicCircuit Var n :=
  let rAnc' : QRegister (hoAncillasM mWork) n := hmAnc ▸ rAnc
  cleanBasisScheduleProgram schedule
    (smToTwosSysOnActDyn (Nat.le_trans (by decide : 7 ≤ 28) hm28) v)
    (mkInitUltraExtHkDyn hk hm28 initSpec v)
    (fun c' j' rA rW hD ↦ segSpec.dSeg c' j' v rA rW hD)
    (mkUninitUltraExtHkDyn hk hm28 initSpec v)
    (smToTwosSysOnActDyn (Nat.le_trans (by decide : 7 ≤ 28) hm28) v)
    c j rSys rAnc'
/-- Parametric spacetime volume evaluator for `slot3InnerCustomSegMasterProgramGen_mAnc`. -/
def slot3InnerGenSpacetime_CustomSegGen (mWork : ℕ) (schedule : Fin 10 → ℕ) (tStreamPair : ℕ)
    (tSegCap : Fin 10 → ℕ) : ℕ := (systemQubits + hoAncillasM mWork) * (50 * (10 * (21072 +
    (cInitUltraSingleCat_T + tStreamPair)) + ∑ j : Fin 10, schedule j * tSegCap j))
theorem slot3InnerCustomSegMasterGen_const_cost_mAnc {Var : Type}
    {bValid : Fin (2 ^ systemQubits) → Bool}
    {mAnc mWork k_idle tStreamPair β_nat M n costCap : ℕ} {hk : k_idle ≤ 48} {α : ℝ}
    {tPrep tSelCtrl tSelCat tSeg tSegCap : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ} (hm28 : 28 ≤ mWork)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (sp :
    GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle)
    (segSpec : CustomOneAngleSegExtHkGenSpec bValid sp tbl tSeg) (schedule : Fin 10 → ℕ)
    (htSeg : ∀ j, tSeg j ≤ tSegCap j) (hCap : slot3InnerGenSpacetime_CustomSegGen mWork schedule
    tStreamPair tSegCap ≤ costCap) (c : Configuration) (v : Var)
    (rSys : QRegister systemQubits n) (rAnc : QRegister mAnc n)
    (hmAnc : mAnc = hoAncillasM mWork) : (∀ j, (slot3InnerCustomSegMasterProgramGen_mAnc hm28
    initSpec sp tbl segSpec schedule c j v rSys rAnc hmAnc).count TOFF = 0) ∧
    (systemQubits + mAnc) * (50 * ∑ j, (slot3InnerCustomSegMasterProgramGen_mAnc hm28 initSpec sp
    tbl segSpec schedule c j v rSys rAnc hmAnc).count T) ≤ costCap := by
  subst hmAnc
  exact cleanBasisSchedule_perHorizon_const_cost schedule tSegCap
    (fun rA rW hD ↦
      count_toff_smToTwosSysOnActDyn (Nat.le_trans (by decide : 7 ≤ 28) hm28) v rA rW hD)
    (fun rA rW hD ↦ count_toff_mkInitUltraExtHkDyn hk hm28 initSpec v rA rW hD)
    (fun c' j' rA rW hD ↦ segSpec.hToff c' j' v rA rW hD)
    (fun rA rW hD ↦ count_toff_mkUninitUltraExtHkDyn hk hm28 initSpec v rA rW hD)
    (fun rA rW hD ↦
      count_toff_smToTwosSysOnActDyn (Nat.le_trans (by decide : 7 ≤ 28) hm28) v rA rW hD)
    (fun rA rW hD ↦ by simp [count_t_smToTwosSysOnActDyn])
    (fun rA rW hD ↦ count_t_mkInitUltraExtHk_add_uninit_le hk hm28 initSpec v rA rW hD)
    (fun c' j' rA rW hD ↦ (segSpec.hT c' j' v rA rW hD).trans (htSeg j'))
    hCap c rSys rAnc
set_option exponentiation.threshold 5000 in
/-- Master correctness theorem under Fermionic-Krylov invariance (`RawBEMapsFermToKrylov3` +
`RawBEBlockCommutesFerm`) and `badElecCount ≤ 3` agreement (`0.0` extra error overhead). -/
theorem slot3InnerCustomSegMasterFermGen_correctness_mAnc {Var : Type} [Finite Var]
    [DecidableEq Var] {bValid : Fin (2 ^ systemQubits) → Bool}
    (hbValid : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x)
    {mAnc mWork k_idle tStreamPair β_nat M n : ℕ} {hk : k_idle ≤ 48} [NeZero (2 ^ n)] {α : ℝ}
    {tPrep tSelCtrl tSelCat tSeg : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ} (hk17 : k_idle ≤ 17)
    (hm28 : 28 ≤ mWork) (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (sp
    : GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle)
    (segSpec : CustomOneAngleSegExtHkGenSpec bValid sp tbl tSeg) (schedule : Fin 10 → ℕ)
    (hSchedNeZero : ∀ j, schedule j ≠ 0) (hβ : ∀ j : Fin 10, α * ((j.val + 1 : ℝ) / (schedule
    j : ℝ)) = (β_nat : ℝ)) (hTotErr : ∀ j : Fin 10, ((schedule j : ℝ) * ((tbl.nSeg j : ℝ) / (2
    : ℝ) ^ 48) + 2 * catPrepErrUltra1q) + (j.val + 1 : ℝ) * ε_BE j ≤ 0.01) (hKrylovFerm : ∀ (j
    : Fin 10) (c : Configuration) (spinUp : Finset (Fin numElectrons)), RawBEMapsFermToKrylov3
    spinUp (fullSysRawBEUnitary sp.qft (sp.prep j) (sp.selOra j) c)) (hBlockComm : ∀ (j : Fin
    10) (c : Configuration) (spinUp : Finset (Fin numElectrons)), RawBEBlockCommutesFerm
    spinUp (fullSysRawBEUnitary sp.qft (sp.prep j) (sp.selOra j) c)) (c : Configuration)
    (j : Fin 10) (v : Var) (rSys : QRegister systemQubits n) (rAnc : QRegister mAnc n)
    (hmAnc : mAnc = hoAncillasM mWork) (hdisj : rSys.DisjointWires rAnc) : ∃ W, (∀ spinUp,
    ApproximatesTimeEvolution (hamiltonian c) (j.val + 1 : ℝ) 0.01 (fermionicProjector spinUp)
    W) ∧ RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys gridStates rAnc hdisj W
    (slot3InnerCustomSegMasterProgramGen_mAnc hm28 initSpec sp tbl segSpec schedule c j v rSys rAnc
    hmAnc).compile := by
  cases nonempty_fintype Var
  subst hmAnc
  let hm7 : 7 ≤ mWork := Nat.le_trans (by decide : 7 ≤ 28) hm28
  let sysAct : QRegister systemQubits kFull80 :=
    QRegister.block 0 systemQubits (fullSys_zero_add_le systemQubits mActHoist)
  let U_full : Unitary (2 ^ kFull80) := sysAct.embedUnitary smToTwosSysUnitary
  let U_pre : Unitary (2 ^ kFull80) :=
    uHadIdleFull k_idle hk * rAct0.embedUnitary (vPrepUltraSingleCat 80 48 40)
  have hSysDisjExt : sysAct.DisjointWires (rExt48IdleFull k_idle hk) :=
    disj_of_val_ne fun a b ↦ by
      have ha : (sysAct a).val = a.val := by simp [sysAct]
      have hge := rExt48IdleFull_val_ge_sys k_idle hk b
      have := a.isLt; rw [ha]; omega
  have hUfullComm : U_full.1 * pZeroInitExt k_idle hk = pZeroInitExt k_idle hk * U_full.1 := by
    dsimp only [U_full, pZeroInitExt]; rw [QRegister.embedUnitary_val]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sysAct)
      (rExt48IdleFull k_idle hk) hSysDisjExt smToTwosSysUnitary.1 0
  have hVp : (vPrepUltraExtHk k_idle hk initSpec.uStreamInit).1 * pZeroInitExt k_idle hk =
      E_segExt k_idle hk * U_pre.1 := vPrepUltraExtHk_mul_pZeroInitExt hk hk17 initSpec
  have hInitMat : (vPrepUltraExtHk k_idle hk initSpec.uStreamInit * U_full).1 *
      pZeroInitExt k_idle hk = E_segExt k_idle hk * (U_pre.1 * U_full.1) := by
    rw [Submonoid.coe_mul, Matrix.mul_assoc, hUfullComm, ← Matrix.mul_assoc, hVp, Matrix.mul_assoc]
  have hVi : (vInvUltraExtHk k_idle hk initSpec.uStreamInit).1 * E_segExt k_idle hk =
      pZeroInitExt k_idle hk * (U_pre⁻¹).1 := vInvUltraExtHk_mul_E_segExt hk hk17 initSpec
  exact cleanBasisSchedule_correctness_onProj_gen
    (outcomes := gridStates) (U_sys := smToTwosSysUnitary)
    (V_prep := vPrepUltraExtHk k_idle hk initSpec.uStreamInit)
    (V_inv := vInvUltraExtHk k_idle hk initSpec.uStreamInit)
    (W_seg := fun c' j' ↦ uSegOneAngleExtHkGen bValid (sp.prep j') (sp.sel j') M (tbl.cert j').C c')
    (E₀ := pZeroExtOn k_idle hk) (E_seg := pHoistExtOn k_idle hk) c j
    (fun spinUp ↦ by
      rw [smToTwosSysUnitary_fermionicProjector_conj spinUp]
      obtain ⟨E₀, δ_prep, ε_id, Heff_act, Heff_id, hSum, hAGrid, hBE, hIdH, _hIdG, hDiff, hAg⟩ :=
        sp.hPert j c spinUp
      exact approximatesTimeEvolution_of_mul_pZeroInitExt_eq hk
        (unitarySandwichPow_ultra_extHk_oneAngleGen_mul_pZeroInitExt bValid hk hk17 initSpec
          (sp.prep j) (sp.sel j) M (tbl.cert j).C c (schedule j) (tbl.hDiv j)
          (sp.hPrepLow j c) (sp.hPrepCtrl3 j c))
        (stepa_oneAngleUltraSingleCatFermGen_of_gridPerturbat hbValid
          (by decide : 42 ≤ 48) (sp.selImpl j) (tbl.cert j) c j (hSchedNeZero j) spinUp
          (hKrylovFerm j c spinUp) (hBlockComm j c spinUp)
          (sp.hTwist_s2 j c) (sp.hTwist_s1 j c) (sp.hTwist_s0 j c) (sp.hPos_slack j c)
          (hTotErr j) sp.hα (hβ j) hSum hAGrid hBE hIdH hDiff hAg))
    (fun _ _ _ hSA hSW ↦ pZeroExtOn_absorb_concat_anc hk hSA hSW)
    (fun _ _ hD ↦ embedIntertwine2 hD hInitMat)
    (fun _ _ hD ↦ embedIntertwine2 hD
      (uSegOneAngleExtHkGen_mul_E_segExt bValid (sp.prep j) (sp.sel j) M (tbl.cert j).C c
        (tbl.hDiv j) (sp.hPrepLow j c) (sp.hPrepCtrl3 j c)))
    (fun rA rW hD ↦ by
      have pSys := RealizesOnProj.of_clean_embed hD (pZeroInitExt k_idle hk)
        (realizesCleanWorkspace_smToTwosSysOnActDyn hm7 v rA rW hD)
      have pInit := mkInitUltraExtHkDyn_realizesOnProj hk hk17 hm28 initSpec v rA rW hD
      have hChain := pSys.seq_intertwine (embedIntertwine2 hD hUfullComm) pInit
      rw [← QRegister.embedUnitary_mul] at hChain; exact hChain)
    (fun rA rW hD ↦ segSpec.hReal c j v rA rW hD)
    (fun rA rW hD ↦ by
      have pUninit := mkUninitUltraExtHkDyn_realizesOnProj hk hm28 initSpec v rA rW hD
      have pSysInv : RealizesOnProj (pZeroExtOn k_idle hk rA rW)
          (rA.embedUnitary U_full⁻¹) (smToTwosSysOnActDyn hm7 v rA rW hD) := by
        have hInvEq : U_full⁻¹ = U_full := smToTwosSysOnAct_inv_eq
        dsimp only [U_full, sysAct] at hInvEq; rw [hInvEq]
        exact RealizesOnProj.of_clean_embed hD (pZeroInitExt k_idle hk)
          (realizesCleanWorkspace_smToTwosSysOnActDyn hm7 v rA rW hD)
      have hChain := pUninit.seq_intertwine (embedIntertwine2 hD hVi) pSysInv
      rw [← QRegister.embedUnitary_mul] at hChain; exact hChain)
    rSys rAnc hdisj
/-- Turnkey `2 * rotToffSum` (`OneAngleUnheldExtHkGuardSpecBundleGen`) master program. -/
noncomputable def mkGenBetaTwoRotFermGuardMasterProgramGen_mAnc {Var : Type}
    {bValid : Fin (2 ^ systemQubits) → Bool}
    {mAnc mWork k_idle tStreamPair tGuard β_nat M n : ℕ} {hk : k_idle ≤ 48} {α : ℝ}
    {tPrep tSelCtrl tSelCat : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ} (hm28 : 28 ≤ mWork)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (guard :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard) (sp :
    GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle) (schedule : Fin 10 → ℕ)
    (c : Configuration) (j : Fin 10) (v : Var) (rSys : QRegister systemQubits n)
    (rAnc : QRegister mAnc n) (hmAnc : mAnc = hoAncillasM mWork) : DynamicCircuit Var n :=
    slot3InnerCustomSegMasterProgramGen_mAnc hm28 initSpec sp tbl
    (mkCustomOneAngleSegGenOfUnheldGuard (Nat.le_trans (by decide : 1 ≤ 28) hm28) guard sp
    tbl) schedule c j v rSys rAnc hmAnc
theorem mkGenBetaTwoRotFermGuardMasterGen_const_cost_mAnc {Var : Type}
    {bValid : Fin (2 ^ systemQubits) → Bool}
    {mAnc mWork k_idle tStreamPair tGuard β_nat M n costCap : ℕ} {hk : k_idle ≤ 48} {α : ℝ}
    {tPrep tSelCtrl tSelCat : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ} (hm28 : 28 ≤ mWork)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) (guard :
    OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard) (sp :
    GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle) (schedule : Fin 10 → ℕ) (hCap :
    slot3InnerGenSpacetime_CustomSegGen mWork schedule tStreamPair (fun j ↦
    wSegSingleCatExt48_TwoRot_T (tPrep j) (tSelCtrl j) (tSelCat j) tGuard (tbl.rotToffSum j)
    M) ≤ costCap) (c : Configuration) (v : Var) (rSys : QRegister systemQubits n)
    (rAnc : QRegister mAnc n) (hmAnc : mAnc = hoAncillasM mWork) : (∀ j,
    (mkGenBetaTwoRotFermGuardMasterProgramGen_mAnc hm28 initSpec guard sp tbl schedule c j v
    rSys rAnc hmAnc).count TOFF = 0) ∧ (systemQubits + mAnc) * (50 * ∑ j,
    (mkGenBetaTwoRotFermGuardMasterProgramGen_mAnc hm28 initSpec guard sp tbl schedule c j v
    rSys rAnc hmAnc).count T) ≤ costCap := slot3InnerCustomSegMasterGen_const_cost_mAnc hm28
    initSpec sp tbl (mkCustomOneAngleSegGenOfUnheldGuard (Nat.le_trans (by decide : 1 ≤ 28)
    hm28) guard sp tbl) schedule (fun _ ↦ le_rfl) hCap c v rSys rAnc hmAnc
set_option exponentiation.threshold 5000 in
theorem mkGenBetaTwoRotFermGuardMasterGen_correctness_mAnc {Var : Type} [Finite Var]
    [DecidableEq Var] {bValid : Fin (2 ^ systemQubits) → Bool}
    (hbValid : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x)
    {mAnc mWork k_idle tStreamPair tGuard β_nat M n : ℕ} {hk : k_idle ≤ 48} [NeZero (2 ^ n)]
    {α : ℝ} {tPrep tSelCtrl tSelCat : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ} (hk17 : k_idle ≤ 17)
    (hm28 : 28 ≤ mWork) (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair)
    (guard : OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard) (sp :
    GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle) (schedule : Fin 10 → ℕ)
    (hSchedNeZero : ∀ j, schedule j ≠ 0) (hβ : ∀ j : Fin 10, α * ((j.val + 1 : ℝ) / (schedule
    j : ℝ)) = (β_nat : ℝ)) (hTotErr : ∀ j : Fin 10, ((schedule j : ℝ) * ((tbl.nSeg j : ℝ) / (2
    : ℝ) ^ 48) + 2 * catPrepErrUltra1q) + (j.val + 1 : ℝ) * ε_BE j ≤ 0.01) (hKrylovFerm : ∀ (j
    : Fin 10) (c : Configuration) (spinUp : Finset (Fin numElectrons)), RawBEMapsFermToKrylov3
    spinUp (fullSysRawBEUnitary sp.qft (sp.prep j) (sp.selOra j) c)) (hBlockComm : ∀ (j : Fin
    10) (c : Configuration) (spinUp : Finset (Fin numElectrons)), RawBEBlockCommutesFerm
    spinUp (fullSysRawBEUnitary sp.qft (sp.prep j) (sp.selOra j) c)) (c : Configuration)
    (j : Fin 10) (v : Var) (rSys : QRegister systemQubits n) (rAnc : QRegister mAnc n)
    (hmAnc : mAnc = hoAncillasM mWork) (hdisj : rSys.DisjointWires rAnc) : ∃ W, (∀ spinUp,
    ApproximatesTimeEvolution (hamiltonian c) (j.val + 1 : ℝ) 0.01 (fermionicProjector spinUp)
    W) ∧ RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys gridStates rAnc hdisj W
    (mkGenBetaTwoRotFermGuardMasterProgramGen_mAnc hm28 initSpec guard sp tbl schedule c j v
    rSys rAnc hmAnc).compile := slot3InnerCustomSegMasterFermGen_correctness_mAnc hbValid hk17 hm28
    initSpec sp tbl (mkCustomOneAngleSegGenOfUnheldGuard (Nat.le_trans (by decide : 1 ≤ 28)
    hm28) guard sp tbl) schedule hSchedNeZero hβ hTotErr hKrylovFerm hBlockComm c j v rSys
    rAnc hmAnc hdisj
end ExtHkGenLift
end FermionicKrylovSegBridge
end
end FermionicKrylovSegBridge

end QuantumComputation.Specs.StoppingPowerSolution
end
