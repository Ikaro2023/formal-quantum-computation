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

public import QuantumComputation.QuantumHoareLogic.CQAssertion
public import QuantumComputation.QuantumHoareLogic.CQState
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.AsymTwistShell

set_option Elab.async false

/-!
# Open-Anchor `rAnchor18` `uSlot0Sum42Add` Seam Cancellation (`-216 T/Select`)

Inside `dSingleBarrel6StepAnchorMWork`, Stage A (`dStageARawAnchor_ofStr`) ends by adding the
18-wire `rAnchor18` momentum back into `rSum42` (`dAddSlot0ToSum42`, `156 T`) and conjugating
by `dPreDiagCliffordAnchorInv`, while two-load Stage B immediately re-applies
`dPreDiagCliffordAnchor`, leaves `rAnchor18` and `rSum42` untouched across its outer true-swap
prefix (`cSwapCore3967` + `dTwoLoadHeldKTrueSwapShiftedPartner` load), and subtracts
`rAnchor18 + rPartner18` from `rSum42` (`dSubTwoElec36FromSum42`, `216 T`).

Omitting `dAddSlot0ToSum42` at the end of Stage A (`-156 T`), replacing `dSubTwoElec36FromSum42`
at the entry of Stage B's inner two-electron stream by the single-electron partner subtraction
`dSubSlot0FromSum42` (`216 -> 156 T`, `-60 T`), and wrapping the fused `(Stage A, Stage B)` pair
in a single `dWrapPreDiagCliffordAnchor` shaves `156 + 60 = 216 T` per `Select` (`0` `TOFF`,
`0` extra ancillas) while realizing the exact `uFoldedCtrlFull` and `uFoldedCatFull` unitaries
of `slimFoldedBundle179_Borrow48054`.
-/

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section SlimStageBAnchorInput_Bridge
section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 256
namespace SlimStageBAnchorInput
open SpecsAux SpecsAux.SpecMirror
open Operator
local instance (priority := 1000000) instNeZero_SlimBridge (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open BoothOpt_StageBPartnerCoreShave (stageBFastBoothOptAnchorT)
open BoothOpt_FastAnchorOuterAndStageBShave
  (mkFoldedPass123Bundle179_11_FastAnchorStandalone)
open ChiralDStageABridge (stageAAnchorInputBorrow48054_179_11)
open SlimStageBCircuits (mkStageBAnchorInput179_11_boothOpt)

/-- Concrete zero-hypothesis `SlimFoldedPass123Bundle11 179` pairing `48,054-T` Borrow
Stage A with Booth-optimized Stage B (`74,030 + stageBFastBoothOptAnchorT` `T`, `0 TOFF`). -/
noncomputable def slimFoldedBundle179_Borrow48054
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27) :
    TruncWAsymHeldTwShell.SlimFoldedPass123Bundle11
      179 B hB6 hB27
      (fun j ↦ 25252 + 724 + 48054 + stageBFastBoothOptAnchorT (B j) 141)
      (fun j ↦ 25252 + 724 + 48054 + stageBFastBoothOptAnchorT (B j) 144) :=
  let b := mkFoldedPass123Bundle179_11_FastAnchorStandalone
    stageAAnchorInputBorrow48054_179_11
    (mkStageBAnchorInput179_11_boothOpt B hB6 hB27)
  { uFoldedCtrlFull := b.uFoldedCtrlFull
    uFoldedCatFull := b.uFoldedCatFull
    uFoldedSeg := b.uFoldedSeg
    hInterRawCtrl := b.hInterRawCtrl
    hInterRawCat := b.hInterRawCat
    hCtrl3Seg := b.hCtrl3Seg
    hIdle11Seg := b.hIdle11Seg
    hSlackSeg := b.hSlackSeg
    hCat48 := b.hCat48 }

end SlimStageBAnchorInput
end
end SlimStageBAnchorInput_Bridge


section P1OpenAnchorAdd0TwoLoad
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency false

namespace P1_OpenAnchorAdd0TwoLoad

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instNeZero_P1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

local instance (priority := 1000000) instGroupUnitaryFast_P1 (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instSemigroupUnitaryFast_P1 (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  (instGroupUnitaryFast_P1 D).toSemigroup

open Operator QProg Matrix Real
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
open SpecsAux

/-! ## Section 1: `uSlot0Sum42Add 80` vs `uElec18Sum42Add` Register Congruence -/

section Part1_Slot0CoreVsElec18AddBridge

open InterWalkRSum42Hoist (qreg_block_apply)
open FullSysCatSegmentBridge (fullSysCoreWires)
open Slot0SubAdd14And217Stream
  (rSum14Slice42 selCoreSum14In42 compose_selCoreSum14In42 slot0AxisInCore
   slot0AxisVal slot0AxisVal_eq_sum uSlot0AxisAdd14 uSlot0Sum42Add)
open LocalStageBTwoElecQftStream218Inner
  (rAxis6In18 elec18AxisWire elec18AxisVal elec18AxisVal_eq_sum
   uElec18AxisAdd14 selElec18Sum14In42 compose_selElec18Sum14In42
   uElec18Sum42Add embedUnitary_catModAddUnitary_congr_sys)

theorem slot0AxisInCore80_val_eq_elec18AxisWire (w : Fin 3) (r : Fin 6) :
    (slot0AxisInCore (mPayload := 80) w r).val = (elec18AxisWire w r).val := by
  have hL : (slot0AxisInCore (mPayload := 80) w r).val = (18 * 0 + 6 * w.val) + r.val := rfl
  have hR : (elec18AxisWire w r).val = 6 * w.val + r.val := by
    simp [elec18AxisWire, rAxis6In18]
  omega

/-- Embedding `uSlot0Sum42Add 80` on `rCore ++ rSum42` agrees with embedding `uElec18Sum42Add`
on `rE18 ++ rSum42` whenever the first `18` wires of `rCore` match `rE18`. -/
theorem embed_uSlot0Sum42Add_eq_uElec18Sum42Add {N : ℕ}
    (rCore : QRegister (fullSysCoreWires 80) N)
    (rE18 : QRegister 18 N) (rSum42 : QRegister 42 N)
    (hCS : rCore.DisjointWires rSum42) (hES : rE18.DisjointWires rSum42)
    (hSlot0 : ∀ q : Fin 18,
      rCore ⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ = rE18 q) :
    (rCore.concat rSum42 hCS).embedUnitary (uSlot0Sum42Add 80) =
      (rE18.concat rSum42 hES).embedUnitary uElec18Sum42Add := by
  have hAx : ∀ w : Fin 3,
      (rCore.concat rSum42 hCS).embedUnitary
        ((selCoreSum14In42 80 w).embedUnitary (uSlot0AxisAdd14 w)) =
      (rE18.concat rSum42 hES).embedUnitary
        ((selElec18Sum14In42 w).embedUnitary (uElec18AxisAdd14 w)) := fun w ↦ by
    rw [← QRegister.embedUnitary_compose, compose_selCoreSum14In42,
        ← QRegister.embedUnitary_compose, compose_selElec18Sum14In42]
    unfold uSlot0AxisAdd14 uElec18AxisAdd14
    refine embedUnitary_catModAddUnitary_congr_sys rCore rE18
      (rSum42.compose (rSum14Slice42 w))
      (hCS.compose_right _) (hES.compose_right _)
      (slot0AxisVal w) (elec18AxisVal w) fun β ↦ ?_
    rw [slot0AxisVal_eq_sum, elec18AxisVal_eq_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hIdx : slot0AxisInCore (mPayload := 80) w r =
        ⟨(elec18AxisWire w r).val,
          lt_of_lt_of_le (elec18AxisWire w r).isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ :=
      Fin.ext (slot0AxisInCore80_val_eq_elec18AxisWire w r)
    rw [hIdx, hSlot0 (elec18AxisWire w r)]
  unfold uSlot0Sum42Add uElec18Sum42Add
  simp only [QRegister.embedUnitary_mul, hAx 0, hAx 1, hAx 2]

theorem realizesClean_congr_embed
    {Var : Type} [Fintype Var] [DecidableEq Var] {k₁ k₂ m n : ℕ} [NeZero (2 ^ n)]
    {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n} {rW : QRegister m n}
    {U₁ : Unitary (2 ^ k₁)} {U₂ : Unitary (2 ^ k₂)} {d : DynamicCircuit Var n}
    (hU : r₁.embedUnitary U₁ = r₂.embedUnitary U₂)
    (h : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r₁ rW U₁ d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r₂ rW U₂ d := by
  intro M
  obtain ⟨M', hwp, hEq⟩ := h M
  rw [hU] at hEq
  exact ⟨M', hwp, hEq⟩

end Part1_Slot0CoreVsElec18AddBridge

/-! ## Section 2: Open Stage-A Raw Anchor (`47,898 T`, omitting trailing `dAddSlot0ToSum42`) -/

section Part2_OpenStageARawAnchor

open HoistBorrow42ProjBridge (RealizesOnProj)
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_concat_left
   disjointWires_compose_of_disjoint)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (rFullSysElecSlot_val)
open InterWalkRSum42Hoist (kFull80 rCoreFull rSum0 E_rawStream42 qreg_ext)
open Leaf4Ext48TopStitch
  (rCoreFull_disj_rSum0 rPGIdle rUnusedCtrl3Full rExt6Full
   pExt6Zero pExt6IdleZero pExt6IdleZero_eq_mul pCtrl3Zero pPGIdleZero)
open DoubleDutyFoldedRealizesBridge
  (rPG7Full hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full)
open HeldStreamFoldedPass123Bridge (E_rawCtrl3Ext E_rawSegExt)
open Slot0SubAdd14And217Stream
  (uSlot0Sum42Add dSubSlot0FromSum42 dAddSubSlot0Sum42_counts dAddSubSlot0Sum42_realizesPair)
open FullConcrete7StepAndTrueSwapSelect
  (selCoreSum42InAct selCatInCoreSum42PG7 concat_compose_selCoreSum42InAct)
open ForestQft117BundleNoTopBridge
  (dCanonStage128Fwd dCanonStage128Inv count_dCanonStage128Fwd_toff count_dCanonStage128Inv_toff
   count_dCanonStage128Fwd_t count_dCanonStage128Inv_t
   dCanonStage128Fwd_realizes dCanonStage128Inv_realizes)
open StageADeconstrCore
  (selDataInAct selDataInAct_apply selMeasInAct selDataInAct_disj_selMeasInAct
   concat_compose_selDataInAct concat_compose_selMeasInAct)
open StageAConjHAndStreamBridge
open BoothOpt_Anchor218CachedTrueSwapOuter
open StageADeconstrAndQftShare
  (StrCallback dInnerSwapAnchor_ofStr count_dInnerSwapAnchor_ofStr_toff
   count_dInnerSwapAnchor_ofStr_t_le dInnerSwapAnchor_ofStr_realizesOnProj
   basisOutcomeProjector_comm_part4 realizesOnProj_of_clean_proj0 realizesOnProj_seq_part4
   E_anchor_mul_right E_raw217 uStr218_3Axis uSlot0MeasSwap_conj_uSlot0Sum42Add_eq
   uSlot0MeasSwap_conj_activeOneElecExpQft_eq uSlot0Sum42Full_inv_mul_E_rawStream42
   uExpQft0Full_comm_E_raw217 uInnerSwapFull uInnerSwapFull_def
   rActStageAFull80_disj_rPGIdle11)

/-- Full-width (`kFull80`) `uSlot0Sum42Add 80` unitary at the Stage-A / Stage-B seam. -/
noncomputable abbrev uAddStageAFull : Unitary (2 ^ kFull80) :=
  rActStageAFull80.embedUnitary (selCoreSum42InAct.embedUnitary (uSlot0Sum42Add 80))

/-- Combined `(18 + 42)`-wire selector `(rAnchor18, rSum0)` inside `kFull80 + 18`. -/
def selAncSum0InFull18 : QRegister (18 + 42) (kFull80 + 18) :=
  (selMeasInAct kFull80).concat ((selDataInAct kFull80).compose rSum0)
    ((QRegExt.disjointWires_symm (selDataInAct_disj_selMeasInAct kFull80)).compose_right rSum0)

/-- Anchor-slot `18`-electron addition into `rSum0` directly on `kFull80 + 18`. -/
noncomputable def uAdd0AncFull18 : Unitary (2 ^ (kFull80 + 18)) :=
  selAncSum0InFull18.embedUnitary
    LocalStageBTwoElecQftStream218Inner.uElec18Sum42Add

theorem uAnchorFrame_uAddStageAFull_eq :
    uAnchorFrame uAddStageAFull = uAdd0AncFull18 := by
  have hSwap := uSlot0MeasSwap_conj_uSlot0Sum42Add_eq.1
  change uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary uAddStageAFull * uSlot0MeasSwap =
    uAnchorFrame uAddStageAFull at hSwap
  have hSubMat : (selSubstSlot0 rSlot0InFull).embedUnitary uAddStageAFull =
      uAnchorFrame uAddStageAFull := by
    rw [← hSwap]
    exact Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull uAddStageAFull.1)
  rw [← hSubMat]
  unfold uAddStageAFull uAdd0AncFull18
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
  let rSub := selSubstSlot0 rSlot0InFull
  let rSubCore := rSub.compose rCoreFull
  let rSubSum := rSub.compose rSum0
  let rSubPG7 := rSub.compose rPG7Full
  let hSubCS := disjointWires_compose_of_disjoint rSub rCoreFull_disj_rSum0
  let hSubCPG := disjointWires_compose_of_disjoint rSub hCoreFull_disj_rPG7Full
  let hSubSPG := disjointWires_compose_of_disjoint rSub rSum0_disj_rPG7Full
  have hSubActEq : rSub.compose rActStageAFull80 =
      (rSubCore.concat rSubSum hSubCS).concat rSubPG7
        (disjointWires_concat_left hSubCS hSubCPG hSubSPG) := by
    apply qreg_ext
    intro idx
    refine Fin.addCases (fun iCS ↦ ?_) (fun mPG ↦ ?_) idx
    · refine Fin.addCases (fun iC ↦ ?_) (fun jS ↦ ?_) iCS
      · simp [rSubCore, rActStageAFull80, rCSFull80,
          QRegister.concat_apply_left]
      · simp [rSubSum, rActStageAFull80, rCSFull80,
          QRegister.concat_apply_left, QRegister.concat_apply_right]
    · simp [rSubPG7, rActStageAFull80, QRegister.concat_apply_right]
  have hSubCSComp : (rSub.compose rActStageAFull80).compose selCoreSum42InAct =
      rSubCore.concat rSubSum hSubCS := by
    rw [hSubActEq, concat_compose_selCoreSum42InAct _ rSubPG7
      (disjointWires_concat_left hSubCS hSubCPG hSubSPG)]
  rw [hSubCSComp]
  have hSumEq : rSubSum = (selDataInAct kFull80).compose rSum0 := by
    apply qreg_ext
    intro j
    have hnot : rSum0 j ∉ Set.range rSlot0InFull.wires := by
      rintro ⟨q, hq⟩
      have hDisj : rSlot0InFull.DisjointWires rSum0 :=
        rCoreFull_disj_rSum0.compose_left rSlot0InCore
      exact hDisj.ne q j hq
    dsimp only [rSubSum, rSub, QRegister.compose_apply]
    rw [selSubstSlot0, rDataSubstSlot0_apply_of_not_mem rSlot0InFull _ _ _ hnot]
  have hDisjM : (selMeasInAct kFull80).DisjointWires rSubSum := by
    rw [hSumEq]
    exact (QRegExt.disjointWires_symm (selDataInAct_disj_selMeasInAct kFull80)).compose_right rSum0
  have hSlot0 : ∀ q : Fin 18,
      rSubCore ⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ =
        selMeasInAct kFull80 q := fun q ↦ by
    have hq : (⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ :
        Fin (fullSysCoreWires 80)) = rSlot0InCore q :=
      Fin.ext (by
        rw [rSlot0InCore, rFullSysElecSlot_val]
        simp)
    rw [hq]
    dsimp only [rSubCore, rSub, QRegister.compose_apply]
    change selSubstSlot0 rSlot0InFull (rSlot0InFull q) = selMeasInAct kFull80 q
    rw [selSubstSlot0, rDataSubstSlot0_apply_slot0]
  rw [embed_uSlot0Sum42Add_eq_uElec18Sum42Add rSubCore (selMeasInAct kFull80) rSubSum
    hSubCS hDisjM hSlot0]
  refine congrArg (fun r : QRegister (18 + 42) (kFull80 + 18) ↦ r.embedUnitary _)
    (qreg_ext fun idx ↦ ?_)
  refine Fin.addCases (fun q ↦ ?_) (fun j ↦ ?_) idx
  · rw [QRegister.concat_apply_left, selAncSum0InFull18, QRegister.concat_apply_left]
  · rw [QRegister.concat_apply_right, selAncSum0InFull18, QRegister.concat_apply_right,
        hSumEq]

theorem uAnchorFrame_uAddStageAFull_inv_eq :
    uAnchorFrame uAddStageAFull⁻¹ = uAdd0AncFull18⁻¹ := by
  have hSwap := uSlot0MeasSwap_conj_uSlot0Sum42Add_eq.1
  change uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary uAddStageAFull * uSlot0MeasSwap =
    uAnchorFrame uAddStageAFull at hSwap
  have hSubFwd : (selSubstSlot0 rSlot0InFull).embedUnitary uAddStageAFull =
      uAnchorFrame uAddStageAFull := by
    rw [← hSwap]
    exact Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull uAddStageAFull.1)
  have hSwapInv := uSlot0MeasSwap_conj_uSlot0Sum42Add_eq.2
  change uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary uAddStageAFull⁻¹ * uSlot0MeasSwap =
    uAnchorFrame uAddStageAFull⁻¹ at hSwapInv
  have hSubInv : (selSubstSlot0 rSlot0InFull).embedUnitary uAddStageAFull⁻¹ =
      uAnchorFrame uAddStageAFull⁻¹ := by
    rw [← hSwapInv]
    exact Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull (uAddStageAFull⁻¹).1)
  have hEmbedInv : (selSubstSlot0 rSlot0InFull).embedUnitary uAddStageAFull⁻¹ =
      ((selSubstSlot0 rSlot0InFull).embedUnitary uAddStageAFull)⁻¹ := by
    apply Subtype.ext
    change (selSubstSlot0 rSlot0InFull).embedMatrix (star uAddStageAFull.1) =
      star ((selSubstSlot0 rSlot0InFull).embedMatrix uAddStageAFull.1)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
        QRegister.embedMatrix_conjTranspose]
  rw [← hSubInv, hEmbedInv, hSubFwd, uAnchorFrame_uAddStageAFull_eq]


end Part2_OpenStageARawAnchor

/-! ## Section 2b: Open-QFT Stage-A Raw Anchor (`47,781 T`, omitting trailing `dQftI`, `-117 T`) -/

section Part2_OpenQftStageARawAnchor

open HoistBorrow42ProjBridge (RealizesOnProj)
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_concat_left
   disjointWires_compose_of_disjoint)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (rFullSysElecSlot_val)
open InterWalkRSum42Hoist (kFull80 rCoreFull rSum0 E_rawStream42 qreg_ext qreg_block_apply)
open DyadicQft64WalkCircuit (rIdInCat rPGInCat)
open Leaf4Ext48TopStitch
  (rCoreFull_disj_rSum0 rPGIdle rUnusedCtrl3Full rExt6Full
   pExt6Zero pExt6IdleZero pExt6IdleZero_eq_mul pCtrl3Zero pPGIdleZero)
open DoubleDutyFoldedRealizesBridge
  (rPG7Full hCoreFull_disj_rPG7Full rSum0_disj_rPG7Full)
open HeldStreamFoldedPass123Bridge (E_rawCtrl3Ext E_rawSegExt)
open Slot0SubAdd14And217Stream
  (uSlot0Sum42Add dSubSlot0FromSum42 dAddSubSlot0Sum42_counts dAddSubSlot0Sum42_realizesPair)
open FullConcrete7StepAndTrueSwapSelect
  (selCoreSum42InAct selCatInCoreSum42PG7 concat_compose_selCoreSum42InAct)
open ZeroHypLHSStageAB7Step3StepCatState48Proje
  (rIdInCoreSum42 concat_compose_selCatInCoreSum42PG7)
open MasterZeroHypCompactAndCompactTopBridge (sel18InSys sel25InCat)
open ForestQft117BundleNoTopBridge
  (dCanonStage128Fwd count_dCanonStage128Fwd_toff count_dCanonStage128Fwd_t
   dCanonStage128Fwd_realizes)
open StageADeconstrCore
  (selDataInAct selDataInAct_apply selMeasInAct selMeasInAct_apply
   selDataInAct_disj_selMeasInAct concat_compose_selDataInAct concat_compose_selMeasInAct)
open StageAConjHAndStreamBridge
open BoothOpt_Anchor218CachedTrueSwapOuter
open StageADeconstrAndQftShare
  (StrCallback dInnerSwapAnchor_ofStr count_dInnerSwapAnchor_ofStr_toff
   count_dInnerSwapAnchor_ofStr_t_le dInnerSwapAnchor_ofStr_realizesOnProj
   basisOutcomeProjector_comm_part4 realizesOnProj_of_clean_proj0 realizesOnProj_seq_part4
   E_anchor_mul_right E_raw217 uStr218_3Axis uSlot0MeasSwap_conj_uSlot0Sum42Add_eq
   uSlot0MeasSwap_conj_activeOneElecExpQft_eq uSlot0Sum42Full_inv_mul_E_rawStream42
   uExpQft0Full_comm_E_raw217 uInnerSwapFull uInnerSwapFull_def
   rActStageAFull80_disj_rPGIdle11 SupportedOnSel25
   supportedOnSel25_activeOneElecExpQftStage128)

private theorem exists_unitary_embed_eq_of_smul {k N : ℕ} [NeZero (2 ^ N)]
    (sel : QRegister k N) (U : Unitary (2 ^ N)) (c : ℂ) (u : Unitary (2 ^ k))
    (hU : U.1 = c • (sel.embedUnitary u).1) :
    ∃ u' : Unitary (2 ^ k), U = sel.embedUnitary u' ∧ u'.1 = c • u.1 := by
  let V : Unitary (2 ^ N) := sel.embedUnitary u
  have hUU : U.1 * star U.1 = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  have hVV : V.1 * star V.1 = 1 := Matrix.mem_unitaryGroup_iff.mp V.2
  have hc1 : c * star c = 1 := by
    have hMat : (1 : Operator (2 ^ N)) = (c * star c) • (1 : Operator (2 ^ N)) := by
      calc (1 : Operator (2 ^ N))
          = U.1 * star U.1 := hUU.symm
        _ = (c • V.1) * star (c • V.1) := by rw [hU]
        _ = (c • V.1) * (star c • star V.1) := by rw [star_smul]
        _ = (c * star c) • (V.1 * star V.1) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = (c * star c) • 1 := by rw [hVV]
    have h00 := congrFun (congrFun hMat 0) 0
    simpa using h00.symm
  have hMem : c • u.1 ∈ Matrix.unitaryGroup (Fin (2 ^ k)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc1,
        Matrix.mem_unitaryGroup_iff.mp u.2, one_smul]
  refine ⟨⟨c • u.1, hMem⟩, ?_, rfl⟩
  apply Subtype.ext
  rw [hU, QRegister.embedUnitary_val, QRegister.embedUnitary_val, QRegister.embedMatrix_smul]

theorem exists_uExpQft25 :
    ∃ u' : Unitary (2 ^ (18 + 7)),
      activeOneElecExpQftStage128.uCat = sel25InCat.embedUnitary u' := by
  obtain ⟨c, u25, hc⟩ := supportedOnSel25_activeOneElecExpQftStage128
  obtain ⟨u', hu', _⟩ := exists_unitary_embed_eq_of_smul sel25InCat
    activeOneElecExpQftStage128.uCat c u25 hc
  exact ⟨u', hu'⟩

/-- Exact `25`-wire (`18 + 7`) unitary witness for `activeOneElecExpQftStage128.uCat` on
`sel25InCat` with scalar absorbed into the local unitary. -/
noncomputable def uExpQft25 : Unitary (2 ^ (18 + 7)) :=
  Classical.choose exists_uExpQft25

theorem activeOneElecExpQftStage128_uCat_eq_sel25 :
    activeOneElecExpQftStage128.uCat = sel25InCat.embedUnitary uExpQft25 :=
  Classical.choose_spec exists_uExpQft25

/-- Full-width (`kFull80`) `activeOneElecExpQftStage128.uCat` unitary at the
Stage-A / Stage-B seam. -/
noncomputable abbrev uExpQftStageAFull : Unitary (2 ^ kFull80) :=
  rActStageAFull80.embedUnitary
    (selCatInCoreSum42PG7.embedUnitary activeOneElecExpQftStage128.uCat)

/-- Combined full-width (`kFull80`) raw-catalyst seam unitary
`uAddStageAFull * uExpQftStageAFull⁻¹`. -/
noncomputable abbrev uJunctionRawFull : Unitary (2 ^ kFull80) :=
  uAddStageAFull * uExpQftStageAFull⁻¹

/-- Combined `(18 + 7)`-wire selector `(rAnchor18, rPG7Full)` inside `kFull80 + 18`. -/
def selAncPG7InFull18 : QRegister (18 + 7) (kFull80 + 18) :=
  (selMeasInAct kFull80).concat ((selDataInAct kFull80).compose rPG7Full)
    ((QRegExt.disjointWires_symm (selDataInAct_disj_selMeasInAct kFull80)).compose_right rPG7Full)

/-- Anchor-slot `18`-electron + `7`-catalyst `QFT_64` unitary directly on `kFull80 + 18`. -/
noncomputable def uQft0AncFull18 : Unitary (2 ^ (kFull80 + 18)) :=
  selAncPG7InFull18.embedUnitary uExpQft25

/-- Combined anchor-frame seam unitary `uAdd0AncFull18 * uQft0AncFull18⁻¹` on `kFull80 + 18`. -/
noncomputable def uJunctionAncFull18 : Unitary (2 ^ (kFull80 + 18)) :=
  uAdd0AncFull18 * uQft0AncFull18⁻¹

theorem compose_selAncPG7InFull18_eq {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) :
    (rAct.concat rAnchor18 hAA).compose selAncPG7InFull18 =
      rAnchor18.concat (rAct.compose rPG7Full) (QRegExt.disjointWires_symm (hAA.compose_left
        rPG7Full)) := by
  apply qreg_ext
  intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun q ↦ ?_) (fun m ↦ ?_) idx
  · rw [selAncPG7InFull18, QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hq : selMeasInAct kFull80 q = Fin.natAdd kFull80 q := selMeasInAct_apply q
    rw [hq, QRegister.concat_apply_right]
  · rw [selAncPG7InFull18, QRegister.concat_apply_right, QRegister.concat_apply_right]
    change (rAct.concat rAnchor18 hAA) (selDataInAct kFull80 (rPG7Full m)) = rAct (rPG7Full m)
    rw [selDataInAct_apply, QRegister.concat_apply_left]

theorem uAnchorFrame_uExpQftStageAFull_eq :
    uAnchorFrame uExpQftStageAFull = uQft0AncFull18 := by
  have hSwap := uSlot0MeasSwap_conj_activeOneElecExpQft_eq.1
  change uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary uExpQftStageAFull * uSlot0MeasSwap =
    uAnchorFrame uExpQftStageAFull at hSwap
  have hSubMat : (selSubstSlot0 rSlot0InFull).embedUnitary uExpQftStageAFull =
      uAnchorFrame uExpQftStageAFull := by
    rw [← hSwap]
    exact Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull uExpQftStageAFull.1)
  rw [← hSubMat]
  unfold uExpQftStageAFull uQft0AncFull18
  rw [activeOneElecExpQftStage128_uCat_eq_sel25,
      ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
      ← QRegister.embedUnitary_compose]
  let rSub := selSubstSlot0 rSlot0InFull
  let rSubCore := rSub.compose rCoreFull
  let rSubSum := rSub.compose rSum0
  let rSubPG7 := rSub.compose rPG7Full
  let hSubCS := disjointWires_compose_of_disjoint rSub rCoreFull_disj_rSum0
  let hSubCPG := disjointWires_compose_of_disjoint rSub hCoreFull_disj_rPG7Full
  let hSubSPG := disjointWires_compose_of_disjoint rSub rSum0_disj_rPG7Full
  have hSubActEq : rSub.compose rActStageAFull80 =
      (rSubCore.concat rSubSum hSubCS).concat rSubPG7
        (disjointWires_concat_left hSubCS hSubCPG hSubSPG) := by
    apply qreg_ext
    intro idx
    refine Fin.addCases (fun iCS ↦ ?_) (fun mPG ↦ ?_) idx
    · refine Fin.addCases (fun iC ↦ ?_) (fun jS ↦ ?_) iCS
      · simp [rSubCore, rActStageAFull80, rCSFull80,
          QRegister.concat_apply_left]
      · simp [rSubSum, rActStageAFull80, rCSFull80,
          QRegister.concat_apply_left, QRegister.concat_apply_right]
    · simp [rSubPG7, rActStageAFull80, QRegister.concat_apply_right]
  have hSubCatEq : (rSub.compose rActStageAFull80).compose selCatInCoreSum42PG7 =
      ((rSubCore.concat rSubSum hSubCS).compose rIdInCoreSum42).concat rSubPG7
        ((disjointWires_concat_left hSubCS hSubCPG hSubSPG).compose_left rIdInCoreSum42) := by
    rw [hSubActEq, concat_compose_selCatInCoreSum42PG7]
  have hPG7Eq : rSubPG7 = (selDataInAct kFull80).compose rPG7Full := by
    apply qreg_ext
    intro m
    have hnot : rPG7Full m ∉ Set.range rSlot0InFull.wires := by
      rintro ⟨q, hq⟩
      have hDisj : rSlot0InFull.DisjointWires rPG7Full :=
        hCoreFull_disj_rPG7Full.compose_left rSlot0InCore
      exact hDisj.ne q m hq
    change selSubstSlot0 rSlot0InFull (rPG7Full m) = selDataInAct kFull80 (rPG7Full m)
    rw [selSubstSlot0, rDataSubstSlot0_apply_of_not_mem rSlot0InFull _ _ _ hnot]
  rw [hSubCatEq]
  refine congrArg (fun r : QRegister (18 + 7) (kFull80 + 18) ↦ r.embedUnitary uExpQft25)
    (qreg_ext fun idx ↦ ?_)
  refine Fin.addCases (fun q ↦ ?_) (fun m ↦ ?_) idx
  · let jSys : Fin (3924 + 3) := sel18InSys q
    have hq25 : sel25InCat (Fin.castAdd 7 q) = Fin.castAdd 7 jSys := by
      change ((rIdInCat.compose sel18InSys).concat rPGInCat _) (Fin.castAdd 7 q) =
        Fin.castAdd 7 jSys
      rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [jSys, sel18InSys, rIdInCat])
    have hjId : rIdInCoreSum42 jSys = Fin.castAdd 42 (rSlot0InCore q) := by
      apply Fin.ext
      rw [rIdInCoreSum42_wires_val_of_lt3924_assoc jSys
          (by have := q.isLt; simp [jSys, sel18InSys]; omega),
          Fin.val_castAdd, rSlot0InCore, rFullSysElecSlot_val]
      simp [jSys, sel18InSys]
    rw [QRegister.compose_apply, hq25, QRegister.concat_apply_left,
        QRegister.compose_apply, hjId, QRegister.concat_apply_left,
        selAncPG7InFull18, QRegister.concat_apply_left]
    dsimp only [rSubCore, rSub, QRegister.compose_apply]
    change selSubstSlot0 rSlot0InFull (rSlot0InFull q) = selMeasInAct kFull80 q
    rw [selSubstSlot0, rDataSubstSlot0_apply_slot0]
  · have hm25 : sel25InCat (Fin.natAdd 18 m) = Fin.natAdd (3924 + 3) m := by
      change ((rIdInCat.compose sel18InSys).concat rPGInCat _) (Fin.natAdd 18 m) =
        Fin.natAdd (3924 + 3) m
      rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rPGInCat])
    rw [QRegister.compose_apply, hm25, QRegister.concat_apply_right,
        selAncPG7InFull18, QRegister.concat_apply_right, hPG7Eq]

theorem uAnchorFrame_uExpQftStageAFull_inv_eq :
    uAnchorFrame uExpQftStageAFull⁻¹ = uQft0AncFull18⁻¹ := by
  have hSwap := uSlot0MeasSwap_conj_activeOneElecExpQft_eq.1
  change uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary uExpQftStageAFull * uSlot0MeasSwap =
    uAnchorFrame uExpQftStageAFull at hSwap
  have hSubFwd : (selSubstSlot0 rSlot0InFull).embedUnitary uExpQftStageAFull =
      uAnchorFrame uExpQftStageAFull := by
    rw [← hSwap]
    exact Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull uExpQftStageAFull.1)
  have hSwapInv := uSlot0MeasSwap_conj_activeOneElecExpQft_eq.2
  change uSlot0MeasSwap * (selDataInAct kFull80).embedUnitary uExpQftStageAFull⁻¹ * uSlot0MeasSwap =
    uAnchorFrame uExpQftStageAFull⁻¹ at hSwapInv
  have hSubInv : (selSubstSlot0 rSlot0InFull).embedUnitary uExpQftStageAFull⁻¹ =
      uAnchorFrame uExpQftStageAFull⁻¹ := by
    rw [← hSwapInv]
    exact Subtype.ext (embedMatrix_selSubstSlot0_eq rSlot0InFull (uExpQftStageAFull⁻¹).1)
  have hEmbedInv : (selSubstSlot0 rSlot0InFull).embedUnitary uExpQftStageAFull⁻¹ =
      ((selSubstSlot0 rSlot0InFull).embedUnitary uExpQftStageAFull)⁻¹ := by
    apply Subtype.ext
    change (selSubstSlot0 rSlot0InFull).embedMatrix (star uExpQftStageAFull.1) =
      star ((selSubstSlot0 rSlot0InFull).embedMatrix uExpQftStageAFull.1)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
        QRegister.embedMatrix_conjTranspose]
  rw [← hSubInv, hEmbedInv, hSubFwd, uAnchorFrame_uExpQftStageAFull_eq]

theorem uAnchorFrame_uJunctionRawFull_eq :
    uAnchorFrame uJunctionRawFull = uJunctionAncFull18 := by
  rw [uJunctionRawFull, ← uAnchorFrame_mul, uAnchorFrame_uAddStageAFull_eq,
      uAnchorFrame_uExpQftStageAFull_inv_eq, uJunctionAncFull18]

private theorem mul_inv_inv_eq {G : Type*} [Group G] (a b : G) :
    (a * b⁻¹)⁻¹ = b * a⁻¹ :=
  inv_eq_of_mul_eq_one_left (by
    calc (b * a⁻¹) * (a * b⁻¹)
        = b * (a⁻¹ * a) * b⁻¹ := by simp only [_root_.mul_assoc]
      _ = b * b⁻¹ := by rw [inv_mul_cancel, mul_one]
      _ = 1 := mul_inv_cancel b)

theorem uAnchorFrame_uJunctionRawFull_inv_eq :
    uAnchorFrame uJunctionRawFull⁻¹ = uJunctionAncFull18⁻¹ := by
  rw [uJunctionRawFull, mul_inv_inv_eq, ← uAnchorFrame_mul,
      uAnchorFrame_uExpQftStageAFull_eq, uAnchorFrame_uAddStageAFull_inv_eq,
      uJunctionAncFull18, mul_inv_inv_eq]

end Part2_OpenQftStageARawAnchor

/-! ## Section 3: Two-Load Stage-B Raw Anchor (`stageBTwoLoadBoothOptAnchorT B mClean - 60`) -/

section Part3_OpenTwoLoadStageB

open PosSlots24BranchConcrete (posCoreWires rElecSlot)
open FullSysCatSegmentBridge
  (fullSysCoreWires disjointWires_compose_of_disjoint
   disjointWires_concat_left)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (rFullSysElecSlot_val)
open PosPostPrep80MergedVep (cSwapCore3967 uSwapCore3967 lockPosPostVal_eq)
open HoistBorrow42ProjBridge (RealizesOnProj)
open InterWalkRSum42Hoist (kFull80 rCoreFull rSum0 qreg_block_apply)
open Leaf4Ext48TopStitch (rExt6IdleFull)
open HeldStreamFoldedPass123Bridge (E_rawCtrl3Ext E_rawSegExt)
open LocalHeldStreamFoldedPass123Bridge
  (pRawCtrl3ExtOn pRawHoistExtOn)
open StageADeconstrCore
  (selDataInAct selDataInAct_apply selMeasInAct selMeasInAct_apply
   selDataInAct_disj_selMeasInAct)
open StageAPointPhase128OnStep (activeTwoElecForestFullQftStage128)
open LocalStageAPointPhase128OnStep
  (activeTwoElecForestFullQftStage128_tCost)
open ForestQft117BundleNoTopBridge
  (dCanonStage128Fwd dCanonStage128Inv count_dCanonStage128Fwd_toff count_dCanonStage128Inv_toff
   count_dCanonStage128Fwd_t count_dCanonStage128Inv_t
   dCanonStage128Fwd_realizes dCanonStage128Inv_realizes)
open Slot0SubAdd14And217Stream
  (dSubSlot0FromSum42 dAddSubSlot0Sum42_counts dAddSubSlot0Sum42_realizesPair)
open ElecHadTrueSwapLocalCompClosure (uLensSwap)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 restrictOfCommSlot0)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (rSlot0InCore rDataSubstSlot0 rDataSubstSlot0_apply_slot0 rDataSubstSlot0_disj_of_disj
   E_anchorLoc)
open StageBTwoElecQftStream218Inner
  (posCoreWires_eq_4034 rCoreInActB42 rCoreInActB42_apply rElec0InActB42 rElec0InActB42_apply
   rPartner18InActB42 rPartner18InActB42_apply rCatSlot0Partner
   selCoreInCoreSum42PG7 selPG7InCoreSum42PG7)
open LocalStageBTwoElecQftStream218Inner
  (selSum42InCoreSum42PG7 selSum42InCoreSum42PG7_disj_selCore
   selPG7InCoreSum42PG7_disj_selCore selSum42InCoreSum42PG7_disj_selPG7
   rSum42InActB42 rSum42InActB42_apply rElec0InActB42_disj_rSum42InActB42
   rPartner18InActB42_disj_rSum42InActB42 rCoreInActB42_disj_rPartner18InActB42
   uElec18Sum42Add uStageBTwoElecStreamInner)
open LocalMidUnitaryConjZeroRoot (rCoreSwapPG3Sum42PG7Full)
open LocalStageBCachedTrueSwapIdle
  (rCtrl3IdleFull rWorkCtrl3Idle rCoreSwapPG3Sum42PG7Full_disj_rCtrl3IdleFull)
open LocalStageBPartnerTrueSwapStream218Closure
  (uStageBFull rCoreSwapPG3Sum42PG7Full_disj_rExt6IdleFull
   restrictOfCommSlot0_eq_of_intertwine restrictOfCommSlot0_mul)
open LocalStageBFastInnerPartnerShift
  (dAddTwoElec36ToSum42 dAddSubTwoElec36Sum42_counts dAddSubTwoElec36Sum42_realizesPair
   embed_uTwoElec36Sum42Add_eq_mul
   p3_qreg_ext basisOutcomeProjector_zero_eq_of_bij kStageBData
   kStageBData_eq_4083 shiftedPartnerCoreLens218 shiftedPartnerLens218
   P_slot0_shiftedPartnerLens218_eq dShiftedPartnerCore
   selCoreInDataAnchor selCoreInDataAnchor_val_eq selDataAnchorSubst selDataAnchorSubst_apply
   selSubstWithPartner uAnchorInner uAnchorInner_comm_P_slot0_shiftedPartner
   uAnchorStageBStream218PG7 liftDataMeas embedUnitary_liftDataMeas_uLensSwap
   concat_compose_liftDataMeas liftDataMeas_rCoreSwapPG3Sum42PG7Full_uAnchorStageBStream218PG7
   uAnchorTrueSwapFull uBarrelFastOnActFull uAnchorFrame uAnchorFrame_eq_p3_01
   rCtrl3IdleFull_projZero_comm_anchorSwap_and_barrel
   rExt6IdleFull_projZero_comm_anchorSwap_and_barrel
   rWorkCtrl3Idle_projZero_mul_pRawCtrl3ExtOn rWorkGuardExt_projZero_mul_pRawHoistExtOn
   E_anchor_ctrl11_eq E_anchor_cat11_eq)
open BoothOpt_StageBPartnerCoreShave
  (actPreservesShifted17_mul selShiftedIdx17 rShiftedIdx17OfFin
   orbitSandAnchorBoothOptBaseT dOrbitSandAnchorBoothOptDyn count_dOrbitSandAnchorBoothOptDyn_toff
   count_dOrbitSandAnchorBoothOptDyn_t_le_exact dOrbitSandAnchorBoothOptDyn_realizes)
open BoothOpt_P4_10_TwoLoadHeldRowTrueSwap
  (Elec3924Preserved elec3924Preserved_mul elec3924Preserved_of_disjoint_embed
   ActPreservesShifted17)
open TwoLoadStageBCircuits
  (selSubstWithPartner_val_ge_posCoreWires rElecInAct_selCoreInDataAnchor_val
   elec3924Preserved_uAnchorInner actPreservesShifted17_uAnchorInner
   restrictOfCommSlot0_p410_eq_fused)

theorem posCoreWires_eq_fullSysCoreWires80 :
    posCoreWires = fullSysCoreWires 80 := rfl

noncomputable def uAdd0InActB42 : Unitary (2 ^ (kStageBData + 18)) :=
  (rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42).embedUnitary
    uElec18Sum42Add

theorem rAdd0InActB42_range (t : Fin (18 + 42)) :
    ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42) t).val < 18 ∨
      posCoreWires ≤
        ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42) t).val := by
  have h4034 := posCoreWires_eq_4034
  refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) t
  · left
    rw [QRegister.concat_apply_left, rElec0InActB42_apply]
    exact q.isLt
  · right
    rw [QRegister.concat_apply_right, rSum42InActB42_apply]
    omega

theorem selSubstWithPartner_uAdd0InActB42_comm_P_slot0 :
    (selSubstWithPartner.embedUnitary uAdd0InActB42).1 *
      P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) =
    P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) *
      (selSubstWithPartner.embedUnitary uAdd0InActB42).1 := by
  let s := rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42
  let rCoreOrig := (selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor
  have hCoreOrig_val : ∀ k : Fin posCoreWires, (rCoreOrig k).val = k.val := fun k ↦ by
    simp [rCoreOrig, selCoreInDataAnchor, selDataInAct_apply,
      selCoreInCoreSum42PG7]
  have hDisj : (selSubstWithPartner.compose s).DisjointWires rCoreOrig := by
    rw [QRegister.disjoint_iff]
    intro t k h
    have hv := congrArg Fin.val h
    rw [QRegister.compose_apply, hCoreOrig_val k] at hv
    have hge := selSubstWithPartner_val_ge_posCoreWires (s t) (rAdd0InActB42_range t)
    have hk := k.isLt
    omega
  unfold uAdd0InActB42
  rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      P_slot0_shiftedPartnerLens218_eq]
  exact QRegister.embedMatrix_comm_of_disjoint _ rCoreOrig hDisj uElec18Sum42Add.1 _

theorem elec3924Preserved_selSubst_uAdd0InActB42 :
    Elec3924Preserved selCoreInDataAnchor (selSubstWithPartner.embedUnitary uAdd0InActB42) := by
  let s := rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42
  unfold uAdd0InActB42
  rw [← QRegister.embedUnitary_compose]
  refine elec3924Preserved_of_disjoint_embed selCoreInDataAnchor (selSubstWithPartner.compose s)
    ?_ uElec18Sum42Add
  rw [QRegister.disjoint_iff]
  intro t i h
  have h4034 := posCoreWires_eq_4034
  have hv := congrArg Fin.val h
  rw [QRegister.compose_apply, rElecInAct_selCoreInDataAnchor_val i] at hv
  have hge := selSubstWithPartner_val_ge_posCoreWires (s t) (rAdd0InActB42_range t)
  have hi := i.isLt
  omega

theorem actPreservesShifted17_selSubst_uAdd0InActB42 :
    ActPreservesShifted17 selCoreInDataAnchor
      (selSubstWithPartner.embedUnitary uAdd0InActB42) := by
  let s := rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42
  let sel17 := (BoothOpt_StageBPartnerCoreShave.selDataInAct (kStageBData + 18)).compose
    (selShiftedIdx17 selCoreInDataAnchor)
  have hSel17_lt : ∀ i : Fin 17, (sel17 i).val < posCoreWires := fun i ↦ by
    dsimp only [sel17, selShiftedIdx17, QRegister.compose_apply]
    rw [BoothOpt_StageBPartnerCoreShave.selDataInAct_apply, Fin.val_castAdd,
      selCoreInDataAnchor_val_eq]
    exact (rShiftedIdx17OfFin i).isLt
  intro xy y hnz
  rw [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractIndex_compose_eq,
      BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractIndex_compose_eq]
  unfold uAdd0InActB42 at hnz
  rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      QRegister.embedMatrix_apply] at hnz
  split_ifs at hnz with henv
  · apply (basisBits 17).injective
    funext i
    change basisBits 17 (sel17.extractIndex y) i = basisBits 17 (sel17.extractIndex xy) i
    rw [sel17.basisBits_extractIndex, sel17.basisBits_extractIndex]
    exact (((selSubstWithPartner.compose s).basisSplit_environment_eq_iff y xy).mp henv)
      (sel17 i) fun ⟨t, ht⟩ ↦
        Nat.not_lt.mpr (selSubstWithPartner_val_ge_posCoreWires (s t) (rAdd0InActB42_range t))
          (congrArg Fin.val ht ▸ hSel17_lt i)
  · exact absurd (mul_zero _) hnz


def selAncSum42InDA : QRegister (18 + 42) (kStageBData + 18) :=
  (selMeasInAct kStageBData).concat ((selDataInAct kStageBData).compose selSum42InCoreSum42PG7)
    (QRegExt.disjointWires_symm ((selDataInAct_disj_selMeasInAct kStageBData).compose_left
      selSum42InCoreSum42PG7))

noncomputable def uAdd0AncPG7 : Unitary (2 ^ (kStageBData + 18)) :=
  selAncSum42InDA.embedUnitary uElec18Sum42Add

theorem selSubstWithPartner_uAdd0InActB42_eq_selDataInAct_uAdd0AncPG7 :
    selSubstWithPartner.embedUnitary uAdd0InActB42 =
      (selDataInAct (kStageBData + 18)).embedUnitary uAdd0AncPG7 := by
  unfold uAdd0InActB42 uAdd0AncPG7
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
  refine congrArg (fun r : QRegister (18 + 42) ((kStageBData + 18) + 18) ↦
    r.embedUnitary uElec18Sum42Add) ?_
  apply p3_qreg_ext
  intro idx
  rw [QRegister.compose_apply, QRegister.compose_apply]
  refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) idx
  · rw [QRegister.concat_apply_left, selAncSum42InDA, QRegister.concat_apply_left]
    have h4083 := kStageBData_eq_4083
    have hq := q.isLt
    have hCast : (rElec0InActB42 q : Fin (kStageBData + 18)) =
        Fin.castAdd 18 ⟨q.val, by omega⟩ :=
      Fin.ext (rElec0InActB42_apply q)
    erw [hCast, selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply]
    apply Fin.ext
    simp [selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply, hq, selMeasInAct_apply]
  · rw [QRegister.concat_apply_right, selAncSum42InDA, QRegister.concat_apply_right]
    have h4034 := posCoreWires_eq_4034
    have h4083 := kStageBData_eq_4083
    have hsLt := s.isLt
    have hCast : (rSum42InActB42 s : Fin (kStageBData + 18)) =
        Fin.castAdd 18 ⟨posCoreWires + s.val, by omega⟩ :=
      Fin.ext (rSum42InActB42_apply s)
    erw [hCast, selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
      QRegister.compose_apply]
    apply Fin.ext
    have hge : ¬ posCoreWires + s.val < 18 := by omega
    simp only [selDataInAct_apply, Fin.val_castAdd,
      Function.Embedding.coeFn_mk,
      Fin.val_castLE, Fin.val_natAdd, zero_add]
    erw [selDataAnchorSubst_apply]
    rw [ite_eq_right hge]


theorem selCoreInDataAnchor_disj_selAncSum42InDA :
    selCoreInDataAnchor.DisjointWires selAncSum42InDA := by
  have h4034 := posCoreWires_eq_4034
  have h4083 := kStageBData_eq_4083
  rw [QRegister.disjoint_iff]
  intro i j
  have hi := i.isLt
  refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) j
  · intro h
    have hv := congrArg Fin.val h
    rw [selCoreInDataAnchor_val_eq, selAncSum42InDA, QRegister.concat_apply_left,
        selMeasInAct_apply, Fin.val_natAdd] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    have hsVal : (selSum42InCoreSum42PG7 s).val = posCoreWires + s.val := by
      simp [selSum42InCoreSum42PG7]
    rw [selCoreInDataAnchor_val_eq, selAncSum42InDA, QRegister.concat_apply_right,
        QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd, hsVal] at hv
    omega


theorem rCoreSwapPG3Sum42PG7Full_selSum42 (off : ℕ) (hoff : off + 3 ≤ 41) (s : Fin 42) :
    rCoreSwapPG3Sum42PG7Full off hoff (selSum42InCoreSum42PG7 s) = rSum0 s := by
  have hs : selSum42InCoreSum42PG7 s = Fin.castAdd 7 (Fin.natAdd (fullSysCoreWires 80) s) := by
    ext
    simp [selSum42InCoreSum42PG7, posCoreWires_eq_fullSysCoreWires80]
  rw [hs, rCoreSwapPG3Sum42PG7Full, QRegister.concat_apply_left, QRegister.concat_apply_right]

theorem liftDataMeas_rCoreSwapPG3Sum42PG7Full_uAdd0AncPG7
    (off : ℕ) (hoff : off + 3 ≤ 41) :
    (liftDataMeas (rCoreSwapPG3Sum42PG7Full off hoff)).embedUnitary uAdd0AncPG7 =
      uAdd0AncFull18 := by
  let rSw : QRegister kStageBData kFull80 := rCoreSwapPG3Sum42PG7Full off hoff
  change (liftDataMeas rSw).embedUnitary uAdd0AncPG7 = uAdd0AncFull18
  unfold uAdd0AncPG7 uAdd0AncFull18
  rw [← QRegister.embedUnitary_compose]
  refine congrArg (·.embedUnitary uElec18Sum42Add) (p3_qreg_ext fun idx ↦ ?_)
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) idx
  · rw [selAncSum42InDA, QRegister.concat_apply_left,
        selAncSum0InFull18, QRegister.concat_apply_left]
    have hq : selMeasInAct kStageBData q = Fin.natAdd kStageBData q :=
      selMeasInAct_apply q
    rw [hq, liftDataMeas, QRegister.concat_apply_right]
  · rw [selAncSum42InDA, QRegister.concat_apply_right, QRegister.compose_apply,
        selAncSum0InFull18, QRegister.concat_apply_right, QRegister.compose_apply]
    have hs : selDataInAct kStageBData (selSum42InCoreSum42PG7 s) =
        Fin.castAdd 18 (selSum42InCoreSum42PG7 s) :=
      selDataInAct_apply _
    rw [hs, liftDataMeas, QRegister.concat_apply_left, QRegister.compose_apply]
    exact congrArg (selDataInAct kFull80) (rCoreSwapPG3Sum42PG7Full_selSum42 off hoff s)

theorem compose_selAncSum0InFull18_eq {n : ℕ}
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n)
    (hAA : rAct.DisjointWires rAnchor18) :
    (rAct.concat rAnchor18 hAA).compose selAncSum0InFull18 =
      rAnchor18.concat (rAct.compose rSum0) (QRegExt.disjointWires_symm (hAA.compose_left rSum0)) :=
        by
  apply p3_qreg_ext
  intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) idx
  · rw [selAncSum0InFull18, QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hq : selMeasInAct kFull80 q = Fin.natAdd kFull80 q := selMeasInAct_apply q
    rw [hq, QRegister.concat_apply_right]
  · rw [selAncSum0InFull18, QRegister.concat_apply_right, QRegister.compose_apply,
        QRegister.concat_apply_right, QRegister.compose_apply]
    have hs : selDataInAct kFull80 (rSum0 s) = Fin.castAdd 18 (rSum0 s) :=
      selDataInAct_apply _
    rw [hs, QRegister.concat_apply_left]


section Part3A_OpenQftInner

open FullSysCatSegmentBridge (coreElecCosetB1Block)
open PosSlots24SemanticBridge (pos24_6_le_80)
open InterWalkRSum42Hoist (qreg_ext)
open _root_.QuantumComputation.Specs.StoppingPowerSolution.DyadicQft64 (IntertwinesCatOp)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6 uCoreHadamard18)
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix axisProdPrefix)
open DyadicQft64WalkCircuit (rAxis654)
open DyadicQft64WalkCircuit288 (mulVec_col0_eq_phaseGradKet7)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (U_cat_B_normalized_col_zero_singleCat)
open StageAPointPhase128OnStep (hL3_le_654)
open FullConcrete7StepAndTrueSwapSelect (kCoreSum42PG7 selCatInCoreSum42PG7)
open StageAConjHAndStreamBridge
  (activeOneElecExpQftStage128 activeOneElecExpQftStage128_tCost activeOneElecExpQftStage128_uEff)
open MasterZeroHypCompactAndCompactTopBridge (sel25InCat)
open StageADeconstrAndQftShare
  (SupportedOnSel25 supportedOnSel25_activeOneElecExpQftStage128
   selCatInCoreSum42PG7_sel25InCat_val_lt18_or_ge4076)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (rDataSubstSlot0_apply_of_not_mem coreElecCosetB1Block_elec_val)
open StageBTwoElecQftStream218Inner
  (rPG7InActB42 rPG7InActB42_apply)
open LocalStageBTwoElecQftStream218Inner
  (rElec0InActB42_disj_rPG7InActB42 rSum42InActB42_disj_rPG7InActB42
   rPartner18InActB42_disj_rPG7InActB42 uStageBTwoElecStreamInnerEff
   rIdSlot0Partner_embedUnitary_uEff_eq intertwinesCatOp_embed_of_disj intertwinesCatOp_inv
   uStageBTwoElecStreamInner_mul_catState7_eq_zeroHyp)
open LocalStageBPartnerTrueSwapStream218Closure
  (catState7 embedMatrix_catState7_eq)

/-- `(3924 + 3 + 7)`-wire catalyzed QFT selector for Electron `0` + `rPG7`
inside `kStageBData + 18`. -/
def rCat0InActB42 : QRegister (3924 + 3 + 7) (kStageBData + 18) :=
  (selDataInAct kStageBData).compose selCatInCoreSum42PG7

theorem rCoreInActB42_disj_rSum42InActB42_part3a :
    rCoreInActB42.DisjointWires rSum42InActB42 := by
  have h4034 := posCoreWires_eq_4034
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv := congrArg Fin.val h
  rw [rCoreInActB42_apply, rSum42InActB42_apply] at hv
  have := i.isLt
  omega

theorem rCoreInActB42_disj_rPG7InActB42_part3a :
    rCoreInActB42.DisjointWires rPG7InActB42 := by
  have h4034 := posCoreWires_eq_4034
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv := congrArg Fin.val h
  rw [rCoreInActB42_apply, rPG7InActB42_apply] at hv
  have := i.isLt
  omega

/-- Core register inside `kStageBData + 18` with slot `0` (`[0..18)`) replaced by
`rPartner18InActB42`. -/
noncomputable def rCorePartnerInActB42 : QRegister (fullSysCoreWires 80) (kStageBData + 18) :=
  rDataSubstSlot0 rSlot0InCore rCoreInActB42 rPartner18InActB42
    rCoreInActB42_disj_rPartner18InActB42

theorem rCorePartnerInActB42_disj_rSum42InActB42_part3a :
    rCorePartnerInActB42.DisjointWires rSum42InActB42 :=
  rDataSubstSlot0_disj_of_disj rSlot0InCore rCoreInActB42_disj_rPartner18InActB42
    rCoreInActB42_disj_rSum42InActB42_part3a rPartner18InActB42_disj_rSum42InActB42

theorem rCorePartnerInActB42_disj_rPG7InActB42_part3a :
    rCorePartnerInActB42.DisjointWires rPG7InActB42 :=
  rDataSubstSlot0_disj_of_disj rSlot0InCore rCoreInActB42_disj_rPartner18InActB42
    rCoreInActB42_disj_rPG7InActB42_part3a rPartner18InActB42_disj_rPG7InActB42

/-- `(3924 + 3 + 7)`-wire catalyzed QFT selector for `rPartner18` + `rPG7`
inside `kStageBData + 18`. -/
noncomputable def rCatPartnerInActB42 : QRegister (3924 + 3 + 7) (kStageBData + 18) :=
  ((rCorePartnerInActB42.concat rSum42InActB42
      rCorePartnerInActB42_disj_rSum42InActB42_part3a).concat
    rPG7InActB42
    (disjointWires_concat_left rCorePartnerInActB42_disj_rSum42InActB42_part3a
      rCorePartnerInActB42_disj_rPG7InActB42_part3a rSum42InActB42_disj_rPG7InActB42)).compose
    selCatInCoreSum42PG7

/-- Single-electron `activeOneElecExpQftStage128.uCat` embedded on `(rElec0, rPG7)`
in `kStageBData + 18`. -/
noncomputable def uQft0ExpInActB42 : Unitary (2 ^ (kStageBData + 18)) :=
  rCat0InActB42.embedUnitary activeOneElecExpQftStage128.uCat

/-- Single-electron `activeOneElecExpQftStage128.uCat` embedded on `(rPartner18, rPG7)`
in `kStageBData + 18`. -/
noncomputable def uQftPExpInActB42 : Unitary (2 ^ (kStageBData + 18)) :=
  rCatPartnerInActB42.embedUnitary activeOneElecExpQftStage128.uCat

/-- Raw-catalyst Stage-A/B seam unitary `uAdd0 * uQft0Exp⁻¹` inside `kStageBData + 18`. -/
noncomputable def uJunctionRawInActB42 : Unitary (2 ^ (kStageBData + 18)) :=
  uAdd0InActB42 * uQft0ExpInActB42⁻¹

/-- Closed-form catalyzed Stage-B two-electron stream unitary using factored forward QFT
`uQftPExpInActB42 * uQft0ExpInActB42` (`117 T` in Stage B + `117 T` hoisted from Stage A). -/
noncomputable def uStageBOpenQftStreamInner
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    Unitary (2 ^ (kStageBData + 18)) :=
  let uAdd0 :=
    (rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42).embedUnitary
      uElec18Sum42Add
  let uAddP :=
    (rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uQft2 := rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat
  let uSand :=
    (rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42).embedUnitary
      (diagSignUnitary
        (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
          (PosSlots24CompactPhase288.midPhaseBitSpec slot2SwappedTo0
            PosSlots24SemanticBridge.pos24TailSign
            (MidKickSub33.pos24TailMag30MidpointB B hB1 (by omega)))))
  uAdd0 * (uAddP * (uQft2⁻¹ *
    (uSand * ((uQftPExpInActB42 * uQft0ExpInActB42) * (uAddP⁻¹ * uAdd0⁻¹)))))

/-- Wire-range witness for `rCat0InActB42.compose sel25InCat`: every active wire lies in
`[0..18)` (`rElec0`) or `[posCoreWires + 42 .. kStageBData)` (`rPG7`). -/
theorem rCat0InActB42_sel25_range (idx : Fin (18 + 7)) :
    (rCat0InActB42 (sel25InCat idx)).val < 18 ∨
      (posCoreWires + 42 ≤ (rCat0InActB42 (sel25InCat idx)).val ∧
        (rCat0InActB42 (sel25InCat idx)).val < kStageBData) := by
  have hSub := selCatInCoreSum42PG7_sel25InCat_val_lt18_or_ge4076 idx
  have hLt : (selCatInCoreSum42PG7 (sel25InCat idx)).val < kStageBData :=
    (selCatInCoreSum42PG7 (sel25InCat idx)).isLt
  have hVal : (rCat0InActB42 (sel25InCat idx)).val =
      (selCatInCoreSum42PG7 (sel25InCat idx)).val := by
    rw [rCat0InActB42, QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd]
    rfl
  have hCoreEq : fullSysCoreWires 80 = posCoreWires := rfl
  rcases hSub with h0 | hPG
  · left
    omega
  · right
    omega


private theorem uQft0ExpInActB42_comm_uAddP_inv_part3a :
    let uAddP :=
      (rPartner18InActB42.concat rSum42InActB42
        rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
    uQft0ExpInActB42 * uAddP⁻¹ = uAddP⁻¹ * uQft0ExpInActB42 := by
  intro uAddP
  let rOther := rPartner18InActB42.concat rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  have hDisj : (rCat0InActB42.compose sel25InCat).DisjointWires rOther := by
    have h4034 := posCoreWires_eq_4034
    have h4083 := kStageBData_eq_4083
    rw [QRegister.disjoint_iff]
    intro idx j
    have hR := rCat0InActB42_sel25_range idx
    refine Fin.addCases (fun q h ↦ ?_) (fun s h ↦ ?_) j
    · have hv := congrArg Fin.val h
      rw [QRegister.compose_apply, QRegister.concat_apply_left, rPartner18InActB42_apply] at hv
      have := q.isLt
      rcases hR with h0 | ⟨_, hLt⟩ <;> omega
    · have hv := congrArg Fin.val h
      rw [QRegister.compose_apply, QRegister.concat_apply_right, rSum42InActB42_apply] at hv
      have := s.isLt
      rcases hR with h0 | ⟨hGe, _⟩ <;> omega
  obtain ⟨c, u25, hU⟩ := supportedOnSel25_activeOneElecExpQftStage128
  apply Subtype.ext
  change uQft0ExpInActB42.1 * (uAddP⁻¹).1 = (uAddP⁻¹).1 * uQft0ExpInActB42.1
  have hE : uQft0ExpInActB42.1 = c • ((rCat0InActB42.compose sel25InCat).embedUnitary u25).1 := by
    unfold uQft0ExpInActB42
    rw [QRegister.embedUnitary_val, hU, rCat0InActB42.embedMatrix_smul,
        QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, QRegister.embedUnitary_val]
  have hA : (uAddP⁻¹).1 = rOther.embedMatrix (uElec18Sum42Add⁻¹).1 := by
    have hInv : uAddP⁻¹ = rOther.embedUnitary uElec18Sum42Add⁻¹ :=
      inv_eq_of_mul_eq_one_left
        (by rw [← rOther.embedUnitary_mul, inv_mul_cancel, rOther.embedUnitary_one])
    rw [hInv, QRegister.embedUnitary_val]
  rw [hE, hA, Matrix.smul_mul, Matrix.mul_smul, QRegister.embedUnitary_val,
      (rCat0InActB42.compose sel25InCat).embedMatrix_comm_of_disjoint rOther hDisj u25.1 _]

private theorem uStageBOpenQftStreamInner_mul_uJunctionRawInActB42_e
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    let uAdd0 :=
      (rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42).embedUnitary
        uElec18Sum42Add
    let uAddP :=
      (rPartner18InActB42.concat rSum42InActB42
        rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
    let uQft2 := rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat
    let uSand :=
      (rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42).embedUnitary
        (diagSignUnitary
          (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
            (PosSlots24CompactPhase288.midPhaseBitSpec slot2SwappedTo0
              PosSlots24SemanticBridge.pos24TailSign
              (MidKickSub33.pos24TailMag30MidpointB B hB1 (by omega)))))
    uAdd0 * (uAddP * (uQft2⁻¹ * (uSand * (uQftPExpInActB42 * uAddP⁻¹)))) =
      uStageBOpenQftStreamInner B hB1 hB27 slot2SwappedTo0 * uJunctionRawInActB42 := by
  intro uAdd0 uAddP uQft2 uSand
  have hC : uQft0ExpInActB42 * uAddP⁻¹ = uAddP⁻¹ * uQft0ExpInActB42 :=
    uQft0ExpInActB42_comm_uAddP_inv_part3a
  have hTail :
      ((uQftPExpInActB42 * uQft0ExpInActB42) * (uAddP⁻¹ * uAdd0⁻¹)) *
        (uAdd0 * uQft0ExpInActB42⁻¹) =
      uQftPExpInActB42 * uAddP⁻¹ := by
    calc ((uQftPExpInActB42 * uQft0ExpInActB42) * (uAddP⁻¹ * uAdd0⁻¹)) *
          (uAdd0 * uQft0ExpInActB42⁻¹)
        = uQftPExpInActB42 * (uQft0ExpInActB42 * uAddP⁻¹) *
            (uAdd0⁻¹ * uAdd0) * uQft0ExpInActB42⁻¹ := by
            simp only [_root_.mul_assoc]
      _ = uQftPExpInActB42 * (uAddP⁻¹ * uQft0ExpInActB42) * uQft0ExpInActB42⁻¹ := by
            rw [hC, inv_mul_cancel, mul_one]
      _ = (uQftPExpInActB42 * uAddP⁻¹) * (uQft0ExpInActB42 * uQft0ExpInActB42⁻¹) := by
            simp only [_root_.mul_assoc]
      _ = uQftPExpInActB42 * uAddP⁻¹ := by
            rw [mul_inv_cancel, mul_one]
  unfold uStageBOpenQftStreamInner uJunctionRawInActB42 uAdd0InActB42
  dsimp only
  calc uAdd0 * (uAddP * (uQft2⁻¹ * (uSand * (uQftPExpInActB42 * uAddP⁻¹))))
      = uAdd0 * (uAddP * (uQft2⁻¹ * (uSand *
          (((uQftPExpInActB42 * uQft0ExpInActB42) * (uAddP⁻¹ * uAdd0⁻¹)) *
            (uAdd0 * uQft0ExpInActB42⁻¹))))) := by
          rw [hTail]
    _ = (uAdd0 * (uAddP * (uQft2⁻¹ * (uSand *
          ((uQftPExpInActB42 * uQft0ExpInActB42) * (uAddP⁻¹ * uAdd0⁻¹)))))) *
          (uAdd0 * uQft0ExpInActB42⁻¹) := by
          simp only [_root_.mul_assoc]

/-- Open-QFT 5-step Stage-B inner two-electron stream on `rData : QRegister kStageBData n`:
replaces `dCanonStage128Fwd activeTwoElecForestFullQftStage128` (`221 T` on `rCat`) by
single-electron partner QFT `dCanonStage128Fwd activeOneElecExpQftStage128` (`117 T` on
`rCatPartner`, `0 TOFF`). -/
noncomputable def dStageBTwoElecStreamInnerOpenQftOnData {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rData : QRegister kStageBData n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hDP : rData.DisjointWires rPartner18)
    (hDO : rData.DisjointWires rOrbit16) (hDC : rData.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16) (hPC : rPartner18.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  let rCore : QRegister (fullSysCoreWires 80) n := rData.compose selCoreInCoreSum42PG7
  let rSum42 := rData.compose selSum42InCoreSum42PG7
  let rPG7 := rData.compose selPG7InCoreSum42PG7
  let hCS : rCore.DisjointWires rSum42 :=
    disjointWires_compose_of_disjoint rData (QRegExt.disjointWires_symm
      selSum42InCoreSum42PG7_disj_selCore)
  let hCG : rCore.DisjointWires rPG7 :=
    disjointWires_compose_of_disjoint rData (QRegExt.disjointWires_symm
      selPG7InCoreSum42PG7_disj_selCore)
  let hSG : rSum42.DisjointWires rPG7 :=
    disjointWires_compose_of_disjoint rData selSum42InCoreSum42PG7_disj_selPG7
  let rWork : QRegister (16 + mClean) n := rOrbit16.concat rClean hOC
  let hCW : rCore.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hSW : rSum42.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hGW : rPG7.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hPW : rPartner18.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm hPO)
      (QRegExt.disjointWires_symm hPC)))
  let hCS_G : (rCore.concat rSum42 hCS).DisjointWires rPG7 :=
    disjointWires_concat_left hCS hCG hSG
  let rData0 := (rCore.concat rSum42 hCS).concat rPG7 hCS_G
  let hData0_P : rData0.DisjointWires rPartner18 :=
    disjointWires_concat_left hCS_G
      (disjointWires_concat_left hCS (hDP.compose_left _) (hDP.compose_left _))
      (hDP.compose_left _)
  let rAct := rData0.concat rPartner18 hData0_P
  let hAct_W : rAct.DisjointWires rWork :=
    disjointWires_concat_left hData0_P
      (disjointWires_concat_left hCS_G (disjointWires_concat_left hCS hCW hSW) hGW) hPW
  let rCat := rAct.compose rCatSlot0Partner
  let hCatW : rCat.DisjointWires rWork := hAct_W.compose_left rCatSlot0Partner
  let rCorePartner : QRegister (fullSysCoreWires 80) n :=
    rDataSubstSlot0 rSlot0InCore rCore rPartner18 (hDP.compose_left _)
  let hCPS : rCorePartner.DisjointWires rSum42 :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCS (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hCPG : rCorePartner.DisjointWires rPG7 :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCG (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hCPW : rCorePartner.DisjointWires rWork :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCW hPW
  let hCPS_G : (rCorePartner.concat rSum42 hCPS).DisjointWires rPG7 :=
    disjointWires_concat_left hCPS hCPG hSG
  let rCatPartner :=
    ((rCorePartner.concat rSum42 hCPS).concat rPG7 hCPS_G).compose selCatInCoreSum42PG7
  let hCatPartnerW : rCatPartner.DisjointWires rWork :=
    (disjointWires_concat_left hCPS_G (disjointWires_concat_left hCPS hCPW hSW) hGW).compose_left
      selCatInCoreSum42PG7
  let hE0P : (rElecSlot rCore 0).DisjointWires rPartner18 :=
    (hDP.compose_left _).compose_left _
  let rTwo36 := (rElecSlot rCore 0).concat rPartner18 hE0P
  let hTwoS : rTwo36.DisjointWires rSum42 :=
    disjointWires_concat_left hE0P (hCS.compose_left _) (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hTwoW : rTwo36.DisjointWires rWork :=
    disjointWires_concat_left hE0P (hCW.compose_left _) hPW
  .seq (dSubSlot0FromSum42 (mPayload := 80) v rCorePartner rSum42 rWork
          hCPS hCPW hSW (by omega : 13 ≤ 16 + mClean))
    (.seq (dCanonStage128Fwd activeOneElecExpQftStage128
            (by omega : 128 ≤ 16 + mClean) v rCatPartner rWork hCatPartnerW)
      (.seq (dOrbitSandAnchorBoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v
              rCore rPartner18 rOrbit16 rClean
              (hDP.compose_left _) (hDO.compose_left _) (hDC.compose_left _) hPO hPC hOC)
        (.seq (dCanonStage128Inv activeTwoElecForestFullQftStage128
                (by omega : 128 ≤ 16 + mClean) v rCat rWork hCatW)
          (dAddTwoElec36ToSum42 v rTwo36 rSum42 rWork hTwoS hTwoW hSW
            (by omega : 18 ≤ 16 + mClean)))))

theorem count_dStageBTwoElecStreamInnerOpenQftOnData_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rData : QRegister kStageBData n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hDP : rData.DisjointWires rPartner18)
    (hDO : rData.DisjointWires rOrbit16) (hDC : rData.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16) (hPC : rPartner18.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (dStageBTwoElecStreamInnerOpenQftOnData B hB6 hB27 hmClean slot2SwappedTo0 v
      rData rPartner18 rOrbit16 rClean hDP hDO hDC hPO hPC hOC).count TOFF = 0 := by
  unfold dStageBTwoElecStreamInnerOpenQftOnData
  let rCore : QRegister (fullSysCoreWires 80) n := rData.compose selCoreInCoreSum42PG7
  let rSum42 := rData.compose selSum42InCoreSum42PG7
  let rWork : QRegister (16 + mClean) n := rOrbit16.concat rClean hOC
  let hCS : rCore.DisjointWires rSum42 :=
    disjointWires_compose_of_disjoint rData (QRegExt.disjointWires_symm
      selSum42InCoreSum42PG7_disj_selCore)
  let hCW : rCore.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hSW : rSum42.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hPW : rPartner18.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm hPO)
      (QRegExt.disjointWires_symm hPC)))
  let rCorePartner : QRegister (fullSysCoreWires 80) n :=
    rDataSubstSlot0 rSlot0InCore rCore rPartner18 (hDP.compose_left _)
  let hCPS : rCorePartner.DisjointWires rSum42 :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCS (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hCPW : rCorePartner.DisjointWires rWork :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCW hPW
  let hE0P : (rElecSlot rCore 0).DisjointWires rPartner18 :=
    (hDP.compose_left _).compose_left _
  let rTwo36 := (rElecSlot rCore 0).concat rPartner18 hE0P
  let hTwoS : rTwo36.DisjointWires rSum42 :=
    disjointWires_concat_left hE0P (hCS.compose_left _) (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hTwoW : rTwo36.DisjointWires rWork :=
    disjointWires_concat_left hE0P (hCW.compose_left _) hPW
  have cSub := dAddSubSlot0Sum42_counts (Var := Var) (mPayload := 80) v
    rCorePartner rSum42 rWork hCPS hCPW hSW (by omega : 13 ≤ 16 + mClean)
  have cTwo := dAddSubTwoElec36Sum42_counts (Var := Var) v
    rTwo36 rSum42 rWork hTwoS hTwoW hSW (by omega : 18 ≤ 16 + mClean)
  dsimp only [rCorePartner, rTwo36, rCore, rSum42, rWork] at cSub cTwo
  simp only [DynamicCircuit.count, count_dCanonStage128Fwd_toff, count_dCanonStage128Inv_toff,
    count_dOrbitSandAnchorBoothOptDyn_toff]
  have h1 := cSub.2.1
  have h2 := cTwo.1
  omega

theorem count_dStageBTwoElecStreamInnerOpenQftOnData_t_le {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rData : QRegister kStageBData n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hDP : rData.DisjointWires rPartner18)
    (hDO : rData.DisjointWires rOrbit16) (hDC : rData.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16) (hPC : rPartner18.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (dStageBTwoElecStreamInnerOpenQftOnData B hB6 hB27 hmClean slot2SwappedTo0 v
      rData rPartner18 rOrbit16 rClean hDP hDO hDC hPO hPC hOC).count T ≤
      710 + orbitSandAnchorBoothOptBaseT B mClean + 260 * B := by
  unfold dStageBTwoElecStreamInnerOpenQftOnData
  let rCore : QRegister (fullSysCoreWires 80) n := rData.compose selCoreInCoreSum42PG7
  let rSum42 := rData.compose selSum42InCoreSum42PG7
  let rWork : QRegister (16 + mClean) n := rOrbit16.concat rClean hOC
  let hCS : rCore.DisjointWires rSum42 :=
    disjointWires_compose_of_disjoint rData (QRegExt.disjointWires_symm
      selSum42InCoreSum42PG7_disj_selCore)
  let hCW : rCore.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hSW : rSum42.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hPW : rPartner18.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm hPO)
      (QRegExt.disjointWires_symm hPC)))
  let rCorePartner : QRegister (fullSysCoreWires 80) n :=
    rDataSubstSlot0 rSlot0InCore rCore rPartner18 (hDP.compose_left _)
  let hCPS : rCorePartner.DisjointWires rSum42 :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCS (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hCPW : rCorePartner.DisjointWires rWork :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCW hPW
  let hE0P : (rElecSlot rCore 0).DisjointWires rPartner18 :=
    (hDP.compose_left _).compose_left _
  let rTwo36 := (rElecSlot rCore 0).concat rPartner18 hE0P
  let hTwoS : rTwo36.DisjointWires rSum42 :=
    disjointWires_concat_left hE0P (hCS.compose_left _) (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hTwoW : rTwo36.DisjointWires rWork :=
    disjointWires_concat_left hE0P (hCW.compose_left _) hPW
  have cSub := dAddSubSlot0Sum42_counts (Var := Var) (mPayload := 80) v
    rCorePartner rSum42 rWork hCPS hCPW hSW (by omega : 13 ≤ 16 + mClean)
  have cTwo := dAddSubTwoElec36Sum42_counts (Var := Var) v
    rTwo36 rSum42 rWork hTwoS hTwoW hSW (by omega : 18 ≤ 16 + mClean)
  have cSand := count_dOrbitSandAnchorBoothOptDyn_t_le_exact B hB6 hB27 hmClean slot2SwappedTo0 v
    rCore rPartner18 rOrbit16 rClean (hDP.compose_left _) (hDO.compose_left _)
    (hDC.compose_left _) hPO hPC hOC
  dsimp only [rCorePartner, rTwo36, rCore, rSum42, rWork] at cSub cTwo cSand
  simp only [DynamicCircuit.count, count_dCanonStage128Fwd_t, count_dCanonStage128Inv_t,
    activeOneElecExpQftStage128_tCost, activeTwoElecForestFullQftStage128_tCost]
  have h1 := cSub.2.2.2
  have h2 := cTwo.2.2.1
  omega

theorem dStageBTwoElecStreamInnerOpenQftOnData_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rData : QRegister kStageBData n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hDP : rData.DisjointWires rPartner18)
    (hDO : rData.DisjointWires rOrbit16) (hDC : rData.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16) (hPC : rPartner18.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.concat rPartner18 hDP)
      (rOrbit16.concat rClean hOC)
      (uStageBOpenQftStreamInner B (by omega) hB27 slot2SwappedTo0 * uJunctionRawInActB42)
      (dStageBTwoElecStreamInnerOpenQftOnData B hB6 hB27 hmClean slot2SwappedTo0 v
        rData rPartner18 rOrbit16 rClean hDP hDO hDC hPO hPC hOC) := by
  let rCore : QRegister (fullSysCoreWires 80) n := rData.compose selCoreInCoreSum42PG7
  let rSum42 := rData.compose selSum42InCoreSum42PG7
  let rPG7 := rData.compose selPG7InCoreSum42PG7
  let hCS : rCore.DisjointWires rSum42 :=
    disjointWires_compose_of_disjoint rData (QRegExt.disjointWires_symm
      selSum42InCoreSum42PG7_disj_selCore)
  let hCG : rCore.DisjointWires rPG7 :=
    disjointWires_compose_of_disjoint rData (QRegExt.disjointWires_symm
      selPG7InCoreSum42PG7_disj_selCore)
  let hSG : rSum42.DisjointWires rPG7 :=
    disjointWires_compose_of_disjoint rData selSum42InCoreSum42PG7_disj_selPG7
  let hCS_G : (rCore.concat rSum42 hCS).DisjointWires rPG7 :=
    disjointWires_concat_left hCS hCG hSG
  let rData0 := (rCore.concat rSum42 hCS).concat rPG7 hCS_G
  let hData0_P : rData0.DisjointWires rPartner18 :=
    disjointWires_concat_left hCS_G
      (disjointWires_concat_left hCS (hDP.compose_left _) (hDP.compose_left _))
      (hDP.compose_left _)
  let rAct := rData0.concat rPartner18 hData0_P
  let rWork : QRegister (16 + mClean) n := rOrbit16.concat rClean hOC
  let hm18 : 18 ≤ 16 + mClean := by omega
  let hm128 : 128 ≤ 16 + mClean := by omega
  let hCW : rCore.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hSW : rSum42.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hGW : rPG7.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm
      (hDO.compose_left _)) (QRegExt.disjointWires_symm (hDC.compose_left _))))
  let hPW : rPartner18.DisjointWires rWork :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left hOC (QRegExt.disjointWires_symm hPO)
      (QRegExt.disjointWires_symm hPC)))
  let hData0_W : rData0.DisjointWires rWork :=
    disjointWires_concat_left hCS_G (disjointWires_concat_left hCS hCW hSW) hGW
  let hAct_W : rAct.DisjointWires rWork := disjointWires_concat_left hData0_P hData0_W hPW
  have hData0Eq : (rData0 : QRegister kStageBData n) = rData := by
    have hCoreEq : fullSysCoreWires 80 = posCoreWires := rfl
    apply p3_qreg_ext
    intro iD
    change ((rCore.concat rSum42 hCS).concat rPG7 hCS_G :
      QRegister (fullSysCoreWires 80 + 42 + 7) n) iD =
      (rData : QRegister kStageBData n) ⟨iD.val, iD.isLt⟩
    refine Fin.addCases (fun iCS ↦ ?_) (fun jG ↦ ?_) iD
    · rw [QRegister.concat_apply_left]
      refine Fin.addCases (fun iC ↦ ?_) (fun jS ↦ ?_) iCS
      · rw [QRegister.concat_apply_left]
        exact congrArg (rData : QRegister kStageBData n)
          (Fin.ext (by simp [selCoreInCoreSum42PG7, QRegister.block, Fin.natAddEmb, Fin.castLEEmb]))
      · rw [QRegister.concat_apply_right]
        exact congrArg (rData : QRegister kStageBData n) (Fin.ext (by
          simp [selSum42InCoreSum42PG7, QRegister.block, Fin.natAddEmb]
          omega))
    · rw [QRegister.concat_apply_right]
      exact congrArg (rData : QRegister kStageBData n) (Fin.ext (by
        simp [selPG7InCoreSum42PG7, QRegister.block, Fin.natAddEmb]
        omega))
  have hActEq : (rAct : QRegister (kStageBData + 18) n) = rData.concat rPartner18 hDP := by
    apply p3_qreg_ext
    intro idx
    change (rData0 : QRegister kStageBData n).concat rPartner18 hData0_P idx =
      (rData.concat rPartner18 hDP) idx
    simp only [hData0Eq]
    rfl
  have hCompCore : rAct.compose rCoreInActB42 = rCore := by
    rw [hActEq]
    apply p3_qreg_ext
    intro i
    rw [QRegister.compose_apply]
    have hSel : rCoreInActB42 i = Fin.castAdd 18 (selCoreInCoreSum42PG7 i) := by
      apply Fin.ext
      rw [rCoreInActB42_apply]
      simp [selCoreInCoreSum42PG7, QRegister.block]
    erw [hSel, QRegister.concat_apply_left]
    rfl
  have hCompSum42 : rAct.compose rSum42InActB42 = rSum42 := by
    rw [hActEq]
    apply p3_qreg_ext
    intro i
    rw [QRegister.compose_apply]
    have hSel : rSum42InActB42 i = Fin.castAdd 18 (selSum42InCoreSum42PG7 i) := by
      apply Fin.ext
      rw [rSum42InActB42_apply]
      simp [selSum42InCoreSum42PG7, QRegister.block]
    erw [hSel, QRegister.concat_apply_left]
    rfl
  have hCompPG7 : rAct.compose rPG7InActB42 = rPG7 := by
    rw [hActEq]
    apply p3_qreg_ext
    intro i
    rw [QRegister.compose_apply]
    have hSel : rPG7InActB42 i = Fin.castAdd 18 (selPG7InCoreSum42PG7 i) := by
      apply Fin.ext
      rw [rPG7InActB42_apply]
      simp [selPG7InCoreSum42PG7, QRegister.block]
    erw [hSel, QRegister.concat_apply_left]
    rfl
  have hCompPartner : rAct.compose rPartner18InActB42 = rPartner18 := by
    rw [hActEq]
    apply p3_qreg_ext
    intro i
    rw [QRegister.compose_apply]
    have hSel : rPartner18InActB42 i = Fin.natAdd kStageBData i :=
      Fin.ext (rPartner18InActB42_apply i)
    erw [hSel, QRegister.concat_apply_right]
  have hCompE0 : rAct.compose rElec0InActB42 = rElecSlot rCore 0 := by
    rw [rElec0InActB42, ← QRegister.compose_assoc, hCompCore]
    apply p3_qreg_ext
    intro _
    rfl
  have hConcatEq : ∀ {k₁ k₂ : ℕ} (s₁ : QRegister k₁ (kStageBData + 18))
      (s₂ : QRegister k₂ (kStageBData + 18)) (hs : s₁.DisjointWires s₂)
      (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (hr : r₁.DisjointWires r₂)
      (he₁ : rAct.compose s₁ = r₁) (he₂ : rAct.compose s₂ = r₂),
      r₁.concat r₂ hr = rAct.compose (s₁.concat s₂ hs) := by
    intro k₁ k₂ s₁ s₂ hs r₁ r₂ hr he₁ he₂
    apply p3_qreg_ext
    intro idx
    rw [QRegister.compose_apply]
    refine Fin.addCases (fun i₁ ↦ ?_) (fun i₂ ↦ ?_) idx
    · rw [QRegister.concat_apply_left, QRegister.concat_apply_left, ← he₁, QRegister.compose_apply]
    · rw [QRegister.concat_apply_right, QRegister.concat_apply_right, ← he₂,
          QRegister.compose_apply]
  have hInvEmbed : ∀ {k : ℕ} (sel : QRegister k (kStageBData + 18)) (U : Unitary (2 ^ k)),
      sel.embedUnitary U⁻¹ = (sel.embedUnitary U)⁻¹ := fun sel U ↦
    (inv_eq_of_mul_eq_one_left
      (by rw [← sel.embedUnitary_mul, inv_mul_cancel, sel.embedUnitary_one])).symm
  let rCorePartner : QRegister (fullSysCoreWires 80) n :=
    rDataSubstSlot0 rSlot0InCore rCore rPartner18 (hDP.compose_left _)
  let hCPS : rCorePartner.DisjointWires rSum42 :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCS (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hCPG : rCorePartner.DisjointWires rPG7 :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCG (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hCPW : rCorePartner.DisjointWires rWork :=
    rDataSubstSlot0_disj_of_disj rSlot0InCore (hDP.compose_left _) hCW hPW
  let hCPS_G : (rCorePartner.concat rSum42 hCPS).DisjointWires rPG7 :=
    disjointWires_concat_left hCPS hCPG hSG
  have hCompCorePartner : rAct.compose rCorePartnerInActB42 = rCorePartner := by
    apply p3_qreg_ext
    intro i
    rw [QRegister.compose_apply]
    by_cases hMem : ∃ j : Fin 18, rSlot0InCore j = i
    · obtain ⟨j, rfl⟩ := hMem
      rw [rCorePartnerInActB42, rDataSubstSlot0_apply_slot0,
          rDataSubstSlot0_apply_slot0, ← hCompPartner, QRegister.compose_apply]
    · rw [rCorePartnerInActB42,
          rDataSubstSlot0_apply_of_not_mem rSlot0InCore _ _ _ hMem,
          rDataSubstSlot0_apply_of_not_mem rSlot0InCore _ _ _ hMem,
          ← hCompCore, QRegister.compose_apply]
  have hCompCatPartner :
      rAct.compose rCatPartnerInActB42 =
        ((rCorePartner.concat rSum42 hCPS).concat rPG7 hCPS_G).compose selCatInCoreSum42PG7 := by
    have hCS_eq := (hConcatEq rCorePartnerInActB42 rSum42InActB42
      rCorePartnerInActB42_disj_rSum42InActB42_part3a
      rCorePartner rSum42 hCPS hCompCorePartner hCompSum42).symm
    have hCSG_eq := (hConcatEq
      (rCorePartnerInActB42.concat rSum42InActB42 rCorePartnerInActB42_disj_rSum42InActB42_part3a)
      rPG7InActB42
      (disjointWires_concat_left rCorePartnerInActB42_disj_rSum42InActB42_part3a
        rCorePartnerInActB42_disj_rPG7InActB42_part3a rSum42InActB42_disj_rPG7InActB42)
      (rCorePartner.concat rSum42 hCPS) rPG7 hCPS_G hCS_eq hCompPG7).symm
    rw [rCatPartnerInActB42, ← QRegister.compose_assoc, hCSG_eq]
  let hPSum : rPartner18.DisjointWires rSum42 := (QRegExt.disjointWires_symm (hDP.compose_left _))
  have hSubP_raw := (dAddSubSlot0Sum42_realizesPair (mPayload := 80) v
    rCorePartner rSum42 rWork hCPS hCPW hSW (by omega : 13 ≤ 16 + mClean)).inv
  have hPartnerSlot0 : ∀ q : Fin 18,
      rCorePartner ⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ =
        rPartner18 q := fun q ↦ by
    have hq : (⟨q.val, lt_of_lt_of_le q.isLt (by decide : 18 ≤ fullSysCoreWires 80)⟩ :
        Fin (fullSysCoreWires 80)) = rSlot0InCore q :=
      Fin.ext (by
        rw [rSlot0InCore, rFullSysElecSlot_val]
        simp)
    rw [hq]
    exact rDataSubstSlot0_apply_slot0 rSlot0InCore rCore rPartner18 (hDP.compose_left _) q
  have hSubEmbedEq :
      (rCorePartner.concat rSum42 hCPS).embedUnitary
        (Slot0SubAdd14And217Stream.uSlot0Sum42Add 80)⁻¹ =
      (rPartner18.concat rSum42 hPSum).embedUnitary uElec18Sum42Add⁻¹ := by
    have hFwd := congrArg Subtype.val
      (embed_uSlot0Sum42Add_eq_uElec18Sum42Add rCorePartner rPartner18 rSum42
        hCPS hPSum hPartnerSlot0)
    apply Subtype.ext
    change (rCorePartner.concat rSum42 hCPS).embedMatrix
        (Slot0SubAdd14And217Stream.uSlot0Sum42Add 80).1ᴴ =
      (rPartner18.concat rSum42 hPSum).embedMatrix uElec18Sum42Add.1ᴴ
    rw [QRegister.embedMatrix_conjTranspose, QRegister.embedMatrix_conjTranspose]
    exact congrArg Matrix.conjTranspose hFwd
  have hSubP_clean := realizesClean_congr_embed hSubEmbedEq hSubP_raw
  rw [hConcatEq rPartner18InActB42 rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
      rPartner18 rSum42 hPSum hCompPartner hCompSum42] at hSubP_clean
  have hStep1 := hSubP_clean.widenActive
  rw [hInvEmbed] at hStep1
  let hE0P : (rElecSlot rCore 0).DisjointWires rPartner18 := (hDP.compose_left _).compose_left _
  let rTwo36 := (rElecSlot rCore 0).concat rPartner18 hE0P
  let hTwoS : rTwo36.DisjointWires rSum42 :=
    disjointWires_concat_left hE0P (hCS.compose_left _) (QRegExt.disjointWires_symm
      (hDP.compose_left _))
  let hTwoW : rTwo36.DisjointWires rWork :=
    disjointWires_concat_left hE0P (hCW.compose_left _) hPW
  let hE0P_act : rElec0InActB42.DisjointWires rPartner18InActB42 :=
    rCoreInActB42_disj_rPartner18InActB42.compose_left _
  let rTwo36InActB42 := rElec0InActB42.concat rPartner18InActB42 hE0P_act
  let hTwoS_act : rTwo36InActB42.DisjointWires rSum42InActB42 :=
    disjointWires_concat_left hE0P_act
      rElec0InActB42_disj_rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  have hCompTwo : rAct.compose rTwo36InActB42 = rTwo36 :=
    (hConcatEq rElec0InActB42 rPartner18InActB42 hE0P_act
      (rElecSlot rCore 0) rPartner18 hE0P hCompE0 hCompPartner).symm
  obtain ⟨hAdd36_raw, _⟩ := dAddSubTwoElec36Sum42_realizesPair v
    rTwo36 rSum42 rWork hTwoS hTwoW hSW hm18
  rw [hConcatEq rTwo36InActB42 rSum42InActB42 hTwoS_act
      rTwo36 rSum42 hTwoS hCompTwo hCompSum42] at hAdd36_raw
  have hStep5 := hAdd36_raw.widenActive
  have hStep2_raw := (dCanonStage128Fwd_realizes activeOneElecExpQftStage128 hm128 v
    (rAct.compose rCatPartnerInActB42) rWork (hAct_W.compose_left rCatPartnerInActB42)).widenActive
  have hStep2 : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      uQftPExpInActB42
      (dCanonStage128Fwd activeOneElecExpQftStage128 hm128 v
        (((rCorePartner.concat rSum42 hCPS).concat rPG7 hCPS_G).compose selCatInCoreSum42PG7)
        rWork
        ((disjointWires_concat_left hCPS_G
            (disjointWires_concat_left hCPS hCPW hSW) hGW).compose_left
          selCatInCoreSum42PG7)) := by
    have hCirEq :
        dCanonStage128Fwd activeOneElecExpQftStage128 hm128 v
          (rAct.compose rCatPartnerInActB42) rWork (hAct_W.compose_left rCatPartnerInActB42) =
        dCanonStage128Fwd activeOneElecExpQftStage128 hm128 v
          (((rCorePartner.concat rSum42 hCPS).concat rPG7 hCPS_G).compose selCatInCoreSum42PG7)
          rWork
          ((disjointWires_concat_left hCPS_G
              (disjointWires_concat_left hCPS hCPW hSW) hGW).compose_left
            selCatInCoreSum42PG7) := by
      congr 1
    rw [hCirEq] at hStep2_raw
    exact hStep2_raw
  have hStep4 := (dCanonStage128Inv_realizes activeTwoElecForestFullQftStage128 hm128 v
    (rAct.compose rCatSlot0Partner) rWork (hAct_W.compose_left rCatSlot0Partner)).widenActive
  rw [hInvEmbed] at hStep4
  have hSand_raw := dOrbitSandAnchorBoothOptDyn_realizes B hB6 hB27 hmClean slot2SwappedTo0 v
    rCore rPartner18 rOrbit16 rClean (hDP.compose_left _) (hDO.compose_left _)
    (hDC.compose_left _) hPO hPC hOC
  rw [hConcatEq rCoreInActB42 rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42
      rCore rPartner18 (hDP.compose_left _) hCompCore hCompPartner] at hSand_raw
  have hStep3 := hSand_raw.widenActive
  have hAll := hStep1.seq hAct_W (hStep2.seq hAct_W (hStep3.seq hAct_W (hStep4.seq hAct_W hStep5)))
  have hEmbed36 := embed_uTwoElec36Sum42Add_eq_mul rElec0InActB42 rPartner18InActB42 rSum42InActB42
    hE0P_act rElec0InActB42_disj_rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  have hGoal : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
      (uStageBOpenQftStreamInner B (by omega) hB27 slot2SwappedTo0 * uJunctionRawInActB42)
      (dStageBTwoElecStreamInnerOpenQftOnData B hB6 hB27 hmClean slot2SwappedTo0 v
        rData rPartner18 rOrbit16 rClean hDP hDO hDC hPO hPC hOC) := by
    unfold dStageBTwoElecStreamInnerOpenQftOnData
    dsimp only [rTwo36InActB42, hTwoS_act] at hAll
    rw [hEmbed36] at hAll
    simp only [_root_.mul_assoc] at hAll
    rw [uStageBOpenQftStreamInner_mul_uJunctionRawInActB42_e B (by
      omega) hB27 slot2SwappedTo0] at hAll
    exact hAll
  change DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rAct : QRegister (kStageBData + 18) n) rWork
    (uStageBOpenQftStreamInner B (by omega) hB27 slot2SwappedTo0 * uJunctionRawInActB42) _ at hGoal
  rwa [hActEq] at hGoal

attribute [irreducible] dStageBTwoElecStreamInnerOpenQftOnData

private theorem rId0InActB42_embedUnitary_uEff_eq_part3a :
    let rId0 := rCoreInActB42.compose (coreElecCosetB1Block pos24_6_le_80)
    rId0.embedUnitary activeOneElecExpQftStage128.uEff =
      rElec0InActB42.embedUnitary uCoreHadamard18 := by
  intro rId0
  have hEff : activeOneElecExpQftStage128.uEff =
      axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6) := rfl
  have hProd : axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6) =
      (rAxisPrefix 3 hL3_le_654 0).embedUnitary uCoreHadamard6 *
        ((rAxisPrefix 3 hL3_le_654 1).embedUnitary uCoreHadamard6 *
          (rAxisPrefix 3 hL3_le_654 2).embedUnitary uCoreHadamard6) := by
    dsimp only [axisProdPrefix]
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
        List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
    rfl
  have hAx : ∀ (a : Fin 3),
      rId0.compose (rAxisPrefix 3 hL3_le_654 a) =
        rElec0InActB42.compose
          (QRegister.block (6 * a.val) 6 (by have := a.isLt; omega)) := fun a ↦ by
    apply qreg_ext
    intro q
    have ha := a.isLt
    have hq := q.isLt
    apply Fin.ext
    rw [QRegister.compose_apply, QRegister.compose_apply]
    have hIdx : rAxisPrefix 3 hL3_le_654 a q =
        ⟨6 * a.val + q.val, by omega⟩ := by
      ext
      simp [rAxisPrefix, rAxis654]
    have hVal := coreElecCosetB1Block_elec_val pos24_6_le_80 ⟨6 * a.val + q.val, by omega⟩
    dsimp only at hVal
    rw [hIdx, QRegister.compose_apply, rCoreInActB42_apply]
    erw [hVal, rElec0InActB42_apply]
    simp
  rw [hEff, hProd]
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
  rw [hAx 0, hAx 1, hAx 2]
  unfold uCoreHadamard18
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, _root_.mul_assoc]
  rfl

private theorem rIdPartnerInActB42_embedUnitary_uEff_eq_part3a :
    let rIdP := rCorePartnerInActB42.compose (coreElecCosetB1Block pos24_6_le_80)
    rIdP.embedUnitary activeOneElecExpQftStage128.uEff =
      rPartner18InActB42.embedUnitary uCoreHadamard18 := by
  intro rIdP
  have hEff : activeOneElecExpQftStage128.uEff =
      axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6) := rfl
  have hProd : axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6) =
      (rAxisPrefix 3 hL3_le_654 0).embedUnitary uCoreHadamard6 *
        ((rAxisPrefix 3 hL3_le_654 1).embedUnitary uCoreHadamard6 *
          (rAxisPrefix 3 hL3_le_654 2).embedUnitary uCoreHadamard6) := by
    dsimp only [axisProdPrefix]
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero,
        List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
    rfl
  have hAx : ∀ (a : Fin 3),
      rIdP.compose (rAxisPrefix 3 hL3_le_654 a) =
        rPartner18InActB42.compose
          (QRegister.block (6 * a.val) 6 (by have := a.isLt; omega)) := fun a ↦ by
    apply qreg_ext
    intro q
    have ha := a.isLt
    have hq := q.isLt
    rw [QRegister.compose_apply, QRegister.compose_apply]
    have hIdx : rAxisPrefix 3 hL3_le_654 a q =
        ⟨6 * a.val + q.val, by omega⟩ := by
      ext
      simp [rAxisPrefix, rAxis654]
    rw [hIdx, QRegister.compose_apply]
    have hCoreSlot : coreElecCosetB1Block pos24_6_le_80 ⟨6 * a.val + q.val, by omega⟩ =
        rSlot0InCore ⟨6 * a.val + q.val, by omega⟩ := by
      apply Fin.ext
      rw [coreElecCosetB1Block_elec_val pos24_6_le_80 ⟨6 * a.val + q.val, by omega⟩,
          rSlot0InCore, rFullSysElecSlot_val]
      simp
    rw [hCoreSlot, rCorePartnerInActB42, rDataSubstSlot0_apply_slot0]
    exact congrArg rPartner18InActB42 (Fin.ext (by simp))
  rw [hEff, hProd]
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
  rw [hAx 0, hAx 1, hAx 2]
  unfold uCoreHadamard18
  simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, _root_.mul_assoc]
  rfl

private theorem rCat0InActB42_eq_concat_part3a :
    let rId0 := rCoreInActB42.compose (coreElecCosetB1Block pos24_6_le_80)
    let hDisj0 : rId0.DisjointWires rPG7InActB42 :=
      rCoreInActB42_disj_rPG7InActB42_part3a.compose_left _
    rCat0InActB42 = rId0.concat rPG7InActB42 hDisj0 := by
  intro rId0 hDisj0
  apply qreg_ext
  intro idx
  rw [rCat0InActB42, QRegister.compose_apply]
  unfold selCatInCoreSum42PG7
  refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) idx
  · rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    rfl
  · rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
    rfl

private theorem rCatPartnerInActB42_eq_concat_part3a :
    let rIdP := rCorePartnerInActB42.compose (coreElecCosetB1Block pos24_6_le_80)
    let hDisjP : rIdP.DisjointWires rPG7InActB42 :=
      rCorePartnerInActB42_disj_rPG7InActB42_part3a.compose_left _
    rCatPartnerInActB42 = rIdP.concat rPG7InActB42 hDisjP := by
  intro rIdP hDisjP
  apply qreg_ext
  intro idx
  rw [rCatPartnerInActB42, QRegister.compose_apply]
  unfold selCatInCoreSum42PG7
  refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) idx
  · rw [QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.compose_apply]
    have hCore0 :
        QRegister.block 0 (fullSysCoreWires 80) (by decide : fullSysCoreWires 80 ≤ kCoreSum42PG7)
          (coreElecCosetB1Block pos24_6_le_80 i) =
        Fin.castAdd 7 (Fin.castAdd 42 (coreElecCosetB1Block pos24_6_le_80 i)) :=
      Fin.ext (by simp)
    rw [hCore0, QRegister.concat_apply_left, QRegister.concat_apply_left]
    rfl
  · rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
    have hPG0 :
        QRegister.block (fullSysCoreWires 80 + 42) 7 le_rfl k =
        Fin.natAdd (fullSysCoreWires 80 + 42) k :=
      Fin.ext (by simp)
    rw [hPG0, QRegister.concat_apply_right]

/-- `IntertwinesCatOp` reduction of `uStageBOpenQftStreamInner` to `uStageBTwoElecStreamInnerEff`
on any 7-qubit phase-gradient catalyst `U_cat7` preparing `DyadicQft64.phaseGradKet 7`. -/
private theorem uStageBOpenQftStreamInner_intertwinesCatOp
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool)
    (U_cat7 : Unitary (2 ^ 7))
    (hcol0 : U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7) :
    IntertwinesCatOp
      (rPG7InActB42.embedUnitary U_cat7).1
      (rPG7InActB42.basisOutcomeProjector 0)
      (uStageBOpenQftStreamInner B hB1 hB27 slot2SwappedTo0).1
      (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 := by
  have hDisjE0SumPG :
      (rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42).DisjointWires
        rPG7InActB42 :=
    disjointWires_concat_left rElec0InActB42_disj_rSum42InActB42
      rElec0InActB42_disj_rPG7InActB42 rSum42InActB42_disj_rPG7InActB42
  have hDisjPSumPG :
      (rPartner18InActB42.concat rSum42InActB42
        rPartner18InActB42_disj_rSum42InActB42).DisjointWires rPG7InActB42 :=
    disjointWires_concat_left rPartner18InActB42_disj_rSum42InActB42
      rPartner18InActB42_disj_rPG7InActB42 rSum42InActB42_disj_rPG7InActB42
  have hDisjCorePPG :
      (rCoreInActB42.concat rPartner18InActB42
        rCoreInActB42_disj_rPartner18InActB42).DisjointWires rPG7InActB42 :=
    disjointWires_concat_left rCoreInActB42_disj_rPartner18InActB42
      rCoreInActB42_disj_rPG7InActB42_part3a rPartner18InActB42_disj_rPG7InActB42
  let rId0 := rCoreInActB42.compose (coreElecCosetB1Block pos24_6_le_80)
  let hDisjId0PG : rId0.DisjointWires rPG7InActB42 :=
    rCoreInActB42_disj_rPG7InActB42_part3a.compose_left _
  have hQft0 := activeOneElecExpQftStage128.hIntertwines
    rId0 rPG7InActB42 hDisjId0PG U_cat7 hcol0
  rw [← rCat0InActB42_eq_concat_part3a, rId0InActB42_embedUnitary_uEff_eq_part3a] at hQft0
  let rIdP := rCorePartnerInActB42.compose (coreElecCosetB1Block pos24_6_le_80)
  let hDisjIdPPG : rIdP.DisjointWires rPG7InActB42 :=
    rCorePartnerInActB42_disj_rPG7InActB42_part3a.compose_left _
  have hQftP := activeOneElecExpQftStage128.hIntertwines
    rIdP rPG7InActB42 hDisjIdPPG U_cat7 hcol0
  rw [← rCatPartnerInActB42_eq_concat_part3a, rIdPartnerInActB42_embedUnitary_uEff_eq_part3a]
    at hQftP
  have hHadComm :
      rPartner18InActB42.embedUnitary uCoreHadamard18 *
        rElec0InActB42.embedUnitary uCoreHadamard18 =
      rElec0InActB42.embedUnitary uCoreHadamard18 *
        rPartner18InActB42.embedUnitary uCoreHadamard18 := by
    apply Subtype.ext
    simp only [Submonoid.coe_mul, QRegister.embedUnitary_val]
    exact rPartner18InActB42.embedMatrix_comm_of_disjoint rElec0InActB42
      (QRegExt.disjointWires_symm (rCoreInActB42_disj_rPartner18InActB42.compose_left _))
      uCoreHadamard18.1 uCoreHadamard18.1
  have hQftFwd := hQftP.mul hQft0
  change IntertwinesCatOp _ _
    (uQftPExpInActB42 * uQft0ExpInActB42).1
    (rPartner18InActB42.embedUnitary uCoreHadamard18 *
      rElec0InActB42.embedUnitary uCoreHadamard18).1 at hQftFwd
  rw [hHadComm] at hQftFwd
  let uHad2 :=
    rElec0InActB42.embedUnitary uCoreHadamard18 *
      rPartner18InActB42.embedUnitary uCoreHadamard18
  have hQft2Fwd := activeTwoElecForestFullQftStage128.hIntertwines
    StageBTwoElecQftStream218Inner.rIdSlot0Partner rPG7InActB42
    StageBTwoElecQftStream218Inner.rIdSlot0Partner_disj_rPG7InActB42
    U_cat7 hcol0
  change IntertwinesCatOp _ _
    (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat).1
    (StageBTwoElecQftStream218Inner.rIdSlot0Partner.embedUnitary
      activeTwoElecForestFullQftStage128.uEff).1 at hQft2Fwd
  rw [rIdSlot0Partner_embedUnitary_uEff_eq] at hQft2Fwd
  have hQftInv := intertwinesCatOp_inv rPG7InActB42
    (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat) uHad2 hQft2Fwd
  have hAdd0 := intertwinesCatOp_embed_of_disj _ rPG7InActB42 hDisjE0SumPG U_cat7 uElec18Sum42Add
  have hSub0 := intertwinesCatOp_inv rPG7InActB42
    ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42).embedUnitary
      uElec18Sum42Add)
    ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42).embedUnitary
      uElec18Sum42Add)
    hAdd0
  have hAddP := intertwinesCatOp_embed_of_disj _ rPG7InActB42 hDisjPSumPG U_cat7 uElec18Sum42Add
  have hSubP := intertwinesCatOp_inv rPG7InActB42
    ((rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add)
    ((rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add)
    hAddP
  have hSand := intertwinesCatOp_embed_of_disj _ rPG7InActB42 hDisjCorePPG U_cat7
    (diagSignUnitary
      (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
        (PosSlots24CompactPhase288.midPhaseBitSpec slot2SwappedTo0
          PosSlots24SemanticBridge.pos24TailSign
          (MidKickSub33.pos24TailMag30MidpointB B hB1 (by omega)))))
  unfold uStageBOpenQftStreamInner uStageBTwoElecStreamInnerEff
  simp only [Submonoid.coe_mul]
  exact hAdd0.mul (hAddP.mul (hQftInv.mul (hSand.mul (hQftFwd.mul (hSubP.mul hSub0)))))

/-- **Zero-hypothesis `catState7` agreement of `uStageBOpenQftStreamInner` and
`uStageBTwoElecStreamInner`**: acting on `rPG7InActB42.embedMatrix catState7`, replacing
`uQft2_cat` by `uQftPExp * uQft0Exp` produces the exact same operator (global phase `1`,
zero catalyst leakage). -/
theorem uStageBOpenQftStreamInner_mul_catState7_eq
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uStageBOpenQftStreamInner B hB1 hB27 slot2SwappedTo0).1 *
        rPG7InActB42.embedMatrix catState7 =
      (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 *
        rPG7InActB42.embedMatrix catState7 := by
  let U_cat := (rPG7InActB42.embedUnitary (U_cat_B_normalized 7)).1
  let P_Cat0 := rPG7InActB42.basisOutcomeProjector 0
  have hInt := uStageBOpenQftStreamInner_intertwinesCatOp B hB1 hB27 slot2SwappedTo0
    (U_cat_B_normalized 7)
    (mulVec_col0_eq_phaseGradKet7 (U_cat_B_normalized 7) (U_cat_B_normalized_col_zero_singleCat 7))
  have hClosed := (uStageBTwoElecStreamInner_mul_catState7_eq_zeroHyp B hB1 hB27 slot2SwappedTo0).2
  rw [embedMatrix_catState7_eq]
  change (uStageBOpenQftStreamInner B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0) =
    (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0)
  have hOpen :
      (uStageBOpenQftStreamInner B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0) =
        (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0) := by
    calc (uStageBOpenQftStreamInner B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0)
        = (uStageBOpenQftStreamInner B hB1 hB27 slot2SwappedTo0).1 * U_cat * P_Cat0 := by
            rw [Matrix.mul_assoc]
      _ = U_cat * (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * P_Cat0 := hInt.1
      _ = (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * U_cat * P_Cat0 := by
            rw [← hInt.2.1]
      _ = (uStageBTwoElecStreamInnerEff B hB1 hB27 slot2SwappedTo0).1 * (U_cat * P_Cat0) := by
            rw [Matrix.mul_assoc]
  exact hOpen.trans hClosed.symm

end Part3A_OpenQftInner

section Part3B_OpenQftOuter

set_option exponentiation.threshold 8192

open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open DyadicQft64WalkCircuit (rIdInCat rPGInCat rAxis654 realizes_congr_slice)
open DyadicQft64WalkCircuit288
  (pack7Slices midSlicePerm7 genCatPhasePermUnitary
   genCatPhasePermUnitary_mul embedUnitary_genCatPhasePermUnitary_mulVec_basisKet
   apexCatUnitary)
open CatalystPrep (U_cat_B_normalized)
open DyadicQft64Engine (wireHadamard6)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6)
open CoreQftHadamard140And160
  (nCanon4062 rQftCanon128 rWorkCanon128 rQftCanon128_disjoint_rWorkCanon128
   rSysCanon128 rPGCanon128 rSysCanon128_disjoint_rPGCanon128
   rSysCanon128_disjoint_rWorkCanon128 rPGCanon128_disjoint_rWorkCanon128
   CanonStageSpec128)
open HeldRSum42TwistQftPass2Stitch
  (rAxisPrefix axisProdPrefix CanonStageSpec128.ofAxisPrefixCircuit
   stageHPrefixCanonStage128)
open StageAPointPhase128OnStep
  (ForestSlotConfig forestAxisNat xorForestBatchWork xorForestBatchTCost
   xorForestBatchFwdDyn128 xorForestBatchCanonStage128
   idxForestAx idxForestAx_inj
   diag6Unitary w16AxisCircuit w16Exp6 w16AxisCircuit_eval stageW16PrefixCanonStage128
   forestCfg3 forestExp3 forestCfg3_exp_eq
   forestCfg2 forestExp2 forestCfg2_exp_eq
   forestCfg1 forestExp1 forestCfg1_exp_eq
   forestCfg0 forestExp0 forestCfg0_exp_eq
   hL3_le_654 hL6_le_654
   activeTwoElecSlot3Stage128 activeTwoElecSlot2Stage128
   activeTwoElecSlot1Stage128 activeTwoElecSlot0Stage128
   rawActiveTwoElecForestQftStage128)
open FullConcrete7StepAndTrueSwapSelect (selCatInCoreSum42PG7)
open MasterZeroHypCompactAndCompactTopBridge
  (sel18InSys sel25InCat concat_sel18InSys_rPGCanon128_eq)
open ZeroHypStageBPureCnotAndHMidBClosure
  (idxForestAx18 idxForestAx18_inj)
open StageAConjHAndStreamBridge
  (xorForestBatchExpStage128 stagePointCrossExpC5 stagePointCrossExpC4
   stagePointCrossExpC3 stagePointCrossExpC2 stagePointCrossExpC1
   rawActiveOneElecExpQftStage128 activeOneElecExpQftStage128)
open StageADeconstrAndQftShare
  (realizes_eq_smul_of_same xorForestBatchFwdDyn128_0_3_eq)
open DoubleDutyFoldedRealizesBridge (rPG7Full)
open BoothOpt_Anchor218CachedTrueSwapOuter (coreElecCosetB1Block_elec_val)
open StageBTwoElecQftStream218Inner
  (rPG7InActB42 rPG7InActB42_apply rIdSlot0Partner rIdSlot0Partner_apply)
open LocalStageBPartnerTrueSwapStream218Closure
  (catState7 embedMatrix_catState7_eq)
open LocalStageBFastInnerPartnerShift
  (sel43InQft rSys36Canon rSys36Canon_disj_rPGCanon128
   rSys36Canon_concat_rPGCanon128_eq idxAx36 idxAx36_inj
   xorForestBatchFwdDyn_congr_sys)

/-! ### Part A: 128-State `rPG7` Carry Homomorphism & Factored QFT Equivalence -/

private def low4AddPerm7 (S : ℕ) : Equiv.Perm (Fin (2 ^ 7)) :=
  midSlicePerm7 0 (by decide) S

private theorem low4AddPerm7_val (S : ℕ) (m : Fin (2 ^ 7)) :
    (low4AddPerm7 S m).val = (m.val % 16 + S) % 16 + 16 * (m.val / 16) := by
  change pack7Slices 0 (m.val % 2 ^ 0)
    (((m.val / 2 ^ 0) % 2 ^ (4 - 0) + S) % 2 ^ (4 - 0)) (m.val / 16) = _
  simp [pack7Slices, Nat.mod_one]

private noncomputable def addLow4PG7Unitary (kSys : ℕ)
    (S : BitAssignment kSys → ℕ) : Unitary (2 ^ (kSys + 7)) :=
  genCatPhasePermUnitary kSys 7
    (fun γ ↦ low4AddPerm7 (S γ))
    (fun γ m ↦ 16 * (((m.val % 16 + S γ) / 16 : ℕ) : ℤ))

private theorem addLow4PG7Unitary_mul (kSys : ℕ)
    (S₁ S₂ : BitAssignment kSys → ℕ) :
    addLow4PG7Unitary kSys S₂ * addLow4PG7Unitary kSys S₁ =
      addLow4PG7Unitary kSys (fun γ ↦ S₁ γ + S₂ γ) := by
  unfold addLow4PG7Unitary
  rw [genCatPhasePermUnitary_mul]
  congr 1
  · funext γ
    ext m
    dsimp only
    rw [Equiv.trans_apply, low4AddPerm7_val, low4AddPerm7_val, low4AddPerm7_val]
    have h1 : ((m.val % 16 + S₁ γ) % 16 + 16 * (m.val / 16)) % 16 =
        (m.val % 16 + S₁ γ) % 16 := by omega
    have h2 : ((m.val % 16 + S₁ γ) % 16 + 16 * (m.val / 16)) / 16 =
        m.val / 16 := by omega
    rw [h1, h2]
    omega
  · funext γ m
    dsimp only
    rw [low4AddPerm7_val]
    have hmod : ((m.val % 16 + S₁ γ) % 16 + 16 * (m.val / 16)) % 16 =
        (m.val % 16 + S₁ γ) % 16 := by omega
    rw [hmod]
    have hdiv16 : 16 * ((m.val % 16 + S₁ γ) / 16) +
        16 * (((m.val % 16 + S₁ γ) % 16 + S₂ γ) / 16) =
        16 * ((m.val % 16 + (S₁ γ + S₂ γ)) / 16) := by omega
    exact_mod_cast hdiv16

private theorem apexCatUnitary_eq_addLow4PG7Unitary (kSys s : ℕ) (hs : s ≤ 3)
    (C uLow S : BitAssignment kSys → ℕ)
    (hS : ∀ γ : BitAssignment kSys, 16 * C γ + 2 ^ s * uLow γ = S γ) :
    apexCatUnitary kSys s hs (fun γ ↦ 16 * (C γ : ℤ)) uLow =
      addLow4PG7Unitary kSys S := by
  unfold apexCatUnitary addLow4PG7Unitary
  congr 1
  · funext γ
    ext m
    rw [low4AddPerm7_val]
    change pack7Slices s (m.val % 2 ^ s)
      (((m.val / 2 ^ s) % 2 ^ (4 - s) + uLow γ) % 2 ^ (4 - s)) (m.val / 16) = _
    have hm := m.isLt
    have hγ := hS γ
    rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl <;>
      · simp only [pack7Slices]
        omega
  · funext γ m
    dsimp only
    have hm := m.isLt
    have hγ := hS γ
    have hcarry : C γ + ((m.val / 2 ^ s) % 2 ^ (4 - s) + uLow γ) / 2 ^ (4 - s) =
        (m.val % 16 + S γ) / 16 := by
      rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl <;> omega
    have hmul : 16 * C γ + 16 * (((m.val / 2 ^ s) % 2 ^ (4 - s) + uLow γ) / 2 ^ (4 - s)) =
        16 * ((m.val % 16 + S γ) / 16) := by
      rw [← Nat.mul_add, hcarry]
    exact_mod_cast hmul

section UnsealForestDynSec3B
set_option allowUnsafeReducibility true
open scoped Circuit.Notation
open DyadicQft64Engine DyadicQft64 DyadicQft64WalkCircuit DyadicQft64WalkCircuit288
open StageAPointPhase128OnStep
attribute [local semireducible]
  StageAPointPhase128OnStep.xorForestBatchFwdDyn StageAPointPhase128OnStep.xorForestBatchDyn

private theorem xorForestBatchFwd_realizes_addLow4
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kSys mWork : ℕ} [NeZero (2 ^ n)]
    (v : Var) (s : ℕ) (cfg : ForestSlotConfig s)
    (L : ℕ) (hs : s ≤ 3) (hL : 1 ≤ L)
    (hm : xorForestBatchWork s cfg L ≤ mWork)
    (rSys : QRegister kSys n) (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    (hdisj_SP : rSys.DisjointWires rPG)
    (hdisj_SW : rSys.DisjointWires rWork)
    (hdisj_PW : rPG.DisjointWires rWork)
    (idxAx : Fin L → Fin 6 → Fin kSys)
    (hinj_ax : Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rSys.concat rPG hdisj_SP) rWork
      (addLow4PG7Unitary kSys
        (fun γ ↦ ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i))))
      (xorForestBatchFwdDyn v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW
        idxAx hinj_ax) := by
  let wpairs := batchCnotPairs rSys cfg.pairs idxAx
  have hne_fwd : ∀ wp ∈ wpairs, wp.1 ≠ wp.2 :=
    batchCnotPairs_hne rSys cfg.pairs cfg.hne idxAx hinj_ax
  have hne_inv : ∀ wp ∈ wpairs.reverse, wp.1 ≠ wp.2 :=
    fun wp hwp ↦ hne_fwd wp (List.mem_reverse.mp hwp)
  have hwp_sys : ∀ wp ∈ wpairs, wp.1 ∈ rSys.image ∧ wp.2 ∈ rSys.image :=
    batchCnotPairs_mem_sys rSys cfg.pairs idxAx
  let c_xor_fwd : Circuit n := cnotPairsCircuit wpairs hne_fwd
  let c_xor_inv : Circuit n := cnotPairsCircuit wpairs.reverse hne_inv
  let col0Bucket : List (Wire n) :=
    finMapList (fun i : Fin (L - 1) ↦ rSys (idxAx ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
      expandColWires rSys idxAx cfg.col0Tail6
  let colRest : Fin (3 - s) → List (Wire n) :=
    fun r ↦ expandColWires rSys idxAx (cfg.colRest6 r)
  let buckets : List (List (Wire n)) := col0Bucket :: finMapList colRest
  have hmap_len : buckets.map List.length = xorForestBucketsLen s cfg L := by
    simp only [buckets, xorForestBucketsLen, List.map_cons, col0Bucket, List.length_append,
      finMapList_length, finMapList_map_length_eq_ofFn, expandColWires_length, colRest]
  have hsteps_eq :
      compressStepsCount buckets 0 = compressStepsNat (xorForestBucketsLen s cfg L) 0 := by
    rw [compressStepsCount_eq_nat, hmap_len]
  have hfit_csa : 0 + compressStepsCount buckets 0 ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm
    rw [hsteps_eq]
    omega
  have hB_nodup : ∀ B ∈ buckets, B.Nodup := fun B hB ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rw [List.nodup_append]
      refine ⟨finMapList_nodup (fun i₁ i₂ h ↦ by
          have hp : ((⟨i₁.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) =
              (⟨i₂.val + 1, by omega⟩, cfg.qCin0) := hinj_ax (rSys.wires.injective h)
          have hv : i₁.val + 1 = i₂.val + 1 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
          exact Fin.ext (by omega)),
        expandColWires_nodup rSys idxAx hinj_ax cfg.col0Tail6 cfg.hTailNodup,
        fun x hx y hy hxy ↦ ?_⟩
      subst hxy
      rcases mem_finMapList.mp hx with ⟨i, rfl⟩
      rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hy with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨i.val + 1, by omega⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
      exact cfg.hCinNotTail (hq_eq ▸ hq')
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      exact expandColWires_nodup rSys idxAx hinj_ax (cfg.colRest6 r) (cfg.hRestNodup r)
  have hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂ := by
    rw [List.pairwise_cons]
    refine ⟨fun B₂ hB₂ x hx₁ hx₂ ↦ ?_,
      buckets_pairwise_finMapList colRest fun r₁ r₂ hne x hx₁ hx₂ ↦ ?_⟩
    · rcases mem_finMapList.mp hB₂ with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx₂ with ⟨q₂, hq₂, l₂, rfl⟩
      rcases List.mem_append.mp hx₁ with hx_cin | hx_tail
      · rcases mem_finMapList.mp hx_cin with ⟨i, heq⟩
        have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (l₂, q₂) :=
          hinj_ax (rSys.wires.injective heq)
        have hq_eq : q₂ = cfg.qCin0 := (congrArg Prod.snd hp).symm
        exact cfg.hCinDisjRest r (hq_eq ▸ hq₂)
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hx_tail with ⟨q₁, hq₁, l₁, heq⟩
        have hp : ((l₁, q₁) : Fin L × Fin 6) = (l₂, q₂) := hinj_ax (rSys.wires.injective heq)
        have hq_eq : q₂ = q₁ := (congrArg Prod.snd hp).symm
        exact cfg.hTailDisjRest r q₁ hq₁ (hq_eq ▸ hq₂)
    · rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₁) x).mp hx₁ with ⟨q₁, hq₁, l₁, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₂) _).mp hx₂ with ⟨q₂, hq₂, l₂, heq⟩
      have hp : ((l₂, q₂) : Fin L × Fin 6) = (l₁, q₁) := hinj_ax (rSys.wires.injective heq)
      have hq_eq : q₂ = q₁ := congrArg Prod.snd hp
      exact cfg.hRestDisj r₁ r₂ hne q₁ hq₁ (hq_eq ▸ hq₂)
  have hB_sys : ∀ B ∈ buckets, ∀ x ∈ B, x ∈ rSys.image := fun B hB x hx ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rcases List.mem_append.mp hx with hx_cin | hx_tail
      · rcases mem_finMapList.mp hx_cin with ⟨_, rfl⟩
        exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 x).mp hx_tail with ⟨_, _, _, rfl⟩
        exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx with ⟨_, _, _, rfl⟩
      exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
  have hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rWork.image := fun B hB x hx hm_w ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rWork _).mp hm_w with ⟨k, hk⟩
    exact hdisj_SW.ne i k hk.symm
  have hB_PG : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rPG.image := fun B hB x hx hm_pg ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨k, hk⟩
    exact hdisj_SP.ne i k hk.symm
  let out := compressBuckets rWork buckets 0 hfit_csa hB_nodup hB_disj hB_anc
  have hspec := compressBuckets_spec rPG.image rWork
    (disjWires_image (QRegExt.disjointWires_symm hdisj_PW)) buckets 0 hfit_csa hB_nodup hB_disj
      hB_anc hB_PG
  have hst : out.steps.length = compressStepsNat (xorForestBucketsLen s cfg L) 0 :=
    hspec.2.1.trans hsteps_eq
  let st := out.steps.length
  have hm' : 1 + st + (4 - s) ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm
    omega
  let rGid : QRegister (4 - s) n := rWork.slice (0 + st) (4 - s) (by omega)
  let wZero : Wire n := rWork ⟨st + (4 - s), by omega⟩
  have hblen : buckets.length = 4 - s := by
    simp only [buckets, List.length_cons, finMapList_length]
    omega
  have hsw_len : out.sumWires.length = 4 - s := hspec.1.trans hblen
  let wCin0 : Wire n := rSys (idxAx ⟨0, hL⟩ cfg.qCin0)
  let tWires : List (Wire n) := out.carries
  let rMidPG : QRegister (4 - s) n := rPG.slice s (4 - s) (by omega)
  let uWires : Fin (4 - s) → Wire n := fun j ↦
    optWireOrZero wZero (out.sumWires.get ⟨j.val, by omega⟩)
  have hu_T : ∀ j, uWires j ∉ rMidPG.image := fun j hm_t ↦ by
    have hm_pg : uWires j ∈ rPG.image := QRegister.image_compose_subset rPG _ hm_t
    dsimp only [uWires] at hm_pg
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hm_pg
        dsimp only [optWireOrZero, wZero] at hm_pg
        rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
        exact hdisj_PW.ne i ⟨st + (4 - s), by omega⟩ hi
    | some w =>
        rw [hget] at hm_pg
        dsimp only [optWireOrZero] at hm_pg
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with
          ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · exact hB_PG B hB w hwB hm_pg
        · rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
          exact hdisj_PW.ne i ⟨k, hk⟩ hi
  have hu_C : ∀ j, uWires j ∉ rGid.image := fun j hm_c ↦ by
    rcases (QRegister.mem_image rGid _).mp hm_c with ⟨i, hi⟩
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]
      exact congrArg rWork (Fin.ext (by simp))
    rw [hi'] at hi
    dsimp only [uWires] at hi
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hi
        dsimp only [optWireOrZero, wZero] at hi
        have hv := congrArg Fin.val (rWork.wires.injective hi)
        dsimp at hv
        omega
    | some w =>
        rw [hget] at hi
        dsimp only [optWireOrZero] at hi
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with
          ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt, rfl⟩
        · exact hB_anc B hB w hwB ((QRegister.mem_image rWork _).mpr ⟨_, hi⟩)
        · have hv := congrArg Fin.val (rWork.wires.injective hi)
          dsimp at hv
          have := hspec.2.1
          omega
  have hdisj_TC : rMidPG.DisjointWires rGid :=
    (hdisj_PW.compose_left _).compose_right _
  have hwcin_not_B : ∀ B ∈ buckets, wCin0 ∉ B := fun B hB hmem ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rcases List.mem_append.mp hmem with hcin | htail
      · rcases mem_finMapList.mp hcin with ⟨i, heq⟩
        have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) =
            (⟨0, hL⟩, cfg.qCin0) := hinj_ax (rSys.wires.injective heq)
        have hv : i.val + 1 = 0 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
        omega
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp htail with ⟨q', hq', l, heq⟩
        have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
          hinj_ax (rSys.wires.injective heq)
        have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
        exact cfg.hCinNotTail (hq_eq ▸ hq')
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) _).mp hmem with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
      exact cfg.hCinDisjRest r (hq_eq ▸ hq')
  have hcin_u : ∀ j, wCin0 ≠ uWires j := fun j heq ↦ by
    dsimp only [uWires] at heq
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at heq
        dsimp only [optWireOrZero, wZero, wCin0] at heq
        exact hdisj_SW.ne _ ⟨st + (4 - s), by omega⟩ heq
    | some w =>
        rw [hget] at heq
        dsimp only [optWireOrZero] at heq
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with
          ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · exact hwcin_not_B B hB (heq ▸ hwB)
        · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hcin_T : wCin0 ∉ rMidPG.image := fun hm_t ↦ by
    rcases (QRegister.mem_image rPG _).mp (QRegister.image_compose_subset rPG _ hm_t) with
      ⟨i, hi⟩
    exact hdisj_SP.ne _ i hi.symm
  have hcin_C : wCin0 ∉ rGid.image := fun hm_c ↦ by
    rcases (QRegister.mem_image rWork _).mp (QRegister.image_compose_subset rWork _ hm_c) with
      ⟨k, hk⟩
    exact hdisj_SW.ne _ k hk.symm
  let f_xor_fwd : BitAssignment n → BitAssignment n := cnotPairsPerm wpairs
  let f_xor_inv : BitAssignment n → BitAssignment n := cnotPairsPerm wpairs.reverse
  let β₂_of : BitAssignment kSys → BitAssignment n :=
    fun γ ↦ symStepFwdList out.steps (f_xor_fwd (canonAssign rSys γ))
  let C_fn : BitAssignment kSys → ℕ := fun γ ↦ wireListSum tWires (β₂_of γ)
  let Φ : BitAssignment kSys → ℤ := fun γ ↦ 16 * (C_fn γ : ℤ)
  let uLow : BitAssignment kSys → ℕ :=
    fun γ ↦ weightedOptWiresVal out.sumWires (β₂_of γ) + (β₂_of γ wCin0).val
  have hU_steps : ∀ s' ∈ out.steps, s'.S ⊆ rSys.image ∪ rWork.image := fun s' hs' w hw ↦ by
    rcases hspec.2.2.2.2.2.2.1 s' hs' w hw with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
    · exact Finset.mem_union_left _ (hB_sys B hB w hwB)
    · exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩)
  have hcin0_unchanged : ∀ δ : BitAssignment n,
      symStepFwdList out.steps δ wCin0 = δ wCin0 :=
    fun δ ↦ symStepFwdList_outside out.steps δ wCin0 fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, heq⟩
      · exact hwcin_not_B B hB hwB
      · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hxor_fwd_outside_sys : ∀ (δ : BitAssignment n) (w : Wire n),
      w ∉ rSys.image → f_xor_fwd δ w = δ w :=
    fun δ w hw ↦ cnotPairsPerm_outside wpairs δ w fun wp hwp heq ↦
      hw (heq ▸ (hwp_sys wp hwp).2)
  have hxor_inv_outside_sys : ∀ (δ : BitAssignment n) (w : Wire n),
      w ∉ rSys.image → f_xor_inv δ w = δ w :=
    fun δ w hw ↦ cnotPairsPerm_outside wpairs.reverse δ w fun wp hwp heq ↦
      hw (heq ▸ (hwp_sys wp (List.mem_reverse.mp hwp)).2)
  have hag_U : ∀ (β : BitAssignment n), (∀ j : Fin mWork, β (rWork j) = 0) →
      ∀ w ∈ rSys.image ∪ rWork.image,
        symStepFwdList out.steps (f_xor_fwd β) w = β₂_of (fun i ↦ β (rSys i)) w := by
    intro β hzero
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    refine symStepFwdList_eq_on_superset out.steps hU_steps ?_
    refine cnotPairsPerm_eq_on_superset wpairs
      (fun wp hwp ↦ ⟨Finset.mem_union_left _ (hwp_sys wp hwp).1,
        Finset.mem_union_left _ (hwp_sys wp hwp).2⟩)
      fun w hw ↦ ?_
    rcases Finset.mem_union.mp hw with hws | hww
    · rcases (QRegister.mem_image rSys w).mp hws with ⟨i, rfl⟩
      exact (canonAssign_apply_sys rSys γ i).symm
    · have hnot_sys : w ∉ rSys.image := fun hm_s ↦ by
        rcases (QRegister.mem_image rSys w).mp hm_s with ⟨i, rfl⟩
        rcases (QRegister.mem_image rWork _).mp hww with ⟨j, hj⟩
        exact hdisj_SW.ne i j hj.symm
      rw [canonAssign_apply_outside rSys γ hnot_sys]
      rcases (QRegister.mem_image rWork w).mp hww with ⟨j, rfl⟩
      exact hzero j
  have hnat_eq : ∀ γ : BitAssignment kSys,
      16 * C_fn γ + 2 ^ s * uLow γ =
        ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) := by
    intro γ
    let β₁ := f_xor_fwd (canonAssign rSys γ)
    have hzero_canon : ∀ k, 0 ≤ k → (hk : k < mWork) → β₁ (rWork ⟨k, hk⟩) = 0 :=
      fun k _ hk ↦ by
        have hnot_sys : rWork ⟨k, hk⟩ ∉ rSys.image := fun hm_s ↦ by
          rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
          exact hdisj_SW.ne i ⟨k, hk⟩ hi
        dsimp only [β₁]
        rw [hxor_fwd_outside_sys _ _ hnot_sys, canonAssign_apply_outside rSys γ hnot_sys]
    have hcons := hspec.2.2.2.2.2.2.2 β₁ hzero_canon
    rw [hblen] at hcons
    have hscale_csa : 2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
        16 * wireListSum out.carries (β₂_of γ) = 2 ^ s * weightedBucketsVal buckets β₁ := by
      have hp4 : 2 ^ s * 2 ^ (4 - s) = 16 := two_pow_mul_four_sub s hs
      calc 2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
            16 * wireListSum out.carries (β₂_of γ)
          = 2 ^ s * (weightedOptWiresVal out.sumWires (β₂_of γ) +
              2 ^ (4 - s) * wireListSum out.carries (β₂_of γ)) := by
              rw [mul_add, ← mul_assoc, hp4]
        _ = 2 ^ s * weightedBucketsVal buckets β₁ := congrArg (2 ^ s * ·) hcons
    have hcin0_eq : (β₂_of γ wCin0).val = (β₁ wCin0).val :=
      congrArg ZMod.val (hcin0_unchanged β₁)
    dsimp only [C_fn, tWires, uLow]
    calc 16 * wireListSum out.carries (β₂_of γ) +
          2 ^ s * (weightedOptWiresVal out.sumWires (β₂_of γ) + (β₂_of γ wCin0).val)
        = 2 ^ s * (β₂_of γ wCin0).val +
          (2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
            16 * wireListSum out.carries (β₂_of γ)) := by ring
      _ = 2 ^ s * ((β₁ wCin0).val + weightedBucketsVal buckets β₁) := by
            rw [hcin0_eq, hscale_csa]
            ring
      _ = ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) :=
            weightedBuckets_forest_eq s cfg hL rSys idxAx hinj_ax γ
  have hhc_xor_fwd : PhasePerm rSys.image c_xor_fwd (fun _ ↦ 1) f_xor_fwd :=
    PhasePerm.of_classicalPerm (classicalPerm_cnotPairsCircuit wpairs hne_fwd)
      hxor_fwd_outside_sys
  have hhc_xor_inv : PhasePerm rSys.image c_xor_inv (fun _ ↦ 1) f_xor_inv :=
    PhasePerm.of_classicalPerm (classicalPerm_cnotPairsCircuit wpairs.reverse hne_inv)
      hxor_inv_outside_sys
  have hcancel_xor : ∀ (f_m : BitAssignment n → BitAssignment n),
      (∀ δ w, w ∉ rPG.image → f_m δ w = δ w) →
      ∀ β w, w ∉ rPG.image → f_xor_inv (f_m (f_xor_fwd β)) w = β w := by
    intro f_m hout_m β w hw
    let S_nonPG : Finset (Wire n) := Finset.univ \ rPG.image
    have hmem_S : ∀ u : Wire n, u ∈ S_nonPG ↔ u ∉ rPG.image := by simp [S_nonPG]
    have hsys_S : ∀ u ∈ rSys.image, u ∈ S_nonPG := fun u hu ↦
      (hmem_S u).mpr fun hpg ↦ by
        rcases (QRegister.mem_image rSys u).mp hu with ⟨i, rfl⟩
        rcases (QRegister.mem_image rPG _).mp hpg with ⟨j, hj⟩
        exact hdisj_SP.ne i j hj.symm
    have heq_inv := cnotPairsPerm_eq_on_superset (S := S_nonPG) wpairs.reverse
      (fun wp hwp ↦ by
        have hs' := hwp_sys wp (List.mem_reverse.mp hwp)
        exact ⟨hsys_S _ hs'.1, hsys_S _ hs'.2⟩)
      (β₁ := f_m (f_xor_fwd β)) (β₂ := f_xor_fwd β)
      (fun u hu ↦ hout_m (f_xor_fwd β) u ((hmem_S u).mp hu))
      w ((hmem_S w).mpr hw)
    dsimp only [f_xor_inv, f_xor_fwd] at heq_inv ⊢
    rw [heq_inv, cnotPairsPerm_reverse_cancel wpairs hne_fwd β]
  have hpg_not_sys : ∀ j : Fin 7, rPG j ∉ rSys.image := fun j hm_s ↦ by
    rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
    exact hdisj_SP.ne i j hi
  have hpg_xor_eq : ∀ (f_m : BitAssignment n → BitAssignment n) (β : BitAssignment n),
      regVal rPG (f_xor_inv (f_m (f_xor_fwd β))) = regVal rPG (f_m (f_xor_fwd β)) :=
    fun f_m β ↦ regVal_congr rPG fun j ↦ hxor_inv_outside_sys _ (rPG j) (hpg_not_sys j)
  have hpg_in_eq : ∀ (β : BitAssignment n) (j : Fin 7),
      symStepFwdList out.steps (f_xor_fwd β) (rPG j) = β (rPG j) := fun β j ↦ by
    rw [symStepFwdList_outside out.steps (f_xor_fwd β) (rPG j) (fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, heq⟩
      · exact hB_PG B hB _ hwB ((QRegister.mem_image rPG _).mpr ⟨j, rfl⟩)
      · exact hdisj_PW.ne j ⟨k, hk⟩ heq)]
    exact hxor_fwd_outside_sys β (rPG j) (hpg_not_sys j)
  have hpg_reg_in : ∀ β : BitAssignment n,
      regVal rPG (symStepFwdList out.steps (f_xor_fwd β)) = regVal rPG β :=
    fun β ↦ regVal_congr rPG (hpg_in_eq β)
  have hmid_reg_in : ∀ β : BitAssignment n,
      regVal rMidPG (symStepFwdList out.steps (f_xor_fwd β)) =
        ((regVal rPG β) / 2 ^ s) % 2 ^ (4 - s) := fun β ↦ by
    rw [regVal_midSlice7_eq s hs rPG _, hpg_reg_in β]
  have hwork_not_sys : ∀ k : Fin mWork, rWork k ∉ rSys.image := fun k hm_s ↦ by
    rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
    exact hdisj_SW.ne i k hi
  have hgid_zero_β₂ : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) →
      ∀ i : Fin (4 - s), symStepFwdList out.steps (f_xor_fwd β) (rGid i) = 0 := by
    intro β hzero i
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]
      exact congrArg rWork (Fin.ext (by simp))
    rw [hi', symStepFwdList_outside out.steps (f_xor_fwd β) _ (fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt, heq⟩
      · exact hB_anc B hB _ hwB ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩)
      · have hv := congrArg Fin.val (rWork.wires.injective heq)
        dsimp at hv
        have := hspec.2.1
        omega)]
    rw [hxor_fwd_outside_sys β _ (hwork_not_sys ⟨st + i.val, by omega⟩)]
    exact hzero ⟨st + i.val, by omega⟩
  have huLow_on_β : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) →
      bitsVal (fun j ↦ symStepFwdList out.steps (f_xor_fwd β) (uWires j)) +
        (symStepFwdList out.steps (f_xor_fwd β) wCin0).val =
      uLow (fun i ↦ β (rSys i)) := by
    intro β hzero
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    let δ := symStepFwdList out.steps (f_xor_fwd β)
    have hag := hag_U β hzero
    have hz_δ : δ wZero = 0 := by
      dsimp only [δ]
      rw [hag wZero (Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩))]
      dsimp only [β₂_of]
      rw [symStepFwdList_outside out.steps _ wZero (fun s' hs' hm_s ↦ by
          rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with
            ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt, heq⟩
          · exact hB_anc B hB _ hwB ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩)
          · have hv := congrArg Fin.val (rWork.wires.injective heq)
            dsimp [wZero] at hv
            have := hspec.2.1
            omega),
        hxor_fwd_outside_sys _ _ (hwork_not_sys ⟨st + (4 - s), by omega⟩),
        canonAssign_apply_outside rSys γ (hwork_not_sys ⟨st + (4 - s), by omega⟩)]
    have hbv := weightedOptWiresVal_eq_bitsVal wZero out.sumWires hsw_len δ hz_δ
    dsimp only [uWires]
    rw [hbv]
    have hsw_eq_u : weightedOptWiresVal out.sumWires δ =
        weightedOptWiresVal out.sumWires (β₂_of γ) :=
      weightedOptWiresVal_congr fun ow how w hsome ↦
        hag w (by
          rcases hspec.2.2.2.2.1 ow how w hsome with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
          · exact Finset.mem_union_left _ (hB_sys B hB w hwB)
          · exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩))
    have hcin_u_eq : δ wCin0 = β₂_of γ wCin0 :=
      hag wCin0 (Finset.mem_union_left _ ((QRegister.mem_image rSys _).mpr ⟨_, rfl⟩))
    change weightedOptWiresVal out.sumWires δ + (δ wCin0).val = uLow γ
    rw [hsw_eq_u, hcin_u_eq]
  have htWires_on_β : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) →
      wireListSum tWires (symStepFwdList out.steps (f_xor_fwd β)) =
        wireListSum tWires (β₂_of (fun i ↦ β (rSys i))) := by
    intro β hzero
    refine wireListSum_congr fun w hw ↦ hag_U β hzero w ?_
    rcases hspec.2.2.2.1 w hw with ⟨k, hk, _, rfl⟩
    exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩)
  have hMid_sub_PG : rMidPG.image ⊆ rPG.image := QRegister.image_compose_subset rPG _
  obtain ⟨φ_add, f_add, hp_add0, hval_add, hwp_add⟩ :=
    gidneyApexChain_correct v false (4 - s) uWires rMidPG rGid wCin0
      hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C
  have hp_add : PhasePerm rPG.image _ φ_add f_add := hp_add0.mono hMid_sub_PG
  have hcpp_gid : CleanPhasePerm rGid rPG.image
      (gidneyApexChainDyn v false (4 - s) uWires rMidPG rGid wCin0
        hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C)
      (gidneyApexChainCircuit false (4 - s) uWires rMidPG rGid wCin0
        hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C)
      φ_add f_add :=
    ⟨hp_add,
      fun Q ↦ gidneyApexChainDyn_wp_const v false (4 - s) uWires rMidPG rGid wCin0
        hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C Q,
      fun Q ↦ hwp_add _ fun _ _ ↦ rfl⟩
  have hcpp_in0 := cleanPhasePerm_sandwich_phase
    (tList tWires) Circuit.identity _ (fun _ ↦ 1) id id
    (phasePerm_tList tWires) (PhasePerm.identity ∅) (Finset.disjoint_empty_left _) hcpp_gid
  have hcpp_in : CleanPhasePerm rGid rPG.image
      ((DynamicCircuit.circuit (tList tWires)).seq
        ((gidneyApexChainDyn v false (4 - s) uWires rMidPG rGid wCin0
            hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
          (DynamicCircuit.circuit Circuit.identity)))
      (tList tWires ;;ᶜ
        gidneyApexChainCircuit false (4 - s) uWires rMidPG rGid wCin0
          hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C ;;ᶜ
        Circuit.identity)
      _ f_add :=
    CleanPhasePerm.mono_work_and_set hcpp_in0 (Finset.Subset.refl _) (by simp)
  have ⟨f_mid, hp_mid, hM_mid, hwp_mid⟩ := symWrapDynList_phasePerm_correct
    v rPG.image rWork 0 (4 - s) out.steps hspec.2.2.2.2.2.1 (by omega)
    _ _ _ _ hcpp_in.phasePerm
    (restrictAssertionToZeroAncilla_sandwich_var v rGid ∅ (tList tWires) Circuit.identity
      _ id (phasePerm_tList tWires) (Finset.disjoint_empty_left _) _ _ hwp_add)
  have hcpp_mid : CleanPhasePerm rWork rPG.image
      (symWrapDynList v out.steps
        ((DynamicCircuit.circuit (tList tWires)).seq
          ((gidneyApexChainDyn v false (4 - s) uWires rMidPG rGid wCin0
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
            (DynamicCircuit.circuit Circuit.identity))))
      (symWrapCircuitList out.steps _) _ f_mid :=
    CleanPhasePerm.mono_work_and_set
      ⟨hp_mid, fun Q ↦ symWrapDynList_wp_const v out.steps _ hcpp_in.wp_const Q,
        fun Q ↦ hwp_mid _ fun _ _ ↦ rfl⟩
      (QRegister.image_compose_subset rWork _) (Finset.Subset.refl _)
  have hcpp_tot := cleanPhasePerm_sandwich_phase c_xor_fwd c_xor_inv (fun _ ↦ 1) (fun _ ↦ 1)
    f_xor_fwd f_xor_inv hhc_xor_fwd hhc_xor_inv (disjWires_image hdisj_SW) hcpp_mid
  rw [← apexCatUnitary_eq_addLow4PG7Unitary kSys s hs C_fn uLow _ hnat_eq]
  refine cleanPhasePerm_realizes_genCatPhasePerm hdisj_SP hcpp_tot
    (fun γ ↦ midSlicePerm7 s hs (uLow γ))
    (fun γ m ↦ Φ γ + 16 * (((((m.val / 2 ^ s) % 2 ^ (4 - s)) + uLow γ) / 2 ^ (4 - s) : ℕ) : ℤ))
    (fun β hzero ↦ ?_)
    (fun β q hq ↦ hcancel_xor f_mid hp_mid.outside β q hq)
    (fun β hzero ↦ ?_)
  · let δ := symStepFwdList out.steps (f_xor_fwd β)
    obtain ⟨hφ_a, _⟩ := hval_add δ (hgid_zero_β₂ β hzero)
    dsimp only [id, Φ, C_fn]
    simp only [one_mul, mul_one]
    change dyadicTurn 7 (16 * (wireListSum tWires δ : ℤ)) * φ_add δ = _
    rw [htWires_on_β β hzero, hφ_a, dyadicTurn_add]
    congr 1
    have hS_eq : regVal rMidPG δ + bitsVal (fun j ↦ δ (uWires j)) + (δ wCin0).val =
        ((regVal rPG β) / 2 ^ s) % 2 ^ (4 - s) + uLow (fun i ↦ β (rSys i)) := by
      rw [hmid_reg_in β, add_assoc, huLow_on_β β hzero]
    rw [hS_eq]
    simp
  · let δ := symStepFwdList out.steps (f_xor_fwd β)
    obtain ⟨_, hreg_a⟩ := hval_add δ (hgid_zero_β₂ β hzero)
    dsimp only [Function.comp_apply]
    rw [hpg_xor_eq f_mid β]
    have hreg_m : regVal rPG (f_mid (f_xor_fwd β)) = regVal rPG (f_add δ) :=
      regVal_congr rPG fun j ↦
        hM_mid (f_xor_fwd β) (rPG j) ((QRegister.mem_image rPG _).mpr ⟨j, rfl⟩)
    rw [hreg_m, regVal_after_midSlice7 s hs rPG f_add δ (hp_add0.outside δ),
      hpg_reg_in β, hreg_a, hmid_reg_in β, add_assoc, huLow_on_β β hzero]
    rfl

end UnsealForestDynSec3B

private def rSlot0In36 : QRegister 18 36 := QRegister.block 0 18 (by decide)
private def rPartnerIn36 : QRegister 18 36 := QRegister.block 18 18 (by decide)
private def rSys36In43 : QRegister 36 (36 + 7) := QRegister.block 0 36 (by decide)
private def rPG7In43 : QRegister 7 (36 + 7) := QRegister.block 36 7 (by decide)

private theorem rSlot0In36_disj_rPartnerIn36 : rSlot0In36.DisjointWires rPartnerIn36 :=
  QRegister.block_disjoint_of_le 0 18 18 18 (by decide) (by decide) (by decide)

private theorem rSys36In43_disj_rPG7In43 : rSys36In43.DisjointWires rPG7In43 :=
  QRegister.block_disjoint_of_le 0 36 36 7 (by decide) (by decide) (by decide)

private def sel25Slot0In43 : QRegister (18 + 7) (36 + 7) :=
  (rSys36In43.compose rSlot0In36).concat rPG7In43
    (rSys36In43_disj_rPG7In43.compose_left rSlot0In36)

private def sel25PartnerIn43 : QRegister (18 + 7) (36 + 7) :=
  (rSys36In43.compose rPartnerIn36).concat rPG7In43
    (rSys36In43_disj_rPG7In43.compose_left rPartnerIn36)

private theorem embedUnitary_addLow4PG7Unitary_subSys
    (rSub : QRegister 18 36) (f : BitAssignment 18 → ℕ) :
    ((rSys36In43.compose rSub).concat rPG7In43
      (rSys36In43_disj_rPG7In43.compose_left rSub)).embedUnitary (addLow4PG7Unitary 18 f) =
      addLow4PG7Unitary 36 (fun γ ↦ f (fun i ↦ γ (rSub i))) := by
  have hWhole : rSys36In43.concat rPG7In43 rSys36In43_disj_rPG7In43 =
      QRegister.whole (36 + 7) := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [rSys36In43])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rPG7In43])
  rw [← QRegister.whole_embedUnitary (addLow4PG7Unitary 36 _), ← hWhole]
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  unfold addLow4PG7Unitary
  rw [embedUnitary_genCatPhasePermUnitary_mulVec_basisKet,
      embedUnitary_genCatPhasePermUnitary_mulVec_basisKet]
  rfl

private inductive Slot0Elem43 : Unitary (2 ^ (36 + 7)) → Prop where
  | reg (u18 : Unitary (2 ^ 18)) :
      Slot0Elem43 ((rSys36In43.compose rSlot0In36).embedUnitary u18)
  | low4 (f : BitAssignment 18 → ℕ) :
      Slot0Elem43 (addLow4PG7Unitary 36 (fun γ ↦ f (fun i ↦ γ (rSlot0In36 i))))
  | mul {X₁ X₂} : Slot0Elem43 X₁ → Slot0Elem43 X₂ → Slot0Elem43 (X₁ * X₂)

private inductive PartnerElem43 : Unitary (2 ^ (36 + 7)) → Prop where
  | reg (u18 : Unitary (2 ^ 18)) :
      PartnerElem43 ((rSys36In43.compose rPartnerIn36).embedUnitary u18)
  | low4 (g : BitAssignment 18 → ℕ) :
      PartnerElem43 (addLow4PG7Unitary 36 (fun γ ↦ g (fun i ↦ γ (rPartnerIn36 i))))
  | mul {Y₁ Y₂} : PartnerElem43 Y₁ → PartnerElem43 Y₂ → PartnerElem43 (Y₁ * Y₂)

private theorem partnerElem43_comm_slot0Elem43 {Y X : Unitary (2 ^ (36 + 7))}
    (hY : PartnerElem43 Y) (hX : Slot0Elem43 X) : Y * X = X * Y := by
  have hDisjPP : (rSys36In43.compose rPartnerIn36).DisjointWires
      (rSys36In43.compose rSlot0In36) :=
    disjointWires_compose_of_disjoint rSys36In43 (QRegExt.disjointWires_symm
      rSlot0In36_disj_rPartnerIn36)
  have hDisjP_S25 : (rSys36In43.compose rPartnerIn36).DisjointWires sel25Slot0In43 :=
    (QRegExt.disjointWires_symm (disjointWires_concat_left _ (QRegExt.disjointWires_symm hDisjPP)
      (QRegExt.disjointWires_symm (rSys36In43_disj_rPG7In43.compose_left rPartnerIn36))))
  have hDisjP25_S : sel25PartnerIn43.DisjointWires (rSys36In43.compose rSlot0In36) :=
    disjointWires_concat_left _ hDisjPP
      (QRegExt.disjointWires_symm (rSys36In43_disj_rPG7In43.compose_left rSlot0In36))
  induction hY generalizing X with
  | reg uP =>
      induction hX with
      | reg u0 =>
          exact Subtype.ext (QRegister.embedMatrix_comm_of_disjoint _ _ hDisjPP uP.1 u0.1)
      | low4 f =>
          rw [← embedUnitary_addLow4PG7Unitary_subSys rSlot0In36 f]
          exact Subtype.ext (QRegister.embedMatrix_comm_of_disjoint _ _ hDisjP_S25 uP.1 _)
      | mul _ _ ih₁ ih₂ =>
          calc (rSys36In43.compose rPartnerIn36).embedUnitary uP * (_ * _)
              = ((rSys36In43.compose rPartnerIn36).embedUnitary uP * _) * _ :=
                  (_root_.mul_assoc _ _ _).symm
            _ = (_ * (rSys36In43.compose rPartnerIn36).embedUnitary uP) * _ := by rw [ih₁]
            _ = _ * ((rSys36In43.compose rPartnerIn36).embedUnitary uP * _) :=
                  _root_.mul_assoc _ _ _
            _ = _ * (_ * (rSys36In43.compose rPartnerIn36).embedUnitary uP) := by rw [ih₂]
            _ = (_ * _) * (rSys36In43.compose rPartnerIn36).embedUnitary uP :=
                  (_root_.mul_assoc _ _ _).symm
  | low4 g =>
      induction hX with
      | reg u0 =>
          rw [← embedUnitary_addLow4PG7Unitary_subSys rPartnerIn36 g]
          exact Subtype.ext (QRegister.embedMatrix_comm_of_disjoint _ _ hDisjP25_S _ u0.1)
      | low4 f =>
          rw [addLow4PG7Unitary_mul, addLow4PG7Unitary_mul]
          congr 1; funext γ
          exact Nat.add_comm _ _
      | mul _ _ ih₁ ih₂ =>
          calc addLow4PG7Unitary 36 _ * (_ * _)
              = (addLow4PG7Unitary 36 _ * _) * _ := (_root_.mul_assoc _ _ _).symm
            _ = (_ * addLow4PG7Unitary 36 _) * _ := by rw [ih₁]
            _ = _ * (addLow4PG7Unitary 36 _ * _) := _root_.mul_assoc _ _ _
            _ = _ * (_ * addLow4PG7Unitary 36 _) := by rw [ih₂]
            _ = (_ * _) * addLow4PG7Unitary 36 _ := (_root_.mul_assoc _ _ _).symm
  | mul _ _ ihY₁ ihY₂ =>
      calc (_ * _) * X
          = _ * (_ * X) := _root_.mul_assoc _ _ X
        _ = _ * (X * _) := by rw [ihY₂ hX]
        _ = (_ * X) * _ := (_root_.mul_assoc _ X _).symm
        _ = (X * _) * _ := by rw [ihY₁ hX]
        _ = X * (_ * _) := _root_.mul_assoc X _ _

private theorem seq_interleave_43 {Y₁ Y₂ X₁ X₂ : Unitary (2 ^ (36 + 7))}
    (hY₁ : PartnerElem43 Y₁) (hX₂ : Slot0Elem43 X₂) :
    (Y₂ * Y₁) * (X₂ * X₁) = (Y₂ * X₂) * (Y₁ * X₁) := by
  calc (Y₂ * Y₁) * (X₂ * X₁)
      = Y₂ * ((Y₁ * X₂) * X₁) := by simp only [_root_.mul_assoc]
    _ = Y₂ * ((X₂ * Y₁) * X₁) := by rw [partnerElem43_comm_slot0Elem43 hY₁ hX₂]
    _ = (Y₂ * X₂) * (Y₁ * X₁) := by simp only [_root_.mul_assoc]

private def StageFactorPair (S₁ S₂ : CanonStageSpec128) : Prop :=
  ∃ (u25 : Unitary (2 ^ (18 + 7))) (u43 : Unitary (2 ^ (36 + 7))) (c₁ c₂ : ℂ),
    Slot0Elem43 (sel25Slot0In43.embedUnitary u25) ∧
    PartnerElem43 (sel25PartnerIn43.embedUnitary u25) ∧
    sel25PartnerIn43.embedUnitary u25 * sel25Slot0In43.embedUnitary u25 = u43 ∧
    S₁.uCat.1 = c₁ • (sel25InCat.embedUnitary u25).1 ∧
    S₂.uCat.1 = c₂ • (sel43InQft.embedUnitary u43).1

private theorem StageFactorPair.congr_left {S₁ S₂ : CanonStageSpec128}
    {uEff' : Unitary (2 ^ (3924 + 3))} {tCost' : ℕ}
    (hu : S₁.uEff = uEff') (ht : S₁.tCost = tCost')
    (h : StageFactorPair S₁ S₂) : StageFactorPair (S₁.congr hu ht) S₂ := h

private theorem StageFactorPair.congr_right {S₁ S₂ : CanonStageSpec128}
    {uEff' : Unitary (2 ^ (3924 + 3))} {tCost' : ℕ}
    (hu : S₂.uEff = uEff') (ht : S₂.tCost = tCost')
    (h : StageFactorPair S₁ S₂) : StageFactorPair S₁ (S₂.congr hu ht) := h

private theorem StageFactorPair.seq {A₁ A₂ B₁ B₂ : CanonStageSpec128}
    (hA : StageFactorPair A₁ A₂) (hB : StageFactorPair B₁ B₂) :
    StageFactorPair (A₁.seq B₁) (A₂.seq B₂) := by
  obtain ⟨u25A, u43A, c₁A, c₂A, hSA, hPA, hProdA, hc₁A, hc₂A⟩ := hA
  obtain ⟨u25B, u43B, c₁B, c₂B, hSB, hPB, hProdB, hc₁B, hc₂B⟩ := hB
  refine ⟨u25B * u25A, u43B * u43A, c₁B * c₁A, c₂B * c₂A, ?_, ?_, ?_, ?_, ?_⟩
  · rw [QRegister.embedUnitary_mul]
    exact Slot0Elem43.mul hSB hSA
  · rw [QRegister.embedUnitary_mul]
    exact PartnerElem43.mul hPB hPA
  · rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
        seq_interleave_43 hPA hSB, hProdB, hProdA]
  · change (B₁.uCat * A₁.uCat).1 = _
    rw [Submonoid.coe_mul, hc₁B, hc₁A, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        QRegister.embedUnitary_mul, Submonoid.coe_mul]
  · change (B₂.uCat * A₂.uCat).1 = _
    rw [Submonoid.coe_mul, hc₂B, hc₂A, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        QRegister.embedUnitary_mul, Submonoid.coe_mul]

private theorem embedUnitary_list_prod {A B : ℕ} (r : QRegister A B)
    (L : List (Unitary (2 ^ A))) :
    r.embedUnitary L.prod = (L.map r.embedUnitary).prod := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      rw [List.prod_cons, r.embedUnitary_mul, List.map_cons, List.prod_cons, ih]

private theorem ofFn6_prod_eq_mul_ofFn3 {M : Type*} [Monoid M] (G : Fin 6 → M) :
    (List.ofFn G).prod =
      (List.ofFn fun i : Fin 3 ↦ G ⟨i.val, by omega⟩).prod *
        (List.ofFn fun i : Fin 3 ↦ G ⟨3 + i.val, by omega⟩).prod := by
  have h3L : List.ofFn (fun i : Fin 3 ↦ G ⟨i.val, by omega⟩) = [G 0, G 1, G 2] := rfl
  have h3R : List.ofFn (fun i : Fin 3 ↦ G ⟨3 + i.val, by omega⟩) = [G 3, G 4, G 5] := rfl
  have h6 : List.ofFn G = [G 0, G 1, G 2, G 3, G 4, G 5] := rfl
  rw [h6, h3L, h3R]
  simp only [List.prod_cons, List.prod_nil, _root_.mul_assoc, mul_one]

private theorem stageFactorPair_ofAxisPrefixCircuit
    (c6 : Circuit 6) (u6 : Unitary 64) (t6 : ℕ)
    (hToff6 : c6.count TOFF = 0) (hToffInv6 : c6.inverse.count TOFF = 0)
    (hT6 : c6.count T = t6) (hTInv6 : c6.inverse.count T = t6)
    (heval6 : c6.eval = u6) :
    StageFactorPair
      (CanonStageSpec128.ofAxisPrefixCircuit 3 hL3_le_654
        c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6)
      (CanonStageSpec128.ofAxisPrefixCircuit 6 hL6_le_654
        c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6) := by
  let rAx18 : Fin 3 → QRegister 6 18 := fun i ↦
    QRegister.block (6 * i.val) 6 (by have := i.isLt; omega)
  let r18In25 : QRegister 18 (18 + 7) := QRegister.block 0 18 (by decide)
  let rAx43 : Fin 6 → QRegister 6 (36 + 7) := fun a ↦
    QRegister.block (6 * a.val) 6 (by have := a.isLt; omega)
  let u18 : Unitary (2 ^ 18) := (List.ofFn fun i : Fin 3 ↦ (rAx18 i).embedUnitary u6).prod
  let u25 : Unitary (2 ^ (18 + 7)) := r18In25.embedUnitary u18
  let u43 : Unitary (2 ^ (36 + 7)) := (List.ofFn fun a : Fin 6 ↦ (rAx43 a).embedUnitary u6).prod
  have hCompS : sel25Slot0In43.compose r18In25 = rSys36In43.compose rSlot0In36 := by
    apply qreg_ext; intro i
    rw [QRegister.compose_apply, sel25Slot0In43]
    have hi : r18In25 i = Fin.castAdd 7 i := Fin.ext (by simp [r18In25])
    rw [hi, QRegister.concat_apply_left]
  have hCompP : sel25PartnerIn43.compose r18In25 = rSys36In43.compose rPartnerIn36 := by
    apply qreg_ext; intro i
    rw [QRegister.compose_apply, sel25PartnerIn43]
    have hi : r18In25 i = Fin.castAdd 7 i := Fin.ext (by simp [r18In25])
    rw [hi, QRegister.concat_apply_left]
  have hEmbS : sel25Slot0In43.embedUnitary u25 =
      (rSys36In43.compose rSlot0In36).embedUnitary u18 := by
    dsimp only [u25]
    rw [← QRegister.embedUnitary_compose, hCompS]
  have hEmbP : sel25PartnerIn43.embedUnitary u25 =
      (rSys36In43.compose rPartnerIn36).embedUnitary u18 := by
    dsimp only [u25]
    rw [← QRegister.embedUnitary_compose, hCompP]
  have hSlot0Elem : Slot0Elem43 (sel25Slot0In43.embedUnitary u25) := by
    rw [hEmbS]; exact Slot0Elem43.reg u18
  have hPartnerElem : PartnerElem43 (sel25PartnerIn43.embedUnitary u25) := by
    rw [hEmbP]; exact PartnerElem43.reg u18
  refine ⟨u25, u43, 1, 1, hSlot0Elem, hPartnerElem, ?_, ?_, ?_⟩
  · rw [partnerElem43_comm_slot0Elem43 hPartnerElem hSlot0Elem, hEmbS, hEmbP]
    dsimp only [u18, u43]
    rw [embedUnitary_list_prod, embedUnitary_list_prod, List.map_ofFn, List.map_ofFn,
        ofFn6_prod_eq_mul_ofFn3]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg List.prod (congrArg List.ofFn (funext fun i ↦ ?_))
      dsimp only [Function.comp_apply]
      rw [← QRegister.embedUnitary_compose]
      refine congrArg (fun r : QRegister 6 _ ↦ r.embedUnitary u6) (qreg_ext fun q ↦ Fin.ext ?_)
      simp [rSys36In43, rSlot0In36, rAx18, rAx43]
    · refine congrArg List.prod (congrArg List.ofFn (funext fun i ↦ ?_))
      dsimp only [Function.comp_apply]
      rw [← QRegister.embedUnitary_compose]
      refine congrArg (fun r : QRegister 6 _ ↦ r.embedUnitary u6) (qreg_ext fun q ↦ Fin.ext ?_)
      have hi := i.isLt; have hq := q.isLt
      simp [rSys36In43, rPartnerIn36, rAx18, rAx43]
      omega
  · rw [one_smul]
    apply congrArg Subtype.val
    change rIdInCat.embedUnitary (List.ofFn fun i : Fin 3 ↦
        (rAxisPrefix 3 hL3_le_654 i).embedUnitary u6).prod =
      sel25InCat.embedUnitary (r18In25.embedUnitary
        (List.ofFn fun i : Fin 3 ↦ (rAx18 i).embedUnitary u6).prod)
    rw [← QRegister.embedUnitary_compose, embedUnitary_list_prod, embedUnitary_list_prod,
        List.map_ofFn, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i ↦ ?_))
    dsimp only [Function.comp_apply]
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
    refine congrArg (fun r : QRegister 6 _ ↦ r.embedUnitary u6) (qreg_ext fun q ↦ Fin.ext ?_)
    have hi := i.isLt; have hq := q.isLt
    have hL : ((rIdInCat.compose (rAxisPrefix 3 hL3_le_654 i)) q).val = 6 * i.val + q.val := by
      simp [rIdInCat, rAxisPrefix, rAxis654]
    have hR : (((sel25InCat.compose r18In25).compose (rAx18 i)) q).val = 6 * i.val + q.val := by
      rw [QRegister.compose_apply, QRegister.compose_apply, sel25InCat]
      have hlt : (r18In25 (rAx18 i q)).val < 18 := by
        simp [r18In25, rAx18]; omega
      have hcast : r18In25 (rAx18 i q) = Fin.castAdd 7 ⟨(r18In25 (rAx18 i q)).val, hlt⟩ :=
        Fin.ext rfl
      rw [hcast, QRegister.concat_apply_left]
      simp [r18In25, rAx18, sel18InSys, rIdInCat]
    omega
  · rw [one_smul]
    apply congrArg Subtype.val
    change rIdInCat.embedUnitary (List.ofFn fun a : Fin 6 ↦
        (rAxisPrefix 6 hL6_le_654 a).embedUnitary u6).prod =
      sel43InQft.embedUnitary (List.ofFn fun a : Fin 6 ↦ (rAx43 a).embedUnitary u6).prod
    rw [embedUnitary_list_prod, embedUnitary_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun a ↦ ?_))
    dsimp only [Function.comp_apply]
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
    refine congrArg (fun r : QRegister 6 _ ↦ r.embedUnitary u6) (qreg_ext fun q ↦ Fin.ext ?_)
    have ha := a.isLt; have hq := q.isLt
    have hL : ((rIdInCat.compose (rAxisPrefix 6 hL6_le_654 a)) q).val = 6 * a.val + q.val := by
      simp [rIdInCat, rAxisPrefix, rAxis654]
    have hR : ((sel43InQft.compose (rAx43 a)) q).val = 6 * a.val + q.val := by
      rw [QRegister.compose_apply, sel43InQft]
      have hlt : (rAx43 a q).val < 36 := by simp [rAx43]; omega
      have hcast : rAx43 a q = Fin.castAdd 7 ⟨(rAx43 a q).val, hlt⟩ := Fin.ext rfl
      rw [hcast, QRegister.concat_apply_left]
      simp [rAx43]
    omega

private theorem stageFactorPair_stageHPrefix (kf : Fin 6) :
    StageFactorPair
      (stageHPrefixCanonStage128 3 hL3_le_654 kf)
      (stageHPrefixCanonStage128 6 hL6_le_654 kf) := by
  unfold stageHPrefixCanonStage128
  exact StageFactorPair.congr_right _ _ (StageFactorPair.congr_left _ _
    (stageFactorPair_ofAxisPrefixCircuit (Circuit.H kf) (wireHadamard6 kf) 0
      (by fin_cases kf <;> decide) (by fin_cases kf <;> decide)
      (by fin_cases kf <;> decide) (by fin_cases kf <;> decide) rfl))

private theorem stageFactorPair_stageW16Prefix (k : Fin 5) :
    StageFactorPair
      (stageW16PrefixCanonStage128 3 hL3_le_654 k)
      (stageW16PrefixCanonStage128 6 hL6_le_654 k) := by
  unfold stageW16PrefixCanonStage128
  exact StageFactorPair.congr_right _ _ (StageFactorPair.congr_left _ _
    (stageFactorPair_ofAxisPrefixCircuit (w16AxisCircuit k) (diag6Unitary (w16Exp6 k)) 1
      (by fin_cases k <;> decide) (by fin_cases k <;> decide)
      (by fin_cases k <;> decide) (by fin_cases k <;> decide) (w16AxisCircuit_eval k)))

private theorem stageFactorPair_xorForestBatch (s tB₁ tB₂ : ℕ) (cfg : ForestSlotConfig s)
    (φ6 : Fin 64 → ℤ) (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u)
    (hs : s ≤ 3) (hL3 : 1 ≤ 3) (hoff3 : 0 + 3 ≤ 654)
    (hw₁ : xorForestBatchWork s cfg 3 ≤ 128) (ht₁ : xorForestBatchTCost s cfg 3 = tB₁)
    (hL6 : 1 ≤ 6) (hoff6 : 0 + 6 ≤ 654)
    (hw₂ : xorForestBatchWork s cfg 6 ≤ 128) (ht₂ : xorForestBatchTCost s cfg 6 = tB₂) :
    StageFactorPair
      (xorForestBatchExpStage128 s 0 3 tB₁ cfg φ6 hφ6 hs hL3 hoff3 hw₁ ht₁)
      (xorForestBatchCanonStage128 s 0 6 tB₂ cfg φ6 hφ6 hs hL6 hoff6 hw₂ ht₂) := by
  let f18 : BitAssignment 18 → ℕ :=
    fun γ ↦ ∑ l : Fin 3, forestAxisNat s cfg (fun q ↦ γ (idxForestAx18 l q))
  let f36 : BitAssignment 36 → ℕ :=
    fun γ ↦ ∑ l : Fin 6, forestAxisNat s cfg (fun q ↦ γ (idxAx36 l q))
  let u25 : Unitary (2 ^ (18 + 7)) := addLow4PG7Unitary 18 f18
  let u43 : Unitary (2 ^ (36 + 7)) := addLow4PG7Unitary 36 f36
  have hEmbS : sel25Slot0In43.embedUnitary u25 =
      addLow4PG7Unitary 36 (fun γ ↦ f18 (fun i ↦ γ (rSlot0In36 i))) :=
    embedUnitary_addLow4PG7Unitary_subSys rSlot0In36 f18
  have hEmbP : sel25PartnerIn43.embedUnitary u25 =
      addLow4PG7Unitary 36 (fun γ ↦ f18 (fun i ↦ γ (rPartnerIn36 i))) :=
    embedUnitary_addLow4PG7Unitary_subSys rPartnerIn36 f18
  have hSlot0Elem : Slot0Elem43 (sel25Slot0In43.embedUnitary u25) := by
    rw [hEmbS]; exact Slot0Elem43.low4 f18
  have hPartnerElem : PartnerElem43 (sel25PartnerIn43.embedUnitary u25) := by
    rw [hEmbP]; exact PartnerElem43.low4 f18
  have hProd : sel25PartnerIn43.embedUnitary u25 * sel25Slot0In43.embedUnitary u25 = u43 := by
    rw [hEmbP, hEmbS, addLow4PG7Unitary_mul]
    dsimp only [u43]
    congr 1; funext γ
    dsimp only [f18, f36]
    have hL : ∀ l : Fin 3,
        (fun q : Fin 6 ↦ γ (rSlot0In36 (idxForestAx18 l q))) =
          (fun q : Fin 6 ↦ γ (idxAx36 ⟨l.val, by have := l.isLt; omega⟩ q)) := fun l ↦ by
      funext q
      exact congrArg γ (Fin.ext (by simp [rSlot0In36, idxForestAx18, idxAx36]))
    have hR : ∀ l : Fin 3,
        (fun q : Fin 6 ↦ γ (rPartnerIn36 (idxForestAx18 l q))) =
          (fun q : Fin 6 ↦ γ (idxAx36 ⟨3 + l.val, by have := l.isLt; omega⟩ q)) := fun l ↦ by
      funext q
      apply congrArg γ; apply Fin.ext
      have := l.isLt; have := q.isLt
      simp [rPartnerIn36, idxForestAx18, idxAx36]
      omega
    have hSum3 : ∀ g : Fin 3 → ℕ, (∑ l : Fin 3, g l) = g 0 + g 1 + g 2 := fun g ↦ by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
      simp only [add_zero, add_assoc]
      rfl
    have hSum6 : ∀ g : Fin 6 → ℕ, (∑ l : Fin 6, g l) =
        g 0 + g 1 + g 2 + g 3 + g 4 + g 5 := fun g ↦ by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
          Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
      simp only [add_zero, add_assoc]
      rfl
    rw [hSum3, hSum3, hSum6, hR 0, hR 1, hR 2, hL 0, hL 1, hL 2]
    have e0 : (⟨(0 : Fin 3).val, by omega⟩ : Fin 6) = 0 := rfl
    have e1 : (⟨(1 : Fin 3).val, by omega⟩ : Fin 6) = 1 := rfl
    have e2 : (⟨(2 : Fin 3).val, by omega⟩ : Fin 6) = 2 := rfl
    have e3 : (⟨3 + (0 : Fin 3).val, by omega⟩ : Fin 6) = 3 := rfl
    have e4 : (⟨3 + (1 : Fin 3).val, by omega⟩ : Fin 6) = 4 := rfl
    have e5 : (⟨3 + (2 : Fin 3).val, by omega⟩ : Fin 6) = 5 := rfl
    rw [e0, e1, e2, e3, e4, e5]
    omega
  have hRF18_0 := xorForestBatchFwd_realizes_addLow4 () s cfg 3 hs hL3
    (le_refl (xorForestBatchWork s cfg 3))
    (rSysCanon128.compose sel18InSys) rPGCanon128
    (rWorkCanon128.slice 0 (xorForestBatchWork s cfg 3) (Nat.zero_add _ ▸ hw₁))
    (rSysCanon128_disjoint_rPGCanon128.compose_left sel18InSys)
    ((rSysCanon128_disjoint_rWorkCanon128.compose_left sel18InSys).compose_right _)
    (rPGCanon128_disjoint_rWorkCanon128.compose_right _)
    idxForestAx18 idxForestAx18_inj
  rw [← xorForestBatchFwdDyn128_0_3_eq s cfg hs hL3 hoff3 hw₁] at hRF18_0
  have hRF25 := (realizes_congr_slice (Nat.zero_add _ ▸ hw₁)
    concat_sel18InSys_rPGCanon128_eq hRF18_0).widenActive
  obtain ⟨c₁, hc₁⟩ := realizes_eq_smul_of_same rQftCanon128_disjoint_rWorkCanon128
    (xorForestBatchExpStage128 s 0 3 tB₁ cfg φ6 hφ6 hs hL3 hoff3 hw₁ ht₁).hRealFwd hRF25
  have hDyn6 : xorForestBatchFwdDyn128 s 0 6 cfg hs hL6 hoff6 hw₂ =
      StageAPointPhase128OnStep.xorForestBatchFwdDyn () s cfg 6 hs hL6
        (le_refl (xorForestBatchWork s cfg 6))
        rSys36Canon rPGCanon128
        (rWorkCanon128.slice 0 (xorForestBatchWork s cfg 6) (Nat.zero_add _ ▸ hw₂))
        rSys36Canon_disj_rPGCanon128
        ((rQftCanon128_disjoint_rWorkCanon128.compose_left _).compose_right _)
        (rPGCanon128_disjoint_rWorkCanon128.compose_right _)
        idxAx36 idxAx36_inj := by
    unfold xorForestBatchFwdDyn128
    refine xorForestBatchFwdDyn_congr_sys () s cfg 6 hs hL6 _
      rSysCanon128 rSys36Canon rPGCanon128 _ _ _ _ _ _
      (idxForestAx 0 6 hoff6) (idxForestAx_inj 0 6 hoff6) idxAx36 idxAx36_inj fun l q ↦ ?_
    dsimp only [rSysCanon128, rSys36Canon, QRegister.compose_apply]
    exact congrArg rQftCanon128
      (Fin.ext (by simp [rIdInCat, idxForestAx, idxAx36]))
  have hRF36_0 := xorForestBatchFwd_realizes_addLow4 () s cfg 6 hs hL6
    (le_refl (xorForestBatchWork s cfg 6))
    rSys36Canon rPGCanon128
    (rWorkCanon128.slice 0 (xorForestBatchWork s cfg 6) (Nat.zero_add _ ▸ hw₂))
    rSys36Canon_disj_rPGCanon128
    ((rQftCanon128_disjoint_rWorkCanon128.compose_left _).compose_right _)
    (rPGCanon128_disjoint_rWorkCanon128.compose_right _)
    idxAx36 idxAx36_inj
  rw [← hDyn6] at hRF36_0
  have hRF43 := (realizes_congr_slice (Nat.zero_add _ ▸ hw₂)
    rSys36Canon_concat_rPGCanon128_eq hRF36_0).widenActive
  obtain ⟨c₂, hc₂⟩ := realizes_eq_smul_of_same rQftCanon128_disjoint_rWorkCanon128
    (xorForestBatchCanonStage128 s 0 6 tB₂ cfg φ6 hφ6 hs hL6 hoff6 hw₂ ht₂).hRealFwd hRF43
  exact ⟨u25, u43, c₁, c₂, hSlot0Elem, hPartnerElem, hProd, hc₁, hc₂⟩

private theorem stageFactorPair_activeQft :
    StageFactorPair activeOneElecExpQftStage128 activeTwoElecForestFullQftStage128 := by
  have hC5 : StageFactorPair stagePointCrossExpC5
      (stageW16PrefixCanonStage128 6 hL6_le_654 4) :=
    stageFactorPair_stageW16Prefix 4
  have hC4 : StageFactorPair stagePointCrossExpC4
      ((stageW16PrefixCanonStage128 6 hL6_le_654 3).seq activeTwoElecSlot3Stage128) :=
    (stageFactorPair_stageW16Prefix 3).seq
      (stageFactorPair_xorForestBatch 3 10 15 forestCfg3 forestExp3 forestCfg3_exp_eq
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
  have hC3 : StageFactorPair stagePointCrossExpC3
      ((stageW16PrefixCanonStage128 6 hL6_le_654 2).seq activeTwoElecSlot2Stage128) :=
    (stageFactorPair_stageW16Prefix 2).seq
      (stageFactorPair_xorForestBatch 2 27 54 forestCfg2 forestExp2 forestCfg2_exp_eq
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
  have hC2 : StageFactorPair stagePointCrossExpC2
      ((stageW16PrefixCanonStage128 6 hL6_le_654 1).seq activeTwoElecSlot1Stage128) :=
    (stageFactorPair_stageW16Prefix 1).seq
      (stageFactorPair_xorForestBatch 1 39 78 forestCfg1 forestExp1 forestCfg1_exp_eq
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
  have hC1 : StageFactorPair stagePointCrossExpC1
      ((stageW16PrefixCanonStage128 6 hL6_le_654 0).seq activeTwoElecSlot0Stage128) :=
    (stageFactorPair_stageW16Prefix 0).seq
      (stageFactorPair_xorForestBatch 0 26 44 forestCfg0 forestExp0 forestCfg0_exp_eq
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
  unfold activeOneElecExpQftStage128 activeTwoElecForestFullQftStage128
  refine StageFactorPair.congr_right _ _ (StageFactorPair.congr_left _ _ ?_)
  unfold rawActiveOneElecExpQftStage128 rawActiveTwoElecForestQftStage128
  exact ((stageFactorPair_stageHPrefix 5).seq hC5).seq
    (((stageFactorPair_stageHPrefix 4).seq hC4).seq
      (((stageFactorPair_stageHPrefix 3).seq hC3).seq
        (((stageFactorPair_stageHPrefix 2).seq hC2).seq
          (((stageFactorPair_stageHPrefix 1).seq hC1).seq
            (stageFactorPair_stageHPrefix 0)))))

private theorem selCatInCoreSum42PG7_sel25_left (q : Fin 18) :
    (selCatInCoreSum42PG7 (sel25InCat (Fin.castAdd 7 q))).val = q.val := by
  have hq25 : sel25InCat (Fin.castAdd 7 q) = Fin.castAdd 7 (sel18InSys q) := by
    change ((rIdInCat.compose sel18InSys).concat rPGInCat _) (Fin.castAdd 7 q) =
      Fin.castAdd 7 (sel18InSys q)
    rw [QRegister.concat_apply_left]
    exact Fin.ext (by simp [sel18InSys, rIdInCat])
  rw [hq25]
  unfold selCatInCoreSum42PG7
  dsimp only
  rw [QRegister.concat_apply_left, QRegister.compose_apply, qreg_block_apply]
  let i0 : Fin 3924 := ⟨q.val, by have := q.isLt; omega⟩
  have hSel : sel18InSys.wires q = ⟨i0.val, by have := i0.isLt; omega⟩ := by
    ext; simp [i0, sel18InSys]
  dsimp only
  rw [zero_add, hSel]
  exact coreElecCosetB1Block_elec_val PosSlots24SemanticBridge.pos24_6_le_80 i0

private theorem selCatInCoreSum42PG7_sel25_right (m : Fin 7) :
    (selCatInCoreSum42PG7 (sel25InCat (Fin.natAdd 18 m))).val =
      fullSysCoreWires 80 + 42 + m.val := by
  have hm25 : sel25InCat (Fin.natAdd 18 m) = Fin.natAdd (3924 + 3) m := by
    change ((rIdInCat.compose sel18InSys).concat rPGInCat _) (Fin.natAdd 18 m) =
      Fin.natAdd (3924 + 3) m
    rw [QRegister.concat_apply_right]
    exact Fin.ext (by simp [rPGInCat])
  rw [hm25]
  unfold selCatInCoreSum42PG7
  dsimp only
  rw [QRegister.concat_apply_right, qreg_block_apply]

private theorem rCat0InActB42_compose_sel25InCat :
    rCat0InActB42.compose sel25InCat =
      (rCatSlot0Partner.compose sel43InQft).compose sel25Slot0In43 := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun q ↦ ?_) (fun m ↦ ?_) idx
  · apply Fin.ext
    rw [QRegister.compose_apply, rCat0InActB42, QRegister.compose_apply,
        selDataInAct_apply, Fin.val_castAdd]
    refine Eq.trans (selCatInCoreSum42PG7_sel25_left q) ?_
    have hRHS : sel43InQft (sel25Slot0In43 (Fin.castAdd 7 q)) =
        Fin.castAdd 7 ⟨q.val, by have := q.isLt; omega⟩ := by
      rw [sel25Slot0In43, QRegister.concat_apply_left, sel43InQft]
      have hlt : ((rSys36In43.compose rSlot0In36) q).val < 36 := by
        have := q.isLt; simp [rSys36In43, rSlot0In36]; omega
      have hc : (rSys36In43.compose rSlot0In36) q = Fin.castAdd 7 ⟨_, hlt⟩ := Fin.ext rfl
      rw [hc, QRegister.concat_apply_left]
      exact Fin.ext (by simp [rSys36In43, rSlot0In36])
    rw [QRegister.compose_apply, QRegister.compose_apply, hRHS,
        rCatSlot0Partner, QRegister.concat_apply_left, rIdSlot0Partner_apply,
        dite_eq_left q.isLt, rElec0InActB42_apply]
  · apply Fin.ext
    rw [QRegister.compose_apply, rCat0InActB42, QRegister.compose_apply,
        selDataInAct_apply, Fin.val_castAdd]
    refine Eq.trans (selCatInCoreSum42PG7_sel25_right m) ?_
    have hRHS : sel43InQft (sel25Slot0In43 (Fin.natAdd 18 m)) = Fin.natAdd (3924 + 3) m := by
      rw [sel25Slot0In43, QRegister.concat_apply_right, sel43InQft]
      have hm43 : rPG7In43 m = Fin.natAdd 36 m :=
        Fin.ext (by simp [rPG7In43])
      rw [hm43, QRegister.concat_apply_right]
      exact Fin.ext (by simp)
    rw [QRegister.compose_apply, QRegister.compose_apply, hRHS,
        rCatSlot0Partner, QRegister.concat_apply_right, rPG7InActB42_apply,
        posCoreWires_eq_fullSysCoreWires80]

private theorem rCatPartnerInActB42_compose_sel25InCat :
    rCatPartnerInActB42.compose sel25InCat =
      (rCatSlot0Partner.compose sel43InQft).compose sel25PartnerIn43 := by
  have hCoreEq : fullSysCoreWires 80 = posCoreWires := rfl
  apply qreg_ext; intro idx
  refine Fin.addCases (fun q ↦ ?_) (fun m ↦ ?_) idx
  · apply Fin.ext
    have hqVal := selCatInCoreSum42PG7_sel25_left q
    let jCat := selCatInCoreSum42PG7 (sel25InCat (Fin.castAdd 7 q))
    have hLtCS : jCat.val < fullSysCoreWires 80 + 42 := by
      have := q.isLt; have := posCoreWires_eq_4034; omega
    have hjCS : jCat = Fin.castAdd 7 ⟨jCat.val, hLtCS⟩ := Fin.ext rfl
    have hLtC : jCat.val < fullSysCoreWires 80 := by
      have := q.isLt; have := posCoreWires_eq_4034; omega
    have hjC : (⟨jCat.val, hLtCS⟩ : Fin (fullSysCoreWires 80 + 42)) =
        Fin.castAdd 42 ⟨jCat.val, hLtC⟩ := Fin.ext rfl
    have hSlot : (⟨jCat.val, hLtC⟩ : Fin (fullSysCoreWires 80)) = rSlot0InCore q :=
      Fin.ext (by rw [rSlot0InCore, rFullSysElecSlot_val]; simpa using hqVal)
    have hLHS : rCatPartnerInActB42 (sel25InCat (Fin.castAdd 7 q)) = rPartner18InActB42 q := by
      dsimp only [jCat] at hjCS
      rw [rCatPartnerInActB42, QRegister.compose_apply, hjCS, QRegister.concat_apply_left,
          hjC, QRegister.concat_apply_left, hSlot, rCorePartnerInActB42,
          rDataSubstSlot0_apply_slot0]
    have hRHS : sel43InQft (sel25PartnerIn43 (Fin.castAdd 7 q)) =
        Fin.castAdd 7 ⟨18 + q.val, by have := q.isLt; omega⟩ := by
      rw [sel25PartnerIn43, QRegister.concat_apply_left, sel43InQft]
      have hlt : ((rSys36In43.compose rPartnerIn36) q).val < 36 := by
        have := q.isLt; simp [rSys36In43, rPartnerIn36]; omega
      have hc : (rSys36In43.compose rPartnerIn36) q = Fin.castAdd 7 ⟨_, hlt⟩ := Fin.ext rfl
      rw [hc, QRegister.concat_apply_left]
      exact Fin.ext (by simp [rSys36In43, rPartnerIn36])
    rw [QRegister.compose_apply, hLHS, QRegister.compose_apply, QRegister.compose_apply, hRHS,
        rCatSlot0Partner, QRegister.concat_apply_left, rIdSlot0Partner_apply]
    have hNot0 : ¬ (18 + q.val < 18) := by omega
    have hLt36 : 18 + q.val < 36 := by have := q.isLt; omega
    simp only [hNot0, hLt36, ↓reduceDIte]
    exact congrArg Fin.val (congrArg rPartner18InActB42 (Fin.ext (by dsimp only; omega)))
  · apply Fin.ext
    have hmVal := selCatInCoreSum42PG7_sel25_right m
    let jCat := selCatInCoreSum42PG7 (sel25InCat (Fin.natAdd 18 m))
    have hjPG : jCat = Fin.natAdd (fullSysCoreWires 80 + 42) m :=
      Fin.ext (by simpa [Fin.val_natAdd] using hmVal)
    have hLHS : rCatPartnerInActB42 (sel25InCat (Fin.natAdd 18 m)) = rPG7InActB42 m := by
      dsimp only [jCat] at hjPG
      rw [rCatPartnerInActB42, QRegister.compose_apply, hjPG, QRegister.concat_apply_right]
    have hRHS : sel43InQft (sel25PartnerIn43 (Fin.natAdd 18 m)) = Fin.natAdd (3924 + 3) m := by
      rw [sel25PartnerIn43, QRegister.concat_apply_right, sel43InQft]
      have hm43 : rPG7In43 m = Fin.natAdd 36 m :=
        Fin.ext (by simp [rPG7In43])
      rw [hm43, QRegister.concat_apply_right]
      exact Fin.ext (by simp)
    rw [QRegister.compose_apply, hLHS, QRegister.compose_apply, QRegister.compose_apply, hRHS,
        rCatSlot0Partner, QRegister.concat_apply_right]

/-- Exact operator equality across all `128` `rPG7` basis states: the factored single-electron
`QFT_64` product `uQftPExpInActB42 * uQft0ExpInActB42` equals the `2`-electron Hadamard-Forest
`QFT_64` unitary `rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat`. -/
private theorem uQftPExpInActB42_mul_uQft0ExpInActB42_eq :
    uQftPExpInActB42 * uQft0ExpInActB42 =
      rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat := by
  obtain ⟨u25, u43, c₁, c₂, _, _, hProd43, hc₁, hc₂⟩ := stageFactorPair_activeQft
  have hc₂_norm : star c₂ * c₂ = 1 := by
    let U := activeTwoElecForestFullQftStage128.uCat
    let V := sel43InQft.embedUnitary u43
    have hUU : star U.1 * U.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
    have hVV : star V.1 * V.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp V.2
    have hMat : (1 : Operator (2 ^ (3924 + 3 + 7))) =
        (star c₂ * c₂) • (1 : Operator (2 ^ (3924 + 3 + 7))) := by
      calc (1 : Operator (2 ^ (3924 + 3 + 7)))
          = star U.1 * U.1 := hUU.symm
        _ = star (c₂ • V.1) * (c₂ • V.1) := by rw [hc₂]
        _ = (star c₂ • star V.1) * (c₂ • V.1) := by rw [star_smul]
        _ = (star c₂ * c₂) • (star V.1 * V.1) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        _ = (star c₂ * c₂) • 1 := by rw [hVV]
    have h00 := congrFun (congrFun hMat 0) 0
    simpa using h00.symm
  have hu43_smul : (sel43InQft.embedUnitary u43).1 =
      star c₂ • activeTwoElecForestFullQftStage128.uCat.1 := by
    rw [hc₂, smul_smul, hc₂_norm, one_smul]
  have h0_smul : uQft0ExpInActB42.1 =
      c₁ • ((rCatSlot0Partner.compose sel43InQft).embedUnitary
        (sel25Slot0In43.embedUnitary u25)).1 := by
    unfold uQft0ExpInActB42
    rw [QRegister.embedUnitary_val, hc₁, rCat0InActB42.embedMatrix_smul,
        QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
        rCat0InActB42_compose_sel25InCat,
        QRegister.embedMatrix_compose, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  have hP_smul : uQftPExpInActB42.1 =
      c₁ • ((rCatSlot0Partner.compose sel43InQft).embedUnitary
        (sel25PartnerIn43.embedUnitary u25)).1 := by
    unfold uQftPExpInActB42
    rw [QRegister.embedUnitary_val, hc₁, rCatPartnerInActB42.embedMatrix_smul,
        QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
        rCatPartnerInActB42_compose_sel25InCat,
        QRegister.embedMatrix_compose, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  let c_tot : ℂ := (c₁ * c₁) * star c₂
  have hMulSmul : (uQftPExpInActB42 * uQft0ExpInActB42).1 =
      c_tot • (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat).1 := by
    rw [Submonoid.coe_mul, hP_smul, h0_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, hProd43,
        QRegister.embedUnitary_val, QRegister.embedMatrix_compose, ← QRegister.embedUnitary_val,
        hu43_smul, QRegister.embedMatrix_smul, smul_smul, QRegister.embedUnitary_val]
  have hc_tot_one : c_tot = 1 := by
    have hStreamSmul : (uStageBOpenQftStreamInner 1 (le_refl 1) (by decide) false).1 =
        c_tot • (uStageBTwoElecStreamInner 1 (le_refl 1) (by decide) false).1 := by
      unfold uStageBOpenQftStreamInner uStageBTwoElecStreamInner
      simp only [Submonoid.coe_mul, hMulSmul, Matrix.smul_mul, Matrix.mul_smul]
    have hCatEq := uStageBOpenQftStreamInner_mul_catState7_eq 1 (le_refl 1) (by decide) false
    rw [hStreamSmul, embedMatrix_catState7_eq, Matrix.smul_mul] at hCatEq
    let U_cl := uStageBTwoElecStreamInner 1 (le_refl 1) (by decide) false
    let U_cat := rPG7InActB42.embedUnitary (U_cat_B_normalized 7)
    let P0 := rPG7InActB42.basisOutcomeProjector 0
    have hCancel : (U_cat⁻¹).1 * ((U_cl⁻¹).1 * (U_cl.1 * (U_cat.1 * P0))) = P0 := by
      calc (U_cat⁻¹).1 * ((U_cl⁻¹).1 * (U_cl.1 * (U_cat.1 * P0)))
          = (U_cat⁻¹).1 * (((U_cl⁻¹ * U_cl).1) * (U_cat.1 * P0)) := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = ((U_cat⁻¹ * U_cat).1) * P0 := by
              rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul,
                  Submonoid.coe_mul, Matrix.mul_assoc]
        _ = P0 := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
    have hP0Smul : c_tot • P0 = P0 := by
      have h1 := congrArg (fun M ↦ (U_cat⁻¹).1 * ((U_cl⁻¹).1 * M)) hCatEq
      dsimp only [U_cl, U_cat, P0] at h1
      rwa [Matrix.mul_smul, Matrix.mul_smul, hCancel] at h1
    let g0 : Fin (2 ^ (kStageBData + 18)) := rPG7InActB42.replaceIndex 0 0
    have hP0_g0 : P0 g0 g0 = 1 := by
      dsimp only [P0, g0]
      rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_apply_eq,
          rPG7InActB42.extractIndex_replaceIndex, ite_eq_left rfl]
    have hg0 := congrFun (congrFun hP0Smul g0) g0
    rw [Matrix.smul_apply, smul_eq_mul, hP0_g0, mul_one] at hg0
    exact hg0
  apply Subtype.ext
  rw [hMulSmul, hc_tot_one, one_smul]

/-- Unconditional equality of the open-QFT Stage-B inner stream unitary and the closed-QFT
two-electron stream unitary `uStageBTwoElecStreamInner`. -/
theorem uStageBOpenQftStreamInner_eq_uStageBTwoElecStreamInner
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    uStageBOpenQftStreamInner B hB1 hB27 slot2SwappedTo0 =
      uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0 := by
  unfold uStageBOpenQftStreamInner uStageBTwoElecStreamInner
  rw [uQftPExpInActB42_mul_uQft0ExpInActB42_eq]

/-! ### Part B: Outer Open-QFT Two-Load Stage-B Anchor Wrappers (`-164 T` vs Closed) -/

private theorem uQft0ExpInActB42_inv_eq :
    uQft0ExpInActB42⁻¹ = (rCat0InActB42.compose sel25InCat).embedUnitary uExpQft25⁻¹ := by
  unfold uQft0ExpInActB42
  rw [activeOneElecExpQftStage128_uCat_eq_sel25, ← QRegister.embedUnitary_compose,
      ← QRegister.embedUnitary_inv]

private theorem rCat0InActB42_sel25_range_weak (t : Fin (18 + 7)) :
    ((rCat0InActB42.compose sel25InCat) t).val < 18 ∨
      posCoreWires ≤ ((rCat0InActB42.compose sel25InCat) t).val := by
  rw [QRegister.compose_apply]
  rcases rCat0InActB42_sel25_range t with h0 | ⟨hGe, _⟩
  · exact Or.inl h0
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) hGe)

private theorem selSubstWithPartner_uQft0ExpInv_comm_P_slot0 :
    (selSubstWithPartner.embedUnitary uQft0ExpInActB42⁻¹).1 *
      P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) =
    P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) *
      (selSubstWithPartner.embedUnitary uQft0ExpInActB42⁻¹).1 := by
  let s := rCat0InActB42.compose sel25InCat
  let rCoreOrig := (selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor
  have hCoreOrig_val : ∀ k : Fin posCoreWires, (rCoreOrig k).val = k.val := fun k ↦ by
    simp [rCoreOrig, selCoreInDataAnchor, selDataInAct_apply,
      selCoreInCoreSum42PG7]
  have hDisj : (selSubstWithPartner.compose s).DisjointWires rCoreOrig := by
    rw [QRegister.disjoint_iff]
    intro t k h
    have hv := congrArg Fin.val h
    rw [QRegister.compose_apply, hCoreOrig_val k] at hv
    have hge := selSubstWithPartner_val_ge_posCoreWires (s t) (rCat0InActB42_sel25_range_weak t)
    have hk := k.isLt
    omega
  rw [uQft0ExpInActB42_inv_eq, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      P_slot0_shiftedPartnerLens218_eq]
  exact QRegister.embedMatrix_comm_of_disjoint _ rCoreOrig hDisj (uExpQft25⁻¹).1 _

private theorem elec3924Preserved_selSubst_uQft0ExpInv :
    Elec3924Preserved selCoreInDataAnchor
      (selSubstWithPartner.embedUnitary uQft0ExpInActB42⁻¹) := by
  let s := rCat0InActB42.compose sel25InCat
  rw [uQft0ExpInActB42_inv_eq, ← QRegister.embedUnitary_compose]
  refine elec3924Preserved_of_disjoint_embed selCoreInDataAnchor (selSubstWithPartner.compose s)
    ?_ uExpQft25⁻¹
  rw [QRegister.disjoint_iff]
  intro t i h
  have h4034 := posCoreWires_eq_4034
  have hv := congrArg Fin.val h
  rw [QRegister.compose_apply, rElecInAct_selCoreInDataAnchor_val i] at hv
  have hge := selSubstWithPartner_val_ge_posCoreWires (s t) (rCat0InActB42_sel25_range_weak t)
  have hi := i.isLt
  omega

private theorem actPreservesShifted17_selSubst_uQft0ExpInv :
    ActPreservesShifted17 selCoreInDataAnchor
      (selSubstWithPartner.embedUnitary uQft0ExpInActB42⁻¹) := by
  let s := rCat0InActB42.compose sel25InCat
  let sel17 := (BoothOpt_StageBPartnerCoreShave.selDataInAct (kStageBData + 18)).compose
    (selShiftedIdx17 selCoreInDataAnchor)
  have hSel17_lt : ∀ i : Fin 17, (sel17 i).val < posCoreWires := fun i ↦ by
    dsimp only [sel17, selShiftedIdx17, QRegister.compose_apply]
    rw [BoothOpt_StageBPartnerCoreShave.selDataInAct_apply, Fin.val_castAdd,
      selCoreInDataAnchor_val_eq]
    exact (rShiftedIdx17OfFin i).isLt
  intro xy y hnz
  rw [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractIndex_compose_eq,
      BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractIndex_compose_eq]
  rw [uQft0ExpInActB42_inv_eq, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      QRegister.embedMatrix_apply] at hnz
  split_ifs at hnz with henv
  · apply (basisBits 17).injective
    funext i
    change basisBits 17 (sel17.extractIndex y) i = basisBits 17 (sel17.extractIndex xy) i
    rw [sel17.basisBits_extractIndex, sel17.basisBits_extractIndex]
    exact (((selSubstWithPartner.compose s).basisSplit_environment_eq_iff y xy).mp henv)
      (sel17 i) fun ⟨t, ht⟩ ↦
        Nat.not_lt.mpr (selSubstWithPartner_val_ge_posCoreWires (s t)
          (rCat0InActB42_sel25_range_weak t))
          (congrArg Fin.val ht ▸ hSel17_lt i)
  · exact absurd (mul_zero _) hnz

private theorem selSubstWithPartner_uJunctionRawInActB42_comm_P_slot :
    (selSubstWithPartner.embedUnitary uJunctionRawInActB42).1 *
      P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) =
    P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) *
      (selSubstWithPartner.embedUnitary uJunctionRawInActB42).1 := by
  unfold uJunctionRawInActB42
  rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, Matrix.mul_assoc,
      selSubstWithPartner_uQft0ExpInv_comm_P_slot0, ← Matrix.mul_assoc,
      selSubstWithPartner_uAdd0InActB42_comm_P_slot0, Matrix.mul_assoc]

theorem elec3924Preserved_selSubst_uJunctionRawInActB42 :
    Elec3924Preserved selCoreInDataAnchor
      (selSubstWithPartner.embedUnitary uJunctionRawInActB42) := by
  unfold uJunctionRawInActB42
  rw [QRegister.embedUnitary_mul]
  exact elec3924Preserved_mul selCoreInDataAnchor
    elec3924Preserved_selSubst_uAdd0InActB42 elec3924Preserved_selSubst_uQft0ExpInv

theorem actPreservesShifted17_selSubst_uJunctionRawInActB42 :
    ActPreservesShifted17 selCoreInDataAnchor
      (selSubstWithPartner.embedUnitary uJunctionRawInActB42) := by
  unfold uJunctionRawInActB42
  rw [QRegister.embedUnitary_mul]
  exact actPreservesShifted17_mul selCoreInDataAnchor
    actPreservesShifted17_selSubst_uAdd0InActB42 actPreservesShifted17_selSubst_uQft0ExpInv

def selAncPG7InDA : QRegister (18 + 7) (kStageBData + 18) :=
  (selMeasInAct kStageBData).concat ((selDataInAct kStageBData).compose selPG7InCoreSum42PG7)
    (QRegExt.disjointWires_symm ((selDataInAct_disj_selMeasInAct kStageBData).compose_left
      selPG7InCoreSum42PG7))

noncomputable def uQft0AncPG7 : Unitary (2 ^ (kStageBData + 18)) :=
  selAncPG7InDA.embedUnitary uExpQft25

noncomputable def uJunctionRawAncPG7 : Unitary (2 ^ (kStageBData + 18)) :=
  uAdd0AncPG7 * uQft0AncPG7⁻¹

private theorem selSubstWithPartner_uQft0ExpInActB42_eq_selDataInAct_uQft0AncPG7 :
    selSubstWithPartner.embedUnitary uQft0ExpInActB42 =
      (selDataInAct (kStageBData + 18)).embedUnitary uQft0AncPG7 := by
  unfold uQft0ExpInActB42 uQft0AncPG7
  rw [activeOneElecExpQftStage128_uCat_eq_sel25,
      ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
      ← QRegister.embedUnitary_compose]
  refine congrArg (fun r : QRegister (18 + 7) ((kStageBData + 18) + 18) ↦
    r.embedUnitary uExpQft25) ?_
  apply p3_qreg_ext; intro idx
  rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.compose_apply]
  refine Fin.addCases (fun q ↦ ?_) (fun m ↦ ?_) idx
  · rw [selAncPG7InDA, QRegister.concat_apply_left]
    have h4083 := kStageBData_eq_4083
    have hq := q.isLt
    have hVal : (rCat0InActB42 (sel25InCat (Fin.castAdd 7 q))).val = q.val := by
      rw [rCat0InActB42, QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd]
      exact selCatInCoreSum42PG7_sel25_left q
    have hCast : (rCat0InActB42 (sel25InCat (Fin.castAdd 7 q)) : Fin (kStageBData + 18)) =
        Fin.castAdd 18 ⟨q.val, by omega⟩ := Fin.ext hVal
    erw [hCast, selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply]
    apply Fin.ext
    simp [selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply, hq, selMeasInAct_apply]
  · rw [selAncPG7InDA, QRegister.concat_apply_right]
    have h4034 := posCoreWires_eq_4034
    have h4083 := kStageBData_eq_4083
    have hmLt := m.isLt
    have hVal : (rCat0InActB42 (sel25InCat (Fin.natAdd 18 m))).val =
        posCoreWires + 42 + m.val := by
      rw [rCat0InActB42, QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          posCoreWires_eq_fullSysCoreWires80]
      exact selCatInCoreSum42PG7_sel25_right m
    have hCast : (rCat0InActB42 (sel25InCat (Fin.natAdd 18 m)) : Fin (kStageBData + 18)) =
        Fin.castAdd 18 ⟨posCoreWires + 42 + m.val, by omega⟩ := Fin.ext hVal
    erw [hCast, selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply]
    apply Fin.ext
    have hge : ¬ posCoreWires + 42 + m.val < 18 := by omega
    rw [selDataInAct_apply, selDataInAct_apply, Fin.val_castAdd, Fin.val_castAdd,
        QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd]
    erw [selDataAnchorSubst_apply]
    rw [ite_eq_right hge]
    simp [selPG7InCoreSum42PG7]

private theorem selSubstWithPartner_uJunctionRawInActB42_eq_selDataI :
    selSubstWithPartner.embedUnitary uJunctionRawInActB42 =
      (selDataInAct (kStageBData + 18)).embedUnitary uJunctionRawAncPG7 := by
  unfold uJunctionRawInActB42 uJunctionRawAncPG7
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv,
      selSubstWithPartner_uAdd0InActB42_eq_selDataInAct_uAdd0AncPG7,
      selSubstWithPartner_uQft0ExpInActB42_eq_selDataInAct_uQft0AncPG7,
      ← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_mul]

noncomputable def uAnchorInnerOpenQft
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    Unitary (2 ^ ((kStageBData + 18) + 18)) :=
  uAnchorInner B hB1 hB27 slot2SwappedTo0 * selSubstWithPartner.embedUnitary uJunctionRawInActB42

theorem uAnchorInnerOpenQft_comm_P_slot0_shiftedPartner
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uAnchorInnerOpenQft B hB1 hB27 slot2SwappedTo0).1 *
      P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) =
    P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) *
      (uAnchorInnerOpenQft B hB1 hB27 slot2SwappedTo0).1 := by
  unfold uAnchorInnerOpenQft
  rw [Submonoid.coe_mul, Matrix.mul_assoc, selSubstWithPartner_uJunctionRawInActB42_comm_P_slot,
      ← Matrix.mul_assoc, uAnchorInner_comm_P_slot0_shiftedPartner, Matrix.mul_assoc]

theorem restrictOfCommSlot0_uAnchorInnerOpenQft_eq
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
      (uAnchorInnerOpenQft B hB1 hB27 slot2SwappedTo0)
      (uAnchorInnerOpenQft_comm_P_slot0_shiftedPartner B hB1 hB27 slot2SwappedTo0) =
    restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
      (uAnchorInner B hB1 hB27 slot2SwappedTo0)
      (uAnchorInner_comm_P_slot0_shiftedPartner B hB1 hB27 slot2SwappedTo0) * uJunctionRawAncPG7 :=
        by
  have hRestrMul := restrictOfCommSlot0_mul (shiftedPartnerLens218 selCoreInDataAnchor)
    (uAnchorInner B hB1 hB27 slot2SwappedTo0) (selSubstWithPartner.embedUnitary
      uJunctionRawInActB42)
    (uAnchorInner_comm_P_slot0_shiftedPartner B hB1 hB27 slot2SwappedTo0)
    selSubstWithPartner_uJunctionRawInActB42_comm_P_slot
  change restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
      (uAnchorInner B hB1 hB27 slot2SwappedTo0 *
        selSubstWithPartner.embedUnitary uJunctionRawInActB42)
      _ = _
  rw [hRestrMul]
  refine congrArg (restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
    (uAnchorInner B hB1 hB27 slot2SwappedTo0)
    (uAnchorInner_comm_P_slot0_shiftedPartner B hB1 hB27 slot2SwappedTo0) * ·) ?_
  refine restrictOfCommSlot0_eq_of_intertwine (shiftedPartnerLens218 selCoreInDataAnchor)
    (selSubstWithPartner.embedUnitary uJunctionRawInActB42)
    selSubstWithPartner_uJunctionRawInActB42_comm_P_slot uJunctionRawAncPG7 ?_
  have hSwapEq : uLensSwap (shiftedPartnerLens218 selCoreInDataAnchor) =
      (liftDataMeas selCoreInDataAnchor).embedUnitary (uLensSwap shiftedPartnerCoreLens218) :=
    (embedUnitary_liftDataMeas_uLensSwap selCoreInDataAnchor shiftedPartnerCoreLens218).symm
  have hDisjSum : ((selDataInAct (kStageBData + 18)).compose selAncSum42InDA).DisjointWires
      (liftDataMeas selCoreInDataAnchor) := by
    have h4034 := posCoreWires_eq_4034
    have h4083 := kStageBData_eq_4083
    rw [QRegister.disjoint_iff]
    intro i j
    refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) i <;>
      refine Fin.addCases (fun jc ↦ ?_) (fun jm ↦ ?_) j <;> intro h
    · have hv := congrArg Fin.val h
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          selAncSum42InDA, QRegister.concat_apply_left, selMeasInAct_apply, Fin.val_natAdd,
          liftDataMeas, QRegister.concat_apply_left, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, selCoreInDataAnchor_val_eq] at hv
      have := jc.isLt; omega
    · have hv := congrArg Fin.val h
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          selAncSum42InDA, QRegister.concat_apply_left, selMeasInAct_apply, Fin.val_natAdd,
          liftDataMeas, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd] at hv
      have := q.isLt; omega
    · have hv := congrArg Fin.val h
      have hsVal : (selSum42InCoreSum42PG7 s).val = posCoreWires + s.val := by
        simp [selSum42InCoreSum42PG7]
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          selAncSum42InDA, QRegister.concat_apply_right, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, hsVal,
          liftDataMeas, QRegister.concat_apply_left, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, selCoreInDataAnchor_val_eq] at hv
      have := jc.isLt; omega
    · have hv := congrArg Fin.val h
      have hsVal : (selSum42InCoreSum42PG7 s).val = posCoreWires + s.val := by
        simp [selSum42InCoreSum42PG7]
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          selAncSum42InDA, QRegister.concat_apply_right, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, hsVal,
          liftDataMeas, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd] at hv
      have := s.isLt; omega
  have hDisjPG : ((selDataInAct (kStageBData + 18)).compose selAncPG7InDA).DisjointWires
      (liftDataMeas selCoreInDataAnchor) := by
    have h4034 := posCoreWires_eq_4034
    have h4083 := kStageBData_eq_4083
    rw [QRegister.disjoint_iff]
    intro i j
    refine Fin.addCases (fun q ↦ ?_) (fun m ↦ ?_) i <;>
      refine Fin.addCases (fun jc ↦ ?_) (fun jm ↦ ?_) j <;> intro h
    · have hv := congrArg Fin.val h
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          selAncPG7InDA, QRegister.concat_apply_left, selMeasInAct_apply, Fin.val_natAdd,
          liftDataMeas, QRegister.concat_apply_left, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, selCoreInDataAnchor_val_eq] at hv
      have := jc.isLt; omega
    · have hv := congrArg Fin.val h
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          selAncPG7InDA, QRegister.concat_apply_left, selMeasInAct_apply, Fin.val_natAdd,
          liftDataMeas, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd] at hv
      have := q.isLt; omega
    · have hv := congrArg Fin.val h
      have hmVal : (selPG7InCoreSum42PG7 m).val = posCoreWires + 42 + m.val := by
        simp [selPG7InCoreSum42PG7]
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          selAncPG7InDA, QRegister.concat_apply_right, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, hmVal,
          liftDataMeas, QRegister.concat_apply_left, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, selCoreInDataAnchor_val_eq] at hv
      have := jc.isLt; omega
    · have hv := congrArg Fin.val h
      have hmVal : (selPG7InCoreSum42PG7 m).val = posCoreWires + 42 + m.val := by
        simp [selPG7InCoreSum42PG7]
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
          selAncPG7InDA, QRegister.concat_apply_right, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, hmVal,
          liftDataMeas, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd] at hv
      have := m.isLt; omega
  have hCommAdd : ((selDataInAct (kStageBData + 18)).embedUnitary uAdd0AncPG7).1 *
      (uLensSwap (shiftedPartnerLens218 selCoreInDataAnchor)).1 =
      (uLensSwap (shiftedPartnerLens218 selCoreInDataAnchor)).1 *
      ((selDataInAct (kStageBData + 18)).embedUnitary uAdd0AncPG7).1 := by
    rw [hSwapEq]; unfold uAdd0AncPG7
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisjSum uElec18Sum42Add.1 _
  have hCommQftInv : ((selDataInAct (kStageBData + 18)).embedUnitary uQft0AncPG7⁻¹).1 *
      (uLensSwap (shiftedPartnerLens218 selCoreInDataAnchor)).1 =
      (uLensSwap (shiftedPartnerLens218 selCoreInDataAnchor)).1 *
      ((selDataInAct (kStageBData + 18)).embedUnitary uQft0AncPG7⁻¹).1 := by
    rw [hSwapEq]; unfold uQft0AncPG7
    rw [← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_compose,
        QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisjPG (uExpQft25⁻¹).1 _
  rw [Submonoid.coe_mul, selSubstWithPartner_uJunctionRawInActB42_eq_selDataI]
  unfold uJunctionRawAncPG7
  rw [QRegister.embedUnitary_mul, Submonoid.coe_mul]
  refine congrArg (· * _) ?_
  rw [Matrix.mul_assoc, hCommQftInv, ← Matrix.mul_assoc, hCommAdd, Matrix.mul_assoc]

theorem rCoreSwapPG3Sum42PG7Full_selPG7 (off : ℕ) (hoff : off + 3 ≤ 41) (m : Fin 7) :
    rCoreSwapPG3Sum42PG7Full off hoff (selPG7InCoreSum42PG7 m) = rPG7Full m := by
  have hm : selPG7InCoreSum42PG7 m = Fin.natAdd (fullSysCoreWires 80 + 42) m := by
    ext
    simp [selPG7InCoreSum42PG7, posCoreWires_eq_fullSysCoreWires80]
  rw [hm, rCoreSwapPG3Sum42PG7Full, QRegister.concat_apply_right]

private theorem liftDataMeas_rCoreSwapPG3Sum42PG7Full_uQft0AncPG7
    (off : ℕ) (hoff : off + 3 ≤ 41) :
    (liftDataMeas (rCoreSwapPG3Sum42PG7Full off hoff)).embedUnitary uQft0AncPG7 =
      uQft0AncFull18 := by
  let rSw : QRegister kStageBData kFull80 := rCoreSwapPG3Sum42PG7Full off hoff
  change (liftDataMeas rSw).embedUnitary uQft0AncPG7 = uQft0AncFull18
  unfold uQft0AncPG7 uQft0AncFull18
  rw [← QRegister.embedUnitary_compose]
  refine congrArg (·.embedUnitary uExpQft25) (p3_qreg_ext fun idx ↦ ?_)
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun q ↦ ?_) (fun m ↦ ?_) idx
  · rw [selAncPG7InDA, QRegister.concat_apply_left,
        selAncPG7InFull18, QRegister.concat_apply_left]
    have hq : selMeasInAct kStageBData q = Fin.natAdd kStageBData q :=
      selMeasInAct_apply q
    rw [hq, liftDataMeas, QRegister.concat_apply_right]
  · rw [selAncPG7InDA, QRegister.concat_apply_right, QRegister.compose_apply,
        selAncPG7InFull18, QRegister.concat_apply_right, QRegister.compose_apply]
    have hm : selDataInAct kStageBData (selPG7InCoreSum42PG7 m) =
        Fin.castAdd 18 (selPG7InCoreSum42PG7 m) :=
      selDataInAct_apply _
    rw [hm, liftDataMeas, QRegister.concat_apply_left, QRegister.compose_apply]
    exact congrArg (selDataInAct kFull80) (rCoreSwapPG3Sum42PG7Full_selPG7 off hoff m)

theorem liftDataMeas_rCoreSwapPG3Sum42PG7Full_uJunctionRawAn
    (off : ℕ) (hoff : off + 3 ≤ 41) :
    (liftDataMeas (rCoreSwapPG3Sum42PG7Full off hoff)).embedUnitary uJunctionRawAncPG7 =
      uJunctionAncFull18 := by
  let rLift := liftDataMeas (rCoreSwapPG3Sum42PG7Full off hoff)
  have hInv : rLift.embedUnitary uQft0AncPG7⁻¹ = (rLift.embedUnitary uQft0AncPG7)⁻¹ := by
    apply Subtype.ext
    change rLift.embedMatrix (star uQft0AncPG7.1) = star (rLift.embedMatrix uQft0AncPG7.1)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
        QRegister.embedMatrix_conjTranspose]
  unfold uJunctionRawAncPG7 uJunctionAncFull18
  rw [QRegister.embedUnitary_mul, hInv,
      liftDataMeas_rCoreSwapPG3Sum42PG7Full_uAdd0AncPG7 off hoff,
      liftDataMeas_rCoreSwapPG3Sum42PG7Full_uQft0AncPG7 off hoff]

end Part3B_OpenQftOuter
end Part3_OpenTwoLoadStageB

/-! ## Section 4: Fused Open-QFT `FoldedPass123CircuitSpec_mWork` (`48054 -> 47617`, `-437 T`) -/

section Part4_FusedOpenFoldedBundle

open InterWalkRSum42Hoist (kFull80 rCoreFull)
open Barrel3PassSelectStitch (hm6_80)
open FusedPreDiagFromTwist288 (uPreDiagCliffordCore)
open BarrelPass2AndHeld3PassSelectStitch (uSingleBarrelFolded6Full)
open BoothOpt_Anchor218CachedTrueSwapOuter
  (uAnchorFrame uSlot0MeasSwap uBarrelFastAct uSlot0MeasSwap_mul_self uBarrelFastAct_mul_self
   uWrapPreDiagCliffordFull)

theorem uAnchorFrame_one : uAnchorFrame 1 = 1 := by
  unfold uAnchorFrame
  rw [QRegister.embedUnitary_one, mul_one]
  calc (uBarrelFastAct * uSlot0MeasSwap) * (uSlot0MeasSwap * uBarrelFastAct)
      = uBarrelFastAct * (uSlot0MeasSwap * uSlot0MeasSwap) * uBarrelFastAct := by
          simp only [_root_.mul_assoc]
    _ = uBarrelFastAct * uBarrelFastAct := by rw [uSlot0MeasSwap_mul_self, mul_one]
    _ = 1 := uBarrelFastAct_mul_self

theorem mul_intertwine_same {D : ℕ} {U₂ U₁ E V₂ V₁ : Operator D}
    (h₂ : U₂ * E = E * V₂) (h₁ : U₁ * E = E * V₁) :
    (U₂ * U₁) * E = E * (V₂ * V₁) := by
  calc (U₂ * U₁) * E = U₂ * (U₁ * E) := by simp only [Matrix.mul_assoc]
    _ = U₂ * (E * V₁) := by rw [h₁]
    _ = (U₂ * E) * V₁ := by simp only [Matrix.mul_assoc]
    _ = E * (V₂ * V₁) := by rw [h₂, Matrix.mul_assoc]

theorem uWrapPreDiagCliffordFull_mul (U₂ U₁ : Unitary (2 ^ kFull80)) :
    uWrapPreDiagCliffordFull (U₂ * U₁) =
      uWrapPreDiagCliffordFull U₂ * uWrapPreDiagCliffordFull U₁ := by
  unfold uWrapPreDiagCliffordFull
  have hMulInv : rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80) *
      rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹ = 1 := by
    rw [← QRegister.embedUnitary_mul, mul_inv_cancel, QRegister.embedUnitary_one]
  calc rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹ *
          (U₂ * U₁ * rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))
      = rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹ *
          (U₂ * (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80) *
            rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹) *
            U₁ * rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)) := by
          rw [hMulInv, mul_one]
    _ = rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹ *
          (U₂ * rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)) *
          (rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80)⁻¹ *
            (U₁ * rCoreFull.embedUnitary (uPreDiagCliffordCore hm6_80))) := by
          simp only [_root_.mul_assoc]

theorem uSingleBarrelFolded6Full_mul_one (U₁ U₂ : Unitary (2 ^ kFull80)) :
    uSingleBarrelFolded6Full (U₂ * U₁) 1 = uSingleBarrelFolded6Full U₁ U₂ := by
  unfold uSingleBarrelFolded6Full
  simp only [one_mul, _root_.mul_assoc]

end Part4_FusedOpenFoldedBundle

set_option exponentiation.threshold 256

end P1_OpenAnchorAdd0TwoLoad
end P1OpenAnchorAdd0TwoLoad
end QuantumComputation.Specs.StoppingPowerSolution
end
