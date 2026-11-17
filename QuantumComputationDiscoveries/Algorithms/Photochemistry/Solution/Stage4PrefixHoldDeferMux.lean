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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.MidTap29Coul18Stage4K2

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
scoped instance : NeZero 2 := ⟨two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances

open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18Leg1Pass
    (v1Fin8U10Local_eq_dualLeg v2Fin8U10Local_eq_dualLeg leg1DualLegPass84 leg2DualLegPass60)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18Leg1Pass
    (owLegsMidPkgDualLegOfMid)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (CoulOWScrPkg13 df8Of13
    ySampleK2 x13OfReg13 w11OfReg13 whiten13Tree whiten13Tree_check)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (stepCB_whiten13_lo7
    stepCB_whiten13_hi7 stepCB_whiten13_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA (WOptInj OptBasePred
    oneHotOptPreOp oneHotOptPreVec wLastSplitShiftDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA (count_wLastSplitShiftDyn
    dw_wLastSplitShiftDyn subspaceStep_wLastSplitShiftDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
    (mkKetOpW mkKetOpW_mulVec_ket mkKetOpW_congr natOfZModBits leg_dif_pos leg_dif_neg leg_if_pos)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (leg_if_neg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd (finBitsVal finBitsVal_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor (byteOfBits pPre304
    pAxis25 pHi13 embLo25 embHi25 axMap25 mapCP mapCP_fwd mapCP_fwd_apply)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor (mapCP_fwd_outside)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast (dynWires_wrapDynOnReg
    bennettXorReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu (subspaceStep_of_eq_post)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (ValidPotBFlags24
    rPotBWork24 wPotB24IsScreen wPotB24IsPot wPotB24IsNN rPotB24PortB r41Of24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (r41Of24_ctrl
    r41Of24_work r41Of24_lt81 validPotBFlags_r41Of24 potReflPortBSt24 potReflPortBPh0_24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (f41Of24 f41Of24_tag
    potOraclePortB24BitEval potOraclePortB24CoinEval potB24GateActive)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (rPotBCoin24 wPotB24LocQ
    wPotB24Sp1B0 wPotB24Sp1B1)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (wPotB24Sp2B0
    wPotB24Sp2B1 rPotB24NucA rPotB24ElecA)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOW58U10
    (midOWHi16U10TopPreK58Pkg_104)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17 (pre5OfPre6
    pre5OfPre6_pre6OfCoords)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep
    stepCB)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30 (validPre6Mask64
    ShortBin7Pre6Pkg pre6OfCoords pre6OfCoords_valid)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift (liftFinDyn_c70
    liftFinDyn_eq_c70)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
    (subspaceStep_wrapOnReg_mkKetOpW_mask2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotPortBMux
    (subspaceStep_wrapOnReg_block2 sbScr_lt6)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (stOWZ16 phOWZ16
    stOWZ16_outside stOWZ16_val ValidPotBFlags potBGateActive owCompose_disj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (owLeg2_coords_b2 ow0_lt5
    ow1_lt5 ow2_lt5 ow3_lt5 ow4_lt5)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt (ShortBin7CtrlSafe
    step_wrapUncopy24 dualDisj_copy_elec writeReg_self_z16_local)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt (z16AddVal_mod17_sum
    phAddVal_mod17_sum)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254 (finBitsVal_inj
    finBitsVal_eq_natOfZModBits)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ProviderCore (cw_1 cw_cnot dw_xUnload)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulombFast (subspaceStep_seq_u)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (speciesOfBits2
    wPotBLocQ wPotBIsScreen wPotBIsPot wPotBIsNN wPotBSp1B0 wPotBSp1B1 rPotBNucA)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (rPotBElecA rPotBPortB
    rPotBWork coordOfReg24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_of_circuit subspaceStep_congr_in subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg
    counts_wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (DynCtrlSafe
    ComputeProgCtrlSafe subspaceStep_of_eq_pre_local Wtop wtop_ge192 wtop_le_wp)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (wp_sub1_le_wtop
    IsNonNucPortB41Idx r41_ne r41_blk_ne_blk r41_blk_ne_wire r41_wire_ne_blk r41_blk_st)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (coordOfReg24_congr
    coordOfReg24_ite rMuxZ16 wMuxGate rMuxD2_18 rMuxM1 rMuxMid idxMuxMid rMuxCopy24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (idxMuxLeg1Hdr5
    idxMuxLeg1Hdr5_lt rMuxLeg1Hdr5 rMuxLeg1Hdr5_0_false rMuxLeg1Hdr5_1_false)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (rMuxLeg1Hdr5_2_false
    rMuxLeg1Hdr5_0_true rMuxLeg1Hdr5_1_true rMuxLeg1Hdr5_2_true rMuxLeg1Hdr5_3)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (rMuxLeg1Hdr5_4
    mux1Leg2_bit_eq_ite writeSub24 writeSub24_apply_out writeSub24_apply_reg wrapMux1Dist)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (ctrlSafe_wrapMux1Dist
    step_wrapMux1Dist wrapCopy24 ctrlSafe_wrapCopy24 step_wrapCopy24 wrapFlipLeg2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (ctrlSafe_wrapFlipLeg2
    step_wrapFlipLeg2 wrapGateCsel ctrlSafe_wrapGateCsel step_wrapGateCsel)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (wrapHdrCascade2
    ctrlSafe_wrapHdrCascade2 step_wrapHdrCascade2 muxDisj_m1_d2 gateWrapMux hdrWrapMux)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (hdrWrapMux_keep
    stOWZ16_apply_reg routed_or_of_validFlags z16AddVal phAddVal v1Mux v2Mux idxMuxMid_y)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (idxMuxMid_zLo idxMuxMid_zHi
    idxMuxMid_zHi' idxMuxMid_cln rMidZHi_rMuxMid muxD2Val muxD2Val_le)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (mux_le14_30
    natOfZModBits_of_testBit stepCB_apply_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Legs (v1U10Pre5
    v2U10Pre5 v1Fin8U10Local v2Fin8U10Local)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29 (MidOWTap29Pkg
    midOWTotalSumTap29 midOWZBitsTap29 midOWPostStTap29 midOWPhaseTap29)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2
    (midWTap29_eq_midWTap29OfMode owK2ReflPotSliceSpec24 idxC13Of41 idxC13Of41_bounds rC13Of41)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2 (rC13Of41_ne_of_outside
    rC13Of41_blk_ne_of_outside rC13Of41_lo7 rC13Of41_12 zLo14MuxK2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2 (zLo14MuxK2_lt y36MuxK2
    midSumMuxK2 z16AfterMidK2 phAfterMidK2 xorPortB41NotScr_midInvar_k2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2
    (mux_k2_final_eq_potRefl24 potExpectK2DualLegK17)
noncomputable section


namespace QuantumComputation.Specs.PhotochemistrySolution.DualSumCompact50K2

open scoped Matrix Circuit.Notation BigOperators
open Operator QProg Matrix Circuit Qubit PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket_X ket_CNOT)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (z1 z1_counts z1_dynWires
    z1_step cz2 cz2_counts cz2_dynWires cz2_step ungAdd_lt0 ungAdd_ltZ ungAdd_ltB)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (pUngatedAddCarryKick
    pUngatedAddCarryKick_counts pUngatedAddCarryKick_dynWires pUngatedAddCarryKick_step)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (wPair2 wPair2_wInj
    pSplit2Bracket counts_pSplit2Bracket ctrlSafe_pSplit2Bracket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (step_pSplit2Bracket
    stSplit2Fwd stSplit2Fwd_eq_of_bne stSplit2Fwd_of_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (upd4_eq_of_bne
    XorOp56 applyXorOp56 applyXorOps56 applyXorOp56_invol)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180
    (applyXorOp56_of_ne_tgt applyXorOp56_cnot_same applyXorOps56_eq_of_nonTgt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (applyXorOps56_of_lt
    Distinct5_56 sMaskFront5_22 cpFront5_22 cpFront5_22_vp)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (cpFront5_22_and
    sMaskFront5_22_ge17 sMaskBack16_52 cpBack16_52 cpBack16_52_vp)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (cpBack16_52_and
    sMaskBack16_52_ge34 idx52To56 opsInitA opsPostA opsPreSplits04)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (opsPostSplits04
    f56Front f56Front_zero_ge22 f56PreSplitA f56PostSplitA f56PostA)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (f56PreSplit0
    f56PreSplit1 f56PreSplit2 f56PreSplit3 f56PreSplit4 f56PostSplit4)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (f56PreBack
    f56PreBack_zero_ge38 eActSplitA eActSplit0 eActSplit1 eActSplit2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (eActSplit3 eActSplit4
    inv_f56PreSplitA inv_f56PreSplit0 inv_f56PreSplit1)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180 (inv_f56PreSplit2
    inv_f56PreSplit3 inv_f56PreSplit4 cz4Val52)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterCsaDual180
    (cpBack16_52_wrcsa_spec)
def fin52To56 (u : Fin 52) : Fin 56 := ⟨u.val, Nat.lt_trans u.isLt (by decide)⟩

theorem fin52To56_inj : Function.Injective fin52To56 := fun _ _ h ↦ Fin.ext (Fin.mk.inj h)

def emb52 (x : BitAssignment 52) : BitAssignment 56 := fun u ↦
    if h : u.val < 52 then x ⟨u.val, h⟩ else 0
def proj52 (y : BitAssignment 56) : BitAssignment 52 := fun u ↦ y (fin52To56 u)

def liftSt52 {n : ℕ} (rM : QRegister 52 n) (f56 : BitAssignment 56 → BitAssignment 56)
    (st : BitAssignment n → BitAssignment n) : BitAssignment n → BitAssignment n := fun δ ↦
    writeReg (st δ) rM
    (proj52 (f56 (emb52 (fun u ↦ st δ (rM u)))))
theorem liftSt52_f56Front_lt {n : ℕ} (rM : QRegister 52 n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) {u : Fin 52} (hu : u.val < 22) :
    liftSt52 rM f56Front st δ (rM u) =
      cpFront5_22.fwdBits (fun j : Fin 22 ↦ st δ (rM ⟨j.val, by omega⟩)) ⟨u.val, hu⟩ := by
  unfold liftSt52
  rw [writeReg_apply_reg]
  unfold proj52 f56Front emb52
  rw [_root_.dite_eq_left (show (fin52To56 u).val < 22 from hu)]
  exact congrFun (congrArg cpFront5_22.fwdBits
    (funext fun j ↦ _root_.dite_eq_left (Nat.lt_trans j.isLt (by decide)))) _

theorem liftSt52_f56Front_ge {n : ℕ} (rM : QRegister 52 n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) {u : Fin 52} (hu : ¬(u.val < 22)) : liftSt52 rM f56Front st δ (rM u) =
    st δ (rM u) := by
  unfold liftSt52
  rw [writeReg_apply_reg]
  unfold proj52 f56Front
  have h56 : ¬((fin52To56 u).val < 22) := hu
  rw [_root_.dite_eq_right h56]
  unfold emb52
  exact _root_.dite_eq_left u.isLt
def xorOp56Lt52 : XorOp56 → Bool
  | .x q => decide (q.val < 52)
  | .cnot c tg => decide (c.val < 52) && decide (tg.val < 52)

def circXorOp52 {n : ℕ} (rM : QRegister 52 n) : XorOp56 → Circuit n
  | .x q =>
      if hq : q.val < 52 then Circuit.X (rM ⟨q.val, hq⟩) else .identity
  | .cnot c tg =>
      if hc : c.val < 52 then
        if htg : tg.val < 52 then
          if hEq : (⟨c.val, hc⟩ : Fin 52) = ⟨tg.val, htg⟩ then .identity
          else Circuit.CNOT (rM ⟨c.val, hc⟩) (rM ⟨tg.val, htg⟩) (fun e ↦ hEq (rM.wires.injective e))
        else .identity
      else .identity

def wrapXorOp52 {Var : Type} {n : ℕ} (rM : QRegister 52 n) (op : XorOp56)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
    (DynamicCircuit.circuit (circXorOp52 rM op)).seq
    (mid.seq (DynamicCircuit.circuit (circXorOp52 rM op)))
def wrapXorOps52 {Var : Type} {n : ℕ} (rM : QRegister 52 n) :
    List XorOp56 → DynamicCircuit Var n → DynamicCircuit Var n
  | [], mid => mid
  | op :: rest, mid => wrapXorOp52 rM op (wrapXorOps52 rM rest mid)

theorem counts_wrapXorOp52 {Var : Type} {n : ℕ} (rM : QRegister 52 n) (op : XorOp56)
    (mid : DynamicCircuit Var n) : (wrapXorOp52 rM op mid).count .T = mid.count .T ∧
    (wrapXorOp52 rM op mid).count .TOFF = mid.count
    .TOFF := by
  cases op <;> dsimp [wrapXorOp52, circXorOp52, DynamicCircuit.count] <;> split_ifs <;>
    simp [Circuit.X, Circuit.CNOT]

theorem counts_wrapXorOps52 {Var : Type} {n : ℕ} (rM : QRegister 52 n) :
    ∀ (ops : List XorOp56) (mid : DynamicCircuit Var n),
      (wrapXorOps52 rM ops mid).count .T = mid.count .T ∧
      (wrapXorOps52 rM ops mid).count .TOFF = mid.count .TOFF
  | [], _ => ⟨rfl, rfl⟩
  | op :: rest, mid => by
      obtain ⟨t1, f1⟩ := counts_wrapXorOp52 rM op (wrapXorOps52 rM rest mid)
      obtain ⟨t2, f2⟩ := counts_wrapXorOps52 rM rest mid
      exact ⟨t1.trans t2, f1.trans f2⟩
theorem ctrlSafe_wrapXorOps52 {Var : Type} {n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (rM : QRegister 52 n) (hSM : ∀ u, S_ctrl (rM u) ∧ S_tgt (rM u)) (ops : List XorOp56)
    {mid : DynamicCircuit Var n}
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) : DynCtrlSafe S_ctrl S_tgt (wrapXorOps52 rM ops mid) := by
  induction ops with
  | nil => exact hMid
  | cons op rest ih =>
      have hCirc : DynCtrlSafe (Var := Var) S_ctrl S_tgt (.circuit (circXorOp52 rM op)) := by
        rcases op with q | ⟨c, tg⟩ <;> dsimp [circXorOp52] <;> split_ifs <;> first
          | exact .identity S_ctrl S_tgt
          | exact .of_dynWires (cw_1 (hSM ⟨q.val, ‹_›⟩)) (by simp [DynamicCircuit.count, Circuit.X])
          | exact .of_dynWires (cw_cnot (hSM ⟨c.val, ‹_›⟩) (hSM ⟨tg.val, ‹_›⟩))
              (by simp [DynamicCircuit.count, Circuit.CNOT])
      exact .seq hCirc (.seq ih hCirc)

theorem writeReg_upd52 {m n : ℕ} (r : QRegister m n) (β : BitAssignment n)
    (vals : Fin m → ZMod 2) (idx : Fin m) (v : ZMod 2) :
    Function.update (writeReg β r vals) (r idx) v = writeReg β r (Function.update vals idx v) :=
  PhotochemistrySolution.DeferMux2Wp198Opt.update_writeReg_reg β r vals idx v

theorem proj52_upd (y : BitAssignment 56) (idx : Fin 52) (v : ZMod 2) :
    proj52 (Function.update y (fin52To56 idx) v) = Function.update (proj52 y) idx v := by
  funext u
  by_cases hu : u = idx
  · subst hu
    simp [proj52]
  · simp [proj52, hu, show fin52To56 u ≠ fin52To56 idx from fun e ↦ hu (fin52To56_inj e)]

theorem circXorOp52_mul_liftSt52 {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n)
    (rM : QRegister 52 n) (op : XorOp56) (hop : xorOp56Lt52 op = true)
    (f56 : BitAssignment 56 → BitAssignment 56)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
        (circXorOp52 rM op).eval.1 * mkKetOpW rWork (liftSt52 rM f56 st) ph =
        mkKetOpW rWork (liftSt52 rM (fun x ↦ applyXorOp56 op (f56 x)) st) ph :=
    by
  apply matrix_ext_ket
  intro δ
  simp only [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
  by_cases hz : ∀ q, δ (rWork q) = 0
  · rw [_root_.ite_eq_left hz, _root_.ite_eq_left hz, Matrix.mulVec_smul]
    refine congrArg (_ • ·) ?_
    cases op with
    | x q =>
        have hq : q.val < 52 := of_decide_eq_true hop
        dsimp only [circXorOp52]
        rw [_root_.dite_eq_left hq, ket_X]
        dsimp only [liftSt52, applyXorOp56]
        rw [writeReg_apply_reg, writeReg_upd52, ← proj52_upd]
        dsimp only [proj52]
        rw [show fin52To56 ⟨q.val, hq⟩ = q from Fin.ext rfl]
    | cnot c tg =>
        rw [xorOp56Lt52, Bool.and_eq_true] at hop
        have hc : c.val < 52 := of_decide_eq_true hop.1
        have htg : tg.val < 52 := of_decide_eq_true hop.2
        have hc56 : fin52To56 ⟨c.val, hc⟩ = c := Fin.ext rfl
        have htg56 : fin52To56 ⟨tg.val, htg⟩ = tg := Fin.ext rfl
        dsimp only [circXorOp52]
        rw [_root_.dite_eq_left hc, _root_.dite_eq_left htg]
        by_cases hct52 : (⟨c.val, hc⟩ : Fin 52) = ⟨tg.val, htg⟩
        · rw [_root_.dite_eq_left hct52, Circuit.eval_identity, Submonoid.coe_one,
              Matrix.one_mulVec]
          simp [liftSt52, applyXorOp56, hc56.symm.trans ((congrArg fin52To56 hct52).trans htg56)]
        · rw [_root_.dite_eq_right hct52, ket_CNOT]
          dsimp only [liftSt52, applyXorOp56]
          simp only [show c ≠ tg from fun e ↦
              hct52 (fin52To56_inj (hc56.trans (e.trans htg56.symm))),
            ↓reduceIte, writeReg_apply_reg, writeReg_upd52, ← proj52_upd]
          dsimp only [proj52]
          rw [hc56, htg56]
  · rw [_root_.ite_eq_right hz, _root_.ite_eq_right hz, Matrix.mulVec_zero]

theorem step_wrapXorOps52 {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister W n) (rM : QRegister 52 n) (ops : List XorOp56)
    (hops : (ops.all xorOp56Lt52) = true)
    (f56 : BitAssignment 56 → BitAssignment 56) (st stPost : BitAssignment n → BitAssignment n)
      (phPre phPost : BitAssignment n → ZMod 2) (mid : DynamicCircuit Var n)
    (hMid : SubspaceStep (mkKetOpW rWork (liftSt52 rM (fun x ↦ applyXorOps56 ops (f56 x)) st) phPre)
        (mkKetOpW rWork (liftSt52 rM (fun x ↦ applyXorOps56 ops (f56 x)) stPost) phPost) mid) :
        SubspaceStep
    (mkKetOpW rWork (liftSt52 rM f56 st) phPre) (mkKetOpW rWork (liftSt52 rM f56 stPost) phPost)
        (wrapXorOps52 rM ops mid) := by
  induction ops generalizing f56 with
  | nil => exact hMid
  | cons op rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hops
      dsimp only [wrapXorOps52, wrapXorOp52]
      refine (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _)
        (circXorOp52_mul_liftSt52 rWork rM op hops.1 f56 st phPre)).seq
        ((ih hops.2 (fun x ↦ applyXorOp56 op (f56 x)) hMid).seq
          (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ _) ?_))
      rw [circXorOp52_mul_liftSt52 rWork rM op hops.1 (fun x ↦
          applyXorOp56 op (f56 x)) stPost phPost]
      simp only [applyXorOp56_invol]

theorem wOptInj_of_rM52_car15 {n : ℕ} (rM : QRegister 52 n) (rCar15 : QRegister 15 n)
    (hKM : rCar15.DisjointWires rM) {uIdx l0 h0 l1 h1 : Fin 52}
    (hd : Distinct5_56 (fin52To56 uIdx) (fin52To56 l0) (fin52To56 h0) (fin52To56 l1)
        (fin52To56 h1)) :
    WOptInj 2 1 (fun _ : Fin 1 ↦ rM uIdx) (wPair2 (rM l0) (rM h0) (rM l1) (rM h1))
      (rCar15 ⟨2, by decide⟩) (rCar15 ⟨1, by decide⟩) (rCar15 ⟨0, by decide⟩) where
  w_inj :=
    have n56 {a b : Fin 52} (h : fin52To56 a ≠ fin52To56 b) (e : rM a = rM b) : False :=
      h (congrArg fin52To56 (rM.wires.injective e))
    wPair2_wInj (n56 hd.2.2.2.2.1) (n56 hd.2.2.2.2.2.1) (n56 hd.2.2.2.2.2.2.1)
      (n56 hd.2.2.2.2.2.2.2.1) (n56 hd.2.2.2.2.2.2.2.2.1) (n56 hd.2.2.2.2.2.2.2.2.2)
  uLo_ne_w _ b p := by
    dsimp only [wPair2]
    split_ifs <;> intro e <;> have h := congrArg fin52To56 (rM.wires.injective e) <;>
      first | exact hd.1 h | exact hd.2.1 h | exact hd.2.2.1 h | exact hd.2.2.2.1 h
  uLo_ne_rDum _ h := disj_ne hKM ⟨2, by decide⟩ uIdx h.symm
  uLo_ne_wDum _ h := disj_ne hKM ⟨1, by decide⟩ uIdx h.symm
  uLo_ne_qEnc _ h := disj_ne hKM ⟨0, by decide⟩ uIdx h.symm
  w_ne_rDum b p := by
    dsimp only [wPair2]
    split_ifs <;> exact fun h ↦ disj_ne hKM ⟨2, by decide⟩ _ h.symm
  w_ne_wDum b p := by
    dsimp only [wPair2]
    split_ifs <;> exact fun h ↦ disj_ne hKM ⟨1, by decide⟩ _ h.symm
  w_ne_qEnc b p := by
    dsimp only [wPair2]
    split_ifs <;> exact fun h ↦ disj_ne hKM ⟨0, by decide⟩ _ h.symm
  rDum_ne_wDum h := absurd (rCar15.wires.injective h) (by decide)
  rDum_ne_qEnc h := absurd (rCar15.wires.injective h) (by decide)
  wDum_ne_qEnc h := absurd (rCar15.wires.injective h) (by decide)

theorem stSplit2Fwd_liftSt52 {n : ℕ} (rM : QRegister 52 n) (uIdx l0 h0 l1 h1 : Fin 52)
    (f56 : BitAssignment 56 → BitAssignment 56) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : stSplit2Fwd (rM uIdx)
    (rM l0) (rM h0) (rM l1) (rM h1) (liftSt52 rM f56 st δ) = liftSt52 rM (fun x ↦
        stSplit2Fwd (fin52To56 uIdx) (fin52To56 l0) (fin52To56 h0) (fin52To56 l1) (fin52To56 h1)
        (f56 x)) st δ := by
  dsimp only [liftSt52, stSplit2Fwd]
  simp only [writeReg_apply_reg, writeReg_upd52, ← proj52_upd]
  dsimp only [proj52]

theorem emb52_upd (g : BitAssignment 52) (idx : Fin 52) (v : ZMod 2) :
    emb52 (Function.update g idx v) = Function.update (emb52 g) (fin52To56 idx) v := by
  funext w
  by_cases hw : w.val < 52
  · by_cases hi : (⟨w.val, hw⟩ : Fin 52) = idx
    · have hwi : w = fin52To56 idx := Fin.ext (by simpa [fin52To56] using congrArg Fin.val hi)
      subst hwi
      simp [emb52, fin52To56, idx.isLt]
    · have hwi : w ≠ fin52To56 idx := fun e ↦
        hi (Fin.ext (by simpa [fin52To56] using congrArg Fin.val e))
      simp [emb52, hw, hi, hwi]
  · have hwi : w ≠ fin52To56 idx := fun e ↦ hw (e ▸ idx.isLt)
    simp [emb52, hw, hwi]

theorem upd_rM_comp {n : ℕ} (rM : QRegister 52 n) (β : BitAssignment n)
    (idx : Fin 52) (v : ZMod 2) :
    (fun u ↦ Function.update β (rM idx) v (rM u)) =
      Function.update (fun u ↦ β (rM u)) idx v := by
  funext u
  by_cases h : u = idx
  · subst h
    simp
  · simp [h, show rM u ≠ rM idx from fun e ↦ h (rM.wires.injective e)]

theorem step_split2OnLift52 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n)
    (rM : QRegister 52 n) (rCar15 : QRegister 15 n) (hKM : rCar15.DisjointWires rM)
    (uIdx l0 h0 l1 h1 bIdx : Fin 52)
    (hd : Distinct5_56 (fin52To56 uIdx) (fin52To56 l0) (fin52To56 h0) (fin52To56 l1) (fin52To56 h1))
    (hb : bIdx ≠ l0 ∧ bIdx ≠ l1 ∧ bIdx ≠ h0 ∧ bIdx ≠ h1)
    (e56 : BitAssignment 56 → ZMod 2)
    (he56Proj : ∀ y : BitAssignment 56, e56 (emb52 (proj52 y)) = e56 y)
    (he56Indep : ∀ (y : BitAssignment 56) (v0 v1 v2 v3 : ZMod 2),
      e56 (Function.update (Function.update (Function.update (Function.update y
        (fin52To56 l0) v0) (fin52To56 h0) v1) (fin52To56 l1) v2) (fin52To56 h1) v3) = e56 y)
    (f56 : BitAssignment 56 → BitAssignment 56)
    (st stPost : BitAssignment n → BitAssignment n)
    (phPre phPost : BitAssignment n → ZMod 2) (mid : DynamicCircuit Var n)
    (hSameM : ∀ δ (u : Fin 52), (∀ q, δ (rWork q) = 0) → stPost δ (rM u) = st δ (rM u))
    (hClnCar : ∀ δ (u : Fin 15), (∀ q, δ (rWork q) = 0) →
      st δ (rCar15 u) = 0 ∧ stPost δ (rCar15 u) = 0)
    (hInv56 : ∀ δ, (∀ q, δ (rWork q) = 0) →
      let y := f56 (emb52 (fun u ↦ st δ (rM u)))
      y (fin52To56 l0) * y (fin52To56 l1) = 0 ∧
      y (fin52To56 h0) = 0 ∧ y (fin52To56 h1) = 0 ∧
      (y (fin52To56 l0) = 1 → y (fin52To56 bIdx) = 0) ∧
      (y (fin52To56 l1) = 1 → y (fin52To56 bIdx) = 1) ∧
      e56 y = y (fin52To56 l0) + y (fin52To56 l1))
    (hMid : SubspaceStep
      (mkKetOpW rWork (liftSt52 rM (fun x ↦ stSplit2Fwd (fin52To56 uIdx) (fin52To56 l0)
          (fin52To56 h0)
        (fin52To56 l1) (fin52To56 h1) (f56 x)) st) phPre)
      (mkKetOpW rWork (liftSt52 rM (fun x ↦ stSplit2Fwd (fin52To56 uIdx) (fin52To56 l0)
          (fin52To56 h0)
        (fin52To56 l1) (fin52To56 h1) (f56 x)) stPost) phPost) mid) :
    SubspaceStep
      (mkKetOpW rWork (liftSt52 rM f56 st) phPre)
      (mkKetOpW rWork (liftSt52 rM f56 stPost) phPost)
      (pSplit2Bracket v (rM uIdx) (rM l0) (rM h0) (rM l1) (rM h1)
        (rCar15 ⟨2, by decide⟩) (rCar15 ⟨1, by decide⟩) (rCar15 ⟨0, by decide⟩)
        (wOptInj_of_rM52_car15 rM rCar15 hKM hd) mid) := by
  let eAct : BitAssignment n → ZMod 2 := fun β ↦ e56 (emb52 (fun u ↦ β (rM u)))
  have hCarOut (stX : BitAssignment n → BitAssignment n) (δ) (k : Fin 15) :
      liftSt52 rM f56 stX δ (rCar15 k) = stX δ (rCar15 k) :=
    writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦ disj_ne hKM k u hu.symm)
  refine step_pSplit2Bracket v rWork (rM uIdx) (rM l0) (rM h0) (rM l1) (rM h1)
    (rCar15 ⟨2, by decide⟩) (rCar15 ⟨1, by decide⟩) (rCar15 ⟨0, by decide⟩) (rM bIdx)
    eAct (wOptInj_of_rM52_car15 rM rCar15 hKM hd)
    ⟨fun e ↦ hb.1 (rM.wires.injective e), fun e ↦ hb.2.1 (rM.wires.injective e),
     fun e ↦ hb.2.2.1 (rM.wires.injective e), fun e ↦ hb.2.2.2 (rM.wires.injective e),
     fun e ↦ disj_ne hKM ⟨2, by decide⟩ bIdx e.symm⟩
    (fun β v0 v1 v2 v3 ↦ by
      dsimp only [eAct]
      rw [upd_rM_comp, upd_rM_comp, upd_rM_comp, upd_rM_comp,
          emb52_upd, emb52_upd, emb52_upd, emb52_upd]
      exact he56Indep _ _ _ _ _)
    (liftSt52 rM f56 st) (liftSt52 rM f56 stPost) phPre phPost mid
    (fun δ hz ↦ by
      simp only [liftSt52, proj52, writeReg_apply_reg]
      exact (hInv56 δ hz).1)
    (fun δ hz ↦ by
      simp only [liftSt52, proj52, writeReg_apply_reg]
      exact ⟨(hInv56 δ hz).2.1, (hInv56 δ hz).2.2.1,
        (hCarOut st δ ⟨2, by decide⟩).trans (hClnCar δ ⟨2, by decide⟩ hz).1,
        (hCarOut st δ ⟨1, by decide⟩).trans (hClnCar δ ⟨1, by decide⟩ hz).1,
        (hCarOut st δ ⟨0, by decide⟩).trans (hClnCar δ ⟨0, by decide⟩ hz).1⟩)
    (fun δ hz ↦ by
      simp only [liftSt52, proj52, writeReg_apply_reg]
      exact ⟨(hInv56 δ hz).2.2.2.1, (hInv56 δ hz).2.2.2.2.1⟩)
    (fun δ hz ↦ by
      simp only [eAct, liftSt52, writeReg_apply_reg, he56Proj]
      exact (hInv56 δ hz).2.2.2.2.2)
    (fun δ hz ↦ by
      have hInEq : (fun u ↦ stPost δ (rM u)) = (fun u ↦ st δ (rM u)) := funext fun u ↦ hSameM δ u hz
      have hM (u : Fin 52) : liftSt52 rM f56 stPost δ (rM u) = liftSt52 rM f56 st δ (rM u) := by
        simp only [liftSt52, writeReg_apply_reg, hInEq]
      have hC (k : Fin 15) : liftSt52 rM f56 stPost δ (rCar15 k) = liftSt52 rM f56 st δ (rCar15 k)
          := by
        rw [hCarOut, hCarOut, (hClnCar δ k hz).2, (hClnCar δ k hz).1]
      exact ⟨hM uIdx, hM l0, hM h0, hM l1, hM h1, hC _, hC _, hC _, hM bIdx, by
        simp only [eAct, liftSt52, writeReg_apply_reg, hInEq]⟩)
    (subspaceStep_congr_in
      (mkKetOpW_congr rWork (fun δ _ ↦ stSplit2Fwd_liftSt52 rM uIdx l0 h0 l1 h1 f56 st δ)
          (fun _ _ ↦ rfl))
      (subspaceStep_congr_out hMid
        (mkKetOpW_congr rWork (fun δ _ ↦
            (stSplit2Fwd_liftSt52 rM uIdx l0 h0 l1 h1 f56 stPost δ).symm)
          (fun _ _ ↦ rfl))))

def opsScrub4 : List XorOp56 :=
  [.cnot ⟨0, by decide⟩ ⟨22, by decide⟩,
   .cnot ⟨1, by decide⟩ ⟨22, by decide⟩,
   .cnot ⟨21, by decide⟩ ⟨22, by decide⟩,
   .cnot ⟨24, by decide⟩ ⟨22, by decide⟩,
   .cnot ⟨25, by decide⟩ ⟨22, by decide⟩,
   .cnot ⟨21, by decide⟩ ⟨23, by decide⟩,
   .cnot ⟨25, by decide⟩ ⟨23, by decide⟩,
   .cnot ⟨1, by decide⟩ ⟨26, by decide⟩,
   .cnot ⟨2, by decide⟩ ⟨26, by decide⟩,
   .cnot ⟨28, by decide⟩ ⟨26, by decide⟩,
   .cnot ⟨29, by decide⟩ ⟨26, by decide⟩,
   .cnot ⟨2, by decide⟩ ⟨27, by decide⟩,
   .cnot ⟨29, by decide⟩ ⟨27, by decide⟩]

def f56Scrubbed (x : BitAssignment 56) : BitAssignment 56 := applyXorOps56 opsScrub4 (f56PreBack x)
theorem cnot56_same {f : BitAssignment 56} {c tg : Fin 56}
    (hCol : c ≠ tg) : applyXorOp56 (.cnot c tg) f tg = f tg + f c := applyXorOp56_cnot_same hCol
theorem cnot56_ne {f : BitAssignment 56} {c tg w : Fin 56} (hCol : w ≠ tg) : applyXorOp56
    (.cnot c tg) f w = f w := applyXorOp56_of_ne_tgt (.cnot c tg) f hCol
theorem x56_ne {f : BitAssignment 56} {q w : Fin 56} (hCol : w ≠ q) : applyXorOp56 (.x q) f w =
    f w := applyXorOp56_of_ne_tgt (.x q) f hCol
theorem zmod2_split_sum : ∀ a b : ZMod 2, a * (1 + b) + a * b = a := by decide

theorem stSplit2Fwd_sum {uIdx l0 h0 l1 h1 : Fin 56} (hd : Distinct5_56 uIdx l0 h0 l1 h1)
    (y : BitAssignment 56) : (stSplit2Fwd uIdx l0 h0 l1 h1 y l0 +
    stSplit2Fwd uIdx l0 h0 l1 h1 y h0 = y l0) ∧
    (stSplit2Fwd uIdx l0 h0 l1 h1 y l1 + stSplit2Fwd uIdx l0 h0 l1 h1 y h1 = y l1) := by
  obtain ⟨_, _, _, _, hl0h0, hl0l1, hl0h1, hh0l1, hh0h1, hl1h1⟩ := hd
  simp only [stSplit2Fwd, Function.update_self, Function.update_of_ne hl0h1,
    Function.update_of_ne hl0l1, Function.update_of_ne hl0h0, Function.update_of_ne hh0h1,
    Function.update_of_ne hh0l1, Function.update_of_ne hl1h1, zmod2_split_sum, and_self]

def permBack52 (v : Fin 52) : Fin 52 :=
  if h22 : v.val < 22 then ⟨v.val, by omega⟩
  else if h24 : v.val < 24 then ⟨v.val + 2, by omega⟩
  else if h48 : v.val < 48 then ⟨v.val + 4, by omega⟩
  else if v.val = 48 then ⟨22, by decide⟩
  else if v.val = 49 then ⟨23, by decide⟩
  else if v.val = 50 then ⟨26, by decide⟩
  else ⟨27, by decide⟩

theorem permBack52_inj : Function.Injective permBack52 := fun a b h ↦ by
  have hv := congrArg Fin.val h
  have := a.isLt
  have := b.isLt
  dsimp only [permBack52] at hv
  split_ifs at hv <;> dsimp only at hv <;> exact Fin.ext (by omega)

theorem f56Scrubbed_permBack52_eq (x : BitAssignment 56) (hx : ∀ u : Fin 56, 17 ≤ u.val → x u = 0)
    (v : Fin 52) : proj52 (f56Scrubbed x) (permBack52 v) = f56PreBack x (idx52To56 v) := by
  have hz4 : f56Scrubbed x ⟨22, by decide⟩ = 0 ∧ f56Scrubbed x ⟨23, by decide⟩ = 0 ∧
      f56Scrubbed x ⟨26, by decide⟩ = 0 ∧ f56Scrubbed x ⟨27, by decide⟩ = 0 := by
    let z0 := f56Front x
    let sNe (u : Fin 56) (a b c d : ℕ) (ha : a < 56 := by decide) (hb : b < 56 := by decide)
        (hc : c < 56 := by decide) (hd : d < 56 := by decide) : Bool :=
      u != ⟨a, ha⟩ && u != ⟨b, hb⟩ && u != ⟨c, hc⟩ && u != ⟨d, hd⟩
    have hz0 (u : Fin 56) (hu : 22 ≤ u.val := by decide) : z0 u = 0 := f56Front_zero_ge22 x hx hu
    have hPA_keep (u : Fin 56) (hu : decide (u.val < 3 ∨ u.val = 21) = true := by decide) :
        f56PostA x u = z0 u := by
      obtain ⟨h1, h2, h3⟩ := (by decide : ∀ u : Fin 56, decide (u.val < 3 ∨ u.val = 21) = true →
        (opsPostA.all fun op ↦ u != op.tgt) = true ∧ sNe u 22 24 23 25 = true ∧
        (opsInitA.all fun op ↦ u != op.tgt) = true) u hu
      exact (applyXorOps56_eq_of_nonTgt h1).trans
        ((stSplit2Fwd_eq_of_bne h2).trans (applyXorOps56_eq_of_nonTgt h3))
    have hSumA := stSplit2Fwd_sum (uIdx := ⟨4, by decide⟩) (l0 := ⟨22, by decide⟩)
      (h0 := ⟨24, by decide⟩) (l1 := ⟨23, by decide⟩) (h1 := ⟨25, by decide⟩) (by decide)
          (f56PreSplitA x)
    have hKeepPB (u : Fin 56) (hu : decide (u.val < 3 ∨ (21 ≤ u.val ∧ u.val ≤ 25)) =
        true := by decide) :
        f56PreBack x u = f56PostA x u := by
      obtain ⟨hP, h4, h3, h2, h1, h0, hI⟩ := (by decide : ∀ u : Fin 56,
        decide (u.val < 3 ∨ (21 ≤ u.val ∧ u.val ≤ 25)) = true →
        (opsPostSplits04.all fun op ↦ u != op.tgt) = true ∧ sNe u 34 36 35 37 = true ∧
        sNe u 32 34 33 35 = true ∧ sNe u 30 32 31 33 = true ∧ sNe u 28 30 29 31 = true ∧
        sNe u 26 28 27 29 = true ∧ (opsPreSplits04.all fun op ↦ u != op.tgt) = true) u hu
      unfold f56PreBack f56PostSplit4 f56PreSplit4 f56PreSplit3 f56PreSplit2 f56PreSplit1
          f56PreSplit0
      rw [applyXorOps56_eq_of_nonTgt hP, stSplit2Fwd_eq_of_bne h4, stSplit2Fwd_eq_of_bne h3,
          stSplit2Fwd_eq_of_bne h2, stSplit2Fwd_eq_of_bne h1, stSplit2Fwd_eq_of_bne h0,
          applyXorOps56_eq_of_nonTgt hI]
    have hPA_ge26 (u : Fin 56) (hu : 26 ≤ u.val := by decide) : f56PostA x u = 0 :=
      (applyXorOps56_of_lt opsPostA 26 _ hu).trans ((stSplit2Fwd_of_lt (B :=
          26) hu (by decide)).trans
        ((applyXorOps56_of_lt opsInitA 26 _ hu).trans (hz0 u (by omega))))
    have hS0_26 : f56PreSplit0 x ⟨26, by decide⟩ = (0 + z0 ⟨1, by decide⟩) + z0 ⟨2, by decide⟩ := by
      simp +decide only [f56PreSplit0, opsPreSplits04, applyXorOps56, cnot56_same, cnot56_ne,
          x56_ne]
      rw [hPA_ge26 _, hPA_keep ⟨1, by decide⟩, hPA_keep ⟨2, by decide⟩]
    have hS0_27 : f56PreSplit0 x ⟨27, by decide⟩ = 0 + z0 ⟨2, by decide⟩ := by
      simp +decide only [f56PreSplit0, opsPreSplits04, applyXorOps56, cnot56_same, cnot56_ne,
          x56_ne]
      rw [hPA_ge26 _, hPA_keep ⟨2, by decide⟩]
    have sum1 {u l0 h0 l1 h1 : Fin 56} (y) (hd : Distinct5_56 u l0 h0 l1 h1) :=
        (stSplit2Fwd_sum hd y).1
    have sum2 {u l0 h0 l1 h1 : Fin 56} (y) (hd : Distinct5_56 u l0 h0 l1 h1) :=
        (stSplit2Fwd_sum hd y).2
    let s5 := f56PostSplit4 x
    let E : ZMod 2 := s5 ⟨28, by decide⟩ + (s5 ⟨30, by decide⟩ +
      (s5 ⟨32, by decide⟩ + (s5 ⟨34, by decide⟩ + s5 ⟨36, by decide⟩)))
    let O : ZMod 2 := s5 ⟨29, by decide⟩ + (s5 ⟨31, by decide⟩ +
      (s5 ⟨33, by decide⟩ + (s5 ⟨35, by decide⟩ + s5 ⟨37, by decide⟩)))
    have hEqE : s5 ⟨26, by decide⟩ + E = (0 + z0 ⟨1, by decide⟩) + z0 ⟨2, by decide⟩ := by
      simp +decide only [s5, E, f56PostSplit4, f56PreSplit4, f56PreSplit3, f56PreSplit2,
        f56PreSplit1, stSplit2Fwd_eq_of_bne, sum1, hS0_26]
    have hEqO : s5 ⟨27, by decide⟩ + O = 0 + z0 ⟨2, by decide⟩ := by
      simp +decide only [s5, O, f56PostSplit4, f56PreSplit4, f56PreSplit3, f56PreSplit2,
        f56PreSplit1, stSplit2Fwd_eq_of_bne, sum2, hS0_27]
    have hPB29 : f56PreBack x ⟨29, by decide⟩ = O := by
      simp +decide only [f56PreBack, opsPostSplits04, applyXorOps56, cnot56_same, cnot56_ne, x56_ne]
      dsimp only [s5, O]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp +decide only [f56Scrubbed, opsScrub4, applyXorOps56, cnot56_same, cnot56_ne]
      rw [hKeepPB ⟨22, by decide⟩, hKeepPB ⟨0, by decide⟩, hKeepPB ⟨1, by decide⟩,
          hKeepPB ⟨21, by decide⟩, hKeepPB ⟨24, by decide⟩, hKeepPB ⟨25, by decide⟩,
          hPA_keep ⟨0, by decide⟩, hPA_keep ⟨1, by decide⟩, hPA_keep ⟨21, by decide⟩]
      simp +decide only [f56PostA, opsPostA, applyXorOps56, cnot56_same, cnot56_ne]
      refine (by decide : ∀ a b c c0 c1 d : ZMod 2, a + b = ((0 + c0) + c1) + d →
        ((((a + c0) + c1) + d) + (b + c)) + c = 0) _ _ _ _ _ _ (hSumA.1.trans ?_)
      simp +decide only [f56PreSplitA, opsInitA, applyXorOps56, cnot56_same, cnot56_ne]
      rw [show f56Front x ⟨22, by decide⟩ = 0 from hz0 _]
    · simp +decide only [f56Scrubbed, opsScrub4, applyXorOps56, cnot56_same, cnot56_ne]
      rw [hKeepPB ⟨23, by decide⟩, hKeepPB ⟨21, by decide⟩, hKeepPB ⟨25, by decide⟩,
          hPA_keep ⟨21, by decide⟩]
      simp +decide only [f56PostA, opsPostA, applyXorOps56, cnot56_ne]
      refine (by decide : ∀ a b d : ZMod 2, a + b = 0 + d → (a + d) + b = 0) _ _ _ (hSumA.2.trans
          ?_)
      simp +decide only [f56PreSplitA, opsInitA, applyXorOps56, cnot56_same, cnot56_ne]
      rw [show f56Front x ⟨23, by decide⟩ = 0 from hz0 _]
    · simp +decide only [f56Scrubbed, opsScrub4, applyXorOps56, cnot56_same, cnot56_ne]
      rw [hKeepPB ⟨1, by decide⟩, hKeepPB ⟨2, by decide⟩, hPA_keep ⟨1, by decide⟩,
          hPA_keep ⟨2, by decide⟩,
          show f56PreBack x ⟨26, by decide⟩ =
              s5 ⟨26, by decide⟩ from applyXorOps56_eq_of_nonTgt (by decide),
          show f56PreBack x ⟨28, by decide⟩ = E + O by
            simp +decide only [f56PreBack, opsPostSplits04, applyXorOps56, cnot56_same, cnot56_ne,
                x56_ne]
            dsimp only [s5, E, O],
          hPB29]
      exact (by decide : ∀ a e o c1 c2 : ZMod 2, a + e = (0 + c1) + c2 →
        (((a + c1) + c2) + (e + o)) + o = 0) _ _ _ _ _ hEqE
    · simp +decide only [f56Scrubbed, opsScrub4, applyXorOps56, cnot56_same, cnot56_ne]
      rw [hKeepPB ⟨2, by decide⟩, hPA_keep ⟨2, by decide⟩,
          show f56PreBack x ⟨27, by decide⟩ =
              s5 ⟨27, by decide⟩ from applyXorOps56_eq_of_nonTgt (by decide),
          hPB29]
      exact (by decide : ∀ a o c : ZMod 2, a + o = 0 + c → (a + c) + o = 0) _ _ _ hEqO
  dsimp only [proj52]
  by_cases hv48 : v.val < 48
  · rw [(by decide : ∀ u : Fin 52, u.val < 48 → fin52To56 (permBack52 u) = idx52To56 u) v hv48]
    by_cases hv24 : v.val < 24
    · exact applyXorOps56_eq_of_nonTgt ((by decide : ∀ u : Fin 52, u.val < 24 →
        (opsScrub4.all fun op ↦ idx52To56 u != op.tgt) = true) v hv24)
    · exact applyXorOps56_of_lt opsScrub4 28 (f56PreBack x)
        ((by decide : ∀ u : Fin 52, ¬u.val < 24 → u.val < 48 → 28 ≤ (idx52To56 u).val) v hv24 hv48)
  · rw [f56PreBack_zero_ge38 x hx ((by decide : ∀ u : Fin 52, ¬u.val < 48 → 38 ≤ (idx52To56 u).val)
        v hv48)]
    rcases (by decide : ∀ u : Fin 52, ¬u.val < 48 →
        fin52To56 (permBack52 u) = ⟨22, by decide⟩ ∨ fin52To56 (permBack52 u) = ⟨23, by decide⟩ ∨
        fin52To56 (permBack52 u) = ⟨26, by decide⟩ ∨ fin52To56 (permBack52 u) = ⟨27, by decide⟩)
      v hv48 with hp | hp | hp | hp <;> rw [hp]
    exacts [hz4.1, hz4.2.1, hz4.2.2.1, hz4.2.2.2]

def rBack52Of52 {n : ℕ} (rM : QRegister 52 n) : QRegister 52 n :=
    rM.compose ⟨⟨permBack52, permBack52_inj⟩⟩
def rFront22Of52 {n : ℕ} (rM : QRegister 52 n) : QRegister 22 n :=
  rM.compose (QRegister.block 0 22 (by decide))

theorem disj_rBack52 {m n : ℕ} (rA : QRegister m n) (rM : QRegister 52 n)
    (h : rA.DisjointWires rM) : rA.DisjointWires (rBack52Of52 rM) := disj_of_ne fun i v heq ↦
    disj_ne h i (permBack52 v) heq
theorem rBack52_ne {n : ℕ} (rB : QRegister 52 n) {a b : ℕ} (ha : a < 52) (hb : b < 52)
    (hne : a ≠ b) : rB ⟨a, ha⟩ ≠ rB ⟨b, hb⟩ := fun h ↦ hne (congrArg Fin.val (rB.wires.injective h))
def pCz4_52 {Var : Type} {n : ℕ} (rB : QRegister 52 n) : DynamicCircuit Var n :=
  (cz2 (rB ⟨0, by decide⟩) (rB ⟨17, by decide⟩) (rBack52_ne rB _ _ (by decide))).seq
  ((cz2 (rB ⟨1, by decide⟩) (rB ⟨18, by decide⟩) (rBack52_ne rB _ _ (by decide))).seq
  ((cz2 (rB ⟨2, by decide⟩) (rB ⟨19, by decide⟩) (rBack52_ne rB _ _ (by decide))).seq
   (cz2 (rB ⟨34, by decide⟩) (rB ⟨36, by decide⟩) (rBack52_ne rB _ _ (by decide)))))

theorem pCz4_52_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (rB : QRegister 52 n) (hS : ∀ u, S (rB u)) :
    (pCz4_52 (Var := Var) rB).count .T = 0 ∧
    (pCz4_52 (Var := Var) rB).count .TOFF = 0 ∧
    DynWires S (pCz4_52 (Var := Var) rB) := by
  dsimp only [pCz4_52, DynamicCircuit.count]
  obtain ⟨t1, f1⟩ :=
      cz2_counts (Var := Var) (rB ⟨0, by decide⟩) (rB ⟨17, by decide⟩)
      (rBack52_ne rB _ _ (by decide))
  obtain ⟨t2, f2⟩ :=
      cz2_counts (Var := Var) (rB ⟨1, by decide⟩) (rB ⟨18, by decide⟩)
      (rBack52_ne rB _ _ (by decide))
  obtain ⟨t3, f3⟩ :=
      cz2_counts (Var := Var) (rB ⟨2, by decide⟩) (rB ⟨19, by decide⟩)
      (rBack52_ne rB _ _ (by decide))
  obtain ⟨t4, f4⟩ :=
      cz2_counts (Var := Var) (rB ⟨34, by decide⟩) (rB ⟨36, by decide⟩)
      (rBack52_ne rB _ _ (by decide))
  refine ⟨by rw [t1, t2, t3, t4], by rw [f1, f2, f3, f4],
    ⟨cz2_dynWires S _ _ _ (hS _) (hS _), ⟨cz2_dynWires S _ _ _ (hS _) (hS _),
     ⟨cz2_dynWires S _ _ _ (hS _) (hS _), cz2_dynWires S _ _ _ (hS _) (hS _)⟩⟩⟩⟩

theorem pCz4_52_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister W n) (rB : QRegister 52 n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (mkKetOpW rWork st ph)
      (mkKetOpW rWork st (fun δ ↦ ph δ + cz4Val52 (fun v ↦ st δ (rB v))))
      (pCz4_52 (Var := Var) rB) := by
  unfold pCz4_52
  refine subspaceStep_of_eq_post
    (subspaceStep_seq_u (cz2_step (Var := Var) rWork _ _ _ st ph)
      (subspaceStep_seq_u (cz2_step (Var := Var) rWork _ _ _ st _)
        (subspaceStep_seq_u (cz2_step (Var := Var) rWork _ _ _ st _)
          (cz2_step (Var := Var) rWork _ _ _ st _))))
    (mkKetOpW_congr rWork (fun _ _ ↦ rfl) (fun δ _ ↦ ?_))
  dsimp only [cz4Val52]
  ring
def fOWAdd48Csa_dsc50 {n : ℕ} (rZ16 : QRegister 16 n) (rCar15 : QRegister 15 n)
    (rB : QRegister 52 n) (u : Fin 48) : Wire n :=
  if h0 : u.val = 0 then rB ⟨34, by decide⟩
  else if h1 : u.val < 17 then rZ16 ⟨u.val - 1, by omega⟩
  else if h2 : u.val < 33 then rB ⟨35 + (u.val - 17), by omega⟩
  else rCar15 ⟨u.val - 33, by
      have := u.isLt
      omega⟩

theorem fOWAdd48Csa_dsc50_inj {n : ℕ} (rZ16 : QRegister 16 n) (rCar15 : QRegister 15 n)
    (rB : QRegister 52 n) (hZB : rZ16.DisjointWires rB) (hZK : rZ16.DisjointWires rCar15)
    (hKB : rCar15.DisjointWires rB) :
    Function.Injective (fOWAdd48Csa_dsc50 rZ16 rCar15 rB) := by
  intro a b heq
  have ha := a.isLt
  have hb := b.isLt
  have finEq {m : ℕ} {x y : Fin m} {r : QRegister m n} (h : r x = r y)
      (ho : x.val = y.val → a.val = b.val) : a = b :=
    Fin.ext (ho (congrArg Fin.val (r.wires.injective h)))
  dsimp [fOWAdd48Csa_dsc50] at heq
  split_ifs at heq <;> first
    | exact Fin.ext (by omega)
    | exact finEq heq fun hv ↦ by
        dsimp at hv
        omega
    | exact absurd heq (disj_ne hZB _ _) | exact absurd heq.symm (disj_ne hZB _ _)
    | exact absurd heq (disj_ne hZK _ _) | exact absurd heq.symm (disj_ne hZK _ _)
    | exact absurd heq (disj_ne hKB _ _) | exact absurd heq.symm (disj_ne hKB _ _)

def rOWAdd48Csa_dsc50 {n : ℕ} (rZ16 : QRegister 16 n) (rCar15 : QRegister 15 n)
    (rB : QRegister 52 n) (hZB : rZ16.DisjointWires rB) (hZK : rZ16.DisjointWires rCar15)
    (hKB : rCar15.DisjointWires rB) : QRegister 48 n :=
    ⟨⟨fOWAdd48Csa_dsc50 rZ16 rCar15 rB, fOWAdd48Csa_dsc50_inj rZ16 rCar15 rB hZB hZK hKB⟩⟩
def pOWAdd17Kick16Csa_dsc50 {Var : Type} {n : ℕ} (v : Var) (rZ16 : QRegister 16 n)
    (rCar15 : QRegister 15 n) (rB : QRegister 52 n) (hZB : rZ16.DisjointWires rB)
    (hZK : rZ16.DisjointWires rCar15)
    (hKB : rCar15.DisjointWires rB) : DynamicCircuit Var n :=
  (pUngatedAddCarryKick 15 v (rOWAdd48Csa_dsc50 rZ16 rCar15 rB hZB hZK hKB)).seq
    (z1 (rB ⟨51, by decide⟩))

theorem pOWAdd17Kick16Csa_dsc50_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rZ16 : QRegister 16 n) (rCar15 : QRegister 15 n) (rB : QRegister 52 n)
    (hZB : rZ16.DisjointWires rB) (hZK : rZ16.DisjointWires rCar15) (hKB : rCar15.DisjointWires rB)
    (hSZ : ∀ i, S (rZ16 i)) (hSK : ∀ u, S (rCar15 u)) (hSB : ∀ u, S (rB u)) :
    let p := pOWAdd17Kick16Csa_dsc50 v rZ16 rCar15 rB hZB hZK hKB
    p.count .T = 60 ∧ p.count .TOFF = 0 ∧ DynWires S p := by
  let rA := rOWAdd48Csa_dsc50 rZ16 rCar15 rB hZB hZK hKB
  obtain ⟨cT1, cF1⟩ := pUngatedAddCarryKick_counts 15 v rA
  obtain ⟨cT2, cF2⟩ := z1_counts (Var := Var) (rB ⟨51, by decide⟩)
  have hSA : ∀ i : Fin 48, S (rA i) := fun i ↦ by
    change S (fOWAdd48Csa_dsc50 rZ16 rCar15 rB i)
    dsimp [fOWAdd48Csa_dsc50]
    split_ifs
    · exact hSB _
    · exact hSZ _
    · exact hSB _
    · exact hSK _
  dsimp only [pOWAdd17Kick16Csa_dsc50, DynamicCircuit.count]
  exact ⟨by rw [cT1, cT2], by rw [cF1, cF2],
    ⟨pUngatedAddCarryKick_dynWires 15 S v rA hSA, z1_dynWires S _ (hSB _)⟩⟩

def pWrcsaInnerAddCz_dsc50 {Var : Type} {n : ℕ} (v : Var) (rZ16 : QRegister 16 n)
    (rCar15 : QRegister 15 n) (rB : QRegister 52 n) (hZB : rZ16.DisjointWires rB)
    (hZK : rZ16.DisjointWires rCar15)
    (hKB : rCar15.DisjointWires rB) : DynamicCircuit Var n :=
        (pOWAdd17Kick16Csa_dsc50 v rZ16 rCar15 rB hZB hZK hKB).seq (pCz4_52 rB)
def pWrcsaBack52_dsc50 {Var : Type} {n : ℕ} (v : Var) (rZ16 : QRegister 16 n)
    (rCar15 : QRegister 15 n) (rM : QRegister 52 n) (hZM : rZ16.DisjointWires rM)
    (hZK : rZ16.DisjointWires rCar15)
    (hKM : rCar15.DisjointWires rM) : DynamicCircuit Var n := wrapXorOps52 rM opsPostSplits04
    (wrapXorOps52 rM opsScrub4 (wrapDynOnReg v (rBack52Of52 rM) cpBack16_52 (pWrcsaInnerAddCz_dsc50
        v rZ16 rCar15 (rBack52Of52 rM)
        (disj_rBack52 rZ16 rM hZM) hZK (disj_rBack52 rCar15 rM hKM))))
def pWrcsaSplits04_dsc50 {Var : Type} {n : ℕ} (v : Var) (rZ16 : QRegister 16 n)
    (rCar15 : QRegister 15 n) (rM : QRegister 52 n) (hZM : rZ16.DisjointWires rM)
    (hZK : rZ16.DisjointWires rCar15)
    (hKM : rCar15.DisjointWires rM) : DynamicCircuit Var n :=
  let cCar := fun k : Fin 15 ↦ rCar15 k
  pSplit2Bracket v (rM ⟨11, by decide⟩) (rM ⟨26, by decide⟩) (rM ⟨28, by decide⟩)
    (rM ⟨27, by decide⟩) (rM ⟨29, by decide⟩) (cCar ⟨2, by decide⟩) (cCar ⟨1, by decide⟩)
        (cCar ⟨0, by decide⟩)
    (wOptInj_of_rM52_car15 rM rCar15 hKM (by decide))
  (pSplit2Bracket v (rM ⟨15, by decide⟩) (rM ⟨28, by decide⟩) (rM ⟨30, by decide⟩)
    (rM ⟨29, by decide⟩) (rM ⟨31, by decide⟩) (cCar ⟨2, by decide⟩) (cCar ⟨1, by decide⟩)
        (cCar ⟨0, by decide⟩)
    (wOptInj_of_rM52_car15 rM rCar15 hKM (by decide))
  (pSplit2Bracket v (rM ⟨14, by decide⟩) (rM ⟨30, by decide⟩) (rM ⟨32, by decide⟩)
    (rM ⟨31, by decide⟩) (rM ⟨33, by decide⟩) (cCar ⟨2, by decide⟩) (cCar ⟨1, by decide⟩)
        (cCar ⟨0, by decide⟩)
    (wOptInj_of_rM52_car15 rM rCar15 hKM (by decide))
  (pSplit2Bracket v (rM ⟨13, by decide⟩) (rM ⟨32, by decide⟩) (rM ⟨34, by decide⟩)
    (rM ⟨33, by decide⟩) (rM ⟨35, by decide⟩) (cCar ⟨2, by decide⟩) (cCar ⟨1, by decide⟩)
        (cCar ⟨0, by decide⟩)
    (wOptInj_of_rM52_car15 rM rCar15 hKM (by decide))
  (pSplit2Bracket v (rM ⟨12, by decide⟩) (rM ⟨34, by decide⟩) (rM ⟨36, by decide⟩)
    (rM ⟨35, by decide⟩) (rM ⟨37, by decide⟩) (cCar ⟨2, by decide⟩) (cCar ⟨1, by decide⟩)
        (cCar ⟨0, by decide⟩)
    (wOptInj_of_rM52_car15 rM rCar15 hKM (by decide))
    (pWrcsaBack52_dsc50 v rZ16 rCar15 rM hZM hZK hKM)))))

def pWrcsaAfterFront_dsc50 {Var : Type} {n : ℕ} (v : Var) (rZ16 : QRegister 16 n)
    (rCar15 : QRegister 15 n) (rM : QRegister 52 n) (hZM : rZ16.DisjointWires rM)
    (hZK : rZ16.DisjointWires rCar15)
    (hKM : rCar15.DisjointWires rM) : DynamicCircuit Var n :=
  wrapXorOps52 rM opsInitA
    (pSplit2Bracket v (rM ⟨4, by decide⟩) (rM ⟨22, by decide⟩) (rM ⟨24, by decide⟩)
      (rM ⟨23, by decide⟩) (rM ⟨25, by decide⟩)
      (rCar15 ⟨2, by decide⟩) (rCar15 ⟨1, by decide⟩) (rCar15 ⟨0, by decide⟩)
      (wOptInj_of_rM52_car15 rM rCar15 hKM (by decide))
      (wrapXorOps52 rM opsPostA
        (wrapXorOps52 rM opsPreSplits04
          (pWrcsaSplits04_dsc50 v rZ16 rCar15 rM hZM hZK hKM))))

def pDualSumCore_dsc50 {Var : Type} {n : ℕ} (v : Var) (rZ16 : QRegister 16 n)
    (rCar15 : QRegister 15 n) (rM : QRegister 52 n) (hZM : rZ16.DisjointWires rM)
    (hZK : rZ16.DisjointWires rCar15)
    (hKM : rCar15.DisjointWires rM) : DynamicCircuit Var n :=
        wrapDynOnReg v (rFront22Of52 rM) cpFront5_22 (pWrcsaAfterFront_dsc50 v rZ16 rCar15 rM hZM
        hZK hKM)
theorem counts_pDualSumCore_dsc50 {Var : Type} {n : ℕ} (v : Var) (rZ16 : QRegister 16 n)
    (rCar15 : QRegister 15 n) (rM : QRegister 52 n) (hZM : rZ16.DisjointWires rM)
    (hZK : rZ16.DisjointWires rCar15)
    (hKM : rCar15.DisjointWires rM) : (pDualSumCore_dsc50 v rZ16 rCar15 rM hZM hZK hKM).count .T =
        180 ∧ (pDualSumCore_dsc50 v rZ16 rCar15 rM hZM hZK hKM).count .TOFF = 0 := by
  obtain ⟨tAdd, fAdd, _⟩ := pOWAdd17Kick16Csa_dsc50_counts_wires (S := fun _ ↦ True) v rZ16
    rCar15 (rBack52Of52 rM) (disj_rBack52 rZ16 rM hZM) hZK (disj_rBack52 rCar15 rM hKM)
    (fun _ ↦ trivial) (fun _ ↦ trivial) (fun _ ↦ trivial)
  obtain ⟨tCz, fCz, _⟩ :=
      pCz4_52_counts_wires (Var := Var) (S := fun _ ↦ True) (rBack52Of52 rM) (fun _ ↦ trivial)
  have tXor (ops) (mid : DynamicCircuit Var n) := (counts_wrapXorOps52 rM ops mid).1
  have fXor (ops) (mid : DynamicCircuit Var n) := (counts_wrapXorOps52 rM ops mid).2
  have tSp {u l0 h0 l1 h1 c2 c1 c0 hI} (mid : DynamicCircuit Var n) :=
    (counts_pSplit2Bracket v u l0 h0 l1 h1 c2 c1 c0 hI mid).1
  have fSp {u l0 h0 l1 h1 c2 c1 c0 hI} (mid : DynamicCircuit Var n) :=
    (counts_pSplit2Bracket v u l0 h0 l1 h1 c2 c1 c0 hI mid).2
  simp only [pDualSumCore_dsc50, pWrcsaAfterFront_dsc50, pWrcsaSplits04_dsc50, pWrcsaBack52_dsc50,
    pWrcsaInnerAddCz_dsc50, DynamicCircuit.count, counts_wrapDynOnReg, tXor, fXor, tSp, fSp,
    cpFront5_22_and, cpBack16_52_and, tAdd, fAdd, tCz, fCz]
  simp
theorem ctrlSafe_pDualSumCore_dsc50 {Var : Type} {n : ℕ} {S_ctrl S_tgt : Wire n → Prop} (v : Var)
    (rZ16 : QRegister 16 n) (rCar15 : QRegister 15 n) (rM : QRegister 52 n)
    (hZM : rZ16.DisjointWires rM)
    (hZK : rZ16.DisjointWires rCar15) (hKM : rCar15.DisjointWires rM)
        (hSZ : ∀ i, S_ctrl (rZ16 i) ∧ S_tgt (rZ16 i))
        (hSK : ∀ u, S_ctrl (rCar15 u) ∧ S_tgt (rCar15 u))
        (hSM : ∀ u, S_ctrl (rM u) ∧ S_tgt (rM u)) :
    DynCtrlSafe S_ctrl S_tgt (pDualSumCore_dsc50 v rZ16 rCar15 rM hZM hZK hKM) := by
  have hSBack (u : Fin 52) : S_ctrl (rBack52Of52 rM u) ∧ S_tgt (rBack52Of52 rM u) :=
      hSM (permBack52 u)
  obtain ⟨_, fA, wA⟩ := pOWAdd17Kick16Csa_dsc50_counts_wires (S := fun w ↦ S_ctrl w ∧ S_tgt w)
    v rZ16 rCar15 (rBack52Of52 rM)
        (disj_rBack52 rZ16 rM hZM) hZK (disj_rBack52 rCar15 rM hKM) hSZ hSK hSBack
  obtain ⟨_, fC, wC⟩ :=
      pCz4_52_counts_wires (Var := Var) (S := fun w ↦ S_ctrl w ∧ S_tgt w) (rBack52Of52 rM) hSBack
  have csSplit {u l0 h0 l1 h1 hI mid} (hm : DynCtrlSafe S_ctrl S_tgt mid) :
      DynCtrlSafe S_ctrl S_tgt (pSplit2Bracket v (rM u) (rM l0) (rM h0) (rM l1) (rM h1)
        (rCar15 ⟨2, by decide⟩) (rCar15 ⟨1, by decide⟩) (rCar15 ⟨0, by decide⟩) hI mid) :=
    ctrlSafe_pSplit2Bracket v _ _ _ _ _ _ _ _ _ _ (hSM _) (hSM _) (hSM _) (hSM _) (hSM _) (hSK _)
        (hSK _) (hSK _) hm
  have hSFront (u : Fin 22) : S_ctrl (rFront22Of52 rM u) ∧ S_tgt (rFront22Of52 rM u) := hSM _
  exact .wrapOnReg v (rFront22Of52 rM) cpFront5_22 (fun u ↦ (hSFront u).1)
    (ComputeProgCtrlSafe.of_all hSFront cpFront5_22)
    (ctrlSafe_wrapXorOps52 rM hSM opsInitA (csSplit (ctrlSafe_wrapXorOps52 rM hSM opsPostA
      (ctrlSafe_wrapXorOps52 rM hSM opsPreSplits04 (csSplit (csSplit (csSplit (csSplit (csSplit
        (ctrlSafe_wrapXorOps52 rM hSM opsPostSplits04 (ctrlSafe_wrapXorOps52 rM hSM opsScrub4
          (.wrapOnReg v (rBack52Of52 rM) cpBack16_52 (fun u ↦ (hSBack u).1)
            (ComputeProgCtrlSafe.of_all hSBack cpBack16_52) (.seq (.of_dynWires wA fA)
                (.of_dynWires wC fC))))))))))))))

theorem step_and_counts_pDualSumCore_dsc50 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n)
    (rZ16 : QRegister 16 n) (rCar15 : QRegister 15 n) (rM : QRegister 52 n)
    (hZM : rZ16.DisjointWires rM) (hZK : rZ16.DisjointWires rCar15) (hKM : rCar15.DisjointWires rM)
    (st stPost : BitAssignment n → BitAssignment n) (phPost : BitAssignment n → ZMod 2)
    (p1Fn p2Fn : BitAssignment n → Fin 64)
    (hp1V : ∀ δ, (∀ q, δ (rWork q) = 0) → validPre6Mask64.testBit (p1Fn δ).val = true)
    (hp2V : ∀ δ, (∀ q, δ (rWork q) = 0) → validPre6Mask64.testBit (p2Fn δ).val = true)
    (hP1B : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ j : Fin 6,
      (st δ (rM ⟨5 + j.val, by omega⟩) == 1) = (p1Fn δ).val.testBit j.val)
    (hP2B : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ j : Fin 6,
      (st δ (rM ⟨11 + j.val, by omega⟩) == 1) = (p2Fn δ).val.testBit j.val)
    (hRouted : ∀ δ, (∀ q, δ (rWork q) = 0) →
      ((st δ (rM ⟨0, by decide⟩) == 1) = false ∧ (st δ (rM ⟨1, by decide⟩) == 1) = false ∧
       (st δ (rM ⟨2, by decide⟩) == 1) = false) ∨
      ((st δ (rM ⟨0, by decide⟩) == 1) = true ∧
       ((st δ (rM ⟨1, by decide⟩) == 1) = false → (st δ (rM ⟨2, by decide⟩) == 1) = false)))
    (hClnM : ∀ δ (u : Fin 52), 17 ≤ u.val → (∀ q, δ (rWork q) = 0) → st δ (rM u) = 0)
    (hClnCar : ∀ δ (u : Fin 15), (∀ q, δ (rWork q) = 0) → st δ (rCar15 u) = 0)
    (hPostEq : ∀ δ, (∀ q, δ (rWork q) = 0) →
      let sp1 := speciesOfBits2 (st δ (rM ⟨3, by decide⟩)) (st δ (rM ⟨4, by decide⟩))
      let tgt := if st δ (rM ⟨0, by decide⟩) == 1 then
        (v1U10Pre5 (st δ (rM ⟨1, by decide⟩) == 1) (st δ (rM ⟨2, by decide⟩) == 1)
          sp1 (pre5OfPre6 (p1Fn δ)) +
         v2U10Pre5 (st δ (rM ⟨1, by decide⟩) == 1) (st δ (rM ⟨2, by decide⟩) == 1)
          0 (pre5OfPre6 (p2Fn δ))) % 2 ^ 17
      else 0
      stPost δ = stOWZ16 rZ16 (fun _ ↦ tgt) st δ ∧
      phPost δ = phOWZ16 rZ16 (fun _ ↦ tgt) st (fun _ ↦ 0) δ) :
    let p := pDualSumCore_dsc50 v rZ16 rCar15 rM hZM hZK hKM
    SubspaceStep (mkKetOpW rWork st (fun _ ↦ 0)) (mkKetOpW rWork stPost phPost) p ∧
    p.count .T = 180 ∧
    p.count .TOFF = 0 := by
  have hSameM (δ) (u : Fin 52) (hz : ∀ q, δ (rWork q) = 0) : stPost δ (rM u) = st δ (rM u) := by
    rw [(hPostEq δ hz).1]
    exact stOWZ16_outside rZ16 _ st δ (fun i h ↦ disj_ne hZM i u h.symm)
  have hEmbCln (δ) (hz : ∀ q, δ (rWork q) = 0) (u : Fin 56) (hu : 17 ≤ u.val) :
      emb52 (fun v ↦ st δ (rM v)) u = 0 := by
    dsimp only [emb52]
    split_ifs with h52
    · exact hClnM δ ⟨u.val, h52⟩ hu hz
    · rfl
  have step_pWrcsaBack52_dsc50 : SubspaceStep (mkKetOpW rWork (liftSt52 rM f56PostSplit4 st)
      (fun _ ↦ 0))
      (mkKetOpW rWork (liftSt52 rM f56PostSplit4 stPost) phPost)
      (pWrcsaBack52_dsc50 v rZ16 rCar15 rM hZM hZK hKM) := by
    have hSameOutM (δ) {w : Wire n} (hz : ∀ q, δ (rWork q) = 0) (hwZ : ∀ i : Fin 16, w ≠ rZ16 i) :
        liftSt52 rM f56Scrubbed stPost δ w = liftSt52 rM f56Scrubbed st δ w := by
      dsimp [liftSt52]
      rw [show (fun u ↦ stPost δ (rM u)) = (fun u ↦ st δ (rM u)) from funext fun u ↦ hSameM δ u hz]
      by_cases hm : ∃ u : Fin 52, rM u = w
      · obtain ⟨u, rfl⟩ := hm
        rw [writeReg_apply_reg, writeReg_apply_reg]
      · rw [writeReg_apply_of_not_mem _ _ _ w hm, writeReg_apply_of_not_mem _ _ _ w hm,
            (hPostEq δ hz).1, stOWZ16_outside rZ16 _ st δ hwZ]
    refine step_wrapXorOps52 rWork rM opsPostSplits04 (by decide) f56PostSplit4 st stPost (fun _ ↦
        0) phPost _ ?_
    change SubspaceStep (mkKetOpW rWork (liftSt52 rM f56PreBack st) (fun _ ↦ 0))
      (mkKetOpW rWork (liftSt52 rM f56PreBack stPost) phPost) _
    refine step_wrapXorOps52 rWork rM opsScrub4 (by decide) f56PreBack st stPost (fun _ ↦
        0) phPost _ ?_
    change SubspaceStep (mkKetOpW rWork (liftSt52 rM f56Scrubbed st) (fun _ ↦ 0))
      (mkKetOpW rWork (liftSt52 rM f56Scrubbed stPost) phPost) _
    let rBack := rBack52Of52 rM
    have hZB := disj_rBack52 rZ16 rM hZM
    have hKB := disj_rBack52 rCar15 rM hKM
    exact (subspaceStep_wrapOnReg_block2 (B := 0) (L := 52) (K := 52)
        (by decide) rfl (fun j ↦ by omega)
      v rWork rBack sMaskBack16_52 cpBack16_52 16 64 cpBack16_52_vp cpBack16_52_and rfl
      (liftSt52 rM f56Scrubbed st) (liftSt52 rM f56Scrubbed stPost) (fun _ ↦ 0) phPost
      (pWrcsaInnerAddCz_dsc50 v rZ16 rCar15 rBack hZB hZK hKB)
      (fun u hu δ hz ↦ by
        change liftSt52 rM f56Scrubbed st δ (rM (permBack52 u)) = 0
        dsimp [liftSt52]
        rw [writeReg_apply_reg, f56Scrubbed_permBack52_eq _ (hEmbCln δ hz) u]
        exact f56PreBack_zero_ge38 _ (hEmbCln δ hz)
          ((by decide : ∀ v : Fin 52, 34 ≤ v.val → 38 ≤ (idx52To56 v).val) u (sMaskBack16_52_ge34 u
              hu)))
      (fun δ u hz ↦ hSameOutM δ hz (fun i h ↦ disj_ne hZB i u h.symm))
      (fun _ _ _ hu ↦ absurd hu (Nat.not_lt_zero _))
      (fun stMid hKeep hVal ↦ by
        let rA := rOWAdd48Csa_dsc50 rZ16 rCar15 rBack hZB hZK hKB
        have hCln33 (u : Fin 48) (δ : BitAssignment n) (hu33 : 33 ≤ u.val)
            (hz : ∀ m : Fin W, δ (rWork m) = 0) : stMid δ (rA u) = 0 := by
          have := u.isLt
          rw [show rA u = rCar15 ⟨u.val - 33, Nat.sub_lt_left_of_lt_add hu33 u.isLt⟩ by
                change fOWAdd48Csa_dsc50 rZ16 rCar15 rBack u = _
                dsimp only [fOWAdd48Csa_dsc50]
                rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega),
                    _root_.dite_eq_right (by omega)],
              hKeep δ _ (fun j h ↦ disj_ne hKB _ ⟨0 + j.val, by omega⟩ h)]
          dsimp [liftSt52]
          rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨q, hq⟩ ↦ disj_ne hKM _ q hq.symm)]
          exact hClnCar δ _ hz
        obtain ⟨stAdd, sAdd, hAddKeep, hAddSum⟩ :=
            pUngatedAddCarryKick_step 15 v rWork rA stMid (fun _ ↦ 0) hCln33
        have hrA_Z (i : Fin 16) : rA ⟨1 + i.val, ungAdd_ltZ 15 i⟩ = rZ16 i := by
          have := i.isLt
          change fOWAdd48Csa_dsc50 rZ16 rCar15 rBack ⟨1 + i.val, _⟩ = _
          dsimp only [fOWAdd48Csa_dsc50]
          rw [_root_.dite_eq_right (by omega), _root_.dite_eq_left (by omega)]
          exact congrArg rZ16.wires (Fin.ext (Nat.add_sub_cancel_left 1 i.val))
        have hrA_B (i : Fin 16) : rA ⟨15 + 2 + i.val, ungAdd_ltB 15 i⟩ = rBack ⟨35 + i.val,
            by omega⟩ := by
          have := i.isLt
          change fOWAdd48Csa_dsc50 rZ16 rCar15 rBack ⟨15 + 2 + i.val, _⟩ = _
          dsimp only [fOWAdd48Csa_dsc50]
          rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega),
              _root_.dite_eq_left (by omega)]
          exact congrArg rBack.wires (Fin.ext (by
            dsimp only
            omega))
        have hrA_0 : rA ⟨0, ungAdd_lt0 15⟩ = rBack ⟨34, by decide⟩ := rfl
        let phCarry : BitAssignment n → ZMod 2 := fun δ ↦ (0 : ZMod 2) +
          (((finBitsVal (fun i : Fin 16 ↦ stMid δ (rA ⟨1 + i.val, ungAdd_ltZ 15 i⟩)) +
             finBitsVal (fun i : Fin 16 ↦ stMid δ (rA ⟨15 + 2 + i.val, ungAdd_ltB 15 i⟩)) +
             (stMid δ (rA ⟨0, ungAdd_lt0 15⟩)).val) / 2 ^ 16 : ℕ) : ZMod 2)
        have hMidZ (δ : BitAssignment n) (j : Fin 16) : stMid δ (rZ16 j) = st δ (rZ16 j) := by
          rw [hKeep δ (rZ16 j) (fun k h ↦ disj_ne hZB j ⟨0 + k.val, by omega⟩ h)]
          exact writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦ disj_ne hZM j u hu.symm)
        have hMidBack (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) (u : Wire 52) :
            stMid δ (rBack u) =
              cpBack16_52.fwdBits (fun v ↦ f56PreBack (emb52 (fun q ↦ st δ (rM q)))
                  (idx52To56 v)) u :=
          (hVal δ u hz).trans (congrFun (congrArg cpBack16_52.fwdBits (funext fun v ↦ by
            change liftSt52 rM f56Scrubbed st δ (rM (permBack52 v)) = _
            dsimp [liftSt52]
            rw [writeReg_apply_reg]
            exact f56Scrubbed_permBack52_eq _ (hEmbCln δ hz) v)) u)
        have hEmbLt (δ : BitAssignment n) (k : ℕ) (hk56 : k < 56 := by omega)
            (hk52 : k < 52 := by omega) :
            emb52 (fun v ↦ st δ (rM v)) ⟨k, hk56⟩ = st δ (rM ⟨k, hk52⟩) := _root_.dite_eq_left hk52
        have hSpec (δ : BitAssignment n) (hz : ∀ q, δ (rWork q) = 0) :=
          cpBack16_52_wrcsa_spec (emb52 (fun v ↦ st δ (rM v))) (hEmbCln δ hz)
            (p1Fn δ) (p2Fn δ) (hp1V δ hz) (hp2V δ hz)
            (fun j ↦ (congrArg (fun x : ZMod 2 ↦ x == 1)
                (hEmbLt δ (5 + j.val))).trans (hP1B δ hz j))
            (fun j ↦ (congrArg (fun x : ZMod 2 ↦ x == 1)
                (hEmbLt δ (11 + j.val))).trans (hP2B δ hz j))
            (hRouted δ hz)
        have hjBack (j : Fin 52) : rBack.compose (QRegister.block 0 52 (by decide)) j =
            rBack ⟨0 + j.val, by omega⟩ :=
          congrArg rBack.wires (Fin.ext (by simp only [QRegister.block_apply_val]))
        refine subspaceStep_of_eq_post
          (subspaceStep_seq_u (subspaceStep_seq_u sAdd (z1_step (Var := Var) rWork (rBack ⟨51,
              by decide⟩) stAdd phCarry))
            (pCz4_52_step (Var := Var) rWork rBack stAdd (fun δ ↦ phCarry δ +
                stAdd δ (rBack ⟨51, by decide⟩))))
          (mkKetOpW_congr rWork (fun δ hz ↦ ?_) (fun δ hz ↦ ?_))
        · obtain ⟨c16, _, hSum16, _⟩ := hSpec δ hz
          rw [hEmbLt δ 0, hEmbLt δ 1, hEmbLt δ 2, hEmbLt δ 3, hEmbLt δ 4] at hSum16
          funext w
          by_cases hwB : ∃ j : Fin 52, rBack.compose (QRegister.block 0 52 (by decide)) j = w
          · obtain ⟨j, rfl⟩ := hwB
            rw [writeReg_apply_reg, hjBack j]
            exact hAddKeep δ _ (fun i h ↦ disj_ne hZB i ⟨0 + j.val, by omega⟩ ((hrA_Z i) ▸ h).symm)
          · rw [writeReg_apply_of_not_mem _ _ _ w hwB]
            by_cases hwZ : ∃ i : Fin 16, rZ16 i = w
            · obtain ⟨i, rfl⟩ := hwZ
              dsimp [liftSt52]
              rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦ disj_ne hZM i u hu.symm)]
              exact congrFun (show (fun j : Fin 16 ↦ stAdd δ (rZ16 j)) =
                  (fun j : Fin 16 ↦ stPost δ (rZ16 j)) by
                rw [(hPostEq δ hz).1]
                apply finBitsVal_inj
                have hs := hAddSum δ hz
                simp only [hrA_Z, hrA_B, hrA_0, hMidZ δ, hMidBack δ hz] at hs
                rw [hs, stOWZ16_val]
                rw [Nat.add_assoc, hSum16, ← Nat.add_assoc, Nat.add_mul_mod_self_right]) i
            · have hwZ' : ∀ i : Fin 16, w ≠ rZ16 i := fun i e ↦ hwZ ⟨i, e.symm⟩
              rw [hAddKeep δ w (fun i e ↦ hwZ' i (e.trans (hrA_Z i))),
                  hKeep δ w (fun j e ↦ hwB ⟨j, (hjBack j).trans e.symm⟩), hSameOutM δ hz hwZ']
        · obtain ⟨c16, _, hSum16, hPh16⟩ := hSpec δ hz
          rw [hEmbLt δ 0, hEmbLt δ 1, hEmbLt δ 2, hEmbLt δ 3, hEmbLt δ 4] at hSum16 hPh16
          have hAddB (v : Fin 52) : stAdd δ (rBack v) = stMid δ (rBack v) :=
            hAddKeep δ (rBack v) (fun i e ↦ disj_ne hZB i v (e.trans (hrA_Z i)).symm)
          dsimp only [phCarry]
          simp only [hrA_Z, hrA_B, hrA_0, hMidZ δ, hMidBack δ hz,
            (hAddB ⟨51, by decide⟩).trans (hMidBack δ hz ⟨51, by decide⟩),
            congrArg cz4Val52 (funext fun v ↦ (hAddB v).trans (hMidBack δ hz v)), zero_add]
          change _ = _
          rw [Nat.add_assoc (finBitsVal _), hSum16, ← Nat.add_assoc,
              Nat.add_mul_div_right _ _ (by norm_num : 0 < 2 ^ 16),
              Nat.cast_add, add_assoc, add_assoc, ← add_assoc (c16 : ZMod 2), hPh16,
                  (hPostEq δ hz).2]
          dsimp only [phOWZ16]
          rw [zero_add, Nat.cast_add])).1
  have hCarBoth (δ) (u : Fin 15) (hz : ∀ q, δ (rWork q) = 0) : st δ (rCar15 u) = 0 ∧
      stPost δ (rCar15 u) = 0 :=
    ⟨hClnCar δ u hz, by
      rw [(hPostEq δ hz).1, stOWZ16_outside rZ16 _ st δ (fun i h ↦ disj_ne hZK i u h.symm)]
      exact hClnCar δ u hz⟩
  have sSp (u l0 h0 l1 h1 b : Fin 52) (e56 : _ → ZMod 2) (f56) {mid} (hInv)
      (hMid : SubspaceStep _ _ mid)
      (hd : Distinct5_56 (fin52To56 u) (fin52To56 l0) (fin52To56 h0) (fin52To56 l1) (fin52To56 h1)
          := by decide)
      (hb : b ≠ l0 ∧ b ≠ l1 ∧ b ≠ h0 ∧ b ≠ h1 := by decide)
      (heP : ∀ x, e56 (emb52 (proj52 x)) = e56 x := by
        intro _
        rfl)
      (heI : ∀ y v0 v1 v2 v3, e56 (Function.update (Function.update (Function.update
        (Function.update y (fin52To56 l0) v0) (fin52To56 h0) v1) (fin52To56 l1) v2)
            (fin52To56 h1) v3) = e56 y := by
          intro _ _ _ _ _
          simp +decide only [eActSplit0, eActSplit1, eActSplit2, eActSplit3, eActSplit4,
            eActSplitA, fin52To56, upd4_eq_of_bne]) :=
    step_split2OnLift52 v rWork rM rCar15 hKM u l0 h0 l1 h1 b hd hb e56 heP heI
      f56 st stPost (fun _ ↦ 0) phPost mid hSameM hCarBoth hInv hMid
  have sAF : SubspaceStep (mkKetOpW rWork (liftSt52 rM f56Front st) (fun _ ↦ 0))
      (mkKetOpW rWork (liftSt52 rM f56Front stPost) phPost)
      (pWrcsaAfterFront_dsc50 v rZ16 rCar15 rM hZM hZK hKM) :=
    step_wrapXorOps52 rWork rM opsInitA (by decide) f56Front st stPost (fun _ ↦ 0) phPost _
      (sSp ⟨4, by decide⟩ ⟨22, by decide⟩ ⟨24, by decide⟩ ⟨23, by decide⟩ ⟨25, by decide⟩
        ⟨3, by decide⟩ eActSplitA f56PreSplitA (fun δ hz ↦ inv_f56PreSplitA _ (hEmbCln δ hz))
        (step_wrapXorOps52 rWork rM opsPostA (by decide) f56PostSplitA st stPost (fun _ ↦
            0) phPost _
          (step_wrapXorOps52 rWork rM opsPreSplits04 (by decide) f56PostA st stPost (fun _ ↦
              0) phPost _
            (sSp ⟨11, by decide⟩ ⟨26, by decide⟩ ⟨28, by decide⟩ ⟨27, by decide⟩ ⟨29, by decide⟩
              ⟨2, by decide⟩ eActSplit0 f56PreSplit0 (fun δ hz ↦ inv_f56PreSplit0 _ (hEmbCln δ hz)
                  (hRouted δ hz))
            (sSp ⟨15, by decide⟩ ⟨28, by decide⟩ ⟨30, by decide⟩ ⟨29, by decide⟩ ⟨31, by decide⟩
              ⟨2, by decide⟩ eActSplit1 f56PreSplit1 (fun δ hz ↦ inv_f56PreSplit1 _ (hEmbCln δ hz)
                  (hRouted δ hz))
            (sSp ⟨14, by decide⟩ ⟨30, by decide⟩ ⟨32, by decide⟩ ⟨31, by decide⟩ ⟨33, by decide⟩
              ⟨2, by decide⟩ eActSplit2 f56PreSplit2 (fun δ hz ↦ inv_f56PreSplit2 _ (hEmbCln δ hz)
                  (hRouted δ hz))
            (sSp ⟨13, by decide⟩ ⟨32, by decide⟩ ⟨34, by decide⟩ ⟨33, by decide⟩ ⟨35, by decide⟩
              ⟨2, by decide⟩ eActSplit3 f56PreSplit3 (fun δ hz ↦ inv_f56PreSplit3 _ (hEmbCln δ hz)
                  (hRouted δ hz))
            (sSp ⟨12, by decide⟩ ⟨34, by decide⟩ ⟨36, by decide⟩ ⟨35, by decide⟩ ⟨37, by decide⟩
              ⟨2, by decide⟩ eActSplit4 f56PreSplit4 (fun δ hz ↦ inv_f56PreSplit4 _ (hEmbCln δ hz)
                  (hRouted δ hz))
              step_pWrcsaBack52_dsc50))))))))
  let rFront := rFront22Of52 rM
  have hrF (j : Fin 22) : rFront j = rM ⟨j.val, by omega⟩ :=
    congrArg rM.wires
        (Fin.ext (by simp only [QRegister.block_apply_val, zero_add]))
  have hrFC (j : Fin 22) : rFront.compose (QRegister.block 0 22 (by decide)) j = rFront j :=
    congrArg rFront.wires (Fin.ext (by simp only [QRegister.block_apply_val, zero_add]))
  obtain ⟨tAll, fAll⟩ := counts_pDualSumCore_dsc50 v rZ16 rCar15 rM hZM hZK hKM
  refine ⟨(subspaceStep_wrapOnReg_block2 (B := 0) (L := 22) (K := 22)
      (by decide) rfl (fun j ↦ by omega)
    v rWork rFront sMaskFront5_22 cpFront5_22 5 20 cpFront5_22_vp cpFront5_22_and rfl
    st stPost (fun _ ↦ 0) phPost (pWrcsaAfterFront_dsc50 v rZ16 rCar15 rM hZM hZK hKM)
    (fun u hu δ hz ↦ (congrArg (st δ) (hrF u)).trans (hClnM δ ⟨u.val, by omega⟩
        (sMaskFront5_22_ge17 u hu) hz))
    (fun δ u hz ↦ by rw [hrF u, hSameM δ _ hz])
    (fun _ _ _ hu ↦ absurd hu (Nat.not_lt_zero _))
    (fun stMid hKeep hVal ↦ subspaceStep_congr_in
      (mkKetOpW_congr rWork (fun δ hz ↦ funext fun w ↦ by
        by_cases hm : ∃ u : Fin 52, rM u = w
        · obtain ⟨u, rfl⟩ := hm
          by_cases hu22 : u.val < 22
          · rw [liftSt52_f56Front_lt rM st δ hu22, ← hrF ⟨u.val, hu22⟩, hVal δ ⟨u.val, hu22⟩ hz]
            exact congrFun (congrArg cpFront5_22.fwdBits (funext fun j ↦ congrArg (st δ) (hrF j))) _
          · rw [liftSt52_f56Front_ge rM st δ hu22]
            exact hKeep δ (rM u) (fun j e ↦ by
              have hv := congrArg Fin.val (rM.wires.injective (e.trans (hrF ⟨0 + j.val, by omega⟩)))
              dsimp only at hv
              omega)
        · rw [hKeep δ w (fun j e ↦ hm ⟨⟨0 + j.val, by omega⟩,
              (hrF ⟨0 + j.val, by omega⟩).symm.trans e.symm⟩)]
          exact (writeReg_apply_of_not_mem _ _ _ w hm).symm) (fun _ _ ↦ rfl))
      (subspaceStep_congr_out sAF
        (mkKetOpW_congr rWork (fun δ hz ↦ funext fun w ↦ by
          by_cases hmF : ∃ j : Fin 22, rFront.compose (QRegister.block 0 22 (by decide)) j = w
          · obtain ⟨j, rfl⟩ := hmF
            rw [writeReg_apply_reg, hrFC j, hrF j,
                show rFront ⟨0 + j.val, by omega⟩ =
                    rFront j from congrArg rFront.wires (Fin.ext (zero_add j.val)),
                hVal δ j hz, liftSt52_f56Front_lt rM stPost δ j.isLt]
            exact congrFun (congrArg cpFront5_22.fwdBits
              (funext fun k ↦ (hSameM δ _ hz).trans (congrArg (st δ) (hrF k).symm))) j
          · rw [writeReg_apply_of_not_mem _ _ _ w hmF]
            by_cases hm : ∃ u : Fin 52, rM u = w
            · obtain ⟨u, rfl⟩ := hm
              exact liftSt52_f56Front_ge rM stPost δ
                (fun hu22 ↦ hmF ⟨⟨u.val, hu22⟩, (hrFC ⟨u.val, hu22⟩).trans (hrF ⟨u.val, hu22⟩)⟩)
            · exact writeReg_apply_of_not_mem _ _ _ w hm) (fun _ _ ↦ rfl))))).1, tAll, fAll⟩
attribute [irreducible] pDualSumCore_dsc50
end QuantumComputation.Specs.PhotochemistrySolution.DualSumCompact50K2

namespace QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp193K2

open PhotochemistrySolution.DeferMux2Wp198Opt
export _root_.QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt
    (Stage4ReflCoin24PotOraclePortBInPlace)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket_X ket_CNOT
    eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 (idxValPrefix
    idxValPrefix_lt_two_pow)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
    (xUnloadCzPairsSeqDyn count_xUnloadCzPairsSeqDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (mkVecOp_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB (subspaceStep_mul_right)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec (fin8Bin openBoxDist1D
    biasCoord biasCoord_eq_all signedAbsD9 openBoxDist1D_eq_signedAbsD9)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (openCoordDistSq disj_ne
    disj_of_ne potGen_d2_lt potGen_y36_lt potGen_k_lt potGen_mid_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.MidOW60 (MidOWU10Pkg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (word512DualLegLo6
    v1Fin8DualLeg v2Fin8DualLeg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.OddDivEval (natOfZModBits_split)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18 (decodePrimTree
    decodePrimTree_spec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulOWPersBridge (cowp_stepCB_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (midOW_lt0 midOW_lt1 midOW_ltY
    midOW_ltZ midOW_ltZHi midOW_ltCln)
def pCselHdr2Unld0_193 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
  xUnloadCzPairsSeqDyn v (r41 ⟨241, by omega⟩)
    [⟨r41 ⟨240, by omega⟩, ⟨wPotBIsNN r41, r41_ne r41 _ _ (by omega)⟩⟩]
    (xUnloadCzPairsSeqDyn v (r41 ⟨240, by omega⟩)
      [⟨r41 ⟨122 + Wp - 1, by omega⟩, ⟨wPotBIsScreen r41, r41_ne r41 _ _ (by omega)⟩⟩]
      (.circuit .identity))

theorem count_pCselHdr2Unld0_193 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) : (pCselHdr2Unld0_193 h193 v r41).count .T = 0 ∧
    (pCselHdr2Unld0_193 h193 v r41).count .TOFF = 0 := by
  unfold pCselHdr2Unld0_193
  simp only [fun w ps m ↦ (count_xUnloadCzPairsSeqDyn (Var := Var) v w ps m).1,
    fun w ps m ↦ (count_xUnloadCzPairsSeqDyn (Var := Var) v w ps m).2]
  exact ⟨rfl, rfl⟩

theorem ctrlSafe_pCselHdr2Unld0_193 {Var : Type} {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (h193 : 193 ≤ Wp) (v : Var) (r41 : QRegister (122 + Wp) n)
    (hST : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val → S_ctrl (r41 k) ∧ S_tgt
      (r41 k)) : DynCtrlSafe S_ctrl S_tgt (pCselHdr2Unld0_193 h193 v r41) := by
  have h (m : ℕ) (hm : m < 122 + Wp := by omega)
      (hi : IsNonNucPortB41Idx m := by
        first | exact Or.inl (by omega) | exact Or.inr (Or.inr (by omega))) := hST ⟨m, hm⟩ hi
  exact .of_dynWires (dw_xUnload (h 241) (fun _ hp ↦ (List.mem_singleton.mp hp) ▸ ⟨h 240, h 4⟩)
    (dw_xUnload (h 240) (fun _ hp ↦ (List.mem_singleton.mp hp) ▸ ⟨h (122 + Wp - 1), h 1⟩) trivial))
    (count_pCselHdr2Unld0_193 h193 v r41).2

theorem step_pCselHdr2Unld0_193 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp n : ℕ} [NeZero (2 ^ n)] (h193 : 193 ≤ Wp)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st0 : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (h240 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨240, by omega⟩) = 0)
    (h241 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨241, by omega⟩) = 0) :
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ hdrWrapMux h193 true r41 (st0 δ)) ph)
      (mkKetOpW rWork st0 ph)
      (pCselHdr2Unld0_193 h193 v r41) := by
  let stMid : BitAssignment n → BitAssignment n := fun δ ↦
    Function.update (st0 δ) (r41 ⟨240, by omega⟩)
      (st0 δ (r41 ⟨122 + Wp - 1, by omega⟩) * st0 δ (wPotBIsScreen r41))
  refine subspaceStep_of_eq_pre_local (mkKetOpW_congr rWork (fun δ _ ↦ ?_) (fun _ _ ↦ rfl))
    (subspaceStep_xUnloadSetProd_mkKetOpW v rWork (r41 ⟨241, by omega⟩) (r41 ⟨240, by omega⟩)
      (wPotBIsNN r41) (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega))
      (r41_ne r41 _ _ (by omega)) _ stMid ph (mkKetOpW rWork st0 ph)
      (fun δ hz ↦ (Function.update_of_ne (r41_ne r41 _ _ (by omega)) ..).trans (h241 δ hz))
      (subspaceStep_xUnloadSetProd_mkKetOpW v rWork (r41 ⟨240, by omega⟩)
        (r41 ⟨122 + Wp - 1, by omega⟩) (wPotBIsScreen r41)
        (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega))
        (.circuit .identity) st0 ph (mkKetOpW rWork st0 ph) h240
        (subspaceStep_id_mkKetOpW rWork st0 ph)))
  unfold hdrWrapMux
  simp only [↓reduceIte, stMid]
  rw [Function.update_self, Function.update_of_ne
    (r41_ne r41 (by omega) (by omega) (by omega) : wPotBIsNN r41 ≠ r41 ⟨240, by omega⟩)]

def pCselGateUnld0_193 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
  xUnloadCzPairsSeqDyn v (r41 ⟨122 + Wp - 1, by omega⟩)
    [⟨wPotBLocQ r41, ⟨wPotBIsPot r41, r41_ne r41 _ _ (by omega)⟩⟩]
    (.circuit .identity)

theorem count_pCselGateUnld0_193 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) : (pCselGateUnld0_193 h193 v r41).count .T = 0 ∧
    (pCselGateUnld0_193 h193 v r41).count .TOFF = 0 :=
  count_xUnloadCzPairsSeqDyn v (r41 ⟨122 + Wp - 1, by omega⟩)
    [⟨wPotBLocQ r41, ⟨wPotBIsPot r41, r41_ne r41 _ _ (by omega)⟩⟩] (.circuit .identity)

theorem ctrlSafe_pCselGateUnld0_193 {Var : Type} {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (h193 : 193 ≤ Wp) (v : Var) (r41 : QRegister (122 + Wp) n)
    (hST : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val → S_ctrl (r41 k) ∧ S_tgt
      (r41 k)) : DynCtrlSafe S_ctrl S_tgt (pCselGateUnld0_193 h193 v r41) := by
  have hwG := hST ⟨122 + Wp - 1, by omega⟩ (Or.inr (Or.inr (show 81 ≤ 122 + Wp - 1 by omega)))
  have hLocQ : S_ctrl (wPotBLocQ r41) ∧ S_tgt (wPotBLocQ r41) :=
      hST ⟨0, by omega⟩ (Or.inl (show 0 < 9 by omega))
  have hPot : S_ctrl (wPotBIsPot r41) ∧ S_tgt (wPotBIsPot r41) :=
      hST ⟨2, by omega⟩ (Or.inl (show 2 < 9 by omega))
  refine .of_dynWires ?_ (count_pCselGateUnld0_193 h193 v r41).2
  exact dw_xUnload hwG (fun p hp ↦ (List.mem_singleton.mp hp) ▸ ⟨hLocQ, hPot⟩) trivial

theorem step_pCselGateUnld0_193 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp n : ℕ} [NeZero (2 ^ n)] (h193 : 193 ≤ Wp)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st0 : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hwG0 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨122 + Wp - 1, by omega⟩) = 0) :
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ gateWrapMux h193 true r41 (st0 δ)) ph)
      (mkKetOpW rWork st0 ph)
      (pCselGateUnld0_193 h193 v r41) := by
  unfold gateWrapMux pCselGateUnld0_193
  simp only [↓reduceIte]
  exact subspaceStep_xUnloadSetProd_mkKetOpW v rWork (r41 ⟨122 + Wp - 1, by omega⟩)
    (wPotBLocQ r41) (wPotBIsPot r41)
    (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega)) (r41_ne r41 _ _ (by omega))
    (.circuit .identity) st0 ph (mkKetOpW rWork st0 ph) hwG0
    (subspaceStep_id_mkKetOpW rWork st0 ph)


def idxMono9_193 {Wp : ℕ} (h193 : 193 ≤ Wp) : Fin 9 → Fin (122 + Wp)
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨4, by omega⟩
  | ⟨3, _⟩ => ⟨122, by omega⟩
  | ⟨4, _⟩ => ⟨125, by omega⟩
  | ⟨5, _⟩ => ⟨126, by omega⟩
  | ⟨6, _⟩ => ⟨240, by omega⟩
  | ⟨7, _⟩ => ⟨241, by omega⟩
  | ⟨8, _⟩ => ⟨122 + Wp - 1, by omega⟩

theorem idxMono9_inj_193 {Wp : ℕ} (h193 : 193 ≤ Wp) : Function.Injective (idxMono9_193 h193) := by
  intro i j hij
  have hval := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> simp only [idxMono9_193] at hval <;> first | rfl | omega

def rMono9_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) : QRegister 9 n :=
    ⟨⟨fun i ↦ r41 (idxMono9_193 h193 i), fun _ _ h ↦ idxMono9_inj_193 h193 (r41.wires.injective h)⟩⟩
theorem rMono9_ne_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) (i j : Fin 9)
    (hij : i ≠ j) : rMono9_193 h193 r41 i ≠ rMono9_193 h193 r41 j := fun h ↦
    hij ((rMono9_193 h193 r41).wires.injective h)
theorem rMono9_st_193 {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop} (h193 : 193 ≤ Wp)
    (r41 : QRegister (122 + Wp) n) (hST : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val →
    S_ctrl (r41 k) ∧ S_tgt (r41 k)) (i : Fin 9) :
    S_ctrl (rMono9_193 h193 r41 i) ∧ S_tgt (rMono9_193 h193 r41 i) :=
  hST (idxMono9_193 h193 i) (by
    fin_cases i <;> simp only [idxMono9_193, IsNonNucPortB41Idx] <;>
      first | exact Or.inl (by omega) | exact Or.inr (Or.inr (by omega)))

def wMono_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) : Fin 3 → Fin (2 ^ 1) →
    Wire n
  | ⟨0, _⟩, ⟨0, _⟩ => rMono9_193 h193 r41 1
  | ⟨0, _⟩, ⟨1, _⟩ => rMono9_193 h193 r41 8
  | ⟨1, _⟩, ⟨0, _⟩ => rMono9_193 h193 r41 0
  | ⟨1, _⟩, ⟨1, _⟩ => rMono9_193 h193 r41 6
  | ⟨2, _⟩, ⟨0, _⟩ => rMono9_193 h193 r41 2
  | ⟨2, _⟩, ⟨1, _⟩ => rMono9_193 h193 r41 7

theorem rMono9_apply_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) (i : Fin 9) :
    rMono9_193 h193 r41 i = r41 (idxMono9_193 h193 i) := rfl

theorem wMono_mem_rm {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n)
    (b : Fin 3) (p : Fin (2 ^ 1)) :
    ∃ i : Fin 9, i ≠ 3 ∧ wMono_193 h193 r41 b p = rMono9_193 h193 r41 i := by
  fin_cases b <;> fin_cases p <;> exact ⟨_, by decide, rfl⟩

theorem rMono9_ne_outside {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n)
    (i : Fin 9) (k : Fin (122 + Wp)) (hOut : k.val = 0 ∨ k.val = 123 ∨ k.val = 124) :
    rMono9_193 h193 r41 i ≠ r41 k := by
  intro h
  have hv := congrArg Fin.val (r41.wires.injective h)
  fin_cases i <;> simp only [idxMono9_193] at hv <;> omega

theorem wOptInj_mono_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    WOptInj 3 1 (uLoMono r41) (wMono_193 h193 r41)
      (rMono9_193 h193 r41 3) (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩) where
  w_inj b₁ p₁ b₂ p₂ h := by
    fin_cases b₁ <;> fin_cases p₁ <;> fin_cases b₂ <;> fin_cases p₂ <;>
      first | exact ⟨rfl, rfl⟩ | exact absurd h (rMono9_ne_193 h193 r41 _ _ (by decide))
  uLo_ne_w _ b p h := (wMono_mem_rm h193 r41 b p).elim fun i ⟨_, hw⟩ ↦
    rMono9_ne_outside h193 r41 i ⟨0, by omega⟩ (Or.inl rfl) (hw.symm.trans h.symm)
  uLo_ne_rDum _ h := rMono9_ne_outside h193 r41 3 ⟨0, by omega⟩ (Or.inl rfl) h.symm
  uLo_ne_wDum _ := r41_ne r41 _ _ (by omega)
  uLo_ne_qEnc _ := r41_ne r41 _ _ (by omega)
  w_ne_rDum b p h := (wMono_mem_rm h193 r41 b p).elim fun i ⟨hi3, hw⟩ ↦
    rMono9_ne_193 h193 r41 i 3 hi3 (hw.symm.trans h)
  w_ne_wDum b p h := (wMono_mem_rm h193 r41 b p).elim fun i ⟨_, hw⟩ ↦
    rMono9_ne_outside h193 r41 i _ (Or.inr (Or.inl rfl)) (hw.symm.trans h)
  w_ne_qEnc b p h := (wMono_mem_rm h193 r41 b p).elim fun i ⟨_, hw⟩ ↦
    rMono9_ne_outside h193 r41 i _ (Or.inr (Or.inr rfl)) (hw.symm.trans h)
  rDum_ne_wDum := r41_ne r41 _ _ (by omega)
  rDum_ne_qEnc := r41_ne r41 _ _ (by omega)
  wDum_ne_qEnc := r41_ne r41 _ _ (by omega)

def cMonoPre_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) : Circuit n :=
  let rm := rMono9_193 h193 r41
  Circuit.seq (Circuit.CNOT (rm 0) (rm 4) (rMono9_ne_193 h193 r41 0 4 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 2) (rm 5) (rMono9_ne_193 h193 r41 2 5 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 1) (rm 3) (rMono9_ne_193 h193 r41 1 3 (by decide))) <|
  Circuit.seq (Circuit.X (rm 3)) <|
  Circuit.seq (Circuit.CNOT (rm 0) (rm 1) (rMono9_ne_193 h193 r41 0 1 (by decide))) <|
  Circuit.CNOT (rm 2) (rm 0) (rMono9_ne_193 h193 r41 2 0 (by decide))

def cMonoPost_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) : Circuit n :=
  let rm := rMono9_193 h193 r41
  Circuit.seq (Circuit.CNOT (rm 2) (rm 0) (rMono9_ne_193 h193 r41 2 0 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 7) (rm 6) (rMono9_ne_193 h193 r41 7 6 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 0) (rm 1) (rMono9_ne_193 h193 r41 0 1 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 6) (rm 8) (rMono9_ne_193 h193 r41 6 8 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 6) (rm 0) (rMono9_ne_193 h193 r41 6 0 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 8) (rm 1) (rMono9_ne_193 h193 r41 8 1 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 7) (rm 2) (rMono9_ne_193 h193 r41 7 2 (by decide))) <|
  Circuit.seq (Circuit.X (rm 3)) <|
  Circuit.seq (Circuit.CNOT (rm 1) (rm 3) (rMono9_ne_193 h193 r41 1 3 (by decide))) <|
  Circuit.seq (Circuit.CNOT (rm 0) (rm 4) (rMono9_ne_193 h193 r41 0 4 (by decide))) <|
  Circuit.CNOT (rm 2) (rm 5) (rMono9_ne_193 h193 r41 2 5 (by decide))

def pCselMonoHdrComp_193 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
  (DynamicCircuit.circuit (cMonoPre_193 h193 r41)).seq
    ((wLastSplitShiftDyn v 3 0 (uLoMono r41) (wMono_193 h193 r41)
        (rMono9_193 h193 r41 3) (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩)
        (wOptInj_mono_193 h193 r41)).seq
      (DynamicCircuit.circuit (cMonoPost_193 h193 r41)))

theorem count_cMonoPre_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    (cMonoPre_193 h193 r41).count .T = 0 ∧ (cMonoPre_193 h193 r41).count .TOFF = 0 := by
  unfold cMonoPre_193
  simp only [Circuit.count_seq, (count_cnot_zero _ _ _).1, (count_cnot_zero _ _ _).2,
    (count_x_zero _).1, (count_x_zero _).2, add_zero, and_self]

theorem count_cMonoPost_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    (cMonoPost_193 h193 r41).count .T = 0 ∧ (cMonoPost_193 h193 r41).count .TOFF = 0 := by
  unfold cMonoPost_193
  simp only [Circuit.count_seq, (count_cnot_zero _ _ _).1, (count_cnot_zero _ _ _).2,
    (count_x_zero _).1, (count_x_zero _).2, add_zero, and_self]

theorem count_pCselMonoHdrComp_193 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (v : Var)
    (r41 : QRegister (122 + Wp) n) : (pCselMonoHdrComp_193 h193 v r41).count .T = 8 ∧
    (pCselMonoHdrComp_193 h193 v r41).count .TOFF =
    0 := by
  obtain ⟨t1, f1⟩ := count_cMonoPre_193 h193 r41
  obtain ⟨t2, f2⟩ := count_wLastSplitShiftDyn v 3 0 (uLoMono r41) (wMono_193 h193 r41)
    (rMono9_193 h193 r41 3) (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩) (wOptInj_mono_193 h193 r41)
  obtain ⟨t3, f3⟩ := count_cMonoPost_193 h193 r41
  unfold pCselMonoHdrComp_193
  rw [dc_count_seq, dc_count_seq, dc_count_circ, dc_count_circ, t1, t2, t3,
      dc_count_seq, dc_count_seq, dc_count_circ, dc_count_circ, f1, f2, f3]
  exact ⟨by omega, rfl⟩

theorem ctrlSafe_pCselMonoHdrComp_193 {Var : Type} {Wp n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (h193 : 193 ≤ Wp) (v : Var) (r41 : QRegister (122 + Wp) n)
    (hST : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val → S_ctrl (r41 k) ∧ S_tgt
      (r41 k)) : DynCtrlSafe S_ctrl S_tgt (pCselMonoHdrComp_193 h193 v r41) := by
  have hm := rMono9_st_193 h193 r41 hST
  exact .of_dynWires ⟨⟨cw_cnot (hm 0) (hm 4), cw_cnot (hm 2) (hm 5), cw_cnot (hm 1) (hm 3),
      cw_1 (hm 3), cw_cnot (hm 0) (hm 1), cw_cnot (hm 2) (hm 0)⟩,
    dw_wLastSplitShiftDyn v 3 0 (uLoMono r41) (wMono_193 h193 r41)
      (rMono9_193 h193 r41 3) (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩)
          (wOptInj_mono_193 h193 r41)
      (fun _ ↦ hST ⟨0, by omega⟩ (Or.inl (show 0 < 9 by omega)))
      (fun b p ↦ by fin_cases b <;> fin_cases p <;> exact hm _)
      (hm 3) (hST ⟨123, by omega⟩ (Or.inr (Or.inr (show 81 ≤ 123 by omega))))
      (hST ⟨124, by omega⟩ (Or.inr (Or.inr (show 81 ≤ 124 by omega)))),
    ⟨cw_cnot (hm 2) (hm 0), cw_cnot (hm 7) (hm 6), cw_cnot (hm 0) (hm 1), cw_cnot (hm 6) (hm 8),
      cw_cnot (hm 6) (hm 0), cw_cnot (hm 8) (hm 1), cw_cnot (hm 7) (hm 2), cw_1 (hm 3),
      cw_cnot (hm 1) (hm 3), cw_cnot (hm 0) (hm 4), cw_cnot (hm 2) (hm 5)⟩⟩
    (count_pCselMonoHdrComp_193 h193 v r41).2
theorem eval_cMonoPre_ket_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n)
    (β : BitAssignment n) (scr pot nn : ZMod 2) : (cMonoPre_193 h193 r41).eval.1.mulVec
    (ket (writeReg β (rMono9_193 h193 r41) (mkVec9 scr pot nn 0 0 0 0 0 0))) =
        ket (writeReg β (rMono9_193 h193 r41) (vMonoPre scr pot nn)) := by
  let rm := rMono9_193 h193 r41
  unfold cMonoPre_193 vMonoPre
  dsimp only
  repeat rw [eval_seq_mulVec]
  rw [ket_CNOT_writeReg rm 0 4 (by decide), upd9_4, ket_CNOT_writeReg rm 2 5 (by decide), upd9_5,
      ket_CNOT_writeReg rm 1 3 (by decide), upd9_3, ket_X_writeReg rm 3, upd9_3]
  dsimp only [mkVec9]
  rw [ket_CNOT_writeReg rm 0 1 (by decide), upd9_1, ket_CNOT_writeReg rm 2 0 (by decide), upd9_0]
  congr 2
  rcases zmod2_cases scr with rfl | rfl <;>
    rcases zmod2_cases pot with rfl | rfl <;>
    rcases zmod2_cases nn with rfl | rfl <;> (funext i; fin_cases i <;> rfl)

theorem eval_cMonoPost_ket_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n)
    (β : BitAssignment n) (locQ scr pot nn : ZMod 2) (hps : pot = 0 → scr = 0)
    (hsn : scr = 0 → nn = 0) :
    (cMonoPost_193 h193 r41).eval.1.mulVec (ket (writeReg β (rMono9_193 h193 r41)
        (vMonoMid locQ scr pot nn))) = ket (writeReg β (rMono9_193 h193 r41)
        (vMonoPost locQ scr pot nn)) := by
  let rm := rMono9_193 h193 r41
  unfold cMonoPost_193 vMonoMid vMonoPost
  dsimp only
  repeat rw [eval_seq_mulVec]
  rw [ket_CNOT_writeReg rm 2 0 (by decide), upd9_0, ket_CNOT_writeReg rm 7 6 (by decide), upd9_6,
      ket_CNOT_writeReg rm 0 1 (by decide), upd9_1, ket_CNOT_writeReg rm 6 8 (by decide), upd9_8]
  dsimp only [mkVec9]
  rw [ket_CNOT_writeReg rm 6 0 (by decide), upd9_0, ket_CNOT_writeReg rm 8 1 (by decide), upd9_1,
      ket_CNOT_writeReg rm 7 2 (by decide), upd9_2, ket_X_writeReg rm 3, upd9_3]
  dsimp only [mkVec9]
  rw [ket_CNOT_writeReg rm 1 3 (by decide), upd9_3, ket_CNOT_writeReg rm 0 4 (by decide), upd9_4,
      ket_CNOT_writeReg rm 2 5 (by decide), upd9_5]
  congr 2
  rcases zmod2_cases pot with rfl | rfl <;> rcases zmod2_cases scr with rfl | rfl <;>
    rcases zmod2_cases nn with rfl | rfl <;> first
      | exact absurd (hps rfl) one_ne_zero
      | exact absurd (hsn rfl) one_ne_zero
      | (rcases zmod2_cases locQ with rfl | rfl <;> (funext i; fin_cases i <;> rfl))

def bStarMono_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n)
    (γ : BitAssignment n) : Fin 3 :=
    if γ (rMono9_193 h193 r41 4) = 0 then 0 else if γ (rMono9_193 h193 r41 5) = 0 then 1 else 2
theorem step_pCselMonoHdrComp_193 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp n : ℕ} [NeZero (2 ^ n)] (h193 : 193 ≤ Wp)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st0 : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hMon : ∀ δ, (∀ q, δ (rWork q) = 0) →
      (st0 δ (wPotBIsPot r41) = 0 → st0 δ (wPotBIsScreen r41) = 0) ∧
      (st0 δ (wPotBIsScreen r41) = 0 → st0 δ (wPotBIsNN r41) = 0))
    (h122 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨122, by omega⟩) = 0)
    (h123 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨123, by omega⟩) = 0)
    (h124 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨124, by omega⟩) = 0)
    (h125 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨125, by omega⟩) = 0)
    (h126 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨126, by omega⟩) = 0)
    (h240 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨240, by omega⟩) = 0)
    (h241 : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨241, by omega⟩) = 0)
    (hwG : ∀ δ, (∀ q, δ (rWork q) = 0) → st0 δ (r41 ⟨122 + Wp - 1, by omega⟩) = 0) :
    SubspaceStep
      (mkKetOpW rWork st0 ph)
      (mkKetOpW rWork (fun δ ↦ hdrWrapMux h193 true r41 (gateWrapMux h193 true r41 (st0 δ))) ph)
      (pCselMonoHdrComp_193 h193 v r41) := by
  have writeReg_vMonoPost_eq_hdrGate_193 (β : BitAssignment n)
      (h122 : β (r41 ⟨122, by omega⟩) = 0) (h125 : β (r41 ⟨125, by omega⟩) = 0)
      (h126 : β (r41 ⟨126, by omega⟩) = 0) :
      writeReg β (rMono9_193 h193 r41) (vMonoPost (β (wPotBLocQ r41)) (β (wPotBIsScreen r41))
        (β (wPotBIsPot r41)) (β (wPotBIsNN r41))) =
            hdrWrapMux h193 true r41 (gateWrapMux h193 true r41 β) := by
    let rm := rMono9_193 h193 r41
    have hKeep {m : ℕ} (hm : m < 122 + Wp := by omega) (h1 : m ≠ 241 := by omega)
        (h2 : m ≠ 240 := by omega) (h3 : m ≠ 122 + Wp - 1 := by omega) :
        β (r41 ⟨m, hm⟩) = hdrWrapMux h193 true r41 (gateWrapMux h193 true r41 β) (r41 ⟨m, hm⟩) := by
      unfold hdrWrapMux gateWrapMux
      simp only [↓reduceIte, Function.update_of_ne (r41_ne r41 _ _ h1),
        Function.update_of_ne (r41_ne r41 _ _ h2), Function.update_of_ne (r41_ne r41 _ _ h3)]
    funext w
    by_cases hw : ∃ i : Fin 9, rm i = w
    · obtain ⟨i, rfl⟩ := hw
      rw [writeReg_apply_reg]
      unfold vMonoPost
      fin_cases i <;> first
        | exact hKeep
        | exact h122.symm.trans hKeep
        | exact h125.symm.trans hKeep
        | exact h126.symm.trans hKeep
        | (unfold hdrWrapMux gateWrapMux
           simp only [↓reduceIte, mkVec9, rm, rMono9_apply_193, idxMono9_193])
      · rw [Function.update_of_ne (r41_ne r41 _ _ (by omega)), Function.update_self,
            Function.update_self,
            Function.update_of_ne (r41_ne r41 _ _ (by omega) : wPotBIsScreen r41 ≠ r41 ⟨122 + Wp -
                1, by omega⟩)]
      · rw [Function.update_self, Function.update_self,
            Function.update_of_ne (r41_ne r41 _ _ (by omega) : wPotBIsScreen r41 ≠ r41 ⟨122 + Wp -
                1, by omega⟩),
            Function.update_of_ne (r41_ne r41 _ _ (by omega) : wPotBIsNN r41 ≠ r41 ⟨122 + Wp - 1,
                by omega⟩)]
      · rw [Function.update_of_ne (r41_ne r41 _ _ (by omega)),
            Function.update_of_ne (r41_ne r41 _ _ (by omega)), Function.update_self]
    · rw [writeReg_apply_of_not_mem _ rm _ w hw]
      unfold hdrWrapMux gateWrapMux
      simp only [↓reduceIte]
      rw [Function.update_of_ne (show w ≠ r41 ⟨241, by omega⟩ from fun h ↦ hw ⟨7, h.symm⟩),
          Function.update_of_ne (show w ≠ r41 ⟨240, by omega⟩ from fun h ↦ hw ⟨6, h.symm⟩),
          Function.update_of_ne (show w ≠ r41 ⟨122 + Wp - 1, by omega⟩ from fun h ↦ hw ⟨8, h.symm⟩)]
  have ket_writeReg_upd_rm (β : BitAssignment n) (f g : Fin 9 → ZMod 2) (k : Fin 9)
      (hfg : ∀ i : Fin 9, (if i = k then (1 : ZMod 2) else f i) = g i) :
      ket (Function.update (writeReg β (rMono9_193 h193 r41) f) (rMono9_193 h193 r41 k) 1) =
        ket (writeReg β (rMono9_193 h193 r41) g) := by
    rw [update_writeReg_reg]
    exact congrArg ket (congrArg (writeReg β _)
        (funext fun i ↦ (Function.update_apply f k 1 i).trans (hfg i)))
  let rm := rMono9_193 h193 r41
  let P_all : BitAssignment n → Prop := fun _ ↦ True
  let actPred : BitAssignment n → Prop := fun γ ↦ γ (rm 3) = 0
  let γBaseFn : BitAssignment n → BitAssignment n := fun δ ↦
    writeReg (st0 δ) rm (vMonoBase (st0 δ (wPotBIsScreen r41)) (st0 δ (wPotBIsPot r41))
        (st0 δ (wPotBIsNN r41)))
  let M0 : Operator (2 ^ n) := mkKetOpW rWork γBaseFn ph
  have hInitEq (δ) (hz : ∀ q, δ (rWork q) = 0) : st0 δ = writeReg (st0 δ) rm
      (mkVec9 (st0 δ (wPotBIsScreen r41)) (st0 δ (wPotBIsPot r41))
          (st0 δ (wPotBIsNN r41)) 0 0 0 0 0 0) := by
    refine (writeReg_self_local (st0 δ) rm).symm.trans (congrArg (writeReg (st0 δ) rm)
        (funext fun i ↦ ?_))
    fin_cases i <;> first
      | rfl | exact h122 δ hz | exact h125 δ hz | exact h126 δ hz
      | exact h240 δ hz | exact h241 δ hz | exact hwG δ hz
  have hBaseValid (δ) (hz : ∀ q, δ (rWork q) = 0) :
      OptBasePred P_all (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩) (γBaseFn δ) ∧
      ∀ (b : Fin 3) (p : Fin (2 ^ 1)), γBaseFn δ (wMono_193 h193 r41 b p) = 0 :=
    ⟨⟨trivial,
      (writeReg_apply_of_not_mem _ rm _ _ (fun ⟨i, hi⟩ ↦
        rMono9_ne_outside h193 r41 i _ (Or.inr (Or.inl rfl)) hi)).trans (h123 δ hz),
      (writeReg_apply_of_not_mem _ rm _ _ (fun ⟨i, hi⟩ ↦
        rMono9_ne_outside h193 r41 i _ (Or.inr (Or.inr rfl)) hi)).trans (h124 δ hz)⟩,
     fun b p ↦
         by fin_cases b <;> fin_cases p <;> simp only [rm, γBaseFn, wMono_193, writeReg_apply_reg,
              vMonoBase, mkVec9]⟩
  have hOpPreEq : (cMonoPre_193 h193 r41).eval.1 * mkKetOpW rWork st0 ph =
      oneHotOptPreOp (OptBasePred P_all (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩))
        actPred (bStarMono_193 h193 r41) (uLoMono r41) (wMono_193 h193 r41) 0 (Nat.le_succ 0) *
            M0 := by
    apply matrix_ext_ket
    intro δ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        mkKetOpW_mulVec_ket, show M0 = mkKetOpW rWork γBaseFn ph from rfl, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      congr 1
      have ⟨hps, hsn⟩ := hMon δ hz
      rw [show (cMonoPre_193 h193 r41).eval.1.mulVec (ket (st0 δ)) =
          ket (writeReg (st0 δ) rm (vMonoPre (st0 δ (wPotBIsScreen r41)) (st0 δ (wPotBIsPot r41))
              (st0 δ (wPotBIsNN r41)))) by
        conv_lhs => rw [hInitEq δ hz]
        exact eval_cMonoPre_ket_193 h193 r41 (st0 δ) _ _ _]
      simp only [oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec]
      rw [ite_eq_left (hBaseValid δ hz),
          (Fin.ext rfl : (⟨idxValPrefix (uLoMono r41) (γBaseFn δ) 0 (Nat.le_succ 0),
            Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow (uLoMono r41) (γBaseFn δ) 0 (Nat.le_succ 0))
              (Nat.pow_le_pow_right (by omega) (Nat.le_succ 0))⟩ : Fin (2 ^ 1)) = 0)]
      dsimp only [actPred, bStarMono_193, γBaseFn]
      simp only [rm, writeReg_apply_reg, vMonoBase, mkVec9]
      set scr := st0 δ (wPotBIsScreen r41)
      set pot := st0 δ (wPotBIsPot r41)
      set nn := st0 δ (wPotBIsNN r41)
      rcases zmod2_cases pot with hpot | hpot
      · rw [hpot, hps hpot, hsn (hps hpot), show (1 + 0 : ZMod 2) = 1 from rfl,
            ite_eq_right one_ne_zero]
        exact congrArg ket (congrArg (writeReg (st0 δ) rm) (funext fun i ↦ by fin_cases i <;> rfl))
      · rw [hpot, show (1 + 1 : ZMod 2) = 0 from rfl, ite_eq_left rfl]
        rcases zmod2_cases scr with hscr | hscr
        · rw [hscr, hsn hscr, ite_eq_left rfl]
          exact (ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 0 0 0 0 0) _ 1 (fun i ↦
              by fin_cases i <;> rfl)).symm
        · rw [hscr, ite_eq_right one_ne_zero]
          rcases zmod2_cases nn with hnn | hnn
          · rw [hnn, ite_eq_left rfl]
            exact (ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 1 0 0 0 0) _ 0 (fun i ↦
                by fin_cases i <;> rfl)).symm
          · rw [hnn, ite_eq_right one_ne_zero]
            exact (ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 1 1 0 0 0) _ 2 (fun i ↦
                by fin_cases i <;> rfl)).symm
    · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  let R2 : Operator (2 ^ n) :=
    oneHotOptPreOp (OptBasePred P_all (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩))
      actPred (bStarMono_193 h193 r41) (uLoMono r41) (wMono_193 h193 r41) 1 le_rfl * M0
  have hOpPostEq : (cMonoPost_193 h193 r41).eval.1 * R2 =
      mkKetOpW rWork (fun δ ↦ hdrWrapMux h193 true r41 (gateWrapMux h193 true r41 (st0 δ))) ph := by
    apply matrix_ext_ket
    intro δ
    rw [← Matrix.mulVec_mulVec, show R2 = _ * M0 from rfl, ← Matrix.mulVec_mulVec,
        show M0 = mkKetOpW rWork γBaseFn ph from rfl, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      congr 1
      have ⟨hps, hsn⟩ := hMon δ hz
      have hLocEq : γBaseFn δ (wPotBLocQ r41) = st0 δ (wPotBLocQ r41) :=
        writeReg_apply_of_not_mem _ rm _ _ (fun ⟨i, hi⟩ ↦ rMono9_ne_outside h193 r41 i ⟨0, by omega⟩
            (Or.inl rfl) hi)
      set locQ := st0 δ (wPotBLocQ r41)
      set scr := st0 δ (wPotBIsScreen r41)
      set pot := st0 δ (wPotBIsPot r41)
      set nn := st0 δ (wPotBIsNN r41)
      have hR2Ket : (oneHotOptPreOp (OptBasePred P_all (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩))
          actPred (bStarMono_193 h193 r41) (uLoMono r41)
              (wMono_193 h193 r41) 1 le_rfl).mulVec (ket (γBaseFn δ)) =
          ket (writeReg (st0 δ) rm (vMonoMid locQ scr pot nn)) := by
        simp only [oneHotOptPreOp, mkVecOp_mulVec_ket, oneHotOptPreVec]
        rw [ite_eq_left (hBaseValid δ hz), show (⟨idxValPrefix (uLoMono r41) (γBaseFn δ) 1 le_rfl,
            Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow (uLoMono r41) (γBaseFn δ) 1 le_rfl)
              (Nat.pow_le_pow_right (by omega) le_rfl)⟩ : Fin (2 ^ 1)) = if locQ =
                  1 then 1 else 0 from Fin.ext (by
          simp only [idxValPrefix, uLoMono, hLocEq]
          rcases zmod2_cases locQ with hlq | hlq <;> (rw [hlq]; decide))]
        dsimp only [actPred, bStarMono_193, γBaseFn]
        simp only [rm, writeReg_apply_reg, vMonoBase, mkVec9,
          show st0 δ (wPotBIsScreen r41) = scr from rfl,
          show st0 δ (wPotBIsPot r41) = pot from rfl, show st0 δ (wPotBIsNN r41) = nn from rfl]
        rcases zmod2_cases pot with hpot | hpot
        · rw [hpot, hps hpot, hsn (hps hpot), show (1 + 0 : ZMod 2) = 1 from rfl,
              ite_eq_right one_ne_zero]
          rcases zmod2_cases locQ with hlq | hlq <;>
            (rw [hlq]; exact congrArg ket (congrArg (writeReg (st0 δ) rm)
                (funext fun i ↦ by fin_cases i <;> rfl)))
        · rw [hpot, show (1 + 1 : ZMod 2) = 0 from rfl, ite_eq_left rfl]
          rcases zmod2_cases locQ with hlq | hlq <;> rcases zmod2_cases scr with hscr | hscr
          · rw [hlq, hscr, hsn hscr, ite_eq_right zero_ne_one, ite_eq_left rfl]
            exact ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 0 0 0 0 0) _ 1 (fun i ↦
                by fin_cases i <;> rfl)
          · rw [hlq, hscr, ite_eq_right zero_ne_one, ite_eq_right one_ne_zero]
            rcases zmod2_cases nn with hnn | hnn
            · rw [hnn, ite_eq_left rfl]
              exact ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 1 0 0 0 0) _ 0 (fun i ↦
                  by fin_cases i <;> rfl)
            · rw [hnn, ite_eq_right one_ne_zero]
              exact ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 1 1 0 0 0) _ 2 (fun i ↦
                  by fin_cases i <;> rfl)
          · rw [hlq, hscr, hsn hscr, ite_eq_left rfl, ite_eq_left rfl]
            exact ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 0 0 0 0 0) _ 8 (fun i ↦
                by fin_cases i <;> rfl)
          · rw [hlq, hscr, ite_eq_left rfl, ite_eq_right one_ne_zero]
            rcases zmod2_cases nn with hnn | hnn
            · rw [hnn, ite_eq_left rfl]
              exact ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 1 0 0 0 0) _ 6 (fun i ↦
                  by fin_cases i <;> rfl)
            · rw [hnn, ite_eq_right one_ne_zero]
              exact ket_writeReg_upd_rm (st0 δ) (mkVec9 0 0 0 0 1 1 0 0 0) _ 7 (fun i ↦
                  by fin_cases i <;> rfl)
      rw [hR2Ket, eval_cMonoPost_ket_193 h193 r41 (st0 δ) locQ scr pot nn hps hsn,
          writeReg_vMonoPost_eq_hdrGate_193 (st0 δ) (h122 δ hz) (h125 δ hz) (h126 δ hz)]
    · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact subspaceStep_seq_u
    (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) (mkKetOpW rWork st0 ph)
        (cMonoPre_193 h193 r41)) hOpPreEq)
    (subspaceStep_seq_u
      (subspaceStep_mul_right M0 (subspaceStep_wLastSplitShiftDyn v P_all actPred (bStarMono_193
          h193 r41)
        (uLoMono r41) (wMono_193 h193 r41) (rm 3) (r41 ⟨123, by omega⟩) (r41 ⟨124, by omega⟩)
            (wOptInj_mono_193 h193 r41)
        (fun γ _ ↦ by
          dsimp only [actPred]
          rcases zmod2_cases (γ (rm 3)) with h0 | h1
          · rw [h0, ite_eq_left rfl]
          · rw [h1, ite_eq_right one_ne_zero])))
      (subspaceStep_congr_out (subspaceStep_of_circuit (Var :=
          Var) R2 (cMonoPost_193 h193 r41)) hOpPostEq))


theorem stDualH_dm2_work_zero_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n)
    {u : ℕ} (huLtWp : u < Wp) (hu1 : u ≠ 118) (hu2 : u ≠ 119)
    (hNoGate : isCsel = false ∨ u ≠ Wp - 1)
    (hNoM1 : u < Wtop Wp isCsel - 48 ∨ Wtop Wp isCsel - 24 ≤ u) :
    stDualH_dm2 h193 isCsel r41 z16 β (r41 ⟨122 + u, by omega⟩) = 0 := by
  unfold stDualH_dm2
  rw [hdrWrapMux_keep h193 isCsel r41 _ (122 + u) _ (by omega) (by omega)]
  exact muxStNoM2_pool_zero h193 isCsel r41 0 z16 β huLtWp hNoGate (by omega)

theorem dualHdr_target_eq_dm2_193 {Wp kMid tMid n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgMid : MidOWU10Pkg true 14 kMid tMid)
    (r41 : QRegister (122 + Wp) n)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n)
    (hVF : ValidPotBFlags r41 β)
    (cL2A : Fin 3 → Fin 256)
    (hcL2A : cL2A = if β (wPotBIsNN r41) == 1 then coordOfReg24 (rPotBElecA r41) β
      else coordOfReg24 (rPotBNucA r41) β) :
    let stH := stDualH_dm2 h193 isCsel r41 z16 β
    let rH5 := rMuxLeg1Hdr5 h193 isCsel r41
    let sp1 := speciesOfBits2 (stH (rH5 ⟨3, ow3_lt5⟩)) (stH (rH5 ⟨4, ow4_lt5⟩))
    let p1 := pre6OfCoords (coordOfReg24 (rPotBNucA r41) β) (coordOfReg24 (rPotBElecA r41) β)
    let p2 := pre6OfCoords cL2A (coordOfReg24 (rPotBPortB r41) β)
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60 pkgMid
    (((stH (rH5 ⟨0, ow0_lt5⟩) == 1) = false ∧ (stH (rH5 ⟨1, ow1_lt5⟩) == 1) = false ∧
      (stH (rH5 ⟨2, ow2_lt5⟩) == 1) = false) ∨
     ((stH (rH5 ⟨0, ow0_lt5⟩) == 1) = true ∧
      ((stH (rH5 ⟨1, ow1_lt5⟩) == 1) = false → (stH (rH5 ⟨2, ow2_lt5⟩) == 1) = false))) ∧
    (if stH (rH5 ⟨0, ow0_lt5⟩) == 1 then
      (v1U10Pre5 (stH (rH5 ⟨1, ow1_lt5⟩) == 1) (stH (rH5 ⟨2, ow2_lt5⟩) == 1) sp1 (pre5OfPre6 p1) +
       v2U10Pre5 (stH (rH5 ⟨1, ow1_lt5⟩) == 1)
           (stH (rH5 ⟨2, ow2_lt5⟩) == 1) 0 (pre5OfPre6 p2)) % 2 ^ 17
     else 0) =
    (v1Mux isCsel pkgLM r41 β + v2Mux isCsel pkgLM r41 β) % 2 ^ 17 := by
  intro stH rH5 sp1 p1 p2 pkgLM
  have hLt (w : Wire n) {j : Fin 5} (hr : rH5 j = w) {m : ℕ} (hm : m < 106 := by omega)
      (hw : w = r41 ⟨m, by omega⟩ := by rfl) : stH (rH5 j) = β w := by
    rw [hr, hw]
    exact stDualH_dm2_lt106 h193 isCsel r41 z16 β hm
  have hSpEq : sp1 = speciesOfBits2 (β (wPotBSp1B0 r41)) (β (wPotBSp1B1 r41)) := by
    dsimp only [sp1]
    rw [hLt _ (rMuxLeg1Hdr5_3 h193 isCsel r41) (m := 5),
        hLt _ (rMuxLeg1Hdr5_4 h193 isCsel r41) (m := 6)]
  have hPre1 : pre5OfPre6 p1 = _ := pre5OfPre6_pre6OfCoords _ _
  have hPre2 : pre5OfPre6 p2 = PhotochemistrySolution.Sh14P5Mux17.pre5OfFin8
      (PhotochemistrySolution.ReflStage4.owB2Of3Port (β (wPotBIsNN r41) == 1)
        (coordOfReg24 (rPotBNucA r41) β) (coordOfReg24 (rPotBPortB r41) β)
        (coordOfReg24 (rPotBElecA r41) β)) := by
    dsimp only [p2]
    rw [pre5OfPre6_pre6OfCoords, hcL2A, owLeg2_coords_b2]
  have hv1M : pkgLM.v1Fin8 = v1Fin8U10Local := v1Fin8U10Local_eq_dualLeg.symm
  have hv2M : pkgLM.v2Fin8 = v2Fin8U10Local := v2Fin8U10Local_eq_dualLeg.symm
  cases isCsel
  · rw [hLt _ (rMuxLeg1Hdr5_0_false h193 r41) (m := 2),
        hLt _ (rMuxLeg1Hdr5_1_false h193 r41) (m := 1),
        hLt _ (rMuxLeg1Hdr5_2_false h193 r41) (m := 4)]
    refine ⟨routed_or_of_validFlags hVF, ?_⟩
    unfold v1Mux v2Mux potBGateActive
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases β (wPotBIsPot r41) == 1
    · simp
    · simp only [↓reduceIte, hSpEq, hPre1, hPre2, hv1M, hv2M]
      rfl
  · have hgB := muxStNoM2_gate_true h193 r41 0 z16 β
    have hsB := muxStNoM2_lt106 h193 true r41 0 z16 β (m := 1) (by omega)
    have hnB := muxStNoM2_lt106 h193 true r41 0 z16 β (m := 4) (by omega)
    have h0 : (stH (rH5 ⟨0, ow0_lt5⟩) == 1) = potBGateActive true r41 β := by
      dsimp only [stH, stDualH_dm2, rH5]
      rw [rMuxLeg1Hdr5_0_true]
      unfold hdrWrapMux
      simp only [↓reduceIte]
      rw [Function.update_of_ne (r41_ne r41 _ _ (by omega)),
          Function.update_of_ne (r41_ne r41 _ _ (by omega)), hgB]
      cases potBGateActive true r41 β <;> decide
    have h1 : (stH (rH5 ⟨1, ow1_lt5⟩) == 1) =
        (potBGateActive true r41 β && (β (wPotBIsScreen r41) == 1)) := by
      dsimp only [stH, stDualH_dm2, rH5]
      rw [rMuxLeg1Hdr5_1_true]
      unfold hdrWrapMux
      simp only [↓reduceIte]
      rw [Function.update_of_ne (r41_ne r41 _ _ (by omega)), Function.update_self, hgB, hsB]
      cases potBGateActive true r41 β <;>
        rcases DynCircExt.bit_cases (β (wPotBIsScreen r41)) with hs | hs <;>
        (rw [hs]; decide)
    have h2 : (stH (rH5 ⟨2, ow2_lt5⟩) == 1) =
        ((potBGateActive true r41 β && (β (wPotBIsScreen r41) == 1)) &&
          (β (wPotBIsNN r41) == 1)) := by
      dsimp only [stH, stDualH_dm2, rH5]
      rw [rMuxLeg1Hdr5_2_true]
      unfold hdrWrapMux
      simp only [↓reduceIte]
      rw [Function.update_self, hgB, hsB, hnB]
      cases potBGateActive true r41 β <;>
        rcases DynCircExt.bit_cases (β (wPotBIsScreen r41)) with hs | hs <;>
        rcases DynCircExt.bit_cases (β (wPotBIsNN r41)) with hn | hn <;>
        (rw [hs, hn]; decide)
    rw [h0, h1, h2]
    refine ⟨by cases potBGateActive true r41 β <;> cases (β (wPotBIsScreen r41) == 1) <;>
        cases (β (wPotBIsNN r41) == 1) <;> simp, ?_⟩
    unfold v1Mux v2Mux
    cases potBGateActive true r41 β
    · simp
    · simp only [↓reduceIte, Bool.true_and, hSpEq, hPre1, hPre2, hv1M, hv2M]
      rw [show ((β (wPotBIsScreen r41) == 1) && (β (wPotBIsNN r41) == 1)) =
          (β (wPotBIsNN r41) == 1) by
        rcases DynCircExt.bit_cases (β (wPotBIsScreen r41)) with hs | hs <;> simp [hs, hVF.2]]
      rfl
theorem writeSub24_hdrWrapMux_m1_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n)
    (α : BitAssignment n) (a b : ℕ) (f : Fin 24 → ZMod 2) : writeSub24 (hdrWrapMux h193 true r41 α)
    (rMuxM1 h193 true r41) a b
    f = hdrWrapMux h193 true r41 (writeSub24 α (rMuxM1 h193 true r41) a b f) := by
  have hm1_ne (i : Fin 24) (m : ℕ) (hm : m < 122 + Wp) (hc : m < 242 ∨ m = 122 + Wp - 1) :
      rMuxM1 h193 true r41 i ≠ r41 ⟨m, hm⟩ :=
    r41_blk_ne_wire r41 i _ (by
      have := i.isLt
      dsimp [Wtop]
      omega)
  have hOut (m : ℕ) (hm : m < 122 + Wp) (hc : m < 242 ∨ m = 122 + Wp - 1) :
      writeSub24 α (rMuxM1 h193 true r41) a b f (r41 ⟨m, hm⟩) = α (r41 ⟨m, hm⟩) :=
    writeSub24_apply_out α _ a b f fun i ↦ (hm1_ne i m hm hc).symm
  funext w
  by_cases hwM1 : ∃ i : Fin 24, rMuxM1 h193 true r41 i = w
  · obtain ⟨i, rfl⟩ := hwM1
    have hKeep (β0 : BitAssignment n) :
        hdrWrapMux h193 true r41 β0 (rMuxM1 h193 true r41 i) = β0 (rMuxM1 h193 true r41 i) := by
      unfold hdrWrapMux
      simp only [↓reduceIte, Function.update_of_ne (hm1_ne i 241 (by omega) (Or.inl (by omega))),
        Function.update_of_ne (hm1_ne i 240 (by omega) (Or.inl (by omega)))]
    rw [writeSub24_apply_reg, hKeep, hKeep, writeSub24_apply_reg]
  · rw [writeSub24_apply_out _ _ a b f fun i h ↦ hwM1 ⟨i, h.symm⟩]
    unfold hdrWrapMux wPotBIsScreen wPotBIsNN
    simp only [↓reduceIte, Function.update_apply, hOut 1 (by omega) (Or.inl (by omega)),
      hOut 4 (by omega) (Or.inl (by omega)), hOut (122 + Wp - 1) (by omega) (Or.inr rfl),
      writeSub24_apply_out α (rMuxM1 h193 true r41) a b f fun i h ↦ hwM1 ⟨i, h.symm⟩]


def rDualScr1_193 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (r41 : QRegister (122 + Wp) n) : QRegister kScr n :=
  r41.compose (QRegister.block 122 kScr (by omega))

def rDualScr2_193 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (r41 : QRegister (122 + Wp) n) : QRegister kScr n :=
  r41.compose (QRegister.block 182 kScr (by omega))

def rDualCar15_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) : QRegister 15 n :=
  r41.compose (QRegister.block 242 15 (by omega))

def idxDualMux52_wp193 (Wp : ℕ) (isCsel : Bool) (u : ℕ) : ℕ :=
    if hu5 : u < 5 then idxMuxLeg1Hdr5 Wp isCsel ⟨u, hu5⟩ else if u < 11 then 122 +
    (u - 5) else if u < 17 then 182 + (u - 11) else if u < 26 then 257 + (u - 17)
    else if u < 28 then 180 + (u - 26) else (122 + Wtop Wp isCsel - 24) + (u - 28)
theorem noGate_of_lt_wtop {Wp u : ℕ} (isCsel : Bool) (hu : u < Wtop Wp isCsel) :
    isCsel = false ∨ u ≠ Wp - 1 := by
  cases isCsel
  · exact Or.inl rfl
  · simp only [Wtop, ↓reduceIte] at hu
    exact Or.inr (by omega)

theorem step_of_writeReg_keep {Var : Type} [Fintype Var] [DecidableEq Var]
    {W k n : ℕ} [NeZero (2 ^ n)] {rWork : QRegister W n} {rS : QRegister k n}
    {st0 stMid stPost : BitAssignment n → BitAssignment n} {ph : BitAssignment n → ZMod 2}
    {p : DynamicCircuit Var n}
    (hKeep : ∀ δ w, (∀ u, w ≠ rS u) → stMid δ w = st0 δ w)
    (hs : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ writeReg (st0 δ) rS fun u ↦ stMid δ (rS u)) (fun _ ↦ 0))
      (mkKetOpW rWork stPost ph) p) :
    SubspaceStep (mkKetOpW rWork stMid (fun _ ↦ 0)) (mkKetOpW rWork stPost ph) p :=
  subspaceStep_of_eq_pre_local (mkKetOpW_congr rWork (fun δ _ ↦ funext fun w ↦ by
    by_cases hw : ∃ u : Fin k, rS u = w
    · obtain ⟨u, rfl⟩ := hw
      exact (writeReg_apply_reg (st0 δ) rS (fun u ↦ stMid δ (rS u)) u).symm
    · exact (hKeep δ w fun u h ↦ hw ⟨u, h.symm⟩).trans
        (writeReg_apply_of_not_mem (st0 δ) rS _ w hw).symm) (fun _ _ ↦ rfl)) hs

theorem idxDualMux52_wp193_lt {Wp : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (u : Fin 52) :
    idxDualMux52_wp193 Wp isCsel u.val < 122 + Wp := by
  have := And.intro u.isLt (And.intro (wtop_ge192 h193 isCsel) (wtop_le_wp Wp isCsel))
  unfold idxDualMux52_wp193
  by_cases hu5 : u.val < 5
  · rw [_root_.dite_eq_left hu5]
    exact idxMuxLeg1Hdr5_lt h193 isCsel ⟨u.val, hu5⟩
  · rw [_root_.dite_eq_right hu5]
    split_ifs <;> omega

theorem fDualMux52_wp193_inj {Wp : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) :
    Function.Injective (fun u : Fin 52 ↦
      (⟨idxDualMux52_wp193 Wp isCsel u.val, idxDualMux52_wp193_lt h193 isCsel u⟩ :
        Fin (122 + Wp))) := by
  have hw := And.intro (wtop_ge192 h193 isCsel) (wtop_le_wp Wp isCsel)
  have hCross (x y : Fin 52) (hx : x.val < 5) (hy : ¬ y.val < 5)
      (hv : idxDualMux52_wp193 Wp isCsel x.val = idxDualMux52_wp193 Wp isCsel y.val) : False := by
    have := y.isLt
    unfold idxDualMux52_wp193 at hv
    rw [_root_.dite_eq_left hx, _root_.dite_eq_right hy] at hv
    rcases idxMuxLeg1Hdr5_cases Wp isCsel x.val hx with
        ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;>
      (rw [e] at hv; cases isCsel <;>
        simp only [Wtop, Bool.false_eq_true, ↓reduceIte] at hv hw <;> split_ifs at hv <;> omega)
  intro a b heq
  have hv : idxDualMux52_wp193 Wp isCsel a.val = idxDualMux52_wp193 Wp isCsel b.val :=
    congrArg Fin.val heq
  by_cases ha5 : a.val < 5 <;> by_cases hb5 : b.val < 5
  · unfold idxDualMux52_wp193 at hv
    rw [_root_.dite_eq_left ha5, _root_.dite_eq_left hb5] at hv
    rcases idxMuxLeg1Hdr5_cases Wp isCsel a.val ha5 with
        ⟨_, ea⟩ | ⟨_, ea⟩ | ⟨_, ea⟩ | ⟨_, ea⟩ | ⟨_, ea⟩ <;>
      rcases idxMuxLeg1Hdr5_cases Wp isCsel b.val hb5 with
        ⟨_, eb⟩ | ⟨_, eb⟩ | ⟨_, eb⟩ | ⟨_, eb⟩ | ⟨_, eb⟩ <;>
      (rw [ea, eb] at hv; cases isCsel <;>
        simp only [Wtop, Bool.false_eq_true, ↓reduceIte] at hv hw <;> exact Fin.ext (by omega))
  · exact (hCross a b ha5 hb5 hv).elim
  · exact (hCross b a hb5 ha5 hv.symm).elim
  · have := And.intro a.isLt b.isLt
    unfold idxDualMux52_wp193 at hv
    rw [_root_.dite_eq_right ha5, _root_.dite_eq_right hb5] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)

def rDualMux52_wp193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    QRegister 52 n := r41.compose
    ⟨⟨fun u ↦ ⟨idxDualMux52_wp193 Wp isCsel u.val, idxDualMux52_wp193_lt h193 isCsel u⟩,
        fDualMux52_wp193_inj h193 isCsel⟩⟩
theorem owBlk_disj {N a la b lb n : ℕ} {ha : a + la ≤ N} {hb : b + lb ≤ N}
    (r : QRegister N n) (hd : a + la ≤ b ∨ b + lb ≤ a) :
    (r.compose (QRegister.block a la ha)).DisjointWires (r.compose (QRegister.block b lb hb)) :=
  owCompose_disj r fun i j ↦ by
    have := And.intro i.isLt j.isLt
    simp only [QRegister.block_apply_val]
    omega

theorem blk_disj_m52 {Wp a la n : ℕ} {ha : a + la ≤ 122 + Wp} (h193 : 193 ≤ Wp)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (h1 : a = 106 ∧ la = 16 ∨ a = 242 ∧ la = 15) :
    (r41.compose (QRegister.block a la ha)).DisjointWires (rDualMux52_wp193 h193 isCsel r41) := by
  have hw := wtop_ge192 h193 isCsel
  refine disj_of_ne fun j u h ↦ ?_
  have hv := congrArg Fin.val (r41.wires.injective h)
  simp only [QRegister.block_apply_val] at hv
  change a + j.val = idxDualMux52_wp193 Wp isCsel u.val at hv
  have := And.intro j.isLt u.isLt
  unfold idxDualMux52_wp193 at hv
  by_cases hu5 : u.val < 5
  · rw [_root_.dite_eq_left hu5] at hv
    rcases idxMuxLeg1Hdr5_cases Wp isCsel u.val hu5 with
        ⟨_, eu⟩ | ⟨_, eu⟩ | ⟨_, eu⟩ | ⟨_, eu⟩ | ⟨_, eu⟩ <;>
      (rw [eu] at hv; cases isCsel <;>
        simp only [Wtop, Bool.false_eq_true, ↓reduceIte] at hv hw <;> omega)
  · rw [_root_.dite_eq_right hu5] at hv
    split_ifs at hv <;> omega

theorem dualDisj_m1_copy_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) :
    (rMuxM1 h193 isCsel r41).DisjointWires (rMuxCopy24 h193 r41) :=
  owBlk_disj r41 (by
    have := wtop_ge192 h193 isCsel
    omega)

theorem dualDisj_m1_scr2_193 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) :
    (rMuxM1 h193 isCsel r41).DisjointWires (rDualScr2_193 h193 hScr r41) :=
  owBlk_disj r41 (by
    have := wtop_ge192 h193 isCsel
    omega)

theorem dualDisj_copy_scr2_193 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (r41 : QRegister (122 + Wp) n) :
    (rMuxCopy24 h193 r41).DisjointWires (rDualScr2_193 h193 hScr r41) := owBlk_disj r41 (by omega)

theorem dualDisj_scr1_scr2_193 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (r41 : QRegister (122 + Wp) n) :
    (rDualScr1_193 h193 hScr r41).DisjointWires (rDualScr2_193 h193 hScr r41) :=
        owBlk_disj r41 (by omega)

theorem dualDisj_copy_scr1_193 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (r41 : QRegister (122 + Wp) n) :
    (rMuxCopy24 h193 r41).DisjointWires (rDualScr1_193 h193 hScr r41) := owBlk_disj r41 (by omega)

theorem dualDisj_elec_scr1_193 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (r41 : QRegister (122 + Wp) n) :
    (rPotBElecA r41).DisjointWires (rDualScr1_193 h193 hScr r41) := owBlk_disj r41 (by omega)

theorem dualDisj_z16_car15_193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    (rMuxZ16 r41).DisjointWires (rDualCar15_193 h193 r41) := owBlk_disj r41 (by omega)

theorem dualDisj_z16_m52_wp193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) :
    (rMuxZ16 r41).DisjointWires (rDualMux52_wp193 h193 isCsel r41) :=
        blk_disj_m52 h193 isCsel r41 (Or.inl ⟨rfl, rfl⟩)

theorem dualDisj_car15_m52_wp193 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) :
    (rDualCar15_193 h193 r41).DisjointWires (rDualMux52_wp193 h193 isCsel r41) :=
        blk_disj_m52 h193 isCsel r41 (Or.inr ⟨rfl, rfl⟩)

def stDualS1_dsc50 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2) (z16 : Fin 16 → ZMod 2)
    (β : BitAssignment n) : BitAssignment n := writeReg
    (stDualH_dm2 h193 isCsel r41 z16 β) (rDualScr1_193 h193 hScr r41) fS1
def stDualC2_dsc50 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2) (z16 : Fin 16 → ZMod 2)
    (β : BitAssignment n) : BitAssignment n :=
  let s1 := stDualS1_dsc50 h193 hScr isCsel r41 fS1 z16 β
  writeReg s1 (rMuxCopy24 h193 r41) (fun i ↦ s1 (rPotBPortB r41 i))

def stDualF2_dsc50 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2) (z16 : Fin 16 → ZMod 2)
    (β : BitAssignment n) : BitAssignment n :=
  let c2 := stDualC2_dsc50 h193 hScr isCsel r41 fS1 z16 β
  writeReg c2 (rMuxM1 h193 isCsel r41)
    (fun i ↦ c2 (rMuxM1 h193 isCsel r41 i) + (c2 (rPotBNucA r41 i) + c2 (rPotBElecA r41 i)))

def stDualU2_dsc50 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2) (z16 : Fin 16 → ZMod 2)
    (β : BitAssignment n) : BitAssignment n :=
    writeReg (writeReg (stDualF2_dsc50 h193 hScr isCsel r41 fS1 z16 β)
        (rDualScr2_193 h193 hScr r41) fS2) (rMuxCopy24 h193 r41) (fun _ ↦ 0)
theorem stDualS1_dsc50_lt106 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) {m : ℕ} (hm : m < 106) :
    stDualS1_dsc50 h193 hScr isCsel r41 fS1 z16 β (r41 ⟨m, by omega⟩) =
      β (r41 ⟨m, by omega⟩) :=
  (writeReg_apply_of_not_mem _ _ _ _ fun ⟨u, hu⟩ ↦ r41_blk_ne_wire r41 u _ (by omega) hu).trans
    (stDualH_dm2_lt106 h193 isCsel r41 z16 β hm)

theorem stDualC2_dsc50_lt106 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) {m : ℕ} (hm : m < 106) :
    stDualC2_dsc50 h193 hScr isCsel r41 fS1 z16 β (r41 ⟨m, by omega⟩) =
      β (r41 ⟨m, by omega⟩) :=
  (writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ r41_blk_ne_wire r41 i _ (by omega) hi).trans
    (stDualS1_dsc50_lt106 h193 hScr isCsel r41 fS1 z16 β hm)

theorem stDualF2_dsc50_lt106 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) {m : ℕ} (hm : m < 106) :
    stDualF2_dsc50 h193 hScr isCsel r41 fS1 z16 β (r41 ⟨m, by omega⟩) =
      β (r41 ⟨m, by omega⟩) := by
  have := wtop_ge192 h193 isCsel
  exact (writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦
    r41_blk_ne_wire r41 i _ (by omega) hi).trans
    (stDualC2_dsc50_lt106 h193 hScr isCsel r41 fS1 z16 β hm)

theorem stDualF2_dsc50_m1_bit {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (i : Fin 24) :
    stDualF2_dsc50 h193 hScr isCsel r41 fS1 z16 β (rMuxM1 h193 isCsel r41 i) =
      if β (wPotBIsNN r41) == 1 then β (rPotBElecA r41 i) else β (rPotBNucA r41 i) := by
  have := And.intro (wtop_ge192 h193 isCsel) (And.intro (wtop_le_wp Wp isCsel) i.isLt)
  unfold stDualF2_dsc50
  rw [writeReg_apply_reg]
  have hm1 : rMuxM1 h193 isCsel r41 i =
      r41 ⟨122 + Wtop Wp isCsel - 48 + i.val, by omega⟩ := congrArg r41.wires (Fin.ext rfl)
  have hM1C2 : stDualC2_dsc50 h193 hScr isCsel r41 fS1 z16 β (rMuxM1 h193 isCsel r41 i) =
      if β (wPotBIsNN r41) == 1 then β (rPotBNucA r41 i) else β (rPotBElecA r41 i) := by
    unfold stDualC2_dsc50 stDualS1_dsc50 stDualH_dm2
    rw [writeReg_apply_of_not_mem _ _ _ _
          (fun ⟨k, hk⟩ ↦ disj_ne (dualDisj_m1_copy_193 h193 isCsel r41) i k hk.symm),
        writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦ r41_blk_ne_blk r41 u i (by
          have := u.isLt
          omega) hu),
        hm1, hdrWrapMux_keep h193 isCsel r41 _ _ _ (by omega) (by omega), ← hm1, muxStNoM2_m1]
    simp only [Nat.zero_le, ↓reduceIte]
  rw [hM1C2,
      show rPotBNucA r41 i = r41 ⟨9 + i.val, by omega⟩ from congrArg r41.wires (Fin.ext rfl),
      show rPotBElecA r41 i = r41 ⟨33 + i.val, by omega⟩ from congrArg r41.wires (Fin.ext rfl),
      stDualC2_dsc50_lt106 h193 hScr isCsel r41 fS1 z16 β (by omega),
      stDualC2_dsc50_lt106 h193 hScr isCsel r41 fS1 z16 β (by omega)]
  exact mux1Leg2_bit_eq_ite _ _ _

theorem stDualF2_dsc50_copy {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (i : Fin 24) :
    stDualF2_dsc50 h193 hScr isCsel r41 fS1 z16 β (rMuxCopy24 h193 r41 i) =
      β (rPotBPortB r41 i) := by
  have := i.isLt
  unfold stDualF2_dsc50 stDualC2_dsc50
  dsimp only
  rw [writeReg_apply_of_not_mem _ _ _ _
        (fun ⟨k, hk⟩ ↦ disj_ne (dualDisj_m1_copy_193 h193 isCsel r41) k i hk), writeReg_apply_reg,
      show rPotBPortB r41 i = r41 ⟨57 + i.val, by omega⟩ from congrArg r41.wires (Fin.ext rfl),
      stDualS1_dsc50_lt106 h193 hScr isCsel r41 fS1 z16 β (by omega)]

theorem stDualF2_dsc50_scr2_zero {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (u : Fin kScr) :
    stDualF2_dsc50 h193 hScr isCsel r41 fS1 z16 β (rDualScr2_193 h193 hScr r41 u) = 0 := by
  have := And.intro (wtop_ge192 h193 isCsel) u.isLt
  unfold stDualF2_dsc50 stDualC2_dsc50 stDualS1_dsc50
  dsimp only
  rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦
        disj_ne (dualDisj_m1_scr2_193 h193 hScr isCsel r41) k u hk),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦
        disj_ne (dualDisj_copy_scr2_193 h193 hScr r41) k u hk),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨v, hv⟩ ↦
        disj_ne (dualDisj_scr1_scr2_193 h193 hScr r41) v u hv),
      show rDualScr2_193 h193 hScr r41 u = r41 ⟨122 + (60 + u.val), by omega⟩ from
        congrArg r41.wires (Fin.ext (by omega : 182 + u.val = 122 + (60 + u.val)))]
  exact stDualH_dm2_work_zero_193 h193 isCsel r41 z16 β (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inl (by omega))

theorem stDualU2_dsc50_out {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (k : Fin (122 + Wp))
    (hOut : (k.val < 122 ∨ 122 + kScr ≤ k.val) ∧ (k.val < 182 ∨ 182 + kScr ≤ k.val) ∧
      (k.val < 242 ∨ 266 ≤ k.val) ∧
      (k.val < 122 + Wtop Wp isCsel - 48 ∨ 122 + Wtop Wp isCsel - 24 ≤ k.val)) :
    stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 z16 β (r41 k) =
      stDualH_dm2 h193 isCsel r41 z16 β (r41 k) := by
  unfold stDualU2_dsc50 stDualF2_dsc50 stDualC2_dsc50 stDualS1_dsc50
    rMuxCopy24 rDualScr2_193 rMuxM1 rDualScr1_193
  dsimp only
  have hB {a l : ℕ} {hl : a + l ≤ 122 + Wp} (ha : k.val < a ∨ a + l ≤ k.val) :
      ¬ ∃ i : Fin l, r41.compose (QRegister.block a l hl) i = r41 k := fun ⟨i, hi⟩ ↦ by
    have hv := congrArg Fin.val (r41.wires.injective hi)
    simp only [QRegister.block_apply_val] at hv
    have := i.isLt
    omega
  rw [writeReg_apply_of_not_mem _ _ _ _ (hB hOut.2.2.1),
      writeReg_apply_of_not_mem _ _ _ _ (hB hOut.2.1),
      writeReg_apply_of_not_mem _ _ _ _ (hB (by have := hOut.2.2.2
                                                omega)),
      writeReg_apply_of_not_mem _ _ _ _ (hB hOut.2.2.1),
      writeReg_apply_of_not_mem _ _ _ _ (hB hOut.1)]

theorem writeReg_congr_out {m n : ℕ} {sA sB : BitAssignment n} {r : QRegister m n}
    {fA fB : Fin m → ZMod 2} {w : Wire n} (hf : fA = fB) (hw : sA w = sB w) :
    writeReg sA r fA w = writeReg sB r fB w := by
  subst hf
  by_cases hm : ∃ i : Fin m, r i = w
  · obtain ⟨i, rfl⟩ := hm
    rw [writeReg_apply_reg, writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ w hm, writeReg_apply_of_not_mem _ _ _ w hm]
    exact hw

theorem stDualU2_dsc50_z16 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2) (z16 : Fin 16 → ZMod 2)
    (β : BitAssignment n) (j : Fin 16) :
    stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 z16 β (rMuxZ16 r41 j) = z16 j := by
  have hw := wtop_ge192 h193 isCsel
  refine (stDualU2_dsc50_out h193 hScr isCsel r41 fS1 fS2 z16 β _ ?_).trans (stDualH_dm2_z16 h193
      isCsel r41 z16 β j)
  simp only [QRegister.block_apply_val]
  have := j.isLt
  omega

theorem stDualU2_dsc50_eq_of_ne_z16 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2)
    (zA zB : Fin 16 → ZMod 2) (β : BitAssignment n)
    {w : Wire n} (hwZ : ∀ j : Fin 16, w ≠ rMuxZ16 r41 j) :
        stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 zA β w =
        stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 zB β w := by
  have := wtop_ge192 h193 isCsel
  have hS1Eq (x : Wire n) (hx : ∀ j, x ≠ rMuxZ16 r41 j) :
      stDualS1_dsc50 h193 hScr isCsel r41 fS1 zA β x =
          stDualS1_dsc50 h193 hScr isCsel r41 fS1 zB β x :=
    writeReg_congr_out rfl (stDualH_dm2_eq_of_ne_z16 h193 isCsel r41 zA zB β hx)
  have hC2Eq (x : Wire n) (hx : ∀ j, x ≠ rMuxZ16 r41 j) :
      stDualC2_dsc50 h193 hScr isCsel r41 fS1 zA β x =
          stDualC2_dsc50 h193 hScr isCsel r41 fS1 zB β x :=
    writeReg_congr_out (funext fun i ↦ hS1Eq _ fun j ↦ r41_blk_ne_blk r41 i j (by omega))
        (hS1Eq x hx)
  exact writeReg_congr_out rfl (writeReg_congr_out rfl (writeReg_congr_out (funext fun i ↦ by
    rw [hC2Eq _ fun j ↦ r41_blk_ne_blk r41 i j (by omega),
        hC2Eq _ fun j ↦ r41_blk_ne_blk r41 i j (by omega),
        hC2Eq _ fun j ↦ r41_blk_ne_blk r41 i j (by omega)]) (hC2Eq w hwZ)))

theorem stDualU2_dsc50_hdr52 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (u : Fin 5) :
    stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 z16 β (rDualMux52_wp193 h193 isCsel r41 ⟨u.val,
        by omega⟩) =
      stDualH_dm2 h193 isCsel r41 z16 β (rMuxLeg1Hdr5 h193 isCsel r41 u) := by
  have hw := wtop_ge192 h193 isCsel
  rw [show rDualMux52_wp193 h193 isCsel r41 ⟨u.val, by omega⟩ = rMuxLeg1Hdr5 h193 isCsel r41 u from
    congrArg r41.wires (Fin.ext (by simp [idxDualMux52_wp193, u.isLt]))]
  refine stDualU2_dsc50_out h193 hScr isCsel r41 fS1 fS2 z16 β _ ?_
  change (idxMuxLeg1Hdr5 Wp isCsel u < 122 ∨ _) ∧ _
  fin_cases u <;> cases isCsel <;> simp [idxMuxLeg1Hdr5, Wtop] <;> omega

theorem stDualU2_dsc50_p1_52 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (h6 : 6 ≤ kScr)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (j : Fin 6) :
    stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 z16 β
      (rDualMux52_wp193 h193 isCsel r41 ⟨5 + j.val, by omega⟩) = fS1 ⟨j.val, by omega⟩ := by
  have := And.intro (wtop_ge192 h193 isCsel) j.isLt
  rw [show rDualMux52_wp193 h193 isCsel r41 ⟨5 + j.val, by omega⟩ =
      rDualScr1_193 h193 hScr r41 ⟨j.val, by omega⟩ from congrArg r41.wires (Fin.ext (by
        change idxDualMux52_wp193 Wp isCsel (5 + j.val) = 122 + j.val
        unfold idxDualMux52_wp193
        split_ifs <;> omega))]
  unfold stDualU2_dsc50 stDualF2_dsc50 stDualC2_dsc50 stDualS1_dsc50
  dsimp only
  rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦
        disj_ne (dualDisj_copy_scr1_193 h193 hScr r41) i _ hi),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦
        disj_ne (dualDisj_scr1_scr2_193 h193 hScr r41) _ u hu.symm),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ r41_blk_ne_blk r41 i ⟨j.val, by omega⟩ (by
        have := i.isLt
        omega) hi),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦
        disj_ne (dualDisj_copy_scr1_193 h193 hScr r41) i _ hi), writeReg_apply_reg]

theorem stDualU2_dsc50_p2_52 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (h6 : 6 ≤ kScr)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (j : Fin 6) :
    stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 z16 β
      (rDualMux52_wp193 h193 isCsel r41 ⟨11 + j.val, by omega⟩) = fS2 ⟨j.val, by omega⟩ := by
  have := j.isLt
  rw [show rDualMux52_wp193 h193 isCsel r41 ⟨11 + j.val, by omega⟩ =
      rDualScr2_193 h193 hScr r41 ⟨j.val, by omega⟩ from congrArg r41.wires (Fin.ext (by
        change idxDualMux52_wp193 Wp isCsel (11 + j.val) = 182 + j.val
        unfold idxDualMux52_wp193
        split_ifs <;> omega))]
  unfold stDualU2_dsc50
  rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦
        disj_ne (dualDisj_copy_scr2_193 h193 hScr r41) i _ hi), writeReg_apply_reg]

theorem stDualU2_dsc50_clnCar15 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (u : Fin 15) :
    stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 z16 β (rDualCar15_193 h193 r41 u) = 0 := by
  have := u.isLt
  rw [show rDualCar15_193 h193 r41 u = rMuxCopy24 h193 r41 ⟨u.val, by omega⟩ from
    congrArg r41.wires (Fin.ext rfl)]
  unfold stDualU2_dsc50
  rw [writeReg_apply_reg]

theorem stDualU2_dsc50_clnM52 {Wp kScr n : ℕ} (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58)
    (isCsel : Bool) (r41 : QRegister (122 + Wp) n) (fS1 fS2 : Fin kScr → ZMod 2)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (u : Fin 52) (hu : 17 ≤ u.val) :
    stDualU2_dsc50 h193 hScr isCsel r41 fS1 fS2 z16 β
      (rDualMux52_wp193 h193 isCsel r41 u) = 0 := by
  have := And.intro (wtop_ge192 h193 isCsel) (And.intro (wtop_le_wp Wp isCsel) u.isLt)
  by_cases hu26 : u.val < 26
  · rw [show rDualMux52_wp193 h193 isCsel r41 u = rMuxCopy24 h193 r41 ⟨u.val - 2, by omega⟩ from
      congrArg r41.wires (Fin.ext (by
        change idxDualMux52_wp193 Wp isCsel u.val = 242 + (u.val - 2)
        unfold idxDualMux52_wp193
        split_ifs <;> omega))]
    exact writeReg_apply_reg _ _ _ _
  · let m := idxDualMux52_wp193 Wp isCsel u.val
    have hm : 180 ≤ m ∧ m < 122 + Wtop Wp isCsel ∧ (m < 182 ∨ 122 + Wtop Wp isCsel - 24 ≤ m) := by
      dsimp only [m, idxDualMux52_wp193]
      split_ifs <;> omega
    exact (stDualU2_dsc50_out h193 hScr isCsel r41 fS1 fS2 z16 β ⟨m,
        idxDualMux52_wp193_lt h193 isCsel u⟩ (by
        dsimp only
        omega)).trans
      ((congrArg (stDualH_dm2 h193 isCsel r41 z16 β)
        (congrArg r41.wires (Fin.ext (by omega : m = 122 + (m - 122))) :
          rDualMux52_wp193 h193 isCsel r41 u = r41 ⟨122 + (m - 122), by omega⟩)).trans
        (stDualH_dm2_work_zero_193 h193 isCsel r41 z16 β (by omega) (by omega) (by omega)
          (noGate_of_lt_wtop isCsel (by omega)) (by omega)))


def pMuxDualAfterSB2_dsc50 {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (v : Var)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
  have hdPB : (rPotBPortB r41).DisjointWires (rMuxCopy24 h193 r41) :=
    owCompose_disj r41 fun _ _ ↦ by
      simp only [QRegister.block_apply_val]
      omega
  wrapCopy24 h193 v (rPotBPortB r41) r41 hdPB
    (DualSumCompact50K2.pDualSumCore_dsc50 v (rMuxZ16 r41) (rDualCar15_193 h193 r41)
        (rDualMux52_wp193 h193 isCsel r41)
      (dualDisj_z16_m52_wp193 h193 isCsel r41)
      (dualDisj_z16_car15_193 h193 r41)
      (dualDisj_car15_m52_wp193 h193 isCsel r41))

def pMuxDualAfterSB1_dsc50 {Var : Type} {Wp kScr tSB n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58) (v : Var)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
  have hdNA : (rPotBNucA r41).DisjointWires (rMuxCopy24 h193 r41) :=
    owCompose_disj r41 fun _ _ ↦ by
      simp only [QRegister.block_apply_val]
      omega
  have hdPB : (rPotBPortB r41).DisjointWires (rMuxCopy24 h193 r41) :=
    owCompose_disj r41 fun _ _ ↦ by
      simp only [QRegister.block_apply_val]
      omega
  wrapCopy24 h193 v (rPotBNucA r41) r41 hdNA
    (wrapCopy24 h193 v (rPotBPortB r41) r41 hdPB
      (wrapFlipLeg2 h193 isCsel v r41
        (pkgSB.wrapDom v (rMuxM1 h193 isCsel r41) (rMuxCopy24 h193 r41)
            (rDualScr2_193 h193 hScr r41)
          (pMuxDualAfterSB2_dsc50 h193 isCsel v r41))))

def pMuxDualLegsInner_dsc50 {Var : Type} {Wp kScr tSB n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58) (v : Var)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
  have hdNA : (rPotBNucA r41).DisjointWires (rMuxCopy24 h193 r41) :=
    owCompose_disj r41 fun _ _ ↦ by
      simp only [QRegister.block_apply_val]
      omega
  wrapCopy24 h193 v (rPotBNucA r41) r41 hdNA
    (pkgSB.wrapDom v (rMuxCopy24 h193 r41) (rPotBElecA r41) (rDualScr1_193 h193 hScr r41)
      (pMuxDualAfterSB1_dsc50 h193 isCsel pkgSB hScr v r41))

def pMuxDualLegsBlock_dsc50 {Var : Type} {Wp kScr tSB n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58) (v : Var)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
    wrapHdrCascade2 h193 isCsel v r41 (pMuxDualLegsInner_dsc50 h193 isCsel pkgSB hScr v r41)
theorem ctrlSafe_pMuxDualLegsInner_dsc50 {Var : Type} {Wp kScr tSB n : ℕ}
    {S_ctrl S_tgt : Wire n → Prop} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58) (hSBSafe : ShortBin7CtrlSafe pkgSB)
    (v : Var) (r41 : QRegister (122 + Wp) n) (hSr41 : ∀ k, S_ctrl (r41 k))
    (hTr41 : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val → S_tgt (r41 k)) :
    DynCtrlSafe S_ctrl S_tgt (pMuxDualLegsInner_dsc50 h193 isCsel pkgSB hScr v r41) := by
  have hw := wtop_ge192 h193 isCsel
  have hwle := wtop_le_wp Wp isCsel
  have hST41 (k : Fin (122 + Wp)) (hk : IsNonNucPortB41Idx k.val) : S_ctrl (r41 k) ∧ S_tgt (r41 k)
      :=
    ⟨hSr41 k, hTr41 k hk⟩
  have hCopy (i) : S_ctrl (rMuxCopy24 h193 r41 i) ∧ S_tgt (rMuxCopy24 h193 r41 i) :=
    r41_blk_st r41 hST41 i (by omega)
  have hM1 (i) : S_ctrl (rMuxM1 h193 isCsel r41 i) ∧ S_tgt (rMuxM1 h193 isCsel r41 i) :=
    r41_blk_st r41 hST41 i (by omega)
  have hdNA : (rPotBNucA r41).DisjointWires (rMuxCopy24 h193 r41) := owBlk_disj r41 (by omega)
  have hdPB : (rPotBPortB r41).DisjointWires (rMuxCopy24 h193 r41) := owBlk_disj r41 (by omega)
  unfold pMuxDualLegsInner_dsc50 pMuxDualAfterSB1_dsc50 pMuxDualAfterSB2_dsc50
  dsimp only
  exact ctrlSafe_wrapCopy24 h193 v _ r41 hdNA _ (fun _ ↦ hSr41 _) hCopy
    (hSBSafe v (rMuxCopy24 h193 r41) (rPotBElecA r41) (rDualScr1_193 h193 hScr r41) _ hCopy
      (fun i ↦ r41_blk_st r41 hST41 i (by omega)) (fun u ↦ r41_blk_st r41 hST41 u (by omega))
      (ctrlSafe_wrapCopy24 h193 v _ r41 hdNA _ (fun _ ↦ hSr41 _) hCopy
        (ctrlSafe_wrapCopy24 h193 v _ r41 hdPB _ (fun _ ↦ hSr41 _) hCopy
          (ctrlSafe_wrapFlipLeg2 h193 isCsel v r41 _ hSr41 (fun i ↦ (hM1 i).2)
            (hSBSafe v (rMuxM1 h193 isCsel r41) (rMuxCopy24 h193 r41)
                (rDualScr2_193 h193 hScr r41) _
              hM1 hCopy (fun u ↦ r41_blk_st r41 hST41 u (by omega))
              (ctrlSafe_wrapCopy24 h193 v _ r41 hdPB _ (fun _ ↦ hSr41 _) hCopy
                (DualSumCompact50K2.ctrlSafe_pDualSumCore_dsc50 v (rMuxZ16 r41)
                  (rDualCar15_193 h193 r41) (rDualMux52_wp193 h193 isCsel r41) _ _ _
                  (fun j ↦ r41_blk_st r41 hST41 j (by omega))
                      (fun u ↦ r41_blk_st r41 hST41 u (by omega))
                  fun u ↦
                      hST41 ⟨idxDualMux52_wp193 Wp isCsel u.val,
                      idxDualMux52_wp193_lt h193 isCsel u⟩ (by
                    dsimp only
                    have := u.isLt
                    unfold idxDualMux52_wp193 IsNonNucPortB41Idx
                    by_cases hu5 : u.val < 5
                    · rw [_root_.dite_eq_left hu5]
                      rcases idxMuxLeg1Hdr5_cases Wp isCsel u.val hu5 with
                          ⟨_, eu⟩ | ⟨_, eu⟩ | ⟨_, eu⟩ | ⟨_, eu⟩ | ⟨_, eu⟩ <;>
                        (rw [eu]; cases isCsel <;>
                          simp only [Wtop, Bool.false_eq_true, ↓reduceIte] at hw hwle ⊢ <;> omega)
                    · rw [_root_.dite_eq_right hu5]
                      split_ifs <;> omega))))))))

theorem ctrlSafe_pMuxDualLegsBlock_dsc50 {Var : Type} {Wp kScr tSB n : ℕ} {S_ctrl S_tgt : Wire n →
  Prop} (h193 : 193 ≤ Wp) (isCsel : Bool) (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (hSBSafe : ShortBin7CtrlSafe pkgSB) (v : Var) (r41 : QRegister (122 + Wp) n)
        (hSr41 : ∀ k, S_ctrl (r41 k)) (hTr41 : ∀ k : Fin (122 + Wp), IsNonNucPortB41Idx k.val →
        S_tgt (r41 k)) : DynCtrlSafe S_ctrl S_tgt
    (pMuxDualLegsBlock_dsc50 h193 isCsel pkgSB hScr v r41) :=
        ctrlSafe_wrapHdrCascade2 h193 isCsel v r41 _ hSr41 hTr41 (ctrlSafe_pMuxDualLegsInner_dsc50
        h193 isCsel pkgSB hScr hSBSafe v r41 hSr41 hTr41)
theorem step_pMuxDualAfterSB2_dsc50 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp kScr kMid tMid n : ℕ} [NeZero (2 ^ n)]
    (h193 : 193 ≤ Wp) (hScr : kScr ≤ 58) (h6 : 6 ≤ kScr) (isCsel : Bool)
    (pkgMid : MidOWU10Pkg true 14 kMid tMid)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st : BitAssignment n → BitAssignment n)
    (z16Init : BitAssignment n → Fin 16 → ZMod 2)
    (fS1 fS2 : BitAssignment n → Fin kScr → ZMod 2)
    (hFlags : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags r41 (st δ))
    (hP1 : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ j : Fin 6,
      fS1 δ ⟨j.val, by omega⟩ =
        if (pre6OfCoords (coordOfReg24 (rPotBNucA r41) (st δ))
              (coordOfReg24 (rPotBElecA r41) (st δ))).val.testBit j.val then 1 else 0)
    (hP2 : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ j : Fin 6,
      fS2 δ ⟨j.val, by omega⟩ =
        if (pre6OfCoords
              (if st δ (wPotBIsNN r41) == 1 then coordOfReg24 (rPotBElecA r41) (st δ)
               else coordOfReg24 (rPotBNucA r41) (st δ))
              (coordOfReg24 (rPotBPortB r41) (st δ))).val.testBit j.val then 1 else 0) :
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60 pkgMid
    let z16L1 := fun δ ↦ z16AddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ))
    let z16L2 := fun δ ↦ z16AddVal (z16L1 δ) (v2Mux isCsel pkgLM r41 (st δ))
    let phL2 := fun δ ↦
        phAddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ)) + phAddVal (z16L1 δ)
        (v2Mux isCsel pkgLM r41 (st δ))
    let st6 := fun (zX : BitAssignment n → Fin 16 → ZMod 2) (δ : BitAssignment n) ↦
        writeReg (stDualF2_dsc50 h193 hScr isCsel r41 (fS1 δ) (zX δ) (st δ))
        (rDualScr2_193 h193 hScr r41) (fS2 δ)
    let p := pMuxDualAfterSB2_dsc50 h193 isCsel v r41
    SubspaceStep (mkKetOpW rWork (st6 z16Init) (fun _ ↦ 0))
      (mkKetOpW rWork (st6 z16L2) phL2) p ∧
    p.count .T = 180 ∧
    p.count .TOFF = 0 := by
  intro pkgLM z16L1 z16L2 phL2 st6 p
  have := wtop_ge192 h193 isCsel
  dsimp only [p, pMuxDualAfterSB2_dsc50]
  let p1Fn : BitAssignment n → Fin 64 := fun δ ↦
    pre6OfCoords (coordOfReg24 (rPotBNucA r41) (st δ)) (coordOfReg24 (rPotBElecA r41) (st δ))
  let p2Fn : BitAssignment n → Fin 64 := fun δ ↦
    pre6OfCoords (if st δ (wPotBIsNN r41) == 1 then coordOfReg24 (rPotBElecA r41) (st δ)
      else coordOfReg24 (rPotBNucA r41) (st δ)) (coordOfReg24 (rPotBPortB r41) (st δ))
  obtain ⟨sCore, tCore, fCore⟩ := DualSumCompact50K2.step_and_counts_pDualSumCore_dsc50 v rWork
    (rMuxZ16 r41) (rDualCar15_193 h193 r41) (rDualMux52_wp193 h193 isCsel r41)
    (dualDisj_z16_m52_wp193 h193 isCsel r41) (dualDisj_z16_car15_193 h193 r41)
    (dualDisj_car15_m52_wp193 h193 isCsel r41)
    (fun δ ↦ stDualU2_dsc50 h193 hScr isCsel r41 (fS1 δ) (fS2 δ) (z16Init δ) (st δ))
    (fun δ ↦ stDualU2_dsc50 h193 hScr isCsel r41 (fS1 δ) (fS2 δ) (z16L2 δ) (st δ))
    phL2 p1Fn p2Fn (fun _ _ ↦ pre6OfCoords_valid _ _) (fun _ _ ↦ pre6OfCoords_valid _ _)
    (fun δ hz j ↦ by
      rw [stDualU2_dsc50_p1_52 h193 hScr h6 isCsel r41 _ _ _ _ j, hP1 δ hz j]
      cases (p1Fn δ).val.testBit j.val <;> rfl)
    (fun δ hz j ↦ by
      rw [stDualU2_dsc50_p2_52 h193 hScr h6 isCsel r41 _ _ _ _ j, hP2 δ hz j]
      cases (p2Fn δ).val.testBit j.val <;> rfl)
    (fun δ hz ↦ by
      have h5 := stDualU2_dsc50_hdr52 h193 hScr isCsel r41 (fS1 δ) (fS2 δ) (z16Init δ) (st δ)
      rw [h5 ⟨0, ow0_lt5⟩, h5 ⟨1, ow1_lt5⟩, h5 ⟨2, ow2_lt5⟩]
      exact (dualHdr_target_eq_dm2_193 h193 isCsel pkgMid r41 (z16Init δ) (st δ)
          (hFlags δ hz) _ rfl).1)
    (fun δ u hu _ ↦ stDualU2_dsc50_clnM52 h193 hScr isCsel r41 _ _ _ _ u hu)
    (fun δ u _ ↦ stDualU2_dsc50_clnCar15 h193 hScr isCsel r41 _ _ _ _ u)
    (fun δ hz ↦ by
      have h5 := stDualU2_dsc50_hdr52 h193 hScr isCsel r41 (fS1 δ) (fS2 δ) (z16Init δ) (st δ)
      dsimp only
      rw [h5 ⟨0, ow0_lt5⟩, h5 ⟨1, ow1_lt5⟩, h5 ⟨2, ow2_lt5⟩, h5 ⟨3, ow3_lt5⟩, h5 ⟨4, ow4_lt5⟩]
      dsimp only [p1Fn, p2Fn]
      rw [(dualHdr_target_eq_dm2_193 h193 isCsel pkgMid r41 (z16Init δ) (st δ)
          (hFlags δ hz) _ rfl).2]
      have hZInit : (fun j : Fin 16 ↦
          stDualU2_dsc50 h193 hScr isCsel r41 (fS1 δ) (fS2 δ) (z16Init δ) (st δ)
              (rMuxZ16 r41 j)) = z16Init δ :=
        funext fun j ↦ stDualU2_dsc50_z16 h193 hScr isCsel r41 _ _ _ _ j
      refine ⟨funext fun w ↦ ?_, by
        dsimp only [phOWZ16, phL2, z16L1]
        rw [zero_add, ← phAddVal, hZInit]
        exact (phAddVal_mod17_sum (z16Init δ) _ _).symm⟩
      by_cases hwZ : ∃ j : Fin 16, rMuxZ16 r41 j = w
      · obtain ⟨j, rfl⟩ := hwZ
        rw [stDualU2_dsc50_z16, stOWZ16_apply_reg, hZInit]
        exact congrFun (z16AddVal_mod17_sum (z16Init δ) _ _).symm j
      · rw [stOWZ16_outside _ _ _ δ fun j h ↦ hwZ ⟨j, h.symm⟩]
        exact stDualU2_dsc50_eq_of_ne_z16 h193 hScr isCsel r41 _ _ _ _ (st δ) fun j h ↦
            hwZ ⟨j, h.symm⟩)
  obtain ⟨sU2, tU2, fU2⟩ :=
      step_wrapUncopy24 h193 v rWork (rPotBPortB r41) r41 (owBlk_disj r41 (by omega))
    (st6 z16Init) (st6 z16L2) (fun _ ↦ 0) phL2 _
    (fun δ i _ ↦ by
      have hSub (zX : Fin 16 → ZMod 2) :
          writeReg (stDualF2_dsc50 h193 hScr isCsel r41 (fS1 δ) zX (st δ))
              (rDualScr2_193 h193 hScr r41)
            (fS2 δ) (rMuxCopy24 h193 r41 i) =
          writeReg (stDualF2_dsc50 h193 hScr isCsel r41 (fS1 δ) zX (st δ))
              (rDualScr2_193 h193 hScr r41)
            (fS2 δ) (rPotBPortB r41 i) := by
        rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦
            disj_ne (dualDisj_copy_scr2_193 h193 hScr r41) i u hu.symm),
            writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦ r41_blk_ne_blk r41 u i (by
              have := u.isLt
              omega) hu),
            stDualF2_dsc50_copy,
            show rPotBPortB r41 i = r41 ⟨57 + i.val, by omega⟩ from
              congrArg r41.wires (Fin.ext (by simp only [QRegister.block_apply_val])),
            stDualF2_dsc50_lt106 h193 hScr isCsel r41 (fS1 δ) zX (st δ) (by omega)]
      exact ⟨hSub (z16Init δ), hSub (z16L2 δ)⟩) sCore
  exact ⟨sU2, tU2.trans tCore, fU2.trans fCore⟩

attribute [irreducible] pMuxDualAfterSB2_dsc50

theorem stDualH_dm2_copy_zero {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (i : Fin 24) :
    stDualH_dm2 h193 isCsel r41 z16 β (rMuxCopy24 h193 r41 i) = 0 := by
  have := wtop_ge192 h193 isCsel
  have := i.isLt
  rw [show rMuxCopy24 h193 r41 i = r41 ⟨122 + (120 + i.val), by omega⟩ from
    congrArg r41.wires (Fin.ext (by omega : 242 + i.val = 122 + (120 + i.val)))]
  exact stDualH_dm2_work_zero_193 h193 isCsel r41 z16 β (by omega) (by omega) (by omega)
    (noGate_of_lt_wtop isCsel (by omega)) (Or.inl (by omega))

theorem step_pMuxDualAfterSB1_dsc50 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp kScr tSB kMid tMid n : ℕ} [NeZero (2 ^ n)]
    (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgMid : MidOWU10Pkg true 14 kMid tMid)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st : BitAssignment n → BitAssignment n)
    (z16Init : BitAssignment n → Fin 16 → ZMod 2)
    (fS1 : BitAssignment n → Fin kScr → ZMod 2)
    (hFlags : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags r41 (st δ))
    (hP1 : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ j : Fin 6,
      fS1 δ ⟨j.val, sbScr_lt6 pkgSB.h6 j⟩ =
        if (pre6OfCoords (coordOfReg24 (rPotBNucA r41) (st δ))
              (coordOfReg24 (rPotBElecA r41) (st δ))).val.testBit j.val then 1 else 0) :
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60 pkgMid
    let z16L1 := fun δ ↦ z16AddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ))
    let z16L2 := fun δ ↦ z16AddVal (z16L1 δ) (v2Mux isCsel pkgLM r41 (st δ))
    let phL2 := fun δ ↦
        phAddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ)) + phAddVal (z16L1 δ)
        (v2Mux isCsel pkgLM r41 (st δ))
    let st2 := fun (zX : BitAssignment n → Fin 16 → ZMod 2) (δ : BitAssignment n) ↦ writeReg
        (writeReg (stDualH_dm2 h193 isCsel r41 (zX δ) (st δ)) (rMuxCopy24 h193 r41)
            (fun i ↦ stDualH_dm2 h193 isCsel r41 (zX δ) (st δ) (rPotBNucA r41 i)))
            (rDualScr1_193 h193 hScr r41) (fS1 δ)
    let p := pMuxDualAfterSB1_dsc50 h193 isCsel pkgSB hScr v r41
    SubspaceStep (mkKetOpW rWork (st2 z16Init) (fun _ ↦ 0))
      (mkKetOpW rWork (st2 z16L2) phL2) p ∧
    p.count .T = tSB + 180 ∧
    p.count .TOFF = 0 := by
  intro pkgLM z16L1 z16L2 phL2 st2 p
  have := wtop_ge192 h193 isCsel
  have hdNA : (rPotBNucA r41).DisjointWires (rMuxCopy24 h193 r41) := owBlk_disj r41 (by omega)
  have hdPB : (rPotBPortB r41).DisjointWires (rMuxCopy24 h193 r41) := owBlk_disj r41 (by omega)
  let rC := rMuxCopy24 h193 r41
  let rM1 := rMuxM1 h193 isCsel r41
  let rS2 := rDualScr2_193 h193 hScr r41
  obtain ⟨sSB2, tSB2, fSB2, _⟩ := pkgSB.step_and_counts v rWork rM1 rC rS2
    (dualDisj_m1_copy_193 h193 isCsel r41) (dualDisj_m1_scr2_193 h193 hScr isCsel r41)
    (dualDisj_copy_scr2_193 h193 hScr r41)
    (fun δ ↦ stDualF2_dsc50 h193 hScr isCsel r41 (fS1 δ) (z16Init δ) (st δ))
    (fun δ ↦ stDualF2_dsc50 h193 hScr isCsel r41 (fS1 δ) (z16L2 δ) (st δ))
    (fun _ ↦ 0) phL2 (pMuxDualAfterSB2_dsc50 h193 isCsel v r41)
    (fun δ u _ ↦ stDualF2_dsc50_scr2_zero h193 hScr isCsel r41 (fS1 δ) (z16Init δ) (st δ) u)
    (fun δ _ ↦ ⟨fun i ↦ by rw [stDualF2_dsc50_m1_bit, stDualF2_dsc50_m1_bit],
      fun i ↦ by rw [stDualF2_dsc50_copy, stDualF2_dsc50_copy],
      fun u ↦ stDualF2_dsc50_scr2_zero h193 hScr isCsel r41 (fS1 δ) (z16L2 δ) (st δ) u⟩)
    (fun stMid2 hKeep2 hPre6_2 ↦
      step_of_writeReg_keep hKeep2 (step_pMuxDualAfterSB2_dsc50 h193 hScr pkgSB.h6 isCsel pkgMid
        v rWork r41 st z16Init fS1 (fun δ u ↦ stMid2 δ (rS2 u)) hFlags hP1 fun δ hz j ↦ by
          have h := hPre6_2 δ hz j
          rwa [coordOfReg24_ite (st δ (wPotBIsNN r41) == 1) _ _ _ _ _ (fun i ↦
                 stDualF2_dsc50_m1_bit h193 hScr isCsel r41 (fS1 δ) (z16Init δ) (st δ) i),
               coordOfReg24_congr _ _ _ _ (fun i ↦
                 stDualF2_dsc50_copy h193 hScr isCsel r41 (fS1 δ) (z16Init δ) (st δ) i)] at h).1)
  obtain ⟨_, tAfter2, fAfter2⟩ := step_pMuxDualAfterSB2_dsc50 h193 hScr pkgSB.h6 isCsel pkgMid
    v rWork r41 st z16Init fS1 (fun δ u ↦ if (pre6OfCoords (if st δ (wPotBIsNN r41) == 1 then
      coordOfReg24 (rPotBElecA r41) (st δ) else coordOfReg24 (rPotBNucA r41) (st δ))
      (coordOfReg24 (rPotBPortB r41)
          (st δ))).val.testBit u.val then 1 else 0) hFlags hP1 (fun _ _ _ ↦ rfl)
  obtain ⟨sF2, tF2, fF2⟩ := step_wrapFlipLeg2 h193 isCsel v rWork r41
    (fun δ ↦ stDualC2_dsc50 h193 hScr isCsel r41 (fS1 δ) (z16Init δ) (st δ))
    (fun δ ↦ stDualC2_dsc50 h193 hScr isCsel r41 (fS1 δ) (z16L2 δ) (st δ))
    (fun _ ↦ 0) phL2 (pkgSB.wrapDom v rM1 rC rS2 (pMuxDualAfterSB2_dsc50 h193 isCsel v r41)) sSB2
  have hS1Copy0 (zX : Fin 16 → ZMod 2) (δ : BitAssignment n) (i : Fin 24) :
      stDualS1_dsc50 h193 hScr isCsel r41 (fS1 δ) zX (st δ) (rC i) = 0 :=
    (writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦
        disj_ne (dualDisj_copy_scr1_193 h193 hScr r41) i u hu.symm)).trans
      (stDualH_dm2_copy_zero h193 isCsel r41 zX (st δ) i)
  obtain ⟨sC2, tC2, fC2⟩ := step_wrapCopy24 h193 v rWork (rPotBPortB r41) r41 hdPB
    (fun δ ↦ stDualS1_dsc50 h193 hScr isCsel r41 (fS1 δ) (z16Init δ) (st δ))
    (fun δ ↦ stDualS1_dsc50 h193 hScr isCsel r41 (fS1 δ) (z16L2 δ) (st δ))
    (fun _ ↦ 0) phL2
    (wrapFlipLeg2 h193 isCsel v r41 (pkgSB.wrapDom v rM1 rC rS2 (pMuxDualAfterSB2_dsc50 h193 isCsel
        v r41)))
    (fun δ i _ ↦ ⟨hS1Copy0 (z16Init δ) δ i, hS1Copy0 (z16L2 δ) δ i⟩) sF2
  have hUncopy1Eq (zX : BitAssignment n → Fin 16 → ZMod 2) :
      (fun δ ↦ writeReg (st2 zX δ) rC (fun _ ↦ 0)) =
      (fun δ ↦ stDualS1_dsc50 h193 hScr isCsel r41 (fS1 δ) (zX δ) (st δ)) :=
    funext fun δ ↦ funext fun w ↦ by
      by_cases hmC : ∃ i : Fin 24, rC i = w
      · obtain ⟨i, rfl⟩ := hmC
        exact (writeReg_apply_reg _ rC _ i).trans (hS1Copy0 (zX δ) δ i).symm
      · rw [writeReg_apply_of_not_mem _ _ _ w hmC]
        exact writeReg_congr_out rfl (writeReg_apply_of_not_mem _ _ _ w hmC)
  obtain ⟨sU1, tU1, fU1⟩ := step_wrapUncopy24 h193 v rWork (rPotBNucA r41) r41 hdNA
    (st2 z16Init) (st2 z16L2) (fun _ ↦ 0) phL2
    (wrapCopy24 h193 v (rPotBPortB r41) r41 hdPB
      (wrapFlipLeg2 h193 isCsel v r41 (pkgSB.wrapDom v rM1 rC rS2 (pMuxDualAfterSB2_dsc50 h193
          isCsel v r41))))
    (fun δ i _ ↦ by
      have hSub (zX : BitAssignment n → Fin 16 → ZMod 2) : st2 zX δ (rC i) =
          st2 zX δ (rPotBNucA r41 i) := by
        dsimp only [st2]
        rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦
            disj_ne (dualDisj_copy_scr1_193 h193 hScr r41) i u hu.symm),
            writeReg_apply_reg,
            writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦ r41_blk_ne_blk r41 u i (by omega) hu),
            writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦ disj_ne hdNA i k hk.symm)]
      exact ⟨hSub z16Init, hSub z16L2⟩)
    (subspaceStep_of_eq_pre_local
      (mkKetOpW_congr rWork (fun δ _ ↦ congrFun (hUncopy1Eq z16Init) δ) (fun _ _ ↦ rfl))
      (subspaceStep_of_eq_post sC2 (mkKetOpW_congr rWork (fun δ _ ↦
          (congrFun (hUncopy1Eq z16L2) δ).symm) (fun _ _ ↦ rfl))))
  exact ⟨sU1, by
    change (wrapCopy24 h193 v (rPotBNucA r41) r41 hdNA _).count .T = tSB + 180
    rw [tU1, tC2, tF2, tSB2, tAfter2], by
    change (wrapCopy24 h193 v (rPotBNucA r41) r41 hdNA _).count .TOFF = 0
    rw [fU1, fC2, fF2, fSB2, fAfter2]⟩
attribute [irreducible] pMuxDualAfterSB1_dsc50

theorem step_pMuxDualLegsInner_dsc50 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp kScr tSB kMid tMid n : ℕ} [NeZero (2 ^ n)]
    (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgMid : MidOWU10Pkg true 14 kMid tMid)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st : BitAssignment n → BitAssignment n)
    (z16Init : BitAssignment n → Fin 16 → ZMod 2)
    (hFlags : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags r41 (st δ)) :
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60 pkgMid
    let z16L1 := fun δ ↦ z16AddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ))
    let z16L2 := fun δ ↦ z16AddVal (z16L1 δ) (v2Mux isCsel pkgLM r41 (st δ))
    let phL2 := fun δ ↦
        phAddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ)) + phAddVal (z16L1 δ)
        (v2Mux isCsel pkgLM r41 (st δ))
    let p := pMuxDualLegsInner_dsc50 h193 isCsel pkgSB hScr v r41
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ stDualH_dm2 h193 isCsel r41 (z16Init δ) (st δ)) (fun _ ↦ 0))
      (mkKetOpW rWork (fun δ ↦ stDualH_dm2 h193 isCsel r41 (z16L2 δ) (st δ)) phL2) p ∧
    p.count .T = 2 * tSB + 180 ∧
    p.count .TOFF = 0 := by
  intro pkgLM z16L1 z16L2 phL2 p
  have := wtop_ge192 h193 isCsel
  let rC := rMuxCopy24 h193 r41
  let rS1 := rDualScr1_193 h193 hScr r41
  let stH (zX : BitAssignment n → Fin 16 → ZMod 2) (δ : BitAssignment n) :=
      stDualH_dm2 h193 isCsel r41 (zX δ) (st δ)
  let st1 (zX : BitAssignment n → Fin 16 → ZMod 2) (δ : BitAssignment n) :=
    writeReg (stH zX δ) rC (fun i ↦ stH zX δ (rPotBNucA r41 i))
  have hNA_stH (zX : BitAssignment n → Fin 16 → ZMod 2) (δ : BitAssignment n) (i : Fin 24) :
      stH zX δ (rPotBNucA r41 i) = st δ (rPotBNucA r41 i) := by
    have := i.isLt
    rw [show rPotBNucA r41 i = r41 ⟨9 + i.val, by omega⟩ from congrArg r41.wires (Fin.ext rfl)]
    exact stDualH_dm2_lt106 h193 isCsel r41 (zX δ) (st δ) (by omega)
  have hS1Zero (zX : BitAssignment n → Fin 16 → ZMod 2) (δ : BitAssignment n)
      (u : Fin kScr) : st1 zX δ (rS1 u) = 0 := by
    have := u.isLt
    dsimp only [st1]
    rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦
        disj_ne (dualDisj_copy_scr1_193 h193 hScr r41) i u hi),
        show rS1 u = r41 ⟨122 + u.val, by omega⟩ from congrArg r41.wires (Fin.ext rfl)]
    exact stDualH_dm2_work_zero_193 h193 isCsel r41 (zX δ) (st δ) (by omega) (by omega) (by omega)
      (noGate_of_lt_wtop isCsel (by omega)) (Or.inl (by omega))
  obtain ⟨sSB1, tSB1, fSB1, _⟩ := pkgSB.step_and_counts v rWork rC (rPotBElecA r41) rS1
    (dualDisj_copy_elec h193 r41) (dualDisj_copy_scr1_193 h193 hScr r41)
        (dualDisj_elec_scr1_193 h193 hScr r41)
    (st1 z16Init) (st1 z16L2) (fun _ ↦ 0) phL2 (pMuxDualAfterSB1_dsc50 h193 isCsel pkgSB hScr v r41)
    (fun δ u _ ↦ hS1Zero z16Init δ u)
    (fun δ _ ↦ ⟨fun i ↦ by
        dsimp only [st1]
        rw [writeReg_apply_reg, writeReg_apply_reg, hNA_stH, hNA_stH],
      fun i ↦ by
        dsimp only [st1, stH]
        rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦
            disj_ne (dualDisj_copy_elec h193 r41) k i hk),
            writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦
                disj_ne (dualDisj_copy_elec h193 r41) k i hk),
            stDualH_dm2_eq_of_ne_z16 h193 isCsel r41 _ _ _ (fun j h ↦
                r41_blk_ne_blk r41 i j (by omega) h)],
      fun u ↦ hS1Zero z16L2 δ u⟩)
    (fun stMid1 hKeep1 hPre6_1 ↦
      step_of_writeReg_keep hKeep1 (step_pMuxDualAfterSB1_dsc50 h193 isCsel pkgSB hScr pkgMid v
          rWork r41 st z16Init
        (fun δ u ↦ stMid1 δ (rS1 u)) hFlags fun δ hz j ↦ by
          rw [← coordOfReg24_congr rC (rPotBNucA r41) (st1 z16Init δ) (st δ)
                (fun i ↦ (writeReg_apply_reg _ rC _ i).trans (hNA_stH z16Init δ i)),
              ← coordOfReg24_congr (rPotBElecA r41) (rPotBElecA r41) (st1 z16Init δ) (st δ) fun i ↦
                  by
                have := i.isLt
                dsimp only [st1, stH]
                rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦
                    disj_ne (dualDisj_copy_elec h193 r41) k i hk),
                    show rPotBElecA r41 i = r41 ⟨33 + i.val,
                        by omega⟩ from congrArg r41.wires (Fin.ext rfl),
                    stDualH_dm2_lt106 h193 isCsel r41 (z16Init δ) (st δ) (by omega)]]
          exact hPre6_1 δ hz j).1)
  obtain ⟨_, tAfter1, fAfter1⟩ :=
      step_pMuxDualAfterSB1_dsc50 h193 isCsel pkgSB hScr pkgMid v rWork r41 st z16Init
    (fun δ u ↦ if (pre6OfCoords (coordOfReg24 (rPotBNucA r41) (st δ))
      (coordOfReg24 (rPotBElecA r41) (st δ))).val.testBit u.val then 1 else 0) hFlags (fun _ _ _ ↦
          rfl)
  obtain ⟨sC1, tC1, fC1⟩ :=
      step_wrapCopy24 h193 v rWork (rPotBNucA r41) r41 (owBlk_disj r41 (by omega))
    (stH z16Init) (stH z16L2) (fun _ ↦ 0) phL2 _
    (fun δ i _ ↦ ⟨stDualH_dm2_copy_zero h193 isCsel r41 (z16Init δ) (st δ) i,
      stDualH_dm2_copy_zero h193 isCsel r41 (z16L2 δ) (st δ) i⟩) sSB1
  refine ⟨sC1, ?_, fC1.trans (fSB1.trans fAfter1)⟩
  dsimp only [p, pMuxDualLegsInner_dsc50]
  rw [tC1, tSB1, tAfter1]
  omega

theorem step_pMuxDualLegsBlock_dsc50 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp kScr tSB kMid tMid n : ℕ} [NeZero (2 ^ n)]
    (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgMid : MidOWU10Pkg true 14 kMid tMid)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st : BitAssignment n → BitAssignment n)
    (z16Init : BitAssignment n → Fin 16 → ZMod 2)
    (hFlags : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags r41 (st δ)) :
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60 pkgMid
    let z16L1 := fun δ ↦ z16AddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ))
    let z16L2 := fun δ ↦ z16AddVal (z16L1 δ) (v2Mux isCsel pkgLM r41 (st δ))
    let phL2 := fun δ ↦
        phAddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ)) + phAddVal (z16L1 δ)
        (v2Mux isCsel pkgLM r41 (st δ))
    let p := pMuxDualLegsBlock_dsc50 h193 isCsel pkgSB hScr v r41
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16Init δ) (st δ)) (fun _ ↦ 0))
      (mkKetOpW rWork (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16L2 δ) (st δ)) phL2) p ∧
    p.count .T = (if isCsel then 8 else 0) + (2 * tSB + 180) ∧
    p.count .TOFF = 0 := by
  intro pkgLM z16L1 z16L2 phL2 p
  obtain ⟨sInner, tInner, fInner⟩ :=
      step_pMuxDualLegsInner_dsc50 h193 isCsel pkgSB hScr pkgMid v rWork r41 st z16Init hFlags
  obtain ⟨sBlk, tBlk, fBlk⟩ :=
      step_wrapHdrCascade2 h193 isCsel v rWork r41 (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16Init δ)
      (st δ)) (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16L2 δ) (st δ)) (fun _ ↦ 0) phL2
      (pMuxDualLegsInner_dsc50 h193 isCsel pkgSB hScr v r41) (fun δ _ ↦
        ⟨muxStNoM2_240_zero h193 isCsel r41 _ _ _, muxStNoM2_240_zero h193 isCsel r41 _ _ _⟩)
      (fun δ _ ↦ ⟨muxStNoM2_241_zero h193 isCsel r41 _ _ _,
          muxStNoM2_241_zero h193 isCsel r41 _ _ _⟩) sInner
  exact ⟨sBlk, tBlk.trans (congrArg _ tInner), fBlk.trans fInner⟩


def idxMuxDistPebIpbOff (Wp : ℕ) (isCsel : Bool) (u : ℕ) : ℕ :=
    if 18 + u < Wtop Wp isCsel - 48 then 18 + u else 18 + u + 24
def idxMuxDistPebIpb (Wp : ℕ) (isCsel : Bool) (u : ℕ) : ℕ := 122 + idxMuxDistPebIpbOff Wp isCsel u
theorem idxMuxDistPebIpbOff_bounds {Wp k : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hK : 18 + k ≤ Wp - 25) (u : Fin k) : 18 ≤ idxMuxDistPebIpbOff Wp isCsel u.val ∧
    idxMuxDistPebIpbOff Wp isCsel u.val < Wtop Wp isCsel ∧
    (idxMuxDistPebIpbOff Wp isCsel u.val < Wtop Wp isCsel - 48 ∨ Wtop Wp isCsel - 24 ≤
        idxMuxDistPebIpbOff Wp isCsel u.val) := by
  have := And.intro (wtop_ge192 h193 isCsel) (And.intro (wp_sub1_le_wtop Wp isCsel) u.isLt)
  unfold idxMuxDistPebIpbOff
  split_ifs <;> omega

theorem idxMuxDistPebIpb_lt {Wp k : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (hK : 18 + k ≤ Wp - 25)
    (u : Fin k) : idxMuxDistPebIpb Wp isCsel u.val < 122 + Wp := by
  have := And.intro (idxMuxDistPebIpbOff_bounds h193 isCsel hK u) (wtop_le_wp Wp isCsel)
  unfold idxMuxDistPebIpb
  omega
theorem idxMuxDistPebIpb_inj {Wp k : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (_hK : 18 + k ≤ Wp - 25)
    : Function.Injective (fun u : Fin k ↦ idxMuxDistPebIpb Wp isCsel u.val) := by
  intro a b h
  have := And.intro (wtop_ge192 h193 isCsel) (And.intro a.isLt b.isLt)
  dsimp only [idxMuxDistPebIpb, idxMuxDistPebIpbOff] at h
  split_ifs at h <;> exact Fin.ext (by omega)

def rMuxDistScrPebIpb {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (hK : 18 + k ≤ Wp - 25)
    (r41 : QRegister (122 + Wp) n) : QRegister k n := r41.compose
    ⟨⟨fun u ↦ ⟨idxMuxDistPebIpb Wp isCsel u.val, idxMuxDistPebIpb_lt h193 isCsel hK u⟩, fun _ _ e ↦
        idxMuxDistPebIpb_inj h193 isCsel hK (congrArg Fin.val e)⟩⟩
theorem muxDisj_m1_scrPebIpb {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hK : 18 + k ≤ Wp - 25) (r41 : QRegister (122 + Wp) n) :
    (rMuxM1 h193 isCsel r41).DisjointWires (rMuxDistScrPebIpb h193 isCsel hK r41) :=
  owCompose_disj r41 fun i u ↦ by
    have := And.intro (wtop_ge192 h193 isCsel)
      (And.intro (idxMuxDistPebIpbOff_bounds h193 isCsel hK u) i.isLt)
    simp only [QRegister.block_apply_val]
    change 122 + Wtop Wp isCsel - 48 + i.val ≠ idxMuxDistPebIpb Wp isCsel u.val
    unfold idxMuxDistPebIpb
    omega
theorem muxDisj_portB_scrPebIpb {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hK : 18 + k ≤ Wp - 25) (r41 : QRegister (122 + Wp) n) :
    (rPotBPortB r41).DisjointWires (rMuxDistScrPebIpb h193 isCsel hK r41) :=
  owCompose_disj r41 fun i u ↦ by
    have := And.intro (idxMuxDistPebIpbOff_bounds h193 isCsel hK u) i.isLt
    simp only [QRegister.block_apply_val]
    change 57 + i.val ≠ idxMuxDistPebIpb Wp isCsel u.val
    unfold idxMuxDistPebIpb
    omega
theorem muxDisj_scrPebIpb_d2 {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hK : 18 + k ≤ Wp - 25) (r41 : QRegister (122 + Wp) n) :
    (rMuxDistScrPebIpb h193 isCsel hK r41).DisjointWires (rMuxD2_18 h193 r41) :=
  owCompose_disj r41 fun u j ↦ by
    have := And.intro (idxMuxDistPebIpbOff_bounds h193 isCsel hK u) j.isLt
    simp only [QRegister.block_apply_val]
    change idxMuxDistPebIpb Wp isCsel u.val ≠ 122 + j.val
    unfold idxMuxDistPebIpb
    omega
theorem muxStNoM2_rMuxDistScrPebIpb_zero {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hK : 18 + k ≤ Wp - 25) (r41 : QRegister (122 + Wp) n)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (u : Fin k) :
    muxStNoM2 h193 isCsel r41 0 z16 β (rMuxDistScrPebIpb h193 isCsel hK r41 u) = 0 := by
  have hb := idxMuxDistPebIpbOff_bounds h193 isCsel hK u
  have hwle := wtop_le_wp Wp isCsel
  exact muxStNoM2_pool_zero h193 isCsel r41 0 z16 β (u := idxMuxDistPebIpbOff Wp isCsel u.val)
    (by omega) (noGate_of_lt_wtop isCsel hb.2.1) (by omega)


theorem biasCoord_mod2_pebIpb : ∀ u : Fin 256, biasCoord u % 2 = u.val % 2 := fun u ↦ by
  have h1 : (biasCoord u).testBit 0 = u.val.testBit 0 := by
    unfold biasCoord
    rw [Nat.testBit_xor]
    simp
  rw [Nat.testBit_zero, Nat.testBit_zero] at h1
  rcases (by omega : biasCoord u % 2 = 0 ∨ biasCoord u % 2 = 1) with e1 | e1 <;>
    rcases (by omega : u.val % 2 = 0 ∨ u.val % 2 = 1) with e2 | e2 <;> simp [e1, e2] at h1 ⊢

theorem openBoxDist1D_mod2_pebIpb (u v : Fin 256) : openBoxDist1D u v % 2 =
    (u.val + v.val) % 2 := by
  rw [openBoxDist1D_eq_signedAbsD9]
  have := And.intro (And.intro (biasCoord_eq_all u).2 (biasCoord_eq_all v).2)
    (And.intro (biasCoord_mod2_pebIpb u) (biasCoord_mod2_pebIpb v))
  unfold signedAbsD9
  split_ifs <;> omega

theorem sq_mod2_pebIpb (d : ℕ) : d ^ 2 % 2 = d % 2 := by
  rw [pow_two, Nat.mul_mod]
  rcases (by omega : d % 2 = 0 ∨ d % 2 = 1) with h | h <;> simp [h]

theorem openCoordDistSq_mod2_pebIpb (a b : Fin 3 → Fin 256) : openCoordDistSq a b % 2 =
    ((a 0).val + (b 0).val + (a 1).val + (b 1).val + (a 2).val + (b 2).val) % 2 := by
  unfold openCoordDistSq
  have h0 :=
      (sq_mod2_pebIpb (openBoxDist1D (a 0) (b 0))).trans (openBoxDist1D_mod2_pebIpb (a 0) (b 0))
  have h1 :=
      (sq_mod2_pebIpb (openBoxDist1D (a 1) (b 1))).trans (openBoxDist1D_mod2_pebIpb (a 1) (b 1))
  have h2 :=
      (sq_mod2_pebIpb (openBoxDist1D (a 2) (b 2))).trans (openBoxDist1D_mod2_pebIpb (a 2) (b 2))
  omega
theorem natOfZModBits_one_pebIpb (g : Fin 1 → ZMod 2) : natOfZModBits 1 g = (g 0).val := by
  have hge : g = (fun _ ↦ g 0) := funext fun i ↦ congrArg g (Subsingleton.elim i 0)
  rw [hge]
  rcases DynCircExt.bit_cases (g 0) with h | h <;> (rw [h]; decide)

theorem byteOfBits_mod2_pebIpb (f : Fin 8 → ZMod 2) : (byteOfBits f).val % 2 = (f 0).val := by
  change finBitsVal f % 2 = (f 0).val
  rw [finBitsVal_eq_natOfZModBits 8 f, natOfZModBits_split 1 7 f, natOfZModBits_one_pebIpb]
  have := ZMod.val_lt (f 0)
  change ((f 0).val + 2 * _) % 2 = (f 0).val
  omega
theorem coordOfReg24_mod2_pebIpb {n : ℕ} (r24 : QRegister 24 n) (s : BitAssignment n) (ax : Fin 3) :
    (coordOfReg24 r24 s ax).val % 2 = (s (r24 ⟨8 * ax.val, by omega⟩)).val := by
  unfold coordOfReg24
  rw [byteOfBits_mod2_pebIpb]
  exact congrArg (fun k ↦ (s (r24 k)).val) (Fin.ext (Nat.add_zero (8 * ax.val)))

theorem testBit0_ite_eq_natCast_pebIpb (d : ℕ) : (if d.testBit 0 then (1 : ZMod 2) else 0) =
    ((d % 2 : ℕ) : ZMod 2) := by
  rw [Nat.testBit_zero]
  rcases (by omega : d % 2 = 0 ∨ d % 2 = 1) with h | h <;> simp [h]

theorem openCoordDistSq_lsb_zmod2_pebIpb {n : ℕ} (rA rB : QRegister 24 n) (s : BitAssignment n) :
    (if (openCoordDistSq (coordOfReg24 rA s)
    (coordOfReg24 rB s)).testBit 0 then (1 : ZMod 2) else 0) = s (rA 0) + s (rB 0) +
    s (rA 8) + s (rB 8) + s (rA 16) + s (rB 16) := by
  rw [testBit0_ite_eq_natCast_pebIpb, openCoordDistSq_mod2_pebIpb, ZMod.natCast_mod]
  push_cast
  have hmod : ∀ (x : ℕ), ((x : ZMod 2)) = (((x % 2 : ℕ) : ZMod 2)) := fun x ↦
      (ZMod.natCast_mod x 2).symm
  rw [hmod (coordOfReg24 rA s 0).val, coordOfReg24_mod2_pebIpb, ZMod.natCast_zmod_val,
      hmod (coordOfReg24 rB s 0).val, coordOfReg24_mod2_pebIpb, ZMod.natCast_zmod_val,
      hmod (coordOfReg24 rA s 1).val,
      coordOfReg24_mod2_pebIpb, ZMod.natCast_zmod_val, hmod (coordOfReg24 rB s 1).val,
          coordOfReg24_mod2_pebIpb, ZMod.natCast_zmod_val, hmod (coordOfReg24 rA s 2).val,
          coordOfReg24_mod2_pebIpb, ZMod.natCast_zmod_val,
      hmod (coordOfReg24 rB s 2).val, coordOfReg24_mod2_pebIpb, ZMod.natCast_zmod_val]
  rfl
theorem zmod2_add_self_pebIpb (x : ZMod 2) : x + x = 0 := by
  rcases DynCircExt.bit_cases x with rfl | rfl <;> decide

theorem step_single_cnot_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n)
    (c tgt : Wire n) (hne : c ≠ tgt)
    (st0 : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (Var := Var) (mkKetOpW rWork st0 ph)
      (mkKetOpW rWork (fun δ ↦ Function.update (st0 δ) tgt (st0 δ tgt + st0 δ c)) ph)
      (DynamicCircuit.circuit (Circuit.CNOT c tgt hne)) := by
  refine subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) (mkKetOpW rWork st0 ph) _) ?_
  apply matrix_ext_ket
  intro δ
  rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, ket_CNOT]
  · rw [Matrix.mulVec_zero]

def pScrubM1PebIpb {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) : DynamicCircuit Var n :=
  have hw := wtop_ge192 h193 isCsel
  let tgt := rMuxM1 h193 isCsel r41 16
  (DynamicCircuit.circuit (Circuit.CNOT (rMuxD2_18 h193 r41 0) tgt
      (r41_blk_ne_blk r41 (0 : Fin 18) (16 : Fin 24) (by omega)))).seq
    ((DynamicCircuit.circuit (Circuit.CNOT (rMuxM1 h193 isCsel r41 0) tgt
        ((rMuxM1 h193 isCsel r41).wires.injective.ne (by decide)))).seq
      ((DynamicCircuit.circuit (Circuit.CNOT (rPotBPortB r41 0) tgt
          (r41_blk_ne_blk r41 (0 : Fin 24) (16 : Fin 24) (by omega)))).seq
        ((DynamicCircuit.circuit (Circuit.CNOT (rMuxM1 h193 isCsel r41 8) tgt
            ((rMuxM1 h193 isCsel r41).wires.injective.ne (by decide)))).seq
          ((DynamicCircuit.circuit (Circuit.CNOT (rPotBPortB r41 8) tgt
              (r41_blk_ne_blk r41 (8 : Fin 24) (16 : Fin 24) (by omega)))).seq
            (DynamicCircuit.circuit (Circuit.CNOT (rPotBPortB r41 16) tgt
                (r41_blk_ne_blk r41 (16 : Fin 24) (16 : Fin 24) (by omega))))))))

theorem count_pScrubM1PebIpb {Var : Type} {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) :
    (pScrubM1PebIpb (Var := Var) h193 isCsel r41).count .T = 0 ∧
    (pScrubM1PebIpb (Var := Var) h193 isCsel r41).count .TOFF = 0 := by
  unfold pScrubM1PebIpb
  dsimp only
  constructor <;>
    simp only [dc_count_seq, dc_count_circ, (count_cnot_zero _ _ _).1, (count_cnot_zero _ _ _).2,
        add_zero]

theorem dynWires_pScrubM1PebIpb {Var : Type} {Wp n : ℕ} {S : Wire n → Prop}
    (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (hS : ∀ k, S (r41 k)) :
    DynWires S (pScrubM1PebIpb (Var := Var) h193 isCsel r41) := by
  unfold pScrubM1PebIpb
  dsimp only
  exact ⟨cw_cnot (hS _) (hS _), ⟨cw_cnot (hS _) (hS _), ⟨cw_cnot (hS _) (hS _), ⟨cw_cnot (hS _)
      (hS _), ⟨cw_cnot (hS _) (hS _), cw_cnot (hS _) (hS _)⟩⟩⟩⟩⟩

theorem scrubM1_ne {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n) :
    let tgt := rMuxM1 h193 isCsel r41 16
    rMuxD2_18 h193 r41 0 ≠ tgt ∧ rMuxM1 h193 isCsel r41 0 ≠ tgt ∧
    rPotBPortB r41 0 ≠ tgt ∧ rMuxM1 h193 isCsel r41 8 ≠ tgt ∧
    rPotBPortB r41 8 ≠ tgt ∧ rPotBPortB r41 16 ≠ tgt := by
  have := wtop_ge192 h193 isCsel
  exact ⟨r41_blk_ne_blk r41 (0 : Fin 18) (16 : Fin 24) (by omega),
    (rMuxM1 h193 isCsel r41).wires.injective.ne (by decide),
    r41_blk_ne_blk r41 (0 : Fin 24) (16 : Fin 24) (by omega),
    (rMuxM1 h193 isCsel r41).wires.injective.ne (by decide),
    r41_blk_ne_blk r41 (8 : Fin 24) (16 : Fin 24) (by omega),
    r41_blk_ne_blk r41 (16 : Fin 24) (16 : Fin 24) (by omega)⟩

theorem step_pScrubM1PebIpb_gen {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp n : ℕ} [NeZero (2 ^ n)] (h193 : 193 ≤ Wp) (isCsel : Bool)
    (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st0 : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (Var := Var) (mkKetOpW rWork st0 ph)
      (mkKetOpW rWork (fun δ ↦ Function.update (st0 δ) (rMuxM1 h193 isCsel r41 16)
        (st0 δ (rMuxM1 h193 isCsel r41 16) +
          st0 δ (rMuxD2_18 h193 r41 0) +
          st0 δ (rMuxM1 h193 isCsel r41 0) +
          st0 δ (rPotBPortB r41 0) +
          st0 δ (rMuxM1 h193 isCsel r41 8) +
          st0 δ (rPotBPortB r41 8) +
          st0 δ (rPotBPortB r41 16))) ph)
      (pScrubM1PebIpb h193 isCsel r41) := by
  let tgt := rMuxM1 h193 isCsel r41 16
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := scrubM1_ne h193 isCsel r41
  have step1 {c : Wire n} {s stF : BitAssignment n → BitAssignment n} (hne : c ≠ tgt)
      {q : DynamicCircuit Var n}
      (hs : SubspaceStep (mkKetOpW rWork (fun δ ↦ Function.update (s δ) tgt (s δ tgt + s δ c)) ph)
        (mkKetOpW rWork stF ph) q) :
      SubspaceStep (mkKetOpW rWork s ph) (mkKetOpW rWork stF ph)
        ((DynamicCircuit.circuit (Circuit.CNOT c tgt hne)).seq q) :=
    subspaceStep_seq_u (step_single_cnot_pebIpb rWork c tgt hne s ph) hs
  unfold pScrubM1PebIpb
  dsimp only
  refine step1 h1 (step1 h2 (step1 h3 (step1 h4 (step1 h5 ?_))))
  refine subspaceStep_of_eq_post (step_single_cnot_pebIpb rWork _ tgt h6 _ ph)
    (mkKetOpW_congr rWork (fun δ _ ↦ ?_) (fun _ _ ↦ rfl))
  dsimp only [tgt] at h2 h3 h4 h5 h6 ⊢
  simp only [Function.update_idem, Function.update_self, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
    Function.update_of_ne h6, add_assoc]
theorem muxStNoM2D2_lsb_sum_eq_m1_16_pebIpb {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2)
    {β : BitAssignment n}
    (hPB0 : β (wPotBIsScreen r41) = 0 → ∀ i : Fin 24, β (rPotBPortB r41 i) = 0) :
    let β' := xorPortB41NotScr r41 β
    let sD2 := muxStNoM2D2 h193 isCsel r41 z16 β'
    sD2 (rMuxD2_18 h193 r41 0) +
      sD2 (rMuxM1 h193 isCsel r41 0) +
      sD2 (rPotBPortB r41 0) +
      sD2 (rMuxM1 h193 isCsel r41 8) +
      sD2 (rPotBPortB r41 8) +
      sD2 (rPotBPortB r41 16) =
    sD2 (rMuxM1 h193 isCsel r41 16) := by
  have hw := wtop_ge192 h193 isCsel
  intro β' sD2
  let st0 := muxStNoM2 h193 isCsel r41 0 z16 β'
  have hd0 : sD2 (rMuxD2_18 h193 r41 0) =
      if (openCoordDistSq (coordOfReg24 (rMuxM1 h193 isCsel r41) st0)
      (coordOfReg24 (rPotBPortB r41) st0)).testBit 0 then 1 else 0 := by
    dsimp only [sD2, st0, β']
    rw [muxStNoM2D2_d2 h193 isCsel r41 z16 (xorPortB41NotScr r41 β) 0,
        ← openCoordDistSq_muxStNoM2_m1_portB h193 isCsel r41 z16 hPB0]
    rfl
  have hm1Eq : ∀ i : Fin 24, sD2 (rMuxM1 h193 isCsel r41 i) = st0 (rMuxM1 h193 isCsel r41 i) :=
    fun i ↦ writeReg_apply_of_not_mem _ (rMuxD2_18 h193 r41) _ _
      (fun ⟨j, hj⟩ ↦ r41_blk_ne_blk r41 j i (by omega) hj)
  have hpbEq : ∀ i : Fin 24, sD2 (rPotBPortB r41 i) = st0 (rPotBPortB r41 i) :=
    fun i ↦ writeReg_apply_of_not_mem _ (rMuxD2_18 h193 r41) _ _
      (fun ⟨j, hj⟩ ↦ r41_blk_ne_blk r41 j i (by omega) hj)
  rw [hd0, openCoordDistSq_lsb_zmod2_pebIpb, hm1Eq 0, hm1Eq 8, hm1Eq 16, hpbEq 0, hpbEq 8, hpbEq 16]
  rcases DynCircExt.bit_cases (st0 (rMuxM1 h193 isCsel r41 0)) with h0 | h0 <;>
    rcases DynCircExt.bit_cases (st0 (rPotBPortB r41 0)) with h1 | h1 <;>
    rcases DynCircExt.bit_cases (st0 (rMuxM1 h193 isCsel r41 8)) with h2 | h2 <;>
    rcases DynCircExt.bit_cases (st0 (rPotBPortB r41 8)) with h3 | h3 <;>
    rcases DynCircExt.bit_cases (st0 (rMuxM1 h193 isCsel r41 16)) with h4 | h4 <;>
    rcases DynCircExt.bit_cases (st0 (rPotBPortB r41 16)) with h5 | h5 <;>
    (rw [h0, h1, h2, h3, h4, h5]; decide)


def muxStNoM2D2PebIpb {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (r41 : QRegister (122 + Wp) n)
    (M : ℕ) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) : BitAssignment n := Function.update
    (writeReg (muxStNoM2 h193 isCsel r41 M z16 β) (rMuxD2_18 h193 r41)
        (fun j ↦ if (muxD2Val r41 β).testBit j.val then 1 else 0)) (rMuxM1 h193 isCsel r41 16) 0
theorem muxStNoM2D2PebIpb_zero_eq_update {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) :
    muxStNoM2D2PebIpb h193 isCsel r41 0 z16 β =
      Function.update (muxStNoM2D2 h193 isCsel r41 z16 β) (rMuxM1 h193 isCsel r41 16) 0 := rfl

theorem muxStNoM2D2PebIpb_d2 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (M : ℕ) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n)
    (j : Fin 18) : muxStNoM2D2PebIpb h193 isCsel r41 M z16 β
    (rMuxD2_18 h193 r41 j) = if (muxD2Val r41 β).testBit j.val then 1 else 0 := by
  have hw := wtop_ge192 h193 isCsel
  unfold muxStNoM2D2PebIpb
  rw [Function.update_of_ne (r41_blk_ne_blk r41 j (16 : Fin 24) (by omega)), writeReg_apply_reg]

theorem muxStNoM2D2PebIpb_lt106 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (M : ℕ) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n)
    {m : ℕ} (hm : m < 106) :
    muxStNoM2D2PebIpb h193 isCsel r41 M z16 β (r41 ⟨m, by omega⟩) = β (r41 ⟨m, by omega⟩) := by
  have hw := wtop_ge192 h193 isCsel
  unfold muxStNoM2D2PebIpb
  rw [Function.update_of_ne (r41_wire_ne_blk r41 _ (16 : Fin 24) (by omega)),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ r41_blk_ne_wire r41 j _ (by omega) hj)]
  exact muxStNoM2_lt106 h193 isCsel r41 M z16 β hm

theorem muxStNoM2D2PebIpb_z16 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (M : ℕ) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n)
    (j : Fin 16) : muxStNoM2D2PebIpb h193 isCsel r41 M z16 β
    (rMuxZ16 r41 j) = z16 j := by
  have hw := wtop_ge192 h193 isCsel
  unfold muxStNoM2D2PebIpb
  rw [Function.update_of_ne (r41_blk_ne_blk r41 j (16 : Fin 24) (by omega)),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ r41_blk_ne_blk r41 i j (by omega) hi)]
  exact muxStNoM2_z16 h193 isCsel r41 M z16 β j

theorem muxStNoM2D2PebIpb_gate {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (M : ℕ) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) :
    muxStNoM2D2PebIpb h193 isCsel r41 M z16 β
    (wMuxGate h193 isCsel r41) = if potBGateActive isCsel r41 β then 1 else 0 := by
  have hw := wtop_ge192 h193 isCsel
  cases isCsel <;> simp only [wMuxGate, ↓reduceIte, Bool.false_eq_true]
  · rw [muxStNoM2D2PebIpb_lt106 h193 false r41 M z16 β (by omega)]
    unfold potBGateActive
    simp only [Bool.false_eq_true, ↓reduceIte]
    rcases DynCircExt.bit_cases (β (wPotBIsPot r41)) with h | h <;> (rw [h]; decide)
  · unfold muxStNoM2D2PebIpb
    rw [Function.update_of_ne (r41_wire_ne_blk r41 _ (16 : Fin 24) (by
          dsimp [Wtop]
          omega)),
        writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ r41_blk_ne_wire r41 j _ (by
          have := j.isLt
          omega) hj]
    exact muxStNoM2_gate_true h193 r41 M z16 β

theorem muxStNoM2D2PebIpb_pool_zero {Wp M n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n)
    {u : ℕ} (hu18 : 18 ≤ u) (huLtWp : u < Wp)
    (hNoGate : isCsel = false ∨ u ≠ Wp - 1)
    (hNoM1 : u < Wtop Wp isCsel - 48 + M ∨ u = Wtop Wp isCsel - 32 ∨ Wtop Wp isCsel - 24 ≤ u) :
    muxStNoM2D2PebIpb h193 isCsel r41 M z16 β (r41 ⟨122 + u, by omega⟩) = 0 := by
  have hw := wtop_ge192 h193 isCsel
  unfold muxStNoM2D2PebIpb
  by_cases hu32 : u = Wtop Wp isCsel - 32
  · rw [show r41 ⟨122 + u, by omega⟩ = rMuxM1 h193 isCsel r41 16 from
      congrArg r41.wires (Fin.ext (by
        simp only [QRegister.block_apply_val]
        omega)), Function.update_self]
  · rw [Function.update_of_ne (r41_wire_ne_blk r41 _ (16 : Fin 24) (by
          change 122 + u ≠ 122 + Wtop Wp isCsel - 48 + 16
          omega)),
        writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ r41_blk_ne_wire r41 j _ (by
          have := j.isLt
          omega) hj]
    exact muxStNoM2_pool_zero h193 isCsel r41 M z16 β huLtWp hNoGate (by omega)

theorem muxStNoM2D2PebIpb_eq_of_ne_z16 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (M : ℕ) (zA zB : Fin 16 → ZMod 2) (β : BitAssignment n)
    {w : Wire n}
    (hwZ : ∀ j : Fin 16, w ≠ rMuxZ16 r41 j) : muxStNoM2D2PebIpb h193 isCsel r41 M zA β w =
        muxStNoM2D2PebIpb h193 isCsel r41 M zB β w := by
  unfold muxStNoM2D2PebIpb
  simp only [Function.update_apply]
  split_ifs
  · rfl
  · by_cases hwD : ∃ j : Fin 18, rMuxD2_18 h193 r41 j = w
    · obtain ⟨j, rfl⟩ := hwD
      rw [writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ w hwD, writeReg_apply_of_not_mem _ _ _ w hwD]
      exact muxStNoM2_eq_of_ne_z16 h193 isCsel r41 M zA zB β hwZ
def idxMuxCoulPebIpb (Wp : ℕ) (isCsel : Bool) (M : ℕ) (i : ℕ) : ℕ :=
    if i < Wtop Wp isCsel - 48 + M then 122 + i else if i = Wtop Wp isCsel - 48 + M then 122 +
    (Wtop Wp isCsel - 32) else 122 + (i + (23 - M))
theorem idxMuxCoulPebIpb_bounds {Wp M kRest : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (_hM : M ≤ 16)
    (hCap : 54 + kRest + (23 - M) ≤ Wtop Wp isCsel) (i : Fin (54 + kRest)) : 122 ≤
    idxMuxCoulPebIpb Wp isCsel M i.val ∧
    idxMuxCoulPebIpb Wp isCsel M i.val < 122 + Wtop Wp isCsel := by
  have := And.intro (wtop_ge192 h193 isCsel) i.isLt
  unfold idxMuxCoulPebIpb
  split_ifs <;> omega

theorem idxMuxCoulPebIpb_lt {Wp M kRest : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (hM : M ≤ 16)
    (hCap : 54 + kRest + (23 - M) ≤ Wtop Wp isCsel) (i : Fin (54 + kRest)) :
    idxMuxCoulPebIpb Wp isCsel M i.val < 122 + Wp := by
  have := And.intro (idxMuxCoulPebIpb_bounds h193 isCsel hM hCap i) (wtop_le_wp Wp isCsel)
  omega
theorem idxMuxCoulPebIpb_inj {Wp M kRest : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (hM : M ≤ 16)
    (_hCap : 54 + kRest + (23 - M) ≤ Wtop Wp isCsel) : Function.Injective
    (fun i : Fin (54 + kRest) ↦ idxMuxCoulPebIpb Wp isCsel M i.val) := by
  intro a b h
  have := And.intro (wtop_ge192 h193 isCsel) (And.intro a.isLt b.isLt)
  dsimp only [idxMuxCoulPebIpb] at h
  split_ifs at h <;> exact Fin.ext (by omega)

def rMuxCoulPebIpb {Wp M kRest n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool) (hM : M ≤ 16)
    (hCap : 54 + kRest + (23 - M) ≤ Wtop Wp isCsel) (r41 : QRegister (122 + Wp) n) : QRegister (54 +
    kRest) n := r41.compose
    ⟨⟨fun i ↦ ⟨idxMuxCoulPebIpb Wp isCsel M i.val, idxMuxCoulPebIpb_lt h193 isCsel hM hCap i⟩,
        fun _ _ e ↦ idxMuxCoulPebIpb_inj h193 isCsel hM hCap (congrArg Fin.val e)⟩⟩
theorem rMuxCoulPebIpb_apply {Wp M kRest n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hM : M ≤ 16) (hCap : 54 + kRest + (23 - M) ≤ Wtop Wp isCsel)
    (r41 : QRegister (122 + Wp) n) (i : Fin (54 + kRest)) :
    rMuxCoulPebIpb h193 isCsel hM hCap r41 i =
      r41 ⟨idxMuxCoulPebIpb Wp isCsel M i.val, idxMuxCoulPebIpb_lt h193 isCsel hM hCap i⟩ := rfl

theorem rMuxCoulPebIpb_lt_eq {Wp M kRest n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hM : M ≤ 16) (hCap : 54 + kRest + (23 - M) ≤ Wtop Wp isCsel)
    (r41 : QRegister (122 + Wp) n) (i : Fin (54 + kRest))
    (hlt : i.val < Wtop Wp isCsel - 48 + M) :
    rMuxCoulPebIpb h193 isCsel hM hCap r41 i =
      r41 ⟨122 + i.val, by
        have := wtop_ge192 h193 isCsel
        have := wtop_le_wp Wp isCsel
        omega⟩ :=
  congrArg r41.wires (Fin.ext (by
    change idxMuxCoulPebIpb Wp isCsel M i.val = 122 + i.val
    unfold idxMuxCoulPebIpb
    split_ifs; omega))


def pMuxStageBNoM2_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {Wp M kMid tMid tCoul n : ℕ} {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ} (h193 : 193 ≤ Wp)
    (isCsel : Bool) (hM : M ≤ 16)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
        (hCapMid : 54 + kMid + 48 ≤ Wtop Wp isCsel) (hCap : 54 + pkgC.kRest + (23 - M) ≤
        Wtop Wp isCsel) (v : Var) (r41 : QRegister (122 + Wp) n)
    : DynamicCircuit Var n :=
        pkgC.wrap v (wMuxGate h193 isCsel r41) (wPotBIsScreen r41) (wPotBIsNN r41)
        (rMuxCoulPebIpb h193 isCsel hM hCap r41) (rC13Of41 r41)
    (wrapDynOnReg v (rC13Of41 r41) (decodePrimTree 12 whiten13Tree)
        (pkgMid.pMid v (rMuxMid h193 isCsel (Nat.zero_le 24) hCapMid (Nat.le_refl kMid) r41)))
theorem stageB_coul_disj {Wp M kRest n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hM : M ≤ 16) (hCap : 54 + kRest + (23 - M) ≤ Wtop Wp isCsel) (r41 : QRegister (122 + Wp) n) :
    let rCoul := rMuxCoulPebIpb h193 isCsel hM hCap r41
    let rC13 := rC13Of41 r41
    (∀ i, wMuxGate h193 isCsel r41 ≠ rCoul i) ∧
    (∀ j, wMuxGate h193 isCsel r41 ≠ rC13 j) ∧
    (∀ i, wPotBIsScreen r41 ≠ rCoul i) ∧
    (∀ j, wPotBIsScreen r41 ≠ rC13 j) ∧
    (∀ i, wPotBIsNN r41 ≠ rCoul i) ∧
    (∀ j, wPotBIsNN r41 ≠ rC13 j) ∧
    wPotBIsScreen r41 ≠ wPotBIsNN r41 ∧
    rCoul.DisjointWires rC13 := by
  have := And.intro (wtop_ge192 h193 isCsel) (wtop_le_wp Wp isCsel)
  refine ⟨fun i ↦ ?_, fun j ↦ ?_, fun i ↦ ?_,
    fun j ↦ rC13Of41_ne_of_outside r41 _ (Or.inl (by omega)) j,
    fun i ↦ ?_, fun j ↦ rC13Of41_ne_of_outside r41 _ (Or.inl (by omega)) j,
    r41_ne r41 _ _ (by omega), disj_of_ne fun i j ↦ ?_⟩
  · have hb := idxMuxCoulPebIpb_bounds h193 isCsel hM hCap i
    rw [rMuxCoulPebIpb_apply]
    cases isCsel <;> simp only [wMuxGate, Wtop, ↓reduceIte, Bool.false_eq_true] at hb ⊢ <;>
      exact r41_ne r41 _ _ (by omega)
  · cases isCsel <;> simp only [wMuxGate, ↓reduceIte, Bool.false_eq_true]
    · exact rC13Of41_ne_of_outside r41 _ (Or.inl (by omega)) j
    · exact rC13Of41_ne_of_outside r41 _ (Or.inr (by omega)) j
  · have := idxMuxCoulPebIpb_bounds h193 isCsel hM hCap i
    exact r41_ne r41 _ _ (by omega)
  · have := idxMuxCoulPebIpb_bounds h193 isCsel hM hCap i
    exact r41_ne r41 _ _ (by omega)
  · have := idxMuxCoulPebIpb_bounds h193 isCsel hM hCap i
    exact rC13Of41_ne_of_outside r41 _ (Or.inr (by omega)) j

theorem rCoul_pool_zero {Wp M kRest n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hM : M ≤ 16) (hCap : 54 + kRest + (23 - M) ≤ Wtop Wp isCsel)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n)
    (k : Fin (54 + kRest)) (hk18 : 18 ≤ k.val) :
    muxStNoM2D2PebIpb h193 isCsel r41 M z16 β (rMuxCoulPebIpb h193 isCsel hM hCap r41 k) = 0 := by
  have := And.intro (wtop_ge192 h193 isCsel) (And.intro (wtop_le_wp Wp isCsel) k.isLt)
  let m := idxMuxCoulPebIpb Wp isCsel M k.val
  have hm : 140 ≤ m ∧ m < 122 + Wtop Wp isCsel ∧
      (m - 122 < Wtop Wp isCsel - 48 + M ∨ m - 122 = Wtop Wp isCsel - 32 ∨
       Wtop Wp isCsel - 24 ≤ m - 122) := by
    dsimp only [m, idxMuxCoulPebIpb]
    split_ifs <;> omega
  rw [rMuxCoulPebIpb_apply,
      show (⟨m, idxMuxCoulPebIpb_lt h193 isCsel hM hCap k⟩ : Fin (122 + Wp)) =
        ⟨122 + (m - 122), by omega⟩ from Fin.ext (by omega : m = 122 + (m - 122))]
  exact muxStNoM2D2PebIpb_pool_zero h193 isCsel r41 z16 β (by omega) (by omega)
    (noGate_of_lt_wtop isCsel (by omega)) hm.2.2

theorem counts_pMuxStageBNoM2_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {Wp M kMid tMid tCoul n : ℕ} {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp) (isCsel : Bool) (hM : M ≤ 16)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp isCsel)
    (hCap : 54 + pkgC.kRest + (23 - M) ≤ Wtop Wp isCsel)
    (v : Var) (r41 : QRegister (122 + Wp) n) :
    let pB := pMuxStageBNoM2_k2_pebIpb h193 isCsel hM pkgMid pkgC hCapMid hCap v r41
    pB.count .T = tCoul + tMid ∧ pB.count .TOFF = 0 := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := stageB_coul_disj h193 isCsel hM hCap r41
  let rMid := rMuxMid h193 isCsel (Nat.zero_le 24) hCapMid (Nat.le_refl kMid) r41
  let cpW := decodePrimTree 12 whiten13Tree
  have hMidCnt := pkgMid.counts_wires (S := fun _ ↦ True) v rMid (fun _ ↦ trivial)
  obtain ⟨tW, fW⟩ := counts_wrapDynOnReg v (rC13Of41 r41) cpW (pkgMid.pMid v rMid)
  obtain ⟨tC, fC, _⟩ := pkgC.counts_wires (S := fun _ ↦ True) v
    (wMuxGate h193 isCsel r41) (wPotBIsScreen r41) (wPotBIsNN r41)
    (rMuxCoulPebIpb h193 isCsel hM hCap r41) (rC13Of41 r41) d1 d2 d3 d4 d5 d6 d7 d8
    trivial trivial trivial (fun _ ↦ trivial) (fun _ ↦ trivial) _
  unfold pMuxStageBNoM2_k2_pebIpb
  refine ⟨?_, fC.trans (by rw [fW, hMidCnt.2.1])⟩
  rw [tC, tW, (decodePrimTree_spec 12 whiten13Tree 0 0).2.2.trans whiten13Tree_check.2, hMidCnt.1]
  omega

theorem step_pMuxStageBNoM2_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp M kMid tMid tCoul n : ℕ} [NeZero (2 ^ n)]
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp) (isCsel : Bool) (hM : M ≤ 16)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid)
    (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hKMidLE : kMid ≤ pkgC.kMid)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp isCsel)
    (hCap : 54 + pkgC.kRest + (23 - M) ≤ Wtop Wp isCsel)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n)
    (st : BitAssignment n → BitAssignment n)
    (z16L2 : BitAssignment n → Fin 16 → ZMod 2)
    (phL2 : BitAssignment n → ZMod 2)
    (hFlags : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags r41 (st δ)) :
    let z16M := fun δ ↦ z16AfterMidK2 isCsel ySample13 r41 (z16L2 δ) (st δ)
    let phM := fun δ ↦ phAfterMidK2 isCsel ySample13 r41 (z16L2 δ) (phL2 δ) (st δ)
    let pB := pMuxStageBNoM2_k2_pebIpb h193 isCsel hM pkgMid pkgC hCapMid hCap v r41
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ muxStNoM2D2PebIpb h193 isCsel r41 M (z16L2 δ) (st δ)) phL2)
      (mkKetOpW rWork (fun δ ↦ muxStNoM2D2PebIpb h193 isCsel r41 M (z16M δ) (st δ)) phM) pB ∧
    pB.count .T = tCoul + tMid ∧
    pB.count .TOFF = 0 := by
  intro z16M phM
  have := And.intro (wtop_ge192 h193 isCsel) (wtop_le_wp Wp isCsel)
  let rC13 := rC13Of41 r41
  let rCoul := rMuxCoulPebIpb h193 isCsel hM hCap r41
  let rMid := rMuxMid h193 isCsel (Nat.zero_le 24) hCapMid (Nat.le_refl kMid) r41
  let cpW := decodePrimTree 12 whiten13Tree
  rcases decodePrimTree_spec 12 whiten13Tree 0 0 with ⟨hvW, _, haW⟩
  let st₁ := fun δ ↦ muxStNoM2D2PebIpb h193 isCsel r41 M (z16L2 δ) (st δ)
  let st₂ := fun δ ↦ muxStNoM2D2PebIpb h193 isCsel r41 M (z16M δ) (st δ)
  obtain ⟨hwG_ne_coul, hwG_ne_c13, hwScr_ne_coul, hwScr_ne_c13, hwNN_ne_coul, hwNN_ne_c13,
    hwScr_ne_wNN, hCoul_disj_c13⟩ := stageB_coul_disj h193 isCsel hM hCap r41
  have hd2Val (δ) : natOfZModBits 18 (fun b ↦ st₁ δ (rCoul ⟨b.val, potGen_d2_lt pkgC.kRest b⟩)) =
      muxD2Val r41 (st δ) := by
    rw [show (fun b : Fin 18 ↦ st₁ δ (rCoul ⟨b.val, potGen_d2_lt pkgC.kRest b⟩)) =
          fun b ↦
              if (muxD2Val r41 (st δ)).testBit b.val then (1 : ZMod 2) else 0 from funext fun b ↦ by
        rw [rMuxCoulPebIpb_lt_eq h193 isCsel hM hCap r41 ⟨b.val, potGen_d2_lt pkgC.kRest b⟩
              (Nat.lt_of_lt_of_le b.isLt (by omega)),
            show r41 ⟨122 + b.val, _⟩ = rMuxD2_18 h193 r41 b from congrArg r41.wires (Fin.ext rfl)]
        exact muxStNoM2D2PebIpb_d2 h193 isCsel r41 M (z16L2 δ) (st δ) b,
      natOfZModBits_of_testBit 18]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (muxD2Val_le r41 (st δ)) (by norm_num))
  have hc13Wire₁ (δ) (j : Fin 13) : st₁ δ (rC13 j) = st δ (rC13 j) :=
    have := (idxC13Of41_bounds j).2
    muxStNoM2D2PebIpb_lt106 h193 isCsel r41 M (z16L2 δ) (st δ) (by omega)
  have hw11Eq (δ) : w11OfReg13 rC13 (st₁ δ) = w11OfReg13 rC13 (st δ) := by
    simp only [w11OfReg13, hc13Wire₁ δ]
  have hx13Eq (δ) : x13OfReg13 rC13 (st₁ δ) = x13OfReg13 rC13 (st δ) := by
    simp only [x13OfReg13, hc13Wire₁ δ]
  have hscrEq (δ) : st₁ δ (wPotBIsScreen r41) = st δ (wPotBIsScreen r41) :=
    muxStNoM2D2PebIpb_lt106 h193 isCsel r41 M (z16L2 δ) (st δ) (m := 1) (by omega)
  have hnnEq (δ) : st₁ δ (wPotBIsNN r41) = st δ (wPotBIsNN r41) :=
    muxStNoM2D2PebIpb_lt106 h193 isCsel r41 M (z16L2 δ) (st δ) (m := 4) (by omega)
  have heq1 (k : Fin 36) : rMid ⟨5 + k.val, midOW_ltY kMid k⟩ = r41 ⟨122 + (18 + k.val), by omega⟩
      :=
    congrArg r41.wires (Fin.ext (idxMuxMid_y Wp isCsel k))
  have heq2 (k : Fin 36) : rCoul ⟨18 + k.val, potGen_y36_lt pkgC.kRest k⟩ = r41 ⟨122 + (18 + k.val),
      by omega⟩ :=
    rMuxCoulPebIpb_lt_eq h193 isCsel hM hCap r41 ⟨18 + k.val, potGen_y36_lt pkgC.kRest k⟩
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left k.isLt 18) (by omega))
  have hsB : SubspaceStep (mkKetOpW rWork st₁ phL2) (mkKetOpW rWork st₂ phM)
      (pMuxStageBNoM2_k2_pebIpb h193 isCsel hM pkgMid pkgC hCapMid hCap v r41) := by
    refine pkgC.step_phase2 v rWork (wMuxGate h193 isCsel r41) (wPotBIsScreen r41) (wPotBIsNN r41)
      rCoul rC13 hwG_ne_coul hwG_ne_c13 hwScr_ne_coul hwScr_ne_c13 hwNN_ne_coul hwNN_ne_c13
      hwScr_ne_wNN hCoul_disj_c13 (wrapDynOnReg v rC13 cpW (pkgMid.pMid v rMid)) st₁ st₂ phL2 phM
      (fun δ _ ↦ hd2Val δ ▸ muxD2Val_le r41 (st δ))
      (fun δ hz hs0 ↦ hnnEq δ ▸ (hFlags δ hz).2 (hscrEq δ ▸ hs0))
      (fun δ b _ ↦ ⟨rCoul_pool_zero h193 isCsel hM hCap r41 _ _ _ (Nat.le_add_right 18 b.val),
        rCoul_pool_zero h193 isCsel hM hCap r41 _ _ _ (Nat.le_add_right 18 b.val)⟩)
      (fun δ u _ ↦ ⟨rCoul_pool_zero h193 isCsel hM hCap r41 _ _ _ (Nat.le_trans (by decide)
          (Nat.le_add_right 54 u.val)),
        rCoul_pool_zero h193 isCsel hM hCap r41 _ _ _ (Nat.le_trans (by decide)
            (Nat.le_add_right 54 u.val))⟩)
      (fun δ _ ↦ ⟨muxStNoM2D2PebIpb_eq_of_ne_z16 h193 isCsel r41 M _ _ _ fun j ↦ by
          cases isCsel <;> simp only [wMuxGate, ↓reduceIte, Bool.false_eq_true] <;>
              exact r41_wire_ne_blk r41 _ j (by omega),
        muxStNoM2D2PebIpb_eq_of_ne_z16 h193 isCsel r41 M _ _ _ fun j ↦
            r41_wire_ne_blk r41 _ j (by omega),
        muxStNoM2D2PebIpb_eq_of_ne_z16 h193 isCsel r41 M _ _ _ fun j ↦
            r41_wire_ne_blk r41 _ j (by omega),
        fun b ↦ muxStNoM2D2PebIpb_eq_of_ne_z16 h193 isCsel r41 M _ _ _ fun j ↦
          have :=
              And.intro (idxMuxCoulPebIpb_bounds h193 isCsel hM hCap ⟨b.val,
              potGen_d2_lt pkgC.kRest b⟩) j.isLt
          r41_wire_ne_blk r41 _ j (by omega),
        fun j ↦ muxStNoM2D2PebIpb_eq_of_ne_z16 h193 isCsel r41 M _ _ _ fun i ↦
          (rC13Of41_blk_ne_of_outside r41 i (Or.inr (by omega)) j).symm⟩)
      (fun m₁ m₂ hOutside hyV hMidCln hRestEq ↦ ?_)
    have hClnW {stX : BitAssignment n → BitAssignment n} (u : Wire 13)
        (hu : (0 : ℕ).testBit u.val = true)
        (δ) (_ : ∀ k : Fin W, δ (rWork k) = 0) : stX δ (rC13 u) = 0 :=
      absurd (Nat.zero_testBit _ ▸ hu) Bool.false_ne_true
    refine (subspaceStep_wrapOnReg_mkKetOpW_mask2 v rWork rC13 0 cpW 0
      (hvW.trans whiten13Tree_check.1) (haW.trans whiten13Tree_check.2)
      m₁ m₂ phL2 phM (pkgMid.pMid v rMid) hClnW hClnW ?_).1
    set w₁ := fun δ ↦ stepCB rC13 cpW.fwdBits (m₁ δ)
    set w₂ := fun δ ↦ stepCB rC13 cpW.fwdBits (m₂ δ)
    have hmOut (δ) {m : ℕ} (hm : m < 122) :
        m₁ δ (r41 ⟨m, by omega⟩) = st₁ δ (r41 ⟨m, by omega⟩) ∧ m₂ δ (r41 ⟨m, by omega⟩) =
            st₂ δ (r41 ⟨m, by omega⟩) :=
      hOutside δ (r41 ⟨m, by omega⟩)
        (fun b ↦
            have :=
            idxMuxCoulPebIpb_bounds h193 isCsel hM hCap ⟨18 + b.val, potGen_y36_lt pkgC.kRest b⟩
          r41_ne r41 _ _ (by omega))
        (fun u ↦
            have :=
            idxMuxCoulPebIpb_bounds h193 isCsel hM hCap ⟨54 + u.val, potGen_k_lt pkgC.kRest u⟩
          r41_ne r41 _ _ (by omega))
    have hm1Out (δ) {m : ℕ} (hm : m < 122) := (hmOut δ hm).1
    have hw1Out (δ) {m : ℕ} (hm : m < 122 + Wp) (ho : m < 81 ∨ 100 ≤ m) : w₁ δ (r41 ⟨m, hm⟩) =
        m₁ δ (r41 ⟨m, hm⟩) :=
      stepCB_whiten13_out rC13 (m₁ δ) _ (rC13Of41_ne_of_outside r41 hm ho)
    have hw1Gate (δ) : w₁ δ (rMid ⟨0, midOW_lt0 kMid⟩) = st₁ δ (wMuxGate h193 isCsel r41) := by
      rw [show rMid ⟨0, midOW_lt0 kMid⟩ = wMuxGate h193 isCsel r41 by cases isCsel <;> rfl,
          show w₁ δ _ = m₁ δ _ from stepCB_whiten13_out rC13 (m₁ δ) _ hwG_ne_c13]
      exact (hOutside δ _ (fun _ ↦ hwG_ne_coul _) (fun _ ↦ hwG_ne_coul _)).1
    have hx13M1 (δ) : x13OfReg13 rC13 (m₁ δ) = x13OfReg13 rC13 (st δ) := by
      unfold x13OfReg13
      exact congrArg (natOfZModBits 13) (funext fun j ↦
        have := idxC13Of41_bounds j
        (hm1Out δ (m := idxC13Of41 j) (by omega)).trans (hc13Wire₁ δ j))
    have heq41 (j : Fin 16) : rMuxZ16 r41 j = r41 ⟨106 + j.val, by omega⟩ :=
        congrArg r41.wires (Fin.ext rfl)
    have hw1Z (δ) (j : Fin 16) : w₁ δ (rMuxZ16 r41 j) = z16L2 δ j := by
      rw [heq41 j, hw1Out δ (by omega) (Or.inr (by omega)), hm1Out δ (by omega), ← heq41 j]
      exact muxStNoM2D2PebIpb_z16 h193 isCsel r41 M (z16L2 δ) (st δ) j
    have h1 (δ) : w₁ δ (rMid ⟨1, midOW_lt1 kMid⟩) = st δ (wPotBIsScreen r41) :=
      (hw1Out δ (m := 1) (by omega) (Or.inl (by omega))).trans ((hm1Out δ (m := 1)
          (by omega)).trans (hscrEq δ))
    have hSumEq (δ) (hz : ∀ k, δ (rWork k) = 0) :
        midOWTotalSumTap29 rMid w₁ δ = midSumMuxK2 isCsel ySample13 r41 (z16L2 δ) (st δ) := by
      dsimp only [midOWTotalSumTap29, midSumMuxK2]
      have hZ : natOfZModBits 30 (fun i ↦ w₁ δ (rMid ⟨41 + i.val, midOW_ltZ kMid i⟩)) =
          zLo14MuxK2 r41 (st δ) + 2 ^ 14 * finBitsVal (z16L2 δ) := by
        rw [natOfZModBits_split 14 16, natOfZModBits_split 8 6]
        dsimp only
        have hLo8 : (fun b : Fin 8 ↦ w₁ δ (rMid ⟨41 + b.val, midOW_ltZ kMid ⟨b.val, by omega⟩⟩)) =
            fun b ↦
                if (df8Of13 (x13OfReg13 rC13 (st δ))).val.testBit b.val then (1 : ZMod 2) else 0 :=
                funext fun b ↦ by
          by_cases hb7 : b.val < 7
          · rw [show rMid ⟨41 + b.val, _⟩ = rC13 ⟨b.val, by omega⟩ from
                (congrArg r41.wires (Fin.ext (idxMuxMid_zLo Wp isCsel ⟨b.val, by omega⟩))).trans
                  (rC13Of41_lo7 r41 ⟨b.val, hb7⟩).symm]
            dsimp only [w₁, cpW]
            rw [stepCB_whiten13_lo7 rC13 (m₁ δ) ⟨b.val, hb7⟩, hx13M1 δ]
          · have hbEq : b.val = 7 := Nat.le_antisymm (Nat.lt_succ_iff.mp b.isLt) (by omega)
            have hz0 := idxMuxMid_zLo Wp isCsel ⟨b.val, by omega⟩
            dsimp only at hz0
            rw [show rMid ⟨41 + b.val, _⟩ = rC13 ⟨12, by omega⟩ from
                (congrArg r41.wires (Fin.ext (by
                  change idxMuxMid Wp isCsel (41 + b.val) = 99
                  omega))).trans (rC13Of41_12 r41).symm]
            dsimp only [w₁, cpW]
            rw [stepCB_whiten13_hi7 rC13 (m₁ δ), hx13M1 δ, hbEq]
        have hMid6 : (fun i : Fin 6 ↦ w₁ δ (rMid ⟨41 + (8 + i.val), midOW_ltZ kMid ⟨8 + i.val,
            by omega⟩⟩)) =
            fun i ↦ st δ (r41 ⟨100 + i.val, by omega⟩) := funext fun i ↦ by
          have hz0 := idxMuxMid_zLo Wp isCsel ⟨8 + i.val, by omega⟩
          dsimp only at hz0
          rw [show rMid ⟨41 + (8 + i.val), _⟩ = r41 ⟨100 + i.val,
              by omega⟩ from congrArg r41.wires (Fin.ext (by
                change idxMuxMid Wp isCsel (41 + (8 + i.val)) = 100 + i.val
                omega)),
              hw1Out δ (by omega) (Or.inr (by omega)), hm1Out δ (by omega)]
          exact muxStNoM2D2PebIpb_lt106 h193 isCsel r41 M (z16L2 δ) (st δ) (by omega)
        have hHi : (fun j : Fin 16 ↦ w₁ δ (rMid ⟨41 + (14 + j.val), midOW_ltZ kMid ⟨14 + j.val,
            by omega⟩⟩)) = z16L2 δ :=
          funext fun j ↦
              (congrArg (w₁ δ)
              (congrArg r41.wires (Fin.ext (idxMuxMid_zHi Wp isCsel j)))).trans (hw1Z δ j)
        rw [hLo8, natOfZModBits_of_testBit 8,
            Nat.mod_eq_of_lt (show (df8Of13 _).val < 2 ^ 8 from (df8Of13 _).isLt), hMid6, hHi,
            finBitsVal_eq_natOfZModBits 16 (z16L2 δ)]
        rfl
      have hYDiv : natOfZModBits 36 (fun k ↦ w₁ δ (rMid ⟨5 + k.val, midOW_ltY kMid k⟩)) / 8 =
          (y36MuxK2 isCsel ySample13 r41 (st δ) >>>
            (if (st δ (wPotBIsScreen r41) == 1) && !(st δ (wPotBIsNN r41) == 1) then 1 else 0)) /
                8 := by
        rw [show (fun k : Fin 36 ↦ w₁ δ (rMid ⟨5 + k.val, midOW_ltY kMid k⟩)) =
              fun b ↦ m₁ δ (rCoul ⟨18 + b.val, potGen_y36_lt pkgC.kRest b⟩) from
              funext fun k ↦ by rw [heq1 k, heq2 k, hw1Out δ (by omega) (Or.inr (by omega))],
            (hyV δ hz).1]
        unfold y36MuxK2
        rw [show (st₁ δ (wMuxGate h193 isCsel r41) == 1) = potBGateActive isCsel r41 (st δ) by
              dsimp only [st₁]
              rw [muxStNoM2D2PebIpb_gate h193 isCsel r41 M (z16L2 δ) (st δ)]
              cases potBGateActive isCsel r41 (st δ) <;> decide,
            hscrEq δ, hnnEq δ, hd2Val δ, hw11Eq δ, hx13Eq δ]
      rw [h1 δ, hZ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (zLo14MuxK2_lt r41 (st δ)),
          midWTap29_eq_midWTap29OfMode (st δ (wPotBIsScreen r41) == 1)
              (st δ (wPotBIsNN r41) == 1) hYDiv]
    have hsMidRaw := pkgMid.step_mid v rWork rMid w₁ phL2
      (fun j δ hz ↦ by
        let jC : Fin pkgC.kMid := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hKMidLE⟩
        rw [show rMid ⟨71 + j.val, midOW_ltCln kMid j⟩ = r41 ⟨122 + (54 + j.val), by omega⟩ from
              congrArg r41.wires (Fin.ext (idxMuxMid_cln Wp isCsel j.val)),
            hw1Out δ (by omega) (Or.inr (by omega)),
            ← rMuxCoulPebIpb_lt_eq h193 isCsel hM hCap r41 ⟨54 + j.val, potGen_mid_lt pkgC.hKMid jC⟩
                (Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt 54) (by omega))]
        exact (hMidCln δ jC hz).1)
      (fun k δ hz hg0 ↦ by
        rw [hw1Gate δ] at hg0
        rw [heq1 k, hw1Out δ (by omega) (Or.inr (by omega)), ← heq2 k]
        exact (hyV δ hz).2.2 hg0 k)
    refine subspaceStep_of_eq_post hsMidRaw (mkKetOpW_congr rWork (fun δ hz ↦ ?_) (fun δ hz ↦ ?_))
    · unfold midOWPostStTap29
      rw [show pkgMid.hlZ = mux_le14_30 from Subsingleton.elim _ _, rMidZHi_rMuxMid]
      funext w
      by_cases hwZ : ∃ j : Fin 16, rMuxZ16 r41 j = w
      · obtain ⟨j, rfl⟩ := hwZ
        rw [writeReg_apply_reg, show w₂ δ (rMuxZ16 r41 j) = z16M δ j by
          rw [heq41 j]
          dsimp only [w₂, cpW]
          rw [stepCB_whiten13_out rC13 (m₂ δ) _ (rC13Of41_ne_of_outside r41 (by omega)
              (Or.inr (by omega))),
              (hmOut δ (m := 106 + j.val) (by omega)).2, ← heq41 j]
          exact muxStNoM2D2PebIpb_z16 h193 isCsel r41 M (z16M δ) (st δ) j]
        unfold midOWZBitsTap29 z16M z16AfterMidK2
        rw [hw1Gate δ]
        dsimp only [st₁]
        simp only [muxStNoM2D2PebIpb_gate h193 isCsel r41 M (z16L2 δ) (st δ), hSumEq δ hz]
        cases potBGateActive isCsel r41 (st δ)
        · simp only [show ((0 : ZMod 2) == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
          rw [show rMid ⟨41 + 14 + j.val, midOW_ltZHi 14 kMid mux_le14_30 j⟩ = rMuxZ16 r41 j from
            congrArg r41.wires (Fin.ext (idxMuxMid_zHi' Wp isCsel j))]
          exact hw1Z δ j
        · simp only [show ((1 : ZMod 2) == 1) = true by decide, ↓reduceIte]
      · rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ hwZ ⟨j, hj⟩)]
        by_cases hwC13 : ∃ k : Fin 13, rC13 k = w
        · obtain ⟨k, rfl⟩ := hwC13
          dsimp only [w₁, w₂]
          exact cowp_stepCB_eq rC13 cpW.fwdBits (m₁ δ) (m₂ δ)
            (fun q ↦ by
              have hO := hOutside δ (rC13 q)
                (fun b ↦ (disj_ne hCoul_disj_c13 ⟨18 + b.val, potGen_y36_lt pkgC.kRest b⟩ q).symm)
                (fun u ↦ (disj_ne hCoul_disj_c13 ⟨54 + u.val, potGen_k_lt pkgC.kRest u⟩ q).symm)
              rw [hO.1, hO.2]
              exact muxStNoM2D2PebIpb_eq_of_ne_z16 h193 isCsel r41 M _ _ _
                (fun j ↦ (rC13Of41_blk_ne_of_outside r41 j (Or.inr (by omega)) q).symm))
            (rC13 k) (fun hne ↦ absurd rfl (hne k))
        · dsimp only [w₁, w₂, cpW]
          rw [stepCB_whiten13_out rC13 (m₁ δ) w (fun k h ↦ hwC13 ⟨k, h.symm⟩),
              stepCB_whiten13_out rC13 (m₂ δ) w (fun k h ↦ hwC13 ⟨k, h.symm⟩)]
          by_cases hwY : ∃ b : Fin 36, rCoul ⟨18 + b.val, potGen_y36_lt pkgC.kRest b⟩ = w
          · obtain ⟨b, rfl⟩ := hwY
            exact ((hyV δ hz).2.1 b).symm
          · by_cases hwK : ∃ u : Fin pkgC.kRest, rCoul ⟨54 + u.val, potGen_k_lt pkgC.kRest u⟩ = w
            · obtain ⟨u, rfl⟩ := hwK
              exact (hRestEq δ u hz).symm
            · have hO := hOutside δ w (fun b h ↦ hwY ⟨b, h.symm⟩) (fun u h ↦ hwK ⟨u, h.symm⟩)
              rw [hO.1, hO.2]
              exact muxStNoM2D2PebIpb_eq_of_ne_z16 h193 isCsel r41 M _ _ _ (fun j h ↦
                  hwZ ⟨j, h.symm⟩)
    · unfold midOWPhaseTap29 phM phAfterMidK2
      rw [hw1Gate δ]
      dsimp only [st₁]
      rw [muxStNoM2D2PebIpb_gate h193 isCsel r41 M (z16L2 δ) (st δ), hSumEq δ hz, h1 δ]
  exact ⟨hsB, counts_pMuxStageBNoM2_k2_pebIpb h193 isCsel hM pkgMid pkgC hCapMid hCap v r41⟩

theorem dynWires_pMuxStageBNoM2_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {Wp M kMid tMid tCoul n : ℕ} {S : Wire n → Prop} {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hM : M ≤ 16) (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
        (hCapMid : 54 + kMid + 48 ≤ Wtop Wp isCsel) (hCap : 54 + pkgC.kRest + (23 - M) ≤
        Wtop Wp isCsel) (v : Var)
    (r41 : QRegister (122 + Wp) n) (hS : ∀ k, S (r41 k)) :
        DynWires S (pMuxStageBNoM2_k2_pebIpb h193 isCsel hM pkgMid pkgC hCapMid hCap v r41) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := stageB_coul_disj h193 isCsel hM hCap r41
  have hMidW :=
      (pkgMid.counts_wires v (rMuxMid h193 isCsel (Nat.zero_le 24) hCapMid (Nat.le_refl kMid) r41)
      (fun _ ↦ hS _)).2.2
  have hWW :=
      dynWires_wrapDynOnReg v (rC13Of41 r41) (fun _ ↦ hS _) (decodePrimTree 12 whiten13Tree) hMidW
  have hwGS : S (wMuxGate h193 isCsel r41) := by cases isCsel <;> exact hS _
  exact (pkgC.counts_wires v (wMuxGate h193 isCsel r41) (wPotBIsScreen r41) (wPotBIsNN r41)
    (rMuxCoulPebIpb h193 isCsel hM hCap r41) (rC13Of41 r41) d1 d2 d3 d4 d5 d6 d7 d8 hwGS (hS _)
        (hS _)
    (fun _ ↦ hS _) (fun _ ↦ hS _) _).2.2 hWW

theorem toff_pMuxStageBNoM2_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {Wp M kMid tMid tCoul n : ℕ} {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp) (isCsel : Bool) (hM : M ≤ 16)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp isCsel)
    (hCap : 54 + pkgC.kRest + (23 - M) ≤ Wtop Wp isCsel)
    (v : Var) (r41 : QRegister (122 + Wp) n) :
    (pMuxStageBNoM2_k2_pebIpb h193 isCsel hM pkgMid pkgC hCapMid hCap v r41).count .TOFF = 0 :=
  (counts_pMuxStageBNoM2_k2_pebIpb h193 isCsel hM pkgMid pkgC hCapMid hCap v r41).2

attribute [irreducible] pMuxStageBNoM2_k2_pebIpb

theorem pb0_r41Of24_pebIpb {W Wp n : ℕ} (rWork : QRegister W n) (r : QRegister (105 + Wp) n)
    (rCoin : QRegister 17 n) (hd : r.DisjointWires rCoin) {st : BitAssignment n → BitAssignment n}
    (hPB0 : ∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
      st δ (wPotB24IsScreen r) = 0 → st δ (rPotB24PortB r i) = 0) :
    ∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
      st δ (wPotBIsScreen (r41Of24 r rCoin hd)) = 0 →
      st δ (rPotBPortB (r41Of24 r rCoin hd) i) = 0 := fun δ i hz hs ↦ by
  have := i.isLt
  let r41 := r41Of24 r rCoin hd
  rw [show wPotBIsScreen r41 = wPotB24IsScreen r from
    r41Of24_lt81 r rCoin hd (m := 1) (by omega)] at hs
  rw [show rPotBPortB r41 i = rPotB24PortB r i from
    (congrArg r41.wires (Fin.ext rfl)).trans
      ((r41Of24_lt81 r rCoin hd (m := 57 + i.val) (by omega)).trans
        (congrArg r.wires (Fin.ext rfl)).symm)]
  exact hPB0 δ i hz hs


end QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp193K2
end

/-!
# Uniform `k`-Held Stage-4 `Dist18` Split Family (`0 ≤ k ≤ 44`)

Exports `coord48Of`, `Dist18HeldSplitPkg`, and the uniform catalyst-free
prefix-held split family `dist18HeldSplitPkg k hk1 hk44` of type
`Dist18HeldSplitPkg k (141 - k) (546 - 4 * k) (124 - k) (476 - 4 * k)`.
-/

section Dist18P26DualSection
set_option maxRecDepth 200000
namespace QuantumComputation.Specs.PhotochemistrySolution.Dist18P26Dual
set_option exponentiation.threshold 256
open scoped Matrix BigOperators
open Operator QProg Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.Dist18DualGlfaOpt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
  writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18H2Col9Unld
    (subspaceStep_quadCoreLiveGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18P26QuadCol2Unld (pLo12 pPre304_26
    pCarry77_304)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18QuadUnld (hB18_quad quadCoreGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.LegendreFastEval
    (forceNat validProgMask0Fast validProgMask_zero_eq_fast)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Csa36KickStep
    (bennettXorReg_step_of_spec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (openCoordDistSq disj_ne
    disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Word73PotPool (finBitsVal_testBit
    pDitePos pDiteNeg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (stepCB_apply_reg
    stepCB_apply_of_not_mem stepCB_seq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022
    (subspaceStep_wrapOnReg_vprog2_mask subspaceStep_wrapOnReg_zeroAnd pSplitR2EquivK)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (pSplitR2OnReg
    step_counts_wires_splitR2OnReg noWriteK_fwd pKara22 embKaraAx0Fwd)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (embKaraAx1Fwd
    embKaraAx1Unld embKaraAx1Fwd_inj embKaraAx1Unld_inj pOuterAx2_304)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (pOuterAx2_30
    pOuterFwd304 pOuterFwd189 pPrepClean108_189 pInnerFwd189)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (d2WireFwd189
    preInnerFwd189 pGhostFwd189 sMaskInnerFwd189 pPrepClean108_189_certs)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (pInnerFwd189_certs
    sMaskInnerFwd189_ge48 preInnerFwd189_noWrite)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (pGhostFwd189_props
    wsAx0Fwd189 wsAx1Fwd189 wsAx2Fwd189 wsAx0Fwd189_inj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (wsAx1Fwd189_inj
    wsAx2Fwd189_inj zmod2_mut_branch01 zmod2_mut_branch_ax2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (pOuterUnld304
    pOuterUnld172 pPrepClean108_172 pInnerUnld172 preInnerUnld172)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (pGhostP26Unld172
    sMaskInnerUnld172 pPrepClean108_172_certs pInnerUnld172_certs)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022
    (sMaskInnerUnld172_ge48 preInnerUnld172_noWrite dist18P26KaraSha_parity_local)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022
    (czPairsParity_dist18P26KaraShaPairs_aux dist18P26KaraShaPairs)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022
    (dist18P26KaraShaPairs_mem wsAx1Unld172 wsAx2Unld172 wsAx1Unld172_inj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18KaraSplit1022 (wsAx2Unld172_inj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18Sym3Shared552 (fwdBits_bitsOfNT5
    ones512_testBit setNT5_wf bitsOfNT5_set initNT5_22_cps_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18Sym3Shared552 (initNT5_22_wf
    mkIn22_eq_bitsOfNT5 fAx2ShaTo304 mkIn30 mkIn30_eq_bitsOfNT5 f189To304)
-- ============================================================================
-- Section 0: Shared Interface (`coord48Of`, `Dist18HeldSplitPkg`, `k = 0`)
-- ============================================================================

/-- Concatenate two 24-wire coordinate registers `(rA, rB)` into a 48-bit assignment. -/
def coord48Of {n : ℕ} (rA rB : QRegister 24 n) (β : BitAssignment n) : BitAssignment 48 :=
  fun u ↦ if h : u.val < 24 then β (rA ⟨u.val, h⟩) else β (rB ⟨u.val - 24, by omega⟩)

/-- `k`-wire prefix-held `Dist18` forward + unload split package (`0 ≤ k ≤ 44`). -/
structure Dist18HeldSplitPkg (k kScrF tF kScrU tU : ℕ) where
  sMaskHold : ℕ
  pHold : ComputeProg (48 + k)
  pHold_valid : StructuredCB.validProgMask 0 sMaskHold pHold = true
  pHold_numAnd : pHold.numAnd = k
  sMaskHold_ge48 : ∀ u : Wire (48 + k), sMaskHold.testBit u.val = true → 48 ≤ u.val
  pHold_coords : ∀ (γ : BitAssignment (48 + k)) (i : Fin 48),
    pHold.fwdBits γ ⟨i.val, by omega⟩ = γ ⟨i.val, by omega⟩
  progFwd : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ},
    Var → QRegister 24 n → QRegister 24 n → QRegister k n →
      QRegister kScrF n → QRegister 18 n → DynamicCircuit Var n
  progUnld : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ},
    Var → QRegister 24 n → QRegister 24 n → QRegister k n →
      QRegister kScrU n → QRegister 18 n → DynamicCircuit Var n
  step_fwd : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister kScrF n) (rTgt : QRegister 18 n),
    rA.DisjointWires rB → rA.DisjointWires rHold → rA.DisjointWires rScr → rA.DisjointWires rTgt →
    rB.DisjointWires rHold → rB.DisjointWires rScr → rB.DisjointWires rTgt →
    rHold.DisjointWires rScr → rHold.DisjointWires rTgt → rScr.DisjointWires rTgt →
    ∀ (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ δ (u : Fin kScrF), (∀ q : Fin W, δ (rWork q) = 0) → st δ (rScr u) = 0) →
    (∀ δ (j : Fin k), (∀ q : Fin W, δ (rWork q) = 0) →
      st δ (rHold j) = pHold.fwdBits
        (fun u ↦ if h : u.val < 48 then coord48Of rA rB (st δ) ⟨u.val, h⟩ else 0)
        ⟨48 + j.val, by omega⟩) →
    let p := progFwd v rA rB rHold rScr rTgt
    SubspaceStep (mkKetOpW rWork st ph)
      (mkKetOpW rWork (fun δ ↦ writeReg (st δ) rTgt (fun j ↦
        st δ (rTgt j) +
          if (openCoordDistSq (coordOfReg24 rA (st δ)) (coordOfReg24 rB (st δ))).testBit j.val
          then 1 else 0)) ph) p ∧
    p.count .T = tF ∧
    p.count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ i, S (rA i)) → (∀ i, S (rB i)) → (∀ j, S (rHold j)) →
      (∀ u, S (rScr u)) → (∀ j, S (rTgt j)) → DynWires S p)
  step_unld : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister kScrU n) (rTgt : QRegister 18 n),
    rA.DisjointWires rB → rA.DisjointWires rHold → rA.DisjointWires rScr → rA.DisjointWires rTgt →
    rB.DisjointWires rHold → rB.DisjointWires rScr → rB.DisjointWires rTgt →
    rHold.DisjointWires rScr → rHold.DisjointWires rTgt → rScr.DisjointWires rTgt →
    ∀ (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ δ (u : Fin kScrU), (∀ q : Fin W, δ (rWork q) = 0) → st δ (rScr u) = 0) →
    (∀ δ (j : Fin 18), (∀ q : Fin W, δ (rWork q) = 0) → st δ (rTgt j) = 0) →
    (∀ δ (j : Fin k), (∀ q : Fin W, δ (rWork q) = 0) →
      st δ (rHold j) = pHold.fwdBits
        (fun u ↦ if h : u.val < 48 then coord48Of rA rB (st δ) ⟨u.val, h⟩ else 0)
        ⟨48 + j.val, by omega⟩) →
    let p := progUnld v rA rB rHold rScr rTgt
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ writeReg (st δ) rTgt (fun j ↦
        if (openCoordDistSq (coordOfReg24 rA (st δ)) (coordOfReg24 rB (st δ))).testBit j.val
        then 1 else 0)) ph)
      (mkKetOpW rWork st ph) p ∧
    p.count .T = tU ∧
    p.count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ i, S (rA i)) → (∀ i, S (rB i)) → (∀ j, S (rHold j)) →
      (∀ u, S (rScr u)) → (∀ j, S (rTgt j)) → DynWires S p)

theorem hold_st0_eq {k n : ℕ} (pHold : ComputeProg (48 + k))
    {rA rB : QRegister 24 n} {rHold : QRegister k n}
    (dAH : rA.DisjointWires rHold) (dBH : rB.DisjointWires rHold) (j : Fin k) :
    let st0 := writeReg (fun _ : Wire n ↦ (0 : ZMod 2)) rHold
      (fun q ↦ pHold.fwdBits (fun _ ↦ 0) ⟨48 + q.val, by omega⟩)
    st0 (rHold j) = pHold.fwdBits
      (fun u ↦ if h : u.val < 48 then coord48Of rA rB st0 ⟨u.val, h⟩ else 0)
      ⟨48 + j.val, by omega⟩ := by
  dsimp only
  rw [writeReg_apply_reg]
  congr 1
  funext u
  by_cases hu : u.val < 48
  · simp only [hu, ↓reduceDIte, coord48Of]
    split_ifs with h24
    · rw [writeReg_apply_of_not_mem _ rHold _ (rA ⟨u.val, h24⟩)
        (fun ⟨q, hq⟩ ↦ disj_ne dAH _ q hq.symm)]
    · rw [writeReg_apply_of_not_mem _ rHold _ (rB ⟨u.val - 24, by omega⟩)
        (fun ⟨q, hq⟩ ↦ disj_ne dBH _ q hq.symm)]
  · simp only [hu, ↓reduceDIte]

/-- Extract `count` and `DynWires` for `progFwd` without constructing a caller state. -/
theorem Dist18HeldSplitPkg.counts_wires_fwd {k kScrF tF kScrU tU : ℕ}
    (pkg : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister kScrF n) (rTgt : QRegister 18 n)
    (dAB : rA.DisjointWires rB) (dAH : rA.DisjointWires rHold)
    (dAS : rA.DisjointWires rScr) (dAT : rA.DisjointWires rTgt)
    (dBH : rB.DisjointWires rHold) (dBS : rB.DisjointWires rScr) (dBT : rB.DisjointWires rTgt)
    (dHS : rHold.DisjointWires rScr) (dHT : rHold.DisjointWires rTgt)
    (dST : rScr.DisjointWires rTgt) :
    (pkg.progFwd v rA rB rHold rScr rTgt).count .T = tF ∧
    (pkg.progFwd v rA rB rHold rScr rTgt).count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ i, S (rA i)) → (∀ i, S (rB i)) → (∀ j, S (rHold j)) →
      (∀ u, S (rScr u)) → (∀ j, S (rTgt j)) →
      DynWires S (pkg.progFwd v rA rB rHold rScr rTgt)) := by
  have hS := pkg.step_fwd v (QRegExt.empty n) rA rB rHold rScr rTgt
    dAB dAH dAS dAT dBH dBS dBT dHS dHT dST
    (fun _ ↦ writeReg (fun _ ↦ 0) rHold (fun j ↦ pkg.pHold.fwdBits (fun _ ↦ 0)
        ⟨48 + j.val, by omega⟩))
    (fun _ ↦ 0)
    (fun _ u _ ↦ writeReg_apply_of_not_mem _ rHold _ (rScr u) (fun ⟨j, hj⟩ ↦ disj_ne dHS j u hj))
    (fun _ j _ ↦ hold_st0_eq pkg.pHold dAH dBH j)
  exact ⟨hS.2.1, hS.2.2.1, hS.2.2.2⟩

/-- Extract `count` and `DynWires` for `progUnld` without constructing a caller state. -/
theorem Dist18HeldSplitPkg.counts_wires_unld {k kScrF tF kScrU tU : ℕ}
    (pkg : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister kScrU n) (rTgt : QRegister 18 n)
    (dAB : rA.DisjointWires rB) (dAH : rA.DisjointWires rHold)
    (dAS : rA.DisjointWires rScr) (dAT : rA.DisjointWires rTgt)
    (dBH : rB.DisjointWires rHold) (dBS : rB.DisjointWires rScr) (dBT : rB.DisjointWires rTgt)
    (dHS : rHold.DisjointWires rScr) (dHT : rHold.DisjointWires rTgt)
    (dST : rScr.DisjointWires rTgt) :
    (pkg.progUnld v rA rB rHold rScr rTgt).count .T = tU ∧
    (pkg.progUnld v rA rB rHold rScr rTgt).count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ i, S (rA i)) → (∀ i, S (rB i)) → (∀ j, S (rHold j)) →
      (∀ u, S (rScr u)) → (∀ j, S (rTgt j)) →
      DynWires S (pkg.progUnld v rA rB rHold rScr rTgt)) := by
  have hS := pkg.step_unld v (QRegExt.empty n) rA rB rHold rScr rTgt
    dAB dAH dAS dAT dBH dBS dBT dHS dHT dST
    (fun _ ↦ writeReg (fun _ ↦ 0) rHold (fun j ↦ pkg.pHold.fwdBits (fun _ ↦ 0)
        ⟨48 + j.val, by omega⟩))
    (fun _ ↦ 0)
    (fun _ u _ ↦ writeReg_apply_of_not_mem _ rHold _ (rScr u) (fun ⟨j, hj⟩ ↦ disj_ne dHS j u hj))
    (fun _ j _ ↦ writeReg_apply_of_not_mem _ rHold _ (rTgt j) (fun ⟨q, hq⟩ ↦ disj_ne dHT q j hq))
    (fun _ j _ ↦ hold_st0_eq pkg.pHold dAH dBH j)
  exact ⟨hS.2.1, hS.2.2.1, hS.2.2.2⟩


-- ============================================================================
-- Section 1: Generic `GateN` Compiler, Disjoint Commutation, and Undo/Redo
-- ============================================================================

/-- Boolean equality on `GateN`. -/
def beqGateN : GateN → GateN → Bool
  | .x u1, .x u2 => u1 == u2
  | .cnot c1 t1, .cnot c2 t2 => (c1 == c2) && (t1 == t2)
  | .andGate a1 b1 c1, .andGate a2 b2 c2 => (a1 == a2) && (b1 == b2) && (c1 == c2)
  | _, _ => false

theorem beqGateN_eq : ∀ {g1 g2 : GateN}, beqGateN g1 g2 = true → g1 = g2
  | .x u1, .x u2, h => congrArg GateN.x (beq_iff_eq.mp h)
  | .cnot c1 t1, .cnot c2 t2, h => by
      simp only [beqGateN, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, h.2]
  | .andGate a1 b1 c1, .andGate a2 b2 c2, h => by
      simp only [beqGateN, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, h.1.2, h.2]
  | .x _, .cnot _ _, h | .x _, .andGate _ _ _, h
  | .cnot _ _, .x _, h | .cnot _ _, .andGate _ _ _, h
  | .andGate _ _ _, .x _, h | .andGate _ _ _, .cnot _ _, h => Bool.noConfusion h

/-- Boolean equality on `List GateN`. -/
def beqGateList : List GateN → List GateN → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqGateN x y && beqGateList xs ys
  | _, _ => false

theorem beqGateList_eq : ∀ {xs ys : List GateN}, beqGateList xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [beqGateList, Bool.and_eq_true] at h
      rw [beqGateN_eq h.1, beqGateList_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => Bool.noConfusion h

/-- Compile a single `GateN` into `ComputeProg M`. -/
def gateToCP {M : ℕ} (hM : 0 < M) : GateN → ComputeProg M
  | .x u => .x ⟨u % M, Nat.mod_lt u hM⟩
  | .cnot c t => safeCnotCP ⟨c % M, Nat.mod_lt c hM⟩ ⟨t % M, Nat.mod_lt t hM⟩
  | .andGate a b c =>
      safeAndGateCP ⟨a % M, Nat.mod_lt a hM⟩ ⟨b % M, Nat.mod_lt b hM⟩ ⟨c % M, Nat.mod_lt c hM⟩

/-- Compile a `List GateN` into `ComputeProg M`. -/
def gatesToCP {M : ℕ} (hM : 0 < M) : List GateN → ComputeProg M
  | [] => .id
  | g :: gs => .seq (gateToCP hM g) (gatesToCP hM gs)

theorem gatesToCP_append {M : ℕ} (hM : 0 < M) :
    ∀ (xs ys : List GateN) (γ : BitAssignment M),
      (gatesToCP hM (xs ++ ys)).fwdBits γ =
        (gatesToCP hM ys).fwdBits ((gatesToCP hM xs).fwdBits γ)
  | [], _, _ => rfl
  | g :: gs, ys, γ => gatesToCP_append hM gs ys ((gateToCP hM g).fwdBits γ)

theorem wire_mod_self {M : ℕ} (hM : 0 < M) (w : Wire M) :
    (⟨w.val % M, Nat.mod_lt w.val hM⟩ : Wire M) = w :=
  Fin.ext (Nat.mod_eq_of_lt w.isLt)

theorem toGatesNAux_gatesToCP {M : ℕ} (hM : 0 < M) :
    ∀ (p : ComputeProg M) (acc : List GateN) (γ : BitAssignment M),
      (gatesToCP hM (toGatesNAux p acc)).fwdBits γ =
        (gatesToCP hM acc).fwdBits (p.fwdBits γ)
  | .id, _, _ => rfl
  | .x u, acc, γ => by
      dsimp only [toGatesNAux, gatesToCP, gateToCP, ComputeProg.fwdBits]
      rw [wire_mod_self hM u]
  | .cnot c t hct, acc, γ => by
      dsimp only [toGatesNAux, gatesToCP, gateToCP, ComputeProg.fwdBits]
      rw [wire_mod_self hM c, wire_mod_self hM t]
      dsimp only [safeCnotCP]
      rw [leg_dif_neg hct]
      rfl
  | .andGate a b c hab hac hbc, acc, γ => by
      dsimp only [toGatesNAux, gatesToCP, gateToCP, ComputeProg.fwdBits]
      rw [wire_mod_self hM a, wire_mod_self hM b, wire_mod_self hM c]
      dsimp only [safeAndGateCP]
      rw [leg_dif_neg hab, leg_dif_neg hac, leg_dif_neg hbc]
      rfl
  | .seq p q, acc, γ => by
      dsimp only [toGatesNAux, ComputeProg.fwdBits]
      rw [toGatesNAux_gatesToCP hM p (toGatesNAux q acc) γ,
          toGatesNAux_gatesToCP hM q acc (p.fwdBits γ)]

theorem eq_fwdBits_of_toGates {M : ℕ} (hM : 0 < M) {p q : ComputeProg M}
    (h : toGatesNAux p [] = toGatesNAux q []) (γ : BitAssignment M) :
    p.fwdBits γ = q.fwdBits γ := by
  have hp := toGatesNAux_gatesToCP hM p [] γ
  have hq := toGatesNAux_gatesToCP hM q [] γ
  dsimp only [gatesToCP, ComputeProg.fwdBits] at hp hq
  rw [← hp, h, hq]

/-- Remap wire indices in a `GateN`. -/
def mapGateN (fn : ℕ → ℕ) : GateN → GateN
  | .x u => .x (fn u)
  | .cnot c t => .cnot (fn c) (fn t)
  | .andGate a b c => .andGate (fn a) (fn b) (fn c)

/-- Well-formedness of a `GateN` on `M` wires. -/
def wfGateN (M : ℕ) : GateN → Bool
  | .x u => Nat.blt u M
  | .cnot c t => Nat.blt c M && Nat.blt t M && (c != t)
  | .andGate a b c => Nat.blt a M && Nat.blt b M && Nat.blt c M && (a != b) && (a != c) && (b != c)

/-- Target wire index of a `GateN`. -/
def gateTarget : GateN → ℕ
  | .x u => u
  | .cnot _ t => t
  | .andGate _ _ c => c

/-- XOR increment evaluated by a `GateN`. -/
def gateVal {M : ℕ} (hM : 0 < M) (g : GateN) (γ : BitAssignment M) : ZMod 2 :=
  match g with
  | .x _ => 1
  | .cnot c _ => γ ⟨c % M, Nat.mod_lt c hM⟩
  | .andGate a b _ => γ ⟨a % M, Nat.mod_lt a hM⟩ * γ ⟨b % M, Nat.mod_lt b hM⟩

theorem wireMod_ne {M a b : ℕ} (hM : 0 < M) (ha : a < M) (hb : b < M) (hne : a ≠ b) :
    (⟨a % M, Nat.mod_lt a hM⟩ : Wire M) ≠ ⟨b % M, Nat.mod_lt b hM⟩ := fun e ↦ hne (by
  have hv := congrArg Fin.val e
  dsimp at hv
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv)

theorem wireMod_ne_fin {M a : ℕ} (hM : 0 < M) (ha : a < M) {w : Wire M} (hne : a ≠ w.val) :
    (⟨a % M, Nat.mod_lt a hM⟩ : Wire M) ≠ w := fun e ↦ hne (by
  have hv := congrArg Fin.val e
  dsimp at hv
  rwa [Nat.mod_eq_of_lt ha] at hv)

theorem gateToCP_eq_update {M : ℕ} (hM : 0 < M) {g : GateN}
    (hwf : wfGateN M g = true) (γ : BitAssignment M) :
    (gateToCP hM g).fwdBits γ =
      Function.update γ ⟨gateTarget g % M, Nat.mod_lt _ hM⟩
        (γ ⟨gateTarget g % M, Nat.mod_lt _ hM⟩ + gateVal hM g γ) := by
  cases g with
  | x u => rfl
  | cnot c t =>
      simp only [wfGateN, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne] at hwf
      dsimp only [gateToCP, safeCnotCP, gateTarget, gateVal]
      rw [leg_dif_neg (wireMod_ne hM hwf.1.1 hwf.1.2 hwf.2)]
      rfl
  | andGate a b c =>
      simp only [wfGateN, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne] at hwf
      obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hac⟩, hbc⟩ := hwf
      dsimp only [gateToCP, safeAndGateCP, gateTarget, gateVal]
      rw [leg_dif_neg (wireMod_ne hM ha hb hab), leg_dif_neg (wireMod_ne hM ha hc hac),
          leg_dif_neg (wireMod_ne hM hb hc hbc)]
      rfl

/-- Check if wire index `w` appears anywhere in `g`. -/
def gateTouches (w : ℕ) : GateN → Bool
  | .x u => u == w
  | .cnot c t => (c == w) || (t == w)
  | .andGate a b c => (a == w) || (b == w) || (c == w)

theorem gateTarget_lt {M : ℕ} {g : GateN} (hwf : wfGateN M g = true) : gateTarget g < M := by
  cases g <;> simp only [wfGateN, gateTarget, Bool.and_eq_true, Nat.blt_eq] at hwf ⊢
  · exact hwf
  · exact hwf.1.2
  · exact hwf.1.1.1.2

theorem gateTouches_target (g : GateN) : gateTouches (gateTarget g) g = true := by
  cases g <;> simp [gateTouches, gateTarget]

/-- Pairwise wire-disjointness of two `GateN`s. -/
def disjGatePair (g1 : GateN) (g2 : GateN) : Bool :=
  match g1 with
  | .x u => !gateTouches u g2
  | .cnot c t => !gateTouches c g2 && !gateTouches t g2
  | .andGate a b c => !gateTouches a g2 && !gateTouches b g2 && !gateTouches c g2

theorem disjGatePair_not_touches {g1 g2 : GateN} (hd : disjGatePair g1 g2 = true) :
    gateTouches (gateTarget g1) g2 = false ∧ gateTouches (gateTarget g2) g1 = false := by
  refine ⟨?_, ?_⟩
  · cases g1 <;> simp only [disjGatePair, Bool.and_eq_true, Bool.not_eq_true'] at hd
    · exact hd
    · exact hd.2
    · exact hd.2
  · by_contra h
    have ht : gateTouches (gateTarget g2) g1 = true := Bool.eq_true_of_not_eq_false h
    have hg2 := gateTouches_target g2
    cases g1 <;> simp only [disjGatePair, gateTouches, Bool.or_eq_true, Bool.and_eq_true,
        Bool.not_eq_true', beq_iff_eq] at ht hd
    · rw [ht] at hd
      exact Bool.noConfusion (hd.symm.trans hg2)
    · rcases ht with rfl | rfl
      · exact Bool.noConfusion (hd.1.symm.trans hg2)
      · exact Bool.noConfusion (hd.2.symm.trans hg2)
    · rcases ht with (rfl | rfl) | rfl
      · exact Bool.noConfusion (hd.1.1.symm.trans hg2)
      · exact Bool.noConfusion (hd.1.2.symm.trans hg2)
      · exact Bool.noConfusion (hd.2.symm.trans hg2)

theorem gateComm_of_disj {M : ℕ} (hM : 0 < M) {g1 g2 : GateN}
    (hw1 : wfGateN M g1 = true) (hw2 : wfGateN M g2 = true)
    (hd : disjGatePair g1 g2 = true) (γ : BitAssignment M) :
    (gateToCP hM g2).fwdBits ((gateToCP hM g1).fwdBits γ) =
      (gateToCP hM g1).fwdBits ((gateToCP hM g2).fwdBits γ) := by
  have gateVal_update_of_not_touches {g : GateN} (hwf : wfGateN M g = true) {w : Wire M}
      {x : ZMod 2} (hnt : gateTouches w.val g = false) (γ : BitAssignment M) :
      gateVal hM g (Function.update γ w x) = gateVal hM g γ := by
    cases g with
    | x _ => rfl
    | cnot c t =>
        simp only [wfGateN, Bool.and_eq_true, Nat.blt_eq] at hwf
        simp only [gateTouches, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnt
        dsimp only [gateVal]
        rw [Function.update_of_ne (wireMod_ne_fin hM hwf.1.1 hnt.1)]
    | andGate a b c =>
        simp only [wfGateN, Bool.and_eq_true, Nat.blt_eq] at hwf
        simp only [gateTouches, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnt
        dsimp only [gateVal]
        rw [Function.update_of_ne (wireMod_ne_fin hM hwf.1.1.1.1.1 hnt.1.1),
            Function.update_of_ne (wireMod_ne_fin hM hwf.1.1.1.1.2 hnt.1.2)]
  obtain ⟨nt12, nt21⟩ := disjGatePair_not_touches hd
  let w1 : Wire M := ⟨gateTarget g1 % M, Nat.mod_lt _ hM⟩
  let w2 : Wire M := ⟨gateTarget g2 % M, Nat.mod_lt _ hM⟩
  have hw1v : w1.val = gateTarget g1 := Nat.mod_eq_of_lt (gateTarget_lt hw1)
  have hw2v : w2.val = gateTarget g2 := Nat.mod_eq_of_lt (gateTarget_lt hw2)
  have hne : w1 ≠ w2 := fun e ↦ Bool.noConfusion
    (((hw1v.symm.trans ((congrArg Fin.val e).trans hw2v)) ▸ nt12).symm.trans (gateTouches_target
        g2))
  rw [gateToCP_eq_update hM hw1 γ, gateToCP_eq_update hM hw2,
      gateToCP_eq_update hM hw2 γ, gateToCP_eq_update hM hw1]
  change Function.update (Function.update γ w1 (γ w1 + gateVal hM g1 γ)) w2
      (Function.update γ w1 (γ w1 + gateVal hM g1 γ) w2 +
        gateVal hM g2 (Function.update γ w1 (γ w1 + gateVal hM g1 γ))) =
    Function.update (Function.update γ w2 (γ w2 + gateVal hM g2 γ)) w1
      (Function.update γ w2 (γ w2 + gateVal hM g2 γ) w1 +
        gateVal hM g1 (Function.update γ w2 (γ w2 + gateVal hM g2 γ)))
  rw [Function.update_of_ne hne.symm, Function.update_of_ne hne,
      gateVal_update_of_not_touches hw2 (hw1v.symm ▸ nt12),
      gateVal_update_of_not_touches hw1 (hw2v.symm ▸ nt21), Function.update_comm hne]

/-- Wire-disjointness of two gate lists. -/
def disjLists (xs ys : List GateN) : Bool :=
  xs.all fun x ↦ ys.all fun y ↦ disjGatePair x y

theorem gate_comm_list {M : ℕ} (hM : 0 < M) {g : GateN} (hg : wfGateN M g = true) :
    ∀ (ys : List GateN), ys.all (wfGateN M) = true → (ys.all (disjGatePair g)) = true →
      ∀ (γ : BitAssignment M),
        (gatesToCP hM ys).fwdBits ((gateToCP hM g).fwdBits γ) =
          (gateToCP hM g).fwdBits ((gatesToCP hM ys).fwdBits γ)
  | [], _, _, _ => rfl
  | y :: ys, hwy, hdy, γ => by
      simp only [List.all_cons, Bool.and_eq_true] at hwy hdy
      dsimp only [gatesToCP, ComputeProg.fwdBits]
      rw [gateComm_of_disj hM hg hwy.1 hdy.1 γ,
          gate_comm_list hM hg ys hwy.2 hdy.2 ((gateToCP hM y).fwdBits γ)]

theorem disjLists_comm {M : ℕ} (hM : 0 < M) :
    ∀ (xs ys : List GateN), xs.all (wfGateN M) = true → ys.all (wfGateN M) = true →
      disjLists xs ys = true →
      ∀ (γ : BitAssignment M),
        (gatesToCP hM (xs ++ ys)).fwdBits γ = (gatesToCP hM (ys ++ xs)).fwdBits γ
  | [], _, _, _, _, _ => by simp only [List.nil_append, List.append_nil]
  | x :: xs, ys, hwx, hwy, hd, γ => by
      simp only [List.all_cons, disjLists, Bool.and_eq_true] at hwx hd
      simp only [List.cons_append]
      dsimp only [gatesToCP, ComputeProg.fwdBits]
      rw [disjLists_comm hM xs ys hwx.2 hwy hd.2 ((gateToCP hM x).fwdBits γ),
          gatesToCP_append hM ys xs ((gateToCP hM x).fwdBits γ),
          gatesToCP_append hM ys (x :: xs) γ]
      dsimp only [gatesToCP, ComputeProg.fwdBits]
      rw [gate_comm_list hM hwx.1 ys hwy hd.1 γ]

theorem gatesToCP_comm_mid {M : ℕ} (hM : 0 < M) (pre xs ys suf : List GateN)
    (hwfx : xs.all (wfGateN M) = true) (hwfy : ys.all (wfGateN M) = true)
    (hd : disjLists xs ys = true) (γ : BitAssignment M) :
    (gatesToCP hM (pre ++ (xs ++ (ys ++ suf)))).fwdBits γ =
      (gatesToCP hM (pre ++ (ys ++ (xs ++ suf)))).fwdBits γ := by
  rw [← List.append_assoc xs ys suf, ← List.append_assoc ys xs suf]
  rw [gatesToCP_append hM pre, gatesToCP_append hM pre]
  rw [gatesToCP_append hM (xs ++ ys), gatesToCP_append hM (ys ++ xs)]
  rw [disjLists_comm hM xs ys hwfx hwfy hd]

theorem map_wireMod_eq {N M u : ℕ} (hN : 0 < N) (hM : 0 < M)
    (f : Fin N → Wire M) (fn : ℕ → ℕ) (hfn : ∀ i : Fin N, (f i).val = fn i.val) (hu : u < N) :
    (⟨fn u % M, Nat.mod_lt _ hM⟩ : Wire M) = f ⟨u % N, Nat.mod_lt u hN⟩ := by
  apply Fin.ext
  dsimp
  rw [hfn ⟨u % N, Nat.mod_lt u hN⟩]
  dsimp
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt]
  have hlt := (f ⟨u, hu⟩).isLt
  have he := hfn ⟨u, hu⟩
  dsimp at he
  omega

theorem mapCP_gatesToCP_eq {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (f : Fin N → Wire M) (fn : ℕ → ℕ) (hfn : ∀ i : Fin N, (f i).val = fn i.val) :
    ∀ (gs : List GateN), gs.all (wfGateN N) = true →
      mapCP f (gatesToCP hN gs) = gatesToCP hM (gs.map (mapGateN fn))
  | [], _ => rfl
  | g :: gs, hwf => by
      simp only [List.all_cons, Bool.and_eq_true] at hwf
      dsimp only [gatesToCP, List.map, mapCP]
      refine congrArg₂ ComputeProg.seq ?_ (mapCP_gatesToCP_eq hN hM f fn hfn gs hwf.2)
      cases g with
      | x u =>
          simp only [wfGateN, Nat.blt_eq] at hwf
          exact congrArg ComputeProg.x (map_wireMod_eq hN hM f fn hfn hwf.1).symm
      | cnot c t =>
          simp only [wfGateN, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne] at hwf
          dsimp only [gateToCP, safeCnotCP, mapGateN]
          rw [leg_dif_neg (wireMod_ne hN hwf.1.1.1 hwf.1.1.2 hwf.1.2)]
          dsimp only [mapCP, safeCnotCP]
          rw [map_wireMod_eq hN hM f fn hfn hwf.1.1.1, map_wireMod_eq hN hM f fn hfn hwf.1.1.2]
      | andGate a b c =>
          simp only [wfGateN, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne] at hwf
          obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hac⟩, hbc⟩ := hwf.1
          dsimp only [gateToCP, safeAndGateCP, mapGateN]
          rw [leg_dif_neg (wireMod_ne hN ha hb hab), leg_dif_neg (wireMod_ne hN ha hc hac),
              leg_dif_neg (wireMod_ne hN hb hc hbc)]
          dsimp only [mapCP, safeAndGateCP]
          rw [map_wireMod_eq hN hM f fn hfn ha, map_wireMod_eq hN hM f fn hfn hb,
              map_wireMod_eq hN hM f fn hfn hc]

/-- Well-formed Clifford (`x` / `cnot`) gate check on `M` wires. -/
def isCliffWf (M : ℕ) : GateN → Bool
  | .x u => Nat.blt u M
  | .cnot c t => Nat.blt c M && Nat.blt t M && (c != t)
  | .andGate _ _ _ => false

theorem zmod2_self_cancel : ∀ a b : ZMod 2, a + b + b = a := by decide

theorem zmod2_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem gateToCP_involution {M : ℕ} (hM : 0 < M) {g : GateN}
    (hg : isCliffWf M g = true) (γ : BitAssignment M) :
    (gateToCP hM g).fwdBits ((gateToCP hM g).fwdBits γ) = γ := by
  cases g with
  | x u =>
      dsimp only [gateToCP, ComputeProg.fwdBits]
      funext w
      by_cases hw : w = ⟨u % M, Nat.mod_lt u hM⟩
      · subst hw
        rw [Function.update_self, Function.update_self]
        exact zmod2_self_cancel _ 1
      · rw [Function.update_of_ne hw, Function.update_of_ne hw]
  | cnot c t =>
      simp only [isCliffWf, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne] at hg
      have hne := wireMod_ne hM hg.1.1 hg.1.2 hg.2
      dsimp only [gateToCP, safeCnotCP]
      rw [leg_dif_neg hne]
      dsimp only [ComputeProg.fwdBits]
      funext w
      by_cases hw : w = ⟨t % M, Nat.mod_lt t hM⟩
      · subst hw
        rw [Function.update_self, Function.update_of_ne hne, Function.update_self]
        exact zmod2_self_cancel _ _
      · rw [Function.update_of_ne hw, Function.update_of_ne hw]
  | andGate _ _ _ => cases hg

theorem cliff_redo_cancel {M : ℕ} (hM : 0 < M) :
    ∀ (us : List GateN), us.all (isCliffWf M) = true →
      ∀ (γ : BitAssignment M),
        (gatesToCP hM us.reverse).fwdBits ((gatesToCP hM us).fwdBits γ) = γ
  | [], _, _ => rfl
  | g :: gs, hus, γ => by
      simp only [List.all_cons, Bool.and_eq_true] at hus
      simp only [List.reverse_cons, gatesToCP_append]
      dsimp only [gatesToCP, ComputeProg.fwdBits]
      rw [cliff_redo_cancel hM gs hus.2 ((gateToCP hM g).fwdBits γ),
          gateToCP_involution hM hus.1 γ]

/-- Check if a `GateN` writes to a coordinate wire `< 48`. -/
def writesLt48 : GateN → Bool
  | .x u => Nat.blt u 48
  | .cnot _ t => Nat.blt t 48
  | .andGate _ _ _ => false

/-- Check that `w % M` is never written by `gs`. -/
def noWriteGN (M w : ℕ) : List GateN → Bool
  | [] => true
  | g :: gs => (gateTarget g % M != w % M) && noWriteGN M w gs

theorem noWriteGN_append (M w : ℕ) :
    ∀ (xs ys : List GateN), noWriteGN M w xs = true → noWriteGN M w ys = true →
      noWriteGN M w (xs ++ ys) = true
  | [], _, _, hy => hy
  | _ :: xs, ys, hx, hy => by
      simp only [List.cons_append, noWriteGN, Bool.and_eq_true] at hx ⊢
      exact ⟨hx.1, noWriteGN_append M w xs ys hx.2 hy⟩

theorem noWriteGN_fwd {M : ℕ} (hM : 0 < M) (w : Wire M) :
    ∀ (gs : List GateN), gs.all (wfGateN M) = true → noWriteGN M w.val gs = true →
      ∀ (γ : BitAssignment M), (gatesToCP hM gs).fwdBits γ w = γ w
  | [], _, _, _ => rfl
  | g :: gs, hwf, hnw, γ => by
      simp only [List.all_cons, noWriteGN, Bool.and_eq_true, bne_iff_ne] at hwf hnw
      dsimp only [gatesToCP, ComputeProg.fwdBits]
      rw [noWriteGN_fwd hM w gs hwf.2 hnw.2, gateToCP_eq_update hM hwf.1 γ]
      have hne : w ≠ ⟨gateTarget g % M, Nat.mod_lt _ hM⟩ := fun e ↦ hnw.1 (by
        have hv := congrArg Fin.val e.symm
        dsimp at hv
        rw [hv, Nat.mod_eq_of_lt w.isLt])
      rw [Function.update_of_ne hne]

/-- Reverse Clifford undo list on `< 48` coordinate wires. -/
def undoLt48 (gs : List GateN) : List GateN :=
  (gs.filter writesLt48).reverse

theorem undoLt48_wf {M : ℕ} :
    ∀ (gs : List GateN), gs.all (wfGateN M) = true → (undoLt48 gs).all (wfGateN M) = true := by
  intro gs hwf
  dsimp only [undoLt48]
  rw [List.all_reverse]
  induction gs with
  | nil => rfl
  | cons g rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hwf
      dsimp only [List.filter]
      cases writesLt48 g <;> simp [hwf.1, ih hwf.2]

theorem undoLt48_noWrite_ge48 {M w : ℕ} (hM : 48 ≤ M) (hw : 48 ≤ w) (hwlt : w < M) :
    ∀ (gs : List GateN), gs.all (wfGateN M) = true → noWriteGN M w (undoLt48 gs) = true
  | [], _ => rfl
  | g :: rest, hwf => by
      simp only [List.all_cons, Bool.and_eq_true] at hwf
      dsimp only [undoLt48, List.filter]
      cases hlt : writesLt48 g
      · exact undoLt48_noWrite_ge48 hM hw hwlt rest hwf.2
      · rw [List.reverse_cons]
        refine noWriteGN_append M w (undoLt48 rest) [g]
          (undoLt48_noWrite_ge48 hM hw hwlt rest hwf.2) ?_
        simp only [noWriteGN, Bool.and_true, bne_iff_ne]
        have hgt : gateTarget g < 48 := by
          cases g with
          | x u => exact Nat.blt_eq.mp hlt
          | cnot c t => exact Nat.blt_eq.mp hlt
          | andGate a b c => cases hlt
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hwlt]
        omega

/-- Structural check ensuring `gs ++ undoLt48 gs` restores all `< 48` wires. -/
def okHoldGN (M : ℕ) : List GateN → Bool
  | [] => true
  | g :: rest =>
      wfGateN M g &&
      (match g with
       | .x _ => true
       | .cnot c t => !(Nat.blt t 48) || (Nat.blt c 48 || noWriteGN M c rest)
       | .andGate _ _ a => !Nat.blt a 48) &&
      okHoldGN M rest

theorem okHoldGN_wf {M : ℕ} :
    ∀ (gs : List GateN), okHoldGN M gs = true → gs.all (wfGateN M) = true
  | [], _ => rfl
  | _ :: rest, hok => by
      simp only [okHoldGN, List.all_cons, Bool.and_eq_true] at hok ⊢
      exact ⟨hok.1.1, okHoldGN_wf rest hok.2⟩

theorem exec_append_undo_coords {M : ℕ} (hM : 48 ≤ M) :
    ∀ (gs : List GateN), okHoldGN M gs = true →
      ∀ (γ : BitAssignment M) (i : Fin 48),
        (gatesToCP (by omega) (gs ++ undoLt48 gs)).fwdBits γ ⟨i.val, by omega⟩ =
          γ ⟨i.val, by omega⟩
  | [], _, _, _ => rfl
  | g :: rest, hok, γ, i => by
      have hM0 : 0 < M := by omega
      simp only [okHoldGN, Bool.and_eq_true] at hok
      obtain ⟨⟨hwfg, hcond⟩, hokr⟩ := hok
      let γ1 := (gateToCP hM0 g).fwdBits γ
      let γ2 := (gatesToCP hM0 (rest ++ undoLt48 rest)).fwdBits γ1
      have hγ1 : γ1 = (gateToCP hM0 g).fwdBits γ := rfl
      have ih : ∀ j : Fin 48, γ2 ⟨j.val, by omega⟩ = γ1 ⟨j.val, by omega⟩ :=
        exec_append_undo_coords hM rest hokr γ1
      simp only [List.cons_append]
      dsimp only [gatesToCP, ComputeProg.fwdBits]
      cases hlt : writesLt48 g
      · dsimp only [undoLt48, List.filter]
        rw [hlt]
        change γ2 ⟨i.val, by omega⟩ = γ ⟨i.val, by omega⟩
        rw [ih i, hγ1, gateToCP_eq_update hM0 hwfg γ]
        have : 48 ≤ gateTarget g := by
          by_contra h
          have : Nat.blt (gateTarget g) 48 = true := Nat.blt_eq.mpr (by omega)
          cases g <;> simp_all only [writesLt48, gateTarget, Bool.not_eq_true', Bool.false_eq_true]
        refine Function.update_of_ne (fun e ↦ ?_) _ _
        have hv := congrArg Fin.val e
        dsimp at hv
        rw [Nat.mod_eq_of_lt (gateTarget_lt hwfg)] at hv
        omega
      · rw [show undoLt48 (g :: rest) = undoLt48 rest ++ [g] by
              dsimp only [undoLt48, List.filter]
              rw [hlt, List.reverse_cons],
            ← List.append_assoc, gatesToCP_append hM0 (rest ++ undoLt48 rest) [g] γ1]
        change (gatesToCP hM0 [g]).fwdBits γ2 ⟨i.val, by omega⟩ = γ ⟨i.val, by omega⟩
        dsimp only [gatesToCP, ComputeProg.fwdBits]
        rw [gateToCP_eq_update hM0 hwfg γ2]
        have hgt48 : gateTarget g < 48 := by cases g <;> first | exact Nat.blt_eq.mp hlt | cases hlt
        let wt : Wire M := ⟨gateTarget g % M, Nat.mod_lt _ hM0⟩
        have hwt_val : wt.val = gateTarget g := Nat.mod_eq_of_lt (gateTarget_lt hwfg)
        let wi : Wire M := ⟨i.val, by omega⟩
        change Function.update γ2 wt (γ2 wt + gateVal hM0 g γ2) wi = γ wi
        by_cases hwi : wi = wt
        · have hwt_eq : wt = ⟨gateTarget g, by omega⟩ := Fin.ext hwt_val
          have hval_eq : gateVal hM0 g γ2 = gateVal hM0 g γ := by
            cases g with
            | x _ => rfl
            | cnot c t =>
                have hwfg' := hwfg
                simp only [wfGateN, Bool.and_eq_true, Nat.blt_eq, bne_iff_ne] at hwfg
                dsimp only [gateVal]
                have hne_ct : (⟨c % M, Nat.mod_lt c hM0⟩ : Wire M) ≠ wt := fun e ↦ by
                  have hv := congrArg Fin.val e
                  rw [hwt_val] at hv
                  dsimp [gateTarget] at hv
                  rw [Nat.mod_eq_of_lt hwfg.1.1] at hv
                  exact hwfg.2 hv
                have hce : (⟨c % M, Nat.mod_lt c hM0⟩ : Wire M) = ⟨c, hwfg.1.1⟩ :=
                  Fin.ext (Nat.mod_eq_of_lt hwfg.1.1)
                by_cases hc48 : c < 48
                · rw [hce, ih ⟨c, hc48⟩, hγ1, gateToCP_eq_update hM0 hwfg' γ, ← hce,
                      Function.update_of_ne hne_ct]
                · dsimp only [gateTarget] at hgt48
                  simp only [Nat.blt_eq.mpr hgt48, Bool.eq_false_iff.mpr fun h ↦
                      hc48 (Nat.blt_eq.mp h),
                    Bool.not_true, Bool.false_or] at hcond
                  have hwfr := okHoldGN_wf rest hokr
                  dsimp only [γ2]
                  rw [hce, noWriteGN_fwd hM0 ⟨c, hwfg.1.1⟩ _
                        (List.all_append.trans ((Bool.and_eq_true _ _).mpr ⟨hwfr,
                            undoLt48_wf rest hwfr⟩))
                        (noWriteGN_append M c rest (undoLt48 rest) hcond
                          (undoLt48_noWrite_ge48 hM (by omega) hwfg.1.1 rest hwfr)) γ1,
                      hγ1, gateToCP_eq_update hM0 hwfg' γ, ← hce, Function.update_of_ne hne_ct]
            | andGate _ _ _ => cases hlt
          rw [hwi, Function.update_self, hval_eq, hwt_eq, ih ⟨gateTarget g, hgt48⟩,
              ← hwt_eq, hγ1, gateToCP_eq_update hM0 hwfg γ]
          change Function.update γ wt (γ wt + gateVal hM0 g γ) wt + gateVal hM0 g γ = γ wt
          rw [Function.update_self]
          exact zmod2_self_cancel _ _
        · rw [Function.update_of_ne hwi, ih i, hγ1, gateToCP_eq_update hM0 hwfg γ,
              Function.update_of_ne hwi]

-- ============================================================================
-- Section 2: Catalyst-Free Shared `44`-AND Prefix & Clean `189`/`172` Equivalence
-- ============================================================================

/-- Catalyst-free `19`-gate `Kara22` main body (never touches wire `8`). -/
def gsKara22Main : List GateN := [
  .x 0, .andGate 0 2 13, .andGate 10 3 14, .andGate 0 4 16, .andGate 10 5 17,
  .andGate 0 6 19, .andGate 10 7 20, .cnot 10 0, .cnot 2 3, .cnot 4 5, .cnot 6 7,
  .andGate 0 3 15, .andGate 0 5 18, .andGate 0 7 21, .cnot 6 7, .cnot 4 5,
  .cnot 2 3, .cnot 10 0, .x 0]

/-- Catalyst-free `21`-gate `Kara22` equivalent. -/
def gsKara22CF : List GateN := gsKara22Main ++ [.x 8, .cnot 0 8]

/-- Compiled `ComputeProg 22` for `gsKara22CF`. -/
def pKara22CF : ComputeProg 22 := gatesToCP (by decide) gsKara22CF

/-- Catalyst-free `92`-gate `OuterAx2` main body (never touches wire `8` = `w304 49`). -/
def gsOuterAx2Main : List GateN := [
  .andGate 0 2 11, .x 0, .x 4, .andGate 0 4 12, .x 0, .x 4, .x 12, .cnot 0 12, .cnot 4 12,
  .cnot 1 3, .x 11, .cnot 1 11, .cnot 2 11, .andGate 3 11 13, .cnot 1 3,
  .cnot 2 3, .x 11, .cnot 0 11, .andGate 3 11 14, .cnot 2 3,
  .cnot 0 11, .cnot 1 11, .cnot 2 11,
  .x 13, .cnot 10 13, .cnot 11 13, .cnot 14 13,
  .x 14, .cnot 0 14, .cnot 1 14, .cnot 3 14, .cnot 11 14,
  .cnot 13 12, .cnot 2 12, .cnot 3 12, .cnot 4 12,
  .cnot 1 11, .cnot 2 11, .cnot 10 11, .cnot 0 10,
  .x 0, .cnot 4 0, .cnot 5 0, .x 1, .andGate 0 1 15,
  .x 1, .cnot 5 0, .cnot 4 0, .x 0, .cnot 4 15,
  .cnot 5 12, .cnot 1 0, .andGate 12 0 16, .cnot 5 16, .cnot 0 12, .cnot 5 12, .cnot 1 0,
  .cnot 6 15, .x 0, .andGate 15 0 17, .cnot 6 17, .cnot 0 15, .cnot 6 15, .x 0,
  .cnot 16 15, .x 15, .cnot 1 15, .cnot 5 15,
  .cnot 7 17, .x 1, .cnot 6 1, .cnot 7 1, .andGate 17 1 18,
  .cnot 7 18, .cnot 1 17, .cnot 7 17, .cnot 7 1, .cnot 6 1, .x 1, .cnot 16 17,
  .x 16, .cnot 0 16, .cnot 7 16, .andGate 17 16 19, .cnot 7 16, .cnot 0 16, .x 16,
  .cnot 16 19, .x 17, .cnot 0 17, .cnot 7 17, .cnot 9 19]

/-- Catalyst-free `94`-gate `OuterAx2` equivalent. -/
def gsOuterAx2CF_30 : List GateN := gsOuterAx2Main ++ [.cnot 0 20, .cnot 10 20]

/-- Compiled `ComputeProg 30` for `gsOuterAx2CF_30`. -/
def pOuterAx2CF_30 : ComputeProg 30 := gatesToCP (by decide) gsOuterAx2CF_30

/-- Combined Axis-0 carry-77 + `pAx0Prefix304` unload block on `304` wires. -/
def pCarryAx0_304 : ComputeProg 304 := .seq pCarry77_304 pAx0Prefix304

/-- Pullback of `pCarryAx0_304` onto the `22`-wire Axis-0 local frame. -/
def pCarryAx0_22 : ComputeProg 22 := pullBackAx0 pCarryAx0_304

/-- Wire-by-wire equality check on `M` leaves of two `NTree5` bitboards. -/
def eqNT5Wires (M : ℕ) (t1 t2 : NTree5) : Bool :=
  (List.range M).all fun u ↦ getNT5 5 t1 u == getNT5 5 t2 u

/-- `1024`-input (`2 × 512`) `NTree5` check for `Kara22CF`, `OuterAx2CF`, and `CarryAx0`. -/
def checkNT5_1024_bool : Bool :=
  initNT5_22_cps fun t0 ↦
    let tA := setNT5 5 t0 10 0
    let tB := setNT5 5 t0 10 ones512
    eqNT5Wires 22 (evalProgNT5 ones512 pKara22CF tA) (evalProgNT5 ones512 pKara22 tA) &&
    eqNT5Wires 22 (evalProgNT5 ones512 pKara22CF tB) (evalProgNT5 ones512 pKara22 tB) &&
    eqNT5Wires 30 (evalProgNT5 ones512 pOuterAx2CF_30 tA) (evalProgNT5 ones512 pOuterAx2_30 tA) &&
    eqNT5Wires 30 (evalProgNT5 ones512 pOuterAx2CF_30 tB) (evalProgNT5 ones512 pOuterAx2_30 tB) &&
    (getNT5 5 (evalProgNT5 ones512 pCarryAx0_22 tA) 8 == 0) &&
    (getNT5 5 (evalProgNT5 ones512 pCarryAx0_22 tB) 8 == 0)

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem checkNT5_1024_cert : checkNT5_1024_bool = true := by decide +kernel

theorem eq_bitsOfNT5_of_eqNT5Wires {M : ℕ} {t1 t2 : NTree5}
    (h : eqNT5Wires M t1 t2 = true) (m : ℕ) :
    bitsOfNT5 (M := M) t1 m = bitsOfNT5 (M := M) t2 m := by
  funext u
  dsimp only [bitsOfNT5]
  have hu := beq_iff_eq.mp ((List.all_eq_true.mp h) u.val (List.mem_range.mpr u.isLt))
  rw [hu]

theorem eq_update_mkIn22 (δ : BitAssignment 22)
    (h8 : δ ⟨8, by decide⟩ = 0) (hcl : ∀ u : Wire 22, 11 ≤ u.val → δ u = 0) :
    ∃ m : Fin 512, δ = Function.update (mkIn22 m) ⟨10, by decide⟩ (δ ⟨10, by decide⟩) := by
  let f9 : Fin 9 → ZMod 2 :=
    fun k ↦ if h : k.val < 8 then δ ⟨k.val, by omega⟩ else δ ⟨9, by decide⟩
  let m : Fin 512 := ⟨finBitsVal f9, finBitsVal_lt f9⟩
  refine ⟨m, ?_⟩
  funext u
  by_cases hu10 : u = ⟨10, by decide⟩
  · subst hu10
    rw [Function.update_self]
  · rw [Function.update_of_ne hu10]
    by_cases hu8 : u.val < 8
    · have htb := finBitsVal_testBit f9 ⟨u.val, by omega⟩
      dsimp only [mkIn22, f9] at htb ⊢
      rw [leg_if_pos hu8]
      rw [leg_dif_pos hu8] at htb
      exact htb
    · by_cases heq8 : u = ⟨8, by decide⟩
      · subst heq8
        rw [h8]
        rfl
      · by_cases heq9 : u = ⟨9, by decide⟩
        · subst heq9
          have htb := finBitsVal_testBit f9 ⟨8, by decide⟩
          dsimp only [mkIn22, f9] at htb ⊢
          exact htb
        · have hge11 : 11 ≤ u.val := by
            have n8 : u.val ≠ 8 := fun e ↦ heq8 (Fin.ext e)
            have n9 : u.val ≠ 9 := fun e ↦ heq9 (Fin.ext e)
            have n10 : u.val ≠ 10 := fun e ↦ hu10 (Fin.ext e)
            omega
          rw [hcl u hge11]
          dsimp only [mkIn22]
          rw [leg_if_neg hu8, leg_if_neg (fun e ↦ heq9 (Fin.ext e)),
              leg_if_neg (fun e ↦ hu10 (Fin.ext e))]

theorem fwdBits_nt5_1024 {M : ℕ} (h10M : 10 < M) (hM : M ≤ 32) (p : ComputeProg M)
    (m : Fin 512) (b : ZMod 2) :
    p.fwdBits (Function.update (bitsOfNT5 initNT5_22 m.val) ⟨10, h10M⟩ b) =
      bitsOfNT5 (evalProgNT5 ones512 p
        (setNT5 5 initNT5_22 10 (if b = 0 then 0 else ones512))) m.val := by
  rcases zmod2_zero_or_one b with rfl | rfl
  · simp only [↓reduceIte]
    rw [← bitsOfNT5_set hM initNT5_22 initNT5_22_wf ⟨10, h10M⟩ 0 m.val 0 (by simp),
        fwdBits_bitsOfNT5 hM ones512 m.val (ones512_testBit m) p _ (setNT5_wf 5 _ _ _
            initNT5_22_wf)]
  · have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    rw [← bitsOfNT5_set hM initNT5_22 initNT5_22_wf ⟨10, h10M⟩ ones512 m.val 1
          (by
            rw [ones512_testBit m]
            rfl),
        fwdBits_bitsOfNT5 hM ones512 m.val (ones512_testBit m) p _ (setNT5_wf 5 _ _ _
            initNT5_22_wf)]

theorem pKara22CF_eq_pKara22 (δ : BitAssignment 22)
    (h8 : δ ⟨8, by decide⟩ = 0) (hcl : ∀ u : Wire 22, 11 ≤ u.val → δ u = 0) :
    pKara22CF.fwdBits δ = pKara22.fwdBits δ := by
  obtain ⟨m, hδ⟩ := eq_update_mkIn22 δ h8 hcl
  have hc := checkNT5_1024_cert
  dsimp only [checkNT5_1024_bool] at hc
  rw [initNT5_22_cps_eq] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hA22, hB22⟩, _⟩, _⟩, _⟩, _⟩ := hc
  rw [hδ, mkIn22_eq_bitsOfNT5 m, fwdBits_nt5_1024 (by decide) (by decide) pKara22CF m,
      fwdBits_nt5_1024 (by decide) (by decide) pKara22 m]
  rcases zmod2_zero_or_one (δ ⟨10, by decide⟩) with h10 | h10 <;> simp only [h10, ↓reduceIte]
  · exact eq_bitsOfNT5_of_eqNT5Wires hA22 m.val
  · exact eq_bitsOfNT5_of_eqNT5Wires (by simpa using hB22) m.val

theorem pCarryAx0_22_zero8 (δ : BitAssignment 22)
    (h8 : δ ⟨8, by decide⟩ = 0) (hcl : ∀ u : Wire 22, 11 ≤ u.val → δ u = 0) :
    pCarryAx0_22.fwdBits δ ⟨8, by decide⟩ = 0 := by
  obtain ⟨m, hδ⟩ := eq_update_mkIn22 δ h8 hcl
  have hc := checkNT5_1024_cert
  dsimp only [checkNT5_1024_bool] at hc
  rw [initNT5_22_cps_eq] at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨_, hcA⟩, hcB⟩ := hc
  rw [hδ, mkIn22_eq_bitsOfNT5 m, fwdBits_nt5_1024 (by decide) (by decide) pCarryAx0_22 m]
  dsimp only [bitsOfNT5]
  have h1ne0 : (1 : ZMod 2) ≠ 0 := by decide
  rcases zmod2_zero_or_one (δ ⟨10, by decide⟩) with h10 | h10
  · simp only [h10, ↓reduceIte]
    rw [hcA, Nat.zero_testBit]
    rfl
  · simp only [h10, h1ne0, ↓reduceIte]
    rw [hcB, Nat.zero_testBit]
    rfl

theorem pOuterAx2CF_30_eq (δ : BitAssignment 30)
    (h8 : δ ⟨8, by decide⟩ = 0) (hcl : ∀ u : Wire 30, 11 ≤ u.val → δ u = 0) :
    pOuterAx2CF_30.fwdBits δ = pOuterAx2_30.fwdBits δ := by
  let δ22 : BitAssignment 22 := fun u ↦ δ ⟨u.val, by omega⟩
  obtain ⟨m, hm⟩ := eq_update_mkIn22 δ22 h8 (fun u hu ↦ hcl ⟨u.val, by omega⟩ hu)
  have hc := checkNT5_1024_cert
  dsimp only [checkNT5_1024_bool] at hc
  rw [initNT5_22_cps_eq] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, hA30⟩, hB30⟩, _⟩, _⟩ := hc
  rw [show δ = Function.update (mkIn30 m) ⟨10, by decide⟩ (δ ⟨10, by decide⟩) from funext fun u ↦ by
        rcases Classical.em (u = ⟨10, by decide⟩) with rfl | hu10
        · rw [Function.update_self]
        · rw [Function.update_of_ne hu10]
          by_cases hu22 : u.val < 22
          · change δ22 ⟨u.val, hu22⟩ = _
            rw [congrFun hm ⟨u.val, hu22⟩,
                Function.update_of_ne (fun e ↦ hu10 (Fin.ext (congrArg (Fin.val : Fin 22 → ℕ) e)))]
            dsimp only [mkIn30]
            rw [leg_dif_pos hu22]
          · rw [hcl u (by omega)]
            dsimp only [mkIn30]
            rw [leg_dif_neg hu22],
      mkIn30_eq_bitsOfNT5 m, fwdBits_nt5_1024 (by decide) (by decide) pOuterAx2CF_30 m,
      fwdBits_nt5_1024 (by decide) (by decide) pOuterAx2_30 m]
  rcases zmod2_zero_or_one (δ ⟨10, by decide⟩) with h10 | h10 <;> simp only [h10, ↓reduceIte]
  · exact eq_bitsOfNT5_of_eqNT5Wires hA30 m.val
  · exact eq_bitsOfNT5_of_eqNT5Wires (by simpa using hB30) m.val

/-- Embedding of the `172`-wire unload active set into `Wire 304`. -/
def f172To304 (u : Wire 172) : Wire 304 :=
  if u.val < 48 then ⟨u.val, by omega⟩
  else if u.val < 57 then ⟨u.val + 1, by omega⟩
  else ⟨u.val + 2, by omega⟩

theorem fAx0To304_inj : Function.Injective fAx0To304 := by
  intro x y e
  fin_cases x <;> fin_cases y <;> first | rfl | exact absurd e (by decide)

theorem fAx2ShaTo304_inj : Function.Injective fAx2ShaTo304 := by
  intro x y e
  fin_cases x <;> fin_cases y <;> first | rfl | exact absurd e (by decide)

theorem f189To304_inj : Function.Injective f189To304 := by
  intro x y e
  apply Fin.ext
  have hv := congrArg Fin.val e
  dsimp only [f189To304] at hv
  split_ifs at hv
  all_goals dsimp at hv
  all_goals omega

theorem f172To304_inj : Function.Injective f172To304 := by
  intro x y e
  apply Fin.ext
  have hv := congrArg Fin.val e
  dsimp only [f172To304] at hv
  split_ifs at hv
  all_goals dsimp at hv
  all_goals omega

theorem mapCP_fwdBits_congr {N M : ℕ} (m : Fin N → Wire M) (hinj : Function.Injective m)
    (p1 p2 : ComputeProg N) (β : BitAssignment M)
    (heq : p1.fwdBits (fun q ↦ β (m q)) = p2.fwdBits (fun q ↦ β (m q))) :
    (mapCP m p1).fwdBits β = (mapCP m p2).fwdBits β := by
  funext w
  rw [mapCP_fwd m hinj p1 β w, mapCP_fwd m hinj p2 β w, heq]

/-- Projection `304 → 189` on `ℕ` indices. -/
def f304To189Nat (w : ℕ) : ℕ := if w < 48 then w else w - 1

/-- Projection `304 → 172` on `ℕ` indices. -/
def f304To172Nat (w : ℕ) : ℕ := if w < 48 then w else if w < 58 then w - 1 else w - 2

/-- Shared `44`-AND catalyst-free prefix blocks on `304` wires. -/
def gsLo12_304 : List GateN := toGatesNAux (mapCP (axMap25 0) (mapCP embLo25 pLo12)) []
def gsHi13_304 : List GateN := toGatesNAux (mapCP (axMap25 0) (mapCP embHi25 pHi13)) []
def gsBlk1_304 : List GateN := gsLo12_304 ++ gsHi13_304
def gsBlk2_304 : List GateN := toGatesNAux (mapCP (axMap25 1) pAxis25) []
def gsBlk3_304 : List GateN :=
  gsKara22Main.map (mapGateN fun u ↦ (embKaraAx1Fwd ⟨u % 22, Nat.mod_lt u (by decide)⟩).val)
def gsBlk4_304 : List GateN := toGatesNAux (mapCP (axMap25 2) pAxis25) []
def gsBlk5_304 : List GateN :=
  gsOuterAx2Main.map (mapGateN fun u ↦ (fAx2ShaTo304 ⟨u % 30, Nat.mod_lt u (by decide)⟩).val)

/-- Complete `44`-AND catalyst-free shared prefix on `304` wires. -/
def gsShared44_304 : List GateN :=
  gsBlk1_304 ++ gsBlk2_304 ++ gsBlk3_304 ++ gsBlk4_304 ++ gsBlk5_304

def gsKara0Fwd_304 : List GateN := toGatesNAux (mapCP embKaraAx0Fwd pKara22) []
def gsCarryAx0_304 : List GateN := toGatesNAux pCarryAx0_304 []

def gsSufFwd304 : List GateN :=
  [.andGate 24 25 58] ++ gsKara0Fwd_304 ++ [.x 189, .cnot 32 189, .cnot 40 108, .cnot 76 108]
def gsSufUnld304 : List GateN :=
  gsCarryAx0_304 ++ [.x 173, .cnot 32 173, .cnot 40 108, .cnot 76 108]

def gsCombFwd189 : List GateN := (gsShared44_304 ++ gsSufFwd304).map (mapGateN f304To189Nat)
def gsCombUnld172 : List GateN := (gsShared44_304 ++ gsSufUnld304).map (mapGateN f304To172Nat)
def pCombFwd189 : ComputeProg 189 := gatesToCP (by decide) gsCombFwd189
def pCombUnld172 : ComputeProg 172 := gatesToCP (by decide) gsCombUnld172

/-- Check that `gs` leaves `emb u` (`u = 8` if `chk8`, plus all `u ≥ 11`) untouched and `≥ 48`. -/
def checkCleanEmb {N : ℕ} (emb : Fin N → Wire 304) (chk8 : Bool) (gs : List GateN) : Bool :=
  (List.finRange N).all fun u ↦
    if (chk8 && (u.val == 8)) || Nat.ble 11 u.val then
      Nat.ble 48 (emb u).val && noWriteGN 304 (emb u).val gs
    else true

/-- Bundled `304`-wire structural & disjointness certificate for Section 2. -/
def sec2_304_bool : Bool :=
  let gPre := toGatesNAux pPre304 []
  let gPre26 := toGatesNAux pPre304_26 []
  let gK1F := toGatesNAux (mapCP embKaraAx1Fwd pKara22CF) []
  let gK1U := toGatesNAux (mapCP embKaraAx1Unld pKara22CF) []
  let gAx2CF := toGatesNAux (mapCP fAx2ShaTo304 pOuterAx2CF_30) []
  gsLo12_304.all (wfGateN 304) &&
  gsHi13_304.all (wfGateN 304) &&
  gsBlk2_304.all (wfGateN 304) &&
  gsBlk3_304.all (wfGateN 304) &&
  gsBlk4_304.all (wfGateN 304) &&
  gsBlk5_304.all (wfGateN 304) &&
  ([.andGate 24 25 58] : List GateN).all (wfGateN 304) &&
  gsKara0Fwd_304.all (wfGateN 304) &&
  gsCarryAx0_304.all (wfGateN 304) &&
  ([.x 189, .cnot 32 189] : List GateN).all (wfGateN 304) &&
  ([.x 173, .cnot 32 173] : List GateN).all (wfGateN 304) &&
  ([.cnot 40 108, .cnot 76 108] : List GateN).all (wfGateN 304) &&
  disjLists (gsHi13_304 ++ gsBlk2_304 ++ gsBlk3_304 ++ gsBlk4_304 ++ gsBlk5_304)
    [.andGate 24 25 58] &&
  disjLists gsBlk3_304 gsBlk4_304 &&
  disjLists (gsBlk3_304 ++ gsBlk5_304) gsKara0Fwd_304 &&
  disjLists gsBlk5_304 [.x 189, .cnot 32 189] &&
  disjLists (gsBlk3_304 ++ gsBlk4_304 ++ gsBlk5_304) gsCarryAx0_304 &&
  disjLists (gsCarryAx0_304 ++ gsBlk3_304) gsBlk4_304 &&
  disjLists gsBlk5_304 [.x 173, .cnot 32 173] &&
  beqGateList (gsLo12_304 ++ [.andGate 24 25 58] ++ gsHi13_304 ++ gsBlk2_304 ++ gsBlk4_304) gPre &&
  beqGateList (gsBlk1_304 ++ gsBlk2_304 ++ gsBlk4_304) gPre26 &&
  beqGateList (gsBlk3_304 ++ [.x 189, .cnot 32 189]) gK1F &&
  beqGateList (gsBlk3_304 ++ [.x 173, .cnot 32 173]) gK1U &&
  beqGateList (gsBlk5_304 ++ [.cnot 40 108, .cnot 76 108]) gAx2CF &&
  beqGateList (toGatesNAux (mapCP fAx2ShaTo304 pOuterAx2_30) []) (toGatesNAux pOuterAx2_304 []) &&
  beqGateList (toGatesNAux (mapCP fAx0To304 pCarryAx0_22) []) gsCarryAx0_304 &&
  beqGateList (toGatesNAux (mapCP f189To304 pOuterFwd189) []) (toGatesNAux pOuterFwd304 []) &&
  beqGateList (toGatesNAux (mapCP f189To304 pCombFwd189) []) (gsShared44_304 ++ gsSufFwd304) &&
  beqGateList (toGatesNAux (mapCP f172To304 pOuterUnld172) []) (toGatesNAux pOuterUnld304 []) &&
  beqGateList (toGatesNAux (mapCP f172To304 pCombUnld172) []) (gsShared44_304 ++ gsSufUnld304) &&
  checkCleanEmb embKaraAx1Fwd true (gPre ++ gsKara0Fwd_304) &&
  checkCleanEmb fAx2ShaTo304 true (gPre ++ gsKara0Fwd_304 ++ gK1F) &&
  checkCleanEmb fAx0To304 true gPre26 &&
  checkCleanEmb embKaraAx1Unld true (gPre26 ++ gsCarryAx0_304) &&
  checkCleanEmb fAx2ShaTo304 false (gPre26 ++ gsCarryAx0_304 ++ gK1U) &&
  noWriteGN 304 49 gK1U

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem sec2_304_cert : sec2_304_bool = true := by decide +kernel

theorem cleanEmb_ge11 {N : ℕ} {emb : Fin N → Wire 304} {chk8 : Bool} {gs : List GateN}
    (hchk : checkCleanEmb emb chk8 gs = true) (hwf : gs.all (wfGateN 304) = true)
    {γ : BitAssignment 304} (hcl : ∀ w : Wire 304, 48 ≤ w.val → γ w = 0)
    (u : Fin N) (hu : 11 ≤ u.val) :
    (gatesToCP (by decide) gs).fwdBits γ (emb u) = 0 := by
  have hall := (List.all_eq_true.mp hchk) u (List.mem_finRange u)
  have hcond : ((chk8 && (u.val == 8)) || Nat.ble 11 u.val) = true := by
    rw [Nat.ble_eq.mpr hu, Bool.or_true]
  rw [hcond] at hall
  simp only [↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at hall
  rw [noWriteGN_fwd (by decide) (emb u) gs hwf hall.2 γ]
  exact hcl (emb u) hall.1

theorem cleanEmb_8 {N : ℕ} {emb : Fin N → Wire 304} {gs : List GateN}
    (hchk : checkCleanEmb emb true gs = true) (hwf : gs.all (wfGateN 304) = true)
    {γ : BitAssignment 304} (hcl : ∀ w : Wire 304, 48 ≤ w.val → γ w = 0)
    (hN : 8 < N) :
    (gatesToCP (by decide) gs).fwdBits γ (emb ⟨8, hN⟩) = 0 := by
  have hall := (List.all_eq_true.mp hchk) ⟨8, hN⟩ (List.mem_finRange ⟨8, hN⟩)
  have hcond : ((true && ((8 : ℕ) == 8)) || Nat.ble 11 8) = true := rfl
  rw [hcond] at hall
  simp only [↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at hall
  rw [noWriteGN_fwd (by decide) (emb ⟨8, hN⟩) gs hwf hall.2 γ]
  exact hcl (emb ⟨8, hN⟩) hall.1

theorem wf_append304 {xs ys : List GateN}
    (hx : xs.all (wfGateN 304) = true) (hy : ys.all (wfGateN 304) = true) :
    (xs ++ ys).all (wfGateN 304) = true := by
  rw [List.all_append, Bool.and_eq_true]
  exact ⟨hx, hy⟩

theorem gatesToCP_toGates304 (p : ComputeProg 304) (γ : BitAssignment 304) :
    (gatesToCP (by decide) (toGatesNAux p [])).fwdBits γ = p.fwdBits γ := by
  have e := toGatesNAux_gatesToCP (by decide) p [] γ
  dsimp only [gatesToCP, ComputeProg.fwdBits] at e
  exact e

theorem proj_eq_of_304 {M : ℕ} (f : Fin M → Wire 304) (hinj : Function.Injective f)
    {pC pO : ComputeProg M} {pO304 : ComputeProg 304} {gs : List GateN}
    (bC : beqGateList (toGatesNAux (mapCP f pC) []) gs = true)
    (bO : beqGateList (toGatesNAux (mapCP f pO) []) (toGatesNAux pO304 []) = true)
    (γ0 : BitAssignment M) (γ3 : BitAssignment 304) (hproj : (fun q ↦ γ3 (f q)) = γ0)
    (h304Eq : (gatesToCP (by decide) gs).fwdBits γ3 = pO304.fwdBits γ3) :
    pC.fwdBits γ0 = pO.fwdBits γ0 := by
  funext u
  rw [← hproj, ← mapCP_fwd_apply f hinj pC γ3 u, ← mapCP_fwd_apply f hinj pO γ3 u]
  have eC : (mapCP f pC).fwdBits γ3 = (gatesToCP (by decide) gs).fwdBits γ3 := by
    rw [← gatesToCP_toGates304 (mapCP f pC) γ3, beqGateList_eq bC]
  rw [eC, eq_fwdBits_of_toGates (by decide) (beqGateList_eq bO) γ3, h304Eq]

theorem pCombFwd189_eq_pOuterFwd189 (γ0 : BitAssignment 189)
    (hcl : ∀ u : Wire 189, 48 ≤ u.val → γ0 u = 0) :
    pCombFwd189.fwdBits γ0 = pOuterFwd189.fwdBits γ0 := by
  have h304 : 0 < 304 := by decide
  have hc := sec2_304_cert
  dsimp only [sec2_304_bool] at hc
  simp only [Bool.and_eq_true, and_assoc] at hc
  obtain ⟨wLo, wHi, wB2, wB3, wB4, wB5, w24, wK0, _, w189, _, w40,
    d1, d2, d3, d4, _, _, _, bPre, _, bK1F, _, bAx2, bAx2Eq, _, bOF, bCF, _, _,
    c1, c2, _, _, _, _⟩ := hc
  let γ3 : BitAssignment 304 := fun w ↦ if h : w.val < 48 then γ0 ⟨w.val, by omega⟩ else 0
  have hcl3 : ∀ w : Wire 304, 48 ≤ w.val → γ3 w = 0 := fun _ _ ↦ pDiteNeg (by omega)
  let g24 : List GateN := [.andGate 24 25 58]
  let g189 : List GateN := [.x 189, .cnot 32 189]
  let g40 : List GateN := [.cnot 40 108, .cnot 76 108]
  let gPre := toGatesNAux pPre304 []
  let gK1F := toGatesNAux (mapCP embKaraAx1Fwd pKara22CF) []
  let gAx2CF := toGatesNAux (mapCP fAx2ShaTo304 pOuterAx2CF_30) []
  have hPreEq : gsLo12_304 ++ g24 ++ gsHi13_304 ++ gsBlk2_304 ++ gsBlk4_304 = gPre :=
      beqGateList_eq bPre
  have hK1FEq : gsBlk3_304 ++ g189 = gK1F := beqGateList_eq bK1F
  have wPre : gPre.all (wfGateN 304) = true :=
    hPreEq ▸ wf_append304 (wf_append304 (wf_append304 (wf_append304 wLo w24) wHi) wB2) wB4
  have wK1F : gK1F.all (wfGateN 304) = true := hK1FEq ▸ wf_append304 wB3 w189
  let γA := (gatesToCP h304 (gPre ++ gsKara0Fwd_304)).fwdBits γ3
  let γB := (gatesToCP h304 (gPre ++ gsKara0Fwd_304 ++ gK1F)).fwdBits γ3
  refine proj_eq_of_304 f189To304 f189To304_inj bCF bOF γ0 γ3 (funext fun q ↦ by
    dsimp only [γ3, f189To304]
    by_cases hq : q.val < 48
    · simp only [hq, ↓reduceIte, ↓reduceDIte]
    · simp only [hq, ↓reduceIte, show ¬ (q.val + 1 < 48) by omega, ↓reduceDIte]
      exact (hcl q (by omega)).symm) ?_
  rw [show gsShared44_304 ++ gsSufFwd304 = gsLo12_304 ++
        ((gsHi13_304 ++ gsBlk2_304 ++ gsBlk3_304 ++ gsBlk4_304 ++ gsBlk5_304) ++
          (g24 ++ (gsKara0Fwd_304 ++ (g189 ++ g40)))) by
        dsimp only [gsShared44_304, gsBlk1_304, gsSufFwd304, g24, g189, g40]
        simp only [List.append_assoc, List.cons_append, List.nil_append],
      gatesToCP_comm_mid h304 gsLo12_304
        (gsHi13_304 ++ gsBlk2_304 ++ gsBlk3_304 ++ gsBlk4_304 ++ gsBlk5_304) g24
        (gsKara0Fwd_304 ++ (g189 ++ g40))
        (wf_append304 (wf_append304 (wf_append304 (wf_append304 wHi wB2) wB3) wB4) wB5) w24 d1 γ3,
      show gsLo12_304 ++ (g24 ++ ((gsHi13_304 ++ gsBlk2_304 ++ gsBlk3_304 ++ gsBlk4_304 ++
          gsBlk5_304) ++
          (gsKara0Fwd_304 ++ (g189 ++ g40)))) =
        (gsLo12_304 ++ g24 ++ gsHi13_304 ++ gsBlk2_304) ++
          (gsBlk3_304 ++ (gsBlk4_304 ++ (gsBlk5_304 ++ (gsKara0Fwd_304 ++ (g189 ++ g40))))) by
        simp only [List.append_assoc],
      gatesToCP_comm_mid h304 (gsLo12_304 ++ g24 ++ gsHi13_304 ++ gsBlk2_304)
        gsBlk3_304 gsBlk4_304 (gsBlk5_304 ++ (gsKara0Fwd_304 ++ (g189 ++ g40))) wB3 wB4 d2 γ3,
      show (gsLo12_304 ++ g24 ++ gsHi13_304 ++ gsBlk2_304) ++
          (gsBlk4_304 ++ (gsBlk3_304 ++ (gsBlk5_304 ++ (gsKara0Fwd_304 ++ (g189 ++ g40))))) =
        gPre ++ ((gsBlk3_304 ++ gsBlk5_304) ++ (gsKara0Fwd_304 ++ (g189 ++ g40))) by
        rw [← hPreEq]
        simp only [List.append_assoc],
      gatesToCP_comm_mid h304 gPre (gsBlk3_304 ++ gsBlk5_304) gsKara0Fwd_304
        (g189 ++ g40) (wf_append304 wB3 wB5) wK0 d3 γ3,
      show gPre ++ (gsKara0Fwd_304 ++ ((gsBlk3_304 ++ gsBlk5_304) ++ (g189 ++ g40))) =
        (gPre ++ gsKara0Fwd_304 ++ gsBlk3_304) ++ (gsBlk5_304 ++ (g189 ++ g40)) by
        simp only [List.append_assoc],
      gatesToCP_comm_mid h304 (gPre ++ gsKara0Fwd_304 ++
          gsBlk3_304) gsBlk5_304 g189 g40 wB5 w189 d4 γ3,
      show (gPre ++ gsKara0Fwd_304 ++ gsBlk3_304) ++ (g189 ++ (gsBlk5_304 ++ g40)) =
        ((gPre ++ gsKara0Fwd_304) ++ gK1F) ++ gAx2CF by
        dsimp only [gAx2CF]
        rw [← hK1FEq, ← beqGateList_eq bAx2]
        simp only [g40, List.append_assoc],
      gatesToCP_append]
  change (gatesToCP h304 gAx2CF).fwdBits γB = _
  dsimp only [gAx2CF]
  rw [gatesToCP_toGates304,
      mapCP_fwdBits_congr fAx2ShaTo304 fAx2ShaTo304_inj pOuterAx2CF_30 pOuterAx2_30 γB
        (pOuterAx2CF_30_eq _ (cleanEmb_8 c2 (wf_append304 (wf_append304 wPre wK0) wK1F) hcl3
            (by decide))
          (cleanEmb_ge11 c2 (wf_append304 (wf_append304 wPre wK0) wK1F) hcl3)),
      eq_fwdBits_of_toGates h304 (beqGateList_eq bAx2Eq) γB,
      show γB = (mapCP embKaraAx1Fwd pKara22).fwdBits γA by
        dsimp only [γB, gK1F]
        rw [gatesToCP_append, gatesToCP_toGates304]
        exact mapCP_fwdBits_congr embKaraAx1Fwd embKaraAx1Fwd_inj pKara22CF pKara22 γA
          (pKara22CF_eq_pKara22 _ (cleanEmb_8 c1 (wf_append304 wPre wK0) hcl3 (by decide))
            (cleanEmb_ge11 c1 (wf_append304 wPre wK0) hcl3)),
      show γA = (mapCP embKaraAx0Fwd pKara22).fwdBits (pPre304.fwdBits γ3) by
        dsimp only [γA, gPre, gsKara0Fwd_304]
        rw [gatesToCP_append, gatesToCP_toGates304, gatesToCP_toGates304]]
  rfl

theorem pCombUnld172_eq_pOuterUnld172 (γ0 : BitAssignment 172)
    (hcl : ∀ u : Wire 172, 48 ≤ u.val → γ0 u = 0) :
    pCombUnld172.fwdBits γ0 = pOuterUnld172.fwdBits γ0 := by
  have h304 : 0 < 304 := by decide
  have hc := sec2_304_cert
  dsimp only [sec2_304_bool] at hc
  simp only [Bool.and_eq_true, and_assoc] at hc
  obtain ⟨wLo, wHi, wB2, wB3, wB4, wB5, _, _, wCar, _, w173, w40,
    _, _, _, _, d5, d6, d7, _, bPre26, _, bK1U, bAx2, bAx2Eq, bCarEq, _, _, bOU, bCU,
    _, _, c3, c4, c5, nw49⟩ := hc
  let γ3 : BitAssignment 304 := fun w ↦ if h : w.val < 48 then γ0 ⟨w.val, by omega⟩ else 0
  have hcl3 : ∀ w : Wire 304, 48 ≤ w.val → γ3 w = 0 := fun _ _ ↦ pDiteNeg (by omega)
  let g173 : List GateN := [.x 173, .cnot 32 173]
  let g40 : List GateN := [.cnot 40 108, .cnot 76 108]
  let gPre26 := toGatesNAux pPre304_26 []
  let gK1U := toGatesNAux (mapCP embKaraAx1Unld pKara22CF) []
  let gAx2CF := toGatesNAux (mapCP fAx2ShaTo304 pOuterAx2CF_30) []
  have hPre26Eq : gsBlk1_304 ++ gsBlk2_304 ++ gsBlk4_304 = gPre26 := beqGateList_eq bPre26
  have hK1UEq : gsBlk3_304 ++ g173 = gK1U := beqGateList_eq bK1U
  have wPre26 : gPre26.all (wfGateN 304) = true :=
    hPre26Eq ▸ wf_append304 (wf_append304 (wf_append304 wLo wHi) wB2) wB4
  have wK1U : gK1U.all (wfGateN 304) = true := hK1UEq ▸ wf_append304 wB3 w173
  let γP := (gatesToCP h304 gPre26).fwdBits γ3
  let γC := (gatesToCP h304 (gPre26 ++ gsCarryAx0_304)).fwdBits γ3
  have hγC_eq : γC = pCarryAx0_304.fwdBits γP := by
    dsimp only [γC, gsCarryAx0_304]
    rw [gatesToCP_append, gatesToCP_toGates304]
  let γK := (gatesToCP h304 (gPre26 ++ gsCarryAx0_304 ++ gK1U)).fwdBits γ3
  refine proj_eq_of_304 f172To304 f172To304_inj bCU bOU γ0 γ3 (funext fun q ↦ by
    dsimp only [γ3, f172To304]
    by_cases hq : q.val < 48
    · simp only [hq, ↓reduceIte, ↓reduceDIte]
    · by_cases hq57 : q.val < 57
      · simp only [hq, hq57, ↓reduceIte, show ¬ (q.val + 1 < 48) by omega, ↓reduceDIte]
        exact (hcl q (by omega)).symm
      · simp only [hq, hq57, ↓reduceIte, show ¬ (q.val + 2 < 48) by omega, ↓reduceDIte]
        exact (hcl q (by omega)).symm) ?_
  rw [show gsShared44_304 ++ gsSufUnld304 = (gsBlk1_304 ++ gsBlk2_304) ++
        ((gsBlk3_304 ++ gsBlk4_304 ++ gsBlk5_304) ++ (gsCarryAx0_304 ++ (g173 ++ g40))) by
        dsimp only [gsShared44_304, gsSufUnld304, g173, g40]
        simp only [List.append_assoc, List.cons_append, List.nil_append],
      gatesToCP_comm_mid h304 (gsBlk1_304 ++ gsBlk2_304)
        (gsBlk3_304 ++ gsBlk4_304 ++ gsBlk5_304) gsCarryAx0_304 (g173 ++ g40)
        (wf_append304 (wf_append304 wB3 wB4) wB5) wCar d5 γ3,
      show (gsBlk1_304 ++ gsBlk2_304) ++
          (gsCarryAx0_304 ++ ((gsBlk3_304 ++ gsBlk4_304 ++ gsBlk5_304) ++ (g173 ++ g40))) =
        (gsBlk1_304 ++ gsBlk2_304) ++
          ((gsCarryAx0_304 ++ gsBlk3_304) ++ (gsBlk4_304 ++ (gsBlk5_304 ++ (g173 ++ g40)))) by
        simp only [List.append_assoc],
      gatesToCP_comm_mid h304 (gsBlk1_304 ++ gsBlk2_304)
        (gsCarryAx0_304 ++ gsBlk3_304) gsBlk4_304 (gsBlk5_304 ++ (g173 ++ g40))
            (wf_append304 wCar wB3) wB4 d6 γ3,
      show (gsBlk1_304 ++ gsBlk2_304) ++
          (gsBlk4_304 ++ ((gsCarryAx0_304 ++ gsBlk3_304) ++ (gsBlk5_304 ++ (g173 ++ g40)))) =
        (gPre26 ++ gsCarryAx0_304 ++ gsBlk3_304) ++ (gsBlk5_304 ++ (g173 ++ g40)) by
        rw [← hPre26Eq]
        simp only [List.append_assoc],
      gatesToCP_comm_mid h304 (gPre26 ++ gsCarryAx0_304 ++
          gsBlk3_304) gsBlk5_304 g173 g40 wB5 w173 d7 γ3,
      show (gPre26 ++ gsCarryAx0_304 ++ gsBlk3_304) ++ (g173 ++ (gsBlk5_304 ++ g40)) =
        ((gPre26 ++ gsCarryAx0_304) ++ gK1U) ++ gAx2CF by
        dsimp only [gAx2CF]
        rw [← hK1UEq, ← beqGateList_eq bAx2]
        simp only [g40, List.append_assoc],
      gatesToCP_append]
  change (gatesToCP h304 gAx2CF).fwdBits γK = _
  dsimp only [gAx2CF]
  rw [gatesToCP_toGates304,
      mapCP_fwdBits_congr fAx2ShaTo304 fAx2ShaTo304_inj pOuterAx2CF_30 pOuterAx2_30 γK
        (pOuterAx2CF_30_eq _ (by
            rw [show fAx2ShaTo304 ⟨8, by decide⟩ = ⟨49, by decide⟩ by decide]
            dsimp only [γK]
            rw [gatesToCP_append, noWriteGN_fwd h304 ⟨49, by decide⟩ gK1U wK1U nw49 γC,
                ← (by decide : fAx0To304 ⟨8, by decide⟩ = ⟨49, by decide⟩), hγC_eq,
                (eq_fwdBits_of_toGates h304 (beqGateList_eq bCarEq) γP).symm,
                mapCP_fwd_apply fAx0To304 fAx0To304_inj pCarryAx0_22 γP ⟨8, by decide⟩]
            exact pCarryAx0_22_zero8 _ (cleanEmb_8 c3 wPre26 hcl3 (by decide))
                (cleanEmb_ge11 c3 wPre26 hcl3))
          (cleanEmb_ge11 c5 (wf_append304 (wf_append304 wPre26 wCar) wK1U) hcl3)),
      eq_fwdBits_of_toGates h304 (beqGateList_eq bAx2Eq) γK,
      show γK = (mapCP embKaraAx1Unld pKara22).fwdBits γC by
        dsimp only [γK, gK1U]
        rw [gatesToCP_append, gatesToCP_toGates304]
        exact mapCP_fwdBits_congr embKaraAx1Unld embKaraAx1Unld_inj pKara22CF pKara22 γC
          (pKara22CF_eq_pKara22 _ (cleanEmb_8 c4 (wf_append304 wPre26 wCar) hcl3 (by decide))
            (cleanEmb_ge11 c4 (wf_append304 wPre26 wCar) hcl3)),
      hγC_eq, show γP = pPre304_26.fwdBits γ3 from gatesToCP_toGates304 pPre304_26 γ3]
  rfl

-- ============================================================================
-- Section 3: Uniform `k = 1..44` Split Programs & Single `allSplits44_cert`
-- ============================================================================

/-- `304`-wire target indices of the `44` shared prefix ANDs in topological order. -/
def anc304List : List ℕ := [
  50, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 67, 63, 64, 65, 66,
  91, 92, 94, 95, 97, 98, 93, 96, 99,
  68, 69, 70, 71, 76, 72, 73, 74, 75,
  78, 100, 101, 102, 103, 104, 105, 106, 107]

/-- Permutation of `Fin 141` placing the `44` shared prefix ancillas at `0..43`. -/
def ord141List : List ℕ := [
  1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 18, 14, 15, 16, 17,
  42, 43, 45, 46, 48, 49, 44, 47, 50, 19, 20, 21, 22, 27, 23, 24, 25, 26, 29,
  51, 52, 53, 54, 55, 56, 57, 58,
  0, 9, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
  59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
  80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
  100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133,
  134, 135, 136, 137, 138, 139, 140]

/-- Inverse permutation of `ord141List` on `Fin 141`. -/
def inv141List : List ℕ := [
  44, 0, 1, 2, 3, 4, 5, 6, 7, 45, 8, 9, 10, 11, 13, 14, 15, 16, 12,
  26, 27, 28, 29, 31, 32, 33, 34, 30, 46, 35, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58,
  17, 18, 23, 19, 20, 24, 21, 22, 25, 36, 37, 38, 39, 40, 41, 42, 43,
  59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
  80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
  100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133,
  134, 135, 136, 137, 138, 139, 140]

/-- Permutation of `Fin 124` placing the `44` shared prefix ancillas at `0..43`. -/
def ord124List : List ℕ := [
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 17, 13, 14, 15, 16,
  41, 42, 44, 45, 47, 48, 43, 46, 49, 18, 19, 20, 21, 26, 22, 23, 24, 25, 28,
  50, 51, 52, 53, 54, 55, 56, 57,
  0, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
  58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
  80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
  100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123]

/-- Inverse permutation of `ord124List` on `Fin 124`. -/
def inv124List : List ℕ := [
  44, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 12,
  26, 27, 28, 29, 31, 32, 33, 34, 30, 45, 35, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57,
  17, 18, 23, 19, 20, 24, 21, 22, 25, 36, 37, 38, 39, 40, 41, 42, 43,
  58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
  80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
  100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123]

def ord141 (i : Fin 141) : Fin 141 := ⟨ord141List.getD i.val 0 % 141, Nat.mod_lt _ (by decide)⟩
def inv141 (i : Fin 141) : Fin 141 := ⟨inv141List.getD i.val 0 % 141, Nat.mod_lt _ (by decide)⟩
def ord124 (i : Fin 124) : Fin 124 := ⟨ord124List.getD i.val 0 % 124, Nat.mod_lt _ (by decide)⟩
def inv124 (i : Fin 124) : Fin 124 := ⟨inv124List.getD i.val 0 % 124, Nat.mod_lt _ (by decide)⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem perm_141_124_certs :
    (((List.finRange 141).all fun i ↦ (inv141 (ord141 i) == i) && (ord141 (inv141 i) == i)) &&
     ((List.finRange 124).all fun i ↦ (inv124 (ord124 i) == i) && (ord124 (inv124 i) == i))) =
      true := by decide +kernel

theorem ord141_leftInv (i : Fin 141) : inv141 (ord141 i) = i :=
  beq_iff_eq.mp ((Bool.and_eq_true _ _).mp
    ((List.all_eq_true.mp ((Bool.and_eq_true _ _).mp perm_141_124_certs).1) i (List.mem_finRange
        i))).1

theorem inv141_leftInv (i : Fin 141) : ord141 (inv141 i) = i :=
  beq_iff_eq.mp ((Bool.and_eq_true _ _).mp
    ((List.all_eq_true.mp ((Bool.and_eq_true _ _).mp perm_141_124_certs).1) i (List.mem_finRange
        i))).2

theorem ord124_leftInv (i : Fin 124) : inv124 (ord124 i) = i :=
  beq_iff_eq.mp ((Bool.and_eq_true _ _).mp
    ((List.all_eq_true.mp ((Bool.and_eq_true _ _).mp perm_141_124_certs).2) i (List.mem_finRange
        i))).1

theorem inv124_leftInv (i : Fin 124) : ord124 (inv124 i) = i :=
  beq_iff_eq.mp ((Bool.and_eq_true _ _).mp
    ((List.all_eq_true.mp ((Bool.and_eq_true _ _).mp perm_141_124_certs).2) i (List.mem_finRange
        i))).2

def findIdxAux (x : ℕ) : List ℕ → ℕ → ℕ
  | [], idx => idx
  | y :: ys, idx => if x == y then idx else findIdxAux x ys (idx + 1)

def f304ToHoldNat (w : ℕ) : ℕ :=
  if w < 48 then w else 48 + findIdxAux w anc304List 0

def holdTo189Nat (u : ℕ) : ℕ :=
  if u < 48 then u else 48 + (ord141List.getD (u - 48) 0 % 141)

def holdTo172Nat (u : ℕ) : ℕ :=
  if u < 48 then u else 48 + (ord124List.getD (u - 48) 0 % 124)

def embHold189 (k : ℕ) (u : Fin (48 + k)) : Wire 189 :=
  if h : u.val < 48 then ⟨u.val, by omega⟩
  else ⟨48 + (ord141 ⟨(u.val - 48) % 141, Nat.mod_lt _ (by decide)⟩).val,
    by
      have hlt := (ord141 ⟨(u.val - 48) % 141, Nat.mod_lt _ (by decide)⟩).isLt
      omega⟩

def embHold172 (k : ℕ) (u : Fin (48 + k)) : Wire 172 :=
  if h : u.val < 48 then ⟨u.val, by omega⟩
  else ⟨48 + (ord124 ⟨(u.val - 48) % 124, Nat.mod_lt _ (by decide)⟩).val,
    by
      have hlt := (ord124 ⟨(u.val - 48) % 124, Nat.mod_lt _ (by decide)⟩).isLt
      omega⟩

theorem embHoldGen_inj {M S k : ℕ} (hS : 0 < S) (hkS : k ≤ S)
    (ord inv : Fin S → Fin S) (hlinv : ∀ i, inv (ord i) = i)
    (emb : Fin (48 + k) → Wire M)
    (hval : ∀ u, (emb u).val =
      if u.val < 48 then u.val else 48 + (ord ⟨(u.val - 48) % S, Nat.mod_lt _ hS⟩).val) :
    Function.Injective emb := by
  intro x y e
  have hv := congrArg Fin.val e
  rw [hval x, hval y] at hv
  split_ifs at hv
  · exact Fin.ext hv
  · omega
  · omega
  · have hi := congrArg (fun z ↦ (inv z).val) (Fin.ext (by omega) :
      ord ⟨(x.val - 48) % S, Nat.mod_lt _ hS⟩ = ord ⟨(y.val - 48) % S, Nat.mod_lt _ hS⟩)
    rw [hlinv, hlinv] at hi
    dsimp only at hi
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hi
    exact Fin.ext (by omega)

theorem embHold189_inj {k : ℕ} (hk44 : k ≤ 44) : Function.Injective (embHold189 k) :=
  embHoldGen_inj (by decide) (by omega) ord141 inv141 ord141_leftInv (embHold189 k) fun u ↦ by
    dsimp only [embHold189]
    split_ifs <;> rfl

theorem embHold172_inj {k : ℕ} (hk44 : k ≤ 44) : Function.Injective (embHold172 k) :=
  embHoldGen_inj (by decide) (by omega) ord124 inv124 ord124_leftInv (embHold172 k) fun u ↦ by
    dsimp only [embHold172]
    split_ifs <;> rfl

/-- Split `gs` immediately after its `k`-th `.andGate`. -/
def splitAtAnd : ℕ → List GateN → List GateN × List GateN
  | 0, gs => ([], gs)
  | _ + 1, [] => ([], [])
  | k + 1, g :: gs =>
      match g with
      | .andGate _ _ _ =>
          if k == 0 then ([g], gs)
          else
            let pr := splitAtAnd k gs
            (g :: pr.1, pr.2)
      | _ =>
          let pr := splitAtAnd (k + 1) gs
          (g :: pr.1, pr.2)

/-- Accumulate bitmask of `.andGate` target wires. -/
def andMaskGNAux : List GateN → ℕ → ℕ
  | [], acc => acc
  | .andGate _ _ c :: gs, acc => forceNat (acc ||| (1 <<< c)) fun acc' ↦ andMaskGNAux gs acc'
  | _ :: gs, acc => andMaskGNAux gs acc

def sMaskHoldNat (k : ℕ) : ℕ := forceNat (((1 <<< k) - 1) <<< 48) id

def gsHoldPre (k : ℕ) : List GateN :=
  (splitAtAnd k gsShared44_304).1.map (mapGateN f304ToHoldNat)

def gsHold (k : ℕ) : List GateN :=
  gsHoldPre k ++ undoLt48 (gsHoldPre k)

def pHoldProg (k : ℕ) : ComputeProg (48 + k) :=
  gatesToCP (by omega) (gsHold k)

def gsTailFwd (k : ℕ) : List GateN :=
  let sp := splitAtAnd k gsShared44_304
  ((undoLt48 sp.1).reverse ++ sp.2 ++ gsSufFwd304).map (mapGateN f304To189Nat)

def pTailFwdProg (k : ℕ) : ComputeProg 189 :=
  gatesToCP (by decide) (gsTailFwd k)

def sMaskTailFwd (k : ℕ) : ℕ :=
  andMaskGNAux (gsTailFwd k) 0

def gsTailUnld (k : ℕ) : List GateN :=
  let sp := splitAtAnd k gsShared44_304
  ((undoLt48 sp.1).reverse ++ sp.2 ++ gsSufUnld304).map (mapGateN f304To172Nat)

def pTailUnldProg (k : ℕ) : ComputeProg 172 :=
  gatesToCP (by decide) (gsTailUnld k)

def sMaskTailUnld (k : ℕ) : ℕ :=
  andMaskGNAux (gsTailUnld k) 0

/-- Bundled Boolean obligations for split point `k ∈ [1, 44]`. -/
def checkSplitK (k : ℕ) : Bool :=
  let sp := splitAtAnd k gsShared44_304
  let pre304 := sp.1
  let rem304 := sp.2
  let undo304 := undoLt48 pre304
  let pre189 := pre304.map (mapGateN f304To189Nat)
  let undo189 := undo304.map (mapGateN f304To189Nat)
  let remSuf189 := (rem304 ++ gsSufFwd304).map (mapGateN f304To189Nat)
  let pre172 := pre304.map (mapGateN f304To172Nat)
  let undo172 := undo304.map (mapGateN f304To172Nat)
  let remSuf172 := (rem304 ++ gsSufUnld304).map (mapGateN f304To172Nat)
  let sH := sMaskHoldNat k
  let sTF := sMaskTailFwd k
  let sTU := sMaskTailUnld k
  validProgMask0Fast sH (pHoldProg k) &&
  ((pHoldProg k).numAnd == k) &&
  ((List.range 48).all fun i ↦ !sH.testBit i) &&
  okHoldGN (48 + k) (gsHoldPre k) &&
  validProgMask0Fast sTF (pTailFwdProg k) &&
  ((pTailFwdProg k).numAnd == 54 - k) &&
  ((List.range 189).all fun i ↦
    if sTF.testBit i then
      Nat.ble 48 i && Nat.ble k (inv141 ⟨(i - 48) % 141, Nat.mod_lt _ (by decide)⟩).val
    else true) &&
  beqGateList ((gsHold k).map (mapGateN holdTo189Nat)) (pre189 ++ undo189) &&
  beqGateList (gsTailFwd k) (undo189.reverse ++ remSuf189) &&
  undo189.all (isCliffWf 189) &&
  beqGateList (pre189 ++ remSuf189) gsCombFwd189 &&
  validProgMask0Fast sTU (pTailUnldProg k) &&
  ((pTailUnldProg k).numAnd == 54 - k) &&
  ((List.range 172).all fun i ↦
    if sTU.testBit i then
      Nat.ble 48 i && Nat.ble k (inv124 ⟨(i - 48) % 124, Nat.mod_lt _ (by decide)⟩).val
    else true) &&
  beqGateList ((gsHold k).map (mapGateN holdTo172Nat)) (pre172 ++ undo172) &&
  beqGateList (gsTailUnld k) (undo172.reverse ++ remSuf172) &&
  undo172.all (isCliffWf 172) &&
  beqGateList (pre172 ++ remSuf172) gsCombUnld172

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem allSplits44_cert :
    ((List.range 44).all fun j ↦ checkSplitK (j + 1)) = true := by decide +kernel

theorem checkSplitK_of_bounds {k : ℕ} (hk1 : 1 ≤ k) (hk44 : k ≤ 44) :
    checkSplitK k = true := by
  have hj : k - 1 ∈ List.range 44 := List.mem_range.mpr (by omega)
  have h := (List.all_eq_true.mp allSplits44_cert) (k - 1) hj
  have heq : k - 1 + 1 = k := by omega
  rw [heq] at h
  exact h


-- ============================================================================
-- Section 4: `midFwd189`, `midUnld172`, Ghost-`st0` Bridge, & `dist18HeldSplitPkg`
-- ============================================================================

/-- Inner `330-T` forward `Dist18` core (triple `SplitR` + `0-T` prep + `bennettXorReg`). -/
noncomputable def midFwd189 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r189 : QRegister 189 n) (rTgt : QRegister 18 n)
    (hDisj : r189.DisjointWires rTgt) : DynamicCircuit Var n :=
  pSplitR2OnReg v r189 wsAx0Fwd189 wsAx0Fwd189_inj
    (pSplitR2OnReg v r189 wsAx1Fwd189 wsAx1Fwd189_inj
      (pSplitR2OnReg v r189 wsAx2Fwd189 wsAx2Fwd189_inj
        (wrapDynOnReg v r189 pPrepClean108_189
          (bennettXorReg v r189 pInnerFwd189 d2WireFwd189 rTgt hDisj))))

theorem midFwd189_step
    {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (r189 : QRegister 189 n) (rTgt : QRegister 18 n)
    (hDisj : r189.DisjointWires rTgt)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (valFn : BitAssignment n → ℕ)
    (hCln48 : ∀ (δ : BitAssignment n) (u : Wire 189),
      48 ≤ u.val → (∀ q : Fin W, δ (rWork q) = 0) → st δ (r189 u) = 0)
    (hVal : ∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
      (∑ ax : Fin 3,
        (twosComplement_frozen
            (byteOfBits (fun k : Fin 8 ↦ st δ (r189 ⟨8 * ax.val + k.val, by omega⟩))) -
         twosComplement_frozen
            (byteOfBits
              (fun k : Fin 8 ↦ st δ (r189 ⟨24 + 8 * ax.val + k.val, by omega⟩)))).natAbs ^ 2) =
        valFn δ) :
    let g (δ : BitAssignment n) (j : Fin 18) : ZMod 2 :=
      st δ (rTgt j) + if (valFn δ).testBit j.val then 1 else 0
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ stepCB r189 pOuterFwd189.fwdBits (st δ)) ph)
      (mkKetOpW rWork (fun δ ↦ stepCB r189 pOuterFwd189.fwdBits (writeReg (st δ) rTgt (g δ))) ph)
      (midFwd189 v r189 rTgt hDisj) ∧
    (midFwd189 v r189 rTgt hDisj).count .T = 330 ∧
    (midFwd189 v r189 rTgt hDisj).count .TOFF = 0 ∧
    (∀ S : Wire n → Prop,
      (∀ u, S (r189 u)) → (∀ j, S (rTgt j)) →
      DynWires S (midFwd189 v r189 rTgt hDisj)) := by
  intro g
  let st1 (δ : BitAssignment n) := stepCB r189 pOuterFwd189.fwdBits (st δ)
  let st2 (δ : BitAssignment n) := stepCB r189 (pSplitR2EquivK wsAx0Fwd189).fwdBits (st1 δ)
  let st3 (δ : BitAssignment n) := stepCB r189 (pSplitR2EquivK wsAx1Fwd189).fwdBits (st2 δ)
  let st4 (δ : BitAssignment n) := stepCB r189 (pSplitR2EquivK wsAx2Fwd189).fwdBits (st3 δ)
  let st5 (δ : BitAssignment n) := stepCB r189 pPrepClean108_189.fwdBits (st4 δ)
  have hNotTgt : ∀ u : Wire 189, ¬∃ j : Fin 18, rTgt j = r189 u :=
    fun u ⟨j, hj⟩ ↦ disj_ne hDisj u j hj.symm
  have hNot189 : ∀ j : Fin 18, ¬∃ u : Wire 189, r189 u = rTgt j :=
    fun j ⟨u, hu⟩ ↦ disj_ne hDisj u j hu
  have hComm (f : BitAssignment 189 → BitAssignment 189) (s : BitAssignment n → BitAssignment n) :
      (fun δ ↦ stepCB r189 f (writeReg (s δ) rTgt (g δ))) =
        (fun δ ↦ writeReg (stepCB r189 f (s δ)) rTgt (g δ)) :=
    funext fun δ ↦ PotOracleGen.stepCB_writeReg_comm r189 rTgt hDisj f (g δ) (s δ)
  have hKeep {s : BitAssignment n → BitAssignment n} (δ : BitAssignment n)
      (_ : ∀ q : Fin W, δ (rWork q) = 0) (u : Wire 189) :
      writeReg (s δ) rTgt (g δ) (r189 u) = s δ (r189 u) :=
    writeReg_apply_of_not_mem _ _ _ _ (hNotTgt u)
  have hProps (δ : BitAssignment n) (hz : ∀ q : Fin W, δ (rWork q) = 0) :=
    pGhostFwd189_props (fun q ↦ st δ (r189 q)) (fun u hu ↦ hCln48 δ u hu hz)
  have hst5_reg (δ : BitAssignment n) (u : Wire 189) :
      st5 δ (r189 u) = preInnerFwd189.fwdBits (fun q ↦ st δ (r189 q)) u := by
    dsimp only [st5, st4, st3, st2, st1, preInnerFwd189]
    rw [stepCB_seq, stepCB_seq, stepCB_seq, stepCB_seq, stepCB_apply_reg]
    rfl
  have hInner := bennettXorReg_step_of_spec v rWork r189 sMaskInnerFwd189 pInnerFwd189
    pInnerFwd189_certs.2 d2WireFwd189 rTgt hDisj st5 ph valFn 78 pInnerFwd189_certs.1
    (fun u hu δ hz ↦ by
      rw [hst5_reg δ u]
      by_cases hu107 : u = ⟨107, by decide⟩
      · subst hu107
        exact (hProps δ hz).2.2.2.1
      · rw [noWriteK_fwd u _ (preInnerFwd189_noWrite u hu hu107)]
        exact hCln48 δ u (sMaskInnerFwd189_ge48 u hu) hz)
    (fun δ hz j ↦ by
      have hgh : pInnerFwd189.fwdBits (fun u ↦ st5 δ (r189 u)) =
          pGhostFwd189.fwdBits (fun q ↦ st δ (r189 q)) := by
        rw [funext (hst5_reg δ)]
        rfl
      rw [hgh, finBitsVal_testBit
        (fun k : Fin 18 ↦ pGhostFwd189.fwdBits (fun q ↦ st δ (r189 q)) (d2WireFwd189 k)) j,
        (hProps δ hz).2.2.2.2, hVal δ hz])
  have hPrep := subspaceStep_wrapOnReg_zeroAnd v rWork r189 pPrepClean108_189
    pPrepClean108_189_certs.2 pPrepClean108_189_certs.1
    st4 (fun δ ↦ writeReg (st4 δ) rTgt (g δ)) ph ph _ (by
      rw [hComm]
      refine subspaceStep_congr_out hInner.1 (mkKetOpW_congr rWork (fun δ _ ↦ ?_) (fun _ _ ↦ rfl))
      congr 1
      funext j
      dsimp only [st5, st4, st3, st2, st1]
      repeat rw [stepCB_apply_of_not_mem _ _ _ _ (hNot189 j)])
  have split7 {P1 P2 P3 P4 P5 P6 P7 : Prop} (h : P1 ∧ P2 ∧ P3 ∧ P4 ∧ P5 ∧ P6 ∧ P7) :
      (P1 ∧ P2 ∧ P3 ∧ P4 ∧ P5) ∧ (P6 ∧ P7) :=
    ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have hr3 (δ : BitAssignment n) (k : Fin 10) : st3 δ (r189 (wsAx2Fwd189 k)) =
      (pSplitR2EquivK wsAx1Fwd189).fwdBits ((pSplitR2EquivK wsAx0Fwd189).fwdBits
        (pOuterFwd189.fwdBits (fun q ↦ st δ (r189 q)))) (wsAx2Fwd189 k) := by
    dsimp only [st3, st2, st1]
    rw [stepCB_seq, stepCB_seq, stepCB_apply_reg]
  have hSp2 := step_counts_wires_splitR2OnReg v rWork r189 wsAx2Fwd189 wsAx2Fwd189_inj
    (fun x y ↦ x * (1 + y)) (fun x y ↦ x * y) zmod2_mut_branch_ax2
    st3 (fun δ ↦ writeReg (st3 δ) rTgt (g δ)) ph ph _
    (fun δ hz ↦ by
      simp only [hr3]
      exact (split7 (hProps δ hz).2.2.1).1)
    (fun δ hz ↦ by
      simp only [hr3]
      exact (split7 (hProps δ hz).2.2.1).2)
    hKeep (by
      rw [hComm]
      exact hPrep.1)
  have hr2 (δ : BitAssignment n) (k : Fin 10) : st2 δ (r189 (wsAx1Fwd189 k)) =
      (pSplitR2EquivK wsAx0Fwd189).fwdBits
        (pOuterFwd189.fwdBits (fun q ↦ st δ (r189 q))) (wsAx1Fwd189 k) := by
    dsimp only [st2, st1]
    rw [stepCB_seq, stepCB_apply_reg]
  have hSp1 := step_counts_wires_splitR2OnReg v rWork r189 wsAx1Fwd189 wsAx1Fwd189_inj
    (fun x _ ↦ 1 + x) (fun x y ↦ x * y) zmod2_mut_branch01
    st2 (fun δ ↦ writeReg (st2 δ) rTgt (g δ)) ph ph _
    (fun δ hz ↦ by
      simp only [hr2]
      exact (split7 (hProps δ hz).2.1).1)
    (fun δ hz ↦ by
      simp only [hr2]
      exact (split7 (hProps δ hz).2.1).2)
    hKeep (by
      rw [hComm]
      exact hSp2.1)
  have hr1 (δ : BitAssignment n) (k : Fin 10) : st1 δ (r189 (wsAx0Fwd189 k)) =
      pOuterFwd189.fwdBits (fun q ↦ st δ (r189 q)) (wsAx0Fwd189 k) :=
    stepCB_apply_reg r189 pOuterFwd189.fwdBits (st δ) (wsAx0Fwd189 k)
  have hSp0 := step_counts_wires_splitR2OnReg v rWork r189 wsAx0Fwd189 wsAx0Fwd189_inj
    (fun x _ ↦ 1 + x) (fun x y ↦ x * y) zmod2_mut_branch01
    st1 (fun δ ↦ writeReg (st1 δ) rTgt (g δ)) ph ph _
    (fun δ hz ↦ by
      simp only [hr1]
      exact (split7 (hProps δ hz).1).1)
    (fun δ hz ↦ by
      simp only [hr1]
      exact (split7 (hProps δ hz).1).2)
    hKeep (by
      rw [hComm]
      exact hSp1.1)
  refine ⟨?_, ?_, ?_, fun S h189 hT ↦
    hSp0.2.2.2 S h189 (hSp1.2.2.2 S h189
      (hSp2.2.2.2 S h189 (hPrep.2.2.2 S h189 (hInner.2.2.2 S h189 hT))))⟩
  · dsimp only [midFwd189]
    rw [hComm]
    exact hSp0.1
  · rw [midFwd189, hSp0.2.1, hSp1.2.1, hSp2.2.1, hPrep.2.1, hInner.2.1]
  · rw [midFwd189, hSp0.2.2.1, hSp1.2.2.1, hSp2.2.2.1, hPrep.2.2.1, hInner.2.2.1]

/-- Inner `260-T` unload `Dist18` core (double `SplitR` + `0-T` prep + `62`-AND `quadCoreGen`). -/
def midUnld172 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r172 : QRegister 172 n) (rTgt : QRegister 18 n)
    (hDisj : r172.DisjointWires rTgt) : DynamicCircuit Var n :=
  pSplitR2OnReg v r172 wsAx1Unld172 wsAx1Unld172_inj
    (pSplitR2OnReg v r172 wsAx2Unld172 wsAx2Unld172_inj
      (wrapDynOnReg v r172 pPrepClean108_172
        (quadCoreGen hB18_quad pInnerUnld172 (dist18P26KaraShaPairs r172 rTgt hDisj) v r172 rTgt)))

theorem midUnld172_step
    {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (r172 : QRegister 172 n) (rTgt : QRegister 18 n)
    (hDisj : r172.DisjointWires rTgt)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (valFn : BitAssignment n → ℕ)
    (hCln48 : ∀ (δ : BitAssignment n) (u : Wire 172),
      48 ≤ u.val → (∀ q : Fin W, δ (rWork q) = 0) → st δ (r172 u) = 0)
    (hTgt0 : ∀ (δ : BitAssignment n) (j : Fin 18),
      (∀ q : Fin W, δ (rWork q) = 0) → st δ (rTgt j) = 0)
    (hVal : ∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
      (∑ ax : Fin 3,
        (twosComplement_frozen
            (byteOfBits (fun k : Fin 8 ↦ st δ (r172 ⟨8 * ax.val + k.val, by omega⟩))) -
         twosComplement_frozen
            (byteOfBits
              (fun k : Fin 8 ↦ st δ (r172 ⟨24 + 8 * ax.val + k.val, by omega⟩)))).natAbs ^ 2) =
        valFn δ) :
    let g (δ : BitAssignment n) (j : Fin 18) : ZMod 2 :=
      if (valFn δ).testBit j.val then 1 else 0
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ stepCB r172 pOuterUnld172.fwdBits (writeReg (st δ) rTgt (g δ))) ph)
      (mkKetOpW rWork (fun δ ↦ stepCB r172 pOuterUnld172.fwdBits (st δ)) ph)
      (midUnld172 v r172 rTgt hDisj) ∧
    (midUnld172 v r172 rTgt hDisj).count .T = 260 ∧
    (midUnld172 v r172 rTgt hDisj).count .TOFF = 0 ∧
    (∀ S : Wire n → Prop,
      (∀ u, S (r172 u)) → (∀ j, S (rTgt j)) →
      DynWires S (midUnld172 v r172 rTgt hDisj)) := by
  intro g
  let st1 (δ : BitAssignment n) := stepCB r172 pOuterUnld172.fwdBits (st δ)
  let st2 (δ : BitAssignment n) := stepCB r172 (pSplitR2EquivK wsAx1Unld172).fwdBits (st1 δ)
  let st3 (δ : BitAssignment n) := stepCB r172 (pSplitR2EquivK wsAx2Unld172).fwdBits (st2 δ)
  let st4 (δ : BitAssignment n) := stepCB r172 pPrepClean108_172.fwdBits (st3 δ)
  have hNotTgt : ∀ u : Wire 172, ¬∃ j : Fin 18, rTgt j = r172 u :=
    fun u ⟨j, hj⟩ ↦ disj_ne hDisj u j hj.symm
  have hNot172 : ∀ j : Fin 18, ¬∃ u : Wire 172, r172 u = rTgt j :=
    fun j ⟨u, hu⟩ ↦ disj_ne hDisj u j hu
  have hComm (f : BitAssignment 172 → BitAssignment 172) (s : BitAssignment n → BitAssignment n) :
      (fun δ ↦ stepCB r172 f (writeReg (s δ) rTgt (g δ))) =
        (fun δ ↦ writeReg (stepCB r172 f (s δ)) rTgt (g δ)) :=
    funext fun δ ↦ PotOracleGen.stepCB_writeReg_comm r172 rTgt hDisj f (g δ) (s δ)
  have hKeep {s : BitAssignment n → BitAssignment n} (δ : BitAssignment n)
      (_ : ∀ q : Fin W, δ (rWork q) = 0) (u : Wire 172) :
      s δ (r172 u) = writeReg (s δ) rTgt (g δ) (r172 u) :=
    (writeReg_apply_of_not_mem _ _ _ _ (hNotTgt u)).symm
  have hProps (δ : BitAssignment n) (hz : ∀ q : Fin W, δ (rWork q) = 0) :=
    dist18P26KaraSha_parity_local (fun q ↦ st δ (r172 q)) (fun u hu ↦ hCln48 δ u hu hz)
  have hst4_reg (δ : BitAssignment n) (u : Wire 172) :
      st4 δ (r172 u) = preInnerUnld172.fwdBits (fun q ↦ st δ (r172 q)) u := by
    dsimp only [st4, st3, st2, st1, preInnerUnld172]
    rw [stepCB_seq, stepCB_seq, stepCB_seq, stepCB_apply_reg]
    rfl
  have hInner := subspaceStep_quadCoreLiveGen (nAnd := 62) hB18_quad v rWork r172 rTgt hDisj
    sMaskInnerUnld172 pInnerUnld172 pInnerUnld172_certs.2 pInnerUnld172_certs.1
    (dist18P26KaraShaPairs r172 rTgt hDisj)
    (dist18P26KaraShaPairs_mem r172 rTgt hDisj) st4 ph valFn
    (fun u hu δ hz ↦ by
      rw [hst4_reg δ u]
      by_cases hu106 : u = ⟨106, by decide⟩
      · subst hu106
        exact (hProps δ hz).2.2.1
      · rw [noWriteK_fwd u _ (preInnerUnld172_noWrite u hu hu106)]
        exact hCln48 δ u (sMaskInnerUnld172_ge48 u hu) hz)
    (fun δ j hz ↦ by
      dsimp only [st4, st3, st2, st1]
      repeat rw [stepCB_apply_of_not_mem _ _ _ _ (hNot172 j)]
      exact hTgt0 δ j hz)
    (fun δ hz j ↦ by
      have hgh : pInnerUnld172.fwdBits (fun u ↦ st4 δ (r172 u)) =
          pGhostP26Unld172.fwdBits (fun q ↦ st δ (r172 q)) := by
        rw [funext (hst4_reg δ)]
        rfl
      rw [czPairsParity_dist18P26KaraShaPairs_aux r172 rTgt hDisj pInnerUnld172.fwdBits (st4 δ)
        (fun i ↦ if (valFn δ).testBit i then 1 else 0) j, hgh]
      have hp := (hProps δ hz).2.2.2 j
      rwa [hVal δ hz] at hp)
  have hPrep := subspaceStep_wrapOnReg_zeroAnd v rWork r172 pPrepClean108_172
    pPrepClean108_172_certs.2 pPrepClean108_172_certs.1
    (fun δ ↦ writeReg (st3 δ) rTgt (g δ)) st3 ph ph _ (by
      rw [hComm]
      exact hInner.1)
  have split7 {P1 P2 P3 P4 P5 P6 P7 : Prop} (h : P1 ∧ P2 ∧ P3 ∧ P4 ∧ P5 ∧ P6 ∧ P7) :
      (P1 ∧ P2 ∧ P3 ∧ P4 ∧ P5) ∧ (P6 ∧ P7) :=
    ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  have hr2 (δ : BitAssignment n) (k : Fin 10) :
      writeReg (st2 δ) rTgt (g δ) (r172 (wsAx2Unld172 k)) =
        (pSplitR2EquivK wsAx1Unld172).fwdBits
          (pOuterUnld172.fwdBits (fun q ↦ st δ (r172 q))) (wsAx2Unld172 k) :=
    (writeReg_apply_of_not_mem _ _ _ _ (hNotTgt _)).trans (by
      dsimp only [st2, st1]
      rw [stepCB_seq, stepCB_apply_reg])
  have hSp2 := step_counts_wires_splitR2OnReg v rWork r172 wsAx2Unld172 wsAx2Unld172_inj
    (fun x y ↦ x * (1 + y)) (fun x y ↦ x * y) zmod2_mut_branch_ax2
    (fun δ ↦ writeReg (st2 δ) rTgt (g δ)) st2 ph ph _
    (fun δ hz ↦ by
      simp only [hr2]
      exact (split7 (hProps δ hz).2.1).1)
    (fun δ hz ↦ by
      simp only [hr2]
      exact (split7 (hProps δ hz).2.1).2)
    hKeep (by
      rw [hComm]
      exact hPrep.1)
  have hr1 (δ : BitAssignment n) (k : Fin 10) :
      writeReg (st1 δ) rTgt (g δ) (r172 (wsAx1Unld172 k)) =
        pOuterUnld172.fwdBits (fun q ↦ st δ (r172 q)) (wsAx1Unld172 k) :=
    (writeReg_apply_of_not_mem _ _ _ _ (hNotTgt _)).trans
      (stepCB_apply_reg r172 pOuterUnld172.fwdBits (st δ) (wsAx1Unld172 k))
  have hSp1 := step_counts_wires_splitR2OnReg v rWork r172 wsAx1Unld172 wsAx1Unld172_inj
    (fun x _ ↦ 1 + x) (fun x y ↦ x * y) zmod2_mut_branch01
    (fun δ ↦ writeReg (st1 δ) rTgt (g δ)) st1 ph ph _
    (fun δ hz ↦ by
      simp only [hr1]
      exact (split7 (hProps δ hz).1).1)
    (fun δ hz ↦ by
      simp only [hr1]
      exact (split7 (hProps δ hz).1).2)
    hKeep (by
      rw [hComm]
      exact hSp2.1)
  refine ⟨?_, ?_, ?_, fun S h172 hT ↦
    hSp1.2.2.2 S h172 (hSp2.2.2.2 S h172 (hPrep.2.2.2 S h172 (hInner.2.2.2 S h172 hT)))⟩
  · dsimp only [midUnld172]
    rw [hComm]
    exact hSp1.1
  · rw [midUnld172, hSp1.2.1, hSp2.2.1, hPrep.2.1, hInner.2.1]
  · rw [midUnld172, hSp1.2.2.1, hSp2.2.2.1, hPrep.2.2.1, hInner.2.2.1]

attribute [irreducible] midFwd189 midUnld172

/-- Assemble the `189`-wire forward frame from `(rA, rB, rHold, rScr)` using `inv141`. -/
def fReg189 {k n : ℕ} (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister (141 - k) n) (u : Fin 189) : Wire n :=
  if h0 : u.val < 24 then rA ⟨u.val, h0⟩
  else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
  else
    let idx := inv141 ⟨u.val - 48, by omega⟩
    if hk : idx.val < k then rHold ⟨idx.val, hk⟩
    else rScr ⟨idx.val - k, by omega⟩

/-- Assemble the `172`-wire unload frame from `(rA, rB, rHold, rScr)` using `inv124`. -/
def fReg172 {k n : ℕ} (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister (124 - k) n) (u : Fin 172) : Wire n :=
  if h0 : u.val < 24 then rA ⟨u.val, h0⟩
  else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
  else
    let idx := inv124 ⟨u.val - 48, by omega⟩
    if hk : idx.val < k then rHold ⟨idx.val, hk⟩
    else rScr ⟨idx.val - k, by omega⟩

theorem fRegGen_inj {M S k n : ℕ} (hMS : 48 + S = M)
    (inv ord : Fin S → Fin S) (hlinv : ∀ i, ord (inv i) = i)
    {rA rB : QRegister 24 n} {rHold : QRegister k n} {rScr : QRegister (S - k) n}
    (dAB : rA.DisjointWires rB) (dAH : rA.DisjointWires rHold) (dAS : rA.DisjointWires rScr)
    (dBH : rB.DisjointWires rHold) (dBS : rB.DisjointWires rScr) (dHS : rHold.DisjointWires rScr)
    (fReg : Fin M → Wire n)
    (hf : ∀ u : Fin M, fReg u =
      if h0 : u.val < 24 then rA ⟨u.val, h0⟩
      else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
      else
        let idx := inv ⟨u.val - 48, by omega⟩
        if hk : idx.val < k then rHold ⟨idx.val, hk⟩ else rScr ⟨idx.val - k, by omega⟩) :
    Function.Injective fReg := by
  intro x y e
  apply Fin.ext
  rw [hf x, hf y] at e
  dsimp only at e
  split_ifs at e <;> try first
    | exact absurd e (disj_ne dAB _ _) | exact absurd e.symm (disj_ne dAB _ _)
    | exact absurd e (disj_ne dAH _ _) | exact absurd e.symm (disj_ne dAH _ _)
    | exact absurd e (disj_ne dAS _ _) | exact absurd e.symm (disj_ne dAS _ _)
    | exact absurd e (disj_ne dBH _ _) | exact absurd e.symm (disj_ne dBH _ _)
    | exact absurd e (disj_ne dBS _ _) | exact absurd e.symm (disj_ne dBS _ _)
    | exact absurd e (disj_ne dHS _ _) | exact absurd e.symm (disj_ne dHS _ _)
  · simpa using congrArg Fin.val (rA.wires.injective e)
  · have hv := congrArg Fin.val (rB.wires.injective e)
    dsimp at hv
    omega
  · have ho := congrArg (fun z ↦ (ord z).val)
      (Fin.ext (congrArg (Fin.val : Fin k → ℕ) (rHold.wires.injective e)) :
        inv ⟨x.val - 48, by omega⟩ = inv ⟨y.val - 48, by omega⟩)
    rw [hlinv, hlinv] at ho
    dsimp at ho
    omega
  · have hvs := congrArg Fin.val (rScr.wires.injective e)
    dsimp at hvs
    have ho := congrArg (fun z ↦ (ord z).val)
      (Fin.ext (by omega) : inv ⟨x.val - 48, by omega⟩ = inv ⟨y.val - 48, by omega⟩)
    rw [hlinv, hlinv] at ho
    dsimp at ho
    omega

theorem fReg189_inj {k n : ℕ} {rA rB : QRegister 24 n} {rHold : QRegister k n}
    {rScr : QRegister (141 - k) n}
    (dAB : rA.DisjointWires rB) (dAH : rA.DisjointWires rHold) (dAS : rA.DisjointWires rScr)
    (dBH : rB.DisjointWires rHold) (dBS : rB.DisjointWires rScr) (dHS : rHold.DisjointWires rScr) :
    Function.Injective (fReg189 rA rB rHold rScr) :=
  fRegGen_inj rfl inv141 ord141 inv141_leftInv dAB dAH dAS dBH dBS dHS _ fun _ ↦ rfl

theorem fReg172_inj {k n : ℕ} {rA rB : QRegister 24 n} {rHold : QRegister k n}
    {rScr : QRegister (124 - k) n}
    (dAB : rA.DisjointWires rB) (dAH : rA.DisjointWires rHold) (dAS : rA.DisjointWires rScr)
    (dBH : rB.DisjointWires rHold) (dBS : rB.DisjointWires rScr) (dHS : rHold.DisjointWires rScr) :
    Function.Injective (fReg172 rA rB rHold rScr) :=
  fRegGen_inj rfl inv124 ord124 inv124_leftInv dAB dAH dAS dBH dBS dHS _ fun _ ↦ rfl

/-- Held-prefix forward `Dist18` circuit (`(546 - 4 * k) T`). -/
noncomputable def progFwdHeld (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister (141 - k) n) (rTgt : QRegister 18 n) : DynamicCircuit Var n :=
  let fn := fReg189 rA rB rHold rScr
  @dite _ (Function.Injective fn) (Classical.dec _) (fun hinj ↦
    let r189 : QRegister 189 n := ⟨⟨fn, hinj⟩⟩
    @dite _ (r189.DisjointWires rTgt) (Classical.dec _)
      (fun hd ↦ wrapDynOnReg v r189 (pTailFwdProg k) (midFwd189 v r189 rTgt hd))
      (fun _ ↦ .circuit .identity))
    (fun _ ↦ .circuit .identity)

/-- Held-prefix unload `Dist18` circuit (`(476 - 4 * k) T`). -/
noncomputable def progUnldHeld (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister (124 - k) n) (rTgt : QRegister 18 n) : DynamicCircuit Var n :=
  let fn := fReg172 rA rB rHold rScr
  @dite _ (Function.Injective fn) (Classical.dec _) (fun hinj ↦
    let r172 : QRegister 172 n := ⟨⟨fn, hinj⟩⟩
    @dite _ (r172.DisjointWires rTgt) (Classical.dec _)
      (fun hd ↦ wrapDynOnReg v r172 (pTailUnldProg k) (midUnld172 v r172 rTgt hd))
      (fun _ ↦ .circuit .identity))
    (fun _ ↦ .circuit .identity)

theorem stepCB_tailGen_eq_outer {M S k n : ℕ} (hM : 0 < M) (hS : 0 < S)
    (h44S : 44 ≤ S) (hMS : 48 + S = M) (hk44 : k ≤ 44)
    (ord inv : Fin S → Fin S) (hOrdInv : ∀ i, inv (ord i) = i) (hInvOrd : ∀ i, ord (inv i) = i)
    (embHold : Fin (48 + k) → Wire M) (hinjEmb : Function.Injective embHold)
    (holdToNat f304ToNat : ℕ → ℕ) (gsSuf304 gsTail gsComb : List GateN) (pOuter : ComputeProg M)
    (hemb_lt : ∀ u : Fin (48 + k), u.val < 48 → (embHold u).val = u.val)
    (hemb_ge : ∀ u : Fin (48 + k), ¬ u.val < 48 →
      (embHold u).val = 48 + (ord ⟨(u.val - 48) % S, Nat.mod_lt _ hS⟩).val)
    (hemb_nat : ∀ u : Fin (48 + k), (embHold u).val = holdToNat u.val)
    (hCombEq : ∀ γ0 : BitAssignment M, (∀ u : Wire M, 48 ≤ u.val → γ0 u = 0) →
      (gatesToCP hM gsComb).fwdBits γ0 = pOuter.fwdBits γ0)
    (hOkH : okHoldGN (48 + k) (gsHoldPre k) = true)
    (bHold : beqGateList ((gsHold k).map (mapGateN holdToNat))
      ((splitAtAnd k gsShared44_304).1.map (mapGateN f304ToNat) ++
        (undoLt48 (splitAtAnd k gsShared44_304).1).map (mapGateN f304ToNat)) = true)
    (bTail : beqGateList gsTail
      (((undoLt48 (splitAtAnd k gsShared44_304).1).map (mapGateN f304ToNat)).reverse ++
        ((splitAtAnd k gsShared44_304).2 ++ gsSuf304).map (mapGateN f304ToNat)) = true)
    (hClf : ((undoLt48 (splitAtAnd k gsShared44_304).1).map (mapGateN f304ToNat)).all
      (isCliffWf M) = true)
    (bComb : beqGateList
      (((splitAtAnd k gsShared44_304).1).map (mapGateN f304ToNat) ++
        ((splitAtAnd k gsShared44_304).2 ++ gsSuf304).map (mapGateN f304ToNat)) gsComb = true)
    {rA rB : QRegister 24 n} {rHold : QRegister k n} {rScr : QRegister (S - k) n}
    (rM : QRegister M n)
    (hrM : ∀ u : Fin M, rM u =
      if h0 : u.val < 24 then rA ⟨u.val, h0⟩
      else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
      else
        let idx := inv ⟨u.val - 48, by omega⟩
        if hk : idx.val < k then rHold ⟨idx.val, hk⟩ else rScr ⟨idx.val - k, by omega⟩)
    (dAH : rA.DisjointWires rHold) (dBH : rB.DisjointWires rHold) (dHS : rHold.DisjointWires rScr)
    (β : BitAssignment n) (hScr : ∀ u : Fin (S - k), β (rScr u) = 0)
    (hHold : ∀ j : Fin k, β (rHold j) =
      (pHoldProg k).fwdBits
        (fun u ↦ if h : u.val < 48 then coord48Of rA rB β ⟨u.val, h⟩ else 0)
        ⟨48 + j.val, by omega⟩) :
    stepCB rM (gatesToCP hM gsTail).fwdBits β =
      stepCB rM pOuter.fwdBits (writeReg β rHold (fun _ ↦ 0)) := by
  let β0 := writeReg β rHold (fun _ ↦ 0)
  let γH : BitAssignment M := fun u ↦ β (rM u)
  let γ0 : BitAssignment M := fun u ↦ β0 (rM u)
  have hHoldMem (j : Fin k) : rHold j = rM (embHold ⟨48 + j.val, by omega⟩) := by
    let u0 : Fin (48 + k) := ⟨48 + j.val, by omega⟩
    let wS : Fin S := ord ⟨j.val, by omega⟩
    have : (embHold u0).val = 48 + wS.val :=
      (hemb_ge u0 (Nat.not_lt.mpr (Nat.le_add_right 48 j.val))).trans
        (congrArg (fun x : Fin S ↦ 48 + x.val) (congrArg ord (Fin.ext (by
          dsimp [u0]
          rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt (by omega)]))))
    rw [hrM (embHold u0), pDiteNeg (by omega), pDiteNeg (by omega)]
    have hidx_val : (inv ⟨(embHold u0).val - 48, by omega⟩).val = j.val :=
      congrArg Fin.val ((congrArg inv (Fin.ext (by
        dsimp
        omega) : (⟨(embHold u0).val - 48, by omega⟩ : Fin S) =
            wS)).trans (hOrdInv ⟨j.val, by omega⟩))
    dsimp only
    rw [pDitePos (Nat.lt_of_le_of_lt (Nat.le_of_eq hidx_val) j.isLt)]
    exact congrArg rHold.wires (Fin.ext hidx_val.symm)
  have hγ0_cln (u : Wire M) (hu : 48 ≤ u.val) : γ0 u = 0 := by
    dsimp only [γ0, β0]
    rw [hrM u, pDiteNeg (by omega), pDiteNeg (by omega)]
    dsimp only
    split_ifs with hk
    · exact writeReg_apply_reg β rHold (fun _ ↦ 0) _
    · exact (writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨q, hq⟩ ↦
          disj_ne dHS q _ hq)).trans (hScr _)
  have hγM_eq : (mapCP embHold (pHoldProg k)).fwdBits γ0 = γH := funext fun u ↦ by
    by_cases hu48 : u.val < 48
    · have hu_emb : embHold ⟨u.val, by omega⟩ = u := Fin.ext (hemb_lt ⟨u.val, by omega⟩ hu48)
      rw [← hu_emb, mapCP_fwd_apply embHold hinjEmb (pHoldProg k) γ0]
      dsimp only [pHoldProg, gsHold]
      rw [exec_append_undo_coords (by omega) (gsHoldPre k) hOkH _ ⟨u.val, hu48⟩]
      change γ0 (embHold ⟨u.val, by omega⟩) = γH (embHold ⟨u.val, by omega⟩)
      rw [hu_emb]
      dsimp only [γ0, γH, β0]
      rw [hrM u]
      by_cases hu24 : u.val < 24
      · simp only [hu24, ↓reduceDIte]
        exact writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨j, hj⟩ ↦ disj_ne dAH _ j hj.symm)
      · simp only [hu24, hu48, ↓reduceDIte]
        exact writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨j, hj⟩ ↦ disj_ne dBH _ j hj.symm)
    · let idx := inv ⟨u.val - 48, by omega⟩
      by_cases hk : idx.val < k
      · have hu_emb : embHold ⟨48 + idx.val, by omega⟩ = u := Fin.ext (by
          rw [hemb_ge _ (Nat.not_lt.mpr (Nat.le_add_right 48 idx.val)),
              show (⟨(48 + idx.val - 48) % S, Nat.mod_lt _ hS⟩ : Fin S) = idx from Fin.ext (by
                dsimp
                rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt idx.isLt]),
              hInvOrd ⟨u.val - 48, by omega⟩]
          dsimp
          omega)
        rw [← hu_emb, mapCP_fwd_apply embHold hinjEmb (pHoldProg k) γ0,
            show (fun q : Fin (48 + k) ↦ γ0 (embHold q)) =
                (fun q : Fin (48 + k) ↦ if h : q.val < 48 then coord48Of rA rB β ⟨q.val,
                    h⟩ else 0) from
              funext fun q ↦ by
                by_cases hq : q.val < 48
                · simp only [hq, ↓reduceDIte]
                  dsimp only [γ0, β0, coord48Of]
                  rw [show embHold q = ⟨q.val, by omega⟩ from Fin.ext (hemb_lt q hq),
                      hrM ⟨q.val, by omega⟩]
                  by_cases hq24 : q.val < 24
                  · simp only [hq24, ↓reduceDIte]
                    exact writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨j, hj⟩ ↦
                        disj_ne dAH _ j hj.symm)
                  · simp only [hq24, hq, ↓reduceDIte]
                    exact writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨j, hj⟩ ↦
                        disj_ne dBH _ j hj.symm)
                · simp only [hq, ↓reduceDIte]
                  exact hγ0_cln _ (by
                    rw [hemb_ge q hq]
                    omega)]
        have hr_eq := hHoldMem ⟨idx.val, hk⟩
        rw [hu_emb] at hr_eq
        dsimp only [γH]
        rw [hu_emb, ← hr_eq, hHold ⟨idx.val, hk⟩]
      · rw [mapCP_fwd_outside embHold hinjEmb (pHoldProg k) γ0 u (fun q e ↦ by
            have hv := congrArg Fin.val e
            by_cases hq : q.val < 48
            · rw [hemb_lt q hq] at hv
              omega
            · rw [hemb_ge q hq] at hv
              have hi := congrArg inv (Fin.ext (by
                dsimp
                omega) : ord ⟨(q.val - 48) % S, Nat.mod_lt _ hS⟩ = ⟨u.val - 48, by omega⟩)
              rw [hOrdInv] at hi
              have hiv : idx.val = (q.val - 48) % S := (congrArg Fin.val hi).symm
              rw [Nat.mod_eq_of_lt (by omega)] at hiv
              omega)]
        dsimp only [γ0, γH, β0]
        rw [hrM u, pDiteNeg (by omega), pDiteNeg hu48]
        dsimp only
        rw [pDiteNeg hk]
        exact writeReg_apply_of_not_mem _ rHold _ (rScr ⟨idx.val - k, by omega⟩)
          (fun ⟨j, hj⟩ ↦ disj_ne dHS j ⟨idx.val - k, by omega⟩ hj)
  let sp := splitAtAnd k gsShared44_304
  let preM := sp.1.map (mapGateN f304ToNat)
  let undoM := (undoLt48 sp.1).map (mapGateN f304ToNat)
  let remSufM := (sp.2 ++ gsSuf304).map (mapGateN f304ToNat)
  have hwfp := okHoldGN_wf (gsHoldPre k) hOkH
  have hMapEq := mapCP_gatesToCP_eq (by omega) hM embHold holdToNat hemb_nat (gsHold k) (by
    rw [gsHold, List.all_append, Bool.and_eq_true]
    exact ⟨hwfp, undoLt48_wf (gsHoldPre k) hwfp⟩)
  change mapCP embHold (pHoldProg k) = _ at hMapEq
  funext w
  by_cases hw : ∃ u : Wire M, rM u = w
  · obtain ⟨u, rfl⟩ := hw
    rw [stepCB_apply_reg, stepCB_apply_reg]
    exact congrFun (show (gatesToCP hM gsTail).fwdBits γH = pOuter.fwdBits γ0 by
      rw [← hγM_eq, hMapEq, beqGateList_eq bHold, beqGateList_eq bTail,
          gatesToCP_append hM preM undoM γ0, gatesToCP_append hM undoM.reverse remSufM,
          cliff_redo_cancel hM undoM hClf, ← gatesToCP_append hM preM remSufM γ0,
              beqGateList_eq bComb]
      exact hCombEq γ0 hγ0_cln) u
  · rw [stepCB_apply_of_not_mem _ _ _ _ hw, stepCB_apply_of_not_mem _ _ _ _ hw]
    exact (writeReg_apply_of_not_mem β rHold (fun _ ↦ 0) w
      (fun ⟨j, hj⟩ ↦ hw ⟨embHold ⟨48 + j.val, by omega⟩, (hHoldMem j).symm.trans hj⟩)).symm

theorem writeReg_comm_disj {K1 K2 n : ℕ} (r1 : QRegister K1 n) (r2 : QRegister K2 n)
    (hd : r1.DisjointWires r2) (β : BitAssignment n)
    (f1 : Fin K1 → ZMod 2) (f2 : Fin K2 → ZMod 2) :
    writeReg (writeReg β r1 f1) r2 f2 = writeReg (writeReg β r2 f2) r1 f1 := by
  funext w
  by_cases h2 : ∃ j2 : Fin K2, r2 j2 = w
  · obtain ⟨j2, rfl⟩ := h2
    rw [writeReg_apply_reg,
        writeReg_apply_of_not_mem _ r1 _ _ (fun ⟨j1, hj⟩ ↦ disj_ne hd j1 j2 hj),
        writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ r2 _ _ h2]
    by_cases h1 : ∃ j1 : Fin K1, r1 j1 = w
    · obtain ⟨j1, rfl⟩ := h1
      rw [writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ r1 _ _ h1,
          writeReg_apply_of_not_mem _ r1 _ _ h1,
          writeReg_apply_of_not_mem _ r2 _ _ h2]

theorem fRegGen_disj_tgt {M S k KT n : ℕ} {hMS : 48 + S = M} (inv : Fin S → Fin S)
    {rA rB : QRegister 24 n} {rHold : QRegister k n} {rScr : QRegister (S - k) n}
    {rTgt : QRegister KT n} (rM : QRegister M n)
    (hrM : ∀ u : Fin M, rM u =
      if h0 : u.val < 24 then rA ⟨u.val, h0⟩
      else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
      else
        let idx := inv ⟨u.val - 48, by omega⟩
        if hk : idx.val < k then rHold ⟨idx.val, hk⟩ else rScr ⟨idx.val - k, by omega⟩)
    (dAT : rA.DisjointWires rTgt) (dBT : rB.DisjointWires rTgt)
    (dHT : rHold.DisjointWires rTgt) (dST : rScr.DisjointWires rTgt) :
    rM.DisjointWires rTgt :=
  disj_of_ne fun u j heq ↦ by
    rw [hrM u] at heq
    dsimp only at heq
    split_ifs at heq
    · exact disj_ne dAT _ _ heq
    · exact disj_ne dBT _ _ heq
    · exact disj_ne dHT _ _ heq
    · exact disj_ne dST _ _ heq

theorem fRegGen_cln48 {M S k n : ℕ} {hMS : 48 + S = M} (inv : Fin S → Fin S)
    {rA rB : QRegister 24 n} {rHold : QRegister k n} {rScr : QRegister (S - k) n}
    (rM : QRegister M n)
    (hrM : ∀ u : Fin M, rM u =
      if h0 : u.val < 24 then rA ⟨u.val, h0⟩
      else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
      else
        let idx := inv ⟨u.val - 48, by omega⟩
        if hk : idx.val < k then rHold ⟨idx.val, hk⟩ else rScr ⟨idx.val - k, by omega⟩)
    (dHS : rHold.DisjointWires rScr) (β : BitAssignment n)
    (hScr : ∀ u : Fin (S - k), β (rScr u) = 0) (u : Wire M) (hu : 48 ≤ u.val) :
    writeReg β rHold (fun _ ↦ 0) (rM u) = 0 := by
  rw [hrM u, pDiteNeg (by omega), pDiteNeg (by omega)]
  dsimp only
  split_ifs with hk
  · exact writeReg_apply_reg β rHold (fun _ ↦ 0) _
  · rw [writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨q, hq⟩ ↦ disj_ne dHS q _ hq)]
    exact hScr _

theorem fRegGen_val {M S k n : ℕ} (hMS : 48 + S = M) (inv : Fin S → Fin S)
    {rA rB : QRegister 24 n} {rHold : QRegister k n} {rScr : QRegister (S - k) n}
    (rM : QRegister M n)
    (hrM : ∀ u : Fin M, rM u =
      if h0 : u.val < 24 then rA ⟨u.val, h0⟩
      else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
      else
        let idx := inv ⟨u.val - 48, by omega⟩
        if hk : idx.val < k then rHold ⟨idx.val, hk⟩ else rScr ⟨idx.val - k, by omega⟩)
    (dAH : rA.DisjointWires rHold) (dBH : rB.DisjointWires rHold) (β : BitAssignment n) :
    (∑ ax : Fin 3,
      (twosComplement_frozen
          (byteOfBits (fun q : Fin 8 ↦
            writeReg β rHold (fun _ ↦ 0) (rM ⟨8 * ax.val + q.val, by omega⟩))) -
       twosComplement_frozen
          (byteOfBits (fun q : Fin 8 ↦
            writeReg β rHold (fun _ ↦ 0) (rM ⟨24 + 8 * ax.val + q.val, by omega⟩)))).natAbs ^ 2) =
      openCoordDistSq (coordOfReg24 rA β) (coordOfReg24 rB β) := by
  have hA (ax : Fin 3) :
      byteOfBits (fun q : Fin 8 ↦ writeReg β rHold (fun _ ↦ 0)
          (rM ⟨8 * ax.val + q.val, by omega⟩)) =
        coordOfReg24 rA β ax :=
    congrArg byteOfBits (funext fun q ↦ by
      rw [hrM ⟨8 * ax.val + q.val, by omega⟩, pDitePos (by omega : 8 * ax.val + q.val < 24)]
      exact writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨j, hj⟩ ↦ disj_ne dAH _ j hj.symm))
  have hB (ax : Fin 3) :
      byteOfBits (fun q : Fin 8 ↦ writeReg β rHold (fun _ ↦ 0)
          (rM ⟨24 + 8 * ax.val + q.val, by omega⟩)) =
        coordOfReg24 rB β ax :=
    congrArg byteOfBits (funext fun q ↦ by
      rw [hrM ⟨24 + 8 * ax.val + q.val, by omega⟩,
          pDiteNeg (by omega : ¬ 24 + 8 * ax.val + q.val < 24),
          pDitePos (by omega : 24 + 8 * ax.val + q.val < 48),
          writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨j, hj⟩ ↦ disj_ne dBH _ j hj.symm)]
      exact congrArg (fun x ↦ β (rB x)) (Fin.ext (by
        dsimp
        omega)))
  rw [Fin.sum_univ_three, hA 0, hA 1, hA 2, hB 0, hB 1, hB 2]
  rfl

theorem coord48Of_writeReg_tgt {KT n : ℕ} {rA rB : QRegister 24 n} {rTgt : QRegister KT n}
    (dAT : rA.DisjointWires rTgt) (dBT : rB.DisjointWires rTgt)
    (β : BitAssignment n) (g : Fin KT → ZMod 2) :
    coord48Of rA rB (writeReg β rTgt g) = coord48Of rA rB β := by
  funext u
  dsimp only [coord48Of]
  split_ifs
  · exact writeReg_apply_of_not_mem _ rTgt _ _ (fun ⟨j, hj⟩ ↦ disj_ne dAT _ j hj.symm)
  · exact writeReg_apply_of_not_mem _ rTgt _ _ (fun ⟨j, hj⟩ ↦ disj_ne dBT _ j hj.symm)

theorem fRegGen_maskScr {M S k n : ℕ} (hS : 0 < S) (hMS : 48 + S = M)
    (inv : Fin S → Fin S) (sMask : ℕ)
    (hRng : ((List.range M).all fun i ↦
      if sMask.testBit i then Nat.ble 48 i && Nat.ble k (inv ⟨(i - 48) % S, Nat.mod_lt _ hS⟩).val
      else true) = true)
    {rA rB : QRegister 24 n} {rHold : QRegister k n} {rScr : QRegister (S - k) n}
    (rM : QRegister M n)
    (hrM : ∀ u : Fin M, rM u =
      if h0 : u.val < 24 then rA ⟨u.val, h0⟩
      else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
      else
        let idx := inv ⟨u.val - 48, by omega⟩
        if hk : idx.val < k then rHold ⟨idx.val, hk⟩ else rScr ⟨idx.val - k, by omega⟩)
    (u : Wire M) (hu : sMask.testBit u.val = true) :
    ∃ s : Fin (S - k), rM u = rScr s := by
  have hi := (List.all_eq_true.mp hRng) u.val (List.mem_range.mpr u.isLt)
  rw [hu] at hi
  simp only [↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at hi
  have hmod : (⟨(u.val - 48) % S, Nat.mod_lt _ hS⟩ : Fin S) = ⟨u.val - 48, by omega⟩ :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  rw [hmod] at hi
  let idx := inv ⟨u.val - 48, by omega⟩
  have hnk : ¬ idx.val < k := by
    have := hi.2
    omega
  refine ⟨⟨idx.val - k, by omega⟩, ?_⟩
  rw [hrM u, pDiteNeg (by omega), pDiteNeg (by omega)]
  dsimp only
  rw [pDiteNeg hnk]

theorem fRegGen_wires {M S k n : ℕ} {hMS : 48 + S = M} (inv : Fin S → Fin S)
    {rA rB : QRegister 24 n} {rHold : QRegister k n} {rScr : QRegister (S - k) n}
    (rM : QRegister M n)
    (hrM : ∀ u : Fin M, rM u =
      if h0 : u.val < 24 then rA ⟨u.val, h0⟩
      else if h1 : u.val < 48 then rB ⟨u.val - 24, by omega⟩
      else
        let idx := inv ⟨u.val - 48, by omega⟩
        if hk : idx.val < k then rHold ⟨idx.val, hk⟩ else rScr ⟨idx.val - k, by omega⟩)
    {P : Wire n → Prop} (hA : ∀ i, P (rA i)) (hB : ∀ i, P (rB i))
    (hH : ∀ j, P (rHold j)) (hSc : ∀ u, P (rScr u)) (u : Wire M) : P (rM u) := by
  rw [hrM u]
  dsimp only
  split_ifs
  · exact hA _
  · exact hB _
  · exact hH _
  · exact hSc _

set_option maxHeartbeats 800000 in
-- Large circuit/register elaboration requires raised heartbeat limit.
theorem progFwdHeld_step (k : ℕ) (hk1 : 1 ≤ k) (hk44 : k ≤ 44)
    {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister (141 - k) n) (rTgt : QRegister 18 n)
    (dAB : rA.DisjointWires rB) (dAH : rA.DisjointWires rHold)
    (dAS : rA.DisjointWires rScr) (dAT : rA.DisjointWires rTgt)
    (dBH : rB.DisjointWires rHold) (dBS : rB.DisjointWires rScr) (dBT : rB.DisjointWires rTgt)
    (dHS : rHold.DisjointWires rScr) (dHT : rHold.DisjointWires rTgt)
    (dST : rScr.DisjointWires rTgt)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hScr : ∀ δ (u : Fin (141 - k)), (∀ q : Fin W, δ (rWork q) = 0) → st δ (rScr u) = 0)
    (hHold : ∀ δ (j : Fin k), (∀ q : Fin W, δ (rWork q) = 0) →
      st δ (rHold j) = (pHoldProg k).fwdBits
        (fun u ↦ if h : u.val < 48 then coord48Of rA rB (st δ) ⟨u.val, h⟩ else 0)
        ⟨48 + j.val, by omega⟩) :
    let p := progFwdHeld k v rA rB rHold rScr rTgt
    SubspaceStep (mkKetOpW rWork st ph)
      (mkKetOpW rWork (fun δ ↦ writeReg (st δ) rTgt (fun j ↦
        st δ (rTgt j) +
          if (openCoordDistSq (coordOfReg24 rA (st δ)) (coordOfReg24 rB (st δ))).testBit j.val
          then 1 else 0)) ph) p ∧
    p.count .T = 546 - 4 * k ∧
    p.count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ i, S (rA i)) → (∀ i, S (rB i)) → (∀ j, S (rHold j)) →
      (∀ u, S (rScr u)) → (∀ j, S (rTgt j)) → DynWires S p) := by
  have stepCB_tailFwd_eq_outerFwd (β : BitAssignment n)
      (hScr : ∀ u : Fin (141 - k), β (rScr u) = 0)
      (hHold : ∀ j : Fin k, β (rHold j) = (pHoldProg k).fwdBits
          (fun u ↦ if h : u.val < 48 then coord48Of rA rB β ⟨u.val, h⟩ else 0)
              ⟨48 + j.val, by omega⟩) :
      let r189 : QRegister 189 n :=
          ⟨⟨fReg189 rA rB rHold rScr, fReg189_inj dAB dAH dAS dBH dBS dHS⟩⟩
      stepCB r189 (pTailFwdProg k).fwdBits β =
          stepCB r189 pOuterFwd189.fwdBits (writeReg β rHold (fun _ ↦ 0)) := by
    have hcs := checkSplitK_of_bounds hk1 hk44
    dsimp only [checkSplitK] at hcs
    simp only [Bool.and_eq_true, and_assoc] at hcs
    obtain ⟨_, _, _, hOkH, _, _, _, bHoldF, bTailF, hClfF, bCombF, _, _, _, _, _, _, _⟩ := hcs
    exact stepCB_tailGen_eq_outer (by decide) (by decide) (by decide) rfl hk44
      ord141 inv141 ord141_leftInv inv141_leftInv (embHold189 k) (embHold189_inj hk44)
      holdTo189Nat f304To189Nat gsSufFwd304 (gsTailFwd k) gsCombFwd189 pOuterFwd189
      (fun u hu ↦ by simp only [embHold189, hu, ↓reduceDIte])
      (fun u hu ↦ by simp only [embHold189, hu, ↓reduceDIte])
      (fun u ↦ by
        dsimp only [embHold189, holdTo189Nat, ord141]
        by_cases hu : u.val < 48
        · simp only [hu, ↓reduceDIte, ↓reduceIte]
        · simp only [hu, ↓reduceDIte, ↓reduceIte, Nat.mod_eq_of_lt (by omega : u.val - 48 < 141)])
      pCombFwd189_eq_pOuterFwd189 hOkH bHoldF bTailF hClfF bCombF
      ⟨⟨fReg189 rA rB rHold rScr, fReg189_inj dAB dAH dAS dBH dBS dHS⟩⟩
          (fun _ ↦ rfl) dAH dBH dHS β hScr hHold
  have hinj := fReg189_inj dAB dAH dAS dBH dBS dHS
  let r189 : QRegister 189 n := ⟨⟨fReg189 rA rB rHold rScr, hinj⟩⟩
  have hd := fRegGen_disj_tgt (hMS := rfl) inv141 r189 (fun _ ↦ rfl) dAT dBT dHT dST
  dsimp only [progFwdHeld]
  rw [@pDitePos _ (Classical.dec _) _ hinj, @pDitePos _ (Classical.dec _) _ hd]
  have hcs := checkSplitK_of_bounds hk1 hk44
  dsimp only [checkSplitK] at hcs
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq] at hcs
  obtain ⟨_, _, _, _, hValTF, hAndTF, hRngTF, _, _, _, _, _, _, _, _, _, _, _⟩ := hcs
  let valFn (δ : BitAssignment n) :=
      openCoordDistSq (coordOfReg24 rA (st δ)) (coordOfReg24 rB (st δ))
  let g (δ : BitAssignment n) (j : Fin 18) : ZMod 2 :=
      st δ (rTgt j) + if (valFn δ).testBit j.val then 1 else 0
  let st0 (δ : BitAssignment n) := writeReg (st δ) rHold (fun _ ↦ 0)
  let stPost (δ : BitAssignment n) := writeReg (st δ) rTgt (g δ)
  have hMid0 := midFwd189_step v rWork r189 rTgt hd st0 ph valFn
    (fun δ u hu hz ↦ fRegGen_cln48 (hMS := rfl) inv141 r189 (fun _ ↦ rfl) dHS (st δ)
        (fun q ↦ hScr δ q hz) u hu)
    (fun δ _ ↦ fRegGen_val rfl inv141 r189 (fun _ ↦ rfl) dAH dBH (st δ))
  have hMaskScr := fRegGen_maskScr (by decide) rfl inv141 (sMaskTailFwd k) hRngTF r189 (fun _ ↦ rfl)
  have hWrap := subspaceStep_wrapOnReg_vprog2_mask v rWork r189 (sMaskTailFwd k) (pTailFwdProg k)
    (54 - k) (by rwa [validProgMask_zero_eq_fast]) hAndTF st stPost ph ph (midFwd189 v r189 rTgt hd)
    (fun u hu δ hz ↦ let ⟨s, hs⟩ := hMaskScr u hu
      (congrArg (st δ) hs).trans (hScr δ s hz))
    (fun u hu δ hz ↦ let ⟨s, hs⟩ := hMaskScr u hu
      (congrArg (stPost δ) hs).trans
        ((writeReg_apply_of_not_mem _ rTgt _ _ (fun ⟨j, hj⟩ ↦
            disj_ne dST s j hj.symm)).trans (hScr δ s hz)))
    (subspaceStep_congr_in
      (mkKetOpW_congr rWork (fun δ hz ↦
        stepCB_tailFwd_eq_outerFwd (st δ) (fun u ↦ hScr δ u hz) (fun j ↦ hHold δ j hz))
        (fun _ _ ↦ rfl))
      (subspaceStep_congr_out hMid0.1 (mkKetOpW_congr rWork (fun δ hz ↦ by
        dsimp only
        rw [show (fun j : Fin 18 ↦ st0 δ (rTgt j) + if (valFn δ).testBit j.val then 1 else 0) =
            g δ from funext fun j ↦ by
              dsimp only [st0, g]
              rw [writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨q, hq⟩ ↦ disj_ne dHT q j hq)]]
        dsimp only [st0, stPost]
        rw [writeReg_comm_disj rHold rTgt dHT (st δ)]
        exact (stepCB_tailFwd_eq_outerFwd (stPost δ)
          (fun u ↦ (writeReg_apply_of_not_mem _ rTgt _ _
            (fun ⟨j, hj⟩ ↦ disj_ne dST u j hj.symm)).trans (hScr δ u hz))
          (fun j ↦ by
            dsimp only [stPost]
            rw [writeReg_apply_of_not_mem _ rTgt _ _ (fun ⟨q, hq⟩ ↦ disj_ne dHT j q hq.symm),
                coord48Of_writeReg_tgt dAT dBT]
            exact hHold δ j hz)).symm) (fun _ _ ↦ rfl))))
  refine ⟨hWrap.1, ?_, by rw [hWrap.2.2.1, hMid0.2.2.1], fun S hA hB hH hSc hT ↦
    let h189 := fRegGen_wires (hMS := rfl) inv141 r189 (fun _ ↦ rfl) hA hB hH hSc
    hWrap.2.2.2 S h189 (hMid0.2.2.2 S h189 hT)⟩
  rw [hWrap.2.1, hMid0.2.1]
  omega

set_option maxHeartbeats 800000 in
-- Large circuit/register elaboration requires raised heartbeat limit.
theorem progUnldHeld_step (k : ℕ) (hk1 : 1 ≤ k) (hk44 : k ≤ 44)
    {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (rA rB : QRegister 24 n) (rHold : QRegister k n)
    (rScr : QRegister (124 - k) n) (rTgt : QRegister 18 n)
    (dAB : rA.DisjointWires rB) (dAH : rA.DisjointWires rHold)
    (dAS : rA.DisjointWires rScr) (dAT : rA.DisjointWires rTgt)
    (dBH : rB.DisjointWires rHold) (dBS : rB.DisjointWires rScr) (dBT : rB.DisjointWires rTgt)
    (dHS : rHold.DisjointWires rScr) (dHT : rHold.DisjointWires rTgt)
    (dST : rScr.DisjointWires rTgt)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hScr : ∀ δ (u : Fin (124 - k)), (∀ q : Fin W, δ (rWork q) = 0) → st δ (rScr u) = 0)
    (hTgt : ∀ δ (j : Fin 18), (∀ q : Fin W, δ (rWork q) = 0) → st δ (rTgt j) = 0)
    (hHold : ∀ δ (j : Fin k), (∀ q : Fin W, δ (rWork q) = 0) →
      st δ (rHold j) = (pHoldProg k).fwdBits
        (fun u ↦ if h : u.val < 48 then coord48Of rA rB (st δ) ⟨u.val, h⟩ else 0)
        ⟨48 + j.val, by omega⟩) :
    let p := progUnldHeld k v rA rB rHold rScr rTgt
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ writeReg (st δ) rTgt (fun j ↦
        if (openCoordDistSq (coordOfReg24 rA (st δ)) (coordOfReg24 rB (st δ))).testBit j.val
        then 1 else 0)) ph)
      (mkKetOpW rWork st ph) p ∧
    p.count .T = 476 - 4 * k ∧
    p.count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ i, S (rA i)) → (∀ i, S (rB i)) → (∀ j, S (rHold j)) →
      (∀ u, S (rScr u)) → (∀ j, S (rTgt j)) → DynWires S p) := by
  have stepCB_tailUnld_eq_outerUnld (β : BitAssignment n)
      (hScr : ∀ u : Fin (124 - k), β (rScr u) = 0)
      (hHold : ∀ j : Fin k, β (rHold j) = (pHoldProg k).fwdBits
          (fun u ↦ if h : u.val < 48 then coord48Of rA rB β ⟨u.val, h⟩ else 0)
              ⟨48 + j.val, by omega⟩) :
      let r172 : QRegister 172 n :=
          ⟨⟨fReg172 rA rB rHold rScr, fReg172_inj dAB dAH dAS dBH dBS dHS⟩⟩
      stepCB r172 (pTailUnldProg k).fwdBits β =
          stepCB r172 pOuterUnld172.fwdBits (writeReg β rHold (fun _ ↦ 0)) := by
    have hcs := checkSplitK_of_bounds hk1 hk44
    dsimp only [checkSplitK] at hcs
    simp only [Bool.and_eq_true, and_assoc] at hcs
    obtain ⟨_, _, _, hOkH, _, _, _, _, _, _, _, _, _, _, bHoldU, bTailU, hClfU, bCombU⟩ := hcs
    exact stepCB_tailGen_eq_outer (by decide) (by decide) (by decide) rfl hk44
      ord124 inv124 ord124_leftInv inv124_leftInv (embHold172 k) (embHold172_inj hk44)
      holdTo172Nat f304To172Nat gsSufUnld304 (gsTailUnld k) gsCombUnld172 pOuterUnld172
      (fun u hu ↦ by simp only [embHold172, hu, ↓reduceDIte])
      (fun u hu ↦ by simp only [embHold172, hu, ↓reduceDIte])
      (fun u ↦ by
        dsimp only [embHold172, holdTo172Nat, ord124]
        by_cases hu : u.val < 48
        · simp only [hu, ↓reduceDIte, ↓reduceIte]
        · simp only [hu, ↓reduceDIte, ↓reduceIte, Nat.mod_eq_of_lt (by omega : u.val - 48 < 124)])
      pCombUnld172_eq_pOuterUnld172 hOkH bHoldU bTailU hClfU bCombU
      ⟨⟨fReg172 rA rB rHold rScr, fReg172_inj dAB dAH dAS dBH dBS dHS⟩⟩
          (fun _ ↦ rfl) dAH dBH dHS β hScr hHold
  have hinj := fReg172_inj dAB dAH dAS dBH dBS dHS
  let r172 : QRegister 172 n := ⟨⟨fReg172 rA rB rHold rScr, hinj⟩⟩
  have hd := fRegGen_disj_tgt (hMS := rfl) inv124 r172 (fun _ ↦ rfl) dAT dBT dHT dST
  dsimp only [progUnldHeld]
  rw [@pDitePos _ (Classical.dec _) _ hinj, @pDitePos _ (Classical.dec _) _ hd]
  have hcs := checkSplitK_of_bounds hk1 hk44
  dsimp only [checkSplitK] at hcs
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq] at hcs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hValTU, hAndTU, hRngTU, _, _, _, _⟩ := hcs
  let valFn (δ : BitAssignment n) :=
      openCoordDistSq (coordOfReg24 rA (st δ)) (coordOfReg24 rB (st δ))
  let g (δ : BitAssignment n) (j : Fin 18) : ZMod 2 := if (valFn δ).testBit j.val then 1 else 0
  let st0 (δ : BitAssignment n) := writeReg (st δ) rHold (fun _ ↦ 0)
  let stPre (δ : BitAssignment n) := writeReg (st δ) rTgt (g δ)
  have hMid0 := midUnld172_step v rWork r172 rTgt hd st0 ph valFn
    (fun δ u hu hz ↦ fRegGen_cln48 (hMS := rfl) inv124 r172 (fun _ ↦ rfl) dHS (st δ)
        (fun q ↦ hScr δ q hz) u hu)
    (fun δ j hz ↦ (writeReg_apply_of_not_mem _ rHold _ _ (fun ⟨q, hq⟩ ↦
        disj_ne dHT q j hq)).trans (hTgt δ j hz))
    (fun δ _ ↦ fRegGen_val rfl inv124 r172 (fun _ ↦ rfl) dAH dBH (st δ))
  have hMaskScr :=
      fRegGen_maskScr (by decide) rfl inv124 (sMaskTailUnld k) hRngTU r172 (fun _ ↦ rfl)
  have hWrap := subspaceStep_wrapOnReg_vprog2_mask v rWork r172 (sMaskTailUnld k) (pTailUnldProg k)
    (54 - k) (by rwa [validProgMask_zero_eq_fast]) hAndTU stPre st ph ph (midUnld172 v r172 rTgt hd)
    (fun u hu δ hz ↦ let ⟨s, hs⟩ := hMaskScr u hu
      (congrArg (stPre δ) hs).trans
        ((writeReg_apply_of_not_mem _ rTgt _ _ (fun ⟨j, hj⟩ ↦
            disj_ne dST s j hj.symm)).trans (hScr δ s hz)))
    (fun u hu δ hz ↦ let ⟨s, hs⟩ := hMaskScr u hu
      (congrArg (st δ) hs).trans (hScr δ s hz))
    (subspaceStep_congr_in
      (mkKetOpW_congr rWork (fun δ hz ↦ by
        dsimp only [st0, stPre]
        rw [writeReg_comm_disj rHold rTgt dHT (st δ)]
        exact stepCB_tailUnld_eq_outerUnld (writeReg (st δ) rTgt (g δ))
          (fun u ↦ (writeReg_apply_of_not_mem _ rTgt _ _
            (fun ⟨j, hj⟩ ↦ disj_ne dST u j hj.symm)).trans (hScr δ u hz))
          (fun j ↦ by
            rw [writeReg_apply_of_not_mem _ rTgt _ _ (fun ⟨q, hq⟩ ↦ disj_ne dHT j q hq.symm),
                coord48Of_writeReg_tgt dAT dBT]
            exact hHold δ j hz)) (fun _ _ ↦ rfl))
      (subspaceStep_congr_out hMid0.1 (mkKetOpW_congr rWork (fun δ hz ↦
        (stepCB_tailUnld_eq_outerUnld (st δ) (fun u ↦ hScr δ u hz) (fun j ↦ hHold δ j hz)).symm)
        (fun _ _ ↦ rfl))))
  refine ⟨hWrap.1, ?_, by rw [hWrap.2.2.1, hMid0.2.2.1], fun S hA hB hH hSc hT ↦
    let h172 := fRegGen_wires (hMS := rfl) inv124 r172 (fun _ ↦ rfl) hA hB hH hSc
    hWrap.2.2.2 S h172 (hMid0.2.2.2 S h172 hT)⟩
  rw [hWrap.2.1, hMid0.2.1]
  omega

/-- Uniform `k`-wire prefix-held `Dist18` forward + unload split package (`1 ≤ k ≤ 44`). -/
noncomputable def dist18HeldSplitPkg (k : ℕ) (hk1 : 1 ≤ k) (hk44 : k ≤ 44) :
    Dist18HeldSplitPkg k (141 - k) (546 - 4 * k) (124 - k) (476 - 4 * k) where
  sMaskHold := sMaskHoldNat k
  pHold := pHoldProg k
  pHold_valid := by
    have hcs := checkSplitK_of_bounds hk1 hk44
    dsimp only [checkSplitK] at hcs
    simp only [Bool.and_eq_true, and_assoc] at hcs
    rw [validProgMask_zero_eq_fast]
    exact hcs.1
  pHold_numAnd := by
    have hcs := checkSplitK_of_bounds hk1 hk44
    dsimp only [checkSplitK] at hcs
    simp only [Bool.and_eq_true, and_assoc, beq_iff_eq] at hcs
    exact hcs.2.1
  sMaskHold_ge48 u hu := by
    by_contra hlt
    have hcs := checkSplitK_of_bounds hk1 hk44
    dsimp only [checkSplitK] at hcs
    simp only [Bool.and_eq_true, and_assoc] at hcs
    have hi := (List.all_eq_true.mp hcs.2.2.1) u.val (List.mem_range.mpr (by omega))
    simp [hu] at hi
  pHold_coords γ i := by
    have hcs := checkSplitK_of_bounds hk1 hk44
    dsimp only [checkSplitK] at hcs
    simp only [Bool.and_eq_true, and_assoc] at hcs
    dsimp only [pHoldProg, gsHold]
    exact exec_append_undo_coords (by omega) (gsHoldPre k) hcs.2.2.2.1 γ i
  progFwd := progFwdHeld k
  progUnld := progUnldHeld k
  step_fwd := progFwdHeld_step k hk1 hk44
  step_unld := progUnldHeld_step k hk1 hk44
end QuantumComputation.Specs.PhotochemistrySolution.Dist18P26Dual
end Dist18P26DualSection

noncomputable section Stage4PrefixHoldMuxBody
namespace QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp193K2
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
open PhotochemistrySolution.DeferMux2Wp198Opt
open Operator QProg Matrix Circuit Qubit HermitianMat
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18P26Dual (coord48Of
    Dist18HeldSplitPkg writeReg_comm_disj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (openCoordDistSq disj_ne
    disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (stepCB_apply_reg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (word512DualLegLo6
    v1Fin8DualLeg v2Fin8DualLeg)
/-- Combined `48`-wire coordinate register `(rMuxM1, rPotBPortB)` for `pHold`. -/
def rCoord48 {Wp n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) : QRegister 48 n :=
  (rMuxM1 h193 isCsel r41).concat (rPotBPortB r41) (muxDisj_m1_portB h193 isCsel r41)

/-- Combined `(48 + k)`-wire register `(rMuxM1, rPotBPortB, rHold)` for `pHold`. -/
def rCoord48Hold {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n) (hd41H : r41.DisjointWires rHold) :
    QRegister (48 + k) n :=
  (rCoord48 h193 isCsel r41).concat rHold (disj_of_ne fun i j h ↦ by
    have hi48 := i.isLt
    by_cases hi : i.val < 24
    · have h1 : rCoord48 h193 isCsel r41 (Fin.castAdd 24 ⟨i.val, hi⟩) =
          rMuxM1 h193 isCsel r41 ⟨i.val, hi⟩ := by
        rw [rCoord48, QRegister.concat_apply_left]
      have heq : Fin.castAdd 24 ⟨i.val, hi⟩ = i := Fin.ext rfl
      rw [heq] at h1
      rw [h1] at h
      exact disj_ne hd41H _ j h
    · let i24 : Fin 24 := ⟨i.val - 24, by omega⟩
      have h1 : rCoord48 h193 isCsel r41 (Fin.natAdd 24 i24) = rPotBPortB r41 i24 := by
        rw [rCoord48, QRegister.concat_apply_right]
      have heq : Fin.natAdd 24 i24 = i := Fin.ext (by
        simp only [Fin.val_natAdd, i24]
        omega)
      rw [heq] at h1
      rw [h1] at h
      exact disj_ne hd41H _ j h)


theorem writeReg_rHold_r41 {Wp k n : ℕ} {r41 : QRegister (122 + Wp) n} {rHold : QRegister k n}
    (hd41H : r41.DisjointWires rHold) (β : BitAssignment n) (g : Fin k → ZMod 2)
    (m : Fin (122 + Wp)) :
    writeReg β rHold g (r41 m) = β (r41 m) :=
  writeReg_apply_of_not_mem β rHold g (r41 m) (fun ⟨j, hj⟩ ↦ disj_ne hd41H m j hj.symm)

theorem writeReg_rHold_comp {Wp k w n : ℕ} {r41 : QRegister (122 + Wp) n} {rHold : QRegister k n}
    (hd41H : r41.DisjointWires rHold) (s : QRegister w (122 + Wp))
    (β : BitAssignment n) (g : Fin k → ZMod 2) (i : Fin w) :
    writeReg β rHold g (r41.compose s i) = β (r41.compose s i) :=
  writeReg_rHold_r41 hd41H β g (s i)

theorem xorPortB41NotScr_writeReg_rHold {Wp k n : ℕ} {r41 : QRegister (122 + Wp) n}
    {rHold : QRegister k n} (hd41H : r41.DisjointWires rHold)
    (β : BitAssignment n) (g : Fin k → ZMod 2) :
    xorPortB41NotScr r41 (writeReg β rHold g) = writeReg (xorPortB41NotScr r41 β) rHold g := by
  unfold xorPortB41NotScr
  rw [show (fun i ↦ writeReg β rHold g (rPotBPortB r41 i) +
        (1 + writeReg β rHold g (wPotBIsScreen r41)) * writeReg β rHold g (rPotBNucA r41 i)) =
        (fun i ↦ β (rPotBPortB r41 i) + (1 + β (wPotBIsScreen r41)) * β (rPotBNucA r41 i)) from
      funext fun i ↦ by
        dsimp only [rPotBPortB, rPotBNucA, wPotBIsScreen]
        rw [writeReg_rHold_comp hd41H, writeReg_rHold_r41 hd41H, writeReg_rHold_comp hd41H],
      writeReg_comm_disj rHold (rPotBPortB r41) (disj_of_ne fun j _ h ↦ disj_ne hd41H _ j h.symm)]

theorem muxStNoM2_writeReg_rHold {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    {r41 : QRegister (122 + Wp) n} {rHold : QRegister k n} (hd41H : r41.DisjointWires rHold)
    (m0 : ℕ) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (g : Fin k → ZMod 2) :
    muxStNoM2 h193 isCsel r41 m0 z16 (writeReg β rHold g) =
      writeReg (muxStNoM2 h193 isCsel r41 m0 z16 β) rHold g := by
  unfold muxStNoM2
  rw [show muxWorkValNoM2 h193 isCsel r41 m0 (writeReg β rHold g) =
        muxWorkValNoM2 h193 isCsel r41 m0 β from funext fun u ↦ by
        dsimp only [muxWorkValNoM2, rPotBNucA, rPotBElecA, wPotBLocQ, wPotBIsPot, wPotBIsNN]
        simp only [writeReg_rHold_r41 hd41H, writeReg_rHold_comp hd41H],
      writeReg_comm_disj rHold (rMuxZ16 r41) (disj_of_ne fun j _ h ↦ disj_ne hd41H _ j h.symm),
      writeReg_comm_disj rHold (rPotBWork r41) (disj_of_ne fun j _ h ↦ disj_ne hd41H _ j h.symm)]

theorem muxD2Val_writeReg_rHold {Wp k n : ℕ} {r41 : QRegister (122 + Wp) n}
    {rHold : QRegister k n} (hd41H : r41.DisjointWires rHold)
    (β : BitAssignment n) (g : Fin k → ZMod 2) :
    muxD2Val r41 (writeReg β rHold g) = muxD2Val r41 β := by
  have hC (s : QRegister 24 (122 + Wp)) :=
    coordOfReg24_congr (r41.compose s) (r41.compose s) _ _ (writeReg_rHold_comp hd41H s β g)
  unfold muxD2Val
  rw [writeReg_rHold_r41 hd41H, writeReg_rHold_r41 hd41H, hC _, hC _, hC _]

theorem midInvar_writeReg_rHold {Wp k n : ℕ} (isCsel : Bool)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ)
    {r41 : QRegister (122 + Wp) n} {rHold : QRegister k n} (hd41H : r41.DisjointWires rHold)
    (z16 : Fin 16 → ZMod 2) (ph : ZMod 2) (β : BitAssignment n) (g : Fin k → ZMod 2) :
    z16AfterMidK2 isCsel ySample13 r41 z16 (writeReg β rHold g) =
      z16AfterMidK2 isCsel ySample13 r41 z16 β ∧
    phAfterMidK2 isCsel ySample13 r41 z16 ph (writeReg β rHold g) =
      phAfterMidK2 isCsel ySample13 r41 z16 ph β := by
  have hC13 (j : Fin 13) : writeReg β rHold g (rC13Of41 r41 j) = β (rC13Of41 r41 j) :=
    have := (idxC13Of41_bounds j).2
    writeReg_rHold_r41 hd41H β g ⟨idxC13Of41 j, by omega⟩
  have hgAct : potBGateActive isCsel r41 (writeReg β rHold g) = potBGateActive isCsel r41 β := by
    cases isCsel <;> simp only [potBGateActive, writeReg_rHold_r41 hd41H]
  have hSum : midSumMuxK2 isCsel ySample13 r41 z16 (writeReg β rHold g) =
      midSumMuxK2 isCsel ySample13 r41 z16 β := by
    simp only [midSumMuxK2, y36MuxK2, zLo14MuxK2, x13OfReg13, w11OfReg13, hC13, hgAct,
      muxD2Val_writeReg_rHold hd41H, writeReg_rHold_r41 hd41H]
  exact ⟨funext fun _ ↦ by simp only [z16AfterMidK2, hgAct, hSum],
    by simp only [phAfterMidK2, hgAct, hSum, writeReg_rHold_r41 hd41H]⟩

/--
Canonical `z16`-independent `(48 + k)`-wire input assignment to `pHold` after
`pInPlaceMux2_24`.
-/
def holdIn48k {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n) (β : BitAssignment n) :
    BitAssignment (48 + k) :=
  fun u ↦
    if h : u.val < 48 then
      coord48Of (rMuxM1 h193 isCsel r41) (rPotBPortB r41)
        (muxStNoM2 h193 isCsel r41 0 0 β) ⟨u.val, h⟩
    else β (rHold ⟨u.val - 48, by omega⟩)

/-- Held `k`-wire values written by `pHold` onto `rHold` (`z16`-independent). -/
def heldBitsMux {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n)
    (cp : ComputeProg (48 + k)) (β : BitAssignment n) (j : Fin k) : ZMod 2 :=
  cp.fwdBits (holdIn48k h193 isCsel r41 rHold β) ⟨48 + j.val, by omega⟩

theorem rCoord48Hold_lt24 {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n) (hd41H : r41.DisjointWires rHold)
    (u : Fin (48 + k)) (hu : u.val < 24) :
    rCoord48Hold h193 isCsel r41 rHold hd41H u = rMuxM1 h193 isCsel r41 ⟨u.val, hu⟩ := by
  have h1 : rCoord48Hold h193 isCsel r41 rHold hd41H
      (Fin.castAdd k (Fin.castAdd 24 ⟨u.val, hu⟩)) = rMuxM1 h193 isCsel r41 ⟨u.val, hu⟩ := by
    rw [rCoord48Hold, QRegister.concat_apply_left, rCoord48, QRegister.concat_apply_left]
  exact (congrArg (rCoord48Hold h193 isCsel r41 rHold hd41H).wires (Fin.ext rfl)).trans h1

theorem rCoord48Hold_mid {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n) (hd41H : r41.DisjointWires rHold)
    (u : Fin (48 + k)) (hlo : ¬ u.val < 24) (hhi : u.val < 48) :
    rCoord48Hold h193 isCsel r41 rHold hd41H u = rPotBPortB r41 ⟨u.val - 24, by omega⟩ := by
  let u24 : Fin 24 := ⟨u.val - 24, by omega⟩
  exact (congrArg (rCoord48Hold h193 isCsel r41 rHold hd41H).wires
    (Fin.ext (by
      simp only [Fin.val_castAdd, Fin.val_natAdd, u24]
      omega) : u = Fin.castAdd k (Fin.natAdd 24 u24))).trans (by
    rw [rCoord48Hold, QRegister.concat_apply_left, rCoord48, QRegister.concat_apply_right])

theorem rCoord48Hold_ge48 {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n) (hd41H : r41.DisjointWires rHold)
    (u : Fin (48 + k)) (hu : 48 ≤ u.val) :
    rCoord48Hold h193 isCsel r41 rHold hd41H u = rHold ⟨u.val - 48, by omega⟩ := by
  have := u.isLt
  exact (congrArg (rCoord48Hold h193 isCsel r41 rHold hd41H).wires
    (Fin.ext (by
      simp only [Fin.val_natAdd]
      omega) : u = Fin.natAdd 48 ⟨u.val - 48, by omega⟩)).trans (by
    rw [rCoord48Hold, QRegister.concat_apply_right])

theorem muxStNoM2_rCoord48Hold_eq {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    {r41 : QRegister (122 + Wp) n} {rHold : QRegister k n} (hd41H : r41.DisjointWires rHold)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) :
    (fun u ↦ muxStNoM2 h193 isCsel r41 0 z16 β (rCoord48Hold h193 isCsel r41 rHold hd41H u)) =
      holdIn48k h193 isCsel r41 rHold β := by
  have hw := wtop_ge192 h193 isCsel
  funext u
  unfold holdIn48k coord48Of
  by_cases hu0 : u.val < 24
  · rw [rCoord48Hold_lt24 h193 isCsel r41 rHold hd41H u hu0]
    simp only [hu0, show u.val < 48 by omega, ↓reduceDIte]
    exact muxStNoM2_eq_of_ne_z16 h193 isCsel r41 0 z16 0 β fun j ↦
      r41_blk_ne_blk r41 (⟨u.val, hu0⟩ : Fin 24) j (by omega)
  · by_cases hu1 : u.val < 48
    · rw [rCoord48Hold_mid h193 isCsel r41 rHold hd41H u hu0 hu1]
      simp only [hu0, hu1, ↓reduceDIte]
      exact muxStNoM2_eq_of_ne_z16 h193 isCsel r41 0 z16 0 β fun j ↦
        r41_blk_ne_blk r41 (⟨u.val - 24, by omega⟩ : Fin 24) j (by omega)
    · rw [rCoord48Hold_ge48 h193 isCsel r41 rHold hd41H u (by omega)]
      simp only [hu1, ↓reduceDIte]
      exact muxStNoM2_out h193 isCsel r41 0 z16 β fun q h ↦ disj_ne hd41H q _ h.symm

theorem stepCB_rCoord48Hold_muxStNoM2 {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    {r41 : QRegister (122 + Wp) n} {rHold : QRegister k n} (hd41H : r41.DisjointWires rHold)
    (cp : ComputeProg (48 + k))
    (hCoords : ∀ (γ : BitAssignment (48 + k)) (i : Fin 48),
      cp.fwdBits γ ⟨i.val, by omega⟩ = γ ⟨i.val, by omega⟩)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) :
    stepCB (rCoord48Hold h193 isCsel r41 rHold hd41H) cp.fwdBits
        (muxStNoM2 h193 isCsel r41 0 z16 β) =
      muxStNoM2 h193 isCsel r41 0 z16
        (writeReg β rHold (heldBitsMux h193 isCsel r41 rHold cp β)) := by
  let r48k := rCoord48Hold h193 isCsel r41 rHold hd41H
  let s0 := muxStNoM2 h193 isCsel r41 0 z16 β
  rw [muxStNoM2_writeReg_rHold h193 isCsel hd41H]
  funext w
  by_cases hwH : ∃ j : Fin k, rHold j = w
  · obtain ⟨j, rfl⟩ := hwH
    have hj48 : r48k ⟨48 + j.val, by omega⟩ = rHold j :=
      (rCoord48Hold_ge48 h193 isCsel r41 rHold hd41H _ (Nat.le_add_right 48 j.val)).trans
        (congrArg rHold.wires (Fin.ext (Nat.add_sub_cancel_left 48 j.val)))
    rw [← hj48, stepCB_apply_reg, hj48, writeReg_apply_reg,
        muxStNoM2_rCoord48Hold_eq h193 isCsel hd41H z16 β]
    rfl
  · rw [writeReg_apply_of_not_mem _ rHold _ w hwH]
    by_cases hw48 : ∃ u : Fin (48 + k), r48k u = w
    · obtain ⟨u, rfl⟩ := hw48
      rw [stepCB_apply_reg]
      exact hCoords (fun q ↦ s0 (r48k q)) ⟨u.val, by
        by_contra hge
        exact hwH ⟨⟨u.val - 48, by omega⟩,
            (rCoord48Hold_ge48 h193 isCsel r41 rHold hd41H u (by omega)).symm⟩⟩
    · exact stepCB_apply_out r48k cp.fwdBits s0 (fun u h ↦ hw48 ⟨u, h.symm⟩)

theorem holdIn48k_eq_zero_tail {Wp k n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    {r41 : QRegister (122 + Wp) n} {rHold : QRegister k n} (hd41H : r41.DisjointWires rHold)
    (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) (g : Fin k → ZMod 2)
    (hH0 : ∀ j : Fin k, β (rHold j) = 0) :
    (fun u : Fin (48 + k) ↦
      if h : u.val < 48 then
        coord48Of (rMuxM1 h193 isCsel r41) (rPotBPortB r41)
          (muxStNoM2 h193 isCsel r41 0 z16 (writeReg β rHold g)) ⟨u.val, h⟩
      else 0) =
    holdIn48k h193 isCsel r41 rHold β := by
  have hw := wtop_ge192 h193 isCsel
  funext u
  unfold holdIn48k
  by_cases hu : u.val < 48
  · simp only [hu, ↓reduceDIte]
    unfold coord48Of
    rw [muxStNoM2_writeReg_rHold h193 isCsel hd41H]
    split_ifs with hu0
    · exact (writeReg_rHold_r41 hd41H _ g _).trans (muxStNoM2_eq_of_ne_z16 h193 isCsel r41 0 z16 0 β
        (fun j h ↦ r41_blk_ne_blk r41 (⟨u.val, hu0⟩ : Fin 24) j (by omega) h))
    · exact (writeReg_rHold_r41 hd41H _ g _).trans (muxStNoM2_eq_of_ne_z16 h193 isCsel r41 0 z16 0 β
        (fun j h ↦ r41_blk_ne_blk r41 (⟨u.val - 24, by omega⟩ : Fin 24) j (by omega) h))
  · simp only [hu, ↓reduceDIte]
    exact (hH0 ⟨u.val - 48, by omega⟩).symm

/--
Shared `M = 0` Stage-4 middle block wrapping `pHold` around
`(progFwd >> Scrub >> StageB >> Scrub >> progUnld)`.
-/
def pMuxHeldMid_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {Wp k kScrF tF kScrU tU kMid tMid tCoul n : ℕ}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid)
    (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp - 25) (hDU : 18 + kScrU ≤ Wp - 25)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp isCsel)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp isCsel)
    (v : Var) (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n)
    (hd41H : r41.DisjointWires rHold) : DynamicCircuit Var n :=
  (pInPlaceMux2_24 h193 v r41).seq
    (wrapDynOnReg v (rCoord48Hold h193 isCsel r41 rHold hd41H) pkgH.pHold
      ((pkgH.progFwd v (rMuxM1 h193 isCsel r41) (rPotBPortB r41) rHold
          (rMuxDistScrPebIpb h193 isCsel hDX r41) (rMuxD2_18 h193 r41)).seq
        ((pScrubM1PebIpb h193 isCsel r41).seq
          ((pMuxStageBNoM2_k2_pebIpb h193 isCsel (Nat.zero_le 16)
              pkgMid pkgC hCapMid hCap v r41).seq
            ((pScrubM1PebIpb h193 isCsel r41).seq
              (pkgH.progUnld v (rMuxM1 h193 isCsel r41) (rPotBPortB r41) rHold
                (rMuxDistScrPebIpb h193 isCsel hDU r41) (rMuxD2_18 h193 r41)))))))

theorem muxHold_disj {Wp k kScrF kScrU n : ℕ} (h193 : 193 ≤ Wp) (isCsel : Bool)
    (hDX : 18 + kScrF ≤ Wp - 25) (hDU : 18 + kScrU ≤ Wp - 25)
    {r41 : QRegister (122 + Wp) n} {rHold : QRegister k n} (hd41H : r41.DisjointWires rHold) :
    (rMuxM1 h193 isCsel r41).DisjointWires rHold ∧
    (rPotBPortB r41).DisjointWires rHold ∧
    rHold.DisjointWires (rMuxDistScrPebIpb h193 isCsel hDX r41) ∧
    rHold.DisjointWires (rMuxDistScrPebIpb h193 isCsel hDU r41) ∧
    rHold.DisjointWires (rMuxD2_18 h193 r41) :=
  ⟨disj_of_ne fun _ j h ↦ disj_ne hd41H _ j h,
   disj_of_ne fun _ j h ↦ disj_ne hd41H _ j h,
   disj_of_ne fun j _ h ↦ disj_ne hd41H _ j h.symm,
   disj_of_ne fun j _ h ↦ disj_ne hd41H _ j h.symm,
   disj_of_ne fun j _ h ↦ disj_ne hd41H _ j h.symm⟩

theorem ctrlSafe_pMuxHeldMid_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {Wp k kScrF tF kScrU tU kMid tMid tCoul n : ℕ} {S : Wire n → Prop}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid)
    (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp - 25) (hDU : 18 + kScrU ≤ Wp - 25)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp isCsel)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp isCsel)
    (v : Var) (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n)
    (hd41H : r41.DisjointWires rHold)
    (hS41 : ∀ q, S (r41 q)) (hSH : ∀ j, S (rHold j)) :
    DynCtrlSafe S S
      (pMuxHeldMid_k2_pebIpb h193 isCsel pkgH pkgMid pkgC hDX hDU hCapMid hCap
        v r41 rHold hd41H) := by
  let S2 : Wire n → Prop := fun w ↦ S w ∧ S w
  have hSS41 (q) : S2 (r41 q) := ⟨hS41 q, hS41 q⟩
  have hSSH (j) : S2 (rHold j) := ⟨hSH j, hSH j⟩
  obtain ⟨hdMH, hdPH, hdHSF, hdHSU, hdHD⟩ := muxHold_disj h193 isCsel hDX hDU hd41H
  obtain ⟨_, fF, wF0⟩ := pkgH.counts_wires_fwd v (rMuxM1 h193 isCsel r41) (rPotBPortB r41)
    rHold (rMuxDistScrPebIpb h193 isCsel hDX r41) (rMuxD2_18 h193 r41)
    (muxDisj_m1_portB h193 isCsel r41) hdMH (muxDisj_m1_scrPebIpb h193 isCsel hDX r41)
    (muxDisj_m1_d2 h193 isCsel r41) hdPH (muxDisj_portB_scrPebIpb h193 isCsel hDX r41)
    (muxDisj_portB_d2 h193 r41) hdHSF hdHD (muxDisj_scrPebIpb_d2 h193 isCsel hDX r41)
  obtain ⟨_, fU, wU0⟩ := pkgH.counts_wires_unld v (rMuxM1 h193 isCsel r41) (rPotBPortB r41)
    rHold (rMuxDistScrPebIpb h193 isCsel hDU r41) (rMuxD2_18 h193 r41)
    (muxDisj_m1_portB h193 isCsel r41) hdMH (muxDisj_m1_scrPebIpb h193 isCsel hDU r41)
    (muxDisj_m1_d2 h193 isCsel r41) hdPH (muxDisj_portB_scrPebIpb h193 isCsel hDU r41)
    (muxDisj_portB_d2 h193 r41) hdHSU hdHD (muxDisj_scrPebIpb_d2 h193 isCsel hDU r41)
  have wSc := dynWires_pScrubM1PebIpb (Var := Var) h193 isCsel r41 hSS41
  refine .of_dynWires ⟨dynWires_pInPlaceMux2Range h193 v r41 hSS41 24 (Nat.le_refl 24),
    dynWires_wrapDynOnReg v (rCoord48Hold h193 isCsel r41 rHold hd41H)
      (fun u ↦ by
        by_cases h0 : u.val < 24
        · exact rCoord48Hold_lt24 h193 isCsel r41 rHold hd41H u h0 ▸ hSS41 _
        · by_cases h1 : u.val < 48
          · exact rCoord48Hold_mid h193 isCsel r41 rHold hd41H u h0 h1 ▸ hSS41 _
          · exact rCoord48Hold_ge48 h193 isCsel r41 rHold hd41H u (by omega) ▸ hSSH _)
      pkgH.pHold
      ⟨wF0 S2 (fun _ ↦ hSS41 _) (fun _ ↦ hSS41 _) hSSH (fun _ ↦ hSS41 _) (fun _ ↦ hSS41 _), wSc,
        dynWires_pMuxStageBNoM2_k2_pebIpb h193 isCsel (Nat.zero_le 16) pkgMid pkgC hCapMid hCap v
            r41 hSS41,
        wSc, wU0 S2 (fun _ ↦ hSS41 _) (fun _ ↦ hSS41 _) hSSH (fun _ ↦ hSS41 _)
            (fun _ ↦ hSS41 _)⟩⟩ ?_
  dsimp only [pMuxHeldMid_k2_pebIpb, pInPlaceMux2_24]
  rw [dc_count_seq, (count_pInPlaceMux2Range h193 v r41 24 (Nat.le_refl 24)).2,
      (counts_wrapDynOnReg v (rCoord48Hold h193 isCsel r41 rHold hd41H) pkgH.pHold _).2,
      dc_count_seq, dc_count_seq, dc_count_seq, dc_count_seq, fF,
      (count_pScrubM1PebIpb (Var := Var) h193 isCsel r41).2,
      toff_pMuxStageBNoM2_k2_pebIpb h193 isCsel (Nat.zero_le 16) pkgMid pkgC hCapMid hCap v r41, fU]

set_option maxHeartbeats 800000 in
-- Five-stage held middle composition (`progFwd`, `Scrub`, `StageB`, `Scrub`, `progUnld`).
theorem step_pMuxHeldMid_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp k kScrF tF kScrU tU kMid tMid tCoul n : ℕ} [NeZero (2 ^ n)]
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp) (isCsel : Bool)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid)
    (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp - 25) (hDU : 18 + kScrU ≤ Wp - 25)
    (hKMidLE : kMid ≤ pkgC.kMid)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp isCsel)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp isCsel)
    (v : Var) (rWork : QRegister W n) (r41 : QRegister (122 + Wp) n) (rHold : QRegister k n)
    (hd41H : r41.DisjointWires rHold)
    (st : BitAssignment n → BitAssignment n)
    (z16L2 : BitAssignment n → Fin 16 → ZMod 2)
    (phL2 : BitAssignment n → ZMod 2)
    (hVF41 : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags r41 (st δ))
    (hPB0 : ∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
      st δ (wPotBIsScreen r41) = 0 → st δ (rPotBPortB r41 i) = 0)
    (hHold0 : ∀ δ (j : Fin k), (∀ q, δ (rWork q) = 0) → st δ (rHold j) = 0) :
    let st' := fun δ ↦ xorPortB41NotScr r41 (st δ)
    let z16M := fun δ ↦ z16AfterMidK2 isCsel ySample13 r41 (z16L2 δ) (st δ)
    let phM := fun δ ↦ phAfterMidK2 isCsel ySample13 r41 (z16L2 δ) (phL2 δ) (st δ)
    let pMid := pMuxHeldMid_k2_pebIpb h193 isCsel pkgH pkgMid pkgC
      hDX hDU hCapMid hCap v r41 rHold hd41H
    SubspaceStep
      (mkKetOpW rWork (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16L2 δ) (st δ)) phL2)
      (mkKetOpW rWork (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16M δ) (st' δ)) phM) pMid ∧
    pMid.count .T = 96 + 4 * k + tF + tCoul + tMid + tU ∧
    pMid.count .TOFF = 0 := by
  intro st' z16M phM
  have hw := wtop_ge192 h193 isCsel
  obtain ⟨hdMH, hdPH, hdHSF, hdHSU, hdHD⟩ := muxHold_disj h193 isCsel hDX hDU hd41H
  let gH := fun δ ↦ heldBitsMux h193 isCsel r41 rHold pkgH.pHold (st' δ)
  let stH := fun δ ↦ writeReg (st δ) rHold (gH δ)
  let stH' := fun δ ↦ writeReg (st' δ) rHold (gH δ)
  have hEqStH' : ∀ δ, xorPortB41NotScr r41 (stH δ) = stH' δ :=
    fun δ ↦ xorPortB41NotScr_writeReg_rHold hd41H (st δ) (gH δ)
  have hHold0' (δ) (j : Fin k) (hz : ∀ q, δ (rWork q) = 0) : st' δ (rHold j) = 0 :=
    (writeReg_apply_of_not_mem _ (rPotBPortB r41) _ _
      (fun ⟨i, hi⟩ ↦ disj_ne hdPH i j hi)).trans (hHold0 δ j hz)
  have hPB0H (δ) (i : Fin 24) (hz : ∀ q, δ (rWork q) = 0)
      (hs : stH δ (wPotBIsScreen r41) = 0) : stH δ (rPotBPortB r41 i) = 0 :=
    (writeReg_rHold_comp hd41H _ (st δ) (gH δ) i).trans
      (hPB0 δ i hz ((writeReg_rHold_r41 hd41H (st δ) (gH δ) _).symm.trans hs))
  have hVFH' (δ) (hz : ∀ q, δ (rWork q) = 0) : ValidPotBFlags r41 (stH' δ) := by
    rw [← hEqStH' δ]
    refine xorPortB41NotScr_validFlags r41 ?_
    simpa only [ValidPotBFlags, stH, writeReg_rHold_r41 hd41H] using hVF41 δ hz
  have hHoldEq : ∀ (zX : BitAssignment n → Fin 16 → ZMod 2) δ (j : Fin k),
      (∀ q, δ (rWork q) = 0) →
      muxStNoM2 h193 isCsel r41 0 (zX δ) (stH' δ) (rHold j) =
        pkgH.pHold.fwdBits
          (fun u ↦ if h : u.val < 48 then
            coord48Of (rMuxM1 h193 isCsel r41) (rPotBPortB r41)
              (muxStNoM2 h193 isCsel r41 0 (zX δ) (stH' δ)) ⟨u.val, h⟩
          else 0) ⟨48 + j.val, by omega⟩ := fun zX δ j hz ↦ by
    rw [muxStNoM2_out h193 isCsel r41 0 (zX δ) (stH' δ) (fun q h ↦ disj_ne hd41H q j h.symm)]
    dsimp only [stH', gH]
    rw [writeReg_apply_reg,
        holdIn48k_eq_zero_tail h193 isCsel hd41H (zX δ) (st' δ) _ (fun i ↦ hHold0' δ i hz)]
    rfl
  obtain ⟨sM2, tM2, fM2⟩ := step_pInPlaceMux2_24_muxStNoM2 h193 isCsel v rWork r41 st z16L2 phL2
  obtain ⟨sFRaw, tF0, fF0, _⟩ := pkgH.step_fwd v rWork
    (rMuxM1 h193 isCsel r41) (rPotBPortB r41) rHold
    (rMuxDistScrPebIpb h193 isCsel hDX r41) (rMuxD2_18 h193 r41)
    (muxDisj_m1_portB h193 isCsel r41) hdMH (muxDisj_m1_scrPebIpb h193 isCsel hDX r41)
    (muxDisj_m1_d2 h193 isCsel r41) hdPH (muxDisj_portB_scrPebIpb h193 isCsel hDX r41)
    (muxDisj_portB_d2 h193 r41) hdHSF hdHD (muxDisj_scrPebIpb_d2 h193 isCsel hDX r41)
    (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16L2 δ) (stH' δ)) phL2
    (fun δ u _ ↦ muxStNoM2_rMuxDistScrPebIpb_zero h193 isCsel hDX r41 (z16L2 δ) (stH' δ) u)
    (hHoldEq z16L2)
  have sF : SubspaceStep _
      (mkKetOpW rWork (fun δ ↦ muxStNoM2D2 h193 isCsel r41 (z16L2 δ) (stH' δ)) phL2) _ :=
    subspaceStep_of_eq_post sFRaw (mkKetOpW_congr rWork (fun δ hz ↦ by
      rw [← hEqStH' δ, openCoordDistSq_muxStNoM2_m1_portB h193 isCsel r41 (z16L2 δ)
        (fun hs i ↦ hPB0H δ i hz hs)]
      exact muxStNoM2_writeReg_d2_xor h193 isCsel r41 (z16L2 δ) (xorPortB41NotScr r41 (stH δ)))
      (fun _ _ ↦ rfl))
  have sSc1 : SubspaceStep _
      (mkKetOpW rWork (fun δ ↦ muxStNoM2D2PebIpb h193 isCsel r41 0 (z16L2 δ) (stH' δ)) phL2) _ :=
    subspaceStep_of_eq_post
      (step_pScrubM1PebIpb_gen (Var := Var) h193 isCsel rWork r41
        (fun δ ↦ muxStNoM2D2 h193 isCsel r41 (z16L2 δ) (stH' δ)) phL2)
      (mkKetOpW_congr rWork (fun δ hz ↦ by
        have hSum := muxStNoM2D2_lsb_sum_eq_m1_16_pebIpb h193 isCsel r41 (z16L2 δ)
          (fun hs i ↦ hPB0H δ i hz hs)
        rw [hEqStH' δ] at hSum
        simp only [add_assoc] at hSum ⊢
        rw [hSum, zmod2_add_self_pebIpb]
        rfl) (fun _ _ ↦ rfl))
  obtain ⟨sBRaw, tB, fB⟩ := step_pMuxStageBNoM2_k2_pebIpb h193 isCsel (Nat.zero_le 16)
    pkgMid pkgC hKMidLE hCapMid hCap v rWork r41 stH' z16L2 phL2 hVFH'
  have sB : SubspaceStep _
      (mkKetOpW rWork (fun δ ↦ muxStNoM2D2PebIpb h193 isCsel r41 0 (z16M δ) (stH' δ)) phM) _ :=
    subspaceStep_of_eq_post sBRaw (mkKetOpW_congr rWork
      (fun δ _ ↦ by
        dsimp only [stH, z16M]
        rw [← hEqStH' δ,
            (xorPortB41NotScr_midInvar_k2 isCsel ySample13 r41 (z16L2 δ) (phL2 δ) (stH δ)).1,
            hEqStH' δ,
            (midInvar_writeReg_rHold isCsel ySample13 hd41H (z16L2 δ) (phL2 δ) (st δ) (gH δ)).1])
      (fun δ _ ↦ by
        rw [← hEqStH' δ,
            (xorPortB41NotScr_midInvar_k2 isCsel ySample13 r41 (z16L2 δ) (phL2 δ) (stH δ)).2]
        exact (midInvar_writeReg_rHold isCsel ySample13 hd41H (z16L2 δ) (phL2 δ) (st δ) (gH δ)).2))
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := scrubM1_ne h193 isCsel r41
  have sSc2 : SubspaceStep _
      (mkKetOpW rWork (fun δ ↦ muxStNoM2D2 h193 isCsel r41 (z16M δ) (stH' δ)) phM) _ :=
    subspaceStep_of_eq_post
      (step_pScrubM1PebIpb_gen (Var := Var) h193 isCsel rWork r41
        (fun δ ↦ muxStNoM2D2PebIpb h193 isCsel r41 0 (z16M δ) (stH' δ)) phM)
      (mkKetOpW_congr rWork (fun δ hz ↦ by
        have hSum := muxStNoM2D2_lsb_sum_eq_m1_16_pebIpb h193 isCsel r41 (z16M δ)
          (fun hs i ↦ hPB0H δ i hz hs)
        rw [hEqStH' δ] at hSum
        dsimp only [DFunLike.coe] at h1 h2 h3 h4 h5 h6 hSum ⊢
        rw [muxStNoM2D2PebIpb_zero_eq_update]
        dsimp only [DFunLike.coe]
        simp only [Function.update_self, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
          Function.update_of_ne h6, zero_add, Function.update_idem]
        rw [hSum, Function.update_eq_self]) (fun _ _ ↦ rfl))
  obtain ⟨sURaw, tU0, fU0, _⟩ := pkgH.step_unld v rWork
    (rMuxM1 h193 isCsel r41) (rPotBPortB r41) rHold
    (rMuxDistScrPebIpb h193 isCsel hDU r41) (rMuxD2_18 h193 r41)
    (muxDisj_m1_portB h193 isCsel r41) hdMH (muxDisj_m1_scrPebIpb h193 isCsel hDU r41)
    (muxDisj_m1_d2 h193 isCsel r41) hdPH (muxDisj_portB_scrPebIpb h193 isCsel hDU r41)
    (muxDisj_portB_d2 h193 r41) hdHSU hdHD (muxDisj_scrPebIpb_d2 h193 isCsel hDU r41)
    (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16M δ) (stH' δ)) phM
    (fun δ u _ ↦ muxStNoM2_rMuxDistScrPebIpb_zero h193 isCsel hDU r41 (z16M δ) (stH' δ) u)
    (fun δ j _ ↦ by
      have := j.isLt
      rw [show rMuxD2_18 h193 r41 j = r41 ⟨122 + j.val, by omega⟩ from
        congrArg r41.wires (Fin.ext rfl)]
      exact muxStNoM2_pool_zero h193 isCsel r41 0 _ _ (u := j.val) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)))
    (hHoldEq z16M)
  have sU : SubspaceStep
      (mkKetOpW rWork (fun δ ↦ muxStNoM2D2 h193 isCsel r41 (z16M δ) (stH' δ)) phM) _ _ :=
    subspaceStep_of_eq_pre_local
      (mkKetOpW_congr rWork (fun δ hz ↦ by
        rw [← hEqStH' δ, openCoordDistSq_muxStNoM2_m1_portB h193 isCsel r41 (z16M δ)
          (fun hs i ↦ hPB0H δ i hz hs)]
        rfl) (fun _ _ ↦ rfl))
      sURaw
  have sInner := subspaceStep_seq_u sF
    (subspaceStep_seq_u sSc1 (subspaceStep_seq_u sB (subspaceStep_seq_u sSc2 sU)))
  let r48k := rCoord48Hold h193 isCsel r41 rHold hd41H
  have hCln48k : ∀ {zX : BitAssignment n → Fin 16 → ZMod 2} (u : Wire (48 + k)),
      pkgH.sMaskHold.testBit u.val = true → ∀ δ, (∀ q, δ (rWork q) = 0) →
      muxStNoM2 h193 isCsel r41 0 (zX δ) (st' δ) (r48k u) = 0 := fun {zX} u hu δ hz ↦ by
    rw [rCoord48Hold_ge48 h193 isCsel r41 rHold hd41H u (pkgH.sMaskHold_ge48 u hu),
        muxStNoM2_out h193 isCsel r41 0 (zX δ) (st' δ) (fun q h ↦ disj_ne hd41H q _ h.symm)]
    exact hHold0' δ _ hz
  obtain ⟨sWrap, tWrap, fWrap, _⟩ := subspaceStep_wrapOnReg_mkKetOpW_mask2 v rWork r48k
    pkgH.sMaskHold pkgH.pHold k pkgH.pHold_valid pkgH.pHold_numAnd
    (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16L2 δ) (st' δ))
    (fun δ ↦ muxStNoM2 h193 isCsel r41 0 (z16M δ) (st' δ))
    phL2 phM _ hCln48k hCln48k
    (subspaceStep_of_eq_pre_local
      (mkKetOpW_congr rWork (fun δ _ ↦
        stepCB_rCoord48Hold_muxStNoM2 h193 isCsel hd41H pkgH.pHold pkgH.pHold_coords
          (z16L2 δ) (st' δ))
        (fun _ _ ↦ rfl))
      (subspaceStep_of_eq_post sInner (mkKetOpW_congr rWork (fun δ _ ↦
        (stepCB_rCoord48Hold_muxStNoM2 h193 isCsel hd41H pkgH.pHold pkgH.pHold_coords
          (z16M δ) (st' δ)).symm)
        (fun _ _ ↦ rfl))))
  obtain ⟨tSc, fSc⟩ := count_pScrubM1PebIpb (Var := Var) h193 isCsel r41
  refine ⟨subspaceStep_seq_u sM2 sWrap, ?_, ?_⟩
  · unfold pMuxHeldMid_k2_pebIpb
    rw [dc_count_seq, tM2, tWrap, dc_count_seq, dc_count_seq, dc_count_seq, dc_count_seq,
        tF0, tSc, tB, tU0]
    omega
  · unfold pMuxHeldMid_k2_pebIpb
    rw [dc_count_seq, fM2, fWrap, dc_count_seq, dc_count_seq, dc_count_seq, dc_count_seq,
        fF0, fSc, fB, fU0]

attribute [irreducible] pMuxHeldMid_k2_pebIpb

/-- Contiguous `(105 + Wp₀)`-wire core prefix of `r : QRegister (105 + Wp) n` (`Wp₀ + k = Wp`). -/
def rCorePrefix {Wp₀ k Wp n : ℕ} (hWp : Wp₀ + k = Wp) (r : QRegister (105 + Wp) n) :
    QRegister (105 + Wp₀) n :=
  r.compose (QRegister.block 0 (105 + Wp₀) (by omega))

/-- Contiguous `k`-wire held suffix `r[105 + Wp₀ .. 105 + Wp - 1]` (`Wp₀ + k = Wp`). -/
def rHoldSuffix {Wp₀ k Wp n : ℕ} (hWp : Wp₀ + k = Wp) (r : QRegister (105 + Wp) n) :
    QRegister k n :=
  r.compose (QRegister.block (105 + Wp₀) k (by omega))

theorem rCorePrefix_lt105 {Wp₀ k Wp n : ℕ} (hWp : Wp₀ + k = Wp) (r : QRegister (105 + Wp) n)
    {m : ℕ} (hm : m < 105) :
    rCorePrefix hWp r ⟨m, by omega⟩ = r ⟨m, by omega⟩ :=
  congrArg r.wires (Fin.ext (Nat.zero_add m))

theorem rCorePrefix_block_le105 {Wp₀ k Wp n : ℕ} (hWp : Wp₀ + k = Wp) (r : QRegister (105 + Wp) n)
    (b0 len : ℕ) (h1 : b0 + len ≤ 105 + Wp₀) (h2 : b0 + len ≤ 105 + Wp) :
    (rCorePrefix hWp r).compose (QRegister.block b0 len h1) =
      r.compose (QRegister.block b0 len h2) :=
  QRegister.ext (Function.Embedding.ext fun i ↦
    congrArg r.wires (Fin.ext (Nat.zero_add (b0 + i.val))))

theorem r41Of24_core_disj_hold {Wp₀ k Wp n : ℕ} (hWp : Wp₀ + k = Wp)
    (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (hdCore : (rCorePrefix hWp r).DisjointWires rCoin) :
    (r41Of24 (rCorePrefix hWp r) rCoin hdCore).DisjointWires (rHoldSuffix hWp r) :=
  disj_of_ne fun i j h ↦ by
    change f41Of24 (rCorePrefix hWp r) rCoin i = rHoldSuffix hWp r j at h
    rcases f41Of24_tag (rCorePrefix hWp r) rCoin i with ⟨ka, hka, _⟩ | ⟨ja, hja, _⟩
    · rw [hka] at h
      have hv := congrArg Fin.val (r.wires.injective h)
      simp only [QRegister.block_apply_val] at hv
      omega
    · rw [hja] at h
      exact disj_ne hd _ ja h.symm

theorem validPotBFlags24_rCorePrefix {Wp₀ k Wp n : ℕ} (hWp : Wp₀ + k = Wp)
    (r : QRegister (105 + Wp) n) {β : BitAssignment n} (h : ValidPotBFlags24 r β) :
    ValidPotBFlags24 (rCorePrefix hWp r) β := h

theorem potRefl24_rCorePrefix {Wp₀ k Wp n : ℕ} (hWp : Wp₀ + k = Wp)
    (phaseBitK : BitAssignment 17 → SubCoin63Stage4.PotBPhaseBit24Fn)
    (coinSwapK : BitAssignment 17 → SubCoin63Stage4.PotBCoinSwap24Fn)
    (isCsel : Bool) (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (st : BitAssignment n → BitAssignment n) :
    (∀ δ, potReflPortBSt24 coinSwapK isCsel (rCorePrefix hWp r) rCoin st δ =
      potReflPortBSt24 coinSwapK isCsel r rCoin st δ) ∧
    potReflPortBPh0_24 phaseBitK isCsel (rCorePrefix hWp r) rCoin st =
      potReflPortBPh0_24 phaseBitK isCsel r rCoin st := by
  have lt {m : ℕ} (hm : m < 105 := by omega) := rCorePrefix_lt105 hWp r hm
  have e0 : wPotB24LocQ (rCorePrefix hWp r) = wPotB24LocQ r := lt
  have e1 : wPotB24IsScreen (rCorePrefix hWp r) = wPotB24IsScreen r := lt
  have e2 : wPotB24IsPot (rCorePrefix hWp r) = wPotB24IsPot r := lt
  have e3 : wPotB24IsNN (rCorePrefix hWp r) = wPotB24IsNN r := lt
  have e4 : wPotB24Sp1B0 (rCorePrefix hWp r) = wPotB24Sp1B0 r := lt
  have e5 : wPotB24Sp1B1 (rCorePrefix hWp r) = wPotB24Sp1B1 r := lt
  have e6 : wPotB24Sp2B0 (rCorePrefix hWp r) = wPotB24Sp2B0 r := lt
  have e7 : wPotB24Sp2B1 (rCorePrefix hWp r) = wPotB24Sp2B1 r := lt
  have hNA : rPotB24NucA (rCorePrefix hWp r) = rPotB24NucA r :=
      rCorePrefix_block_le105 hWp r 9 24 _ _
  have hEA : rPotB24ElecA (rCorePrefix hWp r) = rPotB24ElecA r :=
      rCorePrefix_block_le105 hWp r 33 24 _ _
  have hPB : rPotB24PortB (rCorePrefix hWp r) = rPotB24PortB r :=
      rCorePrefix_block_le105 hWp r 57 24 _ _
  have hC24 : rPotBCoin24 (rCorePrefix hWp r) = rPotBCoin24 r :=
      rCorePrefix_block_le105 hWp r 81 24 _ _
  refine ⟨fun δ ↦ ?_, funext fun δ ↦ ?_⟩
  · unfold potReflPortBSt24 potB24GateActive potOraclePortB24CoinEval
    rw [e0, e1, e2, e3, e4, e5, e6, e7, hNA, hEA, hPB, hC24]
  · unfold potReflPortBPh0_24 potOraclePortB24BitEval
    rw [e0, e1, e2, e3, e4, e5, e6, e7, hNA, hEA, hPB, hC24]

theorem r41_core_preconds {W Wp Wp₀ k n : ℕ} (hWp : Wp₀ + k = Wp)
    (rWork : QRegister W n) (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hdCore : (rCorePrefix hWp r).DisjointWires rCoin)
    (st : BitAssignment n → BitAssignment n)
    (hFlags : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags24 r (st δ))
    (hWorkCln : ∀ δ (u : Fin Wp), (∀ q, δ (rWork q) = 0) → st δ (rPotBWork24 r u) = 0)
    (hPB0 : ∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
      st δ (wPotB24IsScreen r) = 0 → st δ (rPotB24PortB r i) = 0) :
    let rCore := rCorePrefix hWp r
    let rHold := rHoldSuffix hWp r
    let r41 := r41Of24 rCore rCoin hdCore
    (∀ δ (j : Fin k), (∀ q, δ (rWork q) = 0) → st δ (rHold j) = 0) ∧
    (∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin Wp₀, st δ (rPotBWork r41 u) = 0) ∧
    (∀ δ, (∀ q, δ (rWork q) = 0) →
      ∀ u : Fin Wp₀, xorPortB41NotScr r41 (st δ) (rPotBWork r41 u) = 0) ∧
    (∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags r41 (st δ)) ∧
    (∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
      st δ (wPotBIsScreen r41) = 0 → st δ (rPotBPortB r41 i) = 0) := by
  intro rCore rHold r41
  have hWk41 : ∀ δ, (∀ q, δ (rWork q) = 0) → ∀ u : Fin Wp₀, st δ (rPotBWork r41 u) = 0 :=
    fun δ hz u ↦ (congrArg (st δ) (r41Of24_work rCore rCoin hdCore u)).trans
      ((congrArg (st δ) (congrArg r.wires (Fin.ext (Nat.zero_add (105 + u.val))))).trans
        (hWorkCln δ ⟨u.val, by omega⟩ hz))
  refine ⟨fun δ j hz ↦ (congrArg (st δ) (congrArg r.wires (Fin.ext
      (by omega : 105 + Wp₀ + j.val = 105 + (Wp₀ + j.val))))).trans
      (hWorkCln δ ⟨Wp₀ + j.val, by omega⟩ hz),
    hWk41, fun δ hz u ↦ (xorPortB41NotScr_work r41 (st δ) u).trans (hWk41 δ hz u),
    fun δ hz ↦ validPotBFlags_r41Of24 rCore rCoin hdCore (hFlags δ hz),
    pb0_r41Of24_pebIpb rWork rCore rCoin hdCore fun δ i hz hs ↦ by
      rw [show rPotB24PortB rCore i = rPotB24PortB r i from
        congrArg r.wires (Fin.ext (Nat.zero_add (57 + i.val)))]
      exact hPB0 δ i hz hs⟩

/-- `M = 0` `Usel` Stage-4 core with `k`-wire prefix-held `Dist18`. -/
def pMuxHeldCore_usel_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {Wp₀ k kScr tSB kScrF tF kScrU tU kMid tMid tCoul n : ℕ}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp₀) (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp₀ - 25) (hDU : 18 + kScrU ≤ Wp₀ - 25)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp₀ false)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp₀ false)
    (v : Var) (r41 : QRegister (122 + Wp₀) n) (rHold : QRegister k n)
    (hd41H : r41.DisjointWires rHold) : DynamicCircuit Var n :=
  wrapGateCsel h193 false v r41
    (wrapMux1Dist h193 false v r41 0 24 (by omega)
      ((pMuxDualLegsBlock_dsc50 h193 false pkgSB hScr v r41).seq
        (pMuxHeldMid_k2_pebIpb h193 false pkgH pkgMid pkgC hDX hDU hCapMid hCap
          v r41 rHold hd41H)))

/-- `M = 0` `Usel` lifted Stage-4 circuit slicing `r` into `(105 + Wp₀)` core + `k` held suffix. -/
def pMuxHeldStage4_usel_k2_pebIpb {Var : Type}
    {Wp Wp₀ k kScr tSB kScrF tF kScrU tU kMid tMid tCoul n : ℕ}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (hWp : Wp₀ + k = Wp) (h193 : 193 ≤ Wp₀)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp₀ - 25) (hDU : 18 + kScrU ≤ Wp₀ - 25)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp₀ false)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp₀ false)
    (v : Var) (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n) : DynamicCircuit Var n :=
  liftFinDyn_c70 fun [Fintype Var] [DecidableEq Var] ↦
    @dite _ (r.DisjointWires rCoin) (Classical.dec _)
      (fun hd ↦
        let hdCore : (rCorePrefix hWp r).DisjointWires rCoin :=
          disj_of_ne fun _ j h ↦ disj_ne hd _ j h
        pMuxHeldCore_usel_k2_pebIpb h193 pkgSB hScr pkgH pkgMid pkgC hDX hDU hCapMid hCap v
          (r41Of24 (rCorePrefix hWp r) rCoin hdCore) (rHoldSuffix hWp r)
          (r41Of24_core_disj_hold hWp r rCoin hd hdCore))
      (fun _ ↦ .circuit .identity)

theorem dynWires_pMuxHeldStage4_usel_k2_pebIpb {Var : Type}
    {Wp Wp₀ k kScr tSB kScrF tF kScrU tU kMid tMid tCoul n : ℕ} {S : Wire n → Prop}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (hWp : Wp₀ + k = Wp) (h193 : 193 ≤ Wp₀)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58) (hSBSafe : ShortBin7CtrlSafe pkgSB)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp₀ - 25) (hDU : 18 + kScrU ≤ Wp₀ - 25)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp₀ false)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp₀ false)
    (v : Var) (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hSr : ∀ i : Fin (105 + Wp), S (r i)) (hSc : ∀ j : Fin 17, S (rCoin j)) :
    DynWires S (pMuxHeldStage4_usel_k2_pebIpb hWp h193 pkgSB hScr pkgH pkgMid pkgC
      hDX hDU hCapMid hCap v r rCoin) := by
  refine (DynCtrlSafe.liftFinDyn (S_ctrl := S) (S_tgt := S) _ ?_).to_dynWires
  intro _ _
  split_ifs with hd
  · let rCore := rCorePrefix hWp r
    let hdCore : rCore.DisjointWires rCoin := disj_of_ne fun _ j h ↦ disj_ne hd _ j h
    let r41 := r41Of24 rCore rCoin hdCore
    have hSr41 : ∀ q, S (r41 q) := r41Of24_ctrl rCore rCoin hdCore (fun _ ↦ hSr _) hSc
    have hTr41 (q : Fin (122 + Wp₀)) (_ : IsNonNucPortB41Idx q.val) : S (r41 q) := hSr41 q
    exact ctrlSafe_wrapGateCsel h193 false v r41 _ hSr41 hTr41
      (ctrlSafe_wrapMux1Dist h193 false v r41 0 24 (by omega) _ hSr41 hTr41
        (.seq (ctrlSafe_pMuxDualLegsBlock_dsc50 h193 false pkgSB hScr hSBSafe v r41 hSr41 hTr41)
          (ctrlSafe_pMuxHeldMid_k2_pebIpb h193 false pkgH pkgMid pkgC hDX hDU hCapMid hCap
            v r41 (rHoldSuffix hWp r) (r41Of24_core_disj_hold hWp r rCoin hd hdCore) hSr41 (fun _ ↦
                hSr _))))
  · exact .identity S S

theorem writeReg_z16_work_zero {Wp₀ n : ℕ} (r41 : QRegister (122 + Wp₀) n)
    (βX : BitAssignment n) (zX : Fin 16 → ZMod 2)
    (hwk : ∀ u : Fin Wp₀, βX (rPotBWork r41 u) = 0) (u : Fin Wp₀) :
    writeReg βX (rMuxZ16 r41) zX (r41 ⟨122 + u.val, by omega⟩) = 0 :=
  (writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ r41_blk_ne_wire r41 j _ (by omega) hj).trans
    ((congrArg βX (congrArg r41.wires (Fin.ext rfl))).trans (hwk u))

theorem gateWrapMux_m1_zero {Wp₀ n : ℕ} (h193 : 193 ≤ Wp₀) (isCsel : Bool)
    (r41 : QRegister (122 + Wp₀) n) (stZ : BitAssignment n) (i : Fin 24)
    (hwkZ : ∀ u : Fin Wp₀, stZ (r41 ⟨122 + u.val, by omega⟩) = 0) :
    gateWrapMux h193 isCsel r41 stZ (rMuxM1 h193 isCsel r41 i) = 0 := by
  have hw := wtop_ge192 h193 isCsel
  have hwle := wtop_le_wp Wp₀ isCsel
  have hi := i.isLt
  have hM1 (b : Bool) : rMuxM1 h193 b r41 i = r41 ⟨122 + (Wtop Wp₀ b - 48 + i.val), by
      have := wtop_ge192 h193 b
      have := wtop_le_wp Wp₀ b
      omega⟩ :=
    congrArg r41.wires (Fin.ext (by
      have := wtop_ge192 h193 b
      simp only [QRegister.block_apply_val]
      omega))
  unfold gateWrapMux
  cases isCsel <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact hM1 false ▸ hwkZ ⟨Wtop Wp₀ false - 48 + i.val, by omega⟩
  · have hwt : Wtop Wp₀ true = Wp₀ - 1 := rfl
    rw [Function.update_of_ne (r41_blk_ne_wire r41 i _ (by
          rw [hwt]
          omega)), hM1 true]
    exact hwkZ ⟨Wtop Wp₀ true - 48 + i.val, by omega⟩

theorem step_pMuxHeldCore_usel_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp Wp₀ k kScr tSB kScrF tF kScrU tU kMid tMid tCoul n : ℕ} [NeZero (2 ^ n)]
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (hWp : Wp₀ + k = Wp) (h193 : 193 ≤ Wp₀)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp₀ - 25) (hDU : 18 + kScrU ≤ Wp₀ - 25)
    (hKMidLE : kMid ≤ pkgC.kMid)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp₀ false)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp₀ false)
    (v : Var) (rWork : QRegister W n)
    (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n) (hd : r.DisjointWires rCoin)
    (st : BitAssignment n → BitAssignment n)
    (hFlags : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags24 r (st δ))
    (hWorkCln : ∀ δ (u : Fin Wp), (∀ q, δ (rWork q) = 0) → st δ (rPotBWork24 r u) = 0)
    (hPB0 : ∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
      st δ (wPotB24IsScreen r) = 0 → st δ (rPotB24PortB r i) = 0) :
    let rCore := rCorePrefix hWp r
    let rHold := rHoldSuffix hWp r
    let hdCore : rCore.DisjointWires rCoin := disj_of_ne fun _ j h ↦ disj_ne hd _ j h
    let r41 := r41Of24 rCore rCoin hdCore
    let hd41H := r41Of24_core_disj_hold hWp r rCoin hd hdCore
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60
      midOWHi16U10TopPreK58Pkg_104
    let z16Init := fun δ (j : Fin 16) ↦ st δ (rMuxZ16 r41 j)
    let z16L1 := fun δ ↦ z16AddVal (z16Init δ) (v1Mux false pkgLM r41 (st δ))
    let z16L2 := fun δ ↦ z16AddVal (z16L1 δ) (v2Mux false pkgLM r41 (st δ))
    let phL2 := fun δ ↦ phAddVal (z16Init δ) (v1Mux false pkgLM r41 (st δ)) +
      phAddVal (z16L1 δ) (v2Mux false pkgLM r41 (st δ))
    let z16M := fun δ ↦ z16AfterMidK2 false ySample13 r41 (z16L2 δ) (st δ)
    let phM := fun δ ↦ phAfterMidK2 false ySample13 r41 (z16L2 δ) (phL2 δ) (st δ)
    let pCore := pMuxHeldCore_usel_k2_pebIpb h193 pkgSB hScr pkgH pkgMid pkgC
      hDX hDU hCapMid hCap v r41 rHold hd41H
    SubspaceStep
      (mkKetOpW rWork st (fun _ ↦ 0))
      (mkKetOpW rWork (fun δ ↦ writeReg (xorPortB41NotScr r41 (st δ)) (rMuxZ16 r41) (z16M δ)) phM)
      pCore ∧
    pCore.count .T = 192 + (2 * tSB + 180) + 4 * k + tF + tCoul + tMid + tU ∧
    pCore.count .TOFF = 0 := by
  intro rCore rHold hdCore r41 hd41H pkgLM z16Init z16L1 z16L2 phL2 z16M phM
  have := And.intro (wtop_ge192 h193 false) (wtop_le_wp Wp₀ false)
  let st' := fun δ ↦ xorPortB41NotScr r41 (st δ)
  obtain ⟨hHold0, hWk41, hWk41', hVF41, hPB41⟩ :=
    r41_core_preconds hWp rWork r rCoin hdCore st hFlags hWorkCln hPB0
  obtain ⟨sLegs, tLegs, fLegs⟩ := step_pMuxDualLegsBlock_dsc50 h193 false pkgSB hScr
    midOWHi16U10TopPreK58Pkg_104 v rWork r41 st z16Init hVF41
  obtain ⟨sMid, tMidC, fMidC⟩ := step_pMuxHeldMid_k2_pebIpb h193 false pkgH pkgMid pkgC
    hDX hDU hKMidLE hCapMid hCap v rWork r41 rHold hd41H st z16L2 phL2 hVF41 hPB41 hHold0
  obtain ⟨sM1, tM1, fM1⟩ := step_wrapMux1Dist h193 false v rWork r41 0 24 (by omega)
    (fun δ ↦ gateWrapMux h193 false r41 (writeReg (st δ) (rMuxZ16 r41) (z16Init δ)))
    (fun δ ↦ gateWrapMux h193 false r41 (writeReg (st' δ) (rMuxZ16 r41) (z16M δ)))
    (fun _ ↦ 0) phM _
    (fun δ i _ hz ↦
      ⟨gateWrapMux_m1_zero h193 false r41 _ i (writeReg_z16_work_zero r41 _ _ (hWk41 δ hz)),
       gateWrapMux_m1_zero h193 false r41 _ i (writeReg_z16_work_zero r41 _ _ (hWk41' δ hz))⟩)
    (subspaceStep_of_eq_pre_local
      (mkKetOpW_congr rWork (fun δ hz ↦
        outer_wrappers_noM2 h193 false (Nat.zero_le 24) r41 (z16Init δ) (hWk41 δ hz))
        (fun _ _ ↦ rfl))
      (subspaceStep_of_eq_post (subspaceStep_seq_u sLegs sMid)
        (mkKetOpW_congr rWork (fun δ hz ↦
          (outer_wrappers_noM2 h193 false (Nat.zero_le 24) r41 (z16M δ) (hWk41' δ hz)).symm)
          (fun _ _ ↦ rfl))))
  have heqG : (⟨122 + Wp₀ - 1, by omega⟩ : Fin (122 + Wp₀)) = ⟨122 + (Wp₀ - 1), by omega⟩ :=
    Fin.ext (by omega : 122 + Wp₀ - 1 = 122 + (Wp₀ - 1))
  obtain ⟨sG, tG, fG⟩ := step_wrapGateCsel h193 false v rWork r41
    (fun δ ↦ writeReg (st δ) (rMuxZ16 r41) (z16Init δ))
    (fun δ ↦ writeReg (st' δ) (rMuxZ16 r41) (z16M δ)) (fun _ ↦ 0) phM _
    (fun δ hz ↦ heqG ▸
      ⟨writeReg_z16_work_zero r41 (st δ) (z16Init δ) (hWk41 δ hz) ⟨Wp₀ - 1, by omega⟩,
       writeReg_z16_work_zero r41 (st' δ) (z16M δ) (hWk41' δ hz) ⟨Wp₀ - 1, by omega⟩⟩) sM1
  refine ⟨subspaceStep_of_eq_pre_local
    (mkKetOpW_congr rWork (fun δ _ ↦ (writeReg_self_z16_local (rMuxZ16 r41) (st δ)).symm)
      (fun _ _ ↦ rfl)) sG, ?_, by
        change (wrapGateCsel h193 _ _ _ _).count .TOFF = 0
        rw [fG, fM1, dc_count_seq, fLegs, fMidC]⟩
  change (wrapGateCsel h193 _ _ _ _).count .T = _
  rw [tG, tM1, dc_count_seq, tLegs, tMidC]
  simp only [Bool.false_eq_true, ↓reduceIte]
  omega

attribute [irreducible] pMuxHeldCore_usel_k2_pebIpb

/-- `M = 0` `Csel` Stage-4 core with `k`-wire prefix-held `Dist18`. -/
def pMuxHeldCore_csel8_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {Wp₀ k kScr tSB kScrF tF kScrU tU kMid tMid tCoul n : ℕ}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (h193 : 193 ≤ Wp₀) (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp₀ - 25) (hDU : 18 + kScrU ≤ Wp₀ - 25)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp₀ true)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp₀ true)
    (v : Var) (r41 : QRegister (122 + Wp₀) n) (rHold : QRegister k n)
    (hd41H : r41.DisjointWires rHold) : DynamicCircuit Var n :=
  (pCselMonoHdrComp_193 h193 v r41).seq
    ((wrapMux1Dist h193 true v r41 0 24 (by omega)
        ((pMuxDualLegsInner_dsc50 h193 true pkgSB hScr v r41).seq
          ((pCselHdr2Unld0_193 h193 v r41).seq
            (pMuxHeldMid_k2_pebIpb h193 true pkgH pkgMid pkgC hDX hDU hCapMid hCap
              v r41 rHold hd41H)))).seq
      (pCselGateUnld0_193 h193 v r41))

/-- `M = 0` `Csel` lifted Stage-4 circuit slicing `r` into `(105 + Wp₀)` core + `k` held suffix. -/
def pMuxHeldStage4_csel8_k2_pebIpb {Var : Type}
    {Wp Wp₀ k kScr tSB kScrF tF kScrU tU kMid tMid tCoul n : ℕ}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (hWp : Wp₀ + k = Wp) (h193 : 193 ≤ Wp₀)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp₀ - 25) (hDU : 18 + kScrU ≤ Wp₀ - 25)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp₀ true)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp₀ true)
    (v : Var) (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n) : DynamicCircuit Var n :=
  liftFinDyn_c70 fun [Fintype Var] [DecidableEq Var] ↦
    @dite _ (r.DisjointWires rCoin) (Classical.dec _)
      (fun hd ↦
        let hdCore : (rCorePrefix hWp r).DisjointWires rCoin :=
          disj_of_ne fun _ j h ↦ disj_ne hd _ j h
        pMuxHeldCore_csel8_k2_pebIpb h193 pkgSB hScr pkgH pkgMid pkgC hDX hDU hCapMid hCap v
          (r41Of24 (rCorePrefix hWp r) rCoin hdCore) (rHoldSuffix hWp r)
          (r41Of24_core_disj_hold hWp r rCoin hd hdCore))
      (fun _ ↦ .circuit .identity)

theorem dynWires_pMuxHeldStage4_csel8_k2_pebIpb {Var : Type}
    {Wp Wp₀ k kScr tSB kScrF tF kScrU tU kMid tMid tCoul n : ℕ} {S : Wire n → Prop}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (hWp : Wp₀ + k = Wp) (h193 : 193 ≤ Wp₀)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58) (hSBSafe : ShortBin7CtrlSafe pkgSB)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp₀ - 25) (hDU : 18 + kScrU ≤ Wp₀ - 25)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp₀ true)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp₀ true)
    (v : Var) (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hSr : ∀ i : Fin (105 + Wp), S (r i)) (hSc : ∀ j : Fin 17, S (rCoin j)) :
    DynWires S (pMuxHeldStage4_csel8_k2_pebIpb hWp h193 pkgSB hScr pkgH pkgMid pkgC
      hDX hDU hCapMid hCap v r rCoin) := by
  refine (DynCtrlSafe.liftFinDyn (S_ctrl := S) (S_tgt := S) _ ?_).to_dynWires
  intro _ _
  split_ifs with hd
  · let rCore := rCorePrefix hWp r
    let hdCore : rCore.DisjointWires rCoin := disj_of_ne fun _ j h ↦ disj_ne hd _ j h
    let r41 := r41Of24 rCore rCoin hdCore
    have hSr41 : ∀ q, S (r41 q) := r41Of24_ctrl rCore rCoin hdCore (fun _ ↦ hSr _) hSc
    have hTr41 (q : Fin (122 + Wp₀)) (_ : IsNonNucPortB41Idx q.val) : S (r41 q) := hSr41 q
    have hST41 (q : Fin (122 + Wp₀)) (_ : IsNonNucPortB41Idx q.val) : S (r41 q) ∧ S (r41 q) :=
        ⟨hSr41 q, hSr41 q⟩
    exact .seq (ctrlSafe_pCselMonoHdrComp_193 h193 v r41 hST41)
      (.seq (ctrlSafe_wrapMux1Dist h193 true v r41 0 24 (by omega) _ hSr41 hTr41
          (.seq (ctrlSafe_pMuxDualLegsInner_dsc50 h193 true pkgSB hScr hSBSafe v r41 hSr41 hTr41)
            (.seq (ctrlSafe_pCselHdr2Unld0_193 h193 v r41 hST41)
              (ctrlSafe_pMuxHeldMid_k2_pebIpb h193 true pkgH pkgMid pkgC hDX hDU hCapMid hCap
                v r41 (rHoldSuffix hWp r)
                    (r41Of24_core_disj_hold hWp r rCoin hd hdCore) hSr41 (fun _ ↦ hSr _)))))
        (ctrlSafe_pCselGateUnld0_193 h193 v r41 hST41))
  · exact .identity S S

theorem step_pMuxHeldCore_csel8_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp Wp₀ k kScr tSB kScrF tF kScrU tU kMid tMid tCoul n : ℕ} [NeZero (2 ^ n)]
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (hWp : Wp₀ + k = Wp) (h193 : 193 ≤ Wp₀)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgH : Dist18HeldSplitPkg k kScrF tF kScrU tU)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid) (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDX : 18 + kScrF ≤ Wp₀ - 25) (hDU : 18 + kScrU ≤ Wp₀ - 25)
    (hKMidLE : kMid ≤ pkgC.kMid)
    (hCapMid : 54 + kMid + 48 ≤ Wtop Wp₀ true)
    (hCap : 54 + pkgC.kRest + 23 ≤ Wtop Wp₀ true)
    (v : Var) (rWork : QRegister W n)
    (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n) (hd : r.DisjointWires rCoin)
    (st : BitAssignment n → BitAssignment n)
    (hFlags : ∀ δ, (∀ q, δ (rWork q) = 0) → ValidPotBFlags24 r (st δ))
    (hWorkCln : ∀ δ (u : Fin Wp), (∀ q, δ (rWork q) = 0) → st δ (rPotBWork24 r u) = 0)
    (hPB0 : ∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
      st δ (wPotB24IsScreen r) = 0 → st δ (rPotB24PortB r i) = 0) :
    let rCore := rCorePrefix hWp r
    let rHold := rHoldSuffix hWp r
    let hdCore : rCore.DisjointWires rCoin := disj_of_ne fun _ j h ↦ disj_ne hd _ j h
    let r41 := r41Of24 rCore rCoin hdCore
    let hd41H := r41Of24_core_disj_hold hWp r rCoin hd hdCore
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60
      midOWHi16U10TopPreK58Pkg_104
    let z16Init := fun δ (j : Fin 16) ↦ st δ (rMuxZ16 r41 j)
    let z16L1 := fun δ ↦ z16AddVal (z16Init δ) (v1Mux true pkgLM r41 (st δ))
    let z16L2 := fun δ ↦ z16AddVal (z16L1 δ) (v2Mux true pkgLM r41 (st δ))
    let phL2 := fun δ ↦ phAddVal (z16Init δ) (v1Mux true pkgLM r41 (st δ)) +
      phAddVal (z16L1 δ) (v2Mux true pkgLM r41 (st δ))
    let z16M := fun δ ↦ z16AfterMidK2 true ySample13 r41 (z16L2 δ) (st δ)
    let phM := fun δ ↦ phAfterMidK2 true ySample13 r41 (z16L2 δ) (phL2 δ) (st δ)
    let pCore := pMuxHeldCore_csel8_k2_pebIpb h193 pkgSB hScr pkgH pkgMid pkgC
      hDX hDU hCapMid hCap v r41 rHold hd41H
    SubspaceStep
      (mkKetOpW rWork st (fun _ ↦ 0))
      (mkKetOpW rWork (fun δ ↦ writeReg (xorPortB41NotScr r41 (st δ)) (rMuxZ16 r41) (z16M δ)) phM)
      pCore ∧
    pCore.count .T = 200 + (2 * tSB + 180) + 4 * k + tF + tCoul + tMid + tU ∧
    pCore.count .TOFF = 0 := by
  intro rCore rHold hdCore r41 hd41H pkgLM z16Init z16L1 z16L2 phL2 z16M phM
  have hw := wtop_ge192 h193 true
  have hwle := wtop_le_wp Wp₀ true
  have hwt : Wtop Wp₀ true = Wp₀ - 1 := rfl
  let st' := fun δ ↦ xorPortB41NotScr r41 (st δ)
  obtain ⟨hHold0, hWk41, hWk41', hVF41, hPB41⟩ :=
    r41_core_preconds hWp rWork r rCoin hdCore st hFlags hWorkCln hPB0
  let stZIn := fun δ ↦ writeReg (st δ) (rMuxZ16 r41) (z16Init δ)
  let stZOut := fun δ ↦ writeReg (st' δ) (rMuxZ16 r41) (z16M δ)
  let stGIn := fun δ ↦ gateWrapMux h193 true r41 (stZIn δ)
  let stGOut := fun δ ↦ gateWrapMux h193 true r41 (stZOut δ)
  let stGHInit := fun δ ↦ hdrWrapMux h193 true r41 (stGIn δ)
  have hWkZIn (δ) (u : Fin Wp₀) (hz : ∀ q, δ (rWork q) = 0) :=
    writeReg_z16_work_zero r41 (st δ) (z16Init δ) (hWk41 δ hz) u
  have hWkZOut (δ) (u : Fin Wp₀) (hz : ∀ q, δ (rWork q) = 0) :=
    writeReg_z16_work_zero r41 (st' δ) (z16M δ) (hWk41' δ hz) u
  have heqG : (⟨122 + Wp₀ - 1, by omega⟩ : Fin (122 + Wp₀)) = ⟨122 + (Wp₀ - 1), by omega⟩ :=
    Fin.ext (by
      dsimp only
      omega)
  have sMono := step_pCselMonoHdrComp_193 h193 v rWork r41 stZIn (fun _ ↦ 0)
    (fun δ hz ↦ by
      have hf := validPotBFlags24_rCorePrefix hWp r (hFlags δ hz)
      have hCtrl (m : ℕ) (hm : m < 81 := by omega) :
          stZIn δ (r41 ⟨m, by omega⟩) = st δ (rCore ⟨m, by omega⟩) :=
        (writeReg_apply_of_not_mem _ _ _ _
          (fun ⟨j, hj⟩ ↦ r41_blk_ne_wire r41 j _ (by omega) hj)).trans
          (congrArg (st δ) (r41Of24_lt81 rCore rCoin hdCore (m := m) hm))
      rw [hCtrl 1, hCtrl 2, hCtrl 4]
      exact ⟨fun hp ↦ (hf.1 hp).1, hf.2⟩)
    (hWkZIn · ⟨0, by omega⟩) (hWkZIn · ⟨1, by omega⟩) (hWkZIn · ⟨2, by omega⟩)
    (hWkZIn · ⟨3, by omega⟩) (hWkZIn · ⟨4, by omega⟩) (hWkZIn · ⟨118, by omega⟩)
    (hWkZIn · ⟨119, by omega⟩) (fun δ hz ↦ heqG ▸ hWkZIn δ ⟨Wp₀ - 1, by omega⟩ hz)
  obtain ⟨tMono, fMono⟩ := count_pCselMonoHdrComp_193 h193 v r41
  obtain ⟨sLegs, tLegs, fLegs⟩ := step_pMuxDualLegsInner_dsc50 h193 true pkgSB hScr
    midOWHi16U10TopPreK58Pkg_104 v rWork r41 st z16Init hVF41
  have sUnld := step_pCselHdr2Unld0_193 h193 v rWork r41
    (fun δ ↦ muxStNoM2 h193 true r41 0 (z16L2 δ) (st δ)) phL2
    (fun δ _ ↦ muxStNoM2_240_zero h193 true r41 _ _ _)
    (fun δ _ ↦ muxStNoM2_241_zero h193 true r41 _ _ _)
  obtain ⟨tUnld, fUnld⟩ := count_pCselHdr2Unld0_193 h193 v r41
  obtain ⟨sMid, tMidC, fMidC⟩ := step_pMuxHeldMid_k2_pebIpb h193 true pkgH pkgMid pkgC
    hDX hDU hKMidLE hCapMid hCap v rWork r41 rHold hd41H st z16L2 phL2 hVF41 hPB41 hHold0
  obtain ⟨sM1, tM1, fM1⟩ := step_wrapMux1Dist h193 true v rWork r41 0 24 (by omega)
    stGHInit stGOut (fun _ ↦ 0) phM _
    (fun δ i _ hz ↦ by
      have hiLt := i.isLt
      refine ⟨?_, gateWrapMux_m1_zero h193 true r41 (stZOut δ) i (fun u ↦ hWkZOut δ u hz)⟩
      dsimp only [stGHInit]
      have heq : rMuxM1 h193 true r41 i = r41 ⟨122 + (Wp₀ - 1) - 48 + i.val, by omega⟩ :=
        congrArg r41.wires (Fin.ext rfl)
      rw [heq, hdrWrapMux_keep h193 true r41 _ _ _ (by omega) (by omega), ← heq]
      exact gateWrapMux_m1_zero h193 true r41 (stZIn δ) i (fun u ↦ hWkZIn δ u hz))
    (subspaceStep_of_eq_pre_local
      (mkKetOpW_congr rWork (fun δ hz ↦ by
        dsimp only [stGHInit, stGIn, stZIn]
        rw [mux1DistBit_hdrWrapMux_210 h193 r41, writeSub24_hdrWrapMux_m1_193 h193 r41]
        exact congrArg (hdrWrapMux h193 true r41)
          (outer_wrappers_noM2 h193 true (Nat.zero_le 24) r41 (z16Init δ) (hWk41 δ hz)))
        (fun _ _ ↦ rfl))
      (subspaceStep_of_eq_post (subspaceStep_seq_u sLegs (subspaceStep_seq_u sUnld sMid))
        (mkKetOpW_congr rWork (fun δ hz ↦
          (outer_wrappers_noM2 h193 true (Nat.zero_le 24) r41 (z16M δ) (hWk41' δ hz)).symm)
          (fun _ _ ↦ rfl))))
  have sGateU := step_pCselGateUnld0_193 h193 v rWork r41 stZOut phM
    (fun δ hz ↦ heqG ▸ hWkZOut δ ⟨Wp₀ - 1, by omega⟩ hz)
  obtain ⟨tGateU, fGateU⟩ := count_pCselGateUnld0_193 h193 v r41
  refine ⟨subspaceStep_of_eq_pre_local
    (mkKetOpW_congr rWork (fun δ _ ↦ (writeReg_self_z16_local (rMuxZ16 r41) (st δ)).symm)
      (fun _ _ ↦ rfl))
    (subspaceStep_seq_u sMono (subspaceStep_seq_u sM1 sGateU)), ?_, ?_⟩
  · unfold pMuxHeldCore_csel8_k2_pebIpb
    rw [dc_count_seq, dc_count_seq, tMono, tGateU, tM1,
        dc_count_seq, dc_count_seq, tLegs, tUnld, tMidC]
    omega
  · unfold pMuxHeldCore_csel8_k2_pebIpb
    rw [dc_count_seq, dc_count_seq, fMono, fGateU, fM1,
        dc_count_seq, dc_count_seq, fLegs, fUnld, fMidC]

attribute [irreducible] pMuxHeldCore_csel8_k2_pebIpb

theorem stage4_post_of_core {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp Wp₀ k n : ℕ} [NeZero (2 ^ n)]
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (hWp : Wp₀ + k = Wp) (isCsel : Bool)
    (rW : QRegister W n) (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hdCore : (rCorePrefix hWp r).DisjointWires rCoin)
    (st : BitAssignment n → BitAssignment n)
    (hFlags : ∀ δ, (∀ q : Fin W, δ (rW q) = 0) → ValidPotBFlags24 r (st δ))
    {pCore : DynamicCircuit Var n}
    (sCore :
      let r41 := r41Of24 (rCorePrefix hWp r) rCoin hdCore
      let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60
        midOWHi16U10TopPreK58Pkg_104
      let z16Init := fun δ (j : Fin 16) ↦ st δ (rMuxZ16 r41 j)
      let z16L1 := fun δ ↦ z16AddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ))
      let z16L2 := fun δ ↦ z16AddVal (z16L1 δ) (v2Mux isCsel pkgLM r41 (st δ))
      let phL2 := fun δ ↦ phAddVal (z16Init δ) (v1Mux isCsel pkgLM r41 (st δ)) +
        phAddVal (z16L1 δ) (v2Mux isCsel pkgLM r41 (st δ))
      let z16M := fun δ ↦ z16AfterMidK2 isCsel ySample13 r41 (z16L2 δ) (st δ)
      let phM := fun δ ↦ phAfterMidK2 isCsel ySample13 r41 (z16L2 δ) (phL2 δ) (st δ)
      SubspaceStep (mkKetOpW rW st (fun _ ↦ 0))
        (mkKetOpW rW (fun δ ↦ writeReg (xorPortB41NotScr r41 (st δ)) (rMuxZ16 r41) (z16M δ)) phM)
        pCore) :
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60
      midOWHi16U10TopPreK58Pkg_104
    let sliceK := owK2ReflPotSliceSpec24 pkgLM.v1Fin8 pkgLM.v2Fin8 ySample13
    SubspaceStep (mkKetOpW rW st (fun _ ↦ 0))
      (mkKetOpW rW
        (fun δ ↦ xorPortB24NotScr r
          (potReflPortBSt24 (fun γ ↦ (sliceK γ).coinSwap) isCsel r rCoin st δ))
        (potReflPortBPh0_24 (fun γ ↦ (sliceK γ).phaseBit) isCsel r rCoin st))
      pCore := by
  intro pkgLM sliceK
  let rCore := rCorePrefix hWp r
  obtain ⟨hStEq, hPhEq⟩ := potRefl24_rCorePrefix hWp
    (fun γ ↦ (sliceK γ).phaseBit) (fun γ ↦ (sliceK γ).coinSwap) isCsel r rCoin st
  refine subspaceStep_of_eq_post sCore (mkKetOpW_congr rW (fun δ hz ↦ ?_) (fun δ hz ↦ ?_))
  · exact (xorPortB41NotScr_writeReg_z16_comm (r41Of24 rCore rCoin hdCore) (st δ) _).trans
      ((congrArg (xorPortB41NotScr (r41Of24 rCore rCoin hdCore))
        (mux_k2_final_eq_potRefl24 isCsel pkgLM rCore rCoin hdCore st
          (validPotBFlags24_rCorePrefix hWp r (hFlags δ hz))).1).trans
        ((xorPortB41NotScr_eq_24 rCore rCoin hdCore _).trans
          ((by
            unfold xorPortB24NotScr
            rw [show rPotB24PortB rCore =
                rPotB24PortB r from rCorePrefix_block_le105 hWp r 57 24 _ _,
                show wPotB24IsScreen rCore =
                    wPotB24IsScreen r from rCorePrefix_lt105 hWp r (by omega),
                show rPotB24NucA rCore =
                    rPotB24NucA r from rCorePrefix_block_le105 hWp r 9 24 _ _] :
              xorPortB24NotScr rCore _ = xorPortB24NotScr r _).trans
            (congrArg (xorPortB24NotScr r) (hStEq δ)))))
  · exact (mux_k2_final_eq_potRefl24 isCsel pkgLM rCore rCoin hdCore st
      (validPotBFlags24_rCorePrefix hWp r (hFlags δ hz))).2.trans (congrFun hPhEq δ)

theorem step_and_counts_pMuxHeldStage4_k2_pebIpb {Var : Type} [Fintype Var] [DecidableEq Var]
    {W Wp WpU kU WpC kC kScr tSB kScrFU tFU kScrUU tUU kScrFC tFC kScrUC tUC : ℕ}
    {kMid tMid tCoul tPotU tPotC n : ℕ} [NeZero (2 ^ n)]
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (hWpU : WpU + kU = Wp) (hWpC : WpC + kC = Wp)
    (h193U : 193 ≤ WpU) (h193C : 193 ≤ WpC)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (pkgHU : Dist18HeldSplitPkg kU kScrFU tFU kScrUU tUU)
    (pkgHC : Dist18HeldSplitPkg kC kScrFC tFC kScrUC tUC)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid)
    (pkgC : CoulOWScrPkg13 tCoul ySample13)
    (hDXU : 18 + kScrFU ≤ WpU - 25) (hDUU : 18 + kScrUU ≤ WpU - 25)
    (hDXC : 18 + kScrFC ≤ WpC - 25) (hDUC : 18 + kScrUC ≤ WpC - 25)
    (hKMidLE : kMid ≤ pkgC.kMid)
    (hCapMidU : 54 + kMid + 48 ≤ WpU) (hCapMidC : 54 + kMid + 48 ≤ WpC - 1)
    (hCapU : 54 + pkgC.kRest + 23 ≤ WpU) (hCapC : 54 + pkgC.kRest + 23 ≤ WpC - 1)
    (htU : 192 + (2 * tSB + 180) + 4 * kU + tFU + tCoul + tMid + tUU = tPotU)
    (htC : 200 + (2 * tSB + 180) + 4 * kC + tFC + tCoul + tMid + tUC = tPotC)
    (v : Var) (rW : QRegister W n)
    (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (isCsel : Bool)
    (st : BitAssignment n → BitAssignment n)
    (hFlags : ∀ δ, (∀ q : Fin W, δ (rW q) = 0) → ValidPotBFlags24 r (st δ))
    (hWorkCln : ∀ δ (u : Fin Wp), (∀ q : Fin W, δ (rW q) = 0) → st δ (rPotBWork24 r u) = 0)
    (hPB0 : ∀ δ (i : Fin 24), (∀ q : Fin W, δ (rW q) = 0) →
      st δ (wPotB24IsScreen r) = 0 → st δ (rPotB24PortB r i) = 0) :
    let pkgLM := owLegsMidPkgDualLegOfMid leg1DualLegPass84 leg2DualLegPass60
      midOWHi16U10TopPreK58Pkg_104
    let sliceK := owK2ReflPotSliceSpec24 pkgLM.v1Fin8 pkgLM.v2Fin8 ySample13
    let p := if isCsel then
      pMuxHeldStage4_csel8_k2_pebIpb hWpC h193C pkgSB hScr pkgHC pkgMid pkgC
        hDXC hDUC hCapMidC hCapC v r rCoin
    else
      pMuxHeldStage4_usel_k2_pebIpb hWpU h193U pkgSB hScr pkgHU pkgMid pkgC
        hDXU hDUU hCapMidU hCapU v r rCoin
    SubspaceStep (mkKetOpW rW st (fun _ ↦ 0))
      (mkKetOpW rW
        (fun δ ↦ xorPortB24NotScr r
          (potReflPortBSt24 (fun γ ↦ (sliceK γ).coinSwap) isCsel r rCoin st δ))
        (potReflPortBPh0_24 (fun γ ↦ (sliceK γ).phaseBit) isCsel r rCoin st)) p ∧
    p.count .T = (if isCsel then tPotC else tPotU) ∧
    p.count .TOFF = 0 := by
  cases isCsel <;> simp only [↓reduceIte, Bool.false_eq_true]
  · unfold pMuxHeldStage4_usel_k2_pebIpb
    rw [liftFinDyn_eq_c70, _root_.dite_eq_left hd]
    obtain ⟨sCore, tCore, fCore⟩ := step_pMuxHeldCore_usel_k2_pebIpb hWpU h193U pkgSB hScr
      pkgHU pkgMid pkgC hDXU hDUU hKMidLE hCapMidU hCapU v rW r rCoin hd st hFlags hWorkCln hPB0
    exact ⟨stage4_post_of_core hWpU false rW r rCoin _ st hFlags sCore, tCore.trans htU, fCore⟩
  · unfold pMuxHeldStage4_csel8_k2_pebIpb
    rw [liftFinDyn_eq_c70, _root_.dite_eq_left hd]
    obtain ⟨sCore, tCore, fCore⟩ := step_pMuxHeldCore_csel8_k2_pebIpb hWpC h193C pkgSB hScr
      pkgHC pkgMid pkgC hDXC hDUC hKMidLE hCapMidC hCapC v rW r rCoin hd st hFlags hWorkCln hPB0
    exact ⟨stage4_post_of_core hWpC true rW r rCoin _ st hFlags sCore, tCore.trans htC, fCore⟩

/--
Stage-4 `PortB` in-place potential oracle with `(WpU, kU)` on `Usel` and `(WpC, kC)` on
`Csel`.
-/
def wstateStage4InPlaceMux2Held_k2
    {Wp WpU kU WpC kC kScr tSB kScrFU tFU kScrUU tUU kScrFC tFC kScrUC tUC : ℕ}
    {kMid tMid tCoul tPotU tPotC : ℕ}
    (hWpU : WpU + kU = Wp) (hWpC : WpC + kC = Wp)
    (h193U : 193 ≤ WpU) (h193C : 193 ≤ WpC)
    (pkgSB : ShortBin7Pre6Pkg kScr tSB) (hScr : kScr ≤ 58)
    (hSBSafe : ShortBin7CtrlSafe pkgSB)
    (pkgHU : Dist18HeldSplitPkg kU kScrFU tFU kScrUU tUU)
    (pkgHC : Dist18HeldSplitPkg kC kScrFC tFC kScrUC tUC)
    (pkgMid : MidOWTap29Pkg 14 kMid tMid)
    (pkgC : CoulOWScrPkg13 tCoul (ySampleK2 word512DualLegLo6))
    (hDXU : 18 + kScrFU ≤ WpU - 25) (hDUU : 18 + kScrUU ≤ WpU - 25)
    (hDXC : 18 + kScrFC ≤ WpC - 25) (hDUC : 18 + kScrUC ≤ WpC - 25)
    (hKMidLE : kMid ≤ pkgC.kMid)
    (hCapMidU : 54 + kMid + 48 ≤ WpU) (hCapMidC : 54 + kMid + 48 ≤ WpC - 1)
    (hCapU : 54 + pkgC.kRest + 23 ≤ WpU) (hCapC : 54 + pkgC.kRest + 23 ≤ WpC - 1)
    (htU : 192 + (2 * tSB + 180) + 4 * kU + tFU + tCoul + tMid + tUU = tPotU)
    (htC : 200 + (2 * tSB + 180) + 4 * kC + tFC + tCoul + tMid + tUC = tPotC) :
    Stage4ReflCoin24PotOraclePortBInPlace 17 Wp tPotU tPotC potExpectK2DualLegK17 where
  sliceSpec γ := owK2ReflPotSliceSpec24 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6) γ
  pCsel v r rCoin :=
    pMuxHeldStage4_csel8_k2_pebIpb hWpC h193C pkgSB hScr pkgHC pkgMid pkgC
      hDXC hDUC hCapMidC hCapC v r rCoin
  pUsel v r rCoin :=
    pMuxHeldStage4_usel_k2_pebIpb hWpU h193U pkgSB hScr pkgHU pkgMid pkgC
      hDXU hDUU hCapMidU hCapU v r rCoin
  step_and_counts v rW r rCoin hd isCsel st hFlags hWorkCln hPB0 :=
    step_and_counts_pMuxHeldStage4_k2_pebIpb hWpU hWpC h193U h193C pkgSB hScr pkgHU pkgHC
      pkgMid pkgC hDXU hDUU hDXC hDUC hKMidLE hCapMidU hCapMidC hCapU hCapC
      htU htC v rW r rCoin hd isCsel st hFlags hWorkCln hPB0
  dynWires _S v r rCoin hSr hSc :=
    ⟨dynWires_pMuxHeldStage4_csel8_k2_pebIpb hWpC h193C pkgSB hScr hSBSafe pkgHC pkgMid pkgC
        hDXC hDUC hCapMidC hCapC v r rCoin hSr hSc,
     dynWires_pMuxHeldStage4_usel_k2_pebIpb hWpU h193U pkgSB hScr hSBSafe pkgHU pkgMid pkgC
        hDXU hDUU hCapMidU hCapU v r rCoin hSr hSc⟩
end QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp193K2
end Stage4PrefixHoldMuxBody
