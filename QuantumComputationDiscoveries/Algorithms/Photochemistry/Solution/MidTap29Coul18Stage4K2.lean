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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SubCoin63InPlaceWalk
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

open scoped BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (fN63 fN63_eq sNT63
    sNT63_eq nat_add_def nat_sub_def nat_mul_def nat_mod_def stVal63 stVal63_eq bNT11)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (sufST ST4 sST4 sST4_eq
    ST4P2 sST63 sST63_eq nat_pow_def checkNum63 checkNum63_sound beqNT beqNT_eq bNT6)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (bNT7 bNT13 bitAtF
    getNT32F getNT64F getNT1024F zeroST zeroST7F zeroST7F_eq stepZeroST stepZeroST_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (insST insST64F
    insST64F_eq stepInsST stepInsST_eq sufST64F sufST64F_eq stepSufST stepSufST_eq addST)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (addST7F addST7F_eq
    stepAddST stepAddST_eq subSTD subST64F subST64F_eq_subSTD stepSubST mkST4F ST4T3)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (andB63 bNT9 getNT256F
    sST4P2 selST4P2 sST4T3 ST4P2B sST4P2B ZLeafL sZLL ZOct10L buildJPackNT r01OfR6)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (sParts allCnt63
    allList63 tail16List sB63_eq xorBF notBF b2n_testBit_eq_div_mod b2n_ite_xor)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (wOfU5GamF_eq_spec
    buildNT63 buildNT63_zero buildNT63_succ bNT11_eq bNT13_eq get_bNT11 IsValidST)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (sumAllST sumSufST
    stVal_eq_sumAllST sumSufST_all sumSufST_none sufST_eq_sumSufST IsTreeOf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (zeroST_isTreeOf updAdd
    updSub insST_isTreeOf subSTD_isTreeOf addST_isTreeOf updAdd_updSub_bkt sST4P2_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (sST4T3_eq j18Sum3_eq
    j18CarryEval j18AtARB j18AtARB_lt_four j18AtARB_even_true_eq_odd_false jPack4Leaf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (jPack4Leaf_unpack
    sufST_le_add_stVal andB63_eq_true sST4P2B_eq sZLL_eq buildJPackNT_eq sParts_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (allCnt63_sound
    allList63_sound zKnotFast_at_lo6NT t11_step_arith is3DBoxDistSq_mod32_ne_28)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (smCoords_lt256
    smCoords_tail16 openDistSq_ge_192512_mem_tail16 elim_st4p2b)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (w11Sub63 zHi16Of24
    natOfZModBits_one_eq ReflPotSliceSpec24 ValidPotBFlags24 potB24GateActive)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (potReflPortBSt24
    potReflPortBPh0_24 potOraclePortB24CoinEval potOraclePortB24BitEval wPotB24LocQ)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (wPotB24IsScreen
    wPotB24IsPot wPotB24IsNN wPotB24Sp1B0 wPotB24Sp1B1 wPotB24Sp2B0 wPotB24Sp2B1)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (rPotB24NucA
    rPotB24ElecA rPotB24PortB rPotBCoin24 f41Of24 r41Of24 r41Of24_lt81 r41Of24_hi99)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (r41Of24_z16
    r41Of24_blocks validPotBFlags_r41Of24 potBGateActive_r41Of24 equivBitZMod2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (pAnd pCnot
    evalPrimTree95_and evalPrimTree95_cnot popBernJ popBernJ_lt_four idx7OfParts t11OfParts)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (parts_popBern_bounds
    dom22Bit compOutIdx cmpBits cmpBits_eq_decide_lt y36PopBernNoClamp rJ2OfPers)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
    (pX95 popBernJ_zero_of_t11_zero evenOctPartsFast evenOctPartsFast_eq fin8BinFast fin8BinFast_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (allRange allRange_eq_true
    cond_false_of_not natLtB natLtB_eq_true Is3DBoxDistSq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
    (is3DBoxDistSq_pairOpenDistSq potExpectAvgK)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (refl16_invol_and_div
    natOfZModBits_of_testBit OWLegsMidPkg r41_ne r41_blk_ne_wire rMuxZ16 z16AddVal)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (z16AddVal_zero
    finBitsVal_z16AddVal phAddVal phAddVal_zero writeReg_self_z16 v1Mux v2Mux muxD2Val)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (muxD2Val_eq_sector)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (mkKetOpW leg_if_pos
    leg_if_neg natOfZModBits)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd (finBitsVal finBitsVal_lt
    finBitsVal_succ)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast (dynWires_wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep
    stepCB)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (potBGateActive
    sectorDist3DSq3 owB2Of3Port testBit_two_pow_sub_one_sub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.OuterW11Alt (ChW11 chFn chFnFast NatTree
    SumTree stVal maxDistW11 evenOctPartsW11 qKnotW11 chFn_eq_chFnFast)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.OuterW11Alt (maxDistW11_eq_w11B
    evenOctPartsW11_eq_w11B evenOct_m_shift_w11B evenOct_mid_props_w11B)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZHi30 (fnEE30 fnNN30 shr_mono_nat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254 (finBitsVal_inj
    finBitsVal_eq_natOfZModBits cnot1 cnot1_counts cnot1_dynWires cnot1_step)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70 (evenOctIdxT10K)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.OddDivEval (natOfZModBits_split)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne potGen_d2_lt
    potGen_y36_lt potGen_k_lt potGen_mid_lt openCoordDistSq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (PotExpectFn
    wPotBIsScreen wPotBIsNN wPotBSp1B0 wPotBSp1B1 wPotBSp2B0 wPotBSp2B1 speciesOfBits2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (coordOfReg24 wPotBLocQ
    wPotBIsPot sysCoord nucParticle elecParticle)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18
    (PrimTree checkPrimTree evalPrimTree decodePrimTree checkPrimTree18S checkPrimTree18S_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec (fin8Bin nucSpecies
    speciesZ)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore (zmod2_maj_id
    sum_bits_testBit_ind nucParticle_eq_nucP elecParticle_eq_elecP openCoordDistSq_sys)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore
    (pairOpenDistSq_mod8_ne7_u fin8Bin_of_ge48_ultra openBoxDist3DSq_sys denomNNFermatCoinVal
    denomENFermatCoin)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg
    counts_wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (v1Fin8DualLeg
    v2Fin8DualLeg dEEDualLegPre5 dNNDualLegPre5 dENDualLegPre5 qEN0DualLegPre5)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (cEE1Sh14P5DualLeg
    cEE2Sh14P5DualLeg cNNSh14P5DualLeg cENSh14P5DualLeg cEE1Fin8DualLeg cEE2Fin8DualLeg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (cNNFin8DualLeg
    cENFin8DualLeg u30DualLeg popBernNonWrap30_dualLeg_lo6 wgtEETier1Walk wgtNNTier1Walk
    sum_wgtEETier1Walk)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (sum_wgtNNTier1Walk
    gEETier1Walk gNNTier1Walk midNNTier1Walk midENTier1Walk short_table_eq_nn_tier1Walk
    short_table_eq_en_tier1Walk)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (wOfU5Gam wOfU5GamF
    word512DualLegLo6T equivW11CLB zKnotLo6)
noncomputable section
set_option exponentiation.threshold 256
namespace QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29
set_option Elab.async false
open scoped Circuit.Notation
open Operator QProg DynamicCircuit Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu (subspaceStep_seq_mbu)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (rMidZHi midOW_lt0 midOW_lt1
    midOW_ltY midOW_ltZ midOW_ltZHi midOW_ltCln zmod2_val_cast)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (zmod2_testBit_eq_div_pow
    finBitsVal_split natOfZModBits_shr majCarryBit majCarryBit_val x1 cz2 cz2_counts)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (cz2_dynWires cz2_step w4_0
    w4_1 w4_2 w4_3 cpMaj4 cpMaj4_numAnd stepCB_cpMaj4_not stepCB_cpMaj4_anc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (wrapCpMaj4 carryCh_ltA
    carryCh_ltB fCarryOut rCarryOut stCarryIn carryChain_top_val)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOW58U10 (topPre_lt0 topPre_ltZ
    topPre_ltB pUngatedAddCarryKickTopPre pUngatedAddCarryKickTopPre_counts)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOW58U10
    (pUngatedAddCarryKickTopPre_dynWires zmod2_add_carry_id)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.MidOW60
    (gh16_finBitsVal_eq_zero gh16_finBitsVal_fin1 gh16_zmod2_ite_beq_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.MidOW60
    (gh16_majCarryBit_13_eq_14 gh16_seam_maj_val gh16_two_pass_hi16)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOW42ExactOpt
    (pCtrlAddCarryKickFast0Anc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Core (nm43_topPre_step)
open PrimitiveGate (T TOFF)
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP

/-- Carry-tap `Mid_OW` shift-add contribution (`+2048 mod 4096` flips `zLo[11]`). -/
def midWTap29 (isScr : Bool) (y36 zLo14 : ℕ) : ℕ :=
  (y36 >>> 5) +
    if isScr then 0
    else 2 ^ 14 * ((y36 >>> 17) + (((zLo14 + 2048) % 4096 + (y36 >>> 5) % 4096) / 4096))

/-- Total `30`-bit sum of `MidOWTap29` on `r : QRegister (71 + kMid) n`. -/
def midOWTotalSumTap29 {kMid n : ℕ} (r : QRegister (71 + kMid) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : ℕ :=
  let z30 := natOfZModBits 30 (fun i ↦ st δ (r ⟨41 + i.val, midOW_ltZ kMid i⟩))
  let y36 := natOfZModBits 36 (fun k ↦ st δ (r ⟨5 + k.val, midOW_ltY kMid k⟩))
  z30 + midWTap29 (st δ (r ⟨1, midOW_lt1 kMid⟩) == 1) y36 (z30 % 2 ^ 14)

/-- High `(30 - lZ)`-bit `Z` output bits of `MidOWTap29`. -/
def midOWZBitsTap29 {kMid n : ℕ} (lZ : ℕ) (hlZ : lZ ≤ 30) (r : QRegister (71 + kMid) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : Fin (30 - lZ) → ZMod 2 :=
  fun j ↦
    if st δ (r ⟨0, midOW_lt0 kMid⟩) == 1 then
      if (midOWTotalSumTap29 r st δ).testBit (lZ + j.val) then 0 else 1
    else
      st δ (r ⟨41 + lZ + j.val, midOW_ltZHi lZ kMid hlZ j⟩)

/-- Post-state of `MidOWTap29` on `r : QRegister (71 + kMid) n`. -/
def midOWPostStTap29 {kMid n : ℕ} (lZ : ℕ) (hlZ : lZ ≤ 30) (r : QRegister (71 + kMid) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
  writeReg (st δ) (rMidZHi lZ kMid hlZ r) (midOWZBitsTap29 lZ hlZ r st δ)

/-- Phase kick of `MidOWTap29` on `r : QRegister (71 + kMid) n`. -/
def midOWPhaseTap29 {kMid n : ℕ} (r : QRegister (71 + kMid) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) (δ : BitAssignment n) :
    ZMod 2 :=
  ph δ + st δ (r ⟨0, midOW_lt0 kMid⟩) *
    ((if (midOWTotalSumTap29 r st δ).testBit 30 then 1 else 0) +
     (if st δ (r ⟨1, midOW_lt1 kMid⟩) == 1 then 1 else 0))

/-- Reusable package interface for `MidOWTap29` (`kMid = 29, tMid = 244`). -/
structure MidOWTap29Pkg (lZ kMid tMid : ℕ) where
  hlZ : lZ ≤ 30
  pMid : {Var : Type} → {n : ℕ} → Var → QRegister (71 + kMid) n → DynamicCircuit Var n
  counts_wires : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (r : QRegister (71 + kMid) n),
    (∀ u : Fin (71 + kMid), S (r u)) →
    (pMid v r).count .T = tMid ∧ (pMid v r).count .TOFF = 0 ∧ DynWires S (pMid v r)
  step_mid : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (r : QRegister (71 + kMid) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ (j : Fin kMid) (δ : BitAssignment n),
      (∀ q : Fin W, δ (rWork q) = 0) → st δ (r ⟨71 + j.val, midOW_ltCln kMid j⟩) = 0) →
    (∀ (k : Fin 36) (δ : BitAssignment n),
      (∀ q : Fin W, δ (rWork q) = 0) → st δ (r ⟨0, midOW_lt0 kMid⟩) = 0 →
      st δ (r ⟨5 + k.val, midOW_ltY kMid k⟩) = 0) →
    SubspaceStep (mkKetOpW rWork st ph)
      (mkKetOpW rWork (midOWPostStTap29 lZ hlZ r st) (midOWPhaseTap29 r st ph))
      (pMid v r)

theorem midOWPostStTap29_of_not_zHi (lZ : ℕ) {K n : ℕ} (hlZ : lZ ≤ 30) (r : QRegister (71 + K) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (w : Wire n)
    (hw : ∀ j : Fin (30 - lZ), w ≠ r ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩) :
    midOWPostStTap29 lZ hlZ r st δ w = st δ w :=
    writeReg_apply_of_not_mem (st δ) (rMidZHi lZ K hlZ r) _ w fun ⟨j, hj⟩ ↦ hw j hj.symm
theorem midOWPostStTap29_zHi (lZ : ℕ) {K n : ℕ} (hlZ : lZ ≤ 30) (r : QRegister (71 + K) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (j : Fin (30 - lZ)) :
    midOWPostStTap29 lZ hlZ r st δ (r ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩) =
    midOWZBitsTap29 lZ hlZ r st δ j :=
    writeReg_apply_reg (st δ) (rMidZHi lZ K hlZ r) (midOWZBitsTap29 lZ hlZ r st δ) j
theorem eq_midOWPostStTap29_of_finBitsVal (lZ : ℕ) {K W n : ℕ} (hlZ : lZ ≤ 30)
    (rWork : QRegister W n) (r : QRegister (71 + K) n) (st stPre stOut : BitAssignment n →
    BitAssignment n) (δ : BitAssignment n) (hz : ∀ q : Fin W, δ (rWork q) = 0)
    (hOutNot : ∀ w : Wire n, (∀ j : Fin (30 - lZ), w ≠ r ⟨41 + lZ + j.val,
    midOW_ltZHi lZ K hlZ j⟩) → stOut δ w = st δ w)
    (hFlip : ∀ j : Fin (30 - lZ), stOut δ (r ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩) =
    stPre δ (r ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩) + st δ (r ⟨0, midOW_lt0 K⟩))
    (hIdle : st δ (r ⟨0, midOW_lt0 K⟩) = 0 → ∀ j : Fin (30 - lZ),
    stPre δ (r ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩) =
    st δ (r ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩)) (hAct : st δ (r ⟨0, midOW_lt0 K⟩) = 1 →
    finBitsVal (fun j : Fin (30 - lZ) ↦ stPre δ (r ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩)) =
    (midOWTotalSumTap29 r st δ / 2 ^ lZ) % 2 ^ (30 - lZ)) : stOut δ =
    midOWPostStTap29 lZ hlZ r st δ := by
  have _ := hz; funext w
  by_cases hm : ∃ j : Fin (30 - lZ), w = r ⟨41 + lZ + j.val, midOW_ltZHi lZ K hlZ j⟩
  · obtain ⟨j, hwEq⟩ := hm; rw [hwEq, midOWPostStTap29_zHi, hFlip j]; dsimp only [midOWZBitsTap29]
    rcases DynCircExt.bit_cases (st δ (r ⟨0, midOW_lt0 K⟩)) with hg0 | hg1
    · rw [hg0, add_zero, hIdle hg0 j];
      have h0b : ((0 : ZMod 2) == 1) = false :=
          rfl; rw [h0b]; simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [hg1]; have h1b : ((1 : ZMod 2) == 1) = true := rfl; rw [h1b]; simp only [↓reduceIte];
      have hValEq :=
          (hAct hg1).trans (MidOWCore.finBitsVal_of_testBit (30 - lZ)
          (midOWTotalSumTap29 r st δ /
          2 ^ lZ)).symm; have hFunEq := congrFun (finBitsVal_inj hValEq) j
      have htb : (midOWTotalSumTap29 r st δ / 2 ^ lZ).testBit j.val =
          (midOWTotalSumTap29 r st δ).testBit (lZ + j.val) := by
        rw [Nat.add_comm lZ j.val, Nat.testBit_add]
      rw [hFunEq, htb]; exact PhotochemistrySolution.MidOWCore.zmod2_not_ite_bool _
  · rw [hOutNot w (fun j hj ↦ hm ⟨j, hj⟩), midOWPostStTap29_of_not_zHi lZ hlZ r st δ w (fun j hj ↦
        hm ⟨j, hj⟩)]

theorem tap29_le14_30 : 14 ≤ 30 := by omega
theorem tap29_lt21 : 21 < 71 + 29 := by omega
theorem tap29_lt23 : 23 < 71 + 29 := by omega
theorem tap29_lt38 : 38 < 71 + 29 := by omega
theorem tap29_lt39 : 39 < 71 + 29 := by omega
theorem tap29_lt40 : 40 < 71 + 29 := by omega
theorem tap29_lt52 : 52 < 71 + 29 := by omega
theorem tap29_lt54 : 54 < 71 + 29 := by omega
theorem tap29_lt70 : 70 < 71 + 29 := by omega
theorem tap29_lt81 : 81 < 71 + 29 := by omega
theorem tap29_lt83 : 83 < 71 + 29 := by omega
theorem tap29_lt84 : 84 < 71 + 29 := by omega

theorem tap29_lt10 (j : Fin 14) : 10 + j.val < 71 + 29 := by have := j.isLt; omega
theorem tap29_lt22 (j : Fin 16) : 22 + j.val < 71 + 29 := by have := j.isLt; omega
theorem tap29_lt24 (j : Fin 16) : 24 + j.val < 71 + 29 := by have := j.isLt; omega
theorem tap29_lt24_15 (j : Fin 15) : 24 + j.val < 71 + 29 := by have := j.isLt; omega
theorem tap29_lt41 (j : Fin 14) : 41 + j.val < 71 + 29 := by have := j.isLt; omega
theorem tap29_lt55 (j : Fin 16) : 55 + j.val < 71 + 29 := by have := j.isLt; omega
theorem tap29_lt55_15 (j : Fin 15) : 55 + j.val < 71 + 29 := by have := j.isLt; omega
theorem tap29_lt71_13 (i : Fin 13) : 71 + i.val < 71 + 29 := by have := i.isLt; omega
theorem tap29_lt84_pool (j : Fin 16) : 84 + j.val < 71 + 29 := by have := j.isLt; omega

theorem tap29_ne_0_40 {n : ℕ} (r : QRegister (71 + 29) n) : r ⟨0, midOW_lt0 29⟩ ≠ r ⟨40, tap29_lt40⟩
    :=
  fun e ↦ by have hv : 0 = 40 := congrArg Fin.val (r.wires.injective e); omega

theorem tap29_ne_70_39 {n : ℕ} (r : QRegister (71 + 29) n) : r ⟨70, tap29_lt70⟩ ≠ r ⟨39, tap29_lt39⟩
    :=
  fun e ↦ by have hv : 70 = 39 := congrArg Fin.val (r.wires.injective e); omega

theorem tap29_ne_39_70 {n : ℕ} (r : QRegister (71 + 29) n) : r ⟨39, tap29_lt39⟩ ≠ r ⟨70, tap29_lt70⟩
    :=
  fun e ↦ by have hv : 39 = 70 := congrArg Fin.val (r.wires.injective e); omega

theorem tap29_ne_0_1 {n : ℕ} (r : QRegister (71 + 29) n) : r ⟨0, midOW_lt0 29⟩ ≠ r ⟨1, midOW_lt1 29⟩
    :=
  fun e ↦ by have hv : 0 = 1 := congrArg Fin.val (r.wires.injective e); omega

theorem tap29_ne_1_38 {n : ℕ} (r : QRegister (71 + 29) n) : r ⟨1, midOW_lt1 29⟩ ≠ r ⟨38, tap29_lt38⟩
    :=
  fun e ↦ by have hv : 1 = 38 := congrArg Fin.val (r.wires.injective e); omega

/-- `39`-wire CarryA subregister `(y[5..17]=10..22, zLo[0..12]=41..53, cA[0..12]=71..83)`. -/
def tap29_idxCarryA (u : Fin (3 * (12 + 1))) : ℕ :=
    if u.val < 13 then 10 + u.val else if u.val < 26 then 28 + u.val else 45 + u.val
theorem tap29_idxCarryA_lt (u : Fin (3 * (12 + 1))) : tap29_idxCarryA u < 71 + 29 := by
  have _ := u.isLt; dsimp only [tap29_idxCarryA]; split_ifs <;> omega
def tap29_fCarryA : Fin (3 * (12 + 1)) → Fin (71 + 29) := fun u ↦
    ⟨tap29_idxCarryA u, tap29_idxCarryA_lt u⟩
theorem tap29_fCarryA_inj : Function.Injective tap29_fCarryA := fun a b e ↦ Fin.ext <| by
  obtain ⟨_, _, hv⟩ := And.intro a.isLt (And.intro b.isLt (congrArg Fin.val e))
  dsimp only [tap29_fCarryA, tap29_idxCarryA] at hv
  split_ifs at hv <;> omega

def tap29_rCarryA {n : ℕ} (r : QRegister (71 + 29) n) : QRegister (3 * (12 + 1)) n :=
  r.compose ⟨tap29_fCarryA, tap29_fCarryA_inj⟩

/-- `4`-wire MajA13 subregister `(y[18]=23, zLo[13]=54, cA[12]=83, cA[13]=84)`. -/
def tap29_idxMajA13 (u : Fin 4) : ℕ :=
    if u.val = 0 then 23 else if u.val = 1 then 54 else if u.val = 2 then 83 else 84
theorem tap29_idxMajA13_lt (u : Fin 4) : tap29_idxMajA13 u < 71 + 29 := by
  dsimp only [tap29_idxMajA13]; split_ifs <;> omega
def tap29_fMajA13 : Fin 4 → Fin (71 + 29) := fun u ↦ ⟨tap29_idxMajA13 u, tap29_idxMajA13_lt u⟩
theorem tap29_fMajA13_inj : Function.Injective tap29_fMajA13 := fun a b e ↦ Fin.ext <| by
  obtain ⟨_, _, hv⟩ := And.intro a.isLt (And.intro b.isLt (congrArg Fin.val e))
  dsimp only [tap29_fMajA13, tap29_idxMajA13] at hv
  split_ifs at hv <;> omega

def tap29_rMajA13 {n : ℕ} (r : QRegister (71 + 29) n) : QRegister 4 n :=
  r.compose ⟨tap29_fMajA13, tap29_fMajA13_inj⟩

/-- `47`-wire UngA15 subregister `(84, zHi[0..15]=55..70, y[19..33]=24..38, cln=85..99)`. -/
def tap29_idxUngA15 (u : Fin (3 * 15 + 2)) : ℕ :=
    if u.val = 0 then 84 else if u.val < 17 then 54 + u.val else if u.val < 32 then 7 +
    u.val else 53 + u.val
theorem tap29_idxUngA15_lt (u : Fin (3 * 15 + 2)) : tap29_idxUngA15 u < 71 + 29 := by
  have _ := u.isLt; dsimp only [tap29_idxUngA15]; split_ifs <;> omega
def tap29_fUngA15 : Fin (3 * 15 + 2) → Fin (71 + 29) := fun u ↦
    ⟨tap29_idxUngA15 u, tap29_idxUngA15_lt u⟩
theorem tap29_fUngA15_inj : Function.Injective tap29_fUngA15 := fun a b e ↦ Fin.ext <| by
  obtain ⟨_, _, hv⟩ := And.intro a.isLt (And.intro b.isLt (congrArg Fin.val e))
  dsimp only [tap29_fUngA15, tap29_idxUngA15] at hv
  split_ifs at hv <;> omega

def tap29_rUngA15 {n : ℕ} (r : QRegister (71 + 29) n) : QRegister (3 * 15 + 2) n :=
    r.compose ⟨tap29_fUngA15, tap29_fUngA15_inj⟩
def tap29_idxCtrlB (u : Fin (4 + 3 * 15)) : ℕ :=
    if u.val = 0 then 1 else if u.val = 1 then 84 else if u.val < 18 then 53 + u.val else if u.val <
    34 then 4 + u.val else 51 + u.val
theorem tap29_idxCtrlB_lt (u : Fin (4 + 3 * 15)) : tap29_idxCtrlB u < 71 + 29 := by
  have _ := u.isLt; dsimp only [tap29_idxCtrlB]; split_ifs <;> omega
def tap29_fCtrlB : Fin (4 + 3 * 15) → Fin (71 + 29) := fun u ↦
    ⟨tap29_idxCtrlB u, tap29_idxCtrlB_lt u⟩
theorem tap29_fCtrlB_inj : Function.Injective tap29_fCtrlB := fun a b e ↦ Fin.ext <| by
  obtain ⟨_, _, hv⟩ := And.intro a.isLt (And.intro b.isLt (congrArg Fin.val e))
  dsimp only [tap29_fCtrlB, tap29_idxCtrlB] at hv
  split_ifs at hv <;> omega

def tap29_rCtrlB {n : ℕ} (r : QRegister (71 + 29) n) : QRegister (4 + 3 * 15) n :=
  r.compose ⟨tap29_fCtrlB, tap29_fCtrlB_inj⟩

/-- `17`-wire Refl subregister `(0, zHi[0..15]=55..70)`. -/
def tap29_idxRefl (u : Fin (2 + 15)) : ℕ := if u.val = 0 then 0 else 54 + u.val
theorem tap29_idxRefl_lt (u : Fin (2 + 15)) : tap29_idxRefl u < 71 + 29 := by
  have _ := u.isLt; dsimp only [tap29_idxRefl]; split_ifs <;> omega
def tap29_fRefl : Fin (2 + 15) → Fin (71 + 29) := fun u ↦ ⟨tap29_idxRefl u, tap29_idxRefl_lt u⟩
theorem tap29_fRefl_inj : Function.Injective tap29_fRefl := fun a b e ↦ Fin.ext <| by
  obtain ⟨_, _, hv⟩ := And.intro a.isLt (And.intro b.isLt (congrArg Fin.val e))
  dsimp only [tap29_fRefl, tap29_idxRefl] at hv
  split_ifs at hv <;> omega

def tap29_rRefl {n : ℕ} (r : QRegister (71 + 29) n) : QRegister (2 + 15) n :=
  r.compose ⟨tap29_fRefl, tap29_fRefl_inj⟩

/-- Zero-mux Pass-A high-16 adder (`64 T`, `0 .TOFF`). -/
def tap29_pPassAHi {Var : Type} {n : ℕ} (v : Var) (r : QRegister (71 + 29) n) :
    DynamicCircuit Var n :=
    .seq (cz2 (r ⟨0, midOW_lt0 29⟩) (r ⟨40, tap29_lt40⟩) (tap29_ne_0_40 r))
    (.seq (cz2 (r ⟨70, tap29_lt70⟩) (r ⟨39, tap29_lt39⟩) (tap29_ne_70_39 r))
    (.seq (cnot1 v (r ⟨39, tap29_lt39⟩) (r ⟨70, tap29_lt70⟩) (tap29_ne_39_70 r))
    (wrapDynOnReg v (tap29_rMajA13 r) cpMaj4 (pUngatedAddCarryKickTopPre 15 v (tap29_rUngA15 r)))))
def tap29_pPassBInner {Var : Type} {n : ℕ} (v : Var) (r : QRegister (71 + 29) n) :
    DynamicCircuit Var n :=
    .seq (cz2 (r ⟨0, midOW_lt0 29⟩) (r ⟨1, midOW_lt1 29⟩) (tap29_ne_0_1 r))
    (.seq (x1 (r ⟨1, midOW_lt1 29⟩)) (.seq (cz2 (r ⟨1, midOW_lt1 29⟩) (r ⟨38, tap29_lt38⟩)
    (tap29_ne_1_38 r)) (.seq (pCtrlAddCarryKickFast0Anc 15 v (tap29_rCtrlB r))
    (x1 (r ⟨1, midOW_lt1 29⟩)))))
theorem tap29_pPassAHi_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : QRegister (71 + 29) n) (hr : ∀ u : Fin (71 + 29), S (r u)) :
    (tap29_pPassAHi v r).count .T = 64 ∧ (tap29_pPassAHi v r).count .TOFF = 0 ∧
    DynWires S (tap29_pPassAHi v r) := by
  obtain ⟨tCz0, fCz0⟩ := cz2_counts (Var := Var) _ _ (tap29_ne_0_40 r)
  obtain ⟨tCzT, fCzT⟩ := cz2_counts (Var := Var) _ _ (tap29_ne_70_39 r)
  obtain ⟨tCnT, fCnT⟩ := cnot1_counts (Var := Var) v _ _ (tap29_ne_39_70 r)
  obtain ⟨tUng, fUng⟩ := pUngatedAddCarryKickTopPre_counts 15 v (tap29_rUngA15 r)
  obtain ⟨tMaj, fMaj⟩ := counts_wrapDynOnReg v (tap29_rMajA13 r) cpMaj4
    (pUngatedAddCarryKickTopPre 15 v (tap29_rUngA15 r))
  refine ⟨by dsimp only [tap29_pPassAHi, DynamicCircuit.count]
             rw [tCz0, tCzT, tCnT, tMaj, cpMaj4_numAnd, tUng],
    by dsimp only [tap29_pPassAHi, DynamicCircuit.count]
       rw [fCz0, fCzT, fCnT, fMaj, fUng],
    cz2_dynWires S _ _ (tap29_ne_0_40 r) (hr _) (hr _),
    cz2_dynWires S _ _ (tap29_ne_70_39 r) (hr _) (hr _),
    cnot1_dynWires S v _ _ (tap29_ne_39_70 r) (hr _) (hr _),
    dynWires_wrapDynOnReg v (tap29_rMajA13 r) (fun u ↦ hr (tap29_fMajA13 u)) cpMaj4
      (pUngatedAddCarryKickTopPre_dynWires 15 S v _ (fun u ↦ hr (tap29_fUngA15 u)))⟩
def tap29_zLoVal {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ℕ := finBitsVal (fun j : Fin 14 ↦ st δ (r ⟨41 + j.val, tap29_lt41 j⟩))
def tap29_zHiVal {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ℕ := finBitsVal (fun j : Fin 16 ↦ st δ (r ⟨55 + j.val, tap29_lt55 j⟩))
def tap29_w1LoVal {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ℕ := finBitsVal (fun j : Fin 14 ↦ st δ (r ⟨10 + j.val, tap29_lt10 j⟩))
def tap29_w1HiVal {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ℕ := finBitsVal (fun j : Fin 16 ↦ st δ (r ⟨24 + j.val, tap29_lt24 j⟩))
def tap29_bLo15Val {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ℕ :=
    finBitsVal (fun j : Fin 15 ↦ st δ (r ⟨24 + j.val, tap29_lt24_15 j⟩))
def tap29_cTapVal {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ℕ :=
    (((tap29_zLoVal r st δ + 2048) % 4096 + tap29_w1LoVal r st δ % 4096) / 4096)
def tap29_w2HiVal {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ℕ :=
    if st δ (r ⟨1, midOW_lt1 29⟩) = 0 then finBitsVal (fun j : Fin 16 ↦
    st δ (r ⟨22 + j.val, tap29_lt22 j⟩)) + tap29_cTapVal r st δ else 0
def tap29_sum30 {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ℕ :=
    (tap29_zLoVal r st δ + 2 ^ 14 * tap29_zHiVal r st δ) + (tap29_w1LoVal r st δ + 2 ^ 14 *
    tap29_w1HiVal r st δ) + (0 + 2 ^ 14 * tap29_w2HiVal r st δ)
theorem tap29_w1HiVal_split {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : tap29_w1HiVal r st δ =
    tap29_bLo15Val r st δ + 2 ^ 15 * (st δ (r ⟨39, tap29_lt39⟩)).val := by
  dsimp only [tap29_w1HiVal, tap29_bLo15Val]; rw [finBitsVal_split 15 1, gh16_finBitsVal_fin1]
  exact congrArg₂ (· + ·) (congrArg finBitsVal (funext fun j ↦
      congrArg (st δ) (congrArg r.wires (Fin.ext (by dsimp)))))
    (congrArg (2 ^ 15 * ZMod.val ·) (congrArg (st δ) (congrArg r.wires (Fin.ext rfl))))

theorem tap29_totalSum_decomp {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : ∃ Q : ℕ,
    midOWTotalSumTap29 r st δ = tap29_sum30 r st δ + 2 ^ 30 * ((st δ (r ⟨40, tap29_lt40⟩)).val +
    ((st δ (r ⟨1, midOW_lt1 29⟩) + 1) * st δ (r ⟨38, tap29_lt38⟩)).val) + 2 ^ 31 * Q := by
  let fY : Fin 36 → ZMod 2 := fun k ↦ st δ (r ⟨5 + k.val, midOW_ltY 29 k⟩)
  have hrFn {m : ℕ} {f g : Fin m → Fin (71 + 29)} (h : ∀ j, (f j).val = (g j).val) :
      finBitsVal (fun j ↦ st δ (r (f j))) = finBitsVal (fun j ↦ st δ (r (g j))) :=
    congrArg finBitsVal (funext fun j ↦ congrArg (st δ) (congrArg r.wires (Fin.ext (h j))))
  have hZ : natOfZModBits 30 (fun i ↦ st δ (r ⟨41 + i.val, midOW_ltZ 29 i⟩)) =
      tap29_zLoVal r st δ + 2 ^ 14 * tap29_zHiVal r st δ := by
    rw [← finBitsVal_eq_natOfZModBits 30, finBitsVal_split 14 16]
    exact congrArg₂ (· + ·) (hrFn fun _ ↦ rfl)
      (congrArg (2 ^ 14 * ·) (hrFn fun j ↦ (Nat.add_assoc 41 14 j.val).symm))
  have hZMod14 : (tap29_zLoVal r st δ + 2 ^ 14 * tap29_zHiVal r st δ) % 2 ^ 14 =
      tap29_zLoVal r st δ :=
    (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt (finBitsVal_lt _))
  have hY5 : (natOfZModBits 36 fY) >>> 5 =
      (tap29_w1LoVal r st δ + 2 ^ 14 * tap29_w1HiVal r st δ) +
        2 ^ 30 * (st δ (r ⟨40, tap29_lt40⟩)).val := by
    rw [natOfZModBits_shr 5 31 fY, finBitsVal_split 14 17, finBitsVal_split 16 1,
        gh16_finBitsVal_fin1]
    rw [show finBitsVal (fun j : Fin 14 ↦ fY ⟨5 + j.val, _⟩) = tap29_w1LoVal r st δ from
          hrFn fun j ↦ (Nat.add_assoc 5 5 j.val).symm,
        show finBitsVal (fun j : Fin 16 ↦ fY ⟨5 + (14 + j.val), _⟩) = tap29_w1HiVal r st δ from
          hrFn fun j ↦
            (Nat.add_assoc 5 5 (14 + j.val)).symm.trans (Nat.add_assoc 10 14 j.val).symm,
        show fY ⟨5 + (14 + (16 + (0 : Fin 1).val)), _⟩ = st δ (r ⟨40, tap29_lt40⟩) from
          congrArg (st δ) (congrArg r.wires (Fin.ext rfl))]
    ring
  have hY5Mod12 : ((natOfZModBits 36 fY) >>> 5) % 4096 = tap29_w1LoVal r st δ % 4096 := by
    rw [hY5]; omega
  rcases (by
      rw [natOfZModBits_shr 17 19 fY, finBitsVal_split 16 3, finBitsVal_succ (n := 2)]
      dsimp only
      rw [show finBitsVal (fun j : Fin 16 ↦ fY ⟨17 + j.val, _⟩) =
            finBitsVal (fun j : Fin 16 ↦ st δ (r ⟨22 + j.val, tap29_lt22 j⟩)) from
            hrFn fun j ↦ (Nat.add_assoc 5 17 j.val).symm,
          show fY ⟨17 + (16 + (0 : Fin 3).val), _⟩ = st δ (r ⟨38, tap29_lt38⟩) from
            congrArg (st δ) (congrArg r.wires (Fin.ext rfl))]
      exact ⟨finBitsVal (fun i : Fin 2 ↦ fY ⟨17 + (16 + i.succ.val), _⟩), by ring⟩ :
      ∃ Q0 : ℕ, (natOfZModBits 36 fY) >>> 17 =
        finBitsVal (fun j : Fin 16 ↦ st δ (r ⟨22 + j.val, tap29_lt22 j⟩)) +
          2 ^ 16 * (st δ (r ⟨38, tap29_lt38⟩)).val + 2 ^ 17 * Q0) with ⟨Q0, hQ0⟩
  dsimp only [fY] at hY5 hY5Mod12 hQ0
  rcases DynCircExt.bit_cases (st δ (r ⟨1, midOW_lt1 29⟩)) with hs0 | hs1
  · refine ⟨Q0, ?_⟩
    dsimp only [midOWTotalSumTap29, midWTap29, tap29_sum30, tap29_w2HiVal, tap29_cTapVal]
    rw [hZ, hZMod14, hY5Mod12, hY5, hQ0]
    simp only [hs0, show ((0 : ZMod 2) == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      zero_add, one_mul]; ring
  · refine ⟨0, ?_⟩
    simp only [midOWTotalSumTap29, midWTap29, tap29_sum30, tap29_w2HiVal, hZ, hY5, hs1,
      show ((1 : ZMod 2) == 1) = true from rfl, ↓reduceIte, one_ne_zero,
      CharTwo.add_self_eq_zero, zero_mul, ZMod.val_zero, mul_zero, add_zero]
    ring

theorem tap29_totalSum_div14_mod16 {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : (midOWTotalSumTap29 r st δ /
    2 ^ 14) % 2 ^ 16 = (tap29_sum30 r st δ / 2 ^ 14) % 2 ^ 16 := by
  obtain ⟨Q, hQ⟩ := tap29_totalSum_decomp r st δ
  rw [hQ]
  omega

theorem tap29_phase_eq_sum30 {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) (δ : BitAssignment n) :
    midOWPhaseTap29 r st ph δ = ph δ + st δ (r ⟨0, midOW_lt0 29⟩) *
    (((tap29_sum30 r st δ / 2 ^ 30 : ℕ) : ZMod 2) + st δ (r ⟨40, tap29_lt40⟩) +
    (st δ (r ⟨1, midOW_lt1 29⟩) + 1) * st δ (r ⟨38, tap29_lt38⟩) + st δ (r ⟨1, midOW_lt1 29⟩)) := by
  obtain ⟨Q, hQ⟩ := tap29_totalSum_decomp r st δ
  have h30 (a b c : ℕ) : (a + 2 ^ 30 * b + 2 ^ 31 * c) / 2 ^ 30 = a / 2 ^ 30 + b + 2 * c := by
    omega
  dsimp only [midOWPhaseTap29]
  rw [zmod2_testBit_eq_div_pow, gh16_zmod2_ite_beq_one, hQ, h30]
  push_cast
  simp only [CharTwo.two_eq_zero, zero_mul, add_zero, zmod2_val_cast]
  ring
def tap29_cA13Bit {n : ℕ} (r : QRegister (71 + 29) n) (st0 : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ZMod 2 :=
    (st0 δ (r ⟨23, tap29_lt23⟩) + st0 δ (r ⟨83, tap29_lt83⟩)) * (st0 δ (r ⟨54, tap29_lt54⟩) +
    st0 δ (r ⟨83, tap29_lt83⟩)) + st0 δ (r ⟨83, tap29_lt83⟩)
def tap29_cTapBit {n : ℕ} (r : QRegister (71 + 29) n) (st0 : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) : ZMod 2 :=
    ((st0 δ (r ⟨52, tap29_lt52⟩) + 1) + st0 δ (r ⟨81, tap29_lt81⟩)) * (st0 δ (r ⟨21, tap29_lt21⟩) +
    st0 δ (r ⟨81, tap29_lt81⟩)) + st0 δ (r ⟨81, tap29_lt81⟩)
theorem tap29_pPassAHi_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (r : QRegister (71 + 29) n)
    (st0 : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hCln84 : ∀ (j : Fin 16) (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
    st0 δ (r ⟨84 + j.val, tap29_lt84_pool j⟩) = 0) : ∃ stA : BitAssignment n → BitAssignment n,
    SubspaceStep (mkKetOpW rWork st0 ph)
    (mkKetOpW rWork stA (fun δ ↦ ph δ + st0 δ (r ⟨0, midOW_lt0 29⟩) * st0 δ (r ⟨40, tap29_lt40⟩) +
    (((finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) + tap29_w1HiVal r st0 δ +
    (tap29_cA13Bit r st0 δ).val) / 2 ^ 16 : ℕ) : ZMod 2))) (tap29_pPassAHi v r) ∧
    (∀ (δ : BitAssignment n) (w : Wire n), (∀ j : Fin 16, w ≠ r ⟨55 + j.val, tap29_lt55 j⟩) →
    stA δ w = st0 δ w) ∧ (∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
    finBitsVal (fun j : Fin 16 ↦ stA δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
    (finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) + tap29_w1HiVal r st0 δ +
    (tap29_cA13Bit r st0 δ).val) % 2 ^ 16) := by
  let rMaj := tap29_rMajA13 r; let rUng := tap29_rUngA15 r; let w70 := r ⟨70, tap29_lt70⟩;
  let w39 := r ⟨39, tap29_lt39⟩
  let ph1 : BitAssignment n → ZMod 2 := fun δ ↦
      ph δ + st0 δ (r ⟨0, midOW_lt0 29⟩) * st0 δ (r ⟨40, tap29_lt40⟩)
  let ph2 : BitAssignment n → ZMod 2 := fun δ ↦ ph1 δ + st0 δ w70 * st0 δ w39
  let phOut : BitAssignment n → ZMod 2 := fun δ ↦
      ph1 δ + (((finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
      tap29_w1HiVal r st0 δ + (tap29_cA13Bit r st0 δ).val) / 2 ^ 16 : ℕ) : ZMod 2)
  have hCz0 := cz2_step (Var := Var) rWork _ _ (tap29_ne_0_40 r) st0 ph
  have hCzT := cz2_step (Var := Var) rWork w70 w39 (tap29_ne_70_39 r) st0 ph1
  let stPre : BitAssignment n → BitAssignment n := fun δ ↦
      Function.update (st0 δ) w70 (st0 δ w70 + st0 δ w39)
  have hCnT := cnot1_step v rWork w39 w70 (tap29_ne_39_70 r) st0 ph2
  have hPreNot70 (δ : BitAssignment n) {idx : ℕ} (hi : idx < 71 + 29) (hne : idx ≠ 70) :
      stPre δ (r ⟨idx, hi⟩) = st0 δ (r ⟨idx, hi⟩) :=
    Function.update_of_ne (fun e ↦ hne (congrArg Fin.val (r.wires.injective e))) _ _
  let st2 : BitAssignment n → BitAssignment n := fun δ ↦ stepCB rMaj cpMaj4.fwdBits (stPre δ)
  have hMaj3Eq : rMaj w4_3 = r ⟨84, tap29_lt84⟩ := rfl
  have hUngEq (u : Fin (3 * 15 + 2)) {m : ℕ} (hm : m < 71 + 29) (h : tap29_idxUngA15 u = m) :
      rUng u = r ⟨m, hm⟩ := congrArg r.wires (Fin.ext h)
  have hSt2Pre (δ : BitAssignment n) {m : ℕ} (hm : m < 71 + 29) (h84 : m ≠ 84) :
      st2 δ (r ⟨m, hm⟩) = stPre δ (r ⟨m, hm⟩) :=
    stepCB_cpMaj4_not rMaj (stPre δ) fun e ↦ h84 (congrArg Fin.val (r.wires.injective e))
  have hUngCln (u : Fin (3 * 15 + 2)) (δ : BitAssignment n) (hu : 2 * 15 + 2 ≤ u.val)
      (hz : ∀ q : Fin W, δ (rWork q) = 0) : st2 δ (rUng u) = 0 := by
    have := u.isLt
    rw [hUngEq u (by omega : 53 + u.val < 71 + 29)
        (by dsimp only [tap29_idxUngA15]; split_ifs <;> omega),
      hSt2Pre δ _ (by omega), hPreNot70 δ _ (by omega)]
    refine Eq.trans ?_ (hCln84 ⟨u.val - 31, by omega⟩ δ hz)
    exact congrArg (st0 δ) (congrArg r.wires (Fin.ext (by dsimp; omega)))
  obtain ⟨st3, hUngStep, h3Not, h3Val⟩ := nm43_topPre_step 15 v rWork rUng st2 ph2 hUngCln
  have hUngZ (i : Fin 16) : rUng ⟨1 + i.val, topPre_ltZ 15 i⟩ = r ⟨55 + i.val, tap29_lt55 i⟩ :=
    hUngEq _ _ (by have := i.isLt; dsimp only [tap29_idxUngA15]; split_ifs <;> omega)
  have hZVal2 (δ : BitAssignment n) :
      finBitsVal (fun i : Fin 16 ↦ st2 δ (rUng ⟨1 + i.val, topPre_ltZ 15 i⟩)) =
      finBitsVal (fun j : Fin 16 ↦ stPre δ (r ⟨55 + j.val, tap29_lt55 j⟩)) :=
    congrArg finBitsVal (funext fun i ↦
      (congrArg (st2 δ) (hUngZ i)).trans (hSt2Pre δ _ (by have := i.isLt; omega)))
  have hBVal2 (δ : BitAssignment n) :
      finBitsVal (fun i : Fin 15 ↦ st2 δ (rUng ⟨15 + 2 + i.val, topPre_ltB 15 i⟩)) =
      tap29_bLo15Val r st0 δ := congrArg finBitsVal (funext fun j ↦ by
    have := j.isLt
    rw [hUngEq _ (tap29_lt24_15 j) (by dsimp only [tap29_idxUngA15]; split_ifs <;> omega),
      hSt2Pre δ _ (by omega)]
    exact hPreNot70 δ _ (by omega))
  have hCin2 (δ : BitAssignment n) (hz : ∀ q : Fin W, δ (rWork q) = 0) :
      st2 δ (rUng ⟨0, topPre_lt0 15⟩) = tap29_cA13Bit r st0 δ := by
    change stepCB rMaj cpMaj4.fwdBits (stPre δ) (rMaj w4_3) = _
    rw [stepCB_cpMaj4_anc, hMaj3Eq, hPreNot70 δ _ (by omega),
        show r ⟨84, tap29_lt84⟩ = r ⟨84 + (0 : Fin 16).val, tap29_lt84_pool 0⟩ from rfl,
        hCln84 0 δ hz, zero_add, show rMaj w4_0 = r ⟨23, tap29_lt23⟩ from rfl,
        show rMaj w4_1 = r ⟨54, tap29_lt54⟩ from rfl, show rMaj w4_2 = r ⟨83, tap29_lt83⟩ from rfl,
        hPreNot70 δ tap29_lt23 (by omega), hPreNot70 δ tap29_lt54 (by omega),
        hPreNot70 δ tap29_lt83 (by omega)]
    rfl
  have hSplit55 (stX : BitAssignment n) :
      finBitsVal (fun j : Fin 16 ↦ stX (r ⟨55 + j.val, tap29_lt55 j⟩)) =
      finBitsVal (fun j : Fin 15 ↦ stX (r ⟨55 + j.val, tap29_lt55_15 j⟩)) +
        2 ^ 15 * (stX w70).val := by
    rw [finBitsVal_split 15 1, gh16_finBitsVal_fin1]
    exact congrArg₂ (· + ·)
      (congrArg finBitsVal (funext fun _ ↦ congrArg stX (congrArg r.wires (Fin.ext (by dsimp)))))
      (congrArg (2 ^ 15 * ZMod.val ·) (congrArg stX (congrArg r.wires (Fin.ext rfl))))
  have hSumFullEq : ∀ δ, finBitsVal (fun j : Fin 16 ↦ st0 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
        tap29_w1HiVal r st0 δ + (tap29_cA13Bit r st0 δ).val =
      (finBitsVal (fun j : Fin 16 ↦ stPre δ (r ⟨55 + j.val, tap29_lt55 j⟩)) +
        tap29_bLo15Val r st0 δ + (tap29_cA13Bit r st0 δ).val) +
      2 ^ 16 * (st0 δ w70 * st0 δ w39).val := fun δ ↦ by
    have hZ0Split := hSplit55 (st0 δ)
    have hZPreSplit : finBitsVal (fun j : Fin 16 ↦ stPre δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
        finBitsVal (fun j : Fin 15 ↦ st0 δ (r ⟨55 + j.val, tap29_lt55_15 j⟩)) +
          2 ^ 15 * (st0 δ w70 + st0 δ w39).val := by
      rw [hSplit55 (stPre δ), congrArg finBitsVal
          (funext fun j : Fin 15 ↦ hPreNot70 δ (tap29_lt55_15 j) (by have := j.isLt; omega))]
      dsimp only [stPre]
      rw [Function.update_self]
    rw [hZ0Split, hZPreSplit, tap29_w1HiVal_split r st0 δ];
    have hc := zmod2_add_carry_id (st0 δ w70) (st0 δ w39); dsimp only [w70, w39] at hc ⊢; omega
  let st4 : BitAssignment n → BitAssignment n := fun δ w ↦
      if w = rMaj w4_3 then stPre δ w else st3 δ w
  have hMajWrap : SubspaceStep (mkKetOpW rWork stPre ph2) (mkKetOpW rWork st4 phOut)
      (wrapDynOnReg v rMaj cpMaj4 (pUngatedAddCarryKickTopPre 15 v rUng)) := by
    refine wrapCpMaj4 v rWork rMaj (pUngatedAddCarryKickTopPre 15 v rUng) stPre st3 ph2 _ phOut
      (fun δ hz ↦ (hPreNot70 δ tap29_lt84 (by omega)).trans (hCln84 ⟨0, by omega⟩ δ hz))
      (fun u δ ↦ h3Not δ (rMaj u) fun i e ↦ by
        have hv := congrArg Fin.val (r.wires.injective (e.trans (hUngZ i)))
        have := i.isLt
        have := u.isLt
        dsimp [rMaj, tap29_rMajA13, tap29_fMajA13, tap29_idxMajA13] at hv
        split_ifs at hv <;> omega)
      (fun δ hz ↦ by
        dsimp only [phOut, ph2]; rw [hZVal2 δ, hBVal2 δ, hCin2 δ hz, hSumFullEq δ,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos 16), Nat.cast_add, zmod2_val_cast]; ring)
      hUngStep
  refine ⟨st4,
      subspaceStep_seq_mbu hCz0 (subspaceStep_seq_mbu hCzT (subspaceStep_seq_mbu hCnT hMajWrap)),
      fun δ w hw ↦ ?_, fun δ hz ↦ ?_⟩
  · have hw70 : w ≠ w70 := hw ⟨15, by omega⟩
    dsimp only [st4]
    by_cases hw3 : w = rMaj w4_3
    · rw [leg_if_pos hw3]; dsimp only [stPre]; exact Function.update_of_ne hw70 _ _
    · rw [leg_if_neg hw3, h3Not δ w (fun i e ↦ hw i (e.trans (hUngZ i)))]
      dsimp only [st2, stPre]; rw [stepCB_cpMaj4_not rMaj _ hw3];
      exact Function.update_of_ne hw70 _ _
  · have hEqZ : finBitsVal (fun j : Fin 16 ↦ st4 δ (r ⟨55 + j.val, tap29_lt55 j⟩)) =
        finBitsVal (fun i : Fin 16 ↦ st3 δ (rUng ⟨1 + i.val, topPre_ltZ 15 i⟩)) :=
      congrArg finBitsVal (funext fun j ↦ (_root_.ite_eq_right fun e ↦ by
        have hv : 55 + j.val = 84 := congrArg Fin.val (r.wires.injective e)
        have := j.isLt; omega).trans (congrArg (st3 δ) (hUngZ j).symm))
    rw [hEqZ, h3Val δ hz, hZVal2 δ, hBVal2 δ, hCin2 δ hz, hSumFullEq δ, Nat.add_mul_mod_self_left]

theorem tap29_rCarryA_out {n : ℕ} (r : QRegister (71 + 29) n)
    (i : Fin 13) : rCarryOut 12 (tap29_rCarryA r) i = r ⟨71 + i.val, tap29_lt71_13 i⟩ :=
  congrArg r.wires (Fin.ext (by
    have := i.isLt; dsimp [tap29_rCarryA, tap29_fCarryA, tap29_idxCarryA, rCarryOut, fCarryOut]
    split_ifs; all_goals omega))

def tap29_st0 {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n) :
    BitAssignment n → BitAssignment n := stCarryIn 12 (tap29_rCarryA r) st
theorem tap29_st0_keep {n : ℕ} (r : QRegister (71 + 29) n) (st : BitAssignment n → BitAssignment n)
    (δ : BitAssignment n) {idx : ℕ} (hi : idx < 71 + 29) (hidx : idx < 71 ∨ 84 ≤ idx) :
    tap29_st0 r st δ (r ⟨idx, hi⟩) = st δ (r ⟨idx, hi⟩) := by
  dsimp only [tap29_st0, stCarryIn]
  exact writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, h⟩ ↦ by
    have hv := congrArg Fin.val (r.wires.injective ((tap29_rCarryA_out r i).symm.trans h))
    have _ := i.isLt; dsimp at hv; omega

theorem tap29_carryA_valA {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :
    finBitsVal (fun i : Fin 13 ↦ st δ (tap29_rCarryA r ⟨i.val, carryCh_ltA 12 i⟩)) =
      finBitsVal (fun k : Fin 13 ↦
        (fun j : Fin 14 ↦ tap29_st0 r st δ (r ⟨10 + j.val, tap29_lt10 j⟩))
          ⟨k.val, by have := k.isLt; omega⟩) :=
  congrArg finBitsVal (funext fun k ↦ Eq.symm <|
    (tap29_st0_keep r st δ _ (.inl (by have := k.isLt; omega))).trans <|
      congrArg (st δ) <| congrArg r.wires <| Fin.ext <| by
        have := k.isLt; dsimp [tap29_fCarryA, tap29_idxCarryA]; split_ifs; omega)

theorem tap29_carryA_valB {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :
    finBitsVal (fun i : Fin 13 ↦ st δ (tap29_rCarryA r ⟨12 + 1 + i.val, carryCh_ltB 12 i⟩)) =
      finBitsVal (fun k : Fin 13 ↦
        (fun j : Fin 14 ↦ tap29_st0 r st δ (r ⟨41 + j.val, tap29_lt41 j⟩))
          ⟨k.val, by have := k.isLt; omega⟩) :=
  congrArg finBitsVal (funext fun k ↦ Eq.symm <|
    (tap29_st0_keep r st δ _ (.inl (by have := k.isLt; omega))).trans <|
      congrArg (st δ) <| congrArg r.wires <| Fin.ext <| by
        have := k.isLt; dsimp [tap29_fCarryA, tap29_idxCarryA]; split_ifs <;> omega)

theorem tap29_cA13Bit_val_eq {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :
    (tap29_cA13Bit r (tap29_st0 r st) δ).val = (tap29_zLoVal r st δ + tap29_w1LoVal r st δ) /
    2 ^ 14 := by
  let f10 (j : Fin 14) := tap29_st0 r st δ (r ⟨10 + j.val, tap29_lt10 j⟩)
  let f41 (j : Fin 14) := tap29_st0 r st δ (r ⟨41 + j.val, tap29_lt41 j⟩)
  have hr83 : r ⟨83, tap29_lt83⟩ = rCarryOut 12 (tap29_rCarryA r) ⟨12, Nat.lt_succ_self 12⟩ := rfl
  have h83 : (tap29_st0 r st δ (r ⟨83, tap29_lt83⟩)).val =
      (finBitsVal (fun k : Fin 13 ↦ f10 ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩) +
       finBitsVal (fun k : Fin 13 ↦ f41 ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩)) / 2 ^ 13 := by
    change (stCarryIn 12 (tap29_rCarryA r) st δ (r ⟨83, tap29_lt83⟩)).val = _
    rw [hr83, carryChain_top_val 12 (tap29_rCarryA r) st δ,
      tap29_carryA_valA r st δ, tap29_carryA_valB r st δ]
  refine (gh16_seam_maj_val f10 f41 _ h83).trans ?_
  rw [show finBitsVal f10 = tap29_w1LoVal r st δ from
        congrArg finBitsVal (funext fun j ↦ tap29_st0_keep r st δ (tap29_lt10 j)
          (.inl (Nat.lt_trans (Nat.add_lt_add_left j.isLt 10) (by decide)))),
      show finBitsVal f41 = tap29_zLoVal r st δ from
        congrArg finBitsVal (funext fun j ↦ tap29_st0_keep r st δ (tap29_lt41 j)
          (.inl (Nat.lt_trans (Nat.add_lt_add_left j.isLt 41) (by decide)))), Nat.add_comm]

theorem tap29_st0_carryA_bit {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
    (i : Fin 13) : tap29_st0 r st δ (r ⟨71 + i.val, tap29_lt71_13 i⟩) =
    majCarryBit (tap29_w1LoVal r st δ) (tap29_zLoVal r st δ) 0 i.val := by
  change stCarryIn 12 (tap29_rCarryA r) st δ (r ⟨71 + i.val, tap29_lt71_13 i⟩) = _
  dsimp only [stCarryIn]
  have hEq := gh16_majCarryBit_13_eq_14
    (fun j : Fin 14 ↦ tap29_st0 r st δ (r ⟨10 + j.val, tap29_lt10 j⟩))
    (fun j : Fin 14 ↦ tap29_st0 r st δ (r ⟨41 + j.val, tap29_lt41 j⟩)) i
  rw [← tap29_rCarryA_out r i, writeReg_apply_reg, tap29_carryA_valA r st δ,
    tap29_carryA_valB r st δ, hEq,
    congrArg finBitsVal (funext fun j ↦ tap29_st0_keep r st δ (tap29_lt10 j)
      (.inl (Nat.lt_trans (Nat.add_lt_add_left j.isLt 10) (by decide)))),
    congrArg finBitsVal (funext fun j ↦ tap29_st0_keep r st δ (tap29_lt41 j)
      (.inl (Nat.lt_trans (Nat.add_lt_add_left j.isLt 41) (by decide))))]
  rfl

theorem tap29_fin14_mod4096_decomp (f : Fin 14 → ZMod 2) :
    finBitsVal f % 4096 = (finBitsVal f % 2048) + 2048 * (f ⟨11, by omega⟩).val := by
  have h11 := finBitsVal_lt (fun j : Fin 11 ↦ f ⟨j.val, by have := j.isLt; omega⟩)
  have hb := ZMod.val_lt (f ⟨11, by omega⟩)
  rw [finBitsVal_split 11 3 f, finBitsVal_split 1 2, gh16_finBitsVal_fin1]
  simp only [Fin.val_zero, add_zero] at h11 ⊢; omega

theorem tap29_cTapBit_val_eq {n : ℕ} (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) :
    (tap29_cTapBit r (tap29_st0 r st) δ).val = tap29_cTapVal r st δ := by
  let fW (j : Fin 14) := st δ (r ⟨10 + j.val, tap29_lt10 j⟩)
  let fZ (j : Fin 14) := st δ (r ⟨41 + j.val, tap29_lt41 j⟩)
  let c10 := tap29_st0 r st δ (r ⟨81, tap29_lt81⟩)
  have hc10Val : c10.val = (tap29_w1LoVal r st δ % 2048 + tap29_zLoVal r st δ % 2048) / 2048 := by
    rw [show c10 = majCarryBit (tap29_w1LoVal r st δ) (tap29_zLoVal r st δ) 0 10 from
      tap29_st0_carryA_bit r st δ ⟨10, by omega⟩,
      majCarryBit_val (Nat.zero_le 1) 10, add_zero, show (2 ^ 11 : ℕ) = 2048 from rfl]
  have hZFlip : (tap29_zLoVal r st δ + 2048) % 4096 =
      tap29_zLoVal r st δ % 2048 + 2048 * (fZ ⟨11, by omega⟩ + 1).val := by
    change (finBitsVal fZ + 2048) % 4096 =
      finBitsVal fZ % 2048 + 2048 * (fZ ⟨11, by omega⟩ + 1).val
    rw [← Nat.mod_add_mod _ 4096 2048, tap29_fin14_mod4096_decomp fZ]
    rcases DynCircExt.bit_cases (fZ ⟨11, by omega⟩) with hb | hb <;>
      simp only [hb, ZMod.val_zero, zero_add, ZMod.val_one, CharTwo.add_self_eq_zero] <;> omega
  have hW : tap29_w1LoVal r st δ % 4096 =
      tap29_w1LoVal r st δ % 2048 + 2048 * (fW ⟨11, by omega⟩).val :=
    tap29_fin14_mod4096_decomp fW
  dsimp only [tap29_cTapBit, tap29_cTapVal]
  rw [tap29_st0_keep r st δ tap29_lt52 (.inl (by omega)),
    tap29_st0_keep r st δ tap29_lt21 (.inl (by omega)), hZFlip, hW]
  change ((fZ ⟨11, by omega⟩ + 1 + c10) * (fW ⟨11, by omega⟩ + c10) + c10).val = _
  have := zmod2_maj_id (fZ ⟨11, by omega⟩ + 1) (fW ⟨11, by omega⟩) c10
  have := ZMod.val_lt ((fZ ⟨11, by omega⟩ + 1) + fW ⟨11, by omega⟩ + c10)
  omega

theorem tap29_yZero_vals {W n : ℕ} (rWork : QRegister W n) (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (hYG : ∀ (k : Fin 36) (δ : BitAssignment n),
    (∀ q : Fin W, δ (rWork q) = 0) → st δ (r ⟨0, midOW_lt0 29⟩) = 0 →
    st δ (r ⟨5 + k.val, midOW_ltY 29 k⟩) = 0) (δ : BitAssignment n)
    (hz : ∀ q : Fin W, δ (rWork q) = 0) (hg0 : st δ (r ⟨0, midOW_lt0 29⟩) = 0) :
    tap29_w1LoVal r st δ = 0 ∧ tap29_w1HiVal r st δ = 0 ∧ tap29_cTapVal r st δ = 0 ∧
    finBitsVal (fun j : Fin 16 ↦ st δ (r ⟨22 + j.val, tap29_lt22 j⟩)) = 0 ∧
    st δ (r ⟨38, tap29_lt38⟩) = 0 ∧ st δ (r ⟨40, tap29_lt40⟩) = 0 := by
  have hy := fun k : Fin 36 ↦ hYG k δ hz hg0
  have hw1L : tap29_w1LoVal r st δ = 0 := gh16_finBitsVal_eq_zero _ fun j ↦
      (congrArg (st δ) (congrArg r.wires (Fin.ext (by dsimp; omega)))).trans
        (hy ⟨5 + j.val, by have := j.isLt; omega⟩)
  refine ⟨hw1L, ?_, ?_, ?_, hy ⟨33, by omega⟩, hy ⟨35, by omega⟩⟩
  · exact gh16_finBitsVal_eq_zero _ fun j ↦
      (congrArg (st δ) (congrArg r.wires (Fin.ext (by dsimp; omega)))).trans
        (hy ⟨19 + j.val, by have := j.isLt; omega⟩)
  · dsimp only [tap29_cTapVal]; rw [hw1L]; omega
  · exact gh16_finBitsVal_eq_zero _ fun j ↦
      (congrArg (st δ) (congrArg r.wires (Fin.ext (by dsimp; omega)))).trans
        (hy ⟨17 + j.val, by have := j.isLt; omega⟩)

theorem tap29_phase_eq {W n : ℕ} (rWork : QRegister W n) (r : QRegister (71 + 29) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) (hYG : ∀ (k : Fin 36)
    (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) → st δ (r ⟨0, midOW_lt0 29⟩) = 0 →
    st δ (r ⟨5 + k.val, midOW_ltY 29 k⟩) = 0) (δ : BitAssignment n)
    (hz : ∀ q : Fin W, δ (rWork q) = 0) : ph δ + st δ (r ⟨0, midOW_lt0 29⟩) *
    st δ (r ⟨40, tap29_lt40⟩) + (((tap29_zHiVal r st δ + tap29_w1HiVal r st δ +
    (tap29_zLoVal r st δ + tap29_w1LoVal r st δ) / 2 ^ 14) / 2 ^ 16 : ℕ) : ZMod 2) +
    st δ (r ⟨0, midOW_lt0 29⟩) * st δ (r ⟨1, midOW_lt1 29⟩) + (st δ (r ⟨1, midOW_lt1 29⟩) + 1) *
    st δ (r ⟨38, tap29_lt38⟩) + (st δ (r ⟨1, midOW_lt1 29⟩) + 1) *
    ((((tap29_zHiVal r st δ + tap29_w1HiVal r st δ + (tap29_zLoVal r st δ + tap29_w1LoVal r st δ) /
    2 ^ 14) % 2 ^ 16 + finBitsVal (fun j : Fin 16 ↦ st δ (r ⟨22 + j.val, tap29_lt22 j⟩)) +
    tap29_cTapVal r st δ) / 2 ^ 16 : ℕ) : ZMod 2) = midOWPhaseTap29 r st ph δ := by
  rcases DynCircExt.bit_cases (st δ (r ⟨0, midOW_lt0 29⟩)) with hg0 | hg1
  · obtain ⟨hw1L, hw1H, hcTapZ, h22z, h38z, _⟩ :=
        tap29_yZero_vals rWork r st hYG δ hz hg0; dsimp only [midOWPhaseTap29]; rw [hg0, hw1L, hw1H,
        hcTapZ, h22z,
        h38z]; have hzLoLt : tap29_zLoVal r st δ < 2 ^ 14 :=
                 finBitsVal_lt _; have hzHiLt : tap29_zHiVal r st δ < 2 ^ 16 :=
                                    finBitsVal_lt _; simp only [add_zero, mul_zero, zero_mul,
                                    Nat.div_eq_of_lt hzLoLt, Nat.div_eq_of_lt hzHiLt,
                                    Nat.mod_eq_of_lt hzHiLt, Nat.cast_zero]
  · rw [tap29_phase_eq_sum30, hg1, one_mul, one_mul, one_mul];
    obtain ⟨_, hPh16⟩ :=
        gh16_two_pass_hi16 (tap29_zLoVal r st δ) (tap29_zHiVal r st δ) (tap29_w1LoVal r st δ)
        (tap29_w1HiVal r st δ) 0 (tap29_w2HiVal r st δ);
        have hsLoLt : (tap29_zLoVal r st δ + tap29_w1LoVal r st δ) % 2 ^ 14 < 2 ^ 14 :=
        Nat.mod_lt _ (Nat.two_pow_pos 14); rw [add_zero, Nat.div_eq_of_lt hsLoLt, add_zero] at hPh16
    rcases DynCircExt.bit_cases (st δ (r ⟨1, midOW_lt1 29⟩)) with hs0 | hs1
    · dsimp only [tap29_sum30, tap29_w2HiVal] at hPh16 ⊢;
      simp only [hs0, ↓reduceIte, zero_add, one_mul] at hPh16 ⊢; rw [← add_assoc] at hPh16
      rw [← hPh16]; ring
    · dsimp only [tap29_sum30, tap29_w2HiVal] at hPh16 ⊢;
      simp only [hs1, one_ne_zero, ↓reduceIte, mul_zero, add_zero, CharTwo.add_self_eq_zero,
          zero_mul] at hPh16 ⊢;
          have hzHiALt : (tap29_zHiVal r st δ + tap29_w1HiVal r st δ + (tap29_zLoVal r st δ +
          tap29_w1LoVal r st δ) / 2 ^ 14) % 2 ^ 16 < 2 ^ 16 :=
          Nat.mod_lt _ (Nat.two_pow_pos 16); rw [Nat.div_eq_of_lt hzHiALt, Nat.cast_zero,
          add_zero] at hPh16
      rw [← hPh16]; ring
end QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29

section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution Real
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (word512DualLegLo6)
namespace QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2
set_option Elab.async false
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Qrom hiding
  word512DualLegLo6
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (zmod2_eq_ite_of_beq_one
    natOfZModBits_lt natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulombFast (stepCB_primTree_bit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (itePos iteNeg ditePos
    diteNeg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (clbGam6 clbGam6_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
    (cmpBorrowStep evalPrimTree95_x_xor out22_t11_bits)
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, p => p k && allBelow k p

theorem allBelow_true_iff : ∀ (n : ℕ) (p : ℕ → Bool),
    allBelow n p = true ↔ ∀ k < n, p k = true
  | 0, _ => ⟨fun _ _ hk ↦ absurd hk (by omega), fun _ ↦ rfl⟩
  | n + 1, p => by
      simp only [allBelow, Bool.and_eq_true, allBelow_true_iff n p]
      exact ⟨fun ⟨hp, hall⟩ k hk ↦ if h : k = n then h ▸ hp else hall k (by omega),
        fun h ↦ ⟨h n (by omega), fun k hk ↦ h k (by omega)⟩⟩

def bxorNat (a b : ℕ) : ℕ := if xor (a % 2 == 1) (b % 2 == 1) then 1 else 0
def bandNat (a b : ℕ) : ℕ := if (a % 2 == 1) && (b % 2 == 1) then 1 else 0

def q01OfR6G6 (r6 g6 : ℕ) : ℕ :=
    bandNat (bxorNat (bxorNat (bxorNat 1 ((r6 / 2) % 2)) (r6 % 2)) ((g6 / 2) % 2)) (g6 % 2)
def subBorrows18Core (a3 b6 q01 z4 z2 z3 : ℕ) : ℕ × ℕ × ℕ :=
  let t6 := a3 % 2; let t7 := (a3 / 2) % 2; let t8 := (a3 / 4) % 2;
  let qEff := bxorNat (bxorNat q01 t6) b6; let za := bxorNat z2 qEff;
  let wC1 := bxorNat (bxorNat z3 z2) qEff;
  let e0 := bxorNat (bandNat (bxorNat (bxorNat z4 1) b6) (bxorNat t6 b6)) b6;
  let c0 := bxorNat (bandNat (bxorNat (bxorNat za 1) t7) (bxorNat t8 t7)) t7;
  let c1 := bxorNat (bandNat wC1 (bxorNat t8 e0)) e0;
  let d2 := bxorNat (bandNat (bxorNat (bxorNat z2 1) e0) (bxorNat t7 e0)) e0;
  let c2 := bxorNat (bandNat (bxorNat (bxorNat z3 1) d2) (bxorNat t8 d2)) d2
  (c0, c1, c2)

def rowO9MaskNat : ℕ → ℕ
  | 0 => 12203 | 1 => 2682 | 2 => 2285 | 3 => 3832 | 4 => 8193
  | 5 => 10877 | 6 => 8208 | 7 => 12538 | _ => 293

def rowDf8MaskNat : ℕ → ℕ
  | 0 => 9306 | 1 => 1171 | 2 => 8483 | 3 => 8548
  | 4 => 9107 | 5 => 818 | 6 => 3480 | _ => 4148

def rowO9Mask (q : Fin 9) : ℕ := rowO9MaskNat q.val
def rowDf8Mask (q : Fin 8) : ℕ := rowDf8MaskNat q.val

def parity13Aux (mask : ℕ) (f : ℕ → Bool) : ℕ → Bool
  | 0 => mask.testBit 13
  | k + 1 =>
      let p := parity13Aux mask f k
      if mask.testBit k then xor p (f k) else p

theorem parity13Aux_congr13 (mask : ℕ) {f g : ℕ → Bool} (hfg : ∀ b < 13, f b = g b) :
    ∀ k ≤ 13, parity13Aux mask f k = parity13Aux mask g k
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [parity13Aux]
      by_cases hm : mask.testBit k <;> simp only [hm, Bool.false_eq_true, ↓reduceIte,
          parity13Aux_congr13 mask hfg k (by omega), hfg k (by omega)]

def affineBit13 (mask x13 : ℕ) : Bool := parity13Aux mask x13.testBit 13
theorem affineBit13_eq (mask x13 : ℕ) :
    affineBit13 mask x13 = parity13Aux mask x13.testBit 13 := rfl

def pack8Bool (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Fin 256 :=
  ⟨(if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) + 4 * (if b2 then 1 else 0) +
    8 * (if b3 then 1 else 0) + 16 * (if b4 then 1 else 0) + 32 * (if b5 then 1 else 0) +
    64 * (if b6 then 1 else 0) + 128 * (if b7 then 1 else 0), by
    split_ifs <;> omega⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem pack8Bool_bits_cert :
    ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
      let v := (pack8Bool b0 b1 b2 b3 b4 b5 b6 b7).val
      v.testBit 0 = b0 ∧ v.testBit 1 = b1 ∧ v.testBit 2 = b2 ∧ v.testBit 3 = b3 ∧
      v.testBit 4 = b4 ∧ v.testBit 5 = b5 ∧ v.testBit 6 = b6 ∧ v.testBit 7 = b7 := by
  decide +kernel

def pack9Bool (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 512 :=
  ⟨(pack8Bool b0 b1 b2 b3 b4 b5 b6 b7).val + 256 * (if b8 then 1 else 0), by
    have := (pack8Bool b0 b1 b2 b3 b4 b5 b6 b7).isLt
    cases b8 <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem fin256_add_256_bool_cert : allBelow 256 (fun a ↦
    decide ((∀ q : Fin 8, (a + 256 * 0).testBit q.val = a.testBit q.val ∧
    (a + 256 * 1).testBit q.val = a.testBit q.val) ∧ (a + 256 * 0).testBit 8 = false ∧
    (a + 256 * 1).testBit 8 = true)) = true := by decide +kernel
def df8Of13 (x13 : ℕ) : Fin 256 :=
    pack8Bool (affineBit13 (rowDf8MaskNat 0) x13) (affineBit13 (rowDf8MaskNat 1) x13)
    (affineBit13 (rowDf8MaskNat 2) x13) (affineBit13 (rowDf8MaskNat 3) x13)
    (affineBit13 (rowDf8MaskNat 4) x13) (affineBit13 (rowDf8MaskNat 5) x13)
    (affineBit13 (rowDf8MaskNat 6) x13) (affineBit13 (rowDf8MaskNat 7) x13)
theorem df8Of13_testBit (x13 : ℕ) (q : Fin 8) : (df8Of13 x13).val.testBit q.val =
    affineBit13 (rowDf8Mask q) x13 := by
  dsimp only [df8Of13, rowDf8Mask]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pack8Bool_bits_cert
    (affineBit13 (rowDf8MaskNat 0) x13) (affineBit13 (rowDf8MaskNat 1) x13)
    (affineBit13 (rowDf8MaskNat 2) x13) (affineBit13 (rowDf8MaskNat 3) x13)
    (affineBit13 (rowDf8MaskNat 4) x13) (affineBit13 (rowDf8MaskNat 5) x13)
    (affineBit13 (rowDf8MaskNat 6) x13) (affineBit13 (rowDf8MaskNat 7) x13)
  rcases q with ⟨_ | _ | _ | _ | _ | _ | _ | _ | q, hq⟩ <;> first | assumption | omega

def o9Of13 (x13 : ℕ) : Fin 512 :=
    pack9Bool (affineBit13 (rowO9MaskNat 0) x13) (affineBit13 (rowO9MaskNat 1) x13)
    (affineBit13 (rowO9MaskNat 2) x13) (affineBit13 (rowO9MaskNat 3) x13)
    (affineBit13 (rowO9MaskNat 4) x13) (affineBit13 (rowO9MaskNat 5) x13)
    (affineBit13 (rowO9MaskNat 6) x13) (affineBit13 (rowO9MaskNat 7) x13)
    (affineBit13 (rowO9MaskNat 8) x13)
theorem o9Of13_testBit (x13 : ℕ) (q : Fin 9) : (o9Of13 x13).val.testBit q.val =
    affineBit13 (rowO9Mask q) x13 := by
  dsimp only [o9Of13, pack9Bool, rowO9Mask]
  set p8 := pack8Bool (affineBit13 (rowO9MaskNat 0) x13) (affineBit13 (rowO9MaskNat 1) x13)
    (affineBit13 (rowO9MaskNat 2) x13) (affineBit13 (rowO9MaskNat 3) x13)
    (affineBit13 (rowO9MaskNat 4) x13) (affineBit13 (rowO9MaskNat 5) x13)
    (affineBit13 (rowO9MaskNat 6) x13) (affineBit13 (rowO9MaskNat 7) x13)
  have hc :=
      of_decide_eq_true ((allBelow_true_iff 256 _).mp fin256_add_256_bool_cert p8.val p8.isLt)
  by_cases h8 : q.val < 8
  · rw [show (p8.val + 256 * if affineBit13 (rowO9MaskNat 8) x13 then 1 else 0).testBit q.val =
        p8.val.testBit q.val by cases affineBit13 (rowO9MaskNat 8) x13 <;> simp [hc.1 ⟨q.val, h8⟩]]
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := pack8Bool_bits_cert _ _ _ _ _ _ _ _
    rcases q with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _, _⟩ <;>
      first | assumption | exact absurd (show _ + 8 < 8 from h8) (by omega)
  · rw [show q.val = 8 by omega]
    cases affineBit13 (rowO9MaskNat 8) x13 <;> simp only [↓reduceIte, Bool.false_eq_true, hc]

def x13OfW11U01 (w : Fin 2048) (u0 u1 : Fin 2) : ℕ := w.val + 2048 * u0.val + 4096 * u1.val
theorem subBorrows18Core_zero_zero (q01 z4 z2 z3 : ℕ) : subBorrows18Core 0 0 q01 z4 z2 z3 =
    (0, 0, 0) := by
  unfold subBorrows18Core bxorNat bandNat
  cases (q01 % 2 == 1) <;> cases (z4 % 2 == 1) <;> cases (z2 % 2 == 1) <;> cases (z3 % 2 == 1) <;>
      rfl

def popBernJK2 (t11 : ℕ) (w : Fin 2048) (o9 : Fin 512) : ℕ :=
  let a5 := t11 / 64; let r6 := t11 % 64; let g6 := clbGam6 w.val
  let b6 := if g6 < r6 then 1 else 0
  let q01 := q01OfR6G6 r6 g6;
  let sb :=
      subBorrows18Core (a5 % 8) b6 q01 ((o9.val / 64) % 2) ((o9.val / 128) % 2)
      ((o9.val / 256) % 2); let aTop2 := (a5 / 8) % 4
  (if o9.val % 4 < aTop2 + sb.1 then 1 else 0) +
  (if (o9.val / 4) % 4 < aTop2 + sb.2.1 then 1 else 0) +
  (if (o9.val / 16) % 4 < aTop2 + sb.2.2 then 1 else 0)

theorem popBernJK2_lt_four (t11 : ℕ) (w : Fin 2048) (o9 : Fin 512) : popBernJK2 t11 w o9 < 4 := by
  unfold popBernJK2; dsimp only; split_ifs <;> omega
theorem popBernJK2_zero_of_t11_zero (w : Fin 2048) (o9 : Fin 512) : popBernJK2 0 w o9 = 0 := by
  unfold popBernJK2
  simp only [Nat.zero_div, Nat.zero_mod, Nat.not_lt_zero, ↓reduceIte,
    subBorrows18Core_zero_zero, Nat.add_zero]
def coin33ProxyOfJK2 (j : ℕ) : Fin 3 → Fin 2048 :=
  fun i ↦ ⟨if i.val < j then 0 else 2047, by split_ifs <;> decide⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem popBernJ_coin33ProxyOfJK2_cert (t11 : Fin 2048) (j : Fin 4) : (t11.val = 0 → j.val = 0) →
    popBernJ t11.val (coin33ProxyOfJK2 j.val) = j.val := by
  have hc : allBelow 2048 (fun t ↦ allBelow 4 (fun jv ↦
    decide ((t = 0 → jv = 0) → popBernJ t (coin33ProxyOfJK2 jv) = jv))) = true := by decide +kernel
  exact of_decide_eq_true ((allBelow_true_iff 4 _).mp ((allBelow_true_iff 2048 _).mp hc t11.val
      t11.isLt) j.val j.isLt)

theorem popBernJ_coin33ProxyOfJK2_eq {t11 : ℕ} (ht11 : t11 < 2048) (w : Fin 2048)
    (o9 : Fin 512) : popBernJ t11 (coin33ProxyOfJK2 (popBernJK2 t11 w o9)) = popBernJK2 t11 w o9 :=
  popBernJ_coin33ProxyOfJK2_cert ⟨t11, ht11⟩ ⟨popBernJK2 t11 w o9, popBernJK2_lt_four t11 w o9⟩
    (fun ht0 ↦ by dsimp only at ht0 ⊢; rw [ht0]; exact popBernJK2_zero_of_t11_zero w o9)

def ySampleK2 (word512 : ℕ → ℕ) (isNN : Bool) (d2 : ℕ) (w : Fin 2048) (o9 : Fin 512) : ℕ :=
  let p := evenOctIdxT10K isNN d2
  (word512 (4 * idx7OfParts p + popBernJK2 (t11OfParts p) w o9)) >>> p.2.2

theorem ySampleK2_eq_proxy (word512 : ℕ → ℕ) (isNN : Bool) {d2 : ℕ} (hd2 : d2 < 262144)
    (w : Fin 2048) (o9 : Fin 512) : ySampleK2 word512 isNN d2 w o9 =
    y36PopBernNoClamp word512 isNN d2 (coin33ProxyOfJK2 (popBernJK2 (t11OfParts (evenOctIdxT10K isNN
    d2)) w o9))
    := by
  have ht11 : t11OfParts (evenOctIdxT10K isNN d2) < 2048 :=
      (parts_popBern_bounds isNN hd2).2.1; unfold ySampleK2 y36PopBernNoClamp; dsimp only;
      rw [popBernJ_coin33ProxyOfJK2_eq ht11 w o9]
def linOpPrim : Bool × ℕ × ℕ → PrimTree
  | (false, u, _) => pX95 u
  | (true, a, b) => pCnot a b

def linOpsTree : List (Bool × ℕ × ℕ) → PrimTree
  | [] => .empty
  | [op] => linOpPrim op
  | op :: op2 :: rest => .node (linOpPrim op) (linOpsTree (op2 :: rest))

def linOpOk : Bool × ℕ × ℕ → Bool
  | (false, u, _) => decide (11 ≤ u ∧ u < 32)
  | (true, a, b) => decide (11 ≤ a ∧ a < 32 ∧ 11 ≤ b ∧ b < 32 ∧ a ≠ b)

def linOpStep : Bool × ℕ × ℕ → (ℕ → Bool) → (ℕ → Bool)
  | (false, u, _), f, i => xor (f i) (decide (i = u))
  | (true, a, b), f, i => if i = b then xor (f i) (f a) else f i

def linOpsStep : List (Bool × ℕ × ℕ) → (ℕ → Bool) → (ℕ → Bool)
  | [], f => f
  | op :: rest, f => linOpsStep rest (linOpStep op f)

theorem evalPrimTree_linOpPrim {op : Bool × ℕ × ℕ} (h : linOpOk op = true)
    (st i : ℕ) : (evalPrimTree 95 st (linOpPrim op)).testBit i = linOpStep op st.testBit i := by
  rcases op with ⟨_ | _, a, b⟩ <;> simp only [linOpOk, decide_eq_true_eq] at h
  · exact evalPrimTree95_x_xor (by omega) st i
  · exact evalPrimTree95_cnot (by omega) (by omega) h.2.2.2.2 st i

theorem linOpStep_congr (op : Bool × ℕ × ℕ) {f g : ℕ → Bool} (hfg : ∀ i, f i = g i)
    (i : ℕ) : linOpStep op f i = linOpStep op g i := by
  rcases op with ⟨isCx, a, b⟩; cases isCx <;> dsimp only [linOpStep]
  · rw [hfg]
  · by_cases hib : i = b <;> simp only [hib, ↓reduceIte, hfg]

theorem linOpsStep_congr :
    ∀ (ops : List (Bool × ℕ × ℕ)) {f g : ℕ → Bool}, (∀ i, f i = g i) →
      ∀ i, linOpsStep ops f i = linOpsStep ops g i
  | [], _, _, hfg, i => hfg i
  | op :: rest, _, _, hfg, i => linOpsStep_congr rest (linOpStep_congr op hfg) i

theorem evalPrimTree_linOpsTree :
    ∀ (ops : List (Bool × ℕ × ℕ)), ops.all linOpOk = true → ∀ (st i : ℕ),
      (evalPrimTree 95 st (linOpsTree ops)).testBit i = linOpsStep ops st.testBit i
  | [], _, st, i => by dsimp only [linOpsTree, evalPrimTree, linOpsStep]
  | [op], hOk, st, i => by
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hOk;
      exact evalPrimTree_linOpPrim hOk st i
  | op :: op2 :: rest, hOk, st, i => by
      simp only [List.all_cons, Bool.and_eq_true] at hOk;
      dsimp only [linOpsTree, evalPrimTree, linOpsStep]
      have h2 : (op2 :: rest).all linOpOk = true := by
        simp only [List.all_cons, Bool.and_eq_true]; exact hOk.2
      rw [evalPrimTree_linOpsTree (op2 :: rest) h2];
      exact linOpsStep_congr (op2 :: rest) (evalPrimTree_linOpPrim hOk.1 st) i
theorem linOpsStep_outside :
    ∀ (ops : List (Bool × ℕ × ℕ)), ops.all linOpOk = true → ∀ (f : ℕ → Bool) (i : ℕ),
      (i < 11 ∨ 32 ≤ i) → linOpsStep ops f i = f i
  | [], _, _, _, _ => rfl
  | op :: rest, hOk, f, i, hi => by
      simp only [List.all_cons, Bool.and_eq_true] at hOk; dsimp only [linOpsStep];
      rw [linOpsStep_outside rest hOk.2 _ i hi]
      rcases op with ⟨isCx, a, b⟩
      cases isCx <;> dsimp only [linOpOk] at hOk <;> simp only [decide_eq_true_eq] at hOk
      · dsimp only [linOpStep]
        have hne : decide (i = a) = false := decide_eq_false (by omega)
        rw [hne, Bool.xor_false]
      · dsimp only [linOpStep]
        exact iteNeg (by omega)

theorem linOpsStep_coin_local :
    ∀ (ops : List (Bool × ℕ × ℕ)), ops.all linOpOk = true → ∀ {f g : ℕ → Bool},
      (∀ i, 11 ≤ i → i < 32 → f i = g i) →
      ∀ i, 11 ≤ i → i < 32 → linOpsStep ops f i = linOpsStep ops g i
  | [], _, _, _, hfg, i, h0, h1 => hfg i h0 h1
  | op :: rest, hOk, f, g, hfg, i, h0, h1 => by
      simp only [List.all_cons, Bool.and_eq_true] at hOk
      refine linOpsStep_coin_local rest hOk.2 (fun j hj0 hj1 ↦ ?_) i h0 h1
      rcases op with ⟨isCx, a, b⟩
      cases isCx <;> dsimp only [linOpOk] at hOk <;> simp only [decide_eq_true_eq] at hOk
      · dsimp only [linOpStep]; rw [hfg j hj0 hj1]
      · dsimp only [linOpStep]
        by_cases hjb : j = b
        · subst hjb; rw [itePos rfl, itePos rfl, hfg j hj0 hj1, hfg a hOk.1.1 hOk.1.2.1]
        · rw [iteNeg hjb, iteNeg hjb, hfg j hj0 hj1]

def cmpSuffixGen (cHi t0 bInit outHi : ℕ) : ℕ → PrimTree
  | 0 => cmpBorrowStep cHi t0 bInit outHi
  | s + 1 =>
      .node (cmpSuffixGen cHi t0 bInit outHi s)
        (cmpBorrowStep (cHi + s + 1) (t0 + s + 1) (outHi + s) (outHi + s + 1))

def cmpGenBits (bInit : Bool) (cFn tFn : ℕ → Bool) : ℕ → Bool
  | 0 => (Bool.not (cFn 0) && tFn 0) || ((cFn 0 == tFn 0) && bInit)
  | s + 1 =>
      let p := cmpGenBits bInit cFn tFn s
      (Bool.not (cFn (s + 1)) && tFn (s + 1)) || ((cFn (s + 1) == tFn (s + 1)) && p)

theorem cmpBorrowStep_eval_gen {c t prev dst : ℕ}
    (hc0 : 11 ≤ c) (hc1 : c < 32) (ht : t < 11)
    (hp0 : prev < 11 ∨ 52 ≤ prev) (hpt : prev ≠ t) (hpd : prev < dst)
    (hd0 : 52 ≤ dst) (hd1 : dst < 85) (st : ℕ) :
    (∀ i, i ≠ dst → (evalPrimTree 95 st (cmpBorrowStep c t prev dst)).testBit i = st.testBit i) ∧
    (st.testBit dst = false →
      (evalPrimTree 95 st (cmpBorrowStep c t prev dst)).testBit dst =
        ((Bool.not (st.testBit c) && st.testBit t) ||
          ((st.testBit c == st.testBit t) && st.testBit prev))) := by
  dsimp only [cmpBorrowStep, evalPrimTree]
  set s1 := evalPrimTree 95 st (pCnot prev c)
  set s2 := evalPrimTree 95 s1 (pCnot prev t)
  set s3 := evalPrimTree 95 s2 (pAnd c t dst)
  set s4 := evalPrimTree 95 s3 (pCnot prev c)
  set s5 := evalPrimTree 95 s4 (pCnot prev t)
  have ePC := evalPrimTree95_cnot (src := prev) (dst := c) (by omega) (by omega) (by omega)
  have ePT := evalPrimTree95_cnot (src := prev) (dst := t) (by omega) (by omega) (by omega)
  have e3 := evalPrimTree95_and (a := c) (b := t) (dst := dst)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) s2
  have e6 := evalPrimTree95_cnot (src := t) (dst := dst) (by omega) (by omega) (by omega) s5
  have hp1 : s1.testBit prev = st.testBit prev := (ePC st prev).trans (iteNeg (by omega))
  have hp3 : s3.testBit prev = st.testBit prev := (e3 prev).trans
    ((iteNeg (by omega)).trans ((ePT s1 prev).trans ((iteNeg (by omega)).trans hp1)))
  have hp4 : s4.testBit prev = _ := (ePC s3 prev).trans ((iteNeg (by omega)).trans hp3)
  have ht5 : s5.testBit t = st.testBit t := by
    rw [ePT s4 t, itePos rfl, hp4, ePC s3 t, iteNeg (by omega),
      e3 t, iteNeg (by omega), ePT s1 t, itePos rfl, hp1, ePC st t, iteNeg (by omega),
      Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  refine ⟨fun i hnd ↦ ?_, fun hd0' ↦ ?_⟩
  · rw [e6 i, iteNeg hnd]
    rcases eq_or_ne i t with rfl | hit
    · exact ht5
    · rw [ePT s4 i, iteNeg hit]
      rcases eq_or_ne i c with rfl | hic
      · rw [ePC s3 i, itePos rfl, hp3, e3 i, iteNeg (by omega), ePT s1 i, iteNeg (by omega),
          ePC st i, itePos rfl, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      · rw [ePC s3 i, iteNeg hic, e3 i, iteNeg hnd, ePT s1 i, iteNeg hit, ePC st i, iteNeg hic]
  · rw [e6 dst, itePos rfl, ht5, ePT s4 dst, iteNeg (by omega), ePC s3 dst, iteNeg (by omega),
      e3 dst, itePos rfl, ePT s1 dst, iteNeg (by omega), ePC st dst, iteNeg (by omega), hd0',
      ePT s1 c, iteNeg (by omega), ePC st c, itePos rfl, ePT s1 t, itePos rfl, hp1, ePC st t,
      iteNeg (by omega)]
    cases st.testBit c <;> cases st.testBit t <;> cases st.testBit prev <;> rfl

theorem cmpSuffixGen_eval {cHi t0 bInit outHi : ℕ}
    (hc0 : 17 ≤ cHi) (hb0 : bInit < 11 ∨ 52 ≤ bInit) (hb1 : bInit < outHi)
    (hbT : bInit ≠ t0) (ho0 : 58 ≤ outHi) :
    ∀ (s : ℕ), cHi + s < 32 → t0 + s < 11 → outHi + s < 85 → ∀ (st : ℕ),
      (∀ i, (i < outHi ∨ outHi + s < i) →
        (evalPrimTree 95 st (cmpSuffixGen cHi t0 bInit outHi s)).testBit i = st.testBit i) ∧
      ((∀ j ≤ s, st.testBit (outHi + j) = false) →
        (evalPrimTree 95 st (cmpSuffixGen cHi t0 bInit outHi s)).testBit (outHi + s) =
          cmpGenBits (st.testBit bInit) (fun j ↦ st.testBit (cHi + j))
            (fun j ↦ st.testBit (t0 + j)) s)
  | 0, _, _, _, st => by
      dsimp only [cmpSuffixGen, cmpGenBits, Nat.add_zero]
      obtain ⟨hp, hv⟩ := cmpBorrowStep_eval_gen (by omega : 11 ≤ cHi) (by omega)
        (by omega : t0 < 11) hb0 hbT hb1 (by omega) (by omega) st
      exact ⟨fun i hi ↦ hp i (by omega), fun hCln ↦ hv (hCln 0 le_rfl)⟩
  | s + 1, _, _, _, st => by
      dsimp only [cmpSuffixGen, evalPrimTree, cmpGenBits]
      obtain ⟨hp0, hv0⟩ := cmpSuffixGen_eval hc0 hb0 hb1 hbT ho0 s
        (by omega) (by omega) (by omega) st
      obtain ⟨hp1, hv1⟩ := cmpBorrowStep_eval_gen (by omega : 11 ≤ cHi + s + 1) (by omega)
        (by omega : t0 + s + 1 < 11) (.inr (by omega : 52 ≤ outHi + s)) (by omega)
        (by omega : outHi + s < outHi + s + 1) (by omega) (by omega)
        (evalPrimTree 95 st (cmpSuffixGen cHi t0 bInit outHi s))
      refine ⟨fun i hi ↦ (hp1 i (by omega)).trans (hp0 i (by omega)), fun hCln ↦ ?_⟩
      rw [show outHi + (s + 1) = outHi + s + 1 by omega,
        hv1 ((hp0 _ (.inr (by omega))).trans (hCln (s + 1) le_rfl)),
        hp0 (cHi + s + 1) (.inl (by omega)), hp0 (t0 + s + 1) (.inl (by omega)),
        show cHi + s + 1 = cHi + (s + 1) by omega, show t0 + s + 1 = t0 + (s + 1) by omega,
        hv0 fun j hj ↦ hCln j (by omega)]

theorem cmpGenBits_congr (b0 : Bool) {c1 c2 t1 t2 : ℕ → Bool} :
    ∀ (s : ℕ), (∀ j ≤ s, c1 j = c2 j) → (∀ j ≤ s, t1 j = t2 j) →
      cmpGenBits b0 c1 t1 s = cmpGenBits b0 c2 t2 s
  | 0, hc, ht => by
      dsimp only [cmpGenBits]; rw [hc 0 le_rfl, ht 0 le_rfl]
  | s + 1, hc, ht => by
      dsimp only [cmpGenBits]
      rw [cmpGenBits_congr b0 s (fun j hj ↦ hc j (by omega)) (fun j hj ↦ ht j (by omega)),
          hc (s + 1) le_rfl, ht (s + 1) le_rfl]

def linOpStepB : Bool × ℕ × ℕ → (ℕ → Bool) → (ℕ → Bool)
  | (false, u, _), f, i => xor (f i) (Nat.beq i u)
  | (true, a, b), f, i => cond (Nat.beq i b) (xor (f i) (f a)) (f i)

def linOpsStepB : List (Bool × ℕ × ℕ) → (ℕ → Bool) → (ℕ → Bool)
  | [], f => f
  | op :: rest, f => linOpsStepB rest (linOpStepB op f)

theorem natBeq_false_of_ne {i k : ℕ} (h : i ≠ k) : Nat.beq i k = false :=
  Bool.eq_false_iff.mpr fun ht ↦ h (Nat.beq_eq.mp ht)

theorem linOpStep_eq_B (op : Bool × ℕ × ℕ) (f : ℕ → Bool) (i : ℕ) :
    linOpStep op f i = linOpStepB op f i := by
  rcases op with ⟨_ | _, a, b⟩
  · by_cases h : i = a <;> simp [linOpStep, linOpStepB, h, natBeq_false_of_ne]
  · by_cases h : i = b <;> simp [linOpStep, linOpStepB, h, natBeq_false_of_ne]

theorem linOpsStep_eq_B :
    ∀ (ops : List (Bool × ℕ × ℕ)) (f : ℕ → Bool) (i : ℕ),
      linOpsStep ops f i = linOpsStepB ops f i
  | [], _, _ => rfl
  | op :: rest, f, i =>
      (linOpsStep_congr rest (linOpStep_eq_B op f) i).trans (linOpsStep_eq_B rest (linOpStepB op f)
          i)

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem t11_bits_split (t11 : Fin 2048) : (∀ b : Fin 6, t11.val.testBit b.val =
    (t11.val % 64).testBit b.val) ∧ (∀ j : Fin 5, t11.val.testBit (6 + j.val) =
    (t11.val / 64).testBit j.val) ∧ (if t11.val.testBit 6 then 1 else 0) = (t11.val / 64) % 2 := by
  have hc : allBelow 2048 (fun x ↦
    allBelow 6 (fun b ↦ decide (x.testBit b = (x % 64).testBit b)) &&
    allBelow 5 (fun j ↦ decide (x.testBit (6 + j) = (x / 64).testBit j)) &&
    decide ((if x.testBit 6 then 1 else 0) = (x / 64) % 2)) = true := by decide +kernel
  have h :=
      (allBelow_true_iff 2048 _).mp hc t11.val t11.isLt; rw [Bool.and_eq_true,
      Bool.and_eq_true] at h
  exact ⟨fun b ↦ of_decide_eq_true ((allBelow_true_iff 6 _).mp h.1.1 b.val b.isLt), fun j ↦
      of_decide_eq_true ((allBelow_true_iff 5 _).mp h.1.2 j.val j.isLt), of_decide_eq_true h.2⟩

inductive GenOp
  | x (u : ℕ)
  | cx (a b : ℕ)
  | tand (a b dst : ℕ)

def genOpPrim : GenOp → PrimTree
  | .x u => pX95 u
  | .cx a b => pCnot a b
  | .tand a b dst => pAnd a b dst

def genOpsTree : List GenOp → PrimTree
  | [] => .empty
  | [op] => genOpPrim op
  | op :: op2 :: rest => .node (genOpPrim op) (genOpsTree (op2 :: rest))

def genOpOk : GenOp → Bool
  | .x u => decide (u < 96)
  | .cx a b => decide (a < 96 ∧ b < 96 ∧ a ≠ b)
  | .tand a b dst => decide (a < 96 ∧ b < 96 ∧ dst < 96 ∧ a ≠ b ∧ a ≠ dst ∧ b ≠ dst)

def genOpStep : GenOp → (ℕ → Bool) → (ℕ → Bool)
  | .x u, f, i => xor (f i) (decide (i = u))
  | .cx a b, f, i => if i = b then xor (f i) (f a) else f i
  | .tand a b dst, f, i => if i = dst then xor (f i) (f a && f b) else f i

def genOpStepB : GenOp → (ℕ → Bool) → (ℕ → Bool)
  | .x u, f, i => xor (f i) (Nat.beq i u)
  | .cx a b, f, i => cond (Nat.beq i b) (xor (f i) (f a)) (f i)
  | .tand a b dst, f, i => cond (Nat.beq i dst) (xor (f i) (f a && f b)) (f i)

def genOpsStep : List GenOp → (ℕ → Bool) → (ℕ → Bool)
  | [], f => f
  | op :: rest, f => genOpsStep rest (genOpStep op f)

def genOpsStepB : List GenOp → (ℕ → Bool) → (ℕ → Bool)
  | [], f => f
  | op :: rest, f => genOpsStepB rest (genOpStepB op f)

theorem genOpStep_congr (op : GenOp) {f g : ℕ → Bool} (hfg : ∀ i, f i = g i)
    (i : ℕ) : genOpStep op f i = genOpStep op g i := by
  cases op with
  | x u => dsimp only [genOpStep]; rw [hfg]
  | cx a b => dsimp only [genOpStep]; by_cases h : i = b <;> simp only [h, ↓reduceIte, hfg]
  | tand a b d => dsimp only [genOpStep]; by_cases h : i = d <;> simp only [h, ↓reduceIte, hfg]

theorem genOpsStep_congr :
    ∀ (ops : List GenOp) {f g : ℕ → Bool}, (∀ i, f i = g i) →
      ∀ i, genOpsStep ops f i = genOpsStep ops g i
  | [], _, _, hfg, i => hfg i
  | op :: rest, _, _, hfg, i => genOpsStep_congr rest (genOpStep_congr op hfg) i

theorem genOpStep_eq_B (op : GenOp) (f : ℕ → Bool) (i : ℕ) :
    genOpStep op f i = genOpStepB op f i := by
  cases op with
  | x u => by_cases h : i = u <;> simp [genOpStep, genOpStepB, h, natBeq_false_of_ne]
  | cx a b => by_cases h : i = b <;> simp [genOpStep, genOpStepB, h, natBeq_false_of_ne]
  | tand a b d => by_cases h : i = d <;> simp [genOpStep, genOpStepB, h, natBeq_false_of_ne]

theorem genOpsStep_eq_B :
    ∀ (ops : List GenOp) (f : ℕ → Bool) (i : ℕ),
      genOpsStep ops f i = genOpsStepB ops f i
  | [], _, _ => rfl
  | op :: rest, f, i =>
      (genOpsStep_congr rest (genOpStep_eq_B op f) i).trans
        (genOpsStep_eq_B rest (genOpStepB op f) i)

theorem evalPrimTree_genOpPrim {op : GenOp} (h : genOpOk op = true)
    (st i : ℕ) : (evalPrimTree 95 st (genOpPrim op)).testBit i = genOpStep op st.testBit i := by
  cases op <;> simp only [genOpOk, decide_eq_true_eq] at h
  · exact evalPrimTree95_x_xor h st i
  · exact evalPrimTree95_cnot h.1 h.2.1 h.2.2 st i
  · exact evalPrimTree95_and h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 st i

theorem evalPrimTree_genOpsTree :
    ∀ (ops : List GenOp), ops.all genOpOk = true → ∀ (st i : ℕ),
      (evalPrimTree 95 st (genOpsTree ops)).testBit i = genOpsStep ops st.testBit i
  | [], _, st, i => by dsimp only [genOpsTree, evalPrimTree, genOpsStep]
  | [op], hOk, st, i => by
      simp only [List.all_cons, List.all_nil, Bool.and_true] at hOk;
      exact evalPrimTree_genOpPrim hOk st i
  | op :: op2 :: rest, hOk, st, i => by
      simp only [List.all_cons, Bool.and_eq_true] at hOk;
      dsimp only [genOpsTree, evalPrimTree, genOpsStep]
      have h2 : (op2 :: rest).all genOpOk = true := by
        simp only [List.all_cons, Bool.and_eq_true]; exact hOk.2
      rw [evalPrimTree_genOpsTree (op2 :: rest) h2];
      exact genOpsStep_congr (op2 :: rest) (evalPrimTree_genOpPrim hOk.1 st) i
def genOpWriteOk (m : ℕ) : GenOp → Bool
  | .x u => m.testBit u
  | .cx _ b => m.testBit b
  | .tand _ _ d => m.testBit d

def genOpLocalOk (m : ℕ) : GenOp → Bool
  | .x u => m.testBit u
  | .cx a b => m.testBit a && m.testBit b
  | .tand a b d => m.testBit a && m.testBit b && m.testBit d

theorem genOpStep_outside {m : ℕ} {op : GenOp} (h : genOpWriteOk m op = true) (f : ℕ → Bool)
    {i : ℕ} (hi : m.testBit i = false) : genOpStep op f i = f i := by
  have ne_of (k : ℕ) (hk : m.testBit k = true) : i ≠ k :=
    fun e ↦ Bool.false_ne_true (hi.symm.trans (e ▸ hk))
  cases op with
  | x u => simp [genOpStep, decide_eq_false (ne_of u h)]
  | cx a b => simp [genOpStep, ne_of b h]
  | tand a b d => simp [genOpStep, ne_of d h]

theorem genOpsStep_outside {m : ℕ} :
    ∀ (ops : List GenOp), ops.all (genOpWriteOk m) = true → ∀ (f : ℕ → Bool) {i : ℕ},
      m.testBit i = false → genOpsStep ops f i = f i
  | [], _, f, _, _ => rfl
  | op :: rest, hOk, f, i, hi => by
      simp only [List.all_cons, Bool.and_eq_true] at hOk; dsimp only [genOpsStep];
      rw [genOpsStep_outside rest hOk.2 _ hi]; exact genOpStep_outside hOk.1 f hi
theorem genOpStep_local {m : ℕ} {op : GenOp} (h : genOpLocalOk m op = true) {f g : ℕ → Bool}
    (hfg : ∀ j, m.testBit j = true → f j = g j) {j : ℕ} (hj : m.testBit j = true) :
    genOpStep op f j = genOpStep op g j := by
  cases op with
  | x u =>
      dsimp only [genOpStep]; rw [hfg j hj]
  | cx a b =>
      simp only [genOpLocalOk, Bool.and_eq_true] at h; dsimp only [genOpStep]
      by_cases hjb : j = b <;> simp only [hjb, ↓reduceIte, hfg j hj, hfg b h.2, hfg a h.1]
  | tand a b d =>
      simp only [genOpLocalOk, Bool.and_eq_true] at h; dsimp only [genOpStep]
      by_cases hjd : j = d <;> simp only [hjd, ↓reduceIte, hfg j hj, hfg d h.2, hfg a h.1.1,
          hfg b h.1.2]

theorem genOpsStep_local {m : ℕ} :
    ∀ (ops : List GenOp), ops.all (genOpLocalOk m) = true →
      ∀ {f g : ℕ → Bool}, (∀ j, m.testBit j = true → f j = g j) →
        ∀ {j : ℕ}, m.testBit j = true → genOpsStep ops f j = genOpsStep ops g j
  | [], _, _, _, hfg, _, hj => hfg _ hj
  | op :: rest, hOk, f, g, hfg, j, hj => by
      simp only [List.all_cons, Bool.and_eq_true] at hOk
      exact genOpsStep_local rest hOk.2 (fun k hk ↦ genOpStep_local hOk.1 hfg hk) hj

def cmpBorrowOps (c t prev dst : ℕ) : List GenOp :=
    [.cx prev c, .cx prev t, .tand c t dst, .cx prev c, .cx prev t, .cx t dst]
def cmp2JointQ01Ops : List GenOp :=
    [ .x 12, .cx 0 12, .cx 1 12, .tand 12 11 52 , .x 12, .cx 0 12 , .cx 52 11, .cx 0 11, .cx 1 11 ,
    .tand 12 11 53 , .cx 1 11, .cx 11 53, .cx 0 11, .cx 52 11, .cx 1 12 ]
def midSubBorrows18Ops : List GenOp :=
    cmpBorrowOps 23 6 57 58 ++ [ .cx 6 52, .cx 57 52, .cx 52 24, .cx 24 25 ] ++
    cmpBorrowOps 24 8 7 59 ++ [ .cx 58 8, .tand 25 8 60, .cx 58 8, .cx 58 60 , .cx 24 25,
    .cx 52 24 ] ++ cmpBorrowOps 24 7 58 61 ++ cmpBorrowOps 25 8 61 62
def popCount3Ops18 : List GenOp :=
    [ .cx 68 64, .cx 68 66, .tand 64 66 69, .cx 68 69, .cx 68 66, .cx 66 64 ]
def cmp2JointQ01Tree : PrimTree := genOpsTree cmp2JointQ01Ops
def midSubBorrows18Tree : PrimTree := genOpsTree midSubBorrows18Ops
def popCount3Tree18 : PrimTree := genOpsTree popCount3Ops18

def coul18K2SMask : ℕ := 1180587117117783932928

def maskCmp2 : ℕ := 13510798882117635
def maskMid18 : ℕ := 9083760448465011136
def maskPop3 : ℕ := 977677435906606235648

theorem cmp2JointQ01Ops_ok :
    cmp2JointQ01Ops.all genOpOk = true ∧
    cmp2JointQ01Ops.all (genOpWriteOk maskCmp2) = true ∧
    cmp2JointQ01Ops.all (genOpLocalOk maskCmp2) = true := by decide

theorem midSubBorrows18Ops_ok :
    midSubBorrows18Ops.all genOpOk = true ∧
    midSubBorrows18Ops.all (genOpWriteOk maskMid18) = true ∧
    midSubBorrows18Ops.all (genOpLocalOk maskMid18) = true := by decide

theorem popCount3Ops18_ok :
    popCount3Ops18.all genOpOk = true ∧
    popCount3Ops18.all (genOpWriteOk maskPop3) = true ∧
    popCount3Ops18.all (genOpLocalOk maskPop3) = true := by decide

def modelCmp2 (r2 g2 : Fin 4) (i : ℕ) : Bool :=
    if i = 0 then r2.val.testBit 0 else if i = 1 then r2.val.testBit 1 else if i =
    11 then g2.val.testBit 0 else if i = 12 then g2.val.testBit 1 else false
def modelCmp2Any (m : Fin 64) (i : ℕ) : Bool :=
    if i = 0 then m.val.testBit 0 else if i = 1 then m.val.testBit 1 else if i =
    11 then m.val.testBit 2 else if i = 12 then m.val.testBit 3 else if i =
    52 then m.val.testBit 4 else if i = 53 then m.val.testBit 5 else false
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem cmp2JointQ01_pres_cert :
    ∀ m : Fin 64,
      let f := genOpsStepB cmp2JointQ01Ops (modelCmp2Any m)
      f 0 = m.val.testBit 0 ∧ f 1 = m.val.testBit 1 ∧
      f 11 = m.val.testBit 2 ∧ f 12 = m.val.testBit 3 := by decide +kernel

def modelCmp2Nat (r2 g2 i : ℕ) : Bool :=
    if i = 0 then r2.testBit 0 else if i = 1 then r2.testBit 1 else if i =
    11 then g2.testBit 0 else if i = 12 then g2.testBit 1 else false
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem cmp2JointQ01_eval_cert (r6 g6 : Fin 64) :
    let f := genOpsStepB cmp2JointQ01Ops (modelCmp2 ⟨r6.val % 4, by omega⟩ ⟨g6.val % 4, by omega⟩)
    f 52 = (q01OfR6G6 r6.val g6.val == 1) ∧
    f 53 = cmpBits 1 g6.val.testBit r6.val.testBit := by
  have hc : allBelow 64 (fun r ↦ allBelow 64 (fun g ↦
    let f := genOpsStepB cmp2JointQ01Ops (modelCmp2Nat (r % 4) (g % 4))
    decide (f 52 = (q01OfR6G6 r g == 1) ∧ f 53 = cmpBits 1 g.testBit r.testBit))) =
        true := by decide +kernel
  exact of_decide_eq_true ((allBelow_true_iff 64 _).mp ((allBelow_true_iff 64 _).mp hc r6.val
      r6.isLt) g6.val g6.isLt)

def modelMid18Any (mHi : Fin 64) (mLo : Fin 128) (i : ℕ) : Bool :=
    if i = 6 then mLo.val.testBit 0 else if i = 7 then mLo.val.testBit 1 else if i =
    8 then mLo.val.testBit 2 else if i = 23 then mLo.val.testBit 3 else if i =
    24 then mLo.val.testBit 4 else if i = 25 then mLo.val.testBit 5 else if i =
    52 then mLo.val.testBit 6 else if i = 57 then mHi.val.testBit 0 else if i =
    58 then mHi.val.testBit 1 else if i = 59 then mHi.val.testBit 2 else if i =
    60 then mHi.val.testBit 3 else if i = 61 then mHi.val.testBit 4 else if i =
    62 then mHi.val.testBit 5 else false
structure Mid18St where
  b6 : Bool
  b7 : Bool
  b8 : Bool
  b23 : Bool
  b24 : Bool
  b25 : Bool
  b52 : Bool
  b57 : Bool
  b58 : Bool
  b59 : Bool
  b60 : Bool
  b61 : Bool
  b62 : Bool

def mid18Get (s : Mid18St) (i : ℕ) : Bool :=
  cond (Nat.beq i 6) s.b6 <|
  cond (Nat.beq i 7) s.b7 <|
  cond (Nat.beq i 8) s.b8 <|
  cond (Nat.beq i 23) s.b23 <|
  cond (Nat.beq i 24) s.b24 <|
  cond (Nat.beq i 25) s.b25 <|
  cond (Nat.beq i 52) s.b52 <|
  cond (Nat.beq i 57) s.b57 <|
  cond (Nat.beq i 58) s.b58 <|
  cond (Nat.beq i 59) s.b59 <|
  cond (Nat.beq i 60) s.b60 <|
  cond (Nat.beq i 61) s.b61 <|
  cond (Nat.beq i 62) s.b62 false

def mid18Set : Mid18St → ℕ → Bool → Mid18St
  | .mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62, i, true =>
      cond (Nat.beq i 6) (.mk true b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 7) (.mk b6 true b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 8) (.mk b6 b7 true b23 b24 b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 23) (.mk b6 b7 b8 true b24 b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 24) (.mk b6 b7 b8 b23 true b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 25) (.mk b6 b7 b8 b23 b24 true b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 52) (.mk b6 b7 b8 b23 b24 b25 true b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 57) (.mk b6 b7 b8 b23 b24 b25 b52 true b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 58) (.mk b6 b7 b8 b23 b24 b25 b52 b57 true b59 b60 b61 b62) <|
      cond (Nat.beq i 59) (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 true b60 b61 b62) <|
      cond (Nat.beq i 60) (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 true b61 b62) <|
      cond (Nat.beq i 61) (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 true b62) <|
      cond (Nat.beq i 62) (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 true)
        (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62)
  | .mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62, i, false =>
      cond (Nat.beq i 6) (.mk false b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 7) (.mk b6 false b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 8) (.mk b6 b7 false b23 b24 b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 23) (.mk b6 b7 b8 false b24 b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 24) (.mk b6 b7 b8 b23 false b25 b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 25) (.mk b6 b7 b8 b23 b24 false b52 b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 52) (.mk b6 b7 b8 b23 b24 b25 false b57 b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 57) (.mk b6 b7 b8 b23 b24 b25 b52 false b58 b59 b60 b61 b62) <|
      cond (Nat.beq i 58) (.mk b6 b7 b8 b23 b24 b25 b52 b57 false b59 b60 b61 b62) <|
      cond (Nat.beq i 59) (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 false b60 b61 b62) <|
      cond (Nat.beq i 60) (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 false b61 b62) <|
      cond (Nat.beq i 61) (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 false b62) <|
      cond (Nat.beq i 62) (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 false)
        (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62)

def sBool {α : Type} (b : Bool) (k : Bool → α) : α := Bool.casesOn b (k false) (k true)
theorem sBool_eq {α : Type} (b : Bool) (k : Bool → α) : sBool b k = k b := by
  cases b <;> rfl

def sMid18 {α : Type} (s : Mid18St) (k : Mid18St → α) : α :=
    Mid18St.casesOn s fun b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62 ↦
    k (.mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62)
theorem sMid18_eq {α : Type} (s : Mid18St) (k : Mid18St → α) : sMid18 s k = k s := by
  cases s; rfl

def mid18StepOp : GenOp → Mid18St → Mid18St
  | .x u, s => mid18Set s u (!mid18Get s u)
  | .cx a b, s => mid18Set s b (xor (mid18Get s b) (mid18Get s a))
  | .tand a b d, s => mid18Set s d (xor (mid18Get s d) (mid18Get s a && mid18Get s b))

def mid18Steps : List GenOp → Mid18St → Mid18St
  | [], s => s
  | op :: rest, s => sMid18 (mid18StepOp op s) (mid18Steps rest)

theorem maskMid18_mem {u : ℕ} (h : maskMid18.testBit u = true) : u = 6 ∨ u = 7 ∨ u = 8 ∨ u = 23 ∨
    u = 24 ∨ u = 25 ∨ u = 52 ∨ u = 57 ∨ u = 58 ∨ u = 59 ∨ u = 60 ∨ u = 61 ∨ u = 62 := by
  refine (by decide : ∀ k < 96, maskMid18.testBit k = true →
    k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 52 ∨
    k = 57 ∨ k = 58 ∨ k = 59 ∨ k = 60 ∨ k = 61 ∨ k = 62) u (Nat.lt_of_not_ge fun hge ↦ ?_) h
  exact Bool.false_ne_true ((Nat.testBit_lt_two_pow
    ((by decide : maskMid18 < 2 ^ 96).trans_le
      (Nat.pow_le_pow_right (by decide) hge))).symm.trans h)

theorem mid18Get_other (s : Mid18St) {i : ℕ} (h6 : i ≠ 6) (h7 : i ≠ 7) (h8 : i ≠ 8) (h23 : i ≠ 23)
    (h24 : i ≠ 24) (h25 : i ≠ 25) (h52 : i ≠ 52) (h57 : i ≠ 57) (h58 : i ≠ 58) (h59 : i ≠ 59)
    (h60 : i ≠ 60) (h61 : i ≠ 61) (h62 : i ≠ 62) : mid18Get s i = false := by
  simp only [mid18Get, natBeq_false_of_ne h6, natBeq_false_of_ne h7, natBeq_false_of_ne h8,
    natBeq_false_of_ne h23, natBeq_false_of_ne h24, natBeq_false_of_ne h25,
    natBeq_false_of_ne h52, natBeq_false_of_ne h57, natBeq_false_of_ne h58,
    natBeq_false_of_ne h59, natBeq_false_of_ne h60, natBeq_false_of_ne h61,
    natBeq_false_of_ne h62, Bool.cond_false]
theorem mid18Get_set (s : Mid18St) {u : ℕ} (h : maskMid18.testBit u = true) (v : Bool)
    (i : ℕ) : mid18Get (mid18Set s u v) i = if i = u then v else mid18Get s i := by
  by_cases hi : maskMid18.testBit i = true
  · cases s
    cases v <;> rcases maskMid18_mem hi with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases maskMid18_mem h with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · have ne : ∀ k, maskMid18.testBit k = true → i ≠ k := fun _ hk e ↦ hi (e ▸ hk)
    have hO (t : Mid18St) := mid18Get_other t (ne 6 (by decide)) (ne 7 (by decide))
      (ne 8 (by decide)) (ne 23 (by decide)) (ne 24 (by decide)) (ne 25 (by decide))
      (ne 52 (by decide)) (ne 57 (by decide)) (ne 58 (by decide)) (ne 59 (by decide))
      (ne 60 (by decide)) (ne 61 (by decide)) (ne 62 (by decide))
    rw [hO, _root_.ite_eq_right (ne u h), hO]

theorem mid18StepOp_eq {op : GenOp} (h : genOpWriteOk maskMid18 op = true) (s : Mid18St)
    (i : ℕ) : genOpStep op (mid18Get s) i = mid18Get (mid18StepOp op s) i := by
  cases op with
  | x u => by_cases hiu : i = u <;> simp [genOpStep, mid18StepOp, mid18Get_set s h, hiu]
  | cx a b =>
      by_cases hib : i = b <;> simp only [genOpStep, mid18StepOp, mid18Get_set s h, hib, ↓reduceIte]
  | tand a b d =>
      by_cases hid : i = d <;> simp only [genOpStep, mid18StepOp, mid18Get_set s h, hid, ↓reduceIte]

theorem mid18Steps_eq :
    ∀ (ops : List GenOp), ops.all (genOpWriteOk maskMid18) = true →
      ∀ (s : Mid18St) (i : ℕ), genOpsStep ops (mid18Get s) i = mid18Get (mid18Steps ops s) i
  | [], _, _, _ => rfl
  | op :: rest, hWr, s, i => by
      simp only [List.all_cons, Bool.and_eq_true] at hWr; dsimp only [genOpsStep, mid18Steps];
      rw [sMid18_eq];
      exact (genOpsStep_congr rest (mid18StepOp_eq hWr.1 s) i).trans (mid18Steps_eq rest hWr.2
          (mid18StepOp op s) i)
def mid18OfHiLo (hi lo : ℕ) : Mid18St := sBool (lo.testBit 0) fun b6 ↦ sBool (lo.testBit 1) fun b7 ↦
    sBool (lo.testBit 2) fun b8 ↦ sBool (lo.testBit 3) fun b23 ↦ sBool (lo.testBit 4) fun b24 ↦
    sBool (lo.testBit 5) fun b25 ↦ sBool (lo.testBit 6) fun b52 ↦ sBool (hi.testBit 0) fun b57 ↦
    sBool (hi.testBit 1) fun b58 ↦ sBool (hi.testBit 2) fun b59 ↦ sBool (hi.testBit 3) fun b60 ↦
    sBool (hi.testBit 4) fun b61 ↦ sBool (hi.testBit 5) fun b62 ↦
    .mk b6 b7 b8 b23 b24 b25 b52 b57 b58 b59 b60 b61 b62
theorem mid18Idx_cases (i : ℕ) :
    (i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8 ∧ i ≠ 23 ∧ i ≠ 24 ∧ i ≠ 25 ∧ i ≠ 52 ∧ i ≠ 57 ∧ i ≠ 58 ∧
      i ≠ 59 ∧ i ≠ 60 ∧ i ≠ 61 ∧ i ≠ 62) ∨
    (i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 52 ∨ i = 57 ∨ i = 58 ∨
      i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62) := by omega
theorem mid18Get_ofHiLo (mHi : Fin 64) (mLo : Fin 128) (i : ℕ) :
    modelMid18Any mHi mLo i = mid18Get (mid18OfHiLo mHi.val mLo.val) i := by
  simp only [mid18OfHiLo, sBool_eq, modelMid18Any]
  rcases mid18Idx_cases i with ⟨h6, h7, h8, h23, h24, h25, h52, h57, h58, h59, h60, h61, h62⟩ | h
  · simp only [h6, h7, h8, h23, h24, h25, h52, h57, h58, h59, h60, h61, h62, ↓reduceIte,
      mid18Get_other _ h6 h7 h8 h23 h24 h25 h52 h57 h58 h59 h60 h61 h62]
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem midSubBorrows18_pres_cert (mHi : Fin 64) (mLo : Fin 128) :
    let f := genOpsStepB midSubBorrows18Ops (modelMid18Any mHi mLo)
    f 6 = mLo.val.testBit 0 ∧ f 7 = mLo.val.testBit 1 ∧ f 8 = mLo.val.testBit 2 ∧
    f 23 = mLo.val.testBit 3 ∧ f 24 = mLo.val.testBit 4 ∧ f 25 = mLo.val.testBit 5 ∧
    f 57 = mHi.val.testBit 0 := by
  have hc : allBelow 64 (fun hi ↦ allBelow 128 (fun lo ↦
      let s := mid18Steps midSubBorrows18Ops (mid18OfHiLo hi lo)
      decide (s.b6 = lo.testBit 0 ∧ s.b7 = lo.testBit 1 ∧ s.b8 = lo.testBit 2 ∧
              s.b23 = lo.testBit 3 ∧ s.b24 = lo.testBit 4 ∧ s.b25 = lo.testBit 5 ∧
              s.b57 = hi.testBit 0))) = true := by decide +kernel
  have hStep (k : ℕ) : genOpsStepB midSubBorrows18Ops (modelMid18Any mHi mLo) k =
      mid18Get (mid18Steps midSubBorrows18Ops (mid18OfHiLo mHi.val mLo.val)) k :=
    (genOpsStep_eq_B midSubBorrows18Ops (modelMid18Any mHi mLo) k).symm.trans
      ((genOpsStep_congr midSubBorrows18Ops (mid18Get_ofHiLo mHi mLo) k).trans
        (mid18Steps_eq midSubBorrows18Ops midSubBorrows18Ops_ok.2.1 _ k))
  dsimp only
  rw [hStep 6, hStep 7, hStep 8, hStep 23, hStep 24, hStep 25, hStep 57]
  exact of_decide_eq_true ((allBelow_true_iff 128 _).mp
    ((allBelow_true_iff 64 _).mp hc mHi.val mHi.isLt) mLo.val mLo.isLt)

def modelMid18Clean (a3 : Fin 8) (b6 q01 z4 z2 z3 : Bool) (i : ℕ) : Bool :=
    if i = 6 then a3.val.testBit 0 else if i = 7 then a3.val.testBit 1 else if i =
    8 then a3.val.testBit 2 else if i = 23 then z4 else if i = 24 then z2 else if i =
    25 then z3 else if i = 52 then q01 else if i = 57 then b6 else false
def mid18OfClean (a3 : ℕ) (b6 q01 z4 z2 z3 : Bool) : Mid18St := sBool (a3.testBit 0) fun t0 ↦
    sBool (a3.testBit 1) fun t1 ↦ sBool (a3.testBit 2) fun t2 ↦ sBool z4 fun bz4 ↦
    sBool z2 fun bz2 ↦ sBool z3 fun bz3 ↦ sBool q01 fun bq01 ↦ sBool b6 fun bb6 ↦
    .mk t0 t1 t2 bz4 bz2 bz3 bq01 bb6 false false false false false
theorem mid18Get_ofClean (a3 : Fin 8) (b6 q01 z4 z2 z3 : Bool) (i : ℕ) :
    modelMid18Clean a3 b6 q01 z4 z2 z3 i =
      mid18Get (mid18OfClean a3.val b6 q01 z4 z2 z3) i := by
  simp only [mid18OfClean, sBool_eq, modelMid18Clean]
  rcases mid18Idx_cases i with ⟨h6, h7, h8, h23, h24, h25, h52, h57, h58, h59, h60, h61, h62⟩ | h
  · simp only [h6, h7, h8, h23, h24, h25, h52, h57, ↓reduceIte,
      mid18Get_other _ h6 h7 h8 h23 h24 h25 h52 h57 h58 h59 h60 h61 h62]
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rfl
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem midSubBorrows18_eval_cert (a3 : Fin 8) (b6 q01 z4 z2 z3 : Fin 2) :
    let f :=
        genOpsStepB midSubBorrows18Ops (modelMid18Clean a3 (b6.val == 1) (q01.val == 1)
        (z4.val == 1) (z2.val == 1)
        (z3.val == 1)); let sb := subBorrows18Core a3.val b6.val q01.val z4.val z2.val z3.val
    f 59 = (sb.1 == 1) ∧ f 60 = (sb.2.1 == 1) ∧ f 62 = (sb.2.2 == 1) := by
  have hc : allBelow 8 (fun a ↦ allBelow 2 (fun vb6 ↦ allBelow 2 (fun vq01 ↦
    allBelow 2 (fun vz4 ↦ allBelow 2 (fun vz2 ↦ allBelow 2 (fun vz3 ↦
      let s :=
          mid18Steps midSubBorrows18Ops (mid18OfClean a (vb6 == 1) (vq01 == 1) (vz4 == 1) (vz2 == 1)
          (vz3 == 1)); let sb := subBorrows18Core a vb6 vq01 vz4 vz2 vz3
      decide (s.b59 = (sb.1 == 1) ∧ s.b60 = (sb.2.1 == 1) ∧ s.b62 = (sb.2.2 == 1)))))))) =
          true := by
    decide +kernel
  have hStep : ∀ k, genOpsStepB midSubBorrows18Ops (modelMid18Clean a3 (b6.val == 1) (q01.val == 1)
      (z4.val == 1) (z2.val == 1)
      (z3.val == 1)) k = mid18Get (mid18Steps midSubBorrows18Ops (mid18OfClean a3.val (b6.val == 1)
      (q01.val == 1) (z4.val == 1) (z2.val == 1) (z3.val == 1))) k := fun k ↦
      (genOpsStep_eq_B midSubBorrows18Ops _ k).symm.trans ((genOpsStep_congr midSubBorrows18Ops
      (mid18Get_ofClean a3 (b6.val == 1) (q01.val == 1) (z4.val == 1) (z2.val == 1)
      (z3.val == 1)) k).trans (mid18Steps_eq midSubBorrows18Ops midSubBorrows18Ops_ok.2.1 _ k))
  dsimp only; rw [hStep 59, hStep 60, hStep 62];
  exact of_decide_eq_true ((allBelow_true_iff 2 _).mp ((allBelow_true_iff 2 _).mp
      ((allBelow_true_iff 2 _).mp ((allBelow_true_iff 2 _).mp ((allBelow_true_iff 2 _).mp
      ((allBelow_true_iff 8 _).mp hc a3.val a3.isLt) b6.val b6.isLt) q01.val q01.isLt) z4.val
      z4.isLt) z2.val z2.isLt) z3.val z3.isLt)
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem cmpGenBits_s1_cert :
    ∀ (x : Fin 4) (a : Fin 32) (b0 : Bool),
      cmpGenBits b0 x.val.testBit (fun j ↦ a.val.testBit (3 + j)) 1 =
        decide (x.val < (a.val / 8) % 4 + if b0 then 1 else 0) := by decide +kernel

def packBitsCmp2 (f : ℕ → Bool) : Fin 64 :=
  ⟨(if f 0 then 1 else 0) + 2 * (if f 1 then 1 else 0) +
   4 * (if f 11 then 1 else 0) + 8 * (if f 12 then 1 else 0) +
   16 * (if f 52 then 1 else 0) + 32 * (if f 53 then 1 else 0), by
   split_ifs <;> omega⟩

theorem maskCmp2_mem {j : ℕ} (hj : maskCmp2.testBit j = true) :
    j = 0 ∨ j = 1 ∨ j = 11 ∨ j = 12 ∨ j = 52 ∨ j = 53 := by
  refine (by decide : ∀ k < 96, maskCmp2.testBit k = true →
    k = 0 ∨ k = 1 ∨ k = 11 ∨ k = 12 ∨ k = 52 ∨ k = 53) j (Nat.lt_of_not_ge fun hge ↦ ?_) hj
  exact Bool.false_ne_true ((Nat.testBit_lt_two_pow
    ((by decide : maskCmp2 < 2 ^ 96).trans_le
      (Nat.pow_le_pow_right (by decide) hge))).symm.trans hj)

theorem packBitsCmp2_bits (f : ℕ → Bool) : ∀ j, maskCmp2.testBit j = true → f j =
    modelCmp2Any (packBitsCmp2 f) j := by
  intro j hj
  have hjSet := maskCmp2_mem hj
  rcases hjSet with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (dsimp only [modelCmp2Any, packBitsCmp2]; simp only [↓reduceIte];
     cases f 0 <;> cases f 1 <;> cases f 11 <;> cases f 12 <;> cases f 52 <;> cases f 53 <;> decide)

set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem cmp2JointQ01Tree_eval (st : ℕ) : (∀ i, i ≠ 52 → i ≠ 53 →
    (evalPrimTree 95 st cmp2JointQ01Tree).testBit i = st.testBit i) ∧ (∀ (r6 g6 : Fin 64),
    st.testBit 0 = r6.val.testBit 0 → st.testBit 1 = r6.val.testBit 1 → st.testBit 11 =
    g6.val.testBit 0 → st.testBit 12 = g6.val.testBit 1 → st.testBit 52 = false → st.testBit 53 =
    false → (evalPrimTree 95 st cmp2JointQ01Tree).testBit 52 = (q01OfR6G6 r6.val g6.val == 1) ∧
    (evalPrimTree 95 st cmp2JointQ01Tree).testBit 53 = cmpBits 1 g6.val.testBit r6.val.testBit)
    := by
  dsimp only [cmp2JointQ01Tree]; obtain ⟨hOk, hWr, hLoc⟩ := cmp2JointQ01Ops_ok
  refine ⟨fun i h52 h53 ↦ ?_, fun r6 g6 h0 h1 h11 h12 h52_0 h53_0 ↦ ?_⟩
  · rw [evalPrimTree_genOpsTree cmp2JointQ01Ops hOk st i]
    by_cases hm : maskCmp2.testBit i = true
    · rw [genOpsStep_local cmp2JointQ01Ops hLoc (packBitsCmp2_bits st.testBit) hm,
          genOpsStep_eq_B]
      obtain ⟨c0, c1, c11, c12⟩ := cmp2JointQ01_pres_cert (packBitsCmp2 st.testBit)
      have pk (k : ℕ) (hk : maskCmp2.testBit k = true) := (packBitsCmp2_bits st.testBit k hk).symm
      rcases maskCmp2_mem hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first
        | exact c0.trans (pk 0 (by decide)) | exact c1.trans (pk 1 (by decide))
        | exact c11.trans (pk 11 (by decide)) | exact c12.trans (pk 12 (by decide))
        | omega
    · exact genOpsStep_outside cmp2JointQ01Ops hWr st.testBit (Bool.eq_false_iff.mpr hm)
  · have hMod4 : ∀ x : Fin 64, x.val.testBit 0 = (x.val % 4).testBit 0 ∧
        x.val.testBit 1 = (x.val % 4).testBit 1 := by decide +kernel
    have hMod (j : ℕ) (hj : maskCmp2.testBit j = true) :
        st.testBit j = modelCmp2 ⟨r6.val % 4, by omega⟩ ⟨g6.val % 4, by omega⟩ j := by
      rcases maskCmp2_mem hj with rfl | rfl | rfl | rfl | rfl | rfl <;> first
        | exact h0.trans (hMod4 r6).1 | exact h1.trans (hMod4 r6).2
        | exact h11.trans (hMod4 g6).1 | exact h12.trans (hMod4 g6).2
        | assumption
    have ev (k : ℕ) (hk : maskCmp2.testBit k = true) :=
      (evalPrimTree_genOpsTree cmp2JointQ01Ops hOk st k).trans
        ((genOpsStep_local cmp2JointQ01Ops hLoc hMod hk).trans (genOpsStep_eq_B _ _ k))
    exact ⟨(ev 52 (by decide)).trans (cmp2JointQ01_eval_cert r6 g6).1,
      (ev 53 (by decide)).trans (cmp2JointQ01_eval_cert r6 g6).2⟩

def packBitsMid18Lo (f : ℕ → Bool) : Fin 128 :=
  ⟨(if f 6 then 1 else 0) + 2 * (if f 7 then 1 else 0) + 4 * (if f 8 then 1 else 0) +
   8 * (if f 23 then 1 else 0) + 16 * (if f 24 then 1 else 0) + 32 * (if f 25 then 1 else 0) +
   64 * (if f 52 then 1 else 0), by split_ifs <;> omega⟩

def packBitsMid18Hi (f : ℕ → Bool) : Fin 64 :=
  ⟨(if f 57 then 1 else 0) + 2 * (if f 58 then 1 else 0) +
   4 * (if f 59 then 1 else 0) + 8 * (if f 60 then 1 else 0) + 16 * (if f 61 then 1 else 0) +
   32 * (if f 62 then 1 else 0), by split_ifs <;> omega⟩

set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem packBitsMid18Lo_bits_cert :
    ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool),
      let v :=
          (if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) + 4 * (if b2 then 1 else 0) + 8 *
          (if b3 then 1 else 0) + 16 * (if b4 then 1 else 0) + 32 * (if b5 then 1 else 0) + 64 *
          (if b6 then 1 else 0)
      v.testBit 0 = b0 ∧ v.testBit 1 = b1 ∧ v.testBit 2 = b2 ∧ v.testBit 3 = b3 ∧
      v.testBit 4 = b4 ∧ v.testBit 5 = b5 ∧ v.testBit 6 = b6 := by decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem packBitsMid18Hi_bits_cert :
    ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      let v :=
          (if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) + 4 * (if b2 then 1 else 0) + 8 *
          (if b3 then 1 else 0) + 16 * (if b4 then 1 else 0) + 32 * (if b5 then 1 else 0)
      v.testBit 0 = b0 ∧ v.testBit 1 = b1 ∧ v.testBit 2 = b2 ∧
      v.testBit 3 = b3 ∧ v.testBit 4 = b4 ∧ v.testBit 5 = b5 := by decide +kernel

theorem packBitsMid18_bits (f : ℕ → Bool) : ∀ j, maskMid18.testBit j = true → f j =
    modelMid18Any (packBitsMid18Hi f) (packBitsMid18Lo f) j := by
  intro j hj
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ :=
    packBitsMid18Lo_bits_cert (f 6) (f 7) (f 8) (f 23) (f 24) (f 25) (f 52)
  obtain ⟨e7, e8, e9, e10, e11, e12⟩ :=
    packBitsMid18Hi_bits_cert (f 57) (f 58) (f 59) (f 60) (f 61) (f 62)
  rcases maskMid18_mem hj with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only [modelMid18Any, packBitsMid18Lo, packBitsMid18Hi] <;> simp only [↓reduceIte] <;>
    exact Eq.symm (by assumption)

theorem popCount3Tree18_eval (st : ℕ) :
    (∀ i, i ≠ 64 → i ≠ 66 → i ≠ 68 → i ≠ 69 →
      (evalPrimTree 95 st popCount3Tree18).testBit i = st.testBit i) ∧
    (st.testBit 69 = false →
      let sum3 :=
          (if st.testBit 64 then 1 else 0) + (if st.testBit 66 then 1 else 0) +
          (if st.testBit 68 then 1 else 0)
      (evalPrimTree 95 st popCount3Tree18).testBit 64 = sum3.testBit 0 ∧
      (evalPrimTree 95 st popCount3Tree18).testBit 69 = sum3.testBit 1) := by
  dsimp only [popCount3Tree18]
  refine ⟨fun i h64 h66 h68 h69 ↦ ?_, fun h69_0 ↦ ?_⟩
  · rw [evalPrimTree_genOpsTree popCount3Ops18 popCount3Ops18_ok.1 st i]
    dsimp only [popCount3Ops18, genOpsStep, genOpStep]
    simp only [h64, h66, h69, ↓reduceIte]
  · rw [evalPrimTree_genOpsTree popCount3Ops18 popCount3Ops18_ok.1 st 64,
        evalPrimTree_genOpsTree popCount3Ops18 popCount3Ops18_ok.1 st 69]
    dsimp only [popCount3Ops18, genOpsStep, genOpStep]
    simp only [↓reduceIte, h69_0]
    cases st.testBit 64 <;> cases st.testBit 66 <;> cases st.testBit 68 <;> decide

set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem midSubBorrows18K2Tree_eval (st : ℕ) :
    (∀ i, (i < 52 ∨ i = 57 ∨ 63 ≤ i) →
      (evalPrimTree 95 st midSubBorrows18Tree).testBit i = st.testBit i) ∧
    (∀ (a5 : Fin 32) (b6 q01 z4 z2 z3 : Fin 2),
      st.testBit 6 = a5.val.testBit 0 →
      st.testBit 7 = a5.val.testBit 1 →
      st.testBit 8 = a5.val.testBit 2 →
      st.testBit 23 = (z4.val == 1) →
      st.testBit 24 = (z2.val == 1) →
      st.testBit 25 = (z3.val == 1) →
      st.testBit 52 = (q01.val == 1) →
      st.testBit 57 = (b6.val == 1) →
      (∀ k, 58 ≤ k → k < 63 → st.testBit k = false) →
      let sb := subBorrows18Core (a5.val % 8) b6.val q01.val z4.val z2.val z3.val
      (evalPrimTree 95 st midSubBorrows18Tree).testBit 59 = (sb.1 == 1) ∧
      (evalPrimTree 95 st midSubBorrows18Tree).testBit 60 = (sb.2.1 == 1) ∧
      (evalPrimTree 95 st midSubBorrows18Tree).testBit 62 = (sb.2.2 == 1)) := by
  dsimp only [midSubBorrows18Tree]; obtain ⟨hOk, hWr, hLoc⟩ := midSubBorrows18Ops_ok
  refine ⟨fun i hi ↦ ?_, fun a5 b6 q01 z4 z2 z3 h6 h7 h8 h23 h24 h25 h52 h57 hCln ↦ ?_⟩
  · rw [evalPrimTree_genOpsTree midSubBorrows18Ops hOk st i]
    by_cases hm : maskMid18.testBit i = true
    · rw [genOpsStep_local midSubBorrows18Ops hLoc (packBitsMid18_bits st.testBit) hm,
          genOpsStep_eq_B]
      obtain ⟨c6, c7, c8, c23, c24, c25, c57⟩ :=
        midSubBorrows18_pres_cert (packBitsMid18Hi st.testBit) (packBitsMid18Lo st.testBit)
      have pk (k : ℕ) (hk : maskMid18.testBit k = true) :=
        (packBitsMid18_bits st.testBit k hk).symm
      have h13 := maskMid18_mem hm
      rcases (by omega : i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 57) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [c6.trans (pk 6 (by decide)), c7.trans (pk 7 (by decide)), c8.trans (pk 8 (by decide)),
        c23.trans (pk 23 (by decide)), c24.trans (pk 24 (by decide)), c25.trans (pk 25 (by decide)),
        c57.trans (pk 57 (by decide))]
    · exact genOpsStep_outside midSubBorrows18Ops hWr st.testBit (Bool.eq_false_iff.mpr hm)
  · have hMod8 : ∀ x : Fin 32, x.val.testBit 0 = (x.val % 8).testBit 0 ∧
        x.val.testBit 1 = (x.val % 8).testBit 1 ∧ x.val.testBit 2 = (x.val % 8).testBit 2 := by
      decide +kernel
    have hMod : ∀ j, maskMid18.testBit j = true →
        st.testBit j = modelMid18Clean ⟨a5.val % 8, by omega⟩ (b6.val == 1) (q01.val == 1)
          (z4.val == 1) (z2.val == 1) (z3.val == 1) j := fun j hj ↦ by
      rcases maskMid18_mem hj with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
        | exact h6.trans (hMod8 a5).1 | exact h7.trans (hMod8 a5).2.1
        | exact h8.trans (hMod8 a5).2.2 | assumption | exact hCln _ (by omega) (by omega)
    obtain ⟨e59, e60, e62⟩ := midSubBorrows18_eval_cert ⟨a5.val % 8, by omega⟩ b6 q01 z4 z2 z3
    have ev : ∀ k, maskMid18.testBit k = true →
        (evalPrimTree 95 st (genOpsTree midSubBorrows18Ops)).testBit k =
          genOpsStepB midSubBorrows18Ops (modelMid18Clean ⟨a5.val % 8, by omega⟩
            (b6.val == 1) (q01.val == 1) (z4.val == 1) (z2.val == 1) (z3.val == 1)) k :=
      fun k hk ↦ (evalPrimTree_genOpsTree midSubBorrows18Ops hOk st k).trans
        ((genOpsStep_local midSubBorrows18Ops hLoc hMod hk).trans
          (genOpsStep_eq_B midSubBorrows18Ops _ k))
    exact ⟨(ev 59 (by decide)).trans e59, (ev 60 (by decide)).trans e60,
      (ev 62 (by decide)).trans e62⟩

def flipsG6Ops : List (Bool × ℕ × ℕ) := [(false, 11, 0), (false, 13, 0), (false, 15, 0)]
theorem flipsG6Ops_ok : flipsG6Ops.all linOpOk = true := by decide

def flipsG6Tree : PrimTree := linOpsTree flipsG6Ops

theorem flipsG6Ops_self_inv (f : ℕ → Bool)
    (i : ℕ) : linOpsStep flipsG6Ops (linOpsStep flipsG6Ops f) i = f i := by
  dsimp only [flipsG6Ops, linOpsStep, linOpStep]
  cases decide (i = 11) <;> cases decide (i = 13) <;> cases decide (i = 15) <;> cases f i <;> rfl

theorem flipsG6Ops_outside17 (f : ℕ → Bool) (i : ℕ) (hi : i < 11 ∨ 17 ≤ i) :
    linOpsStep flipsG6Ops f i = f i := by
  dsimp only [flipsG6Ops, linOpsStep, linOpStep]
  rw [decide_eq_false (by omega), decide_eq_false (by omega), decide_eq_false (by omega)]
  simp only [Bool.xor_false]
def slotG6Model (w : Fin 2048) (i : ℕ) : Bool :=
    if 11 ≤ i ∧ i < 17 then w.val.testBit (21 - i) else false
def slotG6ModelNat (w i : ℕ) : Bool := if 11 ≤ i ∧ i < 17 then w.testBit (21 - i) else false
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem flipsG6_gam6_cert : ∀ (w : Fin 2048) (j : Fin 6), linOpsStepB flipsG6Ops (slotG6Model w)
    (11 + j.val) = (clbGam6 w.val).testBit j.val := by
  have hc : allBelow 2048 (fun w ↦ allBelow 6 (fun j ↦
      decide (linOpsStepB flipsG6Ops (slotG6ModelNat w) (11 + j) = xor (w.testBit (10 - j))
      (decide (j = 0 ∨ j = 2 ∨ j = 4))))) = true := by decide +kernel
  intro w j;
  have hj :=
      of_decide_eq_true ((allBelow_true_iff 6 _).mp ((allBelow_true_iff 2048 _).mp hc w.val w.isLt)
      j.val j.isLt); exact hj.trans (SubCoin63.clbGam6_bit_eq w j.isLt).symm
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem o9_bits_cert (o9 : Fin 512) : (o9.val % 4).testBit 0 = o9.val.testBit 0 ∧
    (o9.val % 4).testBit 1 = o9.val.testBit 1 ∧ ((o9.val / 4) % 4).testBit 0 = o9.val.testBit 2 ∧
    ((o9.val / 4) % 4).testBit 1 = o9.val.testBit 3 ∧ ((o9.val / 16) % 4).testBit 0 =
    o9.val.testBit 4 ∧ ((o9.val / 16) % 4).testBit 1 = o9.val.testBit 5 ∧
    (((o9.val / 64) % 2) == 1) = o9.val.testBit 6 ∧ (((o9.val / 128) % 2) == 1) = o9.val.testBit 7 ∧
    (((o9.val / 256) % 2) == 1) = o9.val.testBit 8 := by
  have hc : allBelow 512 (fun v ↦ decide ( (v % 4).testBit 0 = v.testBit 0 ∧
    (v % 4).testBit 1 = v.testBit 1 ∧ ((v / 4) % 4).testBit 0 = v.testBit 2 ∧
    ((v / 4) % 4).testBit 1 = v.testBit 3 ∧ ((v / 16) % 4).testBit 0 = v.testBit 4 ∧
    ((v / 16) % 4).testBit 1 = v.testBit 5 ∧ (((v / 64) % 2) == 1) = v.testBit 6 ∧
    (((v / 128) % 2) == 1) = v.testBit 7 ∧
    (((v / 256) % 2) == 1) = v.testBit 8)) = true := by decide +kernel
  exact of_decide_eq_true ((allBelow_true_iff 512 _).mp hc o9.val o9.isLt)

def coul18K2CoreTree : PrimTree :=
    .node flipsG6Tree (.node (.node (.node cmp2JointQ01Tree (.node (.node (cmpBorrowStep 13 2 53 54)
    (cmpBorrowStep 14 3 54 55)) (.node (cmpBorrowStep 15 4 55 56)
    (cmpBorrowStep 16 5 56 57)))) midSubBorrows18Tree) (.node (.node (cmpSuffixGen 17 9 59 63 1)
    (.node (cmpSuffixGen 19 9 60 65 1) (cmpSuffixGen 21 9 62 67 1)))
    (.node popCount3Tree18 flipsG6Tree)))
theorem coul18K2CoreTree_pres_nonMask (st i : ℕ) (hM : coul18K2SMask.testBit i = false) :
    (evalPrimTree 95 st coul18K2CoreTree).testBit i = st.testBit i := by
  have hiRange : i < 52 ∨ 70 ≤ i := by
    by_contra hc
    exact Bool.false_ne_true (hM.symm.trans
      ((by decide : ∀ k < 70, 52 ≤ k → coul18K2SMask.testBit k = true) i (by omega) (by omega)))
  dsimp only [coul18K2CoreTree, flipsG6Tree, evalPrimTree]
  set sP1 := evalPrimTree 95 st (linOpsTree flipsG6Ops)
  set sA := evalPrimTree 95 (evalPrimTree 95 (evalPrimTree 95 (evalPrimTree 95
    (evalPrimTree 95 sP1 cmp2JointQ01Tree) (cmpBorrowStep 13 2 53 54))
    (cmpBorrowStep 14 3 54 55)) (cmpBorrowStep 15 4 55 56)) (cmpBorrowStep 16 5 56 57)
  set sPC := evalPrimTree 95 (evalPrimTree 95 (evalPrimTree 95 (evalPrimTree 95
    (evalPrimTree 95 sA midSubBorrows18Tree) (cmpSuffixGen 17 9 59 63 1))
    (cmpSuffixGen 19 9 60 65 1)) (cmpSuffixGen 21 9 62 67 1)) popCount3Tree18
  have hMid (j : ℕ) (hj : j < 52 ∨ 70 ≤ j) : sPC.testBit j = sP1.testBit j := by
    have hB (c t pr ds s : ℕ) (h : 11 ≤ c ∧ c < 32 ∧ t < 11 ∧ 52 ≤ pr ∧ pr ≠ t ∧ pr < ds ∧
        52 ≤ ds ∧ ds < 70 := by decide) := (cmpBorrowStep_eval_gen (c := c) (t := t) (prev := pr)
      (dst := ds) h.1 h.2.1 h.2.2.1 (.inr h.2.2.2.1) h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
      (Nat.lt_trans h.2.2.2.2.2.2.2 (by decide)) s).1 j (by omega)
    have hS (cH bI oH s : ℕ) (h : 17 ≤ cH ∧ 52 ≤ bI ∧ bI < oH ∧ bI ≠ 9 ∧ 58 ≤ oH ∧
        cH + 1 < 32 ∧ oH + 1 < 70 := by decide) := (cmpSuffixGen_eval (cHi := cH) (t0 := 9)
      (bInit := bI) (outHi := oH) h.1 (.inr h.2.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 1
      h.2.2.2.2.2.1 (by decide) (Nat.lt_trans h.2.2.2.2.2.2 (by decide)) s).1 j (by omega)
    dsimp only [sPC, sA]
    rw [(popCount3Tree18_eval _).1 j (by omega) (by omega) (by omega) (by omega),
      hS 21 62 67 _, hS 19 60 65 _, hS 17 59 63 _, (midSubBorrows18K2Tree_eval _).1 j (by omega),
      hB 16 5 56 57 _, hB 15 4 55 56 _, hB 14 3 54 55 _, hB 13 2 53 54 _,
      (cmp2JointQ01Tree_eval sP1).1 j (by omega) (by omega)]
  rw [evalPrimTree_linOpsTree flipsG6Ops flipsG6Ops_ok sPC i]
  by_cases hCoin : 11 ≤ i ∧ i < 32
  · exact (linOpsStep_coin_local flipsG6Ops flipsG6Ops_ok
      (fun j _ hj1 ↦ (hMid j (.inl (by omega))).trans
        (evalPrimTree_linOpsTree flipsG6Ops flipsG6Ops_ok st j))
      i hCoin.1 hCoin.2).trans (flipsG6Ops_self_inv st.testBit i)
  · have hOut : i < 11 ∨ 32 ≤ i := by omega
    rw [linOpsStep_outside flipsG6Ops flipsG6Ops_ok sPC.testBit i hOut, hMid i hiRange,
                                        evalPrimTree_linOpsTree flipsG6Ops flipsG6Ops_ok st i,
                                        linOpsStep_outside flipsG6Ops flipsG6Ops_ok st.testBit i
                                        hOut]

set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem coul18K2CoreTree_eval_j (st t11 : ℕ) (ht11 : t11 < 2048) (w : Fin 2048) (o9 : Fin 512)
    (hT : ∀ b < 11, st.testBit b = t11.testBit b) (hG : ∀ j : Fin 6, st.testBit (11 + j.val) =
    w.val.testBit (10 - j.val)) (hO : ∀ q : Fin 9, st.testBit (17 + q.val) = o9.val.testBit q.val)
    (hCln : ∀ i, coul18K2SMask.testBit i = true → st.testBit i = false) :
    (evalPrimTree 95 st coul18K2CoreTree).testBit 64 = (popBernJK2 t11 w o9).testBit 0 ∧
    (evalPrimTree 95 st coul18K2CoreTree).testBit 69 = (popBernJK2 t11 w o9).testBit 1 := by
  have hmIn : ∀ k < 70, 52 ≤ k → coul18K2SMask.testBit k = true := by decide
  dsimp only [coul18K2CoreTree, flipsG6Tree, evalPrimTree]
  set sP1 := evalPrimTree 95 st (linOpsTree flipsG6Ops)
  have hsP1_lo : ∀ b < 11, sP1.testBit b = t11.testBit b := fun b hb ↦ by
    rw [evalPrimTree_linOpsTree flipsG6Ops flipsG6Ops_ok st b,
        flipsG6Ops_outside17 st.testBit b (Or.inl hb), hT b hb]
  have hsP1_cln : ∀ i, 52 ≤ i → i < 70 → sP1.testBit i = false := fun i h0 h1 ↦ by
    rw [evalPrimTree_linOpsTree flipsG6Ops flipsG6Ops_ok st i,
        flipsG6Ops_outside17 st.testBit i (Or.inr (by omega)), hCln i (hmIn i h1 h0)]
  have hsP1_g6 (j : Fin 6) : sP1.testBit (11 + j.val) = (clbGam6 w.val).testBit j.val := by
    rw [evalPrimTree_linOpsTree flipsG6Ops flipsG6Ops_ok st (11 + j.val),
      show linOpsStep flipsG6Ops st.testBit (11 + j.val) =
        linOpsStep flipsG6Ops (slotG6Model w) (11 + j.val) by
        simp only [flipsG6Ops, linOpsStep, linOpStep, slotG6Model,
          itePos (by omega : 11 ≤ 11 + j.val ∧ 11 + j.val < 17),
          show 21 - (11 + j.val) = 10 - j.val by omega, hG j],
      linOpsStep_eq_B]
    exact flipsG6_gam6_cert w j
  have hsP1_o9 : ∀ q : Fin 9, sP1.testBit (17 + q.val) = o9.val.testBit q.val := fun q ↦ by
    rw [evalPrimTree_linOpsTree flipsG6Ops flipsG6Ops_ok st (17 + q.val),
        flipsG6Ops_outside17 st.testBit (17 + q.val) (Or.inr (by omega)), hO q]
  obtain ⟨ob0, ob1, ob2, ob3, ob4, ob5, ob6, ob7, ob8⟩ := o9_bits_cert o9; obtain ⟨hT6, hTA, _⟩ :=
      t11_bits_split ⟨t11, ht11⟩; dsimp only at hT6 hTA
  set a5 := t11 / 64
  set r6 := t11 % 64
  have haLt : a5 < 32 := by omega
  have hr6Lt : r6 < 64 := by omega
  have hg6Lt : clbGam6 w.val < 64 := clbGam6_lt w.val
  set sC0 := evalPrimTree 95 sP1 cmp2JointQ01Tree
  obtain ⟨hpC0, hvC0_raw⟩ := cmp2JointQ01Tree_eval sP1
  obtain ⟨hv52_0, hv53_0⟩ := hvC0_raw ⟨r6, hr6Lt⟩ ⟨clbGam6 w.val, hg6Lt⟩
    ((hsP1_lo 0 (by omega)).trans (hT6 0)) ((hsP1_lo 1 (by omega)).trans (hT6 1))
    (hsP1_g6 0) (hsP1_g6 1) (hsP1_cln 52 (by omega) (by omega)) (hsP1_cln 53 (by omega) (by omega))
  have hBrwStep {k stIn : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
      (hPres : ∀ i, (i < 54 ∨ 53 + k ≤ i) → stIn.testBit i = sC0.testBit i)
      (hPrev : stIn.testBit (52 + k) = cmpBits k (clbGam6 w.val).testBit r6.testBit) :
      let stOut := evalPrimTree 95 stIn (cmpBorrowStep (12 + k) (1 + k) (52 + k) (53 + k))
      (∀ i, (i < 54 ∨ 54 + k ≤ i) → stOut.testBit i = sC0.testBit i) ∧
      stOut.testBit (53 + k) = cmpBits (k + 1) (clbGam6 w.val).testBit r6.testBit := by
    obtain ⟨hp, hv⟩ := cmpBorrowStep_eval_gen (c := 12 + k) (t := 1 + k)
      (prev := 52 + k) (dst := 53 + k) (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (by omega) (by omega) (by omega) (by omega) stIn
    refine ⟨fun i hi ↦ (hp i (by omega)).trans (hPres i (by omega)), ?_⟩
    rw [hv ((hPres (53 + k) (Or.inr le_rfl)).trans
          ((hpC0 _ (by omega) (by omega)).trans (hsP1_cln _ (by omega) (by omega)))),
        hPres (12 + k) (Or.inl (by omega)), hpC0 _ (by omega) (by omega),
        show sP1.testBit (12 + k) = (clbGam6 w.val).testBit (1 + k) from
          (congrArg sP1.testBit (by omega : 12 + k = 11 + (1 + k))).trans
            (hsP1_g6 ⟨1 + k, by omega⟩),
        hPres (1 + k) (Or.inl (by omega)), hpC0 _ (by omega) (by omega),
        hsP1_lo (1 + k) (by omega),
        show t11.testBit (1 + k) = r6.testBit (1 + k) from hT6 ⟨1 + k, by omega⟩, hPrev,
        Nat.add_comm 1 k]
    rfl
  obtain ⟨hP1, hsC1_54⟩ := hBrwStep (k := 1) (by omega) (by omega) (fun _ _ ↦ rfl) hv53_0
  obtain ⟨hP2, hsC2_55⟩ := hBrwStep (k := 2) (by omega) (by omega) hP1 hsC1_54
  obtain ⟨hP3, hsC3_56⟩ := hBrwStep (k := 3) (by omega) (by omega) hP2 hsC2_55
  obtain ⟨hsA_non54_57, hsA_cmp5⟩ := hBrwStep (k := 4) (by omega) (by omega) hP3 hsC3_56
  set sA := evalPrimTree 95 (evalPrimTree 95 (evalPrimTree 95 (evalPrimTree 95 sC0
      (cmpBorrowStep 13 2 53 54)) (cmpBorrowStep 14 3 54 55))
    (cmpBorrowStep 15 4 55 56)) (cmpBorrowStep 16 5 56 57)
  have hsA_non52_57 (i : ℕ) (hi : i < 52 ∨ 58 ≤ i) : sA.testBit i = sP1.testBit i :=
    (hsA_non54_57 i (by omega)).trans (hpC0 i (by omega) (by omega))
  have hsA_lo (i : ℕ) (hi : i < 52) : sA.testBit i = sP1.testBit i := hsA_non52_57 i (.inl hi)
  have hsA_52 : sA.testBit 52 = (q01OfR6G6 r6 (clbGam6 w.val) == 1) :=
    (hsA_non54_57 52 (Or.inl (by omega))).trans hv52_0
  have hsA_57 : sA.testBit 57 = decide (clbGam6 w.val < r6) := by
    rw [hsA_cmp5, cmpBits_eq_decide_lt 5 (clbGam6 w.val) r6,
        show (2 : ℕ) ^ (5 + 1) = 64 from rfl, Nat.mod_eq_of_lt hg6Lt, Nat.mod_eq_of_lt hr6Lt]
  have hq01Lt : q01OfR6G6 r6 (clbGam6 w.val) < 2 := by
    unfold q01OfR6G6 bandNat; split_ifs <;> omega
  set b6Nat := if clbGam6 w.val < r6 then 1 else 0
  have hb6Lt : b6Nat < 2 := by dsimp only [b6Nat]; split_ifs <;> omega
  have hb6Eq : decide (clbGam6 w.val < r6) = (b6Nat == 1) := by
    by_cases h : clbGam6 w.val < r6 <;> simp [b6Nat, h]
  set sM := evalPrimTree 95 sA midSubBorrows18Tree
  obtain ⟨hpM, hvM_raw⟩ := midSubBorrows18K2Tree_eval sA
  obtain ⟨hsM_59, hsM_60, hsM_62⟩ := hvM_raw ⟨a5, haLt⟩ ⟨b6Nat, hb6Lt⟩ ⟨_, hq01Lt⟩
    ⟨(o9.val / 64) % 2, by omega⟩ ⟨(o9.val / 128) % 2, by omega⟩ ⟨(o9.val / 256) % 2, by omega⟩
    ((hsA_lo 6 (by omega)).trans ((hsP1_lo 6 (by omega)).trans (hTA 0)))
    ((hsA_lo 7 (by omega)).trans ((hsP1_lo 7 (by omega)).trans (hTA 1)))
    ((hsA_lo 8 (by omega)).trans ((hsP1_lo 8 (by omega)).trans (hTA 2)))
    ((hsA_lo 23 (by omega)).trans ((hsP1_o9 6).trans ob6.symm))
    ((hsA_lo 24 (by omega)).trans ((hsP1_o9 7).trans ob7.symm))
    ((hsA_lo 25 (by omega)).trans ((hsP1_o9 8).trans ob8.symm)) hsA_52 (hsA_57.trans hb6Eq)
    (fun k hk0 hk1 ↦ (hsA_non52_57 k (.inr (by omega))).trans (hsP1_cln k (by omega) (by omega)))
  have hSufE (cH bI oH st0 : ℕ) (h : 17 ≤ cH ∧ 52 ≤ bI ∧ bI < oH ∧ bI ≠ 9 ∧ 58 ≤ oH ∧
      cH + 1 < 32 ∧ oH + 1 < 70 := by decide) :=
    cmpSuffixGen_eval (cHi := cH) (t0 := 9) (bInit := bI) (outHi := oH)
      h.1 (.inr h.2.1) h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 1 h.2.2.2.2.2.1 (by decide) (by omega) st0
  set sB0 := evalPrimTree 95 sM (cmpSuffixGen 17 9 59 63 1)
  obtain ⟨hpB0, hvB0⟩ := hSufE 17 59 63 sM
  set sB1 := evalPrimTree 95 sB0 (cmpSuffixGen 19 9 60 65 1)
  obtain ⟨hpB1, hvB1⟩ := hSufE 19 60 65 sB0
  set sB2 := evalPrimTree 95 sB1 (cmpSuffixGen 21 9 62 67 1)
  obtain ⟨hpB2, hvB2⟩ := hSufE 21 62 67 sB1
  have hM_P1 (i : ℕ) (hi : i < 52 ∨ 63 ≤ i) : sM.testBit i = sP1.testBit i :=
    (hpM i (hi.imp id Or.inr)).trans (hsA_non52_57 i (by omega))
  have hB0_P1 (i : ℕ) (hi : i < 52 ∨ 65 ≤ i) : sB0.testBit i = sP1.testBit i :=
    (hpB0 i (by omega)).trans (hM_P1 i (by omega))
  have hB1_P1 (i : ℕ) (hi : i < 52 ∨ 67 ≤ i) : sB1.testBit i = sP1.testBit i :=
    (hpB1 i (by omega)).trans (hB0_P1 i (by omega))
  set sb := subBorrows18Core (a5 % 8) b6Nat (q01OfR6G6 r6 (clbGam6 w.val))
    ((o9.val / 64) % 2) ((o9.val / 128) % 2) ((o9.val / 256) % 2)
  have hsbLt : sb.1 < 2 ∧ sb.2.1 < 2 ∧ sb.2.2 < 2 :=
    (by decide +kernel : ∀ (a3 : Fin 8) (b6 q01 z4 z2 z3 : Fin 2),
      let c := subBorrows18Core a3.val b6.val q01.val z4.val z2.val z3.val
      c.1 < 2 ∧ c.2.1 < 2 ∧ c.2.2 < 2) ⟨a5 % 8, by omega⟩ ⟨b6Nat, hb6Lt⟩ ⟨_, hq01Lt⟩
      ⟨(o9.val / 64) % 2, by omega⟩ ⟨(o9.val / 128) % 2, by omega⟩ ⟨(o9.val / 256) % 2, by omega⟩
  have hxBit (c : ℕ) {x : ℕ} (e0 : sP1.testBit c = x.testBit 0)
      (e1 : sP1.testBit (c + 1) = x.testBit 1) : ∀ j ≤ 1, sP1.testBit (c + j) = x.testBit j := by
    rintro (_ | _ | _) _ <;> first | exact e0 | exact e1 | omega
  have hTA9 (j : ℕ) (hj : j ≤ 1) : sP1.testBit (9 + j) = a5.testBit (3 + j) :=
    (hsP1_lo (9 + j) (by omega)).trans
      ((congrArg t11.testBit (by omega : 9 + j = 6 + (3 + j))).trans (hTA ⟨3 + j, by omega⟩))
  have hSufBit {cH bI oH stIn x bVal : ℕ} (hx : x < 4) (hbLt : bVal < 2) (hoH : 63 ≤ oH ∧ oH ≤ 67)
      (hvS : (∀ j ≤ 1, stIn.testBit (oH + j) = false) →
        (evalPrimTree 95 stIn (cmpSuffixGen cH 9 bI oH 1)).testBit (oH + 1) =
          cmpGenBits (stIn.testBit bI) (fun j ↦ stIn.testBit (cH + j))
            (fun j ↦ stIn.testBit (9 + j)) 1)
      (hP1 : ∀ i, (i < 52 ∨ oH ≤ i) → stIn.testBit i = sP1.testBit i)
      (hcH : cH < 30) (hbI : stIn.testBit bI = (bVal == 1))
      (hxB : ∀ j ≤ 1, sP1.testBit (cH + j) = x.testBit j) :
      (evalPrimTree 95 stIn (cmpSuffixGen cH 9 bI oH 1)).testBit (oH + 1) =
        decide (x < (a5 / 8) % 4 + bVal) := by
    rw [hvS fun j hj ↦ (hP1 _ (by omega)).trans (hsP1_cln _ (by omega) (by omega)), hbI,
      cmpGenBits_congr (bVal == 1) 1 (fun j hj ↦ (hP1 _ (by omega)).trans (hxB j hj))
        (fun j hj ↦ (hP1 _ (by omega)).trans (hTA9 j hj)),
      cmpGenBits_s1_cert ⟨x, hx⟩ ⟨a5, haLt⟩ (bVal == 1),
      show (if bVal == 1 then 1 else 0) = bVal by
        rcases (by omega : bVal = 0 ∨ bVal = 1) with rfl | rfl <;> rfl]
  have hb64 := (hpB2 64 (by omega)).trans ((hpB1 64 (by omega)).trans
    (hSufBit (by omega) hsbLt.1 ⟨by omega, by omega⟩ hvB0 hM_P1 (by omega) hsM_59
      (hxBit 17 ((hsP1_o9 0).trans ob0.symm) ((hsP1_o9 1).trans ob1.symm))))
  have hb66 := (hpB2 66 (by omega)).trans (hSufBit (by omega) hsbLt.2.1 ⟨by omega, by omega⟩
    hvB1 hB0_P1 (by omega) ((hpB0 60 (by omega)).trans hsM_60)
    (hxBit 19 ((hsP1_o9 2).trans ob2.symm) ((hsP1_o9 3).trans ob3.symm)))
  have hb68 := hSufBit (by omega) hsbLt.2.2 ⟨by omega, by omega⟩ hvB2 hB1_P1 (by omega)
    ((hpB1 62 (by omega)).trans ((hpB0 62 (by omega)).trans hsM_62))
    (hxBit 21 ((hsP1_o9 4).trans ob4.symm) ((hsP1_o9 5).trans ob5.symm))
  have hsB2_69 : sB2.testBit 69 = false := (hpB2 69 (by omega)).trans
    ((hB1_P1 69 (by omega)).trans (hsP1_cln 69 (by omega) (by omega)))
  obtain ⟨hpc64, hpc69⟩ := (popCount3Tree18_eval sB2).2 hsB2_69
  rw [hb64, hb66, hb68, show (if decide (o9.val % 4 < (a5 / 8) % 4 + sb.1) = true then 1 else 0) +
      (if decide ((o9.val / 4) % 4 < (a5 / 8) % 4 + sb.2.1) = true then 1 else 0) +
      (if decide ((o9.val / 16) % 4 < (a5 / 8) % 4 + sb.2.2) = true then 1 else 0) =
      popBernJK2 t11 w o9 by unfold popBernJK2; simp only [decide_eq_true_eq]; rfl]
    at hpc64 hpc69
  set sPC := evalPrimTree 95 sB2 popCount3Tree18
  have hOut (k : ℕ) (hk : 17 ≤ k) := (evalPrimTree_linOpsTree flipsG6Ops flipsG6Ops_ok sPC k).trans
    (flipsG6Ops_outside17 sPC.testBit k (Or.inr hk))
  exact ⟨(hOut 64 (by omega)).trans hpc64, (hOut 69 (by omega)).trans hpc69⟩

def coul18K2OutIdx2 : Fin 2 → Fin 18
  | ⟨0, _⟩ => ⟨12, by decide⟩
  | ⟨_ + 1, _⟩ => ⟨17, by decide⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem coul18K2OutIdx2_0 : coul18K2OutIdx2 ⟨0, by omega⟩ = ⟨12, by omega⟩ := rfl
theorem coul18K2OutIdx2_1 : coul18K2OutIdx2 ⟨1, by omega⟩ = ⟨17, by omega⟩ := rfl
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem coul18K2OutIdx2_inj : Function.Injective coul18K2OutIdx2 := by decide +kernel

open PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremCsa36Kick (CT getCT)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ShortBin7 (mkCT getCT_mkCT repMask
    repMask_testBit coordCol coordCol_testBit evalCTW evalCTW_sound)
def whiten13Tree : PrimTree :=
    (.node (.node (.node (.node (.node (.node (.leaf 20525) (.leaf 16429)) (.node (.leaf 14381)
    (.node (.leaf 12333) (.leaf 10285)))) (.node (.node (.leaf 4141) (.node (.leaf 24617)
    (.leaf 18473))) (.node (.leaf 8233) (.node (.leaf 22569) (.leaf 20525)))))
    (.node (.node (.node (.leaf 22569) (.leaf 22565)) (.node (.leaf 16421) (.node (.leaf 14373)
    (.leaf 10277)))) (.node (.node (.leaf 8229) (.node (.leaf 6181) (.leaf 20517)))
    (.node (.leaf 18473) (.node (.leaf 20517) (.leaf 20513))))))
    (.node (.node (.node (.node (.leaf 18465) (.leaf 12321)) (.node (.leaf 10273)
    (.node (.leaf 6177) (.leaf 4129)))) (.node (.node (.leaf 20509) (.node (.leaf 18461)
    (.leaf 10269))) (.node (.leaf 6173) (.node (.leaf 4125) (.leaf 2077)))))
    (.node (.node (.node (.leaf 16413) (.leaf 14369)) (.node (.leaf 16413) (.node (.leaf 24601)
    (.leaf 20505)))) (.node (.node (.leaf 18457) (.node (.leaf 6169) (.leaf 4121)))
    (.node (.leaf 24597) (.node (.leaf 22549) (.leaf 20501)))))))
    (.node (.node (.node (.node (.node (.leaf 18453) (.leaf 8213)) (.node (.leaf 6165)
    (.node (.leaf 4117) (.leaf 21)))) (.node (.node (.leaf 14357) (.node (.leaf 10269)
    (.leaf 14357))) (.node (.leaf 24593) (.node (.leaf 22545) (.leaf 16401)))))
    (.node (.node (.node (.leaf 12305) (.leaf 2065)) (.node (.leaf 10257) (.node (.leaf 8213)
    (.leaf 10257)))) (.node (.node (.leaf 20493) (.node (.leaf 16397) (.leaf 14349)))
    (.node (.leaf 12301) (.node (.leaf 2061) (.leaf 13))))))
    (.node (.node (.node (.node (.leaf 10253) (.leaf 6165)) (.node (.leaf 10253)
    (.node (.leaf 24585) (.leaf 18441)))) (.node (.node (.leaf 6153) (.node (.leaf 4109)
    (.leaf 6153))) (.node (.leaf 16389) (.node (.leaf 14341) (.leaf 10245)))))
    (.node (.node (.node (.leaf 5) (.leaf 14337)) (.node (.leaf 8193) (.node (.leaf 4097)
    (.leaf 2049)))) (.node (.node (.leaf 5) (.node (.leaf 2049) (.leaf 0))) (.node (.leaf 8)
    (.node (.leaf 12) (.leaf 16))))))))
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem checkWhiten13_eq : checkPrimTree18S 12 0 0 whiten13Tree = (true, 0, 0) := by decide +kernel
theorem whiten13Tree_check : (checkPrimTree 12 0 0 whiten13Tree).1 = true ∧
    (checkPrimTree 12 0 0 whiten13Tree).2.2 = 0 := by
  rw [← checkPrimTree18S_eq 12 0 whiten13Tree 0, checkWhiten13_eq]; exact ⟨rfl, rfl⟩
def initWhiten13CT : CT := mkCT 7 fun w ↦ if w < 13 then coordCol 13 w else 0
theorem initWhiten13CT_spec {q : ℕ} (hq : q < 8192) : ∀ u < 13,
    (getCT 7 initWhiten13CT u).testBit q = q.testBit u := by
  intro u hu
  have hu7 : u < 2 ^ 7 := by omega
  have hq13 : q < 2 ^ 13 :=
      hq; rw [initWhiten13CT, getCT_mkCT 7 _ u hu7, itePos hu,
      coordCol_testBit 13 u q hu]; simp only [hq13, decide_true, Bool.true_and]
def parityCol13Aux (mask : ℕ) : ℕ → ℕ
  | 0 => if mask.testBit 13 then repMask 13 else 0
  | k + 1 =>
      let p := parityCol13Aux mask k
      if mask.testBit k then p ^^^ coordCol 13 k else p

theorem parityCol13Aux_testBit (mask : ℕ) {q : ℕ} (hq : q < 8192) :
    ∀ k ≤ 13, (parityCol13Aux mask k).testBit q = parity13Aux mask q.testBit k
  | 0, _ => by
      by_cases hm : mask.testBit 13 <;>
        simp [parityCol13Aux, parity13Aux, hm, repMask_testBit, hq]
  | k + 1, hk => by
      by_cases hm : mask.testBit k <;> simp [parityCol13Aux, parity13Aux, hm,
        parityCol13Aux_testBit mask hq k (by omega), coordCol_testBit 13 k q (by omega),
        hq]

def outWhiten13CT : CT := evalCTW (repMask 13) 12 initWhiten13CT whiten13Tree
def whiten13OutWireNat : ℕ → ℕ
  | 7 => 12
  | b => b

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem whiten13Tree_df8_cert : allBelow 8 (fun b ↦
    Nat.beq (getCT 7 outWhiten13CT (whiten13OutWireNat b)) (parityCol13Aux (rowDf8MaskNat b) 13)) =
    true := by decide +kernel
theorem whiten13Tree_eval_df8 (x : Fin 8192)
    (b : Fin 8) : (evalPrimTree 12 x.val whiten13Tree).testBit (whiten13OutWireNat b.val) =
    (df8Of13 x.val).val.testBit b.val := by
  have hCol : getCT 7 outWhiten13CT (whiten13OutWireNat b.val) = parityCol13Aux (rowDf8Mask b) 13 :=
      Nat.beq_eq.mp ((allBelow_true_iff 8 _).mp whiten13Tree_df8_cert b.val b.isLt)
  have hW : whiten13OutWireNat b.val < 13 := by dsimp only [whiten13OutWireNat]; split <;> omega
  have hSound := evalCTW_sound (W := 13) (M := 12) (by omega : 12 < 128)
    whiten13Tree initWhiten13CT x.val x.val x.isLt
    (initWhiten13CT_spec x.isLt) (whiten13OutWireNat b.val) hW
  dsimp only [outWhiten13CT] at hCol;
  rw [← hSound, hCol, parityCol13Aux_testBit (rowDf8Mask b) x.isLt 13 le_rfl,
      df8Of13_testBit x.val b]; rfl
def x13OfReg13 {n : ℕ} (rC13 : QRegister 13 n) (β : BitAssignment n) : ℕ :=
    natOfZModBits 13 (fun i : Fin 13 ↦ β (rC13 i))
def w11OfReg13 {n : ℕ} (rC13 : QRegister 13 n) (β : BitAssignment n) : Fin 2048 :=
  ⟨natOfZModBits 11 (fun i : Fin 11 ↦ β (rC13 ⟨i.val, by omega⟩)), natOfZModBits_lt 11 _⟩

def inWire13Nat : ℕ → ℕ
  | 0 => 26 | 1 => 27 | 2 => 28 | 3 => 29 | 4 => 30
  | 5 => 16 | 6 => 15 | 7 => 14 | 8 => 13 | 9 => 12 | 10 => 11
  | 11 => 31 | _ => 32

def dstWire9Nat (q : ℕ) : ℕ := 17 + q

def inWire13 (b : Fin 13) : ℕ := inWire13Nat b.val
def dstWire9 (q : Fin 9) : ℕ := dstWire9Nat q.val

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem inWire13_lt (b : Fin 13) : inWire13 b < 96 := by revert b; decide
theorem dstWire9_lt (q : Fin 9) : dstWire9 q < 96 := by revert q; decide
theorem inWire13_ne_dst (b : Fin 13) (q : Fin 9) : inWire13 b ≠ dstWire9 q := by revert b q; decide
theorem dstWire9_inj : Function.Injective dstWire9 := fun a b h ↦
    Fin.ext (by dsimp [dstWire9, dstWire9Nat] at h; omega)
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem dstWire9_nonMask (q : Fin 9) : coul18K2SMask.testBit (dstWire9 q) = false := by
  revert q; decide +kernel
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem inWire13_nonMask (b : Fin 13) : coul18K2SMask.testBit (inWire13 b) = false := by
  revert b; decide +kernel
theorem dstWire9_ge17 (q : Fin 9) : 17 ≤ dstWire9 q := by dsimp [dstWire9, dstWire9Nat]; omega
theorem ne64_dst9 (q : Fin 9) : 64 ≠ dstWire9 q := by dsimp [dstWire9, dstWire9Nat]; omega
theorem ne69_dst9 (q : Fin 9) : 69 ≠ dstWire9 q := by dsimp [dstWire9, dstWire9Nat]; omega

def xorBits13_95 (dst mask : ℕ) : ℕ → PrimTree
  | 0 => if mask.testBit 13 then pX95 dst else .empty
  | k + 1 =>
      let prev := xorBits13_95 dst mask k
      if mask.testBit k then .node prev (pCnot (inWire13Nat k) dst) else prev

def load9Prefix : ℕ → PrimTree
  | 0 => .empty
  | m + 1 => .node (load9Prefix m) (xorBits13_95 (dstWire9Nat m) (rowO9MaskNat m) 13)

def load9Tree95 : PrimTree := load9Prefix 9

def coul18K2Sub63Tree : PrimTree := .node (.node load9Tree95 coul18K2CoreTree) load9Tree95
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem checkCoul18K2Sub63_eq : checkPrimTree18S 95 0 coul18K2SMask coul18K2Sub63Tree =
    (true, 0, 18) := by decide +kernel
theorem coul18K2Sub63Tree_check : (checkPrimTree 95 0 coul18K2SMask coul18K2Sub63Tree).1 = true ∧
    (checkPrimTree 95 0 coul18K2SMask coul18K2Sub63Tree).2.2 = 18 := by
  rw [← checkPrimTree18S_eq 95 0 coul18K2Sub63Tree coul18K2SMask, checkCoul18K2Sub63_eq];
  exact ⟨rfl, rfl⟩
def compOutIdxLo11Nat : ℕ → ℕ
  | 10 => 0
  | u => 8 + u

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem compOutIdxLo11Nat_cert : allBelow 11 (fun u ↦ decide (compOutIdxLo11Nat u =
    (compOutIdx u).val)) = true := by decide +kernel
theorem compOutIdxLo11Nat_eq {u : ℕ} (hu : u < 11) : compOutIdxLo11Nat u = (compOutIdx u).val :=
    of_decide_eq_true ((allBelow_true_iff 11 _).mp compOutIdxLo11Nat_cert u hu)
def coul18K2Sub63Tag (u : Fin 96) : Fin 4 × ℕ :=
  if u.val < 11 then (⟨0, by decide⟩, compOutIdxLo11Nat u.val)
  else if u.val < 17 then (⟨1, by decide⟩, 21 - u.val)
  else if u.val < 26 then (⟨3, by decide⟩, u.val - 17)
  else if u.val < 31 then (⟨1, by decide⟩, u.val - 26)
  else if u.val < 33 then (⟨1, by decide⟩, u.val - 20)
  else if u.val < 52 then (⟨3, by decide⟩, 9 + (u.val - 33))
  else if u.val < 70 then (⟨2, by decide⟩, u.val - 52)
  else (⟨3, by decide⟩, 28 + (u.val - 70))

def coul18K2Sub63InvNat (g k : ℕ) : ℕ :=
  match g with
  | 0 => if k = 0 then 10 else k - 8
  | 1 => inWire13Nat k
  | 2 => 52 + k
  | _ => if k < 9 then 17 + k else if k < 28 then 33 + (k - 9) else 70 + (k - 28)

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem coul18K2Sub63Tag_inv (u : Fin 96) :
    coul18K2Sub63InvNat (coul18K2Sub63Tag u).1.val (coul18K2Sub63Tag u).2 = u.val := by
  revert u; decide +kernel

theorem coul18K2Sub63Tag_inj : Function.Injective coul18K2Sub63Tag :=
  fun a b h ↦ Fin.ext ((coul18K2Sub63Tag_inv a).symm.trans
    ((by rw [h] : coul18K2Sub63InvNat (coul18K2Sub63Tag a).1.val (coul18K2Sub63Tag a).2 =
                  coul18K2Sub63InvNat (coul18K2Sub63Tag b).1.val (coul18K2Sub63Tag b).2).trans
      (coul18K2Sub63Tag_inv b)))

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem coul18K2Sub63Tag_lt0 (u : Fin 96) (h : (coul18K2Sub63Tag u).1.val = 0) :
    (coul18K2Sub63Tag u).2 < 22 := by revert u h; decide +kernel
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem coul18K2Sub63Tag_lt1 (u : Fin 96) (h : (coul18K2Sub63Tag u).1.val = 1) :
    (coul18K2Sub63Tag u).2 < 13 := by revert u h; decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem coul18K2Sub63Tag_lt2 (u : Fin 96) (h : (coul18K2Sub63Tag u).1.val = 2) :
    (coul18K2Sub63Tag u).2 < 18 := by revert u h; decide +kernel
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem coul18K2Sub63Tag_lt3 (u : Fin 96) (h0 : ¬ (coul18K2Sub63Tag u).1.val = 0)
    (h1 : ¬ (coul18K2Sub63Tag u).1.val = 1) (h2 : ¬ (coul18K2Sub63Tag u).1.val = 2) :
    (coul18K2Sub63Tag u).2 < 54 := by revert u h0 h1 h2; decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem coul18K2SMask_iff_sub63Tag2 (u : Fin 96) : coul18K2SMask.testBit u.val = true ↔
    (coul18K2Sub63Tag u).1.val = 2 := by
  revert u; decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem inWire13_tag (b : Fin 13) :
    coul18K2Sub63Tag ⟨inWire13 b, inWire13_lt b⟩ = (⟨1, by decide⟩, b.val) := by
  revert b; decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem dstWire9_tag (q : Fin 9) :
    coul18K2Sub63Tag ⟨dstWire9 q, dstWire9_lt q⟩ = (⟨3, by decide⟩, q.val) := by
  revert q; decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem wire11_eq_inWire13 (j : Fin 6) :
    11 + j.val = inWire13 ⟨10 - j.val, by omega⟩ := by
  revert j; decide

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem coul18K2Sub63Tag_64 : coul18K2Sub63Tag ⟨64, by omega⟩ = (⟨2, by omega⟩, 12) := by
  decide +kernel
set_option maxHeartbeats 3200000 in
-- finite certificate kernel reduction
theorem coul18K2Sub63Tag_69 : coul18K2Sub63Tag ⟨69, by omega⟩ = (⟨2, by omega⟩, 17) := by
  decide +kernel

theorem whiten13OutWireNat_lt7 (b : Fin 7) : whiten13OutWireNat b.val = b.val := by
  revert b; decide

attribute [local irreducible] whiten13Tree PhotochemistrySolution.FineLegendre.natOfZModBits
  o9Of13 df8Of13 affineBit13 popBernJK2

theorem stepCB_whiten13_lo7 {n : ℕ} (rC13 : QRegister 13 n) (β : BitAssignment n) (b : Fin 7) :
    stepCB rC13 (decodePrimTree 12 whiten13Tree).fwdBits β (rC13 ⟨b.val, by omega⟩) =
      if (df8Of13 (x13OfReg13 rC13 β)).val.testBit b.val then 1 else 0 := by
  have hev := whiten13Tree_eval_df8 ⟨x13OfReg13 rC13 β, natOfZModBits_lt 13 _⟩ ⟨b.val, by omega⟩
  dsimp only at hev; rw [whiten13OutWireNat_lt7 b] at hev
  exact (stepCB_primTree_bit whiten13Tree rC13 β ⟨b.val, by omega⟩).trans
    (congrArg (fun c : Bool ↦ if c then (1 : ZMod 2) else 0) hev)

theorem stepCB_whiten13_hi7 {n : ℕ} (rC13 : QRegister 13 n) (β : BitAssignment n) :
    stepCB rC13 (decodePrimTree 12 whiten13Tree).fwdBits β (rC13 ⟨12, by omega⟩) =
      if (df8Of13 (x13OfReg13 rC13 β)).val.testBit 7 then 1 else 0 := by
  have hev := whiten13Tree_eval_df8 ⟨x13OfReg13 rC13 β, natOfZModBits_lt 13 _⟩ ⟨7, by omega⟩
  dsimp only [whiten13OutWireNat] at hev
  exact (stepCB_primTree_bit whiten13Tree rC13 β ⟨12, by omega⟩).trans
    (congrArg (fun c : Bool ↦ if c then (1 : ZMod 2) else 0) hev)

theorem stepCB_whiten13_out {n : ℕ} (rC13 : QRegister 13 n) (β : BitAssignment n) (w : Wire n)
    (hw : ∀ i : Fin 13, w ≠ rC13 i) : stepCB rC13 (decodePrimTree 12 whiten13Tree).fwdBits β w =
    β w := by
  dsimp only [stepCB]
  exact writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ hw i hi.symm)

theorem evalPrimTree_empty (M st : ℕ) : evalPrimTree M st .empty = st := rfl

theorem evalPrimTree_node (M st : ℕ) (l r : PrimTree) :
    evalPrimTree M st (.node l r) = evalPrimTree M (evalPrimTree M st l) r := rfl

theorem xorBits13_95_eval (q : Fin 9) (mask : ℕ) (k : ℕ) : k ≤ 13 → ∀ (st : ℕ),
    (∀ i, i ≠ dstWire9 q → (evalPrimTree 95 st (xorBits13_95 (dstWire9 q) mask k)).testBit i =
    st.testBit i) ∧ ((evalPrimTree 95 st (xorBits13_95 (dstWire9 q) mask k)).testBit (dstWire9 q) =
    xor (st.testBit (dstWire9 q)) (parity13Aux mask (fun b ↦ st.testBit (inWire13Nat b)) k)) := by
  induction k with
  | zero =>
      intro _ st
      by_cases hm : mask.testBit 13 <;>
        simp only [xorBits13_95, parity13Aux, hm, ↓reduceIte, Bool.false_eq_true,
          evalPrimTree_empty, Bool.xor_false]
      · exact ⟨fun i hi ↦ by
            rw [evalPrimTree95_x_xor (dstWire9_lt q) st i, decide_eq_false hi, Bool.xor_false],
          by simp only [evalPrimTree95_x_xor (dstWire9_lt q) st (dstWire9 q), decide_true]⟩
      · exact ⟨fun _ _ ↦ trivial, trivial⟩
  | succ k ih =>
      intro hkLe st
      obtain ⟨hOut, hDst⟩ := ih (by omega) st
      by_cases hm : mask.testBit k <;>
        simp only [xorBits13_95, parity13Aux, hm, ↓reduceIte, Bool.false_eq_true, evalPrimTree_node]
      · rw [show inWire13Nat k = inWire13 ⟨k, by omega⟩ from rfl]
        have hc := evalPrimTree95_cnot (inWire13_lt ⟨k, by omega⟩) (dstWire9_lt q)
          (inWire13_ne_dst ⟨k, by omega⟩ q) (evalPrimTree 95 st (xorBits13_95 (dstWire9 q) mask k))
        exact ⟨fun i hi ↦ (hc i).trans ((iteNeg hi).trans (hOut i hi)),
          (hc _).trans ((itePos rfl).trans (by
            rw [hDst, hOut _ (inWire13_ne_dst ⟨k, by omega⟩ q), Bool.xor_assoc]))⟩
      · exact ⟨hOut, hDst⟩
theorem load9Prefix_eval (m : ℕ) : m ≤ 9 → ∀ (st : ℕ), (∀ i, (∀ q : Fin 9, q.val < m → i ≠
    dstWire9 q) → (evalPrimTree 95 st (load9Prefix m)).testBit i = st.testBit i) ∧
    (∀ q : Fin 9, q.val < m → (evalPrimTree 95 st (load9Prefix m)).testBit (dstWire9 q) =
    xor (st.testBit (dstWire9 q)) (parity13Aux (rowO9Mask q)
    (fun b ↦ st.testBit (inWire13Nat b)) 13)) := by
  induction m with
  | zero => exact fun _ _ ↦ ⟨fun _ _ ↦ rfl, fun _ h ↦ absurd h (by omega)⟩
  | succ m ih =>
      intro hmLe st
      have hm : m < 9 := by omega
      obtain ⟨hOutP, hDstP⟩ := ih (by omega) st
      dsimp only [load9Prefix]
      rw [evalPrimTree_node, show dstWire9Nat m = dstWire9 ⟨m, hm⟩ from rfl,
        show rowO9MaskNat m = rowO9Mask ⟨m, hm⟩ from rfl]
      obtain ⟨hOutCur, hDstCur⟩ := xorBits13_95_eval ⟨m, hm⟩ (rowO9Mask ⟨m, hm⟩) 13 le_rfl
        (evalPrimTree 95 st (load9Prefix m))
      refine ⟨fun i hi ↦ (hOutCur i (hi ⟨m, hm⟩ (Nat.lt_succ_self m))).trans
          (hOutP i fun q' hq' ↦ hi q' (by omega)), fun q hq ↦ ?_⟩
      rcases eq_or_ne q ⟨m, hm⟩ with rfl | hneQ
      · rw [hDstCur, parity13Aux_congr13 _
            (fun b hb ↦ hOutP _ fun q _ ↦ inWire13_ne_dst ⟨b, hb⟩ q) 13 le_rfl,
          hOutP _ fun q' hq' e ↦ absurd (congrArg Fin.val (dstWire9_inj e)) (Nat.ne_of_gt hq')]
      · rw [hOutCur (dstWire9 q) (mt (@dstWire9_inj q ⟨m, hm⟩) hneQ)]
        exact hDstP q (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hq) fun e ↦ hneQ (Fin.ext e))

theorem load9Tree95_eval (st : ℕ) : (∀ i, (∀ q : Fin 9, i ≠ dstWire9 q) →
    (evalPrimTree 95 st load9Tree95).testBit i = st.testBit i) ∧
    (∀ q : Fin 9, (evalPrimTree 95 st load9Tree95).testBit (dstWire9 q) =
    xor (st.testBit (dstWire9 q)) (parity13Aux (rowO9Mask q)
    (fun b ↦ st.testBit (inWire13Nat b)) 13)) := by
  obtain ⟨h1, h2⟩ := load9Prefix_eval 9 le_rfl st
  exact ⟨fun i hi ↦ h1 i (fun q _ ↦ hi q), fun q ↦ h2 q q.isLt⟩

theorem coul18K2Sub63Tree_eq :
    coul18K2Sub63Tree = .node (.node load9Tree95 coul18K2CoreTree) load9Tree95 := rfl

attribute [local irreducible] load9Tree95 coul18K2CoreTree coul18K2Sub63Tree

theorem coul18K2Sub63Tree_pres_nonMask (st i : ℕ) (hi : coul18K2SMask.testBit i = false) :
    (evalPrimTree 95 st coul18K2Sub63Tree).testBit i = st.testBit i := by
  rw [coul18K2Sub63Tree_eq, evalPrimTree_node, evalPrimTree_node];
  obtain ⟨hOut1, hDst1⟩ := load9Tree95_eval st
  generalize hs1 : evalPrimTree 95 st load9Tree95 = s1 at hOut1 hDst1 ⊢
  have hPres2 := coul18K2CoreTree_pres_nonMask s1
  generalize hs2 : evalPrimTree 95 s1 coul18K2CoreTree = s2 at hPres2 ⊢
  obtain ⟨hOut3, hDst3⟩ := load9Tree95_eval s2
  have hSrc2 : ∀ b < 13, s2.testBit (inWire13Nat b) = st.testBit (inWire13Nat b) := fun b hb ↦
      (hPres2 (inWire13 ⟨b, hb⟩) (inWire13_nonMask ⟨b, hb⟩)).trans (hOut1 _ (fun q ↦
      inWire13_ne_dst ⟨b, hb⟩ q))
  by_cases hd : ∃ q : Fin 9, i = dstWire9 q
  · obtain ⟨q, rfl⟩ :=
        hd; rw [hDst3 q, parity13Aux_congr13 _ hSrc2 13 le_rfl, hPres2 (dstWire9 q)
        (dstWire9_nonMask q), hDst1 q, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  · have hd' : ∀ q : Fin 9, i ≠ dstWire9 q := fun q h ↦ hd ⟨q, h⟩
    rw [hOut3 i hd', hPres2 i hi, hOut1 i hd']

theorem coul18K2Sub63Tree_eval_64_69 (st0 t11 : ℕ) (ht11Lt : t11 < 2048) (w11 : Fin 2048)
    (o9 : Fin 512) (hT : ∀ b < 11, (evalPrimTree 95 st0 load9Tree95).testBit b = t11.testBit b)
    (hG : ∀ j : Fin 6, (evalPrimTree 95 st0 load9Tree95).testBit (11 + j.val) =
    w11.val.testBit (10 - j.val)) (hO : ∀ q : Fin 9, (evalPrimTree 95 st0 load9Tree95).testBit (17 +
    q.val) = o9.val.testBit q.val) (hCln : ∀ i, coul18K2SMask.testBit i = true →
    (evalPrimTree 95 st0 load9Tree95).testBit i = false) :
    (evalPrimTree 95 st0 coul18K2Sub63Tree).testBit 64 = (popBernJK2 t11 w11 o9).testBit 0 ∧
    (evalPrimTree 95 st0 coul18K2Sub63Tree).testBit 69 = (popBernJK2 t11 w11 o9).testBit 1 := by
  rw [coul18K2Sub63Tree_eq, evalPrimTree_node, evalPrimTree_node]
  generalize hs1 : evalPrimTree 95 st0 load9Tree95 = s1 at hT hG hO hCln ⊢
  obtain ⟨hj0, hj1⟩ := coul18K2CoreTree_eval_j s1 t11 ht11Lt w11 o9 hT hG hO hCln
  generalize hs2 : evalPrimTree 95 s1 coul18K2CoreTree = s2 at hj0 hj1 ⊢
  obtain ⟨hOut3, _⟩ :=
      load9Tree95_eval s2; rw [hOut3 64 ne64_dst9, hOut3 69 ne69_dst9, hj0, hj1]; exact ⟨rfl, rfl⟩
def fCoul18K2Sub63 {n : ℕ} (rOut22 : QRegister 22 n) (rC13 : QRegister 13 n)
    (rPers18 : QRegister 18 n) (rPad54 : QRegister 54 n) (u : Fin 96) : Wire n :=
    if h0 : (coul18K2Sub63Tag u).1.val = 0 then rOut22 ⟨(coul18K2Sub63Tag u).2,
    coul18K2Sub63Tag_lt0 u h0⟩ else if h1 : (coul18K2Sub63Tag u).1.val =
    1 then rC13 ⟨(coul18K2Sub63Tag u).2, coul18K2Sub63Tag_lt1 u h1⟩ else if h2 :
    (coul18K2Sub63Tag u).1.val = 2 then rPers18 ⟨(coul18K2Sub63Tag u).2,
    coul18K2Sub63Tag_lt2 u h2⟩ else rPad54 ⟨(coul18K2Sub63Tag u).2, coul18K2Sub63Tag_lt3 u h0 h1 h2⟩
theorem fCoul18K2Sub63_inj {n : ℕ} {rOut22 : QRegister 22 n} {rC13 : QRegister 13 n}
    {rPers18 : QRegister 18 n} {rPad54 : QRegister 54 n} (hOC : rOut22.DisjointWires rC13)
    (hOP : rOut22.DisjointWires rPers18) (hOD : rOut22.DisjointWires rPad54)
    (hCP : rC13.DisjointWires rPers18) (hCD : rC13.DisjointWires rPad54)
    (hPD : rPers18.DisjointWires rPad54) :
    Function.Injective (fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54) :=
  fun a b e ↦ coul18K2Sub63Tag_inj (by
    dsimp only [fCoul18K2Sub63] at e
    have eqPair : ∀ {g1 g2 : Fin 4} {k1 k2 : ℕ}, g1.val = g2.val → k1 = k2 →
        (g1, k1) = (g2, k2) := fun hg hk ↦ Prod.ext (Fin.ext hg) hk
    split_ifs at e with ha0 hb0 hb1 hb2 ha1 _ hb1' hb2' ha2 _ _ hb2'' _ _ _
    all_goals try first
      | exact absurd e (disj_ne hOC _ _) | exact absurd e.symm (disj_ne hOC _ _)
      | exact absurd e (disj_ne hOP _ _) | exact absurd e.symm (disj_ne hOP _ _)
      | exact absurd e (disj_ne hOD _ _) | exact absurd e.symm (disj_ne hOD _ _)
      | exact absurd e (disj_ne hCP _ _) | exact absurd e.symm (disj_ne hCP _ _)
      | exact absurd e (disj_ne hCD _ _) | exact absurd e.symm (disj_ne hCD _ _)
      | exact absurd e (disj_ne hPD _ _) | exact absurd e.symm (disj_ne hPD _ _)
    · exact eqPair (ha0.trans hb0.symm) (congrArg Fin.val (rOut22.wires.injective e))
    · exact eqPair (ha1.trans hb1'.symm) (congrArg Fin.val (rC13.wires.injective e))
    · exact eqPair (ha2.trans hb2''.symm) (congrArg Fin.val (rPers18.wires.injective e))
    · refine Prod.ext (Fin.ext ?_) (congrArg Fin.val (rPad54.wires.injective e))
      have ha := (coul18K2Sub63Tag a).1.isLt
      have hb := (coul18K2Sub63Tag b).1.isLt
      omega)

def rCoul18K2Sub63 {n : ℕ} {rOut22 : QRegister 22 n} {rC13 : QRegister 13 n}
    {rPers18 : QRegister 18 n} {rPad54 : QRegister 54 n} (hOC : rOut22.DisjointWires rC13)
    (hOP : rOut22.DisjointWires rPers18) (hOD : rOut22.DisjointWires rPad54)
    (hCP : rC13.DisjointWires rPers18) (hCD : rC13.DisjointWires rPad54)
    (hPD : rPers18.DisjointWires rPad54) : QRegister 96 n :=
    ⟨⟨fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54, fCoul18K2Sub63_inj hOC hOP hOD hCP hCD hPD⟩⟩
theorem stepCB_coul18K2Sub63_pres_nonPers {n : ℕ} {rOut22 : QRegister 22 n} {rC13 : QRegister 13 n}
    {rPers18 : QRegister 18 n} {rPad54 : QRegister 54 n} (hOC : rOut22.DisjointWires rC13)
    (hOP : rOut22.DisjointWires rPers18) (hOD : rOut22.DisjointWires rPad54)
    (hCP : rC13.DisjointWires rPers18) (hCD : rC13.DisjointWires rPad54)
    (hPD : rPers18.DisjointWires rPad54) (β : BitAssignment n) (w : Wire n)
    (hw : ∀ q : Fin 18, w ≠ rPers18 q) : stepCB (rCoul18K2Sub63 hOC hOP hOD hCP hCD hPD)
    (decodePrimTree 95 coul18K2Sub63Tree).fwdBits β w = β w := by
  set rF := rCoul18K2Sub63 hOC hOP hOD hCP hCD hPD
  by_cases hm : ∃ u : Fin 96, rF u = w
  · obtain ⟨u, rfl⟩ := hm; rw [stepCB_primTree_bit coul18K2Sub63Tree rF β u]
    have hNot2 : ¬ (coul18K2Sub63Tag u).1.val = 2 := by
      intro h2
      have hEq : rF u = rPers18 ⟨(coul18K2Sub63Tag u).2, coul18K2Sub63Tag_lt2 u h2⟩ := by
        change fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 u = _; dsimp only [fCoul18K2Sub63]
        rw [diteNeg (by omega), diteNeg (by omega), ditePos h2]
      exact hw _ hEq
    have hmF : coul18K2SMask.testBit u.val = false :=
        Bool.eq_false_iff.mpr (mt (coul18K2SMask_iff_sub63Tag2 u).mp hNot2);
        rw [coul18K2Sub63Tree_pres_nonMask _ u.val hmF,
        natOfZModBits_testBit_lt _ u.isLt]; exact (zmod2_eq_ite_of_beq_one (β (rF u)) _ rfl).symm
  · dsimp only [stepCB]; exact writeReg_apply_of_not_mem _ _ _ _ hm
theorem stepCB_coul18K2Sub63_eval_j {n : ℕ}
    {rOut22 : QRegister 22 n} {rC13 : QRegister 13 n}
    {rPers18 : QRegister 18 n} {rPad54 : QRegister 54 n}
    (hOC : rOut22.DisjointWires rC13) (hOP : rOut22.DisjointWires rPers18)
    (hOD : rOut22.DisjointWires rPad54) (hCP : rC13.DisjointWires rPers18)
    (hCD : rC13.DisjointWires rPad54) (hPD : rPers18.DisjointWires rPad54)
    (β : BitAssignment n) (isNN : Bool) {d2 : ℕ} (hd2 : d2 < 262144)
    (hOut : ∀ j : Fin 22,
      β (rOut22 j) = if dom22Bit (evenOctIdxT10K isNN d2) j then 1 else 0)
    (hPers0 : ∀ q : Fin 18, β (rPers18 q) = 0)
    (hPad0 : ∀ q : Fin 9, β (rPad54 ⟨q.val, by omega⟩) = 0) :
    let p := evenOctIdxT10K isNN d2; let rF := rCoul18K2Sub63 hOC hOP hOD hCP hCD hPD
    ∀ q : Fin 2, stepCB rF (decodePrimTree 95 coul18K2Sub63Tree).fwdBits β
          (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18 q) =
        if (popBernJK2 (t11OfParts p) (w11OfReg13 rC13 β)
            (o9Of13 (x13OfReg13 rC13 β))).testBit q.val
        then 1 else 0 := by
  dsimp only
  set p := evenOctIdxT10K isNN d2
  set rF := rCoul18K2Sub63 hOC hOP hOD hCP hCD hPD
  obtain ⟨ht11Lt, hTBits, _, _⟩ := out22_t11_bits rOut22 β isNN hd2 hOut
  set st0 := natOfZModBits 96 (fun i ↦ β (rF i))
  obtain ⟨hOut1, hDst1⟩ := load9Tree95_eval st0
  generalize hs1 : evalPrimTree 95 st0 load9Tree95 = s1 at hOut1 hDst1
  set w11 := w11OfReg13 rC13 β
  set x13 := x13OfReg13 rC13 β
  set o9 := o9Of13 x13
  have hSrcBits (b : ℕ) (hb : b < 13) : st0.testBit (inWire13Nat b) = x13.testBit b := by
    change st0.testBit (inWire13 ⟨b, hb⟩) = x13.testBit b
    dsimp only [st0, x13, x13OfReg13]
    rw [natOfZModBits_testBit_lt _ (inWire13_lt ⟨b, hb⟩), natOfZModBits_testBit_lt _ hb]
    have ht := inWire13_tag ⟨b, hb⟩
    have hg1 : (coul18K2Sub63Tag ⟨inWire13 ⟨b, hb⟩, inWire13_lt ⟨b, hb⟩⟩).1.val = 1 := by rw [ht]
    refine congrArg (fun x ↦ x == 1) (congrArg β ?_)
    change fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 ⟨inWire13 ⟨b, hb⟩, inWire13_lt ⟨b, hb⟩⟩ = _
    dsimp only [fCoul18K2Sub63]
    rw [diteNeg (by omega), ditePos hg1]
    exact congrArg rC13.wires (Fin.ext (congrArg Prod.snd ht))
  have hParEq (q : Fin 9) :
      parity13Aux (rowO9Mask q) (fun b ↦ st0.testBit (inWire13Nat b)) 13 =
        affineBit13 (rowO9Mask q) x13 :=
    (parity13Aux_congr13 (rowO9Mask q) hSrcBits 13 le_rfl).trans
      (affineBit13_eq (rowO9Mask q) x13).symm
  have hDst0 (q : Fin 9) : st0.testBit (dstWire9 q) = false := by
    have ht := dstWire9_tag q
    have hg3 : (coul18K2Sub63Tag ⟨dstWire9 q, dstWire9_lt q⟩).1.val = 3 := congrArg (·.1.val) ht
    have hEq : rF ⟨dstWire9 q, dstWire9_lt q⟩ = rPad54 ⟨q.val, by omega⟩ := by
      change fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 _ = _
      rw [fCoul18K2Sub63, diteNeg (by omega), diteNeg (by omega), diteNeg (by omega)]
      exact congrArg rPad54.wires (Fin.ext (congrArg Prod.snd ht))
    rw [natOfZModBits_testBit_lt _ (dstWire9_lt q), hEq, hPad0 q]; rfl
  have hT (b : ℕ) (hb : b < 11) : s1.testBit b = (t11OfParts p).testBit b := by
    have hg0 : (coul18K2Sub63Tag ⟨b, by omega⟩).1.val = 0 := by simp [coul18K2Sub63Tag, hb]
    have hEq : rF ⟨b, by omega⟩ = rOut22 (compOutIdx b) := by
      change fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 ⟨b, by omega⟩ = _
      rw [fCoul18K2Sub63, ditePos hg0]
      exact congrArg rOut22.wires (Fin.ext (by simp [coul18K2Sub63Tag, hb, compOutIdxLo11Nat_eq]))
    rw [hOut1 b fun q ↦ by have := dstWire9_ge17 q; omega,
      natOfZModBits_testBit_lt _ (by omega : b < 96), hEq]
    exact hTBits ⟨b, hb⟩
  have hG (j : Fin 6) : s1.testBit (11 + j.val) = w11.val.testBit (10 - j.val) := by
    rw [wire11_eq_inWire13 j, hOut1 _ fun q ↦ inWire13_ne_dst ⟨10 - j.val, by omega⟩ q]
    refine (hSrcBits (10 - j.val) (by omega)).trans ?_
    dsimp only [x13, x13OfReg13, w11, w11OfReg13]
    rw [natOfZModBits_testBit_lt _ (by omega : 10 - j.val < 13),
      natOfZModBits_testBit_lt _ (by omega : 10 - j.val < 11)]
  have hO : ∀ q : Fin 9, s1.testBit (17 + q.val) = o9.val.testBit q.val := fun q ↦ by
    change s1.testBit (dstWire9 q) = _;
    rw [hDst1 q, hDst0 q, Bool.false_xor, hParEq q, ← o9Of13_testBit x13 q]
  have hTag2 (idx : Fin 96) (pI : Fin 18) (hg2 : (coul18K2Sub63Tag idx).1.val = 2)
      (hp : (coul18K2Sub63Tag idx).2 = pI.val) : rF idx = rPers18 pI := by
    change fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 idx = rPers18 pI
    dsimp only [fCoul18K2Sub63]
    rw [diteNeg (by omega), diteNeg (by omega), ditePos hg2]
    exact congrArg rPers18.wires (Fin.ext hp)
  have hCln : ∀ i, coul18K2SMask.testBit i = true → s1.testBit i = false := fun i hi ↦ by
    rw [hOut1 i (fun q e ↦ Bool.false_ne_true ((dstWire9_nonMask q).symm.trans (e ▸ hi)))]
    by_cases hi96 : i < 96
    · have hg2 := (coul18K2SMask_iff_sub63Tag2 ⟨i, hi96⟩).mp hi
      rw [natOfZModBits_testBit_lt _ hi96,
          hTag2 ⟨i, hi96⟩ ⟨_, coul18K2Sub63Tag_lt2 _ hg2⟩ hg2 rfl, hPers0]
      rfl
    · exact Nat.testBit_eq_false_of_lt ((natOfZModBits_lt 96 _).trans_le
        (Nat.pow_le_pow_right (by omega) (by omega)))
  subst hs1
  obtain ⟨he64, he69⟩ :=
    coul18K2Sub63Tree_eval_64_69 st0 (t11OfParts p) ht11Lt w11 o9 hT hG hO hCln
  have hBit {q : Fin 2} (idx : Fin 96) (pI : Fin 18) (hIdx : coul18K2OutIdx2 q = pI)
      (ht : coul18K2Sub63Tag idx = (2, pI.val)) {b : Bool}
      (he : (evalPrimTree 95 st0 coul18K2Sub63Tree).testBit idx.val = b) :
      stepCB rF (decodePrimTree 95 coul18K2Sub63Tree).fwdBits β
        (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18 q) = if b then 1 else 0 :=
    (congrArg (stepCB rF (decodePrimTree 95 coul18K2Sub63Tree).fwdBits β)
      ((congrArg rPers18.wires hIdx).trans
        (hTag2 idx pI (congrArg (fun x ↦ x.1.val) ht) (congrArg Prod.snd ht)).symm)).trans
      ((stepCB_primTree_bit coul18K2Sub63Tree rF β idx).trans
        (congrArg (fun c : Bool ↦ if c then (1 : ZMod 2) else 0) he))
  rintro ⟨_ | ⟨_ | q⟩, hq⟩
  · exact hBit ⟨64, by omega⟩ ⟨12, by omega⟩ coul18K2OutIdx2_0 coul18K2Sub63Tag_64 he64
  · exact hBit ⟨69, by omega⟩ ⟨17, by omega⟩ coul18K2OutIdx2_1 coul18K2Sub63Tag_69 he69
  · omega

def rPad54OfPoolM54 {M n : ℕ} (h54 : 54 ≤ M) (rPool : QRegister M n) : QRegister 54 n :=
  ⟨⟨fun u ↦ rPool ⟨u.val, by omega⟩,
    fun a b e ↦
        Fin.ext (by have hv := congrArg Fin.val (rPool.wires.injective e); dsimp at hv; omega)⟩⟩

def disjCoin13Bool {w n : ℕ} (wG : Wire n) (r : QRegister w n) (rC13 : QRegister 13 n) : Bool :=
    decide ((∀ i, wG ≠ r i) ∧ (∀ j, wG ≠ rC13 j) ∧ (∀ i j, r i ≠ rC13 j))
theorem disjCoin13Bool_sound {w n : ℕ} {wG : Wire n} {r : QRegister w n} {rC13 : QRegister 13 n}
    (h : disjCoin13Bool wG r rC13 = true) : (∀ i, wG ≠ r i) ∧ (∀ j, wG ≠ rC13 j) ∧
    r.DisjointWires rC13 := by
  rcases of_decide_eq_true h with ⟨hGR, hGC, hRC⟩
  exact ⟨hGR, hGC, QRegister.disjoint_iff.mpr hRC⟩

theorem disjCoin13Bool_eq_true {w n : ℕ} {wG : Wire n} {r : QRegister w n} {rC13 : QRegister 13 n}
    (hGR : ∀ i, wG ≠ r i) (hGC : ∀ j, wG ≠ rC13 j) (hRC : r.DisjointWires rC13) :
    disjCoin13Bool wG r rC13 = true := decide_eq_true ⟨hGR, hGC, QRegister.disjoint_iff.mp hRC⟩
structure CoulOWScrPkg13 (tCoul : ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) where
  kRest : ℕ
  kMid : ℕ
  hKMid : kMid ≤ kRest
  wrap : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (_ : Var) (_wG _wScr _wNN : Wire n)
    (_r : QRegister (54 + kRest) n) (_rC13 : QRegister 13 n)
    (_mid : DynamicCircuit Var n), DynamicCircuit Var n
  counts_wires : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {S : Wire n → Prop} (v : Var) (wG wScr wNN : Wire n)
    (r : QRegister (54 + kRest) n) (rC13 : QRegister 13 n)
    (_ : ∀ i, wG ≠ r i) (_ : ∀ j, wG ≠ rC13 j)
    (_ : ∀ i, wScr ≠ r i) (_ : ∀ j, wScr ≠ rC13 j)
    (_ : ∀ i, wNN ≠ r i) (_ : ∀ j, wNN ≠ rC13 j)
    (_ : wScr ≠ wNN) (_ : r.DisjointWires rC13),
    S wG → S wScr → S wNN → (∀ i, S (r i)) → (∀ j, S (rC13 j)) →
    ∀ mid : DynamicCircuit Var n,
      (wrap v wG wScr wNN r rC13 mid).count .T = tCoul + mid.count .T ∧
      (wrap v wG wScr wNN r rC13 mid).count .TOFF = mid.count .TOFF ∧
      (DynWires S mid → DynWires S (wrap v wG wScr wNN r rC13 mid))
  step_phase2 : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (wG wScr wNN : Wire n)
    (r : QRegister (54 + kRest) n) (rC13 : QRegister 13 n)
    (_ : ∀ i, wG ≠ r i) (_ : ∀ j, wG ≠ rC13 j)
    (_ : ∀ i, wScr ≠ r i) (_ : ∀ j, wScr ≠ rC13 j)
    (_ : ∀ i, wNN ≠ r i) (_ : ∀ j, wNN ≠ rC13 j)
    (_ : wScr ≠ wNN) (_ : r.DisjointWires rC13)
    (mid : DynamicCircuit Var n)
    (st₁ st₂ : BitAssignment n → BitAssignment n)
    (ph₁ ph₂ : BitAssignment n → ZMod 2),
    (∀ δ, (∀ k, δ (rWork k) = 0) →
      natOfZModBits 18 (fun b ↦ st₁ δ (r ⟨b.val, potGen_d2_lt kRest b⟩)) ≤ 195075) →
    (∀ δ, (∀ k, δ (rWork k) = 0) → st₁ δ wScr = 0 → st₁ δ wNN = 0) →
    (∀ δ (b : Fin 36), (∀ k, δ (rWork k) = 0) →
      st₁ δ (r ⟨18 + b.val, potGen_y36_lt kRest b⟩) = 0 ∧
      st₂ δ (r ⟨18 + b.val, potGen_y36_lt kRest b⟩) = 0) →
    (∀ δ (u : Fin kRest), (∀ k, δ (rWork k) = 0) →
      st₁ δ (r ⟨54 + u.val, potGen_k_lt kRest u⟩) = 0 ∧
      st₂ δ (r ⟨54 + u.val, potGen_k_lt kRest u⟩) = 0) →
    (∀ δ, (∀ k, δ (rWork k) = 0) →
      st₂ δ wG = st₁ δ wG ∧ st₂ δ wScr = st₁ δ wScr ∧ st₂ δ wNN = st₁ δ wNN ∧
      (∀ b : Fin 18, st₂ δ (r ⟨b.val, potGen_d2_lt kRest b⟩) =
        st₁ δ (r ⟨b.val, potGen_d2_lt kRest b⟩)) ∧
      (∀ j, st₂ δ (rC13 j) = st₁ δ (rC13 j))) →
    (∀ m₁ m₂ : BitAssignment n → BitAssignment n,
      (∀ δ w, (∀ b : Fin 36, w ≠ r ⟨18 + b.val, potGen_y36_lt kRest b⟩) →
        (∀ u : Fin kRest, w ≠ r ⟨54 + u.val, potGen_k_lt kRest u⟩) →
        m₁ δ w = st₁ δ w ∧ m₂ δ w = st₂ δ w) →
      (∀ δ, (∀ k, δ (rWork k) = 0) →
        let yV :=
            if st₁ δ wG == 1 then ySample13 (st₁ δ wNN == 1)
            (natOfZModBits 18 (fun b ↦ st₁ δ (r ⟨b.val, potGen_d2_lt kRest b⟩)))
            (w11OfReg13 rC13 (st₁ δ)) (o9Of13 (x13OfReg13 rC13 (st₁ δ)))
        else 0
        let sh1 := if (st₁ δ wScr == 1) && !(st₁ δ wNN == 1) then 1 else 0
        natOfZModBits 36 (fun b ↦ m₁ δ (r ⟨18 + b.val, potGen_y36_lt kRest b⟩)) / 8 = (yV >>> sh1) /
            8 ∧
        (∀ b : Fin 36,
          m₂ δ (r ⟨18 + b.val, potGen_y36_lt kRest b⟩) =
            m₁ δ (r ⟨18 + b.val, potGen_y36_lt kRest b⟩)) ∧
        (st₁ δ wG = 0 →
          ∀ b : Fin 36, m₁ δ (r ⟨18 + b.val, potGen_y36_lt kRest b⟩) = 0)) →
      (∀ δ (j : Fin kMid), (∀ k, δ (rWork k) = 0) →
        m₁ δ (r ⟨54 + j.val, potGen_mid_lt hKMid j⟩) = 0 ∧
        m₂ δ (r ⟨54 + j.val, potGen_mid_lt hKMid j⟩) = 0) →
      (∀ δ (u : Fin kRest), (∀ k, δ (rWork k) = 0) →
        m₂ δ (r ⟨54 + u.val, potGen_k_lt kRest u⟩) =
          m₁ δ (r ⟨54 + u.val, potGen_k_lt kRest u⟩)) →
      SubspaceStep (mkKetOpW rWork m₁ ph₁) (mkKetOpW rWork m₂ ph₂) mid) →
    SubspaceStep (mkKetOpW rWork st₁ ph₁) (mkKetOpW rWork st₂ ph₂)
      (wrap v wG wScr wNN r rC13 mid)
end QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2
open PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17
    (owmbu_two_leg_kick_collapse)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PrimGateEval (natOfZModBits_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (df8Of13 o9Of13 ySampleK2
    x13OfReg13 w11OfReg13)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29 (midWTap29)
attribute [local irreducible] PhotochemistrySolution.Stage4FineFast.natOfBoolBits
theorem midWTap29_congr_div8 (isScr : Bool) {y1 y2 : ℕ} (h : y1 / 8 = y2 / 8)
    (zLo14 : ℕ) : midWTap29 isScr y1 zLo14 = midWTap29 isScr y2 zLo14 := by
  have h5 : y1 >>> 5 = y2 >>> 5 := by simp only [Nat.shiftRight_eq_div_pow]; omega
  have h17 : y1 >>> 17 = y2 >>> 17 := by simp only [Nat.shiftRight_eq_div_pow]; omega
  unfold midWTap29; rw [h5, h17]
def midWTap29OfMode (isScr isNN : Bool) (y36 zLo14 : ℕ) : ℕ :=
    midWTap29 isScr (y36 >>> (if isScr && !isNN then 1 else 0)) zLo14
theorem midWTap29_eq_midWTap29OfMode (isScr isNN : Bool) {yOut y36 : ℕ}
    (h : yOut / 8 = (y36 >>> (if isScr && !isNN then 1 else 0)) / 8)
    (zLo14 : ℕ) : midWTap29 isScr yOut zLo14 = midWTap29OfMode isScr isNN y36 zLo14 :=
    midWTap29_congr_div8 isScr h zLo14
def x13K2 (γ : BitAssignment 17) (z : BitAssignment 24) : ℕ :=
  (w11Sub63 γ).val +
    2048 * (if z ⟨0, by omega⟩ == 1 then 1 else 0) +
    4096 * (if z ⟨1, by omega⟩ == 1 then 1 else 0)

def zMid6Of24 (z : BitAssignment 24) : ℕ :=
  natOfZModBits 6 (fun i ↦ z ⟨2 + i.val, by omega⟩)

def zLo14K2 (γ : BitAssignment 17) (z : BitAssignment 24) : ℕ :=
    (df8Of13 (x13K2 γ z)).val + 2 ^ 8 * zMid6Of24 z
def z30K2 (γ : BitAssignment 17) (z : BitAssignment 24) : ℕ := zLo14K2 γ z + 2 ^ 14 * zHi16Of24 z
theorem z30K2_split14 (γ : BitAssignment 17) (z : BitAssignment 24) :
    z30K2 γ z = zLo14K2 γ z + 2 ^ 14 * zHi16Of24 z := rfl

theorem zLo14K2_lt (γ : BitAssignment 17) (z : BitAssignment 24) : zLo14K2 γ z < 2 ^ 14 := by
  unfold zLo14K2 zMid6Of24; have h1 := (df8Of13 (x13K2 γ z)).isLt
  have h2 := natOfZModBits_lt 6 (fun i : Fin 6 ↦ z ⟨2 + i.val, by omega⟩)
  omega

theorem z30K2_lo_hi (γ : BitAssignment 17) (z : BitAssignment 24) : zLo14K2 γ z =
    z30K2 γ z % 2 ^ 14 ∧ zHi16Of24 z = z30K2 γ z / 2 ^ 14 := by
  have hsp := z30K2_split14 γ z; have hlt := zLo14K2_lt γ z; refine ⟨?_, ?_⟩
  · rw [hsp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [hsp, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hlt, zero_add]

def t31ModTap29 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ) (s nn : Bool) (sp1 sp2 : Fin 4)
    (b1 b2 : Fin 8) (y36 zLo14 : ℕ) : ℕ :=
    (v1Fn s nn sp1 b1 * 2 ^ 14 + v2Fn s nn sp2 b2 * 2 ^ 14 +
    midWTap29OfMode s nn y36 zLo14) % 2 ^ 31
def owK2SHi14 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) : ℕ :=
  let y36 := ySample13 nn (sectorDist3DSq3 s nn nA pB eA) (w11Sub63 γ) (o9Of13 (x13K2 γ z));
  let b1 := fin8Bin (openCoordDistSq nA eA); let b2 := owB2Of3Port nn nA pB eA;
  let zLo := zLo14K2 γ z
  (t31ModTap29 v1Fn v2Fn s nn sp1 sp2 b1 b2 y36 zLo + zLo) / 2 ^ 14

def owK2CoinSwap3 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) : BitAssignment 24 :=
  fun k ↦ if k.val < 8 then z k
    else
      let u' :=
          2 ^ 16 - 1 -
          (zHi16Of24 z + owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z) % 2 ^ 16
      if u'.testBit (k.val - 8) then 1 else 0

def owK2PhaseBit3 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) : ZMod 2 :=
  let y36 := ySample13 nn (sectorDist3DSq3 s nn nA pB eA) (w11Sub63 γ) (o9Of13 (x13K2 γ z));
  let b1 := fin8Bin (openCoordDistSq nA eA); let b2 := owB2Of3Port nn nA pB eA;
  let tM := t31ModTap29 v1Fn v2Fn s nn sp1 sp2 b1 b2 y36 (zLo14K2 γ z)
  (if (tM + z30K2 γ z).testBit 30 then (1 : ZMod 2) else 0) +
    (if s then (1 : ZMod 2) else 0)

theorem x13K2_lo_congr (γ : BitAssignment 17) {z₁ z₂ : BitAssignment 24}
    (h0 : z₁ ⟨0, by omega⟩ = z₂ ⟨0, by omega⟩)
    (h1 : z₁ ⟨1, by omega⟩ = z₂ ⟨1, by omega⟩) :
    x13K2 γ z₁ = x13K2 γ z₂ := by
  unfold x13K2; rw [h0, h1]

theorem zLo14K2_lo_congr (γ : BitAssignment 17) {z₁ z₂ : BitAssignment 24}
    (h : ∀ k : Fin 24, k.val < 8 → z₁ k = z₂ k) : zLo14K2 γ z₁ = zLo14K2 γ z₂ := by
  have hx :=
      x13K2_lo_congr γ (h ⟨0, by omega⟩ (by dsimp; omega)) (h ⟨1, by omega⟩ (by dsimp; omega))
  have hm : zMid6Of24 z₁ = zMid6Of24 z₂ :=
    congrArg (natOfZModBits 6) (funext fun i ↦ h ⟨2 + i.val, by omega⟩ (by dsimp; omega))
  unfold zLo14K2; rw [hx, hm]

theorem owK2SHi14_lo_congr (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) {z₁ z₂ : BitAssignment 24}
    (h : ∀ k : Fin 24, k.val < 8 → z₁ k = z₂ k) :
    owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z₁ =
    owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z₂ := by
  unfold owK2SHi14
  rw [x13K2_lo_congr γ (h ⟨0, by omega⟩ (by dsimp; omega)) (h ⟨1, by omega⟩ (by dsimp; omega)),
      zLo14K2_lo_congr γ h]

theorem owK2CoinSwap3_lo (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) {k : Fin 24}
    (hk : k.val < 8) : owK2CoinSwap3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z k = z k := by
  simp only [owK2CoinSwap3, hk, ↓reduceIte]
theorem zHi16Of24_owK2CoinSwap3 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) :
    zHi16Of24 (owK2CoinSwap3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z) = 2 ^ 16 - 1 -
    (zHi16Of24 z + owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z) % 2 ^ 16 := by
  set u' :=
      2 ^ 16 - 1 - (zHi16Of24 z + owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z) % 2 ^ 16
  have hu' : u' < 2 ^ 16 := (refl16_invol_and_div (natOfZModBits_lt 16 _) _).1; unfold zHi16Of24
  rw [show (fun j : Fin 16 ↦
        owK2CoinSwap3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z ⟨8 + j.val, by omega⟩) =
      fun j : Fin 16 ↦ if u'.testBit j.val then (1 : ZMod 2) else 0 from funext fun j ↦ by
        simp only [owK2CoinSwap3, show ¬8 + j.val < 8 by omega, ↓reduceIte,
          show 8 + j.val - 8 = j.val by omega]; rfl,
    natOfZModBits_of_testBit 16 u', Nat.mod_eq_of_lt hu']

theorem owK2CoinSwap3_invol (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) :
    owK2CoinSwap3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA (owK2CoinSwap3 v1Fn v2Fn ySample13 γ s
    nn sp1 sp2 nA pB eA z) = z := by
  set z' := owK2CoinSwap3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z
  have hsEq : owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z' =
      owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z :=
      owK2SHi14_lo_congr v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA fun k hk ↦
      owK2CoinSwap3_lo v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z hk
  have hu'' : 2 ^ 16 - 1 - (zHi16Of24 z' +
      owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z') % 2 ^ 16 =
      zHi16Of24 z := by
    rw [hsEq, zHi16Of24_owK2CoinSwap3]; exact (refl16_invol_and_div (natOfZModBits_lt 16 _) _).2.1
  funext k
  by_cases hk : k.val < 8
  · dsimp only [z'];
    rw [owK2CoinSwap3_lo _ _ _ _ _ _ _ _ _ _ _ _ hk, owK2CoinSwap3_lo _ _ _ _ _ _ _ _ _ _ _ _ hk]
  · simp only [owK2CoinSwap3, hk, ↓reduceIte, hu'']
    let j : Fin 16 := ⟨k.val - 8, by have := k.isLt; omega⟩
    have hBits := finBitsVal_inj (m := 16)
      (f := fun q : Fin 16 ↦ if (zHi16Of24 z).testBit q.val then (1 : ZMod 2) else 0)
      (g := fun q : Fin 16 ↦ z ⟨8 + q.val, by omega⟩) <| by
        rw [finBitsVal_eq_natOfZModBits, finBitsVal_eq_natOfZModBits,
            natOfZModBits_of_testBit 16 (zHi16Of24 z)]; unfold zHi16Of24; exact Nat.mod_eq_of_lt
            (natOfZModBits_lt 16 _)
    have hj := congrFun hBits j; dsimp only [j] at hj
    have hkEq : (⟨8 + (k.val - 8), by omega⟩ : Fin 24) = k := Fin.ext (by dsimp; omega)
    rw [hkEq] at hj; exact hj
theorem owK2PhaseBit3_coinSwap (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) :
    owK2PhaseBit3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA (owK2CoinSwap3 v1Fn v2Fn ySample13 γ s
    nn sp1 sp2 nA pB eA z) = owK2PhaseBit3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z := by
  set z' := owK2CoinSwap3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z
  have hLo : ∀ k : Fin 24, k.val < 8 → z' k = z k := fun k hk ↦
      owK2CoinSwap3_lo v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z hk
  have hx : x13K2 γ z' = x13K2 γ z :=
    x13K2_lo_congr γ (hLo ⟨0, by omega⟩ (by dsimp; omega)) (hLo ⟨1, by omega⟩ (by dsimp; omega))
  have hz14 : zLo14K2 γ z' = zLo14K2 γ z := zLo14K2_lo_congr γ hLo
  have hDiv : (zHi16Of24 z' + owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z) / 2 ^ 16 =
      (zHi16Of24 z + owK2SHi14 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA pB eA z) / 2 ^ 16 := by
    rw [zHi16Of24_owK2CoinSwap3]; exact (refl16_invol_and_div (natOfZModBits_lt 16 _) _).2.2
  have htb30 (t : ℕ) (x : BitAssignment 24) : (t + z30K2 γ x).testBit 30 =
      ((zHi16Of24 x + (t + zLo14K2 γ x) / 2 ^ 14) / 2 ^ 16).testBit 0 := by
    rw [z30K2_split14 γ x, show t + (zLo14K2 γ x + 2 ^ 14 * zHi16Of24 x) =
      (t + zLo14K2 γ x) + 2 ^ 14 * zHi16Of24 x by ring]
    conv_lhs => rw [show (30 : ℕ) = 0 + (14 + 16) from rfl]
    rw [Nat.testBit_add, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by norm_num), Nat.add_comm]
  unfold owK2PhaseBit3; dsimp only; rw [hx, hz14, htb30 _ z', htb30 _ z, hz14]
  exact congrArg (fun q : ℕ ↦ (if q.testBit 0 then (1 : ZMod 2) else 0) +
      (if s then (1 : ZMod 2) else 0)) hDiv

theorem owK2_two_leg_collapse {isU10 : Bool} {tLeg1 tLeg2 kMidLM tMidLM : ℕ}
    (pkgLM : OWLegsMidPkg isU10 tLeg1 tLeg2 kMidLM tMidLM)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ)
    (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) :
    let y36 : ℕ := ySample13 nn (sectorDist3DSq3 s nn nA pB eA) (w11Sub63 γ) (o9Of13 (x13K2 γ z));
    let v1 : ℕ := pkgLM.v1Fin8 s nn sp1 (fin8Bin (openCoordDistSq nA eA));
    let v2 : ℕ := pkgLM.v2Fin8 s nn sp2 (owB2Of3Port nn nA pB eA);
    let w : ℕ := midWTap29OfMode s nn y36 (zLo14K2 γ z);
    let zHi1 : ℕ := (z30K2 γ z / 2 ^ 14 + v1 % 2 ^ 16) % 2 ^ 16;
    let zHi2 : ℕ := (zHi1 + v2 % 2 ^ 16) % 2 ^ 16;
    let zMid30 : ℕ := z30K2 γ z % 2 ^ 14 + 2 ^ 14 * zHi2;
    let q1 : ℕ := (z30K2 γ z / 2 ^ 14 + v1 % 2 ^ 16) / 2 ^ 16 + v1 / 2 ^ 16;
    let q2 : ℕ := (zHi1 + v2 % 2 ^ 16) / 2 ^ 16 + v2 / 2 ^ 16
    (((q1 : ZMod 2) + (q2 : ZMod 2) + (if (zMid30 + w).testBit 30 then (1 : ZMod 2) else 0) +
        (if s then (1 : ZMod 2) else 0)) =
      owK2PhaseBit3 pkgLM.v1Fin8 pkgLM.v2Fin8 ySample13 γ s nn sp1 sp2 nA pB eA z) ∧
    (∀ j : Fin 16, (if (zMid30 + w).testBit (14 + j.val) then (0 : ZMod 2) else 1) =
        owK2CoinSwap3 pkgLM.v1Fin8 pkgLM.v2Fin8 ySample13 γ s nn sp1 sp2 nA pB eA z ⟨8 + j.val,
            by omega⟩) := by
  intro y36 v1 v2 w zHi1 zHi2 zMid30 q1 q2
  obtain ⟨_, hFull, _, _⟩ := owmbu_two_leg_kick_collapse (z30K2 γ z) v1 v2 w
  set S := v1 * 2 ^ 14 + v2 * 2 ^ 14 + w
  set tM := t31ModTap29 pkgLM.v1Fin8 pkgLM.v2Fin8 s nn sp1 sp2
    (fin8Bin (openCoordDistSq nA eA)) (owB2Of3Port nn nA pB eA) y36 (zLo14K2 γ z)
  have hS31 : 2 ^ 31 * (S / 2 ^ 31) + tM = S := Nat.div_add_mod S (2 ^ 31)
  have hSumEq : zMid30 + w + 2 ^ 30 * (q1 + q2) = z30K2 γ z + tM + 2 ^ 31 * (S / 2 ^ 31) := by
    dsimp only [zMid30, zHi2, zHi1, q1, q2, S] at hFull hS31 ⊢; linarith
  refine ⟨?_, fun j ↦ ?_⟩
  · have hDivEq : (zMid30 + w) / 2 ^ 30 + (q1 + q2) =
        (z30K2 γ z + tM) / 2 ^ 30 + 2 * (S / 2 ^ 31) := by omega
    have hMod2 := congrArg (Nat.cast (R := ZMod 2)) hDivEq
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero,
      zero_mul, add_zero] at hMod2
    have htb2z (x : ℕ) :
        (if x.testBit 30 then (1 : ZMod 2) else 0) = ((x / 2 ^ 30 : ℕ) : ZMod 2) := by
      rw [show (30 : ℕ) = 0 + 30 from rfl, Nat.testBit_add, Nat.testBit_zero]
      generalize x / 2 ^ 30 = q
      conv_rhs => rw [← Nat.div_add_mod q 2]
      rcases Nat.mod_two_eq_zero_or_one q with h | h <;> simp [h, CharTwo.two_eq_zero]
    change (q1 : ZMod 2) + (q2 : ZMod 2) + (if (zMid30 + w).testBit 30 then 1 else 0) + _ =
      (if (tM + z30K2 γ z).testBit 30 then 1 else 0) + _
    rw [htb2z (zMid30 + w), htb2z (tM + z30K2 γ z), Nat.add_comm tM (z30K2 γ z),
      ← hMod2, add_comm ((q1 : ZMod 2) + (q2 : ZMod 2)) _]
  · have hzSp := z30K2_split14 γ z
    have hm : (zMid30 + w) / 2 ^ 14 % 2 ^ 16 =
        (zHi16Of24 z + (tM + zLo14K2 γ z) / 2 ^ 14) % 2 ^ 16 := by omega
    unfold owK2CoinSwap3
    dsimp only
    rw [_root_.ite_eq_right (by omega : ¬8 + j.val < 8), show 8 + j.val - 8 = j.val by omega,
      show owK2SHi14 pkgLM.v1Fin8 pkgLM.v2Fin8 ySample13 γ s nn sp1 sp2 nA pB eA z =
        (tM + zLo14K2 γ z) / 2 ^ 14 from rfl, ← hm,
      testBit_two_pow_sub_one_sub 16 _ j.val (Nat.mod_lt _ (by norm_num)) j.isLt,
      Nat.testBit_mod_two_pow, decide_eq_true j.isLt, Bool.true_and, Nat.add_comm 14 j.val,
      ← Nat.testBit_add]
    cases (zMid30 + w).testBit (j.val + 14) <;> rfl

def potExpectK2Mode (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) : PotExpectFn :=
    fun s nn sp1 sp2 nA nB eA eB ↦
    (2 ^ 24 : ℝ)⁻¹ * ∑ z : BitAssignment 24,
    if owK2PhaseBit3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA (if nn then nB else eB) eA z =
    1 then (-1 : ℝ) else 1
abbrev potExpectK2DualLegK17 : BitAssignment 17 → PotExpectFn :=
    potExpectK2Mode v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6)
theorem bitSign_eq_cast_ite_real (b : ZMod 2) : bitSign b = ((if b = 1 then (-1 : ℝ) else 1) : ℂ)
    := by
  rcases DynCircExt.bit_cases b with rfl | rfl <;> norm_num [bitSign]

theorem owK2PhaseBit3_avg_coin24 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) (s nn : Bool)
    (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256) : (2 ^ 24 : ℂ)⁻¹ * (∑ z : BitAssignment 24,
    bitSign (owK2PhaseBit3 v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA (if nn then nB else eB) eA z)) =
    (potExpectK2Mode v1Fn v2Fn ySample13 γ s nn sp1 sp2 nA nB eA eB : ℂ) := by
  simp_rw [bitSign_eq_cast_ite_real]; unfold potExpectK2Mode;
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Complex.ofReal_sum]; congr 1
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  split_ifs <;> norm_num

def owK2ReflPotSliceSpec24 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (γ : BitAssignment 17) :
    ReflPotSliceSpec24 (potExpectK2Mode v1Fn v2Fn ySample13 γ) :=
    ReflPotSliceSpec24.of3Port (owK2PhaseBit3 v1Fn v2Fn ySample13 γ)
    (owK2CoinSwap3 v1Fn v2Fn ySample13 γ) (owK2CoinSwap3_invol v1Fn v2Fn ySample13 γ)
    (owK2PhaseBit3_coinSwap v1Fn v2Fn ySample13 γ) (owK2PhaseBit3_avg_coin24 v1Fn v2Fn ySample13 γ)
def idxC13Of41 (j : Fin 13) : ℕ :=
    if j.val < 7 then 92 + j.val else if j.val < 11 then 81 + (j.val - 7) else if j.val =
    11 then 91 else 99
theorem idxC13Of41_bounds (j : Fin 13) : 81 ≤ idxC13Of41 j ∧ idxC13Of41 j < 100 := by
  unfold idxC13Of41; have := j.isLt; split_ifs <;> omega
theorem idxC13Of41_inj : Function.Injective idxC13Of41 := by
  intro a b h; unfold idxC13Of41 at h
  have := a.isLt; have := b.isLt
  apply Fin.ext; split_ifs at h <;> omega

def rC13Of41 {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) : QRegister 13 n :=
  r41.compose ⟨⟨fun j ↦ ⟨idxC13Of41 j, by have := (idxC13Of41_bounds j).2; omega⟩,
    fun a b e ↦ idxC13Of41_inj (congrArg Fin.val e)⟩⟩

theorem rC13Of41_ne_of_outside {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) {m : ℕ} (hm : m < 122 + Wp)
    (hout : m < 81 ∨ 100 ≤ m) (j : Fin 13) : r41 ⟨m, hm⟩ ≠ rC13Of41 r41 j :=
  r41_ne r41 hm _ (by have := idxC13Of41_bounds j; omega)

theorem rC13Of41_blk_ne_of_outside {Wp a b n : ℕ} (r41 : QRegister (122 + Wp) n)
    {h : a + b ≤ 122 + Wp} (i : Fin b) (hout : a + i.val < 81 ∨ 100 ≤ a + i.val)
    (j : Fin 13) : (r41.compose (QRegister.block a b h)) i ≠ rC13Of41 r41 j :=
  r41_blk_ne_wire r41 i _ (by have := idxC13Of41_bounds j; omega)

theorem rC13Of41_lo7 {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (b : Fin 7) :
    rC13Of41 r41 ⟨b.val, by omega⟩ = r41 ⟨92 + b.val, by omega⟩ :=
  congrArg r41.wires (Fin.ext (by
    change idxC13Of41 ⟨b.val, _⟩ = 92 + b.val
    unfold idxC13Of41; simp [b.isLt]))

theorem rC13Of41_12 {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) :
    rC13Of41 r41 ⟨12, by omega⟩ = r41 ⟨99, by omega⟩ :=
  congrArg r41.wires (Fin.ext (by change idxC13Of41 ⟨12, by omega⟩ = 99; decide))

theorem rC13Of41_r41Of24_lt11 {Wp n : ℕ} (r : QRegister (105 + Wp) n)
    (rCoin : QRegister 17 n) (hd : r.DisjointWires rCoin) (j : Fin 11) :
    rC13Of41 (r41Of24 r rCoin hd) ⟨j.val, by omega⟩ = rCoin ⟨j.val, by omega⟩ := by
  change f41Of24 r rCoin ⟨idxC13Of41 ⟨j.val, by omega⟩, _⟩ = _
  dsimp only [f41Of24, idxC13Of41]
  split_ifs <;> first | omega |
    exact congrArg rCoin.wires (Fin.ext (by have := j.isLt; dsimp; omega))

theorem rC13Of41_r41Of24_11 {Wp n : ℕ} (r : QRegister (105 + Wp) n)
    (rCoin : QRegister 17 n) (hd : r.DisjointWires rCoin) :
    rC13Of41 (r41Of24 r rCoin hd) ⟨11, by omega⟩ = rPotBCoin24 r ⟨0, by omega⟩ := by
  change f41Of24 r rCoin ⟨91, by omega⟩ = r ⟨81 + 0, by omega⟩
  dsimp only [f41Of24]; split_ifs <;> first | rfl | omega

theorem rC13Of41_r41Of24_12 {Wp n : ℕ} (r : QRegister (105 + Wp) n)
    (rCoin : QRegister 17 n) (hd : r.DisjointWires rCoin) :
    rC13Of41 (r41Of24 r rCoin hd) ⟨12, by omega⟩ = rPotBCoin24 r ⟨1, by omega⟩ :=
  (rC13Of41_12 (r41Of24 r rCoin hd)).trans
    ((r41Of24_hi99 r rCoin hd (m := 99) (by omega) (by omega)).trans
      (congrArg r.wires (Fin.ext (by dsimp [rPotBCoin24]))))

theorem r41Of24_zMid6 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (i : Fin 6) :
    r41Of24 r rCoin hd ⟨100 + i.val, by omega⟩ = rPotBCoin24 r ⟨2 + i.val, by omega⟩ :=
  (r41Of24_hi99 r rCoin hd (by omega) (by omega)).trans
    (congrArg r.wires (Fin.ext (by dsimp [rPotBCoin24]; omega)))

theorem w11OfReg13_rC13Of41 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (δ : BitAssignment n) :
    w11OfReg13 (rC13Of41 (r41Of24 r rCoin hd)) δ = w11Sub63 (fun j ↦ δ (rCoin j)) := by
  apply Fin.ext; dsimp only [w11OfReg13, w11Sub63]
  exact congrArg (natOfZModBits 11)
    (funext fun j ↦ congrArg δ (rC13Of41_r41Of24_lt11 r rCoin hd j))

theorem x13OfReg13_rC13Of41 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (δ : BitAssignment n) :
    x13OfReg13 (rC13Of41 (r41Of24 r rCoin hd)) δ = x13K2 (fun j ↦ δ (rCoin j))
    (fun k ↦ δ (rPotBCoin24 r k)) := by
  unfold x13OfReg13 x13K2;
  rw [natOfZModBits_split 11 2, natOfZModBits_split 1 1, natOfZModBits_one_eq,
      natOfZModBits_one_eq]; have hw :=
                               congrArg Fin.val (w11OfReg13_rC13Of41 r rCoin hd δ);
                               dsimp only [w11OfReg13] at hw; rw [hw]; dsimp only;
                               simp only [rC13Of41_r41Of24_11 r rCoin hd,
                               rC13Of41_r41Of24_12 r rCoin hd]; ring
def zLo14MuxK2 {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n) : ℕ :=
  (df8Of13 (x13OfReg13 (rC13Of41 r41) β)).val +
    2 ^ 8 * natOfZModBits 6 (fun i ↦ β (r41 ⟨100 + i.val, by omega⟩))

theorem zLo14MuxK2_lt {Wp n : ℕ} (r41 : QRegister (122 + Wp) n) (β : BitAssignment n) :
    zLo14MuxK2 r41 β < 2 ^ 14 := by
  unfold zLo14MuxK2; have h1 := (df8Of13 (x13OfReg13 (rC13Of41 r41) β)).isLt
  have h2 := natOfZModBits_lt 6 (fun i : Fin 6 ↦ β (r41 ⟨100 + i.val, by omega⟩))
  omega

theorem zLo14MuxK2_r41Of24 {Wp n : ℕ} (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin) (δ : BitAssignment n) : zLo14MuxK2 (r41Of24 r rCoin hd) δ =
    zLo14K2 (fun j ↦ δ (rCoin j)) (fun k ↦ δ (rPotBCoin24 r k)) := by
  unfold zLo14MuxK2 zLo14K2 zMid6Of24; rw [x13OfReg13_rC13Of41]
  refine congrArg (_ + 2 ^ 8 * ·) (congrArg (natOfZModBits 6) (funext fun i ↦ congrArg δ ?_))
  exact r41Of24_zMid6 r rCoin hd i

def y36MuxK2 {Wp n : ℕ} (isCsel : Bool) (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ)
    (r41 : QRegister (122 + Wp) n) (β : BitAssignment n) : ℕ :=
    if potBGateActive isCsel r41 β then ySample13 (β (wPotBIsNN r41) == 1) (muxD2Val r41 β)
    (w11OfReg13 (rC13Of41 r41) β) (o9Of13 (x13OfReg13 (rC13Of41 r41) β)) else 0
def midSumMuxK2 {Wp n : ℕ} (isCsel : Bool) (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) : ℕ :=
  let zLo := zLo14MuxK2 r41 β
  (zLo + 2 ^ 14 * finBitsVal z16) +
    midWTap29OfMode (β (wPotBIsScreen r41) == 1) (β (wPotBIsNN r41) == 1)
      (y36MuxK2 isCsel ySample13 r41 β) zLo

def z16AfterMidK2 {Wp n : ℕ} (isCsel : Bool) (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (β : BitAssignment n) : Fin 16 →
    ZMod 2 := fun j ↦
    if potBGateActive isCsel r41 β then if (midSumMuxK2 isCsel ySample13 r41 z16 β).testBit (14 +
    j.val) then 0 else 1 else z16 j
def phAfterMidK2 {Wp n : ℕ} (isCsel : Bool) (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ)
    (r41 : QRegister (122 + Wp) n) (z16 : Fin 16 → ZMod 2) (phPrev : ZMod 2) (β : BitAssignment n) :
    ZMod 2 :=
    phPrev + (if potBGateActive isCsel r41 β then (1 : ZMod 2) else 0) *
    ((if (midSumMuxK2 isCsel ySample13 r41 z16 β).testBit 30 then (1 : ZMod 2) else 0) +
    (if β (wPotBIsScreen r41) == 1 then (1 : ZMod 2) else 0))
theorem mux_k2_final_eq_potRefl24
    {isU10 : Bool} {Wp tLeg1 tLeg2 kMidLM tMidLM n : ℕ}
    {ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ}
    (isCsel : Bool)
    (pkgLM : OWLegsMidPkg isU10 tLeg1 tLeg2 kMidLM tMidLM)
    (r : QRegister (105 + Wp) n) (rCoin : QRegister 17 n)
    (hd : r.DisjointWires rCoin)
    (st : BitAssignment n → BitAssignment n)
    {δ : BitAssignment n} (hVF24 : ValidPotBFlags24 r (st δ)) :
    let r41 := r41Of24 r rCoin hd
    let z16Init := fun j : Fin 16 ↦ st δ (rMuxZ16 r41 j)
    let z16L1 := z16AddVal z16Init (v1Mux isCsel pkgLM r41 (st δ));
    let z16L2 := z16AddVal z16L1 (v2Mux isCsel pkgLM r41 (st δ));
    let phL2 :=
        phAddVal z16Init (v1Mux isCsel pkgLM r41 (st δ)) +
        phAddVal z16L1 (v2Mux isCsel pkgLM r41 (st δ))
    let z16M := z16AfterMidK2 isCsel ySample13 r41 z16L2 (st δ)
    let phM := phAfterMidK2 isCsel ySample13 r41 z16L2 phL2 (st δ)
    let sliceK := owK2ReflPotSliceSpec24 pkgLM.v1Fin8 pkgLM.v2Fin8 ySample13
    writeReg (st δ) (rMuxZ16 r41) z16M =
      potReflPortBSt24 (fun γ ↦ (sliceK γ).coinSwap) isCsel r rCoin st δ ∧
    phM = potReflPortBPh0_24 (fun γ ↦ (sliceK γ).phaseBit) isCsel r rCoin st δ := by
  intro r41 z16Init z16L1 z16L2 phL2 z16M phM sliceK;
  have hgEq := potBGateActive_r41Of24 isCsel r rCoin hd (st δ);
  have hVF41 := validPotBFlags_r41Of24 r rCoin hd hVF24; have hBlk := r41Of24_blocks r rCoin hd
  have hgMul : (if isCsel then st δ (wPotB24LocQ r) * st δ (wPotB24IsPot r)
      else st δ (wPotB24IsPot r)) = if potB24GateActive isCsel r (st δ) then 1 else 0 := by
    unfold potB24GateActive
    rcases DynCircExt.bit_cases (st δ (wPotB24LocQ r)) with h0 | h0 <;>
      rcases DynCircExt.bit_cases (st δ (wPotB24IsPot r)) with h2 | h2 <;>
      cases isCsel <;> simp [h0, h2]
  cases hgAct : potB24GateActive isCsel r (st δ)
  · have hg41 : potBGateActive isCsel r41 (st δ) = false := hgEq.trans hgAct
    have hzM : z16M = z16Init := funext fun j ↦ by
      simp [z16M, z16AfterMidK2, z16L2, z16L1, v1Mux, v2Mux, hg41, z16AddVal_zero]
    refine ⟨?_, by simp [potReflPortBPh0_24, phM, phAfterMidK2, phL2, z16L1, v1Mux, v2Mux,
      phAddVal_zero, hgMul, hgAct, hg41]⟩
    simp only [potReflPortBSt24, hgAct, Bool.false_eq_true, ↓reduceIte, hzM]
    exact writeReg_self_z16 r41 (st δ)
  · have hg41 : potBGateActive isCsel r41 (st δ) = true := hgEq.trans hgAct
    set γ : BitAssignment 17 := fun j ↦ st δ (rCoin j)
    set z24 : BitAssignment 24 := fun k ↦ st δ (rPotBCoin24 r k)
    have hW1 : wPotBIsScreen r41 = wPotB24IsScreen r := r41Of24_lt81 r rCoin hd (m := 1) (by omega)
    have hW4 : wPotBIsNN r41 = wPotB24IsNN r := r41Of24_lt81 r rCoin hd (m := 4) (by omega)
    have hW5 : wPotBSp1B0 r41 = wPotB24Sp1B0 r := r41Of24_lt81 r rCoin hd (m := 5) (by omega)
    have hW6 : wPotBSp1B1 r41 = wPotB24Sp1B1 r := r41Of24_lt81 r rCoin hd (m := 6) (by omega)
    have hW7 : wPotBSp2B0 r41 = wPotB24Sp2B0 r := r41Of24_lt81 r rCoin hd (m := 7) (by omega)
    have hW8 : wPotBSp2B1 r41 = wPotB24Sp2B1 r := r41Of24_lt81 r rCoin hd (m := 8) (by omega)
    have hv1 : v1Mux isCsel pkgLM r41 (st δ) = pkgLM.v1Fin8 (st δ (wPotB24IsScreen r) == 1)
        (st δ (wPotB24IsNN r) == 1) (speciesOfBits2 (st δ (wPotB24Sp1B0 r)) (st δ (wPotB24Sp1B1 r)))
        (fin8Bin (openCoordDistSq (coordOfReg24 (rPotB24NucA r) (st δ))
        (coordOfReg24 (rPotB24ElecA r) (st δ))))
        := by unfold v1Mux; simp only [hg41, ↓reduceIte]; rw [hW1, hW4, hW5, hW6, hBlk.1, hBlk.2.1]
    have hv2 : v2Mux isCsel pkgLM r41 (st δ) = pkgLM.v2Fin8 (st δ (wPotB24IsScreen r) == 1)
        (st δ (wPotB24IsNN r) == 1) (speciesOfBits2 (st δ (wPotB24Sp2B0 r)) (st δ (wPotB24Sp2B1 r)))
        (owB2Of3Port (st δ (wPotB24IsNN r) == 1) (coordOfReg24 (rPotB24NucA r) (st δ))
        (coordOfReg24 (rPotB24PortB r) (st δ)) (coordOfReg24 (rPotB24ElecA r) (st δ)))
        := by
      unfold v2Mux; simp only [hg41, ↓reduceIte];
      rw [hW1, hW4, hW7, hW8, hBlk.1, hBlk.2.1, hBlk.2.2]
    have hyEq : y36MuxK2 isCsel ySample13 r41 (st δ) = ySample13 (st δ (wPotB24IsNN r) == 1)
        (sectorDist3DSq3 (st δ (wPotB24IsScreen r) == 1) (st δ (wPotB24IsNN r) == 1)
        (coordOfReg24 (rPotB24NucA r) (st δ)) (coordOfReg24 (rPotB24PortB r) (st δ))
        (coordOfReg24 (rPotB24ElecA r) (st δ))) (w11Sub63 γ) (o9Of13 (x13K2 γ z24))
        := by
      unfold y36MuxK2; simp only [hg41, ↓reduceIte];
      rw [muxD2Val_eq_sector r41 hVF41, w11OfReg13_rC13Of41 r rCoin hd (st δ),
          x13OfReg13_rC13Of41 r rCoin hd (st δ), hW1, hW4, hBlk.1, hBlk.2.1, hBlk.2.2]
    have hzInitVal : finBitsVal z16Init = z30K2 γ z24 / 2 ^ 14 := by
      rw [finBitsVal_eq_natOfZModBits, ← (z30K2_lo_hi γ z24).2]; unfold zHi16Of24
      exact congrArg (natOfZModBits 16) (funext fun j ↦ congrArg (st δ) (r41Of24_z16 r rCoin hd j))
    have hzLoEq : zLo14MuxK2 r41 (st δ) = zLo14K2 γ z24 := zLo14MuxK2_r41Of24 r rCoin hd (st δ);
    have hzLoVal : zLo14MuxK2 r41 (st δ) = z30K2 γ z24 % 2 ^ 14 :=
        hzLoEq.trans (z30K2_lo_hi γ z24).1
    have hzL1Val : finBitsVal z16L1 = (z30K2 γ z24 / 2 ^ 14 +
        v1Mux isCsel pkgLM r41 (st δ) % 2 ^ 16) % 2 ^ 16
        := by dsimp only [z16L1]; rw [finBitsVal_z16AddVal, hzInitVal]
    have hzL2Val : finBitsVal z16L2 = (finBitsVal z16L1 +
        v2Mux isCsel pkgLM r41 (st δ) % 2 ^ 16) % 2 ^ 16
        := by dsimp only [z16L2]; rw [finBitsVal_z16AddVal]
    obtain ⟨hColPh, hColZ⟩ :=
        owK2_two_leg_collapse pkgLM ySample13 γ (st δ (wPotB24IsScreen r) == 1)
        (st δ (wPotB24IsNN r) == 1) (speciesOfBits2 (st δ (wPotB24Sp1B0 r)) (st δ (wPotB24Sp1B1 r)))
        (speciesOfBits2 (st δ (wPotB24Sp2B0 r)) (st δ (wPotB24Sp2B1 r)))
        (coordOfReg24 (rPotB24NucA r) (st δ)) (coordOfReg24 (rPotB24PortB r) (st δ))
        (coordOfReg24 (rPotB24ElecA r) (st δ)) z24; rw [(z30K2_lo_hi γ z24).1] at hColPh hColZ
    have hMidSumEq : midSumMuxK2 isCsel ySample13 r41 z16L2 (st δ) = (z30K2 γ z24 % 2 ^ 14 +
        2 ^ 14 * (((z30K2 γ z24 / 2 ^ 14 + v1Mux isCsel pkgLM r41 (st δ) % 2 ^ 16) % 2 ^ 16 +
        v2Mux isCsel pkgLM r41 (st δ) % 2 ^ 16) % 2 ^ 16)) +
        midWTap29OfMode (st δ (wPotB24IsScreen r) == 1) (st δ (wPotB24IsNN r) == 1)
        (y36MuxK2 isCsel ySample13 r41 (st δ)) (z30K2 γ z24 % 2 ^ 14) := by
      unfold midSumMuxK2; dsimp only
      rw [hzL2Val, hzL1Val, hW1, hW4, hzLoVal]
    have hPortIf (pB : Fin 3 → Fin 256) :
        (if (st δ (wPotB24IsNN r) == 1) then (if (st δ (wPotB24IsNN r) == 1) then pB else 0)
         else (if (st δ (wPotB24IsNN r) == 1) then 0 else pB)) = pB := by
      cases (st δ (wPotB24IsNN r) == 1) <;> rfl
    refine ⟨?_, ?_⟩
    · simp only [potReflPortBSt24, hgAct, ↓reduceIte]
      rw [show potOraclePortB24CoinEval (fun s' nn' sp1' sp2' nA' nB' eA' eB' z' ↦
          (sliceK γ).coinSwap s' nn' sp1' sp2' nA' nB' eA' eB' z') r (st δ) = _ from
        congrArg (fun pB ↦ owK2CoinSwap3 pkgLM.v1Fin8 pkgLM.v2Fin8 ySample13 γ _ _ _ _ _ pB _ z24)
          (hPortIf _)]
      funext w
      by_cases hwC : ∃ k : Fin 24, rPotBCoin24 r k = w
      · obtain ⟨k, rfl⟩ := hwC
        rw [writeReg_apply_reg]
        by_cases hk8 : k.val < 8
        · rw [owK2CoinSwap3_lo _ _ _ _ _ _ _ _ _ _ _ _ hk8,
            writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ by
              have hv := congrArg Fin.val
                (r.wires.injective ((r41Of24_z16 r rCoin hd j).symm.trans hj))
              dsimp only [QRegister.block_apply_val] at hv; omega]
        · let j0 : Fin 16 := ⟨k.val - 8, by have := k.isLt; omega⟩
          have hkEq : k = ⟨8 + j0.val, by omega⟩ := Fin.ext (by dsimp [j0]; omega)
          rw [show rPotBCoin24 r k = rMuxZ16 r41 j0 from hkEq ▸ (r41Of24_z16 r rCoin hd j0).symm,
            writeReg_apply_reg, hkEq]
          simp only [z16M, z16AfterMidK2, hg41, ↓reduceIte, hMidSumEq, hv1, hv2, hyEq]
          exact hColZ j0
      · rw [writeReg_apply_of_not_mem _ (rPotBCoin24 r) _ w fun ⟨k, hk⟩ ↦ hwC ⟨k, hk⟩,
          writeReg_apply_of_not_mem _ (rMuxZ16 r41) _ w fun ⟨j, hj⟩ ↦
            hwC ⟨⟨8 + j.val, by omega⟩, (r41Of24_z16 r rCoin hd j).symm.trans hj⟩]
    · simp only [potReflPortBPh0_24, hgMul, hgAct, ↓reduceIte, one_mul]
      rw [show potOraclePortB24BitEval (fun s' nn' sp1' sp2' nA' nB' eA' eB' z' ↦
          (sliceK γ).phaseBit s' nn' sp1' sp2' nA' nB' eA' eB' z') r (st δ) = _ from
        congrArg (fun pB ↦ owK2PhaseBit3 pkgLM.v1Fin8 pkgLM.v2Fin8 ySample13 γ _ _ _ _ _ pB _ z24)
          (hPortIf _)]
      simp only [phM, phAfterMidK2, phL2, phAddVal, hg41, ↓reduceIte, one_mul, hMidSumEq,
        hzL1Val, hzInitVal, hW1, hv1, hv2, hyEq, ← add_assoc]
      exact hColPh
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWCore (midOW_lt0 midOW_lt1 midOW_ltY
    midOW_ltZ midOW_ltZHi midOW_ltCln)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt (xorPortB41NotScr
    xorPortB41NotScr_outside xorPortB41NotScr_muxD2Val)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29 (MidOWTap29Pkg
    midOWTotalSumTap29 midOWZBitsTap29 midOWPostStTap29 midOWPhaseTap29)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (CoulOWScrPkg13 whiten13Tree
    whiten13Tree_check stepCB_whiten13_lo7 stepCB_whiten13_hi7)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (stepCB_whiten13_out)
theorem xorPortB41NotScr_midInvar_k2 {Wp n : ℕ} (isCsel : Bool)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) (r41 : QRegister (122 + Wp) n)
    (z16 : Fin 16 → ZMod 2) (phPrev : ZMod 2) (β : BitAssignment n) :
    z16AfterMidK2 isCsel ySample13 r41 z16 (xorPortB41NotScr r41 β) =
    z16AfterMidK2 isCsel ySample13 r41 z16 β ∧
    phAfterMidK2 isCsel ySample13 r41 z16 phPrev (xorPortB41NotScr r41 β) =
    phAfterMidK2 isCsel ySample13 r41 z16 phPrev β := by
  let β' := xorPortB41NotScr r41 β
  have hOut (m : ℕ) (hm : m < 122 + Wp) (ho : m < 57 ∨ 81 ≤ m) :=
    xorPortB41NotScr_outside r41 β hm ho
  have hS : β' (wPotBIsScreen r41) = β (wPotBIsScreen r41) := hOut 1 (by omega) (.inl (by omega))
  have hN : β' (wPotBIsNN r41) = β (wPotBIsNN r41) := hOut 4 (by omega) (.inl (by omega))
  have hG : potBGateActive isCsel r41 β' = potBGateActive isCsel r41 β := by
    unfold potBGateActive
    rw [show β' (wPotBLocQ r41) = _ from hOut 0 (by omega) (.inl (by omega)),
      show β' (wPotBIsPot r41) = _ from hOut 2 (by omega) (.inl (by omega))]
  have hC13 (j : Fin 13) : β' (rC13Of41 r41 j) = β (rC13Of41 r41 j) := by
    have := idxC13Of41_bounds j
    exact hOut (idxC13Of41 j) (by omega) (.inr (by omega))
  have hw11 : w11OfReg13 (rC13Of41 r41) β' = w11OfReg13 (rC13Of41 r41) β := by
    simp [w11OfReg13, hC13]
  have hx13 : x13OfReg13 (rC13Of41 r41) β' = x13OfReg13 (rC13Of41 r41) β := by
    simp [x13OfReg13, hC13]
  have hZLo : zLo14MuxK2 r41 β' = zLo14MuxK2 r41 β :=
    congrArg₂ (· + 2 ^ 8 * ·) (congrArg (fun x ↦ (df8Of13 x).val) hx13)
      (congrArg (natOfZModBits 6) (funext fun i ↦ hOut (100 + i.val) (by omega) (.inr (by omega))))
  have hSum : midSumMuxK2 isCsel ySample13 r41 z16 β' = midSumMuxK2 isCsel ySample13 r41 z16 β := by
    unfold midSumMuxK2 y36MuxK2
    rw [hZLo, hS, hN, hG, hw11, hx13, xorPortB41NotScr_muxD2Val r41 β]
  change z16AfterMidK2 isCsel ySample13 r41 z16 β' = _ ∧
    phAfterMidK2 isCsel ySample13 r41 z16 phPrev β' = _
  exact ⟨funext fun j ↦ by unfold z16AfterMidK2; rw [hG, hSum],
    by unfold phAfterMidK2; rw [hG, hSum, hS]⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2

namespace QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs
open PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ClusterPotSlice (nucP elecP)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt
    natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.TelescopeSlice (pairOpenDistSq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Sh14P5 (y36PopBernNoClampS14
    checkPopBernCtrlRangesNoClamp ctrl_bounds_of_ranges_noClamp pre5OfNat pre5OfFin8)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (df8Of13 o9Of13 x13OfW11U01
    ySampleK2 ySampleK2_eq_proxy)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29 (midWTap29)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2 (midWTap29OfMode x13K2
    zMid6Of24 zLo14K2 z30K2 z30K2_split14 zLo14K2_lt t31ModTap29 owK2PhaseBit3)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2 (potExpectK2Mode
    potExpectK2DualLegK17)
attribute [local irreducible] systemQubits_frozen word512DualLegLo6
theorem natOfZModBits_one_val (f : Fin 1 → ZMod 2) : natOfZModBits 1 f = (f 0).val := by
  have hlt := natOfZModBits_lt 1 f
  have htb := natOfZModBits_testBit_lt f (by omega : 0 < 1)
  have hf0 : (⟨0, by omega⟩ : Fin 1) = 0 := rfl
  rw [Nat.testBit_zero, hf0] at htb
  rcases DynCircExt.bit_cases (f 0) with h0 | h1
  · rw [h0] at htb ⊢
    have hbmod : natOfZModBits 1 f % 2 ≠ 1 := by intro hm; rw [hm] at htb; revert htb; decide
    change natOfZModBits 1 f = 0; omega
  · rw [h1] at htb ⊢;
    have hbmod : natOfZModBits 1 f % 2 = 1 :=
        of_decide_eq_true htb; change natOfZModBits 1 f = 1; omega
theorem natOfZModBits_eq_sum_val : ∀ (m : ℕ) (f : Fin m → ZMod 2),
    natOfZModBits m f = ∑ k : Fin m, (f k).val * 2 ^ k.val
  | 0, f => by
      have := natOfZModBits_lt 0 f
      simp only [Finset.univ_eq_empty, Finset.sum_empty]; omega
  | m + 1, f => by
      rw [natOfZModBits_split m 1 f, natOfZModBits_eq_sum_val m, natOfZModBits_one_val,
        Fin.sum_univ_castSucc]
      simp_rw [show ∀ k : Fin m, (⟨k.val, by omega⟩ : Fin (m + 1)) = k.castSucc from
          fun _ ↦ Fin.ext rfl,
        show (⟨m + (0 : Fin 1).val, by omega⟩ : Fin (m + 1)) = Fin.last m from Fin.ext (by simp)]
      simp only [Fin.val_last, Fin.val_castSucc]; ring
theorem testBit30_mod31_add (a b : ℕ) : (a % 2 ^ 31 + b).testBit 30 = (a + b).testBit 30 := by
  rw [show (30 : ℕ) = 0 + 30 from rfl, Nat.testBit_add, Nat.testBit_add, Nat.testBit_zero,
    Nat.testBit_zero, show a + b = (a % 2 ^ 31 + b) + 2 ^ 30 * (2 * (a / 2 ^ 31)) by
      have := Nat.div_add_mod a (2 ^ 31)
      linarith,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.add_mul_mod_self_left]

theorem testBit16_mod17_add (a b : ℕ) : (a % 131072 + b).testBit 16 = (a + b).testBit 16 := by
  rw [show (16 : ℕ) = 0 + 16 from rfl, Nat.testBit_add, Nat.testBit_add, Nat.testBit_zero,
    Nat.testBit_zero, show a + b = (a % 131072 + b) + 2 ^ 16 * (2 * (a / 131072)) by omega,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.add_mul_mod_self_left]

theorem testBit30_t31ModTap29_eq_q14 (s nn : Bool) (sp1 sp2 : Fin 4) (b1 b2 : Fin 8)
    (y36 zLo14 zHi16 : ℕ) : (t31ModTap29 v1Fin8DualLeg v2Fin8DualLeg s nn sp1 sp2 b1 b2 y36 zLo14 +
    (zLo14 + 2 ^ 14 * zHi16)).testBit 30 =
    (((v1Fin8DualLeg s nn sp1 b1 + v2Fin8DualLeg s nn sp2 b2 + (midWTap29OfMode s nn y36 zLo14 +
    zLo14) / 16384) % 131072) + zHi16).testBit 16 := by
  unfold t31ModTap29; rw [testBit30_mod31_add, testBit16_mod17_add]
  conv_lhs => rw [show (v1Fin8DualLeg s nn sp1 b1 * 2 ^ 14 + v2Fin8DualLeg s nn sp2 b2 * 2 ^ 14 +
        midWTap29OfMode s nn y36 zLo14) + (zLo14 + 2 ^ 14 * zHi16) =
      (midWTap29OfMode s nn y36 zLo14 + zLo14) +
        16384 * (v1Fin8DualLeg s nn sp1 b1 + v2Fin8DualLeg s nn sp2 b2 + zHi16) by ring,
    show (30 : ℕ) = 16 + 14 from rfl]
  rw [Nat.testBit_add, show (2 ^ 14 : ℕ) = 16384 from rfl, Nat.add_mul_div_left _ _ (by norm_num)]
  exact congrArg (fun x : ℕ ↦ x.testBit 16) (by ring)

def cShift14DualLeg (isScr isNN : Bool) (sp1 : Fin 4) (b1 b2 : Fin 8) : ℤ :=
    if isScr then if isNN then (-865 + dNNDualLegPre5 (pre5OfFin8 b1)) +
    (-865 + dNNDualLegPre5 (pre5OfFin8 b2)) else (5580 + dEEDualLegPre5 (pre5OfFin8 b1)) +
    (5580 + dEEDualLegPre5 (pre5OfFin8 b2)) else qEN0DualLegPre5 +
    dENDualLegPre5 sp1 (pre5OfFin8 b1)
theorem cShift14DualLeg_mul16384 : (∀ sp1 b1 b2, 16384 * cShift14DualLeg true false sp1 b1 b2 =
    cEE1Fin8DualLeg b1 + cEE2Fin8DualLeg b2) ∧ (∀ sp1 b1 b2, 16384 *
    cShift14DualLeg true true sp1 b1 b2 = cNNFin8DualLeg b1 + cNNFin8DualLeg b2) ∧
    (∀ sp1 b1 b2, 16384 * cShift14DualLeg false false sp1 b1 b2 = cENFin8DualLeg sp1 b1) := by
  refine ⟨fun _ _ _ ↦ ?_, fun _ _ _ ↦ ?_, fun _ _ _ ↦ ?_⟩
  · unfold cShift14DualLeg cEE1Fin8DualLeg cEE2Fin8DualLeg cEE1Sh14P5DualLeg cEE2Sh14P5DualLeg
    simp only [↓reduceIte, Bool.false_eq_true]; ring
  · unfold cShift14DualLeg cNNFin8DualLeg cNNSh14P5DualLeg
    simp only [↓reduceIte]; ring
  · unfold cShift14DualLeg cENFin8DualLeg cENSh14P5DualLeg
    simp only [Bool.false_eq_true, ↓reduceIte]; ring

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem t1b_shift14_mod_cert : (∀ sp1 sp2 b1 b2, (((v1Fin8DualLeg true false sp1 b1 : ℤ) +
    (v2Fin8DualLeg true false sp2 b2 : ℤ)) -
    (32768 - cShift14DualLeg true false sp1 b1 b2)) % 131072 = 0) ∧ (∀ sp1 sp2 b1 b2,
    (((v1Fin8DualLeg true true sp1 b1 : ℤ) + (v2Fin8DualLeg true true sp2 b2 : ℤ)) -
    (32768 - cShift14DualLeg true true sp1 b1 b2)) % 131072 = 0) ∧ (∀ sp1 sp2 b1 b2,
    (((v1Fin8DualLeg false false sp1 b1 : ℤ) + (v2Fin8DualLeg false false sp2 b2 : ℤ)) -
    (32768 - cShift14DualLeg false false sp1 b1 b2)) % 131072 = 0) := by decide +kernel
theorem q16Mod_eq_of_q14_nonWrap {v1 v2 q14 : ℕ} {cShift : ℤ}
    (hMod : (((v1 : ℤ) + (v2 : ℤ)) - (32768 - cShift)) % 131072 = 0)
    (hq : |(q14 : ℤ) - cShift| ≤ 32768) :
    (((v1 + v2 + q14) % 131072 : ℕ) : ℤ) = 32768 + (q14 : ℤ) - cShift ∧
    (v1 + v2 + q14) % 131072 ≤ 2 ^ 16 := by
  rw [abs_le] at hq
  set S : ℕ := v1 + v2 + q14
  have hDZ : (131072 : ℤ) * ↑(S / 131072) + ↑(S % 131072) = v1 + v2 + q14 := by
    exact_mod_cast Nat.div_add_mod S 131072
  have hRZ : (0 : ℤ) ≤ ↑(S % 131072) ∧ ((S % 131072 : ℕ) : ℤ) < 131072 :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.mod_lt S (by norm_num)⟩
  rw [show (2 ^ 16 : ℕ) = 65536 from rfl]; omega
def mergeLo8 (u0 u1 : Fin 2) (u6 : Fin 64) : BitAssignment 8 := fun j ↦
    if j.val = 0 then equivBitZMod2.symm u0 else if j.val =
    1 then equivBitZMod2.symm u1 else if u6.val.testBit (j.val - 2) then 1 else 0
def equivLo8 : (Fin 2 × Fin 2 × Fin 64) ≃ BitAssignment 8 where
  toFun p := mergeLo8 p.1 p.2.1 p.2.2
  invFun lo :=
    (equivBitZMod2 (lo ⟨0, by omega⟩),
     equivBitZMod2 (lo ⟨1, by omega⟩),
     ⟨natOfZModBits 6 (fun i ↦ lo ⟨2 + i.val, by omega⟩), natOfZModBits_lt 6 _⟩)
  left_inv p := by
    rcases p with ⟨u0, u1, u6⟩
    have h0 : equivBitZMod2 (mergeLo8 u0 u1 u6 ⟨0, by omega⟩) = u0 :=
      equivBitZMod2.apply_symm_apply u0
    have h1 : equivBitZMod2 (mergeLo8 u0 u1 u6 ⟨1, by omega⟩) = u1 :=
      equivBitZMod2.apply_symm_apply u1
    have hFn : (fun i : Fin 6 ↦ mergeLo8 u0 u1 u6 ⟨2 + i.val, by omega⟩) =
        fun i : Fin 6 ↦ if u6.val.testBit i.val then (1 : ZMod 2) else 0 := by
      funext i
      have hn0 : ¬(2 + i.val = 0) := by omega
      have hn1 : ¬(2 + i.val = 1) := by omega
      have hi : 2 + i.val - 2 = i.val := by omega
      simp only [mergeLo8, hn0, hn1, ↓reduceIte, hi]
    have h6 : (⟨natOfZModBits 6 (fun i ↦ mergeLo8 u0 u1 u6 ⟨2 + i.val, by omega⟩),
        natOfZModBits_lt 6 _⟩ : Fin 64) = u6 := by
      apply Fin.ext; dsimp only
      rw [hFn, natOfZModBits_of_testBit 6 u6.val, Nat.mod_eq_of_lt (show u6.val <
          2 ^ 6 from u6.isLt)]
    exact Prod.ext h0 (Prod.ext h1 h6)
  right_inv lo := by
    funext j; dsimp only [mergeLo8]
    by_cases hj0 : j.val = 0
    · simp only [hj0, ↓reduceIte]
      have hjEq : (⟨0, by omega⟩ : Fin 8) = j := Fin.ext hj0.symm
      rw [equivBitZMod2.symm_apply_apply, hjEq]
    · simp only [hj0, ↓reduceIte]
      by_cases hj1 : j.val = 1
      · simp only [hj1, ↓reduceIte]
        have hjEq : (⟨1, by omega⟩ : Fin 8) = j := Fin.ext hj1.symm
        rw [equivBitZMod2.symm_apply_apply, hjEq]
      · simp only [hj1, ↓reduceIte]
        let i : Fin 6 := ⟨j.val - 2, by have := j.isLt; omega⟩
        set v6 := natOfZModBits 6 (fun q : Fin 6 ↦ lo ⟨2 + q.val, by omega⟩)
        have hBits := finBitsVal_inj (m := 6)
          (f := fun q : Fin 6 ↦ if v6.testBit q.val then (1 : ZMod 2) else 0)
          (g := fun q : Fin 6 ↦ lo ⟨2 + q.val, by omega⟩) <| by
            rw [finBitsVal_eq_natOfZModBits, finBitsVal_eq_natOfZModBits,
                natOfZModBits_of_testBit 6 v6]; exact Nat.mod_eq_of_lt (natOfZModBits_lt 6 _)
        have hi := congrFun hBits i; dsimp only [i] at hi
        have hjEq : (⟨2 + (j.val - 2), by omega⟩ : Fin 8) = j := Fin.ext (by dsimp; omega)
        rw [hjEq] at hi; exact hi
def splitEquiv24 : (Fin 16 ⊕ Fin 8) ≃ Fin 24 where
  toFun := Sum.elim (fun k ↦ ⟨8 + k.val, by omega⟩) (fun j ↦ ⟨j.val, by omega⟩)
  invFun i := if h : i.val < 8 then Sum.inr ⟨i.val, h⟩ else Sum.inl ⟨i.val - 8, by omega⟩
  left_inv x := by
    rcases x with k | j
    · simp [show ¬(8 + k.val < 8) by omega]
    · simp [j.isLt]
  right_inv i := by
    apply Fin.ext
    by_cases h : i.val < 8
    · simp [h]
    · simp [h]; omega

def fullEquiv24 : ((Fin 16 → ZMod 2) × BitAssignment 8) ≃ BitAssignment 24 :=
    (Equiv.sumArrowEquivProdArrow (Fin 16) (Fin 8)
    (ZMod 2)).symm.trans (Equiv.arrowCongr splitEquiv24 (Equiv.refl (ZMod 2)))
theorem fullEquiv24_lo (hi : Fin 16 → ZMod 2) (lo : BitAssignment 8) (j : Fin 8) :
    fullEquiv24 (hi, lo) ⟨j.val, by omega⟩ = lo j := by
  change (Sum.elim hi lo) (splitEquiv24.symm ⟨j.val, by omega⟩) = lo j
  simp [splitEquiv24, j.isLt]

theorem fullEquiv24_hi (hi : Fin 16 → ZMod 2) (lo : BitAssignment 8) :
    zHi16Of24 (fullEquiv24 (hi, lo)) = ∑ k : Fin 16, (hi k).val * 2 ^ k.val := by
  unfold zHi16Of24
  have hFn : (fun k : Fin 16 ↦ fullEquiv24 (hi, lo) ⟨8 + k.val, by omega⟩) = hi := by
    funext k
    change (Sum.elim hi lo) (splitEquiv24.symm ⟨8 + k.val, by omega⟩) = hi k
    simp [splitEquiv24, show ¬(8 + k.val < 8) by omega]
  rw [hFn, natOfZModBits_eq_sum_val]

theorem x13K2_fullEquiv24 (γ : BitAssignment 17) (hi : Fin 16 → ZMod 2) (u0 u1 : Fin 2)
    (u6 : Fin 64) : x13K2 γ (fullEquiv24 (hi, equivLo8 (u0, u1, u6))) =
    x13OfW11U01 (w11Sub63 γ) u0 u1 := by
  unfold x13K2 x13OfW11U01
  rw [fullEquiv24_lo hi _ ⟨0, by omega⟩, fullEquiv24_lo hi _ ⟨1, by omega⟩,
    show (if equivLo8 (u0, u1, u6) ⟨0, by omega⟩ == 1 then 1 else 0) = u0.val from
      congrArg Fin.val (equivBitZMod2.apply_symm_apply u0),
    show (if equivLo8 (u0, u1, u6) ⟨1, by omega⟩ == 1 then 1 else 0) = u1.val from
      congrArg Fin.val (equivBitZMod2.apply_symm_apply u1)]

theorem zLo14K2_fullEquiv24 (γ : BitAssignment 17) (hi : Fin 16 → ZMod 2) (u0 u1 : Fin 2)
    (u6 : Fin 64) : zLo14K2 γ (fullEquiv24 (hi, equivLo8 (u0, u1, u6))) =
    (df8Of13 (x13OfW11U01 (w11Sub63 γ) u0 u1)).val + 256 * u6.val := by
  unfold zLo14K2 zMid6Of24
  rw [x13K2_fullEquiv24,
    show (fun i : Fin 6 ↦ fullEquiv24 (hi, equivLo8 (u0, u1, u6)) ⟨2 + i.val, by omega⟩) =
      fun i ↦ if u6.val.testBit i.val then (1 : ZMod 2) else 0 from funext fun i ↦ by
        rw [fullEquiv24_lo hi _ ⟨2 + i.val, by omega⟩]
        change mergeLo8 u0 u1 u6 ⟨2 + i.val, by omega⟩ = _
        simp only [mergeLo8, show ¬(2 + i.val = 0) by omega,
          show ¬(2 + i.val = 1) by omega, ↓reduceIte, show 2 + i.val - 2 = i.val by omega],
    natOfZModBits_of_testBit 6 u6.val, Nat.mod_eq_of_lt (show u6.val < 2 ^ 6 from u6.isLt)]
  ring

theorem sum_hi16_phaseBit (Q16 : ℕ) (hQ : Q16 ≤ 2 ^ 16) (s : Bool) : (2 ^ 16 : ℝ)⁻¹ *
    (∑ hi : (Fin 16 → ZMod 2),
    if ((if (Q16 + ∑ k : Fin 16, (hi k).val * 2 ^ k.val).testBit 16 then (1 : ZMod 2) else 0) +
    (if s then 1 else 0)) = 1 then (-1 : ℝ) else 1) = (if s then (1 : ℝ) else -1) *
    (((Q16 : ℝ) - 32768) / 32768) := by
  have hs := sum_bits_testBit_ind 16 Q16 hQ
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  · simp_rw [show ∀ b : Bool, (if (if b then (1 : ZMod 2) else 0) = 1 then (-1 : ℝ) else 1) =
        if b then -1 else 1 from fun b ↦ by cases b <;> simp, hs]
    norm_num; ring
  · simp_rw [show ∀ b : Bool, (if (if b then (1 : ZMod 2) else 0) + 1 = 1 then (-1 : ℝ) else 1) =
        -(if b then -1 else 1) from fun b ↦ by
          cases b <;> simp [show (1 : ZMod 2) + 1 = 0 from rfl],
      Finset.sum_neg_distrib, hs]
    norm_num; ring

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem hermite_u6_cert : (∀ q6 : Fin 64, (∑ u6 : Fin 64, (q6.val + u6.val) / 64) = q6.val) ∧
    (∀ q6 : Fin 64, ∀ c01 : Fin 2, (∑ u6 : Fin 64, ((q6.val + u6.val + c01.val) / 64 +
    (q6.val + (u6.val + 8) % 16 + c01.val) / 16)) = 5 * (q6.val + c01.val)) := by decide +kernel
theorem hermite_div16384_add (A df8 : ℕ) (_hdf8 : df8 < 256) : (∑ u6 : Fin 64,
    (A + (df8 + 256 * u6.val)) / 16384) = (A + df8) / 256 := by
  set N := A + df8
  set Q := N / 16384
  set q6 : Fin 64 := ⟨(N % 16384) / 256, by omega⟩
  have hTerm : ∀ u6 : Fin 64, (A + (df8 + 256 * u6.val)) / 16384 = Q + (q6.val + u6.val) / 64 :=
    fun u6 ↦ by dsimp only [N, Q, q6]; omega
  simp_rw [hTerm];
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      hermite_u6_cert.1 q6]; dsimp only [N, Q, q6, smul_eq_mul]; omega
theorem midWTap29_false_div16384 (y36 zLo14 : ℕ) : (midWTap29 false y36 zLo14 + zLo14) / 16384 =
    ((y36 >>> 5) + zLo14) / 16384 + ((y36 >>> 5) + (zLo14 + 2048) % 4096) / 4096 := by
  unfold midWTap29; simp only [Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_eq_div_pow]
  have h17 : y36 / 2 ^ 17 = (y36 / 32) / 4096 := by rw [Nat.div_div_eq_div_mul]; rfl
  have h32 : y36 / 2 ^ 5 = y36 / 32 := rfl;
  have h14 : (2 ^ 14 : ℕ) = 16384 := rfl; rw [h32, h17, h14]; omega
theorem hermite_tap29_en_u6 (y36 df8 : ℕ) (hdf8 : df8 < 256) : (∑ u6 : Fin 64,
    (midWTap29 false y36 (df8 + 256 * u6.val) + (df8 + 256 * u6.val)) / 16384) = 5 *
    ((fnNN30 y36 + df8) / 256) := by
  simp_rw [midWTap29_false_div16384]
  set Y5 := y36 >>> 5
  set K := Y5 / 16384
  set q6 : Fin 64 := ⟨(Y5 % 16384) / 256, by omega⟩
  set c01 : Fin 2 := ⟨(Y5 % 256 + df8) / 256, by omega⟩
  have hTerm : ∀ u6 : Fin 64,
      (Y5 + (df8 + 256 * u6.val)) / 16384 + (Y5 + (df8 + 256 * u6.val + 2048) % 4096) / 4096 =
      5 * K + ((q6.val + u6.val + c01.val) / 64 +
        (q6.val + (u6.val + 8) % 16 + c01.val) / 16) := fun u6 ↦ by
    have hm : (df8 + 256 * u6.val + 2048) % 4096 = df8 + 256 * ((u6.val + 8) % 16) := by omega
    rw [hm]
    have hrem16 : (u6.val + 8) % 16 < 16 := Nat.mod_lt _ (by norm_num)
    dsimp only [K, q6, c01]; omega
  simp_rw [hTerm];
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      hermite_u6_cert.2 q6 c01]; unfold fnNN30; dsimp only [Y5, K, q6, c01, smul_eq_mul]; omega
def qTap29LoA (y : ℕ) : ℕ := (y >>> 5) / 16384 + ((y >>> 5) + 2048) / 4096
def qTap29LoB (y : ℕ) : ℕ := ((y >>> 5) + 2048) / 16384 + (y >>> 5) / 4096
def qTap29HiA (y : ℕ) : ℕ := ((y >>> 5) + 14335) / 16384 + ((y >>> 5) + 4095) / 4096
def qTap29HiB (y : ℕ) : ℕ := ((y >>> 5) + 16383) / 16384 + ((y >>> 5) + 2047) / 4096

theorem qTap29_piecewise_bounds (y zLo14 : ℕ) (hz : zLo14 < 16384) : min (qTap29LoA y)
    (qTap29LoB y) ≤ (midWTap29 false y zLo14 + zLo14) / 16384 ∧ (midWTap29 false y zLo14 + zLo14) /
    16384 ≤ max (qTap29HiA y) (qTap29HiB y) := by
  rw [midWTap29_false_div16384]; unfold qTap29LoA qTap29LoB qTap29HiA qTap29HiB; omega
def chkQ14CapFast (q : ℕ) (cSh : ℤ) : Bool :=
    decide (-32768 ≤ (q : ℤ) - cSh ∧ (q : ℤ) - cSh ≤ 32768)
def chkTap29YCapFast (y : ℕ) (cSh : ℤ) : Bool :=
    chkQ14CapFast (qTap29LoA y) cSh && chkQ14CapFast (qTap29LoB y) cSh &&
    chkQ14CapFast (qTap29HiA y) cSh && chkQ14CapFast (qTap29HiB y) cSh
theorem qTap29_abs_le_of_mono {yLo y yHi : ℕ} {cSh : ℤ}
    (hyLo : yLo ≤ y) (hyHi : y ≤ yHi)
    (hcLo : chkQ14CapFast (qTap29LoA yLo) cSh = true ∧ chkQ14CapFast (qTap29LoB yLo) cSh = true)
    (hcHi : chkQ14CapFast (qTap29HiA yHi) cSh = true ∧ chkQ14CapFast (qTap29HiB yHi) cSh = true)
    {zLo14 : ℕ} (hzLt : zLo14 < 16384) :
    |(((midWTap29 false y zLo14 + zLo14) / 16384 : ℕ) : ℤ) - cSh| ≤ 32768 := by
  have hsLo := shr_mono_nat hyLo 5; have hsHi := shr_mono_nat hyHi 5
  have hLA : qTap29LoA yLo ≤ qTap29LoA y := by unfold qTap29LoA; omega
  have hLB : qTap29LoB yLo ≤ qTap29LoB y := by unfold qTap29LoB; omega
  have hHA : qTap29HiA y ≤ qTap29HiA yHi := by unfold qTap29HiA; omega
  have hHB : qTap29HiB y ≤ qTap29HiB yHi := by unfold qTap29HiB; omega
  have hpw := qTap29_piecewise_bounds y zLo14 hzLt; have bLA := of_decide_eq_true hcLo.1;
  have bLB := of_decide_eq_true hcLo.2; have bHA := of_decide_eq_true hcHi.1;
  have bHB := of_decide_eq_true hcHi.2; rw [abs_le]; omega
def checkTap29ENQ14NonWrap (word512 : ℕ → ℕ) (yLoF yHiF yHiF48 yLoT yHiT : ℕ) : Bool :=
  checkPopBernCtrlRangesNoClamp word512 yLoF yHiF yHiF48 yLoT yHiT &&
  chkQ14CapFast (qTap29LoA yLoF) qEN0DualLegPre5 &&
  chkQ14CapFast (qTap29LoB yLoF) qEN0DualLegPre5 &&
  chkQ14CapFast (qTap29HiA yHiF48) qEN0DualLegPre5 &&
  chkQ14CapFast (qTap29HiB yHiF48) qEN0DualLegPre5 &&
  allRange 6 48 (fun d ↦
    cond (Nat.beq (d % 8) 7) true
      (let p := evenOctPartsFast false d
       let fb := fin8BinFast d
       allRange 2 4 fun j ↦
         cond (Nat.beq (t11OfParts p) 0 && natLtB 0 j) true
           (let y := (word512 (4 * idx7OfParts p + j)) >>> p.2.2
            chkTap29YCapFast y (qEN0DualLegPre5 + dENDualLegPre5 0 (pre5OfNat fb)) &&
            chkTap29YCapFast y (qEN0DualLegPre5 + dENDualLegPre5 1 (pre5OfNat fb)) &&
            chkTap29YCapFast y (qEN0DualLegPre5 + dENDualLegPre5 2 (pre5OfNat fb)) &&
            chkTap29YCapFast y (qEN0DualLegPre5 + dENDualLegPre5 3 (pre5OfNat fb)))))

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem checkTap29ENQ14NonWrap_dualLeg_lo6 :
    checkTap29ENQ14NonWrap word512DualLegLo6 103794294 46022909632 6642834816 103794294 16271555744
    = true := by decide +kernel
theorem q14NonWrap_k2_dualLeg_lo6 :
    (∀ x n1 e1 e2 w o9 {zLo14 : ℕ}, zLo14 < 16384 →
      |(((midWTap29OfMode true false
            (ySampleK2 word512DualLegLo6 false (pairOpenDistSq x (elecP e1) (elecP e2)) w o9)
            zLo14 + zLo14) / 16384 : ℕ) : ℤ) -
        cShift14DualLeg true false (nucSpecies n1)
          (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1)))
          (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e2)))| ≤ 32768) ∧
    (∀ x {n1 n2 : Fin 47}, n1 < n2 → ∀ e1 w o9 {zLo14 : ℕ}, zLo14 < 16384 →
      |(((midWTap29OfMode true true
            (ySampleK2 word512DualLegLo6 true (pairOpenDistSq x (nucP n1) (nucP n2)) w o9)
            zLo14 + zLo14) / 16384 : ℕ) : ℤ) -
        cShift14DualLeg true true (nucSpecies n1)
          (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1)))
          (fin8Bin (pairOpenDistSq x (nucP n2) (elecP e1)))| ≤ 32768) ∧
    (∀ x n1 e1 w o9 {zLo14 : ℕ}, zLo14 < 16384 →
      |(((midWTap29OfMode false false
            (ySampleK2 word512DualLegLo6 false (pairOpenDistSq x (nucP n1) (elecP e1)) w o9)
            zLo14 + zLo14) / 16384 : ℕ) : ℤ) -
        cShift14DualLeg false false (nucSpecies n1)
          (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) 0| ≤ 32768) := by
  have hnw := popBernNonWrap30_dualLeg_lo6
  have hd2Lt : ∀ {d2 : ℕ}, Is3DBoxDistSq d2 → d2 < 262144 := fun h3d ↦ by
    have := PhotochemistrySolution.PopBernstein.is3DBoxDistSq_le h3d; omega
  have hCap {v z : ℕ} {cs c1 c2 : ℤ} (hz : z < 16384) (hM : 16384 * cs = c1 + c2)
      (h : |(v : ℤ) - c1 - c2| ≤ 2 ^ 29) : |(((v + z) / 16384 : ℕ) : ℤ) - cs| ≤ 32768 := by
    rw [show (2 ^ 29 : ℤ) = 536870912 by norm_num, abs_le] at h; rw [abs_le]; omega
  let cOf (nn : Bool) (d : ℕ) (w : Fin 2048) (o9 : Fin 512) :=
    PhotochemistrySolution.Coulomb18K2.coin33ProxyOfJK2
      (PhotochemistrySolution.Coulomb18K2.popBernJK2 (t11OfParts (evenOctIdxT10K nn d)) w o9)
  refine ⟨fun x n1 e1 e2 w o9 {zLo14} hz ↦ ?_, fun x {n1 n2} hlt e1 w o9 {zLo14} hz ↦ ?_,
          fun x n1 e1 w o9 {zLo14} hz ↦ ?_⟩
  · rw [ySampleK2_eq_proxy word512DualLegLo6 false
        (hd2Lt (is3DBoxDistSq_pairOpenDistSq x (elecP e1) (elecP e2))) w o9,
      show ∀ y, midWTap29OfMode true false y zLo14 = y >>> 6 from fun _ ↦ by
        simp only [midWTap29OfMode, midWTap29, Bool.not_false, Bool.and_self, ↓reduceIte,
          add_zero, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
    exact hCap hz (cShift14DualLeg_mul16384.1 (nucSpecies n1) _ _)
      (hnw.1 x n1 e1 e2 (cOf false _ w o9))
  · rw [ySampleK2_eq_proxy word512DualLegLo6 true
        (hd2Lt (is3DBoxDistSq_pairOpenDistSq x (nucP n1) (nucP n2))) w o9,
      show ∀ y, midWTap29OfMode true true y zLo14 = y >>> 5 from fun _ ↦ by
        simp only [midWTap29OfMode, midWTap29, Bool.not_true, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte, add_zero, Nat.shiftRight_zero]]
    exact hCap hz (cShift14DualLeg_mul16384.2.1 (nucSpecies n1) _ _)
      (hnw.2.1 x hlt e1 (cOf true _ w o9))
  · set d2 := pairOpenDistSq x (nucP n1) (elecP e1)
    have h3d : Is3DBoxDistSq d2 := is3DBoxDistSq_pairOpenDistSq x (nucP n1) (elecP e1);
    have hd2 := hd2Lt h3d; rw [ySampleK2_eq_proxy word512DualLegLo6 false hd2 w o9]
    set c := PhotochemistrySolution.Coulomb18K2.coin33ProxyOfJK2
      (Coulomb18K2.popBernJK2 (t11OfParts (evenOctIdxT10K false d2)) w o9)
    have hwEq : midWTap29OfMode false false (y36PopBernNoClamp word512DualLegLo6 false d2 c) zLo14 =
        midWTap29 false (y36PopBernNoClampS14 word512DualLegLo6 false d2 c) zLo14 := by
      unfold midWTap29OfMode y36PopBernNoClampS14;
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.shiftRight_zero]
    rw [hwEq];
    have hchk :=
        checkTap29ENQ14NonWrap_dualLeg_lo6; unfold checkTap29ENQ14NonWrap at hchk;
        simp only [Bool.and_eq_true] at hchk
    rcases hchk with ⟨⟨⟨⟨⟨hcr, hLA⟩, hLB⟩, hHA⟩, hHB⟩, henN⟩
    obtain ⟨_, hbF48, _⟩ :=
        ctrl_bounds_of_ranges_noClamp hcr; unfold cShift14DualLeg; simp only [Bool.false_eq_true,
        ↓reduceIte]
    by_cases hd : d2 < 48
    · let p := evenOctIdxT10K false d2;
      let j : Fin 4 := ⟨popBernJ (t11OfParts p) c, popBernJ_lt_four (t11OfParts p) c⟩
      have h1 := allRange_eq_true (by norm_num) henN hd
      have hm7 : ¬ (d2 % 8 = 7) := pairOpenDistSq_mod8_ne7_u x (nucP n1) (elecP e1)
      rw [cond_false_of_not (by simp only [Nat.beq_eq]; exact hm7)] at h1
      have hfb : fin8BinFast d2 = (fin8Bin d2).val :=
          fin8BinFast_eq ⟨d2, hd⟩; rw [evenOctPartsFast_eq, hfb] at h1
      have h2 := allRange_eq_true (by norm_num) h1 j.isLt; clear h1
      rw [cond_false_of_not (by
        simp only [Bool.and_eq_true, Nat.beq_eq, natLtB_eq_true]
        rintro ⟨h0, hj⟩; dsimp only [j] at hj; rw [h0, popBernJ_zero_of_t11_zero] at hj
        omega)] at h2
      simp only [Bool.and_eq_true] at h2;
      have hpre : pre5OfNat (fin8Bin d2).val = pre5OfFin8 (fin8Bin d2) := rfl; rw [hpre] at h2
      have hNear {sp : Fin 4} (hC : chkTap29YCapFast
          (y36PopBernNoClampS14 word512DualLegLo6 false d2 c)
          (qEN0DualLegPre5 + dENDualLegPre5 sp (pre5OfFin8 (fin8Bin d2))) = true) := by
        simp only [chkTap29YCapFast, Bool.and_eq_true] at hC
        exact qTap29_abs_le_of_mono le_rfl le_rfl ⟨hC.1.1.1, hC.1.1.2⟩ ⟨hC.1.2, hC.2⟩ hz
      rcases nucSpecies n1 with ⟨_ | _ | _ | _ | _, _⟩
      exacts [hNear h2.1.1.1, hNear h2.1.1.2, hNear h2.1.2, hNear h2.2, by omega]
    · have hfb0 : fin8Bin d2 = 0 := Fin.ext (fin8Bin_of_ge48_ultra (by omega : 48 ≤ d2))
      rw [hfb0]
      have hd0 : dENDualLegPre5 (nucSpecies n1) (pre5OfFin8 0) = 0 := by
        generalize nucSpecies n1 = sp; fin_cases sp <;> decide
      rw [hd0, add_zero]
      have hy := hbF48 h3d (by omega) c
      exact qTap29_abs_le_of_mono hy.1 hy.2 ⟨hLA, hLB⟩ ⟨hHA, hHB⟩ hz

open _root_.QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge (potExpectStratW11
    potExpectAvgStratW11 mSpCart254 concatBitsK11 equivBits11)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18Leg1Pass (mSpCart254_pos_wstate
    nucSpecies_not_3_3_of_lt_wstate)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1UlpElecNuc (wgtEN)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc (wEESpeciesTier1Walk
    wNNSpeciesTier1Walk wENSpeciesTier1Walk wEESpeciesTier1Walk_eq_factor
    wNNSpeciesTier1Walk_eq_factor wENSpeciesTier1Walk_eq_factor)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (coin33ProxyOfJK2
    popBernJK2)
def wgtENQtr (w : ℕ) : ℕ := if w < 401 then 768 else 763

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem sum_wgtENQtr : (∑ w : Fin 2048, wgtENQtr w.val) = 1564629 := by decide +kernel

theorem wgtEN_eq_four_wgtENQtr (w : ℕ) : wgtEN w = 4 * wgtENQtr w := by
  unfold wgtEN wgtENQtr; split_ifs <;> rfl
def expFnK2 (wgt : ℕ → ℕ) (totW : ℕ) (fn : ℕ → ℕ) (word512 : ℕ → ℕ) (isNN : Bool) (d2 : ℕ) : ℝ :=
  ((64 : ℝ) / (totW : ℝ)) *
    ∑ w : Fin 2048, (wgt w.val : ℝ) *
      ∑ u0 : Fin 2, ∑ u1 : Fin 2,
        let x13 := x13OfW11U01 w u0 u1
        (((fn (ySampleK2 word512 isNN d2 w (o9Of13 x13)) + (df8Of13 x13).val) / 256 : ℕ) : ℝ)

def vEEK2 (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47) (e1 e2 : Fin 187) : ℝ :=
    (expFnK2 wgtEETier1Walk 167340 fnEE30 word512DualLegLo6 false (pairOpenDistSq x (elecP e1)
    (elecP e2)) - (cEE1Fin8DualLeg (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) : ℝ) -
    (cEE2Fin8DualLeg (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e2))) : ℝ)) / (2 ^ 29 : ℝ)
def vNNK2 (x : Fin (2 ^ systemQubits_frozen)) (n1 n2 : Fin 47) (e1 : Fin 187) : ℝ :=
    (expFnK2 wgtNNTier1Walk 167340 fnNN30 word512DualLegLo6 true (pairOpenDistSq x (nucP n1)
    (nucP n2)) - (cNNFin8DualLeg (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) : ℝ) -
    (cNNFin8DualLeg (fin8Bin (pairOpenDistSq x (nucP n2) (elecP e1))) : ℝ)) / (2 ^ 29 : ℝ)
def vENK2 (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47) (e1 : Fin 187) : ℝ :=
    (5 * expFnK2 wgtENQtr 1564629 fnNN30 word512DualLegLo6 false (pairOpenDistSq x (nucP n1)
    (elecP e1)) - (cENFin8DualLeg (nucSpecies n1) (fin8Bin (pairOpenDistSq x (nucP n1)
    (elecP e1))) : ℝ)) / (2 ^ 29 : ℝ)
theorem wgt_avg_sub_div_k2 {wgt : ℕ → ℕ} {totW : ℕ} (htot : 0 < totW)
    (hsum : (∑ w : Fin 2048, wgt w.val) = totW) (m : ℝ) (q : Fin 2048 → Fin 2 → Fin 2 → ℕ)
    (C : ℝ) : ((totW : ℝ) * 4)⁻¹ * (∑ w : Fin 2048, (wgt w.val : ℝ) * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
    (((256 * (m * (q w u0 u1 : ℝ))) - C) / (2 ^ 29 : ℝ))) =
    ((m * (((64 : ℝ) / (totW : ℝ)) * ∑ w : Fin 2048, (wgt w.val : ℝ) * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
    (q w u0 u1 : ℝ))) - C) / (2 ^ 29 : ℝ) := by
  have htR : (totW : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsumR : (∑ w : Fin 2048, (wgt w.val : ℝ)) = (totW : ℝ) := by exact_mod_cast hsum
  have hIn : ∀ w : Fin 2048, (wgt w.val : ℝ) * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
        (((256 * (m * (q w u0 u1 : ℝ))) - C) / (2 ^ 29 : ℝ)) = ((256 * m) / (2 ^ 29 : ℝ)) *
        ((wgt w.val : ℝ) * ∑ u0 : Fin 2, ∑ u1 : Fin 2, (q w u0 u1 : ℝ)) -
      ((4 * C) / (2 ^ 29 : ℝ)) * (wgt w.val : ℝ) := fun w ↦ by
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
        Fin.sum_univ_two]; ring
  simp_rw [hIn, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumR]
  field_simp [htR]; ring

theorem abs_wgt_avg_k2_le_one {wgt : ℕ → ℕ} {totW : ℕ} (htot : 0 < totW)
    (hsum : (∑ w : Fin 2048, wgt w.val) = totW)
    (f : Fin 2048 → Fin 2 → Fin 2 → ℝ)
    (hf : ∀ w u0 u1, |f w u0 u1| ≤ 1) :
    |((totW : ℝ) * 4)⁻¹ *
      ∑ w : Fin 2048, (wgt w.val : ℝ) * ∑ u0 : Fin 2, ∑ u1 : Fin 2, f w u0 u1| ≤ 1 := by
  have ht0 : (0 : ℝ) < (totW : ℝ) * 4 := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.mpr ht0), inv_mul_le_iff₀ ht0, mul_one,
    ← show (∑ w : Fin 2048, (wgt w.val : ℝ)) = totW by exact_mod_cast hsum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans
    ((add_le_add (abs_add_le _ _) (abs_add_le _ _)).trans
      (by linarith [hf w 0 0, hf w 0 1, hf w 1 0, hf w 1 1]))) (Nat.cast_nonneg _)

theorem abs_dither256_le_one {zlo f : ℕ} {C : ℤ} (hzlo : zlo < 256)
    (hC : ∃ k : ℤ, C = 256 * k) (hf : |(f : ℤ) - C| ≤ 2 ^ 29) :
    |((256 * (1 * (((f + zlo) / 256 : ℕ) : ℝ))) - (C : ℝ)) / (2 ^ 29 : ℝ)| ≤ 1 := by
  obtain ⟨k, rfl⟩ := hC
  set q : ℕ := (f + zlo) / 256
  have h1Z : (256 : ℤ) * q ≤ f + zlo := by exact_mod_cast Nat.mul_div_le (f + zlo) 256
  have h2Z : (f : ℤ) + zlo < 256 * q + 256 := by exact_mod_cast (by omega : f + zlo < 256 * q + 256)
  have hzZ : (0 : ℤ) ≤ zlo ∧ (zlo : ℤ) < 256 := ⟨Nat.cast_nonneg _, by exact_mod_cast hzlo⟩
  rw [abs_le, show (2 ^ 29 : ℤ) = 536870912 by norm_num] at hf
  have hR1 : (-536870912 : ℝ) ≤ 256 * (q : ℝ) - 256 * k := by
    exact_mod_cast (by omega : (-536870912 : ℤ) ≤ 256 * q - 256 * k)
  have hR2 : 256 * (q : ℝ) - 256 * k ≤ (536870912 : ℝ) := by
    exact_mod_cast (by omega : (256 : ℤ) * q - 256 * k ≤ 536870912)
  push_cast
  rw [one_mul, show (2 ^ 29 : ℝ) = 536870912 by norm_num, abs_le]
  exact ⟨(le_div_iff₀ (by norm_num)).mpr (by linarith),
    (div_le_iff₀ (by norm_num)).mpr (by linarith)⟩

theorem abs_sum64_q14_le_one {q : Fin 64 → ℕ} {S : ℕ} {cSh : ℤ}
    (hS : (∑ u6 : Fin 64, q u6) = 5 * S)
    (hCap : ∀ u6 : Fin 64, |((q u6 : ℕ) : ℤ) - cSh| ≤ 32768) :
    |((256 * ((5 : ℝ) * (S : ℝ))) - (16384 * (cSh : ℝ))) / (2 ^ 29 : ℝ)| ≤ 1 := by
  have hSumLe : |∑ u6 : Fin 64, ((q u6 : ℝ) - cSh)| ≤ 64 * 32768 :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (s := Finset.univ) fun u6 _ ↦
          (by exact_mod_cast hCap u6 : |(q u6 : ℝ) - cSh| ≤ 32768))
  rw [Finset.sum_sub_distrib, show (∑ u6 : Fin 64, (q u6 : ℝ)) = 5 * S by exact_mod_cast hS,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hSumLe
  push_cast at hSumLe
  rw [abs_le] at hSumLe
  rw [show (2 ^ 29 : ℝ) = 536870912 by norm_num, abs_le]
  exact ⟨(le_div_iff₀ (by norm_num)).mpr (by linarith),
    (div_le_iff₀ (by norm_num)).mpr (by linarith)⟩

theorem vK2_unit :
    (∀ x n1 e1 e2, e1 < e2 → |vEEK2 x n1 e1 e2| ≤ 1) ∧
    (∀ x n1 n2 e1, n1 < n2 → |vNNK2 x n1 n2 e1| ≤ 1) ∧
    (∀ x n1 e1, |vENK2 x n1 e1| ≤ 1) := by
  have hnw := popBernNonWrap30_dualLeg_lo6
  have hd2Lt : ∀ {d2 : ℕ}, Is3DBoxDistSq d2 → d2 < 262144 := fun h3d ↦ by
    have := PhotochemistrySolution.PopBernstein.is3DBoxDistSq_le h3d; omega
  have hScrUnit (isNN : Bool) (wgt : ℕ → ℕ) (hsum : (∑ w : Fin 2048, wgt w.val) = 167340)
      (fn30 : ℕ → ℕ) (d2 : ℕ) (hd2 : d2 < 262144) (sp : Fin 4) (b1 b2 : Fin 8) (c1 c2 : ℤ)
      (hMul : 16384 * cShift14DualLeg true isNN sp b1 b2 = c1 + c2)
      (hBd : ∀ c : Fin 3 → Fin 2048,
        |(fn30 (y36PopBernNoClamp word512DualLegLo6 isNN d2 c) : ℤ) - (c1 + c2)| ≤ 2 ^ 29) :
      |(expFnK2 wgt 167340 fn30 word512DualLegLo6 isNN d2 - (c1 : ℝ) - (c2 : ℝ)) /
        (2 ^ 29 : ℝ)| ≤ 1 := by
    rw [← one_mul (expFnK2 _ _ _ _ _ _), sub_sub, show (c1 : ℝ) + (c2 : ℝ) = ((c1 + c2 : ℤ) : ℝ)
        from (Int.cast_add c1 c2).symm]
    unfold expFnK2
    rw [← wgt_avg_sub_div_k2 (by omega) hsum 1]
    refine abs_wgt_avg_k2_le_one (by omega) hsum _ fun w u0 u1 ↦ ?_
    set x13 := x13OfW11U01 w u0 u1
    rw [ySampleK2_eq_proxy word512DualLegLo6 isNN hd2 w (o9Of13 x13)]
    exact abs_dither256_le_one (df8Of13 x13).isLt
      ⟨64 * cShift14DualLeg true isNN sp b1 b2, by linarith⟩ (hBd _)
  refine ⟨fun x n1 e1 e2 _ ↦ hScrUnit false wgtEETier1Walk sum_wgtEETier1Walk fnEE30 _
      (hd2Lt (is3DBoxDistSq_pairOpenDistSq x (elecP e1) (elecP e2))) (nucSpecies n1) _ _ _ _
      (cShift14DualLeg_mul16384.1 _ _ _) fun c ↦ by
        have h := hnw.1 x n1 e1 e2 c
        simp only [u30DualLeg, fnEE30, Bool.false_eq_true, ↓reduceIte, abs_le] at h ⊢; omega,
    fun x n1 n2 e1 hlt ↦ hScrUnit true wgtNNTier1Walk sum_wgtNNTier1Walk fnNN30 _
      (hd2Lt (is3DBoxDistSq_pairOpenDistSq x (nucP n1) (nucP n2))) (nucSpecies n1) _ _ _ _
      (cShift14DualLeg_mul16384.2.1 _ _ _) fun c ↦ by
        have h := hnw.2.1 x hlt e1 c
        simp only [u30DualLeg, fnNN30, ↓reduceIte, abs_le] at h ⊢; omega,
    fun x n1 e1 ↦ ?_⟩
  unfold vENK2 expFnK2
  rw [← wgt_avg_sub_div_k2 (by omega) sum_wgtENQtr 5]
  refine abs_wgt_avg_k2_le_one (by omega) sum_wgtENQtr _ fun w u0 u1 ↦ ?_
  set x13 := x13OfW11U01 w u0 u1
  rw [show (cENFin8DualLeg (nucSpecies n1) (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) : ℝ) =
      16384 * (cShift14DualLeg false false (nucSpecies n1)
        (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) 0 : ℝ) by
      exact_mod_cast (cShift14DualLeg_mul16384.2.2 _ _ 0).symm]
  exact abs_sum64_q14_le_one
    (hermite_tap29_en_u6 _ (df8Of13 x13).val (df8Of13 x13).isLt) fun u6 ↦ by
      have h := q14NonWrap_k2_dualLeg_lo6.2.2 x n1 e1 w (o9Of13 x13)
        (zLo14 := (df8Of13 x13).val + 256 * u6.val)
        (by have := (df8Of13 x13).isLt; have := u6.isLt; omega)
      rw [show ∀ y z, midWTap29OfMode false false y z = midWTap29 false y z from fun _ _ ↦ rfl] at h
      exact h

noncomputable def midNNK2 (s1 s2 : ℕ) : ℝ :=
    midNNTier1Walk s1 s2 + ((-7496 : ℝ) - (-8958 : ℝ)) / 1000
noncomputable def midENK2 (s : Fin 4) : ℝ := midENTier1Walk s + ((-2061 : ℝ) - (-11431 : ℝ)) / 1000

theorem short_table_eq_nn_k2 (s1 s2 : ℕ)
    (b1 b2 : Fin 8) : ((denomNNFermatCoinVal * (100000 / 100155)) / (2 ^ 29 : ℝ)) *
    ((cNNFin8DualLeg b1 : ℝ) + (cNNFin8DualLeg b2 : ℝ)) = midNNK2 s1 s2 + gNNTier1Walk s1 b1.val +
    gNNTier1Walk s2 b2.val + (-8958 : ℝ) / 1000 := by
  rw [short_table_eq_nn_tier1Walk s1 s2 b1 b2]; unfold midNNK2; ring
theorem short_table_eq_en_k2 (s : Fin 4) (b : Fin 8) : ((denomENFermatCoin 1 * (100000 / 100155)) /
    (2 ^ 29 : ℝ)) * (cENFin8DualLeg s b : ℝ) = midENK2 s + ((186 : ℝ) * gEETier1Walk b.val +
    (187 - (speciesZ s : ℝ)) * gNNTier1Walk s.val b.val) / 187 + (-11431 : ℝ) /
    1000 := by rw [short_table_eq_en_tier1Walk s b]; unfold midENK2; ring
def γ17OfW11 (ω : BitAssignment 11) : BitAssignment 17 :=
  fun j ↦ if h : j.val < 11 then ω ⟨j.val, h⟩ else 0

theorem w11Sub63_γ17OfW11 (ω : BitAssignment 11) : w11Sub63 (γ17OfW11 ω) = equivBits11 ω := by
  apply Fin.ext; dsimp only [w11Sub63, equivBits11]
  exact congrArg (natOfZModBits 11) (funext fun k ↦ by simp [γ17OfW11, k.isLt])

theorem owK2PhaseBit3_congr_w11 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) {γ₁ γ₂ : BitAssignment 17}
    (hw : w11Sub63 γ₁ = w11Sub63 γ₂) (s nn : Bool) (sp1 sp2 : Fin 4)
    (nA pB eA : Fin 3 → Fin 256) (z : BitAssignment 24) :
    owK2PhaseBit3 v1Fn v2Fn ySample13 γ₁ s nn sp1 sp2 nA pB eA z =
      owK2PhaseBit3 v1Fn v2Fn ySample13 γ₂ s nn sp1 sp2 nA pB eA z := by
  have hx : x13K2 γ₁ z = x13K2 γ₂ z := by simp only [x13K2, hw]
  have hz14 : zLo14K2 γ₁ z = zLo14K2 γ₂ z := by simp only [zLo14K2, hx]
  have hz30 : z30K2 γ₁ z = z30K2 γ₂ z := by simp only [z30K2, hz14]
  unfold owK2PhaseBit3
  rw [hw, hx, hz14, hz30]

theorem potExpectK2Mode_congr_w11 (v1Fn v2Fn : Bool → Bool → Fin 4 → Fin 8 → ℕ)
    (ySample13 : Bool → ℕ → Fin 2048 → Fin 512 → ℕ) {γ₁ γ₂ : BitAssignment 17}
    (hw : w11Sub63 γ₁ = w11Sub63 γ₂) :
    potExpectK2Mode v1Fn v2Fn ySample13 γ₁ = potExpectK2Mode v1Fn v2Fn ySample13 γ₂ := by
  funext s nn sp1 sp2 nA nB eA eB
  exact congrArg (fun f : BitAssignment 24 → ZMod 2 ↦
      (2 ^ 24 : ℝ)⁻¹ * ∑ z : BitAssignment 24, if f z = 1 then (-1 : ℝ) else 1)
    (funext fun z ↦ owK2PhaseBit3_congr_w11 v1Fn v2Fn ySample13 hw s nn sp1 sp2 nA _ eA z)

def potExpectK2DualLegW11 (ω : BitAssignment 11) : PotExpectFn := potExpectK2DualLegK17 (γ17OfW11 ω)
theorem avg_u6_q14 (s : Bool) (q : Fin 64 → ℕ) (S : ℕ) (hS : (∑ u6 : Fin 64, q u6) = S)
    (C : ℝ) : (64 : ℝ)⁻¹ * (∑ u6 : Fin 64, (if s then (1 : ℝ) else -1) * ((16384 * (q u6 : ℝ) - C) /
    (2 ^ 29 : ℝ))) = (if s then (1 : ℝ) else -1) * ((256 * (S : ℝ) - C) / (2 ^ 29 : ℝ)) := by
  have hSR : (∑ u6 : Fin 64, (q u6 : ℝ)) = (S : ℝ) := by exact_mod_cast hS
  have hIn : ∀ u6 : Fin 64,
      (if s then (1 : ℝ) else -1) * ((16384 * (q u6 : ℝ) - C) / (2 ^ 29 : ℝ)) =
      ((if s then (1 : ℝ) else -1) * (16384 / (2 ^ 29 : ℝ))) * (q u6 : ℝ) -
        ((if s then (1 : ℝ) else -1) * C / (2 ^ 29 : ℝ)) := fun _ ↦ by ring
  simp_rw [hIn, Finset.sum_sub_distrib, ← Finset.mul_sum, hSR, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] <;> field_simp <;> ring

theorem potExpectK2_collapse_24
    (γ : BitAssignment 17) (s nn : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256)
    (S : Fin 2 → Fin 2 → ℕ)
    (hMod : (((v1Fin8DualLeg s nn sp1 (fin8Bin (openCoordDistSq nA eA)) : ℤ) +
              (v2Fin8DualLeg s nn sp2 (owB2Of3Port nn nA (if nn then nB else eB) eA) : ℤ)) -
            (32768 - cShift14DualLeg s nn sp1
              (fin8Bin (openCoordDistSq nA eA))
              (owB2Of3Port nn nA (if nn then nB else eB) eA))) % 131072 = 0)
    (hCap : ∀ (u0 u1 : Fin 2) (u6 : Fin 64),
      let x13 := x13OfW11U01 (w11Sub63 γ) u0 u1; let zLo := (df8Of13 x13).val + 256 * u6.val
      |(((midWTap29OfMode s nn
            (ySampleK2 word512DualLegLo6 nn
              (sectorDist3DSq3 s nn nA (if nn then nB else eB) eA)
              (w11Sub63 γ) (o9Of13 x13))
            zLo + zLo) / 16384 : ℕ) : ℤ) -
        cShift14DualLeg s nn sp1
          (fin8Bin (openCoordDistSq nA eA))
          (owB2Of3Port nn nA (if nn then nB else eB) eA)| ≤ 32768)
    (hHerm : ∀ (u0 u1 : Fin 2),
      let x13 := x13OfW11U01 (w11Sub63 γ) u0 u1
      (∑ u6 : Fin 64,
        (midWTap29OfMode s nn
          (ySampleK2 word512DualLegLo6 nn
            (sectorDist3DSq3 s nn nA (if nn then nB else eB) eA)
            (w11Sub63 γ) (o9Of13 x13))
          ((df8Of13 x13).val + 256 * u6.val) +
          ((df8Of13 x13).val + 256 * u6.val)) / 16384) = S u0 u1) :
    potExpectK2DualLegK17 γ s nn sp1 sp2 nA nB eA eB =
      (4 : ℝ)⁻¹ * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
        (if s then (1 : ℝ) else -1) *
          ((256 * (S u0 u1 : ℝ) -
            16384 * (cShift14DualLeg s nn sp1
              (fin8Bin (openCoordDistSq nA eA))
              (owB2Of3Port nn nA (if nn then nB else eB) eA) : ℝ)) / (2 ^ 29 : ℝ)) := by
  unfold potExpectK2DualLegK17 potExpectK2Mode
  set pB := if nn then nB else eB
  set d2 := sectorDist3DSq3 s nn nA pB eA
  set b1 := fin8Bin (openCoordDistSq nA eA)
  set b2 := owB2Of3Port nn nA pB eA
  set cSh := cShift14DualLeg s nn sp1 b1 b2
  rw [← fullEquiv24.sum_comp, Fintype.sum_prod_type, Finset.sum_comm, ← equivLo8.sum_comp,
      Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]
  have hp24 : (2 ^ 24 : ℝ)⁻¹ = (4 : ℝ)⁻¹ * ((64 : ℝ)⁻¹ * (2 ^ 16 : ℝ)⁻¹) := by norm_num
  rw [hp24, mul_assoc, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro u0 _
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u1 _
  rw [mul_assoc, Finset.mul_sum]
  set x13 := x13OfW11U01 (w11Sub63 γ) u0 u1
  set y36 := ySampleK2 word512DualLegLo6 nn d2 (w11Sub63 γ) (o9Of13 x13)
  have hInner : ∀ u6 : Fin 64, (2 ^ 16 : ℝ)⁻¹ * (∑ hi : (Fin 16 → ZMod 2),
        if owK2PhaseBit3 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6) γ
            s nn sp1 sp2 nA pB eA (fullEquiv24 (hi, equivLo8 (u0, u1, u6))) = 1
        then (-1 : ℝ) else 1) = (if s then (1 : ℝ) else -1) *
        ((16384 * ((((midWTap29OfMode s nn y36 ((df8Of13 x13).val + 256 * u6.val) +
            ((df8Of13 x13).val + 256 * u6.val)) / 16384 : ℕ) : ℝ)) -
          16384 * (cSh : ℝ)) / (2 ^ 29 : ℝ)) := fun u6 ↦ by
    set zLo := (df8Of13 x13).val + 256 * u6.val
    set q14 := (midWTap29OfMode s nn y36 zLo + zLo) / 16384
    set Q16 := (v1Fin8DualLeg s nn sp1 b1 + v2Fin8DualLeg s nn sp2 b2 + q14) % 131072
    have hPh : (fun hi : Fin 16 → ZMod 2 ↦
        owK2PhaseBit3 v1Fin8DualLeg v2Fin8DualLeg (ySampleK2 word512DualLegLo6) γ s nn sp1 sp2 nA pB
        eA (fullEquiv24 (hi, equivLo8 (u0, u1, u6)))) = (fun hi : Fin 16 → ZMod 2 ↦
        (if (Q16 + ∑ k : Fin 16, (hi k).val * 2 ^ k.val).testBit 16 then (1 : ZMod 2) else 0) +
        (if s then 1 else 0))
        := by
      funext hi; unfold owK2PhaseBit3; dsimp only [d2, b1, b2];
      rw [z30K2_split14, x13K2_fullEquiv24, zLo14K2_fullEquiv24, fullEquiv24_hi,
          testBit30_t31ModTap29_eq_q14]
    have hCongr :=
        congrArg (fun f : (Fin 16 → ZMod 2) → ZMod 2 ↦ (2 ^ 16 : ℝ)⁻¹ * ∑ hi : (Fin 16 → ZMod 2),
        if f hi = 1 then (-1 : ℝ) else 1) hPh
    obtain ⟨hQEq, hQLe⟩ := q16Mod_eq_of_q14_nonWrap hMod (hCap u0 u1 u6)
    have hQR : (Q16 : ℝ) = 32768 + (q14 : ℝ) - (cSh : ℝ) := by exact_mod_cast hQEq
    rw [hCongr, sum_hi16_phaseBit Q16 hQLe s, hQR]
    norm_num; ring
  simp_rw [hInner]; exact avg_u6_q14 s _ (S u0 u1) (hHerm u0 u1) (16384 * (cSh : ℝ))
theorem avgStrat_k2_raw_eq {wgt : ℕ → ℕ} {totW cSp W : ℕ} (hcSp : 0 < cSp) (htotW : 0 < totW)
    (hW : W = cSp * totW) {cnt : BitAssignment 11 → ℕ}
    (hCnt : ∀ ω, cnt ω = cSp * wgt (natOfZModBits 11 ω)) (gSample : Fin 2048 → Fin 2 → Fin 2 → ℝ) :
    (2 ^ 0 : ℝ)⁻¹ * (∑ γExt : BitAssignment 0, (W : ℝ)⁻¹ * ∑ ω : BitAssignment 11, (cnt ω : ℝ) *
    ((4 : ℝ)⁻¹ * ∑ u0 : Fin 2, ∑ u1 : Fin 2, gSample (equivBits11 (concatBitsK11 γExt ω)) u0 u1)) =
    ((totW : ℝ) * 4)⁻¹ * ∑ w : Fin 2048, (wgt w.val : ℝ) * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
    gSample w u0 u1 := by
  have hCat0 (γ : BitAssignment 0) (ω : BitAssignment 11) :
      concatBitsK11 (kExt := 0) γ ω = ω := funext fun i ↦ by
    dsimp only [concatBitsK11, Function.comp_apply]
    cases h : (finSumFinEquiv (m := 0) (n := 11)).symm i with
    | inl a => exact a.elim0
    | inr b =>
        have hb := congrArg Fin.val ((finSumFinEquiv_apply_right b).symm.trans
          (h ▸ (finSumFinEquiv (m := 0) (n := 11)).apply_symm_apply i))
        exact congrArg ω (Fin.ext (by simpa [Fin.val_natAdd] using hb))
  simp only [hCat0, Finset.sum_const, Finset.card_univ,
    show Fintype.card (BitAssignment 0) = 1 by simp [BitAssignment],
    one_smul, pow_zero, inv_one, one_mul]
  simp_rw [show ∀ ω : BitAssignment 11,
      (cnt ω : ℝ) * ((4 : ℝ)⁻¹ * ∑ u0 : Fin 2, ∑ u1 : Fin 2, gSample (equivBits11 ω) u0 u1) =
      ((cSp : ℝ) * (4 : ℝ)⁻¹) * ((wgt (equivBits11 ω).val : ℝ) *
        ∑ u0 : Fin 2, ∑ u1 : Fin 2, gSample (equivBits11 ω) u0 u1) from fun ω ↦ by
    rw [hCnt ω, show natOfZModBits 11 ω = (equivBits11 ω).val from rfl]; push_cast; ring,
    ← Finset.mul_sum]
  rw [Fintype.sum_equiv equivBits11 _
      (fun w ↦ (wgt w.val : ℝ) * ∑ u0 : Fin 2, ∑ u1 : Fin 2, gSample w u0 u1) fun _ ↦ rfl, hW]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (by omega : cSp ≠ 0), Nat.cast_ne_zero.mpr (by omega : totW ≠ 0)]

theorem en_summand_cast_eq (q : ℕ) (c : ℝ) : (-1 : ℝ) * ((256 * (((5 * q : ℕ) : ℝ)) - c) /
    (2 ^ 29 : ℝ)) = -(((256 * ((5 : ℝ) * (q : ℝ))) - c) / (2 ^ 29 : ℝ)) := by push_cast; ring
theorem potExpectAvgStratW11_k2_dualLeg_eq
    {cntEE : Fin 4 → BitAssignment 11 → ℕ}
    {cntNN : Fin 4 → Fin 4 → BitAssignment 11 → ℕ}
    {cntEN : Fin 4 → BitAssignment 11 → ℕ}
    (hCntEE : ∀ s ω, cntEE s ω = (2 * mSpCart254 s) * wgtEETier1Walk (natOfZModBits 11 ω))
    (hCntNN : ∀ s1 s2 ω, ¬(s1.val = 3 ∧ s2.val = 3) →
      cntNN s1 s2 ω = (mSpCart254 s1 * mSpCart254 s2) * wgtNNTier1Walk (natOfZModBits 11 ω))
    (hCntEN : ∀ s ω, cntEN s ω = mSpCart254 s * wgtEN (natOfZModBits 11 ω)) :
    let potAvg :=
        potExpectAvgStratW11 (kExt := 0) wEESpeciesTier1Walk wNNSpeciesTier1Walk wENSpeciesTier1Walk
      cntEE cntNN cntEN potExpectK2DualLegW11
    (∀ x n1 e1 e2, e1 < e2 → potAvg true false (nucSpecies n1) 0 (sysCoord x (nucParticle n1)) 0
        (sysCoord x (elecParticle e1)) (sysCoord x (elecParticle e2)) = vEEK2 x n1 e1 e2) ∧
    (∀ x n1 n2 e1, n1 < n2 → potAvg true true (nucSpecies n1) (nucSpecies n2)
        (sysCoord x (nucParticle n1)) (sysCoord x (nucParticle n2))
        (sysCoord x (elecParticle e1)) 0 = vNNK2 x n1 n2 e1) ∧
    (∀ x n1 e1, potAvg false false (nucSpecies n1) 0
        (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1)) 0 =
      -vENK2 x n1 e1) := by
  have hb1Sys (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47) (e1 : Fin 187) :
      openCoordDistSq (sysCoord x (nucParticle n1)) (sysCoord x (elecParticle e1)) =
        pairOpenDistSq x (nucP n1) (elecP e1) := by
    rw [nucParticle_eq_nucP, elecParticle_eq_elecP, openCoordDistSq_sys]
  have hScrAvg (nn : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256)
      (d2 : ℕ) (b1 b2 : Fin 8) (c1 c2 : ℝ) (fn30 : ℕ → ℕ) (wgt : ℕ → ℕ)
      (cSp W : ℕ) (cnt : BitAssignment 11 → ℕ)
      (hcSp : 0 < cSp) (hW : W = cSp * 167340)
      (hCnt : ∀ ω, cnt ω = cSp * wgt (natOfZModBits 11 ω))
      (hsum : (∑ w : Fin 2048, wgt w.val) = 167340)
      (hMod : (((v1Fin8DualLeg true nn sp1 (fin8Bin (openCoordDistSq nA eA)) : ℤ) +
                (v2Fin8DualLeg true nn sp2 (owB2Of3Port nn nA (if nn then nB else eB) eA) : ℤ)) -
              (32768 - cShift14DualLeg true nn sp1 (fin8Bin (openCoordDistSq nA eA))
                (owB2Of3Port nn nA (if nn then nB else eB) eA))) % 131072 = 0)
      (hdEq : sectorDist3DSq3 true nn nA (if nn then nB else eB) eA = d2)
      (hb1Eq : fin8Bin (openCoordDistSq nA eA) = b1)
      (hb2Eq : owB2Of3Port nn nA (if nn then nB else eB) eA = b2)
      (hMode : ∀ y zLo, midWTap29OfMode true nn y zLo = fn30 y)
      (hCap : ∀ w o9 {zLo14 : ℕ}, zLo14 < 16384 →
        |(((midWTap29OfMode true nn (ySampleK2 word512DualLegLo6 nn d2 w o9) zLo14 + zLo14) /
            16384 : ℕ) : ℤ) - cShift14DualLeg true nn sp1 b1 b2| ≤ 32768)
      (hMul : 16384 * (cShift14DualLeg true nn sp1 b1 b2 : ℝ) = c1 + c2) :
      (2 ^ 0 : ℝ)⁻¹ * (∑ γExt : BitAssignment 0, (W : ℝ)⁻¹ * ∑ ω : BitAssignment 11,
        (cnt ω : ℝ) * potExpectK2DualLegW11 (concatBitsK11 γExt ω) true nn sp1 sp2 nA nB eA eB) =
      (expFnK2 wgt 167340 fn30 word512DualLegLo6 nn d2 - c1 - c2) / (2 ^ 29 : ℝ) := by
    let qS (w : Fin 2048) (u0 u1 : Fin 2) : ℕ :=
      (fn30 (ySampleK2 word512DualLegLo6 nn d2 w (o9Of13 (x13OfW11U01 w u0 u1))) +
        (df8Of13 (x13OfW11U01 w u0 u1)).val) / 256
    let gS (w : Fin 2048) (u0 u1 : Fin 2) : ℝ :=
      (256 * (1 * (qS w u0 u1 : ℝ)) - (c1 + c2)) / (2 ^ 29 : ℝ)
    have hpt (ω : BitAssignment 11) : potExpectK2DualLegW11 ω true nn sp1 sp2 nA nB eA eB =
        (4 : ℝ)⁻¹ * ∑ u0 : Fin 2, ∑ u1 : Fin 2, gS (equivBits11 ω) u0 u1 := by
      unfold potExpectK2DualLegW11
      rw [potExpectK2_collapse_24 (γ17OfW11 ω) true nn sp1 sp2 nA nB eA eB (qS (equivBits11 ω))
        hMod (fun u0 u1 u6 ↦ by
          rw [w11Sub63_γ17OfW11, hdEq, hb1Eq, hb2Eq]
          exact hCap _ _ (by
            have := (df8Of13 (x13OfW11U01 (equivBits11 ω) u0 u1)).isLt
            have := u6.isLt; omega))
        (fun u0 u1 ↦ by
          rw [w11Sub63_γ17OfW11, hdEq]; simp_rw [hMode]
          exact hermite_div16384_add _ _ (df8Of13 _).isLt), hb1Eq, hb2Eq]
      simp only [↓reduceIte, hMul, gS, one_mul]
    simp_rw [hpt]
    rw [avgStrat_k2_raw_eq hcSp (by omega) hW hCnt gS, wgt_avg_sub_div_k2 (by omega) hsum 1]
    unfold expFnK2; rw [one_mul, ← sub_sub]
  refine ⟨fun x n1 e1 e2 _ ↦ ?_, fun x n1 n2 e1 hlt ↦ ?_, fun x n1 e1 ↦ ?_⟩
  · simp only [potExpectAvgStratW11, potExpectStratW11, potExpectAvgK, vEEK2,
      Bool.false_eq_true, ↓reduceIte]
    exact hScrAvg false (nucSpecies n1) 0 _ _ _ _ _ _ _ _ _ fnEE30 wgtEETier1Walk _ _ _
      (Nat.mul_pos (by omega) (mSpCart254_pos_wstate (nucSpecies n1)))
      (wEESpeciesTier1Walk_eq_factor _)
          (hCntEE _) sum_wgtEETier1Walk (t1b_shift14_mod_cert.1 _ _ _ _)
      (by simp [sectorDist3DSq3, elecParticle_eq_elecP, openBoxDist3DSq_sys])
      (congrArg fin8Bin (hb1Sys x n1 e1))
      (by simp [owB2Of3Port, nucParticle_eq_nucP, elecParticle_eq_elecP, openCoordDistSq_sys])
      (fun _ _ ↦ by simp only [midWTap29OfMode, midWTap29, fnEE30, Bool.not_false, Bool.and_self,
        ↓reduceIte, add_zero, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul])
      (q14NonWrap_k2_dualLeg_lo6.1 x n1 e1 e2)
      (by exact_mod_cast cShift14DualLeg_mul16384.1 _ _ _)
  · simp only [potExpectAvgStratW11, potExpectStratW11, potExpectAvgK, vNNK2, ↓reduceIte]
    have hnot33 := nucSpecies_not_3_3_of_lt_wstate hlt
    exact hScrAvg true (nucSpecies n1) (nucSpecies n2) _ _ _ _ _ _ _ _ _ fnNN30 wgtNNTier1Walk _ _ _
      (Nat.mul_pos (mSpCart254_pos_wstate _) (mSpCart254_pos_wstate _))
      (wNNSpeciesTier1Walk_eq_factor _ _ hnot33) (fun ω ↦ hCntNN _ _ ω hnot33) sum_wgtNNTier1Walk
      (t1b_shift14_mod_cert.2.1 _ _ _ _)
      (by simp [sectorDist3DSq3, nucParticle_eq_nucP, openBoxDist3DSq_sys])
      (congrArg fin8Bin (hb1Sys x n1 e1))
      (by simp [owB2Of3Port, nucParticle_eq_nucP, elecParticle_eq_elecP, openCoordDistSq_sys])
      (fun _ _ ↦ by simp [midWTap29OfMode, midWTap29, fnNN30])
      (q14NonWrap_k2_dualLeg_lo6.2.1 x hlt e1)
      (by exact_mod_cast cShift14DualLeg_mul16384.2.1 _ _ _)
  · unfold potExpectAvgStratW11 potExpectStratW11 potExpectAvgK;
    simp only [Bool.false_eq_true, ↓reduceIte]
    let qEN (w : Fin 2048) (u0 u1 : Fin 2) : ℕ :=
      (fnNN30 (ySampleK2 word512DualLegLo6 false (pairOpenDistSq x (nucP n1) (elecP e1)) w
        (o9Of13 (x13OfW11U01 w u0 u1))) + (df8Of13 (x13OfW11U01 w u0 u1)).val) / 256
    let gEN (w : Fin 2048) (u0 u1 : Fin 2) : ℝ := -((256 * ((5 : ℝ) * (qEN w u0 u1 : ℝ)) -
        (cENFin8DualLeg (nucSpecies n1) (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) : ℝ)) /
        (2 ^ 29 : ℝ))
    have hpt (ω : BitAssignment 11) : potExpectK2DualLegW11 ω false false (nucSpecies n1) 0
          (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1)) 0 =
        (4 : ℝ)⁻¹ * ∑ u0 : Fin 2, ∑ u1 : Fin 2, gEN (equivBits11 ω) u0 u1 := by
      unfold potExpectK2DualLegW11
      have hdEq : sectorDist3DSq3 false false (sysCoord x (nucParticle n1)) (if false then 0 else 0)
          (sysCoord x (elecParticle e1)) = pairOpenDistSq x (nucP n1) (elecP e1) := by
        simp only [sectorDist3DSq3, Bool.false_eq_true, ↓reduceIte, Bool.cond_false,
            nucParticle_eq_nucP, elecParticle_eq_elecP, openBoxDist3DSq_sys]
      have hb1Eq : openCoordDistSq (sysCoord x (nucParticle n1)) (sysCoord x (elecParticle e1)) =
          pairOpenDistSq x (nucP n1) (elecP e1) := by
        rw [nucParticle_eq_nucP, elecParticle_eq_elecP, openCoordDistSq_sys]
      have hcENEqGen : ∀ (s : Fin 4) (b1 b2 : Fin 8),
          cShift14DualLeg false false s b1 b2 = cShift14DualLeg false false s b1 0 := by decide
      have hcENEq : ∀ b2 : Fin 8, cShift14DualLeg false false (nucSpecies n1)
          (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) b2 =
          cShift14DualLeg false false (nucSpecies n1) (fin8Bin (pairOpenDistSq x (nucP n1)
          (elecP e1))) 0 := fun b2 ↦ hcENEqGen (nucSpecies n1) _ b2
      rw [potExpectK2_collapse_24 (γ17OfW11 ω) false false (nucSpecies n1) 0 _ _ _ _
        (fun u0 u1 ↦ 5 * qEN (equivBits11 ω) u0 u1) (t1b_shift14_mod_cert.2.2 _ _ _ _)
        (fun u0 u1 u6 ↦ by
          rw [w11Sub63_γ17OfW11, hdEq, hb1Eq, hcENEq]
          exact q14NonWrap_k2_dualLeg_lo6.2.2 x n1 e1 _ _
            (by have := (df8Of13 (x13OfW11U01 (equivBits11 ω) u0 u1)).isLt; have := u6.isLt; omega))
        (fun u0 u1 ↦ by
          rw [w11Sub63_γ17OfW11, hdEq]
          simp_rw [show ∀ y zLo, midWTap29OfMode false false y zLo = midWTap29 false y zLo
            from fun _ _ ↦ rfl]
          exact hermite_tap29_en_u6 _ _ (df8Of13 _).isLt), hb1Eq, hcENEq]
      have hMul : 16384 * (cShift14DualLeg false false (nucSpecies n1)
          (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) 0 : ℝ) = (cENFin8DualLeg (nucSpecies n1)
          (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) : ℝ)
          := by exact_mod_cast cShift14DualLeg_mul16384.2.2 _ _ 0
      simp only [Bool.false_eq_true, ↓reduceIte, hMul]
      simp_rw [en_summand_cast_eq]
      rfl
    simp_rw [hpt]
    have hcSp : 0 < 4 * mSpCart254 (nucSpecies n1) := by
      have := mSpCart254_pos_wstate (nucSpecies n1); omega
    have hwEN : wENSpeciesTier1Walk (nucSpecies n1) = (4 * mSpCart254 (nucSpecies n1)) *
        1564629 := by rw [wENSpeciesTier1Walk_eq_factor (nucSpecies n1)]; ring
    have hCntEN' : ∀ ω, cntEN (nucSpecies n1) ω =
        (4 * mSpCart254 (nucSpecies n1)) * wgtENQtr (natOfZModBits 11 ω) := fun ω ↦ by
      rw [hCntEN, wgtEN_eq_four_wgtENQtr]; ring
    rw [avgStrat_k2_raw_eq hcSp (by omega) hwEN hCntEN' gEN]
    dsimp only [gEN]
    simp_rw [Finset.sum_neg_distrib, mul_neg, Finset.sum_neg_distrib, mul_neg]
    rw [wgt_avg_sub_div_k2 (by omega) sum_wgtENQtr 5]
    unfold vENK2 expFnK2; rfl
end QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs
end

section
set_option Elab.async false
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (nat_div_def)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (df8Of13 o9Of13)
namespace QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (rowDf8MaskNat rowO9MaskNat
    parity13Aux affineBit13)
inductive ChK2 : Type
  | ee : ChK2
  | nn : ChK2
  | en : ChK2

def chFnChK2 : ChK2 → ChW11
  | .ee => .ee
  | .nn => .nn
  | .en => .nn

def chIsNNK2 : ChK2 → Bool
  | .ee => false
  | .nn => true
  | .en => false

def chFn30K2 : ChK2 → ℕ → ℕ
  | .ee => fnEE30
  | .nn => fnNN30
  | .en => fnNN30

theorem chFn_chFnChK2_eq (ch : ChK2) : chFn (chFnChK2 ch) = chFn30K2 ch := by
  cases ch <;> rfl

def chWgtK2 : ChK2 → ℕ → ℕ
  | .ee => wgtEETier1Walk
  | .nn => wgtNNTier1Walk
  | .en => wgtENQtr

def chWgtFK2 : ChK2 → Nat → Nat
  | .ee, w => Bool.casesOn (Nat.ble (Nat.add w 1) 1452) 81 82
  | .nn, w => Bool.casesOn (Nat.ble (Nat.add w 1) 1750) 80 82
  | .en, w => Bool.casesOn (Nat.ble (Nat.add w 1) 401) 763 768

theorem chWgtFK2_eq (ch : ChK2) (w : ℕ) : chWgtFK2 ch w = chWgtK2 ch w := by
  have hble : ∀ K a b : ℕ, Bool.casesOn (Nat.ble (Nat.add w 1) K) b a = if w < K then a else b :=
    fun K a b => by
      cases hb : Nat.ble (Nat.add w 1) K
      · exact (_root_.ite_eq_right fun h =>
            Bool.noConfusion (hb.symm.trans (Nat.ble_eq.mpr h))).symm
      · exact (_root_.ite_eq_left (Nat.ble_eq.mp hb)).symm
  cases ch <;> exact hble _ _ _

def chTotWK2 : ChK2 → ℕ
  | .ee => 167340
  | .nn => 167340
  | .en => 1564629

theorem chTotWK2_pos (ch : ChK2) : 0 < chTotWK2 ch := by cases ch <;> decide

def chMcK2 : ChK2 → ℕ
  | .ee => 273022058496
  | .nn => 136511029248
  | .en => 136511029248

def chDcMilliK2 : ChK2 → ℤ
  | .ee => -24841
  | .nn => -8958
  | .en => -11431

def chEpsMilliK2 : ChK2 → ℕ
  | .ee => 36057
  | .nn => 25742
  | .en => 20126

def chHiNumK2 : ChK2 → ℕ
  | .ee => 60898
  | .nn => 34700
  | .en => 31557

def chLoNumK2 : ChK2 → ℕ
  | .ee => 11216
  | .nn => 16784
  | .en => 8695

theorem chHiNumK2_eq (ch : ChK2) : (chHiNumK2 ch : ℝ) = (chEpsMilliK2 ch : ℝ) - (chDcMilliK2 ch : ℝ)
    := by
  cases ch <;> norm_num [chHiNumK2, chEpsMilliK2, chDcMilliK2]

theorem chLoNumK2_eq (ch : ChK2) : (chLoNumK2 ch : ℝ) = (chEpsMilliK2 ch : ℝ) + (chDcMilliK2 ch : ℝ)
    := by
  cases ch <;> norm_num [chLoNumK2, chEpsMilliK2, chDcMilliK2]

theorem ulp_k2_of_scaled_bounds (ch : ChK2) {m E : ℕ} {y : ℝ} (hm : 1 ≤ m)
    (hEy : 64 * (E : ℝ) = (chTotWK2 ch : ℝ) * y)
    (hlo : chLoNumK2 ch * 5714023029 * chTotWK2 ch ≤ 64000 * chMcK2 ch * E)
    (hU :
      (1000 * 5714023029 * 34359738368 * chTotWK2 ch) ^ 2 ≤
        (64000 * chMcK2 ch * E + chHiNumK2 ch * 5714023029 * chTotWK2 ch) *
        (64000 * chMcK2 ch * E + chHiNumK2 ch * 5714023029 * chTotWK2 ch) * m)
    (hL :
      (64000 * chMcK2 ch * E - chLoNumK2 ch * 5714023029 * chTotWK2 ch) *
        (64000 * chMcK2 ch * E - chLoNumK2 ch * 5714023029 * chTotWK2 ch) * m ≤
        (1000 * 5714023029 * 34359738368 * chTotWK2 ch) ^ 2) :
    |((chMcK2 ch : ℝ) / ((1 : ℝ) * 5714023029)) * y -
        (chDcMilliK2 ch : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √(m : ℝ)| ≤ (chEpsMilliK2 ch : ℝ) / 1000 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hsq : √(m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm0.le;
  have hrt : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  have hTot : (0 : ℝ) < (chTotWK2 ch : ℝ) := by exact_mod_cast chTotWK2_pos ch
  set D : ℝ := (chTotWK2 ch : ℝ)
  set K : ℝ := 1000 * 5714023029 * D
  have hK : 0 < K := by dsimp only [K, D]; positivity
  set S : ℝ := K * (2 ^ 35 : ℝ)
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  set U : ℝ := ((64000 * chMcK2 ch : ℕ) : ℝ) * (E : ℝ) +
    ((chHiNumK2 ch * 5714023029 * chTotWK2 ch : ℕ) : ℝ)
  set L : ℝ := ((64000 * chMcK2 ch : ℕ) : ℝ) * (E : ℝ) -
    ((chLoNumK2 ch * 5714023029 * chTotWK2 ch : ℕ) : ℝ)
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hUR := (Nat.cast_le (α := ℝ)).mpr hU
  have hLR := (Nat.cast_le (α := ℝ)).mpr hL
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hlo] at hLR
  have hUsq : S ^ 2 ≤ (U * √(m : ℝ)) ^ 2 := by
    rw [mul_pow U, hsq]; dsimp only [S, K, D, U]; push_cast at hUR ⊢; linarith
  have hLsq : (L * √(m : ℝ)) ^ 2 ≤ S ^ 2 := by
    rw [mul_pow L, hsq]; dsimp only [S, K, D, L]; push_cast at hLR ⊢; linarith
  have hUrt : S ≤ U * √(m : ℝ) := (sq_le_sq₀ hS0 (mul_nonneg hU0 hrt.le)).mp hUsq;
  have hLrt : L * √(m : ℝ) ≤ S := (abs_le.mp ((sq_le_sq.mp hLsq).trans_eq (abs_of_nonneg hS0))).2
  set X : ℝ := ((chMcK2 ch : ℝ) / ((1 : ℝ) * 5714023029)) * y
  have hScale : ((64000 * chMcK2 ch : ℕ) : ℝ) * E = K * X := by
    dsimp only [K, D, X]
    rw [show ((64000 * chMcK2 ch : ℕ) : ℝ) * E = 1000 * chMcK2 ch * (64 * E) by push_cast; ring,
      hEy]
    field_simp; ring
  have hLin (c : ℕ) : ((c * 5714023029 * chTotWK2 ch : ℕ) : ℝ) = K * (c / 1000) := by
    dsimp only [K, D]; push_cast; ring
  dsimp only [S, U, L] at hUrt hLrt
  rw [hScale, hLin, ← mul_add, mul_assoc K] at hUrt
  rw [hScale, hLin, ← mul_sub, mul_assoc K] at hLrt
  have hHi := (div_le_iff₀ hrt).mpr (le_of_mul_le_mul_left hUrt hK)
  have hLo := (le_div_iff₀ hrt).mpr (le_of_mul_le_mul_left hLrt hK)
  rw [chHiNumK2_eq] at hHi
  rw [chLoNumK2_eq] at hLo
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def ChConstsK2 (ch : ChK2) (g hi lo s0Sq : Nat) : Prop :=
    g = 64000 * chMcK2 ch ∧ hi = chHiNumK2 ch * 5714023029 * chTotWK2 ch ∧ lo = chLoNumK2 ch *
    5714023029 * chTotWK2 ch ∧ s0Sq = (1000 * 5714023029 * 34359738368 * chTotWK2 ch) ^ 2
theorem ulp_k2_of_checkNum63 (ch : ChK2) {g hi lo s0Sq m E : Nat} {y : ℝ}
    (hK : ChConstsK2 ch g hi lo s0Sq) (hm : 1 ≤ m)
    (hEy : 64 * (E : ℝ) = (chTotWK2 ch : ℝ) * y)
    (hc : checkNum63 E m g hi lo s0Sq = true) :
    |((chMcK2 ch : ℝ) / ((1 : ℝ) * 5714023029)) * y -
        (chDcMilliK2 ch : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √(m : ℝ)| ≤ (chEpsMilliK2 ch : ℝ) / 1000 := by
  obtain ⟨hlo, hU, hL⟩ := checkNum63_sound hc
  rcases hK with ⟨rfl, rfl, rfl, rfl⟩
  exact ulp_k2_of_scaled_bounds ch hm hEy hlo hU hL

def zeroST8F : SumTree := stepZeroST zeroST7F

theorem zeroST8F_eq : zeroST8F = zeroST 8 := stepZeroST_eq zeroST7F_eq
def insST128F : SumTree → Nat → Nat → SumTree := stepInsST insST64F 128

theorem insST128F_eq : ∀ t idx dw, insST128F t idx dw = insST 128 t idx dw :=
    stepInsST_eq insST64F_eq
def sufST128F : SumTree → Nat → Nat → Nat := stepSufST sufST64F 128

theorem sufST128F_eq : ∀ t M acc, sufST128F t M acc = sufST 128 t M acc := stepSufST_eq sufST64F_eq
def addST8F : SumTree → SumTree → SumTree := stepAddST addST7F

theorem addST8F_eq : ∀ t1 t2, addST8F t1 t2 = addST t1 t2 := stepAddST_eq addST7F_eq
def subST128F : SumTree → Nat → Nat → SumTree := stepSubST subST64F 128

theorem subST128F_eq_subSTD : subST128F = subSTD 8 := by
  unfold subST128F; rw [subST64F_eq_subSTD]; funext t idx dw; rfl
@[inline] def gSu256F (st : SumTree) (M : Nat) : Nat :=
    Bool.casesOn (Nat.beq M 0) (Bool.casesOn (Nat.ble 256 M) (sufST128F st M 0) 0) (stVal63 st)
@[inline] def evalLane256F (st : SumTree) (z : Nat) : Nat :=
    Nat.add (Nat.mul (stVal63 st) (Nat.div z 256)) (gSu256F st (Nat.sub 256 (Nat.mod z 256)))
def emptyST4K2 : ST4 := sST63 (zeroST 8) fun z => .mk 0 z z z z
def emptyST4K2F : ST4 := sST63 zeroST8F fun z => .mk 0 z z z z

theorem emptyST4K2F_eq : emptyST4K2F = emptyST4K2 := by
  unfold emptyST4K2F emptyST4K2; rw [zeroST8F_eq]
def insST4K2 (p : ST4) (j idx dw : Nat) : ST4 := ST4.casesOn p fun s a b c d =>
    fN63 (Nat.add s dw) fun s1 =>
    Bool.casesOn (Nat.beq j 0) (Bool.casesOn (Nat.beq j 1) (Bool.casesOn (Nat.beq j 2)
    (sST63 (insST128F d idx dw) fun d1 => .mk s1 a b c d1) (sST63 (insST128F c idx dw) fun c1 =>
    .mk s1 a b c1 d)) (sST63 (insST128F b idx dw) fun b1 => .mk s1 a b1 c d))
    (sST63 (insST128F a idx dw) fun a1 => .mk s1 a1 b c d)
def decST4K2 (p : ST4) (j idx dw : Nat) : ST4 := ST4.casesOn p fun s a b c d =>
    fN63 (Nat.sub s dw) fun s1 =>
    Bool.casesOn (Nat.beq j 0) (Bool.casesOn (Nat.beq j 1) (Bool.casesOn (Nat.beq j 2)
    (sST63 (subST128F d idx dw) fun d1 => .mk s1 a b c d1) (sST63 (subST128F c idx dw) fun c1 =>
    .mk s1 a b c1 d)) (sST63 (subST128F b idx dw) fun b1 => .mk s1 a b1 c d))
    (sST63 (subST128F a idx dw) fun a1 => .mk s1 a1 b c d)
def addST4K2 (p q : ST4) : ST4 := ST4.casesOn p fun _ a1 b1 c1 d1 =>
    ST4.casesOn q fun _ a2 b2 c2 d2 =>
    mkST4F (addST8F a1 a2) (addST8F b1 b2) (addST8F c1 c2) (addST8F d1 d2)
@[inline] def evalST4FK2 (p : ST4) (z0 z1 z2 z3 : Nat) : Nat := ST4.casesOn p fun _ a b c d =>
    fN63 (evalLane256F a z0) fun e0 => fN63 (evalLane256F b z1) fun e1 =>
    fN63 (evalLane256F c z2) fun e2 => fN63 (evalLane256F d z3) fun e3 =>
    Nat.add (Nat.add (Nat.add e0 e1) e2) e3
def emptyST4T3K2F : ST4T3 := sST4 emptyST4K2F fun z => .mk z z z

def par14Pure (mask x13 : Nat) : Nat :=
    Nat.mod (Nat.add (Nat.div mask 8192)
    (Nat.add (Nat.add (Nat.add (Nat.mul (Nat.mod mask 2) (Nat.mod x13 2)) (Nat.mul (bitAtF mask 2)
    (bitAtF x13 2))) (Nat.add (Nat.mul (bitAtF mask 4) (bitAtF x13 4)) (Nat.mul (bitAtF mask 8)
    (bitAtF x13 8)))) (Nat.add (Nat.add (Nat.add (Nat.mul (bitAtF mask 16) (bitAtF x13 16))
    (Nat.mul (bitAtF mask 32) (bitAtF x13 32))) (Nat.add (Nat.mul (bitAtF mask 64) (bitAtF x13 64))
    (Nat.mul (bitAtF mask 128) (bitAtF x13 128))))
    (Nat.add (Nat.add (Nat.mul (bitAtF mask 256) (bitAtF x13 256)) (Nat.mul (bitAtF mask 512)
    (bitAtF x13 512))) (Nat.add (Nat.mul (bitAtF mask 1024) (bitAtF x13 1024))
    (Nat.add (Nat.mul (bitAtF mask 2048) (bitAtF x13 2048)) (Nat.mul (bitAtF mask 4096)
    (bitAtF x13 4096)))))))) 2
def d11OfGO9 (g6 o9 : Nat) : Nat :=
    (g6 % 4) + 4 * ((o9 / 64) % 8) + 32 * ((o9 / 16) % 2) + 64 * (o9 % 16) + 1024 * ((o9 / 32) % 2)
@[inline] def d11OfGO9Pure (g6 o9 : Nat) : Nat :=
    Nat.add (Nat.mod g6 4) (Nat.add (Nat.mul 4 (Nat.mod (Nat.div o9 64) 8))
    (Nat.add (Nat.mul 32 (Nat.mod (Nat.div o9 16) 2)) (Nat.add (Nat.mul 64 (Nat.mod o9 16))
    (Nat.mul 1024 (Nat.mod (Nat.div o9 32) 2)))))
def df8Pure (x13 : Nat) : Nat :=
    Nat.add (Nat.add (Nat.add (par14Pure 9306 x13) (Nat.mul 2 (par14Pure 1171 x13)))
    (Nat.add (Nat.mul 4 (par14Pure 8483 x13)) (Nat.mul 8 (par14Pure 8548 x13))))
    (Nat.add (Nat.add (Nat.mul 16 (par14Pure 9107 x13)) (Nat.mul 32 (par14Pure 818 x13)))
    (Nat.add (Nat.mul 64 (par14Pure 3480 x13)) (Nat.mul 128 (par14Pure 4148 x13))))
def o9Pure (x13 : Nat) : Nat :=
    Nat.add (Nat.add (Nat.add (par14Pure 12203 x13) (Nat.mul 2 (par14Pure 2682 x13)))
    (Nat.add (Nat.mul 4 (par14Pure 2285 x13)) (Nat.mul 8 (par14Pure 3832 x13))))
    (Nat.add (Nat.add (Nat.mul 16 (par14Pure 8193 x13)) (Nat.mul 32 (par14Pure 10877 x13)))
    (Nat.add (Nat.mul 64 (par14Pure 8208 x13)) (Nat.add (Nat.mul 128 (par14Pure 12538 x13))
    (Nat.mul 256 (par14Pure 293 x13)))))
def samplePackLeafK2Pure (idx13 : Nat) : Nat := fN63 (Nat.div idx13 128) fun g6 =>
    fN63 (Nat.mod idx13 128) fun rem7 => fN63 (Nat.div rem7 4) fun u5 =>
    fN63 (Nat.mod rem7 4) fun c01 => fN63 (wOfU5GamF u5 g6) fun w =>
    fN63 (Nat.add w (Nat.mul 2048 c01)) fun x13 => fN63 (df8Pure x13) fun df8 =>
    fN63 (o9Pure x13) fun o9 => Nat.add df8 (Nat.mul 256 (d11OfGO9Pure g6 o9))
@[inline] def z13BitB4 (includeBias : Bool) (m x13 : Nat) : Nat :=
    Bool.casesOn includeBias (Nat.mod (Nat.add (par14Pure m x13) (Nat.div m 8192)) 2)
    (par14Pure m x13)
def z13Base4F (includeBias : Bool) (x13 : Nat) : Nat :=
    Nat.add (Nat.add (Nat.add (Nat.add (z13BitB4 includeBias 9306 x13)
    (Nat.mul 4 (z13BitB4 includeBias 1171 x13)))
    (Nat.add (Nat.mul 16 (z13BitB4 includeBias 8483 x13))
    (Nat.mul 64 (z13BitB4 includeBias 8548 x13))))
    (Nat.add (Nat.add (Nat.mul 256 (z13BitB4 includeBias 9107 x13))
    (Nat.mul 1024 (z13BitB4 includeBias 818 x13)))
    (Nat.add (Nat.mul 4096 (z13BitB4 includeBias 3480 x13))
    (Nat.mul 16384 (z13BitB4 includeBias 4148 x13)))))
    (Nat.mul 65536 (Nat.add (Nat.add (Nat.add (z13BitB4 includeBias 12203 x13)
    (Nat.mul 4 (z13BitB4 includeBias 2682 x13)))
    (Nat.add (Nat.mul 16 (z13BitB4 includeBias 2285 x13))
    (Nat.mul 64 (z13BitB4 includeBias 3832 x13))))
    (Nat.add (Nat.add (Nat.mul 256 (z13BitB4 includeBias 8193 x13))
    (Nat.mul 1024 (z13BitB4 includeBias 10877 x13)))
    (Nat.add (Nat.mul 4096 (z13BitB4 includeBias 8208 x13))
    (Nat.add (Nat.mul 16384 (z13BitB4 includeBias 12538 x13))
    (Nat.mul 65536 (z13BitB4 includeBias 293 x13)))))))
def decDf8B4 (b4Df8 : Nat) : Nat :=
    Nat.add (Nat.add (Nat.add (Nat.mod b4Df8 2) (Nat.mul 2 (Nat.mod (Nat.div b4Df8 4) 2)))
    (Nat.add (Nat.mul 4 (Nat.mod (Nat.div b4Df8 16) 2)) (Nat.mul 8 (Nat.mod (Nat.div b4Df8 64) 2))))
    (Nat.add (Nat.add (Nat.mul 16 (Nat.mod (Nat.div b4Df8 256) 2))
    (Nat.mul 32 (Nat.mod (Nat.div b4Df8 1024) 2)))
    (Nat.add (Nat.mul 64 (Nat.mod (Nat.div b4Df8 4096) 2))
    (Nat.mul 128 (Nat.mod (Nat.div b4Df8 16384) 2))))
def decO9B4 (b4O9 : Nat) : Nat :=
    Nat.add (Nat.add (Nat.add (Nat.mod b4O9 2) (Nat.mul 2 (Nat.mod (Nat.div b4O9 4) 2)))
    (Nat.add (Nat.mul 4 (Nat.mod (Nat.div b4O9 16) 2)) (Nat.mul 8 (Nat.mod (Nat.div b4O9 64) 2))))
    (Nat.add (Nat.add (Nat.mul 16 (Nat.mod (Nat.div b4O9 256) 2))
    (Nat.mul 32 (Nat.mod (Nat.div b4O9 1024) 2)))
    (Nat.add (Nat.mul 64 (Nat.mod (Nat.div b4O9 4096) 2))
    (Nat.add (Nat.mul 128 (Nat.mod (Nat.div b4O9 16384) 2))
    (Nat.mul 256 (Nat.mod (Nat.div b4O9 65536) 2)))))
def samplePackLeafK2Fast (wNT11 lo7B4NT hi6B4NT : NatTree) (idx13 : Nat) : Nat :=
    fN63 (Nat.div idx13 128) fun g6 => fN63 (Nat.mod idx13 128) fun rem7 =>
    fN63 (Nat.div rem7 4) fun u5 => fN63 (Nat.mod rem7 4) fun c01 =>
    fN63 (getNT1024F wNT11 (Nat.add (Nat.mul 32 g6) u5)) fun w =>
    fN63 (Nat.add w (Nat.mul 2048 c01)) fun x13 =>
    fN63 (Nat.add (getNT64F lo7B4NT (Nat.mod x13 128))
    (getNT32F hi6B4NT (Nat.div x13 128))) fun sumB4 =>
    fN63 (decDf8B4 (Nat.mod sumB4 65536)) fun df8 => fN63 (decO9B4 (Nat.div sumB4 65536)) fun o9 =>
    Nat.add df8 (Nat.mul 256 (d11OfGO9Pure g6 o9))
def spNTFastK2 : NatTree :=
    sNT63 (bNT11 (fun idx11 => wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)) 0 1024) fun wNT11 =>
    sNT63 (bNT7 (z13Base4F true) 0 64) fun lo7B4NT =>
    sNT63 (bNT6 (fun hi6 => z13Base4F false (Nat.mul 128 hi6)) 0 32) fun hi6B4NT =>
    bNT13 (samplePackLeafK2Fast wNT11 lo7B4NT hi6B4NT) 0 4096
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSpEqK2 : beqNT spNTFastK2 (bNT13 samplePackLeafK2Pure 0 4096) = true := by decide +kernel
def initLeafT3K2 (jpNT : NatTree) (pk dw : Nat) (cur : ST4T3) : ST4T3 :=
    fN63 (Nat.mod pk 256) fun df8 => fN63 (getNT1024F jpNT (Nat.div pk 256)) fun jp =>
    fN63 (Nat.mod jp 4) fun j00 => fN63 (Nat.mod (Nat.div jp 4) 4) fun j10 =>
    ST4T3.casesOn cur fun sc s0 s1 =>
    Bool.casesOn (Nat.beq j00 j10) (sST4 (insST4K2 s0 j00 df8 dw) fun s0' =>
    sST4 (insST4K2 s1 j10 df8 dw) fun s1' =>
    .mk sc s0' s1') (sST4 (insST4K2 sc j00 df8 dw) fun sc' => .mk sc' s0 s1)
@[inline] def initPairT3K2 (jpNT : NatTree) (sp2 : NatTree) (dw : Nat) (cur : ST4T3) : ST4T3 :=
    NatTree.casesOn sp2 (fun _ => cur) fun l r =>
    NatTree.casesOn l (fun pk0 => NatTree.casesOn r (fun pk1 =>
    sST4T3 (initLeafT3K2 jpNT pk0 dw cur) fun mid =>
    initLeafT3K2 jpNT pk1 dw mid) (fun _ _ => cur)) (fun _ _ => cur)
def initTreeT3K2 (jpNT : NatTree) : NatTree → NatTree → ST4T3 → ST4T3
  | .leaf _, _, cur => cur
  | .node spL spR, .leaf dw, cur =>
      sST4T3 (initPairT3K2 jpNT spL dw cur) fun mid =>
      initPairT3K2 jpNT spR dw mid
  | .node spL spR, .node wL wR, cur =>
      sST4T3 (initTreeT3K2 jpNT spL wL cur) fun mid =>
      initTreeT3K2 jpNT spR wR mid

def initTreeP2FastK2 (jpNT spNT wgtNT : NatTree) : ST4P2 :=
    ST4T3.casesOn (initTreeT3K2 jpNT spNT wgtNT emptyST4T3K2F) fun sc s0 s1 =>
    sST4 (addST4K2 sc s0) fun r0 => sST4 (addST4K2 sc s1) fun r1 => .mk r0 r1
@[inline] def advOneST4K2 (jOld jNew df8 dw : Nat) (s : ST4) : ST4 :=
    Bool.casesOn (Nat.beq jOld jNew) (sST4 (decST4K2 s jOld df8 dw) fun mid =>
    insST4K2 mid jNew df8 dw) s
def advLeafP2K2 (jpNT : NatTree) (pk dw : Nat) (cur : ST4P2) : ST4P2 :=
    fN63 (getNT1024F jpNT (Nat.div pk 256)) fun jp => fN63 (Nat.mod jp 16) fun jpOld =>
    fN63 (Nat.div jp 16) fun jpNew =>
    Bool.casesOn (Nat.beq jpOld jpNew)
    (fN63 (Nat.mod pk 256) fun df8 => fN63 (Nat.mod jpOld 4) fun j00 =>
    fN63 (Nat.mod jpNew 4) fun j01 => fN63 (Nat.div jpOld 4) fun j10 =>
    fN63 (Nat.div jpNew 4) fun j11 => ST4P2.casesOn cur fun s0 s1 =>
    sST4 (advOneST4K2 j00 j01 df8 dw s0) fun s0' => sST4 (advOneST4K2 j10 j11 df8 dw s1) fun s1' =>
    .mk s0' s1') cur
@[inline] def advPairP2K2 (jpNT : NatTree) (sp2 : NatTree) (dw : Nat) (cur : ST4P2) : ST4P2 :=
    NatTree.casesOn sp2 (fun _ => cur) fun l r =>
    NatTree.casesOn l (fun pk0 => NatTree.casesOn r (fun pk1 =>
    sST4P2 (advLeafP2K2 jpNT pk0 dw cur) fun mid =>
    advLeafP2K2 jpNT pk1 dw mid) (fun _ _ => cur)) (fun _ _ => cur)
def advSub6P2K2 (jpNT : NatTree) : NatTree → NatTree → ST4P2 → ST4P2
  | .leaf _, _, cur => cur
  | .node spL spR, .leaf dw, cur =>
      sST4P2 (advPairP2K2 jpNT spL dw cur) fun mid =>
      advPairP2K2 jpNT spR dw mid
  | .node spL spR, .node wL wR, cur =>
      sST4P2 (advSub6P2K2 jpNT spL wL cur) fun mid =>
      advSub6P2K2 jpNT spR wR mid

def buildZLLK2 (cb : ChW11) (lo6NT : NatTree) (p2k step2 wBase : Nat) : Nat → Nat → ZLeafL
  | 0, _ => .nil
  | n + 1, i7 =>
      sZLL (buildZLLK2 cb lo6NT p2k step2 wBase n (Nat.add i7 1)) fun tl =>
      fN63 (Nat.div (Nat.add wBase (Nat.mul 2048 i7)) step2) fun m0 =>
      fN63 (Nat.mul 4 i7) fun b4 =>
      fN63 (chFnFast cb (Nat.div (getNT256F lo6NT b4) p2k)) fun z0 =>
      fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 1)) p2k)) fun z1 =>
      fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 2)) p2k)) fun z2 =>
      fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 3)) p2k)) fun z3 =>
      .cons m0
        (Nat.div z0 256) (Nat.sub 256 (Nat.mod z0 256))
        (Nat.div z1 256) (Nat.sub 256 (Nat.mod z1 256))
        (Nat.div z2 256) (Nat.sub 256 (Nat.mod z2 256))
        (Nat.div z3 256) (Nat.sub 256 (Nat.mod z3 256)) tl

def buildZOct10LK2 (cb : ChW11) : ZOct10L := sNT63 (bNT9 word512DualLegLo6T 0 256) fun lo6 =>
    sZLL (buildZLLK2 cb lo6 16 512 131072 64 0) fun l4lo =>
    sZLL (buildZLLK2 cb lo6 16 256 0 64 64) fun l4hi =>
    sZLL (buildZLLK2 cb lo6 32 128 131072 64 0) fun l5lo =>
    sZLL (buildZLLK2 cb lo6 32 64 0 64 64) fun l5hi =>
    sZLL (buildZLLK2 cb lo6 64 32 131072 64 0) fun l6lo =>
    sZLL (buildZLLK2 cb lo6 64 16 0 64 64) fun l6hi =>
    sZLL (buildZLLK2 cb lo6 128 8 131072 64 0) fun l7lo =>
    sZLL (buildZLLK2 cb lo6 128 4 0 64 64) fun l7hi =>
    sZLL (buildZLLK2 cb lo6 256 2 131072 64 0) fun l8lo =>
    sZLL (buildZLLK2 cb lo6 256 1 0 30 64) fun l8hi =>
    .mk l4lo l4hi l5lo l5hi l6lo l6hi l7lo l7hi l8lo l8hi
@[inline] def pack3WgtFK2 (w : Nat) : Nat :=
    Nat.add (chWgtFK2 .ee w) (Nat.mul 1048576 (Nat.add (chWgtFK2 .nn w)
    (Nat.mul 1048576 (chWgtFK2 .en w))))
@[inline] def unpk3K2 (ch : ChK2) (x : Nat) : Nat :=
    ChK2.casesOn ch (Nat.mod x 1048576) (Nat.mod (Nat.div x 1048576) 1048576)
    (Nat.div x 1099511627776)
def evalLaneVQMPackK2 (ch : ChK2) (v : Nat) (st : SumTree) (q M : Nat) : Nat :=
    Nat.add (Nat.mul v q) (Bool.casesOn (Nat.beq M 256) (unpk3K2 ch (sufST128F st M 0)) 0)
def evalCheckPtPackK2 (ch : ChK2) (va : Nat) (a : SumTree) (vb : Nat) (b : SumTree) (vc : Nat)
    (c : SumTree) (vd : Nat) (d : SumTree) (m q0 M0 q1 M1 q2 M2 q3 M3 g hi lo s0Sq : Nat) : Bool :=
    Bool.casesOn (Nat.beq (Nat.mod m 8) 7) (Bool.casesOn (Nat.beq (Nat.mod m 32) 28)
    (fN63 (Nat.add (Nat.add (evalLaneVQMPackK2 ch va a q0 M0) (evalLaneVQMPackK2 ch vb b q1 M1))
    (Nat.add (evalLaneVQMPackK2 ch vc c q2 M2) (evalLaneVQMPackK2 ch vd d q3 M3))) fun E =>
    checkNum63 E m g hi lo s0Sq) true) true
def scanZLLPackK2 (ch : ChK2) (va : Nat) (a : SumTree) (vb : Nat) (b : SumTree)
    (vc : Nat) (c : SumTree) (vd : Nat) (d : SumTree)
    (qt g hi lo s0Sq : Nat) : ZLeafL → Bool
  | .nil => true
  | .cons m0 q0 M0 q1 M1 q2 M2 q3 M3 tl =>
      andB63
        (evalCheckPtPackK2 ch va a vb b vc c vd d (Nat.add m0 qt) q0 M0 q1 M1 q2 M2 q3 M3 g hi lo
            s0Sq)
        (scanZLLPackK2 ch va a vb b vc c vd d qt g hi lo s0Sq tl)

def checkHalfZLLPackK2 (ch : ChK2) (zl : ZLeafL) (va : Nat) (a : SumTree) (vb : Nat) (b : SumTree)
    (vc : Nat) (c : SumTree) (vd : Nat) (d : SumTree) (t11 step2 g hi lo s0Sq : Nat) : Bool :=
    Bool.casesOn (Nat.beq (Nat.mod t11 step2) 0) true (scanZLLPackK2 ch va a vb b vc c vd d
    (Nat.div t11 step2) g hi lo s0Sq zl)
def checkAtT11ZLLPackK2 (ch : ChK2) (zo : ZOct10L) (t11 : Nat) (st4 : ST4) (g hi lo s0Sq : Nat) :
    Bool := ZOct10L.casesOn zo fun l4lo l4hi l5lo l5hi l6lo l6hi l7lo l7hi l8lo l8hi =>
    ST4.casesOn st4 fun _ a b c d => fN63 (unpk3K2 ch (stVal63 a)) fun va =>
    fN63 (unpk3K2 ch (stVal63 b)) fun vb => fN63 (unpk3K2 ch (stVal63 c)) fun vc =>
    fN63 (unpk3K2 ch (stVal63 d)) fun vd =>
    andB63 (checkHalfZLLPackK2 ch l4lo va a vb b vc c vd d t11 512 g hi lo s0Sq)
    (andB63 (checkHalfZLLPackK2 ch l4hi va a vb b vc c vd d t11 256 g hi lo s0Sq)
    (andB63 (checkHalfZLLPackK2 ch l5lo va a vb b vc c vd d t11 128 g hi lo s0Sq)
    (andB63 (checkHalfZLLPackK2 ch l5hi va a vb b vc c vd d t11 64 g hi lo s0Sq)
    (andB63 (checkHalfZLLPackK2 ch l6lo va a vb b vc c vd d t11 32 g hi lo s0Sq)
    (andB63 (checkHalfZLLPackK2 ch l6hi va a vb b vc c vd d t11 16 g hi lo s0Sq)
    (andB63 (checkHalfZLLPackK2 ch l7lo va a vb b vc c vd d t11 8 g hi lo s0Sq)
    (andB63 (checkHalfZLLPackK2 ch l7hi va a vb b vc c vd d t11 4 g hi lo s0Sq)
    (andB63 (checkHalfZLLPackK2 ch l8lo va a vb b vc c vd d t11 2 g hi lo s0Sq)
    (checkHalfZLLPackK2 ch l8hi va a vb b vc c vd d t11 1 g hi lo s0Sq)))))))))
@[inline] def gSu256PackK2 (ch : ChK2) (st : SumTree) (M : Nat) : Nat :=
    Bool.casesOn (Nat.beq M 0) (Bool.casesOn (Nat.ble 256 M) (unpk3K2 ch (sufST128F st M 0)) 0)
    (unpk3K2 ch (stVal63 st))
@[inline] def evalLane256PackK2 (ch : ChK2) (st : SumTree) (z : Nat) : Nat :=
    Nat.add (Nat.mul (unpk3K2 ch (stVal63 st)) (Nat.div z 256))
    (gSu256PackK2 ch st (Nat.sub 256 (Nat.mod z 256)))
@[inline] def evalST4PackK2 (ch : ChK2) (p : ST4) (z0 z1 z2 z3 : Nat) : Nat :=
    ST4.casesOn p fun _ a b c d => fN63 (evalLane256PackK2 ch a z0) fun e0 =>
    fN63 (evalLane256PackK2 ch b z1) fun e1 => fN63 (evalLane256PackK2 ch c z2) fun e2 =>
    fN63 (evalLane256PackK2 ch d z3) fun e3 => Nat.add (Nat.add (Nat.add e0 e1) e2) e3
def checkPtSkipOtherPackK2 (ch : ChK2) (cb : ChW11) (isNN : Bool) (lo6NT : NatTree) (a r6 : Nat)
    (st4 : ST4) (g hi lo s0Sq d2 : Nat) : Bool :=
    Bool.casesOn (Nat.beq (Nat.mod d2 8) 7) (sParts (evenOctPartsW11 isNN d2) fun p1 t10 k =>
    fN63 (Nat.add (Nat.mul (Nat.mod p1 2) 1024) t10) fun t11 =>
    Bool.casesOn (andB63 (Nat.beq (Nat.div t11 64) a)
    (Nat.beq (Nat.mod t11 64) r6)) true (fN63 (maxDistW11 isNN d2) fun m =>
    fN63 (Nat.div p1 2) fun i7 => fN63 (Nat.pow 2 k) fun p2k => fN63 (Nat.mul 4 i7) fun b4 =>
    fN63 (chFnFast cb (Nat.div (getNT256F lo6NT b4) p2k)) fun z0 =>
    fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 1)) p2k)) fun z1 =>
    fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 2)) p2k)) fun z2 =>
    fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 3)) p2k)) fun z3 =>
    fN63 (evalST4PackK2 ch st4 z0 z1 z2 z3) fun E => checkNum63 E m g hi lo s0Sq)) true
def checkSmAtARPackK2 (ch : ChK2) (cb : ChW11) (isNN : Bool) (lo6NT : NatTree) (a r6 : Nat)
    (st4 : ST4) (g hi lo s0Sq : Nat) : Bool :=
    andB63 (Bool.casesOn (andB63 (Nat.beq r6 0)
    (Nat.beq (Nat.mod a 16) 0)) true (allCnt63 (checkPtSkipOtherPackK2 ch cb isNN lo6NT a 0 st4 g hi
    lo s0Sq) 256 0)) (Bool.casesOn (Nat.beq (Nat.mod a 8) 0) true (allList63 (fun d2 =>
    Bool.casesOn (Nat.beq (Nat.mod d2 64) r6) true (checkPtSkipOtherPackK2 ch cb isNN lo6NT a r6 st4
    g hi lo s0Sq d2)) tail16List))
inductive ChCtx3PackK2 : Type
  | mk : ChW11 → Bool → ZOct10L → Nat → Nat → Nat → Nat → ChCtx3PackK2

def buildChCtx3PackK2 (ch : ChK2) : ChCtx3PackK2 := fN63 (chTotWK2 ch) fun D =>
    fN63 (Nat.mul 64000 (chMcK2 ch)) fun g =>
    fN63 (Nat.mul (Nat.mul (chHiNumK2 ch) 5714023029) D) fun hi =>
    fN63 (Nat.mul (Nat.mul (chLoNumK2 ch) 5714023029) D) fun lo =>
    fN63 (Nat.pow (Nat.mul (Nat.mul (Nat.mul 1000 5714023029) 34359738368) D) 2) fun s0Sq =>
    ZOct10L.casesOn (buildZOct10LK2 (chFnChK2 ch)) fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 =>
    .mk (chFnChK2 ch) (chIsNNK2 ch) (.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) g hi lo s0Sq
def checkOneChPackK2 (ch : ChK2) (ctx : ChCtx3PackK2) (lo6NT : NatTree) (a r6 t11 : Nat)
    (st4 : ST4) : Bool := ChCtx3PackK2.casesOn ctx fun cb isNN zo g hi lo s0Sq =>
    andB63 (checkAtT11ZLLPackK2 ch zo t11 st4 g hi lo s0Sq)
    (checkSmAtARPackK2 ch cb isNN lo6NT a r6 st4 g hi lo s0Sq)
def sweepR6TreeP2PackK2 (lo6NT : NatTree) (ctxEE ctxNN ctxEN : ChCtx3PackK2)
    (a : Nat) (jpNT : NatTree) : Nat → Nat → NatTree → NatTree → ST4P2 → ST4P2B
  | 0, r6, spSub, wgtSub, cur =>
      sST4 (selST4P2 (r01OfR6 r6) cur) fun st4 =>
      fN63 (Nat.add (Nat.mul 64 a) r6) fun t11 =>
      Bool.casesOn (checkOneChPackK2 .ee ctxEE lo6NT a r6 t11 st4) (.mk false cur)
        (Bool.casesOn (checkOneChPackK2 .nn ctxNN lo6NT a r6 t11 st4) (.mk false cur)
          (Bool.casesOn (checkOneChPackK2 .en ctxEN lo6NT a r6 t11 st4) (.mk false cur)
            (sST4P2 (advSub6P2K2 jpNT spSub wgtSub cur) fun nxt => .mk true nxt)))
  | d + 1, b, spSub, wgtSub, cur =>
      NatTree.casesOn spSub (fun _ => .mk false cur) fun spL spR =>
      NatTree.casesOn wgtSub (fun _ => .mk false cur) fun wL wR =>
      sST4P2B (sweepR6TreeP2PackK2 lo6NT ctxEE ctxNN ctxEN a jpNT d b spL wL cur) fun ok1 mid =>
      Bool.casesOn ok1 (.mk false mid)
        (fN63 (Nat.add b (Nat.pow 2 d)) fun b2 =>
         sweepR6TreeP2PackK2 lo6NT ctxEE ctxNN ctxEN a jpNT d b2 spR wR mid)

def checkPairFast3K2 (b : Nat) : Bool := sNT63 (bNT9 word512DualLegLo6T 0 256) fun lo6NT =>
    ChCtx3PackK2.casesOn (buildChCtx3PackK2 .ee) fun cbEE nnEE zoEE gEE hiEE loEE sqEE =>
    ChCtx3PackK2.casesOn (buildChCtx3PackK2 .nn) fun cbNN nnNN zoNN gNN hiNN loNN sqNN =>
    ChCtx3PackK2.casesOn (buildChCtx3PackK2 .en) fun cbEN nnEN zoEN gEN hiEN loEN sqEN =>
    sNT63 spNTFastK2 fun spNT =>
    sNT63 (bNT11 (fun idx11 => pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32)
    (Nat.div idx11 32))) 0 1024) fun wgt3NT => fN63 (Nat.mul 2 b) fun a0 =>
    sNT63 (buildJPackNT a0) fun jp0NT => sST4P2 (initTreeP2FastK2 jp0NT spNT wgt3NT) fun initP2 =>
    sST4P2B (sweepR6TreeP2PackK2 lo6NT (.mk cbEE nnEE zoEE gEE hiEE loEE sqEE)
    (.mk cbNN nnNN zoNN gNN hiNN loNN sqNN)
    (.mk cbEN nnEN zoEN gEN hiEN loEN sqEN) a0 jp0NT 6 0 spNT wgt3NT initP2) fun ok0 midP2 =>
    Bool.casesOn ok0 false (fN63 (Nat.add a0 1) fun a1 => sNT63 (buildJPackNT a1) fun jp1NT =>
    ST4P2B.casesOn (sweepR6TreeP2PackK2 lo6NT (.mk cbEE nnEE zoEE gEE hiEE loEE sqEE)
    (.mk cbNN nnNN zoNN gNN hiNN loNN sqNN)
    (.mk cbEN nnEN zoEN gEN hiEN loEN sqEN) a1 jp1NT 6 0 spNT wgt3NT midP2) fun ok1 _ => ok1)
set_option Elab.async true
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_0 : checkPairFast3K2 0 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_1 : checkPairFast3K2 1 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_2 : checkPairFast3K2 2 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_3 : checkPairFast3K2 3 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_4 : checkPairFast3K2 4 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_5 : checkPairFast3K2 5 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_6 : checkPairFast3K2 6 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_7 : checkPairFast3K2 7 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_8 : checkPairFast3K2 8 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_9 : checkPairFast3K2 9 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_10 : checkPairFast3K2 10 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_11 : checkPairFast3K2 11 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_12 : checkPairFast3K2 12 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_13 : checkPairFast3K2 13 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_14 : checkPairFast3K2 14 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tB2K2_15 : checkPairFast3K2 15 = true := by decide +kernel
set_option Elab.async false
theorem tB2K2_all : ∀ b : Nat, b < 16 → checkPairFast3K2 b = true
  | 0, _ => tB2K2_0 | 1, _ => tB2K2_1 | 2, _ => tB2K2_2 | 3, _ => tB2K2_3 | 4, _ => tB2K2_4
  | 5, _ => tB2K2_5 | 6, _ => tB2K2_6 | 7, _ => tB2K2_7 | 8, _ => tB2K2_8 | 9, _ => tB2K2_9
  | 10, _ => tB2K2_10 | 11, _ => tB2K2_11 | 12, _ => tB2K2_12 | 13, _ => tB2K2_13
  | 14, _ => tB2K2_14 | 15, _ => tB2K2_15 | _ + 16, hb => absurd hb (by omega)
end QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs

namespace QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (clbGam6)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (allBelow allBelow_true_iff
    q01OfR6G6 subBorrows18Core popBernJK2 rowDf8MaskNat rowO9MaskNat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (parity13Aux affineBit13
    pack8Bool pack9Bool)
def sumCarryST256 : Nat → Nat → SumTree → Nat → Nat
  | _, base, .leaf v, z => v * ((z + base) / 256)
  | h, base, .node _ l r, z =>
      sumCarryST256 (h / 2) base l z + sumCarryST256 (h / 2) (base + h) r z

theorem IsTreeOf.sumCarry256 {f : Nat → Nat} {d base : Nat} {st : SumTree}
    (h : IsTreeOf f d base st) (z : Nat) : sumCarryST256 (2 ^ d / 2) base st z =
    ∑ i ∈ Finset.range (2 ^ d), f (base + i) * ((z + (base + i)) / 256) := by
  induction h with
  | leaf base => simp [sumCarryST256]
  | @node d base s l r _ _ _ ihl ihr =>
      have hp2 : 0 < 2 ^ d := Nat.two_pow_pos d
      have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; omega
      have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; ring
      rw [hp]; dsimp only [sumCarryST256]
      rw [ihl, ihr, h2, Finset.sum_range_add]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc])

theorem gSu256F_eq_sumSufST {st : SumTree} (hv : IsValidST 8 st) (M : Nat) : gSu256F st M =
    sumSufST 128 0 st M := by
  unfold gSu256F
  cases h0 : Nat.beq M 0
  · cases h1 : Nat.ble 256 M <;> dsimp only [Bool.casesOn]
    · rw [sufST128F_eq]
      simpa using sufST_eq_sumSufST hv 0 M 0
        (by simpa using Nat.lt_of_not_ge fun h ↦
          Bool.noConfusion (h1.symm.trans (Nat.ble_eq.mpr h)))
    · exact (sumSufST_none hv (Nat.ble_eq.mp h1)).symm
  · dsimp only [Bool.casesOn];
    have hz : M = 0 :=
        Nat.eq_of_beq_eq_true h0; subst hz; rw [stVal63_eq,
        stVal_eq_sumAllST hv]; exact (sumSufST_all (d := 8) hv (Nat.le_refl 0)).symm
theorem sumAll_add_sumSuf_eq_sumCarry256 {d : Nat} {st : SumTree} (hv : IsValidST d st) :
    ∀ {base : Nat} (z : Nat), base + 2 ^ d ≤ 256 → sumAllST st * (z / 256) + sumSufST (2 ^ d /
    2) base st (256 - z % 256) = sumCarryST256 (2 ^ d / 2) base st z := by
  induction hv with
  | leaf v =>
      intro base z hb; dsimp only [sumAllST, sumSufST, sumCarryST256]
      have hdiv : (z + base) / 256 = z / 256 + if 256 - z % 256 ≤ base then 1 else 0 := by
        split_ifs <;> omega
      rw [hdiv]; split_ifs <;> ring
  | @node d _ l r _ _ _ ihl ihr =>
      intro base z hb; have hp2 : 0 < 2 ^ d := Nat.two_pow_pos d
      have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; omega
      have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; ring
      rw [hp]; dsimp only [sumAllST, sumSufST, sumCarryST256]
      have el := ihl (base := base) z (by omega)
      have er := ihr (base := base + 2 ^ d) z (by omega)
      linarith [add_mul (sumAllST l) (sumAllST r) (z / 256)]

theorem evalLane256F_eq_sumCarryST256 {st : SumTree} (hv : IsValidST 8 st)
    (z : Nat) : evalLane256F st z = sumCarryST256 128 0 st z := by
  unfold evalLane256F;
  simp only [nat_add_def, nat_mul_def, nat_div_def, nat_sub_def, nat_mod_def, stVal63_eq];
  rw [stVal_eq_sumAllST hv, gSu256F_eq_sumSufST hv]
  exact sumAll_add_sumSuf_eq_sumCarry256 hv z (by norm_num)

def IsValidST4K2 : ST4 → Prop
  | .mk _ a b c d => IsValidST 8 a ∧ IsValidST 8 b ∧ IsValidST 8 c ∧ IsValidST 8 d

def sumCarryST4K2 (p : ST4) (z0 z1 z2 z3 : Nat) : Nat :=
  match p with
  | .mk _ a b c d =>
      sumCarryST256 128 0 a z0 + sumCarryST256 128 0 b z1 +
      sumCarryST256 128 0 c z2 + sumCarryST256 128 0 d z3

theorem evalST4FK2_eq_sumCarryST4K2 {p : ST4} (hp : IsValidST4K2 p) (z0 z1 z2 z3 : Nat) :
    evalST4FK2 p z0 z1 z2 z3 = sumCarryST4K2 p z0 z1 z2 z3 := by
  rcases p with ⟨_, a, b, c, d⟩
  rcases hp with ⟨va, vb, vc, vd⟩
  unfold evalST4FK2 sumCarryST4K2;
  simp only [fN63_eq, nat_add_def, evalLane256F_eq_sumCarryST256 va,
      evalLane256F_eq_sumCarryST256 vb, evalLane256F_eq_sumCarryST256 vc,
      evalLane256F_eq_sumCarryST256 vd]
def IsST4Of8 (F : Nat → Nat → Nat) : ST4 → Prop
  | .mk _ a b c d =>
      IsTreeOf (F 0) 8 0 a ∧ IsTreeOf (F 1) 8 0 b ∧
      IsTreeOf (F 2) 8 0 c ∧ IsTreeOf (F 3) 8 0 d

theorem IsST4Of8.isValid {F : Nat → Nat → Nat} {p : ST4} (h : IsST4Of8 F p) : IsValidST4K2 p := by
  rcases p with ⟨_, a, b, c, d⟩
  exact ⟨h.1.isValid, h.2.1.isValid, h.2.2.1.isValid, h.2.2.2.isValid⟩

theorem IsST4Of8.congr {F G : Nat → Nat → Nat} {p : ST4} (h : IsST4Of8 F p)
    (hFG : ∀ j < 4, ∀ idx < 256, F j idx = G j idx) : IsST4Of8 G p := by
  rcases p with ⟨_, a, b, c, d⟩
  refine ⟨h.1.congr (fun i hi => by simpa using hFG 0 (by omega) i hi),
    h.2.1.congr (fun i hi => by simpa using hFG 1 (by omega) i hi),
    h.2.2.1.congr (fun i hi => by simpa using hFG 2 (by omega) i hi),
    h.2.2.2.congr (fun i hi => by simpa using hFG 3 (by omega) i hi)⟩

theorem emptyST4K2F_isST4Of8 : IsST4Of8 (fun _ _ => 0) emptyST4K2F := by
  rw [emptyST4K2F_eq]; unfold emptyST4K2; rw [sST63_eq]
  have hz := (zeroST_isTreeOf 8 0).1; exact ⟨hz, hz, hz, hz⟩
attribute [local irreducible] emptyST4K2F emptyST4K2 zeroST8F zeroST

def updAddST4K2 (F : Nat → Nat → Nat) (j idx dw j' idx' : Nat) : Nat :=
    F j' idx' + if j' = j ∧ idx' = idx then dw else 0
def updSubST4K2 (F : Nat → Nat → Nat) (j idx dw j' idx' : Nat) : Nat :=
    F j' idx' - if j' = j ∧ idx' = idx then dw else 0
theorem insST4K2_isST4Of8 {F : Nat → Nat → Nat} {p : ST4} (hp : IsST4Of8 F p) {j idx : Nat}
    (dw : Nat) (hj : j < 4) (hidx : idx < 256) :
    IsST4Of8 (updAddST4K2 F j idx dw) (insST4K2 p j idx dw) := by
  rcases p with ⟨_, a, b, c, d⟩
  rcases hp with ⟨ha, hb, hc, hd⟩
  have ins1 {k t} (ht : IsTreeOf (F k) 8 0 t) (hk : j = k) :
      IsTreeOf (updAddST4K2 F j idx dw k) 8 0 (insST 128 t idx dw) :=
    (show IsTreeOf (updAdd (F k) idx dw) 8 0 _ by
      simpa using (insST_isTreeOf ht idx dw hidx).1).congr fun _ _ => by
        simp [updAdd, updAddST4K2, hk]
  have kp1 {k t} (ht : IsTreeOf (F k) 8 0 t) (hk : k ≠ j) :
      IsTreeOf (updAddST4K2 F j idx dw k) 8 0 t := ht.congr fun _ _ => by simp [updAddST4K2, hk]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp only [insST4K2, fN63_eq, sST63_eq, insST128F_eq] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> first
    | exact ins1 ha rfl | exact ins1 hb rfl | exact ins1 hc rfl | exact ins1 hd rfl
    | exact kp1 ha (by decide) | exact kp1 hb (by decide)
    | exact kp1 hc (by decide) | exact kp1 hd (by decide)

theorem decST4K2_isST4Of8 {F : Nat → Nat → Nat} {p : ST4} (hp : IsST4Of8 F p) {j idx : Nat}
    (dw : Nat) (hj : j < 4) (hidx : idx < 256) (hdw : dw ≤ F j idx) :
    IsST4Of8 (updSubST4K2 F j idx dw) (decST4K2 p j idx dw) := by
  rcases p with ⟨_, a, b, c, d⟩
  rcases hp with ⟨ha, hb, hc, hd⟩
  have sub1 {k t} (ht : IsTreeOf (F k) 8 0 t) (hk : j = k) :
      IsTreeOf (updSubST4K2 F j idx dw k) 8 0 (subSTD 8 t idx dw) :=
    (show IsTreeOf (updSub (F k) idx dw) 8 0 _ by
      simpa using (subSTD_isTreeOf ht idx dw hidx (by simpa [← hk] using hdw)).1).congr
      fun _ _ => by simp [updSub, updSubST4K2, hk]
  have kp1 {k t} (ht : IsTreeOf (F k) 8 0 t) (hk : k ≠ j) :
      IsTreeOf (updSubST4K2 F j idx dw k) 8 0 t := ht.congr fun _ _ => by simp [updSubST4K2, hk]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    unfold decST4K2 <;> simp only [fN63_eq, sST63_eq, subST128F_eq_subSTD] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first
    | exact sub1 ha rfl | exact sub1 hb rfl | exact sub1 hc rfl | exact sub1 hd rfl
    | exact kp1 ha (by decide) | exact kp1 hb (by decide)
    | exact kp1 hc (by decide) | exact kp1 hd (by decide)

theorem addST4K2_isST4Of8 {F G : Nat → Nat → Nat} {p q : ST4} (hp : IsST4Of8 F p)
    (hq : IsST4Of8 G q) : IsST4Of8 (fun j idx => F j idx + G j idx) (addST4K2 p q) := by
  rcases p with ⟨_, a1, b1, c1, d1⟩
  rcases q with ⟨_, a2, b2, c2, d2⟩
  rcases hp with ⟨ha1, hb1, hc1, hd1⟩
  rcases hq with ⟨ha2, hb2, hc2, hd2⟩
  unfold addST4K2 mkST4F; dsimp only
  simp only [sST63_eq, fN63_eq, addST8F_eq];
  exact ⟨(addST_isTreeOf ha1 ha2).1, (addST_isTreeOf hb1 hb2).1, (addST_isTreeOf hc1 hc2).1,
      (addST_isTreeOf hd1 hd2).1⟩
attribute [local irreducible] insST4K2 decST4K2 insST128F subST128F addST4K2 addST8F

theorem bool_mul (a b : Bool) : (if a then 1 else 0) * (if b then 1 else 0) =
    if (a && b) then 1 else 0 := by
  cases a <;> cases b <;> rfl

theorem bitAtF_mul_eq (mask x13 j : ℕ) : bitAtF mask (2 ^ j) * bitAtF x13 (2 ^ j) =
    if (mask.testBit j && x13.testBit j) then 1 else 0 := by
  unfold bitAtF; simp only [nat_mod_def, nat_div_def];
  rw [← b2n_testBit_eq_div_mod mask j, ← b2n_testBit_eq_div_mod x13 j, bool_mul]
theorem parity13Aux_toNat (mask x13 : ℕ) :
    ∀ k : ℕ, (if parity13Aux mask x13.testBit k then 1 else 0) =
      ((if mask.testBit 13 then 1 else 0) +
        ∑ j ∈ Finset.range k, if (mask.testBit j && x13.testBit j) then 1 else 0) % 2
  | 0 => by
      rw [show parity13Aux mask x13.testBit 0 = mask.testBit 13 from rfl,
          Finset.range_zero, Finset.sum_empty, add_zero]
      cases mask.testBit 13 <;> rfl
  | k + 1 => by
      rw [show parity13Aux mask x13.testBit (k + 1) =
            (if mask.testBit k then xor (parity13Aux mask x13.testBit k) (x13.testBit k)
             else parity13Aux mask x13.testBit k) from rfl]
      rw [b2n_ite_xor, parity13Aux_toNat mask x13 k, Finset.sum_range_succ]; omega
theorem par14Pure_eq_affineBit13 {mask : ℕ} (hmask : mask < 16384) (x13 : ℕ) : par14Pure mask x13 =
    if affineBit13 mask x13 then 1 else 0 := by
  unfold par14Pure affineBit13
  rw [parity13Aux_toNat mask x13 13]
  have hm13 : (if mask.testBit 13 then 1 else 0) = mask / 8192 := by
    rw [b2n_testBit_eq_div_mod mask 13, show (2 ^ 13 : ℕ) = 8192 from rfl]
    omega
  have hm0 : (mask % 2) * (x13 % 2) = if (mask.testBit 0 && x13.testBit 0) then 1 else 0 := by
    simpa [bitAtF, nat_mod_def, nat_div_def] using bitAtF_mul_eq mask x13 0
  have hb (k p : ℕ) (hp : 2 ^ k = p) :
      bitAtF mask p * bitAtF x13 p = if (mask.testBit k && x13.testBit k) then 1 else 0 :=
    hp ▸ bitAtF_mul_eq mask x13 k
  simp only [nat_add_def, nat_div_def, nat_mod_def, nat_mul_def, Finset.sum_range_succ,
    Finset.range_zero, Finset.sum_empty, zero_add]
  rw [hm13, hm0, hb 1 2 rfl, hb 2 4 rfl, hb 3 8 rfl, hb 4 16 rfl, hb 5 32 rfl, hb 6 64 rfl,
    hb 7 128 rfl, hb 8 256 rfl, hb 9 512 rfl, hb 10 1024 rfl, hb 11 2048 rfl, hb 12 4096 rfl]
  exact congrArg (· % 2) (by ring)

theorem df8Pure_eq (x13 : ℕ) : df8Pure x13 = (df8Of13 x13).val := by
  have hp (m : ℕ) (h : m < 16384 := by decide) := par14Pure_eq_affineBit13 h x13
  dsimp only [df8Pure, df8Of13, pack8Bool, rowDf8MaskNat]
  simp only [nat_add_def, nat_mul_def, hp 9306, hp 1171, hp 8483, hp 8548,
    hp 9107, hp 818, hp 3480, hp 4148]; ring

theorem o9Pure_eq (x13 : ℕ) : o9Pure x13 = (o9Of13 x13).val := by
  have hp (m : ℕ) (h : m < 16384 := by decide) := par14Pure_eq_affineBit13 h x13
  dsimp only [o9Pure, o9Of13, pack9Bool, pack8Bool, rowO9MaskNat]
  simp only [nat_add_def, nat_mul_def, hp 12203, hp 2682, hp 2285, hp 3832, hp 8193,
    hp 10877, hp 8208, hp 12538, hp 293]; ring

theorem d11OfGO9Pure_eq (g6 o9 : ℕ) : d11OfGO9Pure g6 o9 = d11OfGO9 g6 o9 := by
  unfold d11OfGO9Pure d11OfGO9; simp only [nat_add_def, nat_mul_def, nat_div_def, nat_mod_def]; ring
theorem d11OfGO9_lt (g6 o9 : ℕ) : d11OfGO9 g6 o9 < 2048 := by unfold d11OfGO9; omega
def carry3B (r01 b6 g0 g1 z4 z2 z3 t6 t7 t8 : Bool) : Bool × Bool × Bool :=
  let q01 := andB63 (xorBF true (xorBF r01 g1)) g0; let tb6 := xorBF t6 b6;
  let qEff := xorBF q01 tb6; let za := xorBF z2 qEff; let wC1 := xorBF z3 za;
  let e0 := xorBF (andB63 (xorBF (notBF z4) b6) tb6) b6;
  let c0 := xorBF (andB63 (xorBF (notBF za) t7) (xorBF t8 t7)) t7;
  let c1 := xorBF (andB63 wC1 (xorBF t8 e0)) e0;
  let d2b := xorBF (andB63 (xorBF (notBF z2) e0) (xorBF t7 e0)) e0;
  let c2 := xorBF (andB63 (xorBF (notBF z3) d2b) (xorBF t8 d2b)) d2b
  (c0, c1, c2)

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem q01_r01_cert : allBelow 64 (fun r6 => allBelow 4 (fun g01 => decide (q01OfR6G6 r6 g01 =
    if andB63 (xorBF true (xorBF (r01OfR6 r6) (Nat.beq ((g01 / 2) % 2) 1)))
    (Nat.beq (g01 % 2) 1) then 1 else 0))) = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem carry3B_eq_subBorrows_cert :
    allBelow 8 (fun a3 => allBelow 2 (fun r01 => allBelow 2 (fun b6 =>
      allBelow 4 (fun g01 => allBelow 8 (fun top3 =>
        let c :=
            carry3B (r01 == 1) (b6 == 1) (Nat.beq (g01 % 2) 1) (Nat.beq ((g01 / 2) % 2) 1)
            (Nat.beq (top3 % 2) 1) (Nat.beq ((top3 / 2) % 2) 1) (Nat.beq ((top3 / 4) % 2) 1)
            (Nat.beq (a3 % 2) 1) (Nat.beq ((a3 / 2) % 2) 1) (Nat.beq ((a3 / 4) % 2) 1)
        let q01 :=
            if andB63 (xorBF true (xorBF (r01 == 1) (Nat.beq ((g01 / 2) % 2) 1)))
            (Nat.beq (g01 % 2) 1) then 1 else 0
        let sb := subBorrows18Core a3 b6 q01 (top3 % 2) ((top3 / 2) % 2) ((top3 / 4) % 2)
        decide ((if c.1 then 1 else 0) = sb.1 ∧
                (if c.2.1 then 1 else 0) = sb.2.1 ∧
                (if c.2.2 then 1 else 0) = sb.2.2)))))) = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem d11OfGO9_unpack_cert :
    allBelow 4 (fun g01 => allBelow 512 (fun o9 =>
      let d11 := d11OfGO9 g01 o9
      decide (
        (d11 / 64) % 4 = o9 % 4 ∧
        ((d11 / 64) / 4) % 4 = (o9 / 4) % 4 ∧
        (d11 / 32) % 2 + 2 * (((d11 / 64) / 16) % 2) = (o9 / 16) % 4 ∧
        d11 % 2 = g01 % 2 ∧
        (d11 / 2) % 2 = (g01 / 2) % 2 ∧
        (d11 / 4) % 2 = ((o9 / 64) % 8) % 2 ∧
        (d11 / 8) % 2 = (((o9 / 64) % 8) / 2) % 2 ∧
        (d11 / 16) % 2 = (((o9 / 64) % 8) / 4) % 2))) = true := by
  decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem o9_top_bits_cert : allBelow 512 (fun o9 => decide ( ((o9 / 64) % 8) % 2 = (o9 / 64) % 2 ∧
    (((o9 / 64) % 8) / 2) % 2 = (o9 / 128) % 2 ∧ (((o9 / 64) % 8) / 4) % 2 = (o9 / 256) % 2)) =
    true := by decide +kernel
theorem b2n_congr_prop {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : (if P then 1 else 0) =
    (if Q then 1 else 0) :=
  ite_congr (propext h) (fun _ ↦ rfl) (fun _ ↦ rfl)

theorem j18AtARB_eq_popBernJK2 {a r6 : ℕ} (_ha : a < 32) (hr6 : r6 < 64) (w : Fin 2048)
    (o9 : Fin 512) : j18AtARB a (r01OfR6 r6) (decide (clbGam6 w.val < r6))
    (d11OfGO9 (clbGam6 w.val) o9.val) = popBernJK2 (64 * a + r6) w o9 := by
  set g6 := clbGam6 w.val
  set b6N := if g6 < r6 then 1 else 0
  have hb6_arg : decide (clbGam6 w.val < r6) = (b6N == 1) := by
    dsimp [b6N, g6]; by_cases h : clbGam6 w.val < r6 <;> simp [h]
  rw [hb6_arg]
  set d11 := d11OfGO9 g6 o9.val
  have ho9 := o9.isLt
  have hd11_mod : d11 = d11OfGO9 (g6 % 4) o9.val := by unfold d11 d11OfGO9; omega
  have hd_u := of_decide_eq_true ((allBelow_true_iff 512 _).mp
    ((allBelow_true_iff 4 _).mp d11OfGO9_unpack_cert (g6 % 4) (by omega)) o9.val ho9)
  rw [← hd11_mod] at hd_u; obtain ⟨u0, u1, u2, ug0, ug1, uz4, uz2, uz3⟩ := hd_u
  have ha_u : (64 * a + r6) / 64 = a ∧ (64 * a + r6) % 64 = r6 ∧
      a % 2 = (a % 8) % 2 ∧ (a / 2) % 2 = ((a % 8) / 2) % 2 ∧
      (a / 4) % 2 = ((a % 8) / 4) % 2 := by omega
  obtain ⟨hdiv64, hmod64, ht6, ht7, ht8⟩ := ha_u;
  have ho_top := of_decide_eq_true ((allBelow_true_iff 512 _).mp o9_top_bits_cert o9.val ho9)
  have hq_mod : q01OfR6G6 r6 g6 = q01OfR6G6 r6 (g6 % 4) := by
    unfold q01OfR6G6
    rw [show (g6 % 4) % 2 = g6 % 2 by omega, show ((g6 % 4) / 2) % 2 = (g6 / 2) % 2 by omega]
  have hq01 := of_decide_eq_true ((allBelow_true_iff 4 _).mp
    ((allBelow_true_iff 64 _).mp q01_r01_cert r6 hr6) (g6 % 4) (by omega))
  set r01N := if r01OfR6 r6 then 1 else 0
  have hr01B : (r01N == 1) = r01OfR6 r6 := by dsimp [r01N]; cases r01OfR6 r6 <;> rfl
  have hsb := of_decide_eq_true ((allBelow_true_iff 8 _).mp
    ((allBelow_true_iff 4 _).mp ((allBelow_true_iff 2 _).mp ((allBelow_true_iff 2 _).mp
      ((allBelow_true_iff 8 _).mp carry3B_eq_subBorrows_cert (a % 8) (by omega))
      r01N (by dsimp [r01N]; split_ifs <;> omega))
      b6N (by dsimp [b6N]; split_ifs <;> omega)) (g6 % 4) (by omega))
      ((o9.val / 64) % 8) (by omega))
  rw [hr01B, ← hq01, ← hq_mod, ho_top.1, ho_top.2.1, ho_top.2.2] at hsb;
  unfold j18AtARB j18CarryEval popBernJK2;
  simp only [fN63_eq, sB63_eq, nat_div_def, nat_mod_def, nat_add_def, nat_mul_def];
  rw [j18Sum3_eq, hdiv64, hmod64, u0, u1, u2, ug0, ug1, uz4, uz2, uz3, ho_top.1, ho_top.2.1,
      ho_top.2.2, ht6, ht7,
      ht8]; dsimp only [carry3B] at hsb; have hc1 :=
                                           (b2n_congr_prop Iff.rfl).trans hsb.1;
                                           have hc2 :=
                                           (b2n_congr_prop Iff.rfl).trans hsb.2.1;
                                           have hc3 := (b2n_congr_prop Iff.rfl).trans hsb.2.2
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (b2n_congr_prop (by rw [hc1]))
    (b2n_congr_prop (by rw [hc2]))) (b2n_congr_prop (by rw [hc3]))

def wAt13 (i : Nat) : Nat := wOfU5Gam ((i % 128) / 4) (i / 128)
def x13At13 (i : Nat) : Nat := wAt13 i + 2048 * ((i % 128) % 4)
def df8At13 (i : Nat) : Nat := (df8Of13 (x13At13 i)).val
def o9At13 (i : Nat) : Fin 512 := o9Of13 (x13At13 i)
def dwAt13 (ch : ChK2) (i : Nat) : Nat := chWgtK2 ch (wAt13 i)
def d11At13 (i : Nat) : Nat := d11OfGO9 (i / 128) (o9At13 i).val
def j18At13 (a : Nat) (r01 b6 : Bool) (i : Nat) : Nat := j18AtARB a r01 b6 (d11At13 i)

theorem dwAt13_ee_le (i : Nat) : dwAt13 .ee i ≤ 82 := by
  unfold dwAt13; rw [← chWgtFK2_eq]; unfold chWgtFK2; dsimp only
  cases Nat.ble (Nat.add (wAt13 i) 1) 1452 <;> dsimp only [Bool.casesOn] <;> omega

theorem dwAt13_nn_le (i : Nat) : dwAt13 .nn i ≤ 82 := by
  unfold dwAt13; rw [← chWgtFK2_eq]; unfold chWgtFK2; dsimp only
  cases Nat.ble (Nat.add (wAt13 i) 1) 1750 <;> dsimp only [Bool.casesOn] <;> omega

theorem df8At13_lt_256 (i : Nat) : df8At13 i < 256 := (df8Of13 (x13At13 i)).isLt
theorem d11At13_lt_2048 (i : Nat) : d11At13 i < 2048 := d11OfGO9_lt _ _
theorem j18At13_lt_four (a : Nat) (r01 b6 : Bool) (i : Nat) : j18At13 a r01 b6 i < 4 :=
    j18AtARB_lt_four a r01 b6 (d11At13 i)
theorem j18At13_even_true_eq_odd_false {a : Nat} (ha : a % 2 = 0) (r01 : Bool)
    (i : Nat) : j18At13 a r01 true i = j18At13 (a + 1) r01 false i :=
    j18AtARB_even_true_eq_odd_false ha r01 (d11At13 i)
theorem jPack4Leaf_unpack_at13 (a i : Nat) : jPack4Leaf a (d11At13 i) % 4 =
    j18At13 a false false i ∧ (jPack4Leaf a (d11At13 i) / 4) % 4 = j18At13 a true false i ∧
    (jPack4Leaf a (d11At13 i) / 16) % 4 = j18At13 a false true i ∧ jPack4Leaf a (d11At13 i) / 64 =
    j18At13 a true true i := jPack4Leaf_unpack a (d11At13 i)
theorem samplePackLeafK2Pure_eq_pack13 {i : Nat} (hi : i < 8192) : samplePackLeafK2Pure i =
    df8At13 i + 256 * d11At13 i := by
  unfold samplePackLeafK2Pure df8At13 d11At13 o9At13 x13At13 wAt13;
  simp only [fN63_eq, nat_div_def, nat_mod_def, nat_add_def, nat_mul_def]
  rw [wOfU5GamF_eq_spec ⟨(i % 128) / 4, by omega⟩ ⟨i / 128, by omega⟩,
      df8Pure_eq, o9Pure_eq, d11OfGO9Pure_eq]

def pack3NatK2 (v0 v1 v2 : Nat) : Nat := v0 + 1048576 * (v1 + 1048576 * v2)

theorem pack3NatK2_zero : pack3NatK2 0 0 0 = 0 := rfl

theorem pack3NatK2_add (a0 a1 a2 b0 b1 b2 : Nat) : pack3NatK2 a0 a1 a2 + pack3NatK2 b0 b1 b2 =
    pack3NatK2 (a0 + b0) (a1 + b1) (a2 + b2) := by unfold pack3NatK2; ring
theorem unpk3K2_pack3NatK2 (ch : ChK2) {v0 v1 : Nat} (v2 : Nat)
    (h0 : v0 < 1048576) (h1 : v1 < 1048576) :
    unpk3K2 ch (pack3NatK2 v0 v1 v2) =
      match ch with | .ee => v0 | .nn => v1 | .en => v2 := by
  cases ch <;> {
    unfold unpk3K2 pack3NatK2; dsimp only; simp only [nat_mod_def, nat_div_def]; omega
  }

def dwPack13 (i : Nat) : Nat := pack3NatK2 (dwAt13 .ee i) (dwAt13 .nn i) (dwAt13 .en i)
def buildSamplePackK2NT : NatTree := buildNT63 samplePackLeafK2Pure 13 0 4096
def buildWgtPackK2NT : NatTree :=
    buildNT63 (fun idx11 => pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32))) 11 0 1024
theorem buildSamplePackK2NT_def :
    buildNT63 samplePackLeafK2Pure 13 0 4096 = buildSamplePackK2NT := rfl

theorem buildWgtPackK2NT_def :
    buildNT63 (fun idx11 => pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32)
        (Nat.div idx11 32))) 11 0 1024 =
      buildWgtPackK2NT := rfl

theorem spNTFastK2_eq : spNTFastK2 = buildSamplePackK2NT :=
    (beqNT_eq tSpEqK2).trans (bNT13_eq samplePackLeafK2Pure 0 4096)
theorem bNT11_wgtPackK2_eq : bNT11 (fun idx11 => pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32)
    (Nat.div idx11 32))) 0 1024 = buildWgtPackK2NT := bNT11_eq _ 0 1024
attribute [local irreducible] spNTFastK2 buildSamplePackK2NT buildWgtPackK2NT

theorem wgtLeafFK2_eq_dwAt13 (ch : ChK2) {idx11 : Nat} (h11 : idx11 < 2048)
    (c : Fin 4) : chWgtFK2 ch (wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)) =
    dwAt13 ch (4 * idx11 + c.val) := by
  rw [nat_mod_def, nat_div_def, chWgtFK2_eq,
      wOfU5GamF_eq_spec ⟨idx11 % 32, by omega⟩ ⟨idx11 / 32, by omega⟩]
  unfold dwAt13 wAt13
  rw [show ((4 * idx11 + c.val) % 128) / 4 = idx11 % 32 by omega,
      show (4 * idx11 + c.val) / 128 = idx11 / 32 by omega]

theorem pack3WgtFK2_eq_dwPack13 {idx11 : Nat} (h11 : idx11 < 2048)
    (c : Fin 4) : pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)) =
    dwPack13 (4 * idx11 + c.val) := by
  unfold pack3WgtFK2 dwPack13 pack3NatK2; simp only [nat_add_def, nat_mul_def];
  rw [wgtLeafFK2_eq_dwAt13 .ee h11 c, wgtLeafFK2_eq_dwAt13 .nn h11 c,
      wgtLeafFK2_eq_dwAt13 .en h11 c]
def nLanes8 : Nat := 256
theorem nLanes8_eq : nLanes8 = 256 := rfl
def nSamples13 : Nat := 8192
theorem nSamples13_eq : nSamples13 = 8192 := rfl

def sweepBktK2 (ch : ChK2) (a : Nat) (r01 : Bool) (p j idx : Nat) : Nat :=
    ∑ i ∈ Finset.range nSamples13, if j18At13 a r01 (decide (i < p)) i = j ∧ df8At13 i =
    idx then dwAt13 ch i else 0
def initBktPackK2 (a : Nat) (r01 : Bool) (b n j idx : Nat) : Nat :=
    ∑ k ∈ Finset.range n, if j18At13 a r01 false (b + k) = j ∧ df8At13 (b + k) =
    idx then dwPack13 (b + k) else 0
def sweepBktPackK2 (a : Nat) (r01 : Bool) (p j idx : Nat) : Nat :=
    ∑ i ∈ Finset.range nSamples13, if j18At13 a r01 (decide (i < p)) i = j ∧ df8At13 i =
    idx then dwPack13 i else 0
def transBktPackK2 (jOld jNew : Bool → Nat → Nat) (r01 : Bool) (p j idx : Nat) : Nat :=
    ∑ i ∈ Finset.range nSamples13, if (if i < p then jNew r01 i else jOld r01 i) = j ∧ df8At13 i =
    idx then dwPack13 i else 0
theorem sweepBktPackK2_eq_pack3 (a : Nat) (r01 : Bool)
    (p j idx : Nat) : sweepBktPackK2 a r01 p j idx = pack3NatK2 (sweepBktK2 .ee a r01 p j idx)
    (sweepBktK2 .nn a r01 p j idx) (sweepBktK2 .en a r01 p j idx) := by
  unfold sweepBktPackK2 sweepBktK2 dwPack13 pack3NatK2;
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

attribute [local irreducible]
  nLanes8 nSamples13 wAt13 x13At13 df8At13 o9At13 dwAt13 dwPack13 d11At13 j18At13 jPack4Leaf
  bNT11 spNTFastK2 buildSamplePackK2NT buildWgtPackK2NT
  emptyST4K2F emptyST4K2 zeroST8F insST4K2 decST4K2

def IsST4P2Of8 (F0 F1 : Nat → Nat → Nat) : ST4P2 → Prop
  | .mk s0 s1 => IsST4Of8 F0 s0 ∧ IsST4Of8 F1 s1

theorem IsST4P2Of8.congr {F0 F1 F0' F1' : Nat → Nat → Nat} {p : ST4P2} (h : IsST4P2Of8 F0 F1 p)
    (h0 : ∀ j < 4, ∀ idx < 256, F0 j idx = F0' j idx) (h1 : ∀ j < 4, ∀ idx < 256, F1 j idx =
    F1' j idx) : IsST4P2Of8 F0' F1' p := by
  rcases p with ⟨s0, s1⟩
  exact ⟨h.1.congr h0, h.2.congr h1⟩

def IsST4P2PackOfK2 (a p : Nat) (cur : ST4P2) : Prop :=
    IsST4P2Of8 (sweepBktPackK2 a false p) (sweepBktPackK2 a true p) cur
def IsST4P2PackTransK2 (jOld jNew : Bool → Nat → Nat) (p : Nat) (cur : ST4P2) : Prop :=
    IsST4P2Of8 (transBktPackK2 jOld jNew false p) (transBktPackK2 jOld jNew true p) cur
theorem sweepBktPackK2_eq_trans (a : Nat) (r01 : Bool) (p : Nat) : sweepBktPackK2 a r01 p =
    transBktPackK2 (fun r i => j18At13 a r false i) (fun r i => j18At13 a r true i) r01 p := by
  funext j idx; unfold sweepBktPackK2 transBktPackK2
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hlt : i < p <;> simp [hlt]

theorem selST4P2PackK2_sound {a p : Nat} {cur : ST4P2} (h : IsST4P2PackOfK2 a p cur)
    (r01 : Bool) : IsST4Of8 (sweepBktPackK2 a r01 p) (selST4P2 r01 cur) := by
  rcases cur with ⟨s0, s1⟩
  cases r01
  · exact h.1
  · exact h.2

def IsST4T3Sum8 (F0 F1 : Nat → Nat → Nat) : ST4T3 → Prop
  | .mk sc s0 s1 =>
      ∃ Fc G0 G1 : Nat → Nat → Nat,
        IsST4Of8 Fc sc ∧ IsST4Of8 G0 s0 ∧ IsST4Of8 G1 s1 ∧
        (∀ j < 4, ∀ idx < 256, Fc j idx + G0 j idx = F0 j idx) ∧
        (∀ j < 4, ∀ idx < 256, Fc j idx + G1 j idx = F1 j idx)

theorem IsST4T3Sum8.congr {F0 F1 F0' F1' : Nat → Nat → Nat} {t : ST4T3} (h : IsST4T3Sum8 F0 F1 t)
    (h0 : ∀ j < 4, ∀ idx < 256, F0 j idx = F0' j idx) (h1 : ∀ j < 4, ∀ idx < 256, F1 j idx =
    F1' j idx) : IsST4T3Sum8 F0' F1' t := by
  rcases t with ⟨sc, s0, s1⟩
  rcases h with ⟨Fc, G0, G1, hsc, hs0, hs1, e0, e1⟩
  exact ⟨Fc, G0, G1, hsc, hs0, hs1, fun j hj idx hi => (e0 j hj idx hi).trans (h0 j hj idx hi),
      fun j hj idx hi => (e1 j hj idx hi).trans (h1 j hj idx hi)⟩

theorem emptyST4T3K2F_isST4T3Sum8 : IsST4T3Sum8 (fun _ _ => 0) (fun _ _ => 0) emptyST4T3K2F := by
  unfold emptyST4T3K2F; rw [sST4_eq]
  exact ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    emptyST4K2F_isST4Of8, emptyST4K2F_isST4Of8, emptyST4K2F_isST4Of8,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem initLeafT3K2_sound (a : Nat) {i : Nat} (hi : i < 8192) {F0 F1 : Nat → Nat → Nat}
    {cur : ST4T3} (hcur : IsST4T3Sum8 F0 F1 cur) :
    IsST4T3Sum8 (updAddST4K2 F0 (j18At13 a false false i) (df8At13 i) (dwPack13 i))
    (updAddST4K2 F1 (j18At13 a true false i) (df8At13 i) (dwPack13 i))
    (initLeafT3K2 (bNT11 (jPack4Leaf a) 0 1024) (samplePackLeafK2Pure i) (dwPack13 i) cur) := by
  rcases cur with ⟨sc, s0, s1⟩
  rcases hcur with ⟨Fc, G0, G1, hsc, hs0, hs1, e0, e1⟩
  rw [samplePackLeafK2Pure_eq_pack13 hi]; have hdf8 := df8At13_lt_256 i;
  have hd11 := d11At13_lt_2048 i; unfold initLeafT3K2; simp only [fN63_eq, nat_mod_def, nat_div_def]
  have hm256 : (df8At13 i + 256 * d11At13 i) % 256 = df8At13 i := by omega
  have hd256 : (df8At13 i + 256 * d11At13 i) / 256 = d11At13 i := by omega
  rw [hm256, hd256, get_bNT11 (jPack4Leaf a) hd11];
  obtain ⟨u00, u10, _, _⟩ := jPack4Leaf_unpack_at13 a i; rw [u00, u10]
  cases hbeq : Nat.beq (j18At13 a false false i) (j18At13 a true false i)
  · dsimp only [Bool.casesOn]; simp only [sST4_eq]
    refine ⟨Fc, updAddST4K2 G0 (j18At13 a false false i) (df8At13 i)
        (dwPack13 i), updAddST4K2 G1 (j18At13 a true false i) (df8At13 i)
        (dwPack13 i), hsc, insST4K2_isST4Of8 hs0 (dwPack13 i)
        (j18At13_lt_four a false false i) hdf8, insST4K2_isST4Of8 hs1 (dwPack13 i)
        (j18At13_lt_four a true false i) hdf8, fun j hj idx hidx => ?_, fun j hj idx hidx => ?_⟩
    · have h := e0 j hj idx hidx; unfold updAddST4K2; split_ifs <;> omega
    · have h := e1 j hj idx hidx; unfold updAddST4K2; split_ifs <;> omega
  · dsimp only [Bool.casesOn]; simp only [sST4_eq]
    have hjEq : j18At13 a false false i = j18At13 a true false i := Nat.beq_eq.mp hbeq
    refine ⟨updAddST4K2 Fc (j18At13 a false false i) (df8At13 i) (dwPack13 i), G0, G1,
        insST4K2_isST4Of8 hsc (dwPack13 i) (j18At13_lt_four a false false i) hdf8, hs0, hs1,
        fun j hj idx hidx => ?_, fun j hj idx hidx => ?_⟩
    · have h := e0 j hj idx hidx; unfold updAddST4K2; split_ifs <;> omega
    · have h := e1 j hj idx hidx; rw [← hjEq]; unfold updAddST4K2; split_ifs <;> omega

theorem initPairT3K2_sound (a : Nat) {m dw : Nat} (hm : 2 * m + 1 < 8192)
    (hdw0 : dw = dwPack13 (2 * m)) (hdw1 : dw = dwPack13 (2 * m + 1)) {F0 F1 : Nat → Nat → Nat}
    {cur : ST4T3} (hcur : IsST4T3Sum8 F0 F1 cur) : IsST4T3Sum8 (fun j idx => F0 j idx +
    initBktPackK2 a false (2 * m) 2 j idx) (fun j idx => F1 j idx + initBktPackK2 a true (2 *
    m) 2 j idx) (initPairT3K2 (bNT11 (jPack4Leaf a) 0 1024)
    (buildNT63 samplePackLeafK2Pure 1 (2 * m) 1) dw cur) := by
  rw [buildNT63_succ samplePackLeafK2Pure 0 (2 * m) 1, show (1 / 2 : Nat) = 0 from rfl,
      buildNT63_zero, buildNT63_zero]
  unfold initPairT3K2; dsimp only; rw [sST4T3_eq]
  have h0 : IsST4T3Sum8 (updAddST4K2 F0 (j18At13 a false false (2 * m)) (df8At13 (2 * m))
      (dwPack13 (2 * m))) (updAddST4K2 F1 (j18At13 a true false (2 * m)) (df8At13 (2 * m))
      (dwPack13 (2 * m))) (initLeafT3K2 (bNT11 (jPack4Leaf a) 0 1024)
      (samplePackLeafK2Pure (2 * m)) dw cur) := by
    rw [hdw0]; exact initLeafT3K2_sound a (by omega) hcur
  set mid := initLeafT3K2 (bNT11 (jPack4Leaf a) 0 1024) (samplePackLeafK2Pure (2 * m)) dw cur
  have h1 : IsST4T3Sum8 (updAddST4K2 (updAddST4K2 F0 (j18At13 a false false (2 * m))
      (df8At13 (2 * m)) (dwPack13 (2 * m))) (j18At13 a false false (2 * m + 1))
      (df8At13 (2 * m + 1)) (dwPack13 (2 * m + 1)))
      (updAddST4K2 (updAddST4K2 F1 (j18At13 a true false (2 * m)) (df8At13 (2 * m))
      (dwPack13 (2 * m))) (j18At13 a true false (2 * m + 1)) (df8At13 (2 * m + 1))
      (dwPack13 (2 * m + 1))) (initLeafT3K2 (bNT11 (jPack4Leaf a) 0 1024)
      (samplePackLeafK2Pure (2 * m + 1)) dw mid) := by rw [hdw1]; exact initLeafT3K2_sound a hm h0
  refine h1.congr (fun j _ idx _ => ?_) (fun j _ idx _ => ?_) <;> {
    simp only [updAddST4K2, initBktPackK2, Finset.sum_range_succ, Finset.range_zero,
        Finset.sum_empty, zero_add, add_zero]
    split_ifs <;> omega
  }

theorem initTreeT3K2_sound (a : Nat) :
    ∀ (d b11 : Nat) {F0 F1 : Nat → Nat → Nat} {cur : ST4T3},
      b11 + 2 ^ d ≤ 2048 →
      IsST4T3Sum8 F0 F1 cur →
      IsST4T3Sum8
        (fun j idx => F0 j idx + initBktPackK2 a false (4 * b11) (2 ^ (d + 2)) j idx)
        (fun j idx => F1 j idx + initBktPackK2 a true (4 * b11) (2 ^ (d + 2)) j idx)
        (initTreeT3K2 (bNT11 (jPack4Leaf a) 0 1024)
          (buildNT63 samplePackLeafK2Pure (d + 2) (4 * b11) (2 ^ (d + 1)))
          (buildNT63 (fun idx11 => pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)))
            d b11 (2 ^ d / 2))
          cur)
  | 0, b11, F0, F1, cur, hb, hcur => by
      have hw {k m : Nat} (hk : k < 4 := by omega) (hm : 4 * b11 + k = m := by omega) :=
        (pack3WgtFK2_eq_dwPack13 (by omega : b11 < 2048) ⟨k, hk⟩).trans (congrArg dwPack13 hm)
      rw [show (2 ^ (0 + 1) : Nat) = 2 from rfl, show (2 ^ 0 / 2 : Nat) = 0 from rfl,
        buildNT63_succ samplePackLeafK2Pure 1 (4 * b11) 2, show (2 / 2 : Nat) = 1 from rfl,
        buildNT63_zero]
      dsimp only [initTreeT3K2]
      rw [sST4T3_eq]
      have hL := initPairT3K2_sound a (m := 2 * b11) (by omega) (hw (k := 0)) (hw (k := 1)) hcur
      rw [show 2 * (2 * b11) = 4 * b11 by omega] at hL
      have hR := initPairT3K2_sound a (m := 2 * b11 + 1) (by omega) (hw (k := 2)) (hw (k := 3)) hL
      rw [show 2 * (2 * b11 + 1) = 4 * b11 + 2 by omega] at hR
      refine hR.congr (fun j _ idx _ => ?_) (fun j _ idx _ => ?_) <;>
        simp only [initBktPackK2, show (2 ^ 2 : Nat) = 2 + 2 from rfl, Finset.sum_range_add,
          add_assoc]
  | d + 1, b11, F0, F1, cur, hb, hcur => by
      have hp1 : 2 ^ (d + 2) / 2 = 2 ^ (d + 1) := by
        rw [Nat.pow_succ]; have := Nat.two_pow_pos (d + 1); omega
      have hp0 : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
      rw [hp0, buildNT63_succ samplePackLeafK2Pure (d + 2), hp1, buildNT63_succ (fun idx11 =>
          pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32))) d]
      dsimp only [initTreeT3K2]; rw [sST4T3_eq]
      have hL := initTreeT3K2_sound a d b11 (by rw [Nat.pow_succ] at hb; omega) hcur
      have h4b : 4 * b11 + 2 ^ (d + 2) = 4 * (b11 + 2 ^ d) := by
        rw [show 2 ^ (d + 2) = 4 * 2 ^ d by rw [Nat.pow_add]; ring]; ring
      rw [h4b]
      have hR := initTreeT3K2_sound a d (b11 + 2 ^ d) (by rw [Nat.pow_succ] at hb; omega) hL
      have hpow : 2 ^ (d + 3) = 2 ^ (d + 2) + 2 ^ (d + 2) := by rw [Nat.pow_succ]; ring
      refine hR.congr (fun j _ idx _ => ?_) (fun j _ idx _ => ?_) <;> {
        unfold initBktPackK2; rw [hpow, Finset.sum_range_add, ← h4b, add_assoc]
        exact congrArg (_ + ·) (congrArg (_ + ·)
          (Finset.sum_congr rfl fun k _ => by rw [Nat.add_assoc]))
      }

theorem initTreeP2FastK2_of_sum {F0 F1 : Nat → Nat → Nat} (jpNT spNT wgtNT : NatTree)
    (h : IsST4T3Sum8 F0 F1 (initTreeT3K2 jpNT spNT wgtNT emptyST4T3K2F)) :
    IsST4P2Of8 F0 F1 (initTreeP2FastK2 jpNT spNT wgtNT) := by
  unfold initTreeP2FastK2
  rcases hT : initTreeT3K2 jpNT spNT wgtNT emptyST4T3K2F with ⟨sc, s0, s1⟩
  rw [hT] at h; dsimp only; simp only [sST4_eq]
  rcases h with ⟨Fc, G0, G1, hsc, hs0, hs1, e0, e1⟩
  exact ⟨(addST4K2_isST4Of8 hsc hs0).congr e0, (addST4K2_isST4Of8 hsc hs1).congr e1⟩

theorem initTreeP2FastK2_isST4P2PackOf (a : Nat) :
    IsST4P2PackOfK2 a 0 (initTreeP2FastK2 (bNT11 (jPack4Leaf a) 0 1024) buildSamplePackK2NT
    buildWgtPackK2NT) := by
  have hInit := initTreeT3K2_sound a 11 0 (by norm_num) emptyST4T3K2F_isST4T3Sum8
  simp only [show 4 * 0 = 0 from rfl, show 11 + 2 = 13 from rfl,
    show (2 ^ (11 + 1) : Nat) = 4096 by norm_num, show (2 ^ 11 / 2 : Nat) = 1024 by norm_num,
    buildSamplePackK2NT_def, buildWgtPackK2NT_def] at hInit
  refine (initTreeP2FastK2_of_sum _ _ _ hInit).congr
      (fun j _ idx _ => ?_) (fun j _ idx _ => ?_) <;> {
    rw [zero_add, show (2 ^ 13 : Nat) = 8192 by norm_num, ← nSamples13_eq]
    unfold initBktPackK2 sweepBktPackK2
    exact Finset.sum_congr rfl fun k _ => by rw [zero_add, decide_eq_false (Nat.not_lt_zero k)]
  }

theorem advLeafP2K2_eq (jpNT : NatTree) (pk dw : Nat) (s0 s1 : ST4) :
    let jp := getNT1024F jpNT (pk / 256)
    advLeafP2K2 jpNT pk dw (.mk s0 s1) =
      .mk (advOneST4K2 (jp % 4) ((jp / 16) % 4) (pk % 256) dw s0)
          (advOneST4K2 ((jp / 4) % 4) (jp / 64) (pk % 256) dw s1) := by
  dsimp only; unfold advLeafP2K2
  simp only [fN63_eq, nat_div_def, nat_mod_def]
  set jp := getNT1024F jpNT (pk / 256)
  have hm0 : (jp % 16) % 4 = jp % 4 := by omega
  have hd0 : (jp % 16) / 4 = (jp / 4) % 4 := by omega
  have hd1 : (jp / 16) / 4 = jp / 64 := by omega
  cases hbeq : Nat.beq (jp % 16) (jp / 16)
  · dsimp only [Bool.casesOn]; simp only [sST4_eq];
    rw [hm0, hd0, hd1]
  · dsimp only [Bool.casesOn]; have heq : jp % 16 = jp / 16 := Nat.beq_eq.mp hbeq
    have hj0 : jp % 4 = (jp / 16) % 4 := by rw [← hm0, heq]
    have hj1 : (jp / 4) % 4 = jp / 64 := by rw [← hd0, heq, hd1]
    unfold advOneST4K2
    rw [show Nat.beq (jp % 4) ((jp / 16) % 4) = true from Nat.beq_eq.mpr hj0,
        show Nat.beq ((jp / 4) % 4) (jp / 64) = true from Nat.beq_eq.mpr hj1]

theorem advOneST4K2_pack_sound (jOld jNew : Bool → Nat → Nat) (r01 : Bool)
    (hOld4 : ∀ i, jOld r01 i < 4) (hNew4 : ∀ i, jNew r01 i < 4) {p : Nat} (hp : p < 8192) {s : ST4}
    (hs : IsST4Of8 (transBktPackK2 jOld jNew r01 p) s) : IsST4Of8 (transBktPackK2 jOld jNew r01 (p +
    1)) (advOneST4K2 (jOld r01 p) (jNew r01 p) (df8At13 p) (dwPack13 p) s) := by
  unfold advOneST4K2
  have hNe {i : Nat} (hne : i ≠ p) : (if i < p then jNew r01 i else jOld r01 i) =
      if i < p + 1 then jNew r01 i else jOld r01 i := by split_ifs <;> omega
  by_cases hjEq : jOld r01 p = jNew r01 p
  · rw [Nat.beq_eq.mpr hjEq]
    refine hs.congr fun j _ idx _ => Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i p with rfl | hip
    · rw [_root_.ite_eq_right (Nat.lt_irrefl i), _root_.ite_eq_left (Nat.lt_succ_self i), hjEq]
    · rw [hNe hip]
  · rw [Bool.eq_false_iff.mpr (mt Nat.beq_eq.mp hjEq), sST4_eq]
    have hmem : p ∈ Finset.range nSamples13 := Finset.mem_range.mpr (hp.trans_eq nSamples13_eq.symm)
    have hdw_le : dwPack13 p ≤ transBktPackK2 jOld jNew r01 p (jOld r01 p) (df8At13 p) := by
      have hle := Finset.single_le_sum
        (f := fun i => if (if i < p then jNew r01 i else jOld r01 i) = jOld r01 p ∧
          df8At13 i = df8At13 p then dwPack13 i else 0) (fun _ _ => Nat.zero_le _) hmem
      rwa [_root_.ite_eq_right (Nat.lt_irrefl p), _root_.ite_eq_left ⟨rfl, rfl⟩] at hle
    refine (insST4K2_isST4Of8
      (decST4K2_isST4Of8 hs (dwPack13 p) (hOld4 p) (df8At13_lt_256 p) hdw_le)
      (dwPack13 p) (hNew4 p) (df8At13_lt_256 p)).congr fun j _ idx _ => ?_
    simp only [updAddST4K2, updSubST4K2]
    unfold transBktPackK2
    rw [← Finset.add_sum_erase (Finset.range nSamples13) _ hmem,
      ← Finset.add_sum_erase (Finset.range nSamples13)
        (fun i => if (if i < p + 1 then jNew r01 i else jOld r01 i) = j ∧ df8At13 i = idx
          then dwPack13 i else 0) hmem,
      Finset.sum_congr rfl fun x hx => by rw [hNe (Finset.mem_erase.mp hx).1],
      _root_.ite_eq_right (Nat.lt_irrefl p), _root_.ite_eq_left (Nat.lt_succ_self p)]
    exact updAdd_updSub_bkt hjEq
theorem advLeafP2K2_pack_sound (jpLeaf : Nat → Nat) (jOld jNew : Bool → Nat → Nat)
    (hOld4 : ∀ r i, jOld r i < 4) (hNew4 : ∀ r i, jNew r i < 4)
    (hUnpack : ∀ i, i < 8192 → jpLeaf (d11At13 i) % 4 = jOld false i ∧ (jpLeaf (d11At13 i) /
    4) % 4 = jOld true i ∧ (jpLeaf (d11At13 i) / 16) % 4 = jNew false i ∧ jpLeaf (d11At13 i) / 64 =
    jNew true i) {p : Nat} (hp : p < 8192) {cur : ST4P2}
    (hcur : IsST4P2PackTransK2 jOld jNew p cur) : IsST4P2PackTransK2 jOld jNew (p + 1)
    (advLeafP2K2 (bNT11 jpLeaf 0 1024) (samplePackLeafK2Pure p) (dwPack13 p) cur) := by
  rcases cur with ⟨s0, s1⟩
  rcases hcur with ⟨hs0, hs1⟩
  rw [samplePackLeafK2Pure_eq_pack13 hp, advLeafP2K2_eq]; have hd11 := d11At13_lt_2048 p;
  have hdf8 := df8At13_lt_256 p
  have hm256 : (df8At13 p + 256 * d11At13 p) % 256 = df8At13 p := by omega
  have hd256 : (df8At13 p + 256 * d11At13 p) / 256 = d11At13 p := by omega
  rw [hm256, hd256, get_bNT11 jpLeaf hd11];
  obtain ⟨u00, u10, u01, u11⟩ :=
      hUnpack p hp; rw [u00, u10, u01,
      u11]; exact ⟨advOneST4K2_pack_sound jOld jNew false (hOld4 false) (hNew4 false) hp hs0,
      advOneST4K2_pack_sound jOld jNew true (hOld4 true) (hNew4 true) hp hs1⟩
theorem advPairP2K2_pack_sound (jpLeaf : Nat → Nat) (jOld jNew : Bool → Nat → Nat)
    (hOld4 : ∀ r i, jOld r i < 4) (hNew4 : ∀ r i, jNew r i < 4)
    (hUnpack : ∀ i, i < 8192 → jpLeaf (d11At13 i) % 4 = jOld false i ∧ (jpLeaf (d11At13 i) /
    4) % 4 = jOld true i ∧ (jpLeaf (d11At13 i) / 16) % 4 = jNew false i ∧ jpLeaf (d11At13 i) / 64 =
    jNew true i) {m dw : Nat} (hm : 2 * m + 1 < 8192) (hdw0 : dw = dwPack13 (2 * m))
    (hdw1 : dw = dwPack13 (2 * m + 1)) {cur : ST4P2}
    (hcur : IsST4P2PackTransK2 jOld jNew (2 * m) cur) : IsST4P2PackTransK2 jOld jNew (2 * m + 2)
    (advPairP2K2 (bNT11 jpLeaf 0 1024) (buildNT63 samplePackLeafK2Pure 1 (2 * m) 1) dw cur) := by
  rw [buildNT63_succ samplePackLeafK2Pure 0 (2 * m) 1, show (1 / 2 : Nat) = 0 from rfl,
      buildNT63_zero, buildNT63_zero]
  unfold advPairP2K2; dsimp only; rw [sST4P2_eq]
  set mid := advLeafP2K2 (bNT11 jpLeaf 0 1024) (samplePackLeafK2Pure (2 * m)) dw cur
  have h0 : IsST4P2PackTransK2 jOld jNew (2 * m + 1) mid := by
    dsimp only [mid]; rw [hdw0]
    exact advLeafP2K2_pack_sound jpLeaf jOld jNew hOld4 hNew4 hUnpack (by omega) hcur
  have hEq1 : advLeafP2K2 (bNT11 jpLeaf 0 1024) (samplePackLeafK2Pure (2 * m + 1)) dw mid =
      advLeafP2K2 (bNT11 jpLeaf 0 1024) (samplePackLeafK2Pure (2 * m + 1))
      (dwPack13 (2 * m + 1)) mid :=
      congrArg (fun w => advLeafP2K2 (bNT11 jpLeaf 0 1024)
      (samplePackLeafK2Pure (2 * m + 1)) w mid) hdw1
  rw [hEq1]; exact advLeafP2K2_pack_sound jpLeaf jOld jNew hOld4 hNew4 hUnpack hm h0
theorem advSub6P2K2_pack_gen_sound (jpLeaf : Nat → Nat) (jOld jNew : Bool → Nat → Nat)
    (hOld4 : ∀ r i, jOld r i < 4) (hNew4 : ∀ r i, jNew r i < 4)
    (hUnpack : ∀ i, i < 8192 →
      jpLeaf (d11At13 i) % 4 = jOld false i ∧ (jpLeaf (d11At13 i) / 4) % 4 = jOld true i ∧
      (jpLeaf (d11At13 i) / 16) % 4 = jNew false i ∧ jpLeaf (d11At13 i) / 64 = jNew true i) :
    ∀ (d b11 : Nat) {cur : ST4P2},
      b11 + 2 ^ d ≤ 2048 → IsST4P2PackTransK2 jOld jNew (4 * b11) cur →
      IsST4P2PackTransK2 jOld jNew (4 * (b11 + 2 ^ d))
        (advSub6P2K2 (bNT11 jpLeaf 0 1024)
          (buildNT63 samplePackLeafK2Pure (d + 2) (4 * b11) (2 ^ (d + 1)))
          (buildNT63 (fun idx11 => pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)))
            d b11 (2 ^ d / 2))
          cur)
  | 0, b11, cur, hb, hcur => by
      have hw {k m : Nat} (hk : k < 4 := by omega) (hm : 4 * b11 + k = m := by omega) :=
        (pack3WgtFK2_eq_dwPack13 (by omega : b11 < 2048) ⟨k, hk⟩).trans (congrArg dwPack13 hm)
      rw [show (2 ^ (0 + 1) : Nat) = 2 from rfl, show (2 ^ 0 / 2 : Nat) = 0 from rfl,
        buildNT63_succ samplePackLeafK2Pure 1 (4 * b11) 2, show (2 / 2 : Nat) = 1 from rfl,
        buildNT63_zero]
      dsimp only [advSub6P2K2]
      rw [sST4P2_eq]
      have hL := advPairP2K2_pack_sound jpLeaf jOld jNew hOld4 hNew4 hUnpack (m := 2 * b11)
        (by omega) (hw (k := 0)) (hw (k := 1)) (by rwa [show 2 * (2 * b11) = 4 * b11 by omega])
      rw [show 2 * (2 * b11) = 4 * b11 by omega] at hL
      have hR := advPairP2K2_pack_sound jpLeaf jOld jNew hOld4 hNew4 hUnpack (m := 2 * b11 + 1)
        (by omega) (hw (k := 2)) (hw (k := 3))
        (by rwa [show 2 * (2 * b11 + 1) = 4 * b11 + 2 by omega])
      rw [show 2 * (2 * b11 + 1) = 4 * b11 + 2 by omega] at hR
      rwa [show 4 * (b11 + 2 ^ 0) = 4 * b11 + 2 + 2 by omega]
  | d + 1, b11, cur, hb, hcur => by
      have hp1 : 2 ^ (d + 2) / 2 = 2 ^ (d + 1) := by
        rw [Nat.pow_succ]; have := Nat.two_pow_pos (d + 1); omega
      have hp0 : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
      rw [hp0, buildNT63_succ samplePackLeafK2Pure (d + 2), hp1, buildNT63_succ (fun idx11 =>
          pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32))) d]
      dsimp only [advSub6P2K2]; rw [sST4P2_eq]
      have hL := advSub6P2K2_pack_gen_sound jpLeaf jOld jNew hOld4 hNew4 hUnpack
        d b11 (by rw [Nat.pow_succ] at hb; omega) hcur
      have h4b : 4 * b11 + 2 ^ (d + 2) = 4 * (b11 + 2 ^ d) := by
        rw [show 2 ^ (d + 2) = 4 * 2 ^ d by rw [Nat.pow_add]; ring]; ring
      rw [h4b]
      have hR := advSub6P2K2_pack_gen_sound jpLeaf jOld jNew hOld4 hNew4 hUnpack
        d (b11 + 2 ^ d) (by rw [Nat.pow_succ] at hb; omega) hL
      have heq : b11 + 2 ^ (d + 1) = b11 + 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; ring
      rwa [heq]

theorem advSub6P2K2_pack_sound (a d b11 : Nat) {cur : ST4P2} (hb : b11 + 2 ^ d ≤ 2048)
    (hcur : IsST4P2PackOfK2 a (4 * b11) cur) : IsST4P2PackOfK2 a (4 * (b11 + 2 ^ d))
    (advSub6P2K2 (bNT11 (jPack4Leaf a) 0 1024) (buildNT63 samplePackLeafK2Pure (d + 2) (4 * b11)
    (2 ^ (d + 1))) (buildNT63 (fun idx11 => pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32)
    (Nat.div idx11 32))) d b11 (2 ^ d / 2)) cur) := by
  have hcurT : IsST4P2PackTransK2 (fun r i => j18At13 a r false i)
      (fun r i => j18At13 a r true i) (4 * b11) cur :=
    hcur.congr (fun j _ idx _ => by rw [sweepBktPackK2_eq_trans])
               (fun j _ idx _ => by rw [sweepBktPackK2_eq_trans])
  have hRes :=
      advSub6P2K2_pack_gen_sound (jPack4Leaf a) (fun r i => j18At13 a r false i)
      (fun r i => j18At13 a r true i) (fun r i => j18At13_lt_four a r false i)
      (fun r i => j18At13_lt_four a r true i) (fun i _ => jPack4Leaf_unpack_at13 a i) d b11 hb hcurT
  exact hRes.congr (fun j _ idx _ => by rw [← sweepBktPackK2_eq_trans])
                   (fun j _ idx _ => by rw [← sweepBktPackK2_eq_trans])

theorem even_end_isST4P2PackOfK2_succ (b : Nat) {mid : ST4P2}
    (hmid : IsST4P2PackOfK2 (2 * b) 8192 mid) : IsST4P2PackOfK2 (2 * b + 1) 0 mid := by
  have ha0 : (2 * b) % 2 = 0 := by omega
  refine hmid.congr (fun j _ idx _ => ?_) (fun j _ idx _ => ?_) <;> {
    unfold sweepBktPackK2
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi8192 : i < 8192 :=
        (Finset.mem_range.mp hi).trans_eq nSamples13_eq; rw [decide_eq_true hi8192,
        decide_eq_false (Nat.not_lt_zero i), j18At13_even_true_eq_odd_false ha0 _ i]
  }

attribute [local irreducible]
  initTreeP2FastK2 initTreeT3K2 initLeafT3K2 advSub6P2K2 advLeafP2K2
  transBktPackK2 initBktPackK2 sweepBktPackK2

def selCh3K2 {α : Type} (ch : ChK2) (x0 x1 x2 : α) : α :=
  match ch with
  | .ee => x0
  | .nn => x1
  | .en => x2

def chFn3K2 (ch : ChK2) (f0 f1 f2 : Nat → Nat) (x : Nat) : Nat := selCh3K2 ch (f0 x) (f1 x) (f2 x)
theorem chFn3K2_app (ch : ChK2) (F : ChK2 → Nat → Nat) (x : Nat) : chFn3K2 ch (F .ee) (F .nn)
    (F .en) x = F ch x := by
  cases ch <;> rfl

def projUnpkSTK2 (ch : ChK2) : SumTree → SumTree
  | .leaf v => .leaf (unpk3K2 ch v)
  | .node _ l r =>
      let pl := projUnpkSTK2 ch l; let pr := projUnpkSTK2 ch r
      .node (stVal pl + stVal pr) pl pr

theorem stVal_projUnpkSTK2_node (ch : ChK2) (s : Nat) (l r : SumTree) :
    stVal (projUnpkSTK2 ch (.node s l r)) =
      stVal (projUnpkSTK2 ch l) + stVal (projUnpkSTK2 ch r) := rfl

def projUnpkST4K2 (ch : ChK2) : ST4 → ST4
  | .mk _ a b c d =>
      .mk 0 (projUnpkSTK2 ch a) (projUnpkSTK2 ch b) (projUnpkSTK2 ch c) (projUnpkSTK2 ch d)

theorem projUnpkSTK2_spec {f0 f1 f2 : Nat → Nat} {d base : Nat} {st : SumTree}
    (hst : IsTreeOf (fun i => pack3NatK2 (f0 i) (f1 i) (f2 i)) d base st)
    (h0 : (∑ i ∈ Finset.range (2 ^ d), f0 (base + i)) < 1048576)
    (h1 : (∑ i ∈ Finset.range (2 ^ d), f1 (base + i)) < 1048576) :
    (∀ ch, IsTreeOf (chFn3K2 ch f0 f1 f2) d base (projUnpkSTK2 ch st)) ∧
    (∀ ch, stVal (projUnpkSTK2 ch st) = ∑ i ∈ Finset.range (2 ^ d), chFn3K2 ch f0 f1 f2 (base +
    i)) ∧ stVal st = pack3NatK2 (stVal (projUnpkSTK2 .ee st)) (stVal (projUnpkSTK2 .nn st))
    (stVal (projUnpkSTK2 .en st)) ∧ (∀ h M acc0 acc1 acc2,
    sufST h st M (pack3NatK2 acc0 acc1 acc2) = pack3NatK2 (sufST h (projUnpkSTK2 .ee st) M acc0)
    (sufST h (projUnpkSTK2 .nn st) M acc1) (sufST h (projUnpkSTK2 .en st) M acc2)) := by
  induction hst with
  | leaf base =>
      simp only [pow_zero, Finset.range_one, Finset.sum_singleton, add_zero] at h0 h1 ⊢
      have hu : ∀ ch, unpk3K2 ch (pack3NatK2 (f0 base) (f1 base) (f2 base)) =
          chFn3K2 ch f0 f1 f2 base := by
        intro ch; rw [unpk3K2_pack3NatK2 ch (f2 base) h0 h1]
        cases ch <;> rfl
      refine ⟨fun ch => ?_, fun ch => ?_, ?_, fun h M acc0 acc1 acc2 => ?_⟩
      · dsimp only [projUnpkSTK2]; rw [hu ch]; exact .leaf base
      · dsimp only [projUnpkSTK2, stVal]; exact hu ch
      · dsimp only [projUnpkSTK2, stVal]; rw [hu .ee, hu .nn, hu .en]; rfl
      · dsimp only [projUnpkSTK2, sufST]; simp only [nat_add_def, hu .ee, hu .nn, hu .en];
        exact pack3NatK2_add acc0 acc1 acc2 (f0 base) (f1 base) (f2 base)
  | @node d base s l r hs hl hr ihl ihr =>
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := (Nat.pow_succ 2 d).trans (Nat.mul_two _)
      have hSplit {f : Nat → Nat}
          (hf : (∑ i ∈ Finset.range (2 ^ (d + 1)), f (base + i)) < 1048576) :
          (∑ i ∈ Finset.range (2 ^ d), f (base + i)) < 1048576 ∧
          (∑ i ∈ Finset.range (2 ^ d), f (base + 2 ^ d + i)) < 1048576 := by
        simp only [hpow, Finset.sum_range_add, ← Nat.add_assoc] at hf; exact ⟨by omega, by omega⟩
      obtain ⟨tl, vcl, vpl, sufl⟩ := ihl (hSplit h0).1 (hSplit h1).1
      obtain ⟨tr, vcr, vpr, sufr⟩ := ihr (hSplit h0).2 (hSplit h1).2
      refine ⟨fun ch => .node rfl (tl ch) (tr ch), fun ch => ?_,
        by
          simp only [stVal_projUnpkSTK2_node]
          rw [show stVal (.node s l r) = s from rfl, hs, vpl, vpr, pack3NatK2_add],
        fun h M acc0 acc1 acc2 => ?_⟩
      · simp only [stVal_projUnpkSTK2_node, vcl ch, vcr ch, hpow, Finset.sum_range_add, add_assoc]
      · dsimp only [projUnpkSTK2]; unfold sufST
        simp only [nat_add_def, nat_div_def, nat_sub_def, stVal63_eq]
        cases Nat.ble (M + 1) h
        · dsimp only [Bool.casesOn]; exact sufr (h / 2) (M - h) acc0 acc1 acc2
        · dsimp only [Bool.casesOn]; rw [vpr, pack3NatK2_add];
          exact sufl (h / 2) M (acc0 + stVal (projUnpkSTK2 .ee r))
              (acc1 + stVal (projUnpkSTK2 .nn r)) (acc2 + stVal (projUnpkSTK2 .en r))
theorem projUnpkSTK2_unpk {f0 f1 f2 : Nat → Nat} {d base : Nat} {st : SumTree}
    (hst : IsTreeOf (fun i => pack3NatK2 (f0 i) (f1 i) (f2 i)) d base st)
    (h0 : (∑ i ∈ Finset.range (2 ^ d), f0 (base + i)) < 1048576)
    (h1 : (∑ i ∈ Finset.range (2 ^ d), f1 (base + i)) < 1048576)
    (ch : ChK2) : IsTreeOf (chFn3K2 ch f0 f1 f2) d base (projUnpkSTK2 ch st) ∧
    unpk3K2 ch (stVal st) = stVal (projUnpkSTK2 ch st) ∧ (∀ M, unpk3K2 ch (sufST 128 st M 0) =
    sufST 128 (projUnpkSTK2 ch st) M 0) := by
  obtain ⟨ht, hvc, hvp, hsuf⟩ := projUnpkSTK2_spec hst h0 h1
  have hv0 : stVal (projUnpkSTK2 .ee st) < 1048576 := by
    rw [hvc .ee]; simpa only [chFn3K2, selCh3K2] using h0
  have hv1 : stVal (projUnpkSTK2 .nn st) < 1048576 := by
    rw [hvc .nn]; simpa only [chFn3K2, selCh3K2] using h1
  refine ⟨ht ch, ?_, fun M => ?_⟩
  · rw [hvp, unpk3K2_pack3NatK2 ch _ hv0 hv1]; cases ch <;> rfl
  · have hz := hsuf 128 M 0 0 0
    rw [pack3NatK2_zero] at hz; rw [hz]
    have hs0 : sufST 128 (projUnpkSTK2 .ee st) M 0 < 1048576 := by
      have hle := sufST_le_add_stVal (ht .ee).isValid 128 M 0; omega
    have hs1 : sufST 128 (projUnpkSTK2 .nn st) M 0 < 1048576 := by
      have hle := sufST_le_add_stVal (ht .nn).isValid 128 M 0; omega
    rw [unpk3K2_pack3NatK2 ch _ hs0 hs1]; cases ch <;> rfl

theorem sum_sweepBktK2_le_sum_dw (ch : ChK2) (a : Nat) (r01 : Bool)
    (p j : Nat) : (∑ idx ∈ Finset.range (2 ^ 8), sweepBktK2 ch a r01 p j (0 + idx)) ≤
    ∑ i ∈ Finset.range nSamples13, dwAt13 ch i := by
  simp only [zero_add, sweepBktK2]; rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  have hdf8 : df8At13 i < 2 ^ 8 := df8At13_lt_256 i;
  have hmem : df8At13 i ∈ Finset.range (2 ^ 8) :=
      Finset.mem_range.mpr hdf8; rw [← Finset.add_sum_erase (Finset.range (2 ^ 8)) _ hmem]
  have h0 : (∑ x ∈ (Finset.range (2 ^ 8)).erase (df8At13 i),
      if j18At13 a r01 (decide (i < p)) i = j ∧ df8At13 i = x then dwAt13 ch i else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      have hne : x ≠ df8At13 i :=
          (Finset.mem_erase.mp hx).1; simp only [hne.symm, and_false, ↓reduceIte]
  rw [h0, add_zero]
  split_ifs <;> omega

theorem sum_sweepBktK2_ee_lt (a : Nat) (r01 : Bool) (p j : Nat) : (∑ idx ∈ Finset.range (2 ^ 8),
    sweepBktK2 .ee a r01 p j (0 + idx)) < 1048576 := by
  have hle := sum_sweepBktK2_le_sum_dw .ee a r01 p j
  have hdw : (∑ i ∈ Finset.range nSamples13, dwAt13 .ee i) ≤ ∑ _i ∈ Finset.range nSamples13, 82 :=
      Finset.sum_le_sum fun i _ => dwAt13_ee_le i
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hdw; rw [nSamples13_eq] at hle hdw; omega
theorem sum_sweepBktK2_nn_lt (a : Nat) (r01 : Bool) (p j : Nat) : (∑ idx ∈ Finset.range (2 ^ 8),
    sweepBktK2 .nn a r01 p j (0 + idx)) < 1048576 := by
  have hle := sum_sweepBktK2_le_sum_dw .nn a r01 p j
  have hdw : (∑ i ∈ Finset.range nSamples13, dwAt13 .nn i) ≤ ∑ _i ∈ Finset.range nSamples13, 82 :=
      Finset.sum_le_sum fun i _ => dwAt13_nn_le i
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hdw; rw [nSamples13_eq] at hle hdw; omega
theorem evalLaneVQMPackK2_eq_proj {ch : ChK2} {st : SumTree}
    (hv : unpk3K2 ch (stVal st) = stVal (projUnpkSTK2 ch st))
    (hsuf : ∀ M, unpk3K2 ch (sufST 128 st M 0) = sufST 128 (projUnpkSTK2 ch st) M 0)
    (z : Nat) : evalLaneVQMPackK2 ch (unpk3K2 ch (stVal63 st)) st (Nat.div z 256)
    (Nat.sub 256 (Nat.mod z 256)) = evalLane256F (projUnpkSTK2 ch st) z := by
  unfold evalLaneVQMPackK2 evalLane256F gSu256F;
  simp only [nat_div_def, nat_sub_def, nat_mod_def, nat_add_def, nat_mul_def, stVal63_eq,
      sufST128F_eq, hv, hsuf]
  set M := 256 - z % 256
  rw [show Nat.beq M 0 = false from Bool.eq_false_iff.mpr fun hb => by
    have := Nat.beq_eq.mp hb; omega]
  by_cases h256 : M = 256
  · rw [h256]; rfl
  · rw [show Nat.beq M 256 = false from Bool.eq_false_iff.mpr (mt Nat.beq_eq.mp h256),
      show Nat.ble 256 M = false from Bool.eq_false_iff.mpr fun hb =>
        h256 (by have := Nat.ble_eq.mp hb; omega)]

theorem evalLane256PackK2_eq_proj {ch : ChK2} {st : SumTree}
    (hv : unpk3K2 ch (stVal st) = stVal (projUnpkSTK2 ch st))
    (hsuf : ∀ M, unpk3K2 ch (sufST 128 st M 0) = sufST 128 (projUnpkSTK2 ch st) M 0)
    (z : Nat) : evalLane256PackK2 ch st z = evalLane256F (projUnpkSTK2 ch st) z := by
  unfold evalLane256PackK2 evalLane256F gSu256PackK2 gSu256F;
  simp only [stVal63_eq, sufST128F_eq, hv, hsuf]
theorem sweepBktPackK2_lane_unpk (ch : ChK2) {a : Nat} {r01 : Bool} {p j : Nat} {st : SumTree}
    (hst : IsTreeOf (sweepBktPackK2 a r01 p j) 8 0 st) :
    IsTreeOf (sweepBktK2 ch a r01 p j) 8 0 (projUnpkSTK2 ch st) ∧
    (∀ z, evalLaneVQMPackK2 ch (unpk3K2 ch (stVal63 st)) st (Nat.div z 256)
    (Nat.sub 256 (Nat.mod z 256)) = evalLane256F (projUnpkSTK2 ch st) z) ∧
    (∀ z, evalLane256PackK2 ch st z = evalLane256F (projUnpkSTK2 ch st) z) := by
  have hstP := hst.congr (g := fun idx => pack3NatK2 (sweepBktK2 .ee a r01 p j idx)
                 (sweepBktK2 .nn a r01 p j idx)
                 (sweepBktK2 .en a r01 p j idx))
    (fun idx _ => sweepBktPackK2_eq_pack3 a r01 p j (0 + idx))
  obtain ⟨ht, hv, hsuf⟩ :=
      projUnpkSTK2_unpk hstP (sum_sweepBktK2_ee_lt a r01 p j) (sum_sweepBktK2_nn_lt a r01 p j) ch
  refine ⟨ht.congr (g := sweepBktK2 ch a r01 p j)
      (fun idx _ => chFn3K2_app ch (fun c => sweepBktK2 c a r01 p j) (0 + idx)),
    evalLaneVQMPackK2_eq_proj hv hsuf, evalLane256PackK2_eq_proj hv hsuf⟩

theorem projUnpkST4K2_spec (ch : ChK2) {a : Nat} {r01 : Bool} {p : Nat} {st4 : ST4}
    (hst : IsST4Of8 (sweepBktPackK2 a r01 p) st4) : IsST4Of8 (sweepBktK2 ch a r01 p)
    (projUnpkST4K2 ch st4) ∧ (∀ z0 z1 z2 z3, evalST4PackK2 ch st4 z0 z1 z2 z3 =
    evalST4FK2 (projUnpkST4K2 ch st4) z0 z1 z2 z3) := by
  rcases st4 with ⟨_, ta, tb, tc, td⟩
  rcases hst with ⟨ha, hb, hc, hd⟩
  obtain ⟨pa, _, ea⟩ := sweepBktPackK2_lane_unpk ch ha; obtain ⟨pb, _, eb⟩ :=
      sweepBktPackK2_lane_unpk ch hb; obtain ⟨pc, _, ec⟩ :=
      sweepBktPackK2_lane_unpk ch hc; obtain ⟨pd, _, ed⟩ := sweepBktPackK2_lane_unpk ch hd
  refine ⟨⟨pa, pb, pc, pd⟩, fun z0 z1 z2 z3 => ?_⟩
  unfold evalST4PackK2 evalST4FK2 projUnpkST4K2; dsimp only; simp only [fN63_eq, ea, eb, ec, ed]
end QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs

namespace QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs
open Real
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (is3DBoxDistSq_le)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (clbGam6)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (x13OfW11U01 popBernJK2
    popBernJK2_lt_four ySampleK2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (word512DualLegLo6)
attribute [local irreducible]
  spNTFastK2 bNT9 bNT11 buildSamplePackK2NT buildWgtPackK2NT
  initTreeP2FastK2 advSub6P2K2 sweepBktPackK2

def equiv128Of32x2x2 : Fin 32 × (Fin 2 × Fin 2) ≃ Fin 128 where
  toFun p := ⟨4 * p.1.val + (p.2.1.val + 2 * p.2.2.val), by omega⟩
  invFun r := (⟨r.val / 4, by omega⟩, (⟨(r.val % 4) % 2, by omega⟩, ⟨(r.val % 4) / 2, by omega⟩))
  left_inv p := Prod.ext (Fin.ext (by dsimp only; omega))
    (Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega)))
  right_inv r := Fin.ext (by dsimp only; omega)

def equivN13Of64x128 : Fin 64 × Fin 128 ≃ Fin nSamples13 where
  toFun p :=
      ⟨128 * p.1.val + p.2.val,
      (by omega : 128 * p.1.val + p.2.val < 8192).trans_eq nSamples13_eq.symm⟩
  invFun i :=
      (⟨i.val / 128, by have := i.isLt.trans_eq nSamples13_eq; omega⟩, ⟨i.val % 128, by omega⟩)
  left_inv p := Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega))
  right_inv i := Fin.ext (by dsimp only; omega)

theorem sumCarryST256_sweepBktK2 (ch : ChK2) (a : Nat) (r01 : Bool) (r6 j z : Nat) {st : SumTree}
    (h : IsTreeOf (sweepBktK2 ch a r01 (128 * r6) j) 8 0 st) : sumCarryST256 128 0 st z =
    ∑ i ∈ Finset.range nSamples13, if j18At13 a r01 (decide (i < 128 * r6)) i = j then dwAt13 ch i *
    ((z + df8At13 i) / 256) else 0 := by
  have hc := IsTreeOf.sumCarry256 h z
  rw [show (2 ^ 8 / 2 : Nat) = 128 by norm_num,
      show (2 ^ 8 : Nat) = nLanes8 by rw [nLanes8_eq]; norm_num] at hc
  rw [hc]; simp only [zero_add, sweepBktK2, Finset.sum_mul]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdf8L : df8At13 i < nLanes8 := by rw [nLanes8_eq]; exact df8At13_lt_256 i
  have hdf8 : df8At13 i ∈ Finset.range nLanes8 :=
      Finset.mem_range.mpr hdf8L; rw [← Finset.add_sum_erase (Finset.range nLanes8) _ hdf8]
  have h0 : (∑ x ∈ (Finset.range nLanes8).erase (df8At13 i),
      (if j18At13 a r01 (decide (i < 128 * r6)) i = j ∧ df8At13 i = x then dwAt13 ch i else 0) *
        ((z + x) / 256)) = 0 := Finset.sum_eq_zero fun x hx => by
      have hne : x ≠ df8At13 i :=
          (Finset.mem_erase.mp hx).1; simp only [hne.symm, and_false, ↓reduceIte, zero_mul]
  rw [h0, add_zero]
  by_cases hj : j18At13 a r01 (decide (i < 128 * r6)) i = j <;>
    simp only [hj, and_self, false_and, ↓reduceIte, zero_mul]

attribute [local irreducible] sweepBktK2

theorem chFn_ySampleK2_lo6_eq_zKnotLo6 (cb : ChW11) (isNN : Bool) (d2 : ℕ) (w : Fin 2048)
    (o9 : Fin 512) :
    let p := evenOctIdxT10K isNN d2
    chFn cb (ySampleK2 word512DualLegLo6 isNN d2 w o9) =
      zKnotLo6 cb p.2.2 (idx7OfParts p) (popBernJK2 (t11OfParts p) w o9) := by
  dsimp only [ySampleK2, zKnotLo6]; rw [chFn_eq_chFnFast, Nat.shiftRight_eq_div_pow]
theorem zKnotLo6_div256_eq_qKnotW11 (cb : ChW11) (k i7 df8 j : ℕ)
    (hj : j < 4) : (zKnotLo6 cb k i7 j + df8) / 256 = qKnotW11 ((zKnotLo6 cb k i7 0 + df8) / 256)
    ((zKnotLo6 cb k i7 1 + df8) / 256) ((zKnotLo6 cb k i7 2 + df8) / 256)
    ((zKnotLo6 cb k i7 3 + df8) / 256) j := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem evalST4FK2_sweepBktK2_eq_sum (ch : ChK2) {a r6 : Nat} (ha : a < 32) (hr6 : r6 < 64)
    {st4 : ST4} (hst : IsST4Of8 (sweepBktK2 ch a (r01OfR6 r6) (128 * r6)) st4) (z0 z1 z2 z3 : Nat) :
    evalST4FK2 st4 z0 z1 z2 z3 =
      ∑ w : Fin 2048, chWgtK2 ch w.val *
        ∑ u0 : Fin 2, ∑ u1 : Fin 2,
          let x13 := x13OfW11U01 w u0 u1; let df8 := (df8Of13 x13).val
          qKnotW11 ((z0 + df8) / 256) ((z1 + df8) / 256) ((z2 + df8) / 256) ((z3 + df8) / 256)
            (popBernJK2 (64 * a + r6) w (o9Of13 x13)) := by
  rw [evalST4FK2_eq_sumCarryST4K2 hst.isValid]
  rcases st4 with ⟨s, ta, tb, tc, td⟩; rcases hst with ⟨haT, hbT, hcT, hdT⟩
  dsimp only [sumCarryST4K2]; set r01 := r01OfR6 r6
  rw [sumCarryST256_sweepBktK2 ch a r01 r6 0 z0 haT, sumCarryST256_sweepBktK2 ch a r01 r6 1 z1 hbT,
      sumCarryST256_sweepBktK2 ch a r01 r6 2 z2 hcT,
      sumCarryST256_sweepBktK2 ch a r01 r6 3 z3 hdT]; simp only [← Finset.sum_add_distrib]
  have hCollapse : (∑ x ∈ Finset.range nSamples13, ((if j18At13 a r01 (decide (x < 128 * r6)) x =
      0 then dwAt13 ch x * ((z0 + df8At13 x) / 256) else 0) +
      (if j18At13 a r01 (decide (x < 128 * r6)) x = 1 then dwAt13 ch x * ((z1 + df8At13 x) /
      256) else 0) + (if j18At13 a r01 (decide (x < 128 * r6)) x = 2 then dwAt13 ch x *
      ((z2 + df8At13 x) / 256) else 0) + (if j18At13 a r01 (decide (x < 128 * r6)) x =
      3 then dwAt13 ch x * ((z3 + df8At13 x) / 256) else 0))) = ∑ i : Fin nSamples13,
      dwAt13 ch i.val * qKnotW11 ((z0 + df8At13 i.val) / 256) ((z1 + df8At13 i.val) / 256)
      ((z2 + df8At13 i.val) / 256) ((z3 + df8At13 i.val) / 256)
      (j18At13 a r01 (decide (i.val < 128 * r6)) i.val) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hj := j18At13_lt_four a r01 (decide (i.val < 128 * r6)) i.val
    rcases (by omega : j18At13 a r01 (decide (i.val < 128 * r6)) i.val = 0 ∨
        j18At13 a r01 (decide (i.val < 128 * r6)) i.val = 1 ∨
        j18At13 a r01 (decide (i.val < 128 * r6)) i.val = 2 ∨
        j18At13 a r01 (decide (i.val < 128 * r6)) i.val = 3) with h | h | h | h <;>
            simp [h, qKnotW11]
  rw [hCollapse, ← equivN13Of64x128.sum_comp, Fintype.sum_prod_type]
  symm
  rw [← equivW11CLB.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g6 _ => ?_
  rw [← equiv128Of32x2x2.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u5 _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u0 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u1 _ => ?_
  set iVal := 128 * g6.val + (4 * u5.val + (u0.val + 2 * u1.val))
  have hiEq : (equivN13Of64x128 (g6, equiv128Of32x2x2 (u5, (u0, u1)))).val = iVal :=
      rfl; simp only [hiEq]
  have hiDiv : iVal / 128 = g6.val := by dsimp [iVal]; omega
  have hiMod4 : (iVal % 128) / 4 = u5.val := by dsimp [iVal]; omega
  have hiMod01 : (iVal % 128) % 4 = u0.val + 2 * u1.val := by dsimp [iVal]; omega
  set w := equivW11CLB (u5, g6)
  have hg6Eq : clbGam6 w.val = g6.val :=
    congrArg (fun x => x.2.val) (equivW11CLB.left_inv (u5, g6))
  have hwEq : wAt13 iVal = w.val := by rw [wAt13, hiMod4, hiDiv]; rfl
  set x13 := x13OfW11U01 w u0 u1
  have hxEq : x13At13 iVal = x13 := by
    dsimp only [x13, x13At13, x13OfW11U01]
    rw [hwEq, hiMod01]; ring
  unfold dwAt13 df8At13 j18At13 d11At13 o9At13
  rw [hwEq, hxEq, show decide (iVal < 128 * r6) = decide (clbGam6 w.val < r6) by
      rw [hg6Eq, decide_eq_decide]; dsimp only [iVal]; omega,
    hiDiv.trans hg6Eq.symm, j18AtARB_eq_popBernJK2 ha hr6 w (o9Of13 x13)]

theorem evalST4FK2_sweepBktK2_eq_expFnK2 (ch : ChK2) {d2 : ℕ} (hd2 : d2 < 262144) {st4 : ST4}
    (hst : IsST4Of8 (sweepBktK2 ch
      (t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2) / 64)
      (r01OfR6 (t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2) % 64))
      (128 * (t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2) % 64))) st4) :
    let cb := chFnChK2 ch; let p := evenOctIdxT10K (chIsNNK2 ch) d2
    64 * (evalST4FK2 st4
      (zKnotLo6 cb p.2.2 (idx7OfParts p) 0) (zKnotLo6 cb p.2.2 (idx7OfParts p) 1)
      (zKnotLo6 cb p.2.2 (idx7OfParts p) 2) (zKnotLo6 cb p.2.2 (idx7OfParts p) 3) : ℝ) =
    (chTotWK2 ch : ℝ) *
      expFnK2 (chWgtK2 ch) (chTotWK2 ch) (chFn30K2 ch) word512DualLegLo6 (chIsNNK2 ch) d2 := by
  dsimp only
  set cb := chFnChK2 ch
  set p := evenOctIdxT10K (chIsNNK2 ch) d2
  have ht11 : t11OfParts p < 2048 := (parts_popBern_bounds (chIsNNK2 ch) hd2).2.1
  set r6 := t11OfParts p % 64; set a := t11OfParts p / 64
  have hr6 : r6 < 64 := Nat.mod_lt _ (by omega)
  have ha : a < 32 := by dsimp only [a]; omega
  have ht11_eq : 64 * a + r6 = t11OfParts p := Nat.div_add_mod (t11OfParts p) 64
  have hNat : evalST4FK2 st4
      (zKnotLo6 cb p.2.2 (idx7OfParts p) 0) (zKnotLo6 cb p.2.2 (idx7OfParts p) 1)
      (zKnotLo6 cb p.2.2 (idx7OfParts p) 2) (zKnotLo6 cb p.2.2 (idx7OfParts p) 3) =
      ∑ w : Fin 2048, chWgtK2 ch w.val * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
          let x13 := x13OfW11U01 w u0 u1
          (chFn30K2 ch (ySampleK2 word512DualLegLo6 (chIsNNK2 ch) d2 w (o9Of13 x13)) +
            (df8Of13 x13).val) / 256 := by
    rw [evalST4FK2_sweepBktK2_eq_sum ch ha hr6 hst]
    refine Finset.sum_congr rfl fun w _ => congrArg (chWgtK2 ch w.val * ·)
      (Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ?_)
    dsimp only;
    rw [ht11_eq, ← chFn_chFnChK2_eq ch, chFn_ySampleK2_lo6_eq_zKnotLo6 cb (chIsNNK2 ch) d2]
    exact (zKnotLo6_div256_eq_qKnotW11 cb p.2.2 (idx7OfParts p) _ _ (popBernJK2_lt_four (t11OfParts
        p) w (o9Of13 (x13OfW11U01 w u0 u1)))).symm
  rw [congrArg (Nat.cast (R := ℝ)) hNat]; unfold expFnK2
  have htot : (chTotWK2 ch : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (chTotWK2_pos ch))
  push_cast; field_simp [htot]

theorem scanZLLPackK2_sound (ch : ChK2) (cb : ChW11) (k step2 wBase s : Nat) (a b c d : SumTree)
    (vqa : ∀ z, evalLaneVQMPackK2 ch (unpk3K2 ch (stVal63 a)) a (Nat.div z 256)
        (Nat.sub 256 (Nat.mod z 256)) =
      evalLane256F (projUnpkSTK2 ch a) z)
    (vqb : ∀ z, evalLaneVQMPackK2 ch (unpk3K2 ch (stVal63 b)) b (Nat.div z 256)
        (Nat.sub 256 (Nat.mod z 256)) =
      evalLane256F (projUnpkSTK2 ch b) z)
    (vqc : ∀ z, evalLaneVQMPackK2 ch (unpk3K2 ch (stVal63 c)) c (Nat.div z 256)
        (Nat.sub 256 (Nat.mod z 256)) =
      evalLane256F (projUnpkSTK2 ch c) z)
    (vqd : ∀ z, evalLaneVQMPackK2 ch (unpk3K2 ch (stVal63 d)) d (Nat.div z 256)
        (Nat.sub 256 (Nat.mod z 256)) =
      evalLane256F (projUnpkSTK2 ch d) z)
    (qt g hi lo s0Sq : Nat) :
    ∀ {n iBase : Nat}, iBase + n ≤ 128 →
      scanZLLPackK2 ch
        (unpk3K2 ch (stVal63 a)) a (unpk3K2 ch (stVal63 b)) b
        (unpk3K2 ch (stVal63 c)) c (unpk3K2 ch (stVal63 d)) d
        qt g hi lo s0Sq
        (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) (2 ^ k) step2 wBase n iBase) = true →
      ∀ i7, iBase ≤ i7 → i7 < iBase + n →
        let m := (wBase + 2048 * i7) / step2 + qt
        ¬(m % 8 = 7) → ¬(m % 32 = 28) → checkNum63
          (evalST4FK2 (projUnpkST4K2 ch (.mk s a b c d)) (zKnotLo6 cb k i7 0)
            (zKnotLo6 cb k i7 1) (zKnotLo6 cb k i7 2) (zKnotLo6 cb k i7 3)) m g hi lo s0Sq = true
  | 0, _, _, _, _, hi1, hi2 => by omega
  | n + 1, iBase, hle, hscan, i7, hi1, hi2 => by
      dsimp only at hscan ⊢; unfold buildZLLK2 at hscan
      simp only [sZLL_eq, fN63_eq, nat_add_def, nat_mul_def] at hscan
      have hz (j : Nat) (hj : j < 4) := zKnotFast_at_lo6NT cb k iBase j (by omega) hj
      have hz0 := hz 0 (by omega)
      simp only [add_zero] at hz0
      rw [hz0, hz 1 (by omega), hz 2 (by omega), hz 3 (by omega)] at hscan
      unfold scanZLLPackK2 at hscan; rw [andB63_eq_true] at hscan
      rcases hscan with ⟨hHead, hTail⟩
      by_cases heq : i7 = iBase
      · subst heq; intro hm7 hm28; unfold evalCheckPtPackK2 at hHead
        simp only [fN63_eq, vqa, vqb, vqc, vqd] at hHead;
        simp only [nat_add_def, nat_div_def, nat_mod_def] at hHead
        rw [show Nat.beq (((wBase + 2048 * i7) / step2 + qt) % 8) 7 = false from
              Bool.eq_false_iff.mpr fun ht => hm7 (Nat.beq_eq.mp ht)] at hHead
        dsimp only [Bool.casesOn] at hHead
        rw [show Nat.beq (((wBase + 2048 * i7) / step2 + qt) % 32) 28 = false from
              Bool.eq_false_iff.mpr fun ht => hm28 (Nat.beq_eq.mp ht)] at hHead
        dsimp only [Bool.casesOn] at hHead
        have hE : (evalLane256F (projUnpkSTK2 ch a) (zKnotLo6 cb k i7 0) +
            evalLane256F (projUnpkSTK2 ch b) (zKnotLo6 cb k i7 1)) +
            (evalLane256F (projUnpkSTK2 ch c) (zKnotLo6 cb k i7 2) +
            evalLane256F (projUnpkSTK2 ch d) (zKnotLo6 cb k i7 3)) =
            evalST4FK2 (projUnpkST4K2 ch (.mk s a b c d)) (zKnotLo6 cb k i7 0) (zKnotLo6 cb k i7 1)
            (zKnotLo6 cb k i7 2) (zKnotLo6 cb k i7 3) := by
          simp only [evalST4FK2, projUnpkST4K2, fN63_eq, nat_add_def, Nat.add_assoc]
        rwa [hE] at hHead
      · exact scanZLLPackK2_sound ch cb k step2 wBase s a b c d vqa vqb vqc vqd qt g hi lo s0Sq
          (n := n) (iBase := iBase + 1) (by omega) hTail i7 (by omega) (by omega)

attribute [local irreducible] buildZLLK2 scanZLLPackK2 evalCheckPtPackK2 evalLaneVQMPackK2

theorem checkHalfZLLPackK2_sound (ch : ChK2) (cb : ChW11) (k step2 wBase n iBase : Nat)
    (hle : iBase + n ≤ 128)
    {a0 : Nat} {r01 : Bool} {p0 : Nat} {st4 : ST4}
    (hst : IsST4Of8 (sweepBktPackK2 a0 r01 p0) st4)
    (t11 g hi lo s0Sq : Nat)
    (ht11_mod : t11 % step2 = 0)
    (hc : ST4.casesOn st4 (fun _ a b c d =>
      checkHalfZLLPackK2 ch (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256)
          (2 ^ k) step2 wBase n iBase)
        (unpk3K2 ch (stVal63 a)) a (unpk3K2 ch (stVal63 b)) b
        (unpk3K2 ch (stVal63 c)) c (unpk3K2 ch (stVal63 d)) d t11 step2 g hi lo s0Sq) = true) :
    ∀ i7, iBase ≤ i7 → i7 < iBase + n →
      let m := (wBase + 2048 * i7) / step2 + t11 / step2
      ¬(m % 8 = 7) → ¬(m % 32 = 28) →
      checkNum63 (evalST4FK2 (projUnpkST4K2 ch st4) (zKnotLo6 cb k i7 0) (zKnotLo6 cb k i7 1)
        (zKnotLo6 cb k i7 2) (zKnotLo6 cb k i7 3)) m g hi lo s0Sq = true := by
  rcases st4 with ⟨s, a, b, c, d⟩
  rcases hst with ⟨haT, hbT, hcT, hdT⟩
  obtain ⟨_, vqa, _⟩ := sweepBktPackK2_lane_unpk ch haT; obtain ⟨_, vqb, _⟩ :=
      sweepBktPackK2_lane_unpk ch hbT; obtain ⟨_, vqc, _⟩ :=
      sweepBktPackK2_lane_unpk ch hcT; obtain ⟨_, vqd, _⟩ :=
      sweepBktPackK2_lane_unpk ch hdT; dsimp only [checkHalfZLLPackK2] at hc
  rw [nat_mod_def, nat_div_def, ht11_mod, show Nat.beq 0 0 = true from rfl] at hc
  dsimp only [Bool.casesOn] at hc;
  exact scanZLLPackK2_sound ch cb k step2 wBase s a b c d vqa vqb vqc vqd (t11 /
      step2) g hi lo s0Sq hle hc
attribute [local irreducible] checkHalfZLLPackK2

theorem buildZOct10LK2_eq (cb : ChW11) : buildZOct10LK2 cb =
    .mk (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 16 512 131072 64 0)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 16 256 0 64 64)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 32 128 131072 64 0)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 32 64 0 64 64)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 64 32 131072 64 0)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 64 16 0 64 64)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 128 8 131072 64 0)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 128 4 0 64 64)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 256 2 131072 64 0)
    (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) 256 1 0 30 64) := by
  unfold buildZOct10LK2; simp only [sNT63_eq, sZLL_eq]
attribute [local irreducible] buildZOct10LK2

theorem buildChCtx3PackK2_aux (cb : ChW11) (isNN : Bool) (zo : ZOct10L)
    (D c5714 c64k mc hiN loN c1000 c2p35 : Nat) : (fN63 D fun D => fN63 (Nat.mul c64k mc) fun g =>
    fN63 (Nat.mul (Nat.mul hiN c5714) D) fun hi => fN63 (Nat.mul (Nat.mul loN c5714) D) fun lo =>
    fN63 (Nat.pow (Nat.mul (Nat.mul (Nat.mul c1000 c5714) c2p35) D) 2) fun s0Sq =>
    ZOct10L.casesOn zo fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 =>
    ChCtx3PackK2.mk cb isNN (.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) g hi lo s0Sq) =
    ChCtx3PackK2.mk cb isNN zo (c64k * mc) (hiN * c5714 * D) (loN * c5714 * D)
    ((c1000 * c5714 * c2p35 * D) ^ 2) := by
  cases zo
  rfl

theorem chConstsK2_self (ch : ChK2) : ChConstsK2 ch (64000 * chMcK2 ch)
    (chHiNumK2 ch * 5714023029 * chTotWK2 ch) (chLoNumK2 ch * 5714023029 * chTotWK2 ch)
    ((1000 * 5714023029 * 34359738368 * chTotWK2 ch) ^ 2) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem buildChCtx3PackK2_spec (ch : ChK2) : ∃ g hi lo s0Sq : Nat, ChConstsK2 ch g hi lo s0Sq ∧
    buildChCtx3PackK2 ch = .mk (chFnChK2 ch) (chIsNNK2 ch)
    (buildZOct10LK2 (chFnChK2 ch)) g hi lo s0Sq :=
    ⟨64000 * chMcK2 ch, chHiNumK2 ch * 5714023029 * chTotWK2 ch, chLoNumK2 ch * 5714023029 *
    chTotWK2 ch, (1000 * 5714023029 * 34359738368 * chTotWK2 ch) ^ 2, chConstsK2_self ch,
    buildChCtx3PackK2_aux (chFnChK2 ch) (chIsNNK2 ch) (buildZOct10LK2 (chFnChK2 ch))
    (chTotWK2 ch) 5714023029 64000 (chMcK2 ch) (chHiNumK2 ch) (chLoNumK2 ch) 1000 34359738368⟩
attribute [local irreducible] buildChCtx3PackK2 ChConstsK2

theorem ulp_of_checkAtT11ZLLPackK2 (ch : ChK2) {g hi lo s0Sq d2 : Nat} {st : ST4}
    (hK : ChConstsK2 ch g hi lo s0Sq)
    (hd2ge : 256 ≤ d2) (hd2lt : d2 < 192512) (hm7 : ¬(d2 % 8 = 7)) (hm28 : ¬(d2 % 32 = 28))
    (hst : IsST4Of8 (sweepBktPackK2
      (t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2) / 64)
      (r01OfR6 (t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2) % 64))
      (128 * (t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2) % 64))) st)
    (hck : checkAtT11ZLLPackK2 ch (buildZOct10LK2 (chFnChK2 ch))
      (t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2)) st g hi lo s0Sq = true) :
    |((chMcK2 ch : ℝ) / ((1 : ℝ) * 5714023029)) *
        expFnK2 (chWgtK2 ch) (chTotWK2 ch) (chFn30K2 ch) word512DualLegLo6 (chIsNNK2 ch) d2 -
      (chDcMilliK2 ch : ℝ) / 1000 -
      (2 ^ 35 : ℝ) / √((max d2 (if chIsNNK2 ch then 8 else 1) : ℕ) : ℝ)| ≤
        (chEpsMilliK2 ch : ℝ) / 1000 := by
  have hd2_262 : d2 < 262144 := by omega
  obtain ⟨hk4, hk8, hi7lt, ht11lt, _, _⟩ :=
    @evenOct_mid_props_w11B (chIsNNK2 ch) d2 hd2ge (by omega : d2 < 194560)
  have hmsh := evenOct_m_shift_w11B (chIsNNK2 ch) hd2_262; dsimp only at hmsh
  set cb := chFnChK2 ch; set p := evenOctIdxT10K (chIsNNK2 ch) d2
  set i7 := idx7OfParts p; set t11 := t11OfParts p
  rw [show max d2 (if chIsNNK2 ch then 8 else 1) = d2 by
    cases chIsNNK2 ch <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega] at hmsh ⊢
  have hstCh := (projUnpkST4K2_spec ch hst).1
  rcases st with ⟨s_st, ta, tb, tc, td⟩
  rw [buildZOct10LK2_eq] at hck; unfold checkAtT11ZLLPackK2 at hck; dsimp only at hck
  simp only [fN63_eq, andB63_eq_true] at hck
  rcases hck with ⟨c4lo, c4hi, c5lo, c5hi, c6lo, c6hi, c7lo, c7hi, c8lo, c8hi⟩
  have hNum : checkNum63 (evalST4FK2 (projUnpkST4K2 ch (.mk s_st ta tb tc td))
      (zKnotLo6 cb p.2.2 i7 0) (zKnotLo6 cb p.2.2 i7 1)
      (zKnotLo6 cb p.2.2 i7 2) (zKnotLo6 cb p.2.2 i7 3)) d2 g hi lo s0Sq = true := by
    have hG (b k : Nat) {s2 wBase n iBase : Nat} (hk : p.2.2 = k)
        (hmB : d2 * 2 ^ (b - 2 * p.2.2) = wBase + 2048 * i7 + t11)
        (hc : checkHalfZLLPackK2 ch
          (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) (2 ^ k) s2 wBase n iBase)
          (unpk3K2 ch (stVal63 ta)) ta (unpk3K2 ch (stVal63 tb)) tb
          (unpk3K2 ch (stVal63 tc)) tc (unpk3K2 ch (stVal63 td)) td
          t11 s2 g hi lo s0Sq = true)
        (hPow : 2 ^ (b - 2 * k) = s2 := by rfl)
        (hwB : wBase = 0 ∨ wBase = 131072 := by omega)
        (hAr : iBase + n ≤ 128 ∧ iBase ≤ i7 ∧ (d2 * s2 = wBase + 2048 * i7 + t11 → i7 < iBase + n) ∧
          (s2 = 512 ∨ s2 = 256 ∨ s2 = 128 ∨ s2 = 64 ∨ s2 = 32 ∨
            s2 = 16 ∨ s2 = 8 ∨ s2 = 4 ∨ s2 = 2 ∨ s2 = 1) := by omega) := by
      rw [hk, hPow] at hmB
      have hStep := t11_step_arith hAr.2.2.2 hwB hmB
      have h := checkHalfZLLPackK2_sound ch cb k s2 wBase n iBase hAr.1 hst t11 g hi lo s0Sq
        hStep.1 hc i7 hAr.2.1 (hAr.2.2.1 hmB)
      dsimp only at h
      rw [← hk, hStep.2] at h
      exact h hm7 hm28
    by_cases h64 : 64 ≤ i7
    · rw [Nat.ble_eq.mpr h64, Bool.cond_true, Bool.cond_true] at hmsh
      have hmsh0 : d2 * 2 ^ (16 - 2 * p.2.2) = 0 + 2048 * i7 + t11 := by omega
      rcases (by omega : p.2.2 = 4 ∨ p.2.2 = 5 ∨ p.2.2 = 6 ∨ p.2.2 = 7 ∨ p.2.2 = 8) with
        hk | hk | hk | hk | hk
      exacts [hG 16 4 hk hmsh0 c4hi, hG 16 5 hk hmsh0 c5hi, hG 16 6 hk hmsh0 c6hi,
        hG 16 7 hk hmsh0 c7hi, hG 16 8 hk hmsh0 c8hi]
    · rw [Bool.eq_false_iff.mpr (mt Nat.ble_eq.mp h64), Bool.cond_false, Bool.cond_false] at hmsh
      rcases (by omega : p.2.2 = 4 ∨ p.2.2 = 5 ∨ p.2.2 = 6 ∨ p.2.2 = 7 ∨ p.2.2 = 8) with
        hk | hk | hk | hk | hk
      exacts [hG 17 4 hk hmsh c4lo, hG 17 5 hk hmsh c5lo, hG 17 6 hk hmsh c6lo,
        hG 17 7 hk hmsh c7lo, hG 17 8 hk hmsh c8lo]
  exact ulp_k2_of_checkNum63 ch hK (by omega)
    (evalST4FK2_sweepBktK2_eq_expFnK2 ch hd2_262 hstCh) hNum

theorem ulp_of_checkPtSkipOtherPackK2 (ch : ChK2) {g hi lo s0Sq a r6 d2 : Nat} {st4 : ST4}
    (hK : ChConstsK2 ch g hi lo s0Sq) (hd2 : d2 < 262144) (hm7 : ¬(d2 % 8 = 7))
    (ha_eq : t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2) / 64 = a)
    (hr6_eq : t11OfParts (evenOctIdxT10K (chIsNNK2 ch) d2) % 64 = r6)
    (hst : IsST4Of8 (sweepBktPackK2 a (r01OfR6 r6) (128 * r6)) st4)
    (hc : checkPtSkipOtherPackK2 ch (chFnChK2 ch) (chIsNNK2 ch) (bNT9 word512DualLegLo6T 0 256)
      a r6 st4 g hi lo s0Sq d2 = true) :
    |((chMcK2 ch : ℝ) / ((1 : ℝ) * 5714023029)) *
        expFnK2 (chWgtK2 ch) (chTotWK2 ch) (chFn30K2 ch) word512DualLegLo6 (chIsNNK2 ch) d2 -
      (chDcMilliK2 ch : ℝ) / 1000 -
      (2 ^ 35 : ℝ) / √((max d2 (if chIsNNK2 ch then 8 else 1) : ℕ) : ℝ)| ≤
        (chEpsMilliK2 ch : ℝ) / 1000 := by
  obtain ⟨hstCh, hevalEq⟩ := projUnpkST4K2_spec ch hst; unfold checkPtSkipOtherPackK2 at hc
  rw [nat_mod_def, show Nat.beq (d2 % 8) 7 = false from
    Bool.eq_false_iff.mpr fun ht => hm7 (Nat.beq_eq.mp ht)] at hc
  dsimp only [Bool.casesOn] at hc; rw [sParts_eq, evenOctPartsW11_eq_w11B, fN63_eq] at hc
  set cb := chFnChK2 ch; set p := evenOctIdxT10K (chIsNNK2 ch) d2
  obtain ⟨hi7, _, _⟩ := parts_popBern_bounds (chIsNNK2 ch) hd2;
  have ht11 : Nat.add (Nat.mul (Nat.mod p.1 2) 1024) p.2.1 = t11OfParts p := rfl
  have ha_p : Nat.div (t11OfParts p) 64 = a := by rw [nat_div_def]; exact ha_eq
  have hr6_p : Nat.mod (t11OfParts p) 64 = r6 := by rw [nat_mod_def]; exact hr6_eq
  rw [ht11, ha_p, hr6_p, show andB63 (Nat.beq a a) (Nat.beq r6 r6) = true by
    rw [Nat.beq_refl a, Nat.beq_refl r6]; rfl] at hc
  dsimp only [Bool.casesOn] at hc;
  simp only [fN63_eq, nat_div_def, nat_pow_def, nat_mul_def, nat_add_def, maxDistW11_eq_w11B] at hc
  rw [show p.1 / 2 = idx7OfParts p from rfl] at hc
  have hz (j : Nat) (hj : j < 4) := zKnotFast_at_lo6NT cb p.2.2 (idx7OfParts p) j hi7 hj
  have hz0 := hz 0 (by omega)
  simp only [nat_div_def, add_zero] at hz hz0
  rw [hz0, hz 1 (by omega), hz 2 (by omega), hz 3 (by omega), hevalEq] at hc
  subst ha_eq; subst hr6_eq
  have hm1 : 1 ≤ max d2 (if chIsNNK2 ch then 8 else 1) := by
    cases chIsNNK2 ch <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  exact ulp_k2_of_checkNum63 ch hK hm1 (evalST4FK2_sweepBktK2_eq_expFnK2 ch hd2 hstCh) hc

attribute [local irreducible] checkAtT11ZLLPackK2 checkPtSkipOtherPackK2

theorem sweepR6TreeP2PackK2_sound (lo6NT : NatTree) (ctxEE ctxNN ctxEN : ChCtx3PackK2) (a : Nat) :
    ∀ (d b : Nat) {cur : ST4P2},
      b + 2 ^ d ≤ 64 → IsST4P2PackOfK2 a (128 * b) cur →
      match sweepR6TreeP2PackK2 lo6NT ctxEE ctxNN ctxEN a (bNT11 (jPack4Leaf a) 0 1024) d b
        (buildNT63 samplePackLeafK2Pure (d + 7) (128 * b) (2 ^ (d + 6)))
        (buildNT63 (fun idx11 => pack3WgtFK2 (wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)))
          (d + 5) (32 * b) (2 ^ (d + 4))) cur with
      | .mk false _ => True
      | .mk true nxt =>
          IsST4P2PackOfK2 a (128 * (b + 2 ^ d)) nxt ∧ ∀ off < 2 ^ d, ∃ st : ST4,
              IsST4Of8 (sweepBktPackK2 a (r01OfR6 (b + off)) (128 * (b + off))) st ∧
                checkOneChPackK2 .ee ctxEE lo6NT a (b + off) (64 * a + (b + off)) st = true ∧
                checkOneChPackK2 .nn ctxNN lo6NT a (b + off) (64 * a + (b + off)) st = true ∧
                checkOneChPackK2 .en ctxEN lo6NT a (b + off) (64 * a + (b + off)) st = true
  | 0, b, cur, hb, hcur => by
      dsimp only [sweepR6TreeP2PackK2]; rw [sST4_eq, fN63_eq, nat_add_def, nat_mul_def]
      cases cEE : checkOneChPackK2 .ee ctxEE lo6NT a b (64 * a + b) (selST4P2 (r01OfR6 b) cur)
      · exact trivial
      · dsimp only [Bool.casesOn]
        cases cNN : checkOneChPackK2 .nn ctxNN lo6NT a b (64 * a + b) (selST4P2 (r01OfR6 b) cur)
        · exact trivial
        · dsimp only [Bool.casesOn]
          cases cEN : checkOneChPackK2 .en ctxEN lo6NT a b (64 * a + b) (selST4P2 (r01OfR6 b) cur)
          · exact trivial
          · dsimp only [Bool.casesOn]; rw [sST4P2_eq]
            have hcur' : IsST4P2PackOfK2 a (4 * (32 * b)) cur := by
              rwa [show 4 * (32 * b) = 128 * b by ring]
            have hadv := advSub6P2K2_pack_sound a 5 (32 * b) (by omega) hcur'
            rw [show (2 ^ 5 / 2 : Nat) = 16 by norm_num, show 4 * (32 * b) = 128 * b by ring,
                show 4 * (32 * b + 2 ^ 5) = 128 * (b + 1) by ring] at hadv
            refine ⟨by rwa [show 128 * (b + 2 ^ 0) = 128 * (b + 1) by rfl], fun off hoff => ?_⟩
            have hz : off = 0 := by omega
            subst hz; rw [add_zero]
            exact ⟨selST4P2 (r01OfR6 b) cur, selST4P2PackK2_sound hcur (r01OfR6 b), cEE, cNN, cEN⟩
  | d + 1, b, cur, hb, hcur => by
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := (Nat.pow_succ 2 d).trans (Nat.mul_two (2 ^ d))
      have hp := Nat.two_pow_pos d
      rw [hpow] at hb
      have hSplit (f : Nat → Nat) (k m : Nat) (hm : 2 ^ (k + 1) = m) :
          buildNT63 f (d + 1 + (k + 1)) (m * b) (2 ^ (d + 1 + k)) =
            .node (buildNT63 f (d + (k + 1)) (m * b) (2 ^ (d + k)))
                  (buildNT63 f (d + (k + 1)) (m * (b + 2 ^ d)) (2 ^ (d + k))) := by
        rw [show d + 1 + (k + 1) = (d + (k + 1)) + 1 by omega,
          show d + 1 + k = d + (k + 1) by omega, buildNT63_succ f (d + (k + 1)),
          show 2 ^ (d + (k + 1)) / 2 = 2 ^ (d + k) by
            rw [show d + (k + 1) = (d + k) + 1 by omega, Nat.pow_succ]; omega,
          show m * b + 2 ^ (d + (k + 1)) = m * (b + 2 ^ d) by rw [Nat.pow_add, hm]; ring]
      rw [hSplit samplePackLeafK2Pure 6 128 (by norm_num), hSplit _ 4 32 (by norm_num)]
      dsimp only [sweepR6TreeP2PackK2]
      simp only [fN63_eq, nat_add_def, nat_pow_def]
      have hL := sweepR6TreeP2PackK2_sound lo6NT ctxEE ctxNN ctxEN a d b (by omega) hcur
      obtain ⟨ok1, mid, hEqL⟩ := elim_st4p2b (sweepR6TreeP2PackK2 lo6NT ctxEE ctxNN ctxEN a
        (bNT11 (jPack4Leaf a) 0 1024) d b
        (buildNT63 samplePackLeafK2Pure (d + 7) (128 * b) (2 ^ (d + 6)))
        (buildNT63 (fun i => pack3WgtFK2 (wOfU5GamF (Nat.mod i 32) (Nat.div i 32)))
          (d + 5) (32 * b) (2 ^ (d + 4))) cur)
      rw [hEqL] at hL ⊢
      rw [sST4P2B_eq]
      dsimp only
      cases ok1
      · trivial
      · dsimp only [Bool.casesOn]
        rcases hL with ⟨hmid, gL⟩
        have hR := sweepR6TreeP2PackK2_sound lo6NT ctxEE ctxNN ctxEN a d (b + 2 ^ d) (by omega) hmid
        obtain ⟨ok2, nxt, hEqR⟩ := elim_st4p2b (sweepR6TreeP2PackK2 lo6NT ctxEE ctxNN ctxEN a
          (bNT11 (jPack4Leaf a) 0 1024) d (b + 2 ^ d)
          (buildNT63 samplePackLeafK2Pure (d + 7) (128 * (b + 2 ^ d)) (2 ^ (d + 6)))
          (buildNT63 (fun i => pack3WgtFK2 (wOfU5GamF (Nat.mod i 32) (Nat.div i 32)))
            (d + 5) (32 * (b + 2 ^ d)) (2 ^ (d + 4))) mid)
        rw [hEqR] at hR ⊢
        cases ok2
        · trivial
        · dsimp only at hR ⊢
          rcases hR with ⟨hnxt, gR⟩
          refine ⟨by rwa [hpow, ← Nat.add_assoc], fun off hoff => ?_⟩
          by_cases hlt : off < 2 ^ d
          · exact gL off hlt
          · obtain ⟨st, hst, c0, c1, c2⟩ := gR (off - 2 ^ d) (by rw [Nat.pow_succ] at hoff; omega)
            have heq : b + 2 ^ d + (off - 2 ^ d) = b + off := by omega
            rw [heq] at hst c0 c1 c2; exact ⟨st, hst, c0, c1, c2⟩

attribute [local irreducible] sweepR6TreeP2PackK2

theorem sweepR6TreeP2PackK2_sound_top (lo6NT : NatTree) (ctxEE ctxNN ctxEN : ChCtx3PackK2)
    (a : Nat) {cur : ST4P2} (hcur : IsST4P2PackOfK2 a 0 cur) :
    match sweepR6TreeP2PackK2 lo6NT ctxEE ctxNN ctxEN a (bNT11 (jPack4Leaf a) 0 1024) 6 0
      buildSamplePackK2NT buildWgtPackK2NT cur with
    | .mk false _ => True
    | .mk true nxt =>
        IsST4P2PackOfK2 a 8192 nxt ∧ ∀ off < 64, ∃ st : ST4,
            IsST4Of8 (sweepBktPackK2 a (r01OfR6 off) (128 * off)) st ∧
              checkOneChPackK2 .ee ctxEE lo6NT a off (64 * a + off) st = true ∧
              checkOneChPackK2 .nn ctxNN lo6NT a off (64 * a + off) st = true ∧
              checkOneChPackK2 .en ctxEN lo6NT a off (64 * a + off) st = true := by
  have hcur0 : IsST4P2PackOfK2 a (128 * 0) cur := hcur
  have hSw := sweepR6TreeP2PackK2_sound lo6NT ctxEE ctxNN ctxEN a 6 0 (by norm_num) hcur0
  simp only [Nat.mul_zero, zero_add,
    show 6 + 7 = 13 by rfl, show 6 + 6 = 12 by rfl, show 6 + 5 = 11 by rfl, show 6 + 4 = 10 by rfl,
    show (2 ^ 12 : Nat) = 4096 by norm_num, show (2 ^ 10 : Nat) = 1024 by norm_num,
    show (2 ^ 6 : Nat) = 64 by norm_num, show 128 * 64 = 8192 by rfl,
    buildSamplePackK2NT_def, buildWgtPackK2NT_def] at hSw
  exact hSw

theorem checkPairFast3K2_sound (b : Nat) (h : checkPairFast3K2 b = true) : ∀ ch : ChK2, ∀ da < 2,
    ∀ r6 < 64, ∃ g hi lo s0Sq : Nat, ∃ st : ST4, ChConstsK2 ch g hi lo s0Sq ∧
    IsST4Of8 (sweepBktPackK2 (2 * b + da) (r01OfR6 r6) (128 * r6)) st ∧
    checkAtT11ZLLPackK2 ch (buildZOct10LK2 (chFnChK2 ch)) (64 * (2 * b + da) + r6) st g hi lo s0Sq =
    true ∧ checkSmAtARPackK2 ch (chFnChK2 ch) (chIsNNK2 ch) (bNT9 word512DualLegLo6T 0 256)
    (2 * b + da) r6 st g hi lo s0Sq = true := by
  unfold checkPairFast3K2 at h;
  obtain ⟨gEE, hiEE, loEE, sqEE, hKEE, hCtxEE⟩ :=
      buildChCtx3PackK2_spec .ee; obtain ⟨gNN, hiNN, loNN, sqNN, hKNN, hCtxNN⟩ :=
      buildChCtx3PackK2_spec .nn; obtain ⟨gEN, hiEN, loEN, sqEN, hKEN, hCtxEN⟩ :=
      buildChCtx3PackK2_spec .en
  rw [hCtxEE, hCtxNN, hCtxEN] at h; dsimp only at h
  simp only [sNT63_eq, fN63_eq, sST4P2_eq, nat_mul_def, nat_add_def, spNTFastK2_eq, buildJPackNT_eq,
      bNT11_wgtPackK2_eq] at h
  set lo6NT := bNT9 word512DualLegLo6T 0 256
  set ctxEE :=
      ChCtx3PackK2.mk (chFnChK2 .ee) (chIsNNK2 .ee)
      (buildZOct10LK2 (chFnChK2 .ee)) gEE hiEE loEE sqEE
  set ctxNN :=
      ChCtx3PackK2.mk (chFnChK2 .nn) (chIsNNK2 .nn)
      (buildZOct10LK2 (chFnChK2 .nn)) gNN hiNN loNN sqNN
  set ctxEN :=
      ChCtx3PackK2.mk (chFnChK2 .en) (chIsNNK2 .en)
      (buildZOct10LK2 (chFnChK2 .en)) gEN hiEN loEN sqEN
  have hSw0 :=
      sweepR6TreeP2PackK2_sound_top lo6NT ctxEE ctxNN ctxEN (2 * b)
      (initTreeP2FastK2_isST4P2PackOf (2 * b)); obtain ⟨ok0, midP2, hEq0⟩ :=
      elim_st4p2b (sweepR6TreeP2PackK2 lo6NT ctxEE ctxNN ctxEN (2 * b)
      (bNT11 (jPack4Leaf (2 *
      b)) 0 1024) 6 0 buildSamplePackK2NT buildWgtPackK2NT (initTreeP2FastK2 (bNT11 (jPack4Leaf (2 *
      b)) 0 1024) buildSamplePackK2NT buildWgtPackK2NT))
  rw [hEq0] at hSw0 h; rw [sST4P2B_eq] at h; dsimp only at h
  cases ok0
  · exact Bool.noConfusion h
  · dsimp only [Bool.casesOn] at h; rcases hSw0 with ⟨hMid8192, g0⟩
    have hSw1 :=
        sweepR6TreeP2PackK2_sound_top lo6NT ctxEE ctxNN ctxEN (2 * b + 1)
        (even_end_isST4P2PackOfK2_succ b hMid8192); obtain ⟨ok1, _, hEq1⟩ :=
        elim_st4p2b (sweepR6TreeP2PackK2 lo6NT ctxEE ctxNN ctxEN (2 * b + 1)
        (bNT11 (jPack4Leaf (2 * b + 1)) 0 1024) 6 0 buildSamplePackK2NT buildWgtPackK2NT midP2)
    rw [hEq1] at hSw1 h; dsimp only at h; subst h; rcases hSw1 with ⟨_, g1⟩
    intro ch da hda r6 hr6
    have hPair : ∃ st : ST4, IsST4Of8 (sweepBktPackK2 (2 * b + da) (r01OfR6 r6) (128 * r6)) st ∧
        checkOneChPackK2 .ee ctxEE lo6NT (2 * b + da) r6 (64 * (2 * b + da) + r6) st = true ∧
        checkOneChPackK2 .nn ctxNN lo6NT (2 * b + da) r6 (64 * (2 * b + da) + r6) st = true ∧
        checkOneChPackK2 .en ctxEN lo6NT (2 * b + da) r6 (64 * (2 * b + da) + r6) st = true := by
      rcases (by omega : da = 0 ∨ da = 1) with rfl | rfl
      · simpa only [add_zero] using g0 r6 hr6
      · exact g1 r6 hr6
    obtain ⟨st, hst, cEE, cNN, cEN⟩ := hPair
    cases ch
    · dsimp only [checkOneChPackK2, ctxEE] at cEE;
      obtain ⟨cZ, cS⟩ :=
          (andB63_eq_true _ _).mp cEE; exact ⟨gEE, hiEE, loEE, sqEE, st, hKEE, hst, cZ, cS⟩
    · dsimp only [checkOneChPackK2, ctxNN] at cNN;
      obtain ⟨cZ, cS⟩ :=
          (andB63_eq_true _ _).mp cNN; exact ⟨gNN, hiNN, loNN, sqNN, st, hKNN, hst, cZ, cS⟩
    · dsimp only [checkOneChPackK2, ctxEN] at cEN;
      obtain ⟨cZ, cS⟩ :=
          (andB63_eq_true _ _).mp cEN; exact ⟨gEN, hiEN, loEN, sqEN, st, hKEN, hst, cZ, cS⟩
attribute [local irreducible] checkPairFast3K2

theorem channel_ulp_k2_fast (ch : ChK2)
    (hB2 : ∀ b : Nat, b < 16 → checkPairFast3K2 b = true)
    {d2 : ℕ} (h3d : Is3DBoxDistSq d2) (hm7 : ¬(d2 % 8 = 7)) :
    |((chMcK2 ch : ℝ) / ((1 : ℝ) * 5714023029)) *
        expFnK2 (chWgtK2 ch) (chTotWK2 ch) (chFn30K2 ch) word512DualLegLo6 (chIsNNK2 ch) d2 -
      (chDcMilliK2 ch : ℝ) / 1000 -
      (2 ^ 35 : ℝ) / √((max d2 (if chIsNNK2 ch then 8 else 1) : ℕ) : ℝ)| ≤
        (chEpsMilliK2 ch : ℝ) / 1000 := by
  have hd2lt : d2 < 262144 := by have := is3DBoxDistSq_le h3d; omega
  set p := evenOctIdxT10K (chIsNNK2 ch) d2
  obtain ⟨_, ht11lt, _⟩ := parts_popBern_bounds (chIsNNK2 ch) hd2lt
  set t11 := t11OfParts p; set a := t11 / 64; set r6 := t11 % 64
  have ha32 : a < 32 := by dsimp [a]; omega
  have hr6_64 : r6 < 64 := by dsimp [r6]; omega
  obtain ⟨gB, hiB, loB, sqB, st, hKB, hst, hckZLL, hckSm⟩ :=
    checkPairFast3K2_sound (a / 2) (hB2 (a / 2) (by omega)) ch (a % 2) (by omega) r6 hr6_64
  rw [Nat.div_add_mod a 2] at hst hckZLL hckSm; rw [Nat.div_add_mod t11 64] at hckZLL
  by_cases hsm : d2 < 256
  · obtain ⟨hr6_0, ha_mod16⟩ := smCoords_lt256 (chIsNNK2 ch) hsm
    have hr6_0' : r6 = 0 := hr6_0; have ha_mod16' : a % 16 = 0 := ha_mod16
    unfold checkSmAtARPackK2 at hckSm; obtain ⟨hSmLt, _⟩ := (andB63_eq_true _ _).mp hckSm
    rw [show andB63 (Nat.beq r6 0) (Nat.beq (Nat.mod a 16) 0) = true by
      rw [nat_mod_def, hr6_0', ha_mod16']; rfl] at hSmLt
    dsimp only [Bool.casesOn] at hSmLt
    exact ulp_of_checkPtSkipOtherPackK2 ch hKB hd2lt hm7 rfl hr6_0
      (by rwa [hr6_0'] at hst) (by simpa only [zero_add] using allCnt63_sound hSmLt d2 hsm)
  · by_cases hge : 192512 ≤ d2
    · have hmem := openDistSq_ge_192512_mem_tail16 h3d hge hm7; obtain ⟨ha_mod8, hr6_d2⟩ :=
          smCoords_tail16 (chIsNNK2 ch) hmem
      have ha_mod8' : a % 8 = 0 := ha_mod8; have hr6_d2' : d2 % 64 = r6 := hr6_d2.symm
      unfold checkSmAtARPackK2 at hckSm; obtain ⟨_, hSmTl⟩ := (andB63_eq_true _ _).mp hckSm
      rw [show Nat.beq (Nat.mod a 8) 0 = true by rw [nat_mod_def, ha_mod8']; rfl] at hSmTl
      dsimp only [Bool.casesOn] at hSmTl; have hpt := allList63_sound hSmTl d2 hmem
      rw [show Nat.beq (Nat.mod d2 64) r6 =
          true by rw [nat_mod_def, hr6_d2']; exact Nat.beq_refl r6] at hpt
      dsimp only [Bool.casesOn] at hpt;
      exact ulp_of_checkPtSkipOtherPackK2 ch hKB hd2lt hm7 rfl rfl hst hpt
    · exact ulp_of_checkAtT11ZLLPackK2 ch hKB (by omega)
          (by omega) hm7 (is3DBoxDistSq_mod32_ne_28 h3d) hst hckZLL

attribute [local irreducible] checkSmAtARPackK2
end QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs
end
end

end
