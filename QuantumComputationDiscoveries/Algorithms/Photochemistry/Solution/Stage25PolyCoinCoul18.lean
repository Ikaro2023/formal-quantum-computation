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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage4SubCoinK2Bridge
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CyclotomicPhaseCheck
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SelectSwapQromUnload
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CoulombMid36Stage5W298
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
scoped instance : NeZero 2 := ⟨two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
set_option autoImplicit false
set_option allowUnsafeReducibility true
open scoped Matrix BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg
  writeReg_apply_of_not_mem writeReg_apply_reg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
    (basisOutcomeProjector_compose_zero cleanWorkStep_embed_of_subspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Pers12Dom168M72 (fOut22k123 fPers18k123
    pDomSplitPers12_168 pDomSplitPers12_168_counts_wires pDomSplitPers12_168_step_cb2 rOut22k123
    rPers12Of rPers18k123 rPool72k123)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulOWPersBridge (cowp_stepCB_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ClusterPotSlice (elecP nucP)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (mkKetOpW mkKetOpW_congr
    natOfZModBits)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinNormSlice (OpSys)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA (dLayout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor (byteOfBits)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast (dynWires_wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu (subspaceStep_of_eq_post)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge (lcuSubLGen reflULGen
    reflULGen_eq scrSubLGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulombK115 (cnot_counts_wires
    dom22Bit21_eq_d2_xor natOfZModBits18_bit zmod2_dom21_xor_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (ST4 ST4P2 ST4P2B ST4T3
    ZLeafL ZOct10L allCnt63 allCnt63_sound allList63 allList63_sound andB63 andB63_eq_true bNT11
    bNT13 bNT13_eq bNT6 bNT7 bNT9 buildJPackNT buildJPackNT_eq buildNT63)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (buildNT63_succ
    buildNT63_zero checkNum63 checkNum63_sound elim_st4p2b fN63 fN63_eq getNT1024F getNT256F
    getNT32F getNT64F get_bNT11 is3DBoxDistSq_mod32_ne_28 jPack4Leaf nat_add_def)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (nat_div_def nat_mod_def
    nat_mul_def nat_pow_def nat_sub_def openDistSq_ge_192512_mem_tail16 r01OfR6 sB63 sB63_eq sNT63
    sNT63_eq sParts sParts_eq sST4 sST4P2 sST4P2B sST4P2B_eq sST4P2_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (sST4T3 sST4T3_eq sST4_eq
    sZLL_eq selST4P2 smCoords_lt256 smCoords_tail16 stVal63 stVal63_eq stVal_eq_sumAllST sufST
    sufST_eq_sumSufST sufST_le_add_stVal sumAllST sumSufST sumSufST_none)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (t11_step_arith
    tail16List updAdd_updSub_bkt wOfU5GamF_eq_spec zKnotFast_at_lo6NT)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (ReflPotSliceSpec24
    equivBitZMod2 potB24GateActive potOraclePortB24BitEval potOraclePortB24CoinEval
    potReflPortBPh0_24 potReflPortBSt24 rPotB24ElecA rPotB24NucA rPotB24PortB rPotBCoin24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Stage4 (rPotBWork24 w11Sub63
    wPotB24IsNN wPotB24IsPot wPotB24IsScreen wPotB24LocQ wPotB24Sp1B0 wPotB24Sp1B1 wPotB24Sp2B0
    wPotB24Sp2B1 zmod2_eq_of_beq_one_eq_s1b)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Walk
    (liftReflPotSlice24To35_sub63 put24In35_sub63 take24Of35_sub63)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge (concatBitsGen
    equivBits11 mSpCart254 outSubRawBits rCoinExtOut uMuxExtOut uMuxExtOut_val
    val_rCoinExtOut_bounds w11Idx w11RawBits)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBSharedPoly (Stage1AsymRevPkg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Bf33K9Scr31Opt
    (butterfly33K9Scr31Pkg258)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (OffIndexAndScratchPoly
    SelectLocalSpecGen ancWOfScr cat8SharedProjCompactGen lcuProjPoly locAncPoly
    locCat8SharedCompactGen locSysPoly projOneQCompactGen totDimCompactGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep
    stepCB)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney (spliceUnitary
    spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
    (embedUnitary_comm_of_disjoint)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectSandwich (hadamardRegSym
    hadamardRegSym_comm_disjoint)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA (phaseFlipUnitary)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift (circWires_toCircuit_c70
    circ_comm_embedMatrix_c70 concat_compose_rScrExt_c70 dite_pos_c70 embedUnitary_uTogLocal_c70
    hpExt lcuProj_ext_split_c70 muxMat_c70 pScrExt pScrExt_herm)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift (pScrExt_idem projBits_c70
    projBits_eq_embedMatrix_c70 rCoinExt rScrExt subspaceStep_stage1_fwd_ext_c70 sum_projBits_c70
    uPreExt uStage1Clean_c70 uTogGen_c70 uTogLocal_c70 val_rScrExt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (Is3DBoxDistSq d2_lt_262144
    dom22Bit idx7OfParts is3DBoxDistSq_le is3DBoxDistSq_pairOpenDistSq parts_popBern_bounds popBernJ
    rIdx7Of22 rJ2OfPers rK4Of22 rPoolOf rTop22Hi rY36Of)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
    (subspaceStep_wrapOnReg_mkKetOpW_mask2 t11OfParts y36PopBernNoClamp)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (ReflPotSliceSpec owB2Of3Port
    potGateActive4 potOracleCoinEval potReflPh4 potReflSwap4 reflPackPair_ne sectorDist3DSq3
    uPotReflZeroNErem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (uStage4ReflZeroNErem2m1Ideal
    uStage4ReflZeroNErem2m1_98CatCsel uStage4ReflZeroNErem2m1_98CatUsel)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885 (SafeConcatGen
    decDisjSysAnc_top)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.OuterW11Alt (ChW11 NatTree SumTree chFn
    chFnFast evenOctPartsW11 evenOctPartsW11_eq_w11B evenOct_m_shift_w11B evenOct_mid_props_w11B
    maxDistW11 maxDistW11_eq_w11B qKnotW11 stVal)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZHi30 (fnEE30 fnNN30)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254
    (finBitsVal_eq_natOfZModBits finBitsVal_inj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulombFast (subspaceStep_seq_u)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70 (evenOctIdxT10K)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.GenWeightsSelect (ValidGenZeroNEremCoin
    aImplGenZeroNEremOf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne disj_of_ne
    openCoordDistSq potGen_d2_lt potGen_k_lt potGen_mid_lt potGen_y36_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB (cPackCnotAux
    packUnpack_b potWrapSub_le subspaceStep_cnot_mkKetOpW)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream (maxWp24_le_738
    potZeroNEremPortB151WireFn rPotZeroNEremPortB151 val_potZeroNEremPortB151WireFn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (PotExpectFn
    bOuterZeroNErem coordOfReg24 elecParticle nucParticle sysCoord)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec (sum_fin_add)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.TelescopeSlice (pairOpenDistSq
    pairShortBin)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18 (decodePrimTree
    decodePrimTree_spec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec (ZeroNEremSector fin8Bin
    nucSpecies)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ScreenFermatCore (denomEEFermatCoin
    denomENFermatCoin denomNNFermatCoinVal elecParticle_eq_elecP nucParticle_eq_nucP
    openBoxDist3DSq_sys openCoordDistSq_sys pairOpenDistSq_mod8_ne7_u)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Cartesian254 (b2Spec b2Spec_lt255
    b6Inv1023 b6Spec b6Spec_1023 b6Spec_lt1023 sum_a8_a10_cart254 w11NatOfCoin w11NatOfCoin_lt2048
    w11NatOfCoin_testBit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (eqSec eqSec_iff phiU1
    phiU1Inv)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ParametricTelescope (rEEScaledGen
    rENScaledGen rNNScaledGen)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708 (tier1CoinOf5
    tier1CoinOf5_digits tier1EeTag tier1EnTag tier1FbKin tier1NnTag tier1_sum_coin41_split5
    tier1_sum_lo8_lo10_c5_w11 w11NatOfCoin_tier1CoinOf5)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc (aImplTier1WalkOf
    cntEE2048Tier1Walk cntNN2048Tier1Walk totalSlotsIdleTier1Walk wEESpeciesTier1Walk
    wEESpeciesTier1Walk_eq_factor wENSpeciesTier1Walk wENSpeciesTier1Walk_eq_factor wKinTier1Walk
    wNNSpeciesTier1Walk)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.GrayCodeKinNuc
    (wNNSpeciesTier1Walk_eq_factor)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_congr_out subspaceStep_of_circuit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore (ActiveOuterCoinStackOf
    OuterCoinSelectBundleStackAsym hpStack)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (counts_wrapDynOnReg
    wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Stage4 (otpDeltaSub62
    owK2Sub62PhaseBit3 potExpectK2Sub62 rW18Sub41_k2 splicedZ24Sub62 spliced_unsplice_of_eq_at2
    sub18Sub62Idx take17Of18 unspliceZ23Of24 unsplice_splicedZ24Sub62)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (CircWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt
    (Stage4ReflCoin24PotOraclePortBInPlace xorPortB24NotScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WRouterUnload76Opt
    (qromUnloadRootG89DualLeg_wrouter_76_unld)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48
    (clbGam6 natOfZModBits_of_testBit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18Leg1Pass
    (cntEETier1Walk_eq_wgtEETier1Walk cntNNTier1Walk_eq_wgtNNTier1Walk
    mSpCart254_pos_wstate nucSpecies_not_3_3_of_lt_wstate)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
    (out22_t11_bits)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs (ChK2 addST4K2
    addST4K2_isST4Of8 advLeafP2K2 advLeafP2K2_eq advOneST4K2 buildSamplePackK2NT
    buildSamplePackK2NT_def buildZLLK2 buildZOct10LK2 buildZOct10LK2_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs
    (chFn_ySampleK2_lo6_eq_zKnotLo6 d11At13 d11At13_lt_2048 decST4K2 decST4K2_isST4Of8 df8At13
    df8At13_lt_256 emptyST4T3K2F emptyST4T3K2F_isST4T3Sum8 equiv128Of32x2x2 equivN13Of64x128)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs (expFnK2 initLeafT3K2
    insST4K2 insST4K2_isST4Of8 j18At13 j18At13_lt_four j18AtARB_eq_popBernJK2 jPack4Leaf_unpack_at13
    midENK2 midNNK2 nLanes8 nLanes8_eq nSamples13 nSamples13_eq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs (o9At13 par14Pure
    par14Pure_eq_affineBit13 samplePackLeafK2Pure samplePackLeafK2Pure_eq_pack13 spNTFastK2
    spNTFastK2_eq sufST128F sufST128F_eq sumAll_add_sumSuf_eq_sumCarry256)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs (updAddST4K2 updSubST4K2
    vENK2 wAt13 wgtENQtr x13At13)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2 (affineBit13 allBelow
    allBelow_true_iff df8Of13 o9Of13 parity13Aux popBernJK2 popBernJK2_lt_four x13OfW11U01
    ySampleK2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOWTap29 (midWTap29)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Coul18K2 (midWTap29OfMode
    owK2PhaseBit3 potExpectK2Mode potExpectK2DualLegK17 z30K2_split14)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1CoinDecode
    (decodeTier1W11Opt1424Coin decodeTier1W11Opt1424Coin_coinOf5
    fib_ee_t1b_w11Nat_eq_cntEE2048 fib_en_t1b_w11Nat_eq_cntEN2048 fib_nn_t1b_w11Nat_eq_cntNN2048
    g66VOpt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1CoinDecode (kinNucBlkT1b_fst_ne
    sum_hi10_xor96 tier1WalkSym96TileKind tier1WalkSym96TileKind_lt8
    tier1W11ByKind tier1W11IntCell tier1W11IntCell_eq_byKind t1b_cond_ne_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1CoinDecode
    (validOuterW11_decodeTier1W11Opt1424Coin xor1024_96_props)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1UlpElecNuc (cntENTier1_eq_wgtEN)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4NoMuxK9Opt (ScrGGatedCoreDisj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBAncillaScrub
    (activeOuterCoinStack_rPermPotNuc3_potPortB151 cScrubNucFlags3 circWires_cScrubNucFlags3)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBAncillaScrub (rPermPotNuc3
    rSwapNucFlags3Top rSwapNucFlags3Top_fix swapNucFlags3TopVal val_rPermPotNuc3)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterAlwaysLoW338 (val_wOut0 val_wOut1
    val_wOut14 val_wOut15 val_wOut32 val_wOut34 val_wOut35 wOut0 wOut1 wOut14 wOut15 wOut32 wOut34
    wOut35)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KpBasis9WRouterOpt
    (kpBasis9WRouterPkg22)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (cEE1Fin8DualLeg
    cEE2Fin8DualLeg cNNFin8DualLeg equivW11CLB gEETier1Walk gNNTier1Walk midEETier1Walk
    short_table_eq_ee_tier1Walk v1Fin8DualLeg v2Fin8DualLeg wOfU5Gam wOfU5GamF wOfU5Gam_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (word512DualLegLo6
    word512DualLegLo6T zKnotLo6)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlacePortBOracle (castZeroAddReg_ipb
    pPotWrapReflPortB100InPlaceScrub pPotWrapReflPortB151InPlace skip17Of122Wp_ipb spec41Of24_ipb
    val_skip17Of122Wp_ipb)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam (hk0_le72_wstate
    liftReflPotSlice35To41_wstate permPot103Val put35In41_wstate rPermPot103
    rPermPot103_fix_of_bounds take35Of41_wstate)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Load438K78Opt
    (qromLoadRootG78DualLeg_438_k78_certChk certChk_load438_k78_hScr_m72)
open PrimitiveGate (T TOFF)
set_option Elab.async true
set_option maxRecDepth 200000
set_option exponentiation.threshold 8192


noncomputable section
set_option exponentiation.threshold 256
namespace QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2

open Operator QProg Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (ditePos diteNeg)
theorem coul18K2Stagek123_disj {n : ℕ}
    {wG wScr wNN : Wire n} {r : QRegister (54 + 123) n} {rC13 : QRegister 13 n}
    (hGR : ∀ i, wG ≠ r i) (hSR : ∀ i, wScr ≠ r i) (hNR : ∀ i, wNN ≠ r i)
    (hSN : wScr ≠ wNN) (hRC : r.DisjointWires rC13) :
    let rOut22 := rOut22k123 r; let rPers18 := rPers18k123 r; let rPool := rPool72k123 r
    let rPad54 := rPad54OfPoolM54 (by decide : 54 ≤ 72) rPool
    rOut22.DisjointWires rC13 ∧ rOut22.DisjointWires rPers18 ∧ rOut22.DisjointWires rPad54 ∧
    rC13.DisjointWires rPers18 ∧ rC13.DisjointWires rPad54 ∧ rPers18.DisjointWires rPad54 ∧
    ScrGGatedCoreDisj wG wScr wNN (rIdx7Of22 rOut22) (rK4Of22 rOut22)
        (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18) (rY36Of r) rPool := by
  dsimp only
  have rInj {i j : Fin (54 + 123)} (e : r i = r j) : i.val = j.val :=
      congrArg Fin.val (r.wires.injective e)
  have hOutR (j : Fin 22) : ∃ idx : Fin (54 + 123), rOut22k123 r j = r idx ∧ (idx.val = 17 ∨ 155 ≤
      idx.val ∧ idx.val < 176) := by
    change ∃ idx, fOut22k123 r j = r idx ∧ _; dsimp only [fOut22k123]
    split_ifs with hj
    · refine ⟨⟨155 + j.val, by omega⟩, rfl, Or.inr ⟨?_, ?_⟩⟩ <;> ((try dsimp only); omega)
    · exact ⟨⟨17, by decide⟩, rfl, Or.inl rfl⟩
  have hPersR (q : Fin 18) : ∃ idx : Fin (54 + 123), rPers18k123 r q = r idx ∧ (idx.val = 176 ∨
      126 ≤ idx.val ∧ idx.val < 143) := by
    change ∃ idx, fPers18k123 r q = r idx ∧ _; dsimp only [fPers18k123]
    split_ifs with hq
    · refine ⟨⟨126 + q.val, by omega⟩, rfl, Or.inr ⟨?_, ?_⟩⟩ <;> ((try dsimp only); omega)
    · exact ⟨⟨176, by decide⟩, rfl, Or.inl rfl⟩
  have hPoolR (u : Fin 72) : ∃ idx : Fin (54 + 123), rPool72k123 r u = r idx ∧ idx.val = 54 +
      u.val :=
      ⟨⟨54 + u.val, by omega⟩, congrArg r.wires (Fin.ext (by dsimp [rPool72k123, rPoolOf])), rfl⟩
  have hYR (b : Fin 36) : ∃ idx : Fin (54 + 123), rY36Of r b = r idx ∧ idx.val = 18 + b.val :=
      ⟨⟨18 + b.val, by omega⟩, congrArg r.wires (Fin.ext (by dsimp [rY36Of])), rfl⟩
  have neR {w₁ w₂ : Wire n} {P Q : Fin (54 + 123) → Prop} (h1 : ∃ i, w₁ = r i ∧ P i)
      (h2 : ∃ j, w₂ = r j ∧ Q j) (hd : ∀ i j, P i → Q j → i.val ≠ j.val) : w₁ ≠ w₂ :=
    fun e ↦ h1.elim fun i hi ↦ h2.elim fun j hj ↦
        hd i j hi.2 hj.2 (rInj (hi.1.symm.trans (e.trans hj.1)))
  obtain ⟨hOutNotPers, hOutNotPool, hPersNotPool, hOutNotY36⟩ :
      (∀ j q, rOut22k123 r j ≠ rPers18k123 r q) ∧ (∀ j (u : Fin 72), rOut22k123 r j ≠
          rPool72k123 r u) ∧
      (∀ q (u : Fin 72), rPers18k123 r q ≠ rPool72k123 r u) ∧ (∀ j (b : Fin 36), rOut22k123 r j ≠
          rY36Of r b) :=
    ⟨fun j q ↦ neR (hOutR j) (hPersR q) fun _ _ _ _ ↦ by omega, fun j u ↦ neR (hOutR j)
        (hPoolR u) fun _ _ _ _ ↦ by omega,
     fun q u ↦ neR (hPersR q) (hPoolR u) fun _ _ _ _ ↦ by omega, fun j b ↦
         neR (hOutR j) (hYR b) fun _ _ _ _ ↦ by omega⟩
  have hYP : (rY36Of r).DisjointWires (rPool72k123 r) := disj_of_ne fun b u ↦
      neR (hYR b) (hPoolR u) fun _ _ _ _ ↦ by omega
  have hwNotOut (w) (hw : ∀ i, w ≠ r i) (j) : w ≠ rOut22k123 r j := fun e ↦
      (hOutR j).elim fun idx h ↦ hw idx (e.trans h.1)
  have hwNotPers (w) (hw : ∀ i, w ≠ r i) (q) : w ≠ rPers18k123 r q := fun e ↦
      (hPersR q).elim fun idx h ↦ hw idx (e.trans h.1)
  refine ⟨disj_of_ne fun j c e ↦ (hOutR j).elim fun idx h ↦ disj_ne hRC idx c (h.1.symm.trans e),
      disj_of_ne hOutNotPers,
    disj_of_ne fun j u ↦ hOutNotPool j ⟨u.val, by omega⟩, disj_of_ne fun c q e ↦
        (hPersR q).elim fun idx h ↦ disj_ne hRC idx c (h.1.symm.trans e.symm),
    disj_of_ne fun c _ e ↦ disj_ne hRC _ c e.symm, disj_of_ne fun q u ↦
        hPersNotPool q ⟨u.val, by omega⟩,
    ⟨⟨fun _ ↦ hwNotOut wG hGR _, fun _ ↦ hwNotOut wG hGR _, fun _ ↦ hwNotPers wG hGR _, fun _ ↦
        hGR _, fun _ ↦ hGR _,
      disj_of_ne fun a b e ↦
          (fun hv ↦ by dsimp only [rIdx7Of22, rK4Of22] at hv; omega)
          (congrArg Fin.val ((rOut22k123 r).wires.injective e)),
      disj_of_ne fun _ _ ↦ hOutNotPers _ _, disj_of_ne fun _ _ ↦
          hOutNotY36 _ _, disj_of_ne fun _ _ ↦ hOutNotPool _ _,
      disj_of_ne fun _ _ ↦ hOutNotPers _ _, disj_of_ne fun _ b ↦
          hOutNotY36 _ b, disj_of_ne fun _ u ↦ hOutNotPool _ u,
      disj_of_ne fun _ b ↦ neR (hPersR _) (hYR b) fun _ _ _ _ ↦ by omega, disj_of_ne fun _ _ ↦
          hPersNotPool _ _, hYP⟩,
     ⟨hSN, fun _ ↦ hwNotOut wScr hSR _, fun _ ↦ hSR _, fun _ ↦ hSR _, fun _ ↦ hwNotOut wNN hNR _,
         fun _ ↦ hNR _, fun _ ↦ hNR _,
      disj_of_ne fun _ b ↦ hOutNotY36 _ b, disj_of_ne fun _ u ↦ hOutNotPool _ u, hYP⟩⟩⟩

def wrapCoulOWScr13_coulMid_k123 {Var : Type} [Fintype Var] [DecidableEq Var] {kMid tInner n : ℕ}
    (pkgInner : CoulM72Mid36Opt.CoulInnerCorePkgM72 kMid tInner) (v : Var) (wG wScr wNN : Wire n)
    (r : QRegister (54 + 123) n) (rC13 : QRegister 13 n) (mid : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  if hG : disjCoin13Bool wG r rC13 = true then
    if hS : disjCoin13Bool wScr r rC13 = true then
      if hN : disjCoin13Bool wNN r rC13 = true then
        if hSN : wScr ≠ wNN then
          let hdG := disjCoin13Bool_sound hG; let hdS := disjCoin13Bool_sound hS;
          let hdN := disjCoin13Bool_sound hN
          let w16 := r ⟨16, by decide⟩
          let w17 := r ⟨17, by decide⟩
          let w176 := r ⟨176, by decide⟩
          let h16_17 : w16 ≠ w17 := fun e ↦ by
            have hv := congrArg Fin.val (r.wires.injective e); dsimp at hv; omega
          let h17_176 : w17 ≠ w176 := fun e ↦ by
            have hv := congrArg Fin.val (r.wires.injective e); dsimp at hv; omega
          let rOut22 := rOut22k123 r; let rPers18 := rPers18k123 r; let rPool := rPool72k123 r;
          let hh := coul18K2Stagek123_disj hdG.1 hdS.1 hdN.1 hSN hdN.2.2;
          let midRestore :=
              DynamicCircuit.seq (.circuit (.CNOT w16 w17 h16_17))
              (.seq mid (.circuit (.CNOT w16 w17 h16_17)))
          let core :=
              wrapDynOnReg v (rCoul18K2Sub63 hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
              hh.2.2.2.2.2.1) (decodePrimTree 95 coul18K2Sub63Tree)
              (pkgInner.pInner v wG wScr wNN (rIdx7Of22 rOut22) (rK4Of22 rOut22)
              (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18)
              (rY36Of r) rPool hh.2.2.2.2.2.2 midRestore)
          pDomSplitPers12_168 v wNN r hdN.1
            (.seq (.circuit (.CNOT w16 w17 h16_17))
              (.seq (.circuit (.CNOT w17 w176 h17_176))
                (.seq core
                  (.seq (.circuit (.CNOT w17 w176 h17_176))
                    (.circuit (.CNOT w16 w17 h16_17))))))
        else mid
      else mid
    else mid
  else mid

attribute [local irreducible] coul18K2Sub63Tree pDomSplitPers12_168 in
theorem wrapCoulOWScr13_coulMid_k123_counts_wires {Var : Type} [Fintype Var] [DecidableEq Var]
    {kMid tInner n : ℕ} {S : Wire n → Prop}
    (pkgInner : CoulM72Mid36Opt.CoulInnerCorePkgM72 kMid tInner) (v : Var) (wG wScr wNN : Wire n)
    (r : QRegister (54 + 123) n) (rC13 : QRegister 13 n) (hGR : ∀ i, wG ≠ r i)
    (hGC : ∀ j, wG ≠ rC13 j) (hSR : ∀ i, wScr ≠ r i) (hSC : ∀ j, wScr ≠ rC13 j)
    (hNR : ∀ i, wNN ≠ r i) (hNC : ∀ j, wNN ≠ rC13 j) (hSN : wScr ≠ wNN) (hRC : r.DisjointWires rC13)
    (hGS : S wG) (hSS : S wScr) (hNS : S wNN) (hRS : ∀ i, S (r i)) (hCS : ∀ j, S (rC13 j))
    (mid : DynamicCircuit Var n) :
    (wrapCoulOWScr13_coulMid_k123 pkgInner v wG wScr wNN r rC13 mid).count .T = 168 + 72 + tInner +
    mid.count .T ∧ (wrapCoulOWScr13_coulMid_k123 pkgInner v wG wScr wNN r rC13 mid).count .TOFF =
    mid.count .TOFF ∧ (DynWires S mid →
    DynWires S (wrapCoulOWScr13_coulMid_k123 pkgInner v wG wScr wNN r rC13 mid)) := by
  have hbG := disjCoin13Bool_eq_true hGR hGC hRC; have hbS := disjCoin13Bool_eq_true hSR hSC hRC;
  have hbN :=
      disjCoin13Bool_eq_true hNR hNC hRC; unfold wrapCoulOWScr13_coulMid_k123; rw [ditePos hbG,
      ditePos hbS, ditePos hbN, ditePos hSN]
  obtain ⟨hdG, hdS, hdN⟩ : _ ∧ _ ∧ _ :=
      ⟨disjCoin13Bool_sound hbG, disjCoin13Bool_sound hbS, disjCoin13Bool_sound hbN⟩
  let w16 := r ⟨16, by decide⟩
  let w17 := r ⟨17, by decide⟩
  let w176 := r ⟨176, by decide⟩
  obtain ⟨h16_17, h17_176⟩ : w16 ≠ w17 ∧ w17 ≠ w176 :=
    ⟨fun e ↦ absurd (congrArg Fin.val (r.wires.injective e)) (by decide),
     fun e ↦ absurd (congrArg Fin.val (r.wires.injective e)) (by decide)⟩
  obtain ⟨c16, c176⟩ : _ ∧ _ := ⟨cnot_counts_wires (Var := Var) w16 w17 h16_17 (hRS _) (hRS _),
    cnot_counts_wires (Var := Var) w17 w176 h17_176 (hRS _) (hRS _)⟩
  let rOut22 := rOut22k123 r; let rPers18 := rPers18k123 r; let rPool := rPool72k123 r
  let rPad54 := rPad54OfPoolM54 (by decide : 54 ≤ 72) rPool
  let hh := coul18K2Stagek123_disj hdG.1 hdS.1 hdN.1 hSN hdN.2.2;
  let rCLB := rCoul18K2Sub63 hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1
  have hrOutS : ∀ j : Fin 22, S (rOut22 j) := fun j ↦ by
    change S (fOut22k123 r j); dsimp only [fOut22k123]; split_ifs <;> exact hRS _
  have hrPersS : ∀ q : Fin 18, S (rPers18 q) := fun q ↦ by
    change S (fPers18k123 r q); dsimp only [fPers18k123]; split_ifs <;> exact hRS _
  let midRestore :=
      DynamicCircuit.seq (.circuit (.CNOT w16 w17 h16_17))
      (.seq mid (.circuit (.CNOT w16 w17 h16_17)))
  obtain ⟨tI, fI, wI⟩ :=
      pkgInner.counts_wires v wG wScr wNN (rIdx7Of22 rOut22) (rK4Of22 rOut22)
      (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18)
      (rY36Of r) rPool hh.2.2.2.2.2.2 hGS hSS hNS (fun _ ↦ hrOutS _) (fun _ ↦ hrOutS _)
      (fun _ ↦ hrPersS _) (fun _ ↦ hRS _) (fun _ ↦ hRS _) midRestore
  obtain ⟨cnotT, cnotF⟩ : (∀ {c t : Wire n} (h : c ≠ t), (Circuit.CNOT c t h).count .T = 0) ∧
      (∀ {c t : Wire n} (h : c ≠ t), (Circuit.CNOT c t h).count .TOFF = 0) :=
      ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  let inner :=
      pkgInner.pInner v wG wScr wNN (rIdx7Of22 rOut22) (rK4Of22 rOut22)
      (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18)
      (rY36Of r) rPool hh.2.2.2.2.2.2 midRestore
  let cpC := decodePrimTree 95 coul18K2Sub63Tree
  have hAnd18 : cpC.numAnd = 18 :=
    (decodePrimTree_spec 95 coul18K2Sub63Tree 0 coul18K2SMask).2.2.trans coul18K2Sub63Tree_check.2
  obtain ⟨tC, fC⟩ := counts_wrapDynOnReg v rCLB cpC inner
  have hrCLBS : ∀ u, S (rCLB u) := fun u ↦ by
    change S (fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 u); dsimp only [fCoul18K2Sub63]
    split_ifs <;> [exact hrOutS _; exact hCS _; exact hrPersS _; exact hRS _]
  obtain ⟨tO, fO, wO⟩ := pDomSplitPers12_168_counts_wires v wNN r hdN.1 hNS hRS _
  refine ⟨?_, ?_, fun hm ↦ wO ⟨c16.2.2, c176.2.2,
    dynWires_wrapDynOnReg v rCLB hrCLBS cpC (wI ⟨c16.2.2, hm, c16.2.2⟩), c176.2.2, c16.2.2⟩⟩
  · rw [tO]
    dsimp only [DynamicCircuit.count]
    rw [cnotT, cnotT, tC, hAnd18, tI]
    dsimp only [midRestore, DynamicCircuit.count]
    simp only [cnotT]
    omega
  · rw [fO]
    dsimp only [DynamicCircuit.count]
    rw [cnotF, cnotF, fC, fI]
    dsimp only [midRestore, DynamicCircuit.count]
    simp only [cnotF]
    omega

attribute [local irreducible] coul18K2Sub63Tree pDomSplitPers12_168 FineLegendre.mkKetOpW
  EvenOctB70.evenOctIdxT10K PopBernstein.popBernJ PopBernstein.y36PopBernNoClamp popBernJK2
      coin33ProxyOfJK2 o9Of13 in
theorem wrapCoulOWScr13_coulMid_k123_step2_pers {Var : Type} [Fintype Var] [DecidableEq Var]
    {kMid tInner W n : ℕ} [NeZero (2 ^ n)]
    (pkgInner : PhotochemistrySolution.CoulM72Mid36Opt.CoulInnerCorePkgM72 kMid tInner)
    (v : Var) (rWork : QRegister W n) (wG wScr wNN : Wire n)
    (r : QRegister (54 + 123) n) (rC13 : QRegister 13 n)
    (hGR : ∀ i, wG ≠ r i) (hGC : ∀ j, wG ≠ rC13 j)
    (hSR : ∀ i, wScr ≠ r i) (hSC : ∀ j, wScr ≠ rC13 j)
    (hNR : ∀ i, wNN ≠ r i) (hNC : ∀ j, wNN ≠ rC13 j)
    (hSN : wScr ≠ wNN) (hRC : r.DisjointWires rC13)
    (mid : DynamicCircuit Var n) (st₁ st₂ : BitAssignment n → BitAssignment n)
    (ph₁ ph₂ : BitAssignment n → ZMod 2)
    (hd2Le : ∀ δ, (∀ k, δ (rWork k) = 0) →
      natOfZModBits 18 (fun b ↦ st₁ δ (r ⟨b.val, potGen_d2_lt 123 b⟩)) ≤ 195075)
    (hValid0 : ∀ δ, (∀ k, δ (rWork k) = 0) → st₁ δ wScr = 0 → st₁ δ wNN = 0)
    (hY0 : ∀ δ (b : Fin 36), (∀ k, δ (rWork k) = 0) →
      st₁ δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) = 0 ∧
      st₂ δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) = 0)
    (hK0 : ∀ δ (u : Fin 123), (∀ k, δ (rWork k) = 0) →
      st₁ δ (r ⟨54 + u.val, potGen_k_lt 123 u⟩) = 0 ∧
      st₂ δ (r ⟨54 + u.val, potGen_k_lt 123 u⟩) = 0)
    (hAgree : ∀ δ, (∀ k, δ (rWork k) = 0) →
      st₂ δ wG = st₁ δ wG ∧ st₂ δ wScr = st₁ δ wScr ∧ st₂ δ wNN = st₁ δ wNN ∧
      (∀ b : Fin 18, st₂ δ (r ⟨b.val, potGen_d2_lt 123 b⟩) =
        st₁ δ (r ⟨b.val, potGen_d2_lt 123 b⟩)) ∧
      (∀ j, st₂ δ (rC13 j) = st₁ δ (rC13 j)))
    (hMidCB : ∀ m₁ m₂ : BitAssignment n → BitAssignment n,
      (∀ δ w, (∀ b : Fin 36, w ≠ r ⟨18 + b.val, potGen_y36_lt 123 b⟩) →
        (∀ u : Fin 123, w ≠ r ⟨54 + u.val, potGen_k_lt 123 u⟩) →
        m₁ δ w = st₁ δ w ∧ m₂ δ w = st₂ δ w) →
      (∀ δ, (∀ k, δ (rWork k) = 0) →
        let yV :=
            if st₁ δ wG == 1 then ySampleK2 word512DualLegLo6 (st₁ δ wNN == 1)
            (natOfZModBits 18 (fun b ↦ st₁ δ (r ⟨b.val, potGen_d2_lt 123 b⟩)))
            (w11OfReg13 rC13 (st₁ δ)) (o9Of13 (x13OfReg13 rC13 (st₁ δ)))
        else 0
        let sh1 := if (st₁ δ wScr == 1) && !(st₁ δ wNN == 1) then 1 else 0
        natOfZModBits 36 (fun b ↦ m₁ δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩)) / 8 = (yV >>> sh1) /
            8 ∧
        (∀ b : Fin 36,
          m₂ δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) =
            m₁ δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩)) ∧
        (st₁ δ wG = 0 →
          ∀ b : Fin 36, m₁ δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) = 0)) →
      (∀ δ (j : Fin kMid), (∀ k, δ (rWork k) = 0) →
        m₁ δ (r ⟨54 + j.val,
            potGen_mid_lt (Nat.le_trans pkgInner.hMidLE (by decide : 72 ≤ 123)) j⟩) = 0 ∧
        m₂ δ (r ⟨54 + j.val,
            potGen_mid_lt (Nat.le_trans pkgInner.hMidLE (by decide : 72 ≤ 123)) j⟩) = 0) →
      (∀ δ (u : Fin 123), (∀ k, δ (rWork k) = 0) →
        m₂ δ (r ⟨54 + u.val, potGen_k_lt 123 u⟩) =
          m₁ δ (r ⟨54 + u.val, potGen_k_lt 123 u⟩)) →
      SubspaceStep (mkKetOpW rWork m₁ ph₁) (mkKetOpW rWork m₂ ph₂) mid) :
    SubspaceStep (mkKetOpW rWork st₁ ph₁) (mkKetOpW rWork st₂ ph₂)
      (wrapCoulOWScr13_coulMid_k123 pkgInner v wG wScr wNN r rC13 mid) := by
  have hbG := disjCoin13Bool_eq_true hGR hGC hRC; have hbS := disjCoin13Bool_eq_true hSR hSC hRC;
  have hbN :=
      disjCoin13Bool_eq_true hNR hNC hRC; unfold wrapCoulOWScr13_coulMid_k123; rw [ditePos hbG,
      ditePos hbS, ditePos hbN, ditePos hSN]
  obtain ⟨hdG, hdS, hdN⟩ : _ ∧ _ ∧ _ :=
      ⟨disjCoin13Bool_sound hbG, disjCoin13Bool_sound hbS, disjCoin13Bool_sound hbN⟩
  let rTop := rTop22Hi (by decide : 90 ≤ 123) r
  let rP12 := rPers12Of r
  let w16 := r ⟨16, by decide⟩
  let w17 := r ⟨17, by decide⟩
  let w176 := r ⟨176, by decide⟩
  have rInj {i j : Fin (54 + 123)} (e : r i = r j) : i.val = j.val :=
      congrArg Fin.val (r.wires.injective e)
  have z2_cancel (a b : ZMod 2) : a + b + b = a := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have rNe {i j : Fin (54 + 123)} (h : i.val ≠ j.val) : r i ≠ r j := fun e ↦ h (rInj e)
  obtain ⟨h16_17, h17_176, h16_176⟩ : w16 ≠ w17 ∧ w17 ≠ w176 ∧ w16 ≠ w176 :=
      ⟨rNe (by decide), rNe (by decide), rNe (by decide)⟩
  let rOut22 := rOut22k123 r; let rPers18 := rPers18k123 r; let rY36 := rY36Of r;
  let rPool := rPool72k123 r
  let rPad54 := rPad54OfPoolM54 (by decide : 54 ≤ 72) rPool
  let hh := coul18K2Stagek123_disj hdG.1 hdS.1 hdN.1 hSN hdN.2.2;
  let rCLB := rCoul18K2Sub63 hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1;
  let cpC := decodePrimTree 95 coul18K2Sub63Tree
  rcases decodePrimTree_spec 95 coul18K2Sub63Tree 0 coul18K2SMask with ⟨hvC, _, haC⟩
  let isNNFn : BitAssignment n → Bool := fun δ ↦ st₁ δ wNN == 1
  let d2Fn : BitAssignment n → ℕ := fun δ ↦
      natOfZModBits 18 (fun b ↦ st₁ δ (r ⟨b.val, potGen_d2_lt 123 b⟩))
  have hd2Lt : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → d2Fn δ < 262144 := fun δ hz ↦
      d2_lt_262144 (hd2Le δ hz)
  exact pDomSplitPers12_168_step_cb2 v rWork wNN r hdN.1 _ st₁ st₂ ph₁ ph₂ hd2Le
    (fun δ hz ↦ (hAgree δ hz).2.2.1) (fun δ b hz ↦ (hAgree δ hz).2.2.2.1 b)
        (fun δ b hz ↦ (hY0 δ b hz).1) (fun δ b hz ↦ (hY0 δ b hz).2)
    (fun δ u hz ↦ (hK0 δ u hz).1)
        (fun δ u hz ↦
        (hK0 δ u hz).2) fun stDomPre stDomPost hPresDPre hPresDPost hOutDPre hOutDEq hPers12DEq ↦ by
      have hDomLt143 {idx : Fin (54 + 123)} (h : idx.val < 143) (δ : BitAssignment n) :
          stDomPre δ (r idx) = st₁ δ (r idx) ∧ stDomPost δ (r idx) = st₂ δ (r idx) :=
        ⟨hPresDPre δ (r idx) (fun _ e ↦ (fun hv ↦ by dsimp only [rTop, rTop22Hi] at hv; omega)
            (rInj e)) (fun _ e ↦ (fun hv ↦ by dsimp only [rP12, rPers12Of] at hv; omega)
            (rInj e)),
         hPresDPost δ (r idx) (fun _ e ↦ (fun hv ↦ by dsimp only [rTop, rTop22Hi] at hv; omega)
             (rInj e)) (fun _ e ↦ (fun hv ↦ by dsimp only [rP12, rPers12Of] at hv; omega)
             (rInj e))⟩
      obtain ⟨h16Pre, h16Post, h17Pre, h17Post⟩ : (∀ δ, stDomPre δ w16 = st₁ δ w16) ∧
          (∀ δ, stDomPost δ w16 = st₂ δ w16) ∧ (∀ δ, stDomPre δ w17 = st₁ δ w17) ∧
          (∀ δ, stDomPost δ w17 = st₂ δ w17) :=
        ⟨fun δ ↦ (hDomLt143 (by decide) δ).1, fun δ ↦ (hDomLt143 (by decide) δ).2, fun δ ↦
            (hDomLt143 (by decide) δ).1, fun δ ↦ (hDomLt143 (by decide) δ).2⟩
      have hTop21Eq : rTop ⟨21, by decide⟩ = w176 := congrArg r.wires (Fin.ext rfl)
      have hDom21Pre (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) : stDomPre δ w176 = st₁ δ w17 +
          st₁ δ w16 := by
        rw [← hTop21Eq, hOutDPre δ ⟨21, by decide⟩ hz, dom22Bit21_eq_d2_xor (isNNFn δ)
            (hd2Le δ hz), ← zmod2_dom21_xor_eq]
        exact congrArg₂ (· + ·) (natOfZModBits18_bit (fun b ↦ st₁ δ (r ⟨b.val, potGen_d2_lt 123 b⟩))
            ⟨17, by decide⟩) (natOfZModBits18_bit (fun b ↦ st₁ δ (r ⟨b.val, potGen_d2_lt 123 b⟩))
            ⟨16, by decide⟩)
      have hDom21Post (δ) (hz : ∀ k : Fin W, δ (rWork k) = 0) : stDomPost δ w176 = st₂ δ w17 +
          st₂ δ w16 := by
        rw [← hTop21Eq, hOutDEq δ ⟨21, by decide⟩ hz, hTop21Eq, hDom21Pre δ hz,
            (hAgree δ hz).2.2.2.1 ⟨17, by decide⟩, (hAgree δ hz).2.2.2.1 ⟨16, by decide⟩]
      let stDPre : BitAssignment n → BitAssignment n := fun δ ↦
          Function.update (Function.update (stDomPre δ) w17 (stDomPre δ w17 +
          stDomPre δ w16)) w176 0
      let stDPost : BitAssignment n → BitAssignment n := fun δ ↦
          Function.update (Function.update (stDomPost δ) w17 (stDomPost δ w17 +
          stDomPost δ w16)) w176 0
      let std1 := fun δ ↦ Function.update (stDomPre δ) w17 (stDomPre δ w17 + stDomPre δ w16)
      have sd2' : SubspaceStep (Var := Var) (mkKetOpW rWork std1 ph₁) (mkKetOpW rWork stDPre ph₁)
          (.circuit (.CNOT w17 w176 h17_176)) := by
        refine subspaceStep_of_eq_post (subspaceStep_cnot_mkKetOpW (Var :=
            Var) rWork w17 w176 h17_176 std1 ph₁)
            (mkKetOpW_congr rWork (fun δ hz ↦ funext fun w ↦ ?_) (fun _ _ ↦ rfl))
        dsimp only [std1, stDPre]; simp only [Function.update_apply, h17_176.symm, ↓reduceIte]
        rcases eq_or_ne w w176 with rfl | hw <;> simp only [*, ↓reduceIte, hDom21Pre δ hz, h17Pre δ,
            h16Pre δ, CharTwo.add_self_eq_zero]
      let sbd1 := fun δ ↦ Function.update (stDPost δ) w176 (stDPost δ w176 + stDPost δ w17)
      have hPostDom2 : SubspaceStep (Var := Var) (mkKetOpW rWork stDPost ph₂)
          (mkKetOpW rWork stDomPost ph₂) (.seq (.circuit (.CNOT w17 w176 h17_176))
          (.circuit (.CNOT w16 w17 h16_17))) := by
        refine subspaceStep_of_eq_post (subspaceStep_seq_u (subspaceStep_cnot_mkKetOpW (Var :=
            Var) rWork w17 w176 h17_176 stDPost ph₂)
            (subspaceStep_cnot_mkKetOpW (Var := Var) rWork w16 w17 h16_17 sbd1 ph₂))
          (mkKetOpW_congr rWork (fun δ hz ↦ funext fun w ↦ ?_) (fun _ _ ↦ rfl))
        dsimp only [sbd1, stDPost];
        simp only [Function.update_apply, h17_176, h16_17, h16_176, ↓reduceIte]
        rcases eq_or_ne w w17 with rfl | hw17
        · simpa only [↓reduceIte] using z2_cancel _ _
        · rcases eq_or_ne w w176 with rfl | hw176 <;> simp only [*, ↓reduceIte, zero_add,
              hDom21Post δ hz, h17Post δ, h16Post δ]
      have hDPreOut : ∀ δ w, w ≠ w17 → w ≠ w176 → stDPre δ w = stDomPre δ w := fun δ w a b ↦ by
        dsimp only [stDPre]; simp only [Function.update_apply, b, a, ↓reduceIte]
      have hDPostOut : ∀ δ w, w ≠ w17 → w ≠ w176 → stDPost δ w = stDomPost δ w := fun δ w a b ↦ by
        dsimp only [stDPost]; simp only [Function.update_apply, b, a, ↓reduceIte]
      have hDLt143 {idx : Fin (54 + 123)} (h : idx.val < 143) (h17 : idx.val ≠ 17)
          (δ : BitAssignment n) : stDPre δ (r idx) = st₁ δ (r idx) ∧ stDPost δ (r idx) =
          st₂ δ (r idx) :=
        ⟨(hDPreOut δ _ (rNe h17) (rNe (show idx.val ≠ 176 by omega))).trans (hDomLt143 h δ).1,
         (hDPostOut δ _ (rNe h17) (rNe (show idx.val ≠ 176 by omega))).trans (hDomLt143 h δ).2⟩
      have hC13EqD (δ) (j : Fin 13) : stDPre δ (rC13 j) = st₁ δ (rC13 j) ∧ stDPost δ (rC13 j) =
          st₂ δ (rC13 j) :=
        ⟨(hDPreOut δ _ (fun e ↦ disj_ne hRC _ j e.symm)
            (fun e ↦ disj_ne hRC _ j e.symm)).trans (hPresDPre δ _ (fun _ e ↦
            disj_ne hdN.2.2 _ j e.symm) (fun _ e ↦ disj_ne hRC _ j e.symm)),
         (hDPostOut δ _ (fun e ↦ disj_ne hRC _ j e.symm)
             (fun e ↦ disj_ne hRC _ j e.symm)).trans (hPresDPost δ _ (fun _ e ↦
             disj_ne hdN.2.2 _ j e.symm) (fun _ e ↦ disj_ne hRC _ j e.symm))⟩
      have hOutkPre (δ) (j : Fin 22) (hz : ∀ k : Fin W, δ (rWork k) = 0) : stDPre δ (rOut22 j) =
          if dom22Bit (evenOctIdxT10K (isNNFn δ) (d2Fn δ)) j then 1 else 0 := by
        change stDPre δ (fOut22k123 r j) = _; dsimp only [fOut22k123]
        by_cases hj21 : j.val < 21
        · rw [ditePos hj21, hDPreOut δ _ (rNe (by (try dsimp only); omega))
              (rNe (by (try dsimp only); omega)), show r ⟨155 + j.val, by omega⟩ =
              rTop j from congrArg r.wires (Fin.ext (by (try dsimp [rTop, rTop22Hi]); omega))]
          exact hOutDPre δ j hz
        · rw [diteNeg hj21, show j = ⟨21, by decide⟩ from Fin.ext (by (try dsimp only); omega)]
          change stDPre δ w17 = _
          dsimp only [stDPre]
          simp only [Function.update_apply, h17_176, ↓reduceIte]
          rw [h17Pre δ, h16Pre δ, ← hDom21Pre δ hz, ← hTop21Eq]
          exact hOutDPre δ ⟨21, by decide⟩ hz
      have hOutkEq (δ) (j : Fin 22) (hz : ∀ k : Fin W, δ (rWork k) = 0) : stDPost δ (rOut22 j) =
          stDPre δ (rOut22 j) := by
        change stDPost δ (fOut22k123 r j) = stDPre δ (fOut22k123 r j); dsimp only [fOut22k123]
        split_ifs with hj21
        · rw [hDPostOut δ _ (rNe (by (try dsimp only); omega))
              (rNe (by (try dsimp only); omega)),
              hDPreOut δ _ (rNe (by (try dsimp only); omega))
              (rNe (by (try dsimp only); omega)),
              show r ⟨155 + j.val, by omega⟩ =
                  rTop j from congrArg r.wires
                  (Fin.ext (by (try dsimp [rTop, rTop22Hi]); omega))]
          exact hOutDEq δ j hz
        · dsimp only [stDPost, stDPre]; simp only [Function.update_apply]
          rw [h17Post δ, h16Post δ, h17Pre δ, h16Pre δ, (hAgree δ hz).2.2.2.1 ⟨17, by decide⟩,
              (hAgree δ hz).2.2.2.1 ⟨16, by decide⟩]
      have hPers0 (δ) (q : Fin 18) (hz : ∀ k : Fin W, δ (rWork k) = 0) : stDPre δ (rPers18 q) = 0 ∧
          stDPost δ (rPers18 q) = 0 := by
        change stDPre δ (fPers18k123 r q) = 0 ∧ stDPost δ (fPers18k123 r q) = 0
        dsimp only [fPers18k123]
        by_cases hq17 : q.val < 17
        · rw [ditePos hq17]
          obtain ⟨e1, e2⟩ :=
              hDLt143 (idx := ⟨126 + q.val, by omega⟩) (by (try dsimp only); omega)
              (by (try dsimp only); omega) δ
          have hIdx : r ⟨126 + q.val, by omega⟩ = r ⟨54 + (72 + q.val), potGen_k_lt 123 ⟨72 + q.val,
              by omega⟩⟩ := congrArg r.wires (Fin.ext (by (try dsimp only); omega))
          exact ⟨e1.trans ((congrArg (st₁ δ) hIdx).trans (hK0 δ ⟨72 + q.val, by omega⟩ hz).1),
              e2.trans ((congrArg (st₂ δ) hIdx).trans (hK0 δ ⟨72 + q.val, by omega⟩ hz).2)⟩
        · rw [diteNeg hq17]
          exact ⟨Function.update_self _ _ _, Function.update_self _ _ _⟩
      have hPoolEq (u : Fin 72) : rPool u = r ⟨54 + u.val, potGen_k_lt 123 ⟨u.val, by omega⟩⟩ :=
          congrArg r.wires (Fin.ext (by dsimp only [rPool, rPool72k123, rPoolOf]))
      have hPool0 (δ) (u : Fin 72) (hz : ∀ k : Fin W, δ (rWork k) = 0) : stDPre δ (rPool u) = 0 ∧
          stDPost δ (rPool u) = 0 := by
        obtain ⟨e1, e2⟩ :=
            hDLt143 (idx := ⟨54 + u.val, potGen_k_lt 123 ⟨u.val, by omega⟩⟩)
            (by (try dsimp only); omega) (by (try dsimp only); omega) δ
        exact ⟨(congrArg (stDPre δ) (hPoolEq u)).trans (e1.trans (hK0 δ ⟨u.val, by omega⟩ hz).1),
            (congrArg (stDPost δ) (hPoolEq u)).trans (e2.trans (hK0 δ ⟨u.val, by omega⟩ hz).2)⟩
      set stCompPre := fun δ ↦ stepCB rCLB cpC.fwdBits (stDPre δ)
      set stCompPost := fun δ ↦ stepCB rCLB cpC.fwdBits (stDPost δ)
      have hPresCPre : ∀ δ w, (∀ q : Fin 18, w ≠ rPers18 q) → stCompPre δ w = stDPre δ w :=
          fun δ w hw ↦
          stepCB_coul18K2Sub63_pres_nonPers hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
          hh.2.2.2.2.2.1 (stDPre δ) w hw
      have hPresCPost : ∀ δ w, (∀ q : Fin 18, w ≠ rPers18 q) → stCompPost δ w = stDPost δ w :=
          fun δ w hw ↦
          stepCB_coul18K2Sub63_pres_nonPers hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
          hh.2.2.2.2.2.1 (stDPost δ) w hw
      have hWComp {w : Wire n} (hw : ∀ i, w ≠ r i) (δ : BitAssignment n) : stCompPre δ w = st₁ δ w ∧
          stCompPost δ w = st₂ δ w := by
        have hnP (q : Fin 18) : w ≠ rPers18 q := fun e ↦ by
          change w = fPers18k123 r q at e
          dsimp only [fPers18k123] at e
          split_ifs at e <;> exact hw _ e
        exact ⟨(hPresCPre δ w hnP).trans ((hDPreOut δ w (hw _)
            (hw _)).trans (hPresDPre δ w (fun _ e ↦ hw _ e) (fun _ e ↦ hw _ e))),
          (hPresCPost δ w hnP).trans ((hDPostOut δ w (hw _) (hw _)).trans (hPresDPost δ w (fun _ e ↦
              hw _ e) (fun _ e ↦ hw _ e)))⟩
      let cFakeFn : BitAssignment n → Fin 3 → Fin 2048 := fun δ ↦
          coin33ProxyOfJK2 (popBernJK2 (t11OfParts (evenOctIdxT10K (stCompPre δ wNN == 1) (d2Fn δ)))
          (w11OfReg13 rC13 (stDPre δ)) (o9Of13 (x13OfReg13 rC13 (stDPre δ))))
      have hJ2Pre (δ) (q : Fin 2) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
          let p := evenOctIdxT10K (stCompPre δ wNN == 1) (d2Fn δ)
          stCompPre δ (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18 q) =
              if (popBernJ (t11OfParts p) (cFakeFn δ)).testBit q.val then 1 else 0 := by
        dsimp only [cFakeFn]
        have ht11Lt : t11OfParts (evenOctIdxT10K (isNNFn δ) (d2Fn δ)) < 2048 :=
            (out22_t11_bits rOut22 (stDPre δ) (isNNFn δ) (hd2Lt δ hz) (fun j ↦ hOutkPre δ j hz)).1
        change stCompPre δ (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18 q) =
            if (popBernJ (t11OfParts (evenOctIdxT10K (stCompPre δ wNN == 1) (d2Fn δ)))
            (coin33ProxyOfJK2 (popBernJK2 (t11OfParts (evenOctIdxT10K (stCompPre δ wNN == 1)
            (d2Fn δ))) (w11OfReg13 rC13 (stDPre δ))
            (o9Of13 (x13OfReg13 rC13 (stDPre δ)))))).testBit q.val then 1 else 0
        rw [congrArg (· == 1)
            (hWComp hNR δ).1, popBernJ_coin33ProxyOfJK2_eq ht11Lt (w11OfReg13 rC13 (stDPre δ))
            (o9Of13 (x13OfReg13 rC13 (stDPre δ)))]
        exact stepCB_coul18K2Sub63_eval_j hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
            hh.2.2.2.2.2.1 (stDPre δ) (isNNFn δ) (hd2Lt δ hz) (fun j ↦ hOutkPre δ j hz)
            (fun q' ↦ (hPers0 δ q' hz).1) (fun q9 ↦ (hPool0 δ ⟨q9.val, by omega⟩ hz).1) q
      have hPersCPers (δ) (q : Fin 18) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
          stCompPost δ (rPers18 q) = stCompPre δ (rPers18 q) :=
        cowp_stepCB_eq rCLB cpC.fwdBits (stDPost δ) (stDPre δ) (fun u ↦ by
            change stDPost δ (fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 u) =
                stDPre δ (fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 u); dsimp only [fCoul18K2Sub63];
                split_ifs
            · exact hOutkEq δ _ hz
            · exact (hC13EqD δ _).2.trans (((hAgree δ hz).2.2.2.2 _).trans (hC13EqD δ _).1.symm)
            · exact (hPers0 δ _ hz).2.trans (hPers0 δ _ hz).1.symm
            · exact (hPool0 δ ⟨_, by omega⟩ hz).2.trans (hPool0 δ ⟨_, by omega⟩ hz).1.symm)
          (rPers18 q) (fun _ ↦ (hPers0 δ q hz).2.trans (hPers0 δ q hz).1.symm)
      have hYNotPers (b : Fin 36) (q : Fin 18) : rY36 b ≠ rPers18 q := fun e ↦ by
        change rY36 b = fPers18k123 r q at e; dsimp only [fPers18k123] at e
        split_ifs at e <;> (have hv := rInj e; dsimp [rY36, rY36Of] at hv; omega)
      have hPoolNotPers (u : Fin 72) (q : Fin 18) : rPool u ≠ rPers18 q := fun e ↦ by
        change rPool u = fPers18k123 r q at e; dsimp only [fPers18k123] at e
        split_ifs at e <;> (have hv := rInj e; dsimp [rPool, rPool72k123, rPoolOf] at hv; omega)
      let midRestore :=
          DynamicCircuit.seq (.circuit (.CNOT w16 w17 h16_17))
          (.seq mid (.circuit (.CNOT w16 w17 h16_17)))
      have hWIdx7 {w : Wire n} (hw : ∀ i, w ≠ r i) (i : Fin 7) : w ≠ (rIdx7Of22 rOut22) i := fun e ↦
          by
        change w = fOut22k123 r ⟨1 + i.val, _⟩ at e
        dsimp only [fOut22k123] at e
        rw [_root_.dite_eq_left (by omega)] at e
        exact hw _ e
      have hInnerStep :=
          pkgInner.step2_pers v rWork wG wScr wNN (rIdx7Of22 rOut22) (rK4Of22 rOut22)
          (rJ2OfPers coul18K2OutIdx2 coul18K2OutIdx2_inj rPers18)
        rY36 rPool hh.2.2.2.2.2.2 (hWIdx7 hSR)
            (hWIdx7 hNR) midRestore stCompPre stCompPost ph₁ ph₂ cFakeFn d2Fn hd2Lt
        (fun δ hz ↦ (hWComp hGR δ).2.trans ((hAgree δ hz).1.trans (hWComp hGR δ).1.symm))
        (fun δ hz ↦ (hWComp hSR δ).2.trans ((hAgree δ hz).2.1.trans (hWComp hSR δ).1.symm))
        (fun δ hz ↦ (hWComp hNR δ).2.trans ((hAgree δ hz).2.2.1.trans (hWComp hNR δ).1.symm))
        (fun δ hz hs0 ↦ congrArg (· == 1)
            ((hWComp hNR δ).1.trans (hValid0 δ hz (zmod2_eq_of_beq_one_eq_s1b _ false
            ((congrArg (· == 1) (hWComp hSR δ).1).symm.trans hs0)))))
        (fun δ i hz ↦ by
          rw [(hWComp hNR δ).1]
          exact (hPresCPre δ _ fun q ↦ disj_ne hh.2.1 _ q).trans
            ((out22_t11_bits rOut22 (stDPre δ) (isNNFn δ) (hd2Lt δ hz)
                (fun j ↦ hOutkPre δ j hz)).2.2.1 i))
        (fun δ i hz ↦ (hPresCPost δ _ fun q ↦
            disj_ne hh.2.1 _ q).trans ((hOutkEq δ _ hz).trans (hPresCPre δ _ fun q ↦
            disj_ne hh.2.1 _ q).symm))
        (fun δ i hz ↦ by
          rw [(hWComp hNR δ).1]
          exact (hPresCPre δ _ fun q ↦ disj_ne hh.2.1 _ q).trans
            ((out22_t11_bits rOut22 (stDPre δ) (isNNFn δ) (hd2Lt δ hz)
                (fun j ↦ hOutkPre δ j hz)).2.2.2 i))
        (fun δ i hz ↦ (hPresCPost δ _ fun q ↦
            disj_ne hh.2.1 _ q).trans ((hOutkEq δ _ hz).trans (hPresCPre δ _ fun q ↦
            disj_ne hh.2.1 _ q).symm))
        hJ2Pre (fun δ q hz ↦ hPersCPers δ (coul18K2OutIdx2 q) hz)
        (fun δ b hz ↦ (hPresCPre δ _ fun q ↦ hYNotPers b q).trans ((hDLt143 (idx :=
            ⟨18 + b.val, potGen_y36_lt 123 b⟩) (by (try dsimp only); omega)
            (by (try dsimp only); omega) δ).1.trans (hY0 δ b hz).1))
        (fun δ b hz ↦ (hPresCPost δ _ fun q ↦ hYNotPers b q).trans ((hDLt143 (idx :=
            ⟨18 + b.val, potGen_y36_lt 123 b⟩) (by (try dsimp only); omega)
            (by (try dsimp only); omega) δ).2.trans (hY0 δ b hz).2))
        (fun δ u hz ↦ (hPresCPre δ _ fun q ↦ hPoolNotPers u q).trans (hPool0 δ u hz).1)
        (fun δ u hz ↦ (hPresCPost δ _ fun q ↦ hPoolNotPers u q).trans (hPool0 δ u hz).2)
        (fun stMidPre stMidPost hPresMPre hPresMPost hValM hPoolM hPoolMPers ↦ by
          let m₁ : BitAssignment n → BitAssignment n := fun δ ↦
              Function.update (stMidPre δ) w17 (stMidPre δ w17 + stMidPre δ w16)
          let m₂ : BitAssignment n → BitAssignment n := fun δ ↦
              Function.update (stMidPost δ) w17 (stMidPost δ w17 + stMidPost δ w16)
          have hLt18Sep {idx : Fin (54 + 123)} (h : idx.val < 18) : (∀ b : Fin 36, r idx ≠ rY36 b) ∧
              (∀ u : Fin 72, r idx ≠ rPool u) ∧ (∀ q : Fin 18, r idx ≠ rPers18 q) :=
            ⟨fun b e ↦ (fun hv ↦ by (try dsimp [rY36, rY36Of] at hv); omega)
                (rInj e), fun u e ↦
                (fun hv ↦ by (try dsimp [rPool, rPool72k123, rPoolOf] at hv); omega)
                (rInj e), fun q e ↦ by
               change r idx = fPers18k123 r q at e
               dsimp only [fPers18k123] at e
               split_ifs at e <;> exact (fun hv ↦ by (try dsimp at hv); omega) (rInj e)⟩
          obtain ⟨h16NotY, h16NotP, h16NotPers⟩ := hLt18Sep (idx := ⟨16, by decide⟩) (by decide)
          obtain ⟨h17NotY, h17NotP, h17NotPers⟩ := hLt18Sep (idx := ⟨17, by decide⟩) (by decide)
          have hM16Pre : ∀ δ, stMidPre δ w16 = st₁ δ w16 := fun δ ↦
              (hPresMPre δ w16 h16NotY h16NotP).trans ((hPresCPre δ w16 h16NotPers).trans
              ((hDPreOut δ w16 h16_17 h16_176).trans (h16Pre δ)))
          have hM16Post : ∀ δ, stMidPost δ w16 = st₂ δ w16 := fun δ ↦
              (hPresMPost δ w16 h16NotY h16NotP).trans ((hPresCPost δ w16 h16NotPers).trans
              ((hDPostOut δ w16 h16_17 h16_176).trans (h16Post δ)))
          have hM17Pre : ∀ δ, stMidPre δ w17 = st₁ δ w17 + st₁ δ w16 := fun δ ↦ by
            rw [hPresMPre δ w17 h17NotY h17NotP, hPresCPre δ w17 h17NotPers]; dsimp only [stDPre];
            simp only [Function.update_apply, h17_176, ↓reduceIte]; rw [h17Pre δ, h16Pre δ]
          have hM17Post : ∀ δ, stMidPost δ w17 = st₂ δ w17 + st₂ δ w16 := fun δ ↦ by
            rw [hPresMPost δ w17 h17NotY h17NotP, hPresCPost δ w17 h17NotPers];
            dsimp only [stDPost]; simp only [Function.update_apply, h17_176, ↓reduceIte];
            rw [h17Post δ, h16Post δ]
          obtain ⟨hm1_17, hm2_17⟩ : (∀ δ, m₁ δ w17 = st₁ δ w17) ∧ (∀ δ, m₂ δ w17 = st₂ δ w17) :=
            ⟨fun δ ↦ (Function.update_self _ _ _).trans ((congrArg₂ (· + ·) (hM17Pre δ)
                (hM16Pre δ)).trans (z2_cancel _ _)),
             fun δ ↦
                 (Function.update_self _ _ _).trans ((congrArg₂ (· + ·) (hM17Post δ)
                 (hM16Post δ)).trans (z2_cancel _ _))⟩
          have sM2 : SubspaceStep (Var := Var) (mkKetOpW rWork m₂ ph₂)
              (mkKetOpW rWork stMidPost ph₂) (.circuit (.CNOT w16 w17 h16_17)) := by
            refine subspaceStep_of_eq_post (subspaceStep_cnot_mkKetOpW (Var :=
                Var) rWork w16 w17 h16_17 m₂ ph₂)
                (mkKetOpW_congr rWork (fun δ _ ↦ funext fun w ↦ ?_) (fun _ _ ↦ rfl))
            dsimp only [m₂]; simp only [Function.update_apply, h16_17, ↓reduceIte]
            rcases eq_or_ne w w17 with rfl | hw
            · simpa only [↓reduceIte] using z2_cancel _ _
            · simp only [hw, ↓reduceIte]
          have hCoreMid : SubspaceStep (mkKetOpW rWork m₁ ph₁) (mkKetOpW rWork m₂ ph₂) mid :=
            hMidCB m₁ m₂
              (fun δ w hny hnk ↦ by
                rcases eq_or_ne w w17 with rfl | hw17
                · exact ⟨hm1_17 δ, hm2_17 δ⟩
                · have hnP (u : Fin 72) : w ≠ rPool u := fun e ↦
                      hnk ⟨u.val, by omega⟩ (e.trans (hPoolEq u))
                  have hnPers (q : Fin 18) : w ≠ rPers18 q := fun e ↦ by
                    change w = fPers18k123 r q at e; dsimp only [fPers18k123] at e
                    split_ifs at e with hq17
                    · exact hnk ⟨72 + q.val, by omega⟩
                          (e.trans (congrArg r.wires (Fin.ext (by dsimp; omega))))
                    · exact hnk ⟨122, by decide⟩ (e.trans (congrArg r.wires (Fin.ext rfl)))
                  have hn180 : w ≠ w176 := fun e ↦
                      hnk ⟨122, by decide⟩ (e.trans (congrArg r.wires (Fin.ext rfl)))
                  have hnTop (j : Fin 22) : w ≠ rTop j := fun e ↦
                      hnk ⟨101 + j.val, by omega⟩
                      (e.trans (congrArg r.wires (Fin.ext (by dsimp [rTop, rTop22Hi]))))
                  have hnP12 (p : Fin 12) : w ≠ rP12 p := fun e ↦
                      hnk ⟨89 + p.val, by omega⟩
                      (e.trans (congrArg r.wires
                      (Fin.ext (by (try dsimp [rP12, rPers12Of]); omega))))
                  exact ⟨(Function.update_of_ne hw17 _ _).trans ((hPresMPre δ w hny hnP).trans
                      ((hPresCPre δ w hnPers).trans ((hDPreOut δ w hw17 hn180).trans (hPresDPre δ w
                      hnTop hnP12)))),
                    (Function.update_of_ne hw17 _ _).trans ((hPresMPost δ w hny hnP).trans
                        ((hPresCPost δ w hnPers).trans ((hDPostOut δ w hw17 hn180).trans (hPresDPost
                        δ w hnTop hnP12))))⟩)
              (fun δ hz ↦ by
                have hy1 (b : Fin 36) : m₁ δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) =
                    stMidPre δ (rY36 b) := Function.update_of_ne (h17NotY b).symm _ _
                have hy2 (b : Fin 36) : m₂ δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) =
                    stMidPost δ (rY36 b) := Function.update_of_ne (h17NotY b).symm _ _
                rw [funext hy1]
                refine ⟨(hValM δ hz).1.trans ?_, fun b ↦
                    (hy2 b).trans (((hValM δ hz).2.1 b).trans (hy1 b).symm), fun hg0 b ↦
                    (hy1 b).trans ((hValM δ hz).2.2 ((hWComp hGR δ).1.trans hg0) b)⟩
                dsimp only [cFakeFn, d2Fn]
                have hC13Pre (j : Fin 13) : stDPre δ (rC13 j) = st₁ δ (rC13 j) := (hC13EqD δ j).1
                have hW11 : w11OfReg13 rC13 (stDPre δ) = w11OfReg13 rC13 (st₁ δ) := by
                  unfold w11OfReg13
                  simp only [hC13Pre]
                have hX13 : x13OfReg13 rC13 (stDPre δ) = x13OfReg13 rC13 (st₁ δ) := by
                  unfold x13OfReg13
                  simp only [hC13Pre]
                rw [(hWComp hGR δ).1, (hWComp hSR δ).1, (hWComp hNR δ).1, hW11, hX13,
                    ← ySampleK2_eq_proxy word512DualLegLo6 (st₁ δ wNN == 1) (hd2Lt δ hz)])
              (fun δ j hz ↦ by
                let idxR : Fin (54 + 123) :=
                    ⟨54 + j.val,
                    potGen_mid_lt (Nat.le_trans pkgInner.hMidLE (by decide : 72 ≤ 123)) j⟩
                let idxP : Fin 72 := ⟨j.val, Nat.lt_of_lt_of_le j.isLt pkgInner.hMidLE⟩
                have hEqP : r idxR = rPool idxP :=
                    congrArg r.wires (Fin.ext (by dsimp [idxR, idxP, rPool, rPool72k123, rPoolOf]))
                change m₁ δ (r idxR) = 0 ∧ m₂ δ (r idxR) = 0; rw [hEqP];
                have hn17 : rPool idxP ≠ w17 :=
                    (h17NotP idxP).symm; dsimp only [m₁, m₂]; rw [Function.update_of_ne hn17,
                    Function.update_of_ne hn17]
                exact hPoolM δ j hz)
              (fun δ u hz ↦ by
                have hn17 : r ⟨54 + u.val, potGen_k_lt 123 u⟩ ≠ w17 :=
                    rNe (by (try dsimp only); omega)
                dsimp only [m₁, m₂]; simp only [Function.update_apply, hn17, ↓reduceIte]
                by_cases hu76 : u.val < 72
                · simpa only [(hPoolEq ⟨u.val, hu76⟩).symm] using hPoolMPers δ ⟨u.val, hu76⟩ hz
                · rw [hPresMPost δ _ (fun b ↦ rNe (by (try dsimp [rY36, rY36Of]); omega))
                      (fun p ↦ rNe (by (try dsimp [rPool, rPool72k123, rPoolOf]); omega)),
                      hPresMPre δ _ (fun b ↦ rNe (by (try dsimp [rY36, rY36Of]); omega))
                          (fun p ↦ rNe (by (try dsimp [rPool, rPool72k123, rPoolOf]); omega))]
                  by_cases hu93 : u.val < 89
                  · have hEqPers : r ⟨54 + u.val, potGen_k_lt 123 u⟩ = rPers18 ⟨u.val - 72,
                        by omega⟩ := by
                      symm; change fPers18k123 r ⟨u.val - 72, by omega⟩ = _
                      dsimp only [fPers18k123]; rw [ditePos (by omega)]
                      exact congrArg r.wires (Fin.ext (by dsimp; omega))
                    simpa only [hEqPers] using hPersCPers δ ⟨u.val - 72, by omega⟩ hz
                  · by_cases hu126 : u.val < 122
                    · have hnPers (q : Fin 18) : r ⟨54 + u.val, potGen_k_lt 123 u⟩ ≠ rPers18 q :=
                          fun e ↦ by
                        change _ = fPers18k123 r q at e
                        dsimp only [fPers18k123] at e
                        split_ifs at e <;> exact (fun hv ↦ by (try dsimp at hv); omega) (rInj e)
                      have hn180 : r ⟨54 + u.val, potGen_k_lt 123 u⟩ ≠ w176 :=
                          rNe (by (try dsimp [w176]); omega)
                      rw [hPresCPost δ _ hnPers, hPresCPre δ _ hnPers, hDPostOut δ _ hn17 hn180,
                          hDPreOut δ _ hn17 hn180]
                      by_cases hu105 : u.val < 101
                      · simpa only [show r ⟨54 + u.val, potGen_k_lt 123 u⟩ = rP12 ⟨u.val - 89,
                            by omega⟩ from congrArg r.wires
                                 (Fin.ext (by (try dsimp [rP12, rPers12Of]); omega))] using
                                 hPers12DEq δ ⟨u.val - 89, by omega⟩ hz
                      · simpa only [show r ⟨54 + u.val, potGen_k_lt 123 u⟩ = rTop ⟨u.val - 101,
                            by omega⟩ from congrArg r.wires
                                 (Fin.ext (by (try dsimp [rTop, rTop22Hi]); omega))] using
                                 hOutDEq δ ⟨u.val - 101, by omega⟩ hz
                    · have hEqPers17 : r ⟨54 + u.val, potGen_k_lt 123 u⟩ = rPers18 ⟨17, by decide⟩
                          := by
                        change _ = fPers18k123 r ⟨17, by decide⟩
                        dsimp only [fPers18k123]
                        rw [diteNeg (by decide)]
                        exact congrArg r.wires (Fin.ext (by (try dsimp only); omega))
                      simpa only [hEqPers17] using hPersCPers δ ⟨17, by decide⟩ hz)
          exact subspaceStep_seq_u (subspaceStep_cnot_mkKetOpW (Var :=
              Var) rWork w16 w17 h16_17 stMidPre ph₁) (subspaceStep_seq_u hCoreMid sM2))
      have hCLBPers (u : Wire 96) (hu : coul18K2SMask.testBit u.val = true) : ∃ q : Fin 18, rCLB u =
          rPers18 q := by
        have hg2 : (coul18K2Sub63Tag u).1.val = 2 := (coul18K2SMask_iff_sub63Tag2 u).mp hu
        refine ⟨⟨(coul18K2Sub63Tag u).2, coul18K2Sub63Tag_lt2 u hg2⟩, ?_⟩
        change fCoul18K2Sub63 rOut22 rC13 rPers18 rPad54 u = _
        dsimp only [fCoul18K2Sub63]
        rw [diteNeg (by omega), diteNeg (by omega), ditePos hg2]
      have hCoreStep :=
          (subspaceStep_wrapOnReg_mkKetOpW_mask2 v rWork rCLB coul18K2SMask cpC 18 (hvC.trans
          coul18K2Sub63Tree_check.1) (haC.trans coul18K2Sub63Tree_check.2) stDPre stDPost ph₁ ph₂ _
        (fun u hu δ hz ↦ (hCLBPers u hu).elim fun q hq ↦
            (congrArg (stDPre δ) hq).trans (hPers0 δ q hz).1)
        (fun u hu δ hz ↦ (hCLBPers u hu).elim fun q hq ↦
            (congrArg (stDPost δ) hq).trans (hPers0 δ q hz).2) hInnerStep).1
      exact subspaceStep_seq_u (subspaceStep_cnot_mkKetOpW (Var :=
          Var) rWork w16 w17 h16_17 stDomPre ph₁)
          (subspaceStep_seq_u sd2' (subspaceStep_seq_u hCoreStep hPostDom2))
attribute [local irreducible] coul18K2Sub63Tree wrapCoulOWScr13_coulMid_k123 in
def coulOWScrPkg13_coulMid_pe_k123_of {kMid tInner tCoul : ℕ}
    (pkgInner : PhotochemistrySolution.CoulM72Mid36Opt.CoulInnerCorePkgM72 kMid tInner)
    (htCoul : 168 + 72 + tInner = tCoul) :
    CoulOWScrPkg13 tCoul (ySampleK2 word512DualLegLo6) where
  kRest := 123
  kMid := kMid
  hKMid := Nat.le_trans pkgInner.hMidLE (by decide : 72 ≤ 123)
  wrap := wrapCoulOWScr13_coulMid_k123 pkgInner
  counts_wires v wG wScr wNN r rC13 hGR hGC hSR hSC hNR hNC hSN hRC hGS hSS hNS hRS hCS mid := by
    obtain ⟨ht, hf, hw⟩ :=
        wrapCoulOWScr13_coulMid_k123_counts_wires pkgInner v wG wScr wNN r rC13 hGR hGC hSR hSC hNR
        hNC hSN hRC hGS hSS hNS hRS hCS mid
    exact ⟨by rw [ht]; omega, hf, hw⟩
  step_phase2 := wrapCoulOWScr13_coulMid_k123_step2_pers pkgInner
end QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2
end

/-!
# Stage-4 Root QROM Load (`438 T, kScr = 78`)

1. `PhotochemistrySolution.Load438K78Opt`:
   -
   `qromLoadRootG78DualLeg_438_k78_certChk : QromLoadPkgGenN 10 30 (gGatedShr6Word word512DualLeg)`
   - `kScr = 78` (`≤ 72 + 6`), `tLoad = 438 T`.
   - Synthesizes `89` target polynomials (`69` non-leaf Stage-1 intermediates + `20` direct `8` -var
   Stage-2
     product polynomials) via `9` `pWrDual118` `6 T` shared-control dual-AND W-routers (`54 T`) +
     `71` `andComputeCircuit` s (`284 T`) + `534` -CNOT Patel-Markov-Hayes `89x89` `GF(2)` basis
     change (`0 T`),
     joining structurally onto `litLdCT_4`
     and `ldChunk_4..13` (`cert_ldChunk_4..13`, `100 T` , `25` `andComputeCircuit` s + `0 T` MBU
     uncomputes).
2. `PhotochemistrySolution.CoulM72Mid36Opt` (reopened):
   - `coulInnerCoreM72_certChk_tap29_794 : CoulInnerCorePkgM72 29 794` (`438 + 76 + 22 + 258 = 794
   T`)
3. `PhotochemistrySolution.Coulomb18K2` (reopened):
   -
   `coulOWScrPkg13_certChk_m72_k123_tap29_1034 : CoulOWScrPkg13 1034 (ySampleK2 word512DualLegLo6)`
   - `coulOWScrPkg13_certChk_m72_k123_tap29_1034_kRest` (`= 123`) & `..._kMid` (`= 29`).
-/

section
set_option maxRecDepth 8192

namespace QuantumComputation.Specs.PhotochemistrySolution.CoulM72Mid36Opt

/-- `794 T` `0-Scrub` `M = 72, kMid = 29` inner core (`438 + 76 + 22 + 258 = 794 T`). -/
noncomputable def coulInnerCoreM72_certChk_tap29_794 : CoulInnerCorePkgM72 29 794 :=
  coulInnerCoreM72Basis_mid36_0scrub (by decide : 29 ≤ 36)
    qromLoadRootG78DualLeg_438_k78_certChk
    qromUnloadRootG89DualLeg_wrouter_76_unld
    certChk_load438_k78_hScr_m72
    unld76_hScr_m72
    kpBasis9WRouterPkg22
    butterfly33K9Scr31Pkg258
    rfl

end QuantumComputation.Specs.PhotochemistrySolution.CoulM72Mid36Opt

namespace QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2

attribute [local irreducible] CoulM72Mid36Opt.coulInnerCoreM72_certChk_tap29_794 in
noncomputable def coulOWScrPkg13_certChk_m72_k123_tap29_1034 :
    CoulOWScrPkg13 1034 (ySampleK2 word512DualLegLo6) :=
    coulOWScrPkg13_coulMid_pe_k123_of CoulM72Mid36Opt.coulInnerCoreM72_certChk_tap29_794 rfl
theorem coulOWScrPkg13_certChk_m72_k123_tap29_1034_kRest :
    coulOWScrPkg13_certChk_m72_k123_tap29_1034.kRest = 123 := by decide
theorem coulOWScrPkg13_certChk_m72_k123_tap29_1034_kMid :
    coulOWScrPkg13_certChk_m72_k123_tap29_1034.kMid = 29 := by decide

end QuantumComputation.Specs.PhotochemistrySolution.Coulomb18K2
end

noncomputable section
open QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
section
open Operator QProg Matrix Circuit Qubit PrimitiveGate
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin
open HermitianMat
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val


def takeNOf24 {nInner : ℕ} (hn : nInner ≤ 24) (z : BitAssignment 24) : BitAssignment nInner :=
    fun j ↦ z ⟨j.val, Nat.lt_of_lt_of_le j.isLt hn⟩
def putNIn24 {nInner : ℕ} (_hn : nInner ≤ 24) (zN : BitAssignment nInner) (z : BitAssignment 24) :
    BitAssignment 24 := fun i ↦ if h : i.val < nInner then zN ⟨i.val, h⟩ else z i
def equiv24_splitN {nInner : ℕ} (hn : nInner ≤ 24) :
    BitAssignment 24 ≃ BitAssignment nInner × BitAssignment (24 - nInner) where
  toFun z := (takeNOf24 hn z, fun j ↦ z ⟨nInner + j.val, by have := j.isLt; omega⟩)
  invFun p := fun i ↦
    if h : i.val < nInner then p.1 ⟨i.val, h⟩
    else p.2 ⟨i.val - nInner, by have := i.isLt; omega⟩
  left_inv z := funext fun i ↦ by
    by_cases h : i.val < nInner
    · simp [takeNOf24, h]
    · simp only [h, ↓reduceDIte]
      exact congrArg z (Fin.ext (by dsimp; omega))
  right_inv p := Prod.ext
    (funext fun j ↦ by simp [takeNOf24, j.isLt])
    (funext fun j ↦ by
      have hnlt : ¬ (nInner + j.val < nInner) := by omega
      simp only [hnlt, ↓reduceDIte]
      exact congrArg p.2 (Fin.ext (by dsimp; omega)))

def liftReflPotSliceNTo24 {nInner : ℕ} (hn : nInner ≤ 24) {potExpect : PotExpectFn}
    (s : ReflPotSliceSpecN nInner potExpect) : ReflPotSliceSpec24 potExpect where
  phaseBit s0 nn sp1 sp2 nA nB eA eB z :=
    s.phaseBit s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z)
  coinSwap s0 nn sp1 sp2 nA nB eA eB z :=
    putNIn24 hn (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z)) z
  coinSwap_invol s0 nn sp1 sp2 nA nB eA eB z := funext fun i ↦ by
    have hTake : takeNOf24 hn
        (putNIn24 hn (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z)) z) =
        s.coinSwap s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z) :=
      funext fun j ↦ by simp [takeNOf24, putNIn24, j.isLt]
    rw [hTake, s.coinSwap_invol]
    by_cases hi : i.val < nInner <;> simp [putNIn24, takeNOf24, hi]
  phaseBit_coinSwap s0 nn sp1 sp2 nA nB eA eB z := by
    have hTake : takeNOf24 hn
        (putNIn24 hn (s.coinSwap s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z)) z) =
        s.coinSwap s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z) :=
      funext fun j ↦ by simp [takeNOf24, putNIn24, j.isLt]
    rw [hTake]; exact s.phaseBit_coinSwap s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z)
  phaseBit_port s0 nn sp1 sp2 nA nB eA eB z :=
    s.phaseBit_port s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z)
  coinSwap_port s0 nn sp1 sp2 nA nB eA eB z :=
    congrArg (fun u ↦ putNIn24 hn u z)
      (s.coinSwap_port s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z))
  avg_coin24 s0 nn sp1 sp2 nA nB eA eB := by
    let f : BitAssignment 24 → ℂ := fun z ↦
        bitSign (s.phaseBit s0 nn sp1 sp2 nA nB eA eB (takeNOf24 hn z))
    change (2 ^ 24 : ℂ)⁻¹ * ∑ z : BitAssignment 24, f z =
        (potExpect s0 nn sp1 sp2 nA nB eA eB : ℂ); rw [← Equiv.sum_comp (equiv24_splitN hn).symm f,
        Fintype.sum_prod_type]
    have hPoint : ∀ (zN : BitAssignment nInner) (zR : BitAssignment (24 - nInner)),
        f ((equiv24_splitN hn).symm (zN, zR)) =
          bitSign (s.phaseBit s0 nn sp1 sp2 nA nB eA eB zN) := fun zN zR ↦ by
      dsimp only [f]
      rw [show takeNOf24 hn ((equiv24_splitN hn).symm (zN, zR)) = zN from
        congrArg Prod.fst ((equiv24_splitN hn).apply_symm_apply (zN, zR))]
    simp_rw [hPoint]
    have hCard : Fintype.card (BitAssignment (24 - nInner)) = 2 ^ (24 - nInner) := by
      dsimp only [BitAssignment]; rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    simp only [Finset.sum_const, Finset.card_univ, hCard, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, ← Finset.mul_sum, ← mul_assoc]
    have h2 : (2 ^ 24 : ℂ)⁻¹ * (2 : ℂ) ^ (24 - nInner) = (2 ^ nInner : ℂ)⁻¹ := by
      have h24 : (2 : ℂ) ^ 24 = (2 : ℂ) ^ nInner * (2 : ℂ) ^ (24 - nInner) := by
        rw [← pow_add, Nat.add_sub_of_le hn]
      rw [h24, mul_inv, mul_assoc, inv_mul_cancel₀ (pow_ne_zero (24 - nInner) two_ne_zero), mul_one]
    rw [h2]; exact s.avg_coinN s0 nn sp1 sp2 nA nB eA eB
def skipTo24Val (nInner k : ℕ) : ℕ := if k < 81 + nInner then k else k + (24 - nInner)
theorem skipTo24Val_lt {nInner Wp : ℕ} (hn : nInner ≤ 24) (i : Fin ((81 + nInner) + Wp)) :
    skipTo24Val nInner i.val < 105 + Wp := by
  have := i.isLt; unfold skipTo24Val; split_ifs <;> omega
def skipTo24OfN {nInner : ℕ} (hn : nInner ≤ 24) (Wp : ℕ) :
    QRegister ((81 + nInner) + Wp) (105 + Wp) where
  wires :=
    { toFun := fun i ↦ ⟨skipTo24Val nInner i.val, skipTo24Val_lt hn i⟩
      inj' := fun a b h ↦ by
        have hv := congrArg Fin.val h
        have ha := a.isLt; have hb := b.isLt
        dsimp [skipTo24Val] at hv; split_ifs at hv <;> exact Fin.ext (by omega) }

theorem val_skipTo24OfN {nInner Wp : ℕ} (hn : nInner ≤ 24) (i : Fin ((81 + nInner) + Wp)) :
    (skipTo24OfN hn Wp i).val = if i.val < 81 + nInner then i.val else i.val + (24 - nInner) := rfl

def toCoin24InPlaceOfN {nInner kCoin Wp tPotU tPotC : ℕ} (hn : nInner ≤ 24)
    {peK : BitAssignment kCoin → PotExpectFn}
    (oN : Stage4ReflCoinPotOraclePortBInPlace nInner kCoin Wp tPotU tPotC peK) :
    Stage4ReflCoin24PotOraclePortBInPlace kCoin Wp tPotU tPotC peK where
  sliceSpec γ := liftReflPotSliceNTo24 hn (oN.sliceSpec γ)
  pCsel v r rCoin := oN.pCsel v (r.compose (skipTo24OfN hn Wp)) rCoin
  pUsel v r rCoin := oN.pUsel v (r.compose (skipTo24OfN hn Wp)) rCoin
  dynWires S v r rCoin hr hrC :=
    oN.dynWires S v (r.compose (skipTo24OfN hn Wp)) rCoin (fun i ↦ hr _) hrC
  step_and_counts {Var _ _ m n _} v rW r rCoin hd isCsel st hVal hCln hPB0 := by
    let rN := r.compose (skipTo24OfN hn Wp)
    have hLow : ∀ (c : ℕ) (hcN : c < (81 + nInner) + Wp) (hc : c < 81 + nInner),
        rN ⟨c, hcN⟩ = r ⟨c, by omega⟩ := fun c _ hc ↦
      congrArg r.wires (Fin.ext (by rw [val_skipTo24OfN, ite_eq_left hc]))
    have hBlk24 : ∀ (off : ℕ) (hN : off + 24 ≤ (81 + nInner) + Wp) (h24 : off + 24 ≤ 105 + Wp),
        off + 24 ≤ 81 + nInner →
        rN.compose (QRegister.block off 24 hN) = r.compose (QRegister.block off 24 h24) :=
      fun off _ _ _ ↦ congrArg QRegister.mk (Function.Embedding.ext fun k ↦
        hLow (off + k.val) (by have := k.isLt; omega) (by have := k.isLt; omega))
    have hdN : rN.DisjointWires rCoin := disj_of_ne fun i j e ↦
        QRegister.disjoint_iff.mp hd (skipTo24OfN hn Wp i) j e
    have hNucA : rPotBNNucA rN = rPotB24NucA r := hBlk24 9 (by omega) (by omega) (by omega)
    have hElecA : rPotBNElecA rN = rPotB24ElecA r := hBlk24 33 (by omega) (by omega) (by omega)
    have hPortB : rPotBNPortB rN = rPotB24PortB r := hBlk24 57 (by omega) (by omega) (by omega)
    have hScrW : wPotBNIsScreen rN = wPotB24IsScreen r := hLow 1 (by omega) (by omega)
    have hValN : ∀ δ, (∀ q : Fin m, δ (rW q) = 0) → ValidPotBFlagsN rN (st δ) := fun δ hz ↦ by
      have hv := hVal δ hz; dsimp only [ValidPotBFlagsN, wPotBNIsPot, wPotBNIsScreen, wPotBNIsNN]
      rw [hLow 2 (by omega) (by omega), hLow 1 (by omega) (by omega), hLow 4 (by omega) (by omega)]
      exact hv
    have hClnN : ∀ δ (u : Fin Wp), (∀ q : Fin m, δ (rW q) = 0) →
        st δ (rPotBWorkN rN u) = 0 := fun δ u hz ↦ by
      have hwEq : rPotBWorkN rN u = rPotBWork24 r u := congrArg r.wires (Fin.ext (by
        change (skipTo24OfN hn Wp ⟨(81 + nInner) + u.val, _⟩).val = 105 + u.val
        rw [val_skipTo24OfN]; dsimp only; split_ifs <;> omega))
      rw [hwEq]; exact hCln δ u hz
    have hPB0_N : ∀ δ (i : Fin 24), (∀ q : Fin m, δ (rW q) = 0) →
        st δ (wPotBNIsScreen rN) = 0 → st δ (rPotBNPortB rN i) = 0 := fun δ i hz hs0 ↦ by
      rw [hScrW] at hs0
      rw [show rPotBNPortB rN i = rPotB24PortB r i from congrArg (fun reg ↦ reg i) hPortB]
      exact hPB0 δ i hz hs0
    obtain ⟨sN, hT, hF⟩ := oN.step_and_counts v rW rN rCoin hdN isCsel st hValN hClnN hPB0_N
    have hXorEq : ∀ β : BitAssignment n, xorPortBNNotScr rN β = xorPortB24NotScr r β := fun β ↦ by
      unfold xorPortBNNotScr xorPortB24NotScr; rw [hPortB, hScrW, hNucA]
    refine ⟨subspaceStep_congr_out sN (congrArg₂ (mkKetOpW rW) (funext fun δ ↦ ?_)
        (funext fun δ ↦ ?_)), hT, hF⟩
    · rw [hXorEq]; apply congrArg (xorPortB24NotScr r)
      have hGate : potBNGateActive isCsel rN (st δ) = potB24GateActive isCsel r (st δ) := by
        dsimp only [potBNGateActive, potB24GateActive, wPotBNLocQ, wPotBNIsPot, wPotB24LocQ,
            wPotB24IsPot]
        rw [hLow 0 (by omega) (by omega), hLow 2 (by omega) (by omega)]
      have hTakeC : takeNOf24 hn (fun k ↦ st δ (rPotBCoin24 r k)) =
          fun j ↦ st δ (rPotBCoinN rN j) := funext fun j ↦ by
        dsimp only [takeNOf24, rPotBCoin24, rPotBCoinN]
        exact (congrArg (fun u ↦ st δ u) (hLow (81 + j.val) (by have := j.isLt; omega)
          (by have := j.isLt; omega))).symm
      have hCoinEq : potOraclePortBNCoinEval ((oN.sliceSpec (fun j ↦
          st δ (rCoin j))).coinSwap) rN (st δ) =
          takeNOf24 hn (potOraclePortB24CoinEval ((liftReflPotSliceNTo24 hn (oN.sliceSpec (fun j ↦
          st δ (rCoin j)))).coinSwap) r (st δ)) := by
        funext j;
        dsimp only [takeNOf24, potOraclePortB24CoinEval, potOraclePortBNCoinEval,
            liftReflPotSliceNTo24, putNIn24, wPotBNIsScreen, wPotBNIsNN, wPotBNSp1B0, wPotBNSp1B1,
            wPotBNSp2B0, wPotBNSp2B1, wPotB24IsScreen, wPotB24IsNN, wPotB24Sp1B0, wPotB24Sp1B1,
            wPotB24Sp2B0, wPotB24Sp2B1]; simp only [j.isLt, ↓reduceDIte]
        simp only [hLow 1 (by omega) (by omega), hLow 4 (by omega) (by omega),
            hLow 5 (by omega) (by omega), hLow 6 (by omega) (by omega),
            hLow 7 (by omega) (by omega), hLow 8 (by omega) (by omega),
            hNucA, hElecA, hPortB, hTakeC, Fin.eta]
      dsimp only [potReflPortBStN, potReflPortBSt24]; rw [hGate]
      split_ifs with hg
      · funext w; rw [hCoinEq]
        by_cases hm24 : ∃ i : Fin 24, rPotBCoin24 r i = w
        · obtain ⟨i, rfl⟩ := hm24; rw [DynCircExt.writeReg_apply_reg]
          by_cases hi : i.val < nInner
          · have hrEq : rPotBCoinN rN ⟨i.val, hi⟩ = rPotBCoin24 r i :=
              hLow (81 + i.val) (by omega) (by omega)
            rw [← hrEq, DynCircExt.writeReg_apply_reg]; rfl
          · rw [DynCircExt.writeReg_apply_of_not_mem (st δ) (rPotBCoinN rN) _ (rPotBCoin24 r i)
              (fun ⟨j, hj⟩ ↦ by
                have hjEq : rPotBCoinN rN j = rPotBCoin24 r ⟨j.val, by have := j.isLt; omega⟩ :=
                  hLow (81 + j.val) (by have := j.isLt; omega) (by have := j.isLt; omega)
                rw [hjEq] at hj; have hv := congrArg Fin.val ((rPotBCoin24 r).wires.injective hj)
                have := j.isLt; dsimp only at hv; omega)]
            dsimp only [potOraclePortB24CoinEval, liftReflPotSliceNTo24, putNIn24];
            simp only [hi, ↓reduceDIte]
        · rw [DynCircExt.writeReg_apply_of_not_mem _ (rPotBCoin24 r) _ w hm24,
              DynCircExt.writeReg_apply_of_not_mem _ (rPotBCoinN rN) _ w (fun ⟨j, hj⟩ ↦ hm24
                ⟨⟨j.val, by have := j.isLt; omega⟩,
                  (hLow (81 + j.val) (by have := j.isLt; omega)
                      (by have := j.isLt; omega)).symm.trans hj⟩)]
      · rfl
    · have hTakeC : takeNOf24 hn (fun k ↦ st δ (rPotBCoin24 r k)) =
          fun j ↦ st δ (rPotBCoinN rN j) := funext fun j ↦ by
        dsimp only [takeNOf24, rPotBCoin24, rPotBCoinN]
        exact (congrArg (fun u ↦ st δ u) (hLow (81 + j.val) (by have := j.isLt; omega)
          (by have := j.isLt; omega))).symm
      dsimp only [potReflPortBPh0_N, potReflPortBPh0_24, potOraclePortBNBitEval,
          potOraclePortB24BitEval, liftReflPotSliceNTo24, wPotBNLocQ, wPotBNIsPot, wPotBNIsScreen,
          wPotBNIsNN, wPotBNSp1B0, wPotBNSp1B1, wPotBNSp2B0, wPotBNSp2B1, wPotB24LocQ, wPotB24IsPot,
          wPotB24IsScreen, wPotB24IsNN, wPotB24Sp1B0, wPotB24Sp1B1, wPotB24Sp2B0, wPotB24Sp2B1]
      simp only [hLow 0 (by omega) (by omega), hLow 2 (by omega) (by omega),
          hLow 1 (by omega) (by omega), hLow 4 (by omega) (by omega),
          hLow 5 (by omega) (by omega), hLow 6 (by omega) (by omega),
          hLow 7 (by omega) (by omega), hLow 8 (by omega) (by omega),
          hNucA, hElecA, hPortB, hTakeC]

def ReflPotSliceNOnly (nInner : ℕ) {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) :
    Prop :=
    (∀ (hasN1 isEN : Bool) (spA spB : Fin 4) (R_A R_B r_a r_b : Fin 3 → Fin 256)
    (z₁ z₂ : BitAssignment 41), (∀ (m : Fin 41), m.val < nInner → z₁ m = z₂ m) → (∀ (m : Fin 41),
    m.val < nInner → spec.coinSwap hasN1 isEN spA spB R_A R_B r_a r_b z₁ m =
    spec.coinSwap hasN1 isEN spA spB R_A R_B r_a r_b z₂ m) ∧
    spec.phaseBit hasN1 isEN spA spB R_A R_B r_a r_b z₁ =
    spec.phaseBit hasN1 isEN spA spB R_A R_B r_a r_b z₂) ∧ (∀ (hasN1 isEN : Bool) (spA spB : Fin 4)
    (R_A R_B r_a r_b : Fin 3 → Fin 256) (z : BitAssignment 41) (m : Fin 41), ¬ m.val < nInner →
    spec.coinSwap hasN1 isEN spA spB R_A R_B r_a r_b z m = z m)
theorem reflPotSliceNOnly_spec41OfN {nInner kOut : ℕ} (hn : nInner ≤ 24)
    {peOut : BitAssignment kOut → PotExpectFn}
    (sN : ∀ γ : BitAssignment kOut, ReflPotSliceSpecN nInner (peOut γ))
    (γω : BitAssignment (0 + kOut)) : ReflPotSliceNOnly nInner (spec41Of24_ipb (fun γ ↦
    liftReflPotSliceNTo24 hn (sN γ)) γω) := by
  refine ⟨fun hasN1 isEN spA spB R_A R_B r_a r_b z₁ z₂ hEq ↦ ?_,
      fun hasN1 isEN spA spB R_A R_B r_a r_b z m hm ↦ ?_⟩
  · have hT : takeNOf24 hn (take24Of35_sub63 (take35Of41_wstate z₁)) =
        takeNOf24 hn (take24Of35_sub63 (take35Of41_wstate z₂)) := funext fun j ↦
        hEq ⟨j.val, by omega⟩ j.isLt
    refine ⟨fun m hmN ↦ ?_,
        by dsimp only [spec41Of24_ipb, liftReflPotSlice35To41_wstate, liftReflPotSlice24To35_sub63,
             liftReflPotSliceNTo24]; rw [hT]⟩
    dsimp only [spec41Of24_ipb, liftReflPotSlice35To41_wstate, liftReflPotSlice24To35_sub63,
        liftReflPotSliceNTo24, put35In41_wstate, put24In35_sub63, putNIn24]
    simp only [(by omega : m.val < 35), (by omega : m.val < 24), hmN, ↓reduceDIte, hT]
  · dsimp only [spec41Of24_ipb, liftReflPotSlice35To41_wstate, liftReflPotSlice24To35_sub63,
        liftReflPotSliceNTo24, put35In41_wstate, put24In35_sub63, putNIn24]
    by_cases hm35 : m.val < 35 <;> by_cases hm24 : m.val < 24 <;> simp only [hm35, hm24, hm,
        ↓reduceDIte] <;> rfl

theorem circWires_cPackCnotAux_skipPoly {nInner W n : ℕ} {S : Wire n → Prop}
    (r : QRegister (122 + W) n) (h24 : 24 ≤ W)
    (hr : ∀ j : Fin (122 + W), (j.val < 81 + nInner ∨ 122 ≤ j.val) → S (r j)) :
    ∀ (k : ℕ) (hk : k ≤ 24), CircWires S (cPackCnotAux r h24 k hk)
  | 0, _ => trivial
  | k + 1, hk => ⟨circWires_cPackCnotAux_skipPoly r h24 hr k (Nat.le_of_succ_le hk), fun i ↦ by
      fin_cases i
      · exact hr ⟨122 + k, by omega⟩ (Or.inr (by (try dsimp only); omega))
      · exact hr ⟨57 + k, by omega⟩ (Or.inl (by (try dsimp only); omega))⟩

theorem dynWires_pPotWrapReflPortB151InPlace_skipPoly {Var : Type}
    {nInner kOut n Wp tPotU tPotC : ℕ} (hn : nInner ≤ 24) {S : Wire n → Prop}
    {peOut : BitAssignment kOut → PotExpectFn}
    (oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut) (hWp : Wp ≤ 738)
    (v : Var) (rTot : QRegister dLayout n) (rCoin : QRegister (0 + kOut) dLayout) (isCsel : Bool)
    (hrB : ∀ j : Fin (122 + max Wp 24), (j.val < 81 + nInner ∨ 122 ≤ j.val) →
    S (rTot (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp) j)))
    (hrC : ∀ j : Fin (0 + kOut), S (rTot (rCoin j))) :
    DynWires S (pPotWrapReflPortB151InPlace (toCoin24InPlaceOfN hn oN) hWp v rTot rCoin isCsel)
    := by
  let rB := rTot.compose (rPotZeroNEremPortB151 (max Wp 24) (maxWp24_le_738 hWp));
  let rC := rTot.compose rCoin;
  let rSub := rB.compose (QRegister.block 0 (122 + Wp) (potWrapSub_le (Nat.le_max_left Wp 24)));
  let r24 := rSub.compose (skip17Of122Wp_ipb Wp); let rN := r24.compose (skipTo24OfN hn Wp);
  let rC0 := castZeroAddReg_ipb rC
  obtain ⟨wBC, wBU⟩ := oN.dynWires S v rN rC0 (fun i ↦ by
      have hi := i.isLt; let jSub := skip17Of122Wp_ipb Wp (skipTo24OfN hn Wp i)
      refine hrB ⟨0 + jSub.val, by have := jSub.isLt; omega⟩ ?_
      change 0 + jSub.val < 81 + nInner ∨ 122 ≤ 0 + jSub.val; rw [Nat.zero_add]; dsimp only [jSub];
      rw [val_skip17Of122Wp_ipb, val_skipTo24OfN]
      split_ifs <;> omega) (fun _ ↦ hrC _)
  let dPot :=
      if isCsel then (toCoin24InPlaceOfN hn oN).pCsel v r24 rC0 else (toCoin24InPlaceOfN hn
      oN).pUsel v r24 rC0
  have wP : DynWires S dPot := by
    dsimp only [dPot, toCoin24InPlaceOfN]; cases isCsel <;> [exact wBU; exact wBC]
  exact ⟨circWires_cPackCnotAux_skipPoly rB (Nat.le_max_right Wp 24) hrB 24 le_rfl,
    PhotochemistrySolution.PotOraclePortB.dynWires_xUnloadChunkCzPairsSeqDyn v
      (fun i ↦ if hi : i < 24 then rB ⟨122 + i,
          (packUnpack_b (Nat.le_max_right Wp 24) hi).2.2.1⟩ else rB ⟨0,
          (packUnpack_b (Nat.le_max_right Wp 24) (Nat.zero_lt_succ 23)).2.2.2.1⟩) 0
      (fun i ↦ if hi : i < 24 then ⟨rB ⟨4, (packUnpack_b (Nat.le_max_right Wp 24) hi).1⟩,
          ⟨rB ⟨57 + i, (packUnpack_b (Nat.le_max_right Wp 24) hi).2.1⟩,
          reflPackPair_ne rB (Nat.le_max_right Wp 24) hi⟩⟩ :: [] else [])
      dPot wP 24
      (fun _ _ ↦ by split_ifs <;> exact hrB _ (by dsimp; omega))
      (fun _ _ p hp ↦ by
        split_ifs at hp; rw [List.mem_singleton.mp hp]
        exact ⟨hrB _ (Or.inl (by dsimp; omega)), hrB _ (Or.inl (by dsimp; omega))⟩)⟩

attribute [local reducible] totDimCompactGen in
attribute [local irreducible] systemQubits_frozen ancWOfScr in
theorem val_rPotZeroNEremPortB151_skipPoly_lt {nInner Wp : ℕ} (hn : nInner ≤ 24) (hWp : Wp ≤ 738)
    (j : Fin (122 + Wp)) (hj : j.val < 81 + nInner ∨ 122 ≤ j.val) :
    (rPotZeroNEremPortB151 Wp hWp j).val < 7256 + nInner ∨ (rPotZeroNEremPortB151 Wp hWp j).val =
    7297 := by
  have hjLt := j.isLt
  rw [show (rPotZeroNEremPortB151 Wp hWp j).val =
      (potZeroNEremPortB151WireFn Wp hWp j).val from rfl, val_potZeroNEremPortB151WireFn hWp j]
  split_ifs <;> omega

theorem activeStackPoly_of_activeStack74_lt {gLo wWork mCoin nInner : ℕ}
    (hInner : 39 + nInner ≤ mCoin) {w : Wire dLayout} (h74 : ActiveOuterCoinStackOf gLo wWork 74 w)
    (hw : w.val < 7256 + nInner ∨ w.val = 7297) : ActiveOuterCoinStackOf gLo wWork mCoin w := by
  unfold ActiveOuterCoinStackOf at h74 ⊢; omega
theorem dynWires_pPotWrapReflPortB100InPlaceScrub_poly_stack {Var : Type}
    {mCoin nInner kOut n Wp wWork tPotU tPotC : ℕ} {peOut : BitAssignment kOut → PotExpectFn}
    {S : Wire n → Prop} (hn : nInner ≤ 24) (hm39 : 39 ≤ mCoin) (hInner : 39 + nInner ≤ mCoin)
    (hwLo : 232 ≤ wWork) (hwHi : wWork ≤ 886) (hWp : Wp ≤ 609) (hFit : 100 + Wp ≤ wWork)
    (rSub : QRegister kOut 41)
    (oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut) (v : Var)
    (rTot : QRegister dLayout n) (isCsel : Bool)
    (hAct : ∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rTot w)) :
    DynWires S (pPotWrapReflPortB100InPlaceScrub wWork hwLo hwHi rSub (toCoin24InPlaceOfN hn oN) hWp
    v rTot isCsel) := by
  have hSc : CircWires S (cScrubNucFlags3 rTot) := circWires_cScrubNucFlags3 rTot
    (hAct wOut0 (by simp only [ActiveOuterCoinStackOf, val_wOut0]; omega))
        (hAct wOut1 (by simp only [ActiveOuterCoinStackOf, val_wOut1]; omega))
    (hAct wOut14 (by simp only [ActiveOuterCoinStackOf, val_wOut14]; omega))
        (hAct wOut15 (by simp only [ActiveOuterCoinStackOf, val_wOut15]; omega))
    (hAct wOut32 (by simp only [ActiveOuterCoinStackOf, val_wOut32]; omega))
        (hAct wOut34 (by simp only [ActiveOuterCoinStackOf, val_wOut34]; omega))
    (hAct wOut35 (by simp only [ActiveOuterCoinStackOf, val_wOut35]; omega))
  refine ⟨hSc,
      dynWires_pPotWrapReflPortB151InPlace_skipPoly hn oN (by omega) v (rTot.compose (rPermPotNuc3
      wWork hwLo hwHi)) (rCoinExtOut hk0_le72_wstate rSub) isCsel (fun j hj ↦ hAct _ ?_)
      (fun j ↦ hAct _ ?_), hSc⟩
  · refine activeStackPoly_of_activeStack74_lt hInner (activeOuterCoinStack_rPermPotNuc3_potPortB151
        hwLo hwHi hWp hFit j (by omega)) ?_
    let hMax := maxWp24_le_738 (by omega : Wp ≤ 738)
    rcases val_rPotZeroNEremPortB151_skipPoly_lt hn hMax j hj with hlt | heq
    · let x := (rPotZeroNEremPortB151 (max Wp 24) hMax j).val;
      have hxlt : x < 7256 + nInner :=
          hlt; rw [val_rPermPotNuc3]; change swapNucFlags3TopVal wWork (permPot103Val x) < 7256 +
          nInner ∨ swapNucFlags3TopVal wWork (permPot103Val x) = 7297
      set y := permPot103Val x
      have hy : y = permPot103Val x := rfl; unfold permPot103Val at hy; unfold swapNucFlags3TopVal
      split_ifs at hy ⊢ <;> omega
    · rw [val_rPermPotNuc3, heq, show permPot103Val 7297 = 7297 by decide, swapNucFlags3TopVal]
      split_ifs <;> omega
  · have hb := val_rCoinExtOut_bounds hk0_le72_wstate rSub j
    have hFix1 : rPermPot103 (rCoinExtOut hk0_le72_wstate rSub j) =
        rCoinExtOut hk0_le72_wstate rSub j :=
        rPermPot103_fix_of_bounds _ (Or.inr (Or.inr (by omega)))
    have hFix2 : rSwapNucFlags3Top wWork hwLo hwHi (rCoinExtOut hk0_le72_wstate rSub j) =
        rCoinExtOut hk0_le72_wstate rSub j := rSwapNucFlags3Top_fix hwLo hwHi _ (by omega)
    change ActiveOuterCoinStackOf 23 wWork mCoin (rSwapNucFlags3Top wWork hwLo hwHi (rPermPot103
        (rCoinExtOut hk0_le72_wstate rSub j))); rw [hFix1, hFix2]; unfold ActiveOuterCoinStackOf
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
end QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin
open PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.ProviderCoreFused
open PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ProviderZeroFloor
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.Sub5885 PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.FastQft8 PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
    PgBase.phaseGradientState

def rLcuPolyLayout (mCoin : ℕ) (hm80 : mCoin ≤ 80) : QRegister (mCoin + 2) dLayout :=
    (locAncPoly systemQubits_frozen scrWLayout).compose (lcuSubLGen (hpStack mCoin hm80))
theorem val_rLcuPolyLayout {mCoin : ℕ} (hm80 : mCoin ≤ 80) (i : Fin (mCoin + 2)) :
    (rLcuPolyLayout mCoin hm80 i).val = 7215 + i.val := by
  have hs : systemQubits_frozen = 5616 := hSys5616_fused;
  have _ :=
      i.isLt; dsimp only [rLcuPolyLayout, locAncPoly, lcuSubLGen, scrLLayout,
      QRegister.compose_apply, QRegister.block_apply_val]; omega
theorem rLcuPolyLayout_active_stack {wWork mCoin : ℕ} (hm80 : mCoin ≤ 80) (i : Fin (mCoin + 2)) :
    ActiveOuterCoinStackOf 23 wWork mCoin (rLcuPolyLayout mCoin hm80 i) := by
  unfold ActiveOuterCoinStackOf; rw [val_rLcuPolyLayout]; have := i.isLt; omega
theorem rRetPoly_lt {mCoin : ℕ} (hm80 : mCoin ≤ 80) (j : Fin (80 - mCoin)) : (7217 + mCoin) +
    j.val < dLayout := by have hd : dLayout = 7298 := hDLayout_w0; have := j.isLt; omega
theorem rRetPoly_inj {mCoin : ℕ} (hm80 : mCoin ≤ 80) : Function.Injective (fun j : Fin (80 -
    mCoin) ↦ (⟨(7217 + mCoin) + j.val, rRetPoly_lt hm80 j⟩ : Wire dLayout)) :=
  fun a b h ↦ Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega)

def rRetPolyLayout (mCoin : ℕ) (hm80 : mCoin ≤ 80) : QRegister (80 - mCoin) dLayout :=
    ⟨⟨fun j ↦ ⟨(7217 + mCoin) + j.val, rRetPoly_lt hm80 j⟩, rRetPoly_inj hm80⟩⟩
theorem val_rRetPolyLayout {mCoin : ℕ} (hm80 : mCoin ≤ 80) (j : Fin (80 - mCoin)) :
    (rRetPolyLayout mCoin hm80 j).val = (7217 + mCoin) + j.val := rfl
theorem hDisjHadPoly_layout {mCoin : ℕ} (hm80 : mCoin ≤ 80) (i : Fin (mCoin + 2)) :
    rLcuPolyLayout mCoin hm80 i ≠ wHasN1 := fun e ↦ by
  have hv := (congrArg Fin.val e).trans val_wHasN1_wstate
  rw [val_rLcuPolyLayout] at hv; omega
theorem hDisjHadRetPoly_layout {mCoin : ℕ} (hm80 : mCoin ≤ 80) (j : Fin (80 - mCoin)) :
    rRetPolyLayout mCoin hm80 j ≠ wHasN1 := fun e ↦ by
  have hv := (congrArg Fin.val e).trans val_wHasN1_wstate
  rw [val_rRetPolyLayout] at hv; omega

def cHadPolyFwdLayout (mCoin : ℕ) (hm80 : mCoin ≤ 80) : Circuit dLayout :=
    hadamardRegCirc (mCoin + 2) (rLcuPolyLayout mCoin hm80)
def cHadPolyInvLayout (mCoin : ℕ) (hm80 : mCoin ≤ 80) : Circuit dLayout :=
    (hadamardRegCirc (mCoin + 2) (rLcuPolyLayout mCoin hm80)).inverse
noncomputable def uHadPolyLayout (mCoin : ℕ) (hm80 : mCoin ≤ 80) : Unitary (2 ^ dLayout) :=
  (hadamardRegSym (Var := Unit) wHasN1 (mCoin + 2) (rLcuPolyLayout mCoin hm80)
    (hDisjHadPoly_layout hm80)).unitary

noncomputable def uHadRetPolyLayout (mCoin : ℕ) (hm80 : mCoin ≤ 80) : Unitary (2 ^ dLayout) :=
  (hadamardRegSym (Var := Unit) wHasN1 (80 - mCoin) (rRetPolyLayout mCoin hm80)
    (hDisjHadRetPoly_layout hm80)).unitary

theorem eval_cHadPolyFwdLayout {mCoin : ℕ} (hm80 : mCoin ≤ 80) :
    (cHadPolyFwdLayout mCoin hm80).eval = uHadPolyLayout mCoin hm80 :=
    eval_hadamardRegCirc wHasN1 (mCoin + 2) (rLcuPolyLayout mCoin hm80) (hDisjHadPoly_layout hm80)
theorem eval_cHadPolyInvLayout {mCoin : ℕ} (hm80 : mCoin ≤ 80) :
    (cHadPolyInvLayout mCoin hm80).eval = (uHadPolyLayout mCoin hm80)⁻¹ := by
  unfold cHadPolyInvLayout uHadPolyLayout;
  rw [Circuit.eval_inverse, eval_hadamardRegCirc wHasN1 (mCoin + 2) (rLcuPolyLayout mCoin hm80)
      (hDisjHadPoly_layout hm80)]
theorem uHad82Layout_eq_mul_poly {mCoin : ℕ} (hm80 : mCoin ≤ 80) : uHad82Layout =
    uHadRetPolyLayout mCoin hm80 * uHadPolyLayout mCoin hm80 := by
  have he82 := (eval_hadamardRegCirc wHasN1 82 rLcu82Layout hDisjHad82_layout).symm
  have hc82 : (hadamardRegCirc 82 rLcu82Layout).eval =
      (hadamardRegCirc (mLayout + 2) rLcu82Layout).eval := rfl
  have heL :=
      eval_hadamardRegCirc wHasN1 (mCoin + 2) (rLcuPolyLayout mCoin hm80)
      (hDisjHadPoly_layout hm80); have heR :=
                                    eval_hadamardRegCirc wHasN1 (80 - mCoin)
                                    (rRetPolyLayout mCoin hm80) (hDisjHadRetPoly_layout hm80)
  have hsp :=
      eval_hadamardRegCirc_split_wstate (mCoin + 2) (80 - mCoin) (mLayout + 2)
      (by dsimp [mLayout]; omega) (rLcuPolyLayout mCoin hm80)
      (rRetPolyLayout mCoin hm80) rLcu82Layout
    (fun i hi hm' ↦ Fin.ext (by rw [val_rLcu82Layout, val_rLcuPolyLayout]))
        (fun j hj hm' ↦
        Fin.ext (by rw [val_rLcu82Layout, val_rRetPolyLayout]; (try dsimp only); omega))
  unfold uHad82Layout uHadPolyLayout uHadRetPolyLayout; rw [he82, hc82, hsp, heL, heR]
theorem uHadRetPolyLayout_eq_embed {mCoin : ℕ} (hm80 : mCoin ≤ 80) :
    let u0 := (hadamardRegCirc (80 - mCoin) (QRegister.whole (80 - mCoin))).eval
    uHadRetPolyLayout mCoin hm80 = (rRetPolyLayout mCoin hm80).embedUnitary u0 ∧
        (uHadRetPolyLayout mCoin hm80)⁻¹ = (rRetPolyLayout mCoin hm80).embedUnitary u0⁻¹ := by
  have he : uHadRetPolyLayout mCoin hm80 =
      (rRetPolyLayout mCoin hm80).embedUnitary (hadamardRegCirc (80 - mCoin)
      (QRegister.whole (80 - mCoin))).eval :=
      (eval_hadamardRegCirc wHasN1 (80 - mCoin) (rRetPolyLayout mCoin hm80)
      (hDisjHadRetPoly_layout hm80)).symm.trans (Coin70Lift.eval_hadamardRegCirc_eq_embed_c70 (80 -
      mCoin) (rRetPolyLayout mCoin hm80))
  exact ⟨he, by rw [he, QRegister.embedUnitary_inv]⟩

theorem hoffStackPoly_bounds {mCoin k : ℕ} (hm80 : mCoin ≤ 80) {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpStack mCoin hm80))
    (scrSubLGen (hpStack mCoin hm80)) r) (j : Fin k) : (5616 ≤ (r j).val ∧ (r j).val < 5650) ∨
    (7217 + mCoin ≤ (r j).val ∧ (r j).val ≤ 7296) ∨ (r j).val = 7297 := by
  obtain ⟨u, hu, hnl, hns⟩ := hoff j; have hs : systemQubits_frozen = 5616 := hSys5616_fused;
  have huLt : u.val < 1682 := ancWOfScr_layout_odd ▸ u.isLt
  have hrv : (r j).val = 5616 + u.val := by
    have hv := congrArg Fin.val hu.symm; dsimp [locAncPoly, QRegister.block_apply_val] at hv; omega
  exact if h1 : u.val < 34 then Or.inl ⟨by omega, by omega⟩
    else if h2 : u.val < 1599 then False.elim (hns ⟨⟨u.val - 34, by omega⟩,
        Fin.ext (by dsimp [scrSubLGen, QRegister.block_apply_val]; omega)⟩)
    else if h3 : u.val < 1599 + (mCoin + 2) then False.elim (hnl ⟨⟨u.val - 1599, by omega⟩,
        Fin.ext (by dsimp [lcuSubLGen, scrLLayout, QRegister.block_apply_val]; omega)⟩)
    else if h4 : u.val < 1681 then Or.inr (Or.inl ⟨by omega, by omega⟩)
    else Or.inr (Or.inr (by omega))

theorem uPotReflZeroNErem_Nonly_comm_of_disj {nInner : ℕ} (hn : nInner ≤ 24)
    {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect)
    (hN : ReflPotSliceNOnly nInner spec) (isCsel : Bool) {k : ℕ} (r : QRegister k dLayout)
    (hDisj : ∀ (j : Fin 146) (i : Fin k), ((isCsel = true ∧ j.val = 0) ∨ (1 ≤ j.val ∧ j.val < 105 +
    nInner)) → potZeroNEremWireFn 0 pot0_le_690 j ≠ r i) (M : Operator (2 ^ k)) :
    Commute (uPotReflZeroNErem spec isCsel).1 (r.embedMatrix M) := by
  have hkeep : ∀ (δ : BitAssignment dLayout) (η : BitAssignment k) (c : ℕ)
      (hc : c < 146), ((isCsel = true ∧ c = 0) ∨ (1 ≤ c ∧ c < 105 + nInner)) →
      writeReg δ r η (rPot0Layout ⟨c, hc⟩) = δ (rPot0Layout ⟨c, hc⟩) := fun δ η c hc hcond ↦
      writeReg_apply_of_not_mem δ r η (rPot0Layout ⟨c, hc⟩) fun ⟨i, hi⟩ ↦
      hDisj ⟨c, hc⟩ i hcond hi.symm
  have hC24 (δ : BitAssignment dLayout) (η : BitAssignment k) (off : ℕ) (hOff : off + 24 ≤ 146 + 0)
      (hbnd : 1 ≤ off ∧ off + 24 ≤ 105 + nInner) :
      coordOfReg24 (rPot0Layout.compose (QRegister.block off 24 hOff))
          (writeReg δ r η) = coordOfReg24 (rPot0Layout.compose (QRegister.block off 24 hOff)) δ :=
    funext fun ax ↦ congrArg byteOfBits (funext fun b ↦ hkeep δ η (off + (8 * ax.val + b.val))
      ((fun _h ↦ by omega) (PotSelectWiring.coordOfReg24_lt ax b))
          (Or.inr ((fun _h ↦ by omega) (PotSelectWiring.coordOfReg24_lt ax b))))
  have hZN (δ : BitAssignment dLayout) (η : BitAssignment k) (m : Fin 41) (hm : m.val < nInner) :
      writeReg δ r η (rPotCoin41 rPot0Layout m) = δ (rPotCoin41 rPot0Layout m) :=
      hkeep δ η (105 + m.val) (by omega) (Or.inr (by omega))
  have hEvalN (δ : BitAssignment dLayout) (η : BitAssignment k) :
      (∀ m : Fin 41, m.val < nInner →
          potOracleCoinEval spec.coinSwap rPot0Layout (writeReg δ r η) m =
          potOracleCoinEval spec.coinSwap rPot0Layout δ m) ∧
      potOracleBitEval spec.phaseBit rPot0Layout (writeReg δ r η) =
          potOracleBitEval spec.phaseBit rPot0Layout δ := by
    dsimp only [potOracleCoinEval, potOracleBitEval]
    rw [hkeep δ η 1 (by omega) (Or.inr (by omega)), hkeep δ η 4 (by omega) (Or.inr (by omega)),
        hkeep δ η 5 (by omega) (Or.inr (by omega)),
        hkeep δ η 6 (by omega) (Or.inr (by omega)), hkeep δ η 7 (by omega) (Or.inr (by omega)),
            hkeep δ η 8 (by omega) (Or.inr (by omega)),
        hC24 δ η 9 PotSelectWiring.potBlkNucA_le (by omega),
            hC24 δ η 33 PotSelectWiring.potBlkNucB_le (by omega),
        hC24 δ η 57 PotSelectWiring.potBlkElecA_le (by omega),
            hC24 δ η 81 PotSelectWiring.potBlkElecB_le (by omega)]
    exact hN.1 _ _ _ _ _ _ _ _ _ _ (hZN δ η)
  refine ReflStage4.signedPermUnitary_comm_embedMatrix _ _ _ r (fun δ η ↦ ?_) (fun δ η ↦ ?_) M
  · have hgEq : potGateActive4 isCsel rPot0Layout (writeReg δ r η) =
        potGateActive4 isCsel rPot0Layout δ := by
      dsimp only [potGateActive4, wPotLocQ, wPotIsPot]
      by_cases hC : isCsel = true
      · rw [ite_eq_left hC, ite_eq_left hC, hkeep δ η 0 (by omega)
            (Or.inl ⟨hC, rfl⟩), hkeep δ η 2 (by omega) (Or.inr (by omega))]
      · rw [ite_eq_right hC, ite_eq_right hC, hkeep δ η 2 (by omega) (Or.inr (by omega))]
    dsimp only [potReflSwap4]; rw [hgEq]
    split_ifs
    · funext w
      by_cases hwC : ∃ m : Fin 41, rPotCoin41 rPot0Layout m = w
      · obtain ⟨m, rfl⟩ := hwC; rw [writeReg_apply_reg]
        by_cases hmN : m.val < nInner
        · simpa only [writeReg_apply_of_not_mem _ r η (rPotCoin41 rPot0Layout m)
              (fun ⟨i, hi⟩ ↦ hDisj ⟨105 + m.val,
              by omega⟩ i (Or.inr (by (try dsimp only); omega)) hi.symm),
              writeReg_apply_reg] using (hEvalN δ η).1 m hmN
        · have hId (β) : potOracleCoinEval spec.coinSwap rPot0Layout β m =
              β (rPotCoin41 rPot0Layout m) := hN.2 _ _ _ _ _ _ _ _ _ m hmN
          rw [hId]
          by_cases hwR : ∃ i : Fin k, r i = rPotCoin41 rPot0Layout m
          · rcases hwR with ⟨i, hi⟩
            rw [← hi, writeReg_apply_reg, writeReg_apply_reg]
          · rw [writeReg_apply_of_not_mem _ r η _ hwR, writeReg_apply_of_not_mem _ r η _ hwR,
                writeReg_apply_reg, hId]
      · rw [writeReg_apply_of_not_mem _ (rPotCoin41 rPot0Layout) _ w hwC]
        by_cases hwR : ∃ i : Fin k, r i = w
        · obtain ⟨i, rfl⟩ := hwR; rw [writeReg_apply_reg, writeReg_apply_reg]
        · rw [writeReg_apply_of_not_mem _ r η w hwR, writeReg_apply_of_not_mem _ r η w hwR,
              writeReg_apply_of_not_mem _ (rPotCoin41 rPot0Layout) _ w hwC]
    · rfl
  · dsimp only [potReflPh4, wPotLocQ, wPotIsPot]
    rw [(hEvalN δ η).2]
    by_cases hC : isCsel = true
    · rw [ite_eq_left hC, ite_eq_left hC, hkeep δ η 0 (by omega)
          (Or.inl ⟨hC, rfl⟩), hkeep δ η 2 (by omega) (Or.inr (by omega))]
    · rw [ite_eq_right hC, ite_eq_right hC, hkeep δ η 2 (by omega) (Or.inr (by omega))]

theorem uAlignedKin2m1_98_comm_rRetPoly {mCoin : ℕ} (hm53 : 53 ≤ mCoin) (hm80 : mCoin ≤ 80)
    (M : Operator (2 ^ (80 - mCoin))) :
    Commute uAlignedKinIdeal2m1Layout.1 ((rRetPolyLayout mCoin hm80).embedMatrix M) ∧
    Commute uAlignedKinCat2m1_98UselLayout.1 ((rRetPolyLayout mCoin hm80).embedMatrix M) ∧
    Commute uAlignedKinCat2m1_98CselLayout.1 ((rRetPolyLayout mCoin hm80).embedMatrix M) := by
  let rC := rRetPolyLayout mCoin hm80; have hd : dLayout = 7298 := hDLayout_w0
  have cConj {W V : Unitary (2 ^ dLayout)} (cW : Commute W.1 (rC.embedMatrix M))
      (cV : Commute V.1 (rC.embedMatrix M)) : Commute (W⁻¹ * V * W).1 (rC.embedMatrix M) :=
    Commute.mul_left (Commute.mul_left (SelectFastQft8Gidney.unitary_inv_comm W _ cW) cV) cW
  have neRet {w : Wire dLayout} (hw : w.val < 7270 ∨ 7297 ≤ w.val) (j : Fin (80 - mCoin)) : w ≠
      rC j := fun e ↦ by
    rcases (⟨j.isLt, (congrArg Fin.val e).trans (val_rRetPolyLayout hm80 j)⟩ : _ ∧ _) with ⟨_, hv⟩
    omega
  have cA0 : Commute uKinAlign0Layout.1 (rC.embedMatrix M) :=
      fwdCirc_comm_embedMatrix_of_disj rC (cpWires_pKinAlign0
    (fun m ↦ neRet (by rw [val_rAlignLayout]; omega))
    (fun i ↦ neRet (by rw [val_rOut40Layout]; omega))) M
  have cSp : Commute uSpeciesSwap50Layout.1 (rC.embedMatrix M) :=
      embedUnitary_comm_of_disjoint rSpeciesSwap50Layout _ rC
    (disj_of_ne fun i ↦
        neRet (by rw [rSp50_eq_fn_w0, val_speciesSwap50WireFn]; split_ifs <;> omega)) M
  have cMux : Commute uMux27Layout.1 (rC.embedMatrix M) :=
      embedUnitary_comm_of_disjoint rMux27Layout _ rC
    (disj_of_ne fun i ↦ neRet (by rw [rMux27_eq_fn_w0, val_mux27WireFn]; split_ifs <;> omega)) M
  have dP : rPKinLayout.DisjointWires rC := disj_of_ne fun i ↦
      neRet (by rw [val_rPKinLayout]; omega)
  have cQid : Commute (qft8Stg3IdealU scrWLayout rPKinLayout).1 (rC.embedMatrix M) :=
    embedUnitary_comm_of_disjoint rPKinLayout _ rC dP M
  have cQdpost := embedUnitary_comm_of_disjoint rPKinLayout (dPost8U * qftGridUnitary) rC dP M
  have cMid : Commute uKinMid2m1UselLayout.1 (rC.embedMatrix M) :=
      embedUnitary_comm_of_disjoint rKin226Layout _ rC
    (disj_of_ne fun i ↦ neRet (by
      rw [show (rKin226Layout i).val = (kin226WireFn i).val from rfl, val_kin226WireFn];
          split_ifs <;> omega)) M
  have cQcat :
      Commute (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout).1 (rC.embedMatrix M) := by
    let rCln := qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout
    have hCln (i) : ∀ j, rCln i ≠ rC j :=
        neRet (by rw [qft8Stg3Clean13_eq_workInner, val_rWorkInnerLayout]; dsimp; omega)
    have abQ :=
        andBracketWires_polyPostCancelT5Qft8Bracket98 (P := fun w ↦ ∀ j : Fin (80 - mCoin), w ≠
        rC j)
      (locCat8SharedCompactGen scrWLayout) rPKinLayout (qft8Stg3Delta7 scrWLayout offKinLayout
          hoffKinLayout)
      (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout)
          (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
      (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
          (qft8Stg3_delta7_disj_cat8 hoffKinLayout)
      (qft8Stg3_delta7_disj_carry6 hoffKinLayout) (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
      (qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout)
          (fun c ↦ neRet (by rw [val_locCat8_layout]; omega))
      (fun i j e ↦ disj_ne dP i j e)
      (fun i j e ↦ hCln ⟨i.val, by omega⟩ j ((qft8Stg3_clean13_sub_delta7 hoffKinLayout ⟨i.val,
          by omega⟩).trans e))
      (fun i j e ↦ hCln ⟨7 + i.val, by omega⟩ j ((qft8Stg3_clean13_sub_carry6 hoffKinLayout ⟨i.val,
          by omega⟩).trans e))
    have cP13 := rCln.embedMatrix_comm_of_disjoint rC (disj_of_ne hCln) (compProj 0) M
    unfold qft8PostCancel98CatU polyPostCancelCleanUnitary spliceUnitary spliceUnitaryMat
    exact Commute.add_left (Commute.mul_left (circ_comm_embedMatrix_c70 rC M
        (circWires_toCircuit_c70 abQ)) cP13)
      (Commute.mul_left cQdpost (Commute.sub_left (Commute.one_left _) cP13))
  have cId : Commute uAlignedKinIdeal2m1Layout.1 (rC.embedMatrix M) :=
      cConj cA0 (cConj cSp (cConj cMux (cConj cQid cMid)));
      have cUsel : Commute uAlignedKinCat2m1_98UselLayout.1 (rC.embedMatrix M) :=
      cConj cA0 (cConj cSp (cConj cMux (cConj cQcat cMid)));
      let Pq :=
      projOneQCompactGen scrWLayout; have sKin :=
                                       csel_conj_unitary Pq uKinAlign0Layout
                                       uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
                                       comm_pq.2.eq uKin2m1_98Layout_props.1
                                       uKin2m1_98Layout_props.2.1
  have cPq : Commute Pq (rC.embedMatrix M) :=
      (QRegister.singleton wLocQLayout).embedMatrix_comm_of_disjoint rC
    (disj_of_ne fun i j e ↦ neRet (w := wLocQLayout) (by rw [val_wLocQLayout]; omega) j
      ((by fin_cases i; rfl : wLocQLayout = QRegister.singleton wLocQLayout i).trans e))
          (compProj 1) M
  refine ⟨cId, cUsel, ?_⟩
  unfold Commute SemiconjBy
  unfold uAlignedKinCat2m1_98CselLayout uAlignedKinCat2m1_98UselLayout at *
  rw [sKin.1]
  exact Commute.add_left (Commute.sub_left (Commute.one_left _) cPq) (Commute.mul_left cPq cUsel)

theorem uStage1Clean_comm_rRetPoly {mCoin : ℕ} (hm39 : 39 ≤ mCoin) (hm80 : mCoin ≤ 80)
    (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (M : Operator (2 ^ (80 - mCoin))) :
    Commute (uStage1Clean_c70 decodeCoin).1 ((rRetPolyLayout mCoin hm80).embedMatrix M) := by
  rw [uStage1Clean_eq_embed81_wstate decodeCoin]
  exact rStage1Clean81_wstate.embedMatrix_comm_of_disjoint (rRetPolyLayout mCoin hm80)
      (disj_of_ne fun i j e ↦ by
    have hi := i.isLt; have hj := j.isLt
    by_cases h40 : i.val < 40
    · have hv :=
          congrArg Fin.val ((QRegister.concat_apply_left rOut40Layout rOuter41Layout_wstate
          hDisjOut40Outer41_wstate ⟨i.val, h40⟩).symm.trans e)
      rw [val_rOut40Layout, val_rRetPolyLayout] at hv; omega
    · have hiEq : i = Fin.natAdd 40 ⟨i.val - 40, by omega⟩ :=
          Fin.ext (by (try dsimp [Fin.natAdd]); omega)
      have hv :=
          congrArg Fin.val ((QRegister.concat_apply_right rOut40Layout rOuter41Layout_wstate
          hDisjOut40Outer41_wstate ⟨i.val - 40, by omega⟩).symm.trans (hiEq ▸ e))
      rw [val_rOuter41Layout_wstate, val_rRetPolyLayout] at hv; omega) _ M

theorem wNoHadClean_comm_rRetPoly {mCoin : ℕ} (hm39 : 39 ≤ mCoin) (hm80 : mCoin ≤ 80)
    (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (M : Operator (2 ^ (80 - mCoin))) :
    Commute (wNoHad (uStage1Clean_c70 decodeCoin)).1 ((rRetPolyLayout mCoin hm80).embedMatrix M) ∧
    Commute ((wNoHad (uStage1Clean_c70 decodeCoin))⁻¹).1 ((rRetPolyLayout mCoin hm80).embedMatrix
    M) := by
  let rRet := rRetPolyLayout mCoin hm80
  have dE : ∀ (i : Fin (routerWidth 187 8)) (j : Fin (80 - mCoin)), rElecLayout i ≠ rRet j :=
      fun i j e ↦ by
    have hi : i.val < 5056 := hEW5056 ▸ i.isLt; have hj := j.isLt
    have hv := congrArg Fin.val e; have hev : (rElecLayout i).val = (elecRouterWireFn i).val := rfl
    rw [hev, val_elecRouterWireFn, val_rRetPolyLayout] at hv; split_ifs at hv <;> omega
  have dN : ∀ (i : Fin (routerWidth 47 6)) (j : Fin (80 - mCoin)), rNucLayout i ≠ rRet j :=
      fun i j e ↦ by
    have hb := val_rNuc_bounds i; have hj := j.isLt
    have hv := congrArg Fin.val e; rw [val_rRetPolyLayout] at hv; omega
  have cWnh : Commute (wNoHad (uStage1Clean_c70 decodeCoin)).1 (rRet.embedMatrix M) := by
    unfold wNoHad; rw [Submonoid.coe_mul, Submonoid.coe_mul]
    exact Commute.mul_left (comm_uRouterSwapConj_embedMat_pot rElecLayout rRet dE M)
        (Commute.mul_left (comm_uRouterSwapConj_embedMat_pot rNucLayout rRet dN M)
        (uStage1Clean_comm_rRetPoly hm39 hm80 decodeCoin M))
  exact ⟨cWnh,
      SelectFastQft8Gidney.unitary_inv_comm (wNoHad (uStage1Clean_c70 decodeCoin)) _ cWnh⟩

theorem uPreExt_zero_eq_hadPoly {mCoin : ℕ} (hm39 : 39 ≤ mCoin) (hm80 : mCoin ≤ 80)
    (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (u4 : Unitary (2 ^ dLayout))
    (hu4 : ∀ M : Operator (2 ^ (80 - mCoin)),
    Commute u4.1 ((rRetPolyLayout mCoin hm80).embedMatrix M)) :
    uPreExt hk0_le72_wstate decodeCoin u4 = (uHadPolyLayout mCoin hm80)⁻¹ *
    (wNoHad (uStage1Clean_c70 decodeCoin))⁻¹ * u4 * wNoHad (uStage1Clean_c70 decodeCoin) *
    uHadPolyLayout mCoin hm80 := by
  obtain ⟨hHRet, _⟩ := uHadRetPolyLayout_eq_embed hm80;
  let Wnh := wNoHad (uStage1Clean_c70 decodeCoin); let HRet := uHadRetPolyLayout mCoin hm80;
  let HPol := uHadPolyLayout mCoin hm80
  have cWnhHRet : Wnh * HRet = HRet * Wnh := Subtype.ext (by
      dsimp only [HRet];
      rw [Submonoid.coe_mul, Submonoid.coe_mul, hHRet, QRegister.embedUnitary_val]
      exact (wNoHadClean_comm_rRetPoly hm39 hm80 decodeCoin _).1.eq)
  have cU4HRet : u4 * HRet = HRet * u4 := Subtype.ext (by
      dsimp only [HRet];
      rw [Submonoid.coe_mul, Submonoid.coe_mul, hHRet, QRegister.embedUnitary_val]
      exact (hu4 _).eq)
  unfold uPreExt preConj wFull;
  rw [uHadCoinExt_zero_eq_one_wstate, inv_one, one_mul, mul_one, uHad82Layout_eq_mul_poly hm80];
  change (Wnh * (HRet * HPol))⁻¹ * u4 * (Wnh * (HRet * HPol)) = HPol⁻¹ * Wnh⁻¹ * u4 * Wnh * HPol
  rw [show Wnh * (HRet * HPol) = HRet * (Wnh * HPol) by rw [← mul_assoc, cWnhHRet, mul_assoc],
      _root_.mul_inv_rev, _root_.mul_inv_rev]
  calc HPol⁻¹ * Wnh⁻¹ * HRet⁻¹ * u4 * (HRet * (Wnh * HPol))
      = HPol⁻¹ * Wnh⁻¹ * (HRet⁻¹ * (u4 * HRet)) * (Wnh * HPol) := by simp only [mul_assoc]
    _ = HPol⁻¹ * Wnh⁻¹ * ((HRet⁻¹ * HRet) * u4) * (Wnh * HPol) := by
      rw [cU4HRet, mul_assoc HRet⁻¹ HRet u4]
    _ = HPol⁻¹ * Wnh⁻¹ * u4 * Wnh * HPol := by rw [inv_mul_cancel, one_mul]; simp only [mul_assoc]
theorem uPreExt_zero_comm_rRetPoly {mCoin : ℕ} (hm39 : 39 ≤ mCoin) (hm80 : mCoin ≤ 80)
    (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (u4 : Unitary (2 ^ dLayout))
    (hu4 : ∀ M : Operator (2 ^ (80 - mCoin)),
    Commute u4.1 ((rRetPolyLayout mCoin hm80).embedMatrix M)) (M : Operator (2 ^ (80 - mCoin))) :
    Commute (uPreExt hk0_le72_wstate decodeCoin u4).1 ((rRetPolyLayout mCoin hm80).embedMatrix M)
    := by
  rw [uPreExt_zero_eq_hadPoly hm39 hm80 decodeCoin u4 hu4];
  obtain ⟨cW, cWi⟩ := wNoHadClean_comm_rRetPoly hm39 hm80 decodeCoin M
  have cH : Commute (uHadPolyLayout mCoin hm80).1 ((rRetPolyLayout mCoin hm80).embedMatrix M) :=
    hadamardRegSym_comm_disjoint (Var := Unit) wHasN1 (mCoin + 2) (rLcuPolyLayout mCoin hm80)
        (hDisjHadPoly_layout hm80) (rRetPolyLayout mCoin hm80) (disj_of_ne fun i j e ↦ by
      rcases (⟨i.isLt, j.isLt, congrArg Fin.val e⟩ : _ ∧ _ ∧ _) with ⟨_, _, hv⟩
      rw [val_rLcuPolyLayout, val_rRetPolyLayout] at hv; omega) M
  have cHi : Commute ((uHadPolyLayout mCoin hm80)⁻¹).1 ((rRetPolyLayout mCoin hm80).embedMatrix M)
      :=
      SelectFastQft8Gidney.unitary_inv_comm (uHadPolyLayout mCoin hm80) _ cH;
      simp only [Submonoid.coe_mul]; exact (((cHi.mul_left cWi).mul_left (hu4 M)).mul_left
        cW).mul_left cH
theorem potZeroNEremWireFn_ne_rRetPoly {mCoin nInner : ℕ} (hm53 : 53 ≤ mCoin) (hm80 : mCoin ≤ 80)
    (hInner : 39 + nInner ≤ mCoin) (isCsel : Bool) (j : Fin 146) (i : Fin (80 - mCoin))
    (hcond : (isCsel = true ∧ j.val = 0) ∨ (1 ≤ j.val ∧ j.val < 105 + nInner)) :
        potZeroNEremWireFn 0 pot0_le_690 j ≠ rRetPolyLayout mCoin hm80 i := fun e ↦ by
  rcases (⟨j.isLt, i.isLt, (congrArg Fin.val e).trans (val_rRetPolyLayout hm80 i)⟩ : _ ∧ _ ∧
      _) with ⟨_, _, hv⟩
  rw [PhotochemistrySolution.PotSelectWiring.val_potZeroNEremWireFn] at hv
  split_ifs at hv <;> omega

theorem uStage4Refl2m1_98_Nonly_comm_rRetPoly {mCoin nInner : ℕ} (hn : nInner ≤ 24)
    (hm53 : 53 ≤ mCoin) (hm80 : mCoin ≤ 80) (hInner : 39 + nInner ≤ mCoin) {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) (hN : ReflPotSliceNOnly nInner spec)
    (M : Operator (2 ^ (80 - mCoin))) :
    Commute (uStage4ReflZeroNErem2m1Ideal spec).1 ((rRetPolyLayout mCoin hm80).embedMatrix M) ∧
    Commute (uStage4ReflZeroNErem2m1_98CatUsel spec).1 ((rRetPolyLayout mCoin hm80).embedMatrix M) ∧
    Commute (uStage4ReflZeroNErem2m1_98CatCsel spec).1 ((rRetPolyLayout mCoin hm80).embedMatrix M)
    := by
  obtain ⟨cKi, cKu, cKc⟩ := uAlignedKin2m1_98_comm_rRetPoly hm53 hm80 M
  exact ⟨cKi.mul_left (uPotReflZeroNErem_Nonly_comm_of_disj hn spec hN false (rRetPolyLayout mCoin
      hm80) (potZeroNEremWireFn_ne_rRetPoly hm53 hm80 hInner false) M),
    cKu.mul_left (uPotReflZeroNErem_Nonly_comm_of_disj hn spec hN false (rRetPolyLayout mCoin hm80)
        (potZeroNEremWireFn_ne_rRetPoly hm53 hm80 hInner false) M),
    cKc.mul_left (uPotReflZeroNErem_Nonly_comm_of_disj hn spec hN true (rRetPolyLayout mCoin hm80)
        (potZeroNEremWireFn_ne_rRetPoly hm53 hm80 hInner true) M)⟩

theorem uStage4ReflRev2m1_98_Nonly_comm_rRetPoly {mCoin nInner : ℕ} (hn : nInner ≤ 24)
    (hm53 : 53 ≤ mCoin) (hm80 : mCoin ≤ 80) (hInner : 39 + nInner ≤ mCoin) {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) (hN : ReflPotSliceNOnly nInner spec)
    (M : Operator (2 ^ (80 - mCoin))) :
    Commute (uStage4ReflRev2m1_98CatUsel spec).1 ((rRetPolyLayout mCoin hm80).embedMatrix M) ∧
    Commute (uStage4ReflRev2m1_98CatCsel spec).1 ((rRetPolyLayout mCoin hm80).embedMatrix M) := by
  obtain ⟨_, cKu, cKc⟩ := uAlignedKin2m1_98_comm_rRetPoly hm53 hm80 M
  exact ⟨(uPotReflZeroNErem_Nonly_comm_of_disj hn spec hN false (rRetPolyLayout mCoin hm80)
      (potZeroNEremWireFn_ne_rRetPoly hm53 hm80 hInner false) M).mul_left cKu,
    (uPotReflZeroNErem_Nonly_comm_of_disj hn spec hN true (rRetPolyLayout mCoin hm80)
        (potZeroNEremWireFn_ne_rRetPoly hm53 hm80 hInner true) M).mul_left cKc⟩

theorem uMuxExtOut_zero_comm_rRetPoly {mCoin kOut : ℕ} (hm39 : 39 ≤ mCoin) (hm80 : mCoin ≤ 80)
    (rSub : QRegister kOut 41) (uSlice : BitAssignment (0 + kOut) → Unitary (2 ^ dLayout))
    (hu : ∀ γω (M : Operator (2 ^ (0 + kOut))),
    Commute (uSlice γω).1 ((rCoinExtOut hk0_le72_wstate rSub).embedMatrix M))
    (hRet : ∀ γω (M : Operator (2 ^ (80 - mCoin))),
    Commute (uSlice γω).1 ((rRetPolyLayout mCoin hm80).embedMatrix M))
    (M : Operator (2 ^ (80 - mCoin))) :
    Commute (uMuxExtOut hk0_le72_wstate rSub uSlice hu).1 ((rRetPolyLayout mCoin hm80).embedMatrix
    M) := by
  let rCO := rCoinExtOut hk0_le72_wstate rSub; let rRet := rRetPolyLayout mCoin hm80
  have dCO : rCO.DisjointWires rRet := disj_of_ne fun u j e ↦ by
    have hb := val_rCoinExtOut_coinBand7256_wstate hk0_le72_wstate rSub u; have hj := j.isLt;
    have hv : (rCoinExtOut hk0_le72_wstate rSub u).val = (rRet j).val := congrArg Fin.val e
    rw [val_rRetPolyLayout] at hv; omega
  change (uMuxExtOut hk0_le72_wstate rSub uSlice hu).1 * rRet.embedMatrix M = rRet.embedMatrix M *
      (uMuxExtOut hk0_le72_wstate rSub uSlice hu).1
  rw [uMuxExtOut_val]; unfold muxMat_c70; rw [Finset.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun γω _ ↦ ?_
  have cProj : Commute (projBits_c70 rCO γω) (rRet.embedMatrix M) := by
    rw [projBits_eq_embedMatrix_c70 rCO γω]; exact rCO.embedMatrix_comm_of_disjoint rRet dCO _ M
  exact ((hRet γω M).mul_left cProj).eq

attribute [local irreducible] reflULGen
theorem selectLocalSpecGen_reflOuterSub2m1_98_stackPoly {mCoin nInner kOut w1 : ℕ}
    (hn : nInner ≤ 24) (hm53 : 53 ≤ mCoin) (hm80 : mCoin ≤ 80) (hInner : 39 + nInner ≤ mCoin)
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ}
    {wIdle : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (0 + kOut) →
    PotExpectFn} (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (0 + kOut), ReflPotSliceSpec (peKOut γω))
    (hNKOut : ∀ γω : BitAssignment (0 + kOut), ReflPotSliceNOnly nInner (specKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) {A : OpSys}
    (hAvgOp : (2 ^ 0 : ℂ)⁻¹ • ∑ γ : BitAssignment 0, ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
    bOuterZeroNErem decode (peKOut (concatBitsGen γ (outSubRawBits rSub c))) c) = A) :
    SelectLocalSpecGen (scrSubLGen (hpStack mCoin hm80))
    (lcuSubLGen (hpStack mCoin hm80)) A (sReflSliceOuterSub2m1_wstate hk0_le72_wstate rSub o1
    specKOut hCoin) (cselReflSliceOuterSub2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin)
    (reflULGen (hpStack mCoin hm80)) ∧
    (uselReflSliceOuterSub2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin).1 *
    cat8SharedProjCompactGen scrWLayout =
    (sReflSliceOuterSub2m1_wstate hk0_le72_wstate rSub o1 specKOut hCoin).1 *
    cat8SharedProjCompactGen scrWLayout := by
  have hm39 : 39 ≤ mCoin := by omega
  let rLcu := rLcuPolyLayout mCoin hm80;
  let rRet := rRetPolyLayout mCoin hm80; obtain ⟨h0, hCat⟩ :=
      selectLocalSpecGen_reflOuterSub2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin hAvgOp;
      let s4 :=
      stage4OuterSubUnitaryPkg_refl2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin;
      let uS :=
      sReflSliceOuterSub2m1_wstate hk0_le72_wstate rSub o1 specKOut hCoin;
      let P_scr := pScrExt 0 hk0_le72_wstate
  have hScrEq :
      ((locAncPoly systemQubits_frozen scrWLayout).compose (scrSubLGen (hpStack mCoin
      hm80))).basisOutcomeProjector 0 = P_scr := rfl
  have cPscr_ret (M : Operator (2 ^ (80 - mCoin))) : Commute P_scr (rRet.embedMatrix M) :=
    (rScrExt 0 hk0_le72_wstate).embedMatrix_comm_of_disjoint rRet (disj_of_ne fun i j e ↦ by
      have hi1565 : i.val < 1565 := i.isLt
      have hjLt := j.isLt
      have hv := congrArg Fin.val e
      rw [val_rScrExt, val_rRetPolyLayout] at hv; omega) (compProj 0) M
  have cS_ret (M : Operator (2 ^ (80 - mCoin))) : Commute uS.1 (rRet.embedMatrix M) := by
    have cPre :=
        uPreExt_zero_comm_rRetPoly hm39 hm80 decode (uIdMuxWState hk0_le72_wstate rSub o1 s4)
      (fun M' ↦ uMuxExtOut_zero_comm_rRetPoly hm39 hm80 rSub s4.uIdSlice (huId_wstate s4)
        (fun γω M'' ↦ (uStage4Refl2m1_98_Nonly_comm_rRetPoly hn hm53 hm80 hInner (specKOut γω)
            (hNKOut γω) M'').1) M') M
    have huS : uS.1 = (uPreExt hk0_le72_wstate decode (uIdMuxWState hk0_le72_wstate rSub o1 s4)).1 *
        P_scr + (1 - P_scr) :=
      unitaryOnProj_val (d := 2 ^ dLayout)
          (uPreExt hk0_le72_wstate decode (uIdMuxWState hk0_le72_wstate rSub o1 s4))
        (pScrExt 0 hk0_le72_wstate) (pScrExt_herm 0 hk0_le72_wstate)
            (pScrExt_idem 0 hk0_le72_wstate)
        (comm_pScrExt_id_wstate hk0_le72_wstate rSub o1 s4)
    rw [huS]
    exact (cPre.mul_left (cPscr_ret M)).add_left ((Commute.one_left _).sub_left (cPscr_ret M))
  have hL82_split :
      lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpExt 0 hk0_le72_wstate)) =
      lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpStack mCoin hm80)) *
      rRet.basisOutcomeProjector 0 := by
    obtain ⟨hSp, _⟩ := lcuProj_ext_split_c70 hk0_le72_wstate
    have h0P : (rCoinExt 0 hk0_le72_wstate).basisOutcomeProjector 0 = 1 := matrix_ext_ket fun ξ ↦ by
      rw [SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left (fun j ↦ Fin.elim0 j),
          Matrix.one_mulVec]
    rw [hSp, h0P, Matrix.one_mul]
    refine matrix_ext_ket fun β ↦ ?_
    change (rLcu82Layout.basisOutcomeProjector 0).mulVec _ = (rLcu.basisOutcomeProjector 0 *
        rRet.basisOutcomeProjector 0).mulVec _
    rw [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero,
        SelectRefl.ket_basisOutcomeProjector_zero]
    have hIff : (∀ a : Fin (mLayout + 2), β (rLcu82Layout a) = 0) ↔ (∀ i : Fin (mCoin + 2),
        β (rLcu i) = 0) ∧ (∀ j : Fin (80 - mCoin), β (rRet j) = 0) :=
      ⟨fun ha ↦
          ⟨fun i ↦
          (congrArg β (Fin.ext (by rw [val_rLcuPolyLayout, val_rLcu82Layout]))).trans (ha ⟨i.val,
          (fun _h ↦ by (try dsimp [mLayout]); omega) i.isLt⟩),
          fun j ↦
              (congrArg β
              (Fin.ext
              (by rw [val_rRetPolyLayout, val_rLcu82Layout]; (try dsimp); omega))).trans
              (ha ⟨(mCoin + 2) + j.val, (fun _h ↦ by (try dsimp [mLayout]); omega) j.isLt⟩)⟩,
       fun ⟨hL, hR⟩ a ↦ if hlt : a.val < mCoin + 2
         then (congrArg β (Fin.ext (by rw [val_rLcu82Layout, val_rLcuPolyLayout]))).trans
             (hL ⟨a.val, hlt⟩)
         else (congrArg β (Fin.ext (by
           have ha82 : a.val < 82 := a.isLt
           rw [val_rLcu82Layout, val_rRetPolyLayout]; (try dsimp); omega))).trans
           (hR ⟨a.val - (mCoin + 2), (fun (ha82 : a.val < 82) ↦ by omega) a.isLt⟩)⟩
    by_cases hR : ∀ j : Fin (80 - mCoin), β (rRet j) = 0
    · rw [ite_eq_left hR, PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
      by_cases hL : ∀ i : Fin (mCoin + 2), β (rLcu i) = 0
      · rw [ite_eq_left (hIff.mpr ⟨hL, hR⟩), ite_eq_left hL]
      · rw [ite_eq_right (fun ha ↦ hL (hIff.mp ha).1), ite_eq_right hL]
    · rw [ite_eq_right (fun ha ↦ hR (hIff.mp ha).2), ite_eq_right hR, Matrix.mulVec_zero]
  have hBlockPoly : lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpStack mCoin hm80)) *
      uS.1 * lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpStack mCoin hm80)) *
      ((locAncPoly systemQubits_frozen scrWLayout).compose (scrSubLGen (hpStack mCoin
      hm80))).basisOutcomeProjector 0 = (locSysPoly systemQubits_frozen scrWLayout).embedMatrix A *
      lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpStack mCoin hm80)) *
      ((locAncPoly systemQubits_frozen scrWLayout).compose (scrSubLGen (hpStack mCoin
      hm80))).basisOutcomeProjector 0 := by
    let LPol := lcuProjPoly systemQubits_frozen scrWLayout (lcuSubLGen (hpStack mCoin hm80));
    let PRet := rRet.basisOutcomeProjector 0; let rS := locSysPoly systemQubits_frozen scrWLayout;
    have hPolEq : LPol = rLcu.basisOutcomeProjector 0 := rfl
    have cLPol_ret (M : Operator (2 ^ (80 - mCoin))) : Commute LPol (rRet.embedMatrix M) :=
      rLcu.embedMatrix_comm_of_disjoint rRet (disj_of_ne fun i j e ↦ by
        rcases (⟨i.isLt, j.isLt, congrArg Fin.val e⟩ : _ ∧ _ ∧ _) with ⟨hiLt, hjLt, hv⟩
        rw [val_rLcuPolyLayout, val_rRetPolyLayout] at hv; omega) (compProj 0) M
    have cSys_ret (M : Operator (2 ^ (80 - mCoin))) : Commute (rS.embedMatrix A)
        (rRet.embedMatrix M) :=
      rS.embedMatrix_comm_of_disjoint rRet (disj_of_ne fun i j e ↦ by
        rcases (⟨i.isLt, j.isLt, (hSys5616_fused : systemQubits_frozen = 5616),
            congrArg Fin.val e⟩ : _ ∧ _ ∧ _ ∧ _) with
          ⟨hiLt, hjLt, hs5616, hv⟩
        rw [show (rS i).val = i.val from Nat.zero_add i.val, val_rRetPolyLayout] at hv;
            omega) A M
    have hPRet_idem : PRet * PRet = PRet := rRet.basisOutcomeProjector_mul_self 0;
    have h0b := h0.hblock
    have hScr0 :
        ((locAncPoly systemQubits_frozen scrWLayout).compose (scrSubLGen
        (hpExt 0 hk0_le72_wstate))).basisOutcomeProjector 0 = P_scr := rfl
    rw [hL82_split, hScr0] at h0b
    obtain ⟨c1, c2, c3⟩ :
        (PRet * uS.1 = uS.1 * PRet) ∧ (PRet * LPol = LPol * PRet) ∧ (PRet * P_scr = P_scr * PRet) :=
      ⟨(cS_ret (compProj 0)).symm.eq, (cLPol_ret (compProj 0)).symm.eq,
          (cPscr_ret (compProj 0)).symm.eq⟩
    have hLHS : (LPol * PRet) * uS.1 * (LPol * PRet) * P_scr = (LPol * uS.1 * LPol * P_scr) *
        PRet := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc PRet uS.1, c1, Matrix.mul_assoc uS.1,
          ← Matrix.mul_assoc PRet LPol, c2, Matrix.mul_assoc LPol,
          ← Matrix.mul_assoc PRet PRet, hPRet_idem, c3]
    have hRHS : rS.embedMatrix A * (LPol * PRet) * P_scr = (rS.embedMatrix A * LPol * P_scr) *
        PRet := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, c3, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [hLHS, hRHS] at h0b
    have hConjT {X : Operator (2 ^ dLayout)} {η : BitAssignment (80 - mCoin)}
        (hC : Commute X (uTogGen_c70 rRet η).1) :
        (uTogGen_c70 rRet η).1 * (X * PRet) * (uTogGen_c70 rRet η).1 = X * projBits_c70 rRet η := by
      unfold projBits_c70
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (uTogGen_c70 rRet η).1 X, hC.symm.eq, Matrix.mul_assoc X]
    have hProjEta (η : BitAssignment (80 - mCoin)) : (LPol * uS.1 * LPol * P_scr) *
        projBits_c70 rRet η = (rS.embedMatrix A * LPol * P_scr) * projBits_c70 rRet η := by
      let T := (uTogGen_c70 rRet η).1;
      have hTeq : T = rRet.embedMatrix (uTogLocal_c70 η).1 :=
          (congrArg Subtype.val (embedUnitary_uTogLocal_c70 rRet η)).symm
      have cLT : Commute (LPol * uS.1 * LPol * P_scr) T := by
        rw [hTeq];
        exact (((cLPol_ret _).mul_left (cS_ret _)).mul_left (cLPol_ret _)).mul_left (cPscr_ret _)
      have cRT : Commute (rS.embedMatrix A * LPol * P_scr) T := by
        rw [hTeq]; exact ((cSys_ret _).mul_left (cLPol_ret _)).mul_left (cPscr_ret _)
      exact (hConjT cLT).symm.trans ((congrArg (fun X ↦ T * X * T) h0b).trans (hConjT cRT))
    rw [hScrEq]
    calc LPol * uS.1 * LPol * P_scr
        = (LPol * uS.1 * LPol * P_scr) * ∑ η : BitAssignment (80 - mCoin), projBits_c70 rRet η := by
          rw [sum_projBits_c70 rRet, Matrix.mul_one]
      _ = ∑ η : BitAssignment (80 - mCoin), (LPol * uS.1 * LPol * P_scr) * projBits_c70 rRet η :=
          Matrix.mul_sum _ _ _
      _ = ∑ η : BitAssignment (80 - mCoin), (rS.embedMatrix A * LPol * P_scr) *
          projBits_c70 rRet η := Finset.sum_congr rfl fun η _ ↦ hProjEta η
      _ = rS.embedMatrix A * LPol * P_scr := by
        rw [← Matrix.mul_sum, sum_projBits_c70 rRet, Matrix.mul_one]
  refine ⟨
    { S_herm := h0.S_herm, S_scr := h0.S_scr, hblock := hBlockPoly,
      cselU_cat := h0.cselU_cat, reflU_eq := reflULGen_eq (hpStack mCoin hm80),
      S_comm := fun r M hoff ↦ commute_embedMatrix_of_singleton_wstate uS.1 r (fun j N ↦ by
        have hOff1 (h1 : (5616 ≤ (r j).val ∧ (r j).val < 5650) ∨ (r j).val = 7297) :
            Commute uS.1 ((QRegister.singleton (r j)).embedMatrix N) := by
          refine h0.S_comm (QRegister.singleton (r j)) N
            ((Coin70Lift.hoffExt_iff_layout_c70 hk0_le72_wstate _).mpr fun q ↦ ?_)
          fin_cases q
          rcases (⟨hSys5616_fused, ancWOfScr_layout_odd⟩ : _ ∧ _) with ⟨hs, h1682⟩
          have hm80s : mLayout = 80 := rfl
          have hscr1565 : scrLLayout = 1565 := rfl
          refine ⟨⟨(r j).val - 5616, by omega⟩,
              Fin.ext (by dsimp [locAncPoly, QRegister.block_apply_val]; omega),
            fun ⟨a, ha⟩ ↦ ?_, fun ⟨b, hb⟩ ↦ ?_⟩
          · have ha82 : a.val < 82 := a.isLt
            have hv := congrArg Fin.val ha
            dsimp [lcuSubLGen, QRegister.block_apply_val] at hv; omega
          · have hb1565 : b.val < 1565 := b.isLt
            have hv := congrArg Fin.val hb
            dsimp [scrSubLGen, QRegister.block_apply_val] at hv; omega
        rcases hoffStackPoly_bounds hm80 hoff j with hb1 | hb2 | hb3
        · exact hOff1 (Or.inl hb1)
        · rw [show QRegister.singleton (r j) = rRet.compose (QRegister.singleton ⟨(r j).val -
              (7217 + mCoin), by omega⟩) from
            congrArg QRegister.mk (Function.Embedding.ext fun q ↦ by
              fin_cases q;
                  exact Fin.ext
                  (by change (r j).val = (7217 + mCoin) + ((r j).val - (7217 + mCoin)); omega)),
            rRet.embedMatrix_compose]
          exact cS_ret _
        · exact hOff1 (Or.inr hb3)) M }, hCat⟩

attribute [local irreducible] sSliceWState cselSliceWState uselSliceWState
    sReflSliceOuterSub2m1_wstate stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate
    cat8SharedProjCompactGen

theorem selectLocalSpecGen_reflRevOuterSub2m1_98_stackPoly {mCoin nInner kOut w1 : ℕ}
    (hn : nInner ≤ 24) (hm53 : 53 ≤ mCoin) (hm80 : mCoin ≤ 80) (hInner : 39 + nInner ≤ mCoin)
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ}
    {wIdle : ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector} {peKOut : BitAssignment (0 + kOut) →
    PotExpectFn} (rSub : QRegister kOut 41) (o1 : Stage1ZeroNEremLayout w1 decode)
    (specKOut : ∀ γω : BitAssignment (0 + kOut), ReflPotSliceSpec (peKOut γω))
    (hNKOut : ∀ γω : BitAssignment (0 + kOut), ReflPotSliceNOnly nInner (specKOut γω))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) {A : OpSys}
    (hAvgOp : (2 ^ 0 : ℂ)⁻¹ • ∑ γ : BitAssignment 0, ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
    bOuterZeroNErem decode (peKOut (concatBitsGen γ (outSubRawBits rSub c))) c) = A) :
    SelectLocalSpecGen (scrSubLGen (hpStack mCoin hm80))
    (lcuSubLGen (hpStack mCoin hm80)) A (sReflSliceOuterSub2m1_wstate hk0_le72_wstate rSub o1
    specKOut hCoin) (cselReflRevSliceOuterSub2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin)
    (reflULGen (hpStack mCoin hm80)) ∧
    (uselReflRevSliceOuterSub2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin).1 *
    cat8SharedProjCompactGen scrWLayout =
    (sReflSliceOuterSub2m1_wstate hk0_le72_wstate rSub o1 specKOut hCoin).1 *
    cat8SharedProjCompactGen scrWLayout := by
  unfold cselReflRevSliceOuterSub2m1_98_wstate uselReflRevSliceOuterSub2m1_98_wstate;
  obtain ⟨hPol, _⟩ :=
      selectLocalSpecGen_reflOuterSub2m1_98_stackPoly hn hm53 hm80 hInner rSub o1 specKOut hNKOut
      hCoin hAvgOp; obtain ⟨hRev0, hRevCat⟩ :=
      selectLocalSpecGen_outerSubUnitary_wstate hk0_le72_wstate rSub o1
      (stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin) hAvgOp
  have hSEq := sSliceWState_reflRev_eq hk0_le72_wstate rSub o1 specKOut hCoin;
  have hCselCat := hRev0.cselU_cat; rw [hSEq] at hCselCat hRevCat
  exact ⟨{ S_herm := hPol.S_herm, S_comm := hPol.S_comm, S_scr := hPol.S_scr,
           hblock := hPol.hblock, cselU_cat := hCselCat, reflU_eq := hPol.reflU_eq }, hRevCat⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin
open HermitianMat PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr CleanWorkStep phaseFlipUnitary
  reflULGen bOuterZeroNErem

structure Stage25InPlacePolyPkg (mCoin nInner wWork w1 kOut Wp tStage25U tStage25C tPotU tPotC : ℕ)
    (hn : nInner ≤ 24)
    (decode : Fin (2 ^ 41) → ZeroNEremSector)
    (peOut : BitAssignment kOut → PotExpectFn)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (rSub : QRegister kOut 41)
    (oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut) where
  prog : ∀ {Var : Type} {n : ℕ}, Var → QRegister dLayout n → Bool → DynamicCircuit Var n
  counts : ∀ {Var : Type} [Finite Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool),
    (prog v rTot isCsel).count .T = (if isCsel then tStage25C else tStage25U) ∧
    (prog v rTot isCsel).count .TOFF = 0
  dynWires : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool),
    (∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rTot w)) →
    DynWires S (prog v rTot isCsel)
  step25 : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode)
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool)
    (X₁ : Operator (2 ^ n)),
    (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁ →
    let specKOut := spec41Of24_ipb (toCoin24InPlaceOfN hn oN).sliceSpec;
    let s4 := stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk0_le72_wstate rSub o1 specKOut hCoin
    let uStage4 :=
        if isCsel then uCselMuxWState hk0_le72_wstate rSub o1 s4 else uUselMuxWState hk0_le72_wstate
        rSub o1 s4
    let W₁ := rTot.embedUnitary (uStage1Clean_c70 decode);
    let Wnh_loc := wNoHad (uStage1Clean_c70 decode);
    let X₂ := (rTot.embedUnitary (Wnh_loc⁻¹ * uStage4 * Wnh_loc)).1 * X₁
    (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₂ = X₂ →
    SubspaceStep (W₁.1 * X₁) (W₁.1 * X₂) (prog v rTot isCsel)

def pSelectOfStage25InPlace_poly {Var : Type}
    {mCoin nInner wWork w1 tStage1 kOut n Wp tStage25U tStage25C tPotU tPotC : ℕ}
    (hm80 : mCoin ≤ 80) {hn : nInner ≤ 24} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peOut : BitAssignment kOut → PotExpectFn} (s1 : Stage1AsymRevPkg w1 tStage1 decode)
    {rSub : QRegister kOut 41}
    {oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut}
    (pkg25 : Stage25InPlacePolyPkg mCoin nInner wWork w1 kOut Wp tStage25U tStage25C tPotU tPotC hn
    decode peOut s1.o1 rSub oN) (v : Var) (rTot : QRegister dLayout n)
    (isCsel : Bool) : DynamicCircuit Var n :=
    .seq (.circuit ((cHadPolyFwdLayout mCoin hm80).onRegister rTot)) (.seq (s1.o1.fwdAmb v rTot)
    (.seq (pkg25.prog v rTot isCsel) (.seq (s1.revAmb v rTot)
    (.circuit ((cHadPolyInvLayout mCoin hm80).onRegister rTot)))))
def cOfSelectOfStage25InPlace_poly {Var : Type}
    {mCoin nInner wWork w1 tStage1 kOut n Wp tStage25U tStage25C tPotU tPotC : ℕ}
    (hm80 : mCoin ≤ 80) {hn : nInner ≤ 24} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peOut : BitAssignment kOut → PotExpectFn} (s1 : Stage1AsymRevPkg w1 tStage1 decode)
    {rSub : QRegister kOut 41}
    {oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut}
    (pkg25 : Stage25InPlacePolyPkg mCoin nInner wWork w1 kOut Wp tStage25U tStage25C tPotU tPotC hn
    decode peOut s1.o1 rSub oN) (isCsel : Bool) (v : Var) (rS : QRegister systemQubits_frozen n)
    (rA : QRegister (ancWOfScr scrWLayout) n) : DynamicCircuit Var n :=
    @dite _ (rS.DisjointWires rA) (decDisjSysAnc_top rS rA)
    (fun hd ↦ pSelectOfStage25InPlace_poly hm80 s1 pkg25 v (rS.concat rA hd) isCsel)
    (fun _ ↦ .circuit .identity)
theorem counts_pSelectOfStage25InPlace_poly {Var : Type} [Finite Var]
    {mCoin nInner wWork w1 tStage1 kOut n Wp tStage25U tStage25C tPotU tPotC : ℕ} [NeZero (2 ^ n)]
    (hm80 : mCoin ≤ 80) {hn : nInner ≤ 24} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peOut : BitAssignment kOut → PotExpectFn} (s1 : Stage1AsymRevPkg w1 tStage1 decode)
    {rSub : QRegister kOut 41}
    {oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut}
    (pkg25 : Stage25InPlacePolyPkg mCoin nInner wWork w1 kOut Wp tStage25U tStage25C tPotU tPotC hn
    decode peOut s1.o1 rSub oN) (v : Var) (rTot : QRegister dLayout n)
    (isCsel : Bool) : (pSelectOfStage25InPlace_poly hm80 s1 pkg25 v rTot isCsel).count .T =
    tStage1 + (if isCsel then tStage25C else tStage25U) ∧
    (pSelectOfStage25InPlace_poly hm80 s1 pkg25 v rTot isCsel).count .TOFF = 0 := by
  cases nonempty_fintype Var
  classical
  have cHF := counts_hadamardRegCirc (mCoin + 2) (rLcuPolyLayout mCoin hm80);
  have cHI := counts_hadamardRegCirc_inv (mCoin + 2) (rLcuPolyLayout mCoin hm80)
  obtain ⟨tHF, fHF⟩ : ((cHadPolyFwdLayout mCoin hm80).onRegister rTot).count .T = 0 ∧
      ((cHadPolyFwdLayout mCoin hm80).onRegister rTot).count .TOFF = 0 :=
    ⟨by simpa only [cHadPolyFwdLayout, Circuit.count_onRegister] using cHF.1,
        by simpa only [cHadPolyFwdLayout, Circuit.count_onRegister] using cHF.2⟩
  obtain ⟨tHI, fHI⟩ : ((cHadPolyInvLayout mCoin hm80).onRegister rTot).count .T = 0 ∧
      ((cHadPolyInvLayout mCoin hm80).onRegister rTot).count .TOFF = 0 :=
    ⟨by simpa only [cHadPolyInvLayout, Circuit.count_onRegister] using cHI.1,
        by simpa only [cHadPolyInvLayout, Circuit.count_onRegister] using cHI.2⟩
  have fF1 := (s1.o1.step_and_counts v rTot).2.2.2.1; obtain ⟨tS1, fR1⟩ :=
      s1.counts v rTot; obtain ⟨t25, f25⟩ :=
      pkg25.counts v rTot isCsel; dsimp only [pSelectOfStage25InPlace_poly,
      DynamicCircuit.count]; rw [tHF, tHI, fHF, fHI, fF1, fR1, t25, f25]; refine ⟨?_, rfl⟩
  cases isCsel <;> (simp only [↓reduceIte, Bool.false_eq_true]; omega)

theorem dynWires_cOfSelectOfStage25InPlace_poly {Var : Type}
    {mCoin nInner wWork w1 tStage1 kOut m Wp tStage25U tStage25C tPotU tPotC : ℕ}
    (hm80 : mCoin ≤ 80) {hn : nInner ≤ 24} {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peOut : BitAssignment kOut → PotExpectFn} (s1 : Stage1AsymRevPkg w1 tStage1 decode)
    (hAct1 : ∀ {V : Type} {k : ℕ} {S : Wire k → Prop} (v' : V) (rT : QRegister dLayout k),
    (∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rT w)) →
    DynWires S (s1.o1.fwdAmb v' rT) ∧ DynWires S (s1.revAmb v' rT)) {rSub : QRegister kOut 41}
    {oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut}
    (pkg25 : Stage25InPlacePolyPkg mCoin nInner wWork w1 kOut Wp tStage25U tStage25C tPotU tPotC hn
    decode peOut s1.o1 rSub oN) (isCsel : Bool) (v : Var) (rS : QRegister systemQubits_frozen m)
    (rA : QRegister (ancWOfScr scrWLayout) m) :
    DynWires (SafeConcatGen (ActiveOuterCoinStackOf 23 wWork mCoin) rS rA)
    (cOfSelectOfStage25InPlace_poly hm80 s1 pkg25 isCsel v rS rA) := by
  unfold cOfSelectOfStage25InPlace_poly
  cases decDisjSysAnc_top rS rA with
  | isFalse _ => exact trivial
  | isTrue hd =>
      let rTot := rS.concat rA hd
      have hActW (w0 : Wire dLayout) (hwA : ActiveOuterCoinStackOf 23 wWork mCoin w0) :
          SafeConcatGen (ActiveOuterCoinStackOf 23 wWork mCoin) rS rA (rTot w0) :=
          ⟨hd, w0, hwA, rfl⟩
      have dw1 := hAct1 v rTot hActW
      exact ⟨circWires_onRegister rTot hActW (circWires_hadamardRegCirc (mCoin + 2)
          (rLcuPolyLayout mCoin hm80) (fun i ↦ rLcuPolyLayout_active_stack hm80 i)), dw1.1,
        pkg25.dynWires v rTot isCsel hActW, dw1.2,
            circWires_onRegister rTot hActW (circWires_hadamardRegCirc_inv (mCoin + 2)
            (rLcuPolyLayout mCoin hm80) (fun i ↦ rLcuPolyLayout_active_stack hm80 i))⟩

theorem cleanWorkStep_pSelectOfStage25InPlace_poly
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {mCoin nInner wWork w1 tStage1 kOut n Wp tStage25U tStage25C tPotU tPotC : ℕ} [NeZero (2 ^ n)]
    (hm53 : 53 ≤ mCoin) (hm80 : mCoin ≤ 80) {hn : nInner ≤ 24} (hInner : 39 + nInner ≤ mCoin)
    {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peOut : BitAssignment kOut → PotExpectFn}
    (s1 : Stage1AsymRevPkg w1 tStage1 decode)
    (hAct1 : ∀ {V : Type} {m : ℕ} {S : Wire m → Prop} (v' : V) (rT : QRegister dLayout m),
      (∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rT w)) →
      DynWires S (s1.o1.fwdAmb v' rT) ∧ DynWires S (s1.revAmb v' rT))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode)
    {rSub : QRegister kOut 41}
    {oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut}
    (pkg25 : Stage25InPlacePolyPkg mCoin nInner wWork w1 kOut Wp tStage25U tStage25C tPotU tPotC hn
        decode peOut s1.o1 rSub oN)
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool) :
    let uLocal :=
        if isCsel then (cselLocalReflRevOuterSub2m1_98_wstate hk0_le72_wstate rSub s1.o1
        (spec41Of24_ipb (toCoin24InPlaceOfN hn oN).sliceSpec) hCoin).u
      else (uselLocalReflRevOuterSub2m1_98_wstate hk0_le72_wstate rSub s1.o1 (spec41Of24_ipb
          (toCoin24InPlaceOfN hn oN).sliceSpec) hCoin).u
    CleanWorkStep (rTot.compose (rScrExt 0 hk0_le72_wstate)) (rTot.embedUnitary uLocal)
        (pSelectOfStage25InPlace_poly hm80 s1 pkg25 v rTot isCsel) := by
  have hm39 : 39 ≤ mCoin := by omega
  let specKOut := spec41Of24_ipb (toCoin24InPlaceOfN hn oN).sliceSpec;
  let s4 := stage4OuterSubUnitaryPkg_reflRev2m1_98_wstate hk0_le72_wstate rSub s1.o1 specKOut hCoin
  let uStage4 :=
      if isCsel then uCselMuxWState hk0_le72_wstate rSub s1.o1 s4 else uUselMuxWState
      hk0_le72_wstate rSub s1.o1 s4
  let uPre := uPreExt hk0_le72_wstate decode uStage4
  have hCommExt : pScrExt 0 hk0_le72_wstate * uPre.1 = uPre.1 * pScrExt 0 hk0_le72_wstate := by
    dsimp only [uPre, uStage4]
    cases isCsel
    · exact comm_pScrExt_usel_wstate hk0_le72_wstate rSub s1.o1 s4
    · exact comm_pScrExt_csel_wstate hk0_le72_wstate rSub s1.o1 s4
  have hu4Ret (M : Operator (2 ^ (80 - mCoin))) :
      Commute uStage4.1 ((rRetPolyLayout mCoin hm80).embedMatrix M) := by
    have hN4 (γω) := uStage4ReflRev2m1_98_Nonly_comm_rRetPoly hn hm53 hm80 hInner
      (specKOut γω) (reflPotSliceNOnly_spec41OfN hn oN.sliceSpec γω)
    dsimp only [uStage4, uUselMuxWState, uCselMuxWState]
    cases isCsel
    · exact uMuxExtOut_zero_comm_rRetPoly hm39 hm80 rSub s4.uUselSlice (huUsel_wstate s4)
          (fun γω M' ↦ (hN4 γω M').1) M
    · exact uMuxExtOut_zero_comm_rRetPoly hm39 hm80 rSub s4.uCselSlice (huCsel_wstate s4)
          (fun γω M' ↦ (hN4 γω M').2) M
  let Wnh_loc := wNoHad (uStage1Clean_c70 decode)
  let uMid := Wnh_loc⁻¹ * uStage4 * Wnh_loc
  let uSel :=
      unitaryOnProj uPre (pScrExt 0 hk0_le72_wstate) (pScrExt_herm 0 _) (pScrExt_idem 0 _) hCommExt
  have hSelProj :=
      unitaryOnProj_mul_proj uPre (pScrExt 0 hk0_le72_wstate) (pScrExt_herm 0 _)
      (pScrExt_idem 0 _) hCommExt
  have hCommSel :=
      (unitaryOnProj_comm_proj uPre (pScrExt 0 hk0_le72_wstate) (pScrExt_herm 0 _)
      (pScrExt_idem 0 _) hCommExt).eq
  let R₀ := (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0;
  let HPol := rTot.embedUnitary (uHadPolyLayout mCoin hm80); let X₁ := HPol.1 * R₀;
  let X₂ := (rTot.embedUnitary uMid).1 * X₁
  have eAbs (U : Unitary (2 ^ dLayout)) {X : Operator (2 ^ n)}
      (hC : pScrExt 0 hk0_le72_wstate * U.1 = U.1 * pScrExt 0 hk0_le72_wstate)
      (hX : R₀ * X = X) : R₀ * ((rTot.embedUnitary U).1 * X) = (rTot.embedUnitary U).1 * X := by
    have hAmb : R₀ * (rTot.embedUnitary U).1 = (rTot.embedUnitary U).1 * R₀ := by
      dsimp only [R₀];
      rw [basisOutcomeProjector_compose_zero, QRegister.embedUnitary_val, ← rTot.embedMatrix_mul,
          ← rTot.embedMatrix_mul, hC]
    rw [← Matrix.mul_assoc, hAmb, Matrix.mul_assoc, hX]
  have cHPol : pScrExt 0 hk0_le72_wstate * (uHadPolyLayout mCoin hm80).1 =
      (uHadPolyLayout mCoin hm80).1 * pScrExt 0 hk0_le72_wstate := by
    unfold uHadPolyLayout
    exact (hadamardRegSym_comm_disjoint (Var := Unit) wHasN1 (mCoin + 2) (rLcuPolyLayout mCoin hm80)
      (hDisjHadPoly_layout hm80) (rScrExt 0 hk0_le72_wstate) (disj_of_ne fun i j e ↦ by
        have hiLt := i.isLt
        have hj1565 : j.val < 1565 := j.isLt
        have hv := congrArg Fin.val e
        rw [val_rLcuPolyLayout, PhotochemistrySolution.Coin70Lift.val_rScrExt] at hv; omega)
      (compProj 0)).symm
  have cHPolInv : pScrExt 0 hk0_le72_wstate * ((uHadPolyLayout mCoin hm80)⁻¹).1 =
      ((uHadPolyLayout mCoin hm80)⁻¹).1 * pScrExt 0 hk0_le72_wstate :=
      (SelectFastQft8Gidney.unitary_inv_comm (uHadPolyLayout mCoin hm80)
      (pScrExt 0 hk0_le72_wstate) (Commute.symm cHPol)).symm
  have huPrePol : uPre = (uHadPolyLayout mCoin hm80)⁻¹ * uMid * uHadPolyLayout mCoin hm80 := by
    dsimp only [uPre, uMid, Wnh_loc]; rw [uPreExt_zero_eq_hadPoly hm39 hm80 decode uStage4 hu4Ret];
    simp only [mul_assoc]
  have cMid : pScrExt 0 hk0_le72_wstate * uMid.1 = uMid.1 * pScrExt 0 hk0_le72_wstate := by
    have huM : uMid = uHadPolyLayout mCoin hm80 * uPre * (uHadPolyLayout mCoin hm80)⁻¹ := by
      rw [huPrePol]; group
    rw [huM, Submonoid.coe_mul, Submonoid.coe_mul];
    exact (Commute.mul_right (Commute.mul_right cHPol hCommExt) cHPolInv).eq
  have hR₀ : R₀ * R₀ = R₀ := QRegister.basisOutcomeProjector_mul_self _ 0;
  have hAbsX₁ : R₀ * X₁ = X₁ := eAbs (uHadPolyLayout mCoin hm80) cHPol hR₀;
  have hAbsX₂ : R₀ * X₂ = X₂ := eAbs uMid cMid hAbsX₁;
  have s25 := pkg25.step25 hCoin v rTot isCsel X₁ hAbsX₁ hAbsX₂
  have dw1 :=
      hAct1 (S := fun u ↦ ∀ j : Fin 0, u ≠
      (rTot.compose (rCoinExt 0 hk0_le72_wstate)) j) v rTot (fun _ _ j ↦ Fin.elim0 j)
  have sFwd1 := subspaceStep_stage1_fwd_ext_c70 hk0_le72_wstate s1.o1 v rTot dw1.1 hAbsX₁;
  have sRev1 := s1.stepRev hk0_le72_wstate v rTot dw1.2 hAbsX₂
  have hEvF : ((cHadPolyFwdLayout mCoin hm80).onRegister rTot).eval = HPol := by
    rw [Circuit.eval_onRegister, eval_cHadPolyFwdLayout]
  have hEvI : ((cHadPolyInvLayout mCoin hm80).onRegister rTot).eval = HPol⁻¹ := by
    rw [Circuit.eval_onRegister, eval_cHadPolyInvLayout, QRegister.embedUnitary_inv]
  have sH1 : SubspaceStep R₀ X₁ (.circuit ((cHadPolyFwdLayout mCoin hm80).onRegister rTot)) :=
      subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) R₀ _)
      (congrArg (fun U ↦ U.1 * R₀) hEvF)
  have sH2 : SubspaceStep X₂ ((HPol⁻¹).1 * X₂)
      (.circuit ((cHadPolyInvLayout mCoin hm80).onRegister rTot)) :=
      subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) X₂ _)
      (congrArg (fun U ↦ U.1 * X₂) hEvI)
  have hEnd : (HPol⁻¹).1 * X₂ = (rTot.embedUnitary uSel).1 * R₀ := by
    have hPreMat : (HPol⁻¹).1 * X₂ = (rTot.embedUnitary uPre).1 * R₀ := by
      dsimp only [HPol, X₂, X₁]; rw [huPrePol]; dsimp only [uMid];
      simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv, Submonoid.coe_mul,
          Matrix.mul_assoc]
    rw [hPreMat]; dsimp only [R₀];
    rw [basisOutcomeProjector_compose_zero, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
        ← rTot.embedMatrix_mul,
        ← rTot.embedMatrix_mul]; exact congrArg rTot.embedMatrix hSelProj.symm
  have hStepSel :=
      cleanWorkStep_embed_of_subspaceStep rTot (rScrExt 0 hk0_le72_wstate) uSel _ hCommSel
      (subspaceStep_congr_out (sH1.seq (sFwd1.seq (s25.seq (sRev1.seq sH2)))) hEnd)
  cases isCsel <;> exact hStepSel

attribute [local irreducible] pSelectOfStage25InPlace_poly sReflSliceOuterSub2m1_wstate
    cselReflRevSliceOuterSub2m1_98_wstate uselReflRevSliceOuterSub2m1_98_wstate

def outerCoinSelectBundleStackPoly_ofStage25InPlace {mCoin nInner wWork w1 tStage1 kOut Wp tStage25U
    tStage25C tPotU tPotC tUsel tCsel : ℕ} {hgLo : 23 ≤ 23} (hm53 : 53 ≤ mCoin) (hm80 : mCoin ≤ 80)
    (hn : nInner ≤ 24) (hInner : 39 + nInner ≤ mCoin) {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ}
    {wEN : Fin 4 → ℕ} {wKin : Particle_frozen → ℕ} {wIdle : ℕ}
    {decode : Fin (2 ^ 41) → ZeroNEremSector} {peOut : BitAssignment kOut → PotExpectFn} {A : OpSys}
    (hwLo : mCoin + 1 ≤ wWork) (hwHi : wWork ≤ 1500) (s1 : Stage1AsymRevPkg w1 tStage1 decode)
    (hAct1 : ∀ {V : Type} {k : ℕ} {S : Wire k → Prop} (v' : V) (rT : QRegister dLayout k),
    (∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rT w)) →
    DynWires S (s1.o1.fwdAmb v' rT) ∧ DynWires S (s1.revAmb v' rT))
    (hCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode) (rSub : QRegister kOut 41)
    (oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut)
    (pkg25 : Stage25InPlacePolyPkg mCoin nInner wWork w1 kOut Wp tStage25U tStage25C tPotU tPotC hn
    decode peOut s1.o1 rSub oN) (htUsel : tStage1 + tStage25U + 4 * (mCoin + 1) ≤ tUsel)
    (htCsel : tStage1 + tStage25C + 4 * (mCoin + 1) ≤ tCsel)
    (hAvgOp : (2 ^ 0 : ℂ)⁻¹ • ∑ γ : BitAssignment 0, ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
    bOuterZeroNErem decode (peOut (fun j ↦ concatBitsGen γ (outSubRawBits rSub c)
    (Fin.natAdd 0 j))) c) = A) :
    OuterCoinSelectBundleStackAsym 23 wWork mCoin tUsel tCsel hgLo hm80 A :=
  let specKOut := spec41Of24_ipb (toCoin24InPlaceOfN hn oN).sliceSpec
  let hNKOut := fun γω ↦ reflPotSliceNOnly_spec41OfN hn oN.sliceSpec γω
  have hAvgZ : (2 ^ 0 : ℂ)⁻¹ • ∑ γ : BitAssignment 0,
      ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
        bOuterZeroNErem decode
          (peOut (fun j ↦ concatBitsGen γ (outSubRawBits rSub c)
            ⟨j.val, by have := j.isLt; omega⟩)) c) = A := by
    have hIdx : ∀ (γ : BitAssignment 0) (c : Fin (2 ^ 41)),
        (fun j : Fin kOut ↦ concatBitsGen γ (outSubRawBits rSub c)
          ⟨j.val, by have := j.isLt; omega⟩) =
        (fun j : Fin kOut ↦ concatBitsGen γ (outSubRawBits rSub c) (Fin.natAdd 0 j)) :=
      fun γ c ↦ funext fun j ↦ congrArg (concatBitsGen γ (outSubRawBits rSub c))
        (Fin.ext (Nat.zero_add j.val).symm)
    simp_rw [hIdx]; exact hAvgOp
  let hSpec :=
      selectLocalSpecGen_reflRevOuterSub2m1_98_stackPoly hn hm53 hm80 hInner rSub s1.o1 specKOut
      hNKOut hCoin hAvgZ; let hGrad :=
                            comm_locGrad3Hi_reflRevOuterSub2m1_98_wstate hk0_le72_wstate rSub s1.o1
                            specKOut hCoin
  { hwLo := hwLo
    hwHi := hwHi
    S := sLocalReflOuterSub2m1_wstate hk0_le72_wstate rSub s1.o1 specKOut hCoin
    cselU := cselLocalReflRevOuterSub2m1_98_wstate hk0_le72_wstate rSub s1.o1 specKOut hCoin
    uselU := uselLocalReflRevOuterSub2m1_98_wstate hk0_le72_wstate rSub s1.o1 specKOut hCoin
    cOf := fun v rS rA ↦ cOfSelectOfStage25InPlace_poly hm80 s1 pkg25 true v rS rA
    uOf := fun v rS rA ↦ cOfSelectOfStage25InPlace_poly hm80 s1 pkg25 false v rS rA
    hlocal := hSpec.1
    hUselCat := hSpec.2
    hCommC := fun M ↦ (hGrad M).2
    hCommU := fun M ↦ (hGrad M).1
    hC := fun v rS rA hd ↦ by
      have hPosC : cOfSelectOfStage25InPlace_poly hm80 s1 pkg25 true v rS rA =
          pSelectOfStage25InPlace_poly hm80 s1 pkg25 v (rS.concat rA hd) true :=
          dite_pos_c70 (decDisjSysAnc_top rS rA) hd;
          have hPosU : cOfSelectOfStage25InPlace_poly hm80 s1 pkg25 false v rS rA =
          pSelectOfStage25InPlace_poly hm80 s1 pkg25 v (rS.concat rA hd) false :=
          dite_pos_c70 (decDisjSysAnc_top rS rA) hd
      rw [hPosC, hPosU]
      have sC :=
          cleanWorkStep_pSelectOfStage25InPlace_poly hm53 hm80 hInner s1 @hAct1 hCoin pkg25 v
          (rS.concat rA hd) true; have sU :=
                                    cleanWorkStep_pSelectOfStage25InPlace_poly hm53 hm80 hInner s1
                                    @hAct1 hCoin pkg25 v (rS.concat rA hd) false
      obtain ⟨tC, fC⟩ :=
          counts_pSelectOfStage25InPlace_poly hm80 s1 pkg25 v (rS.concat rA hd) true; obtain ⟨tU,
          fU⟩ := counts_pSelectOfStage25InPlace_poly hm80 s1 pkg25 v (rS.concat rA hd) false
      have hScrEq : (rS.concat rA hd).compose (rScrExt 0 hk0_le72_wstate) =
          rA.compose (scrSubLGen (hpStack mCoin hm80)) :=
          concat_compose_rScrExt_c70 hk0_le72_wstate rS rA hd
      rw [hScrEq] at sC sU
      simp only [↓reduceIte, Bool.false_eq_true] at tC tU
      exact ⟨sC, sU, fC, fU, by omega, by omega⟩
    hDyn := fun v rS rA ↦
      ⟨dynWires_cOfSelectOfStage25InPlace_poly hm80 s1 @hAct1 pkg25 true v rS rA,
       dynWires_cOfSelectOfStage25InPlace_poly hm80 s1 @hAct1 pkg25 false v rS rA⟩ }
end QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin
end

namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs
set_option Elab.async false
set_option exponentiation.threshold 256
open Real Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution.Coul18K2Certs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
attribute [local irreducible] systemQubits_frozen word512DualLegLo6

-- ============================================================================
-- Section 1. Coin Bit Extraction & `.en` Bit-5 Involution
-- ============================================================================

theorem concat0_bits18 (γ : BitAssignment 0) (β : BitAssignment 18) :
    (fun j : Fin 18 ↦ concatBitsGen γ β (Fin.natAdd 0 j)) = β := by
  funext j
  dsimp only [concatBitsGen, Function.comp_apply]
  rcases h : (finSumFinEquiv (m := 0) (n := 18)).symm (Fin.natAdd 0 j) with a | b
  · exact a.elim0
  · have hb : finSumFinEquiv (m := 0) (n := 18) (Sum.inr b) = Fin.natAdd 0 j := by
      rw [← h, Equiv.apply_symm_apply]
    rw [finSumFinEquiv_apply_right] at hb
    exact congrArg β (Fin.ext (by simpa [Fin.val_natAdd] using congrArg Fin.val hb))

theorem take17_outSubRawBits_lt11 (c : Fin (2 ^ 41)) (k : Fin 11) :
    take17Of18 (outSubRawBits rW18Sub41_k2 c) ⟨k.val, by omega⟩ = w11RawBits c k := by
  unfold take17Of18 outSubRawBits w11RawBits
  dsimp only
  rw [show rW18Sub41_k2 ⟨k.val, by omega⟩ = w11Idx k by fin_cases k <;> rfl]
theorem w11RawBits_eq_testBit_w11NatOfCoin (c : Fin (2 ^ 41)) (k : Fin 11) : w11RawBits c k =
    if (w11NatOfCoin c).testBit k.val then 1 else 0 := by
  unfold w11RawBits; rw [w11NatOfCoin_testBit c k]
  fin_cases k <;> rfl

theorem equivBits11_w11RawBits (c : Fin (2 ^ 41)) : equivBits11 (w11RawBits c) = ⟨w11NatOfCoin c,
    w11NatOfCoin_lt2048 c⟩ := by
  apply Fin.ext; change natOfZModBits 11 (w11RawBits c) = w11NatOfCoin c
  have hFn : w11RawBits c = fun k : Fin 11 ↦
      if (w11NatOfCoin c).testBit k.val then (1 : ZMod 2) else 0 :=
    funext (w11RawBits_eq_testBit_w11NatOfCoin c)
  rw [hFn, natOfZModBits_of_testBit 11 (w11NatOfCoin c)];
  exact Nat.mod_eq_of_lt (w11NatOfCoin_lt2048 c)
theorem w11Sub63_take17_outSubRawBits (c : Fin (2 ^ 41)) :
    w11Sub63 (take17Of18 (outSubRawBits rW18Sub41_k2 c)) = ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩
    := by
  apply Fin.ext
  change natOfZModBits 11 (fun k : Fin 11 ↦ take17Of18 (outSubRawBits rW18Sub41_k2 c) ⟨k.val, _⟩) =
      w11NatOfCoin c
  have hFn : (fun k : Fin 11 ↦ take17Of18 (outSubRawBits rW18Sub41_k2 c) ⟨k.val, by omega⟩) =
      w11RawBits c := funext (take17_outSubRawBits_lt11 c)
  rw [hFn]; exact congrArg Fin.val (equivBits11_w11RawBits c)
def withBit17 (γ17 : BitAssignment 17) (b : ZMod 2) : BitAssignment 18 := fun j ↦
    if h : j.val < 17 then γ17 ⟨j.val, h⟩ else b
theorem take17_withBit17 (γ17 : BitAssignment 17) (b : ZMod 2) : take17Of18 (withBit17 γ17 b) =
    γ17 := by funext j; unfold take17Of18 withBit17; simp only [j.isLt, ↓reduceDIte]
theorem otpDeltaSub62_withBit17 (γ17 : BitAssignment 17) (b : ZMod 2)
    (u0 u1 : ZMod 2) : otpDeltaSub62 (withBit17 γ17 b) u0 u1 =
    otpDeltaSub62 (withBit17 γ17 0) u0 u1 := by unfold otpDeltaSub62 withBit17; dsimp only; rfl
theorem withBit17_at17 (γ17 : BitAssignment 17) (b : ZMod 2) :
    withBit17 γ17 b ⟨17, by omega⟩ = b := by
  unfold withBit17
  simp only [show ¬((17 : ℕ) < 17) by omega, ↓reduceDIte]

def spliceEquiv24 (γ17 : BitAssignment 17) : (ZMod 2 × BitAssignment 23) ≃ BitAssignment 24 where
  toFun p := splicedZ24Sub62 (withBit17 γ17 p.1) p.2
  invFun z24 :=
    (z24 ⟨2, by omega⟩ -
      otpDeltaSub62 (withBit17 γ17 0) (z24 ⟨0, by omega⟩) (z24 ⟨1, by omega⟩),
     unspliceZ23Of24 z24)
  left_inv p := by
    rcases p with ⟨b, z23⟩
    refine Prod.ext ?_ (unsplice_splicedZ24Sub62 (withBit17 γ17 b) z23); dsimp only
    have h0 : splicedZ24Sub62 (withBit17 γ17 b) z23 ⟨0, by omega⟩ = z23 ⟨0, by omega⟩ := by
      unfold splicedZ24Sub62; simp only [show (0 : ℕ) < 2 by omega, ↓reduceDIte]
    have h1 : splicedZ24Sub62 (withBit17 γ17 b) z23 ⟨1, by omega⟩ = z23 ⟨1, by omega⟩ := by
      unfold splicedZ24Sub62; simp only [show (1 : ℕ) < 2 by omega, ↓reduceDIte]
    have h2 : splicedZ24Sub62 (withBit17 γ17 b) z23 ⟨2, by omega⟩ =
        b + otpDeltaSub62 (withBit17 γ17 0) (z23 ⟨0, by omega⟩) (z23 ⟨1, by omega⟩) := by
      unfold splicedZ24Sub62
      simp only [show ¬((2 : ℕ) < 2) by omega, ↓reduceDIte]
      rw [otpDeltaSub62_withBit17 γ17 b, withBit17_at17]
    rw [h0, h1, h2]; ring
  right_inv z24 := by
    refine spliced_unsplice_of_eq_at2 _ z24 ?_; rw [otpDeltaSub62_withBit17, withBit17_at17]; ring
def flipBit0Nat (x : ℕ) : ℕ := (x / 2) * 2 + (1 - x % 2)

theorem flipBit0Nat_lt {x n : ℕ} (heven : n % 2 = 0) (hx : x < n) : flipBit0Nat x < n := by
  unfold flipBit0Nat; omega
theorem flipBit0Nat_invol (x : ℕ) : flipBit0Nat (flipBit0Nat x) = x := by unfold flipBit0Nat; omega
theorem flipBit0Nat_div64 (x : ℕ) : flipBit0Nat x / 64 = x / 64 := by unfold flipBit0Nat; omega
theorem flipBit0Nat_mod64 (x : ℕ) : flipBit0Nat x % 64 = flipBit0Nat (x % 64) := by
  unfold flipBit0Nat; omega
theorem coin41_decomp (c : Fin (2 ^ 41)) : c.val = (c.val % 32) + 32 *
    ((((c.val / 32) % 1048576) % 1024) + 1024 * ((((c.val / 32) % 1048576) / 1024) + 1024 *
    (((c.val / 33554432) % 256) + 256 * ((c.val / 33554432) / 256)))) := by
  have h1 := Nat.div_add_mod c.val 32; have h2 := Nat.div_add_mod (c.val / 32) 1048576;
  have h3 := Nat.div_add_mod ((c.val / 32) % 1048576) 1024;
  have h4 := Nat.div_add_mod (c.val / 33554432) 256
  have h33 : (c.val / 32) / 1048576 = c.val / 33554432 := by rw [Nat.div_div_eq_div_mul]
  linarith

theorem tier1CoinOf5_val_eq {hi8 lo8 hi10 lo10 c5 : ℕ} (h1 : hi8 < 256) (h2 : lo8 < 256)
    (h3 : hi10 < 1024) (h4 : lo10 < 1024) (h5 : c5 < 32) : (tier1CoinOf5 hi8 lo8 hi10 lo10 c5).val =
    c5 + 32 * (lo10 + 1024 * (hi10 + 1024 * (lo8 + 256 * hi8))) := by
  have hd := tier1CoinOf5_digits h1 h2 h3 h4 h5; dsimp only at hd
  rcases hd with ⟨dc5, dlo10, dhi10, dlo8, dhi8, _⟩
  have hdec :=
      coin41_decomp (tier1CoinOf5 hi8 lo8 hi10 lo10 c5); rw [dc5, dlo10, dhi10, dlo8,
      dhi8] at hdec; exact hdec
theorem testBit_coinOf5_5_15_20_25 {hi8 lo8 hi10 lo10 c5 : ℕ}
    (h1 : hi8 < 256) (h2 : lo8 < 256) (h3 : hi10 < 1024) (h4 : lo10 < 1024) (h5 : c5 < 32) :
    let c := tier1CoinOf5 hi8 lo8 hi10 lo10 c5
    c.val.testBit 5 = (lo10 % 64).testBit 0 ∧
    c.val.testBit 15 = hi10.testBit 0 ∧
    c.val.testBit 20 = hi10.testBit 5 ∧
    c.val.testBit 25 = (lo8 % 64).testBit 0 ∧
    ∀ k < 41, k ≠ 5 →
      (tier1CoinOf5 hi8 lo8 hi10 (flipBit0Nat lo10) c5).val.testBit k = c.val.testBit k := by
  have hv := tier1CoinOf5_val_eq h1 h2 h3 h4 h5
  have hvf := tier1CoinOf5_val_eq h1 h2 h3 (flipBit0Nat_lt (by omega) h4) h5
  set M := hi10 + 1024 * (lo8 + 256 * hi8) with hM_def
  have hBit (n j : ℕ) : n.testBit j = decide ((n / 2 ^ j) % 2 = 1) := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with hm | hm <;> simp [hm]
  dsimp only
  have hd5 : (tier1CoinOf5 hi8 lo8 hi10 lo10 c5).val / 2 ^ 5 = lo10 + 1024 * M := by
    rw [hv, show (2 ^ 5 : ℕ) = 32 by norm_num, Nat.add_mul_div_left _ _ (by norm_num),
        Nat.div_eq_of_lt h5, zero_add]
  have hd15 : (tier1CoinOf5 hi8 lo8 hi10 lo10 c5).val / 2 ^ 15 = M := by
    rw [hv, show c5 + 32 * (lo10 + 1024 * M) = (c5 + 32 * lo10) + 32768 * M by ring,
        show (2 ^ 15 : ℕ) = 32768 by norm_num, Nat.add_mul_div_left _ _ (by norm_num),
            Nat.div_eq_of_lt (by omega), zero_add]
  have hd20 : (tier1CoinOf5 hi8 lo8 hi10 lo10 c5).val / 2 ^ 20 = M / 32 := by
    rw [show (2 ^ 20 : ℕ) = 2 ^ 15 * 32 by norm_num, ← Nat.div_div_eq_div_mul, hd15]
  have hd25 : (tier1CoinOf5 hi8 lo8 hi10 lo10 c5).val / 2 ^ 25 = lo8 + 256 * hi8 := by
    rw [show (2 ^ 25 : ℕ) = 2 ^ 15 * 1024 by norm_num, ← Nat.div_div_eq_div_mul, hd15, hM_def,
        Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt h3, zero_add]
  refine ⟨by rw [hBit, hBit, hd5, Nat.pow_zero, Nat.div_one, decide_eq_decide]; omega,
    by rw [hBit, hBit, hd15, hM_def, Nat.pow_zero, Nat.div_one, decide_eq_decide]; omega, ?_,
    by rw [hBit, hBit, hd25, Nat.pow_zero, Nat.div_one, decide_eq_decide]; omega, fun k hk hne5 ↦
        ?_⟩
  · rw [hBit, hBit, hd20, hM_def, show (2 ^ 5 : ℕ) = 32 by norm_num,
        show (hi10 + 1024 * (lo8 + 256 * hi8)) / 32 = hi10 / 32 + 32 * (lo8 + 256 * hi8) by
          rw [show 1024 * (lo8 + 256 * hi8) = 32 * (32 * (lo8 + 256 * hi8)) by ring,
              Nat.add_mul_div_left _ _ (by norm_num)], decide_eq_decide]
    omega
  · rw [hBit, hBit]
    by_cases hk5 : k < 5
    · have hM2 (m : ℕ) : ((c5 + 32 * m) / 2 ^ k) % 2 = (c5 / 2 ^ k) % 2 := by
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
            <;> norm_num <;> omega
      rw [hvf, hv, hM2, hM2]
    · obtain ⟨r, rfl⟩ : ∃ r, k = 6 + r := ⟨k - 6, by omega⟩
      have hDiv64 (lo10' : ℕ) : (c5 + 32 * (lo10' + 1024 * M)) / 2 ^ (6 + r) = (lo10' / 2 + 512 *
          M) / 2 ^ r := by
        rw [show (2 ^ (6 + r) : ℕ) = 32 * (2 * 2 ^ r) by rw [Nat.pow_add]; ring,
            ← Nat.div_div_eq_div_mul,
            Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt h5, zero_add,
                ← Nat.div_div_eq_div_mul,
            show 1024 * M = 2 * (512 * M) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
      rw [hvf, hv, hDiv64, hDiv64, show flipBit0Nat lo10 / 2 = lo10 /
          2 by unfold flipBit0Nat; omega]
def flipCoinBit5 (c : Fin (2 ^ 41)) : Fin (2 ^ 41) :=
    tier1CoinOf5 ((c.val / 33554432) / 256) ((c.val / 33554432) % 256)
    (((c.val / 32) % 1048576) / 1024) (flipBit0Nat (((c.val / 32) % 1048576) % 1024)) (c.val % 32)
theorem flipCoinBit5_invol (c : Fin (2 ^ 41)) : flipCoinBit5 (flipCoinBit5 c) = c := by
  have hcLt := c.isLt
  have hd := tier1CoinOf5_digits (by omega : (c.val / 33554432) / 256 < 256)
    (by omega : (c.val / 33554432) % 256 < 256) (by omega : ((c.val / 32) % 1048576) / 1024 < 1024)
    (flipBit0Nat_lt (by omega) (by omega : ((c.val / 32) % 1048576) % 1024 < 1024))
        (by omega : c.val % 32 < 32)
  dsimp only at hd
  rcases hd with ⟨dc5, dlo10, dhi10, dlo8, dhi8, _⟩
  unfold flipCoinBit5
  rw [dhi8, dlo8, dhi10, dlo10, flipBit0Nat_invol, dc5]
  exact Fin.ext ((tier1CoinOf5_val_eq (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (coin41_decomp c).symm)
theorem sub18Sub62Idx_lt17_ne5 : ∀ j : Fin 17, (sub18Sub62Idx ⟨j.val, by omega⟩).val ≠ 5 := by
  intro j; fin_cases j <;> decide
theorem take17_flipCoinBit5 (c : Fin (2 ^ 41)) :
    take17Of18 (outSubRawBits rW18Sub41_k2 (flipCoinBit5 c)) =
    take17Of18 (outSubRawBits rW18Sub41_k2 c) := by
  have hcLt := c.isLt
  have hcEq : c = tier1CoinOf5 ((c.val / 33554432) / 256) ((c.val / 33554432) % 256)
      (((c.val / 32) % 1048576) / 1024) (((c.val / 32) % 1048576) % 1024) (c.val % 32) :=
    Fin.ext ((coin41_decomp c).trans (tier1CoinOf5_val_eq (by omega) (by omega) (by omega)
        (by omega) (by omega)).symm)
  have htb := (testBit_coinOf5_5_15_20_25 (by omega : (c.val / 33554432) / 256 < 256)
    (by omega : (c.val / 33554432) % 256 < 256) (by omega : ((c.val / 32) % 1048576) / 1024 < 1024)
    (by omega : ((c.val / 32) % 1048576) % 1024 < 1024) (by omega : c.val % 32 < 32)).2.2.2.2
  funext j
  unfold take17Of18 outSubRawBits flipCoinBit5
  simp only [show ∀ i : Fin 18, rW18Sub41_k2 i = sub18Sub62Idx i from fun _ ↦ rfl]
  rw [htb _ (sub18Sub62Idx ⟨j.val, by omega⟩).isLt (sub18Sub62Idx_lt17_ne5 j), ← hcEq]
theorem bit17_flipCoinBit5 (c : Fin (2 ^ 41)) :
    outSubRawBits rW18Sub41_k2 (flipCoinBit5 c) ⟨17, by omega⟩ =
      1 - outSubRawBits rW18Sub41_k2 c ⟨17, by omega⟩ := by
  have hcLt := c.isLt
  have hcEq : c = tier1CoinOf5 ((c.val / 33554432) / 256) ((c.val / 33554432) % 256)
      (((c.val / 32) % 1048576) / 1024) (((c.val / 32) % 1048576) % 1024) (c.val % 32) :=
    Fin.ext ((coin41_decomp c).trans (tier1CoinOf5_val_eq (by omega) (by omega) (by omega)
        (by omega) (by omega)).symm)
  have ht (lo10 : ℕ) (hlo : lo10 < 1024) := (testBit_coinOf5_5_15_20_25
    (by omega : (c.val / 33554432) / 256 < 256) (by omega : (c.val / 33554432) % 256 < 256)
    (by omega : ((c.val / 32) % 1048576) / 1024 < 1024) hlo (by omega : c.val % 32 < 32)).1
  unfold outSubRawBits rW18Sub41_k2 flipCoinBit5
  change (if (tier1CoinOf5 _ _ _ _ _).val.testBit 5 then (1 : ZMod 2) else 0) =
    1 - (if c.val.testBit 5 then (1 : ZMod 2) else 0)
  conv_rhs => rw [hcEq]
  rw [ht _ (flipBit0Nat_lt (by omega) (by omega)), ht _ (by omega), flipBit0Nat_mod64]
  set r := (((c.val / 32) % 1048576) % 1024) % 64
  rw [show (flipBit0Nat r).testBit 0 = !r.testBit 0 by
    rw [Nat.testBit_zero, Nat.testBit_zero]
    unfold flipBit0Nat
    rcases Nat.mod_two_eq_zero_or_one r with hm | hm <;>
      simp [hm]]
  cases r.testBit 0 <;> norm_num

theorem potExpectK2Sub62_flipCoinBit5_sum (c : Fin (2 ^ 41)) (s nn : Bool) (sp1 sp2 : Fin 4)
    (nA nB eA eB : Fin 3 → Fin 256) :
    potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c) s nn sp1 sp2 nA nB eA eB +
    potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 (flipCoinBit5 c)) s nn sp1 sp2 nA nB eA eB =
      2 * potExpectK2DualLegW11 (w11RawBits c) s nn sp1 sp2 nA nB eA eB := by
  have hW17 (γ18 : BitAssignment 18) : withBit17 (take17Of18 γ18) (γ18 ⟨17, by omega⟩) = γ18 := by
    funext ⟨j, hj⟩
    unfold withBit17 take17Of18
    by_cases hlt : j < 17
    · simp only [hlt, ↓reduceDIte]
    · obtain rfl : j = 17 := by omega
      simp only [hlt, ↓reduceDIte]
  conv_lhs =>
    rw [← hW17 (outSubRawBits rW18Sub41_k2 c), ← hW17 (outSubRawBits rW18Sub41_k2 (flipCoinBit5 c)),
        take17_flipCoinBit5 c, bit17_flipCoinBit5 c]
  set γ17 := take17Of18 (outSubRawBits rW18Sub41_k2 c)
  have hPair (b : ZMod 2) :
      potExpectK2Sub62 (withBit17 γ17 b) s nn sp1 sp2 nA nB eA eB +
      potExpectK2Sub62 (withBit17 γ17 (1 - b)) s nn sp1 sp2 nA nB eA eB =
      potExpectK2Sub62 (withBit17 γ17 0) s nn sp1 sp2 nA nB eA eB +
      potExpectK2Sub62 (withBit17 γ17 1) s nn sp1 sp2 nA nB eA eB := by
    rcases (show b = 0 ∨ b =
        1 by fin_cases b <;> first | exact .inl rfl | exact .inr rfl) with rfl | rfl
    · rw [sub_zero]
    · rw [sub_self, add_comm]
  rw [hPair (outSubRawBits rW18Sub41_k2 c ⟨17, by omega⟩), show
      potExpectK2Sub62 (withBit17 γ17 0) s nn sp1 sp2 nA nB eA eB +
      potExpectK2Sub62 (withBit17 γ17 1) s nn sp1 sp2 nA nB eA eB =
      2 * potExpectK2DualLegK17 γ17 s nn sp1 sp2 nA nB eA eB by
    have sumZ2 (g : ZMod 2 → ℝ) : (∑ b : ZMod 2, g b) = g 0 + g 1 := Fin.sum_univ_two g
    have hSp (b : ZMod 2) (x : BitAssignment 23) :
        spliceEquiv24 γ17 (b, x) = splicedZ24Sub62 (withBit17 γ17 b) x := rfl
    unfold potExpectK2DualLegK17 potExpectK2Mode potExpectK2Sub62
    rw [← (spliceEquiv24 γ17).sum_comp, Fintype.sum_prod_type, sumZ2]
    simp only [hSp]
    unfold owK2Sub62PhaseBit3
    rw [take17_withBit17 γ17 0, take17_withBit17 γ17 1,
        show (2 ^ 23 : ℝ)⁻¹ = 2 * (2 ^ 24 : ℝ)⁻¹ by norm_num]
    ring]
  unfold potExpectK2DualLegW11 potExpectK2DualLegK17
  have hwEq : w11Sub63 γ17 = w11Sub63 (γ17OfW11 (w11RawBits c)) := by
    rw [w11Sub63_take17_outSubRawBits c, w11Sub63_γ17OfW11, equivBits11_w11RawBits]
  rw [potExpectK2Mode_congr_w11 _ _ _ hwEq]
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem g66_flipBit0_raw : allBelow 3 (fun h2 ↦ allBelow 64 (fun lo2 ↦
    g66VOpt h2 (flipBit0Nat lo2) == g66VOpt h2 lo2)) = true := by decide +kernel
theorem g66_flipBit0_cert (h2 : Fin 3) (lo2 : Fin 64) : g66VOpt h2.val (flipBit0Nat lo2.val) =
    g66VOpt h2.val lo2.val :=
    beq_iff_eq.mp ((allBelow_true_iff 64 _).mp ((allBelow_true_iff 3 _).mp g66_flipBit0_raw h2.val
    h2.isLt) lo2.val lo2.isLt)
theorem decode_flipCoinBit5_en_iff (n1 : Fin 47) (e1 : Fin 187) (c : Fin (2 ^ 41)) :
    (decodeTier1W11Opt1424Coin (flipCoinBit5 c) = .en n1 e1) ↔ (decodeTier1W11Opt1424Coin c =
    .en n1 e1) := by
  have hcLt := c.isLt; unfold flipCoinBit5
  set hi8 := (c.val / 33554432) / 256
  set lo8 := (c.val / 33554432) % 256
  set hi10 := ((c.val / 32) % 1048576) / 1024
  set lo10 := ((c.val / 32) % 1048576) % 1024
  set c5 := c.val % 32
  have hcEq : c = tier1CoinOf5 hi8 lo8 hi10 lo10 c5 :=
    Fin.ext ((coin41_decomp c).trans (tier1CoinOf5_val_eq (by omega) (by omega) (by omega)
        (by omega) (by omega)).symm)
  have hNot : (∀ i ax, (.en n1 e1 : ZeroNEremSector) ≠ .kin i ax) ∧ (.en n1 e1 : ZeroNEremSector) ≠
      .idle :=
    ⟨fun _ _ ↦ ZeroNEremSector.noConfusion, ZeroNEremSector.noConfusion⟩
  have iff_ne {a b : ZeroNEremSector} (ha : a ≠ .en n1 e1) (hb : b ≠ .en n1 e1) :
      (a = .en n1 e1) ↔ (b = .en n1 e1) := ⟨fun h ↦ absurd h ha, fun h ↦ absurd h hb⟩
  conv_rhs => rw [hcEq]
  rw [decodeTier1W11Opt1424Coin_coinOf5 (by omega) (by omega) (by omega)
        (flipBit0Nat_lt (by omega) (by omega)) (by omega),
      decodeTier1W11Opt1424Coin_coinOf5 (by omega) (by omega) (by omega) (by omega) (by omega)]
  dsimp only
  by_cases h255 : hi8 = 255
  · rw [h255, show (255 == 255) = true from rfl]
    simp only [Bool.cond_true]
    refine ⟨fun h ↦ absurd h ?_, fun h ↦ absurd h ?_⟩ <;>
      exact t1b_cond_ne_of_ne (t1b_cond_ne_of_ne (kinNucBlkT1b_fst_ne hNot hi10)
          (fun h ↦ hNot.2 h.symm))
        (t1b_cond_ne_of_ne (fun h ↦ hNot.2 h.symm) (fun h ↦ hNot.1 _ _ h.symm))
  · obtain ⟨_, _, hq5, hb2f, _⟩ := b2Spec_lt255 (show hi8 < 255 by dsimp only [hi8]; omega)
    simp only [beq_eq_false_iff_ne.mpr h255, Bool.cond_false]
    simp only [hb2f, Bool.cond_false]
    by_cases hx1023 : Nat.xor hi10 96 = 1023
    · rw [hx1023, b6Spec_1023]
      simp only [Bool.cond_true]
    · obtain ⟨_, hh2, hq31, hb6f, _⟩ := b6Spec_lt1023 (show Nat.xor hi10 96 < 1023 by
        have := (xor1024_96_props (show hi10 < 1024 by dsimp only [hi10]; omega)).1
        omega)
      let b2 := b2Spec hi8
      let b6 := b6Spec (Nat.xor hi10 96)
      rw [hb6f]
      simp only [Bool.cond_false, flipBit0Nat_div64, flipBit0Nat_mod64]
      rw [tier1W11IntCell_eq_byKind _ _ _ _ _ _ ⟨b2.2.2.1, hq5⟩ ⟨b6.2.2.1, hq31⟩,
          tier1W11IntCell_eq_byKind _ _ _ _ _ _ ⟨b2.2.2.1, hq5⟩ ⟨b6.2.2.1, hq31⟩]
      set k := tier1WalkSym96TileKind b2.2.2.1 b6.2.2.1
      have hk8 := tier1WalkSym96TileKind_lt8 b2.2.2.1 b6.2.2.1
      have hEeNe (a b) : tier1EeTag (phiU1 b6.1 b2.1) b2.2.1 b6.2.1 a b ≠ .en n1 e1 := by
        unfold tier1EeTag tier1FbKin
        dsimp only
        cases _ && _ && _ <;> exact ZeroNEremSector.noConfusion
      have hNnNe (a b) : tier1NnTag (phiU1 b6.1 b2.1) b2.2.1 b6.2.1 a b ≠ .en n1 e1 := by
        unfold tier1NnTag tier1FbKin
        dsimp only
        cases _ && _ && _ <;> exact ZeroNEremSector.noConfusion
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
        hk | hk | hk | hk | hk | hk | hk | hk <;> rw [hk] <;> simp only [tier1W11ByKind]
      · exact iff_ne (hEeNe _ _) (hEeNe _ _)
      · cases Nat.blt _ 1452
        · simp only [Bool.cond_false]
        · simp only [Bool.cond_true]
          exact iff_ne (hEeNe _ _) (hEeNe _ _)
      · exact iff_ne (hNnNe _ _) (hNnNe _ _)
      · cases Nat.blt _ 1750
        · simp only [Bool.cond_false]
        · simp only [Bool.cond_true]
          exact iff_ne (hNnNe _ _) (hNnNe _ _)
      · have hgEq := g66_flipBit0_cert ⟨b6.2.1, hh2⟩ ⟨lo10 % 64, by omega⟩
        dsimp only at hgEq
        rw [hgEq]
      · have h6Ne (lo2') : tier1W11ByKind 6 (phiU1 b6.1 b2.1) b2.2.1 b6.2.1 (lo8 % 64) lo2'
            (c5 + 32 * (lo10 / 64) + 512 * (lo8 / 64)) ≠ .en n1 e1 := by
          simp only [tier1W11ByKind, tier1FbKin]
          cases Nat.beq b2.2.1 0 <;> dsimp only [cond]
          · cases Nat.beq b2.2.1 1 && _ <;> dsimp only [cond]
            · cases Nat.beq b2.2.1 2 && _ <;> exact ZeroNEremSector.noConfusion
            · exact ZeroNEremSector.noConfusion
          · cases Nat.blt _ _ <;> exact ZeroNEremSector.noConfusion
        exact iff_ne (h6Ne _) (h6Ne _)

-- ============================================================================
-- Section 2. `vEESub62`, `vNNSub62`, `aImplWState_subCoin_sub62`, Outer Sum
-- ============================================================================

noncomputable def vEESub62 (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47)
    (e1 e2 : Fin 187) : ℝ :=
    (wEESpeciesTier1Walk (nucSpecies n1) : ℝ)⁻¹ * ∑ c : Fin (2 ^ 41),
    if decodeTier1W11Opt1424Coin c =
    .ee n1 e1 e2 then potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c) true false (nucSpecies n1) 0
    (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1))
    (sysCoord x (elecParticle e2)) else 0
noncomputable def vNNSub62 (x : Fin (2 ^ systemQubits_frozen)) (n1 n2 : Fin 47)
    (e1 : Fin 187) : ℝ :=
    (wNNSpeciesTier1Walk (nucSpecies n1) (nucSpecies n2) : ℝ)⁻¹ * ∑ c : Fin (2 ^ 41),
    if decodeTier1W11Opt1424Coin c =
    .nn n1 n2 e1 then potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c) true true (nucSpecies n1)
    (nucSpecies n2) (sysCoord x (nucParticle n1)) (sysCoord x (nucParticle n2))
    (sysCoord x (elecParticle e1)) 0 else 0
noncomputable def aImplWState_subCoin_sub62 : OpSys := aImplTier1WalkOf vEESub62 vNNSub62 vENK2
theorem sum_ee_potExpectK2Sub62 (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47) (e1 e2 : Fin 187)
    (_hlt : e1 < e2) : (∑ c : Fin (2 ^ 41), if decodeTier1W11Opt1424Coin c =
    .ee n1 e1 e2 then potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c) true false (nucSpecies n1) 0
    (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1))
    (sysCoord x (elecParticle e2)) else 0) = (wEESpeciesTier1Walk (nucSpecies n1) : ℝ) *
    vEESub62 x n1 e1 e2 := by
  unfold vEESub62
  have hwPos : 0 < wEESpeciesTier1Walk (nucSpecies n1) := by
    rw [wEESpeciesTier1Walk_eq_factor]; have := mSpCart254_pos_wstate (nucSpecies n1); omega
  have hwNe : (wEESpeciesTier1Walk (nucSpecies n1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← mul_assoc, mul_inv_cancel₀ hwNe, one_mul]

theorem sum_nn_potExpectK2Sub62 (x : Fin (2 ^ systemQubits_frozen)) (n1 n2 : Fin 47) (e1 : Fin 187)
    (hlt : n1 < n2) : (∑ c : Fin (2 ^ 41), if decodeTier1W11Opt1424Coin c =
    .nn n1 n2 e1 then potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c) true true (nucSpecies n1)
    (nucSpecies n2) (sysCoord x (nucParticle n1)) (sysCoord x (nucParticle n2))
    (sysCoord x (elecParticle e1)) 0 else 0) = (wNNSpeciesTier1Walk (nucSpecies n1)
    (nucSpecies n2) : ℝ) * vNNSub62 x n1 n2 e1 := by
  unfold vNNSub62; have hnot33 := nucSpecies_not_3_3_of_lt_wstate hlt
  have hwPos : 0 < wNNSpeciesTier1Walk (nucSpecies n1) (nucSpecies n2) := by
    rw [wNNSpeciesTier1Walk_eq_factor _ _ hnot33]
    exact Nat.mul_pos (Nat.mul_pos (mSpCart254_pos_wstate _) (mSpCart254_pos_wstate _)) (by omega)
  have hwNe : (wNNSpeciesTier1Walk (nucSpecies n1) (nucSpecies n2) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  rw [← mul_assoc, mul_inv_cancel₀ hwNe, one_mul]

def equivFlipCoinBit5 : Fin (2 ^ 41) ≃ Fin (2 ^ 41) where
  toFun := flipCoinBit5
  invFun := flipCoinBit5
  left_inv := flipCoinBit5_invol
  right_inv := flipCoinBit5_invol

theorem sum_en_potExpectK2Sub62 (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47)
    (e1 : Fin 187) : (∑ c : Fin (2 ^ 41), if decodeTier1W11Opt1424Coin c =
    .en n1 e1 then potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c) false false (nucSpecies n1) 0
    (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1)) 0 else 0) = -(wENSpeciesTier1Walk
    (nucSpecies n1) : ℝ) * vENK2 x n1 e1 := by
  let pW11 (ω : BitAssignment 11) : ℝ :=
    potExpectK2DualLegW11 ω false false (nucSpecies n1) 0 (sysCoord x (nucParticle n1)) 0
        (sysCoord x (elecParticle e1)) 0
  let F : Fin (2 ^ 41) → ℝ := fun c ↦ if decodeTier1W11Opt1424Coin c = .en n1 e1 then
    potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c) false false (nucSpecies n1) 0
      (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1)) 0 else 0
  let G : Fin (2 ^ 41) → ℝ := fun c ↦
      if decodeTier1W11Opt1424Coin c = .en n1 e1 then pW11 (w11RawBits c) else 0
  have hPair (c : Fin (2 ^ 41)) : F c + F (flipCoinBit5 c) = 2 * G c := by
    dsimp only [F, G, pW11]
    have hIff := decode_flipCoinBit5_en_iff n1 e1 c
    by_cases hSec : decodeTier1W11Opt1424Coin c = .en n1 e1
    · rw [_root_.ite_eq_left hSec, _root_.ite_eq_left (hIff.mpr hSec), _root_.ite_eq_left hSec]
      exact potExpectK2Sub62_flipCoinBit5_sum c false false (nucSpecies n1) 0 _ 0 _ 0
    · rw [_root_.ite_eq_right hSec, _root_.ite_eq_right (mt hIff.mp hSec), _root_.ite_eq_right hSec,
          add_zero, mul_zero]
  have hSumEq : (∑ c : Fin (2 ^ 41), F c) = ∑ c : Fin (2 ^ 41), G c := by
    have hFlip : (∑ c : Fin (2 ^ 41), F (flipCoinBit5 c)) = ∑ c : Fin (2 ^ 41), F c :=
      Fintype.sum_equiv equivFlipCoinBit5 (fun c ↦ F (flipCoinBit5 c)) F (fun _ ↦ rfl)
    have h2 : (∑ c, F c) + ∑ c, F (flipCoinBit5 c) = 2 * ∑ c, G c := by
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun c _ ↦ hPair c, ← Finset.mul_sum]
    linarith
  change (∑ c : Fin (2 ^ 41), F c) = _
  have hFib : (∑ c : Fin (2 ^ 41), G c) =
      ∑ ω : BitAssignment 11, (Stage1UlpElecNuc.cntENTier1 (nucSpecies n1) ω : ℝ) * pW11 ω := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w11RawBits) (t := Finset.univ)
        (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    dsimp only [G]
    rw [Finset.sum_congr rfl (fun c hc ↦ show _ = if decodeTier1W11Opt1424Coin c =
        .en n1 e1 then pW11 ω else 0 by
          rw [(Finset.mem_filter.mp hc).2]),
        ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
    refine congrArg (· * _) (congrArg Nat.cast ?_)
    rw [show Finset.univ.filter (fun c ↦ w11RawBits c = ω ∧ decodeTier1W11Opt1424Coin c =
        .en n1 e1) =
          Finset.univ.filter (fun c ↦ decodeTier1W11Opt1424Coin c = .en n1 e1 ∧ w11NatOfCoin c =
              (equivBits11 ω).val) from
          Finset.filter_congr fun c _ ↦
            ⟨fun ⟨hw, hs⟩ ↦
                ⟨hs,
                by simpa [equivBits11_w11RawBits c] using congrArg (fun b ↦
                     (equivBits11 b).val) hw⟩,
             fun ⟨hs, hw⟩ ↦
                 ⟨equivBits11.injective (Fin.ext (by rw [equivBits11_w11RawBits c]; exact hw)),
                 hs⟩⟩,
        fib_en_t1b_w11Nat_eq_cntEN2048 n1 e1 (equivBits11 ω).isLt]
    rfl
  rw [hSumEq, hFib]
  have hAvgEN := (potExpectAvgStratW11_k2_dualLeg_eq cntEETier1Walk_eq_wgtEETier1Walk
    cntNNTier1Walk_eq_wgtNNTier1Walk cntENTier1_eq_wgtEN).2.2 x n1 e1
  unfold OuterW11Bridge.potExpectAvgStratW11 OuterW11Bridge.potExpectStratW11
    PhotochemistrySolution.PopBernstein.potExpectAvgK at hAvgEN
  simp only [Bool.false_eq_true, ↓reduceIte] at hAvgEN
  have hCat0 (γ : BitAssignment 0) (ω : BitAssignment 11) :
      OuterW11Bridge.concatBitsK11 (kExt := 0) γ ω = ω := funext fun i ↦ by
    dsimp only [PhotochemistrySolution.OuterW11Bridge.concatBitsK11, Function.comp_apply]
    rcases h : (finSumFinEquiv (m := 0) (n := 11)).symm i with a | b
    · exact a.elim0
    · have hb : finSumFinEquiv (m := 0) (n := 11) (Sum.inr b) = i := by
        rw [← h, Equiv.apply_symm_apply]
      rw [finSumFinEquiv_apply_right] at hb
      exact congrArg ω (Fin.ext (by simpa [Fin.val_natAdd] using congrArg Fin.val hb))
  simp only [hCat0, Finset.sum_const, Finset.card_univ, show Fintype.card (BitAssignment 0) =
      1 by simp [BitAssignment],
    one_smul, pow_zero, inv_one, one_mul] at hAvgEN
  have hwNe : (wENSpeciesTier1Walk (nucSpecies n1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by
    rw [wENSpeciesTier1Walk_eq_factor]; have := mSpCart254_pos_wstate (nucSpecies n1); omega)
  have hMul := congrArg ((wENSpeciesTier1Walk (nucSpecies n1) : ℝ) * ·) hAvgEN
  rw [← mul_assoc, mul_inv_cancel₀ hwNe, one_mul] at hMul
  dsimp only [pW11]
  linarith
theorem sum_coin0_bOuterZeroNErem_k2_sub62_eq : (2 ^ 0 : ℂ)⁻¹ • ∑ γ : BitAssignment 0,
    ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41),
    bOuterZeroNErem decodeTier1W11Opt1424Coin (potExpectK2Sub62 (fun j ↦
    concatBitsGen γ (outSubRawBits rW18Sub41_k2 c) (Fin.natAdd 0 j))) c) =
    aImplWState_subCoin_sub62 := by
  have hCard0 : Fintype.card (BitAssignment 0) = 1 := by simp [BitAssignment]
  simp_rw [concat0_bits18];
  simp only [Finset.sum_const, Finset.card_univ, hCard0, one_smul, pow_zero, inv_one];
  have hCoin := validOuterW11_decodeTier1W11Opt1424Coin.validCoin;
  let decodeCoin := decodeTier1W11Opt1424Coin;
  let potOf (c : Fin (2 ^ 41)) : PotExpectFn := potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c);
  have h241c : (2 : ℂ) ^ 41 ≠ 0 := pow_ne_zero 41 two_ne_zero;
  have h241r : (2 : ℝ) ^ 41 ≠ 0 := pow_ne_zero 41 two_ne_zero
  have h82 : (2 : ℂ) ^ 82 = (2 : ℂ) ^ 41 * (2 : ℂ) ^ 41 := by rw [← pow_add]
  change ((2 ^ 82 : ℂ)⁻¹ • ∑ c : Fin (2 ^ 41), bOuterZeroNErem decodeCoin (potOf c) c) =
      aImplGenZeroNEremOf wEESpeciesTier1Walk wNNSpeciesTier1Walk wENSpeciesTier1Walk wKinTier1Walk
      totalSlotsIdleTier1Walk vEESub62 vNNSub62 vENK2; ext x y
  let fId : Fin (2 ^ 41) → ℂ := fun c ↦
      if decodeCoin c = .idle then ((2 ^ 41 : ℂ) • (1 : OpSys)) x y else 0
  let fKin : Fin (2 ^ 41) → ℂ := fun c ↦
      ∑ i : Particle_frozen, ∑ ax : Fin 3, if decodeCoin c = .kin i ax then (2 ^ 41 : ℂ) *
      KinNormSlice.kinNormOp i ax x y else 0
  let fPot : Fin (2 ^ 41) → ℂ := fun c ↦
      ((2 ^ 41 : ℂ) • SelectApprox.diagReal (PotSelectWiring.potTermZeroNErem decodeCoin (potOf c)
      c)) x y
  have hSplit : ∀ c : Fin (2 ^ 41),
      bOuterZeroNErem decodeCoin (potOf c) c x y = fId c + fKin c + fPot c := fun c ↦ by
    dsimp only [bOuterZeroNErem, fId, fKin, fPot]
    cases hd : decodeCoin c <;>
      simp [hd, ite_and, PotSelectWiring.potTermZeroNErem, SelectApprox.diagReal,
          Matrix.smul_apply, smul_eq_mul]
  unfold aImplGenZeroNEremOf;
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, smul_eq_mul, hSplit];
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hKinDiv : (∑ i : Particle_frozen, ∑ w : Fin 3, (((wKinTier1Walk i : ℝ) / (2 ^ 41 : ℝ)) : ℂ) *
      KinNormSlice.kinNormOp i w x y) = ((2 ^ 41 : ℂ)⁻¹) * ∑ i : Particle_frozen, ∑ w : Fin 3,
      (wKinTier1Walk i : ℂ) * KinNormSlice.kinNormOp i w x y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    push_cast; ring
  have sId : (∑ c : Fin (2 ^ 41), fId c) = (totalSlotsIdleTier1Walk : ℂ) *
      ((2 ^ 41 : ℂ) • (1 : OpSys)) x y := by
    dsimp only [fId]; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hCoin .idle]
  have sKin : (∑ c : Fin (2 ^ 41), fKin c) = (2 ^ 41 : ℂ) * ∑ i : Particle_frozen, ∑ ax : Fin 3,
      (wKinTier1Walk i : ℂ) * KinNormSlice.kinNormOp i ax x y := by
    dsimp only [fKin]; rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ax _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hCoin (.kin i ax)]; ring
  by_cases hxy : x = y
  · subst hxy
    let tEE (c : Fin (2 ^ 41)) : ℝ := ∑ n1 : Fin 47, ∑ e1 : Fin 187, ∑ e2 : Fin 187,
      if decodeCoin c = .ee n1 e1 e2 then potOf c true false (nucSpecies n1) 0
        (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1))
            (sysCoord x (elecParticle e2)) else 0
    let tNN (c : Fin (2 ^ 41)) : ℝ := ∑ n1 : Fin 47, ∑ n2 : Fin 47, ∑ e1 : Fin 187,
      if decodeCoin c = .nn n1 n2 e1 then potOf c true true (nucSpecies n1) (nucSpecies n2)
        (sysCoord x (nucParticle n1)) (sysCoord x (nucParticle n2))
            (sysCoord x (elecParticle e1)) 0 else 0
    let tEN (c : Fin (2 ^ 41)) : ℝ := ∑ n1 : Fin 47, ∑ e1 : Fin 187,
      if decodeCoin c = .en n1 e1 then potOf c false false (nucSpecies n1) 0
        (sysCoord x (nucParticle n1)) 0 (sysCoord x (elecParticle e1)) 0 else 0
    have hPotSplit (c : Fin (2 ^ 41)) :
        PotSelectWiring.potTermZeroNErem decodeCoin (potOf c) c x = tEE c + tNN c + tEN c := by
      dsimp only [tEE, tNN, tEN]
      cases hd : decodeCoin c <;> simp [PotSelectWiring.potTermZeroNErem, hd, ite_and]
    have sEE : (∑ c : Fin (2 ^ 41), tEE c) = ∑ n1 : Fin 47, ∑ e1 : Fin 187, ∑ e2 : Fin 187,
        if e1 < e2 then (wEESpeciesTier1Walk (nucSpecies n1) : ℝ) * vEESub62 x n1 e1 e2 else 0 := by
      dsimp only [tEE]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n1 _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e1 _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e2 _ ↦ ?_
      by_cases hlt : e1 < e2
      · simp only [hlt, ↓reduceIte]
        exact sum_ee_potExpectK2Sub62 x n1 e1 e2 hlt
      · have hE : Finset.univ.filter (fun c ↦ decodeCoin c = .ee n1 e1 e2) = ∅ :=
          Finset.card_eq_zero.mp (by simpa only [hlt, ↓reduceIte] using hCoin (.ee n1 e1 e2))
        rw [_root_.ite_eq_right hlt, ← Finset.sum_filter, hE, Finset.sum_empty]
    have sNN : (∑ c : Fin (2 ^ 41), tNN c) = ∑ n1 : Fin 47, ∑ n2 : Fin 47, ∑ e1 : Fin 187,
        if n1 < n2 then (wNNSpeciesTier1Walk (nucSpecies n1) (nucSpecies n2) : ℝ) *
            vNNSub62 x n1 n2 e1 else 0 := by
      dsimp only [tNN]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n1 _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n2 _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e1 _ ↦ ?_
      by_cases hlt : n1 < n2
      · simp only [hlt, ↓reduceIte]
        exact sum_nn_potExpectK2Sub62 x n1 n2 e1 hlt
      · have hN : Finset.univ.filter (fun c ↦ decodeCoin c = .nn n1 n2 e1) = ∅ :=
          Finset.card_eq_zero.mp (by simpa only [hlt, ↓reduceIte] using hCoin (.nn n1 n2 e1))
        rw [_root_.ite_eq_right hlt, ← Finset.sum_filter, hN, Finset.sum_empty]
    have sEN : (∑ c : Fin (2 ^ 41), tEN c) =
        -(∑ n1 : Fin 47, ∑ e1 : Fin 187, (wENSpeciesTier1Walk (nucSpecies n1) : ℝ) * vENK2 x n1 e1)
            := by
      dsimp only [tEN]
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun n1 _ ↦ ?_
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e1 _ ↦ ?_
      have h := sum_en_potExpectK2Sub62 x n1 e1
      dsimp only [decodeCoin, potOf]
      linarith
    have sPot : (∑ c : Fin (2 ^ 41), fPot c) = (2 ^ 41 : ℂ) * ((2 ^ 41 : ℂ) *
        (PhotochemistrySolution.GenWeightsSelect.vDiagGenZeroNErem wEESpeciesTier1Walk
            wNNSpeciesTier1Walk
          wENSpeciesTier1Walk vEESub62 vNNSub62 vENK2 x : ℂ)) := by
      dsimp only [fPot]
      simp only [PhotochemistrySolution.SelectApprox.diagReal, Matrix.smul_apply,
        Matrix.diagonal_apply_eq, smul_eq_mul, ← Finset.mul_sum]
      refine congrArg ((2 ^ 41 : ℂ) * ·) ?_
      have hreal : (∑ c : Fin (2 ^ 41),
          PhotochemistrySolution.PotSelectWiring.potTermZeroNErem decodeCoin (potOf c) c x) =
          (2 ^ 41 : ℝ) * GenWeightsSelect.vDiagGenZeroNErem wEESpeciesTier1Walk
            wNNSpeciesTier1Walk wENSpeciesTier1Walk vEESub62 vNNSub62 vENK2 x := by
        rw [Finset.sum_congr rfl fun c _ ↦ hPotSplit c, Finset.sum_add_distrib,
            Finset.sum_add_distrib, sEE, sNN, sEN]
        unfold PhotochemistrySolution.GenWeightsSelect.vDiagGenZeroNErem
        rw [mul_sub, mul_add]
        have h1 (w : ℕ) (v : ℝ) : (2 ^ 41 : ℝ) * (((w : ℝ) / (2 ^ 41 : ℝ)) * v) = (w : ℝ) * v := by
          field_simp [h241r]
        simp only [Finset.mul_sum, mul_ite, mul_zero, h1]
        ring
      exact (Complex.ofReal_sum Finset.univ _).symm.trans
        ((congrArg Complex.ofReal hreal).trans (by push_cast; rfl))
    rw [sId, sKin, sPot, hKinDiv, h82];
    simp only [SelectApprox.diagReal, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul];
    push_cast
    field_simp [h241c]
  · have sPot0 : (∑ c : Fin (2 ^ 41), fPot c) = 0 := by
      dsimp only [fPot];
      simp [SelectApprox.diagReal, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hxy]
    rw [sId, sKin, sPot0, hKinDiv, h82];
    simp only [SelectApprox.diagReal, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hxy,
        smul_eq_mul]; push_cast
    field_simp [h241c]
    ring

-- ============================================================================
-- Section 3. Unit Bounds `|vEESub62| <= 1`, `|vNNSub62| <= 1`, `|vENK2| <= 1`
-- ============================================================================

theorem abs_potExpectK2Sub62_le_one (γ18 : BitAssignment 18)
    (s nn : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256) :
    |potExpectK2Sub62 γ18 s nn sp1 sp2 nA nB eA eB| ≤ 1 := by
  unfold potExpectK2Sub62
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 ^ 23 : ℝ)⁻¹)]
  refine (inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 23)).mpr ?_
  have h1 := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
    (Finset.sum_le_sum fun z23 _ ↦
      (show |if owK2Sub62PhaseBit3 γ18 s nn sp1 sp2 nA (if nn then nB else eB) eA z23 = 1
        then (-1 : ℝ) else 1| ≤ 1 by split_ifs <;> norm_num))
  have hCard : (Finset.univ : Finset (BitAssignment 23)).card = 2 ^ 23 := by simp [BitAssignment]
  rw [Finset.sum_const, hCard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one] at h1
  rwa [mul_one]

theorem vSub62_unit :
    (∀ x n1 e1 e2, e1 < e2 → |vEESub62 x n1 e1 e2| ≤ 1) ∧
    (∀ x n1 n2 e1, n1 < n2 → |vNNSub62 x n1 n2 e1| ≤ 1) ∧
    (∀ x n1 e1, |vENK2 x n1 e1| ≤ 1) := by
  have hCoin := validOuterW11_decodeTier1W11Opt1424Coin.validCoin
  have hBnd (s : ZeroNEremSector) {w : ℕ} (hw : 0 < w)
      (hC : (Finset.univ.filter (fun c ↦ decodeTier1W11Opt1424Coin c = s)).card = w)
      (f : Fin (2 ^ 41) → ℝ) (hf : ∀ c, |f c| ≤ 1) :
      |(w : ℝ)⁻¹ * ∑ c : Fin (2 ^ 41), if decodeTier1W11Opt1424Coin c = s then f c else 0| ≤
        1 := by
    have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
    rw [abs_mul, abs_of_pos (inv_pos.mpr hwR), ← Finset.sum_filter]
    refine (inv_mul_le_iff₀ hwR).mpr ?_
    have h1 := (Finset.abs_sum_le_sum_abs f
      (Finset.univ.filter (fun c ↦ decodeTier1W11Opt1424Coin c = s))).trans
      (Finset.sum_le_sum fun c _ ↦ hf c)
    rw [Finset.sum_const, hC, nsmul_eq_mul, mul_one] at h1
    rwa [mul_one]
  refine ⟨fun x n1 e1 e2 hlt ↦ ?_, fun x n1 n2 e1 hlt ↦ ?_, vK2_unit.2.2⟩
  · refine hBnd (.ee n1 e1 e2) (by
        rw [wEESpeciesTier1Walk_eq_factor]
        have := mSpCart254_pos_wstate (nucSpecies n1)
        omega)
      (by simpa [hlt] using hCoin (.ee n1 e1 e2)) _ (fun c ↦ abs_potExpectK2Sub62_le_one _ _ _ _
        _ _ _ _ _)
  · have hnot33 := nucSpecies_not_3_3_of_lt_wstate hlt
    refine hBnd (.nn n1 n2 e1) (by
        rw [wNNSpeciesTier1Walk_eq_factor _ _ hnot33]
        exact Nat.mul_pos (Nat.mul_pos (mSpCart254_pos_wstate _) (mSpCart254_pos_wstate _))
          (by omega))
      (by simpa [hlt] using hCoin (.nn n1 n2 e1)) _ (fun c ↦ abs_potExpectK2Sub62_le_one _ _ _ _
        _ _ _ _ _)

-- ============================================================================
-- Section 4. 23-Bit Collapse & Dual-Polarity `.ee` / `.nn` Stratification
-- ============================================================================

def mergeLo7 (u0 u1 : Fin 2) (u5 : Fin 32) : BitAssignment 7 := fun j ↦
    if j.val = 0 then equivBitZMod2.symm u0 else if j.val =
    1 then equivBitZMod2.symm u1 else if u5.val.testBit (j.val - 2) then 1 else 0
def equivLo7 : (Fin 2 × Fin 2 × Fin 32) ≃ BitAssignment 7 where
  toFun p := mergeLo7 p.1 p.2.1 p.2.2
  invFun lo :=
    (equivBitZMod2 (lo ⟨0, by omega⟩),
     equivBitZMod2 (lo ⟨1, by omega⟩),
     ⟨natOfZModBits 5 (fun i ↦ lo ⟨2 + i.val, by omega⟩), natOfZModBits_lt 5 _⟩)
  left_inv p := by
    rcases p with ⟨u0, u1, u5⟩
    have h0 : equivBitZMod2 (mergeLo7 u0 u1 u5 ⟨0, by omega⟩) = u0 :=
      equivBitZMod2.apply_symm_apply u0
    have h1 : equivBitZMod2 (mergeLo7 u0 u1 u5 ⟨1, by omega⟩) = u1 :=
      equivBitZMod2.apply_symm_apply u1
    have hFn : (fun i : Fin 5 ↦ mergeLo7 u0 u1 u5 ⟨2 + i.val, by omega⟩) =
        fun i : Fin 5 ↦ if u5.val.testBit i.val then (1 : ZMod 2) else 0 := by
      funext i
      have hn0 : ¬(2 + i.val = 0) := by omega
      have hn1 : ¬(2 + i.val = 1) := by omega
      have hi : 2 + i.val - 2 = i.val := by omega
      simp only [mergeLo7, hn0, hn1, ↓reduceIte, hi]
    have h5 : (⟨natOfZModBits 5 (fun i ↦ mergeLo7 u0 u1 u5 ⟨2 + i.val, by omega⟩),
        natOfZModBits_lt 5 _⟩ : Fin 32) = u5 := by
      apply Fin.ext; dsimp only
      rw [hFn, natOfZModBits_of_testBit 5 u5.val, Nat.mod_eq_of_lt (show u5.val <
          2 ^ 5 from u5.isLt)]
    exact Prod.ext h0 (Prod.ext h1 h5)
  right_inv lo := by
    funext j; dsimp only [mergeLo7]
    by_cases hj0 : j.val = 0
    · simp only [hj0, ↓reduceIte]
      have hjEq : (⟨0, by omega⟩ : Fin 7) = j := Fin.ext hj0.symm
      rw [equivBitZMod2.symm_apply_apply, hjEq]
    · simp only [hj0, ↓reduceIte]
      by_cases hj1 : j.val = 1
      · simp only [hj1, ↓reduceIte]
        have hjEq : (⟨1, by omega⟩ : Fin 7) = j := Fin.ext hj1.symm
        rw [equivBitZMod2.symm_apply_apply, hjEq]
      · simp only [hj1, ↓reduceIte]
        let i : Fin 5 := ⟨j.val - 2, by have := j.isLt; omega⟩
        set v5 := natOfZModBits 5 (fun q : Fin 5 ↦ lo ⟨2 + q.val, by omega⟩)
        have hBits := finBitsVal_inj (m := 5)
          (f := fun q : Fin 5 ↦ if v5.testBit q.val then (1 : ZMod 2) else 0)
          (g := fun q : Fin 5 ↦ lo ⟨2 + q.val, by omega⟩) <| by
            rw [finBitsVal_eq_natOfZModBits, finBitsVal_eq_natOfZModBits,
                natOfZModBits_of_testBit 5 v5]; exact Nat.mod_eq_of_lt (natOfZModBits_lt 5 _)
        have hi := congrFun hBits i; dsimp only [i] at hi
        have hjEq : (⟨2 + (j.val - 2), by omega⟩ : Fin 7) = j := Fin.ext (by dsimp; omega)
        rw [hjEq] at hi; exact hi
def splitEquiv23 : (Fin 16 ⊕ Fin 7) ≃ Fin 23 where
  toFun := Sum.elim (fun k ↦ ⟨7 + k.val, by omega⟩) (fun j ↦ ⟨j.val, by omega⟩)
  invFun i := if h : i.val < 7 then Sum.inr ⟨i.val, h⟩ else Sum.inl ⟨i.val - 7, by omega⟩
  left_inv x := by
    rcases x with k | j
    · simp [show ¬(7 + k.val < 7) by omega]
    · simp [j.isLt]
  right_inv i := by
    apply Fin.ext
    by_cases h : i.val < 7
    · simp [h]
    · simp [h]; omega

def fullEquiv23 : ((Fin 16 → ZMod 2) × BitAssignment 7) ≃ BitAssignment 23 :=
    (Equiv.sumArrowEquivProdArrow (Fin 16) (Fin 7)
    (ZMod 2)).symm.trans (Equiv.arrowCongr splitEquiv23 (Equiv.refl (ZMod 2)))
def vz0BoolOfCoin (c : Fin (2 ^ 41)) : Bool :=
    Bool.xor (Bool.xor (c.val.testBit 5) (c.val.testBit 25)) (Bool.xor (c.val.testBit 15)
    (c.val.testBit 20))
theorem zmod2_add_ite_bool (a b : Bool) : (if a then (1 : ZMod 2) else 0) +
    (if b then (1 : ZMod 2) else 0) = if Bool.xor a b then 1 else 0 := by
  cases a <;> cases b <;> rfl

theorem affineBit13_7483_eq (x : ℕ) : affineBit13 7483 x = Bool.xor (x.testBit 0)
    (Bool.xor (x.testBit 1) (Bool.xor (x.testBit 3) (Bool.xor (x.testBit 4) (Bool.xor (x.testBit 5)
    (Bool.xor (x.testBit 8) (Bool.xor (x.testBit 10) (Bool.xor (x.testBit 11) (x.testBit 12))))))))
    := by
  unfold affineBit13
  dsimp only [parity13Aux]
  simp only [show (7483 : ℕ).testBit 13 = false by decide,
    show (7483 : ℕ).testBit 0 = true by decide, show (7483 : ℕ).testBit 1 = true by decide,
    show (7483 : ℕ).testBit 2 = false by decide, show (7483 : ℕ).testBit 3 = true by decide,
    show (7483 : ℕ).testBit 4 = true by decide, show (7483 : ℕ).testBit 5 = true by decide,
    show (7483 : ℕ).testBit 6 = false by decide, show (7483 : ℕ).testBit 7 = false by decide,
    show (7483 : ℕ).testBit 8 = true by decide, show (7483 : ℕ).testBit 9 = false by decide,
    show (7483 : ℕ).testBit 10 = true by decide, show (7483 : ℕ).testBit 11 = true by decide,
    show (7483 : ℕ).testBit 12 = true by decide,
    Bool.false_eq_true, ↓reduceIte, Bool.false_xor, Bool.xor_assoc]

theorem x13OfW11U01_bits_eq (w : Fin 2048) (u0 u1 : Fin 2) :
    (x13OfW11U01 w u0 u1 < 8192) ∧
    (∀ k : Fin 11, (x13OfW11U01 w u0 u1).testBit k.val = w.val.testBit k.val) ∧
    ((x13OfW11U01 w u0 u1).testBit 11 = (u0.val == 1)) ∧
    ((x13OfW11U01 w u0 u1).testBit 12 = (u1.val == 1)) := by
  have hBit (n j : ℕ) : n.testBit j = decide ((n / 2 ^ j) % 2 = 1) := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with hm | hm <;> simp [hm]
  refine ⟨by unfold x13OfW11U01; omega, fun k ↦ ?_, ?_, ?_⟩
  · rcases (by have := k.isLt; omega : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val =
                 4 ∨
      k.val = 5 ∨ k.val = 6 ∨ k.val = 7 ∨ k.val = 8 ∨ k.val = 9 ∨ k.val = 10) with
      hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk <;>
      (rw [hk, hBit, hBit, decide_eq_decide]; unfold x13OfW11U01; omega)
  · rw [hBit, show (2 ^ 11 : ℕ) = 2048 by norm_num]
    unfold x13OfW11U01
    rw [show (w.val + 2048 * u0.val + 4096 * u1.val) / 2048 = u0.val + 2 *
        u1.val by have := w.isLt; omega]
    fin_cases u0 <;> fin_cases u1 <;> rfl
  · rw [hBit, show (2 ^ 12 : ℕ) = 4096 by norm_num]
    unfold x13OfW11U01
    rw [show (w.val + 2048 * u0.val + 4096 * u1.val) / 4096 =
        u1.val by have := w.isLt; have := u0.isLt; omega]
    fin_cases u1 <;> rfl

theorem otp2_outSubRawBits_eq (c : Fin (2 ^ 41)) (u0 u1 : Fin 2) :
    let w : Fin 2048 := ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩
    outSubRawBits rW18Sub41_k2 c ⟨17, by omega⟩ +
      otpDeltaSub62 (outSubRawBits rW18Sub41_k2 c)
        (equivBitZMod2.symm u0) (equivBitZMod2.symm u1) =
    if Bool.xor (vz0BoolOfCoin c) (affineBit13 7483 (x13OfW11U01 w u0 u1))
    then 1 else 0 := by
  dsimp only
  set w : Fin 2048 := ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩
  obtain ⟨_, hxk, hx11, hx12⟩ := x13OfW11U01_bits_eq w u0 u1
  set x := x13OfW11U01 w u0 u1
  have hBitW (j : ℕ) (hj : j < 11) :
      outSubRawBits rW18Sub41_k2 c ⟨j, by omega⟩ = if x.testBit j then 1 else 0 := by
    change take17Of18 (outSubRawBits rW18Sub41_k2 c) ⟨j, by omega⟩ = _
    rw [take17_outSubRawBits_lt11 c ⟨j, hj⟩, w11RawBits_eq_testBit_w11NatOfCoin c ⟨j, hj⟩,
        ← hxk ⟨j, hj⟩]
  have hc17 : outSubRawBits rW18Sub41_k2 c ⟨17, by omega⟩ = if c.val.testBit 5 then 1 else 0 := rfl
  have hc11 : outSubRawBits rW18Sub41_k2 c ⟨11, by omega⟩ = if c.val.testBit 25 then 1 else 0 := rfl
  have hc12 : outSubRawBits rW18Sub41_k2 c ⟨12, by omega⟩ = if c.val.testBit 15 then 1 else 0 := rfl
  have hc13 : outSubRawBits rW18Sub41_k2 c ⟨13, by omega⟩ = if c.val.testBit 20 then 1 else 0 := rfl
  have heqZ (u : Fin 2) : equivBitZMod2.symm u = if u.val == 1 then (1 : ZMod 2) else 0 := by
    fin_cases u <;> rfl
  unfold otpDeltaSub62 vz0BoolOfCoin
  rw [hc17, hc11, hc12, hc13, hBitW 0 (by omega), hBitW 1 (by omega), hBitW 3 (by omega),
      hBitW 4 (by omega), hBitW 5 (by omega), hBitW 8 (by omega), hBitW 10 (by omega),
      heqZ u0, heqZ u1, ← hx11, ← hx12, affineBit13_7483_eq x, add_zero,
      show ∀ a5 a25 a15 a20 b0 b1 b3 b4 b5 b8 b10 b11 b12 : ZMod 2,
        a5 + (a25 + (a15 + (a20 + (b0 + (b1 + (b3 + (b4 + (b5 + (b8 + (b10 + (b11 + b12))))))))))) =
        ((a5 + a25) + (a15 + a20)) +
          (b0 + (b1 + (b3 + (b4 + (b5 + (b8 + (b10 + (b11 + b12)))))))) by intros; ring]
  simp only [zmod2_add_ite_bool]

attribute [local irreducible] w11NatOfCoin outSubRawBits vz0BoolOfCoin affineBit13 x13OfW11U01 in
theorem spliced_fullEquiv23_eq_fullEquiv24 (c : Fin (2 ^ 41))
    (hi : Fin 16 → ZMod 2) (u0 u1 : Fin 2) (u5 : Fin 32) :
    let w : Fin 2048 := ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩
    let b2 : ℕ := if Bool.xor (vz0BoolOfCoin c)
        (affineBit13 7483 (x13OfW11U01 w u0 u1)) then 1 else 0
    splicedZ24Sub62 (outSubRawBits rW18Sub41_k2 c) (fullEquiv23 (hi, equivLo7 (u0, u1, u5))) =
      fullEquiv24 (hi, equivLo8 (u0, u1, ⟨b2 + 2 * u5.val,
        by dsimp [b2]; split_ifs <;> omega⟩)) := by
  intro w b2
  let bw := affineBit13 7483 (x13OfW11U01 w u0 u1)
  let u6 : Fin 64 := ⟨b2 + 2 * u5.val, by dsimp [b2]; split_ifs <;> omega⟩
  have htb0 : (b2 + 2 * u5.val).testBit 0 = Bool.xor (vz0BoolOfCoin c) bw := by
    change ((if Bool.xor (vz0BoolOfCoin c) bw then 1 else 0) + 2 * u5.val).testBit 0 =
      Bool.xor (vz0BoolOfCoin c) bw
    rw [Nat.testBit_zero]
    cases Bool.xor (vz0BoolOfCoin c) bw <;> simp [Nat.mul_mod_right]
  have htbS (r : ℕ) : (b2 + 2 * u5.val).testBit (1 + r) = u5.val.testBit r := by
    rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        show (2 ^ (1 + r) : ℕ) = 2 * 2 ^ r by rw [Nat.pow_add], ← Nat.div_div_eq_div_mul,
        show (b2 + 2 * u5.val) / 2 = u5.val by dsimp only [b2]; split_ifs <;> omega]
  have hz23_lo (j : Fin 7) : fullEquiv23 (hi, equivLo7 (u0, u1, u5))
      ⟨j.val, by omega⟩ = mergeLo7 u0 u1 u5 j := by
    change (Sum.elim hi (mergeLo7 u0 u1 u5)) (splitEquiv23.symm ⟨j.val, by omega⟩) = _
    simp [splitEquiv23, j.isLt]
  have hz23_hi (m : Fin 16) : fullEquiv23 (hi, equivLo7 (u0, u1, u5)) ⟨7 + m.val, by omega⟩ =
      hi m := by
    change (Sum.elim hi (mergeLo7 u0 u1 u5)) (splitEquiv23.symm ⟨7 + m.val, by omega⟩) = hi m
    simp [splitEquiv23, show ¬(7 + m.val < 7) by omega]
  have hz24_hi (m : Fin 16) : fullEquiv24 (hi, equivLo8 (u0, u1, u6)) ⟨8 + m.val, by omega⟩ =
      hi m := by
    change (Sum.elim hi (mergeLo8 u0 u1 u6)) (splitEquiv24.symm ⟨8 + m.val, by omega⟩) = hi m
    simp [splitEquiv24, show ¬(8 + m.val < 8) by omega]
  funext ⟨kv, hkv⟩
  by_cases hk8 : kv < 8
  · rw [fullEquiv24_lo hi _ ⟨kv, hk8⟩]
    change splicedZ24Sub62 _ _ ⟨kv, hkv⟩ = mergeLo8 u0 u1 u6 ⟨kv, hk8⟩
    unfold splicedZ24Sub62
    by_cases hk2 : kv < 2
    · simp only [hk2, ↓reduceDIte, hz23_lo ⟨kv, by omega⟩]
      unfold mergeLo7 mergeLo8
      rcases (by omega : kv = 0 ∨ kv = 1) with rfl | rfl <;> simp
    · by_cases hkEq2 : kv = 2
      · subst hkEq2
        simp only [show ¬((2 : ℕ) < 2) by omega, ↓reduceDIte, hz23_lo ⟨0, by omega⟩,
            hz23_lo ⟨1, by omega⟩]
        change outSubRawBits rW18Sub41_k2 c ⟨17, by omega⟩ +
          otpDeltaSub62 (outSubRawBits rW18Sub41_k2 c) (equivBitZMod2.symm u0)
              (equivBitZMod2.symm u1) = _
        rw [otp2_outSubRawBits_eq c u0 u1]
        unfold mergeLo8
        simp only [show ¬((2 : ℕ) = 0) by omega, show ¬((2 : ℕ) = 1) by omega, ↓reduceIte]
        exact congrArg (if · then (1 : ZMod 2) else 0) htb0.symm
      · simp only [hk2, hkEq2, ↓reduceDIte, hz23_lo ⟨kv - 1, by omega⟩]
        unfold mergeLo7 mergeLo8
        simp only [show ¬(kv - 1 = 0) by omega, show ¬(kv - 1 = 1) by omega,
          show ¬(kv = 0) by omega, show ¬(kv = 1) by omega, ↓reduceIte]
        change _ = if (b2 + 2 * u5.val).testBit (kv - 2) then (1 : ZMod 2) else 0
        rw [show kv - 2 = 1 + (kv - 3) by omega, htbS, show kv - 1 - 2 = kv - 3 by omega]
  · rw [show (⟨kv, hkv⟩ : Fin 24) = ⟨8 + (kv - 8), by omega⟩ from Fin.ext (by dsimp; omega),
        hz24_hi ⟨kv - 8, by omega⟩]
    unfold splicedZ24Sub62
    simp only [show ¬(8 + (kv - 8) < 2) by omega, show ¬(8 + (kv - 8) = 2) by omega, ↓reduceDIte]
    rw [show (⟨8 + (kv - 8) - 1, by omega⟩ : Fin 23) =
        ⟨7 + (kv - 8), by omega⟩ from Fin.ext (by dsimp; omega),
        hz23_hi ⟨kv - 8, by omega⟩]

def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow f n + f n

theorem sum_fin_eq_sumBelow : ∀ (n : ℕ) (f : ℕ → ℕ),
    (∑ i : Fin n, f i.val) = sumBelow f n
  | 0, _ => rfl
  | n + 1, f => by
      rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last];
      rw [sum_fin_eq_sumBelow n f]; rfl
theorem sum_fin2_eq_sumBelow (m n : ℕ) (g : ℕ → ℕ → ℕ) : (∑ i : Fin m, ∑ j : Fin n, g i.val j.val) =
    sumBelow (fun i ↦ sumBelow (fun j ↦ g i j) n) m := by
  have h1 : ∀ i : Fin m, (∑ j : Fin n, g i.val j.val) = sumBelow (fun j ↦ g i.val j) n := fun i ↦
      sum_fin_eq_sumBelow n (fun j ↦ g i.val j)
  simp_rw [h1]
  exact sum_fin_eq_sumBelow m (fun i ↦ sumBelow (fun j ↦ g i j) n)

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem hermite_u5_raw : allBelow 32 (fun q5 ↦ Nat.beq (sumBelow (fun u5 ↦ (q5 + u5) / 32) 32) q5) =
    true := by decide +kernel
theorem hermite_u5_cert (q5 : Fin 32) : (∑ u5 : Fin 32, (q5.val + u5.val) / 32) = q5.val := by
  rw [sum_fin_eq_sumBelow 32 (fun x ↦ (q5.val + x) / 32)]
  exact Nat.beq_eq.mp ((allBelow_true_iff 32 _).mp hermite_u5_raw q5.val q5.isLt)

theorem hermite_div16384_add_512 (A d9 : ℕ)
    (_hd9 : d9 < 512) : (∑ u5 : Fin 32, (A + (d9 + 512 * u5.val)) / 16384) = (A + d9) / 512 := by
  set N := A + d9
  set Q := N / 16384
  set q5 : Fin 32 := ⟨(N % 16384) / 512, by omega⟩
  have hTerm : ∀ u5 : Fin 32, (A + (d9 + 512 * u5.val)) / 16384 = Q + (q5.val + u5.val) / 32 :=
    fun u5 ↦ by dsimp only [N, Q, q5]; omega
  simp_rw [hTerm];
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      hermite_u5_cert q5]; dsimp only [N, Q, q5, smul_eq_mul]; omega
theorem avg_u5_q14 (q : Fin 32 → ℕ) (S : ℕ) (hS : (∑ u5 : Fin 32, q u5) = S) (C : ℝ) : (32 : ℝ)⁻¹ *
    (∑ u5 : Fin 32, ((16384 * (q u5 : ℝ) - C) / (2 ^ 29 : ℝ))) = (512 * (S : ℝ) - C) / (2 ^ 29 : ℝ)
    := by
  have hSR : (∑ u5 : Fin 32, (q u5 : ℝ)) = (S : ℝ) := by exact_mod_cast hS
  have hIn : ∀ u5 : Fin 32,
      ((16384 * (q u5 : ℝ) - C) / (2 ^ 29 : ℝ)) =
      (16384 / (2 ^ 29 : ℝ)) * (q u5 : ℝ) - (C / (2 ^ 29 : ℝ)) := fun _ ↦ by ring
  simp_rw [hIn, Finset.sum_sub_distrib, ← Finset.mul_sum, hSR, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  field_simp; ring

theorem potExpectK2Sub62_collapse_scr
    (c : Fin (2 ^ 41)) (nn : Bool) (sp1 sp2 : Fin 4) (nA nB eA eB : Fin 3 → Fin 256)
    (fn : ℕ → ℕ)
    (hMidW : ∀ y z, midWTap29OfMode true nn y z = fn y)
    (hMod : (((v1Fin8DualLeg true nn sp1 (fin8Bin (openCoordDistSq nA eA)) : ℤ) +
              (v2Fin8DualLeg true nn sp2 (owB2Of3Port nn nA (if nn then nB else eB) eA) : ℤ)) -
            (32768 - cShift14DualLeg true nn sp1
              (fin8Bin (openCoordDistSq nA eA))
              (owB2Of3Port nn nA (if nn then nB else eB) eA))) % 131072 = 0)
    (hCap : ∀ (w : Fin 2048) (o9 : Fin 512) {zLo14 : ℕ}, zLo14 < 16384 →
      |(((midWTap29OfMode true nn
            (ySampleK2 word512DualLegLo6 nn
              (sectorDist3DSq3 true nn nA (if nn then nB else eB) eA) w o9)
            zLo14 + zLo14) / 16384 : ℕ) : ℤ) -
        cShift14DualLeg true nn sp1
          (fin8Bin (openCoordDistSq nA eA))
          (owB2Of3Port nn nA (if nn then nB else eB) eA)| ≤ 32768) :
    potExpectK2Sub62 (outSubRawBits rW18Sub41_k2 c) true nn sp1 sp2 nA nB eA eB =
      (4 : ℝ)⁻¹ * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
        ((512 * (((fn (ySampleK2 word512DualLegLo6 nn
              (sectorDist3DSq3 true nn nA (if nn then nB else eB) eA)
              ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩
              (o9Of13 (x13OfW11U01 ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩ u0 u1))) +
            (df8Of13 (x13OfW11U01 ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩ u0 u1)).val +
            (if Bool.xor (vz0BoolOfCoin c)
                  (affineBit13 7483 (x13OfW11U01 ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩ u0 u1))
              then 256 else 0)) / 512 : ℕ) : ℝ) -
          16384 * (cShift14DualLeg true nn sp1
            (fin8Bin (openCoordDistSq nA eA))
            (owB2Of3Port nn nA (if nn then nB else eB) eA) : ℝ)) / (2 ^ 29 : ℝ)) := by
  unfold potExpectK2Sub62
  set cSh := cShift14DualLeg true nn sp1
    (fin8Bin (openCoordDistSq nA eA))
    (owB2Of3Port nn nA (if nn then nB else eB) eA)
  set w : Fin 2048 := ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩
  have hwTake : w11Sub63 (take17Of18 (outSubRawBits rW18Sub41_k2 c)) = w :=
      w11Sub63_take17_outSubRawBits c; rw [← fullEquiv23.sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm, ← equivLo7.sum_comp, Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]
  have hp23 : (2 ^ 23 : ℝ)⁻¹ = (4 : ℝ)⁻¹ * ((32 : ℝ)⁻¹ * (2 ^ 16 : ℝ)⁻¹) := by norm_num
  rw [hp23, mul_assoc, Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro u0 _
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u1 _
  rw [mul_assoc, Finset.mul_sum]
  set x13 := x13OfW11U01 w u0 u1
  set y36 := ySampleK2 word512DualLegLo6 nn
    (sectorDist3DSq3 true nn nA (if nn then nB else eB) eA) w (o9Of13 x13)
  set bit2 : ℕ := if Bool.xor (vz0BoolOfCoin c) (affineBit13 7483 x13) then 1 else 0
  have hInner : ∀ u5 : Fin 32,
      (2 ^ 16 : ℝ)⁻¹ * (∑ hi : (Fin 16 → ZMod 2),
        if owK2Sub62PhaseBit3 (outSubRawBits rW18Sub41_k2 c)
            true nn sp1 sp2 nA (if nn then nB else eB) eA
            (fullEquiv23 (hi, equivLo7 (u0, u1, u5))) = 1
        then (-1 : ℝ) else 1) =
      ((16384 * ((((midWTap29OfMode true nn y36
            ((df8Of13 x13).val + 256 * (bit2 + 2 * u5.val)) +
            ((df8Of13 x13).val + 256 * (bit2 + 2 * u5.val))) / 16384 : ℕ) : ℝ)) -
        16384 * (cSh : ℝ)) / (2 ^ 29 : ℝ)) := fun u5 ↦ by
    set zLo := (df8Of13 x13).val + 256 * (bit2 + 2 * u5.val)
    set Q16 := (v1Fin8DualLeg true nn sp1 (fin8Bin (openCoordDistSq nA eA)) +
      v2Fin8DualLeg true nn sp2 (owB2Of3Port nn nA (if nn then nB else eB) eA) +
      (midWTap29OfMode true nn y36 zLo + zLo) / 16384) % 131072
    have hPh : (fun hi : Fin 16 → ZMod 2 ↦
        owK2Sub62PhaseBit3 (outSubRawBits rW18Sub41_k2 c) true nn sp1 sp2 nA (if nn then nB else eB)
        eA (fullEquiv23 (hi, equivLo7 (u0, u1, u5)))) = (fun hi : Fin 16 → ZMod 2 ↦
        (if (Q16 + ∑ k : Fin 16, (hi k).val * 2 ^ k.val).testBit 16 then (1 : ZMod 2) else 0) +
        (if true then 1 else 0))
        := by
      funext hi; unfold owK2Sub62PhaseBit3; rw [spliced_fullEquiv23_eq_fullEquiv24 c hi u0 u1 u5];
      unfold owK2PhaseBit3; dsimp only;
      rw [z30K2_split14, x13K2_fullEquiv24, zLo14K2_fullEquiv24, fullEquiv24_hi, hwTake,
          testBit30_t31ModTap29_eq_q14]
    have hCongr :=
        congrArg (fun f : (Fin 16 → ZMod 2) → ZMod 2 ↦ (2 ^ 16 : ℝ)⁻¹ * ∑ hi : (Fin 16 → ZMod 2),
        if f hi = 1 then (-1 : ℝ) else 1) hPh
    have hzLoLt : zLo < 16384 := by
      dsimp only [zLo, bit2]; have := (df8Of13 x13).isLt; have := u5.isLt; split_ifs <;> omega
    obtain ⟨hQEq, hQLe⟩ := q16Mod_eq_of_q14_nonWrap hMod (hCap w (o9Of13 x13) hzLoLt);
    have hQZ : (Q16 : ℤ) = 32768 + (((midWTap29OfMode true nn y36 zLo + zLo) / 16384 : ℕ) : ℤ) -
        cSh := hQEq
    have hQR : (Q16 : ℝ) = 32768 + (((midWTap29OfMode true nn y36 zLo + zLo) / 16384 : ℕ) : ℝ) -
        (cSh : ℝ) := by have h := congrArg (Int.cast : ℤ → ℝ) hQZ; push_cast at h; exact h
    rw [hCongr, sum_hi16_phaseBit Q16 hQLe true, hQR]; simp only [↓reduceIte, one_mul]
    norm_num; ring
  simp_rw [hInner]
  have hHerm : (∑ u5 : Fin 32, (midWTap29OfMode true nn y36 ((df8Of13 x13).val + 256 *
      (bit2 + 2 * u5.val)) + ((df8Of13 x13).val + 256 * (bit2 + 2 * u5.val))) / 16384) =
      (fn y36 + (df8Of13 x13).val + (if Bool.xor (vz0BoolOfCoin c)
      (affineBit13 7483 x13) then 256 else 0)) / 512 := by
    simp_rw [hMidW]
    have hAdd : ∀ u5 : Fin 32,
        (df8Of13 x13).val + 256 * (bit2 + 2 * u5.val) =
        ((df8Of13 x13).val + 256 * bit2) + 512 * u5.val := fun _ ↦ by ring
    simp_rw [hAdd]
    have hd9Lt : (df8Of13 x13).val + 256 * bit2 < 512 := by
      have := (df8Of13 x13).isLt; dsimp only [bit2]; split_ifs <;> omega
    rw [hermite_div16384_add_512 (fn y36) _ hd9Lt]
    have hbEq : 256 * bit2 = if Bool.xor (vz0BoolOfCoin c)
        (affineBit13 7483 x13) then 256 else 0 := by dsimp only [bit2]; split_ifs <;> omega
    rw [hbEq, add_assoc]
  exact avg_u5_q14 _ _ hHerm (16384 * (cSh : ℝ))

def vhRQ31 (r11 h2 q31 : ℕ) : Bool :=
  let h := Nat.xor (b6Inv1023 r11 h2 q31) 96
  Bool.xor (h.testBit 0) (h.testBit 5)

def polRH (r11 h2 : ℕ) : Bool := Bool.or (r11.testBit 0) (Nat.ble 8 r11 && Nat.beq h2 2)
def polCell (u1 h2 lo1 lo2 : ℕ) : Bool :=
    Bool.xor (Bool.xor (lo2.testBit 0) (lo1.testBit 0)) (polRH (phiU1Inv u1).1 h2)
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem b6Inv1023_b6Spec_raw : allBelow 1023 (fun a10 ↦
    Nat.beq (b6Inv1023 (b6Spec a10).1 (b6Spec a10).2.1 (b6Spec a10).2.2.1) a10) =
    true := by decide +kernel
theorem b6Inv1023_b6Spec_cert (a10 : Fin 1023) :
    b6Inv1023 (b6Spec a10.val).1 (b6Spec a10.val).2.1 (b6Spec a10.val).2.2.1 = a10.val :=
    Nat.beq_eq.mp ((allBelow_true_iff 1023 _).mp b6Inv1023_b6Spec_raw a10.val a10.isLt)
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem phiU1Inv_fst_phiU1_raw : allBelow 11 (fun r11 ↦ allBelow 17 (fun r17 ↦
    Nat.beq (phiU1Inv (phiU1 r11 r17)).1 r11)) = true := by decide +kernel
theorem phiU1Inv_fst_phiU1_cert (r11 : Fin 11)
    (r17 : Fin 17) : (phiU1Inv (phiU1 r11.val r17.val)).1 = r11.val :=
    Nat.beq_eq.mp ((allBelow_true_iff 17 _).mp ((allBelow_true_iff 11 _).mp phiU1Inv_fst_phiU1_raw
    r11.val r11.isLt) r17.val r17.isLt)
theorem card_decodeTier1W11Opt1424Coin_pot_w11_vz {s : ZeroNEremSector} (hIdle : s ≠ .idle)
    (hKin : ∀ i ax, s ≠ .kin i ax) {w : ℕ} (hw : w < 2048)
    (vz : Bool) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1W11Opt1424Coin c = s ∧ w11NatOfCoin c = w ∧ vz0BoolOfCoin c = vz)).card = ∑ u1 :
    Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ q5 : Fin 5, ∑ q31 : Fin 31, ∑ lo1 : Fin 64, ∑ lo2 :
    Fin 64,
    cond (eqSec (tier1W11IntCell u1.val h1.val h2.val q5.val q31.val lo1.val lo2.val w) s &&
    (Bool.xor (Bool.xor (lo2.val.testBit 0) (lo1.val.testBit 0))
    (vhRQ31 (phiU1Inv u1.val).1 h2.val q31.val) == vz)) 1 0 := by
  let H : Fin (2 ^ 41) → ℕ := fun c ↦
      cond (eqSec (decodeTier1W11Opt1424Coin c) s && ((w11NatOfCoin c == w) &&
      (vz0BoolOfCoin c == vz))) 1 0
  have hlhs : ((Finset.univ : Finset (Fin (2 ^ 41))).filter
      (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧ w11NatOfCoin c = w ∧ vz0BoolOfCoin c =
          vz)).card =
      ∑ c : Fin (2 ^ 41), H c := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    dsimp only [H]
    by_cases hs : decodeTier1W11Opt1424Coin c = s
    · rw [(eqSec_iff _ _).mpr hs, Bool.true_and]
      by_cases hw0 : w11NatOfCoin c = w <;> by_cases hv0 : vz0BoolOfCoin c = vz <;>
          simp [hs, hw0, hv0]
    · rw [Bool.eq_false_iff.mpr fun ht ↦ hs ((eqSec_iff _ _).mp ht), Bool.false_and,
          Bool.cond_false, _root_.ite_eq_right fun h ↦ hs h.1]
  have hNot : (∀ i ax, s ≠ .kin i ax) ∧ s ≠ .idle := ⟨hKin, hIdle⟩
  have hNe0 (sec) (hne : sec ≠ s) : eqSec sec s = false := Bool.eq_false_iff.mpr fun ht ↦
      hne ((eqSec_iff _ _).mp ht)
  let G8 (hi8 : ℕ) : ℕ := ∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
    H (tier1CoinOf5 hi8 lo8.val hi10.val lo10.val c5.val)
  rw [hlhs, tier1_sum_coin41_split5 H, show (256 : ℕ) = 255 + 1 from rfl, sum_fin_add (M := 255)
      (N := 1) G8,
      Fin.sum_univ_one, show G8 (255 + (0 : Fin 1).val) = 0 from
        Finset.sum_eq_zero fun lo8 _ ↦ Finset.sum_eq_zero fun hi10 _ ↦
          Finset.sum_eq_zero fun lo10 _ ↦ Finset.sum_eq_zero fun c5 _ ↦ by
            dsimp only [G8, H, Fin.val_zero, Nat.add_zero]
            rw [hNe0 _ (by
              rw [decodeTier1W11Opt1424Coin_coinOf5 (by norm_num) lo8.isLt hi10.isLt lo10.isLt
                  c5.isLt,
                  show (255 == 255) = true from rfl, Bool.cond_true]
              exact t1b_cond_ne_of_ne (t1b_cond_ne_of_ne (kinNucBlkT1b_fst_ne hNot hi10.val)
                  (fun h ↦ hIdle h.symm))
                (t1b_cond_ne_of_ne (fun h ↦ hIdle h.symm) (fun h ↦ hKin _ _ h.symm)))]
            rfl, Nat.add_zero]
  have ha8Step (a8 : Fin 255) : G8 a8.val =
      ∑ a10 : Fin 1023, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
        cond (eqSec (tier1W11IntCell (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)
          (b2Spec a8.val).2.1 (b6Spec a10.val).2.1 (b2Spec a8.val).2.2.1 (b6Spec a10.val).2.2.1
              lo1.val lo2.val w) s &&
          (Bool.xor (Bool.xor (lo2.val.testBit 0) (lo1.val.testBit 0))
            (vhRQ31 (phiU1Inv (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)).1
              (b6Spec a10.val).2.1 (b6Spec a10.val).2.2.1) == vz)) 1 0 := by
    dsimp only [G8]
    have ha8Lt256 : a8.val < 256 := Nat.lt_trans a8.isLt (by norm_num)
    have hne8 : (a8.val == 255) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_lt a8.isLt)
    have hb2p := b2Spec_lt255 a8.isLt
    let G10 (h : ℕ) : ℕ := ∑ lo8 : Fin 256, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
      cond (eqSec (cond (b6Spec h).2.2.2 .idle (tier1W11IntCell
        (phiU1 (b6Spec h).1 (b2Spec a8.val).1) (b2Spec a8.val).2.1 (b6Spec h).2.1
        (b2Spec a8.val).2.2.1 (b6Spec h).2.2.1 (lo8.val % 64) (lo10.val % 64)
        (c5.val + 32 * (lo10.val / 64) + 512 * (lo8.val / 64)))) s &&
        (((c5.val + 32 * (lo10.val / 64) + 512 * (lo8.val / 64)) == w) &&
          (Bool.xor (Bool.xor ((lo10.val % 64).testBit 0) ((lo8.val % 64).testBit 0))
            (Bool.xor ((Nat.xor h 96).testBit 0) ((Nat.xor h 96).testBit 5)) == vz))) 1 0
    have hXorH : (∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
        H (tier1CoinOf5 a8.val lo8.val hi10.val lo10.val c5.val)) = ∑ hi10 : Fin 1024,
            G10 hi10.val := by
      rw [Finset.sum_comm, ← sum_hi10_xor96 G10]
      refine Finset.sum_congr rfl fun hi10 _ ↦ Finset.sum_congr rfl fun lo8 _ ↦
        Finset.sum_congr rfl fun lo10 _ ↦ Finset.sum_congr rfl fun c5 _ ↦ ?_
      have htb := testBit_coinOf5_5_15_20_25 ha8Lt256 lo8.isLt hi10.isLt lo10.isLt c5.isLt
      dsimp only [H]
      rw [decodeTier1W11Opt1424Coin_coinOf5 ha8Lt256 lo8.isLt hi10.isLt lo10.isLt c5.isLt,
          w11NatOfCoin_tier1CoinOf5 ha8Lt256 lo8.isLt hi10.isLt lo10.isLt c5.isLt]
      unfold vz0BoolOfCoin
      rw [htb.1, htb.2.1, htb.2.2.1, htb.2.2.2.1, (xor1024_96_props hi10.isLt).2]
      simp only [hne8, hb2p.2.2.2.1, Bool.cond_false]
    rw [hXorH, show (1024 : ℕ) = 1023 + 1 from rfl, sum_fin_add (M := 1023)
        (N := 1) G10, Fin.sum_univ_one,
        show G10 (1023 + (0 : Fin 1).val) = 0 from Finset.sum_eq_zero fun _ _ ↦
            Finset.sum_eq_zero fun _ _ ↦
          Finset.sum_eq_zero fun _ _ ↦ by
            dsimp only [G10, Fin.val_zero, Nat.add_zero]
            rw [b6Spec_1023, Bool.cond_true, hNe0 .idle (fun h ↦ hIdle h.symm)]
            rfl, Nat.add_zero]
    refine Finset.sum_congr rfl fun a10 _ ↦ ?_
    dsimp only [G10]
    have hb6p := b6Spec_lt1023 a10.isLt
    simp only [hb6p.2.2.2.1, Bool.cond_false]
    have hp1 := phiU1Inv_fst_phiU1_cert ⟨(b6Spec a10.val).1, hb6p.1⟩ ⟨(b2Spec a8.val).1, hb2p.1⟩
    have hb6i := b6Inv1023_b6Spec_cert a10
    dsimp only at hp1 hb6i
    rw [show Bool.xor ((Nat.xor a10.val 96).testBit 0) ((Nat.xor a10.val 96).testBit 5) =
          vhRQ31 (phiU1Inv (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)).1
            (b6Spec a10.val).2.1 (b6Spec a10.val).2.2.1 by unfold vhRQ31; rw [hp1, hb6i],
        tier1_sum_lo8_lo10_c5_w11 (fun lo1 lo2 w11 ↦
          cond (eqSec (tier1W11IntCell (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)
            (b2Spec a8.val).2.1 (b6Spec a10.val).2.1 (b2Spec a8.val).2.2.1
            (b6Spec a10.val).2.2.1 lo1 lo2 w11) s &&
            ((w11 == w) && (Bool.xor (Bool.xor (lo2.testBit 0) (lo1.testBit 0))
              (vhRQ31 (phiU1Inv (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1)).1
                (b6Spec a10.val).2.1 (b6Spec a10.val).2.2.1) == vz))) 1 0)]
    refine Finset.sum_congr rfl fun lo1 _ ↦ Finset.sum_congr rfl fun lo2 _ ↦ ?_
    rw [Finset.sum_eq_single ⟨w, hw⟩ (fun u _ hne ↦ by
        rw [beq_eq_false_iff_ne.mpr fun hv ↦ hne (Fin.ext hv), Bool.false_and, Bool.and_false]
        rfl) (fun h ↦ absurd (Finset.mem_univ _) h)]
    dsimp only
    rw [beq_self_eq_true, Bool.true_and]
  rw [Finset.sum_congr rfl fun a8 _ ↦ ha8Step a8]
  exact sum_a8_a10_cart254 (fun u1 h1 h2 q5 q31 ↦ ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
      cond (eqSec (tier1W11IntCell u1 h1 h2 q5 q31 lo1.val lo2.val w) s &&
      (Bool.xor (Bool.xor (lo2.val.testBit 0) (lo1.val.testBit 0))
      (vhRQ31 (phiU1Inv u1).1 h2 q31) == vz)) 1 0)

def wgtEEPol (pol : Bool) (w : ℕ) (vz : Bool) : ℕ :=
    if w < 1452 then 41 else if vz == pol then 40 else 41
def wgtNNPol (pol : Bool) (w : ℕ) (vz : Bool) : ℕ :=
    if w < 1750 then (if vz == pol then 20 else 21) else 20
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem phiU1Inv_fst_lt11_raw : allBelow 187 (fun u1 ↦ Nat.blt (phiU1Inv u1).1 11) = true := by
  decide +kernel
theorem phiU1Inv_fst_lt11_cert (u1 : Fin 187) : (phiU1Inv u1.val).1 < 11 :=
    Nat.blt_eq.mp ((allBelow_true_iff 187 _).mp phiU1Inv_fst_lt11_raw u1.val u1.isLt)
def tileEeCell (r11 h2 : ℕ) (bit01 vz bLt : Bool) (q5 q31 : ℕ) : ℕ :=
  cond (((Nat.beq (tier1WalkSym96TileKind q5 q31) 0) ||
         (Nat.beq (tier1WalkSym96TileKind q5 q31) 1 && bLt)) &&
        (Bool.xor bit01 (vhRQ31 r11 h2 q31) == vz)) 1 0

def tileNnCell (r11 h2 : ℕ) (bit01 vz bLt : Bool) (q5 q31 : ℕ) : ℕ :=
  cond (((Nat.beq (tier1WalkSym96TileKind q5 q31) 2) ||
         (Nat.beq (tier1WalkSym96TileKind q5 q31) 3 && bLt)) &&
        (Bool.xor bit01 (vhRQ31 r11 h2 q31) == vz)) 1 0

def tilePolBody (r11 h2 : ℕ) (bit01 vz bLt : Bool) : Bool :=
    Nat.beq (sumBelow (fun q5 ↦ sumBelow (fun q31 ↦ tileEeCell r11 h2 bit01 vz bLt q5 q31) 31) 5)
    (if bLt then 41 else if vz == Bool.xor bit01 (polRH r11 h2) then 40 else 41) &&
    Nat.beq (sumBelow (fun q5 ↦ sumBelow (fun q31 ↦ tileNnCell r11 h2 bit01 vz bLt q5 q31) 31) 5)
    (if bLt then (if vz == Bool.xor bit01 (polRH r11 h2) then 20 else 21) else 20)
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tilePol_sum_raw : allBelow 11 (fun r11 ↦ allBelow 3 (fun h2 ↦ allBelow 2 (fun i01 ↦
    allBelow 2 (fun ivz ↦ allBelow 2 (fun ibLt ↦ tilePolBody r11 h2 (Nat.beq i01 1) (Nat.beq ivz 1)
    (Nat.beq ibLt 1)))))) = true := by decide +kernel
theorem tilePol_sum_cert (r11 : Fin 11) (h2 : Fin 3) (bit01 vz bLt : Bool) :
    let pol := Bool.xor bit01 (polRH r11.val h2.val)
    (∑ q5 : Fin 5, ∑ q31 : Fin 31,
      cond (((Nat.beq (tier1WalkSym96TileKind q5.val q31.val) 0) ||
             (Nat.beq (tier1WalkSym96TileKind q5.val q31.val) 1 && bLt)) &&
            (Bool.xor bit01 (vhRQ31 r11.val h2.val q31.val) == vz)) 1 0) =
      (if bLt then 41 else if vz == pol then 40 else 41) ∧
    (∑ q5 : Fin 5, ∑ q31 : Fin 31,
      cond (((Nat.beq (tier1WalkSym96TileKind q5.val q31.val) 2) ||
             (Nat.beq (tier1WalkSym96TileKind q5.val q31.val) 3 && bLt)) &&
            (Bool.xor bit01 (vhRQ31 r11.val h2.val q31.val) == vz)) 1 0) =
      (if bLt then (if vz == pol then 20 else 21) else 20) := by
  let bIdx (b : Bool) : ℕ := cond b 1 0
  have hLt (b : Bool) : bIdx b < 2 := by cases b <;> decide
  have hBeq (b : Bool) : Nat.beq (bIdx b) 1 = b := by cases b <;> rfl
  have hRaw := (allBelow_true_iff 2 _).mp ((allBelow_true_iff 2 _).mp ((allBelow_true_iff 2 _).mp
    ((allBelow_true_iff 3 _).mp ((allBelow_true_iff 11 _).mp tilePol_sum_raw r11.val r11.isLt)
        h2.val h2.isLt)
    (bIdx bit01) (hLt bit01)) (bIdx vz) (hLt vz)) (bIdx bLt) (hLt bLt)
  change tilePolBody r11.val h2.val (Nat.beq (bIdx bit01) 1) (Nat.beq (bIdx vz) 1)
      (Nat.beq (bIdx bLt) 1) = true at hRaw
  rw [hBeq bit01, hBeq vz, hBeq bLt] at hRaw
  unfold tilePolBody at hRaw
  rw [Bool.and_eq_true] at hRaw
  exact ⟨(sum_fin2_eq_sumBelow 5 31 (tileEeCell r11.val h2.val bit01 vz bLt)).trans (Nat.beq_eq.mp
      hRaw.1),
         (sum_fin2_eq_sumBelow 5 31 (tileNnCell r11.val h2.val bit01 vz bLt)).trans (Nat.beq_eq.mp
             hRaw.2)⟩

def kPolEE (n1 : Fin 47) (e1 e2 : Fin 187) (pol : Bool) : ℕ :=
  ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
    cond (eqSec (tier1EeTag u1.val h1.val h2.val lo1.val lo2.val) (.ee n1 e1 e2) &&
      (polCell u1.val h2.val lo1.val lo2.val == pol)) 1 0
def kPolNN (n1 n2 : Fin 47) (e1 : Fin 187) (pol : Bool) : ℕ :=
  ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
    cond (eqSec (tier1NnTag u1.val h1.val h2.val lo1.val lo2.val) (.nn n1 n2 e1) &&
      (polCell u1.val h2.val lo1.val lo2.val == pol)) 1 0

theorem eqSec_byKind_pot (isNN : Bool) (s : ZeroNEremSector) (hId : s ≠ .idle)
    (hKin : ∀ i ax, s ≠ .kin i ax) (hEn : ∀ n1 e1, s ≠ .en n1 e1)
    (hOth : ∀ u1 h1 h2 lo1 lo2,
      (if isNN then tier1EeTag u1 h1 h2 lo1 lo2 else tier1NnTag u1 h1 h2 lo1 lo2) ≠ s)
    (k u1 h1 h2 lo1 lo2 w : ℕ) (hk : k < 8) :
    eqSec (tier1W11ByKind k u1 h1 h2 lo1 lo2 w) s =
      (eqSec (if isNN then tier1NnTag u1 h1 h2 lo1 lo2 else tier1EeTag u1 h1 h2 lo1 lo2) s &&
       (Nat.beq k (if isNN then 2 else 0) ||
        (Nat.beq k (if isNN then 3 else 1) && Nat.blt w (if isNN then 1750 else 1452)))) := by
  have hNe0 (sec) (hne : sec ≠ s) : eqSec sec s = false :=
    Bool.eq_false_iff.mpr fun ht ↦ hne ((eqSec_iff _ _).mp ht)
  have hFbNe (ax) : tier1FbKin u1 ax ≠ s := fun h ↦ hKin _ _ h.symm
  have hFb (ax) : eqSec (tier1FbKin u1 ax) s = false := hNe0 _ (hFbNe ax)
  have hEnF : eqSec (tier1EnTag u1 h1 lo1) s = false :=
    hNe0 _ (t1b_cond_ne_of_ne (fun h ↦ hEn _ _ h.symm) (hFbNe _))
  have hIdF : eqSec .idle s = false := hNe0 _ hId.symm
  have hOthF := hNe0 _ (hOth u1 h1 h2 lo1 lo2)
  have hSel (b : Bool) (h : (Nat.beq k (if isNN then 2 else 0) ||
      (Nat.beq k (if isNN then 3 else 1) && Nat.blt w (if isNN then 1750 else 1452))) = b) :
      (eqSec (if isNN then tier1NnTag u1 h1 h2 lo1 lo2 else tier1EeTag u1 h1 h2 lo1 lo2) s &&
       (Nat.beq k (if isNN then 2 else 0) ||
        (Nat.beq k (if isNN then 3 else 1) && Nat.blt w (if isNN then 1750 else 1452)))) =
      (eqSec (if isNN then tier1NnTag u1 h1 h2 lo1 lo2 else tier1EeTag u1 h1 h2 lo1 lo2) s && b)
          := by rw [h]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hSel (!isNN) (by cases isNN <;> rfl)]
    cases isNN <;> (simp only [Bool.false_eq_true, ↓reduceIte] at hOthF; simp [tier1W11ByKind,
        hOthF])
  · rw [hSel (!isNN && Nat.blt w 1452) (by cases isNN <;> rfl)]
    simp only [tier1W11ByKind]
    cases isNN <;> (simp only [Bool.false_eq_true, ↓reduceIte] at hOthF; cases Nat.blt w 1452 <;>
        simp [hFb, hOthF])
  · rw [hSel isNN (by cases isNN <;> rfl)]
    cases isNN <;> (simp only [Bool.false_eq_true, ↓reduceIte] at hOthF; simp [tier1W11ByKind,
        hOthF])
  · rw [hSel (isNN && Nat.blt w 1750) (by cases isNN <;> rfl)]
    simp only [tier1W11ByKind]
    cases isNN <;> (simp only [Bool.false_eq_true, ↓reduceIte] at hOthF; cases Nat.blt w 1750 <;>
        simp [hFb, hOthF])
  · rw [hSel false (by cases isNN <;> rfl), Bool.and_false, tier1W11ByKind, hEnF]
  · rw [hSel false (by cases isNN <;> rfl), Bool.and_false]
    simp only [tier1W11ByKind]
    cases Bool.or (Bool.not (g66VOpt h2 lo2)) (Nat.blt w 401) <;> simp [hEnF, hFb]
  · rw [hSel false (by cases isNN <;> rfl), Bool.and_false]
    simp only [tier1W11ByKind]
    cases Nat.beq h1 0 <;> dsimp only [cond]
    · cases Nat.beq h1 1 && _ <;> dsimp only [cond]
      · cases Nat.beq h1 2 && _ <;> simp [hFb]
      · simp [hFb]
    · cases Nat.blt w _ <;> simp [hIdF, hFb]
  · rw [hSel false (by cases isNN <;> rfl), Bool.and_false]
    simp [tier1W11ByKind, hFb]

theorem fib_pot_vz_eq (isNN : Bool) (s : ZeroNEremSector) (hIdle : s ≠ .idle)
    (hKin : ∀ i ax, s ≠ .kin i ax) (hEn : ∀ n1 e1, s ≠ .en n1 e1)
    (hOth : ∀ u1 h1 h2 lo1 lo2,
      (if isNN then tier1EeTag u1 h1 h2 lo1 lo2 else tier1NnTag u1 h1 h2 lo1 lo2) ≠ s)
    {w : ℕ} (hw : w < 2048) (vz : Bool) :
    let tag := if isNN then tier1NnTag else tier1EeTag
    let wgt := if isNN then wgtNNPol else wgtEEPol
    let kPol (pol : Bool) : ℕ :=
      ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
        cond (eqSec (tag u1.val h1.val h2.val lo1.val lo2.val) s &&
          (polCell u1.val h2.val lo1.val lo2.val == pol)) 1 0
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter
      (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧ w11NatOfCoin c = w ∧
        vz0BoolOfCoin c = vz)).card =
      kPol false * wgt false w vz + kPol true * wgt true w vz := by
  dsimp only
  rw [card_decodeTier1W11Opt1424Coin_pot_w11_vz hIdle hKin hw vz]
  simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
  have hComm (f : Fin 5 → Fin 31 → Fin 64 → Fin 64 → ℕ) :
      (∑ q5, ∑ q31, ∑ lo1, ∑ lo2, f q5 q31 lo1 lo2) = ∑ lo1, ∑ lo2, ∑ q5, ∑ q31,
          f q5 q31 lo1 lo2 := by
    trans ∑ q5, ∑ lo1, ∑ lo2, ∑ q31, f q5 q31 lo1 lo2
    · refine Finset.sum_congr rfl fun q5 _ ↦ ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  refine Finset.sum_congr rfl fun u1 _ ↦ Finset.sum_congr rfl fun h1 _ ↦
      Finset.sum_congr rfl fun h2 _ ↦ ?_
  rw [hComm]
  refine Finset.sum_congr rfl fun lo1 _ ↦ Finset.sum_congr rfl fun lo2 _ ↦ ?_
  simp_rw [tier1W11IntCell_eq_byKind,
    eqSec_byKind_pot isNN s hIdle hKin hEn hOth _ _ _ _ _ _ _ (tier1WalkSym96TileKind_lt8 _
        _),
    show (if isNN then tier1NnTag u1.val h1.val h2.val lo1.val lo2.val
      else tier1EeTag u1.val h1.val h2.val lo1.val lo2.val) =
      (if isNN then tier1NnTag else tier1EeTag) u1.val h1.val h2.val lo1.val lo2.val
          by cases isNN <;> rfl]
  cases eqSec ((if isNN then tier1NnTag else tier1EeTag) u1.val h1.val h2.val lo1.val lo2.val) s
  · simp
  · simp only [Bool.true_and]
    set pc := polCell u1.val h2.val lo1.val lo2.val
    let tp := tilePol_sum_cert ⟨(phiU1Inv u1.val).1, phiU1Inv_fst_lt11_cert u1⟩ h2
      (Bool.xor (lo2.val.testBit 0) (lo1.val.testBit 0)) vz
    cases isNN
    · have hTP := (tp (Nat.blt w 1452)).1
      dsimp only [tp] at hTP
      simp only [Bool.false_eq_true, ↓reduceIte, hTP]
      change (if Nat.blt w 1452 then 41 else if vz == pc then 40 else 41) = _
      unfold wgtEEPol
      by_cases hlt : w < 1452 <;> cases pc <;> simp [hlt, Nat.blt_eq]
    · have hTP := (tp (Nat.blt w 1750)).2
      dsimp only [tp] at hTP
      simp only [↓reduceIte, hTP]
      change (if Nat.blt w 1750 then (if vz == pc then 20 else 21) else 20) = _
      unfold wgtNNPol
      by_cases hlt : w < 1750 <;> cases pc <;> simp [hlt, Nat.blt_eq]
theorem fib_ee_vz_eq (n1 : Fin 47) (e1 e2 : Fin 187) {w : ℕ} (hw : w < 2048) (vz : Bool) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter
      (fun c ↦ decodeTier1W11Opt1424Coin c = .ee n1 e1 e2 ∧ w11NatOfCoin c = w ∧
          vz0BoolOfCoin c = vz)).card =
      kPolEE n1 e1 e2 false * wgtEEPol false w vz + kPolEE n1 e1 e2 true * wgtEEPol true w vz :=
  fib_pot_vz_eq false (.ee n1 e1 e2) ZeroNEremSector.noConfusion (fun _ _ ↦
      ZeroNEremSector.noConfusion) (fun _ _ ↦ ZeroNEremSector.noConfusion)
    (fun _ _ _ _ _ ↦
        t1b_cond_ne_of_ne ZeroNEremSector.noConfusion
        (by unfold tier1FbKin; exact ZeroNEremSector.noConfusion)) hw vz

theorem fib_nn_vz_eq (n1 n2 : Fin 47) (e1 : Fin 187) {w : ℕ} (hw : w < 2048) (vz : Bool) :
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter
      (fun c ↦ decodeTier1W11Opt1424Coin c = .nn n1 n2 e1 ∧ w11NatOfCoin c = w ∧
          vz0BoolOfCoin c = vz)).card =
      kPolNN n1 n2 e1 false * wgtNNPol false w vz + kPolNN n1 n2 e1 true * wgtNNPol true w vz :=
  fib_pot_vz_eq true (.nn n1 n2 e1) ZeroNEremSector.noConfusion (fun _ _ ↦
      ZeroNEremSector.noConfusion) (fun _ _ ↦ ZeroNEremSector.noConfusion)
    (fun _ _ _ _ _ ↦
        t1b_cond_ne_of_ne ZeroNEremSector.noConfusion
        (by unfold tier1FbKin; exact ZeroNEremSector.noConfusion)) hw vz

theorem card_vz_pair_sum (s : ZeroNEremSector)
    (w : ℕ) : ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦
    decodeTier1W11Opt1424Coin c = s ∧ w11NatOfCoin c = w ∧ vz0BoolOfCoin c = false)).card +
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧
    w11NatOfCoin c = w ∧ vz0BoolOfCoin c = true)).card =
    ((Finset.univ : Finset (Fin (2 ^ 41))).filter (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧
    w11NatOfCoin c = w)).card := by
  rw [← Finset.card_union_of_disjoint]
  · refine congrArg Finset.card (Finset.ext fun c ↦ ?_)
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases vz0BoolOfCoin c <;> simp
  · rw [Finset.disjoint_filter]; intro c _ h1 h2; exact Bool.noConfusion (h1.2.2.symm.trans h2.2.2)
theorem kPolEE_sum (n1 : Fin 47) {e1 e2 : Fin 187} (hlt : e1 < e2) : kPolEE n1 e1 e2 false +
    kPolEE n1 e1 e2 true = 2 * mSpCart254 (nucSpecies n1) := by
  have hp := card_vz_pair_sum (.ee n1 e1 e2) 0
  rw [fib_ee_vz_eq n1 e1 e2 (by omega) false,
      fib_ee_vz_eq n1 e1 e2 (by omega) true,
      fib_ee_t1b_w11Nat_eq_cntEE2048 n1 e1 e2 (by omega)] at hp
  simp only [hlt, ↓reduceIte, wgtEEPol, show (0 : ℕ) < 1452 by omega, cntEE2048Tier1Walk] at hp
  omega

theorem kPolNN_sum {n1 n2 : Fin 47} (hlt : n1 < n2) (e1 : Fin 187) : kPolNN n1 n2 e1 false +
    kPolNN n1 n2 e1 true = 2 * (mSpCart254 (nucSpecies n1) * mSpCart254 (nucSpecies n2)) := by
  have hp := card_vz_pair_sum (.nn n1 n2 e1) 1750;
  have hnot33 := nucSpecies_not_3_3_of_lt_wstate hlt
  rw [fib_nn_vz_eq n1 n2 e1 (by omega) false,
      fib_nn_vz_eq n1 n2 e1 (by omega) true,
      fib_nn_t1b_w11Nat_eq_cntNN2048 n1 n2 e1 (by omega)] at hp
  simp only [hlt, ↓reduceIte, wgtNNPol, show ¬((1750 : ℕ) < 1750) by omega,
    cntNN2048Tier1Walk, hnot33] at hp
  omega

def termSub62PolNat (isNN pol : Bool) (w : ℕ) (bw : Bool) (Z : ℕ) : ℕ :=
    if isNN then 80 * (Z / 256) + (if w < 1750 ∧ !bw then 4 else 0) *
    ((Z + (if pol then 0 else 256)) / 512) + (if w < 1750 ∧ bw then 4 else 0) *
    ((Z + (if pol then 256 else 0)) / 512) else (if w < 1452 then 82 else 80) * (Z / 256) +
    (if 1452 ≤ w ∧ !bw then 2 else 0) * ((Z + (if pol then 0 else 256)) / 512) +
    (if 1452 ≤ w ∧ bw then 2 else 0) * ((Z + (if pol then 256 else 0)) / 512)
def eSub62PolNat (isNN pol : Bool) (d2 : ℕ) : ℕ :=
  ∑ w : Fin 2048, ∑ u0 : Fin 2, ∑ u1 : Fin 2,
    let x13 := x13OfW11U01 w u0 u1
    let fn := if isNN then fnNN30 else fnEE30
    let Z := fn (ySampleK2 word512DualLegLo6 isNN d2 w (o9Of13 x13)) + (df8Of13 x13).val
    termSub62PolNat isNN pol w.val (affineBit13 7483 x13) Z

noncomputable def expFnSub62Pol (isNN pol : Bool) (d2 : ℕ) : ℝ :=
    ((64 : ℝ) / 167340) * (eSub62PolNat isNN pol d2 : ℝ)
noncomputable def vEESub62Pol (pol : Bool) (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47)
    (e1 e2 : Fin 187) : ℝ :=
    (expFnSub62Pol false pol (pairOpenDistSq x (elecP e1) (elecP e2)) -
    (cEE1Fin8DualLeg (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) : ℝ) -
    (cEE2Fin8DualLeg (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e2))) : ℝ)) / (2 ^ 29 : ℝ)
noncomputable def vNNSub62Pol (pol : Bool) (x : Fin (2 ^ systemQubits_frozen)) (n1 n2 : Fin 47)
    (e1 : Fin 187) : ℝ :=
    (expFnSub62Pol true pol (pairOpenDistSq x (nucP n1) (nucP n2)) -
    (cNNFin8DualLeg (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) : ℝ) -
    (cNNFin8DualLeg (fin8Bin (pairOpenDistSq x (nucP n2) (elecP e1))) : ℝ)) / (2 ^ 29 : ℝ)
theorem sum_wgtPol_certs :
    (∀ pol : Bool, (∑ w : Fin 2048, (wgtEEPol pol w.val false + wgtEEPol pol w.val true)) =
      167340) ∧
    (∀ pol : Bool, (∑ w : Fin 2048, (wgtNNPol pol w.val false + wgtNNPol pol w.val true)) =
      83670) := by
  have hStep (cut rest a b : ℕ) (hc : 2048 = cut + rest) :
      (∑ w : Fin 2048, if w.val < cut then a else b) = cut * a + rest * b := by
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ if k < cut then a else b) 2048, hc,
        Finset.sum_range_add, Finset.sum_congr rfl (fun i hi ↦
            _root_.ite_eq_left (Finset.mem_range.mp hi)),
        Finset.sum_congr rfl (fun i _ ↦ _root_.ite_eq_right (by omega : ¬(cut + i < cut))),
        Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range]
    rfl
  refine ⟨fun pol ↦ ?_, fun pol ↦ ?_⟩
  · rw [Finset.sum_congr rfl (fun w _ ↦ show wgtEEPol pol w.val false + wgtEEPol pol w.val true =
      if w.val < 1452 then 82 else 81 by unfold wgtEEPol; cases pol <;>
        by_cases hw : w.val < 1452 <;> simp [hw]), hStep 1452 596 82 81 rfl]
  · rw [Finset.sum_congr rfl (fun w _ ↦ show wgtNNPol pol w.val false + wgtNNPol pol w.val true =
      if w.val < 1750 then 41 else 40 by unfold wgtNNPol; cases pol <;>
        by_cases hw : w.val < 1750 <;> simp [hw]), hStep 1750 298 41 40 rfl]

theorem termSub62PolNat_eq (isNN pol : Bool) (w : ℕ) (bw : Bool) (Z : ℕ) :
    (if isNN then 4 else 2) *
      ((if isNN then wgtNNPol else wgtEEPol) pol w false *
        ((Z + (if Bool.xor false bw then 256 else 0)) / 512) +
       (if isNN then wgtNNPol else wgtEEPol) pol w true *
        ((Z + (if Bool.xor true bw then 256 else 0)) / 512)) =
      termSub62PolNat isNN pol w bw Z := by
  have hd : Z / 512 + (Z + 256) / 512 = Z / 256 := by omega
  unfold wgtEEPol wgtNNPol termSub62PolNat
  by_cases h1 : w < 1452 <;> by_cases h2 : w < 1750 <;>
    cases isNN <;> cases pol <;> cases bw <;>
    simp [h1, h2, show (1452 ≤ w) ↔ ¬(w < 1452) by omega] <;> omega

theorem sum_coin41_by_w11_vz (s : ZeroNEremSector) (G : Fin 2048 → Bool → ℝ)
    (F : Fin (2 ^ 41) → ℝ)
    (hFG : ∀ c : Fin (2 ^ 41), decodeTier1W11Opt1424Coin c = s →
      F c = G ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩ (vz0BoolOfCoin c)) :
    (∑ c : Fin (2 ^ 41), if decodeTier1W11Opt1424Coin c = s then F c else 0) =
      ∑ w : Fin 2048,
        (((((Finset.univ : Finset (Fin (2 ^ 41))).filter
          (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧ w11NatOfCoin c = w.val ∧
            vz0BoolOfCoin c = false)).card : ℝ) * G w false) +
         ((((Finset.univ : Finset (Fin (2 ^ 41))).filter
          (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧ w11NatOfCoin c = w.val ∧
            vz0BoolOfCoin c = true)).card : ℝ) * G w true)) := by
  let g : Fin (2 ^ 41) → Fin 2048 × Bool := fun c ↦
      (⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩, vz0BoolOfCoin c)
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _),
      Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [show ∀ H : Bool → ℝ, (∑ vz : Bool, H vz) = H false + H true from fun H ↦
      by simp [Fintype.univ_bool, add_comm]]
  have hVz (vz : Bool) : (∑ x ∈ Finset.univ.filter (fun c ↦ g c = (w, vz)),
      if decodeTier1W11Opt1424Coin x = s then F x else 0) =
      (((Finset.univ.filter (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧
        w11NatOfCoin c = w.val ∧ vz0BoolOfCoin c = vz)).card : ℝ) * G w vz) := by
    have hIn : ∀ c ∈ Finset.univ.filter (fun c ↦ g c = (w, vz)),
        (if decodeTier1W11Opt1424Coin c = s then F c else 0) =
        (if decodeTier1W11Opt1424Coin c = s then G w vz else 0) := fun c hc ↦ by
      have hgc : g c = (w, vz) := (Finset.mem_filter.mp hc).2
      by_cases hs : decodeTier1W11Opt1424Coin c = s
      · rw [_root_.ite_eq_left hs, _root_.ite_eq_left hs, hFG c hs, (Prod.mk.inj hgc).1,
            (Prod.mk.inj hgc).2]
      · rw [_root_.ite_eq_right hs, _root_.ite_eq_right hs]
    rw [Finset.sum_congr rfl hIn, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        Finset.filter_filter]
    refine congrArg (· * G w vz)
        (congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun c _ ↦ ?_)))
    dsimp only [g]
    rw [Prod.mk.injEq, Fin.ext_iff]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ ↦ ⟨⟨h1, h2⟩, h3⟩⟩
  rw [hVz false, hVz true]

theorem vPotSub62_convex_pol (isNN : Bool) (s : ZeroNEremSector) (kPol : Bool → ℕ) (W C1 C2 : ℝ)
    (d2 : ℕ) (F : Fin (2 ^ 41) → ℝ)
    (hFib : ∀ {w : ℕ}, w < 2048 → ∀ vz,
      ((Finset.univ : Finset (Fin (2 ^ 41))).filter
        (fun c ↦ decodeTier1W11Opt1424Coin c = s ∧ w11NatOfCoin c = w ∧
          vz0BoolOfCoin c = vz)).card =
        kPol false * (if isNN then wgtNNPol else wgtEEPol) false w vz +
        kPol true * (if isNN then wgtNNPol else wgtEEPol) true w vz)
    (hwFac : W = ((kPol false : ℝ) + (kPol true : ℝ)) * (if isNN then 83670 else 167340))
    (hkPos : 0 < kPol false + kPol true)
    (hPt : ∀ c : Fin (2 ^ 41), decodeTier1W11Opt1424Coin c = s →
      F c = (4 : ℝ)⁻¹ * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
        ((512 * (((((if isNN then fnNN30 else fnEE30)
            (ySampleK2 word512DualLegLo6 isNN d2 ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩
              (o9Of13 (x13OfW11U01 ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩ u0 u1))) +
          (df8Of13 (x13OfW11U01 ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩ u0 u1)).val) +
          (if Bool.xor (vz0BoolOfCoin c) (affineBit13 7483
            (x13OfW11U01 ⟨w11NatOfCoin c, w11NatOfCoin_lt2048 c⟩ u0 u1)) then 256 else 0)) /
            512 : ℕ) : ℝ) - (C1 + C2)) / (2 ^ 29 : ℝ))) :
    ((kPol false : ℝ) + (kPol true : ℝ)) *
        (W⁻¹ * ∑ c : Fin (2 ^ 41), if decodeTier1W11Opt1424Coin c = s then F c else 0) =
      (kPol false : ℝ) * ((expFnSub62Pol isNN false d2 - C1 - C2) / (2 ^ 29 : ℝ)) +
      (kPol true : ℝ) * ((expFnSub62Pol isNN true d2 - C1 - C2) / (2 ^ 29 : ℝ)) := by
  let Z (w : Fin 2048) (u0 u1 : Fin 2) : ℕ :=
    (if isNN then fnNN30 else fnEE30)
        (ySampleK2 word512DualLegLo6 isNN d2 w (o9Of13 (x13OfW11U01 w u0 u1))) +
      (df8Of13 (x13OfW11U01 w u0 u1)).val
  let G (w : Fin 2048) (vz : Bool) : ℝ := (4 : ℝ)⁻¹ * ∑ u0 : Fin 2, ∑ u1 : Fin 2,
    ((512 *
        (((Z w u0 u1 + (if Bool.xor vz (affineBit13 7483 (x13OfW11U01 w u0 u1)) then 256 else 0)) /
        512 : ℕ) : ℝ) -
      (C1 + C2)) / (2 ^ 29 : ℝ))
  let wgt := if isNN then wgtNNPol else wgtEEPol
  rw [sum_coin41_by_w11_vz s G F hPt, Finset.sum_congr rfl (fun w _ ↦ show _ =
      (kPol false : ℝ) * ((wgt false w.val false : ℝ) * G w false + (wgt false w.val true : ℝ) *
          G w true) +
      (kPol true : ℝ) * ((wgt true w.val false : ℝ) * G w false + (wgt true w.val true : ℝ) *
          G w true) by
    rw [hFib w.isLt false, hFib w.isLt true]
    dsimp only [wgt]
    push_cast
    ring), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hPol (pol : Bool) :
      (∑ w : Fin 2048, ((wgt pol w.val false : ℝ) * G w false + (wgt pol w.val true : ℝ) *
          G w true)) =
        (if isNN then (83670 : ℝ) else 167340) * ((expFnSub62Pol isNN pol d2 - C1 - C2) /
            (2 ^ 29 : ℝ)) := by
    let cNum : ℝ := if isNN then 32 else 64
    rw [Finset.sum_congr rfl (fun w _ ↦ show ((wgt pol w.val false : ℝ) * G w false +
        (wgt pol w.val true : ℝ) * G w true) =
        (cNum / (2 ^ 29 : ℝ)) * (∑ u0 : Fin 2, ∑ u1 : Fin 2,
          (termSub62PolNat isNN pol w.val (affineBit13 7483 (x13OfW11U01 w u0 u1))
              (Z w u0 u1) : ℝ)) -
        (((C1 + C2) / (2 ^ 29 : ℝ)) * ((wgt pol w.val false + wgt pol w.val true : ℕ) : ℝ)) by
      have ht (u0 u1 : Fin 2) := congrArg (Nat.cast (R := ℝ))
        (termSub62PolNat_eq isNN pol w.val (affineBit13 7483 (x13OfW11U01 w u0 u1))
            (Z w u0 u1)).symm
      dsimp only [G, wgt, cNum]
      simp_rw [ht]
      cases isNN <;> simp only [Fin.sum_univ_two, Bool.false_eq_true, ↓reduceIte] <;> push_cast <;>
          ring),
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      show (∑ w : Fin 2048, ∑ u0 : Fin 2, ∑ u1 : Fin 2,
        (termSub62PolNat isNN pol w.val (affineBit13 7483 (x13OfW11U01 w u0 u1)) (Z w u0 u1) : ℝ)) =
          (eSub62PolNat isNN pol d2 : ℝ) by unfold eSub62PolNat; push_cast; rfl]
    cases isNN <;>
      simp only [wgt, cNum, Bool.false_eq_true, ↓reduceIte, ← Nat.cast_sum,
        sum_wgtPol_certs.1, sum_wgtPol_certs.2, expFnSub62Pol] <;> push_cast <;> ring
  rw [hPol false, hPol true, hwFac]
  have hkNe : ((kPol false : ℝ) + (kPol true : ℝ)) ≠ 0 := by exact_mod_cast hkPos.ne'
  field_simp [mul_ne_zero hkNe
      (by cases isNN <;> norm_num : (if isNN then (83670 : ℝ) else 167340) ≠ 0)]

theorem vEESub62_convex_pol (x : Fin (2 ^ systemQubits_frozen)) (n1 : Fin 47) {e1 e2 : Fin 187}
    (hlt : e1 < e2) :
    ((kPolEE n1 e1 e2 false : ℝ) + (kPolEE n1 e1 e2 true : ℝ)) * vEESub62 x n1 e1 e2 =
      (kPolEE n1 e1 e2 false : ℝ) * vEESub62Pol false x n1 e1 e2 +
      (kPolEE n1 e1 e2 true : ℝ) * vEESub62Pol true x n1 e1 e2 := by
  unfold vEESub62 vEESub62Pol
  have hkSum := kPolEE_sum n1 hlt
  refine vPotSub62_convex_pol false (.ee n1 e1 e2) (kPolEE n1 e1 e2) _ _ _ _ _
    (fun hw vz ↦ fib_ee_vz_eq n1 e1 e2 hw vz)
    (by
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [wEESpeciesTier1Walk_eq_factor, ← hkSum]; push_cast; ring)
    (by have := mSpCart254_pos_wstate (nucSpecies n1); omega) fun c _ ↦ ?_
  set cN1 := sysCoord x (nucParticle n1) with hcN1
  set cE1 := sysCoord x (elecParticle e1) with hcE1
  set cE2 := sysCoord x (elecParticle e2) with hcE2
  have hdEq : sectorDist3DSq3 true false cN1 (if false then 0 else cE2) cE1 =
      pairOpenDistSq x (elecP e1) (elecP e2) := by
    simp [hcN1, hcE1, hcE2, sectorDist3DSq3, elecParticle_eq_elecP, openBoxDist3DSq_sys]
  have hb1Eq : openCoordDistSq cN1 cE1 = pairOpenDistSq x (nucP n1) (elecP e1) := by
    rw [hcN1, hcE1, nucParticle_eq_nucP, elecParticle_eq_elecP, openCoordDistSq_sys]
  have hb2Eq : owB2Of3Port false cN1 (if false then 0 else cE2) cE1 =
      fin8Bin (pairOpenDistSq x (nucP n1) (elecP e2)) := by
    simp [hcN1, hcE1, hcE2, owB2Of3Port, nucParticle_eq_nucP, elecParticle_eq_elecP,
        openCoordDistSq_sys]
  rw [potExpectK2Sub62_collapse_scr c false (nucSpecies n1) 0 _ _ _ _ fnEE30
    (fun y z ↦
        by unfold midWTap29OfMode midWTap29 fnEE30; simp [Nat.shiftRight_eq_div_pow,
             Nat.div_div_eq_div_mul])
    (t1b_shift14_mod_cert.1 _ _ _ _)
    (fun w o9 _ hz ↦
        by rw [hdEq, hb1Eq, hb2Eq]; exact q14NonWrap_k2_dualLeg_lo6.1 x n1 e1 e2 w o9 hz),
    hdEq, hb1Eq, hb2Eq]
  set b1 := fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))
  set b2 := fin8Bin (pairOpenDistSq x (nucP n1) (elecP e2))
  have hMul : 16384 * (cShift14DualLeg true false (nucSpecies n1) b1 b2 : ℝ) =
      (cEE1Fin8DualLeg b1 : ℝ) + (cEE2Fin8DualLeg b2 : ℝ) := by
    exact_mod_cast cShift14DualLeg_mul16384.1 _ _ _
  simp_rw [hMul]
  rfl

theorem vNNSub62_convex_pol (x : Fin (2 ^ systemQubits_frozen)) {n1 n2 : Fin 47} (hlt : n1 < n2)
    (e1 : Fin 187) :
    ((kPolNN n1 n2 e1 false : ℝ) + (kPolNN n1 n2 e1 true : ℝ)) * vNNSub62 x n1 n2 e1 =
      (kPolNN n1 n2 e1 false : ℝ) * vNNSub62Pol false x n1 n2 e1 +
      (kPolNN n1 n2 e1 true : ℝ) * vNNSub62Pol true x n1 n2 e1 := by
  unfold vNNSub62 vNNSub62Pol
  have hkSum := kPolNN_sum hlt e1
  refine vPotSub62_convex_pol true (.nn n1 n2 e1) (kPolNN n1 n2 e1) _ _ _ _ _
    (fun hw vz ↦ fib_nn_vz_eq n1 n2 e1 hw vz)
    (by
      simp only [↓reduceIte]
      rw [wNNSpeciesTier1Walk_eq_factor _ _ (nucSpecies_not_3_3_of_lt_wstate hlt),
          show (mSpCart254 (nucSpecies n1) * mSpCart254 (nucSpecies n2)) * 167340 =
            (2 * (mSpCart254 (nucSpecies n1) * mSpCart254 (nucSpecies n2))) * 83670 by ring,
                ← hkSum]
      push_cast
      ring)
    (by rw [hkSum]; exact Nat.mul_pos (by omega) (Nat.mul_pos (mSpCart254_pos_wstate _)
          (mSpCart254_pos_wstate _)))
    fun c _ ↦ ?_
  set cN1 := sysCoord x (nucParticle n1) with hcN1
  set cN2 := sysCoord x (nucParticle n2) with hcN2
  set cE1 := sysCoord x (elecParticle e1) with hcE1
  have hdEq : sectorDist3DSq3 true true cN1 (if true then cN2 else 0) cE1 =
      pairOpenDistSq x (nucP n1) (nucP n2) := by
    simp [hcN1, hcN2, hcE1, sectorDist3DSq3, nucParticle_eq_nucP, openBoxDist3DSq_sys]
  have hb1Eq : openCoordDistSq cN1 cE1 = pairOpenDistSq x (nucP n1) (elecP e1) := by
    rw [hcN1, hcE1, nucParticle_eq_nucP, elecParticle_eq_elecP, openCoordDistSq_sys]
  have hb2Eq : owB2Of3Port true cN1 (if true then cN2 else 0) cE1 =
      fin8Bin (pairOpenDistSq x (nucP n2) (elecP e1)) := by
    simp [hcN1, hcN2, hcE1, owB2Of3Port, nucParticle_eq_nucP, elecParticle_eq_elecP,
        openCoordDistSq_sys]
  rw [potExpectK2Sub62_collapse_scr c true (nucSpecies n1) (nucSpecies n2) _ _ _ _ fnNN30
    (fun y z ↦ by unfold midWTap29OfMode midWTap29 fnNN30; simp)
    (t1b_shift14_mod_cert.2.1 _ _ _ _)
    (fun w o9 _ hz ↦
        by rw [hdEq, hb1Eq, hb2Eq]; exact q14NonWrap_k2_dualLeg_lo6.2.1 x hlt e1 w o9 hz),
    hdEq, hb1Eq, hb2Eq]
  set b1 := fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))
  set b2 := fin8Bin (pairOpenDistSq x (nucP n2) (elecP e1))
  have hMul : 16384 * (cShift14DualLeg true true (nucSpecies n1) b1 b2 : ℝ) =
      (cNNFin8DualLeg b1 : ℝ) + (cNNFin8DualLeg b2 : ℝ) := by
    exact_mod_cast cShift14DualLeg_mul16384.2.1 _ _ _
  simp_rw [hMul]
  rfl
noncomputable def midEESub62 : ℝ := midEETier1Walk + ((-21732 : ℝ) - (-24823 : ℝ)) / 1000

theorem short_table_eq_ee_sub62 (b1 b2 : Fin 8) : ((denomEEFermatCoin * (100000 / 100155)) /
    (2 ^ 29 : ℝ)) * ((cEE1Fin8DualLeg b1 : ℝ) + (cEE2Fin8DualLeg b2 : ℝ)) = midEESub62 +
    gEETier1Walk b1.val + gEETier1Walk b2.val + (-24823 : ℝ) / 1000 := by
  rw [short_table_eq_ee_tier1Walk b1 b2]; unfold midEESub62; ring
theorem convex2_err_le {k0 k1 : ℕ} (hk : 0 < k0 + k1)
    {v v0 v1 d r ε : ℝ}
    (hv : ((k0 : ℝ) + (k1 : ℝ)) * v = (k0 : ℝ) * v0 + (k1 : ℝ) * v1)
    (he0 : |d * v0 - r| ≤ ε)
    (he1 : |d * v1 - r| ≤ ε) :
    |d * v - r| ≤ ε := by
  have hkPos : (0 : ℝ) < (k0 : ℝ) + (k1 : ℝ) := by
    have : 0 < ((k0 + k1 : ℕ) : ℝ) := by exact_mod_cast hk
    push_cast at this; exact this
  have hk0 : (0 : ℝ) ≤ (k0 : ℝ) := Nat.cast_nonneg k0;
  have hk1 : (0 : ℝ) ≤ (k1 : ℝ) := Nat.cast_nonneg k1
  have hLin : ((k0 : ℝ) + (k1 : ℝ)) * (d * v - r) = (k0 : ℝ) * (d * v0 - r) + (k1 : ℝ) *
      (d * v1 - r) := by linear_combination d * hv
  rw [abs_le] at he0 he1 ⊢
  constructor <;> nlinarith

theorem vSub62_err_of_pol_ulp {εEE εNN εEN : ℝ}
    (hUlpEE : ∀ (pol : Bool) {d2 : ℕ}, Is3DBoxDistSq d2 → ¬(d2 % 8 = 7) →
      |((273022058496 : ℝ) / ((1 : ℝ) * 5714023029)) *
          expFnSub62Pol false pol d2 -
        ((-24823 : ℤ) : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √((max d2 1 : ℕ) : ℝ)| ≤ εEE)
    (hUlpNN : ∀ (pol : Bool) {d2 : ℕ}, Is3DBoxDistSq d2 → ¬(d2 % 8 = 7) →
      |((136511029248 : ℝ) / ((1 : ℝ) * 5714023029)) *
          expFnSub62Pol true pol d2 -
        ((-8958 : ℤ) : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √((max d2 8 : ℕ) : ℝ)| ≤ εNN)
    (hUlpEN : ∀ {d2 : ℕ}, Is3DBoxDistSq d2 → ¬(d2 % 8 = 7) →
      |((136511029248 : ℝ) / ((1 : ℝ) * 5714023029)) *
          expFnK2 wgtENQtr 1564629 fnNN30 word512DualLegLo6 false d2 -
        ((-11431 : ℤ) : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √((max d2 1 : ℕ) : ℝ)| ≤ εEN) :
    (∀ x n1 e1 e2, e1 < e2 →
      |(denomEEFermatCoin * (100000 / 100155)) * vEESub62 x n1 e1 e2 -
        rEEScaledGen gEETier1Walk midEESub62 x n1 e1 e2| ≤ εEE) ∧
    (∀ x n1 n2 e1, n1 < n2 →
      |(denomNNFermatCoinVal * (100000 / 100155)) * vNNSub62 x n1 n2 e1 -
        rNNScaledGen gNNTier1Walk midNNK2 x n1 n2 e1| ≤ εNN) ∧
    (∀ x n1 e1,
      |(denomENFermatCoin 1 * (100000 / 100155)) * vENK2 x n1 e1 -
        rENScaledGen gEETier1Walk gNNTier1Walk midENK2 x n1 e1| ≤ εEN) := by
  have linBnd {d a yv num c hsR r dc bnd ε : ℝ} (k : ℝ) (hy : |a * yv - dc - bnd| ≤ ε)
      (hs : ((d * (100000 / 100155)) / (2 ^ 29 : ℝ)) * c = hsR)
      (hd : ((d * (100000 / 100155)) / (2 ^ 29 : ℝ)) * k = a)
      (hnum : num = k * yv - c) (hr : a * yv - hsR - r = a * yv - dc - bnd) :
      |(d * (100000 / 100155)) * (num / (2 ^ 29 : ℝ)) - r| ≤ ε := by
    convert hy using 2
    calc (d * (100000 / 100155)) * (num / (2 ^ 29 : ℝ)) - r
        = (((d * (100000 / 100155)) / (2 ^ 29 : ℝ)) * k) * yv - ((d * (100000 / 100155)) /
            (2 ^ 29 : ℝ)) * c - r := by
          rw [hnum]
          ring
      _ = a * yv - dc - bnd := by rw [hd, hs, hr]
  refine ⟨fun x n1 e1 e2 hlt ↦ ?_, fun x n1 n2 e1 hlt ↦ ?_, fun x n1 e1 ↦ ?_⟩
  · have hPol (pol : Bool) : |(denomEEFermatCoin * (100000 / 100155)) * vEESub62Pol pol x n1 e1 e2 -
        rEEScaledGen gEETier1Walk midEESub62 x n1 e1 e2| ≤ εEE := by
      unfold vEESub62Pol rEEScaledGen pairShortBin
      refine linBnd 1 (hUlpEE pol (is3DBoxDistSq_pairOpenDistSq x (elecP e1) (elecP e2))
        (pairOpenDistSq_mod8_ne7_u x (elecP e1) (elecP e2))) (short_table_eq_ee_sub62
        (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1))) (fin8Bin (pairOpenDistSq x (nucP n1)
            (elecP e2))))
        (by unfold denomEEFermatCoin; norm_num) (by ring) (by push_cast; ring)
    have hkPos : 0 < kPolEE n1 e1 e2 false + kPolEE n1 e1 e2 true := by
      have := mSpCart254_pos_wstate (nucSpecies n1)
      rw [kPolEE_sum n1 hlt]; omega
    exact convex2_err_le hkPos (vEESub62_convex_pol x n1 hlt) (hPol false) (hPol true)
  · have hPol (pol : Bool) : |(denomNNFermatCoinVal * (100000 / 100155)) *
        vNNSub62Pol pol x n1 n2 e1 -
        rNNScaledGen gNNTier1Walk midNNK2 x n1 n2 e1| ≤ εNN := by
      unfold vNNSub62Pol rNNScaledGen pairShortBin
      refine linBnd 1 (hUlpNN pol (is3DBoxDistSq_pairOpenDistSq x (nucP n1) (nucP n2))
        (pairOpenDistSq_mod8_ne7_u x (nucP n1) (nucP n2))) (short_table_eq_nn_k2 (nucSpecies n1).val
        (nucSpecies n2).val (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1)))
        (fin8Bin (pairOpenDistSq x (nucP n2) (elecP e1))))
            (by unfold denomNNFermatCoinVal; norm_num)
        (by ring) (by push_cast; ring)
    have hkPos : 0 < kPolNN n1 n2 e1 false + kPolNN n1 n2 e1 true := by
      rw [kPolNN_sum hlt e1]
      exact Nat.mul_pos (by omega) (Nat.mul_pos (mSpCart254_pos_wstate _) (mSpCart254_pos_wstate _))
    exact convex2_err_le hkPos (vNNSub62_convex_pol x hlt e1) (hPol false) (hPol true)
  · unfold vENK2 rENScaledGen pairShortBin
    exact linBnd 5 (hUlpEN (is3DBoxDistSq_pairOpenDistSq x (nucP n1) (elecP e1))
      (pairOpenDistSq_mod8_ne7_u x (nucP n1) (elecP e1))) (short_table_eq_en_k2 (nucSpecies n1)
      (fin8Bin (pairOpenDistSq x (nucP n1) (elecP e1)))) (by unfold denomENFermatCoin; norm_num)
      (by ring) (by push_cast; ring)
end QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs

namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs
set_option exponentiation.threshold 256
open Real
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubCoin63Certs (IsTreeOf)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs (IsTreeOf.sumCarry256
    IsST4Of8 IsST4Of8.congr IsST4P2Of8 IsST4P2Of8.congr IsST4T3Sum8)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coul18K2Certs (IsST4T3Sum8.congr)
-- ============================================================================
-- Section 1. Sub62 Constants, Scaled-Bounds ULP Bridge, and 5-Lane Packing
-- ============================================================================

def sub62Mc (isNN : Bool) : Nat := if isNN then 136511029248 else 273022058496
def sub62DcMilli (isNN : Bool) : ℤ := if isNN then -8958 else -24823
def sub62EpsMilli (isNN : Bool) : Nat := if isNN then 25760 else 36075
def sub62HiNum (isNN : Bool) : Nat := if isNN then 34718 else 60898
def sub62LoNum (isNN : Bool) : Nat := if isNN then 16802 else 11252
def sub62FnCh (isNN : Bool) : ChW11 := if isNN then .nn else .ee
def sub62Fn30 (isNN : Bool) : ℕ → ℕ := if isNN then fnNN30 else fnEE30

theorem chFn_sub62FnCh_eq (isNN : Bool) : chFn (sub62FnCh isNN) = sub62Fn30 isNN := by
  cases isNN <;> rfl

theorem sub62HiNum_eq (isNN : Bool) : (sub62HiNum isNN : ℝ) = (sub62EpsMilli isNN : ℝ) -
    (sub62DcMilli isNN : ℝ) := by
  cases isNN <;> norm_num [sub62HiNum, sub62EpsMilli, sub62DcMilli]

theorem sub62LoNum_eq (isNN : Bool) : (sub62LoNum isNN : ℝ) = (sub62EpsMilli isNN : ℝ) +
    (sub62DcMilli isNN : ℝ) := by
  cases isNN <;> norm_num [sub62LoNum, sub62EpsMilli, sub62DcMilli]

def Sub62Consts (isNN : Bool) (g hi lo s0Sq : Nat) : Prop :=
    g = 64000 * sub62Mc isNN ∧ hi = sub62HiNum isNN * 5714023029 * 167340 ∧ lo = sub62LoNum isNN *
    5714023029 * 167340 ∧ s0Sq = (1000 * 5714023029 * 34359738368 * 167340) ^ 2
theorem ulp_sub62_of_checkNum63 (isNN : Bool) {g hi lo s0Sq m E : Nat} {y : ℝ}
    (hK : Sub62Consts isNN g hi lo s0Sq) (hm : 1 ≤ m)
    (hEy : 64 * (E : ℝ) = (167340 : ℝ) * y)
    (hc : checkNum63 E m g hi lo s0Sq = true) :
    |((sub62Mc isNN : ℝ) / ((1 : ℝ) * 5714023029)) * y -
        (sub62DcMilli isNN : ℝ) / 1000 -
        (2 ^ 35 : ℝ) / √(m : ℝ)| ≤ (sub62EpsMilli isNN : ℝ) / 1000 := by
  obtain ⟨hlo, hU, hL⟩ := checkNum63_sound hc
  rcases hK with ⟨rfl, rfl, rfl, rfl⟩
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hsq : √(m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hm0.le;
  have hrt : (0 : ℝ) < √(m : ℝ) := Real.sqrt_pos.mpr hm0
  set K : ℝ := 1000 * 5714023029 * (167340 : ℝ)
  have hKpos : 0 < K := by dsimp only [K]; positivity
  set S : ℝ := K * (2 ^ 35 : ℝ)
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  set U : ℝ := ((64000 * sub62Mc isNN : ℕ) : ℝ) * (E : ℝ) +
    ((sub62HiNum isNN * 5714023029 * 167340 : ℕ) : ℝ)
  set L : ℝ := ((64000 * sub62Mc isNN : ℕ) : ℝ) * (E : ℝ) -
    ((sub62LoNum isNN * 5714023029 * 167340 : ℕ) : ℝ)
  have hU0 : 0 ≤ U :=
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hUR := (Nat.cast_le (α := ℝ)).mpr hU
  have hLR := (Nat.cast_le (α := ℝ)).mpr hL
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hlo] at hLR
  have hUsq : S ^ 2 ≤ (U * √(m : ℝ)) ^ 2 := by
    rw [mul_pow U, hsq]; dsimp only [S, K, U]; push_cast at hUR ⊢; linarith
  have hLsq : (L * √(m : ℝ)) ^ 2 ≤ S ^ 2 := by
    rw [mul_pow L, hsq]; dsimp only [S, K, L]; push_cast at hLR ⊢; linarith
  have hUrt : S ≤ U * √(m : ℝ) := (sq_le_sq₀ hS0 (mul_nonneg hU0 hrt.le)).mp hUsq;
  have hLrt : L * √(m : ℝ) ≤ S := (abs_le.mp ((sq_le_sq.mp hLsq).trans_eq (abs_of_nonneg hS0))).2
  set X : ℝ := ((sub62Mc isNN : ℝ) / ((1 : ℝ) * 5714023029)) * y
  have hScale : ((64000 * sub62Mc isNN : ℕ) : ℝ) * (E : ℝ) = K * X := by
    dsimp only [K, X]
    rw [show ((64000 * sub62Mc isNN : ℕ) : ℝ) * (E : ℝ) = 1000 * (sub62Mc isNN : ℝ) *
        (64 * (E : ℝ)) by push_cast; ring,
        hEy]
    field_simp
  have hU_eq : U = K * (X + (sub62HiNum isNN : ℝ) / 1000) := by
    dsimp only [U, K]; rw [hScale]; push_cast; ring
  have hL_eq : L = K * (X - (sub62LoNum isNN : ℝ) / 1000) := by
    dsimp only [L, K]; rw [hScale]; push_cast; ring
  have hU_div : (2 ^ 35 : ℝ) ≤ (X + (sub62HiNum isNN : ℝ) / 1000) * √(m : ℝ) :=
    le_of_mul_le_mul_left (by dsimp only [S] at hUrt; rw [hU_eq] at hUrt; linarith) hKpos
  have hL_div : (X - (sub62LoNum isNN : ℝ) / 1000) * √(m : ℝ) ≤ (2 ^ 35 : ℝ) :=
    le_of_mul_le_mul_left (by dsimp only [S] at hLrt; rw [hL_eq] at hLrt; linarith) hKpos
  have hdivHi : (2 ^ 35 : ℝ) / √(m : ℝ) ≤ X + (sub62HiNum isNN : ℝ) / 1000 :=
      (div_le_iff₀ hrt).mpr hU_div
  have hdivLo : X - (sub62LoNum isNN : ℝ) / 1000 ≤ (2 ^ 35 : ℝ) / √(m : ℝ) :=
      (le_div_iff₀ hrt).mpr hL_div
  rw [sub62HiNum_eq] at hdivHi
  rw [sub62LoNum_eq] at hdivLo
  exact abs_le.mpr ⟨by linarith, by linarith⟩

inductive Lane5 : Type
  | l0 | l1 | l2 | l3 | l4

def selLane5 {α : Type} (c : Lane5) (x0 x1 x2 x3 x4 : α) : α :=
  match c with
  | .l0 => x0
  | .l1 => x1
  | .l2 => x2
  | .l3 => x3
  | .l4 => x4

def chFn5 (c : Lane5) (f0 f1 f2 f3 f4 : Nat → Nat) (x : Nat) : Nat :=
    selLane5 c (f0 x) (f1 x) (f2 x) (f3 x) (f4 x)
theorem chFn5_app (c : Lane5) (F : Lane5 → Nat → Nat) (x : Nat) : chFn5 c (F .l0) (F .l1) (F .l2)
    (F .l3) (F .l4) x = F c x := by
  cases c <;> rfl

def pack5Nat (x0 x1 x2 x3 x4 : Nat) : Nat :=
    x0 + 4096 * (x1 + 4096 * (x2 + 4096 * (x3 + 4096 * x4)))
theorem pack5Nat_zero : pack5Nat 0 0 0 0 0 = 0 := rfl

theorem pack5Nat_add (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : Nat) : pack5Nat a0 a1 a2 a3 a4 +
    pack5Nat b0 b1 b2 b3 b4 = pack5Nat (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) (a4 + b4) := by
  unfold pack5Nat; ring
def unpk5 (c : Lane5) (v : Nat) : Nat :=
  match c with
  | .l0 => v % 4096
  | .l1 => (v / 4096) % 4096
  | .l2 => (v / 16777216) % 4096
  | .l3 => (v / 68719476736) % 4096
  | .l4 => v / 281474976710656

theorem unpk5_zero (c : Lane5) : unpk5 c 0 = 0 := by cases c <;> rfl
theorem unpk5_pack5Nat (c : Lane5) {x0 x1 x2 x3 : Nat} (x4 : Nat) (h0 : x0 < 4096) (h1 : x1 < 4096)
    (h2 : x2 < 4096) (h3 : x3 < 4096) : unpk5 c (pack5Nat x0 x1 x2 x3 x4) =
    selLane5 c x0 x1 x2 x3 x4 := by
  cases c <;> { unfold unpk5 selLane5 pack5Nat; dsimp only; omega }

def u5W (c : Lane5) (w : Nat) (bw : Bool) : Nat :=
  match c with
  | .l0 => if 1452 ≤ w ∧ !bw then 1 else 0
  | .l1 => if 1452 ≤ w ∧ bw then 1 else 0
  | .l2 => if w < 1750 ∧ !bw then 1 else 0
  | .l3 => if w < 1750 ∧ bw then 1 else 0
  | .l4 => 1

def dwSub62W (isNN : Bool) (ch : ChK2) (w : Nat) (bw : Bool) : Nat :=
  if isNN then
    match ch with
    | .ee => 80
    | .nn => if w < 1750 ∧ !bw then 4 else 0
    | .en => if w < 1750 ∧ bw then 4 else 0
  else
    match ch with
    | .ee => if w < 1452 then 82 else 80
    | .nn => if 1452 ≤ w ∧ !bw then 2 else 0
    | .en => if 1452 ≤ w ∧ bw then 2 else 0

theorem dwSub62W_sum_eq_termSub62PolNat (isNN pol : Bool) (w : Nat) (bw : Bool)
    (Z : Nat) : dwSub62W isNN .ee w bw * (Z / 256) + dwSub62W isNN .nn w bw *
    ((Z + (if pol then 0 else 256)) / 512) + dwSub62W isNN .en w bw *
    ((Z + (if pol then 256 else 0)) / 512) = termSub62PolNat isNN pol w bw Z := by
  cases isNN <;> rfl

theorem dwSub62W_ee_false_add (w : Nat) (bw : Bool) :
    dwSub62W false .ee w bw + 2 * (u5W .l0 w bw + u5W .l1 w bw) = 82 * u5W .l4 w bw := by
  unfold dwSub62W u5W
  by_cases hw1 : w < 1452 <;> cases bw <;>
    simp [hw1, show (1452 ≤ w) ↔ ¬(w < 1452) by omega]
theorem dwSub62W_lanes (w : Nat) (bw : Bool) : dwSub62W false .nn w bw = 2 * u5W .l0 w bw ∧
    dwSub62W false .en w bw = 2 * u5W .l1 w bw ∧ dwSub62W true .ee w bw = 80 * u5W .l4 w bw ∧
    dwSub62W true .nn w bw = 4 * u5W .l2 w bw ∧ dwSub62W true .en w bw = 4 * u5W .l3 w bw := by
  unfold dwSub62W u5W
  by_cases hw1 : 1452 ≤ w <;> by_cases hw2 : w < 1750 <;>
    cases bw <;> simp [hw1, hw2]

def dwSub62At13 (isNN : Bool) (ch : ChK2) (i : Nat) : Nat :=
    dwSub62W isNN ch (wAt13 i) (affineBit13 7483 (x13At13 i))
def u5At13 (c : Lane5) (i : Nat) : Nat := u5W c (wAt13 i) (affineBit13 7483 (x13At13 i))
def u5Pack13 (i : Nat) : Nat :=
    pack5Nat (u5At13 .l0 i) (u5At13 .l1 i) (u5At13 .l2 i) (u5At13 .l3 i) (u5At13 .l4 i)
def eqB63 (a b : Bool) : Bool :=
    Bool.casesOn a (Bool.casesOn b true false) (Bool.casesOn b false true)
def checkPar7483Flip (idx12 : Nat) : Bool :=
    fN63 (Nat.add (Nat.mod idx12 2048) (Nat.mul 4096 (Nat.div idx12 2048))) fun x0 =>
    eqB63 (Nat.beq (par14Pure 7483 x0) 0) (Nat.beq (par14Pure 7483 (Nat.add x0 2048)) 1)
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tPar7483Flip : allCnt63 checkPar7483Flip 4096 0 = true := by decide +kernel

theorem affineBit13_7483_flip (w : Fin 2048) (u1 : Fin 2) :
    affineBit13 7483 (x13OfW11U01 w 1 u1) = !(affineBit13 7483 (x13OfW11U01 w 0 u1)) := by
  have hw := w.isLt
  have hu1 := u1.isLt
  have hc := allCnt63_sound tPar7483Flip (w.val + 2048 * u1.val) (by omega)
  simp only [zero_add, checkPar7483Flip, fN63_eq, nat_add_def, nat_mod_def, nat_mul_def,
    nat_div_def, show (w.val + 2048 * u1.val) % 2048 = w.val by omega,
    show (w.val + 2048 * u1.val) / 2048 = u1.val by omega,
    par14Pure_eq_affineBit13 (by norm_num : 7483 < 16384)] at hc
  rw [show x13OfW11U01 w 0 u1 = w.val + 4096 * u1.val by
        unfold x13OfW11U01; simp only [Fin.val_zero]; omega,
      show x13OfW11U01 w 1 u1 = (w.val + 4096 * u1.val) + 2048 by
        unfold x13OfW11U01; simp only [Fin.val_one]; omega]
  revert hc
  cases affineBit13 7483 (w.val + 4096 * u1.val) <;>
    cases affineBit13 7483 (w.val + 4096 * u1.val + 2048) <;> decide
theorem sum_u5At13_eq_sum_w (c : Lane5) : (∑ i ∈ Finset.range nSamples13, u5At13 c i) = ∑ w :
    Fin 2048, ∑ u0 : Fin 2, ∑ u1 : Fin 2, u5W c w.val (affineBit13 7483 (x13OfW11U01 w u0 u1)) := by
  rw [← Fin.sum_univ_eq_sum_range, ← equivN13Of64x128.sum_comp, Fintype.sum_prod_type]
  symm
  rw [← equivW11CLB.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g6 _ => ?_
  rw [← equiv128Of32x2x2.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u5 _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ?_
  set iVal := 128 * g6.val + (4 * u5.val + (u0.val + 2 * u1.val))
  have hiEq : (equivN13Of64x128 (g6, equiv128Of32x2x2 (u5, (u0, u1)))).val = iVal := rfl
  have hiDiv : iVal / 128 = g6.val := by
    have := u5.isLt; have := u0.isLt; have := u1.isLt; dsimp [iVal]; omega
  have hiMod4 : (iVal % 128) / 4 = u5.val := by
    have := u5.isLt; have := u0.isLt; have := u1.isLt; dsimp [iVal]; omega
  have hiMod01 : (iVal % 128) % 4 = u0.val + 2 * u1.val := by
    have := u5.isLt; have := u0.isLt; have := u1.isLt; dsimp [iVal]; omega
  have hwEq : wAt13 iVal = (equivW11CLB (u5, g6)).val := by unfold wAt13; rw [hiMod4, hiDiv]; rfl
  have hxEq : x13At13 iVal = x13OfW11U01 (equivW11CLB (u5, g6)) u0 u1 := by
    unfold x13At13 x13OfW11U01; rw [hwEq, hiMod01]; ring
  unfold u5At13; rw [hiEq, hwEq, hxEq]
theorem u5W_flip_sum (w : Nat) (bw : Bool) : u5W .l0 w bw + u5W .l0 w (!bw) =
    (if 1452 ≤ w then 1 else 0) ∧ u5W .l1 w bw + u5W .l1 w (!bw) = (if 1452 ≤ w then 1 else 0) ∧
    u5W .l2 w bw + u5W .l2 w (!bw) = (if w < 1750 then 1 else 0) ∧ u5W .l3 w bw + u5W .l3 w (!bw) =
    (if w < 1750 then 1 else 0) := by
  unfold u5W
  by_cases h1 : 1452 ≤ w <;> by_cases h2 : w < 1750 <;> cases bw <;> simp [h1, h2]

theorem sum_u5At13_lt_4096 :
    (∑ i ∈ Finset.range nSamples13, u5At13 .l0 i) < 4096 ∧
    (∑ i ∈ Finset.range nSamples13, u5At13 .l1 i) < 4096 ∧
    (∑ i ∈ Finset.range nSamples13, u5At13 .l2 i) < 4096 ∧
    (∑ i ∈ Finset.range nSamples13, u5At13 .l3 i) < 4096 := by
  have hBnd (c : Lane5) (P : Nat → Prop) [DecidablePred P] (w0 : Fin 2048) (hw0 : ¬P w0.val)
      (hFl : ∀ w bw, u5W c w bw + u5W c w (!bw) = if P w then 1 else 0) :
      (∑ i ∈ Finset.range nSamples13, u5At13 c i) < 4096 := by
    rw [sum_u5At13_eq_sum_w c, Finset.sum_congr rfl (fun w _ => show _ =
        2 * (if P w.val then 1 else 0) by
      rw [Finset.sum_comm, Fin.sum_univ_two]
      simp only [Fin.sum_univ_two, affineBit13_7483_flip]
      have e0 := hFl w.val (affineBit13 7483 (x13OfW11U01 w 0 0))
      have e1 := hFl w.val (affineBit13 7483 (x13OfW11U01 w 0 1))
      omega), ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ w0), _root_.ite_eq_right hw0,
          Nat.mul_zero,
      zero_add]
    have hle := Finset.sum_le_sum (s := Finset.univ.erase w0)
      (g := fun _ => 2) fun w _ => show 2 * (if P w.val then 1 else 0) ≤ 2 by split_ifs <;> omega
    have hcard : (∑ _w ∈ Finset.univ.erase w0, 2) = 4094 := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ w0)]
    omega
  exact ⟨hBnd .l0 (1452 ≤ ·) ⟨0, by omega⟩ (by norm_num) (fun w bw => (u5W_flip_sum w bw).1),
         hBnd .l1 (1452 ≤ ·) ⟨0, by omega⟩ (by norm_num) (fun w bw => (u5W_flip_sum w bw).2.1),
         hBnd .l2 (· < 1750) ⟨2047, by omega⟩ (by norm_num) (fun w bw => (u5W_flip_sum w bw).2.2.1),
         hBnd .l3 (· < 1750) ⟨2047, by omega⟩ (by norm_num)
           (fun w bw => (u5W_flip_sum w bw).2.2.2)⟩
def wgtLeaf5Sub62Pure (idx13 : Nat) : Nat := fN63 (Nat.div idx13 128) fun g6 =>
    fN63 (Nat.mod idx13 128) fun rem7 => fN63 (Nat.div rem7 4) fun u5 =>
    fN63 (Nat.mod rem7 4) fun c01 => fN63 (wOfU5GamF u5 g6) fun w =>
    fN63 (Nat.add w (Nat.mul 2048 c01)) fun x13 =>
    sB63 (Nat.beq (par14Pure 7483 x13) 0) fun pZero =>
    fN63 (Bool.casesOn (Nat.ble (Nat.add w 1) 1452) (Bool.casesOn pZero 4096 1) 0) fun loEE =>
    fN63 (Bool.casesOn (Nat.ble (Nat.add w 1) 1750) 0 (Bool.casesOn pZero 68719476736 16777216))
    fun hiNN => Nat.add 281474976710656 (Nat.add loEE hiNN)
theorem wgtLeaf5Sub62Pure_eq_pack13 {i : Nat} (hi : i < 8192) :
    wgtLeaf5Sub62Pure i = u5Pack13 i := by
  unfold wgtLeaf5Sub62Pure u5Pack13 u5At13 u5W x13At13 wAt13 pack5Nat
  simp only [fN63_eq, sB63_eq, nat_div_def, nat_mod_def, nat_add_def, nat_mul_def]
  rw [wOfU5GamF_eq_spec ⟨(i % 128) / 4, by omega⟩ ⟨i / 128, by omega⟩,
      par14Pure_eq_affineBit13 (by norm_num : 7483 < 16384)]
  set w := wOfU5Gam ((i % 128) / 4) (i / 128)
  set bw := affineBit13 7483 (w + 2048 * ((i % 128) % 4))
  have hble (a b : Nat) : Nat.ble (a + 1) b = decide (a < b) :=
    Bool.eq_iff_iff.mpr (by simp [Nat.ble_eq])
  rw [hble w 1452, hble w 1750]
  by_cases hw1 : w < 1452 <;> by_cases hw2 : w < 1750 <;> cases bw <;>
    simp only [hw1, hw2, show (1452 ≤ w) ↔ ¬(w < 1452) by omega,
      decide_true, decide_false, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      and_true, and_false, not_true_eq_false, not_false_eq_true, ↓reduceIte,
      show Nat.beq 0 0 = true from rfl, show Nat.beq 1 0 = false from rfl]
def buildWgt5Sub62NT : NatTree := buildNT63 wgtLeaf5Sub62Pure 13 0 4096
theorem buildWgt5Sub62NT_def :
    buildNT63 wgtLeaf5Sub62Pure 13 0 4096 = buildWgt5Sub62NT := rfl
def wgtLeaf5Sub62Fast (wNT11 lo7ParNT hi6ParNT : NatTree) (idx13 : Nat) : Nat :=
    fN63 (Nat.div idx13 128) fun g6 => fN63 (Nat.mod idx13 128) fun rem7 =>
    fN63 (Nat.div rem7 4) fun u5 => fN63 (Nat.mod rem7 4) fun c01 =>
    fN63 (getNT1024F wNT11 (Nat.add (Nat.mul 32 g6) u5)) fun w =>
    fN63 (Nat.add w (Nat.mul 2048 c01)) fun x13 =>
    sB63 (Nat.beq (getNT64F lo7ParNT (Nat.mod x13 128))
    (getNT32F hi6ParNT (Nat.div x13 128))) fun pZero =>
    fN63 (Bool.casesOn (Nat.ble (Nat.add w 1) 1452) (Bool.casesOn pZero 4096 1) 0) fun loEE =>
    fN63 (Bool.casesOn (Nat.ble (Nat.add w 1) 1750) 0 (Bool.casesOn pZero 68719476736 16777216))
    fun hiNN => Nat.add 281474976710656 (Nat.add loEE hiNN)
def wgt5NTFastSub62 : NatTree :=
    sNT63 (bNT11 (fun idx11 => wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)) 0 1024) fun wNT11 =>
    sNT63 (bNT7 (par14Pure 7483) 0 64) fun lo7ParNT =>
    sNT63 (bNT6 (fun hi6 => par14Pure 7483 (Nat.mul 128 hi6)) 0 32) fun hi6ParNT =>
    bNT13 (wgtLeaf5Sub62Fast wNT11 lo7ParNT hi6ParNT) 0 4096
def checkPar7483Split (lo7ParNT hi6ParNT : NatTree) (x13 : Nat) : Bool :=
    eqB63 (Nat.beq (getNT64F lo7ParNT (Nat.mod x13 128)) (getNT32F hi6ParNT (Nat.div x13 128)))
    (Nat.beq (par14Pure 7483 x13) 0)
def checkPar7483All : Bool := sNT63 (bNT7 (par14Pure 7483) 0 64) fun lo7 =>
    sNT63 (bNT6 (fun hi6 => par14Pure 7483 (Nat.mul 128 hi6)) 0 32) fun hi6 =>
    allCnt63 (checkPar7483Split lo7 hi6) 8192 0
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tPar7483All : checkPar7483All = true := by decide +kernel

theorem wgtLeaf5Sub62Fast_eq_pure {i : Nat} (hi : i < 8192) : wgtLeaf5Sub62Fast (bNT11 (fun idx11 =>
    wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)) 0 1024) (bNT7 (par14Pure 7483) 0 64)
    (bNT6 (fun hi6 => par14Pure 7483 (Nat.mul 128 hi6)) 0 32) i = wgtLeaf5Sub62Pure i := by
  have hAll := tPar7483All; unfold checkPar7483All at hAll; rw [sNT63_eq, sNT63_eq] at hAll
  set wNT11 := bNT11 (fun idx11 => wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)) 0 1024
  set lo7NT := bNT7 (par14Pure 7483) 0 64
  set hi6NT := bNT6 (fun hi6 => par14Pure 7483 (Nat.mul 128 hi6)) 0 32
  change allCnt63 (checkPar7483Split lo7NT hi6NT) 8192 0 = true at hAll
  change wgtLeaf5Sub62Fast wNT11 lo7NT hi6NT i = wgtLeaf5Sub62Pure i
  unfold wgtLeaf5Sub62Fast wgtLeaf5Sub62Pure
  simp only [fN63_eq, sB63_eq, nat_div_def, nat_mod_def, nat_add_def, nat_mul_def]
  rw [show getNT1024F wNT11 (32 * (i / 128) + (i % 128) / 4) = wOfU5GamF ((i % 128) / 4)
      (i / 128) by
    dsimp only [wNT11]
    rw [get_bNT11 (fun idx11 => wOfU5GamF (Nat.mod idx11 32) (Nat.div idx11 32)) (by omega)]
    simp only [nat_mod_def, nat_div_def,
      show (32 * (i / 128) + (i % 128) / 4) % 32 = (i % 128) / 4 by omega,
      show (32 * (i / 128) + (i % 128) / 4) / 32 = i / 128 by omega]]
  set w := wOfU5GamF ((i % 128) / 4) (i / 128)
  have hw_lt : w < 2048 := by
    dsimp only [w]
    rw [wOfU5GamF_eq_spec ⟨(i % 128) / 4, by omega⟩ ⟨i / 128, by omega⟩]
    exact wOfU5Gam_lt ⟨(i % 128) / 4, by omega⟩ ⟨i / 128, by omega⟩
  have hp := allCnt63_sound hAll (w + 2048 * ((i % 128) % 4)) (by omega)
  simp only [zero_add, checkPar7483Split, eqB63, nat_mod_def, nat_div_def] at hp
  rw [show Nat.beq (getNT64F lo7NT ((w + 2048 * ((i % 128) % 4)) % 128))
        (getNT32F hi6NT ((w + 2048 * ((i % 128) % 4)) / 128)) =
      Nat.beq (par14Pure 7483 (w + 2048 * ((i % 128) % 4))) 0 by
    revert hp
    cases Nat.beq (getNT64F lo7NT ((w + 2048 * ((i % 128) % 4)) % 128))
                  (getNT32F hi6NT ((w + 2048 * ((i % 128) % 4)) / 128)) <;>
      cases Nat.beq (par14Pure 7483 (w + 2048 * ((i % 128) % 4))) 0 <;> intro hp <;> first
        | rfl
        | cases hp]

theorem buildNT63_congr {f g : Nat → Nat} :
    ∀ (d b half : Nat), half = 2 ^ d / 2 → (∀ i, b ≤ i → i < b + 2 ^ d → f i = g i) →
      buildNT63 f d b half = buildNT63 g d b half
  | 0, b, half, _, hfg => by
      rw [buildNT63_zero, buildNT63_zero, hfg b (le_refl b) (by omega)]
  | d + 1, b, half, hhalf, hfg => by
      have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
      subst hhalf; rw [hp, buildNT63_succ f d, buildNT63_succ g d]
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; ring
      rw [buildNT63_congr d b (2 ^ d / 2) rfl (fun i h1 h2 => hfg i h1 (by omega)),
          buildNT63_congr d (b + 2 ^ d) (2 ^ d / 2) rfl
            (fun i h1 h2 => hfg i (by omega) (by omega))]

theorem wgt5NTFastSub62_eq : wgt5NTFastSub62 = buildWgt5Sub62NT := by
  unfold wgt5NTFastSub62; rw [sNT63_eq, sNT63_eq, sNT63_eq, bNT13_eq, ← buildWgt5Sub62NT_def]
  exact buildNT63_congr 13 0 4096 (by norm_num)
    (fun i _ hi => wgtLeaf5Sub62Fast_eq_pure (by simpa using hi))

-- ============================================================================
-- Section 2. Synchronous Depth-13 5-Lane Bucket Sweep Soundness
-- ============================================================================

def initTreeT3D13 (jpNT : NatTree) : NatTree → NatTree → ST4T3 → ST4T3
  | .leaf pk, .leaf dw, cur => initLeafT3K2 jpNT pk dw cur
  | .node spL spR, .node wL wR, cur =>
      sST4T3 (initTreeT3D13 jpNT spL wL cur) fun mid =>
      initTreeT3D13 jpNT spR wR mid
  | _, _, cur => cur

def initTreeP2D13 (jpNT spNT wgtNT : NatTree) : ST4P2 :=
    ST4T3.casesOn (initTreeT3D13 jpNT spNT wgtNT emptyST4T3K2F) fun sc s0 s1 =>
    sST4 (addST4K2 sc s0) fun r0 => sST4 (addST4K2 sc s1) fun r1 => .mk r0 r1
def advSubD13 (jpNT : NatTree) : NatTree → NatTree → ST4P2 → ST4P2
  | .leaf pk, .leaf dw, cur => advLeafP2K2 jpNT pk dw cur
  | .node spL spR, .node wL wR, cur =>
      sST4P2 (advSubD13 jpNT spL wL cur) fun mid =>
      advSubD13 jpNT spR wR mid
  | _, _, cur => cur

def sweepBkt5Sub62 (c : Lane5) (a : Nat) (r01 : Bool) (p j idx : Nat) : Nat :=
    ∑ i ∈ Finset.range nSamples13, if j18At13 a r01 (decide (i < p)) i = j ∧ df8At13 i =
    idx then u5At13 c i else 0
def sweepBktSub62 (isNN : Bool) (ch : ChK2) (a : Nat) (r01 : Bool) (p j idx : Nat) : Nat :=
    ∑ i ∈ Finset.range nSamples13, if j18At13 a r01 (decide (i < p)) i = j ∧ df8At13 i =
    idx then dwSub62At13 isNN ch i else 0
def initBktPack5Sub62 (a : Nat) (r01 : Bool) (b n j idx : Nat) : Nat :=
    ∑ k ∈ Finset.range n, if j18At13 a r01 false (b + k) = j ∧ df8At13 (b + k) =
    idx then u5Pack13 (b + k) else 0
def sweepBktPack5Sub62 (a : Nat) (r01 : Bool) (p j idx : Nat) : Nat :=
    ∑ i ∈ Finset.range nSamples13, if j18At13 a r01 (decide (i < p)) i = j ∧ df8At13 i =
    idx then u5Pack13 i else 0
def transBktPack5Sub62 (jOld jNew : Bool → Nat → Nat) (r01 : Bool) (p j idx : Nat) : Nat :=
    ∑ i ∈ Finset.range nSamples13, if (if i < p then jNew r01 i else jOld r01 i) = j ∧ df8At13 i =
    idx then u5Pack13 i else 0
theorem sweepBktPack5Sub62_eq_pack5 (a : Nat) (r01 : Bool)
    (p j idx : Nat) : sweepBktPack5Sub62 a r01 p j idx = pack5Nat (sweepBkt5Sub62 .l0 a r01 p j idx)
    (sweepBkt5Sub62 .l1 a r01 p j idx) (sweepBkt5Sub62 .l2 a r01 p j idx)
    (sweepBkt5Sub62 .l3 a r01 p j idx) (sweepBkt5Sub62 .l4 a r01 p j idx) := by
  unfold sweepBktPack5Sub62 sweepBkt5Sub62 u5Pack13 pack5Nat;
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

theorem sweepBktSub62_ee_false_add (a : Nat) (r01 : Bool)
    (p j idx : Nat) : sweepBktSub62 false .ee a r01 p j idx + 2 *
    (sweepBkt5Sub62 .l0 a r01 p j idx + sweepBkt5Sub62 .l1 a r01 p j idx) = 82 *
    sweepBkt5Sub62 .l4 a r01 p j idx := by
  unfold sweepBktSub62 sweepBkt5Sub62 dwSub62At13 u5At13;
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := dwSub62W_ee_false_add (wAt13 i) (affineBit13 7483 (x13At13 i))
  split_ifs <;> omega

theorem sweepBktSub62_lanes (a : Nat) (r01 : Bool)
    (p j idx : Nat) : sweepBktSub62 false .nn a r01 p j idx = 2 * sweepBkt5Sub62 .l0 a r01 p j idx ∧
    sweepBktSub62 false .en a r01 p j idx = 2 * sweepBkt5Sub62 .l1 a r01 p j idx ∧
    sweepBktSub62 true .ee a r01 p j idx = 80 * sweepBkt5Sub62 .l4 a r01 p j idx ∧
    sweepBktSub62 true .nn a r01 p j idx = 4 * sweepBkt5Sub62 .l2 a r01 p j idx ∧
    sweepBktSub62 true .en a r01 p j idx = 4 * sweepBkt5Sub62 .l3 a r01 p j idx := by
  unfold sweepBktSub62 sweepBkt5Sub62 dwSub62At13 u5At13; simp only [Finset.mul_sum]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> {
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨h0, h1, h2, h3, h4⟩ := dwSub62W_lanes (wAt13 i) (affineBit13 7483 (x13At13 i))
    split_ifs <;> omega
  }

attribute [local irreducible]
  nLanes8 nSamples13 wAt13 x13At13 df8At13 o9At13
  dwSub62At13 u5At13 u5Pack13 d11At13 j18At13 jPack4Leaf
  buildNT63 bNT9 bNT11 bNT13 getNT256F getNT1024F
  spNTFastK2 buildSamplePackK2NT wgt5NTFastSub62 buildWgt5Sub62NT
  samplePackLeafK2Pure wgtLeaf5Sub62Pure par14Pure wOfU5GamF allCnt63 allList63 buildJPackNT
  word512DualLegLo6T emptyST4T3K2F advLeafP2K2 insST4K2 decST4K2 addST4K2 sufST128F

def IsST4P2Pack5Sub62 (a p : Nat) (cur : ST4P2) : Prop :=
    IsST4P2Of8 (sweepBktPack5Sub62 a false p) (sweepBktPack5Sub62 a true p) cur
def IsST4P2Pack5TransSub62 (jOld jNew : Bool → Nat → Nat) (p : Nat) (cur : ST4P2) : Prop :=
    IsST4P2Of8 (transBktPack5Sub62 jOld jNew false p) (transBktPack5Sub62 jOld jNew true p) cur
theorem sweepBktPack5Sub62_eq_trans (a : Nat) (r01 : Bool) (p : Nat) : sweepBktPack5Sub62 a r01 p =
    transBktPack5Sub62 (fun r i => j18At13 a r false i) (fun r i => j18At13 a r true i) r01 p := by
  funext j idx; unfold sweepBktPack5Sub62 transBktPack5Sub62
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hlt : i < p
  · rw [_root_.ite_eq_left hlt, decide_eq_true hlt]
  · rw [_root_.ite_eq_right hlt, decide_eq_false hlt]

theorem selST4P2Pack5_sound {a p : Nat} {cur : ST4P2} (h : IsST4P2Pack5Sub62 a p cur)
    (r01 : Bool) : IsST4Of8 (sweepBktPack5Sub62 a r01 p) (selST4P2 r01 cur) := by
  rcases cur with ⟨s0, s1⟩
  cases r01
  · exact h.1
  · exact h.2

theorem initLeafT3Pack5_sound (a : Nat) {i : Nat} (hi : i < 8192) {F0 F1 : Nat → Nat → Nat}
    {cur : ST4T3} (hcur : IsST4T3Sum8 F0 F1 cur) :
    IsST4T3Sum8 (updAddST4K2 F0 (j18At13 a false false i) (df8At13 i) (u5Pack13 i))
    (updAddST4K2 F1 (j18At13 a true false i) (df8At13 i) (u5Pack13 i))
    (initLeafT3K2 (bNT11 (jPack4Leaf a) 0 1024) (samplePackLeafK2Pure i) (wgtLeaf5Sub62Pure i) cur)
    := by
  rcases cur with ⟨sc, s0, s1⟩
  rcases hcur with ⟨Fc, G0, G1, hsc, hs0, hs1, e0, e1⟩
  rw [samplePackLeafK2Pure_eq_pack13 hi, wgtLeaf5Sub62Pure_eq_pack13 hi]
  have hdf8 := df8At13_lt_256 i
  have hd11 := d11At13_lt_2048 i
  unfold initLeafT3K2
  simp only [fN63_eq, nat_mod_def, nat_div_def]
  have hm256 : (df8At13 i + 256 * d11At13 i) % 256 = df8At13 i := by omega
  have hd256 : (df8At13 i + 256 * d11At13 i) / 256 = d11At13 i := by omega
  rw [hm256, hd256, get_bNT11 (jPack4Leaf a) hd11];
  obtain ⟨u00, u10, _, _⟩ := jPack4Leaf_unpack_at13 a i; rw [u00, u10]
  cases hbeq : Nat.beq (j18At13 a false false i) (j18At13 a true false i)
  · dsimp only [Bool.casesOn]; simp only [sST4_eq]
    refine ⟨Fc, updAddST4K2 G0 (j18At13 a false false i) (df8At13 i) (u5Pack13 i),
      updAddST4K2 G1 (j18At13 a true false i) (df8At13 i) (u5Pack13 i), hsc,
      insST4K2_isST4Of8 hs0 (u5Pack13 i) (j18At13_lt_four a false false i) hdf8,
      insST4K2_isST4Of8 hs1 (u5Pack13 i) (j18At13_lt_four a true false i) hdf8,
      fun j hj idx hidx => ?_, fun j hj idx hidx => ?_⟩
    · have h := e0 j hj idx hidx; unfold updAddST4K2; split_ifs <;> omega
    · have h := e1 j hj idx hidx; unfold updAddST4K2; split_ifs <;> omega
  · dsimp only [Bool.casesOn]; simp only [sST4_eq]
    have hjEq : j18At13 a false false i = j18At13 a true false i := Nat.beq_eq.mp hbeq
    refine ⟨updAddST4K2 Fc (j18At13 a false false i) (df8At13 i) (u5Pack13 i), G0, G1,
      insST4K2_isST4Of8 hsc (u5Pack13 i) (j18At13_lt_four a false false i) hdf8, hs0, hs1,
      fun j hj idx hidx => ?_, fun j hj idx hidx => ?_⟩
    · have h := e0 j hj idx hidx; unfold updAddST4K2; split_ifs <;> omega
    · have h := e1 j hj idx hidx; rw [← hjEq]; unfold updAddST4K2; split_ifs <;> omega

theorem initTreeT3D13_sound (a : Nat) :
    ∀ (d b : Nat) {F0 F1 : Nat → Nat → Nat} {cur : ST4T3},
      b + 2 ^ d ≤ 8192 →
      IsST4T3Sum8 F0 F1 cur →
      IsST4T3Sum8
        (fun j idx => F0 j idx + initBktPack5Sub62 a false b (2 ^ d) j idx)
        (fun j idx => F1 j idx + initBktPack5Sub62 a true b (2 ^ d) j idx)
        (initTreeT3D13 (bNT11 (jPack4Leaf a) 0 1024)
          (buildNT63 samplePackLeafK2Pure d b (2 ^ d / 2))
          (buildNT63 wgtLeaf5Sub62Pure d b (2 ^ d / 2))
          cur)
  | 0, b, F0, F1, cur, hb, hcur => by
      rw [show (2 ^ 0 / 2 : Nat) = 0 from rfl, buildNT63_zero, buildNT63_zero]
      dsimp only [initTreeT3D13]
      have h0 := initLeafT3Pack5_sound a (by omega : b < 8192) hcur
      refine h0.congr (fun j _ idx _ => ?_) (fun j _ idx _ => ?_) <;> {
        simp only [updAddST4K2, initBktPack5Sub62, pow_zero, Finset.range_one, Finset.sum_singleton,
            add_zero]
        split_ifs <;> omega
      }
  | d + 1, b, F0, F1, cur, hb, hcur => by
      have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
      rw [hp, buildNT63_succ samplePackLeafK2Pure d, buildNT63_succ wgtLeaf5Sub62Pure d]
      dsimp only [initTreeT3D13]; rw [sST4T3_eq]
      have hL := initTreeT3D13_sound a d b (by rw [Nat.pow_succ] at hb; omega) hcur
      have hR := initTreeT3D13_sound a d (b + 2 ^ d) (by rw [Nat.pow_succ] at hb; omega) hL
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; ring
      refine hR.congr (fun j _ idx _ => ?_) (fun j _ idx _ => ?_) <;> {
        unfold initBktPack5Sub62; rw [hpow, Finset.sum_range_add, add_assoc]
        exact congrArg (_ + ·) (congrArg (_ + ·)
          (Finset.sum_congr rfl fun k _ => by rw [Nat.add_assoc]))
      }

theorem initTreeP2D13_isST4P2Pack5 (a : Nat) :
    IsST4P2Pack5Sub62 a 0
      (initTreeP2D13 (bNT11 (jPack4Leaf a) 0 1024) buildSamplePackK2NT buildWgt5Sub62NT) := by
  have hInit := initTreeT3D13_sound a 13 0 (by norm_num) emptyST4T3K2F_isST4T3Sum8
  rw [show (2 ^ 13 / 2 : Nat) = 4096 by norm_num, buildSamplePackK2NT_def,
      buildWgt5Sub62NT_def] at hInit
  unfold initTreeP2D13
  rcases hT : initTreeT3D13 (bNT11 (jPack4Leaf a) 0 1024)
      buildSamplePackK2NT buildWgt5Sub62NT emptyST4T3K2F with ⟨sc, s0, s1⟩
  rw [hT] at hInit
  dsimp only
  simp only [sST4_eq]
  rcases hInit with ⟨Fc, G0, G1, hsc, hs0, hs1, e0, e1⟩
  have hn13 : (2 ^ 13 : Nat) = nSamples13 := by
    rw [nSamples13_eq]
    norm_num
  have hCong (r : Bool) (j idx : Nat) :
      0 + initBktPack5Sub62 a r 0 (2 ^ 13) j idx = sweepBktPack5Sub62 a r 0 j idx := by
    rw [zero_add, hn13]
    unfold initBktPack5Sub62 sweepBktPack5Sub62
    exact Finset.sum_congr rfl fun k _ => by rw [zero_add, decide_eq_false (Nat.not_lt_zero k)]
  exact ⟨((addST4K2_isST4Of8 hsc hs0).congr e0).congr (fun j _ idx _ => hCong false j idx),
         ((addST4K2_isST4Of8 hsc hs1).congr e1).congr (fun j _ idx _ => hCong true j idx)⟩
theorem advOneST4Pack5_sound (jOld jNew : Bool → Nat → Nat) (r01 : Bool)
    (hOld4 : ∀ i, jOld r01 i < 4) (hNew4 : ∀ i, jNew r01 i < 4) {p : Nat} (hp : p < 8192)
    {s : ST4} (hs : IsST4Of8 (transBktPack5Sub62 jOld jNew r01 p) s) :
    IsST4Of8 (transBktPack5Sub62 jOld jNew r01 (p + 1))
      (advOneST4K2 (jOld r01 p) (jNew r01 p) (df8At13 p) (u5Pack13 p) s) := by
  unfold advOneST4K2
  have hStep {i : Nat} (hne : i ≠ p) :
      (if i < p then jNew r01 i else jOld r01 i) = if i < p +
          1 then jNew r01 i else jOld r01 i := by
    by_cases hlt : i < p <;> simp [hlt, show (i < p + 1) ↔ i < p by omega]
  by_cases hjEq : jOld r01 p = jNew r01 p
  · rw [Nat.beq_eq.mpr hjEq]
    dsimp only [Bool.casesOn]
    refine hs.congr fun j _ idx _ => Finset.sum_congr rfl fun i _ => ?_
    by_cases hip : i = p
    · subst hip
      rw [_root_.ite_eq_right (Nat.lt_irrefl i), _root_.ite_eq_left (Nat.lt_succ_self i), hjEq]
    · rw [hStep hip]
  · rw [Bool.eq_false_iff.mpr fun hb => hjEq (Nat.beq_eq.mp hb)]
    dsimp only [Bool.casesOn]
    rw [sST4_eq]
    have hmem : p ∈ Finset.range nSamples13 :=
        Finset.mem_range.mpr (by rw [nSamples13_eq]; exact hp)
    have hdw_le : u5Pack13 p ≤ transBktPack5Sub62 jOld jNew r01 p (jOld r01 p) (df8At13 p) := by
      have hle :=
          Finset.single_le_sum (f := fun i => if (if i < p then jNew r01 i else jOld r01 i) =
          jOld r01 p ∧
        df8At13 i = df8At13 p then u5Pack13 i else 0) (fun _ _ => Nat.zero_le _) hmem
      simpa only [transBktPack5Sub62, _root_.ite_eq_right (Nat.lt_irrefl p), and_self,
          ↓reduceIte] using hle
    refine (insST4K2_isST4Of8 (decST4K2_isST4Of8 hs (u5Pack13 p) (hOld4 p)
        (df8At13_lt_256 p) hdw_le)
      (u5Pack13 p) (hNew4 p) (df8At13_lt_256 p)).congr fun j _ idx _ => ?_
    simp only [updAddST4K2, updSubST4K2, transBktPack5Sub62]
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem,
        Finset.sum_congr rfl (fun x hx => by rw [hStep (Finset.mem_erase.mp hx).1]),
        _root_.ite_eq_right (Nat.lt_irrefl p), _root_.ite_eq_left (Nat.lt_succ_self p)]
    exact updAdd_updSub_bkt hjEq
attribute [local irreducible] advOneST4K2 initLeafT3K2

theorem advLeafP2Pack5_sound (a : Nat) {p : Nat} (hp : p < 8192) {cur : ST4P2}
    (hcur : IsST4P2Pack5TransSub62 (fun r i => j18At13 a r false i)
    (fun r i => j18At13 a r true i) p cur) : IsST4P2Pack5TransSub62 (fun r i => j18At13 a r false i)
    (fun r i => j18At13 a r true i) (p + 1) (advLeafP2K2 (bNT11 (jPack4Leaf a) 0 1024)
    (samplePackLeafK2Pure p) (wgtLeaf5Sub62Pure p) cur) := by
  rcases cur with ⟨s0, s1⟩
  rcases hcur with ⟨hs0, hs1⟩
  rw [samplePackLeafK2Pure_eq_pack13 hp, wgtLeaf5Sub62Pure_eq_pack13 hp, advLeafP2K2_eq];
  have hd11 := d11At13_lt_2048 p
  have hm256 : (df8At13 p + 256 * d11At13 p) % 256 = df8At13 p := by have := df8At13_lt_256 p; omega
  have hd256 : (df8At13 p + 256 * d11At13 p) / 256 = d11At13 p := by have := df8At13_lt_256 p; omega
  rw [hm256, hd256, get_bNT11 (jPack4Leaf a) hd11];
  obtain ⟨u00, u10, u01, u11⟩ := jPack4Leaf_unpack_at13 a p; rw [u00, u10, u01, u11]
  exact ⟨advOneST4Pack5_sound (fun r i => j18At13 a r false i) (fun r i => j18At13 a r true i)
      false (fun i => j18At13_lt_four a false false i)
      (fun i => j18At13_lt_four a false true i) hp hs0,
    advOneST4Pack5_sound (fun r i => j18At13 a r false i) (fun r i => j18At13 a r true i)
      true (fun i => j18At13_lt_four a true false i)
      (fun i => j18At13_lt_four a true true i) hp hs1⟩

theorem advSubD13_trans_sound (a : Nat) :
    ∀ (d b : Nat) {cur : ST4P2},
      b + 2 ^ d ≤ 8192 →
      IsST4P2Pack5TransSub62
        (fun r i => j18At13 a r false i) (fun r i => j18At13 a r true i) b cur →
      IsST4P2Pack5TransSub62
        (fun r i => j18At13 a r false i) (fun r i => j18At13 a r true i) (b + 2 ^ d)
        (advSubD13 (bNT11 (jPack4Leaf a) 0 1024)
          (buildNT63 samplePackLeafK2Pure d b (2 ^ d / 2))
          (buildNT63 wgtLeaf5Sub62Pure d b (2 ^ d / 2))
          cur)
  | 0, b, cur, hb, hcur => by
      rw [show (2 ^ 0 / 2 : Nat) = 0 from rfl, buildNT63_zero, buildNT63_zero]
      dsimp only [advSubD13]
      exact advLeafP2Pack5_sound a (by omega) hcur
  | d + 1, b, cur, hb, hcur => by
      have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; have := Nat.two_pow_pos d; omega
      rw [hp, buildNT63_succ samplePackLeafK2Pure d, buildNT63_succ wgtLeaf5Sub62Pure d]
      dsimp only [advSubD13]; rw [sST4P2_eq]
      have hL := advSubD13_trans_sound a d b (by rw [Nat.pow_succ] at hb; omega) hcur
      have hR := advSubD13_trans_sound a d (b + 2 ^ d) (by rw [Nat.pow_succ] at hb; omega) hL
      rwa [show b + 2 ^ (d + 1) = b + 2 ^ d + 2 ^ d by rw [Nat.pow_succ]; ring]

theorem advSubD13_sound (a d b : Nat) {cur : ST4P2} (hb : b + 2 ^ d ≤ 8192)
    (hcur : IsST4P2Pack5Sub62 a b cur) : IsST4P2Pack5Sub62 a (b + 2 ^ d)
    (advSubD13 (bNT11 (jPack4Leaf a) 0 1024) (buildNT63 samplePackLeafK2Pure d b (2 ^ d / 2))
    (buildNT63 wgtLeaf5Sub62Pure d b (2 ^ d / 2)) cur) := by
  have hT : IsST4P2Pack5TransSub62
      (fun r i => j18At13 a r false i) (fun r i => j18At13 a r true i) b cur :=
    hcur.congr (fun j _ idx _ => by rw [sweepBktPack5Sub62_eq_trans])
               (fun j _ idx _ => by rw [sweepBktPack5Sub62_eq_trans])
  have hRes := advSubD13_trans_sound a d b hb hT
  exact hRes.congr (fun j _ idx _ => by rw [← sweepBktPack5Sub62_eq_trans])
                   (fun j _ idx _ => by rw [← sweepBktPack5Sub62_eq_trans])

attribute [local irreducible]
  initTreeP2D13 initTreeT3D13 advSubD13
  transBktPack5Sub62 initBktPack5Sub62 sweepBktPack5Sub62

-- ============================================================================
-- Section 3. Fused 5-Lane Evaluator (`EE + NN`, `2` Polarities Simultaneously)
-- ============================================================================

def sufRawM256 (st : SumTree) (M : Nat) : Nat := Bool.casesOn (Nat.beq M 256) (sufST128F st M 0) 0
def lane512Lo (v s q : Nat) : Nat :=
    Bool.casesOn (Nat.beq (Nat.mod q 2) 0) (Nat.add (Nat.mul v (Nat.div q 2)) s)
    (Nat.mul v (Nat.div q 2))
def lane512Hi (v s q : Nat) : Nat :=
    Bool.casesOn (Nat.beq (Nat.mod q 2) 0) (Nat.mul v (Nat.add (Nat.div q 2) 1))
    (Nat.add (Nat.mul v (Nat.div q 2)) s)
def checkPairNum63 (eF eT m g hi lo s0Sq : Nat) : Bool :=
    fN63 (Bool.casesOn (Nat.ble eF eT) eT eF) fun eMin =>
    fN63 (Bool.casesOn (Nat.ble eF eT) eF eT) fun eMax => fN63 (Nat.mul g eMin) fun geMin =>
    Bool.casesOn (Nat.ble lo geMin) false (fN63 (Nat.add geMin hi) fun u =>
    Bool.casesOn (Nat.ble s0Sq (Nat.mul (Nat.mul u u) m)) false (fN63 (Nat.sub (Nat.mul g eMax) lo)
    fun l => Nat.ble (Nat.mul (Nat.mul l l) m) s0Sq))
theorem checkPairNum63_sound {eF eT m g hi lo s0Sq : Nat}
    (hc : checkPairNum63 eF eT m g hi lo s0Sq = true)
    (pol : Bool) : checkNum63 (if pol then eT else eF) m g hi lo s0Sq = true := by
  obtain ⟨eMin, eMax, ⟨hMin, hMax⟩, hOrd⟩ :
      ∃ eMin eMax : Nat,
        (Bool.casesOn (Nat.ble eF eT) eT eF = eMin ∧
         Bool.casesOn (Nat.ble eF eT) eF eT = eMax) ∧
        (eMin ≤ eF ∧ eF ≤ eMax ∧ eMin ≤ eT ∧ eT ≤ eMax) := by
    cases hb : Nat.ble eF eT
    · have hgt : eT < eF := by
        by_contra hle; exact Bool.noConfusion (hb.symm.trans (Nat.ble_eq.mpr (by omega)))
      exact ⟨eT, eF, ⟨rfl, rfl⟩, by omega⟩
    · have hle := Nat.ble_eq.mp hb
      exact ⟨eF, eT, ⟨rfl, rfl⟩, by omega⟩
  unfold checkPairNum63 at hc; rw [hMin, hMax] at hc;
  simp only [fN63_eq, nat_mul_def, nat_add_def, nat_sub_def] at hc
  cases hlo : Nat.ble lo (g * eMin)
  · rw [hlo] at hc; exact Bool.noConfusion hc
  · rw [hlo] at hc; dsimp only [Bool.casesOn] at hc
    cases hu : Nat.ble s0Sq (((g * eMin + hi) * (g * eMin + hi)) * m)
    · rw [hu] at hc; exact Bool.noConfusion hc
    · rw [hu] at hc; dsimp only [Bool.casesOn] at hc
      have hlo0 := Nat.ble_eq.mp hlo; have hu0 := Nat.ble_eq.mp hu; have hl0 := Nat.ble_eq.mp hc
      set E := if pol then eT else eF
      have hE : eMin ≤ E ∧ E ≤ eMax := by cases pol <;> simp [E, hOrd]
      have hgMin : g * eMin ≤ g * E := Nat.mul_le_mul_left g hE.1;
      have hgMax : g * E ≤ g * eMax := Nat.mul_le_mul_left g hE.2;
      have hloE : lo ≤ g * E := le_trans hlo0 hgMin
      have huE : s0Sq ≤ ((g * E + hi) * (g * E + hi)) * m := by
        have h1 : g * eMin + hi ≤ g * E + hi := by omega
        exact le_trans hu0 (Nat.mul_le_mul_right m (Nat.mul_le_mul h1 h1))
      have hlE : ((g * E - lo) * (g * E - lo)) * m ≤ s0Sq := by
        have h1 : g * E - lo ≤ g * eMax - lo := by omega
        exact le_trans (Nat.mul_le_mul_right m (Nat.mul_le_mul h1 h1)) hl0
      unfold checkNum63; simp only [fN63_eq, nat_mul_def, nat_add_def, nat_sub_def];
      rw [Nat.ble_eq.mpr hloE, Nat.ble_eq.mpr huE, Nat.ble_eq.mpr hlE]
inductive TripleNat : Type
  | mk : Nat → Nat → Nat → TripleNat

@[inline] def sTriple3 {α : Type} (v : TripleNat) (k : TripleNat → α) : α :=
    TripleNat.casesOn v fun a b c => k (.mk a b c)
theorem sTriple3_eq {α : Type} (v : TripleNat) (k : TripleNat → α) : sTriple3 v k = k v := by
  cases v; rfl

def unpkStVal3 (isNN : Bool) (t : SumTree) : TripleNat := fN63 (stVal63 t) fun s =>
    Bool.casesOn isNN (fN63 (Nat.mod s 4096) fun u0 =>
    fN63 (Nat.mod (Nat.div s 4096) 4096) fun u1 => fN63 (Nat.div s 281474976710656) fun cAll =>
    fN63 (Nat.sub (Nat.mul 82 cAll) (Nat.mul 2 (Nat.add u0 u1))) fun v0 =>
    fN63 (Nat.mul 2 u0) fun vB0 => fN63 (Nat.mul 2 u1) fun vB1 =>
    .mk v0 vB0 vB1) (fN63 (Nat.div s 16777216) fun r2 => fN63 (Nat.mod r2 4096) fun u2 =>
    fN63 (Nat.mod (Nat.div r2 4096) 4096) fun u3 => fN63 (Nat.div r2 16777216) fun cAll =>
    fN63 (Nat.mul 80 cAll) fun v0 => fN63 (Nat.mul 4 u2) fun vB0 => fN63 (Nat.mul 4 u3) fun vB1 =>
    .mk v0 vB0 vB1)
inductive PairNat : Type
  | mk : Nat → Nat → PairNat

def addPairNat (x y : PairNat) : PairNat := PairNat.casesOn x fun xF xT =>
    PairNat.casesOn y fun yF yT => fN63 (Nat.add xF yF) fun sF => fN63 (Nat.add xT yT) fun sT =>
    .mk sF sT
def checkPairOfPairNat (p : PairNat) (m g hi lo s0Sq : Nat) : Bool := PairNat.casesOn p fun eF eT =>
    checkPairNum63 eF eT m g hi lo s0Sq
def finishLane5PairP (v0 vB0 vB1 s0 sB0 sB1 q : Nat) : PairNat := fN63 (Nat.div q 2) fun qHalf =>
    fN63 (Nat.add (Nat.add (Nat.mul v0 q) s0) (Nat.add (Nat.mul vB0 qHalf)
    (Nat.mul vB1 qHalf))) fun base =>
    Bool.casesOn (Nat.beq (Nat.mod q 2) 0) (fN63 (Nat.add base (Nat.add vB0 sB1)) fun eF =>
    fN63 (Nat.add base (Nat.add sB0 vB1)) fun eT =>
    .mk eF eT) (fN63 (Nat.add base sB0) fun eF => fN63 (Nat.add base sB1) fun eT => .mk eF eT)
def evalLane5PairP (isNN : Bool) (v : TripleNat) (t : SumTree) (q M : Nat) : PairNat :=
    TripleNat.casesOn v fun v0 vB0 vB1 =>
    Bool.casesOn (Nat.beq M 256)
    (fN63 (sufST128F t M 0) fun s => Bool.casesOn isNN (fN63 (Nat.mod s 4096) fun u0 =>
    fN63 (Nat.mod (Nat.div s 4096) 4096) fun u1 => fN63 (Nat.div s 281474976710656) fun cAll =>
    finishLane5PairP v0 vB0 vB1 (Nat.sub (Nat.mul 82 cAll) (Nat.mul 2 (Nat.add u0 u1)))
    (Nat.mul 2 u0) (Nat.mul 2 u1) q) (fN63 (Nat.div s 16777216) fun r2 =>
    fN63 (Nat.mod r2 4096) fun u2 => fN63 (Nat.mod (Nat.div r2 4096) 4096) fun u3 =>
    fN63 (Nat.div r2 16777216) fun cAll =>
    finishLane5PairP v0 vB0 vB1 (Nat.mul 80 cAll) (Nat.mul 4 u2) (Nat.mul 4 u3) q))
    (finishLane5PairP v0 vB0 vB1 0 0 0 q)
def evalQuad5PairP (isNN : Bool) (va : TripleNat) (ta : SumTree) (vb : TripleNat) (tb : SumTree)
    (vc : TripleNat) (tc : SumTree) (vd : TripleNat) (td : SumTree)
    (q0 M0 q1 M1 q2 M2 q3 M3 m g hi lo s0Sq : Nat) : Bool :=
    checkPairOfPairNat (addPairNat (addPairNat (evalLane5PairP isNN va ta q0 M0)
    (evalLane5PairP isNN vb tb q1 M1)) (addPairNat (evalLane5PairP isNN vc tc q2 M2)
    (evalLane5PairP isNN vd td q3 M3))) m g hi lo s0Sq
def evalCheckPtFastSub62 (isNN : Bool) (va : TripleNat) (ta : SumTree) (vb : TripleNat)
    (tb : SumTree) (vc : TripleNat) (tc : SumTree) (vd : TripleNat) (td : SumTree)
    (m q0 M0 q1 M1 q2 M2 q3 M3 g hi lo s0Sq : Nat) : Bool :=
    Bool.casesOn (Nat.beq (Nat.mod m 8) 7) (Bool.casesOn (Nat.beq (Nat.mod m 32) 28)
    (evalQuad5PairP isNN va ta vb tb vc tc vd td q0 M0 q1 M1 q2 M2 q3 M3 m g hi lo s0Sq) true) true
def scanZLLFastSub62 (isNN : Bool)
    (va : TripleNat) (ta : SumTree)
    (vb : TripleNat) (tb : SumTree)
    (vc : TripleNat) (tc : SumTree)
    (vd : TripleNat) (td : SumTree)
    (qt g hi lo s0Sq : Nat) : ZLeafL → Bool
  | .nil => true
  | .cons m0 q0 M0 q1 M1 q2 M2 q3 M3 tl =>
      andB63
        (evalCheckPtFastSub62 isNN va ta vb tb vc tc vd td
          (Nat.add m0 qt) q0 M0 q1 M1 q2 M2 q3 M3 g hi lo s0Sq)
        (scanZLLFastSub62 isNN va ta vb tb vc tc vd td
          qt g hi lo s0Sq tl)

def checkHalfZLLFastSub62 (isNN : Bool) (zl : ZLeafL) (va : TripleNat) (ta : SumTree)
    (vb : TripleNat) (tb : SumTree) (vc : TripleNat) (tc : SumTree) (vd : TripleNat) (td : SumTree)
    (t11 step2 g hi lo s0Sq : Nat) : Bool :=
    Bool.casesOn (Nat.beq (Nat.mod t11 step2) 0) true (scanZLLFastSub62 isNN va ta vb tb vc tc vd td
    (Nat.div t11 step2) g hi lo s0Sq zl)
def checkAtT11ZLLFastSub62 (isNN : Bool) (zo : ZOct10L) (t11 : Nat) (st4 : ST4)
    (g hi lo s0Sq : Nat) : Bool := ST4.casesOn st4 fun _ ta tb tc td =>
    sTriple3 (unpkStVal3 isNN ta) fun va => sTriple3 (unpkStVal3 isNN tb) fun vb =>
    sTriple3 (unpkStVal3 isNN tc) fun vc => sTriple3 (unpkStVal3 isNN td) fun vd =>
    ZOct10L.casesOn zo fun l4lo l4hi l5lo l5hi l6lo l6hi l7lo l7hi l8lo l8hi =>
    andB63 (checkHalfZLLFastSub62 isNN l4lo va ta vb tb vc tc vd td t11 512 g hi lo s0Sq)
    (andB63 (checkHalfZLLFastSub62 isNN l4hi va ta vb tb vc tc vd td t11 256 g hi lo s0Sq)
    (andB63 (checkHalfZLLFastSub62 isNN l5lo va ta vb tb vc tc vd td t11 128 g hi lo s0Sq)
    (andB63 (checkHalfZLLFastSub62 isNN l5hi va ta vb tb vc tc vd td t11 64 g hi lo s0Sq)
    (andB63 (checkHalfZLLFastSub62 isNN l6lo va ta vb tb vc tc vd td t11 32 g hi lo s0Sq)
    (andB63 (checkHalfZLLFastSub62 isNN l6hi va ta vb tb vc tc vd td t11 16 g hi lo s0Sq)
    (andB63 (checkHalfZLLFastSub62 isNN l7lo va ta vb tb vc tc vd td t11 8 g hi lo s0Sq)
    (andB63 (checkHalfZLLFastSub62 isNN l7hi va ta vb tb vc tc vd td t11 4 g hi lo s0Sq)
    (andB63 (checkHalfZLLFastSub62 isNN l8lo va ta vb tb vc tc vd td t11 2 g hi lo s0Sq)
    (checkHalfZLLFastSub62 isNN l8hi va ta vb tb vc tc vd td t11 1 g hi lo s0Sq)))))))))
def checkPtSkipOtherFastSub62 (cb : ChW11) (isNN : Bool) (lo6NT : NatTree) (a r6 : Nat) (st4 : ST4)
    (g hi lo s0Sq d2 : Nat) : Bool :=
    Bool.casesOn (Nat.beq (Nat.mod d2 8) 7) (sParts (evenOctPartsW11 isNN d2) fun p1 t10 k =>
    fN63 (Nat.add (Nat.mul (Nat.mod p1 2) 1024) t10) fun t11 =>
    Bool.casesOn (andB63 (Nat.beq (Nat.div t11 64) a)
    (Nat.beq (Nat.mod t11 64) r6)) true (fN63 (maxDistW11 isNN d2) fun m =>
    fN63 (Nat.div p1 2) fun i7 => fN63 (Nat.pow 2 k) fun p2k => fN63 (Nat.mul 4 i7) fun b4 =>
    fN63 (chFnFast cb (Nat.div (getNT256F lo6NT b4) p2k)) fun z0 =>
    fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 1)) p2k)) fun z1 =>
    fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 2)) p2k)) fun z2 =>
    fN63 (chFnFast cb (Nat.div (getNT256F lo6NT (Nat.add b4 3)) p2k)) fun z3 =>
    ST4.casesOn st4 fun _ ta tb tc td => sTriple3 (unpkStVal3 isNN ta) fun va =>
    sTriple3 (unpkStVal3 isNN tb) fun vb => sTriple3 (unpkStVal3 isNN tc) fun vc =>
    sTriple3 (unpkStVal3 isNN td) fun vd =>
    evalQuad5PairP isNN va ta vb tb vc tc vd td (Nat.div z0 256) (Nat.sub 256 (Nat.mod z0 256))
    (Nat.div z1 256) (Nat.sub 256 (Nat.mod z1 256)) (Nat.div z2 256) (Nat.sub 256 (Nat.mod z2 256))
    (Nat.div z3 256) (Nat.sub 256 (Nat.mod z3 256)) m g hi lo s0Sq)) true
def checkSmAtARFastSub62 (cb : ChW11) (isNN : Bool) (lo6NT : NatTree) (a r6 : Nat) (st4 : ST4)
    (g hi lo s0Sq : Nat) : Bool :=
    andB63 (Bool.casesOn (andB63 (Nat.beq r6 0)
    (Nat.beq (Nat.mod a 16) 0)) true (allCnt63 (checkPtSkipOtherFastSub62 cb isNN lo6NT a 0 st4 g hi
    lo s0Sq) 256 0)) (Bool.casesOn (Nat.beq (Nat.mod a 8) 0) true (allList63 (fun d2 =>
    Bool.casesOn (Nat.beq (Nat.mod d2 64) r6) true (checkPtSkipOtherFastSub62 cb isNN lo6NT a r6 st4
    g hi lo s0Sq d2)) tail16List))
def sweepR6TreeBothSub62 (zoEE zoNN : ZOct10L) (lo6NT : NatTree)
    (gEE hiEE loEE gNN hiNN loNN s0Sq a : Nat) (jpNT : NatTree) :
    Nat → Nat → NatTree → NatTree → ST4P2 → ST4P2B
  | 0, r6, spSub, wgtSub, cur =>
      sST4 (selST4P2 (r01OfR6 r6) cur) fun st4 =>
      fN63 (Nat.add (Nat.mul 64 a) r6) fun t11 =>
      Bool.casesOn (checkAtT11ZLLFastSub62 false zoEE t11 st4 gEE hiEE loEE s0Sq) (.mk false cur)
        (Bool.casesOn (checkSmAtARFastSub62 .ee false lo6NT a r6 st4 gEE hiEE loEE s0Sq)
            (.mk false cur)
          (Bool.casesOn (checkAtT11ZLLFastSub62 true zoNN t11 st4 gNN hiNN loNN s0Sq)
              (.mk false cur)
            (Bool.casesOn (checkSmAtARFastSub62 .nn true lo6NT a r6 st4 gNN hiNN loNN s0Sq)
                (.mk false cur)
              (sST4P2 (advSubD13 jpNT spSub wgtSub cur) fun nxt => .mk true nxt))))
  | d + 1, b, spSub, wgtSub, cur =>
      NatTree.casesOn spSub (fun _ => .mk false cur) fun spL spR =>
      NatTree.casesOn wgtSub (fun _ => .mk false cur) fun wL wR =>
      sST4P2B (sweepR6TreeBothSub62 zoEE zoNN lo6NT gEE hiEE loEE gNN hiNN loNN s0Sq a jpNT d b spL
          wL cur) fun ok1 mid =>
      Bool.casesOn ok1 (.mk false mid)
        (fN63 (Nat.add b (Nat.pow 2 d)) fun b2 =>
         sweepR6TreeBothSub62 zoEE zoNN lo6NT gEE hiEE loEE gNN hiNN loNN s0Sq a jpNT d b2 spR wR
             mid)

@[inline] def sZOct10L (zo : ZOct10L) (k : ZOct10L → Bool) : Bool :=
    ZOct10L.casesOn zo fun l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 => k (.mk l0 l1 l2 l3 l4 l5 l6 l7 l8 l9)
theorem sZOct10L_eq (zo : ZOct10L) (k : ZOct10L → Bool) : sZOct10L zo k = k zo := by
  cases zo; rfl

def runOneABothSub62 (zoEE zoNN : ZOct10L) (lo6NT spNT wgtNT : NatTree)
    (gEE hiEE loEE gNN hiNN loNN s0Sq a : Nat) : Bool := sNT63 (buildJPackNT a) fun jp0NT =>
    sST4P2 (initTreeP2D13 jp0NT spNT wgtNT) fun initP2 =>
    ST4P2B.casesOn (sweepR6TreeBothSub62 zoEE zoNN lo6NT gEE hiEE loEE gNN hiNN loNN s0Sq a jp0NT 6
    0 spNT wgtNT initP2) fun ok0 _ => ok0
def checkOneABothSub62 (a : Nat) : Bool :=
  sNT63 (bNT9 word512DualLegLo6T 0 256) fun lo6NT =>
  fN63 (Nat.mul 64000 (sub62Mc false)) fun gEE =>
  fN63 (Nat.mul (Nat.mul (sub62HiNum false) 5714023029) 167340) fun hiEE =>
  fN63 (Nat.mul (Nat.mul (sub62LoNum false) 5714023029) 167340) fun loEE =>
  fN63 (Nat.mul 64000 (sub62Mc true)) fun gNN =>
  fN63 (Nat.mul (Nat.mul (sub62HiNum true) 5714023029) 167340) fun hiNN =>
  fN63 (Nat.mul (Nat.mul (sub62LoNum true) 5714023029) 167340) fun loNN =>
  fN63 (Nat.pow (Nat.mul (Nat.mul (Nat.mul 1000 5714023029) 34359738368) 167340) 2) fun s0Sq =>
  sZOct10L (buildZOct10LK2 .ee) fun zoEE =>
  sZOct10L (buildZOct10LK2 .nn) fun zoNN =>
  sNT63 spNTFastK2 fun spNT =>
  sNT63 wgt5NTFastSub62 fun wgtNT =>
  runOneABothSub62 zoEE zoNN lo6NT spNT wgtNT gEE hiEE loEE gNN hiNN loNN s0Sq a

-- ============================================================================
-- Section 4. 5-Lane Unpack Projection & Evaluator Soundness
-- ============================================================================

def projUnpkST5 (c : Lane5) : SumTree → SumTree
  | .leaf v => .leaf (unpk5 c v)
  | .node _ l r =>
      let pl := projUnpkST5 c l; let pr := projUnpkST5 c r
      .node (stVal pl + stVal pr) pl pr

theorem stVal_projUnpkST5_node (c : Lane5) (s : Nat) (l r : SumTree) :
    stVal (projUnpkST5 c (.node s l r)) =
      stVal (projUnpkST5 c l) + stVal (projUnpkST5 c r) := rfl

theorem projUnpkST5_spec {f0 f1 f2 f3 f4 : Nat → Nat} {d base : Nat} {st : SumTree}
    (hst : IsTreeOf (fun i => pack5Nat (f0 i) (f1 i) (f2 i) (f3 i) (f4 i)) d base st)
    (h0 : (∑ i ∈ Finset.range (2 ^ d), f0 (base + i)) < 4096)
    (h1 : (∑ i ∈ Finset.range (2 ^ d), f1 (base + i)) < 4096)
    (h2 : (∑ i ∈ Finset.range (2 ^ d), f2 (base + i)) < 4096)
    (h3 : (∑ i ∈ Finset.range (2 ^ d), f3 (base + i)) < 4096) :
    (∀ c, IsTreeOf (chFn5 c f0 f1 f2 f3 f4) d base (projUnpkST5 c st)) ∧
    (∀ c, stVal (projUnpkST5 c st) = ∑ i ∈ Finset.range (2 ^ d), chFn5 c f0 f1 f2 f3 f4 (base +
    i)) ∧ stVal st = pack5Nat (stVal (projUnpkST5 .l0 st)) (stVal (projUnpkST5 .l1 st))
    (stVal (projUnpkST5 .l2 st)) (stVal (projUnpkST5 .l3 st)) (stVal (projUnpkST5 .l4 st)) ∧
    (∀ h M acc0 acc1 acc2 acc3 acc4, sufST h st M (pack5Nat acc0 acc1 acc2 acc3 acc4) =
    pack5Nat (sufST h (projUnpkST5 .l0 st) M acc0) (sufST h (projUnpkST5 .l1 st) M acc1)
    (sufST h (projUnpkST5 .l2 st) M acc2) (sufST h (projUnpkST5 .l3 st) M acc3)
    (sufST h (projUnpkST5 .l4 st) M acc4)) := by
  induction hst with
  | leaf base =>
      simp only [pow_zero, Finset.range_one, Finset.sum_singleton, add_zero] at h0 h1 h2 h3 ⊢
      have hu : ∀ c, unpk5 c (pack5Nat (f0 base) (f1 base) (f2 base) (f3 base) (f4 base)) =
          chFn5 c f0 f1 f2 f3 f4 base := fun c => by
        rw [unpk5_pack5Nat c (f4 base) h0 h1 h2 h3]; cases c <;> rfl
      refine ⟨fun c => ?_, fun c => ?_, ?_, fun h M acc0 acc1 acc2 acc3 acc4 => ?_⟩
      · dsimp only [projUnpkST5]; rw [hu c]; exact .leaf base
      · dsimp only [projUnpkST5, stVal]; exact hu c
      · dsimp only [projUnpkST5, stVal]; rw [hu .l0, hu .l1, hu .l2, hu .l3, hu .l4]; rfl
      · dsimp only [projUnpkST5, sufST];
        simp only [nat_add_def, hu .l0, hu .l1, hu .l2, hu .l3, hu .l4];
        exact pack5Nat_add acc0 acc1 acc2 acc3 acc4 (f0 base) (f1 base) (f2 base) (f3 base)
            (f4 base)
  | @node d base s l r hs hl hr ihl ihr =>
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; ring
      rw [hpow, Finset.sum_range_add] at h0 h1 h2 h3
      have hAssoc : ∀ g : Nat → Nat,
          (∑ i ∈ Finset.range (2 ^ d), g (base + 2 ^ d + i)) =
          (∑ i ∈ Finset.range (2 ^ d), g (base + (2 ^ d + i))) :=
        fun g => Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc]
      obtain ⟨tl, vcl, vpl, sufl⟩ := ihl (by omega) (by omega) (by omega) (by omega)
      obtain ⟨tr, vcr, vpr, sufr⟩ := ihr
        (by rw [hAssoc]; omega) (by rw [hAssoc]; omega)
        (by rw [hAssoc]; omega) (by rw [hAssoc]; omega)
      refine ⟨fun c => .node rfl (tl c) (tr c), fun c => ?_, ?_, fun h M acc0 acc1 acc2 acc3 acc4 =>
          ?_⟩
      · rw [stVal_projUnpkST5_node, vcl c, vcr c, hpow, Finset.sum_range_add]
        exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc])
      · simp only [stVal_projUnpkST5_node]
        rw [show stVal (.node s l r) = s from rfl, hs, vpl, vpr, pack5Nat_add]
      · dsimp only [projUnpkST5]; unfold sufST
        simp only [nat_add_def, nat_div_def, nat_sub_def, stVal63_eq]
        cases Nat.ble (M + 1) h
        · dsimp only [Bool.casesOn]; exact sufr (h / 2) (M - h) acc0 acc1 acc2 acc3 acc4
        · dsimp only [Bool.casesOn]; rw [vpr, pack5Nat_add];
          exact sufl (h / 2) M (acc0 + stVal (projUnpkST5 .l0 r)) (acc1 + stVal (projUnpkST5 .l1 r))
              (acc2 + stVal (projUnpkST5 .l2 r)) (acc3 + stVal (projUnpkST5 .l3 r))
              (acc4 + stVal (projUnpkST5 .l4 r))
theorem projUnpkST5_unpk {f0 f1 f2 f3 f4 : Nat → Nat} {st : SumTree}
    (hst : IsTreeOf (fun i => pack5Nat (f0 i) (f1 i) (f2 i) (f3 i) (f4 i)) 8 0 st)
    (h0 : (∑ i ∈ Finset.range (2 ^ 8), f0 (0 + i)) < 4096)
    (h1 : (∑ i ∈ Finset.range (2 ^ 8), f1 (0 + i)) < 4096)
    (h2 : (∑ i ∈ Finset.range (2 ^ 8), f2 (0 + i)) < 4096)
    (h3 : (∑ i ∈ Finset.range (2 ^ 8), f3 (0 + i)) < 4096)
    (c : Lane5) : IsTreeOf (chFn5 c f0 f1 f2 f3 f4) 8 0 (projUnpkST5 c st) ∧ unpk5 c (stVal st) =
    stVal (projUnpkST5 c st) ∧ (∀ M, unpk5 c (sufST 128 st M 0) = sufST 128 (projUnpkST5 c st) M 0)
    := by
  obtain ⟨ht, hvc, hvp, hsuf⟩ := projUnpkST5_spec hst h0 h1 h2 h3
  have hv0 : stVal (projUnpkST5 .l0 st) < 4096 := by rw [hvc .l0]; simpa [chFn5, selLane5] using h0
  have hv1 : stVal (projUnpkST5 .l1 st) < 4096 := by rw [hvc .l1]; simpa [chFn5, selLane5] using h1
  have hv2 : stVal (projUnpkST5 .l2 st) < 4096 := by rw [hvc .l2]; simpa [chFn5, selLane5] using h2
  have hv3 : stVal (projUnpkST5 .l3 st) < 4096 := by rw [hvc .l3]; simpa [chFn5, selLane5] using h3
  refine ⟨ht c, ?_, fun M => ?_⟩
  · rw [hvp, unpk5_pack5Nat c _ hv0 hv1 hv2 hv3]; cases c <;> rfl
  · have hz := hsuf 128 M 0 0 0 0 0; rw [pack5Nat_zero] at hz;
    have hs0 := sufST_le_add_stVal (ht .l0).isValid 128 M 0;
    have hs1 := sufST_le_add_stVal (ht .l1).isValid 128 M 0;
    have hs2 := sufST_le_add_stVal (ht .l2).isValid 128 M 0;
    have hs3 := sufST_le_add_stVal (ht .l3).isValid 128 M 0
    rw [hz, unpk5_pack5Nat c _ (by omega) (by omega) (by omega) (by omega)]
    cases c <;> rfl

theorem sumSuf_of_isTreeOf {f : Nat → Nat} {d base : Nat} {st : SumTree} (h : IsTreeOf f d base st)
    (M : Nat) : sumSufST (2 ^ d / 2) base st M = ∑ i ∈ Finset.range (2 ^ d), if M ≤ base +
    i then f (base + i) else 0 := by
  induction h with
  | leaf base => simp [sumSufST]
  | @node d base s l r _ _ _ ihl ihr =>
      have hp2 : 0 < 2 ^ d := Nat.two_pow_pos d
      have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; omega
      have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; ring
      rw [hp]; dsimp only [sumSufST]
      rw [ihl, ihr, h2, Finset.sum_range_add]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => by rw [Nat.add_assoc])

theorem sumAll_eq_sum_of_isTreeOf {f : Nat → Nat} {t : SumTree} (ht : IsTreeOf f 8 0 t) :
    sumAllST t = ∑ idx ∈ Finset.range 256, f idx := by
  have hv := ht.isValid; have hc := IsTreeOf.sumCarry256 ht 256
  have hs := sumAll_add_sumSuf_eq_sumCarry256 hv (base := 0) 256 (by norm_num)
  have hn0 := sumSufST_none hv (base := 0) (K := 256) (by norm_num)
  rw [show (2 ^ 8 / 2 : Nat) = 128 by norm_num] at hc hs hn0
  rw [show 256 / 256 = 1 from rfl, Nat.mul_one, show 256 - 256 % 256 = 256 from rfl,
      hn0, add_zero, hc, show (2 ^ 8 : Nat) = 256 by norm_num] at hs
  refine hs.trans (Finset.sum_congr rfl fun idx hidx => ?_)
  have hlt : idx < 256 := Finset.mem_range.mp hidx
  rw [zero_add, show (256 + idx) / 256 = 1 by omega, Nat.mul_one]

theorem sumCarry256_of_sums {f : Nat → Nat} {v s z : Nat} (hv : v = ∑ idx ∈ Finset.range 256, f idx)
    (hs : s = ∑ idx ∈ Finset.range 256, if 256 - z % 256 ≤ idx then f idx else 0) : v * (z / 256) +
    s = ∑ idx ∈ Finset.range 256, f idx * ((z + idx) / 256) := by
  rw [hv, Finset.sum_mul, hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun idx hidx => ?_
  have hlt : idx < 256 := Finset.mem_range.mp hidx
  have hzDiv : z = 256 * (z / 256) + z % 256 := (Nat.div_add_mod z 256).symm
  have hzMod : z % 256 < 256 := Nat.mod_lt z (by omega)
  by_cases hm : 256 - z % 256 ≤ idx
  · rw [_root_.ite_eq_left hm, show (z + idx) / 256 = z / 256 + 1 by omega, Nat.mul_add,
        Nat.mul_one]
  · rw [_root_.ite_eq_right hm, add_zero, show (z + idx) / 256 = z / 256 by omega]

theorem lane512Lo_Hi_eq {f : Nat → Nat} {v s z : Nat} (hv : v = ∑ idx ∈ Finset.range 256, f idx)
    (hs : v * (z / 256) + s = ∑ idx ∈ Finset.range 256, f idx * ((z + idx) / 256)) :
    lane512Lo v s (z / 256) = (∑ idx ∈ Finset.range 256, f idx * ((z + idx) / 512)) ∧
    lane512Hi v s (z / 256) = (∑ idx ∈ Finset.range 256, f idx * ((z + 256 + idx) / 512)) := by
  unfold lane512Lo lane512Hi; simp only [nat_mod_def, nat_div_def, nat_add_def, nat_mul_def]
  set q := z / 256
  have hzDiv : z = 256 * q + z % 256 := (Nat.div_add_mod z 256).symm
  have hzMod : z % 256 < 256 := Nat.mod_lt z (by omega)
  have hqDiv : q = 2 * (q / 2) + q % 2 := (Nat.div_add_mod q 2).symm
  have hCarry (sh : Nat) (hDiv : ∀ idx < 256, (z + sh + idx) / 512 + q = (z + idx) / 256 + q / 2) :
      (∑ idx ∈ Finset.range 256, f idx * ((z + sh + idx) / 512)) + v * q = (v * q + s) + v * (q / 2)
          := by
    rw [hs, hv, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun idx hidx => by
      rw [← Nat.mul_add, ← Nat.mul_add]
      exact congrArg (f idx * ·) (hDiv idx (Finset.mem_range.mp hidx))
  have hConst (k sh : Nat) (hDiv : ∀ idx < 256, k = (z + sh + idx) / 512) :
      v * k = ∑ idx ∈ Finset.range 256, f idx * ((z + sh + idx) / 512) := by
    rw [hv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun idx hidx =>
        congrArg (f idx * ·) (hDiv idx (Finset.mem_range.mp hidx))
  by_cases hq : q % 2 = 0
  · rw [Nat.beq_eq.mpr hq]
    dsimp only [Bool.casesOn]
    exact ⟨by simpa only [add_zero] using hConst (q / 2) 0 (fun idx hlt => by omega),
      by have := hCarry 256 (fun idx hlt => by omega); omega⟩
  · rw [Bool.eq_false_iff.mpr fun hb => hq (Nat.beq_eq.mp hb)]
    dsimp only [Bool.casesOn]
    exact ⟨by
        have := hCarry 0 (fun idx hlt => by omega)
        simp only [add_zero] at this
        omega,
      hConst (q / 2 + 1) 256 (fun idx hlt => by omega)⟩

theorem sum_sweepBkt5Sub62_le_sum_u5 (c : Lane5) (a : Nat) (r01 : Bool) (p j : Nat) :
    (∑ idx ∈ Finset.range (2 ^ 8), sweepBkt5Sub62 c a r01 p j (0 + idx)) ≤
      ∑ i ∈ Finset.range nSamples13, u5At13 c i := by
  simp only [zero_add, sweepBkt5Sub62]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.add_sum_erase (Finset.range (2 ^ 8)) _ (Finset.mem_range.mpr (df8At13_lt_256 i)),
      Finset.sum_eq_zero (fun x hx => by simp [(Finset.mem_erase.mp hx).1.symm]), add_zero]
  split_ifs <;> omega
theorem sum_sweepBkt5Sub62_lt (a : Nat) (r01 : Bool) (p j : Nat) : (∑ idx ∈ Finset.range (2 ^ 8),
    sweepBkt5Sub62 .l0 a r01 p j (0 + idx)) < 4096 ∧ (∑ idx ∈ Finset.range (2 ^ 8),
    sweepBkt5Sub62 .l1 a r01 p j (0 + idx)) < 4096 ∧ (∑ idx ∈ Finset.range (2 ^ 8),
    sweepBkt5Sub62 .l2 a r01 p j (0 + idx)) < 4096 ∧ (∑ idx ∈ Finset.range (2 ^ 8),
    sweepBkt5Sub62 .l3 a r01 p j (0 + idx)) <
    4096 := by
  obtain ⟨u0, u1, u2, u3⟩ :=
      sum_u5At13_lt_4096; exact ⟨lt_of_le_of_lt (sum_sweepBkt5Sub62_le_sum_u5 .l0 a r01 p j) u0,
      lt_of_le_of_lt (sum_sweepBkt5Sub62_le_sum_u5 .l1 a r01 p j) u1,
      lt_of_le_of_lt (sum_sweepBkt5Sub62_le_sum_u5 .l2 a r01 p j) u2,
      lt_of_le_of_lt (sum_sweepBkt5Sub62_le_sum_u5 .l3 a r01 p j) u3⟩
theorem unpk5_sufRawM256_eq (c : Lane5) {f : Nat → Nat} {st : SumTree}
    (ht : IsTreeOf f 8 0 (projUnpkST5 c st)) (hsuf : ∀ M, unpk5 c (sufST 128 st M 0) =
    sufST 128 (projUnpkST5 c st) M 0) (z : Nat) : unpk5 c (sufRawM256 st (256 - z % 256)) =
    ∑ idx ∈ Finset.range 256, if 256 - z % 256 ≤ idx then f idx else 0 := by
  have hv := ht.isValid
  have hSufSum : ∀ M, sumSufST 128 0 (projUnpkST5 c st) M =
      ∑ idx ∈ Finset.range 256, if M ≤ idx then f idx else 0 := fun M => by
    have hs := sumSuf_of_isTreeOf ht M
    rw [show (2 ^ 8 / 2 : Nat) = 128 by norm_num, show (2 ^ 8 : Nat) = 256 by norm_num] at hs
    exact hs.trans (Finset.sum_congr rfl fun idx _ => by simp only [zero_add])
  unfold sufRawM256
  set M := 256 - z % 256
  by_cases h256 : M = 256
  · rw [h256, show Nat.beq 256 256 = true from rfl]; dsimp only [Bool.casesOn]
    rw [unpk5_zero, ← hSufSum 256]
    have hn0 := sumSufST_none hv (base := 0) (K := 256) (by norm_num)
    rw [show (2 ^ 8 / 2 : Nat) = 128 by norm_num] at hn0
    exact hn0.symm
  · have hlt : M < 256 := by dsimp [M] at h256 ⊢; omega
    rw [show Nat.beq M 256 = false from Bool.eq_false_iff.mpr fun hb => h256 (Nat.beq_eq.mp hb)]
    dsimp only [Bool.casesOn]; rw [sufST128F_eq, hsuf M]
    have hs := sufST_eq_sumSufST hv 0 M 0 (by simpa using hlt)
    simp only [zero_add, show (2 ^ 8 / 2 : Nat) = 128 by norm_num] at hs
    exact hs.trans (hSufSum M)

def laneValsSpecSub62 (isNN : Bool) (a : Nat) (r01 : Bool) (p j : Nat) (v : TripleNat) : Prop :=
    v = .mk (∑ idx ∈ Finset.range 256, sweepBktSub62 isNN .ee a r01 p j idx)
    (∑ idx ∈ Finset.range 256, sweepBktSub62 isNN .nn a r01 p j idx)
    (∑ idx ∈ Finset.range 256, sweepBktSub62 isNN .en a r01 p j idx)
theorem unpk5_div_helpers (s : Nat) : s % 4096 = unpk5 .l0 s ∧ (s / 4096) % 4096 = unpk5 .l1 s ∧
    (s / 16777216) % 4096 = unpk5 .l2 s ∧ ((s / 16777216) / 4096) % 4096 = unpk5 .l3 s ∧
    (s / 16777216) / 16777216 = unpk5 .l4 s ∧ s / 281474976710656 = unpk5 .l4 s := by
  unfold unpk5; dsimp only
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem sum_bkt_lanes (P : Nat → Prop) [DecidablePred P] (a : Nat) (r01 : Bool) (p j : Nat) :
    let S (f : Nat → Nat) := ∑ idx ∈ Finset.range 256, if P idx then f idx else 0
    82 * S (sweepBkt5Sub62 .l4 a r01 p j) -
        2 * (S (sweepBkt5Sub62 .l0 a r01 p j) + S (sweepBkt5Sub62 .l1 a r01 p j)) =
      S (sweepBktSub62 false .ee a r01 p j) ∧
    2 * S (sweepBkt5Sub62 .l0 a r01 p j) = S (sweepBktSub62 false .nn a r01 p j) ∧
    2 * S (sweepBkt5Sub62 .l1 a r01 p j) = S (sweepBktSub62 false .en a r01 p j) ∧
    80 * S (sweepBkt5Sub62 .l4 a r01 p j) = S (sweepBktSub62 true .ee a r01 p j) ∧
    4 * S (sweepBkt5Sub62 .l2 a r01 p j) = S (sweepBktSub62 true .nn a r01 p j) ∧
    4 * S (sweepBkt5Sub62 .l3 a r01 p j) = S (sweepBktSub62 true .en a r01 p j) := by
  intro S
  have hEE : S (sweepBktSub62 false .ee a r01 p j) +
      2 * (S (sweepBkt5Sub62 .l0 a r01 p j) + S (sweepBkt5Sub62 .l1 a r01 p j)) =
      82 * S (sweepBkt5Sub62 .l4 a r01 p j) := by
    dsimp only [S]
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun idx _ => by
      have := sweepBktSub62_ee_false_add a r01 p j idx
      split_ifs <;> omega
  have hM (k : Nat) (f g : Nat → Nat) (hfg : ∀ idx, g idx = k * f idx) : k * S f = S g := by
    dsimp only [S]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun idx _ => by
      have := hfg idx
      split_ifs <;> omega
  have hL := sweepBktSub62_lanes a r01 p j
  exact ⟨by omega, hM 2 _ _ fun i => (hL i).1, hM 2 _ _ fun i => (hL i).2.1,
    hM 80 _ _ fun i => (hL i).2.2.1, hM 4 _ _ fun i => (hL i).2.2.2.1, hM 4 _ _ fun i =>
        (hL i).2.2.2.2⟩

theorem unpkStVal3_spec (isNN : Bool) {a : Nat} {r01 : Bool} {p j : Nat} {st : SumTree}
    (hst : IsTreeOf (sweepBktPack5Sub62 a r01 p j) 8 0 st) :
    laneValsSpecSub62 isNN a r01 p j (unpkStVal3 isNN st) := by
  have hstP := hst.congr (g := fun idx =>
      pack5Nat (sweepBkt5Sub62 .l0 a r01 p j idx) (sweepBkt5Sub62 .l1 a r01 p j idx)
               (sweepBkt5Sub62 .l2 a r01 p j idx) (sweepBkt5Sub62 .l3 a r01 p j idx)
               (sweepBkt5Sub62 .l4 a r01 p j idx))
    (fun idx _ => sweepBktPack5Sub62_eq_pack5 a r01 p j (0 + idx))
  obtain ⟨b0, b1, b2, b3⟩ := sum_sweepBkt5Sub62_lt a r01 p j
  have hU (c : Lane5) :
      unpk5 c (stVal st) = ∑ idx ∈ Finset.range 256, sweepBkt5Sub62 c a r01 p j idx := by
    obtain ⟨ht0, hv0, _⟩ := projUnpkST5_unpk hstP b0 b1 b2 b3 c
    have ht : IsTreeOf (sweepBkt5Sub62 c a r01 p j) 8 0 (projUnpkST5 c st) :=
      ht0.congr (fun idx _ => chFn5_app c (fun l => sweepBkt5Sub62 l a r01 p j) (0 + idx))
    exact hv0.trans ((stVal_eq_sumAllST ht.isValid).trans (sumAll_eq_sum_of_isTreeOf ht))
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd4'⟩ := unpk5_div_helpers (stVal st)
  have hBL := sum_bkt_lanes (fun _ => True) a r01 p j
  dsimp only at hBL
  simp only [↓reduceIte] at hBL
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hBL
  unfold unpkStVal3 laneValsSpecSub62
  simp only [fN63_eq, stVal63_eq, nat_mod_def, nat_div_def, nat_mul_def, nat_add_def, nat_sub_def]
  cases isNN <;> dsimp only [Bool.casesOn]
  · rw [hd0, hd1, hd4', hU .l0, hU .l1, hU .l4, e0, e1, e2]
  · rw [hd2, hd3, hd4, hU .l2, hU .l3, hU .l4, e3, e4, e5]
def lanePolSpecSub62 (isNN pol : Bool) (a : Nat) (r01 : Bool) (p j z : Nat) : Nat :=
    (∑ idx ∈ Finset.range 256, sweepBktSub62 isNN .ee a r01 p j idx * ((z + idx) / 256)) +
    ((∑ idx ∈ Finset.range 256, sweepBktSub62 isNN .nn a r01 p j idx *
    ((z + (if pol then 0 else 256) + idx) / 512)) + (∑ idx ∈ Finset.range 256,
    sweepBktSub62 isNN .en a r01 p j idx * ((z + (if pol then 256 else 0) + idx) / 512)))
theorem finishLane5PairP_eq (v0 vB0 vB1 s0 sB0 sB1 q : Nat) :
    finishLane5PairP v0 vB0 vB1 s0 sB0 sB1 q = .mk ((v0 * q + s0) + (lane512Hi vB0 sB0 q +
    lane512Lo vB1 sB1 q)) ((v0 * q + s0) + (lane512Lo vB0 sB0 q + lane512Hi vB1 sB1 q)) := by
  unfold finishLane5PairP lane512Lo lane512Hi;
  simp only [fN63_eq, nat_div_def, nat_mod_def, nat_mul_def, nat_add_def]
  cases Nat.beq (q % 2) 0 <;> simp only [] <;> congr 1 <;> ring

theorem evalLane5PairP_eq_sufRaw (isNN : Bool) (v0 vB0 vB1 : Nat) (t : SumTree) (q M : Nat) :
    evalLane5PairP isNN (.mk v0 vB0 vB1) t q M =
      let s := sufRawM256 t M
      if isNN then
        let r2 := s / 16777216
        finishLane5PairP v0 vB0 vB1 (80 * (r2 / 16777216)) (4 * (r2 % 4096))
            (4 * ((r2 / 4096) % 4096)) q
      else
        finishLane5PairP v0 vB0 vB1
          (82 * (s / 281474976710656) - 2 * (s % 4096 + (s / 4096) % 4096))
          (2 * (s % 4096)) (2 * ((s / 4096) % 4096)) q := by
  unfold evalLane5PairP sufRawM256; dsimp only
  cases Nat.beq M 256 <;> cases isNN <;>
    simp only [fN63_eq, nat_mod_def, nat_div_def, nat_mul_def, nat_add_def, nat_sub_def,
      ↓reduceIte, Bool.false_eq_true]

theorem evalLane5PairP_spec (isNN : Bool) {a : Nat} {r01 : Bool} {p j : Nat}
    {v : TripleNat} {st : SumTree}
    (hst : IsTreeOf (sweepBktPack5Sub62 a r01 p j) 8 0 st)
    (hv : laneValsSpecSub62 isNN a r01 p j v) (z : Nat) :
    evalLane5PairP isNN v st (Nat.div z 256) (Nat.sub 256 (Nat.mod z 256)) =
      .mk (lanePolSpecSub62 isNN false a r01 p j z) (lanePolSpecSub62 isNN true a r01 p j z) := by
  rcases v with ⟨v0, vB0, vB1⟩
  injection hv with hv0 hvB0 hvB1
  have hstP := hst.congr (g := fun idx =>
      pack5Nat (sweepBkt5Sub62 .l0 a r01 p j idx) (sweepBkt5Sub62 .l1 a r01 p j idx)
               (sweepBkt5Sub62 .l2 a r01 p j idx) (sweepBkt5Sub62 .l3 a r01 p j idx)
               (sweepBkt5Sub62 .l4 a r01 p j idx))
    (fun idx _ => sweepBktPack5Sub62_eq_pack5 a r01 p j (0 + idx))
  obtain ⟨b0, b1, b2, b3⟩ := sum_sweepBkt5Sub62_lt a r01 p j
  have hS (c : Lane5) :
      unpk5 c (sufRawM256 st (256 - z % 256)) =
        ∑ idx ∈ Finset.range 256,
          if 256 - z % 256 ≤ idx then sweepBkt5Sub62 c a r01 p j idx else 0 := by
    obtain ⟨ht0, _, hsuf0⟩ := projUnpkST5_unpk hstP b0 b1 b2 b3 c
    have ht : IsTreeOf (sweepBkt5Sub62 c a r01 p j) 8 0 (projUnpkST5 c st) :=
      ht0.congr (fun idx _ => chFn5_app c (fun l => sweepBkt5Sub62 l a r01 p j) (0 + idx))
    exact unpk5_sufRawM256_eq c ht hsuf0 z
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd4'⟩ := unpk5_div_helpers (sufRawM256 st (256 - z % 256))
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := sum_bkt_lanes (fun idx => 256 - z % 256 ≤ idx) a r01 p j
  rw [evalLane5PairP_eq_sufRaw]
  unfold lanePolSpecSub62
  simp only [nat_div_def, nat_sub_def, nat_mod_def]
  have hc0 := sumCarry256_of_sums hv0 rfl (z := z)
  obtain ⟨h0Lo, h0Hi⟩ := lane512Lo_Hi_eq hvB0 (sumCarry256_of_sums hvB0 rfl (z := z))
  obtain ⟨h1Lo, h1Hi⟩ := lane512Lo_Hi_eq hvB1 (sumCarry256_of_sums hvB1 rfl (z := z))
  cases isNN <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  · rw [hd0, hd1, hd4', hS .l0, hS .l1, hS .l4, e0, e1, e2, finishLane5PairP_eq,
        hc0, h0Lo, h0Hi, h1Lo, h1Hi]
  · rw [hd2, hd3, hd4, hS .l2, hS .l3, hS .l4, e3, e4, e5, finishLane5PairP_eq,
        hc0, h0Lo, h0Hi, h1Lo, h1Hi]
attribute [local irreducible] finishLane5PairP evalLane5PairP

def st4PolSpecSub62 (isNN pol : Bool) (a : Nat) (r01 : Bool) (p z0 z1 z2 z3 : Nat) : Nat :=
    lanePolSpecSub62 isNN pol a r01 p 0 z0 + lanePolSpecSub62 isNN pol a r01 p 1 z1 +
    lanePolSpecSub62 isNN pol a r01 p 2 z2 + lanePolSpecSub62 isNN pol a r01 p 3 z3
def ST4LaneValsSub62 (isNN : Bool) (a : Nat) (r01 : Bool) (p : Nat) (va : TripleNat) (ta : SumTree)
    (vb : TripleNat) (tb : SumTree) (vc : TripleNat) (tc : SumTree) (vd : TripleNat)
    (td : SumTree) : Prop :=
    IsTreeOf (sweepBktPack5Sub62 a r01 p 0) 8 0 ta ∧ laneValsSpecSub62 isNN a r01 p 0 va ∧
    IsTreeOf (sweepBktPack5Sub62 a r01 p 1) 8 0 tb ∧ laneValsSpecSub62 isNN a r01 p 1 vb ∧
    IsTreeOf (sweepBktPack5Sub62 a r01 p 2) 8 0 tc ∧ laneValsSpecSub62 isNN a r01 p 2 vc ∧
    IsTreeOf (sweepBktPack5Sub62 a r01 p 3) 8 0 td ∧ laneValsSpecSub62 isNN a r01 p 3 vd
theorem evalQuad5PairP_step {p0 p1 p2 p3 : PairNat} {f0 t0 f1 t1 f2 t2 f3 t3 : Nat}
    (h0 : p0 = .mk f0 t0) (h1 : p1 = .mk f1 t1) (h2 : p2 = .mk f2 t2) (h3 : p3 = .mk f3 t3)
    (m g hi lo s0Sq : Nat) : checkPairOfPairNat (addPairNat (addPairNat p0 p1)
    (addPairNat p2 p3)) m g hi lo s0Sq = checkPairNum63 (f0 + f1 + f2 + f3)
    (t0 + t1 + t2 + t3) m g hi lo s0Sq := by
  subst h0; subst h1; subst h2; subst h3
  unfold addPairNat checkPairOfPairNat; simp only [fN63_eq, nat_add_def, Nat.add_assoc]
theorem evalQuad5PairP_eq (isNN : Bool) {a : Nat} {r01 : Bool} {p : Nat} {va : TripleNat}
    {ta : SumTree} {vb : TripleNat} {tb : SumTree} {vc : TripleNat} {tc : SumTree} {vd : TripleNat}
    {td : SumTree} (hV : ST4LaneValsSub62 isNN a r01 p va ta vb tb vc tc vd td)
    (z0 z1 z2 z3 m g hi lo s0Sq : Nat) :
    evalQuad5PairP isNN va ta vb tb vc tc vd td (Nat.div z0 256) (Nat.sub 256 (Nat.mod z0 256))
    (Nat.div z1 256) (Nat.sub 256 (Nat.mod z1 256)) (Nat.div z2 256) (Nat.sub 256 (Nat.mod z2 256))
    (Nat.div z3 256) (Nat.sub 256 (Nat.mod z3 256)) m g hi lo s0Sq =
    checkPairNum63 (st4PolSpecSub62 isNN false a r01 p z0 z1 z2 z3)
    (st4PolSpecSub62 isNN true a r01 p z0 z1 z2 z3) m g hi lo s0Sq :=
    evalQuad5PairP_step (evalLane5PairP_spec isNN hV.1 hV.2.1 z0)
    (evalLane5PairP_spec isNN hV.2.2.1 hV.2.2.2.1 z1)
    (evalLane5PairP_spec isNN hV.2.2.2.2.1 hV.2.2.2.2.2.1 z2)
    (evalLane5PairP_spec isNN hV.2.2.2.2.2.2.1 hV.2.2.2.2.2.2.2 z3) m g hi lo s0Sq
attribute [local irreducible] unpkStVal3 addPairNat checkPairOfPairNat evalQuad5PairP checkPairNum63

theorem sum_sweepBktSub62_mul_div (isNN : Bool) (ch : ChK2) (a : Nat) (r01 : Bool)
    (r6 j z sh dv : Nat) : (∑ idx ∈ Finset.range 256, sweepBktSub62 isNN ch a r01 (128 * r6) j idx *
    ((z + sh + idx) / dv)) = ∑ i ∈ Finset.range nSamples13, if j18At13 a r01 (decide (i < 128 *
    r6)) i = j then dwSub62At13 isNN ch i * (((z + df8At13 i) + sh) / dv) else 0 := by
  rw [show (256 : Nat) = nLanes8 by rw [nLanes8_eq]]
  simp only [sweepBktSub62, Finset.sum_mul]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdf8L : df8At13 i < nLanes8 := by rw [nLanes8_eq]; exact df8At13_lt_256 i
  have hdf8 : df8At13 i ∈ Finset.range nLanes8 := Finset.mem_range.mpr hdf8L
  rw [← Finset.add_sum_erase (Finset.range nLanes8) _ hdf8]
  have h0 : (∑ x ∈ (Finset.range nLanes8).erase (df8At13 i),
      (if j18At13 a r01 (decide (i < 128 * r6)) i = j ∧ df8At13 i = x
       then dwSub62At13 isNN ch i else 0) * ((z + sh + x) / dv)) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      have hne : x ≠ df8At13 i :=
          (Finset.mem_erase.mp hx).1; simp only [hne.symm, and_false, ↓reduceIte, zero_mul]
  rw [h0, add_zero, show z + sh + df8At13 i = (z + df8At13 i) + sh by ring]
  by_cases hj : j18At13 a r01 (decide (i < 128 * r6)) i = j <;>
    simp only [hj, and_self, false_and, ↓reduceIte, zero_mul]

theorem lanePolSpecSub62_eq_sum_samples (isNN pol : Bool) (a : Nat) (r01 : Bool)
    (r6 j z : Nat) : lanePolSpecSub62 isNN pol a r01 (128 * r6) j z = ∑ i ∈ Finset.range nSamples13,
    if j18At13 a r01 (decide (i < 128 * r6)) i = j then termSub62PolNat isNN pol (wAt13 i)
    (affineBit13 7483 (x13At13 i)) (z + df8At13 i) else 0 := by
  unfold lanePolSpecSub62;
  have h0 := sum_sweepBktSub62_mul_div isNN .ee a r01 r6 j z 0 256; simp only [add_zero] at h0
  rw [h0, sum_sweepBktSub62_mul_div isNN .nn a r01 r6 j z (if pol then 0 else 256) 512,
      sum_sweepBktSub62_mul_div isNN .en a r01 r6 j z (if pol then 256 else 0) 512,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hj : j18At13 a r01 (decide (i < 128 * r6)) i = j
  · simp only [hj, ↓reduceIte]
    unfold dwSub62At13
    rw [← add_assoc]
    exact dwSub62W_sum_eq_termSub62PolNat isNN pol (wAt13 i)
      (affineBit13 7483 (x13At13 i)) (z + df8At13 i)
  · simp only [hj, ↓reduceIte, add_zero]

theorem st4PolSpecSub62_eq_sum (isNN pol : Bool) {a r6 : Nat} (ha : a < 32) (hr6 : r6 < 64)
    (z0 z1 z2 z3 : Nat) :
    st4PolSpecSub62 isNN pol a (r01OfR6 r6) (128 * r6) z0 z1 z2 z3 =
      ∑ w : Fin 2048, ∑ u0 : Fin 2, ∑ u1 : Fin 2,
        let x13 := x13OfW11U01 w u0 u1;
        let z := qKnotW11 z0 z1 z2 z3 (popBernJK2 (64 * a + r6) w (o9Of13 x13))
        termSub62PolNat isNN pol w.val (affineBit13 7483 x13) (z + (df8Of13 x13).val) := by
  unfold st4PolSpecSub62
  set r01 := r01OfR6 r6
  let hLP := lanePolSpecSub62_eq_sum_samples isNN pol a r01 r6
  rw [hLP 0 z0, hLP 1 z1, hLP 2 z2, hLP 3 z3]
  simp only [← Finset.sum_add_distrib]
  trans ∑ i : Fin nSamples13, termSub62PolNat isNN pol (wAt13 i.val)
      (affineBit13 7483 (x13At13 i.val))
    (qKnotW11 z0 z1 z2 z3 (j18At13 a r01 (decide (i.val < 128 * r6)) i.val) + df8At13 i.val)
  · rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases (by omega : ∀ n < 4, n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) _
      (j18At13_lt_four a r01 (decide (i.val < 128 * r6)) i.val) with h | h | h | h <;>
          simp [h, qKnotW11]
  rw [← equivN13Of64x128.sum_comp, Fintype.sum_prod_type]
  symm
  rw [← equivW11CLB.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun g6 _ => ?_
  rw [← equiv128Of32x2x2.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u5 _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ?_
  set iVal := 128 * g6.val + (4 * u5.val + (u0.val + 2 * u1.val))
  have hiEq : (equivN13Of64x128 (g6, equiv128Of32x2x2 (u5, (u0, u1)))).val = iVal := rfl
  simp only [hiEq]
  have hiDiv : iVal / 128 = g6.val := by dsimp [iVal]; omega
  have hiMod4 : (iVal % 128) / 4 = u5.val := by dsimp [iVal]; omega
  have hiMod01 : (iVal % 128) % 4 = u0.val + 2 * u1.val := by dsimp [iVal]; omega
  set ug : Fin 32 × Fin 64 := (u5, g6)
  have hg6Eq : clbGam6 (equivW11CLB ug).val = g6.val :=
      congrArg (fun x => x.2.val) (equivW11CLB.left_inv ug)
  have hwEq : wAt13 iVal = (equivW11CLB ug).val := by unfold wAt13; rw [hiMod4, hiDiv]; rfl
  set w := equivW11CLB ug
  set x13 := x13OfW11U01 w u0 u1
  have hxEq : x13At13 iVal = x13 := by
    dsimp only [x13]; unfold x13At13 x13OfW11U01; rw [hwEq, hiMod01]; ring
  have hltEq : decide (iVal < 128 * r6) = decide (clbGam6 w.val < r6) := by
    rw [hg6Eq]
    by_cases hlt : g6.val < r6
    · rw [decide_eq_true hlt, decide_eq_true (by dsimp [iVal]; omega)]
    · rw [decide_eq_false hlt, decide_eq_false (by dsimp [iVal]; omega)]
  have hjEq : popBernJK2 (64 * a + r6) w (o9Of13 x13) = j18At13 a r01 (decide (iVal < 128 *
      r6)) iVal := by
    unfold j18At13 d11At13 o9At13
    rw [hltEq, hiDiv, ← hg6Eq, hxEq]
    exact (j18AtARB_eq_popBernJK2 ha hr6 w (o9Of13 x13)).symm
  rw [hwEq, hxEq, show df8At13 iVal = (df8Of13 x13).val by unfold df8At13; rw [hxEq], hjEq]

theorem qKnotW11_zKnotLo6 (cb : ChW11) (k i7 j : ℕ) (hj : j < 4) : qKnotW11 (zKnotLo6 cb k i7 0)
    (zKnotLo6 cb k i7 1) (zKnotLo6 cb k i7 2) (zKnotLo6 cb k i7 3) j = zKnotLo6 cb k i7 j := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem st4PolSpecSub62_eq_expFnSub62Pol (isNN pol : Bool) {d2 : ℕ} (hd2 : d2 < 262144) :
    let cb := sub62FnCh isNN; let p := evenOctIdxT10K isNN d2
    64 * (st4PolSpecSub62 isNN pol
      (t11OfParts p / 64) (r01OfR6 (t11OfParts p % 64)) (128 * (t11OfParts p % 64))
      (zKnotLo6 cb p.2.2 (idx7OfParts p) 0) (zKnotLo6 cb p.2.2 (idx7OfParts p) 1)
      (zKnotLo6 cb p.2.2 (idx7OfParts p) 2) (zKnotLo6 cb p.2.2 (idx7OfParts p) 3) : ℝ) =
    (167340 : ℝ) * expFnSub62Pol isNN pol d2 := by
  dsimp only
  set cb := sub62FnCh isNN
  set p := evenOctIdxT10K isNN d2
  have ht11 : t11OfParts p < 2048 := (parts_popBern_bounds isNN hd2).2.1
  set r6 := t11OfParts p % 64; set a := t11OfParts p / 64
  have hr6 : r6 < 64 := Nat.mod_lt _ (by omega)
  have ha : a < 32 := by dsimp only [a]; omega
  have ht11_eq : 64 * a + r6 = t11OfParts p := Nat.div_add_mod (t11OfParts p) 64
  have hNat :
      st4PolSpecSub62 isNN pol a (r01OfR6 r6) (128 * r6)
        (zKnotLo6 cb p.2.2 (idx7OfParts p) 0) (zKnotLo6 cb p.2.2 (idx7OfParts p) 1)
        (zKnotLo6 cb p.2.2 (idx7OfParts p) 2) (zKnotLo6 cb p.2.2 (idx7OfParts p) 3) =
      eSub62PolNat isNN pol d2 := by
    rw [st4PolSpecSub62_eq_sum isNN pol ha hr6]
    unfold eSub62PolNat
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u0 _ =>
      Finset.sum_congr rfl fun u1 _ => ?_
    dsimp only
    rw [ht11_eq,
        qKnotW11_zKnotLo6 cb p.2.2 (idx7OfParts p) _
          (popBernJK2_lt_four (t11OfParts p) w (o9Of13 (x13OfW11U01 w u0 u1))),
        ← chFn_ySampleK2_lo6_eq_zKnotLo6 cb isNN d2 w (o9Of13 (x13OfW11U01 w u0 u1)),
        chFn_sub62FnCh_eq isNN]
    rfl
  rw [congrArg (Nat.cast (R := ℝ)) hNat]; unfold expFnSub62Pol; ring
theorem scanZLLFastSub62_sound (isNN pol : Bool) (cb : ChW11) (k step2 wBase : Nat)
    {a0 : Nat} {r01 : Bool} {p0 : Nat}
    {va : TripleNat} {ta : SumTree}
    {vb : TripleNat} {tb : SumTree}
    {vc : TripleNat} {tc : SumTree}
    {vd : TripleNat} {td : SumTree}
    (hV : ST4LaneValsSub62 isNN a0 r01 p0 va ta vb tb vc tc vd td)
    (qt g hi lo s0Sq : Nat) :
    ∀ {n iBase : Nat}, iBase + n ≤ 128 →
      scanZLLFastSub62 isNN va ta vb tb vc tc vd td
        qt g hi lo s0Sq
        (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256) (2 ^ k) step2 wBase n iBase) = true →
      ∀ i7, iBase ≤ i7 → i7 < iBase + n →
        let m := (wBase + 2048 * i7) / step2 + qt
        ¬(m % 8 = 7) → ¬(m % 32 = 28) →
        checkNum63 (st4PolSpecSub62 isNN pol a0 r01 p0
          (zKnotLo6 cb k i7 0) (zKnotLo6 cb k i7 1)
          (zKnotLo6 cb k i7 2) (zKnotLo6 cb k i7 3)) m g hi lo s0Sq = true
  | 0, _, _, _, _, hi1, hi2 => by omega
  | n + 1, iBase, hle, hscan, i7, hi1, hi2 => by
      dsimp only at hscan ⊢
      unfold buildZLLK2 at hscan
      simp only [sZLL_eq, fN63_eq, nat_add_def, nat_mul_def] at hscan
      have hz0 := zKnotFast_at_lo6NT cb k iBase 0 (by omega) (by omega)
      simp only [add_zero] at hz0
      rw [hz0, zKnotFast_at_lo6NT cb k iBase 1 (by omega) (by omega),
          zKnotFast_at_lo6NT cb k iBase 2 (by omega) (by omega),
          zKnotFast_at_lo6NT cb k iBase 3 (by omega) (by omega)] at hscan
      unfold scanZLLFastSub62 at hscan
      rcases (andB63_eq_true _ _).mp hscan with ⟨hHead, hTail⟩
      by_cases heq : i7 = iBase
      · subst heq
        intro hm7 hm28
        rw [nat_div_def (wBase + 2048 * i7) step2, nat_add_def] at hHead
        unfold evalCheckPtFastSub62 at hHead
        simp only [nat_mod_def ((wBase + 2048 * i7) / step2 + qt) 8,
          nat_mod_def ((wBase + 2048 * i7) / step2 + qt) 32,
          Bool.eq_false_iff.mpr fun ht => hm7 (Nat.beq_eq.mp ht),
          Bool.eq_false_iff.mpr fun ht => hm28 (Nat.beq_eq.mp ht)] at hHead
        rw [evalQuad5PairP_eq isNN hV] at hHead
        have hPol := checkPairNum63_sound hHead pol
        cases pol <;> simpa using hPol
      · exact scanZLLFastSub62_sound isNN pol cb k step2 wBase hV qt g hi lo s0Sq
          (by omega) hTail i7 (by omega) (by omega)
attribute [local irreducible]
  buildZLLK2 buildZOct10LK2 scanZLLFastSub62 evalCheckPtFastSub62

theorem ulp_of_checkAtT11ZLLFastSub62 (isNN pol : Bool) {g hi lo s0Sq d2 : Nat} {st : ST4}
    (hK : Sub62Consts isNN g hi lo s0Sq)
    (hd2ge : 256 ≤ d2) (hd2lt : d2 < 192512) (hm7 : ¬(d2 % 8 = 7)) (hm28 : ¬(d2 % 32 = 28))
    (hst : IsST4Of8 (sweepBktPack5Sub62
      (t11OfParts (evenOctIdxT10K isNN d2) / 64)
      (r01OfR6 (t11OfParts (evenOctIdxT10K isNN d2) % 64))
      (128 * (t11OfParts (evenOctIdxT10K isNN d2) % 64))) st)
    (hck : checkAtT11ZLLFastSub62 isNN (buildZOct10LK2 (sub62FnCh isNN))
      (t11OfParts (evenOctIdxT10K isNN d2)) st g hi lo s0Sq = true) :
    |((sub62Mc isNN : ℝ) / ((1 : ℝ) * 5714023029)) *
        expFnSub62Pol isNN pol d2 -
      (sub62DcMilli isNN : ℝ) / 1000 -
      (2 ^ 35 : ℝ) / √((max d2 (if isNN then 8 else 1) : ℕ) : ℝ)| ≤
        (sub62EpsMilli isNN : ℝ) / 1000 := by
  have hd2_262 : d2 < 262144 := by omega
  obtain ⟨hk4, hk8, hi7lt, _, _, _⟩ :=
      @evenOct_mid_props_w11B isNN d2 hd2ge (by omega : d2 < 194560)
  have hmsh := evenOct_m_shift_w11B isNN hd2_262
  dsimp only at hmsh
  set cb := sub62FnCh isNN
  set p := evenOctIdxT10K isNN d2
  set i7 := idx7OfParts p
  set t11 := t11OfParts p
  set m := max d2 (if isNN then 8 else 1)
  have hm_eq : m = d2 := by
    dsimp [m]; cases isNN <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
  rcases st with ⟨_, ta, tb, tc, td⟩
  rcases hst with ⟨hta, htb, htc, htd⟩
  rw [buildZOct10LK2_eq] at hck
  unfold checkAtT11ZLLFastSub62 at hck
  dsimp only at hck
  simp only [sTriple3_eq, andB63_eq_true] at hck
  let u := unpkStVal3 isNN
  have hV : ST4LaneValsSub62 isNN (t11 / 64) (r01OfR6 (t11 % 64)) (128 * (t11 % 64))
      (u ta) ta (u tb) tb (u tc) tc (u td) td :=
    ⟨hta, unpkStVal3_spec isNN hta, htb, unpkStVal3_spec isNN htb,
     htc, unpkStVal3_spec isNN htc, htd, unpkStVal3_spec isNN htd⟩
  rcases hck with ⟨c4lo, c4hi, c5lo, c5hi, c6lo, c6hi, c7lo, c7hi, c8lo, c8hi⟩
  have hHalf (k step2 wBase n iBase : Nat) (hle : iBase + n ≤ 128) (hkEq : p.2.2 = k)
      (hStep : step2 = 512 ∨ step2 = 256 ∨ step2 = 128 ∨ step2 = 64 ∨ step2 = 32 ∨
        step2 = 16 ∨ step2 = 8 ∨ step2 = 4 ∨ step2 = 2 ∨ step2 = 1)
      (hwB : wBase = 0 ∨ wBase = 131072) (hmEq : m * step2 = wBase + 2048 * i7 + t11)
      (hc : checkHalfZLLFastSub62 isNN (buildZLLK2 cb (bNT9 word512DualLegLo6T 0 256)
          (2 ^ k) step2 wBase n iBase)
        (u ta) ta (u tb) tb (u tc) tc (u td) td t11 step2 g hi lo s0Sq = true) (hi1 : iBase ≤ i7)
            (hi2 : i7 < iBase + n) :
      checkNum63 (st4PolSpecSub62 isNN pol (t11 / 64) (r01OfR6 (t11 % 64)) (128 * (t11 % 64))
          (zKnotLo6 cb p.2.2 i7 0)
        (zKnotLo6 cb p.2.2 i7 1) (zKnotLo6 cb p.2.2 i7 2) (zKnotLo6 cb p.2.2 i7 3)) m g hi lo s0Sq =
            true := by
    obtain ⟨htMod, hmDiv⟩ := t11_step_arith hStep hwB hmEq
    unfold checkHalfZLLFastSub62 at hc
    rw [nat_mod_def, nat_div_def, htMod, show Nat.beq 0 0 = true from rfl] at hc
    dsimp only [Bool.casesOn] at hc
    have hs :=
        scanZLLFastSub62_sound isNN pol cb k step2 wBase hV (t11 /
        step2) g hi lo s0Sq hle hc i7 hi1 hi2
    dsimp only at hs
    rw [hmDiv, hm_eq] at hs
    rw [hkEq, hm_eq]
    exact hs hm7 hm28
  refine ulp_sub62_of_checkNum63 isNN hK (by omega)
      (st4PolSpecSub62_eq_expFnSub62Pol isNN pol hd2_262) ?_
  have hk5 : p.2.2 = 4 ∨ p.2.2 = 5 ∨ p.2.2 = 6 ∨ p.2.2 = 7 ∨ p.2.2 = 8 := by omega
  by_cases h64 : 64 ≤ i7
  · have hHi (k s) (hk : p.2.2 = k) (hS) (hmE) (hc) :=
      hHalf k s 0 64 64 (by omega) hk hS (.inl rfl) hmE hc h64 (by omega)
    rw [Nat.ble_eq.mpr h64, Bool.cond_true, Bool.cond_true] at hmsh
    rcases hk5 with hk | hk | hk | hk | hk <;> rw [hk] at hmsh <;> norm_num at hmsh
    exacts [hHi 4 256 hk (by omega) (by omega) c4hi, hHi 5 64 hk (by omega) (by omega) c5hi,
      hHi 6 16 hk (by omega) (by omega) c6hi, hHi 7 4 hk (by omega) (by omega) c7hi,
      hHalf 8 1 0 30 64 (by omega) hk (by omega) (.inl rfl) (by omega) c8hi h64 (by omega)]
  · have hLo (k s) (hk : p.2.2 = k) (hS) (hmE) (hc) :=
      hHalf k s 131072 64 0 (by omega) hk hS (.inr rfl) hmE hc (by omega) (by omega)
    rw [Bool.eq_false_iff.mpr fun hb => h64 (Nat.ble_eq.mp hb), Bool.cond_false,
        Bool.cond_false] at hmsh
    rcases hk5 with hk | hk | hk | hk | hk <;> rw [hk] at hmsh <;> norm_num at hmsh
    exacts [hLo 4 512 hk (by omega) (by omega) c4lo, hLo 5 128 hk (by omega) (by omega) c5lo,
      hLo 6 32 hk (by omega) (by omega) c6lo, hLo 7 8 hk (by omega) (by omega) c7lo,
      hLo 8 2 hk (by omega) (by omega) c8lo]
attribute [local irreducible] chFnFast zKnotLo6 st4PolSpecSub62

theorem step_sNT63 {α : Type} (x y : NatTree) (hxy : x = y) (k : NatTree → α) : sNT63 x k =
    k y := by rw [sNT63_eq, hxy]
theorem step_fN63 {α : Type} (x y : Nat) (hxy : x = y) (k : Nat → α) : fN63 x k = k y := by
  rw [fN63_eq, hxy]
theorem one_le_max_sub62 (isNN : Bool) (d2 : Nat) : 1 ≤ max d2 (if isNN then 8 else 1) := by
  cases isNN <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega

theorem checkPairNum63_sound_pol (pol : Bool) {eF eT m g hi lo s0Sq : Nat} (f : Bool → Nat)
    (hfF : f false = eF) (hfT : f true = eT) (hc : checkPairNum63 eF eT m g hi lo s0Sq = true) :
    checkNum63 (f pol) m g hi lo s0Sq = true := by
  have hPol := checkPairNum63_sound hc pol
  cases pol
  · rw [hfF]; rw [_root_.ite_eq_right Bool.false_ne_true] at hPol; exact hPol
  · rw [hfT]; rw [_root_.ite_eq_left rfl] at hPol; exact hPol

theorem ulp_of_checkPtSkipOtherFastSub62 (isNN pol : Bool) {g hi lo s0Sq a r6 d2 : Nat} {st4 : ST4}
    (hK : Sub62Consts isNN g hi lo s0Sq) (hd2 : d2 < 262144) (hm7 : ¬(d2 % 8 = 7))
    (ha_eq : t11OfParts (evenOctIdxT10K isNN d2) / 64 = a)
    (hr6_eq : t11OfParts (evenOctIdxT10K isNN d2) % 64 = r6)
    (hst : IsST4Of8 (sweepBktPack5Sub62 a (r01OfR6 r6) (128 * r6)) st4)
    (hc : checkPtSkipOtherFastSub62 (sub62FnCh isNN) isNN (bNT9 word512DualLegLo6T 0 256)
      a r6 st4 g hi lo s0Sq d2 = true) :
    |((sub62Mc isNN : ℝ) / ((1 : ℝ) * 5714023029)) *
        expFnSub62Pol isNN pol d2 -
      (sub62DcMilli isNN : ℝ) / 1000 -
      (2 ^ 35 : ℝ) / √((max d2 (if isNN then 8 else 1) : ℕ) : ℝ)| ≤
        (sub62EpsMilli isNN : ℝ) / 1000 := by
  rcases st4 with ⟨_, ta, tb, tc, td⟩
  rcases hst with ⟨hta, htb, htc, htd⟩
  unfold checkPtSkipOtherFastSub62 at hc
  rw [nat_mod_def, show Nat.beq (d2 % 8) 7 = false from Bool.eq_false_iff.mpr fun ht =>
      hm7 (Nat.beq_eq.mp ht)] at hc
  dsimp only [Bool.casesOn] at hc
  rw [sParts_eq, evenOctPartsW11_eq_w11B] at hc
  set cb := sub62FnCh isNN
  set p := evenOctIdxT10K isNN d2
  obtain ⟨hi7, _, _⟩ := parts_popBern_bounds isNN hd2
  rw [step_fN63 (Nat.add (Nat.mul (Nat.mod p.1 2) 1024) p.2.1) (t11OfParts p) rfl,
      show Nat.div (t11OfParts p) 64 = a by rw [nat_div_def]; exact ha_eq,
      show Nat.mod (t11OfParts p) 64 = r6 by rw [nat_mod_def]; exact hr6_eq,
      show andB63 (Nat.beq a a)
          (Nat.beq r6 r6) = true by rw [Nat.beq_refl a, Nat.beq_refl r6]; rfl] at hc
  dsimp only [Bool.casesOn] at hc
  have hz0 := zKnotFast_at_lo6NT cb p.2.2 (idx7OfParts p) 0 hi7 (by omega)
  have hz1 := zKnotFast_at_lo6NT cb p.2.2 (idx7OfParts p) 1 hi7 (by omega)
  have hz2 := zKnotFast_at_lo6NT cb p.2.2 (idx7OfParts p) 2 hi7 (by omega)
  have hz3 := zKnotFast_at_lo6NT cb p.2.2 (idx7OfParts p) 3 hi7 (by omega)
  simp only [add_zero] at hz0
  rw [← nat_add_def] at hz1 hz2 hz3
  rw [step_fN63 _ _ (maxDistW11_eq_w11B isNN d2),
      step_fN63 (Nat.div p.1 2) (idx7OfParts p) (nat_div_def p.1 2),
      step_fN63 _ _ (nat_pow_def 2 p.2.2), step_fN63 _ _ (nat_mul_def 4 (idx7OfParts p)),
      step_fN63 _ _ hz0, step_fN63 _ _ hz1, step_fN63 _ _ hz2, step_fN63 _ _ hz3] at hc
  simp only [sTriple3_eq] at hc
  have hV : ST4LaneValsSub62 isNN a (r01OfR6 r6) (128 * r6)
      (unpkStVal3 isNN ta) ta (unpkStVal3 isNN tb) tb (unpkStVal3 isNN tc) tc (unpkStVal3 isNN td)
          td :=
    ⟨hta, unpkStVal3_spec isNN hta, htb, unpkStVal3_spec isNN htb,
     htc, unpkStVal3_spec isNN htc, htd, unpkStVal3_spec isNN htd⟩
  rw [evalQuad5PairP_eq isNN hV, ← ha_eq, ← hr6_eq] at hc
  exact ulp_sub62_of_checkNum63 isNN hK (one_le_max_sub62 isNN d2)
      (st4PolSpecSub62_eq_expFnSub62Pol isNN pol hd2)
    (checkPairNum63_sound_pol pol (fun b => st4PolSpecSub62 isNN b (t11OfParts p / 64)
      (r01OfR6 (t11OfParts p % 64)) (128 * (t11OfParts p % 64))
      (zKnotLo6 cb p.2.2 (idx7OfParts p) 0) (zKnotLo6 cb p.2.2 (idx7OfParts p) 1)
      (zKnotLo6 cb p.2.2 (idx7OfParts p) 2) (zKnotLo6 cb p.2.2 (idx7OfParts p) 3)) rfl rfl hc)

attribute [local irreducible] checkHalfZLLFastSub62 checkAtT11ZLLFastSub62 checkPtSkipOtherFastSub62

theorem sweepR6TreeBothSub62_sound (lo6NT : NatTree) (zoEE zoNN : ZOct10L)
    (gEE hiEE loEE gNN hiNN loNN s0Sq a : Nat) :
    ∀ (d b : Nat) {cur : ST4P2},
      b + 2 ^ d ≤ 64 → IsST4P2Pack5Sub62 a (128 * b) cur →
      match sweepR6TreeBothSub62 zoEE zoNN lo6NT gEE hiEE loEE gNN hiNN loNN s0Sq a
        (bNT11 (jPack4Leaf a) 0 1024) d b
        (buildNT63 samplePackLeafK2Pure (d + 7) (128 * b) (2 ^ (d + 6)))
        (buildNT63 wgtLeaf5Sub62Pure (d + 7) (128 * b) (2 ^ (d + 6))) cur with
      | .mk false _ => True
      | .mk true nxt =>
          IsST4P2Pack5Sub62 a (128 * (b + 2 ^ d)) nxt ∧
            ∀ off < 2 ^ d, ∃ st : ST4,
              IsST4Of8 (sweepBktPack5Sub62 a (r01OfR6 (b + off)) (128 * (b + off))) st ∧
              checkAtT11ZLLFastSub62 false zoEE (64 * a + (b + off)) st gEE hiEE loEE s0Sq = true ∧
              checkSmAtARFastSub62 .ee false lo6NT a (b + off) st gEE hiEE loEE s0Sq = true ∧
              checkAtT11ZLLFastSub62 true zoNN (64 * a + (b + off)) st gNN hiNN loNN s0Sq = true ∧
              checkSmAtARFastSub62 .nn true lo6NT a (b + off) st gNN hiNN loNN s0Sq = true
  | 0, b, cur, hb, hcur => by
      dsimp only [sweepR6TreeBothSub62]; rw [sST4_eq, fN63_eq, nat_add_def, nat_mul_def]
      cases cEE : checkAtT11ZLLFastSub62 false zoEE (64 * a + b)
          (selST4P2 (r01OfR6 b) cur) gEE hiEE loEE s0Sq
      · exact trivial
      · dsimp only [Bool.casesOn]
        cases sEE :
            checkSmAtARFastSub62 .ee false lo6NT a b (selST4P2 (r01OfR6 b) cur) gEE hiEE loEE s0Sq
        · exact trivial
        · dsimp only [Bool.casesOn]
          cases cNN : checkAtT11ZLLFastSub62 true zoNN (64 * a + b)
              (selST4P2 (r01OfR6 b) cur) gNN hiNN loNN s0Sq
          · exact trivial
          · dsimp only [Bool.casesOn]
            cases sNN :
                checkSmAtARFastSub62 .nn true lo6NT a b (selST4P2 (r01OfR6 b) cur) gNN hiNN loNN
                s0Sq
            · exact trivial
            · dsimp only [Bool.casesOn]; rw [sST4P2_eq]
              have hadv := advSubD13_sound a 7 (128 * b) (by omega) hcur
              rw [show (2 ^ 7 / 2 : Nat) = 64 by norm_num,
                  show 128 * b + 2 ^ 7 = 128 * (b + 1) by omega] at hadv
              refine ⟨by rwa [show 128 * (b + 2 ^ 0) = 128 * (b + 1) from rfl], fun off hoff => ?_⟩
              have hz : off = 0 := by omega
              subst hz; rw [add_zero]
              exact ⟨selST4P2 (r01OfR6 b) cur, selST4P2Pack5_sound hcur (r01OfR6 b), cEE, sEE, cNN,
                  sNN⟩
  | d + 1, b, cur, hb, hcur => by
      have hp6 : (2 ^ (d + 7)) / 2 = 2 ^ (d + 6) := by
        rw [Nat.pow_succ]; have := Nat.two_pow_pos (d + 6); omega
      have h128b : 128 * b + 2 ^ (d + 7) = 128 * (b + 2 ^ d) := by
        have : 2 ^ (d + 7) = 128 * 2 ^ d := by rw [Nat.pow_add]; ring
        omega
      have hBld (f : Nat → Nat) : buildNT63 f (d + 1 + 7) (128 * b) (2 ^ (d + 1 + 6)) =
          .node (buildNT63 f (d + 7) (128 * b) (2 ^ (d + 6))) (buildNT63 f (d + 7)
              (128 * (b + 2 ^ d)) (2 ^ (d + 6))) := by
        rw [buildNT63_succ f (d + 7), hp6, h128b]
      rw [hBld samplePackLeafK2Pure, hBld wgtLeaf5Sub62Pure]
      let run (b' : Nat) (st : ST4P2) :=
          sweepR6TreeBothSub62 zoEE zoNN lo6NT gEE hiEE loEE gNN hiNN loNN s0Sq a
        (bNT11 (jPack4Leaf a) 0 1024) d b' (buildNT63 samplePackLeafK2Pure (d + 7) (128 * b')
            (2 ^ (d + 6)))
        (buildNT63 wgtLeaf5Sub62Pure (d + 7) (128 * b') (2 ^ (d + 6))) st
      dsimp only [sweepR6TreeBothSub62]; simp only [fN63_eq, nat_add_def, nat_pow_def]
      have hL := sweepR6TreeBothSub62_sound lo6NT zoEE zoNN gEE hiEE loEE gNN hiNN loNN s0Sq a d b
        (by rw [Nat.pow_succ] at hb; omega) hcur
      obtain ⟨ok1, mid, hEqL⟩ := elim_st4p2b (run b cur)
      dsimp only [run] at hEqL
      rw [hEqL] at hL; rw [hEqL, sST4P2B_eq]; dsimp only
      cases ok1
      · exact trivial
      · dsimp only [Bool.casesOn]; rcases hL with ⟨hmid, gL⟩
        have hR :=
            sweepR6TreeBothSub62_sound lo6NT zoEE zoNN gEE hiEE loEE gNN hiNN loNN s0Sq a d (b +
            2 ^ d)
          (by rw [Nat.pow_succ] at hb; omega) hmid
        obtain ⟨ok2, nxt, hEqR⟩ := elim_st4p2b (run (b + 2 ^ d) mid)
        dsimp only [run] at hEqR
        rw [hEqR] at hR; rw [hEqR]
        cases ok2
        · trivial
        · dsimp only at hR ⊢; rcases hR with ⟨hnxt, gR⟩
          refine ⟨by rwa [show b + 2 ^ (d + 1) = b + 2 ^ d + 2 ^ d by rw [Nat.pow_succ]; ring],
            fun off hoff => ?_⟩
          by_cases hlt : off < 2 ^ d
          · exact gL off hlt
          · obtain ⟨st, hst, c1, c2, c3, c4⟩ :=
                gR (off - 2 ^ d) (by rw [Nat.pow_succ] at hoff; omega)
            have heq : b + 2 ^ d + (off - 2 ^ d) = b + off := by omega
            rw [heq] at hst c1 c2 c3 c4; exact ⟨st, hst, c1, c2, c3, c4⟩

attribute [local irreducible] sweepR6TreeBothSub62

theorem runOneABothSub62_sound (lo6NT : NatTree) (zoEE zoNN : ZOct10L)
    (gEE hiEE loEE gNN hiNN loNN s0Sq a : Nat)
    (hr : runOneABothSub62 zoEE zoNN lo6NT buildSamplePackK2NT buildWgt5Sub62NT
      gEE hiEE loEE gNN hiNN loNN s0Sq a = true) :
    ∀ r6 < 64, ∃ st : ST4,
      IsST4Of8 (sweepBktPack5Sub62 a (r01OfR6 r6) (128 * r6)) st ∧
      checkAtT11ZLLFastSub62 false zoEE (64 * a + r6) st gEE hiEE loEE s0Sq = true ∧
      checkSmAtARFastSub62 .ee false lo6NT a r6 st gEE hiEE loEE s0Sq = true ∧
      checkAtT11ZLLFastSub62 true zoNN (64 * a + r6) st gNN hiNN loNN s0Sq = true ∧
      checkSmAtARFastSub62 .nn true lo6NT a r6 st gNN hiNN loNN s0Sq = true := by
  unfold runOneABothSub62 at hr
  rw [step_sNT63 _ _ (buildJPackNT_eq a), sST4P2_eq] at hr
  have hSw := sweepR6TreeBothSub62_sound lo6NT zoEE zoNN gEE hiEE loEE gNN hiNN loNN s0Sq a 6 0
    (by norm_num) (show IsST4P2Pack5Sub62 a (128 * 0) _ from initTreeP2D13_isST4P2Pack5 a)
  simp only [Nat.mul_zero, zero_add, show 6 + 7 = 13 from rfl, show 6 + 6 = 12 from rfl,
    show (2 ^ 12 : Nat) = 4096 by norm_num, show (2 ^ 6 : Nat) = 64 by norm_num,
    show 128 * 64 = 8192 from rfl, buildSamplePackK2NT_def, buildWgt5Sub62NT_def] at hSw
  obtain ⟨ok0, _, hEq0⟩ := elim_st4p2b (sweepR6TreeBothSub62 zoEE zoNN lo6NT
    gEE hiEE loEE gNN hiNN loNN s0Sq a (bNT11 (jPack4Leaf a) 0 1024) 6 0
    buildSamplePackK2NT buildWgt5Sub62NT
    (initTreeP2D13 (bNT11 (jPack4Leaf a) 0 1024) buildSamplePackK2NT buildWgt5Sub62NT))
  rw [hEq0] at hSw hr
  dsimp only [ST4P2B.casesOn] at hr
  rw [hr] at hSw
  exact hSw.2
attribute [local irreducible] runOneABothSub62
theorem checkOneABothSub62_sound (isNN : Bool) (a : Nat) (h : checkOneABothSub62 a = true) :
    ∀ r6 < 64, ∃ g hi lo s0Sq : Nat, ∃ st : ST4,
      Sub62Consts isNN g hi lo s0Sq ∧
      IsST4Of8 (sweepBktPack5Sub62 a (r01OfR6 r6) (128 * r6)) st ∧
      checkAtT11ZLLFastSub62 isNN (buildZOct10LK2 (sub62FnCh isNN)) (64 * a + r6)
        st g hi lo s0Sq = true ∧
      checkSmAtARFastSub62 (sub62FnCh isNN) isNN (bNT9 word512DualLegLo6T 0 256)
        a r6 st g hi lo s0Sq = true := by
  unfold checkOneABothSub62 at h
  simp only [sNT63_eq, fN63_eq, sZOct10L_eq, nat_mul_def, nat_pow_def,
    spNTFastK2_eq, wgt5NTFastSub62_eq] at h
  intro r6 hr6
  obtain ⟨st, hst, cEE, sEE, cNN, sNN⟩ := runOneABothSub62_sound _ _ _ _ _ _ _ _ _ _ _ h r6 hr6
  cases isNN
  · exact ⟨_, _, _, _, st, ⟨rfl, rfl, rfl, rfl⟩, hst, cEE, sEE⟩
  · exact ⟨_, _, _, _, st, ⟨rfl, rfl, rfl, rfl⟩, hst, cNN, sNN⟩
attribute [local irreducible] checkOneABothSub62

theorem sub62_pol_ulp (isNN pol : Bool)
    (hAllA : ∀ a : Nat, a < 32 → checkOneABothSub62 a = true)
    {d2 : ℕ} (h3d : Is3DBoxDistSq d2) (hm7 : ¬(d2 % 8 = 7)) :
    |((sub62Mc isNN : ℝ) / ((1 : ℝ) * 5714023029)) *
        expFnSub62Pol isNN pol d2 -
      (sub62DcMilli isNN : ℝ) / 1000 -
      (2 ^ 35 : ℝ) / √((max d2 (if isNN then 8 else 1) : ℕ) : ℝ)| ≤
        (sub62EpsMilli isNN : ℝ) / 1000 := by
  have hd2lt : d2 < 262144 := by have := is3DBoxDistSq_le h3d; omega
  set p := evenOctIdxT10K isNN d2
  obtain ⟨_, ht11lt, _⟩ := parts_popBern_bounds isNN hd2lt
  set t11 := t11OfParts p; set a := t11 / 64; set r6 := t11 % 64
  have ha32 : a < 32 := by dsimp [a]; omega
  have hr6_64 : r6 < 64 := by dsimp [r6]; omega
  obtain ⟨gB, hiB, loB, sqB, st, hKB, hst, hckZLL, hckSm⟩ :=
    checkOneABothSub62_sound isNN a (hAllA a ha32) r6 hr6_64
  rw [Nat.div_add_mod t11 64] at hckZLL
  by_cases hsm : d2 < 256
  · obtain ⟨hr6_0, ha_mod16⟩ := smCoords_lt256 isNN hsm
    have hr6_0' : r6 = 0 := hr6_0; have ha_mod16' : a % 16 = 0 := ha_mod16
    unfold checkSmAtARFastSub62 at hckSm; obtain ⟨hSmLt, _⟩ := (andB63_eq_true _ _).mp hckSm
    rw [show andB63 (Nat.beq r6 0) (Nat.beq (Nat.mod a 16) 0) = true by
      rw [nat_mod_def, hr6_0', ha_mod16']; rfl] at hSmLt
    dsimp only [Bool.casesOn] at hSmLt
    exact ulp_of_checkPtSkipOtherFastSub62 isNN pol hKB hd2lt hm7 rfl hr6_0
      (by rwa [hr6_0'] at hst) (by simpa only [zero_add] using allCnt63_sound hSmLt d2 hsm)
  · by_cases hge : 192512 ≤ d2
    · have hmem := openDistSq_ge_192512_mem_tail16 h3d hge hm7; obtain ⟨ha_mod8, hr6_d2⟩ :=
          smCoords_tail16 isNN hmem
      have ha_mod8' : a % 8 = 0 := ha_mod8; have hr6_d2' : d2 % 64 = r6 := hr6_d2.symm
      unfold checkSmAtARFastSub62 at hckSm; obtain ⟨_, hSmTl⟩ := (andB63_eq_true _ _).mp hckSm
      rw [show Nat.beq (Nat.mod a 8) 0 = true by rw [nat_mod_def, ha_mod8']; rfl] at hSmTl
      dsimp only [Bool.casesOn] at hSmTl; have hpt := allList63_sound hSmTl d2 hmem
      rw [show Nat.beq (Nat.mod d2 64) r6 = true by
        rw [nat_mod_def, hr6_d2']; exact Nat.beq_refl r6] at hpt
      dsimp only [Bool.casesOn] at hpt;
      exact ulp_of_checkPtSkipOtherFastSub62 isNN pol hKB hd2lt hm7 rfl rfl hst hpt
    · exact ulp_of_checkAtT11ZLLFastSub62 isNN pol hKB (by omega) (by omega) hm7
        (is3DBoxDistSq_mod32_ne_28 h3d) hst hckZLL

attribute [local irreducible] checkSmAtARFastSub62
end QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs
end

end
