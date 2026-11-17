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
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CyclotomicPhaseCheck
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SelectSwapQromUnload
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage2ElecSemiBellW287
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance : NeZero 2 := ⟨two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlacePortBOracle
    (xorNucLoToElecHiNotScrOp)
open scoped Matrix BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulDomWRouter216 (band_left band_right
    bitZMod2_congr checkZeroRange checkZeroRange_sound dom216M dom216OutW dom216Post21SMask
    dom216Post21SMask_outside dom216Post21Tree dom216Post21Tree_check dom216PreTree)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulDomWRouter216 (dom216Setup2Tree
    dom216Setup2Tree_check dom216Setup3Tree dom216Setup3Tree_check dom216Setup4Tree
    dom216Setup4Tree_check dom216_1add_lt dom216_stage_facts evalPrimTree_node fR1 fR2 fR3 fR4
    hfB_R1)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulDomWRouter216 (hfB_R2 hfB_R3 hfB_R4
    mut2_of_disj mut3_of_disj natOfZModBits_stTree118 pWIntactBracket stTree118 stTree118_apply_reg
    stTree118_empty stTree118_eq_zero_of_false stTree118_writeReg_disj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulDomWRouter216
    (subspaceStep_pWIntactTreeBracket subspaceStep_treeWrap118 tDom1 tDom2 tDom3 tDom4 tDom5 tDom6
    tDom7 tDom8 tDom9_eq uR1 uR2 uR3 uR4)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
    (supportedOn_uOneHotToggle toggleOneHotBits toggleOneHotBits_apply_other
    toggleOneHotBits_apply_out uOneHotToggle uOneHotToggle_mulVec_ket)
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
set_option autoImplicit false
set_option allowUnsafeReducibility true
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast
  QuantumComputation.Specs.PhotochemistrySolution.TopSelectBridge
  QuantumComputation.Specs.PhotochemistrySolution.CoulombK115
  QuantumComputation.Specs.PhotochemistrySolution.Bf33K9Scr31Opt
  QuantumComputation.Specs.PhotochemistrySolution.CoulM72K115Opt
open QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Chunk
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectRefl
open QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
  QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.CoulombFast
open QuantumComputation.Specs.PhotochemistrySolution.EvenOctB70
  QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream
  QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirstZero
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremCsa36Kick
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
open QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
  QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
  QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960
  QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
  QuantumComputation.Specs.PhotochemistrySolution.Sub63Stage25W309
  QuantumComputation.Specs.PhotochemistrySolution.WStateCoulombOpt
open QuantumComputation.Specs.PhotochemistrySolution.WRouterUnload76Opt
  QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
  QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW325
  QuantumComputation.Specs.PhotochemistrySolution.Stage1CoinDecode
  QuantumComputation.Specs.PhotochemistrySolution.Stage4NoMuxK9Opt
open QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW322
  QuantumComputation.Specs.PhotochemistrySolution.WStateKin446
  QuantumComputation.Specs.PhotochemistrySolution.KpBasis9WRouterOpt
  QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW338Wp237
  QuantumComputation.Specs.PhotochemistrySolution.Stage25InPlace
open QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulDom22NoZeroLive232
    (appendRegRev42_22 appendRegRev42_22_hi appendRegRev42_22_lo eoBitFn
    evalPrimTree_testBit_outside expEvenOctRevCols expEvenOctRevCols_getD expEvenOctRevCols_length
    fullLive12CT getCT_setColsAt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulDom22NoZeroLive232
    (initDomCT_hi0_chk initRev64CT live12FullTree live12FullTree_targets live12Full_parity_eq
    live12QuadMask live12Quad_lt64 outWireOfRegRev outWireOfRegRev_eq_appendRegRev42_22
    pUnloadLive12Range)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulDom22NoZeroLive232
    (primTreeTargetsIn primTreeWiresLt setColsAt stepCB_decodePrimTree_outside
    stepCB_decodePrimTree_updRange_comm subspaceStep_pUnloadLive12Range updPrefixRev
    updPrefixRev_apply_in)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulDom22NoZeroLive232
    (updPrefixRev_apply_lt updPrefixRev_eq_writeReg updRange updRange_eq_updPrefixRev
    zmod2_eq_of_beq_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA (dLayout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
    (uAlignedKinCat2m1_98CselLayout uAlignedKinCat2m1_98UselLayout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6 (circ_comm_of_disj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (HCNOTSupportedIn
    SharedPortBWiring hcnotSupportedIn_fixedBellVec hcnotSupportedIn_fixedSwapVec uSwapHi24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (SharedPortBInput341
    UnloadFootprintN fixedBell1Circ_mulVec_ket_zero fixedFanoutBits fixedFanoutCirc_mulVec_ket
    routerChain_sharedPortB341_ext supportedOn_and)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.StarCcz4Sub16T (StrictOneHotMask
    cGatherStrict1HotZ8 cHadamardVec cZ8PairRangeLoop count_pOneHotScatterStrict1HotDyn
    gatherCzPairs pLiveStarCCZOfClean pOneHotScatterStrict1HotDyn scatterBitsRec scatterUnitary)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.StarCcz4Sub16T
    (scatterUnitary_mulVec_ket subspaceStep_pOneHotScatterStrict1HotDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport
    (ValidZeroGatedWithoutHA copyLoHi_mul_routerSwap_ket_eq_of_oneHot directPrefixSum)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport
    (fixedFanoutBits_oneHot fixedSwap1Circ_oneHot_ket zgat_actsIndepOf_mul)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport
    (zgat_actsIndepOf_rHA_uCopyLoHi zgat_actsIndepOf_rHA_uRouterSwap zgat_ket_dc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport (zgat_ket_sr
    zgat_rHA_inj zgat_rHA_not_pubCtrlSet zgat_supportedOn_H)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport
    (zgat_validZeroGatedWithoutHA_iff zgat_validZeroGatedWithoutHA_update_rHA)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport
    (subspaceStep_drop_zero_vec uCopyLoHiAlwaysLoConj uCopyLoHiAlwaysLoConj_val)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport
    (uDirectGatherPlanesAfterXor uDirectGatherPlanesAfterXor_ket_eval)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimGather9432
    (ValidZ8MuxD1GatherPlaneIn count_pZ8MuxD1GatherPlanesDyn cw_cZ8PairStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimGather9432
    (dynWires_pZ8MuxD1GatherPlanesDyn pZ8MuxD1GatherPlanesDyn subspaceStep_pZ8MuxD1GatherPlanesDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney (spliceUnitary
    spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift (circWires_toCircuit_c70
    rCoinExt rScrExt scrLExt uStage1Clean_c70 val_rScrExt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (privRank454Sub rElecSub
    rNucSub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (coordState
    coordState_spec evalStrict evalStrict_sound ltMask natOfZModBits_lt natOfZModBits_testBit_lt
    subspaceStep_primTreeXor testBit_ltMask)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne disj_of_ne
    potGen_d2_lt potGen_k_lt potGen_y36_lt subspaceStep_wrapOnReg_vprog2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (Stage1ZeroNEremLayout
    wNoHad)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (SortedZeroNEremCoin
    ValidZeroGatedSortedRouterInput routerCtrlHi_of_zeroGatedSorted routerCtrlLo_of_zeroGatedSorted
    zmod2_cases)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg187_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF (z2_add_self_cancel)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65 (QromLoadPkgGenN
    QromUnloadPkgGenN outWire_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg cleanProj
    cleanProj_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse (InnerLoCopyHiSafe
    cFixedBellLoCopyHiCirc fixedFanoutVecCirc hcnotSupportedIn_fixedFanoutVec hne_bufHi_sys)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Qrom (word512DualLeg
    word512DualLeg_lt_pow36)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2W325AlwaysLo
    (Stage5ElecFootprintNoHB7)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage2Load
    (actsIndepOf_allPlaneMod_uOneHotToggle hne_wOutLoN48_wOutHiN48 idxValD_eq_zero_of_zero padLoN48
    wOutHiN48 wOutHiN48_mem wOutLoN48 wOutLoN48_mem wRouterDisj_hiN48 wRouterDisj_loN48)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (word512DualLegLo6)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam (cFixedCopyLoHiCirc
    hk0_le72_wstate)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47 (ValidWRouterCleanHi47
    ValidWRouterCleanLo47 ValidWRouterInHi47 ValidWRouterInLo47 count_wStateComputeLo47
    count_wStateUncomputeLo47 count_wrapWRouterHi47 count_wrapWRouterLo47)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47
    (dynWires_wStateComputeLo47 dynWires_wStateUncomputeLo47 dynWires_wrapWRouterHi47
    dynWires_wrapWRouterLo47 subspaceStep_wrapWRouterHi47 subspaceStep_wrapWRouterLo47
    wStateComputeLo47)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterNuc47 (wStateUncomputeLo47
    wrapWRouterHi47 wrapWRouterLo47)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload (padEOfS7 padNOfS7
    padWires_cast qEncOfS7 s7OfHBE)
open PrimitiveGate (T TOFF)
set_option Elab.async true
set_option maxRecDepth 200000
set_option exponentiation.threshold 8192

/-!
# Genuine-`BellLo` Stage-2E Suite

Catalyst-free genuine-`BellLo` Stage-2E electronic router suite:
1. `8,976-T` 24-plane `OneHotScatter` pre-scatter, `48`-CNOT `cFixupBellLoFromGatherCirc`, and
   factored `pBellLoAfterPubCtrlLo` / `pBellLoFromPostXorTail` (keeping `{M D n : ℕ}` polymorphic
   at `routerOfInvol` / `sPrivCleanSet` sites so `Fin 5146` WHNF never fires).
2. All 4 closed genuine-`BellLo` tiers: **`19,142 T`** (`UsedPrivRank 307`), **`19,146 T`**
   (`UsedPrivRank 262`), **`19,152 T`** (`UsedPrivRank 283` / `238` / `UsedSemiBell238`), and
   **`19,242 T`** (`UsedPrivRank 211` / `214`).
3. `LowQ` (`W = 343..439`) and `0`-Fredkin-swap `UltraLowQ` (`W = 84..135..894`)
   clean-pool loaders + `+0 T` `rPack6604ToLowW` lifts.
-/

noncomputable section
open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit HermitianMat QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouterFredkinMux
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouterMuxD1
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
  QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
  QuantumComputation.Specs.PhotochemistrySolution.RouterAlwaysLoW338
  QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW338At19580
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (idxValD_congr)
namespace QuantumComputation.Specs.PhotochemistrySolution.SlimBellLo19142
open scoped ComplexOrder MatrixOrder
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2EW287Planes
  PhotochemistrySolution.Stage2EW287Unload PhotochemistrySolution.Stage2EW287Pkg
open PrimitiveGate hiding cnot h s swap t toffoli x y z
open _root_.QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse (hne_hA_sys)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket matrix_ext_ket ket_X
    ket_CNOT eval_seq_mulVec bit_cases)
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local reducible] totDimCompactGen

-- Section 2A: `8,976-T` (`0 .TOFF`) 24-Plane `OneHotScatter` Pre-Scatter
-- (`pElecPlanesOneHotScatterLoPubCtrlLo` & `uBellLoPreScatter`)

private theorem zgat_cw_cHadamardVec {n M : ℕ} {S : Wire n → Prop} (x : Fin M → Wire n)
    (hx : ∀ p : Fin M, S (x p)) :
    ∀ (k : ℕ) (hk : k ≤ M), CircWires S (cHadamardVec x k hk)
  | 0, _ => trivial
  | k + 1, hk => cw_seq (zgat_cw_cHadamardVec x hx k (Nat.le_of_succ_le hk)) (cw_1 (hx ⟨k, hk⟩))

private theorem zgat_cw_cZ8PairRangeLoop {n M : ℕ} {S : Wire n → Prop}
    (w x : Fin M → Wire n) (a : Wire n)
    (hwa : ∀ p : Fin M, w p ≠ a) (hxa : ∀ p : Fin M, x p ≠ a)
    (hw : ∀ p : Fin M, S (w p)) (hx : ∀ p : Fin M, S (x p)) (ha : S a) (ofs : ℕ) :
    ∀ (k : ℕ) (hk : ofs + k ≤ M), CircWires S (cZ8PairRangeLoop w x a hwa hxa ofs k hk)
  | 0, _ => trivial
  | k + 1, hk =>
      cw_seq (zgat_cw_cZ8PairRangeLoop w x a hwa hxa hw hx ha ofs k (by omega))
        (cw_cZ8PairStep (hw ⟨ofs + k, by omega⟩) (hx ⟨ofs + k, by omega⟩) ha)

private theorem zgat_dynWires_pOneHotScatterStrict1HotDyn {Var : Type} {n M : ℕ} {S : Wire n → Prop}
    (hM : 1 ≤ M) (v : Var) (w x : Fin M → Wire n) (q a : Wire n) (hwx : ∀ p : Fin M, w p ≠ x p)
    (hwa : ∀ p : Fin M, w p ≠ a) (hxa : ∀ p : Fin M, x p ≠ a) (haq : a ≠ q)
    (hw : ∀ p : Fin M, S (w p)) (hx : ∀ p : Fin M, S (x p)) (hq : S q)
    (ha : S a) : DynWires S (pOneHotScatterStrict1HotDyn hM v w x q a hwx hwa hxa haq) := by
  let p0 : Fin M := ⟨0, hM⟩; have hHad := zgat_cw_cHadamardVec x hx M le_rfl
  have hLoop := zgat_cw_cZ8PairRangeLoop w x a hwa hxa hw hx ha 1 (M - 1) (by omega)
  have hComp : CircWires S (cGatherStrict1HotZ8 hM w x a hwa hxa) :=
      cw_seq (cw_1 ha) (cw_seq (cw_1 ha) (cw_seq (cw_cnot (hx p0) ha)
      (cw_seq hLoop (cw_seq (cw_cnot (hx p0) ha) (cw_seq (cw_1 ha) (cw_seq (cw_cnot (hw p0) ha)
      (cw_seq (cw_T_inv ha) (cw_seq (cw_cnot (hw p0) ha) (cw_seq (cw_1 ha) (cw_seq (cw_1 ha)
      (cw_seq (cw_1 ha) (cw_cnot (hx p0) ha))))))))))))
  have hPairs : ∀ (k : ℕ) (hk : k ≤ M), ∀ pr ∈ gatherCzPairs w x hwx k hk, S pr.1 ∧ S pr.2.1 := by
    intro k; induction k with
    | zero => intro _ _ hp; nomatch hp
    | succ k ih =>
        intro hk pr hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨hw ⟨k, hk⟩, hx ⟨k, hk⟩⟩
        · exact ih (Nat.le_of_succ_le hk) pr hp'
  have hStar : DynWires S
      (pLiveStarCCZOfClean v (cGatherStrict1HotZ8 hM w x a hwa hxa) w x q a hwx haq) :=
    ⟨cw_seq hComp (cw_seq (cw_1 hq) (cw_seq (cw_cnot ha hq) (cw_1 hq))),
     dw_xUnload ha (hPairs M le_rfl) trivial⟩
  exact ⟨hHad, hStar, hHad⟩

/-- Classical-control `k`-plane `BellLo` prefix circuit (`k ≤ 24`). -/
def cBellLoPfxCirc {M D n : ℕ} (r : RouterReg M D n) (k : ℕ) (hk : k ≤ 24)
    (cLo _cHi : Fin M → ZMod 2) : Circuit n :=
    fixedBellVecCirc M k (fun i ↦ rHA r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) cLo (fun i p ↦
    rSys r p ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) (fun _i p ↦ hne_hA_sys r _ p)
theorem zgat_preservesKetPred_cBellLoPfxCirc {M D n : ℕ} (r : RouterReg M D n) (k : ℕ) (hk : k ≤ 24)
    (cLo cHi : Fin M → ZMod 2) {P : BitAssignment n → Prop}
    (hModKeep : ∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cBellLoPfxCirc r k hk cLo cHi).eval.1.mulVec ψ) :=
  (hcnotSupportedIn_fixedBellVec (S := AllPlaneMod r) cLo k
    (fun i ↦ rHA r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)
    (fun i p ↦ rSys r p ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)
    (fun _i p ↦ hne_hA_sys r _ p)
    (fun i ↦ ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩, Or.inr (Or.inr (Or.inl rfl))⟩)
    (fun i p _ ↦ ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r _ p).symm⟩)))⟩)).preservesKetPred
    hModKeep hψ

/-- Ghost `k`-plane `BellLo` pre-scatter unitary under `cLoAlways r`. -/
def uBellLoPreScatterPfx {M D n : ℕ} (r : RouterReg M D n) (k : ℕ) (hk : k ≤ 24) : Unitary (2 ^ n)
    :=
  uAlwaysLoGhost r (cBellLoPfxCirc r k hk) (zgat_preservesKetPred_cBellLoPfxCirc r k hk)

/-- Full 24-plane `BellLo` pre-scatter unitary under `cLoAlways r`. -/
abbrev uBellLoPreScatter {M D n : ℕ} (r : RouterReg M D n) : Unitary (2 ^ n) :=
    uBellLoPreScatterPfx r 24 le_rfl
private theorem zgat_fixedFanoutBits_eq_scatterBitsRec {n M : ℕ} (qH : Wire n)
    (w x : Fin M → Wire n) (_hx_inj : Function.Injective x) (γ : BitAssignment n) :
    fixedFanoutBits M (γ qH) (fun p ↦ γ (w p)) x γ = scatterBitsRec qH w x M le_rfl γ := by
  have hAux : ∀ (k : ℕ) (hk : k ≤ M), fixedFanoutBits k (γ qH)
      (fun p : Fin k ↦ γ (w ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩))
      (fun p : Fin k ↦ x ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) γ =
      scatterBitsRec qH w x k hk γ := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk; dsimp only [fixedFanoutBits, scatterBitsRec, Fin.val_last]
        have hCast : (fun p : Fin k ↦
            γ (w ⟨(Fin.castSucc p).val, Nat.lt_of_lt_of_le p.castSucc.isLt hk⟩)) =
            (fun p : Fin k ↦ γ (w ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_succ_le hk)⟩)) := rfl
        have hCastX : (fun p : Fin k ↦ x ⟨(Fin.castSucc p).val,
            Nat.lt_of_lt_of_le p.castSucc.isLt hk⟩) =
            (fun p : Fin k ↦ x ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_succ_le hk)⟩) := rfl
        rw [hCast, hCastX, ih (Nat.le_of_succ_le hk)]
        split_ifs with h1
        · rw [h1, mul_one]
        · rcases bit_cases (γ (w ⟨k, hk⟩)) with hw0 | hw1
          · rw [hw0, mul_zero, add_zero, Function.update_eq_self]
          · exact False.elim (h1 hw1)
  exact hAux M le_rfl


private theorem zgat_ket_inj {n : ℕ} {α β : BitAssignment n} (h : ket α = ket β) : α = β := by
  by_contra hne
  have h1 := congrFun h ((basisBitsEquiv n).symm α)
  have h2 : (basisBitsEquiv n).symm α ≠ (basisBitsEquiv n).symm β :=
    fun e ↦ hne ((basisBitsEquiv n).symm.injective e)
  simp [ket, basisState, h2] at h1

/--
Single-plane `2 * M`-`T` (`0 .TOFF`) `BellLo` pre-scatter
(`H (rHA r b)` + `pOneHotScatterStrict1HotDyn`) using `rHB r 0` as the clean ancilla.
-/
def pPlaneOneHotScatterLo {Var : Type} {M D n : ℕ} (hM0 : 0 < M) (v : Var)
    (r : RouterReg M D n) (b : Fin 24) : DynamicCircuit Var n :=
  .seq (.circuit (Circuit.H (rHA r b)))
    (pOneHotScatterStrict1HotDyn hM0 v (rCtrlLo r) (fun p ↦ rSys r p b)
      (rHA r b) (rHB r ⟨0, by decide⟩)
      (fun p ↦ rr_ne r (by have := p.isLt; have := b.isLt; dsimp [rCtrlLo, rSys, basePub]; omega))
      (fun p ↦ rr_ne r (by have := p.isLt; dsimp [rCtrlLo, rHB, basePub]; omega))
      (fun p ↦ rr_ne r (by have := p.isLt; have := b.isLt; dsimp [rSys, rHB]; omega))
      (rr_ne r (by have := b.isLt; dsimp [rHB, rHA]; omega)))

/-- `k`-plane loop of `pPlaneOneHotScatterLo` (`2 * M * k` `T` gates, `0 .TOFF`). -/
def pPlanesOneHotScatterLoLoop {Var : Type} {M D n : ℕ} (hM0 : 0 < M) (v : Var)
    (r : RouterReg M D n) : ∀ k : ℕ, k ≤ 24 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | k + 1, hk =>
      .seq (pPlanesOneHotScatterLoLoop hM0 v r k (Nat.le_of_succ_le hk))
        (pPlaneOneHotScatterLo hM0 v r ⟨k, hk⟩)

/--
`48 * M`-`T` (`0 .TOFF`) 24-plane `BellLo` pre-scatter on `pubCtrlLo r`: conjugates
`pPlanesOneHotScatterLoLoop` by `cFlipLo0` so `rCtrlLo r` carries the strict `1`-hot `cLoAlways r`.
-/
def pPlanesOneHotScatterLoPubCtrlLo {Var : Type} {M D n : ℕ} (hM0 : 0 < M) (v : Var)
    (r : RouterReg M D n) : DynamicCircuit Var n :=
  .seq (.circuit (cFlipLo0 hM0 r))
    (.seq (pPlanesOneHotScatterLoLoop hM0 v r 24 le_rfl) (.circuit (cFlipLo0 hM0 r)))

theorem count_pPlanesOneHotScatterLoLoop {Var : Type} {M D n : ℕ} (hM0 : 0 < M) (v : Var)
    (r : RouterReg M D n) :
    ∀ (k : ℕ) (hk : k ≤ 24),
      (pPlanesOneHotScatterLoLoop (Var := Var) hM0 v r k hk).count .T = 2 * M * k ∧
      (pPlanesOneHotScatterLoLoop (Var := Var) hM0 v r k hk).count .TOFF = 0 := by
  intro k
  induction k with
  | zero => exact fun _ ↦ ⟨by simp [pPlanesOneHotScatterLoLoop], rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨t1, f1⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨t2, f2⟩ := count_pOneHotScatterStrict1HotDyn (Var := Var) hM0 v
        (rCtrlLo r) (fun p ↦ rSys r p ⟨k, hk⟩) (rHA r ⟨k, hk⟩) (rHB r ⟨0, by decide⟩) _ _ _ _
      unfold pPlanesOneHotScatterLoLoop pPlaneOneHotScatterLo
      change _ + (0 + _) = 2 * M * (k + 1) ∧ _ + (0 + _) = 0
      rw [t1, t2, f1, f2]
      exact ⟨by ring, rfl⟩

theorem count_pPlanesOneHotScatterLoPubCtrlLo {Var : Type} {M D n : ℕ} (hM0 : 0 < M) (v : Var)
    (r : RouterReg M D n) :
    (pPlanesOneHotScatterLoPubCtrlLo hM0 v r).count .T = 48 * M ∧
    (pPlanesOneHotScatterLoPubCtrlLo hM0 v r).count .TOFF = 0 := by
  obtain ⟨tl, fl⟩ := count_pPlanesOneHotScatterLoLoop (Var := Var) hM0 v r 24 le_rfl
  unfold pPlanesOneHotScatterLoPubCtrlLo
  dsimp only [DynamicCircuit.count]
  rw [count_cFlipLo0_T hM0 r, count_cFlipLo0_TOFF hM0 r, tl, fl]
  exact ⟨by ring, rfl⟩

theorem dynWires_pPlanesOneHotScatterLoLoop {Var : Type} {M D n : ℕ} {S : Wire n → Prop}
    (hM0 : 0 < M) (v : Var) (r : RouterReg M D n)
    (hCtrl : ∀ p : Fin M, S (rCtrlLo r p))
    (hSys : ∀ (b : Fin 24) (p : Fin M), S (rSys r p b))
    (hHA : ∀ b : Fin 24, S (rHA r b))
    (hHB0 : S (rHB r ⟨0, by decide⟩)) :
    ∀ (k : ℕ) (hk : k ≤ 24), DynWires S (pPlanesOneHotScatterLoLoop hM0 v r k hk)
  | 0, _ => trivial
  | k + 1, hk =>
      ⟨dynWires_pPlanesOneHotScatterLoLoop hM0 v r hCtrl hSys hHA hHB0 k (Nat.le_of_succ_le hk),
       cw_1 (hHA ⟨k, hk⟩),
       zgat_dynWires_pOneHotScatterStrict1HotDyn hM0 v _ _ _ _ _ _ _ _
         hCtrl (fun p ↦ hSys ⟨k, hk⟩ p) (hHA ⟨k, hk⟩) hHB0⟩

theorem dynWires_pPlanesOneHotScatterLoPubCtrlLo {Var : Type} {M D n : ℕ} {S : Wire n → Prop}
    (hM0 : 0 < M) (v : Var) (r : RouterReg M D n)
    (hHas1 : S (rHas1 r))
    (hCtrl : ∀ p : Fin M, S (rCtrlLo r p))
    (hSys : ∀ (b : Fin 24) (p : Fin M), S (rSys r p b))
    (hHA : ∀ b : Fin 24, S (rHA r b))
    (hHB0 : S (rHB r ⟨0, by decide⟩)) :
    DynWires S (pPlanesOneHotScatterLoPubCtrlLo hM0 v r) := by
  have hFl : CircWires S (cFlipLo0 hM0 r) :=
    cw_seq (cw_1 (hCtrl ⟨0, hM0⟩)) (cw_cnot hHas1 (hCtrl ⟨0, hM0⟩))
  exact ⟨hFl, dynWires_pPlanesOneHotScatterLoLoop hM0 v r hCtrl hSys hHA hHB0 24 le_rfl, hFl⟩

private theorem zgat_validZeroGatedWithoutHA_update_j {M D n : ℕ}
    (r : RouterReg M D n) (j : Fin (routerWidth M D))
    (hj : (50 + 2 * D ≤ j.val ∧ j.val < 74 + 2 * D) ∨ (98 + 2 * D ≤ j.val ∧ j.val < basePub M D))
    (β : BitAssignment n) (v : ZMod 2) (hβ : ValidZeroGatedWithoutHA r β) :
    ValidZeroGatedWithoutHA r (Function.update β (r j) v) := by
  have wUpd {w} (hne : w ≠ r j) : Function.update β (r j) v w = β w :=
    Function.update_of_ne hne v β
  have hPub : ∀ w, PubCtrlSet r w → Function.update β (r j) v w = β w := by
    rintro _ ⟨k, _, rfl⟩
    exact wUpd (rr_ne r (by omega))
  rcases pubCtrlSet_roles r with ⟨r1, r2, rI1, rI2⟩
  have hH1 := hPub _ r1
  have hH2 := hPub _ r2
  have hI1 := idxValD_congr (rIdx1 r) fun d ↦ hPub _ (rI1 d)
  have hI2 := idxValD_congr (rIdx2 r) fun d ↦ hPub _ (rI2 d)
  rcases hβ with ⟨h1, h2, h3, hB, hP, z1, z2, hLt⟩
  have hB' (b' : Fin 24) : rBufLo r b' ≠ r j ∧ rBufHi r b' ≠ r j ∧ rHB r b' ≠ r j := by
    have := b'.isLt
    refine ⟨rr_ne r ?_, rr_ne r ?_, rr_ne r ?_⟩
    all_goals
      dsimp [rBufLo, rBufHi, rHB]
      omega
  refine ⟨fun e ↦ hH1.trans (h1 (hH2.symm.trans e)), fun e ↦ hI1 ▸ h2 (hH1.symm.trans e),
    fun e ↦ hI2 ▸ h3 (hH2.symm.trans e),
    fun b' ↦ ⟨(wUpd (hB' b').1).trans (hB b').1, (wUpd (hB' b').2.1).trans (hB b').2.1,
      (wUpd (hB' b').2.2).trans (hB b').2.2⟩,
    fun w hw ↦ (wUpd fun e ↦ ?_).trans (hP w hw),
    fun e d ↦ (hPub _ (rI1 d)).trans (z1 (hH1.symm.trans e) d),
    fun e d ↦ (hPub _ (rI2 d)).trans (z2 (hH2.symm.trans e) d),
    fun e ↦ hI1.symm ▸ hI2.symm ▸ hLt (hH2.symm.trans e)⟩
  subst e
  have hm := (mem_sPrivCleanSet_iff r j).mp hw
  dsimp [basePub] at hm hj
  omega

private theorem zgat_preservesKetPred_uBellLoPreScatterPfx {M D n : ℕ}
    (r : RouterReg M D n) (k : ℕ) (hk : k ≤ 24) (β : BitAssignment n)
    (hβ : ValidZeroGatedWithoutHA r β) :
    PreservesKetPred (fun α ↦ ValidZeroGatedWithoutHA r α ∧ ∀ w, PubCtrlSet r w → α w = β w)
      ((uBellLoPreScatterPfx r k hk).1.mulVec (ket β)) := by
  have hb : basePub M D = 98 + 2 * D + 24 * M := rfl
  dsimp only [uBellLoPreScatterPfx]
  rw [show (uAlwaysLoGhost r (cBellLoPfxCirc r k hk) _).1.mulVec (ket β) =
      (cBellLoPfxCirc r k hk (cLoAlways r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) from
      uAlwaysLoGhostMat_mulVec_ket r (cBellLoPfxCirc r k hk) β]
  refine (hcnotSupportedIn_fixedBellVec
    (S := fun u ↦ (∃ b : Fin 24, u = rHA r b) ∨ (∃ (b : Fin 24) (p : Fin M), u = rSys r p b))
    (cLoAlways r β) k
    (fun i ↦ rHA r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)
    (fun i p ↦ rSys r p ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)
    (fun _i p ↦ hne_hA_sys r _ p)
    (fun i ↦ Or.inl ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩, rfl⟩)
    (fun i p _ ↦ Or.inr ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩, p, rfl⟩)).preservesKetPred
    (fun {u} hu α v ⟨hV, hPub⟩ ↦ ?_) (preservesKetPred_ket ⟨hβ, fun _ _ ↦ rfl⟩)
  rcases hu with ⟨b, rfl⟩ | ⟨b, p, rfl⟩
  · exact ⟨zgat_validZeroGatedWithoutHA_update_rHA r b α v hV,
      fun w hw ↦ (Function.update_of_ne (zgat_rHA_not_pubCtrlSet r b w hw) v α).trans (hPub w hw)⟩
  · refine ⟨zgat_validZeroGatedWithoutHA_update_j r _
      (Or.inr ⟨by dsimp [rSys]; omega,
          by have := p.isLt; have := b.isLt; dsimp [rSys]; rw [hb]; omega⟩)
      α v hV, fun w ⟨m, hm, hw⟩ ↦ ?_⟩
    subst hw
    have hne : r m ≠ rSys r p b :=
      rr_ne r (by have := p.isLt; have := b.isLt; dsimp [rSys]; omega)
    exact (Function.update_of_ne hne v α).trans (hPub _ ⟨m, hm, rfl⟩)

theorem supportedOn_validZeroGatedWithoutHA_uBellLoPreScatterPfx {M D n : ℕ}
    (r : RouterReg M D n) (k : ℕ) (hk : k ≤ 24) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedWithoutHA r) R) :
    SupportedOn (ValidZeroGatedWithoutHA r) ((uBellLoPreScatterPfx r k hk).1 * R) := by
  intro A B hAB
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR (A * (uBellLoPreScatterPfx r k hk).1) (B * (uBellLoPreScatterPfx r k hk).1) fun β hβ ↦
      ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact zgat_preservesKetPred_uBellLoPreScatterPfx r k hk β hβ A B fun α hα ↦ hAB α hα.1

theorem supportedOn_validZeroGatedWithoutHA_uBellLoPreScatter {M D n : ℕ}
    (r : RouterReg M D n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SupportedOn (ValidZeroGatedWithoutHA r) ((uBellLoPreScatter r).1 * R) :=
  supportedOn_validZeroGatedWithoutHA_uBellLoPreScatterPfx r 24 le_rfl R
    (fun A B hAB ↦ hR A B fun β hβ ↦ hAB β ((zgat_validZeroGatedWithoutHA_iff r β).mpr hβ).1)

/--
Generic `SubspaceStep` for `pPlanesOneHotScatterLoLoop` on any ket-mapping unitary `U_c`
acting independently of `AllPlaneMod r` whose output on `rCtrlLo r` equals `cLoAlways r`.
-/
theorem subspaceStep_pPlanesOneHotScatterLoLoop_of_ketMap
    {Var : Type} [Fintype Var] [DecidableEq Var] {M D n : ℕ}
    (hM0 : 0 < M) (v : Var) (r : RouterReg M D n)
    (U_c : Unitary (2 ^ n)) (f_c : BitAssignment n → BitAssignment n)
    (hUcKet : ∀ α, U_c.1.mulVec (ket α) = ket (f_c α))
    (hInd : ActsIndepOf (AllPlaneMod r) U_c)
    (hFcLo : ∀ α, ValidZeroGatedWithoutHA r α → ∀ p : Fin M, f_c α (rCtrlLo r p) = cLoAlways r α p)
    (R : Operator (2 ^ n)) (hRW : SupportedOn (ValidZeroGatedWithoutHA r) R)
    (k : ℕ) (hk : k ≤ 24) :
    SubspaceStep (Var := Var)
      (U_c.1 * R)
      (U_c.1 * ((uBellLoPreScatterPfx r k hk).1 * R))
      (pPlanesOneHotScatterLoLoop hM0 v r k hk) := by
  obtain ⟨G, hGKet, hGUpd⟩ := hInd
  have hFG (δ : BitAssignment n) : f_c δ = G δ :=
    zgat_ket_inj ((hUcKet δ).symm.trans (hGKet δ))
  have hFcUpd (q : Wire n) (hq : AllPlaneMod r q) (δ : BitAssignment n) (val : ZMod 2) :
      f_c (Function.update δ q val) = Function.update (f_c δ) q val := by
    rw [hFG, hFG, hGUpd q hq δ val]
  have hFcSame (q : Wire n) (hq : AllPlaneMod r q) (δ : BitAssignment n) : f_c δ q = δ q := by
    simpa using congrFun (hFcUpd q hq δ (δ q)) q
  have hModHA (b : Fin 24) : AllPlaneMod r (rHA r b) := ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩
  have hModHB0 : AllPlaneMod r (rHB r ⟨0, by decide⟩) :=
    ⟨⟨0, by decide⟩, Or.inr (Or.inr (Or.inr (Or.inl (planeOfRouter_hB r ⟨0, by decide⟩).symm)))⟩
  have hModSys (b : Fin 24) (p : Fin M) : AllPlaneMod r (rSys r p b) :=
    ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩
  have hFcProps (α : BitAssignment n) (hα : ValidZeroGatedWithoutHA r α) :
      StrictOneHotMask (rCtrlLo r) (f_c α) ∧ f_c α (rHB r ⟨0, by decide⟩) = 0 := by
    have hIdxLt : idxValD (rIdx1 r) α < M := by
      rcases bit_cases (α (rHas1 r)) with h0 | h1
      · exact idxValD_eq_zero_of_zero (rIdx1 r) (hα.2.2.2.2.2.1 h0) ▸ hM0
      · exact hα.2.1 h1
    refine ⟨⟨⟨idxValD (rIdx1 r) α, hIdxLt⟩, ?_, fun p hp ↦ ?_⟩,
      (hFcSame _ hModHB0 α).trans (hα.2.2.2.1 ⟨0, by decide⟩).2.2⟩
    · simp [hFcLo α hα, cLoAlways]
    · simp [hFcLo α hα, cLoAlways, Fin.val_ne_of_ne hp]
  have hGhost (m : ℕ) (hm : m ≤ 24) (β : BitAssignment n) :
      (uBellLoPreScatterPfx r m hm).1.mulVec (ket β) =
        (cBellLoPfxCirc r m hm (cLoAlways r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) :=
    uAlwaysLoGhostMat_mulVec_ket r (cBellLoPfxCirc r m hm) β
  induction k with
  | zero =>
      have h0 : (uBellLoPreScatterPfx r 0 hk).1 = 1 :=
        matrix_ext_ket fun β ↦ by
          simpa [cBellLoPfxCirc, fixedBellVecCirc, Circuit.eval_identity] using hGhost 0 hk β
      exact subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) (U_c.1 * R) .identity)
        (by simp [Circuit.eval_identity, h0])
  | succ k ih =>
      let hk' := Nat.le_of_succ_le hk
      let bk : Fin 24 := ⟨k, hk⟩
      let R_k := U_c.1 * ((uBellLoPreScatterPfx r k hk').1 * R)
      have hNe6 (p₁ p₂ : Fin M) :
          rCtrlLo r p₁ ≠ rHA r bk ∧ rHB r ⟨0, by decide⟩ ≠ rHA r bk ∧
          rCtrlLo r p₁ ≠ rSys r p₂ bk ∧ rHA r bk ≠ rSys r p₂ bk ∧
          rCtrlLo r p₁ ≠ rHB r ⟨0, by decide⟩ ∧ rSys r p₂ bk ≠ rHB r ⟨0, by decide⟩ := by
        have := p₁.isLt
        have := p₂.isLt
        have := bk.isLt
        refine ⟨rr_ne r ?_, rr_ne r ?_, rr_ne r ?_, rr_ne r ?_, rr_ne r ?_, rr_ne r ?_⟩
        all_goals
          dsimp [rCtrlLo, rSys, rHA, rHB, basePub]
          omega
      have hHBHA : rHB r ⟨0, by decide⟩ ≠ rHA r bk := (hNe6 ⟨0, hM0⟩ ⟨0, hM0⟩).2.1
      have hSuppRk : SupportedOn
          (fun γ ↦ StrictOneHotMask (rCtrlLo r) γ ∧ γ (rHB r ⟨0, by decide⟩) = 0) R_k :=
        supportedOn_ketMap hUcKet hFcProps
          (supportedOn_validZeroGatedWithoutHA_uBellLoPreScatterPfx r k hk' R hRW)
      have hSuppHk := zgat_supportedOn_H (rHA r bk)
        (fun γ z ⟨⟨p₀, h1, h0⟩, hb0⟩ ↦
          ⟨⟨p₀, (Function.update_of_ne (hNe6 p₀ p₀).1 z γ).trans h1,
            fun p hp ↦ (Function.update_of_ne (hNe6 p p).1 z γ).trans (h0 p hp)⟩,
           (Function.update_of_ne hHBHA z γ).trans hb0⟩) hSuppRk
      have sH := subspaceStep_of_circuit (Var := Var) R_k (Circuit.H (rHA r bk))
      have hSysInj : Function.Injective (fun p : Fin M ↦ rSys r p bk) := fun p₁ p₂ e ↦ by
        have hv := congrArg Fin.val (r.wires.injective e)
        have := p₁.isLt
        have := p₂.isLt
        have := bk.isLt
        dsimp [rSys] at hv
        exact Fin.ext (by omega)
      have hCtrlNeSys (p₁ p₂ : Fin M) := (hNe6 p₁ p₂).2.2.1
      have hHANeSys (p : Fin M) := (hNe6 p p).2.2.2.1
      obtain ⟨sSc, _⟩ := subspaceStep_pOneHotScatterStrict1HotDyn (Var := Var) hM0 v
        (rCtrlLo r) (fun p ↦ rSys r p bk) (rHA r bk) (rHB r ⟨0, by decide⟩) hSysInj
        hCtrlNeSys (fun p ↦ (hNe6 p p).2.2.2.2.1) (fun p ↦ (hNe6 p p).2.2.2.2.2)
        hHANeSys hHBHA ((Circuit.H (rHA r bk)).eval.1 * R_k) hSuppHk
      refine (ih hk').seq (subspaceStep_congr_out (sH.seq sSc) ?_)
      dsimp only [R_k]
      simp only [← Matrix.mul_assoc]
      refine hRW _ _ fun β hβ ↦ ?_
      have hStepEq : ∀ α : BitAssignment n,
          (ValidZeroGatedWithoutHA r α ∧ ∀ w, PubCtrlSet r w → α w = β w) →
          ((scatterUnitary (rHA r bk) (rCtrlLo r) (fun p ↦ rSys r p bk) hSysInj
              hHANeSys hCtrlNeSys).1 *
            (Circuit.H (rHA r bk)).eval.1 * U_c.1).mulVec (ket α) =
          (U_c.1 * (fixedBell1Circ M (rHA r bk) (cLoAlways r β) (fun p ↦ rSys r p bk)
            (hne_hA_sys r bk)).eval.1).mulVec (ket α) := by
        rintro α ⟨hαV, hαPub⟩
        have hFanFc (vSrc : ZMod 2) (δ : BitAssignment n) :
            f_c (fixedFanoutBits M vSrc (cLoAlways r β) (fun p ↦ rSys r p bk) δ) =
            fixedFanoutBits M vSrc (cLoAlways r β) (fun p ↦ rSys r p bk) (f_c δ) := by
          suffices ∀ (m : ℕ) (hm : m ≤ M),
              f_c (fixedFanoutBits m vSrc
                (fun p : Fin m ↦ cLoAlways r β ⟨p.val, Nat.lt_of_lt_of_le p.isLt hm⟩)
                (fun p : Fin m ↦ rSys r ⟨p.val, Nat.lt_of_lt_of_le p.isLt hm⟩ bk) δ) =
              fixedFanoutBits m vSrc
                (fun p : Fin m ↦ cLoAlways r β ⟨p.val, Nat.lt_of_lt_of_le p.isLt hm⟩)
                (fun p : Fin m ↦ rSys r ⟨p.val, Nat.lt_of_lt_of_le p.isLt hm⟩ bk) (f_c δ) from
            this M le_rfl
          intro m
          induction m with
          | zero => exact fun _ ↦ rfl
          | succ m ihm =>
              intro hm
              dsimp only [fixedFanoutBits, Fin.val_last, Fin.castSucc, Fin.castAdd, Fin.castLE,
                Fin.castLT]
              split_ifs
              · rw [hFcUpd _ (hModSys bk ⟨m, hm⟩), ← ihm (Nat.le_of_succ_le hm),
                    hFcSame _ (hModSys bk ⟨m, hm⟩)]
              · exact ihm (Nat.le_of_succ_le hm)
        have hBr : ∀ z : ZMod 2,
            (scatterUnitary (rHA r bk) (rCtrlLo r)
                (fun p ↦ rSys r p bk) hSysInj hHANeSys hCtrlNeSys).1.mulVec
              (ket (Function.update (f_c α) (rHA r bk) z)) =
            U_c.1.mulVec ((fixedFanoutCirc M (rHA r bk) (cLoAlways r β) (fun p ↦ rSys r p bk)
              (hne_hA_sys r bk)).eval.1.mulVec (ket (Function.update α (rHA r bk) z))) := by
          intro z
          let αz := Function.update α (rHA r bk) z
          have hFcAz : Function.update (f_c α) (rHA r bk) z = f_c αz :=
            (hFcUpd _ (hModHA bk) α z).symm
          have hAzV : ValidZeroGatedWithoutHA r αz :=
            zgat_validZeroGatedWithoutHA_update_rHA r bk α z hαV
          have hAzLo : (fun p : Fin M ↦ f_c αz (rCtrlLo r p)) = cLoAlways r β :=
            (funext (hFcLo αz hAzV)).trans <| by
              change cLoAlways r αz = cLoAlways r β
              rw [← pubCtrlLoAlways_eq_cLoAlways, ← pubCtrlLoAlways_eq_cLoAlways]
              exact pubCtrlLoAlways_congr r fun w hw ↦
                (Function.update_of_ne (zgat_rHA_not_pubCtrlSet r bk w hw) z α).trans (hαPub w hw)
          have hAzHA : f_c αz (rHA r bk) = αz (rHA r bk) := hFcSame _ (hModHA bk) αz
          rw [hFcAz, scatterUnitary_mulVec_ket,
              ← zgat_fixedFanoutBits_eq_scatterBitsRec (rHA r bk) (rCtrlLo r) _ hSysInj (f_c αz),
              hAzLo, hAzHA, fixedFanoutCirc_mulVec_ket, hUcKet, hFanFc]
        have hH0 : f_c α (rHA r bk) = α (rHA r bk) := hFcSame _ (hModHA bk) α
        dsimp only [fixedBell1Circ]
        simp only [← Matrix.mulVec_mulVec, eval_seq_mulVec]
        rw [hUcKet α, ← zgat_ket_dc (f_c α), DynCircExt.gad_ket_H,
            ← zgat_ket_dc α, DynCircExt.gad_ket_H]
        simp only [zgat_ket_dc, Matrix.mulVec_smul, Matrix.mulVec_add]
        rw [hH0, hBr 0, hBr 1]
      have hPfxStep : (uBellLoPreScatterPfx r (k + 1) hk).1.mulVec (ket β) =
          (fixedBell1Circ M (rHA r bk) (cLoAlways r β) (fun p ↦ rSys r p bk)
            (hne_hA_sys r bk)).eval.1.mulVec ((uBellLoPreScatterPfx r k hk').1.mulVec (ket β)) := by
        rw [hGhost (k + 1) hk β, hGhost k hk' β]
        dsimp only [cBellLoPfxCirc, fixedBellVecCirc, Fin.val_last]
        rw [eval_seq_mulVec]
        rfl
      rw [zgat_ket_sr β,
          ← Matrix.mulVec_mulVec (ket β) (_ * _ * _) (uBellLoPreScatterPfx r k hk').1,
          ← Matrix.mulVec_mulVec (ket β) U_c.1 (uBellLoPreScatterPfx r (k + 1) hk).1,
          hPfxStep, Matrix.mulVec_mulVec _ U_c.1 _]
      exact zgat_preservesKetPred_uBellLoPreScatterPfx r k hk' β hβ _ _ fun α hα ↦ hStepEq α hα

private theorem zgat_actsIndepOf_allPlaneMod_uXorPubLo {n : ℕ} (r : RouterReg 187 8 n) :
    ActsIndepOf (AllPlaneMod r) (uXorPubLo r) := by
  have hSpec := vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r)
  refine ⟨vecToggleBits (rCtrlLo r) (pubCtrlLo r), uVecToggle_mulVec_ket _ _ _ _,
    fun q hq α val ↦ ?_⟩
  have hNeOut (p : Fin 187) : q ≠ rCtrlLo r p := fun e ↦
    not_allPlaneMod_of_idx r (Or.inr (by
      dsimp [rCtrlLo, basePub]
      omega)) (e ▸ hq)
  have hDelUpd : pubCtrlLo r (Function.update α q val) = pubCtrlLo r α :=
    (pubCtrl_congr r fun _ ⟨k, hk, hw⟩ ↦ hw ▸ Function.update_of_ne
      (fun (e : r k = q) ↦ not_allPlaneMod_of_idx r (Or.inl hk) (e.symm ▸ hq)) val α).1
  funext u
  by_cases hw : ∃ p : Fin 187, u = rCtrlLo r p
  · obtain ⟨p, rfl⟩ := hw
    have hu := (hNeOut p).symm
    rw [(hSpec _ _).1 p, hDelUpd, Function.update_of_ne hu, Function.update_of_ne hu,
        (hSpec _ α).1 p]
  · have nw (p : Fin 187) : u ≠ rCtrlLo r p := fun e ↦ hw ⟨p, e⟩
    rw [(hSpec _ _).2 u nw]
    rcases eq_or_ne u q with rfl | hu
    · simp only [Function.update_self]
    · rw [Function.update_of_ne hu, Function.update_of_ne hu, (hSpec _ α).2 u nw]

theorem flipLo0Bits_rCtrlLo_eq_cLoAlways {M D n : ℕ} (hM0 : 0 < M)
    (r : RouterReg M D n) (α γ : BitAssignment n)
    (hIdx1Zero : α (rHas1 r) = 0 → idxValD (rIdx1 r) α = 0)
    (hHas1 : γ (rHas1 r) = α (rHas1 r))
    (hLo : ∀ q : Fin M,
      γ (rCtrlLo r q) = if q.val = idxValD (rIdx1 r) α then α (rHas1 r) else 0)
    (p : Fin M) : flipLo0Bits hM0 r γ (rCtrlLo r p) = cLoAlways r α p := by
  by_cases hp0 : p = ⟨0, hM0⟩
  · subst hp0
    simp only [flipLo0Bits, cLoAlways, Function.update_self, hLo ⟨0, hM0⟩, hHas1]
    rcases bit_cases (α (rHas1 r)) with h0 | h1
    · simp [h0, hIdx1Zero h0]
    · by_cases hz : (0 : ℕ) = idxValD (rIdx1 r) α <;> simp [h1, hz, CharTwo.add_self_eq_zero]
  · have hpNz : p.val ≠ 0 := fun e ↦ hp0 (Fin.ext e)
    rw [flipLo0Bits_other hM0 r _ (rCtrlLo_inj_ne r p _ hp0), hLo p]
    rcases bit_cases (α (rHas1 r)) with h0 | h1
    · simp [cLoAlways, hIdx1Zero h0, hpNz]
    · simp [cLoAlways, h1]

/--
Closed `SubspaceStep` theorem for `pPlanesOneHotScatterLoPubCtrlLo` (`48 * 187 = 8,976` `T` ,
`0 .TOFF` ).
-/
theorem subspaceStep_pPlanesOneHotScatterLoPubCtrlLo
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (hM0 : 0 < 187) (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SubspaceStep (Var := Var)
      ((uXorPubLo r).1 * R)
      ((uXorPubLo r).1 * ((uBellLoPreScatter r).1 * R))
      (pPlanesOneHotScatterLoPubCtrlLo hM0 v r) := by
  let F_fl := (cFlipLo0 hM0 r).eval
  let U_c : Unitary (2 ^ n) := F_fl * uXorPubLo r
  let f_c (α : BitAssignment n) : BitAssignment n :=
    flipLo0Bits hM0 r (vecToggleBits (rCtrlLo r) (pubCtrlLo r) α)
  have hUcKet (α : BitAssignment n) : U_c.1.mulVec (ket α) = ket (f_c α) := by
    dsimp only [U_c, F_fl, f_c, uXorPubLo]
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, uVecToggle_mulVec_ket, cFlipLo0_mulVec_ket]
  have hFcLo (α : BitAssignment n) (hα : ValidZeroGatedWithoutHA r α) (p : Fin 187) :
      f_c α (rCtrlLo r p) = cLoAlways r α p :=
    flipLo0Bits_rCtrlLo_eq_cLoAlways hM0 r α _
      (fun h0 ↦ idxValD_eq_zero_of_zero (rIdx1 r) (hα.2.2.2.2.2.1 h0))
      ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2 _
        (fun p' ↦ rr_ne r (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide : 0 < 4624)
          (Nat.le_add_right 4624 p'.val)))))
      (fun q ↦ by
        rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).1 q,
            hα.2.2.2.2.1 _ ((mem_sPrivCleanSet_iff r _).mpr
              (Nat.le_trans (by decide) (Nat.le_add_right 4624 q.val))),
            zero_add]
        exact cond_nat_beq _ _ _ _) p
  have eqOut : F_fl.1 * (U_c.1 * ((uBellLoPreScatter r).1 * R)) =
      (uXorPubLo r).1 * ((uBellLoPreScatter r).1 * R) := by
    dsimp only [U_c, F_fl]
    rw [Submonoid.coe_mul, ← Matrix.mul_assoc _ _ ((uBellLoPreScatter r).1 * R),
        ← Matrix.mul_assoc (cFlipLo0 hM0 r).eval.1 (cFlipLo0 hM0 r).eval.1,
        cFlipLo0_eval_sq_eq_one hM0 r, Matrix.one_mul]
  exact (subspaceStep_congr_out
      (subspaceStep_of_circuit (Var := Var) ((uXorPubLo r).1 * R) (cFlipLo0 hM0 r))
      (by simp only [U_c, F_fl, Submonoid.coe_mul, Matrix.mul_assoc])).seq
    ((subspaceStep_pPlanesOneHotScatterLoLoop_of_ketMap hM0 v r U_c f_c hUcKet
        (zgat_actsIndepOf_mul (actsIndepOf_allPlaneMod_cFlipLo0 hM0 r)
          (zgat_actsIndepOf_allPlaneMod_uXorPubLo r))
        hFcLo R
        (fun A B hAB ↦ hR A B fun β hβ ↦
          hAB β ((zgat_validZeroGatedWithoutHA_iff r β).mpr hβ).1)
        24 le_rfl).seq
      (subspaceStep_congr_out
        (subspaceStep_of_circuit (Var := Var) (U_c.1 * ((uBellLoPreScatter r).1 * R))
          (cFlipLo0 hM0 r)) eqOut))

/--
Closed `SubspaceStep` theorem for the `2,256-T` (`0 .TOFF`) 24-plane nuclear `BellLo`
pre-scatter `pPlanesOneHotScatterLoLoop hM0 v rn 24 le_rfl` on
`U_mid.1 * R` (`U_mid = (cFlipLo0 hM0 rn).eval * (ULo * UHi)`).
-/
theorem subspaceStep_pPlanesOneHotScatterLoLoop_nuc
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (hM0 : 0 < 47) (v : Var) (rn : RouterReg 47 6 n)
    (R : Operator (2 ^ n)) (hR : SupportedOn (ValidZeroGatedSortedRouterInput rn) R) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    let U_mid : Unitary (2 ^ n) := (cFlipLo0 hM0 rn).eval * (ULo * UHi)
    SubspaceStep (Var := Var)
      (U_mid.1 * R)
      (U_mid.1 * ((uBellLoPreScatter rn).1 * R))
      (pPlanesOneHotScatterLoLoop hM0 v rn 24 le_rfl) := by
  intro dLo dHi ULo UHi U_mid
  have hRW : SupportedOn (ValidZeroGatedWithoutHA rn) R :=
    fun A B hAB ↦ hR A B fun β hβ ↦ hAB β ((zgat_validZeroGatedWithoutHA_iff rn β).mpr hβ).1
  let f_hi (α : BitAssignment n) := toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) α
  let f_lh (α : BitAssignment n) := toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (f_hi α)
  let f_c (α : BitAssignment n) := flipLo0Bits hM0 rn (f_lh α)
  have hUcKet (α : BitAssignment n) : U_mid.1.mulVec (ket α) = ket (f_c α) := by
    dsimp only [U_mid, ULo, UHi, f_c, f_lh, f_hi]
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket, cFlipLo0_mulVec_ket]
  have ⟨hIndLo, hIndHi⟩ :
      ActsIndepOf (AllPlaneMod rn) ULo ∧ ActsIndepOf (AllPlaneMod rn) UHi := by
    refine ⟨actsIndepOf_allPlaneMod_uOneHotToggle rn dLo.has_ne_out dLo.idx_ne_out
        (not_allPlaneMod_of_idx rn (Or.inl ?_)) (fun d ↦ not_allPlaneMod_of_idx rn (Or.inl ?_))
        (wOutLoN48_mem (S := fun u ↦ ¬ AllPlaneMod rn u) rn
          (fun p ↦ not_allPlaneMod_of_idx rn (Or.inr ?_))
          (not_allPlaneMod_of_idx rn (Or.inr ?_))),
      actsIndepOf_allPlaneMod_uOneHotToggle rn dHi.has_ne_out dHi.idx_ne_out
        (not_allPlaneMod_of_idx rn (Or.inl ?_)) (fun d ↦ not_allPlaneMod_of_idx rn (Or.inl ?_))
        (wOutHiN48_mem (S := fun u ↦ ¬ AllPlaneMod rn u) rn
          (fun p ↦ not_allPlaneMod_of_idx rn (Or.inr ?_))
          (not_allPlaneMod_of_idx rn (Or.inr ?_)))⟩
    all_goals
      dsimp [rHas1, rRawHas2, rIdx1, rIdx2, rCtrlLo, rCtrlHi, basePub, routerWidth]
      omega
  have hInd := zgat_actsIndepOf_mul (actsIndepOf_allPlaneMod_cFlipLo0 hM0 rn)
    (zgat_actsIndepOf_mul hIndLo hIndHi)
  have hFcLo (α : BitAssignment n) (hα : ValidZeroGatedWithoutHA rn α) (p : Fin 47) :
      f_c α (rCtrlLo rn p) = cLoAlways rn α p := by
    have hIdx1Zero (h0 : α (rHas1 rn) = 0) :=
      idxValD_eq_zero_of_zero (rIdx1 rn) (hα.2.2.2.2.2.1 h0)
    have hIdxLt : idxValD (rIdx1 rn) α < 47 := by
      rcases bit_cases (α (rHas1 rn)) with h0 | h1
      · exact hIdx1Zero h0 ▸ hM0
      · exact hα.2.1 h1
    have hHiNe : (∀ j, rHas1 rn ≠ wOutHiN48 rn j) ∧ (∀ d j, rIdx1 rn d ≠ wOutHiN48 rn j) := by
      refine ⟨wOutHiN48_mem (S := fun u ↦ rHas1 rn ≠ u) rn (fun q ↦ rr_ne rn ?_) (rr_ne rn ?_),
        fun d ↦ wOutHiN48_mem (S := fun u ↦ rIdx1 rn d ≠ u) rn (fun q ↦ rr_ne rn ?_) (rr_ne rn ?_)⟩
      all_goals
        dsimp [rHas1, rIdx1, rCtrlHi, basePub]
        omega
    have hHas1Hi : f_hi α (rHas1 rn) = α (rHas1 rn) := toggleOneHotBits_apply_other α hHiNe.1
    have hHas1Lh : f_lh α (rHas1 rn) = α (rHas1 rn) :=
      (toggleOneHotBits_apply_other (f_hi α) dLo.has_ne_out).trans hHas1Hi
    have hI1Hi : idxValD (rIdx1 rn) (f_hi α) = idxValD (rIdx1 rn) α :=
      idxValD_congr (rIdx1 rn) fun d ↦ toggleOneHotBits_apply_other α (hHiNe.2 d)
    have hHiLo0 (j : Fin 48) : f_hi α (wOutLoN48 rn j) = 0 := by
      refine (toggleOneHotBits_apply_other α (hne_wOutLoN48_wOutHiN48 rn j)).trans ?_
      refine wOutLoN48_mem (S := fun u ↦ α u = 0) rn
        (fun q ↦ hα.2.2.2.2.1 _ ((mem_sPrivCleanSet_iff rn _).mpr ?_))
        (hα.2.2.2.2.1 _ ((mem_sPrivCleanSet_iff rn _).mpr ?_)) j
      all_goals
        dsimp [rCtrlLo, basePub]
        omega
    have hLhLo (q : Fin 47) :
        f_lh α (rCtrlLo rn q) = if q.val = idxValD (rIdx1 rn) α then α (rHas1 rn) else 0 := by
      let jq : Fin 48 := ⟨q.val, Nat.lt_of_lt_of_le q.isLt (by decide)⟩
      have h47 : 47 ≤ 48 := by decide
      rw [← padWires_cast h47 (rCtrlLo rn) (padLoN48 rn) q]
      dsimp only [f_lh]
      rw [toggleOneHotBits_apply_out dLo.out_inj hHiLo0
            (hI1Hi ▸ Nat.lt_trans hIdxLt (by decide)) jq, hI1Hi, hHas1Hi]
      simp only [jq, eq_comm]
    exact flipLo0Bits_rCtrlLo_eq_cLoAlways hM0 rn α (f_lh α) hIdx1Zero hHas1Lh hLhLo p
  exact subspaceStep_pPlanesOneHotScatterLoLoop_of_ketMap
    hM0 v rn U_mid f_c hUcKet hInd hFcLo R hRW 24 le_rfl

-- Section 2B: `48`-CNOT (`0 T`, `0 .TOFF`) Post-Gather `BellLo` Fixup
-- (`cFixupBellLoFromGatherCirc`) & `uBellLoCopyHiAlwaysLoConj` Operator Identity

/-- Single-plane `2`-CNOT post-gather fixup `CNOT (rHA -> rBufLo) ;;ᶜ CNOT (rBufLo -> rHA)`. -/
def cFixupBellLoPlaneCirc {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) : Circuit n :=
  Circuit.CNOT (rHA r b) (rBufLo r b) (rr_ne r (by have := b.isLt; dsimp [rHA, rBufLo]; omega)) ;;ᶜ
  Circuit.CNOT (rBufLo r b) (rHA r b) (rr_ne r (by have := b.isLt; dsimp [rBufLo, rHA]; omega))

/-- `m`-plane prefix of `cFixupBellLoPlaneCirc` (`0 T`, `0 .TOFF`). -/
def cFixupBellLoPfxCirc {M D n : ℕ} (r : RouterReg M D n) : ∀ m : ℕ, m ≤ 24 → Circuit n
  | 0, _ => .identity
  | m + 1, hm => cFixupBellLoPfxCirc r m (Nat.le_of_succ_le hm) ;;ᶜ cFixupBellLoPlaneCirc r ⟨m, hm⟩

/-- `48`-CNOT (`0 T`, `0 .TOFF`) post-gather `BellLo` fixup across all `24` planes. -/
abbrev cFixupBellLoFromGatherCirc {M D n : ℕ} (r : RouterReg M D n) : Circuit n :=
  cFixupBellLoPfxCirc r 24 le_rfl

theorem count_cFixupBellLoFromGatherCirc {M D n : ℕ} (r : RouterReg M D n) :
    (cFixupBellLoFromGatherCirc r).count .T = 0 ∧ (cFixupBellLoFromGatherCirc r).count .TOFF =
        0 := by
  suffices ∀ (m : ℕ) (hm : m ≤ 24), (cFixupBellLoPfxCirc r m hm).count .T = 0 ∧
      (cFixupBellLoPfxCirc r m hm).count .TOFF = 0 from this 24 le_rfl
  intro m
  induction m with
  | zero => exact fun _ ↦ ⟨rfl, rfl⟩
  | succ m ih =>
      exact fun hm ↦ by
        simp [cFixupBellLoPfxCirc, cFixupBellLoPlaneCirc, Circuit.count_seq, Circuit.CNOT,
          ih (Nat.le_of_succ_le hm)]

theorem cw_cFixupBellLoFromGatherCirc {M D n : ℕ} {S : Wire n → Prop} (r : RouterReg M D n)
    (hHA : ∀ b : Fin 24, S (rHA r b)) (hBufLo : ∀ b : Fin 24, S (rBufLo r b)) :
    CircWires S (cFixupBellLoFromGatherCirc r) := by
  suffices ∀ (m : ℕ) (hm : m ≤ 24), CircWires S (cFixupBellLoPfxCirc r m hm) from this 24 le_rfl
  intro m
  induction m with
  | zero => exact fun _ ↦ trivial
  | succ m ih =>
      exact fun hm ↦ cw_seq (ih (Nat.le_of_succ_le hm))
        (cw_seq (cw_cnot (hHA ⟨m, hm⟩) (hBufLo ⟨m, hm⟩)) (cw_cnot (hBufLo ⟨m, hm⟩) (hHA ⟨m, hm⟩)))

private theorem zgat_hcnotSupportedIn_cFixupPfx {M D n : ℕ} {S : Wire n → Prop}
    (r : RouterReg M D n) :
    ∀ (m : ℕ) (hm : m ≤ 24),
      (∀ k : Fin 24, k.val < m → S (rHA r k) ∧ S (rBufLo r k)) →
      HCNOTSupportedIn S (cFixupBellLoPfxCirc r m hm)
  | 0, _, _ => .id
  | m + 1, hm, hS =>
      .seq (zgat_hcnotSupportedIn_cFixupPfx r m (Nat.le_of_succ_le hm)
              (fun k hk ↦ hS k (Nat.lt_succ_of_lt hk)))
        (.seq (.cnot _ (hS ⟨m, hm⟩ (Nat.lt_succ_self m)).1 (hS ⟨m, hm⟩ (Nat.lt_succ_self m)).2)
          (.cnot _ (hS ⟨m, hm⟩ (Nat.lt_succ_self m)).2 (hS ⟨m, hm⟩ (Nat.lt_succ_self m)).1))

theorem hcnotSupportedIn_cFixupBellLoFromGatherCirc {M D n : ℕ} (r : RouterReg M D n) :
    HCNOTSupportedIn (AllPlaneMod r) (cFixupBellLoFromGatherCirc r) :=
  zgat_hcnotSupportedIn_cFixupPfx r 24 le_rfl
    (fun k _ ↦ ⟨⟨k, Or.inr (Or.inr (Or.inl rfl))⟩, ⟨k, Or.inl rfl⟩⟩)

private theorem zgat_hcnotSupportedIn_fixedSwap1 {M n : ℕ} {S : Wire n → Prop}
    (qB : Wire n) (cVec : Fin M → ZMod 2) (wT : Fin M → Wire n) (hbt : ∀ p, qB ≠ wT p)
    (hq : S qB) (hw : ∀ p, cVec p = 1 → S (wT p)) :
    HCNOTSupportedIn S (fixedSwap1Circ M qB cVec wT hbt) := by
  induction M with
  | zero => exact .id
  | succ K ih =>
      dsimp only [fixedSwap1Circ]
      refine .seq (ih _ _ _ (fun p hp ↦ hw p.castSucc hp)) ?_
      split_ifs with hc
      · exact .seq (.cnot _ hq (hw _ hc)) (.seq (.cnot _ (hw _ hc) hq) (.cnot _ hq (hw _ hc)))
      · exact .id

private theorem zgat_lo_plane_fixup_ket {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (cLo : Fin M → ZMod 2) (pMin : Fin M) (hc1 : cLo pMin = 1)
    (hc0 : ∀ p : Fin M, p ≠ pMin → cLo p = 0) (α : BitAssignment n)
    (hHA0 : α (rHA r b) = 0) (hLo0 : α (rBufLo r b) = 0) :
    ((cFixupBellLoPlaneCirc r b).eval.1 *
      (fixedFanoutCirc M (rBufLo r b) cLo (fun p ↦ rSys r p b) ((hne_fixed_router r).1 b)).eval.1 *
      (fixedSwap1Circ M (rBufLo r b) cLo (fun p ↦ rSys r p b) ((hne_fixed_router r).1 b)).eval.1 *
      (fixedBell1Circ M (rHA r b) cLo (fun p ↦ rSys r p b)
          (hne_hA_sys r b)).eval.1).mulVec (ket α) =
    ((fixedBell1Circ M (rHA r b) cLo (fun p ↦ rSys r p b) (hne_hA_sys r b)).eval.1 *
      (fixedSwap1Circ M (rBufLo r b) cLo (fun p ↦ rSys r p b)
        ((hne_fixed_router r).1 b)).eval.1).mulVec (ket α) := by
  have hne_hb : rHA r b ≠ rBufLo r b := rr_ne r (by
    dsimp [rHA, rBufLo]
    omega)
  have hne_hs : rHA r b ≠ rSys r pMin b := hne_hA_sys r b pMin
  have hne_bs : rBufLo r b ≠ rSys r pMin b := (hne_fixed_router r).1 b pMin
  have upd3_eq {f g : BitAssignment n}
      (hO : ∀ w, w ≠ rHA r b → w ≠ rBufLo r b → w ≠ rSys r pMin b → f w = g w)
      (hH : f (rHA r b) = g (rHA r b)) (hB : f (rBufLo r b) = g (rBufLo r b))
      (hS : f (rSys r pMin b) = g (rSys r pMin b)) : f = g := by
    funext w
    rcases eq_or_ne w (rHA r b) with rfl | wh
    · exact hH
    rcases eq_or_ne w (rBufLo r b) with rfl | wb
    · exact hB
    rcases eq_or_ne w (rSys r pMin b) with rfl | ws
    · exact hS
    exact hO w wh wb ws
  let br (δ : BitAssignment n) :=
    Function.update (Function.update δ (rBufLo r b) (δ (rSys r pMin b) + δ (rHA r b)))
      (rHA r b) (δ (rSys r pMin b))
  have hOneBranch (δ : BitAssignment n) (hd0 : δ (rBufLo r b) = 0) :
      (cFixupBellLoPlaneCirc r b).eval.1.mulVec
        ((fixedFanoutCirc M (rBufLo r b) cLo (fun p ↦ rSys r p b)
            ((hne_fixed_router r).1 b)).eval.1.mulVec
          ((fixedSwap1Circ M (rBufLo r b) cLo (fun p ↦ rSys r p b)
              ((hne_fixed_router r).1 b)).eval.1.mulVec (ket δ))) = ket (br δ) := by
    rw [fixedSwap1Circ_oneHot_ket M (rBufLo r b) cLo _ ((hne_fixed_router r).1 b) pMin hc1 hc0 δ
        hd0, fixedFanoutCirc_mulVec_ket, fixedFanoutBits_oneHot M _ cLo _ pMin hc1 hc0]
    dsimp only [cFixupBellLoPlaneCirc, br]
    rw [eval_seq_mulVec, ket_CNOT, ket_CNOT]
    congr 1
    refine upd3_eq (fun _ wh wb ws ↦ by
        simp only [Function.update_of_ne wh, Function.update_of_ne wb, Function.update_of_ne ws])
      (by
        simp only [Function.update_self, Function.update_of_ne hne_hb,
          Function.update_of_ne hne_hs, Function.update_of_ne hne_bs]
        rcases bit_cases (δ (rHA r b)) with h1 | h1 <;>
          rcases bit_cases (δ (rSys r pMin b)) with h2 | h2 <;> rw [h1, h2] <;> decide) ?_ ?_ <;>
      simp only [Function.update_self, Function.update_of_ne hne_hb,
        Function.update_of_ne hne_hb.symm, Function.update_of_ne hne_hs,
        Function.update_of_ne hne_hs.symm, Function.update_of_ne hne_bs,
        Function.update_of_ne hne_bs.symm, zero_add]
  let α_sw := Function.update (Function.update α (rBufLo r b) (α (rSys r pMin b))) (rSys r pMin b) 0
  let α₁ := Function.update (Function.update α (rSys r pMin b) (α (rSys r pMin b) + 1)) (rHA r b) 1
  have hSwHA0 : α_sw (rHA r b) = 0 := by
    simp only [α_sw, Function.update_of_ne hne_hs, Function.update_of_ne hne_hb, hHA0]
  have hα₁_bLo : α₁ (rBufLo r b) = 0 := by
    simp only [α₁, Function.update_of_ne hne_hb.symm, Function.update_of_ne hne_bs, hLo0]
  simp only [← Matrix.mulVec_mulVec]
  rw [fixedBell1Circ_mulVec_ket_zero M (rHA r b) cLo _ (hne_hA_sys r b) hHA0,
      fixedFanoutBits_oneHot M 1 cLo _ pMin hc1 hc0 α,
      fixedSwap1Circ_oneHot_ket M (rBufLo r b) cLo _ _ pMin hc1 hc0 α hLo0,
      fixedBell1Circ_mulVec_ket_zero M (rHA r b) cLo _ (hne_hA_sys r b) hSwHA0,
      fixedFanoutBits_oneHot M 1 cLo _ pMin hc1 hc0 α_sw]
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add]
  rw [hOneBranch α hLo0, hOneBranch α₁ hα₁_bLo]
  let α_sw1 := Function.update (Function.update α_sw (rSys r pMin b) (α_sw (rSys r pMin b) + 1))
    (rHA r b) 1
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases bit_cases (α (rSys r pMin b)) with hs | hs
  · suffices br α = α_sw ∧ br α₁ = α_sw1 by rw [this.1, this.2]
    refine ⟨upd3_eq (fun _ wh wb ws ↦ by
        simp only [br, α_sw, Function.update_of_ne wh, Function.update_of_ne wb,
          Function.update_of_ne ws]) ?_ ?_ ?_,
      upd3_eq (fun _ wh wb ws ↦ by
        simp only [br, α₁, α_sw1, α_sw, Function.update_of_ne wh, Function.update_of_ne wb,
          Function.update_of_ne ws]) ?_ ?_ ?_⟩
    all_goals simp only [br, α₁, α_sw, α_sw1, Function.update_self, Function.update_of_ne hne_hb,
      Function.update_of_ne hne_hb.symm, Function.update_of_ne hne_hs,
      Function.update_of_ne hne_hs.symm, Function.update_of_ne hne_bs,
      Function.update_of_ne hne_bs.symm, hHA0, hs, zero_add, add_zero, h11]
  · suffices br α = α_sw1 ∧ br α₁ = α_sw by rw [this.1, this.2, add_comm]
    refine ⟨upd3_eq (fun _ wh wb ws ↦ by
        simp only [br, α_sw1, α_sw, Function.update_of_ne wh, Function.update_of_ne wb,
          Function.update_of_ne ws]) ?_ ?_ ?_,
      upd3_eq (fun _ wh wb ws ↦ by
        simp only [br, α₁, α_sw, Function.update_of_ne wh, Function.update_of_ne wb,
          Function.update_of_ne ws]) ?_ ?_ ?_⟩
    all_goals simp only [br, α₁, α_sw, α_sw1, Function.update_self, Function.update_of_ne hne_hb,
      Function.update_of_ne hne_hb.symm, Function.update_of_ne hne_hs,
      Function.update_of_ne hne_hs.symm, Function.update_of_ne hne_bs,
      Function.update_of_ne hne_bs.symm, hHA0, hs, zero_add, add_zero, h11]

/--
Post-gather `48`-CNOT fixup restores the genuine-`BellLo` operator
`(uBellLoCopyHiAlwaysLoConj r).1 * ((uRouterSwapAlwaysLoConj r).1 * R)` from
`uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * ((uBellLoPreScatter r).1 * R))`.
-/
theorem cFixupBellLoFromGatherCirc_mul_eq {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n)
    (R : Operator (2 ^ n)) (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    (cFixupBellLoFromGatherCirc r).eval.1 *
      (uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * ((uBellLoPreScatter r).1 * R))) =
    (uBellLoCopyHiAlwaysLoConj r).1 * ((uRouterSwapAlwaysLoConj r).1 * R) := by
  simp only [← Matrix.mul_assoc]
  refine hR _ _ fun β hβ ↦ ?_
  have hlt1 : idxValD (rIdx1 r) β < M := by
    rcases bit_cases (β (rHas1 r)) with h0 | h1
    · exact idxValD_eq_zero_of_zero (rIdx1 r) (hβ.2.1 h0) ▸ hM0
    · exact hβ.1.2.1 h1
  let cLo := cLoAlways r β
  let cHi := routerCtrlHi r β
  let pMin : Fin M := ⟨idxValD (rIdx1 r) β, hlt1⟩
  have hcL1 : cLo pMin = 1 := by simp [cLo, pMin, cLoAlways]
  have hcL0 (p : Fin M) (hp : p ≠ pMin) : cLo p = 0 := by
    simp [cLo, pMin, cLoAlways, Fin.val_ne_of_ne hp]
  have hcHMin : cHi pMin = 0 := by
    dsimp only [cHi]
    rw [congrFun (routerCtrlHi_of_zeroGatedSorted hβ) pMin]
    rcases bit_cases (β (rRawHas2 r)) with hH0 | hH1
    · simp [hH0]
    · exact _root_.ite_eq_right (Nat.ne_of_lt (hβ.2.2.2 hH1))
  let SLo (k : Fin 24) (w : Wire n) : Prop := w = rHA r k ∨ w = rBufLo r k ∨ w = rSys r pMin k
  have hSLoDisj (j k : Fin 24) (hjk : j ≠ k) (w : Wire n) (hj : SLo j w) (hk : SLo k w) :
      False := by
    have hne := Fin.val_ne_of_ne hjk
    rcases hj with rfl | rfl | rfl <;> rcases hk with h | h | h
    all_goals
      refine rr_ne r ?_ h
      dsimp [rHA, rBufLo, rSys]
      omega
  let SHi (w : Wire n) : Prop :=
    (∃ b : Fin 24, w = rBufHi r b) ∨ (∃ (b : Fin 24) (p : Fin M), cHi p = 1 ∧ w = rSys r p b)
  have hHiLoDisj : ∀ w, (∃ k : Fin 24, SLo k w) → ¬ SHi w := by
    rintro w ⟨k, hSLo⟩ (⟨b, rfl⟩ | ⟨b, p, hp1, rfl⟩)
    · rcases hSLo with h | h | h
      all_goals
        refine rr_ne r ?_ h.symm
        dsimp [rHA, rBufLo, rBufHi, rSys]
        omega
    · rcases hSLo with h | h | h
      · exact rr_ne r (by
          dsimp [rHA, rSys]
          omega) h.symm
      · exact rr_ne r (by
          dsimp [rBufLo, rSys]
          omega) h.symm
      · have hv := congrArg Fin.val (r.wires.injective h)
        dsimp [rSys] at hv
        have hpEq : p = pMin := Fin.ext (by omega)
        exact zero_ne_one (hcHMin ▸ hpEq ▸ hp1)
  let finM {m : ℕ} (hm : m ≤ 24) (i : Fin m) : Fin 24 :=
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩
  let cBellPfx (m : ℕ) (hm : m ≤ 24) :=
    fixedBellVecCirc M m (fun i ↦ rHA r (finM hm i)) cLo
      (fun i p ↦ rSys r p (finM hm i)) (fun _ p ↦ hne_hA_sys r _ p)
  let cSwapLoPfx (m : ℕ) (hm : m ≤ 24) :=
    fixedSwapVecCirc M m (fun i ↦ rBufLo r (finM hm i)) cLo
      (fun i p ↦ rSys r p (finM hm i)) (fun _ p ↦ (hne_fixed_router r).1 _ p)
  let cFanLoPfx (m : ℕ) (hm : m ≤ 24) :=
    fixedFanoutVecCirc M m (fun i ↦ rBufLo r (finM hm i)) cLo
      (fun i p ↦ rSys r p (finM hm i)) (fun _ p ↦ (hne_fixed_router r).1 _ p)
  have hCP (p : Fin M) (hp : cLo p = 1) : p = pMin :=
    Decidable.byContradiction fun hne ↦ zero_ne_one ((hcL0 p hne).symm.trans hp)
  have hSysS (m : ℕ) (hm : m ≤ 24) (i : Fin m) (p : Fin M) (hp : cLo p = 1) :
      ∃ k : Fin 24, k.val < m ∧ SLo k (rSys r p (finM hm i)) :=
    ⟨finM hm i, i.isLt, Or.inr (Or.inr (by rw [hCP p hp]))⟩
  have hHCBell (m : ℕ) (hm : m ≤ 24) :
      HCNOTSupportedIn (fun w ↦ ∃ k : Fin 24, k.val < m ∧ SLo k w) (cBellPfx m hm) :=
    hcnotSupportedIn_fixedBellVec cLo m _ _ _
      (fun i ↦ ⟨finM hm i, i.isLt, Or.inl rfl⟩) (hSysS m hm)
  have hHCSwapLo (m : ℕ) (hm : m ≤ 24) :
      HCNOTSupportedIn (fun w ↦ ∃ k : Fin 24, k.val < m ∧ SLo k w) (cSwapLoPfx m hm) :=
    hcnotSupportedIn_fixedSwapVec cLo m _ _ _
      (fun i ↦ ⟨finM hm i, i.isLt, Or.inr (Or.inl rfl)⟩) (hSysS m hm)
  have hHCFanLo (m : ℕ) (hm : m ≤ 24) :
      HCNOTSupportedIn (fun w ↦ ∃ k : Fin 24, k.val < m ∧ SLo k w) (cFanLoPfx m hm) :=
    hcnotSupportedIn_fixedFanoutVec m _ cLo _ _
      (fun i ↦ ⟨finM hm i, i.isLt, Or.inr (Or.inl rfl)⟩) (hSysS m hm)
  have hHCFix (m : ℕ) (hm : m ≤ 24) :
      HCNOTSupportedIn (fun w ↦ ∃ k : Fin 24, k.val < m ∧ SLo k w)
        (cFixupBellLoPfxCirc r m hm) :=
    zgat_hcnotSupportedIn_cFixupPfx r m hm
      (fun k hk ↦ ⟨⟨k, hk, Or.inl rfl⟩, ⟨k, hk, Or.inr (Or.inl rfl)⟩⟩)
  have pull1 {X Y Z : Operator (2 ^ n)} (h : X * Y = Y * X) : X * (Y * Z) = Y * (X * Z) := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
  have hLoInd (m : ℕ) : ∀ (hm : m ≤ 24) (α : BitAssignment n),
      (∀ k : Fin 24, k.val < m → α (rHA r k) = 0 ∧ α (rBufLo r k) = 0) →
      ((cFixupBellLoPfxCirc r m hm).eval.1 * (cFanLoPfx m hm).eval.1 *
        (cSwapLoPfx m hm).eval.1 * (cBellPfx m hm).eval.1).mulVec (ket α) =
      ((cBellPfx m hm).eval.1 * (cSwapLoPfx m hm).eval.1).mulVec (ket α) := by
    induction m with
    | zero =>
        intro hm α _
        dsimp only [cFixupBellLoPfxCirc, cFanLoPfx, cSwapLoPfx, cBellPfx,
          fixedFanoutVecCirc, fixedSwapVecCirc, fixedBellVecCirc]
        simp [Circuit.eval_identity]
    | succ m ih =>
        intro hm α hα0
        let hm' := Nat.le_of_succ_le hm
        let bm : Fin 24 := ⟨m, hm⟩
        have hDisjM : ∀ w, (∃ k : Fin 24, k.val < m ∧ SLo k w) → ¬ SLo bm w :=
          fun w ⟨k, hkm, hk⟩ hbm ↦
            hSLoDisj k bm (fun e ↦ Nat.ne_of_lt hkm (congrArg Fin.val e)) w hk hbm
        let cF1 := cFixupBellLoPlaneCirc r bm
        let cFn1 := fixedFanoutCirc M (rBufLo r bm) cLo (fun p ↦ rSys r p bm)
          ((hne_fixed_router r).1 bm)
        let cSw1 := fixedSwap1Circ M (rBufLo r bm) cLo (fun p ↦ rSys r p bm)
          ((hne_fixed_router r).1 bm)
        let cBl1 := fixedBell1Circ M (rHA r bm) cLo (fun p ↦ rSys r p bm) (hne_hA_sys r bm)
        have hcF1 : HCNOTSupportedIn (SLo bm) cF1 :=
          .seq (.cnot _ (Or.inl rfl) (Or.inr (Or.inl rfl)))
            (.cnot _ (Or.inr (Or.inl rfl)) (Or.inl rfl))
        have hSysBm (p : Fin M) (hp : cLo p = 1) : SLo bm (rSys r p bm) :=
          Or.inr (Or.inr (by rw [hCP p hp]))
        have hcFn1 : HCNOTSupportedIn (SLo bm) cFn1 :=
          PhotochemistrySolution.HalfBellCollapse.hcnotSupportedIn_fixedFanout1 _ cLo _ _
            (Or.inr (Or.inl rfl)) hSysBm
        have hcSw1 : HCNOTSupportedIn (SLo bm) cSw1 :=
          zgat_hcnotSupportedIn_fixedSwap1 _ cLo _ _ (Or.inr (Or.inl rfl)) hSysBm
        have hcBl1 : HCNOTSupportedIn (SLo bm) cBl1 :=
          .seq (.h (Or.inl rfl))
            (PhotochemistrySolution.HalfBellCollapse.hcnotSupportedIn_fixedFanout1 _ cLo _ _
              (Or.inl rfl) hSysBm)
        have eFix : (cFixupBellLoPfxCirc r (m + 1) hm).eval.1 =
            cF1.eval.1 * (cFixupBellLoPfxCirc r m hm').eval.1 := by
          dsimp only [cFixupBellLoPfxCirc]
          rw [Circuit.eval_seq, Submonoid.coe_mul]
        have eFan : (cFanLoPfx (m + 1) hm).eval.1 =
            cFn1.eval.1 * (cFanLoPfx m hm').eval.1 := by
          dsimp only [cFanLoPfx, fixedFanoutVecCirc, finM, Fin.val_last]
          rw [Circuit.eval_seq, Submonoid.coe_mul]
          rfl
        have eSw : (cSwapLoPfx (m + 1) hm).eval.1 =
            cSw1.eval.1 * (cSwapLoPfx m hm').eval.1 := by
          dsimp only [cSwapLoPfx, fixedSwapVecCirc, finM, Fin.val_last]
          rw [Circuit.eval_seq, Submonoid.coe_mul]
          rfl
        have eBl : (cBellPfx (m + 1) hm).eval.1 =
            cBl1.eval.1 * (cBellPfx m hm').eval.1 := by
          dsimp only [cBellPfx, fixedBellVecCirc, finM, Fin.val_last]
          rw [Circuit.eval_seq, Submonoid.coe_mul]
          rfl
        have hRearrL :
            (cFixupBellLoPfxCirc r (m + 1) hm).eval.1 * (cFanLoPfx (m + 1) hm).eval.1 *
              (cSwapLoPfx (m + 1) hm).eval.1 * (cBellPfx (m + 1) hm).eval.1 =
            ((cFixupBellLoPfxCirc r m hm').eval.1 * (cFanLoPfx m hm').eval.1 *
              (cSwapLoPfx m hm').eval.1 * (cBellPfx m hm').eval.1) *
              (cF1.eval.1 * cFn1.eval.1 * cSw1.eval.1 * cBl1.eval.1) := by
          rw [eFix, eFan, eSw, eBl]
          simp only [Matrix.mul_assoc]
          rw [← (hHCBell m hm').comm hcBl1 hDisjM,
              pull1 (((hHCSwapLo m hm').comm hcSw1 hDisjM).symm),
              pull1 (((hHCBell m hm').comm hcSw1 hDisjM).symm),
              pull1 (((hHCFanLo m hm').comm hcFn1 hDisjM).symm),
              pull1 (((hHCSwapLo m hm').comm hcFn1 hDisjM).symm),
              pull1 (((hHCBell m hm').comm hcFn1 hDisjM).symm),
              pull1 (((hHCFix m hm').comm hcF1 hDisjM).symm),
              pull1 (((hHCFanLo m hm').comm hcF1 hDisjM).symm),
              pull1 (((hHCSwapLo m hm').comm hcF1 hDisjM).symm),
              pull1 (((hHCBell m hm').comm hcF1 hDisjM).symm)]
        have hRearrR :
            (cBellPfx (m + 1) hm).eval.1 * (cSwapLoPfx (m + 1) hm).eval.1 =
            ((cBellPfx m hm').eval.1 * (cSwapLoPfx m hm').eval.1) *
              (cBl1.eval.1 * cSw1.eval.1) := by
          rw [eBl, eSw]
          simp only [Matrix.mul_assoc]
          rw [← (hHCSwapLo m hm').comm hcSw1 hDisjM,
              pull1 (((hHCBell m hm').comm hcBl1 hDisjM).symm),
              pull1 (((hHCSwapLo m hm').comm hcBl1 hDisjM).symm)]
        rw [hRearrL, hRearrR,
            ← Matrix.mulVec_mulVec (ket α) _
              (cF1.eval.1 * cFn1.eval.1 * cSw1.eval.1 * cBl1.eval.1),
            ← Matrix.mulVec_mulVec (ket α) _ (cBl1.eval.1 * cSw1.eval.1)]
        dsimp only [cF1, cFn1, cSw1, cBl1]
        rw [zgat_lo_plane_fixup_ket r bm cLo pMin hcL1 hcL0 α
              (hα0 bm (Nat.lt_succ_self m)).1 (hα0 bm (Nat.lt_succ_self m)).2]
        have hStepPres {u : Wire n} (hu : SLo bm u) (γ : BitAssignment n) (v : ZMod 2)
            (hγ : ∀ k : Fin 24, k.val < m → γ (rHA r k) = 0 ∧ γ (rBufLo r k) = 0)
            (k : Fin 24) (hkm : k.val < m) :
            Function.update γ u v (rHA r k) = 0 ∧ Function.update γ u v (rBufLo r k) = 0 := by
          have hkb : k ≠ bm := fun e ↦ Nat.ne_of_lt hkm (congrArg Fin.val e)
          exact ⟨(Function.update_of_ne
                    (fun (e : rHA r k = u) ↦ hSLoDisj k bm hkb _ (Or.inl rfl) (e.symm ▸ hu))
                    v γ).trans (hγ k hkm).1,
                 (Function.update_of_ne
                    (fun (e : rBufLo r k = u) ↦
                      hSLoDisj k bm hkb _ (Or.inr (Or.inl rfl)) (e.symm ▸ hu))
                    v γ).trans (hγ k hkm).2⟩
        have hPres : PreservesKetPred
            (fun γ ↦ ∀ k : Fin 24, k.val < m → γ (rHA r k) = 0 ∧ γ (rBufLo r k) = 0)
            ((cBl1.eval.1 * cSw1.eval.1).mulVec (ket α)) := by
          rw [← Matrix.mulVec_mulVec]
          exact hcBl1.preservesKetPred hStepPres
            (hcSw1.preservesKetPred hStepPres
              (preservesKetPred_ket fun k hk ↦ hα0 k (Nat.lt_succ_of_lt hk)))
        exact hPres _ _ fun γ hγ ↦ ih hm' γ hγ
  let cSwapHi := fixedSwapVecCirc M 24 (rBufHi r) cHi (fun b p ↦ rSys r p b)
    (hne_fixed_router r).2.1
  let cFanHi := fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun b p ↦ rSys r p b) (hne_bufHi_sys r)
  have hcSwapHi : HCNOTSupportedIn SHi cSwapHi :=
    hcnotSupportedIn_fixedSwapVec cHi 24 _ _ _ (fun b ↦ Or.inl ⟨b, rfl⟩)
      (fun b p hp ↦ Or.inr ⟨b, p, hp, rfl⟩)
  have hcFanHi : HCNOTSupportedIn SHi cFanHi :=
    hcnotSupportedIn_fixedFanoutVec 24 _ cHi _ _ (fun b ↦ Or.inl ⟨b, rfl⟩)
      (fun b p hp ↦ Or.inr ⟨b, p, hp, rfl⟩)
  have hDisj24 : ∀ w, (∃ k : Fin 24, k.val < 24 ∧ SLo k w) → ¬ SHi w :=
    fun w ⟨k, _, hk⟩ ↦ hHiLoDisj w ⟨k, hk⟩
  have hPresSwap {ψ : Fin (2 ^ n) → ℂ}
      (hψ : PreservesKetPred (fun α ↦ ∀ w, PubCtrlSet r w → α w = β w) ψ) :
      PreservesKetPred (fun α ↦ ∀ w, PubCtrlSet r w → α w = β w)
        ((cFixedSwapCirc r cLo cHi).eval.1.mulVec ψ) := by
    have hSysMod (b : Fin 24) (p : Fin M) : AllPlaneMod r (rSys r p b) :=
      ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩
    refine (HCNOTSupportedIn.seq (S := AllPlaneMod r)
      (hcnotSupportedIn_fixedSwapVec cLo 24 _ _ _ (fun b ↦ ⟨b, Or.inl rfl⟩)
        (fun b p _ ↦ hSysMod b p))
      (hcnotSupportedIn_fixedSwapVec cHi 24 _ _ _ (fun b ↦ ⟨b, Or.inr (Or.inl rfl)⟩)
        (fun b p _ ↦ hSysMod b p))).preservesKetPred
      (fun {u} hu α v hPub w ⟨k, hk, hw⟩ ↦ ?_) hψ
    subst hw
    exact (Function.update_of_ne
      (fun (e : r k = u) ↦ not_allPlaneMod_of_idx r (Or.inl hk) (e.symm ▸ hu))
      v α).trans (hPub _ ⟨k, hk, rfl⟩)
  have hCtrlPub {α : BitAssignment n} (hPub : ∀ w, PubCtrlSet r w → α w = β w) :
      cLoAlways r α = cLo ∧ routerCtrlHi r α = cHi :=
    cLoAlways_routerCtrlHi_eq_of_eq r fun u hu ↦ hPub u (routerCtrlSet_sub_pubCtrlSet r hu)
  have hGhostL :
      (uCopyLoHiAlwaysLoMat r * (uRouterSwapAlwaysLoConj r).1 *
        (uBellLoPreScatter r).1).mulVec (ket β) =
      ((cFixedCopyLoHiCirc r cLo cHi).eval.1 * (cFixedSwapCirc r cLo cHi).eval.1 *
        (cBellLoPfxCirc r 24 le_rfl cLo cHi).eval.1).mulVec (ket β) := by
    have eG24 : (uBellLoPreScatterPfx r 24 le_rfl).1.mulVec (ket β) =
        (cBellLoPfxCirc r 24 le_rfl cLo cHi).eval.1.mulVec (ket β) :=
      uAlwaysLoGhostMat_mulVec_ket r (cBellLoPfxCirc r 24 le_rfl) β
    have hP1 : PreservesKetPred (fun α ↦ ∀ w, PubCtrlSet r w → α w = β w)
        ((cBellLoPfxCirc r 24 le_rfl cLo cHi).eval.1.mulVec (ket β)) := by
      have h0 := zgat_preservesKetPred_uBellLoPreScatterPfx r 24 le_rfl β
        ((zgat_validZeroGatedWithoutHA_iff r β).mpr hβ).1
      rw [eG24] at h0
      exact fun A B hAB ↦ h0 A B fun α hα ↦ hAB α hα.2
    simp only [← Matrix.mulVec_mulVec]
    dsimp only [uBellLoPreScatter]
    rw [eG24, hP1 (uRouterSwapAlwaysLoConj r).1 (cFixedSwapCirc r cLo cHi).eval.1 fun α hPub ↦ by
      rw [uRouterSwapAlwaysLoConj_mulVec_ket_any, (hCtrlPub hPub).1, (hCtrlPub hPub).2]]
    exact (hPresSwap hP1) _ _ fun α hPub ↦ by
      rw [uCopyLoHiAlwaysLoMat_mulVec_ket, (hCtrlPub hPub).1, (hCtrlPub hPub).2]
  have hGhostR :
      ((uBellLoCopyHiAlwaysLoConj r).1 * (uRouterSwapAlwaysLoConj r).1).mulVec (ket β) =
      ((cFixedBellLoCopyHiCirc r cLo cHi).eval.1 *
        (cFixedSwapCirc r cLo cHi).eval.1).mulVec (ket β) := by
    simp only [← Matrix.mulVec_mulVec]
    rw [uRouterSwapAlwaysLoConj_mulVec_ket_any]
    exact (hPresSwap (preservesKetPred_ket fun _ _ ↦ rfl)) _ _ fun α hPub ↦ by
      rw [uBellLoCopyHiAlwaysLoConj_mulVec_ket_any, (hCtrlPub hPub).1, (hCtrlPub hPub).2]
  have hAssocL :
      (cFixupBellLoFromGatherCirc r).eval.1 * uCopyLoHiAlwaysLoMat r *
        (uRouterSwapAlwaysLoConj r).1 * (uBellLoPreScatter r).1 =
      (cFixupBellLoFromGatherCirc r).eval.1 *
        (uCopyLoHiAlwaysLoMat r * (uRouterSwapAlwaysLoConj r).1 * (uBellLoPreScatter r).1) := by
    simp only [Matrix.mul_assoc]
  rw [zgat_ket_sr β, hAssocL,
      ← Matrix.mulVec_mulVec (ket β) (cFixupBellLoFromGatherCirc r).eval.1 _,
      hGhostL, hGhostR,
      Matrix.mulVec_mulVec (ket β) (cFixupBellLoFromGatherCirc r).eval.1 _,
      show (cFixedCopyLoHiCirc r cLo cHi).eval.1 =
        (cFanLoPfx 24 le_rfl).eval.1 * cFanHi.eval.1 by
          dsimp only [cFixedCopyLoHiCirc]
          rw [Circuit.eval_seq, Submonoid.coe_mul],
      show (cFixedSwapCirc r cLo cHi).eval.1 =
        cSwapHi.eval.1 * (cSwapLoPfx 24 le_rfl).eval.1 by
          dsimp only [cFixedSwapCirc]
          rw [Circuit.eval_seq, Submonoid.coe_mul],
      show (cFixedBellLoCopyHiCirc r cLo cHi).eval.1 =
        cFanHi.eval.1 * (cBellPfx 24 le_rfl).eval.1 by
          dsimp only [cFixedBellLoCopyHiCirc]
          rw [Circuit.eval_seq, Submonoid.coe_mul],
      show (cBellLoPfxCirc r 24 le_rfl cLo cHi).eval.1 = (cBellPfx 24 le_rfl).eval.1 from rfl]
  have hCommL :
      (cFixupBellLoFromGatherCirc r).eval.1 *
        (((cFanLoPfx 24 le_rfl).eval.1 * cFanHi.eval.1) *
          (cSwapHi.eval.1 * (cSwapLoPfx 24 le_rfl).eval.1) * (cBellPfx 24 le_rfl).eval.1) =
      (cFanHi.eval.1 * cSwapHi.eval.1) *
        ((cFixupBellLoPfxCirc r 24 le_rfl).eval.1 * (cFanLoPfx 24 le_rfl).eval.1 *
          (cSwapLoPfx 24 le_rfl).eval.1 * (cBellPfx 24 le_rfl).eval.1) := by
    dsimp only [cFixupBellLoFromGatherCirc]
    simp only [Matrix.mul_assoc]
    rw [pull1 ((hHCFanLo 24 le_rfl).comm hcFanHi hDisj24),
        pull1 ((hHCFix 24 le_rfl).comm hcFanHi hDisj24),
        pull1 ((hHCFanLo 24 le_rfl).comm hcSwapHi hDisj24),
        pull1 ((hHCFix 24 le_rfl).comm hcSwapHi hDisj24)]
  have hCommR :
      (cFanHi.eval.1 * (cBellPfx 24 le_rfl).eval.1) *
        (cSwapHi.eval.1 * (cSwapLoPfx 24 le_rfl).eval.1) =
      (cFanHi.eval.1 * cSwapHi.eval.1) *
        ((cBellPfx 24 le_rfl).eval.1 * (cSwapLoPfx 24 le_rfl).eval.1) := by
    simp only [Matrix.mul_assoc]
    rw [pull1 ((hHCBell 24 le_rfl).comm hcSwapHi hDisj24)]
  rw [hCommL, hCommR,
      ← Matrix.mulVec_mulVec (ket β) (cFanHi.eval.1 * cSwapHi.eval.1) _,
      ← Matrix.mulVec_mulVec (ket β) (cFanHi.eval.1 * cSwapHi.eval.1) _,
      hLoInd 24 le_rfl β (fun k _ ↦ ⟨(hβ.1.2.2.2.1 k).2.2.1, (hβ.1.2.2.2.1 k).1⟩)]

attribute [irreducible]
  pPlaneOneHotScatterLo pPlanesOneHotScatterLoLoop pPlanesOneHotScatterLoPubCtrlLo
  cFixupBellLoPfxCirc

/--
Post-`uXorPubLo` `OneHotScatter` (`8,976 T`) + `pTail r'` (`tTail` `T`) + `48`-CNOT fixup (`0 T`)
core (`8,976 + tTail` `T`, `0 .TOFF`), shared by both `pBellLoFromPostXorTail` and
`pHoldLoFromPostXorTail`.
-/
def pBellLoAfterPubCtrlLo {Var : Type} {n : ℕ}
    (pTail : RouterReg 187 8 n → DynamicCircuit Var n)
    (r' : RouterReg 187 8 n) (v : Var) (r : RouterReg 187 8 n) : DynamicCircuit Var n :=
  .seq (pPlanesOneHotScatterLoPubCtrlLo zg187_hM0 v r)
    (.seq (pTail r') (.circuit (cFixupBellLoFromGatherCirc r)))

theorem count_pBellLoAfterPubCtrlLo {Var : Type} {n tTail : ℕ}
    (pTail : RouterReg 187 8 n → DynamicCircuit Var n)
    (r' : RouterReg 187 8 n) (v : Var) (r : RouterReg 187 8 n)
    (hTail : (pTail r').count .T = tTail ∧ (pTail r').count .TOFF = 0) :
    (pBellLoAfterPubCtrlLo pTail r' v r).count .T = 8976 + tTail ∧
    (pBellLoAfterPubCtrlLo pTail r' v r).count .TOFF = 0 := by
  obtain ⟨t1, f1⟩ := count_pPlanesOneHotScatterLoPubCtrlLo (Var := Var) zg187_hM0 v r
  obtain ⟨t3, f3⟩ := count_cFixupBellLoFromGatherCirc r
  unfold pBellLoAfterPubCtrlLo
  dsimp only [DynamicCircuit.count]
  rw [t1, f1, hTail.1, hTail.2, t3, f3]
  exact ⟨by omega, rfl⟩

theorem dynWires_pBellLoAfterPubCtrlLo_idx {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (pTail : RouterReg 187 8 n → DynamicCircuit Var n)
    (r' : RouterReg 187 8 n) (v : Var) (r : RouterReg 187 8 n)
    (h290 : ∀ j : Fin (routerWidth 187 8), NoNFW290Idx j.val → S (r j))
    (hTail : DynWires S (pTail r')) :
    DynWires S (pBellLoAfterPubCtrlLo pTail r' v r) :=
  ⟨dynWires_pPlanesOneHotScatterLoPubCtrlLo zg187_hM0 v r
      (h290 ⟨0, rw_lt0 187 8⟩ (Or.inl (by decide)))
      (fun p ↦ h290 _ (Or.inr ⟨by dsimp [rCtrlLo, basePub]; omega,
        by have := p.isLt; dsimp [rCtrlLo, basePub]; omega⟩))
      (fun b p ↦ h290 _ (Or.inl (by have := p.isLt; have := b.isLt; dsimp [rSys]; omega)))
      (fun b ↦ h290 _ (Or.inl (by have := b.isLt; dsimp [rHA]; omega)))
      (h290 ⟨90, rw_ltHB 187 8 ⟨0, by decide⟩⟩ (Or.inl (by decide))),
   hTail,
   cw_cFixupBellLoFromGatherCirc r
      (fun b ↦ h290 _ (Or.inl (by have := b.isLt; dsimp [rHA]; omega)))
      (fun b ↦ h290 _ (Or.inl (by have := b.isLt; dsimp [rBufLo]; omega)))⟩

/--
Generic `368 + 8,976 + tTail`-`T` (`0 .TOFF`) genuine-`BellLo` electronic router built from
`pDecLoEWState368_pubCtrlLo` + `pBellLoAfterPubCtrlLo`.
-/
def pBellLoFromPostXorTail {Var : Type} {n : ℕ} (pTail : RouterReg 187 8 n → DynamicCircuit Var n)
    (r' : RouterReg 187 8 n) (v : Var) (r : RouterReg 187 8 n) : DynamicCircuit Var n :=
    .seq (pDecLoEWState368_pubCtrlLo v r) (pBellLoAfterPubCtrlLo pTail r' v r)
theorem count_pBellLoFromPostXorTail {Var : Type} {n tTail : ℕ}
    (pTail : RouterReg 187 8 n → DynamicCircuit Var n) (r' : RouterReg 187 8 n) (v : Var)
    (r : RouterReg 187 8 n) (hTail : (pTail r').count .T = tTail ∧ (pTail r').count .TOFF = 0) :
    (pBellLoFromPostXorTail pTail r' v r).count .T = 9344 + tTail ∧
    (pBellLoFromPostXorTail pTail r' v r).count .TOFF = 0 := by
  have hSeqT (p q : DynamicCircuit Var n) : (p.seq q).count .T = p.count .T + q.count .T := rfl;
  have hSeqF (p q : DynamicCircuit Var n) : (p.seq q).count .TOFF = p.count .TOFF + q.count .TOFF :=
      rfl; obtain ⟨t0, f0⟩ := count_pDecLoEWState368_pubCtrlLo v r; obtain ⟨t1, f1⟩ :=
      count_pBellLoAfterPubCtrlLo pTail r' v r hTail; unfold pBellLoFromPostXorTail; rw [hSeqT,
      hSeqF, t0, f0, t1, f1]
  exact ⟨by omega, by omega⟩

theorem dynWires_pBellLoFromPostXorTail_idx {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (pTail : RouterReg 187 8 n → DynamicCircuit Var n) (r' : RouterReg 187 8 n) (v : Var)
    (r : RouterReg 187 8 n) (h290 : ∀ j : Fin (routerWidth 187 8), NoNFW290Idx j.val → S (r j))
    (hTail : DynWires S (pTail r')) : DynWires S (pBellLoFromPostXorTail pTail r' v r) :=
    ⟨dynWires_pDecLoEWState368_pubCtrlLo_idx v r h290,
    dynWires_pBellLoAfterPubCtrlLo_idx pTail r' v r h290 hTail⟩
-- Section 3B: Tier 2 (`19,146 T`, `UsedPrivRank 262` & `283` ) and Tier 1 (`19,142 T`,
-- `UsedPrivRank 307` )
-- Section 3C: Tier 3 (`19,152 T`, `UsedPrivRank 238` & `UsedSemiBell238`)
end QuantumComputation.Specs.PhotochemistrySolution.SlimBellLo19142

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2NucKinW294
open PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCoreFused PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ProviderZeroFloor
open PhotochemistrySolution.FastQft8 PhotochemistrySolution.Kinetic664
  PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.Stage2ChDiffNoNF
open PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateWalkSeam
  PhotochemistrySolution.NucPairFlags PhotochemistrySolution.AlwaysLoNuc8886W338
  PhotochemistrySolution.Stage2W325AlwaysLo PhotochemistrySolution.ParityCheckW309
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage2Load hiding
  preservesKetPred_cFixedSwapCirc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated hiding zg47_hM0
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket eval_seq_mulVec
    ket_CNOT)
attribute [local reducible] totDimCompactGen
/-!
## Part 1: Nuclear Bell-Scattered `Z_8` `MuxD1` Gather (`4,864 T`, `0 TOFF` , `UsedNucOnlineW294` )
-/

lemma rw47_eq : routerWidth 47 6 = 1394 := rfl
lemma bp47_eq : basePub 47 6 = 1238 := rfl
lemma rw47_lt_1 : 1 < routerWidth 47 6 := by rw [rw47_eq]; omega
lemma rRawHas2_47_eq_r1 {n : ℕ} (r : RouterReg 47 6 n) :
    rRawHas2 r = r ⟨1, rw47_lt_1⟩ := rfl

def UsedNucOnlineW294 {n : ℕ} (r : RouterReg 47 6 n) (w : Wire n) : Prop :=
    ∃ k : Fin (routerWidth 47 6), w = r k ∧ (k.val < 87 ∨ (110 ≤ k.val ∧ k.val < 1238) ∨
    (1244 ≤ k.val ∧ k.val < 1338) ∨ (1351 ≤ k.val ∧ k.val < 1357) ∨ (1358 ≤ k.val ∧ k.val < 1373) ∨
    (1381 ≤ k.val ∧ k.val < 1394))
theorem rNucW340_in_usedNucOnlineW294 {n : ℕ} (r : RouterReg 47 6 n) {u : Fin (routerWidth 47 6)}
    (hu : u.val < 87 ∨ (110 ≤ u.val ∧ u.val < basePub 47 6) ∨ (1244 ≤ u.val ∧ u.val < 1350) ∨
    (1351 ≤ u.val ∧ u.val < 1357) ∨ (1364 ≤ u.val ∧ u.val < 1367) ∨ (1381 ≤ u.val ∧ u.val < 1394)) :
    UsedNucOnlineW294 r (rNucW340 r u) := by
  have huLt : u.val < 1394 := rw47_eq ▸ u.isLt; let s1 := swapNucW350 u.val
  have hs1 : s1 < 87 ∨ (110 ≤ s1 ∧ s1 < 1238) ∨ (1244 ≤ s1 ∧ s1 < 1344) ∨ (1351 ≤ s1 ∧ s1 < 1357) ∨
      (1358 ≤ s1 ∧ s1 < 1367) ∨ (1381 ≤ s1 ∧ s1 < 1394) := by
    rw [bp47_eq] at hu; dsimp only [s1]; unfold swapNucW350 swapPair; split_ifs <;> omega
  let kv := swapNucW340 u.val
  have hkv : kv < 87 ∨ (110 ≤ kv ∧ kv < 1238) ∨ (1244 ≤ kv ∧ kv < 1338) ∨ (1351 ≤ kv ∧ kv < 1357) ∨
      (1358 ≤ kv ∧ kv < 1373) ∨ (1381 ≤ kv ∧ kv < 1394) := by
    have hkv_eq : kv = swapPair 1338 1367 6 s1 := rfl
    rw [hkv_eq]; unfold swapPair; split_ifs <;> omega
  exact ⟨⟨kv, swapNucW340_lt u.val u.isLt⟩, rfl, hkv⟩

def swapHBNuc0 (b : Fin 24) (j : ℕ) : ℕ := if b.val = 0 then j else swapPair 86 (86 + b.val) 1 j
lemma swapHBNuc0_lt (b : Fin 24) {j : ℕ} (hj : j < routerWidth 47 6) : swapHBNuc0 b j <
    routerWidth 47 6 := by
  unfold swapHBNuc0
  split_ifs with h0
  · exact hj
  · exact swapPair_lt (by rw [rw47_eq]; omega) (by rw [rw47_eq]; have := b.isLt; omega) hj

lemma swapHBNuc0_invol (b : Fin 24) {j : ℕ} (_ : j < routerWidth 47 6) :
    swapHBNuc0 b (swapHBNuc0 b j) = j := by
  unfold swapHBNuc0
  split_ifs with h0
  · rfl
  · exact swapPair_invol (by omega) j

lemma swapHBNuc0_outside (b : Fin 24) {j : ℕ} (hj : j < 86 ∨ 110 ≤ j) : swapHBNuc0 b j = j := by
  unfold swapHBNuc0
  split_ifs with h0
  · rfl
  · exact swapPair_fixed (by omega) (by have := b.isLt; omega)

def rOnlinePlNuc {n : ℕ} (rn : RouterReg 47 6 n) (b : Fin 24) : RouterReg 47 6 n :=
    routerOfInvol rn (swapHBNuc0 b) (fun _ hj ↦ swapHBNuc0_lt b hj)
    (fun _ hj ↦ swapHBNuc0_invol b hj)
abbrev prOnlineNuc {n : ℕ} (rn : RouterReg 47 6 n) (b : Fin 24) : PlaneReg 47 6 n :=
    planeOfRouter (rIdx12Alias (rOnlinePlNuc rn b)) b
lemma rOnlinePlNuc_fix {n : ℕ} (rn : RouterReg 47 6 n) (b : Fin 24) (j : Fin (routerWidth 47 6))
    (hj : j.val < 86 ∨ 110 ≤ j.val) : rOnlinePlNuc rn b j = rn j := by
  dsimp only [rOnlinePlNuc]; rw [routerOfInvol_apply];
  exact congrArg rn.wires (Fin.ext (swapHBNuc0_outside b hj))
lemma rOnlinePlNuc_roles_eq {n : ℕ} (rn : RouterReg 47 6 n)
    (b : Fin 24) : rHas1 (rOnlinePlNuc rn b) = rHas1 rn ∧ rRawHas2 (rOnlinePlNuc rn b) =
    rRawHas2 rn ∧ rIdx1 (rOnlinePlNuc rn b) = rIdx1 rn ∧ rIdx2 (rOnlinePlNuc rn b) = rIdx2 rn ∧
    rBufLo (rOnlinePlNuc rn b) b = rBufLo rn b ∧ rBufHi (rOnlinePlNuc rn b) b = rBufHi rn b ∧
    rHA (rOnlinePlNuc rn b) b = rHA rn b ∧ rHB (rOnlinePlNuc rn b) b = rHB rn 0 ∧
    (∀ p : Fin 47, rSys (rOnlinePlNuc rn b) p b = rSys rn p b) ∧ rCtrlLo (rOnlinePlNuc rn b) =
    rCtrlLo rn ∧ rCtrlHi (rOnlinePlNuc rn b) = rCtrlHi rn ∧ rUMsb (rOnlinePlNuc rn b) = rUMsb rn ∧
    rAMsb (rOnlinePlNuc rn b) = rAMsb rn ∧ rCReg (rOnlinePlNuc rn b) = rCReg rn ∧
    rAnc (rOnlinePlNuc rn b) = rAnc rn := by
  have rOnlinePlNuc_hB_self : rHB (rOnlinePlNuc rn b) b = rHB rn 0 := by
    let jB : Fin (routerWidth 47 6) := ⟨86 + b.val, by have := b.isLt; rw [rw47_eq]; omega⟩
    change rOnlinePlNuc rn b jB = rHB rn 0; dsimp only [rOnlinePlNuc]; rw [routerOfInvol_apply]
    have hSw : swapHBNuc0 b jB.val = 86 := by
      change swapHBNuc0 b (86 + b.val) = 86
      unfold swapHBNuc0 swapPair; split_ifs <;> omega
    have hFin : (⟨swapHBNuc0 b jB.val, swapHBNuc0_lt b jB.isLt⟩ : Fin (routerWidth 47 6)) =
        ⟨86, by rw [rw47_eq]; omega⟩ := Fin.ext hSw
    rw [hFin]; rfl
  refine ⟨rOnlinePlNuc_fix rn b _ (Or.inl (by dsimp; omega)),
    by rw [rRawHas2_47_eq_r1,
         rRawHas2_47_eq_r1]; exact rOnlinePlNuc_fix rn b _ (Or.inl (by change 1 < 86; omega)),
    funext (fun d ↦ rOnlinePlNuc_fix rn b _ (Or.inl (by have := d.isLt; dsimp; omega))),
    funext (fun d ↦ rOnlinePlNuc_fix rn b _ (Or.inl (by have := d.isLt; dsimp; omega))),
    rOnlinePlNuc_fix rn b _ (Or.inl (by have := b.isLt; dsimp; omega)),
    rOnlinePlNuc_fix rn b _ (Or.inl (by have := b.isLt; dsimp; omega)),
    rOnlinePlNuc_fix rn b _ (Or.inl (by have := b.isLt; dsimp; omega)),
    rOnlinePlNuc_hB_self,
    fun p ↦ rOnlinePlNuc_fix rn b _ (Or.inr (by dsimp [rSys]; omega)),
    funext (fun p ↦ rOnlinePlNuc_fix rn b _ (Or.inr (by dsimp [rCtrlLo, basePub]; omega))),
    funext (fun p ↦ rOnlinePlNuc_fix rn b _ (Or.inr (by dsimp [rCtrlHi, basePub]; omega))),
    funext (fun d ↦ rOnlinePlNuc_fix rn b _ (Or.inr (by dsimp [rUMsb, basePub]; omega))),
    funext (fun d ↦ rOnlinePlNuc_fix rn b _ (Or.inr (by dsimp [rAMsb, basePub]; omega))),
    funext (fun d ↦ rOnlinePlNuc_fix rn b _ (Or.inr (by dsimp [rCReg, basePub]; omega))),
    rOnlinePlNuc_fix rn b _ (Or.inr (by dsimp [rAnc, basePub]; omega))⟩

lemma validPlaneCtrlMuxD1NoNF_congr_nuc {n : ℕ} {pr₁ pr₂ : PlaneReg 47 6 n}
    {α₁ α₂ : BitAssignment n} (h1 : α₁ (pHas1 pr₁) = α₂ (pHas1 pr₂))
    (h2 : α₁ (pHas2Eff pr₁) = α₂ (pHas2Eff pr₂)) (hMin : ∀ d : Fin 6, α₁ (pNotMin pr₁ d) =
    α₂ (pNotMin pr₂ d)) (hMax : ∀ d : Fin 6, α₁ (pNotMax pr₁ d) = α₂ (pNotMax pr₂ d))
    (hU : ∀ d : Fin 6, 1 ≤ d.val → α₁ (pUMsb pr₁ d) = α₂ (pUMsb pr₂ d))
    (hCL : ∀ p : Fin 47, α₁ (pCtrlLo pr₁ p) = α₂ (pCtrlLo pr₂ p))
    (hCH : ∀ p : Fin 47, α₁ (pCtrlHi pr₁ p) = α₂ (pCtrlHi pr₂ p)) : ValidPlaneCtrlMuxD1NoNF pr₁ α₁ ↔
    ValidPlaneCtrlMuxD1NoNF pr₂ α₂ := by
  let δ₁ := toggleNotFlags pr₁ α₁; let δ₂ := toggleNotFlags pr₂ α₂
  have nMinInj : ∀ {pr : PlaneReg 47 6 n} {a b : Fin 6}, a ≠ b → pNotMin pr a ≠ pNotMin pr b :=
    fun {pr} {a b} h e ↦
        h
        (Fin.ext
        (by have hv := congrArg Fin.val (pr.wires.injective e); dsimp [pNotMin] at hv; omega))
  have nMaxInj : ∀ {pr : PlaneReg 47 6 n} {a b : Fin 6}, a ≠ b → pNotMax pr a ≠ pNotMax pr b :=
    fun {pr} {a b} h e ↦
        h
        (Fin.ext
        (by have hv := congrArg Fin.val (pr.wires.injective e); dsimp [pNotMax] at hv; omega))
  have eq_oth {i : Fin (planeWidth 47 6)} (h : α₁ (pr₁ i) = α₂ (pr₂ i))
      (hi : i.val < 14 ∨ 26 ≤ i.val) : δ₁ (pr₁ i) = δ₂ (pr₂ i) :=
    (toggleNotFlagsLoop_other pr₁ α₁
      (fun d ↦ pr_ne pr₁ (by have := d.isLt; dsimp [pNotMin]; omega))
      (fun d ↦ pr_ne pr₁ (by have := d.isLt; dsimp [pNotMax]; omega)) 6 le_rfl).trans
      (h.trans (toggleNotFlagsLoop_other pr₂ α₂
        (fun d ↦ pr_ne pr₂ (by have := d.isLt; dsimp [pNotMin]; omega))
        (fun d ↦ pr_ne pr₂ (by have := d.isLt; dsimp [pNotMax]; omega)) 6 le_rfl).symm)
  have e1 : δ₁ (pHas1 pr₁) = δ₂ (pHas1 pr₂) := eq_oth h1 (Or.inl (by dsimp; omega))
  have e2 : δ₁ (pHas2Eff pr₁) = δ₂ (pHas2Eff pr₂) :=
    eq_oth h2 (Or.inl (by dsimp [pHas2Eff, planeWidth]; omega))
  have eU : ∀ d : Fin 6, 1 ≤ d.val → δ₁ (pUMsb pr₁ d) = δ₂ (pUMsb pr₂ d) :=
    fun d hd ↦ eq_oth (hU d hd) (Or.inl (by have := d.isLt; dsimp; omega))
  have eCL : ∀ p : Fin 47, δ₁ (pCtrlLo pr₁ p) = δ₂ (pCtrlLo pr₂ p) :=
    fun p ↦ eq_oth (hCL p) (Or.inr (by have := p.isLt; dsimp; omega))
  have eCH : ∀ p : Fin 47, δ₁ (pCtrlHi pr₁ p) = δ₂ (pCtrlHi pr₂ p) :=
    fun p ↦ eq_oth (hCH p) (Or.inr (by have := p.isLt; dsimp; omega))
  have hLoop : ∀ (k : ℕ) (hk : k ≤ 6) (d : Fin 6), toggleNotFlagsLoop pr₁ α₁ k hk (pNotMin pr₁ d) =
      toggleNotFlagsLoop pr₂ α₂ k hk (pNotMin pr₂ d) ∧
      toggleNotFlagsLoop pr₁ α₁ k hk (pNotMax pr₁ d) =
      toggleNotFlagsLoop pr₂ α₂ k hk (pNotMax pr₂ d) := by
    intro k; induction k with
    | zero => intro _ d; exact ⟨hMin d, hMax d⟩
    | succ k ih =>
        intro hk d; obtain ⟨ihMin, ihMax⟩ := ih (Nat.le_of_succ_le hk) d;
        let dk : Fin 6 := ⟨k, hk⟩; dsimp only [toggleNotFlagsLoop]
        rw [Function.update_of_ne (pr_ne pr₁ (by have := d.isLt; dsimp [dk]; omega) : pNotMin pr₁ d
            ≠ pNotMax pr₁ dk),
            Function.update_of_ne (pr_ne pr₂ (by have := d.isLt; dsimp [dk]; omega) : pNotMin pr₂ d
                ≠ pNotMax pr₂ dk)]
        constructor
        · by_cases hdk : d = dk
          · subst hdk; rw [Function.update_self, Function.update_self];
            exact congrArg₂ (· + ·) ihMin h1
          · rw [Function.update_of_ne (nMinInj hdk), Function.update_of_ne (nMinInj hdk), ihMin]
        · by_cases hdk : d = dk
          · subst hdk; rw [Function.update_self, Function.update_self];
            exact congrArg₂ (· + ·) ihMax h2
          · rw [Function.update_of_ne (nMaxInj hdk), Function.update_of_ne (nMaxInj hdk),
                Function.update_of_ne (pr_ne pr₁ (by have := d.isLt; dsimp [dk]; omega) : pNotMax
                    pr₁ d ≠ pNotMin pr₁ dk),
                Function.update_of_ne (pr_ne pr₂ (by have := d.isLt; dsimp [dk]; omega) : pNotMax
                    pr₂ d ≠ pNotMin pr₂ dk),
                ihMax]
  have eMin : ∀ d : Fin 6, δ₁ (pNotMin pr₁ d) = δ₂ (pNotMin pr₂ d) := fun d ↦ (hLoop 6 le_rfl d).1
  have eMax : ∀ d : Fin 6, δ₁ (pNotMax pr₁ d) = δ₂ (pNotMax pr₂ d) := fun d ↦ (hLoop 6 le_rfl d).2
  dsimp only [ValidPlaneCtrlMuxD1NoNF, ValidPlaneCtrlMuxD1]
  simp only [show toggleNotFlags pr₁ α₁ = δ₁ from rfl, show toggleNotFlags pr₂ α₂ = δ₂ from rfl,
    e1, e2, eMin, eMax, eCL, eCH]
  constructor <;> (
    rintro ⟨c1, c2, c3, c4⟩
    refine ⟨c1, fun hz1 ↦ ?_, c3, fun hH1 ↦ ?_⟩
    · obtain ⟨c2a, c2b, c2c⟩ := c2 hz1
      refine ⟨c2a, c2b, fun d hd ↦ ?_⟩
      first | exact (eU d hd).symm.trans (c2c d hd) | exact (eU d hd).trans (c2c d hd)
    · obtain ⟨pMin, hp1, hp0, hpN, hpS, hpD⟩ := c4 hH1
      refine ⟨pMin, hp1, hp0, hpN, fun hH20 ↦ ?_, fun hH21 ↦ ?_⟩
      · obtain ⟨dS, hdS, hdU⟩ := hpS hH20
        exact ⟨dS, hdS, fun d hd ↦ by
          first | exact (eU d hd).symm.trans (hdU d hd) | exact (eU d hd).trans (hdU d hd)⟩
      · obtain ⟨pMax, hlt, hm1, hm0, hmN, dS, hd1, hd2, hdU⟩ := hpD hH21
        exact ⟨pMax, hlt, hm1, hm0, hmN, dS, hd1, hd2, fun d hd ↦ by
          first | exact (eU d hd).symm.trans (hdU d hd) | exact (eU d hd).trans (hdU d hd)⟩)

section NucBellZ8Core
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld hiding ket sqrtHalf
  eval_seq_mulVec
open PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2WWork341
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimBellLo19142
    (pPlanesOneHotScatterLoLoop count_pPlanesOneHotScatterLoLoop dynWires_pPlanesOneHotScatterLoLoop
    uBellLoPreScatter supportedOn_validZeroGatedWithoutHA_uBellLoPreScatter
    subspaceStep_pPlanesOneHotScatterLoLoop_nuc cFixupBellLoFromGatherCirc
    count_cFixupBellLoFromGatherCirc cw_cFixupBellLoFromGatherCirc
    hcnotSupportedIn_cFixupBellLoFromGatherCirc cFixupBellLoFromGatherCirc_mul_eq)
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
/-- Role equalities for the `(47, 6)` online nuclear plane view `prOnlineNuc rn b`. -/
theorem prOnlineNuc_roles {n : ℕ} (rn : RouterReg 47 6 n) (b : Fin 24) :
    pHas1 (prOnlineNuc rn b) = rHas1 rn ∧
    pHas2Eff (prOnlineNuc rn b) = rRawHas2 rn ∧
    pBufLo (prOnlineNuc rn b) = rBufLo rn b ∧
    pBufHi (prOnlineNuc rn b) = rBufHi rn b ∧
    pHA (prOnlineNuc rn b) = rHA rn b ∧
    pHB (prOnlineNuc rn b) = rHB rn 0 ∧
    pAnc (prOnlineNuc rn b) = rAnc rn ∧
    pUMsb (prOnlineNuc rn b) = rUMsb rn ∧
    pNotMin (prOnlineNuc rn b) = rIdx1 rn ∧
    pNotMax (prOnlineNuc rn b) = rIdx2 rn ∧
    pAMsb (prOnlineNuc rn b) = rAMsb rn ∧
    pCReg (prOnlineNuc rn b) = rCReg rn ∧
    pCtrlLo (prOnlineNuc rn b) = rCtrlLo rn ∧
    pCtrlHi (prOnlineNuc rn b) = rCtrlHi rn ∧
    (∀ p : Fin 47, pSys (prOnlineNuc rn b) p = rSys rn p b) := by
  obtain ⟨b1, b2, _, bBL, bBH, bHA, bHB, bAnc, bUM, bNMin, bNMax, bAM, bCR, bCL, bCH, bSy⟩ :=
    planeOfRouter_rIdx12Alias_roles (rOnlinePlNuc rn b) b
  obtain ⟨eH1, eH2, eI1, eI2, eBL, eBH, eHA, eHB, eSys, eCL, eCH, eUM, eAM, eCR, eAnc⟩ :=
    rOnlinePlNuc_roles_eq rn b
  exact ⟨b1.trans eH1, b2.trans eH2, bBL.trans ((planeOfRouter_bufLo _ b).trans eBL),
    bBH.trans ((planeOfRouter_bufHi _ b).trans eBH), bHA.trans ((planeOfRouter_hA _ b).trans eHA),
    bHB.trans ((planeOfRouter_hB _ b).trans eHB), bAnc.trans eAnc, bUM.trans eUM, bNMin.trans eI1,
    bNMax.trans eI2, bAM.trans eAM, bCR.trans eCR, bCL.trans eCL, bCH.trans eCH,
    fun p ↦ (congrFun bSy p).trans ((planeOfRouter_sys _ b p).trans (eSys p))⟩

/-- Router index witness for every wire in `prOnlineNuc rn k`. -/
theorem prOnlineNuc_wire_idx {n : ℕ} (rn : RouterReg 47 6 n) (k : Fin 24)
    (i : Fin (planeWidth 47 6)) :
    ∃ u : Fin (routerWidth 47 6),
      prOnlineNuc rn k i = rn u ∧
      (u.val < 14 ∨ u.val = 14 + k.val ∨ u.val = 38 + k.val ∨
       u.val = 62 + k.val ∨ 86 ≤ u.val) := by
  have hi := i.isLt
  unfold planeWidth at hi
  have hk := k.isLt
  obtain ⟨_, eH2, eI1, eI2, _, _, _, _, _, _, _, _, _, _, _⟩ := rOnlinePlNuc_roles_eq rn k
  by_cases hi1 : i.val = 1
  · have hiEq : i = ⟨1, by unfold planeWidth; omega⟩ := Fin.ext hi1
    rw [hiEq, show prOnlineNuc rn k ⟨1, _⟩ = pHas2Eff (prOnlineNuc rn k) from rfl,
        (planeOfRouter_rIdx12Alias_roles (rOnlinePlNuc rn k) k).2.1, eH2, rRawHas2_47_eq_r1]
    exact ⟨⟨1, by rw [rw47_eq]; omega⟩, rfl, Or.inl (by change 1 < 14; omega)⟩
  · by_cases hiMin : 14 ≤ i.val ∧ i.val < 20
    · let d : Fin 6 := ⟨i.val - 14, by omega⟩
      have hiEq : i = ⟨14 + d.val, by unfold planeWidth; omega⟩ := Fin.ext (by dsimp [d]; omega)
      rw [hiEq, show prOnlineNuc rn k ⟨14 + d.val, _⟩ = pNotMin (prOnlineNuc rn k) d from rfl,
          congrFun (planeOfRouter_rIdx12Alias_roles (rOnlinePlNuc rn k) k).2.2.2.2.2.2.2.2.2.1 d,
              eI1]
      exact ⟨_, rfl, Or.inl (by have := d.isLt; dsimp [rIdx1]; omega)⟩
    · by_cases hiMax : 20 ≤ i.val ∧ i.val < 26
      · let d : Fin 6 := ⟨i.val - 20, by omega⟩
        have hiEq : i = ⟨20 + d.val, by unfold planeWidth; omega⟩ := Fin.ext (by dsimp [d]; omega)
        rw [hiEq, show prOnlineNuc rn k ⟨20 + d.val, _⟩ = pNotMax (prOnlineNuc rn k) d from rfl,
            congrFun (planeOfRouter_rIdx12Alias_roles (rOnlinePlNuc rn k) k).2.2.2.2.2.2.2.2.2.2.1
                d, eI2]
        exact ⟨_, rfl, Or.inl (by have := d.isLt; dsimp [rIdx2]; omega)⟩
      · rw [planeOfRouter_rIdx12Alias_apply_of_ne (rOnlinePlNuc rn k) k i hi1 (by omega)]
        let pv := planeIdxVal 47 6 k i.val
        have hpvLt : pv < routerWidth 47 6 := planeIdxVal_lt k i
        let uv := swapHBNuc0 k pv
        have huvLt : uv < routerWidth 47 6 := swapHBNuc0_lt k hpvLt
        refine ⟨⟨uv, huvLt⟩, ?_, ?_⟩
        · change rOnlinePlNuc rn k ⟨pv, hpvLt⟩ = rn ⟨uv, huvLt⟩
          dsimp only [rOnlinePlNuc]
          rw [routerOfInvol_apply]
        · have hpvCases :
              pv < 14 ∨ pv = 14 + k.val ∨ pv = 38 + k.val ∨
              pv = 62 + k.val ∨ 86 ≤ pv := by
            dsimp only [pv]
            unfold planeIdxVal
            split_ifs with c8 c5d
            · unfold planeIdxFixed basePub
              split_ifs <;> omega
            · unfold planeIdxD basePub
              split_ifs <;> omega
            · unfold planeIdxM basePub
              split_ifs <;> omega
          dsimp only [uv]
          unfold swapHBNuc0 swapPair
          split_ifs <;> omega

/--
Pairwise buffer disjointness across planes `Fin 24` for `pZ8MuxD1GatherPlanesDyn` on `(47, 6)` .
-/
theorem hDisjPl_prOnlineNuc {n : ℕ} (rn : RouterReg 47 6 n)
    (j k : Fin 24) (hjk : j ≠ k) (i : Fin (planeWidth 47 6)) :
    pBufLo (prOnlineNuc rn j) ≠ prOnlineNuc rn k i ∧
    pBufHi (prOnlineNuc rn j) ≠ prOnlineNuc rn k i := by
  have hj := j.isLt
  have hk := k.isLt
  have hneVal : j.val ≠ k.val := Fin.val_ne_of_ne hjk
  obtain ⟨_, _, eBL, eBH, _⟩ := prOnlineNuc_roles rn j
  obtain ⟨u, eqW, hu⟩ := prOnlineNuc_wire_idx rn k i
  rw [eBL, eBH, eqW]
  exact ⟨rr_ne rn (by dsimp [rBufLo]; omega), rr_ne rn (by dsimp [rBufHi]; omega)⟩

/--
Evaluation-disjointness bundle for `uDirectGatherPlanesAfterXor_ket_eval` on `prOnlineNuc rn` .
-/
theorem hDisjEval_prOnlineNuc {n : ℕ} (rn : RouterReg 47 6 n)
    (j k : Fin 24) (hjk : j ≠ k) :
    pBufLo (prOnlineNuc rn j) ≠ pBufLo (prOnlineNuc rn k) ∧
    pBufLo (prOnlineNuc rn j) ≠ pBufHi (prOnlineNuc rn k) ∧
    pBufHi (prOnlineNuc rn j) ≠ pBufLo (prOnlineNuc rn k) ∧
    pBufHi (prOnlineNuc rn j) ≠ pBufHi (prOnlineNuc rn k) ∧
    (∀ p : Fin 47,
      pBufLo (prOnlineNuc rn j) ≠ pCtrlLo (prOnlineNuc rn k) p ∧
      pBufLo (prOnlineNuc rn j) ≠ pCtrlHi (prOnlineNuc rn k) p ∧
      pBufLo (prOnlineNuc rn j) ≠ pSys (prOnlineNuc rn k) p ∧
      pBufHi (prOnlineNuc rn j) ≠ pCtrlLo (prOnlineNuc rn k) p ∧
      pBufHi (prOnlineNuc rn j) ≠ pCtrlHi (prOnlineNuc rn k) p ∧
      pBufHi (prOnlineNuc rn j) ≠ pSys (prOnlineNuc rn k) p) :=
  let d := hDisjPl_prOnlineNuc rn j k hjk
  ⟨(d _).1, (d _).1, (d _).2, (d _).2,
   fun _ ↦ ⟨(d _).1, (d _).1, (d _).1, (d _).2, (d _).2, (d _).2⟩⟩

/-- Every active `Z_8` gather wire of `prOnlineNuc (rNucW340 r) b` lies in `UsedNucOnlineW294 r`. -/
theorem prOnlineNuc_z8_roles_usedNucOnlineW294 {n : ℕ} {S : Wire n → Prop}
    (r : RouterReg 47 6 n) (hS : ∀ w, UsedNucOnlineW294 r w → S w) (b : Fin 24) :
    let pr := prOnlineNuc (rNucW340 r) b
    S (pHas2Eff pr) ∧ S (pBufLo pr) ∧ S (pBufHi pr) ∧ S (pHB pr) ∧
    (∀ d : Fin 6, 1 ≤ d.val → S (pUMsb pr d)) ∧
    (∀ d : Fin 6, 1 ≤ d.val → S (pAMsb pr d)) ∧
    (∀ p : Fin 47, S (pCtrlLo pr p)) ∧
    (∀ p : Fin 47, S (pSys pr p)) := by
  intro pr
  let rn := rNucW340 r
  have hU {w : Wire n} {u : Fin (routerWidth 47 6)} (e : w = rn u)
      (hu : u.val < 87 ∨ (110 ≤ u.val ∧ u.val < basePub 47 6) ∨
       (1244 ≤ u.val ∧ u.val < 1350) ∨ (1351 ≤ u.val ∧ u.val < 1357) ∨
       (1364 ≤ u.val ∧ u.val < 1367) ∨ (1381 ≤ u.val ∧ u.val < 1394)) : S w :=
    e ▸ hS _ (rNucW340_in_usedNucOnlineW294 r hu)
  obtain ⟨_, eH2, eBL, eBH, _, eHB, _, eUM, _, _, eAM, _, eCL, _, eSy⟩ := prOnlineNuc_roles rn b
  refine ⟨hU (eH2.trans (rRawHas2_47_eq_r1 rn)) (Or.inl (by decide)), hU eBL (Or.inl ?_),
    hU eBH (Or.inl ?_), hU eHB (Or.inl ?_),
    fun d _ ↦ hU (congrFun eUM d) (Or.inr (Or.inr (Or.inr (Or.inl ?_)))),
    fun d _ ↦ hU (congrFun eAM d) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))),
    fun p ↦ hU (congrFun eCL p) (Or.inr (Or.inr (Or.inl ?_))),
    fun p ↦ hU (eSy p) (Or.inr (Or.inl ?_))⟩
  all_goals
    dsimp [rBufLo, rBufHi, rHB, rUMsb, rAMsb, rCtrlLo, rSys, basePub]
    omega

/-- Every active `Z_8` gather wire of `prOnlineNuc rn b` is disjoint from `rHA rn b'`. -/
theorem prOnlineNuc_z8_roles_ne_rHA {n : ℕ} (rn : RouterReg 47 6 n) (b b' : Fin 24) :
    let pr := prOnlineNuc rn b
    pHas2Eff pr ≠ rHA rn b' ∧ pBufLo pr ≠ rHA rn b' ∧
    pBufHi pr ≠ rHA rn b' ∧ pHB pr ≠ rHA rn b' ∧
    (∀ d : Fin 6, 1 ≤ d.val → pUMsb pr d ≠ rHA rn b') ∧
    (∀ d : Fin 6, 1 ≤ d.val → pAMsb pr d ≠ rHA rn b') ∧
    (∀ p : Fin 47, pCtrlLo pr p ≠ rHA rn b') ∧
    (∀ p : Fin 47, pSys pr p ≠ rHA rn b') := by
  intro pr
  obtain ⟨_, eH2, eBL, eBH, _, eHB, _, eUM, _, _, eAM, _, eCL, _, eSy⟩ := prOnlineNuc_roles rn b
  have neHA {w : Wire n} {u : Fin (routerWidth 47 6)} (e : w = rn u) (h : u.val ≠ 62 + b'.val) :
      w ≠ rHA rn b' := e ▸ rr_ne rn h
  refine ⟨neHA (eH2.trans (rRawHas2_47_eq_r1 rn))
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 62 _))),
    neHA eBL ?_, neHA eBH ?_, neHA eHB ?_,
    fun d _ ↦ neHA (congrFun eUM d) ?_, fun d _ ↦ neHA (congrFun eAM d) ?_,
    fun p ↦ neHA (congrFun eCL p) ?_, fun p ↦ neHA (eSy p) ?_⟩
  all_goals
    dsimp [rBufLo, rBufHi, rHB, rUMsb, rAMsb, rCtrlLo, rSys, basePub]
    omega

/--
Wrapper programs `constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn)` and `pXorCtrlHiToLo rn`
never touch `rHA rn b'`.
-/
theorem hdr_and_xor_progSupportedIn_ne_rHA {n : ℕ} (rn : RouterReg 47 6 n) (b' : Fin 24) :
    ProgSupportedIn (· ≠ rHA rn b') (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn)) ∧
    ProgSupportedIn (· ≠ rHA rn b') (pXorCtrlHiToLo rn) := by
  have hbp : basePub 47 6 = 1238 := rfl
  have hb' := b'.isLt
  constructor
  · refine progSupportedIn_mono ?_
      (progSupportedIn_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG zg47_hD2 rn)
        (progSupportedIn_pUMsbHdrZG zg47_hD2 rn))
    rintro w ⟨⟨k, hk, rfl⟩ | ⟨d, rfl⟩, _⟩
    · exact rr_ne rn (by dsimp [rHA]; omega)
    · exact rr_ne rn (by have := d.isLt; dsimp [rUMsb, rHA]; rw [hbp]; omega)
  · exact progSupportedIn_pXorCtrlHiToLo rn
      (fun p ↦ rr_ne rn (by dsimp [rCtrlLo, rHA]; rw [hbp]; omega))
      (fun p ↦ rr_ne rn (by dsimp [rCtrlHi, rHA]; rw [hbp]; omega))

/-- Bit-assignment image of `ket β` after `U_mid`, `F_hdr1`, and `uPlaneXorCtrl` on `(47, 6)`. -/
def f_xi_nuc_al {n : ℕ} (rn : RouterReg 47 6 n) (β : BitAssignment n) : BitAssignment n :=
  planeXorBits (planeOfRouter (rHas2Alias rn) 0) (f_eta_nuc_al rn β)

/-- Ket action of `uPlaneXorCtrl (planeOfRouter (rHas2Alias rn) 0)` composed with `U_prep`. -/
theorem uPlaneXorCtrl_uPrep_nuc_mulVec_ket {n : ℕ} (rn : RouterReg 47 6 n) (β : BitAssignment n) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    let U_mid : Unitary (2 ^ n) := (cFlipLo0 zg47_hM0 rn).eval * (ULo * UHi)
    let U_prep : Unitary (2 ^ n) :=
      (fwdCirc (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn))).eval * U_mid
    let UX0 := uPlaneXorCtrl (planeOfRouter (rHas2Alias rn) 0)
    (UX0.1 * U_prep.1).mulVec (ket β) = ket (f_xi_nuc_al rn β) := by
  intro dLo dHi ULo UHi U_mid U_prep UX0
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
  have hMidKet : U_mid.1.mulVec (ket β) = ket (f_mid_nuc_al rn β) := by
    dsimp only [U_mid, f_mid_nuc_al]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket, cFlipLo0_mulVec_ket]
  have hEtaKet : U_prep.1.mulVec (ket β) = ket (f_eta_nuc_al rn β) := by
    dsimp only [U_prep, f_eta_nuc_al]
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hMidKet, fwdCirc_mulVec_ket]
  rw [← Matrix.mulVec_mulVec, hEtaKet, ← ket_sr, uPlaneXorCtrl_mulVec_ket]
  rfl

/-- Online nuclear plane control and clean invariants on `f_eta_nuc_al rn β`. -/
theorem validPlaneOnline_f_eta_nuc_al {n : ℕ} (rn : RouterReg 47 6 n) (β : BitAssignment n)
    (hβ : ValidZeroGatedSortedRouterInput rn β) (b : Fin 24) :
    ValidPlaneCtrlMuxD1NoNFAlwaysLo (prOnlineNuc rn b) (f_eta_nuc_al rn β) ∧
    ValidPlaneCleanMuxD1 (prOnlineNuc rn b) (f_eta_nuc_al rn β) := by
  obtain ⟨_, _, hVP⟩ := ketProps_pNucCoreMidAlwaysLo rn β hβ
  obtain ⟨b1, b2, bBL, bBH, bHA, bHB, bAnc, bUM, bNMin, bNMax, bAM, bCR, bCL, bCH, _⟩ :=
    prOnlineNuc_roles rn b
  obtain ⟨z1, z2, _, zBL, zBH, zHA, _, zAnc, zUM, zNMin, zNMax, zAM, zCR, zCL, zCH, _⟩ :=
    planeOfRouter_rIdx12Alias_roles rn b
  have zHB0 := (planeOfRouter_rIdx12Alias_roles rn 0).2.2.2.2.2.2.1
  have hp1Eq := b1.trans z1.symm
  refine ⟨by
    dsimp only [ValidPlaneCtrlMuxD1NoNFAlwaysLo]
    rw [hp1Eq]
    exact (validPlaneCtrlMuxD1NoNF_congr_nuc (congrArg _ hp1Eq) (by rw [b2, z2])
      (fun d ↦ by rw [congrFun bNMin d, congrFun zNMin d])
      (fun d ↦ by rw [congrFun bNMax d, congrFun zNMax d])
      (fun d _ ↦ by rw [congrFun bUM d, congrFun zUM d])
      (fun p ↦ by rw [congrFun bCL p, congrFun zCL p])
      (fun p ↦ by rw [congrFun bCH p, congrFun zCH p])).mpr (hVP b).1, ?_⟩
  have hZb := (hVP b).2
  have hZ0 := (hVP 0).2
  dsimp only [ValidPlaneCleanMuxD1] at hZb hZ0 ⊢
  rw [bBL, ← planeOfRouter_bufLo rn b, ← zBL, bBH, ← planeOfRouter_bufHi rn b, ← zBH,
      bHA, ← planeOfRouter_hA rn b, ← zHA, bHB, ← planeOfRouter_hB rn 0, ← zHB0,
      bAM, ← zAM, bCR, ← zCR, bAnc, ← zAnc]
  exact ⟨hZb.1, hZb.2.1, hZb.2.2.1, hZ0.2.2.2.1, hZb.2.2.2.2.1, hZb.2.2.2.2.2.1, hZb.2.2.2.2.2.2⟩

/--
Involution of `planeXorBits` between `planeOfRouter (rHas2Alias rn) 0` and `prOnlineNuc rn b` .
-/
theorem planeXorBits_prOnlineNuc_f_xi {n : ℕ} (rn : RouterReg 47 6 n)
    (β : BitAssignment n) (b : Fin 24) :
    planeXorBits (prOnlineNuc rn b) (f_xi_nuc_al rn β) = f_eta_nuc_al rn β := by
  let pr0 := planeOfRouter (rHas2Alias rn) 0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, bCL, bCH, _⟩ := prOnlineNuc_roles rn b
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, zCL0, zCH0, _⟩ :=
    planeOfRouter_rHas2Alias_roles rn 0
  have eCL := bCL.trans zCL0.symm
  have eCH := bCH.trans zCH0.symm
  funext w
  dsimp only [f_xi_nuc_al]
  by_cases hw : ∃ p : Fin 47, w = pCtrlLo (prOnlineNuc rn b) p
  · obtain ⟨p, rfl⟩ := hw
    rw [planeXorBits_ctrlLo, congrFun eCL p, congrFun eCH p, planeXorBits_ctrlLo,
        planeXorBits_other pr0 _ fun p' e ↦ rr_ne rn (by
          dsimp [rCtrlHi, rCtrlLo, basePub]
          omega) ((congrFun zCH0 p).symm.trans (e.trans (congrFun zCL0 p'))),
        z2_add_self_cancel]
  · rw [planeXorBits_other (prOnlineNuc rn b) _ fun p e ↦ hw ⟨p, e⟩,
        planeXorBits_other pr0 _ fun p e ↦ hw ⟨p, e.trans (congrFun eCL p).symm⟩]

/-- Pointwise `ValidZ8MuxD1GatherPlaneIn` for all `24` nuclear planes on `f_xi_nuc_al rn β`. -/
theorem validZ8MuxD1GatherPlaneIn_prOnlineNuc_ket {n : ℕ} (rn : RouterReg 47 6 n)
    (β : BitAssignment n) (hβ : ValidZeroGatedSortedRouterInput rn β) (b : Fin 24) :
    ValidZ8MuxD1GatherPlaneIn (prOnlineNuc rn b) (f_xi_nuc_al rn β) := by
  obtain ⟨hCtrl, hCln⟩ := validPlaneOnline_f_eta_nuc_al rn β hβ b
  obtain ⟨_, _, bBL, bBH, _, bHB, _, _, _, _, bAM, _, _, _, _⟩ := prOnlineNuc_roles rn b
  have zCL0 := (planeOfRouter_rHas2Alias_roles rn 0).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hOth {w : Wire n} (hw : ∀ p : Fin 47, w ≠ rCtrlLo rn p) :
      f_xi_nuc_al rn β w = f_eta_nuc_al rn β w :=
    planeXorBits_other (planeOfRouter (rHas2Alias rn) 0) _ fun p e ↦
      hw p (e.trans (congrFun zCL0 p))
  refine ⟨(planeXorBits_prOnlineNuc_f_xi rn β b).symm ▸ hCtrl,
    (hOth fun p ↦ bHB ▸ rr_ne rn ?_).trans hCln.2.2.2.1,
    (hOth fun p ↦ bBL ▸ rr_ne rn ?_).trans hCln.1,
    (hOth fun p ↦ bBH ▸ rr_ne rn ?_).trans hCln.2.1,
    fun d hd ↦ (hOth fun p ↦ congrFun bAM d ▸ rr_ne rn ?_).trans (hCln.2.2.2.2.1 d hd)⟩
  all_goals
    dsimp [rHB, rBufLo, rBufHi, rAMsb, rCtrlLo, basePub]
    omega

/-- Subspace support theorem feeding `subspaceStep_pZ8MuxD1GatherPlanesDyn` on `(47, 6)`. -/
theorem supportedOn_validZ8MuxD1GatherPlaneIn_prOnlineNuc {n : ℕ}
    (rn : RouterReg 47 6 n) (R₀ : Operator (2 ^ n))
    (hR₀ : SupportedOn (ValidZeroGatedSortedRouterInput rn) R₀) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    let U_mid : Unitary (2 ^ n) := (cFlipLo0 zg47_hM0 rn).eval * (ULo * UHi)
    let U_prep : Unitary (2 ^ n) :=
      (fwdCirc (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn))).eval * U_mid
    let UX0 := uPlaneXorCtrl (planeOfRouter (rHas2Alias rn) 0)
    SupportedOn (fun ξ ↦ ∀ b : Fin 24, ValidZ8MuxD1GatherPlaneIn (prOnlineNuc rn b) ξ)
      (UX0.1 * (U_prep.1 * R₀)) := by
  intro dLo dHi ULo UHi U_mid U_prep UX0 A B hAB
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
  simp only [← Matrix.mul_assoc]
  refine hR₀ _ _ fun β hβ ↦ ?_
  rw [Matrix.mul_assoc A UX0.1 U_prep.1, Matrix.mul_assoc B UX0.1 U_prep.1,
      ← Matrix.mulVec_mulVec _ A (UX0.1 * U_prep.1),
      ← Matrix.mulVec_mulVec _ B (UX0.1 * U_prep.1),
      ket_sr, uPlaneXorCtrl_uPrep_nuc_mulVec_ket rn β, ← ket_sr]
  exact hAB (f_xi_nuc_al rn β) (validZ8MuxD1GatherPlaneIn_prOnlineNuc_ket rn β hβ)

/--
One-hot decomposition of `(cLoAlways rn β, routerCtrlHi rn β)` on
`ValidZeroGatedSortedRouterInput rn β` .
-/
theorem oneHot_ctrlLoHi_of_validZeroGated_nuc {n : ℕ} (rn : RouterReg 47 6 n)
    (β : BitAssignment n) (hβ : ValidZeroGatedSortedRouterInput rn β) :
    ∃ pMin : Fin 47,
      cLoAlways rn β pMin = 1 ∧
      (∀ p : Fin 47, p ≠ pMin → cLoAlways rn β p = 0) ∧
      ((∀ p : Fin 47, routerCtrlHi rn β p = 0) ∨
       (∃ pMax : Fin 47, pMin.val < pMax.val ∧ routerCtrlHi rn β pMax = 1 ∧
         ∀ p : Fin 47, p ≠ pMax → routerCtrlHi rn β p = 0)) := by
  obtain ⟨hηLo, hηHi, hVP⟩ := ketProps_pNucCoreMidAlwaysLo rn β hβ
  let r₀ := planeOfRouter (rIdx12Alias rn) 0
  obtain ⟨hHas1_r₀, _, _, _, _, _, _, _, _, _, _, _, _, hCL0, hCH0, _⟩ :=
    planeOfRouter_rIdx12Alias_roles rn 0
  let η := f_eta_nuc_al rn β
  let η₁ := Function.update η (pHas1 r₀) 1
  let ηT := toggleNotFlags r₀ η₁
  have hC0 : ValidPlaneCtrlMuxD1 r₀ ηT := (hVP 0).1
  have hT_has1 : ηT (pHas1 r₀) = 1 :=
    (toggleNotFlags_other r₀ η₁ (fun _ ↦ pr_ne r₀ (by dsimp; omega))
      (fun _ ↦ pr_ne r₀ (by dsimp; omega))).trans (Function.update_self _ _ _)
  have hTog {u : Fin (planeWidth 47 6)} (hu : 26 ≤ u.val) : ηT (r₀ u) = η (r₀ u) :=
    (toggleNotFlags_other r₀ η₁ (fun _ ↦ pr_ne r₀ (by dsimp; omega))
      (fun _ ↦ pr_ne r₀ (by dsimp; omega))).trans
      (Function.update_of_ne (pr_ne r₀ (by dsimp; omega)) _ _)
  have hT_cL (p : Fin 47) : ηT (pCtrlLo r₀ p) = cLoAlways rn β p :=
    (hTog (by dsimp; omega)).trans
      (by change η (pCtrlLo r₀ p) = _; dsimp only [r₀]; rw [congrFun hCL0 p]; exact hηLo p)
  have hT_cH (p : Fin 47) : ηT (pCtrlHi r₀ p) = routerCtrlHi rn β p :=
    (hTog (by dsimp; omega)).trans
      (by change η (pCtrlHi r₀ p) = _; dsimp only [r₀]; rw [congrFun hCH0 p]; exact hηHi p)
  rcases hC0.2.2.2 hT_has1 with ⟨pMin, hcL1', hcL0', _, _, hCase1⟩
  refine ⟨pMin, (hT_cL pMin).symm.trans hcL1',
    fun p hp ↦ (hT_cL p).symm.trans (hcL0' p hp), ?_⟩
  rcases PhotochemistrySolution.SortedRouterSpec.zmod2_cases (ηT (pHas2Eff r₀)) with hz2 | ho2
  · exact Or.inl fun p ↦ (hT_cH p).symm.trans ((hC0.2.2.1 hz2).1 p)
  · obtain ⟨pMax, hlt, hcH1', hcH0', _⟩ := hCase1 ho2
    exact Or.inr ⟨pMax, hlt, (hT_cH pMax).symm.trans hcH1',
      fun p hp ↦ (hT_cH p).symm.trans (hcH0' p hp)⟩

private theorem toggleOneHotBits_congr_on {D N n : ℕ} {S : Wire n → Prop}
    (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin N → Wire n)
    {δ₁ δ₂ : BitAssignment n}
    (hS : ∀ w, S w → δ₁ w = δ₂ w)
    (hHas : δ₁ wHas = δ₂ wHas)
    (hIdx : idxValD wIdx δ₁ = idxValD wIdx δ₂)
    (hOutS : ∀ j : Fin N, S (wOut j))
    (w : Wire n) (hw : S w) :
    toggleOneHotBits wHas wIdx wOut δ₁ w = toggleOneHotBits wHas wIdx wOut δ₂ w := by
  by_cases h1 : idxValD wIdx δ₁ < N
  · have h2 : idxValD wIdx δ₂ < N := hIdx ▸ h1
    simp only [toggleOneHotBits, h1, h2, ↓reduceDIte]
    have htEq : wOut ⟨idxValD wIdx δ₁, h1⟩ = wOut ⟨idxValD wIdx δ₂, h2⟩ :=
      congrArg wOut (Fin.ext hIdx)
    rw [← htEq]
    by_cases hwt : w = wOut ⟨idxValD wIdx δ₁, h1⟩
    · subst hwt
      rw [Function.update_self, Function.update_self, hS _ (hOutS _), hHas]
    · rw [Function.update_of_ne hwt, Function.update_of_ne hwt, hS w hw]
  · have h2 : ¬ idxValD wIdx δ₂ < N := hIdx ▸ h1
    simp only [toggleOneHotBits, h1, h2, ↓reduceDIte]
    exact hS w hw

theorem f_mid_nuc_al_fix {n : ℕ} (rn : RouterReg 47 6 n) (γ : BitAssignment n)
    {u : Fin (routerWidth 47 6)} (hu : u.val < 1244 ∨ (1350 ≤ u.val ∧ u.val < 1364)) :
    f_mid_nuc_al rn γ (rn u) = γ (rn u) := by
  have hbp : basePub 47 6 = 1238 := rfl
  dsimp only [f_mid_nuc_al]
  exact (flipLo0Bits_other zg47_hM0 rn _
    (rr_ne rn (by dsimp [rCtrlLo]; rw [hbp]; omega))).trans
    ((toggleOneHotBits_apply_other _
      (wOutLoN48_mem (S := fun v ↦ rn u ≠ v) rn
        (fun p ↦ rr_ne rn (by have := p.isLt; dsimp [rCtrlLo]; rw [hbp]; omega))
        (rr_ne rn (by dsimp; omega)))).trans
      (toggleOneHotBits_apply_other γ
        (wOutHiN48_mem (S := fun v ↦ rn u ≠ v) rn
          (fun p ↦ rr_ne rn (by have := p.isLt; dsimp [rCtrlHi]; rw [hbp]; omega))
          (rr_ne rn (by dsimp; omega)))))

theorem f_xi_nuc_al_fix {n : ℕ} (rn : RouterReg 47 6 n) (γ : BitAssignment n)
    {u : Fin (routerWidth 47 6)} (hu : u.val < 1238) :
    f_xi_nuc_al rn γ (rn u) = γ (rn u) := by
  have hbp : basePub 47 6 = 1238 := rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, zCL0, _, _⟩ :=
    planeOfRouter_rHas2Alias_roles rn 0
  dsimp only [f_xi_nuc_al, f_eta_nuc_al]
  exact (planeXorBits_other (planeOfRouter (rHas2Alias rn) 0) _
    (fun p e ↦ rr_ne rn (by have := p.isLt; dsimp [rCtrlLo]; rw [hbp]; omega)
      (e.trans (congrFun zCL0 p)))).trans
    ((fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg47_hD2 rn _
      (fun d ↦ rr_ne rn (by have := d.isLt; dsimp [rUMsb]; rw [hbp]; omega))).trans
      (f_mid_nuc_al_fix rn γ (Or.inl (by omega))))

/--
Buffer-invariance of `f_mid_nuc_al` and `f_xi_nuc_al` when two assignments agree outside `rBufLo`
/`rBufHi`.
-/
theorem f_mid_f_xi_nuc_al_congr_of_not_buf {n : ℕ} (rn : RouterReg 47 6 n)
    {β₁ β₂ : BitAssignment n}
    (hOth : ∀ w : Wire n, (∀ b : Fin 24, w ≠ rBufLo rn b ∧ w ≠ rBufHi rn b) → β₁ w = β₂ w) :
    (∀ (γ : BitAssignment n) (b : Fin 24),
      f_xi_nuc_al rn γ (rBufLo rn b) = γ (rBufLo rn b) ∧
      f_xi_nuc_al rn γ (rBufHi rn b) = γ (rBufHi rn b)) ∧
    (∀ w : Wire n, (∀ b : Fin 24, w ≠ rBufLo rn b ∧ w ≠ rBufHi rn b) →
      f_mid_nuc_al rn β₁ w = f_mid_nuc_al rn β₂ w ∧
      f_xi_nuc_al rn β₁ w = f_xi_nuc_al rn β₂ w) := by
  let pr0 := planeOfRouter (rHas2Alias rn) 0
  let NB (w : Wire n) : Prop := ∀ b : Fin 24, w ≠ rBufLo rn b ∧ w ≠ rBufHi rn b
  have hNB {u : Fin (routerWidth 47 6)} (hu : u.val < 14 ∨ 62 ≤ u.val) : NB (rn u) := fun b ↦ by
    refine ⟨rr_ne rn ?_, rr_ne rn ?_⟩
    all_goals
      dsimp [rBufLo, rBufHi]
      omega
  have hXiBuf (γ : BitAssignment n) (b : Fin 24) :
      f_xi_nuc_al rn γ (rBufLo rn b) = γ (rBufLo rn b) ∧
      f_xi_nuc_al rn γ (rBufHi rn b) = γ (rBufHi rn b) := by
    refine ⟨f_xi_nuc_al_fix rn γ ?_, f_xi_nuc_al_fix rn γ ?_⟩
    all_goals
      dsimp [rBufLo, rBufHi]
      omega
  have hHiCongr : ∀ w, NB w →
      toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) β₁ w =
      toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) β₂ w :=
    toggleOneHotBits_congr_on _ _ _ hOth
      (rRawHas2_47_eq_r1 rn ▸ hOth _ (hNB (Or.inl (by decide))))
      (idxValD_congr (rIdx2 rn) fun d ↦ hOth _ (hNB (Or.inl (by
        dsimp [rIdx2]
        omega))))
      (wOutHiN48_mem (S := NB) rn
        (fun p ↦ hNB (Or.inr (by
          dsimp [rCtrlHi, basePub]
          omega)))
        (hNB (Or.inr (by
          dsimp
          omega))))
  have hLoCongr : ∀ w, NB w →
      toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn)
        (toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) β₁) w =
      toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn)
        (toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) β₂) w :=
    toggleOneHotBits_congr_on _ _ _ hHiCongr
      (hHiCongr _ (hNB (Or.inl (by decide))))
      (idxValD_congr (rIdx1 rn) fun d ↦ hHiCongr _ (hNB (Or.inl (by
        dsimp [rIdx1]
        omega))))
      (wOutLoN48_mem (S := NB) rn
        (fun p ↦ hNB (Or.inr (by
          dsimp [rCtrlLo, basePub]
          omega)))
        (hNB (Or.inr (by
          dsimp
          omega))))
  have hMidCongr (w : Wire n) (hw : NB w) : f_mid_nuc_al rn β₁ w = f_mid_nuc_al rn β₂ w := by
    dsimp only [f_mid_nuc_al, flipLo0Bits]
    by_cases hw0 : w = rCtrlLo rn ⟨0, zg47_hM0⟩
    · subst hw0
      rw [Function.update_self, Function.update_self, hLoCongr _ hw,
          hLoCongr (rHas1 rn) (hNB (Or.inl (by decide)))]
    · rw [Function.update_of_ne hw0, Function.update_of_ne hw0, hLoCongr _ hw]
  have hSuppHdr1 :
      ProgSupportedIn (UMsbHdrSet rn) (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn)) :=
    progSupportedIn_mono (fun _ h ↦ h.1)
      (progSupportedIn_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG zg47_hD2 rn)
        (progSupportedIn_pUMsbHdrZG zg47_hD2 rn))
  have hEtaCongr (w : Wire n) (hw : NB w) : f_eta_nuc_al rn β₁ w = f_eta_nuc_al rn β₂ w := by
    by_cases hwU : ∃ d : Fin 6, w = rUMsb rn d
    · obtain ⟨d, rfl⟩ := hwU
      refine Stage2ZeroGated.fwdBits_congr_on_supp _ hSuppHdr1 (fun v' hv ↦ ?_) _
        (Or.inr ⟨d, rfl⟩)
      rcases hv with ⟨u, hu, rfl⟩ | ⟨d', rfl⟩
      · exact hMidCongr _ (hNB (Or.inl (by omega)))
      · exact hMidCongr _ (hNB (Or.inr (by
          dsimp [rUMsb, basePub]
          omega)))
    · dsimp only [f_eta_nuc_al]
      rw [fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg47_hD2 rn _ fun d e ↦ hwU ⟨d, e⟩,
          fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg47_hD2 rn _ fun d e ↦ hwU ⟨d, e⟩,
          hMidCongr w hw]
  refine ⟨hXiBuf, fun w hw ↦ ⟨hMidCongr w hw, ?_⟩⟩
  dsimp only [f_xi_nuc_al]
  by_cases hwL : ∃ p : Fin 47, w = pCtrlLo pr0 p
  · obtain ⟨p, rfl⟩ := hwL
    have zCH0 := (planeOfRouter_rHas2Alias_roles rn 0).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [planeXorBits_ctrlLo, planeXorBits_ctrlLo, hEtaCongr _ hw,
        hEtaCongr (pCtrlHi pr0 p) (congrFun zCH0 p ▸ hNB (Or.inr (by
          dsimp [rCtrlHi, basePub]
          omega)))]
  · rw [planeXorBits_other pr0 _ fun p e ↦ hwL ⟨p, e⟩,
        planeXorBits_other pr0 _ fun p e ↦ hwL ⟨p, e⟩, hEtaCongr w hw]

/--
Operator bridge unwrapping `UX0` , `F_hdr1` , and `F_flip` around
`uDirectGatherPlanesAfterXor 24 (prOnlineNuc rn)` .
-/
theorem uDirectGatherPlanesAfterXor_prOnlineNuc_eq {n : ℕ}
    (rn : RouterReg 47 6 n) (R₀ : Operator (2 ^ n))
    (hR₀ : SupportedOn (ValidZeroGatedSortedRouterInput rn) R₀) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    let U_mid : Unitary (2 ^ n) := (cFlipLo0 zg47_hM0 rn).eval * (ULo * UHi)
    let U_prep : Unitary (2 ^ n) :=
      (fwdCirc (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn))).eval * U_mid
    let UX0 := uPlaneXorCtrl (planeOfRouter (rHas2Alias rn) 0)
    (uDirectGatherPlanesAfterXor 24 (prOnlineNuc rn)).1 * (UX0.1 * (U_prep.1 * R₀)) =
      UX0.1 * (U_prep.1 * (uCopyLoHiAlwaysLoMat rn * ((uRouterSwapAlwaysLoConj rn).1 * R₀))) := by
  intro dLo dHi ULo UHi U_mid U_prep UX0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, zCL0, zCH0, _⟩ :=
    planeOfRouter_rHas2Alias_roles rn 0
  simp only [← Matrix.mul_assoc]
  refine hR₀ _ _ fun β hβ ↦ ?_
  obtain ⟨hηLo, hηHi, _⟩ := ketProps_pNucCoreMidAlwaysLo rn β hβ
  obtain ⟨pMin, hcL1, hcL0, hHiCases⟩ := oneHot_ctrlLoHi_of_validZeroGated_nuc rn β hβ
  obtain ⟨ξ', heUG, hξ'Lo, hξ'Hi, hξ'Oth⟩ :=
    uDirectGatherPlanesAfterXor_ket_eval 24 (prOnlineNuc rn) (hDisjEval_prOnlineNuc rn)
      (f_xi_nuc_al rn β)
  obtain ⟨β_out, heCS, hβOutLo, hβOutHi, hβOutOth⟩ :=
    copyLoHi_mul_routerSwap_ket_eq_of_oneHot rn β
      (fun b ↦ (hβ.1.2.2.2.1 b).1) (fun b ↦ (hβ.1.2.2.2.1 b).2.1) pMin hcL1 hcL0 hHiCases
  rw [← Matrix.mulVec_mulVec] at heCS
  obtain ⟨hXiBuf, hCongrOut⟩ := f_mid_f_xi_nuc_al_congr_of_not_buf rn hβOutOth
  rw [show PhotochemistrySolution.SplitRouterSeqBell26k.ket β = ket β from rfl,
      Matrix.mul_assoc _ UX0.1 U_prep.1, ← Matrix.mulVec_mulVec,
      uPlaneXorCtrl_uPrep_nuc_mulVec_ket rn β, heUG,
      ← Matrix.mulVec_mulVec (ket β), ← Matrix.mulVec_mulVec _ (UX0.1 * U_prep.1),
      heCS, uPlaneXorCtrl_uPrep_nuc_mulVec_ket rn β_out]
  have hξLo (p : Fin 47) :
      f_xi_nuc_al rn β (rCtrlLo rn p) = cLoAlways rn β p + routerCtrlHi rn β p := by
    dsimp only [f_xi_nuc_al]
    rw [← congrFun zCL0 p, planeXorBits_ctrlLo, congrFun zCL0 p, congrFun zCH0 p, hηLo p, hηHi p]
  have hξHi (p : Fin 47) : f_xi_nuc_al rn β (rCtrlHi rn p) = routerCtrlHi rn β p := by
    dsimp only [f_xi_nuc_al]
    rw [planeXorBits_other _ _ (fun p' e ↦ rr_ne rn
      (by have := p.isLt
          have := p'.isLt
          dsimp [rCtrlHi, rCtrlLo, basePub]
          omega)
      (e.trans (congrFun zCL0 p'))), hηHi p]
  have hξSys (p : Fin 47) (b : Fin 24) : f_xi_nuc_al rn β (rSys rn p b) = β (rSys rn p b) :=
    f_xi_nuc_al_fix rn β (by
      have := p.isLt
      have := b.isLt
      dsimp [rSys]
      omega)
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hwLo : ∃ b : Fin 24, w = rBufLo rn b
  · obtain ⟨b, rfl⟩ := hwLo
    obtain ⟨_, _, bBL, _, _, _, _, _, _, _, _, _, bCL, bCH, bSy⟩ := prOnlineNuc_roles rn b
    rw [← bBL, hξ'Lo b, (validZ8MuxD1GatherPlaneIn_prOnlineNuc_ket rn β hβ b).2.2.1, zero_add,
        bBL, (hXiBuf β_out b).1, hβOutLo b]
    exact congrArg (fun f ↦ directPrefixSum f 47 le_rfl) (funext fun p ↦ by
      rw [congrFun bCL p, congrFun bCH p, bSy p, hξLo p, hξHi p, z2_add_self_cancel, hξSys p b])
  · by_cases hwHi : ∃ b : Fin 24, w = rBufHi rn b
    · obtain ⟨b, rfl⟩ := hwHi
      obtain ⟨_, _, _, bBH, _, _, _, _, _, _, _, _, _, bCH, bSy⟩ := prOnlineNuc_roles rn b
      rw [← bBH, hξ'Hi b, (validZ8MuxD1GatherPlaneIn_prOnlineNuc_ket rn β hβ b).2.2.2.1, zero_add,
          bBH, (hXiBuf β_out b).2, hβOutHi b]
      exact congrArg (fun f ↦ directPrefixSum f 47 le_rfl) (funext fun p ↦ by
        rw [congrFun bCH p, bSy p, hξHi p, hξSys p b])
    · have hwNotBuf (b : Fin 24) : w ≠ rBufLo rn b ∧ w ≠ rBufHi rn b :=
        ⟨fun e ↦ hwLo ⟨b, e⟩, fun e ↦ hwHi ⟨b, e⟩⟩
      rw [hξ'Oth w fun b ↦
            ⟨(prOnlineNuc_roles rn b).2.2.1.symm ▸ (hwNotBuf b).1,
             (prOnlineNuc_roles rn b).2.2.2.1.symm ▸ (hwNotBuf b).2⟩,
          (hCongrOut w hwNotBuf).2.symm]

/--
Clean-projection invariance (`hCleanIn` and `hCleanOut` ) on `sCleanHdr (6 - 2) rn` around `U_mid` .
-/
theorem cleanProj_sCleanHdr_nuc_in_out {n : ℕ}
    (rn : RouterReg 47 6 n) (R₀ : Operator (2 ^ n))
    (hR₀ : SupportedOn (ValidZeroGatedSortedRouterInput rn) R₀) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    let U_mid : Unitary (2 ^ n) := (cFlipLo0 zg47_hM0 rn).eval * (ULo * UHi)
    let R₀' := uCopyLoHiAlwaysLoMat rn * ((uRouterSwapAlwaysLoConj rn).1 * R₀)
    cleanProj (sCleanHdr (6 - 2) rn) * (U_mid.1 * R₀) = U_mid.1 * R₀ ∧
    cleanProj (sCleanHdr (6 - 2) rn) * (U_mid.1 * R₀') = U_mid.1 * R₀' := by
  intro dLo dHi ULo UHi U_mid R₀'
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
  have hMidKet (γ : BitAssignment n) : U_mid.1.mulVec (ket γ) = ket (f_mid_nuc_al rn γ) := by
    dsimp only [U_mid, f_mid_nuc_al]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket, cFlipLo0_mulVec_ket]
  have hMid0 (β : BitAssignment n) (hβ : ValidZeroGatedSortedRouterInput rn β)
      (w : Wire n) (hw : w ∈ sCleanHdr (6 - 2) rn) : f_mid_nuc_al rn β w = 0 := by
    rcases Finset.mem_image.mp hw with ⟨d, _, rfl⟩
    exact (f_mid_nuc_al_fix rn β (Or.inr (by
        dsimp [rUMsb, basePub]
        omega))).trans
      (hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff rn _).mpr (by
        dsimp [rUMsb]
        omega)))
  constructor
  · simp only [← Matrix.mul_assoc]
    refine hR₀ (cleanProj (sCleanHdr (6 - 2) rn) * U_mid.1) U_mid.1 fun β hβ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ket_sr, hMidKet β, cleanProj_mulVec_ket,
        _root_.ite_eq_left (hMid0 β hβ)]
  · dsimp only [R₀']
    simp only [← Matrix.mul_assoc]
    refine hR₀ _ _ fun β hβ ↦ ?_
    obtain ⟨pMin, hcL1, hcL0, hHiCases⟩ := oneHot_ctrlLoHi_of_validZeroGated_nuc rn β hβ
    obtain ⟨β_out, heCS, _, _, hβOutOth⟩ := copyLoHi_mul_routerSwap_ket_eq_of_oneHot rn β
      (fun b ↦ (hβ.1.2.2.2.1 b).1) (fun b ↦ (hβ.1.2.2.2.1 b).2.1) pMin hcL1 hcL0 hHiCases
    rw [← Matrix.mulVec_mulVec] at heCS
    obtain ⟨_, hCongrOut⟩ := f_mid_f_xi_nuc_al_congr_of_not_buf rn hβOutOth
    have hMidOut0 (w : Wire n) (hw : w ∈ sCleanHdr (6 - 2) rn) :
        f_mid_nuc_al rn β_out w = 0 := by
      rcases Finset.mem_image.mp hw with ⟨d, _, rfl⟩
      refine ((hCongrOut (rUMsb rn d) fun b ↦ ⟨rr_ne rn ?_, rr_ne rn ?_⟩).1).trans
        (hMid0 β hβ _ hw)
      all_goals
        dsimp [rUMsb, rBufLo, rBufHi, basePub]
        omega
    simp only [ket_sr, ← Matrix.mulVec_mulVec]
    rw [heCS, hMidKet β_out, cleanProj_mulVec_ket, _root_.ite_eq_left hMidOut0]

section IrredNucHdrXorGather
attribute [local irreducible]
  pUMsbHdrZG uOneHotToggle fwdCirc wrapDyn cFlipLo0
  uPlaneXorCtrl cleanProj uRouterSwapAlwaysLoConj
  uCopyLoHiAlwaysLoMat uDirectGatherPlanesAfterXor pXorCtrlHiToLo
/--
Complete `SubspaceStep` for `wrapDyn pHdr1 (wrapDyn pXorCtrlHiToLo pGatherPlanes)` on
`ValidZeroGatedSortedRouterInput rn`, parameterized by `pGatherPlanes`.
-/
theorem subspaceStep_nucHdrXorGather_of_validZeroGated
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rn : RouterReg 47 6 n) (pGatherPlanes : DynamicCircuit Var n)
    (hGather : ∀ X : Operator (2 ^ n),
      SupportedOn (fun ξ ↦ ∀ b : Fin 24, ValidZ8MuxD1GatherPlaneIn (prOnlineNuc rn b) ξ) X →
      SubspaceStep (Var := Var) X ((uDirectGatherPlanesAfterXor 24 (prOnlineNuc rn)).1 * X)
        pGatherPlanes)
    (R₀ : Operator (2 ^ n)) (hR₀ : SupportedOn (ValidZeroGatedSortedRouterInput rn) R₀) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    let U_mid : Unitary (2 ^ n) := (cFlipLo0 zg47_hM0 rn).eval * (ULo * UHi)
    SubspaceStep (Var := Var)
      (U_mid.1 * R₀)
      (U_mid.1 * (uCopyLoHiAlwaysLoMat rn * ((uRouterSwapAlwaysLoConj rn).1 * R₀)))
      (wrapDyn v (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn))
        (wrapDyn v (pXorCtrlHiToLo rn) pGatherPlanes)) := by
  intro dLo dHi ULo UHi U_mid
  let pHdr1 := constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn)
  let F_hdr1 := (fwdCirc pHdr1).eval
  let U_prep : Unitary (2 ^ n) := F_hdr1 * U_mid
  let R₀' := uCopyLoHiAlwaysLoMat rn * ((uRouterSwapAlwaysLoConj rn).1 * R₀)
  have sPl := subspaceStep_congr_out
    (hGather _ (supportedOn_validZ8MuxD1GatherPlaneIn_prOnlineNuc rn R₀ hR₀))
    (uDirectGatherPlanesAfterXor_prOnlineNuc_eq rn R₀ hR₀)
  have sXor := subspaceStep_congr_in (Matrix.mul_assoc F_hdr1.1 U_mid.1 R₀).symm
    (subspaceStep_congr_out
      (subspaceStep_wrap_pXorCtrlHiToLo v rn pGatherPlanes (U_prep.1 * R₀) (U_prep.1 * R₀') sPl)
      (Matrix.mul_assoc F_hdr1.1 U_mid.1 R₀'))
  obtain ⟨hCleanIn, hCleanOut⟩ := cleanProj_sCleanHdr_nuc_in_out rn R₀ hR₀
  exact subspaceStep_wrapDyn v pHdr1 (sCleanHdr (6 - 2) rn) _ _ _
    (validProg_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG zg47_hD2 rn)
      (rHas1_not_mem_sCleanHdr (6 - 2) rn) (validProg_pUMsbHdrZG zg47_hD2 rn))
    hCleanIn hCleanOut sXor
end IrredNucHdrXorGather

/-- `U_mid` acts independently of `AllPlaneMod rn` (and in particular every `rHA rn b`). -/
theorem actsIndepOf_allPlaneMod_uMid_nuc {n : ℕ} (rn : RouterReg 47 6 n) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    ActsIndepOf (AllPlaneMod rn) (ULo * UHi) ∧
    ActsIndepOf (AllPlaneMod rn) ((cFlipLo0 zg47_hM0 rn).eval * (ULo * UHi)) ∧
    (∀ b : Fin 24, ActsIndepOf (· = rHA rn b) ((cFlipLo0 zg47_hM0 rn).eval * (ULo * UHi))) := by
  intro dLo dHi ULo UHi
  have ⟨hIndLo, hIndHi⟩ :
      ActsIndepOf (AllPlaneMod rn) ULo ∧ ActsIndepOf (AllPlaneMod rn) UHi := by
    refine ⟨actsIndepOf_allPlaneMod_uOneHotToggle rn dLo.has_ne_out dLo.idx_ne_out
        (not_allPlaneMod_of_idx rn (Or.inl ?_)) (fun d ↦ not_allPlaneMod_of_idx rn (Or.inl ?_))
        (wOutLoN48_mem (S := fun v ↦ ¬ AllPlaneMod rn v) rn
          (fun p ↦ not_allPlaneMod_of_idx rn (Or.inr ?_))
          (not_allPlaneMod_of_idx rn (Or.inr ?_))),
      actsIndepOf_allPlaneMod_uOneHotToggle rn dHi.has_ne_out dHi.idx_ne_out
        (not_allPlaneMod_of_idx rn (Or.inl ?_)) (fun d ↦ not_allPlaneMod_of_idx rn (Or.inl ?_))
        (wOutHiN48_mem (S := fun v ↦ ¬ AllPlaneMod rn v) rn
          (fun p ↦ not_allPlaneMod_of_idx rn (Or.inr ?_))
          (not_allPlaneMod_of_idx rn (Or.inr ?_)))⟩
    all_goals
      dsimp [rHas1, rRawHas2, rIdx1, rIdx2, rCtrlLo, rCtrlHi, basePub, routerWidth]
      omega
  have hLoHi := actsIndepOf_mul_unitary hIndLo hIndHi
  have hMid := actsIndepOf_mul_unitary (actsIndepOf_allPlaneMod_cFlipLo0 zg47_hM0 rn) hLoHi
  obtain ⟨G, hk, hf⟩ := hMid
  exact ⟨hLoHi, ⟨G, hk, hf⟩,
    fun b ↦ ⟨G, hk, fun q hq ↦ hf q (hq ▸ ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩)⟩⟩

/--
Commutation of any `AllPlaneMod rn` -supported `{H, CNOT}` circuit (such as
`cFixupBellLoFromGatherCirc rn` )
past `ULo * UHi`.
-/
theorem comm_allPlaneMod_circ_uLoHi_nuc {n : ℕ} (rn : RouterReg 47 6 n)
    (c : Circuit n) (hc : HCNOTSupportedIn (AllPlaneMod rn) c) (X : Operator (2 ^ n)) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    c.eval.1 * (ULo.1 * (UHi.1 * X)) = ULo.1 * (UHi.1 * (c.eval.1 * X)) := by
  intro dLo dHi ULo UHi
  have cComm : c.eval.1 * (ULo.1 * UHi.1) = (ULo.1 * UHi.1) * c.eval.1 :=
    hc.toCircSupportedIn (ULo * UHi) (actsIndepOf_allPlaneMod_uMid_nuc rn).1
  calc c.eval.1 * (ULo.1 * (UHi.1 * X))
      = (c.eval.1 * (ULo.1 * UHi.1)) * X := by
          rw [← Matrix.mul_assoc ULo.1 UHi.1 X, ← Matrix.mul_assoc c.eval.1 (ULo.1 * UHi.1) X]
    _ = ((ULo.1 * UHi.1) * c.eval.1) * X := by rw [cComm]
    _ = ULo.1 * (UHi.1 * (c.eval.1 * X)) := by
          rw [Matrix.mul_assoc (ULo.1 * UHi.1) c.eval.1 X, Matrix.mul_assoc ULo.1 UHi.1 (c.eval.1 *
              X)]

/--
`4,864-T` (`0 .TOFF`) genuine-`BellLo` nuclear router core (`2,256-T` `OneHotScatter` +
`16-T` `pUMsbHdrZG` + `2,592-T` `Z_8` `MuxD1` gather + `48`-CNOT fixup, `0` `rHB[1..23]` wires).
-/
def pNucCoreMidBellZ8W294 {Var : Type} {n : ℕ} (v : Var) (rn : RouterReg 47 6 n) :
    DynamicCircuit Var n :=
  .seq (.circuit (cFlipLo0 zg47_hM0 rn))
    (.seq (pPlanesOneHotScatterLoLoop zg47_hM0 v rn 24 le_rfl)
      (.seq (wrapDyn v (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn))
              (wrapDyn v (pXorCtrlHiToLo rn)
                (pZ8MuxD1GatherPlanesDyn v 24 (prOnlineNuc rn))))
        (.seq (.circuit (cFlipLo0 zg47_hM0 rn))
          (.circuit (cFixupBellLoFromGatherCirc rn)))))

theorem count_pNucCoreMidBellZ8W294 {Var : Type} {n : ℕ} (v : Var) (rn : RouterReg 47 6 n) :
    (pNucCoreMidBellZ8W294 v rn).count .T = 4864 ∧
    (pNucCoreMidBellZ8W294 v rn).count .TOFF = 0 := by
  let pHdr1 := constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn)
  let bPl := pZ8MuxD1GatherPlanesDyn (Var := Var) v 24 (prOnlineNuc rn)
  let bXor := wrapDyn v (pXorCtrlHiToLo rn) bPl
  obtain ⟨tSc, fSc⟩ := count_pPlanesOneHotScatterLoLoop (Var := Var) zg47_hM0 v rn 24 le_rfl
  obtain ⟨tHdr, fHdr⟩ := count_wrapDyn v pHdr1 bXor
  obtain ⟨tXor, fXor⟩ := count_wrapDyn v (pXorCtrlHiToLo rn) bPl
  obtain ⟨tPl, fPl⟩ := count_pZ8MuxD1GatherPlanesDyn (Var := Var) v (by decide) 24 (prOnlineNuc rn)
  obtain ⟨tFx, fFx⟩ := count_cFixupBellLoFromGatherCirc rn
  unfold pNucCoreMidBellZ8W294
  dsimp only [DynamicCircuit.count]
  rw [count_cFlipLo0_T zg47_hM0 rn, count_cFlipLo0_TOFF zg47_hM0 rn, tSc, fSc, tFx, fFx,
      tHdr, fHdr, numAnd_constOneProg, numAnd_pUMsbHdrZG zg47_hD2 rn,
      tXor, fXor, numAnd_pXorCtrlHiToLo rn, tPl, fPl]
  exact ⟨by omega, rfl⟩

theorem dynWires_pNucCoreMidBellZ8W294_w294 {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (r : RouterReg 47 6 n) (hS : ∀ w, UsedNucOnlineW294 r w → S w) :
    DynWires S (pNucCoreMidBellZ8W294 v (rNucW340 r)) := by
  let rn := rNucW340 r
  have hU {u : Fin (routerWidth 47 6)}
      (hu : u.val < 87 ∨ (110 ≤ u.val ∧ u.val < basePub 47 6) ∨
       (1244 ≤ u.val ∧ u.val < 1350) ∨ (1351 ≤ u.val ∧ u.val < 1357) ∨
       (1364 ≤ u.val ∧ u.val < 1367) ∨ (1381 ≤ u.val ∧ u.val < 1394)) : S (rn u) :=
    hS _ (rNucW340_in_usedNucOnlineW294 r hu)
  have ⟨hH1, hCLo, hCHi, hSys, hHA, hHB0, hBufLo, hUM⟩ :
      S (rHas1 rn) ∧ (∀ p, S (rCtrlLo rn p)) ∧ (∀ p, S (rCtrlHi rn p)) ∧
      (∀ b p, S (rSys rn p b)) ∧ (∀ b, S (rHA rn b)) ∧ S (rHB rn ⟨0, by decide⟩) ∧
      (∀ b, S (rBufLo rn b)) ∧ (∀ d, S (rUMsb rn d)) := by
    refine ⟨hU (Or.inl ?_), fun p ↦ hU (Or.inr (Or.inr (Or.inl ?_))),
      fun p ↦ hU (Or.inr (Or.inr (Or.inl ?_))), fun b p ↦ hU (Or.inr (Or.inl ?_)),
      fun b ↦ hU (Or.inl ?_), hU (Or.inl ?_), fun b ↦ hU (Or.inl ?_),
      fun d ↦ hU (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
    all_goals
      dsimp [rHas1, rCtrlLo, rCtrlHi, rSys, rHA, rHB, rBufLo, rUMsb, basePub]
      omega
  have hFl := cw_cFlipLo0 zg47_hM0 rn hH1 (hCLo _)
  have hHdr : ProgSupportedIn S (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn)) :=
    progSupportedIn_mono
      (fun _ hw ↦ hw.1.elim (fun ⟨_, hu, eq⟩ ↦ eq ▸ hU (Or.inl (by omega)))
        fun ⟨d, eq⟩ ↦ eq ▸ hUM d)
      (progSupportedIn_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG zg47_hD2 rn)
        (progSupportedIn_pUMsbHdrZG zg47_hD2 rn))
  have hz := prOnlineNuc_z8_roles_usedNucOnlineW294 r hS
  exact ⟨hFl, dynWires_pPlanesOneHotScatterLoLoop zg47_hM0 v rn hCLo hSys hHA hHB0 24 le_rfl,
    dynWires_wrapDyn v _ _ (computeProgWires_of_supp hHdr)
      (dynWires_wrapDyn v (pXorCtrlHiToLo rn) _
        (computeProgWires_of_supp (progSupportedIn_pXorCtrlHiToLo rn hCLo hCHi))
        (dynWires_pZ8MuxD1GatherPlanesDyn v 24 (prOnlineNuc rn)
          (fun b ↦ (hz b).1) (fun b ↦ (hz b).2.1) (fun b ↦ (hz b).2.2.1) (fun b ↦ (hz b).2.2.2.1)
          (fun b ↦ (hz b).2.2.2.2.1) (fun b ↦ (hz b).2.2.2.2.2.1)
          (fun b ↦ (hz b).2.2.2.2.2.2.1) (fun b ↦ (hz b).2.2.2.2.2.2.2))),
    hFl, cw_cFixupBellLoFromGatherCirc rn hHA hBufLo⟩

section IrredNucCoreMidBellZ8
attribute [local irreducible]
  pUMsbHdrZG uOneHotToggle fwdCirc wrapDyn cFlipLo0
  uCopyLoHiAlwaysLoMat uRouterSwapAlwaysLoConj
  uBellLoPreScatter uBellLoCopyHiAlwaysLoConj
  pZ8MuxD1GatherPlanesDyn pPlanesOneHotScatterLoLoop
  cFixupBellLoFromGatherCirc pXorCtrlHiToLo
theorem subspaceStep_pNucCoreMidBellZ8W294 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rn : RouterReg 47 6 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput rn) R) :
    let dLo := wRouterDisj_loN48 rn
    let dHi := wRouterDisj_hiN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    let UHi := uOneHotToggle (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) dHi.has_ne_out dHi.idx_ne_out
    SubspaceStep (Var := Var)
      (ULo.1 * (UHi.1 * R))
      (ULo.1 * (UHi.1 * ((uBellLoCopyHiAlwaysLoConj rn).1 * ((uRouterSwapAlwaysLoConj rn).1 * R))))
      (pNucCoreMidBellZ8W294 v rn) := by
  intro dLo dHi ULo UHi
  let F_flip := (cFlipLo0 zg47_hM0 rn).eval
  let U_mid : Unitary (2 ^ n) := F_flip * (ULo * UHi)
  let X := (uBellLoPreScatter rn).1 * R
  let X_out := uCopyLoHiAlwaysLoMat rn * ((uRouterSwapAlwaysLoConj rn).1 * X)
  let pGatherWrap := wrapDyn v (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn))
    (wrapDyn v (pXorCtrlHiToLo rn) (pZ8MuxD1GatherPlanesDyn v 24 (prOnlineNuc rn)))
  have hMidAssoc (Y : Operator (2 ^ n)) : F_flip.1 * (ULo.1 * (UHi.1 * Y)) = U_mid.1 * Y := by
    simp only [U_mid, Submonoid.coe_mul, Matrix.mul_assoc]
  let U_out : Unitary (2 ^ n) := U_mid * (uCopyLoHiAlwaysLoConj rn * uRouterSwapAlwaysLoConj rn)
  have hUoutEq (Y : Operator (2 ^ n)) :
      U_out.1 * Y =
        U_mid.1 * (uCopyLoHiAlwaysLoMat rn * ((uRouterSwapAlwaysLoConj rn).1 * Y)) := by
    simp only [U_out, U_mid, Submonoid.coe_mul, uCopyLoHiAlwaysLoConj_val, Matrix.mul_assoc]
  have hpDisjHA (b' : Fin 24) : DynWires (· ≠ rHA rn b') pGatherWrap := by
    obtain ⟨hHdrHA, hXorHA⟩ := hdr_and_xor_progSupportedIn_ne_rHA rn b'
    have hz (b : Fin 24) := prOnlineNuc_z8_roles_ne_rHA rn b b'
    exact dynWires_wrapDyn v _ _ (computeProgWires_of_supp hHdrHA)
      (dynWires_wrapDyn v (pXorCtrlHiToLo rn) _ (computeProgWires_of_supp hXorHA)
        (dynWires_pZ8MuxD1GatherPlanesDyn v 24 (prOnlineNuc rn)
          (fun b ↦ (hz b).1) (fun b ↦ (hz b).2.1) (fun b ↦ (hz b).2.2.1)
          (fun b ↦ (hz b).2.2.2.1) (fun b ↦ (hz b).2.2.2.2.1) (fun b ↦ (hz b).2.2.2.2.2.1)
          (fun b ↦ (hz b).2.2.2.2.2.2.1) (fun b ↦ (hz b).2.2.2.2.2.2.2)))
  have hIndHA := (actsIndepOf_allPlaneMod_uMid_nuc rn).2.2
  have sGather := subspaceStep_congr_out
    (subspaceStep_drop_zero_vec (rHA rn) (zgat_rHA_inj rn)
      (fun b β val hβ ↦ zgat_validZeroGatedWithoutHA_update_rHA rn b β val hβ)
      hIndHA (fun b ↦ zgat_actsIndepOf_mul (hIndHA b)
        (zgat_actsIndepOf_mul (zgat_actsIndepOf_rHA_uCopyLoHi rn b)
          (zgat_actsIndepOf_rHA_uRouterSwap rn b))) hpDisjHA
      (fun R₀ hR₀ ↦ subspaceStep_congr_out
        (subspaceStep_nucHdrXorGather_of_validZeroGated v rn _
          (fun Y hY ↦ subspaceStep_pZ8MuxD1GatherPlanesDyn v (by decide) (by decide) 24
            (prOnlineNuc rn) (hDisjPl_prOnlineNuc rn) Y hY) R₀
          fun A B hAB ↦ hR₀ A B fun γ hγ ↦
            hAB γ ((zgat_validZeroGatedWithoutHA_iff rn γ).mp hγ))
        (hUoutEq R₀).symm)
      X (supportedOn_validZeroGatedWithoutHA_uBellLoPreScatter rn R hR)) (hUoutEq X)
  exact (subspaceStep_congr_out (subspaceStep_of_circuit _ (cFlipLo0 zg47_hM0 rn))
      (hMidAssoc R)).seq
    ((subspaceStep_pPlanesOneHotScatterLoLoop_nuc zg47_hM0 v rn R hR).seq
      (sGather.seq
        ((subspaceStep_congr_out (subspaceStep_of_circuit _ (cFlipLo0 zg47_hM0 rn))
            (by rw [← hMidAssoc X_out, ← Matrix.mul_assoc F_flip.1 F_flip.1,
                    cFlipLo0_eval_sq_eq_one, Matrix.one_mul])).seq
          (subspaceStep_congr_out (subspaceStep_of_circuit _ (cFixupBellLoFromGatherCirc rn))
            (by rw [comm_allPlaneMod_circ_uLoHi_nuc rn _
                      (hcnotSupportedIn_cFixupBellLoFromGatherCirc rn) X_out,
                    cFixupBellLoFromGatherCirc_mul_eq zg47_hM0 rn R hR])))))
end IrredNucCoreMidBellZ8

attribute [irreducible] pNucCoreMidBellZ8W294
end NucBellZ8Core

section IrredNucInnerHiWrap
attribute [local irreducible]
  uOneHotToggle uRouterSwapAlwaysLoConj uBellLoCopyHiAlwaysLoConj
theorem subspaceStep_pNucInnerHiWrapOnlineHB {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rn : RouterReg 47 6 n)
    (R : Operator (2 ^ n)) (hRn : SupportedOn (ValidZeroGatedSortedRouterInput rn) R) :
    let dLo := wRouterDisj_loN48 rn;
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out;
    let R_sw := (uRouterSwapAlwaysLoConj rn).1 * R
    SubspaceStep (Var := Var)
      (ULo.1 * R)
      (ULo.1 * ((uBellLoCopyHiAlwaysLoConj rn).1 * R_sw))
      (wrapWRouterHi47 v (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) (qEncNuc rn)
        (pNucCoreMidBellZ8W294 v rn)) := by
  intro dLo ULo R_sw
  let dHi := wRouterDisj_hiN48 rn
  have hDisjLoHi := hne_wOutLoN48_wOutHiN48 rn
  have hLoOth (β : BitAssignment n) {w : Wire n} (h : ∀ j : Fin 48, w ≠ wOutLoN48 rn j) :
      toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) β w = β w :=
    toggleOneHotBits_apply_other β h
  have ⟨hNeI2, hNeH2⟩ :
      (∀ d j, rIdx2 rn d ≠ wOutLoN48 rn j) ∧ (∀ j, rRawHas2 rn ≠ wOutLoN48 rn j) := by
    refine ⟨fun d ↦ wOutLoN48_mem (S := fun v ↦ rIdx2 rn d ≠ v) rn (fun p ↦ rr_ne rn ?_)
        (rr_ne rn ?_),
      wOutLoN48_mem (S := fun v ↦ rRawHas2 rn ≠ v) rn (fun p ↦ rr_ne rn ?_) (rr_ne rn ?_)⟩
    all_goals
      dsimp [rIdx2, rRawHas2, rCtrlLo, basePub, routerWidth]
      omega
  have hLoIdx2 (β : BitAssignment n) :=
    idxValD_congr (rIdx2 rn) fun d ↦ hLoOth β (hNeI2 d)
  have hLoHas2 (β : BitAssignment n) := hLoOth β hNeH2
  have hHiIn : SupportedOn
      (ValidWRouterInHi47 (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) (qEncNuc rn)) (ULo.1 * R) :=
    supportedOn_uOneHotToggle _ _ _ dLo.has_ne_out dLo.idx_ne_out
      (fun β hβ ↦ ⟨fun j ↦ (hLoOth β fun i ↦ (hDisjLoHi i j).symm).trans (hβ.1 j),
        (hLoOth β fun j ↦ (dLo.out_ne_q j).symm).trans hβ.2.1, hLoIdx2 β ▸ hβ.2.2.1,
        fun h0 ↦ hLoIdx2 β ▸ hβ.2.2.2.1 ((hLoHas2 β).symm.trans h0),
        fun h1 ↦ hLoIdx2 β ▸ hβ.2.2.2.2 ((hLoHas2 β).symm.trans h1)⟩)
      (fun A B hAB ↦ hRn A B fun β hβ ↦ hAB β (validWRouterBase_nuc8886 rn hβ).1)
  have hHiOut : SupportedOn (ValidWRouterCleanHi47 (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn))
      (ULo.1 * ((uBellLoCopyHiAlwaysLoConj rn).1 * R_sw)) :=
    supportedOn_uOneHotToggle _ _ _ dLo.has_ne_out dLo.idx_ne_out
      (fun β hβ ↦ ⟨fun j ↦ (hLoOth β fun i ↦ (hDisjLoHi i j).symm).trans (hβ.1 j),
        hLoIdx2 β ▸ hβ.2.1, fun h0 ↦ hLoIdx2 β ▸ hβ.2.2.1 ((hLoHas2 β).symm.trans h0),
        fun h1 ↦ hLoIdx2 β ▸ hβ.2.2.2 ((hLoHas2 β).symm.trans h1)⟩)
      (supportedOn_uBellLoCopyHiAlwaysLoConj_of_not_mod rn (validWRouterCleanHi47_hiN48_inv rn)
        R_sw (supportedOn_uRouterSwapAlwaysLoConj_of_not_mod rn
          (validWRouterCleanHi47_hiN48_inv rn) R hRn
          fun β hβ ↦ (validWRouterBase_nuc8886 rn hβ).2.1))
  exact subspaceStep_wrapWRouterHi47 v (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) (qEncNuc rn)
    dHi _ (ULo.1 * R) (ULo.1 * ((uBellLoCopyHiAlwaysLoConj rn).1 * R_sw)) hHiIn hHiOut
    (subspaceStep_congr_in
      (by rw [← Matrix.mul_assoc, uLoToggle_comm_uHiToggle_nuc rn, Matrix.mul_assoc])
      (subspaceStep_congr_out (subspaceStep_pNucCoreMidBellZ8W294 (Var := Var) v rn R hRn)
        (by rw [← Matrix.mul_assoc ULo.1, ← uLoToggle_comm_uHiToggle_nuc rn,
                Matrix.mul_assoc])))
end IrredNucInnerHiWrap

/-! ## Part 2: Sequential Permutations `rPermNuc294` & `rPermKin294` (`294 ≤ wWork`) -/

def permNuc294Val (x : ℕ) : ℕ :=
    if x = 6014 then 5828 else if x = 5828 then 6014 else if 6019 ≤ x ∧ x < 6041 then x -
    190 else if 5829 ≤ x ∧ x < 5851 then x + 190 else if 6041 ≤ x ∧ x < 6055 then x -
    118 else if 5923 ≤ x ∧ x < 5937 then x + 118 else x
theorem permNuc294Val_invol (x : ℕ) : permNuc294Val (permNuc294Val x) = x := by
  conv_lhs => arg 1; unfold permNuc294Val
  split_ifs <;> (unfold permNuc294Val; split_ifs <;> omega)

theorem permNuc294Val_lt (w : Wire dLayout) : permNuc294Val w.val < dLayout := by
  have hw : w.val < 7298 := hDLayout_eq_7298_w322 ▸ w.isLt;
  have hd : dLayout = 7298 := hDLayout_eq_7298_w322
  unfold permNuc294Val; split_ifs <;> omega

def rPermNuc294 : QRegister dLayout dLayout :=
  ⟨⟨fun w ↦ ⟨permNuc294Val w.val, permNuc294Val_lt w⟩, fun a b h ↦ Fin.ext (by
    have hv := congrArg Fin.val h; dsimp only at hv
    have h2 := congrArg permNuc294Val hv
    rwa [permNuc294Val_invol, permNuc294Val_invol] at h2)⟩⟩

theorem val_rPermNuc294 (w : Wire dLayout) : (rPermNuc294 w).val = permNuc294Val w.val := rfl

def permKin294Val (x : ℕ) : ℕ :=
    if 6020 ≤ x ∧ x < 6044 then x - 97 else if 5923 ≤ x ∧ x < 5947 then x + 97 else if 6044 ≤ x ∧
    x < 6051 then x - 54 else if 5990 ≤ x ∧ x < 5997 then x + 54 else if x =
    6051 then 5998 else if x = 5998 then 6051 else if 6052 ≤ x ∧ x < 6055 then x - 52 else if 6000 ≤
    x ∧ x < 6003 then x + 52 else x
set_option maxHeartbeats 4000000 in
-- 294-wire kinetic permutation involution
theorem permKin294Val_invol (x : ℕ) : permKin294Val (permKin294Val x) = x := by
  conv_lhs => arg 1; unfold permKin294Val
  split_ifs <;> (unfold permKin294Val; split_ifs <;> omega)

theorem permKin294Val_lt (w : Wire dLayout) : permKin294Val w.val < dLayout := by
  have hw : w.val < 7298 := hDLayout_eq_7298_w322 ▸ w.isLt;
  have hd : dLayout = 7298 := hDLayout_eq_7298_w322
  unfold permKin294Val; split_ifs <;> omega

def rPermKin294 : QRegister dLayout dLayout :=
  ⟨⟨fun w ↦ ⟨permKin294Val w.val, permKin294Val_lt w⟩, fun a b h ↦ Fin.ext (by
    have hv := congrArg Fin.val h; dsimp only at hv
    have h2 := congrArg permKin294Val hv
    rwa [permKin294Val_invol, permKin294Val_invol] at h2)⟩⟩

theorem val_rPermKin294 (w : Wire dLayout) : (rPermKin294 w).val = permKin294Val w.val := rfl

structure ValidPerm294NK (rP : QRegister dLayout dLayout) : Prop where
  invol : ∀ w : Wire dLayout, rP (rP w) = w
  fix_out : ∀ w : Wire dLayout,
    (¬ (5828 ≤ w.val ∧ w.val < 5851) ∧ ¬ (5923 ≤ w.val ∧ w.val < 5947) ∧
     ¬ (5990 ≤ w.val ∧ w.val < 5997) ∧ w.val ≠ 5998 ∧
     ¬ (6000 ≤ w.val ∧ w.val < 6003) ∧ w.val ≠ 6014 ∧
     ¬ (6019 ≤ w.val ∧ w.val < 6055)) → rP w = w
  scr_bounds : ∀ w : Wire dLayout,
    5650 ≤ w.val → w.val < 5650 + 1565 → 5650 ≤ (rP w).val ∧ (rP w).val < 5650 + 1565

theorem validPerm294NK_rPermNuc294 : ValidPerm294NK rPermNuc294 where
  invol w := Fin.ext (permNuc294Val_invol w.val)
  fix_out w h := Fin.ext (by rw [val_rPermNuc294]; unfold permNuc294Val; split_ifs <;> omega)
  scr_bounds w h1 h2 := by rw [val_rPermNuc294]; unfold permNuc294Val; split_ifs <;> omega

theorem validPerm294NK_rPermKin294 : ValidPerm294NK rPermKin294 where
  invol w := Fin.ext (permKin294Val_invol w.val)
  fix_out w h := Fin.ext (by rw [val_rPermKin294]; unfold permKin294Val; split_ifs <;> omega)
  scr_bounds w h1 h2 := by rw [val_rPermKin294]; unfold permKin294Val; split_ifs <;> omega

theorem validPerm294NK_rNucSub_noHB_eq {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP)
    (i : Fin (routerWidth 47 6)) (hi : i.val < 86 ∨ (110 ≤ i.val ∧ i.val < 1238) ∨ (1256 ≤ i.val ∧
    i.val < 1303) ∨ i.val = 1364 ∨ i.val = 1366) : rP (rNucSub i) = rNucSub i := by
  have hiLt : i.val < 1394 := rw47_eq ▸ i.isLt
  have hrk : i.val < 86 ∨ (110 ≤ i.val ∧ i.val < 1238) ∨ privRank156Sub (i.val - 1238) < 59 ∨
      privRank156Sub (i.val - 1238) = 83 ∨ privRank156Sub (i.val - 1238) = 85 := by
    rcases hi with h0 | h1 | hRest
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_); unfold privRank156Sub; split_ifs <;> omega
  apply hP.fix_out;
  have hv : (rNucSub i).val = (nucSubWireFn i).val := rfl; rw [hv, val_nucSubWireFn]
  split_ifs <;> omega

theorem validPerm294NK_rn_fix {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP) {n : ℕ}
    (rTot : QRegister dLayout n) (u : Fin (routerWidth 47 6))
    (hu : u.val < 86 ∨ (110 ≤ u.val ∧ u.val < 1238) ∨ (1256 ≤ u.val ∧ u.val < 1303) ∨ u.val = 1364 ∨
    u.val = 1366) : rNucW340 ((rTot.compose rP).compose rNucSub) u =
    rNucW340 (rTot.compose rNucSub) u := by
  have huLt : u.val < 1394 := rw47_eq ▸ u.isLt
  have hSw : swapNucW340 u.val = u.val := by
    change swapPair 1338 1367 6 (swapNucW350 u.val) = u.val; unfold swapNucW350 swapPair
    split_ifs <;> omega
  have hApp1 : rNucW340 ((rTot.compose rP).compose rNucSub) u = rTot (rP (rNucSub u)) := by
    change rTot (rP (rNucSub ⟨swapNucW340 u.val, swapNucW340_lt u.val u.isLt⟩)) = _
    exact congrArg (fun k ↦ rTot (rP (rNucSub k))) (Fin.ext hSw)
  have hApp2 : rNucW340 (rTot.compose rNucSub) u = rTot (rNucSub u) := by
    change rTot (rNucSub ⟨swapNucW340 u.val, swapNucW340_lt u.val u.isLt⟩) = _
    exact congrArg (fun k ↦ rTot (rNucSub k)) (Fin.ext hSw)
  rw [hApp1, hApp2, validPerm294NK_rNucSub_noHB_eq hP u hu]

theorem validPerm294NK_rElecSub_noHB_eq {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP)
    (j : Fin (routerWidth 187 8)) (hj : j.val < 90 ∨ (114 ≤ j.val ∧ j.val < 4602)) :
    rP (rElecSub j) = rElecSub j := by
  apply hP.fix_out;
  have hv : (rElecSub j).val = (elecSubWireFn j).val := rfl; rw [hv, val_elecSubWireFn]
  split_ifs <;> omega

theorem validPerm294NK_rElec_ctrlPair_eq {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP)
    {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    routerCtrlLo ((rTot.compose rP).compose rElecSub) β = routerCtrlLo (rTot.compose rElecSub) β ∧
    routerCtrlHi ((rTot.compose rP).compose rElecSub) β =
    routerCtrlHi (rTot.compose rElecSub) β := by
  let rE' := (rTot.compose rP).compose rElecSub; let rE := rTot.compose rElecSub
  have h18 : ∀ j : Fin (routerWidth 187 8), j.val < 18 → rE' j = rE j := fun j hj ↦
    congrArg rTot (validPerm294NK_rElecSub_noHB_eq hP j (Or.inl (by omega)))
  have hHas1 : rHas1 rE' = rHas1 rE := h18 ⟨0, rw_lt0 187 8⟩ (by dsimp [routerWidth]; omega)
  have hRaw2 : rRawHas2 rE' = rRawHas2 rE := h18 ⟨1, rw_lt1 187 8⟩ (by dsimp [routerWidth]; omega)
  have hIdx1 : rIdx1 rE' = rIdx1 rE := funext fun d ↦
      h18 _ (by have := d.isLt; dsimp [routerWidth]; omega)
  have hIdx2 : rIdx2 rE' = rIdx2 rE := funext fun d ↦
      h18 _ (by have := d.isLt; dsimp [routerWidth]; omega)
  change routerCtrlLo rE' β = routerCtrlLo rE β ∧ routerCtrlHi rE' β = routerCtrlHi rE β
  refine ⟨funext fun p ↦ ?_, funext fun p ↦ ?_⟩
  · simp only [routerCtrlLo, routerIdxMinVal, routerHas2Eff, hHas1, hRaw2, hIdx1, hIdx2]; rfl
  · simp only [routerCtrlHi, routerIdxMaxVal, routerHas2Eff, hRaw2, hIdx1, hIdx2]; rfl

theorem validPerm294NK_rNuc_ctrlPair_eq {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP)
    {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    routerCtrlLo ((rTot.compose rP).compose rNucSub) β = routerCtrlLo (rTot.compose rNucSub) β ∧
    routerCtrlHi ((rTot.compose rP).compose rNucSub) β = routerCtrlHi (rTot.compose rNucSub) β := by
  let rN' := (rTot.compose rP).compose rNucSub; let rN := rTot.compose rNucSub
  have h14 : ∀ i : Fin (routerWidth 47 6), i.val < 14 → rN' i = rN i := fun i hi ↦
    congrArg rTot (validPerm294NK_rNucSub_noHB_eq hP i (Or.inl (by omega)))
  have hHas1 : rHas1 rN' = rHas1 rN := h14 ⟨0, rw_lt0 47 6⟩ (by dsimp [routerWidth]; omega)
  have hRaw2 : rRawHas2 rN' = rRawHas2 rN := h14 ⟨1, rw_lt1 47 6⟩ (by dsimp [routerWidth]; omega)
  have hIdx1 : rIdx1 rN' = rIdx1 rN := funext fun d ↦
      h14 _ (by have := d.isLt; dsimp [routerWidth]; omega)
  have hIdx2 : rIdx2 rN' = rIdx2 rN := funext fun d ↦
      h14 _ (by have := d.isLt; dsimp [routerWidth]; omega)
  change routerCtrlLo rN' β = routerCtrlLo rN β ∧ routerCtrlHi rN' β = routerCtrlHi rN β
  refine ⟨funext fun p ↦ ?_, funext fun p ↦ ?_⟩
  · simp only [routerCtrlLo, routerIdxMinVal, routerHas2Eff, hHas1, hRaw2, hIdx1, hIdx2]; rfl
  · simp only [routerCtrlHi, routerIdxMaxVal, routerHas2Eff, hRaw2, hIdx1, hIdx2]; rfl

theorem validPerm294NK_cLoAlways_elec_eq {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP)
    {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    cLoAlways ((rTot.compose rP).compose rElecSub) β = cLoAlways (rTot.compose rElecSub) β := by
  have hI1 : rIdx1 ((rTot.compose rP).compose rElecSub) = rIdx1 (rTot.compose rElecSub) :=
    funext fun d ↦ congrArg rTot (validPerm294NK_rElecSub_noHB_eq hP _
      (Or.inl (by have := d.isLt; dsimp [rIdx1]; omega)))
  funext p; unfold cLoAlways; rw [hI1]

theorem validPerm294NK_cLoAlways_nuc_eq {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP)
    {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    cLoAlways ((rTot.compose rP).compose rNucSub) β = cLoAlways (rTot.compose rNucSub) β := by
  have hI1 : rIdx1 ((rTot.compose rP).compose rNucSub) = rIdx1 (rTot.compose rNucSub) :=
    funext fun d ↦ congrArg rTot (validPerm294NK_rNucSub_noHB_eq hP _
      (Or.inl (by have := d.isLt; dsimp [rIdx1]; omega)))
  funext p; unfold cLoAlways; rw [hI1]

theorem cFixedSwapCirc_validPerm294NK_rElec_eq {rP : QRegister dLayout dLayout}
    (hP : ValidPerm294NK rP) {n : ℕ} (rTot : QRegister dLayout n) (cLo cHi : Fin 187 → ZMod 2) :
    cFixedSwapCirc ((rTot.compose rP).compose rElecSub) cLo cHi =
    cFixedSwapCirc (rTot.compose rElecSub) cLo cHi := by
  let rE' := (rTot.compose rP).compose rElecSub; let rE := rTot.compose rElecSub
  have hBL : rBufLo rE' = rBufLo rE := funext fun b ↦
    congrArg rTot (validPerm294NK_rElecSub_noHB_eq hP _
        (Or.inl (by have := b.isLt; dsimp [rBufLo]; omega)))
  have hBH : rBufHi rE' = rBufHi rE := funext fun b ↦
    congrArg rTot (validPerm294NK_rElecSub_noHB_eq hP _
        (Or.inl (by have := b.isLt; dsimp [rBufHi]; omega)))
  have hSys : (fun b q ↦ rSys rE' q b) = (fun b q ↦ rSys rE q b) := funext fun b ↦ funext fun q ↦
    congrArg rTot (validPerm294NK_rElecSub_noHB_eq hP _
      (Or.inr ⟨by dsimp [rSys]; omega, by have := q.isLt; have := b.isLt; dsimp [rSys]; omega⟩))
  unfold cFixedSwapCirc;
  rw [fixedSwapVecCirc_congr_w325 hBL cLo hSys, fixedSwapVecCirc_congr_w325 hBH cHi hSys]
theorem cFixedSwapCirc_validPerm294NK_rNuc_eq {rP : QRegister dLayout dLayout}
    (hP : ValidPerm294NK rP) {n : ℕ} (rTot : QRegister dLayout n) (cLo cHi : Fin 47 → ZMod 2) :
    cFixedSwapCirc ((rTot.compose rP).compose rNucSub) cLo cHi =
    cFixedSwapCirc (rTot.compose rNucSub) cLo cHi := by
  let rN' := (rTot.compose rP).compose rNucSub; let rN := rTot.compose rNucSub
  have hBL : rBufLo rN' = rBufLo rN := funext fun b ↦
    congrArg rTot (validPerm294NK_rNucSub_noHB_eq hP _
        (Or.inl (by have := b.isLt; dsimp [rBufLo]; omega)))
  have hBH : rBufHi rN' = rBufHi rN := funext fun b ↦
    congrArg rTot (validPerm294NK_rNucSub_noHB_eq hP _
        (Or.inl (by have := b.isLt; dsimp [rBufHi]; omega)))
  have hSys : (fun b p ↦ rSys rN' p b) = (fun b p ↦ rSys rN p b) := funext fun b ↦ funext fun p ↦
    congrArg rTot (validPerm294NK_rNucSub_noHB_eq hP _
      (Or.inr (Or.inl ⟨by dsimp [rSys]; omega,
          by have := p.isLt; have := b.isLt; dsimp [rSys]; omega⟩)))
  unfold cFixedSwapCirc;
  rw [fixedSwapVecCirc_congr_w325 hBL cLo hSys, fixedSwapVecCirc_congr_w325 hBH cHi hSys]
theorem uRouterSwapAlwaysLoConj_validPerm294NK_rElec_eq {rP : QRegister dLayout dLayout}
    (hP : ValidPerm294NK rP) {n : ℕ} (rTot : QRegister dLayout n) :
    uRouterSwapAlwaysLoConj ((rTot.compose rP).compose rElecSub) =
    uRouterSwapAlwaysLoConj (rTot.compose rElecSub) := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [uRouterSwapAlwaysLoConj_mulVec_ket_any, uRouterSwapAlwaysLoConj_mulVec_ket_any,
      validPerm294NK_cLoAlways_elec_eq hP rTot β, (validPerm294NK_rElec_ctrlPair_eq hP rTot β).2,
      cFixedSwapCirc_validPerm294NK_rElec_eq hP rTot]

theorem uRouterSwapAlwaysLoConj_validPerm294NK_rNuc_eq {rP : QRegister dLayout dLayout}
    (hP : ValidPerm294NK rP) {n : ℕ} (rTot : QRegister dLayout n) :
    uRouterSwapAlwaysLoConj ((rTot.compose rP).compose rNucSub) =
    uRouterSwapAlwaysLoConj (rTot.compose rNucSub) := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [uRouterSwapAlwaysLoConj_mulVec_ket_any, uRouterSwapAlwaysLoConj_mulVec_ket_any,
      validPerm294NK_cLoAlways_nuc_eq hP rTot β, (validPerm294NK_rNuc_ctrlPair_eq hP rTot β).2,
      cFixedSwapCirc_validPerm294NK_rNuc_eq hP rTot]

theorem uBellLoCopyHiAlwaysLoConj_validPerm294NK_rElec_eq {rP : QRegister dLayout dLayout}
    (hP : ValidPerm294NK rP) {n : ℕ} (rTot : QRegister dLayout n) :
    uBellLoCopyHiAlwaysLoConj ((rTot.compose rP).compose rElecSub) =
    uBellLoCopyHiAlwaysLoConj (rTot.compose rElecSub) := by
  let rE' := (rTot.compose rP).compose rElecSub; let rE := rTot.compose rElecSub
  have hHA : rHA rE' = rHA rE := funext fun b ↦
    congrArg rTot (validPerm294NK_rElecSub_noHB_eq hP _
        (Or.inl (by have := b.isLt; dsimp [rHA]; omega)))
  have hBH : rBufHi rE' = rBufHi rE := funext fun b ↦
    congrArg rTot (validPerm294NK_rElecSub_noHB_eq hP _
        (Or.inl (by have := b.isLt; dsimp [rBufHi]; omega)))
  have hSys : (fun b q ↦ rSys rE' q b) = (fun b q ↦ rSys rE q b) := funext fun b ↦ funext fun q ↦
    congrArg rTot (validPerm294NK_rElecSub_noHB_eq hP _
      (Or.inr ⟨by dsimp [rSys]; omega, by have := q.isLt; have := b.isLt; dsimp [rSys]; omega⟩))
  have hFVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin 187 → ZMod 2)
      (t₁ t₂ : Fin 24 → Fin 187 → Wire n) (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p),
      q₁ = q₂ → t₁ = t₂ → fixedFanoutVecCirc 187 24 q₁ cV t₁ h₁ =
      fixedFanoutVecCirc 187 24 q₂ cV t₂ h₂ := by rintro _ _ _ _ _ _ _ rfl rfl; rfl
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [uBellLoCopyHiAlwaysLoConj_mulVec_ket_any, uBellLoCopyHiAlwaysLoConj_mulVec_ket_any,
      validPerm294NK_cLoAlways_elec_eq hP rTot β,
      (validPerm294NK_rElec_ctrlPair_eq hP rTot β).2]; dsimp only [cFixedBellLoCopyHiCirc];
      rw [fixedBellVecCirc_congr_w325 hHA _ hSys _ _, hFVEq _ _ _ _ _ _ _ hBH hSys]
theorem uBellLoCopyHiAlwaysLoConj_validPerm294NK_rNuc_eq {rP : QRegister dLayout dLayout}
    (hP : ValidPerm294NK rP) {n : ℕ} (rTot : QRegister dLayout n) :
    uBellLoCopyHiAlwaysLoConj ((rTot.compose rP).compose rNucSub) =
    uBellLoCopyHiAlwaysLoConj (rTot.compose rNucSub) := by
  let rN' := (rTot.compose rP).compose rNucSub; let rN := rTot.compose rNucSub
  have hHA : rHA rN' = rHA rN := funext fun b ↦
    congrArg rTot (validPerm294NK_rNucSub_noHB_eq hP _
        (Or.inl (by have := b.isLt; dsimp [rHA]; omega)))
  have hBH : rBufHi rN' = rBufHi rN := funext fun b ↦
    congrArg rTot (validPerm294NK_rNucSub_noHB_eq hP _
        (Or.inl (by have := b.isLt; dsimp [rBufHi]; omega)))
  have hSys : (fun b p ↦ rSys rN' p b) = (fun b p ↦ rSys rN p b) := funext fun b ↦ funext fun p ↦
    congrArg rTot (validPerm294NK_rNucSub_noHB_eq hP _
      (Or.inr (Or.inl ⟨by dsimp [rSys]; omega,
          by have := p.isLt; have := b.isLt; dsimp [rSys]; omega⟩)))
  have hFVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin 47 → ZMod 2) (t₁ t₂ : Fin 24 → Fin 47 → Wire n)
      (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p), q₁ = q₂ → t₁ = t₂ →
      fixedFanoutVecCirc 47 24 q₁ cV t₁ h₁ = fixedFanoutVecCirc 47 24 q₂ cV t₂ h₂ := by
    rintro _ _ _ _ _ _ _ rfl rfl; rfl
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [uBellLoCopyHiAlwaysLoConj_mulVec_ket_any, uBellLoCopyHiAlwaysLoConj_mulVec_ket_any,
      validPerm294NK_cLoAlways_nuc_eq hP rTot β,
      (validPerm294NK_rNuc_ctrlPair_eq hP rTot β).2]; dsimp only [cFixedBellLoCopyHiCirc];
      rw [fixedBellVecCirc_congr_w325 hHA _ hSys _ _, hFVEq _ _ _ _ _ _ _ hBH hSys]
theorem validPerm294NK_basisOutcomeProjector_rScrExt_eq {rP : QRegister dLayout dLayout}
    (hP : ValidPerm294NK rP) {n : ℕ} (rTot : QRegister dLayout n) :
    ((rTot.compose rP).compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 =
    (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 := by
  apply matrix_ext_ket; intro β
  rw [ket_basisOutcomeProjector_zero, ket_basisOutcomeProjector_zero]
  let rScr := rScrExt 0 hk0_le72_wstate
  have hMap (i : Fin (scrLExt 0)) : ∃ j, rScr j = rP (rScr i) := by
    have hi : i.val < 1565 := i.isLt
    have hw0Val : (rScr i).val = 5650 + i.val := val_rScrExt hk0_le72_wstate i
    have hb := hP.scr_bounds (rScr i) (by omega) (by omega)
    refine ⟨⟨(rP (rScr i)).val - 5650, by change _ < 1565; omega⟩, Fin.ext ?_⟩
    rw [val_rScrExt]
    dsimp only
    omega
  refine if_congr ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩ rfl rfl
  · obtain ⟨j, hj⟩ := hMap i
    have hj0 : β (rTot (rP (rScr j))) = 0 := h j
    rwa [hj, hP.invol] at hj0
  · obtain ⟨j, hj⟩ := hMap i
    have hj0 : β (rTot (rScr j)) = 0 := h j
    change β (rTot (rP (rScr i))) = 0
    rwa [← hj]

theorem validPerm294NK_embedUnitary_uStage1Clean_eq {rP : QRegister dLayout dLayout}
    (hP : ValidPerm294NK rP) (decode : Fin (2 ^ 41) → ZeroNEremSector) :
    rP.embedUnitary (uStage1Clean_c70 decode) = uStage1Clean_c70 decode := by
  apply Subtype.ext; unfold uStage1Clean_c70;
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  refine embedMatrix_fix_of_subreg_wstate rP Coin70Lift.rStage1Clean122_c70 (fun idx ↦ ?_) _
  unfold PhotochemistrySolution.Coin70Lift.rStage1Clean122_c70
  by_cases h40 : idx.val < 40
  · have hl : (rOut40Layout.concat rLcu82Layout Coin70Lift.hDisjOut40Lcu82_c70) idx =
        rOut40Layout ⟨idx.val, h40⟩ :=
      QRegister.concat_apply_left rOut40Layout rLcu82Layout _ ⟨idx.val, h40⟩
    rw [hl]
    exact hP.fix_out _ (by rw [val_rOut40Layout]; dsimp; omega)
  · have hi := idx.isLt
    let i82 : Fin (mLayout + 2) := ⟨idx.val - 40, by omega⟩
    have heq : idx = Fin.natAdd 40 i82 := Fin.ext (by dsimp [i82, Fin.natAdd]; omega)
    rw [heq, QRegister.concat_apply_right rOut40Layout rLcu82Layout _ i82]
    have hi82 := i82.isLt; dsimp [mLayout] at hi82
    exact hP.fix_out _ (by rw [val_rLcu82Layout]; omega)

theorem rPermKin294_embedUnitary_uAlignedKin_eq :
    rPermKin294.embedUnitary uAlignedKinCat2m1_98UselLayout = uAlignedKinCat2m1_98UselLayout ∧
    rPermKin294.embedUnitary uAlignedKinCat2m1_98CselLayout = uAlignedKinCat2m1_98CselLayout := by
  let rP := rPermKin294; have hP := validPerm294NK_rPermKin294
  have fConj : ∀ {W V : Unitary (2 ^ dLayout)},
      rP.embedUnitary W = W → rP.embedUnitary V = V →
      rP.embedUnitary (W⁻¹ * V * W) = W⁻¹ * V * W := fun {W V} hW hV ↦ by
    rw [rP.embedUnitary_mul, rP.embedUnitary_mul, rP.embedUnitary_inv, hW, hV]
  have fA0 : rP.embedUnitary uKinAlign0Layout = uKinAlign0Layout :=
    embedUnitary_circ_fix_wstate rP (FusedUnembedLGen.circWires_fwdCirc_of_cpWires_fs
      (cpWires_pKinAlign0_exact
        ⟨hP.fix_out _ (by dsimp [wAxis0]; rw [val_rOut40Layout]; dsimp; omega),
         hP.fix_out _ (by dsimp [wKinAxis0]; rw [val_rAlignLayout]; dsimp; omega)⟩
        ⟨hP.fix_out _ (by dsimp [wAxis1]; rw [val_rOut40Layout]; dsimp; omega),
         hP.fix_out _ (by dsimp [wKinAxis1]; rw [val_rAlignLayout]; dsimp; omega)⟩
        ⟨hP.fix_out _ (by dsimp [wIsFine]; rw [val_rOut40Layout]; dsimp; omega),
         hP.fix_out _ (by dsimp [wIsFineCopy]; rw [val_rAlignLayout]; dsimp; omega)⟩
        ⟨hP.fix_out _ (by dsimp [wHasE1]; rw [val_rOut40Layout]; dsimp; omega),
         hP.fix_out _ (by dsimp [wIsElecKin]; rw [val_rAlignLayout]; dsimp; omega)⟩))
  have fSp : rP.embedUnitary uSpeciesSwap50Layout = uSpeciesSwap50Layout :=
    Subtype.ext (embedMatrix_fix_of_subreg_wstate rP rSpeciesSwap50Layout (fun i ↦ by
      have hi := i.isLt; rw [rSp50_eq_fn_w0]
      exact hP.fix_out _ (by rw [val_speciesSwap50WireFn]; split_ifs <;> omega)) _)
  have fMux : rP.embedUnitary uMux27Layout = uMux27Layout :=
    Subtype.ext (embedMatrix_fix_of_subreg_wstate rP rMux27Layout (fun i ↦ by
      have hi := i.isLt; rw [rMux27_eq_fn_w0]
      exact hP.fix_out _ (by rw [val_mux27WireFn]; split_ifs <;> omega)) _)
  have hFixP : ∀ i : Fin 8, rP (rPKinLayout i) = rPKinLayout i := fun i ↦ by
    have hi := i.isLt
    exact hP.fix_out _ (by rw [val_rPKinLayout]; omega)
  have fQdpost : rP.embedUnitary
      (rPKinLayout.embedUnitary (dPost8U * qftGridUnitary)) =
      rPKinLayout.embedUnitary (dPost8U * qftGridUnitary) :=
    Subtype.ext (embedMatrix_fix_of_subreg_wstate rP rPKinLayout hFixP _)
  have fMid : rP.embedUnitary uKinMid2m1UselLayout = uKinMid2m1UselLayout :=
    Subtype.ext (embedMatrix_fix_of_subreg_wstate rP rKin226Layout (fun i ↦ by
      have hi := i.isLt; rw [rKin226_eq_fn_w0]
      exact hP.fix_out _ (by rw [val_kin226WireFn]; split_ifs <;> omega)) _)
  have fQcat :
      rP.embedUnitary (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout) =
      qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout := by
    let rCln := qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout
    have hFixCln : ∀ i : Fin 13, rP (rCln i) = rCln i := fun i ↦ by
      rw [qft8Stg3Clean13_eq_workInner ⟨i.val, by omega⟩]
      exact hP.fix_out _ (by
        have hi : i.val < 13 := i.isLt
        rw [val_rWorkInnerLayout]; dsimp only; omega)
    have abQ := andBracketWires_polyPostCancelT5Qft8Bracket98
      (P := fun w ↦ rP w = w)
      (locCat8SharedCompactGen scrWLayout) rPKinLayout
      (qft8Stg3Delta7 scrWLayout offKinLayout hoffKinLayout)
      (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout)
      (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
      (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
      (qft8Stg3_delta7_disj_cat8 hoffKinLayout)
      (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
      (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
      (qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout)
      (fun c ↦ hP.fix_out _ (by rw [val_locCat8_layout]; omega))
      hFixP
      (fun i ↦ by
        have hi := i.isLt
        rw [← qft8Stg3_clean13_sub_delta7 hoffKinLayout ⟨i.val, by omega⟩]; exact hFixCln _)
      (fun i ↦ by
        have hi := i.isLt
        rw [← qft8Stg3_clean13_sub_carry6 hoffKinLayout ⟨i.val, by omega⟩]; exact hFixCln _)
    have fBr :
        rP.embedMatrix (polyPostCancelT5Qft8Bracket98 (locCat8SharedCompactGen scrWLayout)
        rPKinLayout (qft8Stg3Delta7 scrWLayout offKinLayout hoffKinLayout)
        (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout)
        (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
        (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
        (qft8Stg3_delta7_disj_cat8 hoffKinLayout) (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
        (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
        (qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout)).toCircuit.eval.1 = _ :=
        congrArg Subtype.val (embedUnitary_circ_fix_wstate rP (circWires_toCircuit_c70 abQ));
        have fP13 : rP.embedMatrix (rCln.basisOutcomeProjector 0) = rCln.basisOutcomeProjector 0 :=
        embedMatrix_fix_of_subreg_wstate rP rCln hFixCln (compProj 0);
        have fQdpostM : rP.embedMatrix (rPKinLayout.embedUnitary (dPost8U * qftGridUnitary)).1 =
        (rPKinLayout.embedUnitary (dPost8U * qftGridUnitary)).1 :=
        congrArg Subtype.val fQdpost; refine Subtype.ext ?_; unfold qft8PostCancel98CatU
        polyPostCancelCleanUnitary spliceUnitary; change rP.embedMatrix (spliceUnitaryMat _ _ _) =
        spliceUnitaryMat _ _ _; unfold spliceUnitaryMat; rw [rP.embedMatrix_add, rP.embedMatrix_mul,
        rP.embedMatrix_mul, (QRegExt.embedMatrix_sub rP), rP.embedMatrix_one, fBr, fP13, fQdpostM]
  have fUsel : rP.embedUnitary uAlignedKinCat2m1_98UselLayout = uAlignedKinCat2m1_98UselLayout :=
      fConj fA0 (fConj fSp (fConj fMux (fConj fQcat fMid)));
      let Pq :=
      projOneQCompactGen scrWLayout; have sKin :=
                                       csel_conj_unitary Pq uKinAlign0Layout
                                       uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
                                       comm_pq.2.eq uKin2m1_98Layout_props.1
                                       uKin2m1_98Layout_props.2.1
  have fPq : rP.embedMatrix Pq = Pq :=
    embedMatrix_fix_of_subreg_wstate rP (QRegister.singleton wLocQLayout)
      (fun i ↦ by
        fin_cases i; change rP wLocQLayout = wLocQLayout
        exact hP.fix_out _ (by rw [val_wLocQLayout]; omega))
      (compProj 1)
  have fCsel : rP.embedUnitary uAlignedKinCat2m1_98CselLayout = uAlignedKinCat2m1_98CselLayout := by
    have fUselM : rP.embedMatrix (uKinAlign0Layout⁻¹ * uKinCat2m1_98UselLayout *
        uKinAlign0Layout).1 = (uKinAlign0Layout⁻¹ * uKinCat2m1_98UselLayout * uKinAlign0Layout).1 :=
        congrArg Subtype.val fUsel; refine Subtype.ext ?_; change rP.embedMatrix
        uAlignedKinCat2m1_98CselLayout.1 = uAlignedKinCat2m1_98CselLayout.1
    unfold uAlignedKinCat2m1_98CselLayout at *
    rw [sKin.1, rP.embedMatrix_add, (QRegExt.embedMatrix_sub rP), rP.embedMatrix_one,
        rP.embedMatrix_mul, fPq,
        fUselM]
  exact ⟨fUsel, fCsel⟩

theorem rPermNuc294_usedNucOnlineW294_active_w294_mCoin {wWork mCoin : ℕ} (hw : 291 ≤ wWork)
    {w : Wire dLayout} (h : UsedNucOnlineW294 rNucSub w) :
    ActiveOuterCoinStackOf 23 wWork mCoin (rPermNuc294 w) := by
  rcases h with ⟨k, rfl, hk⟩
  have hkLt : k.val < 1394 := rw47_eq ▸ k.isLt
  have hrk : k.val < 87 ∨ (110 ≤ k.val ∧ k.val < 1238) ∨ privRank156Sub (k.val - 1238) < 76 ∨
      (77 ≤ privRank156Sub (k.val - 1238) ∧ privRank156Sub (k.val - 1238) < 92) ∨
      privRank156Sub (k.val - 1238) = 100 ∨ (105 ≤ privRank156Sub (k.val - 1238) ∧
      privRank156Sub (k.val - 1238) < 141) := by
    rcases hk with h0 | h1 | hRest
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_); unfold privRank156Sub; split_ifs <;> omega
  let v := (rNucSub k).val; have hv_eq : v = (nucSubWireFn k).val := rfl
  have hv_bds : v < 5616 ∨ (5680 ≤ v ∧ v < 5713) ∨ (5715 ≤ v ∧ v < 5828) ∨ (5947 ≤ v ∧ v < 5990) ∨
      (5991 ≤ v ∧ v < 6006) ∨ v = 6014 ∨ (6019 ≤ v ∧ v < 6055) := by
    rw [hv_eq, val_nucSubWireFn]
    split_ifs <;> omega
  unfold ActiveOuterCoinStackOf; rw [val_rPermNuc294]; unfold permNuc294Val
  split_ifs <;> omega

theorem rPermKin294_kin446Stack_active_w294_mCoin {wWork mCoin : ℕ} (hw : 288 ≤ wWork)
    (hm : 53 ≤ mCoin) {w : Wire dLayout} (h : IsKinBellMux446StackWire_wstate w) :
    ActiveOuterCoinStackOf 23 wWork mCoin (rPermKin294 w) := by
  unfold IsKinBellMux446StackWire_wstate IsKinBellMuxStackWire_wstate at h;
  unfold ActiveOuterCoinStackOf; rw [val_rPermKin294]; unfold permKin294Val
  split_ifs <;> omega

theorem rNucSub_loWrap_active_w294_mCoin {wWork mCoin : ℕ} (hw : 285 ≤ wWork)
    {u : Fin (routerWidth 47 6)} (hu : u.val < 86 ∨ (110 ≤ u.val ∧ u.val < 1238) ∨ (1256 ≤ u.val ∧
    u.val < 1303) ∨ u.val = 1364 ∨ u.val = 1366) :
    ActiveOuterCoinStackOf 23 wWork mCoin (rNucW340 rNucSub u) := by
  have huLt : u.val < 1394 := rw47_eq ▸ u.isLt
  have hSw : swapNucW340 u.val = u.val := by
    change swapPair 1338 1367 6 (swapNucW350 u.val) = u.val; unfold swapNucW350 swapPair
    split_ifs <;> omega
  have hEq : rNucW340 rNucSub u = rNucSub u := by
    change rNucSub ⟨swapNucW340 u.val, swapNucW340_lt u.val u.isLt⟩ = rNucSub u;
    exact congrArg rNucSub (Fin.ext hSw)
  rw [hEq]
  have hrk : u.val < 86 ∨ (110 ≤ u.val ∧ u.val < 1238) ∨ privRank156Sub (u.val - 1238) < 59 ∨
      privRank156Sub (u.val - 1238) = 83 ∨ privRank156Sub (u.val - 1238) = 85 := by
    rcases hu with h0 | h1 | hRest
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_); unfold privRank156Sub; split_ifs <;> omega
  have hv : (rNucSub u).val = (nucSubWireFn u).val :=
      rfl; unfold ActiveOuterCoinStackOf; rw [hv, val_nucSubWireFn]
  split_ifs <;> omega

/-! ## Part 3: Combined Stage 2N + 3 (`pNucKinOnlineHBW294`, `5,038 + 446/450 T`, `294 ≤ wWork`) -/

def pNucKinOnlineHBW294 {Var : Type} {n : ℕ} (v : Var) (rTot : QRegister dLayout n)
    (isCsel : Bool) : DynamicCircuit Var n :=
  let rTotN := rTot.compose rPermNuc294; let rTotK := rTot.compose rPermKin294;
  let rn := rNucW340 (rTot.compose rNucSub); let rnN := rNucW340 (rTotN.compose rNucSub)
  wrapWRouterLo47 v (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (qEncNuc rn)
    (.seq
      (wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN)
        (pNucCoreMidBellZ8W294 v rnN))
      (.seq (pAlignedKinBellMux446AsymStack_wstate v rTotK isCsel)
        (pHACollapseFlipLo0_24Dyn v rn)))

theorem counts_pNucKinOnlineHBW294 {Var : Type} [Finite Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rTot : QRegister dLayout n) (isCsel : Bool) : (pNucKinOnlineHBW294 v rTot isCsel).count .T =
    5038 + (if isCsel then 450 else 446) ∧ (pNucKinOnlineHBW294 v rTot isCsel).count .TOFF = 0 := by
  let _ := Fintype.ofFinite Var
  classical
  let rTotN := rTot.compose rPermNuc294; let rTotK := rTot.compose rPermKin294;
  let rn := rNucW340 (rTot.compose rNucSub);
  let rnN := rNucW340 (rTotN.compose rNucSub); obtain ⟨tm, fm⟩ :=
      count_pNucCoreMidBellZ8W294 v rnN; obtain ⟨_, tk, fk⟩ :=
      subspaceStep_counts_pAlignedKinBellMux446_wstate v rTotK isCsel; obtain ⟨tcA, fcA⟩ :=
      count_pHACollapseFlipLo0_24Dyn v rn
  have hSeqT : ∀ (p q : DynamicCircuit Var n), (p.seq q).count .T = p.count .T + q.count .T :=
    fun _ _ ↦ rfl
  have hSeqF : ∀ (p q : DynamicCircuit Var n), (p.seq q).count .TOFF = p.count .TOFF +
      q.count .TOFF :=
    fun _ _ ↦ rfl
  obtain ⟨tHi, fHi⟩ :=
      count_wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN)
      (pNucCoreMidBellZ8W294 v rnN); obtain ⟨tLo, fLo⟩ :=
      count_wrapWRouterLo47 v (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (qEncNuc rn)
      (.seq (wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN)
      (pNucCoreMidBellZ8W294 v rnN)) (.seq (pAlignedKinBellMux446AsymStack_wstate v rTotK isCsel)
      (pHACollapseFlipLo0_24Dyn v rn))); change (wrapWRouterLo47 v (rHas1 rn) (rIdx1 rn)
      (wOutLoN48 rn) (qEncNuc rn) _).count .T = _ ∧ (wrapWRouterLo47 v (rHas1 rn) (rIdx1 rn)
      (wOutLoN48 rn) (qEncNuc rn) _).count .TOFF = 0; rw [tLo, fLo, hSeqT, hSeqT, hSeqF, hSeqF, tHi,
      fHi, tm, tk, tcA, fm, fk, fcA]
  cases isCsel <;> dsimp <;> omega

theorem dynWires_pNucKinOnlineHBW294_mCoin {Var : Type} {n wWork mCoin : ℕ} {S : Wire n → Prop}
    (hw : 291 ≤ wWork) (hm : 53 ≤ mCoin) (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool)
    (hAct : ∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rTot w)) :
    DynWires S (pNucKinOnlineHBW294 v rTot isCsel) := by
  let rTotN := rTot.compose rPermNuc294
  let rNN := rTotN.compose rNucSub
  let rnN := rNucW340 rNN
  let rn := rNucW340 (rTot.compose rNucSub)
  have hSN (w : Wire n) : UsedNucOnlineW294 rNN w → S w := fun ⟨k, hk, hcond⟩ ↦
    hk ▸ hAct _ (rPermNuc294_usedNucOnlineW294_active_w294_mCoin hw ⟨k, rfl, hcond⟩)
  have hUN {u : Fin (routerWidth 47 6)}
      (hu : u.val < 87 ∨ (110 ≤ u.val ∧ u.val < basePub 47 6) ∨
       (1244 ≤ u.val ∧ u.val < 1350) ∨ (1351 ≤ u.val ∧ u.val < 1357) ∨
       (1364 ≤ u.val ∧ u.val < 1367) ∨ (1381 ≤ u.val ∧ u.val < 1394)) : S (rnN u) :=
    hSN _ (rNucW340_in_usedNucOnlineW294 rNN hu)
  have hU0 {u : Fin (routerWidth 47 6)}
      (hu : u.val < 86 ∨ (110 ≤ u.val ∧ u.val < 1238) ∨
       (1256 ≤ u.val ∧ u.val < 1303) ∨ u.val = 1364 ∨ u.val = 1366) : S (rn u) :=
    hAct _ (rNucSub_loWrap_active_w294_mCoin (by omega) hu)
  refine dynWires_wrapWRouterLo47 v (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (qEncNuc rn) _
    (hU0 (Or.inl (by decide))) (fun d ↦ hU0 (Or.inl ?_))
    (wOutLoN48_mem rn (fun p ↦ hU0 (Or.inr (Or.inr (Or.inl ?_))))
      (hU0 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (hU0 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    ⟨dynWires_wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN) _
      (hUN (u := ⟨1, rw47_lt_1⟩) (Or.inl (by decide))) (fun d ↦ hUN (Or.inl ?_))
      (wOutHiN48_mem rnN (fun p ↦ hUN (Or.inr (Or.inr (Or.inl ?_))))
        (hUN (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))
      (hUN (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
      (dynWires_pNucCoreMidBellZ8W294_w294 v rNN hSN),
     ⟨dynWires_pAlignedKinBellMux446AsymStack_wstate v (rTot.compose rPermKin294) isCsel
        (fun w hwK ↦ hAct _ (rPermKin294_kin446Stack_active_w294_mCoin (by omega) hm hwK)),
      dynWires_pHACollapseFlipLo0_24Dyn v rn (hU0 (Or.inl (by decide)))
        (fun b ↦ hU0 (Or.inl ?_)) (fun b ↦ hU0 (Or.inl ?_))
        (fun p ↦ hU0 (Or.inr (Or.inr (Or.inl ?_))))
        (fun b p ↦ hU0 (Or.inr (Or.inl ?_)))⟩⟩
  all_goals
    dsimp [rIdx1, rIdx2, rCtrlLo, rCtrlHi, rBufLo, rHA, rSys, basePub]
    omega

attribute [local irreducible] wStateComputeLo47 wStateUncomputeLo47 wrapWRouterHi47
  pAlignedKinBellMux446AsymStack_wstate pHACollapseFlipLo0_24Dyn
  systemQubits_frozen ancWOfScr uDualBellAlwaysLoRouterConj uRouterSwapConj
  uRouterSwapAlwaysLoConj uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj uZeroSwapNE
lemma uOneHotToggle_congr48 {n : ℕ} {h₁ h₂ : Wire n} {i₁ i₂ : Fin 6 → Wire n}
    {o₁ o₂ : Fin 48 → Wire n} {g1a : ∀ j, h₁ ≠ o₁ j} {g1b : ∀ d j, i₁ d ≠ o₁ j}
    {g2a : ∀ j, h₂ ≠ o₂ j} {g2b : ∀ d j, i₂ d ≠ o₂ j} (eh : h₁ = h₂) (ei : i₁ = i₂)
    (eo : o₁ = o₂) : uOneHotToggle h₁ i₁ o₁ g1a g1b = uOneHotToggle h₂ i₂ o₂ g2a g2b := by
  subst eh; subst ei; subst eo; rfl
theorem validPerm294NK_uLoToggle_rn_eq {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP)
    {n : ℕ} (rTot : QRegister dLayout n) :
    let rn' := rNucW340 ((rTot.compose rP).compose rNucSub);
    let rn := rNucW340 (rTot.compose rNucSub); let dLo' := wRouterDisj_loN48 rn';
    let dLo := wRouterDisj_loN48 rn
    uOneHotToggle (rHas1 rn') (rIdx1 rn') (wOutLoN48 rn') dLo'.has_ne_out dLo'.idx_ne_out =
      uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out := by
  intro rn' rn dLo' dLo; have hbp : basePub 47 6 = 1238 := rfl
  have eh : rHas1 rn' = rHas1 rn :=
    validPerm294NK_rn_fix hP rTot _ (Or.inl (by dsimp [rHas1]; omega))
  have ei : rIdx1 rn' = rIdx1 rn := funext fun d ↦
    validPerm294NK_rn_fix hP rTot _ (Or.inl (by have := d.isLt; dsimp [rIdx1]; omega))
  have eo : wOutLoN48 rn' = wOutLoN48 rn := funext fun j ↦ by
    by_cases hj : j.val < 47
    · have hL : wOutLoN48 rn' j = rCtrlLo rn' ⟨j.val, hj⟩ := by
        unfold wOutLoN48 PhotochemistrySolution.WStateStage5Unload.padWires;
        rw [_root_.dite_eq_left hj]
      have hR : wOutLoN48 rn j = rCtrlLo rn ⟨j.val, hj⟩ := by
        unfold wOutLoN48 WStateStage5Unload.padWires; rw [_root_.dite_eq_left hj]
      rw [hL, hR]
      exact validPerm294NK_rn_fix hP rTot _ (Or.inr (Or.inr (Or.inl
        ⟨by dsimp [rCtrlLo]; rw [hbp]; omega, by dsimp [rCtrlLo]; rw [hbp]; omega⟩)))
    · have hj47 : j.val = 47 := by have := j.isLt; omega
      have hL : wOutLoN48 rn' j = padLoN48 rn' ⟨0, by omega⟩ := by
        unfold wOutLoN48 PhotochemistrySolution.WStateStage5Unload.padWires
        rw [_root_.dite_eq_right hj]; rfl
      have hR : wOutLoN48 rn j = padLoN48 rn ⟨0, by omega⟩ := by
        unfold wOutLoN48 PhotochemistrySolution.WStateStage5Unload.padWires
        rw [_root_.dite_eq_right hj]; rfl
      rw [hL, hR]; exact validPerm294NK_rn_fix hP rTot _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  exact uOneHotToggle_congr48 eh ei eo

theorem validPerm294NK_rn_unitaries_eq {rP : QRegister dLayout dLayout} (hP : ValidPerm294NK rP)
    {n : ℕ} (rTot : QRegister dLayout n) :
    let rn' := rNucW340 ((rTot.compose rP).compose rNucSub);
    let rn := rNucW340 (rTot.compose rNucSub)
    uRouterSwapAlwaysLoConj rn' = uRouterSwapAlwaysLoConj rn ∧
    uBellLoCopyHiAlwaysLoConj rn' = uBellLoCopyHiAlwaysLoConj rn := by
  intro rn' rn;
  obtain ⟨_, hSw', _, hBL'⟩ :=
      routerAlwaysLoUnitaries_congr_of_samePubPriv (samePubPriv_rNucW340 ((rTot.compose rP).compose
      rNucSub)); obtain ⟨_, hSw, _, hBL⟩ :=
      routerAlwaysLoUnitaries_congr_of_samePubPriv (samePubPriv_rNucW340 (rTot.compose rNucSub))
  exact ⟨Subtype.ext ((hSw'.trans (congrArg Subtype.val
      (uRouterSwapAlwaysLoConj_validPerm294NK_rNuc_eq hP rTot))).trans hSw.symm),
         Subtype.ext ((hBL'.trans (congrArg Subtype.val
             (uBellLoCopyHiAlwaysLoConj_validPerm294NK_rNuc_eq hP rTot))).trans hBL.symm)⟩

theorem commutesWithDyn_uBellLoCopyHiAlwaysLoConj_pNucKinOnlineHBW294 {Var : Type} [Finite Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rTot : QRegister dLayout n)
    (isCsel : Bool) : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj (rTot.compose rElecSub))
    (pNucKinOnlineHBW294 v rTot isCsel) := by
  let _ := Fintype.ofFinite Var
  classical
  let rE := rTot.compose rElecSub; let rN := rTot.compose rNucSub; let rn := rNucW340 rN;
  let rTotN := rTot.compose rPermNuc294; let rEN := rTotN.compose rElecSub;
  let rNN := rTotN.compose rNucSub; let rnN := rNucW340 rNN; let rTotK := rTot.compose rPermKin294;
  have hbp : basePub 47 6 = 1238 := rfl
  have hSNrN : ∀ w, UsedNucOnlineW294 rNN w → InnerLoCopyHiSafe rEN w := by
    rintro _ ⟨k, rfl, _⟩; exact innerLoCopyHiSafe_rElecSub_of_rNucSub rTotN k
  have hUN : ∀ {u : Fin (routerWidth 47 6)},
      (u.val < 87 ∨ (110 ≤ u.val ∧ u.val < basePub 47 6) ∨
       (1244 ≤ u.val ∧ u.val < 1350) ∨ (1351 ≤ u.val ∧ u.val < 1357) ∨
       (1364 ≤ u.val ∧ u.val < 1367) ∨ (1381 ≤ u.val ∧ u.val < 1394)) →
      InnerLoCopyHiSafe rEN (rnN u) :=
    fun {u} hu ↦ hSNrN _ (rNucW340_in_usedNucOnlineW294 rNN hu)
  have hU0 : ∀ (u : Fin (routerWidth 47 6)), InnerLoCopyHiSafe rE (rn u) := fun u ↦ by
    change InnerLoCopyHiSafe rE (rTot (rNucSub ⟨swapNucW340 u.val, swapNucW340_lt u.val u.isLt⟩));
    exact innerLoCopyHiSafe_rElecSub_of_rNucSub rTot _
  have dwHi : DynWires (InnerLoCopyHiSafe rEN)
      (wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN)
        (pNucCoreMidBellZ8W294 v rnN)) :=
    dynWires_wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN) _
      (hUN (u := ⟨1, rw47_lt_1⟩) (Or.inl (by change 1 < 87; omega)))
      (fun d ↦ hUN (Or.inl (by have := d.isLt; dsimp [rIdx2]; omega)))
      (wOutHiN48_mem rnN
        (fun p ↦ hUN (Or.inr (Or.inr (Or.inl ⟨by dsimp [rCtrlHi]; rw [hbp]; omega,
          by have := p.isLt; dsimp [rCtrlHi]; rw [hbp]; omega⟩))))
        (hUN (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, by dsimp; omega⟩)))))))
      (hUN (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, by dsimp; omega⟩))))))
      (dynWires_pNucCoreMidBellZ8W294_w294 v rNN hSNrN)
  have fHi : (wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN)
      (pNucCoreMidBellZ8W294 v rnN)).count .TOFF =
      0 := by
    obtain ⟨_, fW⟩ :=
        count_wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN)
        (pNucCoreMidBellZ8W294 v rnN); obtain ⟨_, fm⟩ :=
        count_pNucCoreMidBellZ8W294 v rnN; rw [fW, fm]
  have cHi : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj rE) (wrapWRouterHi47 v (rRawHas2 rnN)
      (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN) (pNucCoreMidBellZ8W294 v rnN))
      := by
    rw [← uBellLoCopyHiAlwaysLoConj_validPerm294NK_rElec_eq validPerm294NK_rPermNuc294 rTot];
    exact commutesWithDyn_uBellLoCopyHiAlwaysLoConj_of_dynWires rEN dwHi fHi
  have cKin : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj rE)
      (pAlignedKinBellMux446AsymStack_wstate v rTotK isCsel) := by
    rw [← uBellLoCopyHiAlwaysLoConj_validPerm294NK_rElec_eq validPerm294NK_rPermKin294 rTot];
    exact commutesWithDyn_uBellLoCopyHiAlwaysLoConj_pAlignedKinBellMux446AsymStack v rTotK isCsel
  have cHA : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj rE) (pHACollapseFlipLo0_24Dyn v rn) :=
      commutesWithDyn_uBellLoCopyHiAlwaysLoConj_of_dynWires rE (dynWires_pHACollapseFlipLo0_24Dyn v
      rn (hU0 _) (fun _ ↦ hU0 _) (fun _ ↦ hU0 _) (fun _ ↦ hU0 _) (fun _ _ ↦ hU0 _))
      (count_pHACollapseFlipLo0_24Dyn v rn).2
  have cComp : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj rE) (wStateComputeLo47 v (rHas1 rn)
      (rIdx1 rn) (wOutLoN48 rn) (qEncNuc rn)) :=
      commutesWithDyn_uBellLoCopyHiAlwaysLoConj_of_dynWires rE (dynWires_wStateComputeLo47 v
      (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (qEncNuc rn) (hU0 _) (fun _ ↦ hU0 _)
      (wOutLoN48_mem rn (fun _ ↦ hU0 _) (hU0 _)) (hU0 _)) (count_wStateComputeLo47 v (rHas1 rn)
      (rIdx1 rn) (wOutLoN48 rn) (qEncNuc rn)).2
  have cUncomp : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj rE) (wStateUncomputeLo47 v (rHas1 rn)
      (rIdx1 rn) (wOutLoN48 rn)) :=
      commutesWithDyn_uBellLoCopyHiAlwaysLoConj_of_dynWires rE (dynWires_wStateUncomputeLo47 v
      (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) (hU0 _) (fun _ ↦ hU0 _) (wOutLoN48_mem rn (fun _ ↦ hU0 _)
      (hU0 _))) (count_wStateUncomputeLo47 v (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn)).2
  exact ⟨cComp, ⟨cHi, cKin, cHA⟩, cUncomp⟩

theorem subspaceStep_pNucKinOnlineHBW294_raw
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {w1 n : ℕ} [NeZero (2 ^ n)]
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (hSort : SortedZeroNEremCoin decode)
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool)
    (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁) :
    let rN := rTot.compose rNucSub; let rE := rTot.compose rElecSub;
    let W₁ := rTot.embedUnitary (uStage1Clean_c70 decode);
    let Wnh := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    SubspaceStep (Var := Var)
      ((uBellLoCopyHiAlwaysLoConj rE).1 * ((uRouterSwapAlwaysLoConj rE).1 * (W₁.1 * X₁)))
      ((uBellLoCopyHiAlwaysLoConj rE).1 *
        (uCopyLoHiAlwaysLoMat rN *
          ((uZeroSwapNE rTot).1 *
            (uKin.1 * (Wnh.1 * X₁)))))
      (pNucKinOnlineHBW294 v rTot isCsel) := by
  intro rN rE W₁ Wnh uKin; have hbp : basePub 47 6 = 1238 := rfl;
  have hPN := validPerm294NK_rPermNuc294; have hPK := validPerm294NK_rPermKin294;
  let rTotN := rTot.compose rPermNuc294; let rTotK := rTot.compose rPermKin294;
  let rNN := rTotN.compose rNucSub; let rEN := rTotN.compose rElecSub;
  let rNK := rTotK.compose rNucSub; let rEK := rTotK.compose rElecSub; let rn := rNucW340 rN;
  let rnN := rNucW340 rNN; let rnK := rNucW340 rNK
  have hAbsX₁N : (rTotN.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁ := by
    rw [validPerm294NK_basisOutcomeProjector_rScrExt_eq hPN]; exact hAbsX₁
  have hAbsX₁K : (rTotK.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁ := by
    rw [validPerm294NK_basisOutcomeProjector_rScrExt_eq hPK]; exact hAbsX₁
  have dN0 : ∀ (i : Fin (routerWidth 47 6)) (j : Fin 0), rNucSub i ≠ rCoinExt 0 hk0_le72_wstate j :=
      fun _ j ↦ Fin.elim0 j
  have dE0 : ∀ (i : Fin (routerWidth 187 8)) (j : Fin 0), rElecSub i ≠
      rCoinExt 0 hk0_le72_wstate j := fun _ j ↦ Fin.elim0 j
  obtain ⟨cSh₁, _, _, cEq₁, _, _⟩ :=
      routerChain_sharedPortB341_ext hk0_le72_wstate validMuxD1Stage2Regs_sub
      cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub dN0 dE0 hSort rTot o1 hAbsX₁;
      obtain ⟨cSh₁N, _, _, _, _, _⟩ :=
      routerChain_sharedPortB341_ext hk0_le72_wstate validMuxD1Stage2Regs_sub
      cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub dN0 dE0 hSort rTotN o1 hAbsX₁N;
      obtain ⟨cSh₁K, _, _, cEq₁K, _, c714₁K⟩ :=
      routerChain_sharedPortB341_ext hk0_le72_wstate validMuxD1Stage2Regs_sub
      cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub dN0 dE0 hSort rTotK o1 hAbsX₁K
  have hW₁EqN : rTotN.embedUnitary (uStage1Clean_c70 decode) = W₁ := by
    dsimp only [rTotN, W₁];
    rw [QRegister.embedUnitary_compose, validPerm294NK_embedUnitary_uStage1Clean_eq hPN]
  have hW₁EqK : rTotK.embedUnitary (uStage1Clean_c70 decode) = W₁ := by
    dsimp only [rTotK, W₁];
    rw [QRegister.embedUnitary_compose, validPerm294NK_embedUnitary_uStage1Clean_eq hPK]
  let R := (uRouterSwapAlwaysLoConj rE).1 * (W₁.1 * X₁);
  let R_sw := (uRouterSwapAlwaysLoConj rn).1 * R; obtain ⟨cN₁, cSwEq⟩ :=
      sharedPortB341_routerAlwaysLo_chain_wstate rTot cSh₁;
      have hSPP := samePubPriv_rNucW340 rN; obtain ⟨_, hSwEq0, _, _⟩ :=
      routerAlwaysLoUnitaries_congr_of_samePubPriv hSPP
  have hRn : SupportedOn (ValidZeroGatedSortedRouterInput rn) R := fun A B hAB ↦ cN₁ A B fun β hβ ↦
      hAB β ((validZeroGated_iff_of_samePubPriv hSPP β).mpr hβ)
  obtain ⟨cN₁N_raw, _⟩ := sharedPortB341_routerAlwaysLo_chain_wstate rTotN cSh₁N
  have cN₁N : SupportedOn (ValidZeroGatedSortedRouterInput rNN) R := by
    dsimp only [R]; rw [← hW₁EqN, ← uRouterSwapAlwaysLoConj_validPerm294NK_rElec_eq hPN rTot];
    exact cN₁N_raw
  have hSPPN := samePubPriv_rNucW340 rNN
  have hRnN : SupportedOn (ValidZeroGatedSortedRouterInput rnN) R := fun A B hAB ↦
      cN₁N A B fun β hβ ↦ hAB β ((validZeroGated_iff_of_samePubPriv hSPPN β).mpr hβ)
  let dLo := wRouterDisj_loN48 rn;
  let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out;
  have hULoN := validPerm294NK_uLoToggle_rn_eq hPN rTot; obtain ⟨hSwN, hBLN⟩ :=
      validPerm294NK_rn_unitaries_eq hPN rTot
  have sPiece1 : SubspaceStep (Var := Var)
      (ULo.1 * R)
      (ULo.1 * ((uBellLoCopyHiAlwaysLoConj rn).1 * R_sw))
      (wrapWRouterHi47 v (rRawHas2 rnN) (rIdx2 rnN) (wOutHiN48 rnN) (qEncNuc rnN)
        (pNucCoreMidBellZ8W294 v rnN)) :=
    subspaceStep_congr_in
      (congrArg (fun U : Unitary (2 ^ n) ↦ U.1 * R) hULoN.symm)
      (subspaceStep_congr_out
        (subspaceStep_pNucInnerHiWrapOnlineHB v rnN R hRnN)
        (by dsimp only [R_sw]; rw [hULoN, hBLN, hSwN]))
  obtain ⟨_, cSwEqK⟩ := sharedPortB341_routerAlwaysLo_chain_wstate rTotK cSh₁K;
  let WnhK := rTotK.embedUnitary (wNoHad (uStage1Clean_c70 decode))
  have hSwWnhK : R_sw = (uZeroSwapNE rTotK).1 * (WnhK.1 * X₁) := by
    dsimp only [R_sw, R];
    rw [hSwEq0, ← uRouterSwapAlwaysLoConj_validPerm294NK_rNuc_eq hPK rTot,
        ← uRouterSwapAlwaysLoConj_validPerm294NK_rElec_eq hPK rTot, ← hW₁EqK]
    exact cSwEqK.trans (congrArg ((uZeroSwapNE rTotK).1 * ·) cEq₁K)
  have hPred0K := projPred448_absorb_R_in hk0_le72_wstate o1 rTotK hAbsX₁K;
  have hClean0K := clean690_absorb_on_Wnh_wstate rTotK X₁ hAbsX₁K c714₁K
  have hPredSwK : rTotK.embedMatrix projPred448Layout * R_sw = R_sw := by
    rw [hSwWnhK, ← Matrix.mul_assoc, ← comm_uZeroSwapNE_projPred448_wstate rTotK, Matrix.mul_assoc,
        hPred0K]
  have hCleanSwK :
      (rTotK.compose (rPermKinStack_wstate.compose rClean690Layout)).basisOutcomeProjector 0 *
      R_sw = R_sw := by
    rw [hSwWnhK, ← Matrix.mul_assoc, ← comm_uZeroSwapNE_clean690_wstate rTotK, Matrix.mul_assoc,
        hClean0K]
  let P_inK :=
      rTotK.embedMatrix projPred448Layout *
      (rTotK.compose (rPermKinStack_wstate.compose rClean690Layout)).basisOutcomeProjector 0
  have hPinSwK : P_inK * R_sw = R_sw := by
    dsimp only [P_inK]; rw [Matrix.mul_assoc, hCleanSwK, hPredSwK]
  have hKinEqK :
      rTotK.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
      uAlignedKinCat2m1_98UselLayout) = uKin := by
    dsimp only [rTotK, uKin]; rw [QRegister.embedUnitary_compose];
    obtain ⟨fU, fC⟩ := rPermKin294_embedUnitary_uAlignedKin_eq
    cases isCsel <;> simp [fU, fC]
  have sKin0 := (subspaceStep_counts_pAlignedKinBellMux446_wstate v rTotK isCsel).1
  have sKinSw : SubspaceStep (Var := Var) R_sw (uKin.1 * R_sw)
      (pAlignedKinBellMux446AsymStack_wstate v rTotK isCsel) :=
    subspaceStep_congr_in hPinSwK.symm
      (subspaceStep_congr_out
        (PhotochemistrySolution.PotOraclePortB.subspaceStep_mul_right R_sw sKin0)
        (by rw [hKinEqK, Matrix.mul_assoc, hPinSwK]))
  have hULoK := validPerm294NK_uLoToggle_rn_eq hPK rTot; obtain ⟨_, hBLK⟩ :=
      validPerm294NK_rn_unitaries_eq hPK rTot
  have cKinLo : CommutesWithDyn ULo (pAlignedKinBellMux446AsymStack_wstate v rTotK isCsel) := by
    dsimp only [ULo]; rw [← hULoK];
    exact commutesWithDyn_uLoToggle_pAlignedKinBellMux446AsymStack v rTotK isCsel
  have cKinBL : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj rn)
      (pAlignedKinBellMux446AsymStack_wstate v rTotK isCsel) := by
    rw [← hBLK];
    exact commutesWithDyn_uBellLoCopyHiAlwaysLoConj_rn_pAlignedKinBellMux446AsymStack v rTotK isCsel
  have sPiece2 : SubspaceStep (Var := Var)
      (ULo.1 * ((uBellLoCopyHiAlwaysLoConj rn).1 * R_sw))
      ((uBellLoCopyHiAlwaysLoConj rn).1 * (ULo.1 * (uKin.1 * R_sw)))
      (pAlignedKinBellMux446AsymStack_wstate v rTotK isCsel) :=
    subspaceStep_congr_out
      (subspaceStep_mul_left_of_commutesWithDyn ULo cKinLo
        (subspaceStep_mul_left_of_commutesWithDyn (uBellLoCopyHiAlwaysLoConj rn) cKinBL sKinSw))
      (by rw [← Matrix.mul_assoc, uLoToggle_comm_uBellLoCopyHiAlwaysLoConj_nuc rn,
            Matrix.mul_assoc])
  have pubCtrl_eq {δ₁ δ₂ : BitAssignment n}
      (hPub : ∀ w, PubCtrlSet rn w → δ₁ w = δ₂ w) :
      δ₁ (rHas1 rn) = δ₂ (rHas1 rn) ∧
      idxValD (rIdx1 rn) δ₁ = idxValD (rIdx1 rn) δ₂ ∧
      (∀ p : Fin 47, routerCtrlLo rn δ₁ p = routerCtrlLo rn δ₂ p) := by
    have hI1 : idxValD (rIdx1 rn) δ₁ = idxValD (rIdx1 rn) δ₂ :=
      idxValD_congr (rIdx1 rn) fun d ↦ hPub _ ((pubCtrlSet_roles rn).2.2.1 d)
    refine ⟨hPub _ (pubCtrlSet_roles rn).1, hI1, fun p ↦ ?_⟩
    unfold routerCtrlLo routerIdxMinVal routerHas2Eff
    rw [hPub _ (pubCtrlSet_roles rn).1, hPub _ (pubCtrlSet_roles rn).2.1, hI1,
        idxValD_congr (rIdx2 rn) fun d ↦ hPub _ ((pubCtrlSet_roles rn).2.2.2 d)]
  let P_lo : BitAssignment n → Prop := fun α ↦
      (∀ b : Fin 24, α (rHA rn b) = 0) ∧ ValidWRouterCleanLo47 (rHas1 rn) (rIdx1 rn)
      (wOutLoN48 rn) α ∧ (∀ p : Fin 47, routerCtrlLo rn α p = if idxValD (rIdx1 rn) α =
      p.val then α (rHas1 rn) else 0)
  have hLoSw : SupportedOn P_lo R_sw := by
    refine supportedOn_uRouterSwapAlwaysLoConj_of_not_swapMod rn ?_ R hRn (fun β hβ ↦ ?_)
    · intro u hu α val ⟨hHA0, hCln, hCL⟩;
      have hAll : AllPlaneMod rn u := swapModSet_sub_allPlaneMod rn hu
      have neHA : ∀ b : Fin 24, rHA rn b ≠ u := fun b e ↦ by
        rcases hu with ⟨d, rfl⟩ | ⟨d, rfl⟩ | ⟨d, q, rfl⟩
        · exact rr_ne rn (by have := b.isLt; have := d.isLt; dsimp [rHA, rBufLo]; omega) e
        · exact rr_ne rn (by have := b.isLt; have := d.isLt; dsimp [rHA, rBufHi]; omega) e
        · exact rr_ne rn
              (by have := b.isLt; have := d.isLt; have := q.isLt; dsimp [rHA, rSys]; omega) e
      have nePub : ∀ w, PubCtrlSet rn w → w ≠ u := by
        rintro _ ⟨i, hi, rfl⟩ e
        exact not_allPlaneMod_of_idx rn (Or.inl hi) (e ▸ hAll)
      obtain ⟨hHas1Eq, hIdx1Eq, hCLEq⟩ := pubCtrl_eq (δ₁ := Function.update α u val) (δ₂ := α)
        fun w hw ↦ Function.update_of_ne (nePub w hw) val α
      refine ⟨fun b ↦ (Function.update_of_ne (neHA b) val α).trans (hHA0 b),
        validWRouterCleanLo47_loN48_inv rn hAll α val hCln, fun p ↦ ?_⟩
      rw [hCLEq p, hCL p, hIdx1Eq, hHas1Eq]
    · have hBase := validWRouterBase_nuc8886 rn hβ;
      have hPCRLo := routerCtrlLo_of_zeroGatedSorted hβ
      refine ⟨fun b ↦ (hβ.1.2.2.2.1 b).2.2.1, hBase.2.2.2, fun p ↦ ?_⟩
      rw [congrFun hPCRLo p]
      by_cases hv : p.val = idxValD (rIdx1 rn) β
      · rw [_root_.ite_eq_left hv, _root_.ite_eq_left hv.symm]
      · rw [_root_.ite_eq_right hv, _root_.ite_eq_right (fun e ↦ hv e.symm)]
  have hLoKin : SupportedOn P_lo (uKin.1 * R_sw) := by
    refine supportedOn_uKin_of_dep_kinDisjBand_wstate rTot isCsel (fun α α' hBand ⟨hHA0, hCln,
        hCL⟩ ↦ ?_) hLoSw
    have hRnEq : ∀ {u : Fin (routerWidth 47 6)},
        (u.val < 14 ∨ (62 ≤ u.val ∧ u.val < 86) ∨ (1256 ≤ u.val ∧ u.val < 1303) ∨ u.val = 1364) →
        α' (rn u) = α (rn u) := fun {u} hu ↦ by
      obtain ⟨hEq, hKB⟩ := rNucW340_kinDisjBand_fixed rTot hu
      rw [hEq]; exact (hBand (rNucSub u) hKB).symm
    obtain ⟨hHas1Eq, hIdx1Eq, hCLEq⟩ := pubCtrl_eq (δ₁ := α') (δ₂ := α)
      (by rintro _ ⟨u, hu, rfl⟩; exact hRnEq (Or.inl hu))
    have hHAEq : ∀ b : Fin 24, α' (rHA rn b) = α (rHA rn b) := fun b ↦
      hRnEq (Or.inr (Or.inl ⟨by dsimp [rHA]; omega, by have := b.isLt; dsimp [rHA]; omega⟩))
    have hOutEq : ∀ j : Fin 48, α' (wOutLoN48 rn j) = α (wOutLoN48 rn j) :=
      wOutLoN48_mem (S := fun v ↦ α' v = α v) rn
        (fun p ↦ hRnEq (Or.inr (Or.inr (Or.inl ⟨by dsimp [rCtrlLo]; rw [hbp]; omega,
          by have := p.isLt; dsimp [rCtrlLo]; rw [hbp]; omega⟩))))
        (hRnEq (Or.inr (Or.inr (Or.inr rfl))))
    refine ⟨fun b ↦ (hHAEq b).trans (hHA0 b),
      ⟨fun j ↦ (hOutEq j).trans (hCln.1 j), hIdx1Eq ▸ hCln.2.1,
       fun h0 ↦ hIdx1Eq ▸ hCln.2.2 (hHas1Eq.symm.trans h0)⟩, fun p ↦ ?_⟩
    rw [hCLEq p, hCL p, hIdx1Eq, hHas1Eq]
  have hSuppHAFlipIn : SupportedOn (fun γ ↦ (∀ b : Fin 24, γ (rHA rn b) = 0) ∧ (γ (rHas1 rn) = 0 →
      idxValD (rIdx1 rn) γ = 0) ∧ (∀ p : Fin 47, γ (rCtrlLo rn p) = if idxValD (rIdx1 rn) γ =
      p.val then γ (rHas1 rn) else 0)) (ULo.1 * (uKin.1 * R_sw)) := by
    refine supportedOn_uOneHotToggle (rHas1 rn) (rIdx1 rn)
        (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out (fun α ⟨hHA0, ⟨hLo0, hLt, hZ1⟩, hCL⟩ ↦
        ?_) hLoKin
    let γ := toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) α
    have hOth : ∀ {w : Wire n}, (∀ j : Fin 48, w ≠ wOutLoN48 rn j) → γ w = α w :=
      fun h ↦ toggleOneHotBits_apply_other α h
    obtain ⟨hHas1γ, hIdx1γ, _⟩ := pubCtrl_eq (δ₁ := γ) (δ₂ := α) (by
      rintro _ ⟨u, _, rfl⟩
      exact hOth (wOutLoN48_mem (S := fun v ↦ rn u ≠ v) rn
        (fun p ↦ rr_ne rn (by have := p.isLt; dsimp [rCtrlLo]; rw [hbp]; omega))
        (rr_ne rn (by dsimp; omega))))
    refine ⟨fun b ↦ (hOth (wOutLoN48_mem (S := fun v ↦ rHA rn b ≠ v) rn
      (fun p ↦ rr_ne rn (by have := b.isLt; have := p.isLt; dsimp [rHA, rCtrlLo]; rw [hbp]; omega))
      (rr_ne rn (by have := b.isLt; dsimp [rHA]; omega)))).trans (hHA0 b),
      fun hz ↦ hIdx1γ.trans (hZ1 (hHas1γ.symm.trans hz)),
      fun p ↦ ?_⟩
    have hp48 : wOutLoN48 rn ⟨p.val, Nat.lt_trans p.isLt (by omega)⟩ = rCtrlLo rn p :=
      padWires_cast (by omega) (rCtrlLo rn) (padLoN48 rn) p
    change γ (rCtrlLo rn p) = if idxValD (rIdx1 rn) γ = p.val then γ (rHas1 rn) else 0
    rw [hIdx1γ, hHas1γ, ← hp48]; dsimp only [γ]
    rw [toggleOneHotBits_apply_out dLo.out_inj hLo0 (Nat.lt_trans hLt (by omega))]
  have sPiece3 : SubspaceStep (Var := Var)
      ((uBellLoCopyHiAlwaysLoConj rn).1 * (ULo.1 * (uKin.1 * R_sw)))
      (ULo.1 * (uCopyLoHiAlwaysLoMat rn * (uKin.1 * R_sw)))
      (pHACollapseFlipLo0_24Dyn v rn) :=
    subspaceStep_congr_out
      (subspaceStep_pHACollapseFlipLo0_24Dyn v rn hSuppHAFlipIn)
      (by rw [← Matrix.mul_assoc, ← uLoToggle_comm_uCopyLoHiAlwaysLoMat_nuc rn, Matrix.mul_assoc])
  have hLoIn : SupportedOn (ValidWRouterInLo47 (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn)
      (qEncNuc rn)) R := fun A B hAB ↦ hRn A B fun β hβ ↦
      hAB β (validWRouterBase_nuc8886 rn hβ).2.2.1
  have hLoOut : SupportedOn (ValidWRouterCleanLo47 (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn))
      (uCopyLoHiAlwaysLoMat rn * (uKin.1 * R_sw)) :=
    supportedOn_uCopyLoHiAlwaysLoMat_of_not_sys rn
      (fun b p α val hα ↦ validWRouterCleanLo47_loN48_inv rn
        (swapModSet_sub_allPlaneMod rn (Or.inr (Or.inr ⟨b, p, rfl⟩))) α val hα)
      (uKin.1 * R_sw) (fun A B hAB ↦ hLoKin A B fun α hα ↦ hAB α hα.2.1)
  have sOuter :=
      subspaceStep_wrapWRouterLo47 v (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn)
      (qEncNuc rn) dLo _ R (uCopyLoHiAlwaysLoMat rn *
      (uKin.1 * R_sw)) hLoIn hLoOut (sPiece1.seq (sPiece2.seq sPiece3))
  have hSwWnh₀ : R_sw = (uZeroSwapNE rTot).1 * (Wnh.1 * X₁) := by
    dsimp only [R_sw, R]; rw [hSwEq0]
    exact cSwEq.trans (congrArg ((uZeroSwapNE rTot).1 * ·) cEq₁)
  have sCore : SubspaceStep (Var := Var) R
      (uCopyLoHiAlwaysLoMat rN * ((uZeroSwapNE rTot).1 * (uKin.1 * (Wnh.1 * X₁))))
      (pNucKinOnlineHBW294 v rTot isCsel) :=
    subspaceStep_congr_out sOuter (by
      rw [uCopyLoHiAlwaysLoMat_congr_of_samePubPriv hSPP, hSwWnh₀,
          uKin_mul_uZeroSwapNE_wnh_wstate o1 rTot isCsel X₁ hAbsX₁])
  exact subspaceStep_mul_left_of_commutesWithDyn (uBellLoCopyHiAlwaysLoConj rE)
      (commutesWithDyn_uBellLoCopyHiAlwaysLoConj_pNucKinOnlineHBW294 v rTot isCsel) sCore
end QuantumComputation.Specs.PhotochemistrySolution.Stage2NucKinW294
end

noncomputable section
set_option exponentiation.threshold 256
open scoped Circuit.Notation
section Stage5PreEqDirectLocal
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage5W298
open Operator QProg Matrix HermitianMat Circuit Qubit PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.PortBDualBellUnld
open PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.WStateStage5Unload
  PhotochemistrySolution.WStateWalkSeam PhotochemistrySolution.RouterAlwaysLoW338
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.AlwaysLoNuc8886W338
open PhotochemistrySolution.ParityCheckW309
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
abbrev IsOptCtrl {M : ℕ} (cV : Fin M → ZMod 2) (o : Option (Fin M)) : Prop :=
  ∀ p : Fin M, cV p = if some p = o then 1 else 0

abbrev hiOpt {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n)
    (hLt : idxValD (rIdx2 r) β < M) : Option (Fin M) :=
  if β (rRawHas2 r) = 1 then some ⟨idxValD (rIdx2 r) β, hLt⟩ else none

abbrev appendOpt {M₁ M₂ : ℕ} (o₁ : Option (Fin M₁)) (o₂ : Option (Fin M₂)) :
    Option (Fin (M₁ + M₂)) :=
  match o₁ with
  | some p => some (Fin.castAdd M₂ p)
  | none => o₂.map (Fin.natAdd M₁)

/-- Update a 24-wire slice `qB` to `v` on `α : BitAssignment n`. -/
def set24 {n : ℕ} (qB : Fin 24 → Wire n) (v : Fin 24 → ZMod 2)
    (α : BitAssignment n) : BitAssignment n :=
  fun u ↦ if h : ∃ b : Fin 24, u = qB b then v h.choose else α u

abbrev optSet24 {M n : ℕ} (wT : Fin M → Fin 24 → Wire n) (o : Option (Fin M))
    (v : Fin 24 → ZMod 2) (α : BitAssignment n) : BitAssignment n :=
  match o with
  | none => α
  | some p => set24 (wT p) v α

theorem set24_self {n : ℕ} {qB : Fin 24 → Wire n} (hqI : Function.Injective qB)
    (v : Fin 24 → ZMod 2) (α : BitAssignment n) (b : Fin 24) :
    set24 qB v α (qB b) = v b := by
  dsimp only [set24]
  rw [_root_.dite_eq_left ⟨b, rfl⟩]
  exact congrArg v (hqI (Exists.choose_spec (⟨b, rfl⟩ : ∃ k, qB b = qB k)).symm)

theorem set24_of_ne {n : ℕ} {qB : Fin 24 → Wire n} {v : Fin 24 → ZMod 2}
    {α : BitAssignment n} {u : Wire n} (h : ∀ b, u ≠ qB b) : set24 qB v α u = α u :=
  _root_.dite_eq_right (fun ⟨b, e⟩ ↦ h b e)

theorem set24_comm {n : ℕ} {qA qB : Fin 24 → Wire n} (h : ∀ j k, qA j ≠ qB k)
    (v w : Fin 24 → ZMod 2) (α : BitAssignment n) :
    set24 qA v (set24 qB w α) = set24 qB w (set24 qA v α) := by
  funext u
  by_cases hA : ∃ j, u = qA j
  · obtain ⟨j, rfl⟩ := hA
    dsimp only [set24]
    rw [_root_.dite_eq_left ⟨j, rfl⟩, _root_.dite_eq_right (fun ⟨k, e⟩ ↦ h j k e),
        _root_.dite_eq_left ⟨j, rfl⟩]
  · by_cases hB : ∃ k, u = qB k
    · obtain ⟨k, rfl⟩ := hB
      rw [set24_of_ne (fun j e ↦ hA ⟨j, e⟩)]
      dsimp only [set24]
      rw [_root_.dite_eq_left ⟨k, rfl⟩, _root_.dite_eq_left ⟨k, rfl⟩]
    · simp only [set24_of_ne (fun j e ↦ hA ⟨j, e⟩), set24_of_ne (fun k e ↦ hB ⟨k, e⟩)]

theorem optSet24_comm_set24 {M n : ℕ} {wT : Fin M → Fin 24 → Wire n} {o : Option (Fin M)}
    {qB : Fin 24 → Wire n} (h : ∀ p, o = some p → ∀ j k, wT p j ≠ qB k)
    (v w : Fin 24 → ZMod 2) (α : BitAssignment n) :
    optSet24 wT o v (set24 qB w α) = set24 qB w (optSet24 wT o v α) := by
  cases o with
  | none => rfl
  | some p => exact set24_comm (h p rfl) v w α

theorem optSet24_of_ne {M n : ℕ} {wT : Fin M → Fin 24 → Wire n} {o : Option (Fin M)}
    {v : Fin 24 → ZMod 2} {α : BitAssignment n} {u : Wire n}
    (h : ∀ p, o = some p → ∀ b, u ≠ wT p b) : optSet24 wT o v α u = α u := by
  cases o with
  | none => rfl
  | some p => exact set24_of_ne (h p rfl)

theorem add_fin_lt {k a c : ℕ} (i : Fin k) (h : a + k ≤ c) : a + i.val < c :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt a) h

theorem mul24_add_lt {M a c : ℕ} (p : Fin M) (b : Fin 24) (h : a + 24 * M ≤ c) :
    a + 24 * p.val + b.val < c := by
  have hp := p.isLt
  have hb := b.isLt
  omega

theorem fixedBellVecCirc_congr_stage5 {M m n : ℕ} {q₁ q₂ : Fin m → Wire n} (hq : q₁ = q₂)
    (cV : Fin M → ZMod 2) {w₁ w₂ : Fin m → Fin M → Wire n} (hw : w₁ = w₂)
    (h₁ : ∀ k p, q₁ k ≠ w₁ k p) (h₂ : ∀ k p, q₂ k ≠ w₂ k p) :
    fixedBellVecCirc M m q₁ cV w₁ h₁ = fixedBellVecCirc M m q₂ cV w₂ h₂ := by
  subst hq
  subst hw
  rfl

theorem swap24_zeroBuf_eq {n : ℕ} {qB wT : Fin 24 → Wire n}
    (hqI : Function.Injective qB) (htI : Function.Injective wT)
    (hbt : ∀ j k, qB j ≠ wT k) (α : BitAssignment n) (hB0 : ∀ k, α (qB k) = 0) :
    swapVecBits 24 qB wT α = set24 wT (fun _ ↦ 0) (set24 qB (fun b ↦ α (wT b)) α) := by
  obtain ⟨sQ, sT, sO⟩ := swapVecBits_spec 24 qB wT hqI htI hbt α
  funext u
  by_cases hT : ∃ b, u = wT b
  · obtain ⟨b, rfl⟩ := hT
    exact ((sT b).trans (hB0 b)).trans (set24_self htI (fun _ ↦ 0) _ b).symm
  · rw [set24_of_ne (fun b e ↦ hT ⟨b, e⟩)]
    by_cases hQ : ∃ b, u = qB b
    · obtain ⟨b, rfl⟩ := hQ
      exact (sQ b).trans (set24_self hqI (fun k ↦ α (wT k)) α b).symm
    · exact (sO u (fun b e ↦ hQ ⟨b, e⟩) (fun b e ↦ hT ⟨b, e⟩)).trans
        (set24_of_ne (fun b e ↦ hQ ⟨b, e⟩)).symm

theorem fixedFanoutBits_oneHot_stage5 {n : ℕ} :
    ∀ (M : ℕ) (s : ZMod 2) (cV : Fin M → ZMod 2) (wT : Fin M → Wire n)
      (p₀ : Fin M) (β : BitAssignment n),
      (∀ p : Fin M, cV p = if p = p₀ then 1 else 0) →
      fixedFanoutBits M s cV wT β = Function.update β (wT p₀) (β (wT p₀) + s)
  | 0, _, _, _, p₀, _, _ => Fin.elim0 p₀
  | M + 1, s, cV, wT, p₀, β, hc => by
      dsimp only [fixedFanoutBits]
      by_cases hp : p₀ = Fin.last M
      · subst hp
        rw [fixedFanoutBits_zero_ctrl M s (fun p ↦ cV p.castSucc) (fun p ↦ wT p.castSucc) β
              (fun p ↦ (hc p.castSucc).trans (ite_eq_right (Fin.castSucc_lt_last p).ne)),
            hc (Fin.last M)]
        simp
      · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hp
        rw [hc (Fin.last M), ite_eq_right (Fin.castSucc_lt_last j).ne.symm,
            ite_eq_right zero_ne_one]
        exact fixedFanoutBits_oneHot_stage5 M s (fun p ↦ cV p.castSucc) (fun p ↦ wT p.castSucc)
          j β (fun p ↦ (hc p.castSucc).trans (by simp [Fin.castSucc_inj]))

theorem copyVecAuxBits_oneHot_stage5 {M n : ℕ} (qB : Fin 24 → Wire n) (cV : Fin M → ZMod 2)
    (wT : Fin 24 → Fin M → Wire n) (p₀ : Fin M) (hc : ∀ p, cV p = if p = p₀ then 1 else 0)
    (htI : Function.Injective (fun k : Fin 24 ↦ wT k p₀))
    (hbt : ∀ j k : Fin 24, qB j ≠ wT k p₀) (β : BitAssignment n) :
    (∀ k : Fin 24,
      copyVecAuxBits_wstate qB cV wT 24 le_rfl β (wT k p₀) = β (wT k p₀) + β (qB k)) ∧
    (∀ w : Wire n, (∀ k : Fin 24, w ≠ wT k p₀) →
      copyVecAuxBits_wstate qB cV wT 24 le_rfl β w = β w) := by
  suffices h : ∀ (m : ℕ) (hm : m ≤ 24),
      (∀ k : Fin 24, k.val < m →
        copyVecAuxBits_wstate qB cV wT m hm β (wT k p₀) = β (wT k p₀) + β (qB k)) ∧
      (∀ w : Wire n, (∀ k : Fin 24, k.val < m → w ≠ wT k p₀) →
        copyVecAuxBits_wstate qB cV wT m hm β w = β w) by
    exact ⟨fun k ↦ (h 24 le_rfl).1 k k.isLt, fun w hw ↦ (h 24 le_rfl).2 w (fun k _ ↦ hw k)⟩
  intro m
  induction m with
  | zero => exact fun _ ↦ ⟨fun _ hk ↦ absurd hk (Nat.not_lt_zero _), fun _ _ ↦ rfl⟩
  | succ m ih =>
      intro hm
      obtain ⟨hT, hO⟩ := ih (Nat.le_of_succ_le hm)
      let km : Fin 24 := ⟨m, hm⟩
      dsimp only [copyVecAuxBits_wstate]
      rw [fixedFanoutBits_oneHot_stage5 M _ cV (wT km) p₀ _ hc, hO (qB km) (fun k _ ↦ hbt km k),
          hO (wT km p₀) (fun k hk e ↦ Nat.ne_of_lt hk (congrArg Fin.val (htI e)).symm)]
      refine ⟨fun k hk ↦ ?_, fun w hw ↦ ?_⟩
      · by_cases hkm : k = km
        · subst hkm
          exact Function.update_self _ _ _
        · rw [Function.update_of_ne (fun e ↦ hkm (htI e))]
          exact hT k (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk) (fun e ↦ hkm (Fin.ext e)))
      · rw [Function.update_of_ne (hw km (Nat.lt_succ_self m))]
        exact hO w (fun k hk ↦ hw k (Nat.lt_succ_of_lt hk))

theorem copyVecAuxBits_zero_stage5 {M n : ℕ} (qB : Fin 24 → Wire n) (cV : Fin M → ZMod 2)
    (wT : Fin 24 → Fin M → Wire n) (hz : ∀ p, cV p = 0) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ 24), copyVecAuxBits_wstate qB cV wT m hm β = β
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [copyVecAuxBits_wstate]
      rw [copyVecAuxBits_zero_stage5 qB cV wT hz β m (Nat.le_of_succ_le hm)]
      exact fixedFanoutBits_zero_ctrl M _ cV (wT ⟨m, hm⟩) β hz

theorem copyRestore_peel {M n : ℕ} (qB : Fin 24 → Wire n) (cV : Fin M → ZMod 2)
    (wT : Fin M → Fin 24 → Wire n) (o : Option (Fin M)) (ξ : BitAssignment n)
    (hc : IsOptCtrl cV o) (htI : ∀ p, o = some p → Function.Injective (wT p))
    (hbt : ∀ p, o = some p → ∀ j k, qB j ≠ wT p k)
    (hB : ∀ p, o = some p → ∀ k, ξ (qB k) = ξ (wT p k)) :
    copyVecAuxBits_wstate qB cV (fun b p ↦ wT p b) 24 le_rfl
      (optSet24 wT o (fun _ ↦ 0) ξ) = ξ := by
  cases o with
  | none =>
      exact copyVecAuxBits_zero_stage5 qB cV _ (fun p ↦ (hc p).trans (by simp)) ξ 24 le_rfl
  | some p₀ =>
      obtain ⟨cT, cO⟩ := copyVecAuxBits_oneHot_stage5 qB cV (fun b p ↦ wT p b) p₀
        (fun p ↦ (hc p).trans (by simp)) (htI p₀ rfl) (hbt p₀ rfl) (set24 (wT p₀) (fun _ ↦ 0) ξ)
      funext u
      by_cases hT : ∃ k, u = wT p₀ k
      · obtain ⟨k, rfl⟩ := hT
        rw [cT k, set24_self (htI p₀ rfl), set24_of_ne (hbt p₀ rfl k), zero_add, hB p₀ rfl k]
      · exact (cO u (fun k e ↦ hT ⟨k, e⟩)).trans (set24_of_ne (fun k e ↦ hT ⟨k, e⟩))

theorem optLoad24_eq_set24 {M n : ℕ} (qB : Fin 24 → Wire n) (cV : Fin M → ZMod 2)
    (wT : Fin 24 → Fin M → Wire n) (hbt : ∀ k p, qB k ≠ wT k p) (hqI : Function.Injective qB)
    (o : Option (Fin M)) (htI : ∀ p, o = some p → Function.Injective (fun k ↦ wT k p))
    (hbt2 : ∀ p, o = some p → ∀ j k, qB j ≠ wT k p)
    (hc : IsOptCtrl cV o) (α : BitAssignment n) (hB0 : ∀ k, α (qB k) = 0) :
    (Circuit.seq (fixedSwapVecCirc M 24 qB cV wT hbt)
      (fixedFanoutVecCirc M 24 qB cV wT hbt)).eval.1.mulVec (ket α) =
      ket (set24 qB (fun k ↦ (o.map (fun p ↦ α (wT k p))).getD 0) α) := by
  cases o with
  | none =>
      have hz : ∀ p, cV p = 0 := fun p ↦ (hc p).trans (by simp)
      rw [DynCircExt.eval_seq_mulVec, fixedSwapVecCirc_zero_ket_ul 24 qB cV wT hbt α hz,
          fixedFanoutVecCirc_24_mulVec_ket_wstate qB cV wT hbt,
          copyVecAuxBits_zero_stage5 qB cV wT hz α 24 le_rfl]
      exact congrArg ket (funext fun u ↦ by
        by_cases h : ∃ b, u = qB b
        · obtain ⟨b, rfl⟩ := h
          exact (hB0 b).trans
            (set24_self hqI (fun k ↦ (Option.map (fun p ↦ α (wT k p)) none).getD 0) α b).symm
        · exact (set24_of_ne (fun b e ↦ h ⟨b, e⟩)).symm)
  | some p₀ =>
      rw [DynCircExt.eval_seq_mulVec,
          fixedSwapVecCirc_oneHot_ket_ul 24 qB cV wT hbt p₀ α (fun p ↦ (hc p).trans (by simp)),
          fixedFanoutVecCirc_24_mulVec_ket_wstate qB cV wT hbt,
          swap24_zeroBuf_eq hqI (htI p₀ rfl) (hbt2 p₀ rfl) α hB0]
      exact congrArg ket (copyRestore_peel qB cV (fun p k ↦ wT k p) (some p₀) _ hc htI hbt2
        (fun p hp k ↦ by
          cases hp
          exact (set24_self hqI _ _ k).trans
            (set24_of_ne (fun j e ↦ hbt2 p₀ rfl j k e.symm)).symm))

theorem rWire_inj {M D n : ℕ} (r : RouterReg M D n) {f : Fin 24 → Fin (routerWidth M D)}
    (hf : ∀ a b, (f a).val = (f b).val → a.val = b.val) :
    Function.Injective (fun b ↦ r (f b)) :=
  fun a b e ↦ Fin.ext (hf a b (congrArg Fin.val (r.wires.injective e)))

theorem rBufLo_inj_s5 {M D n : ℕ} (r : RouterReg M D n) : Function.Injective (rBufLo r) :=
  rWire_inj r (fun _ _ h ↦ Nat.add_left_cancel h)

theorem rBufHi_inj_s5 {M D n : ℕ} (r : RouterReg M D n) : Function.Injective (rBufHi r) :=
  rWire_inj r (fun _ _ h ↦ Nat.add_left_cancel h)

theorem rSys_inj_s5 {M D n : ℕ} (r : RouterReg M D n) (p : Fin M) :
    Function.Injective (fun k : Fin 24 ↦ rSys r p k) :=
  rWire_inj r (fun _ _ h ↦ Nat.add_left_cancel h)

theorem rBufLo_ne_rBufHi_s5 {M D n : ℕ} (r : RouterReg M D n) (a b : Fin 24) :
    rBufLo r a ≠ rBufHi r b :=
  rr_ne r (by
    dsimp [rBufLo, rBufHi]
    omega)

theorem rBufLo_ne_rSys_s5 {M D n : ℕ} (r : RouterReg M D n) (a b : Fin 24) (p : Fin M) :
    rBufLo r a ≠ rSys r p b :=
  rr_ne r (by
    dsimp [rBufLo, rSys]
    omega)

theorem rBufHi_ne_rSys_s5 {M D n : ℕ} (r : RouterReg M D n) (a b : Fin 24) (p : Fin M) :
    rBufHi r a ≠ rSys r p b :=
  rr_ne r (by
    dsimp [rBufHi, rSys]
    omega)

theorem rSys_ne_of_ne_s5 {M D n : ℕ} (r : RouterReg M D n) {p₁ p₂ : Fin M}
    (hp : p₁ ≠ p₂) (a b : Fin 24) : rSys r p₁ a ≠ rSys r p₂ b := fun e ↦ by
  have hv := congrArg Fin.val (r.wires.injective e)
  dsimp [rSys] at hv
  exact hp (Fin.ext (by omega))

theorem cLoAlways_opt {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n)
    (hLt : idxValD (rIdx1 r) β < M) :
    IsOptCtrl (cLoAlways r β) (some ⟨idxValD (rIdx1 r) β, hLt⟩) := fun p ↦ by
  dsimp only [cLoAlways]
  by_cases hp : p = ⟨idxValD (rIdx1 r) β, hLt⟩
  · subst hp
    simp
  · rw [ite_eq_right (fun e ↦ hp (Fin.ext e)), ite_eq_right (by simp [hp])]

theorem cOfSortedHi_opt {M D n : ℕ} (r : RouterReg M D n) {β : BitAssignment n}
    {cV : Fin M → ZMod 2} (hc : cOfSortedHi r β = cV) (hLt : idxValD (rIdx2 r) β < M) :
    IsOptCtrl cV (hiOpt r β hLt) := fun p ↦ by
  rw [← congrFun hc p]
  dsimp only [cOfSortedHi, hiOpt]
  rcases DynCircExt.bit_cases (β (rRawHas2 r)) with h0 | h1
  · simp [h0]
  · by_cases hp : p = ⟨idxValD (rIdx2 r) β, hLt⟩
    · subst hp
      simp [h1]
    · have hpv : idxValD (rIdx2 r) β ≠ p.val := fun e ↦ hp (Fin.ext e.symm)
      simp [h1, hp, hpv]

theorem isOptCtrl_appendFin {M₁ M₂ : ℕ} {c₁ : Fin M₁ → ZMod 2} {c₂ : Fin M₂ → ZMod 2}
    {o₁ : Option (Fin M₁)} {o₂ : Option (Fin M₂)}
    (hc₁ : IsOptCtrl c₁ o₁) (hc₂ : IsOptCtrl c₂ o₂) (hEx : ∀ p, o₁ = some p → o₂ = none) :
    IsOptCtrl (appendFin c₁ c₂) (appendOpt o₁ o₂) := fun i ↦ by
  rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · rw [appendFin_castAdd, hc₁ p]
    cases o₁ with
    | none =>
        cases o₂ with
        | none => simp [appendOpt]
        | some q₀ =>
            rw [ite_eq_right (by simp)]
            exact (ite_eq_right (fun e ↦ Nat.ne_of_lt
              (Nat.lt_of_lt_of_le p.isLt (Nat.le_add_right M₁ q₀.val))
              (congrArg (Fin.val : Fin (M₁ + M₂) → ℕ) (Option.some.inj e)))).symm
    | some p₀ => simp [appendOpt, Fin.ext_iff]
  · rw [appendFin_natAdd, hc₂ q]
    cases o₁ with
    | none =>
        cases o₂ with
        | none => simp [appendOpt]
        | some q₀ => simp [appendOpt, Fin.ext_iff]
    | some p₀ =>
        rw [hEx p₀ rfl, ite_eq_right (by simp)]
        exact (ite_eq_right (fun e ↦ Nat.ne_of_gt
          (Nat.lt_of_lt_of_le p₀.isLt (Nat.le_add_right M₁ q.val))
          (congrArg (Fin.val : Fin (M₁ + M₂) → ℕ) (Option.some.inj e)))).symm

theorem unloadHiPred_two_s5 {M D n : ℕ} {r₁ r₂ : RouterReg M D n} {α β : BitAssignment n}
    (hRaw : α (rRawHas2 r₁) = β (rRawHas2 r₂))
    (hIdx : ∀ d : Fin D, α (rIdx2 r₁ d) = β (rIdx2 r₂ d))
    (hβ : UnloadHiPred r₂ β) : UnloadHiPred r₁ α :=
  ⟨(SplitRouter47_187.idxValD_congr hIdx).trans_lt hβ.1,
   fun hz ↦ (SplitRouter47_187.idxValD_congr hIdx).trans (hβ.2.1 (hRaw.symm.trans hz)),
   fun ho h0 ↦ hβ.2.2 (hRaw.symm.trans ho) ((SplitRouter47_187.idxValD_congr hIdx).symm.trans h0)⟩

theorem uRouterSwap_eq_set24 {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) (pLo : Fin M) (oHi : Option (Fin M)) (δ : BitAssignment n)
    (hcLoEq : cLoAlways r δ = cLo) (hcHiEq : routerCtrlHi r δ = cHi)
    (hcLo : IsOptCtrl cLo (some pLo)) (hcHi : IsOptCtrl cHi oHi)
    (hne : ∀ p, oHi = some p → p ≠ pLo)
    (hBL0 : ∀ b : Fin 24, δ (rBufLo r b) = 0) (hBH0 : ∀ b : Fin 24, δ (rBufHi r b) = 0) :
    (uRouterSwapAlwaysLoConj r).1.mulVec (ket δ) =
      ket (optSet24 (rSys r) oHi (fun _ ↦ 0) (set24 (rSys r pLo) (fun _ ↦ 0)
        (set24 (rBufHi r) (fun b ↦ (oHi.map (fun p ↦ δ (rSys r p b))).getD 0)
          (set24 (rBufLo r) (fun b ↦ δ (rSys r pLo b)) δ)))) := by
  rw [uRouterSwapAlwaysLoConj_mulVec_ket_any r δ, hcLoEq, hcHiEq]
  dsimp only [cFixedSwapCirc]
  rw [DynCircExt.eval_seq_mulVec,
      fixedSwapVecCirc_oneHot_ket_ul 24 (rBufLo r) cLo _ _ pLo δ (fun p ↦ (hcLo p).trans (by simp)),
      swap24_zeroBuf_eq (rBufLo_inj_s5 r) (rSys_inj_s5 r pLo)
        (fun j k ↦ rBufLo_ne_rSys_s5 r j k pLo) δ hBL0]
  let δ₁ := set24 (rSys r pLo) (fun _ ↦ 0) (set24 (rBufLo r) (fun b ↦ δ (rSys r pLo b)) δ)
  have hBH1 : ∀ b, δ₁ (rBufHi r b) = 0 := fun b ↦
    (set24_of_ne (fun k ↦ rBufHi_ne_rSys_s5 r b k pLo)).trans
      ((set24_of_ne (fun k ↦ (rBufLo_ne_rBufHi_s5 r k b).symm)).trans (hBH0 b))
  cases oHi with
  | none =>
      rw [fixedSwapVecCirc_zero_ket_ul 24 (rBufHi r) cHi _ _ δ₁
        (fun p ↦ (hcHi p).trans (by simp))]
      refine congrArg ket (congrArg (set24 (rSys r pLo) (fun _ ↦ 0)) (funext fun u ↦ ?_))
      by_cases h : ∃ b, u = rBufHi r b
      · obtain ⟨b, rfl⟩ := h
        exact ((set24_of_ne (fun k ↦ (rBufLo_ne_rBufHi_s5 r k b).symm)).trans (hBH0 b)).trans
          (set24_self (rBufHi_inj_s5 r)
            (fun k ↦ (Option.map (fun p ↦ δ (rSys r p k)) none).getD 0) _ b).symm
      · exact (set24_of_ne (fun b e ↦ h ⟨b, e⟩)).symm
  | some pHi =>
      rw [fixedSwapVecCirc_oneHot_ket_ul 24 (rBufHi r) cHi _ _ pHi δ₁
            (fun p ↦ (hcHi p).trans (by simp)),
          swap24_zeroBuf_eq (rBufHi_inj_s5 r) (rSys_inj_s5 r pHi)
            (fun j k ↦ rBufHi_ne_rSys_s5 r j k pHi) δ₁ hBH1]
      have hSH1 : (fun b ↦ δ₁ (rSys r pHi b)) = (fun b ↦ δ (rSys r pHi b)) := funext fun b ↦
        (set24_of_ne (fun k ↦ rSys_ne_of_ne_s5 r (hne pHi rfl) b k)).trans
          (set24_of_ne (fun k ↦ (rBufLo_ne_rSys_s5 r k b pHi).symm))
      rw [hSH1, set24_comm (fun j k ↦ rBufHi_ne_rSys_s5 r j k pLo)]
      rfl

abbrev idxBufLoN (b : Fin 24) : Fin (routerWidth 47 6) := ⟨14 + b.val, add_fin_lt b (by decide)⟩
abbrev idxBufHiN (b : Fin 24) : Fin (routerWidth 47 6) := ⟨38 + b.val, add_fin_lt b (by decide)⟩
abbrev idxSysN (p : Fin 47) (b : Fin 24) : Fin (routerWidth 47 6) :=
  ⟨110 + 24 * p.val + b.val, mul24_add_lt p b (by decide)⟩
abbrev idxBufLoE (b : Fin 24) : Fin (routerWidth 187 8) := ⟨18 + b.val, add_fin_lt b (by decide)⟩
abbrev idxBufHiE (b : Fin 24) : Fin (routerWidth 187 8) := ⟨42 + b.val, add_fin_lt b (by decide)⟩
abbrev idxSysE (q : Fin 187) (b : Fin 24) : Fin (routerWidth 187 8) :=
  ⟨114 + 24 * q.val + b.val, mul24_add_lt q b (by decide)⟩

theorem layout_mid_ne_nucMod {n : ℕ} (rTot : QRegister dLayout n) {wt : Wire dLayout}
    (hlo : 5715 ≤ wt.val) (hhi : wt.val < 5755) {i : Fin (routerWidth 47 6)}
    (h1 : 14 ≤ i.val) (h2 : i.val < 1238) :
    rTot wt ≠ (rTot.compose rNucSub) i := fun e ↦ by
  have hpub := validMuxD1Stage2Regs_sub.pubNuc i h2
  have hv := congrArg Fin.val (rTot.wires.injective (e.trans (congrArg rTot.wires hpub)))
  rw [val_rNucLayout_eq, val_nucRouterWireFn] at hv
  split_ifs at hv <;> omega

theorem layout_mid_ne_elecMod {n : ℕ} (rTot : QRegister dLayout n) {wt : Wire dLayout}
    (hlo : 5715 ≤ wt.val) (hhi : wt.val < 5755) {k : Fin (routerWidth 187 8)}
    (h1 : 18 ≤ k.val) (h2 : k.val < 4602) :
    rTot wt ≠ (rTot.compose rElecSub) k := fun e ↦ by
  have hpub := validMuxD1Stage2Regs_sub.pubElec k h2
  have hv := congrArg Fin.val (rTot.wires.injective (e.trans (congrArg rTot.wires hpub)))
  rw [val_rElecLayout_eq, val_elecRouterWireFn] at hv
  split_ifs at hv <;> omega

/-- Direct `BitAssignment` ket equality for Stage-5 `hPreEq`. -/
theorem stage5AlwaysLo_preEq_ket_gen {n : ℕ}
    (rTot : QRegister dLayout n) (rE_Lo rE235 : RouterReg 187 8 n)
    (w235 : SharedPortBWiring (rTot.compose rNucSub) rE235 (fun p ↦ rTot (cHiNSub341 p)))
    (hPubLo : ∀ {j : Fin (routerWidth 187 8)},
      (j.val < 97 ∨ (114 ≤ j.val ∧ j.val < 4602)) → rE_Lo j = (rTot.compose rElecSub) j)
    (hPub235 : ∀ {j : Fin (routerWidth 187 8)},
      (j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 4602)) → rE235 j = (rTot.compose rElecSub) j)
    {β : BitAssignment n}
    (hβ : SharedPortBInput341 rTot (rTot.compose rNucSub) (rTot.compose rElecSub) β)
    (hc235_0 : ∀ q : Fin 187, β (rCtrlLo rE235 q) = 0)
    (hc235_ne : ∀ (q : Fin 187) (b : Fin 24),
      rCtrlLo rE235 q ≠ rBufLo (rTot.compose rNucSub) b)
    (hcLo_0 : ∀ q : Fin 187, β (rCtrlLo rE_Lo q) = 0)
    (hcLo_ne : ∀ (q : Fin 187) (b : Fin 24),
      rCtrlLo rE_Lo q ≠ rBufLo (rTot.compose rNucSub) b ∧
      rCtrlLo rE_Lo q ≠ rBufHi (rTot.compose rElecSub) b) :
    let rN := rTot.compose rNucSub
    let rE := rTot.compose rElecSub
    let cHiN := fun p ↦ rTot (cHiNSub341 p)
    (uLoEAlways1Conj rE_Lo).mulVec
      ((uSharedHiPortOnlyConj rN rE235 cHiN w235).mulVec
        ((uLoNPortOnlyAlways1Conj rN).mulVec (PhotochemistrySolution.XMeasUnld.ket β))) =
    (uBellLoEAlwaysLoMux_wstate rTot).1.mulVec
      ((uSwapHi24 rTot).1.mulVec
        ((uCopyAll3AlwaysLoMux_wstate rTot).1.mulVec
          ((uRouterSwapAlwaysLoConj rN).1.mulVec
            ((uRouterSwapAlwaysLoConj rE).1.mulVec
              (PhotochemistrySolution.XMeasUnld.ket β))))) := by
  intro rN rE cHiN
  have hRegs := validMuxD1Stage2Regs_sub
  let w := SharedPortBWiring.ofValidMuxD1_341 hRegs
    cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub rTot
  obtain ⟨_, hPLoE, hPHiE, _, hcHiEEq⟩ := facts_of_zeroGatedSorted (by decide) rE hβ.1
  obtain ⟨hC0N, hPLoN, hPHiN, _, hcHiNEq⟩ := facts_of_zeroGatedSorted (by decide) rN hβ.2.1
  let pLoN : Fin 47 := ⟨idxValD (rIdx1 rN) β, hPLoN.1⟩
  let qLoE : Fin 187 := ⟨idxValD (rIdx1 rE) β, hPLoE.1⟩
  let oHiN := hiOpt rN β hPHiN.1
  let oHiE := hiOpt rE β hPHiE.1
  let oHiNE := appendOpt oHiN oHiE
  let cLoN := cLoAlways rN β
  let cHiNVec := routerCtrlHi rN β
  let cLoE := cLoAlways rE β
  let cHiE := routerCtrlHi rE β
  have hcLoN : IsOptCtrl cLoN (some pLoN) := cLoAlways_opt rN β hPLoN.1
  have hcLoE : IsOptCtrl cLoE (some qLoE) := cLoAlways_opt rE β hPLoE.1
  have hcHiN : IsOptCtrl cHiNVec oHiN := cOfSortedHi_opt rN hcHiNEq hPHiN.1
  have hcHiE : IsOptCtrl cHiE oHiE := cOfSortedHi_opt rE hcHiEEq hPHiE.1
  have hExHi : ∀ p, oHiN = some p → oHiE = none := fun p hp ↦ by
    dsimp only [oHiN, oHiE, hiOpt] at hp ⊢
    by_cases hRN : β (rRawHas2 rN) = 1
    · exact ite_eq_right ((hβ.2.2.2.2 hRN).trans_ne zero_ne_one)
    · rw [ite_eq_right hRN] at hp
      cases hp
  have hBLN0 : ∀ b, β (rBufLo rN b) = 0 := fun b ↦ (hβ.2.1.1.2.2.2.1 b).1
  have hBHN0 : ∀ b, β (rBufHi rN b) = 0 := fun b ↦ (hβ.2.1.1.2.2.2.1 b).2.1
  have hBLE0 : ∀ b, β (rBufLo rE b) = 0 := fun b ↦ (hβ.1.1.2.2.2.1 b).1
  have hBHE0 : ∀ b, β (rBufHi rE b) = 0 := fun b ↦ (hβ.1.1.2.2.2.1 b).2.1
  have hBN_lt : ∀ b, (idxBufLoN b).val < 1238 ∧ (idxBufHiN b).val < 1238 :=
    fun b ↦ ⟨add_fin_lt b (by decide), add_fin_lt b (by decide)⟩
  have hBE_lt : ∀ b, (idxBufLoE b).val < 4602 ∧ (idxBufHiE b).val < 4602 :=
    fun b ↦ ⟨add_fin_lt b (by decide), add_fin_lt b (by decide)⟩
  have hSN_lt : ∀ p b, (idxSysN p b).val < 1238 := fun p b ↦ mul24_add_lt p b (by decide)
  have hSE_lt : ∀ q b, (idxSysE q b).val < 4602 := fun q b ↦ mul24_add_lt q b (by decide)
  have hMidN {wt : Wire dLayout} (hlo : 5715 ≤ wt.val) (hhi : wt.val < 5755) :
      (∀ b, rTot wt ≠ rBufLo rN b) ∧ (∀ b, rTot wt ≠ rBufHi rN b) ∧
      (∀ p b, rTot wt ≠ rSys rN p b) :=
    ⟨fun b ↦ layout_mid_ne_nucMod rTot hlo hhi (Nat.le_add_right 14 _) (hBN_lt b).1,
     fun b ↦ layout_mid_ne_nucMod rTot hlo hhi
       (Nat.le_trans (by decide) (Nat.le_add_right 38 _)) (hBN_lt b).2,
     fun p b ↦ layout_mid_ne_nucMod rTot hlo hhi
       (Nat.le_trans (by decide) (Nat.le_trans (Nat.le_add_right 110 _) (Nat.le_add_right _ _)))
       (hSN_lt p b)⟩
  have hMidE {wt : Wire dLayout} (hlo : 5715 ≤ wt.val) (hhi : wt.val < 5755) :
      (∀ b, rTot wt ≠ rBufLo rE b) ∧ (∀ b, rTot wt ≠ rBufHi rE b) ∧
      (∀ q b, rTot wt ≠ rSys rE q b) :=
    ⟨fun b ↦ layout_mid_ne_elecMod rTot hlo hhi (Nat.le_add_right 18 _) (hBE_lt b).1,
     fun b ↦ layout_mid_ne_elecMod rTot hlo hhi
       (Nat.le_trans (by decide) (Nat.le_add_right 42 _)) (hBE_lt b).2,
     fun q b ↦ layout_mid_ne_elecMod rTot hlo hhi
       (Nat.le_trans (by decide) (Nat.le_trans (Nat.le_add_right 114 _) (Nat.le_add_right _ _)))
       (hSE_lt q b)⟩
  let vLoN := fun b ↦ β (rSys rN pLoN b)
  let vLoE := fun b ↦ β (rSys rE qLoE b)
  let vHiN := fun b ↦ (oHiN.map (fun p ↦ β (rSys rN p b))).getD 0
  let vHiE := fun b ↦ (oHiE.map (fun q ↦ β (rSys rE q b))).getD 0
  let wSysNE : Fin 24 → Fin (47 + 187) → Wire n :=
    fun b ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b)
  let β₁ := set24 (rBufLo rN) vLoN β
  have hL1 : (uLoNPortOnlyAlways1Conj rN).mulVec (XMeasUnld.ket β) = ket β₁ :=
    (uLoNPortOnlyAlways1Conj_mulVec_ket rN hC0N hPLoN).trans
      (optLoad24_eq_set24 (rBufLo rN) cLoN (fun b p ↦ rSys rN p b) (hne_fixed_router rN).1
        (rBufLo_inj_s5 rN) (some pLoN) (fun _ h ↦ Option.some.inj h ▸ rSys_inj_s5 rN pLoN)
        (fun _ h j k ↦ Option.some.inj h ▸ rBufLo_ne_rSys_s5 rN j k pLoN) hcLoN β hBLN0)
  have hβ₁_hdrN (i : Fin (routerWidth 47 6)) (hi : i.val < 14) : β₁ (rN i) = β (rN i) :=
    set24_of_ne fun b ↦ rr_ne rN (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi (Nat.le_add_right 14 b.val)))
  have hβ₁_rE (j : Fin (routerWidth 187 8)) (hj : j.val < 4602) : β₁ (rE j) = β (rE j) :=
    set24_of_ne fun b e ↦ w.pubN_ne_pubE (hBN_lt b).1 hj e.symm
  have hβ₁RawN : β₁ (rRawHas2 rN) = β (rRawHas2 rN) := hβ₁_hdrN ⟨1, rw_lt1 47 6⟩ (by decide)
  have hβ₁Idx2N (d : Fin 6) : β₁ (rIdx2 rN d) = β (rIdx2 rN d) :=
    hβ₁_hdrN ⟨2 + 6 + d.val, rw_ltIdx2 d⟩ (add_fin_lt (a := 8) d (by decide))
  have hβ₁_pub235 (j : Fin (routerWidth 187 8)) (hj : j.val < 18) : β₁ (rE235 j) = β (rE j) :=
    (congrArg β₁ (hPub235 (Or.inl hj))).trans (hβ₁_rE j (Nat.lt_trans hj (by decide)))
  have hβ₁RawE235 : β₁ (rRawHas2 rE235) = β (rRawHas2 rE) :=
    hβ₁_pub235 ⟨1, rw_lt1 187 8⟩ (by decide)
  have hβ₁Idx2E235 (d : Fin 8) : β₁ (rIdx2 rE235 d) = β (rIdx2 rE d) :=
    hβ₁_pub235 ⟨2 + 8 + d.val, rw_ltIdx2 d⟩ (add_fin_lt (a := 10) d (by decide))
  have hSys235Eq :
      (fun b : Fin 24 ↦ appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE235 q b)) = wSysNE :=
    funext fun b ↦ funext fun i ↦ by
      rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · simp [wSysNE, appendFin_castAdd]
      · simpa only [wSysNE, appendFin_natAdd] using hPub235 (j := idxSysE q b)
          (Or.inr ⟨Nat.le_trans (by decide)
            (Nat.le_trans (Nat.le_add_right 114 _) (Nat.le_add_right _ _)), hSE_lt q b⟩)
  let vHiNE := fun b ↦ (oHiNE.map (fun i ↦ β₁ (wSysNE b i))).getD 0
  let β₂ := set24 (rBufHi rE) vHiNE β₁
  have hL2 : (uSharedHiPortOnlyConj rN rE235 cHiN w235).mulVec (ket β₁) = ket β₂ := by
    have h0 := uSharedHiPortOnlyConj_mulVec_ket rN rE235 cHiN w235 (α := β₁)
      (fun p ↦ (set24_of_ne (fun b e ↦ w.cHiN_notModN p ⟨b, Or.inl e⟩)).trans (hβ.2.2.1 p))
      (fun q ↦ (set24_of_ne (hc235_ne q)).trans (hc235_0 q))
      (unloadHiPred_two_s5 hβ₁RawN hβ₁Idx2N hPHiN)
      (unloadHiPred_two_s5 hβ₁RawE235 hβ₁Idx2E235 hPHiE)
    have hcHiN₁ : cOfSortedHi rN β₁ = cHiNVec := (funext fun p ↦ by
      dsimp only [cOfSortedHi]
      rw [SplitRouter47_187.idxValD_congr hβ₁Idx2N, hβ₁RawN]).trans hcHiNEq
    have hcHiE₁ : cOfSortedHi rE235 β₁ = cHiE := (funext fun q ↦ by
      dsimp only [cOfSortedHi]
      rw [SplitRouter47_187.idxValD_congr hβ₁Idx2E235, hβ₁RawE235]).trans hcHiEEq
    have hBufHi235Eq : rBufHi rE235 = rBufHi rE := funext fun b ↦
      hPub235 (j := idxBufHiE b) (Or.inr ⟨Nat.le_add_right 42 _, (hBE_lt b).2⟩)
    rw [show ket β₁ = PhotochemistrySolution.XMeasUnld.ket β₁ from rfl, h0, hcHiN₁, hcHiE₁,
        fixedSwapVecCirc_congr_w310 hBufHi235Eq _ hSys235Eq _ w.hBTs_NE,
        fixedFanoutVecCirc_congr_w310 _ hBufHi235Eq hSys235Eq _ w.hBTs_NE]
    exact optLoad24_eq_set24 (rBufHi rE) (appendFin cHiNVec cHiE) wSysNE w.hBTs_NE
      (rBufHi_inj_s5 rE) oHiNE
      (fun i _ _ _ e ↦ by
        rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
        · exact rSys_inj_s5 rN p ((appendFin_castAdd _ _ p).symm.trans
            (e.trans (appendFin_castAdd _ _ p)))
        · exact rSys_inj_s5 rE q ((appendFin_natAdd _ _ q).symm.trans
            (e.trans (appendFin_natAdd _ _ q))))
      (fun i _ j k e ↦ by
        rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
        · exact w.pubN_ne_pubE (hSN_lt p k) (hBE_lt j).2 ((e.trans (appendFin_castAdd _ _ p)).symm)
        · exact rBufHi_ne_rSys_s5 rE j k q (e.trans (appendFin_natAdd _ _ q)))
      (isOptCtrl_appendFin hcHiN hcHiE hExHi) β₁
      (fun b ↦ (hβ₁_rE (idxBufHiE b) (hBE_lt b).2).trans (hBHE0 b))
  have hβ₂_hdrE (j : Fin (routerWidth 187 8)) (hj : j.val < 18) : β₂ (rE j) = β (rE j) :=
    (set24_of_ne fun b ↦ rr_ne rE (Nat.ne_of_lt
      (Nat.lt_of_lt_of_le hj (Nat.le_trans (by decide) (Nat.le_add_right 42 _))))).trans
      (hβ₁_rE j (by omega))
  have hβ₂Idx1Lo (d : Fin 8) : β₂ (rIdx1 rE_Lo d) = β (rIdx1 rE d) :=
    (congrArg β₂ (hPubLo (j := ⟨2 + d.val, rw_ltIdx1 d⟩)
      (Or.inl (add_fin_lt (a := 2) d (by decide))))).trans
      (hβ₂_hdrE ⟨2 + d.val, rw_ltIdx1 d⟩ (add_fin_lt (a := 2) d (by decide)))
  have hPLoE₂ : UnloadLoPred rE_Lo β₂ :=
    ⟨(SplitRouter47_187.idxValD_congr hβ₂Idx1Lo).trans_lt hPLoE.1,
     fun hz ↦ (SplitRouter47_187.idxValD_congr hβ₂Idx1Lo).trans (hPLoE.2
       (((congrArg β₂ (hPubLo (j := ⟨0, rw_lt0 187 8⟩) (Or.inl (by decide)))).trans
         (hβ₂_hdrE ⟨0, rw_lt0 187 8⟩ (by decide))).symm.trans hz))⟩
  have hcLoE₂ : cLoAlways rE_Lo β₂ = cLoE := funext fun q ↦ by
    dsimp only [cLoAlways, cLoE]
    rw [SplitRouter47_187.idxValD_congr hβ₂Idx1Lo]
  have hSysEqLo : (fun b q ↦ rSys rE_Lo q b) = (fun b q ↦ rSys rE q b) :=
    funext fun b ↦ funext fun q ↦ hPubLo (j := idxSysE q b)
      (Or.inr ⟨Nat.le_trans (Nat.le_add_right 114 _) (Nat.le_add_right _ _), hSE_lt q b⟩)
  let cBLoE := fixedBellVecCirc 187 24 (rHA rE) cLoE (fun b q ↦ rSys rE q b) (hne_hA_sys rE)
  let β₃ := set24 (rSys rE qLoE) (fun _ ↦ 0) (set24 (rBufLo rE) vLoE β₂)
  have hL3 : (uLoEAlways1Conj rE_Lo).mulVec (ket β₂) = cBLoE.eval.1.mulVec (ket β₃) := by
    have h0 := uLoEAlways1Conj_mulVec_ket rE_Lo (δ := β₂)
      (fun q ↦ ((set24_of_ne (fun b ↦ (hcLo_ne q b).2)).trans
        (set24_of_ne (fun b ↦ (hcLo_ne q b).1))).trans (hcLo_0 q)) hPLoE₂
    rw [show ket β₂ = PhotochemistrySolution.XMeasUnld.ket β₂ from rfl, h0, hcLoE₂]
    dsimp only [cFixedPortCirc]
    rw [fixedSwapVecCirc_congr_w310
          (funext fun b ↦ hPubLo (j := idxBufLoE b) (Or.inl (add_fin_lt (a := 18) b (by decide))))
          cLoE hSysEqLo _ (hne_fixed_router rE).1,
        fixedBellVecCirc_congr_stage5
          (funext fun b ↦ hPubLo (j := ⟨66 + b.val, rw_ltHA 187 8 b⟩)
            (Or.inl (add_fin_lt (a := 66) b (by decide))))
          cLoE hSysEqLo _ (hne_hA_sys rE),
        DynCircExt.eval_seq_mulVec,
        fixedSwapVecCirc_oneHot_ket_ul 24 (rBufLo rE) cLoE _ _ qLoE β₂
          (fun q ↦ (hcLoE q).trans (by simp)),
        swap24_zeroBuf_eq (rBufLo_inj_s5 rE) (rSys_inj_s5 rE qLoE)
          (fun j k ↦ rBufLo_ne_rSys_s5 rE j k qLoE) β₂
          (fun b ↦ (set24_of_ne (fun k ↦ rBufLo_ne_rBufHi_s5 rE b k)).trans
            ((hβ₁_rE (idxBufLoE b) (hBE_lt b).1).trans (hBLE0 b))),
        show (fun b ↦ β₂ (rSys rE qLoE b)) = vLoE from funext fun b ↦
          (set24_of_ne (fun k ↦ (rBufHi_ne_rSys_s5 rE k b qLoE).symm)).trans
            (hβ₁_rE (idxSysE qLoE b) (hSE_lt qLoE b))]
  have hHiOptNe {M D : ℕ} {rx : RouterReg M D n} {hLt : idxValD (rIdx2 rx) β < M}
      {pLo : Fin M} (hOrd : β (rRawHas2 rx) = 1 → pLo.val < idxValD (rIdx2 rx) β) :
      ∀ p, hiOpt rx β hLt = some p → p ≠ pLo := fun p hp e ↦ by
    dsimp only [hiOpt] at hp
    by_cases h1 : β (rRawHas2 rx) = 1
    · rw [ite_eq_left h1] at hp
      exact Nat.ne_of_lt (hOrd h1) (congrArg Fin.val ((Option.some.inj hp).trans e)).symm
    · rw [ite_eq_right h1] at hp
      cases hp
  have hHiENe : ∀ q, oHiE = some q → q ≠ qLoE := hHiOptNe hβ.1.2.2.2
  have hHiNNe : ∀ p, oHiN = some p → p ≠ pLoN := hHiOptNe hβ.2.1.2.2.2
  let ξE := set24 (rSys rE qLoE) (fun _ ↦ 0) (set24 (rBufHi rE) vHiE (set24 (rBufLo rE) vLoE β))
  let δ₂ := optSet24 (rSys rE) oHiE (fun _ ↦ 0) ξE
  have hR1 : (uRouterSwapAlwaysLoConj rE).1.mulVec (ket β) = ket δ₂ :=
    uRouterSwap_eq_set24 rE cLoE cHiE qLoE oHiE β rfl rfl hcLoE hcHiE hHiENe hBLE0 hBHE0
  have hξE_rN (i : Fin (routerWidth 47 6)) (hi : i.val < 1238) : ξE (rN i) = β (rN i) :=
    (set24_of_ne (fun b ↦ w.pubN_ne_pubE hi (hSE_lt qLoE b))).trans
      ((set24_of_ne (fun b ↦ w.pubN_ne_pubE hi (hBE_lt b).2)).trans
        (set24_of_ne (fun b ↦ w.pubN_ne_pubE hi (hBE_lt b).1)))
  have hd2_rN (i : Fin (routerWidth 47 6)) (hi : i.val < 1238) : δ₂ (rN i) = β (rN i) :=
    (optSet24_of_ne (fun q _ b ↦ w.pubN_ne_pubE hi (hSE_lt q b))).trans (hξE_rN i hi)
  have hd2_mid {wt : Wire dLayout} (hlo : 5715 ≤ wt.val) (hhi : wt.val < 5755) :
      δ₂ (rTot wt) = β (rTot wt) :=
    (optSet24_of_ne (fun q _ ↦ (hMidE hlo hhi).2.2 q)).trans
      ((set24_of_ne ((hMidE hlo hhi).2.2 qLoE)).trans
        ((set24_of_ne (hMidE hlo hhi).2.1).trans (set24_of_ne (hMidE hlo hhi).1)))
  have hcLoN_d2 : cLoAlways rN δ₂ = cLoN := funext fun p ↦ by
    dsimp only [cLoAlways, cLoN]
    rw [SplitRouter47_187.idxValD_congr
      (fun d ↦ hd2_rN ⟨2 + d.val, rw_ltIdx1 d⟩ (add_fin_lt (a := 2) d (by decide)))]
  have ctrl32_eq {δ : BitAssignment n}
      (hm : ∀ {wt : Wire dLayout}, 5715 ≤ wt.val → wt.val < 5755 → δ (rTot wt) = β (rTot wt)) :
      (fun j : Fin 32 ↦ δ ((rTot.compose rCtrl32Layout_wstate) j)) =
        fun j ↦ β ((rTot.compose rCtrl32Layout_wstate) j) := funext fun j ↦
    hm (wt := rCtrl32Layout_wstate j) (Nat.le_add_right 5715 j.val)
      (add_fin_lt (a := 5715) j (by decide))
  have hcHiN_d2 : routerCtrlHi rN δ₂ = cHiNVec := by
    rw [(routerCtrlPair_eq_ctrlBits32_wstate rTot δ₂).1.2, ctrl32_eq hd2_mid,
        ← (routerCtrlPair_eq_ctrlBits32_wstate rTot β).1.2]
  let ξ := set24 (rBufHi rN) vHiN (set24 (rBufLo rN) vLoN ξE)
  let ξ₂ := optSet24 (rSys rE) oHiE (fun _ ↦ 0) ξ
  let ξ₁ := set24 (rSys rN pLoN) (fun _ ↦ 0) ξ₂
  let δ₄ := optSet24 (rSys rN) oHiN (fun _ ↦ 0) ξ₁
  have hR2 : (uRouterSwapAlwaysLoConj rN).1.mulVec (ket δ₂) = ket δ₄ := by
    rw [uRouterSwap_eq_set24 rN cLoN cHiNVec pLoN oHiN δ₂ hcLoN_d2 hcHiN_d2 hcLoN hcHiN hHiNNe
          (fun b ↦ (hd2_rN (idxBufLoN b) (hBN_lt b).1).trans (hBLN0 b))
          (fun b ↦ (hd2_rN (idxBufHiN b) (hBN_lt b).2).trans (hBHN0 b)),
        show (fun b ↦ δ₂ (rSys rN pLoN b)) = vLoN from
          funext fun b ↦ hd2_rN (idxSysN pLoN b) (hSN_lt pLoN b),
        show (fun b ↦ (oHiN.map (fun p ↦ δ₂ (rSys rN p b))).getD 0) = vHiN from
          funext fun b ↦ by
            dsimp only [vHiN]
            generalize oHiN = oN
            cases oN with
            | none => rfl
            | some p => exact hd2_rN (idxSysN p b) (hSN_lt p b)]
    dsimp only [δ₄, ξ₁, ξ₂, ξ, δ₂]
    rw [← optSet24_comm_set24 (fun q _ j k e ↦ w.pubN_ne_pubE (hBN_lt k).1 (hSE_lt q j) e.symm),
        ← optSet24_comm_set24 (fun q _ j k e ↦ w.pubN_ne_pubE (hBN_lt k).2 (hSE_lt q j) e.symm)]
  have hξ_mid {wt : Wire dLayout} (hlo : 5715 ≤ wt.val) (hhi : wt.val < 5755) :
      ξ (rTot wt) = β (rTot wt) :=
    (set24_of_ne (hMidN hlo hhi).2.1).trans ((set24_of_ne (hMidN hlo hhi).1).trans
      ((set24_of_ne ((hMidE hlo hhi).2.2 qLoE)).trans
        ((set24_of_ne (hMidE hlo hhi).2.1).trans (set24_of_ne (hMidE hlo hhi).1))))
  have hd4_mid {wt : Wire dLayout} (hlo : 5715 ≤ wt.val) (hhi : wt.val < 5755) :
      δ₄ (rTot wt) = β (rTot wt) :=
    (optSet24_of_ne (fun p _ ↦ (hMidN hlo hhi).2.2 p)).trans
      ((set24_of_ne ((hMidN hlo hhi).2.2 pLoN)).trans
        ((optSet24_of_ne (fun q _ ↦ (hMidE hlo hhi).2.2 q)).trans (hξ_mid hlo hhi)))
  have hcAll_d4 :
      routerCtrlHi rN δ₄ = cHiNVec ∧ cLoAlways rN δ₄ = cLoN ∧ routerCtrlHi rE δ₄ = cHiE := by
    obtain ⟨⟨_, eHN4⟩, ⟨_, eHE4⟩⟩ := routerCtrlPair_eq_ctrlBits32_wstate rTot δ₄
    obtain ⟨⟨_, eHN0⟩, ⟨_, eHE0⟩⟩ := routerCtrlPair_eq_ctrlBits32_wstate rTot β
    rw [eHN4, (cLoAlways_eq_ctrlBits32_wstate rTot δ₄).1, eHE4, ctrl32_eq hd4_mid,
        ← eHN0, ← (cLoAlways_eq_ctrlBits32_wstate rTot β).1, ← eHE0]
    exact ⟨rfl, rfl, rfl⟩
  have hCopy3 : copyAll3AlwaysLoBits_wstate rTot δ₄ = ξ := by
    dsimp only [copyAll3AlwaysLoBits_wstate]
    rw [hcAll_d4.1, hcAll_d4.2.1, hcAll_d4.2.2]
    have hξ₂_sysN (p : Fin 47) (k : Fin 24) : ξ₂ (rSys rN p k) = β (rSys rN p k) :=
      (optSet24_of_ne (fun q _ j ↦ w.pubN_ne_pubE (hSN_lt p k) (hSE_lt q j))).trans
        ((set24_of_ne (fun j ↦ (rBufHi_ne_rSys_s5 rN j k p).symm)).trans
          ((set24_of_ne (fun j ↦ (rBufLo_ne_rSys_s5 rN j k p).symm)).trans
            (hξE_rN (idxSysN p k) (hSN_lt p k))))
    have hP1 : copyVecAuxBits_wstate (rBufHi rN) cHiNVec (fun b p ↦ rSys rN p b) 24 le_rfl δ₄ =
        ξ₁ := copyRestore_peel (rBufHi rN) cHiNVec (rSys rN) oHiN ξ₁ hcHiN
      (fun p _ ↦ rSys_inj_s5 rN p) (fun p _ j k ↦ rBufHi_ne_rSys_s5 rN j k p)
      (fun p hp k ↦
        ((set24_of_ne (fun j ↦ rBufHi_ne_rSys_s5 rN k j pLoN)).trans
          ((optSet24_of_ne (fun q _ j ↦ w.pubN_ne_pubE (hBN_lt k).2 (hSE_lt q j))).trans
            ((set24_self (rBufHi_inj_s5 rN) vHiN _ k).trans (by simp [vHiN, hp])))).trans
          ((set24_of_ne (fun j ↦ rSys_ne_of_ne_s5 rN (hHiNNe p hp) k j)).trans
            (hξ₂_sysN p k)).symm)
    have hP2 : copyVecAuxBits_wstate (rBufLo rN) cLoN (fun b p ↦ rSys rN p b) 24 le_rfl ξ₁ =
        ξ₂ := copyRestore_peel (rBufLo rN) cLoN (rSys rN) (some pLoN) ξ₂ hcLoN
      (fun _ h ↦ Option.some.inj h ▸ rSys_inj_s5 rN pLoN)
      (fun _ h j k ↦ Option.some.inj h ▸ rBufLo_ne_rSys_s5 rN j k pLoN)
      (fun p hp k ↦ by
        cases hp
        exact ((optSet24_of_ne (fun q _ j ↦ w.pubN_ne_pubE (hBN_lt k).1 (hSE_lt q j))).trans
          ((set24_of_ne (fun j ↦ rBufLo_ne_rBufHi_s5 rN k j)).trans
            (set24_self (rBufLo_inj_s5 rN) vLoN ξE k))).trans (hξ₂_sysN pLoN k).symm)
    rw [hP1, hP2]
    exact copyRestore_peel (rBufHi rE) cHiE (rSys rE) oHiE ξ hcHiE
      (fun q _ ↦ rSys_inj_s5 rE q) (fun q _ j k ↦ rBufHi_ne_rSys_s5 rE j k q)
      (fun q hq k ↦
        ((set24_of_ne (fun j e ↦ w.pubN_ne_pubE (hBN_lt j).2 (hBE_lt k).2 e.symm)).trans
          ((set24_of_ne (fun j e ↦ w.pubN_ne_pubE (hBN_lt j).1 (hBE_lt k).2 e.symm)).trans
            ((set24_of_ne (fun j ↦ rBufHi_ne_rSys_s5 rE k j qLoE)).trans
              ((set24_self (rBufHi_inj_s5 rE) vHiE _ k).trans (by simp [vHiE, hq]))))).trans
          ((set24_of_ne (fun j e ↦ w.pubN_ne_pubE (hBN_lt j).2 (hSE_lt q k) e.symm)).trans
            ((set24_of_ne (fun j e ↦ w.pubN_ne_pubE (hBN_lt j).1 (hSE_lt q k) e.symm)).trans
              ((set24_of_ne (fun j ↦ rSys_ne_of_ne_s5 rE (hHiENe q hq) k j)).trans
                ((set24_of_ne (fun j ↦ (rBufHi_ne_rSys_s5 rE j k q).symm)).trans
                  (set24_of_ne (fun j ↦ (rBufLo_ne_rSys_s5 rE j k q).symm)))))).symm)
  let base := set24 (rSys rE qLoE) (fun _ ↦ 0) (set24 (rBufLo rE) vLoE (set24 (rBufLo rN) vLoN β))
  have hβ₃_eq : β₃ = set24 (rBufHi rE) vHiNE base := by
    dsimp only [β₃, β₂, β₁, base]
    rw [set24_comm (fun j k ↦ rBufLo_ne_rBufHi_s5 rE j k),
        set24_comm (fun j k ↦ (rBufHi_ne_rSys_s5 rE k j qLoE).symm)]
  have hξ_eq : ξ = set24 (rBufHi rN) vHiN (set24 (rBufHi rE) vHiE base) := by
    dsimp only [ξ, ξE, base]
    rw [set24_comm (fun j k ↦ (rBufHi_ne_rSys_s5 rE k j qLoE).symm),
        set24_comm (fun j k ↦ w.pubN_ne_pubE (hBN_lt j).1 (hBE_lt k).2),
        set24_comm (fun j k ↦ w.pubN_ne_pubE (hBN_lt j).1 (hSE_lt qLoE k)),
        set24_comm (fun j k ↦ w.pubN_ne_pubE (hBN_lt j).1 (hBE_lt k).1)]
  have hBufHiN_layout (b : Fin 24) : rTot (rBufHi rNucLayout b) = rBufHi rN b :=
    (congrArg rTot.wires (hRegs.pubNuc (idxBufHiN b) (hBN_lt b).2)).symm
  have hBufHiE_layout (b : Fin 24) : rTot (rBufHi rElecLayout b) = rBufHi rE b :=
    (congrArg rTot.wires (hRegs.pubElec (idxBufHiE b) (hBE_lt b).2)).symm
  have hξNN : ξ (rTot (wPotIsNN rPot0Layout)) = β (rRawHas2 rN) := by
    have h5750 := val_wPotIsNN_rPot0Layout
    exact (hξ_mid (by omega) (by omega)).trans hβ.2.2.2.1
  obtain ⟨swE, swN, swO⟩ := swapHi24Bits_apply rTot ξ
  have hβ₁_sysNE (b : Fin 24) (i : Fin (47 + 187)) : β₁ (wSysNE b i) = β (wSysNE b i) := by
    dsimp only [wSysNE]
    rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · rw [appendFin_castAdd (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b) p]
      exact set24_of_ne (fun k ↦ (rBufLo_ne_rSys_s5 rN k b p).symm)
    · rw [appendFin_natAdd (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b) q]
      exact hβ₁_rE (idxSysE q b) (hSE_lt q b)
  have hξ_BHN (b : Fin 24) : ξ (rBufHi rN b) = vHiN b :=
    (congrFun hξ_eq (rBufHi rN b)).trans (set24_self (rBufHi_inj_s5 rN) vHiN _ b)
  have hξ_BHE (b : Fin 24) : ξ (rBufHi rE b) = vHiE b :=
    (congrFun hξ_eq (rBufHi rE b)).trans
      ((set24_of_ne (fun k e ↦ w.pubN_ne_pubE (hBN_lt k).2 (hBE_lt b).2 e.symm)).trans
        (set24_self (rBufHi_inj_s5 rE) vHiE base b))
  have hEqBits : β₃ = swapHi24Bits rTot ξ := funext fun u ↦ by
    by_cases hBHE : ∃ b : Fin 24, u = rBufHi rE b
    · obtain ⟨b, rfl⟩ := hBHE
      have hsw := swE b
      rw [hBufHiE_layout b, hBufHiN_layout b, hξNN, hξ_BHN b, hξ_BHE b] at hsw
      rw [hβ₃_eq, set24_self (rBufHi_inj_s5 rE), hsw]
      rcases DynCircExt.bit_cases (β (rRawHas2 rN)) with hRN0 | hRN1
      · have hoN : oHiN = none := ite_eq_right (hRN0.trans_ne zero_ne_one)
        rw [ite_eq_right (hRN0.trans_ne zero_ne_one)]
        dsimp only [vHiNE, vHiE, oHiNE]
        rw [hoN]
        generalize oHiE = oE
        cases oE with
        | none => rfl
        | some q =>
            exact (hβ₁_sysNE b (Fin.natAdd 47 q)).trans
              (congrArg β (appendFin_natAdd (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b) q))
      · let p₀ : Fin 47 := ⟨idxValD (rIdx2 rN) β, hPHiN.1⟩
        rw [ite_eq_left hRN1]
        dsimp only [vHiNE, vHiN, oHiNE]
        rw [show oHiN = some p₀ from ite_eq_left hRN1]
        exact (hβ₁_sysNE b (Fin.castAdd 187 p₀)).trans
          (congrArg β (appendFin_castAdd (fun p ↦ rSys rN p b) (fun q ↦ rSys rE q b) p₀))
    by_cases hBHN : ∃ b : Fin 24, u = rBufHi rN b
    · obtain ⟨b, rfl⟩ := hBHN
      have hsw := swN b
      rw [hBufHiN_layout b, hBufHiE_layout b, hξNN, hξ_BHE b, hξ_BHN b] at hsw
      dsimp only [base] at hβ₃_eq
      rw [hβ₃_eq, set24_of_ne (fun k ↦ w.pubN_ne_pubE (hBN_lt b).2 (hBE_lt k).2),
          set24_of_ne (fun k ↦ w.pubN_ne_pubE (hBN_lt b).2 (hSE_lt qLoE k)),
          set24_of_ne (fun k ↦ w.pubN_ne_pubE (hBN_lt b).2 (hBE_lt k).1),
          set24_of_ne (fun k ↦ (rBufLo_ne_rBufHi_s5 rN k b).symm), hBHN0 b, hsw]
      rcases DynCircExt.bit_cases (β (rRawHas2 rN)) with hRN0 | hRN1
      · simp [vHiN, oHiN, hiOpt, hRN0]
      · rw [ite_eq_left hRN1]
        dsimp only [vHiE]
        rw [hExHi ⟨idxValD (rIdx2 rN) β, hPHiN.1⟩ (ite_eq_left hRN1)]
        rfl
    rw [swO u (fun b e ↦ hBHE ⟨b, e.trans (hBufHiE_layout b)⟩)
          (fun b e ↦ hBHN ⟨b, e.trans (hBufHiN_layout b)⟩),
        hβ₃_eq, hξ_eq, set24_of_ne (fun b e ↦ hBHE ⟨b, e⟩),
        set24_of_ne (fun b e ↦ hBHN ⟨b, e⟩), set24_of_ne (fun b e ↦ hBHE ⟨b, e⟩)]
  rw [hL1, hL2, hL3]
  symm
  rw [show PhotochemistrySolution.XMeasUnld.ket β = ket β from rfl, hR1, hR2,
      uCopyAll3AlwaysLoMux_mulVec_ket_wstate rTot δ₄, hCopy3, uSwapHi24_mulVec_ket rTot ξ,
      ← hEqBits, uBellLoEAlwaysLoMux_mulVec_ket_wstate rTot β₃]
  dsimp only [cBellLoEAlwaysLoSlice_wstate]
  rw [ctrl32_eq (δ := β₃) fun {wt} hlo hhi ↦ by
        rw [hEqBits]
        exact (swO (rTot wt)
          (fun b e ↦ (hMidE hlo hhi).2.1 b (e.trans (hBufHiE_layout b)))
          (fun b e ↦ (hMidN hlo hhi).2.1 b (e.trans (hBufHiN_layout b)))).trans (hξ_mid hlo hhi),
      ← (cLoAlways_eq_ctrlBits32_wstate rTot β).2]
end QuantumComputation.Specs.PhotochemistrySolution.Stage5W298
end Stage5PreEqDirectLocal

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage5W298
open Operator QProg Matrix HermitianMat Circuit Qubit PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.PortBStage5Merged
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.WStateStage5Unload
  PhotochemistrySolution.WStateWalkSeam PhotochemistrySolution.RouterAlwaysLoW338
  PhotochemistrySolution.WState25PortOpt PhotochemistrySolution.Stage2AlwaysLo
open PhotochemistrySolution.AlwaysLoW338At19580 PhotochemistrySolution.AlwaysLoNuc8886W338
  PhotochemistrySolution.ParityCheckW309 PhotochemistrySolution.PortBAncillaScrub
  PhotochemistrySolution.InPlacePortBOracle
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg47_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SharedHi235Port hiding ket_sr_eq_xm
attribute [local irreducible] systemQubits_frozen ancWOfScr uLoNPortOnlyAlways1Conj uLoEAlways1Conj

/--
Stage-5 `LoE_368` wire bijection for `298 ≤ wWork` (`5715 + 298 = 6013`):
relocates `5755..5778` (`24` `rBufLo_N` wires) onto `5680..5691` + `5930..5941`,
`6013..6017` (`5` wires) onto `5942..5946`, and `6018..6020` (`3` wires) onto `5692..5694`.
-/
def permLoE298Val (x : ℕ) : ℕ :=
    if 5680 ≤ x ∧ x < 5692 then 5755 + (x - 5680) else if 5755 ≤ x ∧ x < 5767 then 5680 +
    (x - 5755) else if 5930 ≤ x ∧ x < 5942 then 5767 + (x - 5930) else if 5767 ≤ x ∧ x <
    5779 then 5930 + (x - 5767) else if 5942 ≤ x ∧ x < 5947 then x + 71 else if 6013 ≤ x ∧ x <
    6018 then x - 71 else if 5692 ≤ x ∧ x < 5695 then x + 326 else if 6018 ≤ x ∧ x < 6021 then x -
    326 else x
set_option maxHeartbeats 4000000 in
-- 298-wire low-electron permutation involution
theorem permLoE298Val_invol (x : ℕ) : permLoE298Val (permLoE298Val x) = x := by
  conv_lhs => arg 1; unfold permLoE298Val
  split_ifs <;> (unfold permLoE298Val; split_ifs <;> omega)

theorem permLoE298Val_lt (w : Wire dLayout) : permLoE298Val w.val < dLayout := by
  have hw : w.val < 7298 := hDLayout_eq_7298_w322 ▸ w.isLt;
  have hd : dLayout = 7298 := hDLayout_eq_7298_w322
  unfold permLoE298Val; split_ifs <;> omega

def rPermLoE298 : QRegister dLayout dLayout :=
  ⟨⟨fun w ↦ ⟨permLoE298Val w.val, permLoE298Val_lt w⟩, fun a b h ↦ Fin.ext (by
    have hv := congrArg Fin.val h; dsimp only at hv
    have h2 := congrArg permLoE298Val hv
    rwa [permLoE298Val_invol, permLoE298Val_invol] at h2)⟩⟩

theorem val_rPermLoE298 (w : Wire dLayout) :
    (rPermLoE298 w).val = permLoE298Val w.val := rfl

theorem rPermLoE298_fix_out {w : Wire dLayout} (h : ¬ (5680 ≤ w.val ∧ w.val < 5695) ∧
    ¬ (5755 ≤ w.val ∧ w.val < 5779) ∧ ¬ (5930 ≤ w.val ∧ w.val < 5947) ∧ ¬ (6013 ≤ w.val ∧ w.val <
    6021)) : rPermLoE298 w = w :=
  Fin.ext (by rw [val_rPermLoE298]; unfold permLoE298Val; split_ifs <;> omega)

theorem rPermLoE298_rElecSub_fix {j : Fin (routerWidth 187 8)}
    (hj : j.val < 97 ∨ (114 ≤ j.val ∧ j.val < 4602)) : rPermLoE298 (rElecSub j) = rElecSub j := by
  have hv : (rElecSub j).val = (elecSubWireFn j).val := rfl; refine rPermLoE298_fix_out ?_
  rw [hv, val_elecSubWireFn]; split_ifs <;> omega

theorem val_rCtrlLo_rElecSub_w298 (q : Fin 187) : (rCtrlLo rElecSub q).val = if 16 + q.val <
    33 then 5680 + (16 + q.val) else if 16 + q.val < 129 then 5755 + (16 + q.val - 33) else 5947 +
    (16 + q.val - 129) := by
  let j : Fin (routerWidth 187 8) := ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩;
  have hjVal : j.val = 4624 + q.val := rfl
  have hrk : privRank454Sub (j.val - 4602) = 16 + q.val := by
    rw [hjVal, privRank454Sub_of_6_209 (by omega) (by omega)]; omega
  have hv0 : (rCtrlLo rElecSub q).val = (elecSubWireFn j).val := rfl
  rw [hv0, val_elecSubWireFn, hrk, hjVal,
      _root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega),
          _root_.ite_eq_right (by omega)]

theorem val_rPermLoE298_rCtrlLo_bounds (q : Fin 187) :
    let v := (rPermLoE298 (rCtrlLo rElecSub q)).val
    (5680 ≤ v ∧ v < 5713) ∨ (5779 ≤ v ∧ v < 5851) ∨
    (5930 ≤ v ∧ v < 5947) ∨ (5947 ≤ v ∧ v < 6013) := by
  have hq := q.isLt; have hvC := val_rCtrlLo_rElecSub_w298 q; dsimp only; rw [val_rPermLoE298]
  by_cases h1 : 16 + q.val < 33
  · rw [_root_.ite_eq_left h1] at hvC; rw [hvC]; unfold permLoE298Val; split_ifs <;> omega
  · rw [_root_.ite_eq_right h1] at hvC
    by_cases h2 : 16 + q.val < 129
    · rw [_root_.ite_eq_left h2] at hvC; rw [hvC]; unfold permLoE298Val; split_ifs <;> omega
    · rw [_root_.ite_eq_right h2] at hvC; rw [hvC]; unfold permLoE298Val; split_ifs <;> omega

theorem stage5ElecNoHB7_rPermLoE298_active_mCoin_w298 {wWork mCoin : ℕ} (hw : 298 ≤ wWork)
    {j : Fin (routerWidth 187 8)} (hj : j.val < 97 ∨ (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧
    j.val < 4811)) : ActiveOuterCoinStackOf 23 wWork mCoin (rPermLoE298 (rElecSub j)) := by
  rcases hj with h | h | h
  · rw [rPermLoE298_rElecSub_fix (Or.inl h)];
    have hv : (rElecSub j).val = (elecSubWireFn j).val := rfl
    unfold ActiveOuterCoinStackOf; rw [hv, val_elecSubWireFn]; split_ifs <;> omega
  · rw [rPermLoE298_rElecSub_fix (Or.inr h)];
    have hv : (rElecSub j).val = (elecSubWireFn j).val := rfl
    unfold ActiveOuterCoinStackOf; rw [hv, val_elecSubWireFn]; split_ifs <;> omega
  · let q : Fin 187 := ⟨j.val - 4624, by omega⟩
    have hjEq : j = ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩ :=
      Fin.ext (by dsimp [q, basePub]; omega)
    have hwEq : rPermLoE298 (rElecSub j) = rPermLoE298 (rCtrlLo rElecSub q) :=
        congrArg (fun idx ↦ rPermLoE298 (rElecSub idx)) hjEq
    rw [hwEq]; have hb := val_rPermLoE298_rCtrlLo_bounds q
    unfold ActiveOuterCoinStackOf; omega

set_option maxHeartbeats 4000000 in
-- 341-wire shared Port-B low-control zero invariance
theorem rCtrlLo_rPermLoE298_zero_of_sharedPortB341 {n : ℕ} (rTot : QRegister dLayout n)
    {β : BitAssignment n} (hβ : SharedPortBInput341 rTot (rTot.compose rNucSub)
    (rTot.compose rElecSub) β)
    (q : Fin 187) : β (rCtrlLo ((rTot.compose rPermLoE298).compose rElecSub) q) = 0 := by
  have hq := q.isLt
  obtain ⟨hC0E, _, _, _, _⟩ := facts_of_zeroGatedSorted (by omega) (rTot.compose rElecSub) hβ.1
  have hvC := val_rCtrlLo_rElecSub_w298 q
  by_cases hfx0 : q.val < 17 ∨ (41 ≤ q.val ∧ q.val < 179)
  · have hfx : rPermLoE298 (rCtrlLo rElecSub q) = rCtrlLo rElecSub q :=
      rPermLoE298_fix_out (by rw [hvC]; split_ifs <;> omega)
    change β (rTot (rPermLoE298 (rCtrlLo rElecSub q))) = 0
    rw [hfx]
    exact hC0E q
  by_cases h29 : q.val < 29
  · rw [_root_.ite_eq_right (by omega), _root_.ite_eq_left (by omega)] at hvC
    let p : Fin 47 := ⟨q.val - 17, by omega⟩
    have hvN : (cHiNSub341 p).val = 5680 + (q.val - 17) := by
      rw [val_cHiNSub341]; dsimp [p]; split_ifs <;> omega
    have heq : rPermLoE298 (rCtrlLo rElecSub q) = cHiNSub341 p := Fin.ext (by
      rw [val_rPermLoE298, hvN, hvC]; unfold permLoE298Val; split_ifs <;> omega)
    change β (rTot (rPermLoE298 (rCtrlLo rElecSub q))) = 0
    rw [heq]
    exact hβ.2.2.1 p
  by_cases hHB : q.val < 41 ∨ q.val < 184
  · let b : Fin 24 := ⟨if q.val < 41 then 7 + (q.val - 29) else 19 + (q.val - 179), by
      split_ifs <;> omega⟩
    have hvHB : (rHB rElecSub b).val = 5923 + b.val := by
      have := b.isLt
      change (elecSubWireFn ⟨90 + b.val, rw_ltHB 187 8 b⟩).val = _
      rw [val_elecSubWireFn]; dsimp only; split_ifs <;> omega
    have heq : rPermLoE298 (rCtrlLo rElecSub q) = rHB rElecSub b := Fin.ext (by
      rw [val_rPermLoE298, hvHB, hvC]; dsimp [b]; unfold permLoE298Val; split_ifs <;> omega)
    change β (rTot (rPermLoE298 (rCtrlLo rElecSub q))) = 0
    rw [heq]
    exact (hβ.1.1.2.2.2.1 b).2.2.2
  · rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega)] at hvC
    let iN : Fin (routerWidth 47 6) := ⟨1256 + (q.val - 184), by dsimp [routerWidth]; omega⟩
    have hrkN : privRank156Sub (1256 + (q.val - 184) - 1238) = 12 + (q.val - 184) := by
      unfold privRank156Sub
      rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega),
          _root_.ite_eq_left (by omega)]
      omega
    have hvN : (rNucSub iN).val = 5692 + (q.val - 184) := by
      have hv1 : (rNucSub iN).val = (nucSubWireFn iN).val := rfl
      rw [hv1, val_nucSubWireFn]; dsimp only [iN]; rw [hrkN]; split_ifs <;> omega
    have heq : rPermLoE298 (rCtrlLo rElecSub q) = rNucSub iN := Fin.ext (by
      rw [val_rPermLoE298, hvN, hvC]; unfold permLoE298Val; split_ifs <;> omega)
    change β (rTot (rPermLoE298 (rCtrlLo rElecSub q))) = 0; rw [heq];
    refine hβ.2.1.1.2.2.2.2 ((rTot.compose rNucSub) iN) ?_;
    simp only [sPrivCleanSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨iN, by dsimp [iN, basePub]; omega, rfl⟩

attribute [local irreducible] systemQubits_frozen ancWOfScr uLoNPortOnlyAlways1Conj uLoEAlways1Conj
  uSharedHiPortOnlyConj uSharedHi235Conj uSwapHi24 uRouterSwapAlwaysLoConj in
theorem comm_uLoEAlways1_xorNucLoToElecHiNotScrOp_w298 {n : ℕ} [NeZero (2 ^ n)]
    (rTot : QRegister dLayout n) (Y : Operator (2 ^ n))
    (hY : SupportedOn (fun δ ↦
      (∀ q : Fin 187, δ (rCtrlLo ((rTot.compose rPermLoE298).compose rElecSub) q) = 0) ∧
      UnloadLoPred ((rTot.compose rPermLoE298).compose rElecSub) δ) Y) :
    let rE := (rTot.compose rPermLoE298).compose rElecSub
    uLoEAlways1Conj rE * (xorNucLoToElecHiNotScrOp rTot * Y) =
      xorNucLoToElecHiNotScrOp rTot * (uLoEAlways1Conj rE * Y) := by
  intro rE; let rE0 := rTot.compose rElecSub; let rN := rTot.compose rNucSub;
  let w :=
      SharedPortBWiring.ofValidMuxD1_341 validMuxD1Stage2Regs_sub cHiNSub341_ne_rCtrlLo_rNucSub
      cHiNSub341_ne_rCtrlLo_rElecSub rTot; obtain ⟨eScr32, _, _, eBufLoN, eBufHiE⟩ :=
      pot0_routerSub_dLayout_eqs
  have hPubEq : ∀ {j : Fin (routerWidth 187 8)}, (j.val < 97 ∨ (114 ≤ j.val ∧ j.val < 4602)) →
      rE j = rE0 j := fun hj ↦ congrArg rTot (rPermLoE298_rElecSub_fix hj)
  have hEB : ∀ b : Fin 24, rBufHi rE b = rTot (rBufHi rElecLayout b) := fun b ↦
    (hPubEq (j := ⟨42 + b.val, by have := b.isLt; dsimp [routerWidth]; omega⟩)
      (Or.inl (by have := b.isLt; dsimp; omega))).trans (congrArg rTot (eBufHiE b))
  have hNL : ∀ b : Fin 24, rBufLo rN b = rTot (rBufLo rNucLayout b) := fun b ↦
      congrArg rTot (eBufLoN b)
  have hXEval : xorNucLoToElecHiNotScrOp rTot = (cXorNucLoToElecHiNotScr rTot).eval.1 :=
      rfl; simp only [← Matrix.mul_assoc]
  refine hY _ _ fun δ ⟨hc0, hPLo⟩ ↦ ?_
  simp only [← Matrix.mulVec_mulVec];
  let δ' := xorNucLoToElecHiNotScrBits rTot δ; obtain ⟨_, xOth⟩ :=
      xorNucLoToElecHiNotScrBits_apply rTot δ
  have hc0' : ∀ q : Fin 187, δ' (rCtrlLo rE q) = 0 := fun q ↦
    (xOth _ fun b e ↦ rr_ne rE
      (by have := q.isLt; have := b.isLt; unfold basePub; dsimp; omega)
      (e.trans (hEB b).symm)).trans (hc0 q)
  have hh1 : δ' (rHas1 rE) = δ (rHas1 rE) :=
    xOth _ fun b e ↦ rr_ne rE (by have := b.isLt; dsimp [routerWidth]; omega) (e.trans (hEB b).symm)
  have hi1 : ∀ d : Fin 8, δ' (rIdx1 rE d) = δ (rIdx1 rE d) := fun d ↦
    xOth _ fun b e ↦ rr_ne rE
      (by have := d.isLt; have := b.isLt; dsimp [routerWidth]; omega) (e.trans (hEB b).symm)
  have hPLo' : UnloadLoPred rE δ' :=
      ⟨(SplitRouter47_187.idxValD_congr hi1).trans_lt hPLo.1, fun hz ↦
      (SplitRouter47_187.idxValD_congr hi1).trans (hPLo.2 (hh1.symm.trans hz))⟩
  have hcLoEq : cLoAlways rE δ' = cLoAlways rE δ := by
    funext q; dsimp [cLoAlways]; rw [SplitRouter47_187.idxValD_congr hi1]
  let cPortLoE :=
      cFixedPortCirc (rBufLo rE) (rHA rE) (cLoAlways rE δ) (fun b q ↦ rSys rE q b)
      (hne_fixed_router rE).1 (hne_fixed_router rE).2.2.1
  let S_LoE : Wire n → Prop := fun u ↦
      (∃ b : Fin 24, u = rBufLo rE b ∨ u = rHA rE b) ∨ ∃ (q : Fin 187) (b : Fin 24), u = rSys rE q b
  let S_Xor : Wire n → Prop := fun u ↦
      u = rTot (wPotIsScreen rPot0Layout) ∨ (∃ b : Fin 24, u = rTot (rBufLo rNucLayout b)) ∨
      (∃ b : Fin 24, u = rTot (rBufHi rElecLayout b))
  have cwLoE : CircWires S_LoE cPortLoE :=
    hcnotSupportedIn_toCircWires (hcnotSupportedIn_cFixedPort _ _ _ _ _ _
      (fun b ↦ Or.inl ⟨b, Or.inl rfl⟩) (fun b ↦ Or.inl ⟨b, Or.inr rfl⟩)
      (fun b q _ ↦ Or.inr ⟨q, b, rfl⟩))
  have cwXor : CircWires S_Xor (cXorNucLoToElecHiNotScr rTot) :=
    circWires_cXorNucLoToElecHiNotScr rTot (Or.inl rfl)
      (fun b ↦ Or.inr (Or.inl ⟨b, rfl⟩)) (fun b ↦ Or.inr (Or.inr ⟨b, rfl⟩))
  have notScr32 : ∀ j : Fin (routerWidth 187 8), j.val < 4602 →
      rE0 j ≠ rTot (wPotIsScreen rPot0Layout) := fun j hj e ↦ by
    have hv :=
        congrArg Fin.val (rTot.wires.injective (e.trans (congrArg rTot eScr32))); change
        (elecSubWireFn j).val = wOut32.val at hv
    rw [val_elecSubWireFn, val_wOut32] at hv; split_ifs at hv <;> omega
  have noXor {j : Fin (routerWidth 187 8)}
      (hj : j.val < 42 ∨ (66 ≤ j.val ∧ j.val < 90) ∨ (114 ≤ j.val ∧ j.val < 4602))
      (hMod : AllPlaneMod rE0 (rE0 j)) (hX : S_Xor (rE j)) : False := by
    have eq0 : rE j = rE0 j := hPubEq (by omega)
    rcases hX with e | ⟨b', e⟩ | ⟨b', e⟩
    · exact notScr32 j (by omega) (eq0.symm.trans e)
    · exact w.rN_disj_rE_mod ⟨14 + b'.val, by have := b'.isLt; dsimp [routerWidth]; omega⟩
        _ hMod ((hNL b').trans (e.symm.trans eq0))
    · exact rr_ne rE (by have := b'.isLt; dsimp [rBufHi, routerWidth]; omega)
        (e.trans (hEB b').symm)
  have hComm : cPortLoE.eval.1 * (cXorNucLoToElecHiNotScr rTot).eval.1 =
      (cXorNucLoToElecHiNotScr rTot).eval.1 * cPortLoE.eval.1 :=
    circ_comm_of_disj (fun u hL hX ↦ by
      rcases hL with ⟨b, rfl | rfl⟩ | ⟨q, b, rfl⟩
      · exact noXor (j := ⟨18 + b.val, by have := b.isLt; dsimp [routerWidth]; omega⟩)
          (Or.inl (by have := b.isLt; dsimp; omega)) ⟨b, Or.inl rfl⟩ hX
      · exact noXor (j := ⟨66 + b.val, rw_ltHA 187 8 b⟩)
          (Or.inr (Or.inl ⟨by dsimp; omega, by have := b.isLt; dsimp; omega⟩))
          ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩ hX
      · exact noXor (j := ⟨114 + 24 * q.val + b.val,
            by have := q.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩)
          (Or.inr (Or.inr ⟨by dsimp; omega, by have := q.isLt; have := b.isLt; dsimp; omega⟩))
          ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨q, (planeOfRouter_sys rE0 b q).symm⟩)))⟩ hX)
      cwLoE cwXor
  rw [ket_sr_eq_xm, xorNucLoToElecHiNotScrOp_mulVec_ket, uLoEAlways1Conj_mulVec_ket rE hc0' hPLo',
      hcLoEq, ← xorNucLoToElecHiNotScrOp_mulVec_ket rTot δ, uLoEAlways1Conj_mulVec_ket rE hc0 hPLo,
      hXEval, Matrix.mulVec_mulVec, hComm, ← Matrix.mulVec_mulVec]

theorem rElecLo298_ne_loNSub {n : ℕ} (rTot : QRegister dLayout n) {j : Fin (routerWidth 187 8)}
    (hj : j.val < 97 ∨ (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧ j.val < 4811)) {u : Wire n}
    (hu : (∃ b : Fin 24, u = rBufLo (rTot.compose rNucSub) b) ∨ ∃ (p : Fin 47)
    (b : Fin 24), u = rSys (rTot.compose rNucSub) p b) :
    ((rTot.compose rPermLoE298).compose rElecSub) j ≠ u := by
  rcases hj with h | h | h
  · change rTot (rPermLoE298 (rElecSub j)) ≠ u; rw [rPermLoE298_rElecSub_fix (Or.inl h)]
    exact rElecSub_pub_ne_loNSub rTot (by omega) hu
  · change rTot (rPermLoE298 (rElecSub j)) ≠ u; rw [rPermLoE298_rElecSub_fix (Or.inr h)];
    exact rElecSub_pub_ne_loNSub rTot h.2 hu
  · let q : Fin 187 := ⟨j.val - 4624, by omega⟩
    have hjEq : j = ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩ :=
      Fin.ext (by dsimp [q, basePub]; omega)
    have hwEq : ((rTot.compose rPermLoE298).compose rElecSub) j =
        rTot (rPermLoE298 (rCtrlLo rElecSub q)) :=
        congrArg (fun idx ↦ rTot (rPermLoE298 (rElecSub idx))) hjEq
    rw [hwEq]; have hbE := val_rPermLoE298_rCtrlLo_bounds q
    rcases hu with ⟨b, rfl⟩ | ⟨p, b, rfl⟩ <;> intro e
    · have e' : rTot (rPermLoE298 (rCtrlLo rElecSub q)) = rTot (rBufLo rNucSub b) := e;
      have hv :=
          congrArg Fin.val (rTot.wires.injective e'); rw [pot0_routerSub_dLayout_eqs.2.2.2.1 b,
          val_rBufLo_nuc b] at hv
      have := b.isLt; omega
    · have e' : rTot (rPermLoE298 (rCtrlLo rElecSub q)) = rTot (rSys rNucSub p b) := e;
      have hv := congrArg Fin.val (rTot.wires.injective e')
      have hvN : (rSys rNucSub p b).val = (nucSubWireFn ⟨110 + 24 * p.val + b.val,
        by have := p.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩).val := rfl
      rw [hvN, val_nucSubWireFn] at hv
      have := p.isLt; have := b.isLt; dsimp only at hv; split_ifs at hv <;> omega

theorem rElecLo298_not_portOnlyHiMod {n : ℕ} (rTot : QRegister dLayout n)
    {j : Fin (routerWidth 187 8)} (hj : j.val < 42 ∨ (66 ≤ j.val ∧ j.val < 97) ∨ (4624 ≤ j.val ∧
    j.val < 4811)) : ¬ PortOnlyHiMod (rTot.compose rNucSub) (rTot.compose rElecSub)
    (((rTot.compose rPermLoE298).compose rElecSub) j) := by
  let rN := rTot.compose rNucSub; let rE := rTot.compose rElecSub;
  let rE_Lo := (rTot.compose rPermLoE298).compose rElecSub;
  have w :=
      SharedPortBWiring.ofValidMuxD1_341 validMuxD1Stage2Regs_sub cHiNSub341_ne_rCtrlLo_rNucSub
      cHiNSub341_ne_rCtrlLo_rElecSub rTot
  by_cases hj97 : j.val < 97
  · rw [show rE_Lo j = rE j from congrArg rTot (rPermLoE298_rElecSub_fix (Or.inl hj97))]
    rintro (⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩)
    · exact rr_ne rE (by have := b.isLt; dsimp [routerWidth]; omega) h
    · exact w.pubN_ne_pubE
        (i := ⟨110 + 24 * p'.val + b.val,
          by have := p'.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩)
        (j := j) (by have := p'.isLt; have := b.isLt; dsimp; omega)
        (by rcases hj with h | h | h <;> omega) h.symm
    · exact rr_ne rE (by have := q'.isLt; have := b.isLt; dsimp [routerWidth]; omega) h
  · have h2 : 4624 ≤ j.val ∧ j.val < 4811 := by rcases hj with h | h | h <;> omega
    let q : Fin 187 := ⟨j.val - 4624, by omega⟩
    have hjEq : j = ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩ :=
      Fin.ext (by dsimp [q, basePub]; omega)
    have hwEq : rE_Lo j = rTot (rPermLoE298 (rCtrlLo rElecSub q)) :=
        congrArg (fun idx ↦ rTot (rPermLoE298 (rElecSub idx))) hjEq
    rw [hwEq]; have hbE := val_rPermLoE298_rCtrlLo_bounds q
    rintro (⟨b, h⟩ | ⟨p', b, h⟩ | ⟨q', b, h⟩)
    · have hv :=
          congrArg Fin.val (rTot.wires.injective (h.trans (congrArg rTot
          (pot0_routerSub_dLayout_eqs.2.2.2.2 b))))
      rw [val_bufHi_elec b] at hv; have := b.isLt; omega
    · have hv := congrArg Fin.val (rTot.wires.injective h)
      have hvN : (rSys rNucSub p' b).val = (nucSubWireFn ⟨110 + 24 * p'.val + b.val,
        by have := p'.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩).val := rfl
      rw [hvN, val_nucSubWireFn] at hv
      have := p'.isLt; have := b.isLt; dsimp only at hv; split_ifs at hv <;> omega
    · have hv := congrArg Fin.val (rTot.wires.injective h)
      have hvS : (rSys rElecSub q' b).val = (elecSubWireFn ⟨114 + 24 * q'.val + b.val,
        by have := q'.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩).val := rfl
      rw [hvS, val_elecSubWireFn] at hv
      have := q'.isLt; have := b.isLt; dsimp only at hv; split_ifs at hv <;> omega

/--
Stage-5 `SharedHi_452` wire bijection for `298 ≤ wWork` (`5715 + 298 = 6013`):
uses all `43` `0`-T clean `|0>` holes outside `SharedHi235` + `UnloadFootprintN`
(`3` from `cOut40Scrub3`, `12` on `5899..5910`, `11` on `5912..5922` skipping `5911 = qScrNotE`,
and `17` on `5930..5946`) to relocate `[6013..6052]` (`40` wires) into `< 6013`!
-/
def permSharedHi298Val (x : ℕ) : ℕ :=
    if 5899 ≤ x ∧ x < 5911 then x + 125 else if 6024 ≤ x ∧ x < 6036 then x - 125 else if 5912 ≤ x ∧
    x < 5923 then x + 101 else if 6013 ≤ x ∧ x < 6024 then x - 101 else if 5930 ≤ x ∧ x <
    5947 then x + 106 else if 6036 ≤ x ∧ x < 6053 then x - 106 else x
theorem permSharedHi298Val_invol (x : ℕ) : permSharedHi298Val (permSharedHi298Val x) = x := by
  conv_lhs => arg 1; unfold permSharedHi298Val
  split_ifs <;> (unfold permSharedHi298Val; split_ifs <;> omega)

theorem permSharedHi298Val_lt (w : Wire dLayout) : permSharedHi298Val w.val < dLayout := by
  have hw : w.val < 7298 := hDLayout_eq_7298_w322 ▸ w.isLt;
  have hd : dLayout = 7298 := hDLayout_eq_7298_w322
  unfold permSharedHi298Val; split_ifs <;> omega

def rPermSharedHi298 : QRegister dLayout dLayout :=
  ⟨⟨fun w ↦ ⟨permSharedHi298Val w.val, permSharedHi298Val_lt w⟩, fun a b h ↦ Fin.ext (by
    have hv := congrArg Fin.val h; dsimp only at hv
    have h2 := congrArg permSharedHi298Val hv
    rwa [permSharedHi298Val_invol, permSharedHi298Val_invol] at h2)⟩⟩

theorem val_rPermSharedHi298 (w : Wire dLayout) :
    (rPermSharedHi298 w).val = permSharedHi298Val w.val := rfl

theorem rPermSharedHi298_fix_out {w : Wire dLayout} (h : ¬ (5899 ≤ w.val ∧ w.val < 5911) ∧
    ¬ ((5912 ≤ w.val ∧ w.val < 5923) ∨ (5930 ≤ w.val ∧ w.val < 5947)) ∧ ¬ (6013 ≤ w.val ∧ w.val <
    6053)) : rPermSharedHi298 w = w :=
  Fin.ext (by rw [val_rPermSharedHi298]; unfold permSharedHi298Val; split_ifs <;> omega)

theorem rPermSharedHi298_unloadFootprintN_facts_mCoin {wWork mCoin : ℕ} (hw : 298 ≤ wWork)
    {i : Fin (routerWidth 47 6)} (hi : i.val < basePub 47 6 ∨ (1256 ≤ i.val ∧ i.val < 1303)) :
    rPermScrub338 (rNucSub i) = rNucSub i ∧ rPermSharedHi298 (rNucSub i) = rNucSub i ∧
    ActiveOuterCoinStackOf 23 wWork mCoin (rNucSub i) := by
  have hbp : basePub 47 6 = 1238 := rfl; have hrw : routerWidth 47 6 = 1394 := rfl;
  have hiLt : i.val < 1394 := hrw ▸ i.isLt; rw [hbp] at hi
  have hrLt : i.val < 1238 ∨ privRank156Sub (i.val - 1238) < 59 := by
    rcases hi with h | h
    · exact Or.inl h
    · refine Or.inr ?_; unfold privRank156Sub
      rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega),
          _root_.ite_eq_left (by omega)]
      omega
  have hv : (rNucSub i).val = (nucSubWireFn i).val :=
      rfl; refine ⟨rPermScrub338_fix ?_, rPermSharedHi298_fix_out ?_, ?_⟩
  · rw [hv, val_nucSubWireFn]; split_ifs <;> omega
  · rw [hv, val_nucSubWireFn]; split_ifs <;> omega
  · unfold ActiveOuterCoinStackOf; rw [hv, val_nucSubWireFn]; split_ifs <;> omega

theorem rPermSharedHi298_rPermScrub338_cHiNSub341_active_w298_mCoin {wWork mCoin : ℕ}
    (hw : 298 ≤ wWork)
    (p : Fin 47) :
    ActiveOuterCoinStackOf 23 wWork mCoin (rPermSharedHi298 (rPermScrub338 (cHiNSub341 p))) := by
  have hp := p.isLt; let s0 := (cHiNSub341 p).val
  have hs0 : (5680 ≤ s0 ∧ s0 < 5692) ∨ (6021 ≤ s0 ∧ s0 < 6056) := by
    dsimp only [s0]; rw [val_cHiNSub341]; split_ifs <;> omega
  let s1 := (rPermScrub338 (cHiNSub341 p)).val
  have hs1 : (5680 ≤ s1 ∧ s1 < 5692) ∨ s1 = 5747 ∨ s1 = 5749 ∨ s1 = 5750 ∨ (6021 ≤ s1 ∧ s1 < 6053)
      := by
    dsimp only [s1]; rw [val_rPermScrub338]
    change (5680 ≤ permScrub338Val s0 ∧ permScrub338Val s0 < 5692) ∨ permScrub338Val s0 = 5747 ∨
        permScrub338Val s0 = 5749 ∨ permScrub338Val s0 = 5750 ∨ (6021 ≤ permScrub338Val s0 ∧
        permScrub338Val s0 < 6053)
    unfold permScrub338Val; split_ifs <;> omega
  unfold ActiveOuterCoinStackOf; rw [val_rPermSharedHi298]; unfold permSharedHi298Val
  split_ifs <;> omega

theorem rPermSharedHi298_out40Scrub3Rel_iff {n : ℕ} (rTot : QRegister dLayout n)
    (β : BitAssignment n) : Out40Scrub3Rel (rTot.compose rPermSharedHi298) β ↔
    Out40Scrub3Rel rTot β := by
  have fx {w : Wire dLayout} {v : ℕ} (hv : w.val = v) (h : v < 5899 := by decide) :
      rPermSharedHi298 w = w := rPermSharedHi298_fix_out ⟨by omega, by omega, by omega⟩
  dsimp only [Out40Scrub3Rel, QRegister.compose_apply]
  rw [fx val_wOut0, fx val_wOut1, fx val_wOut14, fx val_wOut15, fx val_wOut32,
      fx val_wOut34, fx val_wOut35]
theorem zSwapped_rPermSharedHi298 {n : ℕ} (rTot : QRegister dLayout n) {β : BitAssignment n}
    (hβ : SharedPortBInput341 rTot (rTot.compose rNucSub) (rTot.compose rElecSub) β)
    {w : Wire dLayout} (hge : 6013 ≤ w.val) (hlt : w.val < 6053) : β (rTot (rPermSharedHi298 w)) =
    0 := by
  by_cases h36 : w.val < 6036
  · let b : Fin 24 :=
      ⟨if w.val < 6024 then 13 + (w.val - 6013) else w.val - 6024, by split_ifs <;> omega⟩
    have heq : rPermSharedHi298 w = rElecSub ⟨66 + b.val, rw_ltHA 187 8 b⟩ := Fin.ext (by
      change permSharedHi298Val w.val = (elecSubWireFn ⟨66 + b.val, rw_ltHA 187 8 b⟩).val
      rw [val_elecSubWireFn]
      unfold permSharedHi298Val
      dsimp only [b]
      split_ifs <;> omega)
    exact (congrArg (fun x ↦ β (rTot x)) heq).trans (hβ.1.1.2.2.2.1 b).2.2.1
  · let b : Fin 24 := ⟨7 + (w.val - 6036), by omega⟩
    have heq : rPermSharedHi298 w = rElecSub ⟨90 + b.val, rw_ltHB 187 8 b⟩ := Fin.ext (by
      change permSharedHi298Val w.val = (elecSubWireFn ⟨90 + b.val, rw_ltHB 187 8 b⟩).val
      rw [val_elecSubWireFn]
      unfold permSharedHi298Val
      dsimp only [b]
      split_ifs <;> omega)
    exact (congrArg (fun x ↦ β (rTot x)) heq).trans (hβ.1.1.2.2.2.1 b).2.2.2

theorem sharedHiPortOnlyPred_rPermSharedHi298_of_sharedPortB341 {n : ℕ}
    (rTot : QRegister dLayout n) {β : BitAssignment n}
    (hβ : SharedPortBInput341 rTot (rTot.compose rNucSub) (rTot.compose rElecSub) β) :
    let rHi := rTot.compose rPermSharedHi298; let rN_Hi := rHi.compose rNucSub;
    let rE_Hi := rHi.compose rElecSub
    let cHiN_Hi := fun p ↦ rHi (cHiNSub341 p)
    SharedHiPortOnlyPred rN_Hi rE_Hi cHiN_Hi β ∧
      ∀ j : Fin 7, β (s7OfHBE rE_Hi j) = 0 := by
  intro rHi rN_Hi rE_Hi cHiN_Hi; let rN := rTot.compose rNucSub; let rE := rTot.compose rElecSub
  obtain ⟨hC0E, _, hPHiE, _, _⟩ := facts_of_zeroGatedSorted (by omega) rE hβ.1
  obtain ⟨_, _, hPHiN, _, _⟩ := facts_of_zeroGatedSorted (by omega) rN hβ.2.1
  have pubNEq : ∀ i : Fin (routerWidth 47 6), i.val < 1238 → rN_Hi i = rN i := fun i hi ↦ by
    have hv : (rNucSub i).val = (nucSubWireFn i).val := rfl
    exact congrArg rTot (rPermSharedHi298_fix_out
        (by rw [hv, val_nucSubWireFn]; split_ifs <;> omega))
  have elecFix : ∀ j : Fin (routerWidth 187 8),
      (j.val < 66 ∨ (90 ≤ j.val ∧ j.val < 97) ∨ (114 ≤ j.val ∧ j.val < 4602) ∨
       (4624 ≤ j.val ∧ j.val < 4803)) → rE_Hi j = rE j := fun j hj ↦ by
    have hrw : routerWidth 187 8 = 5056 := rfl; have hjLt : j.val < 5056 := hrw ▸ j.isLt
    have hrLt : j.val < 66 ∨ (90 ≤ j.val ∧ j.val < 97) ∨ (114 ≤ j.val ∧ j.val < 4602) ∨
        privRank454Sub (j.val - 4602) < 195 := by
      rcases hj with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ?_)); unfold privRank454Sub
        rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega),
            _root_.ite_eq_left (by omega)]; omega
    have hv : (rElecSub j).val = (elecSubWireFn j).val := rfl
    exact congrArg rTot (rPermSharedHi298_fix_out
        (by rw [hv, val_elecSubWireFn]; split_ifs <;> omega))
  have hcN_Hi : ∀ p : Fin 47, β (cHiN_Hi p) = 0 := fun p ↦ by
    have hpLt : p.val < 47 := p.isLt; let s := cHiNSub341 p
    have hs_bds : (5680 ≤ s.val ∧ s.val < 5692) ∨ (6021 ≤ s.val ∧ s.val < 6053) ∨ (6053 ≤ s.val ∧
        s.val < 6056) := by dsimp only [s]; rw [val_cHiNSub341]; split_ifs <;> omega
    by_cases h6021 : 6021 ≤ s.val ∧ s.val < 6053
    · exact zSwapped_rPermSharedHi298 rTot hβ (by omega) h6021.2
    · change β (rTot (rPermSharedHi298 s)) = 0
      rw [rPermSharedHi298_fix_out ⟨by omega, by omega, by omega⟩]
      exact hβ.2.2.1 p
  have hcE_Hi : ∀ q : Fin 187, β (rCtrlLo rE_Hi q) = 0 := fun q ↦ by
    have hqLt := q.isLt
    by_cases hq179 : q.val < 179
    · have heq : rCtrlLo rE_Hi q = rCtrlLo rE q :=
        elecFix ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩
          (Or.inr (Or.inr (Or.inr ⟨by dsimp [basePub]; omega, by dsimp [basePub]; omega⟩)))
      rw [heq]; exact hC0E q
    · have hvC := val_rCtrlLo_rElecSub_w298 q
      rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega)] at hvC
      exact zSwapped_rPermSharedHi298 rTot hβ (w := rCtrlLo rElecSub q) (by omega) (by omega)
  have rawNEq : rRawHas2 rN_Hi = rRawHas2 rN :=
    pubNEq ⟨1, rw_lt1 47 6⟩ (by dsimp [routerWidth]; omega)
  have rawEEq : rRawHas2 rE_Hi = rRawHas2 rE :=
    elecFix ⟨1, rw_lt1 187 8⟩ (Or.inl (by dsimp [routerWidth]; omega))
  have nIdx2 : ∀ d : Fin 6, rIdx2 rN_Hi d = rIdx2 rN d :=
    fun d ↦ pubNEq ⟨2 + 6 + d.val, rw_ltIdx2 d⟩ (by have := d.isLt; dsimp; omega)
  have idx2NEq : idxValD (rIdx2 rN_Hi) β = idxValD (rIdx2 rN) β :=
    SplitRouter47_187.idxValD_congr fun d ↦ congrArg β (nIdx2 d)
  have hPHiN_Hi : UnloadHiPred rN_Hi β := unloadHiPred_router_congr rawNEq nIdx2 hPHiN
  have hPHiE_Hi : UnloadHiPred rE_Hi β := unloadHiPred_router_congr rawEEq
    (fun d ↦ elecFix ⟨2 + 8 + d.val, rw_ltIdx2 d⟩ (Or.inl (by have := d.isLt; dsimp; omega))) hPHiE
  have hBufE0_Hi : ∀ k : Fin 24, β (rBufHi rE_Hi k) = 0 := fun k ↦
    (congrArg β (elecFix ⟨42 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩
      (Or.inl (by have := k.isLt; dsimp; omega)))).trans (hβ.1.1.2.2.2.1 k).2.1
  have hs7_Hi : ∀ j : Fin 7, β (s7OfHBE rE_Hi j) = 0 := fun j ↦
    (congrArg β (elecFix ⟨90 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩
      (Or.inr (Or.inl ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩)))).trans
      (hβ.1.1.2.2.2.1 ⟨j.val, by omega⟩).2.2.2
  have hVN_Hi : ValidZeroGatedSortedRouterInput rN_Hi β := by
    have nHas1 : rHas1 rN_Hi = rHas1 rN := pubNEq ⟨0, rw_lt0 47 6⟩ (by dsimp; omega)
    have nIdx1 : ∀ d : Fin 6, rIdx1 rN_Hi d = rIdx1 rN d :=
      fun d ↦ pubNEq ⟨2 + d.val, rw_ltIdx1 d⟩ (by have := d.isLt; dsimp; omega)
    have idx1NEq : idxValD (rIdx1 rN_Hi) β = idxValD (rIdx1 rN) β :=
      SplitRouter47_187.idxValD_congr fun d ↦ congrArg β (nIdx1 d)
    have bufN (i : Fin (routerWidth 47 6)) (hi : i.val < 1238) {z : ZMod 2}
        (hz : β (rN i) = z) : β (rN_Hi i) = z := (congrArg β (pubNEq i hi)).trans hz
    have hBufN0 (b : Fin 24) :
        β (rBufLo rN_Hi b) = 0 ∧ β (rBufHi rN_Hi b) = 0 ∧ β (rHA rN_Hi b) = 0 ∧ β (rHB rN_Hi b) =
            0 :=
      have hb := b.isLt
      ⟨bufN ⟨14 + b.val, by dsimp [routerWidth]; omega⟩ (by dsimp; omega) (hβ.2.1.1.2.2.2.1 b).1,
       bufN ⟨38 + b.val, by dsimp [routerWidth]; omega⟩ (by dsimp; omega) (hβ.2.1.1.2.2.2.1 b).2.1,
       bufN ⟨62 + b.val, rw_ltHA 47 6 b⟩ (by dsimp; omega) (hβ.2.1.1.2.2.2.1 b).2.2.1,
       bufN ⟨86 + b.val, rw_ltHB 47 6 b⟩ (by dsimp; omega) (hβ.2.1.1.2.2.2.1 b).2.2.2⟩
    have hPrivN0 : ∀ u ∈ sPrivCleanSet rN_Hi, β u = 0 := by
      intro u hu
      simp only [sPrivCleanSet, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and] at hu
      obtain ⟨i, hiGe, rfl⟩ := hu
      have hbp : basePub 47 6 = 1238 := rfl
      have hrw : routerWidth 47 6 = 1394 := rfl
      have hiLt : i.val < 1394 := hrw ▸ i.isLt
      have _ : privRank156Sub (i.val - 1238) < 156 :=
        privRank156Sub_lt (by rw [hbp] at hiGe; omega)
      let s := rNucSub i
      have hs_bds : (5680 ≤ s.val ∧ s.val < 5713) ∨ (5947 ≤ s.val ∧ s.val < 6013) ∨
          (6013 ≤ s.val ∧ s.val < 6053) ∨ (6053 ≤ s.val ∧ s.val < 6070) := by
        have hv : s.val = (nucSubWireFn i).val := rfl
        rw [hv, val_nucSubWireFn]; split_ifs <;> (rw [hbp] at hiGe; omega)
      by_cases h6013 : 6013 ≤ s.val ∧ s.val < 6053
      · exact zSwapped_rPermSharedHi298 rTot hβ h6013.1 h6013.2
      · change β (rTot (rPermSharedHi298 s)) = 0
        rw [rPermSharedHi298_fix_out ⟨by omega, by omega, by omega⟩]
        refine hβ.2.1.1.2.2.2.2 (rN i) ?_
        simp only [sPrivCleanSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, hiGe, rfl⟩
    exact ⟨⟨fun h ↦ by rw [nHas1]; exact hβ.2.1.1.1 (by rwa [← rawNEq]),
            fun h ↦ idx1NEq.trans_lt (hβ.2.1.1.2.1 (by rwa [← nHas1])),
            fun h ↦ idx2NEq.trans_lt (hβ.2.1.1.2.2.1 (by rwa [← rawNEq])),
            hBufN0, hPrivN0⟩,
      fun h d ↦ by rw [nIdx1 d]; exact hβ.2.1.2.1 (by rwa [← nHas1]) d,
      fun h d ↦ by rw [nIdx2 d]; exact hβ.2.1.2.2.1 (by rwa [← rawNEq]) d,
      fun h ↦ by rw [idx1NEq, idx2NEq]; exact hβ.2.1.2.2.2 (by rwa [← rawNEq])⟩
  exact ⟨⟨hcN_Hi, hcE_Hi, hPHiN_Hi, hPHiE_Hi,
    fun h1 ↦ by rw [rawEEq]; exact hβ.2.2.2.2 (by rwa [← rawNEq]),
    hBufE0_Hi, hVN_Hi⟩, hs7_Hi⟩

def pStage5AlwaysLoInPlaceW298_908 {Var : Type} {n : ℕ} (v : Var) (rTot : QRegister dLayout n) :
    DynamicCircuit Var n :=
  let rN := rTot.compose rNucSub; let rE := rTot.compose rElecSub;
  let rE_Lo := (rTot.compose rPermLoE298).compose rElecSub; let s7 := s7OfHBE rE;
  let s7_Lo := s7OfHBE rE_Lo
  .seq (pUnloadLoEAlways1WState_368 v rE_Lo (padEOfS7 s7_Lo) (qEncOfS7 s7_Lo))
    (.seq (pUnloadSharedHi235W338_452 v (rTot.compose rPermSharedHi298))
      (pUnloadLoNPortOnlyAlways1WState88 v rN (padNOfS7 s7) (qEncOfS7 s7)))

theorem counts_pStage5AlwaysLoInPlaceW298_908 {Var : Type} {n : ℕ} (v : Var)
    (rTot : QRegister dLayout n) : (pStage5AlwaysLoInPlaceW298_908 v rTot).count .T = 908 ∧
    (pStage5AlwaysLoInPlaceW298_908 v rTot).count .TOFF = 0 := by
  let rN := rTot.compose rNucSub; let rE := rTot.compose rElecSub;
  let rE_Lo := (rTot.compose rPermLoE298).compose rElecSub; let s7 := s7OfHBE rE;
  let s7_Lo := s7OfHBE rE_Lo; let rHi := rTot.compose rPermSharedHi298;
  let rHi' := rHi.compose rPermScrub338;
  let w' := sharedPortBWiring_hi235 rHi'; obtain ⟨tS, fS⟩ :=
      counts_cOut40Scrub3 rHi; obtain ⟨t1, f1⟩ :=
      count_pUnloadLoNPortOnlyAlways1WState88 v rN (padNOfS7 s7) (qEncOfS7 s7); obtain ⟨t2, f2⟩ :=
      count_pUnloadLoEAlways1WState_368 v rE_Lo (padEOfS7 s7_Lo) (qEncOfS7 s7_Lo)
  obtain ⟨t3, f3⟩ :=
      count_pUnloadSharedHiPortOnly235WState_452 v (rHi'.compose rNucSub) (rHi'.compose rElecHi235)
      (fun p ↦ rHi' (cHiNSub341 p)) w' (ctrlE_ne_bufLoN_hi235 rHi')
      (s7OfHBE (rHi'.compose rElecHi235))
  dsimp only [pStage5AlwaysLoInPlaceW298_908, pUnloadSharedHi235W338_452,
      pUnloadSharedHiPortOnly235HBEWState_452, DynamicCircuit.count]; rw [t2, f2, tS, fS, t3, f3,
      t1, f1]; exact ⟨rfl, rfl⟩
theorem rPermSharedHi298_sharedHi235ElecFootprint_fix_lt4803 {j : Fin (routerWidth 187 8)}
    (hj : j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 66) ∨ j.val = 78 ∨ (90 ≤ j.val ∧ j.val < 97) ∨
    (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧ j.val < 4803)) : rPermScrub338 (rElecHi235 j) =
    rElecHi235 j ∧ rPermSharedHi298 (rElecHi235 j) = rElecHi235 j := by
  by_cases h4641 : 4641 ≤ j.val ∧ j.val < 4665
  · let q : Fin 187 := ⟨j.val - 4624, by omega⟩
    have hqVal : q.val = j.val - 4624 := rfl
    have hjEq : j = ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩ :=
      Fin.ext (by dsimp only [basePub]; rw [hqVal]; omega)
    have hwEq : rElecHi235 j = rBufLo rElecSub ⟨q.val - 17, by omega⟩ :=
      (congrArg rElecHi235.wires hjEq).trans (rCtrlLo_rElecHi235_eq_bufLo_of_17_41
          (by rw [hqVal]; omega) (by rw [hqVal]; omega))
    rw [hwEq]
    set b : Fin 24 := ⟨q.val - 17, by omega⟩
    have hb := b.isLt
    have hv : (rBufLo rElecSub b).val = 5851 + b.val := by
      have hv0 : (rBufLo rElecSub b).val =
          (elecSubWireFn ⟨18 + b.val, by dsimp [routerWidth]; omega⟩).val := rfl
      rw [hv0, val_elecSubWireFn]; dsimp only; split_ifs <;> omega
    exact ⟨rPermScrub338_fix (by omega), rPermSharedHi298_fix_out ⟨by omega, by omega, by omega⟩⟩
  · have hEq0 : rElecHi235 j = rElecSub j := by
      refine rElecHi235_eq_of_not_swap ?_
      rcases hj with h | h | h | h | h | h <;> omega
    rw [hEq0]
    have hv0 : (rElecSub j).val = (elecSubWireFn j).val := rfl
    by_cases hj4602 : j.val < 4602
    · refine ⟨rPermScrub338_fix ?_, rPermSharedHi298_fix_out ?_⟩ <;>
        (rw [hv0, val_elecSubWireFn]
         rcases hj with h | h | h | h | h | h <;> split_ifs <;> omega)
    · have h4 : 4624 ≤ j.val ∧ j.val < 4803 := by rcases hj with h | h | h | h | h | h <;> omega
      have hrk : privRank454Sub (j.val - 4602) = j.val - 4608 := by
        rw [privRank454Sub_of_6_209 (by omega) (by omega)]
        omega
      refine ⟨rPermScrub338_fix ?_, rPermSharedHi298_fix_out ?_⟩ <;>
        (rw [hv0, val_elecSubWireFn, hrk]
         split_ifs <;> omega)

theorem rPermSharedHi298_sharedHi235ElecFootprint_active_mCoin {wWork mCoin : ℕ} (hw : 298 ≤ wWork)
    {j : Fin (routerWidth 187 8)} (hj : j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 66) ∨ j.val = 78 ∨
    (90 ≤ j.val ∧ j.val < 97) ∨ (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧ j.val < 4811)) :
    ActiveOuterCoinStackOf 23 wWork mCoin (rPermSharedHi298 (rPermScrub338 (rElecHi235 j))) := by
  by_cases h4803 : 4803 ≤ j.val ∧ j.val < 4811
  · have hEq0 : rElecHi235 j = rElecSub j := rElecHi235_eq_of_not_swap (by omega)
    have hrk : privRank454Sub (j.val - 4602) = j.val - 4608 := by
      rw [privRank454Sub_of_6_209 (by omega) (by omega)]; omega
    have hv : (rElecSub j).val = 6013 + (j.val - 4803) := by
      have hv0 : (rElecSub j).val = (elecSubWireFn j).val := rfl
      rw [hv0, val_elecSubWireFn, hrk]; split_ifs <;> omega
    have fSc : rPermScrub338 (rElecSub j) = rElecSub j := rPermScrub338_fix (by omega)
    rw [hEq0, fSc]; unfold ActiveOuterCoinStackOf
    rw [val_rPermSharedHi298, hv]; unfold permSharedHi298Val; split_ifs <;> omega
  · have hj' : j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 66) ∨ j.val = 78 ∨ (90 ≤ j.val ∧ j.val < 97) ∨
        (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧ j.val < 4803) := by
      rcases hj with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩))))
    obtain ⟨fSc, fHi⟩ := rPermSharedHi298_sharedHi235ElecFootprint_fix_lt4803 hj'; rw [fSc, fHi]
    by_cases h4641 : 4641 ≤ j.val ∧ j.val < 4665
    · let q : Fin 187 := ⟨j.val - 4624, by omega⟩
      have hqVal : q.val = j.val - 4624 := rfl
      have hjEq : j = ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩ :=
        Fin.ext (by dsimp only [basePub]; rw [hqVal]; omega)
      have hwEq : rElecHi235 j = rBufLo rElecSub ⟨q.val - 17, by omega⟩ :=
        (congrArg rElecHi235.wires hjEq).trans (rCtrlLo_rElecHi235_eq_bufLo_of_17_41
            (by rw [hqVal]; omega) (by rw [hqVal]; omega))
      rw [hwEq]
      set b : Fin 24 := ⟨q.val - 17, by omega⟩
      have hb := b.isLt
      have hv0 : (rBufLo rElecSub b).val =
          (elecSubWireFn ⟨18 + b.val, by dsimp [routerWidth]; omega⟩).val := rfl
      unfold ActiveOuterCoinStackOf; rw [hv0, val_elecSubWireFn]; dsimp only; split_ifs <;> omega
    · have hEq0 : rElecHi235 j = rElecSub j := by
        refine rElecHi235_eq_of_not_swap ?_
        rcases hj' with h | h | h | h | h | h <;> omega
      rw [hEq0]
      have hv0 : (rElecSub j).val = (elecSubWireFn j).val := rfl
      unfold ActiveOuterCoinStackOf
      by_cases hj4602 : j.val < 4602
      · rw [hv0, val_elecSubWireFn]
        rcases hj' with h | h | h | h | h | h <;> split_ifs <;> omega
      · have h4 : 4624 ≤ j.val ∧ j.val < 4803 := by rcases hj' with h | h | h | h | h | h <;> omega
        have hrk : privRank454Sub (j.val - 4602) = j.val - 4608 := by
          rw [privRank454Sub_of_6_209 (by omega) (by omega)]
          omega
        rw [hv0, val_elecSubWireFn, hrk]
        split_ifs <;> omega

theorem dynWires_pStage5AlwaysLoInPlaceW298_908_mCoin {Var : Type} {wWork mCoin n : ℕ}
    {S : Wire n → Prop} (hw : 298 ≤ wWork) (v : Var) (rTot : QRegister dLayout n)
    (hAct : ∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rTot w)) :
    DynWires S (pStage5AlwaysLoInPlaceW298_908 v rTot) := by
  let rN := rTot.compose rNucSub; let rE := rTot.compose rElecSub;
  let rE_Lo := (rTot.compose rPermLoE298).compose rElecSub;
  let rHi := rTot.compose rPermSharedHi298; let rHi' := rHi.compose rPermScrub338;
  let rN' := rHi'.compose rNucSub; let rE' := rHi'.compose rElecHi235;
  let w' := sharedPortBWiring_hi235 rHi'
  have cwS : CircWires S (cOut40Scrub3 rHi) := by
    have ok {w : Wire dLayout} {v : ℕ} (hv : w.val = v)
        (h1 : 5715 ≤ v := by decide) (h2 : v ≤ 5754 := by decide) : S (rHi w) :=
      congrArg rTot (rPermSharedHi298_fix_out (w := w) ⟨by omega, by omega, by omega⟩) ▸
        hAct w (by unfold ActiveOuterCoinStackOf; omega)
    have cnotS {a b : Wire n} {hne : a ≠ b} (ha : S a) (hb : S b) :
        CircWires S (Circuit.CNOT a b hne) := by
      dsimp only [CircWires, Circuit.CNOT]
      intro i
      fin_cases i
      · exact ha
      · exact hb
    dsimp only [cOut40Scrub3]
    exact ⟨⟨⟨⟨cnotS (ok val_wOut1) (ok val_wOut32), cnotS (ok val_wOut15) (ok val_wOut32)⟩,
      cnotS (ok val_wOut0) (ok val_wOut34)⟩, cnotS (ok val_wOut14) (ok val_wOut34)⟩,
      cnotS (ok val_wOut1) (ok val_wOut35)⟩
  have hrN : ∀ u, UnloadFootprintN rN u → S u := by
    rintro _ ⟨i, rfl, hi⟩;
    exact hAct (rNucSub i) (rPermSharedHi298_unloadFootprintN_facts_mCoin hw hi).2.2
  have hrE_Lo : ∀ u, Stage5ElecFootprintNoHB7 rE_Lo u → S u := by
    rintro _ ⟨j, rfl, hj⟩;
    exact hAct (rPermLoE298 (rElecSub j)) (stage5ElecNoHB7_rPermLoE298_active_mCoin_w298 hw hj)
  have hrN' : ∀ u, UnloadFootprintN rN' u → S u := by
    rintro _ ⟨i, rfl, hi⟩;
    obtain ⟨fSc, fHi, hA⟩ :=
        rPermSharedHi298_unloadFootprintN_facts_mCoin hw hi; change S (rTot (rPermSharedHi298
        (rPermScrub338 (rNucSub i))))
    rw [fSc, fHi]; exact hAct _ hA
  have hrE' : ∀ u, Stage5SharedHi235ElecFootprint rE' u → S u := by
    rintro _ ⟨j, rfl, hj⟩;
    exact hAct (rPermSharedHi298 (rPermScrub338 (rElecHi235 j)))
        (rPermSharedHi298_sharedHi235ElecFootprint_active_mCoin hw hj)
  have hs7_Lo : ∀ j : Fin 7, S (s7OfHBE rE_Lo j) :=
    fun j ↦ hrE_Lo _ ⟨⟨74 + 2 * 8 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩, rfl,
      Or.inl (by have := j.isLt; dsimp; omega)⟩
  have hs7 : ∀ j : Fin 7, S (s7OfHBE rE j) := fun j ↦ by
    have heq : s7OfHBE rE_Lo j = s7OfHBE rE j := congrArg rTot (rPermLoE298_rElecSub_fix
      (j := ⟨90 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩)
      (Or.inl (by have := j.isLt; dsimp; omega)))
    rw [← heq]; exact hs7_Lo j
  have hs7' : ∀ j : Fin 7, S (s7OfHBE rE' j) :=
    fun j ↦ hrE' _ ⟨⟨74 + 2 * 8 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩, rfl,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩)))⟩
  have dw1 :=
      dynWires_pUnloadLoNPortOnlyAlways1WState88 v rN (padNOfS7 (s7OfHBE rE))
      (qEncOfS7 (s7OfHBE rE)) hrN (fun _ ↦ hs7 _) (hs7 _)
  have dw2 :=
      dynWires_pUnloadLoEAlways1WState_368_noHB7 v rE_Lo (padEOfS7 (s7OfHBE rE_Lo))
      (qEncOfS7 (s7OfHBE rE_Lo))
    hrE_Lo (fun i ↦ hs7_Lo ⟨1 + i.val, by omega⟩) (hs7_Lo _)
  have dw3 : DynWires S (pUnloadSharedHiPortOnly235HBEWState_452 v rN' rE'
      (fun p ↦ rHi' (cHiNSub341 p)) w' (ctrlE_ne_bufLoN_hi235 rHi')) :=
    dynWires_pUnloadSharedHiPortOnly235WState_452_exact v rN' rE'
      (fun p ↦ rHi' (cHiNSub341 p)) w' (ctrlE_ne_bufLoN_hi235 rHi') (s7OfHBE rE')
      (hrN' _ ⟨Fin.mk 1 (rw_lt1 47 6), rfl, Or.inl (by dsimp [routerWidth, basePub]; omega)⟩)
      (fun d ↦ hrN' _ ⟨⟨2 + 6 + d.val, rw_ltIdx2 d⟩, rfl,
        Or.inl (by have := d.isLt; dsimp [basePub]; omega)⟩)
      (fun k ↦ hrN' _ ⟨⟨14 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩, rfl,
        Or.inl (by have := k.isLt; dsimp [basePub]; omega)⟩)
      (fun p k ↦ hrN' _ ⟨⟨110 + 24 * p.val + k.val,
          by have := p.isLt; have := k.isLt; dsimp [routerWidth]; omega⟩, rfl,
        Or.inl (by have := p.isLt; have := k.isLt; dsimp [basePub]; omega)⟩)
      hrE'
      (fun p ↦ hAct (rPermSharedHi298 (rPermScrub338 (cHiNSub341 p)))
        (rPermSharedHi298_rPermScrub338_cHiNSub341_active_w298_mCoin hw p))
      hs7'
  exact ⟨dw2, ⟨cwS, dw3, cwS⟩, dw1⟩

theorem xorNucLoToElecHiNotScrOp_rPermSharedHi298 {n : ℕ} (rTot : QRegister dLayout n) :
    xorNucLoToElecHiNotScrOp (rTot.compose rPermSharedHi298) = xorNucLoToElecHiNotScrOp rTot :=
  xorNucLoToElecHiNotScrOp_congr_of_pot0Eq (rTot.compose rPermSharedHi298) rTot
    (congrArg QRegister.mk (Function.Embedding.ext fun j ↦ congrArg rTot.wires (by
      have hj := j.isLt;
      have hv : (rPot0Layout j).val = (potZeroNEremWireFn 0 pot0_le_690 j).val := rfl
      exact rPermSharedHi298_fix_out (by
        rw [hv, val_potZeroNEremWireFn pot0_le_690]; dsimp; split_ifs <;> omega))))

attribute [local irreducible] systemQubits_frozen ancWOfScr uLoNPortOnlyAlways1Conj uLoEAlways1Conj
  uSharedHiPortOnlyConj uSharedHi235Conj uSwapHi24 uRouterSwapAlwaysLoConj
  uBellLoEAlwaysLoMux_wstate uCopyAll3AlwaysLoMux_wstate xorNucLoToElecHiNotScrOp
  pUnloadLoNPortOnlyAlways1WState88 pUnloadLoEAlways1WState_368
  pUnloadSharedHi235W338_452 in
theorem subspaceStep_Stage5AlwaysLoInPlace_w298_908
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister dLayout n) (R' : Operator (2 ^ n))
    (hR' : SupportedOn (SharedPortBInput341 rTot (rTot.compose rNucSub) (rTot.compose rElecSub)) R')
    (hRel : SupportedOn (Out40Scrub3Rel rTot) R') :
    let rN := rTot.compose rNucSub; let rE := rTot.compose rElecSub
    SubspaceStep (Var := Var)
      ((uBellLoEAlwaysLoMux_wstate rTot).1 *
        (xorNucLoToElecHiNotScrOp rTot *
          ((uSwapHi24 rTot).1 * ((uCopyAll3AlwaysLoMux_wstate rTot).1 *
            ((uRouterSwapAlwaysLoConj rN).1 * ((uRouterSwapAlwaysLoConj rE).1 * R'))))))
      R'
      (pStage5AlwaysLoInPlaceW298_908 v rTot) := by
  intro rN rE; let rE_Lo := (rTot.compose rPermLoE298).compose rElecSub;
  let rE235 := rTot.compose rElecHi235
  let cHiN := fun p ↦ rTot (cHiNSub341 p)
  let w :=
      SharedPortBWiring.ofValidMuxD1_341 validMuxD1Stage2Regs_sub cHiNSub341_ne_rCtrlLo_rNucSub
      cHiNSub341_ne_rCtrlLo_rElecSub rTot; let w235 :=
                                             sharedPortBWiring_hi235 rTot;
                                             let rHi :=
                                             rTot.compose rPermSharedHi298;
                                             let rN_Hi :=
                                             rHi.compose rNucSub;
                                             let rE235_Hi := rHi.compose rElecHi235
  let cHiN_Hi := fun p ↦ rHi (cHiNSub341 p)
  let w235_Hi := sharedPortBWiring_hi235 rHi;
  let hs := stage5PortOnlyScratch_s7OfHBE validMuxD1Stage2Regs_sub rTot;
  let hs_Lo :=
      stage5PortOnlyScratch_s7OfHBE validMuxD1Stage2Regs_sub (rTot.compose rPermLoE298); obtain
      ⟨hPadN, hQN⟩ := hs.padN_disj_loN; obtain ⟨hPadE_Lo, hQE_Lo⟩ :=
      hs_Lo.padE_disj_loE; let X₁ := uLoNPortOnlyAlways1Conj rN * R'
  have sLoN : SubspaceStep (Var := Var) X₁ R'
      (pUnloadLoNPortOnlyAlways1WState88 v rN (padNOfS7 (s7OfHBE rE)) (qEncOfS7 (s7OfHBE rE))) :=
    subspaceStep_pUnloadLoNPortOnlyAlways1WState88 v rN
      (padNOfS7 (s7OfHBE rE)) (qEncOfS7 (s7OfHBE rE)) hs.disjLoN
      (fun i ↦ ⟨fun b ↦ ((hPadN i).1 b).1, (hPadN i).2⟩)
      ⟨fun b ↦ (hQN.1 b).1, hQN.2⟩ R'
      (fun A B hAB ↦ hR' A B fun β hβ ↦ by
        obtain ⟨hC0N, hPLoN, _, _, _⟩ := facts_of_zeroGatedSorted (by omega) rN hβ.2.1
        have hs0 : ∀ j : Fin 7, β (s7OfHBE rE j) = 0 :=
          fun j ↦ (hβ.1.1.2.2.2.1 ⟨j.val, by omega⟩).2.2.2
        exact hAB β ⟨hC0N, fun _ ↦ hs0 _, hs0 _, hPLoN, fun k ↦ (hβ.2.1.1.2.2.2.1 k).1⟩)
  let P_LoE : BitAssignment n → Prop := fun δ ↦
    (∀ q : Fin 187, δ (rCtrlLo rE_Lo q) = 0) ∧
    (∀ i : Fin (192 - 187), δ (padEOfS7 (s7OfHBE rE_Lo) i) = 0) ∧
    δ (qEncOfS7 (s7OfHBE rE_Lo)) = 0 ∧ UnloadLoPred rE_Lo δ ∧
    (∀ k : Fin 24, δ (rBufLo rE_Lo k) = 0) ∧ (∀ k : Fin 24, δ (rHA rE_Lo k) = 0)
  have pLoE_congr : ∀ {δ₁ δ₂ : BitAssignment n},
      (∀ j (hj : j.val < 42 ∨ (66 ≤ j.val ∧ j.val < 97) ∨ (4624 ≤ j.val ∧ j.val < 4811)),
        δ₁ (rE_Lo j) = δ₂ (rE_Lo j)) → P_LoE δ₂ → P_LoE δ₁ := by
    intro δ₁ δ₂ hEq ⟨hc0, hpad0, hq0, hPLo, hB0, hH0⟩
    have hs7Eq : ∀ j : Fin 7, δ₁ (s7OfHBE rE_Lo j) = δ₂ (s7OfHBE rE_Lo j) := fun j ↦
      hEq ⟨90 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩
        (Or.inr (Or.inl ⟨by dsimp; omega, by have := j.isLt; dsimp; omega⟩))
    have hh1 := hEq ⟨0, rw_lt0 187 8⟩ (Or.inl (by dsimp; omega))
    have hi1 : ∀ d : Fin 8, δ₁ (rIdx1 rE_Lo d) = δ₂ (rIdx1 rE_Lo d) :=
      fun d ↦ hEq ⟨2 + d.val, rw_ltIdx1 d⟩ (Or.inl (by have := d.isLt; dsimp; omega))
    exact ⟨fun q ↦ (hEq ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩
              (Or.inr (Or.inr ⟨by dsimp [basePub]; omega,
                by have := q.isLt; dsimp [basePub]; omega⟩))).trans (hc0 q),
           fun i ↦ (hs7Eq ⟨1 + i.val, by omega⟩).trans (hpad0 i),
           (hs7Eq _).trans hq0,
           ⟨(SplitRouter47_187.idxValD_congr hi1).trans_lt hPLo.1,
            fun hz ↦ (SplitRouter47_187.idxValD_congr hi1).trans (hPLo.2 (hh1.symm.trans hz))⟩,
           fun k ↦ (hEq ⟨18 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩
              (Or.inl (by have := k.isLt; dsimp; omega))).trans (hB0 k),
           fun k ↦ (hEq ⟨66 + k.val, rw_ltHA 187 8 k⟩
              (Or.inr (Or.inl ⟨by dsimp; omega, by have := k.isLt; dsimp; omega⟩))).trans (hH0 k)⟩
  have pubNFix : ∀ i : Fin (routerWidth 47 6), i.val < 1238 → rN_Hi i = rN i := fun i hi ↦ by
    have hv : (rNucSub i).val = (nucSubWireFn i).val := rfl
    exact congrArg rTot (rPermSharedHi298_fix_out
        (by rw [hv, val_nucSubWireFn]; split_ifs <;> omega))
  have elec235Fix : ∀ j : Fin (routerWidth 187 8), (j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 66) ∨ j.val =
      78 ∨ (90 ≤ j.val ∧ j.val < 97) ∨ (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧ j.val <
      4803)) → rE235_Hi j = rE235 j := fun j hj ↦
      congrArg rTot (rPermSharedHi298_sharedHi235ElecFootprint_fix_lt4803 hj).2
  have pubEq235 : ∀ {j : Fin (routerWidth 187 8)}, (j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 4602)) →
      rE235 j = rE j := fun hj ↦
    congrArg rTot (rElecHi235_eq_of_not_swap (by rcases hj with h | h <;> omega))
  have pubEqLo : ∀ {j : Fin (routerWidth 187 8)}, (j.val < 97 ∨ (114 ≤ j.val ∧ j.val < 4602)) →
      rE_Lo j = rE j := fun hj ↦ congrArg rTot (rPermLoE298_rElecSub_fix hj)
  have notModLoN_wt : ∀ {wt : Wire dLayout}, 5616 ≤ wt.val → ¬ (5755 ≤ wt.val ∧ wt.val < 5779) →
      ∀ {u : Wire n}, ((∃ b : Fin 24, u = rBufLo rN b) ∨ ∃ (p : Fin 47)
      (b : Fin 24), u = rSys rN p b) → rTot wt ≠ u := by
    rintro wt hge hnb u (⟨b, rfl⟩ | ⟨p, b, rfl⟩) e
    · have hv := congrArg Fin.val (rTot.wires.injective
        (e.trans (congrArg rTot (pot0_routerSub_dLayout_eqs.2.2.2.1 b))))
      rw [val_rBufLo_nuc b] at hv; have := b.isLt; omega
    · have hv :=
          congrArg Fin.val (rTot.wires.injective e); change wt.val =
          (nucSubWireFn ⟨110 + 24 * p.val + b.val, _⟩).val at hv
      rw [val_nucSubWireFn] at hv; have := p.isLt;
      have := b.isLt; dsimp at hv; split_ifs at hv <;> omega
  have notModLoN_N : ∀ (i : Fin (routerWidth 47 6)), i.val < 14 → ∀ {u : Wire n},
      ((∃ b : Fin 24, u = rBufLo rN b) ∨ ∃ (p : Fin 47) (b : Fin 24), u = rSys rN p b) → rN i ≠
      u := by
    rintro i hi u (⟨b, rfl⟩ | ⟨p, b, rfl⟩)
    · exact rr_ne rN (by have := b.isLt; dsimp [routerWidth]; omega)
    · exact rr_ne rN (by have := p.isLt; have := b.isLt; dsimp [routerWidth]; omega)
  have hSuppX1_all : SupportedOn (fun α ↦ (SharedHi235Pred rN_Hi rE235_Hi cHiN_Hi α ∧ ∀ j : Fin 7,
      α (s7OfHBE rE235_Hi j) = 0) ∧ Out40Scrub3Rel rHi α ∧ SharedHi235Pred rN rE235 cHiN α ∧
      P_LoE α) X₁ := by
    refine supportedOn_preserves_uLoNPortOnlyAlways1Conj rN
      (fun {u} hu α val ⟨⟨hHi1, hs7Hi⟩, hRelHi, hHi0, hPLoE_α⟩ ↦ ?_)
      (fun A B hAB ↦ (supportedOn_and hR' hRel) A B fun β ⟨hβ, hrβ⟩ ↦ ?_)
    · have uE235 : ∀ j (hj : j.val < 4602 ∨ (4624 ≤ j.val ∧ j.val < 4811)),
          Function.update α u val (rE235 j) = α (rE235 j) :=
        fun j hj ↦ Function.update_of_ne (rElecHi235_ne_loNSub rTot hj hu) _ _
      have uELo : ∀ j (hj : j.val < 97 ∨ (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧ j.val <
          4811)), Function.update α u val (rE_Lo j) = α (rE_Lo j) := fun j hj ↦
          Function.update_of_ne (rElecLo298_ne_loNSub rTot hj hu) _ _
      have uN : ∀ i (hi : i.val < 14), Function.update α u val (rN i) = α (rN i) := fun i hi ↦
          Function.update_of_ne (notModLoN_N i hi hu) _ _
      have uE235Hi : ∀ j (hj : j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 66) ∨ j.val = 78 ∨
          (90 ≤ j.val ∧ j.val < 97) ∨
          (114 ≤ j.val ∧ j.val < 4602) ∨ (4624 ≤ j.val ∧ j.val < 4811)),
          Function.update α u val (rE235_Hi j) = α (rE235_Hi j) :=
        fun j hj ↦ by
          by_cases h4803 : 4803 ≤ j.val ∧ j.val < 4811
          · have hEq0 : rElecHi235 j = rElecSub j := rElecHi235_eq_of_not_swap (by omega)
            have hrk : privRank454Sub (j.val - 4602) = j.val - 4608 := by
              rw [privRank454Sub_of_6_209 (by omega) (by omega)]; omega
            have hv0 : (rElecSub j).val = 6013 + (j.val - 4803) := by
              have hv1 : (rElecSub j).val = (elecSubWireFn j).val := rfl
              rw [hv1, val_elecSubWireFn, hrk]; split_ifs <;> omega
            have hbds : 5616 ≤ (rPermSharedHi298 (rElecHi235 j)).val ∧
                ¬ (5755 ≤ (rPermSharedHi298 (rElecHi235 j)).val ∧
                (rPermSharedHi298 (rElecHi235 j)).val < 5779)
                := by
              rw [hEq0, val_rPermSharedHi298, hv0]; unfold permSharedHi298Val; split_ifs <;> omega
            exact Function.update_of_ne (notModLoN_wt hbds.1 hbds.2 hu) _ _
          · rw [elec235Fix j (by rcases hj with h | h | h | h | h | h <;> omega)]
            exact uE235 j (by rcases hj with h | h | h | h | h | h <;> omega)
      have uNHi : ∀ i (hi : i.val < 14), Function.update α u val (rN_Hi i) = α (rN_Hi i) :=
        fun i hi ↦ by
          rw [pubNFix i (by omega)]
          exact uN i hi
      have uCHiN : ∀ p : Fin 47, Function.update α u val (cHiN p) = α (cHiN p) := fun p ↦
        Function.update_of_ne (by
          rcases hu with ⟨b, rfl⟩ | ⟨p', b, rfl⟩
          · exact fun e ↦ w.cHiN_notModN p ⟨b, Or.inl e⟩
          · exact fun e ↦ w.cHiN_notModN p
              ⟨b,
                  Or.inr (Or.inr (Or.inr (Or.inr ⟨p',
                  e.trans (planeOfRouter_sys rN b p').symm⟩)))⟩) _ _
      have uCHiN_Hi : ∀ p : Fin 47, Function.update α u val (cHiN_Hi p) = α (cHiN_Hi p) := fun p ↦
          by
        have hp := p.isLt
        have hs0 : (5680 ≤ (cHiNSub341 p).val ∧ (cHiNSub341 p).val < 5692) ∨
            (6021 ≤ (cHiNSub341 p).val ∧ (cHiNSub341 p).val < 6056) := by
          rw [val_cHiNSub341]; split_ifs <;> omega
        have hbds : 5616 ≤ (rPermSharedHi298 (cHiNSub341 p)).val ∧
            ¬ (5755 ≤ (rPermSharedHi298 (cHiNSub341 p)).val ∧
            (rPermSharedHi298 (cHiNSub341 p)).val < 5779)
            := by rw [val_rPermSharedHi298]; unfold permSharedHi298Val; split_ifs <;> omega
        exact Function.update_of_ne (notModLoN_wt hbds.1 hbds.2 hu) _ _
      have uOutHi {wt : Wire dLayout} {v : ℕ} (hv : wt.val = v)
          (h1 : 5715 ≤ v := by decide) (h2 : v ≤ 5754 := by decide) :
          Function.update α u val (rHi wt) = α (rHi wt) := by
        rw [show rHi wt = rTot wt from
          congrArg rTot (rPermSharedHi298_fix_out ⟨by omega, by omega, by omega⟩)]
        exact Function.update_of_ne (notModLoN_wt (by omega) (by omega) hu) _ _
      have sharedHi235_upd {rx : QRegister (routerWidth 47 6) n}
          {rEx : QRegister (routerWidth 187 8) n} {cHiNx : Fin 47 → Wire n}
          (uC : ∀ p, Function.update α u val (cHiNx p) = α (cHiNx p))
          (uNx : ∀ i, i.val < 14 → Function.update α u val (rx i) = α (rx i))
          (uEx : ∀ j, (j.val < 18 ∨ (42 ≤ j.val ∧ j.val < 66) ∨ j.val = 78 ∨
              (4624 ≤ j.val ∧ j.val < 4811)) →
            Function.update α u val (rEx j) = α (rEx j))
          (hHi : SharedHi235Pred rx rEx cHiNx α) :
          SharedHi235Pred rx rEx cHiNx (Function.update α u val) :=
        ⟨fun p ↦ (uC p).trans (hHi.1 p),
         fun q ↦ (uEx ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩
           (Or.inr (Or.inr (Or.inr ⟨by dsimp [basePub]; omega,
             by have := q.isLt; dsimp [basePub]; omega⟩)))).trans (hHi.2.1 q),
         unloadHiPred_congr (uNx ⟨1, rw_lt1 47 6⟩ (by decide))
           (fun d ↦ uNx ⟨2 + 6 + d.val, rw_ltIdx2 d⟩ (add_fin_lt (a := 8) d (by decide))) hHi.2.2.1,
         unloadHiPred_congr (uEx ⟨1, rw_lt1 187 8⟩ (Or.inl (by decide)))
           (fun d ↦ uEx ⟨2 + 8 + d.val, rw_ltIdx2 d⟩
             (Or.inl (add_fin_lt (a := 10) d (by decide)))) hHi.2.2.2.1,
         fun h1 ↦ (uEx ⟨1, rw_lt1 187 8⟩ (Or.inl (by decide))).trans
           (hHi.2.2.2.2.1 ((uNx ⟨1, rw_lt1 47 6⟩ (by decide)).symm.trans h1)),
         fun k ↦ (uEx ⟨42 + k.val, by have := k.isLt; dsimp [routerWidth]; omega⟩
           (Or.inr (Or.inl ⟨by dsimp; omega,
             by have := k.isLt; dsimp; omega⟩))).trans (hHi.2.2.2.2.2.1 k),
         (uEx ⟨78, rw_ltHA 187 8 ⟨12, by decide⟩⟩
           (Or.inr (Or.inr (Or.inl rfl)))).trans hHi.2.2.2.2.2.2⟩
      refine ⟨⟨sharedHi235_upd uCHiN_Hi uNHi
                 (fun j hj ↦ uE235Hi j (by rcases hj with h | h | h | h <;> omega)) hHi1,
               fun j ↦ (uE235Hi ⟨90 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩
                 (Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega,
                   by have := j.isLt; dsimp; omega⟩))))).trans (hs7Hi j)⟩,
        by
          dsimp only [Out40Scrub3Rel]
          rw [uOutHi val_wOut32, uOutHi val_wOut1, uOutHi val_wOut15, uOutHi val_wOut34,
              uOutHi val_wOut0, uOutHi val_wOut14, uOutHi val_wOut35]
          exact hRelHi,
        sharedHi235_upd uCHiN uN
          (fun j hj ↦ uE235 j (by rcases hj with h | h | h | h <;> omega)) hHi0,
        pLoE_congr (fun j hj ↦ uELo j (Or.elim hj (fun h ↦ Or.inl (Nat.lt_trans h (by decide)))
          (fun h2 ↦ Or.elim h2 (fun h ↦ Or.inl h.2) (fun h ↦ Or.inr (Or.inr h))))) hPLoE_α⟩
    · obtain ⟨⟨hcN_Hi, _, hPHiN_Hi, _, _, _, _⟩, _⟩ :=
        sharedHiPortOnlyPred_rPermSharedHi298_of_sharedPortB341 rTot hβ
      obtain ⟨_, hPLoE, hPHiE, _, _⟩ := facts_of_zeroGatedSorted (by omega) rE hβ.1
      obtain ⟨hC0N, hPLoN, hPHiN, _, _⟩ := facts_of_zeroGatedSorted (by omega) rN hβ.2.1
      have hcE235 : ∀ q : Fin 187, β (rCtrlLo rE235 q) = 0 :=
          rCtrlLo_rElecHi235_zero_of_sharedPortB341 rTot hβ
      have hcE235_Hi : ∀ q : Fin 187, β (rCtrlLo rE235_Hi q) = 0 := fun q ↦ by
        have hqLt := q.isLt
        by_cases hq179 : q.val < 179
        · rw [show rCtrlLo rE235_Hi q = rCtrlLo rE235 q from
            elec235Fix ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by dsimp [basePub]; omega,
                  by dsimp [basePub]; omega⟩)))))]
          exact hcE235 q
        · have hEq235 : rCtrlLo rElecHi235 q = rCtrlLo rElecSub q :=
            rElecHi235_eq_of_not_swap (j := ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩)
              (by dsimp [basePub]; omega)
          have hvC := val_rCtrlLo_rElecSub_w298 q
          rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega)] at hvC
          change β (rTot (rPermSharedHi298 (rCtrlLo rElecHi235 q))) = 0; rw [hEq235]
          exact zSwapped_rPermSharedHi298 rTot hβ (w := rCtrlLo rElecSub q) (by omega) (by omega)
      have raw2Eq235 : rRawHas2 rE235 = rRawHas2 rE :=
        pubEq235 (j := ⟨1, rw_lt1 187 8⟩) (Or.inl (by decide))
      have raw2Eq235Hi : rRawHas2 rE235_Hi = rRawHas2 rE235 :=
        elec235Fix ⟨1, rw_lt1 187 8⟩ (Or.inl (by decide))
      have hPHiE235 : UnloadHiPred rE235 β :=
        unloadHiPred_router_congr raw2Eq235
          (fun d ↦ pubEq235 (j := ⟨2 + 8 + d.val, rw_ltIdx2 d⟩)
            (Or.inl (add_fin_lt (a := 10) d (by decide)))) hPHiE
      have hPHiE235_Hi : UnloadHiPred rE235_Hi β :=
        unloadHiPred_router_congr raw2Eq235Hi
          (fun d ↦ elec235Fix ⟨2 + 8 + d.val, rw_ltIdx2 d⟩
            (Or.inl (add_fin_lt (a := 10) d (by decide)))) hPHiE235
      have raw2NEqHi : rRawHas2 rN_Hi = rRawHas2 rN := pubNFix ⟨1, rw_lt1 47 6⟩ (by decide)
      have hq0_235 : β (qScrNotE rE235) = 0 :=
        (congrArg β (pubEq235 (j := ⟨78, rw_ltHA 187 8 ⟨12, by decide⟩⟩)
          (Or.inr ⟨by decide, by decide⟩))).trans (hβ.1.1.2.2.2.1 ⟨12, by decide⟩).2.2.1
      have hq0_235Hi : β (qScrNotE rE235_Hi) = 0 :=
        (congrArg β (elec235Fix ⟨78, rw_ltHA 187 8 ⟨12, by decide⟩⟩
          (Or.inr (Or.inr (Or.inl rfl))))).trans hq0_235
      have hBufE0_235 (k : Fin 24) : β (rBufHi rE235 k) = 0 :=
        (congrArg β (pubEq235 (j := ⟨42 + k.val, add_fin_lt (a := 42) k (by decide)⟩)
          (Or.inr ⟨Nat.le_add_right 42 _, add_fin_lt (a := 42) k (by decide)⟩))).trans
          (hβ.1.1.2.2.2.1 k).2.1
      have hBufE0_235Hi (k : Fin 24) : β (rBufHi rE235_Hi k) = 0 :=
        (congrArg β (elec235Fix ⟨42 + k.val, add_fin_lt (a := 42) k (by decide)⟩
          (Or.inr (Or.inl ⟨Nat.le_add_right 42 _, add_fin_lt (a := 42) k (by decide)⟩)))).trans
          (hBufE0_235 k)
      have hs0 (j : Fin 7) : β (s7OfHBE rE j) = 0 := (hβ.1.1.2.2.2.1 ⟨j.val, by omega⟩).2.2.2
      have hs7_235Hi (j : Fin 7) : β (s7OfHBE rE235_Hi j) = 0 :=
        (congrArg β ((elec235Fix ⟨90 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩
          (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨Nat.le_add_right 90 _, add_fin_lt (a := 90) j (by decide)⟩))))).trans
          (congrFun (s7OfHBE_hi235_eq rTot) j))).trans (hs0 j)
      have hs0_Lo (j : Fin 7) : β (s7OfHBE rE_Lo j) = 0 :=
        (congrArg β (pubEqLo (j := ⟨90 + j.val, rw_ltHB 187 8 ⟨j.val, by omega⟩⟩)
          (Or.inl (add_fin_lt (a := 90) j (by decide))))).trans (hs0 j)
      have idx1ValLo : idxValD (rIdx1 rE_Lo) β = idxValD (rIdx1 rE) β :=
        SplitRouter47_187.idxValD_congr fun d ↦ congrArg β (pubEqLo
          (j := ⟨2 + d.val, rw_ltIdx1 d⟩) (Or.inl (add_fin_lt (a := 2) d (by decide))))
      exact hAB β ⟨hC0N, hPLoN,
        ⟨⟨hcN_Hi, hcE235_Hi, hPHiN_Hi, hPHiE235_Hi,
          fun h1 ↦ (congrArg β (raw2Eq235Hi.trans raw2Eq235)).trans
            (hβ.2.2.2.2 ((congrArg β raw2NEqHi).symm.trans h1)),
          hBufE0_235Hi, hq0_235Hi⟩, hs7_235Hi⟩,
        (rPermSharedHi298_out40Scrub3Rel_iff rTot β).mpr hrβ,
        ⟨hβ.2.2.1, hcE235, hPHiN, hPHiE235,
         fun h1 ↦ (congrArg β raw2Eq235).trans (hβ.2.2.2.2 h1), hBufE0_235, hq0_235⟩,
        ⟨rCtrlLo_rPermLoE298_zero_of_sharedPortB341 rTot hβ,
         fun i ↦ hs0_Lo ⟨1 + i.val, by omega⟩, hs0_Lo _,
         ⟨idx1ValLo.trans_lt hPLoE.1, fun hz ↦ idx1ValLo.trans
           (hPLoE.2 ((congrArg β
             (pubEqLo (j := ⟨0, rw_lt0 187 8⟩) (Or.inl (by decide)))).symm.trans
             hz))⟩,
         fun k ↦ (congrArg β (pubEqLo (j := ⟨18 + k.val, add_fin_lt (a := 18) k (by decide)⟩)
           (Or.inl (add_fin_lt (a := 18) k (by decide))))).trans (hβ.1.1.2.2.2.1 k).1,
         fun k ↦ (congrArg β (pubEqLo (j := ⟨66 + k.val, rw_ltHA 187 8 k⟩)
           (Or.inl (add_fin_lt (a := 66) k (by decide))))).trans (hβ.1.1.2.2.2.1 k).2.2.1⟩⟩
  have hUHiPerm : uSharedHiPortOnlyConj rN_Hi rE235_Hi cHiN_Hi w235_Hi * X₁ =
      uSharedHiPortOnlyConj rN rE235 cHiN w235 * X₁ := by
    refine hSuppX1_all _ _ fun α ⟨⟨hHi1, _⟩, _, hHi0, _⟩ ↦ ?_
    rw [ket_sr_eq_xm,
        uSharedHiPortOnlyConj_mulVec_ket rN_Hi rE235_Hi cHiN_Hi w235_Hi hHi1.1 hHi1.2.1 hHi1.2.2.1
        hHi1.2.2.2.1,
        uSharedHiPortOnlyConj_mulVec_ket rN rE235 cHiN w235 hHi0.1 hHi0.2.1 hHi0.2.2.1 hHi0.2.2.2.1]
    have hBufEq : rBufHi rE235_Hi = rBufHi rE235 := funext fun b ↦
      elec235Fix ⟨42 + b.val, by have := b.isLt; dsimp [routerWidth]; omega⟩
        (Or.inr (Or.inl ⟨by dsimp; omega, by have := b.isLt; dsimp; omega⟩))
    have hCN : cOfSortedHi rN_Hi α = cOfSortedHi rN α := by
      funext p; dsimp only [cOfSortedHi, rIdx2, rRawHas2]
      rw [SplitRouter47_187.idxValD_congr fun d ↦
            congrArg α (pubNFix ⟨2 + 6 + d.val, rw_ltIdx2 d⟩ (by have := d.isLt; dsimp; omega)),
          pubNFix ⟨1, rw_lt1 47 6⟩ (by dsimp [routerWidth]; omega)]
    have hCE : cOfSortedHi rE235_Hi α = cOfSortedHi rE235 α := by
      funext q; dsimp only [cOfSortedHi, rIdx2, rRawHas2]
      rw [SplitRouter47_187.idxValD_congr fun d ↦
            congrArg α (elec235Fix ⟨2 + 8 + d.val, rw_ltIdx2 d⟩
                (Or.inl (by have := d.isLt; dsimp; omega))),
          elec235Fix ⟨1, rw_lt1 187 8⟩ (Or.inl (by dsimp [routerWidth]; omega))]
    have hSysEq : (fun b : Fin 24 ↦ appendFin (fun p ↦ rSys rN_Hi p b)
        (fun q ↦ rSys rE235_Hi q b)) = (fun b : Fin 24 ↦ appendFin (fun p ↦ rSys rN p b)
        (fun q ↦ rSys rE235 q b)) := by
      funext b i
      rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · rw [appendFin_castAdd, appendFin_castAdd]
        exact pubNFix ⟨110 + 24 * p.val + b.val,
            by have := p.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩
          (by have := p.isLt; have := b.isLt; dsimp; omega)
      · rw [appendFin_natAdd, appendFin_natAdd]
        exact elec235Fix ⟨114 + 24 * q.val + b.val,
            by have := q.isLt; have := b.isLt; dsimp [routerWidth]; omega⟩
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp; omega,
              by have := q.isLt; have := b.isLt; dsimp; omega⟩)))))
    rw [hCN, hCE, fixedSwapVecCirc_congr_w310 hBufEq _ hSysEq _ _,
        fixedFanoutVecCirc_congr_w310 _ hBufEq hSysEq _ _]
  let Z₁ := uSharedHiPortOnlyConj rN rE235 cHiN w235 * X₁;
  let Y := xorNucLoToElecHiNotScrOp rTot * Z₁
  have sHi0 :=
      subspaceStep_pUnloadSharedHi235W338_452 v rHi X₁ (fun A B hAB ↦ hSuppX1_all A B fun α ⟨h1, _,
      _, _⟩ ↦ hAB α h1) (fun A B hAB ↦ hSuppX1_all A B fun α ⟨_, hr, _, _⟩ ↦ hAB α hr)
  dsimp only at sHi0
  have sHi : SubspaceStep (Var := Var) Y X₁ (pUnloadSharedHi235W338_452 v rHi) :=
    subspaceStep_congr_in
        (by dsimp only [Y, Z₁]; rw [← hUHiPerm, ← xorNucLoToElecHiNotScrOp_rPermSharedHi298 rTot])
        sHi0
  have hSuppZ1_LoE : SupportedOn P_LoE Z₁ := fun A B hAB ↦ by
    dsimp only [Z₁]; rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
    refine hSuppX1_all _ _ fun α ⟨_, _, hHi0, hPLoE_α⟩ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_sr_eq_xm,
        uSharedHiPortOnlyConj_mulVec_ket rN rE235 cHiN w235 hHi0.1 hHi0.2.1 hHi0.2.2.1 hHi0.2.2.2.1,
        ← ket_sr_eq_xm]
    have hSuppSys : ∀ (b : Fin 24) (i : Fin (47 + 187)),
        appendFin (cOfSortedHi rN α) (cOfSortedHi rE235 α) i = 1 →
        PortOnlyHiMod rN rE235 (appendFin (fun p ↦ rSys rN p b) (fun q ↦ rSys rE235 q b) i) :=
            fun b i _ ↦ by
      rcases appendFin_eq i with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · rw [appendFin_castAdd]; exact Or.inr (Or.inl ⟨p, b, rfl⟩)
      · rw [appendFin_natAdd]; exact Or.inr (Or.inr ⟨q, b, rfl⟩)
    exact ((HCNOTSupportedIn.seq
      (hcnotSupportedIn_fixedSwapVec _ 24 _ _ w235.hBTs_NE (fun b ↦ Or.inl ⟨b, rfl⟩) hSuppSys)
      (hcnotSupportedIn_fixedFanoutVec 24 _ _ _ w235.hBTs_NE (fun b ↦
          Or.inl ⟨b, rfl⟩) hSuppSys)).preservesKetPred
      (fun {u} hu δ val hδ ↦ pLoE_congr (fun j hj ↦ Function.update_of_ne
        (fun e ↦ rElecLo298_not_portOnlyHiMod rTot (j := j) hj
          ((portOnlyHiMod_hi235_iff rTot _).mp (by rw [e]; exact hu))) _ _) hδ)
      (preservesKetPred_ket hPLoE_α)) A B hAB
  have hSuppY_LoE : SupportedOn P_LoE Y := fun A B hAB ↦ by
    dsimp only [Y]; rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
    refine hSuppZ1_LoE _ _ fun δ hδ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_sr_eq_xm,
        xorNucLoToElecHiNotScrOp_mulVec_ket, ← ket_sr_eq_xm]
    obtain ⟨_, xOth⟩ := xorNucLoToElecHiNotScrBits_apply rTot δ
    have hEB_Lo : ∀ b : Fin 24, rBufHi rE_Lo b = rTot (rBufHi rElecLayout b) := fun b ↦
      (pubEqLo (j := ⟨42 + b.val, by have := b.isLt; dsimp [routerWidth]; omega⟩)
        (Or.inl (by have := b.isLt; dsimp; omega))).trans
        (congrArg rTot (pot0_routerSub_dLayout_eqs.2.2.2.2 b))
    exact hAB _ (pLoE_congr (fun j hj ↦ xOth _ fun b e ↦ rr_ne rE_Lo
      (by have := b.isLt; have := j.isLt; dsimp [routerWidth] at hj ⊢; omega)
      (e.trans (hEB_Lo b).symm)) hδ)
  have sLoE0 :=
      subspaceStep_pUnloadLoEAlways1WState_368 v rE_Lo (padEOfS7 (s7OfHBE rE_Lo))
      (qEncOfS7 (s7OfHBE rE_Lo)) hs_Lo.disjLoE hPadE_Lo hQE_Lo Y hSuppY_LoE
  have hCommXorLoE : uLoEAlways1Conj rE_Lo * Y = xorNucLoToElecHiNotScrOp rTot *
      (uLoEAlways1Conj rE_Lo * Z₁) :=
      comm_uLoEAlways1_xorNucLoToElecHiNotScrOp_w298 rTot Z₁ (fun A B hAB ↦
      hSuppZ1_LoE A B fun δ h ↦ hAB δ ⟨h.1, h.2.2.2.1⟩)
  have hPreEq : uLoEAlways1Conj rE_Lo * Z₁ = (uBellLoEAlwaysLoMux_wstate rTot).1 *
      ((uSwapHi24 rTot).1 * ((uCopyAll3AlwaysLoMux_wstate rTot).1 *
      ((uRouterSwapAlwaysLoConj rN).1 * ((uRouterSwapAlwaysLoConj rE).1 * R')))) := by
    dsimp only [Z₁, X₁]; simp only [← Matrix.mul_assoc]
    refine hR' _ _ fun β hβ ↦ ?_
    have hcLo_ne : ∀ (q : Fin 187) (b : Fin 24),
        rCtrlLo rE_Lo q ≠ rBufLo rN b ∧ rCtrlLo rE_Lo q ≠ rBufHi rE b := fun q b ↦
      ⟨rElecLo298_ne_loNSub rTot (j := ⟨basePub 187 8 + 6 + 2 * 8 + q.val, rw_ltCtrlLo q⟩)
         (Or.inr (Or.inr ⟨by dsimp [basePub]; omega, by have := q.isLt; dsimp [basePub]; omega⟩))
         (Or.inl ⟨b, rfl⟩),
       fun e ↦ rr_ne rE_Lo (by have := q.isLt; have := b.isLt; dsimp [routerWidth, basePub]; omega)
         (e.trans (pubEqLo (j := ⟨42 + b.val, by have := b.isLt; dsimp [routerWidth]; omega⟩)
           (Or.inl (by have := b.isLt; dsimp; omega))).symm)⟩
    have hPreKet := stage5AlwaysLo_preEq_ket_gen rTot rE_Lo rE235 w235 pubEqLo pubEq235 hβ
      (rCtrlLo_rElecHi235_zero_of_sharedPortB341 rTot hβ) (ctrlE_ne_bufLoN_hi235 rTot)
      (rCtrlLo_rPermLoE298_zero_of_sharedPortB341 rTot hβ) hcLo_ne
    dsimp only at hPreKet
    rw [ket_sr_eq_xm]
    simpa only [← Matrix.mulVec_mulVec] using hPreKet
  have hInEq : uLoEAlways1Conj rE_Lo * Y = (uBellLoEAlwaysLoMux_wstate rTot).1 *
      (xorNucLoToElecHiNotScrOp rTot * ((uSwapHi24 rTot).1 * ((uCopyAll3AlwaysLoMux_wstate rTot).1 *
      ((uRouterSwapAlwaysLoConj rN).1 * ((uRouterSwapAlwaysLoConj rE).1 * R')))))
      := by
    rw [hCommXorLoE, hPreEq, ← Matrix.mul_assoc (xorNucLoToElecHiNotScrOp rTot),
        xorNucLoToElecHiNotScrOp_comm_uBellLoELoMux_wstate rTot, Matrix.mul_assoc]
  unfold pStage5AlwaysLoInPlaceW298_908;
  exact (subspaceStep_congr_in hInEq.symm sLoE0).seq (sHi.seq sLoN)
end QuantumComputation.Specs.PhotochemistrySolution.Stage5W298
end

/-!
# Stage-4 Coulomb `Load440_k78` + `M72_0Scrub` + `Pers12Dom168_M72_K123` (`tCoul = 1,036 T`)


1. `PhotochemistrySolution.CoulM72Mid36Opt`:
   - `CoulInnerCorePkgM72`: `M = 72` inner-core interface carrying `hScrI` and `hNNI`.
   - `pInnerM72Mid36_0Scrub` : omits `10 T` `pMidScrub42_m72` whenever `kMid ≤ 36` (e.g.
   `MidOWTap29_244` with `kMid = 29 ≤ 36` ), using `cowp_pUnshift30_mid42_m72` 's `hPoolLt36`
   directly (`440 + 76 + 22 + 258 = 796 T`).
2. `PhotochemistrySolution.Pers12Dom168M72`:
- Self-contained `168 T` persistent-12 domain normalizer (`Pers12Dom168`) specialized to
`(M = 72, kRest = 123)` (`54 + 123 = 177` wires `r[0..176]` ), plus `widenCoulOWScrPkg12` lifting
`kRest = 123` to any `kRest' ≥ 123` (e.g. `kRest = 124` for `Sub63` `Coul18K2` + `MidOWTap29_244` at
`Wp = 204` ).
-/

section
set_option maxRecDepth 8192

namespace QuantumComputation.Specs.PhotochemistrySolution.CoulM72Mid36Opt

open Operator QProg Matrix Circuit Qubit HermitianMat
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (ditePos diteNeg)
/-- `M = 72` inner-core package carrying `hScrI` and `hNNI` for `rScr40PoolIdx72`. -/
structure CoulInnerCorePkgM72 (kMid tInner : ℕ) where
  hMidLE : kMid ≤ 72
  pInner : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ},
    Var → (wG wScr wNN : Wire n) → (rIdx7 : QRegister 7 n) → (rK4 : QRegister 4 n) →
    (rJ2 : QRegister 2 n) → (rY36 : QRegister 36 n) → (rPool : QRegister 72 n) →
    ScrGGatedCoreDisj wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool →
    DynamicCircuit Var n → DynamicCircuit Var n
  counts_wires : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} {S : Wire n → Prop}
    (v : Var) (wG wScr wNN : Wire n) (rIdx7 : QRegister 7 n) (rK4 : QRegister 4 n)
    (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n) (rPool : QRegister 72 n)
    (hd : ScrGGatedCoreDisj wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool),
    S wG → S wScr → S wNN →
    (∀ i, S (rIdx7 i)) → (∀ i, S (rK4 i)) → (∀ i, S (rJ2 i)) →
    (∀ b, S (rY36 b)) → (∀ u, S (rPool u)) →
    ∀ mid : DynamicCircuit Var n,
      (pInner v wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd mid).count .T = tInner + mid.count .T ∧
      (pInner v wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd mid).count .TOFF = mid.count .TOFF ∧
      (DynWires S mid → DynWires S (pInner v wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd mid))
  step2_pers : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (wG wScr wNN : Wire n) (rIdx7 : QRegister 7 n) (rK4 : QRegister 4 n)
    (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n) (rPool : QRegister 72 n)
    (hd : ScrGGatedCoreDisj wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool)
    (_ : ∀ i, wScr ≠ rIdx7 i) (_ : ∀ i, wNN ≠ rIdx7 i)
    (mid : DynamicCircuit Var n)
    (stPre stPost : BitAssignment n → BitAssignment n)
    (phPre phPost : BitAssignment n → ZMod 2)
    (cFn : BitAssignment n → Fin 3 → Fin 2048) (d2Fn : BitAssignment n → ℕ),
    (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → d2Fn δ < 262144) →
    (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPost δ wG = stPre δ wG) →
    (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPost δ wScr = stPre δ wScr) →
    (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPost δ wNN = stPre δ wNN) →
    (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      (stPre δ wScr == 1) = false → (stPre δ wNN == 1) = false) →
    (∀ δ (i : Fin 7), (∀ k : Fin W, δ (rWork k) = 0) →
      stPre δ (rIdx7 i) = if (idx7OfParts (evenOctIdxT10K (stPre δ wNN == 1)
          (d2Fn δ))).testBit i.val
        then 1 else 0) →
    (∀ δ (i : Fin 7), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rIdx7 i) = stPre δ (rIdx7 i)) →
    (∀ δ (i : Fin 4), (∀ k : Fin W, δ (rWork k) = 0) →
      stPre δ (rK4 i) = if (evenOctIdxT10K (stPre δ wNN == 1)
          (d2Fn δ)).2.2.testBit i.val then 1 else 0) →
    (∀ δ (i : Fin 4), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rK4 i) = stPre δ (rK4 i)) →
    (∀ δ (q : Fin 2), (∀ k : Fin W, δ (rWork k) = 0) →
      let p := evenOctIdxT10K (stPre δ wNN == 1) (d2Fn δ)
      stPre δ (rJ2 q) = if (popBernJ (t11OfParts p) (cFn δ)).testBit q.val then 1 else 0) →
    (∀ δ (q : Fin 2), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rJ2 q) = stPre δ (rJ2 q)) →
    (∀ δ (b : Fin 36), (∀ k : Fin W, δ (rWork k) = 0) → stPre δ (rY36 b) = 0) →
    (∀ δ (b : Fin 36), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rY36 b) = 0) →
    (∀ δ (u : Fin 72), (∀ k : Fin W, δ (rWork k) = 0) → stPre δ (rPool u) = 0) →
    (∀ δ (u : Fin 72), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rPool u) = 0) →
    (∀ stMidPre stMidPost : BitAssignment n → BitAssignment n,
      (∀ δ w, (∀ b : Fin 36, w ≠ rY36 b) → (∀ u : Fin 72, w ≠ rPool u) →
        stMidPre δ w = stPre δ w) →
      (∀ δ w, (∀ b : Fin 36, w ≠ rY36 b) → (∀ u : Fin 72, w ≠ rPool u) →
        stMidPost δ w = stPost δ w) →
      (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
        let yV :=
            if stPre δ wG == 1 then y36PopBernNoClamp word512DualLegLo6 (stPre δ wNN == 1) (d2Fn δ)
            (cFn δ) else 0
        let sh1 := if (stPre δ wScr == 1) && !(stPre δ wNN == 1) then 1 else 0
        natOfZModBits 36 (fun b ↦ stMidPre δ (rY36 b)) / 8 = (yV >>> sh1) / 8 ∧
        (∀ b : Fin 36, stMidPost δ (rY36 b) = stMidPre δ (rY36 b)) ∧
        (stPre δ wG = 0 → ∀ b : Fin 36, stMidPre δ (rY36 b) = 0)) →
      (∀ δ (j : Fin kMid), (∀ k : Fin W, δ (rWork k) = 0) →
        stMidPre δ (rPool ⟨j.val, Nat.lt_of_lt_of_le j.isLt hMidLE⟩) = 0 ∧
        stMidPost δ (rPool ⟨j.val, Nat.lt_of_lt_of_le j.isLt hMidLE⟩) = 0) →
      (∀ δ (u : Fin 72), (∀ k : Fin W, δ (rWork k) = 0) →
        stMidPost δ (rPool u) = stMidPre δ (rPool u)) →
      SubspaceStep (mkKetOpW rWork stMidPre phPre) (mkKetOpW rWork stMidPost phPost) mid) →
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
      (pInner v wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd mid)

/-- `0-Scrub` `M = 72` inner core for `kMid ≤ 36`. -/
def pInnerM72Mid36_0Scrub {Var : Type} [Fintype Var] [DecidableEq Var] {tBasis tBf n : ℕ}
    (pkgQ : QromLoadPkgGenN 10 30 (gGatedShr6Word word512DualLeg))
    (pkgU : QromUnloadPkgGenN 10 30 (gGatedShr6Word word512DualLeg)) (hLoad : pkgQ.kScr ≤ 72 + 6)
    (hUnld : pkgU.kUnload ≤ 72 + 6) (pkgBasis : KpBasis9Pkg tBasis)
    (pkgBf : Butterfly33K9Scr31Pkg tBf) (v : Var) (wG wScr wNN : Wire n) (rIdx7 : QRegister 7 n)
    (rK4 : QRegister 4 n) (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n) (rPool : QRegister 72 n)
    (hd : ScrGGatedCoreDisj wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool) (mid : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
    .seq (pkgQ.pLoad v (rLoad30BorrowY6 hLoad hd.1))
    (.seq (pUnshift30Bf33K9Scr31Wrap72 pkgBasis pkgBf v wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd mid)
    (pkgU.pUnload v (rLoad30BorrowY6 hUnld hd.1)))
theorem pInnerM72Mid36_0Scrub_counts_wires {Var : Type} [Fintype Var] [DecidableEq Var]
    {tBasis tBf n : ℕ} {S : Wire n → Prop}
    (pkgQ : QromLoadPkgGenN 10 30 (gGatedShr6Word word512DualLeg))
    (pkgU : QromUnloadPkgGenN 10 30 (gGatedShr6Word word512DualLeg)) (hLoad : pkgQ.kScr ≤ 72 + 6)
    (hUnld : pkgU.kUnload ≤ 72 + 6) (pkgBasis : KpBasis9Pkg tBasis)
    (pkgBf : Butterfly33K9Scr31Pkg tBf) (v : Var) (wG wScr wNN : Wire n) (rIdx7 : QRegister 7 n)
    (rK4 : QRegister 4 n) (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n) (rPool : QRegister 72 n)
    (hd : ScrGGatedCoreDisj wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool) (hGS : S wG) (hSS : S wScr)
    (hNS : S wNN) (hIS : ∀ i, S (rIdx7 i)) (hKS : ∀ i, S (rK4 i)) (hJS : ∀ i, S (rJ2 i))
    (hYS : ∀ b, S (rY36 b)) (hPS : ∀ u, S (rPool u)) (mid : DynamicCircuit Var n) :
    (pInnerM72Mid36_0Scrub pkgQ pkgU hLoad hUnld pkgBasis pkgBf v wG wScr wNN rIdx7 rK4 rJ2 rY36
    rPool hd mid).count .T = pkgQ.tLoad + pkgU.tUnload + tBasis + tBf + mid.count .T ∧
    (pInnerM72Mid36_0Scrub pkgQ pkgU hLoad hUnld pkgBasis pkgBf v wG wScr wNN rIdx7 rK4 rJ2 rY36
    rPool hd mid).count .TOFF = mid.count .TOFF ∧ (DynWires S mid →
    DynWires S (pInnerM72Mid36_0Scrub pkgQ pkgU hLoad hUnld pkgBasis pkgBf v wG wScr wNN rIdx7 rK4
    rJ2 rY36 rPool hd mid)) := by
  let rQ := rLoad30BorrowY6 hLoad hd.1
  let rU := rLoad30BorrowY6 hUnld hd.1
  let stZ : BitAssignment n → BitAssignment n := fun _ _ ↦ 0
  let mkSt0 := fun {kS : ℕ} (rX : QRegister (10 + 30 + kS) n) (_ : BitAssignment n) (w : Wire n) ↦
    if hm : ∃ j : Fin 30, w = rX ⟨10 + j.val, outWire_lt j.isLt⟩ then
      if (gGatedShr6Word word512DualLeg
        (natOfZModBits 10 (fun _ ↦ (0 : ZMod 2)))).testBit hm.choose.val then 1 else 0
    else (0 : ZMod 2)
  have hMkOut {kS : ℕ} (rX : QRegister (10 + 30 + kS) n) (j : Fin 30) (δ : BitAssignment n) :
      mkSt0 rX δ (rX ⟨10 + j.val, outWire_lt j.isLt⟩) =
        if (gGatedShr6Word word512DualLeg
          (natOfZModBits 10 (fun i ↦ stZ δ (rX ⟨i.val, by omega⟩)))).testBit j.val
        then 1 else 0 := by
    have hex : ∃ j' : Fin 30, rX ⟨10 + j.val, outWire_lt j.isLt⟩ =
        rX ⟨10 + j'.val, outWire_lt j'.isLt⟩ := ⟨j, rfl⟩
    dsimp only [mkSt0, stZ]
    rw [ditePos hex, show hex.choose = j from Fin.ext (Nat.add_left_cancel
      (congrArg Fin.val (rX.wires.injective hex.choose_spec.symm)))]
  have hBorrowS {kS : ℕ} (hS : kS ≤ 72 + 6) (u : Fin (10 + 30 + kS)) :
      S (rLoad30BorrowY6 hS hd.1 u) := by
    change S (fLoad30BorrowY6 hS wG rIdx7 rJ2 rY36 rPool u)
    dsimp only [fLoad30BorrowY6]
    split_ifs <;> first | exact hJS _ | exact hIS _ | exact hGS | exact hYS _ | exact hPS _
  have hQ := pkgQ.step_and_counts v (rWork0 n) rQ stZ (mkSt0 rQ) (fun _ ↦ 0)
    (fun _ _ _ ↦ rfl) (hMkOut rQ) (fun w _ hnot ↦ diteNeg hnot)
  have hU := pkgU.step_and_counts v (rWork0 n) rU stZ (mkSt0 rU) (fun _ ↦ 0)
    (fun _ _ _ ↦ rfl) (hMkOut rU) (fun w _ hnot ↦ diteNeg hnot)
  obtain ⟨tB, fB, wB⟩ := pUnshift30Bf33K9Scr31Wrap72_counts_wires (S := S) pkgBasis pkgBf v
    wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd hSS hNS hIS hKS hYS hPS mid
  unfold pInnerM72Mid36_0Scrub
  dsimp only [DynamicCircuit.count]
  rw [hQ.2.1, tB, hU.2.1, hQ.2.2, fB, hU.2.2]
  exact ⟨by omega, by omega, fun hm ↦ ⟨pkgQ.dynWires S v rQ (hBorrowS hLoad), wB hm,
    pkgU.dynWires S v rU (hBorrowS hUnld)⟩⟩

set_option maxHeartbeats 1600000 in
-- M72 Mid36 persistent-register inner step
attribute [local irreducible] PhotochemistrySolution.FineLegendre.mkKetOpW in
theorem pInnerM72Mid36_0Scrub_step2_pers {Var : Type} [Fintype Var] [DecidableEq Var]
    {kMid tBasis tBf W n : ℕ} [NeZero (2 ^ n)]
    (hkMid36 : kMid ≤ 36)
    (pkgQ : QromLoadPkgGenN 10 30 (gGatedShr6Word word512DualLeg))
    (pkgU : QromUnloadPkgGenN 10 30 (gGatedShr6Word word512DualLeg))
    (hLoad : pkgQ.kScr ≤ 72 + 6) (hUnld : pkgU.kUnload ≤ 72 + 6)
    (pkgBasis : KpBasis9Pkg tBasis) (pkgBf : Butterfly33K9Scr31Pkg tBf)
    (v : Var) (rWork : QRegister W n)
    (wG wScr wNN : Wire n) (rIdx7 : QRegister 7 n) (rK4 : QRegister 4 n)
    (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n) (rPool : QRegister 72 n)
    (hd : ScrGGatedCoreDisj wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool)
    (hScrI : ∀ i, wScr ≠ rIdx7 i) (hNNI : ∀ i, wNN ≠ rIdx7 i)
    (mid : DynamicCircuit Var n)
    (stPre stPost : BitAssignment n → BitAssignment n)
    (phPre phPost : BitAssignment n → ZMod 2)
    (cFn : BitAssignment n → Fin 3 → Fin 2048) (d2Fn : BitAssignment n → ℕ)
    (hd2Lt : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → d2Fn δ < 262144)
    (hGEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPost δ wG = stPre δ wG)
    (hScrEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPost δ wScr = stPre δ wScr)
    (hNNEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPost δ wNN = stPre δ wNN)
    (hValid : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      (stPre δ wScr == 1) = false → (stPre δ wNN == 1) = false)
    (hIdx7Pre : ∀ δ (i : Fin 7), (∀ k : Fin W, δ (rWork k) = 0) →
      stPre δ (rIdx7 i) = if (idx7OfParts (evenOctIdxT10K (stPre δ wNN == 1)
          (d2Fn δ))).testBit i.val
        then 1 else 0)
    (hIdx7Eq : ∀ δ (i : Fin 7), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rIdx7 i) =
        stPre δ (rIdx7 i))
    (hK4Pre : ∀ δ (i : Fin 4), (∀ k : Fin W, δ (rWork k) = 0) →
      stPre δ (rK4 i) = if (evenOctIdxT10K (stPre δ wNN == 1)
          (d2Fn δ)).2.2.testBit i.val then 1 else 0)
    (hK4Eq : ∀ δ (i : Fin 4), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rK4 i) = stPre δ (rK4 i))
    (hJ2Pre : ∀ δ (q : Fin 2), (∀ k : Fin W, δ (rWork k) = 0) →
      let p := evenOctIdxT10K (stPre δ wNN == 1) (d2Fn δ)
      stPre δ (rJ2 q) = if (popBernJ (t11OfParts p) (cFn δ)).testBit q.val then 1 else 0)
    (hJ2Eq : ∀ δ (q : Fin 2), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rJ2 q) = stPre δ (rJ2 q))
    (hY0Pre : ∀ δ (b : Fin 36), (∀ k : Fin W, δ (rWork k) = 0) → stPre δ (rY36 b) = 0)
    (hY0Post : ∀ δ (b : Fin 36), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rY36 b) = 0)
    (hP0Pre : ∀ δ (u : Fin 72), (∀ k : Fin W, δ (rWork k) = 0) → stPre δ (rPool u) = 0)
    (hP0Post : ∀ δ (u : Fin 72), (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (rPool u) = 0)
    (hMidCB : ∀ stMidPre stMidPost : BitAssignment n → BitAssignment n,
      (∀ δ w, (∀ b : Fin 36, w ≠ rY36 b) → (∀ u : Fin 72, w ≠ rPool u) →
        stMidPre δ w = stPre δ w) →
      (∀ δ w, (∀ b : Fin 36, w ≠ rY36 b) → (∀ u : Fin 72, w ≠ rPool u) →
        stMidPost δ w = stPost δ w) →
      (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
        let yV :=
            if stPre δ wG == 1 then y36PopBernNoClamp word512DualLegLo6 (stPre δ wNN == 1) (d2Fn δ)
            (cFn δ) else 0
        let sh1 := if (stPre δ wScr == 1) && !(stPre δ wNN == 1) then 1 else 0
        natOfZModBits 36 (fun b ↦ stMidPre δ (rY36 b)) / 8 = (yV >>> sh1) / 8 ∧
        (∀ b : Fin 36, stMidPost δ (rY36 b) = stMidPre δ (rY36 b)) ∧
        (stPre δ wG = 0 → ∀ b : Fin 36, stMidPre δ (rY36 b) = 0)) →
      (∀ δ (j : Fin kMid), (∀ k : Fin W, δ (rWork k) = 0) →
        stMidPre δ (rPool ⟨j.val,
            Nat.lt_of_lt_of_le j.isLt (Nat.le_trans hkMid36 (by decide : 36 ≤ 72))⟩) = 0 ∧
        stMidPost δ (rPool ⟨j.val,
            Nat.lt_of_lt_of_le j.isLt (Nat.le_trans hkMid36 (by decide : 36 ≤ 72))⟩) = 0) →
      (∀ δ (u : Fin 72), (∀ k : Fin W, δ (rWork k) = 0) →
        stMidPost δ (rPool u) = stMidPre δ (rPool u)) →
      SubspaceStep (mkKetOpW rWork stMidPre phPre) (mkKetOpW rWork stMidPost phPost) mid) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
      (pInnerM72Mid36_0Scrub pkgQ pkgU hLoad hUnld pkgBasis pkgBf v
        wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd mid) := by
  let isNNFn : BitAssignment n → Bool := fun δ ↦ stPre δ wNN == 1
  let gFn : BitAssignment n → Bool := fun δ ↦ stPre δ wG == 1
  let idx7Fn : BitAssignment n → ℕ := fun δ ↦ idx7OfParts (evenOctIdxT10K (isNNFn δ) (d2Fn δ))
  let jFn : BitAssignment n → ℕ := fun δ ↦
      popBernJ (t11OfParts (evenOctIdxT10K (isNNFn δ) (d2Fn δ))) (cFn δ)
  let x32Fn : BitAssignment n → ℕ := fun δ ↦ rootG90X32 (gFn δ) (idx7Fn δ) (jFn δ)
  let stQPre : BitAssignment n → BitAssignment n := fun δ ↦
      rootG90StQ (rootG90X30 (gFn δ) (idx7Fn δ) (jFn δ)) rY36 (stPre δ)
  let stQPost : BitAssignment n → BitAssignment n := fun δ ↦
      rootG90StQ (rootG90X30 (gFn δ) (idx7Fn δ) (jFn δ)) rY36 (stPost δ)
  have hIdx7Lt : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → idx7Fn δ < 128 := fun δ hz ↦
      (parts_popBern_bounds (isNNFn δ) (hd2Lt δ hz)).1
  have hJLt : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → jFn δ < 4 := fun δ _ ↦
      popBernJ_lt_four _ (cFn δ)
  have hSidePre :=
    rootG90Side_eval pkgQ pkgU hLoad hUnld v rWork wG rIdx7 rK4 rJ2 rY36 rPool hd.1
      stPre gFn idx7Fn jFn hIdx7Lt hJLt (fun _ _ ↦ rfl) hIdx7Pre hJ2Pre hY0Pre hP0Pre
  have hx32 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → x32Fn δ < 2 ^ 32 :=
      hSidePre.1; have hLoadPre := hSidePre.2.1; have hNotQPre :=
                                                   hSidePre.2.2.2.1;
                                                   have hYQPre :=
                                                   hSidePre.2.2.2.2.1;
                                                   have hPoolQPre := hSidePre.2.2.2.2.2
  have hSidePost :=
    rootG90Side_eval pkgQ pkgU hLoad hUnld v rWork wG rIdx7 rK4 rJ2 rY36 rPool hd.1
      stPost gFn idx7Fn jFn hIdx7Lt hJLt
      (fun δ hz ↦ by dsimp only [gFn]; rw [hGEq δ hz])
      (fun δ i hz ↦ (hIdx7Eq δ i hz).trans (hIdx7Pre δ i hz))
      (fun δ q hz ↦ (hJ2Eq δ q hz).trans (hJ2Pre δ q hz))
      hY0Post hP0Post
  have hUnldPost := hSidePost.2.2.1; have hNotQPost := hSidePost.2.2.2.1;
  have hYQPost := hSidePost.2.2.2.2.1; have hPoolQPost := hSidePost.2.2.2.2.2
  have hStQLo6 (x : ℕ) (st0 : BitAssignment n) {b : Fin 36} (hb : b.val < 6) :
      rootG90StQ x rY36 st0 (rY36 b) = st0 (rY36 b) :=
    writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ by
      have hv := congrArg Fin.val (rY36.wires.injective hj)
      dsimp [rYHi30] at hj hv; omega
  have hYLo6Pre : ∀ δ (b : Fin 36), b.val < 6 → (∀ k : Fin W, δ (rWork k) = 0) →
      stQPre δ (rY36 b) = 0 := fun δ b hb hz ↦ (hStQLo6 _ (stPre δ) hb).trans (hY0Pre δ b hz)
  have hYLo6Post : ∀ δ (b : Fin 36), b.val < 6 → (∀ k : Fin W, δ (rWork k) = 0) →
      stQPost δ (rY36 b) = 0 := fun δ b hb hz ↦ (hStQLo6 _ (stPost δ) hb).trans (hY0Post δ b hz)
  have hKVal : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 4 (fun i ↦ stQPre δ (rK4 i)) =
        (evenOctIdxT10K (isNNFn δ) (d2Fn δ)).2.2 := fun δ hz ↦ by
    have hk8 := (parts_popBern_bounds (isNNFn δ) (hd2Lt δ hz)).2.2
    apply Nat.eq_of_testBit_eq; intro k
    by_cases hk : k < 4
    · rw [natOfZModBits_testBit_lt _ hk]; dsimp only [stQPre]
      rw [hNotQPre δ (rK4 ⟨k, hk⟩) (fun b hb ↦ disj_ne (ggCore_KY hd.1) _ b hb),
          hK4Pre δ ⟨k, hk⟩ hz]
      cases (evenOctIdxT10K (isNNFn δ) (d2Fn δ)).2.2.testBit k <;> rfl
    · have hk16 : (evenOctIdxT10K (isNNFn δ) (d2Fn δ)).2.2 < 16 := by omega
      have hp4 : 16 ≤ 2 ^ k :=
                                                            (by decide : 16 ≤ 2 ^ 4).trans
                                                            (Nat.pow_le_pow_right (by omega)
                                                            (by omega))
      rw [Nat.testBit_eq_false_of_lt ((natOfZModBits_lt 4 _).trans_le hp4),
          Nat.testBit_eq_false_of_lt (hk16.trans_le hp4)]
  have hShrEq : ∀ δ,
      (((mask30 (x32Fn δ)) <<< 4) >>> (evenOctIdxT10K (isNNFn δ) (d2Fn δ)).2.2) =
        if stPre δ wG == 1 then
          y36PopBernNoClamp word512DualLegLo6 (isNNFn δ) (d2Fn δ) (cFn δ)
        else 0 := fun δ ↦ by
    dsimp only [x32Fn, rootG90X32, gFn]; split_ifs
    · rw [mask30_shl4_word512DualLeg]; rfl
    · have hm0 : mask30 0 = 0 := rfl; rw [hm0, Nat.zero_shiftLeft, Nat.zero_shiftRight]
  have hOutLt36 : ∀ δ (sh1 : ℕ), (∀ k : Fin W, δ (rWork k) = 0) →
      ((if stPre δ wG == 1 then
          y36PopBernNoClamp word512DualLegLo6 (isNNFn δ) (d2Fn δ) (cFn δ)
        else 0) >>> sh1) < 2 ^ 36 := fun δ sh1 hz ↦ by
    refine (Nat.shiftRight_le _ _).trans_lt ?_; split_ifs
    · unfold y36PopBernNoClamp word512DualLegLo6; dsimp only
      have hLt4 : 4 * idx7Fn δ + jFn δ < 512 := by have := hIdx7Lt δ hz; have := hJLt δ hz; omega
      exact (Nat.shiftRight_le _ _).trans_lt ((Nat.div_mul_le_self _ 64).trans_lt
          (word512DualLeg_lt_pow36 _ hLt4))
    · exact Nat.two_pow_pos 36
  have hScrQPre : ∀ δ, stQPre δ wScr = stPre δ wScr := fun δ ↦ hNotQPre δ wScr hd.2.2.2.1
  have hScrQPost : ∀ δ, stQPost δ wScr = stPost δ wScr := fun δ ↦ hNotQPost δ wScr hd.2.2.2.1
  have hNNQPre : ∀ δ, stQPre δ wNN = stPre δ wNN := fun δ ↦ hNotQPre δ wNN hd.2.2.2.2.2.2.1
  have hNNQPost : ∀ δ, stQPost δ wNN = stPost δ wNN := fun δ ↦ hNotQPost δ wNN hd.2.2.2.2.2.2.1
  have hUnsh := cowp_pUnshift30_mid42_m72 pkgBasis pkgBf v rWork
    wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd hScrI hNNI mid
    stQPre stQPost phPre phPost x32Fn hx32
    (fun δ hz ↦ by rw [hKVal δ hz]; exact (parts_popBern_bounds _ (hd2Lt δ hz)).2.2)
    (fun δ i hz ↦ by
      dsimp only [stQPre, stQPost]
      rw [hNotQPost δ (rK4 i) (fun b hb ↦ disj_ne (ggCore_KY hd.1) i b hb), hNotQPre δ (rK4 i)
          (fun b hb ↦ disj_ne (ggCore_KY hd.1) i b hb)]
      exact hK4Eq δ i hz)
    (fun δ hz ↦ by rw [hScrQPost δ, hScrQPre δ]; exact hScrEq δ hz)
    (fun δ hz ↦ by rw [hNNQPost δ, hNNQPre δ]; exact hNNEq δ hz)
    (fun δ hz hs0 ↦ by rw [hScrQPre δ] at hs0; rw [hNNQPre δ]; exact hValid δ hz hs0)
    hYQPre hYQPost hYLo6Pre hYLo6Post hPoolQPre hPoolQPost
    (fun stCleanPre stCleanPost hPresPre hPresPost hVal hPoolLt36 hPoolPers _ ↦
      hMidCB stCleanPre stCleanPost
        (fun δ w hny hnp ↦ (hPresPre δ w hny hnp).trans (hNotQPre δ w hny))
        (fun δ w hny hnp ↦ (hPresPost δ w hny hnp).trans (hNotQPost δ w hny))
        (fun δ hz ↦
          ⟨natOfZModBits36_div8_eq_shr3 (fun b ↦ stCleanPre δ (rY36 b)) _
            (hOutLt36 δ _ hz)
            (fun b hb3 ↦ by
              rw [(hVal δ b).1 hb3, hKVal δ hz, hScrQPre δ, hNNQPre δ, shr_add_eq, hShrEq δ]),
           fun b ↦ (hVal δ b).2.2,
           fun hg0 b ↦ by
             have hgF : gFn δ = false := by dsimp only [gFn]; rw [hg0]; rfl
             have hx0 : x32Fn δ = 0 := by dsimp only [x32Fn, rootG90X32]; rw [hgF]; rfl
             have hm0 : mask30 0 = 0 := rfl
             by_cases hb3 : b.val < 3
             · rw [(hVal δ b).2.1 hb3, hx0, Nat.zero_testBit]; rfl
             · rw [(hVal δ b).1 (by omega), hx0, hm0, Nat.zero_shiftLeft, Nat.zero_shiftRight,
                   Nat.zero_testBit]; rfl⟩)
        (fun δ j hz ↦
          hPoolLt36 δ ⟨j.val,
              Nat.lt_of_lt_of_le j.isLt (Nat.le_trans hkMid36 (by decide : 36 ≤ 72))⟩
            (Nat.lt_of_lt_of_le j.isLt hkMid36) hz)
        hPoolPers)
  unfold pInnerM72Mid36_0Scrub;
  exact subspaceStep_seq_u (hLoadPre phPre) (subspaceStep_seq_u hUnsh (hUnldPost phPost))
def coulInnerCoreM72Basis_mid36_0scrub {kMid tBasis tBf tInner : ℕ}
    (hkMid36 : kMid ≤ 36)
    (pkgQ : QromLoadPkgGenN 10 30 (gGatedShr6Word word512DualLeg))
    (pkgU : QromUnloadPkgGenN 10 30 (gGatedShr6Word word512DualLeg))
    (hLoad : pkgQ.kScr ≤ 72 + 6) (hUnld : pkgU.kUnload ≤ 72 + 6)
    (pkgBasis : KpBasis9Pkg tBasis) (pkgBf : Butterfly33K9Scr31Pkg tBf)
    (htInner : pkgQ.tLoad + pkgU.tUnload + tBasis + tBf = tInner) :
    CoulInnerCorePkgM72 kMid tInner where
  hMidLE := Nat.le_trans hkMid36 (by decide : 36 ≤ 72)
  pInner := pInnerM72Mid36_0Scrub pkgQ pkgU hLoad hUnld pkgBasis pkgBf
  counts_wires v wG wScr wNN rIdx7 rK4 rJ2 rY36 rPool hd hGS hSS hNS hIS hKS hJS hYS hPS mid := by
    obtain ⟨ht, hf, hw⟩ :=
        pInnerM72Mid36_0Scrub_counts_wires pkgQ pkgU hLoad hUnld pkgBasis pkgBf v wG wScr wNN rIdx7
        rK4 rJ2 rY36 rPool hd hGS hSS hNS hIS hKS hJS hYS hPS mid
    exact ⟨by rw [ht]; omega, hf, hw⟩
  step2_pers := pInnerM72Mid36_0Scrub_step2_pers hkMid36 pkgQ pkgU hLoad hUnld pkgBasis pkgBf

theorem unld76_hScr_m72 : qromUnloadRootG89DualLeg_wrouter_76_unld.kUnload ≤ 72 + 6 := by
  decide

end QuantumComputation.Specs.PhotochemistrySolution.CoulM72Mid36Opt

namespace QuantumComputation.Specs.PhotochemistrySolution.Pers12Dom168M72

open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket_X ket_CNOT
    eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (ditePos diteNeg)
/-! ### 1. Split `PrimTree` ASTs (`outerDomPre76Tree`, `remDomPre8Tree`, `pers12Setup4Tree`) -/

def outerDomPreSMask : ℕ := 0xfffc00000

def outerDomPre73Tree : PrimTree :=
    (pN (pN (pN (pN (p4 76 38981 38985 80) (p5 41025 23109710 76 38981 38985))
    (pN (p5 39001 41021 41025 24158286 39001) (p5 39005 41017 41021 25206862 39005)))
    (pN (pN (p5 39009 41013 41017 26255438 39009) (p5 39013 41009 41013 27304014 39013))
    (pN (p5 39017 41005 41009 28352590 39017) (p5 39021 41001 41005 29401166 39021))))
    (pN (pN (pN (p4 39025 40997 41001 30449742) (p5 39025 39029 40993 40997 31498318))
    (pN (p5 39029 39033 40989 40993 32546894) (p5 39033 39037 40985 40989 33595470)))
    (pN (pN (p5 39037 39041 40981 40985 34644046) (p5 39041 39045 40977 40981 35692622))
    (p5 39045 39049 40961 40977 36741198))))
def outerDomPre76Tree : PrimTree := .node outerDomPre73Tree (p3 39049 40961 80)
def remDomPre8Tree : PrimTree := .node (p3 80 40961 39049) (p5 73865 73869 75921 73801 75845)
def pers12Setup4Tree : PrimTree := p4 76 80 41033 41029
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem outerDomPre76Tree_check : (checkPrimTree 35 0 outerDomPreSMask outerDomPre76Tree).1 = true ∧
    (checkPrimTree 35 0 outerDomPreSMask outerDomPre76Tree).2.2 = 14 :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem outerDomPreSMask_bounds (u : ℕ) (hu : u < 36) (hm : outerDomPreSMask.testBit u = true) :
    22 ≤ u := by
  revert hm hu u; decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem outerDomPre76Tree_targets : primTreeTargetsIn 35 19 36 outerDomPre76Tree = true := by
  decide +kernel
set_option maxHeartbeats 1600000 in
-- finite certificate kernel reduction
theorem remDomPre8Tree_check : (checkPrimTree 117 0 0 remDomPre8Tree).1 = true ∧
    (checkPrimTree 117 0 0 remDomPre8Tree).2.2 = 0 :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem pers12Setup4Tree_check : (checkPrimTree 63 0 0 pers12Setup4Tree).1 = true ∧
    (checkPrimTree 63 0 0 pers12Setup4Tree).2.2 = 0 :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem pers12Setup4Tree_loc : primTreeTargetsIn 63 19 35 pers12Setup4Tree = true ∧
    primTreeWiresLt 63 42 pers12Setup4Tree = true :=
  ⟨by decide +kernel, by decide +kernel⟩

def primGateRawLt36 (c : ℕ) : Bool :=
    Nat.blt ((c >>> 2) % 512) 36 && Nat.blt ((c >>> 11) % 512) 36 && Nat.blt ((c >>> 20) % 512) 36
def primTreeRawLt36 : PrimTree → Bool
  | .empty => true
  | .leaf c => primGateRawLt36 c
  | .node l r => primTreeRawLt36 l && primTreeRawLt36 r

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem outerDomPre76Tree_rawLt36 : primTreeRawLt36 outerDomPre76Tree = true := by decide +kernel
theorem evalPrimGate_35_eq_117 {c : ℕ} (hc : primGateRawLt36 c = true)
    (x : ℕ) : evalPrimGate 35 x c = evalPrimGate 117 x c := by
  simp only [primGateRawLt36, Bool.and_eq_true_iff, Nat.blt_eq] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  unfold evalPrimGate
  dsimp only
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (show (c >>> 2) % 512 < 118 by omega),
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (show (c >>> 11) % 512 < 118 by omega),
      Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt (show (c >>> 20) % 512 < 118 by omega)]

theorem evalPrimTree_35_eq_117 :
    ∀ {t : PrimTree}, primTreeRawLt36 t = true → ∀ x : ℕ,
      evalPrimTree 35 x t = evalPrimTree 117 x t
  | .empty, _, _ => rfl
  | .leaf c, hc, x => evalPrimGate_35_eq_117 hc x
  | .node l r, hc, x => by
      obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hc
      dsimp only [evalPrimTree]
      rw [evalPrimTree_35_eq_117 hl x, evalPrimTree_35_eq_117 hr]
theorem evalPrimGate_x_invol {M c : ℕ} (h0 : Nat.beq (c % 4) 0 = true)
    (z : ℕ) : evalPrimGate M (evalPrimGate M z c) c = z := by
  unfold evalPrimGate
  simp only [h0, ↓reduceIte, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem evalPrimGate_cnot_invol {M c : ℕ} (h1 : Nat.beq (c % 4) 1 = true)
    (z : ℕ) : evalPrimGate M (evalPrimGate M z c) c = z := by
  unfold evalPrimGate
  have h0 : Nat.beq (c % 4) 0 = false := Nat.eq_of_beq_eq_true h1 ▸ rfl
  set w1 := ((c >>> 2) % 512) % (M + 1)
  set w2 := ((c >>> 11) % 512) % (M + 1)
  simp only [h0, h1, Bool.false_eq_true, ↓reduceIte]
  cases hw : Nat.beq w1 w2
  · cases hz : z.testBit w1
    · simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte, hz]
    · have hne : w2 ≠ w1 := fun e ↦ Bool.noConfusion (hw.symm.trans (Nat.beq_eq.mpr e.symm))
      simp only [Bool.not_false, Bool.true_and, ↓reduceIte, testBit_xor_shift1, hne, hz,
        Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · simp

set_option maxHeartbeats 1600000 in
-- finite certificate kernel reduction
theorem evalPrimTree_outer_rem_eq_dom216Pre (x : ℕ) :
    evalPrimTree 117 (evalPrimTree 35 x outerDomPre76Tree) remDomPre8Tree =
    evalPrimTree 117 x dom216PreTree := by
  rw [evalPrimTree_35_eq_117 outerDomPre76Tree_rawLt36 x]
  dsimp only [outerDomPre76Tree, outerDomPre73Tree, remDomPre8Tree, dom216PreTree, p3, p2,
    evalPrimTree]
  rw [evalPrimGate_x_invol (by decide), evalPrimGate_cnot_invol (by decide),
      evalPrimGate_cnot_invol (by decide)]
/-! ### 2. Single-Pass `CT` Verification (`checkPers12All`, `decide +kernel`) -/

def pers12PadCols43 (cOut : CT) : List ℕ :=
    (List.range 43).map (fun t ↦ if t < 14 then getCT 7 cOut (22 + t) else 0)
theorem pers12PadCols43_length (cOut : CT) : (pers12PadCols43 cOut).length = 43 := by
  simp [pers12PadCols43]
theorem pers12PadCols43_getD (cOut : CT) {t : ℕ} (ht : t < 43) : (pers12PadCols43 cOut).getD t 0 =
    if t < 14 then getCT 7 cOut (22 + t) else 0 := by
  simp [pers12PadCols43, List.getD_eq_getElem?_getD, ht]
def pers12UnldInitCT (nn : ℕ) (cOut : CT) : CT := setColsAt (pers12PadCols43 cOut) 21 (initDomCT nn)
def checkPers12All (nn : ℕ) : Bool :=
  let mx := (coordState 18).2.1; let vm := ltMask 196608; let cInit := initDomCT nn;
  let cOut := evalStrict 35 mx cInit outerDomPre76Tree;
  let expCols := expEvenOctCols nn mx (coordState 18).2.2;
  let cSetup := evalStrict 63 mx (pers12UnldInitCT nn cOut) pers12Setup4Tree;
  let cFull := fullLive12CT nn
  checkZeroRange cOut vm 19 3 &&
  Nat.beq ((getCT 7 cOut 29 ^^^ mx ^^^ getCT 7 cInit 17 ^^^ getCT 7 cInit 18 ^^^ expCols.getD 20 0)
      &&& vm) 0 &&
  Nat.beq ((getCT 7 cOut 33 ^^^ getCT 7 cOut 25 ^^^ expCols.getD 20 0 ^^^ expCols.getD 19 0) &&& vm)
      0 &&
  (List.range 42).all (fun u ↦ Nat.beq ((getCT 7 cSetup u ^^^ getCT 7 cFull u) &&& vm) 0)

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem checkPers12All_0 : checkPers12All 0 = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- finite certificate kernel reduction
theorem checkPers12All_1 : checkPers12All 1 = true := by decide +kernel

theorem checkPers12All_nn (b : Bool) : checkPers12All (if b then 1 else 0) = true := by
  cases b
  · exact checkPers12All_0
  · exact checkPers12All_1

theorem xor_and_vm_zero_eq {a b vm d2 : ℕ} (h : Nat.beq ((a ^^^ b) &&& vm) 0 = true)
    (hvm : vm.testBit d2 = true) : a.testBit d2 = b.testBit d2 := by
  have hb := congrArg (fun x ↦ x.testBit d2) (Nat.beq_eq.mp h)
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit, hvm, Bool.and_true,
      bne_eq_false_iff_eq] at hb; exact hb
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem initDomCT_zero_21_43 (nn : ℕ) (hnn : nn = 0 ∨ nn = 1) : ∀ t < 43, getCT 7 (initDomCT nn)
    (21 + t) = 0 := by
  have hc0 : ((List.range 43).all (fun t ↦
      Nat.beq (getCT 7 (initDomCT 0) (21 + t)) 0)) = true := by decide +kernel
  have hc1 : ((List.range 43).all (fun t ↦
      Nat.beq (getCT 7 (initDomCT 1) (21 + t)) 0)) = true := by decide +kernel
  intro t ht
  rcases hnn with rfl | rfl
  · exact Nat.beq_eq.mp (List.all_eq_true.mp hc0 t (List.mem_range.mpr ht))
  · exact Nat.beq_eq.mp (List.all_eq_true.mp hc1 t (List.mem_range.mpr ht))

def chain14Bit (isNN : Bool) (d2 : ℕ) (s : Fin 14) : Bool :=
    (evalPrimTree 35 ((if isNN then 1 else 0) + 2 * (d2 % 262144)) outerDomPre76Tree).testBit (22 +
    s.val)
def pers12Idx (p : Fin 12) : Fin 14 :=
  if p.val < 7 then ⟨p.val, by omega⟩
  else if p.val < 10 then ⟨p.val + 1, by omega⟩
  else ⟨p.val + 2, by omega⟩

def pers12Bit (isNN : Bool) (d2 : ℕ) (p : Fin 12) : Bool := chain14Bit isNN d2 (pers12Idx p)
theorem natOfZModBits36_clean19 (β : Fin 36 → ZMod 2)
    (hZero : ∀ u : Fin 36, 19 ≤ u.val → β u = 0) :
    natOfZModBits 36 β =
      (if β ⟨0, by decide⟩ == 1 then 1 else 0) +
        2 * (natOfZModBits 18 (fun b ↦ β ⟨1 + b.val, by omega⟩) % 262144) := by
  set d2 := natOfZModBits 18 (fun b ↦ β ⟨1 + b.val, by omega⟩)
  have hd2Lt : d2 < 262144 := natOfZModBits_lt 18 _; rw [Nat.mod_eq_of_lt hd2Lt]
  set rhs := (if β ⟨0, by decide⟩ == 1 then 1 else 0) + 2 * d2
  have hrhsLt : rhs < 2 ^ 19 := by dsimp [rhs]; split_ifs <;> omega
  apply Nat.eq_of_testBit_eq; intro k
  have hmod : rhs % 2 = if β ⟨0, by decide⟩ == 1 then 1 else 0 := by
    dsimp only [rhs]; split_ifs <;> omega
  have hTestRhs0 : rhs.testBit 0 = (β ⟨0, by decide⟩ == 1) := by
    rw [Nat.testBit_zero, hmod]; cases (β ⟨0, by decide⟩ == 1) <;> decide
  have hTestRhsSucc : ∀ m : ℕ, rhs.testBit (m + 1) = d2.testBit m := fun m ↦ by
    rw [Nat.testBit_succ]
    have hdiv : rhs / 2 = d2 := by dsimp [rhs]; split_ifs <;> omega
    rw [hdiv]
  by_cases hk36 : k < 36
  · rw [natOfZModBits_testBit_lt β hk36]
    by_cases hk0 : k = 0
    · subst hk0; exact hTestRhs0.symm
    · by_cases hk19 : k < 19
      · have hm : k = (k - 1) + 1 := by omega
        have hr : rhs.testBit k = d2.testBit (k - 1) := by
          conv_lhs => rw [hm]
          exact hTestRhsSucc (k - 1)
        rw [hr, natOfZModBits_testBit_lt (fun b : Fin 18 ↦ β ⟨1 + b.val, by omega⟩) (by omega)]
        exact congrArg (fun u ↦ β u == 1) (Fin.ext (by dsimp; omega))
      · rw [hZero ⟨k, hk36⟩ (by dsimp; omega)]
        have hkPow : 2 ^ 19 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hrhsLt hkPow)]; rfl
  · have hltL : natOfZModBits 36 β < 2 ^ k :=
      lt_of_lt_of_le (natOfZModBits_lt 36 β) (Nat.pow_le_pow_right (by omega) (by omega))
    have hltR : rhs < 2 ^ k :=
      lt_of_lt_of_le hrhsLt (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hltL, Nat.testBit_lt_two_pow hltR]

theorem pers12_ct_facts (isNN : Bool) {d2 : ℕ} (hd2 : d2 < 196608) :
    let x0 := (if isNN then 1 else 0) + 2 * (d2 % 262144)
    let xOut := evalPrimTree 35 x0 outerDomPre76Tree
    let nn := if isNN then 1 else 0
    let cOut := evalStrict 35 (coordState 18).2.1 (initDomCT nn) outerDomPre76Tree;
    let cSetup := evalStrict 63 (coordState 18).2.1 (pers12UnldInitCT nn cOut) pers12Setup4Tree;
    let p := evenOctIdxT10K isNN d2
    (xOut.testBit 19 = false ∧ xOut.testBit 20 = false ∧ xOut.testBit 21 = false) ∧
    (∀ s : Fin 14, (getCT 7 cOut (22 + s.val)).testBit d2 = chain14Bit isNN d2 s) ∧
    chain14Bit isNN d2 ⟨7, by decide⟩ =
      !(xor (xor (d2.testBit 16) (d2.testBit 17)) (dom22Bit p ⟨20, by decide⟩)) ∧
    chain14Bit isNN d2 ⟨11, by decide⟩ =
      xor (xor (pers12Bit isNN d2 ⟨3, by decide⟩) (dom22Bit p ⟨20, by decide⟩))
          (dom22Bit p ⟨19, by decide⟩) ∧
    (∀ u < 42, (getCT 7 cSetup u).testBit d2 = (getCT 7 (fullLive12CT nn) u).testBit d2) := by
  dsimp only
  have hd2_262 : d2 < 262144 := by omega
  have hd2Pow : d2 < 2 ^ 18 := hd2_262
  let nn := if isNN then 1 else 0
  have hnnLt : nn < 2 := by change (if isNN then 1 else 0) < 2; cases isNN <;> decide
  let β : Fin 36 → ZMod 2 := fun u ↦
      if u.val = 0 then (if isNN then 1 else 0) else if u.val < 19 then (if d2.testBit (u.val -
      1) then 1 else 0) else 0
  have hd2Eq : ∀ b : Fin 18, (β ⟨1 + b.val, by omega⟩ == 1) = d2.testBit b.val := fun b ↦ by
    dsimp only [β]
    rw [_root_.ite_eq_right (by omega), _root_.ite_eq_left (by omega)]
    have hsub : 1 + b.val - 1 = b.val := by omega
    rw [hsub]; cases d2.testBit b.val <;> rfl
  have hZeroβ : ∀ u : Fin 36, 19 ≤ u.val → β u = 0 := fun u hu ↦ by
    dsimp only [β]; rw [_root_.ite_eq_right (by omega), _root_.ite_eq_right (by omega)]
  have hx0Eq : natOfZModBits 36 β = (if isNN then 1 else 0) + 2 * (d2 % 262144) := by
    rw [natOfZModBits36_clean19 β hZeroβ, Nat.mod_eq_of_lt hd2_262]
    have hb0 : (β ⟨0, by decide⟩ == 1) = isNN := by dsimp [β]; cases isNN <;> rfl
    have hdEq : natOfZModBits 18 (fun b ↦ β ⟨1 + b.val, by omega⟩) = d2 := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 18
      · rw [natOfZModBits_testBit_lt _ hk]; exact hd2Eq ⟨k, hk⟩
      · have h1 : natOfZModBits 18 (fun b ↦ β ⟨1 + b.val, by omega⟩) < 2 ^ k :=
          lt_of_lt_of_le (natOfZModBits_lt 18 _) (Nat.pow_le_pow_right (by omega) (by omega))
        have h2 : d2 < 2 ^ k :=
          lt_of_lt_of_le hd2Pow (Nat.pow_le_pow_right (by decide) (by omega))
        rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    rw [hb0, hdEq, Nat.mod_eq_of_lt hd2_262]
  have hnnβ : (if β ⟨0, by decide⟩ == 1 then 1 else 0) = nn := by dsimp [β, nn]; cases isNN <;> rfl
  have hEvOut : ∀ u < 36, (evalPrimTree 35 ((if isNN then 1 else 0) + 2 *
      (d2 % 262144)) outerDomPre76Tree).testBit u =
      (getCT 7 (evalStrict 35 (coordState 18).2.1 (initDomCT nn) outerDomPre76Tree) u).testBit d2
      := by
    intro u hu; rw [← hx0Eq, ← hnnβ]
    exact (evalStrict_initDomCT (by decide : 18 ≤ 35) (by decide : 35 < 128)
      outerDomPre76Tree β d2 hd2_262 hd2Eq hZeroβ u hu).symm
  have hvm : (ltMask 196608).testBit d2 = true := by rw [testBit_ltMask]; exact decide_eq_true hd2
  have hAll :=
      checkPers12All_nn isNN; change checkPers12All nn =
      true at hAll; dsimp only [checkPers12All] at hAll
  have p3 := band_left hAll; have h42 := band_right hAll
  have p2 := band_left p3; have hz4 := band_right p3
  have hz19 := band_left p2; have hz8 := band_right p2
  obtain ⟨_, hC18, _, _, _⟩ := coordState_spec 18
  have hmx : (coordState 18).2.1.testBit d2 = true := by
    rw [hC18, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hd2Pow
  have hnnBeq : nn.beq 1 = isNN := by dsimp [nn]; cases isNN <;> rfl
  have hExp20 : ((expEvenOctCols nn (coordState 18).2.1 (coordState 18).2.2).getD 20 0).testBit d2 =
      dom22Bit (evenOctIdxT10K isNN d2) ⟨20, by decide⟩ := by
    have he := expEvenOctCols_testBit nn hnnLt hd2Pow 20 (by decide)
    rw [hnnBeq] at he; exact he
  have hExp19 : ((expEvenOctCols nn (coordState 18).2.1 (coordState 18).2.2).getD 19 0).testBit d2 =
      dom22Bit (evenOctIdxT10K isNN d2) ⟨19, by decide⟩ := by
    have he := expEvenOctCols_testBit nn hnnLt hd2Pow 19 (by decide)
    rw [hnnBeq] at he; exact he
  have hc17 : (getCT 7 (initDomCT nn) 17).testBit d2 = d2.testBit 16 := by
    rw [getCT_initDomCT nn d2 17 hd2_262 (by decide)]; rfl
  have hc18 : (getCT 7 (initDomCT nn) 18).testBit d2 = d2.testBit 17 := by
    rw [getCT_initDomCT nn d2 18 hd2_262 (by decide)]; rfl
  let cOut := evalStrict 35 (coordState 18).2.1 (initDomCT nn) outerDomPre76Tree
  let expC := expEvenOctCols nn (coordState 18).2.1 (coordState 18).2.2
  have cz (u : ℕ) (h1 : 19 ≤ u := by decide) (h2 : u < 19 + 3 := by decide) :
      (evalPrimTree 35 ((if isNN then 1 else 0) + 2 * (d2 % 262144)) outerDomPre76Tree).testBit u =
        false :=
    (hEvOut u (by omega)).trans (checkZeroRange_sound _ _ 19 d2 hvm 3 hz19 u h1 h2)
  refine ⟨⟨cz 19, cz 20, cz 21⟩, fun s ↦ (hEvOut (22 + s.val) (by omega)).symm, ?_, ?_,
    fun u hu ↦ xor_and_vm_zero_eq (List.all_eq_true.mp h42 u (List.mem_range.mpr hu)) hvm⟩
  · dsimp only [chain14Bit]
    have hEq8 : (getCT 7 cOut 29 ^^^ (coordState 18).2.1 ^^^ getCT 7 (initDomCT nn) 17 ^^^
        getCT 7 (initDomCT nn) 18 ^^^ expC.getD 20 0) =
      (getCT 7 cOut 29 ^^^ ((coordState 18).2.1 ^^^ getCT 7 (initDomCT nn) 17 ^^^
        getCT 7 (initDomCT nn) 18 ^^^ expC.getD 20 0)) := by simp only [Nat.xor_assoc]
    rw [hEvOut 29 (by decide), xor_and_vm_zero_eq (by rwa [← hEq8]) hvm]
    simp only [expC, Nat.testBit_xor, hmx, hc17, hc18, hExp20]
    cases d2.testBit 16 <;> cases d2.testBit 17 <;>
      cases dom22Bit (evenOctIdxT10K isNN d2) ⟨20, by decide⟩ <;> rfl
  · have hp3 : (pers12Idx ⟨3, by decide⟩).val = 3 := rfl
    have hEq4 : (getCT 7 cOut 33 ^^^ getCT 7 cOut 25 ^^^ expC.getD 20 0 ^^^ expC.getD 19 0) =
      (getCT 7 cOut 33 ^^^ (getCT 7 cOut 25 ^^^ expC.getD 20 0 ^^^ expC.getD 19 0)) := by
      simp only [Nat.xor_assoc]
    dsimp only [chain14Bit, pers12Bit]
    rw [hp3, hEvOut 33 (by decide), hEvOut 25 (by decide),
        xor_and_vm_zero_eq (by rwa [← hEq4]) hvm]
    simp only [cOut, expC, Nat.testBit_xor, hExp20, hExp19]
/-! ### 3. Registers & Sub-Circuits for `Pers12Dom168` (`kRest = 123`, `168 T`, `0 .TOFF`) -/

def chain14RIdx (s : Fin 14) : Fin (54 + 123) :=
  if s.val < 7 then ⟨143 + s.val, by omega⟩
  else if s.val = 7 then ⟨122, by decide⟩
  else if s.val < 11 then ⟨142 + s.val, by omega⟩
  else if s.val = 11 then ⟨123, by decide⟩
  else ⟨141 + s.val, by omega⟩

theorem chain14RIdx_inj : Function.Injective chain14RIdx := by
  intro a b e; have hv := congrArg Fin.val e
  fin_cases a <;> fin_cases b <;> first | rfl | cases hv

theorem chain14RIdx_pers12 (p : Fin 12) :
    chain14RIdx (pers12Idx p) = ⟨143 + p.val, by omega⟩ := by
  fin_cases p <;> rfl

theorem chain14RIdx_bounds (s : Fin 14) : (chain14RIdx s).val = 122 ∨ (chain14RIdx s).val = 123 ∨
    (143 ≤ (chain14RIdx s).val ∧ (chain14RIdx s).val < 155) := by
  fin_cases s <;> decide

def fOuter36 {n : ℕ} (wNN : Wire n) (r : QRegister (54 + 123) n) (u : Fin 36) : Wire n :=
  if _ : u.val = 0 then wNN
  else if h22 : u.val < 22 then r ⟨u.val - 1, by omega⟩
  else r (chain14RIdx ⟨u.val - 22, by omega⟩)

theorem fOuter36_inj {n : ℕ} {wNN : Wire n} {r : QRegister (54 + 123) n} (hw : ∀ i, wNN ≠ r i) :
    Function.Injective (fOuter36 wNN r) := by
  intro x y e
  dsimp only [fOuter36] at e
  split_ifs at e <;> first
    | exact Fin.ext (by omega)
    | exact absurd e (hw _)
    | exact absurd e.symm (hw _)
    | (have hc := congrArg Fin.val (chain14RIdx_inj (r.wires.injective e))
       dsimp at hc
       exact Fin.ext (by omega))
    | exact Fin.ext (by
        have hv := congrArg Fin.val (r.wires.injective e)
        try have := chain14RIdx_bounds ⟨x.val - 22, by omega⟩
        try have := chain14RIdx_bounds ⟨y.val - 22, by omega⟩
        dsimp at hv
        omega)

def rOuter36 {n : ℕ} {wNN : Wire n} {r : QRegister (54 + 123) n} (hw : ∀ i, wNN ≠ r i) :
    QRegister 36 n := ⟨⟨fOuter36 wNN r, fOuter36_inj hw⟩⟩
def fDom118Pers {n : ℕ} (wNN : Wire n) (r : QRegister (54 + 123) n) (u : Fin 118) : Wire n :=
  if h36 : u.val < 36 then fOuter36 wNN r ⟨u.val, h36⟩
  else if h69 : u.val < 69 then r ⟨21 + (u.val - 36), by omega⟩
  else r ⟨54 + (u.val - 69), by omega⟩

theorem fDom118Pers_inj {n : ℕ} {wNN : Wire n} {r : QRegister (54 + 123) n} (hw : ∀ i, wNN ≠ r i) :
    Function.Injective (fDom118Pers wNN r) := by
  intro x y e
  have hCross {a b : Fin 118} (ha : a.val < 36) (hb : ¬ b.val < 36)
      (hab : fDom118Pers wNN r a = fDom118Pers wNN r b) : False := by
    dsimp only [fDom118Pers, fOuter36] at hab
    rw [_root_.dite_eq_left ha, _root_.dite_eq_right hb] at hab
    split_ifs at hab <;> first
      | exact hw _ hab
      | (have hv := congrArg Fin.val (r.wires.injective hab)
         try have := chain14RIdx_bounds ⟨a.val - 22, by omega⟩
         dsimp at hv
         omega)
  by_cases hx36 : x.val < 36 <;> by_cases hy36 : y.val < 36
  · dsimp only [fDom118Pers] at e
    rw [_root_.dite_eq_left hx36, _root_.dite_eq_left hy36] at e
    exact Fin.ext (congrArg (fun z : Fin 36 ↦ z.val) (fOuter36_inj hw e))
  · exact False.elim (hCross hx36 hy36 e)
  · exact False.elim (hCross hy36 hx36 e.symm)
  · dsimp only [fDom118Pers] at e
    rw [_root_.dite_eq_right hx36, _root_.dite_eq_right hy36] at e
    split_ifs at e <;> exact Fin.ext (by
      have hv := congrArg Fin.val (r.wires.injective e)
      dsimp at hv
      omega)

def rDom118Pers {n : ℕ} {wNN : Wire n} {r : QRegister (54 + 123) n} (hw : ∀ i, wNN ≠ r i) :
    QRegister 118 n := ⟨⟨fDom118Pers wNN r, fDom118Pers_inj hw⟩⟩
def fUnld42Pers {n : ℕ} (wNN : Wire n) (r : QRegister (54 + 123) n) (u : Fin 42) : Wire n :=
  if _ : u.val = 0 then wNN
  else if _ : u.val < 21 then r ⟨u.val - 1, by omega⟩
  else if _ : u.val < 35 then r (chain14RIdx ⟨u.val - 21, by omega⟩)
  else r ⟨20 + (u.val - 35), by omega⟩

theorem fUnld42Pers_inj {n : ℕ} {wNN : Wire n} {r : QRegister (54 + 123) n} (hw : ∀ i, wNN ≠ r i) :
    Function.Injective (fUnld42Pers wNN r) := by
  intro x y e
  dsimp only [fUnld42Pers] at e
  split_ifs at e <;> first
    | exact Fin.ext (by omega)
    | exact absurd e (hw _)
    | exact absurd e.symm (hw _)
    | (have hc := congrArg Fin.val (chain14RIdx_inj (r.wires.injective e))
       dsimp at hc
       exact Fin.ext (by omega))
    | exact Fin.ext (by
        have hv := congrArg Fin.val (r.wires.injective e)
        try have := chain14RIdx_bounds ⟨x.val - 21, by omega⟩
        try have := chain14RIdx_bounds ⟨y.val - 21, by omega⟩
        dsimp at hv
        omega)

def rUnld42Pers {n : ℕ} {wNN : Wire n} {r : QRegister (54 + 123) n} (hw : ∀ i, wNN ≠ r i) :
    QRegister 42 n := ⟨⟨fUnld42Pers wNN r, fUnld42Pers_inj hw⟩⟩
theorem domPers_disj_top {n : ℕ} {wNN : Wire n} {r : QRegister (54 + 123) n}
    (hw : ∀ i, wNN ≠ r i) :
    (rDom118Pers hw).DisjointWires (rTop22Hi (by decide : 90 ≤ 123) r) ∧
    (rUnld42Pers hw).DisjointWires (rTop22Hi (by decide : 90 ≤ 123) r) := by
  refine ⟨disj_of_ne fun u j e ↦ ?_, disj_of_ne fun u j e ↦ ?_⟩
  · change fDom118Pers wNN r u = _ at e
    dsimp only [fDom118Pers, fOuter36] at e
    split_ifs at e <;> first
      | exact hw _ e
      | (have hv := congrArg Fin.val (r.wires.injective e)
         try have := chain14RIdx_bounds ⟨u.val - 22, by omega⟩
         dsimp [rTop22Hi] at hv
         omega)
  · change fUnld42Pers wNN r u = _ at e
    dsimp only [fUnld42Pers] at e
    split_ifs at e <;> first
      | exact hw _ e
      | (have hv := congrArg Fin.val (r.wires.injective e)
         try have := chain14RIdx_bounds ⟨u.val - 21, by omega⟩
         dsimp [rTop22Hi] at hv
         omega)

/-! ### 4. `112 T` Forward Remainder Domain Normalizer `pEvenOctBandDomRem112` -/

def pEvenOctBandDomRem112 {Var : Type} {n : ℕ} (v : Var) (rInScr : QRegister (dom216M + 1) n)
    (rTgt : QRegister 22 n) (hDisj : rInScr.DisjointWires rTgt) : DynamicCircuit Var n :=
  wrapDynOnReg v rInScr (decodePrimTree 117 remDomPre8Tree)
    (pWIntactBracket v rInScr uR1 fR1 39 (by decide) (by decide) (fun b ↦ (hfB_R1 b).1)
      (wrapDynOnReg v rInScr (decodePrimTree 117 dom216Setup2Tree)
        (pWIntactBracket v rInScr uR2 fR2 46 (by decide) (by decide) (fun b ↦ (hfB_R2 b).1)
          (wrapDynOnReg v rInScr (decodePrimTree 117 dom216Setup3Tree)
            (pWIntactBracket v rInScr uR3 fR3 56 (by decide) (by decide) (fun b ↦ (hfB_R3 b).1)
              (wrapDynOnReg v rInScr (decodePrimTree 117 dom216Setup4Tree)
                (pWIntactBracket v rInScr uR4 fR4 67 (by decide) (by decide) (fun b ↦ (hfB_R4 b).1)
                  (bennettXorReg v rInScr (decodePrimTree 117 dom216Post21Tree)
                    dom216OutW rTgt hDisj))))))))

theorem subspaceStep_pEvenOctBandDomRem112 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (rInScr : QRegister (dom216M + 1) n) (rTgt : QRegister 22 n)
    (hDisj : rInScr.DisjointWires rTgt)
    (stClean stCur : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hd2Lt : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 18 (fun b ↦ stClean δ (rInScr ⟨1 + b.val, dom216_1add_lt b⟩)) < 196608)
    (hCln19 : ∀ (u : Fin (dom216M + 1)) (δ : BitAssignment n),
      19 ≤ u.val → (∀ k : Fin W, δ (rWork k) = 0) → stClean δ (rInScr u) = 0)
    (hOutEq : ∀ δ w, (∀ u : Fin (dom216M + 1), w ≠ rInScr u) → stCur δ w = stClean δ w)
    (hBitsEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 118 (fun i ↦ stCur δ (rInScr i)) =
        evalPrimTree 35 (natOfZModBits 118 (fun i ↦ stClean δ (rInScr i))) outerDomPre76Tree) :
    SubspaceStep (mkKetOpW rWork stCur ph)
      (mkKetOpW rWork (fun δ ↦ writeReg (stCur δ) rTgt (fun j ↦
        let p :=
            evenOctIdxT10K (stClean δ (rInScr ⟨0, Nat.succ_pos dom216M⟩) == 1)
            (natOfZModBits 18 (fun b ↦ stClean δ (rInScr ⟨1 + b.val, dom216_1add_lt b⟩)))
        stClean δ (rTgt j) + if dom22Bit p j then 1 else 0)) ph)
      (pEvenOctBandDomRem112 v rInScr rTgt hDisj) ∧
    (pEvenOctBandDomRem112 v rInScr rTgt hDisj).count .T = 112 ∧
    (pEvenOctBandDomRem112 v rInScr rTgt hDisj).count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ u, S (rInScr u)) → (∀ j, S (rTgt j)) →
      DynWires S (pEvenOctBandDomRem112 v rInScr rTgt hDisj)) := by
  let gOut : BitAssignment n → Fin 22 → ZMod 2 := fun δ j ↦
    let p :=
        evenOctIdxT10K (stClean δ (rInScr ⟨0, Nat.succ_pos dom216M⟩) == 1)
        (natOfZModBits 18 (fun b ↦ stClean δ (rInScr ⟨1 + b.val, dom216_1add_lt b⟩)))
    stClean δ (rTgt j) + if dom22Bit p j then 1 else 0
  have hFacts (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0) :=
      dom216_stage_facts (fun u ↦ stClean δ (rInScr u)) (hd2Lt δ hz) (fun u hu ↦ hCln19 u δ hu hz)
  obtain ⟨hS9_raw, hT9, hF9, hD9⟩ := subspaceStep_primTreeXor v rWork rInScr dom216Post21SMask
    dom216Post21Tree dom216Post21Tree_check dom216OutW rTgt hDisj (stTree118 rInScr tDom8 stClean)
        ph
    (fun u hm δ hz ↦ by
      obtain ⟨hge, hlt⟩ := dom216Post21SMask_outside u.val u.isLt hm
      exact stTree118_eq_zero_of_false rInScr tDom8 stClean δ u ((hFacts δ hz).2.2.2.2.1 u.val hge
          hlt))
  dsimp only [dom216M] at hT9 hF9
  have hS9 : SubspaceStep (mkKetOpW rWork (stTree118 rInScr tDom8 stClean) ph)
      (mkKetOpW rWork (stTree118 rInScr tDom8 (fun δ ↦ writeReg (stClean δ) rTgt (gOut δ))) ph)
      (bennettXorReg v rInScr (decodePrimTree 117 dom216Post21Tree) dom216OutW rTgt hDisj) := by
    refine subspaceStep_congr_out hS9_raw ?_;
    rw [stTree118_writeReg_disj rInScr rTgt hDisj tDom8 stClean gOut]
    refine mkKetOpW_congr rWork (fun δ hz ↦ ?_) (fun _ _ ↦ rfl)
    refine congrArg (writeReg (stTree118 rInScr tDom8 stClean δ) rTgt) (funext fun j ↦ ?_)
    have htgt : stTree118 rInScr tDom8 stClean δ (rTgt j) = stClean δ (rTgt j) :=
        writeReg_apply_of_not_mem _ _ _ _ (fun ⟨u, hu⟩ ↦ disj_ne hDisj u j hu)
    rw [htgt, natOfZModBits_stTree118, ← evalPrimTree_node, ← tDom9_eq,
        bitZMod2_congr ((hFacts δ hz).2.2.2.2.2 j)]
  obtain ⟨hS8, hT8, hF8, hD8⟩ := subspaceStep_pWIntactTreeBracket (by decide : 0 < 2)
    v rWork rInScr rTgt hDisj uR4 fR4 67 (by decide) (by decide) hfB_R4 tDom7 stClean gOut ph ph _
    (fun δ hz ↦ mut2_of_disj rInScr tDom7 stClean δ fR4 65 66 rfl rfl (hFacts δ hz).2.2.2.1.1)
    (fun δ hz ↦ ⟨(hFacts δ hz).2.2.2.1.2.1, (hFacts δ hz).2.2.2.1.2.2⟩)
    hS9
  have zBit {t : PrimTree} {stX : BitAssignment n → BitAssignment n} :
      ∀ (u : Wire 118), Nat.testBit 0 u.val = true →
      ∀ (δ : BitAssignment n), (∀ q : Fin W, δ (rWork q) = 0) →
        stTree118 rInScr t stX δ (rInScr u) = 0 := fun u hm _ _ ↦ by
    rw [Nat.zero_testBit] at hm; cases hm
  obtain ⟨hS7, hT7, hF7, hD7⟩ := subspaceStep_treeWrap118 v rWork rInScr rTgt hDisj
    0 0 tDom6 dom216Setup4Tree dom216Setup4Tree_check stClean gOut ph ph _ zBit hS8
  obtain ⟨hRk, hT6, hF6, hD6⟩ := subspaceStep_pWIntactTreeBracket (by decide : 0 < 3)
    v rWork rInScr rTgt hDisj uR3 fR3 56 (by decide) (by decide) hfB_R3 tDom5 stClean gOut ph ph _
    (fun δ hz ↦ mut3_of_disj rInScr tDom5 stClean δ fR3 17 18 55 rfl rfl rfl
      (hFacts δ hz).2.2.1.1 (hFacts δ hz).2.2.1.2.1 (hFacts δ hz).2.2.1.2.2.1)
    (fun δ hz ↦ ⟨(hFacts δ hz).2.2.1.2.2.2.1, (hFacts δ hz).2.2.1.2.2.2.2⟩)
    hS7
  obtain ⟨hS5, hT5, hF5, hD5⟩ := subspaceStep_treeWrap118 v rWork rInScr rTgt hDisj
    0 0 tDom4 dom216Setup3Tree dom216Setup3Tree_check stClean gOut ph ph _ zBit hRk
  obtain ⟨hK4, hT4, hF4, hD4⟩ := subspaceStep_pWIntactTreeBracket (by decide : 0 < 3)
    v rWork rInScr rTgt hDisj uR2 fR2 46 (by decide) (by decide) hfB_R2 tDom3 stClean gOut ph ph _
    (fun δ hz ↦ mut3_of_disj rInScr tDom3 stClean δ fR2 45 18 37 rfl rfl rfl
      (hFacts δ hz).2.1.1 (hFacts δ hz).2.1.2.1 (hFacts δ hz).2.1.2.2.1)
    (fun δ hz ↦ ⟨(hFacts δ hz).2.1.2.2.2.1, (hFacts δ hz).2.1.2.2.2.2⟩)
    hS5
  obtain ⟨hS3, hT3, hF3, hD3⟩ := subspaceStep_treeWrap118 v rWork rInScr rTgt hDisj
    0 0 tDom2 dom216Setup2Tree dom216Setup2Tree_check stClean gOut ph ph _ zBit hK4
  obtain ⟨hS2, hT2, hF2, hD2⟩ := subspaceStep_pWIntactTreeBracket (by decide : 0 < 2)
    v rWork rInScr rTgt hDisj uR1 fR1 39 (by decide) (by decide) hfB_R1 tDom1 stClean gOut ph ph _
    (fun δ hz ↦ mut2_of_disj rInScr tDom1 stClean δ fR1 35 36 rfl rfl (hFacts δ hz).1.1)
    (fun δ hz ↦ ⟨(hFacts δ hz).1.2 38 le_rfl (by omega),
      fun j hj1 hj2 ↦ (hFacts δ hz).1.2 j (by omega) hj2⟩)
    hS3
  have hNodeEmpty (x : ℕ) (t : PrimTree) :
      evalPrimTree 117 x (.node .empty t) = evalPrimTree 117 x t := rfl
  have hTreePt (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0) (w : Wire n) :
      stTree118 rInScr (.node .empty remDomPre8Tree) stCur δ w =
        stTree118 rInScr tDom1 stClean δ w := by
    by_cases hw : ∃ u, rInScr u = w
    · obtain ⟨u, rfl⟩ := hw
      rw [stTree118_apply_reg, stTree118_apply_reg,
          show tDom1 = .node .empty dom216PreTree from rfl, hNodeEmpty, hNodeEmpty,
          hBitsEq δ hz, evalPrimTree_outer_rem_eq_dom216Pre]
    · dsimp only [stTree118]
      rw [writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_of_not_mem _ _ _ _ hw]
      exact hOutEq δ w fun u hu ↦ hw ⟨u, hu.symm⟩
  have hTreeEqPost :
      mkKetOpW rWork (stTree118 rInScr tDom1 (fun δ ↦ writeReg (stClean δ) rTgt (gOut δ))) ph =
      mkKetOpW rWork (stTree118 rInScr (.node .empty remDomPre8Tree)
        (fun δ ↦ writeReg (stCur δ) rTgt (gOut δ))) ph := by
    rw [stTree118_writeReg_disj rInScr rTgt hDisj _ stClean gOut,
        stTree118_writeReg_disj rInScr rTgt hDisj _ stCur gOut]
    exact mkKetOpW_congr rWork (fun δ hz ↦ by rw [funext (hTreePt δ hz)]) (fun _ _ ↦ rfl)
  obtain ⟨hS1, hT1, hF1, hD1⟩ := subspaceStep_treeWrap118 v rWork rInScr rTgt hDisj
    0 0 .empty remDomPre8Tree remDomPre8Tree_check stCur gOut ph ph _ zBit
    (subspaceStep_congr_in
      (mkKetOpW_congr rWork (fun δ hz ↦ funext (hTreePt δ hz)) (fun _ _ ↦ rfl))
      (subspaceStep_congr_out hS2 hTreeEqPost))
  rw [stTree118_empty, stTree118_empty] at hS1
  unfold pEvenOctBandDomRem112
  exact ⟨hS1, by rw [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9],
    by rw [hF1, hF2, hF3, hF4, hF5, hF6, hF7, hF8, hF9],
    fun S hr ht ↦ hD1 S hr (hD2 S hr (hD3 S hr (hD4 S hr
      (hD5 S hr (hD6 S hr (hD7 S hr (hD8 S hr (hD9 S hr ht))))))))⟩

/-! ### 5. `0 T` Persistent-`12` Reversed-Output Unloader `pEvenOctBandPers12Unld0` -/

def pEvenOctBandPers12Unld0 {Var : Type} {n : ℕ} (v : Var) (rInScr : QRegister 42 n)
    (rOut : QRegister 22 n) (hDisj : rInScr.DisjointWires rOut) : DynamicCircuit Var n :=
  let r64 := appendRegRev42_22 rInScr rOut hDisj
  wrapDynOnReg v r64 (decodePrimTree 63 pers12Setup4Tree)
    (pUnloadLive12Range v rInScr rOut hDisj 0 22)

theorem subspaceStep_pEvenOctBandPers12Unld0
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (rInScr : QRegister 42 n) (rOut : QRegister 22 n)
    (hDisj : rInScr.DisjointWires rOut)
    (st stWB : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2)
    (hd2Lt : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 18 (fun b ↦ st δ (rInScr ⟨1 + b.val, by omega⟩)) < 196608)
    (hZ19_20 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      st δ (rInScr ⟨19, by decide⟩) = 0 ∧ st δ (rInScr ⟨20, by decide⟩) = 0)
    (hChain : ∀ (s : Fin 14) (δ : BitAssignment n), (∀ k : Fin W, δ (rWork k) = 0) →
      st δ (rInScr ⟨21 + s.val, by omega⟩) =
        if chain14Bit (st δ (rInScr ⟨0, by omega⟩) == 1)
          (natOfZModBits 18 (fun b ↦ st δ (rInScr ⟨1 + b.val, by omega⟩))) s
        then 1 else 0)
    (hZ35_41 : ∀ (u : Fin 42) (δ : BitAssignment n),
      35 ≤ u.val → (∀ k : Fin W, δ (rWork k) = 0) → st δ (rInScr u) = 0)
    (hOut0 : ∀ (j : Fin 22) (δ : BitAssignment n),
      (∀ k : Fin W, δ (rWork k) = 0) → st δ (rOut j) = 0)
    (hWB : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      let p := evenOctIdxT10K (st δ (rInScr ⟨0, by omega⟩) == 1)
        (natOfZModBits 18 (fun b ↦ st δ (rInScr ⟨1 + b.val, by omega⟩)))
      stWB δ = writeReg (st δ) rOut (fun j ↦
        if dom22Bit p j then 1 else 0)) :
    SubspaceStep (mkKetOpW rWork stWB ph) (mkKetOpW rWork st ph)
      (pEvenOctBandPers12Unld0 v rInScr rOut hDisj) ∧
    (pEvenOctBandPers12Unld0 v rInScr rOut hDisj).count .T = 0 ∧
    (pEvenOctBandPers12Unld0 v rInScr rOut hDisj).count .TOFF = 0 ∧
    (∀ S : Wire n → Prop, (∀ u, S (rInScr u)) → (∀ j, S (rOut j)) →
      DynWires S (pEvenOctBandPers12Unld0 v rInScr rOut hDisj)) := by
  let r64 := appendRegRev42_22 rInScr rOut hDisj; let outW := outWireOfRegRev eo_pos22 rOut;
  let cpS : ComputeProg 64 := decodePrimTree 63 pers12Setup4Tree
  rcases decodePrimTree_spec 63 pers12Setup4Tree 0 0 with ⟨hvS, _, haS⟩
  let hVal : BitAssignment n → Fin 22 → ZMod 2 := fun δ ↦
    eoBitFn (evenOctIdxT10K (st δ (rInScr ⟨0, by omega⟩) == 1)
      (natOfZModBits 18 (fun b ↦ st δ (rInScr ⟨1 + b.val, by omega⟩))))
  let gRev : BitAssignment n → ℕ → ZMod 2 := fun δ t ↦
    hVal δ ⟨21 - (t % 22), by omega⟩
  let stBase : BitAssignment n → BitAssignment n := fun δ ↦ stepCB r64 cpS.fwdBits (st δ)
  let γ0 : BitAssignment n → BitAssignment n := fun δ ↦
      writeReg (st δ) rInScr (fun u ↦ if u.val < 19 then st δ (rInScr u) else 0)
  let stRef : BitAssignment n → BitAssignment n := fun δ ↦
      stepCB r64 (decodePrimTree 63 live12FullTree).fwdBits (updPrefixRev eo_pos22 rOut (γ0 δ)
      (gRev δ) 22)
  have hγ0_in0 : ∀ δ, γ0 δ (rInScr ⟨0, by omega⟩) = st δ (rInScr ⟨0, by omega⟩) := fun δ ↦ by
    dsimp only [γ0]; rw [writeReg_apply_reg]; rfl
  have hγ0_d2 : ∀ δ,
      (fun b : Fin 18 ↦ γ0 δ (rInScr ⟨1 + b.val, by omega⟩)) =
        fun b ↦ st δ (rInScr ⟨1 + b.val, by omega⟩) := fun δ ↦ funext fun b ↦ by
    dsimp only [γ0]; rw [writeReg_apply_reg, _root_.ite_eq_left (by dsimp; omega)]
  have hγ0_z19 : ∀ (u : Fin 42) (δ : BitAssignment n), 19 ≤ u.val → γ0 δ (rInScr u) = 0 :=
    fun u δ hu ↦ by dsimp only [γ0]; rw [writeReg_apply_reg, _root_.ite_eq_right (by omega)]
  have hStepWBEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      stepCB r64 cpS.fwdBits (stWB δ) = updRange outW (stBase δ) (gRev δ) 0 22 :=
    fun δ hz ↦ by
      have hwbRange : stWB δ = updRange outW (st δ) (gRev δ) 0 22 := by
        have h1 := updRange_eq_updPrefixRev eo_pos22 rOut (st δ) (gRev δ) 0 22;
        have h2 :=
            updPrefixRev_eq_writeReg eo_pos22 rOut (st δ)
            (hVal δ); exact (hWB δ hz).trans (h2.symm.trans h1.symm)
      rw [hwbRange]
      exact stepCB_decodePrimTree_updRange_comm rInScr rOut hDisj pers12Setup4Tree
        (by decide : 35 ≤ 42) pers12Setup4Tree_loc.1 pers12Setup4Tree_loc.2
        (st δ) (gRev δ) 0 le_rfl 22 le_rfl
  have hOutEq64 {i : ℕ} (hi : i < 22) : outW i = r64 ⟨42 + i, by omega⟩ :=
    outWireOfRegRev_eq_appendRegRev42_22 rInScr rOut hDisj hi
  have hBaseOut0 (i : ℕ) (hi : i < 22) (δ : BitAssignment n)
      (hz : ∀ k : Fin W, δ (rWork k) = 0) : stBase δ (outW (0 + i)) = 0 := by
    rw [Nat.zero_add, hOutEq64 hi]
    dsimp only [stBase, cpS]
    rw [stepCB_decodePrimTree_outside r64 pers12Setup4Tree pers12Setup4Tree_loc.1 _ _
          (fun ⟨_, h⟩ ↦
            absurd h (Nat.not_lt.mpr (Nat.le_trans (by decide) (Nat.le_add_right 42 i)))),
        ← hOutEq64 hi]
    exact hOut0 _ δ hz
  have hRefUpd (δ : BitAssignment n) (_ : ∀ k : Fin W, δ (rWork k) = 0)
      (t : ℕ) (ht : t < 22) : stRef δ (outW (0 + t)) = gRev δ (0 + t) := by
    rw [Nat.zero_add, hOutEq64 ht]
    dsimp only [stRef]
    rw [stepCB_decodePrimTree_outside r64 live12FullTree live12FullTree_targets _ _
          (fun ⟨_, h⟩ ↦
            absurd h (Nat.not_lt.mpr (Nat.le_trans (by decide) (Nat.le_add_right 42 t)))),
        ← hOutEq64 ht]
    exact updPrefixRev_apply_lt eo_pos22 rOut (γ0 δ) (gRev δ) ht le_rfl
  have hParityRef : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      ∀ i < 22, czPairsParity (utPairs r64 (live12QuadMask (0 + i))) (stRef δ) = gRev δ (0 + i) :=
    fun δ hz i hi ↦ by
      rw [Nat.zero_add]
      have hd2γ : natOfZModBits 18 (fun b ↦ γ0 δ (rInScr ⟨1 + b.val, by omega⟩)) < 196608 := by
        rw [hγ0_d2 δ]; exact hd2Lt δ hz
      have hp :=
          live12Full_parity_eq rInScr rOut hDisj (γ0 δ) hd2γ (fun u hu ↦ hγ0_z19 u δ hu) ⟨i, hi⟩
      dsimp only at hp; rw [hγ0_in0 δ, hγ0_d2 δ] at hp
      exact hp.trans (congrArg (hVal δ) (Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt hi]))).symm
  have hAgreeLo : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      ∀ u : Fin 64, u.val < 64 → u.val < 42 + 0 → stBase δ (r64 u) = stRef δ (r64 u) :=
    fun δ hz u _ hu42 ↦ by
      set isNN := st δ (rInScr ⟨0, by omega⟩) == 1
      set d2 := natOfZModBits 18 (fun b ↦ st δ (rInScr ⟨1 + b.val, by omega⟩))
      have hd2_196 := hd2Lt δ hz
      have hd2_262 : d2 < 262144 := by omega
      have hd2Pow : d2 < 2 ^ 18 := hd2_262
      let nn := if isNN then 1 else 0
      have hnn : nn = 0 ∨ nn = 1 := by
        dsimp [nn]; cases isNN <;> [exact Or.inl rfl; exact Or.inr rfl]
      have hPF := pers12_ct_facts isNN hd2_196;
      let cOut := evalStrict 35 (coordState 18).2.1 (initDomCT nn) outerDomPre76Tree;
      let cInitU := pers12UnldInitCT nn cOut;
      let cSetup :=
          evalStrict 63 (coordState 18).2.1 cInitU pers12Setup4Tree; obtain ⟨_, hC18, _, _, _⟩ :=
          coordState_spec 18
      have hmx : (coordState 18).2.1.testBit d2 = true := by
        rw [hC18, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hd2Pow
      have hInitLo19 (k : ℕ) (hk42 : k < 42) (hk19 : k < 19) :
          (getCT 7 (initDomCT nn) k).testBit d2 = (st δ (rInScr ⟨k, hk42⟩) == 1) := by
        rw [getCT_initDomCT nn d2 k hd2_262 (by omega)]
        by_cases hk0 : k = 0
        · subst hk0
          simp only [↓reduceIte, nn]
          change (if isNN = true then 1 else 0).beq 1 = isNN
          cases isNN <;> rfl
        · simp only [hk0, hk19, ↓reduceIte]
          exact (natOfZModBits_testBit_lt (fun b : Fin 18 ↦ st δ (rInScr ⟨1 + b.val, by omega⟩))
            (show k - 1 < 18 by omega)).trans
            (congrArg (fun idx ↦ st δ (rInScr idx) == 1) (Fin.ext (Nat.add_sub_of_le (by omega))))
      -- 1. Show (stBase δ (r64 u) == 1) = (getCT 7 cSetup u.val).testBit d2
      let βS : Fin 64 → ZMod 2 := fun k ↦ st δ (r64 k)
      have hInitS (k : ℕ) (hk : k < 64) :
          (getCT 7 cInitU k).testBit d2 = (natOfZModBits 64 βS).testBit k := by
        have hlen43 := pers12PadCols43_length cOut
        rw [natOfZModBits_testBit_lt βS hk]
        dsimp only [cInitU, pers12UnldInitCT, βS]
        rw [getCT_setColsAt (pers12PadCols43 cOut) 21 (initDomCT nn) (by omega)
              (fun t ht ↦ initDomCT_zero_21_43 nn hnn t (by omega)) k (by omega)]
        by_cases hk42 : k < 42
        · rw [appendRegRev42_22_lo rInScr rOut hDisj ⟨k, hk⟩ hk42]
          by_cases hk21 : k < 21
          · rw [_root_.ite_eq_left hk21]
            by_cases hk19 : k < 19
            · exact hInitLo19 k hk42 hk19
            · rw [getCT_initDomCT nn d2 k hd2_262 (by omega), _root_.ite_eq_right (by omega),
                  _root_.ite_eq_right hk19]
              rcases (show k = 19 ∨ k = 20 by omega) with rfl | rfl
              · rw [(hZ19_20 δ hz).1]
                rfl
              · rw [(hZ19_20 δ hz).2]
                rfl
          · rw [_root_.ite_eq_right hk21, pers12PadCols43_getD cOut (show k - 21 < 43 by omega)]
            by_cases hk35 : k < 35
            · let s : Fin 14 := ⟨k - 21, by omega⟩
              have hfin : (⟨k, hk42⟩ : Fin 42) = ⟨21 + s.val, by omega⟩ :=
                Fin.ext (show k = 21 + (k - 21) by omega)
              rw [_root_.ite_eq_left (show k - 21 < 14 by omega), hfin, hChain s δ hz]
              exact (hPF.2.1 s).trans (by cases chain14Bit isNN d2 s <;> rfl)
            · rw [_root_.ite_eq_right (show ¬(k - 21 < 14) by omega), Nat.zero_testBit,
                  hZ35_41 ⟨k, hk42⟩ δ (Nat.not_lt.mp hk35) hz]
              rfl
        · rw [_root_.ite_eq_right (by omega), pers12PadCols43_getD cOut (by omega),
              _root_.ite_eq_right (by omega), Nat.zero_testBit,
              appendRegRev42_22_hi rInScr rOut hDisj ⟨k, hk⟩ hk42]
          dsimp only [outWireOfRegRev]
          rw [hOut0 _ δ hz]
          rfl
      have hTreeBit (t : PrimTree) (c0 : CT) (γ : BitAssignment n)
          (hInit : ∀ k < 64, (getCT 7 c0 k).testBit d2 =
            (natOfZModBits 64 (fun k ↦ γ (r64 k))).testBit k) :
          (stepCB r64 (decodePrimTree 63 t).fwdBits γ (r64 u) == 1) =
            (getCT 7 (evalStrict 63 (coordState 18).2.1 c0 t) u.val).testBit d2 := by
        let βG : Fin 64 → ZMod 2 := fun k ↦ γ (r64 k)
        dsimp only [stepCB]
        rw [writeReg_apply_reg]
        exact (fwdBits_decodePrimTree_testBit t βG (natOfZModBits 64 βG)
          (fun i ↦ (natOfZModBits_testBit_lt βG i.isLt).symm) u).trans
          (evalStrict_sound (by decide : 63 < 128) t c0 (natOfZModBits 64 βG)
            d2 hmx hInit u.val u.isLt).symm
      -- 2. Show (stRef δ (r64 u) == 1) = (getCT 7 (fullLive12CT nn) u.val).testBit d2
      let γ22 := updPrefixRev eo_pos22 rOut (γ0 δ) (gRev δ) 22
      let βR : Fin 64 → ZMod 2 := fun k ↦ γ22 (r64 k)
      have hInitR : ∀ k < 64,
          (getCT 7 (initRev64CT nn) k).testBit d2 =
            (natOfZModBits 64 βR).testBit k := fun k hk ↦ by
        rw [natOfZModBits_testBit_lt βR hk]; dsimp only [initRev64CT, βR];
        have hlen := expEvenOctRevCols_length nn (coordState 18).2.1 (coordState 18).2.2
        have hset :=
            getCT_setColsAt (expEvenOctRevCols nn (coordState 18).2.1 (coordState 18).2.2) 42
            (initDomCT nn) (by omega)
          (fun t ht ↦ initDomCT_hi0_chk nn hnn t (by omega)) k (by omega)
        rw [hset]
        by_cases hk42 : k < 42
        · rw [_root_.ite_eq_left (by omega : k < 42), appendRegRev42_22_lo rInScr rOut hDisj ⟨k,
              hk⟩ hk42]
          dsimp only [γ22]
          rw [updPrefixRev_apply_in eo_pos22 rInScr rOut hDisj]
          by_cases hk19 : k < 19
          · dsimp only [γ0]
            rw [writeReg_apply_reg, _root_.ite_eq_left (by dsimp; exact hk19)]
            exact hInitLo19 k hk42 hk19
          · have hk0 : k ≠ 0 := by omega
            rw [getCT_initDomCT nn d2 k hd2_262 (by omega), hγ0_z19 ⟨k, hk42⟩ δ (by dsimp; omega)]
            simp only [hk0, hk19, ↓reduceIte]; rfl
        · rw [_root_.ite_eq_right (by omega : ¬(k < 42)),
              appendRegRev42_22_hi rInScr rOut hDisj ⟨k, hk⟩ hk42]
          have ht : k - 42 < 22 := by omega
          dsimp only [γ22];
          rw [updPrefixRev_apply_lt eo_pos22 rOut _ _ ht le_rfl, expEvenOctRevCols_getD _ _ _ ht];
          dsimp only [gRev, hVal]
          have hmod : eoBitFn (evenOctIdxT10K isNN d2) ⟨21 - ((k - 42) % 22), by omega⟩ =
              eoBitFn (evenOctIdxT10K isNN d2) ⟨21 - (k - 42), by omega⟩ :=
            congrArg (eoBitFn (evenOctIdxT10K isNN d2))
                (Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt ht]))
          change _ = (eoBitFn (evenOctIdxT10K isNN d2) ⟨21 - ((k - 42) % 22), by omega⟩ == 1)
          rw [hmod]
          set j0 : Fin 22 := ⟨21 - (k - 42), by omega⟩
          set p0 := evenOctIdxT10K isNN d2
          have h1 : (eoBitFn p0 j0 == 1) = (if j0.val < 8 then p0.1.testBit j0.val else if j0.val <
              18 then p0.2.1.testBit (j0.val - 8) else p0.2.2.testBit (j0.val - 18)) := by
            dsimp only [eoBitFn]
            cases (if j0.val < 8 then p0.1.testBit j0.val
                   else if j0.val < 18 then p0.2.1.testBit (j0.val - 8)
                   else p0.2.2.testBit (j0.val - 18)) <;> rfl
          rw [h1]
          have he :=
              expEvenOctCols_testBit nn
              (by change (if isNN then 1 else 0) < 2; cases isNN <;> decide) hd2Pow
            j0.val j0.isLt
          have hnnBeq : nn.beq 1 = isNN := by dsimp [nn]; cases isNN <;> rfl
          dsimp only at he; rwa [hnnBeq] at he
      exact PhotochemistrySolution.CoulDom22NoZeroLive232.zmod2_eq_of_beq_one
        ((hTreeBit pers12Setup4Tree cInitU (st δ) hInitS).trans
          ((hPF.2.2.2.2 u.val hu42).trans
            (hTreeBit live12FullTree (initRev64CT nn) γ22 hInitR).symm))
  obtain ⟨hUn, htUn, hfUn, hDynUn⟩ :=
      subspaceStep_pUnloadLive12Range v rWork rInScr rOut hDisj 0 22 64 le_rfl (fun i _ ↦
      live12Quad_lt64 (0 + i)) stBase stRef ph gRev hBaseOut0 hAgreeLo hRefUpd hParityRef
  have hUnWB : SubspaceStep (mkKetOpW rWork (fun δ ↦ stepCB r64 cpS.fwdBits (stWB δ)) ph)
      (mkKetOpW rWork (fun δ ↦ stepCB r64 cpS.fwdBits (st δ)) ph)
      (pUnloadLive12Range v rInScr rOut hDisj 0 22) := by
    have hEqPre : mkKetOpW rWork (fun δ ↦ updRange outW (stBase δ) (gRev δ) 0 22) ph =
        mkKetOpW rWork (fun δ ↦ stepCB r64 cpS.fwdBits (stWB δ)) ph :=
      mkKetOpW_congr rWork (fun δ hz ↦ (hStepWBEq δ hz).symm) (fun _ _ ↦ rfl)
    rwa [hEqPre] at hUn
  have hMask0 {stX : BitAssignment n → BitAssignment n} : ∀ u ∈ maskFinset 64 0,
      ∀ (δ : BitAssignment n), (∀ k : Fin W, δ (rWork k) = 0) → stX δ (r64 u) = 0 :=
    fun u hu _ _ ↦ by
      have hm := mem_maskFinset.mp hu; rw [Nat.zero_testBit] at hm; cases hm
  obtain ⟨hWrap, htW, hfW, hDynW⟩ := subspaceStep_wrapOnReg_vprog2 v rWork
    r64 (maskFinset 64 0) cpS 0
    (maskFinset_zero 64 ▸ StructuredCB.validProg_of_validProgMask (hvS.trans
        pers12Setup4Tree_check.1))
    (haS.trans pers12Setup4Tree_check.2)
    stWB st ph ph (pUnloadLive12Range v rInScr rOut hDisj 0 22) hMask0 hMask0 hUnWB
  refine ⟨hWrap, ?_, ?_, ?_⟩
  · change (wrapDynOnReg v r64 cpS (pUnloadLive12Range v rInScr rOut hDisj 0 22)).count .T = 0;
    rw [htW, htUn]
  · change (wrapDynOnReg v r64 cpS (pUnloadLive12Range v rInScr rOut hDisj 0 22)).count .TOFF = 0;
    rw [hfW, hfUn]
  · intro S hr ho
    have hr64 : ∀ u : Fin 64, S (r64 u) := fun u ↦ by
      by_cases hu : u.val < 42
      · rw [appendRegRev42_22_lo rInScr rOut hDisj u hu]; exact hr _
      · rw [appendRegRev42_22_hi rInScr rOut hDisj u hu]; exact ho _
    exact hDynW S hr64 (hDynUn S hr ho)

/-!
### 6. `0 T` `Z8` /`Z4` Scrub/Restore & `168 T` Persistent-`12` Domain Wrapper `pDomSplitPers12_168`
-/

def rPers12Of {n : ℕ} (r : QRegister (54 + 123) n) : QRegister 12 n :=
  ⟨⟨fun p : Fin 12 ↦ r ⟨143 + p.val, by omega⟩, fun a b e ↦ by
    have hv := congrArg Fin.val (r.wires.injective e)
    dsimp at hv; exact Fin.ext (by omega)⟩⟩

def cScrubZ8Z4 {n : ℕ} (r : QRegister (54 + 123) n) : Circuit n :=
  have rInj : ∀ {a b : Fin (54 + 123)}, r a = r b → a.val = b.val :=
    fun h ↦ congrArg Fin.val (r.wires.injective h)
  let w16 := r ⟨16, by decide⟩
  let w17 := r ⟨17, by decide⟩
  let w122 := r ⟨122, by decide⟩
  let w123 := r ⟨123, by decide⟩
  let w150 := r ⟨146, by decide⟩
  let w178 := r ⟨174, by decide⟩
  let w179 := r ⟨175, by decide⟩
  Circuit.X w122 ;;ᶜ
  Circuit.CNOT w16 w122 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w17 w122 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w179 w122 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w150 w123 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w179 w123 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w178 w123 (fun e ↦ by have hv := rInj e; dsimp at hv; omega)

def cRestoreZ4Z8 {n : ℕ} (r : QRegister (54 + 123) n) : Circuit n :=
  have rInj : ∀ {a b : Fin (54 + 123)}, r a = r b → a.val = b.val :=
    fun h ↦ congrArg Fin.val (r.wires.injective h)
  let w16 := r ⟨16, by decide⟩
  let w17 := r ⟨17, by decide⟩
  let w122 := r ⟨122, by decide⟩
  let w123 := r ⟨123, by decide⟩
  let w150 := r ⟨146, by decide⟩
  let w178 := r ⟨174, by decide⟩
  let w179 := r ⟨175, by decide⟩
  Circuit.CNOT w178 w123 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w179 w123 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w150 w123 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w179 w122 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w17 w122 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.CNOT w16 w122 (fun e ↦ by have hv := rInj e; dsimp at hv; omega) ;;ᶜ
  Circuit.X w122

theorem cScrubZ8Z4_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (r : QRegister (54 + 123) n) (hRS : ∀ i, S (r i)) :
    (DynamicCircuit.circuit (Var := Var) (cScrubZ8Z4 r)).count .T = 0 ∧
    (DynamicCircuit.circuit (Var := Var) (cScrubZ8Z4 r)).count .TOFF = 0 ∧
    DynWires S (DynamicCircuit.circuit (Var := Var) (cScrubZ8Z4 r)) :=
  ⟨rfl, rfl,
   ⟨cw_1 (hRS _), cw_cnot (hRS _) (hRS _), cw_cnot (hRS _) (hRS _),
    cw_cnot (hRS _) (hRS _), cw_cnot (hRS _) (hRS _),
    cw_cnot (hRS _) (hRS _), cw_cnot (hRS _) (hRS _)⟩⟩

theorem cRestoreZ4Z8_counts_wires {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (r : QRegister (54 + 123) n) (hRS : ∀ i, S (r i)) :
    (DynamicCircuit.circuit (Var := Var) (cRestoreZ4Z8 r)).count .T = 0 ∧
    (DynamicCircuit.circuit (Var := Var) (cRestoreZ4Z8 r)).count .TOFF = 0 ∧
    DynWires S (DynamicCircuit.circuit (Var := Var) (cRestoreZ4Z8 r)) :=
  ⟨rfl, rfl,
   ⟨cw_cnot (hRS _) (hRS _), cw_cnot (hRS _) (hRS _), cw_cnot (hRS _) (hRS _),
    cw_cnot (hRS _) (hRS _), cw_cnot (hRS _) (hRS _),
    cw_cnot (hRS _) (hRS _), cw_1 (hRS _)⟩⟩

theorem cScrubZ8Z4_mulVec_ket {n : ℕ} (r : QRegister (54 + 123) n) (β : BitAssignment n) :
    (cScrubZ8Z4 r).eval.1.mulVec (ket β) =
      ket (Function.update
        (Function.update β (r ⟨122, by decide⟩)
          (β (r ⟨122, by decide⟩) + 1 + β (r ⟨16, by decide⟩) +
            β (r ⟨17, by decide⟩) + β (r ⟨175, by decide⟩)))
        (r ⟨123, by decide⟩)
          (β (r ⟨123, by decide⟩) + β (r ⟨146, by decide⟩) +
            β (r ⟨175, by decide⟩) + β (r ⟨174, by decide⟩))) := by
  unfold cScrubZ8Z4
  simp only [eval_seq_mulVec, ket_X, ket_CNOT]
  exact congrArg ket (funext fun w ↦ by
    simp only [Function.update_apply, r.wires.injective.eq_iff, Fin.ext_iff, ↓reduceIte,
      Nat.reduceEqDiff]
    split_ifs <;> rfl)

theorem cRestoreZ4Z8_mulVec_ket {n : ℕ} (r : QRegister (54 + 123) n) (β : BitAssignment n) :
    (cRestoreZ4Z8 r).eval.1.mulVec (ket β) =
      ket (Function.update
        (Function.update β (r ⟨123, by decide⟩)
          (β (r ⟨123, by decide⟩) + β (r ⟨174, by decide⟩) +
            β (r ⟨175, by decide⟩) + β (r ⟨146, by decide⟩)))
        (r ⟨122, by decide⟩)
          (β (r ⟨122, by decide⟩) + β (r ⟨175, by decide⟩) +
            β (r ⟨17, by decide⟩) + β (r ⟨16, by decide⟩) + 1)) := by
  unfold cRestoreZ4Z8
  simp only [eval_seq_mulVec, ket_X, ket_CNOT]
  exact congrArg ket (funext fun w ↦ by
    simp only [Function.update_apply, r.wires.injective.eq_iff, Fin.ext_iff, ↓reduceIte,
      Nat.reduceEqDiff]
    split_ifs <;> rfl)

theorem zmod2_scrub_z8 (b16 b17 b20 : Bool) :
    (if !(xor (xor b16 b17) b20) then (1 : ZMod 2) else 0) + 1 + (if b16 then 1 else 0) +
    (if b17 then 1 else 0) + (if b20 then 1 else 0) = 0 := by
  cases b16 <;> cases b17 <;> cases b20 <;> decide

theorem zmod2_scrub_z4 (p3 b20 b19 : Bool) : (if xor (xor p3 b20) b19 then (1 : ZMod 2) else 0) +
    (if p3 then 1 else 0) + (if b20 then 1 else 0) + (if b19 then 1 else 0) = 0 := by
  cases p3 <;> cases b20 <;> cases b19 <;> decide

theorem zmod2_restore_z4 (p3 b20 b19 : Bool) : (0 : ZMod 2) + (if b19 then 1 else 0) +
    (if b20 then 1 else 0) + (if p3 then 1 else 0) = if xor (xor p3 b20) b19 then 1 else 0 := by
  cases p3 <;> cases b20 <;> cases b19 <;> decide

theorem zmod2_restore_z8 (b16 b17 b20 : Bool) : (0 : ZMod 2) + (if b20 then 1 else 0) +
    (if b17 then 1 else 0) + (if b16 then 1 else 0) + 1 =
    if !(xor (xor b16 b17) b20) then 1 else 0 := by
  cases b16 <;> cases b17 <;> cases b20 <;> decide

noncomputable def stDomPers12 {n : ℕ} (wNN : Wire n) (r : QRegister (54 + 123) n)
    (s : BitAssignment n → BitAssignment n) (δ : BitAssignment n) : BitAssignment n :=
  let isNN := s δ wNN == 1
  let d2 := natOfZModBits 18 (fun b ↦ s δ (r ⟨b.val, potGen_d2_lt 123 b⟩))
  let p := evenOctIdxT10K isNN d2
  writeReg
    (writeReg (s δ) (rPers12Of r) (fun q ↦ if pers12Bit isNN d2 q then 1 else 0))
    (rTop22Hi (by decide : 90 ≤ 123) r)
    (fun j ↦ if dom22Bit p j then 1 else 0)

def pDomSplitPers12_168 {Var : Type} {n : ℕ} (v : Var) (wNN : Wire n) (r : QRegister (54 + 123) n)
    (hw : ∀ i, wNN ≠ r i) (inner : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let rTop := rTop22Hi (by decide : 90 ≤ 123) r
  let hDisj := domPers_disj_top hw
  wrapDynOnReg v (rOuter36 hw) (decodePrimTree 35 outerDomPre76Tree)
    (.seq (pEvenOctBandDomRem112 v (rDom118Pers hw) rTop hDisj.1)
      (.seq (.circuit (cScrubZ8Z4 r))
        (.seq inner
          (.seq (.circuit (cRestoreZ4Z8 r))
            (pEvenOctBandPers12Unld0 v (rUnld42Pers hw) rTop hDisj.2)))))

theorem apply_y36_zero {n : ℕ} {r : QRegister (54 + 123) n} {β : BitAssignment n}
    (hY0 : ∀ b : Fin 36, β (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) = 0) (idx : Fin (54 + 123))
    (hlo : 18 ≤ idx.val) (hhi : idx.val < 54) : β (r idx) = 0 := by
  let b : Fin 36 := ⟨idx.val - 18, by omega⟩
  have hEq : idx = ⟨18 + b.val, potGen_y36_lt 123 b⟩ := Fin.ext (by dsimp [b]; omega)
  rw [hEq]; exact hY0 b

theorem apply_k123_zero {n : ℕ} {r : QRegister (54 + 123) n} {β : BitAssignment n}
    (hK0 : ∀ u : Fin 123, β (r ⟨54 + u.val, potGen_k_lt 123 u⟩) = 0) (idx : Fin (54 + 123))
    (hlo : 54 ≤ idx.val) : β (r idx) = 0 := by
  let u : Fin 123 := ⟨idx.val - 54, by omega⟩
  have hEq : idx = ⟨54 + u.val, potGen_k_lt 123 u⟩ := Fin.ext (by dsimp [u]; omega)
  rw [hEq]; exact hK0 u

theorem stepCB_outerDomPre_props {n : ℕ} {wNN : Wire n} {r : QRegister (54 + 123) n}
    (hw : ∀ i, wNN ≠ r i) (β : BitAssignment n)
    (hd2 : natOfZModBits 18 (fun b ↦ β (r ⟨b.val, potGen_d2_lt 123 b⟩)) < 196608)
    (hY0 : ∀ b : Fin 36, β (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) = 0)
    (hK0 : ∀ u : Fin 123, β (r ⟨54 + u.val, potGen_k_lt 123 u⟩) = 0) :
    let stO := stepCB (rOuter36 hw) (decodePrimTree 35 outerDomPre76Tree).fwdBits β;
    let isNN := β wNN == 1
    let d2 := natOfZModBits 18 (fun b ↦ β (r ⟨b.val, potGen_d2_lt 123 b⟩))
    (∀ s : Fin 14, stO (r (chain14RIdx s)) = if chain14Bit isNN d2 s then 1 else 0) ∧
    (∀ w : Wire n, (∀ s : Fin 14, w ≠ r (chain14RIdx s)) → stO w = β w) ∧
    (natOfZModBits 118 (fun i ↦ stO (rDom118Pers hw i)) =
      evalPrimTree 35 (natOfZModBits 118 (fun i ↦ β (rDom118Pers hw i))) outerDomPre76Tree) := by
  dsimp only
  have rInj : ∀ {a b : Fin (54 + 123)}, r a = r b → a.val = b.val :=
    fun h ↦ congrArg Fin.val (r.wires.injective h)
  set isNN := β wNN == 1
  set d2 := natOfZModBits 18 (fun b ↦ β (r ⟨b.val, potGen_d2_lt 123 b⟩))
  set stO := stepCB (rOuter36 hw) (decodePrimTree 35 outerDomPre76Tree).fwdBits β
  have hZero36 : ∀ u : Fin 36, 19 ≤ u.val → β (rOuter36 hw u) = 0 := fun u hu ↦ by
    change β (fOuter36 wNN r u) = 0; dsimp only [fOuter36]
    rw [_root_.dite_eq_right (by omega)]
    split_ifs with h22
    · exact apply_y36_zero hY0 _ (by dsimp; omega) (by dsimp; omega)
    · have hb := chain14RIdx_bounds ⟨u.val - 22, by omega⟩
      exact apply_k123_zero hK0 _ (by omega)
  have hd2RegEq : (fun b : Fin 18 ↦ β (rOuter36 hw ⟨1 + b.val, by omega⟩)) =
      (fun b : Fin 18 ↦ β (r ⟨b.val, potGen_d2_lt 123 b⟩)) := funext fun b ↦ by
    change β (fOuter36 wNN r ⟨1 + b.val, by omega⟩) = _
    dsimp only [fOuter36]
    rw [_root_.dite_eq_right (by omega), _root_.dite_eq_left (by omega)]
    exact congrArg β (congrArg r.wires (Fin.ext (by dsimp; omega)))
  have hx36Eq : natOfZModBits 36 (fun u ↦ β (rOuter36 hw u)) = (if isNN then 1 else 0) + 2 *
      (d2 % 262144) := by
    rw [natOfZModBits36_clean19 (fun u ↦ β (rOuter36 hw u)) hZero36, hd2RegEq]
    rfl
  have hStepApply : ∀ u : Fin 36, stO (rOuter36 hw u) =
      if (evalPrimTree 35 ((if isNN then 1 else 0) + 2 *
          (d2 % 262144)) outerDomPre76Tree).testBit u.val
      then 1 else 0 := fun u ↦ by
    dsimp only [stO]; rw [stepCB_decodePrimTree_apply outerDomPre76Tree (rOuter36 hw) β u, hx36Eq]
  have hPF := pers12_ct_facts isNN hd2
  have hChain : ∀ s : Fin 14, stO (r (chain14RIdx s)) = if chain14Bit isNN d2 s then 1 else 0 :=
    fun s ↦ by
      have hEqU : r (chain14RIdx s) = rOuter36 hw ⟨22 + s.val, by omega⟩ := by
        symm; change fOuter36 wNN r ⟨22 + s.val, by omega⟩ = _
        dsimp only [fOuter36]; rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega)]
        exact congrArg r.wires (congrArg chain14RIdx (Fin.ext (by dsimp; omega)))
      rw [hEqU, hStepApply]; rfl
  have hPres : ∀ w : Wire n, (∀ s : Fin 14, w ≠ r (chain14RIdx s)) → stO w = β w :=
    fun w hnw ↦ by
      by_cases hm : ∃ u : Fin 36, rOuter36 hw u = w
      · obtain ⟨u, rfl⟩ := hm
        by_cases hu19 : u.val < 19
        · exact stepCB_decodePrimTree_outside (rOuter36 hw) outerDomPre76Tree
            outerDomPre76Tree_targets β u (by omega)
        · by_cases hu22 : u.val < 22
          · rw [hStepApply u, hZero36 u (by omega)]
            rcases (by omega : u.val = 19 ∨ u.val = 20 ∨ u.val = 21) with h19 | h20 | h21
            · rw [h19, hPF.1.1]; rfl
            · rw [h20, hPF.1.2.1]; rfl
            · rw [h21, hPF.1.2.2]; rfl
          · exfalso
            have hEq : rOuter36 hw u = r (chain14RIdx ⟨u.val - 22, by omega⟩) := by
              change fOuter36 wNN r u = _; dsimp only [fOuter36]
              rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right hu22]
            exact hnw ⟨u.val - 22, by omega⟩ hEq
      · exact writeReg_apply_of_not_mem β (rOuter36 hw) _ w hm
  refine ⟨hChain, hPres, ?_⟩
  have hDomEq {k : ℕ} (hk36 : k < 36) :
      rDom118Pers hw ⟨k, by omega⟩ = rOuter36 hw ⟨k, hk36⟩ := by
    change fDom118Pers wNN r ⟨k, by omega⟩ = fOuter36 wNN r ⟨k, hk36⟩
    dsimp only [fDom118Pers]
    rw [_root_.dite_eq_left hk36]
  have hDomHi0 {k : ℕ} (hk36 : ¬ k < 36) (hk118 : k < 118) :
      β (rDom118Pers hw ⟨k, hk118⟩) = 0 := by
    change β (fDom118Pers wNN r ⟨k, hk118⟩) = 0
    dsimp only [fDom118Pers]
    rw [_root_.dite_eq_right hk36]
    split_ifs with hk69
    · exact apply_y36_zero hY0 _ (by dsimp; omega) (by dsimp; omega)
    · exact apply_k123_zero hK0 _ (by dsimp; omega)
  have hBitsZeroGe (m k : ℕ) (f : Fin m → ZMod 2) (hmk : m ≤ k) :
      (natOfZModBits m f).testBit k = false :=
    Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (natOfZModBits_lt m f) (Nat.pow_le_pow_right (by decide) hmk))
  have hx118Eq : natOfZModBits 118 (fun i ↦ β (rDom118Pers hw i)) =
      natOfZModBits 36 (fun u ↦ β (rOuter36 hw u)) := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk36 : k < 36
    · rw [natOfZModBits_testBit_lt _ (by omega : k < 118), natOfZModBits_testBit_lt _ hk36,
          hDomEq hk36]
    · rw [hBitsZeroGe 36 k _ (by omega)]
      by_cases hk118 : k < 118
      · rw [natOfZModBits_testBit_lt _ hk118, hDomHi0 hk36 hk118]
        rfl
      · exact hBitsZeroGe 118 k _ (by omega)
  rw [hx118Eq]
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk36 : k < 36
  · rw [natOfZModBits_testBit_lt _ (by omega : k < 118), hDomEq hk36, hStepApply ⟨k, hk36⟩, hx36Eq]
    cases (evalPrimTree 35 ((if isNN then 1 else 0) + 2 *
        (d2 % 262144)) outerDomPre76Tree).testBit k <;> rfl
  · rw [evalPrimTree_testBit_outside outerDomPre76Tree _ k outerDomPre76Tree_targets (by omega),
        hBitsZeroGe 36 k _ (by omega)]
    by_cases hk118 : k < 118
    · have hnChain : ∀ s : Fin 14, rDom118Pers hw ⟨k, hk118⟩ ≠ r (chain14RIdx s) := fun s e ↦ by
        change fDom118Pers wNN r ⟨k, hk118⟩ = r (chain14RIdx s) at e
        dsimp only [fDom118Pers] at e
        rw [_root_.dite_eq_right hk36] at e
        have hb := chain14RIdx_bounds s
        split_ifs at e <;> (have hv := rInj e; dsimp at hv; omega)
      rw [natOfZModBits_testBit_lt _ hk118, hPres _ hnChain, hDomHi0 hk36 hk118]
      rfl
    · exact hBitsZeroGe 118 k _ (by omega)

theorem pDomSplitPers12_168_counts_wires {Var : Type} [Finite Var] {n : ℕ} {S : Wire n → Prop}
    (v : Var) (wNN : Wire n) (r : QRegister (54 + 123) n) (hw : ∀ i, wNN ≠ r i) (hNS : S wNN)
    (hRS : ∀ i, S (r i)) (inner : DynamicCircuit Var n) :
    (pDomSplitPers12_168 v wNN r hw inner).count .T = 168 + inner.count .T ∧
    (pDomSplitPers12_168 v wNN r hw inner).count .TOFF = inner.count .TOFF ∧ (DynWires S inner →
    DynWires S (pDomSplitPers12_168 v wNN r hw inner)) := by
  let _ := Fintype.ofFinite Var; classical
  have hDomM : dom216M = 117 := rfl
  have rInj : ∀ {a b : Fin (54 + 123)}, r a = r b → a.val = b.val :=
    fun h ↦ congrArg Fin.val (r.wires.injective h)
  let rTop := rTop22Hi (by decide : 90 ≤ 123) r
  let hDisj := domPers_disj_top hw; let cpO := decodePrimTree 35 outerDomPre76Tree;
  have hAnd14 : cpO.numAnd = 14 :=
      (decodePrimTree_spec 35 outerDomPre76Tree 0 outerDomPreSMask).2.2.trans
      outerDomPre76Tree_check.2
  let β0 : BitAssignment n := fun _ ↦ 0
  have hd2Zero : natOfZModBits 18 (fun _ : Fin 18 ↦ (0 : ZMod 2)) < 196608 := by decide
  obtain ⟨hCh0, hPr0, hBits0⟩ :=
    stepCB_outerDomPre_props hw β0 hd2Zero (fun _ ↦ rfl) (fun _ ↦ rfl)
  let stO0 := stepCB (rOuter36 hw) cpO.fwdBits β0
  obtain ⟨_, tRem, fRem, wRem⟩ := subspaceStep_pEvenOctBandDomRem112 v
    (rWork0 n) (rDom118Pers hw) rTop hDisj.1
    (fun _ ↦ β0) (fun _ ↦ stO0) (fun _ ↦ 0) (fun _ _ ↦ hd2Zero) (fun _ _ _ _ ↦ rfl)
    (fun _ w hnw ↦ hPr0 w fun s e ↦ hnw ⟨22 + s.val, by omega⟩ (e.trans (by
      symm
      change fDom118Pers wNN r ⟨22 + s.val, by omega⟩ = _
      dsimp only [fDom118Pers, fOuter36]
      rw [_root_.dite_eq_left (by omega), _root_.dite_eq_right (by omega),
          _root_.dite_eq_right (by omega)]
      exact congrArg r.wires (congrArg chain14RIdx (Fin.ext (Nat.add_sub_cancel_left 22 _))))))
    (fun _ _ ↦ hBits0)
  have hUnldLo0 {u : Fin 42} (hu0 : u.val ≠ 0) (hu21 : u.val < 21) :
      stO0 (rUnld42Pers hw u) = 0 := by
    change stO0 (fUnld42Pers wNN r u) = 0
    dsimp only [fUnld42Pers]
    rw [_root_.dite_eq_right hu0, _root_.dite_eq_left hu21]
    exact hPr0 _ fun s e ↦ by
      have hv := rInj e
      have hb := chain14RIdx_bounds s
      dsimp at hv
      omega
  have hNN0 : (stO0 (rUnld42Pers hw ⟨0, by omega⟩) == 1) = false := by
    have h0 : stO0 (rUnld42Pers hw ⟨0, by omega⟩) = 0 := hPr0 wNN (fun s e ↦ hw _ e)
    rw [h0]; rfl
  have hd2Val0 : natOfZModBits 18 (fun b ↦ stO0 (rUnld42Pers hw ⟨1 + b.val, by omega⟩)) = 0 := by
    have hEqF : (fun b : Fin 18 ↦ stO0 (rUnld42Pers hw ⟨1 + b.val, by omega⟩)) = fun _ ↦ 0 :=
      funext fun b ↦ hUnldLo0 (by dsimp; omega) (by dsimp; omega)
    rw [hEqF]; decide
  obtain ⟨_, tUnld, fUnld, wUnld⟩ := subspaceStep_pEvenOctBandPers12Unld0 v
    (rWork0 n) (rUnld42Pers hw) rTop hDisj.2
    (fun _ ↦ stO0)
    (fun _ ↦ writeReg stO0 rTop (fun j ↦ if dom22Bit (evenOctIdxT10K false 0) j then 1 else 0))
    (fun _ ↦ 0)
    (fun _ _ ↦ hd2Val0 ▸ (by decide))
    (fun _ _ ↦ ⟨hUnldLo0 (by decide) (by decide), hUnldLo0 (by decide) (by decide)⟩)
    (fun s _ _ ↦ by
      rw [hNN0, hd2Val0]
      change stO0 (fUnld42Pers wNN r ⟨21 + s.val, by omega⟩) = _
      dsimp only [fUnld42Pers];
      rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega),
          _root_.dite_eq_left (by omega)]
      have hFin : (⟨21 + s.val - 21, by omega⟩ : Fin 14) = s := Fin.ext (by dsimp; omega)
      rw [hFin]; exact hCh0 s)
    (fun u _ hu _ ↦ by
      change stO0 (fUnld42Pers wNN r u) = 0; dsimp only [fUnld42Pers]
      rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega),
          _root_.dite_eq_right (by omega)]
      exact hPr0 _ fun s e ↦ by
        have hv := rInj e; have hb := chain14RIdx_bounds s; dsimp at hv; omega)
    (fun j _ _ ↦ hPr0 _ fun s e ↦ by
      have hv := rInj e; have hb := chain14RIdx_bounds s; dsimp [rTop, rTop22Hi] at hv; omega)
    (fun _ _ ↦ by dsimp only; rw [hNN0, hd2Val0])
  have cScrub := cScrubZ8Z4_counts_wires (Var := Var) r hRS
  have cRest := cRestoreZ4Z8_counts_wires (Var := Var) r hRS
  let body :=
      DynamicCircuit.seq (pEvenOctBandDomRem112 v (rDom118Pers hw) rTop hDisj.1)
      (.seq (.circuit (cScrubZ8Z4 r)) (.seq inner (.seq (.circuit (cRestoreZ4Z8 r))
      (pEvenOctBandPers12Unld0 v (rUnld42Pers hw) rTop hDisj.2)))); obtain ⟨tO, fO⟩ :=
      counts_wrapDynOnReg v (rOuter36 hw) cpO body
  have hrOuterS : ∀ u, S (rOuter36 hw u) := fun u ↦ by
    change S (fOuter36 wNN r u); dsimp only [fOuter36]
    split_ifs <;> [exact hNS; exact hRS _; exact hRS _]
  have hrDomS : ∀ u, S (rDom118Pers hw u) := fun u ↦ by
    change S (fDom118Pers wNN r u); dsimp only [fDom118Pers]
    split_ifs <;> [exact hrOuterS _; exact hRS _; exact hRS _]
  have hrUnldS : ∀ u, S (rUnld42Pers hw u) := fun u ↦ by
    change S (fUnld42Pers wNN r u); dsimp only [fUnld42Pers]
    split_ifs <;> [exact hNS; exact hRS _; exact hRS _; exact hRS _]
  have hrTopS : ∀ j, S (rTop j) := fun _ ↦ hRS _
  have cScT : (cScrubZ8Z4 r).count .T = 0 := rfl; have cScF : (cScrubZ8Z4 r).count .TOFF = 0 := rfl;
  have cReT : (cRestoreZ4Z8 r).count .T = 0 := rfl;
  have cReF : (cRestoreZ4Z8 r).count .TOFF = 0 := rfl
  refine ⟨?_, ?_, fun hm ↦ dynWires_wrapDynOnReg v (rOuter36 hw) hrOuterS cpO ⟨wRem S hrDomS hrTopS,
      cScrub.2.2, hm, cRest.2.2, wUnld S hrUnldS hrTopS⟩⟩
  · change (wrapDynOnReg v (rOuter36 hw) cpO body).count .T = 168 + inner.count .T; rw [tO, hAnd14];
    dsimp only [body, DynamicCircuit.count]
    rw [tRem, cScT, cReT, tUnld]; omega
  · change (wrapDynOnReg v (rOuter36 hw) cpO body).count .TOFF = inner.count .TOFF; rw [fO];
    dsimp only [body, DynamicCircuit.count]
    rw [fRem, cScF, cReF, fUnld]; omega

theorem chain14_or_nonchain {n : ℕ} (r : QRegister (54 + 123) n) (w : Wire n)
    (hn122 : w ≠ r ⟨122, by decide⟩) (hn123 : w ≠ r ⟨123, by decide⟩)
    (hnP12 : ∀ p : Fin 12, w ≠ rPers12Of r p) :
    ∀ s : Fin 14, w ≠ r (chain14RIdx s) := by
  have hp (s : Fin 14)
      (heq : r (chain14RIdx s) =
        rPers12Of r ⟨if s.val < 7 then s.val else if s.val < 11 then s.val - 1 else s.val - 2,
          by split_ifs <;> omega⟩)
      (e : w = r (chain14RIdx s)) : False :=
    hnP12 _ (heq ▸ e)
  intro s
  fin_cases s <;> first | exact hn122 | exact hn123 | exact hp _ rfl

theorem pDomSplitPers12_168_step_cb2 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n)
    (wNN : Wire n) (r : QRegister (54 + 123) n) (hw : ∀ i, wNN ≠ r i)
    (inner : DynamicCircuit Var n)
    (stPre stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
    (hd2Le : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 18 (fun b ↦ stPre δ (r ⟨b.val, potGen_d2_lt 123 b⟩)) ≤ 195075)
    (hNNEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → stPost δ wNN = stPre δ wNN)
    (hd2Eq : ∀ δ (b : Fin 18), (∀ k : Fin W, δ (rWork k) = 0) →
      stPost δ (r ⟨b.val, potGen_d2_lt 123 b⟩) = stPre δ (r ⟨b.val, potGen_d2_lt 123 b⟩))
    (hY0Pre : ∀ (δ : BitAssignment n) (b : Fin 36), (∀ k : Fin W, δ (rWork k) = 0) →
      stPre δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) = 0)
    (hY0Post : ∀ (δ : BitAssignment n) (b : Fin 36), (∀ k : Fin W, δ (rWork k) = 0) →
      stPost δ (r ⟨18 + b.val, potGen_y36_lt 123 b⟩) = 0)
    (hK0Pre : ∀ (δ : BitAssignment n) (u : Fin 123), (∀ k : Fin W, δ (rWork k) = 0) →
      stPre δ (r ⟨54 + u.val, potGen_k_lt 123 u⟩) = 0)
    (hK0Post : ∀ (δ : BitAssignment n) (u : Fin 123), (∀ k : Fin W, δ (rWork k) = 0) →
      stPost δ (r ⟨54 + u.val, potGen_k_lt 123 u⟩) = 0)
    (hInner : ∀ stDomPre stDomPost : BitAssignment n → BitAssignment n,
      (∀ (δ : BitAssignment n) (w : Wire n),
        (∀ j : Fin 22, w ≠ rTop22Hi (by decide : 90 ≤ 123) r j) →
        (∀ p : Fin 12, w ≠ rPers12Of r p) → stDomPre δ w = stPre δ w) →
      (∀ (δ : BitAssignment n) (w : Wire n),
        (∀ j : Fin 22, w ≠ rTop22Hi (by decide : 90 ≤ 123) r j) →
        (∀ p : Fin 12, w ≠ rPers12Of r p) → stDomPost δ w = stPost δ w) →
      (∀ (δ : BitAssignment n) (j : Fin 22), (∀ k : Fin W, δ (rWork k) = 0) →
        stDomPre δ (rTop22Hi (by decide : 90 ≤ 123) r j) =
          if dom22Bit (evenOctIdxT10K (stPre δ wNN == 1)
            (natOfZModBits 18 (fun b ↦ stPre δ (r ⟨b.val, potGen_d2_lt 123 b⟩)))) j
          then 1 else 0) →
      (∀ (δ : BitAssignment n) (j : Fin 22), (∀ k : Fin W, δ (rWork k) = 0) →
        stDomPost δ (rTop22Hi (by decide : 90 ≤ 123) r j) =
          stDomPre δ (rTop22Hi (by decide : 90 ≤ 123) r j)) →
      (∀ (δ : BitAssignment n) (p : Fin 12), (∀ k : Fin W, δ (rWork k) = 0) →
        stDomPost δ (rPers12Of r p) = stDomPre δ (rPers12Of r p)) →
      SubspaceStep (mkKetOpW rWork stDomPre phPre) (mkKetOpW rWork stDomPost phPost) inner) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
      (pDomSplitPers12_168 v wNN r hw inner) := by
  let _ := Fintype.ofFinite Var; classical
  have hDomM : dom216M = 117 := rfl
  have rInj : ∀ {a b : Fin (54 + 123)}, r a = r b → a.val = b.val :=
    fun h ↦ congrArg Fin.val (r.wires.injective h)
  let rTop := rTop22Hi (by decide : 90 ≤ 123) r
  let rP12 := rPers12Of r; let hDisj := domPers_disj_top hw;
  let cpO := decodePrimTree 35 outerDomPre76Tree
  rcases decodePrimTree_spec 35 outerDomPre76Tree 0 outerDomPreSMask with ⟨hvO, _, haO⟩
  let stOPre : BitAssignment n → BitAssignment n := fun δ ↦
      stepCB (rOuter36 hw) cpO.fwdBits (stPre δ)
  let stOPost : BitAssignment n → BitAssignment n := fun δ ↦
      stepCB (rOuter36 hw) cpO.fwdBits (stPost δ)
  let isNNFn : BitAssignment n → Bool := fun δ ↦ stPre δ wNN == 1
  let d2Fn : BitAssignment n → ℕ := fun δ ↦
      natOfZModBits 18 (fun b ↦ stPre δ (r ⟨b.val, potGen_d2_lt 123 b⟩))
  have hd2Lt196 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → d2Fn δ < 196608 :=
    fun δ hz ↦ Nat.lt_of_le_of_lt (hd2Le δ hz) (by decide)
  have hd2PostEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 18 (fun b ↦ stPost δ (r ⟨b.val, potGen_d2_lt 123 b⟩)) = d2Fn δ :=
    fun δ hz ↦ congrArg (natOfZModBits 18) (funext fun b ↦ hd2Eq δ b hz)
  have hPropsPre (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      (∀ s : Fin 14, stOPre δ (r (chain14RIdx s)) = if chain14Bit (isNNFn δ)
      (d2Fn δ) s then 1 else 0) ∧ (∀ w : Wire n, (∀ s : Fin 14, w ≠ r (chain14RIdx s)) →
      stOPre δ w = stPre δ w) ∧ natOfZModBits 118 (fun i ↦ stOPre δ (rDom118Pers hw i)) =
      evalPrimTree 35 (natOfZModBits 118 (fun i ↦ stPre δ (rDom118Pers hw i))) outerDomPre76Tree :=
      stepCB_outerDomPre_props hw (stPre δ) (hd2Lt196 δ hz) (fun b ↦ hY0Pre δ b hz)
      (fun u ↦ hK0Pre δ u hz)
  have hPropsPost (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      (∀ s : Fin 14, stOPost δ (r (chain14RIdx s)) =
        if chain14Bit (stPost δ wNN == 1)
          (natOfZModBits 18 (fun b ↦ stPost δ (r ⟨b.val, potGen_d2_lt 123 b⟩))) s then 1 else 0) ∧
      (∀ w : Wire n, (∀ s : Fin 14, w ≠ r (chain14RIdx s)) → stOPost δ w = stPost δ w) ∧
      natOfZModBits 118 (fun i ↦ stOPost δ (rDom118Pers hw i)) =
        evalPrimTree 35 (natOfZModBits 118 (fun i ↦
            stPost δ (rDom118Pers hw i))) outerDomPre76Tree :=
    stepCB_outerDomPre_props hw (stPost δ) (by rw [hd2PostEq δ hz]; exact hd2Lt196 δ hz)
      (fun b ↦ hY0Post δ b hz) (fun u ↦ hK0Post δ u hz)
  have hd2DomEq : ∀ (s : BitAssignment n) (b : Fin 18),
      s (rDom118Pers hw ⟨1 + b.val, dom216_1add_lt b⟩) = s (r ⟨b.val, potGen_d2_lt 123 b⟩) :=
    fun s b ↦ by
      change s (fDom118Pers wNN r ⟨1 + b.val, _⟩) = _; dsimp only [fDom118Pers, fOuter36]
      rw [_root_.dite_eq_left (by omega), _root_.dite_eq_right (by omega),
          _root_.dite_eq_left (by omega)]
      exact congrArg s (congrArg r.wires (Fin.ext (by dsimp; omega)))
  have hNNDomEq : ∀ (s : BitAssignment n),
      s (rDom118Pers hw ⟨0, Nat.succ_pos dom216M⟩) = s wNN := fun _ ↦ rfl
  -- Step 1: Forward pEvenOctBandDomRem112
  obtain ⟨hSRem, _, _, _⟩ := subspaceStep_pEvenOctBandDomRem112 v rWork
    (rDom118Pers hw) rTop hDisj.1 stPre stOPre phPre
    (fun δ hz ↦ by
      have hEq : (fun b ↦ stPre δ (rDom118Pers hw ⟨1 + b.val, dom216_1add_lt b⟩)) =
          (fun b ↦ stPre δ (r ⟨b.val, potGen_d2_lt 123 b⟩)) := funext (hd2DomEq (stPre δ))
      rw [hEq]; exact hd2Lt196 δ hz)
    (fun u δ hu hz ↦ by
      change stPre δ (fDom118Pers wNN r u) = 0; dsimp only [fDom118Pers, fOuter36]; split_ifs
      · omega
      · exact apply_y36_zero (fun b ↦ hY0Pre δ b hz) _ (by dsimp; omega) (by dsimp; omega)
      · have hb := chain14RIdx_bounds ⟨u.val - 22, by omega⟩
        exact apply_k123_zero (fun v ↦ hK0Pre δ v hz) _ (by omega)
      · exact apply_y36_zero (fun b ↦ hY0Pre δ b hz) _ (by dsimp; omega) (by dsimp; omega)
      · exact apply_k123_zero (fun v ↦ hK0Pre δ v hz) _ (by dsimp; omega))
    (fun δ w hnw ↦ by
      by_cases hm : ∃ u : Fin 36, rOuter36 hw u = w
      · obtain ⟨u, rfl⟩ := hm
        have hEq : rOuter36 hw u = rDom118Pers hw ⟨u.val, by omega⟩ := by
          symm; change fDom118Pers wNN r ⟨u.val, by omega⟩ = fOuter36 wNN r u
          dsimp only [fDom118Pers]; rw [_root_.dite_eq_left u.isLt]
        exact absurd hEq (hnw ⟨u.val, by omega⟩)
      · exact writeReg_apply_of_not_mem (stPre δ) (rOuter36 hw) _ w hm)
    (fun δ hz ↦ (hPropsPre δ hz).2.2)
  set stRemPre := fun δ ↦ writeReg (stOPre δ) rTop (fun j ↦
    let p :=
        evenOctIdxT10K (stPre δ (rDom118Pers hw ⟨0, Nat.succ_pos dom216M⟩) == 1)
        (natOfZModBits 18 (fun b ↦ stPre δ (rDom118Pers hw ⟨1 + b.val, dom216_1add_lt b⟩)))
    stPre δ (rTop j) + if dom22Bit p j then 1 else 0)
  let stDomPre := stDomPers12 wNN r stPre; let stDomPost := stDomPers12 wNN r stPost
  have hP12DisjTop : rP12.DisjointWires rTop := disj_of_ne fun p j e ↦ by
    have hv := rInj e; dsimp [rP12, rPers12Of, rTop, rTop22Hi] at hv; omega
  have hnTopIdx : ∀ (idx : Fin (54 + 123)), idx.val < 155 → ∀ j : Fin 22, r idx ≠ rTop j :=
    fun idx _ j e ↦ by have hv := rInj e; dsimp [rTop, rTop22Hi] at hv; omega
  have hTop174 : r ⟨174, by decide⟩ = rTop ⟨19, by decide⟩ := rfl
  have hTop175 : r ⟨175, by decide⟩ = rTop ⟨20, by decide⟩ := rfl
  have hDomOut (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n) (w : Wire n)
      (hnTop : ∀ j : Fin 22, w ≠ rTop j) (hnP12 : ∀ p : Fin 12, w ≠ rP12 p) :
      stDomPers12 wNN r st δ w = st δ w := by
    dsimp only [stDomPers12]
    rw [writeReg_apply_of_not_mem _ rTop _ w (fun ⟨j, hj⟩ ↦ hnTop j hj.symm),
        writeReg_apply_of_not_mem _ rP12 _ w (fun ⟨p, hp⟩ ↦ hnP12 p hp.symm)]
  have hDomLt143 (st : BitAssignment n → BitAssignment n) (δ : BitAssignment n)
      {idx : Fin (54 + 123)} (hlt : idx.val < 143) :
      stDomPers12 wNN r st δ (r idx) = st δ (r idx) :=
    hDomOut st δ (r idx) (hnTopIdx idx (by omega)) fun p hp ↦ by
      have hv := rInj hp
      dsimp [rP12, rPers12Of] at hv
      omega
  have hNon122_123 (st : BitAssignment n → BitAssignment n)
      (stO stW : BitAssignment n) (δ : BitAssignment n)
      (hTop : ∀ j : Fin 22, stW (rTop j) =
        if dom22Bit (evenOctIdxT10K (st δ wNN == 1)
          (natOfZModBits 18 (fun b ↦ st δ (r ⟨b.val, potGen_d2_lt 123 b⟩)))) j then 1 else 0)
      (hNonTop : ∀ x : Wire n, (∀ j : Fin 22, x ≠ rTop j) → stW x = stO x)
      (hCh : ∀ s : Fin 14, stO (r (chain14RIdx s)) =
        if chain14Bit (st δ wNN == 1)
          (natOfZModBits 18 (fun b ↦ st δ (r ⟨b.val, potGen_d2_lt 123 b⟩))) s then 1 else 0)
      (hPr : ∀ w : Wire n, (∀ s : Fin 14, w ≠ r (chain14RIdx s)) → stO w = st δ w)
      {w : Wire n} (hw122 : w ≠ r ⟨122, by decide⟩) (hw123 : w ≠ r ⟨123, by decide⟩) :
      stW w = stDomPers12 wNN r st δ w := by
    by_cases hmTop : ∃ j : Fin 22, rTop j = w
    · obtain ⟨j, rfl⟩ := hmTop
      dsimp only [stDomPers12]
      rw [hTop j, writeReg_apply_reg]
    · dsimp only [stDomPers12]
      rw [writeReg_apply_of_not_mem _ rTop _ w hmTop, hNonTop w (fun j hj ↦ hmTop ⟨j, hj.symm⟩)]
      by_cases hmP12 : ∃ p : Fin 12, rP12 p = w
      · obtain ⟨p, rfl⟩ := hmP12
        rw [writeReg_apply_reg, show rP12 p = r (chain14RIdx (pers12Idx p)) from
          congrArg r.wires (chain14RIdx_pers12 p).symm]
        exact hCh (pers12Idx p)
      · rw [writeReg_apply_of_not_mem _ rP12 _ w hmP12]
        exact hPr w (chain14_or_nonchain r w hw122 hw123 (fun p hp ↦ hmP12 ⟨p, hp.symm⟩))
  have sCircKet {stA stB : BitAssignment n → BitAssignment n} {ph : BitAssignment n → ZMod 2}
      {c : Circuit n} {f : BitAssignment n → BitAssignment n}
      (hc : ∀ β, c.eval.1.mulVec (ket β) = ket (f β))
      (hf : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → ∀ w, f (stA δ) w = stB δ w) :
      SubspaceStep (Var := Var) (mkKetOpW rWork stA ph) (mkKetOpW rWork stB ph)
        (DynamicCircuit.circuit (Var := Var) c) := by
    refine subspaceStep_congr_out
      (subspaceStep_of_circuit (Var := Var) (mkKetOpW rWork stA ph) c) (matrix_ext_ket fun δ ↦ ?_)
    rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · rw [Matrix.mulVec_smul, hc, funext (hf δ hz)]
    · rw [Matrix.mulVec_zero]
  -- Step 2: Scrub Z8, Z4 on r[122], r[123]
  have hSScrub : SubspaceStep (Var := Var)
      (mkKetOpW rWork stRemPre phPre) (mkKetOpW rWork stDomPre phPre)
      (DynamicCircuit.circuit (Var := Var) (cScrubZ8Z4 r)) :=
    sCircKet (cScrubZ8Z4_mulVec_ket r) fun δ hz w ↦ by
      obtain ⟨hCh, hPr, _⟩ := hPropsPre δ hz
      have hPF := pers12_ct_facts (isNNFn δ) (hd2Lt196 δ hz)
      have hRemTop (j : Fin 22) : stRemPre δ (rTop j) =
          if dom22Bit (evenOctIdxT10K (isNNFn δ) (d2Fn δ)) j then 1 else 0 := by
        have hTop0 : stPre δ (rTop j) = 0 :=
          apply_k123_zero (fun v ↦ hK0Pre δ v hz) _ (by
            dsimp [rTop, rTop22Hi]
            omega)
        dsimp only [stRemPre]
        rw [writeReg_apply_reg, hNNDomEq (stPre δ), funext (hd2DomEq (stPre δ)), hTop0, zero_add]
      have hRemNonTop (x : Wire n) (hnx : ∀ j : Fin 22, x ≠ rTop j) :
          stRemPre δ x = stOPre δ x :=
        writeReg_apply_of_not_mem _ rTop _ x (fun ⟨j, hj⟩ ↦ hnx j hj.symm)
      by_cases hw123 : w = r ⟨123, by decide⟩
      · subst hw123
        simp only [Function.update_self]
        rw [(hRemNonTop (r ⟨123, by decide⟩) (hnTopIdx ⟨123, by decide⟩ (by decide))).trans
              (hCh ⟨11, by decide⟩),
            show stRemPre δ (r ⟨146, by decide⟩) =
                if pers12Bit (isNNFn δ) (d2Fn δ) ⟨3, by decide⟩ then 1 else 0 from
              (hRemNonTop (r ⟨146, by decide⟩) (hnTopIdx ⟨146, by decide⟩ (by decide))).trans
                (hCh ⟨3, by decide⟩),
            hTop175, hTop174, hRemTop ⟨20, by decide⟩, hRemTop ⟨19, by decide⟩,
            hPF.2.2.2.1, zmod2_scrub_z4]
        exact ((@hDomLt143 stPre δ ⟨123, by decide⟩ (by decide)).trans
          (hK0Pre δ ⟨69, by decide⟩ hz)).symm
      · rw [Function.update_of_ne hw123]
        by_cases hw122 : w = r ⟨122, by decide⟩
        · subst hw122
          simp only [Function.update_self]
          have hBitPre (b : Fin 18) : stRemPre δ (r ⟨b.val, potGen_d2_lt 123 b⟩) =
              if (d2Fn δ).testBit b.val then 1 else 0 := by
            rw [hRemNonTop _ (hnTopIdx _ (Nat.lt_trans b.isLt (by decide))),
                hPr _ (fun s e ↦ by
                  have hv := rInj e
                  have hb := chain14RIdx_bounds s
                  have := b.isLt
                  dsimp at hv
                  omega)]
            exact (natOfZModBits18_bit
              (fun b' ↦ stPre δ (r ⟨b'.val, potGen_d2_lt 123 b'⟩)) b).symm
          rw [(hRemNonTop (r ⟨122, by decide⟩) (hnTopIdx ⟨122, by decide⟩ (by decide))).trans
                (hCh ⟨7, by decide⟩),
              hBitPre ⟨16, by decide⟩, hBitPre ⟨17, by decide⟩, hTop175,
              hRemTop ⟨20, by decide⟩, hPF.2.2.1, zmod2_scrub_z8]
          exact ((@hDomLt143 stPre δ ⟨122, by decide⟩ (by decide)).trans
            (hK0Pre δ ⟨68, by decide⟩ hz)).symm
        · rw [Function.update_of_ne hw122]
          exact hNon122_123 stPre (stOPre δ) (stRemPre δ) δ
            hRemTop hRemNonTop hCh hPr hw122 hw123
  -- Step 3: Inner step
  have hSInner :
      SubspaceStep (mkKetOpW rWork stDomPre phPre) (mkKetOpW rWork stDomPost phPost) inner :=
    hInner stDomPre stDomPost (hDomOut stPre) (hDomOut stPost)
      (fun _ _ _ ↦ writeReg_apply_reg _ _ _ _)
      (fun δ _ hz ↦ by
        dsimp only [stDomPost, stDomPre, stDomPers12]
        rw [writeReg_apply_reg, writeReg_apply_reg, hNNEq δ hz, hd2PostEq δ hz])
      (fun δ p hz ↦ by
        dsimp only [stDomPost, stDomPre, stDomPers12]
        have hnTop : ¬∃ j : Fin 22, rTop j = rP12 p :=
          fun ⟨j, hj⟩ ↦ disj_ne hP12DisjTop p j hj.symm
        rw [writeReg_apply_of_not_mem _ rTop _ _ hnTop,
            writeReg_apply_of_not_mem _ rTop _ _ hnTop,
            writeReg_apply_reg, writeReg_apply_reg, hNNEq δ hz, hd2PostEq δ hz])
  -- Step 4: Restore Z4, Z8 on r[123], r[122]
  let stWBPost : BitAssignment n → BitAssignment n := fun δ ↦ writeReg (stOPost δ) rTop (fun j ↦
    if dom22Bit (evenOctIdxT10K (stPost δ wNN == 1)
      (natOfZModBits 18 (fun b ↦ stPost δ (r ⟨b.val, potGen_d2_lt 123 b⟩)))) j then 1 else 0)
  have hSRest : SubspaceStep (Var := Var)
      (mkKetOpW rWork stDomPost phPost) (mkKetOpW rWork stWBPost phPost)
      (DynamicCircuit.circuit (Var := Var) (cRestoreZ4Z8 r)) :=
    sCircKet (cRestoreZ4Z8_mulVec_ket r) fun δ hz w ↦ by
      obtain ⟨hChP, hPrP, _⟩ := hPropsPost δ hz
      have hPF := pers12_ct_facts (isNNFn δ) (hd2Lt196 δ hz)
      have hDomTop (j : Fin 22) : stDomPost δ (rTop j) =
          if dom22Bit (evenOctIdxT10K (isNNFn δ) (d2Fn δ)) j then 1 else 0 := by
        dsimp only [stDomPost, stDomPers12]
        rw [writeReg_apply_reg, hNNEq δ hz, hd2PostEq δ hz]
      have hDomBit (b : Fin 18) :
          stDomPost δ (r ⟨b.val, potGen_d2_lt 123 b⟩) = if (d2Fn δ).testBit b.val then 1 else 0 :=
        (hDomLt143 stPost δ (Nat.lt_trans b.isLt (by decide))).trans
          ((hd2Eq δ b hz).trans (natOfZModBits18_bit
            (fun b' ↦ stPre δ (r ⟨b'.val, potGen_d2_lt 123 b'⟩)) b).symm)
      by_cases hw122 : w = r ⟨122, by decide⟩
      · subst hw122
        simp only [Function.update_self]
        dsimp only [stWBPost]
        rw [show stDomPost δ (r ⟨122, by decide⟩) = 0 from
              (@hDomLt143 stPost δ ⟨122, by decide⟩ (by decide)).trans
                (hK0Post δ ⟨68, by decide⟩ hz),
            hTop175, hDomTop ⟨20, by decide⟩, hDomBit ⟨17, by decide⟩,
            hDomBit ⟨16, by decide⟩, zmod2_restore_z8, ← hPF.2.2.1,
            writeReg_apply_of_not_mem _ rTop _ _ (fun ⟨j, hj⟩ ↦ hnTopIdx _ (by decide) j hj.symm)]
        have hCh7 := (hChP ⟨7, by decide⟩).symm
        rwa [hNNEq δ hz, hd2PostEq δ hz] at hCh7
      · rw [Function.update_of_ne hw122]
        by_cases hw123 : w = r ⟨123, by decide⟩
        · subst hw123
          simp only [Function.update_self]
          dsimp only [stWBPost]
          have hDom150 : stDomPost δ (r ⟨146, by decide⟩) =
              if pers12Bit (isNNFn δ) (d2Fn δ) ⟨3, by decide⟩ then 1 else 0 := by
            change stDomPost δ (rP12 ⟨3, by decide⟩) = _
            dsimp only [stDomPost, stDomPers12]
            rw [writeReg_apply_of_not_mem _ rTop _ _
                  (fun ⟨j, hj⟩ ↦ disj_ne hP12DisjTop _ j hj.symm),
                writeReg_apply_reg, hNNEq δ hz, hd2PostEq δ hz]
          rw [show stDomPost δ (r ⟨123, by decide⟩) = 0 from
                (@hDomLt143 stPost δ ⟨123, by decide⟩ (by decide)).trans
                  (hK0Post δ ⟨69, by decide⟩ hz),
              hTop174, hTop175, hDomTop ⟨19, by decide⟩, hDomTop ⟨20, by decide⟩,
              hDom150, zmod2_restore_z4, ← hPF.2.2.2.1,
              writeReg_apply_of_not_mem _ rTop _ _
                (fun ⟨j, hj⟩ ↦ hnTopIdx _ (by decide) j hj.symm)]
          have hCh11 := (hChP ⟨11, by decide⟩).symm
          rwa [hNNEq δ hz, hd2PostEq δ hz] at hCh11
        · rw [Function.update_of_ne hw123]
          exact (hNon122_123 stPost (stOPost δ) (stWBPost δ) δ
            (fun _ ↦ writeReg_apply_reg _ _ _ _)
            (fun x hnx ↦ writeReg_apply_of_not_mem _ rTop _ x (fun ⟨j, hj⟩ ↦ hnx j hj.symm))
            hChP hPrP hw122 hw123).symm
  -- Step 5: Reverse pEvenOctBandPers12Unld0
  have hd2OPostEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      natOfZModBits 18 (fun b ↦ stOPost δ (rUnld42Pers hw ⟨1 + b.val, by omega⟩)) =
        natOfZModBits 18 (fun b ↦ stPost δ (r ⟨b.val, potGen_d2_lt 123 b⟩)) := fun δ hz ↦
    congrArg (natOfZModBits 18) (funext fun b ↦ by
      change stOPost δ (fUnld42Pers wNN r ⟨1 + b.val, by omega⟩) = _
      dsimp only [fUnld42Pers]; rw [_root_.dite_eq_right (by omega), _root_.dite_eq_left (by omega)]
      have hEq : r ⟨1 + b.val - 1, by omega⟩ = r ⟨b.val, potGen_d2_lt 123 b⟩ :=
        congrArg r.wires (Fin.ext (by dsimp; omega))
      rw [hEq]
      exact (hPropsPost δ hz).2.1 _ (fun s e ↦ by
        have hv := rInj e; have hb := chain14RIdx_bounds s; dsimp at hv; omega))
  have hNNOPostEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      stOPost δ (rUnld42Pers hw ⟨0, by omega⟩) = stPost δ wNN := fun δ hz ↦
    (hPropsPost δ hz).2.1 wNN (fun s e ↦ hw _ e)
  obtain ⟨hSUnld, _, _, _⟩ := subspaceStep_pEvenOctBandPers12Unld0 v rWork
    (rUnld42Pers hw) rTop hDisj.2 stOPost stWBPost phPost
    (fun δ hz ↦ by rw [hd2OPostEq δ hz, hd2PostEq δ hz]; exact hd2Lt196 δ hz)
    (fun δ hz ↦ by
      have hU (u : Fin 42) (hu0 : u.val ≠ 0) (hu21 : u.val < 21) (b : Fin 36)
          (hb : u.val - 1 = 18 + b.val) : stOPost δ (rUnld42Pers hw u) = 0 := by
        change stOPost δ (fUnld42Pers wNN r u) = 0
        dsimp only [fUnld42Pers]; rw [_root_.dite_eq_right hu0, _root_.dite_eq_left hu21]
        refine ((hPropsPost δ hz).2.1 _ (fun s e ↦ by
          have hv := rInj e; have hc := chain14RIdx_bounds s; dsimp at hv; omega)).trans ?_
        exact (congrArg (stPost δ) (congrArg r.wires (Fin.ext hb))).trans (hY0Post δ b hz)
      exact ⟨hU ⟨19, by decide⟩ (by decide) (by decide) ⟨0, by decide⟩ rfl,
             hU ⟨20, by decide⟩ (by decide) (by decide) ⟨1, by decide⟩ rfl⟩)
    (fun s δ hz ↦ by
      rw [hNNOPostEq δ hz, hd2OPostEq δ hz]
      change stOPost δ (fUnld42Pers wNN r ⟨21 + s.val, by omega⟩) = _
      dsimp only [fUnld42Pers];
      rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega),
          _root_.dite_eq_left (by omega)]
      have hFin : (⟨21 + s.val - 21, by omega⟩ : Fin 14) = s := Fin.ext (by dsimp; omega)
      rw [hFin]; exact (hPropsPost δ hz).1 s)
    (fun u δ hu hz ↦ by
      change stOPost δ (fUnld42Pers wNN r u) = 0; dsimp only [fUnld42Pers]
      rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega),
          _root_.dite_eq_right (by omega)]
      refine ((hPropsPost δ hz).2.1 _ (fun s e ↦ by
        have hv := rInj e; have hb := chain14RIdx_bounds s; dsimp at hv; omega)).trans ?_
      exact apply_y36_zero (fun b ↦ hY0Post δ b hz) _ (by dsimp; omega) (by dsimp; omega))
    (fun j δ hz ↦ by
      refine ((hPropsPost δ hz).2.1 _ (fun s e ↦ by
        have hv :=
            rInj e; have hb := chain14RIdx_bounds s; dsimp [rTop, rTop22Hi] at hv; omega)).trans ?_
      exact apply_k123_zero (fun v ↦ hK0Post δ v hz) _ (by dsimp [rTop, rTop22Hi]; omega))
    (fun δ hz ↦ by
      dsimp only [stWBPost]
      rw [hNNOPostEq δ hz, hd2OPostEq δ hz])
  -- Step 6: Outer wrapDynOnReg (outerDomPre76Tree, 14 ANDs = 56 T)
  have hBodyStep : SubspaceStep (mkKetOpW rWork stOPre phPre) (mkKetOpW rWork stOPost phPost) _ :=
      subspaceStep_seq_u hSRem (subspaceStep_seq_u hSScrub (subspaceStep_seq_u hSInner
      (subspaceStep_seq_u hSRest hSUnld)))
  have hOuterSMask (st : BitAssignment n → BitAssignment n)
      (hK0 : ∀ (δ : BitAssignment n) (v : Fin 123),
        (∀ k : Fin W, δ (rWork k) = 0) → st δ (r ⟨54 + v.val, potGen_k_lt 123 v⟩) = 0)
      (u : Fin 36) (hu : u ∈ maskFinset 36 outerDomPreSMask)
      (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      st δ (rOuter36 hw u) = 0 := by
    have hge := outerDomPreSMask_bounds u.val u.isLt (mem_maskFinset.mp hu)
    change st δ (fOuter36 wNN r u) = 0; dsimp only [fOuter36]
    rw [_root_.dite_eq_right (by omega), _root_.dite_eq_right (by omega)]
    have hb := chain14RIdx_bounds ⟨u.val - 22, by omega⟩
    exact apply_k123_zero (fun v ↦ hK0 δ v hz) _ (by omega)
  exact (subspaceStep_wrapOnReg_vprog2 v rWork (rOuter36 hw)
    (maskFinset 36 outerDomPreSMask) cpO 14
    (maskFinset_zero 36 ▸
      StructuredCB.validProg_of_validProgMask (hvO.trans outerDomPre76Tree_check.1))
    (haO.trans outerDomPre76Tree_check.2)
    stPre stPost phPre phPost _
    (hOuterSMask stPre hK0Pre) (hOuterSMask stPost hK0Post) hBodyStep).1

/-!
### 7. `CoulOWScrPkg12` Package (`kRest = 123`, `M = 72` , `168 + 72 + tInner` T/step) &
`widenCoulOWScrPkg12` (`kRest ≥ 123`)
-/

def fOut22k123 {n : ℕ} (r : QRegister (54 + 123) n) (j : Fin 22) : Wire n :=
  if h : j.val < 21 then r ⟨155 + j.val, by omega⟩ else r ⟨17, by decide⟩

def rOut22k123 {n : ℕ} (r : QRegister (54 + 123) n) : QRegister 22 n :=
  ⟨⟨fOut22k123 r, fun a b e ↦ by
    have rInj : ∀ {x y : Fin (54 + 123)}, r x = r y → x.val = y.val :=
      fun h ↦ congrArg Fin.val (r.wires.injective h)
    dsimp only [fOut22k123] at e
    split_ifs at e with ha hb hb
    · exact Fin.ext (by have hv := rInj e; dsimp at hv; omega)
    · exfalso; have hv := rInj e; dsimp at hv; omega
    · exfalso; have hv := rInj e; dsimp at hv; omega
    · exact Fin.ext (by omega)⟩⟩

def fPers18k123 {n : ℕ} (r : QRegister (54 + 123) n) (q : Fin 18) : Wire n :=
  if h : q.val < 17 then r ⟨126 + q.val, by omega⟩ else r ⟨176, by decide⟩

def rPers18k123 {n : ℕ} (r : QRegister (54 + 123) n) : QRegister 18 n :=
  ⟨⟨fPers18k123 r, fun a b e ↦ by
    have rInj : ∀ {x y : Fin (54 + 123)}, r x = r y → x.val = y.val :=
      fun h ↦ congrArg Fin.val (r.wires.injective h)
    dsimp only [fPers18k123] at e
    split_ifs at e with ha hb hb
    · exact Fin.ext (by have hv := rInj e; dsimp at hv; omega)
    · exfalso; have hv := rInj e; dsimp at hv; omega
    · exfalso; have hv := rInj e; dsimp at hv; omega
    · exact Fin.ext (by omega)⟩⟩

def rPool72k123 {n : ℕ} (r : QRegister (54 + 123) n) : QRegister 72 n :=
  rPoolOf (by decide : 72 ≤ 123) r

end QuantumComputation.Specs.PhotochemistrySolution.Pers12Dom168M72

end

end
