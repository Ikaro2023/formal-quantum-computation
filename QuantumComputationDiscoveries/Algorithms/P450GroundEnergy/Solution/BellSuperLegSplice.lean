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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellAsymCore

/-!
# Asymmetric & `D_neg` Bell-Persistent Super-Reflection Leg Splice (`0 < wInner2`, `kPark = 0`)

Provides 6-unitary asymmetric (`BellAsymLegs`) and zero-`hPull` `D_neg` (`BellAsymLegs.ofDNeg`)
`CleanWalkRefl2At` splices for arbitrary-`K` (`1 ≤ K`, `bellSuperNoNeg*`, `2 ≤ K`-gated inter-step
support) and single-step (`bellRefl2NoNeg*`) reflections, plus `WalkKStepRefl2InvErrLe` (`1 ≤ K`).

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A* **87**,
  022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellSuperLegSplice
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn AliasPrep
open QuantumComputation.Specs QuantumComputation.Specs.P450 TwoGearBox
open CircuitModular BlockEncodingCore
open BlockEncodingCircuit SelectSwapQROM
open TopIntegrationBridge Lac2Fused184Select Phase2MidSandwich MidReflCtxRetain
open PolymorphicFused184Select ReordOuter13Bridge
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
  hiding blockRemWidth
  outRemWidth midRemWidth combARem
open CompactOuter9Bound50Core CompactTuned162StepWalk
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
  (ubCustomMuxCatUnitary outerSandwich_eq_reflPulledPair_customMux)
open CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open OneHotSimulates LowBitPi145Select BellPhaseASelect BellSingletCSwap58
open Cat11CompactPhase2Bridge DihedralWalkQPE DihedralWalkQPE.MultiGearQPE
open DihedralWalkQPE.BlockReflection TwoGearQPEPhase5
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open BellRouter57 CompactCore145Bundle BellPersistNoNeg
open BellSelectNoNegPair Select57Slices BellPersistCore
open BellPersistSuperWalk BellSuperNoNegWalk TwoGearSuperPhase5
open ThreeGearBellSuper BellAsymCore

export QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellAsymCore (
  scrMidZeroSet scrOutZeroSet bellForbidSet embed_pull_of_cat pull_fwd_dneg
  pull_bwd_dneg pull_sym disjoint_bell_of_support_subset imageCombOutRegB_subset_rAllInCat
  disjoint_bell_onRegister_out_slice restrictZeroSet_wp_threeStepPrefix_congr
  cleanRealizesSet_fiveStepCSwap_asym cleanRealizesSet_bellFiveStepNoNegCoreSliceDyn_asym
  BellAsymLegs WalkKStepRefl2InvErrLe walkKStepRefl2InvErrLe_of_walkRefl2InvErrLe
  walkKStepRefl2InvErrLe_zero_of_exact
)
namespace BellAsymLegs
export QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellAsymCore.BellAsymLegs
  (mk ofDNeg ofSym)
end BellAsymLegs

local instance instNeZeroTwoPowLegSplice (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Arbitrary-`K` (`1 ≤ K`) Asymmetric / `D_neg` Super-Reflection Splices -/

theorem cleanWalkRefl2At_bellSuperNoNegGenBundleDyn_asym {Var : Type} [Fintype Var]
    [DecidableEq Var]
    {kInner tCoreF tCoreB : ℕ} (hk7 : 7 ≤ kInner)
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23))
    (specA : (Fin 16 → Bool) → State24) (specBF specBB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 hk23Le24 stepsA (initState23 x16) = some (specA x16))
    (hRunBF : ∀ x16, runSteps24 hk23Le24 stepsBF (specA x16) = some (specBF (specA x16)))
    (hBorBF : ∀ x16 (k : Fin 6), (specBF (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145F : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specBF (specA x16))) < 145)
    (hRunBB : ∀ x16, runSteps24 hk23Le24 stepsBB (specA x16) = some (specBB (specA x16)))
    (hBorBB : ∀ x16 (k : Fin 6), (specBB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145B : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specBB (specA x16))) < 145)
    {bQPE wOuter wInner2 ko km mLow sUb : ℕ} (K : ℕ) (hK : 1 ≤ K) {hkOut : ko ≤ wOuter}
    {hkMid : km ≤ wInner2}
    (hGiPos : 0 < wInner2) (hs : 1 + kInner ≤ sUb)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ kInner)
    {v : Var} {prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
    {M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2)}
    {raw_4 raw_3 sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (legs : BellAsymLegs Var bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v prepOutImpl M_fwd
      M_bwd
      raw_4 raw_3 sF sB pOutFwd pOutBwd P_1 pTurn P_4)
    (hs1 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_4)
      (selectLowBitNoNegCoreSliceDyn bundleF stepsA stepsBF hs v wOuter wInner2 hGiPos
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hs2 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_3)
      (selectLowBitNoNegCoreSliceDyn bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hTurnSupp : Disjoint pTurn.support (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb kInner
      hs))
    (hInterSupp : 2 ≤ K → Disjoint (P_1.support ∪ P_4.support ∪ pOutFwd.support ∪ pOutBwd.support)
      (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb kInner hs)) :
    let uRefl2 := QubitisedWalk.reflPulledPair (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
      (ubCustomMuxCatUnitary M_fwd prepOutImpl sF)
      (ubCustomMuxCatUnitary M_bwd prepOutImpl sB⁻¹)⁻¹
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    CleanWalkRefl2At bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v
      (uRefl2 * (R₀ * uRefl2) ^ (K - 1))
      (bellSuperNoNegGenBundleDyn bundleF bundleB stepsA stepsBF stepsBB bQPE wOuter wInner2 ko km
        mLow sUb K
        hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4) := by
  intro uRefl2 R₀
  have _ := hK
  rcases legs with ⟨M_1_pre, M_1_post, M_2_pre, M_2_post, hFwd, hBwd, hConj, h1, hTurn, h4,
    hPull1, hPull2, hPres1, hPres2, hPresAll⟩
  let wNegIn : Wire wInner2 := ⟨0, hGiPos⟩
  let N := combQubitsAt bQPE wOuter wInner2 ko km mLow sUb
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rUB := combUBRegB bQPE wOuter wInner2 ko km mLow sUb
  let rOut := combOutRegB bQPE wOuter wInner2 ko km mLow sUb
  let rMid := combMidRegB bQPE wOuter wInner2 ko km mLow sUb
  let rMidZero := rMid.compose (midZeroPrefixReg wInner2 km hkMid)
  let rOutZero := rOut.compose (outZeroPrefixReg wOuter ko hkOut)
  let rAncZ := liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2)
    (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
  let rUbZero : QRegister (sUb + (ko + km)) N :=
    rUbZeroLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sUb rAncZ
  have hdisj := combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb
  have hUBScr : rUB.DisjointWires rScrUb := hdisj.compose_left _
  have hScrMid : rScrUb.DisjointWires rMidZero := ((hUBScr.compose_left _).compose_left _).symm
  let rClean := rScrUb.concat rMidZero hScrMid
  let S_ext := rScrUb.image ∪ rMidZero.image
  let S_full := S_ext ∪ rOutZero.image
  have hCleanImg : rClean.image = S_ext := QRegister.image_concat rScrUb rMidZero hScrMid
  have hUbImg : rUbZero.image = S_full := by
    dsimp only [rUbZero, rAncZ, S_full, S_ext, rScrUb, rOutZero, rMidZero, rOut, rMid, rUB,
      combOutRegB, combMidRegB, combUBRegB, combScrUbRegAt, combWalkCatRegAt]
    rw [image_rUbZeroLoc, ← union_outMidZero_eq_rAncZeroLoc]
    ext w
    simp only [Finset.mem_union]
    tauto
  have hFwdSet := (SelectSwapQROM.cleanRealizes_iff_set v _ _ _ _).mp
    ((AliasPrep.cleanRealizes_sbx_iff _ _ _ _ _).mpr hFwd)
  let selF :=
      selectLowBitNoNegCoreSliceDyn bundleF stepsA stepsBF hs v wOuter wInner2 hGiPos rMain rScrUb
  let selB :=
      selectLowBitNoNegCoreSliceDyn bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos rMain rScrUb
  let P_single : DynamicCircuit Var N := outerSeqWrapDyn pOutFwd
    (.seq P_1 (.seq (bellSelectNoNegCoreSlicePairDyn bundleF bundleB stepsA stepsBF stepsBB hs v
      wOuter
      wInner2 hGiPos rMain rScrUb pTurn) P_4)) pOutBwd
  let P_single_cswap : DynamicCircuit Var N := outerSeqWrapDyn pOutFwd
    (.seq P_1 (.seq (.seq selF (.seq pTurn selB)) P_4)) pOutBwd
  let pReflIn := reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega) v
  let R_mid := QubitisedWalk.reflMidUnitary (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
  let u_in1 := (rUBInCat wOuter wInner2 11).embedUnitary M_fwd⁻¹ * sF *
    (rUBInCat wOuter wInner2 11).embedUnitary M_fwd
  let u_in2 := (rUBInCat wOuter wInner2 11).embedUnitary M_bwd⁻¹ * sB *
    (rUBInCat wOuter wInner2 11).embedUnitary M_bwd
  have hW2_sel : (rUB.embedUnitary M_2_pre).1 * zeroProjOn rScrUb.image =
      zeroProjOn rScrUb.image * (rUB.embedUnitary M_2_pre).1 :=
    preservesWires_comm_zeroProjOn (preservesWires_embedMatrix_of_disjoint rUB M_2_pre.1
      rScrUb.image (disjoint_image_of_disjointWires hUBScr)) Finset.Subset.rfl
  have hPresR : PreservesWires (rMain.embedUnitary R_mid).1 rClean.image :=
    preservesWires_congr_set hCleanImg.symm (preservesWires_embed_reflMid_zc20 rMain _ _)
  have hSubClean : rScrUb.image ⊆ rClean.image := by
    rw [hCleanImg]
    exact Finset.subset_union_left
  have hInnerBell := cleanRealizesSet_congr_set hCleanImg
    (cleanRealizesSet_bellFiveStepNoNegCoreSliceDyn_asym hk7 bundleF bundleB stepsA stepsBF stepsBB
      specA specBF specBB hRunA hRunBF hBorBF h145F hRunBB hBorBB h145B hs v wOuter wInner2 hGiPos
      rMain rScrUb rClean hdisj hSubClean (rUB.embedUnitary M_1_pre) (rUB.embedUnitary M_1_post)
      (rUB.embedUnitary M_2_pre) (rUB.embedUnitary M_2_post) (rMain.embedUnitary raw_4)
      (rMain.embedUnitary raw_3) u_in1 u_in2 R_mid h1 hs1
      (cleanTurnaroundWp_congr hCleanImg rfl rfl hTurn) hs2
      (cleanUnloadsWp_congr hCleanImg rfl h4) hW2_sel hPull1 hPull2
      (preservesWires_congr_set hCleanImg.symm hPres1) hPresR
      (preservesWires_congr_set hCleanImg.symm hPres2) hTurnSupp)
  have hInnerCSwap := cleanRealizesSet_congr_set hCleanImg
    (cleanRealizesSet_fiveStepCSwap_asym rMain rScrUb rClean hSubClean (rUB.embedUnitary M_1_pre)
      (rUB.embedUnitary M_1_post) (rUB.embedUnitary M_2_pre) (rUB.embedUnitary M_2_post)
      (rMain.embedUnitary raw_4) (rMain.embedUnitary raw_3) u_in1 u_in2 R_mid h1 hs1
      (cleanTurnaroundWp_congr hCleanImg rfl rfl hTurn) hs2
      (cleanUnloadsWp_congr hCleanImg rfl h4) hW2_sel hPull1 hPull2
      (preservesWires_congr_set hCleanImg.symm hPres1) hPresR
      (preservesWires_congr_set hCleanImg.symm hPres2))
  have hSingleSet : CleanRealizesSet v S_full (rMain.embedUnitary uRefl2) P_single := by
    have hS := outerSandwich_cleanRealizesSet hkOut hkMid hFwd hBwd hConj _ _ hInnerBell hPresAll
    rwa [outerSandwich_eq_reflPulledPair_customMux rMain] at hS
  have hSingleCSwap : CleanRealizesSet v S_full (rMain.embedUnitary uRefl2) P_single_cswap := by
    have hS := outerSandwich_cleanRealizesSet hkOut hkMid hFwd hBwd hConj _ _ hInnerCSwap hPresAll
    rwa [outerSandwich_eq_reflPulledPair_customMux rMain] at hS
  have hR0Set : CleanRealizesSet v S_full (rMain.embedUnitary R₀) pReflIn :=
    cleanRealizesSetReflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega) v
  have H_step := hSingleCSwap.seq hR0Set
  have hDisjOut := combOutRegB_disjoint_scr_midZero bQPE wOuter wInner2 ko km mLow sUb hkMid
  have hPresRefl2 : AliasPrep.PreservesWires (rMain.embedUnitary uRefl2).1 S_full := by
    have hp : AliasPrep.PreservesWires
        (((rOut.embedUnitary prepOutImpl)⁻¹ *
          rMain.embedUnitary (innerMidCoreUnitary M_fwd M_bwd sF sB) *
          rOut.embedUnitary prepOutImpl).1) S_full :=
      hConj rOut S_ext hDisjOut hPresAll
    rw [congrArg Subtype.val
      (outerSandwich_eq_reflPulledPair_customMux rMain M_fwd M_bwd prepOutImpl sF sB)] at hp
    exact hp
  have hPresSuper (m : ℕ) :
      AliasPrep.PreservesWires (rMain.embedUnitary (uRefl2 * (R₀ * uRefl2) ^ m)).1 S_full := by
    induction m with
    | zero => simpa using hPresRefl2
    | succ k ih =>
      rw [show uRefl2 * (R₀ * uRefl2) ^ (k + 1) = (uRefl2 * (R₀ * uRefl2) ^ k) * R₀ * uRefl2 by
        simp only [_root_.pow_succ, mul_assoc], rMain.embedUnitary_mul, rMain.embedUnitary_mul]
      exact preservesWires_mul (preservesWires_mul ih (preservesWires_embed_reflIn rMain _ _))
        hPresRefl2
  let rScr : QRegister (1 + kInner) N := rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
  have hLiftScr {A B : QCAssertion Var (2 ^ N)}
      (h : SelectSwapQROM.restrictZeroSet A rScr.image =
        SelectSwapQROM.restrictZeroSet B rScr.image) :
      SelectSwapQROM.restrictZeroSet A rScrUb.image =
        SelectSwapQROM.restrictZeroSet B rScrUb.image :=
    restrictZeroSet_eq_of_subset (rScrUb.image_compose_subset _) h
  have hSubScrFull : rScrUb.image ⊆ S_full :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wNegIn)
  let rSys116 := (rMain.compose (rSysCatUB wOuter wInner2 11)).compose
    (QRegister.block 0 (2 * 58) (by decide))
  let rRt := lowBitRouter23 bundleF.hk6 wOuter wInner2 wNegIn rMain rScr hdisjScr
  let L := lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisjScr
  let rSwap117 := rSwap117LowBit wOuter wInner2 wNegIn rMain
  let cSw := (cswapBlockCircuit 58).onRegister rSwap117
  let dSwap := cswapBlockDyn () 58 rSwap117 (L.rInner ⟨0, by omega⟩)
  let sA := liftRouterStepsN rRt stepsA
  let sB1 := liftRouterStepsN rRt stepsBF
  let sB2 := liftRouterStepsN rRt stepsBB
  let uEnt1 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB1)
  let uEnt2 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB2)
  let pPost1 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB1) (routerStepsBwdUnitDyn sA))
  let pPost2 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB2) (routerStepsBwdUnitDyn sA))
  let wDst := rScr ⟨kInner, by omega⟩
  let wTmp := rScr ⟨kInner - 1, by omega⟩
  let pHead := DynamicCircuit.seq pOutFwd (.seq P_1 (liftUnitVar v (.seq uEnt1 dSwap)))
  let pMidCore := DynamicCircuit.seq (liftUnitVar v (bundleF.coreUnitDyn L))
    (.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
      (.seq pPost1 (.seq pTurn (.seq (liftUnitVar v uEnt2)
        (.seq (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst)
          (liftUnitVar v (bundleB.coreUnitDyn L)))))))
  let pInter := DynamicCircuit.seq pPost2
    (.seq P_4 (.seq pOutBwd (.seq pReflIn (.seq pOutFwd (.seq P_1 (liftUnitVar v uEnt1))))))
  let pTransBell := DynamicCircuit.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
    (.seq pInter (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst))
  let pTail := DynamicCircuit.seq pMidCore
    (.seq (liftUnitVar v dSwap) (.seq pPost2 (.seq P_4 pOutBwd)))
  obtain ⟨_, _, hInnerEq, hCtrl10Eq⟩ :=
    lowBitCoreLayout_wires bundleF.hk6 wOuter wInner2 wNegIn rMain rScr hdisjScr
  have hSysRt23 := lowBit_disj_sysCat_router23 bundleF.hk6 wOuter wInner2 wNegIn rMain rScr hdisjScr
  have hPool := disjoint_rSwap117_rInner bundleF.hk6 wOuter wInner2 wNegIn rMain rScr hdisjScr
  have hSys2 : (QRegister.singleton (rCtrl16 14)).DisjointWires rSys116 :=
    QRegister.disjoint_iff.mpr fun i _ heq ↦ by
      fin_cases i
      exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _ (rMain.wires.injective heq)
  have hrSwapEq : (QRegister.singleton (rCtrl16 14)).concat rSys116 hSys2 = rSwap117 := rfl
  let USwapLoc : Unitary (2 ^ (1 + 2 * 58)) := muxUnitary (QRegister.singleton 0)
    (QRegister.block 1 (2 * 58) (by omega)) (disj_singleton0_block1 (2 * 58))
    (fun σ ↦ if σ = 0 then 1 else permutationUnitary (spinSwapEquiv 58))
  have hcSwEval : cSw.eval = rSwap117.embedUnitary USwapLoc := by
    apply Subtype.ext
    rw [Circuit.eval_onRegister, cswapBlockCircuit_eval]
  have hSwClean := diagProjSimulates_of_cleanRealizes_unit_bound50 rSwap117 L.rInner hPool _ _
    (cleanRealizes_cswapBlockDyn () 58 rSwap117 L.rInner hPool ⟨0, by omega⟩)
  have hSimSw0 : SimulatesOnProj (zeroProjOn L.rInner.image) cSw.eval dSwap := by
    rw [← basisOutcomeProjector_zero_eq_zeroProjOn, hcSwEval]
    exact SimulatesOnProj.ofDiagProj hSwClean
  have hEq_3 : rCtrl16 14 = rRt 15 := by
    rw [lowBitRouter23_apply, dite_eq_right (by decide), dite_eq_left (by decide)]
    rfl
  have hSwapValid : DiagProjSimulates (ketPredProj (sValidCore L))
      (rSwap117.embedUnitary USwapLoc) dSwap := by
    refine hSwClean.tighten ⟨sValidCore L, rfl⟩
      (by rw [basisOutcomeProjector_zero_eq_ketPredProj]
          exact ketPredProj_mul_of_imp fun _ h ↦ h.2)
      (embedMatrix_comm_ketPredProj_bound50 rSwap117 USwapLoc.1 (sValidCore L) fun β l ↦ ?_)
    have hNot (u : Fin 10) : L.rCtrl10 u ∉ Set.range rSwap117.wires := by
      rintro ⟨k, hk⟩
      revert hk
      refine Fin.addCases (fun a hk ↦ ?_) (fun b hk ↦ ?_) k
      · fin_cases a
        have h15 := (QRegister.concat_apply_left _ rSys116 hSys2 0).trans hEq_3
        have hne : (15 : Wire 23) ≠ routed10Wire23 u := by fin_cases u <;> decide
        exact hne (rRt.wires.injective (h15.symm.trans (hk.trans (hCtrl10Eq u))))
      · exact hSysRt23.ne (QRegister.block 0 (2 * 58) (by decide) b) (routed10Wire23 u)
          ((QRegister.concat_apply_right _ rSys116 hSys2 b).symm.trans (hk.trans (hCtrl10Eq u)))
    have hPairLoc := localIdx_congr_bound50 (β₁ := writeRegBitsBound50 β rSwap117 (basisBits _ l))
      (β₂ := β) L.rSelPair8 fun i ↦ writeRegBitsBound50_apply_of_not_mem _ _ _ _
      (hNot (Lac2Fused184Select.selPair10 i))
    have hIn (idx : Fin kInner) := writeRegBitsBound50_apply_of_not_mem β rSwap117 (basisBits _ l)
      (L.rInner idx) (fun ⟨k, hk⟩ ↦ hPool.ne k idx hk)
    dsimp only [sValidCore]
    simp only [hPairLoc, hIn]
  have hPValIn : zeroProjOn L.rInner.image * ketPredProj (sValidCore L) =
      ketPredProj (sValidCore L) := by
    rw [← basisOutcomeProjector_zero_eq_zeroProjOn, basisOutcomeProjector_zero_eq_ketPredProj]
    exact (IsDiagProj.comm ⟨_, rfl⟩ ⟨sValidCore L, rfl⟩).trans
      (ketPredProj_mul_of_imp fun _ h ↦ h.2)
  obtain ⟨U_e1, hSimEnt1, hMapEnt1⟩ := simulatesOnProj_noNegCoreSliceEntry bundleF.hk6 stepsA
    stepsBF specA specBF hRunA hRunBF hBorBF h145F wOuter wInner2 wNegIn rMain rScr hdisjScr
  obtain ⟨U_e2, hSimEnt2, hMapEnt2⟩ := simulatesOnProj_noNegCoreSliceEntry bundleF.hk6 stepsA
    stepsBB specA specBB hRunA hRunBB hBorBB h145B wOuter wInner2 wNegIn rMain rScr hdisjScr
  obtain ⟨_, hSimC1, _⟩ := bundleF.simCore L
  obtain ⟨_, hSimC2, _⟩ := bundleB.simCore L
  have hdBody1 := diagProjSimulates_seq_same_bound50 hSwapValid hSimC1
  have hdBody2 := diagProjSimulates_seq_same_bound50 hSwapValid hSimC2
  have hSimPre1 := hSimEnt1.seq (SimulatesOnProj.ofDiagProj hdBody1) (zeroProjOn_conjTranspose _)
    hdBody1.1.conjTranspose_eq hMapEnt1
  have hSimPre2 := hSimEnt2.seq (SimulatesOnProj.ofDiagProj hdBody2) (zeroProjOn_conjTranspose _)
    hdBody2.1.conjTranspose_eq hMapEnt2
  have hMapPre1 : zeroProjOn L.rInner.image * (_ * U_e1).1 * zeroProjOn rScr.image =
      (_ * U_e1).1 * zeroProjOn rScr.image :=
    proj_map_mul hMapEnt1 (by
      rw [Matrix.mul_assoc, hdBody1.2.1, ← Matrix.mul_assoc, hPValIn, ← hdBody1.2.1])
  have hMapPre2' : zeroProjOn L.rInner.image * (_ * U_e2).1 * zeroProjOn rScr.image =
      (_ * U_e2).1 * zeroProjOn rScr.image :=
    proj_map_mul hMapEnt2 (by
      rw [Matrix.mul_assoc, hdBody2.2.1, ← Matrix.mul_assoc, hPValIn, ← hdBody2.2.1])
  have hMapEnt1' : zeroProjOn L.rInner.image * U_e1.1 * zeroProjOn rScr.image =
      U_e1.1 * zeroProjOn rScr.image := by
    rw [Matrix.mul_assoc, ← hMapEnt1, ← Matrix.mul_assoc, ← Matrix.mul_assoc (zeroProjOn _),
      hPValIn, hMapEnt1]
  have hMapEnt2' : zeroProjOn L.rInner.image * U_e2.1 * zeroProjOn rScr.image =
      U_e2.1 * zeroProjOn rScr.image := by
    rw [Matrix.mul_assoc, ← hMapEnt2, ← Matrix.mul_assoc, ← Matrix.mul_assoc (zeroProjOn _),
      hPValIn, hMapEnt2]
  have hwDstS : wDst ∈ L.rInner.image := (QRegister.mem_image _ _).mpr
    ⟨⟨kInner - 1, by omega⟩, by
      rw [hInnerEq]
      refine congrArg rScr (Fin.ext ?_)
      dsimp
      omega⟩
  have hwTmpS : wTmp ∈ L.rInner.image := (QRegister.mem_image _ _).mpr
    ⟨⟨kInner - 2, by omega⟩, by
      rw [hInnerEq]
      refine congrArg rScr (Fin.ext ?_)
      dsimp
      omega⟩
  have hNotS : rCtrl16 14 ∉ L.rInner.image := fun hm ↦ by
    obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
    rw [hInnerEq] at hj
    exact hdisjScr.ne _ _ hj.symm
  have hSysDisjS : Disjoint rSys116.image L.rInner.image :=
    Finset.disjoint_left.mpr fun _ hw1 hw2 ↦ by
      obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hw1
      obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hw2
      rw [hInnerEq] at hj
      exact hdisjScr.ne _ _ hj.symm
  have hDstTmp : wDst ≠ wTmp := rScr.wires.injective.ne fun h ↦ by
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  have hDst2 : rCtrl16 14 ≠ wDst := hdisjScr.ne _ _
  have hwDstEq : wDst = rScrUb ⟨kInner, by omega⟩ := congrArg rScrUb (Fin.ext (Nat.zero_add _))
  have hRtDisj : Disjoint rRt.image (rSys116.image ∪ {wDst}) :=
    Finset.disjoint_left.mpr fun _ hw hU ↦ by
      obtain ⟨u, rfl⟩ := (QRegister.mem_image rRt _).mp hw
      rcases Finset.mem_union.mp hU with hS | hD
      · obtain ⟨_, hk⟩ := (QRegister.mem_image rSys116 _).mp hS
        exact hSysRt23.ne _ u hk
      · rw [Finset.mem_singleton, lowBitRouter23_apply] at hD
        split_ifs at hD
        · exact absurd (congrArg Fin.val (rScr.wires.injective hD)) (by
            dsimp
            omega)
        · exact hdisjScr.ne _ _ hD
        · exact absurd (congrArg Fin.val (rScr.wires.injective hD)) (by
            dsimp
            omega)
  have hSubRt (st : List (RouterStep 23)) := support_routerStepsFwdBwd_subset
    (liftRouterStepsN rRt st) (touchesIn_liftRouterStepsN rRt _
      (fun u ↦ (QRegister.mem_image rRt _).mpr ⟨u, rfl⟩) st)
  let pMid1 := DynamicCircuit.seq pPost1 (.seq pTurn (liftUnitVar v uEnt2))
  have hMid1Disj : Disjoint pMid1.support (rSys116.image ∪ {wDst}) := by
    have hTurnDst : Disjoint pTurn.support (rSys116.image ∪ {wDst}) := by rwa [hwDstEq]
    simp only [pMid1, pPost1, uEnt2, DynamicCircuit.support_seq, support_liftUnitVar]
    exact Finset.disjoint_union_left.mpr ⟨hRtDisj.mono_left (Finset.union_subset (hSubRt _).2
      (hSubRt _).2), Finset.disjoint_union_left.mpr ⟨hTurnDst, hRtDisj.mono_left
      (Finset.union_subset (hSubRt _).1 (hSubRt _).1)⟩⟩
  have hSys (m : Fin (1 + kInner)) : rSys116.DisjointWires (QRegister.singleton (rScr m)) :=
    QRegister.disjoint_iff.mpr fun _ j ↦ by
      fin_cases j
      exact hdisjScr.ne _ m
  have hExV : PreservesVInv v (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp) :=
    (cleanRealizesSet_dBellExit58Dyn (Var := Var) v (rCtrl16 14) rSys116 wDst wTmp
      (hSys _) (hSys _) hDstTmp (hdisjScr.ne _ _) (hdisjScr.ne _ _)).2.1
  have hEnV : PreservesVInv v (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst) :=
    fun Θ _ ↦ wp_dBellEntry58Dyn_update_self v (rCtrl16 14) rSys116 wDst hDst2 Θ
  have hPost1V : PreservesVInv v pPost1 :=
    ((ConstWp.routerStepsFwdBwd sB1).2.seq (ConstWp.routerStepsFwdBwd sA).2).preservesVInv v
  have hPost2V : PreservesVInv v pPost2 :=
    ((ConstWp.routerStepsFwdBwd sB2).2.seq (ConstWp.routerStepsFwdBwd sA).2).preservesVInv v
  have hEnt1V : PreservesVInv v (liftUnitVar v uEnt1) := hSimEnt1.1.preservesVInv v
  have hEnt2V : PreservesVInv v (liftUnitVar v uEnt2) := hSimEnt2.1.preservesVInv v
  have hSwV : PreservesVInv v (liftUnitVar v dSwap) := hSimSw0.1.preservesVInv v
  have hC1V := (SimulatesOnProj.ofDiagProj hSimC1).1.preservesVInv v
  have hC2V := (SimulatesOnProj.ofDiagProj hSimC2).1.preservesVInv v
  have hMid1V := preservesVInv_seq hPost1V (preservesVInv_seq hTurn.2.1 hEnt2V)
  have hHeadV := preservesVInv_seq hFwdSet.2.1 (preservesVInv_seq h1.2.1
    ((hSimEnt1.1.seq hSimSw0.1).preservesVInv v))
  have hMidCoreV := preservesVInv_seq hC1V (preservesVInv_seq hExV
    (preservesVInv_seq hPost1V (preservesVInv_seq hTurn.2.1
      (preservesVInv_seq hEnt2V (preservesVInv_seq hEnV hC2V)))))
  have hInterV := preservesVInv_seq hPost2V (preservesVInv_seq h4.2.1
    (preservesVInv_seq hBwd.2.1 (preservesVInv_seq hR0Set.2.1
      (preservesVInv_seq hFwdSet.2.1 (preservesVInv_seq h1.2.1 hEnt1V)))))
  have hTransV := preservesVInv_seq hExV (preservesVInv_seq hInterV hEnV)
  have hTailV := preservesVInv_seq hMidCoreV (preservesVInv_seq hSwV
    (preservesVInv_seq hPost2V (preservesVInv_seq h4.2.1 hBwd.2.1)))
  have hcWoutExt : (rOut.embedUnitary prepOutImpl).1 * zeroProjOn S_ext =
      zeroProjOn S_ext * (rOut.embedUnitary prepOutImpl).1 :=
    preservesWires_comm_zeroProjOn
      (preservesWires_embedMatrix_of_disjoint rOut prepOutImpl.1 S_ext hDisjOut) Finset.Subset.rfl
  have hPrefixCongr {X₁ X₂ : QCAssertion Var (2 ^ N)}
      (hX1 : ∀ σ val, X₁ (Function.update σ v val) = X₁ σ)
      (hX2 : ∀ σ val, X₂ (Function.update σ v val) = X₂ σ)
      (hEqScr : SelectSwapQROM.restrictZeroSet X₁ rScrUb.image =
        SelectSwapQROM.restrictZeroSet X₂ rScrUb.image) :
      SelectSwapQROM.restrictZeroSet
        (wp pOutFwd.compile (wp P_1.compile (wp selF.compile (wp pTurn.compile X₁)))) S_full =
      SelectSwapQROM.restrictZeroSet
        (wp pOutFwd.compile (wp P_1.compile (wp selF.compile (wp pTurn.compile X₂)))) S_full := by
    have hInEq := restrictZeroSet_wp_threeStepPrefix_congr
      (Finset.subset_union_left : rScrUb.image ⊆ S_ext) h1 hs1 hTurn hW2_sel hPull1
      hPres1 (preservesWires_congr_set hCleanImg hPresR) hX1 hX2 hEqScr
    have hA1V := h1.2.1 _ (hs1.2.1 _ (hTurn.2.1 X₁ hX1))
    have hA2V := h1.2.1 _ (hs1.2.1 _ (hTurn.2.1 X₂ hX2))
    refine restrictZeroSet_eq_of_subset Finset.subset_union_left ?_
    rw [restrictZeroSet_eq_of_subset Finset.subset_union_left (hFwdSet.2.2.1 _ hA1V),
      restrictZeroSet_qcWpQAssign_comm hcWoutExt, hInEq,
      ← restrictZeroSet_qcWpQAssign_comm hcWoutExt,
      ← restrictZeroSet_eq_of_subset Finset.subset_union_left (hFwdSet.2.2.1 _ hA2V)]
  have hEntSw {uEnt : DynamicCircuit Unit N} {U_e : Unitary (2 ^ N)}
      (hSimE : SimulatesOnProj (zeroProjOn rScr.image) U_e uEnt)
      (hMapE : zeroProjOn L.rInner.image * U_e.1 * zeroProjOn rScr.image =
        U_e.1 * zeroProjOn rScr.image)
      (Ξ : QCAssertion Var (2 ^ N)) (hΞ : ∀ σ val, Ξ (Function.update σ v val) = Ξ σ) :
      SelectSwapQROM.restrictZeroSet
        (wp (liftUnitVar v uEnt).compile (wp (DynamicCircuit.circuit cSw).compile Ξ)) rScr.image =
      SelectSwapQROM.restrictZeroSet
        (wp (liftUnitVar v (.seq uEnt dSwap)).compile Ξ) rScr.image := by
    have hSwΞ : ∀ σ val, wp (DynamicCircuit.circuit cSw).compile Ξ (Function.update σ v val) =
        wp (DynamicCircuit.circuit cSw).compile Ξ σ := fun σ val ↦ by
      simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign,
        hΞ σ val]
    rw [hSimE.restrictZeroSet_eq v hMapE _ hSwΞ, ← hSimSw0.restrictZeroSet_eq_circuit v Ξ hΞ,
      ← hSimE.restrictZeroSet_eq v hMapE _ (hSwV Ξ hΞ), liftUnitVar_seq, wp_seq_compile]
  have hcTarget := preservesWires_comm_zeroProjOn (hPresSuper (K - 1)) Finset.Subset.rfl
  have hCR : XMeasCircuit.CleanRealizes v (QRegister.whole N) rUbZero
      (rMain.embedUnitary (uRefl2 * (R₀ * uRefl2) ^ (K - 1)))
      (bellSuperNoNegGenBundleDyn bundleF bundleB stepsA stepsBF stepsBB bQPE wOuter wInner2 ko km
        mLow sUb K
        hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4) := by
    refine XMeasCircuit.CleanRealizes.mkOfWpClean
      (count_bellSuperNoNegGenBundleDyn_toff bundleF bundleB stepsA stepsBF stepsBB bQPE wOuter
        wInner2 ko km
        mLow sUb K hkOut hkMid hGiPos hs hsIn v hFwdSet.1 hBwd.1 h1.1 hTurn.1 h4.1)
      (fun Θ hΘ ↦ preservesVInv_seq hHeadV (preservesVInv_seq (preservesVInv_iterBinDyn (K - 1)
        (preservesVInv_seq hMidCoreV hTransV)) hTailV) Θ hΘ)
      (fun Θ hΘ ↦ ?_) ?_
    · rw [SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet,
        SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet,
        QRegister.whole_embedUnitary, hUbImg]
      dsimp only [bellSuperNoNegGenBundleDyn]
      simp only [wp_seq_compile, wp_iterBinDyn_compile]
      let Φ : ℕ → QCAssertion Var (2 ^ N) :=
        fun m ↦ (wp (DynamicCircuit.seq pMidCore pTransBell).compile)^[m] (wp pTail.compile Θ)
      have hΦV (m : ℕ) : ∀ σ val, Φ m (Function.update σ v val) = Φ m σ := by
        induction m with
        | zero => exact hTailV Θ hΘ
        | succ k ih =>
          intro σ val
          dsimp only [Φ]
          simp only [Function.iterate_succ_apply']
          exact preservesVInv_seq hMidCoreV hTransV _ ih σ val
      suffices hLoop : ∀ m : ℕ, m ≤ K - 1 →
          SelectSwapQROM.restrictZeroSet (wp pHead.compile (Φ m)) S_full =
            SelectSwapQROM.restrictZeroSet
              (qcWpQAssign (rMain.embedUnitary (uRefl2 * (R₀ * uRefl2) ^ m)) Θ) S_full from
        hLoop (K - 1) le_rfl
      intro m
      induction m with
      | zero =>
        intro _
        have hBase0 : wp pHead.compile (Φ 0) = wp P_single.compile Θ := by
          dsimp only [Φ, Function.iterate_zero, id_eq, P_single, outerSeqWrapDyn]
          unfold bellSelectNoNegCoreSlicePairDyn
          rw [dite_eq_left hdisj]
          dsimp only [pHead, pTail, pMidCore, pPost1, pPost2, uEnt1, uEnt2, sA, sB1, sB2,
            dSwap, rSwap117, L, rRt, wNegIn, rScr, wDst, wTmp, rCtrl16, rSys116]
          conv_lhs => simp only [liftUnitVar_seq, wp_seq_compile]
          conv_rhs => simp only [liftUnitVar_seq, wp_seq_compile]
        rw [hBase0, _root_.pow_zero, mul_one]
        exact hSingleSet.2.2.1 Θ hΘ
      | succ k ih =>
        intro hk
        have hIS : Disjoint (P_1.support ∪ P_4.support ∪ pOutFwd.support ∪ pOutBwd.support)
            (rSys116.image ∪ {wDst}) := by
          rw [hwDstEq]
          exact hInterSupp (by omega)
        simp only [Finset.disjoint_union_left] at hIS
        have hInterDisj : Disjoint pInter.support (rSys116.image ∪ {wDst}) := by
          have hReflDst : Disjoint pReflIn.support (rSys116.image ∪ {wDst}) := by
            rw [hwDstEq]
            exact disjointReflInSliceDyn_bell bQPE wOuter wInner2 ko km mLow sUb kInner hkOut hkMid
              hsIn hs v
          simp only [pInter, pPost2, uEnt1, DynamicCircuit.support_seq, support_liftUnitVar,
            Finset.disjoint_union_left]
          exact ⟨⟨hRtDisj.mono_left (hSubRt _).2, hRtDisj.mono_left (hSubRt _).2⟩, hIS.1.1.2,
            hIS.2, hReflDst, hIS.1.2, hIS.1.1.1, hRtDisj.mono_left (hSubRt _).1,
            hRtDisj.mono_left (hSubRt _).1⟩
        have hSucc : Φ (k + 1) = wp pMidCore.compile (wp pTransBell.compile (Φ k)) := by
          dsimp only [Φ]
          simp only [Function.iterate_succ_apply', wp_seq_compile]
        let Ψ_k := wp pTransBell.compile (Φ k)
        have hΨkV := hTransV (Φ k) (hΦV k)
        let Θ_mid1 := wp (liftUnitVar v (bundleB.coreUnitDyn L)).compile Ψ_k
        have hΘmid1V : ∀ σ val, Θ_mid1 (Function.update σ v val) = Θ_mid1 σ := hC2V Ψ_k hΨkV
        let B_bell := wp (DynamicCircuit.seq (liftUnitVar v uEnt2) (.circuit cSw)).compile Θ_mid1
        have hBbellV : ∀ σ val, B_bell (Function.update σ v val) = B_bell σ := by
          dsimp only [B_bell]
          rw [wp_seq_compile]
          exact hEnt2V _ (fun σ val ↦ by
            simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile,
              qcWpQAssign, hΘmid1V σ val])
        have hStepA : SelectSwapQROM.restrictZeroSet
            (wp (liftUnitVar v (.seq uEnt1 dSwap)).compile (wp pMidCore.compile Ψ_k)) rScrUb.image =
            SelectSwapQROM.restrictZeroSet
              (wp selF.compile (wp pTurn.compile B_bell)) rScrUb.image := by
          apply hLiftScr
          let pBell1 := DynamicCircuit.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
            (.seq pMid1 (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst))
          have hBell1V := preservesVInv_seq hExV (preservesVInv_seq hMid1V hEnV) Θ_mid1 hΘmid1V
          have hSplitA : wp (liftUnitVar v (.seq uEnt1 dSwap)).compile (wp pMidCore.compile Ψ_k) =
              wp (liftUnitVar v (.seq uEnt1 (.seq dSwap (bundleF.coreUnitDyn L)))).compile
                (wp pBell1.compile Θ_mid1) := by
            dsimp only [pMidCore, pBell1, pMid1, Θ_mid1]
            simp only [liftUnitVar_seq, wp_seq_compile]
          have hSim1 := hSimPre1.restrictZeroSet_eq v hMapPre1 _ hBell1V
          have hSand1 := restrictZeroSet_wp_bellSandwich58_eq_cswapCircuit v (rCtrl16 14)
            (rCtrl16 14) rSys116 wDst wTmp L.rInner.image hwDstS hwTmpS hNotS hSysDisjS
            hDstTmp hSys2 hSys2 hDst2 pMid1 hMid1Disj hMid1V Θ_mid1 hΘmid1V
          dsimp only at hSand1
          rw [hrSwapEq] at hSand1
          have hMid1Sw : wp (DynamicCircuit.seq (.circuit cSw) (.seq pMid1 (.circuit cSw))).compile
              Θ_mid1 = wp (DynamicCircuit.circuit cSw).compile
                (wp pPost1.compile (wp pTurn.compile B_bell)) := by
            dsimp only [pMid1, B_bell]
            simp only [wp_seq_compile]
          rw [hMid1Sw] at hSand1
          have hPTBb := hPost1V _ (hTurn.2.1 B_bell hBbellV)
          dsimp only [uEnt1, sA, sB1, dSwap, L, rRt, rScr, hdisjScr] at hSplitA hSim1 hSand1 ⊢
          rw [hSplitA, hSim1, hSand1, ← hSimSw0.restrictZeroSet_eq_circuit v _ hPTBb,
            ← hSimPre1.restrictZeroSet_eq v hMapPre1 _ (hSwV _ hPTBb)]
          dsimp only [selF]
          rw [wp_selectLowBitNoNegCoreSliceDyn bundleF stepsA stepsBF hs v wOuter wInner2 hGiPos
            rMain
            rScrUb hdisj (wp pTurn.compile B_bell)]
          dsimp only [pPost1, sA, sB1, dSwap, rSwap117, rRt, wNegIn, L, rScr]
          conv_lhs => simp only [liftUnitVar_seq, wp_seq_compile]
          conv_rhs => simp only [liftUnitVar_seq, wp_seq_compile]
        let Y_csw := wp pOutFwd.compile (wp P_1.compile
          (wp (liftUnitVar v uEnt1).compile (wp (DynamicCircuit.circuit cSw).compile (Φ k))))
        let Z_csw := wp P_4.compile (wp pOutBwd.compile (wp pReflIn.compile Y_csw))
        have hYcswV : ∀ σ val, Y_csw (Function.update σ v val) = Y_csw σ :=
          hFwdSet.2.1 _ (h1.2.1 _ (hEnt1V _ (fun σ val ↦ by
            simp [DynamicCircuit.compile_circuit, qcWpQAssign, hΦV k σ val])))
        have hZcswV := h4.2.1 _ (hBwd.2.1 _ (hR0Set.2.1 Y_csw hYcswV))
        have hStepB : SelectSwapQROM.restrictZeroSet B_bell rScrUb.image =
            SelectSwapQROM.restrictZeroSet (wp selB.compile Z_csw) rScrUb.image := by
          apply hLiftScr
          have hB1 : SelectSwapQROM.restrictZeroSet B_bell rScr.image =
              SelectSwapQROM.restrictZeroSet
                (wp (liftUnitVar v (.seq uEnt2 (.seq dSwap (bundleB.coreUnitDyn L)))).compile Ψ_k)
                rScr.image := by
            dsimp only [B_bell]
            rw [wp_seq_compile, hEntSw hSimEnt2 hMapEnt2' Θ_mid1 hΘmid1V]
            dsimp only [Θ_mid1, uEnt2, sA, sB2, rRt]
            simp only [liftUnitVar_seq, wp_seq_compile]
          have hSim2 := hSimPre2.restrictZeroSet_eq v hMapPre2' Ψ_k hΨkV
          have hSand2 := restrictZeroSet_wp_bellSandwich58_eq_cswapCircuit v (rCtrl16 14)
            (rCtrl16 14) rSys116 wDst wTmp L.rInner.image hwDstS hwTmpS hNotS hSysDisjS
            hDstTmp hSys2 hSys2 hDst2 pInter hInterDisj hInterV (Φ k) (hΦV k)
          dsimp only at hSand2
          rw [hrSwapEq] at hSand2
          have hInterSw :
              wp (DynamicCircuit.seq (.circuit cSw) (.seq pInter (.circuit cSw))).compile (Φ k) =
                wp (DynamicCircuit.circuit cSw).compile (wp pPost2.compile Z_csw) := by
            dsimp only [pInter, Z_csw, Y_csw]
            simp only [wp_seq_compile]
          rw [hInterSw] at hSand2
          have hP2Z := hPost2V Z_csw hZcswV
          dsimp only [Ψ_k, pTransBell, uEnt2, sA, sB2, dSwap, L, rRt, rScr,
            hdisjScr] at hB1 hSim2 hSand2 ⊢
          rw [hB1, hSim2, hSand2, ← hSimSw0.restrictZeroSet_eq_circuit v _ hP2Z,
            ← hSimPre2.restrictZeroSet_eq v hMapPre2' _ (hSwV _ hP2Z)]
          dsimp only [selB]
          rw [wp_selectLowBitNoNegCoreSliceDyn bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos
            rMain
            rScrUb hdisj Z_csw]
          dsimp only [pPost2, sA, sB2, dSwap, rSwap117, rRt, wNegIn, L, rScr]
          conv_lhs => simp only [liftUnitVar_seq, wp_seq_compile]
          conv_rhs => simp only [liftUnitVar_seq, wp_seq_compile]
        have hHeadA : SelectSwapQROM.restrictZeroSet (wp pHead.compile (Φ (k + 1))) S_full =
            SelectSwapQROM.restrictZeroSet
              (wp pOutFwd.compile (wp P_1.compile (wp selF.compile (wp pTurn.compile B_bell))))
              S_full := by
          rw [hSucc]
          refine restrictZeroSet_eq_of_subset hSubScrFull ?_
          change SelectSwapQROM.restrictZeroSet (wp (DynamicCircuit.seq pOutFwd P_1).compile _)
            rScrUb.image = SelectSwapQROM.restrictZeroSet
              (wp (DynamicCircuit.seq pOutFwd P_1).compile _) rScrUb.image
          rw [← (hFwdSet.seq h1).2.2.2, hStepA, (hFwdSet.seq h1).2.2.2]
        have hReassocStep : wp pOutFwd.compile (wp P_1.compile (wp selF.compile
            (wp pTurn.compile (wp selB.compile Z_csw)))) =
            wp (DynamicCircuit.seq P_single_cswap pReflIn).compile Y_csw := by
          dsimp only [P_single_cswap, outerSeqWrapDyn, Z_csw]
          simp only [wp_seq_compile]
        have hY_eq : SelectSwapQROM.restrictZeroSet Y_csw S_full =
            SelectSwapQROM.restrictZeroSet
              (qcWpQAssign (rMain.embedUnitary (uRefl2 * (R₀ * uRefl2) ^ k)) Θ) S_full := by
          refine (restrictZeroSet_eq_of_subset hSubScrFull ?_).trans (ih (by omega))
          change SelectSwapQROM.restrictZeroSet (wp (DynamicCircuit.seq pOutFwd P_1).compile _)
            rScrUb.image = SelectSwapQROM.restrictZeroSet
              (wp (DynamicCircuit.seq pOutFwd P_1).compile _) rScrUb.image
          rw [← (hFwdSet.seq h1).2.2.2, hLiftScr (hEntSw hSimEnt1 hMapEnt1' (Φ k) (hΦV k)),
            (hFwdSet.seq h1).2.2.2]
        rw [hHeadA, hPrefixCongr hBbellV (hs2.2.1 Z_csw hZcswV) hStepB, hReassocStep,
          ← H_step.2.2.2 Y_csw, hY_eq, H_step.2.2.2 _,
          H_step.2.2.1 _ (fun σ val ↦ by simp [qcWpQAssign, hΘ σ val]),
          qc_wp_qAssign_comp, ← rMain.embedUnitary_mul, ← rMain.embedUnitary_mul, mul_assoc,
          ← pow_succ]
    · rw [QRegister.whole_embedUnitary, SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
        hUbImg, ← Matrix.mul_assoc, ← hcTarget, Matrix.mul_assoc,
        SelectSwapQROM.zeroProjOn_mul_self]
  have hSet := (SelectSwapQROM.cleanRealizes_iff_set v (QRegister.whole N) rUbZero _ _).mp
    ((AliasPrep.cleanRealizes_sbx_iff _ _ _ _ _).mp hCR)
  dsimp only [rUbZero, rAncZ, rMain, N, combWalkCatRegAt] at hSet
  rw [QRegister.whole_embedUnitary, image_rUbZeroLoc] at hSet
  exact cleanRealizes_rFullZeroLoc_of_set bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sUb v
    (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2)
      (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)) hSet

/-- Router-pre-discharged (`57`-AND) asymmetric / `D_neg` `CleanWalkRefl2At` for
`bellSuperNoNegGen57Dyn` (`1 ≤ K`, covering `K = 1024, 768, 256, 128, 1`). -/
theorem cleanWalkRefl2At_bellSuperNoNegGen57Dyn_asym {Var : Type} [Fintype Var] [DecidableEq Var]
    {kInner tCoreF tCoreB : ℕ} (hk7 : 7 ≤ kInner)
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    {bQPE wOuter wInner2 ko km mLow sUb : ℕ} (K : ℕ) (hK : 1 ≤ K) {hkOut : ko ≤ wOuter}
    {hkMid : km ≤ wInner2}
    (hGiPos : 0 < wInner2) (hs : 1 + kInner ≤ sUb)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ kInner)
    {v : Var} {prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
    {M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2)}
    {raw_4 raw_3 sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (legs : BellAsymLegs Var bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v prepOutImpl M_fwd
      M_bwd
      raw_4 raw_3 sF sB pOutFwd pOutBwd P_1 pTurn P_4)
    (hs1 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_4)
      (selectLowBitNoNegCoreSliceDyn bundleF stepsA57 stepsBFwd57 hs v wOuter wInner2 hGiPos
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hs2 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_3)
      (selectLowBitNoNegCoreSliceDyn bundleB stepsA57 stepsBBwd57 hs v wOuter wInner2 hGiPos
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hTurnSupp : Disjoint pTurn.support (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb kInner
      hs))
    (hInterSupp : 2 ≤ K → Disjoint (P_1.support ∪ P_4.support ∪ pOutFwd.support ∪ pOutBwd.support)
      (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb kInner hs)) :
    let uRefl2 := QubitisedWalk.reflPulledPair (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
      (ubCustomMuxCatUnitary M_fwd prepOutImpl sF)
      (ubCustomMuxCatUnitary M_bwd prepOutImpl sB⁻¹)⁻¹
    let R₀ := QubitisedWalk.reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    CleanWalkRefl2At bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v
      (uRefl2 * (R₀ * uRefl2) ^ (K - 1))
      (bellSuperNoNegGen57Dyn bundleF bundleB bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid
        hGiPos
        hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4) :=
  cleanWalkRefl2At_bellSuperNoNegGenBundleDyn_asym hk7 bundleF bundleB stepsA57 stepsBFwd57
    stepsBBwd57
    specA57 (specB57 false) (specB57 true) runSteps24StepsA57
    (runSteps24StepsB57 false) (specB57_borrows_false false) (ctrl10_pair8_lt145_2 false)
    (runSteps24StepsB57 true) (specB57_borrows_false true) (ctrl10_pair8_lt145_2 true)
    K hK hGiPos hs hsIn legs hs1 hs2 hTurnSupp hInterSupp

/-! ## Section 2: Single-Step (`K = 1`, `StageF` / `StageB`, `hTurnSupp` Only) Splices -/

theorem cleanWalkRefl2At_congr_u {Var : Type} [Fintype Var] [DecidableEq Var]
    {bQPE wOuter wInner2 ko km mLow sUb : ℕ} {hkOut : ko ≤ wOuter} {hkMid : km ≤ wInner2} {v : Var}
    {u₁ u₂ : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))}
    {P : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (hu : u₁ = u₂) (h : CleanWalkRefl2At bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v u₁ P) :
    CleanWalkRefl2At bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v u₂ P :=
  hu ▸ h

/-! ## Section 3: Computable (`{Var : Type}`) `*CompDyn` Circuit Constructors & `rfl` Bridges -/

/-- Computable (`{Var : Type}`) `wNegIn`-free `K`-step `57`-AND Bell-persistent super-reflection
parameterized directly by `(hk6 : 6 ≤ kInner)` and computable `coreF`, `coreB` circuits. -/
def bellSuperNoNegGen57CompDyn {Var : Type} {kInner : ℕ} (hk6 : 6 ≤ kInner)
    (bQPE wOuter wInner2 ko km mLow sUb K : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2)
    (hs : 1 + kInner ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ kInner)
    (coreF coreB :
      Core145Layout kInner (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) →
        DynamicCircuit Unit (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb))
    (v : Var)
    (pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  let wNegIn : Wire wInner2 := ⟨0, hGiPos⟩
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  have hdisj : rMain.DisjointWires rScrUb :=
    combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb
  let rScr := rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
  have hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wNegIn)
  let rSys116 := (rMain.compose (rSysCatUB wOuter wInner2 11)).compose
    (QRegister.block 0 (2 * 58) (by decide))
  let rRt := lowBitRouter23 hk6 wOuter wInner2 wNegIn rMain rScr hdisjScr
  let L := lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisjScr
  let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wNegIn rMain)
    (L.rInner ⟨0, by omega⟩)
  let sA := liftRouterStepsN rRt stepsA57
  let sB1 := liftRouterStepsN rRt stepsBFwd57
  let sB2 := liftRouterStepsN rRt stepsBBwd57
  let uEnt1 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB1)
  let uEnt2 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB2)
  let pPost1 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB1) (routerStepsBwdUnitDyn sA))
  let pPost2 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB2) (routerStepsBwdUnitDyn sA))
  let wDst := rScr ⟨kInner, by omega⟩
  let wTmp := rScr ⟨kInner - 1, by omega⟩
  let pReflIn := reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega) v
  let pHead := DynamicCircuit.seq pOutFwd (.seq P_1 (liftUnitVar v (.seq uEnt1 dSwap)))
  let pMidCore := DynamicCircuit.seq (liftUnitVar v (coreF L))
    (.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
      (.seq pPost1 (.seq pTurn (.seq (liftUnitVar v uEnt2)
        (.seq (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst)
          (liftUnitVar v (coreB L)))))))
  let pInter := DynamicCircuit.seq pPost2
    (.seq P_4 (.seq pOutBwd (.seq pReflIn (.seq pOutFwd (.seq P_1 (liftUnitVar v uEnt1))))))
  let pTransBell := DynamicCircuit.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
    (.seq pInter (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst))
  let pTail := DynamicCircuit.seq pMidCore
    (.seq (liftUnitVar v dSwap) (.seq pPost2 (.seq P_4 pOutBwd)))
  .seq pHead (.seq (iterBinDyn (K - 1) (.seq pMidCore pTransBell)) pTail)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellSuperLegSplice

end
