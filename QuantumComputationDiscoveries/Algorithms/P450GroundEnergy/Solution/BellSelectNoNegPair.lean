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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellPersistNoNeg
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellPersistCore

/-!
# Bell-Singlet Two-Pass `wNegIn`-Free `SELECT` Pair & `5`-Step Mid-Core Realization

Constructs `bellSelectNoNegCoreSlicePairDyn` (`0 < wInner2`, no `wNegIn` or `cEntrySign23`), proves
its
exact `wp` unfolding (`wp_selectLowBitNoNegCoreSliceDyn`), `23`-wire entry simulation
(`simulatesOnProj_noNegCoreSliceEntry`), and `5`-step Bell-persistent middle-core realization
(`cleanRealizesSet_bellFiveStepNoNegCoreSliceDyn`).

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

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellSelectNoNegPair
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn AliasPrep
open QuantumComputation.Specs QuantumComputation.Specs.P450
open CircuitModular GivensOps
open BlockEncodingCore BlockEncodingCircuit
open SelectSwapQROM GivensCascade
open SelectRouter10 TopIntegrationBridge
open Lac2Fused184Select Lac2Fused184SelectWrap Router10Lac2Select
open Phase2MidSandwich MidReflCtxRetain
open PolymorphicFused184Select Lac2ZeroPar183Select
open CompactFoldedSelect ReordOuter13Bridge
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
  hiding blockRemWidth
  outRemWidth midRemWidth combARem
open StepEncK StepDecK CompactStepFast175Core
open CompactOuter9Bound50Core CompactOuter9Bound50Select
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
  (ubCustomMuxCatUnitary outerSandwich_eq_reflPulledPair_customMux)
open CompactTuned162StepWalk CompactTuned162StepZeroCmp20
open CompactZeroCmp20OuterParam CompactStepZeroCmp20OuterParam
open Balanced160Select Pi145SOSPermBridge OneHotSimulates
open LowBitPi145Select BellPhaseASelect BellSingletCSwap58
open Cat11CompactPhase2Bridge DihedralWalkQPE DihedralWalkQPE.MultiGearQPE
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.BlockReflection
open ZeroRcHotPrepMid21Fast TwoGearQPEPhase5
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBox
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open BellRouter57 BellRouter57Pure NoNegSelect57Pure CompactCore145Bundle
open BellPersistNoNeg BellPersistCore

/-! ## Section 3: Bell-Singlet Two-Pass `wNegIn`-Free `SELECT` Pair -/

/-- Branch-polymorphic `wNegIn`-free Bell-singlet two-pass `SELECT` pair (`1 + kInner ≤ sUb`,
`0 < wInner2`, `0 TOFF` when `pTurn.count .TOFF = 0`). -/
noncomputable def bellSelectNoNegCoreSlicePairDyn {Var : Type} {N kInner tCoreF tCoreB sUb : ℕ}
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23)) (hs : 1 + kInner ≤ sUb) (v : Var)
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (rScrUb : QRegister sUb N) (pTurn : DynamicCircuit Var N) : DynamicCircuit Var N :=
  if hdisj : rMain.DisjointWires rScrUb then
    let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
    let rScr : QRegister (1 + kInner) N :=
      rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
    have hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
    let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)
    let rSys116 := (rMain.compose (rSysCatUB wOuter wInner2 11)).compose
      (QRegister.block 0 (2 * 58) (by decide))
    let rRt := lowBitRouter23 bundleF.hk6 wOuter wInner2 wDummy rMain rScr hdisjScr
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisjScr
    let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wDummy rMain)
      (L.rInner ⟨0, by have := bundleF.hk6; omega⟩)
    let sA := LowBitPi145Select.liftRouterStepsN rRt stepsA
    let sB1 := LowBitPi145Select.liftRouterStepsN rRt stepsBF
    let sB2 := LowBitPi145Select.liftRouterStepsN rRt stepsBB
    let uEnt1 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB1)
    let uEnt2 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB2)
    let pPre1 := liftUnitVar v (.seq uEnt1 (.seq dSwap (bundleF.coreUnitDyn L)))
    let pPost1 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB1) (routerStepsBwdUnitDyn sA))
    let pPost2 := liftUnitVar v (.seq (bundleB.coreUnitDyn L)
      (.seq dSwap (.seq (routerStepsBwdUnitDyn sB2) (routerStepsBwdUnitDyn sA))))
    let wDst := rScr ⟨kInner, by omega⟩
    let wTmp := rScr ⟨kInner - 1, by have := bundleF.hk6; omega⟩
    .seq pPre1 (.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
      (.seq pPost1 (.seq pTurn (.seq (liftUnitVar v uEnt2)
        (.seq (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst) pPost2)))))
  else pTurn

@[simp] theorem count_bellSelectNoNegCoreSlicePairDyn_toff {Var : Type}
    {N kInner tCoreF tCoreB sUb : ℕ} {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23)) (hs : 1 + kInner ≤ sUb) (v : Var)
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (rScrUb : QRegister sUb N) (pTurn : DynamicCircuit Var N) :
    (bellSelectNoNegCoreSlicePairDyn bundleF bundleB stepsA stepsBF stepsBB hs v wOuter wInner2
      hGiPos rMain
      rScrUb pTurn).count .TOFF = pTurn.count .TOFF := by
  dsimp only [bellSelectNoNegCoreSlicePairDyn]; split_ifs with hdisj
  · simp [count_liftUnitVar, cswapBlockDyn_count_toff, bundleF.count_toff, bundleB.count_toff]
  · rfl

theorem preservesVInv_bellSelectNoNegCoreSlicePairDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N kInner tCoreF tCoreB sUb : ℕ} {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23)) (hs : 1 + kInner ≤ sUb) (v : Var)
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (rScrUb : QRegister sUb N) {pTurn : DynamicCircuit Var N} (hTurnV : PreservesVInv v pTurn) :
    PreservesVInv v (bellSelectNoNegCoreSlicePairDyn bundleF bundleB stepsA stepsBF stepsBB hs v
      wOuter wInner2
      hGiPos rMain rScrUb pTurn) := by
  dsimp only [bellSelectNoNegCoreSlicePairDyn]; split_ifs with hdisj
  · let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
    let rScr : QRegister (1 + kInner) N :=
      rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
    have hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
    let rRt := lowBitRouter23 bundleF.hk6 wOuter wInner2 wDummy rMain rScr hdisjScr
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisjScr
    have hPool := disjoint_rSwap117_rInner bundleF.hk6 wOuter wInner2 wDummy rMain rScr hdisjScr
    have hcSw := (SimulatesOnProj.ofDiagProj (diagProjSimulates_of_cleanRealizes_unit_bound50 _
      L.rInner hPool _ _ (cleanRealizes_cswapBlockDyn () 58 _ L.rInner hPool
        ⟨0, by have := bundleF.hk6; omega⟩))).1
    obtain ⟨_, hC1, _⟩ := bundleF.simCore L
    have hcEnt (stB : List (RouterStep 23)) :
        ConstWp (.seq
          (routerStepsFwdUnitDyn (LowBitPi145Select.liftRouterStepsN rRt stepsA))
          (routerStepsFwdUnitDyn (LowBitPi145Select.liftRouterStepsN rRt stB))) :=
      (ConstWp.routerStepsFwdBwd _).1.seq (ConstWp.routerStepsFwdBwd _).1
    have hPre1 := (hcEnt stepsBF |>.seq (hcSw.seq
      (SimulatesOnProj.ofDiagProj hC1).1)).preservesVInv v
    have hPost1 := ((ConstWp.routerStepsFwdBwd
      (LowBitPi145Select.liftRouterStepsN rRt stepsBF)).2.seq
      (ConstWp.routerStepsFwdBwd
        (LowBitPi145Select.liftRouterStepsN rRt stepsA)).2).preservesVInv v
    have hPre2 := (hcEnt stepsBB).preservesVInv v
    have hSys (m : Fin (1 + kInner)) : ((rMain.compose (rSysCatUB wOuter wInner2 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).DisjointWires (QRegister.singleton (rScr m)) :=
      QRegister.disjoint_iff.mpr fun _ j ↦ by fin_cases j; exact hdisjScr.ne _ m
    have hDstTmp : rScr ⟨kInner, by omega⟩ ≠ rScr ⟨kInner - 1, by have := bundleF.hk6; omega⟩ :=
      rScr.wires.injective.ne fun h ↦ by
        have hv := congrArg Fin.val h; have hk6 := bundleF.hk6; dsimp at hv; omega
    let wSig := (rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)) 14
    have hEx := (cleanRealizesSet_dBellExit58Dyn (Var := Var) v wSig _ _ _ (hSys _) (hSys _)
      hDstTmp (hdisjScr.ne _ _) (hdisjScr.ne _ _)).2.1
    exact fun Θ _ σ val ↦ hPre1 _ (hEx _ (hPost1 _ (hTurnV _ (hPre2 _
      (wp_dBellEntry58Dyn_update_self v wSig _ _ (hdisjScr.ne _ _) (wp _ Θ)))))) σ val
  · exact hTurnV

theorem wp_selectLowBitNoNegCoreSliceDyn {Var : Type} [Finite Var] [DecidableEq Var]
    {N kInner tCore sUb : ℕ} {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N)
    (hdisj : rMain.DisjointWires rScrUb) (Θ : QCAssertion Var (2 ^ N)) :
    let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
    let rScr : QRegister (1 + kInner) N :=
      rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
    let hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
    let rRt := lowBitRouter23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisjScr
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisjScr
    let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wDummy rMain)
      (L.rInner ⟨0, by have := P.hk6; omega⟩)
    wp (selectLowBitNoNegCoreSliceDyn P stepsA stepsB hs v wOuter wInner2 hGiPos rMain
        rScrUb).compile Θ =
      wp (liftUnitVar v (.seq
          (routerStepsFwdUnitDyn (LowBitPi145Select.liftRouterStepsN rRt stepsA))
          (routerStepsFwdUnitDyn (LowBitPi145Select.liftRouterStepsN rRt stepsB)))).compile
        (wp (liftUnitVar v dSwap).compile (wp (liftUnitVar v (P.coreUnitDyn L)).compile
          (wp (liftUnitVar v dSwap).compile
            (wp (liftUnitVar v (.seq
              (routerStepsBwdUnitDyn (LowBitPi145Select.liftRouterStepsN rRt stepsB))
              (routerStepsBwdUnitDyn
                (LowBitPi145Select.liftRouterStepsN rRt stepsA)))).compile Θ)))) := by
  have := Fintype.ofFinite Var
  intro wDummy rScr hdisjScr rRt L dSwap
  unfold selectLowBitNoNegCoreSliceDyn selectLowBitNoNegCoreDyn selectLowBitNoNegCoreUnitDyn
    selectLowBitNoNegInnerBUnitDyn
  rw [dite_eq_left hdisjScr, dite_eq_left hdisjScr]; dsimp only
  rw [wp_liftUnitVar_routerStepsProg, wp_liftUnitVar_routerStepsProg]
  conv_rhs => rw [liftUnitVar_seq, wp_seq_compile]
  rw [liftUnitVar_seq v dSwap, wp_seq_compile (liftUnitVar v dSwap),
    liftUnitVar_seq v (P.coreUnitDyn L), wp_seq_compile (liftUnitVar v (P.coreUnitDyn L)),
    liftUnitVar_seq v (routerStepsBwdUnitDyn _),
    wp_seq_compile (liftUnitVar v (routerStepsBwdUnitDyn _))]

theorem simulatesOnProj_noNegCoreSliceEntry {N kInner : ℕ} (hk6 : 6 ≤ kInner)
    (stepsA stepsB : List (RouterStep 23)) (specA : (Fin 16 → Bool) → State24)
    (specB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 hk23Le24 stepsA (initState23 x16) = some (specA x16))
    (hRunB : ∀ x16, runSteps24 hk23Le24 stepsB (specA x16) = some (specB (specA x16)))
    (hBorB : ∀ x16 (k : Fin 6), (specB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145)
    (wOuter wInner2 : ℕ) (wDummy : Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (rScr : QRegister (1 + kInner) N) (hdisj : rMain.DisjointWires rScr) :
    let rRt := lowBitRouter23 hk6 wOuter wInner2 wDummy rMain rScr hdisj
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
    ∃ U : Unitary (2 ^ N), SimulatesOnProj (zeroProjOn rScr.image) U
      (.seq (routerStepsFwdUnitDyn (LowBitPi145Select.liftRouterStepsN rRt stepsA))
        (routerStepsFwdUnitDyn (LowBitPi145Select.liftRouterStepsN rRt stepsB))) ∧
      ketPredProj (sValidCore L) * U.1 * zeroProjOn rScr.image = U.1 * zeroProjOn rScr.image := by
  classical
  intro rRt L
  obtain ⟨_, _, hInnerEq, hCtrl10Eq⟩ :=
      lowBitCoreLayout_wires hk6 wOuter wInner2 wDummy rMain rScr hdisj
  let S0 : BitAssignment N → Prop := fun β ↦ ∀ j, β (rScr j) = 0
  have hP0 : zeroProjOn rScr.image = ketPredProj S0 := by
    rw [← basisOutcomeProjector_zero_eq_zeroProjOn, basisOutcomeProjector_zero_eq_ketPredProj]
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)
  let x16Of (β : BitAssignment N) : Fin 16 → Bool := fun j ↦ decide (β (rCtrl16 j) = 1)
  have hInitA (β : BitAssignment N) (h0 : S0 β) (u : Wire 23) :
      β (rRt u) = if (initState23 (x16Of β)).get24 ⟨u.val, by omega⟩ then 1 else 0 := by
    rw [lowBitRouter23_apply, get24_initState23]
    by_cases h1 : u.val = 0
    · rw [dite_eq_left h1, ite_eq_left h1, h0 _]; rfl
    · rw [dite_eq_right h1, ite_eq_right h1]; by_cases h17 : u.val < 17
      · rw [dite_eq_left h17, dite_eq_left h17]; dsimp only [x16Of]
        change β (rCtrl16 ⟨u.val - 1, by omega⟩) =
          if decide (β (rCtrl16 ⟨u.val - 1, by omega⟩) = 1) = true then 1 else 0
        rcases UnsignedGivens.zmod2_eq_zero_or_one (β (rCtrl16 ⟨u.val - 1, by omega⟩)) with h | h
          <;>
          rw [h] <;> decide
      · rw [dite_eq_right h17, dite_eq_right h17, h0 _]; rfl
  let SM : BitAssignment N → Prop := fun γ ↦ ∃ x16,
    (∀ u : Wire 23, γ (rRt u) = if (specA x16).get24 ⟨u.val, by omega⟩ then 1 else 0) ∧
    ∀ idx, γ (L.rInner (innerAfter6Idx idx)) = 0
  let sA := LowBitPi145Select.liftRouterStepsN rRt stepsA
  let sB := LowBitPi145Select.liftRouterStepsN rRt stepsB
  have hSpecA (β : BitAssignment N) (h0 : S0 β) :
      routerStepsOk sA β ∧ SM (routerStepsAssign sA β) := by
    obtain ⟨hOk, hW, hOut⟩ := liftRouterStepsN_spec24 hk23Le24 rRt stepsA _ _
      (hRunA (x16Of β)) β (hInitA β h0)
    refine ⟨hOk, x16Of β, hW, fun idx ↦ ?_⟩
    rw [hOut _ (lowBit_inner6_not_mem_router23 hk6 wOuter wInner2 wDummy rMain rScr hdisj idx),
      hInnerEq, QRegister.compose_apply]; exact h0 _
  have hSpecB (γ : BitAssignment N) (hM : SM γ) :
      routerStepsOk sB γ ∧ sValidCore L (routerStepsAssign sB γ) := by
    rcases hM with ⟨x16, hγRt, hγIn6⟩
    obtain ⟨hOk, hW, hOut⟩ := liftRouterStepsN_spec24 hk23Le24 rRt stepsB _ _ (hRunB x16) γ hγRt
    have hPair (i : Fin 8) : routerStepsAssign sB γ (L.rSelPair8 i) =
        if ctrl10OfState24 (specB (specA x16)) ⟨i.val + 2, by omega⟩ then 1 else 0 := by
      have hs : Lac2Fused184Select.selPair10 i = ⟨i.val + 2, by omega⟩ := by fin_cases i <;> rfl
      change routerStepsAssign sB γ (L.rCtrl10 (Lac2Fused184Select.selPair10 i)) = _
      rw [hs, hCtrl10Eq, hW]; rfl
    refine ⟨hOk, ?_, fun idx ↦ ?_⟩
    · rw [(OneHotSimulates.bitsToNat_basisBits _).symm,
        show basisBits 8 (UnsignedGivens.localIdx L.rSelPair8 _)
        = _ from (basisBits 8).apply_symm_apply _, funext hPair,
        bitsToNat_pair8_eq_pair8NatOf10_b]
      exact h145 x16
    · by_cases h6 : idx.val < 6
      · have heqB : L.rInner idx = rRt ⟨17 + idx.val, by omega⟩ := by
          rw [hInnerEq, QRegister.compose_apply, lowBitRouter23_apply,
            dite_eq_right (by dsimp; omega), dite_eq_right (by dsimp; omega)]
          exact congrArg rScr (Fin.ext (by dsimp; omega))
        rw [heqB, hW, hBorB x16 ⟨idx.val, h6⟩]; rfl
      · rw [show idx = innerAfter6Idx ⟨idx.val - 6, by omega⟩ from
          Fin.ext (by dsimp [innerAfter6Idx]; omega),
          hOut _ (lowBit_inner6_not_mem_router23 hk6 wOuter wInner2 wDummy rMain rScr hdisj _)]
        exact hγIn6 _
  have hMapA : ketPredProj SM * (routerStepsCircuit sA).eval.1 * ketPredProj S0 =
      (routerStepsCircuit sA).eval.1 * ketPredProj S0 := by
    apply OneHotSimulates.matrix_ext_ket
    intro β
    simp only [← mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases h0 : S0 β
    · simp only [h0, (hSpecA β h0).2, ↓reduceIte, ket_routerStepsCircuit, ketPredProj_mulVec_ket]
    · simp only [h0, ↓reduceIte, mulVec_zero]
  have hMapB : ketPredProj (sValidCore L) * (routerStepsCircuit sB).eval.1 * ketPredProj SM =
      (routerStepsCircuit sB).eval.1 * ketPredProj SM := by
    apply OneHotSimulates.matrix_ext_ket
    intro γ
    simp only [← mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases hM : SM γ
    · simp only [hM, (hSpecB γ hM).2, ↓reduceIte, ket_routerStepsCircuit, ketPredProj_mulVec_ket]
    · simp only [hM, ↓reduceIte, mulVec_zero]
  have hSimEnt := (SimulatesOnProj.routerStepsFwd sA S0 fun β h ↦ (hSpecA β h).1).seq
    (SimulatesOnProj.routerStepsFwd sB SM fun γ h ↦ (hSpecB γ h).1)
    (IsDiagProj.conjTranspose_eq ⟨S0, rfl⟩) (IsDiagProj.conjTranspose_eq ⟨SM, rfl⟩) hMapA
  rw [← hP0] at hSimEnt; refine ⟨_, hSimEnt, ?_⟩; rw [hP0]; exact proj_map_mul hMapA hMapB

theorem restrictZeroSet_wp_bellNoNegCoreSlicePair_eq_mid {Var : Type} [Fintype Var]
    [DecidableEq Var] {N kInner tCoreF tCoreB sUb : ℕ} (hk7 : 7 ≤ kInner)
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23)) (specA : (Fin 16 → Bool) → State24)
    (specBF specBB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 hk23Le24 stepsA (initState23 x16) = some (specA x16))
    (hRunBF : ∀ x16, runSteps24 hk23Le24 stepsBF (specA x16) = some (specBF (specA x16)))
    (hBorBF : ∀ x16 (k : Fin 6), (specBF (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145F : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specBF (specA x16))) < 145)
    (hRunBB : ∀ x16, runSteps24 hk23Le24 stepsBB (specA x16) = some (specBB (specA x16)))
    (hBorBB : ∀ x16 (k : Fin 6), (specBB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145B : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specBB (specA x16))) < 145)
    (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N)
    (hdisj : rMain.DisjointWires rScrUb) {pTurn : DynamicCircuit Var N}
    (hTurnSupp : Disjoint pTurn.support
      (((rMain.compose (rSysCatUB wOuter wInner2 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).image ∪ {rScrUb ⟨kInner, by omega⟩}))
    (hTurnV : PreservesVInv v pTurn) (Ψ : QCAssertion Var (2 ^ N))
    (hΨ : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) :
    ∃ B_c : QCAssertion Var (2 ^ N),
      (∀ σ val, B_c (Function.update σ v val) = B_c σ) ∧
      SelectSwapQROM.restrictZeroSet B_c rScrUb.image =
        SelectSwapQROM.restrictZeroSet
          (wp (selectLowBitNoNegCoreSliceDyn bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos rMain
            rScrUb).compile Ψ) rScrUb.image ∧
      SelectSwapQROM.restrictZeroSet
          (wp (bellSelectNoNegCoreSlicePairDyn bundleF bundleB stepsA stepsBF stepsBB hs v wOuter
            wInner2 hGiPos
            rMain rScrUb pTurn).compile Ψ) rScrUb.image =
        SelectSwapQROM.restrictZeroSet
          (wp (selectLowBitNoNegCoreSliceDyn bundleF stepsA stepsBF hs v wOuter wInner2 hGiPos rMain
            rScrUb).compile (wp pTurn.compile B_c)) rScrUb.image := by
  let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
  let rScr : QRegister (1 + kInner) N := rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
  have hLift {A B : QCAssertion Var (2 ^ N)}
      (h : SelectSwapQROM.restrictZeroSet A rScr.image =
        SelectSwapQROM.restrictZeroSet B rScr.image) :
      SelectSwapQROM.restrictZeroSet A rScrUb.image =
        SelectSwapQROM.restrictZeroSet B rScrUb.image := by
    have hu : rScr.image ∪ rScrUb.image = rScrUb.image :=
      Finset.union_eq_right.mpr (rScrUb.image_compose_subset _)
    rw [← hu, ← SelectSwapQROM.restrictZeroSet_union, h, SelectSwapQROM.restrictZeroSet_union]
  have hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)
  let rSys116 := (rMain.compose (rSysCatUB wOuter wInner2 11)).compose
    (QRegister.block 0 (2 * 58) (by decide))
  let rRt := lowBitRouter23 bundleF.hk6 wOuter wInner2 wDummy rMain rScr hdisjScr
  let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisjScr
  let rSwap117 := rSwap117LowBit wOuter wInner2 wDummy rMain
  let cSw := (cswapBlockCircuit 58).onRegister rSwap117
  let dSwap := cswapBlockDyn () 58 rSwap117 (L.rInner ⟨0, by have := bundleF.hk6; omega⟩)
  let sA := LowBitPi145Select.liftRouterStepsN rRt stepsA
  let sB1 := LowBitPi145Select.liftRouterStepsN rRt stepsBF
  let sB2 := LowBitPi145Select.liftRouterStepsN rRt stepsBB
  obtain ⟨_, _, hInnerEq, hCtrl10Eq⟩ :=
    lowBitCoreLayout_wires bundleF.hk6 wOuter wInner2 wDummy rMain rScr hdisjScr
  have hSysRt23 := lowBit_disj_sysCat_router23 bundleF.hk6 wOuter wInner2 wDummy rMain rScr hdisjScr
  have hPool := disjoint_rSwap117_rInner bundleF.hk6 wOuter wInner2 wDummy rMain rScr hdisjScr
  have hSys2 : (QRegister.singleton (rCtrl16 14)).DisjointWires rSys116 :=
    QRegister.disjoint_iff.mpr fun i _ heq ↦ by
      fin_cases i
      exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _ (rMain.wires.injective heq)
  have hrSwapEq : (QRegister.singleton (rCtrl16 14)).concat rSys116 hSys2 = rSwap117 := rfl
  let USwapLoc : Unitary (2 ^ (1 + 2 * 58)) := muxUnitary (QRegister.singleton 0)
    (QRegister.block 1 (2 * 58) (by omega)) (disj_singleton0_block1 (2 * 58))
    (fun σ ↦ if σ = 0 then 1 else permutationUnitary (spinSwapEquiv 58))
  have hcSwEval : cSw.eval = rSwap117.embedUnitary USwapLoc := by
    apply Subtype.ext; rw [Circuit.eval_onRegister, cswapBlockCircuit_eval]
  have hSwClean := diagProjSimulates_of_cleanRealizes_unit_bound50 rSwap117 L.rInner hPool _ _
    (cleanRealizes_cswapBlockDyn () 58 rSwap117 L.rInner hPool ⟨0, by have := bundleF.hk6; omega⟩)
  have hSimSw0 : SimulatesOnProj (zeroProjOn L.rInner.image) cSw.eval dSwap := by
    rw [← basisOutcomeProjector_zero_eq_zeroProjOn, hcSwEval]
    exact SimulatesOnProj.ofDiagProj hSwClean
  have hEq_3 : rCtrl16 14 = rRt 15 := by
    rw [lowBitRouter23_apply, dite_eq_right (by decide), dite_eq_left (by decide)]; rfl
  have hSwapValid : DiagProjSimulates (ketPredProj (sValidCore L))
      (rSwap117.embedUnitary USwapLoc) dSwap := by
    refine hSwClean.tighten ⟨sValidCore L, rfl⟩
      (by rw [basisOutcomeProjector_zero_eq_ketPredProj]
          exact ketPredProj_mul_of_imp fun _ h ↦ h.2)
      (embedMatrix_comm_ketPredProj_bound50 rSwap117 USwapLoc.1 (sValidCore L) fun β l ↦ ?_)
    have hNot (u : Fin 10) : L.rCtrl10 u ∉ Set.range rSwap117.wires := by
      rintro ⟨k, hk⟩; revert hk; refine Fin.addCases (fun a hk ↦ ?_) (fun b hk ↦ ?_) k
      · fin_cases a
        have h15 : rSwap117 (Fin.castAdd (2 * 58) 0) = rRt 15 :=
          (QRegister.concat_apply_left _ rSys116 hSys2 0).trans hEq_3
        have hne : (15 : Wire 23) ≠ routed10Wire23 u := by fin_cases u <;> decide
        exact hne (rRt.wires.injective (h15.symm.trans (hk.trans (hCtrl10Eq u))))
      · exact hSysRt23.ne (QRegister.block 0 (2 * 58) (by decide) b) (routed10Wire23 u)
          ((QRegister.concat_apply_right _ rSys116 hSys2 b).symm.trans (hk.trans (hCtrl10Eq u)))
    have hPairLoc := localIdx_congr_bound50 (β₁ := writeRegBitsBound50 β rSwap117 (basisBits _ l))
      (β₂ := β) L.rSelPair8 fun i ↦ writeRegBitsBound50_apply_of_not_mem _ _ _ _
      (hNot (Lac2Fused184Select.selPair10 i))
    have hIn (idx : Fin kInner) := writeRegBitsBound50_apply_of_not_mem β rSwap117 (basisBits _ l)
      (L.rInner idx) (fun ⟨k, hk⟩ ↦ hPool.ne k idx hk)
    dsimp only [sValidCore]; simp only [hPairLoc, hIn]
  have hPValIn : zeroProjOn L.rInner.image * ketPredProj (sValidCore L) =
      ketPredProj (sValidCore L) := by
    rw [← basisOutcomeProjector_zero_eq_zeroProjOn, basisOutcomeProjector_zero_eq_ketPredProj]
    exact (IsDiagProj.comm ⟨_, rfl⟩ ⟨sValidCore L, rfl⟩).trans
      (ketPredProj_mul_of_imp fun _ h ↦ h.2)
  obtain ⟨U_e1, hSimEnt1, hMapEnt1⟩ :=
    simulatesOnProj_noNegCoreSliceEntry bundleF.hk6 stepsA stepsBF
    specA specBF hRunA hRunBF hBorBF h145F wOuter wInner2 wDummy rMain rScr hdisjScr
  obtain ⟨U_e2, hSimEnt2, hMapEnt2⟩ :=
    simulatesOnProj_noNegCoreSliceEntry bundleF.hk6 stepsA stepsBB
    specA specBB hRunA hRunBB hBorBB h145B wOuter wInner2 wDummy rMain rScr hdisjScr
  obtain ⟨_, hSimC1, _⟩ := bundleF.simCore L; obtain ⟨_, hSimC2, _⟩ := bundleB.simCore L
  have hdBody1 := diagProjSimulates_seq_same_bound50 hSwapValid hSimC1
  have hSimPre1 := hSimEnt1.seq (SimulatesOnProj.ofDiagProj hdBody1) (zeroProjOn_conjTranspose _)
    hdBody1.1.conjTranspose_eq hMapEnt1
  have hMapPre1 : zeroProjOn L.rInner.image * (_ * U_e1).1 * zeroProjOn rScr.image =
      (_ * U_e1).1 * zeroProjOn rScr.image :=
    proj_map_mul hMapEnt1 (by
      rw [Matrix.mul_assoc, hdBody1.2.1, ← Matrix.mul_assoc, hPValIn, ← hdBody1.2.1])
  have hMapPre2 : zeroProjOn L.rInner.image * U_e2.1 * zeroProjOn rScr.image =
      U_e2.1 * zeroProjOn rScr.image := by
    rw [Matrix.mul_assoc, ← hMapEnt2, ← Matrix.mul_assoc, ← Matrix.mul_assoc (zeroProjOn _),
      hPValIn, hMapEnt2]
  let wDst := rScr ⟨kInner, by omega⟩; let wTmp := rScr ⟨kInner - 1, by have := bundleF.hk6; omega⟩
  have hwDstS : wDst ∈ L.rInner.image := (QRegister.mem_image _ _).mpr
    ⟨⟨kInner - 1, by have := bundleF.hk6; omega⟩, by
      rw [hInnerEq]; exact congrArg rScr (Fin.ext (by have := bundleF.hk6; dsimp; omega))⟩
  have hwTmpS : wTmp ∈ L.rInner.image := (QRegister.mem_image _ _).mpr
    ⟨⟨kInner - 2, by have := bundleF.hk6; omega⟩, by
      rw [hInnerEq]; exact congrArg rScr (Fin.ext (by have := bundleF.hk6; dsimp; omega))⟩
  have hNotS : rCtrl16 14 ∉ L.rInner.image := fun hm ↦ by
    obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
    rw [hInnerEq] at hj; exact hdisjScr.ne _ _ hj.symm
  have hSysDisjS : Disjoint rSys116.image L.rInner.image :=
    Finset.disjoint_left.mpr fun _ hw1 hw2 ↦ by
      obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hw1
      obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hw2
      rw [hInnerEq] at hj; exact hdisjScr.ne _ _ hj.symm
  have hDstTmp : wDst ≠ wTmp := rScr.wires.injective.ne fun h ↦ by
    have hv := congrArg Fin.val h; have := bundleF.hk6; dsimp at hv; omega
  have hDst2 : rCtrl16 14 ≠ wDst := hdisjScr.ne _ _
  let pPost1 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB1) (routerStepsBwdUnitDyn sA))
  let pPre2 := liftUnitVar v (.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB2))
  let pMid := DynamicCircuit.seq pPost1 (.seq pTurn pPre2)
  let pPost2 := liftUnitVar v (.seq (bundleB.coreUnitDyn L)
    (.seq dSwap (.seq (routerStepsBwdUnitDyn sB2) (routerStepsBwdUnitDyn sA))))
  have hRtDisj : Disjoint rRt.image (rSys116.image ∪ {wDst}) :=
    Finset.disjoint_left.mpr fun _ hw hU ↦ by
      obtain ⟨u, rfl⟩ := (QRegister.mem_image rRt _).mp hw
      rcases Finset.mem_union.mp hU with hS | hD
      · obtain ⟨_, hk⟩ := (QRegister.mem_image rSys116 _).mp hS; exact hSysRt23.ne _ u hk
      · rw [Finset.mem_singleton, lowBitRouter23_apply] at hD; split_ifs at hD
        · exact absurd (congrArg Fin.val (rScr.wires.injective hD)) (by dsimp; omega)
        · exact hdisjScr.ne _ _ hD
        · exact absurd (congrArg Fin.val (rScr.wires.injective hD)) (by dsimp; omega)
  have hSubRt (st : List (RouterStep 23)) := support_routerStepsFwdBwd_subset
    (LowBitPi145Select.liftRouterStepsN rRt st)
    (LowBitPi145Select.touchesIn_liftRouterStepsN rRt _
      (fun u ↦ (QRegister.mem_image rRt _).mpr ⟨u, rfl⟩) st)
  have hMidDisj : Disjoint pMid.support (rSys116.image ∪ {wDst}) := by
    have hTurnDst : Disjoint pTurn.support (rSys116.image ∪ {wDst}) := by
      rwa [show wDst = rScrUb ⟨kInner, by omega⟩ from congrArg rScrUb (Fin.ext (Nat.zero_add _))]
    simp only [pMid, pPost1, pPre2, DynamicCircuit.support_seq, support_liftUnitVar]
    exact Finset.disjoint_union_left.mpr ⟨hRtDisj.mono_left (Finset.union_subset (hSubRt _).2
      (hSubRt _).2), Finset.disjoint_union_left.mpr ⟨hTurnDst, hRtDisj.mono_left
      (Finset.union_subset (hSubRt _).1 (hSubRt _).1)⟩⟩
  have hPost1V : PreservesVInv v pPost1 :=
    ((ConstWp.routerStepsFwdBwd sB1).2.seq (ConstWp.routerStepsFwdBwd sA).2).preservesVInv v
  have hMidV : PreservesVInv v pMid :=
    fun Θ hΘ ↦ hPost1V _ (hTurnV _ (hSimEnt2.1.preservesVInv v _ hΘ))
  have hPost2V : PreservesVInv v pPost2 :=
    ((SimulatesOnProj.ofDiagProj hSimC2).1.seq (hSimSw0.1.seq
      ((ConstWp.routerStepsFwdBwd sB2).2.seq (ConstWp.routerStepsFwdBwd sA).2))).preservesVInv v
  let Θ₂ := wp pPost2.compile Ψ
  have hΘ₂ : ∀ σ val, Θ₂ (Function.update σ v val) = Θ₂ σ := hPost2V Ψ hΨ
  let selBwd :=
      selectLowBitNoNegCoreSliceDyn bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos rMain rScrUb
  let B_c := wp (DynamicCircuit.seq pPre2 (.circuit cSw)).compile Θ₂
  have hSwΘ₂ : ∀ σ val, wp (DynamicCircuit.circuit cSw).compile Θ₂ (Function.update σ v val) =
      wp (DynamicCircuit.circuit cSw).compile Θ₂ σ := fun σ val ↦ by
    simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign,
      hΘ₂ σ val]
  have hBcV : ∀ σ val, B_c (Function.update σ v val) = B_c σ := by
    dsimp only [B_c]; rw [wp_seq_compile]; exact hSimEnt2.1.preservesVInv v _ hSwΘ₂
  refine ⟨B_c, hBcV, ?_, ?_⟩
  · apply hLift; dsimp only [B_c, selBwd]
    rw [wp_seq_compile,
      wp_selectLowBitNoNegCoreSliceDyn bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos rMain
        rScrUb hdisj Ψ]
    have hFoldΘ₂ : wp (liftUnitVar v (bundleB.coreUnitDyn L)).compile
        (wp (liftUnitVar v dSwap).compile
          (wp (liftUnitVar v (.seq (routerStepsBwdUnitDyn sB2)
            (routerStepsBwdUnitDyn sA))).compile Ψ)) = Θ₂ := by
      symm; dsimp only [Θ₂, pPost2]
      rw [liftUnitVar_seq v (bundleB.coreUnitDyn L), wp_seq_compile,
        liftUnitVar_seq v dSwap, wp_seq_compile]
    dsimp only [wDummy, rScr, hdisjScr, rRt, L, rSwap117, dSwap, sA, sB2, pPre2] at hFoldΘ₂ ⊢
    rw [hFoldΘ₂, hSimEnt2.restrictZeroSet_eq v hMapPre2 _ hSwΘ₂,
      ← hSimSw0.restrictZeroSet_eq_circuit v Θ₂ hΘ₂,
      ← hSimEnt2.restrictZeroSet_eq v hMapPre2 _ (hSimSw0.1.preservesVInv v Θ₂ hΘ₂)]
  · apply hLift
    have hSys (m : Fin (1 + kInner)) : rSys116.DisjointWires (QRegister.singleton (rScr m)) :=
      QRegister.disjoint_iff.mpr fun _ j ↦ by fin_cases j; exact hdisjScr.ne _ m
    have hExV := (cleanRealizesSet_dBellExit58Dyn (Var := Var) v (rCtrl16 14) rSys116 wDst wTmp
      (hSys _) (hSys _) hDstTmp (hdisjScr.ne _ _) (hdisjScr.ne _ _)).2.1
    let pBell := DynamicCircuit.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
      (.seq pMid (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst))
    have hBellV : ∀ σ val,
        wp pBell.compile Θ₂ (Function.update σ v val) = wp pBell.compile Θ₂ σ := by
      intro σ val; dsimp only [pBell]; simp only [wp_seq_compile]
      exact hExV _ (hMidV _ (wp_dBellEntry58Dyn_update_self v (rCtrl16 14) rSys116 wDst
        hDst2 Θ₂)) σ val
    dsimp only [bellSelectNoNegCoreSlicePairDyn]
    rw [dite_eq_left hdisj, wp_seq_compile, wp_bell_assoc]
    have hSim1 := hSimPre1.restrictZeroSet_eq v hMapPre1 _ hBellV
    have hSand := restrictZeroSet_wp_bellSandwich58_eq_cswapCircuit v (rCtrl16 14) (rCtrl16 14)
      rSys116 wDst wTmp L.rInner.image hwDstS hwTmpS hNotS hSysDisjS hDstTmp hSys2 hSys2
      hDst2 pMid hMidDisj hMidV Θ₂ hΘ₂
    dsimp only at hSand; rw [hrSwapEq] at hSand
    have hMidSw : wp (DynamicCircuit.seq (.circuit cSw) (.seq pMid (.circuit cSw))).compile Θ₂ =
        wp (DynamicCircuit.circuit cSw).compile (wp pPost1.compile (wp pTurn.compile B_c)) := by
      dsimp only [pMid, B_c]; simp only [wp_seq_compile]
    rw [hMidSw] at hSand
    dsimp only [wDummy, rScr, hdisjScr, rCtrl16, rSys116, rRt, L, rSwap117, dSwap, sA, sB1, sB2,
      pPost1, pPre2, pMid, pPost2, Θ₂, wDst, wTmp] at hSim1 hSand ⊢
    rw [hSim1, hSand]
    have hPTBc := hPost1V _ (hTurnV B_c hBcV)
    rw [← hSimSw0.restrictZeroSet_eq_circuit v _ hPTBc,
      ← hSimPre1.restrictZeroSet_eq v hMapPre1 _ (hSimSw0.1.preservesVInv v _ hPTBc),
      wp_selectLowBitNoNegCoreSliceDyn bundleF stepsA stepsBF hs v wOuter wInner2 hGiPos rMain
        rScrUb hdisj
        (wp pTurn.compile B_c)]
    dsimp only [pPost1, sA, sB1, dSwap, rSwap117, rRt, wDummy, L, rScr]
    conv_lhs => simp only [liftUnitVar_seq, wp_seq_compile]
    conv_rhs => simp only [liftUnitVar_seq, wp_seq_compile]

attribute [irreducible] bellSelectNoNegCoreSlicePairDyn

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellSelectNoNegPair
end
