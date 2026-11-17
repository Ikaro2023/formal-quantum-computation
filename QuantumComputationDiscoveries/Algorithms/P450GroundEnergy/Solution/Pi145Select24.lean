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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145Select24Aux
/-!
# `24`-Wire `55`-AND `wNegIn`-Free Bell-Persistent Super-Reflections
Constructs `{Var : Type}`-polymorphic `K`-step and single-step Bell-persistent walk reflections
(`bellSuperNoNeg24GenDyn`, `bellSuperNoNeg2455Dyn`, `bellRefl2NoNeg24GenDyn`,
`bellRefl2NoNeg24_se55Dyn`) and drop-in `*CompDyn` / `*_se55Dyn` aliases instantiated with the
`55`-AND (`14 + 41`) `π145` `SiZero` single-pass slices from `Pi145Select24Aux`.
-/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn AliasPrep
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution Solution.TwoGearBox
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Phase2MidSandwich Solution.MidReflCtxRetain
open Solution.OneHotSimulates
open Solution.PolymorphicFused184Select Solution.ReordOuter13Bridge
open Solution.CompactOuter9Bound50Core
open Solution.CompactStepFast176Select hiding blockRemWidth
  outRemWidth midRemWidth combARem
open Solution.MobiusOptSubcube163Walk
  (ubCustomMuxCatUnitary outerSandwich_eq_reflPulledPair_customMux)
open Solution.CompactOuter9Bound50Select Solution.CompactTuned162StepWalk Solution.Balanced160Select
open Solution.CompactTuned162StepZeroCmp20 Solution.CompactZeroCmp20OuterParam
open Solution.BellPhaseASelect
open Solution.CompactStepZeroCmp20OuterParam Solution.Pi145SOSPermBridge Solution.LowBitPi145Select
open Solution.BellSingletCSwap58 Solution.Cat11CompactPhase2Bridge Solution.DihedralWalkQPE
open Solution.DihedralWalkQPE.MultiGearQPE Solution.DihedralWalkQPE.BlockReflection
open Solution.TwoGearQPEPhase5
open Solution.ZeroRcHotPrepMid21Fast Solution.Pi145CompactRouter Solution.NoNegSelect57Pure
open Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Solution.CompactCore145Bundle Solution.BellPersistNoNeg Solution.BellSelectNoNegPair
open Solution.Select57Slices Solution.BellPersistCore Solution.BellPersistSuperWalk
open Solution.BellSuperNoNegWalk Solution.BellAsymCore Solution.TwoGearSuperPhase5
open Solution.ThreeGearBellSuper Solution.BellSuperLegSplice
open Solution.QubitisedWalk (reflPulledPair reflInUnitary reflMidUnitary)
open Solution.GivensCascade (compose_disjointWires_right)
open Solution.BellRouter57 Solution.BellRouter57Pure
local instance (priority := 99999) instNeZeroTwoPowSel24B (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance instDecDisjWires24B {k₁ k₂ N : ℕ} (r₁ : QRegister k₁ N) (r₂ : QRegister k₂ N) :
    Decidable (r₁.DisjointWires r₂) :=
  decidable_of_iff (∀ i j, r₁ i ≠ r₂ j) QRegister.disjoint_iff.symm
open NoNegSelect57Pure
namespace Pi145CompactSelect24
theorem realizesEmbedded_selectLowBit24NoNegCoreUnitDyn {N kInner tCore : ℕ} (hk7 : 7 ≤ kInner)
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)} (P :
      GenCore145Bundle kInner tCore branch10) (stepsA
    stepsB : List (RouterStep 24)) (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 le_rfl stepsA (initState23 x16) = some (specA x16)) (hRunB : ∀ x16,
    runSteps24 le_rfl stepsB (specA x16) = some (specB (specA x16))) (hBorB : ∀ x16 (k : Fin 7),
    (specB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false) (h145 : ∀ x16, pair8NatOf10
    (ctrl10OfState24 (specB (specA x16))) < 145) (hInd15 : ∀ x16 : Fin 16 → Bool, y12NoNegOfState24
    specA specB x16 = y12NoNegOf15 specA specB (fun i ↦ x16 ⟨i.val, by omega⟩)) (wOuter wInner2 : ℕ)
    (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N)
    (hdisj : rMain.DisjointWires rScr) : ∃ WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)),
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rMain rScr (selectNoNegCat11Unitary
    specA specB wOuter wInner2 WPhased)
      (selectLowBit24NoNegCoreUnitDyn hk7 P.coreUnitDyn stepsA stepsB
    wOuter wInner2 hGiPos rMain rScr) ∧ ∀ (c : Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ),
      (WPhased c).1 *ᵥ
    prodState ψ (phaseGradientLowFactor 11 3) = prodState ((branch10 c).1 *ᵥ ψ)
    (phaseGradientLowFactor 11 3) := by
  classical
  let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
  let rRouter24 := lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
  let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
  have hInnerEq := (lowBitCoreLayout_wires24 hk7 wOuter wInner2 wDummy rMain rScr hdisj).2.2.1
  let rAllN := rMain.compose (rAllInCat wOuter wInner2 11)
  let rSysCat := rMain.compose (rSysCatUB wOuter wInner2 11)
  have hSysRt24 := lowBit_disj_sysCat_router24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
  have hRtSys := QRegister.disjoint_comm.mp hSysRt24
  obtain ⟨WPhased, hSimInnerB, hCatPh⟩ := diagProjSimulates_selectLowBit24NoNegInnerBUnitDyn hk7 P
    stepsB specA specB hRunB hBorB h145 wOuter wInner2 hGiPos rMain rScr hdisj
  refine ⟨WPhased, ?_, hCatPh⟩
  rw [selectLowBit24NoNegCoreUnitDyn, dite_eq_left hdisj]
  let PMid := ketPredProj (sMidLowBit24 hk7 specA wOuter wInner2 wDummy rMain rScr hdisj)
  let UMid := lowBitMidUnitary24 specB rRouter24 rSysCat hRtSys WPhased
  let SScr : BitAssignment N → Prop := fun β ↦ ∀ j : Fin (1 + kInner), β (rScr j) = 0
  let x16Of (β : BitAssignment N) : Fin 16 → Bool := bitsOfFin 16
    ((selPolyCtrl16 wOuter wInner2 wDummy).extractIndex (rAllN.extractIndex ((basisBits N).symm β)))
  have hx16Eq (β : BitAssignment N) (l : Fin (2 ^ (2 * 58 + 11))) : x16Of (writeRegBitsBound50 β
      rSysCat (basisBits _ l)) = x16Of β := by
    dsimp only [x16Of]
    congr 2
    refine (basisBits (mAncUB wOuter wInner2)).injective (funext fun i ↦ ?_)
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, basisBits_symm,
      basisBits_symm]
    exact writeRegBitsBound50_apply_of_not_mem β rSysCat (basisBits _ l) (rAllN i) fun ⟨k, hk⟩ ↦
      (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne i k (rMain.wires.injective hk.symm)
  have hInitβ (β : BitAssignment N) (h0 : SScr β) :
      ∀ u : Wire 24, β (rRouter24 u) = if (initState23 (x16Of β)).get24 ⟨u.val, by omega⟩ then 1
        else 0 :=
          initState23_assign_lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj h0 fun j ↦
    by
      dsimp only [x16Of]
      rw [congrFun (bitsOfFin_extractIndex (selPolyCtrl16 wOuter wInner2 wDummy) _) j]
      dsimp only [bitsOfFin]
      rw [QRegister.basisBits_extractIndex, basisBits_symm]
      rfl
  have hStA (β : BitAssignment N) (h0 : SScr β) :
      state24OfRouter24 rRouter24 (routerStepsAssign (liftRouterStepsN rRouter24 stepsA) β) =
        specA (x16Of β) := State24.ext24 fun i ↦ by
    obtain ⟨_, hRtW, _⟩ := liftRouterStepsN_spec24 le_rfl rRouter24 stepsA _ _
      (hRunA (x16Of β)) β (hInitβ β h0)
    rw [get24_state24OfRouter24, hRtW i, show (⟨i.val, by omega⟩ : Fin 24) = i from rfl]
    cases (specA (x16Of β)).get24 i <;> decide
  let BOf (β : BitAssignment N) : Unitary (2 ^ (2 * 58 + 11)) := selectGenCoreBranch 11
    (fun m10 ↦ WPhased (finOfBits 10 m10)) (y12NoNegOfState24 specA specB (x16Of β))
  let UTgt := rMain.embedUnitary (selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased)
  have hPScrEq : ketPredProj SScr = rScr.basisOutcomeProjector 0 :=
    (basisOutcomeProjector_zero_eq_ketPredProj rScr).symm
  have hSimAll : DiagProjSimulates (ketPredProj SScr) UTgt (routerStepsProg () (liftRouterStepsN
      rRouter24 stepsA) (selectLowBit24NoNegInnerBUnitDyn hk7 P.coreUnitDyn stepsB wOuter wInner2
        hGiPos
      rMain rScr)) := by
    refine diagProjSimulates_liftRouterStepsN le_rfl rRouter24 rSysCat hSysRt24 stepsA PMid UMid
      UTgt _ hSimInnerB (commutesWithWire_lowBitMidUnitary24 specB rRouter24 rSysCat hRtSys WPhased)
      SScr (fun β ↦ initState23 (x16Of β)) (fun β ↦ specA (x16Of β)) BOf
      (fun β l _ ↦ congrArg initState23 (hx16Eq β l)) (fun β l _ ↦ congrArg specA (hx16Eq β l))
      hInitβ (fun β _ ↦ hRunA (x16Of β)) ?_ ?_ ?_ ?_
    · intro β h0
      obtain ⟨_, _, hRtOut⟩ := liftRouterStepsN_spec24 le_rfl rRouter24 stepsA _ _
        (hRunA (x16Of β)) β (hInitβ β h0)
      have hIn7 (idx : Fin (kInner - 7)) : routerStepsAssign (liftRouterStepsN rRouter24 stepsA) β
          (L.rInner (innerAfter7Idx idx)) = 0 := by
        rw [hRtOut _ (lowBit_inner7_not_mem_router24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
          idx),
          hInnerEq, QRegister.compose_apply]
        exact h0 _
      rw [ketPredProj_mulVec_ket, ite_eq_left_of_eq_true _ _ (eq_true ⟨⟨x16Of β, hStA β h0⟩, hIn7⟩)]
    · intro β h0
      let βA := routerStepsAssign (liftRouterStepsN rRouter24 stepsA) β
      have hm := lowBitMidUnitary24_mulVec_ket specB rRouter24 rSysCat hRtSys WPhased βA
      dsimp only at hm
      rw [hStA β h0] at hm
      have h10 : (fun j : Fin 10 ↦ y12NoNegOfState24 specA specB (x16Of β) ⟨j.val, by omega⟩) =
          ctrl10OfState24 (specB (specA (x16Of β))) := funext fun j ↦ dite_eq_left j.isLt
      rw [hm]
      refine congrArg (fun M ↦ M.mulVec (OneHotSimulates.ket βA))
        (congrArg rSysCat.embedMatrix (congrArg Subtype.val ?_))
      dsimp only [BOf, selectGenCoreBranch]
      rw [h10, show y12NoNegOfState24 specA specB (x16Of β) 10 = sigSelOfState24 (specB (specA
        (x16Of β))) from rfl, show y12NoNegOfState24 specA specB (x16Of β) 11 = false from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    · intro β _
      dsimp only [UTgt]
      rw [selectNoNegCat11Unitary_eq_mux_rAllInCat hInd15 wOuter wInner2 wDummy WPhased,
        embedUnitary_muxUnitary]
      refine muxUnitary_mulVec_of_proj rAllN rSysCat _ _
        (rAllN.extractIndex ((basisBits N).symm β)) _ fun q hq ↦ ?_
      simp only [OneHotSimulates.ket, basisState]
      rw [Pi.single_eq_of_ne]
      rintro rfl
      exact hq rfl
    · rw [hPScrEq]
      exact rMain.embedMatrix_comm_basisOutcomeProjector_of_disjoint rScr hdisj _ 0
  rw [hPScrEq] at hSimAll
  exact hSimAll.toGlobalCleanSimulates.toRealizesEmbedded
theorem cleanRealizes_selectLowBit24NoNegCoreDyn {Var : Type} [Fintype Var] [DecidableEq Var] {N
    kInner tCore : ℕ} (hk7 : 7 ≤ kInner) {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)} (P :
    GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 24)) (specA :
      (Fin 16 →
    Bool) → State24) (specB : State24 → State24) (hRunA : ∀ x16, runSteps24 le_rfl stepsA
    (initState23 x16) = some (specA x16)) (hRunB : ∀ x16, runSteps24 le_rfl stepsB (specA x16) =
    some (specB (specA x16))) (hBorB : ∀ x16 (k : Fin 7), (specB (specA x16)).get24 ⟨17 + k.val,
    by omega⟩ = false) (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145)
    (hInd15 : ∀ x16 : Fin 16 → Bool, y12NoNegOfState24 specA specB x16 = y12NoNegOf15 specA specB
    (fun i ↦ x16 ⟨i.val, by omega⟩)) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain :
      QRegister
    (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) (hdisj :
      rMain.DisjointWires rScr) : ∃
    WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)), CleanRealizes v rMain rScr
    (selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased) (selectLowBit24NoNegCoreDyn hk7
    P.coreUnitDyn stepsA stepsB v wOuter wInner2 hGiPos rMain rScr) ∧ ∀ (c : Fin (2 ^ 10)) (ψ :
      Fin (2 ^
    58) → ℂ), (WPhased c).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) = prodState ((branch10
    c).1 *ᵥ ψ) (phaseGradientLowFactor 11 3) := by
  obtain ⟨WPhased, hReal, hCatPh⟩ := realizesEmbedded_selectLowBit24NoNegCoreUnitDyn hk7 P stepsA
    stepsB specA specB hRunA hRunB hBorB h145 hInd15 wOuter wInner2 hGiPos rMain rScr hdisj
  exact ⟨WPhased, cleanRealizes_liftUnitVar v rMain rScr _ _ hdisj
    (count_selectLowBit24NoNegCoreUnitDyn_toff hk7 P.count_toff stepsA stepsB wOuter wInner2 hGiPos
      rMain
      rScr) hReal, hCatPh⟩
theorem cleanRealizesSet_selectLowBit24NoNegCoreSliceDyn {Var : Type} [Fintype Var] [DecidableEq
    Var] {N kInner tCore sUb : ℕ} (hk7 : 7 ≤ kInner) {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 24)) (specA :
      (Fin
    16 → Bool) → State24) (specB : State24 → State24) (hRunA : ∀ x16, runSteps24 le_rfl stepsA
    (initState23 x16) = some (specA x16)) (hRunB : ∀ x16, runSteps24 le_rfl stepsB (specA x16) =
    some (specB (specA x16))) (hBorB : ∀ x16 (k : Fin 7), (specB (specA x16)).get24 ⟨17 + k.val,
    by omega⟩ = false) (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145)
    (hInd15 : ∀ x16 : Fin 16 → Bool, y12NoNegOfState24 specA specB x16 = y12NoNegOf15 specA specB
    (fun i ↦ x16 ⟨i.val, by omega⟩)) (hInv126 : ∀ (xo' : Fin (2 ^ 8)) (so : Bool) (b : Fin (2 ^ 5))
    (si : Bool), 126 ≤ xo'.val → y12NoNegOf15 specA specB (pack15 xo' so b si) = y12NoNegOf15 specA
    specB (pack15 xo' so 0 si)) (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos :
      0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N) (hdisj :
    rMain.DisjointWires rScrUb) : ∃ selectCat : Unitary (2 ^ (nUB wOuter wInner2 + 11)),
      CleanRealizesSet
    v rScrUb.image (rMain.embedUnitary selectCat) (selectLowBit24NoNegCoreSliceDyn hk7
    P.coreUnitDyn stepsA stepsB hs v wOuter wInner2 hGiPos rMain rScrUb) ∧ PreservesWires
    (rMain.embedUnitary selectCat).1 ((((rMain.compose (rUBInCat wOuter wInner2 11)).compose
      (rAllUB wOuter
    wInner2)).image) ∪ rScrUb.image) ∧ LowBitPi145Select.SelCatEqOuterInner wOuter wInner2 selectCat
    (selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2) ∧
      LowBitPi145Select.SelCatEqOuterInner
    wOuter wInner2 selectCat⁻¹ (selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2)⁻¹ ∧
    SelectCatPi145OneBodyMidCoreComm selectCat ∧ (∀ A : Operator (2 ^ wInner2), selectCat.1 *
    (rMidInnerInCat wOuter wInner2 11).embedMatrix A =
      (rMidInnerInCat wOuter wInner2 11).embedMatrix A *
    selectCat.1) := by
  obtain ⟨WPhased, hClean, hCatPh⟩ := cleanRealizes_selectLowBit24NoNegCoreDyn hk7 P stepsA stepsB
    specA specB hRunA hRunB hBorB h145 hInd15 v wOuter wInner2 hGiPos rMain
    (rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))) (compose_disjointWires_right hdisj)
  have hFwd :=
    selectNoNegCat11Unitary_mulVec_tensorUBCat_eq branch10 specA specB wOuter wInner2 WPhased
    hCatPh
  exact ⟨selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased,
    (cleanRealizes_iff_set v rMain rScrUb _ _).mp
      (hClean.extend_scr hdisj (rScrUb.image_compose_subset _)),
    preservesWires_selectNoNegCat11Unitary specA specB WPhased rMain rScrUb hdisj, hFwd,
    unitary_inv_mulVec_tensorUBCat_poly _ _ _ hFwd,
    selectCatPi145OneBodyMidCoreComm_selectNoNegCat11Unitary specA specB hInv126 wOuter wInner2
      WPhased,
    selectNoNegCat11Unitary_comm_rMidInnerInCat specA specB wOuter wInner2 WPhased⟩
/-- Computable `(160 - d)`-scratch (`0 ≤ d ≤ 10`) single-pass `55`-AND `wNegIn`-free `SELECT` slice
(`0 < wInner2`). -/
def compactSelect55NoNegSliceDyn {Var : Type} {N sUb : ℕ} (d : ℕ) (hd : d ≤ 10) (oddPass : Bool)
    (hs : 160 - d ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain :
      QRegister (nUB wOuter wInner2
    + 11) N) (rScrUb : QRegister sUb N) : DynamicCircuit Var N :=
  selectLowBit24NoNegCoreSliceDyn (kInner := 159 - d) (by omega)
    (compactStepCoreUnitDyn d hd actFlip145 (orbitalOfPi14555 oddPass)
      (negMaskPi14555 oddPass)) stepsA55 (stepsB55 oddPass) (by omega) v wOuter wInner2 hGiPos rMain
    rScrUb
theorem cleanRealizesSetCompactSelect55NoNegSliceDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sUb : ℕ} (d : ℕ) (hd : d ≤ 10) (oddPass : Bool) (hs : 160 - d ≤ sUb) (v :
      Var) (wOuter wInner2 : ℕ)
    (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb :
      QRegister sUb N) (hdisj :
    rMain.DisjointWires rScrUb) : ∃ selectCat : Unitary (2 ^ (nUB wOuter wInner2 + 11)),
      CleanRealizesSet
    v rScrUb.image (rMain.embedUnitary selectCat) (compactSelect55NoNegSliceDyn d hd oddPass hs v
    wOuter wInner2 hGiPos rMain rScrUb) ∧ PreservesWires (rMain.embedUnitary selectCat).1
    ((((rMain.compose (rUBInCat wOuter wInner2 11)).compose (rAllUB wOuter wInner2)).image) ∪
      rScrUb.image) ∧
    LowBitPi145Select.SelCatEqOuterInner wOuter wInner2 selectCat
      (select55NoNegPureUnitary oddPass wOuter
    wInner2) ∧
      LowBitPi145Select.SelCatEqOuterInner wOuter wInner2 selectCat⁻¹ (select55NoNegPureUnitary
    oddPass wOuter wInner2)⁻¹ ∧ SelectCatPi145OneBodyMidCoreComm selectCat ∧ (∀ A :
      Operator (2 ^ wInner2),
    selectCat.1 * (rMidInnerInCat wOuter wInner2 11).embedMatrix A =
      (rMidInnerInCat wOuter wInner2 11).embedMatrix A
    * selectCat.1) := by
  rw [compactSelect55NoNegSliceDyn, select55NoNegPureUnitary]
  exact cleanRealizesSet_selectLowBit24NoNegCoreSliceDyn (by omega)
    (compactCore145Bundle d hd oddPass).toGen stepsA55 (stepsB55 oddPass) specA55
    (specB55 oddPass) runSteps24StepsA55 (runSteps24StepsB55 oddPass)
    (specB55_borrows_false oddPass) (ctrl10_pair8_lt145 oddPass)
    (y12NoNegOfState2455_indep15 oddPass) (y12NoNegOf1555_of_ge126 oddPass) (by omega) v wOuter
    wInner2 hGiPos rMain rScrUb hdisj
/-! ## Section 3: `24`-Wire Slice `wp` Expansion & Entry Simulation -/
theorem wp_selectLowBit24NoNegCoreSliceDyn {Var : Type} [Finite Var] [DecidableEq Var]
    {N kInner tCore sUb : ℕ} (hk7 : 7 ≤ kInner) {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 24))
    (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N)
    (hdisj : rMain.DisjointWires rScrUb) (Θ : QCAssertion Var (2 ^ N)) :
    let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
    let rScr : QRegister (1 + kInner) N :=
      rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
    let hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
    let rRt := lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisjScr
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisjScr
    let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wDummy rMain) (L.rInner ⟨0, by
      omega⟩)
    wp (selectLowBit24NoNegCoreSliceDyn hk7 P.coreUnitDyn stepsA stepsB hs v wOuter wInner2 hGiPos
      rMain
        rScrUb).compile Θ =
      wp (liftUnitVar v (.seq (routerStepsFwdUnitDyn (liftRouterStepsN rRt stepsA))
          (routerStepsFwdUnitDyn (liftRouterStepsN rRt stepsB)))).compile
        (wp (liftUnitVar v dSwap).compile (wp (liftUnitVar v (P.coreUnitDyn L)).compile
          (wp (liftUnitVar v dSwap).compile
            (wp (liftUnitVar v (.seq (routerStepsBwdUnitDyn (liftRouterStepsN rRt stepsB))
              (routerStepsBwdUnitDyn (liftRouterStepsN rRt stepsA)))).compile Θ)))) := by
  intro wDummy rScr hdisjScr rRt L dSwap
  cases nonempty_fintype Var
  unfold selectLowBit24NoNegCoreSliceDyn selectLowBit24NoNegCoreDyn selectLowBit24NoNegCoreUnitDyn
    selectLowBit24NoNegInnerBUnitDyn
  rw [dite_eq_left hdisjScr, dite_eq_left hdisjScr]
  dsimp only
  rw [wp_liftUnitVar_routerStepsProg, wp_liftUnitVar_routerStepsProg]
  conv_rhs => rw [liftUnitVar_seq, wp_seq_compile]
  rw [liftUnitVar_seq v dSwap, wp_seq_compile (liftUnitVar v dSwap), liftUnitVar_seq v
    (P.coreUnitDyn L), wp_seq_compile (liftUnitVar v (P.coreUnitDyn L)), liftUnitVar_seq v
    (routerStepsBwdUnitDyn _), wp_seq_compile (liftUnitVar v (routerStepsBwdUnitDyn _))]
theorem simulatesOnProj_noNeg24CoreSliceEntry {N kInner : ℕ} (hk7 : 7 ≤ kInner)
    (stepsA stepsB : List (RouterStep 24)) (specA : (Fin 16 → Bool) → State24)
    (specB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 le_rfl stepsA (initState23 x16) = some (specA x16))
    (hRunB : ∀ x16, runSteps24 le_rfl stepsB (specA x16) = some (specB (specA x16)))
    (hBorB : ∀ x16 (k : Fin 7), (specB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145) (wOuter wInner2 : ℕ)
    (wDummy : Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N)
    (hdisj : rMain.DisjointWires rScr) :
    let rRt := lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
    ∃ U : Unitary (2 ^ N), SimulatesOnProj (zeroProjOn rScr.image) U
      (.seq (routerStepsFwdUnitDyn (liftRouterStepsN rRt stepsA))
        (routerStepsFwdUnitDyn (liftRouterStepsN rRt stepsB))) ∧
      ketPredProj (sValidCore L) * U.1 * zeroProjOn rScr.image = U.1 * zeroProjOn rScr.image := by
  classical
  intro rRt L
  have hInnerEq := (lowBitCoreLayout_wires24 hk7 wOuter wInner2 wDummy rMain rScr hdisj).2.2.1
  let S0 : BitAssignment N → Prop := fun β ↦ ∀ j, β (rScr j) = 0
  have hP0 : zeroProjOn rScr.image = ketPredProj S0 := by
    rw [← basisOutcomeProjector_zero_eq_zeroProjOn, basisOutcomeProjector_zero_eq_ketPredProj]
  let x16Of (β : BitAssignment N) : Fin 16 → Bool :=
    fun j ↦ decide (β ((rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)) j) = 1)
  let SM : BitAssignment N → Prop := fun γ ↦ ∃ x16,
    (∀ u : Wire 24, γ (rRt u) = if (specA x16).get24 ⟨u.val, by omega⟩ then 1 else 0) ∧
    ∀ idx, γ (L.rInner (innerAfter7Idx idx)) = 0
  let sA := liftRouterStepsN rRt stepsA
  let sB := liftRouterStepsN rRt stepsB
  have hSpecA (β : BitAssignment N) (h0 : S0 β) : routerStepsOk sA β ∧ SM (routerStepsAssign sA β)
      := by
    obtain ⟨hOk, hW, hOut⟩ := liftRouterStepsN_spec24 le_rfl rRt stepsA _ _ (hRunA (x16Of β)) β
      (initState23_assign_lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj h0 fun _ ↦ rfl)
    refine ⟨hOk, x16Of β, hW, fun idx ↦ ?_⟩
    rw [hOut _ (lowBit_inner7_not_mem_router24 hk7 wOuter wInner2 wDummy rMain rScr hdisj idx),
      hInnerEq,
      QRegister.compose_apply]
    exact h0 _
  have hSpecB (γ : BitAssignment N) (hM : SM γ) : routerStepsOk sB γ ∧ sValidCore L
      (routerStepsAssign sB γ) := by
    rcases hM with ⟨x16, hγRt, hγIn7⟩
    obtain ⟨hOk, hW, hOut⟩ := liftRouterStepsN_spec24 le_rfl rRt stepsB _ _ (hRunB x16) γ hγRt
    exact ⟨hOk, sValidCore_of_routerSteps24 hk7 wOuter wInner2 wDummy rMain rScr hdisj (hBorB x16)
      (h145 x16) hW hOut hγIn7⟩
  have hMap {s : List (RouterStep N)} {P Q : BitAssignment N → Prop}
      (hPQ : ∀ β, P β → Q (routerStepsAssign s β)) :
      ketPredProj Q * (routerStepsCircuit s).eval.1 * ketPredProj P =
        (routerStepsCircuit s).eval.1 * ketPredProj P := OneHotSimulates.matrix_ext_ket fun β ↦ by
    simp only [← mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases hP : P β
    · simp only [hP, hPQ β hP, ↓reduceIte, ket_routerStepsCircuit, ketPredProj_mulVec_ket]
    · simp only [hP, ↓reduceIte, mulVec_zero]
  have hMapA := hMap fun β h ↦ (hSpecA β h).2
  have hSimEnt := (SimulatesOnProj.routerStepsFwd sA S0 fun β h ↦ (hSpecA β h).1).seq
    (SimulatesOnProj.routerStepsFwd sB SM fun γ h ↦ (hSpecB γ h).1)
    (IsDiagProj.conjTranspose_eq ⟨S0, rfl⟩) (IsDiagProj.conjTranspose_eq ⟨SM, rfl⟩) hMapA
  rw [← hP0] at hSimEnt
  refine ⟨_, hSimEnt, ?_⟩
  rw [hP0]
  exact proj_map_mul hMapA (hMap fun γ h ↦ (hSpecB γ h).2)
/-! ## Section 4: `24`-Wire `K`-Step & `1`-Step Bell Super-Reflections & `BellAsymLegs` Splices -/
/-- Computable (`{Var : Type}`) `24`-wire `wNegIn`-free `K`-step Bell-persistent super-reflection
parameterized by `(hk7 : 7 ≤ kInner)` and computable `coreUnitDynF`, `coreUnitDynB` circuits. -/
def bellSuperNoNeg24GenDyn {Var : Type} {kInner : ℕ} (hk7 : 7 ≤ kInner) (coreUnitDynF coreUnitDynB
    : ∀ {n : ℕ}, Core145Layout kInner n → DynamicCircuit Unit n) (stepsA stepsBF stepsBB : List
    (RouterStep 24)) (bQPE wOuter wInner2 ko km mLow sUb K : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤
      wInner2)
    (hGiPos : 0 < wInner2) (hs : 1 + kInner ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤
      kInner) (v :
    Var) (pOutFwd pOutBwd P_1 pTurn P_4 : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km
    mLow sUb)) : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  let wNegIn : Wire wInner2 := ⟨0, hGiPos⟩
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  have hdisj : rMain.DisjointWires rScrUb :=
    combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow
    sUb
  let rScr := rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
  have hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wNegIn)
  let rSys116 := (rMain.compose (rSysCatUB wOuter wInner2 11)).compose
    (QRegister.block 0 (2 * 58) (by decide))
  let rRt := lowBitRouter24 hk7 wOuter wInner2 wNegIn rMain rScr hdisjScr
  let L := lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisjScr
  let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wNegIn rMain) (L.rInner ⟨0, by
    omega⟩)
  let sA := liftRouterStepsN rRt stepsA
  let sB1 := liftRouterStepsN rRt stepsBF
  let sB2 := liftRouterStepsN rRt stepsBB
  let uEnt1 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB1)
  let uEnt2 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB2)
  let pPost1 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB1) (routerStepsBwdUnitDyn sA))
  let pPost2 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB2) (routerStepsBwdUnitDyn sA))
  let wDst := rScr ⟨kInner, by omega⟩
  let wTmp := rScr ⟨kInner - 1, by omega⟩
  let pReflIn := reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega) v
  let pHead := DynamicCircuit.seq pOutFwd (.seq P_1 (liftUnitVar v (.seq uEnt1 dSwap)))
  let pMidCore := DynamicCircuit.seq (liftUnitVar v (coreUnitDynF L))
    (.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp) (.seq pPost1 (.seq pTurn
      (.seq (liftUnitVar v uEnt2) (.seq (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst)
        (liftUnitVar v (coreUnitDynB L)))))))
  let pInter := DynamicCircuit.seq pPost2 (.seq P_4 (.seq pOutBwd (.seq pReflIn
    (.seq pOutFwd (.seq P_1 (liftUnitVar v uEnt1))))))
  let pTransBell := DynamicCircuit.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
    (.seq pInter (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst))
  let pTail := DynamicCircuit.seq pMidCore
    (.seq (liftUnitVar v dSwap) (.seq pPost2 (.seq P_4 pOutBwd)))
  .seq pHead (.seq (iterBinDyn (K - 1) (.seq pMidCore pTransBell)) pTail)
/-- Computable (`{Var : Type}`) `wNegIn`-free `K`-step `55`-AND `(160 - d)`-scratch Bell-persistent
super-reflection on `combQubitsAt` (`0 < wInner2`, `0 ≤ d ≤ 10`, `π145` `SiZero` tables). -/
def bellSuperNoNeg2455Dyn {Var : Type} (d : ℕ) (hd : d ≤ 10) (bQPE wOuter wInner2 ko km mLow sUb K :
    ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2) (hs : 160 - d ≤ sUb) (hsIn :
    combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) (pOutFwd pOutBwd P_1 pTurn P_4 :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) : DynamicCircuit Var
    (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  bellSuperNoNeg24GenDyn (by omega)
    (compactStepCoreUnitDyn d hd actFlip145 (orbitalOfPi14555 false) (negMaskPi14555 false))
    (compactStepCoreUnitDyn d hd actFlip145 (orbitalOfPi14555 true) (negMaskPi14555 true))
    stepsA55 stepsBFwd55 stepsBBwd55 bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos
    (by omega) hsIn v pOutFwd pOutBwd P_1 pTurn P_4
theorem count_bellSuperNoNeg24GenDyn_toff {Var : Type} {kInner : ℕ} (hk7 : 7 ≤ kInner)
    {coreUnitDynF coreUnitDynB : ∀ {n : ℕ}, Core145Layout kInner n → DynamicCircuit Unit n} (hToffF
    : ∀ {n : ℕ} (L : Core145Layout kInner n), (coreUnitDynF L).count .TOFF = 0) (hToffB : ∀ {n : ℕ}
    (L : Core145Layout kInner n), (coreUnitDynB L).count .TOFF = 0) (stepsA stepsBF stepsBB : List
    (RouterStep 24)) (bQPE wOuter wInner2 ko km mLow sUb K : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤
      wInner2)
    (hGiPos : 0 < wInner2) (hs : 1 + kInner ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤
      kInner) (v :
    Var) {pOutFwd pOutBwd P_1 pTurn P_4 : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km
    mLow sUb)} (hFwd0 : pOutFwd.count .TOFF = 0) (hBwd0 : pOutBwd.count .TOFF = 0) (h10 : P_1.count
    .TOFF = 0) (hTurn0 : pTurn.count .TOFF = 0) (h40 : P_4.count .TOFF = 0) :
    (bellSuperNoNeg24GenDyn hk7 coreUnitDynF coreUnitDynB stepsA stepsBF stepsBB bQPE wOuter wInner2
      ko km
    mLow sUb K hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4).count .TOFF = 0 := by
  dsimp only [bellSuperNoNeg24GenDyn]
  simp [count_iterBinDyn, count_liftUnitVar, cswapBlockDyn_count_toff, hToffF, hToffB, hFwd0,
    hBwd0, h10, hTurn0, h40]
theorem count_bellSuperNoNeg24GenDyn_t {Var : Type} {kInner tCoreF tCoreB : ℕ} (hk7 : 7 ≤ kInner)
    {coreUnitDynF coreUnitDynB : ∀ {n : ℕ}, Core145Layout kInner n → DynamicCircuit Unit n} (hTF :
    ∀ {n : ℕ} (L : Core145Layout kInner n), (coreUnitDynF L).count .T = tCoreF) (hTB : ∀ {n : ℕ} (L
    : Core145Layout kInner n), (coreUnitDynB L).count .T = tCoreB) (stepsA stepsBF stepsBB : List
    (RouterStep 24)) (bQPE wOuter wInner2 ko km mLow sUb K : ℕ) (hK : 1 ≤ K) (hkOut : ko ≤
      wOuter) (hkMid :
    km ≤ wInner2) (hGiPos : 0 < wInner2) (hs : 1 + kInner ≤ sUb) (hsIn :
      combARem wOuter wInner2 ko km - 2 ≤
    kInner) (v : Var) (pOutFwd pOutBwd P_1 pTurn P_4 : DynamicCircuit Var (combQubitsAt bQPE wOuter
    wInner2 ko km mLow sUb)) : (bellSuperNoNeg24GenDyn hk7 coreUnitDynF coreUnitDynB stepsA stepsBF
    stepsBB bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1
      pTurn
    P_4).count .T = K * (pOutFwd.count .T + P_1.count .T + tCoreF + tCoreB + 464 + 4 * (2 *
    numRouterAnds stepsA + numRouterAnds stepsBF + numRouterAnds stepsBB) + pTurn.count .T +
    P_4.count .T + pOutBwd.count .T) + 232 + (K - 1) * (4 * (combARem wOuter wInner2 ko km -
        2)) := by
  let wNegIn : Wire wInner2 := ⟨0, hGiPos⟩
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  have hdisj : rMain.DisjointWires rScrUb :=
    combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow
    sUb
  let rScr := rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
  have hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
  let rRt := lowBitRouter24 hk7 wOuter wInner2 wNegIn rMain rScr hdisjScr
  have hSw := disjoint_rSwap117LowBit_rInner0 hk7 wOuter wInner2 wNegIn rMain rScr hdisjScr
  have hSys (q : Fin (1 + kInner)) : ((rMain.compose (rSysCatUB wOuter wInner2 11)).compose
      (QRegister.block 0 (2 * 58) (by decide))).DisjointWires (QRegister.singleton (rScr q)) :=
    QRegister.disjoint_iff.mpr fun _ j ↦ by
      fin_cases j
      exact hdisjScr.ne _ q
  have hDstTmp := rScr_kInner_ne_pred (by omega) rScr
  have hA := count_routerStepsFwdBwd_t (liftRouterStepsN rRt stepsA)
  have hB1 := count_routerStepsFwdBwd_t (liftRouterStepsN rRt stepsBF)
  have hB2 := count_routerStepsFwdBwd_t (liftRouterStepsN rRt stepsBB)
  rw [numRouterAnds_liftRouterStepsN] at hA hB1 hB2
  dsimp only [rRt, wNegIn, rScr, rMain, rScrUb] at hSw hSys hDstTmp hA hB1 hB2
  dsimp only [bellSuperNoNeg24GenDyn, wNegIn] at hSw ⊢
  simp only [dyn_count_seq, count_iterBinDyn, count_liftUnitVar, countReflInSliceDyn_t]
  rw [cswapBlockDyn_count_t _ 58 _ _ hSw, hTF, hTB, dBellEntry58Dyn_count_t, dBellExit58Dyn_count_t
    v ((rMain.compose (rPolyCtrl16InCat wOuter wInner2 ⟨0,
      hGiPos⟩)) 14) _ _ _ (hSys _) (hSys _) hDstTmp
    (hdisjScr.ne _ _)]
  let S := pOutFwd.count .T + P_1.count .T + tCoreF + tCoreB + 464 +
    4 * (2 * numRouterAnds stepsA + numRouterAnds stepsBF + numRouterAnds stepsBB) +
    pTurn.count .T + P_4.count .T + pOutBwd.count .T
  let R := 4 * (combARem wOuter wInner2 ko km - 2)
  let cFA := (routerStepsFwdUnitDyn (liftRouterStepsN rRt stepsA)).count .T
  let cBA := (routerStepsBwdUnitDyn (liftRouterStepsN rRt stepsA)).count .T
  let cFF := (routerStepsFwdUnitDyn (liftRouterStepsN rRt stepsBF)).count .T
  let cBF := (routerStepsBwdUnitDyn (liftRouterStepsN rRt stepsBF)).count .T
  let cFB := (routerStepsFwdUnitDyn (liftRouterStepsN rRt stepsBB)).count .T
  let cBB := (routerStepsBwdUnitDyn (liftRouterStepsN rRt stepsBB)).count .T
  change _ + ((K - 1) * _ + _) = K * S + 232 + (K - 1) * R
  have hb' : tCoreF + (232 + ((cBF + cBA) + (pTurn.count .T + ((cFA + cFB) + (0 + tCoreB))))) +
      (232 + (((cBB + cBA) + (P_4.count .T + (pOutBwd.count .T + (R + (pOutFwd.count .T +
      (P_1.count .T + (cFA + cFF))))))) + 0)) = S + R := by
    dsimp only [S, R, cFA, cBA, cFF, cBF, cFB, cBB, rRt, wNegIn, rScr, rMain, rScrUb]
    omega
  have hht' : (pOutFwd.count .T + (P_1.count .T + ((cFA + cFF) + 232))) + ((tCoreF + (232 + ((cBF +
      cBA) + (pTurn.count .T + ((cFA + cFB) + (0 + tCoreB)))))) + (232 + ((cBB + cBA) + (P_4.count
      .T + pOutBwd.count .T)))) = S + 232 := by
    dsimp only [S, cFA, cBA, cFF, cBF, cFB, cBB, rRt, wNegIn, rScr, rMain, rScrUb]
    omega
  dsimp only [cFA, cBA, cFF, cBF, cFB, cBB, rRt, wNegIn, rScr, rMain, rScrUb] at hb' hht'
  rw [hb', Nat.add_comm ((K - 1) * (S + R)), ← Nat.add_assoc, hht']
  have hK1 : 1 + (K - 1) = K := by omega
  calc (S + 232) + (K - 1) * (S + R)
      = (1 + (K - 1)) * S + 232 + (K - 1) * R := by ring
    _ = K * S + 232 + (K - 1) * R := by rw [hK1]
theorem count_bellSuperNoNeg2455Dyn_toff {Var : Type} (d : ℕ) (hd : d ≤
    10) (bQPE wOuter wInner2 ko km
    mLow sUb K : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2) (hs : 160 -
      d ≤ sUb)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v : Var) {pOutFwd pOutBwd P_1 pTurn P_4 :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)} (hFwd0 :
      pOutFwd.count .TOFF =
    0) (hBwd0 : pOutBwd.count .TOFF = 0) (h10 : P_1.count .TOFF = 0) (hTurn0 : pTurn.count .TOFF =
    0) (h40 : P_4.count .TOFF = 0) :
      (bellSuperNoNeg2455Dyn d hd bQPE wOuter wInner2 ko km mLow sUb K
    hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4).count .TOFF = 0 :=
  count_bellSuperNoNeg24GenDyn_toff (by omega) (compactCore145Bundle d hd false).toGen.count_toff
    (compactCore145Bundle d hd true).toGen.count_toff stepsA55 stepsBFwd55 stepsBBwd55 bQPE
    wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos (by omega) hsIn v hFwd0 hBwd0 h10 hTurn0 h40
theorem count_bellSuperNoNeg2455Dyn_t {Var : Type} (d : ℕ) (hd : d ≤ 10) (bQPE wOuter wInner2 ko km
    mLow sUb K : ℕ) (hK : 1 ≤ K) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos :
      0 < wInner2) (hs : 160
    - d ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v :
      Var) (pOutFwd pOutBwd P_1 pTurn
    P_4 : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :
    (bellSuperNoNeg2455Dyn d hd bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn v
    pOutFwd pOutBwd P_1 pTurn P_4).count .T = K * (pOutFwd.count .T + P_1.count .T +
    compactBellSuperStep55TCount d + pTurn.count .T + P_4.count .T + pOutBwd.count .T) + 232 + (K -
    1) * (4 * (combARem wOuter wInner2 ko km - 2)) := by
  rw [bellSuperNoNeg2455Dyn]
  refine (count_bellSuperNoNeg24GenDyn_t (by omega)
    (compactCore145Bundle d hd false).toGen.count_t (compactCore145Bundle d hd true).toGen.count_t
    stepsA55 stepsBFwd55 stepsBBwd55 bQPE wOuter wInner2 ko km mLow sUb K hK hkOut hkMid hGiPos
    (by omega) hsIn v pOutFwd pOutBwd P_1 pTurn P_4).trans ?_
  rw [numRouterAndsStepsA55, numRouterAndsStepsB55, numRouterAndsStepsB55]
  have hc := compactBellSuperStep55TCount_eq_core d
  refine congrArg (fun x ↦ x + 232 + (K - 1) * (4 * (combARem wOuter wInner2 ko km - 2)))
    (congrArg (K * ·) ?_)
  omega
theorem cleanWalkRefl2At_bellSuperNoNeg24GenDyn_asym {Var : Type} [Fintype Var] [DecidableEq Var]
    {kInner tCoreF tCoreB : ℕ} (hk8 : 8 ≤ kInner)
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF) (bundleB :
      GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 24)) (specA : (Fin 16 → Bool) → State24)
    (specBF specBB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 le_rfl stepsA (initState23 x16) = some (specA x16))
    (hRunBF : ∀ x16, runSteps24 le_rfl stepsBF (specA x16) = some (specBF (specA x16)))
    (hBorBF : ∀ x16 (k : Fin 7), (specBF (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145F : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specBF (specA x16))) < 145)
    (hRunBB : ∀ x16, runSteps24 le_rfl stepsBB (specA x16) = some (specBB (specA x16)))
    (hBorBB : ∀ x16 (k : Fin 7), (specBB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145B : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specBB (specA x16))) < 145)
    {bQPE wOuter wInner2 ko km mLow sUb : ℕ} (K : ℕ) (hK : 1 ≤ K) {hkOut : ko ≤ wOuter} {hkMid :
      km ≤ wInner2}
    (hGiPos : 0 < wInner2) (hs : 1 + kInner ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤
      kInner)
    {v : Var} {prepOutImpl : Unitary (2 ^ mOutUB wOuter)} {M_fwd M_bwd :
      Unitary (2 ^ nUB wOuter wInner2)}
    {raw_4 raw_3 sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (legs :
      BellAsymLegs Var bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v prepOutImpl M_fwd M_bwd
      raw_4 raw_3 sF sB pOutFwd pOutBwd P_1 pTurn P_4)
    (hs1 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_4)
      (selectLowBit24NoNegCoreSliceDyn
        (by omega) bundleF.coreUnitDyn stepsA stepsBF hs v wOuter wInner2
        hGiPos (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hs2 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_3)
      (selectLowBit24NoNegCoreSliceDyn
        (by omega) bundleB.coreUnitDyn stepsA stepsBB hs v wOuter wInner2
        hGiPos (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hTurnSupp :
      Disjoint pTurn.support (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb kInner hs))
    (hInterSupp : 2 ≤ K → Disjoint (P_1.support ∪ P_4.support ∪ pOutFwd.support ∪ pOutBwd.support)
      (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb kInner hs)) :
    let uRefl2 := reflPulledPair (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
      (ubCustomMuxCatUnitary M_fwd prepOutImpl sF) (ubCustomMuxCatUnitary M_bwd prepOutImpl sB⁻¹)⁻¹
    let R₀ := reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    CleanWalkRefl2At bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v (uRefl2 * (R₀ * uRefl2) ^ (K -
      1))
      (bellSuperNoNeg24GenDyn (by omega) bundleF.coreUnitDyn bundleB.coreUnitDyn stepsA stepsBF
        stepsBB
        bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn
        P_4) := by
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
  let rAncZ :=
    liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2) (outZeroPrefixReg wOuter ko hkOut)
    (midZeroPrefixReg wInner2 km hkMid)
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
  have hSubClean : rScrUb.image ⊆ rClean.image := by
    rw [hCleanImg]
    exact Finset.subset_union_left
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
    selectLowBit24NoNegCoreSliceDyn (by omega) bundleF.coreUnitDyn stepsA stepsBF hs v wOuter
    wInner2 hGiPos rMain rScrUb
  let selB :=
    selectLowBit24NoNegCoreSliceDyn (by omega) bundleB.coreUnitDyn stepsA stepsBB hs v wOuter
    wInner2 hGiPos rMain rScrUb
  let P_single_cswap : DynamicCircuit Var N := outerSeqWrapDyn pOutFwd
    (.seq P_1 (.seq (.seq selF (.seq pTurn selB)) P_4)) pOutBwd
  let pReflIn := reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega) v
  let R_mid := reflMidUnitary (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
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
  have hInnerCSwap := cleanRealizesSet_congr_set hCleanImg
    (cleanRealizesSet_fiveStepCSwap_asym rMain rScrUb rClean hSubClean
      (rUB.embedUnitary M_1_pre) (rUB.embedUnitary M_1_post) (rUB.embedUnitary M_2_pre)
      (rUB.embedUnitary M_2_post) (rMain.embedUnitary raw_4) (rMain.embedUnitary raw_3) u_in1
      u_in2 R_mid h1 hs1 (cleanTurnaroundWp_congr hCleanImg rfl rfl hTurn) hs2
      (cleanUnloadsWp_congr hCleanImg rfl h4) hW2_sel hPull1 hPull2
      (preservesWires_congr_set hCleanImg.symm hPres1) hPresR
      (preservesWires_congr_set hCleanImg.symm hPres2))
  have hSingleCSwap : CleanRealizesSet v S_full (rMain.embedUnitary uRefl2) P_single_cswap := by
    have hS := outerSandwich_cleanRealizesSet hkOut hkMid hFwd hBwd hConj _ _ hInnerCSwap hPresAll
    rwa [outerSandwich_eq_reflPulledPair_customMux rMain] at hS
  have hR0Set : CleanRealizesSet v S_full (rMain.embedUnitary R₀) pReflIn :=
    cleanRealizesSetReflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega) v
  have H_step := hSingleCSwap.seq hR0Set
  have hDisjOut := combOutRegB_disjoint_scr_midZero bQPE wOuter wInner2 ko km mLow sUb hkMid
  have hPresRefl2 : PreservesWires (rMain.embedUnitary uRefl2).1 S_full := by
    have hp : PreservesWires (((rOut.embedUnitary prepOutImpl)⁻¹ *
        rMain.embedUnitary (innerMidCoreUnitary M_fwd M_bwd sF sB) *
        rOut.embedUnitary prepOutImpl).1) S_full := hConj rOut S_ext hDisjOut hPresAll
    rwa [congrArg Subtype.val (outerSandwich_eq_reflPulledPair_customMux rMain M_fwd M_bwd
      prepOutImpl sF sB)] at hp
  have hPresSuper (m : ℕ) : PreservesWires (rMain.embedUnitary (uRefl2 * (R₀ * uRefl2) ^ m)).1
      S_full := by
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
  let rRt := lowBitRouter24 (by omega) wOuter wInner2 wNegIn rMain rScr hdisjScr
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
    (.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp) (.seq pPost1 (.seq pTurn
      (.seq (liftUnitVar v uEnt2) (.seq (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst)
        (liftUnitVar v (bundleB.coreUnitDyn L)))))))
  let pRest2 := DynamicCircuit.seq P_4 (.seq pOutBwd (.seq pReflIn
    (.seq pOutFwd (.seq P_1 (liftUnitVar v uEnt1)))))
  let pInter := DynamicCircuit.seq pPost2 pRest2
  let pTransBell := DynamicCircuit.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
    (.seq pInter (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst))
  let pTail := DynamicCircuit.seq pMidCore
    (.seq (liftUnitVar v dSwap) (.seq pPost2 (.seq P_4 pOutBwd)))
  have hInnerEq :=
    (lowBitCoreLayout_wires24 (by omega) wOuter wInner2 wNegIn rMain rScr hdisjScr).2.2.1
  have hSysRt24 := lowBit_disj_sysCat_router24 (by omega) wOuter wInner2 wNegIn rMain rScr hdisjScr
  have hPool := disjoint_rSwap117_rInner (by omega) wOuter wInner2 wNegIn rMain rScr hdisjScr
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
  have hSwapValid : DiagProjSimulates (ketPredProj (sValidCore L))
      (rSwap117.embedUnitary USwapLoc) dSwap :=
    diagProjSimulates_dSwap24_valid (by omega) wOuter wInner2 wNegIn rMain rScr hdisjScr
  have hPValIn : zeroProjOn L.rInner.image * ketPredProj (sValidCore L) = ketPredProj (sValidCore
      L) := by
    rw [← basisOutcomeProjector_zero_eq_zeroProjOn, basisOutcomeProjector_zero_eq_ketPredProj]
    exact (IsDiagProj.comm ⟨_, rfl⟩ ⟨sValidCore L, rfl⟩).trans
      (ketPredProj_mul_of_imp fun _ h ↦ h.2)
  obtain ⟨U_e1, hSimEnt1, hMapEnt1⟩ := simulatesOnProj_noNeg24CoreSliceEntry (by omega) stepsA
    stepsBF specA specBF hRunA hRunBF hBorBF h145F wOuter wInner2 wNegIn rMain rScr hdisjScr
  obtain ⟨U_e2, hSimEnt2, hMapEnt2⟩ := simulatesOnProj_noNeg24CoreSliceEntry (by omega) stepsA
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
      (_ * U_e1).1 * zeroProjOn rScr.image := proj_map_mul hMapEnt1 (by
    rw [Matrix.mul_assoc, hdBody1.2.1, ← Matrix.mul_assoc, hPValIn, ← hdBody1.2.1])
  have hMapPre2' : zeroProjOn L.rInner.image * (_ * U_e2).1 * zeroProjOn rScr.image =
      (_ * U_e2).1 * zeroProjOn rScr.image := proj_map_mul hMapEnt2 (by
    rw [Matrix.mul_assoc, hdBody2.2.1, ← Matrix.mul_assoc, hPValIn, ← hdBody2.2.1])
  have hToIn {U : Unitary (2 ^ N)} (hM : ketPredProj (sValidCore L) * U.1 * zeroProjOn rScr.image =
      U.1 * zeroProjOn rScr.image) : zeroProjOn L.rInner.image * U.1 * zeroProjOn rScr.image = U.1
      * zeroProjOn rScr.image := by
    rw [Matrix.mul_assoc, ← hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc (zeroProjOn _), hPValIn, hM]
  have hInMem (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ kInner) : rScr ⟨m, by omega⟩ ∈ L.rInner.image :=
    (QRegister.mem_image _ _).mpr ⟨⟨m - 1, by omega⟩, by
      rw [hInnerEq]
      refine congrArg rScr (Fin.ext ?_)
      dsimp
      omega⟩
  have hNotS : rCtrl16 14 ∉ L.rInner.image := fun hm ↦ by
    obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hm
    rw [hInnerEq] at hj
    exact hdisjScr.ne _ _ hj.symm
  have hSysDisjS : Disjoint rSys116.image L.rInner.image := Finset.disjoint_left.mpr fun _ hw1 hw2 ↦
    by
      obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hw1
      obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hw2
      rw [hInnerEq] at hj
      exact hdisjScr.ne _ _ hj.symm
  have hDstTmp : wDst ≠ wTmp := rScr_kInner_ne_pred (by omega) rScr
  have hDst2 : rCtrl16 14 ≠ wDst := hdisjScr.ne _ _
  have hwDstEq : wDst = rScrUb ⟨kInner, by omega⟩ := congrArg rScrUb (Fin.ext (Nat.zero_add _))
  have hRtDisj : Disjoint rRt.image (rSys116.image ∪ {wDst}) := Finset.disjoint_left.mpr
    fun _ hw hU ↦ by
      obtain ⟨u, rfl⟩ := (QRegister.mem_image rRt _).mp hw
      rcases Finset.mem_union.mp hU with hS | hD
      · obtain ⟨_, hk⟩ := (QRegister.mem_image rSys116 _).mp hS
        exact hSysRt24.ne _ u hk
      · have huLt := u.isLt
        rw [Finset.mem_singleton, lowBitRouter24_apply] at hD
        split_ifs at hD
        · refine absurd (congrArg Fin.val (rScr.wires.injective hD)) ?_
          dsimp
          omega
        · exact hdisjScr.ne _ _ hD
        · refine absurd (congrArg Fin.val (rScr.wires.injective hD)) ?_
          dsimp
          omega
  have hSubRt (st : List (RouterStep 24)) := support_routerStepsFwdBwd_subset
    (liftRouterStepsN rRt st) (touchesIn_liftRouterStepsN rRt _
      (fun u ↦ (QRegister.mem_image rRt _).mpr ⟨u, rfl⟩) st)
  let pRest1 := DynamicCircuit.seq pTurn (liftUnitVar v uEnt2)
  let pMid1 := DynamicCircuit.seq pPost1 pRest1
  have hMid1Disj : Disjoint pMid1.support (rSys116.image ∪ {wDst}) := by
    have hTurnDst : Disjoint pTurn.support (rSys116.image ∪ {wDst}) := by rwa [hwDstEq]
    simp only [pMid1, pRest1, pPost1, uEnt2, DynamicCircuit.support_seq, support_liftUnitVar]
    exact Finset.disjoint_union_left.mpr ⟨hRtDisj.mono_left (Finset.union_subset (hSubRt _).2
      (hSubRt _).2), Finset.disjoint_union_left.mpr ⟨hTurnDst, hRtDisj.mono_left
      (Finset.union_subset (hSubRt _).1 (hSubRt _).1)⟩⟩
  have hSys (m : Fin (1 + kInner)) : rSys116.DisjointWires (QRegister.singleton (rScr m)) :=
    QRegister.disjoint_iff.mpr fun _ j ↦ by
      fin_cases j
      exact hdisjScr.ne _ m
  have hExV : PreservesVInv v (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp) :=
    (cleanRealizesSet_dBellExit58Dyn (Var := Var) v (rCtrl16 14) rSys116 wDst wTmp (hSys _)
      (hSys _) hDstTmp (hdisjScr.ne _ _) (hdisjScr.ne _ _)).2.1
  have hEnV : PreservesVInv v (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst) :=
    fun Θ _ ↦ wp_dBellEntry58Dyn_update_self v (rCtrl16 14) rSys116 wDst hDst2 Θ
  have hPostVOf (stB : List (RouterStep 24)) : PreservesVInv v
      (liftUnitVar v (.seq (routerStepsBwdUnitDyn (liftRouterStepsN rRt stB))
        (routerStepsBwdUnitDyn sA))) :=
    ((ConstWp.routerStepsFwdBwd (liftRouterStepsN rRt stB)).2.seq
      (ConstWp.routerStepsFwdBwd sA).2).preservesVInv v
  have hPost1V : PreservesVInv v pPost1 := hPostVOf stepsBF
  have hPost2V : PreservesVInv v pPost2 := hPostVOf stepsBB
  have hEnt1V : PreservesVInv v (liftUnitVar v uEnt1) := hSimEnt1.1.preservesVInv v
  have hEnt2V : PreservesVInv v (liftUnitVar v uEnt2) := hSimEnt2.1.preservesVInv v
  have hSwV : PreservesVInv v (liftUnitVar v dSwap) := hSimSw0.1.preservesVInv v
  have hC1V := (SimulatesOnProj.ofDiagProj hSimC1).1.preservesVInv v
  have hC2V := (SimulatesOnProj.ofDiagProj hSimC2).1.preservesVInv v
  have hRest1V := preservesVInv_seq hTurn.2.1 hEnt2V
  have hRest2V := preservesVInv_seq h4.2.1 (preservesVInv_seq hBwd.2.1 (preservesVInv_seq
    hR0Set.2.1 (preservesVInv_seq hFwdSet.2.1 (preservesVInv_seq h1.2.1 hEnt1V))))
  have hHeadV := preservesVInv_seq hFwdSet.2.1 (preservesVInv_seq h1.2.1
    ((hSimEnt1.1.seq hSimSw0.1).preservesVInv v))
  have hMidCoreV := preservesVInv_seq hC1V (preservesVInv_seq hExV (preservesVInv_seq hPost1V
    (preservesVInv_seq hTurn.2.1 (preservesVInv_seq hEnt2V (preservesVInv_seq hEnV hC2V)))))
  have hTransV := preservesVInv_seq hExV (preservesVInv_seq
    (preservesVInv_seq hPost2V hRest2V) hEnV)
  have hTailV := preservesVInv_seq hMidCoreV (preservesVInv_seq hSwV
    (preservesVInv_seq hPost2V (preservesVInv_seq h4.2.1 hBwd.2.1)))
  have hcWoutExt : (rOut.embedUnitary prepOutImpl).1 * zeroProjOn S_ext =
      zeroProjOn S_ext * (rOut.embedUnitary prepOutImpl).1 := preservesWires_comm_zeroProjOn
    (preservesWires_embedMatrix_of_disjoint rOut prepOutImpl.1 S_ext hDisjOut) Finset.Subset.rfl
  have hPrefixCongr {X₁ X₂ : QCAssertion Var (2 ^ N)} (hX1 : ∀ σ val, X₁ (Function.update σ v val)
      = X₁ σ) (hX2 : ∀ σ val, X₂ (Function.update σ v val) = X₂ σ) (hEqScr :
      SelectSwapQROM.restrictZeroSet X₁ rScrUb.image = SelectSwapQROM.restrictZeroSet X₂
      rScrUb.image) : SelectSwapQROM.restrictZeroSet (wp pOutFwd.compile (wp P_1.compile (wp
      selF.compile (wp pTurn.compile X₁)))) S_full = SelectSwapQROM.restrictZeroSet (wp
      pOutFwd.compile (wp P_1.compile (wp selF.compile (wp pTurn.compile X₂)))) S_full := by
    have hInEq := restrictZeroSet_wp_threeStepPrefix_congr
      (Finset.subset_union_left : rScrUb.image ⊆ S_ext) h1 hs1 hTurn hW2_sel hPull1 hPres1
      (preservesWires_congr_set hCleanImg hPresR) hX1 hX2 hEqScr
    have hA1V := h1.2.1 _ (hs1.2.1 _ (hTurn.2.1 X₁ hX1))
    have hA2V := h1.2.1 _ (hs1.2.1 _ (hTurn.2.1 X₂ hX2))
    refine restrictZeroSet_eq_of_subset Finset.subset_union_left ?_
    rw [restrictZeroSet_eq_of_subset Finset.subset_union_left (hFwdSet.2.2.1 _ hA1V),
      restrictZeroSet_qcWpQAssign_comm hcWoutExt, hInEq, ← restrictZeroSet_qcWpQAssign_comm
      hcWoutExt, ← restrictZeroSet_eq_of_subset Finset.subset_union_left (hFwdSet.2.2.1 _ hA2V)]
  have hEntSw {uEnt : DynamicCircuit Unit N} {U_e : Unitary (2 ^ N)} (hSimE : SimulatesOnProj
      (zeroProjOn rScr.image) U_e uEnt) (hMapE : zeroProjOn L.rInner.image * U_e.1 * zeroProjOn
      rScr.image = U_e.1 * zeroProjOn rScr.image) (Ξ : QCAssertion Var (2 ^ N)) (hΞ : ∀ σ val, Ξ
      (Function.update σ v val) = Ξ σ) : SelectSwapQROM.restrictZeroSet (wp (liftUnitVar v
      uEnt).compile (wp (DynamicCircuit.circuit cSw).compile Ξ)) rScr.image =
      SelectSwapQROM.restrictZeroSet (wp (liftUnitVar v (.seq uEnt dSwap)).compile Ξ) rScr.image
      := by
    have hSwΞ : ∀ σ val, wp (DynamicCircuit.circuit cSw).compile Ξ (Function.update σ v val) =
        wp (DynamicCircuit.circuit cSw).compile Ξ σ := fun σ val ↦ by
      simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign,
        hΞ σ val]
    rw [hSimE.restrictZeroSet_eq v hMapE _ hSwΞ, ← hSimSw0.restrictZeroSet_eq_circuit v Ξ hΞ, ←
      hSimE.restrictZeroSet_eq v hMapE _ (hSwV Ξ hΞ), liftUnitVar_seq, wp_seq_compile]
  have hBellSplice {tC : ℕ} {br : Fin (2 ^ 10) → Unitary (2 ^ 58)}
      (bundleSpec : GenCore145Bundle kInner tC br) (stB : List (RouterStep 24)) {U_p :
        Unitary (2 ^ N)}
      (hSimP : SimulatesOnProj (zeroProjOn rScr.image) U_p
        (.seq (.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn (liftRouterStepsN rRt stB)))
          (.seq dSwap (bundleSpec.coreUnitDyn L))))
      (hMapP : zeroProjOn L.rInner.image * U_p.1 * zeroProjOn rScr.image =
        U_p.1 * zeroProjOn rScr.image)
      (pRest : DynamicCircuit Var N) (hRestV : PreservesVInv v pRest)
      (hDisjB : Disjoint (DynamicCircuit.seq (liftUnitVar v
        (.seq (routerStepsBwdUnitDyn (liftRouterStepsN rRt stB)) (routerStepsBwdUnitDyn sA)))
        pRest).support (rSys116.image ∪ {wDst}))
      (Ξ : QCAssertion Var (2 ^ N)) (hΞ : ∀ σ val, Ξ (Function.update σ v val) = Ξ σ) :
      let sBi := liftRouterStepsN rRt stB
      let uEnt := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sBi)
      let pPost := liftUnitVar v (.seq (routerStepsBwdUnitDyn sBi) (routerStepsBwdUnitDyn sA))
      let pBell := DynamicCircuit.seq (dBellExit58Dyn v (rCtrl16 14) rSys116 wDst wTmp)
        (.seq (.seq pPost pRest) (dBellEntry58Dyn v (rCtrl16 14) rSys116 wDst))
      SelectSwapQROM.restrictZeroSet
        (wp (liftUnitVar v (.seq uEnt (.seq dSwap (bundleSpec.coreUnitDyn L)))).compile
          (wp pBell.compile Ξ)) rScr.image =
      SelectSwapQROM.restrictZeroSet
        (wp (selectLowBit24NoNegCoreSliceDyn
          (by omega) bundleSpec.coreUnitDyn stepsA stB hs v wOuter wInner2
          hGiPos rMain rScrUb).compile
          (wp pRest.compile (wp (DynamicCircuit.circuit cSw).compile Ξ))) rScr.image := by
    intro sBi uEnt pPost pBell
    have hPostV : PreservesVInv v pPost := hPostVOf stB
    have hBodyV := preservesVInv_seq hPostV hRestV
    have hBellV := preservesVInv_seq hExV (preservesVInv_seq hBodyV hEnV) Ξ hΞ
    have hSim := hSimP.restrictZeroSet_eq v hMapP (wp pBell.compile Ξ) hBellV
    have hSand := restrictZeroSet_wp_bellSandwich58_eq_cswapCircuit v (rCtrl16 14) (rCtrl16 14)
      rSys116 wDst wTmp L.rInner.image (hInMem kInner (by omega) le_rfl)
      (hInMem (kInner - 1) (by omega) (by omega)) hNotS hSysDisjS hDstTmp hSys2 hSys2 hDst2
      (.seq pPost pRest) hDisjB hBodyV Ξ hΞ
    dsimp only at hSand
    have hBodySw : wp (DynamicCircuit.seq (.circuit cSw) (.seq (.seq pPost pRest) (.circuit
        cSw))).compile Ξ = wp (DynamicCircuit.circuit cSw).compile (wp pPost.compile (wp
        pRest.compile (wp (DynamicCircuit.circuit cSw).compile Ξ))) := by
      simp only [wp_seq_compile]
    rw [hrSwapEq, hBodySw] at hSand
    have hPW := hPostV _ (hRestV (wp (DynamicCircuit.circuit cSw).compile Ξ) fun σ val ↦ by
      simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile, qcWpQAssign,
        hΞ σ val])
    dsimp only [pBell, uEnt, sA, sBi, dSwap, L, rRt, rScr, hdisjScr] at hSim hSand ⊢
    rw [hSim, hSand, ← hSimSw0.restrictZeroSet_eq_circuit v _ hPW,
      ← hSimP.restrictZeroSet_eq v hMapP _ (hSwV _ hPW),
      wp_selectLowBit24NoNegCoreSliceDyn
        (by omega) bundleSpec stepsA stB hs v wOuter wInner2 hGiPos rMain
        rScrUb hdisj]
    dsimp only [pPost, sA, sBi, dSwap, rSwap117, rRt, wNegIn, L, rScr]
    conv_lhs => simp only [liftUnitVar_seq, wp_seq_compile]
    conv_rhs => simp only [liftUnitVar_seq, wp_seq_compile]
  have hcTarget := preservesWires_comm_zeroProjOn (hPresSuper (K - 1)) Finset.Subset.rfl
  have hCR : Solution.XMeasCircuit.CleanRealizes v (QRegister.whole N) rUbZero (rMain.embedUnitary
    (uRefl2 *
      (R₀ * uRefl2) ^ (K - 1))) (bellSuperNoNeg24GenDyn (by omega) bundleF.coreUnitDyn
      bundleB.coreUnitDyn stepsA stepsBF stepsBB bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid
        hGiPos hs
      hsIn v pOutFwd pOutBwd P_1 pTurn P_4) := by
    refine Solution.XMeasCircuit.CleanRealizes.mkOfWpClean
      (count_bellSuperNoNeg24GenDyn_toff
        (by omega) bundleF.count_toff bundleB.count_toff stepsA stepsBF
        stepsBB bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn v hFwdSet.1 hBwd.1
          h1.1
        hTurn.1 h4.1)
      (fun Θ hΘ ↦ preservesVInv_seq hHeadV (preservesVInv_seq (preservesVInv_iterBinDyn (K - 1)
        (preservesVInv_seq hMidCoreV hTransV)) hTailV) Θ hΘ) (fun Θ hΘ ↦ ?_) ?_
    · rw [SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet,
        SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet,
        QRegister.whole_embedUnitary, hUbImg]
      dsimp only [bellSuperNoNeg24GenDyn]
      simp only [wp_seq_compile, wp_iterBinDyn_compile]
      let B_bell_of (Ψ : QCAssertion Var (2 ^ N)) : QCAssertion Var (2 ^ N) :=
        wp (DynamicCircuit.seq (liftUnitVar v uEnt2) (.circuit cSw)).compile
          (wp (liftUnitVar v (bundleB.coreUnitDyn L)).compile Ψ)
      have hBbellV (Ψ : QCAssertion Var (2 ^ N))
          (hΨV : ∀ σ val, Ψ (Function.update σ v val) = Ψ σ) :
          ∀ σ val, B_bell_of Ψ (Function.update σ v val) = B_bell_of Ψ σ := fun σ val ↦ by
        dsimp only [B_bell_of]
        rw [wp_seq_compile]
        exact hEnt2V _ (fun σ' val' ↦ by
          simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile,
            qcWpQAssign, hC2V Ψ hΨV σ' val']) σ val
      have hHeadA_gen (Ψ : QCAssertion Var (2 ^ N)) (hΨV : ∀ σ val, Ψ (Function.update σ v val) = Ψ
          σ) : SelectSwapQROM.restrictZeroSet (wp pHead.compile (wp pMidCore.compile Ψ)) S_full =
          SelectSwapQROM.restrictZeroSet (wp pOutFwd.compile (wp P_1.compile (wp selF.compile (wp
          pTurn.compile (B_bell_of Ψ))))) S_full := by
        have hSp := hBellSplice bundleF stepsBF hSimPre1 hMapPre1 pRest1 hRest1V hMid1Disj
          (wp (liftUnitVar v (bundleB.coreUnitDyn L)).compile Ψ) (hC2V Ψ hΨV)
        dsimp only at hSp
        have hStepA : SelectSwapQROM.restrictZeroSet
            (wp (liftUnitVar v (.seq uEnt1 dSwap)).compile (wp pMidCore.compile Ψ)) rScrUb.image =
          SelectSwapQROM.restrictZeroSet
            (wp selF.compile (wp pTurn.compile (B_bell_of Ψ))) rScrUb.image := hLiftScr
          (Eq.trans (congrArg (SelectSwapQROM.restrictZeroSet · rScr.image) (by
            dsimp only [pMidCore, pRest1, uEnt1, pPost1, sB1]
            simp only [liftUnitVar_seq, wp_seq_compile]))
            (hSp.trans (congrArg (fun X ↦ SelectSwapQROM.restrictZeroSet (wp selF.compile X)
              rScr.image) (by
                dsimp only [pRest1, B_bell_of]
                simp only [wp_seq_compile]))))
        dsimp only [pHead]
        simp only [wp_seq_compile]
        refine restrictZeroSet_eq_of_subset hSubScrFull ?_
        rw [← wp_seq_compile pOutFwd P_1, ← wp_seq_compile pOutFwd P_1, ← (hFwdSet.seq h1).2.2.2,
          hStepA, (hFwdSet.seq h1).2.2.2]
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
        let Z_0 := wp P_4.compile (wp pOutBwd.compile Θ)
        have hZ0V := h4.2.1 _ (hBwd.2.1 Θ hΘ)
        let Ψ_0 := wp (liftUnitVar v dSwap).compile (wp pPost2.compile Z_0)
        have hΨ0V := hSwV _ (hPost2V Z_0 hZ0V)
        have hΦ0 : Φ 0 = wp pMidCore.compile Ψ_0 := by
          dsimp only [Φ, pTail, Ψ_0, Z_0, Function.iterate_zero, id_eq]
          simp only [wp_seq_compile]
        have hStepB0 : SelectSwapQROM.restrictZeroSet (B_bell_of Ψ_0) rScrUb.image =
            SelectSwapQROM.restrictZeroSet (wp selB.compile Z_0) rScrUb.image := by
          apply hLiftScr
          dsimp only [B_bell_of]
          rw [wp_seq_compile, hEntSw hSimEnt2 (hToIn hMapEnt2) _ (hC2V Ψ_0 hΨ0V)]
          dsimp only [selB]
          rw [wp_selectLowBit24NoNegCoreSliceDyn
            (by omega) bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos
            rMain rScrUb hdisj Z_0]
          dsimp only [Ψ_0, pPost2, uEnt2, sA, sB2, dSwap, rSwap117, rRt, wNegIn, L, rScr]
          conv_lhs => simp only [liftUnitVar_seq, wp_seq_compile]
          conv_rhs => simp only [liftUnitVar_seq, wp_seq_compile]
        have hCSw0 : wp pOutFwd.compile (wp P_1.compile (wp selF.compile (wp pTurn.compile (wp
            selB.compile Z_0)))) = wp P_single_cswap.compile Θ := by
          dsimp only [P_single_cswap, outerSeqWrapDyn, Z_0]
          simp only [wp_seq_compile]
        rw [hΦ0, hHeadA_gen Ψ_0 hΨ0V, hPrefixCongr (hBbellV Ψ_0 hΨ0V) (hs2.2.1 Z_0 hZ0V) hStepB0,
          hCSw0, _root_.pow_zero, mul_one]
        exact hSingleCSwap.2.2.1 Θ hΘ
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
          simp only [pInter, pRest2, pPost2, uEnt1, DynamicCircuit.support_seq,
            support_liftUnitVar, Finset.disjoint_union_left]
          exact ⟨⟨hRtDisj.mono_left (hSubRt _).2, hRtDisj.mono_left (hSubRt _).2⟩, hIS.1.1.2,
            hIS.2, hReflDst, hIS.1.2, hIS.1.1.1, hRtDisj.mono_left (hSubRt _).1,
            hRtDisj.mono_left (hSubRt _).1⟩
        let Ψ_k := wp pTransBell.compile (Φ k)
        have hΨkV := hTransV (Φ k) (hΦV k)
        have hSucc : Φ (k + 1) = wp pMidCore.compile Ψ_k := by
          dsimp only [Φ, Ψ_k]
          simp only [Function.iterate_succ_apply', wp_seq_compile]
        let Y_csw := wp pOutFwd.compile (wp P_1.compile
          (wp (liftUnitVar v uEnt1).compile (wp (DynamicCircuit.circuit cSw).compile (Φ k))))
        let Z_csw := wp P_4.compile (wp pOutBwd.compile (wp pReflIn.compile Y_csw))
        have hYcswV : ∀ σ val, Y_csw (Function.update σ v val) = Y_csw σ :=
          hFwdSet.2.1 _ (h1.2.1 _ (hEnt1V _ (fun σ val ↦ by
            simp only [DynamicCircuit.compile_circuit, DynamicCircuit.qc_wp_circuit_compile,
              qcWpQAssign, hΦV k σ val])))
        have hZcswV := h4.2.1 _ (hBwd.2.1 _ (hR0Set.2.1 Y_csw hYcswV))
        have hSp2 := hBellSplice bundleB stepsBB hSimPre2 hMapPre2' pRest2 hRest2V hInterDisj (Φ k)
          (hΦV k)
        dsimp only at hSp2
        have hStepB : SelectSwapQROM.restrictZeroSet (B_bell_of Ψ_k) rScrUb.image =
            SelectSwapQROM.restrictZeroSet (wp selB.compile Z_csw) rScrUb.image := by
          apply hLiftScr
          dsimp only [B_bell_of]
          rw [wp_seq_compile, hEntSw hSimEnt2 (hToIn hMapEnt2) _ (hC2V Ψ_k hΨkV)]
          exact Eq.trans (congrArg (SelectSwapQROM.restrictZeroSet · rScr.image) (by
            dsimp only [uEnt2, sA, sB2, rRt, Ψ_k, pTransBell, pInter, pPost2]
            simp only [liftUnitVar_seq, wp_seq_compile]))
            (hSp2.trans (congrArg (fun X ↦ SelectSwapQROM.restrictZeroSet (wp selB.compile X)
              rScr.image) (by
                dsimp only [pRest2, Z_csw, Y_csw]
                simp only [wp_seq_compile])))
        have hReassocStep : wp pOutFwd.compile (wp P_1.compile (wp selF.compile (wp pTurn.compile
            (wp selB.compile Z_csw)))) = wp (DynamicCircuit.seq P_single_cswap pReflIn).compile
            Y_csw := by
          dsimp only [P_single_cswap, outerSeqWrapDyn, Z_csw]
          simp only [wp_seq_compile]
        have hY_eq : SelectSwapQROM.restrictZeroSet Y_csw S_full =
            SelectSwapQROM.restrictZeroSet (qcWpQAssign (rMain.embedUnitary (uRefl2 * (R₀ *
            uRefl2) ^ k)) Θ) S_full := by
          refine (restrictZeroSet_eq_of_subset hSubScrFull ?_).trans (ih (by omega))
          dsimp only [Y_csw, pHead]
          simp only [wp_seq_compile]
          rw [← wp_seq_compile pOutFwd P_1, ← wp_seq_compile pOutFwd P_1, ← (hFwdSet.seq h1).2.2.2,
            hLiftScr (hEntSw hSimEnt1 (hToIn hMapEnt1) (Φ k) (hΦV k)), (hFwdSet.seq h1).2.2.2]
        rw [hSucc, hHeadA_gen Ψ_k hΨkV, hPrefixCongr (hBbellV Ψ_k hΨkV) (hs2.2.1 Z_csw hZcswV)
          hStepB, hReassocStep, ← H_step.2.2.2 Y_csw, hY_eq, H_step.2.2.2 _,
          H_step.2.2.1 _ (fun σ val ↦ by simp only [qcWpQAssign, hΘ σ val]), qc_wp_qAssign_comp,
          ← rMain.embedUnitary_mul, ← rMain.embedUnitary_mul, mul_assoc, ← pow_succ]
    · rw [QRegister.whole_embedUnitary, SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
        hUbImg, ← Matrix.mul_assoc, ← hcTarget, Matrix.mul_assoc,
        SelectSwapQROM.zeroProjOn_mul_self]
  have hSet := (SelectSwapQROM.cleanRealizes_iff_set v (QRegister.whole N) rUbZero _ _).mp
    ((AliasPrep.cleanRealizes_sbx_iff _ _ _ _ _).mp hCR)
  dsimp only [rUbZero, rAncZ, rMain, N, combWalkCatRegAt] at hSet
  rw [QRegister.whole_embedUnitary, image_rUbZeroLoc] at hSet
  exact cleanRealizes_rFullZeroLoc_of_set bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sUb v
    (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2) (outZeroPrefixReg wOuter ko hkOut)
      (midZeroPrefixReg wInner2 km hkMid)) hSet
/-- Standard `(160 - d)`-scratch (`0 ≤ d ≤ 10`) `55`-AND asymmetric / `D_neg` `CleanWalkRefl2At`
for `bellSuperNoNeg2455Dyn` (`1 ≤ K`). -/
theorem cleanWalkRefl2At_bellSuperNoNeg2455Dyn_asym {Var : Type} [Fintype Var] [DecidableEq Var]
    (d : ℕ) (hd : d ≤ 10) {bQPE wOuter wInner2 ko km mLow sUb : ℕ} (K : ℕ) (hK : 1 ≤ K)
    {hkOut : ko ≤ wOuter} {hkMid : km ≤ wInner2} (hGiPos : 0 < wInner2) (hs : 160 - d ≤ sUb)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) {v : Var}
    {prepOutImpl : Unitary (2 ^ mOutUB wOuter)} {M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2)}
    {raw_4 raw_3 sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (legs :
      BellAsymLegs Var bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v prepOutImpl M_fwd M_bwd
      raw_4 raw_3 sF sB pOutFwd pOutBwd P_1 pTurn P_4)
    (hs1 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_4)
      (compactSelect55NoNegSliceDyn d hd false hs v wOuter wInner2 hGiPos
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hs2 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_3)
      (compactSelect55NoNegSliceDyn d hd true hs v wOuter wInner2 hGiPos
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
        (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)))
    (hTurnSupp : Disjoint pTurn.support
      (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb (159 - d) (by omega)))
    (hInterSupp : 2 ≤ K → Disjoint (P_1.support ∪ P_4.support ∪ pOutFwd.support ∪ pOutBwd.support)
      (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb (159 - d) (by omega))) :
    let uRefl2 := reflPulledPair (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
      (ubCustomMuxCatUnitary M_fwd prepOutImpl sF) (ubCustomMuxCatUnitary M_bwd prepOutImpl sB⁻¹)⁻¹
    let R₀ := reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    CleanWalkRefl2At bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v (uRefl2 * (R₀ * uRefl2) ^ (K -
      1))
      (bellSuperNoNeg2455Dyn d hd bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn v
        pOutFwd pOutBwd P_1 pTurn P_4) := by
  rw [bellSuperNoNeg2455Dyn]
  rw [compactSelect55NoNegSliceDyn] at hs1 hs2
  exact cleanWalkRefl2At_bellSuperNoNeg24GenDyn_asym (by omega)
    (compactCore145Bundle d hd false).toGen (compactCore145Bundle d hd true).toGen stepsA55
    stepsBFwd55 stepsBBwd55 specA55 (specB55 false) (specB55 true) runSteps24StepsA55
    (runSteps24StepsB55 false) (specB55_borrows_false false) (ctrl10_pair8_lt145 false)
    (runSteps24StepsB55 true) (specB55_borrows_false true) (ctrl10_pair8_lt145 true) K hK
    hGiPos (by omega) hsIn legs hs1 hs2 hTurnSupp hInterSupp
/-- Drop-in computable `K`-step `55`-AND super-reflection alias with aligned argument order. -/
abbrev bellSuperNoNeg55CompDyn {Var : Type} := @bellSuperNoNeg2455Dyn Var
theorem count_bellSuperNoNeg55CompDyn_toff {Var : Type} (d : ℕ) (hd : d ≤
    10) (bQPE wOuter wInner2 ko
    km mLow sUb K : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2) (hs :
      160 - d ≤
    sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v :
      Var) {pOutFwd pOutBwd P_1 pTurn P_4 :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)} (hFwd0 :
      pOutFwd.count .TOFF =
    0) (hBwd0 : pOutBwd.count .TOFF = 0) (h10 : P_1.count .TOFF = 0) (hTurn0 : pTurn.count .TOFF =
    0) (h40 : P_4.count .TOFF = 0) :
      (bellSuperNoNeg55CompDyn d hd bQPE wOuter wInner2 ko km mLow sUb K
    hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4).count .TOFF = 0 :=
  count_bellSuperNoNeg2455Dyn_toff d hd bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs
    hsIn v hFwd0 hBwd0 h10 hTurn0 h40
theorem count_bellSuperNoNeg55CompDyn_t {Var : Type} (d : ℕ) (hd : d ≤
    10) (bQPE wOuter wInner2 ko km
    mLow sUb K : ℕ) (hK : 1 ≤ K) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos :
      0 < wInner2) (hs : 160
    - d ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ 159 - d) (v :
      Var) (pOutFwd pOutBwd P_1 pTurn
    P_4 : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :
    (bellSuperNoNeg55CompDyn d hd bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn v
    pOutFwd pOutBwd P_1 pTurn P_4).count .T = K * (pOutFwd.count .T + P_1.count .T +
    compactBellSuperStep55TCount d + pTurn.count .T + P_4.count .T + pOutBwd.count .T) + 232 + (K -
    1) * (4 * (combARem wOuter wInner2 ko km - 2)) :=
  count_bellSuperNoNeg2455Dyn_t d hd bQPE wOuter wInner2 ko km mLow sUb K hK hkOut hkMid hGiPos hs
    hsIn v pOutFwd pOutBwd P_1 pTurn P_4
end Pi145CompactSelect24
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
end
