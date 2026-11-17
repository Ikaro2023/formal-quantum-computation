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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellSelectNoNegPair
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellPersistSuperWalk

/-!
# Concrete `57`-AND `SELECT` Slices & `K`-Step `wNegIn`-Free Bell Super-Reflection Circuit

Instantiates `select57NoNegPureUnitary`, concrete single-pass and Bell-pair `(160 - d)`-scratch
`57`-AND `SELECT` slices in both `cEntrySign23` and `wNegIn`-free modes, and defines
`bellSuperNoNegGenBundleDyn` / `bellSuperNoNegRouterDyn` with exact `.TOFF = 0` and `.T` counts.

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

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Select57Slices
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn AliasPrep
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
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
open DihedralWalkQPE.BlockReflection
open ZeroRcHotPrepMid21Fast TwoGearQPEPhase5
open TwoGearBox
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
open BellPersistNoNeg BellSelectNoNegPair BellPersistCore

/-! ## Section 1: `57`-AND `wNegIn`-Free Pure `SELECT` Unitaries & Exact Branch Action -/

/-- Pass-indexed `wNegIn`-free pure `nUB wOuter wInner2`-qubit `SELECT` unitary for `57`-AND `π145`
`SiZero` (reads only the `15` `(xo, so, b, si)` wires; commutes with inner ancillas). -/
noncomputable def select57NoNegPureUnitary (oddPass : Bool) (wOuter wInner2 : ℕ) :
    Unitary (2 ^ nUB wOuter wInner2) :=
  selectNoNegGenPureUnitary
    (phase2Bal145PhasedBranch actFlip145 (orbitalOfPi14557 oddPass)
      (negMaskPi14557 oddPass))
    specA57 (specB57 oddPass) wOuter wInner2

/-- Pass-1 (`oddPass = false`) `wNegIn`-free pure `SELECT` unitary (`57`-AND `π145`). -/
noncomputable abbrev select57NoNegFwdPureUnitary (wOuter wInner2 : ℕ) : Unitary (2 ^ nUB wOuter
    wInner2) :=
  select57NoNegPureUnitary false wOuter wInner2

/-- Pass-2 (`oddPass = true`) `wNegIn`-free pure `SELECT` unitary (`57`-AND `π145`). -/
noncomputable abbrev select57NoNegBwdPureUnitary (wOuter wInner2 : ℕ) : Unitary (2 ^ nUB wOuter
    wInner2) :=
  select57NoNegPureUnitary true wOuter wInner2

@[simp] theorem select57NoNegPureUnitary_inv (oddPass : Bool) (wOuter wInner2 : ℕ) :
    (select57NoNegPureUnitary oddPass wOuter wInner2)⁻¹ =
      select57NoNegPureUnitary oddPass wOuter wInner2 :=
  selectNoNegGenPureUnitary_inv
    (phase2Bal145PhasedBranch_inv actFlip145 (orbitalOfPi14557 oddPass)
      (negMaskPi14557 oddPass))
    specA57 (specB57 oddPass) wOuter wInner2

theorem y12NoNegOfState2457_indep15 (oddPass : Bool) (x16 : Fin 16 → Bool) :
    y12NoNegOfState24 specA57 (specB57 oddPass) x16 =
      y12NoNegOf15 specA57 (specB57 oddPass) (fun i ↦ x16 ⟨i.val, by omega⟩) := by
  dsimp only [y12NoNegOf15]
  have hx1 := pack16_eq_self_bound50 x16
  set x0 : Fin 16 → Bool := pad15False fun i ↦ x16 ⟨i.val, by omega⟩
  have hx0 := pack16_eq_self_bound50 x0
  have heqXo : (finOfBits 8 fun i ↦ x0 ⟨i.val, by omega⟩) =
      finOfBits 8 fun i ↦ x16 ⟨i.val, by omega⟩ :=
    congrArg (finOfBits 8) (funext fun i ↦ dite_eq_left (by have := i.isLt; dsimp; omega))
  have heqB : (finOfBits 5 fun j ↦ x0 ⟨9 + j.val, by omega⟩) =
      finOfBits 5 fun j ↦ x16 ⟨9 + j.val, by omega⟩ :=
    congrArg (finOfBits 5) (funext fun j ↦ dite_eq_left (by have := j.isLt; dsimp; omega))
  have h8 : x0 8 = x16 8 := dite_eq_left (by decide)
  have h14 : x0 14 = x16 14 := dite_eq_left (by decide)
  have h15 : x0 15 = false := dite_eq_right (by decide)
  set xo' := finOfBits 8 fun i ↦ x16 ⟨i.val, by omega⟩
  set b := finOfBits 5 fun j ↦ x16 ⟨9 + j.val, by omega⟩
  have hp1 : x16 = pack16 xo' (x16 8) b (x16 14) (x16 15) := hx1.symm
  have hp0 : x0 = pack16 xo' (x16 8) b (x16 14) false := by
    rw [← hx0, heqXo, h8, heqB, h14, h15]
  rw [hp1, hp0]
  obtain ⟨_, _, h2B1, h1B1⟩ := pre3_pack16_2 oddPass xo' (x16 8) b (x16 14) (x16 15)
  obtain ⟨_, _, h2B0, h1B0⟩ := pre3_pack16_2 oddPass xo' (x16 8) b (x16 14) false
  funext j
  by_cases hj10 : j.val < 10
  · dsimp only [y12NoNegOfState24]; rw [dite_eq_left hj10, dite_eq_left hj10]
    dsimp only [specB57]; rw [ctrl10_mergeMaskPost, ctrl10_mergeMaskPost]
    by_cases hxo' : xo'.val < 126
    · rw [(h2B1 hxo').2.2.2, (h2B0 hxo').2.2.2]
    · rw [(h1B1 (by omega)).2.2, (h1B0 (by omega)).2.2]
  · by_cases hjEq10 : j.val = 10
    · dsimp only [y12NoNegOfState24]
      rw [dite_eq_right hj10, dite_eq_right hj10, ite_eq_left hjEq10, ite_eq_left hjEq10]
      dsimp only [sigSelOfState24, specB57]
      by_cases hxo' : xo'.val < 126
      · exact (h2B1 hxo').2.1.trans (h2B0 hxo').2.1.symm
      · exact (h1B1 (by omega)).2.1.trans (h1B0 (by omega)).2.1.symm
    · dsimp only [y12NoNegOfState24]
      rw [dite_eq_right hj10, dite_eq_right hj10, ite_eq_right hjEq10, ite_eq_right hjEq10]

theorem y12NoNegOf1557_pack15 (oddPass : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32)
    (si : Bool) :
    y12NoNegOf15 specA57 (specB57 oddPass) (pack15 xo' so b si) =
      y12OfState24 specA57 (specB57 oddPass) (pack16 xo' so b si false) := by
  dsimp only [y12NoNegOf15]; rw [pad15False_pack15]
  funext j
  by_cases hj10 : j.val < 10
  · dsimp only [y12NoNegOfState24, y12OfState24]; rw [dite_eq_left hj10, dite_eq_left hj10]
  · by_cases hjEq10 : j.val = 10
    · dsimp only [y12NoNegOfState24, y12OfState24]
      rw [dite_eq_right hj10, dite_eq_right hj10, ite_eq_left hjEq10, ite_eq_left hjEq10]
    · dsimp only [y12NoNegOfState24, y12OfState24]
      rw [dite_eq_right hj10, dite_eq_right hj10, ite_eq_right hjEq10, ite_eq_right hjEq10]
      have h16 : (specA57 (pack16 xo' so b si false)).get24 16 = false := by
        dsimp only [specA57]; generalize step24_2 _ _ = sA; rfl
      dsimp only [signBitOfState24]; rw [h16, Bool.and_false]

theorem y12NoNegOf1557_of_ge126 (oddPass : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32)
    (si : Bool) (h126 : 126 ≤ xo'.val) :
    y12NoNegOf15 specA57 (specB57 oddPass) (pack15 xo' so b si) =
      y12NoNegOf15 specA57 (specB57 oddPass) (pack15 xo' so 0 si) := by
  rw [y12NoNegOf1557_pack15, y12NoNegOf1557_pack15]
  exact y12OfState2457_of_ge126 oddPass xo' so b si false h126

theorem select57NoNegPureUnitary_mulVec_ge126 {wOuter wInner2 : ℕ} (oddPass : Bool)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (h126 : 126 ≤ ((rXoLoc wOuter).extractIndex o').val) :
    let xo' := (rXoLoc wOuter).extractIndex o'
    let si := (rSigInLoc wInner2).extractIndex m
    let br1 := selectBranchUnitary (pi145XoEquiv xo') ((rSigOutLoc wOuter).extractIndex o')
      ((rBLoc wInner2).extractIndex m) 1
    (select57NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      if (si == 0) && xor (inPass1Pi145Xo xo') (decide (xo'.val < 184) && oddPass) then
        embedKet (br1.1 *ᵥ ψ) o' m else embedKet ψ o' m := by
  intro xo' si br1
  have hsiAll (s : Fin (2 ^ 1)) : (!(decide (s = 1))) = (s == 0) := by
    fin_cases s <;> rfl
  have hsi : (!(decide (si = 1))) = (si == 0) := hsiAll si
  have hEq : (select57NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      embedKet
        ((if oneBodyActive2 oddPass xo' (decide (si = 1)) then br1 else 1).1 *ᵥ ψ) o' m := by
    refine selectNoNegGenPureUnitary_mulVec_embedKet_eq_of_branch _ _ _ ψ o' m _ ?_
    rw [y12NoNegOf1557_pack15]
    exact r57Branch_ge126 oddPass _ _ _ _ false h126
  rw [hEq]; simp only [oneBodyActive2, hsi]
  cases ((si == 0) && xor (inPass1Pi145Xo xo') (decide (xo'.val < 184) && oddPass)) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_one, Matrix.one_mulVec]

theorem select57NoNegPureUnitary_mulVec_oneBodyZero {wOuter wInner2 : ℕ}
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (h126 : 126 ≤ ((rXoLoc wOuter).extractIndex o').val)
    (h184 : ((rXoLoc wOuter).extractIndex o').val < 184) (hSi : (rSigInLoc wInner2).extractIndex m =
      0) :
    let xo' := (rXoLoc wOuter).extractIndex o'
    let br1 := selectBranchUnitary (pi145XoEquiv xo') ((rSigOutLoc wOuter).extractIndex o')
      ((rBLoc wInner2).extractIndex m) 1
    (select57NoNegFwdPureUnitary wOuter wInner2).1 *ᵥ embedKet ψ o' m =
        (if inPass1Pi145Xo xo' then embedKet (br1.1 *ᵥ ψ) o' m else embedKet ψ o' m) ∧
      (select57NoNegBwdPureUnitary wOuter wInner2).1 *ᵥ embedKet ψ o' m =
        (if !inPass1Pi145Xo xo' then embedKet (br1.1 *ᵥ ψ) o' m else embedKet ψ o' m) := by
  intro xo' br1
  have hd : decide (((rXoLoc wOuter).extractIndex o').val < 184) = true := decide_eq_true h184
  refine ⟨?_, ?_⟩
  · have hF := select57NoNegPureUnitary_mulVec_ge126 false ψ o' m h126
    dsimp only at hF; rw [select57NoNegFwdPureUnitary, hF, hSi, Bool.and_false]
    dsimp only [xo', br1]; cases inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') <;> rfl
  · have hB := select57NoNegPureUnitary_mulVec_ge126 true ψ o' m h126
    dsimp only at hB; rw [select57NoNegBwdPureUnitary, hB, hSi, hd, Bool.and_self]
    dsimp only [xo', br1]; cases inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') <;> rfl

theorem select57NoNegPureUnitary_mulVec_ge184 {wOuter wInner2 : ℕ} (oddPass : Bool)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (h184 : 184 ≤ ((rXoLoc wOuter).extractIndex o').val) :
    (select57NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m = embedKet ψ o' m := by
  have hG := select57NoNegPureUnitary_mulVec_ge126 oddPass ψ o' m (by omega)
  dsimp only at hG; rw [hG]
  have hp1 : inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') = false := by
    dsimp only [inPass1Pi145Xo]; exact decide_eq_false (by omega)
  have hd : decide (((rXoLoc wOuter).extractIndex o').val < 184) = false := decide_eq_false
    (by omega)
  rw [hp1, hd]; simp

/-! ## Section 2: Concrete `(160 - d)`-Scratch `57`-AND `SELECT` Slices (Both Modes) -/

/-- `K`-step Bell-persistent super-reflection on `combQubitsAt`, eliminating the `232-T` spin
swap across all `K - 1` inter-step `R₀` boundaries (`0 TOFF`). -/
noncomputable def bellSuperNoNegGenBundleDyn {Var : Type}
    {kInner tCoreF tCoreB : ℕ}
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23))
    (bQPE wOuter wInner2 ko km mLow sUb K : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2)
    (hs : 1 + kInner ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ kInner)
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
  let rRt := lowBitRouter23 bundleF.hk6 wOuter wInner2 wNegIn rMain rScr hdisjScr
  let L := lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisjScr
  let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wNegIn rMain)
    (L.rInner ⟨0, by have := bundleF.hk6; omega⟩)
  let sA := liftRouterStepsN rRt stepsA
  let sB1 := liftRouterStepsN rRt stepsBF
  let sB2 := liftRouterStepsN rRt stepsBB
  let uEnt1 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB1)
  let uEnt2 := DynamicCircuit.seq (routerStepsFwdUnitDyn sA) (routerStepsFwdUnitDyn sB2)
  let pPost1 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB1) (routerStepsBwdUnitDyn sA))
  let pPost2 := liftUnitVar v (.seq (routerStepsBwdUnitDyn sB2) (routerStepsBwdUnitDyn sA))
  let wDst := rScr ⟨kInner, by omega⟩
  let wTmp := rScr ⟨kInner - 1, by have := bundleF.hk6; omega⟩
  let pReflIn := reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega) v
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
  .seq pHead (.seq (iterBinDyn (K - 1) (.seq pMidCore pTransBell)) pTail)

theorem count_bellSuperNoNegGenBundleDyn_toff {Var : Type}
    {kInner tCoreF tCoreB : ℕ}
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23))
    (bQPE wOuter wInner2 ko km mLow sUb K : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2)
    (hs : 1 + kInner ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ kInner)
    (v : Var)
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (hFwd0 : pOutFwd.count .TOFF = 0) (hBwd0 : pOutBwd.count .TOFF = 0)
    (h10 : P_1.count .TOFF = 0) (hTurn0 : pTurn.count .TOFF = 0) (h40 : P_4.count .TOFF = 0) :
    (bellSuperNoNegGenBundleDyn bundleF bundleB stepsA stepsBF stepsBB bQPE wOuter wInner2 ko km
      mLow sUb K
      hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4).count .TOFF = 0 := by
  dsimp only [bellSuperNoNegGenBundleDyn]
  simp [count_iterBinDyn, count_liftUnitVar, cswapBlockDyn_count_toff,
    bundleF.count_toff, bundleB.count_toff, hFwd0, hBwd0, h10, hTurn0, h40]

theorem count_bellSuperNoNegGenBundleDyn_t {Var : Type}
    {kInner tCoreF tCoreB : ℕ}
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF)
    (bundleB : GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23))
    (bQPE wOuter wInner2 ko km mLow sUb K : ℕ) (hK : 1 ≤ K)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hGiPos : 0 < wInner2)
    (hs : 1 + kInner ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ kInner)
    (v : Var)
    (pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :
    (bellSuperNoNegGenBundleDyn bundleF bundleB stepsA stepsBF stepsBB bQPE wOuter wInner2 ko km
      mLow sUb K
      hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4).count .T =
      K * (pOutFwd.count .T + P_1.count .T + tCoreF + tCoreB + 464 +
        4 * (2 * numRouterAnds stepsA + numRouterAnds stepsBF + numRouterAnds stepsBB) +
        pTurn.count .T + P_4.count .T + pOutBwd.count .T) + 232 +
      (K - 1) * (4 * (combARem wOuter wInner2 ko km - 2)) := by
  let wNegIn : Wire wInner2 := ⟨0, hGiPos⟩
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  have hdisj : rMain.DisjointWires rScrUb :=
    combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb
  let rScr := rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega))
  have hdisjScr : rMain.DisjointWires rScr := QRegister.disjoint_iff.mpr fun _ _ ↦ hdisj.ne _ _
  let L := lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisjScr
  let rRt := lowBitRouter23 bundleF.hk6 wOuter wInner2 wNegIn rMain rScr hdisjScr
  have hSw : (rSwap117LowBit wOuter wInner2 wNegIn rMain).DisjointWires
      (QRegister.singleton (L.rInner ⟨0, by have := bundleF.hk6; omega⟩)) :=
    QRegister.disjoint_iff.mpr fun i j ↦ by
      fin_cases j
      exact (disjoint_rSwap117_rInner bundleF.hk6 wOuter wInner2 wNegIn rMain rScr hdisjScr).ne i
        ⟨0, by have := bundleF.hk6; omega⟩
  have hSys (m : Fin (1 + kInner)) : ((rMain.compose (rSysCatUB wOuter wInner2 11)).compose
      (QRegister.block 0 (2 * 58) (by decide))).DisjointWires (QRegister.singleton (rScr m)) :=
    QRegister.disjoint_iff.mpr fun _ j ↦ by fin_cases j; exact hdisjScr.ne _ m
  have hDstTmp : rScr ⟨kInner, by omega⟩ ≠ rScr ⟨kInner - 1, by have := bundleF.hk6; omega⟩ :=
    rScr.wires.injective.ne fun h ↦ by
      have hv := congrArg Fin.val h; have hk6 := bundleF.hk6; dsimp at hv; omega
  have hA := count_routerStepsFwdBwd_t (liftRouterStepsN rRt stepsA)
  have hB1 := count_routerStepsFwdBwd_t (liftRouterStepsN rRt stepsBF)
  have hB2 := count_routerStepsFwdBwd_t (liftRouterStepsN rRt stepsBB)
  rw [numRouterAnds_liftRouterStepsN] at hA hB1 hB2
  dsimp only [rRt, L, wNegIn, rScr, rMain, rScrUb] at hSw hSys hDstTmp hA hB1 hB2
  dsimp only [bellSuperNoNegGenBundleDyn, wNegIn] at hSw ⊢
  simp only [dyn_count_seq, count_iterBinDyn, count_liftUnitVar, countReflInSliceDyn_t]
  rw [cswapBlockDyn_count_t _ 58 _ _ hSw, bundleF.count_t, bundleB.count_t, dBellEntry58Dyn_count_t,
    dBellExit58Dyn_count_t v ((rMain.compose (rPolyCtrl16InCat wOuter wInner2 ⟨0,
      hGiPos⟩)) 14) _ _ _
      (hSys _) (hSys _) hDstTmp (hdisjScr.ne _ _)]
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
  have hb' : tCoreF + (232 + ((cBF + cBA) +
      (pTurn.count .T + ((cFA + cFB) + (0 + tCoreB))))) +
      (232 + (((cBB + cBA) + (P_4.count .T + (pOutBwd.count .T +
        (R + (pOutFwd.count .T + (P_1.count .T + (cFA + cFF))))))) + 0)) = S + R := by
    dsimp only [S, R, cFA, cBA, cFF, cBF, cFB, cBB,
      rRt, wNegIn, rScr, rMain, rScrUb] at hA hB1 hB2 ⊢; omega
  have hht' : (pOutFwd.count .T + (P_1.count .T + ((cFA + cFF) + 232))) +
      ((tCoreF + (232 + ((cBF + cBA) + (pTurn.count .T + ((cFA + cFB) + (0 + tCoreB)))))) +
        (232 + ((cBB + cBA) + (P_4.count .T + pOutBwd.count .T)))) = S + 232 := by
    dsimp only [S, cFA, cBA, cFF, cBF, cFB, cBB,
      rRt, wNegIn, rScr, rMain, rScrUb] at hA hB1 hB2 ⊢; omega
  dsimp only [cFA, cBA, cFF, cBF, cFB, cBB,
      rRt, wNegIn, rScr, rMain, rScrUb] at hb' hht'
  rw [hb', Nat.add_comm ((K - 1) * (S + R)), ← Nat.add_assoc, hht']
  have hK1 : 1 + (K - 1) = K := by omega
  calc (S + 232) + (K - 1) * (S + R)
      = (1 + (K - 1)) * S + 232 + (K - 1) * R := by ring
    _ = K * S + 232 + (K - 1) * R := by rw [hK1]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Select57Slices
end

/-!
# `K`-Step `wNegIn`-Free Bell-Persistent Super-Walk Theorem (`GenCore145Bundle`)

Proves `bellSuperNoNegGenBundleDyn` correctness by induction on `K - 1`: a `K`-step
Bell-persistent super-reflection parameterized by arbitrary `GenCore145Bundle`s `bundleF`, `bundleB`
in
`wNegIn`-free mode (`0 < wInner2`) cleanly realizes `uRefl2 * (R₀ * uRefl2) ^ (K - 1)` on
`combQubitsAt`.

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

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellSuperNoNegWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn AliasPrep
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
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
open DihedralWalkQPE.BlockReflection
open ZeroRcHotPrepMid21Fast TwoGearQPEPhase5
open TwoGearBox
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open BellPersistCore BellPersistSuperWalk
open BellPersistNoNeg BellSelectNoNegPair Select57Slices

local instance instNeZeroTwoPowNoNegSuperWalk (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellSuperNoNegWalk
end
