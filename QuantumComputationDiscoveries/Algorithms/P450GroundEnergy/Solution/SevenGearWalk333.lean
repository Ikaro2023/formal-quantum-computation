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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellSelectD11CoreC
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SevenGearBondDeferD
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HGadgetQrom
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ThreeGearWindow47487
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PureSelect55Bridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18SuperWalk

/-!
# `333`-Qubit (`Ancillas = 217`) Seven-Gear `(M = 47,487)` QPE Walk (`436,509,499,221`)

Combines:
- `d = 0` (`sUb = 160`), `d = 1` (`sUb = 159`), and `d = 4` (`sUb = 156`) `55`-AND `π145`
  super-reflections (`390-T` QROM),
- `d = 11` (`sRem = 149`, `148` inner scratch wires, `K = 1`) `57`-AND `π145` fine reflection
  with `418-T` low-`25` H-gadget QROM (`Inner18HGadgetQrom`),
- Universal Recursive Peel `7`-Gear Bond-Deferred QPE (`SevenGearBondDeferD`, `M = 47,487`,
  `nStd = 45`, `kTail = 384`, `tShift = 56`),
yielding `Ancillas = 217`, `Q = 333`, `T = 1,310,839,337`, `Q × T = 436,509,499,221`.

## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- G. H. Low et al., *Phys. Rev. X* **15**, 041016 (2025), DOI: 10.1103/pb2g-j9cw.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearWalk333
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit Real HermitianMat CoherentAlias CleanDyn AliasPrep
open SelectSwapQROM QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open TopIntegrationBridge Phase2MidSandwich ReordOuter13Bridge
open HGadgetPrepOutOuter8 Inner18Symp14Walk Pi145SOSPermBridge
open Inner18HadWSuperLegsA Inner18HadWSuperLegsB Inner18HadWSuperLegsC
open Inner18HadWSuperLegs MainLow27HGadget HadWMux23SOSBridge
open NoNegDNegSOSAndSuperWalk LowBitPi145Select
open Pi145CompactSelect24 BellAsymCore BellSuperLegSplice
open BellPersistCore BellPersistSuperWalk ThreeGearBellSuper
open TailShiftWindow46847 TailShiftBox TwoGearQPEPhase5
open PhaseBD11CompactCore SevenGearBondDefer Select55PureBridge
open MainInner18SuperWalk Inner18Bound322HGadgetQrom
open DihedralWalkQPE ApproxIqft16
open HadWStateMux25CompactA Outer8Pi145Compact2RotDyn StepAnfAndCoin14Core
open Cat11CompactPhase2Bridge ZeroRcHotPrepMid21Fast StepKeep9Symp14Data
open QuantizedFactoredMag30 TailShiftThreeGear MidReflCtxRetain
open CompactZeroCmp20OuterParam CompactTuned162StepZeroCmp20
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
  (prepMidDirectXo7MuxUnitary)
open
  _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE
  (CleanWalkRefl2 combARem)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowWalk333 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- Reindex classical variables of a `DynamicCircuit` from `Unit` to `v : Var`. -/
abbrev instUnitVar {Var : Type} {n : ℕ} (v : Var) : DynamicCircuit Unit n → DynamicCircuit Var n :=
  Lac2Fused184Select.liftUnitVar v

@[simp]
theorem count_instUnitVar_toff {Var : Type} {n : ℕ} (v : Var) (p : DynamicCircuit Unit n) :
    (instUnitVar v p).count .TOFF = p.count .TOFF :=
  Lac2Fused184Select.count_liftUnitVar v .TOFF p

@[simp]
theorem count_instUnitVar_t {Var : Type} {n : ℕ} (v : Var) (p : DynamicCircuit Unit n) :
    (instUnitVar v p).count .T = p.count .T :=
  Lac2Fused184Select.count_liftUnitVar v .T p

theorem realizes_instUnitVar {Var : Type} [Finite Var] [DecidableEq Var] {n k m : ℕ}
    [NeZero (2 ^ n)]
    (v : Var) (rTarget : QRegister k n) (outcomes : Finset (Fin (2 ^ k)))
    (rAnc : QRegister m n) (hdisj : rTarget.DisjointWires rAnc)
    (U : Unitary (2 ^ (k + m))) (p : DynamicCircuit Unit n)
    (hp : RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rTarget outcomes rAnc hdisj U p.compile)
        :
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rTarget outcomes rAnc hdisj U
      (instUnitVar v p).compile := by
  cases nonempty_fintype Var
  rw [qc_realizesUnitaryFromBasisOutcomesAndZeroWorkspace_iff] at hp ⊢
  intro M σ
  have hM := hp M (fun _ ↦ σ v)
  have hwp : wp (instUnitVar v p).compile (fun _ ↦ M) =
      fun τ ↦ wp p.compile (fun _ ↦ M) (fun _ ↦ τ v) :=
    funext fun τ ↦ Lac2Fused184Select.wp_liftUnitVar v p (fun _ ↦ M) τ
  rw [hwp]
  exact hM

/-- `17-T` `Clifford+T` outer magnitude word (`orthGrover184L1 ≤ 24 / 10 ^ 11`). -/
abbrev mag8To23Word17 : List OuterWeights.GroverUniform.Gate1 := MainInner18SuperWalk.mag8To23Word17

theorem checkOrthGrover184L1Word_word17 :
    Pi145Fast2RotCore.checkOrthGrover184L1Word 17 24 (10 ^ 11) mag8To23Word17 = true :=
  MainInner18SuperWalk.checkOrthGrover184L1Word_word17

/-- Reference `(wOuter = 8, wInner2 = 18)` block-encoding walk unitary `mainUB`. -/
noncomputable abbrev mainUB : Unitary (2 ^ nUB 8 18) := MainInner18SuperWalk.mainUB2

/-- Parametric `55`-AND `π145` super-reflection (`390-T` QROM, `Var = Unit`) at `(d, bQPE, sUb, K)`.
-/
def r55GearCirc (d bQPE sUb K : ℕ) (hd : d ≤ 10 := by decide)
    (hs : 160 - d ≤ sUb := by decide)
    (hsIn : combARem 8 18 4 14 - 2 ≤ 159 - d := by decide)
    (hk1 : max 144 (121 + 33) ≤ 159 - d := by decide)
    (hkT : max 146 (121 + 33) ≤ 159 - d := by decide)
    (hUb : 159 - d ≤ sUb := by decide)
    (hs87 : 0 + 87 ≤ sUb := by decide)
    (hk4 : 68 ≤ 159 - d := by decide) : FGCircAt Unit bQPE 8 18 4 14 sUb :=
  bellSuperNoNeg55CompDyn d hd bQPE 8 18 4 14 0 sUb K
    (by decide) (by decide) (by decide) hs hsIn ()
    (pOutFwdAt bQPE sUb hs87) (pOutBwdAt bQPE sUb hs87)
    (pStep1At (mainKeep9HGadget400LoadCirc Unit) bQPE sUb (159 - d) hk1 hUb)
    (pTurnAt (mainKeep9HGadget400LoadCirc Unit) bQPE sUb (159 - d) hkT hUb)
    (pStep4At bQPE sUb (159 - d) hk4 hUb)

theorem count55GearCirc_toff (d bQPE sUb K : ℕ) (hd : d ≤ 10 := by decide)
    (hs : 160 - d ≤ sUb := by decide)
    (hsIn : combARem 8 18 4 14 - 2 ≤ 159 - d := by decide)
    (hk1 : max 144 (121 + 33) ≤ 159 - d := by decide)
    (hkT : max 146 (121 + 33) ≤ 159 - d := by decide)
    (hUb : 159 - d ≤ sUb := by decide)
    (hs87 : 0 + 87 ≤ sUb := by decide)
    (hk4 : 68 ≤ 159 - d := by decide) :
    (r55GearCirc d bQPE sUb K hd hs hsIn hk1 hkT hUb hs87 hk4).count .TOFF = 0 :=
  count_bellSuperNoNeg55CompDyn_toff d hd bQPE 8 18 4 14 0 sUb K
    (by decide) (by decide) (by decide) hs hsIn ()
    (count_pOutFwdAt_toff ..) (count_pOutBwdAt_toff ..)
    (count_pStep1At_toff ..) (count_pTurnAt_toff ..) (count_pStep4At_toff ..)

theorem count55GearCirc_t (d bQPE sUb K t : ℕ) (hK : 1 ≤ K := by decide)
    (hd : d ≤ 10 := by decide) (hs : 160 - d ≤ sUb := by decide)
    (hsIn : combARem 8 18 4 14 - 2 ≤ 159 - d := by decide)
    (hk1 : max 144 (121 + 33) ≤ 159 - d := by decide)
    (hkT : max 146 (121 + 33) ≤ 159 - d := by decide)
    (hUb : 159 - d ≤ sUb := by decide)
    (hs87 : 0 + 87 ≤ sUb := by decide)
    (hk4 : 68 ≤ 159 - d := by decide)
    (ht : K * (319 + (386 + 390) + compactBellSuperStep55TCount d +
      (732 + 390) + 366 + 279) + 232 + (K - 1) * (4 * (combARem 8 18 4 14 - 2)) = t := by
        decide) :
    (r55GearCirc d bQPE sUb K hd hs hsIn hk1 hkT hUb hs87 hk4).count .T = t := by
  rw [r55GearCirc, count_bellSuperNoNeg55CompDyn_t d hd bQPE 8 18 4 14 0 sUb K hK,
    count_pOutFwdAt_t, count_pOutBwdAt_t, count_pStep1At_t, count_pTurnAt_t, count_pStep4At_t]
  exact ht

/-- Unused even-`top` Slot-B placeholder (`peelTop 45 0 = 46` is even, `0` gates). -/
def p4B_333 : FGCircAt Unit 6 8 18 4 14 159 := .circuit .identity

theorem count_p4B_333_toff : p4B_333.count .TOFF = 0 := rfl

theorem count_p4B_333_t : p4B_333.count .T = 0 := rfl

/-- Stage `F` (`K = 1`, `d = 11`, `sRem = 149`, `418-T` low-`25` QROM) single-step reflection. -/
def pRefl2F333 : FGCircB Unit 8 18 4 14 149 :=
  bellRefl2NoNeg57D11CompDyn 11 (by decide) 16 8 18 4 14 0 149
    (by decide) (by decide) (by decide) (by decide) (by decide) ()
    (pOutFwdAt 16 149 (by decide)) (pOutBwdAt 16 149 (by decide))
    (pStep1At (OneHot14LoadCirc2.hgLow25 Unit) 16 149 148 (by decide) (by decide))
    (pTurnAt (OneHot14LoadCirc2.hgLow25 Unit) 16 149 148 (by decide) (by decide))
    (pStep4At 16 149 148 (by decide) (by decide))

theorem count_pRefl2F333_toff : pRefl2F333.count .TOFF = 0 :=
  count_bellRefl2NoNeg57D11CompDyn_toff 11 (by decide) 16 8 18 4 14 0 149
    (by decide) (by decide) (by decide) (by decide) (by decide) ()
    (count_pOutFwdAt_toff ..) (count_pOutBwdAt_toff ..)
    (count_pStep1At_toff ..) (count_pTurnAt_toff ..) (count_pStep4At_toff ..)

theorem count_pRefl2F333_t : pRefl2F333.count .T = 37642 := by
  rw [pRefl2F333, count_bellRefl2NoNeg57D11CompDyn_t,
    count_pOutFwdAt_t, count_pOutBwdAt_t, count_pStep1At_t, count_pTurnAt_t, count_pStep4At_t]
  decide

/-- Clean ancilla count (`217`, giving `116 + 217 = 333` total qubits). -/
abbrev mainAncillas : ℕ := combAncillasB 8 18 4 14 149

/-- `Unit`-indexed top-level `333`-qubit Seven-Gear `(M = 47,487)` QPE dynamic circuit. -/
def fast7gUnitProg {n : ℕ} (rSys : QRegister systemQubits_local n)
    (rAnc : QRegister mainAncillas n) : DynamicCircuit Unit n :=
  p450SymbolicSevenGearProg 8 18 4 14 149 160 160 160 160 159 156
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    regData_47487_7 threeGearWinCirc_47487_10_7 (tailShiftParams_47487_10 7) () fastIqft16Circuit
    (r55GearCirc 0 2 160 16384) (r55GearCirc 0 2 160 14720)
    (r55GearCirc 0 3 160 1664) (r55GearCirc 0 3 160 6528)
    (r55GearCirc 0 4 160 1664) (r55GearCirc 0 4 160 2432)
    (r55GearCirc 0 5 160 1664) (r55GearCirc 0 5 160 384)
    (r55GearCirc 1 6 159 1024) p4B_333
    (r55GearCirc 4 3 156 128) pRefl2F333 rSys rAnc

/-- Polymorphic `{Var : Type}` top-level `333`-qubit Seven-Gear QPE dynamic circuit. -/
def fast7gProg {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_local n)
    (rAnc : QRegister mainAncillas n) : DynamicCircuit Var n :=
  instUnitVar v (fast7gUnitProg rSys rAnc)

theorem fast7gProg_const_cost {Var : Type} {n : ℕ} (v : Var)
    (rSys : QRegister systemQubits_local n) (rAnc : QRegister mainAncillas n) :
    (fast7gProg v rSys rAnc).count .TOFF = 0 ∧
      (systemQubits_local + mainAncillas) * (fast7gProg v rSys rAnc).count .T ≤
        436509499221 := by
  rw [fast7gProg, count_instUnitVar_toff, count_instUnitVar_t]
  exact p450SymbolicSevenGearProg_const_cost_of_eq
    (tWin := 142248) (tIqft := 12603)
    (t0A := 450330772) (t0B := 404594068) (t1A := 45736852) (t1B := 179428756)
    (t2A := 45736852) (t2B := 66846100) (t3A := 45736852) (t3B := 10554772)
    (t4A := 29063316) (t4B := 0) (tM := 3980180) (tF := 37642)
    (tTot := 1310839337) (c := 436509499221)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    regData_47487_7 threeGearWinCirc_47487_10_7 threeGearWin_47487_10_7
    threeGearWin_47487_10_7_toCirc threeGearWin_47487_10_7_cWinC
    (threeGearWin_47487_10_7.base.count_t.trans_le threeGearWin_47487_10_7_tWin.le)
    (tailShiftParams_47487_10 7) ()
    fastIqft16Circuit_count_toff fastIqft16Circuit_count_t.le
    (count55GearCirc_toff 0 2 160 16384) (count55GearCirc_toff 0 2 160 14720)
    (count55GearCirc_toff 0 3 160 1664) (count55GearCirc_toff 0 3 160 6528)
    (count55GearCirc_toff 0 4 160 1664) (count55GearCirc_toff 0 4 160 2432)
    (count55GearCirc_toff 0 5 160 1664) (count55GearCirc_toff 0 5 160 384)
    (count55GearCirc_toff 1 6 159 1024) count_p4B_333_toff
    (count55GearCirc_toff 4 3 156 128) count_pRefl2F333_toff
    (count55GearCirc_t 0 2 160 16384 450330772).le
    (count55GearCirc_t 0 2 160 14720 404594068).le
    (count55GearCirc_t 0 3 160 1664 45736852).le
    (count55GearCirc_t 0 3 160 6528 179428756).le
    (count55GearCirc_t 0 4 160 1664 45736852).le
    (count55GearCirc_t 0 4 160 2432 66846100).le
    (count55GearCirc_t 0 5 160 1664 45736852).le
    (count55GearCirc_t 0 5 160 384 10554772).le
    (count55GearCirc_t 1 6 159 1024 29063316).le
    count_p4B_333_t.le
    (count55GearCirc_t 4 3 156 128 3980180).le
    count_pRefl2F333_t.le
    rSys rAnc (by decide) (by decide)

theorem bellAsymLegsMain_d11_low25
    {raw_4 raw_3 : Unitary (2 ^ (nUB 8 18 + 11))}
    (hsF_pres : AliasPrep.PreservesWires
      ((combWalkCatRegAt 16 8 18 4 14 0 149).embedUnitary raw_4).1
      ((((combWalkCatRegAt 16 8 18 4 14 0 149).compose (rUBInCat 8 18 11)).compose
        (rAllUB 8 18)).image ∪ (combScrUbRegAt 16 8 18 4 14 0 149).image))
    (hsB_pres : AliasPrep.PreservesWires
      ((combWalkCatRegAt 16 8 18 4 14 0 149).embedUnitary raw_3).1
      ((((combWalkCatRegAt 16 8 18 4 14 0 149).compose (rUBInCat 8 18 11)).compose
        (rAllUB 8 18)).image ∪ (combScrUbRegAt 16 8 18 4 14 0 149).image)) :
    let D_neg := dNegUB 8 18 Pi145CompactRouter.hot128NegBit2
    let M_a := asymMidMux 8 18 mainPrepMid
    BellAsymLegs Unit 16 8 18 4 14 0 149 (by decide) (by decide) ()
      (outer8PrepOutWordImpl mag8To23Word17) M_a M_a raw_4 raw_3
      ((rUBInCat 8 18 11).embedUnitary D_neg * raw_4)
      (raw_3 * (rUBInCat 8 18 11).embedUnitary D_neg)
      (pOutFwdAt 16 149 (by decide)) (pOutBwdAt 16 149 (by decide))
      (pStep1At (OneHot14LoadCirc2.hgLow25 Unit) 16 149 148 (by decide) (by decide))
      (pTurnAt (OneHot14LoadCirc2.hgLow25 Unit) 16 149 148 (by decide) (by decide))
      (pStep4At 16 149 148 (by decide) (by decide)) := by
  intro D_neg M_a
  let rMain := combWalkCatRegAt 16 8 18 4 14 0 149
  let rScrUb := combScrUbRegAt 16 8 18 4 14 0 149
  let rUB := combUBRegB 16 8 18 4 14 0 149
  let rOut := combOutRegB 16 8 18 4 14 0 149
  let S₁ := scrMidZeroSet 16 8 18 4 14 0 149 (by decide)
  let S₂ := rOut.image ∪ S₁
  have hMainScr := combWalkCatRegB_disjoint_scr 16 8 18 4 14 0 149
  have hD_pres : AliasPrep.PreservesWires
      (rMain.embedUnitary ((rUBInCat 8 18 11).embedUnitary D_neg)).1
      (((rMain.compose (rUBInCat 8 18 11)).compose (rAllUB 8 18)).image ∪ rScrUb.image) :=
    preservesWiresDNegCat 8 18 Pi145CompactRouter.hot128NegBit2 rMain _
  have hNotAll := sigIn_not_mem_out_scr_midZero 16 149
  have hMuxEq : prepMidDirectXo7MuxUnitary 8 18 (fun rc ↦ mainPrepMid (pi128Equiv rc)) =
      directXo7Mux18Of 8 mux9AltBit
        (genPi128SliceFn14 keep9SliceTargetFn14 pi128Equiv)
        factoredMag30T72Circuit.eval :=
    congrArg (muxUnitary _ _ _) (funext fun _ ↦ rfl)
  have hPresHalf {V : Unitary (2 ^ (nUB 8 18 + 11))}
      (hVP : AliasPrep.PreservesWires (rMain.embedUnitary V).1
        (((rMain.compose (rUBInCat 8 18 11)).compose (rAllUB 8 18)).image ∪ rScrUb.image)) :
      AliasPrep.PreservesWires
        (rMain.embedUnitary ((rUBInCat 8 18 11).embedUnitary M_a⁻¹ * V *
          (rUBInCat 8 18 11).embedUnitary M_a)).1 S₂ := by
    refine preservesWiresAsymMidSandwich rMain prepMidSpinFactoredMainPrepMid hNotAll ?_
    rw [hMuxEq]
    dsimp only [S₂, S₁, rOut, scrMidZeroSet]
    rw [← Finset.union_assoc]
    exact preservesWiresDirectXo7Sandwich18_out_scr_midZero rMain rScrUb hMainScr
      (genPi128SliceFn14 keep9SliceTargetFn14 pi128Equiv) factoredMag30T72Circuit.eval V hVP
  have hPresF_all : AliasPrep.PreservesWires
      (rMain.embedUnitary ((rUBInCat 8 18 11).embedUnitary M_a⁻¹ *
        ((rUBInCat 8 18 11).embedUnitary D_neg * raw_4) *
        (rUBInCat 8 18 11).embedUnitary M_a)).1 S₂ :=
    hPresHalf (by
      rw [rMain.embedUnitary_mul]
      exact AliasPrep.preservesWires_mul hD_pres hsF_pres)
  have hPresB_all : AliasPrep.PreservesWires
      (rMain.embedUnitary ((rUBInCat 8 18 11).embedUnitary M_a⁻¹ *
        (raw_3 * (rUBInCat 8 18 11).embedUnitary D_neg) *
        (rUBInCat 8 18 11).embedUnitary M_a)).1 S₂ :=
    hPresHalf (by
      rw [rMain.embedUnitary_mul]
      exact AliasPrep.preservesWires_mul hsB_pres hD_pres)
  have h1Raw := cleanRealizesSetInner18Step1Dyn (OneHot14LoadBundle_3.hgLow25 Unit)
    (Mag30Bundle2.t72 Unit) pi128Equiv rUB rScrUb 148 (by decide) (by decide)
    (hMainScr.compose_left _) ()
  dsimp only [Mag30Bundle2.t72] at h1Raw
  rw [inner18Mfwd_eqAsymMidMux] at h1Raw
  have hTurnRaw := cleanTurnaroundWpInner18TurnDyn (OneHot14LoadBundle_3.hgLow25 Unit)
    (Mag30Bundle2.t72 Unit) (Mag30Bundle2.t72 Unit) pi128Equiv rUB rScrUb 148 (by decide)
      (by decide)
    (hMainScr.compose_left _) ()
  dsimp only [Mag30Bundle2.t72] at hTurnRaw
  rw [hot128NegUB_eqDNegUB, inner18Mfwd_eqAsymMidMux,
    embed_reflMidUnitary_inMidWalkCat_eq rMain] at hTurnRaw
  have h4Raw := cleanUnloadsWpInner18Step4ColdDyn (Mag30Bundle2.t72 Unit) pi128Equiv
    rUB rScrUb 148 (by decide) (by decide) (hMainScr.compose_left _) ()
  dsimp only [Mag30Bundle2.t72] at h4Raw
  rw [inner18Mfwd_eqAsymMidMux] at h4Raw
  exact BellAsymLegs.ofDNeg M_a M_a D_neg
    (dNegUB_inv 8 18 Pi145CompactRouter.hot128NegBit2) raw_4 raw_3
    (cleanRealizes_pOutFwdAt 16 149 (by decide))
    (cleanUnloadsWp_pOutBwdAt 16 149 (by decide))
    (MainInner18SuperWalk.outerConjPreservesZeroOuter8PrepOutWordImpl mag8To23Word17)
    h1Raw hTurnRaw h4Raw
    (fun i j ⟨w, hw, hne⟩ ↦ hPresF_all i j ⟨w, Finset.subset_union_right hw, hne⟩)
    (fun i j ⟨w, hw, hne⟩ ↦ hPresB_all i j ⟨w, Finset.subset_union_right hw, hne⟩)
    (by
      rw [innerMidCoreUnitary, rMain.embedUnitary_mul, rMain.embedUnitary_mul]
      exact AliasPrep.preservesWires_mul
        (AliasPrep.preservesWires_mul hPresB_all (preservesWires_embed_reflMid_zc20 rMain _ S₂))
        hPresF_all)

theorem r55_gearCert (d bQPE sUb K : ℕ) (hd : d ≤ 10 := by decide) (hK : 1 ≤ K := by decide)
    (hs : 160 - d ≤ sUb := by decide)
    (hsIn : combARem 8 18 4 14 - 2 ≤ 159 - d := by decide)
    (hk1 : max 144 (121 + 33) ≤ 159 - d := by decide)
    (hkT : max 146 (121 + 33) ≤ 159 - d := by decide)
    (hUb : 159 - d ≤ sUb := by decide)
    (hs87 : 0 + 87 ≤ sUb := by decide)
    (hk4 : 68 ≤ 159 - d := by decide) :
    ∃ u : FGWalkU (mOutUB 8) (mMidUB 18),
      CleanWalkRefl2At bQPE 8 18 4 14 0 sUb (by decide) (by decide) () u
        (r55GearCirc d bQPE sUb K hd hs hsIn hk1 hkT hUb hs87 hk4) ∧
      TailShiftThreeGear.WalkKStepRefl2InvErrLe 8 18 K mainUB u 0 := by
  let rMain := combWalkCatRegAt bQPE 8 18 4 14 0 sUb
  let rScrUb := combScrUbRegAt bQPE 8 18 4 14 0 sUb
  have hMainScr := combWalkCatRegB_disjoint_scr bQPE 8 18 4 14 0 sUb
  obtain ⟨sF, hs1, hsF_pres, hsF_eq, _, _, _⟩ :=
    cleanRealizesSetCompactSelect55NoNegSliceDyn d hd false hs () 8 18 (by decide)
      rMain rScrUb hMainScr
  obtain ⟨sB, hs2, hsB_pres, hsB_eq, _, _, _⟩ :=
    cleanRealizesSetCompactSelect55NoNegSliceDyn d hd true hs () 8 18 (by decide)
      rMain rScrUb hMainScr
  have legs := bellAsymLegsMain mainKeep9HGadget400LoadBundle d hd bQPE sUb hs hk1 hkT
    hsF_pres hsB_pres
  have hClean := cleanWalkRefl2At_bellSuperNoNeg2455Dyn_asym d hd K hK (by decide) hs hsIn
    legs hs1 hs2
    (disjoint_supportInner18TurnDyn (mainKeep9HGadget400LoadCirc Unit) (Mag30Circ2.t72 Unit)
      (Mag30Circ2.t72 Unit) pi128Equiv rMain rScrUb hkT (by omega) hMainScr ())
    (fun _ ↦ Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨disjoint_supportInner18Step1Dyn (mainKeep9HGadget400LoadCirc Unit)
          (Mag30Circ2.t72 Unit) pi128Equiv rMain rScrUb hk1 (by omega) hMainScr (),
         disjoint_supportInner18Step4ColdDyn (Mag30Circ2.t72 Unit) pi128Equiv rMain rScrUb
          (kInner := 159 - d) hk4 (by omega) hMainScr ()⟩,
       disjoint_bell_onRegister_out_slice (by omega) (by omega) hs87 _ _⟩,
      disjoint_bell_onRegister_out_slice (by omega) (by omega) hs87 _ _⟩)
  have h1 := Select55PureBridge.walkRefl2InvErrLe_noNegDNeg55_ideal
    (outer8PrepOutWordImpl mag8To23Word17) prepMidSpinFactoredMainPrepMid
    mainPrepMid_vanish_ge30 isValidDNegBit_routerHot128 hsF_eq hsB_eq
  exact ⟨_, hClean, Select55PureBridge.walkKStepRefl2InvErrLe_zero_of_exact hK (by
    rw [mainUB, mainUB_eq]
    exact h1)⟩

theorem fast7gSevenGearCert :
    SymbolicSevenGearCert 8 18 4 14 45 384 149 160 160 160 160 159 156
      (by decide) (by decide) () mainUB
      (r55GearCirc 0 2 160 16384) (r55GearCirc 0 2 160 14720)
      (r55GearCirc 0 3 160 1664) (r55GearCirc 0 3 160 6528)
      (r55GearCirc 0 4 160 1664) (r55GearCirc 0 4 160 2432)
      (r55GearCirc 0 5 160 1664) (r55GearCirc 0 5 160 384)
      (r55GearCirc 1 6 159 1024) p4B_333
      (r55GearCirc 4 3 156 128) pRefl2F333
      0 0 0 0 0 0 0 0 0 0 0 0 := by
  obtain ⟨u0A, hc0A, hi0A⟩ := r55_gearCert 0 2 160 16384
  obtain ⟨u0B, hc0B, hi0B⟩ := r55_gearCert 0 2 160 14720
  obtain ⟨u1A, hc1A, hi1A⟩ := r55_gearCert 0 3 160 1664
  obtain ⟨u1B, hc1B, hi1B⟩ := r55_gearCert 0 3 160 6528
  obtain ⟨u2A, hc2A, hi2A⟩ := r55_gearCert 0 4 160 1664
  obtain ⟨u2B, hc2B, hi2B⟩ := r55_gearCert 0 4 160 2432
  obtain ⟨u3A, hc3A, hi3A⟩ := r55_gearCert 0 5 160 1664
  obtain ⟨u3B, hc3B, hi3B⟩ := r55_gearCert 0 5 160 384
  obtain ⟨u4A, hc4A, hi4A⟩ := r55_gearCert 1 6 159 1024
  obtain ⟨uM, hcM, hiM⟩ := r55_gearCert 4 3 156 128
  let rMain := combWalkCatRegAt 16 8 18 4 14 0 149
  let rScrUb := combScrUbRegAt 16 8 18 4 14 0 149
  have hMainScr := combWalkCatRegB_disjoint_scr 16 8 18 4 14 0 149
  obtain ⟨sF, hs1, hsF_pres, hsF_eq, _, _, _⟩ :=
    cleanRealizesSetCompactSelect57NoNegD11SliceDyn 11 (by decide) false (by decide) () 8 18
      (by decide) rMain rScrUb hMainScr
  obtain ⟨sB, hs2, hsB_pres, hsB_eq, _, _, _⟩ :=
    cleanRealizesSetCompactSelect57NoNegD11SliceDyn 11 (by decide) true (by decide) () 8 18
      (by decide) rMain rScrUb hMainScr
  have legsF := bellAsymLegsMain_d11_low25 hsF_pres hsB_pres
  have hTurnSuppF : Disjoint
      (pTurnAt (OneHot14LoadCirc2.hgLow25 Unit) 16 149 148 (by decide) (by decide)).support
      (bellForbidSet 16 8 18 4 14 0 149 148 (by decide)) :=
    disjoint_supportInner18TurnDyn (OneHot14LoadCirc2.hgLow25 Unit) (Mag30Circ2.t72 Unit)
      (Mag30Circ2.t72 Unit) pi128Equiv rMain rScrUb (by decide) (by decide) hMainScr ()
  have hcF : CleanWalkRefl2 8 18 4 14 0 149 (by decide) (by decide) ()
      (asymURefl2 (outer8PrepOutWordImpl mag8To23Word17) mainPrepMid
        Pi145CompactRouter.hot128NegBit2 sF sB) pRefl2F333 :=
    cleanWalkRefl2At_bellRefl2NoNeg57D11CompDyn_asym 11 (by decide) (by decide) (by decide)
      (by decide) legsF hs1 hs2 hTurnSuppF
  have hiF : WalkRefl2InvErrLe 8 18 mainUB
      (asymURefl2 (outer8PrepOutWordImpl mag8To23Word17) mainPrepMid
        Pi145CompactRouter.hot128NegBit2 sF sB) 0 := by
    rw [mainUB, mainUB_eq]
    exact walkRefl2InvErrLe_noNegDNeg_gen (outer8PrepOutWordImpl mag8To23Word17)
      prepMidSpinFactoredMainPrepMid mainPrepMid_vanish_ge30
      isValidDNegBit_routerHot128 hsF_eq hsB_eq false fun h ↦ Bool.noConfusion h
  exact ⟨⟨u0A, u0B, u1A, u2A, u3A, u4A, uM, _,
    0, 0, 0, 0, 0, 0, 0, 0,
    hc0A, hc0B, hc1A, hc2A, hc3A, hc4A, hcM, hcF,
    le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    hi0A, hi0B, hi1A, hi2A, hi3A, hi4A, hiM, hiF,
    le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    PeelSlotBCert.of_odd hc1B le_rfl hi1B le_rfl,
    PeelSlotBCert.of_odd hc2B le_rfl hi2B le_rfl,
    PeelSlotBCert.of_odd hc3B le_rfl hi3B le_rfl,
    PeelSlotBCert.of_even (by decide) (by decide) () mainUB p4B_333 (by decide) le_rfl⟩⟩

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearWalk333
end
