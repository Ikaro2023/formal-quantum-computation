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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearC
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.NoNegSOSAndSuperWalk
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145Select24
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellPersistCore
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellAsymCore
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145SOSPermBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsA
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsC
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HadWMux23SOSBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Low27HGadget
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.HGadgetPrepOutOuter8
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Outer8TwoRotWalk
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TwoGearQPE

/-!
# `334`-Qubit `wOuter = 8, wInner2 = 18` Three-Gear Tail-Shift Super-Walk

Assembles the `M = 46719` (`m2 = 10`, `m1 = 7`, `nStd = 44`, `kTail = 640`, `tShift = 56`)
three-gear tail-shift QPE program on `334` total qubits (`218` ancillas, `sRem = 150`) combining:
- `17-T` outer angle word `mag8To23Word17` with `H`-gadget `PREP_out` (`319 T` fwd, `279 T` bwd),
- `390-T` (`33`-scratch) / `434-T` (`27`-scratch) co-optimized `keep9` `H`-gadget one-hot QROM,
- `72-T` factored inner `Mag30` (`Mag30Circ2.t72`) and `46-T` Hadamard W-state `23`-item mux,
- `55`-AND `π145` Bell-singlet `SELECT`
  (`bellSuperNoNeg55CompDyn` / `bellRefl2NoNeg_se55CompDyn`),
- `Fast12603` IQFT and `threeGearWin_46719_10_7` (`141,700 T`) window preparer.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MainInner18SuperWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit Real HermitianMat CoherentAlias CleanDyn AliasPrep
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open TopIntegrationBridge Phase2MidSandwich ReordOuter13Bridge
open HGadgetPrepOutOuter8 Pi145Fast2RotCore Outer8Pi145Compact2RotOuter
open Inner18Symp14Walk Pi145SOSPermBridge
open Inner18HadWSuperLegsA Inner18HadWSuperLegsC Inner18HadWSuperLegs
open MainLow27HGadget HadWMux23SOSBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.NoNegDNegSOSAndSuperWalk
open Pi145CompactSelect24 BellAsymCore BellSuperLegSplice
open BellPersistCore BellPersistSuperWalk ThreeGearBellSuper
open TailShiftThreeGear TailShiftWindow46847 TailShiftBox
open TwoGearQPEPhase5 MobiusOptSubcube163Walk
open CompactTuned162StepZeroCmp20 SelectSwapQROM
open Inner18HadWSuperLegsB LowBitPi145Select
open HadWStateMux25CompactA Outer8Pi145Compact2RotDyn StepAnfAndCoin14Core
open Cat11CompactPhase2Bridge ZeroRcHotPrepMid21Fast StepKeep9Symp14Data
open QuantizedFactoredMag30 MidReflCtxRetain
open CompactZeroCmp20OuterParam StepOuter8Pi145Outer
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance instNeZeroTwoPowMain (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

theorem ite_pos_3 {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  split_ifs
  rfl

theorem ite_neg_3 {α : Sort*} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by
  split_ifs
  rfl

/-! ## Section 1A: `[DecidableEq Var]`-Only Reindexing from `Unit` -/

/-- Reindex classical variables of a `DynamicCircuit` from `Unit` to `v : Var`. -/
def instUnitVar {Var : Type} {n : ℕ} (v : Var) : DynamicCircuit Unit n → DynamicCircuit Var n
  | .circuit c => .circuit c
  | .measure _ r => .measure v r
  | @DynamicCircuit.qIf _ _ cond hdec t f =>
      @DynamicCircuit.qIf _ _ (fun σ ↦ cond (fun _ ↦ σ v)) (fun σ ↦ hdec (fun _ ↦ σ v))
        (instUnitVar v t) (instUnitVar v f)
  | .seq p₁ p₂ => .seq (instUnitVar v p₁) (instUnitVar v p₂)

theorem wp_circuit_pull {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) :
    ∀ (c : Circuit n) (Θ : QCAssertion Unit (2 ^ n)),
      wp (Var := Var) c.compile (fun σ ↦ Θ (fun _ ↦ σ v)) =
        fun σ ↦ wp (Var := Unit) c.compile Θ (fun _ ↦ σ v)
  | .identity, _ => rfl
  | .gate _ _, _ => rfl
  | .seq c₁ c₂, Θ => by
      change wp c₁.compile (wp c₂.compile _) = fun σ ↦ wp c₁.compile (wp c₂.compile Θ) _
      rw [wp_circuit_pull v c₂ Θ, wp_circuit_pull v c₁ (wp c₂.compile Θ)]

private theorem wp_qMeasure_coe_local {Var : Type} [DecidableEq Var] {d i : ℕ} [NeZero d]
    (ℳ : Measurement d i) (x : Var) (Θ : QCAssertion Var d) (σ : Store Var) :
    (wp (.qMeasure x ℳ) Θ σ).1 =
      ∑ o : Fin i, HermitianMat.conj (ℳ.1 o)ᴴ (Θ (Store.subst σ x (↑o.1))).1 := rfl

theorem wp_instUnitVar {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) :
    ∀ (p : DynamicCircuit Unit n) (Θ : QCAssertion Unit (2 ^ n)),
      wp (instUnitVar v p).compile (fun σ ↦ Θ (fun _ ↦ σ v)) =
        fun σ ↦ wp p.compile Θ (fun _ ↦ σ v)
  | .circuit c, Θ => wp_circuit_pull v c Θ
  | .measure u r, Θ => by
      cases u
      funext σ
      apply Subtype.ext
      simp only [instUnitVar, DynamicCircuit.compile, QProg.measureRegister,
        wp_qMeasure_coe_local, CompleteMeasurement.toMeasurement_coe]
      congr 1
      funext o
      have hsub : (fun _ : Unit ↦ Store.subst σ v (↑o.1) v) =
          Store.subst (fun _ : Unit ↦ σ v) () (↑o.1) := by
        funext w
        cases w
        simp [Store.subst]
      exact congrArg (fun τ ↦ HermitianMat.conj (r.computationalBasisMeasurement.1 o)ᴴ (Θ τ).1) hsub
  | @DynamicCircuit.qIf _ _ cond hdec t f, Θ => by
      funext σ
      dsimp only [instUnitVar, DynamicCircuit.compile, wp_qIf]
      split_ifs with h
      · exact congrFun (wp_instUnitVar v t Θ) σ
      · exact congrFun (wp_instUnitVar v f Θ) σ
  | .seq p₁ p₂, Θ => by
      dsimp only [instUnitVar, DynamicCircuit.compile, wp_qSeq]
      rw [wp_instUnitVar v p₂ Θ, wp_instUnitVar v p₁ (wp p₂.compile Θ)]

theorem realizes_instUnitVar {Var : Type} [DecidableEq Var] {n k m : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTarget : QRegister k n) (outcomes : Finset (Fin (2 ^ k)))
    (rAnc : QRegister m n) (hdisj : rTarget.DisjointWires rAnc)
    (U : Unitary (2 ^ (k + m))) (p : DynamicCircuit Unit n)
    (hp : RealizesUnitaryFromBasisOutcomesAndZeroWorkspace
      rTarget outcomes rAnc hdisj U p.compile) :
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rTarget outcomes rAnc hdisj U
      (instUnitVar v p).compile := by
  intro M σ
  have hM := hp M (fun _ ↦ σ v)
  have hwp : wp (instUnitVar v p).compile (fun _ ↦ M) =
      fun τ ↦ wp p.compile (fun _ ↦ M) (fun _ ↦ τ v) :=
    wp_instUnitVar v p (fun _ ↦ M)
  rw [hwp]
  exact hM

/-! ## Section 1B: Parametric `(wOuter = 8, wInner2 = 18)` Outer & Inner Walk Legs (`Var = Unit`) -/

/-- `17-T` `Clifford+T` outer magnitude word (`orthGrover184L1 ≤ 24 / 10 ^ 11`). -/
def mag8To23Word17 : List OuterWeights.GroverUniform.Gate1 :=
  [.H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
   .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .X]

@[simp]
theorem wordCountTMag8To23Word17 :
    OuterWeights.GroverUniform.wordCountT mag8To23Word17 = 17 := rfl

theorem checkOrthGrover184L1Word_word17 :
    checkOrthGrover184L1Word 17 24 (10 ^ 11) mag8To23Word17 = true := by
  decide +kernel

/-- Placement `(rOut, rScr[0..87))` inside `combQubitsAt bQPE 8 18 4 14 0 sUb`. -/
def plOut87At (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    QRegister (mOutUB 8 + 87) (combQubitsAt bQPE 8 18 4 14 0 sUb) :=
  (combOutRegB bQPE 8 18 4 14 0 sUb).concat
    ((combScrUbRegAt bQPE 8 18 4 14 0 sUb).slice 0 87 hs87)
    ((combOutRegB_disjoint_scr bQPE 8 18 4 14 0 sUb).compose_right _)

/-- Forward `Word17` `H`-gadget `PREP_out` (`319 T`, `0 TOFF`) on `rScr[0..87)`. -/
def pOutFwdAt (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    DynamicCircuit Unit (combQubitsAt bQPE 8 18 4 14 0 sUb) :=
  (hGadgetOuter8PrepOutWordFwdDyn mag8To23Word17 ()
    (QRegister.block 0 (mOutUB 8) (by decide)) (QRegister.block (mOutUB 8) 87 le_rfl) le_rfl
    (QRegister.block_disjoint_of_le 0 (mOutUB 8) (mOutUB 8) 87 (by decide) le_rfl le_rfl)
    ).onRegister (plOut87At bQPE sUb hs87)

/-- Backward `Word17` `H`-gadget `PREP_out†` (`279 T`, `0 TOFF`) on `rScr[0..87)`. -/
def pOutBwdAt (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    DynamicCircuit Unit (combQubitsAt bQPE 8 18 4 14 0 sUb) :=
  (hGadgetOuter8PrepOutWordBwdDyn mag8To23Word17 ()
    (QRegister.block 0 (mOutUB 8) (by decide)) (QRegister.block (mOutUB 8) 87 le_rfl) (by decide)
    (QRegister.block_disjoint_of_le 0 (mOutUB 8) (mOutUB 8) 87 (by decide) le_rfl le_rfl)
    ).onRegister (plOut87At bQPE sUb hs87)

@[simp]
theorem count_pOutFwdAt_toff (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    (pOutFwdAt bQPE sUb hs87).count .TOFF = 0 := by
  simp [pOutFwdAt, DynamicCircuit.count_onRegister]

@[simp]
theorem count_pOutFwdAt_t (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    (pOutFwdAt bQPE sUb hs87).count .T = 319 := by
  rw [pOutFwdAt, DynamicCircuit.count_onRegister, countHGadgetOuter8PrepOutWordFwdDyn_t,
    wordCountTMag8To23Word17]

@[simp]
theorem count_pOutBwdAt_toff (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    (pOutBwdAt bQPE sUb hs87).count .TOFF = 0 := by
  simp [pOutBwdAt, DynamicCircuit.count_onRegister]

@[simp]
theorem count_pOutBwdAt_t (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    (pOutBwdAt bQPE sUb hs87).count .T = 279 := by
  rw [pOutBwdAt, DynamicCircuit.count_onRegister, countHGadgetOuter8PrepOutWordBwdDyn_t,
    wordCountTMag8To23Word17]

/-- Step-1 `wInner2 = 18` inner mux leg at `(bQPE, sUb, kInner)`. -/
def pStep1At {sQrom tLoad14 : ℕ} (qrom : OneHot14LoadCirc2 Unit sQrom tLoad14)
    (bQPE sUb kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb) :
    DynamicCircuit Unit (combQubitsAt bQPE 8 18 4 14 0 sUb) :=
  inner18Step1Dyn qrom (Mag30Circ2.t72 Unit) pi128Equiv
    (combUBRegB bQPE 8 18 4 14 0 sUb) (combScrUbRegAt bQPE 8 18 4 14 0 sUb)
    kInner hk hUb ((combWalkCatRegB_disjoint_scr bQPE 8 18 4 14 0 sUb).compose_left _) ()

/-- Turnaround `wInner2 = 18` inner mux + `Hot128` `D_neg` leg at `(bQPE, sUb, kInner)`. -/
def pTurnAt {sQrom tLoad14 : ℕ} (qrom : OneHot14LoadCirc2 Unit sQrom tLoad14)
    (bQPE sUb kInner : ℕ) (hk : max 146 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb) :
    DynamicCircuit Unit (combQubitsAt bQPE 8 18 4 14 0 sUb) :=
  inner18TurnDyn qrom (Mag30Circ2.t72 Unit) (Mag30Circ2.t72 Unit) pi128Equiv
    (combUBRegB bQPE 8 18 4 14 0 sUb) (combScrUbRegAt bQPE 8 18 4 14 0 sUb)
    kInner hk hUb ((combWalkCatRegB_disjoint_scr bQPE 8 18 4 14 0 sUb).compose_left _) ()

/-- Step-4 cold `wInner2 = 18` inner uncomputation leg at `(bQPE, sUb, kInner)`. -/
def pStep4At (bQPE sUb kInner : ℕ) (hk : 68 ≤ kInner) (hUb : kInner ≤ sUb) :
    DynamicCircuit Unit (combQubitsAt bQPE 8 18 4 14 0 sUb) :=
  inner18Step4ColdDyn (Mag30Circ2.t72 Unit) pi128Equiv
    (combUBRegB bQPE 8 18 4 14 0 sUb) (combScrUbRegAt bQPE 8 18 4 14 0 sUb)
    kInner hk hUb ((combWalkCatRegB_disjoint_scr bQPE 8 18 4 14 0 sUb).compose_left _) ()

@[simp]
theorem count_pStep1At_toff {sQrom tLoad14 : ℕ} (qrom : OneHot14LoadCirc2 Unit sQrom tLoad14)
    (bQPE sUb kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb) :
    (pStep1At qrom bQPE sUb kInner hk hUb).count .TOFF = 0 := by
  rw [pStep1At]
  exact countInner18Step1Dyn_toff qrom (Mag30Circ2.t72 Unit) pi128Equiv _ _ kInner hk hUb _ ()

@[simp]
theorem count_pStep1At_t {sQrom tLoad14 : ℕ} (qrom : OneHot14LoadCirc2 Unit sQrom tLoad14)
    (bQPE sUb kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb) :
    (pStep1At qrom bQPE sUb kInner hk hUb).count .T = 386 + tLoad14 := by
  rw [pStep1At, countInner18Step1Dyn_t]
  omega

@[simp]
theorem count_pTurnAt_toff {sQrom tLoad14 : ℕ} (qrom : OneHot14LoadCirc2 Unit sQrom tLoad14)
    (bQPE sUb kInner : ℕ) (hk : max 146 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb) :
    (pTurnAt qrom bQPE sUb kInner hk hUb).count .TOFF = 0 := by
  rw [pTurnAt]
  exact countInner18TurnDyn_toff qrom (Mag30Circ2.t72 Unit) (Mag30Circ2.t72 Unit) pi128Equiv _ _
    kInner hk hUb _ ()

@[simp]
theorem count_pTurnAt_t {sQrom tLoad14 : ℕ} (qrom : OneHot14LoadCirc2 Unit sQrom tLoad14)
    (bQPE sUb kInner : ℕ) (hk : max 146 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb) :
    (pTurnAt qrom bQPE sUb kInner hk hUb).count .T = 732 + tLoad14 := by
  rw [pTurnAt, countInner18TurnDyn_t]
  omega

@[simp]
theorem count_pStep4At_toff (bQPE sUb kInner : ℕ) (hk : 68 ≤ kInner) (hUb : kInner ≤ sUb) :
    (pStep4At bQPE sUb kInner hk hUb).count .TOFF = 0 := by
  rw [pStep4At]
  exact countInner18Step4ColdDyn_toff (Mag30Circ2.t72 Unit) pi128Equiv _ _ kInner hk hUb _ ()

@[simp]
theorem count_pStep4At_t (bQPE sUb kInner : ℕ) (hk : 68 ≤ kInner) (hUb : kInner ≤ sUb) :
    (pStep4At bQPE sUb kInner hk hUb).count .T = 366 := by
  rw [pStep4At, countInner18Step4ColdDyn_t]

/-! ## Section 2A: Concrete 4-Gear Super-Reflection Circuits & Top-Level Program (`Unit`) -/

/-! ## Section 2B: Wire Preservation & 4-Gear `CleanWalkRefl2At` / `CleanWalkRefl2` -/

/-- Unpermuted `24`-wire (`mMidUB 18`) `PREP_mid` unitary family (`72-T` `Mag30`). -/
noncomputable abbrev mainPrepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB 18) :=
  prepMid18FromSlice mux9AltBit keep9SliceTargetFn14 factoredMag30T72Circuit.eval

/-- Reference `(wOuter = 8, wInner2 = 18)` block-encoding walk unitary `mainUB2`. -/
noncomputable def mainUB2 : Unitary (2 ^ nUB 8 18) :=
  ubDirectXo7PureUnitary
    (outer8PrepOutWordImpl mag8To23Word17)
    (genPi128PrepMid18Of mux9AltBit keep9SliceTargetFn14 pi128Equiv
      factoredMag30T72Circuit.eval)
    (idealPi145SelectPure 8 18)

theorem mainUB_eq :
    mainUB2 = ubDirectXo7PureUnitary (outer8PrepOutWordImpl mag8To23Word17)
      (fun rc ↦ mainPrepMid (pi128Equiv rc)) (idealPi145SelectPure 8 18) :=
  congrArg (fun f ↦ ubDirectXo7PureUnitary _ f _) (funext fun _ ↦ rfl)

theorem preservesWires_conj_embedEquiv2 {N k : ℕ} {A : Operator (2 ^ N)}
    {T : Finset (Wire N)} (hA : AliasPrep.PreservesWires A T)
    (rSub : QRegister k N) (hSub : rSub.image ⊆ T)
    (U : Unitary (2 ^ k)) (perm : Equiv.Perm (BitAssignment k))
    (hUk : ∀ γ : BitAssignment k,
      U.1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (perm γ)) :
    AliasPrep.PreservesWires ((rSub.embedUnitary U)⁻¹.1 * A * (rSub.embedUnitary U).1) T := by
  let gFwd : BitAssignment N → BitAssignment N :=
    fun β ↦ Comparators.writeReg β rSub (perm (fun i ↦ β (rSub i)))
  let gInv : BitAssignment N → BitAssignment N :=
    fun β ↦ Comparators.writeReg β rSub (perm.symm (fun i ↦ β (rSub i)))
  have hgLeft (β : BitAssignment N) : gInv (gFwd β) = β := by
    funext w
    by_cases hw : w ∈ Set.range rSub.wires
    · obtain ⟨i, rfl⟩ := hw
      dsimp only [gInv, gFwd]
      rw [Comparators.writeReg_apply_reg]
      have hfn : (fun j ↦ Comparators.writeReg β rSub (perm fun u ↦ β (rSub u)) (rSub j)) =
          perm (fun u ↦ β (rSub u)) :=
        funext fun j ↦ Comparators.writeReg_apply_reg _ _ _ j
      rw [hfn, perm.symm_apply_apply]
    · dsimp only [gInv, gFwd]
      rw [Comparators.writeReg_apply_of_not_mem _ _ _ w hw,
        Comparators.writeReg_apply_of_not_mem _ _ _ w hw]
  have hgRight (β : BitAssignment N) : gFwd (gInv β) = β := by
    funext w
    by_cases hw : w ∈ Set.range rSub.wires
    · obtain ⟨i, rfl⟩ := hw
      dsimp only [gInv, gFwd]
      rw [Comparators.writeReg_apply_reg]
      have hfn : (fun j ↦ Comparators.writeReg β rSub (perm.symm fun u ↦ β (rSub u)) (rSub j)) =
          perm.symm (fun u ↦ β (rSub u)) :=
        funext fun j ↦ Comparators.writeReg_apply_reg _ _ _ j
      rw [hfn, perm.apply_symm_apply]
    · dsimp only [gInv, gFwd]
      rw [Comparators.writeReg_apply_of_not_mem _ _ _ w hw,
        Comparators.writeReg_apply_of_not_mem _ _ _ w hw]
  have hUinvk (γ : BitAssignment k) :
      (U⁻¹).1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (perm.symm γ) := by
    have h1 := congrArg (U⁻¹.1.mulVec ·) (hUk (perm.symm γ))
    rw [perm.apply_symm_apply, Matrix.mulVec_mulVec,
      show (U⁻¹).1 * U.1 = 1 from congrArg Subtype.val (inv_mul_cancel U),
      Matrix.one_mulVec] at h1
    exact h1.symm
  have hWFwd (β : BitAssignment N) :
      (rSub.embedUnitary U).1.mulVec (SelectSwapQROM.ket β) =
        SelectSwapQROM.ket (gFwd β) := by
    rw [QRegister.embedUnitary_val, Comparators.embedMatrix_mulVec_ket]
    have hcol (l : Fin (2 ^ k)) :
        U.1 l (Comparators.localIdx rSub β) =
          (U.1.mulVec (SelectSwapQROM.ket (fun i ↦ β (rSub i)))) l := by
      change U.1 l _ = (U.1.mulVec (basisState (Comparators.localIdx rSub β))) l
      simp [basisState]
    simp_rw [hcol, hUk (fun i ↦ β (rSub i))]
    rw [Finset.sum_eq_single ((basisBits k).symm (perm (fun i ↦ β (rSub i))))]
    · simp only [SelectSwapQROM.ket, basisState, Pi.single_eq_same, one_smul,
        SelectSwapQROM.basisBits_symm]
      rfl
    · intro l _ hl
      simp [SelectSwapQROM.ket, basisState, Pi.single_eq_of_ne hl]
    · simp
  have hWInvVec (β : BitAssignment N) :
      ((rSub.embedUnitary U)⁻¹).1.mulVec (SelectSwapQROM.ket β) =
        SelectSwapQROM.ket (gInv β) := by
    rw [← QRegister.embedUnitary_inv, QRegister.embedUnitary_val,
      Comparators.embedMatrix_mulVec_ket]
    have hcol (l : Fin (2 ^ k)) :
        (U⁻¹).1 l (Comparators.localIdx rSub β) =
          ((U⁻¹).1.mulVec (SelectSwapQROM.ket (fun i ↦ β (rSub i)))) l := by
      change (U⁻¹).1 l _ = ((U⁻¹).1.mulVec (basisState (Comparators.localIdx rSub β))) l
      simp [basisState]
    simp_rw [hcol, hUinvk (fun i ↦ β (rSub i))]
    rw [Finset.sum_eq_single ((basisBits k).symm (perm.symm (fun i ↦ β (rSub i))))]
    · simp only [SelectSwapQROM.ket, basisState, Pi.single_eq_same, one_smul,
        SelectSwapQROM.basisBits_symm]
      rfl
    · intro l _ hl
      simp [SelectSwapQROM.ket, basisState, Pi.single_eq_of_ne hl]
    · simp
  have hWInvAny (vec : Fin (2 ^ N) → ℂ) (i : Fin (2 ^ N)) :
      (((rSub.embedUnitary U)⁻¹).1 *ᵥ vec) i =
        vec ((basisBits N).symm (gFwd (basisBits N i))) := by
    have hv : vec = ∑ m : Fin (2 ^ N), vec m • SelectSwapQROM.ket (basisBits N m) := by
      funext x
      simp [SelectSwapQROM.ket, basisState, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_sum, Finset.sum_apply]
    simp_rw [Matrix.mulVec_smul, hWInvVec, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ((basisBits N).symm (gFwd (basisBits N i)))]
    · rw [SelectSwapQROM.ket, basisState, SelectSwapQROM.basisBits_symm, hgLeft,
        SelectSwapQROM.symm_basisBits, Pi.single_eq_same, mul_one]
    · intro m _ hm
      have hne : (basisBits N).symm (gInv (basisBits N m)) ≠ i := by
        intro heq
        apply hm
        have h1 := congrArg (fun x ↦ (basisBits N).symm (gFwd (basisBits N x))) heq
        simpa only [SelectSwapQROM.basisBits_symm, hgRight,
          SelectSwapQROM.symm_basisBits] using h1
      simp [SelectSwapQROM.ket, basisState, hne.symm]
    · simp
  intro i j ⟨w, hw, hij⟩
  have hentry : ((rSub.embedUnitary U)⁻¹.1 * A * (rSub.embedUnitary U).1) i j =
      A ((basisBits N).symm (gFwd (basisBits N i)))
        ((basisBits N).symm (gFwd (basisBits N j))) := by
    have hcol : ((rSub.embedUnitary U)⁻¹.1 * A * (rSub.embedUnitary U).1) i j =
        (((rSub.embedUnitary U)⁻¹.1 * A * (rSub.embedUnitary U).1) *ᵥ
          SelectSwapQROM.ket (basisBits N j)) i := by
      simp [SelectSwapQROM.ket, basisState]
    rw [hcol, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hWInvAny, hWFwd]
    change (A *ᵥ SelectSwapQROM.ket (gFwd (basisBits N j))) _ = _
    simp [SelectSwapQROM.ket, basisState]
  rw [hentry]
  apply hA
  simp only [SelectSwapQROM.basisBits_symm]
  by_contra hallNot
  have hall (w' : Wire N) (hw' : w' ∈ T) :
      gFwd (basisBits N i) w' = gFwd (basisBits N j) w' :=
    not_ne_iff.mp fun hne ↦ hallNot ⟨w', hw', hne⟩
  apply hij
  have hlocEq : (fun u ↦ gFwd (basisBits N i) (rSub u)) =
      fun u ↦ gFwd (basisBits N j) (rSub u) :=
    funext fun u ↦ hall (rSub u) (hSub ((QRegister.mem_image rSub _).mpr ⟨u, rfl⟩))
  have hgEq : gInv (gFwd (basisBits N i)) w = gInv (gFwd (basisBits N j)) w := by
    by_cases hwR : w ∈ Set.range rSub.wires
    · obtain ⟨u, rfl⟩ := hwR
      change Comparators.writeReg (gFwd (basisBits N i)) rSub _ (rSub u) =
        Comparators.writeReg (gFwd (basisBits N j)) rSub _ (rSub u)
      rw [Comparators.writeReg_apply_reg, Comparators.writeReg_apply_reg, hlocEq]
    · change Comparators.writeReg (gFwd (basisBits N i)) rSub _ w =
        Comparators.writeReg (gFwd (basisBits N j)) rSub _ w
      rw [Comparators.writeReg_apply_of_not_mem _ _ _ w hwR,
        Comparators.writeReg_apply_of_not_mem _ _ _ w hwR]
      exact hall w hw
  rwa [hgLeft, hgLeft] at hgEq

theorem outerConjPreservesZero_of_disjoint2 {wOuter kZeroOut kInit : ℕ}
    (hkOut : kZeroOut ≤ wOuter) (rInit : QRegister kInit (mOutUB wOuter))
    (hDisj : rInit.DisjointWires (outZeroPrefixReg wOuter kZeroOut hkOut))
    (uInit : Unitary (2 ^ kInit)) :
    OuterConjPreservesZero wOuter kZeroOut hkOut (rInit.embedUnitary uInit) := by
  intro N rOut S_ext hDisjOut U_core hPres
  let S_all := S_ext ∪ (rOut.compose (outZeroPrefixReg wOuter kZeroOut hkOut)).image
  have hSubAll : S_all ⊆ rOut.image ∪ S_ext :=
    Finset.union_subset Finset.subset_union_right
      ((rOut.image_compose_subset _).trans Finset.subset_union_left)
  have hCoreSub : AliasPrep.PreservesWires U_core S_all :=
    fun i j ⟨w, hw, hne⟩ ↦ hPres i j ⟨w, hSubAll hw, hne⟩
  have hDisjInit : Disjoint (rOut.compose rInit).image S_all := by
    refine Finset.disjoint_union_right.mpr
      ⟨Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut,
       SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr
         fun i j hij ↦ hDisj.ne i j (rOut.wires.injective hij))⟩
  have hW : AliasPrep.PreservesWires (rOut.embedUnitary (rInit.embedUnitary uInit)).1 S_all := by
    rw [← QRegister.embedUnitary_compose]
    exact AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S_all hDisjInit
  have hWinv :
      AliasPrep.PreservesWires ((rOut.embedUnitary (rInit.embedUnitary uInit))⁻¹).1 S_all := by
    rw [← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_inv,
      ← QRegister.embedUnitary_compose]
    exact AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S_all hDisjInit
  exact AliasPrep.preservesWires_mul (AliasPrep.preservesWires_mul hWinv hCoreSub) hW

theorem outerConjPreservesZero_mul_left_invol2 {wOuter kZeroOut : ℕ} {hkOut : kZeroOut ≤ wOuter}
    {uPerm uRest : Unitary (2 ^ mOutUB wOuter)}
    (g : BitAssignment (mOutUB wOuter) → BitAssignment (mOutUB wOuter))
    (hgInvol : ∀ γ, g (g γ) = γ)
    (hPerm : ∀ γ : BitAssignment (mOutUB wOuter),
      uPerm.1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (g γ))
    (hRest : OuterConjPreservesZero wOuter kZeroOut hkOut uRest) :
    OuterConjPreservesZero wOuter kZeroOut hkOut (uPerm * uRest) := by
  intro N rOut S_ext hDisjOut U_core hPres
  let perm : Equiv.Perm (BitAssignment (mOutUB wOuter)) :=
    { toFun := g, invFun := g, left_inv := hgInvol, right_inv := hgInvol }
  have hPermPres := preservesWires_conj_embedEquiv2 hPres rOut Finset.subset_union_left
    uPerm perm hPerm
  have hStep := hRest rOut S_ext hDisjOut hPermPres
  have hRewrite :
      (rOut.embedUnitary (uPerm * uRest))⁻¹.1 * U_core * (rOut.embedUnitary (uPerm * uRest)).1 =
      (rOut.embedUnitary uRest)⁻¹.1 *
        ((rOut.embedUnitary uPerm)⁻¹.1 * U_core * (rOut.embedUnitary uPerm).1) *
        (rOut.embedUnitary uRest).1 := by
    rw [rOut.embedUnitary_mul, _root_.mul_inv_rev]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rwa [hRewrite]

theorem outerConjPreservesZeroOuter8PrepOutWordImpl
    (rotWord : List OuterWeights.GroverUniform.Gate1) :
    OuterConjPreservesZero 8 4 (by decide) (outer8PrepOutWordImpl rotWord) := by
  rw [outer8PrepOutWordImpl, outer8PrepOutUnit, mul_assoc]
  exact outerConjPreservesZero_mul_left_invol2 gromCswap17Bits gromCswap17Bits_invol
    gromCswap17_mulVec_ket
    (outerConjPreservesZero_mul_left_invol2 gromXor17Bits gromXor17Bits_invol
      gromXor17_mulVec_ket
      (outerConjPreservesZero_of_disjoint2 (by decide) nonAlt13Loc (by decide)
        (init13Unitary _)))

theorem prepMidSpinFactoredMainPrepMid : PrepMidSpinFactored mainPrepMid :=
  ⟨core23 mux9AltBit keep9SliceTargetFn14 factoredMag30T72Circuit.eval, fun _ ↦ rfl⟩

theorem mainPrepMid_vanish_ge30 (rc : Fin 126) (m : Fin (2 ^ mMidUB 18))
    (hm : 30 ≤ ((rBLoc 18).extractIndex m).val) :
    (mainPrepMid ⟨rc.val, by omega⟩).1 m 0 = 0 := by
  by_contra hne
  exact absurd
    (b_lt_30_ofPrepMid18FromSliceKeep9_ne_zero mux9AltBit
      factoredMag30T72Circuit_vanish ⟨rc.val, by omega⟩ m hne)
    (by omega)

theorem inner18Mfwd_eqAsymMidMux :
    inner18Mfwd 8 pi128Equiv factoredMag30T72Circuit.eval = asymMidMux 8 18 mainPrepMid :=
  congrArg₂ (· * ·) (muxCongr (CoherentAlias.qreg_ext fun _ ↦ rfl) rfl _ _ fun _ ↦ rfl)
    (muxCongr rfl rfl _ _ fun _ ↦ rfl)

theorem isValidDNegBit_routerHot128 : IsValidDNegBit Pi145CompactRouter.hot128NegBit2 := by
  refine ⟨fun xo' b hx hb ↦ ?_, fun xo' b hx ↦ ?_⟩
  · rw [Pi145CompactRouter.hot128NegBit_eq_default_of_lt30_or_ge126 _ _ (Or.inl hb),
      Pi145CompactRouter.defaultNegBit, decide_eq_true ⟨hx, hb⟩, Bool.true_and]
  · rw [Pi145CompactRouter.hot128NegBit_eq_default_of_lt30_or_ge126 _ _ (Or.inr hx),
      Pi145CompactRouter.defaultNegBit, decide_eq_false (by omega), Bool.false_and]

theorem hot128NegUB_eqDNegUB :
    hot128NegUB 8 = dNegUB 8 18 Pi145CompactRouter.hot128NegBit2 := by
  refine Subtype.ext <| matrix_eq_of_mulVec_single fun g ↦ ?_
  have hL : (hot128NegUB 8).1 *ᵥ Pi.single g 1 =
      (if Pi145CompactRouter.hot128NegBit2
          ((rXoLoc 8).extractIndex ((rOutUB 8 18).extractIndex g))
          ((rBLoc 18).extractIndex ((rMidUB 8 18).extractIndex g))
        then (-1 : ℂ) else 1) • Pi.single g 1 := by
    unfold hot128NegUB Pi145CompactRouter.hot128NegRegUnitary
      Pi145CompactRouter.hot128NegUnitary
    have hk := Pi145CompactRouter.embedNegPh13_ket Pi145CompactRouter.hot128NegBit2
      (rXoUB 8 18) ((rMidUB 8 18).compose (rBLoc 18))
      (((disjoint_rOutUB_rMidUB 8 18).compose_left _).compose_right _)
      (basisBits (nUB 8 18) g)
    have hXo : CircuitModular.UnsignedGivens.localIdx (rXoUB 8 18)
        (basisBits (nUB 8 18) g) = (rXoLoc 8).extractIndex ((rOutUB 8 18).extractIndex g) :=
      QRegister.extractIndex_compose (rOutUB 8 18) (rXoLoc 8) g
    have hB : CircuitModular.UnsignedGivens.localIdx
        ((rMidUB 8 18).compose (rBLoc 18)) (basisBits (nUB 8 18) g) =
        (rBLoc 18).extractIndex ((rMidUB 8 18).extractIndex g) :=
      QRegister.extractIndex_compose (rMidUB 8 18) (rBLoc 18) g
    rw [hXo, hB, ← SelectSwapQROM.single_eq_ket g] at hk
    exact hk
  rw [hL]
  ext k
  rw [dNegUB_apply_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hgk : k = g
  · subst hgk
    rfl
  · simp [Pi.single_eq_of_ne hgk]

theorem preservesWires_conjPrepMid18FromSlice_set {N : ℕ}
    {U_sel : Operator (2 ^ N)} (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14)
    (uIdxImpl : Unitary (2 ^ 5)) (rMid : QRegister (mMidUB 18) N) (S₀ : Finset (Wire N))
    (hMidS₀ : Disjoint rMid.image S₀)
    (hPres : AliasPrep.PreservesWires U_sel (rMid.image ∪ S₀)) (rc : Fin (2 ^ 7)) :
    AliasPrep.PreservesWires
      ((rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdxImpl rc))⁻¹.1 * U_sel *
        (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdxImpl rc)).1)
      (S₀ ∪ (rMid.compose mid18AliasOutReg).image) := by
  let rSig := rMid.compose (rSigInLoc 18)
  let rA23 := rMid.compose mid18Core23Reg
  let T23 := rA23.image ∪ S₀
  let S_all := S₀ ∪ (rMid.compose mid18AliasOutReg).image
  have hrA23_sub : rA23.image ⊆ rMid.image := rMid.image_compose_subset _
  have hSel23 : AliasPrep.PreservesWires U_sel T23 :=
    fun i j ⟨w, hw, hne⟩ ↦ hPres i j ⟨w, (Finset.union_subset_union_left hrA23_sub) hw, hne⟩
  have hDisjSig : Disjoint rSig.image T23 := by
    refine Finset.disjoint_union_right.mpr ⟨?_,
      Finset.disjoint_of_subset_left (rMid.image_compose_subset _) hMidS₀⟩
    refine SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr ?_)
    intro i j hij
    have hv := congrArg Fin.val (rMid.wires.injective hij)
    simp [rSigInLoc, mid18Core23Reg] at hv
    omega
  let U_H := rSig.embedUnitary (Circuit.H 0).eval
  let W_ms := (rA23.compose core23MuxSwap23Reg).embedUnitary
    (bitPermUnitary (pktMuxSwap23Perm mux9AltBit))
  let f := sliceFn rc
  let W_qrom := (rA23.compose core23Qrom19Reg).embedUnitary (aliasTableXorUnitary 5 14 f)
  let U_pkt := (rA23.compose core23PktReg).embedUnitary optCoin9Unitary
  let U_u := (rA23.compose core23IdxReg).embedUnitary uIdxImpl
  have hH : AliasPrep.PreservesWires ((U_H⁻¹).1 * U_sel * U_H.1) T23 := by
    rw [← QRegister.embedUnitary_inv]
    exact AliasPrep.preservesWires_mul
      (AliasPrep.preservesWires_mul
        (AliasPrep.preservesWires_embedMatrix_of_disjoint rSig _ T23 hDisjSig) hSel23)
      (AliasPrep.preservesWires_embedMatrix_of_disjoint rSig _ T23 hDisjSig)
  have hPresMS := AliasPrep.preservesWires_conj_embedBitPerm hH
    (rA23.compose core23MuxSwap23Reg)
    ((rA23.image_compose_subset _).trans Finset.subset_union_left)
    (pktMuxSwap23Perm mux9AltBit) (pktMuxSwap23Bits_invol mux9AltBit)
  have hPresQrom := AliasPrep.preservesWires_conj_embedBitPerm hPresMS
    (rA23.compose core23Qrom19Reg)
    ((rA23.image_compose_subset _).trans Finset.subset_union_left)
    ⟨aliasTableXorBits 5 14 f, aliasTableXorBits 5 14 f,
      aliasTableXorBits_self 5 14 f, aliasTableXorBits_self 5 14 f⟩
    (aliasTableXorBits_self 5 14 f)
  have hOutEq : rMid.compose mid18AliasOutReg = rA23.compose core23Out14Reg := by
    apply CoherentAlias.qreg_ext
    intro j
    simp [mid18AliasOutReg, rA23, mid18Core23Reg, core23Out14Reg]
  have hSubAll : S_all ⊆ T23 := by
    refine Finset.union_subset Finset.subset_union_right ?_
    dsimp only [T23]
    rw [hOutEq]
    exact (rA23.image_compose_subset _).trans Finset.subset_union_left
  have hQSub : AliasPrep.PreservesWires
      (W_qrom.1 * (W_ms.1 * ((U_H⁻¹).1 * U_sel * U_H.1) * W_ms.1) * W_qrom.1) S_all :=
    fun i j ⟨w, hw, hne⟩ ↦ hPresQrom i j ⟨w, hSubAll hw, hne⟩
  have hDisjA23S₀ : Disjoint rA23.image S₀ := Finset.disjoint_of_subset_left hrA23_sub hMidS₀
  have hDisjPktS : Disjoint (rA23.compose core23PktReg).image S_all := by
    dsimp only [S_all]
    rw [hOutEq]
    refine Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_of_subset_left (rA23.image_compose_subset _) hDisjA23S₀,
       SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr fun i j hij ↦ by
         have hv := congrArg Fin.val (rA23.wires.injective hij)
         simp only [core23PktReg, core23Out14Reg, QRegister.block_apply_val] at hv
         have := j.isLt
         omega)⟩
  have hDisjIdxS : Disjoint (rA23.compose core23IdxReg).image S_all := by
    dsimp only [S_all]
    rw [hOutEq]
    refine Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_of_subset_left (rA23.image_compose_subset _) hDisjA23S₀,
       SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr fun i j hij ↦ by
         have hv := congrArg Fin.val (rA23.wires.injective hij)
         simp only [core23IdxReg, core23Out14Reg, QRegister.block_apply_val] at hv
         have := i.isLt
         omega)⟩
  have hFac : rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdxImpl rc) =
      U_H * (W_ms * (W_qrom * (U_pkt * U_u))) := by
    simp only [prepMid18FromSlice, core23, coin9Perm23,
      pktMuxSwap23Unitary_eq_bitPermUnitary, U_H, W_ms, W_qrom, U_pkt, U_u, f, rSig, rA23,
      QRegister.embedUnitary_mul, QRegister.embedUnitary_compose, mul_assoc]
  have hWMS : W_ms⁻¹ = W_ms := by
    dsimp only [W_ms]
    rw [← QRegister.embedUnitary_inv, ← pktMuxSwap23Unitary_eq_bitPermUnitary,
      pktMuxSwap23Unitary_inv]
  have hWQ : W_qrom⁻¹ = W_qrom := by
    dsimp only [W_qrom]
    rw [← QRegister.embedUnitary_inv, aliasTableXorUnitary_inv]
  have hInv : (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdxImpl rc))⁻¹ =
      U_u⁻¹ * (U_pkt⁻¹ * (W_qrom * (W_ms * U_H⁻¹))) := by
    rw [hFac]
    simp only [_root_.mul_inv_rev, hWMS, hWQ, mul_assoc]
  have hMat :
      (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdxImpl rc))⁻¹.1 * U_sel *
        (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdxImpl rc)).1 =
      (U_u⁻¹).1 * ((U_pkt⁻¹).1 *
        (W_qrom.1 * (W_ms.1 * ((U_H⁻¹).1 * U_sel * U_H.1) * W_ms.1) * W_qrom.1) * U_pkt.1) *
        U_u.1 := by
    rw [hInv, hFac]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rw [hMat]
  have hPktInv : AliasPrep.PreservesWires (U_pkt⁻¹).1 S_all := by
    rw [← QRegister.embedUnitary_inv]
    exact AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S_all hDisjPktS
  have hIdxInv : AliasPrep.PreservesWires (U_u⁻¹).1 S_all := by
    rw [← QRegister.embedUnitary_inv]
    exact AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S_all hDisjIdxS
  exact AliasPrep.preservesWires_mul
    (AliasPrep.preservesWires_mul hIdxInv
      (AliasPrep.preservesWires_mul
        (AliasPrep.preservesWires_mul hPktInv hQSub)
        (AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S_all hDisjPktS)))
    (AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S_all hDisjIdxS)

theorem preservesWires_comm_proj {N k : ℕ} {A : Operator (2 ^ N)}
    {T : Finset (Wire N)} (hA : AliasPrep.PreservesWires A T)
    (r : QRegister k N) (hSub : r.image ⊆ T) (c : Fin (2 ^ k)) :
    A * r.basisOutcomeProjector c = r.basisOutcomeProjector c * A := by
  rw [r.basisOutcomeProjector_eq_diagonal]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hEq : r.extractIndex i = r.extractIndex j
  · rw [hEq]
    ring
  · have hDiff : ∃ u : Fin k, basisBits N i (r u) ≠ basisBits N j (r u) := by
      by_contra hall
      simp only [not_exists, Decidable.not_not] at hall
      apply hEq
      unfold QRegister.extractIndex
      congr 1
      funext u
      exact hall u
    obtain ⟨u, hu⟩ := hDiff
    rw [hA i j ⟨r u, hSub ((QRegister.mem_image r _).mpr ⟨u, rfl⟩), hu⟩, zero_mul, mul_zero]

theorem proj_mul_proj_ite {N k : ℕ} (r : QRegister k N) (c₁ c₂ : Fin (2 ^ k)) :
    r.basisOutcomeProjector c₁ * r.basisOutcomeProjector c₂ =
      if c₁ = c₂ then r.basisOutcomeProjector c₁ else 0 := by
  by_cases h : c₁ = c₂
  · subst h
    rw [ite_pos_3 rfl, r.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext g
    by_cases hg : r.extractIndex g = c₁ <;> simp [hg]
  · rw [ite_neg_3 h, r.basisOutcomeProjector_eq_diagonal, r.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext g
    by_cases hg : r.extractIndex g = c₁
    · rw [ite_pos_3 hg, ite_neg_3 (fun h₂ ↦ h (hg.symm.trans h₂)), mul_zero]
    · rw [ite_neg_3 hg, zero_mul]

theorem preservesWiresDirectXo7Sandwich18_out_scr_midZero {N wOuter kCat sUb : ℕ}
    (rMain : QRegister (nUB wOuter 18 + kCat) N) (rScr : QRegister sUb N)
    (hDisj : rMain.DisjointWires rScr)
    (sliceFn : Fin (2 ^ 7) → Fin (2 ^ 5) → BitAssignment 14) (uIdx : Unitary (2 ^ 5))
    (selectCat : Unitary (2 ^ (nUB wOuter 18 + kCat)))
    (hselPres : AliasPrep.PreservesWires (rMain.embedUnitary selectCat).1
      (((rMain.compose (rUBInCat wOuter 18 kCat)).compose (rAllUB wOuter 18)).image ∪ rScr.image)) :
    let rUB := rMain.compose (rUBInCat wOuter 18 kCat)
    let rOut := rUB.compose (rOutUB wOuter 18)
    let rMidZero := (rUB.compose (rMidUB wOuter 18)).compose (midZeroPrefixReg 18 14 (by decide))
    let M_impl := directXo7Mux18Of wOuter mux9AltBit sliceFn uIdx
    AliasPrep.PreservesWires
      (rMain.embedUnitary
        ((rUBInCat wOuter 18 kCat).embedUnitary M_impl⁻¹ * selectCat *
          (rUBInCat wOuter 18 kCat).embedUnitary M_impl)).1
      ((rOut.image ∪ rScr.image) ∪ rMidZero.image) := by
  intro rUB rOut rMidZero M_impl
  let rAll := rUB.compose (rAllUB wOuter 18)
  let rMid := rUB.compose (rMidUB wOuter 18)
  let rXo7 := rUB.compose (rXo7UB wOuter 18)
  let U_sel := rMain.embedUnitary selectCat
  let W_mid := rUB.embedUnitary M_impl
  let S₀ := rOut.image ∪ rScr.image
  have hMidOut : rMid.DisjointWires rOut :=
    compose_disjoint_opt163 rUB (disjoint_rOutUB_rMidUB wOuter 18).symm
  have hMidScr : rMid.DisjointWires rScr := (hDisj.compose_left _).compose_left _
  have hMidS₀ : Disjoint rMid.image S₀ :=
    Finset.disjoint_union_right.mpr
      ⟨SelectSwapQROM.disjoint_image_of_disjointWires hMidOut,
       SelectSwapQROM.disjoint_image_of_disjointWires hMidScr⟩
  have hAllEq : rMid.image ∪ S₀ = rAll.image ∪ rScr.image := by
    have hAllImg : rAll.image = rOut.image ∪ rMid.image := by
      ext w
      simp only [Finset.mem_union, QRegister.mem_image]
      constructor
      · rintro ⟨u, rfl⟩
        by_cases hu : u.val < mOutUB wOuter
        · refine Or.inl ⟨⟨u.val, hu⟩, ?_⟩
          have huEq : u = Fin.castAdd (mMidUB 18) ⟨u.val, hu⟩ := Fin.ext rfl
          conv_rhs => rw [huEq]
          change rUB _ = rUB (rAllUB wOuter 18 _)
          rw [rAllUB_eq_concat, QRegister.concat_apply_left]
        · let b : Fin (mMidUB 18) :=
            ⟨u.val - mOutUB wOuter, by
              have := u.isLt
              dsimp [mAncUB] at this
              omega⟩
          refine Or.inr ⟨b, ?_⟩
          have huEq : u = Fin.natAdd (mOutUB wOuter) b := Fin.ext (by
            dsimp [b]
            omega)
          conv_rhs => rw [huEq]
          change rUB _ = rUB (rAllUB wOuter 18 _)
          rw [rAllUB_eq_concat, QRegister.concat_apply_right]
      · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
        · refine ⟨Fin.castAdd (mMidUB 18) a, ?_⟩
          change rUB (rAllUB wOuter 18 _) = rUB _
          rw [rAllUB_eq_concat, QRegister.concat_apply_left]
        · refine ⟨Fin.natAdd (mOutUB wOuter) b, ?_⟩
          change rUB (rAllUB wOuter 18 _) = rUB _
          rw [rAllUB_eq_concat, QRegister.concat_apply_right]
    dsimp only [S₀]
    rw [hAllImg, Finset.union_comm rOut.image rMid.image, Finset.union_assoc]
  have hXoSub : rXo7.image ⊆ rAll.image ∪ rScr.image := by
    rw [← hAllEq]
    have hEq : rXo7 = rOut.compose (rXo7Loc wOuter) := CoherentAlias.qreg_ext fun _ ↦ rfl
    rw [hEq]
    exact (rOut.image_compose_subset _).trans
      (Finset.subset_union_left.trans Finset.subset_union_right)
  have hMidXo : rMid.DisjointWires rXo7 :=
    compose_disjoint_opt163 rUB (disjoint_rXo7UB_rMidUB wOuter 18).symm
  have hW_sum : W_mid.1 = ∑ rc : Fin (2 ^ 7),
      rXo7.basisOutcomeProjector rc *
        (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc)).1 := by
    change rUB.embedMatrix M_impl.1 = _
    dsimp only [M_impl, directXo7Mux18Of, muxUnitary, QRegister.basisOutcomeProjector]
    rw [rUB.embedMatrix_sum]
    refine Finset.sum_congr rfl fun rc _ ↦ ?_
    rw [rUB.embedMatrix_mul, ← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose]
    rfl
  have hWinv_sum : (W_mid⁻¹).1 = ∑ rc : Fin (2 ^ 7),
      ((rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc))⁻¹).1 *
        rXo7.basisOutcomeProjector rc := by
    change star W_mid.1 = _
    rw [Matrix.star_eq_conjTranspose, hW_sum, conjTranspose_sum]
    refine Finset.sum_congr rfl fun rc _ ↦ ?_
    rw [conjTranspose_mul, rXo7.basisOutcomeProjector_conjTranspose]
    rfl
  have hEmbEq : (rMain.embedUnitary ((rUBInCat wOuter 18 kCat).embedUnitary M_impl⁻¹ * selectCat *
      (rUBInCat wOuter 18 kCat).embedUnitary M_impl)).1 = (W_mid⁻¹).1 * U_sel.1 * W_mid.1 := by
    simp only [rMain.embedUnitary_mul, ← QRegister.embedUnitary_compose,
      QRegister.embedUnitary_inv, Submonoid.coe_mul, W_mid, U_sel, rUB]
  have hProd : (W_mid⁻¹).1 * U_sel.1 * W_mid.1 = ∑ rc : Fin (2 ^ 7),
      rXo7.basisOutcomeProjector rc *
        (((rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc))⁻¹).1 *
          U_sel.1 * (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc)).1) := by
    rw [hWinv_sum, hW_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun rc₁ _ ↦ ?_
    rw [Finset.mul_sum]
    have hTerm (rc₂ : Fin (2 ^ 7)) :
        (((rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc₁))⁻¹).1 *
          rXo7.basisOutcomeProjector rc₁ * U_sel.1) * (rXo7.basisOutcomeProjector rc₂ *
            (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc₂)).1) =
        if rc₁ = rc₂ then rXo7.basisOutcomeProjector rc₁ *
          (((rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc₁))⁻¹).1 *
            U_sel.1 * (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc₁)).1)
        else 0 := by
      let P₁ := rXo7.basisOutcomeProjector rc₁
      let P₂ := rXo7.basisOutcomeProjector rc₂
      let A₁ := ((rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc₁))⁻¹).1
      let B₂ := (rMid.embedUnitary (prepMid18FromSlice mux9AltBit sliceFn uIdx rc₂)).1
      have hMidComm1 : A₁ * P₁ = P₁ * A₁ := by
        dsimp only [A₁, P₁]
        rw [← QRegister.embedUnitary_inv]
        exact rMid.embedMatrix_comm_of_disjoint rXo7 hMidXo _ _
      have hMidComm2 : A₁ * P₂ = P₂ * A₁ := by
        dsimp only [A₁, P₂]
        rw [← QRegister.embedUnitary_inv]
        exact rMid.embedMatrix_comm_of_disjoint rXo7 hMidXo _ _
      have hUSel2 : U_sel.1 * (P₂ * B₂) = P₂ * (U_sel.1 * B₂) := by
        rw [← Matrix.mul_assoc, show U_sel.1 * P₂ = P₂ * U_sel.1 from
          preservesWires_comm_proj hselPres rXo7 hXoSub rc₂, Matrix.mul_assoc]
      have hMid2 : A₁ * (P₂ * (U_sel.1 * B₂)) = P₂ * (A₁ * (U_sel.1 * B₂)) := by
        rw [← Matrix.mul_assoc, hMidComm2, Matrix.mul_assoc]
      calc (A₁ * P₁ * U_sel.1) * (P₂ * B₂)
          = P₁ * (A₁ * (U_sel.1 * (P₂ * B₂))) := by
              rw [hMidComm1]
              simp only [Matrix.mul_assoc]
        _ = P₁ * (A₁ * (P₂ * (U_sel.1 * B₂))) := by rw [hUSel2]
        _ = (P₁ * P₂) * (A₁ * U_sel.1 * B₂) := by
              rw [hMid2]
              simp only [Matrix.mul_assoc]
        _ = _ := by
              dsimp only [P₁, P₂]
              rw [proj_mul_proj_ite]
              by_cases h12 : rc₁ = rc₂
              · subst h12
                rw [ite_pos_3 rfl, ite_pos_3 rfl]
              · rw [ite_neg_3 h12, ite_neg_3 h12, zero_mul]
    simp_rw [hTerm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hZeroEq : rMidZero = rMid.compose mid18AliasOutReg := CoherentAlias.qreg_ext fun _ ↦ rfl
  have hSetEq : (rOut.image ∪ rScr.image) ∪ rMidZero.image =
      S₀ ∪ (rMid.compose mid18AliasOutReg).image :=
    congrArg (fun q : QRegister 14 N ↦ S₀ ∪ q.image) hZeroEq
  have hSelMid : AliasPrep.PreservesWires U_sel.1 (rMid.image ∪ S₀) := by
    dsimp only [U_sel]
    rw [hAllEq]
    exact hselPres
  rw [hEmbEq, hProd, hSetEq]
  exact Phase2MidSandwich.preservesWires_sum Finset.univ _ fun rc _ ↦
    AliasPrep.preservesWires_mul (Phase2MidSandwich.preservesWires_basisOutcomeProjector
      rXo7 rc _)
      (preservesWires_conjPrepMid18FromSlice_set sliceFn uIdx rMid S₀ hMidS₀ hSelMid rc)

theorem sigIn_not_mem_out_scr_midZero (bQPE sUb : ℕ) :
    ((combWalkCatRegAt bQPE 8 18 4 14 0 sUb).compose (rUBInCat 8 18 11))
        ((rMidUB 8 18) (rSigInLoc 18 0)) ∉
      ((combOutRegB bQPE 8 18 4 14 0 sUb).image ∪
        scrMidZeroSet bQPE 8 18 4 14 0 sUb (by decide)) := by
  intro hMem
  rcases Finset.mem_union.mp hMem with hOut | hSM
  · obtain ⟨i, hi⟩ := (QRegister.mem_image _ _).mp hOut
    exact (disjoint_rOutUB_rMidUB 8 18).ne i (rSigInLoc 18 0)
      ((combUBRegB bQPE 8 18 4 14 0 sUb).wires.injective hi)
  · rcases Finset.mem_union.mp hSM with hScr | hMZ
    · obtain ⟨i, hi⟩ := (QRegister.mem_image _ _).mp hScr
      exact (combWalkCatRegB_disjoint_scr bQPE 8 18 4 14 0 sUb).ne _ i hi.symm
    · obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hMZ
      have hv := congrArg Fin.val ((combMidRegB bQPE 8 18 4 14 0 sUb).wires.injective hj)
      have hjlt := j.isLt
      simp [midZeroPrefixReg, blockZeroReg, rSigInLoc, mMidUB] at hv
      omega

theorem cleanRealizes_pOutFwdAt (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes ()
      (combOutRegB bQPE 8 18 4 14 0 sUb)
      (combScrUbRegAt bQPE 8 18 4 14 0 sUb)
      (outer8PrepOutWordImpl mag8To23Word17)
      (pOutFwdAt bQPE sUb hs87) := by
  let pl := plOut87At bQPE sUb hs87
  let rOut := combOutRegB bQPE 8 18 4 14 0 sUb
  let rScrUb := combScrUbRegAt bQPE 8 18 4 14 0 sUb
  have hLoc := cleanRealizesHGadgetOuter8PrepOutWordFwdDyn mag8To23Word17 ()
    (QRegister.block 0 (mOutUB 8) (by decide)) (QRegister.block (mOutUB 8) 87 le_rfl) le_rfl
    (QRegister.block_disjoint_of_le 0 (mOutUB 8) (mOutUB 8) 87 (by decide) le_rfl le_rfl)
  have hOn := hLoc.onRegister pl
  have hPlAct : pl.compose (QRegister.block 0 (mOutUB 8) (by decide)) =
      rOut.compose (QRegister.whole (mOutUB 8)) := by
    ext i
    have hr : (QRegister.block 0 (mOutUB 8) (by decide) : QRegister (mOutUB 8) (mOutUB 8 + 87)) i =
        Fin.castAdd 87 i := Fin.ext (Nat.zero_add i.val)
    dsimp only [pl, plOut87At, rOut]
    rw [QRegister.compose_apply, hr, QRegister.concat_apply_left]
    rfl
  have hPlScr : pl.compose (QRegister.block (mOutUB 8) 87 le_rfl) = rScrUb.slice 0 87 hs87 := by
    ext i
    have hr : (QRegister.block (mOutUB 8) 87 le_rfl : QRegister 87 (mOutUB 8 + 87)) i =
        Fin.natAdd (mOutUB 8) i := Fin.ext rfl
    dsimp only [pl, plOut87At]
    rw [QRegister.compose_apply, hr, QRegister.concat_apply_right]
  rw [hPlAct, hPlScr] at hOn
  have hSub := hOn.subregister (combOutRegB_disjoint_scr bQPE 8 18 4 14 0 sUb)
    (rScrUb.image_compose_subset _)
  rwa [QRegister.whole_embedUnitary] at hSub

/-- Local `(87 + 4)`-wire `(rScr87 ++ outZero4)` register inside `mOutUB 8 + 87`. -/
def locOutCleanReg : QRegister (87 + 4) (mOutUB 8 + 87) :=
  (QRegister.block (mOutUB 8) 87 le_rfl).concat
    ((QRegister.block 0 (mOutUB 8) (by decide)).compose (outZeroPrefixReg 8 4 (by decide)))
    (QRegister.disjoint_comm.mp
      ((QRegister.block_disjoint_of_le 0 (mOutUB 8) (mOutUB 8) 87 (by decide) le_rfl
        le_rfl).compose_left _))

theorem cleanUnloadsWp_pOutBwdAt (bQPE sUb : ℕ) (hs87 : 0 + 87 ≤ sUb) :
    CleanUnloadsWp () (scrOutZeroSet bQPE 8 18 4 14 0 sUb (by decide))
      ((combOutRegB bQPE 8 18 4 14 0 sUb).embedUnitary
        (outer8PrepOutWordImpl mag8To23Word17))
      (pOutBwdAt bQPE sUb hs87) := by
  let pl := plOut87At bQPE sUb hs87
  let rOut := combOutRegB bQPE 8 18 4 14 0 sUb
  let rScrUb := combScrUbRegAt bQPE 8 18 4 14 0 sUb
  have hLoc := cleanUnloadsWpHGadgetOuter8PrepOutWordBwdDyn mag8To23Word17 ()
    (QRegister.block 0 (mOutUB 8) (by decide)) (QRegister.block (mOutUB 8) 87 le_rfl) (by decide)
    (QRegister.block_disjoint_of_le 0 (mOutUB 8) (mOutUB 8) 87 (by decide) le_rfl le_rfl)
  rw [← QRegister.image_concat _ _
    (QRegister.disjoint_comm.mp
      ((QRegister.block_disjoint_of_le 0 (mOutUB 8) (mOutUB 8) 87 (by decide) le_rfl
        le_rfl).compose_left _))] at hLoc
  have hPlOut : pl.compose (QRegister.block 0 (mOutUB 8) (by decide)) = rOut := by
    ext i
    have hr : (QRegister.block 0 (mOutUB 8) (by decide) : QRegister (mOutUB 8) (mOutUB 8 + 87)) i =
        Fin.castAdd 87 i := Fin.ext (Nat.zero_add i.val)
    dsimp only [pl, plOut87At, rOut]
    rw [QRegister.compose_apply, hr, QRegister.concat_apply_left]
  have hPlScr : pl.compose (QRegister.block (mOutUB 8) 87 le_rfl) = rScrUb.slice 0 87 hs87 := by
    ext i
    have hr : (QRegister.block (mOutUB 8) 87 le_rfl : QRegister 87 (mOutUB 8 + 87)) i =
        Fin.natAdd (mOutUB 8) i := Fin.ext rfl
    dsimp only [pl, plOut87At]
    rw [QRegister.compose_apply, hr, QRegister.concat_apply_right]
  have hSub : (pl.compose locOutCleanReg).image ⊆
      scrOutZeroSet bQPE 8 18 4 14 0 sUb (by decide) := by
    intro w hw
    obtain ⟨u, rfl⟩ := (QRegister.mem_image _ _).mp hw
    rcases finSumFinEquiv.surjective u with ⟨a | b, rfl⟩
    · refine Finset.mem_union_left _ ?_
      change pl (locOutCleanReg (Fin.castAdd 4 a)) ∈ rScrUb.image
      dsimp only [locOutCleanReg]
      rw [QRegister.concat_apply_left, ← QRegister.compose_apply, hPlScr]
      exact rScrUb.image_compose_subset _ ((QRegister.mem_image _ _).mpr ⟨a, rfl⟩)
    · refine Finset.mem_union_right _ ?_
      change pl (locOutCleanReg (Fin.natAdd 87 b)) ∈
        (rOut.compose (outZeroPrefixReg 8 4 (by decide))).image
      dsimp only [locOutCleanReg]
      rw [QRegister.concat_apply_right, QRegister.compose_apply, ← QRegister.compose_apply pl,
        hPlOut]
      exact (QRegister.mem_image _ _).mpr ⟨b, rfl⟩
  have hOn := cleanUnloadsWp_onRegister () pl locOutCleanReg hSub _ _ hLoc
  rwa [← QRegister.embedUnitary_compose, hPlOut] at hOn

theorem bellAsymLegsMain {sQrom tLoad14 : ℕ}
    (qromBundle : OneHot14LoadBundle_3 Unit sQrom tLoad14 keep9Hot24BoolTable)
    (d : ℕ) (hd : d ≤ 10) (bQPE sUb : ℕ) (hs : 160 - d ≤ sUb)
    (hk1 : max 144 (121 + sQrom) ≤ 159 - d) (hkT : max 146 (121 + sQrom) ≤ 159 - d)
    {raw_4 raw_3 : Unitary (2 ^ (nUB 8 18 + 11))}
    (hsF_pres : AliasPrep.PreservesWires
      ((combWalkCatRegAt bQPE 8 18 4 14 0 sUb).embedUnitary raw_4).1
      ((((combWalkCatRegAt bQPE 8 18 4 14 0 sUb).compose (rUBInCat 8 18 11)).compose
        (rAllUB 8 18)).image ∪ (combScrUbRegAt bQPE 8 18 4 14 0 sUb).image))
    (hsB_pres : AliasPrep.PreservesWires
      ((combWalkCatRegAt bQPE 8 18 4 14 0 sUb).embedUnitary raw_3).1
      ((((combWalkCatRegAt bQPE 8 18 4 14 0 sUb).compose (rUBInCat 8 18 11)).compose
        (rAllUB 8 18)).image ∪ (combScrUbRegAt bQPE 8 18 4 14 0 sUb).image)) :
    let D_neg := dNegUB 8 18 Pi145CompactRouter.hot128NegBit2
    let M_a := asymMidMux 8 18 mainPrepMid
    BellAsymLegs Unit bQPE 8 18 4 14 0 sUb (by decide) (by decide) ()
      (outer8PrepOutWordImpl mag8To23Word17) M_a M_a raw_4 raw_3
      ((rUBInCat 8 18 11).embedUnitary D_neg * raw_4)
      (raw_3 * (rUBInCat 8 18 11).embedUnitary D_neg)
      (pOutFwdAt bQPE sUb (by omega)) (pOutBwdAt bQPE sUb (by omega))
      (pStep1At qromBundle.toOneHot14LoadCirc2 bQPE sUb (159 - d) hk1 (by omega))
      (pTurnAt qromBundle.toOneHot14LoadCirc2 bQPE sUb (159 - d) hkT (by omega))
      (pStep4At bQPE sUb (159 - d) (by omega) (by omega)) := by
  intro D_neg M_a
  let rMain := combWalkCatRegAt bQPE 8 18 4 14 0 sUb
  let rScrUb := combScrUbRegAt bQPE 8 18 4 14 0 sUb
  let rUB := combUBRegB bQPE 8 18 4 14 0 sUb
  let rOut := combOutRegB bQPE 8 18 4 14 0 sUb
  let S₁ := scrMidZeroSet bQPE 8 18 4 14 0 sUb (by decide)
  let S₂ := rOut.image ∪ S₁
  have hMainScr := combWalkCatRegB_disjoint_scr bQPE 8 18 4 14 0 sUb
  have hD_pres : AliasPrep.PreservesWires
      (rMain.embedUnitary ((rUBInCat 8 18 11).embedUnitary D_neg)).1
      (((rMain.compose (rUBInCat 8 18 11)).compose (rAllUB 8 18)).image ∪ rScrUb.image) :=
    preservesWiresDNegCat 8 18 Pi145CompactRouter.hot128NegBit2 rMain _
  have hNotAll := sigIn_not_mem_out_scr_midZero bQPE sUb
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
  have h1Raw := cleanRealizesSetInner18Step1Dyn qromBundle (Mag30Bundle2.t72 Unit) pi128Equiv
    rUB rScrUb (159 - d) hk1 (by omega) (hMainScr.compose_left _) ()
  dsimp only [Mag30Bundle2.t72] at h1Raw
  rw [inner18Mfwd_eqAsymMidMux] at h1Raw
  have hTurnRaw := cleanTurnaroundWpInner18TurnDyn qromBundle (Mag30Bundle2.t72 Unit)
    (Mag30Bundle2.t72 Unit) pi128Equiv rUB rScrUb (159 - d) hkT (by omega)
    (hMainScr.compose_left _) ()
  dsimp only [Mag30Bundle2.t72] at hTurnRaw
  rw [hot128NegUB_eqDNegUB, inner18Mfwd_eqAsymMidMux,
    embed_reflMidUnitary_inMidWalkCat_eq rMain] at hTurnRaw
  have h4Raw := cleanUnloadsWpInner18Step4ColdDyn (Mag30Bundle2.t72 Unit) pi128Equiv
    rUB rScrUb (159 - d) (by omega) (by omega) (hMainScr.compose_left _) ()
  dsimp only [Mag30Bundle2.t72] at h4Raw
  rw [inner18Mfwd_eqAsymMidMux] at h4Raw
  exact BellAsymLegs.ofDNeg M_a M_a D_neg
    (dNegUB_inv 8 18 Pi145CompactRouter.hot128NegBit2) raw_4 raw_3
    (cleanRealizes_pOutFwdAt bQPE sUb (by omega))
    (cleanUnloadsWp_pOutBwdAt bQPE sUb (by omega))
    (outerConjPreservesZeroOuter8PrepOutWordImpl mag8To23Word17)
    h1Raw hTurnRaw h4Raw
    (fun i j ⟨w, hw, hne⟩ ↦ hPresF_all i j ⟨w, Finset.subset_union_right hw, hne⟩)
    (fun i j ⟨w, hw, hne⟩ ↦ hPresB_all i j ⟨w, Finset.subset_union_right hw, hne⟩)
    (by
      rw [innerMidCoreUnitary, rMain.embedUnitary_mul, rMain.embedUnitary_mul]
      exact AliasPrep.preservesWires_mul
        (AliasPrep.preservesWires_mul hPresB_all (preservesWires_embed_reflMid_zc20 rMain _ S₂))
        hPresF_all)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MainInner18SuperWalk
