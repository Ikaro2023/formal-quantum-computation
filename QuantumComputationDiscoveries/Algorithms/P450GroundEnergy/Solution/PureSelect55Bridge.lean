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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145Select24
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearC
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearD
public import
    QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.NoNegSOSAndSuperWalk

/-!
# `55`-AND `π145` Pure `SELECT` Bridge & `K`-Step Invariant-Subspace Walk Lift

Proves the pure `mulVec` equations for `select55NoNegPureUnitary` (`twoBody_noNeg`, `ge126`,
`oneBody_siZero`, `ge184`), transfers `kernel_step` from `select57NoNeg*` to
`select55NoNeg*` on `PostOutInv` (`walkRefl2InvErrLe_noNegDNeg55_ideal`), and lifts exact
single-step walk reflection equivalence to general `K ≥ 1` (`walkKStepRefl2InvErrLe_zero_of_exact`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Select55PureBridge
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit Real HermitianMat CoherentAlias CleanDyn AliasPrep
open SelectSwapQROM QuantumComputation.Specs QuantumComputation.Specs.P450
open GivensOps CircuitModular
open BlockEncodingCore BlockEncodingCircuit
open TopIntegrationBridge Phase2MidSandwich MidReflCtxRetain Cat11CompactPhase2Bridge
open ReordOuter13Bridge ZeroRcHotPrepMid21Fast MobiusOptSubcube163Walk
open CompactTuned162StepZeroCmp20 Pi145SOSPermBridge LowBitPi145Select
open CompactOuter9Bound50Core CompactOuter9Bound50Select OneHotSimulates
open QuantizedFactoredMag30 BellSingletCSwap58 BellPersistCore
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
  (pack16)
open BellPersistSuperWalk BellRouter57 BellRouter57Pure
open NoNegSelect57Pure CompactCore145Bundle Select57Slices
open BellSelectNoNegPair BellSuperNoNegWalk TwoGearSuperPhase5
open ThreeGearBellSuper TwoGearQPEPhase5 Phase2FlexBridge
open Pi145CompactRouter Pi145CompactSelect24
open NoNegDNegSOSAndSuperWalk Balanced160Select TailShiftThreeGear
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowR55Br (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: `55`-AND `π145` Branch & `select55NoNegPureUnitary` `mulVec` Lemmas -/

theorem y12_lt12655 (op : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32) (si neg : Bool)
    (hxo' : xo'.val < 126) :
    let y := y12OfState24 specA55 (specB55 op) (pack16 xo' so b si neg)
    let r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))
    (fun j : Fin 10 ↦ y ⟨j.val, by omega⟩) =
        ctrl10OfState24 (step24 (postB55 op) (twoBodyRIn r b)) ∧
      y 10 = si ∧ y 11 = neg := by
  obtain ⟨hw8_0, h15_3, h16_0, hCanon⟩ := (pre3_pack16 op xo' so b si neg).2.2.1 hxo'
  exact ⟨funext fun j ↦ (dite_eq_left j.isLt).trans ((congrFun (ctrl10_mergePost _ _) j).trans
    (congrFun (congrArg (fun s ↦ ctrl10OfState24 (step24 (postB55 op) s))
      (hCanon.trans (tbIn_eq_rIn op xo' hxo' b))) j)), h15_3,
    by simp [y12OfState24, signBitOfState24, hw8_0, h16_0]⟩

/-- Boolean check on `(r : Fin 9, b32 : Fin 32)` for two-body active bit, row index, and phase. -/
def chkTbR55 (op : Bool) (r : Fin 9) (b32 : Fin 32) : Bool :=
  withR (postB55 op) (twoBodyRIn r b32) fun s1 ↦
    (bal145ActOf10 actFlip145 (fastCtrl10 s1) == decide (b32.val < 29)) &&
    (!bal145ActOf10 actFlip145 (fastCtrl10 s1) ||
      (bal145RowIdxOf10 (orbitalOfPi14555 op) (fastCtrl10 s1) ==
        ⟨58 + 29 * r.val + min b32.val 28, by omega⟩)) &&
    (bal145PhaseOf10 actFlip145 (negMaskPi14555 op) (fastCtrl10 s1) == decide (b32.val < 29))

theorem r55Branch_twoBody (op : Bool) (xo' : Fin 256) (so : Fin 2) (b : Fin 32) (si : Fin 2)
    (neg : Bool) (hk126 : xo'.val < 126) (hb30 : b.val < 30)
    (hBit : neg = negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b) :
    selectGenCoreBranch 0
      (fun m10 ↦ phase2Bal145PhasedBranch actFlip145 (orbitalOfPi14555 op)
        (negMaskPi14555 op) (finOfBits 10 m10))
      (y12OfState24 specA55 (specB55 op)
        (pack16 xo' (decide (so = 1)) b (decide (si = 1)) neg)) =
    selectBranchUnitary (pi145XoEquiv xo') so b si := by
  rw [hBit]
  let xo := pi145XoEquiv xo'
  let negP := negInPadded (rcBitsOfXo xo) b
  let x16 := pack16 xo' (decide (so = 1)) b (decide (si = 1)) negP
  let y12 := y12OfState24 specA55 (specB55 op) x16
  obtain ⟨hf, hs, hy⟩ := y12_lt12655 op xo' (decide (so = 1)) b (decide (si = 1)) negP hk126
  let r := rDiv14OfRc (rcBitsOfXo xo)
  have hr : chkTbR55 op r b = true := by
    have hb : ∀ od : Bool, allPow2 4 0 (fun r ↦
      if hr : r < 9 then allPow2 5 0 (fun b ↦
        if b < 30 then chkTbR55 od ⟨r, hr⟩ ⟨b % 32, Nat.mod_lt _ (by decide)⟩ else true)
      else true) = true := by
      decide +kernel
    have h1 := allPow2_zero_true (hb op) r.val (by omega)
    rw [dite_eq_left r.isLt] at h1
    have h2 := allPow2_zero_true h1 b.val b.isLt
    rwa [ite_eq_left hb30, mod32_fin b] at h2
  dsimp only [chkTbR55] at hr
  rw [withR_eq, fastCtrl10_eq] at hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hr
  rcases hr with ⟨⟨hc0, hrowR⟩, hphR⟩
  have hpi := pi145XoEquiv_hpi xo' (by omega)
  have hn58 : ¬ (pi145XoEquiv xo').val < 58 := by omega
  have h2b : isOneBodyXo xo = false := decide_eq_false hn58
  have hf10B : (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) =
      ctrl10OfState24 (specB55 op (specA55 x16)) := funext fun j ↦ dite_eq_left j.isLt
  refine y12_bal145_eq_selectBranchUnitary actFlip145 (orbitalOfPi14555 op)
    (negMaskPi14555 op) y12 xo so b si (hf10B.symm ▸ ctrl10_pair8_lt145 op x16)
    (((congrArg (bal145ActOf10 actFlip145) hf).trans hc0).trans (by simp [enROf, h2b]))
    (fun hact ↦ ?_) (hs.trans (by simp [sigSelOf, h2b]))
    ((congrArg₂ xor hy ((congrArg (bal145PhaseOf10 actFlip145 (negMaskPi14555 op)) hf).trans
      hphR)).trans (by simp [negP, negPhaseOf, h2b]))
  dsimp only [y12, x16] at hact ⊢
  rw [hf] at hact ⊢
  rw [hact] at hrowR
  exact (by simpa [beq_iff_eq] using hrowR : _ = _).trans (dite_eq_right hn58).symm

theorem r55Branch_twoBody_noNeg (op : Bool) (xo' : Fin 256) (so : Fin 2) (b : Fin 32) (si : Fin 2)
    (hk126 : xo'.val < 126) (hb30 : b.val < 30) :
    selectGenCoreBranch 0
      (fun m10 ↦ phase2Bal145PhasedBranch actFlip145 (orbitalOfPi14555 op)
        (negMaskPi14555 op) (finOfBits 10 m10))
      (y12OfState24 specA55 (specB55 op)
        (pack16 xo' (decide (so = 1)) b (decide (si = 1)) false)) =
    (if negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b then negOneUnitary (2 * 58) else 1) *
      selectBranchUnitary (pi145XoEquiv xo') so b si := by
  let neg0 := negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b
  obtain ⟨hf0, hs0, hy0⟩ := y12_lt12655 op xo' (decide (so = 1)) b (decide (si = 1)) false hk126
  obtain ⟨hfN, hsN, hyN⟩ := y12_lt12655 op xo' (decide (so = 1)) b (decide (si = 1)) neg0 hk126
  have h2bBr := r55Branch_twoBody op xo' so b si neg0 hk126 hb30 rfl
  dsimp only [selectGenCoreBranch] at h2bBr ⊢
  rw [hyN] at h2bBr
  rw [hy0, ite_eq_right Bool.false_ne_true, one_mul, hs0.trans hsN.symm, hf0.trans hfN.symm,
    show negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b = neg0 from rfl, ← h2bBr,
    ← mul_assoc (if neg0 then negOneUnitary (2 * 58) else 1),
    show (if neg0 then negOneUnitary (2 * 58) else 1) *
      (if neg0 then negOneUnitary (2 * 58 + 0) else 1) = 1 by
      cases neg0
      exacts [one_mul 1, Subtype.ext (by simp [negOneUnitary_val])], one_mul]

section
attribute [local irreducible] selectBranchUnitary

theorem select55NoNegPureUnitary_mulVec_twoBody_full {wOuter wInner2 : ℕ} (oddPass : Bool)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (hxo' : ((rXoLoc wOuter).extractIndex o').val < 126)
    (hb : ((rBLoc wInner2).extractIndex m).val < 30) :
    let xo' := (rXoLoc wOuter).extractIndex o'
    let b := (rBLoc wInner2).extractIndex m
    let br := selectBranchUnitary (pi145XoEquiv xo')
      ((rSigOutLoc wOuter).extractIndex o') b ((rSigInLoc wInner2).extractIndex m)
    (select55NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      (if negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b then (-1 : ℂ) else 1) •
        embedKet (br.1 *ᵥ ψ) o' m := by
  intro xo' b br
  have hBr : (select55NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      embedKet (((if negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b then
        negOneUnitary (2 * 58) else 1) * br).1 *ᵥ ψ) o' m := by
    refine selectNoNegGenPureUnitary_mulVec_embedKet_eq_of_branch _ _ _ ψ o' m _ ?_
    rw [y12NoNegOf1555_pack15]
    exact r55Branch_twoBody_noNeg oddPass xo' ((rSigOutLoc wOuter).extractIndex o') b
      ((rSigInLoc wInner2).extractIndex m) hxo' hb
  rw [hBr]
  dsimp only [br]
  cases negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, one_mul, one_smul]
  | true =>
    simp only [↓reduceIte, Submonoid.coe_mul, negOneUnitary_val, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec]
    funext g
    dsimp only [embedKet, Pi.smul_apply]
    split_ifs <;> simp

end

/-! ## Section 2: `55`-AND = `57`-AND on Active Subspace & `WalkRefl2InvErrLe` + `K`-Step Lift -/

theorem r55_eq57_embedKet {wOuter wInner2 : ℕ} (ξ : Fin (2 ^ (2 * 58)) → ℂ)
    (o' : Fin (2 ^ mOutUB wOuter)) (m' : Fin (2 ^ mMidUB wInner2))
    (hAct : (((rXoLoc wOuter).extractIndex o').val < 126 ∧
        ((rBLoc wInner2).extractIndex m').val < 30) ∨
      (126 ≤ ((rXoLoc wOuter).extractIndex o').val ∧
        ((rXoLoc wOuter).extractIndex o').val < 184 ∧
        (rSigInLoc wInner2).extractIndex m' = 0) ∨
      184 ≤ ((rXoLoc wOuter).extractIndex o').val) :
    (select55NoNegFwdPureUnitary wOuter wInner2).1 *ᵥ embedKet ξ o' m' =
        (select57NoNegFwdPureUnitary wOuter wInner2).1 *ᵥ embedKet ξ o' m' ∧
      (select55NoNegBwdPureUnitary wOuter wInner2).1 *ᵥ embedKet ξ o' m' =
        (select57NoNegBwdPureUnitary wOuter wInner2).1 *ᵥ embedKet ξ o' m' := by
  rcases hAct with ⟨hx, hb⟩ | ⟨h126, h184, hSi⟩ | h184
  · exact ⟨(select55NoNegPureUnitary_mulVec_twoBody_full false ξ o' m' hx hb).trans
        (select57NoNegPureUnitary_mulVec_twoBody_full false ξ o' m' hx hb).symm,
      (select55NoNegPureUnitary_mulVec_twoBody_full true ξ o' m' hx hb).trans
        (select57NoNegPureUnitary_mulVec_twoBody_full true ξ o' m' hx hb).symm⟩
  · have h55 := select55NoNegPureUnitary_mulVec_oneBodyZero ξ o' m' h126 h184 hSi
    have h57 := select57NoNegPureUnitary_mulVec_oneBodyZero ξ o' m' h126 h184 hSi
    exact ⟨h55.1.trans h57.1.symm, h55.2.trans h57.2.symm⟩
  · exact ⟨(select55NoNegPureUnitary_mulVec_ge184 false ξ o' m' h184).trans
        (select57NoNegPureUnitary_mulVec_ge184 false ξ o' m' h184).symm,
      (select55NoNegPureUnitary_mulVec_ge184 true ξ o' m' h184).trans
        (select57NoNegPureUnitary_mulVec_ge184 true ξ o' m' h184).symm⟩

theorem uRefl2_noNegDNeg_mulVec_walkCat_gen {wOuter wInner2 : ℕ}
    (prepOutImpl : Unitary (2 ^ mOutUB wOuter))
    (prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) (dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool)
    {sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    {SF OuterWeights : Unitary (2 ^ nUB wOuter wInner2)}
    (hsF : SelCatEqOuterInner wOuter wInner2 sF SF)
    (hsB : SelCatEqOuterInner wOuter wInner2 sB OuterWeights)
    (v : Fin (2 ^ nUB wOuter wInner2) → ℂ) :
    let M_a := asymMidMux wOuter wInner2 prepMid
    let Out := (rOutUB wOuter wInner2).embedUnitary prepOutImpl
    let K_asym := M_a⁻¹ * (OuterWeights * dNegUB wOuter wInner2 dBit) * M_a *
      QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2) *
      (M_a⁻¹ * (dNegUB wOuter wInner2 dBit * SF) * M_a)
    let cat := CircuitModular.phaseGradientLowFactor 11 3
    (asymURefl2 prepOutImpl prepMid dBit sF sB).1 *ᵥ tensorWalkCat v cat =
      tensorWalkCat ((Out⁻¹ * K_asym * Out).1 *ᵥ v) cat := by
  intro M_a Out K_asym cat
  let rMidCat := inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2)
  have hemb (A : Unitary (2 ^ nUB wOuter wInner2)) (x : Fin (2 ^ nUB wOuter wInner2) → ℂ) :
      ((rUBInCat wOuter wInner2 11).embedUnitary A).1 *ᵥ tensorUBCat x cat =
        tensorUBCat (A.1 *ᵥ x) cat :=
    embedMatrix_rUBInCat_mulVec_tensorUBCat A.1 x cat
  have hRmidCat (u : Fin (2 ^ nUB wOuter wInner2) → ℂ) : (QubitisedWalk.reflMidUnitary rMidCat).1 *ᵥ
      tensorUBCat u cat =
        tensorUBCat ((QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2)).1 *ᵥ u) cat := by
    have hrMid : rMidCat = (rUBInCat wOuter wInner2 11).compose (rMidUB wOuter wInner2) :=
      CoherentAlias.qreg_ext fun i ↦ by
        simp [rMidCat, inMidWalkCat, rUBInCat, rMidUB, rWalkInWalkCat, rMidInWalk]
    have hP : QubitisedWalk.projMid rMidCat =
        (rUBInCat wOuter wInner2 11).embedMatrix (QubitisedWalk.projMid (rMidUB wOuter wInner2)) :=
          by
      dsimp only [QubitisedWalk.projMid, QRegister.basisOutcomeProjector]
      rw [hrMid, QRegister.embedMatrix_compose]
    rw [QubitisedWalk.reflMidUnitary_val, QubitisedWalk.reflMidUnitary_val, Matrix.sub_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, hP, embedMatrix_rUBInCat_mulVec_tensorUBCat]
    ext g
    dsimp only [tensorUBCat, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hBwdInv : (ubCustomMuxCatUnitary M_a prepOutImpl (sB * dNegCat wOuter wInner2 dBit)⁻¹)⁻¹ =
      (rUBInCat wOuter wInner2 11).embedUnitary Out⁻¹ *
        (rUBInCat wOuter wInner2 11).embedUnitary M_a⁻¹ * sB *
        dNegCat wOuter wInner2 dBit * (rUBInCat wOuter wInner2 11).embedUnitary M_a := by
    dsimp only [ubCustomMuxCatUnitary, Out]
    rw [QRegister.embedUnitary_compose]
    simp only [_root_.mul_inv_rev, inv_inv, QRegister.embedUnitary_inv, mul_assoc]
  rw [tensorWalkCat_eq_tensorUBCat, tensorWalkCat_eq_tensorUBCat]
  dsimp only [asymURefl2, QubitisedWalk.reflPulledPair]
  change (_ * QubitisedWalk.reflMidUnitary rMidCat *
    ubCustomMuxCatUnitary M_a prepOutImpl (dNegCat wOuter wInner2 dBit * sF)).1 *ᵥ _ = _
  rw [hBwdInv]
  dsimp only [ubCustomMuxCatUnitary, dNegCat, Out]
  rw [QRegister.embedUnitary_compose]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [hemb, hemb, hsF, hemb, hemb, hRmidCat, hemb, hemb, hsB, hemb, hemb]
  dsimp only [K_asym]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

theorem kAsym55_eq57_on_postOutInv {wOuter wInner2 : ℕ}
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hSpin : PrepMidSpinFactored prepMid)
    (hB30 : ∀ (rc : Fin 126) (m : Fin (2 ^ mMidUB wInner2)),
      30 ≤ ((rBLoc wInner2).extractIndex m).val → (prepMid ⟨rc.val, by omega⟩).1 m 0 = 0)
    {dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool} (hd : IsValidDNegBit dBit)
    {x : Fin (2 ^ nUB wOuter wInner2) → ℂ} (hx : PostOutInv wOuter wInner2 prepMid false x) :
    let M_a := asymMidMux wOuter wInner2 prepMid
    let R_mid := QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2)
    let K55 :=
      M_a⁻¹ * (select55NoNegBwdPureUnitary wOuter wInner2 * dNegUB wOuter wInner2 dBit) * M_a *
      R_mid *
        (M_a⁻¹ * (dNegUB wOuter wInner2 dBit * select55NoNegFwdPureUnitary wOuter wInner2) * M_a)
    let K57 :=
      M_a⁻¹ * (select57NoNegBwdPureUnitary wOuter wInner2 * dNegUB wOuter wInner2 dBit) * M_a *
      R_mid *
        (M_a⁻¹ * (dNegUB wOuter wInner2 dBit * select57NoNegFwdPureUnitary wOuter wInner2) * M_a)
    K55.1 *ᵥ x = K57.1 *ᵥ x := by
  intro M_a R_mid K55 K57
  let D := dNegUB wOuter wInner2 dBit
  let F55 := M_a⁻¹ * (D * select55NoNegFwdPureUnitary wOuter wInner2) * M_a
  let F57 := M_a⁻¹ * (D * select57NoNegFwdPureUnitary wOuter wInner2) * M_a
  let B55 := M_a⁻¹ * (select55NoNegBwdPureUnitary wOuter wInner2 * D) * M_a
  let B57 := M_a⁻¹ * (select57NoNegBwdPureUnitary wOuter wInner2 * D) * M_a
  let M_s := prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))
  let U_I := M_s⁻¹ * idealPi145SelectPure wOuter wInner2 * M_s
  have hBranchAct (o' : Fin (2 ^ mOutUB wOuter)) (m' : Fin (2 ^ mMidUB wInner2))
      (hnz : (asymMidBranch prepMid o').1 m' 0 ≠ 0) :
      (((rXoLoc wOuter).extractIndex o').val < 126 ∧ ((rBLoc wInner2).extractIndex m').val < 30) ∨
        (126 ≤ ((rXoLoc wOuter).extractIndex o').val ∧ ((rXoLoc wOuter).extractIndex o').val < 184 ∧
          (rSigInLoc wInner2).extractIndex m' = 0) ∨
        184 ≤ ((rXoLoc wOuter).extractIndex o').val := by
    by_cases h126 : ((rXoLoc wOuter).extractIndex o').val < 126
    · left
      rw [asymMidBranch_of_lt126 prepMid o' h126] at hnz
      have hrc126 : ((rXo7Loc wOuter).extractIndex o').val < 126 := by
        rwa [extract_rXo7Loc_of_lt128 o' (by omega)]
      have hpi126 := pi128Equiv_lt126_of_lt126 _ hrc126
      exact ⟨h126, by_contra fun hge ↦ hnz (hB30 ⟨_, hpi126⟩ m' (by omega))⟩
    · by_cases h184 : ((rXoLoc wOuter).extractIndex o').val < 184
      · right
        left
        exact ⟨by omega, h184, asymMidBranchZero_of_oneBody hSpin o' (by omega) h184 m' hnz⟩
      · right
        right
        omega
  have hLift {A S₁ S₂ : Unitary (2 ^ nUB wOuter wInner2)} {v : Fin (2 ^ nUB wOuter wInner2) → ℂ}
      (hS : S₁.1 *ᵥ (A.1 *ᵥ v) = S₂.1 *ᵥ (A.1 *ᵥ v)) :
      (A⁻¹ * S₁ * A).1 *ᵥ v = (A⁻¹ * S₂ * A).1 *ᵥ v := by
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hS]
  have hMidZeroEq (ξ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) :
      F55.1 *ᵥ embedKet ξ o' 0 = F57.1 *ᵥ embedKet ξ o' 0 ∧
        B55.1 *ᵥ embedKet ξ o' 0 = B57.1 *ᵥ embedKet ξ o' 0 := by
    have hF : (D * select55NoNegFwdPureUnitary wOuter wInner2).1 *ᵥ (M_a.1 *ᵥ embedKet ξ o' 0) =
        (D * select57NoNegFwdPureUnitary wOuter wInner2).1 *ᵥ (M_a.1 *ᵥ embedKet ξ o' 0) := by
      rw [asymMidMux_mulVec_embedKet, embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum,
        Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun m' _ ↦ ?_
      by_cases hnz : (asymMidBranch prepMid o').1 m' 0 = 0
      · simp only [hnz, zero_smul, Matrix.mulVec_zero]
      · simp only [Matrix.mulVec_smul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          (r55_eq57_embedKet ξ o' m' (hBranchAct o' m' hnz)).1]
    have hB : (select55NoNegBwdPureUnitary wOuter wInner2 * D).1 *ᵥ (M_a.1 *ᵥ embedKet ξ o' 0) =
        (select57NoNegBwdPureUnitary wOuter wInner2 * D).1 *ᵥ (M_a.1 *ᵥ embedKet ξ o' 0) := by
      rw [asymMidMux_mulVec_embedKet, embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum,
        Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun m' _ ↦ ?_
      by_cases hnz : (asymMidBranch prepMid o').1 m' 0 = 0
      · simp only [hnz, zero_smul, Matrix.mulVec_zero]
      · simp only [Matrix.mulVec_smul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, D,
          dNegUB_mulVec_embedKet, (r55_eq57_embedKet _ o' m' (hBranchAct o' m' hnz)).2]
    exact ⟨hLift hF, hLift hB⟩
  have hTwoBodyUEq (ξ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter))
      (hxo' : ((rXoLoc wOuter).extractIndex o').val < 126) :
      F55.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0) = F57.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0) ∧
        B55.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0) = B57.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0) := by
    have hMsMulInv : M_s.1 * (M_s⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel M_s)
    have hMa (ζ : Fin (2 ^ (2 * 58)) → ℂ) (m : Fin (2 ^ mMidUB wInner2)) :
        M_a.1 *ᵥ embedKet ζ o' m = M_s.1 *ᵥ embedKet ζ o' m := by
      rw [asymMidMux_mulVec_embedKet, asymMidBranch_of_lt126 prepMid o' hxo',
        embedMatrix_rMidUB_mulVec_embedKet, prepMidDirectXo7Mux_mulVec_embedKet_loc]
    have hMsEq (f : Fin (2 ^ mMidUB wInner2) → Fin (2 ^ (2 * 58)) → ℂ) :
        M_a.1 *ᵥ ((M_s⁻¹).1 *ᵥ ∑ m', embedKet (f m') o' m') = ∑ m', embedKet (f m') o' m' := by
      rw [Matrix.mulVec_sum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun m' _ ↦ ?_
      have hInvMux :=
        prepMidDirectXo7Mux_mulVec_embedKet_loc (wOuter := wOuter) (wInner2 := wInner2)
        (fun rc ↦ (prepMid (pi128Equiv rc))⁻¹) (f m') o' m'
      have hInvEq : M_s⁻¹ = prepMidDirectXo7MuxUnitary wOuter wInner2
          (fun rc ↦ (prepMid (pi128Equiv rc))⁻¹) := muxUnitary_inv _ _ _ _
      rw [hInvEq, hInvMux, Matrix.mulVec_sum]
      have hs (x : Fin (2 ^ mMidUB wInner2)) :
          M_a.1 *ᵥ ((((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o')))⁻¹).1 x m') •
            embedKet (f m') o' x) =
          M_s.1 *ᵥ ((((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o')))⁻¹).1 x m') •
            embedKet (f m') o' x) := by rw [Matrix.mulVec_smul, hMa, Matrix.mulVec_smul]
      rw [Finset.sum_congr rfl fun x _ ↦ hs x, ← Matrix.mulVec_sum, ← hInvMux, ← hInvEq,
        Matrix.mulVec_mulVec, hMsMulInv, Matrix.one_mulVec]
    have hMaUI : M_a.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0) =
        ∑ m', embedKet (((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0) •
          ((idealPi145Branch wOuter wInner2 o' m').1 *ᵥ ξ)) o' m' := by
      simp only [U_I, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      have hSum : (idealPi145SelectPure wOuter wInner2).1 *ᵥ (M_s.1 *ᵥ embedKet ξ o' 0) =
          ∑ m', embedKet (((prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0) •
            ((idealPi145Branch wOuter wInner2 o' m').1 *ᵥ ξ)) o' m' := by
        rw [prepMidDirectXo7Mux_mulVec_embedKet_loc, Matrix.mulVec_sum]
        exact Finset.sum_congr rfl fun m' _ ↦ by
          rw [Matrix.mulVec_smul, idealPi145SelectPure_mulVec_embedKet, embedKet_smul]
      rw [hSum, hMsEq]
    have hrc126 : ((rXo7Loc wOuter).extractIndex o').val < 126 := by
      rwa [extract_rXo7Loc_of_lt128 o' (by omega)]
    have hpi126 := pi128Equiv_lt126_of_lt126 _ hrc126
    have hbAct (m' : Fin (2 ^ mMidUB wInner2))
        (hnz : (prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0 ≠ 0) :
        ((rXoLoc wOuter).extractIndex o').val < 126 ∧ ((rBLoc wInner2).extractIndex m').val < 30 :=
      ⟨hxo', by_contra fun hge ↦ hnz (hB30 ⟨_, hpi126⟩ m' (by omega))⟩
    have hF : (D * select55NoNegFwdPureUnitary wOuter wInner2).1 *ᵥ
        (M_a.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0))
        =
        (D * select57NoNegFwdPureUnitary wOuter wInner2).1 *ᵥ
          (M_a.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0)) := by
      rw [hMaUI, Matrix.mulVec_sum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun m' _ ↦ ?_
      by_cases hnz : (prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0 = 0
      · simp only [hnz, zero_smul, embedKet_zero, Matrix.mulVec_zero]
      · rw [embedKet_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Submonoid.coe_mul,
          Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          (r55_eq57_embedKet _ o' m' (Or.inl (hbAct m' hnz))).1]
    have hB : (select55NoNegBwdPureUnitary wOuter wInner2 * D).1 *ᵥ
        (M_a.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0))
        =
        (select57NoNegBwdPureUnitary wOuter wInner2 * D).1 *ᵥ
          (M_a.1 *ᵥ (U_I.1 *ᵥ embedKet ξ o' 0)) := by
      rw [hMaUI, Matrix.mulVec_sum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun m' _ ↦ ?_
      by_cases hnz : (prepMid (pi128Equiv ((rXo7Loc wOuter).extractIndex o'))).1 m' 0 = 0
      · simp only [hnz, zero_smul, embedKet_zero, Matrix.mulVec_zero]
      · dsimp only [D]
        rw [embedKet_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Submonoid.coe_mul,
          Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          dNegUB_mulVec_embedKet, Matrix.mulVec_smul, Matrix.mulVec_smul,
          (r55_eq57_embedKet _ o' m' (Or.inl (hbAct m' hnz))).2]
    exact ⟨hLift hF, hLift hB⟩
  have hRmid0 (ξ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) :
      R_mid.1 *ᵥ embedKet ξ o' 0 = (-1 : ℂ) • embedKet ξ o' 0 := by
    change (1 - (2 : ℂ) • (rMidUB wOuter wInner2).basisOutcomeProjector 0) *ᵥ embedKet ξ o' 0 = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, projMid_mulVec_embedKet,
      ite_eq_left rfl]
    module
  have hProjB (w : Fin (2 ^ nUB wOuter wInner2) → ℂ) :
      B55.1 *ᵥ ((rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ w) =
        B57.1 *ᵥ ((rMidUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ w) := by
    have hw : w = ∑ g, w g • Pi.single g 1 := funext fun i ↦ by simp [Pi.single_apply]
    rw [hw, Matrix.mulVec_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, single_eq_embedKet g,
      projMid_mulVec_embedKet]
    by_cases hm0 : (rMidUB wOuter wInner2).extractIndex g = 0
    · rw [ite_eq_left hm0, (hMidZeroEq _ _).2]
    · rw [ite_eq_right hm0, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hRmExpand (y : Fin (2 ^ nUB wOuter wInner2) → ℂ) (hy : B55.1 *ᵥ y = B57.1 *ᵥ y) :
      B55.1 *ᵥ (R_mid.1 *ᵥ y) = B57.1 *ᵥ (R_mid.1 *ᵥ y) := by
    change B55.1 *ᵥ ((1 - (2 : ℂ) • (rMidUB wOuter wInner2).basisOutcomeProjector 0) *ᵥ y) =
      B57.1 *ᵥ ((1 - (2 : ℂ) • (rMidUB wOuter wInner2).basisOutcomeProjector 0) *ᵥ y)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hy, hProjB y]
  have hTri (A B C : Unitary (2 ^ nUB wOuter wInner2)) (v : Fin (2 ^ nUB wOuter wInner2) → ℂ) :
      (A * B * C).1 *ᵥ v = A.1 *ᵥ (B.1 *ᵥ (C.1 *ᵥ v)) := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change (B55 * R_mid * F55).1 *ᵥ x = (B57 * R_mid * F57).1 *ᵥ x
  induction hx with
  | zero => simp only [Matrix.mulVec_zero]
  | add _ _ ih1 ih2 => rw [Matrix.mulVec_add, Matrix.mulVec_add, ih1, ih2]
  | smul c _ ih => rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ih]
  | twoBodyU ψ o' h126 =>
    have hAs := asymHalfStep_eq_symHalfStep_of_lt126 hB30 hd ψ o' h126
    change (B55 * R_mid * F55).1 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0) =
      (B57 * R_mid * F57).1 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0)
    rw [hTri B55 R_mid F55, hTri B57 R_mid F57, (hTwoBodyUEq ψ o' h126).1,
      show F57.1 *ᵥ (U_I.1 *ᵥ embedKet ψ o' 0) = embedKet ψ o' 0 from hAs.2.2.2,
      hRmid0, Matrix.mulVec_smul, Matrix.mulVec_smul, (hMidZeroEq ψ o').2]
  | midZero ψ o' _ =>
    rw [hTri B55 R_mid F55, hTri B57 R_mid F57, (hMidZeroEq ψ o').1]
    by_cases h126 : ((rXoLoc wOuter).extractIndex o').val < 126
    · have hAs := asymHalfStep_eq_symHalfStep_of_lt126 hB30 hd ψ o' h126
      rw [show F57.1 *ᵥ embedKet ψ o' 0 = U_I.1 *ᵥ embedKet ψ o' 0 from hAs.1]
      exact hRmExpand _ (hTwoBodyUEq ψ o' h126).2
    · have hge126 : 126 ≤ ((rXoLoc wOuter).extractIndex o').val := by omega
      have hMaConj (S_mid : Unitary (2 ^ nUB wOuter wInner2)) (V : Unitary (2 ^ (2 * 58)))
          (ξ : Fin (2 ^ (2 * 58)) → ℂ) (hBr : ∀ m', (asymMidBranch prepMid o').1 m' 0 ≠ 0 →
            S_mid.1 *ᵥ embedKet ξ o' m' = embedKet (V.1 *ᵥ ξ) o' m') :
          (M_a⁻¹ * S_mid * M_a).1 *ᵥ embedKet ξ o' 0 = embedKet (V.1 *ᵥ ξ) o' 0 := by
        rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          asymMidMux_mulVec_embedKet]
        have hMid : S_mid.1 *ᵥ ((rMidUB wOuter wInner2).embedMatrix (asymMidBranch prepMid o').1 *ᵥ
            embedKet ξ o' 0) =
            ∑ m', embedKet (((asymMidBranch prepMid o').1 m' 0) • (V.1 *ᵥ ξ)) o' m' := by
          rw [embedMatrix_rMidUB_mulVec_embedKet, Matrix.mulVec_sum]
          refine Finset.sum_congr rfl fun m' _ ↦ ?_
          by_cases hz : (asymMidBranch prepMid o').1 m' 0 = 0
          · simp only [hz, zero_smul, Matrix.mulVec_zero, embedKet_zero]
          · rw [Matrix.mulVec_smul, hBr m' hz, embedKet_smul]
        have hInvSum (g : Fin (2 ^ mMidUB wInner2) → (Fin (2 ^ (2 * 58)) → ℂ)) :
            (M_a⁻¹).1 *ᵥ ∑ m', embedKet (g m') o' m' =
              (rMidUB wOuter wInner2).embedMatrix ((asymMidBranch prepMid o')⁻¹).1 *ᵥ
                ∑ m', embedKet (g m') o' m' := by
          rw [Matrix.mulVec_sum, Matrix.mulVec_sum]
          exact Finset.sum_congr rfl fun m' _ ↦ asymMidMux_inv_mulVec_embedKet prepMid (g m') o'
              m'
        rw [hMid, hInvSum, ← hMid]
        exact conj_rMidUB_mulVec_embedKet_const_branch _ S_mid V ξ o' hBr
      by_cases h184 : ((rXoLoc wOuter).extractIndex o').val < 184
      · let xo' := (rXoLoc wOuter).extractIndex o'
        let so := (rSigOutLoc wOuter).extractIndex o'
        let br1 := selectBranchUnitary (pi145XoEquiv xo') so 0 1
        have h1B : (pi145XoEquiv xo').val < 58 := pi145XoEquiv_h1B xo' hge126 h184
        let VF : Unitary (2 ^ (2 * 58)) := if inPass1Pi145Xo xo' then br1 else 1
        have hF57 : F57.1 *ᵥ embedKet ψ o' 0 = embedKet (VF.1 *ᵥ ψ) o' 0 :=
          hMaConj (D * select57NoNegFwdPureUnitary wOuter wInner2) VF ψ fun m' hnz ↦ by
            have hsi0 := asymMidBranchZero_of_oneBody hSpin o' hge126 h184 m' hnz
            have h1s := (select57NoNegPureUnitary_mulVec_oneBodyZero ψ o' m' hge126 h184
                hsi0).1
            rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, h1s,
              selectBranchUnitary_oneBody1 h1B so ((rBLoc wInner2).extractIndex m')]
            dsimp only [VF, br1, xo', so, D]
            cases inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') <;>
              simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_one, Matrix.one_mulVec,
                dNegUB_mulVec_embedKet, hd.2 ((rXoLoc wOuter).extractIndex o') _ hge126, one_smul]
        rw [hF57, hRmid0, Matrix.mulVec_smul, Matrix.mulVec_smul, (hMidZeroEq (VF.1 *ᵥ ψ) o').2]
      · have hge184 : 184 ≤ ((rXoLoc wOuter).extractIndex o').val := by omega
        have hF57 : F57.1 *ᵥ embedKet ψ o' 0 = embedKet ψ o' 0 := by
          simpa only [Submonoid.coe_one, Matrix.one_mulVec] using
            hMaConj (D * select57NoNegFwdPureUnitary wOuter wInner2) 1 ψ fun m' _ ↦ by
              dsimp only [D]
              rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
                select57NoNegPureUnitary_mulVec_ge184 false ψ o' m' hge184,
                dNegUB_mulVec_embedKet, hd.2 ((rXoLoc wOuter).extractIndex o') _ hge126,
                ite_eq_right Bool.false_ne_true, one_smul, Submonoid.coe_one, Matrix.one_mulVec]
        rw [hF57, hRmid0, Matrix.mulVec_smul, Matrix.mulVec_smul, (hMidZeroEq ψ o').2]

theorem walkRefl2InvErrLe_noNegDNeg55_ideal {wOuter wInner2 : ℕ} (prepOutImpl : Unitary (2 ^ mOutUB
    wOuter))
    {prepMid : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)} (hSpin : PrepMidSpinFactored prepMid)
    (hB30 : ∀ (rc : Fin 126) (m : Fin (2 ^ mMidUB wInner2)),
      30 ≤ ((rBLoc wInner2).extractIndex m).val → (prepMid ⟨rc.val, by omega⟩).1 m 0 = 0)
    {dBit : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool} (hd : IsValidDNegBit dBit)
    {sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    (hsF : SelCatEqOuterInner wOuter wInner2 sF (select55NoNegFwdPureUnitary wOuter wInner2))
    (hsB : SelCatEqOuterInner wOuter wInner2 sB (select55NoNegBwdPureUnitary wOuter wInner2)) :
    WalkRefl2InvErrLe wOuter wInner2
      (ubDirectXo7PureUnitary prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc))
        (idealPi145SelectPure wOuter wInner2))
      (asymURefl2 prepOutImpl prepMid dBit sF sB) 0 := by
  let Out := (rOutUB wOuter wInner2).embedUnitary prepOutImpl
  let M_s := prepMidDirectXo7MuxUnitary wOuter wInner2 (fun rc ↦ prepMid (pi128Equiv rc))
  let U_ref := M_s⁻¹ * idealPi145SelectPure wOuter wInner2 * M_s
  let K_ref := U_ref * QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2) * U_ref
  let P_inv : (Fin (2 ^ nUB wOuter wInner2) → ℂ) → Prop := fun v ↦
    PostOutInv wOuter wInner2 prepMid false (Out.1 *ᵥ v)
  have hZ0 (ξ : Fin (2 ^ (2 * 58)) → ℂ) : P_inv (embedKet ξ 0 0) := by
    dsimp only [P_inv, Out]
    rw [QRegister.embedUnitary_val, embedMatrix_rOutUB_mulVec_embedKet]
    exact PostOutInv.sum Finset.univ _ fun o' _ ↦
      .smul _ (.midZero ξ o' fun h ↦ Bool.noConfusion h)
  have hUref_sq : U_ref * U_ref = 1 := by
    have hAssoc : U_ref * U_ref =
        M_s⁻¹ * idealPi145SelectPure wOuter wInner2 * (M_s * M_s⁻¹) *
          idealPi145SelectPure wOuter wInner2 * M_s := by
      dsimp only [U_ref]
      simp only [mul_assoc]
    rw [hAssoc, mul_inv_cancel, mul_one, mul_assoc (M_s⁻¹),
      idealPi145SelectPure_mul_self, mul_one, inv_mul_cancel]
  have hR2Eq : QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2))
      (ubDirectXo7PureUnitary prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc))
        (idealPi145SelectPure wOuter wInner2)) = Out⁻¹ * K_ref * Out := by
    have hrM : rMidInWalk (mOutUB wOuter) (mMidUB wInner2) = rMidUB wOuter wInner2 :=
      CoherentAlias.qreg_ext fun _ ↦ rfl
    have huB : ubDirectXo7PureUnitary prepOutImpl (fun rc ↦ prepMid (pi128Equiv rc))
        (idealPi145SelectPure wOuter wInner2) = U_ref * Out := rfl
    rw [QubitisedWalk.reflPulledUnitary, QubitisedWalk.reflPulledPair, hrM, huB, _root_.mul_inv_rev,
      inv_eq_of_mul_eq_one_right hUref_sq]
    simp only [K_ref, mul_assoc]
  refine ⟨P_inv, fun ψ ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · rw [show rSysInWalk (mOutUB wOuter) (mMidUB wInner2) = rSysUB wOuter wInner2 from
      CoherentAlias.qreg_ext fun _ ↦ rfl, ← embedKet_zero_zero_eq_tensorState]
    exact hZ0 ψ
  · dsimp only [P_inv]
    rw [show rAllInWalk (mOutUB wOuter) (mMidUB wInner2) = rAllUB wOuter wInner2 from
        CoherentAlias.qreg_ext fun _ ↦ rfl, QubitisedWalk.reflInUnitary_val, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_add_neg, Matrix.mulVec_add,
      Matrix.mulVec_smul, ← neg_one_smul ℂ v, Matrix.mulVec_smul]
    refine .add (.smul 2 ?_) (.smul (-1) hv)
    have hv_sum : v = ∑ g : Fin (2 ^ nUB wOuter wInner2), v g • Pi.single g 1 := by
      ext i
      simp [Pi.single_apply]
    rw [hv_sum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    refine PostOutInv.sum Finset.univ _ fun g _ ↦ ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, single_eq_embedKet g]
    change PostOutInv _ _ _ _ (v g • (Out.1 *ᵥ ((rAllUB wOuter wInner2).basisOutcomeProjector 0 *ᵥ
      _)))
    rw [projAll_mulVec_embedKet]
    by_cases hc : (rOutUB wOuter wInner2).extractIndex g =
        0 ∧ (rMidUB wOuter wInner2).extractIndex g = 0
    · rw [ite_eq_left hc]
      exact .smul (v g) (hZ0 _)
    · rw [ite_eq_right hc, Matrix.mulVec_zero, smul_zero]
      exact .zero
  · obtain ⟨hKId, _, _⟩ := kernel_step hSpin hB30 hd hv
    have hOutMulInv : Out.1 * (Out⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel Out)
    dsimp only [P_inv]
    rw [hR2Eq, Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Out.1 (Out⁻¹).1, hOutMulInv,
      Matrix.one_mulVec]
    exact hKId
  · obtain ⟨_, hKAs57, _⟩ := kernel_step hSpin hB30 hd hv
    have h55_57 := kAsym55_eq57_on_postOutInv hSpin hB30 hd hv
    dsimp only at h55_57
    rw [zero_mul, uRefl2_noNegDNeg_mulVec_walkCat_gen prepOutImpl prepMid dBit hsF hsB v, hR2Eq]
    let M_a := asymMidMux wOuter wInner2 prepMid
    let K55 :=
      M_a⁻¹ * (select55NoNegBwdPureUnitary wOuter wInner2 * dNegUB wOuter wInner2 dBit) * M_a *
      QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2) *
      (M_a⁻¹ * (dNegUB wOuter wInner2 dBit * select55NoNegFwdPureUnitary wOuter wInner2) * M_a)
    have hVecEq : (Out⁻¹ * K55 * Out).1 *ᵥ v = (Out⁻¹ * K_ref * Out).1 *ᵥ v := by
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [h55_57, hKAs57]
    rw [hVecEq, sub_self, WithLp.toLp_zero, norm_zero]

theorem walkKStepRefl2InvErrLe_zero_of_exact {wOuter wInner2 K : ℕ} (hK : 1 ≤ K)
    {uB : Unitary (2 ^ nUB wOuter wInner2)}
    {uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))}
    (h : WalkRefl2InvErrLe wOuter wInner2 uB uRefl2 0) :
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    TailShiftThreeGear.WalkKStepRefl2InvErrLe wOuter wInner2 K uB
      (uRefl2 * (R₁c * uRefl2) ^ (K - 1)) 0 := by
  intro R₁c
  obtain ⟨P_inv, hInit, hR1, hR2, hErr⟩ := h
  refine ⟨P_inv, hInit, hR1, hR2, ?_⟩
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let cat := CircuitModular.phaseGradientLowFactor 11 3
  let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
  let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
  have hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0 := by
    refine ⟨hR1, fun v _ ↦ ?_⟩
    rw [zero_mul]
    have heq : R₁c.1 *ᵥ tensorWalkCat v cat = tensorWalkCat (R₁.1 *ᵥ v) cat := by
      dsimp only [R₁c]
      rw [tgEmbedUnitary_rWalkInWalkCat_reflIn, QRegister.embedUnitary_val]
      exact embedMatrix_rWalkInWalkCat_mulVec R₁.1 v cat
    rw [heq, sub_self, WithLp.toLp_zero, norm_zero]
  have hRelR₂ : InvCatRel P_inv cat uRefl2 R₂ 0 := ⟨hR2, hErr⟩
  have hRelW : InvCatRel P_inv cat (R₁c * uRefl2) (R₁ * R₂) 0 := by
    simpa only [zero_add] using invCatRel_mul hRelR₁ hRelR₂
  have hRelSup := invCatRel_mul hRelR₂ (invCatRel_pow hRelW (K - 1))
  have hIdEq : R₁ * (R₁ * R₂) ^ K = R₂ * (R₁ * R₂) ^ (K - 1) := by
    have hm : K = (K - 1) + 1 := by omega
    conv_lhs => rw [hm, pow_succ']
    calc R₁ * ((R₁ * R₂) * (R₁ * R₂) ^ (K - 1))
        = (R₁ * R₁) * R₂ * (R₁ * R₂) ^ (K - 1) := by simp only [mul_assoc]
      _ = R₂ * (R₁ * R₂) ^ (K - 1) := by rw [QubitisedWalk.reflInUnitary_mul_self, one_mul]
  intro v hv
  have hSupV := hRelSup.2 v hv
  rw [← hIdEq] at hSupV
  simpa only [mul_zero, add_zero] using hSupV

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Select55PureBridge
end
