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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsA
/-!
# Narrow `wInner2 = 18` + `46-T` Hadamard W-State Walk Legs — Part B (Alignment, Step 1 & `-D_l`)

Continuation of `Inner18HadWSuperLegsA`:
1. `mainSpinCancel22Dyn`: `22-T` hot-context `s_i = 0` spin-cancellation widget.
2. `inner18Mfwd` & `hot128Neg_walkRefl_eq_defaultNeg` (`Hot128` vs `Default` `-D_l` alignment).
3. `workPlace` local `(32 + kInner)`-wire workspace placement & Bell/`rSys116` disjointness.
4. `qromW642Keep9Mid31UnloadDyn` (`212-T` Keep-9 cold Step-4 `31`-bit unloader).
5. `inner18Step1Dyn` (`314 + tLoad14 + tMag` `T` Step-1 forward leg) & `HotDNegBundle`.
-/

@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsB
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450 CoherentAlias CleanDyn AliasPrep
open CircuitModular GivensOps MidReflCtxRetain
open Phase2MidSandwich OptFactoredMag30AndCoin9 QuantizedFactoredMag30
open Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast OptXMeasUnload21
open Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 TopIntegrationBridge
open MobiusOptSubcube163Walk CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20
open Pi145SOSPermBridge StepOuter8Pi145Outer StepOuter8Pi145L1 StepKeep9Symp14Data
open StepBound148Borrow Tuned155Hot128SympQrom20 CompactOuter9Bound50Core LowBitPi145Select
open BellSingletCSwap58 FastUniform Inner18Symp14Walk HGadgetSympQrom
open QRegister InnerTable GroupUnary Pi145CompactRouter HadWStateMux25CompactA
open HadWStateMux25CompactB
open CircuitModular.UnsignedGivens (maskSumBit basisBits_symm_eq cnotMaskReg
  evolve_cnotMaskReg_ket eval_identity_mulVec)
open Function (update update_of_ne update_self update_apply)
open Observable (conj_coe)
open Unitary (coe_star)
open Submonoid (coe_mul)
open DynamicCircuit (qc_wp_circuit_compile compile_circuit)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Inner18HadWSuperLegsA
local instance (priority := 1000000) instNeZeroTwoPowLegsB (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
/-! ## Section 4: Spin Cancellation (`22-T` / `2-T`), `inner18Mfwd` & `D_hot = D_def` Alignment -/

theorem muxCongr {n kc kt : ℕ} {rC₁ rC₂ : QRegister kc n} {rT₁ rT₂ : QRegister kt n}
    (hC : rC₁ = rC₂) (hT : rT₁ = rT₂) (hd₁ : rC₁.DisjointWires rT₁) (hd₂ : rC₂.DisjointWires rT₂)
    {F₁ F₂ : Fin (2 ^ kc) → Unitary (2 ^ kt)} (hF : ∀ c, F₁ c = F₂ c) :
    muxUnitary rC₁ rT₁ hd₁ F₁ = muxUnitary rC₂ rT₂ hd₂ F₂ := by
  subst hC
  subst hT
  exact BlockEncodingCircuit.muxUnitary_congr _ _ hF
theorem muxConst {n kc kt : ℕ} (rC : QRegister kc n) (rT : QRegister kt n)
    (hd : rC.DisjointWires rT) (U : Unitary (2 ^ kt)) :
    muxUnitary rC rT hd (fun _ ↦ U) = rT.embedUnitary U := by
  apply Subtype.ext
  dsimp only [muxUnitary, QRegister.embedUnitary_val]
  rw [← Finset.sum_mul, QRegister.sum_basisOutcomeProjector, one_mul]
theorem muxConstOne {n kc kt : ℕ} (rC : QRegister kc n) (rT : QRegister kt n)
    (hd : rC.DisjointWires rT) : muxUnitary rC rT hd (fun _ ↦ 1) = 1 :=
  (muxConst rC rT hd 1).trans rT.embedUnitary_one
theorem concat_singleton_right {k n : ℕ} (r₁ : QRegister k n) (r₂ : QRegister 1 n)
    (h : r₁.DisjointWires r₂) :
    (r₁.concat r₂ h).compose (QRegister.singleton ⟨k, by omega⟩) = r₂ :=
  CoherentAlias.qreg_ext fun i ↦ by
    fin_cases i
    exact congrArg Fin.val (QRegister.concat_apply_right r₁ r₂ h 0)
theorem preservesWires_muxUnitary {N kc kt : ℕ} (rC : QRegister kc N) (rT : QRegister kt N)
    (hd : rC.DisjointWires rT) (F : Fin (2 ^ kc) → Unitary (2 ^ kt)) (T : Finset (Wire N))
    (hDisj : Disjoint rT.image T) : AliasPrep.PreservesWires (muxUnitary rC rT hd F).1 T :=
  Phase2MidSandwich.preservesWires_sum Finset.univ _ fun c _ ↦
    AliasPrep.preservesWires_mul
      (Phase2MidSandwich.preservesWires_basisOutcomeProjector rC c T)
      (AliasPrep.preservesWires_embedMatrix_of_disjoint rT (F c).1 T hDisj)
theorem circuitH0_mul_self : (Circuit.H (0 : Wire 1)).eval * (Circuit.H 0).eval = 1 := by
  apply Subtype.ext
  apply OneHotSimulates.matrix_ext_ket
  intro β
  have hk : OneHotSimulates.ket = XMeasCircuit.ket (n := 1) := rfl
  have hsq : XMeasCircuit.sqrtHalf ^ 2 = 1 / 2 :=
    by linear_combination XMeasCircuit.sqrtHalf_mul_sqrtHalf
  have h10 : ((1 : ZMod 2) = 0) = False := by decide
  have hu := Function.update_eq_self (0 : Wire 1) β
  rw [hk, coe_mul, OneMemClass.coe_one, Matrix.one_mulVec, ← mulVec_mulVec]
  rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β 0) with hb | hb <;> {
    rw [hb] at hu
    simp only [XMeasCircuit.ket_H, mulVec_smul, Matrix.mulVec_add, hb, h10, ↓reduceIte,
      one_smul, update_self, Function.update_idem, XMeasCircuit.bitSign, smul_add, smul_smul, hu]
    ext idx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    simp only [hsq]
    ring }
theorem circuitH_mul_self {n : ℕ} (q : Wire n) : (Circuit.H q).eval * (Circuit.H q).eval = 1 := by
  have hq : (Circuit.H q).eval = (QRegister.singleton q).embedUnitary (Circuit.H 0).eval := by
    rw [← Circuit.eval_onRegister]
    exact congrArg Circuit.eval (congrArg (Circuit.gate PrimitiveGate.H)
      (CoherentAlias.qreg_ext fun i ↦ by
          fin_cases i
          rfl))
  rw [hq, ← QRegister.embedUnitary_mul, circuitH0_mul_self, QRegister.embedUnitary_one]
theorem cnot_mulVec_H_ket {n : ℕ} (c t q : Wire n) (hct : c ≠ t) (hcq : c ≠ q) (htq : t ≠ q)
    (β : BitAssignment n) :
    (Circuit.CNOT c t hct).eval.1.mulVec ((Circuit.H q).eval.1.mulVec (SelectSwapQROM.ket β)) =
      (Circuit.H q).eval.1.mulVec (SelectSwapQROM.ket (update β t (β t + β c))) := by
  rw [SelectSwapQROM.ket_H, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    SelectSwapQROM.ket_CNOT, SelectSwapQROM.ket_CNOT, SelectSwapQROM.ket_H]
  simp only [update_of_ne hcq, update_of_ne htq, update_of_ne htq.symm,
    Function.update_comm htq.symm]
/-- `2-T`, `0-TOFF` `2`-control XOR-parity controlled-`H` (`w0 ⊕ w1 → H(wSig)`). -/
def cHXor2 {n : ℕ} (w0 w1 wSig : Wire n) (h10 : w1 ≠ w0) (h0s : w0 ≠ wSig) : Circuit n :=
  .seq (Circuit.CNOT w1 w0 h10)
    (.seq (CoherentAlias.ctrlH.onRegister (QRegister.pair w0 wSig h0s))
      (Circuit.CNOT w1 w0 h10))
/-- `2-T`, `0-TOFF` `3`-control XOR-parity controlled-`H` (`w0 ⊕ w1 ⊕ w2 → H(wSig)`). -/
def cHXoMain {n : ℕ} (w0 w1 w2 wSig : Wire n) (h10 : w1 ≠ w0) (h20 : w2 ≠ w0) (h0s : w0 ≠ wSig) :
    Circuit n :=
  .seq (Circuit.CNOT w2 w0 h20)
    (.seq (cHXor2 w0 w1 wSig h10 h0s) (Circuit.CNOT w2 w0 h20))
@[simp] theorem countCHXor2_toff {n : ℕ} (w0 w1 wSig : Wire n) (h10 : w1 ≠ w0)
    (h0s : w0 ≠ wSig) : (cHXor2 w0 w1 wSig h10 h0s).count .TOFF = 0 := by
  simp [cHXor2, Circuit.count_onRegister]
@[simp] theorem countCHXor2_t {n : ℕ} (w0 w1 wSig : Wire n) (h10 : w1 ≠ w0)
    (h0s : w0 ≠ wSig) : (cHXor2 w0 w1 wSig h10 h0s).count .T = 2 := by
  simp [cHXor2, Circuit.count_onRegister]
@[simp] theorem countCHXoMain_toff {n : ℕ} (w0 w1 w2 wSig : Wire n) (h10 : w1 ≠ w0)
    (h20 : w2 ≠ w0) (h0s : w0 ≠ wSig) : (cHXoMain w0 w1 w2 wSig h10 h20 h0s).count .TOFF = 0 := by
  simp [cHXoMain]
@[simp] theorem countCHXoMain_t {n : ℕ} (w0 w1 w2 wSig : Wire n) (h10 : w1 ≠ w0)
    (h20 : w2 ≠ w0) (h0s : w0 ≠ wSig) : (cHXoMain w0 w1 w2 wSig h10 h20 h0s).count .T = 2 := by
  simp [cHXoMain]
theorem ketCHXor2 {n : ℕ} (w0 w1 wSig : Wire n) (h10 : w1 ≠ w0) (h0s : w0 ≠ wSig)
    (h1s : w1 ≠ wSig) (β : BitAssignment n) :
    (cHXor2 w0 w1 wSig h10 h0s).eval.1.mulVec (SelectSwapQROM.ket β) =
      if β w0 + β w1 = 1 then (Circuit.H wSig).eval.1.mulVec (SelectSwapQROM.ket β)
      else SelectSwapQROM.ket β := by
  have hRest : update (update β w0 (β w0 + β w1)) w0
      (update β w0 (β w0 + β w1) w0 + update β w0 (β w0 + β w1) w1) = β := by
    rw [update_self, update_of_ne h10, Function.update_idem, add_assoc,
      CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
  dsimp only [cHXor2]
  rw [SelectSwapQROM.eval_seq_mulVec, SelectSwapQROM.eval_seq_mulVec,
    SelectSwapQROM.ket_CNOT, ket_ctrlH_pair, update_self]
  by_cases h1 : β w0 + β w1 = 1
  · rw [ite_eq_left h1, ite_eq_left h1, cnot_mulVec_H_ket w1 w0 wSig h10 h1s h0s, hRest]
  · rw [ite_eq_right h1, ite_eq_right h1, SelectSwapQROM.ket_CNOT, hRest]
theorem ketCHXoMain {n : ℕ} (w0 w1 w2 wSig : Wire n) (h10 : w1 ≠ w0) (h20 : w2 ≠ w0)
    (h0s : w0 ≠ wSig) (h1s : w1 ≠ wSig) (h2s : w2 ≠ wSig) (_h21 : w2 ≠ w1) (β : BitAssignment n) :
    (cHXoMain w0 w1 w2 wSig h10 h20 h0s).eval.1.mulVec (SelectSwapQROM.ket β) =
      if β w0 + β w2 + β w1 = 1 then (Circuit.H wSig).eval.1.mulVec (SelectSwapQROM.ket β)
      else SelectSwapQROM.ket β := by
  have hRest : update (update β w0 (β w0 + β w2)) w0
      (update β w0 (β w0 + β w2) w0 + update β w0 (β w0 + β w2) w2) = β := by
    rw [update_self, update_of_ne h20, Function.update_idem, add_assoc,
      CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
  dsimp only [cHXoMain]
  rw [SelectSwapQROM.eval_seq_mulVec, SelectSwapQROM.eval_seq_mulVec,
    SelectSwapQROM.ket_CNOT, ketCHXor2 w0 w1 wSig h10 h0s h1s, update_self, update_of_ne h10]
  by_cases h1 : β w0 + β w2 + β w1 = 1
  · rw [ite_eq_left h1, ite_eq_left h1, cnot_mulVec_H_ket w2 w0 wSig h20 h2s h0s, hRest]
  · rw [ite_eq_right h1, ite_eq_right h1, SelectSwapQROM.ket_CNOT, hRest]
/-- Boolean indicator `126 ≤ xo.val < 254` (`b₇ ^^ hot₁₂₆ ^^ hot₁₂₇`). -/
def is1BBool2 (xo : Fin (2 ^ 8)) : Bool := decide (126 ≤ xo.val ∧ xo.val < 254)
theorem is1BBool_eq_hotZMod (xo : Fin (2 ^ 8)) :
    let x7 : Fin (2 ^ 7) := (QRegister.block 0 7 (by decide)).extractIndex xo
    is1BBool2 xo = decide (basisBits 8 xo ⟨7, by decide⟩ +
      (if x7 = ⟨126, by decide⟩ then 1 else 0) +
      (if x7 = ⟨127, by decide⟩ then 1 else 0) = (1 : ZMod 2)) := by
  intro x7
  have hb7 : basisBits 8 xo ⟨7, by decide⟩ = if xo.val / 128 % 2 = 1 then 1 else 0 := by
    have hd : decide (basisBits 8 xo ⟨7, by decide⟩ = 1) = decide (xo.val / 128 % 2 = 1) :=
      bitsOfFin_eq_div_mod_b xo ⟨7, by decide⟩
    rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (basisBits 8 xo ⟨7, by decide⟩) with
        h0 | h1
    · rw [h0, show decide ((0 : ZMod 2) = 1) = false from rfl] at hd
      rw [h0, ite_eq_right (of_decide_eq_false hd.symm)]
    · rw [h1, show decide ((1 : ZMod 2) = 1) = true from rfl] at hd
      rw [h1, ite_eq_left (of_decide_eq_true hd.symm)]
  have hx (g : ℕ) (hg : g < 128) : (x7 = ⟨g, hg⟩) ↔ xo.val % 128 = g := by
    rw [Fin.ext_iff]
    change ((QRegister.block 0 7 (by decide)).extractIndex xo).val = g ↔ _
    rw [CoherentAlias.extractIndex_block_val (by decide : 0 + 7 ≤ 8) xo]
    simp
  have hlt := xo.isLt
  simp only [is1BBool2, hb7, hx 126 (by decide), hx 127 (by decide)]
  rcases (by omega :
      (xo.val < 126 ∧ xo.val / 128 % 2 ≠ 1 ∧ xo.val % 128 ≠ 126 ∧ xo.val % 128 ≠ 127) ∨
      xo.val = 126 ∨ xo.val = 127 ∨
      (128 ≤ xo.val ∧ xo.val < 254 ∧ xo.val / 128 % 2 = 1 ∧
        xo.val % 128 ≠ 126 ∧ xo.val % 128 ≠ 127) ∨
      xo.val = 254 ∨ xo.val = 255) with
    ⟨h1, h2, h3, h4⟩ | h | h | ⟨h1, h2, h3, h4, h5⟩ | h | h
  · rw [decide_eq_false (by omega), ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    decide
  · rw [h]
    decide
  · rw [h]
    decide
  · rw [decide_eq_true ⟨by omega, h2⟩, ite_eq_left h3, ite_eq_right h4, ite_eq_right h5]
    decide
  · rw [h]
    decide
  · rw [h]
    decide
/-- `(wOuter, wInner2)`-polymorphic controlled-`H` spin-cancellation mux on `rSigInLoc wInner2` by
`rXoUB`. -/
noncomputable def mainSpinCancelUBMux (wOuter wInner2 : ℕ) : Unitary (2 ^ nUB wOuter wInner2) :=
  muxUnitary (rXoUB wOuter wInner2) ((rMidUB wOuter wInner2).compose (rSigInLoc wInner2))
    ((disjoint_rOutUB_rMidUB wOuter wInner2).compose_left _ |>.compose_right _)
    (fun xo ↦ if is1BBool2 xo then (Circuit.H 0).eval else 1)
/-- `mMidUB wInner2` sub-register inside `mMidUB wInner2 + 8`. -/
abbrev midInMX (wInner2 : ℕ) : QRegister (mMidUB wInner2) (mMidUB wInner2 + 8) :=
  QRegister.block 0 (mMidUB wInner2) (by omega)
/-- `8`-wire `xo` sub-register inside `mMidUB wInner2 + 8`. -/
abbrev xo8InMX (wInner2 : ℕ) : QRegister 8 (mMidUB wInner2 + 8) :=
  QRegister.block (mMidUB wInner2) 8 (by omega)
/-- Low `7`-wire `xo[0..6]` sub-register inside `mMidUB wInner2 + 8`. -/
abbrev xo7InMX (wInner2 : ℕ) : QRegister 7 (mMidUB wInner2 + 8) :=
  (xo8InMX wInner2).compose (QRegister.block 0 7 (by decide))
/-- `(mMidUB wInner2 + 8)`-wire `(rMidUB ++ rXoUB)` bundle extracted from `rUB`. -/
abbrev mXOfUB {N wOuter wInner2 : ℕ} (rUB : QRegister (nUB wOuter wInner2) N) : QRegister
    (mMidUB wInner2 + 8) N :=
  (rUB.compose (rMidUB wOuter wInner2)).concat (rUB.compose (rXoUB wOuter wInner2))
    (compose_disjoint_zc20 rUB ((disjoint_rOutUB_rMidUB wOuter wInner2).compose_left _).symm)
theorem xo8InMX_disjoint_sig (wInner2 : ℕ) :
    (xo8InMX wInner2).DisjointWires ((midInMX wInner2).compose (rSigInLoc wInner2)) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  simp only [xo8InMX, midInMX, QRegister.compose_apply, QRegister.block_apply_val] at hv
  have := (rSigInLoc wInner2 j).isLt
  dsimp [mMidUB] at hv this
  omega
theorem midInMX_disjoint_xo7 (wInner2 : ℕ) : (midInMX wInner2).DisjointWires (xo7InMX wInner2) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  have := i.isLt
  simp only [midInMX, xo7InMX, xo8InMX, QRegister.compose_apply,
    QRegister.block_apply_val] at hv
  omega
theorem xo7InMX_disjoint_mid (wInner2 : ℕ) : (xo7InMX wInner2).DisjointWires (midInMX wInner2) :=
  (midInMX_disjoint_xo7 wInner2).symm
/-- `(mMidUB wInner2 + 8)`-wire controlled-`H` spin-cancellation mux on `rSigInLoc wInner2`. -/
noncomputable def spinCancelMXMux (wInner2 : ℕ) : Unitary (2 ^ (mMidUB wInner2 + 8)) :=
  muxUnitary (xo8InMX wInner2) ((midInMX wInner2).compose (rSigInLoc wInner2))
    (xo8InMX_disjoint_sig wInner2) (fun xo ↦ if is1BBool2 xo then (Circuit.H 0).eval else 1)
theorem spinCancelMXMux_mul_self (wInner2 : ℕ) :
    spinCancelMXMux wInner2 * spinCancelMXMux wInner2 = 1 := by
  unfold spinCancelMXMux
  rw [muxUnitary_mul]
  exact (muxCongr rfl rfl (xo8InMX_disjoint_sig wInner2) (xo8InMX_disjoint_sig wInner2) fun xo ↦ by
    cases is1BBool2 xo <;>
      simp only [↓reduceIte, Bool.false_eq_true, circuitH0_mul_self, mul_one]).trans
        (muxConstOne _ _ (xo8InMX_disjoint_sig wInner2))
theorem embedSpinCancelMXMux_ofUB {N wOuter wInner2 : ℕ} (rUB : QRegister (nUB wOuter wInner2) N) :
    (mXOfUB rUB).embedUnitary (spinCancelMXMux wInner2) =
      rUB.embedUnitary (mainSpinCancelUBMux wOuter wInner2) := by
  dsimp only [spinCancelMXMux, mainSpinCancelUBMux]
  rw [embedUnitary_muxUnitary, embedUnitary_muxUnitary]
  have h1 : (mXOfUB rUB).compose (xo8InMX wInner2) = rUB.compose (rXoUB wOuter wInner2) :=
    concat_compose_block_right _ _ _ _
  have h2 : (mXOfUB rUB).compose ((midInMX wInner2).compose (rSigInLoc wInner2)) =
      rUB.compose ((rMidUB wOuter wInner2).compose (rSigInLoc wInner2)) :=
    (QRegister.compose_assoc _ _ _).symm.trans ((congrArg
      (fun r : QRegister (mMidUB wInner2) N ↦ r.compose (rSigInLoc wInner2))
      (concat_compose_block_left _ _ _ _)).trans (QRegister.compose_assoc _ _ _))
  exact muxCongr h1 h2 _ _ fun _ ↦ rfl
theorem embed_xo7MuxMX_ofUB {N wOuter wInner2 : ℕ} (rUB : QRegister (nUB wOuter wInner2) N)
    (F : Fin (2 ^ 7) → Unitary (2 ^ mMidUB wInner2)) :
    (mXOfUB rUB).embedUnitary (muxUnitary (xo7InMX wInner2) (midInMX wInner2)
      (xo7InMX_disjoint_mid wInner2) F) =
      rUB.embedUnitary (prepMidDirectXo7MuxUnitary wOuter wInner2 F) := by
  dsimp only [prepMidDirectXo7MuxUnitary]
  rw [embedUnitary_muxUnitary, embedUnitary_muxUnitary]
  have h8eq : (mXOfUB rUB).compose (xo8InMX wInner2) = rUB.compose (rXoUB wOuter wInner2) :=
    concat_compose_block_right _ _ _ _
  have hsub : (rXoUB wOuter wInner2).compose (QRegister.block 0 7 (by decide)) =
      rXo7UB wOuter wInner2 :=
    CoherentAlias.qreg_ext fun i ↦ by
      dsimp only [rXoUB, rXo7UB, rOutUB, rXoLoc, rXo7Loc, QRegister.compose_apply,
        QRegister.block_apply_val]
  have h1 : (mXOfUB rUB).compose (xo7InMX wInner2) = rUB.compose (rXo7UB wOuter wInner2) :=
    (QRegister.compose_assoc _ _ _).symm.trans ((congrArg
      (fun r : QRegister 8 N ↦ r.compose (QRegister.block 0 7 (by decide))) h8eq).trans
      ((QRegister.compose_assoc _ _ _).trans (congrArg (rUB.compose ·) hsub)))
  have h2 : (mXOfUB rUB).compose (midInMX wInner2) = rUB.compose (rMidUB wOuter wInner2) :=
    concat_compose_block_left _ _ _ _
  exact muxCongr h1 h2 _ _ fun _ ↦ rfl
/-- `(mMidUB wInner2 + 1)`-wire active sub-register `midInMX wInner2 ++ [xo8InMX wInner2 7]`. -/
def actInMX (wInner2 : ℕ) : QRegister (mMidUB wInner2 + 1) (mMidUB wInner2 + 8) :=
  (midInMX wInner2).concat (QRegister.singleton (xo8InMX wInner2 ⟨7, by decide⟩))
    (by rw [QRegister.disjoint_iff]
        intro i j hij
        fin_cases j
        have hv := congrArg Fin.val hij
        have := i.isLt
        simp only [midInMX, xo8InMX, QRegister.singleton_apply, QRegister.block_apply_val,
          mMidUB] at hv ⊢
        omega)
theorem actInMX_disjoint_xo7 (wInner2 : ℕ) : (actInMX wInner2).DisjointWires (xo7InMX wInner2) :=
  disjointWires_concat_left _ (midInMX_disjoint_xo7 wInner2)
    (by rw [QRegister.disjoint_iff]
        intro i j hij
        fin_cases i
        have hv := congrArg Fin.val hij
        have := j.isLt
        simp only [xo7InMX, xo8InMX, QRegister.compose_apply, QRegister.singleton_apply,
          QRegister.block_apply_val] at hv
        omega)
theorem spinAct_disj (wInner2 : ℕ) :
    (QRegister.singleton (⟨mMidUB wInner2, by omega⟩ : Wire (mMidUB wInner2 + 1))).DisjointWires
      ((QRegister.block 0 (mMidUB wInner2) (by omega)).compose (rSigInLoc wInner2)) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  fin_cases i
  have hv := congrArg Fin.val hij
  have hs := (rSigInLoc wInner2 j).isLt
  simp only [QRegister.singleton_apply, QRegister.compose_apply, QRegister.block_apply_val,
    mMidUB] at hv hs
  omega
/-- `(mMidUB wInner2 + 1)`-wire controlled-`H` branch on `rSigInLoc wInner2` by `b7 ⊕ h126 ⊕ h127`.
-/
noncomputable def spinAct (wInner2 : ℕ) (h126 h127 : Bool) : Unitary (2 ^ (mMidUB wInner2 + 1)) :=
  muxUnitary (QRegister.singleton ⟨mMidUB wInner2, by omega⟩)
    ((QRegister.block 0 (mMidUB wInner2) (by omega)).compose (rSigInLoc wInner2))
    (spinAct_disj wInner2)
    (fun b7 ↦ if (if bitsOfFin 1 b7 0 then (1 : ZMod 2) else 0) +
      (if h127 then 1 else 0) + (if h126 then 1 else 0) = 1 then (Circuit.H 0).eval else 1)
/-- `2-T`, `0-TOFF` pure `Circuit` for `s_i = 0` spin cancellation inside `withHot128Dyn`. -/
def mainHotSpinCircuit {N wInner2 sScr : ℕ} (rMX : QRegister (mMidUB wInner2 + 8) N)
    (rScr : QRegister sScr N) (hs : 128 ≤ sScr) (hDisj : rMX.DisjointWires rScr) : Circuit N :=
  cHXoMain (rMX (xo8InMX wInner2 ⟨7, by decide⟩)) (rScr ⟨126, by omega⟩) (rScr ⟨127, by omega⟩)
    (rMX (midInMX wInner2 (rSigInLoc wInner2 ⟨0, by decide⟩)))
    (hDisj.ne _ _).symm (hDisj.ne _ _).symm
    (rMX.wires.injective.ne ((xo8InMX_disjoint_sig wInner2).ne ⟨7, by decide⟩ ⟨0, by decide⟩))
@[simp]
theorem countMainHotSpinCircuit_toff {N wInner2 sScr : ℕ} (rMX : QRegister (mMidUB wInner2 + 8) N)
    (rScr : QRegister sScr N) (hs : 128 ≤ sScr) (hDisj : rMX.DisjointWires rScr) :
    (mainHotSpinCircuit rMX rScr hs hDisj).count .TOFF = 0 := by simp [mainHotSpinCircuit]
@[simp]
theorem countMainHotSpinCircuit_t {N wInner2 sScr : ℕ} (rMX : QRegister (mMidUB wInner2 + 8) N)
    (rScr : QRegister sScr N) (hs : 128 ≤ sScr) (hDisj : rMX.DisjointWires rScr) :
    (mainHotSpinCircuit rMX rScr hs hDisj).count .T = 2 := by simp [mainHotSpinCircuit]
theorem mainHotSpinCircuit_mul_self {N wInner2 sScr : ℕ} (rMX : QRegister (mMidUB wInner2 + 8) N)
    (rScr : QRegister sScr N) (hs : 128 ≤ sScr) (hDisj : rMX.DisjointWires rScr) :
    (mainHotSpinCircuit rMX rScr hs hDisj).eval *
      (mainHotSpinCircuit rMX rScr hs hDisj).eval = 1 := by
  apply Subtype.ext
  apply SelectSwapQROM.matrix_ext_ket
  intro β
  let w0 := rMX (xo8InMX wInner2 ⟨7, by decide⟩)
  let w1 := rScr ⟨126, by omega⟩
  let w2 := rScr ⟨127, by omega⟩
  let wSig := rMX (midInMX wInner2 (rSigInLoc wInner2 ⟨0, by decide⟩))
  have h10 : w1 ≠ w0 := (hDisj.ne _ _).symm
  have h20 : w2 ≠ w0 := (hDisj.ne _ _).symm
  have h0s : w0 ≠ wSig :=
    rMX.wires.injective.ne ((xo8InMX_disjoint_sig wInner2).ne ⟨7, by decide⟩ ⟨0, by decide⟩)
  have h1s : w1 ≠ wSig := (hDisj.ne _ _).symm
  have h2s : w2 ≠ wSig := (hDisj.ne _ _).symm
  have h21 : w2 ≠ w1 := rScr.wires.injective.ne (by
    intro h
    have := congrArg Fin.val h
    dsimp at this
    omega)
  have hApp (γ : BitAssignment N) :
      (mainHotSpinCircuit rMX rScr hs hDisj).eval.1.mulVec (SelectSwapQROM.ket γ) =
        if γ w0 + γ w2 + γ w1 = 1 then (Circuit.H wSig).eval.1.mulVec (SelectSwapQROM.ket γ)
        else SelectSwapQROM.ket γ :=
    ketCHXoMain w0 w1 w2 wSig h10 h20 h0s h1s h2s h21 γ
  rw [coe_mul, OneMemClass.coe_one, Matrix.one_mulVec, ← mulVec_mulVec, hApp β]
  by_cases hp : β w0 + β w2 + β w1 = 1
  · rw [ite_eq_left hp, SelectSwapQROM.ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
      Matrix.mulVec_smul, hApp, hApp]
    simp only [update_of_ne h0s, update_of_ne h2s, update_of_ne h1s, hp, ↓reduceIte]
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← Matrix.mulVec_smul, ← SelectSwapQROM.ket_H,
      mulVec_mulVec, ← coe_mul, circuitH_mul_self wSig, OneMemClass.coe_one, Matrix.one_mulVec]
  · rw [ite_eq_right hp, hApp β, ite_eq_right hp]
theorem xo8InMX_disjoint_mid (wInner2 : ℕ) : (xo8InMX wInner2).DisjointWires (midInMX wInner2) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  have := j.isLt
  simp only [xo8InMX, midInMX, QRegister.block_apply_val] at hv
  omega
theorem embed_reflMidUnitary_congr {N k₁ k₂ m : ℕ} (r₁ : QRegister k₁ N) (s₁ : QRegister m k₁)
    (r₂ : QRegister k₂ N) (s₂ : QRegister m k₂) (h : r₁.compose s₁ = r₂.compose s₂) :
    r₁.embedUnitary (QubitisedWalk.reflMidUnitary s₁) =
      r₂.embedUnitary (QubitisedWalk.reflMidUnitary s₂) := by
  have he {k} (r : QRegister k N) (s : QRegister m k) :
      (r.embedUnitary (QubitisedWalk.reflMidUnitary s)).1 =
        1 - (2 : ℂ) • SelectSwapQROM.zeroProjOn (r.compose s).image := by
    change r.embedMatrix (1 - (2 : ℂ) • s.basisOutcomeProjector 0) = _
    rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_one, QRegister.embedMatrix_smul,
      ← CleanDyn.compose_basisOutcomeProjector,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn]
  apply Subtype.ext
  rw [he, he, h]
theorem embed_reflMidUnitary_inMidWalkCat_eq {N bCat wOuter wInner2 : ℕ}
    (rMain : QRegister (nUB wOuter wInner2 + bCat) N) :
    (rMain.compose (rUBInCat wOuter wInner2 bCat)).embedUnitary
      (QubitisedWalk.reflMidUnitary (rMidUB wOuter wInner2)) =
    rMain.embedUnitary (QubitisedWalk.reflMidUnitary (inMidWalkCat bCat (mOutUB wOuter) (mMidUB
      wInner2))) :=
  embed_reflMidUnitary_congr _ _ _ _ (CoherentAlias.qreg_ext fun i ↦ by
    simp [rUBInCat, rMidUB, inMidWalkCat, rWalkInWalkCat, rMidInWalk, systemQubits_local])
theorem mainHotSpinCircuit_eval_eqHotMux135 {N wInner2 sScr : ℕ}
    (rMX : QRegister (mMidUB wInner2 + 8) N) (rScr : QRegister sScr N) (hScr : 129 ≤ sScr)
    (hDisj : rMX.DisjointWires rScr) :
    let rAct := rMX.compose (actInMX wInner2)
    let rCtx := rMX.compose (xo7InMX wInner2)
    let L := stepScrLayout rCtx rScr hScr (hDisj.compose_left _)
    have hAC : rAct.DisjointWires L.rCtx := compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 wInner2)
    have hAH : rAct.DisjointWires L.rHot := (hDisj.compose_left _).compose_right _
    (mainHotSpinCircuit rMX rScr (by omega) hDisj).eval = hotMux135 L rAct hAC hAH (fun z ↦
      spinAct wInner2 (z (Fin.natAdd 7 ⟨126, by decide⟩)) (z (Fin.natAdd 7 ⟨127, by decide⟩))) := by
  intro rAct rCtx L hAC hAH
  let w0 := rMX (xo8InMX wInner2 ⟨7, by decide⟩)
  let w1 := rScr ⟨126, by omega⟩
  let w2 := rScr ⟨127, by omega⟩
  let wSig := rMX (midInMX wInner2 (rSigInLoc wInner2 ⟨0, by decide⟩))
  have h0s : w0 ≠ wSig :=
    rMX.wires.injective.ne ((xo8InMX_disjoint_sig wInner2).ne ⟨7, by decide⟩ ⟨0, by decide⟩)
  have h21 : w2 ≠ w1 := rScr.wires.injective.ne (by
    intro h
    have := congrArg Fin.val h
    dsimp at this
    omega)
  let rP2 := QRegister.pair w1 w2 h21.symm
  have hActP : rAct.DisjointWires rP2 := by
    rw [QRegister.disjoint_iff]
    intro a b
    fin_cases b
    · exact (hDisj.compose_left _).ne a ⟨126, by omega⟩
    · exact (hDisj.compose_left _).ne a ⟨127, by omega⟩
  let c0 : Fin (7 + 128) := Fin.natAdd 7 ⟨126, by decide⟩
  let c1 : Fin (7 + 128) := Fin.natAdd 7 ⟨127, by decide⟩
  let out2 : QRegister 2 (7 + 128) := QRegister.pair c0 c1
    (by
        intro h
        have := congrArg Fin.val h
        dsimp [c0, c1] at this
        omega)
  let G2 (u : Fin 2 → Bool) : Unitary (2 ^ (mMidUB wInner2 + 1)) := spinAct wInner2 (u 0) (u 1)
  have hMuxRed : hotMux135 L rAct hAC hAH (fun z ↦ spinAct wInner2 (z c0) (z c1)) =
      muxUnitary rP2 rAct (QRegister.disjoint_comm.mp hActP) (fun c2 ↦ G2 (bitsOfFin 2 c2)) := by
    dsimp only [hotMux135]
    have hFn : (fun z : Fin (7 + 128) → Bool ↦ spinAct wInner2 (z c0) (z c1)) =
        fun z ↦ G2 (fun j ↦ z (out2 j)) := rfl
    rw [hFn, ← subActPullback_embedUnitary_muxOnAct out2 G2, ← QRegister.embedUnitary_compose,
      ← embedUnitary_muxOnAct rAct rP2 hActP]
    refine congrArg (QRegister.embedUnitary · _) (CoherentAlias.qreg_ext fun i ↦ ?_)
    obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
    · change (((rAct.concat _ _).compose _) (Fin.castAdd 2 a)).val =
          ((rAct.concat rP2 hActP) (Fin.castAdd 2 a)).val
      dsimp only [subActPullback, QRegister.compose_apply]
      rw [concat_apply_left, concat_apply_left]
      have ha : (QRegister.block 0 (mMidUB wInner2 + 1) (by omega)) a =
          Fin.castAdd (7 + 128) a := Fin.ext (by simp)
      rw [ha, concat_apply_left]
    · change (((rAct.concat _ _).compose _) (Fin.natAdd (mMidUB wInner2 + 1) b)).val =
          ((rAct.concat rP2 hActP) (Fin.natAdd (mMidUB wInner2 + 1) b)).val
      dsimp only [subActPullback, QRegister.compose_apply]
      rw [concat_apply_right, concat_apply_right]
      have hb01 : b = 0 ∨ b = 1 := by
        rcases b with ⟨_ | _ | _, _⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · omega
      rcases hb01 with rfl | rfl
      · have hb0 : ((QRegister.block (mMidUB wInner2 + 1) (7 + 128) (by omega)).compose out2) 0 =
            Fin.natAdd (mMidUB wInner2 + 1) c0 := Fin.ext (by
          simp [out2, c0, QRegister.pair])
        rw [hb0, concat_apply_right]
        dsimp only [c0]
        rw [concat_apply_right]
        exact congrArg Fin.val ((slice_apply ..).trans (congrArg rScr (Fin.ext (Nat.zero_add 126))))
      · have hb1 : ((QRegister.block (mMidUB wInner2 + 1) (7 + 128) (by omega)).compose out2) 1 =
            Fin.natAdd (mMidUB wInner2 + 1) c1 := Fin.ext (by
          simp [out2, c1, QRegister.pair])
        rw [hb1, concat_apply_right]
        dsimp only [c1]
        rw [concat_apply_right]
        exact congrArg Fin.val ((slice_apply ..).trans (congrArg rScr (Fin.ext (Nat.zero_add 127))))
  rw [hMuxRed]
  apply Subtype.ext
  apply SelectSwapQROM.matrix_ext_ket
  intro β
  let k := (basisBits N).symm β
  have hk (w : Wire N) : basisBits N k w = β w := congrFun (CoherentAlias.basisBits_symm_apply β) w
  have hpk {m : ℕ} (r : QRegister m N) (q : Fin (2 ^ N)) (hq : r.extractIndex q ≠ r.extractIndex k)
      : SelectSwapQROM.ket β q = 0 := by
    change basisState k q = 0
    rw [basisState, Pi.single_eq_of_ne]
    rintro rfl
    exact hq rfl
  rw [mainHotSpinCircuit, ketCHXoMain w0 w1 w2 wSig (hDisj.ne _ _).symm (hDisj.ne _ _).symm
    h0s (hDisj.ne _ _).symm (hDisj.ne _ _).symm h21 β,
    muxUnitary_mulVec_of_proj rP2 rAct _ _ (rP2.extractIndex k) _ (hpk rP2),
    ← QRegister.embedUnitary_val]
  dsimp only [G2]
  rw [spinAct, embedUnitary_muxUnitary]
  let rB7 := QRegister.singleton w0
  have ha1 : rAct.compose (QRegister.singleton ⟨mMidUB wInner2, by omega⟩) = rB7 :=
    (QRegister.compose_assoc _ _ _).trans ((congrArg (rMX.compose ·)
      (concat_singleton_right _ _ _)).trans (CoherentAlias.qreg_ext fun i ↦ by
        fin_cases i
        rfl))
  have ha2 : rAct.compose ((QRegister.block 0 (mMidUB wInner2) (by omega)).compose (rSigInLoc
      wInner2)) =
      QRegister.singleton wSig := (QRegister.compose_assoc _ _ _).symm.trans ((congrArg
      (fun r : QRegister (mMidUB wInner2) N ↦ r.compose (rSigInLoc wInner2))
      ((QRegister.compose_assoc _ _ _).trans (congrArg (rMX.compose ·)
      (concat_compose_block_left _ _ _ _)))).trans
      (CoherentAlias.qreg_ext fun i ↦ by
          fin_cases i
          rfl))
  have hdB7 : rB7.DisjointWires (QRegister.singleton wSig) := by
    rw [QRegister.disjoint_iff]
    intro i j
    fin_cases i
    fin_cases j
    exact h0s
  rw [muxCongr ha1 ha2 _ hdB7 (fun _ ↦ rfl),
    muxUnitary_mulVec_of_proj rB7 (QRegister.singleton wSig) _ _ (rB7.extractIndex k) _ (hpk rB7)]
  have hbZ {m : ℕ} (r : QRegister m N) (j : Fin m) :
      (if bitsOfFin m (r.extractIndex k) j then (1 : ZMod 2) else 0) = β (r j) := by
    rw [bitsOfFin, QRegister.basisBits_extractIndex, hk]
    rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β (r j)) with h | h <;> simp [h]
  rw [hbZ rB7 0, hbZ rP2 1, hbZ rP2 0, show rB7 0 = w0 from rfl, show rP2 1 = w2 from rfl,
    show rP2 0 = w1 from rfl]
  have hHeq : (QRegister.singleton wSig).embedUnitary (Circuit.H 0).eval = (Circuit.H wSig).eval :=
    (Circuit.eval_onRegister (QRegister.singleton wSig) (Circuit.H 0)).symm.trans
      (congrArg Circuit.eval (congrArg (Circuit.gate PrimitiveGate.H)
        (CoherentAlias.qreg_ext fun i ↦ by
            fin_cases i
            rfl)))
  by_cases hp : β w0 + β w2 + β w1 = 1
  · rw [ite_eq_left hp, ite_eq_left hp, ← QRegister.embedUnitary_val, hHeq]
  · rw [ite_eq_right hp, ite_eq_right hp, OneMemClass.coe_one, QRegister.embedMatrix_one,
      Matrix.one_mulVec]
theorem cleanPredRealizesMainHotSpinCircuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {N wInner2 sScr : ℕ} (v : Var) (rMX : QRegister (mMidUB wInner2 + 8) N)
    (rScr : QRegister sScr N)
    (hScr : 129 ≤ sScr) (hDisj : rMX.DisjointWires rScr) :
    let rXo7 := rMX.compose (xo7InMX wInner2)
    let rHot := rScr.slice 0 128 (by omega)
    let rTail := rScr.slice 128 (sScr - 128) (by omega)
    CleanPredRealizes v (Mobius126OneHot.cleanPredProj rTail.image (xoOneHotPred rXo7 rHot))
      (mainHotSpinCircuit rMX rScr (by omega) hDisj).eval
      (.circuit (mainHotSpinCircuit rMX rScr (by omega) hDisj)) := by
  intro rXo7 rHot rTail
  let rAct := rMX.compose (actInMX wInner2)
  let L := stepScrLayout rXo7 rScr hScr (hDisj.compose_left _)
  have hAC : rAct.DisjointWires L.rCtx := compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 wInner2)
  have hAH : rAct.DisjointWires L.rHot := (hDisj.compose_left _).compose_right _
  let rCH := L.rCtx.concat L.rHot L.hCtxHot
  have hActTail : rAct.DisjointWires rTail := (hDisj.compose_left _).compose_right _
  have hMuxEq : (mainHotSpinCircuit rMX rScr (by omega) hDisj).eval = muxUnitary rCH rAct
      (disjointWires_concat_right L.hCtxHot hAC hAH).symm (fun c ↦ spinAct wInner2
      (bitsOfFin (7 + 128) c (Fin.natAdd 7 ⟨126, by decide⟩))
      (bitsOfFin (7 + 128) c (Fin.natAdd 7 ⟨127, by decide⟩))) := by
    rw [mainHotSpinCircuit_eval_eqHotMux135 rMX rScr hScr hDisj]
    dsimp only [hotMux135]
    rw [embedUnitary_muxOnAct]
  have hPresT : PreservesWires (mainHotSpinCircuit rMX rScr (by omega) hDisj).eval.1 rTail.image :=
    by
      rw [hMuxEq]
      exact preservesWires_muxUnitary rCH rAct _ _ _
        (SelectSwapQROM.disjoint_image_of_disjointWires hActTail)
  have hPresXH : PreservesWires (mainHotSpinCircuit rMX rScr (by omega) hDisj).eval.1
      (rXo7.image ∪ rHot.image) := by
    rw [hMuxEq, show rXo7.image ∪ rHot.image = rCH.image from
      (QRegister.image_concat L.rCtx L.rHot L.hCtxHot).symm]
    exact preservesWires_muxUnitary rCH rAct _ _ _
      (SelectSwapQROM.disjoint_image_of_disjointWires
        (disjointWires_concat_right L.hCtxHot hAC hAH))
  have hQSplit : Mobius126OneHot.cleanPredProj rTail.image (xoOneHotPred rXo7 rHot) =
      SelectSwapQROM.zeroProjOn rTail.image * predProj (xoOneHotPred rXo7 rHot) := rfl
  refine ⟨countMainHotSpinCircuit_toff rMX rScr (by omega) hDisj, ?_,
    fun Θ hΘ σ val ↦ by simp [compile_circuit, qcWpQAssign, hΘ σ val],
    fun Θ _ σ ↦ by rw [compile_circuit, qc_wp_circuit_compile]⟩
  rw [conjTranspose_eq_self_of_mul_self _ (mainHotSpinCircuit_mul_self rMX rScr (by omega) hDisj),
    hQSplit, Matrix.mul_assoc, ← preservesWires_comm_predProj_xoOneHot hPresXH, ← Matrix.mul_assoc,
    ← preservesWires_comm_zeroProjOn hPresT Finset.Subset.rfl, Matrix.mul_assoc]
theorem ctxMux7SpinAct_eq {N wInner2 sScr : ℕ} (rMX : QRegister (mMidUB wInner2 + 8) N)
    (rScr : QRegister sScr N) (hScr : 129 ≤ sScr) (hDisj : rMX.DisjointWires rScr) :
    let rAct := rMX.compose (actInMX wInner2)
    let rCtx := rMX.compose (xo7InMX wInner2)
    let L := stepScrLayout rCtx rScr hScr (hDisj.compose_left _)
    have hAC : rAct.DisjointWires L.rCtx := compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 wInner2)
    ctxMux7 L rAct hAC (fun z ↦ spinAct wInner2
      (z (Fin.natAdd 7 ⟨126, by decide⟩)) (z (Fin.natAdd 7 ⟨127, by decide⟩))) =
      rMX.embedUnitary (spinCancelMXMux wInner2) := by
  intro rAct rCtx L hAC
  apply Subtype.ext
  apply SelectSwapQROM.matrix_ext_ket
  intro β
  let k := (basisBits N).symm β
  have hk (w : Wire N) : basisBits N k w = β w := congrFun (CoherentAlias.basisBits_symm_apply β) w
  have hpk {m : ℕ} (r : QRegister m N) (q : Fin (2 ^ N)) (hq : r.extractIndex q ≠ r.extractIndex k)
      : SelectSwapQROM.ket β q = 0 := by
    change basisState k q = 0
    rw [basisState, Pi.single_eq_of_ne]
    rintro rfl
    exact hq rfl
  dsimp only [ctxMux7]
  rw [embedUnitary_muxOnAct, spinCancelMXMux, embedUnitary_muxUnitary]
  let rXo8 := rMX.compose (xo8InMX wInner2)
  let w0 := rMX (xo8InMX wInner2 ⟨7, by decide⟩)
  let wSig := rMX (midInMX wInner2 (rSigInLoc wInner2 ⟨0, by decide⟩))
  have h0s : w0 ≠ wSig :=
    rMX.wires.injective.ne ((xo8InMX_disjoint_sig wInner2).ne ⟨7, by decide⟩ ⟨0, by decide⟩)
  rw [muxUnitary_mulVec_of_proj L.rCtx rAct _ _ (L.rCtx.extractIndex k) _ (hpk L.rCtx),
    muxUnitary_mulVec_of_proj rXo8 _ _ _ (rXo8.extractIndex k) _ (hpk rXo8),
    ← QRegister.embedUnitary_val, spinAct, embedUnitary_muxUnitary]
  let rB7 := QRegister.singleton w0
  have ha1 : rAct.compose (QRegister.singleton ⟨mMidUB wInner2, by omega⟩) = rB7 :=
    (QRegister.compose_assoc _ _ _).trans ((congrArg (rMX.compose ·)
      (concat_singleton_right _ _ _)).trans (CoherentAlias.qreg_ext fun i ↦ by
        fin_cases i
        rfl))
  have ha2 : rAct.compose ((QRegister.block 0 (mMidUB wInner2) (by omega)).compose (rSigInLoc
      wInner2)) =
      QRegister.singleton wSig := (QRegister.compose_assoc _ _ _).symm.trans ((congrArg
      (fun r : QRegister (mMidUB wInner2) N ↦ r.compose (rSigInLoc wInner2))
      ((QRegister.compose_assoc _ _ _).trans (congrArg (rMX.compose ·)
      (concat_compose_block_left _ _ _ _)))).trans
      (CoherentAlias.qreg_ext fun i ↦ by
          fin_cases i
          rfl))
  have hdB7 : rB7.DisjointWires (QRegister.singleton wSig) := by
    rw [QRegister.disjoint_iff]
    intro i j
    fin_cases i
    fin_cases j
    exact h0s
  rw [muxCongr ha1 ha2 _ hdB7 (fun _ ↦ rfl),
    muxUnitary_mulVec_of_proj rB7 (QRegister.singleton wSig) _ _ (rB7.extractIndex k) _ (hpk rB7)]
  have hSigEq : rMX.compose ((midInMX wInner2).compose (rSigInLoc wInner2)) =
      QRegister.singleton wSig :=
    CoherentAlias.qreg_ext fun i ↦ by
      fin_cases i
      rfl
  rw [hSigEq]
  let xo := rXo8.extractIndex k
  have hx7 : L.rCtx.extractIndex k = (QRegister.block 0 7 (by decide)).extractIndex xo := by
    apply (basisBits 7).injective
    funext i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      QRegister.basisBits_extractIndex]
    rfl
  have hHot (g : Fin 128) :
      (if stepOneHotCtrlBits (bitsOfFin 7 (L.rCtx.extractIndex k)) (Fin.natAdd 7 g)
        then (1 : ZMod 2) else 0) =
      if (QRegister.block 0 7 (by decide)).extractIndex xo = g then 1 else 0 := by
    dsimp only [stepOneHotCtrlBits]
    have hn : ¬ ((Fin.natAdd 7 g).val < 7) ∧ (Fin.natAdd 7 g).val - 7 = g.val := by
      dsimp
      omega
    simp only [hn.1, ↓reduceDIte, hn.2, finOfBits_bitsOfFin, hx7, Fin.ext_iff]
    by_cases he : g.val = ((QRegister.block 0 7 (by decide)).extractIndex xo).val <;>
      simp [he, eq_comm]
  have hb7 : (if bitsOfFin 1 (rB7.extractIndex k) 0 then (1 : ZMod 2) else 0) =
      basisBits 8 xo ⟨7, by decide⟩ := by
    dsimp only [xo]
    rw [bitsOfFin, QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hk, hk]
    have hSing : rB7 0 = rXo8 ⟨7, by decide⟩ := by simp [rB7, rXo8, w0]
    rw [hSing]
    rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one (β (rXo8 ⟨7, by decide⟩)) with h0 | h1
    · rw [h0]
      rfl
    · rw [h1]
      rfl
  rw [hb7, hHot ⟨127, by decide⟩, hHot ⟨126, by decide⟩, is1BBool_eq_hotZMod xo]
  have hComm : basisBits 8 xo ⟨7, by decide⟩ +
      (if (QRegister.block 0 7 (by decide)).extractIndex xo = ⟨127, by decide⟩ then 1 else 0) +
      (if (QRegister.block 0 7 (by decide)).extractIndex xo = ⟨126, by decide⟩ then 1 else 0) =
    basisBits 8 xo ⟨7, by decide⟩ +
      (if (QRegister.block 0 7 (by decide)).extractIndex xo = ⟨126, by decide⟩ then 1 else 0) +
      (if (QRegister.block 0 7 (by decide)).extractIndex xo = ⟨127, by decide⟩ then 1 else 0) := by
    ring
  rw [hComm]
  simp
/-- `9`-wire `(sig ++ xo[0..7])` active subregister inside `mMidUB wInner2 + 8` for `TempProg` spin.
-/
def spin9InMX (wInner2 : ℕ) : QRegister (1 + 8) (mMidUB wInner2 + 8) :=
  ((midInMX wInner2).compose (rSigInLoc wInner2)).concat (xo8InMX wInner2)
  (xo8InMX_disjoint_sig wInner2).symm
/-- `5`-AND + `1`-linear `RawOp` program computing `b₇ ⊕ (b₁ ∧ b₂ ∧ b₃ ∧ b₄ ∧ b₅ ∧ b₆)` (`20 T`). -/
def spinRawOps : List RawOp :=
  [.andGate 1 2, .andGate 8 3, .andGate 9 4, .andGate 10 5, .andGate 11 6, .linear [7, 12] false]
/-- Compiled `TempProg 8 14 6` for `spinRawOps` (`5` ANDs = `20 T`, `6` temporary wires). -/
def spinSteps : TempProg 8 14 6 := compileRawOps 8 spinRawOps
@[simp] theorem spinSteps_numAnds : spinSteps.numAnds = 5 :=
  (numAnds_compileRawOps spinRawOps 8).trans (by decide)
/-- `2-T`, `0-TOFF` middle `ctrlH` callback on `(1 + 14)` wires (`y 13 → H(0)`). -/
def spinCtrlHMidFn {Var : Type} {N : ℕ} (rF : QRegister (1 + 14) N) : DynamicCircuit Var N :=
  .circuit (CoherentAlias.ctrlH.onRegister
    (QRegister.pair (rF ⟨14, by decide⟩) (rF ⟨0, by decide⟩)
      (rF.wires.injective.ne (by decide))))
/-- `22-T` (`5 × 4 + 2`), `0-TOFF`, `6`-scratch cold spin-cancellation dynamic circuit. -/
def mainSpinCancel22Dyn {Var : Type} {N wInner2 sScr : ℕ} (v : Var)
    (rMX : QRegister (mMidUB wInner2 + 8) N) (rScr : QRegister sScr N) (hs : 6 ≤ sScr) :
    DynamicCircuit Var N :=
  spinSteps.wrapDyn v 1 (rMX.compose (spin9InMX wInner2))
    (rScr.compose (QRegister.block 0 6 hs)) spinCtrlHMidFn
@[simp] theorem countMainSpinCancel22Dyn_toff {Var : Type} {N wInner2 sScr : ℕ} (v : Var)
    (rMX : QRegister (mMidUB wInner2 + 8) N) (rScr : QRegister sScr N) (hs : 6 ≤ sScr) :
    (mainSpinCancel22Dyn v rMX rScr hs).count .TOFF = 0 :=
  spinSteps.wrapDyn_count_toff v 1 _ _ spinCtrlHMidFn fun _ ↦ by
    simp [spinCtrlHMidFn, Circuit.count_onRegister]
@[simp] theorem countMainSpinCancel22Dyn_t {Var : Type} {N wInner2 sScr : ℕ} (v : Var)
    (rMX : QRegister (mMidUB wInner2 + 8) N) (rScr : QRegister sScr N) (hs : 6 ≤ sScr)
    (hDisj : rMX.DisjointWires rScr) :
    (mainSpinCancel22Dyn v rMX rScr hs).count .T = 22 := by
  let rAct := rMX.compose (spin9InMX wInner2)
  let rTemp := rScr.compose (QRegister.block 0 6 hs)
  let rEmpty : QRegister 0 N := QRegister.block 0 0 (Nat.zero_le N)
  have hAT : rAct.DisjointWires rTemp := (hDisj.compose_left _).compose_right _
  have hAE : rAct.DisjointWires rEmpty := QRegister.disjoint_iff.mpr fun _ j ↦ Fin.elim0 j
  have hTE : rTemp.DisjointWires rEmpty := QRegister.disjoint_iff.mpr fun _ j ↦ Fin.elim0 j
  rw [mainSpinCancel22Dyn, spinSteps.wrapDyn_count_t v 1 rAct rTemp rEmpty hAT hAE hTE
    spinCtrlHMidFn 2 (fun _ _ ↦ by simp [spinCtrlHMidFn, Circuit.count_onRegister]),
    spinSteps_numAnds]
theorem spinCtrlH_eval_eq :
    (CoherentAlias.ctrlH.onRegister
      (QRegister.pair (⟨14, by decide⟩ : Wire (1 + 14)) ⟨0, by decide⟩ (by decide))).eval =
      muxOnAct 1 14 (fun y ↦ if y ⟨13, by decide⟩ then (Circuit.H 0).eval else 1) := by
  apply Subtype.ext
  apply SelectSwapQROM.matrix_ext_ket
  intro β
  let k := (basisBits (1 + 14)).symm β
  rw [ket_ctrlH_pair]
  dsimp only [muxOnAct]
  rw [muxUnitary_mulVec_of_proj (QRegister.block 1 14 (by omega)) (QRegister.block 0 1 (by omega))
    _ _ ((QRegister.block 1 14 (by omega)).extractIndex k) _ (fun q hq ↦ by
      change basisState k q = 0
      rw [basisState, Pi.single_eq_of_ne]
      rintro rfl
      exact hq rfl)]
  have hb : bitsOfFin 14 ((QRegister.block 1 14 (by omega)).extractIndex k) ⟨13, by decide⟩ =
      decide (β ⟨14, by decide⟩ = 1) := by
    dsimp only [bitsOfFin, k]
    rw [QRegister.basisBits_extractIndex, CoherentAlias.basisBits_symm_apply]
    rfl
  have hB0 : QRegister.block 0 1 (by omega) = QRegister.singleton (0 : Wire (1 + 14)) :=
    CoherentAlias.qreg_ext fun i ↦ by
      fin_cases i
      rfl
  have hH0 : (QRegister.singleton (0 : Wire (1 + 14))).embedUnitary (Circuit.H 0).eval =
      (Circuit.H (⟨0, by decide⟩ : Wire (1 + 14))).eval :=
    (Circuit.eval_onRegister (QRegister.singleton (0 : Wire (1 + 14))) (Circuit.H 0)).symm.trans
      (congrArg Circuit.eval (congrArg (Circuit.gate PrimitiveGate.H)
        (CoherentAlias.qreg_ext fun i ↦ by
            fin_cases i
            rfl)))
  rw [hb, hB0]
  by_cases h14 : β ⟨14, by decide⟩ = 1
  · rw [decide_eq_true h14, ite_eq_left rfl, ite_eq_left h14, ← QRegister.embedUnitary_val, hH0]
  · rw [decide_eq_false h14, ite_eq_right Bool.false_ne_true, ite_eq_right h14, OneMemClass.coe_one,
      QRegister.embedMatrix_one, Matrix.one_mulVec]
theorem cleanRealizesSpinCtrlHMidFn {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (v : Var) (rF : QRegister (1 + 14) N) (rE : QRegister 0 N) (h : rF.DisjointWires rE) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v rF rE
      (muxOnAct 1 14 (fun y ↦ if y ⟨13, by decide⟩ then (Circuit.H 0).eval else 1))
      (spinCtrlHMidFn rF) := by
  let cLoc := CoherentAlias.ctrlH.onRegister
    (QRegister.pair (⟨14, by decide⟩ : Wire (1 + 14)) ⟨0, by decide⟩ (by decide))
  have hProg : spinCtrlHMidFn (Var := Var) rF = .circuit (cLoc.onRegister rF) := by
    unfold spinCtrlHMidFn
    congr 1
    rw [Circuit.onRegister_compose]
    exact congrArg (CoherentAlias.ctrlH.onRegister ·)
      (CoherentAlias.qreg_ext fun i ↦ by fin_cases i <;> rfl)
  rw [hProg, ← spinCtrlH_eval_eq]
  exact CleanDyn.CleanRealizes.circuit v rF rE h cLoc
    (by simp [cLoc, Circuit.count_onRegister])
theorem cleanRealizesMainSpinCancel22Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N wInner2 sScr : ℕ} (v : Var) (rMX : QRegister (mMidUB wInner2 + 8) N)
    (rScr : QRegister sScr N)
    (hs : 6 ≤ sScr) (hDisj : rMX.DisjointWires rScr) :
    CleanDyn.CleanRealizes v rMX rScr (spinCancelMXMux wInner2)
      (mainSpinCancel22Dyn v rMX rScr hs) := by
  let rAct := rMX.compose (spin9InMX wInner2)
  let rTemp := rScr.compose (QRegister.block 0 6 hs)
  let rEmpty : QRegister 0 N := QRegister.block 0 0 (Nat.zero_le N)
  have hAT : rAct.DisjointWires rTemp := (hDisj.compose_left _).compose_right _
  have hAE : rAct.DisjointWires rEmpty := QRegister.disjoint_iff.mpr fun _ j ↦ Fin.elim0 j
  have hTE : rTemp.DisjointWires rEmpty := QRegister.disjoint_iff.mpr fun _ j ↦ Fin.elim0 j
  have hraw := spinSteps.cleanRealizes_mux v rAct rTemp rEmpty hAT hAE hTE
    (fun y ↦ if y ⟨13, by decide⟩ then (Circuit.H 0).eval else 1) spinCtrlHMidFn
    (fun rF hF ↦ cleanRealizesSpinCtrlHMidFn v rF rEmpty hF)
  have hFast : ∀ n < 2 ^ 8, evalRawRevFast 8 spinRawOps (bitsRevFast 8 n []) (fun rev ↦ boolEq
      (bget rev (rawOutLen 8 spinRawOps - 1 -
        (⟨13, by decide⟩ : Fin (rawOutLen 8 spinRawOps)).val))
      (Nat.blt 125 n && Nat.blt n 254)) = true := allPow2_zero_true rfl
  have hb (c : Fin (2 ^ 8)) :
      (compileRawOps 8 spinRawOps).evalBits (bitsOfFin 8 c) ⟨13, by decide⟩ = is1BBool2 c := by
    have hc := check_compileRawOps_of_fast 8 spinRawOps c
      (fun out ↦ boolEq (out ⟨13, by decide⟩) (Nat.blt 125 c.val && Nat.blt c.val 254))
      (hFast c.val c.isLt)
    have hblt : (Nat.blt 125 c.val && Nat.blt c.val 254) = is1BBool2 c := by
      rw [is1BBool2, Bool.eq_iff_iff, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, decide_eq_true_eq]
      omega
    rw [hblt] at hc
    revert hc
    cases (compileRawOps 8 spinRawOps).evalBits (bitsOfFin 8 c) ⟨13, by decide⟩ <;>
      cases is1BBool2 c <;> decide
  have hEv (x : Fin 8 → Bool) :
      spinSteps.evalBits x ⟨13, by decide⟩ = is1BBool2 (finOfBits 8 x) := by
    dsimp only [spinSteps]
    conv_lhs => rw [← bitsOfFin_finOfBits 8 x]
    exact hb (finOfBits 8 x)
  simp_rw [hEv] at hraw
  have hExt : CleanDyn.CleanRealizes v rAct rScr _ (mainSpinCancel22Dyn v rMX rScr hs) :=
    hraw.extend_scr (hDisj.compose_left _) (by
      rw [QRegister.image_concat]
      refine Finset.union_subset (rScr.image_compose_subset _) ?_
      intro _ hw
      obtain ⟨j, _⟩ := (QRegister.mem_image rEmpty _).mp hw
      exact Fin.elim0 j)
  have hComp := cr_of_compose hExt
  have hMux : (spin9InMX wInner2).embedUnitary
      (muxOnAct 1 8 (fun x ↦ if is1BBool2 (finOfBits 8 x) then (Circuit.H 0).eval else 1)) =
      spinCancelMXMux wInner2 := by
    rw [muxOnAct_finOfBits_eq_muxUnitary (k_t := 1) (k_c := 8)
      (fun c ↦ if is1BBool2 c then (Circuit.H 0).eval else 1),
      embedUnitary_muxUnitary, spinCancelMXMux]
    exact muxCongr (concat_compose_block_right _ _ _ _) (concat_compose_block_left _ _ _ _)
      _ _ fun _ ↦ rfl
  rwa [hMux] at hComp
attribute [irreducible] spinCtrlHMidFn mainSpinCancel22Dyn
/-- Forward `wInner2 = 18` inner walk preparation `S_spin * PREP_mid` on `nUB wOuter 18` (`0
D_neg`). -/
noncomputable def inner18Mfwd (wOuter : ℕ) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (uIdx : Unitary (2 ^ 5)) : Unitary (2 ^ nUB wOuter 18) :=
  mainSpinCancelUBMux wOuter 18 * pi128DirectXo7Mux18Of wOuter mux9AltBit π128 uIdx
/-- Hardware `Hot128` `D_neg` diagonal unitary embedded inside `nUB wOuter 18`. -/
noncomputable def hot128NegUB (wOuter : ℕ) : Unitary (2 ^ nUB wOuter 18) :=
  hot128NegRegUnitary (rXoUB wOuter 18) ((rMidUB wOuter 18).compose (rBLoc 18))
    (((disjoint_rOutUB_rMidUB wOuter 18).compose_left _).compose_right _)
/-- `32`-wire (`mMidUB 18 + 8`) forward `S_spin * PREP_mid` mux matching `inner18Mfwd`. -/
noncomputable def inner18MX32Mux (π128 : Equiv.Perm (Fin (2 ^ 7))) (uIdx : Unitary (2 ^ 5)) :
    Unitary (2 ^ (mMidUB 18 + 8)) :=
  spinCancelMXMux 18 * muxUnitary (xo7InMX 18) (midInMX 18) (xo7InMX_disjoint_mid 18)
    (genPi128PrepMid18Of mux9AltBit keep9SliceTargetFn14 π128 uIdx)
theorem embedInner18MX32Mux_ofUB {N wOuter : ℕ} (rUB : QRegister (nUB wOuter 18) N)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (uIdx : Unitary (2 ^ 5)) :
    (mXOfUB rUB).embedUnitary (inner18MX32Mux π128 uIdx) =
      rUB.embedUnitary (inner18Mfwd wOuter π128 uIdx) := by
  dsimp only [inner18MX32Mux, inner18Mfwd, pi128DirectXo7Mux18Of, genPi128DirectXo7Mux18Of,
    directXo7Mux18Of]
  rw [QRegister.embedUnitary_mul, embedSpinCancelMXMux_ofUB, embed_xo7MuxMX_ofUB,
    ← QRegister.embedUnitary_mul]
/-- `13`-wire `(rXo8 ++ rBLoc 18)` subregister inside `mMidUB 18 + 8 = 32`. -/
def xoBInMX32 : QRegister 13 (mMidUB 18 + 8) :=
  (xo8InMX 18).concat ((midInMX 18).compose (rBLoc 18))
    (by rw [QRegister.disjoint_iff]
        intro i j hij
        have hv := congrArg Fin.val hij
        have hj := ((rBLoc 18) j).isLt
        dsimp [xo8InMX, midInMX, mMidUB] at hv hj
        omega)
theorem embedXoBInMX32_ofUB {N wOuter : ℕ} (rUB : QRegister (nUB wOuter 18) N)
    (U : Unitary (2 ^ 13)) :
    (mXOfUB rUB).embedUnitary (xoBInMX32.embedUnitary U) =
      rUB.embedUnitary (((rXoUB wOuter 18).concat ((rMidUB wOuter 18).compose (rBLoc 18))
        (((disjoint_rOutUB_rMidUB wOuter 18).compose_left _).compose_right _)).embedUnitary U) := by
  have hRight : (mXOfUB rUB).compose (xo8InMX 18) = rUB.compose (rXoUB wOuter 18) :=
    concat_compose_block_right _ _ _ _
  have hLeft : (mXOfUB rUB).compose (midInMX 18) = rUB.compose (rMidUB wOuter 18) :=
    concat_compose_block_left _ _ _ _
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
  refine congrArg (QRegister.embedUnitary · U) (CoherentAlias.qreg_ext fun k ↦ ?_)
  by_cases hk : k.val < 8
  · dsimp only [xoBInMX32]
    rw [QRegister.compose_apply, QRegister.compose_apply,
      show k = Fin.castAdd 5 ⟨k.val, hk⟩ from rfl, concat_apply_left, concat_apply_left]
    exact congrArg (fun r : QRegister 8 N ↦ (r ⟨k.val, hk⟩).val) hRight
  · let j : Fin 5 := ⟨k.val - 8, by omega⟩
    dsimp only [xoBInMX32]
    rw [QRegister.compose_apply, QRegister.compose_apply,
      show k = Fin.natAdd 8 j from Fin.ext (by
          dsimp [j]
          omega),
      concat_apply_right, concat_apply_right, QRegister.compose_apply, QRegister.compose_apply]
    exact congrArg (fun r : QRegister (mMidUB 18) N ↦ (r ((rBLoc 18) j)).val) hLeft
theorem preserves_vec_zero {n : ℕ} {M : Operator (2 ^ n)} {K : Finset (Wire n)}
    (hM : PreservesWires M K) {P : BitAssignment n → Prop}
    (hPK : ∀ β₁ β₂ : BitAssignment n, (∀ w ∈ K, β₁ w = β₂ w) → P β₁ → P β₂)
    {ψ : Fin (2 ^ n) → ℂ} (hψ : ∀ j, P (basisBits n j) → ψ j = 0)
    (i : Fin (2 ^ n)) (hi : P (basisBits n i)) : (M *ᵥ ψ) i = 0 := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  by_cases hEq : ∀ w ∈ K, basisBits n i w = basisBits n j w
  · rw [hψ j (hPK _ _ hEq hi), mul_zero]
  · obtain ⟨w, hw, hne⟩ : ∃ w, ∃ (_ : w ∈ K), basisBits n i w ≠ basisBits n j w := by
      simpa only [not_forall, Classical.not_imp] using hEq
    rw [hM i j ⟨w, hw, hne⟩, zero_mul]
theorem bitPerm_vec_zero {k n : ℕ} (r : QRegister k n) (e : Equiv.Perm (BitAssignment k))
    {P Q : BitAssignment n → Prop}
    (hPQ : ∀ β, ¬ P β → ¬ Q (CoherentAlias.writeReg β r (e fun u ↦ β (r u))))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : ∀ j, P (basisBits n j) → ψ j = 0)
    (i : Fin (2 ^ n)) (hi : Q (basisBits n i)) :
    ((r.embedUnitary (CoherentAlias.bitPermUnitary e)).1 *ᵥ ψ) i = 0 := by
  have hExp : ψ = ∑ j : Fin (2 ^ n), ψ j • CoherentAlias.ket (basisBits n j) := by
    ext q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, CoherentAlias.ket,
      SelectSwapQROM.symm_basisBits, basisState, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hExp, Matrix.mulVec_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    CoherentAlias.embedUnitary_bitPermUnitary_mulVec_ket]
  by_cases hPj : P (basisBits n j)
  · rw [hψ j hPj, zero_mul]
  · rw [CoherentAlias.ket, basisState, Pi.single_eq_of_ne, mul_zero]
    intro hEq
    have hb := congrArg (basisBits n) hEq
    rw [CoherentAlias.basisBits_symm_apply] at hb
    exact hPQ (basisBits n j) hPj (by
      rw [← hb]
      exact hi)
theorem keep9Slice_alt_lt30 (rc : Fin (2 ^ 7)) (x : Fin (2 ^ 5)) (hx : x.val < 30) :
    (finOfBits 5 fun i : Fin 5 ↦
      decide (keep9SliceTargetFn14 rc x ⟨i.val, by omega⟩ = 1)).val < 30 := by
  by_cases hrc : rc.val < 126
  · have hEq : (finOfBits 5 fun i : Fin 5 ↦
        decide (keep9SliceTargetFn14 rc x ⟨i.val, by omega⟩ = 1)) =
        ⟨(keep9InnerAliasTable ⟨rc.val, hrc⟩ ⟨x.val, hx⟩).alt.val,
          (keep9InnerAliasTable ⟨rc.val, hrc⟩ ⟨x.val, hx⟩).alt.isLt.trans (by decide)⟩ := by
      apply (basisBits 5).injective
      funext i
      dsimp only [finOfBits]
      rw [SelectSwapQROM.basisBits_symm]
      change (if decide (keep9SliceTargetFn14 rc x ⟨i.val, _⟩ = 1) = true then (1 : ZMod 2)
        else 0) = _
      have hBit : keep9SliceTargetFn14 rc x ⟨i.val, by omega⟩ =
          if keep9InnerAliasBits ⟨rc.val, hrc⟩ ⟨x.val, hx⟩ ⟨i.val, by omega⟩ then 1 else 0 := by
        dsimp only [keep9SliceTargetFn14]
        rw [keep9Hot24BoolTable_of_lt hrc hx ⟨i.val, by omega⟩]
      rw [hBit]
      dsimp only [keep9InnerAliasBits]
      simp only [i.isLt, ↓reduceIte, basisBits_eq_testBit]
      cases ((keep9InnerAliasTable ⟨rc.val, hrc⟩ ⟨x.val, hx⟩).alt.val).testBit i.val <;> rfl
    rw [hEq]
    exact (keep9InnerAliasTable ⟨rc.val, hrc⟩ ⟨x.val, hx⟩).alt.isLt
  · have hZ : (fun i : Fin 5 ↦ decide (keep9SliceTargetFn14 rc x ⟨i.val, by omega⟩ = 1)) =
        fun _ ↦ false := funext fun i ↦ by
      have h0 : keep9SliceTargetFn14 rc x ⟨i.val, by omega⟩ = 0 := by
        dsimp only [keep9SliceTargetFn14]
        rw [keep9Hot24BoolTable_of_ge (by omega) x ⟨i.val, by omega⟩]
        rfl
      rw [h0]
      rfl
    rw [hZ]
    decide
theorem b_lt_30_ofPrepMid18FromSliceKeep9_ne_zero
    (muxBit : Fin (2 ^ 4) → Fin (2 ^ 9) → Bool) {uIdx : Unitary (2 ^ 5)}
    (huVanish : ∀ x : Fin (2 ^ 5), 30 ≤ x.val → (uIdx.1 *ᵥ basisState 0) x = 0)
    (rc : Fin (2 ^ 7)) (m : Fin (2 ^ mMidUB 18))
    (hne : (prepMid18FromSlice muxBit keep9SliceTargetFn14 uIdx rc).1 m 0 ≠ 0) :
    ((rBLoc 18).extractIndex m).val < 30 := by
  by_contra hge
  have hm30 : 30 ≤ ((rBLoc 18).extractIndex m).val := by omega
  let idxB (β : BitAssignment (mMidUB 18)) : Fin (2 ^ 5) :=
    (basisBits 5).symm fun i ↦ β ((rBLoc 18) i)
  let rAlt : QRegister 5 (mMidUB 18) := QRegister.block 5 5 (by decide)
  let altB (β : BitAssignment (mMidUB 18)) : Fin (2 ^ 5) :=
    (basisBits 5).symm fun i ↦ β (rAlt i)
  let r05 := mid18Core23Reg.compose core23IdxReg
  have hr05 : r05 = rBLoc 18 := CoherentAlias.qreg_ext fun i ↦ by fin_cases i <;> rfl
  let ψ0 : Fin (2 ^ mMidUB 18) → ℂ := basisState 0
  let ψ1 := (r05.embedUnitary uIdx).1 *ᵥ ψ0
  have hψ1 (j : Fin (2 ^ mMidUB 18)) (hj : 30 ≤ (idxB (basisBits _ j)).val ∨
      ∃ i : Fin 5, basisBits _ j (rAlt i) ≠ 0) : ψ1 j = 0 := by
    rcases hj with h30 | ⟨i, hi⟩
    · change ((r05.embedUnitary uIdx).1 *ᵥ ψ0) j = 0
      rw [hr05, QRegister.embedUnitary_val, (rBLoc 18).embedMatrix_mulVec_apply]
      refine Finset.sum_eq_zero fun loc _ ↦ ?_
      by_cases h0 : (rBLoc 18).basisSplitEquiv.symm (loc, ((rBLoc 18).basisSplitEquiv j).2) = 0
      · have hEnv0 : ((rBLoc 18).basisSplitEquiv j).2 = ((rBLoc 18).basisSplitEquiv 0).2 := by
          have := congrArg ((rBLoc 18).basisSplitEquiv · |>.2) h0
          rwa [Equiv.apply_symm_apply] at this
        have hloc0 : loc = 0 := by
          have := congrArg (rBLoc 18).extractIndex h0
          rwa [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply,
            show (rBLoc 18).extractIndex 0 = 0 by decide] at this
        subst hloc0
        have hex : idxB (basisBits _ j) = (rBLoc 18).extractIndex j := by
          apply (basisBits 5).injective
          funext k
          dsimp only [idxB]
          rw [SelectSwapQROM.basisBits_symm,
            QRegister.basisBits_extractIndex]
        have hu0 : uIdx.1 ((rBLoc 18).extractIndex j) 0 = 0 := by
          simpa [basisState, Matrix.mulVec_single_one, Matrix.col_apply] using
            huVanish ((rBLoc 18).extractIndex j) (hex ▸ h30)
        rw [hu0, zero_mul]
      · simp [ψ0, basisState, Pi.single_eq_of_ne h0]
    · refine preserves_vec_zero (preservesWires_embedMatrix_of_disjoint r05 uIdx.1 rAlt.image
        (SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr (by decide))))
        (P := fun β ↦ β (rAlt i) ≠ 0) (fun β₁ β₂ hEq h1 ↦ by
          rwa [← hEq (rAlt i) ((QRegister.mem_image rAlt _).mpr ⟨i, rfl⟩)])
        (fun q hq ↦ ?_) j hi
      by_cases hq0 : q = 0
      · subst hq0
        have h0w : basisBits (mMidUB 18) 0 (rAlt i) = 0 := by simp [basisBits_eq_testBit]
        exact absurd h0w hq
      · simp [ψ0, basisState, Pi.single_eq_of_ne hq0]
  let rPk := mid18Core23Reg.compose core23PktReg
  let ψ2 := (rPk.embedUnitary optCoin9Unitary).1 *ᵥ ψ1
  have hψ2 (j : Fin (2 ^ mMidUB 18)) (hj : 30 ≤ (idxB (basisBits _ j)).val ∨
      ∃ i : Fin 5, basisBits _ j (rAlt i) ≠ 0) : ψ2 j = 0 :=
    preserves_vec_zero (preservesWires_embedMatrix_of_disjoint rPk optCoin9Unitary.1
      ((rBLoc 18).image ∪ rAlt.image) (Finset.disjoint_union_right.mpr
        ⟨SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr (by decide)),
         SelectSwapQROM.disjoint_image_of_disjointWires
           (QRegister.disjoint_iff.mpr (by decide))⟩))
      (P := fun β ↦ 30 ≤ (idxB β).val ∨ ∃ i : Fin 5, β (rAlt i) ≠ 0)
      (fun β₁ β₂ hEq h1 ↦ by
        have hI : idxB β₁ = idxB β₂ := congrArg (basisBits 5).symm (funext fun k ↦
          hEq _ (Finset.mem_union_left _ ((QRegister.mem_image _ _).mpr ⟨k, rfl⟩)))
        rcases h1 with h30 | ⟨i, hi⟩
        · exact Or.inl (hI ▸ h30)
        · exact Or.inr ⟨i, (hEq _ (Finset.mem_union_right _
            ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩))) ▸ hi⟩) hψ1 j hj
  let rQr := mid18Core23Reg.compose core23Qrom19Reg
  let ψ3 := (rQr.embedUnitary (aliasTableXorUnitary 5 14 (keep9SliceTargetFn14 rc))).1 *ᵥ ψ2
  have hψ3 (j : Fin (2 ^ mMidUB 18))
      (hj : 30 ≤ (idxB (basisBits _ j)).val ∨ 30 ≤ (altB (basisBits _ j)).val) : ψ3 j = 0 := by
    dsimp only [ψ3, aliasTableXorUnitary]
    refine bitPerm_vec_zero rQr ⟨aliasTableXorBits 5 14 (keep9SliceTargetFn14 rc),
      aliasTableXorBits 5 14 (keep9SliceTargetFn14 rc),
      aliasTableXorBits_self 5 14 (keep9SliceTargetFn14 rc),
      aliasTableXorBits_self 5 14 (keep9SliceTargetFn14 rc)⟩
      (P := fun β ↦ 30 ≤ (idxB β).val ∨ ∃ i : Fin 5, β (rAlt i) ≠ 0)
      (Q := fun β ↦ 30 ≤ (idxB β).val ∨ 30 ≤ (altB β).val)
      (fun β hNot hBad ↦ ?_) hψ2 j hj
    rw [not_or] at hNot
    obtain ⟨hIdxLt, hAlt0⟩ := hNot
    rw [not_le] at hIdxLt
    simp only [not_exists, not_ne_iff] at hAlt0
    let γ := CoherentAlias.writeReg β rQr
      (aliasTableXorBits 5 14 (keep9SliceTargetFn14 rc) fun u ↦ β (rQr u))
    have hγIdx : idxB γ = idxB β := congrArg (basisBits 5).symm (funext fun k ↦ by
      have hrk : (rBLoc 18) k = rQr ⟨k.val, by omega⟩ := by fin_cases k <;> rfl
      rw [hrk]
      dsimp only [γ]
      rw [CoherentAlias.writeReg_apply_reg]
      simp [aliasTableXorBits, k.isLt])
    have hAddr : ((basisBits 5).symm fun u : Fin 5 ↦ β (rQr ⟨u.val, by omega⟩)) = idxB β :=
      congrArg (basisBits 5).symm (funext fun u ↦ congrArg β (by fin_cases u <;> rfl))
    have hγAlt : altB γ = (finOfBits 5 fun i : Fin 5 ↦
        decide (keep9SliceTargetFn14 rc (idxB β) ⟨i.val, by omega⟩ = 1)) := by
      apply (basisBits 5).injective
      funext k
      dsimp only [altB, finOfBits]
      rw [SelectSwapQROM.basisBits_symm, SelectSwapQROM.basisBits_symm]
      have hrk : rAlt k = rQr ⟨5 + k.val, by omega⟩ := by fin_cases k <;> rfl
      rw [hrk]
      dsimp only [γ]
      rw [CoherentAlias.writeReg_apply_reg]
      simp only [aliasTableXorBits, show 5 ≤ 5 + k.val by omega, ↓reduceDIte, hAddr, ← hrk,
        hAlt0 k, zero_add, show (⟨5 + k.val - 5, by omega⟩ : Fin 14) = ⟨k.val, by omega⟩ from
          Fin.ext (by
              dsimp
              omega)]
      rcases CircuitModular.UnsignedGivens.zmod2_eq_zero_or_one
        (keep9SliceTargetFn14 rc (idxB β) ⟨k.val, by omega⟩) with h0 | h1
      · simp [h0]
      · simp [h1]
    rcases hBad with hI | hA
    · change 30 ≤ (idxB γ).val at hI
      rw [hγIdx] at hI
      omega
    · change 30 ≤ (altB γ).val at hA
      rw [hγAlt] at hA
      exact absurd (keep9Slice_alt_lt30 rc (idxB β) hIdxLt) (by omega)
  let rMs := mid18Core23Reg.compose Inner18Symp14Walk.core23MuxSwap23Reg
  let ψ4 := (rMs.embedUnitary (pktMuxSwap23Unitary muxBit)).1 *ᵥ ψ3
  have hψ4 (j : Fin (2 ^ mMidUB 18)) (hj : 30 ≤ (idxB (basisBits _ j)).val) : ψ4 j = 0 := by
    dsimp only [ψ4]
    rw [pktMuxSwap23Unitary_eq_bitPermUnitary]
    refine bitPerm_vec_zero rMs (pktMuxSwap23Perm muxBit)
      (P := fun β ↦ 30 ≤ (idxB β).val ∨ 30 ≤ (altB β).val)
      (Q := fun β ↦ 30 ≤ (idxB β).val)
      (fun β hNot hBad ↦ ?_) hψ3 j hj
    rw [not_or, not_le, not_le] at hNot
    obtain ⟨hI, hA⟩ := hNot
    let γ := CoherentAlias.writeReg β rMs (pktMuxSwap23Bits muxBit fun u ↦ β (rMs u))
    let sw := muxBit (finOfBits 4 fun i ↦ decide (β (rMs ⟨10 + i.val, by omega⟩) = 1))
      (finOfBits 9 fun k ↦ decide (β (rMs ⟨14 + k.val, by omega⟩) = 1))
    have hγ : idxB γ = if sw then altB β else idxB β := by
      cases hsw : sw
      · refine congrArg (basisBits 5).symm (funext fun k ↦ ?_)
        have hrk : (rBLoc 18) k = rMs ⟨k.val, by omega⟩ := by fin_cases k <;> rfl
        rw [hrk]
        dsimp only [γ]
        rw [CoherentAlias.writeReg_apply_reg]
        simp [pktMuxSwap23Bits, show muxBit _ _ = false from hsw]
      · refine congrArg (basisBits 5).symm (funext fun k ↦ ?_)
        have hrk : (rBLoc 18) k = rMs ⟨k.val, by omega⟩ := by fin_cases k <;> rfl
        rw [hrk]
        dsimp only [γ]
        rw [CoherentAlias.writeReg_apply_reg]
        simp only [pktMuxSwap23Bits, k.isLt, ↓reduceDIte,
          show muxBit _ _ = true from hsw, ↓reduceIte]
        exact congrArg β (by fin_cases k <;> rfl)
    rw [pktMuxSwap23Perm_apply, hγ] at hBad
    split_ifs at hBad <;> omega
  let ψ5 := ((rSigInLoc 18).embedUnitary (Circuit.H 0).eval).1 *ᵥ ψ4
  have hψ5 : ψ5 m = 0 :=
    preserves_vec_zero (preservesWires_embedMatrix_of_disjoint (rSigInLoc 18) _ (rBLoc 18).image
      (SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr (by decide))))
      (P := fun β ↦ 30 ≤ (idxB β).val)
      (fun β₁ β₂ hEq h1 ↦ by
        have hI : idxB β₁ = idxB β₂ := congrArg (basisBits 5).symm (funext fun k ↦
          hEq _ ((QRegister.mem_image _ _).mpr ⟨k, rfl⟩))
        exact hI ▸ h1) hψ4 m (by
          have hex : idxB (basisBits _ m) = (rBLoc 18).extractIndex m := by
            apply (basisBits 5).injective
            funext k
            dsimp only [idxB]
            rw [SelectSwapQROM.basisBits_symm,
              QRegister.basisBits_extractIndex]
          exact hex ▸ hm30)
  have hEq5 : (prepMid18FromSlice muxBit keep9SliceTargetFn14 uIdx rc).1 m 0 = ψ5 m := by
    have hv : (prepMid18FromSlice muxBit keep9SliceTargetFn14 uIdx rc).1 m 0 =
        ((prepMid18FromSlice muxBit keep9SliceTargetFn14 uIdx rc).1 *ᵥ ψ0) m := by
      change _ = ((prepMid18FromSlice muxBit keep9SliceTargetFn14 uIdx rc).1 *ᵥ basisState 0) m
      rw [basisState, Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hv]
    dsimp only [prepMid18FromSlice, core23, coin9Perm23, ψ5, ψ4, ψ3, ψ2, ψ1,
      rMs, rQr, rPk, r05]
    simp only [QRegister.embedUnitary_mul, QRegister.embedUnitary_compose, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec]
  exact hne (hEq5.trans hψ5)
/-! ## Section 5: `workPlace` Relocation & Coarse/Medium `wInner2 = 18` Walk Legs -/
/-- Local `32`-wire `(mMidUB 18 + 8)` register inside `32 + kInner`. -/
abbrev locMX (kInner : ℕ) : QRegister (mMidUB 18 + 8) (32 + kInner) :=
  QRegister.block 0 32 (by omega)
/-- Local `kInner`-wire scratch register inside `32 + kInner`. -/
abbrev locScr (kInner : ℕ) : QRegister kInner (32 + kInner) :=
  QRegister.block 32 kInner (by omega)
theorem locMX_disjoint_scr (kInner : ℕ) : (locMX kInner).DisjointWires (locScr kInner) :=
  QRegister.disjoint_iff.mpr fun i j hij ↦ by
    have hv := congrArg Fin.val hij
    have hi := i.isLt
    dsimp [locMX, locScr, mMidUB] at hv hi
    omega
/-- `(32 + kInner)`-wire workspace `(mXOfUB rUB) ++ rScrUb[0..kInner)` disjoint from Bell pairs
and `rScrUb ⟨kInner, _⟩` when `1 + kInner ≤ sUb`. -/
abbrev workPlace {N wOuter sUb : ℕ} (rUB : QRegister (nUB wOuter 18) N) (rScrUb : QRegister sUb N)
    (kInner : ℕ) (hk : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) :
    QRegister (32 + kInner) N :=
  (mXOfUB rUB).concat (rScrUb.slice 0 kInner (by omega))
    (disjointWires_concat_left _ ((hDisj.compose_left _).compose_right _)
      ((hDisj.compose_left _).compose_right _))
theorem workPlace_compose_locMX {N wOuter sUb : ℕ} (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) :
    (workPlace rUB rScrUb kInner hk hDisj).compose (locMX kInner) = mXOfUB rUB :=
  concat_compose_block_left _ _ _ _
theorem workPlace_compose_locScr {N wOuter sUb : ℕ} (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ) (hk : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) :
    (workPlace rUB rScrUb kInner hk hDisj).compose (locScr kInner) =
      rScrUb.slice 0 kInner (by omega) :=
  concat_compose_block_right _ _ _ _
theorem disjoint_support_onRegisterWorkPlace {Var : Type} {N wOuter sUb kInner : ℕ}
    (rMain : QRegister (nUB wOuter 18 + 11) N) (rScrUb : QRegister sUb N)
    (hk1 : 1 + kInner ≤ sUb) (hMainScr : rMain.DisjointWires rScrUb)
    (pLoc : DynamicCircuit Var (32 + kInner)) :
    let rUB := rMain.compose (rUBInCat wOuter 18 11)
    Disjoint (pLoc.onRegister (workPlace rUB rScrUb kInner (by omega)
        (hMainScr.compose_left _))).support
      ((((rMain.compose (rSysCatUB wOuter 18 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).image ∪ {rScrUb ⟨kInner, by omega⟩})) := by
  intro rUB
  have hSub := (DynamicCircuit.support_onRegister_subset
    (workPlace rUB rScrUb kInner (by omega) (hMainScr.compose_left _)) pLoc).trans
    (le_of_eq (QRegister.image_concat _ _ _))
  have hSysEq : ((rMain.compose (rSysCatUB wOuter 18 11)).compose
      (QRegister.block 0 (2 * 58) (by decide))) = rUB.compose (rSysUB wOuter 18) := by
    rw [QRegister.compose_assoc, rSysCatUB, concat_compose_block_left, ← QRegister.compose_assoc]
  rw [hSysEq]
  refine Disjoint.mono_left hSub (Finset.disjoint_union_left.mpr ⟨?_, ?_⟩)
  · rw [QRegister.image_concat, Finset.disjoint_union_left, Finset.disjoint_union_right,
      Finset.disjoint_union_right]
    have hdMS : (rMidUB wOuter 18).DisjointWires (rSysUB wOuter 18) :=
      QRegister.disjoint_iff.mpr fun i j hij ↦ by
        have hv := congrArg Fin.val hij
        have := j.isLt
        simp [rMidUB, rSysUB, mOutUB] at hv
        omega
    have hdXS : (rXoUB wOuter 18).DisjointWires (rSysUB wOuter 18) :=
      QRegister.disjoint_iff.mpr fun i j hij ↦ by
        have hv := congrArg Fin.val hij
        have := j.isLt
        simp [rXoUB, rOutUB, rXoLoc, rSysUB] at hv
        omega
    refine ⟨⟨SelectSwapQROM.disjoint_image_of_disjointWires (compose_disjoint_zc20 rUB hdMS),
      Finset.disjoint_singleton_right.mpr fun hm ↦ ?_⟩,
      ⟨SelectSwapQROM.disjoint_image_of_disjointWires (compose_disjoint_zc20 rUB hdXS),
      Finset.disjoint_singleton_right.mpr fun hm ↦ ?_⟩⟩
    · obtain ⟨i, hi⟩ := (QRegister.mem_image _ _).mp hm
      exact ((hMainScr.compose_left (rUBInCat wOuter 18 11)).compose_left (rMidUB wOuter 18)).ne
        i ⟨kInner, by omega⟩ hi
    · obtain ⟨i, hi⟩ := (QRegister.mem_image _ _).mp hm
      exact ((hMainScr.compose_left (rUBInCat wOuter 18 11)).compose_left (rXoUB wOuter 18)).ne
        i ⟨kInner, by omega⟩ hi
  · refine Finset.disjoint_union_right.mpr
      ⟨SelectSwapQROM.disjoint_image_of_disjointWires
        (((hMainScr.compose_left _).compose_left _).compose_right _).symm,
       Finset.disjoint_singleton_right.mpr fun hm ↦ ?_⟩
    obtain ⟨u, hu⟩ := (QRegister.mem_image _ _).mp hm
    have hv := congrArg Fin.val (rScrUb.wires.injective (hu.symm.trans (slice_apply ..)))
    have := u.isLt
    dsimp at hv
    omega

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsB
end
