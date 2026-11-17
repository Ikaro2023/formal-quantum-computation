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
public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Outer8TwoRotWalk
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Outer8Pi145Prep
@[expose] public section
/-! # `68-T` `Hot128` One-Sided `D_neg` & `55`-AND `State24` `π145` `SiZero` Router -/
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Pi145CompactRouter
open QuantumComputation.Specs QuantumComputation.Specs.P450
local instance (priority := 99999) neZero2 (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
open Function Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution QuantumComputation.Specs.P450
  CircuitModular GivensOps BlockEncodingCore BlockEncodingCircuit AliasPrep SelectSwapQROM
  SelectRouter10 Lac2Fused184Select PolymorphicFused184Select
  CompactStepFast176Select CompactOuter9Bound50Core CompactOuter9Bound50Select
  Pi145SOSPermBridge Balanced160Select LowBitPi145Select
  StepBound148Borrow StepOuter8Pi145Outer
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GroupUnary (
  predProj predProj_conjTranspose restrictPred_coe)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Mobius126OneHot (
  cleanPredProj)
open QRegister (block block_disjoint_of_le concat_apply_left concat_apply_right compose_apply
  disjoint_iff disjointWires_concat_left image_concat image_singleton)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Lac2Folded184Select (
  revComputeDyn revUncomputeDyn
  count_revComputeDyn_toff count_revComputeDyn_t count_revUncomputeDyn_toff count_revUncomputeDyn_t)
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.XMeasCircuit (
  phaseFlipUnitary phaseFlipUnitary_val phaseFlipUnitary_mulVec_ket
  phaseFlipUnitary_conjTranspose embedUnitary_phaseFlipUnitary dynOnRegister count_dynOnRegister)
open
  _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens
  (maskSumBit cnotMaskReg evolve_cnotMaskReg_ket basisBits_symm_eq)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
/-- Exact two-body sign bit `(-1)^{negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b}` (`<126, <30`). -/
def defaultNegBit (xo' : Fin (2 ^ 8)) (b : Fin (2 ^ 5)) : Bool := decide (xo'.val < 126 ∧ b.val <
  30) && negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b
/-- Hardware `Hot128` sign bit agreeing with `defaultNegBit` whenever `b < 30` or `126 ≤ xo'`. -/
def hot128NegBit2 (xo' : Fin (2 ^ 8)) (b : Fin (2 ^ 5)) : Bool := if b.val < 30 then
  defaultNegBit xo' b else defaultNegBit xo' ⟨b.val - 16, by omega⟩
@[simp] theorem hot128NegBit_eq_default_of_lt30_or_ge126 (xo' : Fin (2 ^ 8)) (b : Fin (2 ^ 5)) (h
  : b.val < 30 ∨ 126 ≤ xo'.val) : hot128NegBit2 xo' b = defaultNegBit xo' b := by
  rcases h with hb | hx
  exacts [ite_eq_left hb, by simp [hot128NegBit2, defaultNegBit, show ¬ xo'.val < 126 by omega]]
/-- Generic `13`-qubit (`xo' : 8`, `b : 5`) phase exponent for a `(Fin 256, Fin 32)` sign table. -/
noncomputable def negPh13 (f : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) (β : BitAssignment 13) : ZMod 2
  := if f ((basisBits 8).symm fun i ↦ β ⟨i.val, by omega⟩) ((basisBits 5).symm fun j ↦ β
  ⟨8 + j.val, by omega⟩) then 1 else 0
/-- Hardware `13`-qubit diagonal `D_neg` unitary flipping phase by `hot128NegBit2`. -/
noncomputable def hot128NegUnitary : Unitary (2 ^ 13) := phaseFlipUnitary (negPh13
  hot128NegBit2)
/-- Ambient `N`-qubit hardware `D_neg` unitary embedded on `rXo.concat rB`. -/
noncomputable abbrev hot128NegRegUnitary {N : ℕ} (rXo : QRegister 8 N) (rB : QRegister 5 N) (hXoB
  : rXo.DisjointWires rB) : Unitary (2 ^ N) := (rXo.concat rB hXoB).embedUnitary hot128NegUnitary
theorem negPh13_concat {N : ℕ} (f : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) (rXo : QRegister 8 N) (rB :
  QRegister 5 N) (hXoB : rXo.DisjointWires rB) (β : BitAssignment N) : negPh13 f (fun k ↦ β
  ((rXo.concat rB hXoB) k)) = if f (UnsignedGivens.localIdx rXo β) (UnsignedGivens.localIdx rB β)
    then 1 else 0 :=
  congrArg₂ (if f · · then 1 else 0) (congrArg (basisBits 8).symm (funext fun i ↦ congrArg β
  (concat_apply_left rXo rB hXoB i))) (congrArg (basisBits 5).symm (funext fun j ↦ congrArg β
  ((congrArg (rXo.concat rB hXoB) (Fin.ext (by simp) : _ = Fin.natAdd 8 j)).trans
  (concat_apply_right rXo rB hXoB j))))
theorem embedNegPh13_ket {N : ℕ} (f : Fin (2 ^ 8) → Fin (2 ^ 5) → Bool) (rXo : QRegister 8 N) (rB
  : QRegister 5 N) (hXoB : rXo.DisjointWires rB) (β : BitAssignment N) : ((rXo.concat rB
  hXoB).embedUnitary (phaseFlipUnitary (negPh13 f))).1.mulVec (SelectSwapQROM.ket β) = (if f
  (UnsignedGivens.localIdx rXo β) (UnsignedGivens.localIdx rB β) then (-1 : ℂ) else 1) •
    SelectSwapQROM.ket β := by
  change ((rXo.concat rB hXoB).embedUnitary (phaseFlipUnitary (negPh13 f))).1 *ᵥ XMeasCircuit.ket β
    = _
  rw [embedUnitary_phaseFlipUnitary, phaseFlipUnitary_mulVec_ket, negPh13_concat]
  cases f (UnsignedGivens.localIdx rXo β) (UnsignedGivens.localIdx rB β) <;> rfl
/-- Base `b_4 = 0` (`b = 0..15`) sign mask across `g : Fin 128`. -/
def val0Table (c : Fin 16) (g : Fin 128) := defaultNegBit ⟨g.val, by omega⟩ ⟨c.val, by omega⟩
/-- Differential `b_4 = 1` (`c = 0..13`, `b = 16 + c < 30`) XOR mask across `g : Fin 128`. -/
def deltaTable (k : Fin 14) (g : Fin 128) : Bool := xor (defaultNegBit ⟨g.val, by omega⟩
  ⟨k.val, by omega⟩) (defaultNegBit ⟨g.val, by omega⟩ ⟨16 + k.val, by omega⟩)
/-- Exact `134`-qubit (`xo7 : 1`, `rB : 5`, `rHot : 128`) phase exponent of `hot128DNeg62Dyn`. -/
noncomputable def hot128Ph134 (β : BitAssignment 134) : ZMod 2 :=
  let c : Fin 16 := (basisBits 4).symm fun j ↦ β ⟨1 + j.val, by omega⟩
  (1 + β ⟨0, by decide⟩) * (maskSumBit (block 6 128 (by decide)) (val0Table c) β + if hk : c.val <
    14 then β ⟨5, by decide⟩ * maskSumBit (block 6 128 (by decide)) (deltaTable ⟨c.val, hk⟩) β else
    0)
/-- Exact `134`-qubit diagonal unitary cleanly realized by `hot128DNeg62Dyn`. -/
noncomputable def hot128DNegUnitary : Unitary (2 ^ 134) := phaseFlipUnitary hot128Ph134
/-- Precondition for `dWGated`: one-hot `w0` if `wXo7 = 0`, all-zero `w0` if `wXo7 = 1`. -/
def InvWGated {n : ℕ} (R : ℕ) (wXo7 : Wire n) (w0 w1 : Fin R → Wire n) (qEnc : Wire n) (γ :
  BitAssignment n) : Prop := γ qEnc = 0 ∧ (∀ i : Fin R, γ (w1 i) = 0) ∧ (if γ wXo7 = 0 then ∃ iStar
  : Fin R, γ (w0 iStar) = 1 ∧ ∀ i : Fin R, i ≠ iStar → γ (w0 i) = 0 else ∀ i : Fin R, γ (w0 i) = 0)
/-- `(2 + 2 * R)`-`T` (`0 TOFF`) `!wXo7`-gated W-state controlled range swap on `R` wire pairs. -/
def dWGated {Var : Type} {n : ℕ} (v : Var) (R : ℕ) (wXo7 ctrl : Wire n) (w0 w1 : Fin R → Wire n)
  (qEnc : Wire n) (hv : WSplitValid R ctrl w0 w1 qEnc) (hxo7 : wXo7 ≠ qEnc) : DynamicCircuit Var n
  := measureZ1AndBranch v qEnc (CoherentAlias.ctrlH.onRegister (QRegister.pair wXo7 qEnc hxo7) ;;ᶜ
  wSeqFin R (fun i ↦ wSplitPair (w0 i) (w1 i) (hv.w01_ne i i)) ;;ᶜ wSeqFin R (fun i ↦ Circuit.CNOT
  (w1 i) qEnc (hv.q_w1 i).symm) ;;ᶜ Circuit.CNOT ctrl qEnc hv.q_ctrl.symm) (Circuit.X qEnc ;;ᶜ
  wSeqFin R fun i ↦ swap3Circ (w0 i) (w1 i) (hv.w01_ne i i))
theorem count_mbu {Var : Type} {n a : ℕ} (v : Var) (q : Wire n) (cPre cFix : Circuit n) (g :
  PrimitiveGate a) : (measureZ1AndBranch v q cPre cFix).count g = cPre.count g + cFix.count g := by
  simp [measureZ1AndBranch, DynamicCircuit.count, DynamicCircuit.identity]
@[simp] theorem dWGated_toff {Var : Type} {n : ℕ} (v : Var) (R : ℕ) (wXo7 ctrl : Wire n) (w0 w1 :
  Fin R → Wire n) (qEnc : Wire n) (hv : WSplitValid R ctrl w0 w1 qEnc) (hxo7 : wXo7 ≠ qEnc) :
  (dWGated v R wXo7 ctrl w0 w1 qEnc hv hxo7).count .TOFF = 0 := by
  simp [dWGated, count_mbu, wSeqFin_count_eq_zero .TOFF R _ fun i ↦ wSplitPair_count_toff (w0 i) (w1
    i) _, wSeqFin_count_eq_zero .TOFF R (fun i ↦ Circuit.CNOT (w1 i) qEnc (hv.q_w1 i).symm) fun _ ↦
    rfl, wSeqFin_count_eq_zero .TOFF R _ fun i ↦ swap3Circ_count_toff (w0 i) (w1 i) _]
@[simp] theorem dWGated_t {Var : Type} {n : ℕ} (v : Var) (R : ℕ) (wXo7 ctrl : Wire n) (w0 w1 : Fin R
  → Wire n) (qEnc : Wire n) (hv : WSplitValid R ctrl w0 w1 qEnc) (hxo7 : wXo7 ≠ qEnc) : (dWGated v R
  wXo7 ctrl w0 w1 qEnc hv hxo7).count .T = 2 + 2 * R := by
  simp [dWGated, count_mbu, wSeqFin_count_const .T 2 R _ fun i ↦ wSplitPair_count_t (w0 i) (w1 i) _,
    wSeqFin_count_eq_zero .T R (fun i ↦ Circuit.CNOT (w1 i) qEnc (hv.q_w1 i).symm) fun _ ↦ rfl,
    wSeqFin_count_eq_zero .T R _ fun i ↦ swap3Circ_count_t (w0 i) (w1 i) _]
theorem cswapRange_oneHot {n R : ℕ} {ctrl : Wire n} {w0 w1 : Fin R → Wire n} (hd : WPairDisj R ctrl
  w0 w1) (β : BitAssignment n) (i0 : Fin R) (hw1_0 : ∀ i, β (w1 i) = 0) (hw0_1 : β (w0 i0) = 1)
  (hw0_0 : ∀ i, i ≠ i0 → β (w0 i) = 0) : cswapRangeBits R ctrl w0 w1 β = if β ctrl = 1 then update
  (update β (w0 i0) 0) (w1 i0) 1 else β := by
  by_cases hc : β ctrl = 1
  · refine funext fun u ↦ ?_
    conv_rhs => rw [ite_eq_left hc]
    rcases Classical.em (∃ i : Fin R, u = w0 i) with ⟨i, rfl⟩ | h0
    · rw [cswapRangeBits_w0 hd β i, ite_eq_left hc, hw1_0 i]
      rcases eq_or_ne i i0 with rfl | hi
      exacts [(by rw [update_of_ne (hd.w01_ne i i), update_self]),
        (by rw [update_of_ne (hd.w01_ne i i0), update_of_ne (hd.w0_inj.ne hi), hw0_0 i hi])]
    · rcases Classical.em (∃ i : Fin R, u = w1 i) with ⟨i, rfl⟩ | h1
      · rw [cswapRangeBits_w1 hd β i, ite_eq_left hc]
        rcases eq_or_ne i i0 with rfl | hi
        exacts [by rw [update_self, hw0_1], by rw [update_of_ne (hd.w1_inj.ne hi),
          update_of_ne (hd.w01_ne i0 i).symm, hw0_0 i hi, hw1_0 i]]
      · rw [cswapRangeBits_other β (fun i he ↦ h0 ⟨i, he⟩) (fun i he ↦ h1 ⟨i, he⟩), update_of_ne
          (fun he ↦ h1 ⟨i0, he⟩), update_of_ne (fun he ↦ h0 ⟨i0, he⟩)]
  · simp only [cswapRangeBits, ite_eq_right hc]
theorem EquivRev.dWGated {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var) (R : ℕ) (wx
  ctrl : Wire n) (w0 w1 : Fin R → Wire n) (q : Wire n) (hv : WSplitValid R ctrl w0 w1 q) (hxo7 : wx
  ≠ q) (S : BitAssignment n → Bool) (hI : ∀ β, S β = true → InvWGated R wx w0 w1 q β) : EquivRev v S
  (splitRevLoop ctrl R w0 w1 hv.toWPairDisj) (dWGated v R wx ctrl w0 w1 q hv hxo7) := by
  refine ⟨fun β hS ↦ (splitRevLoop_spec ctrl R w0 w1 hv.toWPairDisj β (hI β hS).2.1).1,
    BijectiveBitMap.ofInvolutive (cswapRangeBits R ctrl w0 w1) (cswapRangeBits_involutive
    hv.toWPairDisj), ?_, fun β hS ↦ (splitRevLoop_spec ctrl R w0 w1 hv.toWPairDisj β (hI β
    hS).2.1).2.symm⟩
  let cPre := CoherentAlias.ctrlH.onRegister (QRegister.pair wx q hxo7) ;;ᶜ wSeqFin R (fun i ↦
    wSplitPair (w0 i) (w1 i) (hv.w01_ne i i)) ;;ᶜ wSeqFin R (fun i ↦ Circuit.CNOT (w1 i) q (hv.q_w1
    i).symm) ;;ᶜ Circuit.CNOT ctrl q hv.q_ctrl.symm
  let cSw := wSeqFin R fun i ↦ swap3Circ (w0 i) (w1 i) (hv.w01_ne i i)
  have hSplit (β : BitAssignment n) (hS : S β = true) : ∃ βt : BitAssignment n, update β q 0 = β ∧
    update βt q 0 = βt ∧ cswapRangeBits R ctrl w0 w1 β = (if β ctrl = 1 then βt else β) ∧
    cPre.eval.1 *ᵥ SelectSwapQROM.ket β = sqrtHalf • SelectSwapQROM.ket (update β q (β ctrl)) +
    sqrtHalf • SelectSwapQROM.ket (update βt q (1 + β ctrl)) ∧ cSw.eval.1 *ᵥ SelectSwapQROM.ket
    β = SelectSwapQROM.ket βt ∧ cSw.eval.1 *ᵥ SelectSwapQROM.ket βt = SelectSwapQROM.ket β
    := by
    obtain ⟨hq0, hw1_0, hCases⟩ := hI β hS
    have hsum0 : (∑ i : Fin R, β (w1 i)) = 0 := Finset.sum_eq_zero fun i _ ↦ hw1_0 i
    rcases bit_cases (β wx) with hx0 | hx1
    · rw [hx0, ite_eq_left rfl] at hCases
      obtain ⟨i0, hw0_1, hw0_0⟩ := hCases
      let βm := update (update β (w0 i0) 0) (w1 i0) 1
      have hqm : βm q = 0 := ((update_of_ne (hv.q_w1 i0) _ _).trans (update_of_ne (hv.q_w0 i0) _
        _)).trans hq0
      have hsum1 : (∑ i : Fin R, βm (w1 i)) = 1 := (Finset.sum_eq_single i0 (fun i _ hi ↦
        ((update_of_ne (hv.w1_inj.ne hi) _ _).trans (update_of_ne (hv.w01_ne i0 i).symm _ _)).trans
        (hw1_0 i)) (fun h ↦ absurd (Finset.mem_univ i0) h)).trans (update_self (w1 i0) 1 _)
      refine ⟨βm, hq0 ▸ update_eq_self q β, hqm ▸ update_eq_self q βm, cswapRange_oneHot
        hv.toWPairDisj β i0 hw1_0 hw0_1 hw0_0, ?_, ?_, ?_⟩
      · rw [show cPre = _ from rfl, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec,
          ket_ctrlH_pair, hx0, ite_eq_right zero_ne_one, ket_wSplitSeq_oneHot R w0 w1 hv.w0_inj
          hv.w1_inj hv.w01_ne β i0 hw1_0 hw0_1 hw0_0, show update (update β (w0 i0) 0) (w1 i0) 1 =
          βm from rfl]
        simp only [mulVec_add, mulVec_smul, ket_cnotToTargetSeq, hsum0, hsum1, hq0, hqm, zero_add,
          ket_CNOT, update_of_ne hv.q_ctrl.symm, update_self, update_idem, show βm ctrl = β ctrl
          from (update_of_ne (hv.ctrl_w1 i0) _ _).trans (update_of_ne (hv.ctrl_w0 i0) _ _)]
      · rw [show cSw = _ from rfl, ket_swap3Seq_single R w0 w1 hv.w0_inj hv.w1_inj hv.w01_ne β i0
          hw0_0 fun i _ ↦ hw1_0 i, hw1_0 i0, hw0_1, show update (update β (w0 i0) 0) (w1 i0) 1 = βm
          from rfl]
      · rw [show cSw = _ from rfl, ket_swap3Seq_single R w0 w1 hv.w0_inj hv.w1_inj hv.w01_ne βm i0
          (fun i hi ↦ ((update_of_ne (hv.w01_ne i i0) _ _).trans (update_of_ne (hv.w0_inj.ne hi) _
          _)).trans (hw0_0 i hi)) (fun i hi ↦ ((update_of_ne (hv.w1_inj.ne hi) _ _).trans
          (update_of_ne (hv.w01_ne i0 i).symm _ _)).trans (hw1_0 i))]
        congr 1
        funext u
        by_cases h1 : u = w1 i0 <;> by_cases h0 : u = w0 i0 <;>
          simp [βm, hv.w01_ne i0 i0, hw1_0 i0, *]
    · rw [hx1, ite_eq_right one_ne_zero] at hCases
      let β1 := update β q 1
      have hw0_b1 (i : Fin R) : β1 (w0 i) = 0 := (update_of_ne (hv.q_w0 i).symm _ _).trans (hCases
        i)
      have hw1_b1 (i : Fin R) : β1 (w1 i) = 0 := (update_of_ne (hv.q_w1 i).symm _ _).trans (hw1_0 i)
      have hSw0 := ket_swap3Seq_all_zero R w0 w1 (fun i ↦ hv.w01_ne i i) β hCases hw1_0
      have hCs0 : cswapRangeBits R ctrl w0 w1 β = if β ctrl = 1 then β else β := by
        by_cases hc : β ctrl = 1
        · funext u
          simp only [cswapRangeBits, hc, ↓reduceIte]
          split_ifs with h0 h1
          exacts [by rw [hw1_0, h0.choose_spec, hCases], by rw [hCases, h1.choose_spec, hw1_0], rfl]
        · simp only [cswapRangeBits, ite_eq_right hc]
      refine ⟨β, hq0 ▸ update_eq_self q β, hq0 ▸ update_eq_self q β, hCs0, ?_, hSw0, hSw0⟩
      rw [show cPre = _ from rfl, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, ket_ctrlH_pair,
        hx1, ite_eq_left rfl, ket_H, hq0]
      simp only [bitSign, ↓reduceIte, one_smul, show update β q 0 = β from hq0 ▸ update_eq_self q β,
        show update β q 1 = β1 from rfl, mulVec_add, mulVec_smul, smul_add, ket_wSplitSeq_all_zero R
        w0 w1 (fun i ↦ hv.w01_ne i i) β hCases hw1_0, ket_wSplitSeq_all_zero R w0 w1 (fun i ↦
        hv.w01_ne i i) β1 hw0_b1 hw1_b1, ket_cnotToTargetSeq, hsum0, Finset.sum_eq_zero fun i _ ↦
        hw1_b1 i, add_zero]
      simp only [β1, ket_CNOT, hq0, zero_add, update_self, update_idem, update_of_ne hv.q_ctrl.symm]
  have hToff := Nat.add_eq_zero_iff.mp ((count_mbu v q cPre _ .TOFF).symm.trans (dWGated_toff v R wx
    ctrl w0 w1 q hv hxo7))
  refine BijectiveTransRealizes.of_measureZ1AndBranch v q cPre (Circuit.X q ;;ᶜ cSw) hToff.1 hToff.2
    S (BijectiveBitMap.ofInvolutive (cswapRangeBits R ctrl w0 w1) (cswapRangeBits_involutive
    hv.toWPairDisj)) (fun β hS ↦ ?_) (fun β hS ↦ ?_)
  · obtain ⟨βt, h0β, h0t, hcswap, hcPre, _⟩ := hSplit β hS
    dsimp only [BijectiveBitMap.ofInvolutive]
    rw [hcswap, ← mulVec_mulVec, hcPre,
      mulVec_add, mulVec_smul, mulVec_smul, singleton_projector_zero_mulVec_ket,
      singleton_projector_zero_mulVec_ket]
    rcases bit_cases (β ctrl) with hc | hc <;>
      simp only [hc, add_zero, zero_add, one_add_one_zmod2, update_self, one_ne_zero, zero_ne_one,
        ↓reduceIte, smul_zero, h0β, h0t]
  · obtain ⟨βt, h0β, h0t, hcswap, hcPre, hSw0, hSw1⟩ := hSplit β hS
    dsimp only [BijectiveBitMap.ofInvolutive]
    rw [hcswap, mul_assoc, ←
      mulVec_mulVec, ← mulVec_mulVec, hcPre, mulVec_add, mulVec_smul, mulVec_smul,
      singleton_projector_one_mulVec_ket, singleton_projector_one_mulVec_ket]
    rcases bit_cases (β ctrl) with hc | hc <;>
      simp only [hc, add_zero, zero_add, one_add_one_zmod2, update_self, zero_ne_one, ↓reduceIte,
        smul_zero, mulVec_smul, eval_seq_mulVec, ket_X, update_idem, h0β, h0t, hSw0, hSw1]
/-- Local `152`-wire `xo7` control wire (`0`). -/
abbrev wXo7Loc : Wire 152 := ⟨0, by decide⟩
/-- Local `152`-wire `b` address wire (`1..5`). -/
abbrev bWireLoc (j : Fin 5) : Wire 152 := ⟨1 + j.val, by omega⟩
/-- Local `152`-wire `128`-bit `rHot` block (`6..133`). -/
abbrev rHot152 : QRegister 128 152 := block 6 128 (by decide)
/-- Local `152`-wire `16`-leaf unary scratch wire (`134..149`). -/
abbrev uLeaf (c : Fin 16) : Wire 152 := ⟨134 + c.val, by omega⟩
/-- Local `152`-wire reusable parity/target ancilla (`150`). -/
abbrev wEnc : Wire 152 := ⟨150, by decide⟩
/-- Local `152`-wire clean parity scratch ancilla (`151`). -/
abbrev wAux : Wire 152 := ⟨151, by decide⟩
theorem pow2_lt4 (d : ℕ) (hd : d < 4) : 2 ^ d ≤ 8 := by interval_cases d <;> decide
theorem wire_ne {n : ℕ} {u : Wire n} {b : ℕ} {hb : b < n} (h : u.val ≠ b) : u ≠ ⟨b, hb⟩ :=
  Fin.ne_of_val_ne h
/-- Level-`d` (`d < 4`, `R = 2 ^ d`) left leaf wire `uLeaf i`. -/
abbrev treeW0 (d : ℕ) (hd : d < 4) (i : Fin (2 ^ d)) : Wire 152 := uLeaf ⟨i.val, Nat.lt_of_lt_of_le
  i.isLt (Nat.le_trans (pow2_lt4 d hd) (by decide))⟩
/-- Level-`d` (`d < 4`, `R = 2 ^ d`) right leaf wire `uLeaf (2 ^ d + i)`. -/
abbrev treeW1 (d : ℕ) (hd : d < 4) (i : Fin (2 ^ d)) : Wire 152 := uLeaf ⟨2 ^ d + i.val,
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (Nat.add_le_add (pow2_lt4 d hd) (pow2_lt4 d
  hd))⟩
theorem wSplitValid_tree (d : ℕ) (hd : d < 4) : WSplitValid (2 ^ d) (bWireLoc ⟨d, by omega⟩) (treeW0
  d hd) (treeW1 d hd) wEnc := by
  have hd8 := pow2_lt4 d hd
  exact ⟨⟨fun _ _ h ↦ Fin.ext (Nat.add_left_cancel (Fin.ext_iff.mp h)), fun _ _ h ↦ Fin.ext
    (Nat.add_left_cancel (Nat.add_left_cancel (Fin.ext_iff.mp h))), fun i j ↦ wire_ne
    (show 134 + i.val ≠ 134 + (2 ^ d + j.val) by omega), fun i ↦ wire_ne
    (show 1 + d ≠ 134 + i.val by omega), fun i ↦ wire_ne
    (show 1 + d ≠ 134 + (2 ^ d + i.val) by omega)⟩, wire_ne (show 150 ≠ 1 + d by omega), fun i ↦
    wire_ne (show 150 ≠ 134 + i.val by omega), fun i ↦ wire_ne
    (show 150 ≠ 134 + (2 ^ d + i.val) by omega)⟩
/-- Reversible `RevCompute 152` prefix through `d ≤ 4` levels of `!wXo7`-gated `16`-leaf tree. -/
def pTreeLevels : (d : ℕ) → d ≤ 4 → GroupUnary.RevCompute 152
  | 0, _ => .seq (.cnot wXo7Loc (uLeaf 0) (by decide)) (.x (uLeaf 0))
  | d + 1, hd => .seq (pTreeLevels d (by omega)) (splitRevLoop (bWireLoc ⟨d, by omega⟩) (2 ^ d)
      (treeW0 d hd) (treeW1 d hd) (wSplitValid_tree d hd).toWPairDisj)
/-- Full `15`-AND reversible `16`-leaf decoder (`0`-`T` MBU uncomputation via `revUncomputeDyn`). -/
abbrev pTree16 : GroupUnary.RevCompute 152 := pTreeLevels 4 le_rfl
/-- Dynamic `!wXo7`-gated W-split tree through `d ≤ 4` levels (`38 T`, `0 TOFF` at `d = 4`). -/
def dTreeLevels {Var : Type} (v : Var) : (d : ℕ) → d ≤ 4 → DynamicCircuit Var 152
  | 0, _ => revComputeDyn (.seq (.cnot wXo7Loc (uLeaf 0) (by decide)) (.x (uLeaf 0)))
  | d + 1, hd => .seq (dTreeLevels v d (by omega)) (dWGated v (2 ^ d) wXo7Loc
      (bWireLoc ⟨d, by omega⟩) (treeW0 d hd) (treeW1 d hd) wEnc (wSplitValid_tree d hd) (by decide))
/-- Clean `18`-wire scratch predicate (`134..151` all zero) on `BitAssignment 152`. -/
def sClean18 (β : BitAssignment 152) : Bool := decide (∀ j : Fin 18, β ⟨134 + j.val, by omega⟩ = 0)
/-- `d`-bit prefix address `b[0..d-1]` (`d ≤ 4`) on `BitAssignment 152`. -/
noncomputable def bSub (d : ℕ) (hd : d ≤ 4) (β : BitAssignment 152) : Fin (2 ^ d) := (basisBits
  d).symm fun i ↦ β ⟨1 + i.val, by omega⟩
/-- Level-`d` post-condition of `pTreeLevels d hd` on `BitAssignment 152`. -/
def TreeProp (d : ℕ) (hd : d ≤ 4) (γ : BitAssignment 152) : Prop := γ wEnc = 0 ∧ γ wAux = 0 ∧ ∀ c :
  Fin 16, γ (uLeaf c) = if γ wXo7Loc = 0 ∧ c.val = (bSub d hd γ).val then 1 else 0
theorem pTreeLevels_spec {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) : ∀ (d : ℕ) (hd : d
  ≤ 4), EquivRev v sClean18 (pTreeLevels d hd) (dTreeLevels v d hd) ∧ ∀ β : BitAssignment 152,
  sClean18 β = true → (∀ w : Wire 152, w.val < 134 → (pTreeLevels d hd).fwdBits β w = β w) ∧
  TreeProp d hd ((pTreeLevels d hd).fwdBits β)
  | 0, hd => by
      refine ⟨EquivRev.ofRevCompute v sClean18 _ fun _ _ ↦ rfl, fun β hβ ↦ ?_⟩
      have hClean : ∀ j : Fin 18, β ⟨134 + j.val, by omega⟩ = 0 := by
        unfold sClean18 at hβ
        have h := of_decide_eq_true hβ
        exact h
      have hγ : (pTreeLevels 0 hd).fwdBits β = update β (uLeaf 0) (β wXo7Loc + 1) := by
        dsimp only [pTreeLevels, GroupUnary.RevCompute.fwdBits]
        rw [update_self, update_idem, show β (uLeaf 0) = 0 from hClean ⟨0, by decide⟩, zero_add]
      refine ⟨fun w hw ↦ by rw [hγ, update_of_ne (wire_ne (by omega))],
        ((congrFun hγ wEnc).trans (update_of_ne (by decide) _ _)).trans (hClean ⟨16, by decide⟩),
        ((congrFun hγ wAux).trans (update_of_ne (by decide) _ _)).trans (hClean ⟨17, by decide⟩),
        fun c ↦ ?_⟩
      rw [Nat.lt_one_iff.mp (bSub 0 hd _).isLt, hγ, update_of_ne (by decide : wXo7Loc ≠ uLeaf 0)]
      by_cases hc0 : c.val = 0
      · rw [show c = 0 from Fin.ext hc0, update_self]
        rcases bit_cases (β wXo7Loc) with hx | hx
        exacts [(by rw [hx, zero_add, ite_eq_left ⟨rfl, rfl⟩]),
          (by rw [hx, one_add_one_zmod2, ite_eq_right fun h ↦ one_ne_zero h.1])]
      · simp [hc0, hClean ⟨c.val, by omega⟩,
          show uLeaf c ≠ uLeaf 0 from wire_ne (show 134 + c.val ≠ 134 by omega)]
  | d + 1, hd => by
      have hd8 := pow2_lt4 d hd
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := (pow_succ 2 d).trans (Nat.mul_two _)
      obtain ⟨heq_d, hspec_d⟩ := pTreeLevels_spec v d (by omega)
      let pd := pTreeLevels d (by omega)
      let hv := wSplitValid_tree d hd
      have hInv_d : ∀ γ, sClean18 (pd.invBits γ) = true → InvWGated (2 ^ d) wXo7Loc (treeW0 d hd)
        (treeW1 d hd) wEnc γ := fun γ hγ ↦ by
        obtain ⟨hEnc, _, hLeaves⟩ := pd.fwdBits_invBits γ ▸ (hspec_d (pd.invBits γ) hγ).2
        refine ⟨hEnc, fun i ↦ (hLeaves _).trans (ite_eq_right fun ⟨_, he⟩ ↦ absurd he (Nat.ne_of_gt
          (Nat.lt_of_lt_of_le (bSub d (by omega) γ).isLt (Nat.le_add_right _ _)))), ?_⟩
        split_ifs with hx
        exacts [⟨bSub d (by omega) γ, (hLeaves _).trans (ite_eq_left ⟨hx, rfl⟩), fun i hi ↦ (hLeaves
          _).trans (ite_eq_right fun ⟨_, he⟩ ↦ hi (Fin.ext he))⟩, fun i ↦ (hLeaves _).trans
          (ite_eq_right fun ⟨hx0, _⟩ ↦ hx hx0)]
      refine ⟨heq_d.seq (EquivRev.dWGated v (2 ^ d) wXo7Loc (bWireLoc ⟨d, by omega⟩) (treeW0 d hd)
        (treeW1 d hd) wEnc hv (by decide) (fun γ ↦ sClean18 (pd.invBits γ)) hInv_d), fun β hβ ↦ ?_⟩
      obtain ⟨hLow_d, hEnc, hAux, hLv⟩ := hspec_d β hβ
      let γ := pd.fwdBits β
      rw [show (pTreeLevels d (by omega)).fwdBits β = γ from rfl] at hLv
      have hInvγ := hInv_d γ ((congrArg sClean18 (pd.invBits_fwdBits β)).trans hβ)
      let γ' := cswapRangeBits (2 ^ d) (bWireLoc ⟨d, by omega⟩) (treeW0 d hd) (treeW1 d hd) γ
      rw [pTreeLevels, GroupUnary.RevCompute.fwdBits, show (pTreeLevels d (by omega)).fwdBits β =
        γ from rfl, (splitRevLoop_spec _ _ _ _ hv.toWPairDisj γ hInvγ.2.1).2, show cswapRangeBits (2
        ^ d) (bWireLoc ⟨d, by omega⟩) (treeW0 d hd) (treeW1 d hd) γ = γ' from rfl]
      have hOther (w : Wire 152) (hw : w.val < 134 ∨ 134 + 2 ^ (d + 1) ≤ w.val) : γ' w = γ w :=
        cswapRangeBits_other γ (fun i ↦ wire_ne (show w.val ≠ 134 + i.val by omega)) fun i ↦
          wire_ne (show w.val ≠ 134 + (2 ^ d + i.val) by omega)
      refine ⟨fun w hw ↦ (hOther w (Or.inl hw)).trans (hLow_d w hw), (hOther wEnc (Or.inr
        (show 134 + 2 ^ (d + 1) ≤ 150 by omega))).trans hEnc, (hOther wAux (Or.inr
        (show 134 + 2 ^ (d + 1) ≤ 151 by omega))).trans hAux, fun c ↦ ?_⟩
      have hbSucc : (bSub (d + 1) hd γ).val = 2 ^ d * (if γ (bWireLoc ⟨d, by omega⟩) = 1 then 1 else
        0) + (bSub d (by omega) γ).val := (localIdx_succ_val (block 1 (d + 1) (by omega)) γ).trans
        (congrArg (· + _) (congrArg (2 ^ d * ·) (ite_congr rfl (fun _ ↦ rfl) (fun _ ↦ rfl))))
      rw [hOther wXo7Loc (Or.inl (by decide)), show bSub (d + 1) hd γ' = bSub (d + 1) hd γ from
        congrArg (basisBits (d + 1)).symm (funext fun i ↦ hOther _ (Or.inl
        (show 1 + i.val < 134 by omega))), hbSucc]
      have hIdxLt := (bSub d (by omega) γ).isLt
      by_cases hc1 : c.val < 2 ^ d
      · rw [show uLeaf c = treeW0 d hd ⟨c.val, hc1⟩ from rfl, show γ' _ = cswapRangeBits _ _ _ _ γ _
          from rfl, cswapRangeBits_w0 hv.toWPairDisj γ ⟨c.val, hc1⟩, hInvγ.2.1 ⟨c.val, hc1⟩, show
          treeW0 d hd ⟨c.val, hc1⟩ = uLeaf c from rfl, hLv c]
        rcases bit_cases (γ (bWireLoc ⟨d, by omega⟩)) with hb | hb
        exacts [by simp [hb], by simp [hb, show c.val ≠ 2 ^ d + (bSub d (by omega) γ).val by omega]]
      · by_cases hc2 : c.val < 2 ^ (d + 1)
        · have hjLt : c.val - 2 ^ d < 2 ^ d := by omega
          rw [show uLeaf c = treeW1 d hd ⟨c.val - 2 ^ d, hjLt⟩ from Fin.ext (congrArg (134 + ·)
            (Nat.add_sub_of_le (Nat.not_lt.mp hc1)).symm), show γ' _ = cswapRangeBits _ _ _ _ γ _
            from rfl, cswapRangeBits_w1 hv.toWPairDisj γ ⟨c.val - 2 ^ d, hjLt⟩, hInvγ.2.1 _, show
            treeW0 d hd ⟨c.val - 2 ^ d, hjLt⟩ = uLeaf ⟨c.val - 2 ^ d, by omega⟩ from rfl, hLv
            ⟨c.val - 2 ^ d, by omega⟩]
          rcases bit_cases (γ (bWireLoc ⟨d, by omega⟩)) with hb | hb
          exacts [by simp [hb, show c.val ≠ (bSub d (by omega) γ).val by omega], by simp [hb,
            show c.val - 2 ^ d = (bSub d (by omega) γ).val ↔ c.val = 2 ^ d + (bSub d (by omega)
            γ).val by omega]]
        · rw [hOther (uLeaf c) (Or.inr (show 134 + 2 ^ (d + 1) ≤ 134 + c.val by omega)), hLv c]
          rcases bit_cases (γ (bWireLoc ⟨d, by omega⟩)) with hcB | hcB
          exacts [by simp [hcB], by simp [hcB, show c.val ≠ (bSub d (by omega) γ).val by omega,
            show c.val ≠ 2 ^ d + (bSub d (by omega) γ).val by omega]]
theorem rHot152_ne_wAux (g : Fin 128) : rHot152 g ≠ wAux := wire_ne (show 6 + g.val ≠ 151 by omega)
theorem rHot152_ne_wEnc (g : Fin 128) : rHot152 g ≠ wEnc := wire_ne (show 6 + g.val ≠ 150 by omega)
/-- `0-T`, `0-TOFF` masked phase kick `(-1)^{γ u * maskSumBit rHot152 m γ}` via clean `wAux`. -/
def maskCz (u : Wire 152) (m : Fin 128 → Bool) (hu : u ≠ wAux) : Circuit 152 := cnotMaskReg 128
  rHot152 wAux m rHot152_ne_wAux ;;ᶜ czCircuit u wAux hu ;;ᶜ cnotMaskReg 128 rHot152 wAux m
  rHot152_ne_wAux
theorem ket_maskCz (u : Wire 152) (m : Fin 128 → Bool) (hu : u ≠ wAux) (γ : BitAssignment 152) (hAux
  : γ wAux = 0) : (maskCz u m hu).eval.1 *ᵥ SelectSwapQROM.ket γ = bitSign (γ u * maskSumBit
  rHot152 m γ) • SelectSwapQROM.ket γ := by
  let γ1 := update γ wAux (maskSumBit rHot152 m γ)
  have hs1 : maskSumBit rHot152 m γ1 = maskSumBit rHot152 m γ := Finset.sum_congr rfl fun g _ ↦
    congrArg (if m g then · else 0) (update_of_ne (rHot152_ne_wAux g) _ _)
  have hket : UnsignedGivens.ket = (SelectSwapQROM.ket : BitAssignment 152 → _) := rfl
  rw [maskCz, eval_seq_mulVec, eval_seq_mulVec, ← hket, evolve_cnotMaskReg_ket, hket, hAux,
    zero_add, show update γ wAux (maskSumBit rHot152 m γ) = γ1 from rfl, ket_czCircuit, show γ1 u =
    γ u from update_of_ne hu _ _, show γ1 wAux = maskSumBit rHot152 m γ from update_self _ _ _,
    mulVec_smul, ← hket, evolve_cnotMaskReg_ket, hket, show γ1 wAux = maskSumBit rHot152 m γ from
    update_self _ _ _, hs1, CharTwo.add_self_eq_zero, show γ1 = update γ wAux (maskSumBit rHot152 m
    γ) from rfl, update_idem, ← hAux, update_eq_self]
theorem ket_cMaskSeq : ∀ (R : ℕ) (u : Fin R → Wire 152) (tbl : Fin R → Fin 128 → Bool) (hu : ∀ k, u
  k ≠ wAux) (γ : BitAssignment 152), γ wAux = 0 → (wSeqFin R fun k ↦ maskCz (u k) (tbl k) (hu
  k)).eval.1 *ᵥ SelectSwapQROM.ket γ = bitSign (∑ k : Fin R, γ (u k) * maskSumBit rHot152 (tbl k)
  γ) • SelectSwapQROM.ket γ
  | 0, _, _, _, γ, _ => by
      simp only [wSeqFin, Finset.univ_eq_empty, Finset.sum_empty, bitSign, ↓reduceIte, one_smul]
      exact one_mulVec (SelectSwapQROM.ket γ)
  | R + 1, u, tbl, hu, γ, hAux => by
      rw [wSeqFin, eval_seq_mulVec, ket_maskCz (u 0) (tbl 0) (hu 0) γ hAux, mulVec_smul,
        ket_cMaskSeq R (fun k ↦ u k.succ) (fun k ↦ tbl k.succ) (fun k ↦ hu k.succ) γ hAux,
        smul_smul, ← bitSign_add, Fin.sum_univ_succ]
theorem uLeaf_ne_wAux (c : Fin 16) : uLeaf c ≠ wAux := wire_ne (show 134 + c.val ≠ 151 by omega)
@[simp] theorem cMaskSeq_toff (R : ℕ) (u : Fin R → Wire 152) (tbl : Fin R → Fin 128 → Bool)
    (hu : ∀ k, u k ≠ wAux) : (wSeqFin R fun k ↦ maskCz (u k) (tbl k) (hu k)).count .TOFF = 0 :=
  wSeqFin_count_eq_zero .TOFF R _ fun _ ↦ by simp [maskCz, count_czCircuit_toff]
@[simp] theorem cMaskSeq_t (R : ℕ) (u : Fin R → Wire 152) (tbl : Fin R → Fin 128 → Bool)
    (hu : ∀ k, u k ≠ wAux) : (wSeqFin R fun k ↦ maskCz (u k) (tbl k) (hu k)).count .T = 0 :=
  wSeqFin_count_eq_zero .T R _ fun _ ↦ by simp [maskCz, count_czCircuit_t]
theorem sqrtHalf_sq_sr : sqrtHalf ^ 2 = 1 / 2 := by rw [sq, sqrtHalf_mul_sqrtHalf]
/-- Phase `ω_8^b` (`b : ZMod 2`). -/
noncomputable abbrev pT (b : ZMod 2) : ℂ := if b = 0 then 1 else omega8_145
/-- Conjugate phase `ω_8^{-b}` (`b : ZMod 2`). -/
noncomputable def pTD (b : ZMod 2) : ℂ := if b = 0 then 1 else (1 - Complex.I) * sqrtHalf
/-- Branch sign `(∓i)^d` (`d, w : ZMod 2`) in the Hadamard inner-product loop. -/
noncomputable def sgnI (d w : ZMod 2) : ℂ := if d = 0 then 1 else if w = 0 then -Complex.I else
  Complex.I
/-- Single-qubit `T† = Z ;; S ;; T` (`1 T`, `0 TOFF`). -/
def tDagSr {n : ℕ} (q : Wire n) : Circuit n := Circuit.Z q ;;ᶜ Circuit.S q ;;ᶜ Circuit.T q
@[simp] theorem tDagSr_toff {n : ℕ} (q : Wire n) : (tDagSr q).count .TOFF = 0 := rfl
@[simp] theorem tDagSr_t {n : ℕ} (q : Wire n) : (tDagSr q).count .T = 1 := rfl
theorem ket_tDag {n : ℕ} (q : Wire n) (β : BitAssignment n) : (tDagSr q).eval.1 *ᵥ
  SelectSwapQROM.ket β = pTD (β q) • SelectSwapQROM.ket β := by
  have hs : XMeasCircuit.sqrtHalf = sqrtHalf := rfl
  simp only [tDagSr, eval_seq_mulVec, ket_Z, ket_S_145, ket_T_145, mulVec_smul, smul_smul]
  congr 1
  rcases bit_cases (β q) with hb | hb
  · simp [hb, bitSign, pTD]
  · simp only [hb, one_ne_zero, ↓reduceIte, bitSign, pTD, omega8_145_eq, hs]
    ring_nf
    simp only [Complex.I_sq]
    ring
theorem lempel_phase (w p u v d : ZMod 2) (hpu : ¬ (p = 1 ∧ u = 1)) (hdp : d = 1 → p = 1) : pT (w +
  p) * sgnI d w * pTD (w + p + v) * pT (w + p + v + u) = pT (w + (p + u)) * sgnI (d + u * v) w := by
  have hs : XMeasCircuit.sqrtHalf = sqrtHalf := rfl
  have hs3 : sqrtHalf ^ 3 = sqrtHalf / 2 := by linear_combination sqrtHalf * sqrtHalf_sq_sr
  have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * Complex.I_sq
  have hI4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq
  rcases bit_cases p with rfl | rfl <;> rcases bit_cases u with rfl | rfl <;>
    rcases bit_cases d with rfl | rfl <;>
    (try exact absurd (hdp rfl) zero_ne_one) <;> (try exact absurd ⟨rfl, rfl⟩ hpu) <;>
    rcases bit_cases w with rfl | rfl <;> rcases bit_cases v with rfl | rfl <;>
    simp only [add_zero, zero_add, one_mul, mul_zero, mul_one, one_add_one_zmod2, pT, pTD, sgnI,
      omega8_145_eq, hs, one_ne_zero, ↓reduceIte] <;>
    ring_nf <;> simp only [hs3, sqrtHalf_sq_sr, hI4, hI3, Complex.I_sq] <;> ring
theorem uLeaf_ne_wEnc (c : Fin 16) : uLeaf c ≠ wEnc := wire_ne (show 134 + c.val ≠ 150 by omega)
/-- Single `2-T`, `0-TOFF` step `k < 14` of the Hadamard inner-product loop on `wEnc`. -/
def lempelStep (k : Fin 14) : Circuit 152 := cnotMaskReg 128 rHot152 wEnc (deltaTable k)
  rHot152_ne_wEnc ;;ᶜ tDagSr wEnc ;;ᶜ Circuit.CNOT (uLeaf ⟨k.val, by omega⟩) wEnc (uLeaf_ne_wEnc _)
  ;;ᶜ Circuit.T wEnc ;;ᶜ cnotMaskReg 128 rHot152 wEnc (deltaTable k) rHot152_ne_wEnc
/-- Prefix `m ≤ 14` (`2 * m` `T`, `0 TOFF`) of `lempelStep`s. -/
def lempelLoop : (m : ℕ) → m ≤ 14 → Circuit 152
  | 0, _ => .identity
  | m + 1, hm => lempelLoop m (by omega) ;;ᶜ lempelStep ⟨m, hm⟩
/-- `30-T`, `0-TOFF` Hadamard inner-product gadget computing `∑_{k<14} u_k * v_k` into `wEnc`. -/
def cLempel14 : Circuit 152 := Circuit.H wEnc ;;ᶜ Circuit.T wEnc ;;ᶜ lempelLoop 14 le_rfl ;;ᶜ tDagSr
  wEnc ;;ᶜ wSeqFin 14 (fun k ↦ Circuit.CNOT (uLeaf ⟨k.val, by omega⟩) wEnc (uLeaf_ne_wEnc _)) ;;ᶜ
  Circuit.H wEnc ;;ᶜ Circuit.S wEnc
@[simp] theorem lempelLoop_toff : ∀ (m : ℕ) (hm : m ≤ 14), (lempelLoop m hm).count .TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by simp [lempelLoop, lempelStep, lempelLoop_toff m (by omega)]
@[simp] theorem lempelLoop_t : ∀ (m : ℕ) (hm : m ≤ 14), (lempelLoop m hm).count .T = 2 * m
  | 0, _ => rfl
  | m + 1, hm => by simp [lempelLoop, lempelStep, lempelLoop_t m (by omega), Nat.mul_succ]
@[simp] theorem cLempel14_toff : cLempel14.count .TOFF = 0 := by
  rw [cLempel14]
  repeat rw [Circuit.count_seq]
  rw [lempelLoop_toff, tDagSr_toff, wSeqFin_count_eq_zero .TOFF 14 (fun k ↦ Circuit.CNOT (uLeaf
    ⟨k.val, by omega⟩) wEnc (uLeaf_ne_wEnc _)) fun _ ↦ rfl]
  rfl
@[simp] theorem cLempel14_t : cLempel14.count .T = 30 := by
  rw [cLempel14]
  repeat rw [Circuit.count_seq]
  rw [lempelLoop_t, tDagSr_t, wSeqFin_count_eq_zero .T 14 (fun k ↦ Circuit.CNOT (uLeaf
    ⟨k.val, by omega⟩) wEnc (uLeaf_ne_wEnc _)) fun _ ↦ rfl]
  rfl
/-- At-most-one-hot invariant on the first `14` unary leaves `uLeaf 0..13`. -/
def AtMostOneHot14 (γ : BitAssignment 152) : Prop := ∀ j k : Fin 14, γ (uLeaf ⟨j.val, by omega⟩) = 1
  → γ (uLeaf ⟨k.val, by omega⟩) = 1 → j = k
/-- Prefix parity `∑_{j < m} γ (uLeaf j)` (`m ≤ 14`). -/
def lPar (m : ℕ) (hm : m ≤ 14) (γ : BitAssignment 152) : ZMod 2 := ∑ j : Fin m, γ (uLeaf
  ⟨j.val, by omega⟩)
/-- Prefix inner product `∑_{j < m} γ (uLeaf j) * maskSumBit rHot152 (deltaTable j) γ`. -/
noncomputable def lDot (m : ℕ) (hm : m ≤ 14) (γ : BitAssignment 152) : ZMod 2 := ∑ j : Fin m, γ
  (uLeaf ⟨j.val, by omega⟩) * maskSumBit rHot152 (deltaTable ⟨j.val, by omega⟩) γ
theorem lempel_prefix_props {γ : BitAssignment 152} (h1 : AtMostOneHot14 γ) (m : ℕ) (hm : m < 14) :
  ¬ (lPar m (by omega) γ = 1 ∧ γ (uLeaf ⟨m, by omega⟩) = 1) ∧ (lDot m (by omega) γ = 1 → lPar m
  (by omega) γ = 1) := by
  by_cases hex : ∃ j : Fin m, γ (uLeaf ⟨j.val, by omega⟩) = 1
  · obtain ⟨j0, hj0⟩ := hex
    refine ⟨fun ⟨_, hu⟩ ↦ absurd (show j0.val = m from congrArg Fin.val (h1 ⟨j0.val, by omega⟩ ⟨m,
      hm⟩ hj0 hu)) (Nat.ne_of_lt j0.isLt), fun _ ↦ (Finset.sum_eq_single j0 (fun i _ hij ↦ ?_) fun h
      ↦ absurd (Finset.mem_univ j0) h).trans hj0⟩
    rcases bit_cases (γ (uLeaf ⟨i.val, by omega⟩)) with hi0 | hi1
    exacts [hi0, absurd (Fin.ext (show i.val = j0.val from congrArg (Fin.val : Fin 14 → ℕ) (h1
      ⟨i.val, by omega⟩ ⟨j0.val, by omega⟩ hi1 hj0))) hij]
  · have h0 (j : Fin m) : γ (uLeaf ⟨j.val, by omega⟩) = 0 := (bit_cases _).resolve_right fun h ↦ hex
      ⟨j, h⟩
    exact ⟨fun ⟨hp, _⟩ ↦ one_ne_zero (hp.symm.trans (Finset.sum_eq_zero fun j _ ↦ h0 j)), fun hd ↦
      absurd (hd.symm.trans (Finset.sum_eq_zero fun j _ ↦ by rw [h0 j, zero_mul])) one_ne_zero⟩
theorem ket_lempelStep (k : Fin 14) (γ : BitAssignment 152) (z : ZMod 2) : (lempelStep k).eval.1 *ᵥ
  SelectSwapQROM.ket (update γ wEnc z) = (pTD (z + maskSumBit rHot152 (deltaTable k) γ) * pT (z +
  maskSumBit rHot152 (deltaTable k) γ + γ (uLeaf ⟨k.val, by omega⟩))) • SelectSwapQROM.ket (update
  γ wEnc (z + γ (uLeaf ⟨k.val, by omega⟩))) := by
  let u := γ (uLeaf ⟨k.val, by omega⟩)
  let v := maskSumBit rHot152 (deltaTable k) γ
  have hket : UnsignedGivens.ket = (SelectSwapQROM.ket : BitAssignment 152 → _) := rfl
  have hkS : XMeasCircuit.ket = (UnsignedGivens.ket : BitAssignment 152 → _) := rfl
  have hmask (a : ZMod 2) : maskSumBit rHot152 (deltaTable k) (update γ wEnc a) = v :=
    Finset.sum_congr rfl fun g _ ↦ congrArg (if deltaTable k g then · else 0) (update_of_ne
    (rHot152_ne_wEnc g) _ _)
  have hzv : z + v + u + v = z + u := by
    rw [show z + v + u + v = z + u + (v + v) by ring, CharTwo.add_self_eq_zero, add_zero]
  rw [lempelStep, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, ← hket,
    evolve_cnotMaskReg_ket, hket, update_self, hmask z, update_idem, ket_tDag, update_self,
    mulVec_smul, ket_CNOT, update_self, update_of_ne (uLeaf_ne_wEnc _), show γ (uLeaf
    ⟨k.val, by omega⟩) = u from rfl, update_idem, mulVec_smul, ket_T_145, update_self, mulVec_smul,
    mulVec_smul, hkS, evolve_cnotMaskReg_ket, hket, update_self, hmask (z + v + u), update_idem,
    hzv, smul_smul]
theorem ket_lempelLoop (γ : BitAssignment 152) (h1 : AtMostOneHot14 γ) (w : ZMod 2) : ∀ (m : ℕ) (hm
  : m ≤ 14), (Circuit.T wEnc ;;ᶜ lempelLoop m hm).eval.1 *ᵥ SelectSwapQROM.ket (update γ wEnc w) =
  (pT (w + lPar m hm γ) * sgnI (lDot m hm γ) w) • SelectSwapQROM.ket (update γ wEnc (w + lPar m hm
  γ))
  | 0, hm => by
      simp only [lempelLoop, eval_seq_mulVec, ket_T_145, update_self, Circuit.eval_identity,
        Submonoid.coe_one, one_mulVec, lPar, lDot, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
        sgnI, ↓reduceIte, mul_one]
  | m + 1, hm => by
      obtain ⟨hpu, hdp⟩ := lempel_prefix_props h1 m (by omega)
      have ih := ket_lempelLoop γ h1 w m (by omega)
      rw [eval_seq_mulVec] at ih
      rw [lempelLoop, eval_seq_mulVec, eval_seq_mulVec, ih, mulVec_smul, ket_lempelStep, smul_smul,
        show lPar (m + 1) hm γ = lPar m (by omega) γ + γ (uLeaf ⟨m, by omega⟩) from
        Fin.sum_univ_castSucc _, show lDot (m + 1) hm γ = lDot m (by omega) γ + γ (uLeaf
        ⟨m, by omega⟩) * maskSumBit rHot152 (deltaTable ⟨m, hm⟩) γ from Fin.sum_univ_castSucc _, ←
        add_assoc w, ← mul_assoc, lempel_phase w (lPar m (by omega) γ) (γ (uLeaf ⟨m, by omega⟩))
        (maskSumBit rHot152 (deltaTable ⟨m, hm⟩) γ) (lDot m (by omega) γ) hpu hdp, add_assoc w]
theorem ket_cLempel14 (γ : BitAssignment 152) (hEnc : γ wEnc = 0) (h1 : AtMostOneHot14 γ) :
  cLempel14.eval.1 *ᵥ SelectSwapQROM.ket γ = SelectSwapQROM.ket (update γ wEnc (lDot 14 le_rfl
  γ)) := by
  let p14 := lPar 14 le_rfl γ
  let d14 := lDot 14 le_rfl γ
  have hs : XMeasCircuit.sqrtHalf = sqrtHalf := rfl
  have hCancel (x : ZMod 2) : pT x * pTD x = 1 := by
    rcases bit_cases x with rfl | rfl
    · simp [pT, pTD]
    · simp only [one_ne_zero, ↓reduceIte, pT, pTD, omega8_145_eq, hs]
      ring_nf
      simp only [sqrtHalf_sq_sr, Complex.I_sq]
      ring
  have hUnpar (w : ZMod 2) : (tDagSr wEnc ;;ᶜ wSeqFin 14 fun k ↦ Circuit.CNOT (uLeaf
    ⟨k.val, by omega⟩) wEnc (uLeaf_ne_wEnc _)).eval.1 *ᵥ ((Circuit.T wEnc ;;ᶜ lempelLoop 14
    le_rfl).eval.1 *ᵥ SelectSwapQROM.ket (update γ wEnc w)) = sgnI d14 w • SelectSwapQROM.ket
    (update γ wEnc w) := by
    rw [ket_lempelLoop γ h1 w 14 le_rfl, show lPar 14 le_rfl γ = p14 from rfl, show lDot 14 le_rfl γ
      = d14 from rfl, eval_seq_mulVec, mulVec_smul, mulVec_smul, ket_tDag, update_self, mulVec_smul,
      ket_cnotToTargetSeq, update_self, show (∑ i : Fin 14, update γ wEnc (w + p14) (uLeaf
      ⟨i.val, by omega⟩)) = p14 from Finset.sum_congr rfl fun k _ ↦ update_of_ne (uLeaf_ne_wEnc _) _
      _, update_idem, show w + p14 + p14 = w by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero],
      smul_smul, show pT (w + p14) * sgnI d14 w * pTD (w + p14) = (pT (w + p14) * pTD (w + p14)) *
      sgnI d14 w by ring, hCancel, one_mul]
  simp only [eval_seq_mulVec] at hUnpar
  simp only [cLempel14, eval_seq_mulVec]
  rw [show lDot 14 le_rfl γ = d14 from rfl, ket_H, hEnc, show bitSign 0 = 1 from rfl, one_smul]
  simp only [mulVec_add, mulVec_smul, hUnpar 0, hUnpar 1, ket_H, update_self, update_idem, bitSign,
    one_ne_zero, ↓reduceIte, one_smul, ket_S_145]
  rcases bit_cases d14 with hd | hd <;> ext i <;>
    simp only [hd, sgnI, one_ne_zero, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring_nf <;> simp only [sqrtHalf_sq_sr, Complex.I_sq] <;> ring
theorem phaseFlipU_comm_diag {n : ℕ} (f : BitAssignment n → ZMod 2) (d : Fin (2 ^ n) → ℂ) :
  (phaseFlipUnitary f).1 * diagonal d = diagonal d * (phaseFlipUnitary f).1 := by
  simp only [phaseFlipUnitary_val, diagonal_mul_diagonal, mul_comm]
theorem tr_mbu_phaseFlip {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var) (q : Wire n)
  (cPre cFix : Circuit n) (htoffPre : cPre.count .TOFF = 0) (htoffFix : cFix.count .TOFF = 0) (S :
  BitAssignment n → Bool) (f : BitAssignment n → ZMod 2) (hL0 : ∀ β, S β = true →
  ((QRegister.singleton q).basisOutcomeProjector 0 * cPre.eval.1) *ᵥ SelectSwapQROM.ket β =
  (sqrtHalf * bitSign (f β)) • SelectSwapQROM.ket β) (hL1 : ∀ β, S β = true → (cFix.eval.1 *
  (QRegister.singleton q).basisOutcomeProjector 1 * cPre.eval.1) *ᵥ SelectSwapQROM.ket β =
  (sqrtHalf * bitSign (f β)) • SelectSwapQROM.ket β) : TransRealizes v S S (phaseFlipUnitary f)
  (measureZ1AndBranch v q cPre cFix) where
  toff_zero := by rw [count_mbu, htoffPre, htoffFix]
  map_proj := phaseFlipU_comm_diag f _
  update_self Θ _ σ _ := Subtype.ext (by simp [wp_measureZ1AndBranch_apply_assertion, update_idem])
  wp_eq Θ hΘ := by
    let U := phaseFlipUnitary f
    have hAdj (M : Operator (2 ^ n)) (hM : ∀ β, S β = true → M *ᵥ SelectSwapQROM.ket β = (sqrtHalf
      * bitSign (f β)) • SelectSwapQROM.ket β) : predProj S * Mᴴ = (sqrtHalf • (U.1 * predProj
      S))ᴴ := by
      have hEq : M * predProj S = sqrtHalf • (U.1 * predProj S) :=
        SelectSwapQROM.matrix_ext_ket fun β ↦ by
          rw [smul_mulVec, ← mulVec_mulVec (SelectSwapQROM.ket β) M, ← mulVec_mulVec
            (SelectSwapQROM.ket β) U.1, predProj_mulVec_ket]
          by_cases hS : S β = true
          · rw [ite_eq_left hS, hM β hS, show SelectSwapQROM.ket β = XMeasCircuit.ket β from rfl,
              show U = phaseFlipUnitary f from rfl, phaseFlipUnitary_mulVec_ket, smul_smul]
          · rw [ite_eq_right hS, mulVec_zero, mulVec_zero, smul_zero]
      simpa only [conjTranspose_mul, predProj_conjTranspose] using congrArg conjTranspose hEq
    refine funext fun σ ↦ Subtype.ext ?_
    simp only [restrictPred_coe, wp_measureZ1AndBranch_apply_assertion, hΘ σ 0, hΘ σ 1, map_add,
      conj_conj, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      star_eq_conjTranspose, hAdj _ hL0, hAdj _ hL1]
    simpa only [show predProj S * (phaseFlipUnitary f).1ᴴ = (U.1 * predProj S)ᴴ from (congrArg (· *
      U.1ᴴ) (predProj_conjTranspose S).symm).trans (conjTranspose_mul U.1 (predProj S)).symm] using
      conj_sqrtHalf_add_self (Θ σ).1 (U.1 * predProj S)
/-- Mid-sandwich `152`-wire phase exponent on `uLeaf 0..15`, `bWireLoc 4`, and `rHot152`. -/
noncomputable def midPh152 (γ : BitAssignment 152) : ZMod 2 := (∑ c : Fin 16, γ (uLeaf c) *
  maskSumBit rHot152 (val0Table c) γ) + γ (bWireLoc 4) * lDot 14 le_rfl γ
/-- Stage-2 `30-T` (`0 TOFF`) mid-circuit applying `midPh152` and uncomputing `wEnc` via MBU. -/
def dPhase2Mid {Var : Type} (v : Var) : DynamicCircuit Var 152 := measureZ1AndBranch v wEnc
  ((wSeqFin 16 fun c ↦ maskCz (uLeaf c) (val0Table c) (uLeaf_ne_wAux c)) ;;ᶜ cLempel14 ;;ᶜ czCircuit
  (bWireLoc 4) wEnc (by decide) ;;ᶜ Circuit.H wEnc) (Circuit.X wEnc ;;ᶜ wSeqFin 14 fun k ↦ maskCz
  (uLeaf ⟨k.val, by omega⟩) (deltaTable k) (uLeaf_ne_wAux _))
theorem tr_dPhase2Mid {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) : TransRealizes v (fun
  γ ↦ sClean18 (pTree16.invBits γ)) (fun γ ↦ sClean18 (pTree16.invBits γ)) (phaseFlipUnitary
  midPh152) (dPhase2Mid v) := by
  let cPre : Circuit 152 := (wSeqFin 16 fun c ↦ maskCz (uLeaf c) (val0Table c) (uLeaf_ne_wAux c))
    ;;ᶜ cLempel14 ;;ᶜ czCircuit (bWireLoc 4) wEnc (by decide) ;;ᶜ Circuit.H wEnc
  have hPre (γ : BitAssignment 152) (hγ : sClean18 (pTree16.invBits γ) = true) : γ wEnc = 0 ∧ γ wAux
    = 0 ∧ cPre.eval.1 *ᵥ SelectSwapQROM.ket γ = (sqrtHalf * bitSign (midPh152 γ)) •
    SelectSwapQROM.ket γ + (sqrtHalf * bitSign (midPh152 γ) * bitSign (lDot 14 le_rfl γ)) •
    SelectSwapQROM.ket (update γ wEnc 1) := by
    obtain ⟨hEnc, hAux, hLeaves⟩ : TreeProp 4 le_rfl γ := pTree16.fwdBits_invBits γ ▸
      ((pTreeLevels_spec v 4 le_rfl).2 (pTree16.invBits γ) hγ).2
    have hOneHot : AtMostOneHot14 γ := fun j k hj hk ↦ by
      rw [hLeaves] at hj hk
      split_ifs at hj with hcj
      · split_ifs at hk with hck
        exacts [Fin.ext (hcj.2.trans hck.2.symm), absurd hk zero_ne_one]
      · exact absurd hj zero_ne_one
    refine ⟨hEnc, hAux, ?_⟩
    rw [show cPre = _ from rfl, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, ket_cMaskSeq 16
      uLeaf val0Table _ γ hAux, mulVec_smul, ket_cLempel14 γ hEnc hOneHot, mulVec_smul,
      ket_czCircuit, update_of_ne (by decide : (bWireLoc 4 : Wire 152) ≠ wEnc), update_self,
      smul_smul, ← bitSign_add, show (∑ c : Fin 16, γ (uLeaf c) * maskSumBit rHot152 (val0Table c)
      γ) + γ (bWireLoc 4) * lDot 14 le_rfl γ = midPh152 γ from rfl, mulVec_smul, ket_H, update_self,
      update_idem, show update γ wEnc 0 = γ from hEnc ▸ update_eq_self wEnc γ]
    simp only [smul_add, smul_smul, update_idem]
    exact congrArg₂ (· + ·) (congrArg (· • SelectSwapQROM.ket γ) (by ring)) (congrArg (· •
      SelectSwapQROM.ket (update γ wEnc 1)) (by ring))
  refine tr_mbu_phaseFlip v wEnc cPre (Circuit.X wEnc ;;ᶜ wSeqFin 14 fun k ↦ maskCz (uLeaf
    ⟨k.val, by omega⟩) (deltaTable k) (uLeaf_ne_wAux _))
    (by
      dsimp only [cPre]
      repeat rw [Circuit.count_seq]
      rw [cMaskSeq_toff 16 uLeaf val0Table _, cLempel14_toff, count_czCircuit_toff]
      rfl)
    (by
      rw [Circuit.count_seq, cMaskSeq_toff 14 (fun k ↦ uLeaf ⟨k.val, by omega⟩) deltaTable _]
      rfl)
    (fun γ ↦ sClean18 (pTree16.invBits γ)) midPh152 (fun γ hγ ↦ ?_) (fun γ hγ ↦ ?_)
  · obtain ⟨hEnc, _, hE⟩ := hPre γ hγ
    rw [← mulVec_mulVec, hE, mulVec_add, mulVec_smul, mulVec_smul,
      singleton_projector_zero_mulVec_ket, singleton_projector_zero_mulVec_ket]
    simp [hEnc, one_ne_zero]
  · obtain ⟨hEnc, hAux, hE⟩ := hPre γ hγ
    rw [mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hE, mulVec_add, mulVec_smul, mulVec_smul,
      singleton_projector_one_mulVec_ket, singleton_projector_one_mulVec_ket]
    simp only [hEnc, zero_ne_one, update_self, ↓reduceIte, smul_zero, zero_add, mulVec_smul,
      eval_seq_mulVec, ket_X, update_idem, one_add_one_zmod2, show update γ wEnc 0 = γ from hEnc ▸
      update_eq_self wEnc γ]
    rw [ket_cMaskSeq 14 (fun k ↦ uLeaf ⟨k.val, by omega⟩) deltaTable _ γ hAux, smul_smul, show (∑ k
      : Fin 14, γ (uLeaf ⟨k.val, by omega⟩) * maskSumBit rHot152 (deltaTable k) γ) = lDot 14 le_rfl
      γ from rfl, mul_assoc, bitSign_mul_self, mul_one]
/-- Local `152`-wire (`134` active + `18` scratch) `68-T` (`0 TOFF`) `Hot128` `D_neg` circuit. -/
def hot128DNegLocDyn {Var : Type} (v : Var) : DynamicCircuit Var 152 := .seq (.seq (dTreeLevels v
  4 le_rfl) (dPhase2Mid v)) (revUncomputeDyn v pTree16)
theorem dTree_cnt {Var : Type} (v : Var) : ∀ (d : ℕ) (hd : d ≤ 4), (dTreeLevels v d hd).count .TOFF
  = 0 ∧ (dTreeLevels v d hd).count .T = 2 * d + 2 * (2 ^ d - 1)
  | 0, _ => ⟨count_revComputeDyn_toff _, count_revComputeDyn_t _⟩
  | d + 1, hd => by
      obtain ⟨h0, h1⟩ := dTree_cnt v d (by omega)
      simp only [dTreeLevels, dyn_count_seq, h0, h1, dWGated_toff, dWGated_t]
      refine ⟨trivial, ?_⟩
      have : d ≤ 3 := by omega
      interval_cases d <;> decide
attribute [irreducible] hot128DNegLocDyn
theorem locDyn_toff {Var : Type} (v : Var) : (hot128DNegLocDyn v).count .TOFF = 0 := by
  delta hot128DNegLocDyn
  rw [dyn_count_seq, dyn_count_seq, (dTree_cnt v 4 le_rfl).1,
    count_revUncomputeDyn_toff, dPhase2Mid, count_mbu]
  repeat rw [Circuit.count_seq]
  rw [cMaskSeq_toff 16 uLeaf val0Table _,
    cMaskSeq_toff 14 (fun k ↦ uLeaf ⟨k.val, by omega⟩) deltaTable _,
    cLempel14_toff, count_czCircuit_toff]
  rfl
theorem locDyn_t {Var : Type} (v : Var) : (hot128DNegLocDyn v).count .T = 68 := by
  delta hot128DNegLocDyn
  rw [dyn_count_seq, dyn_count_seq, (dTree_cnt v 4 le_rfl).2,
    count_revUncomputeDyn_t, dPhase2Mid, count_mbu]
  repeat rw [Circuit.count_seq]
  rw [cMaskSeq_t 16 uLeaf val0Table _,
    cMaskSeq_t 14 (fun k ↦ uLeaf ⟨k.val, by omega⟩) deltaTable _,
    cLempel14_t, count_czCircuit_t]
  rfl
/-- Local `134`-wire active slice `0..133` inside `152` wires. -/
abbrev rAct152 : QRegister 134 152 := block 0 134 (by decide)
/-- Local `18`-wire scratch slice `134..151` inside `152` wires. -/
abbrev rScr152 : QRegister 18 152 := block 134 18 (by decide)
theorem midPh152_fwd (β : BitAssignment 152) (hβ : sClean18 β = true) : midPh152 (pTree16.fwdBits β)
  = hot128Ph134 fun i ↦ β (rAct152 i) := by
  obtain ⟨hLow, _, _, hLeaves⟩ := (pTreeLevels_spec () 4 le_rfl).2 β hβ
  let γ := (pTreeLevels 4 le_rfl).fwdBits β
  let βAct : BitAssignment 134 := fun i ↦ β (rAct152 i)
  rw [show (pTreeLevels 4 le_rfl).fwdBits β = γ from rfl] at hLeaves
  have hAct (k : ℕ) (hk : k < 134) : γ ⟨k, by omega⟩ = βAct ⟨k, hk⟩ := (hLow ⟨k, by omega⟩ hk).trans
    (congrArg β (Fin.ext (by simp [rAct152])))
  let c : Fin 16 := (basisBits 4).symm fun j ↦ βAct ⟨1 + j.val, by omega⟩
  have hcEq : bSub 4 le_rfl γ = c := congrArg (basisBits 4).symm (funext fun j ↦ hAct (1 +
    j.val) (by omega))
  have hMask (mask : Fin 128 → Bool) : maskSumBit rHot152 mask γ = maskSumBit (block 6 128
    (by decide)) mask βAct := Finset.sum_congr rfl fun g _ ↦ by
      rw [rHot152, qreg_block_apply, qreg_block_apply, hAct (6 + g.val) (by omega)]
  have hx0 : γ wXo7Loc = βAct ⟨0, by decide⟩ := hAct 0 (by decide)
  rw [show pTree16.fwdBits β = γ from rfl, show (fun i ↦ β (rAct152 i)) = βAct from rfl, midPh152,
    hot128Ph134, lDot, show γ (bWireLoc 4) = βAct ⟨5, by decide⟩ from hAct 5 (by decide)]
  rcases bit_cases (βAct ⟨0, by decide⟩) with hx | hx
  · rw [hx, add_zero, one_mul]
    have hLeaf0 (c' : Fin 16) : γ (uLeaf c') = if c'.val = c.val then 1 else 0 := by
      rw [hLeaves c', hx0, hx, hcEq]
      simp
    rw [Finset.sum_eq_single c (fun c' _ hne ↦ by rw [hLeaf0 c', ite_eq_right fun he ↦ hne (Fin.ext
      he), zero_mul]) fun h ↦ absurd (Finset.mem_univ c) h, hLeaf0 c, ite_eq_left rfl, one_mul,
      hMask]
    refine congrArg (_ + ·) ?_
    by_cases hk : c.val < 14
    · rw [dite_eq_left hk, Finset.sum_eq_single ⟨c.val, hk⟩ (fun j _ hne ↦ by rw [hLeaf0 ⟨j.val,
        by omega⟩, ite_eq_right fun he ↦ hne (Fin.ext he), zero_mul]) fun h ↦ absurd
        (Finset.mem_univ _) h, hLeaf0 ⟨c.val, by omega⟩, ite_eq_left rfl, one_mul, hMask]
    · rw [dite_eq_right hk, Finset.sum_eq_zero fun j _ ↦ by rw [hLeaf0 ⟨j.val, by omega⟩,
        ite_eq_right (by dsimp; omega), zero_mul], mul_zero]
  · rw [hx, one_add_one_zmod2, zero_mul]
    have hLeaf1 (c' : Fin 16) : γ (uLeaf c') = 0 := (hLeaves c').trans (ite_eq_right fun h ↦
      one_ne_zero ((hx0.trans hx).symm.trans h.1))
    simp [hLeaf1]
theorem cleanRealizesLocDyn {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) :
  CleanDyn.CleanRealizes v rAct152 rScr152 hot128DNegUnitary (hot128DNegLocDyn v) := by
  obtain ⟨hv1, _, htr1, hfwd1⟩ := (pTreeLevels_spec v 4 le_rfl).1
  let U_tgt := rAct152.embedUnitary hot128DNegUnitary
  have hMapTgt : U_tgt.1 * predProj sClean18 = predProj sClean18 * U_tgt.1 := by
    dsimp only [U_tgt, hot128DNegUnitary]
    rw [embedUnitary_phaseFlipUnitary]
    exact phaseFlipU_comm_diag _ _
  have hMatEq : (pTree16.toCircuit.eval⁻¹ * (phaseFlipUnitary midPh152 * pTree16.toCircuit.eval)).1
    * predProj sClean18 = U_tgt.1 * predProj sClean18 := SelectSwapQROM.matrix_ext_ket fun β ↦ by
      rw [← mulVec_mulVec, ← mulVec_mulVec, predProj_mulVec_ket]
      by_cases hβ : sClean18 β = true
      · rw [ite_eq_left hβ]
        dsimp only [U_tgt, hot128DNegUnitary]
        simp only [Submonoid.coe_mul, ← mulVec_mulVec]
        have hkG : (SelectSwapQROM.ket : BitAssignment 152 → _) = GroupUnary.ket := rfl
        have hkS : (SelectSwapQROM.ket : BitAssignment 152 → _) = XMeasCircuit.ket := rfl
        rw [hkG, pTree16.toCircuit_mulVec_ket, ← hkG, hkS, phaseFlipUnitary_mulVec_ket, mulVec_smul,
          ← hkS, hkG, revCompute_eval_inv_mulVec_ket, pTree16.invBits_fwdBits, ← hkG,
          embedUnitary_phaseFlipUnitary, hkS, phaseFlipUnitary_mulVec_ket, midPh152_fwd β hβ]
      · rw [ite_eq_right hβ, mulVec_zero, mulVec_zero]
  delta hot128DNegLocDyn
  have hsClean : sClean18 = fun β ↦ decide (∀ j : Fin 18, β (rScr152 j) = 0) :=
    funext fun β ↦ by
      unfold sClean18
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
      exact forall_congr' fun j ↦ (congrArg (β · = 0) (Fin.ext rfl)).to_iff
  exact cleanRealizes_of_transRealizes rAct152 rScr152 (block_disjoint_of_le 0 134 134 18 _ _
    (by decide)) (((((htr1.to_transRealizes_revCompute pTree16 hfwd1).seq (tr_dPhase2Mid v)).seq
    (TransRealizes.uncomputeDyn v pTree16 sClean18 hv1)).congr_unitary hMapTgt hMatEq).congr_pred
    hsClean hsClean)
/-- `134`-wire active register `(rXo[7] : 1) ++ (rB : 5) ++ (rHot : 128)`. -/
abbrev rAct134 {N : ℕ} (rXo : QRegister 8 N) (rB : QRegister 5 N) (rHot : QRegister 128 N) (hXB :
  (QRegister.singleton (rXo ⟨7, by decide⟩)).DisjointWires rB) (hXBH : ((QRegister.singleton (rXo
  ⟨7, by decide⟩)).concat rB hXB).DisjointWires rHot) : QRegister 134 N := ((QRegister.singleton
  (rXo ⟨7, by decide⟩)).concat rB hXB).concat rHot hXBH
local instance instDecDisjWires {k₁ k₂ N : ℕ} (r₁ : QRegister k₁ N) (r₂ : QRegister k₂ N) :
  Decidable (r₁.DisjointWires r₂) := decidable_of_iff (∀ i j, r₁ i ≠ r₂ j) disjoint_iff.symm
/-- Ambient `N`-wire `68-T/pass` (`0 TOFF`) coherent `Hot128` one-sided `D_neg` dynamic circuit. -/
def hot128DNeg62Dyn {Var : Type} {N sTail : ℕ} (hs : 18 ≤ sTail) (v : Var) (rXo : QRegister 8 N)
  (rB : QRegister 5 N) (rHot : QRegister 128 N) (rTail : QRegister sTail N) : DynamicCircuit Var N
  := if hXB : (QRegister.singleton (rXo ⟨7, by decide⟩)).DisjointWires rB then if hXBH :
  ((QRegister.singleton (rXo ⟨7, by decide⟩)).concat rB hXB).DisjointWires rHot then if hDisj :
  (rAct134 rXo rB rHot hXB hXBH).DisjointWires (rTail.slice 0 18 hs) then dynOnRegister ((rAct134
  rXo rB rHot hXB hXBH).concat (rTail.slice 0 18 hs) hDisj) (hot128DNegLocDyn v) else .identity
  else .identity else .identity
theorem cleanRealizesHot128DNeg62Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {N sTail : ℕ}
  (hs : 18 ≤ sTail) (v : Var) (rXo : QRegister 8 N) (rB : QRegister 5 N) (rHot : QRegister 128 N)
  (rTail : QRegister sTail N) (hXB : (QRegister.singleton (rXo ⟨7, by decide⟩)).DisjointWires rB)
  (hXBH : ((QRegister.singleton (rXo ⟨7, by decide⟩)).concat rB hXB).DisjointWires rHot) (hActTail :
  (rAct134 rXo rB rHot hXB hXBH).DisjointWires rTail) : CleanDyn.CleanRealizes v (rAct134 rXo rB
  rHot hXB hXBH) rTail hot128DNegUnitary (hot128DNeg62Dyn hs v rXo rB rHot rTail) := by
  have hActScr : (rAct134 rXo rB rHot hXB hXBH).DisjointWires (rTail.slice 0 18 hs) :=
    hActTail.compose_right (block 0 18 hs)
  let pl := (rAct134 rXo rB rHot hXB hXBH).concat (rTail.slice 0 18 hs) hActScr
  have hCompAct : pl.compose rAct152 = rAct134 rXo rB rHot hXB hXBH := by
    ext i
    rw [compose_apply, show rAct152 i = Fin.castAdd 18 i from Fin.ext (Nat.zero_add i.val),
      concat_apply_left]
  have hCompScr : pl.compose rScr152 = rTail.slice 0 18 hs := by
    ext j
    rw [compose_apply, show rScr152 j = Fin.natAdd 134 j from Fin.ext rfl, concat_apply_right]
  have hOnReg := XMeasCircuit.CleanRealizes.onRegister pl ((cleanRealizes_sbx_iff v rAct152 rScr152
    hot128DNegUnitary (hot128DNegLocDyn v)).mpr (cleanRealizesLocDyn v))
  rw [hCompAct, hCompScr] at hOnReg
  rw [hot128DNeg62Dyn, dite_eq_left hXB, dite_eq_left hXBH, dite_eq_left hActScr]
  exact CleanDyn.CleanRealizes.extend_scr hActTail (rTail.image_compose_subset _)
    ((cleanRealizes_sbx_iff v (rAct134 rXo rB rHot hXB hXBH) (rTail.slice 0 18 hs)
    hot128DNegUnitary _).mp hOnReg)
attribute [irreducible] hot128DNeg62Dyn
theorem hot128Ph_eq : ∀ (x7 b4 : ZMod 2) (c : Fin 16) (g : Fin 128), (1 + x7) * ((if val0Table c g
  then 1 else 0) + if hk : c.val < 14 then b4 * if deltaTable ⟨c.val, hk⟩ g then 1 else 0 else 0) =
  if hot128NegBit2 ⟨128 * (if x7 = 1 then 1 else 0) + g.val, by split_ifs <;> omega⟩
  ⟨16 * (if b4 = 1 then 1 else 0) + c.val, by split_ifs <;> omega⟩ then 1 else 0 := by
  decide +kernel
theorem cleanPredRealizesHot128DNeg62Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {N sTail
  : ℕ} (hs : 18 ≤ sTail) (v : Var) (rXo : QRegister 8 N) (rB : QRegister 5 N) (rHot : QRegister 128
  N) (rTail : QRegister sTail N) (hXoB : rXo.DisjointWires rB) (hXoHot : rXo.DisjointWires rHot)
  (hXoTail : rXo.DisjointWires rTail) (hBHot : rB.DisjointWires rHot) (hBTail : rB.DisjointWires
  rTail) (hHotTail : rHot.DisjointWires rTail) : CleanPredRealizes v (cleanPredProj rTail.image
  (xoOneHotPred (rXo.slice 0 7 (by decide)) rHot)) ((rXo.concat rB hXoB).embedUnitary
  hot128NegUnitary) (hot128DNeg62Dyn hs v rXo rB rHot rTail) := by
  have hXB : (QRegister.singleton (rXo ⟨7, by decide⟩)).DisjointWires rB := disjoint_iff.mpr fun _ j
    ↦ hXoB.ne ⟨7, by decide⟩ j
  have hXBH : ((QRegister.singleton (rXo ⟨7, by decide⟩)).concat rB hXB).DisjointWires rHot :=
    disjointWires_concat_left hXB (disjoint_iff.mpr fun _ g ↦ hXoHot.ne ⟨7, by decide⟩ g) hBHot
  have hActTail : (rAct134 rXo rB rHot hXB hXBH).DisjointWires rTail := disjointWires_concat_left
    hXBH (disjointWires_concat_left hXB (disjoint_iff.mpr fun _ t ↦ hXoTail.ne ⟨7, by decide⟩ t)
    hBTail) hHotTail
  let r134 := rAct134 rXo rB rHot hXB hXBH
  let H := xoOneHotPred (rXo.slice 0 7 (by decide)) rHot
  have hPh (β : BitAssignment N) (hHot : H β = true) : hot128Ph134 (fun i ↦ β (r134 i)) = negPh13
    hot128NegBit2 (fun i ↦ β ((rXo.concat rB hXoB) i)) := by
    let g0 := UnsignedGivens.localIdx (rXo.slice 0 7 (by decide)) β
    have hOneHot : ∀ g : Fin 128, β (rHot g) = if g = g0 then 1 else 0 := by
      dsimp only [H] at hHot
      unfold xoOneHotPred at hHot
      have h := of_decide_eq_true hHot
      exact h
    have hr0 : r134 ⟨0, by decide⟩ = rXo ⟨7, by decide⟩ := (concat_apply_left _ _ _
      ⟨0, by decide⟩).trans (concat_apply_left _ _ _ 0)
    have hrB (j : Fin 5) : r134 ⟨1 + j.val, by omega⟩ = rB j := by
      rw [show (⟨1 + j.val, by omega⟩ : Fin 134) = Fin.castAdd 128 (Fin.natAdd 1 j) from Fin.ext
        (by simp), concat_apply_left, concat_apply_right]
    have hrH (g : Fin 128) : r134 (block 6 128 (by decide) g) = rHot g := by
      rw [show block 6 128 (by decide) g = Fin.natAdd 6 g from Fin.ext (by simp),
        concat_apply_right]
    have hMask (mask : Fin 128 → Bool) : maskSumBit (block 6 128 (by decide)) mask (fun i ↦ β (r134
      i)) = if mask g0 then 1 else 0 := by
      dsimp only [maskSumBit]
      refine (Finset.sum_eq_single g0 (fun g _ hne ↦ ?_) (fun h ↦ absurd (Finset.mem_univ g0)
        h)).trans ?_
      · rw [hrH g, hOneHot g, ite_eq_right hne, ite_self]
      · rw [hrH g0, hOneHot g0, ite_eq_left rfl]
    let c : Fin 16 := (basisBits 4).symm fun j : Fin 4 ↦ β (rB ⟨j.val, by omega⟩)
    have hcEq : ((basisBits 4).symm fun j : Fin 4 ↦ β (r134 ⟨1 + j.val, by omega⟩)) = c :=
      congrArg (basisBits 4).symm (funext fun j ↦ congrArg β (hrB ⟨j.val, by omega⟩))
    have hxoEq : UnsignedGivens.localIdx rXo β =
      ⟨128 * (if β (rXo ⟨7, by decide⟩) = 1 then 1 else 0) + g0.val, by split_ifs <;> omega⟩ :=
      Fin.ext ((localIdx_succ_val rXo β).trans (congrArg₂ (· + ·) (by split_ifs <;> rfl) (congrArg
      Fin.val (congrArg (basisBits 7).symm (show (fun i : Fin 7 ↦ β (rXo.subregister
      (Fin.castLEEmb (Nat.le_succ 7)) i)) = fun i ↦ β ((rXo.slice 0 7 (by decide)) i) from funext
      fun i ↦ congrArg (fun k ↦ β (rXo k)) (Fin.ext (Nat.zero_add i.val).symm))))))
    have hbEq : UnsignedGivens.localIdx rB β =
      ⟨16 * (if β (rB ⟨4, by decide⟩) = 1 then 1 else 0) + c.val, by split_ifs <;> omega⟩ := Fin.ext
      ((localIdx_succ_val rB β).trans (congrArg (· + c.val) (by split_ifs <;> rfl)))
    rw [negPh13_concat, hxoEq, hbEq]
    dsimp only [hot128Ph134]
    rw [hcEq, hr0, show r134 ⟨5, by decide⟩ = rB ⟨4, by decide⟩ from hrB 4]
    simpa only [hMask] using hot128Ph_eq (β (rXo ⟨7, by decide⟩)) (β (rB ⟨4, by decide⟩)) c g0
  let Q := cleanPredProj rTail.image H
  let U_act := r134.embedUnitary hot128DNegUnitary
  let U_13 := (rXo.concat rB hXoB).embedUnitary hot128NegUnitary
  have hSet := (cleanRealizes_iff_set v r134 rTail hot128DNegUnitary (hot128DNeg62Dyn hs v rXo rB
    rHot rTail)).mp ((cleanRealizes_sbx_iff v _ _ _ _).mpr (cleanRealizesHot128DNeg62Dyn hs v
    rXo rB rHot rTail hXB hXBH hActTail))
  have hCommQ : Q * U_13.1ᴴ = U_13.1ᴴ * Q := by
    dsimp only [Q, U_13, hot128NegUnitary, cleanPredProj, zeroProjOn, predProj]
    rw [embedUnitary_phaseFlipUnitary, phaseFlipUnitary_conjTranspose, diagonal_mul_diagonal]
    exact (phaseFlipU_comm_diag _ _).symm
  have hUQ : U_act.1 * Q = U_13.1 * Q := by
    dsimp only [Q, U_act, U_13, hot128DNegUnitary, hot128NegUnitary, cleanPredProj, zeroProjOn,
      predProj]
    rw [embedUnitary_phaseFlipUnitary, embedUnitary_phaseFlipUnitary, phaseFlipUnitary_val,
      phaseFlipUnitary_val, diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal]
    refine congrArg diagonal (funext fun i ↦ ?_)
    by_cases hH : H (basisBits N i) = true
    exacts [by rw [ite_eq_left hH, hPh _ hH], by simp [hH]]
  have hQAdj : Q * U_act.1ᴴ = Q * U_13.1ᴴ := by
    rw [show Q = (cleanPredProj rTail.image H)ᴴ from (cleanPredProj_conjTranspose _ _).symm, ←
      conjTranspose_mul, ← conjTranspose_mul, hUQ]
  refine ⟨hSet.1, hCommQ, hSet.2.1, fun Θ hΘ σ ↦ HermitianMat.ext ?_⟩
  have hQP : zeroProjOn rTail.image * predProj H = cleanPredProj rTail.image H := by
    rw [← zeroProjOn_conjTranspose, ← predProj_conjTranspose, ← conjTranspose_mul,
      predProj_mul_zeroProjOn_eq_cleanPredProj, cleanPredProj_conjTranspose]
  have hv := congrArg (fun x : Observable (Fin (2 ^ N)) ↦ (x.1.conj (predProj H)).mat) (congrFun
    (hSet.2.2.1 Θ hΘ) σ)
  simp only [SelectSwapQROM.restrictZeroSet_coe, conj_apply_mat, predProj_conjTranspose,
    zeroProjOn_conjTranspose, cleanPredProj_conjTranspose] at hv ⊢
  simp only [← mul_assoc, predProj_mul_zeroProjOn_eq_cleanPredProj] at hv
  simp only [mul_assoc, hQP] at hv
  rw [mul_assoc _ _ (cleanPredProj rTail.image H), hv, ← mul_assoc]
  change Q * (qcWpQAssign U_act Θ σ).1.mat * Q = Q * (qcWpQAssign U_13 Θ σ).1.mat * Q
  simp only [qcWpQAssign, qcQAssignObsMap, Observable.conj_coe, conj_apply_mat, Unitary.coe_star,
    star_eq_conjTranspose, conjTranspose_conjTranspose]
  simpa only [mul_assoc] using congrArg₂ (· * ·) (congrArg (· * (Θ σ).1.mat) hQAdj) hUQ
/-- Pass-indexed dyad sign mask (`false` Pass 1, `true` Pass 2) for `55`-AND `π145` `SiZero`. -/
abbrev negMaskPi14555 : Bool → Fin 145 → Bool := negMaskPi14561
/-- Pass-indexed `(Fin 145, Bool) → Fin 319` orbital table (`false` Pass 1, `true` Pass 2). -/
def orbitalOfPi14555 : Bool → Fin 145 → Bool → Fin 319 := orbitalOfPi14561
@[simp] theorem orbitalOfPi14555_eq_61 : orbitalOfPi14555 = orbitalOfPi14561 := rfl
/-- `RouterStep.x` shorthand on `24` router wires. -/
abbrev x_6 (a : Wire 24) : RouterStep 24 := .x a
/-- `RouterStep.cnot` shorthand on `24` router wires. -/
abbrev c_3 (c t : Wire 24) (h : c ≠ t := by decide) : RouterStep 24 := .cnot c t h
/-- `RouterStep.andAlloc` shorthand on `24` router wires. -/
abbrev a_9 (a b c : Wire 24) (h1 : a ≠ b := by decide) (h2 : a ≠ c := by decide)
  (h3 : b ≠ c := by decide) : RouterStep 24 := .andAlloc a b c h1 h2 h3
/-- `RouterStep.andFree` shorthand on `24` router wires. -/
abbrev f_3 (a b c : Wire 24) (h1 : a ≠ b := by decide) (h2 : a ≠ c := by decide)
  (h3 : b ≠ c := by decide) : RouterStep 24 := .andFree a b c h1 h2 h3
/-- Shared `14`-AND Stage-A prefix on `24` router wires (`w23` untouched). -/
def stepsA55 : List (RouterStep 24) := [a_9 2 3 18, a_9 18 4 19, x_6 8, a_9 8 19 0, x_6 8, f_3 18
  4 19, f_3 2 3 18, c_3 0 2, c_3 0 3, c_3 0 4, a_9 0 5 20, a_9 20 6 19, a_9 19 7 18, c_3 18 8, c_3
  18 1, f_3 20 6 19, c_3 20 2, c_3 20 5, f_3 0 2 20, a_9 0 6 20, c_3 20 3, c_3 20 6, f_3 0 3 20, a_9
  0 7 20, c_3 20 4, c_3 20 7, f_3 0 4 20]
/-- Pass-indexed Stage-B prefix before `7`-CSWAP (`6` ANDs Pass 1, `4` ANDs Pass 2). -/
def preB55 (op : Bool) : List (RouterStep 24) := if op then [c_3 8 5, c_3 18 5, x_6 5, a_9 3 5 19,
  x_6 5, c_3 19 2, x_6 5, f_3 3 5 19, x_6 5, c_3 6 4, a_9 2 4 19, c_3 19 3, f_3 2 4 19, c_3 6 4, c_3
  2 3, x_6 3, x_6 4, c_3 2 3, c_3 3 2, c_3 2 3, c_3 2 4, c_3 4 2, c_3 2 4, c_3 0 2, c_3 0 3, x_6 3,
  c_3 0 3] else [c_3 8 18, a_9 18 4 19, c_3 19 6, f_3 18 4 19, c_3 6 2, a_9 5 2 19, c_3 19 3, c_3 19
  4, f_3 5 2 19, c_3 6 2, c_3 2 4, c_3 5 4, a_9 3 4 19, c_3 19 2, f_3 3 4 19, c_3 5 4, c_3 2 4, c_3
  18 5, c_3 2 3, c_3 4 2, c_3 3 4, c_3 4 3, c_3 3 4, c_3 6 2, x_6 2, c_3 8 18, c_3 0 2]
/-- First half (`6` ANDs) of `w8`-controlled `7`-CSWAP. -/
def midCsA55 : List (RouterStep 24) := [c_3 3 10, a_9 8 10 19, c_3 19 3, f_3 8 10 19, c_3 3 10,
  c_3 9 15, a_9 8 15 19, c_3 19 9, f_3 8 15 19, c_3 9 15, x_6 9, c_3 9 14, a_9 8 14 19, c_3 19 9,
  f_3 8 14 19, c_3 9 14]
/-- Pass-indexed second half (`8` ANDs) of `7`-CSWAP. -/
def midCsB55 (op : Bool) : List (RouterStep 24) := [c_3 2 11, a_9 8 11 19, c_3 19 2, f_3 8 11 19,
  c_3 2 11, c_3 4 7, a_9 8 7 19, c_3 19 4, f_3 8 7 19, c_3 4 7] ++ (if op then [x_6 4] else [x_6 1,
  x_6 4]) ++ [c_3 1 12, a_9 8 12 19, c_3 19 1, f_3 8 12 19, c_3 1 12, c_3 4 13, a_9 8 13 19, c_3 19
  4, f_3 8 13 19, c_3 4 13]
/-- Pass-indexed Stage-B post-router (`w23` retains `w12 & !w11`, saving `-2` ANDs). -/
def postB55 (op : Bool) : List (RouterStep 24) := [a_9 14 13 19, x_6 11, a_9 12 11 23, x_6 11, a_9
  19 23 20, a_9 20 8 17] ++ (if op then [x_6 5, x_6 6, a_9 6 5 22, x_6 5, x_6 6, a_9 17 22 21, x_6
  5, x_6 6, f_3 6 5 22, x_6 5, x_6 6, f_3 20 8 17, c_3 21 0, a_9 21 7 17, c_3 17 5, c_3 17 7, c_3 17
  14, c_3 17 13, c_3 17 12, c_3 17 19, c_3 17 20, c_3 17 23, c_3 17 21, c_3 21 18, x_6 10, a_9 21 10
  22, x_6 10, c_3 22 11, c_3 22 20, c_3 22 23, x_6 10, f_3 21 10 22, x_6 10, c_3 10 11, f_3 18 11
  21, c_3 10 11, c_3 17 18, f_3 18 5 17] else [x_6 5, a_9 6 5 22, x_6 5, a_9 17 22 21, x_6 5, f_3 6
  5 22, x_6 5, f_3 20 8 17, c_3 21 0, c_3 21 6, c_3 21 18, c_3 21 20, a_9 21 7 17, c_3 17 5, c_3 17
  7, c_3 17 14, c_3 17 13, c_3 17 12, c_3 17 19, c_3 21 11, c_3 17 11, c_3 21 23, f_3 21 5 17, c_3 5
  11, f_3 18 11 21, c_3 5 11]) ++ [c_3 5 10, a_9 20 10 21, x_6 22, c_3 8 22, c_3 0 22, c_3 18 22,
  a_9 22 21 17, c_3 17 5, f_3 22 21 17, c_3 18 22, c_3 0 22, c_3 8 22, x_6 22, f_3 8 0 18, a_9 0 21
  17, c_3 17 8, f_3 0 21 17, f_3 20 10 21, c_3 5 10, f_3 19 23 20, x_6 11, f_3 12 11 23, x_6 11, f_3
  14 13 19]
/-- Complete `41`-AND Stage-B router (`false` Pass 1, `true` Pass 2). -/
def stepsB55 (op : Bool) : List (RouterStep 24) := (preB55 op ++ (midCsA55 ++ midCsB55 op))
  ++ postB55 op
/-- Pass-1 `41`-AND Stage-B router alias. -/
abbrev stepsBFwd55 : List (RouterStep 24) := stepsB55 false
/-- Pass-2 `41`-AND Stage-B router alias. -/
abbrev stepsBBwd55 : List (RouterStep 24) := stepsB55 true
@[simp] theorem numRouterAndsStepsA55 : numRouterAnds stepsA55 = 14 := by decide
@[simp] theorem numRouterAndsStepsB55 (op : Bool) :
    numRouterAnds (stepsB55 op) = 41 := by cases op <;> decide
/-- Execute `steps : List (RouterStep 24)` on `st : State24`, falling back to `st` if `none`. -/
def step24 (steps : List (RouterStep 24)) (st : State24) : State24 := (runSteps24 le_rfl steps
  st).getD st
/-- Strictly execute `steps : List (RouterStep 24)` once from `s0` and pass the result to `k`. -/
def withR {α : Type} (steps : List (RouterStep 24)) (s0 : State24) (k : State24 → α) : α :=
  strictState24 s0 fun s0' ↦ match fastSteps24 steps s0' with | none => k s0' | some s1 => k s1
theorem withR_eq {α : Type} (steps : List (RouterStep 24)) (s0 : State24) (k : State24 → α) : withR
  steps s0 k = k (step24 steps s0) := by
  rw [withR, step24, strictState24_eq, fastSteps24_eq le_rfl]
  cases runSteps24 le_rfl steps s0 <;> rfl
/-- Active-wire mask `[0..8, 18..20]` of `stepsA55`. -/
def maskA (i : Fin 24) : Bool := i.val ≤ 8 || (18 ≤ i.val && i.val ≤ 20)
/-- Stage-A `State24` specification of `stepsA55` on `initState23 x16`. -/
def specA55 (x16 : Fin 16 → Bool) : State24 := mergeState24 maskA (step24 stepsA55
  (canonA (initState23 x16))) (initState23 x16)
/-- Strictly evaluate `specA55 x16` once in CPS and pass it to `k`. -/
def withA {α : Type} (x16 : Fin 16 → Bool) (k : State24 → α) : α := strictState24 (initState23 x16)
  fun b ↦ withR stepsA55 (canonA b) fun a ↦ k ⟨a.q0, ⟨a.q1.b0, b.q1.b1, b.q1.b2, b.q1.b3,
  b.q1.b4, b.q1.b5, b.q1.b6, b.q1.b7⟩, ⟨b.q2.b0, b.q2.b1, a.q2.b2, a.q2.b3, a.q2.b4, b.q2.b5,
  b.q2.b6, b.q2.b7⟩⟩
theorem withA_eq {α : Type} (x16 : Fin 16 → Bool) (k : State24 → α) : withA x16 k = k (specA55
  x16) := (strictState24_eq _ _).trans (withR_eq _ _ _)
/-- Active-wire mask `[0..8, 18, 19]` of `preB55`. -/
def mPre (i : Fin 24) : Bool := i.val ≤ 8 || i.val == 18 || i.val == 19
/-- Canonical `9`-bit projection onto `[0..8]` with `w18 = w8 && w0` (`q2.b2`) and `w19 = false`. -/
def cPre2 (st : State24) : State24 := ⟨st.q0, ⟨st.q1.b0, false, false, false, false, false, false,
  false⟩, ⟨false, false, st.q1.b0 && st.q0.b0, false, false, false, false, false⟩⟩
/-- Active-wire mask `[3, 8, 9, 10, 14, 15, 19]` of `midCsA55`. -/
def mCsA (i : Fin 24) : Bool := i.1 == 3 || i.1 == 8 || i.1 == 9 || i.1 == 10 || i.1 == 14 || i.1
  == 15 || i.1 == 19
/-- Active-wire mask `[1, 2, 4, 7, 8, 11, 12, 13, 19]` of `midCsB55`. -/
def mCsB (i : Fin 24) : Bool := i.1 == 1 || i.1 == 2 || i.1 == 4 || i.1 == 7 || i.1 == 8 || i.1 ==
  11 || i.1 == 12 || i.1 == 13 || i.1 == 19
/-- Active-wire mask `[0, 5..8, 10..14, 17..23]` of `postB55`. -/
def mPost (i : Fin 24) : Bool := i.1 == 0 || 5 ≤ i.1 && i.1 ≤ 8 || 10 ≤ i.1 && i.1 ≤ 14 || 17 ≤
  i.1
/-- Canonical `10`-bit projection onto `[0, 5..8, 10..14]` with `w18 = w8 && w0` (`q2.b2`). -/
def cPost2 (st : State24) : State24 := ⟨⟨st.q0.b0, false, false, false, false, st.q0.b5, st.q0.b6,
  st.q0.b7⟩, ⟨st.q1.b0, false, st.q1.b2, st.q1.b3, st.q1.b4, st.q1.b5, st.q1.b6, false⟩, ⟨false,
  false, st.q1.b0 && st.q0.b0, false, false, false, false, false⟩⟩
/-- Exact `State24` effect of `midCsA55` on canonical `6`-bit inputs (`w19 = false`). -/
def csASpec (b3 b8 b9 b10 b14 b15 : Bool) : State24 := ⟨⟨false, false, false, if b8 then b10 else
  b3, false, false, false, false⟩, ⟨b8, if b8 then b14 else !b9, if b8 then b3 else b10, false,
  false, false, if b8 then !b15 else b14, if b8 then b9 else b15⟩, zeroState8⟩
/-- Exact `State24` effect of `midCsB55 op` on canonical `8`-bit inputs (`w19 = false`). -/
def csBSpec (op b1 b2 b4 b7 b8 b11 b12 b13 : Bool) : State24 := ⟨⟨false, if b8 then b12 else xor
  b1 (!op), if b8 then b11 else b2, false, if b8 then b13 else !b4, false, false, if b8 then b4 else
  b7⟩, ⟨b8, false, false, if b8 then b2 else b11, if b8 then xor b1 (!op) else b12, if b8 then !b7
  else b13, false, false⟩, zeroState8⟩
/-- Stage-B `State24` after `preB55 ++ midCsA55 ++ midCsB55`. -/
def pre3 (op : Bool) (st0 : State24) : State24 :=
  let st1 := mergeState24 mPre (step24 (preB55 op) (cPre2 st0)) st0
  let st2 := mergeState24 mCsA (csASpec st1.q0.b3 st1.q1.b0 st1.q1.b1 st1.q1.b2 st1.q1.b6
    st1.q1.b7) st1
  mergeState24 mCsB (csBSpec op st2.q0.b1 st2.q0.b2 st2.q0.b4 st2.q0.b7 st2.q1.b0 st2.q1.b3
    st2.q1.b4 st2.q1.b5) st2
/-- Four-slice Stage-B `State24` specification of `stepsB55 op`. -/
def specB55 (op : Bool) (st0 : State24) : State24 := mergeState24 mPost (step24 (postB55 op)
  (cPost2 (pre3 op st0))) (pre3 op st0)
theorem runA_ok (a0 a1 a2 a3 a4 a5 a6 a7 : Bool) :
    let s0 : State24 := ⟨⟨false, a0, a1, a2, a3, a4, a5, a6⟩, ⟨a7, false, false, false, false,
      false, false, false⟩, zeroState8⟩
    let s1 := step24 stepsA55 s0
    runSteps24 le_rfl stepsA55 s0 = some s1 ∧ s1.get24 18 = (s1.get24 8 && s1.get24 0) ∧
      s1.get24 19 = false ∧ s1.get24 20 = false := by
  have hb : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool, fastCheckRun24 stepsA55 ⟨⟨false, a0, a1, a2, a3, a4,
    a5, a6⟩, ⟨a7, false, false, false, false, false, false, false⟩, zeroState8⟩ (fun s1 ↦ (s1.get24
    18 == (s1.get24 8 && s1.get24 0)) && !s1.get24 19 && !s1.get24 20) = true := by decide +kernel
  obtain ⟨hr, hp⟩ := fastCheckRun24_iff le_rfl (hb a0 a1 a2 a3 a4 a5 a6 a7)
  dsimp only [step24] at hp ⊢
  generalize (runSteps24 _ _ _).getD _ = s1 at hr hp ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp
  exact ⟨hr, hp.1.1, hp.1.2, hp.2⟩
theorem runSteps24StepsA55 (x16 : Fin 16 → Bool) : runSteps24 le_rfl stepsA55 (initState23 x16)
  = some (specA55 x16) := (congrArg (runSteps24 le_rfl _) (rfl : initState23 x16 = mergeState24
  maskA (canonA (initState23 x16)) (initState23 x16))).trans (runSteps24_merge le_rfl maskA
  stepsA55 (by decide +kernel) _ _ (initState23 x16) (runA_ok (x16 0) (x16 1) (x16 2) (x16 3)
  (x16 4) (x16 5) (x16 6) (x16 7)).1)
theorem specA55_borrows (x16 : Fin 16 → Bool) : (specA55 x16).get24 17 = false ∧ (specA55
  x16).get24 18 = ((specA55 x16).get24 8 && (specA55 x16).get24 0) ∧ (∀ k : Fin 5, (specA55
  x16).get24 ⟨19 + k.val, by omega⟩ = false) := by
  have hok := (runA_ok (x16 0) (x16 1) (x16 2) (x16 3) (x16 4) (x16 5) (x16 6) (x16 7)).2
  dsimp only [specA55, canonA, initState23]
  generalize step24 stepsA55 _ = s1 at hok ⊢
  refine ⟨rfl, hok.1, fun k ↦ ?_⟩
  fin_cases k
  exacts [hok.2.1, hok.2.2, rfl, rfl, rfl]
/-- Stage-B `preB55` state on canonical `xo'` input. -/
def sPre2 (op : Bool) (xo' : Fin 256) : State24 := step24 (preB55 op) (cPre2 (specA55
  (pack16 xo' false 0 false false)))
/-- Post-CSWAP canonical input for `126 ≤ xo'` and arbitrary `si : Bool` given `sp`. -/
def geIn (op : Bool) (sp : State24) (si : Bool) : State24 := ⟨⟨sp.q0.b0, false, false, false,
  false, sp.q0.b5, sp.q0.b6, sp.q0.b4⟩, ⟨true, false, sp.q0.b3, sp.q0.b2, xor sp.q0.b1 (!op),
  !sp.q0.b7, !si, false⟩, ⟨false, false, sp.q0.b0, false, false, false, false, false⟩⟩
/-- Boolean check of wire `w8 = decide (126 ≤ xo'.val)` and `r : Fin 9` bits on `xo' < 126`. -/
def chkXoW8 (op : Bool) (xo' : Fin 256) : Bool :=
  let r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))
  withA (pack16 xo' false 0 false false) fun st0 ↦ (st0.q1.b0 == decide (126 ≤ xo'.val)) && withR
    (preB55 op) (cPre2 st0) fun sp ↦ (sp.q1.b0 == decide (126 ≤ xo'.val)) && (decide (126 ≤
    xo'.val) || ((sp.q0.b0 == (r.val / 8 % 2 == 1)) && (sp.q0.b5 == (r.val % 2 == 1)) && (sp.q0.b6
    == (r.val / 2 % 2 == 1)) && (sp.q0.b7 == (r.val / 4 % 2 == 1))))
theorem mod256_fin (x : Fin 256) : (⟨x.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = x :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt)
theorem mod32_fin (b : Fin 32) : (⟨b.val % 32, Nat.mod_lt _ (by decide)⟩ : Fin 32) = b := Fin.ext
  (Nat.mod_eq_of_lt b.isLt)
theorem xoW8_full (op : Bool) (x : Fin 256) :
    let r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv x))
    let sp := sPre2 op x
    (specA55 (pack16 x false 0 false false)).get24 8 = decide (126 ≤ x.val) ∧ sp.get24 8 = decide
      (126 ≤ x.val) ∧ (x.val < 126 → sp.q0.b0 = (r.val / 8 % 2 == 1) ∧ sp.q0.b5 = (r.val % 2 == 1) ∧
      sp.q0.b6 = (r.val / 2 % 2 == 1) ∧ sp.q0.b7 = (r.val / 4 % 2 == 1)) := by
  have hb : ∀ od : Bool, allPow2 8 0 (fun q ↦ chkXoW8 od ⟨q % 256, Nat.mod_lt _ (by decide)⟩) =
    true := by decide +kernel
  have h : chkXoW8 op x = true := (congrArg (chkXoW8 op) (mod256_fin x)).symm.trans
    (allPow2_zero_true (hb op) x.val x.isLt)
  rw [chkXoW8, withA_eq, withR_eq] at h
  change ((specA55 (pack16 x false 0 false false)).get24 8 == decide (126 ≤ x.val) && (((sPre2 op
    x).get24 8 == decide (126 ≤ x.val)) && _)) = true at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, h.2.1, fun hlt ↦ ?_⟩
  have hr := h.2.2
  simp only [decide_eq_false (by omega : ¬ 126 ≤ x.val), Bool.false_or, Bool.and_eq_true,
    beq_iff_eq] at hr
  exact ⟨hr.1.1.1, hr.1.1.2, hr.1.2, hr.2⟩
theorem tbIn_eq_rIn (od : Bool) (x : Fin 256) (hx : x.1 < 126) (b : Fin 32) : twoBodyPostIn
  (sPre2 od x) b = twoBodyRIn (rDiv14OfRc (rcBitsOfXo (pi145XoEquiv x))) b := by
  obtain ⟨hb0, hb5, hb6, hb7⟩ := (xoW8_full od x).2.2 hx
  simp only [twoBodyPostIn, twoBodyRIn, hb0, hb5, hb6, hb7]
/-- Pure boolean check that `postB55 op` succeeds with `7` clean borrows and `< 145`. -/
def chkPost (op : Bool) (s0 : State24) : Bool := fastCheckRun24 (postB55 op) s0 fun s1 ↦ !s1.q2.b1
  && !s1.q2.b2 && !s1.q2.b3 && !s1.q2.b4 && !s1.q2.b5 && !s1.q2.b6 && !s1.q2.b7 && lt145Nat
  (pair8NatOf10 (fastCtrl10 s1))
theorem ctrl10_mergePost (sOut st3 : State24) : ctrl10OfState24 (mergeState24 mPost sOut st3) =
  ctrl10OfState24 sOut := funext fun u ↦ by fin_cases u <;> rfl
theorem mergeCs (s : State24) (h19 : s.get24 19 = false) : mergeState24 mCsA (canonCsA2 s) s =
  s ∧ mergeState24 mCsB ⟨⟨false, s.q0.b1, s.q0.b2, false, s.q0.b4, false, false, s.q0.b7⟩,
  ⟨s.q1.b0, false, false, s.q1.b3, s.q1.b4, s.q1.b5, false, false⟩, zeroState8⟩ s = s := by
  rcases s with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  dsimp [State24.get24, State8.get8] at h19
  subst h19
  exact ⟨rfl, rfl⟩
theorem mergePrePost (s : State24) (h17 : s.get24 17 = false) (h18 : s.get24 18 = (s.get24 8 &&
  s.get24 0)) (h19 : s.get24 19 = false) (h20 : s.get24 20 = false) (h21 : s.get24 21 = false) (h22
  : s.get24 22 = false) (h23 : s.get24 23 = false) : mergeState24 mPre (cPre2 s) s = s ∧
  mergeState24 mPost (cPost2 s) s = s := by
  rcases s with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩⟩
  dsimp [State24.get24, State8.get8] at h17 h18 h19 h20 h21 h22 h23
  subst h17 h18 h19 h20 h21 h22 h23
  exact ⟨rfl, rfl⟩
theorem pre3_run (op : Bool) (st0 : State24) (h17_0 : st0.get24 17 = false) (hw18_0 : st0.get24 18
  = (st0.get24 8 && st0.get24 0)) (hb0 : ∀ k : Fin 5, st0.get24 ⟨19 + k.val, by omega⟩ = false) :
  runSteps24 le_rfl (preB55 op ++ (midCsA55 ++ midCsB55 op)) st0 = some (pre3 op st0) ∧
  mergeState24 mPost (cPost2 (pre3 op st0)) (pre3 op st0) = pre3 op st0 := by
  dsimp only [pre3, step24]
  have hPreB : ∀ od a b c d e f g h k : Bool, fastCheckRun24 (preB55 od) ⟨⟨a, b, c, d, e, f, g,
    h⟩, ⟨k, false, false, false, false, false, false, false⟩, ⟨false, false, k && a, false, false,
    false, false, false⟩⟩ (fun s1 ↦ (s1.get24 18 == (s1.get24 8 && s1.get24 0)) && !s1.get24 19) =
    true := by decide +kernel
  have hCsA : ∀ a b c d e f : Bool, runSteps24 le_rfl midCsA55 ⟨⟨false, false, false, a, false,
    false, false, false⟩, ⟨b, c, d, false, false, false, e, f⟩, zeroState8⟩ = some (csASpec a b c
    d e f) := by decide +kernel
  have hCsB : ∀ od a b c d e f g h : Bool, runSteps24 le_rfl (midCsB55 od) ⟨⟨false, a, b, false,
    c, false, false, d⟩, ⟨e, false, false, f, g, h, false, false⟩, zeroState8⟩ = some (csBSpec od
    a b c d e f g h) := by decide +kernel
  obtain ⟨hr1_0, hp1⟩ := fastCheckRun24_iff le_rfl (hPreB op st0.q0.b0 st0.q0.b1 st0.q0.b2 st0.q0.b3
    st0.q0.b4 st0.q0.b5 st0.q0.b6 st0.q0.b7 st0.q1.b0)
  rw [show (⟨⟨st0.q0.b0, st0.q0.b1, st0.q0.b2, st0.q0.b3, st0.q0.b4, st0.q0.b5, st0.q0.b6,
    st0.q0.b7⟩, ⟨st0.q1.b0, false, false, false, false, false, false, false⟩, ⟨false, false,
    st0.q1.b0 && st0.q0.b0, false, false, false, false, false⟩⟩ : State24) = cPre2 st0 from rfl]
    at hr1_0 hp1
  generalize (runSteps24 _ _ _).getD _ = s1 at hr1_0 hp1 ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hp1
  let s2 := mergeState24 mPre s1 st0
  let s3 := mergeState24 mCsA (csASpec s2.q0.b3 s2.q1.b0 s2.q1.b1 s2.q1.b2 s2.q1.b6 s2.q1.b7) s2
  let s4 := mergeState24 mCsB (csBSpec op s3.q0.b1 s3.q0.b2 s3.q0.b4 s3.q0.b7 s3.q1.b0 s3.q1.b3
    s3.q1.b4 s3.q1.b5) s3
  have hr1 : runSteps24 le_rfl (preB55 op) st0 = some s2 := (congrArg (runSteps24 le_rfl (preB55
    op)) (mergePrePost st0 h17_0 hw18_0 (hb0 0) (hb0 1) (hb0 2) (hb0 3) (hb0 4)).1.symm).trans
    (runSteps24_merge le_rfl mPre _ (by cases op <;> decide +kernel) _ _ st0 hr1_0)
  have hr2 : runSteps24 le_rfl midCsA55 s2 = some s3 := (congrArg (runSteps24 le_rfl midCsA55)
    (mergeCs s2 hp1.2).1.symm).trans (runSteps24_merge le_rfl mCsA _ (by decide +kernel) _ _ s2
    (hCsA s2.q0.b3 s2.q1.b0 s2.q1.b1 s2.q1.b2 s2.q1.b6 s2.q1.b7))
  have hr3 : runSteps24 le_rfl (midCsB55 op) s3 = some s4 := (congrArg (runSteps24 le_rfl
    (midCsB55 op)) (mergeCs s3 rfl).2.symm).trans (runSteps24_merge le_rfl mCsB _
    (by cases op <;> decide +kernel) _ _ s3 (hCsB op s3.q0.b1 s3.q0.b2 s3.q0.b4 s3.q0.b7 s3.q1.b0
    s3.q1.b3 s3.q1.b4 s3.q1.b5))
  exact ⟨by rw [runSteps24_append le_rfl _ _ st0 s2 hr1, runSteps24_append le_rfl _ _ s2 s3 hr2,
    hr3], (mergePrePost s4 h17_0 hp1.1 rfl (hb0 1) (hb0 2) (hb0 3) (hb0 4)).2⟩
theorem pre3_pack16 (op : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32) (si neg : Bool) :
    let st0 := specA55 (pack16 xo' so b si neg)
    let st3 := pre3 op st0
    runSteps24 le_rfl (preB55 op ++ (midCsA55 ++ midCsB55 op)) st0 = some st3 ∧ mergeState24
      mPost (cPost2 st3) st3 = st3 ∧ (xo'.val < 126 → st0.get24 8 = false ∧ st3.get24 15 = si ∧
      st0.get24 16 = neg ∧ cPost2 st3 = twoBodyPostIn (sPre2 op xo') b) ∧ (126 ≤ xo'.val →
      st0.get24 8 = true ∧ st3.get24 15 = so ∧ cPost2 st3 = geIn op (sPre2 op xo') si) := by
  dsimp only
  set sA0 := specA55 (pack16 xo' false 0 false false)
  let sp := sPre2 op xo'
  obtain ⟨hPE, hg8⟩ : cPre2 (specA55 (pack16 xo' so b si neg)) = cPre2 sA0 ∧ (specA55 (pack16
    xo' so b si neg)).get24 8 = sA0.get24 8 := by
    dsimp only [sA0, cPre2, specA55]
    rw [show canonA (initState23 (pack16 xo' so b si neg)) = canonA (initState23 (pack16 xo'
      false 0 false false)) from rfl]
    generalize step24 stepsA55 _ = sA
    exact ⟨rfl, rfl⟩
  obtain ⟨hso, hsi, hneg, h2I⟩ : let s0 := specA55 (pack16 xo' so b si neg)
      s0.q1.b1 = so ∧ s0.q1.b7 = si ∧ s0.get24 16 = neg ∧ (⟨⟨sp.q0.b0, false, false, false, false,
        sp.q0.b5, sp.q0.b6, sp.q0.b7⟩, ⟨false, false, s0.q1.b2, s0.q1.b3, s0.q1.b4, s0.q1.b5,
        s0.q1.b6, false⟩, zeroState8⟩ : State24) = twoBodyPostIn sp b := by
    dsimp only [specA55, twoBodyPostIn, initState23, pack16]
    generalize step24 _ _ = sA
    exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨h17, h18, hb0⟩ := specA55_borrows (pack16 xo' so b si neg)
  generalize specA55 (pack16 xo' so b si neg) = s0 at hPE hg8 hso hsi hneg h2I h17 h18 hb0 ⊢
  obtain ⟨hrPre3, hm4⟩ := pre3_run op s0 h17 h18 hb0
  have hsPre : step24 (preB55 op) (cPre2 s0) = sPre2 op xo' := congrArg _ hPE
  have hCs : (sp.q1.b0 = false → (pre3 op s0).get24 15 = s0.q1.b7 ∧ cPost2 (pre3 op s0) =
    ⟨⟨sp.q0.b0, false, false, false, false, sp.q0.b5, sp.q0.b6, sp.q0.b7⟩, ⟨false, false, s0.q1.b2,
    s0.q1.b3, s0.q1.b4, s0.q1.b5, s0.q1.b6, false⟩, zeroState8⟩) ∧ (sp.q1.b0 = true → (pre3 op
    s0).get24 15 = s0.q1.b1 ∧ cPost2 (pre3 op s0) = geIn op sp s0.q1.b7) := by
    dsimp only [sp, pre3]
    rw [hsPre]
    generalize sPre2 op xo' = sp0
    rcases sp0 with ⟨⟨_, _, _, _, _, _, _, _⟩, ⟨_ | _, _, _, _, _, _, _, _⟩, _⟩
    exacts [⟨fun _ ↦ ⟨rfl, rfl⟩, nofun⟩, ⟨nofun, fun _ ↦ ⟨rfl, rfl⟩⟩]
  obtain ⟨h8A, h8S, _⟩ := xoW8_full op xo'
  refine ⟨hrPre3, hm4, fun hxo' ↦ ?_, fun h126 ↦ ?_⟩
  · obtain ⟨h15, hPost⟩ := hCs.1 (h8S.trans (decide_eq_false (by omega)))
    exact ⟨hg8.trans (h8A.trans (decide_eq_false (by omega))), h15.trans hsi, hneg, hPost.trans h2I⟩
  · obtain ⟨h15, hPost⟩ := hCs.2 (h8S.trans (decide_eq_true h126))
    exact ⟨hg8.trans (h8A.trans (decide_eq_true h126)), h15.trans hso, hPost.trans (congrArg (geIn
      op sp) hsi)⟩
theorem post_all (op : Bool) (x : Fin 16 → Bool) : runSteps24 le_rfl (stepsB55 op) (specA55 x)
  = some (specB55 op (specA55 x)) ∧ (∀ k : Fin 7, (specB55 op (specA55 x)).get24
  ⟨17 + k.val, by omega⟩ = false) ∧ pair8NatOf10 (ctrl10OfState24 (specB55 op (specA55 x))) <
  145 := by
  let st0 := specA55 x
  set xo' : Fin 256 := finOfBits 8 fun i ↦ x ⟨i.val, by omega⟩
  set b : Fin 32 := finOfBits 5 fun j ↦ x ⟨9 + j.val, by omega⟩
  obtain ⟨hrPre3, hm4, h2B, h1B⟩ := pre3_pack16 op xo' (x 8) b (x 14) (x 15)
  rw [← show st0 = specA55 (pack16 xo' (x 8) b (x 14) (x 15)) from congrArg specA55
    (pack16_eq_self_bound50 x).symm] at hrPre3 hm4 h2B h1B
  let st3 := pre3 op st0
  have hPostChk : chkPost op (cPost2 st3) = true := by
    by_cases hxo' : xo'.val < 126
    · have hb2 : ∀ od : Bool, allPow2 4 0 (fun r ↦ if hr : r < 9 then allPow2 5 0 (fun b ↦
        chkPost od (twoBodyRIn ⟨r, hr⟩ ⟨b % 32, Nat.mod_lt _ (by decide)⟩)) else true) = true :=
        by decide +kernel
      rw [(h2B hxo').2.2.2, tbIn_eq_rIn op xo' hxo' b]
      set r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))
      have h1 := allPow2_zero_true (hb2 op) r.val (by omega)
      rw [dite_eq_left r.isLt] at h1
      simpa only [mod32_fin b] using allPow2_zero_true h1 b.val b.isLt
    · have hb1 : ∀ od si : Bool, allPow2 8 0 (fun q ↦ if 126 ≤ q then withA (pack16 ⟨q % 256,
        Nat.mod_lt _ (by decide)⟩ false 0 false false) fun s0 ↦ withR (preB55 od) (cPre2 s0) fun
        sp ↦ chkPost od (geIn od sp si) else true) = true := by decide +kernel
      rw [(h1B (by omega)).2.2]
      have h1 := allPow2_zero_true (hb1 op (x 14)) xo'.val xo'.isLt
      rwa [ite_eq_left (by omega), mod256_fin xo', withA_eq, withR_eq] at h1
  obtain ⟨hr4_0, hp4⟩ := fastCheckRun24_iff le_rfl hPostChk
  rw [fastCtrl10_eq] at hp4
  have hDef : specB55 op st0 = mergeState24 mPost ((runSteps24 le_rfl (postB55 op) (cPost2
    st3)).getD (cPost2 st3)) st3 := rfl
  generalize (runSteps24 _ _ _).getD _ = s4 at hr4_0 hp4 hDef
  simp only [lt145Nat, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hp4
  have hr4 : runSteps24 le_rfl (postB55 op) st3 = some (specB55 op st0) := ((congrArg
    (runSteps24 le_rfl (postB55 op)) hm4.symm).trans (runSteps24_merge le_rfl mPost _
    (by cases op <;> decide +kernel) _ _ st3 hr4_0)).trans (congrArg some hDef.symm)
  refine ⟨by rw [stepsB55, runSteps24_append le_rfl _ _ st0 st3 hrPre3, hr4], fun k ↦ ?_, ?_⟩
  · rw [show specA55 x = st0 from rfl, hDef]
    fin_cases k
    exacts [hp4.1.1.1.1.1.1.1, hp4.1.1.1.1.1.1.2, hp4.1.1.1.1.1.2, hp4.1.1.1.1.2, hp4.1.1.1.2,
      hp4.1.1.2, hp4.1.2]
  · rw [show specA55 x = st0 from rfl, hDef, ctrl10_mergePost]; exact hp4.2
theorem runSteps24StepsB55 (op : Bool) (x16 : Fin 16 → Bool) : runSteps24 le_rfl (stepsB55 op)
  (specA55 x16) = some (specB55 op (specA55 x16)) := (post_all op x16).1
theorem specB55_borrows_false (op : Bool) (x16 : Fin 16 → Bool) (k : Fin 7) : (specB55 op
  (specA55 x16)).get24 ⟨17 + k.val, by omega⟩ = false := (post_all op x16).2.1 k
theorem ctrl10_pair8_lt145 (op : Bool) (x16 : Fin 16 → Bool) : pair8NatOf10 (ctrl10OfState24
  (specB55 op (specA55 x16))) < 145 := (post_all op x16).2.2
theorem specB55_get24_ne16_indep15 (op : Bool) (x16 : Fin 16 → Bool) (v : Bool) (i : Fin 24) (hi :
  i ≠ 16) : (specB55 op (specA55 (update x16 15 v))).get24 i = (specB55 op (specA55
  x16)).get24 i := by
  let f (st : State24) : State24 := ⟨st.q0, st.q1, ⟨v, st.q2.b1, st.q2.b2, st.q2.b3, st.q2.b4,
    st.q2.b5, st.q2.b6, st.q2.b7⟩⟩
  have hInit : initState23 (update x16 15 v) = f (initState23 x16) := by simp [initState23, f]
  rw [show specA55 (update x16 15 v) = f (specA55 x16) from congrArg (fun s ↦ mergeState24
    maskA (step24 stepsA55 (canonA s)) s) hInit]
  generalize specA55 x16 = sA
  rw [show specB55 op (f sA) = f (specB55 op sA) from rfl]
  generalize specB55 op sA = s
  fin_cases i <;> first | contradiction | rfl
theorem y12_ge126 (op : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32) (si neg : Bool)
    (h126 : 126 ≤ xo'.val) :
    let y12 := y12OfState24 specA55 (specB55 op) (pack16 xo' so b si neg)
    (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) = ctrl10OfState24 (step24 (postB55 op)
      (geIn op (sPre2 op xo') si)) ∧ y12 10 = so ∧ y12 11 = false := by
  obtain ⟨hw8_0, h15_so, hCanon⟩ := (pre3_pack16 op xo' so b si neg).2.2.2 h126
  exact ⟨funext fun j ↦ (dite_eq_left j.isLt).trans ((congrFun (ctrl10_mergePost _ _) j).trans
    (congrFun (congrArg (fun s ↦ ctrl10OfState24 (step24 (postB55 op) s)) hCanon) j)), h15_so,
    by simp [y12OfState24, signBitOfState24, hw8_0]⟩
theorem y12OfState2455_of_ge126 (op : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32) (si neg :
  Bool) (h126 : 126 ≤ xo'.val) : y12OfState24 specA55 (specB55 op) (pack16 xo' so b si neg) =
  y12OfState24 specA55 (specB55 op) (pack16 xo' so 0 si false) := funext fun j ↦ by
  obtain ⟨hc1, hs1, hp1⟩ := y12_ge126 op xo' so b si neg h126
  obtain ⟨hc0, hs0, hp0⟩ := y12_ge126 op xo' so 0 si false h126
  by_cases hj10 : j.val < 10
  · exact congrFun (hc1.trans hc0.symm) ⟨j.val, hj10⟩
  · rcases (by omega : j.val = 10 ∨ j.val = 11) with hj | hj
    exacts [(show j = 10 from Fin.ext hj) ▸ hs1.trans hs0.symm, (show j = 11 from Fin.ext hj) ▸
      hp1.trans hp0.symm]
theorem y12_lt126 (op : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32) (si neg : Bool)
    (hxo' : xo'.val < 126) :
    let y := y12OfState24 specA55 (specB55 op) (pack16 xo' so b si neg)
    let r := rDiv14OfRc (rcBitsOfXo (pi145XoEquiv xo'))
    (fun j : Fin 10 ↦ y ⟨j.val, by omega⟩) = ctrl10OfState24 (step24 (postB55 op)
      (twoBodyRIn r b)) ∧ y 10 = si ∧ y 11 = neg := by
  obtain ⟨hw8_0, h15_3, h16_0, hCanon⟩ := (pre3_pack16 op xo' so b si neg).2.2.1 hxo'
  exact ⟨funext fun j ↦ (dite_eq_left j.isLt).trans ((congrFun (ctrl10_mergePost _ _) j).trans
    (congrFun (congrArg (fun s ↦ ctrl10OfState24 (step24 (postB55 op) s))
      (hCanon.trans (tbIn_eq_rIn op xo' hxo' b))) j)), h15_3,
    by simp [y12OfState24, signBitOfState24, hw8_0, h16_0]⟩
/-- Boolean check on `(r : Fin 9, b32 : Fin 32)` for two-body active bit, row index, and phase. -/
def chkTbR (op : Bool) (r : Fin 9) (b32 : Fin 32) : Bool := withR (postB55 op)
  (twoBodyRIn r b32) fun s1 ↦ (bal145ActOf10 actFlip145 (fastCtrl10 s1) == decide (b32.val <
  29)) && (!bal145ActOf10 actFlip145 (fastCtrl10 s1) || (bal145RowIdxOf10 (orbitalOfPi14555 op)
  (fastCtrl10 s1) == ⟨58 + 29 * r.val + min b32.val 28, by omega⟩)) && (bal145PhaseOf10 actFlip145
  (negMaskPi14555 op) (fastCtrl10 s1) == decide (b32.val < 29))
/-- Active predicate on `(op, xo', bit2)` for `126 ≤ xo'.val` under `SiZero`. -/
def oneBodyActive (op : Bool) (xo' : Fin 256) (bit2 : Bool) : Bool := (!bit2) && xor
  (inPass1Pi145Xo xo') (decide (xo'.val < 184) && op)
/-- Boolean check on `(op, xo', bit2)` for `126 ≤ xo'.val` (one-body and `184 ≤ xo'` pad). -/
def chkGe126 (op : Bool) (xo' : Fin 256) (bit2 : Bool) : Bool := withA (pack16 xo' false 0 false
  false) fun st0 ↦ withR (preB55 op) (cPre2 st0) fun sp ↦ withR (postB55 op)
  (geIn op sp bit2) fun s1 ↦ if oneBodyActive op xo' bit2 then (bal145ActOf10 actFlip145
  (fastCtrl10 s1) == true) && (bal145RowIdxOf10 (orbitalOfPi14555 op) (fastCtrl10 s1) == rowIdxOf
  (pi145XoEquiv xo') 0) && (bal145PhaseOf10 actFlip145 (negMaskPi14555 op) (fastCtrl10 s1) ==
  negPhaseOf (pi145XoEquiv xo') 0 1) else !bal145ActOf10 actFlip145 (fastCtrl10 s1)
theorem r55Branch_twoBody (op : Bool) (xo' : Fin 256) (so : Fin 2) (b : Fin 32) (si : Fin 2) (neg :
  Bool) (hk126 : xo'.val < 126) (hb30 : b.val < 30) (hBit : neg = negInPadded (rcBitsOfXo
  (pi145XoEquiv xo')) b) : selectGenCoreBranch 0 (fun m10 ↦ phase2Bal145PhasedBranch actFlip145
  (orbitalOfPi14555 op) (negMaskPi14555 op) (finOfBits 10 m10)) (y12OfState24 specA55
  (specB55 op) (pack16 xo' (decide (so = 1)) b (decide (si = 1)) neg)) = selectBranchUnitary
  (pi145XoEquiv xo') so b si := by
  rw [hBit]
  let xo := pi145XoEquiv xo'
  let negP := negInPadded (rcBitsOfXo xo) b
  let x16 := pack16 xo' (decide (so = 1)) b (decide (si = 1)) negP
  let y12 := y12OfState24 specA55 (specB55 op) x16
  obtain ⟨hf, hs, hy⟩ := y12_lt126 op xo' (decide (so = 1)) b (decide (si = 1)) negP hk126
  let r := rDiv14OfRc (rcBitsOfXo xo)
  have hr : chkTbR op r b = true := by
    have hb : ∀ od : Bool, allPow2 4 0 (fun r ↦ if hr : r < 9 then allPow2 5 0 (fun b ↦ if b < 30
      then chkTbR od ⟨r, hr⟩ ⟨b % 32, Nat.mod_lt _ (by decide)⟩ else true) else true) = true := by
      decide +kernel
    have h1 := allPow2_zero_true (hb op) r.val (by omega)
    rw [dite_eq_left r.isLt] at h1
    have h2 := allPow2_zero_true h1 b.val b.isLt
    rwa [ite_eq_left hb30, mod32_fin b] at h2
  dsimp only [chkTbR] at hr
  rw [withR_eq, fastCtrl10_eq] at hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hr
  rcases hr with ⟨⟨hc0, hrowR⟩, hphR⟩
  have hpi := pi145XoEquiv_hpi xo' (by omega)
  have hn58 : ¬ (pi145XoEquiv xo').val < 58 := by omega
  have h2b : isOneBodyXo xo = false := decide_eq_false hn58
  have hf10B : (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) = ctrl10OfState24 (specB55 op (specA55
    x16)) := funext fun j ↦ dite_eq_left j.isLt
  refine y12_bal145_eq_selectBranchUnitary actFlip145 (orbitalOfPi14555 op) (negMaskPi14555
    op) y12 xo so b si (hf10B.symm ▸ ctrl10_pair8_lt145 op x16) (((congrArg (bal145ActOf10
    actFlip145) hf).trans hc0).trans (by simp [enROf, h2b])) (fun hact ↦ ?_) (hs.trans
    (by simp [sigSelOf, h2b])) ((congrArg₂ xor hy ((congrArg (bal145PhaseOf10 actFlip145
    (negMaskPi14555 op)) hf).trans hphR)).trans (by simp [negP, negPhaseOf, h2b]))
  dsimp only [y12, x16] at hact ⊢
  rw [hf] at hact ⊢
  rw [hact] at hrowR
  exact (by simpa [beq_iff_eq] using hrowR : _ = _).trans (dite_eq_right hn58).symm
theorem r55Branch_twoBody_noNeg (op : Bool) (xo' : Fin 256) (so : Fin 2) (b : Fin 32) (si : Fin 2)
  (hk126 : xo'.val < 126) (hb30 : b.val < 30) : selectGenCoreBranch 0 (fun m10 ↦
  phase2Bal145PhasedBranch actFlip145 (orbitalOfPi14555 op) (negMaskPi14555 op) (finOfBits 10
  m10)) (y12OfState24 specA55 (specB55 op) (pack16 xo' (decide (so = 1)) b (decide (si = 1))
  false)) = (if negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b then negOneUnitary (2 * 58) else 1) *
  selectBranchUnitary (pi145XoEquiv xo') so b si := by
  let neg0 := negInPadded (rcBitsOfXo (pi145XoEquiv xo')) b
  obtain ⟨hf0, hs0, hy0⟩ := y12_lt126 op xo' (decide (so = 1)) b (decide (si = 1)) false hk126
  obtain ⟨hfN, hsN, hyN⟩ := y12_lt126 op xo' (decide (so = 1)) b (decide (si = 1)) neg0 hk126
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
theorem r55Branch_ge126 (op : Bool) (xo' : Fin 256) (so : Fin 2) (b : Fin 32) (si : Fin 2) (neg :
  Bool) (h126 : 126 ≤ xo'.val) : selectGenCoreBranch 0 (fun m10 ↦ phase2Bal145PhasedBranch
  actFlip145 (orbitalOfPi14555 op) (negMaskPi14555 op) (finOfBits 10 m10)) (y12OfState24
  specA55 (specB55 op) (pack16 xo' (decide (so = 1)) b (decide (si = 1)) neg)) = if
  oneBodyActive op xo' (decide (si = 1)) then selectBranchUnitary (pi145XoEquiv xo') so b 1 else 1
  := by
  let xo := pi145XoEquiv xo'
  let b_4 := decide (si = 1)
  let x16 := pack16 xo' (decide (so = 1)) b b_4 neg
  let y12 := y12OfState24 specA55 (specB55 op) x16
  obtain ⟨hf10, hy10, hy11⟩ := y12_ge126 op xo' (decide (so = 1)) b b_4 neg h126
  dsimp only [sPre2] at hf10
  have hf10B : (fun j : Fin 10 ↦ y12 ⟨j.val, by omega⟩) = ctrl10OfState24 (specB55 op (specA55
    x16)) := funext fun j ↦ dite_eq_left j.isLt
  have hc : chkGe126 op xo' b_4 = true := by
    have hb : ∀ od si0 : Bool, allPow2 8 0 (fun q ↦ if 126 ≤ q then chkGe126 od ⟨q % 256, Nat.mod_lt
      _ (by decide)⟩ si0 else true) = true := by decide +kernel
    have h1 := allPow2_zero_true (hb op b_4) xo'.val xo'.isLt
    rwa [ite_eq_left h126, mod256_fin xo'] at h1
  dsimp only [chkGe126] at hc
  rw [withA_eq, withR_eq, withR_eq, fastCtrl10_eq] at hc
  change (if oneBodyActive op xo' b_4 then _ else _) = true at hc
  by_cases hAct : oneBodyActive op xo' b_4 = true
  · rw [ite_eq_left hAct] at hc ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with ⟨⟨hact1, hrow1⟩, hph1⟩
    have hlt184 : xo'.val < 184 := Nat.lt_of_not_le fun hge ↦ absurd hAct (by simp [oneBodyActive,
      show inPass1Pi145Xo xo' = false from decide_eq_false (by omega),
      decide_eq_false (show ¬ xo'.val < 184 by omega)])
    have hxo58 : xo.val < 58 := pi145XoEquiv_h1B xo' h126 hlt184
    have h1b : isOneBodyXo xo = true := decide_eq_true hxo58
    have hxo : pi145XoEquiv xo' = xo := rfl
    exact y12_bal145_eq_selectBranchUnitary actFlip145 (orbitalOfPi14555 op) (negMaskPi14555
      op) y12 xo so b 1 (hf10B.symm ▸ ctrl10_pair8_lt145 op x16) (((congrArg (bal145ActOf10
      actFlip145) hf10).trans hact1).trans (by simp [enROf, h1b])) (fun _ ↦ ((congrArg
      (bal145RowIdxOf10 (orbitalOfPi14555 op)) hf10).trans hrow1).trans
      (by simp [hxo, rowIdxOf, hxo58])) (hy10.trans (by simp [sigSelOf, h1b])) ((congrArg₂ xor hy11
      ((congrArg (bal145PhaseOf10 actFlip145 (negMaskPi14555 op)) hf10).trans hph1)).trans
      (by simp [hxo, negPhaseOf, h1b]))
  · simp only [Bool.not_eq_true] at hAct
    rw [hAct] at hc ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true'] at hc ⊢
    exact y12_bal145_eq_one_of_act_false actFlip145 (orbitalOfPi14555 op) (negMaskPi14555 op)
      y12 (hf10B.symm ▸ ctrl10_pair8_lt145 op x16) ((congrArg (bal145ActOf10 actFlip145)
      hf10).trans hc) hy11
/-- `10`-wire Stage-2 control indices inside `24 = (1 + 16) + 7`: `[10, 8, 11..14, 5..7, 0]`. -/
def routed10Wire24 (u : Fin 10) : Wire 24 := ⟨_, Nat.lt_trans (routed10Wire17 u).isLt (by decide)⟩
/-- Snapshot all `24` bits of `rRouter24` in `β` into a `State24`. -/
def state24OfRouter24 {N : ℕ} (rRouter24 : QRegister 24 N) (β : BitAssignment N) : State24 :=
  let b (u : Wire 24) : Bool := decide (β (rRouter24 u) = 1)
  ⟨⟨b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7⟩, ⟨b 8, b 9, b 10, b 11, b 12, b 13, b 14, b 15⟩,
    ⟨b 16, b 17, b 18, b 19, b 20, b 21, b 22, b 23⟩⟩
theorem get24_state24OfRouter24 {N : ℕ} (rRouter24 : QRegister 24 N) (β : BitAssignment N) (i : Fin
  24) : (state24OfRouter24 rRouter24 β).get24 i = decide (β (rRouter24 i) = 1) := by
  fin_cases i <;> rfl
theorem assign_of_state24OfRouter24_eq {N : ℕ} (rRouter24 : QRegister 24 N) (β : BitAssignment N)
  (st : State24) (h : state24OfRouter24 rRouter24 β = st) (u : Wire 24) : β (rRouter24 u) = if
  st.get24 u then 1 else 0 := by
  rw [← h, get24_state24OfRouter24]
  rcases UnsignedGivens.zmod2_eq_zero_or_one (β (rRouter24 u)) with h0 | h0 <;> rw [h0] <;> decide
/-- Decode a `24`-bit index `c24 : Fin (2 ^ 24)` into `State24`. -/
noncomputable def state24OfFin24 (c24 : Fin (2 ^ 24)) : State24 :=
  let b := bitsOfFin 24 c24
  ⟨⟨b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7⟩, ⟨b 8, b 9, b 10, b 11, b 12, b 13, b 14, b 15⟩,
    ⟨b 16, b 17, b 18, b 19, b 20, b 21, b 22, b 23⟩⟩
theorem state24OfFin24_localIdx_eq {N : ℕ} (rRouter24 : QRegister 24 N) (β : BitAssignment N) :
  state24OfFin24 (UnsignedGivens.localIdx rRouter24 β) = state24OfRouter24 rRouter24 β := by
  have hb (u : Wire 24) : bitsOfFin 24 (UnsignedGivens.localIdx rRouter24 β) u =
    decide (β (rRouter24 u) = 1)
    := congrArg (fun x ↦ decide (x = 1)) (congrFun (basisBits_symm_eq fun i ↦ β (rRouter24 i)) u)
  simp only [state24OfFin24, state24OfRouter24, hb]
theorem get24_initState23_24 (x16 : Fin 16 → Bool) (u : Wire 24) : (initState23 x16).get24 u = if
  u.val = 0 then false else if h17 : u.val < 17 then x16 ⟨u.val - 1, by omega⟩ else false := by
  fin_cases u <;> rfl
/-- Embed `Fin (kInner - 7)` after the `7` router-borrowed inner wires `0..6`. -/
def innerAfter7Idx {kInner : ℕ} (idx : Fin (kInner - 7)) : Fin kInner := ⟨7 + idx.val, by omega⟩
/-- `24`-wire router register `(rScr[0] ++ rCtrl16) ++ rScr[1..7]` (`7` inner borrows). -/
def lowBitRouter24 {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ) (wNegIn : Wire wInner2)
    (rMain :
    QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) (hdisj :
    rMain.DisjointWires rScr) : QRegister 24 N :=
  let r23 := lowBitRouter23 (by omega) wOuter wInner2 wNegIn rMain rScr hdisj
  r23.concat (QRegister.singleton (rScr ⟨7, by omega⟩)) (disjoint_iff.mpr fun u _ heq ↦ by
    change r23 u = rScr ⟨7, by omega⟩ at heq
    rw [lowBitRouter23_apply] at heq
    split_ifs at heq
    exacts [absurd (congrArg Fin.val (rScr.wires.injective heq)) (by simp), hdisj.ne _ _ heq, absurd
      (show 1 + (u.val - 17) = 7 from congrArg Fin.val (rScr.wires.injective heq)) (by omega)])
theorem lowBitRouter24_apply {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ) (wNegIn : Wire
    wInner2)
  (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N) (hdisj :
  rMain.DisjointWires rScr) (u : Wire 24) : lowBitRouter24 hk7 wOuter wInner2 wNegIn rMain rScr
    hdisj u =
  if h1 : u.val = 0 then rScr ⟨0, by omega⟩ else if h17 : u.val < 17 then (rMain.compose
  (rPolyCtrl16InCat wOuter wInner2 wNegIn)) ⟨u.val - 1, by omega⟩ else rScr ⟨1 + (u.val - 17),
    by omega⟩
  := by
  dsimp only [lowBitRouter24]
  by_cases h23 : u.val < 23
  · rw [show u = Fin.castAdd 1 ⟨u.1, h23⟩ from Fin.ext rfl, concat_apply_left, lowBitRouter23_apply]
    rfl
  · have hu23 : u.val = 23 := by omega
    rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    conv_lhs => rw [show u = Fin.natAdd 23 (0 : Fin 1) from Fin.ext (by simp [hu23]),
      concat_apply_right]
    exact congrArg rScr (Fin.ext (by simp [hu23]))
theorem lowBitCoreLayout_wires24 {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ)
    (wNegIn : Wire wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
    (hdisj : rMain.DisjointWires rScr) :
    let L := lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisj
    let rSC := rMain.compose (rSysCatUB wOuter wInner2 11)
    L.rSpin = rSC.compose (block 0 58 (by decide)) ∧
      L.rCat11 = rSC.compose (block (2 * 58) 11 (by decide)) ∧
      L.rInner = rScr.compose (block 1 kInner (by omega)) ∧ ∀ u : Fin 10,
      L.rCtrl10 u = lowBitRouter24 hk7 wOuter wInner2 wNegIn rMain rScr hdisj (routed10Wire24
        u) := by
  have hw6 := lowBitCoreLayout_wires (by omega) wOuter wInner2 wNegIn rMain rScr hdisj
  exact ⟨hw6.1, hw6.2.1, hw6.2.2.1, fun u ↦ (hw6.2.2.2 u).trans ((lowBitRouter23_apply (by omega)
    wOuter wInner2 wNegIn rMain rScr hdisj _).trans (lowBitRouter24_apply hk7 wOuter wInner2 wNegIn
      rMain rScr
    hdisj (routed10Wire24 u)).symm)⟩
theorem lowBit_disj_sysCat_router24 {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ)
    (wNegIn : Wire
  wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
    (hdisj :
  rMain.DisjointWires rScr) : (rMain.compose (rSysCatUB wOuter wInner2 11)).DisjointWires
    (lowBitRouter24
  hk7 wOuter wInner2 wNegIn rMain rScr hdisj) := disjoint_iff.mpr fun k u heq ↦ by
    rw [lowBitRouter24_apply] at heq
    split_ifs at heq
    exacts [hdisj.ne _ _ heq, (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _
      (rMain.wires.injective heq).symm, hdisj.ne _ _ heq]
theorem lowBit_inner7_not_mem_router24 {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ)
    (wNegIn :
  Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
    (hdisj :
  rMain.DisjointWires rScr) (idx : Fin (kInner - 7)) : (lowBitCoreLayout wOuter wInner2 wNegIn rMain
    rScr
  hdisj).rInner (innerAfter7Idx idx) ∉ Set.range (lowBitRouter24 hk7 wOuter wInner2 wNegIn rMain
    rScr
  hdisj).wires := fun ⟨u, hu⟩ ↦ by
  rw [(lowBitCoreLayout_wires24 hk7 wOuter wInner2 wNegIn rMain rScr hdisj).2.2.1, compose_apply,
    lowBitRouter24_apply] at hu
  split_ifs at hu
  · have hv := congrArg Fin.val (rScr.wires.injective hu)
    change 0 = 1 + (7 + idx.val) at hv
    omega
  · exact hdisj.ne _ _ hu
  · have hv := congrArg Fin.val (rScr.wires.injective hu)
    change 1 + (u.val - 17) = 1 + (7 + idx.val) at hv
    omega
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Pi145CompactRouter
end
