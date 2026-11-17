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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.ApexCsaCondStage288

set_option Elab.async false

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModSlot3Exact216Oracle80
@[expose] public section
namespace Slot3Exact216Oracle80
section ConfigSlot3Exact216Oracle80
local instance (priority := 10) instNeZeroTwoPowExact216 (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
section Slot3Exact216
section SubBlockAB
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (wire_ne_of_lt wire_ne_of_gt CliffProg TempPhaseProg cleanRem cleanRem_anti ValidCleanRem
  validCleanRem_mono TempCtx)
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (ctxCliffAlloc ctxCliffAlloc_disjoint ctxCliffAlloc_supports ctxTempBit)
open TwosCompAndWire0Cancel (twosComp8Int)
open ZeroAncillaUSP
  (Mat2Zw HSTGate matId evalList evalList_append zwMul zwConj normSq_zw_eq hstWordCircuit
  hstWordTCount)
open ZeroAncillaUSP
  (wordMatrix2 wordMatrix2_unitary hstWordCircuit_eval_eq_embedMatrix ctrlProbGate
  ctrlProbGate_mulVec_ket_zero)
open ZeroAncillaUSP
  (ctrlProbGate_mulVec_ket_one_zero alpha0 alpha1 norm_sq_alpha0_TH norm_sq_alpha1_TH)
open ZeroAncillaUSP (singleton_embedMatrix_mulVec_ket)
open FastMidKick275Aux FullSysPrepare6Slot
open FullSysMomSlots0135Concrete MomSlots35Slot3ProjNuclear
def wThirdC0 : List HSTGate :=
  [.H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T]
def wThirdC1 : List HSTGate :=
  [.H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T]
def wThirdC2 : List HSTGate :=
  [.H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H]
def wThirdC3 : List HSTGate := [.T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H]
def wThird37 : List HSTGate := wThirdC0 ++ (wThirdC1 ++ (wThirdC2 ++ wThirdC3))
def mThirdC0 : Mat2Zw := ⟨⟨-20, 0, 36, 0⟩, ⟨12, 0, 12, 8⟩, ⟨-8, -12, 0, -12⟩, ⟨0, 36, 0, -20⟩, 11⟩
def mThirdC1 : Mat2Zw :=
  ⟨⟨-64, -704, -768, 736⟩, ⟨96, 32, -672, 64⟩, ⟨32, 96, -64, 672⟩, ⟨704, 64, 736, -768⟩, 21⟩
def mThirdC2 : Mat2Zw :=
  ⟨⟨-6784, 10368, -7296, -57984⟩, ⟨11648, 19328, -13440, -6016⟩, ⟨-19328, -11648, -6016, -13440⟩,
  ⟨10368, -6784, 57984, 7296⟩, 32⟩
def mThird37 : Mat2Zw :=
  ⟨⟨-8192, 224768, 242176, -1024⟩, ⟨-355328, 193024, -512, 46080⟩, ⟨46080, -512, 193024, -355328⟩,
  ⟨1024, -242176, -224768, 8192⟩, 38⟩
theorem evalList_wThird37 : evalList wThird37 matId = mThird37 := by
  dsimp only [wThird37]
  rw [evalList_append wThirdC0 _ matId mThirdC0 rfl,
    evalList_append wThirdC1 _ mThirdC0 mThirdC1 rfl,
    evalList_append wThirdC2 _ mThirdC1 mThirdC2 rfl]
  rfl
private theorem star_mul_self_eq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
theorem norm_sq_wordMatrix2_col0 (w : List HSTGate) : ‖wordMatrix2 w 0 0‖ ^ 2 +
    ‖wordMatrix2 w 1 0‖ ^ 2 = 1 := by
  have h00 := congrArg (fun A ↦ A 0 0) (mul_eq_one_comm.mp (wordMatrix2_unitary w))
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    star_mul_self_eq, ← Complex.ofReal_add] at h00
  exact Complex.ofReal_injective (by simpa using h00)
noncomputable def pThird : ℝ := ‖wordMatrix2 wThird37 1 0‖ ^ 2
theorem pThird_eq : pThird = ((165639880704 : ℝ) + (-52335738880 : ℝ) * Real.sqrt 2) /
    (2 : ℝ) ^ 38 := by
  have hw : wordMatrix2 wThird37 1 0 = ((MeasureBranchHadamardSem.sqrtHalf : ℂ) ^ 38) *
    mThird37.m10.toComplex := by
    rw [wordMatrix2, evalList_wThird37]
    simp [Mat2Zw.toMatrix, mThird37]
  have h2 : (((‖(MeasureBranchHadamardSem.sqrtHalf : ℂ)‖ ^ 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
    rw [← star_mul_self_eq, MeasureBranchHadamardSem.star_sqrtHalf,
      MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf]
  have h3 : ‖(MeasureBranchHadamardSem.sqrtHalf : ℂ)‖ ^ 2 = 1 / 2 :=
    Complex.ofReal_injective (by simpa using h2)
  rw [pThird, hw, norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm 38 2, pow_mul, h3, one_div,
    inv_pow, normSq_zw_eq mThird37.m10,
    show (zwMul mThird37.m10 (zwConj mThird37.m10)).c0 = 165639880704 from rfl,
      show (zwMul mThird37.m10 (zwConj mThird37.m10)).c1 = -52335738880 from rfl]
  push_cast
  ring
noncomputable def qProb (t : Fin 3) : ℝ :=
  if t.val = 0 then (1 - pThird) / 2 else if t.val = 1 then (1 - pThird) / 2 else pThird
theorem qProb_nonneg (t : Fin 3) : 0 ≤ qProb t := by
  have hcol : ‖wordMatrix2 wThird37 0 0‖ ^ 2 + pThird = 1 := norm_sq_wordMatrix2_col0 wThird37
  unfold qProb
  split_ifs
  all_goals linarith [sq_nonneg ‖wordMatrix2 wThird37 0 0‖, show 0 ≤ pThird from sq_nonneg _]
theorem qProb_sum : qProb 0 + qProb 1 + qProb 2 = 1 := by
  dsimp [qProb]
  ring
def s3Trit (a c : ZMod 2) : ℕ := if c.val = 1 then 1 else 2 * a.val
theorem s3Trit_lt_three (a c : ZMod 2) : s3Trit a c < 3 := by
  unfold s3Trit
  have ha := ZMod.val_lt a
  split_ifs
  all_goals omega
noncomputable def qAmp2 (a c : ZMod 2) : ℂ :=
  if a = 0 then if c = 0 then wordMatrix2 wThird37 0 0 * alpha0 [.T, .H]
    else wordMatrix2 wThird37 0 0 * alpha1 [.T, .H]
  else if c = 0 then wordMatrix2 wThird37 1 0 else 0
theorem sum_norm_sq_qAmp2_fiber (t : Fin 3) : (∑ a : ZMod 2, ∑ c : ZMod 2, if (⟨s3Trit a c,
    s3Trit_lt_three a c⟩ : Fin 3) = t then ‖qAmp2 a c‖ ^ 2 else 0) = qProb t := by
  rw [(by decide : (Finset.univ : Finset (ZMod 2)) = {0, 1})]
  simp only [Finset.sum_pair zero_ne_one]
  have hcol : ‖wordMatrix2 wThird37 0 0‖ ^ 2 + pThird = 1 := norm_sq_wordMatrix2_col0 wThird37
  rw [show ‖qAmp2 0 0‖ ^ 2 = (1 - pThird) / 2 by
      rw [show qAmp2 0 0 = wordMatrix2 wThird37 0 0 * alpha0 [.T, .H] from rfl,
        norm_mul, mul_pow, norm_sq_alpha0_TH]
      linarith,
    show ‖qAmp2 0 1‖ ^ 2 = (1 - pThird) / 2 by
      rw [show qAmp2 0 1 = wordMatrix2 wThird37 0 0 * alpha1 [.T, .H] from rfl,
        norm_mul, mul_pow, norm_sq_alpha1_TH]
      linarith,
    show ‖qAmp2 1 0‖ ^ 2 = pThird from rfl, show ‖qAmp2 1 1‖ ^ 2 = 0 by simp [qAmp2]]
  fin_cases t
  all_goals simp [Fin.ext_iff, s3Trit, qProb, ZMod.val_zero]
def cPrepQutrit2 : Circuit 2 :=
  Circuit.H 0 ;;ᶜ Circuit.H 1 ;;ᶜ hstWordCircuit wThird37 0 ;;ᶜ
    Circuit.X 0 ;;ᶜ ctrlProbGate [.T, .H] 0 1 (by decide) ;;ᶜ Circuit.X 0
theorem cPrepQutrit2_count_toff : cPrepQutrit2.count PrimitiveGate.TOFF = 0 := by
  simp [cPrepQutrit2]
theorem cPrepQutrit2_count_t : cPrepQutrit2.count PrimitiveGate.T = 39 := by
  have h37 : hstWordTCount wThird37 = 37 := rfl
  simp [cPrepQutrit2, h37, ZeroAncillaUSP.hstWordTCount]
theorem H_eval_mulVec_involutive {n : ℕ} (q : Wire n) (v : Fin (2 ^ n) →
    ℂ) : (Circuit.H q).eval.1.mulVec ((Circuit.H q).eval.1.mulVec v) = v := by
  suffices h : (Circuit.H q).eval.1 * (Circuit.H q).eval.1 = 1 by
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have hsq : (MeasureBranchHadamardSem.sqrtHalf : ℂ) ^ 2 = 1 / 2 := by
    rw [sq, MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf]
  refine MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ funext fun x ↦ ?_
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, MeasureBranchHadamardSem.ket_H,
    Matrix.mulVec_smul, Matrix.mulVec_add, MeasureBranchHadamardSem.ket_H,
    Matrix.mulVec_smul, MeasureBranchHadamardSem.ket_H]
  simp only [Function.update_self, Function.update_idem, MeasureBranchHadamardSem.bitSign,
    ↓reduceIte, one_ne_zero, one_smul, neg_smul, smul_add, smul_neg, smul_smul,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rcases MeasureBranchHadamardSem.bit_cases (β q) with hb | hb
  all_goals
    simp only [hb, ↓reduceIte, one_ne_zero, ZeroAncillaUSP.upd_eq_self β q hb, neg_mul, one_mul]
    ring_nf
    rw [hsq]
    ring
private theorem wire2_ext {f g : BitAssignment 2} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g :=
  funext (Fin.cases h0 (Fin.cases h1 fun i ↦ i.elim0))
theorem cPrepQutrit2_row_sum (k2 : Fin (2 ^ 2)) : (∑ l2 : Fin (2 ^ 2), cPrepQutrit2.eval.1 k2 l2) =
    (2 : ℂ) * qAmp2 (basisBits 2 k2 0) (basisBits 2 k2 1) := by
  let β00 : BitAssignment 2 := fun _ ↦ 0
  let β10 : BitAssignment 2 := Function.update β00 0 1
  let β01 : BitAssignment 2 := Function.update β00 1 1
  let β11 : BitAssignment 2 := Function.update β10 1 1
  have hk_eval (γ : BitAssignment 2) (x : Fin (2 ^ 2)) : MeasureBranchHadamardSem.ket γ x = if x =
    (basisBitsEquiv 2).symm γ then 1 else 0 := by
    simp [MeasureBranchHadamardSem.ket, basisState, Pi.single_apply]
  have hH10 : (Circuit.H (1 : Wire 2) ;;ᶜ Circuit.H (0 : Wire 2)).eval.1.mulVec
    (MeasureBranchHadamardSem.ket β00) = (1 / 2 : ℂ) • (fun _ ↦ (1 : ℂ)) := by
    rw [MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.ket_H,
      Matrix.mulVec_smul, Matrix.mulVec_add, MeasureBranchHadamardSem.ket_H,
      Matrix.mulVec_smul, MeasureBranchHadamardSem.ket_H]
    dsimp only [MeasureBranchHadamardSem.bitSign]
    rw [s3ItePos (show Function.update β00 1 0 0 = 0 from rfl), one_smul,
      s3ItePos (show β00 1 = 0 from rfl), one_smul,
      s3ItePos (show Function.update β00 1 1 0 = 0 from rfl), one_smul, smul_add, smul_smul,
        smul_smul, MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf]
    funext x
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hk_eval, ← mul_add]
    rw [show (basisBitsEquiv 2).symm (Function.update (Function.update β00 1 0) 0 0) = 0 by decide,
      show (basisBitsEquiv 2).symm (Function.update (Function.update β00 1 0) 0 1) = 1 by decide,
      show (basisBitsEquiv 2).symm (Function.update (Function.update β00 1 1) 0 0) = 2 by decide,
      show (basisBitsEquiv 2).symm (Function.update (Function.update β00 1 1) 0 1) = 3 by decide]
    fin_cases x
    all_goals simp
  have hOnes : (fun _ : Fin (2 ^ 2) ↦
    (1 : ℂ)) = (2 : ℂ) • ((Circuit.H (1 : Wire 2) ;;ᶜ Circuit.H (0 : Wire 2)).eval.1.mulVec
      (MeasureBranchHadamardSem.ket β00)) := by
    rw [hH10, smul_smul, (by norm_num : (2 : ℂ) * (1 / 2 : ℂ) = 1), one_smul]
  rw [show (∑ l2, cPrepQutrit2.eval.1 k2 l2) = (cPrepQutrit2.eval.1.mulVec (fun _ ↦ 1)) k2 by
      simp [Matrix.mulVec, dotProduct],
    hOnes, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  dsimp only [cPrepQutrit2]
  repeat rw [MeasureBranchHadamardSem.eval_seq_mulVec]
  have hb00 : β00 0 = 0 := rfl
  rw [H_eval_mulVec_involutive 0, H_eval_mulVec_involutive 1,
    show MeasureBranchHadamardSem.ket β00 = ZeroAncillaUSP.ket β00 from rfl,
    hstWordCircuit_eval_eq_embedMatrix, singleton_embedMatrix_mulVec_ket,
      ZeroAncillaUSP.ite_pos' hb00, ZeroAncillaUSP.upd_eq_self β00 0 hb00]
  dsimp only [ZeroAncillaUSP.ket]
  have hx10 : Function.update β10 0 (β10 0 + 1) = β00 := wire2_ext (by decide) (by decide)
  have hx11 : Function.update β11 0 (β11 0 + 1) = β01 := wire2_ext (by decide) (by decide)
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    MeasureBranchHadamardSem.ket_X 0 β00, MeasureBranchHadamardSem.ket_X 0 β10,
    show Function.update β00 0 (β00 0 + 1) = β10 from rfl, hx10,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    ctrlProbGate_mulVec_ket_one_zero [.T, .H] 0 1 (by decide) β10 rfl rfl,
    ctrlProbGate_mulVec_ket_zero [.T, .H] 0 1 (by decide) β00 rfl,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_smul, MeasureBranchHadamardSem.ket_X 0 β10,
    MeasureBranchHadamardSem.ket_X 0 β11, MeasureBranchHadamardSem.ket_X 0 β00, hx10, hx11,
    show Function.update β00 0 (β00 0 + 1) = β10 from rfl]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk_eval]
  rw [show (basisBitsEquiv 2).symm β00 = 0 by decide,
    show (basisBitsEquiv 2).symm β10 = 1 by decide,
    show (basisBitsEquiv 2).symm β01 = 2 by decide]
  fin_cases k2
  · simp [qAmp2, show basisBits 2 (0 : Fin (2 ^ 2)) 0 = 0 by decide,
      show basisBits 2 (0 : Fin (2 ^ 2)) 1 = 0 by decide]
  · simp [qAmp2, show basisBits 2 (1 : Fin (2 ^ 2)) 0 = 1 by decide,
      show basisBits 2 (1 : Fin (2 ^ 2)) 1 = 0 by decide]
  · simp [qAmp2, show basisBits 2 (2 : Fin (2 ^ 2)) 0 = 0 by decide,
      show basisBits 2 (2 : Fin (2 ^ 2)) 1 = 1 by decide]
  · simp [qAmp2, show basisBits 2 (3 : Fin (2 ^ 2)) 0 = 1 by decide,
      show basisBits 2 (3 : Fin (2 ^ 2)) 1 = 1 by decide]
abbrev s3QutritPairCore {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (j : Fin 3) : QRegister 2 (momCoreWires mPayload) :=
  QRegister.block (4020 + 2 * j.val) 2 (by have := s3MomCore_ge_4034 hmPay; omega)
noncomputable def uQutrit3 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Unitary
    (2 ^ (momCoreWires mPayload)) := (s3QutritPairCore hmPay 2).embedUnitary cPrepQutrit2.eval
    * ((s3QutritPairCore hmPay 1).embedUnitary cPrepQutrit2.eval * (s3QutritPairCore hmPay
    0).embedUnitary cPrepQutrit2.eval)
noncomputable def uPrep3_216 {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) : Unitary (2 ^ (momCoreWires mPayload)) := uQutrit3 hmPay * uPrep3 hmPay
theorem s3EmbedDisj_mul_apply {mPayload k : ℕ} (rSub : QRegister k (momCoreWires mPayload))
    (U : Unitary (2 ^ k)) (A : Matrix (Fin (2 ^ (momCoreWires mPayload))) (Fin (2 ^
    (momCoreWires mPayload))) ℂ) (z g : Fin (2 ^ (momCoreWires mPayload))) (valZ : ℂ) (hA : ∀
    y : Fin (2 ^ (momCoreWires mPayload)), (∀ w : Wire (momCoreWires mPayload), w ∉ Set.range
    rSub.wires → basisBits (momCoreWires mPayload) y w = basisBits (momCoreWires mPayload) z w) →
      A y g = valZ) : ((rSub.embedUnitary U).1 * A) z g =
    (∑ l : Fin (2 ^ k), U.1 (rSub.extractIndex z) l) * valZ := by
  have hRow (y : Fin (2 ^ (momCoreWires mPayload))) : (rSub.embedUnitary U).1 z y =
    ∑ l : Fin (2 ^ k), U.1 (rSub.extractIndex z) l *
      Slot3CleanPrim.ket
        (Slot3CleanPrim.writeReg (basisBits (momCoreWires mPayload) z) rSub (basisBits k l)) y := by
    have hc :
      ((rSub.embedMatrix U.1ᴴ).mulVec (Slot3CleanPrim.ket (basisBits (momCoreWires mPayload) z))) y
      = (rSub.embedMatrix U.1)ᴴ y z := by
      rw [← Slot3CleanPrim.single_eq_ket, Matrix.mulVec_single_one, Matrix.col_apply,
        QRegister.embedMatrix_conjTranspose]
    have hloc : Slot3CleanPrim.localIdx rSub (basisBits (momCoreWires mPayload) z) =
        rSub.extractIndex z := (basisBitsEquiv k).injective <| funext fun i ↦ by
      change basisBits k _ i = basisBits k _ i
      rw [Slot3CleanPrim.basisBits_symm_apply_s1, QRegister.basisBits_extractIndex]
    have hmv := congrFun (Slot3CleanPrim.embedMatrix_mulVec_ket rSub U.1ᴴ
      (basisBits (momCoreWires mPayload) z)) y
    rw [QRegister.embedUnitary_val, ← star_star (rSub.embedMatrix U.1 z y),
      ← Matrix.conjTranspose_apply, ← hc, hmv, hloc, Finset.sum_apply, star_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', Slot3CleanPrim.ket_apply_eq,
      Matrix.conjTranspose_apply]
    split_ifs
    all_goals simp
  rw [Matrix.mul_apply]
  simp_rw [hRow, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Slot3CleanPrim.ket_apply_eq, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine Finset.sum_congr rfl fun l _ ↦ congrArg (U.1 (rSub.extractIndex z) l * ·) (hA _ ?_)
  intro w hw
  rw [Slot3CleanPrim.basisBits_symm_apply_s1, Slot3CleanPrim.writeReg_apply_of_not_mem _ _ _ _ hw]
noncomputable def s3QutritFactor {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (z : Fin (2 ^ (momCoreWires mPayload))) : ℂ := ((2 : ℂ) * qAmp2 (basisBits 2
    ((s3QutritPairCore hmPay 2).extractIndex z) 0) (basisBits 2 ((s3QutritPairCore hmPay
    2).extractIndex z) 1)) * (((2 : ℂ) * qAmp2 (basisBits 2 ((s3QutritPairCore hmPay
    1).extractIndex z) 0) (basisBits 2 ((s3QutritPairCore hmPay 1).extractIndex z) 1)) * ((2 :
    ℂ) * qAmp2 (basisBits 2 ((s3QutritPairCore hmPay 0).extractIndex z) 0) (basisBits 2
    ((s3QutritPairCore hmPay 0).extractIndex z) 1)))
theorem uPrep3_216_mul_coreHadamard_apply {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z g : Fin (2 ^ (momCoreWires mPayload))) (hgAnc : (momAncReg mPayload).extractIndex g =
      coinSelOutcome (momCoin3Sel mPayload) (fullSysCoinIdx 3)) :
    (uPrep3_216 hmPay * coreHadamardMom mPayload).1 z g = if s3SamePrefix3954 z g then
    s3QutritFactor hmPay z * (∑ l : Fin (2 ^ 33), uOaa33.1 ((s3Coarse33Core
    hmPay).extractIndex z) l) * (((1 / Real.sqrt 2 : ℝ) ^ mPayload : ℝ) : ℂ) else 0 := by
  let baseFn (y : Fin (2 ^ (momCoreWires mPayload))) : ℂ := if s3SamePrefix3954 y g then
      (∑ l : Fin (2 ^ 33), uOaa33.1 ((s3Coarse33Core hmPay).extractIndex y) l) *
      (((1 / Real.sqrt 2 : ℝ) ^ mPayload : ℝ) : ℂ) else 0
  let qF (j : Fin 3) (y : Fin (2 ^ (momCoreWires mPayload))) : ℂ := (2 : ℂ) *
      qAmp2 (basisBits 2 ((s3QutritPairCore hmPay j).extractIndex y) 0)
        (basisBits 2 ((s3QutritPairCore hmPay j).extractIndex y) 1)
  have hnot_pair (j : Fin 3) {w : Wire (momCoreWires mPayload)} (hw : w.val < 4020 + 2 * j.val ∨
    4020 + 2 * j.val + 2 ≤ w.val) :
      w ∉ Set.range (s3QutritPairCore hmPay j).wires := by
    rintro ⟨b, hb⟩
    have hv := congrArg Fin.val hb
    have hb_lt := b.isLt
    dsimp [s3QutritPairCore, MomSlots35Slot3ProjNuclearAlt.qreg_block_apply,
      MomSlots35Slot3ProjNuclearAlt.qreg_block_wires_apply] at hv
    omega
  have hext_eq {k : ℕ} (r : QRegister k (momCoreWires mPayload)) (j : Fin 3)
    {y₁ y₂ : Fin (2 ^ (momCoreWires mPayload))}
      (hd : ∀ idx : Fin k,
        r idx ∉ Set.range (s3QutritPairCore hmPay j).wires)
        (hag : ∀ w ∉ Set.range (s3QutritPairCore hmPay j).wires,
      basisBits (momCoreWires mPayload) y₁ w =
        basisBits (momCoreWires mPayload) y₂ w) : r.extractIndex y₁ = r.extractIndex y₂ :=
    (basisBitsEquiv k).injective <| funext fun idx ↦ by
      change basisBits k _ idx = basisBits k _ idx
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      exact hag (r idx) (hd idx)
  have hBase_congr (j : Fin 3) {y₁ y₂ : Fin (2 ^ (momCoreWires mPayload))}
    (hag : ∀ w ∉ Set.range (s3QutritPairCore hmPay j).wires,
      basisBits (momCoreWires mPayload) y₁ w = basisBits (momCoreWires mPayload) y₂ w) : baseFn y₁ =
        baseFn y₂ := by
    have hpref : s3SamePrefix3954 y₁ g ↔ s3SamePrefix3954 y₂ g :=
      forall₂_congr fun w hw ↦ by rw [hag w (hnot_pair j (Or.inl (by omega)))]
    have hcoarse := hext_eq (s3Coarse33Core hmPay) j (fun idx ↦ hnot_pair j (Or.inl (by
      have := idx.isLt
      dsimp [s3Coarse33Core, MomSlots35Slot3ProjNuclearAlt.qreg_block_apply]
      omega))) hag
    simp only [baseFn, hpref, hcoarse]
  have hPair_congr (j₁ j₂ : Fin 3) (hne : j₁ ≠ j₂) {y₁ y₂ : Fin (2 ^ (momCoreWires mPayload))}
    (hag : ∀ w ∉ Set.range (s3QutritPairCore hmPay j₁).wires,
      basisBits (momCoreWires mPayload) y₁ w = basisBits (momCoreWires mPayload) y₂ w) : qF j₂ y₁ =
        qF j₂ y₂ := by
    have he := hext_eq (s3QutritPairCore hmPay j₂) j₁ (fun b ↦ hnot_pair j₁ (by
      have := b.isLt
      have : j₁.val ≠ j₂.val := fun h ↦ hne (Fin.ext h)
      dsimp [s3QutritPairCore, MomSlots35Slot3ProjNuclearAlt.qreg_block_apply]
      omega)) hag
    dsimp only [qF]
    rw [he]
  let A₀ := (uPrep3 hmPay * coreHadamardMom mPayload).1
  let A₁ := ((s3QutritPairCore hmPay 0).embedUnitary cPrepQutrit2.eval).1 * A₀
  let A₂ := ((s3QutritPairCore hmPay 1).embedUnitary cPrepQutrit2.eval).1 * A₁
  have hStep (j : Fin 3) (M : Matrix _ _ ℂ) (f : _ → ℂ)
      (hf : ∀ y y', (∀ w ∉ Set.range (s3QutritPairCore hmPay j).wires,
        basisBits (momCoreWires mPayload) y' w = basisBits (momCoreWires mPayload) y w) →
        M y' g = f y) (y) :
      (((s3QutritPairCore hmPay j).embedUnitary cPrepQutrit2.eval).1 * M) y g = qF j y * f y :=
    (s3EmbedDisj_mul_apply _ _ M y g (f y) (hf y)).trans (by rw [cPrepQutrit2_row_sum])
  have hA₁ : ∀ y, A₁ y g = qF 0 y * baseFn y := hStep 0 A₀ baseFn fun y y' hag ↦
    (uPrep3_mul_coreHadamard_apply hmPay y' g hgAnc).trans (hBase_congr 0 hag)
  have hA₂ : ∀ y, A₂ y g = qF 1 y * (qF 0 y * baseFn y) :=
    hStep 1 A₁ (fun y ↦ qF 0 y * baseFn y) fun y y' hag ↦ by
      rw [hA₁ y', hPair_congr 1 0 (by decide) hag, hBase_congr 1 hag]
  rw [show (uPrep3_216 hmPay * coreHadamardMom mPayload).1 =
      ((s3QutritPairCore hmPay 2).embedUnitary cPrepQutrit2.eval).1 * A₂ by
    simp only [uPrep3_216, uQutrit3, A₂, A₁, A₀, Submonoid.coe_mul, Matrix.mul_assoc]]
  rw [hStep 2 A₂ (fun y ↦ qF 1 y * (qF 0 y * baseFn y)) (fun y y' hag ↦ by
    rw [hA₂ y', hPair_congr 2 1 (by decide) hag, hPair_congr 2 0 (by decide) hag,
      hBase_congr 2 hag])]
  dsimp only [s3QutritFactor, qF, baseFn]
  split_ifs
  all_goals ring
theorem s3EmbedUnitary_mul {k n : ℕ} (r : QRegister k n) (u v : Unitary (2 ^ k)) : r.embedUnitary
    (u * v) = r.embedUnitary u * r.embedUnitary v :=
  Subtype.ext (by simp [QRegister.embedUnitary_val])
def s3NucleusQ27 (u : Fin 16 → ZMod 2) : ℕ :=
  s3Trit (u 2) (u 3) + 3 * s3Trit (u 4) (u 5) + 9 * s3Trit (u 6) (u 7)
theorem s3NucleusQ27_lt (u : Fin 16 → ZMod 2) : s3NucleusQ27 u < 27 := by
  unfold s3NucleusQ27
  linarith [s3Trit_lt_three (u 2) (u 3), s3Trit_lt_three (u 4) (u 5), s3Trit_lt_three (u 6) (u 7)]
theorem s3Trit_00 : s3Trit 0 0 = 0 := by decide
theorem s3Trit_01 : s3Trit 0 1 = 1 := by decide
theorem s3Trit_10 : s3Trit 1 0 = 2 := by decide
theorem s3Trit_11 : s3Trit 1 1 = 1 := by decide
private theorem fmkTernaryStep_fwd (N : ℕ) (hdst : (280 + 2 * N) + N ≤ 437)
    (aW cW : Wire 437) (ha : aW.val < 280) (hc : cW.val < 280)
    (β β₀ : BitAssignment 437) (hβ : cleanRem 437 (437 - (280 + N)) β)
    (hβ₀ : ∀ w : Wire 437, w.val < 280 → β w = β₀ w)
    (g : ZMod 2) (v_lo : ℕ) (hv_lt : v_lo < N)
    (h_in : ∀ k : ℕ, (hk : k < N) →
      β ⟨280 + k, by omega⟩ = g * (if k = v_lo then 1 else 0)) :
    let K₁ := fmkCtxSplitPrefix 280 (280 + N) N cW hc (by omega) (by omega) N le_rfl
    let K₂ := fmkCtxSplitPrefix 280 (280 + 2 * N) N aW ha (by omega) hdst N le_rfl
    let β₂ := K₂.fwdBits (K₁.fwdBits β)
    cleanRem 437 (437 - (280 + 3 * N)) β₂ ∧
      (∀ w : Wire 437, w.val < 280 → β₂ w = β₀ w) ∧
      (∀ k : ℕ, (hk : k < 3 * N) →
        β₂ ⟨280 + k, by omega⟩ =
          g * (if k = v_lo + N * s3Trit (β₀ aW) (β₀ cW) then 1 else 0)) := by
  intro K₁ K₂ β₂
  obtain ⟨hcl1, hlt1, hu1⟩ := fmkSplitPrefix_unary_contiguous (M := 437) 280 N N cW
    hc le_rfl (by omega) β hβ g v_lo hv_lt (fun _ ↦ hv_lt) h_in
  obtain ⟨hcl2, hSrc2, hDst2, hOut2⟩ :=
    (fmkCtxSplitPrefix_scoped (M := 437) 280 (280 + 2 * N) N aW ha (by omega) hdst N le_rfl).2
      (K₁.fwdBits β) fun w hw ↦ hcl1 w (by omega)
  have ha1 : K₁.fwdBits β aW = β₀ aW := (hlt1 aW ha).trans (hβ₀ aW ha)
  refine ⟨fun w hw ↦ hcl2 w (by omega), fun w hw ↦ (hOut2 w (by omega) (by omega)).trans
    ((hlt1 w hw).trans (hβ₀ w hw)), fun k hk ↦ ?_⟩
  have hK2 : β₂ ⟨280 + k, by omega⟩ = g *
      if k < N then (1 + β₀ aW) * (if k = v_lo + N * (β₀ cW).val then 1 else 0)
      else if k < 2 * N then (if k = v_lo + N * (β₀ cW).val then 1 else 0)
      else β₀ aW * (if k - 2 * N = v_lo + N * (β₀ cW).val then 1 else 0) := by
    dsimp only [β₂, K₂]
    by_cases hk1 : k < N
    · rw [ite_eq_left hk1, hSrc2 k (by omega) hk1, ha1, hu1 k (by omega), hβ₀ cW hc]
      ring
    · rw [ite_eq_right hk1]
      by_cases hk2 : k < 2 * N
      · rw [ite_eq_left hk2, hOut2 ⟨280 + k, by omega⟩ (by dsimp; omega) (by dsimp; omega),
          hu1 k (by omega), hβ₀ cW hc]
      · rw [ite_eq_right hk2, show (⟨280 + k, by omega⟩ : Wire 437) =
            ⟨(280 + 2 * N) + (k - 2 * N), by omega⟩ from Fin.ext (by dsimp; omega),
          hDst2 (k - 2 * N) (by omega) (by omega), ha1, hu1 (k - 2 * N) (by omega), hβ₀ cW hc]
        ring
  rw [hK2]
  refine congrArg (g * ·) ?_
  rcases fmkBit_cases (β₀ aW) with ha | ha
  all_goals rcases fmkBit_cases (β₀ cW) with hc' | hc'
  all_goals
    rw [ha, hc']
    simp only [s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11, ZMod.val_zero, ZMod.val_one, add_zero,
      CharTwo.add_self_eq_zero, one_mul, zero_mul]
    split_ifs
    all_goals first | rfl | omega
def fmkCtxUnary54Ternary : TempCtx 437 :=
  (ctxCliffAlloc (.cnot fmkAccW ⟨280, by decide⟩ (by decide))).append
    ((fmkCtxSplitPrefix 280 281 1 (fmkU16W 3) (by decide) (by decide) (by decide) 1 le_rfl).append
      ((fmkCtxSplitPrefix 280 282 1 (fmkU16W 2) (by decide) (by decide) (by decide) 1 le_rfl).append
        ((fmkCtxSplitPrefix 280 283 3 (fmkU16W 5) (by decide) (by decide) (by decide) 3
          le_rfl).append
          ((fmkCtxSplitPrefix 280 286 3 (fmkU16W 4) (by decide) (by decide) (by decide) 3
            le_rfl).append
            ((fmkCtxSplitPrefix 280 289 9 (fmkU16W 7) (by decide) (by decide) (by decide) 9
              le_rfl).append
              ((fmkCtxSplitPrefix 280 298 9 (fmkU16W 6) (by decide) (by decide) (by decide) 9
                le_rfl).append
                (fmkCtxSplitPrefix 280 307 27 fmkBParW (by decide) (by decide) (by decide) 27
                  le_rfl)))))))

private theorem fmkAppend_props {a b c : ℕ} {F G : TempCtx 437} (hab : b ≤
    c) (hF : F.DisjointFrom (fun w ↦ 107 ≤ w.val ∧ w.val < 149) ∧
    F.SupportsBelowCtx b ∧ fmkTempCtxLiftEx a b F) (hG : G.DisjointFrom (fun w ↦
      107 ≤ w.val ∧ w.val < 149) ∧
    G.SupportsBelowCtx c ∧ fmkTempCtxLiftEx b c G) : (F.append G).DisjointFrom (fun w ↦
      107 ≤ w.val ∧ w.val < 149) ∧
    (F.append G).SupportsBelowCtx c ∧ fmkTempCtxLiftEx a c (F.append G) :=
  ⟨TempCtx.disjointFrom_append hF.1 hG.1,
    TempCtx.supportsBelowCtx_append hab hF.2.1 hG.2.1, fmkTempCtxLiftEx_append hF.2.2 hG.2.2⟩
private theorem fmkCtxUnary54Ternary_fwd (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 280) β) :
    cleanRem 437 (437 - 334) (fmkCtxUnary54Ternary.fwdBits β) ∧ (∀ w : Wire 437,
      w.val < 280 → fmkCtxUnary54Ternary.fwdBits β w = β w) ∧
    (∀ p : ℕ, (hp : p < 54) → fmkCtxUnary54Ternary.fwdBits β ⟨280 + p, by omega⟩ = β fmkAccW *
    (if p = s3NucleusQ27 (fun i ↦ β (fmkU16W i)) + 27 * (β fmkBParW).val then 1 else 0)) := by
  let β0 := (ctxCliffAlloc (.cnot fmkAccW ⟨280, by decide⟩ (by decide))).fwdBits β
  have hβ0_cl : cleanRem 437 (437 - 281) β0 := fun w hw ↦ by
    dsimp [β0, ctxCliffAlloc, TempCtx.fwdBits, CliffProg.eval]
    rw [Function.update_of_ne (wire_ne_of_gt (show 280 < w.val by omega))]
    exact hβ w (by omega)
  have hβ0_lt (w : Wire 437) (hw : w.val < 280) : β0 w = β w :=
    Function.update_of_ne (wire_ne_of_lt hw) _ _
  have hβ0_u (k : ℕ) (hk : k < 1) : β0 ⟨280 + k, by omega⟩ = β fmkAccW * (if k = 0 then 1 else 0) :=
    by
    obtain rfl : k = 0 := by omega
    rw [show (⟨280 + 0, by omega⟩ : Wire 437) = ⟨280, by decide⟩ from rfl]
    dsimp only [β0, ctxCliffAlloc, TempCtx.fwdBits, CliffProg.eval]
    rw [Function.update_self, hβ ⟨280, by decide⟩ (by decide), zero_add, ite_eq_left rfl, mul_one]
  obtain ⟨hcl1, hlt1, hu1⟩ := fmkTernaryStep_fwd 1 (by decide) (fmkU16W 2) (fmkU16W 3)
    (by decide) (by decide) β0 β hβ0_cl hβ0_lt (β fmkAccW) 0 (by decide) hβ0_u
  let β1 := (fmkCtxSplitPrefix 280 282 1 (fmkU16W 2) (by decide) (by decide) (by decide) 1
    le_rfl).fwdBits ((fmkCtxSplitPrefix 280 281 1 (fmkU16W 3) (by decide) (by decide) (by decide)
      1 le_rfl).fwdBits β0)
  obtain ⟨hcl2, hlt2, hu2⟩ := fmkTernaryStep_fwd 3 (by decide) (fmkU16W 4) (fmkU16W 5)
    (by decide) (by decide) β1 β hcl1 hlt1 (β fmkAccW) (s3Trit (β (fmkU16W 2)) (β (fmkU16W 3)))
    (s3Trit_lt_three _ _) fun k hk ↦ by simpa only [zero_add, one_mul] using hu1 k hk
  let β2 := (fmkCtxSplitPrefix 280 286 3 (fmkU16W 4) (by decide) (by decide) (by decide) 3
    le_rfl).fwdBits ((fmkCtxSplitPrefix 280 283 3 (fmkU16W 5) (by decide) (by decide) (by decide)
      3 le_rfl).fwdBits β1)
  obtain ⟨hcl3, hlt3, hu3⟩ := fmkTernaryStep_fwd 9 (by decide) (fmkU16W 6) (fmkU16W 7)
    (by decide) (by decide) β2 β hcl2 hlt2 (β fmkAccW)
    (s3Trit (β (fmkU16W 2)) (β (fmkU16W 3)) + 3 * s3Trit (β (fmkU16W 4)) (β (fmkU16W 5)))
    (by linarith [s3Trit_lt_three (β (fmkU16W 2)) (β (fmkU16W 3)),
                  s3Trit_lt_three (β (fmkU16W 4)) (β (fmkU16W 5))]) hu2
  let β3 := (fmkCtxSplitPrefix 280 298 9 (fmkU16W 6) (by decide) (by decide) (by decide) 9
    le_rfl).fwdBits ((fmkCtxSplitPrefix 280 289 9 (fmkU16W 7) (by decide) (by decide) (by decide)
      9 le_rfl).fwdBits β2)
  let K4 := fmkCtxSplitPrefix 280 307 27 fmkBParW (by decide) (by decide) (by decide) 27 le_rfl
  obtain ⟨hcl4, hlt4, hu4⟩ := fmkSplitPrefix_unary_contiguous (M := 437) 280 27 27 fmkBParW
    (by decide) le_rfl (by decide) β3 hcl3 (β fmkAccW) (s3NucleusQ27 (fun i ↦ β (fmkU16W i)))
    (s3NucleusQ27_lt _) (fun _ ↦ s3NucleusQ27_lt _) hu3
  rw [show fmkCtxUnary54Ternary.fwdBits β = K4.fwdBits β3 by
    dsimp only [fmkCtxUnary54Ternary, K4, β3, β2, β1, β0]
    repeat rw [fmkAppend_fwdBits]]
  have hbpar3 : β3 fmkBParW = β fmkBParW := hlt3 fmkBParW (by decide)
  refine ⟨hcl4, fun w hw ↦ (hlt4 w hw).trans (hlt3 w hw), fun p hp ↦ ?_⟩
  rw [hu4 p hp, hbpar3]
def fmkCtxUnary71Ternary : TempCtx 437 :=
  fmkCtxUnary54Ternary.append
    (fmkCtxSplitPrefix 280 334 18 ⟨92, by decide⟩ (by decide) (by decide) (by decide) 18 le_rfl)
def fmkCtxUnary72Ternary : TempCtx 437 :=
  fmkCtxUnary71Ternary.append
    (ctxTempBit ⟨92, by decide⟩ ⟨91, by decide⟩ fmkWalk10W (by decide) (by decide) (by decide))
private theorem fmkCtxUnary72Ternary_props :
    let mutCat : Wire 437 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
    fmkCtxUnary72Ternary.DisjointFrom mutCat ∧
      fmkCtxUnary72Ternary.SupportsBelowCtx 353 ∧
      fmkTempCtxLiftEx 280 353 fmkCtxUnary72Ternary := by
  intro mutCat
  have hc_supp : (CliffProg.cnot fmkAccW ⟨280, by decide⟩ (by decide)).SupportsBelow 281 :=
    ⟨by decide, by decide⟩
  have hp0 : (ctxCliffAlloc (.cnot fmkAccW ⟨280, by decide⟩ (by decide))).DisjointFrom mutCat ∧
      (ctxCliffAlloc (.cnot fmkAccW ⟨280, by decide⟩ (by decide))).SupportsBelowCtx 281 ∧
      fmkTempCtxLiftEx 280 281 (ctxCliffAlloc (.cnot fmkAccW ⟨280, by decide⟩ (by decide))) :=
    ⟨ctxCliffAlloc_disjoint ⟨by decide, by decide⟩, ctxCliffAlloc_supports hc_supp,
      fmkTempCtxLiftEx_mono (by decide) le_rfl (by decide)
        (fmkTempCtxLiftEx_cliff (cur := 281) (by decide) _ hc_supp)⟩
  have sp (dst N : ℕ) (ctrl : Wire 437) (hc : ctrl.val < 280 := by decide)
      (hsrc : 280 + N ≤ dst := by decide) (hdst : dst + N ≤ 437 := by decide)
      (hnc : ¬ mutCat ctrl := by decide) :
      let S := fmkCtxSplitPrefix 280 dst N ctrl hc hsrc hdst N le_rfl
      S.DisjointFrom mutCat ∧ S.SupportsBelowCtx (dst + N) ∧ fmkTempCtxLiftEx dst (dst + N) S :=
    let ⟨hd, hs⟩ := fmkCtxSplitPrefix_props (mutW := mutCat) 280 dst N ctrl hc hsrc hdst hnc
      (fun _ _ _ ↦ by omega) (fun _ _ _ ↦ by omega) N le_rfl
    ⟨hd, hs, fmkTempCtxLiftEx_mono (Nat.le_add_right _ _) le_rfl hdst
      (fmkCtxSplitPrefix_scoped (M := 437) 280 dst N ctrl hc hsrc hdst N le_rfl).1⟩
  have hp71 := fmkAppend_props (by decide)
    (fmkAppend_props (by decide) hp0 <|
      fmkAppend_props (by decide) (sp 281 1 (fmkU16W 3)) <|
      fmkAppend_props (by decide) (sp 282 1 (fmkU16W 2)) <|
      fmkAppend_props (by decide) (sp 283 3 (fmkU16W 5)) <|
      fmkAppend_props (by decide) (sp 286 3 (fmkU16W 4)) <|
      fmkAppend_props (by decide) (sp 289 9 (fmkU16W 7)) <|
      fmkAppend_props (by decide) (sp 298 9 (fmkU16W 6)) (sp 307 27 fmkBParW))
    (sp 334 18 ⟨92, by decide⟩)
  exact fmkAppend_props (by decide) hp71
    ⟨⟨by decide, by decide, by decide, trivial⟩, ⟨by decide, trivial⟩,
      fmkTempCtxLiftEx_tempBit (cur := 352) (by decide) ⟨92, by decide⟩ ⟨91, by decide⟩
        (by decide) (by decide) (by decide)⟩
private theorem fmkCtxUnary72Ternary_fwdBits (β : BitAssignment 437)
    (hβ : cleanRem 437 (437 - 280) β) :
    let γ := fmkCtxUnary72Ternary.fwdBits β
    let q27 := s3NucleusQ27 (fun i ↦ β (fmkU16W i))
    let bPar := (β fmkBParW).val
    let b0 := β ⟨91, by decide⟩
    let b1 := β ⟨92, by decide⟩
    let leaf (p : ℕ) : ZMod 2 := β fmkAccW * (if p = q27 + 27 * bPar then 1 else 0)
    cleanRem 437 (437 - 353) γ ∧
      (∀ w : Wire 437, w.val < 280 → γ w = β w) ∧
      (∀ (p : ℕ) (hp : p < 18),
        γ ⟨280 + p, by omega⟩ = (1 + b1) * leaf p ∧
        γ ⟨334 + p, by omega⟩ = b1 * leaf p) ∧
      (∀ (p : ℕ), 18 ≤ p → (hp : p < 54) → γ ⟨280 + p, by omega⟩ = leaf p) ∧
      γ fmkWalk10W = b1 * b0 := by
  have hw10 : fmkWalk10W.val = 352 := rfl
  obtain ⟨hcl54, hlt54, hu54⟩ := fmkCtxUnary54Ternary_fwd β hβ
  obtain ⟨hcl71, hsrc71, hdst71, hout71⟩ :=
    (fmkCtxSplitPrefix_scoped (M := 437) 280 334 18 ⟨92, by decide⟩
      (by decide) (by decide) (by decide) 18 le_rfl).2 (fmkCtxUnary54Ternary.fwdBits β) hcl54
  let β71 := fmkCtxUnary71Ternary.fwdBits β
  have hβ71 : β71 = _ := fmkAppend_fwdBits _ _ β
  have hlt71 (w : Wire 437) (hw : w.val < 280) : β71 w = β w := by
    rw [hβ71, hout71 w (by omega) (by omega), hlt54 w hw]
  rw [show fmkCtxUnary72Ternary.fwdBits β =
      Function.update β71 fmkWalk10W (β ⟨92, by decide⟩ * β ⟨91, by decide⟩) by
    rw [fmkCtxUnary72Ternary, fmkAppend_fwdBits]
    change Function.update β71 fmkWalk10W (β71 fmkWalk10W + β71 ⟨92, by decide⟩ * β71 ⟨91,
      by decide⟩) = _
    rw [show β71 fmkWalk10W = 0 from hβ71 ▸ hcl71 fmkWalk10W (by decide),
      zero_add, hlt71 ⟨92, by decide⟩ (by decide), hlt71 ⟨91, by decide⟩ (by decide)]]
  refine ⟨fun w hw ↦ (Function.update_of_ne (wire_ne_of_gt (by omega)) _ _).trans
      (hβ71 ▸ hcl71 w (by omega)),
    fun w hw ↦ (Function.update_of_ne (wire_ne_of_lt (by omega)) _ _).trans (hlt71 w hw),
    fun p hp ↦ ⟨?_, ?_⟩, fun p hlo hhi ↦ ?_, Function.update_self _ _ _⟩
  · rw [Function.update_of_ne (wire_ne_of_lt (show 280 + p < fmkWalk10W.val by omega)), hβ71,
      hsrc71 p (by omega) hp, hlt54 ⟨92, by decide⟩ (by decide), hu54 p (by omega)]
    ring
  · rw [Function.update_of_ne (wire_ne_of_lt (show 334 + p < fmkWalk10W.val by omega)), hβ71,
      hdst71 p (by omega) hp, hlt54 ⟨92, by decide⟩ (by decide), hu54 p (by omega), mul_comm]
  · rw [Function.update_of_ne (wire_ne_of_lt (show 280 + p < fmkWalk10W.val by omega)), hβ71,
      hout71 ⟨280 + p, by omega⟩ (by dsimp; omega) (by dsimp; omega), hu54 p hhi]
def fmkMidKick216FromTables (t0 t1 t2 : Fin 256 → ℕ) : TempPhaseProg 437 :=
  fmkCtxUnary72Ternary.plug (fmkMidKickInner353 t0 t1 t2)
noncomputable def s3LockVal {α : Sort _} (x : α) : α :=
  Classical.choose (⟨x, rfl⟩ : ∃ y : α, y = x)
theorem s3LockVal_eq {α : Sort _} (x : α) : s3LockVal x = x :=
  Classical.choose_spec (⟨x, rfl⟩ : ∃ y : α, y = x)
noncomputable def progMidKick216_437 (cfg : SpecsAux.SpecMirror.Configuration) : TempPhaseProg 437
    :=
  s3LockVal
    (fmkMidKick216FromTables (fmkNegCoordTable cfg 0) (fmkNegCoordTable cfg 1)
    (fmkNegCoordTable cfg 2))
theorem progMidKick216_437_raw_spec (cfg : SpecsAux.SpecMirror.Configuration) :
    let catTop42 : Fin 42 → Wire 437 := fun j ↦ ⟨107 + j.val, by omega⟩
    let u16W : Fin 16 → Wire 437 := fun i ↦ ⟨91 + i.val, by omega⟩
    let accW : Wire 437 := ⟨149, by decide⟩
    ValidCleanRem 437 (437 - 275) (progMidKick216_437 cfg) ∧
    (∀ β, cleanRem 437 (437 - 275) β → (progMidKick216_437 cfg).evalSign β = 0) ∧
    (∀ β,
      cleanRem 437 (437 - 275) β → cleanRem 437 (437 - 275) ((progMidKick216_437 cfg).evalBits β)) ∧
    (∀ β, cleanRem 437 (437 - 275) β → ∀ q : Wire 437, ¬(107 ≤ q.val ∧ q.val < 149) →
      (progMidKick216_437 cfg).evalBits β q = β q) ∧
    (∀ β, cleanRem 437 (437 - 275) β →
      let idx0 : Fin 256 :=
        ⟨(β (u16W 0)).val + 2 * (β (u16W 1)).val +
          4 * s3NucleusQ27 (fun i ↦ β (u16W i)) + 128 * (β ⟨90, by decide⟩).val,
          by have := ZMod.val_lt (β (u16W 0))
             have := ZMod.val_lt (β (u16W 1))
             have := s3NucleusQ27_lt (fun i ↦ β (u16W i))
             have := ZMod.val_lt (β ⟨90, by decide⟩); omega⟩
      let pNew0 : Fin 3 → Fin 256 := fun w ↦
        ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
      let pOld0 : Fin 3 → Fin 256 := fun w ↦
        ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
      ((bitsVal (fun m ↦ (progMidKick216_437 cfg).evalBits β (catTop42 m)) : ℤ)).emod (2 ^ 42 : ℤ) =
        ((bitsVal (fun m ↦ β (catTop42 m)) : ℤ) + ((β accW).val : ℤ) *
          ∑ w : Fin 3, (twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) *
            (fmkNegCoordTable cfg w idx0 : ℤ)).emod (2 ^ 42 : ℤ)) := by
  intro catTop42 u16W accW
  let t0 := fmkNegCoordTable cfg 0
  let t1 := fmkNegCoordTable cfg 1
  let t2 := fmkNegCoordTable cfg 2
  have hp : progMidKick216_437 cfg = fmkMidKick216FromTables t0 t1 t2 := s3LockVal_eq _
  obtain ⟨hdU72, hsU72, hlU72⟩ := fmkCtxUnary72Ternary_props
  obtain ⟨hv280, hSign280, _, hNon280, hCat280⟩ :=
    fmkGraft280_frameC fmkCtxUnary72Ternary hdU72 hsU72 hlU72
      (fmkMidKickInner353 t0 t1 t2) (fmkMidKickInner353_mutC t0 t1 t2)
  have hNonAll (β) (hβ : cleanRem 437 (437 - 275) β) (q : Wire 437) (hq : ¬(107 ≤ q.val ∧ q.val <
    149)) : (progMidKick216_437 cfg).evalBits β q = β q := by
    rw [hp]
    exact hNon280 β (cleanRem_anti (by decide) hβ) q hq
  refine ⟨hp.symm ▸ validCleanRem_mono (by decide) hv280,
    fun β hβ ↦ hp.symm ▸ hSign280 β (cleanRem_anti (by decide) hβ),
    fun β hβ q hq ↦ (hNonAll β hβ q (by omega)).trans (hβ q hq), hNonAll, fun β hβ ↦ ?_⟩
  intro idx0 pNew0 pOld0
  rw [hp]
  have hβ280 : cleanRem 437 (437 - 280) β := cleanRem_anti (by decide) hβ
  obtain ⟨hcl72, hlt72, hpre72, hsuf72, _⟩ := fmkCtxUnary72Ternary_fwdBits β hβ280
  rw [show (fun m : Fin 42 ↦ (fmkMidKick216FromTables t0 t1 t2).evalBits β (catTop42 m)) =
      fun m ↦ (fmkMidKickInner353 t0 t1 t2).evalBits (fmkCtxUnary72Ternary.fwdBits β)
        (fmkCat42W m) from funext fun m ↦ hCat280 β hβ280 m]
  let p0_idx := s3NucleusQ27 (fun i ↦ β (fmkU16W i)) + 27 * (β fmkBParW).val
  have h91 := ZMod.val_lt (β ⟨91, by decide⟩)
  have h92 := ZMod.val_lt (β ⟨92, by decide⟩)
  have hbp := ZMod.val_lt (β fmkBParW)
  have hnq := s3NucleusQ27_lt (fun i ↦ β (fmkU16W i))
  have hidx_eq : fmkIdx0 (β ⟨92, by decide⟩).val p0_idx (β ⟨91, by decide⟩).val = idx0 :=
    Fin.ext <| by
      dsimp only [fmkIdx0, idx0, p0_idx]
      rw [show (β (u16W 0)).val = (β ⟨91, by decide⟩).val from rfl,
        show (β (u16W 1)).val = (β ⟨92, by decide⟩).val from rfl,
        show s3NucleusQ27 (fun i ↦ β (u16W i)) = s3NucleusQ27 (fun i ↦ β (fmkU16W i)) from rfl,
        show (β ⟨90, by decide⟩).val = (β fmkBParW).val from rfl]
      omega
  have hE := fmkMidKickInner353_eval_catC t0 t1 t2 (fmkNegCoordTable_lt cfg 0)
    (fmkNegCoordTable_lt cfg 1) (fmkNegCoordTable_lt cfg 2) β
    (fmkCtxUnary72Ternary.fwdBits β) hcl72 (fun q hq ↦ hlt72 q (by omega)) idx0 pNew0 pOld0
    (fun _ ↦ rfl) (fun _ ↦ rfl) p0_idx (by omega) hidx_eq
    (fun p hp ↦ by
      rw [hlt72 ⟨92, by decide⟩ (by decide)]
      exact hpre72 p hp) hsuf72
  refine hE.trans (congrArg (fun s ↦
    ((bitsVal (fun m ↦ β (catTop42 m)) : ℤ) + ((β accW).val : ℤ) * s).emod (2 ^ 42 : ℤ))
    (Finset.sum_congr rfl fun w _ ↦ ?_))
  fin_cases w
  all_goals rfl
attribute [local irreducible]
  fmkCtxUnary71Ternary fmkCtxUnary72Ternary fmkMidKick216FromTables
end SubBlockAB
namespace Micro216
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 512
local instance (priority := 1000000) instNeZeroTwoPowS3M (k : Nat) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open LocalClassicalPerm
open MeasureBranchHadamardSem (bit_cases)
open scoped Matrix BigOperators
theorem s3mItePos {c : Prop} [h : Decidable c] {α : Sort _} (hc : c) {t e : α} : ite c t e = t :=
  ite_eq_left hc
theorem s3mIteNeg {c : Prop} [h : Decidable c] {α : Sort _} (hnc : ¬ c) {t e : α} : ite c t e = e :=
  ite_eq_right hnc
theorem s3mDitePos {c : Prop} [h : Decidable c] {α : Sort _} (hc : c) {t : c → α} {e : ¬ c →
    α} : dite c t e = t hc := dite_eq_left hc
theorem s3mDiteNeg {c : Prop} [h : Decidable c] {α : Sort _} (hnc : ¬ c) {t : c → α} {e : ¬ c →
    α} : dite c t e = e hnc := dite_eq_right hnc
theorem s3mLtLe {a b c : ℕ} (h1 : a < b) (h2 : b ≤ c) : a < c := Nat.lt_of_lt_of_le h1 h2
theorem s3m_testBit_div_two_pow (x : ℕ) : ∀ (k i : ℕ),
    (x / 2 ^ k).testBit i = x.testBit (k + i)
  | 0, _ => by simp
  | k + 1, i => by
      rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.testBit_succ,
        s3m_testBit_div_two_pow x k (i + 1)]
      exact congrArg _ (by omega)
def s3mTop7Mu (t : ℕ) : ℕ := if t < 2 then 0 else if t < 4 then 1 else if t < 8 then 2 else if
    t < 16 then 3 else if t < 32 then 4 else if t < 64 then 5 else 6
theorem bitsVal_succ_split {W : ℕ} (f : Fin (W + 1) → ZMod 2) : bitsVal f = (f 0).val + 2 *
    bitsVal (fun j ↦ f j.succ) := by
  rw [bitsVal, Fin.sum_univ_succ]
  simp only [Fin.val_zero, _root_.pow_zero, mul_one, bitsVal, Finset.mul_sum]
  congr 1; refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Fin.val_succ, pow_succ]; ring
theorem bitsVal_injective : ∀ {W : ℕ}, Function.Injective (bitsVal (q := W))
  | 0, _, _, _ => funext fun i ↦ Fin.elim0 i
  | W + 1, f, g, h => by
      rw [bitsVal_succ_split f, bitsVal_succ_split g] at h
      have hf0 := ZMod.val_lt (f 0)
      have hg0 := ZMod.val_lt (g 0)
      have h0 : f 0 = g 0 := ZMod.val_injective 2 (by omega)
      rw [h0] at h
      exact funext (Fin.cases h0 (congrFun (@bitsVal_injective W _ _ (by omega))))
theorem bitsVal_eq_of_testBit {W : ℕ} (f : Fin W → ZMod 2) (v : ℕ) (hv : v < 2 ^ W)
    (h : ∀ j : Fin W, f j = if v.testBit j.val then 1 else 0) : bitsVal f = v := by
  induction W generalizing v with
  | zero =>
      obtain rfl : v = 0 := by omega
      simp [bitsVal]
  | succ W ih =>
      have h0 := h 0
      simp only [Fin.val_zero, Nat.testBit_zero] at h0
      rw [bitsVal_succ_split, ih (fun j ↦ f j.succ) (v / 2)
        (Nat.div_lt_of_lt_mul (by rwa [← pow_succ'])) fun j ↦ by
          rw [h j.succ, Fin.val_succ, Nat.testBit_succ], h0]
      split_ifs with hb
      · have := of_decide_eq_true hb
        rw [ZMod.val_one]
        omega
      · have := of_decide_eq_false (Bool.eq_false_of_ne_true hb)
        rw [ZMod.val_zero]
        omega
def cnotVec {M : ℕ} :
    (W : ℕ) → (src dst : Fin W → Wire M) → (∀ j, src j ≠ dst j) → CliffProg M
  | 0, _, _, _ => .nil
  | W + 1, src, dst, hne =>
      .seq (.cnot (src 0) (dst 0) (hne 0))
        (cnotVec W (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem cnotVec_eval {M : ℕ} :
    ∀ (W : ℕ) (src dst : Fin W → Wire M) (hne : ∀ j, src j ≠ dst j)
      (_ : Function.Injective dst) (_ : ∀ i j, src i ≠ dst j)
      (β : BitAssignment M) (w : Wire M),
      (cnotVec W src dst hne).eval β w =
        if h : ∃ j, w = dst j then β w + β (src h.choose) else β w
  | 0, _, _, _, _, _, _, _ => by simp [cnotVec, CliffProg.eval]
  | W + 1, src, dst, hne, hinj, hdisj, β, w => by
      dsimp only [cnotVec, CliffProg.eval]
      let β₁ := Function.update β (dst 0) (β (dst 0) + β (src 0))
      rw [cnotVec_eval W (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ)
        (hinj.comp (Fin.succ_injective W)) (fun i j ↦ hdisj i.succ j.succ) β₁ w]
      by_cases hs : ∃ j : Fin W, w = dst j.succ
      · have hall : ∃ i : Fin (W + 1), w = dst i := ⟨hs.choose.succ, hs.choose_spec⟩
        have hw₁ : β₁ w = β w := hs.choose_spec ▸
          Function.update_of_ne (fun h ↦ Fin.succ_ne_zero _ (hinj h)) _ _
        have hsrc₁ (j : Fin W) : β₁ (src j.succ) = β (src j.succ) :=
          Function.update_of_ne (hdisj j.succ 0) _ _
        simp only [hs, hall, ↓reduceDIte, hw₁, hsrc₁,
          hinj (hall.choose_spec.symm.trans hs.choose_spec)]
      · simp only [hs, ↓reduceDIte]
        by_cases h0 : w = dst 0
        · subst h0
          have hall : ∃ i : Fin (W + 1), dst 0 = dst i := ⟨0, rfl⟩
          simp only [hall, ↓reduceDIte, β₁, Function.update_self, hinj hall.choose_spec.symm]
        · have hall : ¬ ∃ i : Fin (W + 1), w = dst i := fun ⟨i, hi⟩ ↦ by
            cases i using Fin.cases with
            | zero => exact h0 hi
            | succ j => exact hs ⟨j, hi⟩
          simp only [hall, ↓reduceDIte, β₁, Function.update_of_ne h0]
theorem TempCtx.fwdBits_mut {M : ℕ} {mutW : Wire M →
    Prop} {K : TempCtx M} (hDisj : K.DisjointFrom mutW) :
    ∀ (β : BitAssignment M) {w : Wire M}, mutW w → K.fwdBits β w = β w := by
  intro β w hw
  induction K generalizing β with
  | hole => rfl
  | seqPre c K₁ ih =>
      dsimp only [TempCtx.fwdBits]
      rw [ih hDisj.2 (c.eval β), hDisj.1.eval_mut β hw]
  | seqPost K₁ c ih => exact ih hDisj.1 β
  | tempAnd c₁ c₂ anc _ _ _ K₁ ih =>
      dsimp only [TempCtx.fwdBits]
      have hw_ne : w ≠ anc := fun heq ↦ hDisj.2.2.1 (heq ▸ hw)
      rw [ih hDisj.2.2.2 _, Function.update_of_ne hw_ne]
theorem TempCtx.supportsBelowCtx_mono {M b₁ b₂ : ℕ} (hle : b₁ ≤
    b₂) {K : TempCtx M} : K.SupportsBelowCtx b₁ → K.SupportsBelowCtx b₂ := by
  induction K with
  | hole => exact id
  | seqPre c _ ih => exact fun h ↦ ⟨CliffProg.supportsBelow_mono hle h.1, ih h.2⟩
  | seqPost _ c ih => exact fun h ↦ ⟨ih h.1, CliffProg.supportsBelow_mono hle h.2⟩
  | tempAnd _ _ _ _ _ _ _ ih => exact fun h ↦ ⟨Nat.lt_of_lt_of_le h.1 hle, ih h.2⟩
theorem TempCtx.append_countTempAnd {M : ℕ} (F G : TempCtx M) : (F.append G).countTempAnd =
    F.countTempAnd + G.countTempAnd := by
  induction F with
  | hole => dsimp [TempCtx.append, TempCtx.countTempAnd]; omega
  | seqPre _ _ ih => exact ih
  | seqPost _ _ ih => exact ih
  | tempAnd _ _ _ _ _ _ _ ih =>
      dsimp [TempCtx.append, TempCtx.countTempAnd]; omega
theorem TempCtx.append_fwdBits {M : ℕ} (F G : TempCtx M) (β : BitAssignment M) :
    (F.append G).fwdBits β = G.fwdBits (F.fwdBits β) := by
  induction F generalizing β with
  | hole => rfl
  | seqPre c _ ih => exact ih (c.eval β)
  | seqPost _ _ ih => exact ih β
  | tempAnd _ _ _ _ _ _ _ ih => exact ih _
theorem TempCtx.scopedBlock_fwdBits {M rem : ℕ} (K : TempCtx M) (hEx : ∀ q : Wire M, ∃ sQ,
    ScopedBlock M rem sQ (.z q) (K.plug (.z q))) (q : Wire M) :
    ScopedBlock M rem K.fwdBits (.z q) (K.plug (.z q)) where
  valid := (hEx q).choose_spec.valid
  bits := (hEx q).choose_spec.bits
  sign β _ := K.plug_evalSign (.z q) β
theorem TempCtx.fwdBits_eq_of_block {M rem : ℕ} (K : TempCtx M) (u : Wire M) {sU : BitAssignment M →
    BitAssignment M}
    (hBlk : ScopedBlock M rem sU (.z u) (K.plug (.z u))) (β : BitAssignment M)
      (hβ : cleanRem M rem β) : K.fwdBits β u = sU β u := by
  have h1 := K.plug_evalSign (.z u) β
  have h2 := hBlk.sign β hβ
  dsimp [TempPhaseProg.evalSign] at h1 h2
  exact h1.symm.trans h2
def TempCtxLiftEx {M : ℕ} (cur next : ℕ) (K : TempCtx M) : Prop :=
  ∀ {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M},
    ScopedBlock M (M - next) sBody leaf body →
    ∃ sOut, ScopedBlock M (M - cur) sOut leaf (K.plug body)
theorem TempCtxLiftEx.probe {M cur next : ℕ} {K : TempCtx M} (hK : TempCtxLiftEx cur next K)
    (q : Wire M) :
    ScopedBlock M (M - cur) K.fwdBits (.z q) (K.plug (.z q)) :=
  TempCtx.scopedBlock_fwdBits K (fun q ↦ hK (ScopedBlock.z_kick q)) q
theorem TempCtxLiftEx.mono {M cur₀ cur₁ next₀ next₁ : ℕ} {K : TempCtx M}
    (hK : TempCtxLiftEx cur₁ next₀ K)
    (hc : cur₀ ≤ cur₁) (hn : next₀ ≤ next₁) (hM : next₁ ≤ M) :
    TempCtxLiftEx cur₀ next₁ K := fun hBody ↦ by
  have hb' : ScopedBlock M (M - next₀) _ _ _ := ⟨validCleanRem_mono (by omega) hBody.valid,
      fun β hβ ↦ hBody.bits β (cleanRem_anti (by omega) hβ), fun β hβ ↦ hBody.sign β
      (cleanRem_anti (by omega) hβ)⟩
  obtain ⟨sOut, hOut⟩ := hK hb'
  exact ⟨sOut, validCleanRem_mono (by omega) hOut.valid, fun β hβ ↦ hOut.bits β (cleanRem_anti
    (by omega) hβ), fun β hβ ↦ hOut.sign β (cleanRem_anti (by omega) hβ)⟩
theorem TempCtxLiftEx.append {M cur mid next : ℕ} {F G : TempCtx M}
    (hF : TempCtxLiftEx cur mid F) (hG : TempCtxLiftEx mid next G) :
    TempCtxLiftEx cur next (F.append G) := fun hBody ↦ by
  obtain ⟨_, h1⟩ := hG hBody
  obtain ⟨sOut, h2⟩ := hF h1
  exact ⟨sOut, by rwa [TempCtx.append_plug]⟩
theorem TempCtxLiftEx.cliff {M : ℕ} (cur : ℕ) (hcur : cur ≤
    M) (c : CliffProg M) (hc : c.SupportsBelow cur) :
    TempCtxLiftEx cur cur (ctxCliffAlloc c) := fun {leaf body sBody} hBody ↦
  ⟨sBody ∘ c.eval, by
    rw [ctxCliffAlloc_plug]
    exact ScopedBlock.withCliffAlloc_block (by omega) le_rfl c
      (CliffProg.supportsBelow_mono (by omega) hc) hBody⟩
theorem TempCtxLiftEx.tempBit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) : TempCtxLiftEx cur (cur + 1)
    (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2)) :=
  fun {leaf body sBody} hBody ↦
    ⟨fun β ↦ sBody (Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂)), by
      rw [ctxTempBit_plug]
      exact ScopedBlock.withTempBit_block cur hcur c₁ c₂ h12 hc1 hc2 hBody⟩
theorem ctxCliffAlloc_fwdBits {M : ℕ} (cur : ℕ) (hcur : cur ≤ M) (c : CliffProg M)
    (hc : c.SupportsBelow cur) (β : BitAssignment M) (hβ : cleanRem M (M -
      cur) β) : (ctxCliffAlloc c).fwdBits β = c.eval β := by
  exact funext fun u ↦ TempCtx.fwdBits_eq_of_block (ctxCliffAlloc c) u
    (ctxCliffAlloc_plug c (.z u) ▸ ScopedBlock.withCliffAlloc_block (by omega) le_rfl c
      (CliffProg.supportsBelow_mono (by omega) hc) (ScopedBlock.z_kick u)) β hβ
theorem ctxTempBit_fwdBits_clean {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) (β : BitAssignment M)
    (hβ : cleanRem M (M - cur) β) : (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1)
    (wire_ne_of_lt hc2)).fwdBits β = Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂) :=
  funext fun u ↦ TempCtx.fwdBits_eq_of_block _ u
    (ctxTempBit_plug c₁ c₂ ⟨cur, hcur⟩ h12 _ _ (.z u) ▸
      ScopedBlock.withTempBit_block cur hcur c₁ c₂ h12 hc1 hc2 (ScopedBlock.z_kick u)) β hβ
theorem xorBlock_of_ctx {M curStart curEnd W : ℕ} [NeZero M]
    (hEnd : curEnd ≤ M) (hStart : curStart ≤ curEnd)
    (out : Fin W → Wire M) (hout_lt : ∀ j, (out j).val < curStart)
    (hout_inj : Function.Injective out)
    (src : Fin W → Wire M) (hsrc_ge : ∀ j, curStart ≤ (src j).val)
    (K : TempCtx M)
    (hDisj : K.DisjointFrom (fun w ↦ ∃ j, w = out j))
    (hSupp : K.SupportsBelowCtx curEnd)
    (setup : BitAssignment M → BitAssignment M)
    (hProbe : ∀ q : Wire M, ScopedBlock M (M - curStart) setup (.z q) (K.plug (.z q))) :
    let hne : ∀ j, src j ≠ out j := fun j ↦ wire_ne_of_gt (s3mLtLe (hout_lt j) (hsrc_ge j))
    let p := K.plug (.cliff (cnotVec W src out hne))
    ValidCleanRem M (M - curStart) p ∧
      p.countTempAnd = K.countTempAnd ∧
      (∀ β : BitAssignment M, cleanRem M (M - curStart) β → p.evalSign β = 0) ∧
      (∀ β : BitAssignment M, cleanRem M (M - curStart) β → ∀ w : Wire M,
        p.evalBits β w = if h : ∃ j, w = out j then β w + setup β (src h.choose) else β w) := by
  set hne : ∀ j, src j ≠ out j := fun j ↦ wire_ne_of_gt (s3mLtLe (hout_lt j) (hsrc_ge j))
  have hdisj_so : ∀ i j, src i ≠ out j := fun i j ↦ wire_ne_of_gt (s3mLtLe (hout_lt j) (hsrc_ge i))
  obtain ⟨hVal, hCnt, hSgn, hBits⟩ := ScopedBlock.graft_mutating_body (M := M)
    (rem := M - curStart) (curHole := curEnd) (fun w ↦ ∃ j, w = out j) K hDisj hSupp (by omega)
    setup hProbe (.cliff (cnotVec W src out hne)) trivial fun γ w hnw ↦ by
      simp [TempPhaseProg.evalBits, cnotVec_eval W src out hne hout_inj hdisj_so γ w, hnw]
  refine ⟨hVal, by dsimp only [TempPhaseProg.countTempAnd] at hCnt; omega,
    fun β hβ ↦ by simpa [TempPhaseProg.evalSign] using hSgn β hβ, fun β hβ w ↦ ?_⟩
  rw [hBits β hβ w]
  by_cases hw : ∃ j, w = out j
  · simp only [hw, ↓reduceIte, TempPhaseProg.evalBits,
      cnotVec_eval W src out hne hout_inj hdisj_so (setup β) w, ↓reduceDIte]
    have hFwd : setup β w = β w := by
      have h₁ := K.plug_evalSign (.z w) β
      have h₂ := (hProbe w).sign β hβ
      dsimp only [TempPhaseProg.evalSign] at h₁ h₂
      exact h₂.symm.trans (h₁.trans (TempCtx.fwdBits_mut hDisj β hw))
    rw [hFwd]
  · simp [hw]
inductive MicroOp where
  | notW (a : ℕ)
  | cnotW (a b : ℕ)
  | andAlloc (a b : ℕ)
  | zeroAlloc
def microAllocs : List MicroOp → ℕ
  | [] => 0
  | .notW _ :: rest => microAllocs rest
  | .cnotW _ _ :: rest => microAllocs rest
  | .andAlloc _ _ :: rest => 1 + microAllocs rest
  | .zeroAlloc :: rest => 1 + microAllocs rest
def microAnds : List MicroOp → ℕ
  | [] => 0
  | .notW _ :: rest => microAnds rest
  | .cnotW _ _ :: rest => microAnds rest
  | .andAlloc _ _ :: rest => 1 + microAnds rest
  | .zeroAlloc :: rest => microAnds rest
def microValid : ℕ → List MicroOp → Bool
  | _, [] => true
  | top, .notW a :: rest => decide (a < top) && microValid top rest
  | top, .cnotW a b :: rest =>
      decide (a < top) && decide (b < top) && decide (a ≠ b) && microValid top rest
  | top, .andAlloc a b :: rest =>
      decide (a < top) && decide (b < top) && decide (a ≠ b) && microValid (top + 1) rest
  | top, .zeroAlloc :: rest => microValid (top + 1) rest
theorem microValid_notW {top a : ℕ} {rest : List MicroOp} (hv : microValid top (.notW a :: rest) =
    true) : a < top ∧ microValid top rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq] using hv
theorem microValid_cnotW {top a b : ℕ} {rest : List MicroOp}
    (hv : microValid top (.cnotW a b :: rest) = true) :
    a < top ∧ b < top ∧ a ≠ b ∧ microValid top rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
theorem microValid_andAlloc {top a b : ℕ} {rest : List MicroOp}
    (hv : microValid top (.andAlloc a b :: rest) = true) :
    a < top ∧ b < top ∧ a ≠ b ∧ microValid (top + 1) rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0
theorem boolToZMod2_not (x : Bool) : boolToZMod2 (!x) = boolToZMod2 x + 1 := by
  cases x <;> decide
theorem boolToZMod2_xor (x y : Bool) : boolToZMod2 (xor x y) = boolToZMod2 x + boolToZMod2 y := by
  cases x <;> cases y <;> decide
theorem boolToZMod2_and (x y : Bool) : boolToZMod2 (x && y) = boolToZMod2 x * boolToZMod2 y := by
  cases x <;> cases y <;> decide
theorem zmod2_eq_boolToZMod2 (z : ZMod 2) : z = boolToZMod2 (decide (z = 1)) := by
  rcases bit_cases z with rfl | rfl <;> decide
def getBoolAt : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, k + 1 => getBoolAt bs k
def setBoolAt : List Bool → ℕ → Bool → List Bool
  | [], _, _ => []
  | _ :: bs, 0, v => v :: bs
  | b :: bs, k + 1, v => b :: setBoolAt bs k v
theorem length_setBoolAt : ∀ (st : List Bool) (k : ℕ) (v : Bool),
    (setBoolAt st k v).length = st.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: bs, k + 1, v => by simp [setBoolAt, length_setBoolAt bs k v]
theorem getBoolAt_setBoolAt : ∀ (st : List Bool) (k i : ℕ),
    k < st.length → ∀ (v : Bool),
    getBoolAt (setBoolAt st k v) i = if i = k then v else getBoolAt st i
  | [], _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0,0, _, _ => rfl
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1,0, _, _ => rfl
  | _ :: bs, k + 1, i + 1, hk, v => by
      dsimp only [setBoolAt, getBoolAt]
      rw [getBoolAt_setBoolAt bs k i (by simp at hk; omega) v]
      by_cases h : i = k <;> simp [h]
def evalMicroList : ℕ → List MicroOp → List Bool → List Bool
  | _, [], st => st
  | top, .notW a :: rest, st =>
      evalMicroList top rest (setBoolAt st a (!getBoolAt st a))
  | top, .cnotW a b :: rest, st =>
      evalMicroList top rest (setBoolAt st b (xor (getBoolAt st b) (getBoolAt st a)))
  | top, .andAlloc a b :: rest, st =>
      evalMicroList (top + 1) rest (setBoolAt st top (getBoolAt st a && getBoolAt st b))
  | top, .zeroAlloc :: rest, st =>
      evalMicroList (top + 1) rest (setBoolAt st top false)
def setBoolAtStrict : List Bool → ℕ → Bool → List Bool
  | [], _, _ => []
  | _ :: bs, 0, true => true :: bs
  | _ :: bs, 0, false => false :: bs
  | b :: bs, k + 1, v =>
      match setBoolAtStrict bs k v with
      | [] => [b]
      | h :: t => b :: h :: t
theorem setBoolAtStrict_eq : ∀ (st : List Bool) (k : ℕ) (v : Bool),
    setBoolAtStrict st k v = setBoolAt st k v
  | [], _, _ => rfl
  | _ :: _, 0, true => rfl
  | _ :: _, 0, false => rfl
  | b :: bs, k + 1, v => by
      dsimp only [setBoolAtStrict, setBoolAt]
      rw [setBoolAtStrict_eq bs k v]
      cases setBoolAt bs k v <;> rfl
theorem evalMicroList_nil : ∀ (top : ℕ) (ops : List MicroOp),
    evalMicroList top ops [] = []
  | _, [] => rfl
  | top, .notW _ :: rest => evalMicroList_nil top rest
  | top, .cnotW _ _ :: rest => evalMicroList_nil top rest
  | top, .andAlloc _ _ :: rest => evalMicroList_nil (top + 1) rest
  | top, .zeroAlloc :: rest => evalMicroList_nil (top + 1) rest
def evalMicroListStrict : ℕ → List MicroOp → List Bool → List Bool
  | _, [], st => st
  | top, .notW a :: rest, st =>
      match setBoolAtStrict st a (!getBoolAt st a) with
      | [] => []
      | h :: t => evalMicroListStrict top rest (h :: t)
  | top, .cnotW a b :: rest, st =>
      match setBoolAtStrict st b (xor (getBoolAt st b) (getBoolAt st a)) with
      | [] => []
      | h :: t => evalMicroListStrict top rest (h :: t)
  | top, .andAlloc a b :: rest, st =>
      match setBoolAtStrict st top (getBoolAt st a && getBoolAt st b) with
      | [] => []
      | h :: t => evalMicroListStrict (top + 1) rest (h :: t)
  | top, .zeroAlloc :: rest, st =>
      match setBoolAtStrict st top false with
      | [] => []
      | h :: t => evalMicroListStrict (top + 1) rest (h :: t)
private theorem evalMicroListStrict_step (top' : ℕ) (rest : List MicroOp) (l : List Bool)
    (ih : ∀ h t, evalMicroListStrict top' rest (h :: t) = evalMicroList top' rest (h :: t)) :
    (match l with | [] => [] | h :: t => evalMicroListStrict top' rest (h :: t)) =
      evalMicroList top' rest l := by
  cases l with
  | nil => exact (evalMicroList_nil top' rest).symm
  | cons h t => exact ih h t
theorem evalMicroListStrict_eq : ∀ (ops : List MicroOp) (top : ℕ) (st : List Bool),
    evalMicroListStrict top ops st = evalMicroList top ops st
  | [], _, _ => rfl
  | op :: rest, top, st => by
      cases op with
      | notW _ | cnotW _ _ =>
          dsimp only [evalMicroListStrict, evalMicroList]
          rw [setBoolAtStrict_eq]
          exact evalMicroListStrict_step top rest _ fun h t ↦
            evalMicroListStrict_eq rest top (h :: t)
      | andAlloc _ _ | zeroAlloc =>
          dsimp only [evalMicroListStrict, evalMicroList]
          rw [setBoolAtStrict_eq]
          exact evalMicroListStrict_step (top + 1) rest _ fun h t ↦
            evalMicroListStrict_eq rest (top + 1) (h :: t)
def mkBoolList (nIn mask off : ℕ) : ℕ → List Bool
  | 0 => []
  | rem + 1 => (decide (off < nIn) && mask.testBit off) :: mkBoolList nIn mask (off + 1) rem
theorem length_mkBoolList (nIn mask off : ℕ) : ∀ rem : ℕ,
    (mkBoolList nIn mask off rem).length = rem
  | 0 => rfl
  | rem + 1 => by simp [mkBoolList, length_mkBoolList nIn mask (off + 1) rem]
theorem getBoolAt_mkBoolList (nIn mask : ℕ) :
    ∀ (off rem k : ℕ), k < rem →
      getBoolAt (mkBoolList nIn mask off rem) k =
        (decide (off + k < nIn) && mask.testBit (off + k))
  | _, 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | off, _ + 1, 0, _ => by simp [mkBoolList, getBoolAt]
  | off, rem + 1, k + 1, hk => by
      rw [mkBoolList, getBoolAt, getBoolAt_mkBoolList nIn mask (off + 1) rem k (by omega),
        show off + 1 + k = off + (k + 1) by omega]
def initBoolList (nIn len mask : ℕ) : List Bool := mkBoolList nIn mask 0 len
def getNatAt : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getNatAt xs k
def allBelowFrom (pred : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | off, rem + 1 => pred off && allBelowFrom pred (off + 1) rem
theorem allBelowFrom_iff (pred : ℕ → Bool) :
    ∀ (off rem : ℕ), allBelowFrom pred off rem = true ↔ ∀ k < rem, pred (off + k) = true
  | _, 0 => by simp [allBelowFrom]
  | off, rem + 1 => by
      simp only [allBelowFrom, Bool.and_eq_true, allBelowFrom_iff pred (off + 1) rem]
      refine ⟨fun ⟨h0, hr⟩ k hk ↦ ?_, fun h ↦ ⟨by simpa using h 0 (by omega), fun k hk ↦ ?_⟩⟩
      · rcases k with _ | k'
        · simpa using h0
        · simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hr k' (by omega)
      · simpa [Nat.add_assoc, Nat.add_comm 1 k] using h (k + 1) (by omega)
theorem allBelowFrom_add (pred : ℕ → Bool) :
    ∀ (off a b : ℕ),
      allBelowFrom pred off (a + b) = (allBelowFrom pred off a && allBelowFrom pred (off + a) b)
  | _, 0, _ => by simp [allBelowFrom]
  | off, a + 1, b => by
      rw [Nat.succ_add]
      simp only [allBelowFrom, allBelowFrom_add pred (off + 1) a b, Bool.and_assoc]
      have heq : off + 1 + a = off + (a + 1) := by omega
      rw [heq]
theorem allBelowFrom_chunks4 (off sz : ℕ) (pred : ℕ → Bool) (h0 : allBelowFrom pred off sz =
    true) (h1 : allBelowFrom pred (off + sz) sz = true)
    (h2 : allBelowFrom pred (off + 2 * sz) sz = true) (h3 : allBelowFrom pred (off + 3 * sz) sz =
      true) : allBelowFrom pred off (4 * sz) = true := by
  rw [show 4 * sz = (sz + sz) + (sz + sz) by omega, allBelowFrom_add, allBelowFrom_add,
    show off + (sz + sz) = off + 2 * sz by omega, allBelowFrom_add,
    show off + 2 * sz + sz = off + 3 * sz by omega, h0, h1, h2, h3]
  rfl
def allBelow (bound : ℕ) (pred : ℕ → Bool) : Bool := allBelowFrom pred 0 bound
theorem allBelow_iff (bound : ℕ) (pred : ℕ → Bool) : allBelow bound pred = true ↔ ∀ m < bound,
    pred m = true := by
  simpa [allBelow] using allBelowFrom_iff pred 0 bound
def microWire {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ) (hs : nIn ≤ s → cur + (s - nIn) <
    M) : Wire M :=
  if h : s < nIn then inW ⟨s, h⟩ else ⟨cur + (s - nIn), hs (Nat.le_of_not_lt h)⟩
theorem microWire_lt_in {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ) (hs : s < nIn)
    (hb : nIn ≤ s → cur + (s - nIn) < M) : microWire inW cur s hb = inW ⟨s, hs⟩ := by
  dsimp [microWire]; exact s3mDitePos hs
theorem microWire_ge_in {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ) (hs : nIn ≤ s) (hb : nIn ≤
    s → cur + (s - nIn) < M) :
    microWire inW cur s hb = ⟨cur + (s - nIn), hb hs⟩ := by
  dsimp [microWire]; exact s3mDiteNeg (by omega)
theorem microWire_val_lt {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur : ℕ) (hin_lt : ∀ i,
    (inW i).val < cur) {s top : ℕ} (hn : nIn ≤ top) (hs : s < top)
    (hM : cur + (top - nIn) ≤ M) : (microWire inW cur s (fun hge ↦
      by omega)).val < cur + (top - nIn) := by
  by_cases hlt : s < nIn
  · rw [microWire_lt_in inW cur s hlt]
    exact s3mLtLe (hin_lt ⟨s, hlt⟩) (by omega)
  · rw [microWire_ge_in inW cur s (by omega)]
    dsimp; omega
theorem microWire_ne {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) {s₁ s₂ : ℕ} (hne : s₁ ≠ s₂)
    (hb₁ : nIn ≤ s₁ → cur + (s₁ - nIn) < M) (hb₂ : nIn ≤ s₂ → cur + (s₂ - nIn) <
      M) : microWire inW cur s₁ hb₁ ≠ microWire inW cur s₂ hb₂ := by
  by_cases h1 : s₁ < nIn <;> by_cases h2 : s₂ < nIn
  · rw [microWire_lt_in inW cur s₁ h1, microWire_lt_in inW cur s₂ h2]
    intro heq
    exact hne (congrArg Fin.val (hin_inj heq))
  · rw [microWire_lt_in inW cur s₁ h1, microWire_ge_in inW cur s₂ (by omega)]
    exact wire_ne_of_lt (by have := hin_lt ⟨s₁, h1⟩; dsimp; omega)
  · rw [microWire_ge_in inW cur s₁ (by omega), microWire_lt_in inW cur s₂ h2]
    exact wire_ne_of_gt (by have := hin_lt ⟨s₂, h2⟩; dsimp; omega)
  · rw [microWire_ge_in inW cur s₁ (by omega), microWire_ge_in inW cur s₂ (by omega)]
    intro heq
    have hv := congrArg Fin.val heq
    dsimp at hv; omega
def ctxMicroRun {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) :
    (top : ℕ) → (hn : nIn ≤ top) → (ops : List MicroOp) →
    (hv : microValid top ops = true) →
    (hcur : cur + (top - nIn) + microAllocs ops ≤ M) → TempCtx M
  | _, _, [], _, _ => .hole
  | top, hn, .notW a :: rest, hv, hcur =>
      let ha := (microValid_notW hv).1
      let wA := microWire inW cur a (fun hge ↦ by dsimp [microAllocs] at hcur; omega)
      (ctxCliffAlloc (.x wA)).append
        (ctxMicroRun inW hin_inj cur hin_lt top hn rest (microValid_notW hv).2 hcur)
  | top, hn, .cnotW a b :: rest, hv, hcur =>
      let h := microValid_cnotW hv
      let wA := microWire inW cur a (fun hge ↦ by have := h.1; dsimp [microAllocs] at hcur; omega)
      let wB := microWire inW cur b (fun hge ↦ by have := h.2.1; dsimp [microAllocs] at hcur; omega)
      (ctxCliffAlloc (.cnot wA wB (microWire_ne inW hin_inj cur hin_lt h.2.2.1 _ _))).append
        (ctxMicroRun inW hin_inj cur hin_lt top hn rest h.2.2.2 hcur)
  | top, hn, .andAlloc a b :: rest, hv, hcur =>
      let h := microValid_andAlloc hv
      let curTop := cur + (top - nIn)
      let wA := microWire inW cur a (fun hge ↦ by have := h.1; dsimp [microAllocs] at hcur; omega)
      let wB := microWire inW cur b (fun hge ↦ by have := h.2.1; dsimp [microAllocs] at hcur; omega)
      have hwA_lt : wA.val < curTop :=
        microWire_val_lt inW cur hin_lt hn h.1 (by dsimp [microAllocs] at hcur; omega)
      have hwB_lt : wB.val < curTop :=
        microWire_val_lt inW cur hin_lt hn h.2.1 (by dsimp [microAllocs] at hcur; omega)
      (ctxTempBit wA wB ⟨curTop, by dsimp [curTop]; dsimp [microAllocs] at hcur; omega⟩
        (microWire_ne inW hin_inj cur hin_lt h.2.2.1 _ _)
        (wire_ne_of_lt hwA_lt) (wire_ne_of_lt hwB_lt)).append
        (ctxMicroRun inW hin_inj cur hin_lt (top + 1) (by omega) rest h.2.2.2
          (by dsimp [microAllocs] at hcur; omega))
  | top, hn, .zeroAlloc :: rest, hv, hcur =>
      ctxMicroRun inW hin_inj cur hin_lt (top + 1) (by omega) rest
        (by simpa [microValid] using hv)
        (by dsimp [microAllocs] at hcur; omega)
private theorem microWire_not_mut {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ) (hb : nIn ≤ s →
    cur + (s - nIn) < M) {mutW : Wire M → Prop}
    (hni : ∀ i, ¬ mutW (inW i)) (hnc : ∀ w : Wire M,
      cur ≤ w.val → ¬ mutW w) : ¬ mutW (microWire inW cur s hb) := by
  by_cases hlt : s < nIn
  · rw [microWire_lt_in inW cur s hlt]
    exact hni _
  · rw [microWire_ge_in inW cur s (by omega)]
    exact hnc ⟨cur + (s - nIn), hb (by omega)⟩ (Nat.le_add_right _ _)
private def MicroRunSpec {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur top allocR andR : ℕ)
    (hcur : cur + (top - nIn) + allocR ≤ M) (evalR : List Bool →
      List Bool) (K : TempCtx M) : Prop :=
  K.countTempAnd = andR ∧
    (∀ {mutW : Wire M → Prop},
      (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      K.DisjointFrom mutW ∧ K.SupportsBelowCtx (cur + (top - nIn) + allocR)) ∧
    TempCtxLiftEx (cur + (top - nIn)) (cur + (top - nIn) + allocR) K ∧
    (∀ (β : BitAssignment M) (st : List Bool),
      cleanRem M (M - (cur + (top - nIn))) β → st.length = top + allocR →
      (∀ (s : ℕ) (hs : s < top),
        β (microWire inW cur s (fun _ ↦ by omega)) = boolToZMod2 (getBoolAt st s)) →
      cleanRem M (M - (cur + (top - nIn) + allocR)) (K.fwdBits β) ∧
      (∀ w : Wire M, w.val < cur → (∀ i, w ≠ inW i) → K.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hs : s < top + allocR),
        K.fwdBits β (microWire inW cur s (fun _ ↦ by omega)) =
          boolToZMod2 (getBoolAt (evalR st) s)))

private theorem ctxMicroRun_cliff_step {M nIn : ℕ} (inW : Fin nIn →
    Wire M) (hin_inj : Function.Injective inW) (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur)
    {top allocR andR t : ℕ} (hn : nIn ≤ top) (ht : t < top) (hcur : cur + (top - nIn) + allocR ≤ M)
    (c : CliffProg M) (vBool : List Bool → Bool) (K_rest : TempCtx M) (evalR : List Bool →
      List Bool) (hDisjC : ∀ {mutW : Wire M → Prop},
    (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M,
      cur ≤ w.val → ¬ mutW w) → CliffDisjoint mutW c) (hSuppC : c.SupportsBelow (cur + (top - nIn)))
    (hEvalC : ∀ (β : BitAssignment M) (st : List Bool), (∀ (s : ℕ) (hs : s < top),
    β (microWire inW cur s (fun _ ↦
      by omega)) = boolToZMod2 (getBoolAt st s)) → c.eval β =
      Function.update β (microWire inW cur t (fun _ ↦ by omega))
    (boolToZMod2 (vBool st))) (hIH : MicroRunSpec inW cur top allocR andR hcur evalR K_rest) :
      MicroRunSpec inW cur top allocR andR hcur
    (fun st ↦ evalR (setBoolAt st t (vBool st))) ((ctxCliffAlloc c).append K_rest) := by
  obtain ⟨hCnt, hProps, hLiftR, hEvalR⟩ := hIH
  let curTop := cur + (top - nIn)
  let wT := microWire inW cur t (fun _ ↦ by omega)
  have hwT_lt : wT.val < curTop := microWire_val_lt inW cur hin_lt hn ht (by omega)
  refine ⟨by
      rw [TempCtx.append_countTempAnd, hCnt]
      dsimp [ctxCliffAlloc, TempCtx.countTempAnd]
      omega,
    fun hni hnc ↦ ⟨TempCtx.disjointFrom_append
      (ctxCliffAlloc_disjoint (hDisjC hni hnc)) (hProps hni hnc).1,
      TempCtx.supportsBelowCtx_append (c₁ := curTop) (by omega)
        (ctxCliffAlloc_supports hSuppC) (hProps hni hnc).2⟩,
    TempCtxLiftEx.append (TempCtxLiftEx.cliff curTop (by omega) c hSuppC) hLiftR,
    fun β st hβ hlen hst ↦ ?_⟩
  rw [TempCtx.append_fwdBits, ctxCliffAlloc_fwdBits curTop (by omega) c hSuppC β hβ,
    hEvalC β st hst]
  let β₁ := Function.update β wT (boolToZMod2 (vBool st))
  let st₁ := setBoolAt st t (vBool st)
  have hcl₁ : cleanRem M (M - curTop) β₁ := fun w hw ↦ by
    dsimp only [β₁]
    rw [Function.update_of_ne (wire_ne_of_gt (by omega))]
    exact hβ w hw
  have hst₁ (s : ℕ) (hs : s < top) : β₁ (microWire inW cur s (fun _ ↦
    by omega)) = boolToZMod2 (getBoolAt st₁ s) := by
    dsimp only [β₁, st₁]
    rw [getBoolAt_setBoolAt st t s (by omega)]
    by_cases hst_eq : s = t
    · subst hst_eq
      simp only [wT, Function.update_self, ↓reduceIte]
    · rw [Function.update_of_ne (microWire_ne inW hin_inj cur hin_lt hst_eq _ _),
        s3mIteNeg hst_eq, hst s hs]
  obtain ⟨hclOut, hpresOut, hsOut⟩ :=
    hEvalR β₁ st₁ hcl₁ ((length_setBoolAt _ _ _).trans hlen) hst₁
  refine ⟨hclOut, fun w hw hwni ↦ (hpresOut w hw hwni).trans ?_, hsOut⟩
  exact Function.update_of_ne (microWire_not_mut (mutW := (w = ·)) inW cur t _ hwni
    fun _ hge ↦ wire_ne_of_lt (lt_of_lt_of_le hw hge)) _ _
theorem ctxMicroRun_loop {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) :
    ∀ (ops : List MicroOp) (top : ℕ) (hn : nIn ≤ top)
      (hv : microValid top ops = true)
      (hcur : cur + (top - nIn) + microAllocs ops ≤ M),
      let K := ctxMicroRun inW hin_inj cur hin_lt top hn ops hv hcur
      K.countTempAnd = microAnds ops ∧
      (∀ {mutW : Wire M → Prop},
        (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
        K.DisjointFrom mutW ∧ K.SupportsBelowCtx (cur + (top - nIn) + microAllocs ops)) ∧
      TempCtxLiftEx (cur + (top - nIn)) (cur + (top - nIn) + microAllocs ops) K ∧
      (∀ (β : BitAssignment M) (st : List Bool),
        cleanRem M (M - (cur + (top - nIn))) β →
        st.length = top + microAllocs ops →
        (∀ (s : ℕ) (hs : s < top), β (microWire inW cur s (fun hge ↦ by omega)) =
          boolToZMod2 (getBoolAt st s)) →
        cleanRem M (M - (cur + (top - nIn) + microAllocs ops)) (K.fwdBits β) ∧
        (∀ w : Wire M, w.val < cur → (∀ i, w ≠ inW i) → K.fwdBits β w = β w) ∧
        (∀ (s : ℕ) (hs : s < top + microAllocs ops),
          K.fwdBits β (microWire inW cur s (fun hge ↦ by omega)) =
            boolToZMod2 (getBoolAt (evalMicroList top ops st) s))) := by
  intro ops
  induction ops with
  | nil =>
      intro top hn hv hcur
      dsimp only [ctxMicroRun, microAllocs, microAnds, evalMicroList, Nat.add_zero]
      exact ⟨rfl, fun _ _ ↦ ⟨trivial, trivial⟩, fun h ↦ ⟨_, h⟩,
        fun _ _ hβ _ hst ↦ ⟨hβ, fun _ _ _ ↦ rfl, hst⟩⟩
  | cons op rest ih =>
      cases op with
      | notW a =>
          intro top hn hv hcur
          obtain ⟨ha, hvR⟩ := microValid_notW hv
          dsimp only [ctxMicroRun, microAllocs, microAnds, evalMicroList] at hcur ⊢
          let wA := microWire inW cur a (fun _ ↦ by omega)
          exact ctxMicroRun_cliff_step inW hin_inj cur hin_lt hn ha hcur (.x wA)
            (fun st ↦ !getBoolAt st a) _ _
            (fun hni hnc ↦ microWire_not_mut inW cur a _ hni hnc)
            (microWire_val_lt inW cur hin_lt hn ha (by omega))
            (fun β st hst ↦ congrArg (Function.update β wA)
              ((congrArg (· + 1) (hst a ha)).trans (boolToZMod2_not _).symm))
            (ih top hn hvR hcur)
      | cnotW a b =>
          intro top hn hv hcur
          obtain ⟨ha, hb, hab, hvR⟩ := microValid_cnotW hv
          dsimp only [ctxMicroRun, microAllocs, microAnds, evalMicroList] at hcur ⊢
          let wA := microWire inW cur a (fun _ ↦ by omega)
          let wB := microWire inW cur b (fun _ ↦ by omega)
          exact ctxMicroRun_cliff_step inW hin_inj cur hin_lt hn hb hcur
            (.cnot wA wB (microWire_ne inW hin_inj cur hin_lt hab _ _))
            (fun st ↦ xor (getBoolAt st b) (getBoolAt st a)) _ _
            (fun hni hnc ↦ ⟨microWire_not_mut inW cur a _ hni hnc,
              microWire_not_mut inW cur b _ hni hnc⟩)
            ⟨microWire_val_lt inW cur hin_lt hn ha (by omega),
              microWire_val_lt inW cur hin_lt hn hb (by omega)⟩
            (fun β st hst ↦ congrArg (Function.update β wB)
              ((congrArg₂ (· + ·) (hst b hb) (hst a ha)).trans (boolToZMod2_xor _ _).symm))
            (ih top hn hvR hcur)
      | andAlloc a b =>
          intro top hn hv hcur
          obtain ⟨ha, hb, hab, hvR⟩ := microValid_andAlloc hv
          dsimp only [ctxMicroRun, microAllocs, microAnds, evalMicroList] at hcur ⊢
          obtain ⟨hCnt, hProps, hLiftR, hEvalR⟩ := ih (top + 1) (by omega) hvR (by omega)
          let curTop := cur + (top - nIn)
          let wA := microWire inW cur a (fun _ ↦ by omega)
          let wB := microWire inW cur b (fun _ ↦ by omega)
          let anc : Wire M := ⟨curTop, by omega⟩
          have hwA_lt : wA.val < curTop := microWire_val_lt inW cur hin_lt hn ha (by omega)
          have hwB_lt : wB.val < curTop := microWire_val_lt inW cur hin_lt hn hb (by omega)
          have hneAB : wA ≠ wB := microWire_ne inW hin_inj cur hin_lt hab _ _
          refine ⟨by
              rw [TempCtx.append_countTempAnd, hCnt]
              rfl,
            fun hni hnc ↦ ⟨TempCtx.disjointFrom_append
              ⟨microWire_not_mut inW cur a _ hni hnc, microWire_not_mut inW cur b _ hni hnc,
                hnc anc (Nat.le_add_right _ _), trivial⟩ (hProps hni hnc).1,
              TempCtx.supportsBelowCtx_append (c₁ := curTop + 1) (by omega)
                ⟨Nat.lt_succ_self _, trivial⟩
                (TempCtx.supportsBelowCtx_mono (by omega) (hProps hni hnc).2)⟩,
            TempCtxLiftEx.append
              (TempCtxLiftEx.tempBit curTop (by omega) wA wB hneAB hwA_lt hwB_lt)
              (TempCtxLiftEx.mono hLiftR (by omega) (by omega) (by omega)),
            fun β st hβ hlen hst ↦ ?_⟩
          rw [TempCtx.append_fwdBits,
            ctxTempBit_fwdBits_clean curTop (by omega) wA wB hneAB hwA_lt hwB_lt β hβ]
          let β₁ := Function.update β anc (β wA * β wB)
          let st₁ := setBoolAt st top (getBoolAt st a && getBoolAt st b)
          have hcl₁ : cleanRem M (M - (cur + (top + 1 - nIn))) β₁ := fun w hw ↦
            (Function.update_of_ne (wire_ne_of_gt (show curTop < w.val by omega)) _ _).trans
              (hβ w (by omega))
          have hst₁ (s : ℕ) (hs : s < top + 1) :
              β₁ (microWire inW cur s (fun _ ↦ by omega)) = boolToZMod2 (getBoolAt st₁ s) := by
            dsimp only [β₁, st₁]
            rw [getBoolAt_setBoolAt st top s (by omega)]
            by_cases hst_top : s = top
            · subst hst_top
              rw [microWire_ge_in inW cur s hn _, Function.update_self, s3mItePos rfl,
                hst a ha, hst b hb, boolToZMod2_and]
            · rw [Function.update_of_ne (wire_ne_of_lt (microWire_val_lt inW cur hin_lt hn
                (by omega) (by omega))), s3mIteNeg hst_top, hst s (by omega)]
          obtain ⟨hclOut, hpresOut, hsOut⟩ :=
            hEvalR β₁ st₁ hcl₁ ((length_setBoolAt _ _ _).trans (by omega)) hst₁
          refine ⟨cleanRem_anti (by omega) hclOut, fun w hw hwni ↦ (hpresOut w hw hwni).trans
            (Function.update_of_ne (wire_ne_of_lt (lt_of_lt_of_le hw (Nat.le_add_right _ _)))
              _ _), fun s hs ↦ hsOut s (by omega)⟩
      | zeroAlloc =>
          intro top hn hv hcur
          dsimp only [ctxMicroRun, microAllocs, microAnds, evalMicroList] at hcur ⊢
          obtain ⟨hCnt, hProps, hLiftR, hEvalR⟩ :=
            ih (top + 1) (by omega) (by simpa [microValid] using hv) (by omega)
          refine ⟨hCnt,
            fun hni hnc ↦ ⟨(hProps hni hnc).1,
              TempCtx.supportsBelowCtx_mono (by omega) (hProps hni hnc).2⟩,
            TempCtxLiftEx.mono hLiftR (by omega) (by omega) (by omega),
            fun β st hβ hlen hst ↦ ?_⟩
          let st₁ := setBoolAt st top false
          have hst₁ (s : ℕ) (hs : s < top + 1) : β (microWire inW cur s (fun _ ↦
            by omega)) = boolToZMod2 (getBoolAt st₁ s) := by
            dsimp only [st₁]
            rw [getBoolAt_setBoolAt st top s (by omega)]
            by_cases hst_top : s = top
            · subst s
              rw [microWire_ge_in inW cur top hn _, s3mItePos rfl]
              exact hβ _ (show M - (M - (cur + (top - nIn))) ≤ cur + (top - nIn) by omega)
            · rw [s3mIteNeg hst_top]
              exact hst s (by omega)
          obtain ⟨hclOut, hpresOut, hsOut⟩ := hEvalR β st₁
            (cleanRem_anti (by omega) hβ) ((length_setBoolAt _ _ _).trans (by omega)) hst₁
          exact ⟨cleanRem_anti (by omega) hclOut, hpresOut, fun s hs ↦ hsOut s (by omega)⟩
def ctxMicro {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur nAlloc nAnd : ℕ) (hin_lt : ∀ i, (inW i).val < cur) (ops : List MicroOp) (hMeta :
    microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ microAnds ops =
      nAnd) (hcur : cur + nAlloc ≤ M) : TempCtx M :=
  ctxMicroRun inW hin_inj cur hin_lt nIn le_rfl ops hMeta.1 (by have := hMeta.2.1; omega)
theorem bitsVal_testBit_eq {W : ℕ} (g : Fin W → ZMod 2) (i : Fin W) : (bitsVal g).testBit i.val =
    decide (g i = 1) := by
  have hi : g i = if (bitsVal g).testBit i.val then 1 else 0 :=
    congrFun (bitsVal_injective (bitsVal_eq_of_testBit _ (bitsVal g)
      (bitsVal_lt_two_pow g) fun _ ↦ rfl).symm) i
  rw [hi]
  cases (bitsVal g).testBit i.val
  all_goals decide
theorem ctxMicro_scoped {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur nAlloc nAnd : ℕ) (hin_lt : ∀ i, (inW i).val < cur)
    (ops : List MicroOp)
    (hMeta : microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ microAnds ops = nAnd)
    (hcur : cur + nAlloc ≤ M) :
    let K := ctxMicro inW hin_inj cur nAlloc nAnd hin_lt ops hMeta hcur
    K.countTempAnd = nAnd ∧
    (∀ {mutW : Wire M → Prop},
      (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      K.DisjointFrom mutW ∧ K.SupportsBelowCtx (cur + nAlloc)) ∧
    TempCtxLiftEx cur (cur + nAlloc) K ∧
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      let m := bitsVal (fun i ↦ β (inW i))
      let stOut := evalMicroList nIn ops (initBoolList nIn (nIn + nAlloc) m)
      cleanRem M (M - (cur + nAlloc)) (K.fwdBits β) ∧
      (allBelow nIn (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire M, w.val < cur → K.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : nIn ≤ s) (hhi : s < nIn + nAlloc),
        K.fwdBits β ⟨cur + (s - nIn), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) := by
  intro K
  have hAlloc := hMeta.2.1
  obtain ⟨hCnt, hProps, hLift, hEval⟩ :=
    ctxMicroRun_loop inW hin_inj cur hin_lt ops nIn le_rfl hMeta.1 (by omega)
  refine ⟨hCnt.trans hMeta.2.2, fun hni hnc ↦ ⟨(hProps hni hnc).1,
    TempCtx.supportsBelowCtx_mono (by omega) (hProps hni hnc).2⟩,
    TempCtxLiftEx.mono hLift (by omega) (by omega) hcur, fun β hβ ↦ ?_⟩
  let m := bitsVal (fun i ↦ β (inW i))
  have hst₀ (s : ℕ) (hs : s < nIn) : β (microWire inW cur s (fun _ ↦
    by omega)) = boolToZMod2 (getBoolAt (initBoolList nIn (nIn + nAlloc) m) s) := by
    rw [microWire_lt_in inW cur s hs, initBoolList,
      getBoolAt_mkBoolList nIn m 0 (nIn + nAlloc) s (by omega)]
    simp only [Nat.zero_add, hs, decide_true, Bool.true_and]
    rw [show m.testBit s = decide (β (inW ⟨s, hs⟩) = 1) from
      bitsVal_testBit_eq (fun i ↦ β (inW i)) ⟨s, hs⟩, ← zmod2_eq_boolToZMod2]
  obtain ⟨hclOut, hpresOut, hsOut⟩ := hEval β _ (by simpa using hβ)
    (by rw [initBoolList, length_mkBoolList, hAlloc]) hst₀
  refine ⟨cleanRem_anti (by omega) hclOut, fun hall w hw ↦ ?_, fun s hge hlt ↦ ?_⟩
  · by_cases hmem : ∃ i, w = inW i
    · obtain ⟨i, rfl⟩ := hmem
      rw [← microWire_lt_in inW cur i.val i.isLt (fun _ ↦ by omega)]
      dsimp only [K, ctxMicro]
      rw [hsOut i.val (by omega), beq_iff_eq.mp ((allBelow_iff nIn _).mp hall i.val i.isLt),
        bitsVal_testBit_eq (fun j ↦ β (inW j)) i, ← zmod2_eq_boolToZMod2,
        microWire_lt_in inW cur i.val i.isLt]
    · exact hpresOut w hw fun i h ↦ hmem ⟨i, h⟩
  · dsimp only [K, ctxMicro]
    rw [← microWire_ge_in inW cur s hge (fun _ ↦ by omega)]
    exact hsOut s (by omega)
theorem boolToZMod2_decide_eq_one (b : Bool) : decide (boolToZMod2 b = 1) = b := by
  cases b <;> decide
theorem allBelowFrom_chunks2 (off sz : ℕ) (pred : ℕ → Bool) (h0 : allBelowFrom pred off sz =
    true) (h1 : allBelowFrom pred (off + sz) sz = true) :
    allBelowFrom pred off (2 * sz) = true := by
  have s1 : 2 * sz = sz + sz := by omega
  rw [s1, allBelowFrom_add, h0, h1]
  rfl
def u64Bit (w : UInt64) (k : ℕ) : Bool := w.toBitVec.getLsbD k
theorem u64Bit_xor (a b : UInt64) (k : ℕ) : u64Bit (a ^^^ b) k = xor (u64Bit a k) (u64Bit b k) := by
  simp [u64Bit]
theorem u64Bit_and (a b : UInt64) (k : ℕ) : u64Bit (a &&& b) k = (u64Bit a k && u64Bit b k) := by
  simp [u64Bit]
theorem u64Bit_zero (k : ℕ) : u64Bit 0 k = false := by
  simp [u64Bit]
theorem u64Bit_ones_ok : allBelow 64 (fun k ↦ u64Bit 0xFFFFFFFFFFFFFFFF k) = true := by decide
theorem u64Bit_ones (k : ℕ) (hk : k < 64) : u64Bit 0xFFFFFFFFFFFFFFFF k = true :=
  (allBelow_iff 64 _).mp u64Bit_ones_ok k hk
theorem u64Bit_not (a : UInt64) (k : ℕ) (hk : k < 64) : u64Bit (a ^^^ 0xFFFFFFFFFFFFFFFF) k =
    !u64Bit a k := by
  rw [u64Bit_xor, u64Bit_ones k hk]
  cases u64Bit a k <;> rfl
inductive U64Tree where
  | leaf (v : UInt64)
  | node (l r : U64Tree)
def mkU64Tree : ℕ → (ℕ → UInt64) → ℕ → ℕ → U64Tree
  | 0, f, off, _ => .leaf (f off)
  | d + 1, f, off, stride =>
      .node (mkU64Tree d f off (2 * stride))
            (mkU64Tree d f (off + stride) (2 * stride))
def getU64Tree : ℕ → U64Tree → ℕ → UInt64
  | 0, .leaf v, _ => v
  | d + 1, .node l r, idx =>
      if idx % 2 = 0 then getU64Tree d l (idx / 2) else getU64Tree d r (idx / 2)
  | _, _, _ => 0
def setU64Tree : ℕ → U64Tree → ℕ → UInt64 → U64Tree
  | 0, .leaf _, _, v => .leaf v
  | d + 1, .node l r, idx, v =>
      if idx % 2 = 0 then
        match setU64Tree d l (idx / 2) v with
        | .leaf x => .node (.leaf x) r
        | .node a b => .node (.node a b) r
      else
        match setU64Tree d r (idx / 2) v with
        | .leaf x => .node l (.leaf x)
        | .node a b => .node l (.node a b)
  | _, t, _, _ => t
def wfU64Tree : ℕ → U64Tree → Prop
  | 0, .leaf _ => True
  | 0, .node _ _ => False
  | d + 1, .node l r => wfU64Tree d l ∧ wfU64Tree d r
  | _ + 1, .leaf _ => False
theorem wfU64Tree_mk : ∀ (d : ℕ) (f : ℕ → UInt64) (off stride : ℕ),
    wfU64Tree d (mkU64Tree d f off stride)
  | 0, _, _, _ => trivial
  | d + 1, f, off, stride =>
      ⟨wfU64Tree_mk d f off (2 * stride), wfU64Tree_mk d f (off + stride) (2 * stride)⟩
private theorem setU64Tree_eta_left : ∀ (t r : U64Tree),
    (match t with
      | .leaf x => U64Tree.node (.leaf x) r
      | .node a b => U64Tree.node (.node a b) r) = U64Tree.node t r
  | .leaf _, _ | .node _ _, _ => rfl
private theorem setU64Tree_eta_right : ∀ (l t : U64Tree),
    (match t with
      | .leaf x => U64Tree.node l (.leaf x)
      | .node a b => U64Tree.node l (.node a b)) = U64Tree.node l t
  | _, .leaf _ | _, .node _ _ => rfl
theorem wfU64Tree_set : ∀ (d : ℕ) (t : U64Tree) (idx : ℕ) (v : UInt64),
    wfU64Tree d t → wfU64Tree d (setU64Tree d t idx v)
  | 0, .leaf _, _, _, _ => trivial
  | 0, .node _ _, _, _, h => False.elim h
  | _ + 1, .leaf _, _, _, h => False.elim h
  | d + 1, .node l r, idx, v, ⟨hl, hr⟩ => by
      dsimp only [setU64Tree]
      split_ifs
      · rw [setU64Tree_eta_left]
        exact ⟨wfU64Tree_set d l (idx / 2) v hl, hr⟩
      · rw [setU64Tree_eta_right]
        exact ⟨hl, wfU64Tree_set d r (idx / 2) v hr⟩
theorem getU64Tree_mk : ∀ (d : ℕ) (f : ℕ → UInt64) (off stride idx : ℕ),
    idx < 2 ^ d → getU64Tree d (mkU64Tree d f off stride) idx = f (off + idx * stride)
  | 0, f, off, stride, idx, h => by
      obtain rfl : idx = 0 := by simpa using h
      simp [mkU64Tree, getU64Tree]
  | d + 1, f, off, stride, idx, h => by
      have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      dsimp only [mkU64Tree, getU64Tree]
      by_cases hev : idx % 2 = 0
      · rw [s3mItePos hev, getU64Tree_mk d f off (2 * stride) (idx / 2) (by omega)]
        exact congrArg f ((by ring : off + idx / 2 * (2 * stride) = off + (idx / 2 * 2) *
          stride).trans
          (congrArg (fun x ↦ off + x * stride) (by omega)))
      · rw [s3mIteNeg hev, getU64Tree_mk d f (off + stride) (2 * stride) (idx / 2) (by omega)]
        exact congrArg f ((by ring : off + stride + idx / 2 * (2 * stride) = off +
          (idx / 2 * 2 + 1) * stride).trans
          (congrArg (fun x ↦ off + x * stride) (by omega)))
theorem getU64Tree_set : ∀ (d : ℕ) (t : U64Tree) (a b : ℕ) (v : UInt64),
    wfU64Tree d t → a < 2 ^ d → b < 2 ^ d →
    getU64Tree d (setU64Tree d t a v) b = if b = a then v else getU64Tree d t b
  | 0, .leaf _, a, b, _, _, ha, hb => by
      obtain rfl : a = 0 := by simpa using ha
      obtain rfl : b = 0 := by simpa using hb
      rfl
  | 0, .node _ _, _, _, _, h, _, _ => False.elim h
  | _ + 1, .leaf _, _, _, _, h, _, _ => False.elim h
  | d + 1, .node l r, a, b, v, ⟨hl, hr⟩, ha, hb => by
      have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      dsimp only [setU64Tree]
      by_cases ha_ev : a % 2 = 0
      · rw [s3mItePos ha_ev, setU64Tree_eta_left]
        dsimp only [getU64Tree]
        by_cases hb_ev : b % 2 = 0
        · rw [s3mItePos hb_ev, s3mItePos hb_ev,
            getU64Tree_set d l (a / 2) (b / 2) v hl (by omega) (by omega)]
          exact if_congr (by omega) rfl rfl
        · rw [s3mIteNeg hb_ev, s3mIteNeg hb_ev, s3mIteNeg (by omega)]
      · rw [s3mIteNeg ha_ev, setU64Tree_eta_right]
        dsimp only [getU64Tree]
        by_cases hb_ev : b % 2 = 0
        · rw [s3mItePos hb_ev, s3mItePos hb_ev, s3mIteNeg (by omega)]
        · rw [s3mIteNeg hb_ev, s3mIteNeg hb_ev,
            getU64Tree_set d r (a / 2) (b / 2) v hr (by omega) (by omega)]
          exact if_congr (by omega) rfl rfl
def lowU64Word : ℕ → UInt64
  | 0 => 0xAAAAAAAAAAAAAAAA
  | 1 => 0xCCCCCCCCCCCCCCCC
  | 2 => 0xF0F0F0F0F0F0F0F0
  | 3 => 0xFF00FF00FF00FF00
  | 4 => 0xFFFF0000FFFF0000
  | _ => 0xFFFFFFFF00000000
theorem lowU64Word_ok : allBelow 6 (fun i ↦
    allBelow 64 (fun k ↦ u64Bit (lowU64Word i) k == k.testBit i)) = true := by
  decide
def initU64Word (nIn blk i : ℕ) : UInt64 := if i < nIn then if i < 6 then lowU64Word i else if
    blk.testBit (i - 6) then 0xFFFFFFFFFFFFFFFF else 0 else 0
theorem u64Bit_initU64Word (nIn blk i k : ℕ) (hk : k < 64) : u64Bit (initU64Word nIn blk i) k =
    (decide (i < nIn) && (64 * blk + k).testBit i) := by
  dsimp only [initU64Word]
  by_cases hin : i < nIn
  · rw [s3mItePos hin]
    simp only [hin, decide_true, Bool.true_and]
    by_cases hi6 : i < 6
    · rw [s3mItePos hi6]
      have hp : 2 * 2 ^ (5 - i) * 2 ^ i = 64 := by
        rw [mul_assoc, ← pow_add, show 5 - i + i = 5 by omega]
        rfl
      have h64 : 64 * blk + k = k + 2 * (2 ^ (5 - i) * blk) * 2 ^ i := by
        rw [← hp]
        ring
      rw [← Nat.add_zero i, ← s3m_testBit_div_two_pow (64 * blk + k) i 0, h64,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos i),
        Nat.testBit_zero, Nat.add_mul_mod_self_left, ← Nat.testBit_zero,
          s3m_testBit_div_two_pow k i 0, Nat.add_zero]
      exact beq_iff_eq.mp ((allBelow_iff 64 _).mp ((allBelow_iff 6 _).mp lowU64Word_ok i hi6) k hk)
    · rw [s3mIteNeg hi6]
      have hd := s3m_testBit_div_two_pow (64 * blk + k) 6 (i - 6)
      rw [show (64 * blk + k) / 2 ^ 6 = blk from (by omega : (64 * blk + k) / 64 = blk),
        Nat.add_sub_of_le (by omega : 6 ≤ i)] at hd
      rw [← hd]
      cases blk.testBit (i - 6)
      exacts [u64Bit_zero k, u64Bit_ones k hk]
  · rw [s3mIteNeg hin]
    simp [hin, u64Bit_zero]
def evalMicroU64 (d : ℕ) : ℕ → List MicroOp → U64Tree → U64Tree
  | _, [], st => st
  | top, .notW a :: rest, st =>
      let v := getU64Tree d st a ^^^ 0xFFFFFFFFFFFFFFFF
      match setU64Tree d st a v with
      | .leaf x => evalMicroU64 d top rest (.leaf x)
      | .node l r => evalMicroU64 d top rest (.node l r)
  | top, .cnotW a b :: rest, st =>
      let v := getU64Tree d st b ^^^ getU64Tree d st a
      match setU64Tree d st b v with
      | .leaf x => evalMicroU64 d top rest (.leaf x)
      | .node l r => evalMicroU64 d top rest (.node l r)
  | top, .andAlloc a b :: rest, st =>
      let v := getU64Tree d st a &&& getU64Tree d st b
      match setU64Tree d st top v with
      | .leaf x => evalMicroU64 d (top + 1) rest (.leaf x)
      | .node l r => evalMicroU64 d (top + 1) rest (.node l r)
  | top, .zeroAlloc :: rest, st =>
      match setU64Tree d st top 0 with
      | .leaf x => evalMicroU64 d (top + 1) rest (.leaf x)
      | .node l r => evalMicroU64 d (top + 1) rest (.node l r)
theorem evalMicroU64_eta (d top : ℕ) (rest : List MicroOp) (t : U64Tree) :
    (match t with
      | .leaf x => evalMicroU64 d top rest (.leaf x)
      | .node l r => evalMicroU64 d top rest (.node l r)) =
    evalMicroU64 d top rest t := by
  cases t <;> rfl
private theorem u64Bit_set_rel {d idx k : ℕ} {t : U64Tree} {st : List Bool} {wVal : UInt64}
    {bVal : Bool} (ht : wfU64Tree d t) (hlen : st.length ≤ 2 ^ d)
    (hidx : idx < st.length) (hw : u64Bit wVal k = bVal) (hrel : ∀ s < st.length,
      u64Bit (getU64Tree d t s) k = getBoolAt st s) :
    ∀ q < (setBoolAt st idx bVal).length,
      u64Bit (getU64Tree d (setU64Tree d t idx wVal) q) k = getBoolAt (setBoolAt st idx bVal) q :=
      by
  intro q hq
  rw [length_setBoolAt] at hq
  rw [getU64Tree_set d t idx q wVal ht (by omega) (by omega),
    getBoolAt_setBoolAt st idx q hidx]
  by_cases hqi : q = idx
  · subst hqi
    simp [hw]
  · rw [s3mIteNeg hqi, s3mIteNeg hqi, hrel q hq]
theorem u64Bit_evalMicroU64 (d : ℕ) : ∀ (ops : List MicroOp) (top : ℕ) (_ : microValid top ops =
    true)
    (t : U64Tree) (_ : wfU64Tree d t) (st : List Bool) (k : ℕ) (_ : k < 64) (_ : st.length ≤
      2 ^ d) (_ : top + microAllocs ops ≤ st.length)
    (_ : ∀ s < st.length, u64Bit (getU64Tree d t s) k = getBoolAt st s), ∀ s < st.length,
      u64Bit (getU64Tree d (evalMicroU64 d top ops t) s) k =
    getBoolAt (evalMicroList top ops st) s := by
  intro ops
  induction ops with
  | nil => exact fun _ _ _ _ _ _ _ _ _ hrel s hs ↦ hrel s hs
  | cons op rest ih =>
      intro top hv t ht st k hk hlen htop hrel s hs
      have hStep (top' idx : ℕ) (wVal : UInt64) (bVal : Bool) (hvR : microValid top' rest = true)
          (hidx : idx < st.length) (htop' : top' + microAllocs rest ≤ st.length)
          (hw : u64Bit wVal k = bVal) :
          u64Bit (getU64Tree d (evalMicroU64 d top' rest (setU64Tree d t idx wVal)) s) k =
            getBoolAt (evalMicroList top' rest (setBoolAt st idx bVal)) s :=
        ih top' hvR (setU64Tree d t idx wVal) (wfU64Tree_set d t idx wVal ht)
          (setBoolAt st idx bVal) k hk (by rwa [length_setBoolAt]) (by rwa [length_setBoolAt])
          (u64Bit_set_rel ht hlen hidx hw hrel) s (by rwa [length_setBoolAt])
      cases op with
      | notW a =>
          obtain ⟨ha, hvR⟩ := microValid_notW hv
          dsimp only [microAllocs, evalMicroU64, evalMicroList] at htop ⊢
          rw [evalMicroU64_eta]
          refine hStep top a _ _ hvR (by omega) htop ?_
          rw [u64Bit_not _ k hk, hrel a (by omega)]
      | cnotW a b =>
          obtain ⟨ha, hb, _, hvR⟩ := microValid_cnotW hv
          dsimp only [microAllocs, evalMicroU64, evalMicroList] at htop ⊢
          rw [evalMicroU64_eta]
          refine hStep top b _ _ hvR (by omega) htop ?_
          rw [u64Bit_xor, hrel b (by omega), hrel a (by omega)]
      | andAlloc a b =>
          obtain ⟨ha, hb, _, hvR⟩ := microValid_andAlloc hv
          dsimp only [microAllocs, evalMicroU64, evalMicroList] at htop ⊢
          rw [evalMicroU64_eta]
          refine hStep (top + 1) top _ _ hvR (by omega) (by omega) ?_
          rw [u64Bit_and, hrel a (by omega), hrel b (by omega)]
      | zeroAlloc =>
          dsimp only [microAllocs, evalMicroU64, evalMicroList] at htop ⊢
          rw [evalMicroU64_eta]
          exact hStep (top + 1) top 0 false (by simpa [microValid] using hv)
            (by omega) (by omega) (u64Bit_zero k)
theorem u64Bit_evalMicroU64_init (d nIn len : ℕ) (ops : List MicroOp)
    (hv : microValid nIn ops = true) (hlen : len ≤ 2 ^ d) (htop : nIn + microAllocs ops ≤
      len) (blk k : ℕ) (hk : k < 64) (s : ℕ) (hs : s < len) :
    u64Bit (getU64Tree d (evalMicroU64 d nIn ops (mkU64Tree d (initU64Word nIn blk) 0 1)) s) k =
    getBoolAt (evalMicroList nIn ops (initBoolList nIn len (64 * blk + k))) s := by
  have hlen_st : (initBoolList nIn len (64 * blk + k)).length = len := length_mkBoolList _ _ 0 len
  refine u64Bit_evalMicroU64 d ops nIn hv _ (wfU64Tree_mk d _ 0 1) _ k hk
    (by rw [hlen_st]; exact hlen) (by rw [hlen_st]; exact htop) (fun q hq ↦
      ?_) s (by rw [hlen_st]; exact hs)
  rw [hlen_st] at hq
  rw [getU64Tree_mk d _ 0 1 q (by omega)]
  simp only [Nat.zero_add, Nat.mul_one]
  rw [u64Bit_initU64Word nIn blk q k hk]
  dsimp [initBoolList]
  rw [getBoolAt_mkBoolList nIn _ 0 len q hq]
  simp
theorem u64_inputs_preserved (d nIn len blk k : ℕ) (hk : k < 64) (hn : nIn ≤
    len) (t : U64Tree) (st : List Bool)
    (hrel : ∀ s < len, u64Bit (getU64Tree d t s) k = getBoolAt st s) (hIn : allBelow nIn (fun i ↦
      getU64Tree d t i == initU64Word nIn blk i) = true) :
    allBelow nIn (fun i ↦ getBoolAt st i == (64 * blk + k).testBit i) = true := by
  rw [allBelow_iff]
  intro i hi
  have hi_eq : getU64Tree d t i = initU64Word nIn blk i :=
    beq_iff_eq.mp ((allBelow_iff nIn _).mp hIn i hi)
  rw [beq_iff_eq, ← hrel i (by omega), hi_eq, u64Bit_initU64Word nIn blk i k hk]
  simp [hi]
theorem allBelow_64_mul_of_blk (nBlk : ℕ) (pred : ℕ → Bool) (blkPred : ℕ → Bool)
    (hBlk : allBelow nBlk blkPred = true) (hImp : ∀ blk < nBlk, blkPred blk = true → ∀ k < 64,
    pred (64 * blk + k) = true) : allBelow (64 * nBlk) pred = true := by
  rw [allBelow_iff]
  intro m hm
  have hblk_lt : m / 64 < nBlk := by omega
  have hk_lt : m % 64 < 64 := by omega
  have hm_eq : 64 * (m / 64) + m % 64 = m := Nat.div_add_mod m 64
  rw [← hm_eq]
  exact hImp (m / 64) hblk_lt ((allBelow_iff nBlk blkPred).mp hBlk (m / 64) hblk_lt) (m % 64) hk_lt
def top7DecodeExactOps : List MicroOp :=
  [.notW 0, .notW 1, .notW 2, .notW 3, .notW 4, .notW 5, .notW 6, .andAlloc 6 5, .andAlloc 7 4,
  .andAlloc 8 3,
    .andAlloc 9 2, .andAlloc 10 1, .andAlloc 11 0, .notW 0, .notW 1, .notW 2, .notW 3, .notW 4,
      .notW 5, .notW 6, .zeroAlloc, .cnotW 6 13, .zeroAlloc,
    .notW 14, .cnotW 6 14, .cnotW 7 14, .cnotW 8 7, .cnotW 9 8, .cnotW 10 9, .cnotW 11 10, .notW 12]
def or3Ops : List MicroOp :=
  [.notW 0, .notW 1, .andAlloc 0 1, .notW 0, .notW 1, .notW 3, .notW 3, .notW 2, .andAlloc 3 2,
  .notW 3, .notW 2, .notW 4]
def maxMag13Ops : List MicroOp :=
  [.andAlloc 0 6, .andAlloc 1 7, .cnotW 14 13, .andAlloc 2 8, .cnotW 15 13, .andAlloc 3 9,
  .cnotW 16 13,
    .andAlloc 4 10, .cnotW 17 13, .andAlloc 5 11, .cnotW 18 13, .cnotW 12 13]
def signMagOk8Ops : List MicroOp :=
  [.notW 1, .notW 2, .notW 3, .notW 4, .notW 5, .notW 6, .notW 7, .andAlloc 0 1, .andAlloc 8 2,
  .andAlloc 9 3,
    .andAlloc 10 4, .andAlloc 11 5, .andAlloc 12 6, .andAlloc 13 7, .notW 1, .notW 2, .notW 3,
      .notW 4, .notW 5, .notW 6, .notW 7, .notW 14]
def and6Ops : List MicroOp :=
  [.andAlloc 0 1, .andAlloc 6 2, .andAlloc 7 3, .andAlloc 8 4, .andAlloc 9 5]
def top7ExactSelSlots : List ℕ := [11, 10, 9, 8, 7, 14, 13]
theorem top7DecodeExact_meta : microValid 7 top7DecodeExactOps = true ∧
    microAllocs top7DecodeExactOps = 8 ∧ microAnds top7DecodeExactOps = 6 ∧
    top7ExactSelSlots.length = 7 ∧ allBelow 7 (fun k ↦
      decide (7 ≤ getNatAt top7ExactSelSlots k) && decide (getNatAt top7ExactSelSlots k < 15)) =
      true ∧
    allBelow 7 (fun i ↦
      allBelow 7 (fun j ↦
      decide (i = j) || decide (getNatAt top7ExactSelSlots i ≠ getNatAt top7ExactSelSlots j))) =
      true := by decide
theorem top7DecodeExact_meta3 : microValid 7 top7DecodeExactOps = true ∧ microAllocs
    top7DecodeExactOps = 8 ∧ microAnds top7DecodeExactOps = 6 := ⟨top7DecodeExact_meta.1,
    top7DecodeExact_meta.2.1, top7DecodeExact_meta.2.2.1⟩
theorem top7ExactSelSlots_bounds (k : Fin 7) : 7 ≤ getNatAt top7ExactSelSlots k.val ∧
    getNatAt top7ExactSelSlots k.val < 15 := by
  have hk := (allBelow_iff 7 _).mp top7DecodeExact_meta.2.2.2.2.1 k.val k.isLt
  simpa [Bool.and_eq_true, decide_eq_true_eq] using hk
theorem top7ExactSelSlots_inj : Function.Injective (fun k : Fin 7 ↦
    getNatAt top7ExactSelSlots k.val) := by
  intro i j hij
  have h2 :=
    (allBelow_iff 7 _).mp ((allBelow_iff 7 _).mp top7DecodeExact_meta.2.2.2.2.2 i.val i.isLt) j.val
    j.isLt
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
  exact h2.elim Fin.ext (absurd hij)
def top7DecodeExactCheckStrict (m : ℕ) : Bool :=
  let st := evalMicroListStrict 7 top7DecodeExactOps (initBoolList 7 15 m)
  allBelow 7 (fun i ↦ getBoolAt st i == m.testBit i) &&
    allBelow 7 (fun a ↦ getBoolAt st (getNatAt top7ExactSelSlots a) == decide (s3mTop7Mu m = a)) &&
    (getBoolAt st 12 == decide (0 < m))
theorem top7DecodeExactStrict_eval_ok : allBelow 128 top7DecodeExactCheckStrict = true :=
  allBelowFrom_chunks4 0 32 top7DecodeExactCheckStrict
    (allBelowFrom_chunks4 0 8 _ (by decide) (by decide) (by decide) (by decide))
    (allBelowFrom_chunks4 32 8 _ (by decide) (by decide) (by decide) (by decide))
    (allBelowFrom_chunks4 64 8 _ (by decide) (by decide) (by decide) (by decide))
    (allBelowFrom_chunks4 96 8 _ (by decide) (by decide) (by decide) (by decide))
theorem or3_meta : microValid 3 or3Ops = true ∧ microAllocs or3Ops = 2 ∧ microAnds or3Ops = 2 := by
  decide
def or3CheckStrict (m : ℕ) : Bool :=
  let st := evalMicroListStrict 3 or3Ops (initBoolList 3 5 m)
  allBelow 3 (fun i ↦
    getBoolAt st i ==
    m.testBit i) && (getBoolAt st 4 == (m.testBit 0 || m.testBit 1 || m.testBit 2))
theorem or3Strict_eval_ok : allBelow 8 or3CheckStrict = true := by decide
theorem maxMag13_meta : microValid 13 maxMag13Ops = true ∧ microAllocs maxMag13Ops = 6 ∧
    microAnds maxMag13Ops = 6 := by decide
def maxMag13Spec (m : ℕ) : Bool :=
  xor
    (xor
    (xor
    (xor
    (xor (xor (m.testBit 0 && m.testBit 6) (m.testBit 1 && m.testBit 7))
    (m.testBit 2 && m.testBit 8))
    (m.testBit 3 && m.testBit 9)) (m.testBit 4 && m.testBit 10)) (m.testBit 5 && m.testBit 11))
      (m.testBit 12)
def maxMag13Check (m : ℕ) : Bool :=
  let st := evalMicroList 13 maxMag13Ops (initBoolList 13 19 m)
  allBelow 13 (fun i ↦ getBoolAt st i == m.testBit i) && (getBoolAt st 13 == maxMag13Spec m)
def maxMag13BlkCheck (blk : ℕ) : Bool :=
  let t := evalMicroU64 5 13 maxMag13Ops (mkU64Tree 5 (initU64Word 13 blk) 0 1)
  let w13 := getU64Tree 5 t 13
  allBelow 13 (fun i ↦ getU64Tree 5 t i == initU64Word 13 blk i) &&
    allBelow 64 (fun k ↦ u64Bit w13 k == maxMag13Spec (64 * blk + k))
theorem maxMag13Blk_eval_ok : allBelow 128 maxMag13BlkCheck = true :=
  allBelowFrom_chunks4 0 32 maxMag13BlkCheck
    (allBelowFrom_chunks4 0 8 _ (by decide) (by decide) (by decide) (by decide))
    (allBelowFrom_chunks4 32 8 _ (by decide) (by decide) (by decide) (by decide))
    (allBelowFrom_chunks4 64 8 _ (by decide) (by decide) (by decide) (by decide))
    (allBelowFrom_chunks4 96 8 _ (by decide) (by decide) (by decide) (by decide))
theorem maxMag13_eval_ok : allBelow 8192 maxMag13Check = true := by
  change allBelow (64 * 128) maxMag13Check = true
  refine allBelow_64_mul_of_blk 128 maxMag13Check maxMag13BlkCheck maxMag13Blk_eval_ok ?_
  intro blk _ hblk k hk
  dsimp only [maxMag13BlkCheck] at hblk
  have h1 := (Bool.and_eq_true _ _).mp hblk
  have hOut := (allBelow_iff 64 _).mp h1.2 k hk
  have hrel : ∀ s < 19,
    u64Bit (getU64Tree 5 (evalMicroU64 5 13 maxMag13Ops (mkU64Tree 5 (initU64Word 13 blk) 0 1)) s) k
    =
      getBoolAt (evalMicroList 13 maxMag13Ops (initBoolList 13 19 (64 * blk + k))) s :=
    u64Bit_evalMicroU64_init 5 13 19 maxMag13Ops maxMag13_meta.1 (by decide)
      (by have := maxMag13_meta.2.1; omega) blk k hk
  dsimp only [maxMag13Check]
  have hIn_ok := u64_inputs_preserved 5 13 19 blk k hk (by decide) _ _ hrel h1.1
  rw [← hrel 13 (by decide), hIn_ok, Bool.true_and]
  exact hOut
theorem signMagOk8_meta : microValid 8 signMagOk8Ops = true ∧ microAllocs signMagOk8Ops = 7 ∧
    microAnds signMagOk8Ops = 7 := by decide
def signMagOk8CheckStrict (m : ℕ) : Bool :=
  let st := evalMicroListStrict 8 signMagOk8Ops (initBoolList 8 15 m)
  allBelow 8 (fun i ↦
    getBoolAt st i == m.testBit i) && (getBoolAt st 14 == !(m.testBit 0 && decide (m / 2 = 0)))
theorem signMagOk8Strict_eval_ok : allBelow 256 signMagOk8CheckStrict = true :=
  allBelowFrom_chunks2 0 128 signMagOk8CheckStrict
    (allBelowFrom_chunks4 0 32 _
      (allBelowFrom_chunks4 0 8 _ (by decide) (by decide) (by decide) (by decide))
      (allBelowFrom_chunks4 32 8 _ (by decide) (by decide) (by decide) (by decide))
      (allBelowFrom_chunks4 64 8 _ (by decide) (by decide) (by decide) (by decide))
      (allBelowFrom_chunks4 96 8 _ (by decide) (by decide) (by decide) (by decide)))
    (allBelowFrom_chunks4 128 32 _
      (allBelowFrom_chunks4 128 8 _ (by decide) (by decide) (by decide) (by decide))
      (allBelowFrom_chunks4 160 8 _ (by decide) (by decide) (by decide) (by decide))
      (allBelowFrom_chunks4 192 8 _ (by decide) (by decide) (by decide) (by decide))
      (allBelowFrom_chunks4 224 8 _ (by decide) (by decide) (by decide) (by decide)))
theorem and6_meta : microValid 6 and6Ops = true ∧ microAllocs and6Ops = 5 ∧ microAnds and6Ops = 5 :=
  by decide
def and6CheckStrict (m : ℕ) : Bool :=
  let st := evalMicroListStrict 6 and6Ops (initBoolList 6 11 m)
  allBelow 6 (fun i ↦ getBoolAt st i == m.testBit i) &&
    (getBoolAt st 10 ==
      (m.testBit 0 && m.testBit 1 && m.testBit 2 && m.testBit 3 && m.testBit 4 && m.testBit 5))
theorem and6Strict_eval_ok : allBelow 64 and6CheckStrict = true :=
  allBelowFrom_chunks2 0 32 and6CheckStrict
    (allBelowFrom_chunks4 0 8 and6CheckStrict (by decide) (by decide) (by decide) (by decide))
    (allBelowFrom_chunks4 32 8 and6CheckStrict (by decide) (by decide) (by decide) (by decide))
end Micro216
section Outer216_C1
open MomSlot0CircuitHalf (padZeroBits)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMu3_lt_seven shellMagCoord3)
open MomSlots35Slot3ProjNuclear (cRad7Computable)
open MomSlots35Slot3ProjNuclear (s3ShellMagCoord3_lt_128)
open StepBBlock0 (s3DitePos s3DiteNeg zmod2_eq_zero_or_one zmod2_add_self_cancel)
open StepBBlock0 (bitsVal_eq_of_testBit)
open StepBBlock0 (cnotVec xorBlock_of_ctx)
open StepBBlock0 (TempCtxLiftEx shellTop7Mu bitsVal_top7_of_22 shellTop7Mu_eq_shellMu3)
open StepBBlock0 (IsMutBlock padZeroBits149_clean padZeroBits149_lt)
open Prod57BoothHoist
  (boothConst57 p57ProjW p57S3W p57U38W p57MW p57OutW sTrue18WDefault sTrueRawVal)
open scoped Matrix BigOperators
open StepBOuter
def xorBlockProg216 (W : ℕ) (out src : Fin W → Wire 437) (hout_lt : ∀ j,
    (out j).val < 275) (hsrc_ge : ∀ j, 275 ≤ (src j).val) (K : TempCtx 437) :
    TempPhaseProg 437 := K.plug (.cliff (Micro216.cnotVec W src out (fun j ↦ wire_ne_of_gt
    (lt_of_lt_of_le (hout_lt j) (hsrc_ge j)))))
def xorBlock1Prog216 (out0 src0 : Wire 437) (hout0 : out0.val < 275)
    (hsrc0 : 275 ≤ src0.val) (K : TempCtx 437) : TempPhaseProg 437 := xorBlockProg216 1
    (fun _ ↦ out0) (fun _ ↦ src0) (fun _ ↦ hout0) (fun _ ↦ hsrc0) K
theorem xorBlock1_275_216_spec {curEnd : ℕ} (hEnd : curEnd ≤ 437) (hStart : 275 ≤ curEnd)
    (out0 src0 : Wire 437) (hout0 : out0.val < 275) (hsrc0 : 275 ≤ src0.val)
    (K : TempCtx 437)
    (hDisj : K.DisjointFrom (fun w ↦ ∃ _ : Fin 1, w = out0))
    (hSupp : K.SupportsBelowCtx curEnd)
    (hLift : Micro216.TempCtxLiftEx 275 curEnd K) :
    let p := xorBlock1Prog216 out0 src0 hout0 hsrc0 K
    IsMutBlock 437 (437 - 275) (fun q ↦ q = out0) p ∧
      p.countTempAnd = K.countTempAnd ∧
      (∀ β, cleanRem 437 (437 - 275) β →
        p.evalBits β out0 = β out0 + K.fwdBits β src0) := by
  obtain ⟨hVal, hCnt, hSgn, hBits⟩ :=
    Micro216.xorBlock_of_ctx hEnd hStart (fun _ : Fin 1 ↦ out0) (fun _ ↦ hout0)
      (fun i j _ ↦ Subsingleton.elim i j) (fun _ : Fin 1 ↦ src0) (fun _ ↦ hsrc0)
      K hDisj hSupp K.fwdBits (Micro216.TempCtxLiftEx.probe hLift)
  have hNon (β) (hβ : cleanRem 437 (437 -
    275) β) (q : Wire 437) (hq : q ≠ out0) : (xorBlock1Prog216 out0 src0 hout0 hsrc0 K).evalBits β q
    = β q := by
    dsimp only [xorBlock1Prog216, xorBlockProg216]
    rw [hBits β hβ q, s3DiteNeg (fun ⟨_, h⟩ ↦ hq h)]
  refine ⟨⟨hVal, hSgn, fun β hβ u hu ↦ ?_, hNon⟩, hCnt, fun β hβ ↦ ?_⟩
  · rw [hNon β hβ u (wire_ne_of_gt (lt_of_lt_of_le hout0 (by omega)))]
    exact hβ u hu
  · dsimp only [xorBlock1Prog216, xorBlockProg216]
    rw [hBits β hβ out0, s3DitePos ⟨0, rfl⟩]
theorem top7W_216_inj : Function.Injective top7W := fun i j h ↦ by
  have hv := congrArg Fin.val h
  dsimp [top7W] at hv
  exact Fin.ext (by omega)
def vsExactSel216W (a : Fin 7) : Wire 437 :=
  ⟨275 + (Micro216.getNatAt Micro216.top7ExactSelSlots a.val - 7), by
    have hb := Micro216.top7ExactSelSlots_bounds a
    omega⟩
theorem vsExactSel216W_inj : Function.Injective vsExactSel216W := fun i j h ↦ by
  have hv := congrArg Fin.val h
  have hbi := Micro216.top7ExactSelSlots_bounds i
  have hbj := Micro216.top7ExactSelSlots_bounds j
  dsimp [vsExactSel216W] at hv hbi hbj
  exact Micro216.top7ExactSelSlots_inj (by dsimp; omega)
def vsOr3_216W (b : Fin 7) : Wire 437 := ⟨284 + 2 * b.val, by omega⟩
theorem p57MW_lt275 (w : Fin 3) (b : Fin 7) : (p57MW w b).val < 275 := by
  dsimp [p57MW]
  omega
theorem p57S3W_lt275 (w : Fin 3) : (p57S3W w).val < 275 := by
  dsimp [p57S3W]
  omega
theorem p57MW_inj_left (b : Fin 7) : Function.Injective (fun w ↦ p57MW w b) := fun i j h ↦ by
  have hv := congrArg Fin.val h
  dsimp [p57MW] at hv
  exact Fin.ext (by omega)
def ctxVsOr3Loop216 : (n : ℕ) → n ≤ 7 → TempCtx 437
  | 0, _ => .hole
  | n + 1, hn =>
      let b : Fin 7 := ⟨n, by omega⟩
      (ctxVsOr3Loop216 n (by omega)).append
        (Micro216.ctxMicro (fun w ↦ p57MW w b) (p57MW_inj_left b) (283 + 2 * n) 2 2
          (fun w ↦ lt_of_lt_of_le (p57MW_lt275 w b) (by omega))
          Micro216.or3Ops Micro216.or3_meta (by omega))
theorem ctxVsOr3Loop216_scoped :
    ∀ (n : ℕ) (hn : n ≤ 7),
      let K := ctxVsOr3Loop216 n hn
      K.countTempAnd = 2 * n ∧
        (∀ {mutW : Wire 437 → Prop},
          (∀ w b, ¬ mutW (p57MW w b)) → (∀ q : Wire 437, 283 ≤ q.val → ¬ mutW q) →
          K.DisjointFrom mutW ∧ K.SupportsBelowCtx (283 + 2 * n)) ∧
        Micro216.TempCtxLiftEx 283 (283 + 2 * n) K ∧
        (∀ γ : BitAssignment 437, cleanRem 437 (437 - 283) γ →
          cleanRem 437 (437 - (283 + 2 * n)) (K.fwdBits γ) ∧
          (∀ q : Wire 437, q.val < 283 → K.fwdBits γ q = γ q) ∧
          (∀ (b : Fin 7), b.val < n →
            K.fwdBits γ (vsOr3_216W b) =
              Micro216.boolToZMod2
                (decide (γ (p57MW 0 b) = 1) || decide (γ (p57MW 1 b) = 1) ||
                  decide (γ (p57MW 2 b) = 1))))
  | 0, _ =>
      ⟨rfl, fun _ _ ↦ ⟨trivial, trivial⟩, fun h ↦ ⟨_, h⟩,
        fun _ hγ ↦ ⟨hγ, fun _ _ ↦ rfl, fun _ hb ↦ absurd hb (Nat.not_lt_zero _)⟩⟩
  | n + 1, hn => by
      obtain ⟨hCntP, hPropsP, hLiftP, hEvalP⟩ := ctxVsOr3Loop216_scoped n (by omega)
      let b₀ : Fin 7 := ⟨n, by omega⟩
      obtain ⟨hCntM, hPropsM, hLiftM, hEvalM⟩ :=
        Micro216.ctxMicro_scoped (fun w ↦ p57MW w b₀) (p57MW_inj_left b₀) (283 + 2 * n) 2 2
          (fun w ↦ lt_of_lt_of_le (p57MW_lt275 w b₀) (by omega))
          Micro216.or3Ops Micro216.or3_meta (by omega)
      dsimp only [ctxVsOr3Loop216]
      refine ⟨by rw [Micro216.TempCtx.append_countTempAnd, hCntP, hCntM, Nat.mul_succ],
        fun hnm hnq ↦ ⟨TempCtx.disjointFrom_append (hPropsP hnm hnq).1
            (hPropsM (fun w ↦ hnm w b₀) (fun q hq ↦ hnq q (by omega))).1,
          TempCtx.supportsBelowCtx_append le_rfl
            (Micro216.TempCtx.supportsBelowCtx_mono (by omega) (hPropsP hnm hnq).2)
            (Micro216.TempCtx.supportsBelowCtx_mono (by omega)
              (hPropsM (fun w ↦ hnm w b₀) (fun q hq ↦ hnq q (by omega))).2)⟩,
        Micro216.TempCtxLiftEx.append hLiftP
          (Micro216.TempCtxLiftEx.mono hLiftM le_rfl (by omega) (by omega)),
        fun γ hγ ↦ ?_⟩
      obtain ⟨hcl₁, hpres₁, hout₁⟩ := hEvalP γ hγ
      set γ₁ := (ctxVsOr3Loop216 n (by omega)).fwdBits γ
      obtain ⟨hcl₂, hpres₂, hsOut₂⟩ := hEvalM γ₁ hcl₁
      have hchk := (Micro216.allBelow_iff 8 Micro216.or3CheckStrict).mp
        Micro216.or3Strict_eval_ok (bitsVal (fun i ↦ γ₁ (p57MW i b₀))) (bitsVal_lt_two_pow _)
      simp only [Micro216.or3CheckStrict, Micro216.evalMicroListStrict_eq, Bool.and_eq_true,
        beq_iff_eq] at hchk
      rw [Micro216.TempCtx.append_fwdBits]
      refine ⟨cleanRem_anti (by omega) hcl₂,
        fun q hq ↦ (hpres₂ hchk.1 q (by omega)).trans (hpres₁ q hq), fun b hb ↦ ?_⟩
      by_cases hbn : b.val < n
      · exact (hpres₂ hchk.1 (vsOr3_216W b) (by dsimp [vsOr3_216W]; omega)).trans (hout₁ b hbn)
      · obtain rfl : b = b₀ := Fin.ext (by dsimp [b₀]; omega)
        have ht (w : Fin 3) :
            (bitsVal (fun i ↦ γ₁ (p57MW i b₀))).testBit w.val = decide (γ (p57MW w b₀) = 1) := by
          rw [Micro216.bitsVal_testBit_eq, hpres₁ _ (lt_trans (p57MW_lt275 w b₀) (by decide))]
        rw [show vsOr3_216W b₀ = ⟨283 + 2 * n + (4 - 3), by omega⟩ from
          Fin.ext (by dsimp [vsOr3_216W, b₀]; omega), hsOut₂ 4 (by decide) (by decide), hchk.2,
          show (bitsVal _).testBit 0 = _ from ht 0,
          show (bitsVal _).testBit 1 = _ from ht 1,
          show (bitsVal _).testBit 2 = _ from ht 2]
def vsMaxMagIn216W (k : Fin 13) : Wire 437 :=
  if hk : k.val < 6 then vsExactSel216W ⟨k.val, by omega⟩
  else vsOr3_216W ⟨k.val - 6, by omega⟩
theorem vsMaxMagIn216W_bounds (k : Fin 13) : 275 ≤ (vsMaxMagIn216W k).val ∧ (vsMaxMagIn216W k).val <
    297 := by
  dsimp only [vsMaxMagIn216W]
  split_ifs with hk
  · have hb := Micro216.top7ExactSelSlots_bounds ⟨k.val, by omega⟩
    dsimp [vsExactSel216W] at hb ⊢
    omega
  · dsimp [vsOr3_216W]
    omega
theorem vsMaxMagIn216W_inj : Function.Injective vsMaxMagIn216W := fun i j h ↦ by
  dsimp only [vsMaxMagIn216W] at h
  have hv := congrArg Fin.val h
  split_ifs at h hv with hi hj1 hj2
  · exact Fin.ext (congrArg (Fin.val (n := 7)) (vsExactSel216W_inj h))
  · have hb := Micro216.top7ExactSelSlots_bounds ⟨i.val, by omega⟩
    dsimp [vsExactSel216W, vsOr3_216W] at hb hv
    omega
  · have hb := Micro216.top7ExactSelSlots_bounds ⟨j.val, by omega⟩
    dsimp [vsExactSel216W, vsOr3_216W] at hb hv
    omega
  · dsimp [vsOr3_216W] at hv
    exact Fin.ext (by omega)
def vsSignIn216W (w : Fin 3) (k : Fin 8) : Wire 437 :=
  if hk : k.val = 0 then p57S3W w else p57MW w ⟨k.val - 1, by omega⟩
theorem vsSignIn216W_lt275 (w : Fin 3) (k : Fin 8) : (vsSignIn216W w k).val < 275 := by
  dsimp only [vsSignIn216W]
  split_ifs
  · exact p57S3W_lt275 w
  · exact p57MW_lt275 w _
theorem vsSignIn216W_inj (w : Fin 3) : Function.Injective (vsSignIn216W w) := fun i j h ↦ by
  have hv := congrArg Fin.val h
  dsimp only [vsSignIn216W] at hv
  split_ifs at hv with hi hj
  all_goals dsimp [p57S3W, p57MW] at hv
  all_goals exact Fin.ext (by omega)
def vsSignOut216W (w : Fin 3) : Wire 437 := ⟨309 + 7 * w.val, by omega⟩
def ctxVsSignLoop216 : (n : ℕ) → n ≤ 3 → TempCtx 437
  | 0, _ => .hole
  | n + 1, hn =>
      let w : Fin 3 := ⟨n, by omega⟩
      (ctxVsSignLoop216 n (by omega)).append
        (Micro216.ctxMicro (vsSignIn216W w) (vsSignIn216W_inj w) (303 + 7 * n) 7 7
          (fun k ↦ lt_of_lt_of_le (vsSignIn216W_lt275 w k) (by omega))
          Micro216.signMagOk8Ops Micro216.signMagOk8_meta (by omega))
theorem ctxVsSignLoop216_scoped :
    ∀ (n : ℕ) (hn : n ≤ 3),
      let K := ctxVsSignLoop216 n hn
      K.countTempAnd = 7 * n ∧
        (∀ {mutW : Wire 437 → Prop},
          (∀ w, ¬ mutW (p57S3W w)) → (∀ w b, ¬ mutW (p57MW w b)) →
          (∀ q : Wire 437, 303 ≤ q.val → ¬ mutW q) →
          K.DisjointFrom mutW ∧ K.SupportsBelowCtx (303 + 7 * n)) ∧
        Micro216.TempCtxLiftEx 303 (303 + 7 * n) K ∧
        (∀ γ : BitAssignment 437, cleanRem 437 (437 - 303) γ →
          cleanRem 437 (437 - (303 + 7 * n)) (K.fwdBits γ) ∧
          (∀ q : Wire 437, q.val < 303 → K.fwdBits γ q = γ q) ∧
          (∀ (w : Fin 3), w.val < n →
            K.fwdBits γ (vsSignOut216W w) =
              Micro216.boolToZMod2
                (!(decide ((γ (p57S3W w)).val = 1) &&
                  decide (bitsVal (fun b ↦ γ (p57MW w b)) = 0)))))
  | 0, _ =>
      ⟨rfl, fun _ _ _ ↦ ⟨trivial, trivial⟩, fun h ↦ ⟨_, h⟩,
        fun _ hγ ↦ ⟨hγ, fun _ _ ↦ rfl, fun _ hw ↦ absurd hw (Nat.not_lt_zero _)⟩⟩
  | n + 1, hn => by
      obtain ⟨hCntP, hPropsP, hLiftP, hEvalP⟩ := ctxVsSignLoop216_scoped n (by omega)
      let w₀ : Fin 3 := ⟨n, by omega⟩
      obtain ⟨hCntM, hPropsM, hLiftM, hEvalM⟩ :=
        Micro216.ctxMicro_scoped (vsSignIn216W w₀) (vsSignIn216W_inj w₀) (303 + 7 * n) 7 7
          (fun k ↦ lt_of_lt_of_le (vsSignIn216W_lt275 w₀ k) (by omega))
          Micro216.signMagOk8Ops Micro216.signMagOk8_meta (by omega)
      dsimp only [ctxVsSignLoop216]
      refine ⟨by rw [Micro216.TempCtx.append_countTempAnd, hCntP, hCntM, Nat.mul_succ],
        fun hns hnm hnq ↦ ?_,
        Micro216.TempCtxLiftEx.append hLiftP
          (Micro216.TempCtxLiftEx.mono hLiftM le_rfl (by omega) (by omega)),
        fun γ hγ ↦ ?_⟩
      · obtain ⟨hdP, hsP⟩ := hPropsP hns hnm hnq
        obtain ⟨hdM, hsM⟩ := hPropsM
          (fun k ↦ by dsimp only [vsSignIn216W]; split_ifs; exacts [hns w₀, hnm w₀ _])
          (fun q hq ↦ hnq q (by omega))
        exact ⟨TempCtx.disjointFrom_append hdP hdM, TempCtx.supportsBelowCtx_append le_rfl
          (Micro216.TempCtx.supportsBelowCtx_mono (by omega) hsP)
          (Micro216.TempCtx.supportsBelowCtx_mono (by omega) hsM)⟩
      · obtain ⟨hcl₁, hpres₁, hout₁⟩ := hEvalP γ hγ
        set γ₁ := (ctxVsSignLoop216 n (by omega)).fwdBits γ
        obtain ⟨hcl₂, hpres₂, hsOut₂⟩ := hEvalM γ₁ hcl₁
        have hchk := (Micro216.allBelow_iff 256 Micro216.signMagOk8CheckStrict).mp
          Micro216.signMagOk8Strict_eval_ok (bitsVal (fun k ↦ γ₁ (vsSignIn216W w₀ k)))
          (bitsVal_lt_two_pow _)
        dsimp only [Micro216.signMagOk8CheckStrict] at hchk
        rw [Micro216.evalMicroListStrict_eq] at hchk
        simp only [Bool.and_eq_true, beq_iff_eq] at hchk
        rw [Micro216.TempCtx.append_fwdBits]
        refine ⟨cleanRem_anti (by omega) hcl₂,
          fun q hq ↦ (hpres₂ hchk.1 q (by omega)).trans (hpres₁ q hq), fun w hw ↦ ?_⟩
        by_cases hwn : w.val < n
        · exact (hpres₂ hchk.1 (vsSignOut216W w) (by dsimp [vsSignOut216W]; omega)).trans
            (hout₁ w hwn)
        · obtain rfl : w = w₀ := Fin.ext (by dsimp [w₀]; omega)
          rw [show vsSignOut216W w₀ = ⟨303 + 7 * n + (14 - 8), by omega⟩ from
              Fin.ext (by dsimp [vsSignOut216W, w₀]; omega),
            hsOut₂ 14 (by decide) (by decide), hchk.2,
            show (fun k ↦ γ₁ (vsSignIn216W w₀ k)) = fun k ↦ γ (vsSignIn216W w₀ k) from
              funext fun k ↦ hpres₁ _ (lt_trans (vsSignIn216W_lt275 w₀ k) (by decide))]
          have hsplit := Micro216.bitsVal_succ_split (fun k : Fin 8 ↦ γ (vsSignIn216W w₀ k))
          have htail : (fun j : Fin 7 ↦ γ (vsSignIn216W w₀ j.succ)) =
              fun b ↦ γ (p57MW w₀ b) := funext fun j ↦ by
            dsimp only [vsSignIn216W]
            rw [s3DiteNeg (show j.succ.val ≠ 0 by simp)]
            exact congrArg (γ ∘ p57MW w₀) (Fin.ext rfl)
          have hs_lt2 := ZMod.val_lt (γ (p57S3W w₀))
          rw [show γ (vsSignIn216W w₀ 0) = γ (p57S3W w₀) from rfl, htail] at hsplit
          rw [show (bitsVal (fun k ↦ γ (vsSignIn216W w₀ k))).testBit 0 = _ from
              Micro216.bitsVal_testBit_eq (fun k ↦ γ (vsSignIn216W w₀ k)) 0,
            show bitsVal (fun k ↦ γ (vsSignIn216W w₀ k)) / 2 =
              bitsVal (fun b ↦ γ (p57MW w₀ b)) by omega]
          change Micro216.boolToZMod2 (!(decide (γ (p57S3W w₀) = 1) && _)) = _
          rcases zmod2_eq_zero_or_one (γ (p57S3W w₀)) with h | h
          all_goals simp [h]
private theorem vsMaxMagMux (m : Fin 7) (b0 b1 b2 b3 b4 b5 b6 : Bool)
    (h6 : m.val < 6 → b6 = false) :
    xor (xor (xor (xor (xor (xor (decide (m.val = 0) && b0) (decide (m.val = 1) && b1))
      (decide (m.val = 2) && b2)) (decide (m.val = 3) && b3)) (decide (m.val = 4) && b4))
      (decide (m.val = 5) && b5)) b6 =
    match m.val with
    | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 | _ => b6 := by
  fin_cases m
  all_goals simp [h6]
theorem vsMaxMag216_algebra (μ c0 c1 c2 : ℕ) (hμ : μ < 7)
    (hc0 : c0 < 2 ^ (μ + 1)) (hc1 : c1 < 2 ^ (μ + 1)) (hc2 : c2 < 2 ^ (μ + 1)) :
    let orB := fun b : ℕ ↦ c0.testBit b || c1.testBit b || c2.testBit b
    let selB := fun a : ℕ ↦ decide (μ = a)
    xor (xor (xor (xor (xor (xor (selB 0 && orB 0) (selB 1 && orB 1))
      (selB 2 && orB 2)) (selB 3 && orB 3)) (selB 4 && orB 4)) (selB 5 && orB 5)) (orB 6) =
      decide (2 ^ μ ≤ max c0 (max c1 c2)) := by
  have htb_mu (c : ℕ) (hc : c < 2 ^ (μ + 1)) : c.testBit μ = decide (2 ^ μ ≤ c) := by
    have hpow : 2 ^ (μ + 1) = 2 * 2 ^ μ := pow_succ' 2 μ
    rw [← Nat.add_zero μ, ← Micro216.s3m_testBit_div_two_pow]
    by_cases hle : 2 ^ μ ≤ c
    · rw [show c = (c - 2 ^ μ) + 2 ^ μ by omega, Nat.add_div_right _ (Nat.two_pow_pos μ),
        Nat.div_eq_of_lt (by omega)]
      simp [hle]
    · simp [Nat.div_eq_of_lt (by omega : c < 2 ^ μ), hle]
  have htb6 (hlt6 : μ < 6) (c : ℕ) (hc : c < 2 ^ (μ + 1)) : c.testBit 6 = false := by
    rw [← Nat.add_zero 6, ← Micro216.s3m_testBit_div_two_pow,
      Nat.div_eq_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl
  have hor_mu : (c0.testBit μ || c1.testBit μ || c2.testBit μ) =
      decide (2 ^ μ ≤ max c0 (max c1 c2)) := by
    simp only [htb_mu c0 hc0, htb_mu c1 hc1, htb_mu c2 hc2, ← Bool.decide_or, le_max_iff, or_assoc]
  refine (vsMaxMagMux ⟨μ, hμ⟩ _ _ _ _ _ _ _ fun h6 ↦ ?_).trans ?_
  · simp [htb6 h6 c0 hc0, htb6 h6 c1 hc1, htb6 h6 c2 hc2]
  · rcases (by omega : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hor_mu
def vsAnd6In216W : Fin 6 → Wire 437 :=
  ![coinOkW, ⟨280, by decide⟩, ⟨297, by decide⟩,
    ⟨309, by decide⟩, ⟨316, by decide⟩, ⟨323, by decide⟩]
theorem vsAnd6In216W_lt324 (i : Fin 6) : (vsAnd6In216W i).val < 324 := by
  fin_cases i
  all_goals decide
theorem vsAnd6In216W_inj : Function.Injective vsAnd6In216W := fun i j h ↦ by
  fin_cases i
  all_goals fin_cases j
  all_goals first | rfl | exact absurd (congrArg Fin.val h) (by decide)
def validStatic216_275Ctx : TempCtx 437 :=
  (Micro216.ctxMicro top7W top7W_216_inj 275 8 6 (fun i ↦ by dsimp [top7W]; omega)
    Micro216.top7DecodeExactOps Micro216.top7DecodeExact_meta3 (by decide)).append
  ((ctxVsOr3Loop216 7 le_rfl).append
    ((Micro216.ctxMicro vsMaxMagIn216W vsMaxMagIn216W_inj 297 6 6 (fun k ↦
      (vsMaxMagIn216W_bounds k).2)
      Micro216.maxMag13Ops Micro216.maxMag13_meta (by decide)).append
    ((ctxVsSignLoop216 3 le_rfl).append
      (Micro216.ctxMicro vsAnd6In216W vsAnd6In216W_inj 324 5 5 vsAnd6In216W_lt324 Micro216.and6Ops
        Micro216.and6_meta (by decide)))))
def validStatic216_275 : TempPhaseProg 437 :=
  xorBlock1Prog216 validStaticW ⟨328, by decide⟩ (by decide) (by decide) validStatic216_275Ctx

theorem validStatic216_275_spec :
    IsMutBlock 437 (437 - 275) vsMutW validStatic216_275 ∧
      validStatic216_275.countTempAnd = 52 ∧
      (∀ β, cleanRem 437 (437 - 275) β →
        let u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
        bitsVal (fun j ↦ β (muW j)) = shellMu3 u22 →
        (∀ w : Fin 3, bitsVal (fun b ↦ β (p57MW w b)) = shellMagCoord3 u22 w) →
        validStatic216_275.evalBits β validStaticW = β validStaticW +
          (β coinOkW) *
            (if 32768 ≤ u22.val ∧
                2 ^ shellMu3 u22 ≤ max (shellMagCoord3 u22 0)
                  (max (shellMagCoord3 u22 1) (shellMagCoord3 u22 2)) ∧
                (∀ w : Fin 3, ¬(shellMagCoord3 u22 w = 0 ∧ (β (p57S3W w)).val = 1))
              then 1 else 0)) := by
  let mut1 : Wire 437 → Prop := fun q ↦ ∃ _ : Fin 1, q = validStaticW
  have hnot_ge259 (q : Wire 437) (hq : 259 ≤ q.val) : ¬ mut1 q :=
    fun ⟨_, h⟩ ↦ absurd (h ▸ hq) (by decide)
  let hin2 : ∀ i, (top7W i).val < 275 := fun i ↦ by dsimp [top7W]; omega
  obtain ⟨hCnt2, hP2, hL2, hEval2⟩ := Micro216.ctxMicro_scoped top7W top7W_216_inj 275
      8 6 hin2 Micro216.top7DecodeExactOps Micro216.top7DecodeExact_meta3 (by decide)
  obtain ⟨hCnt3, hP3, hL3, hEval3⟩ := ctxVsOr3Loop216_scoped 7 le_rfl
  obtain ⟨hCnt4, hP4, hL4, hEval4⟩ := Micro216.ctxMicro_scoped vsMaxMagIn216W
      vsMaxMagIn216W_inj 297 6 6 (fun k ↦ (vsMaxMagIn216W_bounds k).2)
      Micro216.maxMag13Ops Micro216.maxMag13_meta (by decide)
  obtain ⟨hCnt5, hP5, hL5, hEval5⟩ := ctxVsSignLoop216_scoped 3 le_rfl
  obtain ⟨hCnt6, hP6, hL6, hEval6⟩ := Micro216.ctxMicro_scoped vsAnd6In216W vsAnd6In216W_inj
      324 5 5 vsAnd6In216W_lt324 Micro216.and6Ops Micro216.and6_meta (by decide)
  have hnm_val {q : Wire 437} (hne : q.val ≠ validStaticW.val) : ¬ mut1 q :=
    fun ⟨_, h⟩ ↦ hne (congrArg Fin.val h)
  have hnm_mw (w : Fin 3) (b : Fin 7) : ¬ mut1 (p57MW w b) :=
    hnm_val (by dsimp [p57MW, validStaticW]; omega)
  obtain ⟨hd2, hs2⟩ := hP2 (fun i ↦ hnm_val (by dsimp [top7W, validStaticW]; omega))
    (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hd3, hs3⟩ := hP3 hnm_mw (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hd4, hs4⟩ :=
    hP4 (fun k ↦ hnot_ge259 _ (le_trans (by decide) (vsMaxMagIn216W_bounds k).1)) (fun q hq ↦
    hnot_ge259 q (by omega))
  obtain ⟨hd5, hs5⟩ := hP5 (fun w ↦ hnm_val (by dsimp [p57S3W, validStaticW]; omega))
    hnm_mw (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hd6, hs6⟩ := hP6 (fun i ⟨_, h⟩ ↦ by
      fin_cases i
      all_goals exact absurd (congrArg Fin.val h) (by decide))
    (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hBlk, hCnt, hEv⟩ := xorBlock1_275_216_spec (by decide) (by decide) validStaticW
    ⟨328, by decide⟩ (by decide) (by decide) validStatic216_275Ctx
    (TempCtx.disjointFrom_append hd2 (TempCtx.disjointFrom_append hd3
      (TempCtx.disjointFrom_append hd4 (TempCtx.disjointFrom_append hd5 hd6))))
    (TempCtx.supportsBelowCtx_append le_rfl (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs2)
      (TempCtx.supportsBelowCtx_append le_rfl
        (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs3)
        (TempCtx.supportsBelowCtx_append le_rfl
          (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs4)
          (TempCtx.supportsBelowCtx_append le_rfl
            (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs5) hs6))))
    (Micro216.TempCtxLiftEx.append hL2 (Micro216.TempCtxLiftEx.append hL3
      (Micro216.TempCtxLiftEx.append hL4 (Micro216.TempCtxLiftEx.append hL5 hL6))))
  refine ⟨hBlk, hCnt.trans (by
      simp only [validStatic216_275Ctx, Micro216.TempCtx.append_countTempAnd,
        hCnt2, hCnt3, hCnt4, hCnt5, hCnt6]),
    fun β hβ _hmuEq hmEq ↦ ?_⟩
  set u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
  have htop22 : bitsVal (fun i ↦ β (top7W i)) = u22.val / 32768 := by
    rw [show (fun i : Fin 7 ↦ β (top7W i)) =
        fun i : Fin 7 ↦ β (u22WAux ⟨15 + i.val, by omega⟩) from
      funext fun i ↦ congrArg β (Fin.ext (by dsimp [top7W, u22WAux]; omega))]
    exact bitsVal_top7_of_22 (fun j ↦ β (u22WAux j))
  clear_value u22
  dsimp only [validStatic216_275]
  rw [hEv β hβ]
  refine congrArg (β validStaticW + ·) ?_
  obtain ⟨hcl2, hpres2, hsOut2⟩ := hEval2 β hβ
  have hchk2 := (Micro216.allBelow_iff 128 Micro216.top7DecodeExactCheckStrict).mp
    Micro216.top7DecodeExactStrict_eval_ok (bitsVal (fun i ↦ β (top7W i)))
    (bitsVal_lt_two_pow _)
  simp only [Micro216.top7DecodeExactCheckStrict, Micro216.evalMicroListStrict_eq,
    Bool.and_eq_true, beq_iff_eq] at hchk2
  set β₂ := (Micro216.ctxMicro top7W top7W_216_inj 275 8 6 hin2
    Micro216.top7DecodeExactOps Micro216.top7DecodeExact_meta3 (by decide)).fwdBits β
  have hexact_β₂ (a : Fin 7) :
      β₂ (vsExactSel216W a) = Micro216.boolToZMod2 (decide (shellMu3 u22 = a.val)) := by
    have hb := Micro216.top7ExactSelSlots_bounds a
    dsimp only [vsExactSel216W]
    rw [hsOut2 _ hb.1 hb.2,
      beq_iff_eq.mp ((Micro216.allBelow_iff 7 _).mp hchk2.1.2 a.val a.isLt),
      show Micro216.s3mTop7Mu (bitsVal (fun i ↦ β (top7W i))) = shellMu3 u22 by
        rw [htop22]
        exact shellTop7Mu_eq_shellMu3 u22]
  have hw280_β₂ : β₂ ⟨280, by decide⟩ = Micro216.boolToZMod2 (decide (32768 ≤ u22.val)) := by
    rw [show (⟨280, by decide⟩ : Wire 437) = ⟨275 + (12 - 7), by decide⟩ from rfl,
      hsOut2 12 (by decide) (by decide), hchk2.2, htop22,
      decide_eq_decide.mpr (by omega : 0 < u22.val / 32768 ↔ 32768 ≤ u22.val)]
  obtain ⟨hcl3, hpres3, hout3⟩ := hEval3 β₂ hcl2
  set β₃ := (ctxVsOr3Loop216 7 le_rfl).fwdBits β₂
  have hor3_β₃ (b : Fin 7) : β₃ (vsOr3_216W b) =
    Micro216.boolToZMod2
    ((shellMagCoord3 u22 0).testBit b.val || (shellMagCoord3 u22 1).testBit b.val ||
      (shellMagCoord3 u22 2).testBit b.val) := by
    have hmw (w : Fin 3) : decide (β₂ (p57MW w b) = 1) = (shellMagCoord3 u22 w).testBit b.val := by
      rw [hpres2 hchk2.1.1 _ (p57MW_lt275 w b),
        ← Micro216.bitsVal_testBit_eq (fun j ↦ β (p57MW w j)) b, hmEq w]
    rw [hout3 b b.isLt, hmw 0, hmw 1, hmw 2]
  obtain ⟨hcl4, hpres4, hsOut4⟩ := hEval4 β₃ hcl3
  have hchk4 := (Micro216.allBelow_iff 8192 Micro216.maxMag13Check).mp
    Micro216.maxMag13_eval_ok (bitsVal (fun k ↦ β₃ (vsMaxMagIn216W k)))
    (bitsVal_lt_two_pow _)
  dsimp only [Micro216.maxMag13Check, Micro216.maxMag13Spec] at hchk4
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk4
  set β₄ := (Micro216.ctxMicro vsMaxMagIn216W vsMaxMagIn216W_inj 297 6 6
    (fun k ↦ (vsMaxMagIn216W_bounds k).2)
    Micro216.maxMag13Ops Micro216.maxMag13_meta (by decide)).fwdBits β₃
  have hpres24 (q : Wire 437) (hq : q.val < 275) : β₄ q = β q :=
    (hpres4 hchk4.1 q (by omega)).trans ((hpres3 q (by omega)).trans (hpres2 hchk2.1.1 q hq))
  have hw297_β₄ : β₄ ⟨297,
    by decide⟩ = Micro216.boolToZMod2 (decide (2 ^ shellMu3 u22 ≤ max (shellMagCoord3 u22 0)
      (max (shellMagCoord3 u22 1) (shellMagCoord3 u22 2)))) := by
    rw [show (⟨297, by decide⟩ : Wire 437) = ⟨297 + (13 - 13), by decide⟩ from rfl,
      hsOut4 13 (by decide) (by decide), hchk4.2]
    have htb_sel (a : ℕ) (ha : a < 6 := by decide) :
        (bitsVal (fun k ↦ β₃ (vsMaxMagIn216W k))).testBit a = decide (shellMu3 u22 = a) := by
      have hb := Micro216.top7ExactSelSlots_bounds ⟨a, by omega⟩
      dsimp only at hb
      rw [show a = (⟨a, by omega⟩ : Fin 13).val from rfl, Micro216.bitsVal_testBit_eq,
        show vsMaxMagIn216W ⟨a, by omega⟩ = vsExactSel216W ⟨a, by omega⟩ from s3DitePos ha,
        hpres3 _ (by dsimp [vsExactSel216W]; omega), hexact_β₂,
        Micro216.boolToZMod2_decide_eq_one]
    have htb_or (k : ℕ) (hk6 : 6 ≤ k := by decide) (hk13 : k < 13 := by decide) :
        (bitsVal (fun i ↦ β₃ (vsMaxMagIn216W i))).testBit k =
          ((shellMagCoord3 u22 0).testBit (k - 6) ||
            (shellMagCoord3 u22 1).testBit (k - 6) || (shellMagCoord3 u22 2).testBit (k - 6)) := by
      rw [show k = (⟨k, hk13⟩ : Fin 13).val from rfl, Micro216.bitsVal_testBit_eq,
        show vsMaxMagIn216W ⟨k, hk13⟩ = vsOr3_216W ⟨k - 6, by omega⟩ from
          s3DiteNeg (by dsimp; omega),
        hor3_β₃, Micro216.boolToZMod2_decide_eq_one]
    rw [htb_sel 0, htb_sel 1, htb_sel 2, htb_sel 3, htb_sel 4, htb_sel 5,
      htb_or 6, htb_or 7, htb_or 8, htb_or 9, htb_or 10, htb_or 11, htb_or 12]
    exact congrArg Micro216.boolToZMod2 (vsMaxMag216_algebra (shellMu3 u22) _ _ _
      (shellMu3_lt_seven u22) (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _)))
  obtain ⟨hcl5, hpres5, hout5⟩ := hEval5 β₄ hcl4
  set β₅ := (ctxVsSignLoop216 3 le_rfl).fwdBits β₄
  have hsign_β₅ (w : Fin 3) : β₅ (vsSignOut216W w) =
      Micro216.boolToZMod2 (decide (¬(shellMagCoord3 u22 w = 0 ∧ (β (p57S3W w)).val = 1))) := by
    rw [hout5 w w.isLt, hpres24 (p57S3W w) (p57S3W_lt275 w),
      show (fun b ↦ β₄ (p57MW w b)) = fun b ↦ β (p57MW w b) from
        funext fun b ↦ hpres24 _ (p57MW_lt275 w b), hmEq w]
    by_cases hm0 : shellMagCoord3 u22 w = 0
    · simp [hm0]
    · simp [hm0]
  obtain ⟨_, _, hsOut6⟩ := hEval6 β₅ hcl5
  have hchk6 := (Micro216.allBelow_iff 64 Micro216.and6CheckStrict).mp
    Micro216.and6Strict_eval_ok (bitsVal (fun j ↦ β₅ (vsAnd6In216W j))) (bitsVal_lt_two_pow _)
  simp only [Micro216.and6CheckStrict, Micro216.evalMicroListStrict_eq,
    Bool.and_eq_true, beq_iff_eq] at hchk6
  have ht (i : ℕ) (hi : i < 6 := by decide) :
      (bitsVal (fun j ↦ β₅ (vsAnd6In216W j))).testBit i = decide (β₅ (vsAnd6In216W ⟨i, hi⟩) = 1) :=
    Micro216.bitsVal_testBit_eq _ ⟨i, hi⟩
  have hAllFwd : validStatic216_275Ctx.fwdBits β =
      (Micro216.ctxMicro vsAnd6In216W vsAnd6In216W_inj 324 5 5 vsAnd6In216W_lt324
        Micro216.and6Ops Micro216.and6_meta (by decide)).fwdBits β₅ := by
    dsimp only [validStatic216_275Ctx]
    repeat rw [Micro216.TempCtx.append_fwdBits]
  rw [hAllFwd, show (⟨328, by decide⟩ : Wire 437) = ⟨324 + (10 - 6), by decide⟩ from rfl,
    hsOut6 10 (by decide) (by decide), hchk6.2, ht 0, ht 1, ht 2, ht 3, ht 4, ht 5]
  change Micro216.boolToZMod2 (decide (β₅ coinOkW = 1) &&
      decide (β₅ ⟨280, by decide⟩ = 1) && decide (β₅ ⟨297, by decide⟩ = 1) &&
      decide (β₅ (vsSignOut216W 0) = 1) && decide (β₅ (vsSignOut216W 1) = 1) &&
      decide (β₅ (vsSignOut216W 2) = 1)) = _
  rw [(hpres5 _ (by decide)).trans (hpres24 coinOkW (by decide)),
    (hpres5 _ (by decide)).trans ((hpres4 hchk4.1 _ (by decide)).trans (hpres3 _ (by decide))),
    hw280_β₂, hpres5 ⟨297, by decide⟩ (by decide), hw297_β₄, hsign_β₅ 0, hsign_β₅ 1, hsign_β₅ 2]
  simp only [Micro216.boolToZMod2_decide_eq_one]
  rcases zmod2_eq_zero_or_one (β coinOkW) with hc | hc
  · simp [hc, Micro216.boolToZMod2]
  · rw [hc, show decide ((1 : ZMod 2) = 1) = true from rfl, Bool.true_and, one_mul]
    have hAll3 : (∀ w : Fin 3, ¬(shellMagCoord3 u22 w = 0 ∧ (β (p57S3W w)).val = 1)) ↔
        (¬(shellMagCoord3 u22 0 = 0 ∧ (β (p57S3W 0)).val = 1) ∧
          ¬(shellMagCoord3 u22 1 = 0 ∧ (β (p57S3W 1)).val = 1) ∧
          ¬(shellMagCoord3 u22 2 = 0 ∧ (β (p57S3W 2)).val = 1)) :=
      ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ w ↦ by fin_cases w <;> assumption⟩
    exact if_congr (by simp only [Bool.and_eq_true, decide_eq_true_eq, hAll3, and_assoc]) rfl rfl
set_option maxRecDepth 2000
theorem tempPhaseProg216_seq_evalBits {n : ℕ} (p q : TempPhaseProg n) (x : BitAssignment n) :
    (p.seq q).evalBits x = q.evalBits (p.evalBits x) := rfl
attribute [local irreducible] progMidKick216_437
def validStaticVal216 (γ : BitAssignment 437) : ZMod 2 :=
    (if bitsVal (fun b ↦ γ (coinW b)) = 6 then 1 else 0) * (if 32768 ≤ (getU22 γ).val
    ∧ 2 ^ shellMu3 (getU22 γ) ≤ max (shellMagCoord3 (getU22 γ) 0) (max (shellMagCoord3
    (getU22 γ) 1) (shellMagCoord3 (getU22 γ) 2)) ∧ (∀ w : Fin 3, ¬(shellMagCoord3
    (getU22 γ) w = 0 ∧ (γ (p57S3W w)).val = 1)) then 1 else 0)
def prod57Val216 (γ : BitAssignment 437) : ℕ :=
  sTrueRawVal γ * (bitsVal (fun k ↦ γ (p57U38W k)) + 1) + boothConst57
def accVal216 (γ : BitAssignment 437) : ZMod 2 := validStaticVal216 γ * (if
    prod57Val216 γ < cRad7Computable (shellMu3 (getU22 γ)) + 1 + boothConst57 then 1
    else 0) * (if (∀ w : Fin 3, (getProj γ w).val ≠ 128) then 1 else 0)
structure RetainedInv216 (γ : BitAssignment 437) : Prop where
  hcl : cleanRem 437 (437 - 275) γ
  hcoin : γ coinOkW = if bitsVal (fun b ↦ γ (coinW b)) = 6 then 1 else 0
  hmu : ∀ j : Fin 3, γ (muW j) = if (shellMu3 (getU22 γ)).testBit j.val then 1 else 0
  hm : ∀ (w : Fin 3) (b : Fin 7),
    γ (p57MW w b) = if (shellMagCoord3 (getU22 γ) w).testBit b.val then 1 else 0
  hvs : γ validStaticW = validStaticVal216 γ
  hstrue : bitsVal (fun j ↦ γ (sTrue18WDefault j)) = sTrueRawVal γ
  hprod : bitsVal (fun m ↦ γ (p57OutW m)) = prod57Val216 γ
  hpbuf : ∀ (w : Fin 3) (b : Fin 8), γ (pBufW w b) =
    if (axisFastVal (getProj γ w) (shellMagCoord3 (getU22 γ) w)
      (γ (p57S3W w)).val).testBit b.val
    then 1 else 0
  hacc : γ accWAux = accVal216 γ
theorem RetainedInv216.mu_val {γ : BitAssignment 437} (h : RetainedInv216 γ) : bitsVal (fun j ↦
    γ (muW j)) = shellMu3 (getU22 γ) :=
  bitsVal_eq_of_testBit _ _ (lt_trans (shellMu3_lt_seven _) (by decide)) h.hmu
theorem RetainedInv216.m_val {γ : BitAssignment 437} (h : RetainedInv216 γ) (w : Fin 3) :
    bitsVal (fun b ↦ γ (p57MW w b)) = shellMagCoord3 (getU22 γ) w :=
  bitsVal_eq_of_testBit _ _ (s3ShellMagCoord3_lt_128 _ w) (h.hm w)
theorem top7_eq_shellMu3_216 (γ : BitAssignment 437) : shellTop7Mu
    ⟨bitsVal (fun i ↦ γ (top7W i)), bitsVal_lt_two_pow _⟩ = shellMu3 (getU22 γ) := by
  have hfn : (fun i : Fin 7 ↦ γ (top7W i)) = fun i : Fin 7 ↦ γ (u22WAux ⟨15 + i.val, by omega⟩) :=
    funext fun i ↦ congrArg γ (Fin.ext (by dsimp [top7W, u22WAux]; omega))
  have htop : bitsVal (fun i : Fin 7 ↦ γ (top7W i)) = (getU22 γ).val / 32768 := by
    rw [hfn]
    exact bitsVal_top7_of_22 (fun j ↦ γ (u22WAux j))
  have hfin : (⟨bitsVal (fun i ↦ γ (top7W i)), bitsVal_lt_two_pow _⟩ : Fin 128) =
      ⟨(getU22 γ).val / 32768, by have := (getU22 γ).isLt; omega⟩ :=
    Fin.ext htop
  rw [hfin]
  exact shellTop7Mu_eq_shellMu3 (getU22 γ)
theorem sTrueRawVal216_congr {γ₁ γ₂ : BitAssignment 437} (hp : ∀ w b,
    γ₁ (p57ProjW w b) = γ₂ (p57ProjW w b))
    (hm : ∀ w b, γ₁ (p57MW w b) = γ₂ (p57MW w b)) (hs : ∀ w,
      γ₁ (p57S3W w) = γ₂ (p57S3W w)) : sTrueRawVal γ₁ = sTrueRawVal γ₂ := by
  unfold sTrueRawVal
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hp_w : (fun b ↦ γ₁ (p57ProjW w b)) = fun b ↦ γ₂ (p57ProjW w b) := funext (hp w)
  have hm_w : (fun b ↦ γ₁ (p57MW w b)) = fun b ↦ γ₂ (p57MW w b) := funext (hm w)
  simp only [hp_w, hm_w, hs w]
theorem sTrue18WDefault216_bounds (j : Fin 18) : (199 ≤ (sTrue18WDefault j).val ∧
    (sTrue18WDefault j).val < 201) ∨
    (259 ≤ (sTrue18WDefault j).val ∧ (sTrue18WDefault j).val < 275) := by
  dsimp [sTrue18WDefault]
  split_ifs with hj
  · exact Or.inr ⟨by dsimp; omega, by dsimp; omega⟩
  · exact Or.inl ⟨by dsimp; omega, by dsimp; omega⟩
theorem p57U38W216_lt107 (k : Fin 38) : (p57U38W k).val < 107 := by
  dsimp [p57U38W]
  split_ifs <;> (dsimp; omega)
theorem eq_padZeroBits149_216_of_lt_and_ge (δ : BitAssignment 437) (f : BitAssignment 149)
    (hlt : ∀ k : Fin 149, δ ⟨k.val, by omega⟩ = f k)
    (hge : ∀ q : Wire 437,149 ≤ q.val → δ q = 0) : δ = padZeroBits (mClean := 288) f := by
  funext q
  by_cases hq : q.val < 149
  · have hq_eq : q = ⟨q.val, by omega⟩ := rfl
    rw [hq_eq, hlt ⟨q.val, hq⟩, ← padZeroBits149_lt f ⟨q.val, hq⟩]
  · rw [hge q (by omega), padZeroBits149_clean f q (by omega)]
theorem zMod2_216_add_self (x : ZMod 2) : x + x = 0 := by
  simpa only [zero_add] using zmod2_add_self_cancel 0 x
theorem toNat216_emod_two_pow42 (x : ℤ) : ((x.emod (2 ^ 42 : ℤ)).toNat : ℤ) = x.emod (2 ^ 42 : ℤ) :=
  by
  have h : 0 ≤ x.emod (2 ^ 42 : ℤ) := Int.emod_nonneg x (by decide)
  omega
theorem elec216_emod_sum3 (a₀ r₀ a₁ r₁ a₂ r₂ m : ℤ) : (a₀ * r₀.emod m + a₁ * r₁.emod m + a₂ *
    r₂.emod m).emod m =
    (a₀ * r₀ + a₁ * r₁ + a₂ * r₂).emod m := by
  change (a₀ * (r₀ % m) + a₁ * (r₁ % m) + a₂ * (r₂ % m)) % m = (a₀ * r₀ + a₁ * r₁ + a₂ * r₂) % m
  simp only [Int.add_emod, Int.mul_emod, Int.emod_emod]
theorem elec216_emod_add_emod_right (a b m : ℤ) : (a + b.emod m).emod m = (a + b).emod m := by
  change (a + (b % m)) % m = (a + b) % m
  simp only [Int.add_emod, Int.emod_emod]
set_option allowUnsafeReducibility true in
theorem rejPhase216_ite_eq (c : ℕ) (a : Bool) (b : ZMod 2) : (if c = 6 then (1 : ZMod 2) else 0) *
    ((if a = true then 1 else 0) + 1) * b = if c = 6 ∧ a
    = false ∧ b = 1 then 1 else 0 := by
  by_cases hc : c = 6
  · cases a
    · rcases zmod2_eq_zero_or_one b with rfl | rfl
      · simp [hc]
      · simp [hc]
    · simp [hc]
  · simp [hc]
end Outer216_C1
section SubpartD
open SpecsAux.SpecMirror SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm SpecsAux.BridgeFermionicComm.SpecInner
open PosMomSelectSandwich PosMomSelectDynamic
open FullSysMomSlots0135Concrete
open ModWrapCoarse8PureMomentum
open SpecsAux.DyadicSubgridToeplitz512AndShift DyadicQft64 DyadicQft64.PhasePerm
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit MomSlots35Slot3ProjNuclear
open StepBBlock0 (bitsVal_split_add)
open scoped Matrix BigOperators Matrix.Norms.L2Operator NNReal ComplexOrder
theorem s3And4 {a b c d : Bool} : (a && b && c && d) = true ↔ a = true ∧ b = true ∧ c = true ∧
    d = true := by simp only [Bool.and_eq_true, and_assoc]
noncomputable def s3NucleusIdx216 {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (z : Fin (2 ^ (momCoreWires mPayload))) : Fin 216 :=
  let u16 := (s3U16Core hmPay).extractIndex z
  let bPar := (basisBits (momCoreWires mPayload) z (s3BParCore hmPay)).val
  ⟨2 * ((u16.val % 4) + 4 * s3NucleusQ27 (basisBits 16 u16)) + bPar, by
    have := Nat.mod_lt u16.val (by decide : 0 < 4)
    have := s3NucleusQ27_lt (basisBits 16 u16)
    have := ZMod.val_lt (basisBits (momCoreWires mPayload) z (s3BParCore hmPay))
    omega⟩
theorem uQutritPair_comm_slotBitProj {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (j : Fin 3) {w : Wire (momCoreWires mPayload)} (hw : w.val < 3954) (b : Fin 2) :
    ((s3QutritPairCore hmPay j).embedUnitary cPrepQutrit2.eval).1 * slotBitProj w b =
    slotBitProj w b * ((s3QutritPairCore hmPay j).embedUnitary cPrepQutrit2.eval).1 := by
  have hwOut : w ∉ Set.range (s3QutritPairCore hmPay j).wires := by
    rintro ⟨idx, hi⟩
    have hv := congrArg Fin.val hi
    dsimp [s3QutritPairCore, MomSlots35Slot3ProjNuclearAlt.qreg_block_apply,
        MomSlots35Slot3ProjNuclearAlt.qreg_block_wires_apply,
        MomSlots35Slot3ProjNuclearAlt.qreg_whole_wires,
          MomSlots35Slot3ProjNuclearAlt.emb_trans_apply,
        MomSlots35Slot3ProjNuclearAlt.emb_refl_apply, MomSlots35Slot3ProjNuclearAlt.emb_mk_apply]
        at hv
    omega
  rw [QRegister.embedUnitary_val, slotBitProj]
  exact embedMatrix_comm_diagonal_of_outside (s3QutritPairCore hmPay j) cPrepQutrit2.eval.1 _
    fun i k hOut ↦ by rw [hOut w hwOut]
private theorem comm_mul_left {N : ℕ} {A B P : Matrix (Fin N) (Fin N) ℂ} (hA : A * P = P *
    A) (hB : B * P = P * B) : (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
theorem uPrep3_216_comm_momCoinProj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (c : Fin 8) :
    (uPrep3_216 hmPay).1 * momCoinProj mPayload c = momCoinProj mPayload c * (uPrep3_216 hmPay).1 :=
      by
  have hSlot {w : Wire (momCoreWires mPayload)} (hw : w.val < 3954) (b : Fin 2) :
      (uPrep3_216 hmPay).1 * slotBitProj w b = slotBitProj w b * (uPrep3_216 hmPay).1 :=
    comm_mul_left (comm_mul_left (uQutritPair_comm_slotBitProj hmPay 2 hw b)
      (comm_mul_left (uQutritPair_comm_slotBitProj hmPay 1 hw b)
        (uQutritPair_comm_slotBitProj hmPay 0 hw b)))
      (uPrep3_comm_slotBitProj hmPay hw b)
  rw [momCoinProj]
  exact op_comm_triple _ _ _ _
    (hSlot (by dsimp [iSlot0Mom]; omega) (coinBitFin2 c 0))
    (hSlot (by dsimp [iSlot1Mom]; omega) (coinBitFin2 c 1))
    (hSlot (by dsimp [iSlot2Mom]; omega) (coinBitFin2 c 2))
attribute [local irreducible] box3D nonzeroBox3D
noncomputable def s3NucleusProb27 (q : Fin 27) : ℝ :=
  qProb ⟨q.val % 3, Nat.mod_lt _ (by decide)⟩ *
    qProb ⟨(q.val / 3) % 3, Nat.mod_lt _ (by decide)⟩ *
    qProb ⟨q.val / 9, by omega⟩

def s3Fin3CubeEquiv : Fin 3 × Fin 3 × Fin 3 ≃ Fin 27 where
  toFun p := ⟨p.1.val + 3 * p.2.1.val + 9 * p.2.2.val, by
    have := p.1.isLt; have := p.2.1.isLt; have := p.2.2.isLt; omega⟩
  invFun q := (⟨q.val % 3, Nat.mod_lt _ (by decide)⟩,
    ⟨(q.val / 3) % 3, Nat.mod_lt _ (by decide)⟩,
    ⟨q.val / 9, by omega⟩)
  left_inv := fun ⟨a, b, c⟩ ↦ by
    refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
      (dsimp only; have := a.isLt; have := b.isLt; have := c.isLt; omega)
  right_inv := fun q ↦ Fin.ext (by dsimp only; have := q.isLt; omega)
private theorem s3NucleusProb27_cube (t0 t1 t2 : Fin 3) : s3NucleusProb27 (s3Fin3CubeEquiv (t0, t1,
    t2)) = qProb t0 * qProb t1 * qProb t2 := by
  have := t0.isLt
  have := t1.isLt
  have := t2.isLt
  unfold s3NucleusProb27
  exact congrArg₂ (· *
    ·) (congrArg₂ (· * ·) (congrArg qProb (Fin.ext (by dsimp [s3Fin3CubeEquiv]; omega)))
    (congrArg qProb (Fin.ext (by dsimp [s3Fin3CubeEquiv]; omega))))
      (congrArg qProb (Fin.ext (by dsimp [s3Fin3CubeEquiv]; omega)))
theorem s3NucleusProb27_sum : (∑ q : Fin 27, s3NucleusProb27 q) = 1 := by
  rw [← s3Fin3CubeEquiv.sum_comp]
  simp_rw [Fintype.sum_prod_type, s3NucleusProb27_cube, Fin.sum_univ_three]
  rw [show (1 : ℝ) = 1 ^ 3 by norm_num, ← qProb_sum]
  ring
noncomputable def s3SynthStructureFactor216 (B_kick : ℕ) (cfg : SpecsAux.SpecMirror.Configuration)
    (Δ : Fin 3 → ℤ) : ℂ :=
  ∑ l : Fin 216,
    (((27 : ℝ) * s3NucleusProb27 ⟨l.val / 8, by omega⟩ : ℝ) : ℂ) *
      Complex.exp ((thetaProtonNearest B_kick cfg l Δ : ℂ) * Complex.I)
def s3Fin27Mul8Equiv : Fin 27 × Fin 8 ≃ Fin 216 where
  toFun p := ⟨p.2.val + 8 * p.1.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun l := (⟨l.val / 8, by omega⟩, ⟨l.val % 8, Nat.mod_lt _ (by decide)⟩)
  left_inv := fun ⟨q, m⟩ ↦ by
    have := q.isLt
    have := m.isLt
    exact Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega))
  right_inv := fun l ↦ Fin.ext (by have := l.isLt; dsimp only; omega)
lemma norm_s3SynthStructureFactor216_le_216 (B_kick : ℕ) (cfg : SpecsAux.SpecMirror.Configuration)
    (Δ : Fin 3 → ℤ) : ‖s3SynthStructureFactor216 B_kick cfg Δ‖ ≤ 216 := by
  unfold s3SynthStructureFactor216
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  trans ∑ l : Fin 216, (27 : ℝ) * s3NucleusProb27 ⟨l.val / 8, by omega⟩
  · refine Finset.sum_congr rfl fun l _ ↦ ?_
    have hnn : 0 ≤ (27 : ℝ) * s3NucleusProb27 ⟨l.val / 8, by omega⟩ :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (qProb_nonneg _) (qProb_nonneg _))
        (qProb_nonneg _))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  · rw [← s3Fin27Mul8Equiv.sum_comp, Fintype.sum_prod_type]
    simp_rw [show ∀ (q : Fin 27) (m : Fin 8),
        (⟨(s3Fin27Mul8Equiv (q, m)).val / 8, by omega⟩ : Fin 27) = q from
      fun q m ↦ Fin.ext (by have := m.isLt; dsimp [s3Fin27Mul8Equiv]; omega),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
      s3NucleusProb27_sum]
    norm_num
noncomputable def alphaSlot3_216 : ℝ := (8192 * 216 * (2 / 42 : ℝ)) / boost127_coarse8_w13
theorem alphaSlot3_216_pos_and_le_20123 : 0 < alphaSlot3_216 ∧ alphaSlot3_216 ≤ 20123 := by
  rw [alphaSlot3_216, boost127_coarse8_w13_eq]
  exact ⟨by positivity, by norm_num⟩
lemma slot3_216_alpha_cheb_step :
    let p := coulombCoarse8PreOAAProb 127 8192
    (8192 * 216 * (2 / 42 : ℝ)) * p ≤ alphaSlot3_216 := by
  intro p
  have hp_le1 : p ≤ 1 := coulombCoarse8PreOAAProb_127_8192_le_one
  have hb_pos : 0 < boost127_coarse8_w13 :=
    lt_of_lt_of_le (by positivity) w13_slot3_slot5_oaa_caps.2.1
  have hcheb : p * boost127_coarse8_w13 ≤ 1 := by
    change p * (3 - 4 * p) ^ 2 ≤ 1
    nlinarith [mul_nonneg (sub_nonneg.mpr hp_le1) (sq_nonneg (1 - 4 * p))]
  rw [alphaSlot3_216, le_div_iff₀ hb_pos, mul_assoc]
  exact mul_le_of_le_one_right (by positivity) hcheb
lemma norm_unitary_conj_le {D : ℕ} (U : Unitary D) (M : Operator D) : ‖U.1 * M * U.1‖ ≤ ‖M‖ := by
  have hU1 : ‖U.1‖ ≤ 1 := by
    by_cases hD : D = 0
    · subst hD
      simp [Subsingleton.elim U.1 0]
    · have : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hD)
      exact (CStarRing.norm_coe_unitary U).le
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hU1).trans
    ((norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hU1)))
noncomputable def s3U16QutritWeight (u16 : Fin 65536) : ℝ :=
  let u := basisBits 16 u16
  (64 : ℝ) * (‖qAmp2 (u 6) (u 7)‖ ^ 2 * (‖qAmp2 (u 4) (u 5)‖ ^ 2 * ‖qAmp2 (u 2) (u 3)‖ ^ 2))
theorem s3QutritPair_bit_eq_u16 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) (j : Fin 3) (b : Fin 2) :
    basisBits 2 ((s3QutritPairCore hmPay j).extractIndex z) b =
      basisBits 16 ((s3U16Core hmPay).extractIndex z)
        ⟨2 + 2 * j.val + b.val, by have := j.isLt; have := b.isLt; omega⟩ := by
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  exact congrArg (basisBits (momCoreWires mPayload) z)
    (Fin.ext (by dsimp [s3QutritPairCore, s3U16Core,
      MomSlots35Slot3ProjNuclearAlt.qreg_block_apply]; omega))
theorem s3QutritFactor_congr_u16 {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) {z₁ z₂ : Fin (2 ^ (momCoreWires mPayload))}
    (hu : (s3U16Core hmPay).extractIndex z₁ =
      (s3U16Core hmPay).extractIndex z₂) : s3QutritFactor hmPay z₁ = s3QutritFactor hmPay z₂ := by
  unfold s3QutritFactor
  simp only [s3QutritPair_bit_eq_u16 hmPay z₁, s3QutritPair_bit_eq_u16 hmPay z₂, hu]
theorem star_s3QutritFactor_mul_self {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) : star (s3QutritFactor hmPay z) * s3QutritFactor
    hmPay z = ((s3U16QutritWeight ((s3U16Core hmPay).extractIndex z) : ℝ) : ℂ) := by
  rw [star_mul_self_eq]
  apply congrArg Complex.ofReal
  unfold s3QutritFactor s3U16QutritWeight
  simp only [s3QutritPair_bit_eq_u16 hmPay z]
  change ‖((2 : ℂ) * qAmp2 (basisBits 16 _ 6) (basisBits 16 _ 7)) *
      (((2 : ℂ) * qAmp2 (basisBits 16 _ 4) (basisBits 16 _ 5)) *
        ((2 : ℂ) * qAmp2 (basisBits 16 _ 2) (basisBits 16 _ 3)))‖ ^ 2 = _
  simp only [norm_mul, mul_pow, Complex.norm_ofNat]
  ring
def s3Bits16SplitEquiv : (Fin 16 →
    ZMod 2) ≃ (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) ×
    (Fin 8 → ZMod 2) where
  toFun u :=
    ((u 6, u 7), (u 4, u 5), (u 2, u 3), (u 0, u 1), fun k : Fin 8 ↦ u ⟨8 + k.val, by omega⟩)
  invFun p := fun i : Fin 16 ↦
    if i.val = 0 then p.2.2.2.1.1 else if i.val = 1 then p.2.2.2.1.2 else if i.val = 2 then
      p.2.2.1.1
    else if i.val = 3 then p.2.2.1.2 else if i.val = 4 then p.2.1.1 else if i.val = 5 then p.2.1.2
    else if i.val = 6 then p.1.1 else if i.val = 7 then p.1.2 else p.2.2.2.2 ⟨i.val - 8, by omega⟩
  left_inv u := by
    funext i
    fin_cases i <;> rfl
  right_inv := fun ⟨⟨b6, b7⟩,⟨b4, b5⟩,⟨b2, b3⟩,⟨b0, b1⟩, hi8⟩ ↦ by
    refine Prod.ext (Prod.ext rfl rfl) (Prod.ext (Prod.ext rfl rfl) (Prod.ext (Prod.ext rfl
      rfl) (Prod.ext (Prod.ext rfl rfl) (funext fun k ↦ ?_))))
    fin_cases k <;> rfl
private abbrev s3Idx216Of (lo q27 b : ℕ) (hlo : lo < 4) (hq : q27 < 27) (hb : b < 2) : Fin 216 :=
  ⟨2 * (lo + 4 * q27) + b, by omega⟩
private theorem s3ZMod2Pair_lt4 (p0 : ZMod 2 × ZMod 2) : p0.1.val + 2 * p0.2.val < 4 := by
  have := ZMod.val_lt p0.1
  have := ZMod.val_lt p0.2
  omega
private theorem s3TritCube_lt27 (p1 p2 p3 : ZMod 2 × ZMod 2) : s3Trit p1.1 p1.2 + 3 *
    s3Trit p2.1 p2.2 + 9 * s3Trit p3.1 p3.2 < 27 := by
  have := s3Trit_lt_three p1.1 p1.2
  have := s3Trit_lt_three p2.1 p2.2
  have := s3Trit_lt_three p3.1 p3.2
  omega
private theorem sum_low2_bPar_eq_fin8 (q : Fin 27) (φ : Fin 216 → ℂ) : (∑ p0 : ZMod 2 × ZMod 2,
    ∑ bPar : Fin 2,
    φ (s3Idx216Of (p0.1.val + 2 * p0.2.val) q.val bPar.val (s3ZMod2Pair_lt4 p0) q.isLt bPar.isLt)) =
      ∑ m : Fin 8, φ (s3Fin27Mul8Equiv (q, m)) := by
  have hz2 (f : ZMod 2 → ℂ) : (∑ b : ZMod 2, f b) = f 0 + f 1 := by
    rw [(by decide : (Finset.univ : Finset (ZMod 2)) = {0, 1}), Finset.sum_pair zero_ne_one]
  rw [Fintype.sum_prod_type]
  simp_rw [hz2, Fin.sum_univ_two]
  rw [Fin.sum_univ_eight]
  have hterm (b0 b1 bP m : ℕ) (hm : m < 8) (heq : 2 * (b0 + 2 * b1) + bP = m) (hL : 2 *
    ((b0 + 2 * b1) + 4 * q.val) + bP < 216) :
      φ ⟨2 * ((b0 + 2 * b1) + 4 * q.val) + bP, hL⟩ = φ (s3Fin27Mul8Equiv (q, ⟨m, hm⟩)) :=
    congrArg φ (Fin.ext (by dsimp [s3Fin27Mul8Equiv]; omega))
  simp only [ZMod.val_zero, ZMod.val_one, Fin.val_zero, Fin.val_one]
  rw [hterm 0 0 0 0 (by decide) rfl, hterm 0 0 1 1 (by decide) rfl,
    hterm 0 1 0 4 (by decide) rfl, hterm 0 1 1 5 (by decide) rfl,
    hterm 1 0 0 2 (by decide) rfl, hterm 1 0 1 3 (by decide) rfl,
    hterm 1 1 0 6 (by decide) rfl, hterm 1 1 1 7 (by decide) rfl]
  change (φ (s3Fin27Mul8Equiv (q, 0)) + φ (s3Fin27Mul8Equiv (q, 1))) +
      (φ (s3Fin27Mul8Equiv (q, 4)) + φ (s3Fin27Mul8Equiv (q, 5))) +
      ((φ (s3Fin27Mul8Equiv (q, 2)) + φ (s3Fin27Mul8Equiv (q, 3))) +
        (φ (s3Fin27Mul8Equiv (q, 6)) + φ (s3Fin27Mul8Equiv (q, 7)))) = _
  ring
theorem sum_zmod2_pair_by_s3Trit (f : ZMod 2 → ZMod 2 → ℝ) (g : Fin 3 → ℂ) : (∑ p : ZMod 2 ×
    ZMod 2, ((f p.1 p.2 : ℝ) : ℂ) * g ⟨s3Trit p.1 p.2, s3Trit_lt_three p.1 p.2⟩) = ∑ t : Fin
    3,
      (((∑ a : ZMod 2, ∑ c : ZMod 2,
      if (⟨s3Trit a c, s3Trit_lt_three a c⟩ : Fin 3) = t then f a c else 0 : ℝ) : ℂ)) * g t := by
  rw [Fintype.sum_prod_type]
  have hpart : ∀ a c : ZMod 2, ((f a c : ℝ) : ℂ) * g ⟨s3Trit a c, s3Trit_lt_three a c⟩ = ∑ t :
      Fin 3,
        (((if (⟨s3Trit a c, s3Trit_lt_three a c⟩ : Fin 3) = t then f a c else 0 : ℝ) : ℂ)) * g t :=
        by
    intro a c
    rw [Finset.sum_eq_single ⟨s3Trit a c, s3Trit_lt_three a c⟩]
    · simp
    · intro t _ hne; rw [s3IteNeg hne.symm, Complex.ofReal_zero, zero_mul]
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  simp_rw [hpart]
  rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp_rw [← Finset.sum_mul]
  push_cast
  rfl
private theorem s3SumU16BParQutrit216 (φ : Fin 216 → ℂ) : (∑ u16 : Fin 65536, ∑ bPar : Fin 2,
    ((s3U16QutritWeight u16 : ℝ) : ℂ) *
    φ
      (s3Idx216Of (u16.val % 4) (s3NucleusQ27 (basisBits 16 u16)) bPar.val
      (Nat.mod_lt _ (by decide)) (s3NucleusQ27_lt _) bPar.isLt)) =
    (((16384 / 27 : ℝ) : ℂ)) * ∑ l : Fin 216,
      (((27 : ℝ) * s3NucleusProb27 ⟨l.val / 8, by omega⟩ : ℝ) : ℂ) * φ l := by
  let e16 : (Fin 16 → ZMod 2) ≃ Fin 65536 := (basisBitsEquiv 16).symm
  rw [← e16.sum_comp]
  dsimp only [e16]
  have hU16_term (u : Fin 16 → ZMod 2) :
      (∑ bPar : Fin 2, ((s3U16QutritWeight ((basisBitsEquiv 16).symm u) : ℝ) : ℂ) *
        φ (s3Idx216Of (((basisBitsEquiv 16).symm u).val % 4)
          (s3NucleusQ27 (basisBits 16 ((basisBitsEquiv 16).symm u)))
          bPar.val (Nat.mod_lt _ (by decide)) (s3NucleusQ27_lt _) bPar.isLt)) =
      ∑ bPar : Fin 2, (((64 : ℝ) * (‖qAmp2 (u 6) (u 7)‖ ^ 2 *
          (‖qAmp2 (u 4) (u 5)‖ ^ 2 * ‖qAmp2 (u 2) (u 3)‖ ^ 2)) : ℝ) : ℂ) *
        φ (s3Idx216Of ((u 0).val + 2 * (u 1).val) (s3NucleusQ27 u) bPar.val
          (s3ZMod2Pair_lt4 (u 0, u 1)) (s3NucleusQ27_lt u) bPar.isLt) := by
    have hb : basisBits 16 ((basisBitsEquiv 16).symm u) = u :=
      (basisBitsEquiv 16).apply_symm_apply u
    have hsp : ((basisBitsEquiv 16).symm u).val =
        bitsVal (fun i : Fin 2 ↦ u ⟨i.val, by omega⟩) +
          2 ^ 2 * bitsVal (fun j : Fin 14 ↦ u ⟨2 + j.val, by omega⟩) :=
      bitsVal_split_add 2 14 (fun i : Fin (2 + 14) ↦ u i)
    have h2 : bitsVal (fun i : Fin 2 ↦ u ⟨i.val, by omega⟩) = (u 0).val + 2 * (u 1).val := by
      simp [bitsVal, Fin.sum_univ_two]
      ring
    have h0 := ZMod.val_lt (u 0)
    have h1 := ZMod.val_lt (u 1)
    refine Finset.sum_congr rfl fun bPar _ ↦ congrArg₂ (· * ·) (by simp [s3U16QutritWeight, hb])
      (congrArg φ (Fin.ext (by
        dsimp only [s3Idx216Of]
        rw [hb]
        omega)))
  simp_rw [hU16_term]
  rw [← s3Bits16SplitEquiv.symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_congr rfl fun _ _ ↦ Fintype.sum_prod_type _,
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Fintype.sum_prod_type _,
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
      Finset.sum_congr rfl fun _ _ ↦ Fintype.sum_prod_type _]
  have hSplitTerm (p3 p2 p1 p0 : ZMod 2 × ZMod 2) (hi8 : Fin 8 → ZMod 2) (bPar : Fin 2) :
      let u := s3Bits16SplitEquiv.symm (p3, p2, p1, p0, hi8)
      (((64 : ℝ) * (‖qAmp2 (u 6) (u 7)‖ ^ 2 *
          (‖qAmp2 (u 4) (u 5)‖ ^ 2 * ‖qAmp2 (u 2) (u 3)‖ ^ 2)) : ℝ) : ℂ) *
        φ (s3Idx216Of ((u 0).val + 2 * (u 1).val) (s3NucleusQ27 u) bPar.val
          (s3ZMod2Pair_lt4 (u 0, u 1)) (s3NucleusQ27_lt u) bPar.isLt) =
      (64 : ℂ) * (((‖qAmp2 p3.1 p3.2‖ ^ 2 : ℝ) : ℂ) *
        (((‖qAmp2 p2.1 p2.2‖ ^ 2 : ℝ) : ℂ) * (((‖qAmp2 p1.1 p1.2‖ ^ 2 : ℝ) : ℂ) *
          φ (s3Idx216Of (p0.1.val + 2 * p0.2.val)
            (s3Trit p1.1 p1.2 + 3 * s3Trit p2.1 p2.2 + 9 * s3Trit p3.1 p3.2) bPar.val
            (s3ZMod2Pair_lt4 p0) (s3TritCube_lt27 p1 p2 p3) bPar.isLt)))) := by
    intro u
    have hphi : φ (s3Idx216Of ((u 0).val + 2 * (u 1).val) (s3NucleusQ27 u) bPar.val
          (s3ZMod2Pair_lt4 (u 0, u 1)) (s3NucleusQ27_lt u) bPar.isLt) =
        φ (s3Idx216Of (p0.1.val + 2 * p0.2.val)
          (s3Trit p1.1 p1.2 + 3 * s3Trit p2.1 p2.2 + 9 * s3Trit p3.1 p3.2) bPar.val
          (s3ZMod2Pair_lt4 p0) (s3TritCube_lt27 p1 p2 p3) bPar.isLt) :=
      congrArg φ (Fin.ext rfl)
    rw [hphi]
    change (((64 : ℝ) * (‖qAmp2 p3.1 p3.2‖ ^ 2 *
      (‖qAmp2 p2.1 p2.2‖ ^ 2 * ‖qAmp2 p1.1 p1.2‖ ^ 2)) : ℝ) : ℂ) * _ = _
    push_cast
    ring
  simp_rw [hSplitTerm]
  have hHi8 (S : ℂ) : (∑ _hi8 : Fin 8 → ZMod 2, S) = (256 : ℂ) * S := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  have hLow8 (p3 p2 p1 : ZMod 2 × ZMod 2) : (∑ p0 : ZMod 2 × ZMod 2, ∑ bPar : Fin 2,
      φ (s3Idx216Of (p0.1.val + 2 * p0.2.val) (s3Trit p1.1 p1.2 + 3 * s3Trit p2.1 p2.2 + 9 *
        s3Trit p3.1 p3.2) bPar.val
      (s3ZMod2Pair_lt4 p0) (s3TritCube_lt27 p1 p2 p3) bPar.isLt)) =
      ∑ m : Fin 8,
        φ (s3Fin27Mul8Equiv (s3Fin3CubeEquiv (⟨s3Trit p1.1 p1.2, s3Trit_lt_three p1.1 p1.2⟩,
      ⟨s3Trit p2.1 p2.2, s3Trit_lt_three p2.1 p2.2⟩, ⟨s3Trit p3.1 p3.2, s3Trit_lt_three p3.1 p3.2⟩),
        m)) :=
    sum_low2_bPar_eq_fin8 (s3Fin3CubeEquiv (⟨s3Trit p1.1 p1.2, s3Trit_lt_three p1.1 p1.2⟩,
      ⟨s3Trit p2.1 p2.2, s3Trit_lt_three p2.1 p2.2⟩,
        ⟨s3Trit p3.1 p3.2, s3Trit_lt_three p3.1 p3.2⟩)) φ
  have hCollapse (g : Fin 3 → ℂ) : (∑ p : ZMod 2 × ZMod 2,
    ((‖qAmp2 p.1 p.2‖ ^ 2 : ℝ) : ℂ) * g ⟨s3Trit p.1 p.2, s3Trit_lt_three p.1 p.2⟩) =
      ∑ t : Fin 3, ((qProb t : ℝ) : ℂ) * g t :=
    (sum_zmod2_pair_by_s3Trit _ g).trans <|
      Finset.sum_congr rfl fun t _ ↦ by rw [sum_norm_sq_qAmp2_fiber t]
  simp_rw [hHi8, ← Finset.mul_sum, hLow8]
  simp_rw [fun p3 p2 : ZMod 2 × ZMod 2 ↦ hCollapse fun t0 ↦ ∑ m : Fin 8,
      φ (s3Fin27Mul8Equiv (s3Fin3CubeEquiv (t0,
        ⟨s3Trit p2.1 p2.2, s3Trit_lt_three p2.1 p2.2⟩,
        ⟨s3Trit p3.1 p3.2, s3Trit_lt_three p3.1 p3.2⟩), m)),
    fun p3 : ZMod 2 × ZMod 2 ↦ hCollapse fun t1 ↦ ∑ t0 : Fin 3, ((qProb t0 : ℝ) : ℂ) *
      ∑ m : Fin 8, φ (s3Fin27Mul8Equiv (s3Fin3CubeEquiv (t0, t1,
        ⟨s3Trit p3.1 p3.2, s3Trit_lt_three p3.1 p3.2⟩), m)),
    hCollapse fun t2 ↦ ∑ t1 : Fin 3, ((qProb t1 : ℝ) : ℂ) *
      ∑ t0 : Fin 3, ((qProb t0 : ℝ) : ℂ) * ∑ m : Fin 8,
        φ (s3Fin27Mul8Equiv (s3Fin3CubeEquiv (t0, t1, t2), m))]
  rw [← s3Fin27Mul8Equiv.sum_comp, Fintype.sum_prod_type, ← s3Fin3CubeEquiv.sum_comp]
  simp_rw [Fintype.sum_prod_type, show ∀ (t0 t1 t2 : Fin 3) (m : Fin 8),
      s3NucleusProb27 ⟨(s3Fin27Mul8Equiv (s3Fin3CubeEquiv (t0, t1, t2), m)).val / 8, by omega⟩ =
        qProb t0 * qProb t1 * qProb t2 from fun t0 t1 t2 m ↦ by
    rw [show (⟨(s3Fin27Mul8Equiv (s3Fin3CubeEquiv (t0, t1, t2), m)).val / 8, by omega⟩ : Fin 27) =
        s3Fin3CubeEquiv (t0, t1, t2) from
      Fin.ext (by have := m.isLt; dsimp [s3Fin27Mul8Equiv]; omega)]
    exact s3NucleusProb27_cube t0 t1 t2, ← Finset.mul_sum, Fin.sum_univ_three]
  push_cast
  ring
theorem s3TopBlock216_step_factor_abstract {mPayload : ℕ} (cfg : SpecsAux.SpecMirror.Configuration)
    (hmPay : 80 ≤ mPayload) (Δ : Fin 3 → ℤ)
    (P : Fin 4194304 → Fin 8 → Fin 256 → Fin (2 ^ 30) → Prop)
    [∀ a b c d, Decidable (P a b c d)] :
    let ampReal : ℝ := boost127_coarse8_w13 * (1 / 2 : ℝ) ^ mPayload
    (∑ t : Slot3PayloadTuple mPayload,
      (if P t.1 t.2.1 t.2.2.1 t.2.2.2.1 then (ampReal : ℂ) else 0) *
      (((s3U16QutritWeight t.2.2.2.2.2.1 : ℝ) : ℂ) *
        Complex.exp ((thetaProtonNearest 42 cfg
          ⟨2 * ((t.2.2.2.2.2.1.val % 4) + 4 * s3NucleusQ27 (basisBits 16 t.2.2.2.2.2.1)) +
            t.2.2.2.2.1.val,
            by have := Nat.mod_lt t.2.2.2.2.2.1.val (by decide : 0 < 4)
               have := s3NucleusQ27_lt (basisBits 16 t.2.2.2.2.2.1)
               have := t.2.2.2.2.1.isLt; omega⟩ Δ : ℂ) * Complex.I))) =
    (((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) *
      (∑ u22 : Fin 4194304, ∑ s3 : Fin 8, ∑ c8 : Fin 256, ∑ f30 : Fin (2 ^ 30),
        if P u22 s3 c8 f30 then (1 : ℂ) else 0) *
      ((((16384 / 27 : ℝ) : ℂ)) * s3SynthStructureFactor216 42 cfg Δ) := by
  intro ampReal
  simp_rw [← mul_boole (P _ _ _ _) (ampReal : ℂ)]
  rw [s3SumProd7Factor (ampReal : ℂ) (fun a b c d ↦ if P a b c d then (1 : ℂ) else 0)
      (fun (bPar : Fin 2) (u16 : Fin 65536) ↦ ((s3U16QutritWeight u16 : ℝ) : ℂ) *
        Complex.exp ((thetaProtonNearest 42 cfg
          ⟨2 * ((u16.val % 4) + 4 * s3NucleusQ27 (basisBits 16 u16)) + bPar.val,
            by have := Nat.mod_lt u16.val (by decide : 0 < 4)
               have := s3NucleusQ27_lt (basisBits 16 u16)
               have := bPar.isLt; omega⟩ Δ : ℂ) * Complex.I)),
    Fintype.card_fin,
    s3SumU16BParQutrit216 (fun l ↦ Complex.exp ((thetaProtonNearest 42 cfg l Δ : ℂ) * Complex.I)),
    show (((2 ^ (mPayload - 80) : ℕ) : ℂ) * (ampReal : ℂ)) =
        (((boost127_coarse8_w13 / (2 : ℝ) ^ 80 : ℝ) : ℂ)) by
      dsimp only [ampReal]
      set k : ℕ := mPayload - 80
      have hreal : ((2 ^ k : ℕ) : ℝ) * (boost127_coarse8_w13 * (1 / 2 : ℝ) ^ mPayload) =
          boost127_coarse8_w13 / (2 : ℝ) ^ 80 := by
        rw [show mPayload = 80 + k by omega, one_div, inv_pow, pow_add,
          Nat.cast_pow, Nat.cast_ofNat]
        field_simp [pow_ne_zero 80 (two_ne_zero' ℝ), pow_ne_zero k (two_ne_zero' ℝ)]
      exact_mod_cast hreal]
  rfl
theorem s3Coarse33Core_80_ge_3924 (i : Fin 33) : 3924 ≤
    (MomSlots35Slot3ProjNuclear.s3Coarse33Core (le_refl 80) i).val := by
  fin_cases i
  all_goals decide
theorem s3QutritPairCore_80_ge_3924 (j : Fin 3) (i : Fin 2) : 3924 ≤
    (s3QutritPairCore (le_refl 80) j i).val := by
  fin_cases j
  all_goals fin_cases i
  all_goals decide
end SubpartD
end Slot3Exact216
end
end ConfigSlot3Exact216Oracle80
end Slot3Exact216Oracle80
end
end ModSlot3Exact216Oracle80

section ModSlot2ZeroMuxPureGidney48
@[expose] public section
namespace Slot2ZeroMuxSignedMul46
section ConfigSlot2ZeroMuxPureGidney48
set_option maxRecDepth 4096
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation
open SpecsAux.SpecMirror SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64Engine DyadicQft64WalkCircuit
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes NuclearTwistMulKickAndBridge288
open WindowedSlot2MulKick288 WindowedSlot2FusedTwist288
local instance (priority := 1000000) instNeZeroTwoPowSlot2ZM48 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
attribute [local irreducible] cnotFanoutCircuit
theorem zmod2_full_adder_val_zm (u t c : ZMod 2) : (u + t + c).val + 2 *
    (c + (u + c) * (t + c)).val = u.val + t.val + c.val := by
  revert u t c; decide
def cOptX {n : ℕ} (flag : Bool) (w : Wire n) : Circuit n :=
  if flag then Circuit.X w else .identity
@[simp] theorem count_cOptX_toff {n : ℕ} (flag : Bool) (w : Wire n) :
    (cOptX flag w).count .TOFF = 0 := by cases flag <;> rfl
@[simp] theorem count_cOptX_t {n : ℕ} (flag : Bool) (w : Wire n) :
    (cOptX flag w).count .T = 0 := by cases flag <;> rfl
def fOptX {n : ℕ} (flag : Bool) (w : Wire n) (β : BitAssignment n) : BitAssignment n :=
  Function.update β w (β w + if flag then 1 else 0)
theorem localPerm_cOptX {n : ℕ} (flag : Bool) (w : Wire n) : LocalClassicalPerm
    ({w} : Finset (Wire n)) (cOptX flag w) (fOptX flag w) := by
  cases flag
  · rw [show fOptX false w = id from funext fun β ↦ by simp [fOptX]]
    exact LocalClassicalPerm.identity ({w} : Finset (Wire n))
  · rw [show fOptX true w = fun β ↦ Function.update β w (β w + 1) from funext fun β ↦
      by simp [fOptX]]
    exact WindowedSlot2MulKick288.localClassicalPerm_X w (Finset.mem_singleton_self w)
theorem fOptX_self_inv {n : ℕ} (flag : Bool) (w : Wire n) (β : BitAssignment n) : fOptX flag w
    (fOptX flag w β) = β := by
  cases flag
  · simp [fOptX, Function.update_eq_self]
  · exact zmod2_x_self_cancel w β
theorem quantum_sign_bit_eq (isInv : Bool) (b : ZMod 2) : (1 - 2 *
    (((b + if !isInv then 1 else 0 : ZMod 2).val) : ℤ)) =
    (if isInv then -1 else 1) * (2 * (b.val : ℤ) - 1) := by
  revert isInv b; decide
theorem bitsVal_succ_head_tail {k : ℕ} (M : Fin (k + 1) → ZMod 2) : bitsVal M = (M 0).val + 2 *
    bitsVal (fun j : Fin k ↦ M j.succ) := by
  unfold bitsVal
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simpa [Fin.val_succ, pow_succ] using Finset.sum_congr rfl fun j _ ↦ by ring
theorem zeroMux_koff_sum_identity (isInv : Bool) (B : Fin 14 → ZMod 2) (M : Fin 48 → ZMod 2) :
    let sgn : ℤ := if isInv then -1 else 1
    sgn * (((B 0).val : ℤ) * (bitsVal M : ℤ) - (bitsVal (fun j : Fin 47 ↦ M j.succ) : ℤ)) +
      (∑ i : Fin 13,
        sgn * (2 * ((B ⟨i.val + 1, by omega⟩).val : ℤ) - 1) * (2 ^ i.val : ℤ) * (bitsVal M : ℤ)) =
    sgn * ((bitsVal B : ℤ) * (bitsVal M : ℤ) -
      ((2 ^ 13 : ℤ) * (bitsVal M : ℤ) -
        ((bitsVal (fun j : Fin 47 ↦ M j.succ) : ℤ) + ((M 0).val : ℤ)))) := by
  intro sgn
  have hFactor : (∑ i : Fin 13, sgn * (2 * ((B ⟨i.val + 1, by omega⟩).val : ℤ) - 1) *
        (2 ^ i.val : ℤ) * (bitsVal M : ℤ)) =
      sgn * (∑ i : Fin 13, (2 * ((B i.succ).val : ℤ) - 1) * (2 ^ i.val : ℤ)) * (bitsVal M : ℤ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by
      change sgn * (2 * ((B i.succ).val : ℤ) - 1) * (2 ^ i.val : ℤ) * (bitsVal M : ℤ) = _
      ring
  have hB0 : (bitsVal B : ℤ) =
      ((B 0).val : ℤ) + ∑ i : Fin 13, ((B i.succ).val : ℤ) * (2 ^ (i.val + 1) : ℤ) := by
    unfold bitsVal
    rw [Fin.sum_univ_succ, Nat.cast_add, Nat.cast_sum]
    simp [Fin.val_succ]
  have hSplit : (∑ i : Fin 13, (2 * ((B i.succ).val : ℤ) - 1) * (2 ^ i.val : ℤ)) =
      (∑ i : Fin 13, ((B i.succ).val : ℤ) * (2 ^ (i.val + 1) : ℤ)) - 8191 := by
    rw [show (8191 : ℤ) = ∑ i : Fin 13, (2 ^ i.val : ℤ) by decide, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [pow_succ]
      ring
  have hM : (bitsVal M : ℤ) = ((M 0).val : ℤ) + 2 * (bitsVal (fun j : Fin 47 ↦ M j.succ) : ℤ) := by
    exact_mod_cast @bitsVal_succ_head_tail 47 M
  rw [hFactor, show (bitsVal B : ℤ) = ((B 0).val : ℤ) +
    (∑ i : Fin 13, (2 * ((B i.succ).val : ℤ) - 1) * (2 ^ i.val : ℤ)) + 8191 by linarith, hM]
  ring
structure CleanPhasePermEquiv {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAnc : QRegister m n) (M_set : Finset (Wire n))
    (d : DynamicCircuit Var n) (c : Circuit n)
    (φ : BitAssignment n → ℂ) (f : BitAssignment n → BitAssignment n) : Prop where
  varIndep : PreservesVarIndep v d
  storeClosed : StoreClosed d
  phasePerm : PhasePerm M_set c φ f
  wp_eq : ∀ Θ : CQAssertionCompat Var (2 ^ n),
    (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
      CQAssertion.restrictToZeroAncilla (wp d.compile Θ) rAnc =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Θ) rAnc
theorem restrict_wp_qAssign_comm_of_phasePerm {Var : Type} [Fintype Var] {m n : ℕ}
    [NeZero (2 ^ n)] {M_set : Finset (Wire n)} {c : Circuit n} {φ : BitAssignment n → ℂ}
    {f : BitAssignment n → BitAssignment n} (hPP : PhasePerm M_set c φ f)
    (rAnc : QRegister m n) (hDisj : Disjoint M_set rAnc.image) (Θ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat c.eval Θ) rAnc =
      wpQAssignCompat c.eval (CQAssertion.restrictToZeroAncilla Θ rAnc) := by
  have hComm : c.eval.1 * rAnc.basisOutcomeProjector 0 = rAnc.basisOutcomeProjector 0 * c.eval.1 :=
    by
    apply matrix_ext_basisKet
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      register_basisOutcomeProjector_zero_mulVec_basisKet, hPP.evolve β,
      Matrix.mulVec_smul, register_basisOutcomeProjector_zero_mulVec_basisKet]
    have hIff : (∀ i : Fin m, f β (rAnc i) = 0) ↔ (∀ i : Fin m, β (rAnc i) = 0) :=
      forall_congr' fun i ↦ by
        rw
          [hPP.outside β (rAnc i)
          (Finset.disjoint_right.mp hDisj ((QRegister.mem_image rAnc _).mpr ⟨i, rfl⟩))]
    simp only [hIff]
    split_ifs
    · exact hPP.evolve β
    · simp only [Matrix.mulVec_zero, smul_zero]
  have hCommAdj : c.eval.1ᴴ * rAnc.basisOutcomeProjector 0 = rAnc.basisOutcomeProjector 0 *
    c.eval.1ᴴ := by
    have h1 := congrArg Matrix.conjTranspose hComm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      QRegister.basisOutcomeProjector_conjTranspose] at h1
    exact h1.symm
  funext σ
  apply Subtype.ext
  simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, HermitianMat.conj_conj]
  rw [hCommAdj]
theorem CleanPhasePermEquiv.ofCircuit {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rAnc : QRegister m n) {M_set : Finset (Wire n)}
    {c : Circuit n} {φ : BitAssignment n → ℂ} {f : BitAssignment n → BitAssignment n}
    (hPP : PhasePerm M_set c φ f) : CleanPhasePermEquiv v rAnc M_set (.circuit c) c φ f :=
  ⟨preservesVarIndep_circuit v c, storeClosed_circuit c, hPP, fun Θ _ ↦ by
    rw [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]⟩
theorem CleanPhasePermEquiv.identity {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] (v : Var) (rAnc : QRegister m n) (M_set : Finset (Wire n)) :
    CleanPhasePermEquiv v rAnc M_set (.identity : DynamicCircuit Var n) .identity (fun _ ↦ 1) id :=
  CleanPhasePermEquiv.ofCircuit v rAnc (PhasePerm.identity M_set)
theorem CleanPhasePermEquiv.mono {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rAnc : QRegister m n} {M₁ M₂ : Finset (Wire n)}
      {d : DynamicCircuit Var n} {c : Circuit n} {φ : BitAssignment n → ℂ}
    {f : BitAssignment n →
      BitAssignment n} (hSub : M₁ ⊆ M₂) (h : CleanPhasePermEquiv v rAnc M₁ d c φ f) :
      CleanPhasePermEquiv v rAnc M₂ d c φ f :=
  ⟨h.varIndep, h.storeClosed, h.phasePerm.mono hSub, h.wp_eq⟩
theorem CleanPhasePermEquiv.widenAnc {Var : Type} [Fintype Var] [DecidableEq Var] {m m' n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rAnc : QRegister m n} {rAnc' : QRegister m' n}
      {M_set : Finset (Wire n)} {d : DynamicCircuit Var n} {c : Circuit n}
    {φ : BitAssignment n → ℂ} {f : BitAssignment n →
      BitAssignment n} (hSub : rAnc.image ⊆ rAnc'.image)
      (h : CleanPhasePermEquiv v rAnc M_set d c φ f) :
    CleanPhasePermEquiv v rAnc' M_set d c φ f :=
  ⟨h.varIndep, h.storeClosed, h.phasePerm,
    fun Θ hΘ ↦ restrictAssertionToZeroAncilla_eq_of_subset hSub (h.wp_eq Θ hΘ)⟩
theorem CleanPhasePermEquiv.congr_phase {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {rAnc : QRegister m n} {M_set : Finset (Wire n)}
      {d : DynamicCircuit Var n} {c : Circuit n} {φ₁ φ₂ : BitAssignment n → ℂ}
    {f : BitAssignment n → BitAssignment n} (h : CleanPhasePermEquiv v rAnc M_set d c φ₁ f)
    (hφ : ∀ β, φ₁ β = φ₂ β) : CleanPhasePermEquiv v rAnc M_set d c φ₂ f :=
  ⟨h.varIndep, h.storeClosed, h.phasePerm.congr_phase hφ, h.wp_eq⟩
theorem CleanPhasePermEquiv.seq {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] {v : Var} {rAnc : QRegister m n} {M_set : Finset (Wire n)}
      {d₁ d₂ : DynamicCircuit Var n} {c₁ c₂ : Circuit n}
    {φ₁ φ₂ : BitAssignment n → ℂ} {f₁ f₂ : BitAssignment n →
      BitAssignment n} (hDisj : Disjoint M_set rAnc.image)
    (h₁ : CleanPhasePermEquiv v rAnc M_set d₁ c₁ φ₁ f₁)
      (h₂ : CleanPhasePermEquiv v rAnc M_set d₂ c₂ φ₂ f₂) :
    CleanPhasePermEquiv v rAnc M_set (.seq d₁ d₂) (c₁ ;;ᶜ c₂) (fun β ↦
      φ₁ β * φ₂ (f₁ β)) (f₂ ∘ f₁) :=
  ⟨preservesVarIndep_seq h₁.varIndep h₂.varIndep,
    storeClosed_seq h₁.storeClosed h₂.storeClosed,
    h₁.phasePerm.seq h₂.phasePerm, fun Θ hΘ ↦ by
      simp only [compile, wp_qSeq, Circuit.eval_seq]
      rw [h₁.wp_eq (wp d₂.compile Θ) (h₂.varIndep Θ hΘ),
        restrict_wp_qAssign_comm_of_phasePerm h₁.phasePerm rAnc hDisj,
        h₂.wp_eq Θ hΘ,
        ← restrict_wp_qAssign_comm_of_phasePerm h₁.phasePerm rAnc hDisj,
        wpQAssignCompat_comp]⟩
theorem CleanPhasePermEquiv.conjLocalPerm {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] {v : Var} {rAnc : QRegister m n} {M_set S_p : Finset (Wire n)}
    {cPrep cUnprep : Circuit n} {fPrep fUnprep : BitAssignment n →
      BitAssignment n} {d : DynamicCircuit Var n} {c : Circuit n}
    {φ : BitAssignment n → ℂ} {f : BitAssignment n →
      BitAssignment n} (hpPrep : LocalClassicalPerm S_p cPrep fPrep)
    (hpUnprep : LocalClassicalPerm S_p cUnprep fUnprep) (hInv : ∀ γ,
      fUnprep (fPrep γ) = γ) (hDisjPM : Disjoint S_p M_set)
    (hDisjPA : Disjoint S_p rAnc.image) (hInner : CleanPhasePermEquiv v rAnc M_set d c φ f) :
      CleanPhasePermEquiv v rAnc M_set
    (.seq (.circuit cPrep) (.seq d (.circuit cUnprep))) (cPrep ;;ᶜ (c ;;ᶜ cUnprep)) (fun β ↦
      φ (fPrep β))
    (fun β w ↦ if w ∈ M_set then f (fPrep β) w else β w) := by
  have hComb : ((fUnprep ∘ f) ∘ fPrep) = (fun β w ↦ if w ∈ M_set then f (fPrep β) w else β w) := by
    funext β w
    dsimp only [Function.comp_apply]
    by_cases hwM : w ∈ M_set
    · simp only [hwM, ↓reduceIte]
      exact hpUnprep.preserves_outside (f (fPrep β)) w (Finset.disjoint_right.mp hDisjPM hwM)
    · simp only [hwM, ↓reduceIte]
      by_cases hwP : w ∈ S_p
      · have hAgree : ∀ u ∈ S_p, f (fPrep β) u = fPrep β u := fun u hu ↦
          hInner.phasePerm.outside (fPrep β) u (Finset.disjoint_left.mp hDisjPM hu)
        rw [hpUnprep.depends_on (f (fPrep β)) (fPrep β) hAgree w hwP, hInv β]
      · rw [hpUnprep.preserves_outside _ w hwP, hInner.phasePerm.outside _ w hwM,
          hpPrep.preserves_outside _ w hwP]
  have hPP1 : PhasePerm Finset.univ cPrep (fun _ ↦ 1) fPrep :=
    PhasePerm.of_classicalPerm hpPrep.perm (fun _ _ hw ↦ absurd (Finset.mem_univ _) hw)
  have hPP3 : PhasePerm Finset.univ cUnprep (fun _ ↦ 1) fUnprep :=
    PhasePerm.of_classicalPerm hpUnprep.perm (fun _ _ hw ↦ absurd (Finset.mem_univ _) hw)
  have hPPSeq := hPP1.seq ((hInner.phasePerm.mono (Finset.subset_univ _)).seq hPP3)
  exact
    { varIndep := preservesVarIndep_seq (preservesVarIndep_circuit v cPrep)
        (preservesVarIndep_seq hInner.varIndep (preservesVarIndep_circuit v cUnprep))
      storeClosed := storeClosed_seq (storeClosed_circuit cPrep)
        (storeClosed_seq hInner.storeClosed (storeClosed_circuit cUnprep))
      phasePerm :=
        { evolve := fun β ↦ by
            have hev := hPPSeq.evolve β
            rw [hComb] at hev
            simpa only [one_mul, mul_one] using hev
          outside := fun β w hw ↦ by simp only [hw, ↓reduceIte] }
      wp_eq := fun Θ hΘ ↦ by
        have hΘ' : ∀ σ val, (wpQAssignCompat cUnprep.eval Θ) (Function.update σ v val) =
            (wpQAssignCompat cUnprep.eval Θ) σ := fun σ val ↦ congrArg
            (qAssignObsMap cUnprep.eval) (hΘ σ val)
        simp only [compile, wp_qSeq, DynCircuitExt.wp_circuit_compile_compat, Circuit.eval_seq]
        rw [restrict_wp_qAssign_comm_of_perm hpPrep.perm hpPrep.preserves_outside rAnc hDisjPA,
          hInner.wp_eq (wpQAssignCompat cUnprep.eval Θ) hΘ',
          ← restrict_wp_qAssign_comm_of_perm hpPrep.perm hpPrep.preserves_outside rAnc hDisjPA]
        simp only [wpQAssignCompat_comp, mul_assoc] }
private theorem lemHex42d (k : ℤ) : DyadicQft64.dyadicTurn 7 k =
    DyadicQft64.dyadicTurn 48 ((2 ^ 41 : ℤ) * k) := by
  unfold DyadicQft64.dyadicTurn
  congr 1
  have hpow : (2 : ℂ) ^ 48 = (2 : ℂ) ^ 41 * (2 : ℂ) ^ 7 := by norm_num
  have hne : (2 : ℂ) ^ 41 ≠ 0 := by norm_num
  have hnum : 2 * Real.pi * Complex.I * (((2 ^ 41 : ℤ) * k : ℤ) : ℂ) = (2 : ℂ) ^ 41 *
    (2 * Real.pi * Complex.I * (k : ℂ)) := by
    push_cast; ring
  rw [hpow, hnum, mul_div_mul_left _ _ hne]
theorem phasePerm_Z48 {n : ℕ} (x : Wire n) : PhasePerm (∅ : Finset (Wire n)) (Circuit.Z x)
    (fun β ↦ DyadicQft64.dyadicTurn 48 ((2 ^ 47 : ℤ) * ((β x).val : ℤ))) id :=
  (PhasePerm.gateZ x).congr_phase fun β ↦ by
    rw [lemHex42d]
    congr 1; ring
theorem phasePerm_SDag48 {n : ℕ} (x : Wire n) : PhasePerm (∅ : Finset (Wire n))
    ((Circuit.S x).inverse)
    (fun β ↦ DyadicQft64.dyadicTurn 48 (-(2 ^ 46 : ℤ) * ((β x).val : ℤ))) id :=
  (PhasePerm.gateSDag x).congr_phase fun β ↦ by
    rw [lemHex42d]
    congr 1; ring
def cQuantumQuarterTurn {n : ℕ} (wNeg x : Wire n) (hw : wNeg ≠ x) : Circuit n :=
  Circuit.S x ;;ᶜ cliffordCZ wNeg x hw
@[simp] theorem count_cQuantumQuarterTurn_toff {n : ℕ} (wNeg x : Wire n) (hw : wNeg ≠ x) :
    (cQuantumQuarterTurn wNeg x hw).count .TOFF = 0 := rfl
@[simp] theorem count_cQuantumQuarterTurn_t {n : ℕ} (wNeg x : Wire n) (hw : wNeg ≠ x) :
    (cQuantumQuarterTurn wNeg x hw).count .T = 0 := rfl
theorem phasePerm_cQuantumQuarterTurn {n : ℕ} (wNeg x : Wire n) (hw : wNeg ≠ x) : PhasePerm
    (∅ : Finset (Wire n)) (cQuantumQuarterTurn wNeg x hw) (fun β ↦ DyadicQft64.dyadicTurn 48
    ((1 - 2 * ((β wNeg).val : ℤ)) * (2 ^ 46 : ℤ) * ((β x).val : ℤ))) id := by
  refine ((PhasePerm.gateS x).seq (phasePerm_cliffordCZ wNeg x hw)).congr_phase fun β ↦ ?_
  dsimp only [Function.comp_apply, id_eq]
  rw [DyadicQft64.dyadicTurn_add, lemHex42d]
  refine DyadicQft64.dyadicTurn_eq_of_emod_eq 48 ?_
  rw [show (2 ^ 41 : ℤ) * (32 * ((β x).val : ℤ) + 64 * (((β wNeg).val : ℤ) * ((β x).val : ℤ))) =
    (1 - 2 * ((β wNeg).val : ℤ)) * (2 ^ 46 : ℤ) * ((β x).val : ℤ) +
      (((β wNeg).val : ℤ) * ((β x).val : ℤ)) * (2 ^ 48 : ℤ) by ring, Int.add_mul_emod_self_right]
def cQuantumEighthTurn {n : ℕ} (wNeg x : Wire n) (hw : wNeg ≠ x) : Circuit n :=
  Circuit.CNOT wNeg x hw ;;ᶜ (Circuit.T x ;;ᶜ Circuit.CNOT wNeg x hw)
@[simp] theorem count_cQuantumEighthTurn_toff {n : ℕ} (wNeg x : Wire n) (hw : wNeg ≠ x) :
    (cQuantumEighthTurn wNeg x hw).count .TOFF = 0 := rfl
@[simp] theorem count_cQuantumEighthTurn_t {n : ℕ} (wNeg x : Wire n) (hw : wNeg ≠ x) :
    (cQuantumEighthTurn wNeg x hw).count .T = 1 := rfl
private theorem lemHex42e (b x : ZMod 2) : ((x + b).val : ℤ) = (1 - 2 * (b.val : ℤ)) * (x.val : ℤ) +
    (b.val : ℤ) := by
  revert b x; decide
theorem phasePerm_cQuantumEighthTurn {n : ℕ} (wNeg x : Wire n) (hw : wNeg ≠ x) : PhasePerm
    (∅ : Finset (Wire n)) (cQuantumEighthTurn wNeg x hw) (fun β ↦ DyadicQft64.dyadicTurn 48
    ((1 - 2 * ((β wNeg).val : ℤ)) * (2 ^ 45 : ℤ) * ((β x).val : ℤ) + (2 ^ 45 : ℤ) *
      ((β wNeg).val : ℤ))) id := by
  let fc : BitAssignment n → BitAssignment n := fun γ ↦ Function.update γ x (γ x + γ wNeg)
  have hcnot : PhasePerm (insert x ∅) (Circuit.CNOT wNeg x hw) (fun _ ↦ 1) fc :=
    PhasePerm.of_classicalPerm (ClassicalPerm.CNOT wNeg x hw)
      (fun _ _ hnw ↦ Function.update_of_ne (by simpa using hnw) _ _)
  have hseq := hcnot.seq (((PhasePerm.gateT x).mono (Finset.empty_subset _)).seq hcnot)
  refine { evolve := fun β ↦ ?_, outside := fun _ _ _ ↦ rfl }
  refine (hseq.evolve β).trans ?_
  dsimp only [Function.comp_apply, id_eq]
  have hfc2 : fc (fc β) = β := LocalClassicalPerm.cnot_self_cancel wNeg x hw β
  rw [hfc2]
  refine congrArg (· • basisKet β) ?_
  simp only [fc, one_mul, mul_one, Function.update_self, lemHex42d, lemHex42e (β wNeg) (β x)]
  exact congrArg (DyadicQft64.dyadicTurn 48) (by ring)
def cApexQuantum {n : ℕ} (wNeg : Wire n) (c : Wire n) : Circuit n :=
  if hw : wNeg ≠ c then cQuantumEighthTurn wNeg c hw else Circuit.T c
@[simp] theorem count_cApexQuantum_toff {n : ℕ} (wNeg c : Wire n) : (cApexQuantum wNeg c).count
    .TOFF = 0 := by
  unfold cApexQuantum; split_ifs <;> rfl
@[simp] theorem count_cApexQuantum_t {n : ℕ} (wNeg c : Wire n) : (cApexQuantum wNeg c).count .T =
    1 := by
  unfold cApexQuantum; split_ifs <;> rfl
theorem phasePerm_cApexQuantum {n : ℕ} (wNeg c : Wire n) (hw : wNeg ≠ c) : PhasePerm
    (∅ : Finset (Wire n)) (cApexQuantum wNeg c) (fun β ↦ DyadicQft64.dyadicTurn 48 ((1 - 2 *
    ((β wNeg).val : ℤ)) * (2 ^ 45 : ℤ) * ((β c).val : ℤ) + (2 ^ 45 : ℤ) * ((β wNeg).val : ℤ))) id :=
      by
  unfold cApexQuantum
  split_ifs
  exact phasePerm_cQuantumEighthTurn wNeg c hw
abbrev rSysLow45Block (kSys : ℕ) : QRegister (kSys + 45) (kSys + 48) :=
  QRegister.block 0 (kSys + 45) (by omega)
noncomputable def apexPhaseExpZ (kSys : ℕ) (Δ : BitAssignment kSys →
    ℤ) (γ : BitAssignment (kSys + 48)) : ℤ :=
  let xSys : BitAssignment kSys := fun i ↦ γ (Fin.castAdd 48 i)
  let mLow : ℕ := bitsVal (fun j : Fin 45 ↦ γ (Fin.natAdd kSys (Fin.castAdd 3 j)))
  let s45 : ℕ := ((Δ xSys) % (2 ^ 45 : ℤ)).toNat
  let mOut : ℕ := (mLow + s45) % 2 ^ 45
  Δ xSys - ((mOut : ℤ) - (mLow : ℤ))
noncomputable def apexCatModAddZ (kSys : ℕ) (Δ : BitAssignment kSys →
    ℤ) : Unitary (2 ^ (kSys + 48)) := (rSysLow45Block kSys).embedUnitary
    (catModAddUnitary kSys 45 (fun x ↦ ((Δ x) % (2 ^ 45 : ℤ)).toNat)) *
    DyadicQft64.dyadicDiagUnitary (kSys + 48) 48 (apexPhaseExpZ kSys Δ)
theorem natCast_mod_two_pow (k a : ℕ) : ((a % 2 ^ k : ℕ) : ℤ) = (a : ℤ) % (2 ^ k : ℤ) := by
  simp [Int.natCast_emod]
private theorem lemHex42f {mOut mLow : ℕ} {d : ℤ} (hLt : mOut <
    2 ^ 45) (hMod : ((mOut : ℤ) - ((mLow : ℤ) + d)) % (2 ^ 45 : ℤ) = 0) : mOut =
    (mLow + (d % (2 ^ 45 : ℤ)).toNat) % 2 ^ 45 := by
  refine Nat.cast_injective (R := ℤ) ?_
  rw [← Int.emod_eq_of_lt (Nat.cast_nonneg mOut)
      (by exact_mod_cast hLt : (mOut : ℤ) < (2 ^ 45 : ℤ)),
    show (mOut : ℤ) = ((mOut : ℤ) - ((mLow : ℤ) + d)) + ((mLow : ℤ) + d) by ring,
    Int.add_emod, hMod, zero_add, Int.emod_emod, natCast_mod_two_pow 45, Nat.cast_add,
    Int.toNat_of_nonneg (Int.emod_nonneg d (by norm_num)), Int.add_emod_emod]
theorem apexCatModAddZ_mulVec_basisKet {kSys n : ℕ} [NeZero (2 ^ n)] (rSys : QRegister kSys n)
    (rCat : QRegister 48 n) (hdisj : rSys.DisjointWires rCat) (Δ : BitAssignment kSys → ℤ)
    (β_out β : BitAssignment n) (hout : ∀ w, w ∉ (rCat.slice 0 45 (by decide)).image → β_out w
    = β w) (hmod45 : ((regVal (rCat.slice 0 45 (by decide)) β_out : ℤ) - ((regVal (rCat.slice
    0 45 (by decide)) β : ℤ) + Δ (fun i ↦ β (rSys i)))) % (2 ^ 45 : ℤ) = 0) : ((rSys.concat
    rCat hdisj).embedUnitary (apexCatModAddZ kSys Δ)).1.mulVec (basisKet β) =
    DyadicQft64.dyadicTurn 48 (Δ (fun i ↦ β (rSys i)) - ((regVal (rCat.slice 0 45 (by decide))
    β_out : ℤ) - (regVal (rCat.slice 0 45 (by decide)) β : ℤ))) • basisKet β_out := by
  let rSC := rSys.concat rCat hdisj
  let rCat45 := rCat.slice 0 45 (by decide)
  have hdisj45 : rSys.DisjointWires rCat45 :=
    QRegExt.disjointWires_mono_right hdisj (QRegister.image_compose_subset rCat _)
  have hComp45 : rSC.compose (rSysLow45Block kSys) = rSys.concat rCat45 hdisj45 := by
    refine WindowedSlot2FusedTwist288Alt.qreg_ext fun idx ↦ ?_
    rw [QRegister.compose_apply]
    by_cases h : idx.val < kSys
    · let i0 : Fin kSys := ⟨idx.val, h⟩
      rw [show rSysLow45Block kSys idx = Fin.castAdd 48 i0 from Fin.ext
          (by simp [rSysLow45Block, i0]),
        show idx = Fin.castAdd 45 i0 from Fin.ext rfl]
      exact (QRegister.concat_apply_left rSys rCat hdisj i0).trans
        (QRegister.concat_apply_left rSys rCat45 hdisj45 i0).symm
    · let j : Fin 45 := ⟨idx.val - kSys, by have := idx.isLt; omega⟩
      rw [show rSysLow45Block kSys idx = Fin.natAdd kSys (Fin.castAdd 3 j) from Fin.ext (by
          simp only [rSysLow45Block, WindowedSlot2FusedTwist288Alt.qreg_block_apply,
            Fin.val_natAdd, Fin.val_castAdd, j]
          omega),
        show idx = Fin.natAdd kSys j from Fin.ext (by
          simp only [Fin.val_natAdd, j]
          omega),
        QRegister.concat_apply_right, QRegister.concat_apply_right, rCat.slice_apply]
      exact congrArg rCat (Fin.ext (by simp))
  rw [apexCatModAddZ, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← QRegister.embedUnitary_compose, hComp45, ← Matrix.mulVec_mulVec,
    DyadicQft64.embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul]
  have hmOut : regVal rCat45 β_out = (regVal rCat45 β + ((Δ (fun i ↦
    β (rSys i))) % (2 ^ 45 : ℤ)).toNat) % 2 ^ 45 :=
    lemHex42f (regVal_lt_two_pow rCat45 β_out) hmod45
  have hCatEv : (((rSys.concat rCat45 hdisj45).embedUnitary (catModAddUnitary kSys 45 (fun x ↦
      ((Δ x) % (2 ^ 45 : ℤ)).toNat))).1).mulVec (basisKet β) = basisKet β_out :=
      (catModAddUnitary_mulVec_basisKet rSys rCat45 hdisj45 (fun x ↦ ((Δ x) % (2 ^ 45 :
      ℤ)).toNat) (fun _ ↦ β_out) β hout hmOut).symm
  rw [hCatEv]
  refine congrArg (· • basisKet β_out) (congrArg (DyadicQft64.dyadicTurn 48) ?_)
  dsimp only [apexPhaseExpZ]
  have hxSys : (fun i : Fin kSys ↦ β (rSC (Fin.castAdd 48 i))) = (fun i ↦ β (rSys i)) :=
    funext fun i ↦ congrArg β (QRegister.concat_apply_left rSys rCat hdisj i)
  have hmLow : bitsVal (fun j : Fin 45 ↦
    β (rSC (Fin.natAdd kSys (Fin.castAdd 3 j)))) = regVal rCat45 β := by
    unfold regVal
    refine congrArg bitsVal (funext fun j ↦ congrArg β ?_)
    dsimp only [rSC, rCat45]
    rw [QRegister.concat_apply_right, QRegister.slice_apply]
    exact congrArg rCat (Fin.ext (by simp))
  rw [hxSys, hmLow, ← hmOut]
private theorem lemHex430 {kSys : ℕ} :
    let rSys0 : QRegister kSys (kSys + 48) := QRegister.block 0 kSys (by omega)
    let rCat0 : QRegister 48 (kSys + 48) := QRegister.block kSys 48 le_rfl
    let hdisj : rSys0.DisjointWires rCat0 :=
      QRegister.block_disjoint_of_le 0 kSys kSys 48 (by omega) (by omega) (by omega)
    rSys0.concat rCat0 hdisj = QRegExt.idReg (kSys + 48) := by
  intro rSys0 rCat0 hdisj
  apply WindowedSlot2FusedTwist288Alt.qreg_ext
  intro idx
  by_cases h : idx.val < kSys
  · rw [show idx = Fin.castAdd 48 ⟨idx.val, h⟩ from Fin.ext rfl, QRegister.concat_apply_left]
    exact Fin.ext (by simp [QRegExt.idReg, rSys0])
  · rw [show idx = Fin.natAdd kSys ⟨idx.val - kSys, by omega⟩ from
        Fin.ext (by simp only [Fin.val_natAdd]; omega),
      QRegister.concat_apply_right]
    exact Fin.ext (by simp [QRegExt.idReg, rCat0])
private theorem apexCatModAddZ_step {kSys n : ℕ} [NeZero (2 ^ n)]
    (rSys : QRegister kSys n) (rCat : QRegister 48 n) (hdisj : rSys.DisjointWires rCat)
    (Δ : BitAssignment kSys → ℤ) (β : BitAssignment n) :
    let rCat45 := rCat.slice 0 45 (by decide)
    let dVal := Δ (fun i ↦ β (rSys i))
    let mOut : Fin (2 ^ 45) :=
      ⟨(regVal rCat45 β + (dVal % (2 ^ 45 : ℤ)).toNat) % 2 ^ 45, Nat.mod_lt _ (by positivity)⟩
    let β_out := basisBits n (rCat45.replaceIndex ((basisBitsEquiv n).symm β) mOut)
    (∀ w, w ∉ rCat45.image → β_out w = β w) ∧
    (((regVal rCat45 β_out : ℤ) - ((regVal rCat45 β : ℤ) + dVal)) % (2 ^ 45 : ℤ) = 0) ∧
    ((rSys.concat rCat hdisj).embedUnitary (apexCatModAddZ kSys Δ)).1.mulVec (basisKet β) =
      DyadicQft64.dyadicTurn 48
        (dVal - ((regVal rCat45 β_out : ℤ) - (regVal rCat45 β : ℤ))) • basisKet β_out := by
  intro rCat45 dVal mOut β_out
  have hout (w : Wire n) (hw : w ∉ rCat45.image) : β_out w = β w := by
    have hnot : w ∉ Set.range rCat45.wires := fun ⟨j, hj⟩ ↦
      hw ((rCat45.mem_image w).mpr ⟨j, hj⟩)
    simp only [β_out, rCat45.basisBits_replaceIndex_of_not_mem _ _ w hnot,
      NuclearTwistRealizes.basisBits_symm_apply]
  have hval : regVal rCat45 β_out = mOut.val := by
    rw [regVal, show (fun j ↦ β_out (rCat45 j)) = basisBits 45 mOut from
      funext fun j ↦ rCat45.basisBits_replaceIndex_apply _ mOut j, bitsVal_basisBits]
  have hm : ((regVal rCat45 β_out : ℤ) - ((regVal rCat45 β : ℤ) + dVal)) % (2 ^ 45 : ℤ) = 0 := by
    rw [hval]
    dsimp only [mOut]
    rw [natCast_mod_two_pow 45, Nat.cast_add,
      Int.toNat_of_nonneg (Int.emod_nonneg dVal (by positivity)),
      Int.add_emod_emod, Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod]
  exact ⟨hout, hm, apexCatModAddZ_mulVec_basisKet rSys rCat hdisj Δ β_out β hout hm⟩
theorem apexCatModAddZ_inv (kSys : ℕ) (Δ : BitAssignment kSys → ℤ) : (apexCatModAddZ kSys Δ)⁻¹ =
    apexCatModAddZ kSys (fun x ↦ -Δ x) := by
  suffices hmul : apexCatModAddZ kSys (fun x ↦ -Δ x) * apexCatModAddZ kSys Δ = 1 by
    rw [← one_mul (apexCatModAddZ kSys Δ)⁻¹, ← hmul]
    group
  let rSys0 : QRegister kSys (kSys + 48) := QRegister.block 0 kSys (by omega)
  let rCat0 : QRegister 48 (kSys + 48) := QRegister.block kSys 48 le_rfl
  let hdisj : rSys0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 kSys kSys 48 (by omega) (by omega) (by omega)
  have hid : rSys0.concat rCat0 hdisj = QRegExt.idReg (kSys + 48) := lemHex430
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, OneMemClass.coe_one, Matrix.one_mulVec]
  obtain ⟨hout1, hm1, hev1⟩ := apexCatModAddZ_step rSys0 rCat0 hdisj Δ β
  set rCat45 := rCat0.slice 0 45 (by decide)
  set xSys : BitAssignment kSys := fun i ↦ β (rSys0 i)
  set mOut : Fin (2 ^ 45) :=
    ⟨(regVal rCat45 β + ((Δ xSys) % (2 ^ 45 : ℤ)).toNat) % 2 ^ 45, Nat.mod_lt _ (by positivity)⟩
  set β_mid := basisBits (kSys + 48) (rCat45.replaceIndex ((basisBitsEquiv _).symm β) mOut)
  have hxMid : (fun i ↦ β_mid (rSys0 i)) = xSys := funext fun i ↦
    hout1 (rSys0 i)
      ((QRegExt.disjointWires_mono_right hdisj
        (QRegister.image_compose_subset rCat0 _)).apply_not_mem_right i)
  have hm2 : ((regVal rCat45 β : ℤ) - ((regVal rCat45 β_mid : ℤ) + (-Δ (fun i ↦
    β_mid (rSys0 i))))) % (2 ^ 45 : ℤ) = 0 := by
    rw [hxMid, show (regVal rCat45 β : ℤ) - ((regVal rCat45 β_mid : ℤ) + (-Δ xSys)) =
        -((regVal rCat45 β_mid : ℤ) - ((regVal rCat45 β : ℤ) + Δ xSys)) by ring]
    exact Int.emod_eq_zero_of_dvd (dvd_neg.mpr (Int.dvd_of_emod_eq_zero hm1))
  have hev2 := apexCatModAddZ_mulVec_basisKet rSys0 rCat0 hdisj (fun x ↦ -Δ x) β β_mid
    (fun w hw ↦ (hout1 w hw).symm) hm2
  rw [hid, embedUnitary_idReg_eq] at hev1 hev2
  rw [hev1, Matrix.mulVec_smul, hev2, hxMid, smul_smul, DyadicQft64.dyadicTurn_add,
    show (Δ xSys - ((regVal rCat45 β_mid : ℤ) - (regVal rCat45 β : ℤ))) +
      (-Δ xSys - ((regVal rCat45 β : ℤ) - (regVal rCat45 β_mid : ℤ))) = 0 by ring,
    DyadicQft64.dyadicTurn_zero, one_smul]
theorem embed_apexCatModAddZ_sub {kSub kAmb : ℕ}
    (subSys : QRegister kSub kAmb)
    (rSub : QRegister (kSub + 48) (kAmb + 48))
    (hrSub : ∀ idx : Fin (kSub + 48),
      rSub idx =
        if h : idx.val < kSub then Fin.castAdd 48 (subSys ⟨idx.val, h⟩)
        else Fin.natAdd kAmb ⟨idx.val - kSub, by have := idx.isLt; omega⟩)
    {Δ : BitAssignment kSub → ℤ} :
    rSub.embedUnitary (apexCatModAddZ kSub Δ) =
      apexCatModAddZ kAmb (fun γ ↦ Δ (fun q ↦ γ (subSys q))) := by
  let rAmb0 : QRegister kAmb (kAmb + 48) := QRegister.block 0 kAmb (by omega)
  let rCat0 : QRegister 48 (kAmb + 48) := QRegister.block kAmb 48 le_rfl
  let rSub0 : QRegister kSub (kAmb + 48) := rAmb0.compose subSys
  have hAmbCat : rAmb0.DisjointWires rCat0 :=
    QRegister.block_disjoint_of_le 0 kAmb kAmb 48 (by omega) (by omega) (by omega)
  have hSubCat : rSub0.DisjointWires rCat0 :=
    QRegExt.disjointWires_mono_left hAmbCat (QRegister.image_compose_subset rAmb0 subSys)
  have hidAmb : rAmb0.concat rCat0 hAmbCat = QRegExt.idReg (kAmb + 48) := lemHex430
  have hSubEq : rSub0.concat rCat0 hSubCat = rSub := by
    apply WindowedSlot2FusedTwist288Alt.qreg_ext
    intro idx
    by_cases h : idx.val < kSub
    · conv_lhs =>
        rw [show idx = Fin.castAdd 48 ⟨idx.val, h⟩ from Fin.ext rfl, QRegister.concat_apply_left]
      rw [hrSub idx, dite_eq_left h]
      exact Fin.ext (by simp [rSub0, rAmb0])
    · let j : Fin 48 := ⟨idx.val - kSub, by omega⟩
      conv_lhs =>
        rw [show idx = Fin.natAdd kSub j from Fin.ext
            (show idx.val = kSub + (idx.val - kSub) by omega),
          QRegister.concat_apply_right]
      rw [hrSub idx, dite_eq_right h]
      exact Fin.ext (by simp [rCat0, j])
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro β
  obtain ⟨hout, hmSub, hevL⟩ := apexCatModAddZ_step rSub0 rCat0 hSubCat Δ β
  have hevR := apexCatModAddZ_mulVec_basisKet rAmb0 rCat0 hAmbCat
    (fun γ ↦ Δ (fun q ↦ γ (subSys q))) _ β hout hmSub
  rw [hSubEq] at hevL
  rw [hidAmb, embedUnitary_idReg_eq] at hevR
  exact hevL.trans hevR.symm
private def lemHex431 (s45 : ℕ) : Equiv.Perm (Fin (2 ^ 48)) where
  toFun m :=
    ⟨(m.val % 2 ^ 45 + s45) % 2 ^ 45 + 2 ^ 45 * (m.val / 2 ^ 45), by
      have := Nat.mod_lt (m.val % 2 ^ 45 + s45) (by positivity : 0 < 2 ^ 45)
      have : m.val / 2 ^ 45 < 2 ^ 3 := Nat.div_lt_of_lt_mul (by have := m.isLt; linarith)
      linarith⟩
  invFun k :=
    ⟨(k.val % 2 ^ 45 + (2 ^ 45 - s45 % 2 ^ 45)) % 2 ^ 45 + 2 ^ 45 * (k.val / 2 ^ 45), by
      have := Nat.mod_lt (k.val % 2 ^ 45 + (2 ^ 45 - s45 % 2 ^ 45))
        (by positivity : 0 < 2 ^ 45)
      have : k.val / 2 ^ 45 < 2 ^ 3 := Nat.div_lt_of_lt_mul (by have := k.isLt; linarith)
      linarith⟩
  left_inv m := Fin.ext <| by
    have hpos : 0 < 2 ^ 45 := by positivity
    let r := (m.val % 2 ^ 45 + s45) % 2 ^ 45
    have hr : r < 2 ^ 45 := Nat.mod_lt _ hpos
    change ((r + 2 ^ 45 * (m.val / 2 ^ 45)) % 2 ^ 45 + (2 ^ 45 - s45 % 2 ^ 45)) % 2 ^ 45 +
        2 ^ 45 * ((r + 2 ^ 45 * (m.val / 2 ^ 45)) / 2 ^ 45) = m.val
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.add_mul_div_left _ _ hpos,
      Nat.div_eq_of_lt hr, zero_add,
      DyadicQft64.mod_add_sub_cancel (2 ^ 45) hpos (m.val % 2 ^ 45) s45 (Nat.mod_lt _ hpos)]
    linarith [Nat.div_add_mod m.val (2 ^ 45)]
  right_inv k := Fin.ext <| by
    have hpos : 0 < 2 ^ 45 := by positivity
    let r := (k.val % 2 ^ 45 + (2 ^ 45 - s45 % 2 ^ 45)) % 2 ^ 45
    have hr : r < 2 ^ 45 := Nat.mod_lt _ hpos
    have hs : s45 % 2 ^ 45 < 2 ^ 45 := Nat.mod_lt _ hpos
    change ((r + 2 ^ 45 * (k.val / 2 ^ 45)) % 2 ^ 45 + s45) % 2 ^ 45 +
        2 ^ 45 * ((r + 2 ^ 45 * (k.val / 2 ^ 45)) / 2 ^ 45) = k.val
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr, Nat.add_mul_div_left _ _ hpos,
      Nat.div_eq_of_lt hr, zero_add]
    dsimp only [r]
    rw [Nat.mod_add_mod, ← Nat.add_mod_mod,
      show k.val % 2 ^ 45 + (2 ^ 45 - s45 % 2 ^ 45) + s45 % 2 ^ 45 =
        k.val % 2 ^ 45 + 2 ^ 45 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (Nat.mod_lt _ hpos)]
    linarith [Nat.div_add_mod k.val (2 ^ 45)]
private theorem lemHex432 {n : ℕ} (rCat : QRegister 48 n)
    (idx₀ : Fin (2 ^ n)) (m : Fin (2 ^ 48)) :
    let β_m := basisBits n (rCat.replaceIndex idx₀ m)
    regVal (rCat.slice 0 45 (by decide)) β_m = m.val % 2 ^ 45 ∧
    regVal (rCat.slice 45 3 (by decide)) β_m = m.val / 2 ^ 45 := by
  intro β_m
  have hSplit := DyadicQft64.regVal_split_slice rCat (by decide : 45 + 3 = 48) β_m
  rw [regVal, show (fun j ↦ β_m (rCat j)) = basisBits 48 m from
    funext fun j ↦ rCat.basisBits_replaceIndex_apply idx₀ m j, bitsVal_basisBits] at hSplit
  have hlo : regVal (rCat.slice 0 45 (by decide)) β_m < 2 ^ 45 := regVal_lt_two_pow _ β_m
  refine ⟨by rw [hSplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo], ?_⟩
  rw [hSplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 45), Nat.div_eq_of_lt hlo, zero_add]
theorem apexCatModAddZ_intertwinesLocal {kAct : ℕ} (U_cat_48 : Unitary (2 ^ 48)) (hcol0 :
    U_cat_48.1.mulVec (Pi.single 0 1) = DyadicQft64Engine.phaseGradKet 48)
    (Δ : BitAssignment kAct → ℤ) : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
    (apexCatModAddZ kAct Δ) (DyadicQft64.dyadicDiagUnitary kAct 48 Δ) := by
  let rSys : QRegister kAct (kAct + 48) := QRegister.block 0 kAct (by omega)
  let rCat : QRegister 48 (kAct + 48) := QRegister.block kAct 48 le_rfl
  have hdisj : rSys.DisjointWires rCat :=
    QRegister.block_disjoint_of_le 0 kAct kAct 48 (by omega) (by omega) (by omega)
  have hid : rSys.concat rCat hdisj = QRegExt.idReg (kAct + 48) := lemHex430
  refine ⟨?_, rSys.embedMatrix_comm_of_disjoint rCat hdisj _ _,
    rSys.embedMatrix_comm_of_disjoint rCat hdisj _ (compProj 0)⟩
  rw [← embedUnitary_idReg_eq (apexCatModAddZ kAct Δ), ← hid]
  apply matrix_ext_basisKet
  intro β
  repeat rw [← Matrix.mulVec_mulVec]
  rw [register_basisOutcomeProjector_zero_mulVec_basisKet]
  split_ifs with hzero
  · let idx₀ := (basisBitsEquiv (kAct + 48)).symm β
    let γ : BitAssignment kAct := fun i ↦ β (rSys i)
    have hext0 : rCat.extractIndex idx₀ = 0 := by
      rw [QRegExt.extractIndex_eq_zero_iff]
      intro j
      exact (congrFun ((basisBitsEquiv (kAct + 48)).apply_symm_apply β) (rCat j)).trans (hzero j)
    have hprep : (rCat.embedUnitary U_cat_48).1.mulVec (basisKet β) =
        ∑ m : Fin (2 ^ 48), DyadicQft64Engine.phaseGradKet 48 m •
          basisKet (basisBits (kAct + 48) (rCat.replaceIndex idx₀ m)) := by
      conv_lhs =>
        rw [QRegister.embedUnitary_val, basisKet, basisState,
          rCat.embedMatrix_mulVec_single_factors, hext0, hcol0,
          show DyadicQft64Engine.phaseGradKet 48 =
              ∑ m : Fin (2 ^ 48), DyadicQft64Engine.phaseGradKet 48 m • Pi.single m (1 : ℂ) from
            funext fun x ↦ by simp [Finset.sum_apply, Pi.single_apply],
          rCat.tensorState_sum_left]
      exact Finset.sum_congr rfl fun m _ ↦ by
        rw [rCat.tensorState_smul_left, rCat.tensorState_single_replaceIndex]
        simp [basisKet, basisState, idx₀, (basisBitsEquiv (kAct + 48)).symm_apply_apply]
    rw [DyadicQft64.embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul, hprep,
      Matrix.mulVec_sum, Finset.smul_sum]
    let s45 : ℕ := ((Δ γ) % (2 ^ 45 : ℤ)).toNat
    let e : Equiv.Perm (Fin (2 ^ 48)) := lemHex431 s45
    have hstep' (m : Fin (2 ^ 48)) :
      ((rSys.concat rCat hdisj).embedUnitary (apexCatModAddZ kAct Δ)).1.mulVec
        (basisKet (basisBits (kAct + 48) (rCat.replaceIndex idx₀ m))) =
          DyadicQft64.dyadicTurn 48 (Δ γ - (((e m).val : ℤ) - (m.val : ℤ))) •
        basisKet (basisBits (kAct + 48) (rCat.replaceIndex idx₀ (e m))) := by
      let β_m := basisBits (kAct + 48) (rCat.replaceIndex idx₀ m)
      let β_em := basisBits (kAct + 48) (rCat.replaceIndex idx₀ (e m))
      let rCat45 := rCat.slice 0 45 (by decide)
      let rCatHi3 := rCat.slice 45 3 (by decide)
      have hSplit_m := lemHex432 rCat idx₀ m
      have hSplit_em := lemHex432 rCat idx₀ (e m)
      have hr_em : (m.val % 2 ^ 45 + s45) % 2 ^ 45 < 2 ^ 45 := Nat.mod_lt _ (Nat.two_pow_pos 45)
      have hem : (e m).val = (m.val % 2 ^ 45 + s45) % 2 ^ 45 + 2 ^ 45 * (m.val / 2 ^ 45) := rfl
      have hHiEq : (e m).val / 2 ^ 45 = m.val / 2 ^ 45 := by
        rw [hem, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 45), Nat.div_eq_of_lt hr_em, zero_add]
      have hLoEq : (e m).val % 2 ^ 45 = (m.val % 2 ^ 45 + s45) % 2 ^ 45 := by
        rw [hem, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr_em]
      have hSys_m : (fun i ↦ β_m (rSys i)) = γ := funext fun i ↦ by
        dsimp only [β_m]
        rw [rCat.basisBits_replaceIndex_of_not_mem idx₀ m (rSys i)
          (fun ⟨j, hj⟩ ↦ hdisj.ne i j hj.symm)]
        simp [γ, idx₀]
      have hout (w : Wire (kAct + 48)) (hw45 : w ∉ rCat45.image) : β_em w = β_m w := by
        by_cases hwCat : w ∈ Set.range rCat.wires
        · obtain ⟨j, rfl⟩ := hwCat
          have hj45 : 45 ≤ j.val := by
            by_contra hnot
            exact hw45 ((rCat45.mem_image _).mpr ⟨⟨j.val, by omega⟩, by
              dsimp only [rCat45]
              rw [QRegister.slice_apply]
              exact congrArg rCat (Fin.ext (by simp))⟩)
          let t : Fin 3 := ⟨j.val - 45, by have := j.isLt; omega⟩
          have hjt : rCat j = rCatHi3 t := by
            dsimp only [rCatHi3]
            rw [QRegister.slice_apply]
            exact congrArg rCat (Fin.ext (by change j.val = 45 + (j.val - 45); omega))
          have hBitsHi : (fun u ↦ β_em (rCatHi3 u)) = fun u ↦ β_m (rCatHi3 u) :=
            (basisBitsEquiv 3).symm.injective <| Fin.ext <| by
              rw [← bitsVal_eq_symm_val, ← bitsVal_eq_symm_val]
              exact hSplit_em.2.trans (hHiEq.trans hSplit_m.2.symm)
          exact hjt ▸ congrFun hBitsHi t
        · dsimp only [β_em, β_m]
          rw [rCat.basisBits_replaceIndex_of_not_mem idx₀ (e m) w hwCat,
            rCat.basisBits_replaceIndex_of_not_mem idx₀ m w hwCat]
      have hmod45 : ((regVal rCat45 β_em : ℤ) - ((regVal rCat45 β_m : ℤ) + Δ (fun i ↦
        β_m (rSys i)))) % (2 ^ 45 : ℤ) = 0 := by
        rw [hSys_m, hSplit_em.1, hSplit_m.1, hLoEq, natCast_mod_two_pow 45, Nat.cast_add,
          Int.toNat_of_nonneg (Int.emod_nonneg (Δ γ) (by positivity)),
          Int.add_emod_emod, Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod]
      have hev := apexCatModAddZ_mulVec_basisKet rSys rCat hdisj Δ β_em β_m hout hmod45
      rw [hSys_m, hSplit_em.1, hSplit_m.1] at hev
      rw [hev]
      refine congrArg (· • basisKet β_em) (congrArg (DyadicQft64.dyadicTurn 48) ?_)
      have hdm : ((2 ^ 45 : ℕ) : ℤ) * ((m.val / 2 ^ 45 : ℕ) : ℤ) + ((m.val % 2 ^ 45 : ℕ) : ℤ) =
        (m.val : ℤ) := by
        exact_mod_cast Nat.div_add_mod m.val (2 ^ 45)
      have hdem : ((2 ^ 45 : ℕ) : ℤ) * ((m.val / 2 ^ 45 : ℕ) : ℤ) + (((e m).val % 2 ^ 45 : ℕ) : ℤ) =
        ((e m).val : ℤ) := by
        have h1 := Nat.div_add_mod (e m).val (2 ^ 45)
        rw [hHiEq] at h1
        exact_mod_cast h1
      rw [← hdem, ← hdm]
      ring
    simp_rw [Matrix.mulVec_smul, hstep', smul_smul]
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    change (DyadicQft64.phaseGradKet 48 (e.symm k) *
        DyadicQft64.dyadicTurn 48 (Δ γ - (((e (e.symm k)).val : ℤ) - ((e.symm k).val : ℤ)))) •
        basisKet (basisBits (kAct + 48) (rCat.replaceIndex idx₀ (e (e.symm k)))) =
      (DyadicQft64.dyadicTurn 48 (Δ γ) * DyadicQft64.phaseGradKet 48 k) •
        basisKet (basisBits (kAct + 48) (rCat.replaceIndex idx₀ k))
    rw [e.apply_symm_apply k]
    refine congrArg (· • basisKet (basisBits (kAct + 48) (rCat.replaceIndex idx₀ k))) ?_
    rw [DyadicQft64.phaseGradKet_eq_norm_mul_dyadicTurn 48 (e.symm k),
      DyadicQft64.phaseGradKet_eq_norm_mul_dyadicTurn 48 k,
      mul_assoc, DyadicQft64.dyadicTurn_add,
      show -((e.symm k).val : ℤ) + (Δ γ - ((k.val : ℤ) - ((e.symm k).val : ℤ))) =
        Δ γ + -(k.val : ℤ) by ring,
      ← DyadicQft64.dyadicTurn_add]
    ring
  · simp only [Matrix.mulVec_zero]
@[simp] theorem dyn_count_circuit {Var : Type} {n m : ℕ} (c : Circuit n) (g : PrimitiveGate m) :
    (DynamicCircuit.circuit (Var := Var) c).count g = c.count g := rfl
theorem realizesClean_of_cleanPhasePermEquiv {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct m n : ℕ} [NeZero (2 ^ n)] {v : Var} {rAct : QRegister kAct n} {rAnc : QRegister m n}
    {M_set : Finset (Wire n)} {u : Unitary (2 ^ kAct)} {d : DynamicCircuit Var n}
    {c : Circuit n} {φ : BitAssignment n → ℂ} {f : BitAssignment n → BitAssignment n}
    (hEquiv : CleanPhasePermEquiv v rAnc M_set d c φ f) (hAction : ∀ β : BitAssignment n, (∀ i
    : Fin m, β (rAnc i) = 0) → φ β • basisKet (f β) = (rAct.embedUnitary u).1.mulVec (basisKet
    β)) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rAnc u d := by
  have hProjConj : rAnc.basisOutcomeProjector 0 * c.eval.1ᴴ =
      rAnc.basisOutcomeProjector 0 * (rAct.embedUnitary u).1ᴴ := by
    have hMul : c.eval.1 * rAnc.basisOutcomeProjector 0 =
        (rAct.embedUnitary u).1 * rAnc.basisOutcomeProjector 0 :=
      matrix_ext_basisKet fun β ↦ by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          register_basisOutcomeProjector_zero_mulVec_basisKet]
        split_ifs with hz
        · rw [hEquiv.phasePerm.evolve β, hAction β hz]
        · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
    simpa [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using
      congrArg Matrix.conjTranspose hMul
  intro M
  obtain ⟨M', hM'⟩ := hEquiv.storeClosed M
  refine ⟨M', hM', ?_⟩
  have hEq0 := congrArg (fun X ↦ (X (fun _ ↦ 0)).1) (hEquiv.wp_eq (fun _ ↦ M) (fun _ _ ↦ rfl))
  simp only [hM', CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, HermitianMat.conj_conj,
    hProjConj] at hEq0
  simpa [HermitianMat.conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose,
    Matrix.mul_assoc] using congrArg Subtype.val (hEq0.trans (HermitianMat.conj_conj _ _ _).symm)
theorem CleanPhasePermEquiv.wrapSymStep {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (s : SymTempAndStep n) {M_set : Finset (Wire n)}
    (hdisj_SM : Disjoint s.S M_set) (rTotal : QRegister (m + 1) n) (hanc : s.anc = rTotal 0)
    (hdisj_S_rest : Disjoint s.S (rTotal.slice 1 m (by omega)).image)
      {d_inner : DynamicCircuit Var n} {c_inner : Circuit n} {φ_inner : BitAssignment n → ℂ}
    {f_inner : BitAssignment n → BitAssignment n} (hInner : CleanPhasePermEquiv v
    (rTotal.slice 1 m (by omega)) M_set d_inner c_inner φ_inner f_inner) : CleanPhasePermEquiv v
      rTotal M_set (s.toTempAndStep.wrapDynamic v d_inner)
    (s.toTempAndStep.wrapCircuit c_inner) (fun β ↦ φ_inner (s.stepFwd β)) (fun β w ↦
      if w ∈ M_set then f_inner (s.stepFwd β) w else β w) := by
  obtain ⟨hPP, hWp⟩ :=
    symTempAndStep_wrap_phasePerm_correct v s hdisj_SM d_inner c_inner φ_inner f_inner rTotal hanc
    hdisj_S_rest hInner.phasePerm hInner.wp_eq
  exact ⟨preservesVarIndep_wrapDynamic v s.toTempAndStep hInner.varIndep,
    storeClosed_wrapDynamic v s.toTempAndStep hInner.storeClosed, hPP, hWp⟩
theorem zmod2_half_adder_val_zm (u t : ZMod 2) : (u + t).val + 2 * (u * t).val = u.val + t.val := by
  revert u t; decide
set_option allowUnsafeReducibility true in
theorem phasePerm_cnotFanout {m n : ℕ} [NeZero (2 ^ n)] (wNeg : Wire n) (rT : QRegister m n)
    (hwNeg : wNeg ∉ rT.image) :
    PhasePerm rT.image (cnotFanoutCircuit m wNeg rT hwNeg) (fun _ ↦ 1) (fanoutToggleFn wNeg rT) :=
  PhasePerm.of_classicalPerm (localClassicalPerm_cnotFanout m wNeg rT hwNeg).perm
    (fun β _ hw ↦ fanoutToggleFn_of_not_mem wNeg rT β hw)
theorem regVal_fanoutToggleFn {m n : ℕ} (wNeg : Wire n) (rT : QRegister m n) (β : BitAssignment n) :
    regVal rT (fanoutToggleFn wNeg rT β) =
    if β wNeg = 0 then regVal rT β else (2 ^ m - 1) - regVal rT β := by
  rcases bit_cases (β wNeg) with hw0 | hw1
  · simp only [hw0, ↓reduceIte]
    exact regVal_congr rT fun j ↦ by
      rw [fanoutToggleFn_of_mem wNeg rT β ((QRegister.mem_image rT _).mpr ⟨j, rfl⟩), hw0, add_zero]
  · simp only [hw1, (by decide : (1 : ZMod 2) ≠ 0), ↓reduceIte]
    have hComp := onesComplement_bitsVal (fun j : Fin m ↦ β (rT j))
    rw [show regVal rT (fanoutToggleFn wNeg rT β) = bitsVal (fun j : Fin m ↦ β (rT j) + 1) from
      congrArg bitsVal (funext fun j ↦ by
        rw [fanoutToggleFn_of_mem wNeg rT β ((QRegister.mem_image rT _).mpr ⟨j, rfl⟩), hw1])]
    change _ = (2 ^ m - 1) - bitsVal (fun j : Fin m ↦ β (rT j))
    omega
theorem signed_carry_shift_algebra {s W : ℕ} (hs45 : s + W = 45)
    (V_lo V_hi V_mid V_hi' U : ℕ) (c_out b_neg : ZMod 2)
    (hVhi_lt : V_hi < 2 ^ W) (hVmid_lt : V_mid < 2 ^ W)
    (hCase0 : b_neg = 0 → V_mid + 2 ^ W * c_out.val = V_hi + U ∧ V_hi' = V_mid)
    (hCase1 : b_neg = 1 →
      V_mid + 2 ^ W * c_out.val = (2 ^ W - 1 - V_hi) + U ∧ V_hi' = (2 ^ W - 1) - V_mid) :
    let V_45 : ℕ := V_lo + 2 ^ s * V_hi
    let V_45' : ℕ := V_lo + 2 ^ s * V_hi'
    let sgn : ℤ := 1 - 2 * (b_neg.val : ℤ)
    ((V_45' : ℤ) - ((V_45 : ℤ) + sgn * (2 ^ s : ℤ) * (U : ℤ))) % (2 ^ 45 : ℤ) = 0 ∧
      sgn * (2 ^ s : ℤ) * (U : ℤ) - ((V_45' : ℤ) - (V_45 : ℤ)) =
        sgn * (2 ^ 45 : ℤ) * (c_out.val : ℤ) := by
  intro V_45 V_45' sgn
  have hPow45 : (2 ^ s : ℤ) * (2 ^ W : ℤ) = (2 ^ 45 : ℤ) := by rw [← pow_add, hs45]
  have hDiff : (V_hi' : ℤ) - (V_hi : ℤ) = sgn * ((U : ℤ) - (2 ^ W : ℤ) * (c_out.val : ℤ)) := by
    rcases bit_cases b_neg with hb0 | hb1
    · obtain ⟨hAdd, rfl⟩ := hCase0 hb0
      have hAddZ : (V_hi' : ℤ) + (2 ^ W : ℤ) * (c_out.val : ℤ) = (V_hi : ℤ) + (U : ℤ) := by
        exact_mod_cast hAdd
      dsimp only [sgn]
      rw [hb0, ZMod.val_zero, Nat.cast_zero]
      linarith
    · obtain ⟨hAdd, rfl⟩ := hCase1 hb1
      have hAddZ := congrArg (Nat.cast (R := ℤ)) hAdd
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        Nat.cast_sub (by omega : V_hi ≤ 2 ^ W - 1), Nat.cast_sub Nat.one_le_two_pow] at hAddZ
      have hVpZ : (((2 ^ W - 1) - V_mid : ℕ) : ℤ) = (2 ^ W : ℤ) - 1 - (V_mid : ℤ) := by
        simp [Nat.cast_sub (by omega : V_mid ≤ 2 ^ W - 1), Nat.cast_sub Nat.one_le_two_pow]
      dsimp only [sgn]
      rw [hb1, show ((1 : ZMod 2).val : ℤ) = 1 from rfl]
      linarith
  have hMain : (V_45' : ℤ) - (V_45 : ℤ) =
      sgn * (2 ^ s : ℤ) * (U : ℤ) - sgn * (2 ^ 45 : ℤ) * (c_out.val : ℤ) := by
    rw [show (V_45' : ℤ) - (V_45 : ℤ) = (2 ^ s : ℤ) * ((V_hi' : ℤ) - (V_hi : ℤ)) by
      dsimp only [V_45, V_45']
      push_cast
      ring, hDiff, ← hPow45]
    ring
  refine ⟨?_, by linarith⟩
  rw [show (V_45' : ℤ) - ((V_45 : ℤ) + sgn * (2 ^ s : ℤ) * (U : ℤ)) = (-sgn * (c_out.val : ℤ)) *
    (2 ^ 45 : ℤ) by linarith, Int.mul_emod_left]
def apexGidneyRippleAuxCircuit {n : ℕ} (cApex : Wire n → Circuit n) :
    (k : ℕ) → (uWires : Fin (k + 1) → Wire n) → (rT rC : QRegister (k + 1) n) → (c_in : Wire n) →
    (∀ j, uWires j ∉ rT.image) → (∀ j, uWires j ∉ rC.image) → rT.DisjointWires rC →
    (∀ j, c_in ≠ uWires j) → c_in ∉ rT.image → c_in ∉ rC.image → Circuit n
  | 0, uWires, rT, rC, c_in, hu_T, hu_C, hdisj_TC, hcin_u, hcin_T, hcin_C =>
      let hut := rT.ne_apply_of_not_mem_image _ (hu_T 0) 0
      let hcin_t := rT.ne_apply_of_not_mem_image _ hcin_T 0
      ((carrySymStep (uWires 0) (rT 0) c_in (rC 0) hut (hcin_u 0).symm
        (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0)
          hcin_t.symm (hdisj_TC.ne 0 0)
            (rC.ne_apply_of_not_mem_image _ hcin_C 0)).toTempAndStep.wrapCircuit (cApex (rC 0))) ;;ᶜ
      (Circuit.CNOT c_in (rT 0) hcin_t ;;ᶜ Circuit.CNOT (uWires 0) (rT 0) hut)
  | k + 1, uWires, rT, rC, c_in, hu_T, hu_C, hdisj_TC, hcin_u, hcin_T, hcin_C =>
      let hut := rT.ne_apply_of_not_mem_image _ (hu_T 0) 0
      let hcin_t := rT.ne_apply_of_not_mem_image _ hcin_T 0
      ((carrySymStep (uWires 0) (rT 0) c_in (rC 0) hut (hcin_u 0).symm
        (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0)
          hcin_t.symm (hdisj_TC.ne 0 0)
            (rC.ne_apply_of_not_mem_image _ hcin_C 0)).toTempAndStep.wrapCircuit
        (apexGidneyRippleAuxCircuit cApex k (fun j ↦
          uWires j.succ) (rT.slice 1 (k + 1) (by omega)) (rC.slice 1 (k + 1) (by omega)) (rC 0)
          (fun j hj ↦ hu_T j.succ (rT.image_compose_subset _ hj)) (fun j hj ↦
            hu_C j.succ (rC.image_compose_subset _ hj))
          ((hdisj_TC.compose_left _).compose_right _) (fun j h ↦
            hu_C j.succ ((rC.mem_image _).mpr ⟨0, h⟩))
          (fun hj ↦
            hdisj_TC.apply_not_mem_left 0 (rT.image_compose_subset _ hj))
            (QRegExt.head_not_mem_tail_image rC))) ;;ᶜ
      (Circuit.CNOT c_in (rT 0) hcin_t ;;ᶜ Circuit.CNOT (uWires 0) (rT 0) hut)
def apexGidneyRippleAuxDyn {Var : Type} {n : ℕ} (v : Var) (cApex : Wire n → Circuit n) :
    (k : ℕ) → (uWires : Fin (k + 1) → Wire n) → (rT rC : QRegister (k + 1) n) → (c_in : Wire n) →
    (∀ j, uWires j ∉ rT.image) → (∀ j, uWires j ∉ rC.image) → rT.DisjointWires rC →
    (∀ j, c_in ≠ uWires j) → c_in ∉ rT.image → c_in ∉ rC.image → DynamicCircuit Var n
  | 0, uWires, rT, rC, c_in, hu_T, hu_C, hdisj_TC, hcin_u, hcin_T, hcin_C =>
      let hut := rT.ne_apply_of_not_mem_image _ (hu_T 0) 0
      let hcin_t := rT.ne_apply_of_not_mem_image _ hcin_T 0
      .seq
        ((carrySymStep (uWires 0) (rT 0) c_in (rC 0) hut (hcin_u 0).symm
        (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0)
            hcin_t.symm (hdisj_TC.ne 0 0)
              (rC.ne_apply_of_not_mem_image _ hcin_C 0)).toTempAndStep.wrapDynamic v
              (.circuit (cApex (rC 0))))
        (.circuit (Circuit.CNOT c_in (rT 0) hcin_t ;;ᶜ Circuit.CNOT (uWires 0) (rT 0) hut))
  | k + 1, uWires, rT, rC, c_in, hu_T, hu_C, hdisj_TC, hcin_u, hcin_T, hcin_C =>
      let hut := rT.ne_apply_of_not_mem_image _ (hu_T 0) 0
      let hcin_t := rT.ne_apply_of_not_mem_image _ hcin_T 0
      .seq
        ((carrySymStep (uWires 0) (rT 0) c_in (rC 0) hut (hcin_u 0).symm
        (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0)
            hcin_t.symm (hdisj_TC.ne 0 0)
              (rC.ne_apply_of_not_mem_image _ hcin_C 0)).toTempAndStep.wrapDynamic v
          (apexGidneyRippleAuxDyn v cApex k (fun j ↦
            uWires j.succ) (rT.slice 1 (k + 1) (by omega)) (rC.slice 1 (k + 1) (by omega)) (rC 0)
            (fun j hj ↦ hu_T j.succ (rT.image_compose_subset _ hj)) (fun j hj ↦
              hu_C j.succ (rC.image_compose_subset _ hj))
            ((hdisj_TC.compose_left _).compose_right _) (fun j h ↦
              hu_C j.succ ((rC.mem_image _).mpr ⟨0, h⟩))
            (fun hj ↦
              hdisj_TC.apply_not_mem_left 0 (rT.image_compose_subset _ hj))
              (QRegExt.head_not_mem_tail_image rC)))
        (.circuit (Circuit.CNOT c_in (rT 0) hcin_t ;;ᶜ Circuit.CNOT (uWires 0) (rT 0) hut))
theorem count_apexGidneyRippleAuxDyn_toff {Var : Type} {n : ℕ} (v : Var) (cApex : Wire n →
    Circuit n) (hApexToff : ∀ w, (cApex w).count .TOFF = 0) (k : ℕ)
    (uWires : Fin (k + 1) → Wire n) (rT : QRegister (k + 1) n) (rC : QRegister (k + 1) n)
    (c_in : Wire n) (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j,
      uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) : (apexGidneyRippleAuxDyn v cApex k
    uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).count .TOFF = 0 := by
  induction k generalizing c_in with
  | zero =>
      rw [apexGidneyRippleAuxDyn]
      simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq,
        TempAndStep.count_wrapDynamic_toff _ _ _ (carrySymStep ..).clifford,
        dyn_count_circuit, hApexToff]
      rfl
  | succ k ih =>
      rw [apexGidneyRippleAuxDyn]
      simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq,
        TempAndStep.count_wrapDynamic_toff _ _ _ (carrySymStep ..).clifford, ih]
      rfl
theorem count_apexGidneyRippleAuxDyn_t {Var : Type} {n : ℕ} (v : Var) (cApex : Wire n →
    Circuit n) (hApexT : ∀ w, (cApex w).count .T = 1) (k : ℕ)
    (uWires : Fin (k + 1) → Wire n) (rT : QRegister (k + 1) n) (rC : QRegister (k + 1) n)
    (c_in : Wire n) (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j,
      uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) : (apexGidneyRippleAuxDyn v cApex k
    uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).count .T = 4 * (k + 1) + 1 := by
  induction k generalizing c_in with
  | zero =>
      rw [apexGidneyRippleAuxDyn]
      simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq,
        TempAndStep.count_wrapDynamic_t _ _ _ (carrySymStep ..).clifford, dyn_count_circuit, hApexT]
      rfl
  | succ k ih =>
      rw [apexGidneyRippleAuxDyn]
      simp only [NuclearTwistMulKickAndBridge288.count_dyn_seq,
        TempAndStep.count_wrapDynamic_t _ _ _ (carrySymStep ..).clifford, ih]
      have h0 :
          (DynamicCircuit.circuit (Var := Var)
            (Circuit.CNOT c_in (rT 0) (QRegister.ne_apply_of_not_mem_image rT _ hcin_T 0) ;;ᶜ
              Circuit.CNOT (uWires 0) (rT 0)
                (QRegister.ne_apply_of_not_mem_image rT _ (hu_T 0) 0))).count .T = 0 := rfl
      rw [h0]
      omega
private theorem apexGidneyTail_equiv {Var : Type} [Fintype Var] [DecidableEq Var] {k n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (u0 c_in : Wire n) (rT rC : QRegister (k + 1) n)
    (hdisj_TC : rT.DisjointWires rC) (hut : u0 ≠ rT 0) (hcin_t : c_in ≠ rT 0)
    {dW : DynamicCircuit Var n} {cW : Circuit n}
    {φW : BitAssignment n → ℂ} {fW : BitAssignment n → BitAssignment n}
    (hWrap : CleanPhasePermEquiv v rC rT.image dW cW φW fW) :
    let cTail := Circuit.CNOT c_in (rT 0) hcin_t ;;ᶜ Circuit.CNOT u0 (rT 0) hut
    let fTail := (fun γ : BitAssignment n ↦ Function.update γ (rT 0) (γ (rT 0) + γ u0)) ∘
      (fun γ : BitAssignment n ↦ Function.update γ (rT 0) (γ (rT 0) + γ c_in))
    CleanPhasePermEquiv v rC rT.image (.seq dW (.circuit cTail)) (cW ;;ᶜ cTail)
      (fun β ↦ φW β * 1) (fTail ∘ fW) := by
  have ht0_mem : rT 0 ∈ rT.image := (rT.mem_image _).mpr ⟨0, rfl⟩
  have hPP_c1 : PhasePerm rT.image (Circuit.CNOT c_in (rT 0) hcin_t) (fun _ ↦ 1) (fun γ ↦
    Function.update γ (rT 0) (γ (rT 0) + γ c_in)) :=
    PhasePerm.of_classicalPerm (ClassicalPerm.CNOT c_in (rT 0) hcin_t)
      (fun γ w hw ↦ Function.update_of_ne (fun h : w = rT 0 ↦ hw (h ▸ ht0_mem)) _ _)
  have hPP_c2 : PhasePerm rT.image (Circuit.CNOT u0 (rT 0) hut) (fun _ ↦ 1) (fun γ ↦
    Function.update γ (rT 0) (γ (rT 0) + γ u0)) :=
    PhasePerm.of_classicalPerm (ClassicalPerm.CNOT u0 (rT 0) hut)
      (fun γ w hw ↦ Function.update_of_ne (fun h : w = rT 0 ↦ hw (h ▸ ht0_mem)) _ _)
  exact CleanPhasePermEquiv.seq
    ((QRegExt.disjointWires_iff_disjoint_image rT rC).mp hdisj_TC) hWrap
    (CleanPhasePermEquiv.ofCircuit v rC
      ((hPP_c1.seq hPP_c2).congr_phase fun _ ↦ mul_one 1))
theorem apexGidneyRippleAux_correct {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (cApex : Wire n → Circuit n)
    (φApex : BitAssignment n → ZMod 2 → ℂ) (k : ℕ) (uWires : Fin (k + 1) →
      Wire n) (rT : QRegister (k + 1) n) (rC : QRegister (k + 1) n) (c_in : Wire n)
    (hu_T : ∀ j, uWires j ∉ rT.image) (hu_C : ∀ j,
      uWires j ∉ rC.image) (hdisj_TC : rT.DisjointWires rC) (hcin_u : ∀ j, c_in ≠ uWires j)
    (hcin_T : c_in ∉ rT.image) (hcin_C : c_in ∉ rC.image) (hApex_pp : ∀ w ∈ rC.image,
    PhasePerm (∅ : Finset (Wire n)) (cApex w) (fun γ ↦ φApex γ (γ w)) id) (hApex_upd : ∀ (γ :
    BitAssignment n) (w : Wire n), w ∈ rC.image → ∀ b : ZMod 2, φApex (Function.update γ w b)
    = φApex γ) : ∃ φ f, CleanPhasePermEquiv v rC rT.image (apexGidneyRippleAuxDyn v cApex k
    uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) (apexGidneyRippleAuxCircuit
    cApex k uWires rT rC c_in hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) φ f ∧ (∀ β, (∀ i : Fin
    (k + 1), β (rC i) = 0) → ∃ c_out : ZMod 2, regVal rT (f β) + 2 ^ (k + 1) * c_out.val =
    regVal rT β + bitsVal (fun j ↦ β (uWires j)) + (β c_in).val ∧ φ β = φApex β c_out) := by
  induction k generalizing c_in with
  | zero =>
      let hut := rT.ne_apply_of_not_mem_image _ (hu_T 0) 0
      let hcin_t := rT.ne_apply_of_not_mem_image _ hcin_T 0
      let st := carrySymStep (uWires 0) (rT 0) c_in (rC 0) hut (hcin_u 0).symm
        (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0) hcin_t.symm (hdisj_TC.ne 0 0)
        (rC.ne_apply_of_not_mem_image _ hcin_C 0)
      have hc0_mem : rC 0 ∈ rC.image := (rC.mem_image _).mpr ⟨0, rfl⟩
      have hWrap := (CleanPhasePermEquiv.wrapSymStep v st (Finset.disjoint_empty_right _)
        rC rfl (Finset.disjoint_right.mpr fun w hw ↦
          Fin.elim0 ((QRegister.mem_image _ w).mp hw).choose)
        (CleanPhasePermEquiv.ofCircuit v _ (hApex_pp (rC 0) hc0_mem))).mono
        (Finset.empty_subset rT.image)
      refine ⟨_, _, apexGidneyTail_equiv v (uWires 0) c_in rT rC hdisj_TC hut hcin_t hWrap,
        fun β hz ↦ ⟨β c_in + (β (uWires 0) + β c_in) * (β (rT 0) + β c_in), ?_, ?_⟩⟩
      · have hReg0 (r0 : QRegister 0 n) (γ : BitAssignment n) : regVal r0 γ = 0 := by
          simp [regVal, bitsVal]
        have hBits1 : bitsVal (fun j : Fin 1 ↦ β (uWires j)) = (β (uWires 0)).val := by
          simp [bitsVal]
        rw [regVal_head_tail, regVal_head_tail, hReg0, hReg0, hBits1]
        simp only [zero_add, mul_zero, add_zero, _root_.pow_one, Function.comp_apply,
          Finset.notMem_empty, ↓reduceIte, Function.update_self, Function.update_of_ne hut]
        rw [show β (rT 0) + β c_in + β (uWires 0) = β (uWires 0) + β (rT 0) + β c_in by ring]
        linarith [zmod2_full_adder_val_zm (β (uWires 0)) (β (rT 0)) (β c_in)]
      · rw [mul_one, carrySymStep_stepFwd (uWires 0) (rT 0) c_in (rC 0) hut (hcin_u 0).symm
          (rC.ne_apply_of_not_mem_image _ (hu_C 0) 0) hcin_t.symm (hdisj_TC.ne 0 0)
          (rC.ne_apply_of_not_mem_image _ hcin_C 0) β (hz 0),
          hApex_upd β (rC 0) hc0_mem _, Function.update_self]
  | succ k ih =>
      let rT_rest := rT.slice 1 (k + 1) (by omega)
      let rC_rest := rC.slice 1 (k + 1) (by omega)
      have hut : uWires 0 ≠ rT 0 := rT.ne_apply_of_not_mem_image _ (hu_T 0) 0
      have huc : uWires 0 ≠ rC 0 := rC.ne_apply_of_not_mem_image _ (hu_C 0) 0
      have htc : rT 0 ≠ rC 0 := hdisj_TC.ne 0 0
      have hcin_t : c_in ≠ rT 0 := rT.ne_apply_of_not_mem_image _ hcin_T 0
      have hcin_c : c_in ≠ rC 0 := rC.ne_apply_of_not_mem_image _ hcin_C 0
      have hc0_u (j : Fin (k + 1)) : rC 0 ≠ uWires j.succ :=
        fun h ↦ hu_C j.succ ((rC.mem_image _).mpr ⟨0, h⟩)
      have hc0_T_rest : rC 0 ∉ rT_rest.image :=
        fun hj ↦ hdisj_TC.apply_not_mem_left 0 (rT.image_compose_subset _ hj)
      have hc0_C_rest : rC 0 ∉ rC_rest.image := (QRegExt.head_not_mem_tail_image rC)
      have ht0_T_rest : rT 0 ∉ rT_rest.image := (QRegExt.head_not_mem_tail_image rT)
      have hu0_T_rest : uWires 0 ∉ rT_rest.image := fun hj ↦
        hu_T 0 (rT.image_compose_subset _ hj)
      have hcin_T_rest : c_in ∉ rT_rest.image := fun hj ↦
        hcin_T (rT.image_compose_subset _ hj)
      obtain ⟨φ_rest, f_rest, hEq_rest, hVal_rest⟩ := ih (fun j ↦ uWires j.succ) rT_rest
          rC_rest (rC 0)
          (fun j hj ↦ hu_T j.succ (rT.image_compose_subset _ hj))
          (fun j hj ↦ hu_C j.succ (rC.image_compose_subset _ hj))
          ((hdisj_TC.compose_left _).compose_right _) hc0_u hc0_T_rest hc0_C_rest
          (fun w hw ↦ hApex_pp w (rC.image_compose_subset _ hw))
          (fun γ w hw ↦ hApex_upd γ w (rC.image_compose_subset _ hw))
      let st := carrySymStep (uWires 0) (rT 0) c_in (rC 0)
        hut (hcin_u 0).symm huc hcin_t.symm htc hcin_c
      have hDisjSM : Disjoint st.S rT_rest.image := by
        rw [show st.S = {uWires 0, rT 0, c_in, rC 0} from rfl]
        simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
        exact ⟨hu0_T_rest, ht0_T_rest, hcin_T_rest, hc0_T_rest⟩
      have hDisjSR : Disjoint st.S rC_rest.image := by
        rw [show st.S = {uWires 0, rT 0, c_in, rC 0} from rfl]
        simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
        exact ⟨fun hj ↦ hu_C 0 (rC.image_compose_subset _ hj),
          fun hj ↦ hdisj_TC.apply_not_mem_right 0 (rC.image_compose_subset _ hj),
          fun hj ↦ hcin_C (rC.image_compose_subset _ hj), hc0_C_rest⟩
      have hWrap := (CleanPhasePermEquiv.wrapSymStep v st hDisjSM rC rfl hDisjSR hEq_rest).mono
        (rT.image_compose_subset _)
      refine ⟨_, _, apexGidneyTail_equiv v (uWires 0) c_in rT rC hdisj_TC hut hcin_t hWrap,
        fun β hz ↦ ?_⟩
      let c₀ : ZMod 2 := β c_in + (β (uWires 0) + β c_in) * (β (rT 0) + β c_in)
      have hStep : st.stepFwd β = Function.update β (rC 0) c₀ :=
        carrySymStep_stepFwd (uWires 0) (rT 0) c_in (rC 0)
          hut (hcin_u 0).symm huc hcin_t.symm htc hcin_c β (hz 0)
      let β_mid := st.stepFwd β
      have hz_rest (i : Fin (k + 1)) : β_mid (rC_rest i) = 0 := by
        have hi_mem : rC_rest i ∈ rC_rest.image := (rC_rest.mem_image _).mpr ⟨i, rfl⟩
        dsimp only [β_mid]
        rw [hStep, Function.update_of_ne (fun h : rC_rest i = rC 0 ↦ hc0_C_rest (h ▸ hi_mem))]
        obtain ⟨q, hq⟩ := (rC.mem_image _).mp (rC.image_compose_subset _ hi_mem)
        exact hq ▸ hz q
      obtain ⟨c_out, hVal_mid, hPhi_mid⟩ := hVal_rest β_mid hz_rest
      have hc0_mem : rC 0 ∈ rC.image := (rC.mem_image _).mpr ⟨0, rfl⟩
      refine ⟨c_out, ?_, ?_⟩
      · have hT_mid : regVal rT_rest β_mid = regVal rT_rest β :=
          regVal_congr rT_rest fun i ↦ by
            dsimp only [β_mid]
            rw [hStep, Function.update_of_ne fun h : rT_rest i = rC 0 ↦
              hc0_T_rest (h ▸ (rT_rest.mem_image _).mpr ⟨i, rfl⟩)]
        have hc0_mid : β_mid (rC 0) = c₀ := by
          dsimp only [β_mid]
          rw [hStep, Function.update_self]
        rw [hT_mid, show bitsVal (fun j : Fin (k + 1) ↦ β_mid (uWires j.succ)) =
              bitsVal (fun j : Fin (k + 1) ↦ β (uWires j.succ)) from
            congrArg bitsVal (funext fun j ↦ by
              dsimp only [β_mid]
              rw [hStep, Function.update_of_ne (hc0_u j).symm]),
          hc0_mid] at hVal_mid
        let fTail :=
          (fun γ : BitAssignment n ↦ Function.update γ (rT 0) (γ (rT 0) + γ (uWires 0))) ∘
            (fun γ : BitAssignment n ↦ Function.update γ (rT 0) (γ (rT 0) + γ c_in))
        let fAll := fTail ∘ fun (γ : BitAssignment n) (w : Wire n) ↦
          if w ∈ rT_rest.image then f_rest (st.stepFwd γ) w else γ w
        have hf0 : fAll β (rT 0) = β (uWires 0) + β (rT 0) + β c_in := by
          simp only [fAll, fTail, Function.comp_apply, ht0_T_rest, hu0_T_rest, hcin_T_rest,
            ↓reduceIte, Function.update_self, Function.update_of_ne hut]
          ring
        have hf_rest : regVal rT_rest (fAll β) = regVal rT_rest (f_rest β_mid) :=
          regVal_congr rT_rest fun i ↦ by
            have hi_mem : rT_rest i ∈ rT_rest.image := (rT_rest.mem_image _).mpr ⟨i, rfl⟩
            simp [fAll, fTail, β_mid,
              Function.update_of_ne (fun h : rT_rest i = rT 0 ↦ ht0_T_rest (h ▸ hi_mem))]
        rw [regVal_head_tail rT (fAll β), hf0, hf_rest, regVal_head_tail rT β,
          @bitsVal_succ_head_tail (k + 1) (fun j ↦ β (uWires j)),
          show 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) from pow_succ' 2 (k + 1)]
        dsimp only [c₀] at hVal_mid
        linarith [zmod2_full_adder_val_zm (β (uWires 0)) (β (rT 0)) (β c_in)]
      · rw [mul_one, hPhi_mid]
        dsimp only [β_mid]
        rw [hStep, hApex_upd β (rC 0) hc0_mem c₀]
attribute [local irreducible] apexGidneyRippleAuxDyn apexGidneyRippleAuxCircuit
end ConfigSlot2ZeroMuxPureGidney48
end Slot2ZeroMuxSignedMul46
end
end ModSlot2ZeroMuxPureGidney48

end QuantumComputation.Specs.StoppingPowerSolution
