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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot5MatScaleCert

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModZeroAncillaUSP
set_option exponentiation.threshold 256
@[expose] public section
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace ZeroAncillaUSP
instance (priority := 100000) instNeZeroTwoPowUSP (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable abbrev ket {n : ℕ} (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  MeasureBranchHadamardSem.ket β
@[simp] theorem basisBits_symm_eq {m : ℕ} (γ : BitAssignment m) :
    basisBits m ((basisBitsEquiv m).symm γ) = γ := (basisBitsEquiv m).apply_symm_apply γ
@[simp] theorem symm_basisBits_eq {m : ℕ} (j : Fin (2 ^ m)) :
    (basisBitsEquiv m).symm (basisBits m j) = j := (basisBitsEquiv m).symm_apply_apply j
theorem upd_eq_self {n : ℕ} (β : BitAssignment n) (q : Wire n) {v : ZMod 2} (h : β q = v) :
    Function.update β q v = β := h ▸ Function.update_eq_self q β
theorem ite_pos' {α : Type*} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := ite_eq_left hp
theorem dite_neg' {α : Type*} {p : Prop} [Decidable p] (hp : ¬ p) (a : p → α) (b : ¬ p → α) :
    (if h : p then a h else b h) = b hp := dite_eq_right hp
noncomputable def writeReg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeReg_apply_reg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]
theorem writeReg_apply_of_not_mem {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) : writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
theorem lt_pow_succ_of_lt {d : ℕ} (p : Fin (2 ^ d)) : p.val < 2 ^ (d + 1) := by
  have := p.isLt; rw [pow_succ]; omega
theorem add_lt_pow_succ {d : ℕ} (p : Fin (2 ^ d)) : 2 ^ d + p.val < 2 ^ (d + 1) := by
  have := p.isLt; rw [pow_succ]; omega
theorem sub_pow_lt_of_not_lt {m : ℕ} (j : Fin (2 ^ (m + 1))) (h : ¬ j.val < 2 ^ m) :
    j.val - 2 ^ m < 2 ^ m := by
  have := j.isLt; have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
  omega
structure Zw where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  deriving DecidableEq, Repr
noncomputable def omega8 : ℂ := (1 + Complex.I) / (√2 : ℂ)
theorem sqrt2_mul_self_c : (√2 : ℂ) * (√2 : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
theorem sqrt2_ne_zero_c : (√2 : ℂ) ≠ 0 := by
  exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
theorem omega8_sq : omega8 ^ 2 = Complex.I := by
  rw [omega8, div_pow, sq (√2 : ℂ), sqrt2_mul_self_c]
  linear_combination Complex.I_sq / 2
theorem omega8_pow_four : omega8 ^ 4 = -1 := by
  linear_combination (omega8 ^ 2 + Complex.I) * omega8_sq + Complex.I_sq
theorem star_omega8 : star omega8 = -omega8 ^ 3 := by
  have h1 : star omega8 = (1 - Complex.I) / (√2 : ℂ) := by
    simp [omega8, Complex.conj_ofReal]
    ring
  rw [h1, show omega8 ^ 3 = omega8 ^ 2 * omega8 by ring, omega8_sq, omega8]
  ring_nf
  rw [Complex.I_sq]
  ring
theorem omega8_sub_cube_eq_sqrt2 : omega8 - omega8 ^ 3 = (√2 : ℂ) := by
  rw [show omega8 ^ 3 = omega8 ^ 2 * omega8 by ring, omega8_sq, omega8]
  field_simp [sqrt2_ne_zero_c]
  rw [sq (√2 : ℂ), sqrt2_mul_self_c]; ring_nf; rw [Complex.I_sq]; ring
noncomputable def Zw.toComplex (z : Zw) : ℂ :=
  (z.c0 : ℂ) + (z.c1 : ℂ) * omega8 + (z.c2 : ℂ) * omega8 ^ 2 + (z.c3 : ℂ) * omega8 ^ 3
def zwAdd (a b : Zw) : Zw := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩
def zwSub (a b : Zw) : Zw := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3⟩
def zwMulI (a : Zw) : Zw := ⟨-a.c2, -a.c3, a.c0, a.c1⟩
def zwMulW (a : Zw) : Zw := ⟨-a.c3, a.c0, a.c1, a.c2⟩
def zwConj (a : Zw) : Zw := ⟨a.c0, -a.c3, -a.c2, -a.c1⟩
def zwMul (a b : Zw) : Zw := ⟨a.c0 * b.c0 - a.c1 * b.c3 - a.c2 * b.c2 - a.c3 * b.c1, a.c0 *
    b.c1 + a.c1 * b.c0 - a.c2 * b.c3 - a.c3 * b.c2, a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 -
    a.c3 * b.c3, a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0⟩
theorem toComplex_zwAdd (a b : Zw) : (zwAdd a b).toComplex = a.toComplex + b.toComplex := by
  simp only [zwAdd, Zw.toComplex, Int.cast_add]; ring
theorem toComplex_zwConj (a : Zw) : (zwConj a).toComplex = star a.toComplex := by
  have hs2 : star (omega8 ^ 2) = -omega8 ^ 2 := by rw [omega8_sq, Complex.star_def, Complex.conj_I]
  have hs3 : star (omega8 ^ 3) = -omega8 := by
    rw [star_pow, star_omega8]; linear_combination -(omega8 ^ 4 - 1) * omega8 * omega8_pow_four
  have hc_int (k : ℤ) : star (k : ℂ) = (k : ℂ) := by simp
  simp only [zwConj, Zw.toComplex, Int.cast_neg, star_add, star_mul, hc_int, star_omega8, hs2, hs3]
  ring
theorem toComplex_zwMul (a b : Zw) : (zwMul a b).toComplex = a.toComplex * b.toComplex := by
  simp only [zwMul, Zw.toComplex, Int.cast_add, Int.cast_sub, Int.cast_mul]
  linear_combination
    (-((a.c1 : ℂ) * (b.c3 : ℂ) + (a.c2 : ℂ) * (b.c2 : ℂ) + (a.c3 : ℂ) * (b.c1 : ℂ)) -
      ((a.c2 : ℂ) * (b.c3 : ℂ) + (a.c3 : ℂ) * (b.c2 : ℂ)) * omega8 -
      (a.c3 : ℂ) * (b.c3 : ℂ) * omega8 ^ 2) * omega8_pow_four
theorem normSq_zw_eq (a : Zw) :
    ‖a.toComplex‖ ^ 2 = ((zwMul a (zwConj a)).c0 : ℝ) + ((zwMul a (zwConj a)).c1 : ℝ) * √2 := by
  let p := zwMul a (zwConj a)
  have hc2 : p.c2 = 0 := by dsimp [p, zwMul, zwConj]; ring
  have hc3 : p.c3 = -p.c1 := by dsimp [p, zwMul, zwConj]; ring
  have hreal : (Complex.normSq a.toComplex : ℂ) = ((p.c0 : ℝ) + (p.c1 : ℝ) * √2 : ℝ) := by
    rw [← Complex.mul_conj]; change a.toComplex * star a.toComplex = _
    rw [← toComplex_zwConj, ← toComplex_zwMul]
    calc p.toComplex = (p.c0 : ℂ) + (p.c1 : ℂ) * (omega8 - omega8 ^ 3) := by
          simp only [Zw.toComplex, hc2, hc3, Int.cast_zero, Int.cast_neg]; ring
      _ = ((p.c0 : ℝ) + (p.c1 : ℝ) * √2 : ℝ) := by rw [omega8_sub_cube_eq_sqrt2]; push_cast; ring
  rw [Complex.sq_norm]; exact Complex.ofReal_injective hreal
inductive HSTGate where
  | H | S | T
  deriving DecidableEq, Repr
def hstGateCircuit {n : ℕ} (g : HSTGate) (q : Wire n) : Circuit n :=
  match g with | .H => Circuit.H q | .S => Circuit.S q | .T => Circuit.T q
def hstWordCircuit {n : ℕ} (w : List HSTGate) (q : Wire n) : Circuit n :=
  match w with | [] => Circuit.identity | g :: gs => hstGateCircuit g q ;;ᶜ hstWordCircuit gs q
def hstWordTCount (w : List HSTGate) : ℕ :=
  match w with | [] => 0 | .T :: gs => 1 + hstWordTCount gs | _ :: gs => hstWordTCount gs
def ctrlProbGate {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t) : Circuit n :=
  (hstWordCircuit w t).inverse ;;ᶜ Circuit.CNOT c t hct ;;ᶜ hstWordCircuit w t
@[simp] theorem count_toff_hstWordCircuit {n : ℕ} (w : List HSTGate) (q : Wire n) :
    (hstWordCircuit w q).count PrimitiveGate.TOFF = 0 := by
  induction w with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [hstWordCircuit, hstGateCircuit, ih]
@[simp] theorem count_t_hstWordCircuit {n : ℕ} (w : List HSTGate) (q : Wire n) :
    (hstWordCircuit w q).count PrimitiveGate.T = hstWordTCount w := by
  induction w with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [hstWordCircuit, hstGateCircuit, hstWordTCount, ih]
@[simp] theorem count_toff_ctrlProbGate {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t) :
    (ctrlProbGate w c t hct).count PrimitiveGate.TOFF = 0 := by simp [ctrlProbGate]
@[simp] theorem count_t_ctrlProbGate {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t) :
    (ctrlProbGate w c t hct).count PrimitiveGate.T = 2 * hstWordTCount w := by
      simp [ctrlProbGate, two_mul]
structure Mat2Zw where
  m00 : Zw
  m01 : Zw
  m10 : Zw
  m11 : Zw
  h : ℕ
  deriving DecidableEq, Repr
def matId : Mat2Zw := ⟨⟨1,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨1,0,0,0⟩, 0⟩
def evalList : List HSTGate → Mat2Zw → Mat2Zw
  | [], m => m
  | .H :: gs, m =>
    evalList gs ⟨zwAdd m.m00 m.m10, zwAdd m.m01 m.m11, zwSub m.m00 m.m10, zwSub m.m01 m.m11,
      m.h + 1⟩
  | .S :: gs, m => evalList gs ⟨m.m00, m.m01, zwMulI m.m10, zwMulI m.m11, m.h⟩
  | .T :: gs, m => evalList gs ⟨m.m00, m.m01, zwMulW m.m10, zwMulW m.m11, m.h⟩
theorem evalList_append (u v : List HSTGate) (m m1 : Mat2Zw) (h1 : evalList u m = m1) :
    evalList (u ++ v) m = evalList v m1 := by
  induction u generalizing m with
  | nil => simpa using h1 ▸ rfl
  | cons g gs ih => cases g <;> exact ih _ h1
noncomputable def Mat2Zw.toMatrix (m : Mat2Zw) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((MeasureBranchHadamardSem.sqrtHalf : ℂ) ^ m.h) •
    !![m.m00.toComplex, m.m01.toComplex; m.m10.toComplex, m.m11.toComplex]
noncomputable def wordMatrix2 (w : List HSTGate) : Matrix (Fin 2) (Fin 2) ℂ :=
  (evalList w matId).toMatrix
noncomputable def alpha0 (w : List HSTGate) : ℂ :=
  (wordMatrix2 w * !![(0 : ℂ), 1; 1,0] * (wordMatrix2 w)ᴴ) 0 0
noncomputable def alpha1 (w : List HSTGate) : ℂ :=
  (wordMatrix2 w * !![(0 : ℂ), 1; 1,0] * (wordMatrix2 w)ᴴ) 1 0
theorem singleton_embedMatrix_mulVec_ket {n : ℕ} (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) : ((QRegister.singleton q).embedMatrix A).mulVec (ket β) = A 0
    (if β q = 0 then 0 else 1) • ket (Function.update β q 0) + A 1 (if β q = 0 then 0 else 1)
    • ket (Function.update β q 1) := OctahedralOrbit.singleton_embedMatrix_mulVec_ket q A β
theorem hstGate_eval_eq {n : ℕ} (g : HSTGate) (q : Wire n) : (hstGateCircuit g q).eval.1 =
    (QRegister.singleton q).embedMatrix (wordMatrix2 [g]) := by
  cases g
  · apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
    rw [hstGateCircuit, MeasureBranchHadamardSem.ket_H, singleton_embedMatrix_mulVec_ket]
    rcases MeasureBranchHadamardSem.bit_cases (β q) with hb | hb <;>
      simp [hb, one_ne_zero, MeasureBranchHadamardSem.bitSign, wordMatrix2, evalList, matId,
        Mat2Zw.toMatrix, zwAdd, zwSub, Zw.toComplex, smul_add, neg_smul, smul_neg]
  · rw [hstGateCircuit, Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_s_val]
    congr 1
    ext i j
    simp only [Matrix.diagonal_apply, wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwMulI,
      Zw.toComplex, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> dsimp <;> norm_num
    exact omega8_sq.symm
  · rw [hstGateCircuit, Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_t_val]
    congr 1
    ext i j
    simp only [Matrix.diagonal_apply, wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwMulW,
      omega8, Zw.toComplex, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> dsimp <;> norm_num
theorem evalList_mul_right (gs : List HSTGate) (m : Mat2Zw) :
    (evalList gs m).toMatrix = (evalList gs matId).toMatrix * m.toMatrix := by
  induction gs generalizing m with
  | nil =>
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, evalList, matId, Mat2Zw.toMatrix,
      Zw.toComplex, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> dsimp <;> norm_num
  | cons g gs ih =>
    have hstep (x : Mat2Zw) : evalList (g :: gs) x = evalList gs (evalList [g] x) := by
      cases g <;> rfl
    rw [hstep m, hstep matId, ih (evalList [g] m), ih (evalList [g] matId), Matrix.mul_assoc]
    congr 1
    ext i j
    rcases m with ⟨m00, m01, m10, m11, h⟩
    cases g
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, evalList, matId, Mat2Zw.toMatrix,
        zwAdd, zwSub, Zw.toComplex, Matrix.smul_apply, smul_eq_mul]
      fin_cases i <;> fin_cases j <;> dsimp <;> norm_num <;> ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, evalList, matId, Mat2Zw.toMatrix,
        zwMulI, Zw.toComplex, Matrix.smul_apply, smul_eq_mul]
      fin_cases i <;> fin_cases j <;> dsimp <;> norm_num
      · linear_combination -MeasureBranchHadamardSem.sqrtHalf ^ h * (↑m10.c2 + ↑m10.c3 * omega8) *
        omega8_pow_four
      · linear_combination -MeasureBranchHadamardSem.sqrtHalf ^ h * (↑m11.c2 + ↑m11.c3 * omega8) *
        omega8_pow_four
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, evalList, matId, Mat2Zw.toMatrix,
        zwMulW, Zw.toComplex, Matrix.smul_apply, smul_eq_mul]
      fin_cases i <;> fin_cases j <;> dsimp <;> norm_num
      · linear_combination -MeasureBranchHadamardSem.sqrtHalf ^ h * ↑m10.c3 * omega8_pow_four
      · linear_combination -MeasureBranchHadamardSem.sqrtHalf ^ h * ↑m11.c3 * omega8_pow_four
theorem hstWordCircuit_eval_eq_embedMatrix {n : ℕ} (w : List HSTGate) (q : Wire n) :
    (hstWordCircuit w q).eval.1 = (QRegister.singleton q).embedMatrix (wordMatrix2 w) := by
  induction w with
  | nil =>
    have hid : wordMatrix2 [] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, Zw.toComplex]
    rw [hstWordCircuit, Circuit.eval_identity, hid, QRegister.embedMatrix_one]; rfl
  | cons g gs ih =>
    rw [hstWordCircuit, Circuit.eval_seq, Submonoid.coe_mul, ih, hstGate_eval_eq,
      ← QRegister.embedMatrix_mul]
    congr 1; cases g <;> exact (evalList_mul_right gs _).symm
theorem wordMatrix2_unitary (w : List HSTGate) : wordMatrix2 w * (wordMatrix2 w)ᴴ = 1 := by
  have hreg : QRegister.singleton (0 : Wire 1) = QRegister.whole 1 :=
    QRegister.ext (Function.Embedding.ext fun _ => Subsingleton.elim _ _)
  have h : (hstWordCircuit w (0 : Wire 1)).eval.1 * ((hstWordCircuit w (0 : Wire 1)).eval.1)ᴴ = 1 :=
    ((hstWordCircuit w (0 : Wire 1)).eval).2.2
  rwa [hstWordCircuit_eval_eq_embedMatrix, ← QRegister.embedMatrix_conjTranspose,
    ← QRegister.embedMatrix_mul, hreg, QRegister.whole_embedMatrix] at h
theorem hstWordCircuit_eval_inv {n : ℕ} (w : List HSTGate) (t : Wire n) :
    ((hstWordCircuit w t).eval⁻¹).1 = (QRegister.singleton t).embedMatrix ((wordMatrix2 w)ᴴ) := by
  change star ((hstWordCircuit w t).eval.1) = _
  rw [Matrix.star_eq_conjTranspose, hstWordCircuit_eval_eq_embedMatrix,
    QRegister.embedMatrix_conjTranspose]
theorem ctrlProbGate_mulVec_ket_zero {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t)
    (β : BitAssignment n) (hc : β c = 0) :
    (ctrlProbGate w c t hct).eval.1.mulVec (ket β) = ket β := by
  have hcnot (b : ZMod 2) : (Circuit.CNOT c t hct).eval.1.mulVec (ket (Function.update β t b)) =
      ket (Function.update β t b) := by
    rw [MeasureBranchHadamardSem.ket_CNOT, Function.update_of_ne hct, hc, add_zero,
      Function.update_idem, Function.update_self]
  have hcancel : (hstWordCircuit w t).eval.1 * ((hstWordCircuit w t).eval⁻¹).1 = 1 :=
    congrArg Subtype.val (mul_inv_cancel (hstWordCircuit w t).eval)
  rw [ctrlProbGate, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec, Circuit.eval_inverse, hstWordCircuit_eval_inv,
    singleton_embedMatrix_mulVec_ket, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    hcnot, hcnot, ← singleton_embedMatrix_mulVec_ket t ((wordMatrix2 w)ᴴ) β,
    ← hstWordCircuit_eval_inv, Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
theorem ctrlProbGate_mulVec_ket_one_zero {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t)
    (β : BitAssignment n) (hc : β c = 1) (ht : β t = 0) :
    (ctrlProbGate w c t hct).eval.1.mulVec (ket β) =
      alpha0 w • ket β + alpha1 w • ket (Function.update β t 1) := by
  let M2 : Matrix (Fin 2) (Fin 2) ℂ := wordMatrix2 w * !![(0 : ℂ), 1; 1,0] * (wordMatrix2 w)ᴴ
  suffices hM : (ctrlProbGate w c t hct).eval.1.mulVec (ket β) =
      ((QRegister.singleton t).embedMatrix M2).mulVec (ket β) by
    rw [hM, singleton_embedMatrix_mulVec_ket, ite_pos' ht, upd_eq_self β t ht]; rfl
  have hcnot_eq_x (b : ZMod 2) :
      (Circuit.CNOT c t hct).eval.1.mulVec (ket (Function.update β t b)) =
        ((QRegister.singleton t).embedMatrix !![(0 : ℂ), 1; 1,0]).mulVec
          (ket (Function.update β t b)) := by
    rw [MeasureBranchHadamardSem.ket_CNOT, Function.update_of_ne hct, hc,
      singleton_embedMatrix_mulVec_ket, Function.update_self, Function.update_idem,
      Function.update_idem]
    rcases MeasureBranchHadamardSem.bit_cases b with rfl | rfl <;>
      simp [one_ne_zero, show (1 : ZMod 2) + 1 = 0 from rfl]
  have hmid : (Circuit.CNOT c t hct).eval.1.mulVec
      (((QRegister.singleton t).embedMatrix ((wordMatrix2 w)ᴴ)).mulVec (ket β)) =
      ((QRegister.singleton t).embedMatrix !![(0 : ℂ), 1; 1,0]).mulVec
        (((QRegister.singleton t).embedMatrix ((wordMatrix2 w)ᴴ)).mulVec (ket β)) := by
    rw [singleton_embedMatrix_mulVec_ket, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hcnot_eq_x, hcnot_eq_x]
  rw [ctrlProbGate, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec, Circuit.eval_inverse, hstWordCircuit_eval_inv,
    hmid, hstWordCircuit_eval_eq_embedMatrix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
theorem norm_sq_alpha0_add_alpha1 (w : List HSTGate) : ‖alpha0 w‖ ^ 2 + ‖alpha1 w‖ ^ 2 = 1 := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := wordMatrix2 w * !![(0 : ℂ), 1; 1,0] * (wordMatrix2 w)ᴴ
  have hX : (!![(0 : ℂ), 1; 1,0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![(0 : ℂ), 1; 1,0] = 1 := by
    ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    fin_cases i <;> fin_cases j <;> dsimp <;> norm_num
  have hU : (wordMatrix2 w)ᴴ * wordMatrix2 w = 1 := mul_eq_one_comm.mp (wordMatrix2_unitary w)
  have hM : Mᴴ * M = 1 := by
    calc Mᴴ * M
        = wordMatrix2 w * ((!![(0 : ℂ), 1; 1,0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
            ((wordMatrix2 w)ᴴ * wordMatrix2 w) * !![(0 : ℂ), 1; 1,0]) * (wordMatrix2 w)ᴴ := by
            simp only [M, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
              Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hX, Matrix.mul_one, wordMatrix2_unitary]
  have h00 := congrArg (fun A => A 0 0) hM
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.one_apply_eq] at h00
  have hnorm (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnorm (M 0 0), hnorm (M 1 0), ← Complex.ofReal_add] at h00
  exact Complex.ofReal_injective (by simpa [alpha0, alpha1] using h00)
theorem norm_sq_alpha1_of_eval (w : List HSTGate) (m : Mat2Zw) (heval : evalList w matId = m) :
    let a1 := zwAdd (zwMul m.m10 (zwConj m.m01)) (zwMul m.m11 (zwConj m.m00))
    let p := zwMul a1 (zwConj a1)
    ‖alpha1 w‖ ^ 2 = ((p.c0 : ℝ) + (p.c1 : ℝ) * √2) / ((2 : ℝ) ^ (2 * m.h)) := by
  let a1 := zwAdd (zwMul m.m10 (zwConj m.m01)) (zwMul m.m11 (zwConj m.m00))
  let p := zwMul a1 (zwConj a1)
  have hsh : ((MeasureBranchHadamardSem.sqrtHalf : ℂ) ^ m.h) *
      star ((MeasureBranchHadamardSem.sqrtHalf : ℂ) ^ m.h) = (1 / 2 : ℂ) ^ m.h := by
    rw [star_pow, MeasureBranchHadamardSem.star_sqrtHalf, ← mul_pow,
      MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf]
  have ha1 : alpha1 w = ((1 / 2 : ℂ) ^ m.h) * a1.toComplex := by
    simp only [alpha1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      wordMatrix2, heval, Mat2Zw.toMatrix, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, star_mul]
    rw [show a1.toComplex =
        m.m10.toComplex * star m.m01.toComplex + m.m11.toComplex * star m.m00.toComplex by
      simp only [a1, toComplex_zwAdd, toComplex_zwMul, toComplex_zwConj], ← hsh]
    ring
  change ‖alpha1 w‖ ^ 2 = ((p.c0 : ℝ) + (p.c1 : ℝ) * √2) / ((2 : ℝ) ^ (2 * m.h))
  rw [ha1, norm_mul, mul_pow, normSq_zw_eq a1, norm_pow, one_div (2 : ℂ), norm_inv,
    Complex.norm_ofNat, ← pow_mul, mul_comm m.h 2, inv_pow]
  dsimp only [p]; ring
@[simp] theorem alpha1_H_eq_zero : alpha1 [.H] = 0 := by
  have h := norm_sq_alpha1_of_eval [.H] _ rfl
  dsimp [evalList, matId, zwAdd, zwSub, zwMul, zwConj] at h; norm_num at h; exact h
@[simp] theorem alpha0_nil_eq_zero : alpha0 [] = 0 := by
  simp only [alpha0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, Zw.toComplex, Pi.smul_apply, smul_eq_mul]
  norm_num
theorem norm_sq_alpha1_TH : ‖alpha1 [.T, .H]‖ ^ 2 = 1 / 2 := by
  have h := norm_sq_alpha1_of_eval [.T, .H] _ rfl
  dsimp [evalList, matId, zwAdd, zwSub, zwMulW, zwMul, zwConj] at h; norm_num at h; exact h
theorem norm_sq_alpha0_TH : ‖alpha0 [.T, .H]‖ ^ 2 = 1 / 2 := by
  linarith [norm_sq_alpha0_add_alpha1 [.T, .H], norm_sq_alpha1_TH]
def leSqrt2Int (b rhs : ℤ) : Bool := if b == 0 then decide (0 ≤ rhs) else if b > 0 then decide
    (0 ≤ rhs) && decide (2 * b * b ≤ rhs * rhs) else if rhs ≥ 0 then true else decide
    (rhs * rhs ≤ 2 * b * b)
theorem leSqrt2Int_sound (b rhs : ℤ) (h : leSqrt2Int b rhs = true) : (b : ℝ) * √2 ≤ (rhs : ℝ) := by
  unfold leSqrt2Int at h
  by_cases hb : b = 0
  · subst hb; simp at h; simpa using (by exact_mod_cast h : (0 : ℝ) ≤ (rhs : ℝ))
  · rw [beq_false_of_ne hb] at h; dsimp at h
    by_cases hpos : b > 0
    · simp only [hpos, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
      have hsq : ((b : ℝ) * √2) ^ 2 ≤ (rhs : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [show 2 * (b : ℝ) * (b : ℝ) ≤ (rhs : ℝ) * (rhs : ℝ) by exact_mod_cast h.2]
      exact (abs_le_of_sq_le_sq' hsq (by exact_mod_cast h.1)).2
    · simp only [hpos, ↓reduceIte] at h
      by_cases hrpos : rhs ≥ 0
      · exact (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega : b ≤ 0))
          (Real.sqrt_nonneg 2)).trans (by exact_mod_cast hrpos)
      · simp only [hrpos, ↓reduceIte, decide_eq_true_eq] at h
        have hmb : (0 : ℝ) ≤ (-b : ℝ) * √2 :=
          mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ -b)) (Real.sqrt_nonneg 2)
        have hsq : (rhs : ℝ) ^ 2 ≤ ((-b : ℝ) * √2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          nlinarith [show (rhs : ℝ) * (rhs : ℝ) ≤ 2 * (b : ℝ) * (b : ℝ) by exact_mod_cast h]
        linarith [(abs_le_of_sq_le_sq' hsq hmb).1]
def cnotIf {n : ℕ} (c t : Wire n) : Circuit n :=
  if hct : c = t then Circuit.identity else Circuit.CNOT c t hct
def andComputeIf {n : ℕ} (c₁ c₂ anc : Wire n) : Circuit n := if h1 : c₁ = anc then
    Circuit.identity else if h2 : c₂ = anc then Circuit.identity else Circuit.andCompute c₁ c₂
    anc h1 h2
@[simp] theorem count_toff_cnotIf {n : ℕ} (c t : Wire n) :
    (cnotIf c t).count PrimitiveGate.TOFF = 0 := by unfold cnotIf; split_ifs <;> simp
@[simp] theorem count_t_cnotIf {n : ℕ} (c t : Wire n) :
    (cnotIf c t).count PrimitiveGate.T = 0 := by unfold cnotIf; split_ifs <;> simp
@[simp] theorem count_toff_andComputeIf {n : ℕ} (c₁ c₂ anc : Wire n) :
    (andComputeIf c₁ c₂ anc).count PrimitiveGate.TOFF = 0 := by
  unfold andComputeIf; split_ifs <;> simp [Circuit.count_andCompute_toff]
theorem ket_andCompute_of_zero {n : ℕ} (c₁ c₂ anc : Wire n) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (β : BitAssignment n) (hanc : β anc = 0) :
    (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval.1.mulVec (ket β) =
      ket (Function.update β anc (β c₁ * β c₂)) := by
  have ket_diag (q : Wire n) (z : ℂ) (γ : BitAssignment n) : ((QRegister.singleton q).embedMatrix
        (Matrix.diagonal (fun i : Fin 2 ↦ if i = 1 then z else 1))).mulVec (ket γ) =
        (if γ q = 0 then 1 else z) • ket γ := by
    rw [singleton_embedMatrix_mulVec_ket]
    rcases MeasureBranchHadamardSem.bit_cases (γ q) with hb | hb <;>
      simp [hb, one_ne_zero, upd_eq_self γ q hb]
  have ket_S_loc (q : Wire n) (γ : BitAssignment n) : (Circuit.S q).eval.1.mulVec (ket γ) =
      (if γ q = 0 then (1 : ℂ) else Complex.I) • ket γ := by
    rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_s_val]
    exact ket_diag q Complex.I γ
  have ket_T_loc (q : Wire n) (γ : BitAssignment n) : (Circuit.T q).eval.1.mulVec (ket γ) =
      (if γ q = 0 then (1 : ℂ) else omega8) • ket γ := by
    rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_t_val]
    exact ket_diag q omega8 γ
  have ket_Tinv_loc (q : Wire n) (γ : BitAssignment n) :
      (Circuit.T q).inverse.eval.1.mulVec (ket γ) =
        (if γ q = 0 then (1 : ℂ) else -omega8 ^ 3) • ket γ := by
    change (Circuit.T q ;;ᶜ (Circuit.S q ;;ᶜ (Circuit.Z q ;;ᶜ .identity))).eval.1.mulVec (ket γ) = _
    simp only [MeasureBranchHadamardSem.eval_seq_mulVec, Circuit.eval_identity, Submonoid.coe_one,
      Matrix.one_mulVec, ket_T_loc, ket_S_loc, MeasureBranchHadamardSem.ket_Z,
      Matrix.mulVec_smul, smul_smul]
    congr 1
    rcases MeasureBranchHadamardSem.bit_cases (γ q) with hb | hb
    · simp [hb, MeasureBranchHadamardSem.bitSign]
    · simp only [hb, MeasureBranchHadamardSem.bitSign, one_ne_zero, ↓reduceIte, ← omega8_sq]; ring
  let fT : ZMod 2 → ℂ := fun b => if b = 0 then 1 else omega8
  let fTi : ZMod 2 → ℂ := fun b => if b = 0 then 1 else -omega8 ^ 3
  have hTTi (b : ZMod 2) : fT b * fTi b = 1 := by
    rcases MeasureBranchHadamardSem.bit_cases b with rfl | rfl
    · dsimp [fT, fTi]; ring
    · dsimp [fT, fTi]; linear_combination -omega8_pow_four
  have hsh2 : (MeasureBranchHadamardSem.sqrtHalf : ℂ) ^ 2 = 1 / 2 := by
    rw [sq, MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf]
  have hjones (rest : Circuit n) (γ : BitAssignment n) :
      (Circuit.T anc ;;ᶜ Circuit.CNOT c₂ anc h₂a ;;ᶜ (Circuit.T anc).inverse ;;ᶜ
        Circuit.CNOT c₁ anc h₁a ;;ᶜ Circuit.T anc ;;ᶜ Circuit.CNOT c₂ anc h₂a ;;ᶜ
        (Circuit.T anc).inverse ;;ᶜ Circuit.CNOT c₁ anc h₁a ;;ᶜ rest).eval.1.mulVec (ket γ) =
        (fT (γ anc + γ c₂ + γ c₁) * fTi (γ anc + γ c₂) * fT (γ anc) * fTi (γ anc + γ c₁)) •
          rest.eval.1.mulVec (ket γ) := by
    have hadd1 (x y : ZMod 2) : x + y + y = x := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hadd2 (x y z : ZMod 2) : x + y + z + y = x + z := by
      rw [show x + y + z + y = x + z + (y + y) by ring, CharTwo.add_self_eq_zero, add_zero]
    simp only [MeasureBranchHadamardSem.eval_seq_mulVec, ket_T_loc, ket_Tinv_loc,
      MeasureBranchHadamardSem.ket_CNOT, Matrix.mulVec_smul, Function.update_self,
      Function.update_of_ne h₁a, Function.update_of_ne h₂a, Function.update_idem,
      hadd2, hadd1, Function.update_eq_self, smul_smul]
    congr 1
    dsimp [fT, fTi]
    ring
  have hph (x₁ x₂ a : ZMod 2) : fT (a + x₂ + x₁) * fTi (a + x₂) * fT a * fTi (a + x₁) = if x₁
      * x₂ = 0 then 1 else if a = 0 then -Complex.I else Complex.I := by
    rcases MeasureBranchHadamardSem.bit_cases x₁ with rfl | rfl
    · rw [zero_mul, ite_pos' rfl, add_zero, add_zero]
      linear_combination fT a * fTi a * hTTi (a + x₂) + hTTi a
    · rcases MeasureBranchHadamardSem.bit_cases x₂ with rfl | rfl
      · rw [mul_zero, ite_pos' rfl, add_zero]
        linear_combination fT a * fTi a * hTTi (a + 1) + hTTi a
      · rcases MeasureBranchHadamardSem.bit_cases a with rfl | rfl
        · simp only [one_mul, zero_add, show (1 : ZMod 2) + 1 = 0 from rfl, one_ne_zero, ↓reduceIte,
          fT, fTi]
          linear_combination omega8 ^ 2 * omega8_pow_four - omega8_sq
        · simp only [one_mul, show (1 : ZMod 2) + 1 = 0 from rfl, zero_add, one_ne_zero, ↓reduceIte,
          fT, fTi]
          linear_combination omega8_sq
  have hs0 : MeasureBranchHadamardSem.bitSign (β anc) = 1 := by
    simp [hanc, MeasureBranchHadamardSem.bitSign]
  rw [Circuit.andCompute, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.ket_H, hs0, one_smul, Matrix.mulVec_smul, Matrix.mulVec_add,
    hjones, hjones]
  simp only [Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a, hph,
    MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.ket_H,
    Function.update_idem, Matrix.mulVec_add, Matrix.mulVec_smul, ket_S_loc,
    MeasureBranchHadamardSem.bitSign, one_ne_zero, ↓reduceIte, one_smul]
  rcases MeasureBranchHadamardSem.bit_cases (β c₁ * β c₂) with hp | hp
  · rw [hp]; ext idx; simp only [ite_true, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket (Function.update β anc 0) idx) * (2 * hsh2)
  · rw [hp]; ext idx; simp only [one_ne_zero, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket (Function.update β anc 1) idx) * (-2 * Complex.I ^ 2 * hsh2 -
      Complex.I_sq)
theorem fin_sum_pow_succ {α : Type*} [AddCommMonoid α] (m : ℕ) (f : Fin (2 ^ (m + 1)) → α) :
    (∑ j : Fin (2 ^ (m + 1)), f j) = (∑ x : Fin (2 ^ m), f ⟨x.val, lt_pow_succ_of_lt x⟩) +
    (∑ x : Fin (2 ^ m), f ⟨2 ^ m + x.val, add_lt_pow_succ x⟩) := by
  let e : Fin (2 ^ m) ⊕ Fin (2 ^ m) ≃ Fin (2 ^ (m + 1)) :=
    { toFun := Sum.elim (fun x => ⟨x.val, lt_pow_succ_of_lt x⟩) (fun x =>
      ⟨2 ^ m + x.val, add_lt_pow_succ x⟩)
      invFun := fun j => if hj : j.val < 2 ^ m then Sum.inl ⟨j.val, hj⟩
                         else Sum.inr ⟨j.val - 2 ^ m, sub_pow_lt_of_not_lt j hj⟩
      left_inv := fun
        | .inl x => by simp [x.isLt]
        | .inr x => by simp [show ¬ (2 ^ m + x.val < 2 ^ m) by omega]
      right_inv := fun j => by by_cases hj : j.val < 2 ^ m <;> simp [hj, Fin.ext_iff]; omega }
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]; rfl
@[simp] theorem alpha1_nil_eq_one : alpha1 [] = 1 := by
  simp only [alpha1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, Zw.toComplex, Pi.smul_apply, smul_eq_mul]
  norm_num
noncomputable def sbmAmp : (m : ℕ) → ((d : Fin m) → Fin (2 ^ d.val) → List HSTGate) →
    Fin (2 ^ m) → ℂ
  | 0, _, _ => 1
  | m + 1, words, j =>
    let wordsL := fun (d : Fin m) (p : Fin (2 ^ d.val)) => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩
    let wordsR := fun (d : Fin m) (p : Fin (2 ^ d.val)) =>
      words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩
    if hlt : j.val < 2 ^ m then alpha0 (words 0 0) * sbmAmp m wordsL ⟨j.val, hlt⟩
    else alpha1 (words 0 0) * sbmAmp m wordsR ⟨j.val - 2 ^ m, sub_pow_lt_of_not_lt j hlt⟩
theorem norm_sq_sum_sbmAmp (m : ℕ) (words : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate) :
    ∑ j : Fin (2 ^ m), ‖sbmAmp m words j‖ ^ 2 = 1 := by
  induction m with
  | zero => simp [sbmAmp]
  | succ m ih =>
    have hL : (∑ x : Fin (2 ^ m), ‖sbmAmp (m + 1) words ⟨x.val, lt_pow_succ_of_lt x⟩‖ ^ 2) =
        ‖alpha0 (words 0 0)‖ ^ 2 := by
      rw [← mul_one (‖alpha0 (words 0 0)‖ ^ 2),
        ← ih (fun d p => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩), Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by simp [sbmAmp, x.isLt, mul_pow]
    have hR : (∑ x : Fin (2 ^ m), ‖sbmAmp (m + 1) words ⟨2 ^ m + x.val, add_lt_pow_succ x⟩‖ ^ 2) =
        ‖alpha1 (words 0 0)‖ ^ 2 := by
      rw [← mul_one (‖alpha1 (words 0 0)‖ ^ 2),
        ← ih (fun d p => words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩), Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp [sbmAmp, show ¬ (2 ^ m + x.val < 2 ^ m) by omega, mul_pow]
    rw [fin_sum_pow_succ, hL, hR]; exact norm_sq_alpha0_add_alpha1 (words 0 0)
def SbmTreeCertW : (m : ℕ) → ((d : Fin m) → Fin (2 ^ d.val) → List HSTGate) →
    (Fin (2 ^ m) → ℕ) → ℕ → ℕ → Prop
  | 0, _, W, S, _ => W 0 = S
  | m + 1, words, W, S, errNat =>
    let WL : Fin (2 ^ m) → ℕ := fun x => W ⟨x.val, lt_pow_succ_of_lt x⟩
    let WR : Fin (2 ^ m) → ℕ := fun x => W ⟨2 ^ m + x.val, add_lt_pow_succ x⟩
    let wordsL := fun (d : Fin m) (p : Fin (2 ^ d.val)) => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩
    let wordsR := fun (d : Fin m) (p : Fin (2 ^ d.val)) =>
      words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩
    ∃ wL wR : ℕ, wL + wR = S ∧
      (if wL = 0 then words 0 0 = [] ∧ (∀ x, WL x = 0) ∧ SbmTreeCertW m wordsR WR wR errNat
       else if wR = 0 then words 0 0 = [.H] ∧ (∀ x, WR x = 0) ∧ SbmTreeCertW m wordsL WL wL errNat
       else ∃ eSplit eL eR : ℕ, eL + eR + 2 * eSplit ≤ errNat ∧
         |(S : ℝ) * ‖alpha1 (words 0 0)‖ ^ 2 - (wR : ℝ)| ≤ (eSplit : ℝ) / (2 : ℝ) ^ 48 ∧
         SbmTreeCertW m wordsL WL wL eL ∧ SbmTreeCertW m wordsR WR wR eR)
instance instDecidableSbmTreeCertWZero (words : (d : Fin 0) → Fin (2 ^ d.val) → List HSTGate)
    (W : Fin (2 ^ 0) → ℕ) (S errNat : ℕ) : Decidable (SbmTreeCertW 0 words W S errNat) :=
  inferInstanceAs (Decidable (W 0 = S))
theorem scaled_half_sbm_bound {k : ℕ} (S wSub : ℕ) (a : ℝ) (p : Fin k → ℝ) (W : Fin k → ℕ)
    (B E0 : ℝ) (hp_nn : ∀ x, 0 ≤ p x) (hp_sum : ∑ x : Fin k, p x = 1)
    (ha_err : |(S : ℝ) * a - (wSub : ℝ)| ≤ E0)
    (hsub_err : ∑ x : Fin k, |(wSub : ℝ) * p x - (W x : ℝ)| ≤ B) :
    ∑ x : Fin k, |(S : ℝ) * (a * p x) - (W x : ℝ)| ≤ B + E0 := by
  calc ∑ x : Fin k, |(S : ℝ) * (a * p x) - (W x : ℝ)|
      ≤ ∑ x : Fin k, (|(wSub : ℝ) * p x - (W x : ℝ)| + |(S : ℝ) * a - (wSub : ℝ)| * p x) :=
          Finset.sum_le_sum fun x _ => by
            rw [show (S : ℝ) * (a * p x) - (W x : ℝ) =
              ((wSub : ℝ) * p x - (W x : ℝ)) + ((S : ℝ) * a - (wSub : ℝ)) * p x by ring]
            exact (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg (hp_nn x)])
    _ = (∑ x : Fin k, |(wSub : ℝ) * p x - (W x : ℝ)|) +
          |(S : ℝ) * a - (wSub : ℝ)| * (∑ x : Fin k, p x) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ B + E0 := by rw [hp_sum, mul_one]; exact add_le_add hsub_err ha_err
theorem SbmTreeCertW.sound {m : ℕ} {words : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate}
    {W : Fin (2 ^ m) → ℕ} {S errNat : ℕ} (hcert : SbmTreeCertW m words W S errNat) (hS : 0 < S) :
    (∑ j : Fin (2 ^ m), W j = S) ∧ (∀ j : Fin (2 ^ m), W j = 0 → sbmAmp m words j = 0) ∧
    (∑ j : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ)| ≤
      (errNat : ℝ) / (2 : ℝ) ^ 48) := by
  induction m generalizing S errNat with
  | zero =>
    have hW0 : W 0 = S := hcert
    have hj0 (j : Fin (2 ^ 0)) : j = 0 := Fin.ext (by have := j.isLt; omega)
    refine ⟨?_, fun j hj => by rw [hj0 j] at hj; omega, ?_⟩
    · calc ∑ j : Fin (2 ^ 0), W j = ∑ _ : Fin (2 ^ 0), S :=
            Finset.sum_congr rfl fun j _ => by rw [hj0 j, hW0]
        _ = S := by simp
    · rw [Finset.sum_eq_zero fun j _ => by simp [hj0 j, hW0, sbmAmp]]; positivity
  | succ m ih =>
    obtain ⟨wL, wR, hwsum, hbody⟩ := hcert
    let WL : Fin (2 ^ m) → ℕ := fun x => W ⟨x.val, lt_pow_succ_of_lt x⟩
    let WR : Fin (2 ^ m) → ℕ := fun x => W ⟨2 ^ m + x.val, add_lt_pow_succ x⟩
    let wordsL := fun (d : Fin m) (p : Fin (2 ^ d.val)) => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩
    let wordsR := fun (d : Fin m) (p : Fin (2 ^ d.val)) =>
      words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩
    have hWR_eq {j : Fin (2 ^ (m + 1))} (hlt : ¬ j.val < 2 ^ m) :
        WR ⟨j.val - 2 ^ m, sub_pow_lt_of_not_lt j hlt⟩ = W j :=
      congrArg W (Fin.ext (Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)))
    have hl_eq : (∑ x : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp (m + 1) words ⟨x.val,
      lt_pow_succ_of_lt x⟩‖ ^ 2 -
          (W ⟨x.val, lt_pow_succ_of_lt x⟩ : ℝ)|) =
        ∑ x : Fin (2 ^ m),
          |(S : ℝ) * (‖alpha0 (words 0 0)‖ ^ 2 * ‖sbmAmp m wordsL x‖ ^ 2) - (WL x : ℝ)| :=
      Finset.sum_congr rfl fun x _ => by simp [WL, wordsL, sbmAmp, x.isLt, mul_pow]
    have hr_eq : (∑ x : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp (m + 1) words ⟨2 ^ m + x.val,
      add_lt_pow_succ x⟩‖ ^ 2 -
          (W ⟨2 ^ m + x.val, add_lt_pow_succ x⟩ : ℝ)|) =
        ∑ x : Fin (2 ^ m),
          |(S : ℝ) * (‖alpha1 (words 0 0)‖ ^ 2 * ‖sbmAmp m wordsR x‖ ^ 2) - (WR x : ℝ)| :=
      Finset.sum_congr rfl fun x _ => by
        simp [WR, wordsR, sbmAmp, show ¬ (2 ^ m + x.val < 2 ^ m) by omega, mul_pow]
    by_cases hwL : wL = 0
    · simp only [hwL, ↓reduceIte] at hbody
      rcases hbody with ⟨hw0, hWL0, hcertR⟩
      have hwR_eq : wR = S := by omega
      rcases ih hcertR (by omega) with ⟨hsumR, hzeroR, herrR⟩
      have hl0 : (∑ x : Fin (2 ^ m),
          |(S : ℝ) * (‖alpha0 (words 0 0)‖ ^ 2 * ‖sbmAmp m wordsL x‖ ^ 2) - (WL x : ℝ)|) = 0 :=
        Finset.sum_eq_zero fun x _ => by simp [WL, hw0, hWL0 x]
      refine ⟨by rw [fin_sum_pow_succ, Finset.sum_eq_zero fun x _ =>
        hWL0 x, zero_add, hsumR, hwR_eq],
        fun j hj =>
          ?_, by rw [fin_sum_pow_succ, hl_eq, hr_eq, hl0, zero_add]; simpa [hw0,
          hwR_eq] using herrR⟩
      by_cases hlt : j.val < 2 ^ m
      · simp [sbmAmp, hlt, hw0]
      · simp [sbmAmp, hlt, hzeroR _ ((hWR_eq hlt).trans hj)]
    · simp only [hwL, ↓reduceIte] at hbody
      by_cases hwR : wR = 0
      · simp only [hwR, ↓reduceIte] at hbody
        rcases hbody with ⟨hw0, hWR0, hcertL⟩
        have hwL_eq : wL = S := by omega
        have ha0 : ‖alpha0 [.H]‖ ^ 2 = 1 := by simpa using norm_sq_alpha0_add_alpha1 [.H]
        rcases ih hcertL (by omega) with ⟨hsumL, hzeroL, herrL⟩
        have hr0 : (∑ x : Fin (2 ^ m),
            |(S : ℝ) * (‖alpha1 (words 0 0)‖ ^ 2 * ‖sbmAmp m wordsR x‖ ^ 2) - (WR x : ℝ)|) = 0 :=
          Finset.sum_eq_zero fun x _ => by simp [WR, hw0, hWR0 x]
        refine ⟨by rw [fin_sum_pow_succ, Finset.sum_eq_zero fun x _ =>
          hWR0 x, add_zero, hsumL, hwL_eq],
          fun j hj =>
            ?_, by rw [fin_sum_pow_succ, hl_eq, hr_eq, hr0, add_zero]; simpa [hw0, ha0,
            hwL_eq] using herrL⟩
        by_cases hlt : j.val < 2 ^ m
        · simp [sbmAmp, hlt, hzeroL ⟨j.val, hlt⟩ hj]
        · simp [sbmAmp, hlt, hw0]
      · simp only [hwR, ↓reduceIte] at hbody
        rcases hbody with ⟨eSplit, eL, eR, heSum, hsplit1, hcertL, hcertR⟩
        rcases ih hcertL (by omega) with ⟨hsumL, hzeroL, herrL⟩
        rcases ih hcertR (by omega) with ⟨hsumR, hzeroR, herrR⟩
        refine ⟨by rw [fin_sum_pow_succ, hsumL, hsumR, hwsum], fun j hj => ?_, ?_⟩
        · by_cases hlt : j.val < 2 ^ m
          · simp [sbmAmp, hlt, hzeroL ⟨j.val, hlt⟩ hj]
          · simp [sbmAmp, hlt, hzeroR _ ((hWR_eq hlt).trans hj)]
        · have hsplit0 : |(S : ℝ) * ‖alpha0 (words 0 0)‖ ^ 2 - (wL : ℝ)| ≤
              (eSplit : ℝ) / (2 : ℝ) ^ 48 := by
            have hmul : (S : ℝ) * (‖alpha0 (words 0 0)‖ ^ 2 + ‖alpha1 (words 0 0)‖ ^ 2) =
                (S : ℝ) := by rw [norm_sq_alpha0_add_alpha1, mul_one]
            have hwsumR : (wL : ℝ) + (wR : ℝ) = (S : ℝ) := by exact_mod_cast hwsum
            rw [show (S : ℝ) * ‖alpha0 (words 0 0)‖ ^ 2 - (wL : ℝ) =
              -((S : ℝ) * ‖alpha1 (words 0 0)‖ ^ 2 - (wR : ℝ)) by linarith, abs_neg]
            exact hsplit1
          rw [fin_sum_pow_succ, hl_eq, hr_eq]
          refine (add_le_add
            (scaled_half_sbm_bound S wL _ (fun x => ‖sbmAmp m wordsL x‖ ^ 2) WL _ _
              (fun _ => by positivity) (norm_sq_sum_sbmAmp m wordsL) hsplit0 herrL)
            (scaled_half_sbm_bound S wR _ (fun x => ‖sbmAmp m wordsR x‖ ^ 2) WR _ _
              (fun _ => by positivity) (norm_sq_sum_sbmAmp m wordsR) hsplit1 herrR)).trans ?_
          rw [show ((eL : ℝ) / (2 : ℝ) ^ 48 + (eSplit : ℝ) / (2 : ℝ) ^ 48) +
              ((eR : ℝ) / (2 : ℝ) ^ 48 + (eSplit : ℝ) / (2 : ℝ) ^ 48) =
              ((eL : ℝ) + (eR : ℝ) + 2 * (eSplit : ℝ)) / (2 : ℝ) ^ 48 by ring]
          exact div_le_div_of_nonneg_right (by exact_mod_cast heSum) (by positivity)
theorem SbmTreeCertW.l1_err_le {m : ℕ} {words : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate}
    {W : Fin (2 ^ m) → ℕ} {S errNat : ℕ} (hcert : SbmTreeCertW m words W S errNat) (hS : 0 < S) :
    ∑ j : Fin (2 ^ m), |‖sbmAmp m words j‖ ^ 2 - (W j : ℝ) / (S : ℝ)| ≤
      (errNat : ℝ) / ((S : ℝ) * (2 : ℝ) ^ 48) := by
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hrew : (∑ j : Fin (2 ^ m), |‖sbmAmp m words j‖ ^ 2 - (W j : ℝ) / (S : ℝ)|) =
      (∑ j : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ)|) / (S : ℝ) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ) / (S : ℝ) =
      ((S : ℝ) * ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ)) / (S : ℝ) by field_simp [hSR.ne'],
      abs_div, abs_of_pos hSR]
  rw [hrew, mul_comm (S : ℝ)]
  exact (div_le_div_of_nonneg_right ((hcert.sound hS).2.2) hSR.le).trans_eq (div_div _ _ _)
set_option exponentiation.threshold 512
@[simp] theorem alpha0_singleton_H : alpha0 [.H] = 1 := by
  simp only [alpha0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, Zw.toComplex,
    Pi.smul_apply, smul_eq_mul]
  norm_num; rw [← Complex.star_def, MeasureBranchHadamardSem.star_sqrtHalf]
  linear_combination 2 * MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf
set_option maxRecDepth 4096
set_option maxRecDepth 512
set_option exponentiation.threshold 256
end ZeroAncillaUSP
end
end ModZeroAncillaUSP

section ModDynProgS2
@[expose] public section
open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
section SharedScope
variable {Var : Type} {n k m a : ℕ}
noncomputable def cleanSetProj (S : Finset (Wire n)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal fun g ↦ if ∀ w ∈ S, basisBits n g w = 0 then 1 else 0
@[simp] theorem cleanSetProj_conjTranspose (S : Finset (Wire n)) :
    (cleanSetProj S)ᴴ = cleanSetProj S := by
  rw [cleanSetProj, Matrix.diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  change star (if ∀ w ∈ S, basisBits n g w = 0 then (1 : ℂ) else 0) = _
  split_ifs <;> simp
@[simp] theorem cleanSetProj_mul_self (S : Finset (Wire n)) :
    cleanSetProj S * cleanSetProj S = cleanSetProj S := by
  rw [cleanSetProj, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun g ↦ by split_ifs <;> simp)
theorem cleanSetProj_union (S₁ S₂ : Finset (Wire n)) :
    cleanSetProj (S₁ ∪ S₂) = cleanSetProj S₁ * cleanSetProj S₂ := by
  rw [cleanSetProj, cleanSetProj, cleanSetProj, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  by_cases h₁ : ∀ w ∈ S₁, basisBits n g w = 0
  · by_cases h₂ : ∀ w ∈ S₂, basisBits n g w = 0
    · rw [ite_eq_left (fun w hw ↦
      (Finset.mem_union.mp hw).elim (h₁ w) (h₂ w)), ite_eq_left h₁, ite_eq_left h₂, mul_one]
    · rw [ite_eq_right (fun h ↦ h₂ fun w hw ↦
      h w (Finset.mem_union_right _ hw)), ite_eq_right h₂, mul_zero]
  · rw [ite_eq_right (fun h ↦ h₁ fun w hw ↦
    h w (Finset.mem_union_left _ hw)), ite_eq_right h₁, zero_mul]
theorem cleanSetProj_singleton (q : Wire n) :
    cleanSetProj ({q} : Finset (Wire n)) = (QRegister.singleton q).basisOutcomeProjector 0 := by
  rw [cleanSetProj, QRegister.basisOutcomeProjector_eq_diagonal]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  have hiff : (∀ w ∈ ({q} : Finset (Wire n)), basisBits n g w = 0) ↔
      (QRegister.singleton q).extractIndex g = 0 := by
    rw [(QRegExt.extractIndex_eq_zero_iff (QRegister.singleton q)) g]
    simp only [Finset.mem_singleton, forall_eq, Fin.forall_fin_one, QRegister.singleton_apply]
  simp only [hiff]
theorem basisOutcomeProjector_zero_mul_cleanSetProj (rWork : QRegister m n)
    (S : Finset (Wire n)) (hsub : ∀ w ∈ S, ∃ j : Fin m, rWork j = w) :
    rWork.basisOutcomeProjector 0 * cleanSetProj S = rWork.basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, cleanSetProj, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
  by_cases h : rWork.extractIndex g = 0
  · have hS : ∀ w ∈ S, basisBits n g w = 0 := fun w hw ↦ by
      obtain ⟨j, rfl⟩ := hsub w hw; exact ((QRegExt.extractIndex_eq_zero_iff rWork) g).mp h j
    rw [ite_eq_left h, ite_eq_left hS, mul_one]
  · rw [ite_eq_right h, zero_mul]
noncomputable def cleanSetRestrict [Fintype Var]
    (S : Finset (Wire n)) (M : CQAssertionCompat Var (2 ^ n)) : CQAssertionCompat Var (2 ^ n) :=
  fun σ ↦ ⟨(M σ).1.conj (cleanSetProj S), ⟨(M σ).1.conj_nonneg (cleanSetProj S) (M σ).2.1, by
    refine (HermitianMat.conj_mono (M σ).2.2).trans (HermitianMat.le_iff.mpr ?_)
    have hmat : (1 - HermitianMat.conj (cleanSetProj S) 1).mat =
        Matrix.diagonal fun g ↦ 1 - if ∀ w ∈ S, basisBits n g w = 0 then 1 else 0 := by
      simp only [HermitianMat.mat_sub, HermitianMat.mat_one, HermitianMat.conj_apply_mat,
        Matrix.mul_one, cleanSetProj_conjTranspose, cleanSetProj_mul_self]
      rw [cleanSetProj, ← Matrix.diagonal_one, ← Matrix.diagonal_sub]
    rw [hmat]
    exact Matrix.PosSemidef.diagonal fun g ↦ by split_ifs <;> norm_num⟩⟩
@[simp] theorem cleanSetRestrict_coe [Fintype Var]
    (S : Finset (Wire n)) (M : CQAssertionCompat Var (2 ^ n)) (σ : Store Var) :
    (cleanSetRestrict S M σ).1 = (M σ).1.conj (cleanSetProj S) := rfl
theorem cleanSetRestrict_union [Fintype Var]
    (S₁ S₂ : Finset (Wire n)) (M : CQAssertionCompat Var (2 ^ n)) :
    cleanSetRestrict (S₁ ∪ S₂) M = cleanSetRestrict S₂ (cleanSetRestrict S₁ M) :=
  funext fun _ ↦ Subtype.ext (by
    have hc : cleanSetProj S₁ * cleanSetProj S₂ = cleanSetProj S₂ * cleanSetProj S₁ := by
      simp only [cleanSetProj, Matrix.diagonal_mul_diagonal, mul_comm]
    simp only [cleanSetRestrict_coe, conj_conj, cleanSetProj_union, hc])
theorem cleanSetRestrict_singleton [Fintype Var] (q : Wire n) (M : CQAssertionCompat Var (2 ^ n)) :
    cleanSetRestrict ({q} : Finset (Wire n)) M = CQAssertion.restrictToZeroAncilla M
    (QRegister.singleton q) :=
  funext fun _ ↦ Subtype.ext (by
    simp only [cleanSetRestrict_coe, CQAssertion.restrictToZeroAncilla_coe, cleanSetProj_singleton])
def PreservesCleanSet (S : Finset (Wire n)) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Prop :=
  cleanSetProj S * A * cleanSetProj S = A * cleanSetProj S
theorem PreservesCleanSet.one (S : Finset (Wire n)) :
    PreservesCleanSet S (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  simp [PreservesCleanSet, cleanSetProj_mul_self]
theorem PreservesCleanSet.mul {S : Finset (Wire n)}
    {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hA : PreservesCleanSet S A)
    (hB : PreservesCleanSet S B) : PreservesCleanSet S (A * B) := by
  unfold PreservesCleanSet at *
  rw [← Matrix.mul_assoc (cleanSetProj S) A B, Matrix.mul_assoc (cleanSetProj S * A) B,
    ← hB, ← Matrix.mul_assoc (cleanSetProj S * A) (cleanSetProj S * B),
    ← Matrix.mul_assoc (cleanSetProj S * A) (cleanSetProj S) B, hA,
    Matrix.mul_assoc A (cleanSetProj S) B, Matrix.mul_assoc A (cleanSetProj S * B),
    hB, ← Matrix.mul_assoc]
theorem PreservesCleanSet.pow {S : Finset (Wire n)} {U : Unitary (2 ^ n)}
    (hU : PreservesCleanSet S U.1) : ∀ R : ℕ, PreservesCleanSet S ((U ^ R).1)
  | 0 => PreservesCleanSet.one S
  | R + 1 => by rw [pow_succ, Submonoid.coe_mul]; exact (PreservesCleanSet.pow hU R).mul hU
theorem cleanSetRestrict_wp_qAssign_absorb [Fintype Var] {S : Finset (Wire n)}
    {U : Unitary (2 ^ n)} (hU : PreservesCleanSet S U.1) (Ψ : CQAssertionCompat Var (2 ^ n)) :
    cleanSetRestrict S (wpQAssignCompat U (cleanSetRestrict S Ψ)) = cleanSetRestrict S
    (wpQAssignCompat U Ψ) :=
  funext fun _ ↦ Subtype.ext (by
    have hadj : cleanSetProj S * U.1ᴴ * cleanSetProj S = cleanSetProj S * U.1ᴴ := by
      simpa only [conjTranspose_mul, cleanSetProj_conjTranspose, Matrix.mul_assoc] using
        congrArg conjTranspose hU
    simp only [cleanSetRestrict_coe, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    rw [← Matrix.mul_assoc, hadj])
theorem toffoli_comm_cleanSetProj_of_not_mem (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (S : Finset (Wire n)) (hanc : anc ∉ S) :
    (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * cleanSetProj S = cleanSetProj S *
    (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 := by
  have hket (β : BitAssignment n) : (cleanSetProj S).mulVec (MeasureBranchHadamardSem.ket β) =
      if ∀ w ∈ S, β w = 0 then MeasureBranchHadamardSem.ket β else 0 := by
    rw [cleanSetProj, MeasureBranchHadamardSem.ket, basisState,
      Matrix.diagonal_mulVec_single, mul_one, ZeroAncillaUSP.basisBits_symm_eq]
    split_ifs <;> simp
  apply MeasureBranchHadamardSem.matrix_ext_ket; intro β
  have hiff : (∀ w ∈ S, Function.update β anc (β anc + β c₁ * β c₂) w = 0) ↔ ∀ w ∈ S, β w = 0 :=
    forall₂_congr fun w hw ↦ by rw [Function.update_of_ne (fun h ↦ hanc (by rwa [← h]))]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hket, MeasureBranchHadamardSem.ket_TOFF, hket]
  simp only [hiff]
  split_ifs with hS
  · exact MeasureBranchHadamardSem.ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
  · exact Matrix.mulVec_zero _
theorem eval_comm_cleanSetProj_of_disjoint
    (c : Circuit n) (S : Finset (Wire n)) (hdisj : Disjoint c.support S) :
    c.eval.1 * cleanSetProj S = cleanSetProj S * c.eval.1 := by
  induction c with
  | identity => simp
  | gate g r =>
      simp only [Circuit.support_gate] at hdisj
      ext i j; rw [cleanSetProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
      change (r.embedMatrix g.eval.1) i j * _ = _ * (r.embedMatrix g.eval.1) i j
      by_cases hEnv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2
      · have hOut := (r.basisSplit_environment_eq_iff i j).mp hEnv
        have hiff : (∀ w ∈ S, basisBits n i w = 0) ↔ (∀ w ∈ S, basisBits n j w = 0) :=
          forall₂_congr fun w hw ↦ by
            rw [hOut w fun ⟨idx, hidx⟩ ↦
              Finset.disjoint_left.mp hdisj ((QRegister.mem_image r w).mpr ⟨idx, hidx⟩) hw]
        simp only [hiff]; exact mul_comm _ _
      · simp [QRegister.embedMatrix_apply, hEnv]
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [Circuit.support_seq, Finset.disjoint_union_left] at hdisj
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, ih₁ hdisj.1, ← Matrix.mul_assoc, ih₂ hdisj.2, Matrix.mul_assoc]
theorem PreservesCleanSet.of_comm {S : Finset (Wire n)}
    {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hcomm : A * cleanSetProj S = cleanSetProj S * A) :
    PreservesCleanSet S A := by
  rw [PreservesCleanSet, ← hcomm, Matrix.mul_assoc, cleanSetProj_mul_self]
theorem PreservesCleanSet.union {S₁ S₂ : Finset (Wire n)}
    {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (h₁ : PreservesCleanSet S₁ A)
    (h₂ : PreservesCleanSet S₂ A) : PreservesCleanSet (S₁ ∪ S₂) A := by
  unfold PreservesCleanSet at *
  have hc12 : cleanSetProj S₁ * cleanSetProj S₂ = cleanSetProj S₂ * cleanSetProj S₁ := by
    simp only [cleanSetProj, Matrix.diagonal_mul_diagonal, mul_comm]
  have hswap := congrArg (A * ·) hc12.symm
  calc cleanSetProj (S₁ ∪ S₂) * A * cleanSetProj (S₁ ∪ S₂)
      = cleanSetProj S₁ * (cleanSetProj S₂ * A * cleanSetProj S₂) * cleanSetProj S₁ := by
          rw [cleanSetProj_union]; simp only [Matrix.mul_assoc, hc12]
          simp only [← Matrix.mul_assoc, hc12]
    _ = (cleanSetProj S₁ * A * cleanSetProj S₁) * cleanSetProj S₂ := by
          rw [h₂]; simp only [Matrix.mul_assoc, hswap]
    _ = A * cleanSetProj (S₁ ∪ S₂) := by rw [h₁, cleanSetProj_union, Matrix.mul_assoc]
def substGate (v : Var) (qToff : Wire n) :
    {a : ℕ} → PrimitiveGate a → QRegister a n → DynamicCircuit Var n
  | 3, .toffoli, r => have h₀₁ : r 0 ≠ r 1 := fun h ↦ by cases r.wires.injective h
      if h : r 0 ≠ qToff ∧ r 1 ≠ qToff ∧ r 2 ≠ qToff then
        DynamicCircuit.jonesToffoli v (r 0) (r 1) (r 2) qToff h₀₁ h.1 h.2.1 h.2.2
      else .identity
  | 1, .x, r => .circuit (.gate .x r)
  | 1, .y, r => .circuit (.gate .y r)
  | 1, .z, r => .circuit (.gate .z r)
  | 1, .h, r => .circuit (.gate .h r)
  | 1, .s, r => .circuit (.gate .s r)
  | 1, .t, r => .circuit (.gate .t r)
  | 2, .cnot, r => .circuit (.gate .cnot r)
  | 2, .swap, r => .circuit (.gate .swap r)
def substCircuit (v : Var) (qToff : Wire n) : Circuit n → DynamicCircuit Var n
  | .identity => .identity
  | .gate g r => substGate v qToff g r
  | .seq c₁ c₂ => .seq (substCircuit v qToff c₁) (substCircuit v qToff c₂)
theorem substCircuit_eq_toffoliSubst (v : Var) (qToff : Wire n) (c : Circuit n) :
    substCircuit v qToff c = ToffoliSubst.substCircuit v qToff c := by
  induction c with
  | identity => rfl
  | gate g r => cases g <;>
    simp [substCircuit, substGate, ToffoliSubst.substCircuit, ToffoliSubst.substGate]
  | seq c₁ c₂ ih₁ ih₂ => simp [substCircuit, ToffoliSubst.substCircuit, ih₁, ih₂]
@[simp] theorem count_substCircuit_toff (v : Var) (qToff : Wire n) (c : Circuit n) :
    (substCircuit v qToff c).count PrimitiveGate.TOFF = 0 := by
  rw [substCircuit_eq_toffoliSubst]; exact ToffoliSubst.count_substCircuit_toff v qToff c
theorem count_substCircuit_t_le (v : Var) (qToff : Wire n) (c : Circuit n) :
    (substCircuit v qToff c).count PrimitiveGate.T ≤ c.count .T + 4 * c.count .TOFF := by
  induction c with
  | identity => simp [substCircuit]
  | gate g r =>
      cases g with
      | toffoli => simp only [substCircuit, substGate]; split_ifs <;> simp
      | x | y | z | h | s | t | cnot | swap => simp [substCircuit, substGate]
  | seq c₁ c₂ ih₁ ih₂ => simp only [substCircuit, DynamicCircuit.count, Circuit.count_seq]; omega
def StoreIndep [Fintype Var] {d : ℕ} (Θ : CQAssertionCompat Var d) : Prop :=
  ∀ σ₁ σ₂ : Store Var, Θ σ₁ = Θ σ₂
theorem StoreIndep.const [Fintype Var] {d : ℕ} (M : Observable (Fin d)) : StoreIndep
    (fun _ : Store Var ↦ M) := fun _ _ ↦ rfl
def repCircuit : ℕ → Circuit n → Circuit n
  | 0, _ => .identity
  | R + 1, c => repCircuit R c ;;ᶜ c
def repDynamic : ℕ → DynamicCircuit Var n → DynamicCircuit Var n
  | 0, _ => .identity
  | R + 1, d => .seq (repDynamic R d) d
inductive DynProgS2 (Var : Type) (n : ℕ) where
  | circ (c : Circuit n)
  | seq (p₁ p₂ : DynProgS2 Var n)
  | rep (R : ℕ) (body : DynProgS2 Var n)
  | tempAnd (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : DynProgS2 Var n)
  | custom (cSpec : Circuit n) (dImpl : DynamicCircuit Var n) (tMax : ℕ)
namespace DynProgS2
def toCircuit : DynProgS2 Var n → Circuit n
  | .circ c => c
  | .seq p₁ p₂ => p₁.toCircuit ;;ᶜ p₂.toCircuit
  | .rep R body => repCircuit R body.toCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toCircuit ;;ᶜ
        Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
  | .custom cSpec _ _ => cSpec
def compile (v : Var) (qToff : Wire n) : DynProgS2 Var n → DynamicCircuit Var n
  | .circ c => substCircuit v qToff c
  | .seq p₁ p₂ => .seq (p₁.compile v qToff) (p₂.compile v qToff)
  | .rep R body => repDynamic R (body.compile v qToff)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (.seq (body.compile v qToff) (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))
  | .custom _ dImpl _ => dImpl
section Soundness
variable [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
def SemValid (v : Var) (qToff : Wire n) : Finset (Wire n) → DynProgS2 Var n → Prop
  | S, .circ c => qToff ∈ S ∧ Disjoint c.support S
  | S, .seq p₁ p₂ => SemValid v qToff S p₁ ∧ SemValid v qToff S p₂
  | S, .rep _ body => SemValid v qToff S body
  | S, .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      anc ∈ S ∧ SemValid v qToff (S.erase anc) body ∧
      PreservesCleanSet ({anc} : Finset (Wire n))
        (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toCircuit ;;ᶜ
          Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1
  | S, .custom cSpec dImpl _ =>
      PreservesCleanSet S cSpec.eval.1 ∧
      (∀ Θ : CQAssertionCompat Var (2 ^ n), StoreIndep Θ → StoreIndep (wp dImpl.compile Θ)) ∧
      (∀ Θ : CQAssertionCompat Var (2 ^ n), StoreIndep Θ →
        cleanSetRestrict S (wp dImpl.compile Θ) = cleanSetRestrict S (wpQAssignCompat cSpec.eval Θ))
theorem SemValid.preservesCleanSet {v : Var} {qToff : Wire n} {S : Finset (Wire n)}
    {p : DynProgS2 Var n} (hv : p.SemValid v qToff S) :
    PreservesCleanSet S p.toCircuit.eval.1 := by
  induction p generalizing S with
  | circ c => exact PreservesCleanSet.of_comm (eval_comm_cleanSetProj_of_disjoint c S hv.2)
  | seq p₁ p₂ ih₁ ih₂ =>
      rw [toCircuit, Circuit.eval_seq, Submonoid.coe_mul]; exact (ih₂ hv.2).mul (ih₁ hv.1)
  | rep R body ih =>
      have hbody := ih hv
      clear hv
      rw [toCircuit]
      induction R with
      | zero => exact PreservesCleanSet.one S
      | succ R ihr => rw [repCircuit, Circuit.eval_seq, Submonoid.coe_mul]; exact hbody.mul ihr
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      rcases hv with ⟨hanc, hbody, hanc_pres⟩
      have hT_rest := PreservesCleanSet.of_comm (toffoli_comm_cleanSetProj_of_not_mem
        c₁ c₂ anc h₁₂ h₁a h₂a (S.erase anc) (Finset.notMem_erase anc S))
      rw [toCircuit, ← Finset.insert_erase hanc]; refine hanc_pres.union ?_
      simp only [Circuit.eval_seq, Submonoid.coe_mul]; exact (hT_rest.mul (ih hbody)).mul hT_rest
  | custom _ _ _ => exact hv.1
theorem wp_compile_storeIndep {v : Var} {qToff : Wire n} {S : Finset (Wire n)}
    {p : DynProgS2 Var n} (hv : p.SemValid v qToff S) {Θ : CQAssertionCompat Var (2 ^ n)}
    (hΘ : StoreIndep Θ) : StoreIndep (wp (p.compile v qToff).compile Θ) := by
  induction p generalizing S Θ with
  | circ c =>
      rw [compile, substCircuit_eq_toffoliSubst]
      exact MomSlot0CircuitHalf.RevProg.wp_substCircuit_storeConst v qToff c Θ hΘ
  | seq p₁ p₂ ih₁ ih₂ =>
      dsimp only [compile]
      exact OctahedralOrbit.storeConst_wp_seq (fun {_} ↦ ih₁ hv.1) (fun {_} ↦ ih₂ hv.2) hΘ
  | rep R body ih =>
      have hbody : body.SemValid v qToff S := hv; clear hv; dsimp only [compile]
      induction R generalizing Θ with
      | zero => simpa [repDynamic] using hΘ
      | succ R ihr =>
          dsimp only [repDynamic]
          exact OctahedralOrbit.storeConst_wp_seq (fun {_} ↦ ihr) (fun {_} ↦ ih hbody) hΘ
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      dsimp only [compile]
      exact OctahedralOrbit.storeConst_wp_seq
        (OctahedralOrbit.storeConst_wp_andCompute c₁ c₂ anc h₁a h₂a)
        (OctahedralOrbit.storeConst_wp_seq (fun {_} ↦ ih hv.2.1)
          (OctahedralOrbit.storeConst_wp_andUncompute v c₁ c₂ anc h₁₂)) hΘ
  | custom _ _ _ => exact hv.2.1 Θ hΘ
theorem cleanSetRestrict_wp_compile_eq {v : Var} {qToff : Wire n} {S : Finset (Wire n)}
    {p : DynProgS2 Var n} (hv : p.SemValid v qToff S) (Θ : CQAssertionCompat Var (2 ^ n))
    (hΘ : StoreIndep Θ) : cleanSetRestrict S (wp (p.compile v qToff).compile Θ) =
    cleanSetRestrict S (wpQAssignCompat p.toCircuit.eval Θ) := by
  induction p generalizing S Θ with
  | circ c =>
      have hunion : ({qToff} : Finset (Wire n)) ∪ S = S := Finset.insert_eq_of_mem hv.1
      have hsingle : cleanSetRestrict ({qToff} : Finset (Wire n))
          (wp (substCircuit v qToff c).compile Θ) =
          cleanSetRestrict ({qToff} : Finset (Wire n)) (wpQAssignCompat c.eval Θ) := by
        rw [cleanSetRestrict_singleton, cleanSetRestrict_singleton, substCircuit_eq_toffoliSubst]
        exact ToffoliSubst.restrictToZeroAncilla_wp_substCircuit_of_not_mem_support
          v qToff c (fun hm ↦ Finset.disjoint_left.mp hv.2 hm hv.1) Θ (fun σ _ ↦ hΘ _ σ)
      rw [compile, toCircuit, ← hunion, cleanSetRestrict_union, cleanSetRestrict_union, hsingle]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [compile, toCircuit, DynamicCircuit.compile_seq, wp_qSeq, Circuit.eval_seq]
      have h₁_pres := hv.1.preservesCleanSet
      rw [ih₁ hv.1 _ (wp_compile_storeIndep hv.2 hΘ),
        ← cleanSetRestrict_wp_qAssign_absorb h₁_pres, ih₂ hv.2 Θ hΘ,
        cleanSetRestrict_wp_qAssign_absorb h₁_pres, wpQAssignCompat_comp]
  | rep R body ih =>
      have hbody : body.SemValid v qToff S := hv; clear hv
      induction R generalizing Θ with
      | zero =>
          exact funext fun _ ↦ Subtype.ext
            (by simp [compile, toCircuit, repDynamic, repCircuit])
      | succ R ihr =>
          simp only [compile, toCircuit] at ihr
          simp only [compile, toCircuit, repDynamic, repCircuit, DynamicCircuit.compile_seq,
            wp_qSeq, Circuit.eval_seq]
          have hR_pres := SemValid.preservesCleanSet (p := .rep R body) hbody
          dsimp only [toCircuit] at hR_pres
          rw [ihr _ (wp_compile_storeIndep hbody hΘ),
            ← cleanSetRestrict_wp_qAssign_absorb hR_pres, ih hbody Θ hΘ,
            cleanSetRestrict_wp_qAssign_absorb hR_pres, wpQAssignCompat_comp]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      rcases hv with ⟨hanc, hbody, hanc_pres⟩
      let S' := S.erase anc
      let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
      have hunion : ({anc} : Finset (Wire n)) ∪ S' = S := Finset.insert_erase hanc
      have hT_swap (Φ : CQAssertionCompat Var (2 ^ n)) :
          cleanSetRestrict S' (wpQAssignCompat T_anc Φ) =
            wpQAssignCompat T_anc (cleanSetRestrict S' Φ) :=
        funext fun _ ↦ Subtype.ext (by
          have hadj : cleanSetProj S' * T_anc.1ᴴ = T_anc.1ᴴ * cleanSetProj S' := by
            simpa only [conjTranspose_mul, cleanSetProj_conjTranspose] using congrArg conjTranspose
              (toffoli_comm_cleanSetProj_of_not_mem c₁ c₂ anc h₁₂ h₁a h₂a S' (Finset.notMem_erase
                anc S))
          simp only [cleanSetRestrict_coe, wpQAssignCompat, qAssignObsMap, Observable.conj_coe,
            Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hadj])
      let Ψ_u := wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ
      have ha₁ : cleanSetRestrict ({anc} : Finset (Wire n))
          (wp (DynamicCircuit.seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
            (DynamicCircuit.seq (body.compile v qToff) (DynamicCircuit.andUncompute v c₁ c₂ anc
              h₁₂))).compile Θ) =
          cleanSetRestrict ({anc} : Finset (Wire n)) (wpQAssignCompat T_anc (wp (body.compile v
            qToff).compile Ψ_u)) := by
        rw [cleanSetRestrict_singleton, cleanSetRestrict_singleton]
        exact DynCircuitExt.restrictToZeroAncilla_wp_andCompute_seq_compat c₁ c₂ anc h₁₂ h₁a h₂a _ Θ
      have ha₂ : cleanSetRestrict ({anc} : Finset (Wire n)) (wpQAssignCompat T_anc (wpQAssignCompat
        body.toCircuit.eval Ψ_u)) =
          cleanSetRestrict ({anc} : Finset (Wire n))
            (wpQAssignCompat (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toCircuit ;;ᶜ Circuit.TOFF
              c₁ c₂ anc h₁₂ h₁a h₂a).eval Θ) := by
        rw [cleanSetRestrict_singleton, cleanSetRestrict_singleton]
        have hanc_pres' : (QRegister.singleton anc).basisOutcomeProjector 0 *
            (T_anc.1 * body.toCircuit.eval.1 * T_anc.1 *
              (QRegister.singleton anc).basisOutcomeProjector 0) =
            T_anc.1 * body.toCircuit.eval.1 * T_anc.1 *
              (QRegister.singleton anc).basisOutcomeProjector 0 := by
          rw [← cleanSetProj_singleton]
          simpa only [PreservesCleanSet, Circuit.eval_seq, Submonoid.coe_mul,
            Matrix.mul_assoc] using hanc_pres
        have hmid : wpQAssignCompat body.toCircuit.eval Ψ_u =
            wp (.qSeq body.toCircuit.compile (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile)
              Θ := by simp [Ψ_u]
        rw [hmid, ← DynCircuitExt.restrictToZeroAncilla_wp_andCompute_seq_compat
              c₁ c₂ anc h₁₂ h₁a h₂a (.qSeq body.toCircuit.compile (DynamicCircuit.andUncompute v c₁
                c₂ anc h₁₂).compile) Θ,
        ← DynCircuitExt.restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq_compat
              v c₁ c₂ anc h₁₂ h₁a h₂a body.toCircuit hanc_pres' Θ (fun σ _ ↦ hΘ _ σ)]
        rfl
      have hcomm_restr (Φ : CQAssertionCompat Var (2 ^ n)) :
          cleanSetRestrict S' (cleanSetRestrict ({anc} : Finset (Wire n)) Φ) =
            cleanSetRestrict ({anc} : Finset (Wire n)) (cleanSetRestrict S' Φ) := by
        rw [← cleanSetRestrict_union, ← cleanSetRestrict_union, Finset.union_comm]
      dsimp only [compile, toCircuit]
      rw [← hunion, cleanSetRestrict_union, cleanSetRestrict_union, ha₁, hcomm_restr,
        hT_swap, ih hbody Ψ_u (OctahedralOrbit.storeConst_wp_andUncompute v c₁ c₂ anc h₁₂ hΘ),
        ← hT_swap, ← hcomm_restr, ha₂]
  | custom _ _ _ => exact hv.2.2 Θ hΘ
theorem wp_compile_clean_workspace_spec {v : Var} {qToff : Wire n} {S : Finset (Wire n)}
    {p : DynProgS2 Var n} (hv : p.SemValid v qToff S) (rAct : QRegister k n)
    (rWork : QRegister m n) (hsub : ∀ w ∈ S, ∃ j : Fin m, rWork j = w) (u : Unitary (2 ^ k))
    (heval : p.toCircuit.eval = rAct.embedUnitary u) : ∀ M : Observable (Fin (2 ^ n)), ∃ M' :
    Observable (Fin (2 ^ n)), wp (p.compile v qToff).compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    rWork.basisOutcomeProjector 0 * M'.1.1 * rWork.basisOutcomeProjector 0 =
    rWork.basisOutcomeProjector 0 *
    ((rAct.embedUnitary u).1ᴴ * M.1.1 * (rAct.embedUnitary u).1) * rWork.basisOutcomeProjector
    0 := by
  have habs (A : CQAssertionCompat Var (2 ^ n)) :
      CQAssertion.restrictToZeroAncilla (cleanSetRestrict S A) rWork =
        CQAssertion.restrictToZeroAncilla A rWork :=
    funext fun _ ↦ Subtype.ext (by simp only [CQAssertion.restrictToZeroAncilla_coe,
      cleanSetRestrict_coe, conj_conj, basisOutcomeProjector_zero_mul_cleanSetProj rWork S hsub])
  intro M
  let σ₀ : Store Var := fun _ ↦ 0
  let M' : Observable (Fin (2 ^ n)) := wp (p.compile v qToff).compile (fun _ ↦ M) σ₀
  have hconst : wp (p.compile v qToff).compile (fun _ ↦ M) = (fun _ ↦ M') :=
    funext fun σ ↦ wp_compile_storeIndep hv (StoreIndep.const M) σ σ₀
  have hrestr : CQAssertion.restrictToZeroAncilla (wp (p.compile v qToff).compile (fun _ ↦
    M)) rWork =
      CQAssertion.restrictToZeroAncilla (wpQAssignCompat (rAct.embedUnitary u) (fun _ ↦ M)) rWork :=
        by
    rw [← habs, cleanSetRestrict_wp_compile_eq hv (fun _ ↦ M) (StoreIndep.const M), habs, heval]
  refine ⟨M', hconst, ?_⟩
  have hval := congrArg (fun A ↦ HermitianMat.mat (A σ₀).1) hrestr
  simp only [hconst, CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    conjTranspose_conjTranspose, HermitianMat.conj_apply_mat,
    QRegister.basisOutcomeProjector_conjTranspose, Matrix.mul_assoc] at hval
  change rWork.basisOutcomeProjector 0 * HermitianMat.mat M'.1 * rWork.basisOutcomeProjector 0
    = rWork.basisOutcomeProjector 0 * ((rAct.embedUnitary u).1ᴴ * HermitianMat.mat M.1 *
    (rAct.embedUnitary u).1) * rWork.basisOutcomeProjector 0
  simpa only [Matrix.mul_assoc] using hval
end Soundness
end DynProgS2
end SharedScope
end
end ModDynProgS2

end QuantumComputation.Specs.StoppingPowerSolution
