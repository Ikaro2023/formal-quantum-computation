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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WeightedCsa3Gen

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ZeroAncillaUSPS3Aux
local instance (priority := 1000000) instNeZeroTwoPow_ZeroAncillaUSPS3 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
section ZeroAncillaUSPS3

section ModZeroAncillaUSPS3
set_option exponentiation.threshold 256
public section
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation
namespace ZeroAncillaUSPS3
local instance (priority := 100000) instLoc_ZeroAncillaUSPS3_1InstNeZeroTwoPowUSPS3 (k : ℕ) : NeZero
  (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable abbrev ket {n : ℕ} (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  MeasureBranchHadamardSem.ket β
@[scoped simp] theorem basisBits_symm_eq {m : ℕ} (γ : BitAssignment m) : basisBits m
    ((basisBitsEquiv m).symm γ) = γ := (basisBitsEquiv m).apply_symm_apply γ
@[scoped simp] theorem symm_basisBits_eq {m : ℕ} (j : Fin (2 ^ m)) : (basisBitsEquiv m).symm
    (basisBits m j) = j := (basisBitsEquiv m).symm_apply_apply j
theorem upd_eq_self {n : ℕ} (β : BitAssignment n) (q : Wire n) {v : ZMod 2}
    (h : β q = v) : Function.update β q v = β := h ▸ Function.update_eq_self q β
theorem ite_pos' {α : Type*} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by simp [hp]
theorem dite_neg' {α : Type*} {p : Prop} [Decidable p] (hp : ¬ p)
    (a : p → α) (b : ¬ p → α) : (if h : p then a h else b h) = b hp := by simp [hp]
noncomputable def writeReg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[scoped simp] theorem writeReg_apply_reg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeReg β r γ (r i) = γ i := by
  simp [writeReg, QRegister.basisBits_replaceIndex_apply]
theorem writeReg_apply_of_not_mem {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeReg β r γ w = β w := by
  simp [writeReg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
def qregInit {m n : ℕ} (r : QRegister (m + 1) n) : QRegister m n where
  wires := ⟨fun i => r i.castSucc, fun _ _ h => Fin.castSucc_inj.mp (r.wires.injective h)⟩
theorem lt_pow_succ_of_lt {d : ℕ} (p : Fin (2 ^ d)) : p.val < 2 ^ (d + 1) :=
  p.isLt.trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self d))
theorem add_lt_pow_succ {d : ℕ} (p : Fin (2 ^ d)) : 2 ^ d + p.val < 2 ^ (d + 1) := by
  have := p.isLt
  rw [pow_succ]
  omega
theorem sub_pow_lt_of_not_lt {m : ℕ} (j : Fin (2 ^ (m + 1))) (h : ¬ j.val < 2 ^ m) :
    j.val - 2 ^ m < 2 ^ m := by
  have hj : j.val < 2 ^ m * 2 := pow_succ 2 m ▸ j.isLt
  omega
theorem writeReg_self {k n : ℕ} (β : BitAssignment n) (r : QRegister k n) {γ : BitAssignment k}
    (hγ : ∀ i : Fin k, γ i = β (r i)) : writeReg β r γ = β := funext fun w =>
  if hw : w ∈ Set.range r.wires then
    hw.elim fun i hi => hi ▸ (writeReg_apply_reg β r γ i).trans (hγ i)
  else writeReg_apply_of_not_mem β r γ w hw
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
  linear_combination (1 / 2 : ℂ) * Complex.I_sq
theorem omega8_pow_four : omega8 ^ 4 = -1 := by
  rw [show omega8 ^ 4 = (omega8 ^ 2) ^ 2 by ring, omega8_sq, Complex.I_sq]
theorem star_omega8 : star omega8 = -omega8 ^ 3 := by
  rw [show omega8 ^ 3 = omega8 ^ 2 * omega8 by ring, omega8_sq]
  simp only [omega8, div_eq_mul_inv, map_mul, map_add, map_one, Complex.star_def,
    Complex.conj_I, Complex.conj_inv, Complex.conj_ofReal]
  linear_combination (√2 : ℂ)⁻¹ * Complex.I_sq
theorem omega8_sub_cube_eq_sqrt2 : omega8 - omega8 ^ 3 = (√2 : ℂ) := by
  rw [show omega8 ^ 3 = omega8 ^ 2 * omega8 by ring, omega8_sq, omega8]
  field_simp [sqrt2_ne_zero_c]
  rw [sq (√2 : ℂ), sqrt2_mul_self_c]
  ring_nf
  rw [Complex.I_sq]
  ring
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
    rw [star_pow, star_omega8, show (-omega8 ^ 3) ^ 3 = -(omega8 ^ 4 * omega8 ^ 4 * omega8) by ring,
      omega8_pow_four]
    ring
  have hc_int (k : ℤ) : star (k : ℂ) = (k : ℂ) := by simp
  simp only [zwConj, Zw.toComplex, Int.cast_neg, star_add, star_mul, hc_int, star_omega8, hs2, hs3]
  ring
theorem toComplex_zwMul (a b : Zw) : (zwMul a b).toComplex = a.toComplex * b.toComplex := by
  simp only [zwMul, Zw.toComplex, Int.cast_add, Int.cast_sub, Int.cast_mul]
  linear_combination (-((a.c1 : ℂ) * b.c3 + a.c2 * b.c2 + a.c3 * b.c1) -
    (a.c2 * b.c3 + a.c3 * b.c2) * omega8 - a.c3 * b.c3 * omega8 ^ 2) * omega8_pow_four
theorem normSq_zw_eq (a : Zw) :
    ‖a.toComplex‖ ^ 2 = ((zwMul a (zwConj a)).c0 : ℝ) + ((zwMul a (zwConj a)).c1 : ℝ) * √2 := by
  rw [Complex.sq_norm]
  apply Complex.ofReal_injective
  rw [← Complex.mul_conj, ← Complex.star_def, ← toComplex_zwConj, ← toComplex_zwMul]
  have h : (zwMul a (zwConj a)).toComplex =
      ((zwMul a (zwConj a)).c0 : ℂ) + (zwMul a (zwConj a)).c1 * (omega8 - omega8 ^ 3) := by
    simp only [Zw.toComplex, zwMul, zwConj, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg]
    ring
  rw [h, omega8_sub_cube_eq_sqrt2]
  push_cast
  ring
inductive HSTGate where
  | H
  | S
  | T
  deriving DecidableEq, Repr
def hstGateCircuit {n : ℕ} (g : HSTGate) (q : Wire n) : Circuit n :=
  match g with
  | .H => Circuit.H q
  | .S => Circuit.S q
  | .T => Circuit.T q
def hstWordCircuit {n : ℕ} (w : List HSTGate) (q : Wire n) : Circuit n :=
  match w with
  | [] => Circuit.identity
  | g :: gs => hstGateCircuit g q ;;ᶜ hstWordCircuit gs q
def hstWordTCount (w : List HSTGate) : ℕ :=
  match w with
  | [] => 0
  | .T :: gs => 1 + hstWordTCount gs
  | _ :: gs => hstWordTCount gs
def ctrlProbGate {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t) : Circuit n :=
  (hstWordCircuit w t).inverse ;;ᶜ Circuit.CNOT c t hct ;;ᶜ hstWordCircuit w t
@[scoped simp] theorem count_toff_hstWordCircuit {n : ℕ} (w : List HSTGate) (q : Wire n) :
    (hstWordCircuit w q).count PrimitiveGate.TOFF = 0 := by
  induction w with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [hstWordCircuit, hstGateCircuit, ih]
@[scoped simp] theorem count_t_hstWordCircuit {n : ℕ} (w : List HSTGate) (q : Wire n) :
    (hstWordCircuit w q).count PrimitiveGate.T = hstWordTCount w := by
  induction w with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [hstWordCircuit, hstGateCircuit, hstWordTCount, ih]
@[scoped simp]
theorem count_toff_ctrlProbGate {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t) :
    (ctrlProbGate w c t hct).count PrimitiveGate.TOFF = 0 := by
  simp [ctrlProbGate]
@[scoped simp]
theorem count_t_ctrlProbGate {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t) :
    (ctrlProbGate w c t hct).count PrimitiveGate.T = 2 * hstWordTCount w := by
  simp [ctrlProbGate, two_mul]
structure Mat2Zw where
  m00 : Zw
  m01 : Zw
  m10 : Zw
  m11 : Zw
  h : ℕ
  deriving DecidableEq, Repr
def matId : Mat2Zw := ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, 0⟩
def evalList : List HSTGate → Mat2Zw → Mat2Zw
  | [], m => m
  | .H :: gs, m =>
    evalList gs ⟨zwAdd m.m00 m.m10, zwAdd m.m01 m.m11, zwSub m.m00 m.m10, zwSub m.m01 m.m11, m.h +
      1⟩
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
  (wordMatrix2 w * !![(0 : ℂ), 1; 1, 0] * (wordMatrix2 w)ᴴ) 0 0
noncomputable def alpha1 (w : List HSTGate) : ℂ :=
  (wordMatrix2 w * !![(0 : ℂ), 1; 1, 0] * (wordMatrix2 w)ᴴ) 1 0
theorem singleton_embedMatrix_mulVec_ket {n : ℕ} (q : Wire n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (β : BitAssignment n) : ((QRegister.singleton q).embedMatrix A).mulVec (ket β) = A 0
    (if β q = 0 then 0 else 1) • ket (Function.update β q 0) + A 1 (if β q = 0 then 0 else 1)
    • ket (Function.update β q 1) := by
  let A1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ := A
  change ((QRegister.singleton q).embedMatrix A1).mulVec (ket β) = _
  have hext : (QRegister.singleton q).extractIndex ((basisBitsEquiv n).symm β) =
      if β q = 0 then 0 else 1 := by
    simp only [QRegister.extractIndex, basisBits_symm_eq]
    exact (by decide : ∀ b : ZMod 2,
      ((basisBitsEquiv 1).symm (fun _ => b) : Fin 2) = if b = 0 then 0 else 1) (β q)
  have hcol (j : Fin (2 ^ 1)) :
      A1.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ 1), A1 l j • Pi.single l 1 :=
    funext fun x => by simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hw (l : Fin (2 ^ 1)) (b : ZMod 2) (hb : basisBits 1 l = fun _ => b) :
      writeReg β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b :=
    funext fun w =>
      if hqw : w = q then
        hqw ▸ (by simpa [hb] using writeReg_apply_reg β (QRegister.singleton w) (basisBits 1 l) 0)
      else
        (writeReg_apply_of_not_mem _ _ _ _ fun ⟨_, h⟩ => hqw h.symm).trans
          (Function.update_of_ne hqw _ _).symm
  rw [ket, MeasureBranchHadamardSem.ket, basisState, QRegister.embedMatrix_mulVec_single_factors,
    hext, hcol, QRegister.tensorState_sum_left]
  change (∑ index : Fin 2, _) = _
  rw [Fin.sum_univ_two, QRegister.tensorState_smul_left, QRegister.tensorState_smul_left,
    QRegister.tensorState_single_replaceIndex, QRegister.tensorState_single_replaceIndex]
  have hk (l : Fin (2 ^ 1)) :
      Pi.single ((QRegister.singleton q).replaceIndex ((basisBitsEquiv n).symm β) l) (1 : ℂ) =
        ket (writeReg β (QRegister.singleton q) (basisBits 1 l)) := by
    rw [ket, MeasureBranchHadamardSem.ket, basisState, writeReg,
      symm_basisBits_eq, symm_basisBits_eq]
  rw [hk 0, hk 1, hw 0 0 (by decide), hw 1 1 (by decide)]
theorem hstGate_eval_eq {n : ℕ} (g : HSTGate) (q : Wire n) : (hstGateCircuit g q).eval.1 =
    (QRegister.singleton q).embedMatrix (wordMatrix2 [g]) := by
  cases g
  · apply MeasureBranchHadamardSem.matrix_ext_ket
    intro β
    rw [hstGateCircuit, MeasureBranchHadamardSem.ket_H, singleton_embedMatrix_mulVec_ket]
    rcases MeasureBranchHadamardSem.bit_cases (β q) with hb | hb
    · rw [hb, ite_pos' rfl]
      dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, Zw.toComplex,
        Pi.smul_apply, smul_eq_mul, MeasureBranchHadamardSem.bitSign]
      ext idx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [hb]
      simp only [one_ne_zero, ↓reduceIte, MeasureBranchHadamardSem.bitSign]
      dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, Zw.toComplex,
        Pi.smul_apply, smul_eq_mul]
      ext idx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  · rw [hstGateCircuit, Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_s_val]
    congr 1; ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.diagonal_apply] <;>
      dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwMulI, Zw.toComplex,
        Pi.smul_apply, smul_eq_mul] <;>
      norm_num
    exact omega8_sq.symm
  · rw [hstGateCircuit, Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_t_val]
    congr 1; ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.diagonal_apply] <;>
      dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwMulW, omega8, Zw.toComplex,
        Pi.smul_apply, smul_eq_mul] <;>
      norm_num
theorem evalList_mul_right (gs : List HSTGate) (m : Mat2Zw) :
    (evalList gs m).toMatrix = (evalList gs matId).toMatrix * m.toMatrix := by
  induction gs generalizing m with
  | nil =>
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
      dsimp [evalList, matId, Mat2Zw.toMatrix, Zw.toComplex, Pi.smul_apply, smul_eq_mul] <;>
      ring
  | cons g gs ih =>
    rcases m with ⟨m00, m01, m10, m11, h⟩
    cases g
    · conv_lhs => dsimp only [evalList]; rw [ih]
      conv_rhs => arg 1; dsimp only [evalList]; rw [ih]
      rw [Matrix.mul_assoc]; congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
        dsimp [evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, Zw.toComplex, Pi.smul_apply,
          smul_eq_mul] <;>
        norm_num <;>
        ring
    · conv_lhs => dsimp only [evalList]; rw [ih]
      conv_rhs => arg 1; dsimp only [evalList]; rw [ih]
      rw [Matrix.mul_assoc]; congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
        dsimp [evalList, matId, Mat2Zw.toMatrix, zwMulI, Zw.toComplex, Pi.smul_apply, smul_eq_mul]
          <;>
        norm_num
      · linear_combination -MeasureBranchHadamardSem.sqrtHalf ^ h * (↑m10.c2 + ↑m10.c3 * omega8) *
          omega8_pow_four
      · linear_combination -MeasureBranchHadamardSem.sqrtHalf ^ h * (↑m11.c2 + ↑m11.c3 * omega8) *
          omega8_pow_four
    · conv_lhs => dsimp only [evalList]; rw [ih]
      conv_rhs => arg 1; dsimp only [evalList]; rw [ih]
      rw [Matrix.mul_assoc]; congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
        dsimp [evalList, matId, Mat2Zw.toMatrix, zwMulW, Zw.toComplex, Pi.smul_apply, smul_eq_mul]
          <;>
        norm_num
      · linear_combination -MeasureBranchHadamardSem.sqrtHalf ^ h * ↑m10.c3 * omega8_pow_four
      · linear_combination -MeasureBranchHadamardSem.sqrtHalf ^ h * ↑m11.c3 * omega8_pow_four
theorem hstWordCircuit_eval_eq_embedMatrix {n : ℕ} (w : List HSTGate) (q : Wire n) :
    (hstWordCircuit w q).eval.1 = (QRegister.singleton q).embedMatrix (wordMatrix2 w) := by
  induction w with
  | nil =>
    rw [hstWordCircuit, Circuit.eval_identity]
    have hid : wordMatrix2 [] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, Zw.toComplex,
          Pi.smul_apply, smul_eq_mul] <;>
        norm_num
    rw [hid, QRegister.embedMatrix_one]; rfl
  | cons g gs ih =>
    rw [hstWordCircuit, Circuit.eval_seq, Submonoid.coe_mul, ih, hstGate_eval_eq,
      ← QRegister.embedMatrix_mul]
    congr 1
    cases g <;> exact (evalList_mul_right gs _).symm
theorem wordMatrix2_unitary (w : List HSTGate) : wordMatrix2 w * (wordMatrix2 w)ᴴ = 1 := by
  let M := wordMatrix2 w * (wordMatrix2 w)ᴴ
  have h1 : (QRegister.singleton (0 : Wire 1)).embedMatrix M = 1 := by
    rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_conjTranspose,
      ← hstWordCircuit_eval_eq_embedMatrix w (0 : Wire 1)]
    exact ((hstWordCircuit w (0 : Wire 1)).eval).2.2
  let β0 : BitAssignment 1 := fun _ => 0
  let β1 : BitAssignment 1 := fun _ => 1
  let g0 : Fin (2 ^ 1) := (basisBitsEquiv 1).symm β0
  let g1 : Fin (2 ^ 1) := (basisBitsEquiv 1).symm β1
  have hg01 : g0 ≠ g1 := fun h => zero_ne_one (α := ZMod 2)
    (by simpa [g0, g1, β0, β1] using congrArg (fun x => basisBits 1 x 0) h)
  have hupd (b c : ZMod 2) : Function.update (fun _ : Wire 1 => b) 0 c = fun _ => c := by
    ext q
    rw [Subsingleton.elim q 0, Function.update_self]
  have hc0 := congrArg (fun A => A.mulVec (ket β0)) h1
  rw [singleton_embedMatrix_mulVec_ket, Matrix.one_mulVec, ite_pos' rfl, hupd 0 0, hupd 0 1] at hc0
  have hm00 : M 0 0 = 1 := by
    simpa [ket, MeasureBranchHadamardSem.ket, basisState, g0, g1, β0, β1,
      Pi.single_eq_of_ne hg01] using congrFun hc0 g0
  have hm10 : M 1 0 = 0 := by
    simpa [ket, MeasureBranchHadamardSem.ket, basisState, g0, g1, β0, β1,
      Pi.single_eq_of_ne hg01.symm] using congrFun hc0 g1
  have hc1 := congrArg (fun A => A.mulVec (ket β1)) h1
  rw [singleton_embedMatrix_mulVec_ket, Matrix.one_mulVec] at hc1
  simp only [β1, one_ne_zero, ↓reduceIte, hupd 1 0, hupd 1 1] at hc1
  have hm01 : M 0 1 = 0 := by
    simpa [ket, MeasureBranchHadamardSem.ket, basisState, g0, g1, β0, β1,
      Pi.single_eq_of_ne hg01] using congrFun hc1 g0
  have hm11 : M 1 1 = 1 := by
    simpa [ket, MeasureBranchHadamardSem.ket, basisState, g0, g1, β0, β1,
      Pi.single_eq_of_ne hg01.symm] using congrFun hc1 g1
  ext i j
  fin_cases i <;> fin_cases j <;> assumption
private theorem hstWordCircuit_inv_eval_eq {n : ℕ} (w : List HSTGate) (t : Wire n) :
    ((hstWordCircuit w t).eval⁻¹).1 =
      (QRegister.singleton t).embedMatrix ((wordMatrix2 w)ᴴ) := by
  change star ((hstWordCircuit w t).eval.1) = _
  rw [Matrix.star_eq_conjTranspose, hstWordCircuit_eval_eq_embedMatrix,
    QRegister.embedMatrix_conjTranspose]
theorem ctrlProbGate_mulVec_ket_zero {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t)
    (β : BitAssignment n) (hc : β c = 0) :
    (ctrlProbGate w c t hct).eval.1.mulVec (ket β) = ket β := by
  have hcnot (x : ZMod 2) :
      (Circuit.CNOT c t hct).eval.1.mulVec (ket (Function.update β t x)) =
        ket (Function.update β t x) := by
    rw [MeasureBranchHadamardSem.ket_CNOT, Function.update_of_ne hct, hc, add_zero,
      Function.update_idem, Function.update_self]
  rw [ctrlProbGate, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec, Circuit.eval_inverse,
    hstWordCircuit_inv_eval_eq, singleton_embedMatrix_mulVec_ket,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hcnot 0, hcnot 1,
    ← singleton_embedMatrix_mulVec_ket t ((wordMatrix2 w)ᴴ) β,
    ← hstWordCircuit_inv_eval_eq, Matrix.mulVec_mulVec, ← Submonoid.coe_mul,
    congrArg Subtype.val (mul_inv_cancel (hstWordCircuit w t).eval), Submonoid.coe_one,
      Matrix.one_mulVec]
theorem ctrlProbGate_mulVec_ket_one_zero {n : ℕ} (w : List HSTGate) (c t : Wire n) (hct : c ≠ t)
    (β : BitAssignment n) (hc : β c = 1) (ht : β t = 0) :
    (ctrlProbGate w c t hct).eval.1.mulVec (ket β) =
      alpha0 w • ket β + alpha1 w • ket (Function.update β t 1) := by
  let M2 : Matrix (Fin 2) (Fin 2) ℂ := wordMatrix2 w * !![(0 : ℂ), 1; 1, 0] * (wordMatrix2 w)ᴴ
  suffices hM : (ctrlProbGate w c t hct).eval.1.mulVec (ket β) =
      ((QRegister.singleton t).embedMatrix M2).mulVec (ket β) by
    rw [hM, singleton_embedMatrix_mulVec_ket, ite_pos' ht, upd_eq_self β t ht]
    rfl
  have hcnot (x : ZMod 2) :
      (Circuit.CNOT c t hct).eval.1.mulVec (ket (Function.update β t x)) =
        ket (Function.update β t (x + 1)) := by
    rw [MeasureBranchHadamardSem.ket_CNOT, Function.update_of_ne hct, hc,
      Function.update_self, Function.update_idem]
  have hx (x : ZMod 2) :
      ((QRegister.singleton t).embedMatrix !![(0 : ℂ), 1; 1, 0]).mulVec
        (ket (Function.update β t x)) = ket (Function.update β t (x + 1)) := by
    rw [singleton_embedMatrix_mulVec_ket, Function.update_self, Function.update_idem,
      Function.update_idem]
    rcases MeasureBranchHadamardSem.bit_cases x with rfl | rfl
    · simp
    · simp [one_ne_zero, show (1 : ZMod 2) + 1 = 0 from rfl]
  rw [ctrlProbGate, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec, Circuit.eval_inverse, hstWordCircuit_inv_eval_eq,
    singleton_embedMatrix_mulVec_ket, ite_pos' ht,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hcnot 0, hcnot 1,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  symm
  dsimp only [M2]
  rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, singleton_embedMatrix_mulVec_ket t ((wordMatrix2 w)ᴴ) β,
    ite_pos' ht, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx 0, hx 1,
    ← hstWordCircuit_eval_eq_embedMatrix, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul]
theorem norm_sq_alpha0_add_alpha1 (w : List HSTGate) :
    ‖alpha0 w‖ ^ 2 + ‖alpha1 w‖ ^ 2 = 1 := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := wordMatrix2 w * !![(0 : ℂ), 1; 1, 0] * (wordMatrix2 w)ᴴ
  have hX : (!![(0 : ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![(0 : ℂ), 1; 1, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      dsimp <;>
      norm_num
  have hU : (wordMatrix2 w)ᴴ * wordMatrix2 w = 1 := mul_eq_one_comm.mp (wordMatrix2_unitary w)
  have hM : Mᴴ * M = 1 := by
    dsimp [M]
    calc (wordMatrix2 w * !![(0 : ℂ), 1; 1, 0] * (wordMatrix2 w)ᴴ)ᴴ *
          (wordMatrix2 w * !![(0 : ℂ), 1; 1, 0] * (wordMatrix2 w)ᴴ)
        = wordMatrix2 w * ((!![(0 : ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
            ((wordMatrix2 w)ᴴ * wordMatrix2 w) * !![(0 : ℂ), 1; 1, 0]) * (wordMatrix2 w)ᴴ := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
              Matrix.mul_assoc]
      _ = wordMatrix2 w * (wordMatrix2 w)ᴴ := by rw [hU, Matrix.mul_one, hX, Matrix.mul_one]
      _ = 1 := wordMatrix2_unitary w
  have h00 := congrArg (fun A => A 0 0) hM
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.one_apply_eq]
    at h00
  have hnorm (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hnorm (M 0 0), hnorm (M 1 0), ← Complex.ofReal_add] at h00
  exact Complex.ofReal_injective (by simpa [alpha0, alpha1] using h00)
theorem norm_sq_alpha1_of_eval (w : List HSTGate) (m : Mat2Zw)
    (heval : evalList w matId = m) :
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
    simp only [alpha1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    rw [wordMatrix2, heval]
    simp only [Mat2Zw.toMatrix, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, star_mul]
    have hexp : a1.toComplex =
        m.m10.toComplex * star m.m01.toComplex + m.m11.toComplex * star m.m00.toComplex := by
      simp only [a1, toComplex_zwAdd, toComplex_zwMul, toComplex_zwConj]
    calc _ = ((MeasureBranchHadamardSem.sqrtHalf : ℂ) ^ m.h *
            star ((MeasureBranchHadamardSem.sqrtHalf : ℂ) ^ m.h)) *
            (m.m10.toComplex * star m.m01.toComplex + m.m11.toComplex * star m.m00.toComplex) := by
          ring
      _ = ((1 / 2 : ℂ) ^ m.h) * a1.toComplex := by rw [hsh, hexp]
  change ‖alpha1 w‖ ^ 2 = ((p.c0 : ℝ) + (p.c1 : ℝ) * √2) / ((2 : ℝ) ^ (2 * m.h))
  rw [ha1, norm_mul, mul_pow, normSq_zw_eq a1]
  have hhalf : ‖(1 / 2 : ℂ) ^ m.h‖ ^ 2 = 1 / ((2 : ℝ) ^ (2 * m.h)) := by
    rw [norm_pow, one_div (2 : ℂ), norm_inv, Complex.norm_ofNat,
      ← pow_mul, mul_comm m.h 2, inv_pow, one_div]
  rw [hhalf]
  dsimp only [p]
  ring
theorem alpha1_H_eq_zero : alpha1 [.H] = 0 := by
  have h := norm_sq_alpha1_of_eval [.H] _ rfl
  dsimp [evalList, matId, zwAdd, zwSub, zwMul, zwConj] at h
  norm_num at h
  exact h
attribute [local simp] alpha1_H_eq_zero
theorem alpha0_nil_eq_zero : alpha0 [] = 0 := by
  simp only [alpha0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, Zw.toComplex, Pi.smul_apply, smul_eq_mul]
  norm_num
attribute [local simp] alpha0_nil_eq_zero
def leSqrt2Int (b rhs : ℤ) : Bool := if b == 0 then decide (0 ≤ rhs) else if b > 0 then decide
    (0 ≤ rhs) && decide (2 * b * b ≤ rhs * rhs) else if rhs ≥ 0 then true else decide
    (rhs * rhs ≤ 2 * b * b)
theorem leSqrt2Int_sound (b rhs : ℤ) (h : leSqrt2Int b rhs = true) :
    (b : ℝ) * √2 ≤ (rhs : ℝ) := by
  unfold leSqrt2Int at h
  by_cases hb : b = 0
  · subst hb
    simp only [beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at h
    simpa using (by exact_mod_cast h : (0 : ℝ) ≤ (rhs : ℝ))
  · rw [beq_false_of_ne hb] at h
    by_cases hpos : b > 0
    · simp only [Bool.false_eq_true, ↓reduceIte, hpos, Bool.and_eq_true, decide_eq_true_eq] at h
      have hsq : ((b : ℝ) * √2) ^ 2 ≤ (rhs : ℝ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), sq]
        linarith [show 2 * (b : ℝ) * b ≤ rhs * rhs from by exact_mod_cast h.2]
      exact (abs_le_of_sq_le_sq' hsq (by exact_mod_cast h.1)).2
    · simp only [Bool.false_eq_true, ↓reduceIte, hpos] at h
      by_cases hrpos : rhs ≥ 0
      · exact (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega : b ≤ 0))
          (Real.sqrt_nonneg 2)).trans (by exact_mod_cast hrpos)
      · simp only [hrpos, ↓reduceIte, decide_eq_true_eq] at h
        have hmb : (0 : ℝ) ≤ (-b : ℝ) * √2 :=
          mul_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ -b)) (Real.sqrt_nonneg 2)
        have hsq : (rhs : ℝ) ^ 2 ≤ ((-b : ℝ) * √2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num), sq]
          linarith [show (rhs : ℝ) * rhs ≤ 2 * b * b from by exact_mod_cast h]
        linarith [(abs_le_of_sq_le_sq' hsq hmb).1]
def ctrlProbIf {n : ℕ} (w : List HSTGate) (c t : Wire n) : Circuit n :=
  if hct : c = t then Circuit.identity else ctrlProbGate w c t hct
def cnotIf {n : ℕ} (c t : Wire n) : Circuit n :=
  if hct : c = t then Circuit.identity else Circuit.CNOT c t hct
def andComputeIf {n : ℕ} (c₁ c₂ anc : Wire n) : Circuit n := if h1 : c₁ = anc then
    Circuit.identity else if h2 : c₂ = anc then Circuit.identity else Circuit.andCompute c₁ c₂
    anc h1 h2
@[scoped simp] theorem count_toff_ctrlProbIf {n : ℕ} (w : List HSTGate) (c t : Wire n) :
    (ctrlProbIf w c t).count PrimitiveGate.TOFF = 0 := by
  unfold ctrlProbIf
  split_ifs <;> simp
@[scoped simp] theorem count_toff_cnotIf {n : ℕ} (c t : Wire n) :
    (cnotIf c t).count PrimitiveGate.TOFF = 0 := by
  unfold cnotIf
  split_ifs <;> simp
@[scoped simp] theorem count_t_cnotIf {n : ℕ} (c t : Wire n) :
    (cnotIf c t).count PrimitiveGate.T = 0 := by
  unfold cnotIf
  split_ifs <;> simp
@[scoped simp] theorem count_toff_andComputeIf {n : ℕ} (c₁ c₂ anc : Wire n) :
    (andComputeIf c₁ c₂ anc).count PrimitiveGate.TOFF = 0 := by
  unfold andComputeIf
  split_ifs <;> simp [Circuit.count_andCompute_toff]
theorem ket_andCompute_of_zero {n : ℕ} (c₁ c₂ anc : Wire n) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (β : BitAssignment n) (hanc : β anc = 0) :
    (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval.1.mulVec (ket β) =
      ket (Function.update β anc (β c₁ * β c₂)) := by
  have ket_S_loc : ∀ (q : Wire n) (γ : BitAssignment n), (Circuit.S q).eval.1.mulVec (ket γ) =
      (if γ q = 0 then (1 : ℂ) else Complex.I) • ket γ := by
    intro q γ
    rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_s_val,
      singleton_embedMatrix_mulVec_ket]
    have e := Function.update_eq_self q γ
    rcases MeasureBranchHadamardSem.bit_cases (γ q) with hb | hb <;>
      rw [hb] at e <;> simp [hb, e]
  have ket_T_loc : ∀ (q : Wire n) (γ : BitAssignment n), (Circuit.T q).eval.1.mulVec (ket γ) =
      (if γ q = 0 then (1 : ℂ) else omega8) • ket γ := by
    intro q γ
    rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_t_val,
      singleton_embedMatrix_mulVec_ket]
    have e := Function.update_eq_self q γ
    rcases MeasureBranchHadamardSem.bit_cases (γ q) with hb | hb <;>
      rw [hb] at e <;> simp [hb, e, omega8]
  have ket_Z_loc : ∀ (q : Wire n) (γ : BitAssignment n), (Circuit.Z q).eval.1.mulVec (ket γ) =
      MeasureBranchHadamardSem.bitSign (γ q) • ket γ := by
    intro q γ
    rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
    change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec _ = _
    rw [singleton_embedMatrix_mulVec_ket]
    have e := Function.update_eq_self q γ
    rcases MeasureBranchHadamardSem.bit_cases (γ q) with hb | hb <;>
      rw [hb] at e <;> simp [hb, e, MeasureBranchHadamardSem.bitSign]
  have ket_Tinv_loc : ∀ (q : Wire n) (γ : BitAssignment n),
      (Circuit.T q).inverse.eval.1.mulVec (ket γ) =
        (if γ q = 0 then (1 : ℂ) else -omega8 ^ 3) • ket γ := by
    intro q γ
    change (Circuit.T q ;;ᶜ (Circuit.S q ;;ᶜ (Circuit.Z q ;;ᶜ .identity))).eval.1.mulVec (ket γ) = _
    simp only [MeasureBranchHadamardSem.eval_seq_mulVec, Circuit.eval_identity, Submonoid.coe_one,
      Matrix.one_mulVec, ket_T_loc, ket_S_loc, ket_Z_loc, Matrix.mulVec_smul, smul_smul]
    congr 1
    rcases MeasureBranchHadamardSem.bit_cases (γ q) with hb | hb
    · simp [hb, MeasureBranchHadamardSem.bitSign]
    · simp only [hb, MeasureBranchHadamardSem.bitSign, one_ne_zero, ↓reduceIte]
      rw [← omega8_sq]
      ring
  let fT : ZMod 2 → ℂ := fun b => if b = 0 then 1 else omega8
  let fTi : ZMod 2 → ℂ := fun b => if b = 0 then 1 else -omega8 ^ 3
  have hTTi (b : ZMod 2) : fT b * fTi b = 1 := by
    rcases MeasureBranchHadamardSem.bit_cases b with rfl | rfl
    · dsimp [fT, fTi]; ring
    · dsimp [fT, fTi]
      calc omega8 * -omega8 ^ 3 = -omega8 ^ 4 := by ring
        _ = 1 := by rw [omega8_pow_four]; ring
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
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
      calc x + y + z + y = x + z + (y + y) := by ring
        _ = x + z := by rw [CharTwo.add_self_eq_zero, add_zero]
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
      calc fT (a + x₂) * fTi (a + x₂) * fT a * fTi a
          = (fT (a + x₂) * fTi (a + x₂)) * (fT a * fTi a) := by ring
        _ = 1 := by rw [hTTi, hTTi, mul_one]
    · rcases MeasureBranchHadamardSem.bit_cases x₂ with rfl | rfl
      · rw [mul_zero, ite_pos' rfl, add_zero]
        calc fT (a + 1) * fTi a * fT a * fTi (a + 1)
            = (fT (a + 1) * fTi (a + 1)) * (fT a * fTi a) := by ring
          _ = 1 := by rw [hTTi, hTTi, mul_one]
      · have hne : (1 : ZMod 2) ≠ 0 := one_ne_zero
        rw [one_mul]
        simp only [hne, ↓reduceIte]
        rcases MeasureBranchHadamardSem.bit_cases a with rfl | rfl
        · rw [zero_add, h11, ite_pos' rfl]
          dsimp [fT, fTi]
          calc 1 * -omega8 ^ 3 * 1 * -omega8 ^ 3 = omega8 ^ 4 * omega8 ^ 2 := by ring
            _ = -Complex.I := by rw [omega8_pow_four, omega8_sq]; ring
        · rw [h11, zero_add]
          dsimp [fT, fTi]
          calc omega8 * 1 * omega8 * 1 = omega8 ^ 2 := by ring
            _ = Complex.I := omega8_sq
  have ket_H_loc (q : Wire n) (γ : BitAssignment n) : (Circuit.H q).eval.1.mulVec (ket γ) =
      MeasureBranchHadamardSem.sqrtHalf • (ket (Function.update γ q 0) +
      MeasureBranchHadamardSem.bitSign (γ q) • ket (Function.update γ q 1)) :=
      MeasureBranchHadamardSem.ket_H q γ
  have hs0 : MeasureBranchHadamardSem.bitSign (β anc) = 1 := by
    simp [hanc, MeasureBranchHadamardSem.bitSign]
  rw [Circuit.andCompute, MeasureBranchHadamardSem.eval_seq_mulVec, ket_H_loc,
    hs0, one_smul, Matrix.mulVec_smul, Matrix.mulVec_add, hjones, hjones]
  simp only [Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a, hph]
  simp only [MeasureBranchHadamardSem.eval_seq_mulVec, ket_H_loc,
    Function.update_self, Function.update_idem, Matrix.mulVec_add, Matrix.mulVec_smul, ket_S_loc]
  have hne10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  simp only [MeasureBranchHadamardSem.bitSign, hne10, ↓reduceIte, one_smul]
  rcases MeasureBranchHadamardSem.bit_cases (β c₁ * β c₂) with hp | hp
  · rw [hp]
    simp only [ite_true]
    ext idx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket (Function.update β anc 0) idx) * (2 * hsh2)
  · rw [hp]
    simp only [hne10, ↓reduceIte]
    ext idx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket (Function.update β anc 1) idx) * (-2 * Complex.I ^ 2 * hsh2 -
      Complex.I_sq)
theorem ket_andCompute_inv_of_zero {n : ℕ} (c₁ c₂ anc : Wire n) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (β : BitAssignment n) (hanc : β anc = 0) :
    (Circuit.andCompute c₁ c₂ anc h₁a h₂a).inverse.eval.1.mulVec
        (ket (Function.update β anc (β c₁ * β c₂))) = ket β := by
  rw [← ket_andCompute_of_zero c₁ c₂ anc h₁a h₂a β hanc, Circuit.eval_inverse, Matrix.mulVec_mulVec]
  have hcancel : ((Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval⁻¹).1 *
      (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval.1 = 1 :=
    congrArg Subtype.val (inv_mul_cancel (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval)
  rw [hcancel, Matrix.one_mulVec]
theorem writeReg_split_msb {m n : ℕ} (β : BitAssignment n) (r : QRegister (m + 1) n)
    (b : ZMod 2) (x : Fin (2 ^ m))
    (j : Fin (2 ^ (m + 1))) (hj : j.val = (if b = 0 then 0 else 2 ^ m) + x.val) :
    writeReg (Function.update β (r (Fin.last m)) b) (qregInit r)
        (basisBits m x) = writeReg β r (basisBits (m + 1) j) := by
  let rLow : QRegister m n := qregInit r
  have hbit_low (i : Fin m) : basisBits (m + 1) j i.castSucc = basisBits m x i := by
    rw [basisBits_eq_div_mod, basisBits_eq_div_mod, hj]
    dsimp only [Fin.val_castSucc]
    rcases MeasureBranchHadamardSem.bit_cases b with hb | hb
    · simp [hb]
    · simp only [hb, one_ne_zero, ↓reduceIte]
      have h2 : 2 ^ m = 2 ^ (m - i.val) * 2 ^ i.val := by
        rw [← pow_add, Nat.sub_add_cancel i.isLt.le]
      have hev : 2 ^ (m - i.val) % 2 = 0 := by
        rw [show m - i.val = (m - i.val - 1) + 1 by omega, pow_succ]
        omega
      have hdiv (k : ℕ) : (2 ^ m + k) / 2 ^ i.val = 2 ^ (m - i.val) + k / 2 ^ i.val := by
        rw [h2, add_comm, Nat.add_mul_div_right k _ (Nat.two_pow_pos i.val), add_comm]
      rw [hdiv x.val]
      congr 1
      omega
  have hbit_top : basisBits (m + 1) j (Fin.last m) = b := by
    rw [basisBits_eq_div_mod, hj]
    rcases MeasureBranchHadamardSem.bit_cases b with hb | hb
    · simp [hb, Nat.div_eq_of_lt x.isLt]
    · simp only [hb, one_ne_zero, ↓reduceIte, Fin.val_last]
      have hdiv : (2 ^ m + x.val) / 2 ^ m = 1 := by
        rw [add_comm, Nat.add_div_right _ (by positivity : 0 < 2 ^ m), Nat.div_eq_of_lt x.isLt,
          zero_add]
      rw [hdiv]; norm_num
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [writeReg_apply_reg]
    refine Fin.lastCases (motive := fun i =>
        writeReg (Function.update β (r (Fin.last m)) b) rLow (basisBits m x) (r i) =
          basisBits (m + 1) j i) ?_ ?_ i
    · rw [writeReg_apply_of_not_mem _ _ _ _
        (by rintro ⟨k, hk⟩; exact Fin.castSucc_ne_last k (r.wires.injective hk)),
        Function.update_self, hbit_top]
    · intro k
      change writeReg _ rLow _ (rLow k) = _
      rw [writeReg_apply_reg, hbit_low k]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw,
      writeReg_apply_of_not_mem _ _ _ _ (by rintro ⟨k, rfl⟩; exact hw ⟨k.castSucc, rfl⟩),
      Function.update_of_ne (fun h => hw ⟨Fin.last m, h.symm⟩)]
theorem fin_sum_pow_succ {α : Type*} [AddCommMonoid α] (m : ℕ) (f : Fin (2 ^ (m + 1)) → α) :
    (∑ j : Fin (2 ^ (m + 1)), f j) = (∑ x : Fin (2 ^ m), f ⟨x.val, lt_pow_succ_of_lt x⟩) +
    (∑ x : Fin (2 ^ m), f ⟨2 ^ m + x.val, add_lt_pow_succ x⟩) := by
  let e : Fin (2 ^ m) ⊕ Fin (2 ^ m) ≃ Fin (2 ^ (m + 1)) :=
    { toFun := Sum.elim (fun x => ⟨x.val, lt_pow_succ_of_lt x⟩)
                        (fun x => ⟨2 ^ m + x.val, add_lt_pow_succ x⟩)
      invFun := fun j => if hj : j.val < 2 ^ m then Sum.inl ⟨j.val, hj⟩
                         else Sum.inr ⟨j.val - 2 ^ m, sub_pow_lt_of_not_lt j hj⟩
      left_inv := fun s => by
        cases s with
        | inl x => simp [x.isLt]
        | inr x =>
          have hlt : ¬ (2 ^ m + x.val < 2 ^ m) := by omega
          simp [hlt]
      right_inv := fun j => by
        by_cases hj : j.val < 2 ^ m
        · simp [hj]
        · simp [hj, Fin.ext_iff]; omega }
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  rfl
@[scoped simp] theorem alpha1_nil_eq_one : alpha1 [] = 1 := by
  simp only [alpha1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, Zw.toComplex, Pi.smul_apply, smul_eq_mul]
  norm_num
noncomputable def sbmAmp : (m : ℕ) → ((d : Fin m) → Fin (2 ^ d.val) → List HSTGate) →
    Fin (2 ^ m) → ℂ
  | 0, _, _ => 1
  | m + 1, words, j =>
    let wordsL : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate :=
      fun d p => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩
    let wordsR : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate :=
      fun d p => words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩
    if hlt : j.val < 2 ^ m then
      alpha0 (words 0 0) * sbmAmp m wordsL ⟨j.val, hlt⟩
    else
      alpha1 (words 0 0) * sbmAmp m wordsR ⟨j.val - 2 ^ m, sub_pow_lt_of_not_lt j hlt⟩
theorem norm_sq_sum_sbmAmp (m : ℕ) (words : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate) :
    ∑ j : Fin (2 ^ m), ‖sbmAmp m words j‖ ^ 2 = 1 := by
  induction m with
  | zero => simp [sbmAmp]
  | succ m ih =>
    let wordsL : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate :=
      fun d p => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩
    let wordsR : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate :=
      fun d p => words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩
    have hL : (∑ x : Fin (2 ^ m), ‖sbmAmp (m + 1) words ⟨x.val, lt_pow_succ_of_lt x⟩‖ ^ 2) =
        ‖alpha0 (words 0 0)‖ ^ 2 * ∑ x : Fin (2 ^ m), ‖sbmAmp m wordsL x‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by simp [sbmAmp, wordsL, x.isLt, mul_pow]
    have hR : (∑ x : Fin (2 ^ m), ‖sbmAmp (m + 1) words ⟨2 ^ m + x.val, add_lt_pow_succ x⟩‖ ^ 2) =
        ‖alpha1 (words 0 0)‖ ^ 2 * ∑ x : Fin (2 ^ m), ‖sbmAmp m wordsR x‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp [sbmAmp, wordsR, show ¬ (2 ^ m + x.val < 2 ^ m) by omega, mul_pow]
    rw [fin_sum_pow_succ, hL, hR, ih wordsL, ih wordsR, mul_one, mul_one]
    exact norm_sq_alpha0_add_alpha1 (words 0 0)
def SbmTreeCertW : (m : ℕ) → ((d : Fin m) → Fin (2 ^ d.val) → List HSTGate) →
    (Fin (2 ^ m) → ℕ) → ℕ → ℕ → Prop
  | 0, _, W, S, _ => W 0 = S
  | m + 1, words, W, S, errNat =>
    let WL : Fin (2 ^ m) → ℕ := fun x => W ⟨x.val, lt_pow_succ_of_lt x⟩
    let WR : Fin (2 ^ m) → ℕ := fun x => W ⟨2 ^ m + x.val, add_lt_pow_succ x⟩
    let wordsL : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate :=
      fun d p => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩
    let wordsR : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate :=
      fun d p => words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩
    ∃ wL wR : ℕ, wL + wR = S ∧
      (if wL = 0 then words 0 0 = [] ∧ (∀ x, WL x = 0) ∧ SbmTreeCertW m wordsR WR wR errNat
       else if wR = 0 then words 0 0 = [.H] ∧ (∀ x, WR x = 0) ∧ SbmTreeCertW m wordsL WL wL errNat
       else ∃ eSplit eL eR : ℕ,
         eL + eR + 2 * eSplit ≤ errNat ∧
         |(S : ℝ) * ‖alpha1 (words 0 0)‖ ^ 2 - (wR : ℝ)| ≤ (eSplit : ℝ) / (2 : ℝ) ^ 48 ∧
         SbmTreeCertW m wordsL WL wL eL ∧
         SbmTreeCertW m wordsR WR wR eR)
scoped instance instLoc_ZeroAncillaUSPS3_2_instDecidableSbmTreeCertW (words : (d : Fin 0) →
  Fin (2 ^ d.val) → List HSTGate)
    (W : Fin (2 ^ 0) → ℕ) (S errNat : ℕ) : Decidable (SbmTreeCertW 0 words W S errNat) :=
  inferInstanceAs (Decidable (W 0 = S))
theorem scaled_half_sbm_bound {k : ℕ} (S wSub : ℕ) (a : ℝ) (p : Fin k → ℝ) (W : Fin k → ℕ)
    (B E0 : ℝ) (hp_nn : ∀ x, 0 ≤ p x) (hp_sum : ∑ x : Fin k, p x = 1)
    (ha_err : |(S : ℝ) * a - (wSub : ℝ)| ≤ E0)
    (hsub_err : ∑ x : Fin k, |(wSub : ℝ) * p x - (W x : ℝ)| ≤ B) :
    ∑ x : Fin k, |(S : ℝ) * (a * p x) - (W x : ℝ)| ≤ B + E0 := by
  have hterm : ∀ x : Fin k, |(S : ℝ) * (a * p x) - (W x : ℝ)| ≤
      |(wSub : ℝ) * p x - (W x : ℝ)| + |(S : ℝ) * a - (wSub : ℝ)| * p x := fun x => by
    have hid : (S : ℝ) * (a * p x) - (W x : ℝ) =
        ((wSub : ℝ) * p x - (W x : ℝ)) + ((S : ℝ) * a - (wSub : ℝ)) * p x := by ring
    rw [hid]
    exact (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg (hp_nn x)])
  calc ∑ x : Fin k, |(S : ℝ) * (a * p x) - (W x : ℝ)|
      ≤ ∑ x : Fin k, (|(wSub : ℝ) * p x - (W x : ℝ)| + |(S : ℝ) * a - (wSub : ℝ)| * p x) :=
          Finset.sum_le_sum fun x _ => hterm x
    _ = (∑ x : Fin k, |(wSub : ℝ) * p x - (W x : ℝ)|) +
          |(S : ℝ) * a - (wSub : ℝ)| * (∑ x : Fin k, p x) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ B + E0 * 1 := add_le_add hsub_err (by rw [hp_sum]; linarith)
    _ = B + E0 := by ring
theorem SbmTreeCertW.sound {m : ℕ} {words : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate}
    {W : Fin (2 ^ m) → ℕ} {S errNat : ℕ}
    (hcert : SbmTreeCertW m words W S errNat) (hS : 0 < S) :
    (∑ j : Fin (2 ^ m), W j = S) ∧
    (∀ j : Fin (2 ^ m), W j = 0 → sbmAmp m words j = 0) ∧
    (∑ j : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp m words j‖ ^ 2 - (W j : ℝ)| ≤
      (errNat : ℝ) / (2 : ℝ) ^ 48) := by
  induction m generalizing S errNat with
  | zero =>
    have hW0 : W 0 = S := hcert
    have hj0 : ∀ j : Fin (2 ^ 0), j = 0 := fun j => Fin.ext (by have := j.isLt; omega)
    refine ⟨?_, fun j hj => by rw [hj0 j] at hj; omega, ?_⟩
    · calc ∑ j : Fin (2 ^ 0), W j = ∑ _ : Fin (2 ^ 0), S :=
            Finset.sum_congr rfl fun j _ => by rw [hj0 j, hW0]
        _ = S := by simp
    · have hterm : ∀ j : Fin (2 ^ 0), |(S : ℝ) * ‖sbmAmp 0 words j‖ ^ 2 - (W j : ℝ)| = 0 :=
        fun j => by
        rw [hj0 j, hW0]
        simp [sbmAmp]
      rw [Finset.sum_eq_zero fun j _ => hterm j]
      positivity
  | succ m ih =>
    obtain ⟨wL, wR, hwsum, hbody⟩ := hcert
    let WL : Fin (2 ^ m) → ℕ := fun x => W ⟨x.val, lt_pow_succ_of_lt x⟩
    let WR : Fin (2 ^ m) → ℕ := fun x => W ⟨2 ^ m + x.val, add_lt_pow_succ x⟩
    let wordsL : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate :=
      fun d p => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩
    let wordsR : (d : Fin m) → Fin (2 ^ d.val) → List HSTGate :=
      fun d p => words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩
    have hampL (x : Fin (2 ^ m)) :
        ‖sbmAmp (m + 1) words ⟨x.val, lt_pow_succ_of_lt x⟩‖ ^ 2 =
          ‖alpha0 (words 0 0)‖ ^ 2 * ‖sbmAmp m wordsL x‖ ^ 2 := by
      simp [sbmAmp, wordsL, x.isLt, mul_pow]
    have hampR (x : Fin (2 ^ m)) :
        ‖sbmAmp (m + 1) words ⟨2 ^ m + x.val, add_lt_pow_succ x⟩‖ ^ 2 =
          ‖alpha1 (words 0 0)‖ ^ 2 * ‖sbmAmp m wordsR x‖ ^ 2 := by
      have hlt : ¬ (2 ^ m + x.val < 2 ^ m) := by omega
      simp [sbmAmp, wordsR, hlt, mul_pow]
    have hWR_idx (j : Fin (2 ^ (m + 1))) (hlt : ¬ j.val < 2 ^ m) :
        WR ⟨j.val - 2 ^ m, sub_pow_lt_of_not_lt j hlt⟩ = W j :=
      congrArg W (Fin.ext (Nat.add_sub_cancel' (Nat.le_of_not_lt hlt)))
    by_cases hwL : wL = 0
    · simp only [hwL, ↓reduceIte] at hbody
      rcases hbody with ⟨hw0, hWL0, hcertR⟩
      have hwR_eq : wR = S := by omega
      rcases ih hcertR (by omega) with ⟨hsumR, hzeroR, herrR⟩
      refine ⟨?_, fun j hj => ?_, ?_⟩
      · rw [fin_sum_pow_succ, Finset.sum_eq_zero fun x _ => hWL0 x, zero_add, hsumR, hwR_eq]
      · by_cases hlt : j.val < 2 ^ m
        · simp [sbmAmp, hlt, hw0]
        · simp only [sbmAmp, hlt, ↓reduceDIte, hzeroR _ ((hWR_idx j hlt).trans hj), mul_zero]
      · have hr_eq : (∑ x : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp (m + 1) words ⟨2 ^ m + x.val,
          add_lt_pow_succ x⟩‖ ^ 2 -
            (W ⟨2 ^ m + x.val, add_lt_pow_succ x⟩ : ℝ)|) =
            ∑ x : Fin (2 ^ m), |(wR : ℝ) * ‖sbmAmp m wordsR x‖ ^ 2 - (WR x : ℝ)| :=
          Finset.sum_congr rfl fun x _ => by simp [WR, hampR x, hw0, hwR_eq]
        rw [fin_sum_pow_succ, Finset.sum_eq_zero fun x _ =>
          by simp [hampL x, hw0, hWL0 x], zero_add, hr_eq]
        exact herrR
    · simp only [hwL, ↓reduceIte] at hbody
      by_cases hwR : wR = 0
      · simp only [hwR, ↓reduceIte] at hbody
        rcases hbody with ⟨hw0, hWR0, hcertL⟩
        have hwL_eq : wL = S := by omega
        rcases ih hcertL (by omega) with ⟨hsumL, hzeroL, herrL⟩
        refine ⟨?_, fun j hj => ?_, ?_⟩
        · rw [fin_sum_pow_succ, Finset.sum_eq_zero fun x _ => hWR0 x, add_zero, hsumL, hwL_eq]
        · by_cases hlt : j.val < 2 ^ m
          · simp only [sbmAmp, hlt, ↓reduceDIte, hzeroL ⟨j.val, hlt⟩ hj, mul_zero]
          · simp [sbmAmp, hlt, hw0]
        · have ha0 : ‖alpha0 [.H]‖ ^ 2 = 1 := by simpa using norm_sq_alpha0_add_alpha1 [.H]
          have hl_eq : (∑ x : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp (m + 1) words ⟨x.val,
            lt_pow_succ_of_lt x⟩‖ ^ 2 -
              (W ⟨x.val, lt_pow_succ_of_lt x⟩ : ℝ)|) =
              ∑ x : Fin (2 ^ m), |(wL : ℝ) * ‖sbmAmp m wordsL x‖ ^ 2 - (WL x : ℝ)| :=
            Finset.sum_congr rfl fun x _ => by simp [WL, hampL x, hw0, ha0, hwL_eq]
          have hr0 : (∑ x : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp (m + 1) words ⟨2 ^ m + x.val,
            add_lt_pow_succ x⟩‖ ^ 2 -
              (W ⟨2 ^ m + x.val, add_lt_pow_succ x⟩ : ℝ)|) = 0 :=
            Finset.sum_eq_zero fun x _ => by simp [hampR x, hw0, hWR0 x]
          rw [fin_sum_pow_succ, hl_eq, hr0, add_zero]
          exact herrL
      · simp only [hwR, ↓reduceIte] at hbody
        rcases hbody with ⟨eSplit, eL, eR, heSum, hsplit1, hcertL, hcertR⟩
        rcases ih hcertL (by omega) with ⟨hsumL, hzeroL, herrL⟩
        rcases ih hcertR (by omega) with ⟨hsumR, hzeroR, herrR⟩
        refine ⟨by rw [fin_sum_pow_succ, hsumL, hsumR, hwsum], fun j hj => ?_, ?_⟩
        · by_cases hlt : j.val < 2 ^ m
          · simp only [sbmAmp, hlt, ↓reduceDIte, hzeroL ⟨j.val, hlt⟩ hj, mul_zero]
          · simp only [sbmAmp, hlt, ↓reduceDIte, hzeroR _ ((hWR_idx j hlt).trans hj), mul_zero]
        · have hsplit0 : |(S : ℝ) * ‖alpha0 (words 0 0)‖ ^ 2 - (wL : ℝ)| ≤ (eSplit : ℝ) / (2 : ℝ) ^
            48 := by
            have hmul : (S : ℝ) * (‖alpha0 (words 0 0)‖ ^ 2 + ‖alpha1 (words 0 0)‖ ^ 2) = S := by
              rw [norm_sq_alpha0_add_alpha1, mul_one]
            have hwsumR : (wL : ℝ) + (wR : ℝ) = S := by exact_mod_cast hwsum
            rw [show (S : ℝ) * ‖alpha0 (words 0 0)‖ ^ 2 - wL = -((S : ℝ) * ‖alpha1 (words 0 0)‖ ^ 2
              - wR) by linarith, abs_neg]
            exact hsplit1
          have hbL := scaled_half_sbm_bound S wL (‖alpha0 (words 0 0)‖ ^ 2) (fun x =>
            ‖sbmAmp m wordsL x‖ ^ 2) WL
            ((eL : ℝ) / (2 : ℝ) ^ 48) ((eSplit : ℝ) / (2 : ℝ) ^ 48) (fun _ => by positivity)
              (norm_sq_sum_sbmAmp m wordsL) hsplit0 herrL
          have hbR := scaled_half_sbm_bound S wR (‖alpha1 (words 0 0)‖ ^ 2) (fun x =>
            ‖sbmAmp m wordsR x‖ ^ 2) WR
            ((eR : ℝ) / (2 : ℝ) ^ 48) ((eSplit : ℝ) / (2 : ℝ) ^ 48) (fun _ => by positivity)
              (norm_sq_sum_sbmAmp m wordsR) hsplit1 herrR
          have hl_eq : (∑ x : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp (m + 1) words ⟨x.val,
            lt_pow_succ_of_lt x⟩‖ ^ 2 -
              (W ⟨x.val, lt_pow_succ_of_lt x⟩ : ℝ)|) =
              ∑ x : Fin (2 ^ m), |(S : ℝ) * (‖alpha0 (words 0 0)‖ ^ 2 * ‖sbmAmp m wordsL x‖ ^ 2) -
                (WL x : ℝ)| :=
            Finset.sum_congr rfl fun x _ => by simp only [WL, hampL x]
          have hr_eq : (∑ x : Fin (2 ^ m), |(S : ℝ) * ‖sbmAmp (m + 1) words ⟨2 ^ m + x.val,
            add_lt_pow_succ x⟩‖ ^ 2 -
              (W ⟨2 ^ m + x.val, add_lt_pow_succ x⟩ : ℝ)|) =
              ∑ x : Fin (2 ^ m), |(S : ℝ) * (‖alpha1 (words 0 0)‖ ^ 2 * ‖sbmAmp m wordsR x‖ ^ 2) -
                (WR x : ℝ)| :=
            Finset.sum_congr rfl fun x _ => by simp only [WR, hampR x]
          rw [fin_sum_pow_succ, hl_eq, hr_eq]
          refine (add_le_add hbL hbR).trans ?_
          rw [show ((eL : ℝ) / (2 : ℝ) ^ 48 + (eSplit : ℝ) / (2 : ℝ) ^ 48) + ((eR : ℝ) / (2 : ℝ) ^
            48 + (eSplit : ℝ) / (2 : ℝ) ^ 48) =
            ((eL : ℝ) + (eR : ℝ) + 2 * (eSplit : ℝ)) / (2 : ℝ) ^ 48 by ring]
          exact div_le_div_of_nonneg_right (by exact_mod_cast heSum) (by positivity)
set_option exponentiation.threshold 512
def hstPoolWord_0 : List HSTGate := [.T, .S, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
    .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H]
def hstPoolWord_1 : List HSTGate := [.T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H]
def hstPoolWord_2 : List HSTGate := [.T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .H, .T, .H]
set_option maxRecDepth 4096
def hstPoolWord_3 : List HSTGate := [.T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S,
    .H, .T, .H, .T, .S, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H]
def hstPoolWord_4 : List HSTGate := [.T, .S, .S, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H]
def hstPoolWord_5 : List HSTGate := [.T, .S, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H]
def hstPoolWord_6 : List HSTGate := [.T, .S, .S, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .S, .H]
def hstPoolWord_7 : List HSTGate := [.T, .S, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .H]
def hstPoolWord_8 : List HSTGate := [.T, .S, .S, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .H]
def hstPoolWord_9 : List HSTGate := [.T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .S, .H]
def hstPoolWord_10 : List HSTGate := [.T, .S, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .H]
def hstPoolWord_11 : List HSTGate := [.T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .S, .H, .T, .S, .H]
def hstPoolWord_12 : List HSTGate := [.T, .S, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H,
    .T, .H]
def hstPoolWord_13 : List HSTGate := [.T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .S, .H]
def hstPoolWord_14 : List HSTGate := [.T, .S, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H]
def hstPoolWord_15 : List HSTGate := [.T, .S, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H]
def hstPoolWord_16 : List HSTGate := [.T, .S, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H]
def hstPoolWord_17 : List HSTGate := [.T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S,
    .H]
def hstPoolWord_18 : List HSTGate := [.T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H]
def hstPoolWord_19 : List HSTGate := [.T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S,
    .H]
def hstPoolWord_20 : List HSTGate := [.T, .S, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S,
    .H, .T, .S, .H]
def hstPoolWord_21 : List HSTGate := [.T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .H]
def hstPoolWord_22 : List HSTGate := [.T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H]
def hstPoolWord_23 : List HSTGate := [.T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H]
def hstPoolWord_24 : List HSTGate := [.T, .S, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H]
def hstPoolWord_25 : List HSTGate := [.T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .H]
def hstPoolWord_26 : List HSTGate := [.T, .S, .S, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H]
def hstPoolWord_27 : List HSTGate := [.T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .H]
def hstPoolWord_28 : List HSTGate := [.T, .S, .S, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H]
def hstPoolWord_29 : List HSTGate := [.T, .S, .S, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .S, .H]
def hstPoolWord_30 : List HSTGate := [.T, .S, .S, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H]
def hstPoolWord_31 : List HSTGate := [.T, .S, .S, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .H]
def hstPoolWord_32 : List HSTGate := [.T, .S, .S, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H]
def hstPoolWord_33 : List HSTGate := [.T, .S, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H]
def hstPoolWord_34 : List HSTGate := [.T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S,
    .H]
def hstPoolWord_35 : List HSTGate := [.T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H]
def hstPoolWord_36 : List HSTGate := [.T, .S, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T,
    .H, .T, .H, .T, .H]
def hstPoolWord_37 : List HSTGate := [.T, .S, .S, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T,
    .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T,
    .S, .H, .T, .H, .T, .S, .H, .T, .H]
def hstPoolWord_38 : List HSTGate := [.T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S,
    .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T,
    .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H, .T, .H]
def hstPoolWord_39 : List HSTGate := [.T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .H, .T, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H, .T, .H, .T, .S,
    .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .S, .H, .T, .H, .T, .S, .H,
    .T, .H, .T, .H, .T, .H, .T, .S, .H]
set_option maxRecDepth 512
abbrev isHeadS0FalseWord : List HSTGate := hstPoolWord_0
abbrev isHeadS0TrueWord : List HSTGate := hstPoolWord_1
def headShell64Weights : Fin (2 ^ 6) → ℕ := ![22715236741, 54760703790, 68771346192, 34208170224,
    17758053786, 65094721536, 57680531760, 23079413100, 39134725656, 9985603888, 11637692592,
    36895880832, 32885364672, 25160219880, 47008606944, 16818043920, 7969827852, 14841024192,
    10241616864, 1912648904, 3570015162, 15755590992, 15500146632, 14158274256, 21705959472,
    9196259184, 6221741640, 12058503648, 5701527120, 72, 1301750808, 9060312, 0, 0, 0, 2984867244,
    6959905536, 5964692856, 2692479240, 5415067488, 72, 129182784, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def headShell64Words : (d : Fin 6) → Fin (2 ^ d.val) → List HSTGate
  | ⟨0, _⟩, p => (![hstPoolWord_2] : Fin 1 → List HSTGate) p
  | ⟨1, _⟩, p => (![hstPoolWord_3, [.H]] : Fin 2 → List HSTGate) p
  | ⟨2, _⟩, p => (![hstPoolWord_4, hstPoolWord_5, hstPoolWord_6, [.H]] : Fin 4 → List HSTGate) p
  | ⟨3, _⟩, p =>
      (![hstPoolWord_7, hstPoolWord_8, hstPoolWord_9, hstPoolWord_10, hstPoolWord_11, [.H], [.H],
      [.H]] : Fin 8 → List HSTGate) p
  | ⟨4, _⟩, p =>
      (![hstPoolWord_12, hstPoolWord_13, hstPoolWord_14, hstPoolWord_15, hstPoolWord_16,
      hstPoolWord_17, hstPoolWord_18, hstPoolWord_19, [], hstPoolWord_20, [.H], [.H], [.H], [.H],
      [.H], [.H]] : Fin 16 → List HSTGate) p
  | ⟨5, _⟩, p =>
      (![hstPoolWord_21, hstPoolWord_22, hstPoolWord_23, hstPoolWord_24, hstPoolWord_25,
      hstPoolWord_26, hstPoolWord_27, hstPoolWord_28, hstPoolWord_29, hstPoolWord_30,
      hstPoolWord_31, hstPoolWord_32, hstPoolWord_33, hstPoolWord_34, hstPoolWord_35,
      hstPoolWord_36, [.H], [], hstPoolWord_37, hstPoolWord_38, hstPoolWord_39, [.H], [.H], [.H],
      [.H], [.H], [.H], [.H], [.H], [.H], [.H], [.H]] : Fin 32 → List HSTGate) p
private def sbmZero : (m : ℕ) → ((d : Fin m) → Fin (2 ^ d.val) → List HSTGate) →
    Fin (2 ^ m) → Bool
  | 0, _, _ => false
  | m + 1, words, j =>
    if hlt : j.val < 2 ^ m then
      decide (words 0 0 = []) ||
        sbmZero m (fun d p => words d.succ ⟨p.val, lt_pow_succ_of_lt p⟩) ⟨j.val, hlt⟩
    else
      decide (words 0 0 = [.H]) ||
        sbmZero m (fun d p => words d.succ ⟨2 ^ d.val + p.val, add_lt_pow_succ p⟩)
          ⟨j.val - 2 ^ m, sub_pow_lt_of_not_lt j hlt⟩
private theorem sbmAmp_eq_zero_of_sbmZero : ∀ (m : ℕ) (words) (j : Fin (2 ^ m)),
    sbmZero m words j = true → sbmAmp m words j = 0
  | 0, _, _, h => by simp [sbmZero] at h
  | m + 1, words, j, h => by
    by_cases hlt : j.val < 2 ^ m <;>
      simp only [sbmZero, hlt, ↓reduceDIte, Bool.or_eq_true, decide_eq_true_eq] at h <;>
      rcases h with hw | hrec
    · simp [sbmAmp, hlt, hw]
    · simp [sbmAmp, hlt, sbmAmp_eq_zero_of_sbmZero m _ _ hrec]
    · simp [sbmAmp, hlt, hw]
    · simp [sbmAmp, hlt, sbmAmp_eq_zero_of_sbmZero m _ _ hrec]
theorem headShell64_amp_zero (j : Fin (2 ^ 6)) (hj : headShell64Weights j = 0) : sbmAmp 6
    headShell64Words j = 0 :=
  sbmAmp_eq_zero_of_sbmZero 6 headShell64Words j
    ((by decide : ∀ i : Fin (2 ^ 6), headShell64Weights i = 0 →
      sbmZero 6 headShell64Words i = true) j hj)
def tailDp8Weights : Fin (2 ^ 3) → ℕ := ![771830103, 814177451, 814177451, 796552300, 814177451,
    796552300, 796552300, 784365019]
@[scoped simp] theorem alpha0_singleton_H : alpha0 [.H] = 1 := by
  simp only [alpha0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, Zw.toComplex,
    Pi.smul_apply, smul_eq_mul]
  norm_num
  rw [← Complex.star_def, MeasureBranchHadamardSem.star_sqrtHalf]
  linear_combination 2 * MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf
theorem wordMatrix2_append (u v : List HSTGate) :
    wordMatrix2 (u ++ v) = wordMatrix2 v * wordMatrix2 u := by
  unfold wordMatrix2
  rw [evalList_append u v matId (evalList u matId) rfl, evalList_mul_right]
def syllGates : Fin 4 → List HSTGate
  | ⟨0, _⟩ => [.T, .H]
  | ⟨1, _⟩ => [.T, .S, .H]
  | ⟨2, _⟩ => [.T, .S, .S, .H]
  | ⟨3, _⟩ => [.T, .S, .S, .S, .H]
def syllB0 : Fin 4 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => true
def syllB1 : Fin 4 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => true
  | ⟨3, _⟩ => false
noncomputable def syllPhase : Fin 4 → ℂ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => omega8
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => omega8
theorem syllPhase_mul_star (a : Fin 4) : syllPhase a * star (syllPhase a) = 1 := by
  have hw : omega8 * star omega8 = 1 := by
    rw [star_omega8, show omega8 * -omega8 ^ 3 = -(omega8 ^ 4) by ring, omega8_pow_four]
    norm_num
  fin_cases a
  · simp [syllPhase]
  · simpa [syllPhase] using hw
  · simp [syllPhase]
  · simpa [syllPhase] using hw
def oddsToHst : List (Fin 4) → List HSTGate
  | [] => []
  | a :: rest => syllGates a ++ oddsToHst rest
noncomputable def oddsPhase : List (Fin 4) → ℂ
  | [] => 1
  | a :: rest => oddsPhase rest * syllPhase a
theorem oddsPhase_mul_star (odds : List (Fin 4)) :
    oddsPhase odds * star (oddsPhase odds) = 1 := by
  induction odds with
  | nil => simp [oddsPhase]
  | cons a rest ih =>
    dsimp only [oddsPhase]
    rw [star_mul]
    linear_combination (syllPhase a * star (syllPhase a)) * ih + syllPhase_mul_star a
def pauliXPow (b : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if b = 0 then 1 else !![(0 : ℂ), 1; 1, 0]
def listXor {n : ℕ} : List (Wire n) → BitAssignment n → ZMod 2
  | [], _ => 0
  | u :: us, β => β u + listXor us β
def cnotList {n : ℕ} : List (Wire n) → Wire n → Circuit n
  | [], _ => Circuit.identity
  | c :: cs, t => cnotIf c t ;;ᶜ cnotList cs t
@[scoped simp] theorem count_toff_cnotList {n : ℕ} (cs : List (Wire n)) (t : Wire n) :
    (cnotList cs t).count PrimitiveGate.TOFF = 0 := by
  induction cs <;> simp [cnotList, *]
@[scoped simp] theorem count_t_cnotList {n : ℕ} (cs : List (Wire n)) (t : Wire n) :
    (cnotList cs t).count PrimitiveGate.T = 0 := by
  induction cs <;> simp [cnotList, *]
theorem cnotIf_mulVec_ket {n : ℕ} (c t : Wire n) (hct : c ≠ t) (β : BitAssignment n) :
    (cnotIf c t).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [cnotIf, dite_neg' hct, MeasureBranchHadamardSem.ket_CNOT]
theorem listXor_update_of_not_mem {n : ℕ} (cs : List (Wire n)) (q : Wire n) (v : ZMod 2)
    (β : BitAssignment n) (hdisj : ∀ u ∈ cs, u ≠ q) :
    listXor cs (Function.update β q v) = listXor cs β := by
  induction cs with
  | nil => rfl
  | cons u us ih =>
    have huq : u ≠ q := hdisj u (by simp)
    have hus : ∀ w ∈ us, w ≠ q := fun w hw => hdisj w (by simp [hw])
    simp only [listXor, Function.update_of_ne huq, ih hus]
theorem cnotList_mulVec_ket {n : ℕ} (cs : List (Wire n)) (t : Wire n)
    (hdisj : ∀ u ∈ cs, u ≠ t) (β : BitAssignment n) :
    (cnotList cs t).eval.1.mulVec (ket β) = ket (Function.update β t (β t + listXor cs β)) := by
  induction cs generalizing β with
  | nil =>
    simp only [cnotList, listXor, add_zero, Circuit.eval_identity, Submonoid.coe_one,
      Matrix.one_mulVec, upd_eq_self β t rfl]
  | cons c cs ih =>
    have hct : c ≠ t := hdisj c (by simp)
    have hcs : ∀ u ∈ cs, u ≠ t := fun u hu => hdisj u (by simp [hu])
    rw[cnotList, MeasureBranchHadamardSem.eval_seq_mulVec, cnotIf_mulVec_ket c t hct, ih hcs,
        Function.update_self, Function.update_idem, listXor_update_of_not_mem cs t _ β hcs]
    congr 2
    dsimp [listXor]
    ring
theorem ket_update_add_eq_pauliXPow_embed {n : ℕ} (t : Wire n) (b : ZMod 2)
    (β : BitAssignment n) : ket (Function.update β t (β t + b)) =
    ((QRegister.singleton t).embedMatrix (pauliXPow b)).mulVec (ket β) := by
  rcases MeasureBranchHadamardSem.bit_cases b with rfl | rfl
  · simp only [pauliXPow, ↓reduceIte, add_zero, upd_eq_self β t rfl,
      QRegister.embedMatrix_one, Matrix.one_mulVec]
  · simp only [pauliXPow, one_ne_zero, ↓reduceIte, singleton_embedMatrix_mulVec_ket]
    rcases MeasureBranchHadamardSem.bit_cases (β t) with ht0 | ht1
    · rw [ht0, ite_pos' rfl, zero_add]
      dsimp
      rw [zero_smul, one_smul, zero_add]
    · rw [ht1]
      simp only [one_ne_zero, ↓reduceIte, show (1 : ZMod 2) + 1 = 0 from rfl]
      dsimp
      rw [one_smul, zero_smul, add_zero]
theorem cnotList_mulVec_ket_embed {n : ℕ} (cs : List (Wire n)) (t : Wire n)
    (hdisj : ∀ u ∈ cs, u ≠ t) (β : BitAssignment n) : (cnotList cs t).eval.1.mulVec (ket β) =
    ((QRegister.singleton t).embedMatrix (pauliXPow (listXor cs β))).mulVec (ket β) := by
  rw [cnotList_mulVec_ket cs t hdisj β, ket_update_add_eq_pauliXPow_embed]
theorem mulVec_singleton_embedMatrix_of_ket {n : ℕ} (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (t : Wire n) (A B : Matrix (Fin 2) (Fin 2) ℂ) (β₁ β₂ : BitAssignment n) (ht : β₁ t = β₂ t)
    (hket : ∀ x : ZMod 2, M.mulVec (ket (Function.update β₁ t x)) = ((QRegister.singleton
    t).embedMatrix B).mulVec (ket (Function.update β₂ t x))) : M.mulVec
    (((QRegister.singleton t).embedMatrix A).mulVec (ket β₁)) =
    ((QRegister.singleton t).embedMatrix (B * A)).mulVec (ket β₂) := by
  rw[singleton_embedMatrix_mulVec_ket t A β₁, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hket 0, hket 1, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul,
      ← Matrix.mulVec_add, ht, ← singleton_embedMatrix_mulVec_ket t A β₂,
      Matrix.mulVec_mulVec, ← QRegister.embedMatrix_mul]
noncomputable def muxLayerMat (b0 b1 : ZMod 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliXPow b1 * wordMatrix2 [.H] * pauliXPow b0 * wordMatrix2 [.T] * pauliXPow b0
theorem muxLayerMat_eq_syll (a : Fin 4) : muxLayerMat (if syllB0 a then 1 else 0)
    (if syllB1 a then 1 else 0) = syllPhase a • wordMatrix2 (syllGates a) := by
  have h10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  fin_cases a <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    simp only [muxLayerMat, syllB0, syllB1, syllPhase, syllGates, pauliXPow, h10, ↓reduceIte,
      Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul] <;>
    dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, zwAdd, zwSub, zwMulI, zwMulW,
      Zw.toComplex, Pi.smul_apply, smul_eq_mul] <;>
    norm_num <;>
    ring_nf <;>
    (try rw [omega8_pow_four]; ring)
theorem muxLayerMat_unitary (b0 b1 : ZMod 2) :
    muxLayerMat b0 b1 * (muxLayerMat b0 b1)ᴴ = 1 := by
  obtain ⟨a, rfl, rfl⟩ : ∃ a : Fin 4,
      b0 = (if syllB0 a then 1 else 0) ∧ b1 = (if syllB1 a then 1 else 0) := by
    rcases MeasureBranchHadamardSem.bit_cases b0 with rfl | rfl <;>
      rcases MeasureBranchHadamardSem.bit_cases b1 with rfl | rfl
    exacts [⟨0, rfl, rfl⟩, ⟨2, rfl, rfl⟩, ⟨3, rfl, rfl⟩, ⟨1, rfl, rfl⟩]
  rw [muxLayerMat_eq_syll a, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, syllPhase_mul_star a, one_smul, wordMatrix2_unitary]
def b0Xor {n : ℕ} : List (Wire n × Fin 4) → BitAssignment n → ZMod 2
  | [], _ => 0
  | (u, a) :: us, β => (if syllB0 a then β u else 0) + b0Xor us β
def b1Xor {n : ℕ} : List (Wire n × Fin 4) → BitAssignment n → ZMod 2
  | [], _ => 0
  | (u, a) :: us, β => (if syllB1 a then β u else 0) + b1Xor us β
theorem listXor_filter_syllB0 {n : ℕ} (us : List (Wire n × Fin 4)) (β : BitAssignment n) :
    listXor ((us.filter (fun p => syllB0 p.2)).map Prod.fst) β = b0Xor us β := by
  induction us with
  | nil => rfl
  | cons p us ih =>
    rcases p with ⟨u, a⟩
    cases h : syllB0 a <;> simp [List.filter, h, listXor, b0Xor, ih]
theorem listXor_filter_syllB1 {n : ℕ} (us : List (Wire n × Fin 4)) (β : BitAssignment n) :
    listXor ((us.filter (fun p => syllB1 p.2)).map Prod.fst) β = b1Xor us β := by
  induction us with
  | nil => rfl
  | cons p us ih =>
    rcases p with ⟨u, a⟩
    cases h : syllB1 a <;> simp [List.filter, h, listXor, b1Xor, ih]
theorem b0Xor_update_of_not_mem {n : ℕ} (us : List (Wire n × Fin 4)) (q : Wire n) (v : ZMod 2)
    (β : BitAssignment n) (hdisj : ∀ u ∈ us.map Prod.fst, u ≠ q) :
    b0Xor us (Function.update β q v) = b0Xor us β := by
  rw [← listXor_filter_syllB0, ← listXor_filter_syllB0]
  exact listXor_update_of_not_mem _ q v β fun u hu => by
    rcases List.mem_map.mp hu with ⟨p, hp, rfl⟩
    exact hdisj p.1 (List.mem_map_of_mem (List.mem_filter.mp hp).1)
theorem b1Xor_update_of_not_mem {n : ℕ} (us : List (Wire n × Fin 4)) (q : Wire n) (v : ZMod 2)
    (β : BitAssignment n) (hdisj : ∀ u ∈ us.map Prod.fst, u ≠ q) :
    b1Xor us (Function.update β q v) = b1Xor us β := by
  rw [← listXor_filter_syllB1, ← listXor_filter_syllB1]
  exact listXor_update_of_not_mem _ q v β fun u hu => by
    rcases List.mem_map.mp hu with ⟨p, hp, rfl⟩
    exact hdisj p.1 (List.mem_map_of_mem (List.mem_filter.mp hp).1)
def cMuxLayer {n : ℕ} (us : List (Wire n × Fin 4)) (wPar t : Wire n) : Circuit n :=
  let b0Wires := (us.filter (fun p => syllB0 p.2)).map Prod.fst
  let b1Wires := (us.filter (fun p => syllB1 p.2)).map Prod.fst
  cnotList b0Wires wPar ;;ᶜ
    cnotIf wPar t ;;ᶜ
    Circuit.T t ;;ᶜ
    cnotIf wPar t ;;ᶜ
    cnotList b0Wires wPar ;;ᶜ
    Circuit.H t ;;ᶜ
    cnotList b1Wires t
@[scoped simp] theorem count_toff_cMuxLayer {n : ℕ} (us : List (Wire n × Fin 4))
    (wPar t : Wire n) : (cMuxLayer us wPar t).count PrimitiveGate.TOFF = 0 := by simp [cMuxLayer]
@[scoped simp] theorem count_t_cMuxLayer {n : ℕ} (us : List (Wire n × Fin 4))
    (wPar t : Wire n) : (cMuxLayer us wPar t).count PrimitiveGate.T = 1 := by simp [cMuxLayer]
theorem cMuxLayer_mulVec_ket_embed {n : ℕ} (us : List (Wire n × Fin 4)) (wPar t : Wire n)
    (hwpt : wPar ≠ t) (hdisj : ∀ u ∈ us.map Prod.fst, u ≠ wPar ∧ u ≠ t) (β : BitAssignment n)
    (hwPar : β wPar = 0) : (cMuxLayer us wPar t).eval.1.mulVec (ket β) = ((QRegister.singleton
    t).embedMatrix (muxLayerMat (b0Xor us β) (b1Xor us β))).mulVec (ket β) := by
  let b0Wires := (us.filter (fun p => syllB0 p.2)).map Prod.fst
  let b1Wires := (us.filter (fun p => syllB1 p.2)).map Prod.fst
  have hmem_flt {f : Fin 4 → Bool} {u : Wire n}
      (hu : u ∈ (us.filter (fun p => f p.2)).map Prod.fst) : u ≠ wPar ∧ u ≠ t := by
    rcases List.mem_map.mp hu with ⟨p, hp, rfl⟩
    exact hdisj p.1 (List.mem_map_of_mem (List.mem_filter.mp hp).1)
  have hb0_wPar : ∀ u ∈ b0Wires, u ≠ wPar := fun u hu => (hmem_flt hu).1
  have hb0_t : ∀ u ∈ b0Wires, u ≠ t := fun u hu => (hmem_flt hu).2
  have hb1_t : ∀ u ∈ b1Wires, u ≠ t := fun u hu => (hmem_flt hu).2
  let b0 := b0Xor us β
  let b1 := b1Xor us β
  let β₁ := Function.update β wPar b0
  have hβ₁_t : β₁ t = β t := Function.update_of_ne hwpt.symm b0 β
  have hβ₁_wPar (x : ZMod 2) : Function.update β₁ t x wPar = b0 := by
    dsimp [β₁]
    rw [Function.update_of_ne hwpt, Function.update_self]
  have hstep1 : (cnotList b0Wires wPar).eval.1.mulVec (ket β) = ket β₁ := by
    rw [cnotList_mulVec_ket b0Wires wPar hb0_wPar β, hwPar, zero_add, listXor_filter_syllB0]
  have hstep2 : (cnotIf wPar t).eval.1.mulVec (ket β₁) =
      ((QRegister.singleton t).embedMatrix (pauliXPow b0)).mulVec (ket β₁) := by
    rw [cnotIf_mulVec_ket wPar t hwpt β₁, show β₁ wPar = b0 from Function.update_self ..,
      ket_update_add_eq_pauliXPow_embed]
  have hstep3 (A : Matrix (Fin 2) (Fin 2) ℂ) :
      (Circuit.T t).eval.1.mulVec (((QRegister.singleton t).embedMatrix A).mulVec (ket β₁)) =
        ((QRegister.singleton t).embedMatrix (wordMatrix2 [.T] * A)).mulVec (ket β₁) := by
    have hT : (Circuit.T t).eval.1 = (QRegister.singleton t).embedMatrix (wordMatrix2 [.T]) :=
      hstGate_eval_eq .T t
    rw [hT, Matrix.mulVec_mulVec, ← QRegister.embedMatrix_mul]
  have hstep4 (A : Matrix (Fin 2) (Fin 2) ℂ) :
      (cnotIf wPar t).eval.1.mulVec (((QRegister.singleton t).embedMatrix A).mulVec (ket β₁)) =
        ((QRegister.singleton t).embedMatrix (pauliXPow b0 * A)).mulVec (ket β₁) :=
    mulVec_singleton_embedMatrix_of_ket _ t A (pauliXPow b0) β₁ β₁ rfl fun x => by
      rw [cnotIf_mulVec_ket wPar t hwpt, hβ₁_wPar x, ket_update_add_eq_pauliXPow_embed]
  have hadd_self_b0 : b0 + b0 = 0 := by
    rcases MeasureBranchHadamardSem.bit_cases b0 with h | h <;> rw [h] <;> rfl
  have hstep5 (A : Matrix (Fin 2) (Fin 2) ℂ) :
      (cnotList b0Wires wPar).eval.1.mulVec
        (((QRegister.singleton t).embedMatrix A).mulVec (ket β₁)) =
        ((QRegister.singleton t).embedMatrix (1 * A)).mulVec (ket β) := by
    refine mulVec_singleton_embedMatrix_of_ket _ t A 1 β₁ β hβ₁_t fun x => ?_
    rw [QRegister.embedMatrix_one, Matrix.one_mulVec,
      cnotList_mulVec_ket b0Wires wPar hb0_wPar, hβ₁_wPar x,
      listXor_update_of_not_mem b0Wires t x β₁ hb0_t,
      listXor_update_of_not_mem b0Wires wPar b0 β hb0_wPar, listXor_filter_syllB0]
    change ket (Function.update (Function.update β₁ t x) wPar (b0 + b0)) =
      ket (Function.update β t x)
    rw [hadd_self_b0]
    congr 1
    funext w
    rcases eq_or_ne w t with rfl | hwt
    · simp [hwpt.symm]
    · rcases eq_or_ne w wPar with rfl | hww
      · simp [hwt, hwPar]
      · simp [β₁, hwt, hww]
  have hstep6 (A : Matrix (Fin 2) (Fin 2) ℂ) :
      (Circuit.H t).eval.1.mulVec (((QRegister.singleton t).embedMatrix A).mulVec (ket β)) =
        ((QRegister.singleton t).embedMatrix (wordMatrix2 [.H] * A)).mulVec (ket β) := by
    have hH : (Circuit.H t).eval.1 = (QRegister.singleton t).embedMatrix (wordMatrix2 [.H]) :=
      hstGate_eval_eq .H t
    rw [hH, Matrix.mulVec_mulVec, ← QRegister.embedMatrix_mul]
  have hstep7 (A : Matrix (Fin 2) (Fin 2) ℂ) :
      (cnotList b1Wires t).eval.1.mulVec (((QRegister.singleton t).embedMatrix A).mulVec (ket β)) =
        ((QRegister.singleton t).embedMatrix (pauliXPow b1 * A)).mulVec (ket β) :=
    mulVec_singleton_embedMatrix_of_ket _ t A (pauliXPow b1) β β rfl fun x => by
      rw [cnotList_mulVec_ket_embed b1Wires t hb1_t,
        listXor_update_of_not_mem b1Wires t x β hb1_t, listXor_filter_syllB1]
  unfold cMuxLayer
  dsimp only
  change (cnotList b0Wires wPar ;;ᶜ cnotIf wPar t ;;ᶜ Circuit.T t ;;ᶜ cnotIf wPar t ;;ᶜ
      cnotList b0Wires wPar ;;ᶜ Circuit.H t ;;ᶜ cnotList b1Wires t).eval.1.mulVec (ket β) = _
  simp only [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [hstep1, hstep2, hstep3, hstep4, hstep5, Matrix.one_mul, hstep6, hstep7]
  dsimp only [muxLayerMat, b0, b1]
  simp only [Matrix.mul_assoc]
def cMuxWord {n : ℕ} : ℕ → List (Wire n × List (Fin 4)) → Wire n → Wire n → Circuit n
  | 0, _, _, _ => Circuit.identity
  | L + 1, branches, wPar, t =>
      cMuxLayer (branches.map (fun p => (p.1, p.2.headD 0))) wPar t ;;ᶜ
        cMuxWord L (branches.map (fun p => (p.1, p.2.tail))) wPar t
@[scoped simp] theorem count_toff_cMuxWord {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (wPar t : Wire n) : (cMuxWord L branches wPar t).count PrimitiveGate.TOFF = 0 := by
  induction L generalizing branches <;> simp [cMuxWord, *]
@[scoped simp] theorem count_t_cMuxWord {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (wPar t : Wire n) : (cMuxWord L branches wPar t).count PrimitiveGate.T = L := by
  induction L generalizing branches <;> simp [cMuxWord, Nat.add_comm, *]
noncomputable def muxWordMat {n : ℕ} :
    ℕ → List (Wire n × List (Fin 4)) → BitAssignment n → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _, _ => 1
  | L + 1, branches, β =>
      let us0 := branches.map (fun p => (p.1, p.2.headD 0))
      muxWordMat L (branches.map (fun p => (p.1, p.2.tail))) β *
        muxLayerMat (b0Xor us0 β) (b1Xor us0 β)
theorem muxWordMat_unitary {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (β : BitAssignment n) : muxWordMat L branches β * (muxWordMat L branches β)ᴴ = 1 := by
  induction L generalizing branches with
  | zero => simp [muxWordMat]
  | succ L ih =>
    dsimp only [muxWordMat]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (muxLayerMat _ _), muxLayerMat_unitary, Matrix.one_mul, ih]
theorem muxWordMat_update_of_not_mem {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (q : Wire n) (v : ZMod 2) (β : BitAssignment n)
    (hdisj : ∀ u ∈ branches.map Prod.fst, u ≠ q) :
    muxWordMat L branches (Function.update β q v) = muxWordMat L branches β := by
  induction L generalizing branches with
  | zero => rfl
  | succ L ih =>
    have hmap0 : (branches.map (fun p => (p.1, p.2.headD 0))).map Prod.fst =
        branches.map Prod.fst := by simp [List.map_map]
    have hmapT : (branches.map (fun p => (p.1, p.2.tail))).map Prod.fst =
        branches.map Prod.fst := by simp [List.map_map]
    dsimp only [muxWordMat]
    rw [ih _ (by simpa [hmapT] using hdisj),
      b0Xor_update_of_not_mem _ q v β (by simpa [hmap0] using hdisj),
      b1Xor_update_of_not_mem _ q v β (by simpa [hmap0] using hdisj)]
theorem cMuxWord_mulVec_ket_embed {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (wPar t : Wire n) (hwpt : wPar ≠ t)
    (hdisj : ∀ u ∈ branches.map Prod.fst, u ≠ wPar ∧ u ≠ t) (β : BitAssignment n)
    (hwPar : β wPar = 0) : (cMuxWord L branches wPar t).eval.1.mulVec (ket β) =
    ((QRegister.singleton t).embedMatrix (muxWordMat L branches β)).mulVec (ket β) := by
  induction L generalizing branches β with
  | zero =>
    simp [cMuxWord, muxWordMat, QRegister.embedMatrix_one]
  | succ L ih =>
    have hmap0 : (branches.map (fun p => (p.1, p.2.headD 0))).map Prod.fst =
        branches.map Prod.fst := by simp [List.map_map]
    have hmapT : (branches.map (fun p => (p.1, p.2.tail))).map Prod.fst =
        branches.map Prod.fst := by simp [List.map_map]
    have hdisj_t : ∀ u ∈ (branches.map (fun p => (p.1, p.2.tail))).map Prod.fst, u ≠ t :=
      fun u hu => (hdisj u (by simpa [hmapT] using hu)).2
    rw [cMuxWord, MeasureBranchHadamardSem.eval_seq_mulVec,
      cMuxLayer_mulVec_ket_embed _ wPar t hwpt (by simpa [hmap0] using hdisj) β hwPar]
    let us0 := branches.map (fun p => (p.1, p.2.headD 0))
    let brT := branches.map (fun p => (p.1, p.2.tail))
    refine mulVec_singleton_embedMatrix_of_ket (cMuxWord L brT wPar t).eval.1 t
      (muxLayerMat (b0Xor us0 β) (b1Xor us0 β)) (muxWordMat L brT β) β β rfl (fun x => ?_)
    have hwPar_x : Function.update β t x wPar = 0 := by
      rw [Function.update_of_ne hwpt, hwPar]
    have hdisj_brT : ∀ u ∈ brT.map Prod.fst, u ≠ wPar ∧ u ≠ t := by
      dsimp only [brT]
      rwa [hmapT]
    rw [ih brT hdisj_brT (Function.update β t x) hwPar_x,
      muxWordMat_update_of_not_mem L brT t x β hdisj_t]
theorem inverse_mulVec_ket_of_embed_unitary {n : ℕ} (C : Circuit n) (t : Wire n)
    (U : Matrix (Fin 2) (Fin 2) ℂ) (β : BitAssignment n) (hU : U * Uᴴ = 1) (hfwd : ∀ x : ZMod
    2, C.eval.1.mulVec (ket (Function.update β t x)) = ((QRegister.singleton t).embedMatrix
    U).mulVec (ket (Function.update β t x))) : C.inverse.eval.1.mulVec (ket β) =
    ((QRegister.singleton t).embedMatrix (Uᴴ)).mulVec (ket β) := by
  let ψ := ((QRegister.singleton t).embedMatrix (Uᴴ)).mulVec (ket β)
  have hCψ : C.eval.1.mulVec ψ = ket β := by
    rw [mulVec_singleton_embedMatrix_of_ket C.eval.1 t (Uᴴ) U β β rfl hfwd,
      hU, QRegister.embedMatrix_one, Matrix.one_mulVec]
  have hinv : C.inverse.eval.1 * C.eval.1 = 1 := by
    rw [Circuit.eval_inverse]
    exact congrArg Subtype.val (inv_mul_cancel C.eval)
  nth_rw 1 [← hCψ]
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
def PmSplitDisj {n : ℕ} (branchWires flipWires : List (Wire n)) (wPar t : Wire n) : Prop :=
    wPar ≠ t ∧ (∀ u ∈ branchWires, u ≠ wPar ∧ u ≠ t) ∧ (∀ u ∈ flipWires, u ≠ wPar ∧ u ≠ t)
scoped instance instLoc_ZeroAncillaUSPS3_3_instDecidablePmSplitDisj {n : ℕ} (branchWires flipWires :
  List (Wire n))
    (wPar t : Wire n) : Decidable (PmSplitDisj branchWires flipWires wPar t) := by
  unfold PmSplitDisj; infer_instance
def cPmSplit {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (flips : List (Wire n)) (wPar t : Wire n) : Circuit n :=
  (cMuxWord L branches wPar t).inverse ;;ᶜ
    cnotList (branches.map Prod.fst) t ;;ᶜ
    cMuxWord L branches wPar t ;;ᶜ
    cnotList flips t
@[scoped simp] theorem count_toff_cPmSplit {n : ℕ} (L : ℕ)
    (branches : List (Wire n × List (Fin 4))) (flips : List (Wire n)) (wPar t : Wire n) :
    (cPmSplit L branches flips wPar t).count PrimitiveGate.TOFF = 0 := by simp [cPmSplit]
@[scoped simp] theorem count_t_cPmSplit {n : ℕ} (L : ℕ)
    (branches : List (Wire n × List (Fin 4))) (flips : List (Wire n)) (wPar t : Wire n) :
    (cPmSplit L branches flips wPar t).count PrimitiveGate.T = 2 * L := by simp [cPmSplit, two_mul]
noncomputable def pmSplitMat {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (flips : List (Wire n)) (β : BitAssignment n) : Matrix (Fin 2) (Fin 2) ℂ := pauliXPow
    (listXor flips β) * muxWordMat L branches β * pauliXPow
    (listXor (branches.map Prod.fst) β) * (muxWordMat L branches β)ᴴ
theorem cPmSplit_mulVec_ket_embed {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (flips : List (Wire n)) (wPar t : Wire n)
    (hdisj : PmSplitDisj (branches.map Prod.fst) flips wPar t) (β : BitAssignment n)
    (hwPar : β wPar = 0) : (cPmSplit L branches flips wPar t).eval.1.mulVec (ket β) =
    ((QRegister.singleton t).embedMatrix (pmSplitMat L branches flips β)).mulVec (ket β) := by
  rcases hdisj with ⟨hwpt, hbr, hfl⟩
  have hbr_t : ∀ u ∈ branches.map Prod.fst, u ≠ t := fun u hu => (hbr u hu).2
  have hfl_t : ∀ u ∈ flips, u ≠ t := fun u hu => (hfl u hu).2
  have hinv : (cMuxWord L branches wPar t).inverse.eval.1.mulVec (ket β) =
      ((QRegister.singleton t).embedMatrix ((muxWordMat L branches β)ᴴ)).mulVec (ket β) := by
    refine inverse_mulVec_ket_of_embed_unitary _ t (muxWordMat L branches β) β
      (muxWordMat_unitary L branches β) (fun x => ?_)
    have hwPar_x : Function.update β t x wPar = 0 := by
      rw [Function.update_of_ne hwpt, hwPar]
    rw [cMuxWord_mulVec_ket_embed L branches wPar t hwpt hbr _ hwPar_x,
      muxWordMat_update_of_not_mem L branches t x β hbr_t]
  have hmid (A : Matrix (Fin 2) (Fin 2) ℂ) :
      (cnotList (branches.map Prod.fst) t).eval.1.mulVec
      (((QRegister.singleton t).embedMatrix A).mulVec (ket β)) = ((QRegister.singleton
      t).embedMatrix (pauliXPow (listXor (branches.map Prod.fst) β) * A)).mulVec (ket β) := by
    refine mulVec_singleton_embedMatrix_of_ket (cnotList (branches.map Prod.fst) t).eval.1 t A
      (pauliXPow (listXor (branches.map Prod.fst) β)) β β rfl (fun x => ?_)
    rw[cnotList_mulVec_ket_embed _ t hbr_t, listXor_update_of_not_mem _ t x β hbr_t]
  have hfwd (A : Matrix (Fin 2) (Fin 2) ℂ) : (cMuxWord L branches wPar t).eval.1.mulVec
      (((QRegister.singleton t).embedMatrix A).mulVec (ket β)) = ((QRegister.singleton
      t).embedMatrix (muxWordMat L branches β * A)).mulVec (ket β) := by
    refine mulVec_singleton_embedMatrix_of_ket (cMuxWord L branches wPar t).eval.1 t A
      (muxWordMat L branches β) β β rfl (fun x => ?_)
    have hwPar_x : Function.update β t x wPar = 0 := by
      rw [Function.update_of_ne hwpt, hwPar]
    rw [cMuxWord_mulVec_ket_embed L branches wPar t hwpt hbr _ hwPar_x,
      muxWordMat_update_of_not_mem L branches t x β hbr_t]
  have hflip (A : Matrix (Fin 2) (Fin 2) ℂ) : (cnotList flips t).eval.1.mulVec
      (((QRegister.singleton t).embedMatrix A).mulVec (ket β)) = ((QRegister.singleton
      t).embedMatrix (pauliXPow (listXor flips β) * A)).mulVec (ket β) := by
    refine mulVec_singleton_embedMatrix_of_ket (cnotList flips t).eval.1 t A
      (pauliXPow (listXor flips β)) β β rfl (fun x => ?_)
    rw[cnotList_mulVec_ket_embed _ t hfl_t, listXor_update_of_not_mem _ t x β hfl_t]
  unfold cPmSplit
  simp only [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [hinv, hmid, hfwd, hflip]
  dsimp only [pmSplitMat]
  simp only [Matrix.mul_assoc]
theorem listXor_filter_one {n : ℕ} (us : List (Wire n)) (β : BitAssignment n) :
    listXor (us.filter (fun u => β u == 1)) β = listXor us β := by
  have h01 : ((0 : ZMod 2) == 1) = false := rfl
  induction us with
  | nil => rfl
  | cons u us ih =>
    rcases MeasureBranchHadamardSem.bit_cases (β u) with h | h
    · simp [List.filter, listXor, h, ih, h01]
    · simp [List.filter, listXor, h, ih]
theorem filter_one_map_fst {n : ℕ} {α : Type*} (xs : List (Wire n × α)) (β : BitAssignment n) :
    (xs.filter (fun p => β p.1 == 1)).map Prod.fst =
      (xs.map Prod.fst).filter (fun u => β u == 1) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    cases h : (β p.1 == 1) <;> simp [List.filter, h, ih]
theorem b0Xor_filter_one {n : ℕ} (us : List (Wire n × Fin 4)) (β : BitAssignment n) :
    b0Xor (us.filter (fun p => β p.1 == 1)) β = b0Xor us β := by
  rw [← listXor_filter_syllB0, ← listXor_filter_syllB0, List.filter_comm,
    filter_one_map_fst, listXor_filter_one]
theorem b1Xor_filter_one {n : ℕ} (us : List (Wire n × Fin 4)) (β : BitAssignment n) :
    b1Xor (us.filter (fun p => β p.1 == 1)) β = b1Xor us β := by
  rw [← listXor_filter_syllB1, ← listXor_filter_syllB1, List.filter_comm,
    filter_one_map_fst, listXor_filter_one]
theorem filter_one_map_snd {n : ℕ} {α γ : Type*} (f : α → γ) (xs : List (Wire n × α))
    (β : BitAssignment n) : (xs.map (fun p => (p.1, f p.2))).filter (fun p => β p.1 == 1) =
    (xs.filter (fun p => β p.1 == 1)).map (fun p => (p.1, f p.2)) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    cases h : (β p.1 == 1) <;> simp [List.filter, h, ih]
theorem muxWordMat_filter_one {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (β : BitAssignment n) :
    muxWordMat L (branches.filter (fun p => β p.1 == 1)) β = muxWordMat L branches β := by
  induction L generalizing branches with
  | zero => rfl
  | succ L ih =>
    dsimp only [muxWordMat]
    rw [← filter_one_map_snd List.tail branches β, ih,
      ← b0Xor_filter_one (branches.map (fun p => (p.1, p.2.headD 0))) β,
      ← b1Xor_filter_one (branches.map (fun p => (p.1, p.2.headD 0))) β,
      filter_one_map_snd (fun l => l.headD 0) branches β]
theorem pmSplitMat_filter_one {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (flips : List (Wire n)) (β : BitAssignment n) : pmSplitMat L
    (branches.filter (fun p => β p.1 == 1)) (flips.filter (fun u => β u == 1)) β = pmSplitMat
    L branches flips β := by
  dsimp only [pmSplitMat]
  rw [listXor_filter_one flips β, muxWordMat_filter_one L branches β,
    filter_one_map_fst branches β, listXor_filter_one (branches.map Prod.fst) β]
theorem muxWordMat_singleton_one {n : ℕ} (u : Wire n) (odds : List (Fin 4))
    (β : BitAssignment n) (hu : β u = 1) : muxWordMat odds.length [(u, odds)] β = oddsPhase
    odds • wordMatrix2 (oddsToHst odds) := by
  induction odds with
  | nil =>
    simp only [List.length_nil, muxWordMat, oddsPhase, oddsToHst, one_smul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      dsimp [wordMatrix2, evalList, matId, Mat2Zw.toMatrix, Zw.toComplex,
        Pi.smul_apply, smul_eq_mul] <;>
      norm_num
  | cons a rest ih =>
    simp only [List.length_cons, muxWordMat, List.map, List.headD_cons, List.tail_cons,
      b0Xor, b1Xor, hu, add_zero]
    rw [ih, muxLayerMat_eq_syll a, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      oddsToHst, wordMatrix2_append, oddsPhase]
theorem cPmSplit_mulVec_ket_zero {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (flips : List (Wire n)) (wPar t : Wire n)
    (hdisj : PmSplitDisj (branches.map Prod.fst) flips wPar t) (β : BitAssignment n)
    (hwPar : β wPar = 0) (hbr : branches.filter (fun p => β p.1 == 1) = [])
    (hfl : flips.filter (fun u => β u == 1) = []) :
    (cPmSplit L branches flips wPar t).eval.1.mulVec (ket β) = ket β := by
  rw [cPmSplit_mulVec_ket_embed L branches flips wPar t hdisj β hwPar,
    ← pmSplitMat_filter_one L branches flips β, hbr, hfl]
  have hmat : pmSplitMat L ([] : List (Wire n × List (Fin 4))) ([] : List (Wire n)) β = 1 := by
    dsimp [pmSplitMat, listXor, pauliXPow]
    rw [Matrix.one_mul, Matrix.mul_one, muxWordMat_unitary]
  rw [hmat, QRegister.embedMatrix_one, Matrix.one_mulVec]
theorem cPmSplit_mulVec_ket_flip {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (flips : List (Wire n)) (wPar t u : Wire n)
    (hdisj : PmSplitDisj (branches.map Prod.fst) flips wPar t) (β : BitAssignment n)
    (hwPar : β wPar = 0) (ht : β t = 0) (hbr : branches.filter (fun p => β p.1 == 1) = [])
    (hfl : flips.filter (fun w => β w == 1) = [u]) :
    (cPmSplit L branches flips wPar t).eval.1.mulVec (ket β) = ket (Function.update β t 1) := by
  have hu_mem : u ∈ flips.filter (fun w => β w == 1) := by simp [hfl]
  have hu : β u = 1 := ((List.mem_filter.mp hu_mem).2 |> beq_iff_eq.mp)
  rw [cPmSplit_mulVec_ket_embed L branches flips wPar t hdisj β hwPar,
    ← pmSplitMat_filter_one L branches flips β, hbr, hfl]
  have hmat : pmSplitMat L ([] : List (Wire n × List (Fin 4))) [u] β = !![(0 : ℂ), 1; 1, 0] := by
    dsimp [pmSplitMat, List.map, listXor]
    rw [hu, add_zero]
    simp only [pauliXPow, ↓reduceIte, one_ne_zero, Matrix.mul_one, Matrix.mul_assoc,
      muxWordMat_unitary]
  rw [hmat, singleton_embedMatrix_mulVec_ket, ite_pos' ht]
  dsimp
  rw [zero_smul, one_smul, zero_add]
theorem cPmSplit_mulVec_ket_onehot {n : ℕ} (L : ℕ) (branches : List (Wire n × List (Fin 4)))
    (flips : List (Wire n)) (wPar t u : Wire n) (odds : List (Fin 4))
    (hdisj : PmSplitDisj (branches.map Prod.fst) flips wPar t) (hlen : odds.length = L)
    (β : BitAssignment n) (hwPar : β wPar = 0) (ht : β t = 0)
    (hbr : branches.filter (fun p => β p.1 == 1) = [(u, odds)])
    (hfl : flips.filter (fun w => β w == 1) = []) :
    (cPmSplit L branches flips wPar t).eval.1.mulVec (ket β) = alpha0 (oddsToHst odds) • ket β
    + alpha1 (oddsToHst odds) • ket (Function.update β t 1) := by
  subst hlen
  have hu_mem : (u, odds) ∈ branches.filter (fun p => β p.1 == 1) := by simp [hbr]
  have hu : β u = 1 := ((List.mem_filter.mp hu_mem).2 |> beq_iff_eq.mp)
  rw [cPmSplit_mulVec_ket_embed odds.length branches flips wPar t hdisj β hwPar,
    ← pmSplitMat_filter_one odds.length branches flips β, hbr, hfl]
  have hmat : pmSplitMat odds.length [(u, odds)] ([] : List (Wire n)) β =
      wordMatrix2 (oddsToHst odds) * !![(0 : ℂ), 1; 1, 0] * (wordMatrix2 (oddsToHst odds))ᴴ := by
    dsimp [pmSplitMat, List.map, listXor]
    rw [hu, add_zero, muxWordMat_singleton_one u odds β hu]
    simp only [pauliXPow, ↓reduceIte, one_ne_zero, Matrix.one_mul, Matrix.conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [mul_comm (star (oddsPhase odds)), oddsPhase_mul_star, one_smul]
  rw [hmat, singleton_embedMatrix_mulVec_ket, ite_pos' ht, upd_eq_self β t ht]
  rfl
set_option maxRecDepth 4096
def hstPoolOdds_0 : List (Fin 4) := [2, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_0 : hstPoolOdds_0.length = 44 := rfl
theorem oddsToHst_hstPoolOdds_0 : oddsToHst hstPoolOdds_0 = hstPoolWord_0 := rfl
def hstPoolOdds_1 : List (Fin 4) := [1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0,
    0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1]
@[scoped simp] theorem length_hstPoolOdds_1 : hstPoolOdds_1.length = 44 := rfl
theorem oddsToHst_hstPoolOdds_1 : oddsToHst hstPoolOdds_1 = hstPoolWord_1 := rfl
def hstPoolOdds_2 : List (Fin 4) := [0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 1, 2, 1, 0,
    0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_2 : hstPoolOdds_2.length = 38 := rfl
theorem oddsToHst_hstPoolOdds_2 : oddsToHst hstPoolOdds_2 = hstPoolWord_2 := rfl
def hstPoolOdds_3 : List (Fin 4) := [0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 2, 1, 1,
    1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_3 : hstPoolOdds_3.length = 40 := rfl
theorem oddsToHst_hstPoolOdds_3 : oddsToHst hstPoolOdds_3 = hstPoolWord_3 := rfl
def hstPoolOdds_4 : List (Fin 4) := [3, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0]
@[scoped simp] theorem length_hstPoolOdds_4 : hstPoolOdds_4.length = 44 := rfl
theorem oddsToHst_hstPoolOdds_4 : oddsToHst hstPoolOdds_4 = hstPoolWord_4 := rfl
def hstPoolOdds_5 : List (Fin 4) := [2, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1,
    1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_5 : hstPoolOdds_5.length = 44 := rfl
theorem oddsToHst_hstPoolOdds_5 : oddsToHst hstPoolOdds_5 = hstPoolWord_5 := rfl
def hstPoolOdds_6 : List (Fin 4) := [3, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_6 : hstPoolOdds_6.length = 44 := rfl
theorem oddsToHst_hstPoolOdds_6 : oddsToHst hstPoolOdds_6 = hstPoolWord_6 := rfl
def hstPoolOdds_7 : List (Fin 4) := [2, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1,
    0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0]
@[scoped simp] theorem length_hstPoolOdds_7 : hstPoolOdds_7.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_7 : oddsToHst hstPoolOdds_7 = hstPoolWord_7 := rfl
def hstPoolOdds_8 : List (Fin 4) := [3, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0,
    1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0]
@[scoped simp] theorem length_hstPoolOdds_8 : hstPoolOdds_8.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_8 : oddsToHst hstPoolOdds_8 = hstPoolWord_8 := rfl
def hstPoolOdds_9 : List (Fin 4) := [0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1,
    0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_9 : hstPoolOdds_9.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_9 : oddsToHst hstPoolOdds_9 = hstPoolWord_9 := rfl
def hstPoolOdds_10 : List (Fin 4) := [2, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1,
    0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_10 : hstPoolOdds_10.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_10 : oddsToHst hstPoolOdds_10 = hstPoolWord_10 := rfl
def hstPoolOdds_11 : List (Fin 4) := [0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0,
    1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1]
@[scoped simp] theorem length_hstPoolOdds_11 : hstPoolOdds_11.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_11 : oddsToHst hstPoolOdds_11 = hstPoolWord_11 := rfl
def hstPoolOdds_12 : List (Fin 4) := [2, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0,
    1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_12 : hstPoolOdds_12.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_12 : oddsToHst hstPoolOdds_12 = hstPoolWord_12 := rfl
def hstPoolOdds_13 : List (Fin 4) := [0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0,
    0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_13 : hstPoolOdds_13.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_13 : oddsToHst hstPoolOdds_13 = hstPoolWord_13 := rfl
def hstPoolOdds_14 : List (Fin 4) := [2, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1,
    1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_14 : hstPoolOdds_14.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_14 : oddsToHst hstPoolOdds_14 = hstPoolWord_14 := rfl
def hstPoolOdds_15 : List (Fin 4) := [2, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0,
    0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_15 : hstPoolOdds_15.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_15 : oddsToHst hstPoolOdds_15 = hstPoolWord_15 := rfl
def hstPoolOdds_16 : List (Fin 4) := [2, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0]
@[scoped simp] theorem length_hstPoolOdds_16 : hstPoolOdds_16.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_16 : oddsToHst hstPoolOdds_16 = hstPoolWord_16 := rfl
def hstPoolOdds_17 : List (Fin 4) := [1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0,
    0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_17 : hstPoolOdds_17.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_17 : oddsToHst hstPoolOdds_17 = hstPoolWord_17 := rfl
def hstPoolOdds_18 : List (Fin 4) := [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_18 : hstPoolOdds_18.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_18 : oddsToHst hstPoolOdds_18 = hstPoolWord_18 := rfl
def hstPoolOdds_19 : List (Fin 4) := [0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_19 : hstPoolOdds_19.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_19 : oddsToHst hstPoolOdds_19 = hstPoolWord_19 := rfl
def hstPoolOdds_20 : List (Fin 4) := [2, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1,
    0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1]
@[scoped simp] theorem length_hstPoolOdds_20 : hstPoolOdds_20.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_20 : oddsToHst hstPoolOdds_20 = hstPoolWord_20 := rfl
def hstPoolOdds_21 : List (Fin 4) := [0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1,
    0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0]
@[scoped simp] theorem length_hstPoolOdds_21 : hstPoolOdds_21.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_21 : oddsToHst hstPoolOdds_21 = hstPoolWord_21 := rfl
def hstPoolOdds_22 : List (Fin 4) := [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1,
    0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_22 : hstPoolOdds_22.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_22 : oddsToHst hstPoolOdds_22 = hstPoolWord_22 := rfl
def hstPoolOdds_23 : List (Fin 4) := [1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0,
    1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_23 : hstPoolOdds_23.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_23 : oddsToHst hstPoolOdds_23 = hstPoolWord_23 := rfl
def hstPoolOdds_24 : List (Fin 4) := [2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_24 : hstPoolOdds_24.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_24 : oddsToHst hstPoolOdds_24 = hstPoolWord_24 := rfl
def hstPoolOdds_25 : List (Fin 4) := [1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1,
    0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0]
@[scoped simp] theorem length_hstPoolOdds_25 : hstPoolOdds_25.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_25 : oddsToHst hstPoolOdds_25 = hstPoolWord_25 := rfl
def hstPoolOdds_26 : List (Fin 4) := [3, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]
@[scoped simp] theorem length_hstPoolOdds_26 : hstPoolOdds_26.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_26 : oddsToHst hstPoolOdds_26 = hstPoolWord_26 := rfl
def hstPoolOdds_27 : List (Fin 4) := [0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0,
    0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]
@[scoped simp] theorem length_hstPoolOdds_27 : hstPoolOdds_27.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_27 : oddsToHst hstPoolOdds_27 = hstPoolWord_27 := rfl
def hstPoolOdds_28 : List (Fin 4) := [3, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_28 : hstPoolOdds_28.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_28 : oddsToHst hstPoolOdds_28 = hstPoolWord_28 := rfl
def hstPoolOdds_29 : List (Fin 4) := [3, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0,
    0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1]
@[scoped simp] theorem length_hstPoolOdds_29 : hstPoolOdds_29.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_29 : oddsToHst hstPoolOdds_29 = hstPoolWord_29 := rfl
def hstPoolOdds_30 : List (Fin 4) := [3, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1]
@[scoped simp] theorem length_hstPoolOdds_30 : hstPoolOdds_30.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_30 : oddsToHst hstPoolOdds_30 = hstPoolWord_30 := rfl
def hstPoolOdds_31 : List (Fin 4) := [3, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_31 : hstPoolOdds_31.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_31 : oddsToHst hstPoolOdds_31 = hstPoolWord_31 := rfl
def hstPoolOdds_32 : List (Fin 4) := [3, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1,
    0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_32 : hstPoolOdds_32.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_32 : oddsToHst hstPoolOdds_32 = hstPoolWord_32 := rfl
def hstPoolOdds_33 : List (Fin 4) := [2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
    0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_33 : hstPoolOdds_33.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_33 : oddsToHst hstPoolOdds_33 = hstPoolWord_33 := rfl
def hstPoolOdds_34 : List (Fin 4) := [1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1,
    0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_34 : hstPoolOdds_34.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_34 : oddsToHst hstPoolOdds_34 = hstPoolWord_34 := rfl
def hstPoolOdds_35 : List (Fin 4) := [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0,
    1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1]
@[scoped simp] theorem length_hstPoolOdds_35 : hstPoolOdds_35.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_35 : oddsToHst hstPoolOdds_35 = hstPoolWord_35 := rfl
def hstPoolOdds_36 : List (Fin 4) := [2, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_36 : hstPoolOdds_36.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_36 : oddsToHst hstPoolOdds_36 = hstPoolWord_36 := rfl
def hstPoolOdds_37 : List (Fin 4) := [3, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0,
    1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]
@[scoped simp] theorem length_hstPoolOdds_37 : hstPoolOdds_37.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_37 : oddsToHst hstPoolOdds_37 = hstPoolWord_37 := rfl
def hstPoolOdds_38 : List (Fin 4) := [1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1,
    0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]
@[scoped simp] theorem length_hstPoolOdds_38 : hstPoolOdds_38.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_38 : oddsToHst hstPoolOdds_38 = hstPoolWord_38 := rfl
def hstPoolOdds_39 : List (Fin 4) := [0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1]
@[scoped simp] theorem length_hstPoolOdds_39 : hstPoolOdds_39.length = 47 := rfl
theorem oddsToHst_hstPoolOdds_39 : oddsToHst hstPoolOdds_39 = hstPoolWord_39 := rfl
set_option maxRecDepth 512
abbrev isHeadS0FalseOdds : List (Fin 4) := hstPoolOdds_0
abbrev isHeadS0TrueOdds : List (Fin 4) := hstPoolOdds_1
set_option exponentiation.threshold 256
end ZeroAncillaUSPS3
end
end ModZeroAncillaUSPS3
end ZeroAncillaUSPS3
end
set_option exponentiation.threshold 256
end ZeroAncillaUSPS3Aux

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
