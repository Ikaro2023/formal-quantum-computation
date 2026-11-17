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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspVerifierBase

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section BiGqspVerifierSlice
set_option maxRecDepth 250000
@[expose] public section
namespace SpecsAux
open Operator Matrix QProg HermitianMat Circuit
open scoped Matrix ComplexOrder MatrixOrder QHLExpectation BigOperators
theorem smul_mem_unitaryGroup_of_norm_eq_one {d : Type*} [Fintype d] [DecidableEq d]
    {γ : ℂ} (hγ : ‖γ‖ = 1) {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) :
    (γ • U) ∈ Matrix.unitaryGroup d ℂ := by
  have hstar_γ : star γ * γ = 1 := by
    rw [RCLike.star_def, mul_comm, Complex.mul_conj', hγ, Complex.ofReal_one, _root_.one_pow]
  rw [Matrix.mem_unitaryGroup_iff']
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hstar_γ, one_smul]
  exact hU.1
theorem real_sqrt_two_pow (b : ℕ) : (Real.sqrt 2) ^ b = Real.sqrt ((2 : ℝ) ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, pow_succ, ih, ← Real.sqrt_mul (by positivity)]
theorem sqrt_half_pow_eq_inv_sqrt_two_pow (b : ℕ) :
    ((Real.sqrt (1 / 2) : ℂ) ^ b) = (Real.sqrt (2 ^ b) : ℂ)⁻¹ := by
  have h_real : (Real.sqrt (1 / 2) : ℝ) ^ b = (Real.sqrt ((2 : ℝ) ^ b))⁻¹ := by
    rw [one_div, Real.sqrt_inv, inv_pow, real_sqrt_two_pow]
  exact_mod_cast h_real
def rRev (b : ℕ) : QRegister b b := ⟨fun i : Fin b ↦ i.rev, fun _ _ h ↦ Fin.rev_injective h⟩
theorem sum_rev_basisBits_val_mul_two_pow_rev {b : ℕ} (k : Fin (2 ^ b)) :
    ∑ i : Fin b, ((basisBits b k i.rev).val : ℂ) * ((2 : ℂ) ^ i.rev.val) = (k.val : ℂ) := by
  have hbij : ∑ i : Fin b, ((basisBits b k i.rev).val : ℂ) * ((2 : ℂ) ^ i.rev.val) = ∑ j : Fin
      b, ((basisBits b k j).val : ℂ) * ((2 : ℂ) ^ j.val) := Equiv.sum_comp Fin.revPerm
      (fun j : Fin b ↦ ((basisBits b k j).val : ℂ) * ((2 : ℂ) ^ j.val))
  have hnat : ∑ j : Fin b, (basisBits b k j).val * 2 ^ j.val = k.val :=
    congrArg Fin.val ((basisBitsEquiv b).symm_apply_apply k)
  have hcast := congrArg (Nat.cast : ℕ → ℂ) hnat
  simpa only [hbij, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hcast
end SpecsAux
end
end BiGqspVerifierSlice

section ModWeighted3ACatalystPrep
@[expose] public section
namespace CatalystPrepAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
end CatalystPrepAlt
theorem catPrepItePos {c : Prop} {_h : Decidable c} (hc : c) {α : Sort*} {t e : α} :
    @ite α c _h t e = t := by
  cases _h with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h
theorem catPrepIteNeg {c : Prop} {_h : Decidable c} (hnc : ¬c) {α : Sort*} {t e : α} :
    @ite α c _h t e = e := by
  cases _h with
  | isTrue h => exact absurd h hnc
  | isFalse _ => rfl
namespace CatalystPrep
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open scoped Matrix Matrix.Norms.L2Operator BigOperators
section GenericCatalystPrep
variable {n : ℕ}
noncomputable def phaseGradAngle (idx : ℕ) : ℝ := Real.pi / (2 : ℝ) ^ (idx + 1)
theorem basisBits_one_if_eq_one (b : ZMod 2) :
    basisBits 1 (if b = 1 then (1 : Fin 2) else 0) 0 = b := by
  fin_cases b <;> rfl
def seqProd {M : Type*} [Monoid M] : {K : ℕ} → (Fin K → M) → M
  | 0, _ => 1
  | _ + 1, u => seqProd (fun j ↦ u j.succ) * u 0
theorem eval_sequence_ofFn_eq_seqProd :
    ∀ {K : ℕ} (c : Fin K → Circuit n),
      (Circuit.sequence (List.ofFn c)).eval = seqProd (fun i ↦ (c i).eval)
  | 0, _ => by simp [seqProd, List.ofFn_zero]
  | K + 1, c => by
    rw [List.ofFn_succ, Circuit.sequence, Circuit.eval_seq,
      eval_sequence_ofFn_eq_seqProd (fun j ↦ c j.succ)]
    rfl
theorem seqProd_coe_unitary {d : Type*} [Fintype d] [DecidableEq d] :
    ∀ {K : ℕ} (u : Fin K → Matrix.unitaryGroup d ℂ),
      (seqProd u).1 = seqProd (fun i ↦ (u i).1)
  | 0, _ => rfl
  | K + 1, u => by
    dsimp only [seqProd]
    rw [Submonoid.coe_mul, seqProd_coe_unitary (fun j ↦ u j.succ)]
theorem seqProd_succ_last {M : Type*} [Monoid M] :
    ∀ {K : ℕ} (u : Fin (K + 1) → M),
      seqProd u = u (Fin.last K) * seqProd (fun i : Fin K ↦ u i.castSucc)
  | 0, u => by simp [seqProd, Fin.last]
  | K + 1, u => by
    change seqProd (fun j : Fin (K + 1) ↦ u j.succ) * u 0 = _
    rw [seqProd_succ_last (fun j : Fin (K + 1) ↦ u j.succ), mul_assoc]
    rfl
theorem seqProd_embedUnitary {k : ℕ} (r : QRegister k n) :
    ∀ {K : ℕ} (u : Fin K → Unitary (2 ^ k)),
      seqProd (fun i ↦ r.embedUnitary (u i)) = r.embedUnitary (seqProd u)
  | 0, _ => by simp [seqProd]
  | K + 1, u => by
    dsimp only [seqProd]
    rw [seqProd_embedUnitary r (fun j ↦ u j.succ), ← r.embedUnitary_mul]
theorem seqProd_comm_single {M : Type*} [Monoid M] {K : ℕ} (u : Fin K → M) (x : M)
    (hcomm : ∀ j : Fin K, u j * x = x * u j) : seqProd u * x = x * seqProd u := by
  induction K with
  | zero => simp [seqProd]
  | succ K ih =>
    dsimp only [seqProd]
    rw [mul_assoc, hcomm 0, ← mul_assoc, ih (fun j ↦ u j.succ) (fun j ↦ hcomm j.succ), mul_assoc]
theorem seqProd_mul_comm_of_disjoint {M : Type*} [Monoid M] {K : ℕ} (f g : Fin K → M)
    (hcomm : ∀ i j : Fin K, i ≠ j → g j * f i = f i * g j) : seqProd (fun i ↦ f i * g i) =
    seqProd f * seqProd g := by
  induction K with
  | zero => simp [seqProd]
  | succ K ih =>
    dsimp only [seqProd]
    rw [ih (fun j ↦ f j.succ) (fun j ↦ g j.succ)
      (fun i j hij ↦ hcomm i.succ j.succ (fun h ↦ hij (Fin.succ_inj.mp h)))]
    have hcomm0 : seqProd (fun j : Fin K ↦ g j.succ) * f 0 = f 0 * seqProd
        (fun j : Fin K ↦ g j.succ) := seqProd_comm_single (fun j : Fin K ↦ g j.succ) (f 0)
        (fun j ↦ hcomm 0 j.succ (Fin.succ_ne_zero j).symm)
    calc (seqProd (fun j ↦ f j.succ) * seqProd (fun j ↦ g j.succ)) * (f 0 * g 0)
      _ = seqProd (fun j ↦ f j.succ) * (seqProd (fun j ↦ g j.succ) * f 0) * g 0 := by
          simp only [mul_assoc]
      _ = (seqProd (fun j ↦ f j.succ) * f 0) * (seqProd (fun j ↦ g j.succ) * g 0) := by
          rw [hcomm0]; simp only [mul_assoc]
theorem seqProd_diagonal {d : ℕ} {K : ℕ} (δ : Fin K → Fin d → ℂ) :
    seqProd (fun i : Fin K ↦ Matrix.diagonal (δ i)) =
      Matrix.diagonal (fun k : Fin d ↦ ∏ i : Fin K, δ i k) := by
  induction K with
  | zero => simp [seqProd, Matrix.diagonal_one]
  | succ K ih =>
    dsimp only [seqProd]
    rw [ih (fun j ↦ δ j.succ), Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext k
    rw [Fin.prod_univ_succ, mul_comm]
theorem norm_seqProd_le_one {A : Type*} [NormedRing A] [NormOneClass A] :
    ∀ {K : ℕ} (u : Fin K → A),(∀ i, ‖u i‖ ≤ 1) → ‖seqProd u‖ ≤ 1
  | 0, _, _ => by
    dsimp only [seqProd]
    exact norm_one.le
  | K + 1, u, hu => by
    dsimp only [seqProd]
    exact (norm_mul_le_of_right_le_one (hu 0)).trans
      (norm_seqProd_le_one (fun j ↦ u j.succ) (fun j ↦ hu j.succ))
noncomputable def rzDiagMatrix (θ : ℝ) : Operator 2 :=
  Matrix.diagonal ![Complex.exp (θ * Complex.I), Complex.exp (-(θ * Complex.I))]
theorem rzDiagMatrix_mem_unitaryGroup (θ : ℝ) :
    rzDiagMatrix θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, rzDiagMatrix,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ← Complex.exp_conj, ← Complex.exp_add]
noncomputable def rzDiagUnitary (θ : ℝ) : Unitary 2 :=
  ⟨rzDiagMatrix θ, rzDiagMatrix_mem_unitaryGroup θ⟩
noncomputable def idealPhaseGradDiagBit (idx : ℕ) : Unitary 2 := if idx = 0 then Qubit.Z else
    if idx = 1 then Qubit.S⁻¹ else rzDiagUnitary (phaseGradAngle idx)
noncomputable def phaseGradBitGlobalPhase (idx : ℕ) : ℂ :=
  if idx < 2 then 1 else Complex.exp (phaseGradAngle idx * Complex.I)
theorem norm_phaseGradBitGlobalPhase (idx : ℕ) : ‖phaseGradBitGlobalPhase idx‖ = 1 := by
  unfold phaseGradBitGlobalPhase
  split_ifs
  · simp
  · exact Complex.norm_exp_ofReal_mul_I (phaseGradAngle idx)
theorem qubit_Z_eq_diagonal : Qubit.Z.1 = Matrix.diagonal ![1,-1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qubit.Z]
theorem qubit_S_inv_eq_diagonal : (Qubit.S⁻¹).1 = Matrix.diagonal ![1, -Complex.I] := by
  change (star Qubit.S.1) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qubit.S]
theorem exp_neg_pi_mul_I : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
theorem exp_neg_pi_div_two_mul_I : Complex.exp (-(Real.pi / 2 * Complex.I)) = -Complex.I := by
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
theorem idealPhaseGradDiagBit_eq_diagonal (idx : ℕ) : (idealPhaseGradDiagBit idx).1 =
    Matrix.diagonal (fun b : Fin 2 ↦ phaseGradBitGlobalPhase idx * Complex.exp (-((b.val : ℂ)
    * (2 * (phaseGradAngle idx : ℂ) * Complex.I)))) := by
  unfold idealPhaseGradDiagBit phaseGradBitGlobalPhase
  by_cases h0 : idx = 0
  · subst h0
    rw [catPrepItePos rfl, catPrepItePos (by decide), qubit_Z_eq_diagonal]
    refine congrArg Matrix.diagonal (funext fun b ↦ ?_)
    fin_cases b
    · simp
    · simp only [Nat.cast_one, one_mul, phaseGradAngle, Nat.zero_add, pow_one, Complex.ofReal_div,
      Complex.ofReal_ofNat]
      rw [show (2 : ℂ) * (↑Real.pi / 2) * Complex.I = ↑Real.pi * Complex.I by ring,
        exp_neg_pi_mul_I]
      rfl
  · rw [catPrepIteNeg h0]
    by_cases h1 : idx = 1
    · subst h1
      rw [catPrepItePos rfl, catPrepItePos (by decide), qubit_S_inv_eq_diagonal]
      refine congrArg Matrix.diagonal (funext fun b ↦ ?_)
      fin_cases b
      · simp
      · simp only [Nat.cast_one, one_mul, phaseGradAngle, Complex.ofReal_div, Complex.ofReal_pow,
        Complex.ofReal_ofNat]
        rw [show (2 : ℂ) * ((Real.pi : ℂ) / 2 ^ (1 + 1)) * Complex.I =
            (Real.pi : ℂ) / 2 * Complex.I by ring, exp_neg_pi_div_two_mul_I]
        rfl
    · rw [catPrepIteNeg h1, catPrepIteNeg (show ¬ (idx < 2) by omega)]
      dsimp only [rzDiagUnitary, rzDiagMatrix]
      refine congrArg Matrix.diagonal (funext fun b ↦ ?_)
      fin_cases b
      · simp
      · simp only [Nat.cast_one, one_mul, ← Complex.exp_add]
        exact congrArg Complex.exp (by ring)
theorem singleton_extractIndex_val {n : ℕ} (w : Wire n) (k : Fin (2 ^ n)) :
    ((QRegister.singleton w).extractIndex k).val = (basisBits n k w).val := by
  have h1 : (QRegister.singleton w).extractIndex k = if basisBits n k w = 1 then 1 else 0 :=
    (basisBitsEquiv 1).injective <| funext fun i ↦ by
      fin_cases i
      change basisBits 1 ((QRegister.singleton w).extractIndex k) 0 =
        basisBits 1 (if basisBits n k w = 1 then 1 else 0) 0
      rw [(QRegister.singleton w).basisBits_extractIndex k 0, basisBits_one_if_eq_one]
      rfl
  rw [h1]
  generalize basisBits n k w = x
  fin_cases x <;> rfl
theorem embed_idealPhaseGradDiagBit_eq_diagonal {n : ℕ} (w : Wire n) (idx : ℕ) :
    ((QRegister.singleton w).embedUnitary (idealPhaseGradDiagBit idx)).1 = Matrix.diagonal
    (fun k : Fin (2 ^ n) ↦ phaseGradBitGlobalPhase idx * Complex.exp (-(((basisBits n k w).val
    : ℂ) * (2 * (phaseGradAngle idx : ℂ) * Complex.I)))) := by
  rw [QRegister.embedUnitary_val, idealPhaseGradDiagBit_eq_diagonal,
    QRegister.embedMatrix_diagonal]
  congr 1
  funext k
  rw [singleton_extractIndex_val]
theorem qubit_H_col_zero (y : Fin 2) : Qubit.H.1 y 0 = (Real.sqrt (1 / 2) : ℂ) := by
  fin_cases y <;> simp [Qubit.H]
theorem basisBits_zero_apply (b : ℕ) (w : Wire b) : basisBits b 0 w = 0 := by
  simp [-Nat.reducePow, basisBits_eq_div_mod]
theorem single_zero_eq_if_all_bits_zero (b : ℕ) (k : Fin (2 ^ b)) :
    (Pi.single 0 1 : Fin (2 ^ b) → ℂ) k =
      if (∀ w : Wire b, basisBits b k w = 0) then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [Pi.single_eq_of_ne hk, catPrepIteNeg]
    exact fun hall ↦ hk ((basisBitsEquiv b).injective
      (funext fun w ↦ (hall w).trans (basisBits_zero_apply b w).symm))
theorem circuit_H_mulVec_of_bit_zero {b : ℕ} (w : Wire b) (v : Fin (2 ^ b) → ℂ)
    (hv : ∀ g : Fin (2 ^ b), basisBits b g w ≠ 0 → v g = 0) (k : Fin (2 ^ b)) :
    ((Circuit.H w).eval.1.mulVec v) k =
      (Real.sqrt (1 / 2) : ℂ) * v ((QRegister.singleton w).replaceIndex k 0) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval,
    QRegister.embedMatrix_mulVec_apply]
  erw [Fin.sum_univ_two]
  change _ * v ((QRegister.singleton w).replaceIndex k 0) +
    _ * v ((QRegister.singleton w).replaceIndex k 1) = _
  have h1 : basisBits b ((QRegister.singleton w).replaceIndex k 1) w ≠ 0 := by
    have h := (QRegister.singleton w).basisBits_replaceIndex_apply k 1 0
    change basisBits b ((QRegister.singleton w).replaceIndex k 1) w = basisBits 1 1 0 at h
    rw [h]
    decide
  rw [hv _ h1, mul_zero, add_zero]
  exact congrArg (· * _) (qubit_H_col_zero _)
theorem seqProd_H_mulVec_zero_aux {b : ℕ} (r : QRegister b b) :
    ∀ {m : ℕ} (hm : m ≤ b),
      (seqProd (fun i : Fin m ↦ (Circuit.H (r ⟨i.val, by omega⟩)).eval.1)).mulVec
        (Pi.single 0 1) =
      fun k : Fin (2 ^ b) ↦
        if (∀ j : Fin b, m ≤ j.val → basisBits b k (r j) = 0)
        then (Real.sqrt (1 / 2) : ℂ) ^ m
        else 0
  | 0, _ => by
    ext k
    simp only [seqProd, Matrix.one_mulVec, single_zero_eq_if_all_bits_zero, Nat.zero_le,
      forall_true_left, pow_zero]
    by_cases h : ∀ j : Fin b, basisBits b k (r j) = 0
    · rw [catPrepItePos h, catPrepItePos]
      intro w
      obtain ⟨j, rfl⟩ := Finite.surjective_of_injective r.wires.injective w
      exact h j
    · rw [catPrepIteNeg h, catPrepIteNeg]
      intro hall
      exact h (fun j ↦ hall (r j))
  | m + 1, hm => by
    have hm_lt : m < b := Nat.lt_of_succ_le hm
    rw [seqProd_succ_last (fun i : Fin (m + 1) ↦ (Circuit.H (r ⟨i.val, by omega⟩)).eval.1),
      ← Matrix.mulVec_mulVec]
    have hcast :
        (fun i : Fin m ↦ (Circuit.H (r ⟨i.castSucc.val, by omega⟩)).eval.1) =
          (fun i : Fin m ↦ (Circuit.H (r ⟨i.val, by omega⟩)).eval.1) := rfl
    have hlast : (⟨(Fin.last m).val, by omega⟩ : Fin b) = ⟨m, hm_lt⟩ := rfl
    rw [hcast, hlast, seqProd_H_mulVec_zero_aux r (by omega)]
    let v_m : Fin (2 ^ b) → ℂ := fun g ↦ if ∀ j : Fin b, m ≤ j.val → basisBits b g (r j) = 0
        then (Real.sqrt (1 / 2) : ℂ) ^ m else 0
    have hv_zero : ∀ g : Fin (2 ^ b), basisBits b g (r ⟨m, hm_lt⟩) ≠ 0 → v_m g = 0 := by
      intro g hg
      dsimp only [v_m]
      rw [catPrepIteNeg]
      intro hall
      exact hg (hall ⟨m, hm_lt⟩ le_rfl)
    ext k
    rw [circuit_H_mulVec_of_bit_zero (r ⟨m, hm_lt⟩) v_m hv_zero k]
    dsimp only [v_m]
    have hne (j : Fin b) (hjm : j.val ≠ m) :
        r j ∉ Set.range (QRegister.singleton (r ⟨m, hm_lt⟩)).wires := by
      rintro ⟨idx, hidx⟩
      fin_cases idx
      exact hjm (congrArg Fin.val (r.wires.injective hidx.symm))
    have hiff : (∀ j : Fin b, m ≤ j.val → basisBits b ((QRegister.singleton (r ⟨m,
        hm_lt⟩)).replaceIndex k 0) (r j) = 0) ↔
        (∀ j : Fin b, m + 1 ≤ j.val → basisBits b k (r j) = 0) := by
      refine ⟨fun h j hj ↦ ?_, fun h j hj ↦ ?_⟩
      · rw [← (QRegister.singleton (r ⟨m, hm_lt⟩)).basisBits_replaceIndex_of_not_mem k 0 (r j)
          (hne j (by omega))]
        exact h j (by omega)
      · by_cases hjm : j.val = m
        · have hj_eq : j = ⟨m, hm_lt⟩ := Fin.ext hjm
          subst hj_eq
          have h0 := (QRegister.singleton (r ⟨m, hm_lt⟩)).basisBits_replaceIndex_apply k 0 0
          exact (h0 : basisBits b _ (r ⟨m, hm_lt⟩) = basisBits 1 0 0).trans (by decide)
        · rw [(QRegister.singleton (r ⟨m, hm_lt⟩)).basisBits_replaceIndex_of_not_mem k 0 (r j)
            (hne j hjm)]
          exact h j (by omega)
    simp only [hiff]
    by_cases h : ∀ j : Fin b, m + 1 ≤ j.val → basisBits b k (r j) = 0
    · rw [catPrepItePos h, catPrepItePos h, pow_succ']
    · rw [catPrepIteNeg h, catPrepIteNeg h, mul_zero]
theorem seqProd_H_col_zero {b : ℕ} (r : QRegister b b) (k : Fin (2 ^ b)) :
    (seqProd (fun i : Fin b ↦ (Circuit.H (r i)).eval.1)) k 0 =
      (Real.sqrt (1 / 2) : ℂ) ^ b := by
  have hcol : (seqProd (fun i : Fin b ↦ (Circuit.H (r i)).eval.1)) k 0 =
      ((seqProd (fun i : Fin b ↦ (Circuit.H (r ⟨i.val, i.isLt⟩)).eval.1)).mulVec
        (Pi.single 0 1)) k := by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [hcol, seqProd_H_mulVec_zero_aux r le_rfl]
  dsimp only
  rw [catPrepItePos (fun j hj ↦ absurd j.isLt (not_lt.mpr hj))]
theorem comm_mul_of_comm {N : ℕ} {A B P : Operator N} (hA : A * P = P * A)
    (hB : B * P = P * B) : (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
noncomputable def phaseGradGlobalPhase (B : ℕ) : ℂ :=
  ∏ i : Fin B, phaseGradBitGlobalPhase i.val
theorem norm_phaseGradGlobalPhase (B : ℕ) : ‖phaseGradGlobalPhase B‖ = 1 := by
  unfold phaseGradGlobalPhase
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i _
  exact norm_phaseGradBitGlobalPhase i.val
theorem star_phaseGradGlobalPhase_mul_self (B : ℕ) :
    star (phaseGradGlobalPhase B) * phaseGradGlobalPhase B = 1 := by
  rw [RCLike.star_def, mul_comm, Complex.mul_conj', norm_phaseGradGlobalPhase B]
  norm_num
theorem two_mul_phaseGradAngle_eq_pow_revB {B : ℕ} (i : Fin B) :
    2 * (phaseGradAngle i.val : ℂ) =
      2 * (Real.pi : ℂ) * ((2 : ℂ) ^ (i.rev.val : ℕ)) / (2 : ℂ) ^ B := by
  unfold phaseGradAngle
  have hi := i.isLt
  have hrev : i.rev.val + (i.val + 1) = B := by
    simp [Fin.val_rev]
  have hpow : (2 : ℂ) ^ B = (2 : ℂ) ^ (i.rev.val : ℕ) * (2 : ℂ) ^ (i.val + 1) := by
    rw [← pow_add, hrev]
  have hB_ne : (2 : ℂ) ^ B ≠ 0 := pow_ne_zero _ (by norm_num)
  have hi_ne : (2 : ℂ) ^ (i.val + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  field_simp [hB_ne, hi_ne]
  rw [hpow]
  ring
noncomputable def U_cat_B_prep (B : ℕ) : Unitary (2 ^ B) := seqProd (fun i : Fin B ↦
    (QRegister.singleton i.rev).embedUnitary (idealPhaseGradDiagBit i.val) * (Circuit.H
    i.rev).eval)
theorem U_cat_B_prep_col_zero (B : ℕ) (k : Fin (2 ^ B)) :
    (U_cat_B_prep B).1 k 0 = phaseGradGlobalPhase B * FullScaleBESector.phaseGradientState B k := by
  have hH_col : (seqProd (fun i : Fin B ↦ (Circuit.H i.rev).eval.1)) k 0 =
      (Real.sqrt (1 / 2) : ℂ) ^ B := seqProd_H_col_zero (rRev B) k
  have hU_val : (U_cat_B_prep B).1 =
      seqProd (fun i : Fin B ↦
        ((QRegister.singleton i.rev).embedUnitary (idealPhaseGradDiagBit i.val)).1) *
        seqProd (fun i : Fin B ↦ (Circuit.H i.rev).eval.1) := by
    unfold U_cat_B_prep
    rw [seqProd_coe_unitary]
    refine seqProd_mul_comm_of_disjoint _ _ fun i j hij ↦ ?_
    have hdisj : (QRegister.singleton i.rev).DisjointWires (QRegister.singleton j.rev) := by
      rw [QRegister.disjoint_iff]
      intro a b
      fin_cases a
      fin_cases b
      exact fun h ↦ hij (Fin.rev_injective h)
    rw [Circuit.eval_single, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact ((QRegister.singleton i.rev).embedMatrix_comm_of_disjoint
      (QRegister.singleton j.rev) hdisj _ _).symm
  have hD_eq : seqProd (fun i : Fin B ↦
      ((QRegister.singleton i.rev).embedUnitary (idealPhaseGradDiagBit i.val)).1) =
      Matrix.diagonal (fun g : Fin (2 ^ B) ↦ ∏ i : Fin B, phaseGradBitGlobalPhase i.val *
        Complex.exp (-(((basisBits B g i.rev).val : ℂ) *
          (2 * (phaseGradAngle i.val : ℂ) * Complex.I)))) := by
    rw [funext fun i : Fin B ↦ embed_idealPhaseGradDiagBit_eq_diagonal i.rev i.val,
      seqProd_diagonal]
  rw [hU_val, hD_eq, Matrix.diagonal_mul, hH_col,
    sqrt_half_pow_eq_inv_sqrt_two_pow B, Finset.prod_mul_distrib, ← phaseGradGlobalPhase,
    ← Complex.exp_sum]
  have hexp_eq : (∑ i : Fin B, -(((basisBits B k i.rev).val : ℂ) *
      (2 * (phaseGradAngle i.val : ℂ) * Complex.I))) =
      -(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ)) / (2 : ℂ) ^ B := by
    have hterm (i : Fin B) :
        -(((basisBits B k i.rev).val : ℂ) * (2 * (phaseGradAngle i.val : ℂ) * Complex.I)) =
          (((basisBits B k i.rev).val : ℂ) * ((2 : ℂ) ^ i.rev.val)) *
            (-(2 * (Real.pi : ℂ) * Complex.I) / (2 : ℂ) ^ B) := by
      rw [two_mul_phaseGradAngle_eq_pow_revB i]
      ring
    simp_rw [hterm, ← Finset.sum_mul]
    rw [show (∑ i : Fin B, ((basisBits B k i.rev).val : ℂ) * ((2 : ℂ) ^ i.rev.val)) =
      (k.val : ℂ) by exact_mod_cast sum_rev_basisBits_val_mul_two_pow_rev k]
    ring
  rw [hexp_eq]
  unfold FullScaleBESector.phaseGradientState
  ring
noncomputable def U_cat_B_normalized (B : ℕ) : Unitary (2 ^ B) :=
  ⟨star (phaseGradGlobalPhase B) • (U_cat_B_prep B).1,
    smul_mem_unitaryGroup_of_norm_eq_one
      (by rw [norm_star, norm_phaseGradGlobalPhase B]) (U_cat_B_prep B).2⟩
theorem U_cat_B_normalized_col_zero (B : ℕ) (k : Fin (2 ^ B)) :
    (U_cat_B_normalized B).1 k 0 = FullScaleBESector.phaseGradientState B k := by
  change (star (phaseGradGlobalPhase B) • (U_cat_B_prep B).1) k 0 = _
  rw [Matrix.smul_apply, smul_eq_mul, U_cat_B_prep_col_zero B k, ← mul_assoc,
    star_phaseGradGlobalPhase_mul_self B, one_mul]
theorem embed_U_cat_B_prep_eq_seqProd_gen {B m : ℕ} (rCat : QRegister B m) :
    (rCat.embedUnitary (U_cat_B_prep B)).1 = seqProd (fun i : Fin B ↦ ((QRegister.singleton
    (rCat i.rev)).embedUnitary (idealPhaseGradDiagBit i.val) * (Circuit.H (rCat
    i.rev)).eval).1) := by
  unfold U_cat_B_prep
  rw [← seqProd_embedUnitary, seqProd_coe_unitary]
  refine congrArg seqProd (funext fun i ↦ ?_)
  have hcomp : rCat.compose (QRegister.singleton i.rev) = QRegister.singleton (rCat i.rev) :=
    CatalystPrepAlt.qreg_ext fun j ↦ by
      fin_cases j
      rfl
  rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, Submonoid.coe_mul]
  congr 1
  · rw [← QRegister.embedUnitary_compose, hcomp]
  · rw [QRegister.embedUnitary_val, Circuit.eval_single, Circuit.eval_single,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      hcomp]
theorem realizesCleanWorkspace_substCircuit_active
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {k mWork m : ℕ} [NeZero (2 ^ m)]
    (hm : 1 ≤ mWork) (v : Var)
    (rAct : QRegister k m) (rWork : QRegister mWork m)
    (hDisj : rAct.DisjointWires rWork)
    (c : Circuit k) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork c.eval
      (substCircuit v (rWork ⟨0, by omega⟩) (Circuit.onRegister rAct c)) := by
  let qToff : Wire m := rWork ⟨0, by omega⟩
  have hq_mem : qToff ∈ rWork.image := (rWork.mem_image qToff).mpr ⟨⟨0, by omega⟩, rfl⟩
  have hSupp : Disjoint (Circuit.onRegister rAct c).support rWork.image := by
    rw [Finset.disjoint_left]
    intro w hw hmem
    rcases (rAct.mem_image w).mp (Circuit.support_onRegister_subset rAct c hw) with ⟨i, hi⟩
    rcases (rWork.mem_image w).mp hmem with ⟨j, hj⟩
    exact Set.disjoint_left.mp hDisj ⟨i, hi⟩ ⟨j, hj⟩
  exact DynProgS2.wp_compile_clean_workspace_spec
    (p := .circ (Circuit.onRegister rAct c)) (S := rWork.image)
    ⟨hq_mem, hSupp⟩ rAct rWork (fun w hw ↦ (rWork.mem_image w).mp hw) c.eval
    (Circuit.eval_onRegister rAct c)
end GenericCatalystPrep
end CatalystPrep
end
end ModWeighted3ACatalystPrep

section ModWeighted3ABiGqspSegmentSpine
@[expose] public section
namespace BiGqspSegmentSpineAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
end BiGqspSegmentSpineAlt
namespace BiGqspSegmentSpine
set_option exponentiation.threshold 8192
open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeDuhamel
open SingleRBEGridGuardWalk
open TFreeLaurentGQSP
open CatalyzedLaurentGQSP BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open scoped Matrix Matrix.Norms.L2Operator BigOperators
instance (priority := 100000) instNeZeroTwoPowSpine (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
lemma basisBits_zero_spine (q : ℕ) (i : Fin q) : basisBits q (0 : Fin (2 ^ q)) i = 0 := by
  rw [basisBits_eq_div_mod]
  simp
lemma zero_extract_iff_bits_zero {r N : ℕ} (reg : QRegister r N) (g : Fin (2 ^ N)) :
    reg.extractIndex g = 0 ↔ ∀ idx : Fin r, basisBits N g (reg idx) = 0 := by
  constructor
  · intro h idx
    have hb := congrArg (fun x ↦ basisBits r x idx) h
    rw [basisBits_zero_spine] at hb
    simpa [-Nat.reducePow, QRegister.basisBits_extractIndex] using hb
  · intro h
    rw [← (basisBitsEquiv r).apply_eq_iff_eq]
    funext idx
    change basisBits r (reg.extractIndex g) idx = basisBits r 0 idx
    rw [basisBits_zero_spine]
    simpa [-Nat.reducePow, QRegister.basisBits_extractIndex] using h idx
noncomputable def physGridReflGen (k m : ℕ) (b : Fin (2 ^ k) → Bool) : Operator (2 ^ (k + m))
    := singleRBEReflMatrix k m (diagProj k b)
theorem physGridReflGen_conjTranspose (k m : ℕ) (b : Fin (2 ^ k) → Bool) :
    (physGridReflGen k m b)ᴴ = physGridReflGen k m b :=
  reflOfProj_conjTranspose (projGridAncZero_isHermitian k m (diagProj_isHermitian k b))
theorem physGridReflGen_mul_self (k m : ℕ) (b : Fin (2 ^ k) → Bool) :
    physGridReflGen k m b * physGridReflGen k m b = 1 :=
  reflOfProj_mul_self (projGridAncZero_idem k m (diagProj_idem k b))
noncomputable def physLaurentWalkGen {k m : ℕ} (b : Fin (2 ^ k) → Bool)
    (U_raw : Unitary (2 ^ (k + m))) : Operator (2 ^ (k + m)) :=
  Complex.I • (physGridReflGen k m b * U_raw.1)
noncomputable def physLaurentWalkInvGen {k m : ℕ} (b : Fin (2 ^ k) → Bool)
    (U_raw : Unitary (2 ^ (k + m))) : Operator (2 ^ (k + m)) :=
  (-Complex.I) • (U_raw.1 * physGridReflGen k m b)
theorem physLaurentWalkGen_mem_unitary {k m : ℕ} (b : Fin (2 ^ k) → Bool)
    (U_raw : Unitary (2 ^ (k + m))) :
    physLaurentWalkGen b U_raw ∈ Matrix.unitaryGroup (Fin (2 ^ (k + m))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, physLaurentWalkGen, Matrix.star_eq_conjTranspose,
    conjTranspose_smul, conjTranspose_mul, physGridReflGen_conjTranspose, smul_mul_smul_comm]
  rw [Matrix.mul_assoc (physGridReflGen k m b), ← Matrix.mul_assoc U_raw.1,
    ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp U_raw.2, Matrix.one_mul,
    physGridReflGen_mul_self]
  simp [Complex.I_mul_I]
theorem physLaurentWalkInvGen_mem_unitary {k m : ℕ} (b : Fin (2 ^ k) → Bool)
    (U_raw : Unitary (2 ^ (k + m))) :
    physLaurentWalkInvGen b U_raw ∈ Matrix.unitaryGroup (Fin (2 ^ (k + m))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, physLaurentWalkInvGen, Matrix.star_eq_conjTranspose,
    conjTranspose_smul, conjTranspose_mul, physGridReflGen_conjTranspose, smul_mul_smul_comm]
  rw [Matrix.mul_assoc U_raw.1, ← Matrix.mul_assoc (physGridReflGen k m b),
    physGridReflGen_mul_self, Matrix.one_mul, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff.mp U_raw.2]
  simp [Complex.I_mul_I]
noncomputable def physBiSegmentUnitaryGen {k m : ℕ} (b : Fin (2 ^ k) → Bool)
    (M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42))
    (U_raw : Unitary (2 ^ (k + m))) : Unitary (2 ^ (k + (m + 1))) :=
  let rBE : QRegister (k + m) (k + (m + 1)) := QRegister.block 0 (k + m) (by omega)
  let q_sig : Wire (k + (m + 1)) := ⟨k + m, by omega⟩
  have hBE_sig : rBE.DisjointWires (QRegister.singleton q_sig) := by
    rw [QRegister.disjoint_iff]
    intro i j h
    have hv := congrArg Fin.val h
    simp [rBE, q_sig, QRegister.singleton] at hv
    omega
  have hW_mem : rBE.embedMatrix (physLaurentWalkGen b U_raw) ∈
      Matrix.unitaryGroup (Fin (2 ^ (k + (m + 1)))) ℂ :=
    (rBE.embedUnitary ⟨physLaurentWalkGen b U_raw, physLaurentWalkGen_mem_unitary b U_raw⟩).2
  have hWinv_mem : rBE.embedMatrix (physLaurentWalkInvGen b U_raw) ∈
      Matrix.unitaryGroup (Fin (2 ^ (k + (m + 1)))) ℂ :=
    (rBE.embedUnitary ⟨physLaurentWalkInvGen b U_raw, physLaurentWalkInvGen_mem_unitary b U_raw⟩).2
  have hW_0 := embedMatrix_comm_sig_proj rBE q_sig hBE_sig (physLaurentWalkGen b U_raw) 0
  have hW_1 := embedMatrix_comm_sig_proj rBE q_sig hBE_sig (physLaurentWalkGen b U_raw) 1
  have hWinv_0 := embedMatrix_comm_sig_proj rBE q_sig hBE_sig
    (physLaurentWalkInvGen b U_raw) 0
  have hWinv_1 := embedMatrix_comm_sig_proj rBE q_sig hBE_sig
    (physLaurentWalkInvGen b U_raw) 1
  ⟨biGqspSegmentOp q_sig
      (rBE.embedMatrix (physLaurentWalkGen b U_raw))
      (rBE.embedMatrix (physLaurentWalkInvGen b U_raw))
      (biCS M C) M,
    Submonoid.mul_mem _
      (Submonoid.mul_mem _
        (Submonoid.mul_mem _
          (Submonoid.mul_mem _ (Circuit.H q_sig).eval.2
            (c0_step_mem_unitaryGroup q_sig _ hWinv_mem hWinv_0))
          (biGqspLoopOp_biCS_mem_unitaryGroup q_sig _ _
            (biWalkStepOp_mem_unitaryGroup q_sig _ _ hW_mem hWinv_mem hW_0 hWinv_0 hWinv_1)
            M C M))
        (c1_step_mem_unitaryGroup q_sig _ hW_mem hW_1))
      (Circuit.H q_sig).eval.2⟩
def rPhysInGhost (k m : ℕ) : QRegister (k + (m + 1)) (k + (m + 1 + 1)) where
  wires := ⟨fun i ↦ if i.val < k + m then ⟨i.val, by omega⟩ else ⟨k + (m + 1), by omega⟩, by
    intro i j h
    have hv := congrArg Fin.val h
    ext
    by_cases hi : i.val < k + m <;> by_cases hj : j.val < k + m <;>
      simp [hi, hj] at hv <;> omega⟩
theorem rPhysInGhost_disjoint_ghost (k m : ℕ) :
    (rPhysInGhost k m).DisjointWires
      (QRegister.singleton (⟨k + m, by omega⟩ : Wire (k + (m + 1 + 1)))) := by
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv : (rPhysInGhost k m i).val = k + m := by
    fin_cases j
    simpa [QRegister.singleton] using congrArg Fin.val h
  by_cases hi : i.val < k + m
  · simp [rPhysInGhost, hi] at hv; omega
  · simp [rPhysInGhost, hi] at hv
theorem rPhysInGhost_sig (k m : ℕ) :
    rPhysInGhost k m ⟨k + m, by omega⟩ =
      (⟨k + (m + 1), by omega⟩ : Wire (k + (m + 1 + 1))) := by
  ext
  simp [rPhysInGhost]
theorem rPhysInGhost_compose_rBE (k m : ℕ) :
    (rPhysInGhost k m).compose (QRegister.block 0 (k + m) (by omega)) =
      (QRegister.block 0 (k + m) (by omega) : QRegister (k + m) (k + (m + 1 + 1))) := by
  apply BiGqspSegmentSpineAlt.qreg_ext
  intro i
  ext
  have hi : i.val < k + m := i.isLt
  simp [rPhysInGhost, hi]
theorem ghostGuard_conj_biCatSegmentOp_mul_ghostZero_gen
    {k m : ℕ} (hm : 0 < m) (b : Fin (2 ^ k) → Bool)
    (M : ℕ) (C : Fin (M + 1) → Fin (2 ^ 42))
    (U_raw : Unitary (2 ^ (k + m))) :
    let U_BE : Unitary (2 ^ (k + (m + 1))) := ghostZeroedBE k m hm b U_raw
    let rBEG : QRegister (k + (m + 1)) (k + (m + 1 + 1)) :=
      QRegister.block 0 (k + (m + 1)) (by omega)
    let qSigG : Wire (k + (m + 1 + 1)) := ⟨k + (m + 1), by omega⟩
    let qGhG : Wire (k + (m + 1 + 1)) := ⟨k + m, by omega⟩
    let GG : Operator (2 ^ (k + (m + 1 + 1))) := rBEG.embedMatrix (ghostGuardMatrix k m b)
    let P_gh0 : Operator (2 ^ (k + (m + 1 + 1))) :=
      (QRegister.singleton qGhG).basisOutcomeProjector 0
    (GG * biCatSegmentOp rBEG qSigG M C U_BE * GG) * P_gh0 =
      (rPhysInGhost k m).embedMatrix (physBiSegmentUnitaryGen b M C U_raw).1 * P_gh0 := by
  intro U_BE rBEG qSigG qGhG GG P_gh0
  let G1 : Operator (2 ^ (k + (m + 1))) := ghostGuardMatrix k m b
  have hGG1 : G1 * G1 = 1 := ghostGuardMatrix_mul_self k m b
  have hGG : GG * GG = 1 := by rw [← rBEG.embedMatrix_mul, hGG1, rBEG.embedMatrix_one]
  have hBE_sig : rBEG.DisjointWires (QRegister.singleton qSigG) := by
    rw [QRegister.disjoint_iff]
    intro i j h
    have hv := congrArg Fin.val h
    simp [rBEG, qSigG, QRegister.singleton] at hv
    omega
  have hGh_sig : (QRegister.singleton qGhG).DisjointWires (QRegister.singleton qSigG) := by
    rw [QRegister.disjoint_iff]
    intro i j h
    fin_cases i
    fin_cases j
    simpa [qGhG, qSigG, QRegister.singleton] using congrArg Fin.val h
  have hCompGh : rBEG.compose (ghostReg k m) = QRegister.singleton qGhG := by
    apply BiGqspSegmentSpineAlt.qreg_ext
    intro i
    fin_cases i
    ext
    simp [rBEG, ghostReg, qGhG, QRegister.singleton]
  have hPgh_emb : rBEG.embedMatrix (ghostZeroProj k m) = P_gh0 := by
    unfold ghostZeroProj QRegister.basisOutcomeProjector
    rw [← QRegister.embedMatrix_compose, hCompGh]
    rfl
  have hCompBase : rBEG.compose (baseReg k m) =
      (rPhysInGhost k m).compose (QRegister.block 0 (k + m) (by omega)) := by
    rw [rPhysInGhost_compose_rBE]
    apply BiGqspSegmentSpineAlt.qreg_ext
    intro i
    ext
    simp [rBEG, baseReg]
  have hEmbBase (X : Operator (2 ^ (k + m))) :
      rBEG.embedMatrix ((baseReg k m).embedMatrix X) =
        (rPhysInGhost k m).embedMatrix ((QRegister.block 0 (k + m) (by omega)).embedMatrix X) := by
    rw [← QRegister.embedMatrix_compose, hCompBase, QRegister.embedMatrix_compose]
  have hRefl1 : (G1 * szegedyRefl k (m + 1) * G1) * ghostZeroProj k m =
      (baseReg k m).embedMatrix (physGridReflGen k m b) * ghostZeroProj k m := by
    have hSzEq : szegedyRefl k (m + 1) = reflOfProj (ancGhostZeroProj k m) := by
      unfold szegedyRefl reflOfProj ancGhostZeroProj ancGhostReg
      dsimp only
      rw [two_mul, two_smul]
    rw [hSzEq]
    exact ghostGuard_conj_refl_mul_ghostZero k m b
  have hUBE1 : (G1 * U_BE.1 * G1) * ghostZeroProj k m =
      (baseReg k m).embedMatrix U_raw.1 * ghostZeroProj k m := by
    have h1 : G1 * U_BE.1 * G1 = ghostMuxOp k m U_raw.1 (ancFlipMatrix k m hm) := by
      calc G1 * (G1 * ghostMuxOp k m U_raw.1 (ancFlipMatrix k m hm) * G1) * G1
        _ = (G1 * G1) * ghostMuxOp k m U_raw.1 (ancFlipMatrix k m hm) * (G1 * G1) := by
              simp only [Matrix.mul_assoc]
        _ = ghostMuxOp k m U_raw.1 (ancFlipMatrix k m hm) := by
              rw [hGG1, Matrix.one_mul, Matrix.mul_one]
    rw [h1, ghostMuxOp_mul_ghostZeroProj]
  have hConjBase (z : ℂ) {A B : Operator (2 ^ (k + (m + 1)))}
      {A' B' : Operator (2 ^ (k + m))}
      (hA : (G1 * A * G1) * ghostZeroProj k m = (baseReg k m).embedMatrix A' * ghostZeroProj k m)
      (hB : (G1 * B * G1) * ghostZeroProj k m = (baseReg k m).embedMatrix B' * ghostZeroProj k m) :
      (G1 * (z • (A * B)) * G1) * ghostZeroProj k m =
        (baseReg k m).embedMatrix (z • (A' * B')) * ghostZeroProj k m := by
    have hmid : G1 * (A * B) * G1 = (G1 * A * G1) * (G1 * B * G1) := by
      calc G1 * (A * B) * G1 = G1 * A * (G1 * G1) * B * G1 := by
            rw [hGG1]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (G1 * A * G1) * (G1 * B * G1) := by simp only [Matrix.mul_assoc]
    have hab : (G1 * (A * B) * G1) * ghostZeroProj k m =
        (baseReg k m).embedMatrix (A' * B') * ghostZeroProj k m := by
      calc (G1 * (A * B) * G1) * ghostZeroProj k m
        _ = (G1 * A * G1) * ((G1 * B * G1) * ghostZeroProj k m) := by
              rw [hmid, Matrix.mul_assoc (G1 * A * G1)]
        _ = ((G1 * A * G1) * ghostZeroProj k m) * (baseReg k m).embedMatrix B' := by
              rw [hB, baseReg_embedMatrix_comm_ghostZeroProj k m B',
                ← Matrix.mul_assoc (G1 * A * G1)]
        _ = (baseReg k m).embedMatrix (A' * B') * ghostZeroProj k m := by
              rw [hA, Matrix.mul_assoc ((baseReg k m).embedMatrix A'),
                ← baseReg_embedMatrix_comm_ghostZeroProj k m B',
                ← Matrix.mul_assoc ((baseReg k m).embedMatrix A'),
                ← (baseReg k m).embedMatrix_mul]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hab,
      (baseReg k m).embedMatrix_smul, Matrix.smul_mul]
  have hW1 : (G1 * laurentWalk U_BE * G1) * ghostZeroProj k m =
      (baseReg k m).embedMatrix (physLaurentWalkGen b U_raw) * ghostZeroProj k m := by
    unfold laurentWalk szegedyWalk physLaurentWalkGen
    exact hConjBase Complex.I hRefl1 hUBE1
  have hWinv1 : (G1 * laurentWalkInv U_BE * G1) * ghostZeroProj k m =
      (baseReg k m).embedMatrix (physLaurentWalkInvGen b U_raw) * ghostZeroProj k m := by
    unfold laurentWalkInv szegedyWalkInv physLaurentWalkInvGen
    exact hConjBase (-Complex.I) hUBE1 hRefl1
  let WpG := (rPhysInGhost k m).embedMatrix ((QRegister.block 0 (k + m) (by omega) : QRegister
      (k + m) (k + (m + 1))).embedMatrix (physLaurentWalkGen b U_raw))
  let WpinvG := (rPhysInGhost k m).embedMatrix ((QRegister.block 0 (k + m) (by omega) :
      QRegister (k + m) (k + (m + 1))).embedMatrix (physLaurentWalkInvGen b U_raw))
  have hWG : (GG * rBEG.embedMatrix (laurentWalk U_BE) * GG) * P_gh0 = WpG * P_gh0 := by
    have h := congrArg rBEG.embedMatrix hW1
    simp only [rBEG.embedMatrix_mul, hPgh_emb, hEmbBase] at h
    exact h
  have hWinvG : (GG * rBEG.embedMatrix (laurentWalkInv U_BE) * GG) * P_gh0 = WpinvG * P_gh0 := by
    have h := congrArg rBEG.embedMatrix hWinv1
    simp only [rBEG.embedMatrix_mul, hPgh_emb, hEmbBase] at h
    exact h
  have hCommPhysGh (X : Operator (2 ^ (k + (m + 1)))) :
      (rPhysInGhost k m).embedMatrix X * P_gh0 = P_gh0 * (rPhysInGhost k m).embedMatrix X :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (rPhysInGhost k m))
      (QRegister.singleton qGhG) (rPhysInGhost_disjoint_ghost k m) X 0
  have hCommG_sig (X : Operator 2) : GG * (QRegister.singleton qSigG).embedMatrix X =
      (QRegister.singleton qSigG).embedMatrix X * GG :=
    rBEG.embedMatrix_comm_of_disjoint (QRegister.singleton qSigG) hBE_sig G1 X
  have hCommGh_sig (X : Operator 2) : (QRegister.singleton qSigG).embedMatrix X * P_gh0 =
      P_gh0 * (QRegister.singleton qSigG).embedMatrix X :=
    ((QRegister.singleton qGhG).embedMatrix_comm_of_disjoint
      (QRegister.singleton qSigG) hGh_sig (compProj (0 : Fin 2)) X).symm
  let P_sig0 := (QRegister.singleton qSigG).basisOutcomeProjector 0
  let P_sig1 := (QRegister.singleton qSigG).basisOutcomeProjector 1
  have hG0 : GG * P_sig0 = P_sig0 * GG := hCommG_sig (compProj 0)
  have hG1_sig : GG * P_sig1 = P_sig1 * GG := hCommG_sig (compProj 1)
  have hP0_gh : P_sig0 * P_gh0 = P_gh0 * P_sig0 := hCommGh_sig (compProj 0)
  have hP1_gh : P_sig1 * P_gh0 = P_gh0 * P_sig1 := hCommGh_sig (compProj 1)
  have hConjFixed {X : Operator (2 ^ (k + (m + 1 + 1)))} (hX : GG * X = X * GG) :
      (GG * X * GG) * P_gh0 = X * P_gh0 := by
    rw [hX, Matrix.mul_assoc X GG GG, hGG, Matrix.mul_one]
  have hConjLeft {R S S' : Operator (2 ^ (k + (m + 1 + 1)))} (hR : GG * R = R * GG)
      (hS : (GG * S * GG) * P_gh0 = S' * P_gh0) :
      (GG * (R * S) * GG) * P_gh0 = (R * S') * P_gh0 := by
    calc (GG * (R * S) * GG) * P_gh0
      _ = R * ((GG * S * GG) * P_gh0) := by
            rw [← Matrix.mul_assoc GG R S, hR]
            simp only [Matrix.mul_assoc]
      _ = (R * S') * P_gh0 := by rw [hS, ← Matrix.mul_assoc R S' P_gh0]
  have hConjRight {S S' R : Operator (2 ^ (k + (m + 1 + 1)))}
      (hR : GG * R = R * GG) (hRgh : R * P_gh0 = P_gh0 * R)
      (hS : (GG * S * GG) * P_gh0 = S' * P_gh0) :
      (GG * (S * R) * GG) * P_gh0 = (S' * R) * P_gh0 := by
    have h1 : GG * (S * R) * GG = (GG * S * GG) * R := by
      calc GG * (S * R) * GG = GG * S * (R * GG) := by simp only [Matrix.mul_assoc]
        _ = (GG * S * GG) * R := by
          rw [← hR]
          simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_assoc (GG * S * GG) R P_gh0, hRgh, ← Matrix.mul_assoc (GG * S * GG),
      hS, Matrix.mul_assoc S' P_gh0 R, ← hRgh, ← Matrix.mul_assoc S' R P_gh0]
  have hConjSeq {U V U' V' : Operator (2 ^ (k + (m + 1 + 1)))}
      (hU : (GG * U * GG) * P_gh0 = U' * P_gh0)
      (hV : (GG * V * GG) * P_gh0 = V' * P_gh0)
      (hVc : V' * P_gh0 = P_gh0 * V') :
      (GG * (U * V) * GG) * P_gh0 = (U' * V') * P_gh0 := by
    have hmid : GG * (U * V) * GG = (GG * U * GG) * (GG * V * GG) := by
      calc GG * (U * V) * GG = GG * U * (GG * GG) * V * GG := by
            rw [hGG]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (GG * U * GG) * (GG * V * GG) := by simp only [Matrix.mul_assoc]
    rw [hmid, Matrix.mul_assoc (GG * U * GG), hV, hVc, ← Matrix.mul_assoc (GG * U * GG),
      hU, Matrix.mul_assoc U' P_gh0 V', ← hVc, ← Matrix.mul_assoc U' V' P_gh0]
  have hConjBranch {A B A' B' : Operator (2 ^ (k + (m + 1 + 1)))}
      (hA : (GG * A * GG) * P_gh0 = A' * P_gh0)
      (hB : (GG * B * GG) * P_gh0 = B' * P_gh0) :
      (GG * (A * P_sig0 + B * P_sig1) * GG) * P_gh0 = (A' * P_sig0 + B' * P_sig1) * P_gh0 := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    rw [hConjRight hG0 hP0_gh hA, hConjRight hG1_sig hP1_gh hB]
  have h1G : (GG * 1 * GG) * P_gh0 = 1 * P_gh0 :=
    hConjFixed (by rw [Matrix.mul_one, Matrix.one_mul])
  have hStep : (GG * biWalkStepOp qSigG (rBEG.embedMatrix (laurentWalk U_BE))
      (rBEG.embedMatrix (laurentWalkInv U_BE)) * GG) * P_gh0 =
      biWalkStepOp qSigG WpG WpinvG * P_gh0 := by
    unfold biWalkStepOp
    exact hConjBranch hWG hWinvG
  have hLoopCommGh (t : ℕ) : biGqspLoopOp qSigG WpG WpinvG (biCS M C) t * P_gh0 =
      P_gh0 * biGqspLoopOp qSigG WpG WpinvG (biCS M C) t := by
    have hEqL : biGqspLoopOp qSigG WpG WpinvG (biCS M C) t =
        (rPhysInGhost k m).embedMatrix (biGqspLoopOp ⟨k + m, by omega⟩
          ((QRegister.block 0 (k + m) (by omega)).embedMatrix (physLaurentWalkGen b U_raw))
          ((QRegister.block 0 (k + m) (by omega)).embedMatrix (physLaurentWalkInvGen b U_raw))
          (biCS M C) t) := by
      rw [embedMatrix_biGqspLoopOp, rPhysInGhost_sig]
    rw [hEqL]
    exact hCommPhysGh _
  have hLoop (t : ℕ) : (GG * biGqspLoopOp qSigG (rBEG.embedMatrix (laurentWalk U_BE))
      (rBEG.embedMatrix (laurentWalkInv U_BE)) (biCS M C) t * GG) * P_gh0 =
      biGqspLoopOp qSigG WpG WpinvG (biCS M C) t * P_gh0 := by
    induction t with
    | zero =>
        dsimp only [biGqspLoopOp]
        exact hConjFixed (hCommG_sig _)
    | succ t ih =>
        dsimp only [biGqspLoopOp]
        exact hConjSeq (hConjLeft (hCommG_sig _) hStep) ih (hLoopCommGh t)
  have hH : (Circuit.H qSigG).eval.1 = (QRegister.singleton qSigG).embedMatrix Qubit.H.1 := by
    rw [Circuit.eval_single, QRegister.embedUnitary_val]
    rfl
  have hHG : GG * (Circuit.H qSigG).eval.1 = (Circuit.H qSigG).eval.1 * GG :=
    hH ▸ hCommG_sig Qubit.H.1
  have hHGh : (Circuit.H qSigG).eval.1 * P_gh0 = P_gh0 * (Circuit.H qSigG).eval.1 :=
    hH ▸ hCommGh_sig Qubit.H.1
  have hLeft : (GG * (rBEG.embedMatrix (laurentWalkInv U_BE) * P_sig0 + P_sig1) * GG) * P_gh0 =
      (WpinvG * P_sig0 + P_sig1) * P_gh0 := by
    have h := hConjBranch hWinvG h1G
    rw [Matrix.one_mul] at h
    exact h
  have hRight : (GG * (P_sig0 + rBEG.embedMatrix (laurentWalk U_BE) * P_sig1) * GG) * P_gh0 =
      (P_sig0 + WpG * P_sig1) * P_gh0 := by
    have h := hConjBranch h1G hWG
    rw [Matrix.one_mul] at h
    exact h
  have hRightCommGh : (P_sig0 + WpG * P_sig1) * P_gh0 = P_gh0 * (P_sig0 + WpG * P_sig1) := by
    simp only [Matrix.add_mul, Matrix.mul_add]
    rw [hP0_gh, Matrix.mul_assoc WpG P_sig1 P_gh0, hP1_gh,
      ← Matrix.mul_assoc WpG P_gh0 P_sig1, hCommPhysGh _, Matrix.mul_assoc]
  have hEmbSeg : (rPhysInGhost k m).embedMatrix (physBiSegmentUnitaryGen b M C U_raw).1 =
      biGqspSegmentOp qSigG WpG WpinvG (biCS M C) M := by
    dsimp only [physBiSegmentUnitaryGen]
    rw [embedMatrix_biGqspSegmentOp, rPhysInGhost_sig]
  rw [hEmbSeg]
  unfold biCatSegmentOp biGqspSegmentOp
  exact hConjRight hHG hHGh (hConjSeq (hConjSeq (hConjLeft hHG hLeft) (hLoop M) (hLoopCommGh M))
    hRight hRightCommGh)
theorem norm_le_of_embedMatrix_mul_proj {k n : ℕ} (r : QRegister k n) (q : Wire n)
    (hq : q ∉ Set.range r.wires) (D : Operator (2 ^ k)) : ‖D‖ ≤ ‖r.embedMatrix D *
    (QRegister.singleton q).basisOutcomeProjector 0‖ := by
  let P_q0 : Operator (2 ^ n) := (QRegister.singleton q).basisOutcomeProjector 0
  let TD := Matrix.toEuclideanCLM (n := Fin (2 ^ k)) (𝕜 := ℂ) D
  let TE := Matrix.toEuclideanCLM (n := Fin (2 ^ n)) (𝕜 := ℂ) (r.embedMatrix D * P_q0)
  rw [← Matrix.l2_opNorm_toEuclideanCLM D,
      ← Matrix.l2_opNorm_toEuclideanCLM (r.embedMatrix D * P_q0)]
  refine TD.opNorm_le_bound (norm_nonneg TE) fun v ↦ ?_
  let env0 : r.Environment → ZMod 2 := (r.basisSplitEquiv (0 : Fin (2 ^ n))).2
  let e0 : (r.Environment → ZMod 2) → ℂ := Pi.single env0 (1 : ℂ)
  let liftVec : (Fin (2 ^ k) → ℂ) → EuclideanSpace ℂ (Fin (2 ^ n)) :=
    fun u ↦ WithLp.toLp 2 (r.tensorState u e0)
  have hLiftNormSq (u : Fin (2 ^ k) → ℂ) :
      ‖liftVec u‖ ^ 2 = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin (2 ^ k)))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hPoint (x : Fin (2 ^ n)) : ‖(liftVec u).ofLp x‖ ^ 2 = ‖u (r.basisSplitEquiv x).1 * e0
        (r.basisSplitEquiv x).2‖ ^ 2 := by
      dsimp only [liftVec, QRegister.tensorState]
      rw [r.basisSplitEquiv_apply_fst]
    simp_rw [hPoint]
    have hSum : (∑ x : Fin (2 ^ n), ‖u (r.basisSplitEquiv x).1 * e0 (r.basisSplitEquiv x).2‖ ^
        2) = ∑ p : Fin (2 ^ k) × (r.Environment → ZMod 2), ‖u p.1 * e0 p.2‖ ^ 2 :=
        r.basisSplitEquiv.sum_comp (fun p : Fin (2 ^ k) × (r.Environment → ZMod 2) ↦ ‖u p.1 *
        e0 p.2‖ ^ 2)
    rw [hSum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single env0]
    · simp [e0]
    · intro b _ hb
      have h0 : e0 b = 0 := Pi.single_eq_of_ne hb 1
      simp [h0]
    · intro hm
      exact (hm (Finset.mem_univ _)).elim
  have hLiftNorm (u : Fin (2 ^ k) → ℂ) :
      ‖liftVec u‖ = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin (2 ^ k)))‖ := by
    have h := congrArg Real.sqrt (hLiftNormSq u)
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  let w : EuclideanSpace ℂ (Fin (2 ^ n)) := liftVec v.ofLp
  have hPq_w : P_q0.mulVec w.ofLp = w.ofLp := by
    funext x
    dsimp only [P_q0]
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mulVec_diagonal]
    by_cases hx : (QRegister.singleton q).extractIndex x = 0
    · simp [hx]
    · have hEnvNe : (r.basisSplitEquiv x).2 ≠ env0 := by
        intro hEnvEq
        have hAgree : r.AgreeOutside x (0 : Fin (2 ^ n)) :=
          (r.basisSplit_environment_eq_iff x (0 : Fin (2 ^ n))).mp hEnvEq
        have hBit0 : basisBits n x q = basisBits n (0 : Fin (2 ^ n)) q := hAgree q hq
        apply hx
        rw [zero_extract_iff_bits_zero]
        intro idx
        fin_cases idx
        change basisBits n x q = 0
        rw [hBit0, basisBits_zero_spine]
      have he0 : e0 (r.basisSplitEquiv x).2 = 0 := Pi.single_eq_of_ne hEnvNe 1
      simp [hx, w, liftVec, QRegister.tensorState, he0]
  have hAction : TE w = liftVec (D.mulVec v.ofLp) := by
    change WithLp.toLp 2 (TE w).ofLp = _
    rw [Matrix.ofLp_toEuclideanCLM, ← Matrix.mulVec_mulVec, hPq_w]
    exact congrArg (WithLp.toLp 2) (r.embedMatrix_mulVec_tensorState D v.ofLp e0)
  have hOutEq : TD v = WithLp.toLp 2 (D.mulVec v.ofLp) := by
    change WithLp.toLp 2 (TD v).ofLp = _
    rw [Matrix.ofLp_toEuclideanCLM]
  have hvEq : WithLp.toLp 2 v.ofLp = v := rfl
  calc ‖TD v‖
    _ = ‖(WithLp.toLp 2 (D.mulVec v.ofLp) : EuclideanSpace ℂ (Fin (2 ^ k)))‖ := by
        rw [hOutEq]
    _ = ‖liftVec (D.mulVec v.ofLp)‖ := (hLiftNorm (D.mulVec v.ofLp)).symm
    _ = ‖TE w‖ := by rw [hAction]
    _ ≤ ‖TE‖ * ‖w‖ := TE.le_opNorm w
    _ = ‖TE‖ * ‖v‖ := by rw [show ‖w‖ = ‖v‖ from (hLiftNorm v.ofLp).trans (congrArg norm hvEq)]
end BiGqspSegmentSpine
end
end ModWeighted3ABiGqspSegmentSpine

section ModWeighted3AOraAndPrepBundle
@[expose] public section
namespace OraAndPrepBundleAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end OraAndPrepBundleAlt
namespace SpecsAux.GhostGuardCircuitBridge
export SixSlotEndpointJunctionBridge (gridValidBool diagProj_gridValidBool_eq_specsGridProjector)
end SpecsAux.GhostGuardCircuitBridge
namespace OraAndPrepBundle
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open FullSysWalkStepEndpoint
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open FullSysPrepare6Slot
open PosMomSelectSandwich
open FullSysCatSegmentBridge
open FullSysFullPrepareAndTopConcrete
open PosMomSelectDynamic (unitaryConj unitaryConj_val)
open FullSysMomSlots0135Concrete
open NuclearTwistRealizes
open PosSlots24TopWrapper
open scoped Matrix Matrix.Norms.L2Operator BigOperators
instance (priority := 100000) instNeZeroTwoPowOra (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
def fin6Tuple {α : Type*} (a0 a1 a2 a3 a4 a5 : α) (k : Fin 6) : α :=
  match k.val with
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | _ => a5
@[simp] theorem fin6Tuple_0 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) : fin6Tuple a0 a1 a2 a3 a4 a5 0 =
    a0 := rfl
@[simp] theorem fin6Tuple_1 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) : fin6Tuple a0 a1 a2 a3 a4 a5 1 =
    a1 := rfl
@[simp] theorem fin6Tuple_2 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) : fin6Tuple a0 a1 a2 a3 a4 a5 2 =
    a2 := rfl
@[simp] theorem fin6Tuple_3 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) : fin6Tuple a0 a1 a2 a3 a4 a5 3 =
    a3 := rfl
@[simp] theorem fin6Tuple_4 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) : fin6Tuple a0 a1 a2 a3 a4 a5 4 =
    a4 := rfl
@[simp] theorem fin6Tuple_5 {α : Type*} (a0 a1 a2 a3 a4 a5 : α) : fin6Tuple a0 a1 a2 a3 a4 a5 5 =
    a5 := rfl
@[simp] theorem sum_fin6Tuple {α : Type*} [AddCommMonoid α] (a0 a1 a2 a3 a4 a5 : α) :
    (∑ k : Fin 6, fin6Tuple a0 a1 a2 a3 a4 a5 k) = a0 + a1 + a2 + a3 + a4 + a5 := by
  simp [Fin.sum_univ_six, add_assoc]
abbrev castNatUnitary {a b : ℕ} (h : a = b) (U : Unitary (2 ^ a)) : Unitary (2 ^ b) :=
  @Eq.rec ℕ a (fun d _ ↦ Unitary (2 ^ d)) U b h
abbrev castNatOp {a b : ℕ} (h : a = b) (M : Operator (2 ^ a)) : Operator (2 ^ b) :=
  @Eq.rec ℕ a (fun d _ ↦ Operator (2 ^ d)) M b h
abbrev castNatReg {a b n : ℕ} (h : a = b) (r : QRegister a n) : QRegister b n :=
  @Eq.rec ℕ a (fun d _ ↦ QRegister d n) r b h
theorem castNatOp_val_unitary {a b : ℕ} (h : a = b) (U : Unitary (2 ^ a)) :
    (castNatUnitary h U).1 = castNatOp h U.1 := by subst h; rfl
theorem castNatOp_mul {a b : ℕ} (h : a = b) (A B : Operator (2 ^ a)) :
    castNatOp h (A * B) = castNatOp h A * castNatOp h B := by subst h; rfl
theorem castNatOp_add {a b : ℕ} (h : a = b) (A B : Operator (2 ^ a)) :
    castNatOp h (A + B) = castNatOp h A + castNatOp h B := by subst h; rfl
theorem castNatOp_smul {a b : ℕ} (h : a = b) (z : ℂ) (A : Operator (2 ^ a)) :
    castNatOp h (z • A) = z • castNatOp h A := by subst h; rfl
theorem castNatOp_conjTranspose {a b : ℕ} (h : a = b) (A : Operator (2 ^ a)) :
    castNatOp h Aᴴ = (castNatOp h A)ᴴ := by subst h; rfl
theorem castNatUnitary_embedUnitary {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ = a₂) (hb : b₁ = b₂)
    (r₁ : QRegister a₁ b₁) (r₂ : QRegister a₂ b₂)
    (hr : ∀ i : Fin a₂, (r₁ (ha.symm ▸ i)).val = (r₂ i).val) (U : Unitary (2 ^ a₁)) :
    castNatUnitary hb (r₁.embedUnitary U) = r₂.embedUnitary (castNatUnitary ha U) := by
  subst ha
  subst hb
  have hreg : r₁ = r₂ := OraAndPrepBundleAlt.qreg_ext fun i ↦ Fin.ext (hr i)
  rw [hreg]
theorem castNatOp_slotBitProj {a b : ℕ} (h : a = b) (q₁ : Wire a) (q₂ : Wire b)
    (hq : q₁.val = q₂.val) (bit : Fin 2) :
    castNatOp h (slotBitProj q₁ bit) = slotBitProj q₂ bit := by
  subst h
  cases q₁; cases q₂
  dsimp at hq
  subst hq
  rfl
theorem castNatReg_disjoint {a b m n : ℕ} (h : a = b) (r : QRegister a n) (s : QRegister m n) :
    (castNatReg h r).DisjointWires s ↔ r.DisjointWires s := by subst h; exact Iff.rfl
theorem castNatCatReg_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {a b mCat mW n : ℕ} (hCore : a = b) (hCat : a + mCat = b + mCat) (rC : QRegister b n)
    (rP : QRegister mCat n) (rW : QRegister mW n) (hCP : rC.DisjointWires rP)
    (U : Unitary (2 ^ (a + mCat))) (d : DynamicCircuit Var n) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace ((castNatReg hCore.symm
    rC).concat rP ((castNatReg_disjoint hCore.symm rC rP).mpr hCP)) rW U d →
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rC.concat rP hCP) rW
    (castNatUnitary hCat U) d := by
  subst hCore
  have hh : hCat = rfl := Subsingleton.elim _ _
  subst hh
  exact id
theorem castNatCat_intertwines {a b mCat : ℕ} (hCore : a = b) (hCat : a + mCat = b + mCat)
    (U_cat : Unitary (2 ^ mCat)) (W : Unitary (2 ^ (a + mCat))) (U : Unitary (2 ^ a)) :
    IntertwinesCat ((QRegister.block a mCat le_rfl).embedUnitary U_cat).1
    ((QRegister.block a mCat le_rfl).basisOutcomeProjector 0) W.1 ((QRegister.block 0 a
    (fullSys_zero_add_le a mCat)).embedUnitary U).1 → IntertwinesLocalCat U_cat
    (castNatUnitary hCat W) (castNatUnitary hCore U) := by
  subst hCore
  have hh : hCat = rfl := Subsingleton.elim _ _
  subst hh
  intro h
  exact ⟨h.1, h.2.1, h.2.2⟩
theorem momCoreWires_eq_fullSysCoreWires (mPayload : ℕ) :
    momCoreWires mPayload = FullSysCatSegmentBridge.fullSysCoreWires mPayload := by
  dsimp [momCoreWires, momSelWires, FullSysCatSegmentBridge.fullSysCoreWires]
  omega
theorem momCatWires_eq_fullSysCatWires (mPayload mPGTwist : ℕ) : momCoreWires mPayload +
    mPGTwist = FullSysCatSegmentBridge.fullSysCoreWires mPayload + mPGTwist := by
  rw [momCoreWires_eq_fullSysCoreWires]
abbrev coreUnitaryToFullSys {mPayload : ℕ} (U : Unitary (2 ^ (momCoreWires mPayload))) :
    Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires mPayload)) := castNatUnitary
    (momCoreWires_eq_fullSysCoreWires mPayload) U
abbrev coreUnitaryFromFullSys {mPayload : ℕ}
    (U : Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires mPayload))) :
    Unitary (2 ^ (momCoreWires mPayload)) :=
  castNatUnitary (momCoreWires_eq_fullSysCoreWires mPayload).symm U
abbrev coreOpFromFullSys {mPayload : ℕ}
    (M : Operator (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires mPayload))) :
    Operator (2 ^ (momCoreWires mPayload)) :=
  castNatOp (momCoreWires_eq_fullSysCoreWires mPayload).symm M
abbrev catUnitaryToFullSys {mPayload mPGTwist : ℕ}
    (U : Unitary (2 ^ (momCoreWires mPayload + mPGTwist))) :
    Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires mPayload + mPGTwist)) :=
  castNatUnitary (momCatWires_eq_fullSysCatWires mPayload mPGTwist) U
abbrev coreRegToSym {mPayload n : ℕ}
    (r : QRegister (FullSysCatSegmentBridge.fullSysCoreWires mPayload) n) :
    QRegister (momCoreWires mPayload) n :=
  castNatReg (momCoreWires_eq_fullSysCoreWires mPayload).symm r
theorem op_sandwiched_proj_sub_eq {D : ℕ} (P G M H : Operator D) (hPG : P * G = P)
    (hGP : G * P = P) : P * (G * M * G - H) * P = P * (M - H) * P := by
  have hL : P * (G * M * G) * P = P * M * P := by
    calc P * (G * M * G) * P
        = (P * G) * M * (G * P) := by simp only [Matrix.mul_assoc]
      _ = P * M * P := by rw [hPG, hGP]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, hL]
theorem embedMatrix_neg_one_eq {k n : ℕ} (r : QRegister k n) :
    r.embedMatrix (-1 : Operator (2 ^ k)) = (-1 : Operator (2 ^ n)) := by
  have hneg : (-1 : Operator (2 ^ k)) = (-1 : ℂ) • (1 : Operator (2 ^ k)) := by
    rw [neg_one_smul]
  rw [hneg, QRegister.embedMatrix_smul, QRegister.embedMatrix_one, neg_one_smul]
theorem singleton_basisOutcomeProjector_eq_slotBitProj {K : ℕ} (q : Wire K) (b : Fin 2) :
    (QRegister.singleton ((QRegExt.ofFin K) q)).basisOutcomeProjector b = slotBitProj q b
    := by
  change (QRegister.singleton q).basisOutcomeProjector b = slotBitProj q b
  rw [QRegister.basisOutcomeProjector_eq_diagonal, slotBitProj]
  refine congrArg Matrix.diagonal (funext fun x ↦ if_congr ?_ rfl rfl)
  have hVal := CatalystPrep.singleton_extractIndex_val q x
  exact ⟨fun h ↦ hVal.symm.trans (congrArg Fin.val h), fun h ↦ Fin.ext (hVal.trans h)⟩
theorem coreAncSym_eq_momAncReg_sym (mPayload : ℕ) :
    FullSysFullPrepareAndTopConcrete.coreAncSym mPayload =
      FullSysMomSlots0135Concrete.momAncReg mPayload :=
  OraAndPrepBundleAlt.qreg_ext fun _ ↦ rfl
theorem selCoin3Sym_eq_momCoin3Sel_sym (mPayload : ℕ) :
    FullSysFullPrepareAndTopConcrete.selCoin3Sym mPayload =
      FullSysMomSlots0135Concrete.momCoin3Sel mPayload :=
  OraAndPrepBundleAlt.qreg_ext fun _ ↦ rfl
theorem coreSysSym_eq_momSysReg_sym (mPayload : ℕ) :
    FullSysFullPrepareAndTopConcrete.coreSysSym mPayload =
      FullSysMomSlots0135Concrete.momSysReg mPayload :=
  OraAndPrepBundleAlt.qreg_ext fun _ ↦ rfl
theorem corePayloadSym_eq_momPayloadReg_sym (mPayload : ℕ) :
    FullSysFullPrepareAndTopConcrete.corePayloadSym mPayload =
      FullSysMomSlots0135Concrete.momPayloadReg mPayload :=
  OraAndPrepBundleAlt.qreg_ext fun _ ↦ rfl
theorem coreHadamardUnitary_eq_mom_sym (mPayload : ℕ) :
    FullSysFullPrepareAndTopConcrete.coreHadamardUnitary mPayload =
      FullSysMomSlots0135Concrete.coreHadamardMom mPayload := by
  unfold FullSysFullPrepareAndTopConcrete.coreHadamardUnitary
    FullSysMomSlots0135Concrete.coreHadamardMom
  rw [corePayloadSym_eq_momPayloadReg_sym]
structure PosPostPrepCert (mPayload : ℕ) where
  mWorkPost : ℕ
  tPosPost : ℕ
  uPosPost : Unitary (2 ^ (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload))
  dPosPost : ∀ {Var : Type} {n : ℕ}, Var →
    QRegister (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload) n →
    QRegister mWorkPost n →
    DynamicCircuit Var n
  dPosPostInv : ∀ {Var : Type} {n : ℕ}, Var →
    QRegister (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload) n →
    QRegister mWorkPost n →
    DynamicCircuit Var n
  hToffPosPost : ∀ {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload) n)
    (rWork : QRegister mWorkPost n),
    (dPosPost v rCore rWork).count PrimitiveGate.TOFF = 0
  hToffPosPostInv : ∀ {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload) n)
    (rWork : QRegister mWorkPost n),
    (dPosPostInv v rCore rWork).count PrimitiveGate.TOFF = 0
  hTPosPost : ∀ {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload) n)
    (rWork : QRegister mWorkPost n),
    (dPosPost v rCore rWork).count PrimitiveGate.T ≤ tPosPost
  hTPosPostInv : ∀ {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload) n)
    (rWork : QRegister mWorkPost n),
    (dPosPostInv v rCore rWork).count PrimitiveGate.T ≤ tPosPost
  hRealPosPost : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var)
    (rCore : QRegister (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload) n)
    (rWork : QRegister mWorkPost n),
    rCore.DisjointWires rWork →
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCore rWork uPosPost (dPosPost v rCore rWork)
  hRealPosPostInv : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var)
    (rCore : QRegister (FullSysFullPrepareAndTopConcrete.coreWiresSym mPayload) n)
    (rWork : QRegister mWorkPost n),
    rCore.DisjointWires rWork →
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCore rWork uPosPost⁻¹ (dPosPostInv v rCore rWork)
  hPosPost_nonPos : ∀ c : Fin 8,2 ≤ c.val →
    uPosPost.1 * FullSysMomSlots0135Concrete.momCoinProj mPayload c =
      FullSysMomSlots0135Concrete.momCoinProj mPayload c
theorem fullSysQftCoreUnitary_comm_coinWire {mPayload : ℕ} (hmPay : 6 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (q : Wire (fullSysCoreWires mPayload)) (hq1 : 3924 ≤ q.val) (hq2 : q.val < 3954)
    (b : Fin 2) : (FullSysCatSegmentBridge.fullSysQftCoreUnitary hmPay qft).1 * slotBitProj
    q b = slotBitProj q b * (FullSysCatSegmentBridge.fullSysQftCoreUnitary hmPay qft).1
    := by
  have hDisj : (coreElecCosetB1Block hmPay).DisjointWires (QRegister.singleton
      ((QRegExt.ofFin (fullSysCoreWires mPayload)) q)) := by
    rw [QRegister.disjoint_iff]
    intro idx _
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · intro heq
      unfold coreElecCosetB1Block at heq
      rw [QRegister.concat_apply_left] at heq
      have hv : (coreElecBlock mPayload i).val = q.val := congrArg Fin.val heq
      have _ := i.isLt
      dsimp [coreElecBlock, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits,
          OraAndPrepBundleAlt.qreg_block_apply, OraAndPrepBundleAlt.qreg_block_wires_apply,
          OraAndPrepBundleAlt.qreg_whole_wires, OraAndPrepBundleAlt.emb_trans_apply,
          OraAndPrepBundleAlt.emb_refl_apply, OraAndPrepBundleAlt.emb_mk_apply] at hv
      omega
    · intro heq
      unfold coreElecCosetB1Block at heq
      rw [QRegister.concat_apply_right] at heq
      have hv : (coreCosetB1Block hmPay j).val = q.val := congrArg Fin.val heq
      have _ := j.isLt
      dsimp [coreCosetB1Block, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits,
          OraAndPrepBundleAlt.qreg_block_apply, OraAndPrepBundleAlt.qreg_block_wires_apply,
          OraAndPrepBundleAlt.qreg_whole_wires, OraAndPrepBundleAlt.emb_trans_apply,
          OraAndPrepBundleAlt.emb_refl_apply, OraAndPrepBundleAlt.emb_mk_apply] at hv
      omega
  have h :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint (coreElecCosetB1Block hmPay))
    (QRegister.singleton ((QRegExt.ofFin (fullSysCoreWires mPayload)) q))
    hDisj qft.uQft654.1 b
  rwa [singleton_basisOutcomeProjector_eq_slotBitProj] at h
abbrev PosSlots24DataOf (mPayload mWorkPos : ℕ) := PosSlots24DataGen
    (FullSysCatSegmentBridge.fullSysCoreWires mPayload)
    (FullSysCatSegmentBridge.iSlot2 mPayload) mWorkPos
abbrev PosSlots24Data80 (mWorkPos : ℕ) := PosSlots24DataOf 80 mWorkPos
abbrev posSlack2Prop {mPayload : ℕ}
    (uPos : Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires mPayload))) : Prop :=
  let P_c2 := slotBitProj (FullSysCatSegmentBridge.iSlot2 mPayload) 0 *
    slotBitProj (FullSysCatSegmentBridge.iSlot1 mPayload) 1 *
    slotBitProj (FullSysCatSegmentBridge.iSlot0 mPayload) 0
  uPos.1 * P_c2 = P_c2
abbrev posSlack3Prop {mPayload : ℕ}
    (uPos : Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires mPayload))) : Prop :=
  let P_c3 := slotBitProj (FullSysCatSegmentBridge.iSlot2 mPayload) 0 *
    slotBitProj (FullSysCatSegmentBridge.iSlot1 mPayload) 1 *
    slotBitProj (FullSysCatSegmentBridge.iSlot0 mPayload) 1
  uPos.1 * P_c3 = -P_c3
theorem slotBitProj_add_compl {K : ℕ} (w : Wire K) :
    slotBitProj w 0 + slotBitProj w 1 = (1 : Operator (2 ^ K)) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp only [slotBitProj, Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rcases (show (basisBits K x w).val = 0 ∨ (basisBits K x w).val = 1 by
      have := ZMod.val_lt (basisBits K x w); omega) with h0 | h1
    · simp [h0]
    · simp [h1]
  · simp [slotBitProj, hxy]
theorem momCoinProj_4567_eq_iSlot2_one (mPayload : ℕ) : momCoinProj mPayload 4 + momCoinProj
    mPayload 5 + momCoinProj mPayload 6 + momCoinProj mPayload 7 = slotBitProj
    (iSlot2Mom mPayload) 1 := by
  have h45 := momCoinProj_4_add_5_eq_slot45 mPayload
  have h67 := momCoinProj_6_add_7_eq_slot67 mPayload
  have hAdd : momCoinProj mPayload 4 + momCoinProj mPayload 5 + momCoinProj mPayload 6 +
      momCoinProj mPayload 7 = slot45MomProj mPayload + slot67MomProj mPayload := by
    rw [_root_.add_assoc (momCoinProj mPayload 4 + momCoinProj mPayload 5), h45, h67]
  rw [hAdd]
  unfold slot45MomProj slot67MomProj
  rw [← Matrix.mul_add, slotBitProj_add_compl, Matrix.mul_one]
theorem postPrep_nonPos_topBlock {mPayload : ℕ}
    (uPosPost S_raw : Unitary (2 ^ (momCoreWires mPayload)))
    (c : Fin 8)
    (hFix : uPosPost.1 * momCoinProj mPayload c = momCoinProj mPayload c) :
    let P_anc := (momAncReg mPayload).basisOutcomeProjector
      (coinSelOutcome (momCoin3Sel mPayload) c)
    P_anc * (unitaryConj (uPosPost * coreHadamardMom mPayload) S_raw).1 * P_anc =
      P_anc * (unitaryConj (coreHadamardMom mPayload) S_raw).1 * P_anc := by
  intro P_anc
  let P_c := momCoinProj mPayload c
  let H := coreHadamardMom mPayload
  have hPc_Ud : P_c * uPosPost.1ᴴ = P_c := by
    simpa only [P_c, Matrix.conjTranspose_mul, momCoinProj_conjTranspose] using
      congrArg Matrix.conjTranspose hFix
  have hHcomm : H.1 * P_c = P_c * H.1 := coreHadamardMom_comm_momCoinProj mPayload c
  have hHdComm : P_c * H.1ᴴ = H.1ᴴ * P_c := by
    simpa only [P_c, Matrix.conjTranspose_mul, momCoinProj_conjTranspose] using
      congrArg Matrix.conjTranspose hHcomm
  have hMP : P_c * P_anc = P_anc := momCoinProj_mul_ancOutcomeProj mPayload c
  have hPM : P_anc * P_c = P_anc := ancOutcomeProj_mul_momCoinProj mPayload c
  have hHP : H.1 * P_anc = P_c * (H.1 * P_anc) := by
    conv_lhs => rw [← hMP]
    rw [← Matrix.mul_assoc, hHcomm, Matrix.mul_assoc]
  have hPHd : P_anc * H.1ᴴ = (P_anc * H.1ᴴ) * P_c := by
    conv_lhs => rw [← hPM]
    rw [Matrix.mul_assoc P_anc P_c, hHdComm, ← Matrix.mul_assoc]
  rw [unitaryConj_mul_outer, unitaryConj_val, unitaryConj_val, unitaryConj_val]
  calc P_anc * (H.1ᴴ * (uPosPost.1ᴴ * S_raw.1 * uPosPost.1) * H.1) * P_anc
      = ((P_anc * H.1ᴴ) * (P_c * uPosPost.1ᴴ)) * S_raw.1 *
          ((uPosPost.1 * P_c) * (H.1 * P_anc)) := by
          conv_lhs => rw [← Matrix.mul_assoc P_anc, ← Matrix.mul_assoc P_anc, hPHd]
          conv_lhs => rw [Matrix.mul_assoc _ H.1 P_anc, hHP]
          simp only [Matrix.mul_assoc]
    _ = P_anc * (H.1ᴴ * S_raw.1 * H.1) * P_anc := by
          rw [hPc_Ud, hFix, ← hPHd, ← hHP]
          simp only [Matrix.mul_assoc]
theorem slackProj_eq_momCoinProj (mPayload : ℕ) (b : Fin 2) : slotBitProj (iSlot2Mom mPayload)
    0 * slotBitProj (iSlot1Mom mPayload) 1 * slotBitProj (iSlot0Mom mPayload) b = momCoinProj
    mPayload (if b.val = 0 then 2 else 3) := by
  let c : Fin 8 := if b.val = 0 then 2 else 3
  have hb_eq : coinBitFin2 c 0 = b ∧ coinBitFin2 c 1 = 1 ∧ coinBitFin2 c 2 = 0 := by
    fin_cases b <;> decide
  unfold momCoinProj
  change slotBitProj (iSlot2Mom mPayload) 0 * slotBitProj (iSlot1Mom mPayload) 1 * slotBitProj
    (iSlot0Mom mPayload) b = slotBitProj (iSlot0Mom mPayload) (coinBitFin2 c 0) * slotBitProj
    (iSlot1Mom mPayload) (coinBitFin2 c 1) * slotBitProj (iSlot2Mom mPayload) (coinBitFin2 c 2)
  rw [hb_eq.1, hb_eq.2.1, hb_eq.2.2,
    slotBitProj_comm_any (iSlot2Mom mPayload) (iSlot1Mom mPayload), Matrix.mul_assoc,
    slotBitProj_comm_any (iSlot2Mom mPayload) (iSlot0Mom mPayload), ← Matrix.mul_assoc,
    slotBitProj_comm_any (iSlot1Mom mPayload) (iSlot0Mom mPayload)]
theorem coreHadamard_conj_slack_block_gen {mPayload : ℕ} (b : Fin 2)
    (S_raw : Unitary (2 ^ (momCoreWires mPayload)))
    (hSlack :
      let P_slack := slotBitProj (iSlot2Mom mPayload) 0 * slotBitProj (iSlot1Mom mPayload) 1 *
          slotBitProj (iSlot0Mom mPayload) b
      S_raw.1 * P_slack = (if b.val = 0 then (1 : ℂ) else -1) • P_slack) :
    let c : Fin 8 := if b.val = 0 then 2 else 3
    let P_anc :=
      (momAncReg mPayload).basisOutcomeProjector (coinSelOutcome (momCoin3Sel mPayload) c)
    P_anc * (unitaryConj (coreHadamardMom mPayload) S_raw).1 * P_anc =
      P_anc * (momSysReg mPayload).embedMatrix
        (if b.val = 0 then (1 : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) else -1) * P_anc :=
          by
  intro c P_anc
  let P_c := momCoinProj mPayload c
  let H := coreHadamardMom mPayload
  have hSlackC : S_raw.1 * P_c = (if b.val = 0 then (1 : ℂ) else -1) • P_c :=
    (congrArg (S_raw.1 * ·) (slackProj_eq_momCoinProj mPayload b).symm).trans
      (hSlack.trans (congrArg (_ • ·) (slackProj_eq_momCoinProj mPayload b)))
  have hMP : P_c * P_anc = P_anc := momCoinProj_mul_ancOutcomeProj mPayload c
  have hHP : H.1 * P_anc = P_c * (H.1 * P_anc) := by
    conv_lhs => rw [← hMP]
    rw [← Matrix.mul_assoc, coreHadamardMom_comm_momCoinProj mPayload c, Matrix.mul_assoc]
  have hLHS : P_anc * (unitaryConj H S_raw).1 * P_anc =
      (if b.val = 0 then (1 : ℂ) else -1) • (P_anc * P_anc) := by
    rw [unitaryConj_val]
    calc P_anc * (H.1ᴴ * S_raw.1 * H.1) * P_anc
        = (P_anc * H.1ᴴ) * (S_raw.1 * P_c) * (H.1 * P_anc) := by
            conv_lhs =>
              simp only [Matrix.mul_assoc]
              rw [hHP]
            simp only [Matrix.mul_assoc]
      _ = (if b.val = 0 then (1 : ℂ) else -1) • (P_anc * (H.1ᴴ * H.1) * P_anc) := by
            rw [hSlackC, mul_smul_comm, smul_mul_assoc]
            congr 1
            simp only [Matrix.mul_assoc]
            rw [← hHP]
      _ = (if b.val = 0 then (1 : ℂ) else -1) • (P_anc * P_anc) := by
            rw [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp H.2,
              Matrix.mul_one]
  rw [hLHS]
  by_cases hb0 : b.val = 0 <;> simp [hb0, embedMatrix_neg_one_eq]
def posCoin01Proj (mPayload : ℕ) : Operator (2 ^ (fullSysCoreWires mPayload)) :=
  slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 0
def posCoin01ProjMom (mPayload : ℕ) : Operator (2 ^ (momCoreWires mPayload)) :=
  slotBitProj (iSlot2Mom mPayload) 0 * slotBitProj (iSlot1Mom mPayload) 0
theorem comm_slotBitProj_zero_of_comm_one {K : ℕ} (w : Wire K) (A : Operator (2 ^ K))
    (h1 : A * slotBitProj w 1 = slotBitProj w 1 * A) :
    A * slotBitProj w 0 = slotBitProj w 0 * A := by
  have h0 : slotBitProj w 0 = 1 - slotBitProj w 1 :=
    eq_sub_of_add_eq (slotBitProj_add_compl w)
  rw [h0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h1]
theorem comm_mul_of_comm {D : ℕ} (A P Q : Operator D) (hP : A * P = P * A)
    (hQ : A * Q = Q * A) : A * (P * Q) = (P * Q) * A := by
  rw [← Matrix.mul_assoc, hP, Matrix.mul_assoc, hQ, ← Matrix.mul_assoc]
theorem twoProj_conjTranspose {K : ℕ} (w₂ w₁ : Wire K) (b₂ b₁ : Fin 2) :
    (slotBitProj w₂ b₂ * slotBitProj w₁ b₁)ᴴ = slotBitProj w₂ b₂ * slotBitProj w₁ b₁ := by
  rw [Matrix.conjTranspose_mul, slotBitProj_self_adj, slotBitProj_self_adj,
    slotBitProj_comm_any w₁ w₂]
theorem threeProj_conjTranspose {K : ℕ} (w₂ w₁ w₀ : Wire K) (b₂ b₁ b₀ : Fin 2) :
    (slotBitProj w₂ b₂ * slotBitProj w₁ b₁ * slotBitProj w₀ b₀)ᴴ =
      slotBitProj w₂ b₂ * slotBitProj w₁ b₁ * slotBitProj w₀ b₀ := by
  rw[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, slotBitProj_self_adj,
      slotBitProj_self_adj, slotBitProj_self_adj, slotBitProj_comm_any w₁ w₂,
      ← Matrix.mul_assoc, slotBitProj_comm_any w₀ w₂, Matrix.mul_assoc,
      slotBitProj_comm_any w₀ w₁, ← Matrix.mul_assoc]
theorem threeProj_partition_eq_one {K : ℕ} (w₂ w₁ w₀ : Wire K) :
    (slotBitProj w₂ 0 * slotBitProj w₁ 0) + ((slotBitProj w₂ 0 * slotBitProj w₁ 1 *
    slotBitProj w₀ 0 + slotBitProj w₂ 0 * slotBitProj w₁ 1 * slotBitProj w₀ 1) + slotBitProj
    w₂ 1) = 1 := by
  have h23 : slotBitProj w₂ 0 * slotBitProj w₁ 1 * slotBitProj w₀ 0 + slotBitProj w₂ 0 *
      slotBitProj w₁ 1 * slotBitProj w₀ 1 = slotBitProj w₂ 0 * slotBitProj w₁ 1 := by
    rw [← Matrix.mul_add, slotBitProj_add_compl, Matrix.mul_one]
  rw [h23, ← _root_.add_assoc, ← Matrix.mul_add, slotBitProj_add_compl, Matrix.mul_one,
    slotBitProj_add_compl]
theorem selfAdj_comm_of_mul_eq_smul {D : ℕ} (M P : Operator D) (z : ℂ) (hM : Mᴴ = M)
    (hP : Pᴴ = P) (hz : star z = z) (hMP : M * P = z • P) : M * P = P * M := by
  have hPM : P * M = z • P := by
    have h := congrArg Matrix.conjTranspose hMP
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hM, hP, hz] using h
  exact hMP.trans hPM.symm
theorem posPhase_comm_posCoin01Proj {mPayload : ℕ}
    (M : Unitary (2 ^ (fullSysCoreWires mPayload)))
    (hSA : M.1ᴴ = M.1)
    (hOnP1 : M.1 * slotBitProj (iSlot2 mPayload) 1 = slotBitProj (iSlot2 mPayload) 1)
    (hSlack2 :
      let P_c2 := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
          slotBitProj (iSlot0 mPayload) 0
      M.1 * P_c2 = P_c2)
    (hSlack3 :
      let P_c3 := slotBitProj (iSlot2 mPayload) 0 * slotBitProj (iSlot1 mPayload) 1 *
          slotBitProj (iSlot0 mPayload) 1
      M.1 * P_c3 = -P_c3) :
    M.1 * posCoin01Proj mPayload = posCoin01Proj mPayload * M.1 := by
  have hC2 := selfAdj_comm_of_mul_eq_smul M.1 _ 1 hSA
    (threeProj_conjTranspose _ _ _ 0 1 0) (by simp) (by simpa [one_smul] using hSlack2)
  have hC3 := selfAdj_comm_of_mul_eq_smul M.1 _ (-1) hSA
    (threeProj_conjTranspose _ _ _ 0 1 1) (by simp) (by simpa [neg_one_smul] using hSlack3)
  have hC1 := selfAdj_comm_of_mul_eq_smul M.1 _ 1 hSA
    (slotBitProj_self_adj (iSlot2 mPayload) 1) (by simp) (by simpa [one_smul] using hOnP1)
  rw [posCoin01Proj, eq_sub_of_add_eq (threeProj_partition_eq_one (iSlot2 mPayload)
      (iSlot1 mPayload) (iSlot0 mPayload)), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
    hC2, hC3, hC1]
theorem postPrep_comm_posCoin01ProjMom {mPayload : ℕ}
    (uPosPost : Unitary (2 ^ (momCoreWires mPayload))) (hNonPos : ∀ c : Fin 8, 2 ≤ c.val →
    uPosPost.1 * momCoinProj mPayload c = momCoinProj mPayload c) : uPosPost.1 *
    posCoin01ProjMom mPayload = posCoin01ProjMom mPayload * uPosPost.1 := by
  let P_c2 := slotBitProj (iSlot2Mom mPayload) 0 * slotBitProj (iSlot1Mom mPayload) 1 *
    slotBitProj (iSlot0Mom mPayload) 0
  let P_c3 := slotBitProj (iSlot2Mom mPayload) 0 * slotBitProj (iSlot1Mom mPayload) 1 *
    slotBitProj (iSlot0Mom mPayload) 1
  let P₁ := slotBitProj (iSlot2Mom mPayload) 1
  let P_rest := (P_c2 + P_c3) + P₁
  have hFix2 : uPosPost.1 * P_c2 = P_c2 :=
    (congrArg (uPosPost.1 * ·) (slackProj_eq_momCoinProj mPayload 0)).trans
      ((hNonPos 2 (by decide)).trans (slackProj_eq_momCoinProj mPayload 0).symm)
  have hFix3 : uPosPost.1 * P_c3 = P_c3 :=
    (congrArg (uPosPost.1 * ·) (slackProj_eq_momCoinProj mPayload 1)).trans
      ((hNonPos 3 (by decide)).trans (slackProj_eq_momCoinProj mPayload 1).symm)
  have hFix1 : uPosPost.1 * P₁ = P₁ := by
    dsimp only [P₁]
    rw [← momCoinProj_4567_eq_iSlot2_one mPayload, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
      hNonPos 4 (by decide), hNonPos 5 (by decide), hNonPos 6 (by decide), hNonPos 7 (by decide)]
  have hU_rest : uPosPost.1 * P_rest = P_rest := by
    dsimp only [P_rest]
    rw [Matrix.mul_add, Matrix.mul_add, hFix2, hFix3, hFix1]
  have hUd_rest : uPosPost.1ᴴ * P_rest = P_rest := by
    nth_rw 1 [← hU_rest]
    rw [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff'.mp uPosPost.2, Matrix.one_mul]
  have hRest_sa : P_restᴴ = P_rest := by
    dsimp only [P_rest, P_c2, P_c3, P₁]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add,
      threeProj_conjTranspose _ _ _ 0 1 0, threeProj_conjTranspose _ _ _ 0 1 1,
      slotBitProj_self_adj]
  have hRest_U : P_rest * uPosPost.1 = P_rest := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRest_sa] using
      congrArg Matrix.conjTranspose hUd_rest
  unfold posCoin01ProjMom
  rw [eq_sub_of_add_eq (threeProj_partition_eq_one (iSlot2Mom mPayload) (iSlot1Mom mPayload)
      (iSlot0Mom mPayload)),
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hU_rest, hRest_U]
theorem postPrep_pos01_branch_eq {mPayload : ℕ}
    (uPosPost S_raw S_pos : Unitary (2 ^ (momCoreWires mPayload)))
    (c : Fin 8) (hc2 : coinBitFin2 c 2 = 0) (hc1 : coinBitFin2 c 1 = 0)
    (hCommP01 : uPosPost.1 * posCoin01ProjMom mPayload =
      posCoin01ProjMom mPayload * uPosPost.1)
    (hBranch01 : S_raw.1 * posCoin01ProjMom mPayload =
      S_pos.1 * posCoin01ProjMom mPayload) :
    let P_anc := (momAncReg mPayload).basisOutcomeProjector
      (coinSelOutcome (momCoin3Sel mPayload) c)
    P_anc * (unitaryConj (uPosPost * coreHadamardMom mPayload) S_raw).1 * P_anc =
      P_anc * (unitaryConj (uPosPost * coreHadamardMom mPayload) S_pos).1 * P_anc := by
  intro P_anc
  let P₀₁ := posCoin01ProjMom mPayload
  let W := uPosPost * coreHadamardMom mPayload
  have hH_P01 : (coreHadamardMom mPayload).1 * P₀₁ = P₀₁ * (coreHadamardMom mPayload).1 :=
    comm_mul_of_comm _ _ _
      (coreHadamardMom_comm_slotBitProj (by
        dsimp [iSlot2Mom]
        omega) 0)
      (coreHadamardMom_comm_slotBitProj (by
        dsimp [iSlot1Mom]
        omega) 0)
  have hW_P01 : W.1 * P₀₁ = P₀₁ * W.1 := by
    change (uPosPost.1 * (coreHadamardMom mPayload).1) * P₀₁ =
      P₀₁ * (uPosPost.1 * (coreHadamardMom mPayload).1)
    rw [Matrix.mul_assoc, hH_P01, ← Matrix.mul_assoc, hCommP01, Matrix.mul_assoc]
  let A := slotBitProj (iSlot0Mom mPayload) (coinBitFin2 c 0)
  let B := slotBitProj (iSlot1Mom mPayload) 0
  let C := slotBitProj (iSlot2Mom mPayload) 0
  have hBC : B * (A * B * C) = A * B * C := by
    rw [← Matrix.mul_assoc B (A * B), ← Matrix.mul_assoc B A B,
      slotBitProj_comm_any (iSlot1Mom mPayload) (iSlot0Mom mPayload),
      Matrix.mul_assoc A B B, slotBitProj_mul_idem]
  have hCC : C * (A * B * C) = A * B * C := by
    rw [← Matrix.mul_assoc C (A * B), ← Matrix.mul_assoc C A B,
      slotBitProj_comm_any (iSlot2Mom mPayload) (iSlot0Mom mPayload),
      Matrix.mul_assoc A C B, slotBitProj_comm_any (iSlot2Mom mPayload) (iSlot1Mom mPayload),
      ← Matrix.mul_assoc A B C, Matrix.mul_assoc (A * B) C C, slotBitProj_mul_idem]
  have hMP : momCoinProj mPayload c * P_anc = P_anc := momCoinProj_mul_ancOutcomeProj mPayload c
  have hP01_Panc : P₀₁ * P_anc = P_anc := by
    have hP01_Pc : P₀₁ * momCoinProj mPayload c = momCoinProj mPayload c := by
      unfold P₀₁ posCoin01ProjMom momCoinProj
      rw [hc1, hc2]
      exact (Matrix.mul_assoc C B (A * B * C)).trans ((congrArg (C * ·) hBC).trans hCC)
    conv_lhs => rw [← hMP]
    rw [← Matrix.mul_assoc, hP01_Pc, hMP]
  have hWP : W.1 * P_anc = P₀₁ * (W.1 * P_anc) := by
    conv_lhs => rw [← hP01_Panc]
    rw [← Matrix.mul_assoc, hW_P01, Matrix.mul_assoc]
  rw [unitaryConj_val, unitaryConj_val]
  calc P_anc * (W.1ᴴ * S_raw.1 * W.1) * P_anc
      = (P_anc * W.1ᴴ) * (S_raw.1 * P₀₁) * (W.1 * P_anc) := by
          conv_lhs =>
            simp only [Matrix.mul_assoc]
            rw [hWP]
          simp only [Matrix.mul_assoc]
    _ = (P_anc * W.1ᴴ) * (S_pos.1 * P₀₁) * (W.1 * P_anc) := by rw [hBranch01]
    _ = P_anc * (W.1ᴴ * S_pos.1 * W.1) * P_anc := by
          conv_rhs =>
            simp only [Matrix.mul_assoc]
            rw [hWP]
          simp only [Matrix.mul_assoc]
theorem fullSysSelectEffUnitary_on_momCoin_sym {mPayload mPGTwist : ℕ}
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (sel : FullSysCatSegmentBridge.FullSysSelectOracleBundle mPayload mPGTwist)
    (cfg : SpecsAux.SpecMirror.Configuration)
    (c : Fin 8) (hc2 : coinBitFin2 c 2 = 1) :
    let P_c := FullSysMomSlots0135Concrete.momCoinProj mPayload c
    (coreUnitaryFromFullSys (fullSysSelectEffUnitary qft sel cfg)).1 * P_c =
      (coreUnitaryFromFullSys (sel.uMomPhase cfg)).1 * P_c := by
  intro P_c
  let hEq := (momCoreWires_eq_fullSysCoreWires mPayload).symm
  have hS_split := fullSysSelectEffUnitary_conjTranspose_and_split qft sel cfg
  have hSplitSym : (coreUnitaryFromFullSys (fullSysSelectEffUnitary qft sel cfg)).1 =
      coreOpFromFullSys (fullSysSelectPosUnitary qft sel cfg).1 * slotBitProj
      (iSlot2Mom mPayload) 0 + (coreUnitaryFromFullSys (sel.uMomPhase cfg)).1 * slotBitProj
      (iSlot2Mom mPayload) 1 := by
    dsimp only [coreUnitaryFromFullSys, coreOpFromFullSys]
    rw [castNatOp_val_unitary, castNatOp_val_unitary, hS_split.1, castNatOp_add, castNatOp_mul,
      castNatOp_mul, castNatOp_slotBitProj hEq (iSlot2 mPayload) (iSlot2Mom mPayload) rfl 0,
      castNatOp_slotBitProj hEq (iSlot2 mPayload) (iSlot2Mom mPayload) rfl 1]
  have hPull (b : Fin 2) : slotBitProj (iSlot2Mom mPayload) b * P_c =
      slotBitProj (iSlot0Mom mPayload) (coinBitFin2 c 0) *
        slotBitProj (iSlot1Mom mPayload) (coinBitFin2 c 1) *
        (slotBitProj (iSlot2Mom mPayload) b * slotBitProj (iSlot2Mom mPayload) 1) := by
    change slotBitProj (iSlot2Mom mPayload) b * (slotBitProj (iSlot0Mom mPayload) (coinBitFin2
      c 0) * slotBitProj (iSlot1Mom mPayload) (coinBitFin2 c 1) * slotBitProj (iSlot2Mom
      mPayload) (coinBitFin2 c 2)) = _
    rw [hc2, Matrix.mul_assoc (slotBitProj (iSlot0Mom mPayload) _),
      ← Matrix.mul_assoc (slotBitProj (iSlot2Mom mPayload) b),
      slotBitProj_comm_any (iSlot2Mom mPayload) (iSlot0Mom mPayload),
      Matrix.mul_assoc (slotBitProj (iSlot0Mom mPayload) _),
      ← Matrix.mul_assoc (slotBitProj (iSlot2Mom mPayload) b),
      slotBitProj_comm_any (iSlot2Mom mPayload) (iSlot1Mom mPayload),
      Matrix.mul_assoc, Matrix.mul_assoc]
  have hP0 : slotBitProj (iSlot2Mom mPayload) 0 * P_c = 0 := by
    rw [hPull 0, slotBitProj_zero_mul_one_eq_zero, Matrix.mul_zero]
  have hP1 : slotBitProj (iSlot2Mom mPayload) 1 * P_c = P_c := by
    rw [hPull 1, slotBitProj_mul_idem, ← hc2]
    rfl
  rw [hSplitSym, Matrix.add_mul, Matrix.mul_assoc, hP0, Matrix.mul_zero, zero_add,
    Matrix.mul_assoc, hP1]
end OraAndPrepBundle
end
end ModWeighted3AOraAndPrepBundle

section ModCoinDispatchedBarrel288
@[expose] public section
namespace CoinDispatchedBarrel288
section ConfigCoinDispatchedBarrel288
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 256
namespace Internal
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open MeasureBranchHadamardSem (ket bitSign bit_cases matrix_ext_ket eval_seq_mulVec ket_X ket_Z
  ket_CNOT ket_TOFF ket_projector_zero projZeroAll ket_projZeroAll projZeroAll_conjTranspose
  projZeroAll_eq_basisOutcomeProjector_zero RealizesCleanUnitary)
open BchCubeDecoder StreamingBchComparator
open MomSlot0CircuitHalf (padZeroBits)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
theorem wire_ne_of_lt {M : ℕ} {a b : Wire M} (h : a.val < b.val) : a ≠ b :=
  fun heq ↦ absurd (congrArg Fin.val heq) (Nat.ne_of_lt h)
theorem wire_ne_of_gt {M : ℕ} {a b : Wire M} (h : b.val < a.val) : a ≠ b :=
  (wire_ne_of_lt h).symm
theorem dite_true_eq {c : Prop} {inst : Decidable c} (hc : c) {α : Sort*}
    {t : c → α} {e : ¬ c → α} : dite c t e = t hc := by
  cases inst with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h
theorem dite_false_eq {c : Prop} {inst : Decidable c} (hnc : ¬ c) {α : Sort*}
    {t : c → α} {e : ¬ c → α} : dite c t e = e hnc := by
  cases inst with
  | isTrue h => exact absurd h hnc
  | isFalse _ => rfl
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s := by
  cases r; cases s; congr; exact Function.Embedding.ext h
def bitsVal {k : ℕ} (f : Fin k → ZMod 2) : ℕ := ∑ i : Fin k, (f i).val * 2 ^ i.val
theorem mul_mulVec_prog {n : ℕ} (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (v : Fin (2 ^ n) → ℂ) : (A * B).mulVec v = A.mulVec (B.mulVec v) :=
  (Matrix.mulVec_mulVec v A B).symm
noncomputable def writeRegProg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBitsEquiv n).symm β) ((basisBitsEquiv k).symm γ))
@[simp] theorem writeRegProg_apply_reg {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i : Fin k) : writeRegProg β r γ (r i) = γ i := by
  simp [writeRegProg, QRegister.basisBits_replaceIndex_apply]
theorem writeRegProg_apply_of_not_mem {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (w : Wire n) (hw : w ∉ Set.range r.wires) :
    writeRegProg β r γ w = β w := by
  simp [writeRegProg, QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw]
noncomputable abbrev localIdxProg {k n : ℕ} (r : QRegister k n) (β : BitAssignment n) : Fin
    (2 ^ k) := (basisBitsEquiv k).symm (fun i ↦ β (r i))
theorem embedMatrix_mulVec_ket_prog {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ket β) =
      ∑ l : Fin (2 ^ k), A l (localIdxProg r β) • ket (writeRegProg β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBitsEquiv n).symm β) = localIdxProg r β := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeRegProg, ket, basisState]
inductive CliffProg (M : ℕ) where
  | nil : CliffProg M
  | x (q : Wire M) : CliffProg M
  | cnot (c t : Wire M) (h : c ≠ t) : CliffProg M
  | seq (c₁ c₂ : CliffProg M) : CliffProg M
namespace CliffProg
def eval {M : ℕ} : CliffProg M → BitAssignment M → BitAssignment M
  | .nil, β => β
  | .x q, β => Function.update β q (β q + 1)
  | .cnot c t _, β => Function.update β t (β t + β c)
  | .seq c₁ c₂, β => c₂.eval (c₁.eval β)
def inv {M : ℕ} : CliffProg M → CliffProg M
  | .nil => .nil
  | .x q => .x q
  | .cnot c t h => .cnot c t h
  | .seq c₁ c₂ => .seq c₂.inv c₁.inv
def toCircuit {M : ℕ} : CliffProg M → Circuit M
  | .nil => .identity
  | .x q => Circuit.X q
  | .cnot c t h => Circuit.CNOT c t h
  | .seq c₁ c₂ => c₁.toCircuit ;;ᶜ c₂.toCircuit
def onRegister {M n : ℕ} (r : QRegister M n) : CliffProg M → CliffProg n
  | .nil => .nil
  | .x q => .x (r q)
  | .cnot c t h => .cnot (r c) (r t) (r.wires.injective.ne h)
  | .seq c₁ c₂ => .seq (c₁.onRegister r) (c₂.onRegister r)
def SupportsBelow {M : ℕ} (bound : ℕ) : CliffProg M → Prop
  | .nil => True
  | .x q => q.val < bound
  | .cnot c t _ => c.val < bound ∧ t.val < bound
  | .seq c₁ c₂ => c₁.SupportsBelow bound ∧ c₂.SupportsBelow bound
@[simp]
theorem toCircuit_count_toff {M : ℕ} : ∀ c : CliffProg M, c.toCircuit.count PrimitiveGate.TOFF = 0
  | .nil => by simp [toCircuit]
  | .x _ => by simp [toCircuit]
  | .cnot _ _ _ => by simp [toCircuit]
  | .seq c₁ c₂ => by simp [toCircuit, toCircuit_count_toff]
@[simp]
theorem toCircuit_count_t {M : ℕ} : ∀ c : CliffProg M, c.toCircuit.count PrimitiveGate.T = 0
  | .nil => by simp [toCircuit]
  | .x _ => by simp [toCircuit]
  | .cnot _ _ _ => by simp [toCircuit]
  | .seq c₁ c₂ => by simp [toCircuit, toCircuit_count_t]
theorem toCircuit_eval_ket {M : ℕ} :
    ∀ (c : CliffProg M) (β : BitAssignment M),
      c.toCircuit.eval.1.mulVec (ket β) = ket (c.eval β)
  | .nil, _ => by simp [toCircuit, eval]
  | .x q, β => by rw [toCircuit, eval, ket_X]
  | .cnot c t h, β => by rw [toCircuit, eval, ket_CNOT]
  | .seq c₁ c₂, β => by
      rw [toCircuit, eval, eval_seq_mulVec, toCircuit_eval_ket c₁, toCircuit_eval_ket c₂]
theorem onRegister_toCircuit_eval {M n : ℕ} (r : QRegister M n) :
    ∀ c : CliffProg M, ((c.onRegister r).toCircuit).eval = (c.toCircuit.onRegister r).eval
  | .nil => by simp [onRegister, toCircuit]
  | .x q => by
      simp only [onRegister, toCircuit, Circuit.X, Circuit.single, Circuit.onRegister]
      congr 2
  | .cnot c t h => by
      simp only [onRegister, toCircuit, Circuit.CNOT, Circuit.onRegister]
      congr 2; apply qreg_ext; intro i; fin_cases i <;> rfl
  | .seq c₁ c₂ => by simp [onRegister, toCircuit, Circuit.eval_seq, onRegister_toCircuit_eval]
theorem inv_eval {M : ℕ} : ∀ (c : CliffProg M) (β : BitAssignment M), c.inv.eval (c.eval β) = β
  | .nil, _ => rfl
  | .x q, β => by
      funext w
      by_cases hw : w = q
      · subst hw
        have h11 : (1 + 1 : ZMod 2) = 0 := rfl
        simp [inv, eval, add_assoc, h11]
      · simp [inv, eval, Function.update_of_ne hw]
  | .cnot c t h, β => by
      funext w
      by_cases hw : w = t
      · subst hw
        simp [inv, eval, Function.update_of_ne h, add_assoc, CharTwo.add_self_eq_zero]
      · simp [inv, eval, Function.update_of_ne hw]
  | .seq c₁ c₂, β => by simp [inv, eval, inv_eval]
theorem eval_outside {M bound : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow bound →
      ∀ (β : BitAssignment M) (w : Wire M), bound ≤ w.val → c.eval β w = β w
  | .nil, _, _, _, _ => rfl
  | .x q, hq, β, w, hw =>
      Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le hq hw)) _ _
  | .cnot _ t _, ⟨_, ht⟩, β, w, hw =>
      Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le ht hw)) _ _
  | .seq c₁ c₂, ⟨h₁, h₂⟩, β, w, hw => by
      simp only [eval]
      rw [eval_outside c₂ h₂ _ w hw, eval_outside c₁ h₁ _ w hw]
theorem inv_supportsBelow {M bound : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow bound → c.inv.SupportsBelow bound
  | .nil, _ => trivial
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => ⟨inv_supportsBelow c₂ h₂, inv_supportsBelow c₁ h₁⟩
end CliffProg
inductive TempPhaseProg (m : ℕ) where
  | nil : TempPhaseProg m
  | cliff (c : CliffProg m) : TempPhaseProg m
  | z (q : Wire m) : TempPhaseProg m
  | seq (p₁ p₂ : TempPhaseProg m) : TempPhaseProg m
  | tempAnd (c₁ c₂ anc : Wire m) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (body : TempPhaseProg m) : TempPhaseProg m
namespace TempPhaseProg
def cnot {m : ℕ} (c t : Wire m) (h : c ≠ t) : TempPhaseProg m := .cliff (.cnot c t h)
def evalBits {m : ℕ} : TempPhaseProg m → BitAssignment m → BitAssignment m
  | .nil, β => β
  | .cliff c, β => c.eval β
  | .z _, β => β
  | .seq p₁ p₂, β => p₂.evalBits (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
      let β₂ := body.evalBits β₁
      Function.update β₂ anc (β₂ anc + β₂ c₁ * β₂ c₂)
def evalSign {m : ℕ} : TempPhaseProg m → BitAssignment m → ZMod 2
  | .nil, _ => 0
  | .cliff _, _ => 0
  | .z q, β => β q
  | .seq p₁ p₂, β => p₁.evalSign β + p₂.evalSign (p₁.evalBits β)
  | .tempAnd c₁ c₂ anc _ _ _ body, β =>
      body.evalSign (Function.update β anc (β anc + β c₁ * β c₂))
def countTempAnd {m : ℕ} : TempPhaseProg m → ℕ
  | .nil => 0
  | .cliff _ => 0
  | .z _ => 0
  | .seq p₁ p₂ => p₁.countTempAnd + p₂.countTempAnd
  | .tempAnd _ _ _ _ _ _ body => 1 + body.countTempAnd
def toToffCircuit {m : ℕ} : TempPhaseProg m → Circuit m
  | .nil => .identity
  | .cliff c => c.toCircuit
  | .z q => Circuit.Z q
  | .seq p₁ p₂ => p₁.toToffCircuit ;;ᶜ p₂.toToffCircuit
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a ;;ᶜ body.toToffCircuit ;;ᶜ
        Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a
def onRegister {m n : ℕ} (r : QRegister m n) : TempPhaseProg m → TempPhaseProg n
  | .nil => .nil
  | .cliff c => .cliff (c.onRegister r)
  | .z q => .z (r q)
  | .seq p₁ p₂ => .seq (p₁.onRegister r) (p₂.onRegister r)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .tempAnd (r c₁) (r c₂) (r anc)
        (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)
        (body.onRegister r)
def toDyn {Var : Type} {n : ℕ} (v : Var) : TempPhaseProg n → DynamicCircuit Var n
  | .nil => .circuit .identity
  | .cliff c => .circuit c.toCircuit
  | .z q => .circuit (Circuit.Z q)
  | .seq p₁ p₂ => .seq (p₁.toDyn v) (p₂.toDyn v)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body =>
      .seq (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
        (.seq (body.toDyn v) (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂))
@[simp] theorem onRegister_countTempAnd {m n : ℕ} (r : QRegister m n) :
    ∀ p : TempPhaseProg m, (p.onRegister r).countTempAnd = p.countTempAnd
  | .nil => rfl
  | .cliff _ => rfl
  | .z _ => rfl
  | .seq p₁ p₂ => by simp [onRegister, countTempAnd, onRegister_countTempAnd]
  | .tempAnd _ _ _ _ _ _ body => by simp [onRegister, countTempAnd, onRegister_countTempAnd]
@[simp] theorem toDyn_count_toff {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : TempPhaseProg n, (p.toDyn v).count PrimitiveGate.TOFF = 0
  | .nil => by simp [toDyn]
  | .cliff _ => by simp [toDyn]
  | .z _ => by simp [toDyn]
  | .seq p₁ p₂ => by simp [toDyn, toDyn_count_toff]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      simp [toDyn, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, toDyn_count_toff]
@[simp] theorem toDyn_count_t {Var : Type} {n : ℕ} (v : Var) :
    ∀ p : TempPhaseProg n, (p.toDyn v).count PrimitiveGate.T = 4 * p.countTempAnd
  | .nil => by simp [toDyn, countTempAnd]
  | .cliff _ => by simp [toDyn, countTempAnd]
  | .z _ => by simp [toDyn, countTempAnd]
  | .seq p₁ p₂ => by
      simp [toDyn, countTempAnd, toDyn_count_t]
      ring
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      simp [toDyn, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, countTempAnd, toDyn_count_t]
      ring
theorem bitSign_eq_neg_one_pow (b : ZMod 2) : bitSign b = (-1 : ℂ) ^ b.val := by
  rcases bit_cases b with rfl | rfl <;> norm_num [bitSign]
theorem neg_one_pow_zmod2_mul (a b : ZMod 2) :
    ((-1 : ℂ) ^ a.val) * ((-1 : ℂ) ^ b.val) = (-1 : ℂ) ^ (a + b).val := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · have h11 : (1 + 1 : ZMod 2) = 0 := rfl
    rw [h11]
    norm_num
theorem toToffCircuit_eval_ket {m : ℕ} :
    ∀ (p : TempPhaseProg m) (β : BitAssignment m),
      (p.toToffCircuit).eval.1.mulVec (ket β) =
        ((-1 : ℂ) ^ (p.evalSign β).val) • ket (p.evalBits β)
  | .nil, β => by simp [toToffCircuit, evalSign, evalBits]
  | .cliff c, β => by rw [toToffCircuit, evalSign, evalBits, c.toCircuit_eval_ket]; simp
  | .z q, β => by rw [toToffCircuit, evalSign, evalBits, ket_Z, bitSign_eq_neg_one_pow]
  | .seq p₁ p₂, β => by
      rw[toToffCircuit, eval_seq_mulVec, toToffCircuit_eval_ket p₁, Matrix.mulVec_smul,
          toToffCircuit_eval_ket p₂, smul_smul, neg_one_pow_zmod2_mul]
      rfl
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, β => by
      rw [toToffCircuit, eval_seq_mulVec, eval_seq_mulVec,
        ket_TOFF, toToffCircuit_eval_ket body, Matrix.mulVec_smul, ket_TOFF]
      rfl
theorem onRegister_toToffCircuit_eval {m n : ℕ} (r : QRegister m n) :
    ∀ p : TempPhaseProg m,
      ((p.onRegister r).toToffCircuit).eval = (p.toToffCircuit.onRegister r).eval
  | .nil => by simp [onRegister, toToffCircuit]
  | .cliff c => by simp [onRegister, toToffCircuit, c.onRegister_toCircuit_eval]
  | .z q => by
      simp only [onRegister, toToffCircuit, Circuit.Z, Circuit.single, Circuit.onRegister]
      congr 2
  | .seq p₁ p₂ => by
      simp [onRegister, toToffCircuit, Circuit.eval_seq, onRegister_toToffCircuit_eval]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body => by
      have htoff : (Circuit.TOFF (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)
          (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)).eval =
          ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).onRegister r).eval := by
        simp only [Circuit.TOFF, Circuit.onRegister]
        congr 2; apply qreg_ext; intro i; fin_cases i <;> rfl
      simp [onRegister, toToffCircuit, Circuit.eval_seq, htoff,
        onRegister_toToffCircuit_eval r body]
end TempPhaseProg
def cleanRem (M rem : ℕ) (β : BitAssignment M) : Prop :=
  ∀ w : Wire M, M - rem ≤ w.val → β w = 0
theorem cleanRem_anti {M rem₁ rem₂ : ℕ} (hle : rem₁ ≤ rem₂) {β : BitAssignment M}
    (h : cleanRem M rem₂ β) : cleanRem M rem₁ β := fun w hw ↦ h w (by omega)
def tailScr {M n : ℕ} (rComb : QRegister M n) (rem : ℕ) (h : rem ≤ M) : Fin rem → Wire n :=
  fun j ↦ rComb ⟨(M - rem) + j.val, by omega⟩
theorem tailScr_succ {M n : ℕ} (rComb : QRegister M n) (rem' : ℕ) (h : rem' + 1 ≤ M) :
    tailScr rComb (rem' + 1) h =
      Fin.cons (rComb ⟨M - (rem' + 1), by omega⟩) (tailScr rComb rem' (by omega)) := by
  funext j
  cases j using Fin.cases with
  | zero => simp only [Fin.cons_zero, tailScr, Fin.val_zero, add_zero]
  | succ i =>
      simp only [Fin.cons_succ, tailScr, Fin.val_succ]
      congr 1; ext; dsimp; omega
theorem projZeroAll_tailScr_sub {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    {rem₁ rem₂ : ℕ} (h₁ : rem₁ ≤ M) (h₂ : rem₂ ≤ M) (hle : rem₁ ≤ rem₂) : projZeroAll rem₁
    (tailScr rComb rem₁ h₁) * projZeroAll rem₂ (tailScr rComb rem₂ h₂) = projZeroAll rem₂
    (tailScr rComb rem₂ h₂) := by
  apply matrix_ext_ket
  intro β
  simp only [mul_mulVec_prog, ket_projZeroAll]
  by_cases hz₂ : ∀ j : Fin rem₂, β (tailScr rComb rem₂ h₂ j) = 0
  · have hz₁ : ∀ i : Fin rem₁, β (tailScr rComb rem₁ h₁ i) = 0 := by
      intro i
      have heq : tailScr rComb rem₁ h₁ i =
          tailScr rComb rem₂ h₂ ⟨(M - rem₁) - (M - rem₂) + i.val, by omega⟩ := by
        dsimp [tailScr]; congr 1; ext; dsimp; omega
      rw [heq]
      exact hz₂ _
    simp [hz₁, hz₂, ket_projZeroAll]
  · simp [hz₂]
def ValidCleanRem (M : ℕ) : ℕ → TempPhaseProg M → Prop
  | _, .nil => True
  | _, .cliff _ => True
  | _, .z _ => True
  | rem, .seq p₁ p₂ =>
      ∃ remMid : ℕ, remMid ≤ M ∧
        ValidCleanRem M rem p₁ ∧ ValidCleanRem M remMid p₂ ∧
        (∀ β : BitAssignment M, cleanRem M rem β → cleanRem M remMid (p₁.evalBits β))
  | rem, .tempAnd c₁ c₂ anc _ _ _ body =>
      M - rem ≤ anc.val ∧
        let rem' := M - (anc.val + 1)
        ValidCleanRem M rem' body ∧
          (∀ β₁ : BitAssignment M, cleanRem M rem' β₁ →
            body.evalBits β₁ c₁ = β₁ c₁ ∧
              body.evalBits β₁ c₂ = β₁ c₂ ∧
              body.evalBits β₁ anc = β₁ anc)
theorem eval_onRegister_prog_ket {M n : ℕ} (rComb : QRegister M n)
    (p : TempPhaseProg M) (β : BitAssignment n) :
    let γ : BitAssignment M := fun idx ↦ β (rComb idx)
    ((p.onRegister rComb).toToffCircuit).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (p.evalSign γ).val) • ket (writeRegProg β rComb (p.evalBits γ)) := by
  intro γ
  rw [p.onRegister_toToffCircuit_eval rComb, Circuit.eval_onRegister,
    QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
  have hloc : localIdxProg rComb β = (basisBitsEquiv M).symm γ := rfl
  rw [hloc]
  have hcol : ∀ l : Fin (2 ^ M), (p.toToffCircuit).eval.1 l ((basisBitsEquiv M).symm γ) = if l
      = (basisBitsEquiv M).symm (p.evalBits γ) then ((-1 : ℂ) ^ (p.evalSign γ).val) else 0
      := by
    intro l
    have hk := congrFun (p.toToffCircuit_eval_ket γ) l
    simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using hk
  simp_rw [hcol, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hbb : basisBits M ((basisBitsEquiv M).symm (p.evalBits γ)) = p.evalBits γ :=
    (basisBitsEquiv M).apply_symm_apply _
  rw [hbb]
theorem RealizesCleanUnitary_seq_asym {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {P₁ P₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {c₁ c₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂)
    (h₁ : RealizesCleanUnitary v P₁ c₁ U₁) (h₂ : RealizesCleanUnitary v P₂ c₂ U₂)
    (hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁) : RealizesCleanUnitary v P₁ (.seq c₁ c₂) (U₂ * U₁)
    := by
  refine ⟨fun Ψ hΨ σ val ↦ ?_, fun Θ hΘ σ ↦ ?_⟩
  · simp only [DynamicCircuit.compile_seq, wp_qSeq]
    exact h₁.1 (wp c₂.compile Ψ) (h₂.1 Ψ hΨ) σ val
  · have hΨ_inv := h₂.1 Θ hΘ
    have hadj : P₁ * U₁.1ᴴ * P₂ = P₁ * U₁.1ᴴ := by
      have h := congrArg conjTranspose hclean
      simpa [conjTranspose_mul, hP₁, hP₂, ← Matrix.mul_assoc] using h
    simp only [DynamicCircuit.compile_seq, wp_qSeq]
    rw [h₁.2 (wp c₂.compile Θ) hΨ_inv σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    calc
      ((wp c₂.compile Θ σ).1).conj (P₁ * U₁.1ᴴ)
        = (((wp c₂.compile Θ σ).1).conj P₂).conj (P₁ * U₁.1ᴴ) := by
            rw [conj_conj, hadj]
      _ = (((wpQAssignCompat U₂ Θ σ).1).conj P₂).conj (P₁ * U₁.1ᴴ) := by
            rw [h₂.2 Θ hΘ σ]
      _ = (Θ σ).1.conj (P₁ * (U₂ * U₁).1ᴴ) := by
            simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
              Matrix.star_eq_conjTranspose, conj_conj, Submonoid.coe_mul, conjTranspose_mul]
            rw [← Matrix.mul_assoc (P₁ * U₁.1ᴴ) P₂ U₂.1ᴴ, hadj, Matrix.mul_assoc]
theorem realizes_of_validCleanRem
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) :
    ∀ (p : TempPhaseProg M) (rem : ℕ) (hrem : rem ≤ M),
      ValidCleanRem M rem p →
      RealizesCleanUnitary v (projZeroAll rem (tailScr rComb rem hrem))
        ((p.onRegister rComb).toDyn v) (((p.onRegister rComb).toToffCircuit).eval)
  | .nil, rem, hrem, _ => RealizesCleanUnitary.circuit v _ _
  | .cliff _, rem, hrem, _ => RealizesCleanUnitary.circuit v _ _
  | .z _, rem, hrem, _ => RealizesCleanUnitary.circuit v _ _
  | .seq p₁ p₂, rem, hrem, ⟨remMid, hmid, hv₁, hv₂, hpres⟩ => by
      let P₁ := projZeroAll rem (tailScr rComb rem hrem)
      let P₂ := projZeroAll remMid (tailScr rComb remMid hmid)
      have hP₁ : P₁ᴴ = P₁ := projZeroAll_conjTranspose rem _
      have hP₂ : P₂ᴴ = P₂ := projZeroAll_conjTranspose remMid _
      have ih₁ := realizes_of_validCleanRem v rComb p₁ rem hrem hv₁
      have ih₂ := realizes_of_validCleanRem v rComb p₂ remMid hmid hv₂
      have hclean : P₂ * (((p₁.onRegister rComb).toToffCircuit).eval.1 * P₁) =
          ((p₁.onRegister rComb).toToffCircuit).eval.1 * P₁ := by
        apply matrix_ext_ket
        intro β
        simp only [P₁, P₂, mul_mulVec_prog, ket_projZeroAll]
        by_cases hz : ∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0
        · simp only [hz, imp_true_iff, ↓reduceIte, eval_onRegister_prog_ket,
            Matrix.mulVec_smul, ket_projZeroAll]
          have hγ : cleanRem M rem (fun idx ↦ β (rComb idx)) := by
            intro w hw
            have hj : w = ⟨(M - rem) + (w.val - (M - rem)), by omega⟩ := by
              ext; dsimp; omega
            rw [hj]
            exact hz ⟨w.val - (M - rem), by omega⟩
          have hout : ∀ j : Fin remMid, writeRegProg β rComb
              (p₁.evalBits (fun idx ↦ β (rComb idx))) (tailScr rComb remMid hmid j) = 0 := by
            intro j
            dsimp [tailScr]
            rw [writeRegProg_apply_reg]
            exact hpres _ hγ ⟨(M - remMid) + j.val, by omega⟩ (by dsimp; omega)
          simp only [hout, imp_true_iff, ↓reduceIte]
        · simp only [hz, ↓reduceIte, Matrix.mulVec_zero]
      have hseq := RealizesCleanUnitary_seq_asym hP₁ hP₂ ih₁ ih₂ hclean
      have heq : (p₂.onRegister rComb).toToffCircuit.eval *
          (p₁.onRegister rComb).toToffCircuit.eval =
          ((TempPhaseProg.seq p₁ p₂).onRegister rComb).toToffCircuit.eval := by
        simp [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
      simpa [TempPhaseProg.onRegister, TempPhaseProg.toDyn, heq] using hseq
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, rem, hrem, ⟨hanc_lo, hvBody, hpresBody⟩ => by
      have hanc_lt : anc.val < M := anc.isLt
      let rem' := M - (anc.val + 1)
      have hrem' : rem' ≤ M := by omega
      have hrem1 : rem' + 1 ≤ M := by omega
      have hrem_le : rem' + 1 ≤ rem := by omega
      have ihBody := realizes_of_validCleanRem v rComb body rem' hrem' hvBody
      have hanc_eq : anc = ⟨M - (rem' + 1), by omega⟩ := by
        ext; dsimp [rem']; omega
      have hdisj : ∀ j : Fin rem', rComb anc ≠ tailScr rComb rem' hrem' j := by
        intro j h
        have hinj := congrArg Fin.val (rComb.wires.injective h)
        dsimp [tailScr, rem'] at hinj
        omega
      let U_body := ((body.onRegister rComb).toToffCircuit).eval
      let U_clean :=
        (((TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister rComb).toToffCircuit).eval
      have hstep := RealizesCleanUnitary.withTempAnd_projZeroAll
        v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
        rem' (tailScr rComb rem' hrem') hdisj
        ((body.onRegister rComb).toDyn v) U_body U_clean ihBody
        (by
          intro β hanc0 _
          simp only [U_clean, U_body, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
            eval_seq_mulVec, ket_TOFF, hanc0, zero_add])
        (by
          intro β hanc0 hscr0
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          have hγ_anc : γ anc = 0 := hanc0
          let β₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
          have hγ₁_clean : cleanRem M rem' β₁ := by
            intro w hw
            have hw_ne : w ≠ anc := wire_ne_of_gt (by dsimp [rem'] at hw; omega)
            dsimp only [β₁]
            rw [Function.update_of_ne hw_ne]
            have hj : w = ⟨(M - rem') + (w.val - (M - rem')), by omega⟩ := by
              ext; dsimp; omega
            rw [hj]
            exact hscr0 ⟨w.val - (M - rem'), by omega⟩
          obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ hγ₁_clean
          have hfinal_anc :
              (TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).evalBits γ anc = 0 := by
            dsimp only [TempPhaseProg.evalBits]
            change Function.update (body.evalBits β₁) anc
              (body.evalBits β₁ anc + body.evalBits β₁ c₁ * body.evalBits β₁ c₂) anc = 0
            rw [Function.update_self, ha, hc₁, hc₂]
            simp [β₁, hγ_anc, Function.update_self, Function.update_of_ne h₁a,
              Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
          rw [show U_clean.1.mulVec (ket β) = _ from
              eval_onRegister_prog_ket rComb
                (TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body) β,
            Matrix.mulVec_smul, ket_projector_zero]
          rw [writeRegProg_apply_reg, hfinal_anc]
          simp)
      have hscr_eq : projZeroAll (rem' + 1) (Fin.cons (rComb anc) (tailScr rComb rem' hrem'))
          = projZeroAll (rem' + 1) (tailScr rComb (rem' + 1) hrem1) := by
        rw [hanc_eq, ← tailScr_succ rComb rem' hrem1]
      have hstep' : RealizesCleanUnitary v
          (projZeroAll (rem' + 1) (tailScr rComb (rem' + 1) hrem1))
          (((TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister rComb).toDyn v) U_clean :=
            by
        simpa [TempPhaseProg.onRegister, TempPhaseProg.toDyn, hscr_eq] using hstep
      exact RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (rem' + 1) _)
        (projZeroAll_conjTranspose rem _) (projZeroAll_tailScr_sub rComb hrem1 hrem hrem_le)
        hstep'
theorem validCleanRem_mono {M : ℕ} :
    ∀ {p : TempPhaseProg M} {rem₁ rem₂ : ℕ}, rem₁ ≤ rem₂ →
      ValidCleanRem M rem₁ p → ValidCleanRem M rem₂ p
  | .nil, _, _, _, _ => trivial
  | .cliff _, _, _, _, _ => trivial
  | .z _, _, _, _, _ => trivial
  | .seq _ _, _, _, hle, ⟨remMid, hmid, hv₁, hv₂, hpres⟩ =>
      ⟨remMid, hmid, validCleanRem_mono hle hv₁, hv₂,
        fun β hβ ↦ hpres β (cleanRem_anti hle hβ)⟩
  | .tempAnd _ _ _ _ _ _ _, _, _, hle, ⟨hanc, hvB, hpB⟩ =>
      ⟨by omega, hvB, hpB⟩
theorem PreservesStoreConst_toDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) : ∀ p : TempPhaseProg n, PreservesStoreConst (p.toDyn v)
  | .nil => PreservesStoreConst.circuit _
  | .cliff _ => PreservesStoreConst.circuit _
  | .z _ => PreservesStoreConst.circuit _
  | .seq p₁ p₂ =>
      PreservesStoreConst.seq (PreservesStoreConst_toDyn v p₁) (PreservesStoreConst_toDyn v p₂)
  | .tempAnd c₁ c₂ anc h₁₂ _ _ body =>
      PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq (PreservesStoreConst_toDyn v body)
          (PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂))
structure ScopedBlock (M rem : ℕ) (setup : BitAssignment M → BitAssignment M)
    (body : TempPhaseProg M) (p : TempPhaseProg M) : Prop where
  valid : ValidCleanRem M rem p
  bits : ∀ β : BitAssignment M, cleanRem M rem β → p.evalBits β = β
  sign : ∀ β : BitAssignment M, cleanRem M rem β → p.evalSign β = body.evalSign (setup β)
theorem ScopedBlock.z_kick {M rem : ℕ} (q : Wire M) :
    ScopedBlock M rem id (.z q) (.z q) where
  valid := trivial
  bits _ _ := rfl
  sign _ _ := rfl
theorem ScopedBlock.leaf_z {M : ℕ} (rem : ℕ) (_ : rem ≤ M) (q : Wire M) : ScopedBlock M rem id
    (.z q) (.z q) := ScopedBlock.z_kick q
theorem ScopedBlock.trans {M rem₁ rem₂ : ℕ}
    {s₁ s₂ : BitAssignment M → BitAssignment M}
    {leaf mid outer : TempPhaseProg M}
    (hOuter : ScopedBlock M rem₁ s₁ mid outer)
    (hInner : ScopedBlock M rem₂ s₂ leaf mid)
    (hClean : ∀ β, cleanRem M rem₁ β → cleanRem M rem₂ (s₁ β)) :
    ScopedBlock M rem₁ (s₂ ∘ s₁) leaf outer where
  valid := hOuter.valid
  bits := hOuter.bits
  sign β hβ := by
    rw [hOuter.sign β hβ, hInner.sign (s₁ β) (hClean β hβ), Function.comp_apply]
def withCliffAlloc {M : ℕ} (c : CliffProg M) (body : TempPhaseProg M) : TempPhaseProg M :=
  .seq (.cliff c) (.seq body (.cliff c.inv))
@[simp]
theorem withCliffAlloc_countTempAnd {M : ℕ} (c : CliffProg M) (body : TempPhaseProg M) :
    (withCliffAlloc c body).countTempAnd = body.countTempAnd := by
  simp [withCliffAlloc, TempPhaseProg.countTempAnd]
theorem ScopedBlock.withCliffAlloc_block {M rem remIn : ℕ}
    (hremIn : remIn ≤ M) (hle : remIn ≤ rem)
    (c : CliffProg M) (hc : c.SupportsBelow (M - remIn))
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M remIn sBody leaf body) :
    ScopedBlock M rem (sBody ∘ c.eval) leaf (withCliffAlloc c body) where
  valid := by
    refine ⟨remIn, hremIn, trivial, ?_, fun β hβ w hw ↦ ?_⟩
    · refine ⟨0, Nat.zero_le M, hBody.valid, trivial, fun _ _ w hw ↦ absurd hw (by omega)⟩
    · rw [TempPhaseProg.evalBits, c.eval_outside hc β w hw]
      exact hβ w (by omega)
  bits β hβ := by
    have hc_clean : cleanRem M remIn (c.eval β) := fun w hw ↦ by
      rw [c.eval_outside hc β w hw]
      exact hβ w (by omega)
    simp only [withCliffAlloc, TempPhaseProg.evalBits, hBody.bits (c.eval β) hc_clean, c.inv_eval]
  sign β hβ := by
    have hc_clean : cleanRem M remIn (c.eval β) := fun w hw ↦ by
      rw [c.eval_outside hc β w hw]
      exact hβ w (by omega)
    simp [withCliffAlloc, TempPhaseProg.evalSign, TempPhaseProg.evalBits,
      hBody.sign (c.eval β) hc_clean, Function.comp_apply]
def withTempBit {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (body : TempPhaseProg M) : TempPhaseProg M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body
@[simp] theorem withTempBit_countTempAnd {M : ℕ} (c₁ c₂ anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : TempPhaseProg M) :
    (withTempBit c₁ c₂ anc h₁₂ h₁a h₂a body).countTempAnd = 1 + body.countTempAnd := rfl
theorem ScopedBlock.withTempBit_block {M : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M) (c₁ c₂ : Wire M)
    (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < pos) (hc₂ : c₂.val < pos)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (pos + 1)) sBody leaf body) : ScopedBlock M (M - pos)
    (fun β ↦ sBody (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂))) leaf (withTempBit c₁ c₂
    ⟨pos, hpos⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) body) := by
  have h1a : c₁ ≠ ⟨pos, hpos⟩ := wire_ne_of_lt hc₁
  have h2a : c₂ ≠ ⟨pos, hpos⟩ := wire_ne_of_lt hc₂
  have hUpdClean {β : BitAssignment M} (hβ : cleanRem M (M - pos) β) :
      cleanRem M (M - (pos + 1)) (Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂)) := fun w hw ↦ by
    rw [Function.update_of_ne (wire_ne_of_gt (show pos < w.val by omega))]
    exact hβ w (by omega)
  refine ⟨⟨show M - (M - pos) ≤ pos by omega, hBody.valid, fun β₁ hβ₁ ↦ by
      rw [hBody.bits β₁ hβ₁]
      exact ⟨rfl, rfl, rfl⟩⟩, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
  · have hanc0 : β ⟨pos, hpos⟩ = 0 := hβ ⟨pos, hpos⟩ (show M - (M - pos) ≤ pos by omega)
    let β₁ := Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂)
    simp only [withTempBit, TempPhaseProg.evalBits, hanc0, zero_add]
    change Function.update (body.evalBits β₁) ⟨pos, hpos⟩
      (body.evalBits β₁ ⟨pos, hpos⟩ + body.evalBits β₁ c₁ * body.evalBits β₁ c₂) = β
    rw [hBody.bits β₁ (hUpdClean hβ)]
    funext w
    by_cases hw : w = ⟨pos, hpos⟩
    · subst hw
      simp [β₁, Function.update_self, Function.update_of_ne h1a, Function.update_of_ne h2a,
        CharTwo.add_self_eq_zero, hanc0]
    · simp [β₁, Function.update_of_ne hw]
  · have hanc0 : β ⟨pos, hpos⟩ = 0 := hβ ⟨pos, hpos⟩ (show M - (M - pos) ≤ pos by omega)
    simp only [withTempBit, TempPhaseProg.evalSign, hanc0, zero_add]
    exact hBody.sign _ (hUpdClean hβ)
def andXor {M : ℕ} (c₁ c₂ target anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (hat : anc ≠ target) : TempPhaseProg M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a
    (.cnot anc target hat)
@[simp] theorem andXor_countTempAnd {M : ℕ} (c₁ c₂ target anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hat : anc ≠ target) :
    (andXor c₁ c₂ target anc h₁₂ h₁a h₂a hat).countTempAnd = 1 := rfl
@[simp] theorem andXor_evalSign {M : ℕ} (c₁ c₂ target anc : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (hat : anc ≠ target) (β : BitAssignment M) :
    (andXor c₁ c₂ target anc h₁₂ h₁a h₂a hat).evalSign β = 0 := rfl
theorem andXor_valid_and_eval {M rem : ℕ}
    (c₁ c₂ target anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ target) (h₂t : c₂ ≠ target)
    (hc₁ : c₁.val < anc.val) (hc₂ : c₂.val < anc.val) (ht : target.val < anc.val)
    (hanc_rem : M - rem ≤ anc.val) :
    let p := andXor c₁ c₂ target anc h₁₂
      (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) (wire_ne_of_gt ht)
    ValidCleanRem M rem p ∧
      ∀ β : BitAssignment M, cleanRem M rem β →
        p.evalBits β = Function.update β target (β target + β c₁ * β c₂) := by
  intro p
  have h1a : c₁ ≠ anc := wire_ne_of_lt hc₁
  have h2a : c₂ ≠ anc := wire_ne_of_lt hc₂
  have hat : anc ≠ target := wire_ne_of_gt ht
  refine ⟨⟨hanc_rem, trivial, fun β₁ _ ↦ ?_⟩, fun β hβ ↦ ?_⟩
  · simp [TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval,
      Function.update_of_ne h₁t, Function.update_of_ne h₂t, Function.update_of_ne hat]
  · have hanc0 : β anc = 0 := hβ anc hanc_rem
    funext w
    by_cases hw_a : w = anc
    · subst hw_a
      simp [p, andXor, TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval, hanc0,
        Function.update_self, Function.update_of_ne h₁t, Function.update_of_ne h₂t,
        Function.update_of_ne hat, Function.update_of_ne h1a, Function.update_of_ne h2a,
        CharTwo.add_self_eq_zero]
    · by_cases hw_t : w = target
      · subst hw_t
        simp [p, andXor, TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval, hanc0,
          Function.update_self, Function.update_of_ne hw_a]
      · simp [p, andXor, TempPhaseProg.cnot, TempPhaseProg.evalBits, CliffProg.eval,
          Function.update_of_ne hw_a, Function.update_of_ne hw_t]
theorem realizes_signedPerm_cleanWorkspace
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kAct mClean mWork : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n)
    (hdisj : rAct.DisjointWires rWork) (hw_len : mClean ≤ mWork)
    (U : Unitary (2 ^ kAct))
    (perm : BitAssignment kAct → BitAssignment kAct)
    (phase : BitAssignment kAct → ZMod 2)
    (hU : ∀ α : BitAssignment kAct,
      U.1.mulVec (ket α) = ((-1 : ℂ) ^ (phase α).val) • ket (perm α))
    (p : TempPhaseProg (kAct + mClean))
    (hValid : ValidCleanRem (kAct + mClean) mClean p)
    (hBits : ∀ α : BitAssignment kAct, p.evalBits (padZeroBits α) = padZeroBits (perm α))
    (hSign : ∀ α : BitAssignment kAct, p.evalSign (padZeroBits α) = phase α) :
    let rSub : QRegister mClean n := rWork.slice 0 mClean (by omega)
    let rComb : QRegister (kAct + mClean) n := rAct.concat rSub (hdisj.compose_right _)
    let dyn := (p.onRegister rComb).toDyn v
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork U dyn ∧
      dyn.count PrimitiveGate.TOFF = 0 ∧
      dyn.count PrimitiveGate.T = 4 * p.countTempAnd := by
  intro rSub rComb dyn
  refine ⟨?_, TempPhaseProg.toDyn_count_toff v _, by
    rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd]⟩
  have hrem : mClean ≤ kAct + mClean := Nat.le_add_left mClean kAct
  have hSmall := realizes_of_validCleanRem v rComb p mClean hrem hValid
  let P_small := projZeroAll mClean (tailScr rComb mClean hrem)
  let P_work := projZeroAll mWork rWork.wires
  have hPs : P_smallᴴ = P_small := projZeroAll_conjTranspose mClean _
  have hPw : P_workᴴ = P_work := projZeroAll_conjTranspose mWork _
  have htail_work : ∀ j : Fin mClean,
      tailScr rComb mClean hrem j = rWork ⟨j.val, by omega⟩ := by
    intro j
    dsimp [tailScr, rComb, rSub]
    have hidx : (⟨(kAct + mClean - mClean) + j.val, by omega⟩ : Fin (kAct + mClean)) =
        Fin.natAdd kAct j := by
      ext; dsimp; omega
    rw [hidx, QRegister.concat_apply_right, QRegister.slice_apply]
    congr 1; ext; dsimp; omega
  have hsub : P_small * P_work = P_work := by
    apply matrix_ext_ket
    intro β
    simp only [P_small, P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · have hs : ∀ j : Fin mClean, β (tailScr rComb mClean hrem j) = 0 := by
        intro j; rw [htail_work j]; exact hw ⟨j.val, by omega⟩
      simp [hw, hs, ket_projZeroAll]
    · simp [hw]
  have hMono := RealizesCleanUnitary.mono_proj hPs hPw hsub hSmall
  have hUeq : ((p.onRegister rComb).toToffCircuit).eval.1 * P_work =
      (rAct.embedUnitary U).1 * P_work := by
    apply matrix_ext_ket
    intro β
    simp only [P_work, mul_mulVec_prog, ket_projZeroAll]
    by_cases hw : ∀ i : Fin mWork, β (rWork i) = 0
    · simp only [hw, imp_true_iff, ↓reduceIte, eval_onRegister_prog_ket]
      let α : BitAssignment kAct := fun i ↦ β (rAct i)
      have hpad : (fun idx ↦ β (rComb idx)) = padZeroBits α := by
        funext idx
        refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
        · simp [rComb, padZeroBits, α]
        · simp only [rComb, QRegister.concat_apply_right, padZeroBits, Fin.addCases_right]
          have hj' : rSub j = rWork ⟨j.val, by omega⟩ := by
            rw [QRegister.slice_apply]; congr 1; ext; dsimp; omega
          rw [hj']
          exact hw _
      rw [hpad, hBits α, hSign α]
      have hwComb : writeRegProg β rComb (padZeroBits (perm α)) = writeRegProg β rAct (perm α) := by
        funext w
        by_cases hmem : w ∈ Set.range rComb.wires
        · obtain ⟨idx, rfl⟩ := hmem
          rw [writeRegProg_apply_reg]
          refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
          · simp [rComb, padZeroBits]
          · simp only [rComb, QRegister.concat_apply_right, padZeroBits, Fin.addCases_right]
            have hnotAct : rSub j ∉ Set.range rAct.wires := by
              rintro ⟨i, hi⟩
              exact hdisj.ne i ⟨j.val, by omega⟩ (by
                rw [hi, QRegister.slice_apply]; congr 1; ext; dsimp; omega)
            rw [writeRegProg_apply_of_not_mem _ _ _ _ hnotAct]
            have hj' : rSub j = rWork ⟨j.val, by omega⟩ := by
              rw [QRegister.slice_apply]; congr 1; ext; dsimp; omega
            rw [hj']
            exact (hw _).symm
        · have hnotAct : w ∉ Set.range rAct.wires := by
            rintro ⟨i, rfl⟩
            exact hmem ⟨Fin.castAdd mClean i, by simp [rComb]⟩
          rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem,
            writeRegProg_apply_of_not_mem _ _ _ _ hnotAct]
      rw [hwComb, QRegister.embedUnitary_val, embedMatrix_mulVec_ket_prog]
      have hloc : localIdxProg rAct β = (basisBitsEquiv kAct).symm α := rfl
      rw [hloc]
      have hEvalAct : ∀ l : Fin (2 ^ kAct), U.1 l ((basisBitsEquiv kAct).symm α) = if l =
          (basisBitsEquiv kAct).symm (perm α) then ((-1 : ℂ) ^ (phase α).val) else 0 := by
        intro l
        have hk := congrFun (hU α) l
        simpa [ket, basisState, Matrix.mulVec_single_one, Pi.single_apply, eq_comm] using hk
      simp_rw [hEvalAct, ite_smul, zero_smul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hbb : basisBits kAct ((basisBitsEquiv kAct).symm (perm α)) = perm α :=
        (basisBitsEquiv kAct).apply_symm_apply _
      rw [hbb]
    · simp [hw]
  have hTarget := RealizesCleanUnitary.congr_unitary hPw hMono hUeq
  intro M_obs
  obtain ⟨M_out, hM_out⟩ := PreservesStoreConst_toDyn v (p.onRegister rComb) M_obs
  refine ⟨M_out, hM_out, ?_⟩
  have hconj := hTarget.2 (fun _ ↦ M_obs) (fun _ _ ↦ rfl) default
  have hM_eq : wp dyn.compile (fun _ ↦ M_obs) default = M_out := by
    dsimp [dyn]; rw [hM_out]
  rw [← hM_eq, ← projZeroAll_eq_basisOutcomeProjector_zero rWork]
  simpa [P_work, hPw, wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, HermitianMat.conj_apply_mat, Matrix.mul_assoc] using
    congrArg Subtype.val hconj
theorem CliffProg.supportsBelow_mono {M b₁ b₂ : ℕ} (hle : b₁ ≤ b₂) :
    ∀ {c : CliffProg M}, c.SupportsBelow b₁ → c.SupportsBelow b₂
  | .nil, _ => trivial
  | .x _, h => lt_of_lt_of_le h hle
  | .cnot _ _ _, ⟨hc, ht⟩ => ⟨lt_of_lt_of_le hc hle, lt_of_lt_of_le ht hle⟩
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨supportsBelow_mono hle h₁, supportsBelow_mono hle h₂⟩
def CliffDisjoint {M : ℕ} (mutW : Wire M → Prop) : CliffProg M → Prop
  | .nil => True
  | .x q => ¬ mutW q
  | .cnot c t _ => ¬ mutW c ∧ ¬ mutW t
  | .seq c₁ c₂ => CliffDisjoint mutW c₁ ∧ CliffDisjoint mutW c₂
theorem CliffDisjoint.inv {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {c : CliffProg M}, CliffDisjoint mutW c → CliffDisjoint mutW c.inv
  | .nil, _ => trivial
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨h₂.inv, h₁.inv⟩
theorem CliffDisjoint.eval_mut {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {c : CliffProg M}, CliffDisjoint mutW c →
      ∀ (β : BitAssignment M) {w : Wire M}, mutW w → c.eval β w = β w
  | .nil, _, _, _, _ => rfl
  | .x q, hq, β, w, hw => by
      dsimp [CliffProg.eval]
      exact Function.update_of_ne (fun heq : w = q ↦ hq (heq ▸ hw)) _ _
  | .cnot _ t _, ⟨_, hnt⟩, β, w, hw => by
      dsimp [CliffProg.eval]
      exact Function.update_of_ne (fun heq : w = t ↦ hnt (heq ▸ hw)) _ _
  | .seq _ _, ⟨h₁, h₂⟩, β, _, hw => by
      dsimp [CliffProg.eval]
      rw [h₂.eval_mut _ hw, h₁.eval_mut _ hw]
theorem CliffDisjoint.eval_congr_nonMut {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {c : CliffProg M}, CliffDisjoint mutW c →
      ∀ {β₁ β₂ : BitAssignment M},
        (∀ w, ¬ mutW w → β₁ w = β₂ w) →
        ∀ w, ¬ mutW w → c.eval β₁ w = c.eval β₂ w
  | .nil, _, _, _, hEq, w, hw => hEq w hw
  | .x q, hq, β₁, β₂, hEq, w, hw => by
      dsimp [CliffProg.eval]
      by_cases hwq : w = q
      · subst hwq; simp [Function.update_self, hEq w hq]
      · simp [Function.update_of_ne hwq, hEq w hw]
  | .cnot c t _, ⟨hnc, hnt⟩, β₁, β₂, hEq, w, hw => by
      dsimp [CliffProg.eval]
      by_cases hwt : w = t
      · subst hwt; simp [Function.update_self, hEq w hnt, hEq c hnc]
      · simp [Function.update_of_ne hwt, hEq w hw]
  | .seq _ _, ⟨h₁, h₂⟩, _, _, hEq, w, hw =>
      h₂.eval_congr_nonMut (fun u hu ↦ h₁.eval_congr_nonMut hEq u hu) w hw
inductive TempCtx (M : ℕ) where
  | hole : TempCtx M
  | seqPre (c : CliffProg M) (K : TempCtx M) : TempCtx M
  | seqPost (K : TempCtx M) (c : CliffProg M) : TempCtx M
  | tempAnd (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (K : TempCtx M) : TempCtx M
namespace TempCtx
def plug {M : ℕ} : TempCtx M → TempPhaseProg M → TempPhaseProg M
  | .hole, body => body
  | .seqPre c K, body => .seq (.cliff c) (K.plug body)
  | .seqPost K c, body => .seq (K.plug body) (.cliff c)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, body => .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (K.plug body)
def append {M : ℕ} : TempCtx M → TempCtx M → TempCtx M
  | .hole, G => G
  | .seqPre c K, G => .seqPre c (K.append G)
  | .seqPost K c, G => .seqPost (K.append G) c
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, G => .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (K.append G)
theorem append_plug {M : ℕ} (F G : TempCtx M) (body : TempPhaseProg M) :
    (F.append G).plug body = F.plug (G.plug body) := by
  induction F with
  | hole => rfl
  | seqPre _ _ ih => simp [append, plug, ih]
  | seqPost _ _ ih => simp [append, plug, ih]
  | tempAnd _ _ _ _ _ _ _ ih => simp [append, plug, ih]
def countTempAnd {M : ℕ} : TempCtx M → ℕ
  | .hole => 0
  | .seqPre _ K => K.countTempAnd
  | .seqPost K _ => K.countTempAnd
  | .tempAnd _ _ _ _ _ _ K => 1 + K.countTempAnd
@[simp] theorem plug_countTempAnd {M : ℕ} (K : TempCtx M) (body : TempPhaseProg M) :
    (K.plug body).countTempAnd = K.countTempAnd + body.countTempAnd := by
  induction K with
  | hole => simp [plug, countTempAnd]
  | seqPre _ _ ih => simp [plug, countTempAnd, TempPhaseProg.countTempAnd, ih]
  | seqPost _ _ ih => simp [plug, countTempAnd, TempPhaseProg.countTempAnd, ih]
  | tempAnd _ _ _ _ _ _ _ ih =>
      simp only [plug, countTempAnd, TempPhaseProg.countTempAnd, ih]
      omega
def fwdBits {M : ℕ} : TempCtx M → BitAssignment M → BitAssignment M
  | .hole, β => β
  | .seqPre c K, β => K.fwdBits (c.eval β)
  | .seqPost K _, β => K.fwdBits β
  | .tempAnd c₁ c₂ anc _ _ _ K, β => K.fwdBits (Function.update β anc (β anc + β c₁ * β c₂))
def DisjointFrom {M : ℕ} (mutW : Wire M → Prop) : TempCtx M → Prop
  | .hole => True
  | .seqPre c K => CliffDisjoint mutW c ∧ K.DisjointFrom mutW
  | .seqPost K c => K.DisjointFrom mutW ∧ CliffDisjoint mutW c
  | .tempAnd c₁ c₂ anc _ _ _ K => ¬ mutW c₁ ∧ ¬ mutW c₂ ∧ ¬ mutW anc ∧ K.DisjointFrom mutW
def SupportsBelowCtx {M : ℕ} (curHole : ℕ) : TempCtx M → Prop
  | .hole => True
  | .seqPre c K => c.SupportsBelow curHole ∧ K.SupportsBelowCtx curHole
  | .seqPost K c => K.SupportsBelowCtx curHole ∧ c.SupportsBelow curHole
  | .tempAnd _ _ anc _ _ _ K => anc.val < curHole ∧ K.SupportsBelowCtx curHole
theorem disjointFrom_append {M : ℕ} {mutW : Wire M → Prop} {F G : TempCtx M}
    (hF : F.DisjointFrom mutW) (hG : G.DisjointFrom mutW) :
    (F.append G).DisjointFrom mutW := by
  induction F with
  | hole => exact hG
  | seqPre _ _ ih => exact ⟨hF.1, ih hF.2⟩
  | seqPost _ _ ih => exact ⟨ih hF.1, hF.2⟩
  | tempAnd _ _ _ _ _ _ _ ih => exact ⟨hF.1, hF.2.1, hF.2.2.1, ih hF.2.2.2⟩
theorem supportsBelowCtx_append {M : ℕ} {c₁ c₂ : ℕ} {F G : TempCtx M} (hle : c₁ ≤ c₂)
    (hF : F.SupportsBelowCtx c₁) (hG : G.SupportsBelowCtx c₂) :
    (F.append G).SupportsBelowCtx c₂ := by
  induction F with
  | hole => exact hG
  | seqPre _ _ ih => exact ⟨CliffProg.supportsBelow_mono hle hF.1, ih hF.2⟩
  | seqPost _ _ ih => exact ⟨ih hF.1, CliffProg.supportsBelow_mono hle hF.2⟩
  | tempAnd _ _ _ _ _ _ _ ih => exact ⟨lt_of_lt_of_le hF.1 hle, ih hF.2⟩
theorem plug_evalSign {M : ℕ} (K : TempCtx M) (body : TempPhaseProg M) (β : BitAssignment M) :
    (K.plug body).evalSign β = body.evalSign (K.fwdBits β) := by
  induction K generalizing β with
  | hole => rfl
  | seqPre c _ ih => simp [plug, fwdBits, TempPhaseProg.evalSign, TempPhaseProg.evalBits, ih]
  | seqPost _ c ih => simp [plug, fwdBits, TempPhaseProg.evalSign, ih]
  | tempAnd _ _ _ _ _ _ _ ih => simp [plug, fwdBits, TempPhaseProg.evalSign, ih]
theorem plug_evalBits_split {M : ℕ} {mutW : Wire M → Prop} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) {body : TempPhaseProg M}
    (hBodyNonMut : ∀ γ w, ¬ mutW w → body.evalBits γ w = γ w) (q₀ : Wire M)
    (β : BitAssignment M) : (∀ w, mutW w → (K.plug body).evalBits β w = body.evalBits
    (K.fwdBits β) w) ∧ (∀ w, ¬ mutW w → (K.plug body).evalBits β w = (K.plug (.z q₀)).evalBits
    β w) := by
  induction K generalizing β with
  | hole =>
      exact ⟨fun _ _ ↦ rfl, fun w hw ↦ hBodyNonMut β w hw⟩
  | seqPre c K₁ ih =>
      exact ih hDisj.2 (c.eval β)
  | seqPost K₁ c ih =>
      obtain ⟨hM, hN⟩ := ih hDisj.1 β
      refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · dsimp [plug, TempPhaseProg.evalBits, fwdBits]
        rw [hDisj.2.eval_mut _ hw]
        exact hM w hw
      · dsimp [plug, TempPhaseProg.evalBits]
        exact hDisj.2.eval_congr_nonMut hN w hw
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
      obtain ⟨hM, hN⟩ := ih hDisj.2.2.2 β₁
      have hc₁ : (K₁.plug body).evalBits β₁ c₁ = (K₁.plug (.z q₀)).evalBits β₁ c₁ := hN c₁ hDisj.1
      have hc₂ : (K₁.plug body).evalBits β₁ c₂ = (K₁.plug (.z q₀)).evalBits β₁ c₂ := hN c₂ hDisj.2.1
      have ha : (K₁.plug body).evalBits β₁ anc = (K₁.plug (.z q₀)).evalBits β₁ anc :=
        hN anc hDisj.2.2.1
      refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · have hw_ne : w ≠ anc := fun heq ↦ hDisj.2.2.1 (heq ▸ hw)
        dsimp only [plug, TempPhaseProg.evalBits, fwdBits]
        change Function.update ((K₁.plug body).evalBits β₁) anc _ w = _
        rw [Function.update_of_ne hw_ne]
        exact hM w hw
      · dsimp only [plug, TempPhaseProg.evalBits]
        change Function.update ((K₁.plug body).evalBits β₁) anc ((K₁.plug body).evalBits β₁
          anc + (K₁.plug body).evalBits β₁ c₁ * (K₁.plug body).evalBits β₁ c₂) w =
          Function.update ((K₁.plug (.z q₀)).evalBits β₁) anc ((K₁.plug (.z q₀)).evalBits β₁
          anc + (K₁.plug (.z q₀)).evalBits β₁ c₁ * (K₁.plug (.z q₀)).evalBits β₁ c₂) w
        by_cases hwa : w = anc
        · subst hwa
          rw [Function.update_self, Function.update_self, ha, hc₁, hc₂]
        · rw [Function.update_of_ne hwa, Function.update_of_ne hwa]
          exact hN w hw
theorem plug_validCleanRem {M : ℕ} {mutW : Wire M → Prop} {curHole : ℕ} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx curHole)
    {body : TempPhaseProg M} (hBodyValid : ValidCleanRem M (M - curHole) body)
    (hBodyNonMut : ∀ γ w, ¬ mutW w → body.evalBits γ w = γ w) (q₀ : Wire M) : ∀ {rem : ℕ}, M -
    curHole ≤ rem → ValidCleanRem M rem (K.plug (.z q₀)) → ValidCleanRem M rem (K.plug body)
    := by
  induction K with
  | hole =>
      intro rem hle _
      exact validCleanRem_mono hle hBodyValid
  | seqPre c K₁ ih =>
      intro rem hle ⟨remMid, hmid, _, hv₁, hpres₁⟩
      let rem' := max remMid (M - curHole)
      refine ⟨rem', by omega, trivial,
        ih hDisj.2 hSupp.2 (Nat.le_max_right _ _) (validCleanRem_mono (Nat.le_max_left _ _) hv₁),
        fun β hβ w hw ↦ ?_⟩
      by_cases hw1 : M - remMid ≤ w.val
      · exact hpres₁ β hβ w hw1
      · have hw2 : curHole ≤ w.val := by omega
        rw [TempPhaseProg.evalBits, c.eval_outside hSupp.1 β w hw2]
        exact hβ w (by omega)
  | seqPost K₁ c ih =>
      intro rem hle ⟨_, _, hv₁, _, _⟩
      exact ⟨0, Nat.zero_le M, ih hDisj.1 hSupp.1 hle hv₁, trivial,
        fun _ _ _ hw ↦ absurd hw (by omega)⟩
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      intro rem _ ⟨hanc_lo, hv₁, hpres₁⟩
      have hrem' : M - curHole ≤ M - (anc.val + 1) := by have := hSupp.1; omega
      refine ⟨hanc_lo, ih hDisj.2.2.2 hSupp.2 hrem' hv₁, fun β₁ hβ₁ ↦ ?_⟩
      obtain ⟨_, hN⟩ := plug_evalBits_split hDisj.2.2.2 hBodyNonMut q₀ β₁
      rw [hN c₁ hDisj.1, hN c₂ hDisj.2.1, hN anc hDisj.2.2.1]
      exact hpres₁ β₁ hβ₁
end TempCtx
theorem ScopedBlock.graft_mutating_body {M rem curHole : ℕ} [NeZero M] (mutW : Wire M → Prop)
    [DecidablePred mutW] (K : TempCtx M) (hDisj : K.DisjointFrom mutW)
    (hSupp : K.SupportsBelowCtx curHole) (hle : M - curHole ≤ rem)
    (setup : BitAssignment M → BitAssignment M) (hProbe : ∀ q : Wire M, ScopedBlock M rem
    setup (.z q) (K.plug (.z q))) (body : TempPhaseProg M)
    (hBodyValid : ValidCleanRem M (M - curHole) body)
    (hBodyNonMut : ∀ γ w, ¬ mutW w → body.evalBits γ w = γ w) : ValidCleanRem M rem
    (K.plug body) ∧ (K.plug body).countTempAnd = K.countTempAnd + body.countTempAnd ∧ (∀ β :
    BitAssignment M, cleanRem M rem β → (K.plug body).evalSign β = body.evalSign (setup β)) ∧
    (∀ β : BitAssignment M, cleanRem M rem β → ∀ w : Wire M, (K.plug body).evalBits β w = if
    mutW w then body.evalBits (setup β) w else β w) := by
  let q₀ : Wire M := ⟨0, NeZero.pos M⟩
  have hFwd : ∀ β : BitAssignment M, cleanRem M rem β → K.fwdBits β = setup β := by
    intro β hβ
    funext q
    have h₁ := K.plug_evalSign (.z q) β
    have h₂ := (hProbe q).sign β hβ
    dsimp [TempPhaseProg.evalSign] at h₁ h₂
    exact h₁.symm.trans h₂
  refine ⟨K.plug_validCleanRem hDisj hSupp hBodyValid hBodyNonMut q₀ hle (hProbe q₀).valid,
    K.plug_countTempAnd body,
    fun β hβ ↦ by rw [K.plug_evalSign, hFwd β hβ],
    fun β hβ w ↦ ?_⟩
  obtain ⟨hM, hN⟩ := K.plug_evalBits_split hDisj hBodyNonMut q₀ β
  by_cases hw : mutW w
  · simp only [hw, ↓reduceIte, hM w hw, hFwd β hβ]
  · simp only [hw, ↓reduceIte, hN w hw, (hProbe q₀).bits β hβ]
def ctxCliffAlloc {M : ℕ} (c : CliffProg M) : TempCtx M := .seqPre c (.seqPost .hole c.inv)
@[simp] theorem ctxCliffAlloc_plug {M : ℕ} (c : CliffProg M) (body : TempPhaseProg M) :
    (ctxCliffAlloc c).plug body = withCliffAlloc c body := rfl
theorem ctxCliffAlloc_disjoint {M : ℕ} {mutW : Wire M → Prop} {c : CliffProg M}
    (hc : CliffDisjoint mutW c) : (ctxCliffAlloc c).DisjointFrom mutW := ⟨hc, trivial, hc.inv⟩
theorem ctxCliffAlloc_supports {M bound : ℕ} {c : CliffProg M}
    (hc : c.SupportsBelow bound) : (ctxCliffAlloc c).SupportsBelowCtx bound :=
  ⟨hc, trivial, CliffProg.inv_supportsBelow c hc⟩
def ctxTempBit {M : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    : TempCtx M := .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a .hole
@[simp] theorem ctxTempBit_plug {M : ℕ} (c₁ c₂ anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : TempPhaseProg M) :
    (ctxTempBit c₁ c₂ anc h₁₂ h₁a h₂a).plug body = withTempBit c₁ c₂ anc h₁₂ h₁a h₂a body := rfl
def cswapBitProg {M : ℕ} (ctrl a b anc : Wire M) (hab : a ≠ b) (hca : ctrl ≠ a)
    (hc_anc : ctrl ≠ anc) (ha_anc : a ≠ anc) (hb_anc : anc ≠ b) : TempPhaseProg M := .seq
    (.cnot b a hab.symm) (.seq (andXor ctrl a b anc hca hc_anc ha_anc hb_anc) (.cnot b a
    hab.symm))
@[simp] theorem cswapBitProg_countTempAnd {M : ℕ} (ctrl a b anc : Wire M) (hab : a ≠ b)
    (hca : ctrl ≠ a) (hc_anc : ctrl ≠ anc) (ha_anc : a ≠ anc) (hb_anc : anc ≠ b) :
    (cswapBitProg ctrl a b anc hab hca hc_anc ha_anc hb_anc).countTempAnd = 1 := by
  simp [cswapBitProg, TempPhaseProg.cnot, TempPhaseProg.countTempAnd]
@[simp] theorem cswapBitProg_evalSign {M : ℕ} (ctrl a b anc : Wire M) (hab : a ≠ b)
    (hca : ctrl ≠ a) (hc_anc : ctrl ≠ anc) (ha_anc : a ≠ anc) (hb_anc : anc ≠ b)
    (β : BitAssignment M) : (cswapBitProg ctrl a b anc hab hca hc_anc ha_anc hb_anc).evalSign
    β = 0 := by
  simp [cswapBitProg, TempPhaseProg.cnot, TempPhaseProg.evalSign]
def cswapRegProg {M : ℕ} :
    (k : ℕ) → (ctrl : Wire M) → (regA regB : Fin k → Wire M) → (anc : Wire M) →
    (hab : ∀ i, regA i ≠ regB i) →
    (hca : ∀ i, ctrl ≠ regA i) →
    (hc_lt : ctrl.val < anc.val) →
    (ha_lt : ∀ i, (regA i).val < anc.val) →
    (hb_lt : ∀ i, (regB i).val < anc.val) →
    TempPhaseProg M
  | 0, _, _, _, _, _, _, _, _, _ => .nil
  | k + 1, ctrl, regA, regB, anc, hab, hca, hc_lt, ha_lt, hb_lt =>
      .seq
        (cswapBitProg ctrl (regA 0) (regB 0) anc (hab 0) (hca 0)
          (wire_ne_of_lt hc_lt) (wire_ne_of_lt (ha_lt 0)) (wire_ne_of_gt (hb_lt 0)))
        (cswapRegProg k ctrl (fun i ↦ regA i.succ) (fun i ↦ regB i.succ) anc
          (fun i ↦ hab i.succ) (fun i ↦ hca i.succ)
          hc_lt (fun i ↦ ha_lt i.succ) (fun i ↦ hb_lt i.succ))
@[simp] theorem cswapRegProg_countTempAnd {M : ℕ} :
    ∀ (k : ℕ) (ctrl : Wire M) (regA regB : Fin k → Wire M) (anc : Wire M)
      (hab : ∀ i, regA i ≠ regB i) (hca : ∀ i, ctrl ≠ regA i)
      (hc_lt : ctrl.val < anc.val)
      (ha_lt : ∀ i, (regA i).val < anc.val) (hb_lt : ∀ i, (regB i).val < anc.val),
      (cswapRegProg k ctrl regA regB anc hab hca hc_lt ha_lt hb_lt).countTempAnd = k
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | k + 1, ctrl, regA, regB, anc, hab, hca, hc_lt, ha_lt, hb_lt => by
      simp only [cswapRegProg, TempPhaseProg.countTempAnd, cswapBitProg_countTempAnd,
        cswapRegProg_countTempAnd]
      omega
@[simp] theorem cswapRegProg_evalSign {M : ℕ} :
    ∀ (k : ℕ) (ctrl : Wire M) (regA regB : Fin k → Wire M) (anc : Wire M)
      (hab : ∀ i, regA i ≠ regB i) (hca : ∀ i, ctrl ≠ regA i)
      (hc_lt : ctrl.val < anc.val)
      (ha_lt : ∀ i, (regA i).val < anc.val) (hb_lt : ∀ i, (regB i).val < anc.val)
      (β : BitAssignment M),
      (cswapRegProg k ctrl regA regB anc hab hca hc_lt ha_lt hb_lt).evalSign β = 0
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | k + 1, ctrl, regA, regB, anc, hab, hca, hc_lt, ha_lt, hb_lt, β => by
      simp [cswapRegProg, TempPhaseProg.evalSign, cswapRegProg_evalSign]
theorem TempCtx.append_fwdBits {M : ℕ} (K₁ K₂ : TempCtx M) (β : BitAssignment M) :
    (K₁.append K₂).fwdBits β = K₂.fwdBits (K₁.fwdBits β) := by
  induction K₁ generalizing β with
  | hole => rfl
  | seqPre c K ih => exact ih (c.eval β)
  | seqPost K _ ih => exact ih β
  | tempAnd c₁ c₂ anc _ _ _ K ih =>
      exact ih (Function.update β anc (β anc + β c₁ * β c₂))
inductive SymCtx {M : ℕ} : ℕ → ℕ → TempCtx M → Prop
  | hole (rem : ℕ) : SymCtx rem rem .hole
  | cliff {remOut remIn : ℕ} (h : remIn ≤ remOut) (hM : remOut ≤ M)
      (c : CliffProg M) (hSupp : c.SupportsBelow (M - remOut))
      {K : TempCtx M} (hK : SymCtx remOut remIn K) :
      SymCtx remOut remIn (.seqPre c (.seqPost K c.inv))
  | temp {pos remIn : ℕ} (hpos : pos + 1 ≤ M)
      (c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < pos) (hc₂ : c₂.val < pos)
      {K : TempCtx M} (hK : SymCtx (M - (pos + 1)) remIn K) :
      SymCtx (M - pos) remIn
        (.tempAnd c₁ c₂ ⟨pos, hpos⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂) K)
  | append {r₀ r₁ r₂ : ℕ} {K₁ K₂ : TempCtx M}
      (h₁ : SymCtx r₀ r₁ K₁) (h₂ : SymCtx r₁ r₂ K₂) :
      SymCtx r₀ r₂ (K₁.append K₂)
  | castOut {r₀ r₀' r₁ : ℕ} (hle : r₀ ≤ r₀') {K : TempCtx M}
      (hK : SymCtx r₀ r₁ K) :
      SymCtx r₀' r₁ K
theorem SymCtx.scopedBlock {M rOut rIn : ℕ} {K : TempCtx M}
    (hSym : SymCtx (M := M) rOut rIn K) :
    (∀ β : BitAssignment M, cleanRem M rOut β → cleanRem M rIn (K.fwdBits β)) ∧
    ∀ {s : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M},
      ScopedBlock M rIn s leaf body →
      ScopedBlock M rOut (fun β ↦ s (K.fwdBits β)) leaf (K.plug body) := by
  induction hSym with
  | hole rem =>
      exact ⟨fun _ hβ ↦ hβ, fun hb ↦ hb⟩
  | cliff h hM c hSupp _ ih =>
      refine ⟨fun β hβ ↦ ih.1 (c.eval β) (fun w hw ↦ by
          rw [c.eval_outside hSupp β w hw]; exact hβ w hw),
        fun hb ↦ ScopedBlock.withCliffAlloc_block hM le_rfl c hSupp (ih.2 hb)⟩
  | temp hpos c₁ c₂ h₁₂ hc₁ hc₂ _ ih =>
      refine ⟨fun β hβ ↦ ?_, fun hb ↦ ?_⟩
      · have hanc0 : β ⟨_, hpos⟩ = 0 := hβ ⟨_, hpos⟩ (by dsimp; omega)
        dsimp only [TempCtx.fwdBits]
        rw [hanc0, zero_add]
        exact ih.1 _ (fun w hw ↦ by
          rw [Function.update_of_ne (wire_ne_of_gt (by dsimp at hw ⊢; omega))]
          exact hβ w (by omega))
      · have hStep := ScopedBlock.withTempBit_block _ hpos c₁ c₂ h₁₂ hc₁ hc₂ (ih.2 hb)
        refine ⟨hStep.valid, hStep.bits, fun β hβ ↦ ?_⟩
        have hanc0 : β ⟨_, hpos⟩ = 0 := hβ ⟨_, hpos⟩ (by dsimp; omega)
        dsimp only [TempCtx.plug, TempCtx.fwdBits]
        change (withTempBit c₁ c₂ ⟨_, hpos⟩ h₁₂ _ _ _).evalSign β = _
        rw [hStep.sign β hβ, hanc0, zero_add]
  | append _ _ ih₁ ih₂ =>
      refine ⟨fun β hβ ↦ by
          rw [TempCtx.append_fwdBits]
          exact ih₂.1 _ (ih₁.1 β hβ),
        fun hb ↦ ?_⟩
      rw [TempCtx.append_plug]
      have hStep := ih₁.2 (ih₂.2 hb)
      refine ⟨hStep.valid, hStep.bits, fun β hβ ↦ ?_⟩
      rw [hStep.sign β hβ]
      simp [TempCtx.append_fwdBits]
  | castOut hle _ ih =>
      refine ⟨fun β hβ ↦ ih.1 β (cleanRem_anti hle hβ), fun hb ↦ ?_⟩
      have hStep := ih.2 hb
      exact ⟨validCleanRem_mono hle hStep.valid, fun β hβ ↦ hStep.bits β (cleanRem_anti hle
        hβ), fun β hβ ↦ hStep.sign β (cleanRem_anti hle hβ)⟩
structure CtxSpec {M : ℕ} (mutW : Wire M → Prop) (curOuter curHole : ℕ)
    (K : TempCtx M) : Prop where
  disj : K.DisjointFrom mutW
  supp : K.SupportsBelowCtx curHole
  sym : SymCtx (M - curOuter) (M - curHole) K
theorem CtxSpec.fwd_clean {M : ℕ} {mutW : Wire M → Prop} {curOuter curHole : ℕ}
    {K : TempCtx M} (h : CtxSpec mutW curOuter curHole K) {β : BitAssignment M}
    (hβ : cleanRem M (M - curOuter) β) : cleanRem M (M - curHole) (K.fwdBits β) :=
    h.sym.scopedBlock.1 β hβ
theorem CtxSpec.probe {M : ℕ} {mutW : Wire M → Prop} {curOuter curHole : ℕ}
    (hHole : curHole ≤ M) {K : TempCtx M} (h : CtxSpec mutW curOuter curHole K) (q : Wire M) :
    ScopedBlock M (M - curOuter) K.fwdBits (.z q) (K.plug (.z q)) := h.sym.scopedBlock.2
    (ScopedBlock.leaf_z (M - curHole) (by omega) q)
theorem CtxSpec.comp {M : ℕ} {mutW : Wire M → Prop} {c₀ c₁ c₂ : ℕ} {K₁ K₂ : TempCtx M}
    (h12 : c₁ ≤ c₂) (h₁ : CtxSpec mutW c₀ c₁ K₁) (h₂ : CtxSpec mutW c₁ c₂ K₂) : CtxSpec mutW
    c₀ c₂ (K₁.append K₂) :=
  { disj := TempCtx.disjointFrom_append h₁.disj h₂.disj
    supp := TempCtx.supportsBelowCtx_append h12 h₁.supp h₂.supp
    sym := .append h₁.sym h₂.sym }
theorem CtxSpec.cliff {M : ℕ} {mutW : Wire M → Prop} (cur : ℕ) (hcur : cur ≤ M)
    (c : CliffProg M) (hDisj : CliffDisjoint mutW c) (hSupp : c.SupportsBelow cur) :
    CtxSpec mutW cur cur (ctxCliffAlloc c) ∧
    ∀ β : BitAssignment M, (ctxCliffAlloc c).fwdBits β = c.eval β :=
  ⟨{ disj := ctxCliffAlloc_disjoint hDisj
     supp := ctxCliffAlloc_supports hSupp
     sym := .cliff le_rfl (by omega) c (by simpa [Nat.sub_sub_self hcur] using hSupp) (.hole _) },
   fun _ ↦ rfl⟩
theorem CtxSpec.tempBit {M : ℕ} {mutW : Wire M → Prop} (pos : ℕ) (hpos : pos + 1 ≤ M)
    (c₁ c₂ : Wire M) (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < pos) (hc₂ : c₂.val < pos)
    (hm₁ : ¬ mutW c₁) (hm₂ : ¬ mutW c₂) (hma : ¬ mutW ⟨pos, hpos⟩) :
    let K := ctxTempBit c₁ c₂ ⟨pos, hpos⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂)
    CtxSpec mutW pos (pos + 1) K ∧
    ∀ β : BitAssignment M, cleanRem M (M - pos) β →
      K.fwdBits β = Function.update β ⟨pos, hpos⟩ (β c₁ * β c₂) := by
  intro K
  refine ⟨{ disj := ⟨hm₁, hm₂, hma, trivial⟩
            supp := ⟨by dsimp; omega, trivial⟩
            sym := .temp hpos c₁ c₂ h₁₂ hc₁ hc₂ (.hole _) },
    fun β hβ ↦ ?_⟩
  have h0 : β ⟨pos, hpos⟩ = 0 := hβ ⟨pos, hpos⟩ (by dsimp; omega)
  dsimp [K, ctxTempBit, TempCtx.fwdBits]
  rw [h0, zero_add]
end Internal
open Real Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open FullSysCatSegmentBridge hiding IntertwinesLocalCat
open HoistedSwapSelectBridge
open MeasureBranchHadamardSem (ket)
open MomSlot0CircuitHalf hiding ket
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open scoped Matrix ComplexOrder MatrixOrder BigOperators
instance (priority := 1000000) instNeZeroTwoPowCoinBarrel (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
instance (priority := 1000000) instNeZeroCorePlusBarrel (mPayload mExtra : ℕ) :
    NeZero (fullSysCoreWires mPayload + mExtra) :=
  ⟨by
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]; omega⟩
def swapElec0Bits {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    (β : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) :=
  if e.val = 0 then β
  else fun w ↦
    if hw : w.val < 18 then
      β ⟨18 * e.val + w.val, by
        have he := e.isLt
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits] at he ⊢
        omega⟩
    else if hew : 18 * e.val ≤ w.val ∧ w.val < 18 * e.val + 18 then
      β ⟨w.val - 18 * e.val, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩
    else β w
@[simp] theorem swapElec0Bits_zero {mPayload : ℕ}
    (β : BitAssignment (fullSysCoreWires mPayload)) :
    swapElec0Bits ⟨0, by decide⟩ β = β := rfl
@[simp] theorem swapElec0Bits_self {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    (β : BitAssignment (fullSysCoreWires mPayload)) :
    swapElec0Bits e (swapElec0Bits e β) = β := by
  by_cases he : e.val = 0
  · simp [swapElec0Bits, he]
  · funext w
    simp only [swapElec0Bits, he, ↓reduceIte]
    by_cases hw0 : w.val < 18
    · have hnot0 : ¬ (18 * e.val + w.val < 18) := by omega
      have hmid : 18 * e.val ≤ 18 * e.val + w.val ∧ 18 * e.val + w.val < 18 * e.val + 18 :=
        ⟨by omega, by omega⟩
      simp only [hw0, ↓reduceDIte, hnot0, hmid, and_self]
      congr 1; apply Fin.ext; dsimp; omega
    · simp only [hw0, ↓reduceDIte]
      by_cases hwe : 18 * e.val ≤ w.val ∧ w.val < 18 * e.val + 18
      · have hlt : w.val - 18 * e.val < 18 := by omega
        simp only [hwe, and_self, ↓reduceDIte, hlt]
        congr 1; apply Fin.ext; dsimp; omega
      · simp [hwe]
theorem swapElec0Bits_high {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    (β : BitAssignment (fullSysCoreWires mPayload)) (w : Wire (fullSysCoreWires mPayload))
    (hw : 3924 ≤ w.val) : swapElec0Bits e β w = β w := by
  have he : e.val < 218 := e.isLt
  by_cases he0 : e.val = 0
  · simp [swapElec0Bits, he0]
  · simp only [swapElec0Bits, he0, ↓reduceIte]
    have h1 : ¬ w.val < 18 := by omega
    have h2 : ¬ (18 * e.val ≤ w.val ∧ w.val < 18 * e.val + 18) := by omega
    simp [h1, h2]
def coinBarrelIdx {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Fin SpecsAux.SpecMirror.numElectrons :=
  let c0 := γ (iSlot0 mPayload)
  let c1 := γ (iSlot1 mPayload)
  let c2 := γ (iSlot2 mPayload)
  if c2 = 0 ∧ c1 = 0 then
    let u8 := Internal.bitsVal (fun j : Fin 8 ↦
      γ ⟨3968 + j.val, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩)
    if h : u8 < 218 then ⟨u8, h⟩ else ⟨0, by decide⟩
  else if c2 = 1 ∧ c1 = 1 ∧ c0 = 1 then
    let u21 := Internal.bitsVal (fun j : Fin 21 ↦
      γ ⟨4011 + j.val, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩)
    ⟨u21 % 218, Nat.mod_lt _ (by decide)⟩
  else if c2 = 1 ∧ c1 = 0 ∧ c0 = 0 then
    let u36 := Internal.bitsVal (fun j : Fin 36 ↦
      γ ⟨3954 + j.val, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩)
    let wBPar : Wire (fullSysCoreWires mPayload) :=
      ⟨3990, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩
    ⟨(2 * (u36 % 327) + (γ wBPar).val) / 3, by
      have := Nat.mod_lt u36 (by omega : 0 < 327)
      have := ZMod.val_lt (γ wBPar)
      change _ < 218
      omega⟩
  else
    ⟨0, by decide⟩
theorem coinBarrelIdx_congr_high {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hHigh : ∀ w : Wire (fullSysCoreWires mPayload), 3924 ≤ w.val → γ₁ w = γ₂ w) :
    coinBarrelIdx hmPay γ₁ = coinBarrelIdx hmPay γ₂ := by
  have hCore : 4034 ≤ fullSysCoreWires mPayload := by
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega
  have hReg (k base : ℕ) (hbase : 3924 ≤ base) (hhi : base + k ≤ 4034) :
      (fun j : Fin k ↦ γ₁ ⟨base + j.val, by omega⟩) =
        (fun j : Fin k ↦ γ₂ ⟨base + j.val, by omega⟩) :=
    funext fun j ↦ hHigh _ (show 3924 ≤ base + j.val by omega)
  dsimp only [coinBarrelIdx]
  simp only [hHigh (iSlot0 mPayload) (by
      dsimp [iSlot0, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
      omega),
    hHigh (iSlot1 mPayload) (by
      dsimp [iSlot1, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
      omega),
    hHigh (iSlot2 mPayload) (by
      dsimp [iSlot2, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
      omega),
    hReg 8 3968 (by omega) (by omega), hReg 21 4011 (by omega) (by omega),
    hReg 36 3954 (by omega) (by omega),
    hHigh ⟨3990, by omega⟩ (show 3924 ≤ 3990 by omega)]
@[simp] theorem coinBarrelIdx_swap_inv {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (e : Fin SpecsAux.SpecMirror.numElectrons) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    coinBarrelIdx hmPay (swapElec0Bits e γ) = coinBarrelIdx hmPay γ :=
    coinBarrelIdx_congr_high hmPay (fun w hw ↦ swapElec0Bits_high e γ w hw)
def coinBarrelBitFn {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : BitAssignment
    (fullSysCoreWires mPayload) := swapElec0Bits (coinBarrelIdx hmPay γ) γ
theorem coinBarrelBitFn_involutive {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Involutive (coinBarrelBitFn hmPay) := fun γ ↦ by
  dsimp only [coinBarrelBitFn]
  rw [coinBarrelIdx_swap_inv, swapElec0Bits_self]
noncomputable def coinBarrelPerm {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Equiv.Perm
    (Fin (2 ^ (fullSysCoreWires mPayload))) :=
    (basisBitsEquiv (fullSysCoreWires mPayload)).trans ((Equiv.ofBijective (coinBarrelBitFn
    hmPay) (coinBarrelBitFn_involutive hmPay).bijective).trans (basisBitsEquiv
    (fullSysCoreWires mPayload)).symm)
@[simp] theorem coinBarrelPerm_apply_self {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (x : Fin (2 ^ (fullSysCoreWires mPayload))) :
    coinBarrelPerm hmPay (coinBarrelPerm hmPay x) = x := by
  unfold coinBarrelPerm
  change (basisBitsEquiv _).symm (coinBarrelBitFn hmPay
    ((basisBitsEquiv _) ((basisBitsEquiv _).symm (coinBarrelBitFn hmPay ((basisBitsEquiv _) x))))) =
      x
  rw [(basisBitsEquiv _).apply_symm_apply, coinBarrelBitFn_involutive hmPay _,
    (basisBitsEquiv _).symm_apply_apply]
noncomputable def uBarrel {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := Operator.permutationUnitary (coinBarrelPerm hmPay)
theorem uBarrel_mul_self {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    uBarrel hmPay * uBarrel hmPay = 1 := by
  have hsq : coinBarrelPerm hmPay * coinBarrelPerm hmPay = 1 := by
    apply Equiv.ext; intro x; exact coinBarrelPerm_apply_self hmPay x
  unfold uBarrel
  rw [← OperatorExt.permutationUnitary_mul, hsq, OperatorExt.permutationUnitary_one]
@[simp] theorem uBarrel_inv {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : (uBarrel hmPay)⁻¹ =
    uBarrel hmPay := (mul_eq_one_iff_inv_eq.mp (uBarrel_mul_self hmPay))
@[simp] theorem uBarrel_conjTranspose {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (uBarrel hmPay).1ᴴ = (uBarrel hmPay).1 := by
  have hinv : (uBarrel hmPay)⁻¹ = star (uBarrel hmPay) := rfl
  have h := congrArg Subtype.val (uBarrel_inv hmPay)
  simpa only [hinv, Unitary.coe_star, Matrix.star_eq_conjTranspose] using h
theorem uBarrel_mulVec_ket {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uBarrel hmPay).1.mulVec (ket γ) = ket (coinBarrelBitFn hmPay γ) := by
  have hid := NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet
      (QRegExt.idReg (fullSysCoreWires mPayload)) (coinBarrelPerm hmPay) γ
      (coinBarrelBitFn hmPay γ) (fun q ↦ (NuclearTwistRealizes.basisBits_perm_ofBijective
      (coinBarrelBitFn hmPay) (coinBarrelBitFn_involutive hmPay).bijective γ q).symm) (fun z
      hz ↦ False.elim (hz ((QRegister.mem_image _ z).mpr ⟨z, rfl⟩)))
  rwa [NuclearTwistRealizes.embedUnitary_idReg_eq] at hid
@[simp] theorem tempCtx_append_countTempAnd {M : ℕ} (F G : Internal.TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd := by
  have h := F.plug_countTempAnd (G.plug .nil)
  rw [← F.append_plug G .nil, Internal.TempCtx.plug_countTempAnd, G.plug_countTempAnd] at h
  omega
@[simp] theorem ctxCliffAlloc_countTempAnd {M : ℕ} (c : Internal.CliffProg M) :
    (Internal.ctxCliffAlloc c).countTempAnd = 0 := by
  have h := (Internal.ctxCliffAlloc c).plug_countTempAnd .nil
  simpa [Internal.ctxCliffAlloc_plug, Internal.withCliffAlloc, Internal.TempPhaseProg.countTempAnd]
    using h.symm
@[simp] theorem ctxTempBit_countTempAnd {M : ℕ} (c₁ c₂ anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) :
    (Internal.ctxTempBit c₁ c₂ anc h₁₂ h₁a h₂a).countTempAnd = 1 := by
  have h := (Internal.ctxTempBit c₁ c₂ anc h₁₂ h₁a h₂a).plug_countTempAnd .nil
  simpa [Internal.ctxTempBit_plug, Internal.TempPhaseProg.countTempAnd] using h.symm
set_option backward.isDefEq.respectTransparency true
end ConfigCoinDispatchedBarrel288
end CoinDispatchedBarrel288
end
end ModCoinDispatchedBarrel288

section ModFullSysHoistedSelectStitch
@[expose] public section
section ConfigFullSysHoistedSelectStitch
set_option exponentiation.threshold 8192
namespace FullSysHoistedSelectStitch
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror SpecsAux.FullScaleBESector
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.GhostGuardCircuitBridge
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open PosMomSelectSandwich
open FullSysCatSegmentBridge
open HoistedSwapSelectBridge
open FullSysMomSlots0135Concrete
open scoped Matrix Matrix.Norms.L2Operator BigOperators
instance (priority := 100000) instNeZeroTwoPowHoistedStitch (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
instance (priority := 100000) instNeZeroTwoPow48HoistedStitch : NeZero (2 ^ 48) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 48)⟩
instance (priority := 100000) instNeZeroTwoPow3948HoistedStitch : NeZero (2 ^ 3948) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 3948)⟩
instance (priority := 100000) instNeZeroTwoPow3951HoistedStitch : NeZero (2 ^ (3948 + 3)) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos (3948 + 3))⟩
instance (priority := 100000) instNeZeroTwoPow4031HoistedStitch : NeZero (2 ^ 4031) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4031)⟩
instance (priority := 100000) instNeZeroTwoPow4034HoistedStitch : NeZero (2 ^ 4034) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4034)⟩
instance (priority := 100000) instNeZeroTwoPow4066HoistedStitch : NeZero (2 ^ 4066) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4066)⟩
instance (priority := 100000) instNeZeroTwoPow4067HoistedStitch : NeZero (2 ^ 4067) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4067)⟩
instance (priority := 100000) instNeZeroTwoPow4109HoistedStitch : NeZero (2 ^ 4109) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4109)⟩
instance (priority := 100000) instNeZeroTwoPow4112HoistedStitch : NeZero (2 ^ 4112) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4112)⟩
instance (priority := 100000) instNeZeroTwoPow4121HoistedStitch : NeZero (2 ^ 4121) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4121)⟩
instance (priority := 100000) instNeZeroTwoPow4144HoistedStitch : NeZero (2 ^ 4144) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4144)⟩
instance (priority := 100000) instNeZeroTwoPow4145HoistedStitch : NeZero (2 ^ 4145) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4145)⟩
instance (priority := 100000) instNeZeroTwoPow4199HoistedStitch : NeZero (2 ^ 4199) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 4199)⟩
set_option exponentiation.threshold 256
theorem mul_comm_of_comm {D : ℕ} {A B P : Operator D} (hA : A * P = P * A)
    (hB : B * P = P * B) : (A * B) * P = P * (A * B) := by
  calc (A * B) * P
      = A * (B * P) := Matrix.mul_assoc A B P
    _ = (A * P) * B := by rw [hB, ← Matrix.mul_assoc]
    _ = P * (A * B) := by rw [hA, Matrix.mul_assoc]
structure HoistedBarrelBundle (mPayload mWork : ℕ) where
  uBarrel : SpecsAux.SpecMirror.Configuration →
    Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires mPayload))
  hHighWireComm : ∀ cfg (q : Wire (FullSysCatSegmentBridge.fullSysCoreWires mPayload)),
    3924 ≤ q.val → ∀ b : Fin 2,
      (uBarrel cfg).1 * slotBitProj q b = slotBitProj q b * (uBarrel cfg).1
abbrev HoistedBarrelSpec := HoistedBarrelBundle
end FullSysHoistedSelectStitch
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
end ConfigFullSysHoistedSelectStitch
end
end ModFullSysHoistedSelectStitch

section ModFastCoinBarrelDecoder279
@[expose] public section
section ConfigFastCoinBarrelDecoder279
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
namespace CoinDispatchedBarrel288
section FastBarrelSpec145
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 256
open Real Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open PosMomSelectSandwich
open FullSysCatSegmentBridge hiding IntertwinesLocalCat
open HoistedSwapSelectBridge
open MeasureBranchHadamardSem (ket)
open MomSlot0CircuitHalf hiding ket
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open scoped Matrix ComplexOrder MatrixOrder BigOperators
def coinBarrelIdxFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Fin SpecsAux.SpecMirror.numElectrons :=
  let c1 := γ (iSlot1 mPayload)
  let c2 := γ (iSlot2 mPayload)
  if c1 = 1 then
    ⟨0, by decide⟩
  else if c2 = 0 then
    let u8 := Internal.bitsVal (fun j : Fin 8 ↦
      γ ⟨3968 + j.val, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩)
    if h : u8 < 218 then ⟨u8, h⟩ else ⟨0, by decide⟩
  else
    let u36 := Internal.bitsVal (fun j : Fin 36 ↦
      γ ⟨3954 + j.val, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩)
    let wBPar : Wire (fullSysCoreWires mPayload) :=
      ⟨3990, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
          SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
            SpecsAux.SpecMirror.projectileBits]
        omega⟩
    ⟨2 * (u36 % 109) + (γ wBPar).val, by
      have := Nat.mod_lt u36 (by omega : 0 < 109)
      have := ZMod.val_lt (γ wBPar)
      change _ < 218
      omega⟩
theorem coinBarrelIdxFast_congr_high {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hHigh : ∀ w : Wire (fullSysCoreWires mPayload), 3924 ≤ w.val → γ₁ w = γ₂ w) :
    coinBarrelIdxFast hmPay γ₁ = coinBarrelIdxFast hmPay γ₂ := by
  have hCore : 4034 ≤ fullSysCoreWires mPayload := by
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega
  have hReg (k base : ℕ) (hbase : 3924 ≤ base) (hhi : base + k ≤ 4034) :
      (fun j : Fin k ↦ γ₁ ⟨base + j.val, by omega⟩) =
        (fun j : Fin k ↦ γ₂ ⟨base + j.val, by omega⟩) :=
    funext fun j ↦ hHigh _ (show 3924 ≤ base + j.val by omega)
  dsimp only [coinBarrelIdxFast]
  simp only [hHigh (iSlot1 mPayload) (by
      dsimp [iSlot1, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
      omega),
    hHigh (iSlot2 mPayload) (by
      dsimp [iSlot2, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
      omega),
    hReg 8 3968 (by omega) (by omega), hReg 36 3954 (by omega) (by omega),
    hHigh ⟨3990, by omega⟩ (show 3924 ≤ 3990 by omega)]
@[simp] theorem coinBarrelIdxFast_swap_inv {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (e : Fin SpecsAux.SpecMirror.numElectrons) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    coinBarrelIdxFast hmPay (swapElec0Bits e γ) = coinBarrelIdxFast hmPay γ :=
    coinBarrelIdxFast_congr_high hmPay (fun w hw ↦ swapElec0Bits_high e γ w hw)
def coinBarrelBitFnFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : BitAssignment
    (fullSysCoreWires mPayload) := swapElec0Bits (coinBarrelIdxFast hmPay γ) γ
theorem coinBarrelBitFnFast_involutive {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Involutive (coinBarrelBitFnFast hmPay) := fun γ ↦ by
  dsimp only [coinBarrelBitFnFast]
  rw [coinBarrelIdxFast_swap_inv, swapElec0Bits_self]
theorem coinBarrelBitFnFast_high {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (w : Wire (fullSysCoreWires mPayload))
    (hw : 3924 ≤ w.val) : coinBarrelBitFnFast hmPay γ w = γ w := swapElec0Bits_high
    (coinBarrelIdxFast hmPay γ) γ w hw
theorem coinBarrelBitFnFast_c2_zero {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (hc2 : γ (iSlot2 mPayload) = 0) :
    coinBarrelBitFnFast hmPay γ = coinBarrelBitFn hmPay γ := by
  dsimp only [coinBarrelBitFnFast, coinBarrelBitFn]
  congr 1
  dsimp only [coinBarrelIdxFast, coinBarrelIdx]
  generalize γ (iSlot1 mPayload) = c1
  fin_cases c1 <;> simp [hc2, (by decide : ¬ ((0 : ZMod 2) = 1)),
    (by decide : ¬ ((1 : ZMod 2) = 0))]
noncomputable def coinBarrelPermFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Equiv.Perm
    (Fin (2 ^ (fullSysCoreWires mPayload))) :=
    (basisBitsEquiv (fullSysCoreWires mPayload)).trans ((Equiv.ofBijective
    (coinBarrelBitFnFast hmPay) (coinBarrelBitFnFast_involutive hmPay).bijective).trans
    (basisBitsEquiv (fullSysCoreWires mPayload)).symm)
@[simp] theorem coinBarrelPermFast_apply_self {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (x : Fin (2 ^ (fullSysCoreWires mPayload))) :
    coinBarrelPermFast hmPay (coinBarrelPermFast hmPay x) = x := by
  unfold coinBarrelPermFast
  change (basisBitsEquiv _).symm (coinBarrelBitFnFast hmPay
    ((basisBitsEquiv _) ((basisBitsEquiv _).symm (coinBarrelBitFnFast hmPay ((basisBitsEquiv _)
      x))))) = x
  rw [(basisBitsEquiv _).apply_symm_apply, coinBarrelBitFnFast_involutive hmPay _,
    (basisBitsEquiv _).symm_apply_apply]
noncomputable def uBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  Operator.permutationUnitary (coinBarrelPermFast hmPay)
theorem uBarrelFast_mul_self {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    uBarrelFast hmPay * uBarrelFast hmPay = 1 := by
  have hsq : coinBarrelPermFast hmPay * coinBarrelPermFast hmPay = 1 := by
    apply Equiv.ext; intro x; exact coinBarrelPermFast_apply_self hmPay x
  unfold uBarrelFast
  rw [← OperatorExt.permutationUnitary_mul, hsq, OperatorExt.permutationUnitary_one]
@[simp] theorem uBarrelFast_inv {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : (uBarrelFast hmPay)⁻¹
    = uBarrelFast hmPay := (mul_eq_one_iff_inv_eq.mp (uBarrelFast_mul_self hmPay))
@[simp] theorem uBarrelFast_conjTranspose {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (uBarrelFast hmPay).1ᴴ = (uBarrelFast hmPay).1 := by
  have hinv : (uBarrelFast hmPay)⁻¹ = star (uBarrelFast hmPay) := rfl
  have h := congrArg Subtype.val (uBarrelFast_inv hmPay)
  simpa only [hinv, Unitary.coe_star, Matrix.star_eq_conjTranspose] using h
theorem uBarrelFast_mulVec_ket {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uBarrelFast hmPay).1.mulVec (ket γ) = ket (coinBarrelBitFnFast hmPay γ) := by
  have hid := NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet
      (QRegExt.idReg (fullSysCoreWires mPayload)) (coinBarrelPermFast hmPay) γ
      (coinBarrelBitFnFast hmPay γ) (fun q ↦ (NuclearTwistRealizes.basisBits_perm_ofBijective
      (coinBarrelBitFnFast hmPay) (coinBarrelBitFnFast_involutive hmPay).bijective γ q).symm)
      (fun z hz ↦ False.elim (hz ((QRegister.mem_image _ z).mpr ⟨z, rfl⟩)))
  rwa [NuclearTwistRealizes.embedUnitary_idReg_eq] at hid
theorem uBarrelFast_comm_high_wire {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3924 ≤ q.val) (b : Fin 2) :
    (uBarrelFast hmPay).1 * slotBitProj q b = slotBitProj q b * (uBarrelFast hmPay).1 := by
  have hComm := NuclearTwistRealizes.comm_singleton_basisOutcomeProjector_of_preserves
    (uBarrelFast hmPay).1 q b (fun _ ↦ (1 : ℂ)) (coinBarrelBitFnFast hmPay)
    (fun γ ↦ by rw [one_smul]; exact uBarrelFast_mulVec_ket hmPay γ)
    (fun γ ↦ coinBarrelBitFnFast_high hmPay γ q hq)
  have hSlotEq : slotBitProj q b = (QRegister.singleton q).basisOutcomeProjector b :=
    (OraAndPrepBundle.singleton_basisOutcomeProjector_eq_slotBitProj q b).symm
  simpa only [hSlotEq] using hComm
end FastBarrelSpec145
end CoinDispatchedBarrel288
namespace FastCoinBarrelDecoder279
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg
open CoinDispatchedBarrel288
open FullSysHoistedSelectStitch
open FullSysCatSegmentBridge
open MomSlot0CircuitHalf (padZeroBits)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
inductive DecStep where
  | allocZero : DecStep
  | x (w : ℕ) : DecStep
  | cnot (src dst : ℕ) : DecStep
  | andAlloc (a b : ℕ) : DecStep
  deriving Repr, DecidableEq
namespace DecStep
def wellFormed (cur : ℕ) : DecStep → Bool
  | .allocZero => decide (cur + 1 ≤ 337)
  | .x w => decide (w < cur)
  | .cnot src dst => decide (src ≠ dst ∧ src < cur ∧ dst < cur)
  | .andAlloc a b => decide (a ≠ b ∧ a < cur ∧ b < cur ∧ cur + 1 ≤ 337)
def nextCur (cur : ℕ) : DecStep → ℕ
  | .allocZero => cur + 1
  | .x _ => cur
  | .cnot _ _ => cur
  | .andAlloc _ _ => cur + 1
def numAnd : DecStep → ℕ
  | .andAlloc _ _ => 1
  | _ => 0
def stepBool (cur : ℕ) (st : ℕ → Bool) : DecStep → (ℕ → Bool)
  | .allocZero => st
  | .x w => fun q ↦ if q == w then !st q else st q
  | .cnot src dst => fun q ↦ if q == dst then xor (st dst) (st src) else st q
  | .andAlloc a b => fun q ↦ if q == cur then (st a && st b) else st q
def touches (cur : ℕ) : DecStep → ℕ → Bool
  | .allocZero, _ => false
  | .x q, w => q == w
  | .cnot _ dst, w => dst == w
  | .andAlloc _ _, w => cur == w
end DecStep
def progWellFormed : ℕ → List DecStep → Bool
  | _, [] => true
  | cur, s :: rest => s.wellFormed cur && progWellFormed (s.nextCur cur) rest
def progEndCur : ℕ → List DecStep → ℕ
  | cur, [] => cur
  | cur, s :: rest => progEndCur (s.nextCur cur) rest
def progNumAnd : List DecStep → ℕ
  | [] => 0
  | s :: rest => s.numAnd + progNumAnd rest
def evalBool : List DecStep → ℕ → (ℕ → Bool) → (ℕ → Bool)
  | [], _, st => st
  | s :: rest, cur, st => evalBool rest (s.nextCur cur) (s.stepBool cur st)
def progUntouched (w : ℕ) : ℕ → List DecStep → Bool
  | _, [] => true
  | cur, s :: rest => (s.touches cur w == false) && progUntouched w (s.nextCur cur) rest
theorem progEndCur_append (p₁ p₂ : List DecStep) :
    ∀ cur, progEndCur cur (p₁ ++ p₂) = progEndCur (progEndCur cur p₁) p₂ := by
  induction p₁ with
  | nil => intro cur; rfl
  | cons s rest ih => intro cur; exact ih (s.nextCur cur)
theorem evalBool_append (p₁ p₂ : List DecStep) :
    ∀ cur st, evalBool (p₁ ++ p₂) cur st = evalBool p₂ (progEndCur cur p₁) (evalBool p₁ cur st) :=
      by
  induction p₁ with
  | nil => intro cur st; rfl
  | cons s rest ih => intro cur st; exact ih (s.nextCur cur) (s.stepBool cur st)
theorem progWellFormed_append (p₁ p₂ : List DecStep) : ∀ cur, progWellFormed cur (p₁ ++ p₂) =
    (progWellFormed cur p₁ && progWellFormed (progEndCur cur p₁) p₂) := by
  induction p₁ with
  | nil => intro cur; simp [progWellFormed, progEndCur]
  | cons s rest ih =>
      intro cur
      simp only [List.cons_append, progWellFormed, progEndCur, ih, Bool.and_assoc]
theorem stepBool_untouched (s : DecStep) (cur : ℕ) (st : ℕ → Bool) (w : ℕ)
    (hu : (s.touches cur w == false) = true) : s.stepBool cur st w = st w := by
  simp only [beq_iff_eq] at hu
  cases s with
  | allocZero => rfl
  | x q =>
      simp only [DecStep.touches, beq_eq_false_iff_ne] at hu
      simp [DecStep.stepBool, Ne.symm hu]
  | cnot src dst =>
      simp only [DecStep.touches, beq_eq_false_iff_ne] at hu
      simp [DecStep.stepBool, Ne.symm hu]
  | andAlloc a b =>
      simp only [DecStep.touches, beq_eq_false_iff_ne] at hu
      simp [DecStep.stepBool, Ne.symm hu]
theorem evalBool_untouched : ∀ (p : List DecStep) (cur : ℕ) (st : ℕ → Bool) (w : ℕ),
    progUntouched w cur p = true → evalBool p cur st w = st w := by
  intro p
  induction p with
  | nil => intro _ _ _ _; rfl
  | cons s rest ih =>
      intro cur st w h
      simp only [progUntouched, Bool.and_eq_true] at h
      rw [evalBool, ih _ _ _ h.2, stepBool_untouched s cur st w h.1]
def progUntouchedAll (ws : List ℕ) (cur : ℕ) : List DecStep → Bool
  | [] => true
  | s :: rest => ws.all (fun w ↦
    s.touches cur w == false) && progUntouchedAll ws (s.nextCur cur) rest
theorem evalBool_untouched_all : ∀ (p : List DecStep) (ws : List ℕ) (cur : ℕ) (st : ℕ → Bool),
    progUntouchedAll ws cur p = true → ∀ w ∈ ws, evalBool p cur st w = st w := by
  intro p
  induction p with
  | nil => intro _ _ _ _ _ _; rfl
  | cons s rest ih =>
      intro ws cur st h w hw
      simp only [progUntouchedAll, Bool.and_eq_true] at h
      rw [evalBool, ih ws _ _ h.2 w hw,
        stepBool_untouched s cur st w (List.all_eq_true.mp h.1 w hw)]
theorem evalBool_clean : ∀ (p : List DecStep) (cur : ℕ) (st : ℕ → Bool), progWellFormed cur p
    = true → (∀ q, cur ≤ q → st q = false) → ∀ q, progEndCur cur p ≤ q → evalBool p cur st q =
    false := by
  intro p
  induction p with
  | nil => intro cur st _ hcl q hq; exact hcl q hq
  | cons s rest ih =>
      intro cur st hwf hcl q hq
      simp only [progWellFormed, Bool.and_eq_true] at hwf
      apply ih (s.nextCur cur) (s.stepBool cur st) hwf.2 _ q hq
      intro r hr
      cases s with
      | allocZero => exact hcl r (by simp [DecStep.nextCur] at hr; omega)
      | x w =>
          simp only [DecStep.wellFormed, decide_eq_true_eq] at hwf
          simp only [DecStep.nextCur] at hr
          have hne : (r == w) = false := beq_false_of_ne (by omega)
          simp [DecStep.stepBool, hne, hcl r hr]
      | cnot src dst =>
          simp only [DecStep.wellFormed, decide_eq_true_eq] at hwf
          simp only [DecStep.nextCur] at hr
          have hne : (r == dst) = false := beq_false_of_ne (by omega)
          simp [DecStep.stepBool, hne, hcl r hr]
      | andAlloc a b =>
          simp only [DecStep.nextCur] at hr
          have hne : (r == cur) = false := beq_false_of_ne (by omega)
          simp [DecStep.stepBool, hne, hcl r (by omega)]
def evalMod (M x : ℕ) : ℕ := if M == 0 then x else x % M
theorem evalMod_congr_right (M c a b : ℕ) (h : evalMod M a = evalMod M b) :
    evalMod M (c + a) = evalMod M (c + b) := by
  by_cases hM : M = 0
  · simp [evalMod, hM] at h ⊢; omega
  · simp only [evalMod, beq_false_of_ne hM, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [Nat.add_mod, h, ← Nat.add_mod]
theorem evalMod_mul_bit (M Wc W : ℕ) (b : Bool) (hW : evalMod M Wc = evalMod M (2 * W)) :
    evalMod M (if b then Wc else 0) = evalMod M (if b then 2 * W else 0) := by
  cases b
  · simp
  · simpa using hW
inductive WtTrie where
  | zero : WtTrie
  | leaf (v : ℕ) : WtTrie
  | branch (l r : WtTrie) : WtTrie
  deriving Repr, DecidableEq
namespace WtTrie
def leftChild : WtTrie → WtTrie
  | .branch l _ => l
  | _ => .zero
def rightChild : WtTrie → WtTrie
  | .branch _ r => r
  | _ => .zero
def mkBranch (l r : WtTrie) : WtTrie :=
  match l, r with
  | .zero, .zero => .zero
  | _, _ => .branch l r
@[simp] theorem leftChild_mkBranch (l r : WtTrie) : (mkBranch l r).leftChild = l := by
  cases l <;> cases r <;> rfl
@[simp] theorem rightChild_mkBranch (l r : WtTrie) : (mkBranch l r).rightChild = r := by
  cases l <;> cases r <;> rfl
def get : ℕ → WtTrie → ℕ → ℕ
  | 0, .leaf v, _ => v
  | 0, _, _ => 0
  | k + 1, t, i =>
      if i % 2 == 0 then get k t.leftChild (i / 2)
      else get k t.rightChild (i / 2)
@[simp] theorem get_zero : ∀ (k i : ℕ), get k .zero i = 0
  | 0, _ => rfl
  | k + 1, i => by simp [get, leftChild, rightChild, get_zero k]
def set : ℕ → WtTrie → ℕ → ℕ → WtTrie
  | 0, _, _, v => if v == 0 then .zero else .leaf v
  | k + 1, t, i, v =>
      if i % 2 == 0 then mkBranch (set k t.leftChild (i / 2) v) t.rightChild
      else mkBranch t.leftChild (set k t.rightChild (i / 2) v)
theorem get_set_same : ∀ (k : ℕ) (t : WtTrie) (i v : ℕ), get k (set k t i v) i = v
  | 0, _, _, v => by by_cases hv : v = 0 <;> simp [set, get, hv]
  | k + 1, t, i, v => by
      by_cases hpar : i % 2 = 0 <;> simp [set, get, hpar, get_set_same k]
theorem get_set_ne :
    ∀ (k : ℕ) (t : WtTrie) (i j v : ℕ),
      i < 2 ^ k → j < 2 ^ k → j ≠ i → get k (set k t i v) j = get k t j
  | 0, _, i, j, _, hi, hj, hne => by simp at hi hj; omega
  | k + 1, t, i, j, v, hi, hj, hne => by
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      by_cases hpar : i % 2 = 0 <;> by_cases hpar2 : j % 2 = 0 <;>
        simp only [set, get, beq_iff_eq, hpar, hpar2, ↓reduceIte,
          leftChild_mkBranch, rightChild_mkBranch]
      · exact get_set_ne k t.leftChild (i / 2) (j / 2) v (by omega) (by omega) (by omega)
      · exact get_set_ne k t.rightChild (i / 2) (j / 2) v (by omega) (by omega) (by omega)
end WtTrie
def wtGet (wt : WtTrie) (w : ℕ) : ℕ := wt.get 9 w
def wtSet (wt : WtTrie) (w v : ℕ) : WtTrie := wt.set 9 w v
@[simp] theorem wtGet_zero (w : ℕ) : wtGet .zero w = 0 := WtTrie.get_zero 9 w
@[simp] theorem wtGet_set_same (wt : WtTrie) (w v : ℕ) : wtGet (wtSet wt w v) w = v :=
    WtTrie.get_set_same 9 wt w v
theorem wtGet_set_ne (wt : WtTrie) {w x : ℕ} (v : ℕ) (hw : w < 337) (hx : x < 337) (hne : x ≠ w) :
    wtGet (wtSet wt w v) x = wtGet wt x :=
  WtTrie.get_set_ne 9 wt w x v (by omega) (by omega) hne
def linSum (st : ℕ → Bool) (wt : WtTrie) : ℕ :=
  ∑ w ∈ Finset.range 337, if st w then wtGet wt w else 0
theorem linSum_set (st : ℕ → Bool) (wt : WtTrie) (w v : ℕ) (hw : w < 337) : linSum st
    (wtSet wt w v) + (if st w then wtGet wt w else 0) = linSum st wt + (if st w then v else 0)
    := by
  unfold linSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hw)]
  conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hw)]
  rw [wtGet_set_same, Finset.sum_congr rfl fun x hx ↦ by
    rw [wtGet_set_ne wt v hw (Finset.mem_range.mp (Finset.mem_erase.mp hx).2)
      (Finset.mem_erase.mp hx).1]]
  omega
theorem linSum_upd1 (st st' : ℕ → Bool) (wt : WtTrie) (w : ℕ) (hw : w < 337)
    (hother : ∀ q, q < 337 → q ≠ w → st' q = st q) : linSum st' wt +
    (if st w then wtGet wt w else 0) = linSum st wt + (if st' w then wtGet wt w else 0) := by
  unfold linSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hw)]
  conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hw)]
  rw [Finset.sum_congr rfl fun x hx ↦ by
    rw [hother x (Finset.mem_range.mp (Finset.mem_erase.mp hx).2)
      (Finset.mem_erase.mp hx).1]]
  omega
theorem linSum_upd2 (st st' : ℕ → Bool) (wt : WtTrie)
    (w₁ w₂ : ℕ) (h12 : w₁ ≠ w₂) (hw₁ : w₁ < 337) (hw₂ : w₂ < 337)
    (hother : ∀ q, q < 337 → q ≠ w₁ → q ≠ w₂ → st' q = st q) :
    linSum st' wt + (if st w₁ then wtGet wt w₁ else 0) + (if st w₂ then wtGet wt w₂ else 0) =
      linSum st wt + (if st' w₁ then wtGet wt w₁ else 0) + (if st' w₂ then wtGet wt w₂ else 0) := by
  let mid : ℕ → Bool := fun q ↦ if q = w₁ then st' w₁ else st q
  have h1 := linSum_upd1 st mid wt w₁ hw₁ (fun q _ hne ↦ by simp [mid, hne])
  have h2 := linSum_upd1 mid st' wt w₂ hw₂ (fun q hq hne2 ↦ by
    by_cases hne1 : q = w₁
    · subst hne1; simp [mid]
    · simp [mid, hne1, hother q hq hne1 hne2])
  simp only [mid, ↓reduceIte, h12.symm] at h1 h2
  omega
inductive CertStep where
  | copySplit (src W : ℕ) : CertStep
  | oneConst (W : ℕ) : CertStep
  | haStep (wa wb W Wc : ℕ) : CertStep
  | faStep (wa wb wc W Wc : ℕ) : CertStep
  | incHalfStep (wa W Wc : ℕ) : CertStep
  | incFullStep (wa wb W Wc : ℕ) : CertStep
  | cnotMod2Step (src dst W : ℕ) : CertStep
  | liftMod (w k : ℕ) : CertStep
  | flipMod (w : ℕ) : CertStep
  | reduceC0Mod : CertStep
  deriving Repr, DecidableEq
def certOps (cur : ℕ) : CertStep → List DecStep
  | .copySplit src _ => [.allocZero, .cnot src cur]
  | .oneConst _ => [.allocZero, .x cur]
  | .haStep wa wb _ _ => [.andAlloc wa wb, .cnot wb wa]
  | .faStep wa wb wc _ _ =>
      [.cnot wc wa, .cnot wc wb, .andAlloc wa wb, .cnot wc wb, .cnot wb wa, .cnot wc cur]
  | .incHalfStep wa _ _ => [.allocZero, .cnot wa cur, .x wa]
  | .incFullStep wa wb _ _ =>
      [.x wa, .x wb, .andAlloc wa wb, .x wb, .x wa, .x cur, .cnot wb wa, .x wa]
  | .cnotMod2Step src dst _ => [.cnot src dst]
  | .liftMod _ _ => []
  | .flipMod w => [.x w]
  | .reduceC0Mod => []
def certNextCur (cur : ℕ) : CertStep → ℕ
  | .cnotMod2Step _ _ _ => cur
  | .liftMod _ _ => cur
  | .flipMod _ => cur
  | .reduceC0Mod => cur
  | _ => cur + 1
def progOfCert : ℕ → List CertStep → List DecStep
  | _, [] => []
  | cur, cs :: rest => certOps cur cs ++ progOfCert (certNextCur cur cs) rest
theorem certOps_endCur (cur : ℕ) (cs : CertStep) :
    progEndCur cur (certOps cur cs) = certNextCur cur cs := by
  cases cs <;> rfl
def stepCert (M cur : ℕ) (wt : WtTrie) (c0 : ℕ) : CertStep → Option (WtTrie × ℕ)
  | .copySplit src W =>
      if (Nat.blt src cur) && (Nat.blt cur 337) && (Nat.ble W (wtGet wt src)) &&
         (wtGet wt cur == 0) then
        some (wtSet (wtSet wt src (wtGet wt src - W)) cur W, c0)
      else none
  | .oneConst W =>
      if (Nat.blt cur 337) && (wtGet wt cur == 0) && (Nat.ble W c0) then
        some (wtSet wt cur W, c0 - W)
      else none
  | .haStep wa wb W Wc =>
      if (wa != wb) && (Nat.blt wa cur) && (Nat.blt wb cur) && (Nat.blt cur 337) &&
         (wtGet wt wa == W) && (Nat.ble W (wtGet wt wb)) && (wtGet wt cur == 0) &&
         (evalMod M Wc == evalMod M (2 * W)) then
        some (wtSet (wtSet wt wb (wtGet wt wb - W)) cur Wc, c0)
      else none
  | .faStep wa wb wc W Wc =>
      if (wa != wb) && (wa != wc) && (wb != wc) &&
         (Nat.blt wa cur) && (Nat.blt wb cur) && (Nat.blt wc cur) && (Nat.blt cur 337) &&
         (wtGet wt wa == W) && (Nat.ble W (wtGet wt wb)) && (Nat.ble W (wtGet wt wc)) &&
         (wtGet wt cur == 0) && (evalMod M Wc == evalMod M (2 * W)) then
        some (wtSet (wtSet (wtSet wt wb (wtGet wt wb - W)) wc (wtGet wt wc - W)) cur Wc, c0)
      else none
  | .incHalfStep wa W Wc =>
      if (Nat.blt wa cur) && (Nat.blt cur 337) && (wtGet wt wa == W) && (wtGet wt cur == 0) &&
         (Nat.ble W c0) && (evalMod M Wc == evalMod M (2 * W)) then
        some (wtSet wt cur Wc, c0 - W)
      else none
  | .incFullStep wa wb W Wc =>
      if (wa != wb) && (Nat.blt wa cur) && (Nat.blt wb cur) && (Nat.blt cur 337) &&
         (wtGet wt wa == W) && (Nat.ble W (wtGet wt wb)) && (wtGet wt cur == 0) &&
         (Nat.ble W c0) && (evalMod M Wc == evalMod M (2 * W)) then
        some (wtSet (wtSet wt wb (wtGet wt wb - W)) cur Wc, c0 - W)
      else none
  | .cnotMod2Step src dst W =>
      if (src != dst) && (Nat.blt src cur) && (Nat.blt dst cur) && (Nat.ble cur 337) &&
         (wtGet wt dst == W) && (Nat.ble W (wtGet wt src)) && (evalMod M (2 * W) == 0) then
        some (wtSet wt src (wtGet wt src - W), c0)
      else none
  | .liftMod w k =>
      if (Nat.blt 0 M) && (Nat.blt w cur) && (Nat.ble cur 337) then
        some (wtSet wt w (wtGet wt w + k * M), c0)
      else none
  | .flipMod w =>
      if (Nat.blt 0 M) && (Nat.blt w cur) && (Nat.ble cur 337) && (Nat.ble (wtGet wt w) M) then
        let old := wtGet wt w
        some (wtSet wt w (M - old), c0 + old)
      else none
  | .reduceC0Mod =>
      if Nat.blt 0 M then
        some (wt, c0 % M)
      else none
def runCert (M : ℕ) : ℕ → WtTrie → ℕ → List CertStep → Option (WtTrie × ℕ)
  | _, wt, c0, [] => some (wt, c0)
  | cur, wt, c0, cs :: rest =>
      match stepCert M cur wt c0 cs with
      | none => none
      | some (wt', c0') => runCert M (certNextCur cur cs) wt' c0' rest
def checkCert (M cur : ℕ) (initWt : WtTrie) (initC0 : ℕ)
    (targetWt : WtTrie) (targetC0 : ℕ) (cert : List CertStep) : Bool :=
  match runCert M cur initWt initC0 cert with
  | none => false
  | some (wtEnd, c0End) => wtEnd == targetWt && c0End == targetC0
theorem evalMod_erase_zero (M a b : ℕ) (h : evalMod M b = evalMod M 0) :
    evalMod M a = evalMod M (a + b) := by
  have h0 : evalMod M (a + b) = evalMod M (a + 0) := evalMod_congr_right M a b 0 h
  rw [h0, Nat.add_zero]
theorem stepCert_sound (M cur : ℕ) (wt wt' : WtTrie) (c0 c0' : ℕ) (cs : CertStep)
    (hok : stepCert M cur wt c0 cs = some (wt', c0')) : progWellFormed cur (certOps cur cs) =
    true ∧ ∀ st : ℕ → Bool, (∀ q, cur ≤ q → st q = false) → (∀ q, certNextCur cur cs ≤ q →
    evalBool (certOps cur cs) cur st q = false) ∧ evalMod M
    (c0' + linSum (evalBool (certOps cur cs) cur st) wt') = evalMod M (c0 + linSum st wt) := by
  have mkStep (hwf : progWellFormed cur (certOps cur cs) = true)
      (hmod : ∀ st : ℕ → Bool, (∀ q, cur ≤ q → st q = false) →
        evalMod M (c0' + linSum (evalBool (certOps cur cs) cur st) wt') =
          evalMod M (c0 + linSum st wt)) :
      progWellFormed cur (certOps cur cs) = true ∧ ∀ st : ℕ → Bool,
        (∀ q, cur ≤ q → st q = false) →
        (∀ q, certNextCur cur cs ≤ q → evalBool (certOps cur cs) cur st q = false) ∧
        evalMod M (c0' + linSum (evalBool (certOps cur cs) cur st) wt') =
          evalMod M (c0 + linSum st wt) :=
    ⟨hwf, fun st hcl ↦ ⟨fun q hq ↦ evalBool_clean _ cur st hwf hcl q
      (by
        rw [certOps_endCur]
        exact hq), hmod st hcl⟩⟩
  have hLe2 {wa wb W : ℕ} (hab : wa ≠ wb) (hwa : wa < 337) (hwb : wb < 337)
      (hwta : wtGet wt wa = W) (hwtb : W ≤ wtGet wt wb) (st : ℕ → Bool) :
      (if st wa then W else 0) + (if st wb then W else 0) ≤ linSum st wt := by
    unfold linSum
    have hma : wa ∈ Finset.range 337 := Finset.mem_range.mpr hwa
    have hmb : wb ∈ (Finset.range 337).erase wa :=
      Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_range.mpr hwb⟩
    rw [← Finset.add_sum_erase _ _ hma, ← Finset.add_sum_erase _ _ hmb, hwta]
    cases st wb <;> simp at hwtb ⊢; omega
  cases cs with
  | copySplit src W =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨⟨hsrc, hcur⟩, hW⟩, hcur0⟩
      refine mkStep (by
          simp [certOps, progWellFormed, DecStep.wellFormed, DecStep.nextCur]
          omega)
        fun st hcl ↦ ?_
      let wt1 := wtSet wt src (wtGet wt src - W)
      let wtN := wtSet wt1 cur W
      let st' := evalBool (certOps cur (.copySplit src W)) cur st
      have hst_cur0 : st cur = false := hcl cur le_rfl
      have hst'_cur : st' cur = st src := by
        simp [st', certOps, evalBool, DecStep.stepBool, hst_cur0]
      have hu := linSum_upd1 st st' wtN cur hcur fun q _ hne ↦ by
        simp [st', certOps, evalBool, DecStep.stepBool, hne]
      have hs2 := linSum_set st wt1 cur W hcur
      have hs1 := linSum_set st wt src (wtGet wt src - W) (lt_trans hsrc hcur)
      rw [hst_cur0, hst'_cur, wtGet_set_same wt1 cur W] at hu
      rw [hst_cur0, wtGet_set_ne wt _ (lt_trans hsrc hcur) hcur (Nat.ne_of_gt hsrc), hcur0] at hs2
      have heq : linSum st' wtN = linSum st wt := by
        dsimp only [wt1, wtN] at hu hs2 hs1 ⊢
        cases hsb : st src <;> simp [hsb] at hu hs2 hs1 <;> omega
      rw [heq]
  | oneConst W =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨hcur, hcur0⟩, hW⟩
      refine mkStep (by
          simp [certOps, progWellFormed, DecStep.wellFormed, DecStep.nextCur]
          omega)
        fun st hcl ↦ ?_
      let st' := evalBool (certOps cur (.oneConst W)) cur st
      have hst_cur0 : st cur = false := hcl cur le_rfl
      have hst'_cur : st' cur = true := by
        simp [st', certOps, evalBool, DecStep.stepBool, hst_cur0]
      have hu := linSum_upd1 st st' (wtSet wt cur W) cur hcur fun q _ hne ↦ by
        simp [st', certOps, evalBool, DecStep.stepBool, hne]
      have hs1 := linSum_set st wt cur W hcur
      rw [hst_cur0, hst'_cur, wtGet_set_same] at hu
      rw [hst_cur0, hcur0] at hs1
      have heq : c0 - W + linSum st' (wtSet wt cur W) = c0 + linSum st wt := by
        simp at hu hs1
        omega
      rw [heq]
  | haStep wa wb W Wc =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, bne_iff_ne, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨⟨⟨hab, hwa⟩, hwb⟩, hcur⟩, hwta⟩, hwtb⟩, hwtc⟩, hWmod⟩
      refine mkStep (by
          simp [certOps, progWellFormed, DecStep.wellFormed, DecStep.nextCur, hab, hab.symm]
          omega) fun st hcl ↦ ?_
      let wt1 := wtSet wt wb (wtGet wt wb - W)
      let wtN := wtSet wt1 cur Wc
      let st' := evalBool (certOps cur (.haStep wa wb W Wc)) cur st
      have hst_cur0 : st cur = false := hcl cur le_rfl
      have hst'_wa : st' wa = xor (st wa) (st wb) := by
        simp [st', certOps, evalBool, DecStep.stepBool, Nat.ne_of_lt hwa, Nat.ne_of_lt hwb]
      have hst'_cur : st' cur = (st wa && st wb) := by
        simp [st', certOps, evalBool, DecStep.stepBool, (Nat.ne_of_lt hwa).symm]
      have hu := linSum_upd2 st st' wtN wa cur (Nat.ne_of_lt hwa) (lt_trans hwa hcur) hcur
        fun q _ h1 h2 ↦ by simp [st', certOps, evalBool, DecStep.stepBool, h1, h2]
      have hs2 := linSum_set st wt1 cur Wc hcur
      have hs1 := linSum_set st wt wb (wtGet wt wb - W) (lt_trans hwb hcur)
      have hget_wa : wtGet wtN wa = W := by
        rw [wtGet_set_ne wt1 _ hcur (lt_trans hwa hcur) (Nat.ne_of_lt hwa),
          wtGet_set_ne wt _ (lt_trans hwb hcur) (lt_trans hwa hcur) hab, hwta]
      rw [hst_cur0, hst'_wa, hst'_cur, hget_wa, wtGet_set_same wt1 cur Wc] at hu
      rw [hst_cur0, wtGet_set_ne wt _ (lt_trans hwb hcur) hcur (Nat.ne_of_gt hwb), hwtc] at hs2
      have hwta_le := hLe2 hab (lt_trans hwa hcur) (lt_trans hwb hcur) hwta hwtb st
      have hbase : c0 + linSum st' wtN = (c0 + (linSum st wt - (if st wa then W else 0) -
          (if st wb then W else 0)) + (if xor (st wa) (st wb) then W else 0)) +
          (if st wa && st wb then Wc else 0) := by
        dsimp only [wt1, wtN] at hu hs2 hs1 ⊢
        cases hsa : st wa <;> cases hsb : st wb <;>
          simp [hsa, hsb] at hu hs2 hs1 hwtb hwta_le ⊢ <;> omega
      have hexact : (c0 + (linSum st wt - (if st wa then W else 0) - (if st wb then W else 0)) +
          (if xor (st wa) (st wb) then W else 0)) +
          (if st wa && st wb then 2 * W else 0) = c0 + linSum st wt := by
        cases hsa : st wa <;> cases hsb : st wb <;> simp [hsa, hsb] at hwta_le ⊢ <;> omega
      rw [hbase]
      exact (evalMod_congr_right M _ _ _ (evalMod_mul_bit M Wc W (st wa && st wb) hWmod)).trans
        (by rw [hexact])
  | faStep wa wb wc W Wc =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, bne_iff_ne, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hac⟩, hbc⟩, hwa⟩, hwb⟩, hwc⟩, hcur⟩, hwta⟩, hwtb⟩,
        hwtc_in⟩, hwtcur0⟩, hWmod⟩
      refine mkStep (by
          simp [certOps, progWellFormed, DecStep.wellFormed, DecStep.nextCur, hab, hab.symm,
            hac.symm, hbc.symm]
          omega) fun st hcl ↦ ?_
      let wt1 := wtSet wt wb (wtGet wt wb - W)
      let wt2 := wtSet wt1 wc (wtGet wt wc - W)
      let wtN := wtSet wt2 cur Wc
      let st' := evalBool (certOps cur (.faStep wa wb wc W Wc)) cur st
      have hst_cur0 : st cur = false := hcl cur le_rfl
      have hst'_wa : st' wa = xor (xor (st wa) (st wc)) (st wb) := by
        cases hsa : st wa <;> cases hsb : st wb <;> cases hsc : st wc <;>
          simp [st', certOps, evalBool, DecStep.stepBool, DecStep.nextCur, hab, hab.symm,
            hac.symm, hbc.symm, Nat.ne_of_lt hwa, (Nat.ne_of_lt hwa).symm, Nat.ne_of_lt hwb,
            (Nat.ne_of_lt hwb).symm, Nat.ne_of_lt hwc, hsa, hsb, hsc]
      have hst'_cur : st' cur = xor ((xor (st wa) (st wc)) && (xor (st wb) (st wc))) (st wc) := by
        cases hsa : st wa <;> cases hsb : st wb <;> cases hsc : st wc <;>
          simp [st', certOps, evalBool, DecStep.stepBool, DecStep.nextCur, hab, hab.symm,
            hac.symm, hbc.symm, Nat.ne_of_lt hwa, (Nat.ne_of_lt hwa).symm, Nat.ne_of_lt hwb,
            (Nat.ne_of_lt hwb).symm, Nat.ne_of_lt hwc, hsa, hsb, hsc]
      have hst'_other : ∀ q, q < 337 → q ≠ wa → q ≠ cur → st' q = st q := fun q _ h1 h2 ↦ by
        by_cases hqb : q = wb
        · subst hqb
          cases hsb : st q <;> cases hsc : st wc <;>
            simp [st', certOps, evalBool, DecStep.stepBool, DecStep.nextCur, hab, hab.symm,
              hac.symm, hbc.symm, Nat.ne_of_lt hwa, (Nat.ne_of_lt hwa).symm, Nat.ne_of_lt hwb,
              (Nat.ne_of_lt hwb).symm, Nat.ne_of_lt hwc, hsb, hsc]
        · simp [st', certOps, evalBool, DecStep.stepBool, DecStep.nextCur, h1, h2, hqb]
      have hu := linSum_upd2 st st' wtN wa cur (Nat.ne_of_lt hwa) (lt_trans hwa hcur) hcur
        hst'_other
      have hs1 := linSum_set st wt wb (wtGet wt wb - W) (lt_trans hwb hcur)
      have hs2 := linSum_set st wt1 wc (wtGet wt wc - W) (lt_trans hwc hcur)
      have hs3 := linSum_set st wt2 cur Wc hcur
      have hwt2_cur : wtGet wt2 cur = 0 := by
        rw [wtGet_set_ne wt1 _ (lt_trans hwc hcur) hcur (Nat.ne_of_gt hwc),
          wtGet_set_ne wt _ (lt_trans hwb hcur) hcur (Nat.ne_of_gt hwb), hwtcur0]
      have hwtN_wa : wtGet wtN wa = W := by
        rw [wtGet_set_ne wt2 _ hcur (lt_trans hwa hcur) (Nat.ne_of_lt hwa),
          wtGet_set_ne wt1 _ (lt_trans hwc hcur) (lt_trans hwa hcur) hac,
          wtGet_set_ne wt _ (lt_trans hwb hcur) (lt_trans hwa hcur) hab, hwta]
      rw [wtGet_set_ne wt _ (lt_trans hwb hcur) (lt_trans hwc hcur) hbc.symm] at hs2
      rw [hst_cur0, hwt2_cur] at hs3
      rw [hst_cur0, hst'_wa, hst'_cur, hwtN_wa, wtGet_set_same wt2 cur Wc] at hu
      let sumOut := xor (xor (st wa) (st wc)) (st wb)
      let carOut := xor ((xor (st wa) (st wc)) && (xor (st wb) (st wc))) (st wc)
      have hwta_le : (if st wa then W else 0) + (if st wb then W else 0) +
          (if st wc then W else 0) ≤ linSum st wt := by
        unfold linSum
        have hma : wa ∈ Finset.range 337 := Finset.mem_range.mpr (lt_trans hwa hcur)
        have hmb : wb ∈ (Finset.range 337).erase wa :=
          Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_range.mpr (lt_trans hwb hcur)⟩
        have hmc : wc ∈ ((Finset.range 337).erase wa).erase wb :=
          Finset.mem_erase.mpr ⟨hbc.symm,
            Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_range.mpr (lt_trans hwc hcur)⟩⟩
        rw [← Finset.add_sum_erase _ _ hma, ← Finset.add_sum_erase _ _ hmb,
          ← Finset.add_sum_erase _ _ hmc, hwta]
        cases st wb <;> cases st wc <;> simp at hwtb hwtc_in ⊢ <;> omega
      have hbase : c0 + linSum st' wtN = (c0 + (linSum st wt - (if st wa then W else 0) -
          (if st wb then W else 0) - (if st wc then W else 0)) + (if sumOut then W else 0)) +
          (if carOut then Wc else 0) := by
        dsimp only [wt1, wt2, wtN] at hu hs1 hs2 hs3 ⊢
        cases hsa : st wa <;> cases hsb : st wb <;> cases hsc : st wc <;>
          simp [sumOut, carOut, hsa, hsb, hsc] at hu hs1 hs2 hs3 hwta_le ⊢ <;> omega
      have hexact : (c0 + (linSum st wt - (if st wa then W else 0) - (if st wb then W else 0) -
          (if st wc then W else 0)) + (if sumOut then W else 0)) +
          (if carOut then 2 * W else 0) = c0 + linSum st wt := by
        cases hsa : st wa <;> cases hsb : st wb <;> cases hsc : st wc <;>
          simp [sumOut, carOut, hsa, hsb, hsc] at hwta_le ⊢ <;> omega
      rw [hbase]
      exact (evalMod_congr_right M _ _ _ (evalMod_mul_bit M Wc W carOut hWmod)).trans
        (by rw [hexact])
  | incHalfStep wa W Wc =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨hwa, hcur⟩, hwta⟩, hwtc0⟩, hc0W⟩, hWmod⟩
      refine mkStep (by
          simp [certOps, progWellFormed, DecStep.wellFormed, DecStep.nextCur, Nat.ne_of_lt hwa]
          omega) fun st hcl ↦ ?_
      let wtN := wtSet wt cur Wc
      let st' := evalBool (certOps cur (.incHalfStep wa W Wc)) cur st
      have hst_cur0 : st cur = false := hcl cur le_rfl
      have hst'_wa : st' wa = !st wa := by
        simp [st', certOps, evalBool, DecStep.stepBool, Nat.ne_of_lt hwa]
      have hst'_cur : st' cur = st wa := by
        simp [st', certOps, evalBool, DecStep.stepBool, (Nat.ne_of_lt hwa).symm, hst_cur0]
      have hu := linSum_upd2 st st' wtN wa cur (Nat.ne_of_lt hwa) (lt_trans hwa hcur) hcur
        fun q _ h1 h2 ↦ by simp [st', certOps, evalBool, DecStep.stepBool, h1, h2]
      have hs1 := linSum_set st wt cur Wc hcur
      rw [hst_cur0, hwtc0] at hs1
      rw [hst_cur0, hst'_wa, hst'_cur,
        wtGet_set_ne wt _ hcur (lt_trans hwa hcur) (Nat.ne_of_lt hwa), hwta,
        wtGet_set_same wt cur Wc] at hu
      have hwta_le : (if st wa then W else 0) ≤ linSum st wt := by
        unfold linSum
        rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (lt_trans hwa hcur)), hwta]
        omega
      have hbase : c0 - W + linSum st' wtN = (c0 - W + (linSum st wt - (if st wa then W else 0)) +
          (if !st wa then W else 0)) + (if st wa then Wc else 0) := by
        dsimp only [wtN] at hu hs1 ⊢
        cases hsa : st wa <;> simp [hsa] at hu hs1 hwta_le ⊢ <;> omega
      have hexact : (c0 - W + (linSum st wt - (if st wa then W else 0)) +
          (if !st wa then W else 0)) + (if st wa then 2 * W else 0) = c0 + linSum st wt := by
        cases hsa : st wa <;> simp [hsa] at hwta_le ⊢ <;> omega
      rw [hbase]
      exact (evalMod_congr_right M _ _ _ (evalMod_mul_bit M Wc W (st wa) hWmod)).trans
        (by rw [hexact])
  | incFullStep wa wb W Wc =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, bne_iff_ne, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨⟨⟨⟨hab, hwa⟩, hwb⟩, hcur⟩, hwta⟩, hwtb⟩, hwtc0⟩, hc0W⟩, hWmod⟩
      refine mkStep (by
          simp [certOps, progWellFormed, DecStep.wellFormed, DecStep.nextCur, hab, hab.symm,
            hwa, hwb, show wa < cur + 1 by omega, show wb < cur + 1 by omega,
            show cur + 1 ≤ 337 by omega]) fun st hcl ↦ ?_
      let wt1 := wtSet wt wb (wtGet wt wb - W)
      let wtN := wtSet wt1 cur Wc
      let st' := evalBool (certOps cur (.incFullStep wa wb W Wc)) cur st
      have hst_cur0 : st cur = false := hcl cur le_rfl
      have hst'_wa : st' wa = !(xor (st wa) (st wb)) := by
        cases hsa : st wa <;> cases hsb : st wb <;>
          simp [st', certOps, evalBool, DecStep.stepBool, DecStep.nextCur, hab, hab.symm,
            Nat.ne_of_lt hwa, Nat.ne_of_lt hwb, hsa, hsb]
      have hst'_cur : st' cur = (st wa || st wb) := by
        cases hsa : st wa <;> cases hsb : st wb <;>
          simp [st', certOps, evalBool, DecStep.stepBool, DecStep.nextCur, hab, hab.symm,
            Nat.ne_of_lt hwa, (Nat.ne_of_lt hwa).symm, Nat.ne_of_lt hwb,
            (Nat.ne_of_lt hwb).symm, hsa, hsb]
      have hst'_other : ∀ q, q < 337 → q ≠ wa → q ≠ cur → st' q = st q := fun q _ h1 h2 ↦ by
        by_cases hqb : q = wb
        · subst hqb
          cases hsb : st q <;>
            simp [st', certOps, evalBool, DecStep.stepBool, DecStep.nextCur, hab, hab.symm,
              Nat.ne_of_lt hwa, Nat.ne_of_lt hwb, hsb]
        · simp [st', certOps, evalBool, DecStep.stepBool, DecStep.nextCur, h1, h2, hqb]
      have hu := linSum_upd2 st st' wtN wa cur (Nat.ne_of_lt hwa) (lt_trans hwa hcur) hcur
        hst'_other
      have hs1 := linSum_set st wt wb (wtGet wt wb - W) (lt_trans hwb hcur)
      have hs2 := linSum_set st wt1 cur Wc hcur
      have hwtN_wa : wtGet wtN wa = W := by
        rw [wtGet_set_ne wt1 _ hcur (lt_trans hwa hcur) (Nat.ne_of_lt hwa),
          wtGet_set_ne wt _ (lt_trans hwb hcur) (lt_trans hwa hcur) hab, hwta]
      rw [hst_cur0, wtGet_set_ne wt _ (lt_trans hwb hcur) hcur (Nat.ne_of_gt hwb), hwtc0] at hs2
      rw [hst_cur0, hst'_wa, hst'_cur, hwtN_wa, wtGet_set_same wt1 cur Wc] at hu
      have hwta_le := hLe2 hab (lt_trans hwa hcur) (lt_trans hwb hcur) hwta hwtb st
      have hbase : c0 - W + linSum st' wtN =
          (c0 - W + (linSum st wt - (if st wa then W else 0) - (if st wb then W else 0)) +
            (if !(xor (st wa) (st wb)) then W else 0)) + (if st wa || st wb then Wc else 0) := by
        dsimp only [wt1, wtN] at hu hs1 hs2 ⊢
        cases hsa : st wa <;> cases hsb : st wb <;>
          simp [hsa, hsb] at hu hs1 hs2 hwtb hwta_le ⊢ <;> omega
      have hexact :
          (c0 - W + (linSum st wt - (if st wa then W else 0) - (if st wb then W else 0)) +
            (if !(xor (st wa) (st wb)) then W else 0)) + (if st wa || st wb then 2 * W else 0) =
            c0 + linSum st wt := by
        cases hsa : st wa <;> cases hsb : st wb <;> simp [hsa, hsb] at hwta_le ⊢ <;> omega
      rw [hbase]
      generalize c0 - W + (linSum st wt - (if st wa then W else 0) - (if st wb then W else 0)) +
        (if !(xor (st wa) (st wb)) then W else 0) = baseVal at hexact ⊢
      exact (evalMod_congr_right M baseVal _ _
        (evalMod_mul_bit M Wc W (st wa || st wb) hWmod)).trans (by rw [hexact])
  | cnotMod2Step src dst W =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, bne_iff_ne, Nat.blt_eq, Nat.ble_eq, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨⟨hne, hsrc⟩, hdst⟩, hcur⟩, hwtdst⟩, hwtsrc⟩, h2W0⟩
      refine mkStep (by simp [certOps, progWellFormed, DecStep.wellFormed, hne, hsrc, hdst])
        fun st _ ↦ ?_
      let wtN := wtSet wt src (wtGet wt src - W)
      let st' := evalBool (certOps cur (.cnotMod2Step src dst W)) cur st
      have hu := linSum_upd1 st st' wtN dst (lt_of_lt_of_le hdst hcur) fun q _ h1 ↦ by
        simp [st', certOps, evalBool, DecStep.stepBool, h1]
      have hs1 := linSum_set st wt src (wtGet wt src - W) (lt_of_lt_of_le hsrc hcur)
      have hst'_dst : st' dst = xor (st dst) (st src) := by
        simp [st', certOps, evalBool, DecStep.stepBool]
      rw [hst'_dst,
        wtGet_set_ne wt _ (lt_of_lt_of_le hsrc hcur) (lt_of_lt_of_le hdst hcur) hne.symm,
        hwtdst] at hu
      have hsum_rel : c0 + linSum st wt = (c0 + linSum st' wtN) +
          (if st src && st dst then 2 * W else 0) := by
        dsimp only [wtN] at hu hs1 ⊢
        cases hss : st src <;> cases hsd : st dst <;>
          simp [hss, hsd] at hu hs1 hwtsrc ⊢ <;> omega
      rw [hsum_rel]
      have hzero : evalMod M (if st src && st dst then 2 * W else 0) = evalMod M 0 := by
        cases st src && st dst
        · rfl
        · exact h2W0.trans (by simp [evalMod])
      exact evalMod_erase_zero M (c0 + linSum st' wtN) _ hzero
  | liftMod w k =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hcond
      rcases hcond with ⟨⟨hM, hw⟩, hcur⟩
      refine ⟨rfl, fun st hcl ↦ ⟨hcl, ?_⟩⟩
      dsimp only [certOps, evalBool]
      have hs := linSum_set st wt w (wtGet wt w + k * M) (lt_of_lt_of_le hw hcur)
      have hsum : c0 + linSum st (wtSet wt w (wtGet wt w + k * M)) =
          (c0 + linSum st wt) + (if st w then k * M else 0) := by
        cases hsw : st w <;> simp [hsw] at hs ⊢ <;> omega
      rw [hsum]
      have hzero : evalMod M (if st w then k * M else 0) = evalMod M 0 := by
        cases st w
        · rfl
        · simp [evalMod, beq_false_of_ne (Nat.ne_of_gt hM)]
      exact (evalMod_erase_zero M (c0 + linSum st wt) _ hzero).symm
  | flipMod w =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hcond
      rcases hcond with ⟨⟨⟨hM, hw⟩, hcur⟩, hold⟩
      refine mkStep (by simp [certOps, progWellFormed, DecStep.wellFormed, hw]) fun st _ ↦ ?_
      let wtN := wtSet wt w (M - wtGet wt w)
      let st' := evalBool (certOps cur (.flipMod w)) cur st
      have hu := linSum_upd1 st st' wtN w (lt_of_lt_of_le hw hcur) fun q _ hne ↦ by
        simp [st', certOps, evalBool, DecStep.stepBool, hne]
      have hs := linSum_set st wt w (M - wtGet wt w) (lt_of_lt_of_le hw hcur)
      have hst'_w : st' w = !st w := by simp [st', certOps, evalBool, DecStep.stepBool]
      rw [hst'_w, wtGet_set_same wt w _] at hu
      have hsum : (c0 + wtGet wt w) + linSum st' wtN =
          (c0 + linSum st wt) + (if st w then 0 else M) := by
        dsimp only [wtN] at hu hs ⊢
        cases hsw : st w <;> simp [hsw] at hu hs ⊢ <;> omega
      rw [hsum]
      have hzero : evalMod M (if st w then 0 else M) = evalMod M 0 := by
        cases st w
        · simp [evalMod, beq_false_of_ne (Nat.ne_of_gt hM)]
        · rfl
      exact (evalMod_erase_zero M (c0 + linSum st wt) _ hzero).symm
  | reduceC0Mod =>
      dsimp only [stepCert] at hok
      split_ifs at hok with hcond
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hok)
      simp only [Nat.blt_eq] at hcond
      refine ⟨rfl, fun st hcl ↦ ⟨hcl, ?_⟩⟩
      dsimp only [certOps, evalBool]
      simp only [evalMod, beq_false_of_ne (Nat.ne_of_gt hcond), Bool.false_eq_true, ↓reduceIte]
      rw [Nat.add_mod (c0 % M), Nat.mod_mod, ← Nat.add_mod]
theorem checkCert_sound (M : ℕ) (cert : List CertStep) : ∀ (cur : ℕ)
    (initWt targetWt : WtTrie) (initC0 targetC0 : ℕ), checkCert M cur initWt initC0 targetWt
    targetC0 cert = true → progWellFormed cur (progOfCert cur cert) = true ∧ ∀ st : ℕ → Bool,
    (∀ q, cur ≤ q → st q = false) → (∀ q, progEndCur cur (progOfCert cur cert) ≤ q → evalBool
    (progOfCert cur cert) cur st q = false) ∧ evalMod M
    (targetC0 + linSum (evalBool (progOfCert cur cert) cur st) targetWt) = evalMod M
    (initC0 + linSum st initWt) := by
  induction cert with
  | nil =>
      intro cur initWt targetWt initC0 targetC0 hchk
      simp only [checkCert, runCert, Bool.and_eq_true, beq_iff_eq] at hchk
      rcases hchk with ⟨rfl, rfl⟩
      exact ⟨rfl, fun st hcl ↦ ⟨hcl, rfl⟩⟩
  | cons cs rest ih =>
      intro cur initWt targetWt initC0 targetC0 hchk
      dsimp only [checkCert, runCert] at hchk
      cases hstep : stepCert M cur initWt initC0 cs with
      | none => simp [hstep] at hchk
      | some pair =>
          rw [hstep] at hchk
          obtain ⟨wtMid, c0Mid⟩ := pair
          obtain ⟨hwfStep, hsemStep⟩ :=
            stepCert_sound M cur initWt wtMid initC0 c0Mid cs hstep
          have hsub : checkCert M (certNextCur cur cs) wtMid c0Mid targetWt targetC0 rest = true :=
            hchk
          obtain ⟨hwfRest, hsemRest⟩ := ih (certNextCur cur cs) wtMid targetWt c0Mid targetC0 hsub
          refine ⟨?_, fun st hcl ↦ ?_⟩
          · rw [progOfCert, progWellFormed_append, certOps_endCur, hwfStep, hwfRest]; rfl
          · obtain ⟨hclMid, heq1⟩ := hsemStep st hcl
            obtain ⟨hclEnd, heq2⟩ := hsemRest _ hclMid
            rw [progOfCert, evalBool_append, progEndCur_append, certOps_endCur]
            exact ⟨hclEnd, heq2.trans heq1⟩
def regValList (st : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | w :: ws => (if st w then 1 else 0) + 2 * regValList st ws
theorem regValList_lt : ∀ (ws : List ℕ) (st : ℕ → Bool), regValList st ws < 2 ^ ws.length
  | [], _ => by simp [regValList]
  | w :: ws, st => by
      have ih := regValList_lt ws st
      simp only [regValList, List.length_cons, Nat.pow_succ]
      cases st w <;> simp <;> omega
theorem regValList_congr {st₁ st₂ : ℕ → Bool} :
    ∀ {ws : List ℕ}, (∀ w ∈ ws, st₁ w = st₂ w) → regValList st₁ ws = regValList st₂ ws
  | [], _ => rfl
  | w :: ws, h => by
      simp only[regValList, h w (.head _), regValList_congr (fun q hq ↦ h q (.tail _ hq))]
theorem regValList_append :
    ∀ (xs ys : List ℕ) (st : ℕ → Bool),
      regValList st (xs ++ ys) = regValList st xs + 2 ^ xs.length * regValList st ys
  | [], ys, st => by simp [regValList]
  | x :: xs, ys, st => by
      simp only [List.cons_append, regValList, regValList_append xs ys st, List.length_cons,
        Nat.pow_succ]
      ring
def pairsVal (st : ℕ → Bool) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (w, v) :: ps => (if st w then v else 0) + pairsVal st ps
def sumPairs : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_, v) :: ps => v + sumPairs ps
theorem pairsVal_le_sumPairs :
    ∀ (ps : List (ℕ × ℕ)) (st : ℕ → Bool), pairsVal st ps ≤ sumPairs ps
  | [], _ => le_rfl
  | (w, v) :: ps, st => by
      have ih := pairsVal_le_sumPairs ps st
      cases h : st w <;> simp [pairsVal, sumPairs, h] <;> omega
def buildWtAux : List (ℕ × ℕ) → WtTrie → WtTrie
  | [], acc => acc
  | (w, v) :: ps, acc => buildWtAux ps (wtSet acc w (wtGet acc w + v))
def mkPairsWt (ps : List (ℕ × ℕ)) : WtTrie := buildWtAux ps .zero
theorem linSum_zero_trie (st : ℕ → Bool) : linSum st .zero = 0 := by
  unfold linSum
  apply Finset.sum_eq_zero
  intro w _
  simp
theorem linSum_buildWtAux :
    ∀ (ps : List (ℕ × ℕ)) (acc : WtTrie) (st : ℕ → Bool),
      (∀ p ∈ ps, p.1 < 337) →
      linSum st (buildWtAux ps acc) = linSum st acc + pairsVal st ps
  | [], acc, st, _ => by simp [buildWtAux, pairsVal]
  | (w, v) :: ps, acc, st, hlt => by
      have hw : w < 337 := hlt (w, v) (.head _)
      rw [buildWtAux, linSum_buildWtAux ps _ st (fun p hp ↦ hlt p (.tail _ hp)), pairsVal]
      have hs := linSum_set st acc w (wtGet acc w + v) hw
      cases h : st w <;> simp [h] at hs ⊢ <;> omega
theorem linSum_mkPairsWt (ps : List (ℕ × ℕ)) (st : ℕ → Bool) (hlt : ∀ p ∈ ps, p.1 < 337) :
    linSum st (mkPairsWt ps) = pairsVal st ps := by
  rw [mkPairsWt, linSum_buildWtAux ps _ st hlt, linSum_zero_trie, zero_add]
def powPairsAux : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | k, w :: ws => (w, 2 ^ k) :: powPairsAux (k + 1) ws
def regPairs (ws : List ℕ) : List (ℕ × ℕ) := powPairsAux 0 ws
theorem pairsVal_powPairsAux :
    ∀ (ws : List ℕ) (k : ℕ) (st : ℕ → Bool),
      pairsVal st (powPairsAux k ws) = 2 ^ k * regValList st ws
  | [], _, _ => by simp [powPairsAux, pairsVal, regValList]
  | w :: ws, k, st => by
      rw [powPairsAux, pairsVal, pairsVal_powPairsAux ws (k + 1) st, regValList]
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      cases st w <;> simp [hp] <;> ring
theorem linSum_regWt (ws : List ℕ) (st : ℕ → Bool) (hlt : ∀ p ∈ regPairs ws, p.1 < 337) :
    linSum st (mkPairsWt (regPairs ws)) = regValList st ws := by
  rw [linSum_mkPairsWt _ st hlt, regPairs, pairsVal_powPairsAux, pow_zero, one_mul]
def u36Wires : List ℕ :=
  [3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,
  37,38]
def u8Wires : List ℕ := [17,18,19,20,21,22,23,24]
def clampGe218 (b1 b2 b3 b4 b5 b6 b7 : Bool) : Bool :=
  b7 && (b6 && (b5 || (b4 && (b3 && (b2 || b1)))))
theorem clampGe218_spec : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, Bool.not
    (clampGe218 b1 b2 b3 b4 b5 b6 b7) = decide ((if b0 then 1 else 0) + 2 * ((if b1 then 1
    else 0) + 2 * ((if b2 then 1 else 0) + 2 * ((if b3 then 1 else 0) + 2 * ((if b4 then 1
    else 0) + 2 * ((if b5 then 1 else 0) + 2 * ((if b6 then 1 else 0) + 2 * ((if b7 then 1
    else 0) + 2 * 0))))))) < 218) := by
  decide
inductive BExpr where
  | const (b : Bool)
  | var (w : ℕ)
  | not (e : BExpr)
  | xor (a b : BExpr)
  | and (a b : BExpr)
  deriving DecidableEq
def BExpr.eval (st : ℕ → Bool) : BExpr → Bool
  | .const b => b
  | .var w => st w
  | .not e => !(e.eval st)
  | .xor a b => Bool.xor (a.eval st) (b.eval st)
  | .and a b => a.eval st && b.eval st
def bexprUsesOnly (vs : List ℕ) : BExpr → Bool
  | .const _ => true
  | .var w => vs.contains w
  | .not e => bexprUsesOnly vs e
  | .xor a b => bexprUsesOnly vs a && bexprUsesOnly vs b
  | .and a b => bexprUsesOnly vs a && bexprUsesOnly vs b
def packAssign (st : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | v :: vs => (if st v then 1 else 0) + 2 * packAssign st vs
theorem packAssign_lt : ∀ (vs : List ℕ) (st : ℕ → Bool), packAssign st vs < 2 ^ vs.length
  | [], _ => by simp [packAssign]
  | v :: vs, st => by
      have ih := packAssign_lt vs st
      simp only [packAssign, List.length_cons, Nat.pow_succ]
      cases st v <;> simp <;> omega
def lookupMask : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => false
  | v :: vs, mask, w => if w == v then mask % 2 == 1 else lookupMask vs (mask / 2) w
theorem lookupMask_packAssign :
    ∀ (vs : List ℕ) (st : ℕ → Bool) {w : ℕ}, w ∈ vs →
      lookupMask vs (packAssign st vs) w = st w
  | [], _, _, h => nomatch h
  | v :: vs, st, w, h => by
      simp only [lookupMask, packAssign]
      by_cases hwv : w = v
      · subst hwv
        simp only [beq_self_eq_true, ↓reduceIte]
        cases st w <;> simp
      · have hmem : w ∈ vs := (List.mem_cons.mp h).resolve_left hwv
        have hdiv : ((if st v then 1 else 0) + 2 * packAssign st vs) / 2 = packAssign st vs := by
          cases st v <;> simp; omega
        simp only [beq_eq_false_iff_ne.mpr hwv, Bool.false_eq_true, ↓reduceIte, hdiv]
        exact lookupMask_packAssign vs st hmem
def evalMask (vs : List ℕ) (mask : ℕ) : BExpr → Bool
  | .const b => b
  | .var w => lookupMask vs mask w
  | .not e => !(evalMask vs mask e)
  | .xor a b => Bool.xor (evalMask vs mask a) (evalMask vs mask b)
  | .and a b => evalMask vs mask a && evalMask vs mask b
theorem evalMask_packAssign (vs : List ℕ) (st : ℕ → Bool) :
    ∀ {e : BExpr}, bexprUsesOnly vs e = true → evalMask vs (packAssign st vs) e = e.eval st
  | .const _, _ => rfl
  | .var w, h => lookupMask_packAssign vs st (List.contains_iff_mem.mp h)
  | .not e, h => by
      dsimp only [bexprUsesOnly] at h
      simp [evalMask, BExpr.eval, evalMask_packAssign vs st h]
  | .xor _ _, h => by
      simp only [bexprUsesOnly, Bool.and_eq_true] at h
      simp [evalMask, BExpr.eval, evalMask_packAssign vs st h.1, evalMask_packAssign vs st h.2]
  | .and _ _, h => by
      simp only [bexprUsesOnly, Bool.and_eq_true] at h
      simp [evalMask, BExpr.eval, evalMask_packAssign vs st h.1, evalMask_packAssign vs st h.2]
def bexprEquivOn (vs : List ℕ) (e1 e2 : BExpr) : Bool := bexprUsesOnly vs e1 && bexprUsesOnly
    vs e2 && (List.range (2 ^ vs.length)).all (fun m ↦ evalMask vs m e1 == evalMask vs m e2)
theorem bexprEquivOn_sound {vs : List ℕ} {e1 e2 : BExpr} (h : bexprEquivOn vs e1 e2 = true)
    (st : ℕ → Bool) : e1.eval st = e2.eval st := by
  simp only [bexprEquivOn, Bool.and_eq_true] at h
  rcases h with ⟨⟨hu1, hu2⟩, hall⟩
  have hm : packAssign st vs ∈ List.range (2 ^ vs.length) :=
    List.mem_range.mpr (packAssign_lt vs st)
  have heq : evalMask vs (packAssign st vs) e1 = evalMask vs (packAssign st vs) e2 :=
    beq_iff_eq.mp (List.all_eq_true.mp hall _ hm)
  rw [← evalMask_packAssign vs st hu1, ← evalMask_packAssign vs st hu2, heq]
inductive SymTrie where
  | zero : SymTrie
  | leaf (e : BExpr) : SymTrie
  | node (lo hi : SymTrie) : SymTrie
def symGetAux : ℕ → SymTrie → ℕ → BExpr
  | _, .zero, _ => .const false
  | 0, .leaf e, _ => e
  | 0, .node _ _, _ => .const false
  | _ + 1, .leaf _, _ => .const false
  | d + 1, .node lo hi, idx =>
      if idx % 2 == 0 then symGetAux d lo (idx / 2) else symGetAux d hi (idx / 2)
def symSetAux : ℕ → SymTrie → ℕ → BExpr → SymTrie
  | 0, _, _, e => .leaf e
  | d + 1, .zero, idx, e =>
      if idx % 2 == 0 then .node (symSetAux d .zero (idx / 2) e) .zero
      else .node .zero (symSetAux d .zero (idx / 2) e)
  | d + 1, .leaf _, idx, e =>
      if idx % 2 == 0 then .node (symSetAux d .zero (idx / 2) e) .zero
      else .node .zero (symSetAux d .zero (idx / 2) e)
  | d + 1, .node lo hi, idx, e =>
      if idx % 2 == 0 then .node (symSetAux d lo (idx / 2) e) hi
      else .node lo (symSetAux d hi (idx / 2) e)
theorem symGetAux_setAux :
    ∀ (d : ℕ) (t : SymTrie) (i j : ℕ) (e : BExpr),
      i < 2 ^ d → j < 2 ^ d →
      symGetAux d (symSetAux d t i e) j = (if j = i then e else symGetAux d t j)
  | 0, _, i, j, e, hi, hj => by
      have : i = 0 := by omega
      have : j = 0 := by omega
      subst i; subst j; rfl
  | d + 1, t, i, j, e, hi, hj => by
      have hi2 : i / 2 < 2 ^ d := by rw [Nat.pow_succ] at hi; omega
      have hj2 : j / 2 < 2 ^ d := by rw [Nat.pow_succ] at hj; omega
      have h00 : i % 2 = 0 → j % 2 = 0 → ((j = i) ↔ j / 2 = i / 2) := by omega
      have h01 : i % 2 = 0 → ¬ j % 2 = 0 → j ≠ i := by omega
      have h10 : ¬ i % 2 = 0 → j % 2 = 0 → j ≠ i := by omega
      have h11 : ¬ i % 2 = 0 → ¬ j % 2 = 0 → ((j = i) ↔ j / 2 = i / 2) := by omega
      cases t <;> by_cases hpar : i % 2 = 0 <;> by_cases hjpar : j % 2 = 0 <;>
        simp [symSetAux, symGetAux, hpar, hjpar, h00, h01, h10, h11,
          symGetAux_setAux d _ (i / 2) (j / 2) e hi2 hj2]
def symGet (t : SymTrie) (w : ℕ) : BExpr := symGetAux 9 t w
def symSet (t : SymTrie) (w : ℕ) (e : BExpr) : SymTrie := symSetAux 9 t w e
theorem symGet_set (t : SymTrie) {i j : ℕ} (e : BExpr) (hi : i < 512) (hj : j < 512) : symGet
    (symSet t i e) j = (if j = i then e else symGet t j) := symGetAux_setAux 9 t i j e hi hj
def mkInitSymAux : ℕ → SymTrie
  | 0 => .zero
  | k + 1 => symSet (mkInitSymAux k) k (.var k)
def mkInitSym (cleanFrom : ℕ) : SymTrie := mkInitSymAux cleanFrom
theorem symGet_mkInitSymAux :
    ∀ (k : ℕ) (_ : k ≤ 512) {q : ℕ} (_ : q < 512),
      symGet (mkInitSymAux k) q = (if q < k then .var q else .const false)
  | 0, _, _, _ => by simp [mkInitSymAux, symGet, symGetAux]
  | k + 1, hk, q, hq => by
      rw [mkInitSymAux, symGet_set _ _ (by omega) hq, symGet_mkInitSymAux k (by omega) hq]
      by_cases hqk : q = k
      · subst hqk; simp
      · have hiff : (q < k + 1) ↔ (q < k) := by omega
        simp [hqk, hiff]
theorem symGet_mkInitSym_eval {cleanFrom : ℕ} (hc : cleanFrom ≤ 337)
    (st₀ : ℕ → Bool) (hcl : ∀ q, cleanFrom ≤ q → st₀ q = false) :
    ∀ {q : ℕ}, q < 512 → (symGet (mkInitSym cleanFrom) q).eval st₀ = st₀ q := by
  intro q hq
  rw [mkInitSym, symGet_mkInitSymAux cleanFrom (by omega) hq]
  by_cases hlt : q < cleanFrom
  · simp [hlt, BExpr.eval]
  · simp [hlt, BExpr.eval, hcl q (by omega)]
def stepSymTrie (cur : ℕ) (t : SymTrie) : DecStep → SymTrie
  | .allocZero => t
  | .x w => symSet t w (.not (symGet t w))
  | .cnot src dst => symSet t dst (.xor (symGet t dst) (symGet t src))
  | .andAlloc a b => symSet t cur (.and (symGet t a) (symGet t b))
def runSymTrie : List DecStep → ℕ → SymTrie → SymTrie
  | [], _, t => t
  | s :: rest, cur, t => runSymTrie rest (s.nextCur cur) (stepSymTrie cur t s)
theorem stepSymTrie_sound (st₀ : ℕ → Bool) (cur : ℕ) (hcur : cur ≤ 337) (t : SymTrie)
    (s : DecStep) (hwf : s.wellFormed cur = true) (st : ℕ → Bool)
    (ht : ∀ {q : ℕ}, q < 512 → (symGet t q).eval st₀ = st q) : s.nextCur cur ≤ 337 ∧ ∀
    {q : ℕ}, q < 512 → (symGet (stepSymTrie cur t s) q).eval st₀ = s.stepBool cur st q := by
  cases s with
  | allocZero =>
      simp only [DecStep.wellFormed, decide_eq_true_eq] at hwf
      exact ⟨by simp [DecStep.nextCur]; omega, fun hq ↦ ht hq⟩
  | x w =>
      simp only [DecStep.wellFormed, decide_eq_true_eq] at hwf
      refine ⟨hcur, fun {q} hq ↦ ?_⟩
      rw [stepSymTrie, symGet_set t _ (by omega) hq, DecStep.stepBool]
      by_cases hqw : q = w
      · subst hqw; simp [BExpr.eval, ht hq]
      · simp [hqw, ht hq]
  | cnot src dst =>
      simp only [DecStep.wellFormed, decide_eq_true_eq] at hwf
      refine ⟨hcur, fun {q} hq ↦ ?_⟩
      rw [stepSymTrie, symGet_set t _ (by omega) hq, DecStep.stepBool]
      by_cases hqd : q = dst
      · subst hqd; simp [BExpr.eval, ht hq, ht (q := src) (by omega)]
      · simp [hqd, ht hq]
  | andAlloc a b =>
      simp only [DecStep.wellFormed, decide_eq_true_eq] at hwf
      refine ⟨by simp [DecStep.nextCur]; omega, fun {q} hq ↦ ?_⟩
      rw [stepSymTrie, symGet_set t _ (by omega) hq, DecStep.stepBool]
      by_cases hqc : q = cur
      · subst hqc; simp [BExpr.eval, ht (q := a) (by omega), ht (q := b) (by omega)]
      · simp [hqc, ht hq]
theorem runSymTrie_sound (st₀ : ℕ → Bool) :
    ∀ (p : List DecStep) (cur : ℕ) (_ : cur ≤ 337) (t : SymTrie),
      progWellFormed cur p = true →
      ∀ (st : ℕ → Bool),
        (∀ {q : ℕ}, q < 512 → (symGet t q).eval st₀ = st q) →
        ∀ {q : ℕ}, q < 512 → (symGet (runSymTrie p cur t) q).eval st₀ = evalBool p cur st q
  | [], _, _, t, _, st, ht, _, hq => ht hq
  | s :: rest, cur, hcur, t, hwf, st, ht, q, hq => by
      simp only [progWellFormed, Bool.and_eq_true] at hwf
      obtain ⟨hcur', ht'⟩ := stepSymTrie_sound st₀ cur hcur t s hwf.1 st ht
      exact runSymTrie_sound st₀ rest (s.nextCur cur) hcur' (stepSymTrie cur t s) hwf.2
        (s.stepBool cur st) ht' hq
theorem checkSymWire (p : List DecStep) (cur : ℕ) (hcur : cur ≤ 337)
    (hwf : progWellFormed cur p = true) (vs : List ℕ) (q : ℕ) (hq : q < 512) (target : BExpr)
    (heq : bexprEquivOn vs (symGet (runSymTrie p cur (mkInitSym cur)) q) target = true)
    (st : ℕ → Bool) (hcl : ∀ r, cur ≤ r → st r = false) : evalBool p cur st q = target.eval st
    := by
  have hs := runSymTrie_sound st p cur hcur (mkInitSym cur) hwf st
    (symGet_mkInitSym_eval hcur st hcl) hq
  rw [← hs]
  exact bexprEquivOn_sound heq st
theorem regValList_testBit :
    ∀ (ws : List ℕ) (j : ℕ) (hj : j < ws.length) (st : ℕ → Bool),
      (regValList st ws).testBit j = st (ws[j]'hj)
  | [], _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | w :: ws, 0, _, st => by
      simp only [regValList, List.getElem_cons_zero]
      cases st w <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
  | w :: ws, j + 1, hj, st => by
      simp only [regValList, List.getElem_cons_succ, Nat.testBit_succ]
      have hdiv : ((if st w then 1 else 0) + 2 * regValList st ws) / 2 = regValList st ws := by
        cases st w <;> simp; omega
      rw [hdiv]
      exact regValList_testBit ws j (Nat.lt_of_succ_lt_succ hj) st
theorem clampGe218_u8_eq (st : ℕ → Bool) :
    Bool.not (clampGe218 (st 18) (st 19) (st 20) (st 21) (st 22) (st 23) (st 24)) =
      decide (regValList st u8Wires < 218) := by
  dsimp only [u8Wires, regValList]
  exact clampGe218_spec (st 17) (st 18) (st 19) (st 20) (st 21) (st 22) (st 23) (st 24)
theorem core_lo_4034 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    4034 ≤ fullSysCoreWires mPayload := by
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits]
  omega
def decWireNum (C w : ℕ) : ℕ := if w < 3 then 3948 + w else if w < 40 then 3951 + w else if w
    < 61 then 3971 + w else C + (w - 61)
theorem zmod2_add_one_decide (z : ZMod 2) : decide (z + 1 = 1) = !(decide (z = 1)) := by
  revert z; decide
theorem zmod2_add_decide (z₁ z₂ : ZMod 2) :
    decide (z₁ + z₂ = 1) = Bool.xor (decide (z₁ = 1)) (decide (z₂ = 1)) := by
  revert z₁ z₂; decide
theorem zmod2_mul_decide (z₁ z₂ : ZMod 2) :
    decide (z₁ * z₂ = 1) = (decide (z₁ = 1) && decide (z₂ = 1)) := by
  revert z₁ z₂; decide
theorem zmod2_eq_ite_decide (z : ZMod 2) : z = (if decide (z = 1) then 1 else 0) := by
  revert z; decide
theorem zmod2_val_eq_ite_decide (z : ZMod 2) : z.val = (if decide (z = 1) then 1 else 0) := by
  revert z; decide
theorem zmod2_zero_iff (z : ZMod 2) : (z = 0) ↔ (decide (z = 1) = false) := by
  revert z; decide
theorem zmod2_one_iff (z : ZMod 2) : (z = 1) ↔ (decide (z = 1) = true) := by
  revert z; decide
theorem progEndCur_mono :
    ∀ (p : List DecStep) (cur : ℕ), cur ≤ progEndCur cur p
  | [], _ => le_rfl
  | s :: rest, cur => by
      have h1 : cur ≤ s.nextCur cur := by cases s <;> simp [DecStep.nextCur]
      exact le_trans h1 (progEndCur_mono rest (s.nextCur cur))
theorem bitsVal_eq_regValList_ofFn :
    ∀ (k base : ℕ) (st : ℕ → Bool) (f : Fin k → ZMod 2),
      (∀ i : Fin k, (f i).val = if st (base + i.val) then 1 else 0) →
      Internal.bitsVal f = regValList st (List.ofFn (fun i : Fin k ↦ base + i.val))
  | 0, _, _, _, _ => by simp [Internal.bitsVal, regValList]
  | k + 1, base, st, f, hf => by
      rw [Internal.bitsVal, Fin.sum_univ_succ, List.ofFn_succ, regValList, hf 0]
      simp only [Fin.val_zero, pow_zero, mul_one, Nat.add_zero]
      have htail : (∑ x : Fin k, (f x.succ).val * 2 ^ (x.succ).val) = 2 * Internal.bitsVal
          (fun x : Fin k ↦ f x.succ) := by
        rw [Internal.bitsVal, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [Fin.val_succ, Nat.pow_succ]
        ring
      rw [htail, bitsVal_eq_regValList_ofFn k (base + 1) st (fun x ↦ f x.succ)
        (fun x ↦ by rw [hf x.succ, Fin.val_succ]; ring_nf)]
      congr 3
      apply List.ext_getElem (by simp)
      intro n h1 h2
      simp only [List.getElem_ofFn, Fin.val_succ]
      omega
theorem padZeroBits_lt {kAct mClean : ℕ} (α : BitAssignment kAct) (w : Wire (kAct + mClean))
    (hw : w.val < kAct) : padZeroBits α w = α ⟨w.val, hw⟩ := by
  unfold padZeroBits
  exact Fin.addCases_left ⟨w.val, hw⟩
theorem padZeroBits_ge {kAct mClean : ℕ} (α : BitAssignment kAct) (w : Wire (kAct + mClean))
    (hw : kAct ≤ w.val) : padZeroBits α w = 0 := by
  unfold padZeroBits
  have hw_eq : w = Fin.natAdd kAct ⟨w.val - kAct, by omega⟩ := by
    apply Fin.ext; dsimp; omega
  rw [hw_eq]
  exact Fin.addCases_right _
theorem decWireNum_u8_eq (C : ℕ) (i : Fin 8) : decWireNum C (17 + i.val) = 3968 + i.val := by
  dsimp [decWireNum]; split_ifs <;> omega
theorem decWireNum_u36_eq (C : ℕ) (i : Fin 36) : decWireNum C (3 + i.val) = 3954 + i.val := by
  dsimp [decWireNum]; split_ifs <;> omega
def progCtrl145 : List DecStep := [
  .x 18, .x 19, .andAlloc 18 19, .x 19, .x 18, .x 61, .andAlloc 20 61, .andAlloc 21 62,
  .x 22, .x 63, .andAlloc 22 63, .x 63, .x 22, .x 64, .andAlloc 23 64, .andAlloc 24 65,
  .x 2, .andAlloc 2 66, .x 2,
  .x 1, .x 67, .andAlloc 1 67, .x 67, .x 1
]
def progU8Copy145 : List DecStep := [
  .allocZero, .cnot 17 69,
  .allocZero, .cnot 18 70,
  .allocZero, .cnot 19 71,
  .allocZero, .cnot 20 72,
  .allocZero, .cnot 21 73,
  .allocZero, .cnot 22 74,
  .allocZero, .cnot 23 75,
  .allocZero, .cnot 24 76
]
def mod109PairsAux : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | k, w :: ws => (w, (2 ^ k) % 109) :: mod109PairsAux (k + 1) ws
theorem pairsVal_mod109PairsAux :
    ∀ (ws : List ℕ) (k : ℕ) (st : ℕ → Bool),
      pairsVal st (mod109PairsAux k ws) % 109 = (2 ^ k * regValList st ws) % 109
  | [], _, _ => by simp [mod109PairsAux, pairsVal, regValList]
  | w :: ws, k, st => by
      rw [mod109PairsAux, pairsVal, Nat.add_mod, pairsVal_mod109PairsAux ws (k + 1) st, regValList]
      have hp : 2 ^ k * ((if st w then 1 else 0) + 2 * regValList st ws) =
          (if st w then 2 ^ k else 0) + 2 ^ (k + 1) * regValList st ws := by
        cases st w <;> simp <;> ring
      rw [hp, Nat.add_mod]
      cases st w <;> simp
def certCSA1_76 : List CertStep := [
  .flipMod 21, .flipMod 22, .flipMod 23, .flipMod 24, .flipMod 25, .flipMod 26, .flipMod 27,
    .flipMod 28, .flipMod 29, .flipMod 30, .flipMod 31, .flipMod 32, .flipMod 33, .flipMod 34,
    .flipMod 35, .flipMod 36, .flipMod 37, .flipMod 38, .reduceC0Mod, .haStep 10 28 19 38,
    .faStep 11 29 77 38 76, .faStep 12 30 78 76 43, .faStep 13 31 79 43 86, .liftMod 13 1,
  .copySplit 13 107, .flipMod 81, .flipMod 13, .faStep 14 32 80 86 63,
  .copySplit 14 1, .copySplit 14 8, .flipMod 14, .faStep 15 33 82 63 17,
  .liftMod 15 1, .copySplit 15 108, .flipMod 86, .faStep 16 34 85 17 34,
  .copySplit 16 1, .faStep 17 35 87 34 68, .copySplit 17 2, .faStep 18 36 89 68 27,
  .copySplit 18 4, .faStep 19 37 91 27 54, .liftMod 19 2, .copySplit 19 108, .flipMod 94,
    .copySplit 19 105, .flipMod 95, .faStep 20 38 93 54 108,
  .liftMod 20 2, .copySplit 20 107, .flipMod 97, .copySplit 20 101, .flipMod 98, .flipMod 96,
    .reduceC0Mod, .faStep 3 21 83 1 2, .faStep 3 86 88 1 2, .faStep 3 94 96 1 2,
    .faStep 4 22 81 2 4, .faStep 4 90 97 2 4, .faStep 4 99 100 2 4, .faStep 5 23 92 4 8,
    .faStep 5 95 102 4 8, .faStep 5 103 104 4 8, .faStep 6 24 84 8 16, .faStep 6 98 105 8 16,
    .faStep 6 106 107 8 16, .faStep 7 25 16 16 32, .faStep 7 108 109 16 32, .faStep 8 26 14 32 64,
    .faStep 8 17 19 32 64, .faStep 8 111 112 32 64, .faStep 9 27 13 64 19, .faStep 9 15 18 64 19,
    .faStep 10 116 117 19 38, .faStep 9 20 113 64 19, .faStep 9 114 115 64 19,
    .faStep 10 119 120 19 38, .faStep 11 118 121 38 76, .copySplit 10 1,
  .copySplit 10 2, .faStep 4 101 124 2 4, .faStep 7 110 10 16 32, .liftMod 11 1,
  .copySplit 11 107, .flipMod 127, .copySplit 11 8, .faStep 8 126 11 32 64,
  .liftMod 122 1, .copySplit 122 108, .flipMod 130, .flipMod 122, .faStep 3 123 130 1 2,
    .faStep 4 127 131 2 4, .faStep 5 125 132 4 8, .faStep 6 128 133 8 16,
  .liftMod 12 1, .copySplit 12 108, .flipMod 135, .flipMod 12, .faStep 8 122 12 32 64,
    .faStep 9 129 136 64 19, .liftMod 137 1, .copySplit 137 108, .flipMod 138, .copySplit 137 4,
    .faStep 3 135 138 1 2, .faStep 7 134 137 16 32,
  .reduceC0Mod, .incFullStep 5 139 4 8, .incFullStep 8 141 32 64
]
def progCSA1_76 : List DecStep := progOfCert 77 certCSA1_76
def s1MidPairs76 : List (ℕ × ℕ) := [
  (3,1),(4,2),(5,4),(6,8),(7,16),(8,32),
  (9,64),(140,2),(142,8),(143,64)
]
def certCPA19_76 : List CertStep := [
  .incHalfStep 3 1 2, .faStep 4 140 144 2 4, .incHalfStep 4 2 4, .faStep 5 145 146 4 8,
    .faStep 6 142 147 8 16, .incFullStep 7 148 16 32, .haStep 8 149 32 64, .faStep 9 143 150 64 128
]
def progCPA19_76 : List DecStep := progOfCert 144 certCPA19_76
def r7Wires76 : List ℕ := [3,4,5,6,7,8,9]
def t8Wires76 : List ℕ := [3,4,5,6,7,8,9,151]
def q8SrcWires76 : List ℕ := [39,3,4,5,6,7,8,9]
def progFlip76 : List DecStep := [.x 151]
def sub109BInitPairs76 : List (ℕ × ℕ) := [
  (3,1),(4,2),(5,4),(6,8),(7,16),(8,32),
  (9,64),(151,109)
]
def certSub109B_76 : List CertStep := [
  .copySplit 151 1, .copySplit 151 4, .copySplit 151 8, .copySplit 151 32, .haStep 3 152 1 2,
    .haStep 4 156 2 4, .faStep 5 157 153 4 8, .faStep 6 158 154 8 16, .haStep 7 159 16 32,
    .faStep 8 160 155 32 64, .cnotMod2Step 151 9 64, .cnotMod2Step 161 9 64
]
def progSub109B_76 : List DecStep := progOfCert 152 certSub109B_76
def idxOutLocal145 : List ℕ := [69,70,71,72,73,74,75,76]
def enLocal145 : ℕ := 271
def progOutMux76 : List DecStep := [
  .allocZero, .cnot 39 162, .cnot 69 162, .andAlloc 2 162, .cnot 163 69, .cnot 70 3, .andAlloc 2 3,
    .cnot 164 70, .cnot 71 4, .andAlloc 2 4, .cnot 165 71, .cnot 72 5, .andAlloc 2 5, .cnot 166 72,
    .cnot 73 6, .andAlloc 2 6, .cnot 167 73, .cnot 74 7, .andAlloc 2 7, .cnot 168 74, .cnot 75 8,
    .andAlloc 2 8, .cnot 169 75, .cnot 76 9, .andAlloc 2 9, .cnot 170 76
]
def progEnCopy76 : List DecStep := List.replicate 101 .allocZero ++ [.cnot 68 271]
def tail6_76 : List DecStep := progEnCopy76
def tail5_76 : List DecStep := progOutMux76 ++ tail6_76
def tail4_76 : List DecStep := progSub109B_76 ++ tail5_76
def tail3_76 : List DecStep := progFlip76 ++ tail4_76
def tail2_76 : List DecStep := progCPA19_76 ++ tail3_76
def tail1_76 : List DecStep := progCSA1_76 ++ tail2_76
def tail0_76 : List DecStep := progU8Copy145 ++ tail1_76
def progAll145 : List DecStep := progCtrl145 ++ tail0_76
theorem progCtrl145_wf : progWellFormed 61 progCtrl145 = true := by decide
theorem progCtrl145_end : progEndCur 61 progCtrl145 = 69 := by decide
theorem progU8Copy145_wf : progWellFormed 69 progU8Copy145 = true := by decide
theorem progU8Copy145_end : progEndCur 69 progU8Copy145 = 77 := by decide
theorem progCSA1_76_end : progEndCur 77 progCSA1_76 = 144 := by decide
theorem progCPA19_76_end : progEndCur 144 progCPA19_76 = 152 := by decide
theorem progFlip76_end : progEndCur 152 progFlip76 = 152 := by decide
theorem progSub109B_76_end : progEndCur 152 progSub109B_76 = 162 := by decide
theorem progOutMux76_wf : progWellFormed 162 progOutMux76 = true := by decide
theorem progOutMux76_end : progEndCur 162 progOutMux76 = 171 := by decide
theorem progEnCopy76_wf : progWellFormed 171 progEnCopy76 = true := by decide
theorem progAll145_stats :
    progWellFormed 61 progAll145 = true ∧
    progEndCur 61 progAll145 = 272 ∧
    progNumAnd progAll145 = 76 := by decide
theorem progAll145_wellFormed : progWellFormed 61 progAll145 = true := progAll145_stats.1
theorem progAll145_endCur : progEndCur 61 progAll145 = 272 := progAll145_stats.2.1
theorem progAll145_numAnd : progNumAnd progAll145 = 76 := progAll145_stats.2.2
theorem certCSA1_76_ok :
    checkCert 109 77 (mkPairsWt (mod109PairsAux 0 u36Wires)) 0
      (mkPairsWt s1MidPairs76) 0 certCSA1_76 = true := by decide +kernel
theorem certCPA19_76_ok :
    checkCert 0 144 (mkPairsWt s1MidPairs76) 19
      (mkPairsWt (regPairs t8Wires76)) 0 certCPA19_76 = true := by decide
theorem certSub109B_76_ok :
    checkCert 128 152 (mkPairsWt sub109BInitPairs76) 0
      (mkPairsWt (regPairs r7Wires76)) 0 certSub109B_76 = true := by decide
theorem s1MidPairs76_sum_eq : sumPairs s1MidPairs76 = 201 := by decide
theorem u36ModPairs76_lt337 : ∀ p ∈ mod109PairsAux 0 u36Wires, p.1 < 337 := by decide
theorem s1MidPairs76_lt337 : ∀ p ∈ s1MidPairs76, p.1 < 337 := by decide
theorem t8Wires76_lt337 : ∀ p ∈ regPairs t8Wires76, p.1 < 337 := by decide
theorem sub109BInitPairs76_lt : ∀ p ∈ sub109BInitPairs76, p.1 < 337 := by decide
theorem r7Wires76_lt337 : ∀ p ∈ regPairs r7Wires76, p.1 < 337 := by decide
def clampGe218BExpr (w1 w2 w3 w4 w5 w6 w7 : ℕ) : BExpr := .and (.var w7) (.and (.var w6) (.not
    (.and (.not (.var w5)) (.not (.and (.var w4) (.and (.var w3) (.not (.and (.not (.var w1))
    (.not (.var w2))))))))))
theorem clampGe218BExpr_eval (st : ℕ → Bool) (w1 w2 w3 w4 w5 w6 w7 : ℕ) :
    (clampGe218BExpr w1 w2 w3 w4 w5 w6 w7).eval st =
      clampGe218 (st w1) (st w2) (st w3) (st w4) (st w5) (st w6) (st w7) := by
  dsimp only [clampGe218BExpr, BExpr.eval, clampGe218]
  cases st w1 <;> cases st w2 <;> cases st w3 <;> cases st w4 <;>
    cases st w5 <;> cases st w6 <;> cases st w7 <;> rfl
theorem ctrl145Sym_ok : (bexprEquivOn [1,2,18,19,20,21,22,23,24] (symGet (runSymTrie
    progCtrl145 61 (mkInitSym 61)) 68) (.and (.not (.var 1)) (.not (.and (.not (.var 2))
    (clampGe218BExpr 18 19 20 21 22 23 24)))) && (List.range 61).all (fun q ↦ bexprEquivOn [q]
    (symGet (runSymTrie progCtrl145 61 (mkInitSym 61)) q) (.var q))) = true := by
  decide
theorem u8Copy145Sym_ok : ((List.range 8).all (fun j ↦ bexprEquivOn [17 + j] (symGet
    (runSymTrie progU8Copy145 69 (mkInitSym 69)) (69 + j)) (.var (17 + j))) && (List.range
    69).all (fun q ↦ bexprEquivOn [q] (symGet (runSymTrie progU8Copy145 69 (mkInitSym 69)) q)
    (.var q))) = true := by
  decide
def muxSrcWire76 (j : ℕ) : ℕ := if j = 0 then 39 else 2 + j
theorem outMux76Sym_ok : (List.range 8).all (fun j ↦ bexprEquivOn [2,69 + j, muxSrcWire76 j]
    (symGet (runSymTrie progOutMux76 162 (mkInitSym 162)) (69 + j)) (.xor (.var (69 + j))
    (.and (.var 2) (.xor (.var (69 + j)) (.var (muxSrcWire76 j)))))) = true := by
  decide
theorem enCopy76Sym_ok : (bexprEquivOn [68] (symGet (runSymTrie progEnCopy76 171 (mkInitSym
    171)) 271) (.var 68) && (List.range 8).all (fun j ↦ bexprEquivOn [69 + j] (symGet
    (runSymTrie progEnCopy76 171 (mkInitSym 171)) (69 + j)) (.var (69 + j)))) = true := by
  decide
def savedWires76 : List ℕ := [2,39,68,69,70,71,72,73,74,75,76]
theorem untouched_csa1_saved76 : progUntouchedAll savedWires76 77 progCSA1_76 = true := by decide
theorem untouched_cpa19_saved76 : progUntouchedAll savedWires76 144 progCPA19_76 = true := by decide
theorem untouched_flip_saved76 : progUntouchedAll savedWires76 152 progFlip76 = true := by decide
theorem untouched_sub109B_saved76 : progUntouchedAll savedWires76 152 progSub109B_76 = true := by
  decide
theorem untouched_outMux76_68 : progUntouched 68 162 progOutMux76 = true := by decide
theorem sub109_oneStage_fin202 (u : Fin 202) :
    (((19 + u.val) % 128) + 109 * (1 - (19 + u.val) / 128)) % 128 = u.val % 109 := by
  have := u.isLt
  by_cases h : u.val < 109 <;> omega
theorem t8Wires76_split (st : ℕ → Bool) :
    regValList st t8Wires76 = regValList st r7Wires76 + 128 * (if st 151 then 1 else 0) := by
  have heq : t8Wires76 = r7Wires76 ++ [151] := rfl
  rw [heq, regValList_append]
  have hlen : r7Wires76.length = 7 := rfl
  rw [hlen]
  simp [regValList]
theorem sub109BInitPairs76_val (st : ℕ → Bool) : pairsVal st sub109BInitPairs76 = regValList
    st r7Wires76 + 109 * (if st 151 then 1 else 0) := by
  have hMul (b : Bool) (c : ℕ) : (if b then c else 0) = c * (if b then 1 else 0) := by
    cases b <;> simp
  dsimp only [sub109BInitPairs76, r7Wires76, pairsVal, regValList]
  rw [hMul (st 4) 2, hMul (st 5) 4, hMul (st 6) 8, hMul (st 7) 16, hMul (st 8) 32,
    hMul (st 9) 64, hMul (st 151) 109]
  omega
def coinBarrelIdxFastPure (st : ℕ → Bool) : ℕ :=
  if st 1 then 0
  else if !st 2 then
    let u8 := regValList st u8Wires
    if u8 < 218 then u8 else 0
  else
    2 * ((regValList st u36Wires) % 109) + (if st 39 then 1 else 0)
theorem evalBool_stage145_to_st2 (st₀ st₁ st₂ : ℕ → Bool)
    (hcl₀ : ∀ q, 61 ≤ q → st₀ q = false)
    (hst₁ : evalBool progCtrl145 61 st₀ = st₁)
    (hst₂ : evalBool progU8Copy145 69 st₁ = st₂) :
    (∀ q, 77 ≤ q → st₂ q = false) ∧
    (∀ q < 61, st₁ q = st₀ q) ∧
    (∀ q < 69, st₂ q = st₁ q) ∧
    st₁ 68 = (!st₀ 1 && (st₀ 2 || decide (regValList st₀ u8Wires < 218))) ∧
    (∀ j < 8, st₂ (69 + j) = st₀ (17 + j)) := by
  have hcl₁ : ∀ q, 69 ≤ q → st₁ q = false :=
    fun q hq ↦
      by
      rw [← hst₁]; exact evalBool_clean _ 61 st₀ progCtrl145_wf hcl₀ q (by
        rw [progCtrl145_end];
        exact hq)
  have hcl₂ : ∀ q, 77 ≤ q → st₂ q = false :=
    fun q hq ↦
      by
      rw [← hst₂]; exact evalBool_clean _ 69 st₁ progU8Copy145_wf hcl₁ q (by
        rw [progU8Copy145_end];
        exact hq)
  have hctrl := ctrl145Sym_ok
  simp only [Bool.and_eq_true] at hctrl
  have hst₁_low : ∀ q < 61, st₁ q = st₀ q := fun q hq ↦ by
    rw [← hst₁]
    exact checkSymWire progCtrl145 61 (by omega) progCtrl145_wf [q] q (by omega) (.var q)
      (List.all_eq_true.mp hctrl.2 q (List.mem_range.mpr hq)) st₀ hcl₀
  have hst₁_68 : st₁ 68 = (!st₀ 1 && (st₀ 2 || decide (regValList st₀ u8Wires < 218))) := by
    have hraw := checkSymWire progCtrl145 61 (by omega) progCtrl145_wf
      [1,2,18,19,20,21,22,23,24] 68 (by omega) _ hctrl.1 st₀ hcl₀
    rw [hst₁] at hraw
    rw [hraw]
    dsimp only [BExpr.eval]
    rw [clampGe218BExpr_eval]
    have hnot := clampGe218_u8_eq st₀
    cases st₀ 1 <;> cases st₀ 2 <;>
      cases hcg : clampGe218 (st₀ 18) (st₀ 19) (st₀ 20) (st₀ 21) (st₀ 22) (st₀ 23) (st₀ 24) <;>
      (rw [hcg] at hnot; simp [← hnot])
  have hu8cp := u8Copy145Sym_ok
  simp only [Bool.and_eq_true] at hu8cp
  have hst₂_low : ∀ q < 69, st₂ q = st₁ q := fun q hq ↦ by
    rw [← hst₂]
    exact checkSymWire progU8Copy145 69 (by omega) progU8Copy145_wf [q] q (by omega) (.var q)
      (List.all_eq_true.mp hu8cp.2 q (List.mem_range.mpr hq)) st₁ hcl₁
  have hst₂_u8copy : ∀ j < 8, st₂ (69 + j) = st₀ (17 + j) := fun j hj ↦ by
    have hraw := checkSymWire progU8Copy145 69 (by omega) progU8Copy145_wf
      [17 + j] (69 + j) (by omega) (.var (17 + j))
      (List.all_eq_true.mp hu8cp.1 j (List.mem_range.mpr hj)) st₁ hcl₁
    rw [hst₂] at hraw
    exact hraw.trans (hst₁_low (17 + j) (by omega))
  exact ⟨hcl₂, hst₁_low, hst₂_low, hst₁_68, hst₂_u8copy⟩
theorem evalBool_stage76_st2_to_st6 (st₀ st₁ st₂ st₃ st₄ st₅ st₆ : ℕ → Bool)
    (hcl₂ : ∀ q, 77 ≤ q → st₂ q = false) (hst₁_low : ∀ q < 61, st₁ q = st₀ q)
    (hst₂_low : ∀ q < 69, st₂ q = st₁ q) (hst₂_u8copy : ∀ j < 8, st₂ (69 + j) = st₀ (17 + j))
    (hst₃ : evalBool progCSA1_76 77 st₂ = st₃) (hst₄ : evalBool progCPA19_76 144 st₃ = st₄)
    (hst₅ : evalBool progFlip76 152 st₄ = st₅) (hst₆ : evalBool progSub109B_76 152 st₅ = st₆)
    : (∀ q, 162 ≤ q → st₆ q = false) ∧ regValList st₆ q8SrcWires76 = 2 *
    ((regValList st₀ u36Wires) % 109) + (if st₀ 39 then 1 else 0) ∧ st₆ 2 = st₀ 2 ∧ st₆ 68 =
    st₁ 68 ∧ (∀ j < 8, st₆ (69 + j) = st₀ (17 + j)) := by
  obtain ⟨hcl₃_raw, hcsa1⟩ := (checkCert_sound 109 certCSA1_76 77 (mkPairsWt (mod109PairsAux 0
      u36Wires)) (mkPairsWt s1MidPairs76) 0 0 certCSA1_76_ok).2 st₂ hcl₂
  rw [show progOfCert 77 certCSA1_76 = progCSA1_76 from rfl, hst₃] at hcl₃_raw hcsa1
  have hcl₃ : ∀ q, 144 ≤ q → st₃ q = false :=
    fun q hq ↦ hcl₃_raw q (by rw [progCSA1_76_end]; exact hq)
  obtain ⟨hcl₄_raw, hcpa19⟩ := (checkCert_sound 0 certCPA19_76 144 (mkPairsWt s1MidPairs76)
      (mkPairsWt (regPairs t8Wires76)) 19 0 certCPA19_76_ok).2 st₃ hcl₃
  rw [show progOfCert 144 certCPA19_76 = progCPA19_76 from rfl, hst₄] at hcl₄_raw hcpa19
  have hcl₄ : ∀ q, 152 ≤ q → st₄ q = false :=
    fun q hq ↦ hcl₄_raw q (by rw [progCPA19_76_end]; exact hq)
  have hcl₅ : ∀ q, 152 ≤ q → st₅ q = false := fun q hq ↦ by
    rw [← hst₅]
    have hne : q ≠ 151 := by omega
    simp [progFlip76, evalBool, DecStep.stepBool, hne, hcl₄ q hq]
  obtain ⟨hcl₆_raw, hsubB⟩ := (checkCert_sound 128 certSub109B_76 152 (mkPairsWt
      sub109BInitPairs76) (mkPairsWt (regPairs r7Wires76)) 0 0 certSub109B_76_ok).2 st₅ hcl₅
  rw [show progOfCert 152 certSub109B_76 = progSub109B_76 from rfl, hst₆] at hcl₆_raw hsubB
  have hcl₆ : ∀ q, 162 ≤ q → st₆ q = false :=
    fun q hq ↦ hcl₆_raw q (by rw [progSub109B_76_end]; exact hq)
  have h109_ne : (109 == 0) = false := rfl
  have h128_ne : (128 == 0) = false := rfl
  simp only [evalMod, h109_ne, Bool.false_eq_true, ↓reduceIte] at hcsa1
  simp only [evalMod, BEq.rfl, ↓reduceIte] at hcpa19
  simp only [evalMod, h128_ne, Bool.false_eq_true, ↓reduceIte] at hsubB
  rw [zero_add, zero_add, linSum_mkPairsWt _ st₃ s1MidPairs76_lt337,
    linSum_mkPairsWt _ st₂ u36ModPairs76_lt337, pairsVal_mod109PairsAux, pow_zero, one_mul] at hcsa1
  rw [zero_add, linSum_regWt t8Wires76 st₄ t8Wires76_lt337,
    linSum_mkPairsWt _ st₃ s1MidPairs76_lt337] at hcpa19
  rw [zero_add, zero_add, linSum_regWt r7Wires76 st₆ r7Wires76_lt337,
    linSum_mkPairsWt _ st₅ sub109BInitPairs76_lt] at hsubB
  have hst₂_u36 : regValList st₂ u36Wires = regValList st₀ u36Wires :=
    regValList_congr fun w hw ↦ by
      have hlt : w < 61 := by simp [u36Wires] at hw; omega
      exact (hst₂_low w (by omega)).trans (hst₁_low w hlt)
  have hs_le : pairsVal st₃ s1MidPairs76 ≤ 201 := by
    rw [← s1MidPairs76_sum_eq]; exact pairsVal_le_sumPairs _ st₃
  have hr7_lt : regValList st₄ r7Wires76 < 128 := by
    have := regValList_lt r7Wires76 st₄; simpa [r7Wires76] using this
  have hr7_st6_lt : regValList st₆ r7Wires76 < 128 := by
    have := regValList_lt r7Wires76 st₆; simpa [r7Wires76] using this
  have hflip_151 : st₅ 151 = !st₄ 151 := by
    rw [← hst₅]; simp [progFlip76, evalBool, DecStep.stepBool]
  have hflip_r7 : regValList st₅ r7Wires76 = regValList st₄ r7Wires76 :=
    regValList_congr fun w hw ↦ by
      rw [← hst₅]
      have hne : w ≠ 151 := by simp [r7Wires76] at hw; omega
      simp [progFlip76, evalBool, DecStep.stepBool, hne]
  have ht8_eq := t8Wires76_split st₄
  rw [hcpa19] at ht8_eq
  have hr7_mod : regValList st₄ r7Wires76 = (19 + pairsVal st₃ s1MidPairs76) % 128 := by omega
  have hbit_div : (if !st₄ 151 then 1 else 0) = 1 - (19 + pairsVal st₃ s1MidPairs76) / 128 := by
    cases hb : st₄ 151 <;> simp [hb] at ht8_eq ⊢ <;> omega
  have hr7_final : regValList st₆ r7Wires76 = regValList st₀ u36Wires % 109 := by
    have h1 : regValList st₆ r7Wires76 = regValList st₆ r7Wires76 % 128 :=
      (Nat.mod_eq_of_lt hr7_st6_lt).symm
    rw [h1, hsubB, sub109BInitPairs76_val, hflip_r7, hflip_151, hr7_mod, hbit_div]
    have hfin := sub109_oneStage_fin202 ⟨pairsVal st₃ s1MidPairs76, by omega⟩
    dsimp only at hfin
    rw [hfin, hcsa1, hst₂_u36]
  have hs3 := evalBool_untouched_all progCSA1_76 savedWires76 77 st₂ untouched_csa1_saved76
  have hs4 := evalBool_untouched_all progCPA19_76 savedWires76 144 st₃ untouched_cpa19_saved76
  have hs5 := evalBool_untouched_all progFlip76 savedWires76 152 st₄ untouched_flip_saved76
  have hs6 := evalBool_untouched_all progSub109B_76 savedWires76 152 st₅ untouched_sub109B_saved76
  rw [hst₃] at hs3; rw [hst₄] at hs4; rw [hst₅] at hs5; rw [hst₆] at hs6
  have hpres_saved : ∀ w ∈ savedWires76, st₆ w = st₂ w := fun w hw ↦
    (hs6 w hw).trans ((hs5 w hw).trans ((hs4 w hw).trans (hs3 w hw)))
  have hst₆_2 : st₆ 2 = st₀ 2 :=
    (hpres_saved 2 (by decide)).trans ((hst₂_low 2 (by omega)).trans (hst₁_low 2 (by omega)))
  have hst₆_39 : st₆ 39 = st₀ 39 :=
    (hpres_saved 39 (by decide)).trans ((hst₂_low 39 (by omega)).trans (hst₁_low 39 (by omega)))
  have hst₆_68 : st₆ 68 = st₁ 68 :=
    (hpres_saved 68 (by decide)).trans (hst₂_low 68 (by omega))
  have hst₆_u8 : ∀ j < 8, st₆ (69 + j) = st₀ (17 + j) := fun j hj ↦ by
    have hmem : 69 + j ∈ savedWires76 := by simp [savedWires76]; omega
    exact (hpres_saved (69 + j) hmem).trans (hst₂_u8copy j hj)
  have hq8_val : regValList st₆ q8SrcWires76 =
      2 * ((regValList st₀ u36Wires) % 109) + (if st₀ 39 then 1 else 0) := by
    have hcons : q8SrcWires76 = 39 :: r7Wires76 := rfl
    rw [hcons, regValList, hst₆_39, hr7_final]
    omega
  exact ⟨hcl₆, hq8_val, hst₆_2, hst₆_68, hst₆_u8⟩
theorem evalBool_progAll76_chain (st₀ st₁ st₂ st₃ st₄ st₅ st₆ st₇ st₈ : ℕ → Bool)
    (hst₁ : evalBool progCtrl145 61 st₀ = st₁) (hst₂ : evalBool progU8Copy145 69 st₁ = st₂)
    (hst₃ : evalBool progCSA1_76 77 st₂ = st₃) (hst₄ : evalBool progCPA19_76 144 st₃ = st₄)
    (hst₅ : evalBool progFlip76 152 st₄ = st₅) (hst₆ : evalBool progSub109B_76 152 st₅ = st₆)
    (hst₇ : evalBool progOutMux76 162 st₆ = st₇) (hst₈ : evalBool progEnCopy76 171 st₇ = st₈)
    : evalBool progAll145 61 st₀ = st₈ := by
  rw [progAll145, evalBool_append, progCtrl145_end, hst₁]
  rw [tail0_76, evalBool_append, progU8Copy145_end, hst₂]
  rw [tail1_76, evalBool_append, progCSA1_76_end, hst₃]
  rw [tail2_76, evalBool_append, progCPA19_76_end, hst₄]
  rw [tail3_76, evalBool_append, progFlip76_end, hst₅]
  rw [tail4_76, evalBool_append, progSub109B_76_end, hst₆]
  rw [tail5_76, evalBool_append, progOutMux76_end, hst₇, tail6_76, hst₈]
theorem evalBool_progOutMux76_bit (st₆ st₇ : ℕ → Bool)
    (hcl₆_raw : ∀ q, 162 ≤ q → st₆ q = false) (hst₇ : evalBool progOutMux76 162 st₆ = st₇)
    (j : Fin 8) : st₇ (69 + j.val) = Bool.xor (st₆ (69 + j.val))
    (st₆ 2 && Bool.xor (st₆ (69 + j.val)) (st₆ (muxSrcWire76 j.val))) := by
  have hj_lt : j.val < 8 := j.isLt
  have hsrc_lt : muxSrcWire76 j.val < 162 := by dsimp [muxSrcWire76]; split_ifs <;> omega
  rw [← hst₇]
  exact checkSymWire progOutMux76 162 (by omega) progOutMux76_wf
    [2,69 + j.val, muxSrcWire76 j.val] (69 + j.val) (by omega) (.xor (.var (69 + j.val)) (.and
    (.var 2) (.xor (.var (69 + j.val)) (.var (muxSrcWire76 j.val))))) (List.all_eq_true.mp
    outMux76Sym_ok j.val (List.mem_range.mpr hj_lt)) st₆ hcl₆_raw
theorem evalBool_progEnCopy76_spec (st₇ st₈ : ℕ → Bool) (hcl₇ : ∀ q, 171 ≤ q → st₇ q = false)
    (hst₈ : evalBool progEnCopy76 171 st₇ = st₈) : st₈ enLocal145 = st₇ 68 ∧ ∀ j : Fin 8, st₈
    (69 + j.val) = st₇ (69 + j.val) := by
  have hencp := enCopy76Sym_ok
  simp only [Bool.and_eq_true] at hencp
  refine ⟨?_, fun j ↦ ?_⟩
  · rw [← hst₈]
    exact checkSymWire progEnCopy76 171 (by omega) progEnCopy76_wf
      [68] 271 (by omega) (.var 68) hencp.1 st₇ hcl₇
  · have hj_lt : j.val < 8 := j.isLt
    rw [← hst₈]
    exact checkSymWire progEnCopy76 171 (by omega) progEnCopy76_wf
      [69 + j.val] (69 + j.val) (by omega) (.var (69 + j.val))
      (List.all_eq_true.mp hencp.2 j.val (List.mem_range.mpr hj_lt)) st₇ hcl₇
theorem idxOutLocal145_get_eq (j : Fin 8) :
    idxOutLocal145[j.val]'(by simp [idxOutLocal145]) = 69 + j.val := by
  fin_cases j <;> rfl
theorem u8Wires145_get_eq (j : Fin 8) :
    u8Wires[j.val]'(by simp [u8Wires]) = 17 + j.val := by
  fin_cases j <;> rfl
theorem q8SrcWires76_get_eq (j : Fin 8) :
    q8SrcWires76[j.val]'(by simp [q8SrcWires76]) = muxSrcWire76 j.val := by
  fin_cases j <;> rfl
theorem coinBarrelIdxFastPure_of_en_false (st₀ : ℕ → Bool)
    (hen0 : (!st₀ 1 && (st₀ 2 || decide (regValList st₀ u8Wires < 218))) = false) :
    coinBarrelIdxFastPure st₀ = 0 := by
  dsimp only [coinBarrelIdxFastPure]
  cases h1 : st₀ 1 <;> cases h2 : st₀ 2 <;>
    by_cases hlt : regValList st₀ u8Wires < 218 <;>
    simp [h1, h2, hlt] at hen0 ⊢
theorem coinBarrelIdxFastPure_mux_bit (st₀ : ℕ → Bool) (j : Fin 8)
    (hen1 : (!st₀ 1 && (st₀ 2 || decide (regValList st₀ u8Wires < 218))) = true) :
    Bool.xor ((regValList st₀ u8Wires).testBit j.val)
      (st₀ 2 && Bool.xor ((regValList st₀ u8Wires).testBit j.val)
        ((2 * ((regValList st₀ u36Wires) % 109) + (if st₀ 39 then 1 else 0)).testBit j.val)) =
      (coinBarrelIdxFastPure st₀).testBit j.val := by
  dsimp only [coinBarrelIdxFastPure]
  cases h1 : st₀ 1 <;> cases h2 : st₀ 2
  · by_cases hlt : regValList st₀ u8Wires < 218
    · simp [hlt]
    · simp [h1, h2, hlt] at hen1
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.true_and]
    cases (regValList st₀ u8Wires).testBit j.val <;>
      cases (2 * (regValList st₀ u36Wires % 109) + if st₀ 39 = true then 1 else 0).testBit j.val <;>
      rfl
  · simp [h1] at hen1
  · simp [h1] at hen1
theorem evalBool_progAll145_spec (st₀ : ℕ → Bool) (hcl₀ : ∀ q, 61 ≤ q → st₀ q = false) :
    evalBool progAll145 61 st₀ enLocal145 =
      (!st₀ 1 && (st₀ 2 || decide (regValList st₀ u8Wires < 218))) ∧
    (evalBool progAll145 61 st₀ enLocal145 = false → coinBarrelIdxFastPure st₀ = 0) ∧
    (evalBool progAll145 61 st₀ enLocal145 = true →
      ∀ j : Fin 8,
        evalBool progAll145 61 st₀ (idxOutLocal145[j.val]'(by simp [idxOutLocal145])) =
          (coinBarrelIdxFastPure st₀).testBit j.val) := by
  generalize hst₁ : evalBool progCtrl145 61 st₀ = st₁
  generalize hst₂ : evalBool progU8Copy145 69 st₁ = st₂
  generalize hst₃ : evalBool progCSA1_76 77 st₂ = st₃
  generalize hst₄ : evalBool progCPA19_76 144 st₃ = st₄
  generalize hst₅ : evalBool progFlip76 152 st₄ = st₅
  generalize hst₆ : evalBool progSub109B_76 152 st₅ = st₆
  generalize hst₇ : evalBool progOutMux76 162 st₆ = st₇
  generalize hst₈ : evalBool progEnCopy76 171 st₇ = st₈
  have hchain := evalBool_progAll76_chain st₀ st₁ st₂ st₃ st₄ st₅ st₆ st₇ st₈
    hst₁ hst₂ hst₃ hst₄ hst₅ hst₆ hst₇ hst₈
  rw [hchain]
  obtain ⟨hcl₂, hst₁_low, hst₂_low, hst₁_68, hst₂_u8copy⟩ :=
    evalBool_stage145_to_st2 st₀ st₁ st₂ hcl₀ hst₁ hst₂
  obtain ⟨hcl₆_raw, hq8_val, hst₆_2, hst₆_68, hst₆_u8⟩ := evalBool_stage76_st2_to_st6 st₀ st₁
      st₂ st₃ st₄ st₅ st₆ hcl₂ hst₁_low hst₂_low hst₂_u8copy hst₃ hst₄ hst₅ hst₆
  have hcl₇ : ∀ q, 171 ≤ q → st₇ q = false :=
    fun q hq ↦
      by
      rw [← hst₇]; exact evalBool_clean _ 162 st₆ progOutMux76_wf hcl₆_raw q (by
        rw
          [progOutMux76_end];
        exact hq)
  have hst₇_68 : st₇ 68 = st₁ 68 := by
    have hp := evalBool_untouched progOutMux76 162 st₆ 68 untouched_outMux76_68
    rw [hst₇] at hp
    exact hp.trans hst₆_68
  obtain ⟨hen_eq, hidx_cp⟩ := evalBool_progEnCopy76_spec st₇ st₈ hcl₇ hst₈
  have hst₈_271 : st₈ enLocal145 = (!st₀ 1 && (st₀ 2 || decide (regValList st₀ u8Wires < 218))) :=
    hen_eq.trans (hst₇_68.trans hst₁_68)
  refine ⟨hst₈_271, fun hen0 ↦ coinBarrelIdxFastPure_of_en_false st₀ (hst₈_271 ▸ hen0), fun hen1 j ↦
    ?_⟩
  rw [idxOutLocal145_get_eq j, hidx_cp j, evalBool_progOutMux76_bit st₆ st₇ hcl₆_raw hst₇ j,
    hst₆_2, hst₆_u8 j.val j.isLt]
  have hu8_bit : st₀ (17 + j.val) = (regValList st₀ u8Wires).testBit j.val := by
    rw [regValList_testBit u8Wires j.val (by simp [u8Wires]) st₀, u8Wires145_get_eq j]
  have hq8_bit : st₆ (muxSrcWire76 j.val) = (regValList st₆ q8SrcWires76).testBit j.val := by
    rw [regValList_testBit q8SrcWires76 j.val (by simp [q8SrcWires76]) st₆, q8SrcWires76_get_eq j]
  rw [hu8_bit, hq8_bit, hq8_val]
  exact coinBarrelIdxFastPure_mux_bit st₀ j (hst₈_271 ▸ hen1)
end FastCoinBarrelDecoder279
end ConfigFastCoinBarrelDecoder279
end
end ModFastCoinBarrelDecoder279

end QuantumComputation.Specs.StoppingPowerSolution
