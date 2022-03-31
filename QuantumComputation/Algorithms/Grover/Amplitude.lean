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

public import QuantumComputation.Algorithms.Grover.Operators
public import QuantumComputation.Primitives.Hadamard
public import QuantumComputation.Primitives.Measure
import Mathlib.NumberTheory.Niven

/-!
# Grover amplitude analysis

This module proves the closed-form success probability for repeated Grover iterations.
-/

@[expose] public section

open Operator
open scoped Matrix ComplexOrder MatrixOrder Real

namespace Grover

variable {n : ℕ}
local notation "d" => 2 ^ n

/-- The Hadamard transform is not the oracle, for every number of qubits and every target. -/
theorem hadamardMatrix_ne_oracleMatrix (target : Fin d) :
    hadamardMatrix n ≠ oracleMatrix target := by
  intro heq
  cases n with
  | zero =>
      obtain rfl : target = 0 := Fin.ext (by omega)
      have h := congr($heq 0 0)
      norm_num [hadamardMatrix_zero_apply, oracleMatrix] at h
  | succ n =>
      have h := congr($heq 0 1)
      norm_num [hadamardMatrix_zero_apply, oracleMatrix] at h

theorem hadamardUnitary_ne_oracleUnitary (target : Fin d) :
    (hadamardUnitary : Unitary d) ≠ oracleUnitary target :=
  fun h ↦ hadamardMatrix_ne_oracleMatrix target congr(($h).1)

/-- The Grover angle `θ`, such that `sin(θ/2) = 1/√d` -/
noncomputable def groverAngle (dim : ℕ) : ℝ :=
  2 * Real.arcsin (1 / √dim)

noncomputable def halfAngle (n : ℕ) : ℝ :=
  Real.arcsin (1 / √(2 ^ n))

/-- Success probability of Grover's algorithm after K iterations.
    `p_succ(K, d) = sin^2((2K+1)/2 * θ)` where `sin(θ/2) = 1/√d`. -/
noncomputable def p_succ (K : ℕ) (dim : ℕ) : ℝ :=
  (Real.sin ((2 * (K : ℝ) + 1) / 2 * groverAngle dim)) ^ 2

/-- `p_succ` in terms of the half angle: `p_succ K dim = sin ((2K + 1) arcsin (1 / √dim)) ^ 2`. -/
lemma p_succ_eq_sin_sq (K dim : ℕ) :
    p_succ K dim = Real.sin ((2 * (K : ℝ) + 1) * Real.arcsin (1 / √dim)) ^ 2 := by
  simp only [p_succ, groverAngle, ← mul_assoc, div_mul_cancel₀ _ (two_ne_zero' ℝ)]

@[simp]
lemma clamp_p_succ (K dim : ℕ) :
    max 0 (min (p_succ K dim) 1) = p_succ K dim := by
  rw [min_eq_left (show p_succ K dim ≤ 1 from Real.sin_sq_le_one _),
    max_eq_right (show 0 ≤ p_succ K dim from sq_nonneg _)]

lemma inv_sqrt_dim_le_one : 1 / √d ≤ 1 :=
  (div_le_one (by positivity)).2 (Real.one_le_sqrt.2 (by exact_mod_cast Nat.one_le_two_pow))

lemma sin_halfAngle : Real.sin (halfAngle n) = 1 / √d := by
  apply Real.sin_arcsin
  · have : (0 : ℝ) ≤ 1 / √d := by positivity
    linarith
  · exact inv_sqrt_dim_le_one

lemma sqrt_dim_mul_sin_halfAngle :
    √d * Real.sin (halfAngle n) = 1 := by
  rw [sin_halfAngle]
  field_simp

lemma sin_step (k : ℕ) :
    Real.sin ((2 * (k : ℝ) + 3) * halfAngle n) =
      Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) +
        2 / d * (√d * Real.cos ((2 * (k : ℝ) + 2) * halfAngle n)) := by
  have htrig := Real.sin_sub_sin
    ((2 * (k : ℝ) + 3) * halfAngle n)
    ((2 * (k : ℝ) + 1) * halfAngle n)
  rw [show (((2 * (k : ℝ) + 3) * halfAngle n -
      (2 * (k : ℝ) + 1) * halfAngle n) / 2) = halfAngle n by ring,
    show (((2 * (k : ℝ) + 3) * halfAngle n +
      (2 * (k : ℝ) + 1) * halfAngle n) / 2) =
      (2 * (k : ℝ) + 2) * halfAngle n by ring] at htrig
  rw [sub_eq_iff_eq_add] at htrig
  rw [htrig, sin_halfAngle, ← Real.sqrt_div_self']
  ring

lemma cos_step (k : ℕ) :
    √d * Real.cos ((2 * (k : ℝ) + 2) * halfAngle n) =
      √d * Real.cos (2 * (k : ℝ) * halfAngle n) -
        2 * Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) := by
  have htrig := Real.cos_sub_cos
    (2 * (k : ℝ) * halfAngle n)
    ((2 * (k : ℝ) + 2) * halfAngle n)
  rw [show ((2 * (k : ℝ) * halfAngle n +
      (2 * (k : ℝ) + 2) * halfAngle n) / 2) =
      (2 * (k : ℝ) + 1) * halfAngle n by ring,
    show ((2 * (k : ℝ) * halfAngle n -
      (2 * (k : ℝ) + 2) * halfAngle n) / 2) = -halfAngle n by ring,
    Real.sin_neg] at htrig
  have hy : Real.cos ((2 * (k : ℝ) + 2) * halfAngle n) =
      Real.cos (2 * (k : ℝ) * halfAngle n) -
        2 * Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) * Real.sin (halfAngle n) := by
    linarith
  have hs := sqrt_dim_mul_sin_halfAngle (n := n)
  rw [hy, mul_sub]
  calc
    √d * Real.cos (2 * (k : ℝ) * halfAngle n) -
        √d *
          (2 * Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) * Real.sin (halfAngle n)) =
        √d * Real.cos (2 * (k : ℝ) * halfAngle n) -
          2 * Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) *
            (√d * Real.sin (halfAngle n)) := by ring
    _ = √d * Real.cos (2 * (k : ℝ) * halfAngle n) -
        2 * Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) := by rw [hs]; ring

lemma oracleMatrix_mulVec (target : Fin d) (v : Fin d → ℂ) (i : Fin d) :
    (oracleMatrix target *ᵥ v) i = if i = target then -v i else v i := by
  classical
  simp [oracleMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal]

lemma diffuserMatrix_mulVec (v : Fin d → ℂ) (i : Fin d) :
    (diffuserMatrix *ᵥ v) i =
      (2 : ℂ) / d * ∑ j, v j - v i := by
  rw [diffuserMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.mulVec_eq_sum]
  simp [-op_smul_eq_smul, Finset.mul_sum]

lemma sum_oracleMatrix_mulVec (target : Fin d) (v : Fin d → ℂ) :
    ∑ i, (oracleMatrix target *ᵥ v) i = ∑ i, v i - 2 * v target := by
  classical
  simp_rw [oracleMatrix_mulVec]
  rw [show (fun i : Fin d ↦ if i = target then -v i else v i) =
      fun i ↦ v i + if i = target then -2 * v i else 0 by
    funext i
    split_ifs <;> ring]
  rw [Finset.sum_add_distrib]
  simp
  abel

lemma sum_diffuserMatrix_mulVec (v : Fin d → ℂ) :
    ∑ i, (diffuserMatrix *ᵥ v) i = ∑ i, v i := by
  classical
  simp_rw [diffuserMatrix_mulVec]
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))
  field_simp
  push_cast
  ring

lemma sin_step_complex (k : ℕ) :
    (Real.sin ((2 * (k : ℝ) + 3) * halfAngle n) : ℂ) =
      (Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) : ℂ) +
        (2 : ℂ) / d *
          (√d * Real.cos ((2 * (k : ℝ) + 2) * halfAngle n) : ℂ) := by
  have h := congrArg (fun x : ℝ ↦ (x : ℂ)) (sin_step (n := n) k)
  push_cast at h
  simpa using h

lemma cos_step_complex (k : ℕ) :
    (√d * Real.cos ((2 * (k : ℝ) + 2) * halfAngle n) : ℂ) =
      (√d * Real.cos (2 * (k : ℝ) * halfAngle n) : ℂ) -
        2 * (Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) : ℂ) := by
  have h := congrArg (fun x : ℝ ↦ (x : ℂ)) (cos_step (n := n) k)
  push_cast at h
  simpa using h

/-- The state vector obtained from the uniform state after `k` Grover iterations. -/
noncomputable def groverState (target : Fin d) : ℕ → Fin d → ℂ
  | 0 => fun _ ↦ (1 / √d : ℝ)
  | k + 1 => diffuserMatrix *ᵥ oracleMatrix target *ᵥ groverState target k

/-- The two scalar invariants needed for Grover's amplitude recurrence: the marked
amplitude and the sum of all amplitudes. -/
theorem groverState_target_sum (target : Fin d) (k : ℕ) :
    groverState target k target =
        (Real.sin ((2 * (k : ℝ) + 1) * halfAngle n) : ℂ) ∧
      ∑ i, groverState target k i =
        (√d * Real.cos (2 * (k : ℝ) * halfAngle n) : ℂ) := by
  induction k with
  | zero =>
      constructor
      · simp [groverState, sin_halfAngle]
      · simp only [groverState, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        norm_cast
        simpa [div_eq_mul_inv] using Real.div_sqrt (x := (d : ℝ))
  | succ k ih =>
      rcases ih with ⟨htarget, hsum⟩
      constructor
      · rw [groverState, diffuserMatrix_mulVec, sum_oracleMatrix_mulVec,
          oracleMatrix_mulVec, ite_eq_left rfl, htarget, hsum]
        rw [← cos_step_complex (n := n) k]
        rw [show (2 * ((k + 1 : ℕ) : ℝ) + 1) * halfAngle n =
            (2 * (k : ℝ) + 3) * halfAngle n by push_cast; ring]
        rw [sin_step_complex (n := n) k]
        ring
      · rw [groverState, sum_diffuserMatrix_mulVec,
          sum_oracleMatrix_mulVec, hsum, htarget]
        rw [← cos_step_complex (n := n) k]
        congr 2
        push_cast
        ring_nf

/-- Every number of Grover iterations succeeds with positive probability. By Niven's theorem
`halfAngle n` is a rational multiple of `π` only for `π / 6`, `π / 4` and `π / 2`, and no odd
multiple of these is a multiple of `π`. -/
lemma p_succ_pos (K : ℕ) : 0 < p_succ K d := by
  rw [p_succ_eq_sin_sq, Nat.cast_pow, Nat.cast_ofNat, ← halfAngle]
  suffices Real.sin ((2 * K + 1) * halfAngle n) ≠ 0 by positivity
  intro h
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 h
  have hpos : 0 < halfAngle n := Real.arcsin_pos.2 (by positivity)
  have hle : halfAngle n ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hcos : Real.cos (2 * halfAngle n) = 1 - 2 / 2 ^ n := by
    rw [Real.cos_two_mul_eq_one_sub, sin_halfAngle, div_pow, Real.sq_sqrt (by positivity)]
    ring
  have hodd (c : ℝ) (hc : 2 * halfAngle n = c * π) : (2 * K + 1) * c = 2 * m :=
    mul_right_cancel₀ Real.pi_ne_zero (by linear_combination -(2 * K + 1) * hc - 2 * hm)
  have hmem := niven_angle_eq (θ := 2 * halfAngle n) ⟨2 * m / (2 * K + 1), by
      push_cast
      field_simp
      linear_combination -hm⟩
    ⟨1 - 2 / 2 ^ n, by rw [hcos]; push_cast; ring⟩ ⟨by linarith, by linarith⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · linarith
  · have := hodd (1 / 3) (by linarith)
    field_simp at this
    norm_cast at this
    omega
  · have := hodd (1 / 2) (by linarith)
    field_simp at this
    norm_cast at this
    omega
  · rw [h, show π * (2 / 3) = π - π / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hcos
    have : (3 : ℝ) * 2 ^ n = 4 := by field_simp at hcos; linarith
    have : 3 * 2 ^ n = 4 := by exact_mod_cast this
    omega
  · have := hodd 1 (by linarith)
    norm_cast at this
    omega

/-- Forward matrix of the Hadamard preparation followed by `k` Grover iterations. -/
noncomputable def groverMatrix (target : Fin d) : ℕ → Matrix (Fin d) (Fin d) ℂ
  | 0 => hadamardMatrix n
  | k + 1 => diffuserMatrix * (oracleMatrix target * groverMatrix target k)

noncomputable def groverOperator (target : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  diffuserMatrix * oracleMatrix target

@[simp]
lemma groverMatrix_succ (target : Fin d) (k : ℕ) :
    groverMatrix target (k + 1) =
      diffuserMatrix * (oracleMatrix target * groverMatrix target k) := rfl

@[simp]
lemma groverMatrix_eq_pow_mul_hadamard (target : Fin d) (k : ℕ) :
    groverMatrix target k =
      (groverOperator target) ^ k * hadamardMatrix n := by
  induction k with
  | zero => simp [groverMatrix]
  | succ k ih =>
      rw [groverMatrix, ih]
      simp only [groverOperator, pow_succ']
      noncomm_ring

@[simp]
lemma groverMatrix_apply_zero (target : Fin d) (k : ℕ) (i : Fin d) :
    groverMatrix target k i 0 = groverState target k i := by
  induction k generalizing i with
  | zero =>
      simp [groverMatrix, groverState]
  | succ k ih =>
      simp only [groverMatrix, groverState, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      simp_rw [ih]

/-- The `(0,0)` entry of the backwards-propagated success projector is exactly Grover's
closed-form success probability. -/
theorem grover_success_matrix_entry (target : Fin d) (k : ℕ) :
    ((groverMatrix target k)ᴴ * compProj target *
      groverMatrix target k) 0 0 =
      (p_succ k d : ℂ) := by
  rw [conjTranspose_compProj_mul_apply, groverMatrix_apply_zero,
    (groverState_target_sum target k).1, p_succ_eq_sin_sq, Nat.cast_pow, Nat.cast_ofNat,
    ← halfAngle, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  norm_cast
  ring

end Grover
