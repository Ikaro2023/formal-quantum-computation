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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.DualBellReflStage5Stack
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

namespace QuantumComputation.Specs.PhotochemistrySolution.RieszQspCovering


open Real Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open WithLp Polynomial ComplexConjugate
open PhotochemistrySolution PhotochemistrySolution.GQSP PhotochemistrySolution.OvBidir
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
open PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
open scoped Matrix Matrix.Norms.L2Operator BigOperators Polynomial

noncomputable section

noncomputable def unitPhase24 (k : Fin 24) : ℂ :=
    Complex.exp (((2 * π * (k.val : ℝ) / 24 : ℝ) : ℂ) * Complex.I)
noncomputable def s3PosVecList : List (ℂ × ℂ) :=
  (List.finRange 24).flatMap fun m ↦ (List.finRange 24).flatMap fun k₀ ↦
      (List.finRange 24).map fun k₁ ↦
    let φ : ℝ := 2 * π * (m.val : ℝ) / 24
    (((|Real.cos φ| : ℝ) : ℂ) * unitPhase24 k₀, ((|Real.sin φ| : ℝ) : ℂ) * unitPhase24 k₁)

/-- Symmetric `2 * 24^3 = 27,648`-vector unit covering of `ℂ × ℂ`. -/
noncomputable def s3VecList : List (ℂ × ℂ) := s3PosVecList ++ s3PosVecList.map fun w ↦ (-w.1, -w.2)
noncomputable def trigPolyRe (q : ℂ[X]) (φ : ℝ) : ℝ :=
    (q.eval (Complex.exp ((φ : ℂ) * Complex.I))).re

/-- Polynomial whose unit-circle real evaluation equals `deriv (trigPolyRe q)`. -/
noncomputable def polyCircDeriv (q : ℂ[X]) : ℂ[X] :=
    ∑ k ∈ Finset.range (q.natDegree + 1), Polynomial.C (Complex.I * (k : ℂ) * q.coeff k) *
    Polynomial.X ^ k
theorem natDegree_polyCircDeriv_le (q : ℂ[X]) : (polyCircDeriv q).natDegree ≤ q.natDegree := by
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  simp only [Finset.fold_max_le]
  exact ⟨Nat.zero_le _, fun _ hk ↦
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))⟩
theorem eval_polyCircDeriv (q : ℂ[X]) (z : ℂ) : (polyCircDeriv q).eval z =
    ∑ k ∈ Finset.range (q.natDegree + 1), Complex.I *
    (k : ℂ) * q.coeff k * z ^ k := by simp [polyCircDeriv, Polynomial.eval_finsetSum]
theorem exp_ofReal_mul_I_pow (φ : ℝ) (k : ℕ) : Complex.exp ((φ : ℂ) * Complex.I) ^ k =
    Complex.exp ((((k : ℝ) * φ : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]

theorem hasDerivAt_trigPolyRe (q : ℂ[X]) (φ : ℝ) : HasDerivAt (trigPolyRe q)
    (trigPolyRe (polyCircDeriv q) φ) φ := by
  have hre (c : ℂ) (k : ℕ) (θ : ℝ) : (c * Complex.exp ((θ : ℂ) * Complex.I) ^ k).re =
      c.re * Real.cos ((k : ℝ) * θ) - c.im * Real.sin ((k : ℝ) * θ) := by
    rw [exp_ofReal_mul_I_pow, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.add_im, Complex.mul_im]
    ring
  rw [show trigPolyRe q = fun θ : ℝ ↦ ∑ k ∈ Finset.range (q.natDegree + 1),
      ((q.coeff k).re * Real.cos ((k : ℝ) * θ) - (q.coeff k).im * Real.sin ((k : ℝ) * θ)) from
      funext fun θ ↦ by simp only [trigPolyRe, Polynomial.eval_eq_sum_range, Complex.re_sum, hre],
    show trigPolyRe (polyCircDeriv q) φ = ∑ k ∈ Finset.range (q.natDegree + 1),
      ((q.coeff k).re * (-Real.sin ((k : ℝ) * φ) * (k : ℝ)) - (q.coeff k).im *
          (Real.cos ((k : ℝ) * φ) * (k : ℝ))) by
      simp only [trigPolyRe, eval_polyCircDeriv, Complex.re_sum, hre, Complex.mul_re,
          Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring]
  convert (HasDerivAt.sum fun (k : ℕ) (_ : k ∈ Finset.range (q.natDegree + 1)) ↦
    (((Real.hasDerivAt_cos ((k : ℝ) *
        φ)).comp φ (by simpa using (hasDerivAt_id φ).const_mul (k : ℝ))).const_mul
      (q.coeff k).re).sub (((Real.hasDerivAt_sin ((k : ℝ) * φ)).comp φ
      (by simpa using (hasDerivAt_id φ).const_mul (k : ℝ))).const_mul (q.coeff k).im)) using 1
  exact funext fun _ ↦ by simp

theorem deriv_trigPolyRe (q : ℂ[X]) : deriv (trigPolyRe q) = trigPolyRe (polyCircDeriv q) :=
    funext fun φ ↦ (hasDerivAt_trigPolyRe q φ).deriv
theorem differentiable_trigPolyRe (q : ℂ[X]) : Differentiable ℝ (trigPolyRe q) := fun φ ↦
    (hasDerivAt_trigPolyRe q φ).differentiableAt
theorem trigPolyRe_periodic (q : ℂ[X]) (φ : ℝ) (n : ℤ) : trigPolyRe q (φ + (n : ℝ) * (2 * π)) =
    trigPolyRe q φ := by
  unfold trigPolyRe
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, show (((n : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I =
      (n : ℂ) *
    (2 * π * Complex.I) by simp [mul_assoc], Complex.exp_eq_one_iff.mpr ⟨n, rfl⟩, mul_one]

/-- Odd Riesz interpolation nodes `ζ_m = exp(i (2m + 1) π / (2d))`. -/
noncomputable def rieszNode (d m : ℕ) : ℝ := (2 * (m : ℝ) + 1) * π / (2 * (d : ℝ))

/-- Complex odd Riesz root `exp(i θ_m)`. -/
noncomputable def rieszZeta (d m : ℕ) : ℂ := Complex.exp ((rieszNode d m : ℂ) * Complex.I)

/-- Positive Riesz weight `w_m = (1 / 2) * ‖∑_{l=0}^{2d-1} ζ_m^l‖^2`. -/
noncomputable def rieszWeight (d m : ℕ) : ℝ :=
    (1 / 2 : ℝ) * ‖∑ l ∈ Finset.range (2 * d), rieszZeta d m ^ l‖ ^ 2
theorem rieszWeight_nonneg (d m : ℕ) : 0 ≤ rieszWeight d m := mul_nonneg (by norm_num) (sq_nonneg _)
theorem rieszWeight_ofReal (d m : ℕ) : (rieszWeight d m : ℂ) = (1 / 2 : ℂ) *
    (∑ l ∈ Finset.range (2 * d), rieszZeta d m ^ l) * (∑ r ∈ Finset.range (2 * d),
    conj (rieszZeta d m) ^ r) := by
  simp only [rieszWeight, Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
      map_sum, map_pow, ← mul_assoc]
  push_cast
  rfl

theorem rieszZeta_pow_d {d : ℕ} (hd : 1 ≤ d) (m : ℕ) : -Complex.I * rieszZeta d m ^ d =
    ((-1 : ℝ) ^ m : ℂ) := by
  unfold rieszZeta
  rw [exp_ofReal_mul_I_pow, show ((((d : ℝ) * rieszNode d m : ℝ) : ℂ) * Complex.I) =
      (m : ℕ) * (π * Complex.I) + (((π / 2 : ℝ) : ℂ) * Complex.I) by
    unfold rieszNode
    push_cast
    field_simp [Nat.cast_ne_zero.mpr (by omega : d ≠ 0)], Complex.exp_add, Complex.exp_nat_mul,
    Complex.exp_pi_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  linear_combination -((-1 : ℂ) ^ m) * Complex.I_sq

theorem rieszZeta_pow_mul_conj_pow {d : ℕ} (m a b : ℕ) :
    rieszZeta d m ^ a * conj (rieszZeta d m) ^ b =
        Complex.exp (((((a : ℝ) - (b : ℝ)) * π / (2 * (d : ℝ)) : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((((a : ℝ) - (b : ℝ)) * π / (d : ℝ) : ℝ) : ℂ) * Complex.I)) ^ m := by
  unfold rieszZeta rieszNode
  rw [← Complex.exp_conj, show conj ((((2 * (m : ℝ) + 1) * π / (2 * (d : ℝ)) : ℝ) : ℂ) *
      Complex.I) = -((((2 * (m : ℝ) + 1) * π / (2 *
    (d : ℝ)) : ℝ) : ℂ) * Complex.I) by simp [map_ofNat]]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sum_rieszZeta_pow_mul_conj_pow {d : ℕ} (hd : 1 ≤ d) (a b : ℕ) :
    ∑ m ∈ Finset.range (2 * d), rieszZeta d m ^ a * conj (rieszZeta d m) ^ b =
      if (2 * (d : ℤ)) ∣ ((a : ℤ) - (b : ℤ)) then (2 * (d : ℂ)) *
          Complex.exp (((((a : ℝ) - (b : ℝ)) * π / (2 * (d : ℝ)) : ℝ) : ℂ) * Complex.I) else 0 := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set n : ℤ := (a : ℤ) - (b : ℤ)
  have hn_cast : (n : ℝ) = (a : ℝ) - (b : ℝ) := by simp [n]
  set c₀ : ℂ := Complex.exp ((((n : ℝ) * π / (2 * (d : ℝ)) : ℝ) : ℂ) * Complex.I)
  set ω : ℂ := Complex.exp ((((n : ℝ) * π / (d : ℝ) : ℝ) : ℂ) * Complex.I)
  have hterm (m : ℕ) : rieszZeta d m ^ a * conj (rieszZeta d m) ^ b = c₀ * ω ^ m := by
    simp only [rieszZeta_pow_mul_conj_pow, c₀, ω, hn_cast]
  simp_rw [hterm, ← Finset.mul_sum]
  split_ifs with hdiv
  · obtain ⟨t, ht⟩ := hdiv
    rw [show ω = 1 from Complex.exp_eq_one_iff.mpr ⟨t, by
      rw [show (n : ℝ) = (2 * (d : ℝ)) * (t : ℝ) by exact_mod_cast ht]
      push_cast; field_simp [hdC]⟩]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hn_cast, c₀]
    push_cast; ring
  · have hω_ne : ω ≠ 1 := fun h1 ↦ by
      obtain ⟨t, ht⟩ := Complex.exp_eq_one_iff.mp h1
      push_cast at ht
      field_simp [hdC, Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] at ht
      exact hdiv ⟨t, by exact_mod_cast (by linear_combination ht : (n : ℂ) = 2 * d * t)⟩
    rw [geom_sum_eq hω_ne, show ω ^ (2 * d) = 1 by
      rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      exact ⟨n, by push_cast; field_simp [hdC]⟩, sub_self, zero_div, mul_zero]

theorem sum_range_ite_add (N c : ℕ) (v : ℂ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if j = c + i then v else 0) = ((N - c : ℕ) : ℂ) *
        v := by
  simp only [Finset.sum_ite_eq', Finset.mem_range, ← Finset.sum_filter]
  rw [show (Finset.range N).filter (fun i ↦ c + i < N) = Finset.range (N -
      c) from Finset.ext fun i ↦ by
    simp only [Finset.mem_filter, Finset.mem_range]
    omega]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem sum_rieszWeight {d : ℕ} (hd : 1 ≤ d) : (1 / (2 * (d : ℝ))) * ∑ m ∈ Finset.range (2 * d),
    rieszWeight d m = (d : ℝ) := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply Complex.ofReal_injective
  push_cast
  have htw (m : ℕ) : (rieszWeight d m : ℂ) = ∑ l ∈ Finset.range (2 * d),
      ∑ r ∈ Finset.range (2 * d), (1 / 2 : ℂ) * (rieszZeta d m ^ l * conj (rieszZeta d m) ^ r) := by
    rw [rieszWeight_ofReal]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  simp_rw [htw]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm]
  have Dinner : ∀ l ∈ Finset.range (2 * d), ∀ r ∈ Finset.range (2 * d),
      ∑ m ∈ Finset.range (2 * d), (1 / 2 : ℂ) * (rieszZeta d m ^ l * conj (rieszZeta d m) ^ r) =
        if r = 0 + l then (d : ℂ) else 0 := fun l hl r hr ↦ by
    rw [Finset.mem_range] at hl hr
    rw [zero_add, ← Finset.mul_sum, sum_rieszZeta_pow_mul_conj_pow hd]
    by_cases hrl : r = l
    · subst hrl
      simp only [sub_self, dvd_zero, ↓reduceIte, zero_mul, zero_div, Complex.ofReal_zero,
          Complex.exp_zero, mul_one]
      ring
    · simp [hrl, show ¬ ((2 * (d : ℤ)) ∣ ((l : ℤ) - (r : ℤ))) from fun ⟨q, hq⟩ ↦ by
        obtain rfl : q = 0 := by
          nlinarith [hq, show -(2 * (d : ℤ)) < (l : ℤ) - (r : ℤ) by omega, show (l : ℤ) - (r : ℤ) <
              2 * (d : ℤ) by omega]
        omega]
  rw [Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl (Dinner l hl), sum_range_ite_add,
      Nat.sub_zero]
  push_cast
  field_simp [hdC]

theorem sum_riesz_kernel_pow {d k : ℕ} (hd : 1 ≤ d) (hk : k ≤ d) :
    (1 / (2 * (d : ℂ))) * ∑ m ∈ Finset.range (2 * d), ((-1 : ℝ) ^ m : ℂ) * (rieszWeight d m : ℂ) *
        rieszZeta d m ^ k = Complex.I * (k : ℂ) := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hterm (m : ℕ) : ((-1 : ℝ) ^ m : ℂ) * (rieszWeight d m : ℂ) * rieszZeta d m ^ k =
      (-Complex.I / 2) * ∑ l ∈ Finset.range (2 * d), ∑ r ∈ Finset.range (2 * d),
          rieszZeta d m ^ (d + k + l) * conj (rieszZeta d m) ^ r := by
    rw [← rieszZeta_pow_d hd m, rieszWeight_ofReal, Finset.sum_comm]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    rw [pow_add, pow_add]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm]
  have Dinner : ∀ l ∈ Finset.range (2 * d), ∀ r ∈ Finset.range (2 * d), ∑ m ∈ Finset.range (2 * d),
      rieszZeta d m ^ (d + k + l) * conj (rieszZeta d m) ^ r =
      (if r = (d + k) + l then (2 * (d : ℂ)) else 0) + (if l = (d - k) +
          r then -(2 * (d : ℂ)) else 0) := by
    intro l hl r hr
    rw [Finset.mem_range] at hl hr
    rw [sum_rieszZeta_pow_mul_conj_pow hd]
    by_cases h0 : r = (d + k) + l
    · subst h0
      simp [show l ≠ (d - k) + (d + k + l) by omega]
    · by_cases h1 : l = (d - k) + r
      · rw [ite_eq_left (show (2 * (d : ℤ)) ∣ (((d + k + l : ℕ) : ℤ) - (r : ℤ)) from ⟨1, by omega⟩),
          show (((d + k + l : ℕ) : ℝ) - (r : ℝ)) = 2 * (d : ℝ) by
            rw [show d + k + l = r + 2 * d by omega]
            push_cast
            ring,
          mul_div_cancel_left₀ π (by positivity), Complex.exp_pi_mul_I, ite_eq_right h0,
              ite_eq_left h1]
        ring
      · simp only [h0, h1, show ¬ ((2 * (d : ℤ)) ∣ (((d + k + l : ℕ) : ℤ) - (r : ℤ))) from fun ⟨q,
            hq⟩ ↦ by
          have hb1 : -1 < q := by
            nlinarith [hq, show -(2 * (d : ℤ)) < ((d + k + l : ℕ) : ℤ) - (r : ℤ) by omega]
          have hb2 : q < 2 := by
            nlinarith [hq, show ((d + k + l : ℕ) : ℤ) - (r : ℤ) < 4 * (d : ℤ) by omega]
          obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
          all_goals omega, ↓reduceIte, zero_add]
  rw [Finset.sum_congr rfl fun l hl ↦ Finset.sum_congr rfl (Dinner l hl)]
  simp_rw [Finset.sum_add_distrib]
  rw [sum_range_ite_add, Finset.sum_comm (s := Finset.range (2 * d)), sum_range_ite_add,
    show 2 * d - (d + k) = d - k by omega, show 2 * d - (d - k) = d + k by omega,
    Nat.cast_sub hk, Nat.cast_add]
  field_simp [hdC]
  ring

/-- Riesz representation of `deriv (trigPolyRe q) φ` at degree `≤ d`. -/
theorem riesz_interp_trigPolyRe {d : ℕ} (hd : 1 ≤ d) {q : ℂ[X]} (hq : q.natDegree ≤ d) (φ : ℝ) :
    trigPolyRe (polyCircDeriv q) φ = (1 / (2 * (d : ℝ))) * ∑ m ∈ Finset.range (2 * d),
        (-1 : ℝ) ^ m * rieszWeight d m * trigPolyRe q (φ + rieszNode d m) := by
  have hsum_deriv (z : ℂ) : (polyCircDeriv q).eval z = ∑ k ∈ Finset.range (d + 1), Complex.I *
      (k : ℂ) * q.coeff k * z ^ k := by
    rw [eval_polyCircDeriv]
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hnot ↦ ?_
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_lt.mp (Finset.mem_range.not.mp hnot)),
        mul_zero, zero_mul]
  have hstep : ∀ k ∈ Finset.range (d + 1), Complex.I * (k : ℂ) * q.coeff k * Complex.exp ((φ : ℂ) *
      Complex.I) ^ k =
      ((1 / (2 * (d : ℝ)) : ℝ) : ℂ) * ∑ m ∈ Finset.range (2 * d),
          (((-1 : ℝ) ^ m * rieszWeight d m : ℝ) : ℂ) * (q.coeff k * Complex.exp
        ((((φ + rieszNode d m : ℝ) : ℂ)) * Complex.I) ^ k) := by
    intro k hk
    rw [show Complex.I * (k : ℂ) * q.coeff k * Complex.exp ((φ : ℂ) * Complex.I) ^ k =
        (Complex.I * (k : ℂ)) * (q.coeff k * Complex.exp ((φ : ℂ) * Complex.I) ^ k) by ring,
      ← sum_riesz_kernel_pow hd (Nat.le_of_lt_succ (Finset.mem_range.mp hk)), mul_assoc,
          Finset.sum_mul]
    congr 1
    · push_cast
      rfl
    · refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [rieszZeta, Complex.ofReal_add, add_mul, Complex.exp_add, mul_pow]
      push_cast
      ring
  have hre_mul (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by simp [Complex.mul_re]
  unfold trigPolyRe
  rw [hsum_deriv, Finset.sum_congr rfl hstep, ← Finset.mul_sum, Finset.sum_comm, hre_mul,
      Complex.re_sum]
  refine congrArg _ (Finset.sum_congr rfl fun m _ ↦ ?_)
  rw [← Finset.mul_sum, ← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hq), hre_mul]

/-- Bernstein-Riesz inequality `|g'(φ)| ≤ d * M` for trigonometric polynomials of degree `≤ d`. -/
theorem riesz_deriv_le {d : ℕ} (hd : 1 ≤ d) {q : ℂ[X]} (hq : q.natDegree ≤ d) {M : ℝ}
    (hM : ∀ θ : ℝ, |trigPolyRe q θ| ≤ M) (φ : ℝ) :
    |deriv (trigPolyRe q) φ| ≤ (d : ℝ) * M := by
  rw [deriv_trigPolyRe, riesz_interp_trigPolyRe hd hq φ, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * (d : ℝ)))]
  calc (1 / (2 * (d : ℝ))) * |∑ m ∈ Finset.range (2 * d), (-1 : ℝ) ^ m * rieszWeight d m *
      trigPolyRe q (φ + rieszNode d m)|
      ≤ (1 / (2 * (d : ℝ))) * ∑ m ∈ Finset.range (2 * d), rieszWeight d m * M := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
        rw [abs_mul, abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (rieszWeight_nonneg d m)]
        exact mul_le_mul_of_nonneg_left (hM _) (rieszWeight_nonneg d m)
    _ = (d : ℝ) * M := by rw [← Finset.sum_mul, ← mul_assoc, sum_rieszWeight hd]

/-- Second Bernstein-Riesz inequality `|g''(φ)| ≤ d^2 * M`. -/
theorem riesz_deriv2_le {d : ℕ} (hd : 1 ≤ d) {q : ℂ[X]} (hq : q.natDegree ≤ d) {M : ℝ}
    (hM : ∀ θ : ℝ, |trigPolyRe q θ| ≤ M) (φ : ℝ) :
    |deriv (deriv (trigPolyRe q)) φ| ≤ (d : ℝ) ^ 2 * M := by
  rw [deriv_trigPolyRe, sq, mul_assoc]
  exact riesz_deriv_le hd ((natDegree_polyCircDeriv_le q).trans hq)
      (fun θ ↦ deriv_trigPolyRe q ▸ riesz_deriv_le hd hq hM θ) φ

noncomputable def mgfVecSum (lam : ℝ) (z : ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ[X]) : ℝ :=
  (s3VecList.map fun w ↦ Real.exp (lam * (conj w.1 * (P 0 0).eval z + conj w.2 *
      (P 1 0).eval z).re)).sum

/-- Total `884,736 * d` MGF potential across the `32 * d` grid and `27,648` unit vectors. -/
noncomputable def mgfPot (d : ℕ) (lam : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ[X]) : ℝ :=
  ∑ j : Fin (32 * d), mgfVecSum lam (Complex.exp (((2 * π * (j.val : ℝ) / (32 * (d : ℝ)) : ℝ) : ℂ) *
      Complex.I)) P

open PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.SelectCompactAnc
open PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.SelectRefl
  PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectCsa64ProvSpec
open PhotochemistrySolution.SelectLcu70Rot32 PhotochemistrySolution.SelectGidneyFast
  PhotochemistrySolution.TargetBScr PhotochemistrySolution.DynQromUncompA
open PhotochemistrySolution.UnembedIdleAncillas PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.UnembedDualBell531 PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.FusedUnembedLGen
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DepthArithWalk (hqTop_kick3_gen_31
    reflAmb_hIC_31 reflAmb_hCC_31 reflAmb_hIn_31 locGrad3HiGen)
open PhotochemistrySolution.Stage5StackCore

set_option allowUnsafeReducibility true

noncomputable section

attribute [local irreducible] systemQubits_frozen ancWOfScr

/-- Pure 1-qubit circuit `c : Circuit 1` embedded on `locQGen hAnc`. -/
noncomputable def pureRotLocalUnitary {ancW : ℕ} (hAnc : 100 ≤ ancW)
    (c : Circuit 1) : Unitary (2 ^ (systemQubits_frozen + ancW)) :=
  (c.onRegister (QRegister.singleton (locQGen hAnc))).eval
theorem pureRotLocalUnitary_val {ancW : ℕ} (hAnc : 100 ≤ ancW)
    (c : Circuit 1) : (pureRotLocalUnitary hAnc c).1 = eQGen hAnc c.eval.1 := by
  rw [pureRotLocalUnitary, Circuit.eval_onRegister]
  exact QRegister.embedUnitary_val _ _

/-- Dynamic circuit executing pure 1-qubit circuit `c : Circuit 1` on `qspQubitGen hAnc rAnc`. -/
def pureRotDyn {Var : Type} {ancW n : ℕ} (hAnc : 100 ≤ ancW) (rAnc : QRegister ancW n)
    (c : Circuit 1) : DynamicCircuit Var n :=
  .circuit (c.onRegister (QRegister.singleton (qspQubitGen hAnc rAnc)))
theorem count_pureRotDyn {Var : Type} {ancW n arity : ℕ} (hAnc : 100 ≤ ancW)
    (rAnc : QRegister ancW n) (c : Circuit 1) (g : PrimitiveGate arity) :
    (pureRotDyn (Var := Var) hAnc rAnc c).count g = c.count g := by
      simp [pureRotDyn, DynamicCircuit.count, Circuit.count_onRegister]
theorem allWiresLtDyn_pureRotDyn {Var : Type} {ancW n k : ℕ} (hAnc : 100 ≤ ancW)
    (rAnc : QRegister ancW n) (c : Circuit 1) (hq : (qspQubitGen hAnc rAnc).val < k) :
    AllWiresLtDyn k (pureRotDyn (Var := Var) hAnc rAnc c) :=
  allWiresLtCirc_onRegister c _ (Fin.forall_fin_one.mpr hq)

theorem compose_singleton_locQGen {ancW n : ℕ} (hAnc : 100 ≤ ancW)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister ancW n)
    (hdisj : rSys.DisjointWires rAnc) :
    (rSys.concat rAnc hdisj).compose (QRegister.singleton (locQGen hAnc)) =
        QRegister.singleton (qspQubitGen hAnc rAnc) :=
  qreg_ext (Fin.forall_fin_one.mpr (QRegister.concat_apply_right rSys rAnc hdisj ⟨ancW - 1,
      by omega⟩))

theorem embedUnitary_pureRotLocalUnitary {ancW n : ℕ} (hAnc : 100 ≤ ancW)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister ancW n)
    (hdisj : rSys.DisjointWires rAnc) (c : Circuit 1) :
    (rSys.concat rAnc hdisj).embedUnitary (pureRotLocalUnitary hAnc c) =
        (c.onRegister (QRegister.singleton (qspQubitGen hAnc rAnc))).eval := by
  rw [pureRotLocalUnitary, Circuit.eval_onRegister, Circuit.eval_onRegister,
      ← QRegister.embedUnitary_compose, compose_singleton_locQGen hAnc rSys rAnc hdisj]

theorem cleanWorkStep_pureRotDyn {Var : Type} [Fintype Var] [DecidableEq Var] {ancW n tSel : ℕ}
    {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
        {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel) (c : Circuit 1) :
    CleanWorkStep (Var := Var) (rAnc.compose D.scrSub)
        ((rSys.concat rAnc hdisj).embedUnitary (pureRotLocalUnitary hAnc c))
        (pureRotDyn hAnc rAnc c) := by
  rw [pureRotDyn, embedUnitary_pureRotLocalUnitary hAnc rSys rAnc hdisj c]
  apply CleanWorkStep.of_pureCircuit_comm
  rw [Circuit.eval_onRegister, QRegister.embedUnitary_val]
  exact (QRegister.singleton (qspQubitGen hAnc rAnc)).embedMatrix_comm_of_disjoint _
    (QRegister.disjoint_iff.mpr (Fin.forall_fin_one.mpr fun j hij ↦
        (D.scr_idx j).2 (congrArg Fin.val (rAnc.wires.injective hij)).symm)) _ _

theorem hSlice26_8 {ancW : ℕ} (hAnc : 100 ≤ ancW) : 26 + 8 ≤ ancW := by omega
theorem locCat8SharedGen_eq_slice {ancW : ℕ} (hAnc : 100 ≤ ancW) : locCat8SharedGen hAnc =
    (locAncGen ancW).slice 26 8 (hSlice26_8 hAnc) :=
  qreg_ext fun i ↦
      Fin.ext (by simp [locCat8SharedGen, locAncGen, QRegister.slice, QRegister.block_apply_val])

theorem commute_walk_data_locCat8SharedGen {Var : Type} [Fintype Var] [DecidableEq Var]
    {ancW n tSel : ℕ} {hAnc : 100 ≤ ancW}
    {rSys : QRegister systemQubits_frozen n} {rAnc : QRegister ancW n}
        {hdisj : rSys.DisjointWires rAnc}
    (D : SelectConjugationDataShared34 (Var := Var) hAnc rSys rAnc hdisj tSel)
        (N : Operator (2 ^ 8)) :
    (∀ M, Commute (eQGen hAnc M) ((locCat8SharedGen hAnc).embedMatrix N)) ∧
        Commute (lcuProjGen D.lcuSub) ((locCat8SharedGen hAnc).embedMatrix N) ∧
      Commute D.S.1 ((locCat8SharedGen hAnc).embedMatrix N) :=
  commute_walk_data_embedMatrixGen D (locCat8SharedGen hAnc)
      (disj_lcu_locCat8SharedGen D) disj_locQGen_locCat8SharedGen
    (fun i ↦ ⟨⟨26 + i.val, by omega⟩,
        Fin.ext (by simp [locCat8SharedGen, locAncGen, QRegister.block_apply_val]),
      fun ⟨a, ha⟩ ↦ ((fun h ↦ (by dsimp only at h; omega : False)) (ha ▸ (D.lcu_idx a).1)),
      fun ⟨a, ha⟩ ↦ ((fun h ↦ (by dsimp only at h; omega : False)) (ha ▸ (D.scr_idx a).1))⟩) N

end

/-- Fused single-wrap `(X q ;; czZ ;; X q) ;; pureRotDyn ;; czZ` (`4 * (m + 1) + c.count .T`). -/
noncomputable def fusedReflPureRotDyn {scrW scrL m offRefl : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL)
    {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_frozen n)
        (rAnc : QRegister (ancWOfScr scrW) n) (hdisj : rSys.DisjointWires rAnc)
        (c : Circuit 1) : DynamicCircuit Var n :=
  let rTot := rSys.concat rAnc hdisj
  let qAmb := qspQubitGen (hAncCompact scrW) rAnc
  let rLcuAmb : Fin (m + 2) → Wire n := fun i ↦ rTot (rLcuLGen hp i)
  let rClnAmb : Fin (m + 1) → Wire n := fun j ↦ rTot (reflRCleanLGenOff hp hm j)
  let cpAmb :=
      norChainReflProg m rLcuAmb rClnAmb (reflAmb_hIC_31 hp hm rTot) (reflAmb_hCC_31 hp hm rTot)
      (reflAmb_hIn_31 hp rTot)
  let czZAmb : Circuit n :=
      .seq (czGateCircuit qAmb (rClnAmb (Fin.last m)) (hqTop_kick3_gen_31 hp hm rSys rAnc hdisj))
      (Circuit.Z qAmb)
  wrapDyn v cpAmb (.seq (.circuit (Circuit.X qAmb)) (.seq (.circuit czZAmb)
      (.seq (.circuit (Circuit.X qAmb)) (.seq (pureRotDyn (hAncCompact scrW) rAnc c)
      (.circuit czZAmb)))))

theorem count_fusedReflPureRotDyn {scrW scrL m offRefl : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL)
    {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_frozen n)
        (rAnc : QRegister (ancWOfScr scrW) n) (hdisj : rSys.DisjointWires rAnc) (c : Circuit 1) :
    (fusedReflPureRotDyn hp hm v rSys rAnc hdisj c).count .T = 4 * (m + 1) + c.count .T ∧
        (fusedReflPureRotDyn hp hm v rSys rAnc hdisj c).count .TOFF = c.count .TOFF := by
  dsimp only [fusedReflPureRotDyn]
  rw [(count_wrapDyn v _ _).1, (count_wrapDyn v _ _).2, norChainReflProg_numAnd]
  simp [DynamicCircuit.count, count_pureRotDyn, Circuit.X, Circuit.Z, czGateCircuit]

theorem allWiresLtDyn_fusedReflPureRotDyn {scrW scrL m offRefl ancW' kIdle : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (_hOff65 : 65 ≤ offRefl) (hm : offRefl + (m + 1) ≤ scrL)
    (part : AncillaPartition (ancWOfScr scrW) ancW' kIdle)
    (hIdleSafe : ∀ l : Fin kIdle, let u := (part.idleIdx l).val
      u < 26 ∨ (31 ≤ u ∧ u < 64) ∨ (97 ≤ u ∧ u < 34 + offRefl) ∨ (34 + offRefl + (m + 1) ≤ u ∧ u <
          34 + scrL) ∨ (34 + scrL + (m + 2) ≤ u ∧ u < ancWOfScr scrW - 1))
    {Var : Type} {n : ℕ} (v : Var) (rSys : QRegister systemQubits_frozen n)
        (rAncSmall : QRegister ancW' n) (_hdisj : rSys.DisjointWires rAncSmall) (c : Circuit 1) :
    let rAmb : QRegister n (n + kIdle) := QRegister.block 0 n (zero_add_le_add_right n kIdle)
    let rPhantom : QRegister kIdle (n + kIdle) := QRegister.block n kIdle le_rfl
    let rS := rAmb.compose rSys
    let rA := assembleAnc part (rAmb.compose rAncSmall) rPhantom (amb_disj_phantom rAncSmall)
    ∀ hdisj' : rS.DisjointWires rA, AllWiresLtDyn n (fusedReflPureRotDyn hp hm v rS rA hdisj' c)
        := by
  intro rAmb rPhantom rS rA hdisj'
  have ha := ancWOfScr_eq_fs scrW
  have hAncLt (j : Fin (ancWOfScr scrW)) (hj : (34 + offRefl ≤ j.val ∧ j.val < 34 + offRefl +
      (m + 1)) ∨ (34 + scrL ≤ j.val ∧ j.val < 34 + scrL + (m + 2)) ∨ j.val = ancWOfScr scrW - 1) :
      (rA j).val < n :=
    UnembedO3Bridge.assembleAnc_val_lt_of_not_idle part rAncSmall j fun l hl ↦ by
      have hu := congrArg Fin.val hl ▸ hIdleSafe l
      dsimp only at hu
      omega
  let qA := qspQubitGen (hAncCompact scrW) rA
  have hq : qA.val < n := hAncLt ⟨ancWOfScr scrW - 1, by omega⟩ (Or.inr (Or.inr rfl))
  have hLcu (i : Fin (m + 2)) : ((rS.concat rA hdisj') (rLcuLGen hp i)).val < n :=
    (concat_rLcu_apply_fs hp rS rA hdisj' i).symm ▸ hAncLt _
        (Or.inr (Or.inl (by dsimp [lcuSubLGen]; omega)))
  have hCln (j : Fin (m + 1)) : ((rS.concat rA hdisj') (reflRCleanLGenOff hp hm j)).val < n :=
    (concat_rScr_apply_fs hp rS rA hdisj' ⟨offRefl + j.val,
        by omega⟩).symm ▸ hAncLt _ (Or.inl (by dsimp [scrSubLGen]; omega))
  have hCzZ : AllWiresLtCirc n (.seq (czGateCircuit qA _ (hqTop_kick3_gen_31 hp hm rS rA hdisj'))
      (Circuit.Z qA)) :=
    ⟨⟨allWiresLtCirc_single (hCln _), allWiresLtCirc_pair hq (hCln _),
        allWiresLtCirc_single (hCln _)⟩, allWiresLtCirc_single hq⟩
  exact allWiresLtDyn_wrapDyn_fs v (cpWires_norChainReflProg_fs hLcu hCln)
    ⟨allWiresLtCirc_single hq, hCzZ, allWiresLtCirc_single hq,
        allWiresLtDyn_pureRotDyn (hAncCompact scrW) rA c hq, hCzZ⟩

theorem cleanProj_image_eq_basisOutcomeProjector_zero {scrL n : ℕ} [NeZero (2 ^ n)]
    (rScr : QRegister scrL n) : cleanProj (Finset.univ.image rScr.wires) =
    rScr.basisOutcomeProjector 0 := by
  apply DynCircExt.matrix_ext_ket
  intro β
  rw [cleanProj_mulVec_ket, SelectRefl.ket_basisOutcomeProjector_zero rScr β]
  by_cases hk : ∀ k : Fin scrL, β (rScr k) = 0 <;> simp [hk]

attribute [local irreducible] fwdCirc wrapDyn in
theorem cleanWorkStep_wrapDyn_fused_circuit5 {Var : Type} [Fintype Var] [DecidableEq Var]
    {scrL n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (cpAmb : ComputeProg n) (rScr : QRegister scrL n) (qAmb : Wire n)
        (czZAmb cAmb : Circuit n) (R_refl : Operator (2 ^ n)) (U_fused : Unitary (2 ^ n))
    (hValid : cpAmb.ValidProg ∅ (Finset.univ.image rScr.wires))
    (hUf : U_fused.1 = R_refl * cAmb.eval.1 * (Circuit.X qAmb).eval.1 * R_refl *
        (Circuit.X qAmb).eval.1)
    (hFCR : czZAmb.eval.1 * ((fwdCirc cpAmb).eval.1 * rScr.basisOutcomeProjector 0) =
        (fwdCirc cpAmb).eval.1 * (R_refl * rScr.basisOutcomeProjector 0))
    (hRP : R_refl * rScr.basisOutcomeProjector 0 = rScr.basisOutcomeProjector 0 * R_refl)
    (hXP : (Circuit.X qAmb).eval.1 * rScr.basisOutcomeProjector 0 = rScr.basisOutcomeProjector 0 *
        (Circuit.X qAmb).eval.1)
    (hUP : cAmb.eval.1 * rScr.basisOutcomeProjector 0 = rScr.basisOutcomeProjector 0 * cAmb.eval.1)
    (hFX : (Circuit.X qAmb).eval.1 * (fwdCirc cpAmb).eval.1 = (fwdCirc cpAmb).eval.1 *
        (Circuit.X qAmb).eval.1)
    (hFU : cAmb.eval.1 * (fwdCirc cpAmb).eval.1 = (fwdCirc cpAmb).eval.1 * cAmb.eval.1) :
    CleanWorkStep (Var := Var) rScr U_fused (wrapDyn v cpAmb (.seq (.circuit (Circuit.X qAmb))
        (.seq (.circuit czZAmb) (.seq (.circuit (Circuit.X qAmb)) (.seq (.circuit cAmb)
        (.circuit czZAmb)))))) := by
  set P := rScr.basisOutcomeProjector 0
  have hCleanP : cleanProj (Finset.univ.image rScr.wires) = P :=
      cleanProj_image_eq_basisOutcomeProjector_zero rScr
  have hPP : P * P = P := proj_absorb_gen rScr rScr fun i ↦ ⟨i, rfl⟩
  have hsAlg :=
      fused_semigrp_steps (fwdCirc cpAmb).eval.1 czZAmb.eval.1 (Circuit.X qAmb).eval.1 R_refl
      cAmb.eval.1 U_fused.1 P 1 hUf hFCR hRP hXP hUP hFX (by rw [one_mul, mul_one]) hFU hPP
      (one_mul P)
  let mk {A B : Operator (2 ^ n)} {c : Circuit n} (h : c.eval.1 * A = B) : SubspaceStep (Var :=
      Var) A B (.circuit c) := h ▸ subspaceStep_circuit (Var := Var) c A
  exact cleanWorkStep_of_subspaceStep rScr U_fused _ hsAlg.1 (subspaceStep_wrapDyn v cpAmb _ _
      P (U_fused.1 * P) hValid (by rw [hCleanP, hPP]) (by rw [hCleanP, hsAlg.2.2.2.2.2.2.2])
    ((mk hsAlg.2.1).seq ((mk hsAlg.2.2.1).seq ((mk hsAlg.2.2.2.1).seq ((mk hsAlg.2.2.2.2.2.1).seq
        (mk hsAlg.2.2.2.2.2.2.1))))))

attribute [local irreducible] systemQubits_frozen ancWOfScr in
theorem norChainReflProg_validProg_empty {scrW scrL m offRefl n : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hm : offRefl + (m + 1) ≤ scrL)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrW) n)
        (hdisj : rSys.DisjointWires rAnc) :
    let rTot := rSys.concat rAnc hdisj
    let rScr := rAnc.compose (scrSubLGen hp)
    let rLcuAmb : Fin (m + 2) → Wire n := fun i ↦ rTot (rLcuLGen hp i)
    let rClnAmb : Fin (m + 1) → Wire n := fun j ↦ rTot (reflRCleanLGenOff hp hm j)
    (norChainReflProg m rLcuAmb rClnAmb (reflAmb_hIC_31 hp hm rTot) (reflAmb_hCC_31 hp hm rTot)
        (reflAmb_hIn_31 hp rTot)).ValidProg ∅ (Finset.univ.image rScr.wires) := by
  intro rTot rScr rLcuAmb rClnAmb
  let sCln := Finset.univ.image rScr.wires
  refine ⟨finSeqProg_x_validProg (m + 2) sCln rLcuAmb (fun i hmem ↦ by
      rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
      exact lcu_scr_ne_L hp i k (rAnc.wires.injective ((concat_rLcu_apply_fs hp rSys rAnc hdisj
          i).symm.trans hk.symm))), ?_⟩
  rw [finSeqProg_x_finalClean (m + 2) sCln rLcuAmb]
  exact andChainProg_validProg_exact (m + 1) ∅ sCln rLcuAmb rClnAmb (reflAmb_hIC_31 hp hm rTot)
      (reflAmb_hCC_31 hp hm rTot)
    (reflAmb_hIn_31 hp rTot) (fun _ ↦ Finset.notMem_empty _) (fun _ ↦ Finset.notMem_empty _) fun j ↦
        by
      dsimp only [rClnAmb, rTot, reflRCleanLGenOff]
      rw [concat_rScr_apply_fs hp rSys rAnc hdisj ⟨offRefl + j.val, by omega⟩]
      exact Finset.mem_image_of_mem rScr.wires (Finset.mem_univ _)

attribute [local irreducible] systemQubits_frozen ancWOfScr reflULGen pureRotLocalUnitary in
theorem embedUnitary_fusedReflPureRot_val {scrW scrL m n : ℕ} [NeZero (2 ^ n)]
    (hp : scrL + (m + 2) ≤ scrW + 70)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrW) n)
        (hdisj : rSys.DisjointWires rAnc) (c : Circuit 1) :
    let hAnc := hAncCompact scrW
    let rTot := rSys.concat rAnc hdisj
    let qAmb := qspQubitGen hAnc rAnc
    let cAmb : Circuit n := c.onRegister (QRegister.singleton qAmb)
    let R_refl := (rTot.embedUnitary (reflULGen hp)).1
    (rTot.embedUnitary (reflULGen hp * pureRotLocalUnitary hAnc c *
        (Circuit.X (locQGen hAnc)).eval * reflULGen hp * (Circuit.X (locQGen hAnc)).eval)).1 =
      R_refl * cAmb.eval.1 * (Circuit.X qAmb).eval.1 * R_refl * (Circuit.X qAmb).eval.1 := by
  intro hAnc rTot qAmb cAmb R_refl
  have hX_emb : (rTot.embedUnitary (Circuit.X (locQGen hAnc)).eval).1 =
      (Circuit.X qAmb).eval.1 := by
    rw [Circuit.eval_single, ← QRegister.embedUnitary_compose,
        compose_singleton_locQGen hAnc rSys rAnc hdisj, ← Circuit.eval_single]
  have hRot_emb : (rTot.embedUnitary (pureRotLocalUnitary hAnc c)).1 = cAmb.eval.1 :=
      congrArg Subtype.val (embedUnitary_pureRotLocalUnitary hAnc rSys rAnc hdisj c)
  simp only [rTot.embedUnitary_mul, Submonoid.coe_mul, hX_emb, hRot_emb, R_refl]

attribute [local irreducible] systemQubits_frozen ancWOfScr reflULGen pureRotLocalUnitary
    fwdCirc wrapDyn norChainReflProg czGateCircuit in
theorem fusedReflPureRotDyn_clean {scrW scrL m offRefl : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (_hOff65 : 65 ≤ offRefl) (hm : offRefl + (m + 1) ≤ scrL)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrW) n)
        (hdisj : rSys.DisjointWires rAnc) (c : Circuit 1) :
    CleanWorkStep (rAnc.compose (scrSubLGen hp))
      ((rSys.concat rAnc hdisj).embedUnitary (reflULGen hp *
          pureRotLocalUnitary (hAncCompact scrW) c *
          (Circuit.X (locQGen (hAncCompact scrW))).eval * reflULGen hp *
          (Circuit.X (locQGen (hAncCompact scrW))).eval))
      (fusedReflPureRotDyn hp hm v rSys rAnc hdisj c) := by
  have _ := ancWOfScr_eq_fs scrW
  let rTot := rSys.concat rAnc hdisj
  let rScr := rAnc.compose (scrSubLGen hp)
  let qAmb := qspQubitGen (hAncCompact scrW) rAnc
  let cpAmb :=
      norChainReflProg m (fun i ↦ rTot (rLcuLGen hp i)) (fun j ↦ rTot (reflRCleanLGenOff hp hm j))
    (reflAmb_hIC_31 hp hm rTot) (reflAmb_hCC_31 hp hm rTot) (reflAmb_hIn_31 hp rTot)
  let q1 := QRegister.singleton qAmb
  have hqEq : qAmb = rTot (locQCompactGen scrW) :=
    (concat_locAnc_apply_fs rSys rAnc hdisj ⟨ancWOfScr scrW - 1, _⟩).symm.trans
      (congrArg rTot
          (Fin.ext
          (by simp only [locQCompactGen, locAncCompactGen, QRegister.block_apply_val]; omega)))
  have hNotQ {u} : rTot u ∈ Set.range q1.wires → locQCompactGen scrW = u := fun ⟨k, hk⟩ ↦
    rTot.wires.injective (hqEq.symm.trans ((congrArg q1.wires (Fin.eq_zero k)).symm.trans hk))
  have hCommScr (M : Operator (2 ^ 1)) : q1.embedMatrix M * rScr.basisOutcomeProjector 0 =
      rScr.basisOutcomeProjector 0 * q1.embedMatrix M := q1.embedMatrix_comm_of_disjoint rScr
    (QRegister.disjoint_iff.mpr (Fin.forall_fin_one.mpr fun j e ↦
      (scr_idx_L hp j).2 (congrArg Fin.val (rAnc.wires.injective e)).symm)) M _
  have hCommFwd (M : Operator (2 ^ 1)) : q1.embedMatrix M * (fwdCirc cpAmb).eval.1 =
      (fwdCirc cpAmb).eval.1 * q1.embedMatrix M :=
    (comm_circWires_embedMatrix_fs q1 M (circWires_fwdCirc_of_cpWires_fs
      (cpWires_norChainReflProg_fs (fun i h ↦ locQ_ne_rLcuLGen hp i (hNotQ h))
        (fun j h ↦ locQ_ne_reflRCleanLGenOff hp hm j (hNotQ h))))).symm
  unfold fusedReflPureRotDyn pureRotDyn
  exact cleanWorkStep_wrapDyn_fused_circuit5 v cpAmb rScr qAmb _ (c.onRegister q1)
      (rTot.embedUnitary (reflULGen hp)).1 _
    (norChainReflProg_validProg_empty hp hm rSys rAnc hdisj)
        (embedUnitary_fusedReflPureRot_val hp rSys rAnc hdisj c)
    (czZAmb_mul_fwd_clean_eq_fs hp hm rSys rAnc hdisj qAmb hqEq _)
        (fastReflCircLGenOff_clean_and_count hp hm v rSys rAnc hdisj).1.1
    (by simpa only [Circuit.eval_single, QRegister.embedUnitary_val] using hCommScr _)
    (by simpa only [Circuit.eval_onRegister, QRegister.embedUnitary_val] using hCommScr _)
    (by simpa only [Circuit.eval_single, QRegister.embedUnitary_val] using hCommFwd _)
    (by simpa only [Circuit.eval_onRegister, QRegister.embedUnitary_val] using hCommFwd _)

theorem hSlice26_5 {ancW : ℕ} (hAnc : 100 ≤ ancW) : 26 + 5 ≤ ancW := by omega

/-- Active `5`-wire low phase-gradient slice `rAnc.slice 26 5` (`ancIdx 26..30`). -/
abbrev gradReg5LoGen {ancW n : ℕ} (hAnc : 100 ≤ ancW) (rAnc : QRegister ancW n) : QRegister 5 n :=
    rAnc.slice 26 5 (hSlice26_5 hAnc)

/-- Local `5`-wire low phase-gradient slice inside `systemQubits + ancW`. -/
abbrev locGrad5LoGen {ancW : ℕ} (hAnc : 100 ≤ ancW) : QRegister 5 (systemQubits_frozen + ancW) :=
    gradReg5LoGen hAnc (locAncGen ancW)
theorem hSlice8_0_5 : 0 + 5 ≤ 8 := by omega
theorem hSlice8_5_3 : 5 + 3 ≤ 8 := by omega
theorem locCat8SharedGen_slice_0_5 {ancW : ℕ} (hAnc : 100 ≤ ancW) :
    (locCat8SharedGen hAnc).slice 0 5 hSlice8_0_5 = locGrad5LoGen hAnc :=
  congrArg QRegister.mk <| Function.Embedding.ext fun i ↦ Fin.ext (by
    change systemQubits_frozen + (0 + (26 + (0 + i.val))) = systemQubits_frozen + (26 + i.val)
    omega)
theorem locCat8SharedGen_slice_5_3 {ancW : ℕ} (hAnc : 100 ≤ ancW) :
    (locCat8SharedGen hAnc).slice 5 3 hSlice8_5_3 = locGrad3HiGen hAnc :=
  congrArg QRegister.mk <| Function.Embedding.ext fun i ↦ Fin.ext (by
    change systemQubits_frozen + (0 + (26 + (5 + i.val))) = systemQubits_frozen + (31 + i.val)
    omega)

theorem count_foldFinDyn_le {Var : Type} {n m arity : ℕ} {g : PrimitiveGate arity} (c : ℕ)
    (body : Fin m → DynamicCircuit Var n) (h : ∀ i, (body i).count g ≤ c) :
    (foldFinDyn body).count g ≤ m * c := by
  induction m with
  | zero => simp [foldFinDyn, DynamicCircuit.identity]
  | succ m ih =>
    rw [Nat.add_one_mul]
    exact Nat.add_le_add (ih _ fun i ↦ h i.castSucc) (h (Fin.last m))

end

end QuantumComputation.Specs.PhotochemistrySolution.RieszQspCovering

end
