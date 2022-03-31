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

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Elementary trigonometric bounds

Bounds on `arcsin (1 / √c)`, a lower bound on `sin φ` near `π / 2`, and bounds on the phase
reached by the nearest odd multiple, used to evaluate Grover-type success probabilities.
-/

@[expose] public section

open Real

/-- For `0 ≤ x ≤ 1`, `x ≤ arcsin x`. -/
theorem self_le_arcsin {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ arcsin x :=
  (le_arcsin_iff_sin_le' ⟨by linarith [pi_pos], hx1.trans (by linarith [pi_gt_three])⟩).2
    (sin_le hx)

/-- `arcsin (1 / √c) ≤ u` whenever `1 ≤ c * (u - u ^ 3 / 6) ^ 2`, using `u - u ^ 3 / 6 < sin u`. -/
theorem arcsin_one_div_sqrt_le {c u : ℝ} (hc : 0 < c) (hu : 0 < u) (hu1 : u ≤ 1)
    (h : 1 ≤ c * (u - u ^ 3 / 6) ^ 2) : arcsin (1 / √c) ≤ u := by
  have hroot : 0 < √c := sqrt_pos.2 hc
  have hcube : u ^ 3 ≤ u := by nlinarith [pow_le_pow_left₀ hu.le hu1 2]
  have hsin := sin_gt_sub_cube hu
  have hx : 1 / √c ≤ u - u ^ 3 / 6 := by
    rw [div_le_iff₀ hroot]
    nlinarith [sq_sqrt hc.le, mul_pos (show 0 < u - u ^ 3 / 6 by linarith) hroot]
  rw [arcsin_le_iff_le_sin ⟨by linarith [one_div_pos.2 hroot], by linarith [sin_le_one u]⟩
    ⟨by linarith [pi_gt_three], by linarith [pi_gt_three]⟩]
  linarith

/-- Double-angle step: a lower bound `0 ≤ c ≤ cos (x / 2)` gives `2 c ^ 2 - 1 ≤ cos x`. -/
theorem two_mul_sq_sub_one_le_cos {x c : ℝ} (hc : 0 ≤ c) (h : c ≤ cos (x / 2)) :
    2 * c ^ 2 - 1 ≤ cos x := by
  have hdouble := cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hdouble
  nlinarith [pow_le_pow_left₀ hc h 2]

/-- `sin φ ≥ 2 (2 (1 - δ ^ 2 / 32) ^ 2 - 1) ^ 2 - 1` whenever `0 ≤ π / 2 - φ ≤ δ ≤ 2`: the bound
`cos x ≥ 1 - x ^ 2 / 2` at `x = δ / 4`, followed by two double-angle steps. -/
theorem sin_ge_of_pi_div_two_sub_le {φ δ : ℝ} (hφ : 0 ≤ π / 2 - φ) (hδ : π / 2 - φ ≤ δ)
    (hδ2 : δ ≤ 2) : 2 * (2 * (1 - δ ^ 2 / 32) ^ 2 - 1) ^ 2 - 1 ≤ sin φ := by
  have hδ0 : 0 ≤ δ := hφ.trans hδ
  have hc : 7 / 8 ≤ 1 - δ ^ 2 / 32 := by nlinarith
  have hquarter : 1 - δ ^ 2 / 32 ≤ cos (δ / 2 / 2) := by
    have := one_sub_sq_div_two_le_cos (x := δ / 2 / 2)
    linarith [show (δ / 2 / 2) ^ 2 / 2 = δ ^ 2 / 32 by ring]
  have hhalf := two_mul_sq_sub_one_le_cos (by linarith) hquarter
  have hfull := two_mul_sq_sub_one_le_cos (by nlinarith) hhalf
  have hcos := cos_le_cos_of_nonneg_of_le_pi hφ (by linarith [pi_gt_three]) hδ
  rw [cos_pi_div_two_sub] at hcos
  exact hfull.trans hcos

/-- For `0 ≤ r`, `((round r).toNat : ℝ) ≤ r + 1 / 2`. -/
theorem toNat_round_le_add_half {r : ℝ} (hr : 0 ≤ r) : ((round r).toNat : ℝ) ≤ r + 1 / 2 := by
  have : ((round r).toNat : ℝ) = (round r : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg (by rw [round_eq]; positivity)
  linarith [round_le_add_half r]

/-- For `K = (round (b / (2 a))).toNat`, the phase error `(2 K + 1) a - b` lies in `[0, 2 a]`. -/
theorem odd_round_div_sub_mem_Icc {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ (2 * ((round (b / (2 * a))).toNat : ℝ) + 1) * a - b ∧
      (2 * ((round (b / (2 * a))).toNat : ℝ) + 1) * a - b ≤ 2 * a := by
  set r := b / (2 * a)
  have hK : ((round r).toNat : ℝ) = (round r : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg (by rw [round_eq]; positivity)
  have hrdef : r * (2 * a) = b := div_mul_cancel₀ _ (by positivity)
  rw [hK]
  exact ⟨by nlinarith [sub_half_lt_round r], by nlinarith [round_le_add_half r]⟩

/-- For `1 ≤ c` and `0 ≤ b`,
`((round (b / (2 * arcsin (1 / √c)))).toNat : ℝ) ≤ b / 2 * √c + 1 / 2`. -/
theorem toNat_round_div_two_mul_arcsin_inv_sqrt_le {b c : ℝ} (hb : 0 ≤ b) (hc : 1 ≤ c) :
    ((round (b / (2 * arcsin (1 / √c)))).toNat : ℝ) ≤ b / 2 * √c + 1 / 2 := by
  have hroot : 0 < √c := sqrt_pos.2 (by linarith)
  have hapos : 0 < arcsin (1 / √c) := arcsin_pos.2 (by positivity)
  have hle : b / (2 * arcsin (1 / √c)) ≤ b / 2 * √c :=
    calc b / (2 * arcsin (1 / √c))
        ≤ b / (2 * (1 / √c)) := by
          gcongr
          exact self_le_arcsin (by positivity) ((div_le_one hroot).2 (one_le_sqrt.2 hc))
      _ = b / 2 * √c := by rw [mul_one_div, div_div_eq_mul_div]; ring
  linarith [toNat_round_le_add_half (by positivity : 0 ≤ b / (2 * arcsin (1 / √c)))]
