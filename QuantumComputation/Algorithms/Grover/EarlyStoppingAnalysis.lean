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

public import QuantumComputation.Algorithms.Grover.EarlyStopping
import Mathlib.Analysis.Real.Pi.Bounds
import QuantumComputation.Maths.Trigonometry

/-!
# Expected oracle calls of early-stopping Grover

Early-stopping Grover (`earlyStoppingGrover`) with `K` iterations per attempt makes exactly
`K / p_succ K d` oracle calls in expectation per unit of input mass
(`expectedCost_earlyStoppingGrover_oracleCalls`). This file bounds this cost when each attempt
stops at a target phase `φ`, i.e. for `K = earlyStoppingIterations φ d ≈ φ / (2 arcsin (1 / √d))`.

* `retryOracleCalls_earlyStoppingIterations_le`: if the final phase stays below `π / 2`, then
  `K / p_succ K d ≤ (φ / 2 · √d + 1 / 2) / sin² φ`.

* `retryOracleCalls_earlyStoppingIterations_seven_sixths_le`: for `d ≥ 2 ^ 5`,
  `K / p_succ K d ≤ 0.691 √d + 0.6` at phase `7 / 6`.

Motivation for `7 / 6` (heuristic, not formalised here): for final phase `φ`,
`K / p_succ K d ≈ √d · φ / (2 sin² φ)`, which is minimised at `tan φ = 2 φ`, `φ ≈ 1.1656`, giving
`≈ 0.69 √d` expected oracle calls against `≈ (π / 4) √d ≈ 0.785 √d` for the standard count
`⌊π / (4 arcsin (1 / √d))⌋`. This matches Zalka's optimal `≈ 0.69 √N` expected queries
(Zalka, *Grover's quantum searching algorithm is optimal*, 1999).

## Main result

* `expectedCost_earlyStoppingGrover_oracleCalls_le`: for `d ≥ 2 ^ 5`, early-stopping Grover with
  phase `7 / 6` makes at most `0.691 √d + 0.6` expected oracle calls per unit of input mass.
-/
@[expose] public section

open ResourceCounting Real
open scoped NNReal

namespace Grover

variable {Var : Type} [DecidableEq Var] {n : ℕ}

local notation "d" => (2 ^ n : ℕ)

/-- The iteration count stopping at phase `φ`: the nearest integer `K` to
`φ / (2 arcsin (1 / √dim))`, so that the final phase `(2K + 1) arcsin (1 / √dim)` is about `φ`. -/
noncomputable def earlyStoppingIterations (φ : ℝ) (dim : ℕ) : ℕ :=
  Int.toNat (round (φ / (2 * arcsin (1 / √dim))))

/-- Expected oracle calls `K / p_succ K dim` of retrying `K`-iteration Grover attempts until one
succeeds (`expectedCost_earlyStoppingGrover_oracleCalls`). -/
noncomputable abbrev retryOracleCalls (K dim : ℕ) : ℝ :=
  K / p_succ K dim

/-- Stopping at phase `0 < φ` makes at most `(φ / 2 · √dim + 1 / 2) / sin² φ` expected oracle
calls, provided the final phase, at most `φ + 2 arcsin (1 / √dim)`, does not pass `π / 2`. -/
theorem retryOracleCalls_earlyStoppingIterations_le {φ : ℝ} {dim : ℕ} (hφ : 0 < φ)
    (hdim : 1 ≤ dim) (hphase : φ + 2 * arcsin (1 / √dim) ≤ π / 2) :
    retryOracleCalls (earlyStoppingIterations φ dim) dim ≤ (φ / 2 * √dim + 1 / 2) / sin φ ^ 2 := by
  have hdim' : (1 : ℝ) ≤ dim := by exact_mod_cast hdim
  have ha : 0 < arcsin (1 / √dim) := arcsin_pos.2 (by positivity)
  obtain ⟨h0, h1⟩ := odd_round_div_sub_mem_Icc ha hφ.le
  rw [← earlyStoppingIterations] at h0 h1
  have hsinφ : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ (by linarith [pi_pos])
  have hsin : sin φ ≤ sin ((2 * (earlyStoppingIterations φ dim : ℝ) + 1) * arcsin (1 / √dim)) :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith) (by linarith)
  have hp : sin φ ^ 2 ≤ p_succ (earlyStoppingIterations φ dim) dim := by
    rw [p_succ_eq_sin_sq]
    exact pow_le_pow_left₀ hsinφ.le hsin 2
  exact div_le_div₀ (by positivity) (toNat_round_div_two_mul_arcsin_inv_sqrt_le hφ.le hdim')
    (pow_pos hsinφ 2) hp

/-- For `d ≥ 2 ^ 5`, stopping at phase `7 / 6` makes at most `0.691 √d + 0.6` expected oracle
calls, using `sin (7 / 6) ≥ 0.919377`. -/
theorem retryOracleCalls_earlyStoppingIterations_seven_sixths_le (hd : 32 ≤ d) :
    retryOracleCalls (earlyStoppingIterations (7 / 6) d) d ≤ 691 / 1000 * √d + 6 / 10 := by
  have hd' : (32 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : arcsin (1 / √d) ≤ 9 / 50 :=
    arcsin_one_div_sqrt_le (by positivity) (by norm_num) (by norm_num) (by nlinarith)
  have hsin : 919377 / 1000000 ≤ sin (7 / 6) :=
    le_trans (by norm_num) (sin_ge_of_pi_div_two_sub_le (δ := 31415927 / 20000000 - 7 / 6)
      (by linarith [pi_gt_three]) (by linarith [pi_lt_d20]) (by norm_num))
  have hsin2 := pow_le_pow_left₀ (by norm_num) hsin 2
  refine (retryOracleCalls_earlyStoppingIterations_le (by norm_num)
    (by exact_mod_cast Nat.one_le_two_pow) (by linarith [pi_gt_d2])).trans ?_
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hsin2)]
  have hmul := mul_le_mul_of_nonneg_left hsin2
    (by positivity : (0 : ℝ) ≤ 691 / 1000 * √d + 6 / 10)
  nlinarith [sqrt_nonneg (d : ℝ)]

/-! ## Main result -/

/-- For `d ≥ 2 ^ 5`, early-stopping Grover with phase `7 / 6` makes at most `0.691 √d + 0.6`
expected oracle calls per unit of input mass. -/
theorem expectedCost_earlyStoppingGrover_oracleCalls_le (k res : Var) (target : Fin d)
    (hd : 32 ≤ d) (Δ : CQState (Store Var) d) :
    expectedCost (oracleCalls (oracleUnitary target))
        (earlyStoppingGrover k res (earlyStoppingIterations (7 / 6) d) target) Δ ≤
      Δ.trace * ENNReal.ofReal (691 / 1000 * √d + 6 / 10) := by
  set K := earlyStoppingIterations (7 / 6) d
  have hcalls : (K : ENNReal) / ENNReal.ofReal (p_succ K d) =
      ENNReal.ofReal (retryOracleCalls K d) := by
    rw [ENNReal.ofReal_div_of_pos (p_succ_pos K), ENNReal.ofReal_natCast]
  rw [expectedCost_earlyStoppingGrover_oracleCalls, mul_div_assoc, hcalls]
  gcongr
  exact retryOracleCalls_earlyStoppingIterations_seven_sixths_le hd

end Grover
