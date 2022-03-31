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

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Order.Lex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Power-Law Cost Metric

Defines `PowerLawCost`, an interface for power-law bounds $c \cdot N^a$ (`a, c : ℚ≥0`) with
(ideally) effective constants, canonical zero representation `valid : c = 0 → a = 0`, lexicographic
`LinearOrder` (`ℚ≥0 ×ₗ ℚ≥0`), and equivalence to eventual order on `eval` as $N \to \infty$.
-/

@[expose] public section

namespace ResourceCounting

open scoped NNRat
open Filter

/-- Power-law cost $c \cdot N^a$ with non-negative rational exponent `a` and leading
constant `c`, ordered lexicographically on `(a, c)`. -/
structure PowerLawCost where
  /-- Non-negative rational power-law exponent $a$. -/
  a : ℚ≥0
  /-- Non-negative rational leading multiplicative constant $c$. -/
  c : ℚ≥0
  /-- Canonical representation of the zero cost (`c = 0` forces `a = 0`). -/
  valid : c = 0 → a = 0
  deriving DecidableEq

namespace PowerLawCost

/-- Evaluate $c \cdot N^a$ on a real problem size $N$. -/
noncomputable def eval (m : PowerLawCost) (N : ℝ) : ℝ :=
  (m.c : ℝ) * N ^ (m.a : ℝ)

/-- Embed `PowerLawCost` into `ℚ≥0 ×ₗ ℚ≥0` as `(a, c)`. -/
def toLexProd (m : PowerLawCost) : ℚ≥0 ×ₗ ℚ≥0 :=
  toLex (m.a, m.c)

theorem toLexProd_injective : Function.Injective toLexProd := by
  rintro ⟨a₁, c₁, _⟩ ⟨a₂, c₂, _⟩ h
  cases h
  rfl

instance : LinearOrder PowerLawCost :=
  LinearOrder.lift' toLexProd toLexProd_injective

/-- If `m₁ < m₂`, then `m₁.eval N < m₂.eval N` for all sufficiently large `N`. -/
theorem eventually_eval_lt_of_lt {m₁ m₂ : PowerLawCost} (h : m₁ < m₂) :
    ∀ᶠ N in atTop, m₁.eval N < m₂.eval N := by
  change toLexProd m₁ < toLexProd m₂ at h
  rw [Prod.Lex.lt_iff] at h
  rcases h with ha | ⟨ha, hc⟩
  · change m₁.a < m₂.a at ha
    have hc₂ : 0 < m₂.c := pos_iff_ne_zero.mpr fun h0 ↦
      (not_lt_of_ge zero_le (m₂.valid h0 ▸ ha)).elim
    have hdiff : (0 : ℝ) < (m₂.a : ℝ) - (m₁.a : ℝ) := sub_pos.mpr (by exact_mod_cast ha)
    have hc₂' : (0 : ℝ) < m₂.c := by exact_mod_cast hc₂
    filter_upwards [(tendsto_rpow_atTop hdiff).eventually_gt_atTop ((m₁.c : ℝ) / (m₂.c : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with N hN hN0
    have hmul := mul_lt_mul_of_pos_right ((div_lt_iff₀ hc₂').mp hN)
      (Real.rpow_pos_of_pos hN0 (m₁.a : ℝ))
    simpa only [eval, mul_comm (N ^ ((m₂.a : ℝ) - (m₁.a : ℝ))), mul_assoc,
      ← Real.rpow_add hN0, add_sub_cancel] using hmul
  · change m₁.a = m₂.a at ha
    change m₁.c < m₂.c at hc
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN0
    simp only [eval, ha]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hc) (Real.rpow_pos_of_pos hN0 _)

/-- `m₁ < m₂` holds if and only if `m₁.eval N < m₂.eval N` eventually as `N → ∞`. -/
theorem lt_iff_eventually_eval_lt {m₁ m₂ : PowerLawCost} :
    m₁ < m₂ ↔ ∀ᶠ N in atTop, m₁.eval N < m₂.eval N := by
  refine ⟨eventually_eval_lt_of_lt, fun h ↦ ?_⟩
  rcases lt_trichotomy m₁ m₂ with hlt | rfl | hgt
  · exact hlt
  · obtain ⟨N, hN⟩ := h.exists
    exact (lt_irrefl _ hN).elim
  · obtain ⟨N, h₁, h₂⟩ := (h.and (eventually_eval_lt_of_lt hgt)).exists
    exact (lt_asymm h₁ h₂).elim

/-- If `m₁ ≤ m₂`, then `m₁.eval N ≤ m₂.eval N` for all sufficiently large `N`. -/
@[gcongr]
theorem eventually_eval_le_of_le {m₁ m₂ : PowerLawCost} (h : m₁ ≤ m₂) :
    m₁.eval ≤ᶠ[atTop] m₂.eval := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact (eventually_eval_lt_of_lt hlt).mono fun _ ↦ le_of_lt
  · exact Eventually.of_forall fun _ ↦ le_rfl

/-- `m₁ ≤ m₂` holds if and only if `m₁.eval N ≤ m₂.eval N` eventually as `N → ∞`. -/
theorem le_iff_eventually_eval_le {m₁ m₂ : PowerLawCost} :
    m₁ ≤ m₂ ↔ m₁.eval ≤ᶠ[atTop] m₂.eval := by
  refine ⟨eventually_eval_le_of_le, fun h ↦ le_of_not_gt fun hgt ↦ ?_⟩
  obtain ⟨N, hle, hlt⟩ := (h.and (eventually_eval_lt_of_lt hgt)).exists
  exact not_lt_of_ge hle hlt

end PowerLawCost

end ResourceCounting
