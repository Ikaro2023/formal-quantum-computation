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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MergedVepCoreSlice
set_option linter.style.longLine false


@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section TwoAngleBiGqspVerifierBridge_aux_p1
local instance (priority := 1000000) instNeZeroTwoPow_TwoAngleBiGqspVerifierBridge_aux_p1 (k :
  ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

namespace TwoAngleBiGqspVerifierBridge

section ConfigTwoAngleBiGqspVerifierBridge

local instance (priority :=
  1000000) instLoc_TwoAngleBiGqspVerifierBridge_aux_1InstNeZero (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

section ConfigSec1_TwoAngleSymbolicCore
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256

open Real Operator Matrix Circuit TFreeLaurentGQSP
open CatalyzedLaurentGQSP TFreeLaurentGQSPPresets
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge
open scoped Matrix Matrix.Norms.L2Operator BigOperators

theorem biGqspTwoAngleRunLoop_support (M : ℕ) (ab : ℕ → ℂ × ℂ) (t : ℕ) (ht : t ≤ M) :
    ∀ i : Fin (2 * (M + 1) + 1), (i.val < (M + 1) - t ∨ (M + 2) + t < i.val) →
      (biGqspTwoAngleRunLoop M ab t).1 i = 0 ∧ (biGqspTwoAngleRunLoop M ab t).2 i = 0 := by
  have hstep : ∀ a b (pq : (Fin (2 * (M + 1) + 1) → ℂ) × (Fin (2 * (M + 1) + 1) → ℂ)) i,
      pq.1 i = 0 → pq.2 i = 0 →
      (gqspSu2Step (M + 1) a b pq).1 i = 0 ∧ (gqspSu2Step (M + 1) a b pq).2 i = 0 :=
    fun _ _ _ _ hp hq ↦ by dsimp only [gqspSu2Step]; rw [hp, hq]; exact ⟨by ring, by ring⟩
  induction t with
  | zero =>
    intro i hi
    exact hstep _ _ _ _ (by simp [biGqspTwoAnglePreInit, show i.val ≠ M + 1 by omega])
      (by simp [biGqspTwoAnglePreInit, show i.val ≠ M + 2 by omega])
  | succ t ih =>
    intro i hi
    dsimp only [biGqspTwoAngleRunLoop, biGqspTwoAngleStep]
    refine hstep _ _ _ _ ?_ ?_
    · dsimp only [shiftRightC]
      split_ifs with hz
      · rfl
      · exact (ih (by omega) ⟨i.val - 1, by omega⟩ (by dsimp only; omega)).1
    · dsimp only [shiftLeftC]
      split_ifs with hlt
      · exact (ih (by omega) ⟨i.val + 1, by omega⟩ (by dsimp only; omega)).2
      · rfl

end ConfigSec1_TwoAngleSymbolicCore

section ConfigSec2_TwoAngleGateTaylorBridge
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 2048

open Real Operator Matrix Circuit
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open TFreeLaurentGQSPPresets.FastRecurrenceVerifier (smToInt)

structure DyadicSu2Gate where
  mar : ℕ
  mai : ℕ
  mbr : ℕ
  mbi : ℕ
  sar : Bool
  sai : Bool
  sbr : Bool
  sbi : Bool

/-- Zero `DyadicSu2Gate` fallback for `List.getD`. -/
def defaultSu2Gate : DyadicSu2Gate := ⟨0, 0, 0, 0, false, false, false, false⟩

/-- Real part of `a` for a `2 ^ b`-scaled `DyadicSu2Gate`. -/
noncomputable def gateSu2ARe (b : ℕ) (g : DyadicSu2Gate) : ℝ :=
  (smToInt g.sar g.mar : ℝ) / (2 ^ b : ℝ)

/-- Imaginary part of `a` for a `2 ^ b`-scaled `DyadicSu2Gate`. -/
noncomputable def gateSu2AIm (b : ℕ) (g : DyadicSu2Gate) : ℝ :=
  (smToInt g.sai g.mai : ℝ) / (2 ^ b : ℝ)

/-- Real part of `b` for a `2 ^ b`-scaled `DyadicSu2Gate`. -/
noncomputable def gateSu2BRe (b : ℕ) (g : DyadicSu2Gate) : ℝ :=
  (smToInt g.sbr g.mbr : ℝ) / (2 ^ b : ℝ)

/-- Imaginary part of `b` for a `2 ^ b`-scaled `DyadicSu2Gate`. -/
noncomputable def gateSu2BIm (b : ℕ) (g : DyadicSu2Gate) : ℝ :=
  (smToInt g.sbi g.mbi : ℝ) / (2 ^ b : ℝ)

/-- Complex `(a, b)` pair for a `2 ^ b`-scaled `DyadicSu2Gate`. -/
noncomputable def gateSu2Pair (b : ℕ) (g : DyadicSu2Gate) : ℂ × ℂ :=
  (((gateSu2ARe b g : ℂ) + Complex.I * (gateSu2AIm b g : ℂ)),
   ((gateSu2BRe b g : ℂ) + Complex.I * (gateSu2BIm b g : ℂ)))

set_option exponentiation.threshold 256
end ConfigSec2_TwoAngleGateTaylorBridge

section ConfigSec3A_TwoAngleTree768
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 2048

open scoped BigOperators
open Real
open TFreeLaurentGQSPPresets.FastRecurrenceVerifier (smToInt)

/-- Zero real coefficient sequence. -/
def ta_polyZero : ℕ → ℝ := fun _ ↦ 0

/-- Constant-`1` real coefficient sequence (`1` at `m = 0`, `0` elsewhere). -/
def ta_polyOne : ℕ → ℝ := fun m ↦ if m = 0 then 1 else 0

/-- Pointwise addition of real coefficient sequences. -/
def ta_polyAdd (f g : ℕ → ℝ) : ℕ → ℝ := fun m ↦ f m + g m

/-- Pointwise subtraction of real coefficient sequences. -/
def ta_polySub (f g : ℕ → ℝ) : ℕ → ℝ := fun m ↦ f m - g m

/-- Pointwise negation of a real coefficient sequence. -/
def ta_polyNeg (f : ℕ → ℝ) : ℕ → ℝ := fun m ↦ -f m

/-- Degree-`L` reversal `m ↦ f (L - m)` (for `m ≤ L`, else `0`) on real coefficient sequences. -/
def ta_polyRev (L : ℕ) (f : ℕ → ℝ) : ℕ → ℝ := fun m ↦ if m ≤ L then f (L - m) else 0

/-- Cauchy convolution of two real coefficient sequences. -/
def ta_polyConv (f g : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i ∈ Finset.range (m + 1), f i * g (m - i)

/-- Support predicate `∀ m > L, f m = 0` on real coefficient sequences. -/
def ta_PolySupp (L : ℕ) (f : ℕ → ℝ) : Prop := ∀ m, L < m → f m = 0

theorem ta_polyConv_succ_left (f g : ℕ → ℝ) (m : ℕ) : ta_polyConv f g (m + 1) = ta_polyConv
    (fun k ↦ f (k + 1)) g m + f 0 * g (m + 1) := by
  unfold ta_polyConv
  rw [Finset.sum_range_succ' (fun i ↦ f i * g (m + 1 - i)) (m + 1), Nat.sub_zero]
  exact congrArg (· + _) (Finset.sum_congr rfl fun i _ ↦ by rw [Nat.succ_sub_succ_eq_sub])

theorem ta_polyConv_comm (f g : ℕ → ℝ) : ta_polyConv f g = ta_polyConv g f := funext fun m ↦
  Finset.sum_bij (fun i _ ↦ m - i)
    (fun _ hi ↦ Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega))
    (fun _ h1 _ h2 _ ↦ by have := Finset.mem_range.mp h1; have := Finset.mem_range.mp h2; omega)
    (fun j hj ↦ ⟨m - j, Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega),
      by have := Finset.mem_range.mp hj; omega⟩)
    (fun i hi ↦ by rw [show m - (m - i) = i by have := Finset.mem_range.mp hi; omega, mul_comm])

theorem ta_polyConv_supp {L1 L2 : ℕ} {f g : ℕ → ℝ} (hf : ta_PolySupp L1 f)
    (hg : ta_PolySupp L2 g) : ta_PolySupp (L1 + L2) (ta_polyConv f g) := fun m hm ↦
  Finset.sum_eq_zero fun i _ ↦ by
    by_cases hi : L1 < i
    · rw [hf i hi, zero_mul]
    · rw [hg (m - i) (by omega), mul_zero]

theorem ta_polyConv_bilinear_err {LU LV : ℕ} {u_hat u v_hat v : ℕ → ℝ} {BU BV EU EV : ℝ}
    (hBU : 0 ≤ BU) (hBV : 0 ≤ BV) (hEU : 0 ≤ EU) (hEV : 0 ≤ EV)
    (hu_hat_s : ta_PolySupp LU u_hat) (hu_s : ta_PolySupp LU u)
    (hv_hat_s : ta_PolySupp LV v_hat) (hv_s : ta_PolySupp LV v)
    (hu_bnd : ∀ i, |u_hat i| ≤ BU) (hv_bnd : ∀ j, |v j| ≤ BV)
    (hu_err : ∀ i, |u_hat i - u i| ≤ EU) (hv_err : ∀ j, |v_hat j - v j| ≤ EV) (m : ℕ) :
    |ta_polyConv u_hat v_hat m - ta_polyConv u v m| ≤
      ((min LU LV + 1 : ℕ) : ℝ) * (BU * EV + BV * EU) := by
  have hl : ∀ {L : ℕ} {uh u0 vh v0 : ℕ → ℝ} {Bu Bv Eu Ev : ℝ},
      0 ≤ Bu → 0 ≤ Bv → 0 ≤ Eu → 0 ≤ Ev → ta_PolySupp L uh → ta_PolySupp L u0 →
      (∀ i, |uh i| ≤ Bu) → (∀ j, |v0 j| ≤ Bv) →
      (∀ i, |uh i - u0 i| ≤ Eu) → (∀ j, |vh j - v0 j| ≤ Ev) →
      |ta_polyConv uh vh m - ta_polyConv u0 v0 m| ≤ ((L + 1 : ℕ) : ℝ) * (Bu * Ev + Bv * Eu) :=
    fun {L uh u0 vh v0 Bu Bv Eu Ev} hBu hBv hEu hEv huh hu0 hub hvb hue hve ↦ by
      unfold ta_polyConv
      rw [← Finset.sum_sub_distrib, ← Finset.sum_subset
          (Finset.range_mono (Nat.min_le_left (m + 1) (L + 1))) (fun i hi₂ hi₁ ↦ by
            simp only [Finset.mem_range] at hi₂ hi₁
            rw [huh i (by omega), hu0 i (by omega)]
            ring)]
      have hterm (i : ℕ) : |uh i * vh (m - i) - u0 i * v0 (m - i)| ≤ Bu * Ev + Bv * Eu := by
        rw [show uh i * vh (m - i) - u0 i * v0 (m - i) =
            uh i * (vh (m - i) - v0 (m - i)) + v0 (m - i) * (uh i - u0 i) by ring]
        exact (abs_add_le _ _).trans (by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (hub i) (hve _) (abs_nonneg _) hBu)
            (mul_le_mul (hvb _) (hue i) (abs_nonneg _) hBv))
      refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ hterm i)).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.min_le_right (m + 1) (L + 1)) (by positivity)
  by_cases hle : LU ≤ LV
  · rw [Nat.min_eq_left hle]
    exact hl hBU hBV hEU hEV hu_hat_s hu_s hu_bnd hv_bnd hu_err hv_err
  · rw [Nat.min_eq_right (by omega), ta_polyConv_comm u_hat v_hat, ta_polyConv_comm u v,
        abs_sub_comm, add_comm (BU * EV)]
    exact hl hBV hBU hEV hEU hv_s hv_hat_s hv_bnd hu_bnd
      (fun j ↦ abs_sub_comm (v_hat j) (v j) ▸ hv_err j)
      (fun i ↦ abs_sub_comm (u_hat i) (u i) ▸ hu_err i)

/-- Split real/imaginary polynomial `(re, im : ℕ → ℝ)` in `Y = X ^ 2`. -/
@[ext] structure PolyC where
  re : ℕ → ℝ
  im : ℕ → ℝ

/-- Evaluates `P : PolyC` at degree index `m` as `P.re m + I * P.im m : ℂ`. -/
noncomputable def PolyC.toC (P : PolyC) (m : ℕ) : ℂ := (P.re m : ℂ) + Complex.I * (P.im m : ℂ)

@[local simp] theorem PolyC.toC_re (P : PolyC) (m : ℕ) : (P.toC m).re = P.re m := by
  simp [PolyC.toC]

@[local simp] theorem PolyC.toC_im (P : PolyC) (m : ℕ) : (P.toC m).im = P.im m := by
  simp [PolyC.toC]

theorem PolyC.ext_toC {P Q : PolyC} (h : ∀ m, P.toC m = Q.toC m) : P = Q := by
  ext m
  · simpa using congrArg Complex.re (h m)
  · simpa using congrArg Complex.im (h m)

/-- Builds a `PolyC` from a complex coefficient sequence `ℕ → ℂ`. -/
noncomputable def PolyC.ofC (f : ℕ → ℂ) : PolyC where
  re := fun m ↦ (f m).re
  im := fun m ↦ (f m).im

@[local simp] theorem PolyC.ofC_toC (f : ℕ → ℂ) (m : ℕ) : (PolyC.ofC f).toC m = f m := by
  simp [PolyC.ofC, PolyC.toC, mul_comm Complex.I]

/-- Support predicate `∀ m > L, P.re m = 0 ∧ P.im m = 0` on `PolyC`. -/
def PolyCSupp (L : ℕ) (P : PolyC) : Prop := ta_PolySupp L P.re ∧ ta_PolySupp L P.im

theorem polyCSupp_toC {L : ℕ} {P : PolyC} (hP : PolyCSupp L P) (m : ℕ) (hm : L < m) :
    P.toC m = 0 := by simp [PolyC.toC, hP.1 m hm, hP.2 m hm]

/-- Componentwise absolute-value bound `|P.re m| ≤ B ∧ |P.im m| ≤ B`. -/
def PolyCAbsBound (B : ℝ) (P : PolyC) : Prop :=
  (∀ m, |P.re m| ≤ B) ∧ (∀ m, |P.im m| ≤ B)

/-- Componentwise `L∞` approximation predicate between two `PolyC` polynomials. -/
def PolyCApprox (P_hat P : PolyC) (err : ℝ) : Prop :=
  (∀ m, |P_hat.re m - P.re m| ≤ err) ∧ (∀ m, |P_hat.im m - P.im m| ≤ err)

/-- Zero complex polynomial. -/
def polyZeroC : PolyC := ⟨ta_polyZero, ta_polyZero⟩

/-- Constant-`1` complex polynomial (`1` at `m = 0`, `0` elsewhere). -/
def polyOneC : PolyC := ⟨ta_polyOne, ta_polyZero⟩

/-- Degree-`0` complex monomial `v` at `m = 0`. -/
noncomputable def polyDelta0C (v : ℂ) : PolyC where
  re := fun m ↦ if m = 0 then v.re else 0
  im := fun m ↦ if m = 0 then v.im else 0

/-- Degree-`1` complex monomial `v * Y` (`v` at `m = 1`). -/
noncomputable def polyDelta1C (v : ℂ) : PolyC where
  re := fun m ↦ if m = 1 then v.re else 0
  im := fun m ↦ if m = 1 then v.im else 0

/-- Pointwise addition of `PolyC` polynomials. -/
def polyAddC (P Q : PolyC) : PolyC := ⟨ta_polyAdd P.re Q.re, ta_polyAdd P.im Q.im⟩

/-- Pointwise subtraction of `PolyC` polynomials. -/
def polySubC (P Q : PolyC) : PolyC := ⟨ta_polySub P.re Q.re, ta_polySub P.im Q.im⟩

/-- Pointwise negation of a `PolyC` polynomial. -/
def polyNegC (P : PolyC) : PolyC := ⟨ta_polyNeg P.re, ta_polyNeg P.im⟩

/-- Complex Cauchy product of two `PolyC` polynomials via real/imag convolutions. -/
def polyMulC (P Q : PolyC) : PolyC where
  re := ta_polySub (ta_polyConv P.re Q.re) (ta_polyConv P.im Q.im)
  im := ta_polyAdd (ta_polyConv P.re Q.im) (ta_polyConv P.im Q.re)

/-- Degree-`L` conjugate-reversal `(polyConjRev L P)(m) = conj(P(L - m))` for `m ≤ L`. -/
def polyConjRev (L : ℕ) (P : PolyC) : PolyC where
  re := ta_polyRev L P.re
  im := ta_polyNeg (ta_polyRev L P.im)

@[local simp] theorem polyZeroC_toC (m : ℕ) : polyZeroC.toC m = 0 := by
  simp [polyZeroC, PolyC.toC, ta_polyZero]

@[local simp] theorem polyOneC_toC (m : ℕ) : polyOneC.toC m = if m = 0 then 1 else 0 := by
  unfold polyOneC PolyC.toC ta_polyOne ta_polyZero
  by_cases hm : m = 0 <;> simp [hm]

@[local simp] theorem polyDelta0C_toC (v : ℂ) (m : ℕ) :
    (polyDelta0C v).toC m = if m = 0 then v else 0 := by
  by_cases hm : m = 0
  · simp [polyDelta0C, PolyC.toC, hm, mul_comm Complex.I]
  · simp [polyDelta0C, PolyC.toC, hm]

@[local simp] theorem polyDelta1C_toC (v : ℂ) (m : ℕ) :
    (polyDelta1C v).toC m = if m = 1 then v else 0 := by
  by_cases hm : m = 1
  · simp [polyDelta1C, PolyC.toC, hm, mul_comm Complex.I]
  · simp [polyDelta1C, PolyC.toC, hm]

@[local simp] theorem polyAddC_toC (P Q : PolyC) (m : ℕ) :
    (polyAddC P Q).toC m = P.toC m + Q.toC m := by
  simp only [polyAddC, PolyC.toC, ta_polyAdd, Complex.ofReal_add]
  ring

@[local simp] theorem polySubC_toC (P Q : PolyC) (m : ℕ) :
    (polySubC P Q).toC m = P.toC m - Q.toC m := by
  simp only [polySubC, PolyC.toC, ta_polySub, Complex.ofReal_sub]
  ring

@[local simp] theorem polyNegC_toC (P : PolyC) (m : ℕ) : (polyNegC P).toC m = -P.toC m := by
  simp only [polyNegC, PolyC.toC, ta_polyNeg, Complex.ofReal_neg]
  ring

theorem polyMulC_toC (P Q : PolyC) (m : ℕ) :
    (polyMulC P Q).toC m = ∑ i ∈ Finset.range (m + 1), P.toC i * Q.toC (m - i) := by
  unfold polyMulC PolyC.toC ta_polySub ta_polyAdd ta_polyConv; dsimp only; push_cast
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  linear_combination -(P.im i : ℂ) * (Q.im (m - i) : ℂ) * Complex.I_mul_I

theorem polyConjRev_toC (L : ℕ) (P : PolyC) (m : ℕ) :
    (polyConjRev L P).toC m = if m ≤ L then star (P.toC (L - m)) else 0 := by
  unfold polyConjRev PolyC.toC ta_polyRev ta_polyNeg; dsimp only
  by_cases hm : m ≤ L
  · simp only [hm, ↓reduceIte, Complex.ofReal_neg, star_add, star_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_I]; ring
  · simp [hm]

theorem polyMulC_delta0_left (v : ℂ) (P : PolyC) (m : ℕ) :
    (polyMulC (polyDelta0C v) P).toC m = v * P.toC m := by
  rw [polyMulC_toC, Finset.sum_eq_single 0 (fun i _ hi ↦ by simp [hi])
    (fun h0 ↦ absurd (Finset.mem_range.mpr (Nat.zero_lt_succ m)) h0)]; simp

theorem polyMulC_delta0_right (P : PolyC) (v : ℂ) (m : ℕ) :
    (polyMulC P (polyDelta0C v)).toC m = P.toC m * v := by
  rw [polyMulC_toC, Finset.sum_eq_single m
    (fun i hi _ ↦ by simp [show m - i ≠ 0 by have := Finset.mem_range.mp hi; omega])
    (fun hm ↦ absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) hm)]; simp

theorem polyMulC_delta1_left (v : ℂ) (P : PolyC) (m : ℕ) :
    (polyMulC (polyDelta1C v) P).toC m = if m = 0 then 0 else v * P.toC (m - 1) := by
  rcases m with _ | m'
  · simp [polyMulC_toC]
  · rw [polyMulC_toC, Finset.sum_eq_single 1 (fun _ _ hi ↦ by simp [hi])
      (fun h1 ↦ absurd (Finset.mem_range.mpr (by omega)) h1)]; simp

theorem polyDelta1C_supp (v : ℂ) : PolyCSupp 1 (polyDelta1C v) :=
  ⟨fun m hm ↦ by simp [polyDelta1C, show m ≠ 1 by omega],
   fun m hm ↦ by simp [polyDelta1C, show m ≠ 1 by omega]⟩

theorem polyConjRev_supp (L : ℕ) (P : PolyC) : PolyCSupp L (polyConjRev L P) :=
  ⟨fun m hm ↦ by simp [polyConjRev, ta_polyRev, show ¬(m ≤ L) by omega],
   fun m hm ↦ by simp [polyConjRev, ta_polyRev, ta_polyNeg, show ¬(m ≤ L) by omega]⟩

theorem polyMulC_supp {L1 L2 : ℕ} {P Q : PolyC} (hP : PolyCSupp L1 P) (hQ : PolyCSupp L2 Q) :
    PolyCSupp (L1 + L2) (polyMulC P Q) :=
  ⟨fun m hm ↦ by
    simp [polyMulC, ta_polySub, ta_polyConv_supp hP.1 hQ.1 m hm, ta_polyConv_supp hP.2 hQ.2 m hm],
   fun m hm ↦ by
    simp [polyMulC, ta_polyAdd, ta_polyConv_supp hP.1 hQ.2 m hm, ta_polyConv_supp hP.2 hQ.1 m hm]⟩

theorem polyConjRev_mul {LU LV : ℕ} {U V : PolyC} (hU : PolyCSupp LU U) (hV : PolyCSupp LV V)
    : polyConjRev (LU + LV) (polyMulC U V) = polyMulC (polyConjRev LU U) (polyConjRev LV V) :=
  PolyC.ext_toC fun m ↦ by
    rw [polyConjRev_toC, polyMulC_toC, polyMulC_toC]
    by_cases hm : m ≤ LU + LV
    · simp only [hm, ↓reduceIte, star_sum, star_mul']
      let K := LU + LV - m
      have h_lhs : ∑ j ∈ Finset.range (K + 1), star (U.toC j) * star (V.toC (K - j)) =
          ∑ j ∈ (Finset.range (K + 1)).filter (fun j ↦ j ≤ LU ∧ K - j ≤ LV),
            star (U.toC j) * star (V.toC (K - j)) := by
        rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs with hj
        · rfl
        · by_cases hjU : j ≤ LU
          · simp [polyCSupp_toC hV (K - j) (by omega)]
          · simp [polyCSupp_toC hU j (by omega)]
      have h_rhs : ∑ i ∈ Finset.range (m + 1), (polyConjRev LU U).toC i *
          (polyConjRev LV V).toC (m - i) =
          ∑ i ∈ (Finset.range (m + 1)).filter (fun i ↦ i ≤ LU ∧ m - i ≤ LV),
            star (U.toC (LU - i)) * star (V.toC (LV - (m - i))) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hiU : i ≤ LU
        · by_cases hiV : m - i ≤ LV <;> simp [polyConjRev_toC, hiU, hiV]
        · simp [polyConjRev_toC, hiU]
      change (∑ j ∈ Finset.range (K + 1), star (U.toC j) * star (V.toC (K - j))) = _
      rw [h_lhs, h_rhs]
      exact Finset.sum_bij (fun j _ ↦ LU - j)
        (fun _ hj ↦ by simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega)
        (fun _ h1 _ h2 _ ↦ by simp only [Finset.mem_filter] at h1 h2; omega)
        (fun i hi ↦ ⟨LU - i, by simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega,
          by simp only [Finset.mem_filter] at hi; omega⟩)
        (fun j hj ↦ by
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          rw [show LU - (LU - j) = j by omega, show LV - (m - (LU - j)) = K - j by omega])
    · simpa only [hm, ↓reduceIte] using (Finset.sum_eq_zero fun i _ ↦ by
        rw [polyConjRev_toC, polyConjRev_toC]
        by_cases hiU : i ≤ LU
        · simp [hiU, show ¬(m - i ≤ LV) by omega]
        · simp [hiU]).symm

/-- Complex `2 × 2` transfer matrix `((a, b), (c, d))` in `Y = X ^ 2`. -/
@[ext] structure PolyMat2C where
  a : PolyC
  b : PolyC
  c : PolyC
  d : PolyC

/-- Support predicate `PolyCSupp L` on all four entries of `PolyMat2C`. -/
def PolyMat2CSupp (L : ℕ) (M : PolyMat2C) : Prop :=
  PolyCSupp L M.a ∧ PolyCSupp L M.b ∧ PolyCSupp L M.c ∧ PolyCSupp L M.d

/-- Identity `2 × 2` complex polynomial matrix. -/
def polyMat2CId : PolyMat2C where
  a := polyOneC
  b := polyZeroC
  c := polyZeroC
  d := polyOneC

/-- Initial step-`0` `2 × 2` Cayley-Klein constant matrix `((a0, -star b0), (b0, star a0))`. -/
noncomputable def polyMat2CInit (a0 b0 : ℂ) : PolyMat2C where
  a := polyDelta0C a0
  b := polyDelta0C (-star b0)
  c := polyDelta0C b0
  d := polyDelta0C (star a0)

/-- Single interior step `2 × 2` complex transfer matrix `((ag * Y, -star bg), (bg * Y, star
ag))`. -/
noncomputable def polyMat2CGate (ag bg : ℂ) : PolyMat2C where
  a := polyDelta1C ag
  b := polyDelta0C (-star bg)
  c := polyDelta1C bg
  d := polyDelta0C (star ag)

/-- Matrix product of two `2 × 2` complex polynomial matrices. -/
def polyMat2CMul (U V : PolyMat2C) : PolyMat2C where
  a := polyAddC (polyMulC U.a V.a) (polyMulC U.b V.c)
  b := polyAddC (polyMulC U.a V.b) (polyMulC U.b V.d)
  c := polyAddC (polyMulC U.c V.a) (polyMulC U.d V.c)
  d := polyAddC (polyMulC U.c V.b) (polyMulC U.d V.d)

theorem polyMat2CMul_id_left (M : PolyMat2C) : polyMat2CMul polyMat2CId M = M := by
  have h1 : polyOneC = polyDelta0C 1 := PolyC.ext_toC fun _ ↦ by simp
  cases M; unfold polyMat2CMul polyMat2CId; dsimp only
  congr 1 <;> (apply PolyC.ext_toC; intro m; simp [h1, polyMulC_toC])

theorem polyMat2CMul_id_right (M : PolyMat2C) : polyMat2CMul M polyMat2CId = M := by
  have h1 : polyOneC = polyDelta0C 1 := PolyC.ext_toC fun _ ↦ by simp
  have h0 : polyZeroC = polyDelta0C 0 := PolyC.ext_toC fun _ ↦ by simp
  cases M; unfold polyMat2CMul polyMat2CId; dsimp only
  congr 1 <;> (apply PolyC.ext_toC; intro m; simp [h1, h0, polyMulC_delta0_right])

theorem polyMat2CMul_assoc (U V W : PolyMat2C) :
    polyMat2CMul (polyMat2CMul U V) W = polyMat2CMul U (polyMat2CMul V W) := by
  have hsr : ∀ A B : PolyC, ∀ m, (polyMulC A B).toC (m + 1) =
      (polyMulC A (PolyC.ofC fun k ↦ B.toC (k + 1))).toC m + A.toC (m + 1) * B.toC 0 :=
    fun A B m ↦ by
      rw [polyMulC_toC, Finset.sum_range_succ _ (m + 1), Nat.sub_self, polyMulC_toC]
      refine congrArg (· + _) (Finset.sum_congr rfl fun i hi ↦ ?_)
      rw [PolyC.ofC_toC, show m + 1 - i = m - i + 1 by have := Finset.mem_range.mp hi; omega]
  have hassoc : ∀ P Q R : PolyC, polyMulC (polyMulC P Q) R = polyMulC P (polyMulC Q R) :=
    fun P Q R ↦ PolyC.ext_toC fun m ↦ by
      induction m generalizing R with
      | zero => simp [polyMulC_toC, mul_assoc]
      | succ m ih =>
        rw [hsr (polyMulC P Q) R m, ih (PolyC.ofC fun k ↦ R.toC (k + 1))]
        conv_rhs => rw [polyMulC_toC, Finset.sum_range_succ, Nat.sub_self]
        rw [show (∑ i ∈ Finset.range (m + 1), P.toC i * (polyMulC Q R).toC (m + 1 - i)) =
              (polyMulC P (polyMulC Q (PolyC.ofC fun k ↦ R.toC (k + 1)))).toC m +
              ∑ i ∈ Finset.range (m + 1), P.toC i * (Q.toC (m + 1 - i) * R.toC 0) by
              rw [polyMulC_toC, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i hi ↦ ?_
              rw [show m + 1 - i = (m - i) + 1 by have := Finset.mem_range.mp hi; omega,
                  hsr Q R, mul_add]]
        simp only [polyMulC_toC, Finset.sum_range_succ, Nat.sub_self,
          add_mul, Finset.sum_mul, mul_assoc]
        ring
  have hal : ∀ A B C, polyMulC (polyAddC A B) C = polyAddC (polyMulC A C) (polyMulC B C) :=
    fun _ _ _ ↦ PolyC.ext_toC fun _ ↦ by simp [polyMulC_toC, ← Finset.sum_add_distrib, add_mul]
  have har : ∀ A B C, polyMulC A (polyAddC B C) = polyAddC (polyMulC A B) (polyMulC A C) :=
    fun _ _ _ ↦ PolyC.ext_toC fun _ ↦ by simp [polyMulC_toC, ← Finset.sum_add_distrib, mul_add]
  unfold polyMat2CMul
  congr 1 <;> (
    apply PolyC.ext_toC
    intro m
    simp only [polyAddC_toC, hal, har, hassoc]
    ring)

theorem polyMat2CGate_mul_apply (ag bg : ℂ) (M : PolyMat2C) (m : ℕ) :
    (polyMat2CMul (polyMat2CGate ag bg) M).a.toC m =
      (if m = 0 then 0 else ag * M.a.toC (m - 1)) - star bg * M.c.toC m ∧
    (polyMat2CMul (polyMat2CGate ag bg) M).b.toC m =
      (if m = 0 then 0 else ag * M.b.toC (m - 1)) - star bg * M.d.toC m ∧
    (polyMat2CMul (polyMat2CGate ag bg) M).c.toC m =
      (if m = 0 then 0 else bg * M.a.toC (m - 1)) + star ag * M.c.toC m ∧
    (polyMat2CMul (polyMat2CGate ag bg) M).d.toC m =
      (if m = 0 then 0 else bg * M.b.toC (m - 1)) + star ag * M.d.toC m := by
  unfold polyMat2CMul polyMat2CGate
  dsimp only
  simp only [polyAddC_toC, polyMulC_delta1_left, polyMulC_delta0_left]
  refine ⟨by ring, by ring, trivial, trivial⟩

/-- Cayley-Klein `2 × 2` embedding `((P, -conjRev_L Q), (Q, conjRev_L P))` of `(P, Q)` at degree
`L`. -/
def cdMat (L : ℕ) (P Q : PolyC) : PolyMat2C where
  a := P
  b := polyNegC (polyConjRev L Q)
  c := Q
  d := polyConjRev L P

/-- Compact Cayley-Dickson pair product `(P', Q')` representing `cdMat LR PR QR * cdMat LL PL
QL`. -/
def cdMul (LR : ℕ) (PR QR PL QL : PolyC) : PolyC × PolyC :=
  (polySubC (polyMulC PR PL) (polyMulC (polyConjRev LR QR) QL),
   polyAddC (polyMulC QR PL) (polyMulC (polyConjRev LR PR) QL))

theorem cdMat_one_gate (ag bg : ℂ) :
    cdMat 1 (polyDelta1C ag) (polyDelta1C bg) = polyMat2CGate ag bg := by
  unfold cdMat polyMat2CGate
  congr 1 <;> (
    apply PolyC.ext_toC
    rintro (_ | _ | _) <;> simp [polyNegC_toC, polyConjRev_toC, polyDelta0C_toC])

theorem cdMat_mul {LR LL : ℕ} {PR QR PL QL : PolyC} (hPR : PolyCSupp LR PR)
    (hQR : PolyCSupp LR QR) (hPL : PolyCSupp LL PL) (hQL : PolyCSupp LL QL) : polyMat2CMul
    (cdMat LR PR QR) (cdMat LL PL QL) = cdMat (LR + LL) (cdMul LR PR QR PL QL).1
    (cdMul LR PR QR PL QL).2 := by
  have hnl : ∀ P Q, polyMulC (polyNegC P) Q = polyNegC (polyMulC P Q) := fun _ _ ↦
    PolyC.ext_toC fun _ ↦ by simp only [polyNegC_toC, polyMulC_toC, neg_mul, Finset.sum_neg_distrib]
  have hnr : ∀ P Q, polyMulC P (polyNegC Q) = polyNegC (polyMulC P Q) := fun _ _ ↦
    PolyC.ext_toC fun _ ↦ by simp only [polyNegC_toC, polyMulC_toC, mul_neg, Finset.sum_neg_distrib]
  have hinv : ∀ {L P}, PolyCSupp L P → polyConjRev L (polyConjRev L P) = P :=
    fun {L P} hP ↦ PolyC.ext_toC fun m ↦ by
      rw [polyConjRev_toC]
      by_cases hm : m ≤ L
      · simp [hm, polyConjRev_toC, show L - m ≤ L by omega, show L - (L - m) = m by omega]
      · simpa [hm] using (polyCSupp_toC hP m (by omega)).symm
  unfold polyMat2CMul cdMat cdMul
  dsimp only
  refine PolyMat2C.ext (PolyC.ext_toC fun _ ↦ by
      simp only [polyAddC_toC, polySubC_toC, hnl, polyNegC_toC]
      ring) ?_ rfl ?_
  · rw [show ∀ A B, polyConjRev (LR + LL) (polyAddC A B) =
          polyAddC (polyConjRev (LR + LL) A) (polyConjRev (LR + LL) B) from fun _ _ ↦
          PolyC.ext_toC fun m ↦ by
            by_cases hm : m ≤ LR + LL <;> simp [polyConjRev_toC, hm, star_add],
        polyConjRev_mul hQR hPL, polyConjRev_mul (polyConjRev_supp LR PR) hQL, hinv hPR]
    exact PolyC.ext_toC fun _ ↦ by
      simp only [polyAddC_toC, hnl, hnr, polyNegC_toC]
      ring
  · rw [show ∀ A B, polyConjRev (LR + LL) (polySubC A B) =
          polySubC (polyConjRev (LR + LL) A) (polyConjRev (LR + LL) B) from fun _ _ ↦
          PolyC.ext_toC fun m ↦ by
            by_cases hm : m ≤ LR + LL <;> simp [polyConjRev_toC, hm, star_sub],
        polyConjRev_mul hPR hPL, polyConjRev_mul (polyConjRev_supp LR QR) hQL, hinv hQR]
    exact PolyC.ext_toC fun _ ↦ by
      simp only [polyAddC_toC, polySubC_toC, hnr, polyNegC_toC]
      ring

/-- Exact `(P, Q)` polynomial transfer pair of a `DyadicSu2Gate` list `gs` at scale `2 ^ b`. -/
noncomputable def gateListTransferPQ (b : ℕ) : List DyadicSu2Gate → PolyC × PolyC
  | [] => (polyOneC, polyZeroC)
  | g :: gs =>
      let pq := gateListTransferPQ b gs
      let ab := gateSu2Pair b g
      cdMul gs.length pq.1 pq.2 (polyDelta1C ab.1) (polyDelta1C ab.2)

theorem gateListTransferPQ_supp (b : ℕ) : ∀ (gs : List DyadicSu2Gate),
    PolyCSupp gs.length (gateListTransferPQ b gs).1 ∧ PolyCSupp gs.length (gateListTransferPQ b
      gs).2
  | [] => ⟨⟨fun m hm ↦ by simp [gateListTransferPQ, polyOneC, ta_polyOne, show m ≠ 0 by omega],
            fun _ _ ↦ rfl⟩,
           ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩⟩
  | g :: gs => by
      dsimp only [gateListTransferPQ, List.length_cons]
      rcases gateListTransferPQ_supp b gs with ⟨hP, hQ⟩
      have h1 := polyMulC_supp hP (polyDelta1C_supp (gateSu2Pair b g).1)
      have h2 := polyMulC_supp
        (polyConjRev_supp gs.length (gateListTransferPQ b gs).2) (polyDelta1C_supp (gateSu2Pair b
          g).2)
      have h3 := polyMulC_supp hQ (polyDelta1C_supp (gateSu2Pair b g).1)
      have h4 := polyMulC_supp
        (polyConjRev_supp gs.length (gateListTransferPQ b gs).1) (polyDelta1C_supp (gateSu2Pair b
          g).2)
      exact ⟨⟨fun m hm ↦ by simp [cdMul, polySubC, ta_polySub, h1.1 m hm, h2.1 m hm],
              fun m hm ↦ by simp [cdMul, polySubC, ta_polySub, h1.2 m hm, h2.2 m hm]⟩,
             ⟨fun m hm ↦ by simp [cdMul, polyAddC, ta_polyAdd, h3.1 m hm, h4.1 m hm],
              fun m hm ↦ by simp [cdMul, polyAddC, ta_polyAdd, h3.2 m hm, h4.2 m hm]⟩⟩

/-- Exact `2 × 2` matrix transfer of a `DyadicSu2Gate` list `gs` at scale `2 ^ b`. -/
noncomputable def gateListTransferMatC (b : ℕ) : List DyadicSu2Gate → PolyMat2C
  | [] => polyMat2CId
  | g :: gs =>
      let ab := gateSu2Pair b g
      polyMat2CMul (gateListTransferMatC b gs) (polyMat2CGate ab.1 ab.2)

theorem gateListTransferMatC_eq_cdMat (b : ℕ) :
    ∀ (gs : List DyadicSu2Gate),
      gateListTransferMatC b gs =
        cdMat gs.length (gateListTransferPQ b gs).1 (gateListTransferPQ b gs).2
  | [] => by
      unfold gateListTransferMatC gateListTransferPQ cdMat polyMat2CId; congr 1
      · exact (PolyC.ext_toC fun _ ↦ by simp [polyNegC_toC, polyConjRev_toC]).symm
      · apply PolyC.ext_toC; intro m; rw [polyConjRev_toC]; rcases m with _ | _ <;> simp
  | g :: gs => by
      dsimp only [gateListTransferMatC, gateListTransferPQ, List.length_cons]
      rw [gateListTransferMatC_eq_cdMat b gs, ← cdMat_one_gate]
      rcases gateListTransferPQ_supp b gs with ⟨hP, hQ⟩
      exact cdMat_mul hP hQ (polyDelta1C_supp _) (polyDelta1C_supp _)

theorem gateListTransferPQ_append (b : ℕ) (gs1 gs2 : List DyadicSu2Gate) : gateListTransferPQ
    b (gs1 ++ gs2) = cdMul gs2.length (gateListTransferPQ b gs2).1
    (gateListTransferPQ b gs2).2 (gateListTransferPQ b gs1).1 (gateListTransferPQ b gs1).2 := by
  have hm : gateListTransferMatC b (gs1 ++ gs2) =
      polyMat2CMul (gateListTransferMatC b gs2) (gateListTransferMatC b gs1) := by
    induction gs1 with
    | nil => simp [gateListTransferMatC, polyMat2CMul_id_right]
    | cons _ tail ih => simp only [gateListTransferMatC, List.cons_append, ih, polyMat2CMul_assoc]
  rw [gateListTransferMatC_eq_cdMat, gateListTransferMatC_eq_cdMat,
      gateListTransferMatC_eq_cdMat] at hm
  rcases gateListTransferPQ_supp b gs2 with ⟨hPR, hQR⟩
  rcases gateListTransferPQ_supp b gs1 with ⟨hPL, hQL⟩
  rw [cdMat_mul hPR hQR hPL hQL] at hm
  exact Prod.ext (congrArg PolyMat2C.a hm) (congrArg PolyMat2C.c hm)

theorem polyCAbsBound_of_approx {P_hat P : PolyC} {B_hat err : ℝ}
    (hbnd : PolyCAbsBound B_hat P_hat) (herr : PolyCApprox P_hat P err) :
    PolyCAbsBound (B_hat + err) P := by
  have hs : ∀ xh x : ℝ, |xh| ≤ B_hat → |xh - x| ≤ err → |x| ≤ B_hat + err := fun xh x h1 h2 ↦ by
    have ht := abs_sub_le x xh 0
    rw [sub_zero, sub_zero, abs_sub_comm] at ht
    linarith
  exact ⟨fun m ↦ hs _ _ (hbnd.1 m) (herr.1 m), fun m ↦ hs _ _ (hbnd.2 m) (herr.2 m)⟩

theorem cdMul_bilinear_err {LR LL : ℕ} {PR_hat PR QR_hat QR PL_hat PL QL_hat QL : PolyC}
    {BR BL ER EL : ℝ} (hBR : 0 ≤ BR) (hBL : 0 ≤ BL) (hER : 0 ≤ ER) (hEL : 0 ≤ EL)
    (hPR_hat_s : PolyCSupp LR PR_hat) (hPR_s : PolyCSupp LR PR)
    (hQR_hat_s : PolyCSupp LR QR_hat) (hQR_s : PolyCSupp LR QR)
    (hPL_hat_s : PolyCSupp LL PL_hat) (hPL_s : PolyCSupp LL PL)
    (hQL_hat_s : PolyCSupp LL QL_hat) (hQL_s : PolyCSupp LL QL)
    (hPR_bnd : PolyCAbsBound BR PR_hat) (hQR_bnd : PolyCAbsBound BR QR_hat)
    (hPL_bnd : PolyCAbsBound BL PL) (hQL_bnd : PolyCAbsBound BL QL)
    (hPR_err : PolyCApprox PR_hat PR ER) (hQR_err : PolyCApprox QR_hat QR ER)
    (hPL_err : PolyCApprox PL_hat PL EL) (hQL_err : PolyCApprox QL_hat QL EL) : PolyCApprox
    (cdMul LR PR_hat QR_hat PL_hat QL_hat).1 (cdMul LR PR QR PL QL).1
    (4 * ((min LR LL + 1 : ℕ) : ℝ) * (BR * EL + BL * ER)) ∧ PolyCApprox
    (cdMul LR PR_hat QR_hat PL_hat QL_hat).2 (cdMul LR PR QR PL QL).2
    (4 * ((min LR LL + 1 : ℕ) : ℝ) * (BR * EL + BL * ER)) := by
  let E1 := ((min LR LL + 1 : ℕ) : ℝ) * (BR * EL + BL * ER)
  have h2_pm : ∀ a1 a2 b1 b2 E : ℝ, |a1 - b1| ≤ E → |a2 - b2| ≤ E →
      |(a1 - a2) - (b1 - b2)| ≤ 2 * E ∧ |(a1 + a2) - (b1 + b2)| ≤ 2 * E :=
    fun a1 a2 b1 b2 E h1 h2 ↦ by
      have hs := abs_sub_le (a1 - b1) 0 (a2 - b2)
      have ha := abs_add_le (a1 - b1) (a2 - b2)
      simp only [sub_zero, zero_sub, abs_neg] at hs
      rw [show (a1 - a2) - (b1 - b2) = (a1 - b1) - (a2 - b2) by ring,
          show (a1 + a2) - (b1 + b2) = (a1 - b1) + (a2 - b2) by ring]
      exact ⟨by linarith, by linarith⟩
  have hmul : ∀ {U_h U V_h V : PolyC}, PolyCSupp LR U_h → PolyCSupp LR U →
      PolyCSupp LL V_h → PolyCSupp LL V → PolyCAbsBound BR U_h → PolyCAbsBound BL V →
      PolyCApprox U_h U ER → PolyCApprox V_h V EL →
      PolyCApprox (polyMulC U_h V_h) (polyMulC U V) (2 * E1) :=
    fun hUh_s hU_s hVh_s hV_s hU_b hV_b hU_e hV_e ↦
      ⟨fun m ↦ (h2_pm _ _ _ _ E1
        (ta_polyConv_bilinear_err hBR hBL hER hEL hUh_s.1 hU_s.1
          hVh_s.1 hV_s.1 hU_b.1 hV_b.1 hU_e.1 hV_e.1 m)
        (ta_polyConv_bilinear_err hBR hBL hER hEL hUh_s.2 hU_s.2
          hVh_s.2 hV_s.2 hU_b.2 hV_b.2 hU_e.2 hV_e.2 m)).1,
       fun m ↦ (h2_pm _ _ _ _ E1
        (ta_polyConv_bilinear_err hBR hBL hER hEL hUh_s.1 hU_s.1
          hVh_s.2 hV_s.2 hU_b.1 hV_b.2 hU_e.1 hV_e.2 m)
        (ta_polyConv_bilinear_err hBR hBL hER hEL hUh_s.2 hU_s.2
          hVh_s.1 hV_s.1 hU_b.2 hV_b.1 hU_e.2 hV_e.1 m)).2⟩
  have hcr_b : ∀ {P}, PolyCAbsBound BR P → PolyCAbsBound BR (polyConjRev LR P) := fun hP ↦
    ⟨fun m ↦ by by_cases hm : m ≤ LR <;> simp [polyConjRev, ta_polyRev, hm, hBR, hP.1 (LR - m)],
     fun m ↦ by
       by_cases hm : m ≤ LR <;> simp [polyConjRev, ta_polyRev, ta_polyNeg, hm, hBR, hP.2 (LR - m)]⟩
  have hcr_e : ∀ {Ph P}, PolyCApprox Ph P ER →
      PolyCApprox (polyConjRev LR Ph) (polyConjRev LR P) ER := fun {Ph P} h ↦
    ⟨fun m ↦ by
      by_cases hm : m ≤ LR
      · simpa [polyConjRev, ta_polyRev, hm] using h.1 (LR - m)
      · simp [polyConjRev, ta_polyRev, hm, hER],
     fun m ↦ by
      by_cases hm : m ≤ LR
      · unfold polyConjRev ta_polyRev ta_polyNeg
        simp only [hm, ↓reduceIte]
        rw [show -Ph.im (LR - m) - -P.im (LR - m) = -(Ph.im (LR - m) - P.im (LR - m)) by ring,
            abs_neg]
        exact h.2 (LR - m)
      · simp [polyConjRev, ta_polyRev, ta_polyNeg, hm, hER]⟩
  have hm1 := hmul hPR_hat_s hPR_s hPL_hat_s hPL_s hPR_bnd hPL_bnd hPR_err hPL_err
  have hm2 := hmul (polyConjRev_supp LR QR_hat) (polyConjRev_supp LR QR) hQL_hat_s hQL_s
    (hcr_b hQR_bnd) hQL_bnd (hcr_e hQR_err) hQL_err
  have hm3 := hmul hQR_hat_s hQR_s hPL_hat_s hPL_s hQR_bnd hPL_bnd hQR_err hPL_err
  have hm4 := hmul (polyConjRev_supp LR PR_hat) (polyConjRev_supp LR PR) hQL_hat_s hQL_s
    (hcr_b hPR_bnd) hQL_bnd (hcr_e hPR_err) hQL_err
  have h4E : 2 * (2 * E1) = 4 * ((min LR LL + 1 : ℕ) : ℝ) * (BR * EL + BL * ER) := by
    dsimp [E1]
    ring
  exact ⟨⟨fun m ↦ ((h2_pm _ _ _ _ (2 * E1) (hm1.1 m) (hm2.1 m)).1).trans_eq h4E,
          fun m ↦ ((h2_pm _ _ _ _ (2 * E1) (hm1.2 m) (hm2.2 m)).1).trans_eq h4E⟩,
         ⟨fun m ↦ ((h2_pm _ _ _ _ (2 * E1) (hm3.1 m) (hm4.1 m)).2).trans_eq h4E,
          fun m ↦ ((h2_pm _ _ _ _ (2 * E1) (hm3.2 m) (hm4.2 m)).2).trans_eq h4E⟩⟩

theorem runLoopEven_lt {M t m : ℕ} (h : m ≤ t ∧ t ≤ M) :
    (M + 1) - t + 2 * m < 2 * (M + 1) + 1 := by omega

theorem runLoopOdd_lt {M t m : ℕ} (h : m ≤ t ∧ t ≤ M) :
    (M + 1) - t + 2 * m + 1 < 2 * (M + 1) + 1 := by omega

/-- Parity-halved `2 × 2` complex polynomial view of `biGqspTwoAngleRunLoop M ab t`. -/
noncomputable def runLoopMatC (M : ℕ) (ab : ℕ → ℂ × ℂ) (t : ℕ) : PolyMat2C where
  a := PolyC.ofC fun m ↦
    if h : m ≤ t ∧ t ≤ M then (biGqspTwoAngleRunLoop M ab t).1 ⟨(M + 1) - t + 2 * m, runLoopEven_lt
      h⟩ else 0
  b := PolyC.ofC fun m ↦
    if h : m ≤ t ∧ t ≤ M then (biGqspTwoAngleRunLoop M ab t).1 ⟨(M + 1) - t + 2 * m + 1,
      runLoopOdd_lt h⟩ else 0
  c := PolyC.ofC fun m ↦
    if h : m ≤ t ∧ t ≤ M then (biGqspTwoAngleRunLoop M ab t).2 ⟨(M + 1) - t + 2 * m, runLoopEven_lt
      h⟩ else 0
  d := PolyC.ofC fun m ↦
    if h : m ≤ t ∧ t ≤ M then (biGqspTwoAngleRunLoop M ab t).2 ⟨(M + 1) - t + 2 * m + 1,
      runLoopOdd_lt h⟩ else 0

theorem runLoop_shift_pair (M : ℕ) (ab : ℕ → ℂ × ℂ) (t p m : ℕ)
    (ht : t < M) (hp : p ≤ 1) (hm : m ≤ t + 1) :
    shiftRightC (M + 1) (biGqspTwoAngleRunLoop M ab t).1
      ⟨(M + 1) - (t + 1) + 2 * m + p, by omega⟩ =
      (if m = 0 then 0 else if h : m - 1 ≤ t ∧ t ≤ M then
        (biGqspTwoAngleRunLoop M ab t).1 ⟨(M + 1) - t + 2 * (m - 1) + p, by omega⟩ else 0) ∧
    shiftLeftC (M + 1) (biGqspTwoAngleRunLoop M ab t).2
      ⟨(M + 1) - (t + 1) + 2 * m + p, by omega⟩ =
      (if h : m ≤ t ∧ t ≤ M then
        (biGqspTwoAngleRunLoop M ab t).2 ⟨(M + 1) - t + 2 * m + p, by omega⟩ else 0) := by
  refine ⟨?_, ?_⟩
  · dsimp only [shiftRightC]
    simp only [show (M + 1) - (t + 1) + 2 * m + p ≠ 0 by omega, ↓reduceDIte]
    rcases m with _ | m'
    · simp only [↓reduceIte]
      exact (biGqspTwoAngleRunLoop_support M ab t (by omega)
        ⟨(M + 1) - (t + 1) + 2 * 0 + p - 1, by omega⟩ (by dsimp only; omega)).1
    · simp only [Nat.add_one_ne_zero, Nat.add_sub_cancel,
        show m' ≤ t ∧ t ≤ M by omega, and_self, ↓reduceIte, ↓reduceDIte]
      exact congrArg (biGqspTwoAngleRunLoop M ab t).1 (by ext; dsimp only; omega)
  · dsimp only [shiftLeftC]
    by_cases hmt : m ≤ t
    · simp only [show (M + 1) - (t + 1) + 2 * m + p < 2 * (M + 1) by omega,
        show m ≤ t ∧ t ≤ M from ⟨hmt, by omega⟩, and_self, ↓reduceDIte]
      exact congrArg (biGqspTwoAngleRunLoop M ab t).2 (by ext; dsimp only; omega)
    · simp only [show ¬(m ≤ t ∧ t ≤ M) by omega, ↓reduceDIte]
      split_ifs with hlt
      · exact (biGqspTwoAngleRunLoop_support M ab t (by omega)
          ⟨(M + 1) - (t + 1) + 2 * m + p + 1, by omega⟩ (by dsimp only; omega)).2
      · rfl

theorem runLoopMatC_succ (M : ℕ) (ab : ℕ → ℂ × ℂ) (t : ℕ) (ht : t < M) :
    runLoopMatC M ab (t + 1) =
      polyMat2CMul (polyMat2CGate (ab (t + 1)).1 (ab (t + 1)).2) (runLoopMatC M ab t) := by
  have hs : ∀ s, PolyMat2CSupp s (runLoopMatC M ab s) := fun s ↦ by
    refine ⟨⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩, ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩,
            ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩, ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩⟩ <;>
      simp [runLoopMatC, PolyC.ofC, show ¬(m ≤ s ∧ s ≤ M) by omega]
  have h1 := hs (t + 1)
  have h0 := hs t
  refine PolyMat2C.ext (PolyC.ext_toC ?_) (PolyC.ext_toC ?_) (PolyC.ext_toC ?_) (PolyC.ext_toC ?_)
  all_goals
    intro m
    rcases polyMat2CGate_mul_apply (ab (t + 1)).1 (ab (t + 1)).2 (runLoopMatC M ab t) m with
      ⟨ga, gb, gc, gd⟩
    first | rw [ga] | rw [gb] | rw [gc] | rw [gd]
    by_cases hm : m ≤ t + 1
    · rcases runLoop_shift_pair M ab t 0 m ht (by omega) hm with ⟨hx0, hy0⟩
      rcases runLoop_shift_pair M ab t 1 m ht (by omega) hm with ⟨hx1, hy1⟩
      simp only [Nat.add_zero] at hx0 hy0
      have hc : m ≤ t + 1 ∧ t + 1 ≤ M := ⟨hm, by omega⟩
      unfold runLoopMatC
      simp only [PolyC.ofC_toC, hc, and_self, ↓reduceDIte]
      first
      | (change (gqspSu2Step (M + 1) _ _ _).1 _ = _; unfold gqspSu2Step; dsimp only; rw [hx0, hy0])
      | (change (gqspSu2Step (M + 1) _ _ _).1 _ = _; unfold gqspSu2Step; dsimp only; rw [hx1, hy1])
      | (change (gqspSu2Step (M + 1) _ _ _).2 _ = _; unfold gqspSu2Step; dsimp only; rw [hx0, hy0])
      | (change (gqspSu2Step (M + 1) _ _ _).2 _ = _; unfold gqspSu2Step; dsimp only; rw [hx1, hy1])
      rcases m with _ | _
      · simp
      · simp
    · simp only [show m ≠ 0 by omega, ↓reduceIte, polyCSupp_toC h1.1 m (by omega),
        polyCSupp_toC h1.2.1 m (by omega), polyCSupp_toC h1.2.2.1 m (by omega),
        polyCSupp_toC h1.2.2.2 m (by omega), polyCSupp_toC h0.1 (m - 1) (by omega),
        polyCSupp_toC h0.2.1 (m - 1) (by omega), polyCSupp_toC h0.2.2.1 m (by omega),
        polyCSupp_toC h0.2.2.2 m (by omega)]
      ring

theorem runLoopMatC_eq_cdMat_mul_init (M b : ℕ) (g0 : DyadicSu2Gate) (gs : List DyadicSu2Gate)
    (hlen : gs.length = M) : runLoopMatC M
    (fun s ↦ gateSu2Pair b ((g0 :: gs).getD s defaultSu2Gate)) M = polyMat2CMul
    (cdMat M (gateListTransferPQ b gs).1 (gateListTransferPQ b gs).2)
    (polyMat2CInit (gateSu2Pair b g0).1 (gateSu2Pair b g0).2) := by
  let ab := fun s ↦ gateSu2Pair b ((g0 :: gs).getD s defaultSu2Gate)
  have hstep : ∀ (xs : List DyadicSu2Gate) (t0 : ℕ), t0 + xs.length ≤ M →
      (∀ j < xs.length, ab (t0 + 1 + j) = gateSu2Pair b (xs.getD j defaultSu2Gate)) →
      runLoopMatC M ab (t0 + xs.length) =
        polyMat2CMul (gateListTransferMatC b xs) (runLoopMatC M ab t0) := by
    intro xs
    induction xs with
    | nil =>
        intro _ _ _
        simp [gateListTransferMatC, polyMat2CMul_id_left]
    | cons g xt ih =>
        intro t0 hle hab
        rw [show t0 + (g :: xt).length = (t0 + 1) + xt.length by
          simp only [List.length_cons]; omega,
            ih (t0 + 1) (by simp only [List.length_cons] at hle; omega) (fun j hj ↦ by
              have hj1 := hab (j + 1) (by simp only [List.length_cons]; omega)
              rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
                  ← List.getD_eq_getElem?_getD] at hj1
              simpa [show (t0 + 1) + 1 + j = t0 + 1 + (j + 1) by omega] using hj1),
            runLoopMatC_succ M ab t0 (by simp only [List.length_cons] at hle; omega),
            show ab (t0 + 1) = gateSu2Pair b g by
              simpa [List.getD_eq_getElem?_getD] using hab 0 (by simp),
            ← polyMat2CMul_assoc]
        rfl
  have hz : runLoopMatC M ab 0 = polyMat2CInit (ab 0).1 (ab 0).2 := by
    refine PolyMat2C.ext (PolyC.ext_toC fun m ↦ ?_) (PolyC.ext_toC fun m ↦ ?_)
      (PolyC.ext_toC fun m ↦ ?_) (PolyC.ext_toC fun m ↦ ?_) <;>
    · rcases m with _ | _ <;>
        simp [runLoopMatC, polyMat2CInit, biGqspTwoAngleRunLoop, gqspSu2Step, biGqspTwoAnglePreInit]
  have hadd := hstep gs 0 (by omega) fun j _ ↦ by
    simp only [ab, zero_add, show 1 + j = j + 1 by omega, List.getD_eq_getElem?_getD,
      List.getElem?_cons_succ]
  rw [zero_add, hlen, hz, show ab 0 = gateSu2Pair b g0 by simp [ab, List.getD_eq_getElem?_getD],
      gateListTransferMatC_eq_cdMat, hlen] at hadd
  exact hadd

/-- Root combined `P` polynomial at `m ≤ M` after multiplying `(P, Q)` on the right by step-`0`
`(a0, b0)`. -/
noncomputable def rootLoopP (M : ℕ) (a0 b0 : ℂ) (P Q : PolyC) (m : ℕ) : ℂ :=
  if m ≤ M then a0 * P.toC m - star (Q.toC (M - m)) * b0 else 0

/-- Root combined `Q` polynomial at `m ≤ M` after multiplying `(P, Q)` on the right by step-`0`
`(a0, b0)`. -/
noncomputable def rootLoopQ (M : ℕ) (a0 b0 : ℂ) (P Q : PolyC) (m : ℕ) : ℂ :=
  if m ≤ M then a0 * Q.toC m + star (P.toC (M - m)) * b0 else 0

theorem cdMat_mul_init_entries {M : ℕ} {P Q : PolyC} (a0 b0 : ℂ) (hP : PolyCSupp M P)
    (hQ : PolyCSupp M Q) (m : ℕ) : (polyMat2CMul (cdMat M P Q) (polyMat2CInit a0 b0)).a.toC m
    = rootLoopP M a0 b0 P Q m ∧ (polyMat2CMul (cdMat M P Q) (polyMat2CInit a0 b0)).b.toC m =
    (if m ≤ M then -star (rootLoopQ M a0 b0 P Q (M - m)) else 0) ∧
    (polyMat2CMul (cdMat M P Q) (polyMat2CInit a0 b0)).c.toC m = rootLoopQ M a0 b0 P Q m ∧
    (polyMat2CMul (cdMat M P Q) (polyMat2CInit a0 b0)).d.toC m =
    (if m ≤ M then star (rootLoopP M a0 b0 P Q (M - m)) else 0) := by
  dsimp only [polyMat2CMul, cdMat, polyMat2CInit]
  simp only [polyAddC_toC, polyMulC_delta0_right, polyNegC_toC, polyConjRev_toC]
  by_cases hm : m ≤ M
  · simp only [hm, ↓reduceIte, rootLoopP, rootLoopQ, show M - m ≤ M by omega,
      show M - (M - m) = m by omega, star_add, star_sub, star_mul, star_star]
    exact ⟨by ring, by ring, by ring, by ring⟩
  · simp [hm, rootLoopP, rootLoopQ, polyCSupp_toC hP m (by omega), polyCSupp_toC hQ m (by omega)]

def sched_tf1 {α : Type} (f : ℕ → α) (x : ℕ) : α :=
  @Nat.casesOn (fun _ ↦ α) (Nat.add 1 x) (f 0) f

theorem sched_tf1_eq {α : Type} (f : ℕ → α) (x : ℕ) : sched_tf1 f x = f x := by
  change @Nat.casesOn (fun _ ↦ α) (1 + x) (f 0) f = f x
  rw [Nat.one_add]

/-- Identity wrapper parameterized by a salt `s` to prevent kernel `m_whnf_cache` collisions. -/
def sched_idSalt (_s x : ℕ) : ℕ := x

theorem sched_idSalt_eq (s x : ℕ) : sched_idSalt s x = x := rfl

/-- Strict `Nat → ℕ` forcing wrapper. -/
def sched_tfNat (f : ℕ → ℕ) (x : ℕ) : ℕ := @Nat.casesOn (fun _ ↦ ℕ) (Nat.add 1 x) 0 f

theorem sched_tfNat_eq (f : ℕ → ℕ) (x : ℕ) : sched_tfNat f x = f x := by
  change @Nat.casesOn (fun _ ↦ ℕ) (1 + x) 0 f = f x
  rw [Nat.one_add]

/-- Salted strict `Nat → ℕ` forcing wrapper. -/
def sched_stfNat (s : ℕ) (f : ℕ → ℕ) (x : ℕ) : ℕ :=
  @Nat.casesOn (fun _ ↦ ℕ) (Nat.add 1 (sched_idSalt s x)) 0 f

theorem sched_stfNat_eq (s : ℕ) (f : ℕ → ℕ) (x : ℕ) : sched_stfNat s f x = f x :=
  sched_tfNat_eq f x

/-- Strict `Nat → List ℕ` forcing wrapper. -/
def sched_tfList (f : ℕ → List ℕ) (x : ℕ) : List ℕ :=
  @Nat.casesOn (fun _ ↦ List ℕ) (Nat.add 1 x) [] f

theorem sched_tfList_eq (f : ℕ → List ℕ) (x : ℕ) : sched_tfList f x = f x := by
  change @Nat.casesOn (fun _ ↦ List ℕ) (1 + x) [] f = f x
  rw [Nat.one_add]

/-- Salted strict `Nat → List ℕ` forcing wrapper. -/
def sched_stfList (s : ℕ) (f : ℕ → List ℕ) (x : ℕ) : List ℕ :=
  @Nat.casesOn (fun _ ↦ List ℕ) (Nat.add 1 (sched_idSalt s x)) [] f

theorem sched_stfList_eq (s : ℕ) (f : ℕ → List ℕ) (x : ℕ) : sched_stfList s f x = f x :=
  sched_tfList_eq f x

/-- Strict `Nat → Option α` forcing wrapper. -/
def sched_tfOpt {α : Type} (f : ℕ → Option α) (x : ℕ) : Option α :=
  @Nat.casesOn (fun _ ↦ Option α) (Nat.add 1 x) none f

theorem sched_tfOpt_eq {α : Type} (f : ℕ → Option α) (x : ℕ) : sched_tfOpt f x = f x := by
  change @Nat.casesOn (fun _ ↦ Option α) (1 + x) none f = f x
  rw [Nat.one_add]

/-- Salted strict `Nat → Option α` forcing wrapper. -/
def sched_stfOpt {α : Type} (s : ℕ) (f : ℕ → Option α) (x : ℕ) : Option α :=
  @Nat.casesOn (fun _ ↦ Option α) (Nat.add 1 (sched_idSalt s x)) none f

theorem sched_stfOpt_eq {α : Type} (s : ℕ) (f : ℕ → Option α) (x : ℕ) : sched_stfOpt s f x = f x :=
  sched_tfOpt_eq f x

/-- Chunked dynamic left-shift avoiding single-step GMP shifts larger than `0xc00000` bits. -/
def sched_shlDyn (x sh : ℕ) : ℕ := sched_tfNat (fun v ↦ if Nat.ble sh 0xc00000 then
    Nat.shiftLeft v sh else sched_tfNat (fun v1 ↦ if Nat.ble sh (Nat.add 0xc00000 0xc00000)
    then Nat.shiftLeft v1 (Nat.sub sh 0xc00000) else sched_tfNat (fun v2 ↦ Nat.shiftLeft v2
    (Nat.sub sh (Nat.add 0xc00000 0xc00000))) (Nat.shiftLeft v1 0xc00000)) (Nat.shiftLeft v
    0xc00000)) x

theorem sched_dynChunk_eq (op : ℕ → ℕ → ℕ)
    (hop : ∀ u a b : ℕ, op (op u a) b = op u (a + b)) (x sh c : ℕ) :
    (if Nat.ble sh c then op x sh
     else if Nat.ble sh (Nat.add c c) then op (op x c) (Nat.sub sh c)
     else op (op (op x c) c) (Nat.sub sh (Nat.add c c))) = op x sh := by
  by_cases h1 : sh ≤ c
  · simp [Nat.ble_eq.mpr h1]
  · have hb1 : Nat.ble sh c = false := Bool.eq_false_iff.mpr (fun h ↦ h1 (Nat.ble_eq.mp h))
    by_cases h2 : sh ≤ c + c
    · simp [hb1, Nat.add_eq, Nat.ble_eq.mpr h2, Nat.sub_eq, hop,
        Nat.add_sub_of_le (Nat.le_of_not_ge h1)]
    · have hb2 : Nat.ble sh (c + c) = false := Bool.eq_false_iff.mpr (fun h ↦ h2 (Nat.ble_eq.mp h))
      simp [hb1, hb2, Nat.add_eq, Nat.sub_eq, hop, Nat.add_sub_of_le (Nat.le_of_not_ge h2)]

theorem sched_shlDyn_eq (x sh : ℕ) : sched_shlDyn x sh = Nat.shiftLeft x sh := by
  simp only [sched_shlDyn, sched_tfNat_eq]
  exact sched_dynChunk_eq Nat.shiftLeft (fun u a b ↦ by
    change (u <<< a) <<< b = u <<< (a + b)
    simp only [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_assoc]) x sh 0xc00000

/-- Salted dynamic left-shift. -/
def sched_shlDynSalt (hSalt x sh : ℕ) : ℕ := sched_stfNat hSalt (fun v ↦ if Nat.ble sh 0xc00000
    then Nat.shiftLeft (sched_idSalt (Nat.add 2 hSalt) v) sh else sched_stfNat (Nat.add 3 hSalt)
    (fun v1 ↦ if Nat.ble sh (Nat.add 0xc00000 0xc00000) then Nat.shiftLeft (sched_idSalt
    (Nat.add 4 hSalt) v1) (Nat.sub sh 0xc00000) else sched_stfNat (Nat.add 5 hSalt) (fun v2 ↦
    Nat.shiftLeft (sched_idSalt (Nat.add 6 hSalt) v2) (Nat.sub sh (Nat.add 0xc00000 0xc00000)))
    (Nat.shiftLeft (sched_idSalt (Nat.add 7 hSalt) v1) 0xc00000)) (Nat.shiftLeft (sched_idSalt
    (Nat.add 8 hSalt) v) 0xc00000)) x

/-- Salted dynamic right-shift. -/
def sched_shrDynSalt (hSalt w sh : ℕ) : ℕ := if Nat.ble sh 0xc00000 then Nat.shiftRight
    (sched_idSalt (Nat.add 2 hSalt) w) sh else sched_stfNat (Nat.add 3 hSalt) (fun v1 ↦ if
    Nat.ble sh (Nat.add 0xc00000 0xc00000) then Nat.shiftRight (sched_idSalt (Nat.add 4 hSalt)
    v1) (Nat.sub sh 0xc00000) else sched_stfNat (Nat.add 5 hSalt) (fun v2 ↦ Nat.shiftRight
    (sched_idSalt (Nat.add 6 hSalt) v2) (Nat.sub sh (Nat.add 0xc00000 0xc00000)))
    (Nat.shiftRight (sched_idSalt (Nat.add 7 hSalt) v1) 0xc00000))
    (Nat.shiftRight (sched_idSalt (Nat.add 8 hSalt) w) 0xc00000)

/-- Bitmask `(1 <<< sh) - 1` built via `sched_shlDyn`. -/
def sched_maskForSh (sh : ℕ) : ℕ := Nat.sub (sched_shlDyn 1 sh) 1

/-- Salted low-`sh`-bit mask `w &&& ((1 <<< sh) - 1)`. -/
def sched_maskLowDynSalt (hSalt w sh : ℕ) : ℕ :=
  Nat.land (sched_idSalt hSalt w) (sched_maskForSh sh)

theorem sched_mask768_eq_mod (w : ℕ) :
    Nat.land w
      0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
        =
      Nat.mod w
        0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
          :=
  Nat.and_two_pow_sub_one_eq_mod w 768

/-- Fixed left-shift by `256` bits (`352 - 96` for `96`-bit pair products). -/
def sched_shl256 (x : ℕ) : ℕ := Nat.shiftLeft x 256
/-- Fixed left-shift by `304` bits (`352 - 48` for `48`-bit single leaves). -/
def sched_shl304 (x : ℕ) : ℕ := Nat.shiftLeft x 304
/-- Fixed left-shift by `768` bits (`1` SWAR lane). -/
def sched_shl768 (x : ℕ) : ℕ := Nat.shiftLeft x 768
/-- Fixed left-shift by `1024` bits (`256 + 768` for `m = 1` pair-leaf lane). -/
def sched_shl1024 (x : ℕ) : ℕ := Nat.shiftLeft x 1024
/-- Fixed left-shift by `1536` bits (`2` SWAR lanes). -/
def sched_shl1536 (x : ℕ) : ℕ := Nat.shiftLeft x 1536
/-- Fixed right-shift by `352` bits (`2 ^ 704 -> 2 ^ 352` tree truncation). -/
def sched_shrLimb (x : ℕ) : ℕ := Nat.shiftRight x 352
/-- Fixed right-shift by `384` bits (sign bit extraction in `roundSplit768`). -/
def sched_shr384 (x : ℕ) : ℕ := Nat.shiftRight x 384
/-- Fixed right-shift by `768` bits (`1` SWAR lane). -/
def sched_shr768 (x : ℕ) : ℕ := Nat.shiftRight x 768

theorem sched_shrLimb_eq (x : ℕ) : sched_shrLimb x = Nat.shiftRight x 352 := rfl
theorem sched_shr384_eq (x : ℕ) : sched_shr384 x = Nat.shiftRight x 384 := rfl
theorem sched_shr768_eq (x : ℕ) : sched_shr768 x = Nat.shiftRight x 768 := rfl

/-- Unsigned `(pos, neg)` packed `768`-bit polynomial pair. -/
structure PolyPN where
  pos : ℕ
  neg : ℕ

/-- Negate a `PolyPN` by swapping its `(pos, neg)` words (`0` arithmetic). -/
def negPN (pn : PolyPN) : PolyPN := ⟨pn.neg, pn.pos⟩

/-- Salted intermediate `(s, pos, neg)` returned by `sched_roundSplit768Masks`. -/
structure SaltedPN where
  s : ℕ
  pos : ℕ
  neg : ℕ

/-- Complex tournament tree node carrying `4` `PolyPN` channels (`pr, pi, qr, qi`) and error
`err`. -/
structure TreeNodeC where
  deg : ℕ
  salt : ℕ
  rep1 : ℕ
  prp : ℕ
  prn : ℕ
  pip : ℕ
  pin : ℕ
  qrp : ℕ
  qrn : ℕ
  qip : ℕ
  qin : ℕ
  err : ℕ

/-- Real-`P` `PolyPN` projection of `TreeNodeC`. -/
abbrev TreeNodeC.pr (nd : TreeNodeC) : PolyPN := ⟨nd.prp, nd.prn⟩
/-- Imaginary-`P` `PolyPN` projection of `TreeNodeC`. -/
abbrev TreeNodeC.pi (nd : TreeNodeC) : PolyPN := ⟨nd.pip, nd.pin⟩
/-- Real-`Q` `PolyPN` projection of `TreeNodeC`. -/
abbrev TreeNodeC.qr (nd : TreeNodeC) : PolyPN := ⟨nd.qrp, nd.qrn⟩
/-- Imaginary-`Q` `PolyPN` projection of `TreeNodeC`. -/
abbrev TreeNodeC.qi (nd : TreeNodeC) : PolyPN := ⟨nd.qip, nd.qin⟩

/-- Pack a list of `768`-bit lanes (`< 2 ^ 768`) into a single `ℕ`. -/
def pack768 : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.add x (Nat.shiftLeft (pack768 xs) 768)

/-- Reference coefficientwise addition on `List ℕ` for Kronecker proofs. -/
def sched_convAdd : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: sched_convAdd xs ys

/-- Reference Cauchy convolution on `List ℕ` for Kronecker proofs. -/
def sched_convNat : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: as, bs => sched_convAdd (bs.map (a * ·)) (0 :: sched_convNat as bs)

def sched_revStepAux (hSalt w : ℕ) (rec_lo rec_hi : ℕ → ℕ) (sh_lo sh_hi : ℕ) : ℕ :=
  let r_hi := sched_stfNat hSalt rec_hi (sched_shrDynSalt (Nat.add 1 hSalt) w sh_lo)
  let r_lo := sched_stfNat (Nat.add 2 hSalt) rec_lo (sched_maskLowDynSalt (Nat.add 3 hSalt) w sh_lo)
  Nat.add r_hi (sched_shlDynSalt (Nat.add 4 hSalt) r_lo sh_hi)

theorem sched_revStepAux_eq (hSalt w : ℕ) (rec_lo rec_hi : ℕ → ℕ) (sh_lo sh_hi : ℕ) :
    sched_revStepAux hSalt w rec_lo rec_hi sh_lo sh_hi =
      Nat.add (rec_hi (Nat.div w (2 ^ sh_lo)))
        (Nat.shiftLeft (rec_lo (Nat.mod w (2 ^ sh_lo))) sh_hi) := by
  have hshl : ∀ s x sh, sched_shlDynSalt s x sh = Nat.shiftLeft x sh := fun s x sh ↦ by
    rw [show sched_shlDynSalt s x sh = sched_shlDyn x sh by
      unfold sched_shlDynSalt sched_shlDyn sched_idSalt; simp only [sched_stfNat_eq,
        sched_tfNat_eq]]
    exact sched_shlDyn_eq x sh
  have hshr : ∀ s x sh, sched_shrDynSalt s x sh = Nat.div x (2 ^ sh) := fun s x sh ↦ by
    unfold sched_shrDynSalt sched_idSalt; simp only [sched_stfNat_eq]
    rw [sched_dynChunk_eq Nat.shiftRight (fun u a b ↦ by
      change (u >>> a) >>> b = u >>> (a + b)
      simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]) x sh 0xc00000]
    exact Nat.shiftRight_eq_div_pow x sh
  have hmsk : ∀ s x sh, sched_maskLowDynSalt s x sh = Nat.mod x (2 ^ sh) := fun s x sh ↦ by
    unfold sched_maskLowDynSalt sched_maskForSh sched_idSalt; rw [sched_shlDyn_eq]
    change x &&& (1 <<< sh - 1) = x % 2 ^ sh
    rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  simp only [sched_revStepAux, sched_stfNat_eq, hshr, hmsk, hshl]

/-- Depth-`d` binary-split `768`-bit lane reversal helper. -/
def sched_revBin768Aux (d : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ → ℕ → ℕ)
    (fun s0 n0 w0 ↦
      @Nat.casesOn (fun _ ↦ ℕ) n0 0 (fun n0' ↦
        @Nat.casesOn (fun _ ↦ ℕ) n0'
          (Nat.land (sched_idSalt (Nat.add 1 s0) w0)
            0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
          (fun _ ↦ 0)))
    (fun _ ih s1 n1 w1 ↦
      @Nat.casesOn (fun _ ↦ ℕ) n1 0 (fun n1' ↦
        @Nat.casesOn (fun _ ↦ ℕ) n1'
          (Nat.land (sched_idSalt (Nat.add 1 s1) w1)
            0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
          (fun k ↦
            let m := Nat.add 2 k
            let h := Nat.div m 2
            let h_hi := Nat.sub m h
            let sh_lo := Nat.mul 768 h
            let sh_hi := Nat.mul 768 h_hi
            sched_revStepAux (Nat.mul 8 s1) w1
              (ih (Nat.mul 2 s1) h)
              (ih (Nat.add 1 (Nat.mul 2 s1)) h_hi)
              sh_lo sh_hi)))
    d

/-- Reverse `n ≤ 2 ^ d` `768`-bit lanes inside `w` in `O(n log n)` bit operations. -/
def revBin768 (d n w : ℕ) : ℕ := sched_tfNat (fun s0 ↦ sched_revBin768Aux d s0 n w)
    (Nat.add 1 (Nat.land w 0xfffffff))

/-- Reverse `n ≤ 2 ^ d` `768`-bit lanes in both `(pos, neg)` words of a `PolyPN`. -/
def revPN (d n : ℕ) (pn : PolyPN) : PolyPN := ⟨revBin768 d n pn.pos, revBin768 d n pn.neg⟩

/-- `2 ^ 768` as a pre-parsed hexadecimal literal. -/
def sched_pow768 : ℕ :=
  0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem sched_pow768_eq_pow : sched_pow768 = 2 ^ 768 := rfl
theorem sched_pow768_pos : 0 < sched_pow768 := Nat.ble_eq.mp rfl
theorem sched_shiftLeft_768_eq (x : ℕ) : (x <<< 768) = sched_pow768 * x := by
  rw [sched_pow768_eq_pow, Nat.shiftLeft_eq, Nat.mul_comm]

theorem sched_pack768_nil : pack768 [] = 0 := rfl
theorem sched_pack768_cons (x : ℕ) (xs : List ℕ) :
    pack768 (x :: xs) = x + (pack768 xs <<< 768) := rfl

theorem sched_pack768_mul (c : ℕ) : ∀ (xs : List ℕ),
    pack768 (xs.map (Nat.mul c)) = c * pack768 xs
  | [] => (Nat.mul_zero c).symm
  | x :: xs => by
      simp only [List.map, sched_pack768_cons, sched_pack768_mul c xs, sched_shiftLeft_768_eq,
        Nat.mul_eq]
      ring

theorem sched_pack768_rep_mul (n c : ℕ) :
    Nat.mul (pack768 (List.replicate n 1)) c = pack768 (List.replicate n c) := by
  have hm : (List.replicate n 1).map (Nat.mul c) = List.replicate n c := by
    rw [List.map_replicate]; simp
  rw [Nat.mul_eq, Nat.mul_comm, ← sched_pack768_mul c (List.replicate n 1), hm]

theorem sched_pack768_mono : ∀ (ys xs : List ℕ),
    List.Forall₂ (· ≤ ·) ys xs → pack768 ys ≤ pack768 xs
  | [], [], _ => Nat.le_refl 0
  | y :: ys, x :: xs, List.Forall₂.cons hxy hrest => by
      have ih := sched_pack768_mono ys xs hrest
      simp only [sched_pack768_cons, sched_shiftLeft_768_eq]
      exact Nat.add_le_add hxy (Nat.mul_le_mul_left sched_pow768 ih)

theorem sched_pack768_sub : ∀ (xs ys : List ℕ), List.Forall₂ (· ≤ ·) ys xs →
    pack768 (List.zipWith Nat.sub xs ys) = pack768 xs - pack768 ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, List.Forall₂.cons hxy hrest => by
      have ih := sched_pack768_sub xs ys hrest
      have hmle : sched_pow768 * pack768 ys ≤ sched_pow768 * pack768 xs :=
        Nat.mul_le_mul_left sched_pow768 (sched_pack768_mono ys xs hrest)
      simp only [List.zipWith, sched_pack768_cons, ih, sched_shiftLeft_768_eq, Nat.sub_eq,
        Nat.mul_sub_left_distrib]
      omega

theorem sched_pack768_convAdd : ∀ (xs ys : List ℕ),
    pack768 (sched_convAdd xs ys) = pack768 xs + pack768 ys
  | [], ys => by simp [sched_convAdd, sched_pack768_nil]
  | x :: xs, [] => by simp [sched_convAdd, sched_pack768_nil]
  | x :: xs, y :: ys => by
      simp only [sched_convAdd, sched_pack768_cons, sched_pack768_convAdd xs ys,
        sched_shiftLeft_768_eq]
      ring

theorem sched_pack768_zipAdd : ∀ (xs ys : List ℕ), xs.length = ys.length →
    pack768 (List.zipWith Nat.add xs ys) = pack768 xs + pack768 ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, hlen => by
      simp only [List.zipWith, sched_pack768_cons,
        sched_pack768_zipAdd xs ys (Nat.succ.inj hlen), sched_shiftLeft_768_eq, Nat.add_eq]
      ring

theorem sched_pack768_convNat : ∀ (as bs : List ℕ),
    pack768 (sched_convNat as bs) = pack768 as * pack768 bs
  | [], _ => by simp [sched_convNat, sched_pack768_nil]
  | a :: as, bs => by
      have hm : bs.map (a * ·) = bs.map (Nat.mul a) := rfl
      simp only [sched_convNat, sched_pack768_convAdd, hm, sched_pack768_mul,
        sched_pack768_cons, sched_pack768_convNat as bs, sched_shiftLeft_768_eq]
      ring

theorem sched_pack768_lt : ∀ (xs : List ℕ), (∀ x ∈ xs, x < sched_pow768) →
    pack768 xs < (1 <<< (768 * xs.length))
  | [], _ => by
      simp only [sched_pack768_nil, List.length_nil, Nat.mul_zero, Nat.shiftLeft_zero]
      exact Nat.zero_lt_one
  | x :: xt, hxs => by
      have hx : x + 1 ≤ sched_pow768 := hxs x List.mem_cons_self
      have h1 := Nat.mul_le_mul_left sched_pow768
        (sched_pack768_lt xt fun a ha ↦ hxs a (List.mem_cons_of_mem x ha))
      rw [List.length_cons, show 768 * (xt.length + 1) = 768 * xt.length + 768 by omega,
          show (1 <<< (768 * xt.length + 768)) = ((1 <<< (768 * xt.length)) <<< 768) by
            simp only [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_assoc],
          sched_shiftLeft_768_eq, sched_pack768_cons, sched_shiftLeft_768_eq]
      change sched_pow768 * (pack768 xt + 1) ≤ _ at h1
      have h2 : sched_pow768 * (pack768 xt + 1) = sched_pow768 * pack768 xt + sched_pow768 := by
        ring
      omega

theorem sched_pack768_append : ∀ (xs ys : List ℕ),
    pack768 (xs ++ ys) = pack768 xs + (pack768 ys <<< (768 * xs.length))
  | [], ys => by simp [sched_pack768_nil]
  | x :: xt, ys => by
      simp only [List.cons_append, sched_pack768_cons, sched_pack768_append xt ys, List.length_cons]
      rw [show 768 * (xt.length + 1) = 768 * xt.length + 768 by omega,
          show (pack768 ys <<< (768 * xt.length + 768)) = ((pack768 ys <<< (768 * xt.length)) <<<
            768) by
            simp only [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_assoc],
          sched_shiftLeft_768_eq, sched_shiftLeft_768_eq, sched_shiftLeft_768_eq]
      ring

theorem sched_mod_div_768_mul_add (n a b : ℕ) (ha : a < 1 <<< (768 * n)) :
    Nat.mod (a + (b <<< (768 * n))) (2 ^ (768 * n)) = a ∧
    Nat.div (a + (b <<< (768 * n))) (2 ^ (768 * n)) = b := by
  change (a + (b <<< (768 * n))) % 2 ^ (768 * n) = a ∧
    (a + (b <<< (768 * n))) / 2 ^ (768 * n) = b
  rw [Nat.one_shiftLeft] at ha
  rw [Nat.shiftLeft_eq, Nat.mul_comm b]
  exact ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha],
         by rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos (768 * n)),
                Nat.div_eq_of_lt ha, Nat.zero_add]⟩

theorem revBin768_spec (d : ℕ) : ∀ (n : ℕ) (xs : List ℕ), n ≤ 2 ^ d → xs.length = n →
    (∀ x ∈ xs, x < 2 ^ 768) → revBin768 d n (pack768 xs) = pack768 xs.reverse := by
  have h1_eq : ∀ d0 s x : ℕ, x < sched_pow768 →
      sched_revBin768Aux d0 s 1 (pack768 [x]) = pack768 [x] := fun d0 s x hx ↦ by
    cases d0 <;> (
      change Nat.land (sched_idSalt (Nat.add 1 s) (x + (0 <<< 768))) _ = x + (0 <<< 768)
      rw [sched_idSalt_eq, sched_mask768_eq_mod, Nat.zero_shiftLeft, Nat.add_zero]
      exact Nat.mod_eq_of_lt hx)
  have haux : ∀ d : ℕ, ∀ (s n : ℕ) (xs : List ℕ), n ≤ 2 ^ d → xs.length = n →
      (∀ x ∈ xs, x < sched_pow768) → sched_revBin768Aux d s n (pack768 xs) = pack768 xs.reverse :=
        by
    intro d; induction d with
    | zero =>
        intro s n xs hle hlen hxs
        rcases xs with _ | ⟨x, _ | _⟩
        · cases hlen; rfl
        · cases hlen; exact h1_eq 0 s x (hxs x List.mem_cons_self)
        · simp only [List.length_cons] at hlen; omega
    | succ d ih =>
        intro s n xs hle hlen hxs
        rcases n with _ | _ | k
        · cases List.length_eq_zero_iff.mp hlen; rfl
        · rcases xs with _ | ⟨x, _ | _⟩
          · cases hlen
          · exact h1_eq (d + 1) s x (hxs x List.mem_cons_self)
          · simp only [List.length_cons] at hlen; omega
        · have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
          let h := (2 + k) / 2
          have hlen1 : (xs.take h).length = h := by rw [List.length_take]; omega
          have hlen2 : (xs.drop h).length = (2 + k) - h := by rw [List.length_drop]; omega
          have hxs1 : ∀ a ∈ xs.take h, a < sched_pow768 := fun a ha ↦
            hxs a (List.mem_of_mem_take ha)
          have hxs2 : ∀ a ∈ xs.drop h, a < sched_pow768 := fun a ha ↦
            hxs a (List.mem_of_mem_drop ha)
          have hp : pack768 xs = pack768 (xs.take h) + (pack768 (xs.drop h) <<< (768 * h)) := by
            conv_lhs => rw [← List.take_append_drop h xs]; rw [sched_pack768_append, hlen1]
          rcases sched_mod_div_768_mul_add h (pack768 (xs.take h)) (pack768 (xs.drop h))
            (by simpa [hlen1] using sched_pack768_lt (xs.take h) hxs1) with ⟨hlo, hhi⟩
          let m0 := Nat.add 2 k
          let h0 := Nat.div m0 2
          change sched_revStepAux (Nat.mul 8 s) (pack768 xs)
            (sched_revBin768Aux d (Nat.mul 2 s) h0)
            (sched_revBin768Aux d (Nat.add 1 (Nat.mul 2 s)) (Nat.sub m0 h0))
            (Nat.mul 768 h0) (Nat.mul 768 (Nat.sub m0 h0)) = pack768 xs.reverse
          simp only [m0, h0, sched_revStepAux_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
          change sched_revBin768Aux d (1 + 2 * s) ((2 + k) - h) (Nat.div (pack768 xs) (2 ^ (768 *
            h))) +
            Nat.shiftLeft
              (sched_revBin768Aux d (2 * s) h (Nat.mod (pack768 xs) (2 ^ (768 * h))))
              (768 * ((2 + k) - h)) = _
          rw [hp, hlo, hhi, ih _ _ _ (by omega) hlen2 hxs2, ih _ _ _ (by omega) hlen1 hxs1]
          conv_rhs => rw [← List.take_append_drop h xs, List.reverse_append,
            sched_pack768_append, List.length_reverse, hlen2]
          rfl
  intro n xs hle hlen hxs; unfold revBin768
  exact (sched_tfNat_eq _ _).trans
    (haux d _ n xs hle hlen fun x hx ↦ sched_pow768_eq_pow.symm ▸ hxs x hx)

/-- Tree fractional scale `2 ^ 352`. -/
def sched_sTree : ℕ :=
  0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- Pre-shift lane midpoint bias `2 ^ 736`. -/
def sched_bMid : ℕ :=
  0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- Post-`shr 352` lane midpoint bias `2 ^ 384`. -/
def sched_bQ : ℕ :=
  0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- Lane mask `2 ^ 352 * (2 ^ 386 - 1)` clearing low `352` fractional bits before `shr 352`. -/
def sched_keepLane : ℕ :=
  0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- `385`-bit lane mask `2 ^ 385 - 1`. -/
def schedAux : ℕ :=
  0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
/-- High-bit overflow guard mask `2 ^ 353 * (2 ^ 32 - 1)` ensuring `< 2 ^ 353` per lane. -/
def sched_clampHiLane : ℕ :=
  0x1fffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/-- `2`-lane `rep1` constant `1 + 2 ^ 768` for degree-`1` leaves. -/
def sched_rep2One : ℕ :=
  0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001
/-- `3`-lane `rep1` constant `1 + 2 ^ 768 + 2 ^ 1536` for degree-`2` pair leaves. -/
def sched_rep3One : ℕ :=
  0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001

theorem sched_sTree_eq : sched_sTree = 2 ^ 352 := rfl
theorem sched_bMid_eq : sched_bMid = 2 ^ 736 := rfl

theorem sched_and_shiftLeft_768_add (a b x y : ℕ) (ha : a < sched_pow768) (hb : b < sched_pow768) :
    (a + (x <<< 768)) &&& (b + (y <<< 768)) = (a &&& b) + ((x &&& y) <<< 768) := by
  rw [sched_shiftLeft_768_eq x, sched_shiftLeft_768_eq y, sched_shiftLeft_768_eq (x &&& y)]
  rw [sched_pow768_eq_pow] at ha hb ⊢
  have hab : (a &&& b) < 2 ^ 768 := Nat.and_lt_two_pow a hb
  rw [Nat.add_comm a, Nat.add_comm b, Nat.add_comm (a &&& b)]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ ha,
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hab]
  by_cases hi : i < 768 <;> simp [hi]

theorem sched_pack768_and : ∀ (xs ms : List ℕ),
    List.Forall₂ (fun x m ↦ x < sched_pow768 ∧ m < sched_pow768) xs ms →
    pack768 (List.zipWith (· &&& ·) xs ms) = pack768 xs &&& pack768 ms
  | [], [], _ => rfl
  | x :: xs, m :: ms, List.Forall₂.cons ⟨hx, hm⟩ hrest => by
      simp only [List.zipWith, sched_pack768_cons, sched_pack768_and xs ms hrest]
      exact (sched_and_shiftLeft_768_add x m (pack768 xs) (pack768 ms) hx hm).symm

theorem sched_mask_mid_lane (sh k z : ℕ) (hz : z < 2 ^ (sh + k)) :
    z &&& (2 ^ sh * (2 ^ k - 1)) = 2 ^ sh * (z >>> sh) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
      Nat.testBit_two_pow_mul, Nat.testBit_shiftRight]
  by_cases h1 : i ≥ sh
  · by_cases h2 : i < sh + k
    · simp [h1, show i - sh < k by omega, show sh + (i - sh) = i by omega]
    · have hi_lt : z < 2 ^ i :=
        hz.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : sh + k ≤ i))
      simp [h1, show ¬(i - sh < k) by omega, show sh + (i - sh) = i by omega,
        Nat.testBit_lt_two_pow hi_lt]
  · simp [h1]

theorem sched_mask_keep_lane (z : ℕ) (hz : z < 2 ^ 738) :
    z &&& sched_keepLane = 2 ^ 352 * (z >>> 352) :=
  (rfl : sched_keepLane = 2 ^ 352 * (2 ^ 386 - 1)) ▸ sched_mask_mid_lane 352 386 z hz

theorem sched_mask_bq_lane (q : ℕ) (hq : q < 2 ^ 385) :
    q &&& sched_bQ = 2 ^ 384 * (q >>> 384) := sched_mask_mid_lane 384 1 q hq

theorem sched_lane_split_spec (q : ℕ) (hq : q < 2 ^ 385) :
    let s := q >>> 384
    let mp := schedAux * s
    let mn := schedAux - mp
    let fp := (q &&& mp) - (sched_bQ &&& mp)
    let fn := (sched_bQ &&& mn) - (q &&& mn)
    mp ≤ schedAux ∧ (sched_bQ &&& mp) ≤ (q &&& mp) ∧ (q &&& mn) ≤ (sched_bQ &&& mn) ∧
    fp < 2 ^ 385 ∧ fn < 2 ^ 385 ∧ ((fp : ℤ) - (fn : ℤ) = (q : ℤ) - (2 ^ 384 : ℤ)) := by
  have hbq_lt : (2 ^ 384 : ℕ) < 2 ^ 385 := Nat.ble_eq.mp rfl
  have hp385 : (2 ^ 385 : ℕ) = 2 * 2 ^ 384 := rfl
  dsimp only
  by_cases hge : 2 ^ 384 ≤ q
  · have hs : q >>> 384 = 1 := Nat.shiftRight_eq_div_pow q 384 ▸
      Nat.le_antisymm (by omega) (Nat.div_pos hge (Nat.two_pow_pos 384))
    have hm385 : schedAux = 2 ^ 385 - 1 := rfl
    have hbq : sched_bQ = 2 ^ 384 := rfl
    simp only [hs, Nat.mul_one, Nat.sub_self, Nat.and_zero, hm385, hbq,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hbq_lt]
    exact ⟨le_rfl, hge, le_rfl, (Nat.sub_le _ _).trans_lt hq, Nat.two_pow_pos 385, by omega⟩
  · have hs : q >>> 384 = 0 := Nat.shiftRight_eq_div_pow q 384 ▸ Nat.div_eq_of_lt (by omega)
    have hm385 : schedAux = 2 ^ 385 - 1 := rfl
    have hbq : sched_bQ = 2 ^ 384 := rfl
    simp only [hs, Nat.mul_zero, Nat.sub_zero, Nat.and_zero, hm385, hbq,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hbq_lt]
    exact ⟨Nat.zero_le _, le_rfl, by omega, Nat.two_pow_pos 385,
      (Nat.sub_le _ _).trans_lt hbq_lt, by omega⟩

/-- Final overflow-guard check of `sched_roundSplit768Masks`. -/
def sched_roundSplit768Finish (s rep_clamp fp fn : ℕ) : Option SaltedPN := if Nat.beq (Nat.add
    (Nat.land (sched_idSalt s fp) rep_clamp) (Nat.land (sched_idSalt s fn) rep_clamp)) 0 then
    some ⟨s, fp, fn⟩ else none

/-- Negative-lane extraction step of `sched_roundSplit768Masks`. -/
def sched_roundSplit768Step2 (s rep_clamp rep_bq q_w mn fp : ℕ) : Option SaltedPN :=
    sched_stfOpt s (sched_roundSplit768Finish s rep_clamp fp) (Nat.sub (Nat.land (sched_idSalt s
    rep_bq) mn) (Nat.land (sched_idSalt s q_w) mn))

/-- Positive-lane extraction step of `sched_roundSplit768Masks`. -/
def sched_roundSplit768Step1c (s rep_clamp rep_bq q_w mp mn : ℕ) : Option SaltedPN :=
    sched_stfOpt s (sched_roundSplit768Step2 s rep_clamp rep_bq q_w mn) (Nat.sub (Nat.land
    (sched_idSalt s q_w) mp) (Nat.land (sched_idSalt s rep_bq) mp))

/-- Negative-mask complement step of `sched_roundSplit768Masks`. -/
def sched_roundSplit768Step1b (s rep_bq repAux rep_clamp q_w mp : ℕ) : Option SaltedPN :=
    sched_stfOpt s (sched_roundSplit768Step1c s rep_clamp rep_bq q_w mp) (Nat.sub repAux mp)

/-- Sign-bit mask step of `sched_roundSplit768Masks`. -/
def sched_roundSplit768Step1 (s rep_bq repAux rep_clamp q_w : ℕ) : Option SaltedPN :=
  sched_stfOpt s (sched_roundSplit768Step1b s rep_bq repAux rep_clamp q_w)
    (Nat.mul (sched_shr384 (Nat.land (sched_idSalt s q_w) rep_bq)) schedAux)

/-- Salted pre-multiplied-mask `roundSplit768` helper used inside tournament merges. -/
def sched_roundSplit768Masks (s rep_bmid rep_keep rep_bq repAux rep_clamp u_pos u_neg : ℕ) :
    Option SaltedPN := sched_stfOpt s (sched_roundSplit768Step1 s rep_bq repAux rep_clamp)
    (sched_shrLimb (Nat.land (Nat.sub (Nat.add (sched_idSalt s u_pos) rep_bmid) u_neg) rep_keep))

/-- Round and split a `2 ^ 704`-scaled `(u_pos, u_neg)` SWAR pair back into `2 ^ 352`-scaled
`PolyPN`. -/
def roundSplit768 (rep1 u_pos u_neg : ℕ) : Option PolyPN :=
  let rep_bmid := Nat.mul rep1 sched_bMid
  let rep_keep := Nat.mul rep1 sched_keepLane
  let rep_bq := Nat.mul rep1 sched_bQ
  let repAux := Nat.mul rep1 schedAux
  let rep_clamp := Nat.mul rep1 sched_clampHiLane
  sched_tf1 (fun q_w ↦
    sched_tf1 (fun mp ↦
      sched_tf1 (fun mn ↦
        sched_tf1 (fun fp ↦
          sched_tf1 (fun fn ↦
            if Nat.beq (Nat.add (Nat.land fp rep_clamp) (Nat.land fn rep_clamp)) 0 then
              some ⟨fp, fn⟩
            else none)
          (Nat.sub (Nat.land rep_bq mn) (Nat.land q_w mn)))
        (Nat.sub (Nat.land q_w mp) (Nat.land rep_bq mp)))
      (Nat.sub repAux mp))
    (Nat.mul (sched_shr384 (Nat.land q_w rep_bq)) schedAux))
  (sched_shrLimb (Nat.land (Nat.sub (Nat.add u_pos rep_bmid) u_neg) rep_keep))

theorem sched_roundSplit768Masks_spec_bridge (salt rep1 u_pos u_neg : ℕ) (x : SaltedPN) (h :
    sched_roundSplit768Masks salt (Nat.mul rep1 sched_bMid) (Nat.mul rep1 sched_keepLane)
    (Nat.mul rep1 sched_bQ) (Nat.mul rep1 schedAux) (Nat.mul rep1 sched_clampHiLane) u_pos
    u_neg = some x) : roundSplit768 rep1 u_pos u_neg = some ⟨x.pos, x.neg⟩ := by
  unfold sched_roundSplit768Masks sched_roundSplit768Step1 sched_roundSplit768Step1b
    sched_roundSplit768Step1c sched_roundSplit768Step2 sched_roundSplit768Finish sched_idSalt at h
  simp only [sched_stfOpt_eq] at h
  simp only [roundSplit768, sched_tf1_eq]
  split at h
  · rename_i hcond
    injection h with hx; subst hx
    simp only [hcond, ↓reduceIte]
  · cases h

/-- Validity predicate for a `2 ^ 352`-scaled `768`-bit packed `PolyPN` of degree `L`. -/
def PolyPNValid (L : ℕ) (pn : PolyPN) (f_hat : ℕ → ℝ) : Prop := ∃ vp vn : List ℕ, vp.length =
    L + 1 ∧ vn.length = L + 1 ∧ (∀ v ∈ vp, v < 2 ^ 353) ∧ (∀ v ∈ vn, v < 2 ^ 353) ∧ pn.pos =
    pack768 vp ∧ pn.neg = pack768 vn ∧ ∀ m, f_hat m = if m ≤ L then
    ((vp.getD m 0 : ℝ) - (vn.getD m 0 : ℝ)) / (2 ^ 352 : ℝ) else 0

/-- Validity predicate for a `TreeNodeC` approximating `gateListTransferPQ 48 gs`. -/
def TreeNodeCValid (gs : List DyadicSu2Gate) (nd : TreeNodeC) : Prop := nd.deg = gs.length ∧ 1
    ≤ nd.deg ∧ nd.err ≤ 2 ^ 352 ∧ nd.rep1 = pack768 (List.replicate (nd.deg + 1) 1) ∧ ∃ P_hat
    Q_hat : PolyC, PolyPNValid nd.deg nd.pr P_hat.re ∧ PolyPNValid nd.deg nd.pi P_hat.im ∧
    PolyPNValid nd.deg nd.qr Q_hat.re ∧ PolyPNValid nd.deg nd.qi Q_hat.im ∧ PolyCApprox P_hat
    (gateListTransferPQ 48 gs).1 ((nd.err : ℝ) / (2 ^ 352 : ℝ)) ∧ PolyCApprox Q_hat
    (gateListTransferPQ 48 gs).2 ((nd.err : ℝ) / (2 ^ 352 : ℝ))

theorem sched_two_pow_pos_real (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos zero_lt_two n

theorem sched_min_self_nat (n : ℕ) : min n n = n := by omega

theorem sched_getD_cons_succ {α : Type} (x : α) (xs : List α) (m : ℕ) (d : α) :
    (x :: xs).getD (m + 1) d = xs.getD m d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]

theorem sched_getD_eq_zero_of_ge : ∀ (xs : List ℕ) (m : ℕ), xs.length ≤ m → xs.getD m 0 = 0
  | [], _, _ => by simp [List.getD_eq_getElem?_getD]
  | _ :: xs, m + 1, h => by
      rw [sched_getD_cons_succ]
      exact sched_getD_eq_zero_of_ge xs m (by simpa using h)

theorem sched_getD_lt_of_forall_lt {B : ℕ} (hB : 0 < B) :
    ∀ (xs : List ℕ) (m : ℕ), (∀ x ∈ xs, x < B) → xs.getD m 0 < B
  | [], _, _ => by simp [List.getD_eq_getElem?_getD, hB]
  | x :: _, 0, h => by simpa [List.getD_eq_getElem?_getD] using h x List.mem_cons_self
  | x :: xs, m + 1, h => by
      rw [sched_getD_cons_succ]
      exact sched_getD_lt_of_forall_lt hB xs m (fun a ha ↦ h a (List.mem_cons_of_mem x ha))

theorem sched_polyPNValid_supp {L : ℕ} {pn : PolyPN} {f_hat : ℕ → ℝ}
    (h : PolyPNValid L pn f_hat) : ta_PolySupp L f_hat := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hf⟩
  intro m hm
  have hnm : ¬(m ≤ L) := Nat.not_le_of_gt hm
  simp only [hf m, hnm, ↓reduceIte]

theorem sched_polyPNValid_abs_le_two {L : ℕ} {pn : PolyPN} {f_hat : ℕ → ℝ}
    (h : PolyPNValid L pn f_hat) : ∀ m, |f_hat m| ≤ 2 := by
  rcases h with ⟨fp, fn, _, _, hfp, hfn, _, _, hf⟩
  have hbnd : ∀ xs : List ℕ, (∀ v ∈ xs, v < 2 ^ 353) → ∀ m,
      (xs.getD m 0 : ℝ) ≤ (2 : ℝ) * (2 ^ 352 : ℝ) := fun xs hxs m ↦ by
    have hc : (xs.getD m 0 : ℝ) ≤ ((2 ^ 353 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_lt (sched_getD_lt_of_forall_lt (Nat.two_pow_pos 353) xs m hxs)
    rw [Nat.cast_pow, Nat.cast_ofNat, show (353 : ℕ) = 352 + 1 from rfl, pow_succ'] at hc
    exact hc
  intro m; rw [hf m]
  by_cases hm : m ≤ L
  · simp only [hm, ↓reduceIte]
    have hp := hbnd fp hfp m
    have hn := hbnd fn hfn m
    have hp0 : (0 : ℝ) ≤ fp.getD m 0 := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ fn.getD m 0 := Nat.cast_nonneg _
    have hS : (0 : ℝ) < (2 : ℝ) ^ 352 := sched_two_pow_pos_real 352
    generalize (2 : ℝ) ^ 352 = S at hp hn hS ⊢
    rw [abs_div, abs_of_pos hS, div_le_iff₀ hS, abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  · simp [hm]

theorem negPN_valid {L : ℕ} {pn : PolyPN} {f_hat : ℕ → ℝ}
    (h : PolyPNValid L pn f_hat) : PolyPNValid L (negPN pn) (ta_polyNeg f_hat) := by
  rcases h with ⟨vp, vn, hvp_len, hvn_len, hvp_lt, hvn_lt, hpos, hneg, hf⟩
  refine ⟨vn, vp, hvn_len, hvp_len, hvn_lt, hvp_lt, hneg, hpos, fun m ↦ ?_⟩
  unfold ta_polyNeg; rw [hf m]
  by_cases hm : m ≤ L <;> simp only [hm, ↓reduceIte] <;> ring

theorem revPN_valid {d L : ℕ} {pn : PolyPN} {f_hat : ℕ → ℝ}
    (hd : L + 1 ≤ 2 ^ d) (h : PolyPNValid L pn f_hat) :
    PolyPNValid L (revPN d (L + 1) pn) (ta_polyRev L f_hat) := by
  have hrev_getD : ∀ (xs : List ℕ) (m : ℕ), m < xs.length →
      xs.reverse.getD m 0 = xs.getD (xs.length - 1 - m) 0 := by
    have happ : ∀ (as bs : List ℕ) (m : ℕ),
        (as ++ bs).getD m 0 = if m < as.length then as.getD m 0 else bs.getD (m - as.length) 0 := by
      intro as; induction as with
      | nil => simp
      | cons _ tail ih =>
          intro bs m; rcases m with _ | m'
          · simp [List.getD_eq_getElem?_getD]
          · simp only [List.cons_append, sched_getD_cons_succ, List.length_cons,
              Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub, ih bs m']
    intro xs; induction xs with
    | nil => intro _ hm; nomatch hm
    | cons _ tail ih =>
        intro m hm; rw [List.reverse_cons, happ, List.length_reverse]
        by_cases hlt : m < tail.length
        · simp only [hlt, ↓reduceIte, ih m hlt, List.length_cons,
            show tail.length + 1 - 1 - m = (tail.length - 1 - m) + 1 by omega, sched_getD_cons_succ]
        · obtain rfl : m = tail.length := by
            simp only [List.length_cons] at hm
            omega
          simp [List.getD_eq_getElem?_getD]
  rcases h with ⟨vp, vn, hvp_len, hvn_len, hvp_lt, hvn_lt, hpos, hneg, hf⟩
  refine ⟨vp.reverse, vn.reverse, by simp [hvp_len], by simp [hvn_len],
    fun x hx ↦ hvp_lt x (List.mem_reverse.mp hx), fun x hx ↦ hvn_lt x (List.mem_reverse.mp hx),
    by simp [revPN, hpos, revBin768_spec d (L + 1) vp hd hvp_len
         fun x hx ↦ (hvp_lt x hx).trans (Nat.ble_eq.mp rfl)],
    by simp [revPN, hneg, revBin768_spec d (L + 1) vn hd hvn_len
         fun x hx ↦ (hvn_lt x hx).trans (Nat.ble_eq.mp rfl)],
    fun m ↦ ?_⟩
  unfold ta_polyRev
  by_cases hm : m ≤ L
  · simp only [hm, ↓reduceIte, hf (L - m), show L - m ≤ L by omega,
      hrev_getD vp m (by omega), hrev_getD vn m (by omega), hvp_len, hvn_len,
      Nat.add_sub_cancel]
  · simp only [hm, ↓reduceIte]

theorem sched_convAdd_nil_right (xs : List ℕ) : sched_convAdd xs [] = xs := by
  cases xs <;> rfl

theorem sched_convAdd_len : ∀ (xs ys : List ℕ),
    (sched_convAdd xs ys).length = max xs.length ys.length
  | [], ys => by simp [sched_convAdd]
  | x :: xs, [] => by simp [sched_convAdd]
  | x :: xs, y :: ys => by
      simp only [sched_convAdd, List.length_cons, sched_convAdd_len xs ys]
      omega

theorem sched_convNat_len : ∀ (dr dl : ℕ) (as bs : List ℕ),
    as.length = dr + 1 → bs.length = dl + 1 →
    (sched_convNat as bs).length = dr + dl + 1
  | _, _, [], _, ha, _ => nomatch ha
  | 0, _, [_], _ :: bt, _, hb => by
      simp [sched_convNat, sched_convAdd, sched_convAdd_nil_right] at hb ⊢; omega
  | dr + 1, dl, _ :: a2 :: at', bs, ha, hb => by
      have ih := sched_convNat_len dr dl (a2 :: at') bs (Nat.succ.inj ha) hb
      rw [sched_convNat, sched_convAdd_len, List.length_map, List.length_cons, hb, ih]
      omega

theorem sched_convAdd_mem_le {Bx By : ℕ} : ∀ (xs ys : List ℕ),
    (∀ x ∈ xs, x ≤ Bx) → (∀ y ∈ ys, y ≤ By) →
    ∀ z ∈ sched_convAdd xs ys, z ≤ Bx + By
  | [], ys, _, hy, z, hz => by have := hy z hz; omega
  | x :: xs, [], hx, _, z, hz => by
      simp only [sched_convAdd_nil_right] at hz
      have := hx z hz; omega
  | x :: xs, y :: ys, hx, hy, z, hz => by
      simp only [sched_convAdd, List.mem_cons] at hz
      rcases hz with rfl | hmem
      · exact Nat.add_le_add (hx x List.mem_cons_self) (hy y List.mem_cons_self)
      · exact sched_convAdd_mem_le xs ys (fun a ha ↦ hx a (List.mem_cons_of_mem x ha))
          (fun b hb ↦ hy b (List.mem_cons_of_mem y hb)) z hmem

theorem sched_convNat_mem_le {Ba Bb : ℕ} : ∀ (as bs : List ℕ),
    (∀ a ∈ as, a ≤ Ba) → (∀ b ∈ bs, b ≤ Bb) →
    ∀ z ∈ sched_convNat as bs, z ≤ as.length * (Ba * Bb)
  | [], _, _, _, _, hz => nomatch hz
  | a :: as, bs, ha, hb, z, hz => by
      have hm1 : ∀ u ∈ bs.map (a * ·), u ≤ Ba * Bb := by
        intro u hu
        rcases List.mem_map.mp hu with ⟨b, hbm, rfl⟩
        exact Nat.mul_le_mul (ha a List.mem_cons_self) (hb b hbm)
      have hm2 : ∀ v ∈ (0 : ℕ) :: sched_convNat as bs, v ≤ as.length * (Ba * Bb) := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hvm
        · exact Nat.zero_le _
        · exact sched_convNat_mem_le as bs (fun x hx ↦ ha x (List.mem_cons_of_mem a hx)) hb v hvm
      have hle := sched_convAdd_mem_le (bs.map (a * ·)) (0 :: sched_convNat as bs) hm1 hm2 z hz
      have hlen : (a :: as).length * (Ba * Bb) = Ba * Bb + as.length * (Ba * Bb) := by
        rw [List.length_cons]; ring
      omega

theorem sched_convAdd_getD : ∀ (xs ys : List ℕ) (m : ℕ),
    (sched_convAdd xs ys).getD m 0 = xs.getD m 0 + ys.getD m 0
  | [], ys, m => by simp [sched_convAdd]
  | x :: xs, [], m => by simp [sched_convAdd_nil_right]
  | x :: xs, y :: ys, 0 => by simp [sched_convAdd, List.getD_eq_getElem?_getD]
  | x :: xs, y :: ys, m + 1 => by
      simp only [sched_convAdd, sched_getD_cons_succ, sched_convAdd_getD xs ys m]

theorem sched_convNat_getD_real : ∀ (as bs : List ℕ) (m : ℕ),
    ((sched_convNat as bs).getD m 0 : ℝ) =
      ta_polyConv (fun i ↦ (as.getD i 0 : ℝ)) (fun j ↦ (bs.getD j 0 : ℝ)) m := by
  have hmul : ∀ (a : ℕ) (bs : List ℕ) (m : ℕ), (bs.map (a * ·)).getD m 0 = a * bs.getD m 0 := by
    intro a bs; induction bs with
    | nil => simp [List.getD_eq_getElem?_getD]
    | cons _ tail ih =>
        intro m; rcases m with _ | m'
        · simp [List.getD_eq_getElem?_getD]
        · simp only [List.map_cons, sched_getD_cons_succ, ih m']
  intro as; induction as with
  | nil => simp [sched_convNat, List.getD_eq_getElem?_getD, ta_polyConv]
  | cons a as ih =>
      intro bs m; rcases m with _ | m'
      · rw [sched_convNat, sched_convAdd_getD, hmul]
        unfold ta_polyConv
        rw [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
          Nat.add_zero, Nat.cast_mul]
      · have hsucc := ta_polyConv_succ_left (fun i ↦ ((a :: as).getD i 0 : ℝ))
          (fun j ↦ (bs.getD j 0 : ℝ)) m'
        have hsh : (fun k ↦ ((a :: as).getD (k + 1) 0 : ℝ)) = fun k ↦ (as.getD k 0 : ℝ) :=
          funext fun k ↦ by rw [sched_getD_cons_succ]
        have hh0 : ((a :: as).getD 0 0 : ℝ) = (a : ℝ) := by simp [List.getD_eq_getElem?_getD]
        rw [hsh, hh0] at hsucc
        simp only [sched_convNat, sched_convAdd_getD, hmul, sched_getD_cons_succ,
          Nat.cast_add, Nat.cast_mul, ih bs m', hsucc]
        ring

theorem sched_map_getD_lt {α β : Type} (f : α → β) (da : α) (db : β) :
    ∀ (xs : List α) (m : ℕ), m < xs.length → (xs.map f).getD m db = f (xs.getD m da)
  | [], _, hm => nomatch hm
  | _ :: _, 0, _ => by simp [List.getD_eq_getElem?_getD]
  | _ :: xs, m + 1, hm => by
      simp only [List.map_cons, sched_getD_cons_succ]
      exact sched_map_getD_lt f da db xs m (Nat.lt_of_succ_lt_succ hm)

theorem sched_zipWith_getD_lt (f : ℕ → ℕ → ℕ) :
    ∀ (xs ys : List ℕ) (m : ℕ), m < xs.length → m < ys.length →
      (List.zipWith f xs ys).getD m 0 = f (xs.getD m 0) (ys.getD m 0)
  | [], _, _, hmx, _ => nomatch hmx
  | _, [], _, _, hmy => nomatch hmy
  | _ :: _, _ :: _, 0, _, _ => by simp [List.getD_eq_getElem?_getD]
  | _ :: xs, _ :: ys, m + 1, hmx, hmy => by
      simp only [List.zipWith_cons_cons, sched_getD_cons_succ]
      exact sched_zipWith_getD_lt f xs ys m (Nat.lt_of_succ_lt_succ hmx) (Nat.lt_of_succ_lt_succ
        hmy)

theorem sched_pack768_and_rep_shift (c sh : ℕ) (hc : c < sched_pow768) (xs : List ℕ)
    (hxs : ∀ x ∈ xs, x < sched_pow768) (hmask : ∀ x ∈ xs, x &&& c = 2 ^ sh * (x >>> sh)) :
    Nat.shiftRight (Nat.land (pack768 xs) (pack768 (List.replicate xs.length c))) sh = pack768
    (xs.map (· >>> sh)) := by
  have hf2 : List.Forall₂ (fun x m ↦ x < sched_pow768 ∧ m < sched_pow768)
      xs (List.replicate xs.length c) := by
    clear hmask
    induction xs with
    | nil => exact List.Forall₂.nil
    | cons x xt ih =>
        exact List.Forall₂.cons ⟨hxs x List.mem_cons_self, hc⟩
          (ih fun a ha ↦ hxs a (List.mem_cons_of_mem x ha))
  have hzip : List.zipWith (· &&& ·) xs (List.replicate xs.length c) =
      (xs.map (· >>> sh)).map (Nat.mul (2 ^ sh)) := by
    clear hf2 hxs
    induction xs with
    | nil => rfl
    | cons x xt ih =>
        simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.map_cons,
          hmask x List.mem_cons_self, ih fun a ha ↦ hmask a (List.mem_cons_of_mem x ha), Nat.mul_eq]
  change ((pack768 xs &&& pack768 (List.replicate xs.length c)) >>> sh) = _
  rw [← sched_pack768_and xs _ hf2, hzip, sched_pack768_mul (2 ^ sh),
      Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.mul_div_left _ (Nat.two_pow_pos sh)]

/-- Reference positive part extracted from quotient lane `q` in `roundSplit768`. -/
def sched_fpLane (q : ℕ) : ℕ :=
  (q &&& (schedAux * (q >>> 384))) - (sched_bQ &&& (schedAux * (q >>> 384)))

/-- Reference negative part extracted from quotient lane `q` in `roundSplit768`. -/
def sched_fnLane (q : ℕ) : ℕ := (sched_bQ &&& (schedAux - schedAux * (q >>> 384))) -
    (q &&& (schedAux - schedAux * (q >>> 384)))

theorem sched_pack768_map_and (f g : ℕ → ℕ) : ∀ (qs : List ℕ),
    (∀ q ∈ qs, f q < sched_pow768) → (∀ q ∈ qs, g q < sched_pow768) →
    pack768 (qs.map f) &&& pack768 (qs.map g) =
      pack768 (qs.map (fun q ↦ f q &&& g q))
  | [], _, _ => by simp only [List.map_nil, sched_pack768_nil]; rfl
  | q :: qt, hf, hg => by
      simp only [List.map_cons, sched_pack768_cons]
      rw [sched_and_shiftLeft_768_add _ _ _ _ (hf q List.mem_cons_self) (hg q List.mem_cons_self),
          sched_pack768_map_and f g qt (fun a ha ↦ hf a (List.mem_cons_of_mem q ha))
            (fun a ha ↦ hg a (List.mem_cons_of_mem q ha))]

theorem sched_pack768_map_sub (f g : ℕ → ℕ) : ∀ (qs : List ℕ),
    (∀ q ∈ qs, g q ≤ f q) →
    Nat.sub (pack768 (qs.map f)) (pack768 (qs.map g)) =
      pack768 (qs.map (fun q ↦ f q - g q))
  | [], _ => by simp only [List.map_nil, sched_pack768_nil]
  | q :: qt, hle => by
      have hle' : ∀ a ∈ qt, g a ≤ f a := fun a ha ↦ hle a (List.mem_cons_of_mem q ha)
      have hf2 : List.Forall₂ (· ≤ ·) (qt.map g) (qt.map f) := by
        clear hle q
        induction qt with
        | nil => exact List.Forall₂.nil
        | cons a at' ih =>
            exact List.Forall₂.cons (hle' a List.mem_cons_self)
              (ih (fun b hb ↦ hle' b (List.mem_cons_of_mem a hb)))
      have hmle := Nat.mul_le_mul_left sched_pow768 (sched_pack768_mono _ _ hf2)
      have hhq := hle q List.mem_cons_self
      have ih := sched_pack768_map_sub f g qt (fun a ha ↦ hle a (List.mem_cons_of_mem q ha))
      simp only [List.map_cons, sched_pack768_cons, sched_shiftLeft_768_eq, Nat.sub_eq] at ih ⊢
      rw [← ih, Nat.mul_sub_left_distrib]
      omega

theorem sched_roundSplitFinish_lists (qs : List ℕ) (hqs : ∀ q ∈ qs, q < 2 ^ 385) :
    let n := qs.length
    let rep_bq := pack768 (List.replicate n sched_bQ)
    let repAux := pack768 (List.replicate n schedAux)
    let sbits := pack768 (qs.map (· >>> 384))
    let mask_pos := Nat.mul sbits schedAux
    let mask_neg := Nat.sub repAux mask_pos
    Nat.sub (Nat.land (pack768 qs) mask_pos) (Nat.land rep_bq mask_pos) =
      pack768 (qs.map sched_fpLane) ∧
    Nat.sub (Nat.land rep_bq mask_neg) (Nat.land (pack768 qs) mask_neg) =
      pack768 (qs.map sched_fnLane) := by
  have hrep : ∀ c : ℕ, List.replicate qs.length c = qs.map (fun _ ↦ c) := fun c ↦ by
    clear hqs
    induction qs with
    | nil => rfl
    | cons _ _ ih => exact congrArg (c :: ·) ih
  have hp385 : (2 ^ 385 : ℕ) < sched_pow768 := Nat.ble_eq.mp rfl
  have hm385_lt : schedAux < sched_pow768 := Nat.ble_eq.mp rfl
  have hbq_lt : sched_bQ < sched_pow768 := Nat.ble_eq.mp rfl
  let mp : ℕ → ℕ := fun q ↦ schedAux * (q >>> 384)
  let mn : ℕ → ℕ := fun q ↦ schedAux - mp q
  have hq_lt : ∀ q ∈ qs, q < sched_pow768 := fun q hq ↦ (hqs q hq).trans hp385
  have hmp_lt : ∀ q ∈ qs, mp q < sched_pow768 :=
    fun q hq ↦ (sched_lane_split_spec q (hqs q hq)).1.trans_lt hm385_lt
  have hmn_lt : ∀ q ∈ qs, mn q < sched_pow768 := fun _ _ ↦ (Nat.sub_le _ _).trans_lt hm385_lt
  have hand_id : ∀ (g : ℕ → ℕ) (hg : ∀ q ∈ qs, g q < sched_pow768),
      Nat.land (pack768 qs) (pack768 (qs.map g)) = pack768 (qs.map fun q ↦ q &&& g q) :=
    fun g hg ↦ by
      have hid := sched_pack768_map_and id g qs hq_lt hg
      rw [List.map_id] at hid
      exact hid
  have hand_bq : ∀ (g : ℕ → ℕ) (hg : ∀ q ∈ qs, g q < sched_pow768),
      Nat.land (pack768 (qs.map fun _ ↦ sched_bQ)) (pack768 (qs.map g)) =
        pack768 (qs.map fun q ↦ sched_bQ &&& g q) :=
    fun g hg ↦ sched_pack768_map_and (fun _ ↦ sched_bQ) g qs (fun _ _ ↦ hbq_lt) hg
  dsimp only
  rw [hrep sched_bQ, hrep schedAux,
      show Nat.mul (pack768 (qs.map (· >>> 384))) schedAux = pack768 (qs.map mp) by
        rw [Nat.mul_eq, Nat.mul_comm, ← sched_pack768_mul, List.map_map]; rfl,
      sched_pack768_map_sub (fun _ ↦ schedAux) mp qs
        (fun q hq ↦ (sched_lane_split_spec q (hqs q hq)).1),
      hand_id mp hmp_lt, hand_bq mp hmp_lt, hand_bq mn hmn_lt, hand_id mn hmn_lt,
      sched_pack768_map_sub _ _ qs (fun q hq ↦ (sched_lane_split_spec q (hqs q hq)).2.1),
      sched_pack768_map_sub _ _ qs (fun q hq ↦ (sched_lane_split_spec q (hqs q hq)).2.2.1)]
  exact ⟨rfl, rfl⟩

theorem roundSplit768_spec (L rep1 : ℕ) (ups uns : List ℕ) (pn : PolyPN)
    (hups_len : ups.length = L + 1) (huns_len : uns.length = L + 1)
    (hups_lt : ∀ x ∈ ups, x < 2 ^ 736) (huns_lt : ∀ x ∈ uns, x < 2 ^ 736)
    (hrep1 : rep1 = pack768 (List.replicate (L + 1) 1))
    (hres : roundSplit768 rep1 (pack768 ups) (pack768 uns) = some pn) :
    ∃ f_hat : ℕ → ℝ, PolyPNValid L pn f_hat ∧
      ∀ m ≤ L, |f_hat m - ((ups.getD m 0 : ℝ) - (uns.getD m 0 : ℝ)) / (2 ^ 704 : ℝ)| ≤
        1 / (2 ^ 352 : ℝ) := by
  have hzs_aux : ∀ (n : ℕ) (us vs : List ℕ), us.length = n → vs.length = n →
      (∀ x ∈ us, x < sched_bMid) → (∀ y ∈ vs, y < sched_bMid) →
      List.Forall₂ (· ≤ ·) vs (List.zipWith Nat.add us (List.replicate n sched_bMid)) ∧
      ∀ z ∈ List.zipWith Nat.sub (List.zipWith Nat.add us (List.replicate n sched_bMid)) vs,
        z < 2 ^ 737 := by
    intro n; induction n with
    | zero =>
        intro us vs hu hv _ _
        cases List.length_eq_zero_iff.mp hu; cases List.length_eq_zero_iff.mp hv
        exact ⟨List.Forall₂.nil, fun _ hz ↦ nomatch hz⟩
    | succ n ih =>
        intro us vs hu hv hus hvs
        rcases us with _ | ⟨u, ut⟩; · cases hu
        rcases vs with _ | ⟨v, vt⟩; · cases hv
        rcases ih ut vt (Nat.succ.inj hu) (Nat.succ.inj hv)
          (fun a ha ↦ hus a (List.mem_cons_of_mem u ha))
          (fun a ha ↦ hvs a (List.mem_cons_of_mem v ha)) with ⟨hf2, hmem⟩
        refine ⟨List.Forall₂.cons
          ((Nat.le_of_lt (hvs v List.mem_cons_self)).trans (Nat.le_add_left _ _)) hf2, fun z hz ↦
            ?_⟩
        rcases List.mem_cons.mp hz with rfl | hzm
        · exact (Nat.sub_le _ _).trans_lt
            ((show (2 ^ 737 : ℕ) = sched_bMid + sched_bMid from rfl) ▸
              Nat.add_lt_add_right (hus u List.mem_cons_self) _)
        · exact hmem z hzm
  rcases hzs_aux (L + 1) ups uns hups_len huns_len
    (fun x hx ↦ sched_bMid_eq.symm ▸ hups_lt x hx)
    (fun y hy ↦ sched_bMid_eq.symm ▸ huns_lt y hy) with ⟨hzs_f2, hzs_lt737⟩
  let zs := List.zipWith Nat.sub (List.zipWith Nat.add ups (List.replicate (L + 1) sched_bMid)) uns
  have hzs_len : zs.length = L + 1 := by
    simp only [zs, List.length_zipWith, List.length_replicate, hups_len, huns_len,
      sched_min_self_nat]
  have hrep_c : ∀ c, Nat.mul rep1 c = pack768 (List.replicate (L + 1) c) := fun c ↦ by
    rw [hrep1, sched_pack768_rep_mul]
  have hzw : Nat.sub (Nat.add (pack768 ups) (Nat.mul rep1 sched_bMid)) (pack768 uns) =
      pack768 zs := by
    rw [hrep_c, Nat.add_eq, ← sched_pack768_zipAdd ups _ (by rw [hups_len, List.length_replicate]),
        Nat.sub_eq, ← sched_pack768_sub _ _ hzs_f2]
  let qs := zs.map (· >>> 352)
  have hqs_len : qs.length = L + 1 := by simp only [qs, List.length_map, hzs_len]
  have hqw : Nat.shiftRight (Nat.land (pack768 zs) (Nat.mul rep1 sched_keepLane)) 352 =
      pack768 qs := by
    rw [hrep_c, ← hzs_len]
    exact sched_pack768_and_rep_shift sched_keepLane 352 (Nat.ble_eq.mp rfl) zs
      (fun z hz ↦ (hzs_lt737 z hz).trans (Nat.ble_eq.mp rfl))
      (fun z hz ↦ sched_mask_keep_lane z ((hzs_lt737 z hz).trans (Nat.ble_eq.mp rfl)))
  have hqs_lt : ∀ q ∈ qs, q < 2 ^ 385 := fun q hq ↦ by
    rcases List.mem_map.mp hq with ⟨z, hz, rfl⟩
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 352)]
    exact hzs_lt737 z hz
  have hsbits : Nat.shiftRight (Nat.land (pack768 qs) (Nat.mul rep1 sched_bQ)) 384 =
      pack768 (qs.map (· >>> 384)) := by
    rw [hrep_c, ← hqs_len]
    exact sched_pack768_and_rep_shift sched_bQ 384 (Nat.ble_eq.mp rfl) qs
      (fun q hq ↦ (hqs_lt q hq).trans (Nat.ble_eq.mp rfl))
      (fun q hq ↦ sched_mask_bq_lane q (hqs_lt q hq))
  let fps := qs.map sched_fpLane
  let fns := qs.map sched_fnLane
  have hfin := sched_roundSplitFinish_lists qs hqs_lt
  simp only [roundSplit768, sched_tf1_eq, sched_shrLimb_eq, sched_shr384_eq] at hres
  rw [hzw, hqw, hsbits, hrep_c sched_bQ, hrep_c schedAux, ← hqs_len,
      hfin.1, hfin.2, hrep_c sched_clampHiLane] at hres
  split at hres
  · rename_i hbeq
    injection hres with hpn; subst hpn
    have hok := Nat.beq_eq.mp hbeq
    rw [Nat.add_eq, Nat.add_eq_zero_iff] at hok
    rcases hok with ⟨hok1, hok2⟩
    have hfps_len : fps.length = L + 1 := by simp only [fps, List.length_map, hqs_len]
    have hfns_len : fns.length = L + 1 := by simp only [fns, List.length_map, hqs_len]
    have hclamp : ∀ fs : List ℕ, (∀ x ∈ fs, x < 2 ^ 385) →
        Nat.land (pack768 fs) (pack768 (List.replicate fs.length sched_clampHiLane)) = 0 →
        ∀ x ∈ fs, x < 2 ^ 353 := fun fs hfs h0 x hx ↦ by
      have hshr : pack768 (fs.map (· >>> 353)) = 0 := by
        rw [← sched_pack768_and_rep_shift sched_clampHiLane 353 (Nat.ble_eq.mp rfl) fs
              (fun y hy ↦ (hfs y hy).trans (Nat.ble_eq.mp rfl))
              (fun y hy ↦ (rfl : sched_clampHiLane = 2 ^ 353 * (2 ^ 32 - 1)) ▸
                sched_mask_mid_lane 353 32 y (hfs y hy)), h0]
        rfl
      have hp0 : ∀ ys : List ℕ, pack768 ys = 0 → ∀ y ∈ ys, y = 0 := fun ys ↦ by
        induction ys with
        | nil => exact fun _ _ hy ↦ nomatch hy
        | cons y yt ih =>
            simp only [sched_pack768_cons, sched_shiftLeft_768_eq, Nat.add_eq_zero_iff, mul_eq_zero]
            exact fun ⟨hy, hyt⟩ a ha ↦ (List.mem_cons.mp ha).elim (· ▸ hy)
              (ih (hyt.resolve_left (Nat.ne_of_gt sched_pow768_pos)) a)
      have hx0 : x >>> 353 = 0 := hp0 _ hshr _ (List.mem_map_of_mem hx)
      rw [Nat.shiftRight_eq_div_pow] at hx0
      exact (Nat.div_eq_zero_iff.mp hx0).resolve_left (Nat.ne_of_gt (Nat.two_pow_pos 353))
    refine ⟨fun m ↦ if m ≤ L then ((fps.getD m 0 : ℝ) - (fns.getD m 0 : ℝ)) / (2 ^ 352 : ℝ) else 0,
      ⟨fps, fns, hfps_len, hfns_len,
        hclamp fps (fun _ hx ↦ by
          rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩
          exact (sched_lane_split_spec q (hqs_lt q hq)).2.2.2.1) (hfps_len ▸ hok1),
        hclamp fns (fun _ hx ↦ by
          rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩
          exact (sched_lane_split_spec q (hqs_lt q hq)).2.2.2.2.1) (hfns_len ▸ hok2),
        rfl, rfl, fun _ ↦ rfl⟩, fun m hm ↦ ?_⟩
    simp only [hm, ↓reduceIte]
    have hm_lt : m < L + 1 := Nat.lt_succ_of_le hm
    have hrep_get : ∀ n k : ℕ, k < n → (List.replicate n sched_bMid).getD k 0 = sched_bMid :=
      fun n ↦ by
        induction n with
        | zero => exact fun _ hk ↦ nomatch hk
        | succ n ih =>
            rintro (_ | k') hk
            · rfl
            · exact ih k' (Nat.lt_of_succ_lt_succ hk)
    let up := ups.getD m 0
    let un := uns.getD m 0
    let q := qs.getD m 0
    let fp := fps.getD m 0
    let fn := fns.getD m 0
    have hun : un < 2 ^ 736 := sched_getD_lt_of_forall_lt (Nat.two_pow_pos 736) uns m huns_lt
    have hq_eq : q = (up + 2 ^ 736 - un) >>> 352 := by
      rw [show q = zs.getD m 0 >>> 352 from sched_map_getD_lt (· >>> 352) 0 0 zs m (hzs_len.symm ▸
        hm_lt),
          sched_zipWith_getD_lt Nat.sub _ uns m
            (by simp [hups_len, hm_lt]) (huns_len.symm ▸ hm_lt),
          sched_zipWith_getD_lt Nat.add ups _ m (hups_len.symm ▸ hm_lt) (by simp [hm_lt]),
          hrep_get (L + 1) m hm_lt, Nat.sub_eq, Nat.add_eq, sched_bMid_eq]
    have hsplit : (fp : ℤ) - (fn : ℤ) = (q : ℤ) - (2 ^ 384 : ℤ) := by
      rw [show fp =
        sched_fpLane q from sched_map_getD_lt sched_fpLane 0 0 qs m (hqs_len.symm ▸ hm_lt),
          show fn =
            sched_fnLane q from sched_map_getD_lt sched_fnLane 0 0 qs m (hqs_len.symm ▸ hm_lt)]
      exact (sched_lane_split_spec q (sched_getD_lt_of_forall_lt (Nat.two_pow_pos 385) qs m
        hqs_lt)).2.2.2.2.2
    let r := (up + 2 ^ 736 - un) % 2 ^ 352
    have heq_nat : 2 ^ 352 * q + r + un = up + 2 ^ 736 := by
      rw [hq_eq, Nat.shiftRight_eq_div_pow, Nat.div_add_mod,
          Nat.sub_add_cancel ((Nat.le_of_lt hun).trans (Nat.le_add_left _ _))]
    have hr_le : (r : ℝ) ≤ (2 : ℝ) ^ 352 := by
      exact_mod_cast Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 352))
    have hsplit_r : (fp : ℝ) - (fn : ℝ) = (q : ℝ) - (2 : ℝ) ^ 384 := by
      simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat] using
        congrArg (Int.cast (R := ℝ)) hsplit
    have heq_r : (2 : ℝ) ^ 352 * (q : ℝ) + (r : ℝ) + (un : ℝ) =
        (up : ℝ) + (2 : ℝ) ^ 352 * (2 : ℝ) ^ 384 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        show (736 : ℕ) = 352 + 384 from rfl, pow_add] using congrArg (Nat.cast (R := ℝ)) heq_nat
    rw [show (2 : ℝ) ^ 704 = (2 : ℝ) ^ 352 * (2 : ℝ) ^ 352 by
          rw [show (704 : ℕ) = 352 + 352 from rfl, pow_add]]
    have hS : (0 : ℝ) < (2 : ℝ) ^ 352 := sched_two_pow_pos_real 352
    generalize (2 : ℝ) ^ 352 = S at hr_le heq_r hS ⊢
    generalize (2 : ℝ) ^ 384 = B at hsplit_r heq_r
    have hSS : 0 < S * S := mul_pos hS hS
    rw [show ((fp : ℝ) - (fn : ℝ)) / S - ((up : ℝ) - (un : ℝ)) / (S * S) = -(r : ℝ) / (S * S) by
          rw [hsplit_r, show (up : ℝ) - (un : ℝ) = S * (q : ℝ) - S * B + (r : ℝ) by linarith,
              ← mul_div_mul_right ((q : ℝ) - B) S (ne_of_gt hS), ← sub_div]
          congr 1; ring,
        neg_div, abs_neg, abs_div, abs_of_nonneg (Nat.cast_nonneg r),
        abs_of_pos hSS, div_le_div_iff₀ hSS hS]
    simpa [one_mul] using mul_le_mul_of_nonneg_right hr_le (le_of_lt hS)
  · cases hres

/-- Unsigned `pos` part of `a * b + c * d` on `PolyPN`. -/
def mulAdd2Pos (a b c d : PolyPN) : ℕ :=
  Nat.add (Nat.add (Nat.mul a.pos b.pos) (Nat.mul a.neg b.neg))
    (Nat.add (Nat.mul c.pos d.pos) (Nat.mul c.neg d.neg))

/-- Unsigned `neg` part of `a * b + c * d` on `PolyPN`. -/
def mulAdd2Neg (a b c d : PolyPN) : ℕ :=
  Nat.add (Nat.add (Nat.mul a.pos b.neg) (Nat.mul a.neg b.pos))
    (Nat.add (Nat.mul c.pos d.neg) (Nat.mul c.neg d.pos))

/-- Unsigned `pos` part of a 4-term `PolyPN` dot product. -/
def mulAdd4Pos (a1 b1 a2 b2 a3 b3 a4 b4 : PolyPN) : ℕ :=
  Nat.add (mulAdd2Pos a1 b1 a2 b2) (mulAdd2Pos a3 b3 a4 b4)

/-- Unsigned `neg` part of a 4-term `PolyPN` dot product. -/
def mulAdd4Neg (a1 b1 a2 b2 a3 b3 a4 b4 : PolyPN) : ℕ :=
  Nat.add (mulAdd2Neg a1 b1 a2 b2) (mulAdd2Neg a3 b3 a4 b4)

/-- Salted scalar `pos` part of `x1 * y1 + x2 * y2`. -/
def sched_mulAdd2PosN (s : ℕ) (x1p x1n y1p y1n x2p x2n y2p y2n : ℕ) : ℕ := Nat.add (Nat.add
    (Nat.mul (sched_idSalt s x1p) y1p) (Nat.mul (sched_idSalt s x1n) y1n)) (Nat.add (Nat.mul
    (sched_idSalt s x2p) y2p) (Nat.mul (sched_idSalt s x2n) y2n))

/-- Salted scalar `neg` part of `x1 * y1 + x2 * y2`. -/
def sched_mulAdd2NegN (s : ℕ) (x1p x1n y1p y1n x2p x2n y2p y2n : ℕ) : ℕ := Nat.add (Nat.add
    (Nat.mul (sched_idSalt s x1p) y1n) (Nat.mul (sched_idSalt s x1n) y1p)) (Nat.add (Nat.mul
    (sched_idSalt s x2p) y2n) (Nat.mul (sched_idSalt s x2n) y2p))

/-- Salted scalar `pos` part of a 4-term `PolyPN` dot product. -/
def sched_mulAdd4PosN (s : ℕ) (a1p a1n b1p b1n a2p a2n b2p b2n a3p a3n b3p b3n a4p a4n b4p b4n
    : ℕ) : ℕ := Nat.add (sched_mulAdd2PosN s a1p a1n b1p b1n a2p a2n b2p b2n)
    (sched_mulAdd2PosN (Nat.add 1 s) a3p a3n b3p b3n a4p a4n b4p b4n)

/-- Salted scalar `neg` part of a 4-term `PolyPN` dot product. -/
def sched_mulAdd4NegN (s : ℕ) (a1p a1n b1p b1n a2p a2n b2p b2n a3p a3n b3p b3n a4p a4n b4p b4n
    : ℕ) : ℕ := Nat.add (sched_mulAdd2NegN s a1p a1n b1p b1n a2p a2n b2p b2n)
    (sched_mulAdd2NegN (Nat.add 1 s) a3p a3n b3p b3n a4p a4n b4p b4n)

theorem sched_polyConv_pn_pair {La Lb : ℕ} {a b : PolyPN} {fa fb : ℕ → ℝ}
    (ha : PolyPNValid La a fa) (hb : PolyPNValid Lb b fb) : ∃ cp cn : List ℕ,
    cp.length = La + Lb + 1 ∧ cn.length = La + Lb + 1 ∧
    (∀ x ∈ cp, x ≤ 2 * (La + 1) * ((2 ^ 353 - 1) * (2 ^ 353 - 1))) ∧
    (∀ x ∈ cn, x ≤ 2 * (La + 1) * ((2 ^ 353 - 1) * (2 ^ 353 - 1))) ∧
    Nat.add (Nat.mul a.pos b.pos) (Nat.mul a.neg b.neg) = pack768 cp ∧
    Nat.add (Nat.mul a.pos b.neg) (Nat.mul a.neg b.pos) = pack768 cn ∧
    ∀ m, ta_polyConv fa fb m = ((cp.getD m 0 : ℝ) - (cn.getD m 0 : ℝ)) / (2 ^ 704 : ℝ) := by
  have heq_all : ∀ {L : ℕ} {vp vn : List ℕ} {f : ℕ → ℝ}, vp.length = L + 1 → vn.length = L + 1 →
      (∀ m, f m = if m ≤ L then ((vp.getD m 0 : ℝ) - (vn.getD m 0 : ℝ)) / (2 ^ 352 : ℝ) else 0) →
      f = fun m ↦ ((vp.getD m 0 : ℝ) - (vn.getD m 0 : ℝ)) / (2 ^ 352 : ℝ) :=
    fun {L} {vp vn} {_} hvp hvn hf ↦ funext fun m ↦ by
      rw [hf m]
      by_cases hm : m ≤ L
      · simp only [hm, ↓reduceIte]
      · simp only [hm, ↓reduceIte, sched_getD_eq_zero_of_ge vp m (by omega),
          sched_getD_eq_zero_of_ge vn m (by omega), Nat.cast_zero, sub_self, zero_div]
  rcases ha with ⟨ap, an, hap_l, han_l, hap_lt, han_lt, hap_p, han_p, hfa⟩
  rcases hb with ⟨bp, bn, hbp_l, hbn_l, hbp_lt, hbn_lt, hbp_p, hbn_p, hfb⟩
  let M := 2 ^ 353 - 1
  have h2m : (La + 1) * (M * M) + (La + 1) * (M * M) = 2 * (La + 1) * (M * M) := by ring
  have hmem : ∀ (u1 v1 u2 v2 : List ℕ), u1.length = La + 1 → u2.length = La + 1 →
      (∀ x ∈ u1, x < 2 ^ 353) → (∀ x ∈ v1, x < 2 ^ 353) →
      (∀ x ∈ u2, x < 2 ^ 353) → (∀ x ∈ v2, x < 2 ^ 353) →
      ∀ x ∈ sched_convAdd (sched_convNat u1 v1) (sched_convNat u2 v2), x ≤ 2 * (La + 1) * (M * M) :=
    fun u1 v1 u2 v2 hl1 hl2 hu1 hv1 hu2 hv2 x hx ↦ h2m ▸ sched_convAdd_mem_le _ _
      (fun u hu ↦ hl1 ▸ sched_convNat_mem_le u1 v1 (fun _ h ↦ Nat.le_sub_one_of_lt (hu1 _ h))
        (fun _ h ↦ Nat.le_sub_one_of_lt (hv1 _ h)) u hu)
      (fun v hv ↦ hl2 ▸ sched_convNat_mem_le u2 v2 (fun _ h ↦ Nat.le_sub_one_of_lt (hu2 _ h))
        (fun _ h ↦ Nat.le_sub_one_of_lt (hv2 _ h)) v hv) x hx
  refine ⟨sched_convAdd (sched_convNat ap bp) (sched_convNat an bn),
    sched_convAdd (sched_convNat ap bn) (sched_convNat an bp),
    by simp only [sched_convAdd_len, sched_convNat_len La Lb ap bp hap_l hbp_l,
         sched_convNat_len La Lb an bn han_l hbn_l, max_self],
    by simp only [sched_convAdd_len, sched_convNat_len La Lb ap bn hap_l hbn_l,
         sched_convNat_len La Lb an bp han_l hbp_l, max_self],
    hmem ap bp an bn hap_l han_l hap_lt hbp_lt han_lt hbn_lt,
    hmem ap bn an bp hap_l han_l hap_lt hbn_lt han_lt hbp_lt,
    by simp only [sched_pack768_convAdd, sched_pack768_convNat, hap_p, han_p, hbp_p, hbn_p,
         Nat.add_eq, Nat.mul_eq],
    by simp only [sched_pack768_convAdd, sched_pack768_convNat, hap_p, han_p, hbp_p, hbn_p,
         Nat.add_eq, Nat.mul_eq],
    fun m ↦ ?_⟩
  rw [heq_all hap_l han_l hfa, heq_all hbp_l hbn_l hfb]
  have hp704 : (2 : ℝ) ^ 704 = (2 : ℝ) ^ 352 * (2 : ℝ) ^ 352 := by
    rw [show (704 : ℕ) = 352 + 352 from rfl, pow_add]
  unfold ta_polyConv
  rw [show (∑ i ∈ Finset.range (m + 1),
        (((ap.getD i 0 : ℝ) - (an.getD i 0 : ℝ)) / (2 ^ 352 : ℝ)) *
          (((bp.getD (m - i) 0 : ℝ) - (bn.getD (m - i) 0 : ℝ)) / (2 ^ 352 : ℝ))) =
      (∑ i ∈ Finset.range (m + 1),
        (((ap.getD i 0 : ℝ) * (bp.getD (m - i) 0 : ℝ) +
          (an.getD i 0 : ℝ) * (bn.getD (m - i) 0 : ℝ)) -
         ((ap.getD i 0 : ℝ) * (bn.getD (m - i) 0 : ℝ) +
          (an.getD i 0 : ℝ) * (bp.getD (m - i) 0 : ℝ)))) / (2 ^ 704 : ℝ) by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [div_mul_div_comm, hp704]
        congr 1
        ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  change ((ta_polyConv (fun i ↦ (ap.getD i 0 : ℝ)) (fun j ↦ (bp.getD j 0 : ℝ)) m +
           ta_polyConv (fun i ↦ (an.getD i 0 : ℝ)) (fun j ↦ (bn.getD j 0 : ℝ)) m) -
          (ta_polyConv (fun i ↦ (ap.getD i 0 : ℝ)) (fun j ↦ (bn.getD j 0 : ℝ)) m +
           ta_polyConv (fun i ↦ (an.getD i 0 : ℝ)) (fun j ↦ (bp.getD j 0 : ℝ)) m)) / (2 ^ 704 : ℝ) =
             _
  rw [← sched_convNat_getD_real, ← sched_convNat_getD_real, ← sched_convNat_getD_real,
      ← sched_convNat_getD_real, ← Nat.cast_add, ← Nat.cast_add,
      ← sched_convAdd_getD, ← sched_convAdd_getD]

theorem mulAdd4_roundSplit_spec {La Lb rep1 : ℕ}
    {a1 b1 a2 b2 a3 b3 a4 b4 pn : PolyPN} {fa1 fb1 fa2 fb2 fa3 fb3 fa4 fb4 : ℕ → ℝ}
    (hLa : La ≤ 262144) (hrep1 : rep1 = pack768 (List.replicate (La + Lb + 1) 1))
    (ha1 : PolyPNValid La a1 fa1) (hb1 : PolyPNValid Lb b1 fb1)
    (ha2 : PolyPNValid La a2 fa2) (hb2 : PolyPNValid Lb b2 fb2)
    (ha3 : PolyPNValid La a3 fa3) (hb3 : PolyPNValid Lb b3 fb3)
    (ha4 : PolyPNValid La a4 fa4) (hb4 : PolyPNValid Lb b4 fb4)
    (hres : roundSplit768 rep1 (mulAdd4Pos a1 b1 a2 b2 a3 b3 a4 b4)
      (mulAdd4Neg a1 b1 a2 b2 a3 b3 a4 b4) = some pn) :
    ∃ f_hat : ℕ → ℝ, PolyPNValid (La + Lb) pn f_hat ∧
      ∀ m, |f_hat m - (ta_polyConv fa1 fb1 m + ta_polyConv fa2 fb2 m +
                       ta_polyConv fa3 fb3 m + ta_polyConv fa4 fb4 m)| ≤ 1 / (2 ^ 352 : ℝ) := by
  let K := (2 ^ 353 - 1) * (2 ^ 353 - 1)
  have hm2 : ∀ {x1 y1 x2 y2 : PolyPN} {fx1 fy1 fx2 fy2 : ℕ → ℝ},
      PolyPNValid La x1 fx1 → PolyPNValid Lb y1 fy1 →
      PolyPNValid La x2 fx2 → PolyPNValid Lb y2 fy2 →
      ∃ ups uns : List ℕ, ups.length = La + Lb + 1 ∧ uns.length = La + Lb + 1 ∧
        (∀ x ∈ ups, x ≤ 4 * (La + 1) * K) ∧ (∀ x ∈ uns, x ≤ 4 * (La + 1) * K) ∧
        mulAdd2Pos x1 y1 x2 y2 = pack768 ups ∧ mulAdd2Neg x1 y1 x2 y2 = pack768 uns ∧
        ∀ m, ta_polyConv fx1 fy1 m + ta_polyConv fx2 fy2 m =
          ((ups.getD m 0 : ℝ) - (uns.getD m 0 : ℝ)) / (2 ^ 704 : ℝ) :=
    fun h1 k1 h2 k2 ↦ by
      rcases sched_polyConv_pn_pair h1 k1 with ⟨c1, d1, hc1, hd1, hc1b, hd1b, hp1, hn1, hr1⟩
      rcases sched_polyConv_pn_pair h2 k2 with ⟨c2, d2, hc2, hd2, hc2b, hd2b, hp2, hn2, hr2⟩
      have h4 : 2 * (La + 1) * K + 2 * (La + 1) * K = 4 * (La + 1) * K := by ring
      exact ⟨sched_convAdd c1 c2, sched_convAdd d1 d2,
        by simp [sched_convAdd_len, hc1, hc2], by simp [sched_convAdd_len, hd1, hd2],
        fun x hx ↦ h4 ▸ sched_convAdd_mem_le c1 c2 hc1b hc2b x hx,
        fun x hx ↦ h4 ▸ sched_convAdd_mem_le d1 d2 hd1b hd2b x hx,
        by unfold mulAdd2Pos; rw [hp1, hp2, Nat.add_eq, ← sched_pack768_convAdd],
        by unfold mulAdd2Neg; rw [hn1, hn2, Nat.add_eq, ← sched_pack768_convAdd],
        fun m ↦ by
          rw [hr1 m, hr2 m, sched_convAdd_getD, sched_convAdd_getD, Nat.cast_add, Nat.cast_add]
          generalize (2 : ℝ) ^ 704 = S
          ring⟩
  rcases hm2 ha1 hb1 ha2 hb2 with ⟨u12, v12, hu12_l, hv12_l, hu12_le, hv12_le, hp12, hn12, hr12⟩
  rcases hm2 ha3 hb3 ha4 hb4 with ⟨u34, v34, hu34_l, hv34_l, hu34_le, hv34_le, hp34, hn34, hr34⟩
  have h8 : 4 * (La + 1) * K + 4 * (La + 1) * K = 8 * (La + 1) * K := by ring
  have hcap0 : 8 * 262145 * ((2 ^ 353 - 1) * (2 ^ 353 - 1)) < 2 ^ 736 := Nat.ble_eq.mp rfl
  have hcap : 8 * (La + 1) * K < 2 ^ 736 :=
    (Nat.mul_le_mul_right K (by omega : 8 * (La + 1) ≤ 8 * 262145)).trans_lt hcap0
  let ups := sched_convAdd u12 u34
  let uns := sched_convAdd v12 v34
  rw [show mulAdd4Pos a1 b1 a2 b2 a3 b3 a4 b4 = pack768 ups by
        unfold mulAdd4Pos; rw [hp12, hp34, Nat.add_eq, ← sched_pack768_convAdd],
      show mulAdd4Neg a1 b1 a2 b2 a3 b3 a4 b4 = pack768 uns by
        unfold mulAdd4Neg; rw [hn12, hn34, Nat.add_eq, ← sched_pack768_convAdd]] at hres
  rcases roundSplit768_spec (La + Lb) rep1 ups uns pn
    (by simp only [ups, sched_convAdd_len, hu12_l, hu34_l, max_self])
    (by simp only [uns, sched_convAdd_len, hv12_l, hv34_l, max_self])
    (fun x hx ↦ (h8 ▸ sched_convAdd_mem_le u12 u34 hu12_le hu34_le x hx).trans_lt hcap)
    (fun x hx ↦ (h8 ▸ sched_convAdd_mem_le v12 v34 hv12_le hv34_le x hx).trans_lt hcap)
    hrep1 hres with ⟨f_hat, hf_val, hf_err⟩
  refine ⟨f_hat, hf_val, fun m ↦ ?_⟩
  by_cases hm : m ≤ La + Lb
  · rw [show ta_polyConv fa1 fb1 m + ta_polyConv fa2 fb2 m + ta_polyConv fa3 fb3 m +
        ta_polyConv fa4 fb4 m = ((ups.getD m 0 : ℝ) - (uns.getD m 0 : ℝ)) / (2 ^ 704 : ℝ) by
      rw [add_assoc (ta_polyConv fa1 fb1 m + ta_polyConv fa2 fb2 m), hr12 m, hr34 m]
      simp only [ups, uns, sched_convAdd_getD, Nat.cast_add]
      generalize (2 : ℝ) ^ 704 = S
      ring]
    exact hf_err m hm
  · have hgt : La + Lb < m := by omega
    rw [sched_polyPNValid_supp hf_val m hgt,
        ta_polyConv_supp (sched_polyPNValid_supp ha1) (sched_polyPNValid_supp hb1) m hgt,
        ta_polyConv_supp (sched_polyPNValid_supp ha2) (sched_polyPNValid_supp hb2) m hgt,
        ta_polyConv_supp (sched_polyPNValid_supp ha3) (sched_polyPNValid_supp hb3) m hgt,
        ta_polyConv_supp (sched_polyPNValid_supp ha4) (sched_polyPNValid_supp hb4) m hgt]
    simp only [add_zero, sub_zero, abs_zero]
    exact le_of_lt (one_div_pos.mpr (sched_two_pow_pos_real 352))

theorem sched_rep1_merge_eq (ldeg rdeg lrep1 rrep1 : ℕ) (_hr1 : 1 ≤ rdeg)
    (hl : lrep1 = pack768 (List.replicate (ldeg + 1) 1))
    (hr : rrep1 = pack768 (List.replicate (rdeg + 1) 1)) : Nat.add lrep1 (Nat.shiftLeft
    (Nat.shiftRight rrep1 768) (Nat.mul 768 (Nat.add ldeg 1))) = pack768
    (List.replicate (ldeg + rdeg + 1) 1) := by
  have hshr : Nat.shiftRight rrep1 768 = pack768 (List.replicate rdeg 1) := by
    change rrep1 >>> 768 = _
    rw [Nat.shiftRight_eq_div_pow, ← sched_pow768_eq_pow, hr, List.replicate_succ,
        sched_pack768_cons, sched_shiftLeft_768_eq, Nat.add_mul_div_left _ _ sched_pow768_pos,
        Nat.div_eq_of_lt (Nat.ble_eq.mp rfl : (1 : ℕ) < sched_pow768), Nat.zero_add]
  rw [hl, hshr, Nat.add_eq, Nat.mul_eq, show Nat.add ldeg 1 = ldeg + 1 from rfl]
  change pack768 (List.replicate (ldeg + 1) 1) +
      (pack768 (List.replicate rdeg 1) <<< (768 * (ldeg + 1))) = _
  have happ := (sched_pack768_append (List.replicate (ldeg + 1) 1) (List.replicate rdeg 1)).symm
  rw [List.length_replicate] at happ
  rw [happ, ← List.replicate_add]
  exact congrArg (pack768 <| List.replicate · 1) (by omega)

theorem sched_gateListTransferPQ_singleton (b : ℕ) (g : DyadicSu2Gate) : gateListTransferPQ b
    [g] = (polyDelta1C (gateSu2Pair b g).1, polyDelta1C (gateSu2Pair b g).2) := by
  have hm := gateListTransferMatC_eq_cdMat b [g]
  dsimp only [gateListTransferMatC, List.length_singleton] at hm
  rw [polyMat2CMul_id_left, ← cdMat_one_gate] at hm
  exact Prod.ext (congrArg PolyMat2C.a hm.symm) (congrArg PolyMat2C.c hm.symm)

/-- Strict `(pos, neg)` continuation for a sign-magnitude word `w` (`false -> (w, 0)`, `true -> (0,
w)`). -/
def sched_withSignWord {α : Type} (sgn : Bool) (w : ℕ) (k : ℕ → ℕ → α) : α :=
  @Bool.casesOn (fun _ ↦ α) sgn (k w 0) (k 0 w)

/-- Construct a degree-`1` `TreeNodeC` from pre-shifted `48`-bit magnitudes of `g`. -/
def sched_mkLeafNodeC (s : ℕ) (sar sai sbr sbi : Bool) (war wai wbr wbi : ℕ) : Option TreeNodeC
    := sched_withSignWord sar war fun prp prn ↦ sched_withSignWord sai wai fun pip pin ↦
    sched_withSignWord sbr wbr fun qrp qrn ↦ sched_withSignWord sbi wbi fun qip qin ↦ some
    ⟨1, s, sched_rep2One, prp, prn, pip, pin, qrp, qrn, qip, qin, 0⟩

/-- Build a degree-`1` `TreeNodeC` leaf from a `48`-bit `DyadicSu2Gate` (`err = 0`). -/
def leafNodeC (g : DyadicSu2Gate) : Option TreeNodeC :=
  if Bool.and
      (Bool.and (Nat.ble g.mar 0x1000000000000) (Nat.ble g.mai 0x1000000000000))
      (Bool.and (Nat.ble g.mbr 0x1000000000000) (Nat.ble g.mbi 0x1000000000000)) then
    let salt0 := Nat.land (Nat.add 1 (Nat.xor (Nat.xor g.mar (Nat.mul g.mai
        0x9e3779b97f4a7c15)) (Nat.xor (Nat.mul g.mbr 0xbf58476d1ce4e5b9) g.mbi)))
        0xfffffffffffffff
    sched_tfOpt (fun s ↦
      sched_stfOpt (Nat.add 1 s) (fun v1 ↦
        sched_stfOpt (Nat.add 2 s) (fun v2 ↦
          sched_stfOpt (Nat.add 3 s) (fun v3 ↦
            sched_stfOpt (Nat.add 4 s) (fun v4 ↦
              sched_stfOpt (Nat.add 5 s) (fun w1 ↦
                sched_stfOpt (Nat.add 6 s) (fun w2 ↦
                  sched_stfOpt (Nat.add 7 s) (fun w3 ↦
                    sched_stfOpt (Nat.add 8 s) (fun w4 ↦
                      sched_mkLeafNodeC s g.sar g.sai g.sbr g.sbi w1 w2 w3 w4)
                    (sched_shl768 (sched_idSalt (Nat.add 8 s) v4)))
                  (sched_shl768 (sched_idSalt (Nat.add 7 s) v3)))
                (sched_shl768 (sched_idSalt (Nat.add 6 s) v2)))
              (sched_shl768 (sched_idSalt (Nat.add 5 s) v1)))
            (sched_shl304 (sched_idSalt (Nat.add 4 s) g.mbi)))
          (sched_shl304 (sched_idSalt (Nat.add 3 s) g.mbr)))
        (sched_shl304 (sched_idSalt (Nat.add 2 s) g.mai)))
      (sched_shl304 (sched_idSalt (Nat.add 1 s) g.mar))) salt0
  else none

theorem sched_leafChannel_valid (sgn : Bool) (mag : ℕ) (hmag : mag ≤ 2 ^ 48) :
    let w := Nat.shiftLeft (Nat.shiftLeft mag 304) 768
    PolyPNValid 1 ⟨if sgn then 0 else w, if sgn then w else 0⟩
      (fun idx ↦ if idx = 1 then (smToInt sgn mag : ℝ) / (2 ^ 48 : ℝ) else 0) := by
  have hp_cap : (2 ^ 48 : ℕ) * 2 ^ 304 < 2 ^ 353 := Nat.ble_eq.mp rfl
  let v := mag <<< 304
  have hv_lt : v < 2 ^ 353 := by
    have hv_eq : v = mag * 2 ^ 304 := Nat.shiftLeft_eq mag 304
    rw [hv_eq]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ 304) hmag) hp_cap
  have hmem2 : ∀ u < 2 ^ 353, ∀ x ∈ ([0, u] : List ℕ), x < 2 ^ 353 := fun u hu x hx ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Nat.two_pow_pos 353
    · exact hu
  refine ⟨[0, if sgn then 0 else v], [0, if sgn then v else 0], rfl, rfl,
    hmem2 _ (Bool.rec (motive := fun b ↦ (if b then 0 else v) < 2 ^ 353) hv_lt
      (Nat.two_pow_pos 353) sgn),
    hmem2 _ (Bool.rec (motive := fun b ↦ (if b then v else 0) < 2 ^ 353)
      (Nat.two_pow_pos 353) hv_lt sgn),
    by cases sgn <;> simp [v, sched_pack768_cons, sched_pack768_nil],
    by cases sgn <;> simp [v, sched_pack768_cons, sched_pack768_nil], fun idx ↦ ?_⟩
  rcases idx with _ | _ | k
  · simp only [Nat.zero_le, show (0 : ℕ) ≠ 1 by omega, ↓reduceIte,
      List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      Nat.cast_zero, sub_self, zero_div]
  · simp only [Nat.le_refl, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    have hv_r : (v : ℝ) = (mag : ℝ) * (2 : ℝ) ^ 304 := by
      have hc : (v : ℕ) = mag * 2 ^ 304 := Nat.shiftLeft_eq mag 304
      rw [hc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hpAux : (2 : ℝ) ^ 352 = (2 : ℝ) ^ 48 * (2 : ℝ) ^ 304 := by
      rw [show (352 : ℕ) = 48 + 304 from rfl, pow_add]
    have h304_ne : ((2 : ℝ) ^ 304) ≠ 0 := ne_of_gt (sched_two_pow_pos_real 304)
    cases sgn <;> simp only [Bool.false_eq_true, ↓reduceIte, smToInt, Int.cast_neg,
      Int.cast_natCast, Nat.cast_zero, hv_r, hpAux, sub_zero, zero_sub, neg_div]
    · exact (mul_div_mul_right (mag : ℝ) ((2 : ℝ) ^ 48) h304_ne).symm
    · exact congrArg Neg.neg (mul_div_mul_right (mag : ℝ) ((2 : ℝ) ^ 48) h304_ne).symm
  · simp only [show ¬(k + 2 ≤ 1) by omega, show k + 2 ≠ 1 by omega, ↓reduceIte]

theorem sched_polyPNValid_congr_fn {L : ℕ} {pn : PolyPN} {f g : ℕ → ℝ}
    (hf : PolyPNValid L pn f) (heq : ∀ m, f m = g m) : PolyPNValid L pn g :=
  funext heq ▸ hf

theorem leafNodeC_spec (g : DyadicSu2Gate) (nd : TreeNodeC)
    (h : leafNodeC g = some nd) : TreeNodeCValid [g] nd := by
  unfold leafNodeC at h
  split at h
  · rename_i hble
    simp only [Bool.and_eq_true, Nat.ble_eq, show (0x1000000000000 : ℕ) = 2 ^ 48 from rfl] at hble
    rcases hble with ⟨⟨hmar, hmai⟩, ⟨hmbr, hmbi⟩⟩
    have hwsw : ∀ {α : Type} (s : Bool) (w : ℕ) (k : ℕ → ℕ → α),
        sched_withSignWord s w k = k (if s then 0 else w) (if s then w else 0) :=
      fun s _ _ ↦ by cases s <;> rfl
    have hreim : ∀ x y : ℝ, ((x : ℂ) + Complex.I * (y : ℂ)).re = x ∧
        ((x : ℂ) + Complex.I * (y : ℂ)).im = y := fun x y ↦ by
      simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    have hshl304 : ∀ x : ℕ, sched_shl304 x = Nat.shiftLeft x 304 := fun _ ↦ rfl
    have hshl768 : ∀ x : ℕ, sched_shl768 x = Nat.shiftLeft x 768 := fun _ ↦ rfl
    have hrep2 : sched_rep2One = pack768 (List.replicate 2 1) := by
      simp only [List.replicate, sched_pack768_cons, sched_pack768_nil, sched_shiftLeft_768_eq]
      rfl
    simp only [sched_tfOpt_eq, sched_stfOpt_eq, sched_idSalt_eq, hshl304, hshl768,
      sched_mkLeafNodeC, hwsw] at h
    injection h with hnd
    subst hnd
    have hPQ := sched_gateListTransferPQ_singleton 48 g
    have h0e : ∀ f : ℕ → ℝ, ∀ m, |f m - f m| ≤ ((0 : ℕ) : ℝ) / (2 ^ 352 : ℝ) :=
      fun _ _ ↦ by simp only [Nat.cast_zero, zero_div, sub_self, abs_zero, le_refl]
    refine ⟨rfl, le_rfl, Nat.zero_le _, hrep2, polyDelta1C (gateSu2Pair 48 g).1,
      polyDelta1C (gateSu2Pair 48 g).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [TreeNodeC.pr]
      refine sched_polyPNValid_congr_fn (sched_leafChannel_valid g.sar g.mar hmar) fun _ ↦ ?_
      unfold polyDelta1C gateSu2Pair gateSu2ARe
      dsimp only
      rw [(hreim _ _).1]
    · dsimp only [TreeNodeC.pi]
      refine sched_polyPNValid_congr_fn (sched_leafChannel_valid g.sai g.mai hmai) fun _ ↦ ?_
      unfold polyDelta1C gateSu2Pair gateSu2AIm
      dsimp only
      rw [(hreim _ _).2]
    · dsimp only [TreeNodeC.qr]
      refine sched_polyPNValid_congr_fn (sched_leafChannel_valid g.sbr g.mbr hmbr) fun _ ↦ ?_
      unfold polyDelta1C gateSu2Pair gateSu2BRe
      dsimp only
      rw [(hreim _ _).1]
    · dsimp only [TreeNodeC.qi]
      refine sched_polyPNValid_congr_fn (sched_leafChannel_valid g.sbi g.mbi hmbi) fun _ ↦ ?_
      unfold polyDelta1C gateSu2Pair gateSu2BIm
      dsimp only
      rw [(hreim _ _).2]
    · rw [hPQ]
      exact ⟨h0e _, h0e _⟩
    · rw [hPQ]
      exact ⟨h0e _, h0e _⟩
  · cases h

/-- Kernel-friendly `Option.bind` wrapper avoiding `Option.casesOn` WHNF unfolding on symbolic
scrutinees. -/
def sched_optBind {α β : Type} (mx : Option α) (f : α → Option β) : Option β :=
  @Option.casesOn α (fun _ ↦ Option β) mx none f

theorem sched_optBind_eq_some {α β : Type} {mx : Option α} {f : α → Option β} {y : β}
    (h : sched_optBind mx f = some y) : ∃ x, mx = some x ∧ f x = some y := by
  cases mx with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

def sched_mkMergedNodeC (salt rep1 prp prn pip pin qrp qrn qip qin deg' err' : ℕ) : Option
    TreeNodeC := if Nat.ble err' sched_sTree then some
    ⟨deg', salt, rep1, prp, prn, pip, pin, qrp, qrn, qip, qin, err'⟩ else none

/-- Strict `err'` forcing step of `sched_mergeNodesCScalarGo`. -/
def sched_mergeNodesCStep5 (salt rep1 prp prn pip pin qrp qrn qip qin err' d_out : ℕ) : Option
    TreeNodeC := sched_stfOpt (Nat.add 1 salt)
    (sched_mkMergedNodeC salt rep1 prp prn pip pin qrp qrn qip qin d_out) err'

/-- Degree and error update step of `sched_mergeNodesCScalarGo`. -/
def sched_mergeNodesCStep4 (ldeg lerr rdeg rerr rep1 salt : ℕ)
    (pr' pi' qr' qi' : SaltedPN) : Option TreeNodeC :=
  let lmin := if Nat.ble ldeg rdeg then ldeg else rdeg
  let err' := Nat.add 1
    (Nat.mul (Nat.mul 4 (Nat.add 1 lmin)) (Nat.add (Nat.mul 3 rerr) (Nat.mul 2 lerr)))
  sched_stfOpt salt
    (sched_mergeNodesCStep5 salt rep1
      pr'.pos pr'.neg pi'.pos pi'.neg qr'.pos qr'.neg qi'.pos qi'.neg err')
    (Nat.add ldeg rdeg)

/-- Fourth channel (`qi'`) round-and-split step of `sched_mergeNodesCScalarGo`. -/
def sched_mergeNodesCStep3 (ldeg lprp lprn lpip lpin lqrp lqrn lqip lqin lerr : ℕ)
    (rdeg rqrp rqrn rqip rqin prvp prvn pivp pivn rerr : ℕ) (rep1 rb rk rbq rm rc salt : ℕ)
    (pr' pi' qr' : SaltedPN) : Option TreeNodeC := sched_optBind (sched_roundSplit768Masks
    (Nat.add 64 salt) rb rk rbq rm rc (sched_mulAdd4PosN (Nat.add 64 salt) rqrp rqrn lpip lpin
    rqip rqin lprp lprn prvp prvn lqip lqin pivn pivp lqrp lqrn) (sched_mulAdd4NegN (Nat.add 64
    salt) rqrp rqrn lpip lpin rqip rqin lprp lprn prvp prvn lqip lqin pivn pivp lqrp lqrn))
    (sched_mergeNodesCStep4 ldeg lerr rdeg rerr rep1 salt pr' pi' qr')

/-- Third channel (`qr'`) round-and-split step of `sched_mergeNodesCScalarGo`. -/
def sched_mergeNodesCStep2 (ldeg lprp lprn lpip lpin lqrp lqrn lqip lqin lerr : ℕ)
    (rdeg rqrp rqrn rqip rqin prvp prvn pivp pivn rerr : ℕ) (rep1 rb rk rbq rm rc salt : ℕ)
    (pr' pi' : SaltedPN) : Option TreeNodeC := sched_optBind (sched_roundSplit768Masks (Nat.add
    48 salt) rb rk rbq rm rc (sched_mulAdd4PosN (Nat.add 48 salt) rqrp rqrn lprp lprn rqin rqip
    lpip lpin prvp prvn lqrp lqrn pivp pivn lqip lqin) (sched_mulAdd4NegN (Nat.add 48 salt)
    rqrp rqrn lprp lprn rqin rqip lpip lpin prvp prvn lqrp lqrn pivp pivn lqip lqin))
    (sched_mergeNodesCStep3 ldeg lprp lprn lpip lpin lqrp lqrn lqip lqin lerr rdeg rqrp rqrn
    rqip rqin prvp prvn pivp pivn rerr rep1 rb rk rbq rm rc salt pr' pi')

/-- Second channel (`pi'`) round-and-split step of `sched_mergeNodesCScalarGo`. -/
def sched_mergeNodesCStep1 (ldeg lprp lprn lpip lpin lqrp lqrn lqip lqin lerr : ℕ) (rdeg rprp
    rprn rpip rpin rqrp rqrn rqip rqin prvp prvn pivp pivn qrvp qrvn qivp qivn rerr : ℕ)
    (rep1 rb rk rbq rm rc salt : ℕ) (pr' : SaltedPN) : Option TreeNodeC := sched_optBind
    (sched_roundSplit768Masks (Nat.add 32 salt) rb rk rbq rm rc (sched_mulAdd4PosN (Nat.add 32
    salt) rprp rprn lpip lpin rpip rpin lprp lprn qrvn qrvp lqip lqin qivp qivn lqrp lqrn)
    (sched_mulAdd4NegN (Nat.add 32 salt) rprp rprn lpip lpin rpip rpin lprp lprn qrvn qrvp lqip
    lqin qivp qivn lqrp lqrn)) (sched_mergeNodesCStep2 ldeg lprp lprn lpip lpin lqrp lqrn lqip
    lqin lerr rdeg rqrp rqrn rqip rqin prvp prvn pivp pivn rerr rep1 rb rk rbq rm rc salt pr')

/-- First channel (`pr'`) round-and-split step of `sched_mergeNodesCScalarGo`. -/
def sched_mergeNodesCScalarGo (ldeg lprp lprn lpip lpin lqrp lqrn lqip lqin lerr : ℕ) (rdeg
    rprp rprn rpip rpin rqrp rqrn rqip rqin prvp prvn pivp pivn qrvp qrvn qivp qivn rerr : ℕ)
    (rep1 rb rk rbq rm rc salt : ℕ) : Option TreeNodeC := sched_optBind
    (sched_roundSplit768Masks (Nat.add 16 salt) rb rk rbq rm rc (sched_mulAdd4PosN (Nat.add 16
    salt) rprp rprn lprp lprn rpin rpip lpip lpin qrvn qrvp lqrp lqrn qivn qivp lqip lqin)
    (sched_mulAdd4NegN (Nat.add 16 salt) rprp rprn lprp lprn rpin rpip lpip lpin qrvn qrvp lqrp
    lqrn qivn qivp lqip lqin)) (sched_mergeNodesCStep1 ldeg lprp lprn lpip lpin lqrp lqrn lqip
    lqin lerr rdeg rprp rprn rpip rpin rqrp rqrn rqip rqin prvp prvn pivp pivn qrvp qrvn qivp
    qivn rerr rep1 rb rk rbq rm rc salt)

/-- Pre-reverse the 8 words of `r` once at depth `d` and run `sched_mergeNodesCScalarGo`. -/
def sched_mergeNodesCRevGo (d : ℕ) (ldeg lprp lprn lpip lpin lqrp lqrn lqip lqin lerr : ℕ)
    (rdeg rprp rprn rpip rpin rqrp rqrn rqip rqin rerr : ℕ) (rep1 rb rk rbq rm rc salt : ℕ) :
    Option TreeNodeC :=
  let nr := Nat.add rdeg 1
  sched_stfOpt (Nat.add 80 salt) (fun prvp ↦
    sched_stfOpt (Nat.add 81 salt) (fun prvn ↦
      sched_stfOpt (Nat.add 82 salt) (fun pivp ↦
        sched_stfOpt (Nat.add 83 salt) (fun pivn ↦
          sched_stfOpt (Nat.add 84 salt) (fun qrvp ↦
            sched_stfOpt (Nat.add 85 salt) (fun qrvn ↦
              sched_stfOpt (Nat.add 86 salt) (fun qivp ↦
                sched_stfOpt (Nat.add 87 salt) (fun qivn ↦
                  sched_mergeNodesCScalarGo
                    ldeg lprp lprn lpip lpin lqrp lqrn lqip lqin lerr
                    rdeg rprp rprn rpip rpin rqrp rqrn rqip rqin
                    prvp prvn pivp pivn qrvp qrvn qivp qivn rerr
                    rep1 rb rk rbq rm rc salt)
                (revBin768 d nr rqin))
              (revBin768 d nr rqip))
            (revBin768 d nr rqrn))
          (revBin768 d nr rqrp))
        (revBin768 d nr rpin))
      (revBin768 d nr rpip))
    (revBin768 d nr rprn))
  (revBin768 d nr rprp)

/-- Unpack `(l, r)` fields and run `sched_mergeNodesCRevGo` with pre-multiplied masks. -/
def sched_mergeNodesCAuxMasks (d salt : ℕ) (l r : TreeNodeC)
    (rep1 rb rk rbq rm rc : ℕ) : Option TreeNodeC :=
  match l, r with
  | ⟨ldeg, _, _, lprp, lprn, lpip, lpin, lqrp, lqrn, lqip, lqin, lerr⟩,
    ⟨rdeg, _, _, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩ =>
    sched_mergeNodesCRevGo d
      ldeg lprp lprn lpip lpin lqrp lqrn lqip lqin lerr
      rdeg rprp rprn rpip rpin rqrp rqrn rqip rqin rerr
      rep1 rb rk rbq rm rc salt

/-- Force `(rbq, rm, rc)` masks and dispatch `sched_mergeNodesCAuxMasks`. -/
def sched_mergeNodesCAux2 (d salt : ℕ) (l r : TreeNodeC) (rep1 rb rk : ℕ) : Option TreeNodeC :=
    sched_stfOpt (Nat.add 4 salt) (fun rbq ↦ sched_stfOpt (Nat.add 5 salt) (fun rm ↦ sched_stfOpt
    (Nat.add 6 salt) (fun rc ↦ sched_mergeNodesCAuxMasks d salt l r rep1 rb rk rbq rm rc)
    (Nat.mul rep1 sched_clampHiLane)) (Nat.mul rep1 schedAux)) (Nat.mul rep1 sched_bQ)

/-- Force `(rb, rk)` masks and dispatch `sched_mergeNodesCAux2`. -/
def sched_mergeNodesCAux (d salt : ℕ) (l r : TreeNodeC) (rep1 : ℕ) : Option TreeNodeC :=
    sched_stfOpt (Nat.add 2 salt) (fun rb ↦ sched_stfOpt (Nat.add 3 salt) (fun rk ↦
    sched_mergeNodesCAux2 d salt l r rep1 rb rk) (Nat.mul rep1 sched_keepLane))
    (Nat.mul rep1 sched_bMid)

/-- Merge two `TreeNodeC` nodes using symbolic lane-reversal depth `d`. -/
def mergeNodesCGo (d : ℕ) (l r : TreeNodeC) : Option TreeNodeC :=
  let salt' := Nat.land (Nat.add 1 (Nat.xor (Nat.mul l.salt 0x9e3779b97f4a7c15) (Nat.mul
      r.salt 0xbf58476d1ce4e5b9))) 0xfffffffffffffff
  let rep1 := Nat.add l.rep1 (sched_shlDyn (sched_shr768 r.rep1) (Nat.mul 768 (Nat.add l.deg 1)))
  sched_tfOpt (fun s ↦ sched_tfOpt (sched_mergeNodesCAux d s l r) rep1) salt'

def mergeNodesC (l r : TreeNodeC) : Option TreeNodeC := mergeNodesCGo 19 l r

theorem sched_polyConv_neg_left (u v : ℕ → ℝ) (m : ℕ) :
    ta_polyConv (ta_polyNeg u) v m = -ta_polyConv u v m := by
  unfold ta_polyConv ta_polyNeg
  simp only [neg_mul, Finset.sum_neg_distrib]

theorem sched_polyPNValid_cast_deg {L1 L2 : ℕ} {pn : PolyPN} {f : ℕ → ℝ} (hL : L1 = L2)
    (h : PolyPNValid L1 pn f) : PolyPNValid L2 pn f := hL ▸ h

theorem sched_polyCApprox_trans {P Q R : PolyC} {e1 e2 : ℝ} (h1 : PolyCApprox P Q e1)
    (h2 : PolyCApprox Q R e2) : PolyCApprox P R (e1 + e2) := by
  refine ⟨fun m ↦ ?_, fun m ↦ ?_⟩
  · have ht := abs_sub_le (P.re m) (Q.re m) (R.re m)
    have a1 := h1.1 m; have a2 := h2.1 m; linarith
  · have ht := abs_sub_le (P.im m) (Q.im m) (R.im m)
    have a1 := h1.2 m; have a2 := h2.2 m; linarith

theorem mergeNodesCGo_spec (d : ℕ) (gs_l gs_r : List DyadicSu2Gate) (l r out : TreeNodeC)
    (hl : TreeNodeCValid gs_l l) (hr : TreeNodeCValid gs_r r)
    (hlen : (gs_l ++ gs_r).length ≤ 262144) (hd : r.deg + 1 ≤ 2 ^ d)
    (hm : mergeNodesCGo d l r = some out) : TreeNodeCValid (gs_l ++ gs_r) out := by
  rcases l with ⟨ldeg, lsalt, lrep1, lprp, lprn, lpip, lpin, lqrp, lqrn, lqip, lqin, lerr⟩
  rcases r with ⟨rdeg, rsalt, rrep1, rprp, rprn, rpip, rpin, rqrp, rqrn, rqip, rqin, rerr⟩
  rcases hl with ⟨hldeg, hl1, hl_err, hl_rep, PL_hat, QL_hat, hl_pr, hl_pi, hl_qr, hl_qi, hl_P,
    hl_Q⟩
  rcases hr with ⟨hrdeg, hr1, hr_err, hr_rep, PR_hat, QR_hat, hr_pr, hr_pi, hr_qr, hr_qi, hr_P,
    hr_Q⟩
  dsimp only [TreeNodeC.pr, TreeNodeC.pi, TreeNodeC.qr, TreeNodeC.qi] at *
  have hr_le : rdeg ≤ 262144 := by rw [List.length_append] at hlen; omega
  let rep1 := Nat.add lrep1
    (Nat.shiftLeft (Nat.shiftRight rrep1 768) (Nat.mul 768 (Nat.add ldeg 1)))
  have hrep_out : rep1 = pack768 (List.replicate (rdeg + ldeg + 1) 1) := by
    dsimp only [rep1]
    rw [sched_rep1_merge_eq ldeg rdeg lrep1 rrep1 hr1 hl_rep hr_rep]
    exact congrArg (fun m ↦ pack768 (List.replicate m 1)) (by omega)
  have hpr_rev := revPN_valid hd hr_pr
  have hpi_rev := revPN_valid hd hr_pi
  have hqr_rev := revPN_valid hd hr_qr
  have hqi_rev := revPN_valid hd hr_qi
  unfold mergeNodesCGo sched_mergeNodesCAux sched_mergeNodesCAux2 sched_mergeNodesCAuxMasks
    sched_mergeNodesCRevGo sched_mergeNodesCScalarGo at hm
  simp only [sched_tfOpt_eq, sched_stfOpt_eq, sched_shlDyn_eq, sched_shr768_eq] at hm
  rcases sched_optBind_eq_some hm with ⟨pr_s, hpr_s, hm1⟩
  unfold sched_mergeNodesCStep1 at hm1
  rcases sched_optBind_eq_some hm1 with ⟨pi_s, hpi_s, hm2⟩
  unfold sched_mergeNodesCStep2 at hm2
  rcases sched_optBind_eq_some hm2 with ⟨qr_s, hqr_s, hm3⟩
  unfold sched_mergeNodesCStep3 at hm3
  rcases sched_optBind_eq_some hm3 with ⟨qi_s, hqi_s, hm4⟩
  unfold sched_mergeNodesCStep4 sched_mergeNodesCStep5 sched_mkMergedNodeC at hm4
  simp only [sched_stfOpt_eq] at hm4
  cases herr_ble : Nat.ble
      (Nat.add 1 (Nat.mul (Nat.mul 4 (Nat.add 1 (if Nat.ble ldeg rdeg then ldeg else rdeg)))
        (Nat.add (Nat.mul 3 rerr) (Nat.mul 2 lerr))))
      sched_sTree with
  | false =>
    rw [herr_ble] at hm4
    simp only [Bool.false_eq_true, ↓reduceIte] at hm4
    cases hm4
  | true =>
    rw [herr_ble] at hm4
    simp only [↓reduceIte] at hm4
    injection hm4 with hout
    subst hout
    have herr_le : Nat.add 1 (Nat.mul (Nat.mul 4
        (Nat.add 1 (if Nat.ble ldeg rdeg then ldeg else rdeg)))
        (Nat.add (Nat.mul 3 rerr) (Nat.mul 2 lerr))) ≤ 2 ^ 352 := by
      rw [← sched_sTree_eq]
      exact Nat.ble_eq.mp herr_ble
    rcases mulAdd4_roundSplit_spec hr_le hrep_out hr_pr hl_pr (negPN_valid hr_pi) hl_pi
      (negPN_valid hqr_rev) hl_qr (negPN_valid hqi_rev) hl_qi
      (by exact sched_roundSplit768Masks_spec_bridge _ rep1 _ _ pr_s hpr_s) with
      ⟨fpr, hfpr_v, hfpr_e⟩
    rcases mulAdd4_roundSplit_spec hr_le hrep_out hr_pr hl_pi hr_pi hl_pr
      (negPN_valid hqr_rev) hl_qi hqi_rev hl_qr
      (by exact sched_roundSplit768Masks_spec_bridge _ rep1 _ _ pi_s hpi_s) with
      ⟨fpi, hfpi_v, hfpi_e⟩
    rcases mulAdd4_roundSplit_spec hr_le hrep_out hr_qr hl_pr (negPN_valid hr_qi) hl_pi
      hpr_rev hl_qr hpi_rev hl_qi
      (by exact sched_roundSplit768Masks_spec_bridge _ rep1 _ _ qr_s hqr_s) with
      ⟨fqr, hfqr_v, hfqr_e⟩
    rcases mulAdd4_roundSplit_spec hr_le hrep_out hr_qr hl_pi hr_qi hl_pr
      hpr_rev hl_qi (negPN_valid hpi_rev) hl_qr
      (by exact sched_roundSplit768Masks_spec_bridge _ rep1 _ _ qi_s hqi_s) with
      ⟨fqi, hfqi_v, hfqi_e⟩
    have habs_eq : ∀ {x y e : ℝ}, y = x → |x| ≤ e → |y| ≤ e := fun hxy hx ↦ by
      rw [hxy]
      exact hx
    have hPQ_rnd : PolyCApprox ⟨fpr, fpi⟩ (cdMul rdeg PR_hat QR_hat PL_hat QL_hat).1
        (1 / (2 ^ 352 : ℝ)) ∧ PolyCApprox ⟨fqr, fqi⟩ (cdMul rdeg PR_hat QR_hat PL_hat QL_hat).2
        (1 / (2 ^ 352 : ℝ)) := by
      refine ⟨⟨fun m ↦ habs_eq ?_ (hfpr_e m), fun m ↦ habs_eq ?_ (hfpi_e m)⟩,
              ⟨fun m ↦ habs_eq ?_ (hfqr_e m), fun m ↦ habs_eq ?_ (hfqi_e m)⟩⟩
      all_goals
        unfold cdMul polySubC polyAddC polyMulC polyConjRev ta_polySub ta_polyAdd
        dsimp only
        simp only [sched_polyConv_neg_left]
        ring
    have hEL_le1 : (lerr : ℝ) / (2 ^ 352 : ℝ) ≤ 1 :=
      (div_le_one (sched_two_pow_pos_real 352)).mpr (by exact_mod_cast hl_err)
    have hbnd3 : ∀ {P_h P : PolyC}, PolyCAbsBound 2 P_h →
        PolyCApprox P_h P ((lerr : ℝ) / (2 ^ 352 : ℝ)) → PolyCAbsBound 3 P := fun hb he ↦
      ⟨fun m ↦ ((polyCAbsBound_of_approx hb he).1 m).trans (by
         generalize (2 : ℝ) ^ 352 = S at hEL_le1 ⊢; linarith),
       fun m ↦ ((polyCAbsBound_of_approx hb he).2 m).trans (by
         generalize (2 : ℝ) ^ 352 = S at hEL_le1 ⊢; linarith)⟩
    rcases gateListTransferPQ_supp 48 gs_r with ⟨hPR_s, hQR_s⟩
    rcases gateListTransferPQ_supp 48 gs_l with ⟨hPL_s, hQL_s⟩
    have hbil := cdMul_bilinear_err (BR := 2) (BL := 3)
      (ER := (rerr : ℝ) / (2 ^ 352 : ℝ)) (EL := (lerr : ℝ) / (2 ^ 352 : ℝ))
      (by norm_num) (by norm_num)
      (div_nonneg (Nat.cast_nonneg _) (le_of_lt (sched_two_pow_pos_real 352)))
      (div_nonneg (Nat.cast_nonneg _) (le_of_lt (sched_two_pow_pos_real 352)))
      ⟨sched_polyPNValid_supp hr_pr, sched_polyPNValid_supp hr_pi⟩ (hrdeg ▸ hPR_s)
      ⟨sched_polyPNValid_supp hr_qr, sched_polyPNValid_supp hr_qi⟩ (hrdeg ▸ hQR_s)
      ⟨sched_polyPNValid_supp hl_pr, sched_polyPNValid_supp hl_pi⟩ (hldeg ▸ hPL_s)
      ⟨sched_polyPNValid_supp hl_qr, sched_polyPNValid_supp hl_qi⟩ (hldeg ▸ hQL_s)
      ⟨sched_polyPNValid_abs_le_two hr_pr, sched_polyPNValid_abs_le_two hr_pi⟩
      ⟨sched_polyPNValid_abs_le_two hr_qr, sched_polyPNValid_abs_le_two hr_qi⟩
      (hbnd3 ⟨sched_polyPNValid_abs_le_two hl_pr, sched_polyPNValid_abs_le_two hl_pi⟩ hl_P)
      (hbnd3 ⟨sched_polyPNValid_abs_le_two hl_qr, sched_polyPNValid_abs_le_two hl_qi⟩ hl_Q)
      hr_P hr_Q hl_P hl_Q
    have herr_eq : 1 / (2 ^ 352 : ℝ) + 4 * ((min rdeg ldeg + 1 : ℕ) : ℝ) * (2 * ((lerr : ℝ) /
        (2 ^ 352 : ℝ)) + 3 * ((rerr : ℝ) / (2 ^ 352 : ℝ))) = ((Nat.add 1 (Nat.mul (Nat.mul 4
        (Nat.add 1 (if Nat.ble ldeg rdeg then ldeg else rdeg))) (Nat.add (Nat.mul 3 rerr)
        (Nat.mul 2 lerr))) : ℕ) : ℝ) / (2 ^ 352 : ℝ) := by
      rw [show (if Nat.ble ldeg rdeg then ldeg else rdeg) = min rdeg ldeg by
            by_cases hle : ldeg ≤ rdeg
            · rw [ite_eq_left (Nat.ble_eq.mpr hle), Nat.min_eq_right hle]
            · rw [ite_eq_right (fun h ↦ hle (Nat.ble_eq.mp h)), Nat.min_eq_left (by omega)]]
      simp only [Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      generalize (2 : ℝ) ^ 352 = S
      ring
    have hPQ_app := hrdeg ▸ gateListTransferPQ_append 48 gs_l gs_r
    have hdeg_comm : rdeg + ldeg = Nat.add ldeg rdeg := Nat.add_comm rdeg ldeg
    exact ⟨by
      simp [List.length_append, hldeg, hrdeg], Nat.le_trans hl1 (Nat.le_add_right ldeg rdeg),
      herr_le,
      hrep_out.trans (congrArg (pack768 <| List.replicate · 1) (congrArg (· + 1) hdeg_comm)),
      ⟨fpr, fpi⟩, ⟨fqr, fqi⟩,
      sched_polyPNValid_cast_deg hdeg_comm hfpr_v, sched_polyPNValid_cast_deg hdeg_comm hfpi_v,
      sched_polyPNValid_cast_deg hdeg_comm hfqr_v, sched_polyPNValid_cast_deg hdeg_comm hfqi_v,
      by dsimp only; rw [hPQ_app, ← herr_eq]; exact sched_polyCApprox_trans hPQ_rnd.1 hbil.1,
      by dsimp only; rw [hPQ_app, ← herr_eq]; exact sched_polyCApprox_trans hPQ_rnd.2 hbil.2⟩

theorem mergeNodesC_spec (gs_l gs_r : List DyadicSu2Gate) (l r out : TreeNodeC)
    (hl : TreeNodeCValid gs_l l) (hr : TreeNodeCValid gs_r r)
    (hlen : (gs_l ++ gs_r).length ≤ 262144) (hm : mergeNodesC l r = some out) :
    TreeNodeCValid (gs_l ++ gs_r) out :=
  mergeNodesCGo_spec 19 gs_l gs_r l r out hl hr hlen
    ((by
        have := hr.1
        rw [List.length_append] at hlen
        omega : r.deg + 1 ≤ 262145).trans (Nat.ble_eq.mp rfl)) hm

def sched_pairPos (sA : Bool) (uA : ℕ) (sB : Bool) (uB : ℕ) : ℕ :=
  Nat.add (@Bool.casesOn (fun _ ↦ ℕ) sA uA 0) (@Bool.casesOn (fun _ ↦ ℕ) sB uB 0)

/-- Negative `97`-bit accumulator of `smToInt sA uA + smToInt sB uB`. -/
def sched_pairNeg (sA : Bool) (uA : ℕ) (sB : Bool) (uB : ℕ) : ℕ :=
  Nat.add (@Bool.casesOn (fun _ ↦ ℕ) sA 0 uA) (@Bool.casesOn (fun _ ↦ ℕ) sB 0 uB)

theorem sched_pairPos_sub_neg_real (sA : Bool) (uA : ℕ) (sB : Bool) (uB : ℕ) :
    ((sched_pairPos sA uA sB uB : ℝ) - (sched_pairNeg sA uA sB uB : ℝ)) =
      (smToInt sA uA : ℝ) + (smToInt sB uB : ℝ) := by
  cases sA <;> cases sB <;>
    simp only [sched_pairPos, sched_pairNeg, smToInt, Bool.false_eq_true, ↓reduceIte,
      Nat.add_eq, Nat.cast_add, Nat.cast_zero, Int.cast_neg, Int.cast_natCast] <;> ring

theorem sched_smToInt_mul_xor (s2 s1 : Bool) (m2 m1 : ℕ) :
    (smToInt (xor s2 s1) (Nat.mul m2 m1) : ℝ) =
      (smToInt s2 m2 : ℝ) * (smToInt s1 m1 : ℝ) := by
  cases s2 <;> cases s1 <;>
    simp only [xor, Bool.bne_true, Bool.bne_false, Bool.not_true, Bool.not_false,
      smToInt, Bool.false_eq_true, ↓reduceIte, Nat.mul_eq,
      Int.cast_neg, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] <;> ring

theorem sched_smToInt_mul_nxor (s2 s1 : Bool) (m2 m1 : ℕ) :
    (smToInt (Bool.not (xor s2 s1)) (Nat.mul m2 m1) : ℝ) =
      -((smToInt s2 m2 : ℝ) * (smToInt s1 m1 : ℝ)) := by
  cases s2 <;> cases s1 <;>
    simp only [xor, Bool.bne_true, Bool.bne_false, Bool.not_true, Bool.not_false,
      smToInt, Bool.false_eq_true, ↓reduceIte, Nat.mul_eq,
      Int.cast_neg, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] <;> ring

/-- Pack lanes `m = 1` (`c1 <<< 256`) and `m = 2` (`c2 <<< 256`) into a `768`-bit SWAR word. -/
def sched_pack12Word (s c1 c2 : ℕ) : ℕ := Nat.add (sched_shl1024 (sched_idSalt s c1))
    (sched_shl256 (sched_shl1536 (sched_idSalt (Nat.add 1 s) c2)))

/-- Guard `p ≤ 2 ^ 97 - 1 ∧ n ≤ 2 ^ 97 - 1` on a pair-leaf coefficient. -/
def sched_pairLe97 (p n : ℕ) : Bool :=
  Bool.and (Nat.ble p 0x1ffffffffffffffffffffffff) (Nat.ble n 0x1ffffffffffffffffffffffff)

/-- Strict `TreeNodeC` constructor for degree-`2` `pairLeafNodeC`. -/
def sched_mkPairNodeC (s pr1p pr1n pr2p pr2n pi1p pi1n pi2p pi2n qr1p qr1n qr2p qr2n qi1p qi1n
    qi2p qi2n : ℕ) : Option TreeNodeC := sched_stfOpt (Nat.add 10 s) (fun prp ↦ sched_stfOpt
    (Nat.add 12 s) (fun prn ↦ sched_stfOpt (Nat.add 14 s) (fun pip ↦ sched_stfOpt (Nat.add 16 s)
    (fun pin ↦ sched_stfOpt (Nat.add 18 s) (fun qrp ↦ sched_stfOpt (Nat.add 20 s) (fun qrn ↦
    sched_stfOpt (Nat.add 22 s) (fun qip ↦ sched_stfOpt (Nat.add 24 s) (fun qin ↦ some ⟨2, s,
    sched_rep3One, prp, prn, pip, pin, qrp, qrn, qip, qin, 0⟩) (sched_pack12Word (Nat.add 24 s)
    qi1n qi2n)) (sched_pack12Word (Nat.add 22 s) qi1p qi2p)) (sched_pack12Word (Nat.add 20 s)
    qr1n qr2n)) (sched_pack12Word (Nat.add 18 s) qr1p qr2p)) (sched_pack12Word (Nat.add 16 s)
    pi1n pi2n)) (sched_pack12Word (Nat.add 14 s) pi1p pi2p)) (sched_pack12Word (Nat.add 12 s)
    pr1n pr2n)) (sched_pack12Word (Nat.add 10 s) pr1p pr2p)

/-- Build a degree-`2` `TreeNodeC` directly from `(g1, g2)` at `96`-bit exact precision (`err =
0`). -/
def pairLeafNodeC (g1 g2 : DyadicSu2Gate) : Option TreeNodeC :=
  if Bool.and
      (Bool.and
        (Bool.and (Nat.ble g1.mar 0x1000000000000) (Nat.ble g1.mai 0x1000000000000))
        (Bool.and (Nat.ble g1.mbr 0x1000000000000) (Nat.ble g1.mbi 0x1000000000000)))
      (Bool.and
        (Bool.and (Nat.ble g2.mar 0x1000000000000) (Nat.ble g2.mai 0x1000000000000))
        (Bool.and (Nat.ble g2.mbr 0x1000000000000) (Nat.ble g2.mbi 0x1000000000000))) then
    let pr1p := sched_pairPos (Bool.not (xor g2.sbr g1.sbr)) (Nat.mul g2.mbr g1.mbr)
                             (Bool.not (xor g2.sbi g1.sbi)) (Nat.mul g2.mbi g1.mbi)
    let pr1n := sched_pairNeg (Bool.not (xor g2.sbr g1.sbr)) (Nat.mul g2.mbr g1.mbr)
                             (Bool.not (xor g2.sbi g1.sbi)) (Nat.mul g2.mbi g1.mbi)
    let pr2p := sched_pairPos (xor g2.sar g1.sar) (Nat.mul g2.mar g1.mar)
                             (Bool.not (xor g2.sai g1.sai)) (Nat.mul g2.mai g1.mai)
    let pr2n := sched_pairNeg (xor g2.sar g1.sar) (Nat.mul g2.mar g1.mar)
                             (Bool.not (xor g2.sai g1.sai)) (Nat.mul g2.mai g1.mai)
    let pi1p := sched_pairPos (xor g2.sbi g1.sbr) (Nat.mul g2.mbi g1.mbr)
                             (Bool.not (xor g2.sbr g1.sbi)) (Nat.mul g2.mbr g1.mbi)
    let pi1n := sched_pairNeg (xor g2.sbi g1.sbr) (Nat.mul g2.mbi g1.mbr)
                             (Bool.not (xor g2.sbr g1.sbi)) (Nat.mul g2.mbr g1.mbi)
    let pi2p := sched_pairPos (xor g2.sar g1.sai) (Nat.mul g2.mar g1.mai)
                             (xor g2.sai g1.sar) (Nat.mul g2.mai g1.mar)
    let pi2n := sched_pairNeg (xor g2.sar g1.sai) (Nat.mul g2.mar g1.mai)
                             (xor g2.sai g1.sar) (Nat.mul g2.mai g1.mar)
    let qr1p := sched_pairPos (xor g2.sar g1.sbr) (Nat.mul g2.mar g1.mbr)
                             (xor g2.sai g1.sbi) (Nat.mul g2.mai g1.mbi)
    let qr1n := sched_pairNeg (xor g2.sar g1.sbr) (Nat.mul g2.mar g1.mbr)
                             (xor g2.sai g1.sbi) (Nat.mul g2.mai g1.mbi)
    let qr2p := sched_pairPos (xor g2.sbr g1.sar) (Nat.mul g2.mbr g1.mar)
                             (Bool.not (xor g2.sbi g1.sai)) (Nat.mul g2.mbi g1.mai)
    let qr2n := sched_pairNeg (xor g2.sbr g1.sar) (Nat.mul g2.mbr g1.mar)
                             (Bool.not (xor g2.sbi g1.sai)) (Nat.mul g2.mbi g1.mai)
    let qi1p := sched_pairPos (xor g2.sar g1.sbi) (Nat.mul g2.mar g1.mbi)
                             (Bool.not (xor g2.sai g1.sbr)) (Nat.mul g2.mai g1.mbr)
    let qi1n := sched_pairNeg (xor g2.sar g1.sbi) (Nat.mul g2.mar g1.mbi)
                             (Bool.not (xor g2.sai g1.sbr)) (Nat.mul g2.mai g1.mbr)
    let qi2p := sched_pairPos (xor g2.sbr g1.sai) (Nat.mul g2.mbr g1.mai)
                             (xor g2.sbi g1.sar) (Nat.mul g2.mbi g1.mar)
    let qi2n := sched_pairNeg (xor g2.sbr g1.sai) (Nat.mul g2.mbr g1.mai)
                             (xor g2.sbi g1.sar) (Nat.mul g2.mbi g1.mar)
    if Bool.and
        (Bool.and (Bool.and (sched_pairLe97 pr1p pr1n) (sched_pairLe97 pr2p pr2n))
                  (Bool.and (sched_pairLe97 pi1p pi1n) (sched_pairLe97 pi2p pi2n)))
        (Bool.and (Bool.and (sched_pairLe97 qr1p qr1n) (sched_pairLe97 qr2p qr2n))
                  (Bool.and (sched_pairLe97 qi1p qi1n) (sched_pairLe97 qi2p qi2n))) then
      let salt0 := Nat.land (Nat.add 1 (Nat.xor (Nat.mul 0x9e3779b97f4a7c15 g1.mar) (Nat.mul
          0xbf58476d1ce4e5b9 g2.mar))) 0xfffffffffffffff
      sched_tfOpt (fun s ↦
        sched_mkPairNodeC s pr1p pr1n pr2p pr2n pi1p pi1n pi2p pi2n
          qr1p qr1n qr2p qr2n qi1p qi1n qi2p qi2n) salt0
    else
      sched_optBind (leafNodeC g1) (fun l1 ↦ sched_optBind (leafNodeC g2) (mergeNodesC l1))
  else none

/-- `2 ^ 256` as a pre-parsed hexadecimal literal for WHNF-neutral `sched_pow256 * c` scaling. -/
def sched_pow256 : ℕ := 0x10000000000000000000000000000000000000000000000000000000000000000

theorem sched_pairChannel_valid (s1 s2 p1 n1 p2 n2 : ℕ)
    (h1 : sched_pairLe97 p1 n1 = true) (h2 : sched_pairLe97 p2 n2 = true) :
    PolyPNValid 2 ⟨sched_pack12Word s1 p1 p2, sched_pack12Word s2 n1 n2⟩
      (fun idx ↦ if idx = 1 then ((p1 : ℝ) - (n1 : ℝ)) / (2 ^ 96 : ℝ)
                 else if idx = 2 then ((p2 : ℝ) - (n2 : ℝ)) / (2 ^ 96 : ℝ) else 0) := by
  have hm97 : sched_pow256 * 0x1ffffffffffffffffffffffff < 2 ^ 353 := Nat.ble_eq.mp rfl
  simp only [sched_pairLe97, Bool.and_eq_true, Nat.ble_eq] at h1 h2
  have hmem : ∀ a b : ℕ, a ≤ 0x1ffffffffffffffffffffffff → b ≤ 0x1ffffffffffffffffffffffff →
      ∀ x ∈ ([0, sched_pow256 * a, sched_pow256 * b] : List ℕ), x < 2 ^ 353 := by
    intro a b ha hb x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.two_pow_pos 353
    · exact (Nat.mul_le_mul_left sched_pow256 ha).trans_lt hm97
    · exact (Nat.mul_le_mul_left sched_pow256 hb).trans_lt hm97
  have hpack : ∀ s c1 c2 : ℕ,
      sched_pack12Word s c1 c2 = pack768 [0, sched_pow256 * c1, sched_pow256 * c2] := fun s c1 c2 ↦
        by
    have hshl_mul : ∀ x n : ℕ, Nat.shiftLeft x n = x * 2 ^ n := Nat.shiftLeft_eq
    unfold sched_pack12Word sched_shl1024 sched_shl1536 sched_shl256
    rw [sched_idSalt_eq, sched_idSalt_eq, sched_pack768_cons, sched_pack768_cons,
      sched_pack768_cons,
        sched_pack768_nil, sched_shiftLeft_768_eq, sched_shiftLeft_768_eq, sched_shiftLeft_768_eq]
    simp only [Nat.add_eq, hshl_mul]
    rw [show (2 : ℕ) ^ 1024 = sched_pow768 * sched_pow256 from rfl,
        Nat.mul_assoc c2 (2 ^ 1536) (2 ^ 256),
        show (2 : ℕ) ^ 1536 * 2 ^ 256 = sched_pow768 * (sched_pow768 * sched_pow256) from rfl]
    ring
  have hcast : ∀ a b : ℕ, (((sched_pow256 * a : ℕ) : ℝ) - ((sched_pow256 * b : ℕ) : ℝ)) /
      (2 ^ 352 : ℝ) = ((a : ℝ) - (b : ℝ)) / (2 ^ 96 : ℝ) := fun a b ↦ by
    rw [Nat.cast_mul, Nat.cast_mul, show sched_pow256 = 2 ^ 256 from rfl,
        Nat.cast_pow, Nat.cast_ofNat,
        show (2 : ℝ) ^ 352 = (2 : ℝ) ^ 96 * (2 : ℝ) ^ 256 by
          rw [show (352 : ℕ) = 96 + 256 from rfl, pow_add],
        mul_comm ((2 : ℝ) ^ 256) (a : ℝ), mul_comm ((2 : ℝ) ^ 256) (b : ℝ), ← sub_mul]
    exact mul_div_mul_right _ _ (ne_of_gt (sched_two_pow_pos_real 256))
  unfold PolyPNValid
  dsimp only
  refine ⟨[0, sched_pow256 * p1, sched_pow256 * p2], [0, sched_pow256 * n1, sched_pow256 * n2],
    rfl, rfl, hmem p1 p2 h1.1 h2.1, hmem n1 n2 h1.2 h2.2,
    hpack s1 p1 p2, hpack s2 n1 n2, fun idx ↦ ?_⟩
  rcases idx with _ | _ | _ | k
  · simp only [Nat.zero_le, show (0 : ℕ) ≠ 1 by omega, show (0 : ℕ) ≠ 2 by omega, ↓reduceIte,
      List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      Nat.cast_zero, sub_self, zero_div]
  · simp only [show 1 ≤ 2 by omega, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    exact (hcast p1 n1).symm
  · simp only [Nat.le_refl, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte,
      List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
    exact (hcast p2 n2).symm
  · simp only [show ¬(k + 3 ≤ 2) by omega, show k + 3 ≠ 1 by omega,
      show k + 3 ≠ 2 by omega, ↓reduceIte]

theorem sched_gateListTransferPQ_pair (b : ℕ) (g1 g2 : DyadicSu2Gate) (m : ℕ) :
    let ab1 := gateSu2Pair b g1
    let ab2 := gateSu2Pair b g2
    (gateListTransferPQ b [g1, g2]).1.toC m =
      (if m = 1 then -(star ab2.2 * ab1.2) else if m = 2 then ab2.1 * ab1.1 else 0) ∧
    (gateListTransferPQ b [g1, g2]).2.toC m =
      (if m = 1 then star ab2.1 * ab1.2 else if m = 2 then ab2.2 * ab1.1 else 0) := by
  have hcr : ∀ v : ℂ, polyConjRev 1 (polyDelta1C v) = polyDelta0C (star v) := fun v ↦ by
    apply PolyC.ext_toC; intro k; rw [polyConjRev_toC, polyDelta0C_toC]
    rcases k with _ | _ | _ <;> simp
  rw [show ([g1, g2] : List DyadicSu2Gate) = [g1] ++ [g2] from rfl,
      gateListTransferPQ_append b [g1] [g2], List.length_singleton,
      sched_gateListTransferPQ_singleton b g2, sched_gateListTransferPQ_singleton b g1]
  unfold cdMul; dsimp only
  rw [hcr, hcr, polySubC_toC, polyAddC_toC,
      polyMulC_delta1_left, polyMulC_delta0_left, polyMulC_delta1_left, polyMulC_delta0_left]
  rcases m with _ | _ | _ | _ <;> simp [sub_eq_neg_add]

theorem pairLeafNodeC_spec (g1 g2 : DyadicSu2Gate) (nd : TreeNodeC)
    (h : pairLeafNodeC g1 g2 = some nd) : TreeNodeCValid [g1, g2] nd := by
  unfold pairLeafNodeC at h
  split at h
  · dsimp only at h
    split at h
    · rename_i _ hle97
      simp only [Bool.and_eq_true] at hle97
      rcases hle97 with ⟨⟨⟨hpr1, hpr2⟩, ⟨hpi1, hpi2⟩⟩, ⟨⟨hqr1, hqr2⟩, ⟨hqi1, hqi2⟩⟩⟩
      simp only [sched_tfOpt_eq, sched_mkPairNodeC, sched_stfOpt_eq] at h
      injection h with hnd; subst hnd
      have hite_p : ∀ (proj : ℂ → ℝ) (h0 : proj 0 = 0) (c1 c2 : ℂ) (m : ℕ),
          proj (if m = 1 then c1 else if m = 2 then c2 else 0) =
            (if m = 1 then proj c1 else if m = 2 then proj c2 else 0) := fun _ h0 _ _ m ↦ by
        rcases m with _ | _ | _ | _ <;> simp [h0]
      have hite_eq : ∀ {a1 b1 a2 b2 : ℝ} (m : ℕ), a1 = b1 → a2 = b2 →
          (if m = 1 then a1 else if m = 2 then a2 else 0) =
            (if m = 1 then b1 else if m = 2 then b2 else 0) := fun _ e1 e2 ↦ by rw [e1, e2]
      have h0e : ∀ f : ℕ → ℝ, ∀ m, |f m - f m| ≤ ((0 : ℕ) : ℝ) / (2 ^ 352 : ℝ) :=
        fun _ _ ↦ by simp only [Nat.cast_zero, zero_div, sub_self, abs_zero, le_refl]
      have hrep3 : sched_rep3One = pack768 (List.replicate 3 1) := by
        simp only [List.replicate, sched_pack768_cons, sched_pack768_nil,
          sched_shiftLeft_768_eq]; rfl
      let salt0 := Nat.land (Nat.add 1 (Nat.xor (Nat.mul 0x9e3779b97f4a7c15 g1.mar) (Nat.mul
          0xbf58476d1ce4e5b9 g2.mar))) 0xfffffffffffffff
      refine ⟨rfl, Nat.ble_eq.mp rfl, Nat.zero_le _, hrep3,
        (gateListTransferPQ 48 [g1, g2]).1, (gateListTransferPQ 48 [g1, g2]).2,
        ?_, ?_, ?_, ?_, ⟨h0e _, h0e _⟩, ⟨h0e _, h0e _⟩⟩
      all_goals
        dsimp only [TreeNodeC.pr, TreeNodeC.pi, TreeNodeC.qr, TreeNodeC.qi]
        first
        | refine sched_polyPNValid_congr_fn
            (sched_pairChannel_valid (Nat.add 10 salt0) (Nat.add 12 salt0) _ _ _ _ hpr1 hpr2) ?_
        | refine sched_polyPNValid_congr_fn
            (sched_pairChannel_valid (Nat.add 14 salt0) (Nat.add 16 salt0) _ _ _ _ hpi1 hpi2) ?_
        | refine sched_polyPNValid_congr_fn
            (sched_pairChannel_valid (Nat.add 18 salt0) (Nat.add 20 salt0) _ _ _ _ hqr1 hqr2) ?_
        | refine sched_polyPNValid_congr_fn
            (sched_pairChannel_valid (Nat.add 22 salt0) (Nat.add 24 salt0) _ _ _ _ hqi1 hqi2) ?_
        intro m
        first
        | rw [← PolyC.toC_re, (sched_gateListTransferPQ_pair 48 g1 g2 m).1,
              hite_p Complex.re Complex.zero_re]
        | rw [← PolyC.toC_im, (sched_gateListTransferPQ_pair 48 g1 g2 m).1,
              hite_p Complex.im Complex.zero_im]
        | rw [← PolyC.toC_re, (sched_gateListTransferPQ_pair 48 g1 g2 m).2,
              hite_p Complex.re Complex.zero_re]
        | rw [← PolyC.toC_im, (sched_gateListTransferPQ_pair 48 g1 g2 m).2,
              hite_p Complex.im Complex.zero_im]
        apply hite_eq m
        all_goals
          simp only [gateSu2Pair, gateSu2ARe, gateSu2AIm, gateSu2BRe, gateSu2BIm,
            Complex.star_def, star_add, star_mul, Complex.conj_ofReal, Complex.conj_I,
            Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
            Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            sched_pairPos_sub_neg_real, sched_smToInt_mul_xor, sched_smToInt_mul_nxor]
          ring
    · rcases sched_optBind_eq_some h with ⟨l1, hl1, h2⟩
      rcases sched_optBind_eq_some h2 with ⟨l2, hl2, hm⟩
      exact mergeNodesC_spec [g1] [g2] l1 l2 nd (leafNodeC_spec g1 l1 hl1)
        (leafNodeC_spec g2 l2 hl2) (Nat.ble_eq.mp rfl) hm
  · cases h

/-- Identity trampoline barrier preventing C++ WHNF stack growth on `@List.rec` loops. -/
def sched_tramp {α : Type} (x : α) : α := x

/-- `O(1)`-stack tail-recursive list reversal on `List TreeNodeC`. -/
def sched_revNodesTR (xs acc : List TreeNodeC) : List TreeNodeC := @List.rec TreeNodeC
    (fun _ ↦ List TreeNodeC → List TreeNodeC) (fun a ↦ a)
    (fun x _ ih a ↦ sched_tramp (ih (x :: a))) xs acc

theorem sched_revNodesTR_eq : ∀ (xs acc : List TreeNodeC),
    sched_revNodesTR xs acc = xs.reverse ++ acc
  | [], _ => rfl
  | x :: xs, acc => by
      rw [show sched_revNodesTR (x :: xs) acc = sched_revNodesTR xs (x :: acc) from rfl,
          sched_revNodesTR_eq xs (x :: acc)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem sched_forall2_nil_right {α β : Type} {R : α → β → Prop} {xs : List α}
    (h : List.Forall₂ R xs []) : xs = [] := by
  cases h; rfl

theorem sched_forall2_cons_right {α β : Type} {R : α → β → Prop} {xs : List α} {y : β} {ys : List β}
    (h : List.Forall₂ R xs (y :: ys)) :
    ∃ x xt, xs = x :: xt ∧ R x y ∧ List.Forall₂ R xt ys := by
  cases h with
  | cons hxy hrest => exact ⟨_, _, rfl, hxy, hrest⟩

theorem sched_forall2_append {α β : Type} {R : α → β → Prop} {xs1 xs2 : List α}
    {ys1 ys2 : List β} (h1 : List.Forall₂ R xs1 ys1) (h2 : List.Forall₂ R xs2 ys2) :
    List.Forall₂ R (xs1 ++ xs2) (ys1 ++ ys2) := by
  induction h1 with
  | nil => exact h2
  | cons hxy _ ih => exact List.Forall₂.cons hxy ih

theorem sched_forall2_reverse {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : List.Forall₂ R xs.reverse ys.reverse := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hxy _ ih =>
      rw [List.reverse_cons, List.reverse_cons]
      exact sched_forall2_append ih (List.Forall₂.cons hxy List.Forall₂.nil)

/-- Reverse `nd :: a` at the end of an odd-length gate stream. -/
def sched_pushTrailingLeafC (a : List TreeNodeC) (nd : TreeNodeC) : Option (List TreeNodeC) :=
  some (sched_revNodesTR (nd :: a) [])

/-- Build a trailing degree-`1` leaf when a gate pair stream ends with one buffered gate. -/
def sched_finishLeavesSomeC (a : List TreeNodeC) (g1 : DyadicSu2Gate) : Option (List TreeNodeC) :=
  sched_optBind (leafNodeC g1) (sched_pushTrailingLeafC a)

/-- Finalize `leavesChunksPairsC` from the optional buffered gate `st` and reversed accumulator
`a`. -/
def sched_finishLeavesPairsC (st : Option DyadicSu2Gate) (a : List TreeNodeC) : Option
    (List TreeNodeC) := @Option.casesOn DyadicSu2Gate (fun _ ↦ Option (List TreeNodeC)) st
    (some (sched_revNodesTR a [])) (sched_finishLeavesSomeC a)

/-- Push a newly constructed degree-`2` pair leaf onto `a` and continue with `st = none`. -/
def sched_pushPairLeafC (ih : Option DyadicSu2Gate → List TreeNodeC → Option (List TreeNodeC))
    (a : List TreeNodeC) (nd : TreeNodeC) : Option (List TreeNodeC) := ih none (nd :: a)

/-- Fuse buffered gate `g1` with `g2` via `pairLeafNodeC` and invoke `sched_pushPairLeafC`. -/
def sched_leavesChunkPairSomeC (ih : Option DyadicSu2Gate → List TreeNodeC → Option (List
    TreeNodeC)) (g2 : DyadicSu2Gate) (a : List TreeNodeC) (g1 : DyadicSu2Gate) : Option
    (List TreeNodeC) := sched_optBind (pairLeafNodeC g1 g2) (sched_pushPairLeafC ih a)

/-- Consume one gate chunk `gs` in CPS, pairing adjacent gates across chunk boundaries. -/
def sched_leavesChunkPairsContC (k : Option DyadicSu2Gate → List TreeNodeC → Option (List
    TreeNodeC)) (gs : List DyadicSu2Gate) (st : Option DyadicSu2Gate) (acc : List TreeNodeC) :
    Option (List TreeNodeC) := @List.rec DyadicSu2Gate (fun _ ↦ Option DyadicSu2Gate → List
    TreeNodeC → Option (List TreeNodeC)) k (fun g _ ih s a ↦ @Option.casesOn DyadicSu2Gate
    (fun _ ↦ Option (List TreeNodeC)) s (sched_tramp (ih (some g) a)) (sched_tramp
    (sched_leavesChunkPairSomeC ih g a))) gs st acc

/-- Consume all gate chunks `chs` into degree-`2` pair leaves (plus optional trailing
`leafNodeC`). -/
def sched_leavesChunksPairsC (chs : List (List DyadicSu2Gate)) (st : Option DyadicSu2Gate)
    (acc : List TreeNodeC) : Option (List TreeNodeC) := @List.rec (List DyadicSu2Gate) (fun _
    ↦ Option DyadicSu2Gate → List TreeNodeC → Option (List TreeNodeC)) sched_finishLeavesPairsC
    (fun ch _ ih s a ↦ sched_tramp (sched_leavesChunkPairsContC ih ch s a)) chs st acc

/-- Build the bottom tournament leaf list from chunked `DyadicSu2Gate` slices. -/
def leavesChunksRevC (chs : List (List DyadicSu2Gate)) (acc : List TreeNodeC) : Option
    (List TreeNodeC) := sched_leavesChunksPairsC chs none acc

theorem leavesChunksRevC_spec (chunks : List (List DyadicSu2Gate)) (leaves : List TreeNodeC)
    (h : leavesChunksRevC chunks [] = some leaves) :
    ∃ gss, List.Forall₂ TreeNodeCValid gss leaves ∧ gss.flatten = chunks.flatten := by
  have hcs : ∀ k g1 g2 gs acc, sched_leavesChunkPairsContC k (g2 :: gs) (some g1) acc =
      sched_optBind (pairLeafNodeC g1 g2)
        (fun nd ↦ sched_leavesChunkPairsContC k gs none (nd :: acc)) := fun _ _ _ _ _ ↦ rfl
  have happ : ∀ k (xs ys : List DyadicSu2Gate) st acc,
      sched_leavesChunkPairsContC k (xs ++ ys) st acc =
        sched_leavesChunkPairsContC (sched_leavesChunkPairsContC k ys) xs st acc := fun k xs ↦ by
    induction xs with
    | nil => exact fun _ _ _ ↦ rfl
    | cons g gs ih =>
        rintro ys (_ | g1) acc
        · exact ih ys (some g) acc
        · simp only [List.cons_append, hcs]
          exact Option.casesOn (pairLeafNodeC g1 g) rfl fun nd ↦ ih ys none (nd :: acc)
  have hflat_eq : ∀ (chs : List (List DyadicSu2Gate)) st acc,
      sched_leavesChunksPairsC chs st acc =
        sched_leavesChunkPairsContC sched_finishLeavesPairsC chs.flatten st acc := fun chs ↦ by
    induction chs with
    | nil => exact fun _ _ ↦ rfl
    | cons ch chs ih =>
        intro st acc
        exact (congrFun (congrFun (congrArg (fun f ↦ sched_leavesChunkPairsContC f ch)
          (funext fun s ↦ funext fun a ↦ ih s a)) st) acc).trans (happ _ ch _ st acc).symm
  have hspec : ∀ (gs : List DyadicSu2Gate) (acc : List TreeNodeC)
      (gss_acc : List (List DyadicSu2Gate)),
      (List.Forall₂ TreeNodeCValid gss_acc acc →
        sched_leavesChunkPairsContC sched_finishLeavesPairsC gs none acc = some leaves →
        ∃ gss_out, List.Forall₂ TreeNodeCValid gss_out leaves ∧
          gss_out.flatten = gss_acc.reverse.flatten ++ gs) ∧
      (∀ g1, List.Forall₂ TreeNodeCValid gss_acc acc →
        sched_leavesChunkPairsContC sched_finishLeavesPairsC gs (some g1) acc = some leaves →
        ∃ gss_out, List.Forall₂ TreeNodeCValid gss_out leaves ∧
          gss_out.flatten = gss_acc.reverse.flatten ++ (g1 :: gs)) := by
    intro gs
    induction gs with
    | nil =>
        intro acc gss_acc
        refine ⟨fun hf2 hn ↦ ?_, fun g1 hf2 hs ↦ ?_⟩
        · injection hn with heq
          subst heq
          rw [sched_revNodesTR_eq, List.append_nil]
          exact ⟨gss_acc.reverse, sched_forall2_reverse hf2, by simp only [List.append_nil]⟩
        · rcases sched_optBind_eq_some hs with ⟨nd, hnd, hs⟩
          injection hs with heq
          subst heq
          rw [sched_revNodesTR_eq, List.append_nil, List.reverse_cons]
          exact ⟨gss_acc.reverse ++ [[g1]],
            sched_forall2_append (sched_forall2_reverse hf2)
              (List.Forall₂.cons (leafNodeC_spec g1 nd hnd) List.Forall₂.nil),
            by simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
                 List.append_nil]⟩
    | cons g2 rest ih =>
        intro acc gss_acc
        refine ⟨fun hf2 hn ↦ (ih acc gss_acc).2 g2 hf2 hn, fun g1 hf2 hs ↦ ?_⟩
        rw [hcs] at hs
        rcases sched_optBind_eq_some hs with ⟨nd, hnd, hs⟩
        rcases (ih (nd :: acc) ([g1, g2] :: gss_acc)).1
            (List.Forall₂.cons (pairLeafNodeC_spec g1 g2 nd hnd) hf2) hs with ⟨gss_out, hf2_o,
              hfl_o⟩
        exact ⟨gss_out, hf2_o, by simpa only [List.reverse_cons, List.flatten_append,
          List.flatten_cons, List.flatten_nil, List.append_nil, List.nil_append,
          List.append_assoc, List.cons_append] using hfl_o⟩
  unfold leavesChunksRevC at h
  rw [hflat_eq] at h
  rcases (hspec chunks.flatten [] []).1 List.Forall₂.nil h with ⟨gss, hf2, hfl⟩
  exact ⟨gss, hf2, by simpa only [List.reverse_nil, List.flatten_nil, List.nil_append] using hfl⟩

/-- Reverse `x :: a` when an odd-count tournament level ends with one buffered node `x`. -/
def sched_finishMergePairsSomeC (a : List TreeNodeC) (x : TreeNodeC) : Option (List TreeNodeC) :=
  some (sched_revNodesTR (x :: a) [])

theorem sched_len_mid_le {a b c m : List DyadicSu2Gate} {B : ℕ}
    (h : (a ++ (b ++ (c ++ m))).length ≤ B) : (b ++ c).length ≤ B := by
  simp only [List.length_append] at h ⊢
  omega

def sched_evalTournamentBaseC (nds : List TreeNodeC) : Option TreeNodeC :=
  @List.casesOn TreeNodeC (fun _ ↦ Option TreeNodeC) nds none (fun r rest0 ↦
    @List.casesOn TreeNodeC (fun _ ↦ Option TreeNodeC) rest0 (some r) (fun _ _ ↦ none))

def treeNodeCPayloadBeq (a b : TreeNodeC) : Bool := Bool.and (Nat.beq a.deg b.deg) (Bool.and
    (Nat.beq a.rep1 b.rep1) (Bool.and (Nat.beq a.prp b.prp) (Bool.and (Nat.beq a.prn b.prn)
    (Bool.and (Nat.beq a.pip b.pip) (Bool.and (Nat.beq a.pin b.pin) (Bool.and (Nat.beq a.qrp
    b.qrp) (Bool.and (Nat.beq a.qrn b.qrn) (Bool.and (Nat.beq a.qip b.qip) (Bool.and (Nat.beq
    a.qin b.qin) (Nat.beq a.err b.err))))))))))

theorem treeNodeCValid_of_payloadBeq {gs : List DyadicSu2Gate} {a b : TreeNodeC}
    (ha : TreeNodeCValid gs a) (heq : treeNodeCPayloadBeq a b = true) :
    TreeNodeCValid gs b := by
  cases a; cases b
  simp only [treeNodeCPayloadBeq, Bool.and_eq_true, Nat.beq_eq] at heq
  rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ha

set_option exponentiation.threshold 256
end ConfigSec3A_TwoAngleTree768

end ConfigTwoAngleBiGqspVerifierBridge

end TwoAngleBiGqspVerifierBridge
end
set_option exponentiation.threshold 256
end TwoAngleBiGqspVerifierBridge_aux_p1

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
