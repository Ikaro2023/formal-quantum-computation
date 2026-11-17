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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PipelinedFuseCertDefs
/-!
# Pure-Integer Certificate Checkers & Soundness for `TensorConveyor` (`(ℂ^N)^{⊗ d}`)

Self-contained, QHL-free real-analytic and fixed-point integer certificate infrastructure for
parameterized `d`-register synchronous unitary tensor-product conveyors (`d ≥ 2`) across `m =
2^e`
parallel oracle slots, importing only `PipelinedFuseCertDefs` and Mathlib inverse/bound
trigonometric lemmas.

Builds on and generalizes the `d = 2` Schur-Weyl symmetric-pair conveyor and multi-slot coupon
structural simplifications specific to pure tensor powers `(ℂ^(2^n))^{⊗ d}`:
- Every weight pair `(2w, 2w + 1)` (`w = 0.. d - 1`) rotates by the identical primary Grover
  angle `θ₁ = 2 arcsin(√(r / 2^n))`, so `tcCheckSched` certifies each `2d`-dimensional
  schedule
  once globally (`r`-independent across all `1 ≤ r ≤ 1024`, `n ≥ 700`) at `10^100` amplitude
  precision (`180` internal angle halvings, zero external trig witness fields) and projects
  hit-weight lower bounds to `tcScale = 10^12`.
- WHNF-forced `List`-memoized `m = 2^e` convolution (`tcCheckConvPow2`) and monotone-in-`r`
  one-pass coupon-occupancy bucket certification (`tcCheckCouponBucket`) at `10^12` scale,
  with
  `+1` ulp (`10⁻¹²`) absorbing the finite-`N` basis shift `2 m d √(2r / 2^n)`.
- Exact `O(sMax)` Abel-summed Bellman stage checker (`tcCheckStageStep`) at `10⁻¹⁶ * √(2^n)`
scale
  splicing onto Cold-entry stage potentials (`PipelinedFuseWarmR1`, `PipelinedFuse`,
  `Stage1Lock`, and `Irrep22`).
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.TensorConveyorCert
open Real
open QuantumComputation.Specs.GroverFindAll.PipeFuseCert
/-! ## 1. WHNF-Forcing Combinators & `10^100` / `10^12` Interval Arithmetic (`TcIv`) -/
/-- WHNF-forcing integer wrapper preventing call-by-name thunk duplication in `decide
  +kernel`. -/
def tcWithForcedInt {α : Type*} (x : ℤ) (k : ℤ → α) : α :=
  Int.casesOn x
    (fun n ↦ Nat.casesOn n (k 0) (fun m ↦ k (Int.ofNat (Nat.succ m))))
    (fun n ↦ Nat.casesOn n (k (Int.negSucc 0)) (fun m ↦ k (Int.negSucc (Nat.succ m))))
theorem tcWithForcedInt_eq {α : Type*} (x : ℤ) (k : ℤ → α) : tcWithForcedInt x k = k x := by
  cases x with
  | ofNat n => cases n <;> rfl
  | negSucc n => cases n <;> rfl
/-- Fixed-point scale `10^12` for weight, `m`-fold convolution, and coupon-tail lower
  bounds. -/
def tcScale : ℤ := 1000000000000
/-- Primitive `Int.ofNat` alias of `tcScale` avoiding `OfNat` projection in `decide
  +kernel`. -/
def tcScalePrim : ℤ := Int.ofNat 1000000000000
theorem tcScalePrim_eq : tcScalePrim = tcScale := rfl
/-- Fixed-point scale `10^100` for internal `2d` intervals (primitive `Nat.pow`). -/
def tcAmpScale : ℤ := Int.ofNat (Nat.pow 10 100)
/-- Scale ratio `10^88 = tcAmpScale / tcScale` projecting squared amplitude bounds to
  `10^12`. -/
def tcAmpToProbDiv : ℤ := Int.ofNat (Nat.pow 10 88)
theorem tcAmpScale_pos : (0 : ℤ) < tcAmpScale := by
  change ((0 : ℕ) : ℤ) < ((10 ^ 100 : ℕ) : ℤ); exact Nat.cast_lt.2 (Nat.pow_pos (by omega))
theorem tcAmpScale_pos_real : (0 : ℝ) < (tcAmpScale : ℝ) :=
  Int.cast_pos.2 tcAmpScale_pos
theorem tcScale_pos : (0 : ℤ) < tcScale := by
  unfold tcScale; omega
theorem tcScale_pos_real : (0 : ℝ) < (tcScale : ℝ) :=
  Int.cast_pos.2 tcScale_pos
theorem tcAmpScale_eq_mul : tcAmpScale = tcScale * tcAmpToProbDiv := by
  have h12 : tcScale = ((10 ^ 12 : ℕ) : ℤ) := (by unfold tcScale; norm_num)
  rw [h12]; change ((10 ^ 100 : ℕ) : ℤ) = ((10 ^ 12 : ℕ) : ℤ) * ((10 ^ 88 : ℕ) : ℤ)
  rw [← Nat.cast_mul, ← pow_add]
theorem tcInt_add_eq (x y : ℤ) : Int.add x y = x + y := rfl
theorem tcInt_sub_eq (x y : ℤ) : Int.sub x y = x - y := rfl
theorem tcInt_mul_eq (x y : ℤ) : Int.mul x y = x * y := rfl
theorem tcInt_ediv_eq (x y : ℤ) : Int.ediv x y = x / y := rfl
theorem tcInt_neg_eq (x : ℤ) : Int.neg x = -x := rfl
theorem tcInt_ofNat_eq (n : ℕ) : Int.ofNat n = (n : ℤ) := rfl
/-- Constructor-level `≤` on `ℤ` avoiding Mathlib `LinearOrder Int` in `decide +kernel`. -/
def bleZ : ℤ → ℤ → Bool
  | Int.ofNat m, Int.ofNat n => Nat.ble m n
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc _, Int.ofNat _ => true
  | Int.negSucc m, Int.negSucc n => Nat.ble n m
theorem bleZ_eq_true_iff (a b : ℤ) : bleZ a b = true ↔ a ≤ b := by
  cases a with
  | ofNat m =>
      cases b with
      | ofNat n => simp only [bleZ, Nat.ble_eq, Int.ofNat_eq_natCast]; omega
      | negSucc n =>
          simp only [bleZ, Bool.false_eq_true, false_iff, Int.ofNat_eq_natCast, Int.negSucc_eq]
          omega
  | negSucc m =>
      cases b with
      | ofNat n => simp only [bleZ, true_iff, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      | negSucc n => simp only [bleZ, Nat.ble_eq, Int.negSucc_eq]; omega
/-- Constructor-level `<` on `ℤ` avoiding Mathlib `LinearOrder Int` in `decide +kernel`. -/
def bltZ (a b : ℤ) : Bool := bleZ (Int.add a (Int.ofNat 1)) b
theorem bltZ_eq_true_iff (a b : ℤ) : bltZ a b = true ↔ a < b := by
  unfold bltZ; rw [bleZ_eq_true_iff, tcInt_add_eq, tcInt_ofNat_eq]; omega
/-- Constructor-level `==` on `ℤ` avoiding Mathlib `DecidableEq` overhead in `decide
  +kernel`. -/
def beqZ (a b : ℤ) : Bool := bleZ a b && bleZ b a
theorem beqZ_eq_true_iff (a b : ℤ) : beqZ a b = true ↔ a = b := by
  unfold beqZ; rw [Bool.and_eq_true, bleZ_eq_true_iff, bleZ_eq_true_iff]; omega
/-- Constructor-level `min` on `ℤ` avoiding Mathlib `Lattice Int` in `decide +kernel`. -/
def minZ (a b : ℤ) : ℤ := cond (bleZ a b) a b
theorem minZ_eq (a b : ℤ) : minZ a b = min a b := by
  unfold minZ
  cases h : bleZ a b <;> simp only [Bool.cond_true, Bool.cond_false]
  · have hle : ¬ a ≤ b := mt (bleZ_eq_true_iff a b).2 (by simp [h])
    exact (min_eq_right (le_of_not_ge hle)).symm
  · exact (min_eq_left ((bleZ_eq_true_iff a b).1 h)).symm
/-- Constructor-level `max` on `ℤ` avoiding Mathlib `Lattice Int` in `decide +kernel`. -/
def maxZ (a b : ℤ) : ℤ := cond (bleZ a b) b a
theorem maxZ_eq (a b : ℤ) : maxZ a b = max a b := by
  unfold maxZ
  cases h : bleZ a b <;> simp only [Bool.cond_true, Bool.cond_false]
  · have hle : ¬ a ≤ b := mt (bleZ_eq_true_iff a b).2 (by simp [h])
    exact (max_eq_left (le_of_not_ge hle)).symm
  · exact (max_eq_right ((bleZ_eq_true_iff a b).1 h)).symm
/-- Closed integer interval `(lo, hi)` representing `[lo / tcAmpScale, hi / tcAmpScale]`. -/
abbrev TcIv : Type := ℤ × ℤ
/-- WHNF-forcing wrapper for a single `TcIv` interval pair. -/
def tcWithForcedIv {α : Type*} (iv : TcIv) (k : TcIv → α) : α :=
  tcWithForcedInt iv.1 fun a ↦ tcWithForcedInt iv.2 fun b ↦ k (a, b)
theorem tcWithForcedIv_eq {α : Type*} (iv : TcIv) (k : TcIv → α) : tcWithForcedIv iv k = k iv := by
  unfold tcWithForcedIv; rw [tcWithForcedInt_eq, tcWithForcedInt_eq]
/-- Tail-recursive accumulator forcing every `(lo, hi)` pair of `l` onto `acc` in reverse. -/
def tcForceIvListRev : List TcIv → List TcIv → List TcIv
  | [], acc => acc
  | iv :: rest, acc => tcWithForcedIv iv fun iv' ↦ tcForceIvListRev rest (iv' :: acc)
theorem tcForceIvListRev_eq (l acc : List TcIv) : tcForceIvListRev l acc = l.reverseAux acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons iv rest ih => unfold tcForceIvListRev List.reverseAux; rw [tcWithForcedIv_eq, ih]
/-- WHNF-forcing wrapper evaluating every `(lo, hi)` element of a `List TcIv`. -/
def tcWithForcedIvList {α : Type*} (l : List TcIv) (k : List TcIv → α) : α :=
  match tcForceIvListRev (tcForceIvListRev l []) [] with
  | [] => k []
  | iv :: rest => k (iv :: rest)
theorem tcWithForcedIvList_eq {α : Type*} (l : List TcIv) (k : List TcIv → α) :
    tcWithForcedIvList l k = k l := by
  unfold tcWithForcedIvList; rw [tcForceIvListRev_eq, tcForceIvListRev_eq]
  change (match l.reverse.reverse with | [] => k [] | iv :: rest => k (iv :: rest)) = k l
  rw [List.reverse_reverse]
  cases l <;> rfl
/-- Tail-recursive accumulator forcing every integer element of `l` onto `acc` in reverse. -/
def tcForceZListRev : List ℤ → List ℤ → List ℤ
  | [], acc => acc
  | x :: rest, acc => tcWithForcedInt x fun x' ↦ tcForceZListRev rest (x' :: acc)
theorem tcForceZListRev_eq (l acc : List ℤ) : tcForceZListRev l acc = l.reverseAux acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x rest ih => unfold tcForceZListRev List.reverseAux; rw [tcWithForcedInt_eq, ih]
/-- WHNF-forcing wrapper evaluating every integer element of a `List ℤ`. -/
def tcWithForcedZList {α : Type*} (l : List ℤ) (k : List ℤ → α) : α :=
  match tcForceZListRev (tcForceZListRev l []) [] with
  | [] => k []
  | x :: rest => k (x :: rest)
theorem tcWithForcedZList_eq {α : Type*} (l : List ℤ) (k : List ℤ → α) :
    tcWithForcedZList l k = k l := by
  unfold tcWithForcedZList; rw [tcForceZListRev_eq, tcForceZListRev_eq]
  change (match l.reverse.reverse with | [] => k [] | x :: rest => k (x :: rest)) = k l
  rw [List.reverse_reverse]
  cases l <;> rfl
/-- Membership of `x: ℝ` in `[iv.1 / 10^100, iv.2 / 10^100]`. -/
def tcMemAmpIv (x : ℝ) (iv : TcIv) : Prop :=
  (iv.1 : ℝ) / (tcAmpScale : ℝ) ≤ x ∧ x ≤ (iv.2 : ℝ) / (tcAmpScale : ℝ)
/-- Certified interval addition at `10^100` scale. -/
def tcIvAdd (a b : TcIv) : TcIv :=
  (Int.add a.1 b.1, Int.add a.2 b.2)
/-- Certified interval subtraction at `10^100` scale. -/
def tcIvSub (a b : TcIv) : TcIv :=
  (Int.sub a.1 b.2, Int.sub a.2 b.1)
/-- Certified interval multiplication at `10^100` scale with WHNF-forced endpoints. -/
def tcIvMul (a b : TcIv) : TcIv :=
  tcWithForcedInt tcAmpScale fun ampS ↦
    tcWithForcedInt (Int.mul a.1 b.1) fun p1 ↦
      tcWithForcedInt (Int.mul a.1 b.2) fun p2 ↦
        tcWithForcedInt (Int.mul a.2 b.1) fun p3 ↦
          tcWithForcedInt (Int.mul a.2 b.2) fun p4 ↦
            tcWithForcedInt (minZ (minZ p1 p2) (minZ p3 p4)) fun lo ↦
              tcWithForcedInt (maxZ (maxZ p1 p2) (maxZ p3 p4)) fun hi ↦
                (Int.ediv lo ampS, Int.neg (Int.ediv (Int.neg hi) ampS))
/-- Certified interval squaring at `10^100` scale exploiting `0 ≤ x^2`. -/
def tcIvSq (a : TcIv) : TcIv :=
  tcWithForcedInt tcAmpScale fun ampS ↦
    if bleZ (Int.ofNat 0) a.1 then
      (Int.ediv (Int.mul a.1 a.1) ampS,
        Int.neg (Int.ediv (Int.neg (Int.mul a.2 a.2)) ampS))
    else if bleZ a.2 (Int.ofNat 0) then
      (Int.ediv (Int.mul a.2 a.2) ampS,
        Int.neg (Int.ediv (Int.neg (Int.mul a.1 a.1)) ampS))
    else
      tcWithForcedInt (maxZ (Int.neg a.1) a.2) fun m ↦
        (Int.ofNat 0, Int.neg (Int.ediv (Int.neg (Int.mul m m)) ampS))
theorem tc_ediv_pos_le_real (x d : ℤ) (hd : 0 < d) : ((x / d : ℤ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  have hd_r : (0 : ℝ) < (d : ℝ) := Int.cast_pos.2 hd; rw [le_div_iff₀ hd_r]
  exact_mod_cast Int.ediv_mul_le x hd.ne'
theorem tc_real_le_neg_ediv_neg_pos (x d : ℤ) (hd : 0 < d) :
    (x : ℝ) / (d : ℝ) ≤ ((-((-x) / d) : ℤ) : ℝ) := by
  have hd_r : (0 : ℝ) < (d : ℝ) := Int.cast_pos.2 hd; rw [div_le_iff₀ hd_r]
  have h1 : ((-x) / d) * d ≤ -x := Int.ediv_mul_le (-x) hd.ne'
  have h2 : x ≤ -((-x) / d) * d := by
    have hneg : -((-x) / d) * d = -(((-x) / d) * d) := neg_mul _ _; linarith
  exact_mod_cast h2
theorem tcMemAmpIv_ratDiv (num den : ℤ) (hden : 0 < den) : tcMemAmpIv ((num : ℝ) / (den : ℝ))
    ((num * tcAmpScale) / den, -((-(num * tcAmpScale)) / den)) := by
  have hS : (0 : ℝ) < (tcAmpScale : ℝ) := tcAmpScale_pos_real
  have hd_ne : (den : ℝ) ≠ 0 := (Int.cast_pos.2 hden).ne'
  have hmul_eq : ((num * tcAmpScale : ℤ) : ℝ) / (den : ℝ) / (tcAmpScale : ℝ) =
      (num : ℝ) / (den : ℝ) := by
    push_cast; field_simp [hd_ne, hS.ne']
  have hlo := div_le_div_of_nonneg_right (tc_ediv_pos_le_real (num * tcAmpScale) den hden) hS.le
  have hhi := div_le_div_of_nonneg_right
    (tc_real_le_neg_ediv_neg_pos (num * tcAmpScale) den hden) hS.le
  rw [hmul_eq] at hlo hhi; exact ⟨hlo, hhi⟩
theorem tcMemAmpIv_add {x y : ℝ} {a b : TcIv} (hx : tcMemAmpIv x a) (hy : tcMemAmpIv y b) :
    tcMemAmpIv (x + y) (tcIvAdd a b) := by
  rcases hx with ⟨hx1, hx2⟩; rcases hy with ⟨hy1, hy2⟩
  unfold tcMemAmpIv tcIvAdd; simp only [tcInt_add_eq]; push_cast; rw [add_div, add_div]
  exact ⟨by linarith, by linarith⟩
theorem tcMemAmpIv_sub {x y : ℝ} {a b : TcIv} (hx : tcMemAmpIv x a) (hy : tcMemAmpIv y b) :
    tcMemAmpIv (x - y) (tcIvSub a b) := by
  rcases hx with ⟨hx1, hx2⟩; rcases hy with ⟨hy1, hy2⟩
  unfold tcMemAmpIv tcIvSub; simp only [tcInt_sub_eq]; push_cast; rw [sub_div, sub_div]
  exact ⟨by linarith, by linarith⟩
theorem tcMemAmpIv_mul {x y : ℝ} {a b : TcIv} (hx : tcMemAmpIv x a) (hy : tcMemAmpIv y b) :
    tcMemAmpIv (x * y) (tcIvMul a b) := by
  have hS_pos : (0 : ℤ) < tcAmpScale := tcAmpScale_pos
  have hS : (0 : ℝ) < (tcAmpScale : ℝ) := tcAmpScale_pos_real; unfold tcIvMul
  simp only [tcWithForcedInt_eq, tcInt_mul_eq, tcInt_ediv_eq, tcInt_neg_eq, minZ_eq, maxZ_eq]
  unfold tcMemAmpIv at hx hy ⊢; dsimp only
  set X : ℝ := x * (tcAmpScale : ℝ); set Y : ℝ := y * (tcAmpScale : ℝ)
  have hX1 : (a.1 : ℝ) ≤ X := (div_le_iff₀ hS).1 hx.1
  have hX2 : X ≤ (a.2 : ℝ) := (le_div_iff₀ hS).1 hx.2
  have hY1 : (b.1 : ℝ) ≤ Y := (div_le_iff₀ hS).1 hy.1
  have hY2 : Y ≤ (b.2 : ℝ) := (le_div_iff₀ hS).1 hy.2
  set loZ : ℤ := min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2))
  set hiZ : ℤ := max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2))
  have hlo11 : (loZ : ℝ) ≤ (a.1 : ℝ) * (b.1 : ℝ) := by
    exact_mod_cast (min_le_left _ _).trans (min_le_left _ _)
  have hlo12 : (loZ : ℝ) ≤ (a.1 : ℝ) * (b.2 : ℝ) := by
    exact_mod_cast (min_le_left _ _).trans (min_le_right _ _)
  have hlo21 : (loZ : ℝ) ≤ (a.2 : ℝ) * (b.1 : ℝ) := by
    exact_mod_cast (min_le_right _ _).trans (min_le_left _ _)
  have hlo22 : (loZ : ℝ) ≤ (a.2 : ℝ) * (b.2 : ℝ) := by
    exact_mod_cast (min_le_right _ _).trans (min_le_right _ _)
  have hhi11 : (a.1 : ℝ) * (b.1 : ℝ) ≤ (hiZ : ℝ) := by
    exact_mod_cast (le_max_left _ _).trans (le_max_left _ _)
  have hhi12 : (a.1 : ℝ) * (b.2 : ℝ) ≤ (hiZ : ℝ) := by
    exact_mod_cast (le_max_right _ _).trans (le_max_left _ _)
  have hhi21 : (a.2 : ℝ) * (b.1 : ℝ) ≤ (hiZ : ℝ) := by
    exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
  have hhi22 : (a.2 : ℝ) * (b.2 : ℝ) ≤ (hiZ : ℝ) := by
    exact_mod_cast (le_max_right _ _).trans (le_max_right _ _)
  have hXY_lo : (loZ : ℝ) ≤ X * Y := by
    rcases le_or_gt 0 X with hX | hX
    · rcases le_or_gt 0 (b.1 : ℝ) with hb1 | hb1 <;> nlinarith
    · rcases le_or_gt 0 (b.2 : ℝ) with hb2 | hb2 <;> nlinarith
  have hXY_hi : X * Y ≤ (hiZ : ℝ) := by
    rcases le_or_gt 0 X with hX | hX
    · rcases le_or_gt 0 (b.2 : ℝ) with hb2 | hb2 <;> nlinarith
    · rcases le_or_gt 0 (b.1 : ℝ) with hb1 | hb1 <;> nlinarith
  have hXY_eq : X * Y / (tcAmpScale : ℝ) / (tcAmpScale : ℝ) = x * y := by
    dsimp [X, Y]; field_simp [hS.ne']
  constructor
  · have hd := tc_ediv_pos_le_real loZ tcAmpScale hS_pos
    have hd2 :=
      div_le_div_of_nonneg_right (hd.trans (div_le_div_of_nonneg_right hXY_lo hS.le)) hS.le
    linarith [hd2, hXY_eq]
  · have hd := tc_real_le_neg_ediv_neg_pos hiZ tcAmpScale hS_pos
    have hd1 : X * Y / (tcAmpScale : ℝ) ≤ ((-((-hiZ) / tcAmpScale) : ℤ) : ℝ) :=
      (div_le_div_of_nonneg_right hXY_hi hS.le).trans hd
    have hd2 := div_le_div_of_nonneg_right hd1 hS.le; linarith [hd2, hXY_eq]
theorem tcMemAmpIv_sq {x : ℝ} {a : TcIv} (hx : tcMemAmpIv x a) : tcMemAmpIv (x ^ 2) (tcIvSq a) := by
  have hS_pos : (0 : ℤ) < tcAmpScale := tcAmpScale_pos
  have hS : (0 : ℝ) < (tcAmpScale : ℝ) := tcAmpScale_pos_real; unfold tcMemAmpIv at hx ⊢
  set X : ℝ := x * (tcAmpScale : ℝ); have hX1 : (a.1 : ℝ) ≤ X := (div_le_iff₀ hS).1 hx.1
  have hX2 : X ≤ (a.2 : ℝ) := (le_div_iff₀ hS).1 hx.2
  have hX_eq : X ^ 2 / (tcAmpScale : ℝ) / (tcAmpScale : ℝ) = x ^ 2 := by
    dsimp [X]; field_simp [hS.ne']
  unfold tcIvSq
  simp only [tcWithForcedInt_eq, bleZ_eq_true_iff, tcInt_ofNat_eq, Nat.cast_zero,
    tcInt_mul_eq, tcInt_ediv_eq, tcInt_neg_eq, maxZ_eq]
  by_cases ha1 : 0 ≤ a.1
  · simp only [ha1, ↓reduceIte]; have ha1_r : (0 : ℝ) ≤ (a.1 : ℝ) := (by exact_mod_cast ha1)
    have hlo_sq : ((a.1 * a.1 : ℤ) : ℝ) ≤ X ^ 2 := (by push_cast; nlinarith)
    have hhi_sq : X ^ 2 ≤ ((a.2 * a.2 : ℤ) : ℝ) := (by push_cast; nlinarith); constructor
    · have hd := tc_ediv_pos_le_real (a.1 * a.1) tcAmpScale hS_pos
      have hd2 := div_le_div_of_nonneg_right
        (hd.trans (div_le_div_of_nonneg_right hlo_sq hS.le)) hS.le
      linarith [hd2, hX_eq]
    · have hd := tc_real_le_neg_ediv_neg_pos (a.2 * a.2) tcAmpScale hS_pos
      have hd2 := div_le_div_of_nonneg_right
        ((div_le_div_of_nonneg_right hhi_sq hS.le).trans hd) hS.le
      linarith [hd2, hX_eq]
  · simp only [ha1, ↓reduceIte]; by_cases ha2 : a.2 ≤ 0
    · simp only [ha2, ↓reduceIte]; have ha2_r : (a.2 : ℝ) ≤ 0 := (by exact_mod_cast ha2)
      have hlo_sq : ((a.2 * a.2 : ℤ) : ℝ) ≤ X ^ 2 := (by push_cast; nlinarith)
      have hhi_sq : X ^ 2 ≤ ((a.1 * a.1 : ℤ) : ℝ) := (by push_cast; nlinarith); constructor
      · have hd := tc_ediv_pos_le_real (a.2 * a.2) tcAmpScale hS_pos
        have hd2 := div_le_div_of_nonneg_right
          (hd.trans (div_le_div_of_nonneg_right hlo_sq hS.le)) hS.le
        linarith [hd2, hX_eq]
      · have hd := tc_real_le_neg_ediv_neg_pos (a.1 * a.1) tcAmpScale hS_pos
        have hd2 := div_le_div_of_nonneg_right
          ((div_le_div_of_nonneg_right hhi_sq hS.le).trans hd) hS.le
        linarith [hd2, hX_eq]
    · simp only [ha2, ↓reduceIte]; set m : ℤ := max (-a.1) a.2
      have hm1 : -(m : ℝ) ≤ (a.1 : ℝ) := by
        have h : -a.1 ≤ m := le_max_left (-a.1) a.2
        have hr : (-(a.1 : ℝ)) ≤ (m : ℝ) := (by exact_mod_cast h); linarith
      have hm2 : (a.2 : ℝ) ≤ (m : ℝ) := (by exact_mod_cast le_max_right (-a.1) a.2)
      have hhi_sq : X ^ 2 ≤ ((m * m : ℤ) : ℝ) := (by push_cast; nlinarith); constructor
      · rw [Int.cast_zero, zero_div]; exact sq_nonneg x
      · have hd := tc_real_le_neg_ediv_neg_pos (m * m) tcAmpScale hS_pos
        have hd2 := div_le_div_of_nonneg_right
          ((div_le_div_of_nonneg_right hhi_sq hS.le).trans hd) hS.le
        linarith [hd2, hX_eq]
/-!
 ## 2. Stereographic Intertwiner Cos/Sin, Primary Grover Angle, & `180`-Halving Trig Generator
-/
/-- Rational Pythagorean cosine `(1 - u^2) / (1 + u^2)`. -/
def tcRatCos (u : ℚ) : ℚ :=
  (1 - u ^ 2) / (1 + u ^ 2)
/-- Rational Pythagorean sine `2u / (1 + u^2)`. -/
def tcRatSin (u : ℚ) : ℚ :=
  (2 * u) / (1 + u ^ 2)
theorem tcRatCos_sq_add_sin_sq (u : ℚ) : (tcRatCos u) ^ 2 + (tcRatSin u) ^ 2 = 1 := by
  unfold tcRatCos tcRatSin; have hpos : (0 : ℚ) < 1 + u ^ 2 := (by positivity)
  field_simp [hpos.ne']; ring
theorem tcRatCos_sq_add_sin_sq_real (u : ℚ) : (tcRatCos u : ℝ) ^ 2 + (tcRatSin u : ℝ) ^ 2 = 1 := by
  exact_mod_cast tcRatCos_sq_add_sin_sq u
theorem tcRatCos_ratDiv_eq (uNum uDen : ℤ) (hd : uDen ≠ 0) : (tcRatCos ((uNum : ℚ) / (uDen : ℚ)) :
    ℝ) = ((uDen * uDen - uNum * uNum : ℤ) : ℝ) / ((uDen * uDen + uNum * uNum : ℤ) : ℝ) := by
  have hq : tcRatCos ((uNum : ℚ) / (uDen : ℚ)) =
      ((uDen * uDen - uNum * uNum : ℤ) : ℚ) / ((uDen * uDen + uNum * uNum : ℤ) : ℚ) := by
    unfold tcRatCos; have hd_q : (uDen : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
    have hden_pos : (0 : ℚ) < (uDen : ℚ) ^ 2 + (uNum : ℚ) ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd_q) (sq_nonneg _)
    have h1 : 1 + ((uNum : ℚ) / (uDen : ℚ)) ^ 2 ≠ 0 := (by positivity)
    push_cast; field_simp [hd_q, h1, hden_pos.ne']
  exact_mod_cast hq
theorem tcRatSin_ratDiv_eq (uNum uDen : ℤ) (hd : uDen ≠ 0) : (tcRatSin ((uNum : ℚ) / (uDen : ℚ)) :
    ℝ) = ((2 * uNum * uDen : ℤ) : ℝ) / ((uDen * uDen + uNum * uNum : ℤ) : ℝ) := by
  have hq : tcRatSin ((uNum : ℚ) / (uDen : ℚ)) =
      ((2 * uNum * uDen : ℤ) : ℚ) / ((uDen * uDen + uNum * uNum : ℤ) : ℚ) := by
    unfold tcRatSin; have hd_q : (uDen : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
    have hden_pos : (0 : ℚ) < (uDen : ℚ) ^ 2 + (uNum : ℚ) ^ 2 :=
      add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd_q) (sq_nonneg _)
    have h1 : 1 + ((uNum : ℚ) / (uDen : ℚ)) ^ 2 ≠ 0 := (by positivity)
    push_cast; field_simp [hd_q, h1, hden_pos.ne']
  exact_mod_cast hq
theorem tcMemAmpIv_pythag_ratDiv (vNum vDen : ℤ) (hd : vDen ≠ 0) :
    let den := vDen * vDen + vNum * vNum; let cNum := vDen * vDen - vNum * vNum
    let sNum := 2 * vNum * vDen
    tcMemAmpIv (tcRatCos ((vNum : ℚ) / (vDen : ℚ)) : ℝ) ((cNum * tcAmpScale) / den, -((-(cNum *
      tcAmpScale)) / den)) ∧ tcMemAmpIv (tcRatSin ((vNum : ℚ) / (vDen : ℚ)) : ℝ) ((sNum *
      tcAmpScale) / den, -((-(sNum * tcAmpScale)) / den)) := by
  intro den cNum sNum
  have hden_pos : 0 < den := by
    dsimp [den]; have h1 : 0 < vDen * vDen := mul_self_pos.mpr hd
    have h2 : 0 ≤ vNum * vNum := mul_self_nonneg vNum; omega
  constructor
  · rw [tcRatCos_ratDiv_eq vNum vDen hd]; exact tcMemAmpIv_ratDiv cNum den hden_pos
  · rw [tcRatSin_ratDiv_eq vNum vDen hd]; exact tcMemAmpIv_ratDiv sNum den hden_pos
/-- Exact cosine `cos θ₁ = 1 - 2r / N` of the primary Grover step angle. -/
noncomputable def tcC1Real (N r : ℕ) : ℝ :=
  1 - 2 * (r : ℝ) / (N : ℝ)
/-- Exact sine `sin θ₁ = 2√(r(N - r)) / N` of the primary Grover step angle. -/
noncomputable def tcS1Real (N r : ℕ) : ℝ :=
  2 * √((r : ℝ) * ((N : ℝ) - (r : ℝ))) / (N : ℝ)
/-- Exact primary Grover step angle `θ₁ = 2 arcsin(√r / √N)`. -/
noncomputable def tcTheta1Real (N r : ℕ) : ℝ :=
  2 * Real.arcsin (√(r : ℝ) / √(N : ℝ))
theorem tcC1Real_sq_add_s1Real_sq {N r : ℕ} (hr1 : 1 ≤ r) (hrN : r < N) :
    tcC1Real N r ^ 2 + tcS1Real N r ^ 2 = 1 ∧ 0 < tcS1Real N r := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := (by have : 1 ≤ N := (by omega); positivity)
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by positivity)
  have hNr_pos : (0 : ℝ) < (N : ℝ) - (r : ℝ) := by
    have : (r : ℝ) < (N : ℝ) := (by exact_mod_cast hrN); linarith
  have hprod_pos : (0 : ℝ) < (r : ℝ) * ((N : ℝ) - (r : ℝ)) := mul_pos hr_pos hNr_pos; constructor
  · unfold tcC1Real tcS1Real
    have hsq : √((r : ℝ) * ((N : ℝ) - (r : ℝ))) ^ 2 = (r : ℝ) * ((N : ℝ) - (r : ℝ)) :=
      Real.sq_sqrt hprod_pos.le
    have hN_ne : (N : ℝ) ≠ 0 := hN_pos.ne'; field_simp [hN_ne]; linear_combination 4 * hsq
  · unfold tcS1Real; positivity
theorem cos_sin_tcTheta1Real {N r : ℕ} (hr1 : 1 ≤ r) (hrN : r < N) : Real.cos (tcTheta1Real N r) =
    tcC1Real N r ∧ Real.sin (tcTheta1Real N r) = tcS1Real N r := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := (by have : 1 ≤ N := (by omega); positivity)
  have hr_pos : (0 : ℝ) ≤ (r : ℝ) := (by positivity); set x : ℝ := √(r : ℝ) / √(N : ℝ)
  have hx0 : 0 ≤ x := (by positivity)
  have hx1 : x ≤ 1 := (div_le_one (Real.sqrt_pos.mpr hN_pos)).mpr
    (Real.sqrt_le_sqrt (by exact_mod_cast hrN.le))
  have hsin : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) hx1
  have hx_sq : x ^ 2 = (r : ℝ) / (N : ℝ) := by
    dsimp [x]; rw [div_pow, Real.sq_sqrt hr_pos, Real.sq_sqrt hN_pos.le]
  have hcos_eq : Real.cos (tcTheta1Real N r) = tcC1Real N r := by
    unfold tcTheta1Real tcC1Real
    have hcos2 : Real.cos (2 * Real.arcsin x) = 1 - 2 * Real.sin (Real.arcsin x) ^ 2 := by
      linear_combination Real.cos_two_mul' (Real.arcsin x) + Real.cos_sq_add_sin_sq (Real.arcsin x)
    rw [hcos2, hsin, hx_sq]; ring
  refine ⟨hcos_eq, ?_⟩
  rcases tcC1Real_sq_add_s1Real_sq hr1 hrN with ⟨hcs1, hs1_pos⟩; rw [← hcos_eq] at hcs1
  have hsq : Real.sin (tcTheta1Real N r) ^ 2 = tcS1Real N r ^ 2 := by
    linear_combination Real.cos_sq_add_sin_sq (tcTheta1Real N r) - hcs1
  have hθ_nonneg : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx0
  have hθ_le : Real.arcsin x ≤ π / 2 := Real.arcsin_le_pi_div_two x
  have hsin_nonneg : 0 ≤ Real.sin (tcTheta1Real N r) := by
    unfold tcTheta1Real; exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [← Real.sqrt_sq hsin_nonneg, ← Real.sqrt_sq hs1_pos.le, hsq]
/-- Grover block length per `TensorConveyor` segment targeting angle `tauNum / tauDen`. -/
noncomputable def tcKBlk (n r tauNum tauDen : ℕ) : ℕ :=
  let α := Real.arcsin (1 / √((2 ^ n : ℝ) / (r : ℝ)))
  (round (((tauNum : ℝ) / (tauDen : ℝ)) / (2 * α))).toNat + 1
/-- Double-angle `10^100`-scale interval step `(c, s) ↦ (c^2 - s^2, 2 c s)`. -/
def tcDoubleCosSinIv (cs : TcIv × TcIv) : TcIv × TcIv :=
  tcWithForcedIv (tcIvSub (tcIvSq cs.1) (tcIvSq cs.2)) fun cNext ↦
    tcWithForcedIv (tcIvMul cs.2 cs.1) fun sc ↦
      tcWithForcedIv (Int.mul (Int.ofNat 2) sc.1, Int.mul (Int.ofNat 2) sc.2) fun sNext ↦
        (cNext, sNext)
theorem tcDoubleCosSinIv_sound {θ : ℝ} {cs : TcIv × TcIv} (hc : tcMemAmpIv (Real.cos θ) cs.1) (hs :
    tcMemAmpIv (Real.sin θ) cs.2) : tcMemAmpIv (Real.cos (2 * θ)) (tcDoubleCosSinIv cs).1 ∧
    tcMemAmpIv (Real.sin (2 * θ)) (tcDoubleCosSinIv cs).2 := by
  unfold tcDoubleCosSinIv
  simp only [tcWithForcedIv_eq, tcInt_mul_eq, tcInt_ofNat_eq, Nat.cast_ofNat]; constructor
  · rw [Real.cos_two_mul']; exact tcMemAmpIv_sub (tcMemAmpIv_sq hc) (tcMemAmpIv_sq hs)
  · rw [Real.sin_two_mul]; rcases tcMemAmpIv_mul hs hc with ⟨hlo, hhi⟩
    unfold tcMemAmpIv; dsimp only; push_cast; rw [mul_div_assoc, mul_div_assoc]
    exact ⟨by linarith, by linarith⟩
/-- Iterated `k`-fold double-angle `10^100`-scale interval generator. -/
def tcIterDoubleCosSinIv : ℕ → TcIv × TcIv → TcIv × TcIv
  | 0, cs => cs
  | k + 1, cs => tcIterDoubleCosSinIv k (tcDoubleCosSinIv cs)
theorem tcIterDoubleCosSinIv_sound {θ : ℝ} {cs : TcIv × TcIv} (k : ℕ)
    (hc : tcMemAmpIv (Real.cos θ) cs.1) (hs : tcMemAmpIv (Real.sin θ) cs.2) :
    tcMemAmpIv (Real.cos ((2 : ℝ) ^ k * θ)) (tcIterDoubleCosSinIv k cs).1 ∧
    tcMemAmpIv (Real.sin ((2 : ℝ) ^ k * θ)) (tcIterDoubleCosSinIv k cs).2 := by
  induction k generalizing θ cs with
  | zero => unfold tcIterDoubleCosSinIv; rw [pow_zero, one_mul]; exact ⟨hc, hs⟩
  | succ k ih =>
      unfold tcIterDoubleCosSinIv; rcases tcDoubleCosSinIv_sound hc hs with ⟨hc2, hs2⟩
      have hrew : (2 : ℝ) ^ (k + 1) * θ = (2 : ℝ) ^ k * (2 * θ) := (by ring)
      rw [hrew]; exact ih hc2 hs2
/-- Number of angle halvings (`180`, so `2^180 > 1.5 × 10^54`) for `10^100`-scale `(cos,
  sin)`. -/
def tcTrigHalvings : ℕ := 180
/-- Internal `10^100`-scale `(cos φ, sin φ)` interval generator for `φ ∈ [a / d, b / e]`. -/
def tcTrigIv100 (a d b e : ℤ) : TcIv × TcIv :=
  let M : ℤ := Int.ofNat (Nat.pow 2 tcTrigHalvings)
  tcWithForcedInt tcAmpScale fun ampS ↦
    tcWithForcedInt (Int.ediv (Int.mul a ampS) (Int.mul M d)) fun yLo ↦
      tcWithForcedInt (Int.neg (Int.ediv (Int.neg (Int.mul b ampS)) (Int.mul M e))) fun yHi ↦
        tcWithForcedInt
          (Int.sub yLo
            (Int.neg (Int.ediv (Int.neg (Int.mul (Int.mul yLo yLo) yLo))
              (Int.mul (Int.mul (Int.ofNat 6) ampS) ampS))))
          fun sLo0 ↦
          tcWithForcedInt
            (Int.sub ampS
              (Int.neg (Int.ediv (Int.neg (Int.mul yHi yHi))
                (Int.mul (Int.ofNat 2) ampS))))
            fun cLo0 ↦
            tcIterDoubleCosSinIv tcTrigHalvings ((cLo0, ampS), (sLo0, yHi))
theorem tcTrigIv100_sound {a d b e : ℤ} {φ : ℝ} (ha : 0 ≤ a) (hd : 0 < d) (he : 0 < e) (hlo : (a :
    ℝ) / (d : ℝ) ≤ φ) (hhi : φ ≤ (b : ℝ) / (e : ℝ)) (hyHi_le : -((-(b * tcAmpScale)) / (((2 : ℤ) ^
    tcTrigHalvings) * e)) ≤ tcAmpScale) : tcMemAmpIv (Real.cos φ) (tcTrigIv100 a d b e).1 ∧
    tcMemAmpIv (Real.sin φ) (tcTrigIv100 a d b e).2 := by
  unfold tcTrigIv100
  simp only [tcWithForcedInt_eq, tcInt_mul_eq, tcInt_sub_eq,
    tcInt_ediv_eq, tcInt_neg_eq, tcInt_ofNat_eq, Nat.cast_ofNat]
  set M : ℤ := (2 : ℤ) ^ tcTrigHalvings; have hM_pos : (0 : ℤ) < M := (by dsimp [M]; positivity)
  have hM_r : (0 : ℝ) < (M : ℝ) := Int.cast_pos.2 hM_pos
  have hM_eq : (M : ℝ) = (2 : ℝ) ^ tcTrigHalvings := (by dsimp [M]; push_cast; rfl)
  have hS_pos : (0 : ℤ) < tcAmpScale := tcAmpScale_pos
  have hS : (0 : ℝ) < (tcAmpScale : ℝ) := tcAmpScale_pos_real
  have hMd_pos : (0 : ℤ) < M * d := mul_pos hM_pos hd
  have hMe_pos : (0 : ℤ) < M * e := mul_pos hM_pos he; set yLo : ℤ := (a * tcAmpScale) / (M * d)
  set yHi : ℤ := -((-(b * tcAmpScale)) / (M * e))
  set sLo0 : ℤ := yLo - (-((-(yLo * yLo * yLo)) / (6 * tcAmpScale * tcAmpScale)))
  set cLo0 : ℤ := tcAmpScale - (-((-(yHi * yHi)) / (2 * tcAmpScale)))
  set θ₀ : ℝ := φ / ((2 : ℝ) ^ tcTrigHalvings); set xLo : ℝ := (yLo : ℝ) / (tcAmpScale : ℝ)
  set xHi : ℝ := (yHi : ℝ) / (tcAmpScale : ℝ)
  have hyLo_nn : (0 : ℤ) ≤ yLo := Int.ediv_nonneg (mul_nonneg ha hS_pos.le) hMd_pos.le
  have hyLo_r : (0 : ℝ) ≤ (yLo : ℝ) := (by exact_mod_cast hyLo_nn)
  have hxLo_nn : 0 ≤ xLo := div_nonneg hyLo_r hS.le
  have hxHi_le1 : xHi ≤ 1 := (div_le_one hS).2 (by exact_mod_cast hyHi_le)
  have hxLo_le_θ0 : xLo ≤ θ₀ := by
    have h1 := tc_ediv_pos_le_real (a * tcAmpScale) (M * d) hMd_pos; push_cast at h1
    have h2 := div_le_div_of_nonneg_right h1 hS.le
    have h3 : (a : ℝ) * (tcAmpScale : ℝ) / ((M : ℝ) * (d : ℝ)) / (tcAmpScale : ℝ) =
        ((a : ℝ) / (d : ℝ)) / ((2 : ℝ) ^ tcTrigHalvings) := by
      have hd_ne : (d : ℝ) ≠ 0 := (Int.cast_pos.2 hd).ne'; rw [hM_eq]; field_simp [hd_ne, hS.ne']
    have h4 : ((a : ℝ) / (d : ℝ)) / ((2 : ℝ) ^ tcTrigHalvings) ≤ θ₀ :=
      div_le_div_of_nonneg_right hlo (by positivity)
    linarith
  have hθ0_le_xHi : θ₀ ≤ xHi := by
    have h1 : ((b * tcAmpScale : ℤ) : ℝ) / ((M * e : ℤ) : ℝ) ≤ (yHi : ℝ) :=
      tc_real_le_neg_ediv_neg_pos (b * tcAmpScale) (M * e) hMe_pos
    have h2 : ((b * tcAmpScale : ℤ) : ℝ) / ((M * e : ℤ) : ℝ) / (tcAmpScale : ℝ) ≤ xHi :=
      div_le_div_of_nonneg_right h1 hS.le
    have h3 : ((b * tcAmpScale : ℤ) : ℝ) / ((M * e : ℤ) : ℝ) / (tcAmpScale : ℝ) =
        ((b : ℝ) / (e : ℝ)) / ((2 : ℝ) ^ tcTrigHalvings) := by
      have he_ne : (e : ℝ) ≠ 0 := (Int.cast_pos.2 he).ne'; push_cast
      rw [hM_eq]; field_simp [he_ne, hS.ne']
    have h4 : θ₀ ≤ ((b : ℝ) / (e : ℝ)) / ((2 : ℝ) ^ tcTrigHalvings) :=
      div_le_div_of_nonneg_right hhi (by positivity)
    linarith
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hc0 : tcMemAmpIv (Real.cos θ₀) (cLo0, tcAmpScale) := by
    unfold tcMemAmpIv; dsimp only; constructor
    · have hd2 : (0 : ℤ) < 2 * tcAmpScale := (by positivity)
      have hceil := tc_real_le_neg_ediv_neg_pos (yHi * yHi) (2 * tcAmpScale) hd2
      have hcast_c : (cLo0 : ℝ) =
          (tcAmpScale : ℝ) - ((-((-(yHi * yHi)) / (2 * tcAmpScale)) : ℤ) : ℝ) := by
        dsimp [cLo0]; exact Int.cast_sub _ _
      have hsub : (cLo0 : ℝ) ≤
          (tcAmpScale : ℝ) - ((yHi * yHi : ℤ) : ℝ) / ((2 * tcAmpScale : ℤ) : ℝ) := by
        linarith [hceil, hcast_c]
      have hdiv := div_le_div_of_nonneg_right hsub hS.le
      have halg : ((tcAmpScale : ℝ) - ((yHi * yHi : ℤ) : ℝ) / ((2 * tcAmpScale : ℤ) : ℝ)) /
        (tcAmpScale : ℝ) = 1 - xHi ^ 2 / 2 := by
        dsimp [xHi]; push_cast; field_simp [hS.ne']
      have hc_xHi : 1 - xHi ^ 2 / 2 ≤ Real.cos xHi := Real.one_sub_sq_div_two_le_cos
      have hc_mono : Real.cos xHi ≤ Real.cos θ₀ :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hθ0_le_xHi
      linarith
    · rw [div_self hS.ne']; exact Real.cos_le_one θ₀
  have hs0 : tcMemAmpIv (Real.sin θ₀) (sLo0, yHi) := by
    unfold tcMemAmpIv; dsimp only; constructor
    · have hd6 : (0 : ℤ) < 6 * tcAmpScale * tcAmpScale := (by positivity)
      have hceil := tc_real_le_neg_ediv_neg_pos (yLo * yLo * yLo) (6 * tcAmpScale * tcAmpScale) hd6
      have hcast_s : (sLo0 : ℝ) = (yLo : ℝ) -
          ((-((-(yLo * yLo * yLo)) / (6 * tcAmpScale * tcAmpScale)) : ℤ) : ℝ) := by
        dsimp [sLo0]; exact Int.cast_sub _ _
      have hsub : (sLo0 : ℝ) ≤ (yLo : ℝ) -
          ((yLo * yLo * yLo : ℤ) : ℝ) / ((6 * tcAmpScale * tcAmpScale : ℤ) : ℝ) := by
        linarith [hceil, hcast_s]
      have hdiv := div_le_div_of_nonneg_right hsub hS.le
      have halg : ((yLo : ℝ) - ((yLo * yLo * yLo : ℤ) : ℝ) / ((6 * tcAmpScale * tcAmpScale : ℤ) :
        ℝ)) / (tcAmpScale : ℝ) = xLo - xLo ^ 3 / 6 := by
        dsimp [xLo]; push_cast; field_simp [hS.ne']
      have hsin_xLo : xLo - xLo ^ 3 / 6 ≤ Real.sin θ₀ := (Real.sin_ge_sub_cube hxLo_nn).trans
          (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hxLo_le_θ0)
      linarith
    · exact (Real.sin_le (by linarith)).trans hθ0_le_xHi
  have hiter :=
    tcIterDoubleCosSinIv_sound (cs := ((cLo0, tcAmpScale), (sLo0, yHi))) tcTrigHalvings hc0 hs0
  have hmul : (2 : ℝ) ^ tcTrigHalvings * θ₀ = φ := (by dsimp [θ₀]; field_simp); rwa [hmul] at hiter
theorem tcSqrtRatio_ge_of_n700 {n r : ℕ} (hn700 : 700 ≤ n) (hr1 : 1 ≤ r) (hr1024 : r ≤ 1024) :
    ((10 : ℝ) ^ 103) ≤ √((2 ^ n : ℝ) / (r : ℝ)) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by positivity)
  have h10_3 : (10 : ℝ) ^ 3 ≤ (2 : ℝ) ^ 10 := (by norm_num)
  have h10_1 : (10 : ℝ) ^ 1 ≤ (2 : ℝ) ^ 5 := (by norm_num)
  have h103 : (10 : ℝ) ^ 103 ≤ (2 : ℝ) ^ 345 :=
    calc (10 : ℝ) ^ 103
        = ((10 : ℝ) ^ 3) ^ 34 * (10 : ℝ) ^ 1 := by rw [← pow_mul, ← pow_add]
      _ ≤ ((2 : ℝ) ^ 10) ^ 34 * (2 : ℝ) ^ 5 :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) h10_3 34) h10_1
            (by positivity) (by positivity)
      _ = (2 : ℝ) ^ 345 := by rw [← pow_mul, ← pow_add]
  have hpow_r : (2 : ℝ) ^ 700 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn700
  have hc_ge : ((2 : ℝ) ^ 345) ^ 2 ≤ (2 ^ n : ℝ) / (r : ℝ) := by
    rw [le_div_iff₀ hr_pos]
    have hr_le : (r : ℝ) ≤ (2 : ℝ) ^ 10 := by
      have h1024 : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
      have h210 : (1024 : ℝ) = (2 : ℝ) ^ 10 := (by norm_num); linarith
    have hmul : ((2 : ℝ) ^ 345) ^ 2 * (r : ℝ) ≤ ((2 : ℝ) ^ 345) ^ 2 * (2 : ℝ) ^ 10 :=
      mul_le_mul_of_nonneg_left hr_le (by positivity)
    have h700 : ((2 : ℝ) ^ 345) ^ 2 * (2 : ℝ) ^ 10 = (2 : ℝ) ^ 700 := (by rw [← pow_mul, ← pow_add])
    exact hmul.trans (h700.le.trans hpow_r)
  have hsqrt_ge : (2 : ℝ) ^ 345 ≤ √((2 ^ n : ℝ) / (r : ℝ)) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 345)]; exact Real.sqrt_le_sqrt hc_ge
  exact h103.trans hsqrt_ge
theorem tcArcsin_small_n700 {x : ℝ} (hx0 : 0 < x) (hx_ub : x ≤ 1 / ((10 : ℝ) ^ 103)) : 0 <
    Real.arcsin x ∧ Real.arcsin x ≤ 1 / (3 * (10 : ℝ) ^ 102) ∧ x ≤ Real.arcsin x := by
  have h102_ge1 : (1 : ℝ) ≤ (10 : ℝ) ^ 102 := one_le_pow₀ (by norm_num)
  have h103_ge1 : (1 : ℝ) ≤ (10 : ℝ) ^ 103 := one_le_pow₀ (by norm_num)
  have hx1 : x ≤ 1 := hx_ub.trans ((div_le_one (by positivity)).2 h103_ge1)
  have hsin_x : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) hx1
  have hα_pos : 0 < Real.arcsin x := by
    simpa [Real.arcsin_zero] using Real.arcsin_lt_arcsin (by norm_num) hx0 hx1
  have hα_lb : x ≤ Real.arcsin x := (by have hle := Real.sin_le hα_pos.le; rwa [hsin_x] at hle)
  set u : ℝ := 1 / (3 * (10 : ℝ) ^ 102); have hu_pos : 0 < u := (by dsimp [u]; positivity)
  have hu_le_third : u ≤ 1 / 3 := by
    dsimp [u]; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hx_le_sinu : x ≤ Real.sin u := by
    have hcube := (Real.sin_gt_sub_cube hu_pos).le
    have hu2 : u ^ 2 ≤ 1 / 9 := (by nlinarith [hu_pos])
    have hu3 : u ^ 3 / 6 ≤ (1 / 54) * u := by
      have h1 : u ^ 3 / 6 = (u ^ 2 / 6) * u := (by ring); rw [h1]
      exact mul_le_mul_of_nonneg_right (by linarith) hu_pos.le
    have h53 : 1 / ((10 : ℝ) ^ 103) ≤ (53 / 54) * u := by
      dsimp [u]; have hp : (0 : ℝ) < (10 : ℝ) ^ 102 := (by positivity)
      rw [show (10 : ℝ) ^ 103 = 10 * (10 : ℝ) ^ 102 by ring]; field_simp [hp.ne']; norm_num
    calc x ≤ 1 / ((10 : ℝ) ^ 103) := hx_ub
      _ ≤ (53 / 54) * u := h53
      _ = u - (1 / 54) * u := by ring
      _ ≤ u - u ^ 3 / 6 := sub_le_sub_left hu3 u
      _ ≤ Real.sin u := hcube
  have hα_le : Real.arcsin x ≤ u := by
    have h1 := Real.arcsin_le_arcsin hx_le_sinu
    have h2 : Real.arcsin (Real.sin u) = u :=
      Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
    linarith
  exact ⟨hα_pos, hα_le, hα_lb⟩
/-- Internal `10^100`-scale primary block `(cos φ₁, sin φ₁)` interval for `(tauNum,
  tauDen)`. -/
def tcSchedTrigIv (tauNum tauDen : ℕ) : TcIv × TcIv :=
  let s102 : ℤ := Int.ofNat (Nat.pow 10 102)
  tcTrigIv100 (Int.ofNat tauNum) (Int.ofNat tauDen)
    (Int.add (Int.mul (Int.ofNat tauNum) s102) (Int.ofNat tauDen))
    (Int.mul (Int.ofNat tauDen) s102)
/-- Pure-integer guard ensuring `tcSchedTrigIv` stays within the base `[0, 1]` octant. -/
def tcCheckSchedAngle (tauNum tauDen : ℕ) : Bool :=
  let s102 : ℤ := Int.ofNat (Nat.pow 10 102)
  let M : ℤ := Int.ofNat (Nat.pow 2 tcTrigHalvings)
  let b : ℤ := Int.add (Int.mul (Int.ofNat tauNum) s102) (Int.ofNat tauDen)
  let e : ℤ := Int.mul (Int.ofNat tauDen) s102
  Nat.blt 0 tauNum && Nat.blt 0 tauDen &&
    bleZ (Int.neg (Int.ediv (Int.neg (Int.mul b tcAmpScale)) (Int.mul M e))) tcAmpScale
theorem tcCheckSchedAngle_sound {n r tauNum tauDen : ℕ} (hn700 : 700 ≤ n) (hr1 : 1 ≤ r) (hr1024 : r
    ≤ 1024) (hchk : tcCheckSchedAngle tauNum tauDen = true) :
    let K_blk := tcKBlk n r tauNum tauDen; let cs := tcSchedTrigIv tauNum tauDen
    tcMemAmpIv (Real.cos ((K_blk : ℝ) * tcTheta1Real (2 ^ n) r)) cs.1 ∧ tcMemAmpIv (Real.sin ((K_blk
      : ℝ) * tcTheta1Real (2 ^ n) r)) cs.2 ∧ (K_blk : ℝ) ≤ ((tauNum : ℝ) / (2 * (tauDen : ℝ))) *
      √((2 ^ n : ℝ) / (r : ℝ)) + 3 / 2 ∧ ((10 : ℝ) ^ 103) ≤ √((2 ^ n : ℝ) / (r : ℝ)) := by
  intro K_blk cs; unfold tcCheckSchedAngle at hchk
  simp only [Bool.and_eq_true, Nat.blt_eq, bleZ_eq_true_iff,
    tcInt_add_eq, tcInt_mul_eq, tcInt_ediv_eq, tcInt_neg_eq, tcInt_ofNat_eq] at hchk
  rcases hchk with ⟨⟨htau_pos, hden_pos⟩, hyHi_le⟩
  have hsqrt_ge := tcSqrtRatio_ge_of_n700 hn700 hr1 hr1024; set c₁ : ℝ := (2 ^ n : ℝ) / (r : ℝ)
  have hsqrt_pos : 0 < √c₁ := lt_of_lt_of_le (by positivity) hsqrt_ge
  set α : ℝ := Real.arcsin (1 / √c₁)
  have hx1_ub : 1 / √c₁ ≤ 1 / ((10 : ℝ) ^ 103) := one_div_le_one_div_of_le (by positivity) hsqrt_ge
  rcases tcArcsin_small_n700 (by positivity) hx1_ub with ⟨hα_pos, hα_le, hα_lb⟩
  have hθ1_eq : tcTheta1Real (2 ^ n) r = 2 * α := by
    unfold tcTheta1Real; dsimp [α, c₁]; push_cast; rw [Real.sqrt_div (by positivity), one_div_div]
  set tau : ℝ := (tauNum : ℝ) / (tauDen : ℝ)
  have htau_pos_r : 0 < tau := div_pos (Nat.cast_pos.2 htau_pos) (Nat.cast_pos.2 hden_pos)
  set y : ℝ := tau / (2 * α); set K₀ : ℕ := (round y).toNat; have hK_eq : K_blk = K₀ + 1 := rfl
  have hK0_cast : (K₀ : ℝ) = ((round y : ℤ) : ℝ) := by
    have hr_nn : 0 ≤ round y := (by rw [round_eq]; exact Int.floor_nonneg.2 (by positivity))
    have hz : (K₀ : ℤ) = round y := Int.toNat_of_nonneg hr_nn; exact_mod_cast hz
  have hK0_lo : y - 1 / 2 < (K₀ : ℝ) := by
    rw [hK0_cast, round_eq]; linarith [Int.lt_floor_add_one (y + 1 / 2)]
  have hK0_hi : (K₀ : ℝ) ≤ y + 1 / 2 := (by rw [hK0_cast, round_eq]; exact Int.floor_le (y + 1 / 2))
  have hK_lo : y + 1 / 2 ≤ (K_blk : ℝ) := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith)
  have hK_hi : (K_blk : ℝ) ≤ y + 3 / 2 := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith)
  have hK_bound : (K_blk : ℝ) ≤ ((tauNum : ℝ) / (2 * (tauDen : ℝ))) * √c₁ + 3 / 2 := by
    have h1 : 1 / α ≤ √c₁ := by
      have hd := one_div_le_one_div_of_le (by positivity) hα_lb; rwa [one_div_one_div] at hd
    have h2 := mul_le_mul_of_nonneg_left h1 (div_nonneg htau_pos_r.le (by norm_num : (0 : ℝ) ≤ 2))
    have h3 : (tau / 2) * (1 / α) = y := (by dsimp [y]; ring)
    have h4 : (tau / 2) * √c₁ = ((tauNum : ℝ) / (2 * (tauDen : ℝ))) * √c₁ := (by dsimp [tau]; ring)
    linarith
  set φ₁ : ℝ := (K_blk : ℝ) * tcTheta1Real (2 ^ n) r
  have hφ1_eq : φ₁ = 2 * (K_blk : ℝ) * α := (by dsimp [φ₁]; rw [hθ1_eq]; ring)
  have h2αy : 2 * α * y = tau := mul_div_cancel₀ tau (by positivity)
  have hφ1_lo : tau ≤ φ₁ := by
    have hm := mul_le_mul_of_nonneg_left hK_lo (by positivity : (0 : ℝ) ≤ 2 * α)
    linarith [hm, h2αy, show (2 * α) * (y + 1 / 2) = 2 * α * y + α by ring,
      show (2 * α) * (K_blk : ℝ) = 2 * (K_blk : ℝ) * α by ring]
  have h3α : 3 * α ≤ 1 / ((10 : ℝ) ^ 102) := by
    have hm := mul_le_mul_of_nonneg_left hα_le (by norm_num : (0 : ℝ) ≤ 3)
    have hrew : 3 * (1 / (3 * (10 : ℝ) ^ 102)) = 1 / ((10 : ℝ) ^ 102) := by
      have hp : (0 : ℝ) < (10 : ℝ) ^ 102 := (by positivity); field_simp [hp.ne']
    linarith
  have hφ1_hi : φ₁ ≤ tau + 1 / ((10 : ℝ) ^ 102) := by
    have hm := mul_le_mul_of_nonneg_left hK_hi (by positivity : (0 : ℝ) ≤ 2 * α)
    linarith [hm, h2αy, h3α, show (2 * α) * (y + 3 / 2) = 2 * α * y + 3 * α by ring,
      show (2 * α) * (K_blk : ℝ) = 2 * (K_blk : ℝ) * α by ring]
  have hs102_pos : (0 : ℤ) < (10 : ℤ) ^ 102 := (by positivity)
  have hden_pos_z : (0 : ℤ) < (tauDen : ℤ) := (by exact_mod_cast hden_pos)
  have hden_ne : (tauDen : ℝ) ≠ 0 := (Nat.cast_pos.2 hden_pos).ne'
  have hs102_ne : ((10 : ℝ) ^ 102) ≠ 0 := (by positivity)
  have hlo_eq : ((tauNum : ℤ) : ℝ) / ((tauDen : ℤ) : ℝ) = tau := (by dsimp [tau]; push_cast; rfl)
  have hhi_eq : (((tauNum : ℤ) * (10 : ℤ) ^ 102 + (tauDen : ℤ) : ℤ) : ℝ) /
      (((tauDen : ℤ) * (10 : ℤ) ^ 102 : ℤ) : ℝ) = tau + 1 / ((10 : ℝ) ^ 102) := by
    have hB_pos : (0 : ℝ) < (((tauDen : ℤ) * (10 : ℤ) ^ 102 : ℤ) : ℝ) := by
      exact_mod_cast mul_pos hden_pos_z hs102_pos
    rw [div_eq_iff hB_pos.ne']; dsimp [tau]; push_cast
    have h1 : ((tauNum : ℝ) / (tauDen : ℝ)) * ((tauDen : ℝ) * (10 : ℝ) ^ 102) =
        (tauNum : ℝ) * (10 : ℝ) ^ 102 := by
      rw [← mul_assoc, div_mul_cancel₀ _ hden_ne]
    have h2 : (1 / ((10 : ℝ) ^ 102)) * ((tauDen : ℝ) * (10 : ℝ) ^ 102) = (tauDen : ℝ) := by
      rw [mul_comm (tauDen : ℝ), ← mul_assoc, one_div_mul_cancel hs102_ne, one_mul]
    linear_combination -h1 - h2
  have hlo_φ1 : ((tauNum : ℤ) : ℝ) / ((tauDen : ℤ) : ℝ) ≤ φ₁ := (by rw [hlo_eq]; exact hφ1_lo)
  have hhi_φ1 : φ₁ ≤ (((tauNum : ℤ) * (10 : ℤ) ^ 102 + (tauDen : ℤ) : ℤ) : ℝ) /
      (((tauDen : ℤ) * (10 : ℤ) ^ 102 : ℤ) : ℝ) := by
    rw [hhi_eq]; exact hφ1_hi
  rcases tcTrigIv100_sound (φ := φ₁) (Int.natCast_nonneg tauNum) hden_pos_z
      (mul_pos hden_pos_z hs102_pos) hlo_φ1 hhi_φ1 hyHi_le with ⟨hc1, hs1⟩
  have hcs : cs = tcTrigIv100 (tauNum : ℤ) (tauDen : ℤ)
      ((tauNum : ℤ) * (10 : ℤ) ^ 102 + (tauDen : ℤ)) ((tauDen : ℤ) * (10 : ℤ) ^ 102) := rfl
  rw [← hcs] at hc1 hs1; exact ⟨hc1, hs1, hK_bound, hsqrt_ge⟩
/-! ## 3. `2d`-Dimensional `TensorConveyor` Evolution & `r`-Independent Schedule Checker -/
/-- Safe lookup into `List TcIv`, defaulting to `(0, 0)`. -/
def tcListGetIv (l : List TcIv) (k : ℕ) : TcIv :=
  match l[k]? with
  | some v => v
  | none => (0, 0)
theorem tcListGetIv_ofFn {m : ℕ} (f : Fin m → TcIv) (k : ℕ) (hk : k < m) :
    tcListGetIv (List.ofFn f) k = f ⟨k, hk⟩ := by
  unfold tcListGetIv; simp [hk]
/-- Safe lookup into `List ℤ`, defaulting to `0`. -/
def tcListGetZ (l : List ℤ) (k : ℕ) : ℤ :=
  match l[k]? with
  | some v => v
  | none => 0
theorem tcListGetZ_ofFn {m : ℕ} (f : Fin m → ℤ) (k : ℕ) (hk : k < m) :
    tcListGetZ (List.ofFn f) k = f ⟨k, hk⟩ := by
  unfold tcListGetZ; simp [hk]
/-- Initial real `2d` state `(1, 0,..., 0)`. -/
def tcInitReal (k : ℕ) : ℝ :=
  if k = 0 then 1 else 0
/-- Real Grover block step rotating every pair `(2w, 2w + 1)` (`w < d`) by `(c1, s1)`. -/
def tcGroverStepReal (d : ℕ) (c1 s1 : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < 2 * d then
    let w := k / 2
    if k % 2 = 0 then
      c1 * a (2 * w) - s1 * a (2 * w + 1)
    else
      s1 * a (2 * w) + c1 * a (2 * w + 1)
  else
    0
/-- Real zero-oracle intertwiner step rotating every pair `(2w - 1, 2w)` (`1 ≤ w < d`). -/
noncomputable def tcIntertwinerStepReal (d : ℕ) (uRow : ℕ → ℤ × ℤ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < 2 * d then
    if k = 0 then
      a 0
    else if k + 1 < 2 * d then
      let w := (k + 1) / 2
      let p := uRow (w - 1)
      let ca : ℝ := (tcRatCos ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
      let sa : ℝ := (tcRatSin ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
      if k % 2 = 1 then
        ca * a (2 * w - 1) - sa * a (2 * w)
      else
        sa * a (2 * w - 1) + ca * a (2 * w)
    else
      a (2 * d - 1)
  else
    0
/-- Real single `TensorConveyor` pulse step (`tcGroverStepReal` followed by intertwiner). -/
noncomputable def tcBlockStepReal (d : ℕ) (c1 s1 : ℝ) (uRow : ℕ → ℤ × ℤ) (a : ℕ → ℝ) :
    ℕ → ℝ :=
  tcIntertwinerStepReal d uRow (tcGroverStepReal d c1 s1 a)
/-- Real `2d`-state after `t` pulses `0.. t - 1`. -/
noncomputable def tcEvolutionReal (d : ℕ) (c1 s1 : ℝ) (uFn : ℕ → ℕ → ℤ × ℤ) :
    ℕ → (ℕ → ℝ)
  | 0 => tcInitReal
  | t + 1 => tcBlockStepReal d c1 s1 (uFn t) (tcEvolutionReal d c1 s1 uFn t)
/-- Ideal hit-weight probability `wt_ideal(w)` (`0 ≤ w ≤ d`) of a `2d` real state `a`. -/
def tcWeightProbReal (d : ℕ) (a : ℕ → ℝ) (w : ℕ) : ℝ :=
  if w = 0 then
    (a 0) ^ 2
  else if w < d then
    (a (2 * w - 1)) ^ 2 + (a (2 * w)) ^ 2
  else if w = d then
    (a (2 * d - 1)) ^ 2
  else
    0
theorem tcWeightProbReal_nonneg (d : ℕ) (a : ℕ → ℝ) (w : ℕ) : 0 ≤ tcWeightProbReal d a w := by
  unfold tcWeightProbReal; split_ifs <;> positivity
/-- Componentwise `10^100`-scale interval membership on coordinates `0.. 2d - 1`. -/
def tcMemStateIv (d : ℕ) (a : ℕ → ℝ) (stIv : List TcIv) : Prop :=
  ∀ k < 2 * d, tcMemAmpIv (a k) (tcListGetIv stIv k)
/-- Force outer `List` constructor to WHNF before invoking `k`. -/
def tcForceListSpine {α β : Type*} (l : List α) (k : List α → β) : β :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem tcForceListSpine_eq {α β : Type*} (l : List α) (k : List α → β) :
    tcForceListSpine l k = k l := by
  cases l <;> rfl
/-- Constructor-pattern WHNF forcing for `ℕ` (`O(1)`, passes reduced GMP `Nat` to `k`). -/
def tcForceNat {α : Type*} (x : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn x (k 0) (fun m ↦ k (Nat.succ m))
theorem tcForceNat_eq {α : Type*} (x : ℕ) (k : ℕ → α) : tcForceNat x k = k x := by
  cases x <;> rfl
/-- `O(1)` head lookup `tcListGetIv l 0` via direct pattern match. -/
def tcHeadIv : List TcIv → TcIv
  | x :: _ => x
  | [] => (Int.ofNat 0, Int.ofNat 0)
/-- Constructor pattern-match extracting `(tcHeadIv l, l.tail)` with zero `List.tail`
  thunks. -/
def tcUnconsIv {α : Type*} (l : List TcIv) (k : TcIv → List TcIv → α) : α :=
  match l with
  | [] => k (Int.ofNat 0, Int.ofNat 0) []
  | x :: xs => k x xs
theorem tcUnconsIv_eq {α : Type*} (l : List TcIv) (k : TcIv → List TcIv → α) :
    tcUnconsIv l k = k (tcHeadIv l) l.tail := by
  cases l <;> rfl
theorem tcHeadIv_eq (l : List TcIv) : tcHeadIv l = tcListGetIv l 0 := by
  cases l <;> rfl
theorem tcListGetIv_cons (x : TcIv) (xs : List TcIv) (k : ℕ) :
    tcListGetIv (x :: xs) (k + 1) = tcListGetIv xs k := rfl
theorem tcListGetIv_tail (l : List TcIv) (k : ℕ) :
    tcListGetIv l.tail k = tcListGetIv l (k + 1) := by
  cases l <;> simp [tcListGetIv]
/-- All-zero `TcIv` list of length `cnt`. -/
def tcZeroIvList : ℕ → List TcIv
  | 0 => []
  | cnt + 1 => (Int.ofNat 0, Int.ofNat 0) :: tcZeroIvList cnt
theorem tcListGetIv_zeroIvList :
    ∀ (cnt k : ℕ), tcListGetIv (tcZeroIvList cnt) k = (0, 0)
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | cnt + 1, k + 1 => tcListGetIv_zeroIvList cnt k
/-- Initial `10^100`-scale interval vector `[(10^100, 10^100), (0, 0),..., (0, 0)]`. -/
def tcInitIv : ℕ → List TcIv
  | 0 => []
  | dPred + 1 =>
      tcWithForcedInt tcAmpScale fun ampS ↦
        (ampS, ampS) :: (Int.ofNat 0, Int.ofNat 0) :: tcZeroIvList (2 * dPred)
theorem tcMemStateIv_init (d : ℕ) : tcMemStateIv d tcInitReal (tcInitIv d) := by
  intro k hk; have hS : (0 : ℝ) < (tcAmpScale : ℝ) := tcAmpScale_pos_real
  cases d with
  | zero => omega
  | succ dPred =>
      simp only [tcInitIv, tcInitReal, tcWithForcedInt_eq]
      cases k with
      | zero => simp [tcListGetIv, tcMemAmpIv, div_self hS.ne']
      | succ k1 =>
          cases k1 with
          | zero => simp [tcListGetIv, tcMemAmpIv]
          | succ k2 =>
              rw [tcListGetIv_cons, tcListGetIv_cons, tcListGetIv_zeroIvList]; simp [tcMemAmpIv]
/-- WHNF-forced `10^100`-scale Grover block step on `2d` amplitudes (`O(d)` linear). -/
def tcGroverStepIv : ℕ → TcIv → TcIv → List TcIv → List TcIv
  | 0, _, _, _ => []
  | dPred + 1, c1Iv, s1Iv, stIv =>
      tcUnconsIv stIv fun a0 rest0 ↦
        tcUnconsIv rest0 fun a1 rest1 ↦
          tcWithForcedIv (tcIvSub (tcIvMul c1Iv a0) (tcIvMul s1Iv a1)) fun y0 ↦
            tcWithForcedIv (tcIvAdd (tcIvMul s1Iv a0) (tcIvMul c1Iv a1)) fun y1 ↦
              tcForceListSpine (tcGroverStepIv dPred c1Iv s1Iv rest1) fun tl ↦
                y0 :: y1 :: tl
theorem tcListGetIv_groverStepIv (d : ℕ) (c1Iv s1Iv : TcIv) : ∀ (stIv : List TcIv) (k : ℕ), k < 2 *
    d → tcListGetIv (tcGroverStepIv d c1Iv s1Iv stIv) k =
        let w := k / 2; let a0 := tcListGetIv stIv (2 * w); let a1 := tcListGetIv stIv (2 * w + 1)
        if k % 2 = 0 then tcIvSub (tcIvMul c1Iv a0) (tcIvMul s1Iv a1) else tcIvAdd (tcIvMul s1Iv a0)
          (tcIvMul c1Iv a1) := by
  induction d with
  | zero => intro _ _ hk; omega
  | succ dPred ih =>
      intro stIv k hk; unfold tcGroverStepIv; rw [tcUnconsIv_eq, tcUnconsIv_eq]
      simp only [tcWithForcedIv_eq, tcForceListSpine_eq, tcHeadIv_eq, tcListGetIv_tail,
        Nat.zero_add]
      cases k with
      | zero => simp [tcListGetIv]
      | succ k1 =>
          cases k1 with
          | zero => simp [tcListGetIv]
          | succ k2 =>
              change tcListGetIv (tcGroverStepIv dPred c1Iv s1Iv stIv.tail.tail) k2 = _
              rw [ih stIv.tail.tail k2 (by omega)]
              have hw : (k2 + 2) / 2 = k2 / 2 + 1 := (by omega)
              have hm : (k2 + 2) % 2 = k2 % 2 := (by omega); dsimp only
              rw [tcListGetIv_tail, tcListGetIv_tail, tcListGetIv_tail, tcListGetIv_tail, hw, hm]
              have h0 : 2 * (k2 / 2) + 1 + 1 = 2 * (k2 / 2 + 1) := (by omega); rw [h0]
theorem tcMemStateIv_groverStep {d : ℕ} {c1 s1 : ℝ} {c1Iv s1Iv : TcIv} {a : ℕ → ℝ} {stIv : List
    TcIv} (hc1 : tcMemAmpIv c1 c1Iv) (hs1 : tcMemAmpIv s1 s1Iv) (hst : tcMemStateIv d a stIv) :
    tcMemStateIv d (tcGroverStepReal d c1 s1 a) (tcGroverStepIv d c1Iv s1Iv stIv) := by
  intro k hk; unfold tcGroverStepReal
  rw [tcListGetIv_groverStepIv d c1Iv s1Iv stIv k hk]; simp only [hk, ↓reduceIte]
  have ha0 := hst (2 * (k / 2)) (by omega); have ha1 := hst (2 * (k / 2) + 1) (by omega)
  by_cases hmod : k % 2 = 0
  · simp only [hmod, ↓reduceIte]
    exact tcMemAmpIv_sub (tcMemAmpIv_mul hc1 ha0) (tcMemAmpIv_mul hs1 ha1)
  · simp only [hmod, ↓reduceIte]
    exact tcMemAmpIv_add (tcMemAmpIv_mul hs1 ha0) (tcMemAmpIv_mul hc1 ha1)
/-- Linear `O(d)` pair-by-pair inner worker for `tcIntertwinerStepIv`. -/
def tcIntertwinerPairs (ampS : ℤ) (uRow : ℕ → ℤ × ℤ) : ℕ → ℕ → List TcIv → List TcIv
  | 0, _, stL =>
      tcUnconsIv stL fun lastIv _ ↦ [lastIv]
  | m + 1, j, stL =>
      tcUnconsIv stL fun x1 rest0 ↦
        tcUnconsIv rest0 fun x2 rest1 ↦
          let p := uRow j
          tcWithForcedInt (Int.add (Int.mul p.2 p.2) (Int.mul p.1 p.1)) fun den ↦
            tcWithForcedInt (Int.sub (Int.mul p.2 p.2) (Int.mul p.1 p.1)) fun cNum ↦
              tcWithForcedInt (Int.mul (Int.mul (Int.ofNat 2) p.1) p.2) fun sNum ↦
                tcWithForcedIv
                  (Int.ediv (Int.mul cNum ampS) den,
                    Int.neg (Int.ediv (Int.neg (Int.mul cNum ampS)) den))
                  fun cIv ↦
                  tcWithForcedIv
                    (Int.ediv (Int.mul sNum ampS) den,
                      Int.neg (Int.ediv (Int.neg (Int.mul sNum ampS)) den))
                    fun sIv ↦
                    tcWithForcedIv (tcIvSub (tcIvMul cIv x1) (tcIvMul sIv x2)) fun z1 ↦
                      tcWithForcedIv (tcIvAdd (tcIvMul sIv x1) (tcIvMul cIv x2)) fun z2 ↦
                        tcForceNat (Nat.add j 1) fun j1 ↦
                          tcForceListSpine (tcIntertwinerPairs ampS uRow m j1 rest1) fun tl ↦
                            z1 :: z2 :: tl
/-- WHNF-forced `10^100`-scale intertwiner step on `2d` amplitudes (`O(d)` linear). -/
def tcIntertwinerStepIv : ℕ → (ℕ → ℤ × ℤ) → List TcIv → List TcIv
  | 0, _, _ => []
  | dPred + 1, uRow, stIv =>
      tcWithForcedInt tcAmpScale fun ampS ↦
        tcUnconsIv stIv fun a0 rest ↦
          tcForceListSpine (tcIntertwinerPairs ampS uRow dPred 0 rest) fun tl ↦
            a0 :: tl
theorem tcListGetIv_intertwinerPairs (uRow : ℕ → ℤ × ℤ) : ∀ (m j : ℕ) (stL : List TcIv) (idx : ℕ),
    idx < 2 * m + 1 → tcListGetIv (tcIntertwinerPairs tcAmpScale uRow m j stL) idx = if idx < 2 * m
    then
          let q := idx / 2; let p := uRow (j + q); let den := p.2 * p.2 + p.1 * p.1
          let cNum := p.2 * p.2 - p.1 * p.1; let sNum := 2 * p.1 * p.2
          let cIv : TcIv := ((cNum * tcAmpScale) / den, -((-(cNum * tcAmpScale)) / den))
          let sIv : TcIv := ((sNum * tcAmpScale) / den, -((-(sNum * tcAmpScale)) / den))
          let x1 := tcListGetIv stL (2 * q); let x2 := tcListGetIv stL (2 * q + 1)
          if idx % 2 = 0 then tcIvSub (tcIvMul cIv x1) (tcIvMul sIv x2) else tcIvAdd (tcIvMul sIv
            x1) (tcIvMul cIv x2) else tcListGetIv stL (2 * m) := by
  intro m
  induction m with
  | zero =>
      intro j stL idx hidx; have hz : idx = 0 := (by omega); subst hz
      simp [tcIntertwinerPairs, tcUnconsIv_eq, tcHeadIv_eq, tcListGetIv]
  | succ mPred ih =>
      intro j stL idx hidx; unfold tcIntertwinerPairs; rw [tcUnconsIv_eq, tcUnconsIv_eq]
      simp only [tcWithForcedInt_eq, tcWithForcedIv_eq, tcForceNat_eq, tcForceListSpine_eq,
        tcHeadIv_eq, tcListGetIv_tail, Nat.zero_add, tcInt_add_eq, tcInt_sub_eq, tcInt_mul_eq,
        tcInt_ediv_eq, tcInt_neg_eq, tcInt_ofNat_eq, Nat.cast_ofNat]
      cases idx with
      | zero => simp [tcListGetIv]
      | succ i1 =>
          cases i1 with
          | zero => have h1lt : 1 < 2 * (mPred + 1) := (by omega); simp [tcListGetIv, h1lt]
          | succ i2 =>
              change tcListGetIv (tcIntertwinerPairs tcAmpScale uRow mPred (j + 1) stL.tail.tail)
                i2 = _
              rw [ih (j + 1) stL.tail.tail i2 (by omega)]
              have hlt_iff : (i2 < 2 * mPred) ↔ (i2 + 2 < 2 * (mPred + 1)) := (by omega)
              by_cases hlt : i2 < 2 * mPred
              · have hlt2 : i2 + 2 < 2 * (mPred + 1) := hlt_iff.1 hlt
                simp only [hlt, hlt2, ↓reduceIte]; have hq : (i2 + 2) / 2 = i2 / 2 + 1 := (by omega)
                have hm : (i2 + 2) % 2 = i2 % 2 := (by omega)
                have hjq : j + 1 + i2 / 2 = j + (i2 / 2 + 1) := (by omega)
                rw [tcListGetIv_tail, tcListGetIv_tail, tcListGetIv_tail, tcListGetIv_tail,
                  hq, hm, hjq]
                have h0 : 2 * (i2 / 2) + 1 + 1 = 2 * (i2 / 2 + 1) := (by omega); rw [h0]
              · have hlt2 : ¬ i2 + 2 < 2 * (mPred + 1) := mt hlt_iff.2 hlt
                simp only [hlt, hlt2, ↓reduceIte, tcListGetIv_tail]
                have heq : 2 * mPred + 1 + 1 = 2 * (mPred + 1) := (by omega); rw [heq]
theorem tcMemStateIv_intertwinerStep {d : ℕ} {uRow : ℕ → ℤ × ℤ} {a : ℕ → ℝ} {stIv : List TcIv} (hu :
    ∀ j < d - 1, (uRow j).2 ≠ 0) (hst : tcMemStateIv d a stIv) : tcMemStateIv d
    (tcIntertwinerStepReal d uRow a) (tcIntertwinerStepIv d uRow stIv) := by
  intro k hk
  cases d with
  | zero => omega
  | succ dPred =>
      simp only [tcIntertwinerStepReal, tcIntertwinerStepIv, tcWithForcedInt_eq, tcUnconsIv_eq,
        tcForceListSpine_eq, tcHeadIv_eq, hk, ↓reduceIte]
      cases k with
      | zero => simp only [↓reduceIte, tcListGetIv]; exact hst 0 hk
      | succ idx =>
          simp only [Nat.succ_ne_zero, ↓reduceIte, tcListGetIv_cons]
          rw [tcListGetIv_intertwinerPairs uRow dPred 0 stIv.tail idx (by omega)]
          have hlt_iff : (idx < 2 * dPred) ↔ (idx + 1 + 1 < 2 * (dPred + 1)) := (by omega)
          by_cases hlt : idx < 2 * dPred
          · have hk1 : idx + 1 + 1 < 2 * (dPred + 1) := hlt_iff.1 hlt; dsimp only
            simp only [hlt, hk1, ↓reduceIte, Nat.zero_add, tcListGetIv_tail]; set q := idx / 2
            have hw_eq : (idx + 1 + 1) / 2 = q + 1 := (by omega)
            have hq_lt : q < dPred := (by omega)
            rcases tcMemAmpIv_pythag_ratDiv (uRow q).1 (uRow q).2 (hu q (by omega)) with
              ⟨hc, hs⟩
            have hx1 : tcMemAmpIv (a (2 * ((idx + 1 + 1) / 2) - 1))
                (tcListGetIv stIv (2 * q + 1)) := by
              rw [hw_eq, show 2 * (q + 1) - 1 = 2 * q + 1 by omega]
              exact hst (2 * q + 1) (by omega)
            have hx2 : tcMemAmpIv (a (2 * ((idx + 1 + 1) / 2)))
                (tcListGetIv stIv (2 * q + 1 + 1)) := by
              rw [hw_eq, show 2 * (q + 1) = 2 * q + 1 + 1 by omega]
              exact hst (2 * q + 1 + 1) (by omega)
            have hsub1 : (idx + 1 + 1) / 2 - 1 = q := (by omega); rw [hsub1]
            by_cases hmod : idx % 2 = 0
            · have hm1 : (idx + 1) % 2 = 1 := (by omega); simp only [hmod, hm1, ↓reduceIte]
              exact tcMemAmpIv_sub (tcMemAmpIv_mul hc hx1) (tcMemAmpIv_mul hs hx2)
            · have hm1 : (idx + 1) % 2 ≠ 1 := (by omega); simp only [hmod, hm1, ↓reduceIte]
              exact tcMemAmpIv_add (tcMemAmpIv_mul hs hx1) (tcMemAmpIv_mul hc hx2)
          · have hk1 : ¬ idx + 1 + 1 < 2 * (dPred + 1) := mt hlt_iff.2 hlt
            simp only [hlt, hk1, ↓reduceIte, tcListGetIv_tail]
            rw [show 2 * (dPred + 1) - 1 = 2 * dPred + 1 by omega]
            exact hst (2 * dPred + 1) (by omega)
/-- WHNF-forced `10^100`-scale `2d` state evolution over `steps` pulses `0.. steps - 1`. -/
def tcEvolutionIv (d : ℕ) (c1Iv s1Iv : TcIv) (uFn : ℕ → ℕ → ℤ × ℤ) : ℕ → List TcIv
  | 0 => tcInitIv d
  | t + 1 =>
      tcIntertwinerStepIv d (uFn t)
        (tcGroverStepIv d c1Iv s1Iv (tcEvolutionIv d c1Iv s1Iv uFn t))
theorem tcMemStateIv_evolution {d : ℕ} {c1 s1 : ℝ} {c1Iv s1Iv : TcIv} {uFn : ℕ → ℕ → ℤ × ℤ} (steps :
    ℕ) (hc1 : tcMemAmpIv c1 c1Iv) (hs1 : tcMemAmpIv s1 s1Iv) (hu : ∀ t < steps, ∀ j < d - 1, (uFn t
    j).2 ≠ 0) : tcMemStateIv d (tcEvolutionReal d c1 s1 uFn steps) (tcEvolutionIv d c1Iv s1Iv uFn
    steps) := by
  induction steps with
  | zero => exact tcMemStateIv_init d
  | succ t ih =>
      unfold tcEvolutionReal tcEvolutionIv tcBlockStepReal
      exact tcMemStateIv_intertwinerStep (hu t (by omega))
        (tcMemStateIv_groverStep hc1 hs1 (ih fun i hi j hj ↦ hu i (by omega) j hj))
/-- `10^12`-scaled hit-weight lower bound projected from a `10^100`-scale `2d` interval
  state. -/
def tcWeightProbLbFromIv (d : ℕ) (stIv : List TcIv) (w : ℕ) : ℤ :=
  if w == 0 then
    Int.ediv (tcIvSq (tcListGetIv stIv 0)).1 tcAmpToProbDiv
  else if w < d then
    Int.ediv (tcIvAdd (tcIvSq (tcListGetIv stIv (2 * w - 1)))
      (tcIvSq (tcListGetIv stIv (2 * w)))).1 tcAmpToProbDiv
  else if w == d then
    Int.ediv (tcIvSq (tcListGetIv stIv (2 * d - 1))).1 tcAmpToProbDiv
  else
    Int.ofNat 0
theorem tcWeightProbLbFromIv_le {d : ℕ} {a : ℕ → ℝ} {stIv : List TcIv}
    (hd : 1 ≤ d) (hst : tcMemStateIv d a stIv) (w : ℕ) (hw : w ≤ d) :
    ((tcWeightProbLbFromIv d stIv w : ℤ) : ℝ) / (tcScale : ℝ) ≤ tcWeightProbReal d a w := by
  have hdiv_pos : (0 : ℤ) < tcAmpToProbDiv := by
    change ((0 : ℕ) : ℤ) < ((10 ^ 88 : ℕ) : ℤ); exact Nat.cast_lt.2 (Nat.pow_pos (by omega))
  have hS : (0 : ℝ) < (tcScale : ℝ) := tcScale_pos_real
  have hmul_eq : (tcScale : ℝ) * (tcAmpToProbDiv : ℝ) = (tcAmpScale : ℝ) := by
    exact_mod_cast tcAmpScale_eq_mul.symm
  have hproj : ∀ {iv : TcIv} {y : ℝ}, tcMemAmpIv y iv →
      ((iv.1 / tcAmpToProbDiv : ℤ) : ℝ) / (tcScale : ℝ) ≤ y := by
    intro iv y hy
    have h1 := div_le_div_of_nonneg_right (tc_ediv_pos_le_real iv.1 tcAmpToProbDiv hdiv_pos) hS.le
    have h2 : (iv.1 : ℝ) / (tcAmpToProbDiv : ℝ) / (tcScale : ℝ) =
        (iv.1 : ℝ) / (tcAmpScale : ℝ) := by
      rw [div_div, mul_comm, hmul_eq]
    linarith [h1, h2, hy.1]
  unfold tcWeightProbLbFromIv tcWeightProbReal
  simp only [tcInt_ediv_eq, tcInt_ofNat_eq, Nat.cast_zero]; by_cases hw0 : w = 0
  · subst hw0; simp only [↓reduceIte, beq_self_eq_true]
    exact hproj (tcMemAmpIv_sq (hst 0 (by omega)))
  · have hbeq0 : (w == 0) = false := beq_false_of_ne hw0
    simp only [hw0, hbeq0, Bool.false_eq_true, ↓reduceIte]; by_cases hwd : w < d
    · simp only [hwd, ↓reduceIte]
      exact hproj (tcMemAmpIv_add (tcMemAmpIv_sq (hst (2 * w - 1) (by omega))) (tcMemAmpIv_sq (hst
        (2 * w) (by omega))))
    · have heq : w = d := (by omega); subst heq; simp only [lt_irrefl, ↓reduceIte, beq_self_eq_true]
      exact hproj (tcMemAmpIv_sq (hst (2 * w - 1) (by omega)))
/-- `r`-independent schedule certificate for a `d`-register `TensorConveyor`. -/
structure TensorSchedCert where
  /-- Number of `n`-bit registers per parallel slot (`2 ≤ d ≤ 12`). -/
  d : ℕ
  /-- Number of pulse segments (`1 ≤ steps ≤ 250`). -/
  steps : ℕ
  /-- Target primary-angle numerator per segment (`tau = tauNum / tauDen`). -/
  tauNum : ℕ
  /-- Target primary-angle denominator per segment (`0 < tauDen`). -/
  tauDen : ℕ
  /-- Rational stereographic intertwiner parameters `uFn t j` (`0 ≤ t < steps`, `0 ≤ j < d -
    1`). -/
  uFn : ℕ → ℕ → ℤ × ℤ
  /-- Certified `10^12`-scaled hit-weight lower bounds `wProbLb w` (`0 ≤ w ≤ d`). -/
  wProbLb : ℕ → ℤ
/-- Global `r`-independent schedule checker (`decide +kernel` runs once per schedule). -/
def tcCheckSched (sc : TensorSchedCert) : Bool :=
  decide (2 ≤ sc.d ∧ sc.d ≤ 12 ∧ 1 ≤ sc.steps ∧ sc.steps ≤ 250) &&
  tcCheckSchedAngle sc.tauNum sc.tauDen &&
  allRange (fun t ↦ allRange (fun j ↦ !beqZ (sc.uFn t j).2 (Int.ofNat 0)) (sc.d - 1)) sc.steps &&
  let cs := tcSchedTrigIv sc.tauNum sc.tauDen
  tcWithForcedIv cs.1 fun c1Iv ↦
    tcWithForcedIv cs.2 fun s1Iv ↦
      tcWithForcedIvList (tcEvolutionIv sc.d c1Iv s1Iv sc.uFn sc.steps) fun stIv ↦
        allRange
          (fun w ↦ bleZ (Int.ofNat 0) (sc.wProbLb w) &&
            bleZ (sc.wProbLb w) (tcWeightProbLbFromIv sc.d stIv w))
          (sc.d + 1)
theorem tcCheckSched_sound {sc : TensorSchedCert} {n r : ℕ} (hn700 : 700 ≤ n) (hr1 : 1 ≤ r) (hr1024
    : r ≤ 1024) (hchk : tcCheckSched sc = true) :
    let K_blk := tcKBlk n r sc.tauNum sc.tauDen; let θ₁ := tcTheta1Real (2 ^ n) r
    let a := tcEvolutionReal sc.d
      (Real.cos ((K_blk : ℝ) * θ₁)) (Real.sin ((K_blk : ℝ) * θ₁)) sc.uFn sc.steps
    2 ≤ sc.d ∧ sc.d ≤ 12 ∧ 1 ≤ sc.steps ∧ sc.steps ≤ 250 ∧ 0 < sc.tauNum ∧ 0 < sc.tauDen ∧ (∀ t <
      sc.steps, ∀ j < sc.d - 1, (sc.uFn t j).2 ≠ 0) ∧ (∀ w ≤ sc.d, 0 ≤ sc.wProbLb w ∧ (sc.wProbLb w
      : ℝ) / (tcScale : ℝ) ≤ tcWeightProbReal sc.d a w) ∧ (K_blk : ℝ) ≤ ((sc.tauNum : ℝ) / (2 *
      (sc.tauDen : ℝ))) * √((2 ^ n : ℝ) / (r : ℝ)) + 3 / 2 ∧ ((10 : ℝ) ^ 103) ≤ √((2 ^ n : ℝ) / (r :
      ℝ)) := by
  intro K_blk θ₁ a; unfold tcCheckSched at hchk
  simp only [Bool.and_eq_true, tcWithForcedIv_eq, tcWithForcedIvList_eq, decide_eq_true_eq] at hchk
  rcases hchk with ⟨⟨⟨⟨hd2, hd12, hst1, hst250⟩, hang⟩, hnz⟩, hw_all⟩
  have hang_cp := hang; unfold tcCheckSchedAngle at hang_cp
  simp only [Bool.and_eq_true, Nat.blt_eq] at hang_cp
  rcases tcCheckSchedAngle_sound hn700 hr1 hr1024 hang with ⟨hc1, hs1, hK_le, hsqrt_ge⟩
  have hu_nz : ∀ t < sc.steps, ∀ j < sc.d - 1, (sc.uFn t j).2 ≠ 0 := by
    intro t ht j hj h0
    have hj_chk := of_allRange (p := fun j' ↦ !beqZ (sc.uFn t j').2 (Int.ofNat 0)) (of_allRange (p
      := fun t' ↦ allRange (fun j' ↦ !beqZ (sc.uFn t' j').2 (Int.ofNat 0)) (sc.d - 1)) hnz ht) hj
    have hbeq : beqZ (sc.uFn t j).2 (Int.ofNat 0) = true := (beqZ_eq_true_iff _ _).2 h0
    rw [hbeq] at hj_chk; exact Bool.noConfusion hj_chk
  have hst := tcMemStateIv_evolution sc.steps hc1 hs1 hu_nz
  refine ⟨hd2, hd12, hst1, hst250, hang_cp.1.1, hang_cp.1.2, hu_nz, ?_, hK_le, hsqrt_ge⟩
  intro w hw; have hw_lt : w < sc.d + 1 := (by omega)
  set stIv := tcEvolutionIv sc.d (tcSchedTrigIv sc.tauNum sc.tauDen).1
    (tcSchedTrigIv sc.tauNum sc.tauDen).2 sc.uFn sc.steps
  have hw_chk := of_allRange (p := fun w' ↦ bleZ (Int.ofNat 0) (sc.wProbLb w') && bleZ (sc.wProbLb
    w') (tcWeightProbLbFromIv sc.d stIv w')) hw_all hw_lt
  simp only [Bool.and_eq_true, bleZ_eq_true_iff, tcInt_ofNat_eq, Nat.cast_zero] at hw_chk
  refine ⟨hw_chk.1, ?_⟩
  have hcast_w : (sc.wProbLb w : ℝ) ≤ (tcWeightProbLbFromIv sc.d stIv w : ℝ) := by
    exact_mod_cast hw_chk.2
  have hle := div_le_div_of_nonneg_right hcast_w tcScale_pos_real.le
  exact hle.trans (tcWeightProbLbFromIv_le (by omega) hst w hw)
/-! ## 4. `m = 2^e` Convolution & Monotone-in-`r` Coupon-Occupancy Bucket Certificates -/
/-- WHNF-forced prefix sum `∑ i ∈ Finset.range cnt, f i` over `ℤ`. -/
def tcSumRangeZ (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => Int.ofNat 0
  | cnt + 1 => tcWithForcedInt (tcSumRangeZ f cnt) fun acc ↦ Int.add acc (f cnt)
theorem tcSumRangeZ_eq (f : ℕ → ℤ) (cnt : ℕ) :
    (tcSumRangeZ f cnt : ℝ) = ∑ i ∈ Finset.range cnt, (f i : ℝ) := by
  induction cnt with
  | zero => simp [tcSumRangeZ]
  | succ n ih =>
      unfold tcSumRangeZ
      rw [tcWithForcedInt_eq, tcInt_add_eq, Int.cast_add, ih, Finset.sum_range_succ]
theorem tcSumRangeZ_nonneg {f : ℕ → ℤ} {cnt : ℕ} (hf : ∀ i < cnt, 0 ≤ f i) :
    0 ≤ tcSumRangeZ f cnt := by
  induction cnt with
  | zero => simp [tcSumRangeZ]
  | succ n ih =>
      unfold tcSumRangeZ; rw [tcWithForcedInt_eq, tcInt_add_eq]
      exact add_nonneg (ih fun i hi ↦ hf i (by omega)) (hf n (by omega))
/-- Real discrete convolution of `p` (`0..lenP`) and `q` (`0..lenQ`) at total sum `h`. -/
def tcConvReal (lenP lenQ : ℕ) (p q : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (lenP + 1), if i ≤ h ∧ h - i ≤ lenQ then p i * q (h - i) else 0
/-- Real `2^e`-fold self-convolution of a `d`-register hit-weight distribution `p`. -/
def tcConvPow2Real (d : ℕ) (p : ℕ → ℝ) : ℕ → (ℕ → ℝ)
  | 0 => p
  | e + 1 =>
      let prev := tcConvPow2Real d p e
      tcConvReal (2 ^ e * d) (2 ^ e * d) prev prev
/-- Binary Okasaki Braun tree over `ℤ` for `O(log n)` random access in convolutions. -/
inductive TcZTree : Type
  | empty : TcZTree
  | node : ℤ → TcZTree → TcZTree → TcZTree
/-- Force outer `TcZTree` constructor to WHNF before invoking `k`. -/
def tcForceZTree {α : Type*} (t : TcZTree) (k : TcZTree → α) : α :=
  match t with
  | .empty => k .empty
  | .node x l r => k (.node x l r)
theorem tcForceZTree_eq {α : Type*} (t : TcZTree) (k : TcZTree → α) : tcForceZTree t k = k t := by
  cases t <;> rfl
/-- Prepend `v` at index `0` of a `TcZTree` (`O(log n)`), forcing internal WHNF. -/
def tcZTreeCons (v : ℤ) : TcZTree → TcZTree
  | .empty => .node v .empty .empty
  | .node x l r => tcForceZTree (tcZTreeCons x r) fun l' ↦ .node v l' l
/-- `O(log n)` lookup in a `TcZTree` by 0-based index `k` (returns `0` out of bounds). -/
def tcZTreeGet : TcZTree → ℕ → ℤ
  | .empty, _ => 0
  | .node x l r, k =>
      if k == 0 then x
      else
        tcForceNat ((k - 1) / 2) fun k' ↦
          if k % 2 == 1 then tcZTreeGet l k' else tcZTreeGet r k'
theorem tcZTreeGet_cons (t : TcZTree) : ∀ (v : ℤ) (k : ℕ), tcZTreeGet (tcZTreeCons v t) k = if k = 0
    then v else tcZTreeGet t (k - 1) := by
  induction t with
  | empty =>
      intro v k
      cases k <;> simp [tcZTreeCons, tcZTreeGet, tcForceNat_eq]
  | node x l r _ ihr =>
      intro v k
      cases k with
      | zero => simp [tcZTreeCons, tcForceZTree_eq, tcZTreeGet]
      | succ j =>
          simp only [tcZTreeCons, tcForceZTree_eq, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          conv_lhs =>
            unfold tcZTreeGet
            simp only [beq_iff_eq, Nat.succ_ne_zero, ↓reduceIte, tcForceNat_eq, Nat.add_sub_cancel]
          rw [ihr x (j / 2)]
          cases j with
          | zero => simp [tcZTreeGet]
          | succ m =>
              have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
              conv_rhs =>
                unfold tcZTreeGet
                simp only [beq_iff_eq, hne, ↓reduceIte, tcForceNat_eq, Nat.add_sub_cancel]
              by_cases hp : (m + 1) % 2 = 1
              · have hp2 : (m + 1 + 1) % 2 = 0 := (by omega)
                have hdiv : (m + 1) / 2 = m / 2 := (by omega); simp [hp, hp2, hdiv]
              · have hp1 : (m + 1) % 2 = 0 := (by omega)
                have hp2 : (m + 1 + 1) % 2 = 1 := (by omega)
                have hdiv : (m + 1) / 2 = m / 2 + 1 := (by omega); simp [hp1, hp2, hdiv]
/-- Build a WHNF-forced `TcZTree` from a `List ℤ` in `O(n log n)` time. -/
def tcZTreeOfList : List ℤ → TcZTree
  | [] => .empty
  | x :: xs => tcZTreeCons x (tcZTreeOfList xs)
theorem tcZTreeGet_ofList :
    ∀ (l : List ℤ) (k : ℕ), tcZTreeGet (tcZTreeOfList l) k = tcListGetZ l k
  | [], _ => by simp [tcZTreeOfList, tcZTreeGet, tcListGetZ]
  | x :: xs, 0 => by simp [tcZTreeOfList, tcZTreeGet_cons, tcListGetZ]
  | x :: xs, k + 1 => by
      simp [tcZTreeOfList, tcZTreeGet_cons, tcZTreeGet_ofList xs k, tcListGetZ]
/-- WHNF-forced `10^12`-scaled self-convolution lower bound on `0.. 2 * maxW`. -/
def tcConvSquareListLb (maxW : ℕ) (lst : List ℤ) : List ℤ :=
  tcForceZTree (tcZTreeOfList lst) fun tree ↦
    tcWithForcedZList
      (List.ofFn fun h : Fin (2 * maxW + 1) ↦
        Int.ediv
          (tcSumRangeZ
            (fun i ↦
              if i ≤ h.val ∧ h.val - i ≤ maxW then
                Int.mul (tcZTreeGet tree i) (tcZTreeGet tree (h.val - i))
              else Int.ofNat 0)
            (maxW + 1))
          tcScalePrim)
      id
theorem tcFinset_sum_div {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]
theorem tcConvSquareListLb_sound {maxW : ℕ} {p : ℕ → ℝ} {lst : List ℤ} (hlst : ∀ i ≤ maxW, 0 ≤
    tcListGetZ lst i ∧ (tcListGetZ lst i : ℝ) / (tcScale : ℝ) ≤ p i) : ∀ h ≤ 2 * maxW, 0 ≤
    tcListGetZ (tcConvSquareListLb maxW lst) h ∧ (tcListGetZ (tcConvSquareListLb maxW lst) h : ℝ) /
    (tcScale : ℝ) ≤ tcConvReal maxW maxW p p h := by
  intro h hh; have hS_pos : (0 : ℤ) < tcScale := tcScale_pos
  have hS : (0 : ℝ) < (tcScale : ℝ) := tcScale_pos_real; have hh_lt : h < 2 * maxW + 1 := (by omega)
  unfold tcConvSquareListLb
  rw [tcForceZTree_eq, tcWithForcedZList_eq, id_eq, tcListGetZ_ofFn _ h hh_lt]
  simp only [tcZTreeGet_ofList, tcInt_ediv_eq, tcInt_mul_eq, tcInt_ofNat_eq, Nat.cast_zero,
    tcScalePrim_eq]
  set f : ℕ → ℤ := fun i ↦
    if i ≤ h ∧ h - i ≤ maxW then tcListGetZ lst i * tcListGetZ lst (h - i) else 0
  have hf_nn : ∀ i < maxW + 1, 0 ≤ f i := by
    intro i hi; dsimp [f]; split_ifs with hcond
    · exact mul_nonneg (hlst i (by omega)).1 (hlst (h - i) hcond.2).1
    · exact le_rfl
  have hsum_nn := tcSumRangeZ_nonneg hf_nn; refine ⟨Int.ediv_nonneg hsum_nn hS_pos.le, ?_⟩
  have hd := div_le_div_of_nonneg_right (tc_ediv_pos_le_real (tcSumRangeZ f (maxW + 1))
    tcScale hS_pos) hS.le
  rw [tcSumRangeZ_eq] at hd
  have hsum_le : (∑ i ∈ Finset.range (maxW + 1), (f i : ℝ)) / (tcScale : ℝ) / (tcScale : ℝ) ≤
      tcConvReal maxW maxW p p h := by
    rw [div_div, tcFinset_sum_div]; unfold tcConvReal; refine Finset.sum_le_sum fun i hi ↦ ?_
    dsimp [f]; split_ifs with hcond
    · have hi_le : i ≤ maxW := (by simp [Finset.mem_range] at hi; omega)
      rcases hlst i hi_le with ⟨hi0, hi_p⟩; rcases hlst (h - i) hcond.2 with ⟨hj0, hj_p⟩
      have hrew : ((tcListGetZ lst i * tcListGetZ lst (h - i) : ℤ) : ℝ) / ((tcScale : ℝ) * (tcScale
        : ℝ)) = ((tcListGetZ lst i : ℝ) / (tcScale : ℝ)) * ((tcListGetZ lst (h - i) : ℝ) / (tcScale
        : ℝ)) := by
        push_cast; rw [div_mul_div_comm]
      rw [hrew]; have hi0_r : (0 : ℝ) ≤ (tcListGetZ lst i : ℝ) := (by exact_mod_cast hi0)
      have hj0_r : (0 : ℝ) ≤ (tcListGetZ lst (h - i) : ℝ) := (by exact_mod_cast hj0)
      exact mul_le_mul hi_p hj_p (div_nonneg hj0_r hS.le) ((div_nonneg hi0_r hS.le).trans hi_p)
    · simp
  exact hd.trans hsum_le
/-- WHNF-forced `e`-squaring `List ℤ` memoized lower bound for `m = 2^e` parallel slots. -/
def tcConvPow2ListLb (d : ℕ) (wProbLb : ℕ → ℤ) : ℕ → List ℤ
  | 0 => tcWithForcedZList (List.ofFn fun w : Fin (d + 1) ↦ wProbLb w.val) id
  | e + 1 => tcConvSquareListLb (2 ^ e * d) (tcConvPow2ListLb d wProbLb e)
/-- Certificate checker for precomputed `m = 2^e` convolution lower bounds `convLb`. -/
def tcCheckConvPow2 (e d : ℕ) (wProbLb convLb : ℕ → ℤ) : Bool :=
  tcForceZTree (tcZTreeOfList (tcConvPow2ListLb d wProbLb e)) fun tree ↦
    allRange
      (fun h ↦ bleZ (Int.ofNat 0) (convLb h) && bleZ (convLb h) (tcZTreeGet tree h))
      (2 ^ e * d + 1)
theorem tcCheckConvPow2_sound {e d : ℕ} {p : ℕ → ℝ} {wProbLb convLb : ℕ → ℤ} (hw : ∀ w ≤ d, 0 ≤
    wProbLb w ∧ (wProbLb w : ℝ) / (tcScale : ℝ) ≤ p w) (hchk : tcCheckConvPow2 e d wProbLb convLb =
    true) : ∀ h ≤ 2 ^ e * d, 0 ≤ convLb h ∧ (convLb h : ℝ) / (tcScale : ℝ) ≤ tcConvPow2Real d p e
    h := by
  have hiter : ∀ k : ℕ, ∀ h ≤ 2 ^ k * d, 0 ≤ tcListGetZ (tcConvPow2ListLb d wProbLb k) h ∧
    (tcListGetZ (tcConvPow2ListLb d wProbLb k) h : ℝ) / (tcScale : ℝ) ≤ tcConvPow2Real d p k h := by
    intro k
    induction k with
    | zero =>
        intro h hh; simp only [pow_zero, one_mul] at hh; unfold tcConvPow2ListLb tcConvPow2Real
        rw [tcWithForcedZList_eq, id_eq, tcListGetZ_ofFn _ h (by omega)]; exact hw h hh
    | succ k ih =>
        intro h hh; have hrew : 2 ^ (k + 1) * d = 2 * (2 ^ k * d) := (by ring)
        rw [hrew] at hh; unfold tcConvPow2ListLb tcConvPow2Real
        exact tcConvSquareListLb_sound ih h hh
  unfold tcCheckConvPow2 at hchk; rw [tcForceZTree_eq] at hchk
  simp only [tcZTreeGet_ofList] at hchk; intro h hh; have hh_lt : h < 2 ^ e * d + 1 := (by omega)
  have hc := of_allRange (p := fun h' ↦ bleZ (Int.ofNat 0) (convLb h') && bleZ (convLb h')
    (tcListGetZ (tcConvPow2ListLb d wProbLb e) h')) hchk hh_lt
  simp only [Bool.and_eq_true, bleZ_eq_true_iff, tcInt_ofNat_eq, Nat.cast_zero] at hc
  refine ⟨hc.1, ?_⟩
  have hcast_c : (convLb h : ℝ) ≤ (tcListGetZ (tcConvPow2ListLb d wProbLb e) h : ℝ) := by
    exact_mod_cast hc.2
  have hle := div_le_div_of_nonneg_right hcast_c tcScale_pos_real.le
  exact hle.trans (hiter e h hh).2
/-- Exact real tail probability `P(distinct ≥ s | h uniform draws from R)` for `|R| = r`. -/
noncomputable def tcCouponTailReal (r : ℕ) : ℕ → ℕ → ℝ
  | 0, s => if s = 0 then 1 else 0
  | h + 1, s =>
      if s = 0 then 1
      else if s ≤ r then
        (((s - 1 : ℕ) : ℝ) / (r : ℝ)) * tcCouponTailReal r h s +
          (((r + 1 - s : ℕ) : ℝ) / (r : ℝ)) * tcCouponTailReal r h (s - 1)
      else 0
theorem tcCouponTailReal_bounds {r : ℕ} (hr : 1 ≤ r) (h s : ℕ) :
    0 ≤ tcCouponTailReal r h s ∧ tcCouponTailReal r h s ≤ 1 := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by positivity)
  induction h generalizing s with
  | zero => unfold tcCouponTailReal; by_cases hs : s = 0 <;> simp [hs]
  | succ h ih =>
      unfold tcCouponTailReal; by_cases hs0 : s = 0
      · simp [hs0]
      · simp only [hs0, ↓reduceIte]; by_cases hsr : s ≤ r
        · simp only [hsr, ↓reduceIte]; rcases ih s with ⟨h1_lo, h1_hi⟩
          rcases ih (s - 1) with ⟨h2_lo, h2_hi⟩
          have hc1 : 0 ≤ ((s - 1 : ℕ) : ℝ) / (r : ℝ) := (by positivity)
          have hc2 : 0 ≤ ((r + 1 - s : ℕ) : ℝ) / (r : ℝ) := (by positivity)
          have hsum1 : ((s - 1 : ℕ) : ℝ) / (r : ℝ) + ((r + 1 - s : ℕ) : ℝ) / (r : ℝ) = 1 := by
            rw [← add_div, div_eq_one_iff_eq hr_pos.ne']
            have hnat : (s - 1) + (r + 1 - s) = r := (by omega); exact_mod_cast hnat
          constructor
          · positivity
          · nlinarith
        · simp [hsr]
theorem tcCouponTailReal_antitone_succ {r : ℕ} (hr : 1 ≤ r) (h s : ℕ) :
    tcCouponTailReal r h (s + 1) ≤ tcCouponTailReal r h s := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by positivity)
  induction h generalizing s with
  | zero => unfold tcCouponTailReal; by_cases hs0 : s = 0 <;> simp [hs0]
  | succ h ih =>
      by_cases hs0 : s = 0
      · subst hs0
        have hb := (tcCouponTailReal_bounds hr (h + 1) 1).2; simpa [tcCouponTailReal] using hb
      · by_cases hsr1 : s + 1 ≤ r
        · have hsr : s ≤ r := (by omega)
          have h_lo : tcCouponTailReal r h s ≤ tcCouponTailReal r (h + 1) s := by
            conv_rhs => rw [tcCouponTailReal]
            simp only [hs0, hsr, ↓reduceIte]; have hprev := ih (s - 1)
            rw [show s - 1 + 1 = s by omega] at hprev
            have hc2 : 0 ≤ ((r + 1 - s : ℕ) : ℝ) / (r : ℝ) := (by positivity)
            have hsum1 : ((s - 1 : ℕ) : ℝ) / (r : ℝ) + ((r + 1 - s : ℕ) : ℝ) / (r : ℝ) = 1 := by
              rw [← add_div, div_eq_one_iff_eq hr_pos.ne']
              exact_mod_cast (show (s - 1) + (r + 1 - s) = r by omega)
            have hmul := mul_le_mul_of_nonneg_left hprev hc2
            have hid : (((s - 1 : ℕ) : ℝ) / (r : ℝ)) * tcCouponTailReal r h s + (((r + 1 - s : ℕ) :
              ℝ) / (r : ℝ)) * tcCouponTailReal r h s = tcCouponTailReal r h s := by
              linear_combination hsum1 * tcCouponTailReal r h s
            linarith
          have h_hi : tcCouponTailReal r (h + 1) (s + 1) ≤ tcCouponTailReal r h s := by
            conv_lhs => rw [tcCouponTailReal]
            simp only [Nat.succ_ne_zero, hsr1, ↓reduceIte, Nat.add_sub_cancel]; have hnext := ih s
            have hc1 : 0 ≤ (s : ℝ) / (r : ℝ) := (by positivity)
            have hsum1 : (s : ℝ) / (r : ℝ) + ((r + 1 - (s + 1) : ℕ) : ℝ) / (r : ℝ) = 1 := by
              rw [← add_div, div_eq_one_iff_eq hr_pos.ne']
              exact_mod_cast (show s + (r + 1 - (s + 1)) = r by omega)
            have hmul := mul_le_mul_of_nonneg_left hnext hc1
            have hid : ((s : ℝ) / (r : ℝ)) * tcCouponTailReal r h s + (((r + 1 - (s + 1) : ℕ) : ℝ) /
              (r : ℝ)) * tcCouponTailReal r h s = tcCouponTailReal r h s := by
              linear_combination hsum1 * tcCouponTailReal r h s
            linarith
          exact h_hi.trans h_lo
        · have h0 : tcCouponTailReal r (h + 1) (s + 1) = 0 := by
            unfold tcCouponTailReal; simp [hsr1]
          rw [h0]; exact (tcCouponTailReal_bounds hr (h + 1) s).1
theorem tcCouponTailReal_mono_r {rMin r : ℕ} (hrMin : 1 ≤ rMin) (hle : rMin ≤ r) (h s : ℕ) :
    tcCouponTailReal rMin h s ≤ tcCouponTailReal r h s := by
  have hr1 : 1 ≤ r := hrMin.trans hle; have hrMin_pos : (0 : ℝ) < (rMin : ℝ) := (by positivity)
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by positivity)
  induction h generalizing s with
  | zero => rfl
  | succ h ih =>
      by_cases hs0 : s = 0
      · simp [tcCouponTailReal, hs0]
      · by_cases hsm : s ≤ rMin
        · have hsr : s ≤ r := hsm.trans hle; unfold tcCouponTailReal
          simp only [hs0, hsm, hsr, ↓reduceIte]
          have hanti : tcCouponTailReal rMin h s ≤ tcCouponTailReal rMin h (s - 1) := by
            have ha := tcCouponTailReal_antitone_succ hrMin h (s - 1)
            rwa [show s - 1 + 1 = s by omega] at ha
          have hsum_min :
              ((s - 1 : ℕ) : ℝ) / (rMin : ℝ) + ((rMin + 1 - s : ℕ) : ℝ) / (rMin : ℝ) = 1 := by
            rw [← add_div, div_eq_one_iff_eq hrMin_pos.ne']
            exact_mod_cast (show (s - 1) + (rMin + 1 - s) = rMin by omega)
          have hsum_r : ((s - 1 : ℕ) : ℝ) / (r : ℝ) + ((r + 1 - s : ℕ) : ℝ) / (r : ℝ) = 1 := by
            rw [← add_div, div_eq_one_iff_eq hr_pos.ne']
            exact_mod_cast (show (s - 1) + (r + 1 - s) = r by omega)
          have hdiv_le : ((s - 1 : ℕ) : ℝ) / (r : ℝ) ≤ ((s - 1 : ℕ) : ℝ) / (rMin : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hrMin_pos (by exact_mod_cast hle)
          have hstep1 : (((s - 1 : ℕ) : ℝ) / (rMin : ℝ)) * tcCouponTailReal rMin h s + (((rMin + 1 -
            s : ℕ) : ℝ) / (rMin : ℝ)) * tcCouponTailReal rMin h (s - 1) ≤ (((s - 1 : ℕ) : ℝ) / (r :
            ℝ)) * tcCouponTailReal rMin h s + (((r + 1 - s : ℕ) : ℝ) / (r : ℝ)) * tcCouponTailReal
            rMin h (s - 1) := by
            set u := tcCouponTailReal rMin h s; set v := tcCouponTailReal rMin h (s - 1)
            have hid_min : (((s - 1 : ℕ) : ℝ) / (rMin : ℝ)) * u + (((rMin + 1 - s : ℕ) : ℝ) / (rMin
              : ℝ)) * v = v - (((s - 1 : ℕ) : ℝ) / (rMin : ℝ)) * (v - u) := by
              linear_combination hsum_min * v
            have hid_r : (((s - 1 : ℕ) : ℝ) / (r : ℝ)) * u + (((r + 1 - s : ℕ) : ℝ) / (r : ℝ)) * v =
                v - (((s - 1 : ℕ) : ℝ) / (r : ℝ)) * (v - u) := by
              linear_combination hsum_r * v
            have hmul_uv := mul_le_mul_of_nonneg_right hdiv_le (sub_nonneg.mpr hanti); linarith
          have hc1 : 0 ≤ ((s - 1 : ℕ) : ℝ) / (r : ℝ) := (by positivity)
          have hc2 : 0 ≤ ((r + 1 - s : ℕ) : ℝ) / (r : ℝ) := (by positivity)
          have hstep2 : (((s - 1 : ℕ) : ℝ) / (r : ℝ)) * tcCouponTailReal rMin h s + (((r + 1 - s :
            ℕ) : ℝ) / (r : ℝ)) * tcCouponTailReal rMin h (s - 1) ≤ (((s - 1 : ℕ) : ℝ) / (r : ℝ)) *
            tcCouponTailReal r h s + (((r + 1 - s : ℕ) : ℝ) / (r : ℝ)) * tcCouponTailReal r h (s -
            1) := add_le_add (mul_le_mul_of_nonneg_left (ih s) hc1) (mul_le_mul_of_nonneg_left (ih
            (s - 1)) hc2)
          exact hstep1.trans hstep2
        · have h0 : tcCouponTailReal rMin (h + 1) s = 0 := by
            unfold tcCouponTailReal; simp [hs0, hsm]
          rw [h0]; exact (tcCouponTailReal_bounds hr1 (h + 1) s).1
/-- Initial `10^12`-scaled coupon tail row `[tcScale, 0,..., 0]` at `h = 0`. -/
def tcCouponInitRowLb (sMax : ℕ) : List ℤ :=
  List.ofFn fun s : Fin (sMax + 1) ↦ if s.val == 0 then tcScale else 0
theorem tcCouponInitRowLb_sound (rMin sMax : ℕ) : ∀ s ≤ sMax, 0 ≤ tcListGetZ (tcCouponInitRowLb
    sMax) s ∧ (tcListGetZ (tcCouponInitRowLb sMax) s : ℝ) / (tcScale : ℝ) ≤ tcCouponTailReal rMin 0
    s := by
  intro s hs; have hS_pos : (0 : ℤ) < tcScale := tcScale_pos
  have hS : (0 : ℝ) < (tcScale : ℝ) := tcScale_pos_real; unfold tcCouponInitRowLb tcCouponTailReal
  rw [tcListGetZ_ofFn _ s (by omega)]; by_cases hs0 : s = 0
  · subst hs0; simp [hS_pos.le, div_self hS.ne']
  · have hbeq : (s == 0) = false := beq_false_of_ne hs0; simp [hs0, hbeq]
/-- Tail-recursive `O(1)`-stack list reversal (`l.reverseAux acc`) without re-forcing
  elements. -/
def tcRevList {α : Type*} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => tcRevList xs (x :: acc)
theorem tcRevList_eq {α : Type*} (l acc : List α) : tcRevList l acc = l.reverseAux acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih (x :: acc)
/-- `O(1)` head lookup `tcListGetZ l 0` via direct pattern match. -/
def tcHeadZ : List ℤ → ℤ
  | x :: _ => x
  | [] => Int.ofNat 0
/-- Constructor pattern-match extracting `(tcHeadZ l, l.tail)` with zero `List.tail` thunks. -/
def tcUnconsZ {α : Type*} (l : List ℤ) (k : ℤ → List ℤ → α) : α :=
  match l with
  | [] => k (Int.ofNat 0) []
  | x :: xs => k x xs
theorem tcUnconsZ_eq {α : Type*} (l : List ℤ) (k : ℤ → List ℤ → α) :
    tcUnconsZ l k = k (tcHeadZ l) l.tail := by
  cases l <;> rfl
theorem tcHeadZ_eq (l : List ℤ) : tcHeadZ l = tcListGetZ l 0 := by
  cases l <;> simp [tcHeadZ, tcListGetZ]
theorem tcListGetZ_tail (l : List ℤ) (k : ℕ) : tcListGetZ l.tail k = tcListGetZ l (k + 1) := by
  cases l <;> simp [tcListGetZ]
theorem tcHeadZ_tail (l : List ℤ) : tcHeadZ l.tail = tcListGetZ l 1 := by
  rw [tcHeadZ_eq, tcListGetZ_tail, Nat.zero_add]
/-- Tail-recursive `O(1)`-stack zero-thunk linear scan for `tcCouponNextRowLb`. -/
def tcCouponNextRev (rMin : ℕ) : ℕ → ℕ → List ℤ → List ℤ → List ℤ
  | 0, _, _, acc => acc
  | rem + 1, s0, rowL, acc =>
      tcUnconsZ rowL fun r0 rest ↦
        let r1 := tcHeadZ rest
        let v := Int.ediv
          (Int.add (Int.mul (Int.ofNat s0) r1)
            (Int.mul (Int.ofNat (Nat.sub rMin s0)) r0))
          (Int.ofNat rMin)
        tcWithForcedInt v fun v' ↦
          tcForceNat (Nat.add s0 1) fun s1 ↦
            tcCouponNextRev rMin rem s1 rest (v' :: acc)
theorem tcCouponNextRev_eq (rMin : ℕ) :
    ∀ (rem s0 : ℕ) (rowL acc : List ℤ),
      tcCouponNextRev rMin rem s0 rowL acc =
        (List.ofFn fun j : Fin rem ↦
          (((s0 + j.val : ℕ) : ℤ) * tcListGetZ rowL (j.val + 1) +
            ((rMin - (s0 + j.val) : ℕ) : ℤ) * tcListGetZ rowL j.val) / (rMin : ℤ)).reverseAux acc
  | 0, _, _, acc => by simp [tcCouponNextRev]
  | rem + 1, s0, rowL, acc => by
      unfold tcCouponNextRev
      rw [tcUnconsZ_eq]
      dsimp only
      rw [tcHeadZ_tail, tcHeadZ_eq]
      simp only [tcWithForcedInt_eq, tcForceNat_eq, tcInt_ediv_eq, tcInt_add_eq, tcInt_mul_eq,
        tcInt_ofNat_eq]
      change tcCouponNextRev rMin rem (s0 + 1) rowL.tail _ = _
      rw [tcCouponNextRev_eq rMin rem (s0 + 1) rowL.tail, List.ofFn_succ, List.reverseAux]
      simp only [Fin.val_zero, Nat.add_zero, Nat.zero_add]
      refine congrArg (fun xs ↦ List.reverseAux xs _) (congrArg List.ofFn ?_)
      funext j
      rw [Fin.val_succ, tcListGetZ_tail, tcListGetZ_tail,
        show s0 + 1 + j.val = s0 + (j.val + 1) by omega]
/-- WHNF-forced one-draw Markov coupon tail transition lower bound at `rMin` (`O(sMax)`
  linear). -/
def tcCouponNextRowLb (rMin sMax : ℕ) (row : List ℤ) : List ℤ :=
  tcWithForcedInt tcScalePrim fun sc ↦
    tcRevList (tcCouponNextRev rMin sMax 0 row [sc]) []
theorem tcCouponNextRowLb_eq_ofFn (rMin sMax : ℕ) (row : List ℤ) : tcCouponNextRowLb rMin sMax row =
    List.ofFn fun s : Fin (sMax + 1) ↦ if s.val == 0 then tcScale else (((s.val - 1 : ℕ) : ℤ) *
    tcListGetZ row s.val + ((rMin + 1 - s.val : ℕ) : ℤ) * tcListGetZ row (s.val - 1)) / (rMin :
    ℤ) := by
  unfold tcCouponNextRowLb
  rw [tcWithForcedInt_eq, tcScalePrim_eq, tcRevList_eq, tcCouponNextRev_eq]
  simp only [Nat.zero_add]
  set rhs := tcScale :: List.ofFn fun j : Fin sMax ↦ (((j.val : ℕ) : ℤ) * tcListGetZ row (j.val +
    1) + ((rMin - j.val : ℕ) : ℤ) * tcListGetZ row j.val) / (rMin : ℤ)
  have hfn : (List.ofFn fun s : Fin (sMax + 1) ↦ if s.val == 0 then tcScale else (((s.val - 1 : ℕ) :
    ℤ) * tcListGetZ row s.val + ((rMin + 1 - s.val : ℕ) : ℤ) * tcListGetZ row (s.val - 1)) / (rMin :
    ℤ)) = rhs := by
    dsimp only [rhs]; rw [List.ofFn_succ]
    refine congrArg₂ List.cons (by simp) (congrArg List.ofFn ?_)
    funext j; have hj_ne : (j.succ.val == 0) = false := (by simp [Fin.val_succ])
    have h1 : j.val + 1 - 1 = j.val := Nat.add_sub_cancel j.val 1
    have h2 : rMin + 1 - (j.val + 1) = rMin - j.val := Nat.add_sub_add_right rMin 1 j.val
    rw [hj_ne]; simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_succ, h1, h2]
  rw [hfn]; exact List.reverse_reverse rhs
theorem tcCouponNextRowLb_sound {rMin sMax h : ℕ} {row : List ℤ} (hrMin : 1 ≤ rMin) (hsMax : sMax ≤
    rMin) (hrow : ∀ s ≤ sMax, 0 ≤ tcListGetZ row s ∧ (tcListGetZ row s : ℝ) / (tcScale : ℝ) ≤
    tcCouponTailReal rMin h s) : ∀ s ≤ sMax, 0 ≤ tcListGetZ (tcCouponNextRowLb rMin sMax row) s ∧
    (tcListGetZ (tcCouponNextRowLb rMin sMax row) s : ℝ) / (tcScale : ℝ) ≤ tcCouponTailReal rMin
    (h + 1) s := by
  intro s hs; have hS_pos : (0 : ℤ) < tcScale := tcScale_pos
  have hS : (0 : ℝ) < (tcScale : ℝ) := tcScale_pos_real
  have hr_pos_z : (0 : ℤ) < (rMin : ℤ) := (by exact_mod_cast (show 0 < rMin by omega))
  have hr_pos : (0 : ℝ) < (rMin : ℝ) := (by positivity)
  rw [tcCouponNextRowLb_eq_ofFn, tcListGetZ_ofFn _ s (by omega)]; by_cases hs0 : s = 0
  · subst hs0; simp [tcCouponTailReal, hS_pos.le, div_self hS.ne']
  · have hbeq : (s == 0) = false := beq_false_of_ne hs0; have hsr : s ≤ rMin := hs.trans hsMax
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]; rcases hrow s hs with ⟨h1_nn, h1_le⟩
    rcases hrow (s - 1) (by omega) with ⟨h2_nn, h2_le⟩
    set num : ℤ := ((s - 1 : ℕ) : ℤ) * tcListGetZ row s +
        ((rMin + 1 - s : ℕ) : ℤ) * tcListGetZ row (s - 1)
    have hnum_nn : 0 ≤ num := by
      dsimp [num]; exact add_nonneg (mul_nonneg (Int.natCast_nonneg _) h1_nn)
        (mul_nonneg (Int.natCast_nonneg _) h2_nn)
    refine ⟨Int.ediv_nonneg hnum_nn hr_pos_z.le, ?_⟩
    have hd := div_le_div_of_nonneg_right (tc_ediv_pos_le_real num (rMin : ℤ) hr_pos_z) hS.le
    unfold tcCouponTailReal; simp only [hs0, hsr, ↓reduceIte]
    have hrew : (num : ℝ) / ((rMin : ℤ) : ℝ) / (tcScale : ℝ) = (((s - 1 : ℕ) : ℝ) / (rMin : ℝ)) *
      ((tcListGetZ row s : ℝ) / (tcScale : ℝ)) + (((rMin + 1 - s : ℕ) : ℝ) / (rMin : ℝ)) *
      ((tcListGetZ row (s - 1) : ℝ) / (tcScale : ℝ)) := by
      dsimp [num]; push_cast; field_simp [hr_pos.ne', hS.ne']
    rw [hrew] at hd; have hc1 : 0 ≤ ((s - 1 : ℕ) : ℝ) / (rMin : ℝ) := (by positivity)
    have hc2 : 0 ≤ ((rMin + 1 - s : ℕ) : ℝ) / (rMin : ℝ) := (by positivity)
    exact hd.trans (add_le_add (mul_le_mul_of_nonneg_left h1_le hc1)
      (mul_le_mul_of_nonneg_left h2_le hc2))
/-- Tail-recursive `O(1)`-stack linear scan accumulating `acc + (ch * row) / tcScale`. -/
def tcCouponAccRev (ch : ℤ) : ℕ → List ℤ → List ℤ → List ℤ → List ℤ
  | 0, _, _, out => out
  | rem + 1, accL, rowL, out =>
      tcUnconsZ accL fun a0 aRest ↦
        tcUnconsZ rowL fun r0 rRest ↦
          let v := Int.add a0 (Int.ediv (Int.mul ch r0) tcScalePrim)
          tcWithForcedInt v fun v' ↦
            tcCouponAccRev ch rem aRest rRest (v' :: out)
theorem tcCouponAccRev_eq (ch : ℤ) :
    ∀ (rem : ℕ) (accL rowL out : List ℤ),
      tcCouponAccRev ch rem accL rowL out =
        (List.ofFn fun j : Fin rem ↦
          tcListGetZ accL j.val + (ch * tcListGetZ rowL j.val) / tcScale).reverseAux out
  | 0, _, _, out => by simp [tcCouponAccRev]
  | rem + 1, accL, rowL, out => by
      unfold tcCouponAccRev
      rw [tcUnconsZ_eq, tcUnconsZ_eq]
      dsimp only
      simp only [tcHeadZ_eq, tcWithForcedInt_eq, tcInt_add_eq, tcInt_ediv_eq, tcInt_mul_eq,
        tcScalePrim_eq]
      rw [tcCouponAccRev_eq ch rem accL.tail rowL.tail, List.ofFn_succ, List.reverseAux]
      simp only [Fin.val_zero]
      refine congrArg (fun xs ↦ List.reverseAux xs _) (congrArg List.ofFn ?_)
      funext j
      rw [Fin.val_succ, tcListGetZ_tail, tcListGetZ_tail]
/-- WHNF-forced `O(sMax)` linear update `acc_s + (ch * row_s) / tcScale` for `0 ≤ s ≤ sMax`. -/
def tcCouponAccNext (sMax : ℕ) (ch : ℤ) (accF rowF : List ℤ) : List ℤ :=
  tcRevList (tcCouponAccRev ch (sMax + 1) accF rowF []) []
theorem tcCouponAccNext_eq_ofFn (sMax : ℕ) (ch : ℤ) (accF rowF : List ℤ) : tcCouponAccNext sMax ch
    accF rowF = List.ofFn fun s : Fin (sMax + 1) ↦ tcListGetZ accF s.val + (ch * tcListGetZ rowF
    s.val) / tcScale := by
  unfold tcCouponAccNext; rw [tcRevList_eq, tcCouponAccRev_eq]
  set rhs := List.ofFn fun s : Fin (sMax + 1) ↦ tcListGetZ accF s.val + (ch * tcListGetZ rowF s.val)
    / tcScale; exact List.reverse_reverse rhs
/-- Pure reference recurrence for `tcCouponBucketRun` (`0.. cnt - 1`). -/
noncomputable def tcCouponBucketSpec (rMin sMax : ℕ) (convLb : ℕ → ℤ) : ℕ → List ℤ × List ℤ
  | 0 =>
      (tcCouponInitRowLb sMax, List.ofFn fun _ : Fin (sMax + 1) ↦ (0 : ℤ))
  | h + 1 =>
      let prev := tcCouponBucketSpec rMin sMax convLb h
      (tcCouponNextRowLb rMin sMax prev.1,
        tcCouponAccNext sMax (convLb h) prev.2 prev.1)
/-- Tail-recursive `O(1)`-stack loop running coupon-occupancy steps `h0.. h0 + rem - 1`. -/
def tcCouponBucketLoop (rMin sMax : ℕ) (convLb : ℕ → ℤ) :
    ℕ → ℕ → List ℤ → List ℤ → List ℤ × List ℤ
  | 0, _, row, acc => (row, acc)
  | rem + 1, h0, row, acc =>
      tcWithForcedInt (convLb h0) fun ch ↦
        tcForceListSpine (tcCouponNextRowLb rMin sMax row) fun rowNext ↦
          tcForceListSpine (tcCouponAccNext sMax ch acc row) fun accNext ↦
            tcForceNat (h0 + 1) fun h1 ↦
              tcCouponBucketLoop rMin sMax convLb rem h1 rowNext accNext
theorem tcCouponBucketLoop_eq_spec (rMin sMax : ℕ) (convLb : ℕ → ℤ) :
    ∀ (rem h0 : ℕ) (row acc : List ℤ),
      (row, acc) = tcCouponBucketSpec rMin sMax convLb h0 →
      tcCouponBucketLoop rMin sMax convLb rem h0 row acc =
        tcCouponBucketSpec rMin sMax convLb (h0 + rem)
  | 0, _, _, _, hinit => hinit
  | rem + 1, h0, row, acc, hinit => by
      unfold tcCouponBucketLoop
      simp only [tcWithForcedInt_eq, tcForceListSpine_eq, tcForceNat_eq]
      rw [show h0 + (rem + 1) = (h0 + 1) + rem by omega]
      apply tcCouponBucketLoop_eq_spec rMin sMax convLb rem (h0 + 1)
      have h1 : row = (tcCouponBucketSpec rMin sMax convLb h0).1 := congrArg Prod.fst hinit
      have h2 : acc = (tcCouponBucketSpec rMin sMax convLb h0).2 := congrArg Prod.snd hinit
      unfold tcCouponBucketSpec
      dsimp only
      rw [← h1, ← h2]
/-- One-pass tail-recursive WHNF-forced `(row_h, acc_h)` accumulator over `0.. cnt - 1`. -/
def tcCouponBucketRun (rMin sMax : ℕ) (convLb : ℕ → ℤ) (cnt : ℕ) : List ℤ × List ℤ :=
  tcForceListSpine (tcWithForcedZList (tcCouponInitRowLb sMax) id) fun row0 ↦
    tcForceListSpine
      (tcWithForcedZList (List.ofFn fun _ : Fin (sMax + 1) ↦ (0 : ℤ)) id) fun acc0 ↦
      tcCouponBucketLoop rMin sMax convLb cnt 0 row0 acc0
theorem tcCouponBucketRun_eq_spec (rMin sMax : ℕ) (convLb : ℕ → ℤ) (cnt : ℕ) :
    tcCouponBucketRun rMin sMax convLb cnt = tcCouponBucketSpec rMin sMax convLb cnt := by
  unfold tcCouponBucketRun; simp only [tcForceListSpine_eq, tcWithForcedZList_eq, id_eq]
  rw [tcCouponBucketLoop_eq_spec rMin sMax convLb cnt 0 _ _ rfl, Nat.zero_add]
theorem tcCouponBucketRun_sound {rMin sMax : ℕ} {pConv : ℕ → ℝ} {convLb : ℕ → ℤ} (cnt : ℕ) (hrMin :
    1 ≤ rMin) (hsMax : sMax ≤ rMin) (hconv : ∀ h < cnt, 0 ≤ convLb h ∧ (convLb h : ℝ) / (tcScale :
    ℝ) ≤ pConv h) : ∀ s ≤ sMax, (0 ≤ tcListGetZ (tcCouponBucketRun rMin sMax convLb cnt).1 s ∧
    (tcListGetZ (tcCouponBucketRun rMin sMax convLb cnt).1 s : ℝ) / (tcScale : ℝ) ≤ tcCouponTailReal
    rMin cnt s) ∧ (tcListGetZ (tcCouponBucketRun rMin sMax convLb cnt).2 s : ℝ) / (tcScale : ℝ) ≤ ∑
    h ∈ Finset.range cnt, pConv h * tcCouponTailReal rMin h s := by
  rw [tcCouponBucketRun_eq_spec]; have hS_pos : (0 : ℤ) < tcScale := tcScale_pos
  have hS : (0 : ℝ) < (tcScale : ℝ) := tcScale_pos_real
  induction cnt with
  | zero =>
      intro s hs; unfold tcCouponBucketSpec; dsimp only
      refine ⟨tcCouponInitRowLb_sound rMin sMax s hs, ?_⟩
      rw [tcListGetZ_ofFn _ s (by omega), Finset.sum_range_zero]; simp
  | succ h ih =>
      intro s hs; have hprev := ih fun i hi ↦ hconv i (by omega)
      unfold tcCouponBucketSpec; dsimp only; set row := (tcCouponBucketSpec rMin sMax convLb h).1
      set acc := (tcCouponBucketSpec rMin sMax convLb h).2
      have hrow_all : ∀ j ≤ sMax, 0 ≤ tcListGetZ row j ∧ (tcListGetZ row j : ℝ) / (tcScale : ℝ) ≤
        tcCouponTailReal rMin h j := fun j hj ↦ (hprev j hj).1
      refine ⟨tcCouponNextRowLb_sound hrMin hsMax hrow_all s hs, ?_⟩
      rw [tcCouponAccNext_eq_ofFn, tcListGetZ_ofFn _ s (by omega),
        Finset.sum_range_succ, Int.cast_add, add_div]
      rcases hconv h (by omega) with ⟨hch_nn, hch_le⟩; rcases hrow_all s hs with ⟨hrs_nn, hrs_le⟩
      have hd := div_le_div_of_nonneg_right
        (tc_ediv_pos_le_real (convLb h * tcListGetZ row s) tcScale hS_pos) hS.le
      have hrew : ((convLb h * tcListGetZ row s : ℤ) : ℝ) / (tcScale : ℝ) / (tcScale : ℝ) =
          ((convLb h : ℝ) / (tcScale : ℝ)) * ((tcListGetZ row s : ℝ) / (tcScale : ℝ)) := by
        push_cast; rw [div_div, div_mul_div_comm]
      rw [hrew] at hd; have hrs_r : (0 : ℝ) ≤ (tcListGetZ row s : ℝ) := (by exact_mod_cast hrs_nn)
      have hch_r : (0 : ℝ) ≤ (convLb h : ℝ) := (by exact_mod_cast hch_nn)
      have hterm : ((convLb h : ℝ) / (tcScale : ℝ)) * ((tcListGetZ row s : ℝ) / (tcScale : ℝ)) ≤
          pConv h * tcCouponTailReal rMin h s :=
        mul_le_mul hch_le hrs_le (div_nonneg hrs_r hS.le) ((div_nonneg hch_r hS.le).trans hch_le)
      exact add_le_add (hprev s hs).2 (hd.trans hterm)
/-- Linear `O(sMax)` tail-bound scan checking `s = s0.. s0 + rem - 1` against `accL`. -/
def tcCheckCouponTailScan (tailLb : ℕ → ℤ) : ℕ → ℕ → List ℤ → Bool
  | 0, _, _ => true
  | rem + 1, s0, accL =>
      tcUnconsZ accL fun a0 aRest ↦
        tcWithForcedInt (tailLb s0) fun ts ↦
          (beqZ ts (Int.ofNat 0) ||
            (bltZ (Int.ofNat 0) ts && bleZ (Int.add ts (Int.ofNat 1)) a0)) &&
          tcForceNat (Nat.add s0 1) fun s1 ↦
            tcCheckCouponTailScan tailLb rem s1 aRest
theorem tcCheckCouponTailScan_iff (tailLb : ℕ → ℤ) :
    ∀ (rem s0 : ℕ) (accL : List ℤ),
      tcCheckCouponTailScan tailLb rem s0 accL = true ↔
        ∀ j < rem,
          tailLb (s0 + j) = 0 ∨
            (0 < tailLb (s0 + j) ∧ tailLb (s0 + j) + 1 ≤ tcListGetZ accL j)
  | 0, _, _ => by simp [tcCheckCouponTailScan]
  | rem + 1, s0, accL => by
      unfold tcCheckCouponTailScan
      rw [tcUnconsZ_eq, tcWithForcedInt_eq]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beqZ_eq_true_iff, bltZ_eq_true_iff,
        bleZ_eq_true_iff, tcInt_add_eq, tcInt_ofNat_eq, Nat.cast_zero, Nat.cast_one, tcForceNat_eq]
      rw [show Nat.add s0 1 = s0 + 1 from rfl,
        tcCheckCouponTailScan_iff tailLb rem (s0 + 1) accL.tail, tcHeadZ_eq]
      constructor
      · rintro ⟨h0, hrest⟩ j hj
        cases j with
        | zero => simpa using h0
        | succ k =>
            have hk := hrest k (by omega)
            rwa [tcListGetZ_tail, show s0 + 1 + k = s0 + (k + 1) by omega] at hk
      · intro hall
        refine ⟨by simpa using hall 0 (by omega), fun k hk ↦ ?_⟩
        have hk' := hall (k + 1) (by omega)
        rwa [tcListGetZ_tail, show s0 + 1 + k = s0 + (k + 1) by omega]
/-- Certificate checker for monotone-in-`r` coupon-occupancy bucket lower bounds `tailLb`. -/
def tcCheckCouponBucket (rMin sMax hMax : ℕ) (convLb tailLb : ℕ → ℤ) : Bool :=
  decide (1 ≤ rMin ∧ 1 ≤ sMax ∧ sMax ≤ rMin) &&
  allRange (fun h ↦ bleZ (Int.ofNat 0) (convLb h)) (hMax + 1) &&
  bleZ (Int.ofNat 1) (tailLb 1) &&
  match tcCouponBucketRun rMin sMax convLb (hMax + 1) with
  | (_, acc) =>
      tcUnconsZ acc fun _ accTail ↦
        tcCheckCouponTailScan tailLb sMax 1 accTail
theorem tcCheckCouponBucket_sound {rMin r sMax hMax : ℕ} {pConv : ℕ → ℝ} {convLb tailLb : ℕ → ℤ} (hr
    : rMin ≤ r) (hconv : ∀ h ≤ hMax, (convLb h : ℝ) / (tcScale : ℝ) ≤ pConv h) (hchk :
    tcCheckCouponBucket rMin sMax hMax convLb tailLb = true) : 1 ≤ rMin ∧ 1 ≤ sMax ∧ sMax ≤ rMin ∧ 1
    ≤ tailLb 1 ∧ ∀ s, 1 ≤ s → s ≤ sMax → 0 ≤ tailLb s ∧ (tailLb s = 0 ∨ ((tailLb s : ℝ) + 1) /
    (tcScale : ℝ) ≤ ∑ h ∈ Finset.range (hMax + 1), pConv h * tcCouponTailReal r h s) := by
  have hS : (0 : ℝ) < (tcScale : ℝ) := tcScale_pos_real; unfold tcCheckCouponBucket at hchk
  rcases heq : tcCouponBucketRun rMin sMax convLb (hMax + 1) with ⟨row, acc⟩
  rw [heq] at hchk; dsimp only at hchk; rw [tcUnconsZ_eq] at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, bleZ_eq_true_iff, tcInt_ofNat_eq,
    Nat.cast_one] at hchk
  rcases hchk with ⟨⟨⟨⟨hrMin, hs1, hsMax⟩, hconv_nn⟩, ht1⟩, htail_all⟩
  have hconv_full : ∀ h < hMax + 1, 0 ≤ convLb h ∧ (convLb h : ℝ) / (tcScale : ℝ) ≤ pConv h := by
    intro h hh; have hnn := of_allRange (p := fun i ↦ bleZ (Int.ofNat 0) (convLb i)) hconv_nn hh
    simp only [bleZ_eq_true_iff, tcInt_ofNat_eq, Nat.cast_zero] at hnn
    exact ⟨hnn, hconv h (by omega)⟩
  have hrun := tcCouponBucketRun_sound (hMax + 1) hrMin hsMax hconv_full; rw [heq] at hrun
  refine ⟨hrMin, hs1, hsMax, ht1, ?_⟩
  intro s hs_lo hs_hi; have hidx : s - 1 < sMax := (by omega)
  have hitem := (tcCheckCouponTailScan_iff tailLb sMax 1 acc.tail).1 htail_all (s - 1) hidx
  rw [tcListGetZ_tail, show 1 + (s - 1) = s by omega, show s - 1 + 1 = s by omega] at hitem
  rcases hitem with hz | ⟨hpos, hplus1⟩
  · exact ⟨by omega, Or.inl hz⟩
  · refine ⟨hpos.le, Or.inr ?_⟩
    have hle_acc : ((tailLb s : ℝ) + 1) / (tcScale : ℝ) ≤
        (tcListGetZ acc s : ℝ) / (tcScale : ℝ) := by
      have hc : ((tailLb s : ℝ) + 1) ≤ (tcListGetZ acc s : ℝ) := (by exact_mod_cast hplus1)
      exact div_le_div_of_nonneg_right hc hS.le
    have hmono_sum : ∑ h ∈ Finset.range (hMax + 1), pConv h * tcCouponTailReal rMin h s ≤ ∑ h ∈
      Finset.range (hMax + 1), pConv h * tcCouponTailReal r h s := by
      refine Finset.sum_le_sum fun h hh ↦ ?_
      have hh_lt : h < hMax + 1 := Finset.mem_range.1 hh; rcases hconv_full h hh_lt with ⟨hc0, hcp⟩
      have hc0_r : (0 : ℝ) ≤ (convLb h : ℝ) := (by exact_mod_cast hc0)
      have hp0 : 0 ≤ pConv h := (div_nonneg hc0_r hS.le).trans hcp
      exact mul_le_mul_of_nonneg_left (tcCouponTailReal_mono_r hrMin hr h s) hp0
    exact (hle_acc.trans (hrun s hs_hi).2).trans hmono_sum
theorem tcCheckCouponBucket_actual_le {rMin r sMax hMax : ℕ} {pConv pActual : ℕ → ℝ} {convLb tailLb
    : ℕ → ℤ} (hr : rMin ≤ r) (hconv : ∀ h ≤ hMax, (convLb h : ℝ) / (tcScale : ℝ) ≤ pConv h) (hp0 : ∀
    s, 0 ≤ pActual s) (hpshift : ∀ s, 1 ≤ s → s ≤ sMax → (∑ h ∈ Finset.range (hMax + 1), pConv h *
    tcCouponTailReal r h s) - 1 / (tcScale : ℝ) ≤ pActual s) (hchk : tcCheckCouponBucket rMin sMax
    hMax convLb tailLb = true) : 1 ≤ sMax ∧ sMax ≤ r ∧ 1 ≤ tailLb 1 ∧ ∀ s, 1 ≤ s → s ≤ sMax → 0 ≤
    tailLb s ∧ (tailLb s : ℝ) / (tcScale : ℝ) ≤ pActual s := by
  rcases tcCheckCouponBucket_sound hr hconv hchk with ⟨_, hs1, hsMax, ht1, hall⟩
  refine ⟨hs1, hsMax.trans hr, ht1, ?_⟩
  intro s hs_lo hs_hi; rcases hall s hs_lo hs_hi with ⟨ht_nn, hz | hbd⟩
  · refine ⟨ht_nn, ?_⟩
    rw [hz]; simpa using hp0 s
  · refine ⟨ht_nn, ?_⟩
    have hsplit : ((tailLb s : ℝ) + 1) / (tcScale : ℝ) =
        (tailLb s : ℝ) / (tcScale : ℝ) + 1 / (tcScale : ℝ) := add_div _ _ _
    linarith [hbd, hsplit, hpshift s hs_lo hs_hi]
/-! ## 5. `10^16`-Scale Stage Cost, Abel-Summed Bellman Induction & Cell Relative-Cost Checks -/
/-- Constructor-WHNF-forced prefix sum `∑ j ∈ Finset.Icc 1 cnt, f j` over `ℕ`. -/
def tcSumIccOneForced (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | cnt + 1 => tcForceNat (tcSumIccOneForced f cnt) fun acc ↦ acc + f (cnt + 1)
theorem tcSumIccOneForced_eq_real (f : ℕ → ℕ) (cnt : ℕ) :
    (tcSumIccOneForced f cnt : ℝ) = ∑ j ∈ Finset.Icc (1 : ℕ) cnt, (f j : ℝ) := by
  induction cnt with
  | zero =>
      have hz : Finset.Icc (1 : ℕ) 0 = ∅ := (by simp)
      rw [hz, Finset.sum_empty]; simp [tcSumIccOneForced]
  | succ n ih =>
      have hIcc : Finset.Icc (1 : ℕ) (n + 1) = insert (n + 1) (Finset.Icc (1 : ℕ) n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnotmem : n + 1 ∉ Finset.Icc (1 : ℕ) n := (by simp)
      rw [hIcc, Finset.sum_insert hnotmem, tcSumIccOneForced, tcForceNat_eq, Nat.cast_add, ih,
        add_comm]
/-- Checker that `(steps * K_blk + d: ℝ) ≤ (attemptCostUb16 / 10^16) * √(2^n)` for `n ≥
  700`. -/
def tcCheckStageCostUb16 (r steps _d tauNum tauDen attemptCostUb16 : ℕ) : Bool :=
  decide (10 ≤ attemptCostUb16 ∧
    (steps * tauNum * 10000000000000000) ^ 2 ≤
      (attemptCostUb16 - 10) ^ 2 * (2 * tauDen) ^ 2 * r)
theorem tcCheckStageCostUb16_sound {n r steps d tauNum tauDen attemptCostUb16 : ℕ} (hn700 : 700 ≤ n)
    (hr1 : 1 ≤ r) (hr1024 : r ≤ 1024) (hsteps : steps ≤ 250) (hd : d ≤ 12) (hden : 0 < tauDen) (hK :
    (tcKBlk n r tauNum tauDen : ℝ) ≤ ((tauNum : ℝ) / (2 * (tauDen : ℝ))) * √((2 ^ n : ℝ) / (r :
    ℝ)) + 3 / 2) (hchk : tcCheckStageCostUb16 r steps d tauNum tauDen attemptCostUb16 = true) :
    (steps : ℝ) * (tcKBlk n r tauNum tauDen : ℝ) + (d : ℝ) ≤ ((attemptCostUb16 : ℝ) /
    10000000000000000) * √(2 ^ n : ℝ) := by
  unfold tcCheckStageCostUb16 at hchk; simp only [decide_eq_true_eq] at hchk
  rcases hchk with ⟨hub10, hsq_nat⟩; have hr_pos : (0 : ℝ) < (r : ℝ) := (by positivity)
  have hsr_pos : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
  have hden_pos : (0 : ℝ) < (tauDen : ℝ) := Nat.cast_pos.2 hden
  have hSN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsqrt_ge := tcSqrtRatio_ge_of_n700 hn700 hr1 hr1024
  have hSN_ge : ((10 : ℝ) ^ 103) ≤ √(2 ^ n : ℝ) := by
    have hdiv_le : (2 ^ n : ℝ) / (r : ℝ) ≤ (2 ^ n : ℝ) :=
      div_le_self (by positivity) (by exact_mod_cast hr1)
    exact hsqrt_ge.trans (Real.sqrt_le_sqrt hdiv_le)
  have hoverhead : (steps : ℝ) * (3 / 2) + (d : ℝ) ≤
      ((10 : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) := by
    have hsd : (steps : ℝ) * (3 / 2) + (d : ℝ) ≤ 387 := by
      have hs_r : (steps : ℝ) ≤ 250 := (by exact_mod_cast hsteps)
      have hd_r : (d : ℝ) ≤ 12 := (by exact_mod_cast hd); linarith
    have h10_ge : (387 : ℝ) ≤ ((10 : ℝ) / 10000000000000000) * ((10 : ℝ) ^ 103) := (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hSN_ge (by positivity : (0 : ℝ) ≤ 10 / 10000000000000000)
    linarith
  have hmain_coeff : ((steps : ℝ) * (tauNum : ℝ)) / (2 * (tauDen : ℝ) * √(r : ℝ)) ≤
    (((attemptCostUb16 - 10 : ℕ) : ℝ) / 10000000000000000) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    refine sq_le_imp_le (by positivity) (by positivity) ?_
    have hcast : (((steps * tauNum * 10000000000000000 : ℕ) : ℝ) ^ 2) ≤ (((attemptCostUb16 - 10 : ℕ)
      : ℝ) ^ 2 * ((2 * tauDen : ℕ) : ℝ) ^ 2 * (r : ℝ)) := by
      exact_mod_cast hsq_nat
    push_cast at hcast
    have hr_sq : ((((attemptCostUb16 - 10 : ℕ) : ℝ) * (2 * (tauDen : ℝ) * √(r : ℝ))) ^ 2) =
      (((attemptCostUb16 - 10 : ℕ) : ℝ) ^ 2 * (2 * (tauDen : ℝ)) ^ 2 * (r : ℝ)) := by
      calc ((((attemptCostUb16 - 10 : ℕ) : ℝ) * (2 * (tauDen : ℝ) * √(r : ℝ))) ^ 2)
          = (((attemptCostUb16 - 10 : ℕ) : ℝ) ^ 2 * (2 * (tauDen : ℝ)) ^ 2 * (√(r : ℝ)) ^ 2) := by
              ring
        _ = (((attemptCostUb16 - 10 : ℕ) : ℝ) ^ 2 * (2 * (tauDen : ℝ)) ^ 2 * (r : ℝ)) := by
              rw [Real.sq_sqrt hr_pos.le]
    rw [hr_sq]; linarith
  have hstep_mul := mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg steps)
  have hsqrt_split : √((2 ^ n : ℝ) / (r : ℝ)) = √(2 ^ n : ℝ) / √(r : ℝ) :=
    Real.sqrt_div (by positivity) (r : ℝ)
  have halg1 : (steps : ℝ) * (((tauNum : ℝ) / (2 * (tauDen : ℝ))) * (√(2 ^ n : ℝ) / √(r : ℝ)) + 3 /
    2) + (d : ℝ) = (((steps : ℝ) * (tauNum : ℝ)) / (2 * (tauDen : ℝ) * √(r : ℝ))) * √(2 ^ n : ℝ) +
    ((steps : ℝ) * (3 / 2) + (d : ℝ)) := by
    field_simp [hden_pos.ne', hsr_pos.ne']; ring
  rw [hsqrt_split] at hstep_mul; have hmain_mul := mul_le_mul_of_nonneg_right hmain_coeff hSN_pos.le
  have hub_split : (((attemptCostUb16 - 10 : ℕ) : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) + ((10 : ℝ)
    / 10000000000000000) * √(2 ^ n : ℝ) = ((attemptCostUb16 : ℝ) / 10000000000000000) * √(2 ^ n :
    ℝ) := by
    have hnat : (attemptCostUb16 - 10) + 10 = attemptCostUb16 := (by omega)
    have hreal : ((attemptCostUb16 - 10 : ℕ) : ℝ) + 10 = (attemptCostUb16 : ℝ) := by
      exact_mod_cast hnat
    linarith [show (((attemptCostUb16 - 10 : ℕ) : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) +
        ((10 : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) =
      ((((attemptCostUb16 - 10 : ℕ) : ℝ) + 10) / 10000000000000000) * √(2 ^ n : ℝ) by ring,
      congrArg (fun z : ℝ ↦ (z / 10000000000000000) * √(2 ^ n : ℝ)) hreal]
  linarith
/-- Monotonicity and zero-base checker for `vTbl` on `0.. rMax`. -/
def tcCheckMonotone (rMax : ℕ) (vTbl : ℕ → ℕ) : Bool :=
  (vTbl 0 == 0) && allRange (fun i ↦ decide (vTbl i ≤ vTbl (i + 1))) rMax
theorem tcCheckMonotone_sound {rMax : ℕ} {vTbl : ℕ → ℕ} (hchk : tcCheckMonotone rMax vTbl = true) :
    vTbl 0 = 0 ∧ ∀ a b, a ≤ b → b ≤ rMax → vTbl a ≤ vTbl b := by
  unfold tcCheckMonotone at hchk; simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  refine ⟨hchk.1, ?_⟩
  intro a b hab hb
  induction b with
  | zero => have ha0 : a = 0 := (by omega); subst ha0; exact le_rfl
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact le_rfl
      · have hk_lt : k < rMax := (by omega)
        exact (ih (by omega) (by omega)).trans (of_decide_eq_true (of_allRange hchk.2 hk_lt))
theorem tcTelescope_sub_v (v : ℕ → ℝ) {r s : ℕ} (hs : s ≤ r) :
    ∑ j ∈ Finset.Icc (1 : ℕ) s, (v (r - j + 1) - v (r - j)) = v r - v (r - s) := by
  induction s with
  | zero =>
      have hz : Finset.Icc (1 : ℕ) 0 = ∅ := (by simp)
      rw [hz, Finset.sum_empty, Nat.sub_zero, sub_self]
  | succ k ih =>
      have hIcc : Finset.Icc (1 : ℕ) (k + 1) = insert (k + 1) (Finset.Icc (1 : ℕ) k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnotmem : k + 1 ∉ Finset.Icc (1 : ℕ) k := (by simp)
      rw [hIcc, Finset.sum_insert hnotmem, ih (by omega)]
      have hsub : r - (k + 1) + 1 = r - k := (by omega); rw [hsub]; ring
theorem tcAbel_bellman_identity (v p : ℕ → ℝ) (r : ℕ) : ∑ j ∈ Finset.Icc (1 : ℕ) r, (∑ s ∈
    Finset.Icc j r, p s) * (v (r - j + 1) - v (r - j)) = ∑ s ∈ Finset.Icc (1 : ℕ) r, p s * (v r - v
    (r - s)) := by
  have hlhs : ∑ j ∈ Finset.Icc (1 : ℕ) r, (∑ s ∈ Finset.Icc j r, p s) * (v (r - j + 1) - v (r - j))
    = ∑ j ∈ Finset.Icc (1 : ℕ) r, ∑ s ∈ Finset.Icc (1 : ℕ) r, if j ≤ s then p s * (v (r - j + 1) - v
    (r - j)) else 0 := by
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1; rw [Finset.sum_mul]
    have hfilt : Finset.Icc j r = (Finset.Icc (1 : ℕ) r).filter (fun s ↦ j ≤ s) := by
      ext s; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    rw [hfilt, Finset.sum_filter]
  have hrhs : ∑ s ∈ Finset.Icc (1 : ℕ) r, p s * (v r - v (r - s)) = ∑ s ∈ Finset.Icc (1 : ℕ) r, ∑ j
    ∈ Finset.Icc (1 : ℕ) r, if j ≤ s then p s * (v (r - j + 1) - v (r - j)) else 0 := by
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hsr : s ≤ r := (Finset.mem_Icc.1 hs).2; rw [← tcTelescope_sub_v v hsr, Finset.mul_sum]
    have hfilt : Finset.Icc (1 : ℕ) s = (Finset.Icc (1 : ℕ) r).filter (fun j ↦ j ≤ s) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    rw [hfilt, Finset.sum_filter]
  rw [hlhs, hrhs, Finset.sum_comm]
/-- Bellman stage step checker at `10^-16 * √(2^n)` scale (`useTc = false` uses `vTail16`). -/
def tcCheckStageStep (r sMax attemptCostUb16 : ℕ) (tailLb : ℕ → ℤ)
    (useTc : Bool) (vTail16 vTbl : ℕ → ℕ) : Bool :=
  if !useTc then
    decide (vTail16 r ≤ vTbl r)
  else
    decide (1 ≤ sMax ∧ sMax ≤ r ∧ 1 ≤ tailLb 1) &&
    allRange (fun idx ↦ decide (vTbl (r - (idx + 1)) ≤ vTbl (r - idx))) sMax &&
    decide (attemptCostUb16 * 1000000000000 ≤
      tcSumIccOneForced (fun j ↦ (tailLb j).toNat * (vTbl (r - j + 1) - vTbl (r - j))) sMax)
theorem tcCheckStageStep_sound {r sMax attemptCostUb16 : ℕ} {tailLb : ℕ → ℤ} {useTc : Bool} {vTail16
    vTbl : ℕ → ℕ} {V pHit : ℕ → ℝ} {α attemptCost : ℝ} (hα : 0 ≤ α) (hv_mono : ∀ i < r, vTbl i ≤
    vTbl (i + 1)) (hih : ∀ j < r, V j ≤ (vTbl j : ℝ) * α) (htail_valid : useTc = false → V r ≤
    (vTail16 r : ℝ) * α) (hp_nn : useTc = true → ∀ s ∈ Finset.Icc (1 : ℕ) r, 0 ≤ pHit s) (htail_lb :
    useTc = true → ∀ j, 1 ≤ j → j ≤ sMax → 0 ≤ tailLb j ∧ (tailLb j : ℝ) / (tcScale : ℝ) ≤ ∑ s ∈
    Finset.Icc j r, pHit s) (hcost : useTc = true → attemptCost ≤ (attemptCostUb16 : ℝ) * α) (hbell
    : useTc = true → (∑ s ∈ Finset.Icc (1 : ℕ) r, pHit s) * V r ≤ attemptCost + ∑ s ∈ Finset.Icc (1
    : ℕ) r, pHit s * V (r - s)) (hchk : tcCheckStageStep r sMax attemptCostUb16 tailLb useTc vTail16
    vTbl = true) : V r ≤ (vTbl r : ℝ) * α := by
  unfold tcCheckStageStep at hchk
  cases useTc
  · simp only [Bool.not_false, ↓reduceIte, decide_eq_true_eq] at hchk
    exact (htail_valid rfl).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hchk) hα)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨⟨hs1, hs_le_r, ht1_ge1⟩, _⟩, hsum_nat⟩
    have hS : (0 : ℝ) < (tcScale : ℝ) := tcScale_pos_real
    have hS_val : (tcScale : ℝ) = 1000000000000 := (by unfold tcScale; norm_num)
    set T : ℕ → ℝ := fun j ↦ ∑ s ∈ Finset.Icc j r, pHit s
    have hT1_lb := (htail_lb rfl 1 le_rfl hs1).2
    have hT1_pos : 0 < T 1 := by
      have hpos : (0 : ℝ) < (tailLb 1 : ℝ) / (tcScale : ℝ) :=
        div_pos (by exact_mod_cast (show (0 : ℤ) < tailLb 1 by omega)) hS
      exact lt_of_lt_of_le hpos hT1_lb
    have hsum_real : (attemptCostUb16 : ℝ) ≤ ∑ j ∈ Finset.Icc (1 : ℕ) sMax, ((tailLb j : ℝ) /
      (tcScale : ℝ)) * ((vTbl (r - j + 1) : ℝ) - (vTbl (r - j) : ℝ)) := by
      have hcast : (attemptCostUb16 : ℝ) * 1000000000000 ≤ (tcSumIccOneForced
            (fun j ↦ (tailLb j).toNat * (vTbl (r - j + 1) - vTbl (r - j))) sMax : ℝ) := by
        exact_mod_cast hsum_nat
      rw [tcSumIccOneForced_eq_real] at hcast; have hdiv := div_le_div_of_nonneg_right hcast hS.le
      rw [← hS_val, mul_div_cancel_right₀ _ hS.ne', tcFinset_sum_div] at hdiv
      refine hdiv.trans (Finset.sum_le_sum fun j hj ↦ ?_)
      rcases Finset.mem_Icc.1 hj with ⟨hj1, hj_hi⟩; have htj_nn := (htail_lb rfl j hj1 hj_hi).1
      have htoNat : (((tailLb j).toNat : ℕ) : ℝ) = (tailLb j : ℝ) := by
        have hz : ((tailLb j).toNat : ℤ) = tailLb j := Int.toNat_of_nonneg htj_nn; exact_mod_cast hz
      have hv_step : vTbl (r - j) ≤ vTbl (r - j + 1) := hv_mono (r - j) (by omega)
      have hv_sub : ((vTbl (r - j + 1) - vTbl (r - j) : ℕ) : ℝ) =
          (vTbl (r - j + 1) : ℝ) - (vTbl (r - j) : ℝ) := Nat.cast_sub hv_step
      apply le_of_eq; push_cast; rw [htoNat, hv_sub, mul_div_right_comm]
    have htrunc_le_full : ∑ j ∈ Finset.Icc (1 : ℕ) sMax, ((tailLb j : ℝ) / (tcScale : ℝ)) * ((vTbl
      (r - j + 1) : ℝ) - (vTbl (r - j) : ℝ)) ≤ ∑ j ∈ Finset.Icc (1 : ℕ) r, T j * ((vTbl (r - j + 1)
      : ℝ) - (vTbl (r - j) : ℝ)) := by
      have h1 : ∑ j ∈ Finset.Icc (1 : ℕ) sMax, ((tailLb j : ℝ) / (tcScale : ℝ)) * ((vTbl (r - j + 1)
        : ℝ) - (vTbl (r - j) : ℝ)) ≤ ∑ j ∈ Finset.Icc (1 : ℕ) sMax, T j * ((vTbl (r - j + 1) : ℝ) -
        (vTbl (r - j) : ℝ)) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        rcases Finset.mem_Icc.1 hj with ⟨hj1, hj_hi⟩
        have hv_nn : 0 ≤ (vTbl (r - j + 1) : ℝ) - (vTbl (r - j) : ℝ) :=
          sub_nonneg.2 (by exact_mod_cast hv_mono (r - j) (by omega))
        exact mul_le_mul_of_nonneg_right (htail_lb rfl j hj1 hj_hi).2 hv_nn
      have hsub_icc : Finset.Icc (1 : ℕ) sMax ⊆ Finset.Icc (1 : ℕ) r :=
        Finset.Icc_subset_Icc_right hs_le_r
      refine h1.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub_icc fun j hj _ ↦ ?_)
      rcases Finset.mem_Icc.1 hj with ⟨hj1, hjr⟩
      have hTj_nn : 0 ≤ T j := Finset.sum_nonneg fun s hs ↦ hp_nn rfl s (Finset.mem_Icc.2 ⟨hj1.trans
        (Finset.mem_Icc.1 hs).1, (Finset.mem_Icc.1 hs).2⟩)
      have hv_nn : 0 ≤ (vTbl (r - j + 1) : ℝ) - (vTbl (r - j) : ℝ) :=
        sub_nonneg.2 (by exact_mod_cast hv_mono (r - j) (by omega))
      exact mul_nonneg hTj_nn hv_nn
    have habel := tcAbel_bellman_identity (fun i ↦ (vTbl i : ℝ)) pHit r
    have hub_le_abel := (hsum_real.trans htrunc_le_full).trans (le_of_eq habel)
    have hmul_α := mul_le_mul_of_nonneg_right hub_le_abel hα
    have hsplit_rhs : (∑ s ∈ Finset.Icc (1 : ℕ) r, pHit s * ((vTbl r : ℝ) - (vTbl (r - s) : ℝ))) * α
      = T 1 * ((vTbl r : ℝ) * α) - ∑ s ∈ Finset.Icc (1 : ℕ) r, pHit s * ((vTbl (r - s) : ℝ) *
      α) := by
      dsimp [T]; rw [Finset.sum_mul, Finset.sum_mul]; have hdiff :
          ∀ s ∈ Finset.Icc (1 : ℕ) r, pHit s * ((vTbl r : ℝ) - (vTbl (r - s) : ℝ)) * α =
              pHit s * ((vTbl r : ℝ) * α) - pHit s * ((vTbl (r - s) : ℝ) * α) :=
        fun _ _ ↦ by ring
      rw [Finset.sum_congr rfl hdiff, Finset.sum_sub_distrib]
    have hrem_le : ∑ s ∈ Finset.Icc (1 : ℕ) r, pHit s * V (r - s) ≤ ∑ s ∈ Finset.Icc (1 : ℕ) r, pHit
      s * ((vTbl (r - s) : ℝ) * α) := by
      refine Finset.sum_le_sum fun s hs ↦ ?_
      have hs1' : 1 ≤ s := (Finset.mem_Icc.1 hs).1
      exact mul_le_mul_of_nonneg_left (hih (r - s) (by omega)) (hp_nn rfl s hs)
    have htot : T 1 * V r ≤ T 1 * ((vTbl r : ℝ) * α) := by
      linarith [hbell rfl, hcost rfl, hmul_α, hsplit_rhs, hrem_le]
    exact le_of_mul_le_mul_left htot hT1_pos
/-- Full `1.. rMax` Bellman table checker for one parallelism exponent `e` (`m = 2^e`). -/
def tcCheckEStages (rMax : ℕ)
    (bSched : ℕ → TensorSchedCert) (bRMin bSMax : ℕ → ℕ) (bTailLb : ℕ → ℕ → ℤ)
    (vTail16 vTbl attemptUb useNat stageBid : ℕ → ℕ) : Bool :=
  tcCheckMonotone rMax vTbl &&
  allRange
    (fun idx ↦
      let r := idx + 1
      if useNat r == 0 then
        tcCheckStageStep r 0 0 (fun _ ↦ 0) false vTail16 vTbl
      else
        let bid := stageBid r
        let sc := bSched bid
        decide (bRMin bid ≤ r) &&
        tcCheckStageCostUb16 r sc.steps sc.d sc.tauNum sc.tauDen (attemptUb r) &&
        tcCheckStageStep r (bSMax bid) (attemptUb r) (bTailLb bid) true vTail16 vTbl)
    rMax
theorem tcCheckEStages_sound {n rMax : ℕ} {bSched : ℕ → TensorSchedCert} {bRMin bSMax : ℕ → ℕ}
    {bTailLb : ℕ → ℕ → ℤ} {vTail16 vTbl attemptUb useNat stageBid : ℕ → ℕ} {V : ℕ → ℝ} {pHit : ℕ → ℕ
    → ℝ} {attemptCost : ℕ → ℝ} (hn700 : 700 ≤ n) (hrMax : rMax ≤ 1024) (hV0 : V 0 ≤ 0) (hsched_ok :
    ∀ r, 1 ≤ r → r ≤ rMax → useNat r ≠ 0 → tcCheckSched (bSched (stageBid r)) = true) (htail_valid :
    ∀ r, 1 ≤ r → r ≤ rMax → useNat r = 0 → V r ≤ ((vTail16 r : ℝ) / 10000000000000000) * √(2 ^ n :
    ℝ)) (hp_nn : ∀ r, 1 ≤ r → r ≤ rMax → useNat r ≠ 0 → ∀ s ∈ Finset.Icc (1 : ℕ) r, 0 ≤ pHit r s)
    (htail_lb : ∀ r, 1 ≤ r → r ≤ rMax → useNat r ≠ 0 → bRMin (stageBid r) ≤ r → ∀ j, 1 ≤ j → j ≤
    bSMax (stageBid r) → 0 ≤ bTailLb (stageBid r) j ∧ (bTailLb (stageBid r) j : ℝ) / (tcScale : ℝ) ≤
    ∑ s ∈ Finset.Icc j r, pHit r s) (hcost : ∀ r, 1 ≤ r → r ≤ rMax → useNat r ≠ 0 →
      let sc := bSched (stageBid r)
      attemptCost r ≤ (sc.steps : ℝ) * (tcKBlk n r sc.tauNum sc.tauDen : ℝ) + (sc.d : ℝ)) (hbell : ∀
        r, 1 ≤ r → r ≤ rMax → useNat r ≠ 0 → (∑ s ∈ Finset.Icc (1 : ℕ) r, pHit r s) * V r ≤
        attemptCost r + ∑ s ∈ Finset.Icc (1 : ℕ) r, pHit r s * V (r - s)) (hchk : tcCheckEStages
        rMax bSched bRMin bSMax bTailLb vTail16 vTbl attemptUb useNat stageBid = true) : ∀ r ≤ rMax,
        V r ≤ ((vTbl r : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) := by
  unfold tcCheckEStages at hchk; simp only [Bool.and_eq_true] at hchk
  rcases tcCheckMonotone_sound hchk.1 with ⟨hv0, hv_mono⟩
  set α : ℝ := √(2 ^ n : ℝ) / 10000000000000000; have hα : 0 ≤ α := (by dsimp [α]; positivity)
  have hrew : ∀ x : ℕ, ((x : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) = (x : ℝ) * α := by
    intro x; dsimp [α]; ring
  suffices hall : ∀ r ≤ rMax, V r ≤ (vTbl r : ℝ) * α by intro r hr; rw [hrew]; exact hall r hr
  intro r hr
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hr0 : r = 0
      · subst hr0; rw [hv0]; simpa using hV0
      · have hr1 : 1 ≤ r := (by omega); have hidx : r - 1 < rMax := (by omega)
        have hitem := of_allRange hchk.2 hidx; rw [show r - 1 + 1 = r by omega] at hitem
        have hv_step : ∀ i < r, vTbl i ≤ vTbl (i + 1) :=
          fun i hi ↦ hv_mono i (i + 1) (by omega) (by omega)
        have hih_r : ∀ j < r, V j ≤ (vTbl j : ℝ) * α := fun j hj ↦ ih j hj (by omega)
        by_cases huse0 : useNat r = 0
        · have hbeq : (useNat r == 0) = true := beq_iff_eq.2 huse0; rw [hbeq] at hitem
          simp only [↓reduceIte] at hitem
          exact tcCheckStageStep_sound (sMax := 0) (attemptCostUb16 := 0) (tailLb := fun _ ↦ 0)
            (useTc := false) (vTail16 := vTail16) (pHit := pHit r) (attemptCost := attemptCost r) hα
            hv_step hih_r (fun _ ↦ by rw [← hrew]; exact htail_valid r hr1 hr huse0) (fun h ↦
            Bool.noConfusion h) (fun h ↦ Bool.noConfusion h) (fun h ↦ Bool.noConfusion h) (fun h ↦
            Bool.noConfusion h) hitem
        · have hbeq : (useNat r == 0) = false := beq_false_of_ne huse0; rw [hbeq] at hitem
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hitem
          rcases hitem with ⟨⟨hrMin_le, hub_chk⟩, hstep_chk⟩
          have hsc := tcCheckSched_sound hn700 hr1 (hr.trans hrMax) (hsched_ok r hr1 hr huse0)
          rcases hsc with ⟨_, hd12, _, hst250, _, hden, _, _, hK_le, _⟩
          have hub_sound := tcCheckStageCostUb16_sound hn700 hr1 (hr.trans hrMax)
            hst250 hd12 hden hK_le hub_chk
          exact tcCheckStageStep_sound (sMax := bSMax (stageBid r)) (attemptCostUb16 := attemptUb r)
            (tailLb := bTailLb (stageBid r)) (useTc := true) (vTail16 := vTail16) (pHit := pHit r)
            (attemptCost := attemptCost r) hα hv_step hih_r (fun h ↦ Bool.noConfusion h) (fun _ ↦
            hp_nn r hr1 hr huse0) (fun _ ↦ htail_lb r hr1 hr huse0 hrMin_le) (fun _ ↦ (hcost r hr1
            hr huse0).trans (by rwa [hrew] at hub_sound)) (fun _ ↦ hbell r hr1 hr huse0) hstep_chk
/-- Grid cell relative-cost inequality checker at `(mIdx, kIdx)` (`m = 2^mIdx`, `k =
  2^kIdx`). -/
def tcCheckRelCostCell (mIdx kIdx : ℕ) (vTbl : ℕ → ℕ) (relNum relDen : ℕ) : Bool :=
  decide (mIdx < 11 ∧ kIdx < 11 ∧ 0 < relDen ∧
    vTbl (2 ^ kIdx) * sqrtMUpNat mIdx * relDen ≤
      relNum * 785398163397 * harmSumPow2 kIdx * 10000)
theorem tcCheckRelCostCell_sound {mIdx kIdx : ℕ} {vTbl : ℕ → ℕ} {relNum relDen n : ℕ} (hchk :
    tcCheckRelCostCell mIdx kIdx vTbl relNum relDen = true) : ((vTbl (2 ^ kIdx) : ℝ) /
    10000000000000000) * √(2 ^ n : ℝ) ≤ ((relNum : ℝ) / (relDen : ℝ)) * ((π / 4) * (∑ r ∈ Finset.Icc
    (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 ^ mIdx : ℝ))) := by
  unfold tcCheckRelCostCell at hchk; simp only [decide_eq_true_eq] at hchk
  rcases hchk with ⟨hm11, hk11, hden_pos, hnat⟩
  rcases sqrtMUpNat_bounds hm11 with ⟨hsm_pos_nat, hsm_sq⟩
  have hsm_pos : (0 : ℝ) < (sqrtMUpNat mIdx : ℝ) := Nat.cast_pos.2 hsm_pos_nat
  have hden_r : (0 : ℝ) < (relDen : ℝ) := Nat.cast_pos.2 hden_pos
  have hSN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsqrtm_pos : (0 : ℝ) < √(2 ^ mIdx : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsqrtm_le : √(2 ^ mIdx : ℝ) ≤ (sqrtMUpNat mIdx : ℝ) / 1000000000000 := by
    rw [le_div_iff₀ (by norm_num)]; refine sq_le_imp_le (by positivity) (by positivity) ?_
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ mIdx)]
    have hcast : ((2 ^ mIdx : ℕ) : ℝ) * 1000000000000 * 1000000000000 ≤
        (sqrtMUpNat mIdx : ℝ) * (sqrtMUpNat mIdx : ℝ) := by exact_mod_cast hsm_sq
    push_cast at hcast
    linarith [hcast, show (2 : ℝ) ^ mIdx * (1000000000000 : ℝ) ^ 2 - (sqrtMUpNat mIdx : ℝ) ^ 2 =
        (2 : ℝ) ^ mIdx * 1000000000000 * 1000000000000 -
          (sqrtMUpNat mIdx : ℝ) * (sqrtMUpNat mIdx : ℝ) by ring]
  have hharm := harmSumPow2_le_sum hk11
  have hpi : (785398163397 : ℝ) / 1000000000000 ≤ π / 4 := (by linarith [Real.pi_gt_d20])
  have hcell_r : (vTbl (2 ^ kIdx) : ℝ) * (sqrtMUpNat mIdx : ℝ) * (relDen : ℝ) ≤ (relNum : ℝ) *
    785398163397 * (harmSumPow2 kIdx : ℝ) * 10000 := by
    exact_mod_cast hnat
  have hcoeff : (vTbl (2 ^ kIdx) : ℝ) / 10000000000000000 ≤ ((relNum : ℝ) / (relDen : ℝ)) *
    ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat
    mIdx : ℝ) / 1000000000000) := by
    have hlhs : (vTbl (2 ^ kIdx) : ℝ) / 10000000000000000 = ((vTbl (2 ^ kIdx) : ℝ) * (sqrtMUpNat
      mIdx : ℝ) * (relDen : ℝ)) / (10000000000000000 * (sqrtMUpNat mIdx : ℝ) * (relDen : ℝ)) := by
      field_simp [hsm_pos.ne', hden_r.ne']
    have hrhs : ((relNum : ℝ) / (relDen : ℝ)) * ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2
      kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat mIdx : ℝ) / 1000000000000) = ((relNum : ℝ) *
      785398163397 * (harmSumPow2 kIdx : ℝ) * 10000) / (10000000000000000 * (sqrtMUpNat mIdx : ℝ) *
      (relDen : ℝ)) := by
      field_simp [hsm_pos.ne', hden_r.ne']; ring
    rw [hlhs, hrhs]; exact div_le_div_of_nonneg_right hcell_r (by positivity)
  have hnum_le : ((relNum : ℝ) / (relDen : ℝ)) * ((785398163397 : ℝ) / 1000000000000) *
    ((harmSumPow2 kIdx : ℝ) / 1000000000000) ≤ ((relNum : ℝ) / (relDen : ℝ)) * ((π / 4) * (∑ r ∈
    Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ))) := by
    have hprod :
        ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) ≤
          (π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) :=
      mul_le_mul hpi hharm (by positivity) (by linarith [Real.pi_pos])
    have hm := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (relNum : ℝ) / (relDen : ℝ))
    linarith [hm, show ((relNum : ℝ) / (relDen : ℝ)) *
          (((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000)) =
        ((relNum : ℝ) / (relDen : ℝ)) *
          ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) by
        ring]
  have hmono : ((relNum : ℝ) / (relDen : ℝ)) * ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2
    kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat mIdx : ℝ) / 1000000000000) ≤ ((relNum : ℝ) / (relDen :
    ℝ)) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ))) / √(2 ^ mIdx : ℝ) :=
    (div_le_div_of_nonneg_right hnum_le (by positivity)).trans (div_le_div_of_nonneg_left
    (mul_nonneg (by positivity) (mul_nonneg (by linarith [Real.pi_pos]) (Finset.sum_nonneg fun _ _ ↦
    by positivity))) hsqrtm_pos hsqrtm_le)
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n) (2 ^ mIdx : ℝ)]
  calc ((vTbl (2 ^ kIdx) : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) ≤ (((relNum : ℝ) / (relDen : ℝ)) *
        ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ))) / √(2 ^ mIdx : ℝ)) * √(2 ^ n
        : ℝ) := mul_le_mul_of_nonneg_right (hcoeff.trans hmono) hSN_pos.le
    _ = ((relNum : ℝ) / (relDen : ℝ)) *
          ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) *
            (√(2 ^ n : ℝ) / √(2 ^ mIdx : ℝ))) := by
        ring
end QuantumComputation.Specs.GroverFindAll.TensorConveyorCert
