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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLCertDefs
/-!
# Zero-Wrapping `L2Ball` Certificate Checkers & Soundness for `H_dist(2 ≤ L ≤ 8)` Conveyors
Extends `SchurWeylHdistLCertDefs` with Euclidean `L2Ball`
contraction propagation `(c_t, ρ_t)` and exact isometric norm conservation
`1 - cum_t = swLNormSq st_t` at fixed-point scale `swScale = 10^9`.
Eliminates `(1 + |sin|)^K` Moore hyperrectangle wrapping across deep `2 ≤ L ≤ 8` conveyor
pulse
trains while preserving the exact `checkSwLBucketCert`, `checkSwLM1Stage_sound`, and
`checkMultiSWLStage_sound` interfaces consumed by `SwLM1CertBundle` and `MultiSWLCertBundle`.
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
namespace SchurWeylLCert
open Real
open scoped BigOperators
/-! ## 1. Isometric Contraction & Polynomial Cauchy-Schwarz on `ℝ^{2L}` -/
theorem swLGroverRotVec_sub (L : ℕ) (cs : Fin L → ℝ × ℝ) (x y : Fin (2 * L) → ℝ) : (fun j ↦
  swLGroverRotVec L cs x j - swLGroverRotVec L cs y j) = swLGroverRotVec L cs (fun j ↦ x j - y j) :=
  by
  ext j; unfold swLGroverRotVec; dsimp only
  split_ifs <;> ring
theorem swLPieriAndWeakVec_sub (L : ℕ) (hL : 2 ≤ L) (p : SwLPulseRat L) (x y : Fin (2 * L) → ℝ) :
  (fun j ↦ swLPieriAndWeakVec L hL p x j - swLPieriAndWeakVec L hL p y j) = swLPieriAndWeakVec L hL
  p (fun j ↦ x j - y j) := by
  ext j; unfold swLPieriAndWeakVec; dsimp only
  split_ifs <;> ring
/-- Exact `1`-Lipschitz Euclidean contraction of `swLPulseStepReal` for any `2 ≤ L`. -/
theorem swLPulseStepReal_distSq_le {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} (hcs : ∀ w : Fin L, (cs
  w).1 ^ 2 + (cs w).2 ^ 2 = 1) {p : SwLPulseRat L} (hp : swLPulseValid p = true) (x y : Fin (2 * L)
  → ℝ) (cumX survX cumY survY : ℝ) : swLNormSq (fun j ↦ (swLPulseStepReal L hL cs x cumX survX p).1
  j - (swLPulseStepReal L hL cs y cumY survY p).1 j) ≤ swLNormSq (fun j ↦ x j - y j) := by
  unfold swLPulseValid at hp; rw [decide_eq_true_eq] at hp; unfold swLPulseStepReal; dsimp only
  rw [swLPieriAndWeakVec_sub, swLGroverRotVec_sub]
  have hpieri := swLPieriAndWeakVec_normSq hL hp (swLGroverRotVec L cs (fun j ↦ x j - y j))
  have hgrov := swLGroverRotVec_normSq hcs (fun j ↦ x j - y j); have hnn : 0 ≤ (swLCayleySin p.vNum
    p.uvDen * swLGroverRotVec L cs (fun j ↦ x j - y j) ⟨2 * L - 1, by omega⟩) ^ 2 := sq_nonneg _
  linarith
theorem sum_mul_sq_le_normSq_mul {L : ℕ} (u v : Fin (2 * L) → ℝ) : (∑ j : Fin (2 * L), u j * v j) ^
  2 ≤ swLNormSq u * swLNormSq v := by
  have hlag : 0 ≤ ∑ i : Fin (2 * L), ∑ j : Fin (2 * L), (u i * v j - u j * v i) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hexp : ∑ i : Fin (2 * L), ∑ j : Fin (2 * L), (u i * v j - u j * v i) ^ 2 = 2 * (swLNormSq u *
    swLNormSq v - (∑ j : Fin (2 * L), u j * v j) ^ 2) := by
    unfold swLNormSq
    have h1 : ∀ i : Fin (2 * L), ∑ j : Fin (2 * L), (u i * v j - u j * v i) ^ 2 = u i ^ 2 * (∑ j :
      Fin (2 * L), v j ^ 2) - 2 * u i * v i * (∑ j : Fin (2 * L), u j * v j) + v i ^ 2 * (∑ j : Fin
      (2 * L), u j ^ 2) := fun i ↦ by
      have hterm : ∀ j : Fin (2 * L), (u i * v j - u j * v i) ^ 2 =
          u i ^ 2 * v j ^ 2 - (2 * u i * v i) * (u j * v j) + v i ^ 2 * u j ^ 2 :=
        fun _ ↦ by ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h2 : ∑ i : Fin (2 * L), 2 * u i * v i = 2 * ∑ i : Fin (2 * L), u i * v i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [h2]; ring
  linarith
theorem swLNormSq_add_le_sq {L : ℕ} {u v : Fin (2 * L) → ℝ} {ru rv : ℝ} (hru0 : 0 ≤ ru) (hrv0 : 0 ≤
  rv) (hu : swLNormSq u ≤ ru ^ 2) (hv : swLNormSq v ≤ rv ^ 2) : swLNormSq (fun j ↦ u j + v j) ≤ (ru
  + rv) ^ 2 := by
  have hprod : swLNormSq u * swLNormSq v ≤ (ru * rv) ^ 2 := by
    have hm := mul_le_mul hu hv (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (sq_nonneg ru)
    linarith [show ru ^ 2 * rv ^ 2 = (ru * rv) ^ 2 by ring]
  have hcs_sq : (∑ j : Fin (2 * L), u j * v j) ^ 2 ≤ (ru * rv) ^ 2 := (sum_mul_sq_le_normSq_mul u
    v).trans hprod
  have hdot : ∑ j : Fin (2 * L), u j * v j ≤ ru * rv := by
    have habs : |∑ j : Fin (2 * L), u j * v j| ≤ |ru * rv| := sq_le_sq.1 hcs_sq; rw [abs_of_nonneg
      (mul_nonneg hru0 hrv0)] at habs; exact (le_abs_self _).trans habs
  have hexp : swLNormSq (fun j ↦ u j + v j) = swLNormSq u + 2 * (∑ j : Fin (2 * L), u j * v j) +
    swLNormSq v := by
    unfold swLNormSq
    have hterm : ∀ j : Fin (2 * L), (u j + v j) ^ 2 = u j ^ 2 + 2 * (u j * v j) + v j ^ 2 :=
      fun _ ↦ by ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [show (ru + rv) ^ 2 = ru ^ 2 + 2 * (ru * rv) + rv ^ 2 by ring]
/-! ## 2. Primitive Kernel-Fast Interval & Walk Operations (`swScale = 10^9`) -/
theorem natBeq_eq_decide : ∀ (a b : ℕ), Nat.beq a b = decide (a = b)
  | 0, 0 => rfl | 0, _ + 1 => rfl | _ + 1, 0 => rfl
  | a + 1, b + 1 => by simp only [Nat.beq, natBeq_eq_decide a b, Nat.add_right_cancel_iff]
/-- Constructor-matched boolean `a ≤ b` on `ℤ` avoiding `LinearOrder` dictionary reduction
  in
  kernel `decide`. -/
def bleZ (a b : ℤ) : Bool :=
  match Int.sub b a with
  | Int.ofNat _ => true
  | Int.negSucc _ => false
theorem bleZ_eq_decide (a b : ℤ) : bleZ a b = decide (a ≤ b) := by
  unfold bleZ; have hsub : Int.sub b a = b - a := rfl; rw [hsub]
  cases h : b - a with
  | ofNat n => have hab : a ≤ b := (by rw [Int.ofNat_eq_natCast] at h; omega); simp [hab]
  | negSucc n => have hab : ¬(a ≤ b) := (by rw [Int.negSucc_eq] at h; omega); simp [hab]
/-- Constructor-matched boolean `a = b` on `ℤ` avoiding `DecidableEq` overhead in kernel
  `decide`. -/
def beqZ (a b : ℤ) : Bool :=
  bleZ a b && bleZ b a
theorem beqZ_eq_decide (a b : ℤ) : beqZ a b = decide (a = b) := by
  unfold beqZ; rw [bleZ_eq_decide, bleZ_eq_decide]; by_cases h1 : a ≤ b
  · by_cases h2 : b ≤ a
    · have heq : a = b := (by omega); simp [heq]
    · have hne : a ≠ b := (by omega); simp [h1, h2, hne]
  · have hne : a ≠ b := (by omega); simp [h1, hne]
/-- Primitive `min` on `ℤ` via `bleZ`. -/
def minZ (a b : ℤ) : ℤ :=
  cond (bleZ a b) a b
theorem minZ_eq (a b : ℤ) : minZ a b = min a b := by
  unfold minZ; rw [bleZ_eq_decide]; by_cases h : a ≤ b
  · simp [h]
  · simp [h]; omega
/-- Primitive `max` on `ℤ` via `bleZ`. -/
def maxZ (a b : ℤ) : ℤ :=
  cond (bleZ a b) b a
theorem maxZ_eq (a b : ℤ) : maxZ a b = max a b := by
  unfold maxZ; rw [bleZ_eq_decide]; by_cases h : a ≤ b
  · simp [h]
  · simp [h]; omega
/-- Primitive ceiling division `⌈x / swScale⌉` via `Int.ediv` and `Int.neg`. -/
def ceilDivScaleP (x : ℤ) : ℤ :=
  Int.neg (Int.ediv (Int.neg x) swScale)
theorem ceilDivScaleP_eq (x : ℤ) : ceilDivScaleP x = -((-x) / swScale) := rfl
/-- Primitive `10^9`-scale interval addition via `Int.add`. -/
def ivAddIntP (a b : IvInt) : IvInt :=
  (Int.add a.1 b.1, Int.add a.2 b.2)
theorem ivAddIntP_eq (a b : IvInt) : ivAddIntP a b = ivAddInt a b := rfl
/-- Primitive `10^9`-scale interval subtraction via `Int.sub`. -/
def ivSubIntP (a b : IvInt) : IvInt :=
  (Int.sub a.1 b.2, Int.sub a.2 b.1)
theorem ivSubIntP_eq (a b : IvInt) : ivSubIntP a b = ivSubInt a b := rfl
/-- Primitive `10^9`-scale interval multiplication via `Int.mul`, `minZ`, `maxZ`, and
  `Int.ediv`. -/
def ivMulIntP (a b : IvInt) : IvInt :=
  withForcedInt (Int.mul a.1 b.1) fun p1 ↦
    withForcedInt (Int.mul a.1 b.2) fun p2 ↦
      withForcedInt (Int.mul a.2 b.1) fun p3 ↦
        withForcedInt (Int.mul a.2 b.2) fun p4 ↦
          withForcedInt (minZ (minZ p1 p2) (minZ p3 p4)) fun lo ↦
            withForcedInt (maxZ (maxZ p1 p2) (maxZ p3 p4)) fun hi ↦
              (Int.ediv lo swScale, ceilDivScaleP hi)
theorem ivMulIntP_eq (a b : IvInt) : ivMulIntP a b = ivMulInt a b := by
  unfold ivMulIntP ivMulInt; simp only [withForcedInt_eq, minZ_eq, maxZ_eq]; rfl
/-- Primitive `10^9`-scale interval squaring via `bleZ`, `Int.mul`, `Int.ediv`, and `maxZ`. -/
def ivSqIntP (a : IvInt) : IvInt :=
  cond (bleZ 0 a.1)
    (Int.ediv (Int.mul a.1 a.1) swScale, ceilDivScaleP (Int.mul a.2 a.2))
    (cond (bleZ a.2 0)
      (Int.ediv (Int.mul a.2 a.2) swScale, ceilDivScaleP (Int.mul a.1 a.1))
      (withForcedInt (maxZ (Int.neg a.1) a.2) fun m ↦
        (0, ceilDivScaleP (Int.mul m m))))
theorem ivSqIntP_eq (a : IvInt) : ivSqIntP a = ivSqInt a := by
  unfold ivSqIntP ivSqInt; rw [bleZ_eq_decide, bleZ_eq_decide, maxZ_eq]; by_cases h1 : 0 ≤ a.1
  · simp only [h1, decide_true, Bool.cond_true, ↓reduceIte]; rfl
  · simp only [h1, decide_false, Bool.cond_false, ↓reduceIte]; by_cases h2 : a.2 ≤ 0
    · simp only [h2, decide_true, Bool.cond_true, ↓reduceIte]; rfl
    · simp only [h2, decide_false, Bool.cond_false, ↓reduceIte, withForcedInt_eq]; rfl
/-- Primitive `10^9`-scale outward rational interval via `Int.mul`, `Int.ediv`, and
  `Int.neg`. -/
def ivRatDivP (num den : ℤ) : IvInt :=
  withForcedInt (Int.mul num swScale) fun sc ↦
    (Int.ediv sc den, Int.neg (Int.ediv (Int.neg sc) den))
theorem ivRatDivP_eq (num den : ℤ) : ivRatDivP num den = ivRatDiv num den := rfl
/-- Primitive `10^9`-scale Pythagorean `(cos, sin)` intervals. -/
def ivPythagP (uNum uDen : ℤ) : IvInt × IvInt :=
  withForcedInt (Int.add (Int.mul uDen uDen) (Int.mul uNum uNum)) fun d ↦
    (ivRatDivP (Int.sub (Int.mul uDen uDen) (Int.mul uNum uNum)) d,
     ivRatDivP (Int.mul (Int.mul 2 uNum) uDen) d)
theorem ivPythagP_eq (uNum uDen : ℤ) : ivPythagP uNum uDen = ivPythag uNum uDen := rfl
/-- Head trigger pair with `((0, 0), (0, 0))` fallback. -/
def headTrigP : List (IvInt × IvInt) → IvInt × IvInt
  | x :: _ => x
  | [] => ((0, 0), (0, 0))
theorem headTrigP_eq (ts : List (IvInt × IvInt)) :
    headTrigP ts = ts.getD 0 ((0, 0), (0, 0)) := by cases ts <;> rfl
/-- Drop one leading trigger pair. -/
def drop1TrigP : List (IvInt × IvInt) → List (IvInt × IvInt)
  | _ :: r => r
  | [] => []
theorem drop1TrigP_getD (ts : List (IvInt × IvInt)) (w : ℕ) : (drop1TrigP ts).getD w ((0, 0), (0,
  0)) = ts.getD (w + 1) ((0, 0), (0, 0)) := by cases ts <;> simp [drop1TrigP]
/-- Head integer with `0` fallback. -/
def headZP : List ℤ → ℤ
  | x :: _ => x
  | [] => 0
theorem headZP_eq (cs : List ℤ) : headZP cs = cs.getD 0 0 := by cases cs <;> rfl
/-- Second integer with `0` fallback. -/
def secondZP : List ℤ → ℤ
  | _ :: y :: _ => y
  | _ => 0
theorem secondZP_eq (cs : List ℤ) : secondZP cs = cs.getD 1 0 := by
  rcases cs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
/-- Drop two leading integers. -/
def drop2ZP : List ℤ → List ℤ
  | _ :: _ :: r => r
  | _ => []
theorem drop2ZP_getD (cs : List ℤ) (m : ℕ) : (drop2ZP cs).getD m 0 = cs.getD (m + 2) 0 := by
  rcases cs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp [drop2ZP]
/-- Head interval with `(0, 0)` fallback. -/
def headIvP : List IvInt → IvInt
  | x :: _ => x
  | [] => (0, 0)
theorem headIvP_eq (ss : List IvInt) : headIvP ss = ss.getD 0 (0, 0) := by cases ss <;> rfl
/-- Second interval with `(0, 0)` fallback. -/
def secondIvP : List IvInt → IvInt
  | _ :: y :: _ => y
  | _ => (0, 0)
theorem secondIvP_eq (ss : List IvInt) : secondIvP ss = ss.getD 1 (0, 0) := by
  rcases ss with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
/-- Drop two leading intervals. -/
def drop2IvP : List IvInt → List IvInt
  | _ :: _ :: r => r
  | _ => []
theorem drop2IvP_getD (ss : List IvInt) (m : ℕ) : (drop2IvP ss).getD m (0, 0) = ss.getD (m + 2) (0,
  0) := by rcases ss with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp [drop2IvP]
/-- Drop one leading interval. -/
def drop1IvP : List IvInt → List IvInt
  | _ :: r => r
  | [] => []
theorem drop1IvP_getD (ss : List IvInt) (m : ℕ) : (drop1IvP ss).getD m (0, 0) = ss.getD (m + 1) (0,
  0) := by cases ss <;> simp [drop1IvP]
theorem list_getElem_eq_getD {α : Type*} (xs : List α) (d : α) (j : ℕ) (hj : j < xs.length) : xs[j]
  = xs.getD j d := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
/-- Point-interval list `[(c_0, c_0),..., (c_{2L-1}, c_{2L-1})]` from `cVec: List ℤ`. -/
def swLCenterPtIvs (cVec : List ℤ) : List IvInt :=
  withForcedList (cVec.map fun cj ↦ (cj, cj)) id
theorem centerPtIvs_getD (cs : List ℤ) (i : ℕ) : (swLCenterPtIvs cs).getD i (0, 0) = (cs.getD i 0,
  cs.getD i 0) := by
  unfold swLCenterPtIvs; rw [withForcedList_eq, id_eq]
  induction cs generalizing i with
  | nil => simp
  | cons c cs ih =>
    cases i with
    | zero => simp
    | succ i' => simp only [List.map_cons, List.getD_cons_succ]; exact ih i'
/-- Constructor-walk Grover plane rotation avoiding `List.finRange` and `List.getD`. -/
def groverWalkP : ℕ → List (IvInt × IvInt) → List ℤ → List IvInt
  | 0, _, _ => []
  | k + 1, ts, cs =>
      let ce := headZP cs
      let co := secondZP cs
      match headTrigP ts with
      | (cw, sw) =>
          withForcedIv (ivSubIntP (ivMulIntP cw (ce, ce)) (ivMulIntP sw (co, co))) fun e' ↦
            withForcedIv (ivAddIntP (ivMulIntP sw (ce, ce)) (ivMulIntP cw (co, co))) fun o' ↦
              withForcedPairList (drop1TrigP ts) fun ts' ↦
                forceListId (drop2ZP cs) fun cs' ↦
                  e' :: o' :: groverWalkP k ts' cs'
theorem groverWalkP_length : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ), (groverWalkP k ts
  cs).length = 2 * k
  | 0, _, _ => rfl
  | k + 1, ts, cs => by
    simp only [groverWalkP, withForcedIv_eq, withForcedPairList_eq, forceListId_eq,
      List.length_cons, groverWalkP_length k]; omega
theorem groverWalkP_getD : ∀ (k : ℕ) (ts : List (IvInt × IvInt)) (cs : List ℤ) (j : ℕ),
    j < 2 * k →
    (groverWalkP k ts cs).getD j (0, 0) =
      let w := j / 2
      match ts.getD w ((0, 0), (0, 0)), (cs.getD (2 * w) 0, cs.getD (2 * w) 0),
          (cs.getD (2 * w + 1) 0, cs.getD (2 * w + 1) 0) with
    | (cw, sw), ae, ao =>
        if j % 2 = 0 then ivSubInt (ivMulInt cw ae) (ivMulInt sw ao)
        else ivAddInt (ivMulInt sw ae) (ivMulInt cw ao)
  | 0, _, _, _, hj => by omega
  | k + 1, ts, cs, j, hj => by
    unfold groverWalkP; simp only [withForcedIv_eq, withForcedPairList_eq, forceListId_eq,
      ivSubIntP_eq, ivAddIntP_eq, ivMulIntP_eq, headTrigP_eq, headZP_eq, secondZP_eq]
    rcases hpair : ts.getD 0 ((0, 0), (0, 0)) with ⟨cw, sw⟩; rcases j with _ | _ | j'
    · change ivSubInt (ivMulInt cw (cs.getD 0 0, cs.getD 0 0))
          (ivMulInt sw (cs.getD 1 0, cs.getD 1 0)) =
        match ts.getD 0 ((0, 0), (0, 0)), (cs.getD 0 0, cs.getD 0 0),
            (cs.getD 1 0, cs.getD 1 0) with
        | (cw, sw), ae, ao => ivSubInt (ivMulInt cw ae) (ivMulInt sw ao)
      rw [hpair]
    · change ivAddInt (ivMulInt sw (cs.getD 0 0, cs.getD 0 0))
          (ivMulInt cw (cs.getD 1 0, cs.getD 1 0)) =
        match ts.getD 0 ((0, 0), (0, 0)), (cs.getD 0 0, cs.getD 0 0),
            (cs.getD 1 0, cs.getD 1 0) with
        | (cw, sw), ae, ao => ivAddInt (ivMulInt sw ae) (ivMulInt cw ao)
      rw [hpair]
    · have hj' : j' < 2 * k := (by omega); simp only [List.getD_cons_succ]; rw [groverWalkP_getD k
        (drop1TrigP ts) (drop2ZP cs) j' hj']; have hd : (j' + 1 + 1) / 2 = j' / 2 + 1 := (by omega)
      have hm : (j' + 1 + 1) % 2 = j' % 2 := by omega
      have hc0 : 2 * (j' / 2 + 1) = 2 * (j' / 2) + 2 := by omega
      have hc1 : 2 * (j' / 2) + 2 + 1 = (2 * (j' / 2) + 1) + 2 := (by omega); dsimp only; rw [hd,
        hm, hc0, hc1, drop1TrigP_getD, drop2ZP_getD, drop2ZP_getD]
theorem groverWalkP_eq (L : ℕ) (trigIvs : List (IvInt × IvInt)) (cVec : List ℤ) : groverWalkP L
  trigIvs cVec = swLGroverRotIv L trigIvs (swLCenterPtIvs cVec) := by
  apply List.ext_getElem
  · simp [groverWalkP_length, swLGroverRotIv]
  · intro j hj1 _; have hj : j < 2 * L := (by simpa [groverWalkP_length] using hj1)
    rw [list_getElem_eq_getD _ (0, 0) j hj1, groverWalkP_getD L trigIvs cVec j hj]
    unfold swLGroverRotIv; simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast,
      centerPtIvs_getD]
/-- `Fin.succ`-recursive Pythagorean table builder avoiding `List.finRange` and `omega`. -/
def uPythagsFin (uDen : ℤ) : ∀ (m : ℕ), (Fin m → ℤ) → List (IvInt × IvInt)
  | 0, _ => []
  | k + 1, f =>
      withForcedPair (ivPythagP (f ⟨0, Nat.zero_lt_succ k⟩) uDen) fun py ↦
        withForcedPairList (uPythagsFin uDen k (fun i ↦ f i.succ)) fun rest ↦
          py :: rest
theorem uPythagsFin_eq (uDen : ℤ) : ∀ (m : ℕ) (f : Fin m → ℤ), uPythagsFin uDen m f = (List.finRange
  m).map fun w0 ↦ ivPythag (f w0) uDen
  | 0, _ => rfl
  | k + 1, f => by
    simp only [uPythagsFin, withForcedPair_eq, withForcedPairList_eq, ivPythagP_eq, uPythagsFin_eq
      uDen k (fun i ↦ f i.succ), List.finRange_succ, List.map_cons, List.map_map]; rfl
/-- Constructor-walk interior Pieri `SO(2)` + top weak-measurement survival update. -/
def pieriWalkIvP (cv : IvInt) : ℕ → List (IvInt × IvInt) → List IvInt → List IvInt
  | 0, _, ss => [ivMulIntP cv (headIvP ss)]
  | k + 1, us, ss =>
      let lv := headIvP ss
      let rv := secondIvP ss
      match headTrigP us with
      | (cu, su) =>
          withForcedIv (ivSubIntP (ivMulIntP cu lv) (ivMulIntP su rv)) fun l' ↦
            withForcedIv (ivAddIntP (ivMulIntP su lv) (ivMulIntP cu rv)) fun r' ↦
              withForcedPairList (drop1TrigP us) fun us' ↦
                withForcedList (drop2IvP ss) fun ss' ↦
                  l' :: r' :: pieriWalkIvP cv k us' ss'
theorem pieriWalkIvP_length (cv : IvInt) : ∀ (k : ℕ) (us : List (IvInt × IvInt)) (ss : List IvInt),
  (pieriWalkIvP cv k us ss).length = 2 * k + 1
  | 0, _, _ => rfl
  | k + 1, us, ss => by
    simp only [pieriWalkIvP, withForcedIv_eq, withForcedPairList_eq, withForcedList_eq,
      List.length_cons, pieriWalkIvP_length cv k]; omega
theorem pieriWalkIvP_getD (cv : IvInt) :
    ∀ (k : ℕ) (us : List (IvInt × IvInt)) (ss : List IvInt) (m : ℕ),
    m < 2 * k + 1 →
    (pieriWalkIvP cv k us ss).getD m (0, 0) =
      if m < 2 * k then
        let idx := m / 2
        match us.getD idx ((0, 0), (0, 0)), ss.getD (2 * idx) (0, 0),
            ss.getD (2 * idx + 1) (0, 0) with
      | (cu, su), lv, rv =>
          if m % 2 = 0 then ivSubInt (ivMulInt cu lv) (ivMulInt su rv)
          else ivAddInt (ivMulInt su lv) (ivMulInt cu rv)
    else
      ivMulInt cv (ss.getD (2 * k) (0, 0))
  | 0, _, ss, m, hm => by
    have hm0 : m = 0 := (by omega); subst hm0; simp [pieriWalkIvP, ivMulIntP_eq, headIvP_eq]
  | k + 1, us, ss, m, hm => by
    unfold pieriWalkIvP; simp only [withForcedIv_eq, withForcedPairList_eq, withForcedList_eq,
      ivSubIntP_eq, ivAddIntP_eq, ivMulIntP_eq, headTrigP_eq, headIvP_eq, secondIvP_eq]
    rcases hpair : us.getD 0 ((0, 0), (0, 0)) with ⟨cu, su⟩; rcases m with _ | _ | m'
    · have hlt0 : 0 < 2 * (k + 1) := by omega
      change ivSubInt (ivMulInt cu (ss.getD 0 (0, 0))) (ivMulInt su (ss.getD 1 (0, 0))) = _
      simp only [hlt0, ↓reduceIte, Nat.zero_div, hpair]
    · have hlt1 : 1 < 2 * (k + 1) := (by omega); have hd1 : 1 / 2 = 0 := rfl; have hm1 : ¬(1 % 2 =
        0) := (by omega); change ivAddInt (ivMulInt su (ss.getD 0 (0, 0))) (ivMulInt cu (ss.getD 1
        (0, 0))) = _; simp only [hlt1, ↓reduceIte, hd1, hpair, hm1]
    · have hm' : m' < 2 * k + 1 := (by omega); simp only [List.getD_cons_succ]
      rw [pieriWalkIvP_getD cv k (drop1TrigP us) (drop2IvP ss) m' hm']; by_cases hlt : m' < 2 * k
      · have hlt2 : m' + 1 + 1 < 2 * (k + 1) := by omega
        have hd : (m' + 1 + 1) / 2 = m' / 2 + 1 := by omega
        have hmod : (m' + 1 + 1) % 2 = m' % 2 := (by omega); have hs0 : 2 * (m' / 2 + 1) = 2 * (m' /
          2) + 2 := (by omega); have hs1 : 2 * (m' / 2) + 2 + 1 = (2 * (m' / 2) + 1) + 2 :=
          (by omega); simp only [hlt, hlt2, ↓reduceIte]; rw [hd, hmod, hs0, hs1, drop1TrigP_getD,
          drop2IvP_getD, drop2IvP_getD]
      · have hnlt2 : ¬(m' + 1 + 1 < 2 * (k + 1)) := by omega
        have htop : 2 * (k + 1) = 2 * k + 2 := by omega
        simp only [hlt, hnlt2, ↓reduceIte]; rw [htop, drop2IvP_getD]
/-- Primitive drop-in replacement for `swLPieriAndWeakIv` avoiding `List.finRange` and
  `List.getD`. -/
def swLPieriAndWeakIvP : ∀ (L : ℕ), SwLPulseRat L → IvInt → List IvInt → List IvInt
  | 0, _, _, _ => []
  | m + 1, p, cv, naIv =>
      withForcedPairList (uPythagsFin (Int.ofNat p.uvDen) m p.uNum) fun ups ↦
        withForcedList (drop1IvP naIv) fun restIv ↦
          headIvP naIv :: pieriWalkIvP cv m ups restIv
theorem swLPieriAndWeakIvP_eq : ∀ (L : ℕ) (p : SwLPulseRat L) (cv : IvInt) (naIv : List IvInt),
  swLPieriAndWeakIvP L p cv naIv = swLPieriAndWeakIv L p cv naIv
  | 0, _, _, _ => rfl
  | m + 1, p, cv, naIv => by
    have hlhs : swLPieriAndWeakIvP (m + 1) p cv naIv = headIvP naIv :: pieriWalkIvP cv m
      (uPythagsFin (Int.ofNat p.uvDen) m p.uNum) (drop1IvP naIv) :=
      (by simp only [swLPieriAndWeakIvP, withForcedPairList_eq, withForcedList_eq]); rw [hlhs];
      unfold swLPieriAndWeakIv; rw [withForcedPairList_eq, uPythagsFin_eq, Int.ofNat_eq_natCast]
    apply List.ext_getElem
    · simp only [List.length_cons, pieriWalkIvP_length, List.length_map, List.length_finRange]
      omega
    · intro j hj1 _; rw [list_getElem_eq_getD _ (0, 0) j hj1]; simp only [List.getElem_map,
        List.getElem_finRange, Fin.val_cast]; rcases j with _ | j'
      · simp [headIvP_eq]
      · have hj' : j' < 2 * m + 1 :=
          (by simp only [List.length_cons, pieriWalkIvP_length] at hj1; omega)
        simp only [List.getD_cons_succ, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [pieriWalkIvP_getD cv m _ (drop1IvP naIv) j' hj']; by_cases hlt : j' < 2 * m
        · have hlt2 : j' + 1 < 2 * (m + 1) - 1 := by omega
          have hi2 : (2 * (j' / 2) + 1) + 1 = 2 * (j' / 2) + 2 := (by omega); simp only [hlt, hlt2,
            ↓reduceIte]; rw [drop1IvP_getD, drop1IvP_getD, hi2]; rfl
        · have hnlt2 : ¬(j' + 1 < 2 * (m + 1) - 1) := (by omega); have htop : 2 * (m + 1) - 1 = 2 *
            m + 1 := (by omega); simp only [hlt, hnlt2, ↓reduceIte]; rw [htop, drop1IvP_getD]
/-- Primitive linear orbit projection accumulator avoiding `Int`/`Nat` dictionary reduction. -/
def swLOrbLinAuxP (o : ℕ) : ℕ → IvInt → List IvInt → IvInt
  | _, acc, [] => acc
  | j, acc, sj :: sjs =>
      let mIv : IvInt :=
        cond (Nat.beq j o) (Int.sub swScale swOrbPad, swScale)
          (Int.neg swOrbPad, swOrbPad)
      withForcedIv (ivAddIntP acc (ivMulIntP sj mIv)) fun acc' ↦
        swLOrbLinAuxP o (Nat.succ j) acc' sjs
theorem swLOrbLinAuxP_eq (o : ℕ) : ∀ (j : ℕ) (acc : IvInt) (stIv : List IvInt), swLOrbLinAuxP o j
  acc stIv = swLOrbLinAux o j acc stIv
  | _, _, [] => rfl
  | j, acc, sj :: sjs => by
    unfold swLOrbLinAuxP swLOrbLinAux
    have hm : (cond (Nat.beq j o) (Int.sub swScale swOrbPad, swScale) (Int.neg swOrbPad, swOrbPad))
      = (if j = o then (swScale - swOrbPad, swScale) else (-swOrbPad, swOrbPad)) := by
      rw [natBeq_eq_decide]; by_cases h : j = o
      · simp only [h, decide_true, Bool.cond_true, ↓reduceIte]; rfl
      · simp only [h, decide_false, Bool.cond_false, ↓reduceIte]; rfl
    simp only [withForcedIv_eq, ivAddIntP_eq, ivMulIntP_eq, hm]
    exact swLOrbLinAuxP_eq o (j + 1) _ sjs
/-- Primitive squared orbit projection interval. -/
def swLOrbSqIvP (stIv : List IvInt) (o : ℕ) : IvInt :=
  ivSqIntP (swLOrbLinAuxP o 0 (0, 0) stIv)
theorem swLOrbSqIvP_eq (stIv : List IvInt) (o : ℕ) : swLOrbSqIvP stIv o = swLOrbSqIv stIv o := by
  unfold swLOrbSqIvP swLOrbSqIv; rw [ivSqIntP_eq, swLOrbLinAuxP_eq]
/-- Primitive descending suffix tail intervals. -/
def swLTailSuffixIvsP (L : ℕ) (stIv : List IvInt) (cumIv : IvInt) : ℕ → List IvInt
  | 0 => []
  | m + 1 =>
      let c := Nat.sub L m
      cond (Nat.beq c L)
        [ivAddIntP (swLOrbSqIvP stIv (Nat.sub (Nat.mul 2 L) 1))
          (ivMulIntP cumIv (ivSqIntP (Int.sub swScale swOrbPad, swScale)))]
        (match swLTailSuffixIvsP L stIv cumIv m with
        | [] => []
        | nextIv :: rest =>
            let phIv := ivAddIntP
              (ivAddIntP (swLOrbSqIvP stIv (Nat.sub (Nat.mul 2 c) 1))
                (swLOrbSqIvP stIv (Nat.mul 2 c)))
              (ivMulIntP cumIv (0, Int.mul 2 swOrbPad))
            withForcedIv (ivAddIntP phIv nextIv) fun curIv ↦ curIv :: nextIv :: rest)
theorem swLTailSuffixIvsP_eq (L : ℕ) (stIv : List IvInt) (cumIv : IvInt) : ∀ (m : ℕ),
  swLTailSuffixIvsP L stIv cumIv m = swLTailSuffixIvs L stIv cumIv m
  | 0 => rfl
  | m + 1 => by
    unfold swLTailSuffixIvsP swLTailSuffixIvs; dsimp only; have hsub : Nat.sub L m = L - m := rfl
    rw [hsub, natBeq_eq_decide]; by_cases h : L - m = L
    · simp only [h, decide_true, Bool.cond_true, ↓reduceIte, ivAddIntP_eq, swLOrbSqIvP_eq,
        ivMulIntP_eq, ivSqIntP_eq]; rfl
    · simp only [h, decide_false, Bool.cond_false, ↓reduceIte, swLTailSuffixIvsP_eq L stIv cumIv m]
      cases swLTailSuffixIvs L stIv cumIv m with
      | nil => rfl
      | cons nextIv rest =>
          simp only [withForcedIv_eq, ivAddIntP_eq, swLOrbSqIvP_eq, ivMulIntP_eq]; rfl
/-- Primitive clamped monotone lower bounds. -/
def swLClampTailLbsP : List IvInt → List ℤ
  | [] => []
  | [ivL] => [maxZ 0 ivL.1]
  | iv :: rest =>
      match swLClampTailLbsP rest with
      | [] => [maxZ 0 iv.1]
      | nextLb :: lbs =>
          withForcedInt (maxZ nextLb (minZ swScale iv.1)) fun curLb ↦ curLb :: nextLb :: lbs
theorem swLClampTailLbsP_eq : ∀ (ivs : List IvInt), swLClampTailLbsP ivs = swLClampTailLbs ivs
  | [] => rfl | [ivL] => (by simp [swLClampTailLbsP, swLClampTailLbs, maxZ_eq])
  | iv :: iv2 :: rest => by
    have ih := swLClampTailLbsP_eq (iv2 :: rest); unfold swLClampTailLbsP swLClampTailLbs; rw [ih]
    cases swLClampTailLbs (iv2 :: rest) with
    | nil => simp [maxZ_eq] | cons nextLb lbs => simp [withForcedInt_eq, maxZ_eq, minZ_eq]
theorem ofNat_mul_self_eq_sq (x : ℕ) : Int.ofNat (Nat.mul x x) = (x : ℤ) ^ 2 := by
  rw [Int.ofNat_eq_natCast]; change ((x * x : ℕ) : ℤ) = (x : ℤ) ^ 2; push_cast; ring
theorem cvP_eq {L : ℕ} (p : SwLPulseRat L) : cond (beqZ p.vNum 0) (swScale, swScale) (ivPythagP
  p.vNum (Int.ofNat p.uvDen)).1 = (if p.vNum = 0 then (swScale, swScale) else (ivPythag p.vNum
  (p.uvDen : ℤ)).1) := by
  rw [beqZ_eq_decide, ivPythagP_eq, Int.ofNat_eq_natCast]; by_cases h : p.vNum = 0
  · simp only [h, decide_true, Bool.cond_true, ↓reduceIte]
  · simp only [h, decide_false, Bool.cond_false, ↓reduceIte]
/-! ## 2b. WHNF-Forced Integer `L2Ball` Trajectory & Bucket Certificate Checker -/
/-- Exact integer ceiling square root `⌈√n⌉` via `Nat.sqrt` and `Nat.beq`. -/
def ceilIsqrtNat (n : ℕ) : ℕ :=
  withForcedNat (Nat.sqrt n) fun s ↦
    cond (Nat.beq (Nat.mul s s) n) s (Nat.succ s)
theorem le_ceilIsqrtNat_sq (n : ℕ) : n ≤ (ceilIsqrtNat n) ^ 2 := by
  unfold ceilIsqrtNat; rw [withForcedNat_eq, natBeq_eq_decide]
  have hm : Nat.mul (Nat.sqrt n) (Nat.sqrt n) = Nat.sqrt n * Nat.sqrt n := rfl; rw [hm]
  by_cases h : Nat.sqrt n * Nat.sqrt n = n
  · simp only [h, decide_true, Bool.cond_true, sq]; exact le_rfl
  · simp only [h, decide_false, Bool.cond_false, sq]; exact (Nat.lt_succ_sqrt n).le
/-- WHNF-forcing wrapper for an `L2Ball` trajectory state `(cVec, rho, survUb)`. -/
def withForcedL2State {α : Type*} (s : List ℤ × ℕ × ℤ)
    (k : List ℤ × ℕ × ℤ → α) : α :=
  match s with
  | (cVec, rho, survUb) =>
      forceListId cVec fun cVec' ↦
        withForcedNat rho fun rho' ↦
          withForcedInt survUb fun survUb' ↦ k (cVec', rho', survUb')
theorem withForcedL2State_eq {α : Type*} (s : List ℤ × ℕ × ℤ) (k : List ℤ × ℕ × ℤ → α) :
  withForcedL2State s k = k s := by
  rcases s with ⟨cVec, rho, survUb⟩; simp only [withForcedL2State, forceListId_eq, withForcedNat_eq,
    withForcedInt_eq]
/-- Real center vector `c_j / 10^9` decoded from `c: List ℤ`. -/
noncomputable def decodeCenterReal (L : ℕ) (c : List ℤ) : Fin (2 * L) → ℝ :=
  fun j ↦ ((c.getD j.1 0 : ℤ) : ℝ) / (swScale : ℝ)
/-- Tail-recursive sum of squared magnitudes `acc + ∑ |c_j|^2` for `c: List ℤ`. -/
def swLSumSqAbs : List ℤ → ℕ → ℕ
  | [], acc => acc
  | cj :: cjs, acc =>
      withForcedNat cj.natAbs fun m ↦
        withForcedNat (Nat.add acc (Nat.mul m m)) fun acc' ↦
          swLSumSqAbs cjs acc'
theorem swLSumSqAbs_eq : ∀ (xs : List ℤ) (acc : ℕ), swLSumSqAbs xs acc = acc + ∑ i ∈ Finset.range
  xs.length, (xs.getD i 0).natAbs ^ 2
  | [], acc => by simp [swLSumSqAbs]
  | x :: xs, acc => by
    unfold swLSumSqAbs; rw [withForcedNat_eq, withForcedNat_eq]; change swLSumSqAbs xs (acc +
      x.natAbs * x.natAbs) = _; rw [swLSumSqAbs_eq xs (acc + x.natAbs * x.natAbs), List.length_cons,
      Finset.sum_range_succ']; simp only [List.getD_cons_zero, List.getD_cons_succ, sq]; omega
/-- Recentered midpoint `(lo + hi) / 2` and half-width `max (mid - lo) (hi - mid)` of `iv`. -/
def ivMidRad (iv : IvInt) : ℤ × ℕ :=
  withForcedInt (Int.ediv (Int.add iv.1 iv.2) 2) fun mid ↦
    (mid, (maxZ (Int.sub mid iv.1) (Int.sub iv.2 mid)).toNat)
theorem memIvInt_sub_center_sq_le {x : ℝ} {iv : IvInt} (h : memIvInt x iv) : (x - ((ivMidRad iv).1 :
  ℝ) / (swScale : ℝ)) ^ 2 ≤ (((ivMidRad iv).2 : ℝ) / (swScale : ℝ)) ^ 2 := by
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); rcases h with ⟨hlo, hhi⟩
  have hiv_le : iv.1 ≤ iv.2 := by
    have hdiv : (iv.1 : ℝ) / (swScale : ℝ) ≤ (iv.2 : ℝ) / (swScale : ℝ) := hlo.trans hhi; have hm :=
      mul_le_mul_of_nonneg_right hdiv hS.le
    rw [div_mul_cancel₀ _ hS.ne', div_mul_cancel₀ _ hS.ne'] at hm; exact_mod_cast hm
  unfold ivMidRad; rw [withForcedInt_eq, maxZ_eq]; change (x - ((((iv.1 + iv.2) / 2 : ℤ) : ℝ) /
    (swScale : ℝ))) ^ 2 ≤ ((((max ((iv.1 + iv.2) / 2 - iv.1) (iv.2 - (iv.1 + iv.2) / 2)).toNat : ℕ)
    : ℝ) / (swScale : ℝ)) ^ 2
  set mid : ℤ := (iv.1 + iv.2) / 2; set radZ : ℤ := max (mid - iv.1) (iv.2 - mid); have hrad0 : 0 ≤
    radZ := (by dsimp [radZ, mid]; omega); have hrad_eq : ((radZ.toNat : ℕ) : ℝ) = (radZ : ℝ) :=
    (by exact_mod_cast Int.toNat_of_nonneg hrad0); rw [hrad_eq]
  have h1 : (mid - radZ : ℝ) / (swScale : ℝ) ≤ x := by
    refine (div_le_div_of_nonneg_right ?_ hS.le).trans hlo; have hle : mid - radZ ≤ iv.1 :=
      (by dsimp [radZ]; omega); exact_mod_cast hle
  have h2 : x ≤ (mid + radZ : ℝ) / (swScale : ℝ) := by
    refine hhi.trans (div_le_div_of_nonneg_right ?_ hS.le); have hle : iv.2 ≤ mid + radZ :=
      (by dsimp [radZ]; omega); exact_mod_cast hle
  rw [sub_div] at h1; rw [add_div] at h2; rw [sq_le_sq, abs_of_nonneg (div_nonneg
    (by exact_mod_cast hrad0) hS.le), abs_le]; exact ⟨by linarith, by linarith⟩
/-- Recenter `nxtPtIv: List IvInt` into `(cNext, radSqSum)` with WHNF-forced fields. -/
def swLRecenterAndRadSq : List IvInt → List ℤ × ℕ
  | [] => ([], 0)
  | iv :: ivs =>
      match ivMidRad iv, swLRecenterAndRadSq ivs with
      | (mid, rad), (cs, acc) =>
          withForcedInt mid fun mid' ↦
            forceListId cs fun cs' ↦
              withForcedNat (Nat.add (Nat.mul rad rad) acc) fun acc' ↦
                (mid' :: cs', acc')
theorem swLRecenterAndRadSq_eq : ∀ (ivs : List IvInt), (swLRecenterAndRadSq ivs).1 = ivs.map (fun iv
  ↦ (ivMidRad iv).1) ∧ (swLRecenterAndRadSq ivs).2 = ∑ i ∈ Finset.range ivs.length, ((ivMidRad
  (ivs.getD i (0, 0))).2) ^ 2
  | [] => by simp [swLRecenterAndRadSq]
  | iv :: ivs => by
    rcases swLRecenterAndRadSq_eq ivs with ⟨h1, h2⟩; unfold swLRecenterAndRadSq
    rcases hmr : ivMidRad iv with ⟨mid, rad⟩; rcases hrec : swLRecenterAndRadSq ivs with ⟨cs, acc⟩
    rw [hrec] at h1 h2; dsimp only at h1 h2 ⊢; simp only [withForcedInt_eq, forceListId_eq,
      withForcedNat_eq]; refine ⟨by simp [hmr, h1], ?_⟩; change rad * rad + acc = _
    rw [List.length_cons, Finset.sum_range_succ']; simp only [List.getD_cons_zero,
      List.getD_cons_succ, hmr, h2, sq]; omega
theorem memIvIntVec_centerPtIvs {L : ℕ} {cVec : List ℤ} (hclen : cVec.length = 2 * L) : memIvIntVec
  (decodeCenterReal L cVec) (swLCenterPtIvs cVec) := by
  unfold swLCenterPtIvs; rw [withForcedList_eq, id_eq]; refine ⟨by simp [hclen], fun j ↦ ?_⟩
  have hj_lt : j.1 < cVec.length := by rw [hclen]; exact j.2
  have hget : (cVec.map fun cj ↦ (cj, cj)).getD j.1 (0, 0) = (cVec.getD j.1 0, cVec.getD j.1 0)
    := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
      (by simp [hj_lt]), List.getElem?_eq_getElem hj_lt, List.getElem_map]; simp
  rw [hget]; exact ⟨le_rfl, le_rfl⟩
/-- One WHNF-forced `L2Ball` conveyor pulse step `(cVec, rho, survUb) ↦ (cNext, rho',
  survUb')`,
  matching `SwL2BallEngine.eval_bucket_cert_l2ball` bit-for-bit via kernel-fast primitives. -/
def swLPulseStepL2 (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) (p : SwLPulseRat L) : List ℤ × ℕ × ℤ :=
  withForcedNat (swLSumSqAbs cVec 0) fun normSqC ↦
    withForcedNat (ceilIsqrtNat normSqC) fun normCUb ↦
      withForcedNat (Nat.add normCUb rho) fun sumR ↦
        withForcedInt
          (minZ swScale (ceilDivScaleP (Int.ofNat (Nat.mul sumR sumR))))
          fun oneMinusCumUb ↦
            withForcedInt (Int.add survUb oneMinusCumUb) fun survUb' ↦
              withForcedList (groverWalkP L trigIvs cVec) fun naIv ↦
                withForcedIv
                  (cond (beqZ p.vNum 0) (swScale, swScale)
                    (ivPythagP p.vNum (Int.ofNat p.uvDen)).1)
                  fun cv ↦
                    withForcedList (swLPieriAndWeakIvP L p cv naIv) fun nxtPtIv ↦
                      match swLRecenterAndRadSq nxtPtIv with
                      | (cNext, radSqSum) =>
                          forceListId cNext fun cNext' ↦
                            withForcedNat (Nat.add rho (ceilIsqrtNat radSqSum)) fun rho' ↦
                              (cNext', rho', survUb')
/-- Multi-pulse WHNF-forced `L2Ball` trajectory from `(cVec, rho, survUb)`. -/
def swLEvolutionL2Aux (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) :
    List (SwLPulseRat L) → List ℤ × ℕ × ℤ
  | [] => (cVec, rho, survUb)
  | p :: ps =>
      withForcedL2State (swLPulseStepL2 L trigIvs cVec rho survUb p) fun nxt ↦
        swLEvolutionL2Aux L trigIvs nxt.1 nxt.2.1 nxt.2.2 ps
/-- Multi-pulse `L2Ball` trajectory starting from `(c_0 = [10^9, 0,..., 0], rho = 0, survUb
  = 0)`. -/
def swLEvolutionL2 (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (pulses : List (SwLPulseRat L)) : List ℤ × ℕ × ℤ :=
  forceListId (swScale :: List.replicate (Nat.sub (Nat.mul 2 L) 1) 0) fun cInit ↦
    swLEvolutionL2Aux L trigIvs cInit 0 0 pulses
/-- Extract WHNF-forced `(stFinalIv, cumIv, (0, survUb))` from terminal `L2Ball` state
  `(cVec, rho, survUb)`, matching `SwL2BallEngine.eval_bucket_cert_l2ball` bit-for-bit. -/
def swLTerminalStateL2 (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) :
    List IvInt × IvInt × IvInt :=
  withForcedNat (swLSumSqAbs cVec 0) fun normSqK ↦
    withForcedNat (ceilIsqrtNat normSqK) fun normKUb ↦
      withForcedNat (Nat.sub (Nat.sqrt normSqK) rho) fun normKLb ↦
        withForcedNat (Nat.add normKUb rho) fun sumR ↦
          withForcedInt
            (minZ swScale (ceilDivScaleP (Int.ofNat (Nat.mul sumR sumR))))
            fun oneMinusCumUb ↦
              withForcedInt (maxZ 0 (Int.sub swScale oneMinusCumUb)) fun cumLo ↦
                withForcedInt
                  (minZ swScale
                    (Int.sub swScale (Int.ediv (Int.ofNat (Nat.mul normKLb normKLb)) swScale)))
                  fun cumHi ↦
                    let rhoZ := Int.ofNat rho
                    withForcedState
                      (cVec.map fun cj ↦ (Int.sub cj rhoZ, Int.add cj rhoZ),
                       (cumLo, cumHi),
                       (0, survUb))
                      id
/-- Pure-integer `L2Ball` bucket certificate checker (`swScale = 10^9`) for `2 ≤ L ≤ 8`,
  matching the exact signature of `checkSwLBucketCert`. -/
def checkSwLBucketCertL2 (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (pulses : List (SwLPulseRat L))
    (tailLbs : List ℤ) (survUb : ℤ) : Bool :=
  decide (1 ≤ pulses.length ∧ pulses.length ≤ 250 ∧ tailLbs.length = L ∧ 0 ≤ survUb ∧
    0 < tailLbs.getD 0 0 ∧ tailLbs.getD 0 0 ≤ swScale ∧ 0 ≤ tailLbs.getD (L - 1) 0) &&
  pulses.all swLPulseValid &&
  (List.range (L - 1)).all (fun i ↦ decide (tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0)) &&
  checkSwLBucketAngles L rMin rMax tauNum tauDen ratios trigIvs &&
  withForcedL2State (swLEvolutionL2 L trigIvs pulses) fun evol ↦
    withForcedState (swLTerminalStateL2 evol.1 evol.2.1 evol.2.2) fun outIv ↦
      withForcedIv (ivAddIntP (swLOrbSqIvP outIv.1 0) (ivMulIntP outIv.2.1 (0, swOrbPad)))
        fun p0Iv ↦
          withForcedIv (ivSubIntP (swScale, swScale) p0Iv) fun t1Iv ↦
            withForcedList (t1Iv :: swLTailSuffixIvsP L outIv.1 outIv.2.1 (Nat.sub L 1))
              fun tailIvs ↦
                forceListId (swLClampTailLbsP tailIvs) fun certLbs ↦
                  decide (outIv.2.2.2 ≤ survUb ∧ certLbs.length = L) &&
                  (List.range L).all fun i ↦ decide (tailLbs.getD i 0 ≤ certLbs.getD i 0)
/-! ## 3. Real Soundness of `L2Ball` Propagation & Terminal Extraction -/
theorem swLCenter_normSq_eq {L : ℕ} {c : List ℤ} (hclen : c.length = 2 * L) : swLNormSq
  (decodeCenterReal L c) = (swLSumSqAbs c 0 : ℝ) / (swScale : ℝ) ^ 2 := by
  unfold swLNormSq decodeCenterReal; simp_rw [div_pow, div_eq_mul_inv, ← Finset.sum_mul, ←
    div_eq_mul_inv]; congr 1; have hf := swLSumSqAbs_eq c 0; rw [zero_add] at hf; rw [hf,
    Nat.cast_sum, hclen]; push_cast; rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (((c.getD i 0).natAbs
    : ℝ)) ^ 2) (2 * L)]; refine Finset.sum_congr rfl fun j _ ↦ ?_; rcases c.getD j.1 0 with n | n
  · simp
  · simp [Int.negSucc_eq]
theorem l2Ball_oneMinusCum_le {L : ℕ} {st : Fin (2 * L) → ℝ} {cum : ℝ} {c : List ℤ} {rho : ℕ} (hclen
  : c.length = 2 * L) (hcons : swLNormSq st + cum = 1 ∧ 0 ≤ cum) (hball : swLNormSq (fun j ↦ st j -
  decodeCenterReal L c j) ≤ ((rho : ℝ) / (swScale : ℝ)) ^ 2) :
    let normCUb := ceilIsqrtNat (swLSumSqAbs c 0)
    let oneMinusCumUb := min swScale (-((-(((normCUb + rho : ℕ) : ℤ) ^ 2)) / swScale))
    1 - cum ≤ (oneMinusCumUb : ℝ) / (swScale : ℝ) := by
  intro normCUb oneMinusCumUb; have hS_pos : (0 : ℤ) < swScale := (by unfold swScale; omega)
  have hS : (0 : ℝ) < (swScale : ℝ) := by unfold swScale; norm_num
  have hc_norm : swLNormSq (decodeCenterReal L c) ≤ ((normCUb : ℝ) / (swScale : ℝ)) ^ 2 := by
    rw [swLCenter_normSq_eq hclen, div_pow]; refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    exact_mod_cast le_ceilIsqrtNat_sq (swLSumSqAbs c 0)
  have hst_norm : swLNormSq st ≤ (((normCUb + rho : ℕ) : ℝ) / (swScale : ℝ)) ^ 2 := by
    have htri := swLNormSq_add_le_sq (div_nonneg (Nat.cast_nonneg normCUb) hS.le) (div_nonneg
      (Nat.cast_nonneg rho) hS.le) hc_norm hball; have heq_v : st = fun j ↦ decodeCenterReal L c j +
      (st j - decodeCenterReal L c j) := (by ext j; ring); have heq_r : (normCUb : ℝ) / (swScale :
      ℝ) + (rho : ℝ) / (swScale : ℝ) = ((normCUb + rho : ℕ) : ℝ) / (swScale : ℝ) :=
      (by push_cast; ring)
    rwa [← heq_v, heq_r] at htri
  set q : ℤ := ((normCUb + rho : ℕ) : ℤ) ^ 2; set ceilZ : ℤ := -((-q) / swScale)
  have hceil_ub : (((normCUb + rho : ℕ) : ℝ) / (swScale : ℝ)) ^ 2 ≤ (ceilZ : ℝ) / (swScale : ℝ)
    := by
    rw [div_pow, sq (swScale : ℝ), ← div_div]; refine div_le_div_of_nonneg_right ?_ hS.le
    have hd := real_le_neg_ediv_neg_pos q swScale hS_pos
    have hq_eq : (((normCUb + rho : ℕ) : ℝ)) ^ 2 = (q : ℝ) := by dsimp [q]; push_cast; rfl
    rwa [hq_eq]
  have heq1 : 1 - cum = swLNormSq st := by linarith [hcons.1]
  have hns_eq : oneMinusCumUb = min swScale ceilZ := rfl; rw [heq1, hns_eq, Int.cast_min]
  rcases le_total (swScale : ℝ) (ceilZ : ℝ) with h | h
  · rw [min_eq_left h, div_self hS.ne']; linarith [hcons.1, hcons.2]
  · rw [min_eq_right h]; exact hst_norm.trans hceil_ub
theorem swLPulseStepL2_sound {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} {trigIvs : List (IvInt ×
  IvInt)} (hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (htrig : ∀ w : Fin L, memIvInt (cs
  w).1 (trigIvs.getD w.1 ((0, 0), (0, 0))).1 ∧ memIvInt (cs w).2 (trigIvs.getD w.1 ((0, 0), (0,
  0))).2) {p : SwLPulseRat L} (hp : swLPulseValid p = true) {st : Fin (2 * L) → ℝ} {cum surv : ℝ}
  {cVec : List ℤ} {rho : ℕ} {survUb : ℤ} (hclen : cVec.length = 2 * L) (hin : swLNormSq st + cum = 1
  ∧ 0 ≤ cum ∧ cum ≤ 1 ∧ 0 ≤ surv) (hball : swLNormSq (fun j ↦ st j - decodeCenterReal L cVec j) ≤
  ((rho : ℝ) / (swScale : ℝ)) ^ 2) (hsurv : surv ≤ (survUb : ℝ) / (swScale : ℝ)) :
    let outR := swLPulseStepReal L hL cs st cum surv p
    let outL2 := swLPulseStepL2 L trigIvs cVec rho survUb p
    outL2.1.length = 2 * L ∧ (swLNormSq outR.1 + outR.2.1 = 1 ∧ 0 ≤ outR.2.1 ∧ outR.2.1 ≤ 1 ∧ 0 ≤
      outR.2.2) ∧ swLNormSq (fun j ↦ outR.1 j - decodeCenterReal L outL2.1 j) ≤ ((outL2.2.1 : ℝ) /
      (swScale : ℝ)) ^ 2 ∧ outR.2.2 ≤ (outL2.2.2 : ℝ) / (swScale : ℝ) := by
  intro outR outL2; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hp_den : 0 < p.uvDen := by unfold swLPulseValid at hp; rwa [decide_eq_true_eq] at hp
  have hin_next := swLPulseStepReal_normSq_add_cum hL hcs st cum surv hp hin; have hcum_step :=
    l2Ball_oneMinusCum_le hclen ⟨hin.1, hin.2.1⟩ hball
  set cv : IvInt := if p.vNum = 0 then (swScale, swScale) else (ivPythag p.vNum (p.uvDen : ℤ)).1
  have hcv : memIvInt (swLCayleyCos p.vNum p.uvDen) cv := by
    dsimp [cv]; by_cases hv0 : p.vNum = 0
    · simp only [hv0, ↓reduceIte]; have hd_ne : (p.uvDen : ℝ) ^ 2 ≠ 0 := (by positivity)
      have hc0 : swLCayleyCos 0 p.uvDen = 1 := by unfold swLCayleyCos; simp [div_self hd_ne]
      rw [hc0]; exact memIvInt_one
    · simp only [hv0, ↓reduceIte]; exact (memIvInt_ivPythag p.vNum hp_den).1
  set naIv := swLGroverRotIv L trigIvs (swLCenterPtIvs cVec)
  set nxtPtIv := swLPieriAndWeakIv L p cv naIv; have hna : memIvIntVec (swLGroverRotVec L cs
    (decodeCenterReal L cVec)) naIv := memIvIntVec_groverRot htrig (memIvIntVec_centerPtIvs hclen)
  have hpt : memIvIntVec (swLPulseStepReal L hL cs (decodeCenterReal L cVec) 0 0 p).1 nxtPtIv :=
    memIvIntVec_pieriAndWeak hL hp_den hcv hna; rcases swLRecenterAndRadSq_eq nxtPtIv with ⟨hrec1,
    hrec2⟩; rcases hrec : swLRecenterAndRadSq nxtPtIv with ⟨cNext, radSqSum⟩
  rw [hrec] at hrec1 hrec2; dsimp only at hrec1 hrec2
  have houtL2_eq : outL2 = (cNext, rho + ceilIsqrtNat radSqSum, survUb + min swScale
    (-((-(((ceilIsqrtNat (swLSumSqAbs cVec 0) + rho : ℕ) : ℤ) ^ 2)) / swScale))) := by
    have hrec_raw : swLRecenterAndRadSq (swLPieriAndWeakIv L p (if p.vNum = 0 then (swScale,
      swScale) else (ivPythag p.vNum (p.uvDen : ℤ)).1) (swLGroverRotIv L trigIvs (swLCenterPtIvs
      cVec))) = (cNext, radSqSum) := hrec; dsimp only [outL2]; unfold swLPulseStepL2
    simp only [withForcedNat_eq, withForcedInt_eq, withForcedList_eq, withForcedIv_eq, minZ_eq,
      ceilDivScaleP_eq, ofNat_mul_self_eq_sq, groverWalkP_eq, cvP_eq, swLPieriAndWeakIvP_eq]
    rw [hrec_raw]; simp only [forceListId_eq]; rfl
  rw [houtL2_eq]; dsimp only; have hcNext_len : cNext.length = 2 * L :=
    (by rw [hrec1, List.length_map, hpt.1])
  have hsurv_next : outR.2.2 ≤ ((survUb + min swScale (-((-(((ceilIsqrtNat (swLSumSqAbs cVec 0) +
    rho : ℕ) : ℤ) ^ 2)) / swScale)) : ℤ) : ℝ) / (swScale : ℝ) := by
    have h2 : outR.2.2 = surv + (1 - cum) := rfl; rw [h2, Int.cast_add, add_div]
    exact add_le_add hsurv hcum_step
  set fc := (swLPulseStepReal L hL cs (decodeCenterReal L cVec) 0 0 p).1; have hlip : swLNormSq (fun
    j ↦ outR.1 j - fc j) ≤ ((rho : ℝ) / (swScale : ℝ)) ^ 2 := (swLPulseStepReal_distSq_le hL hcs hp
    st (decodeCenterReal L cVec) cum surv 0 0).trans hball; set drho : ℕ := ceilIsqrtNat radSqSum
  have hpt_err : swLNormSq (fun j ↦ fc j - decodeCenterReal L cNext j) ≤ ((drho : ℝ) / (swScale :
    ℝ)) ^ 2 := by
    have hcoord : ∀ j : Fin (2 * L), (fc j - decodeCenterReal L cNext j) ^ 2 ≤ (((ivMidRad
      (nxtPtIv.getD j.1 (0, 0))).2 : ℝ) / (swScale : ℝ)) ^ 2 := fun j ↦ by
      have hj_lt : j.1 < nxtPtIv.length := by rw [hpt.1]; exact j.2
      have hc_get : cNext.getD j.1 0 = (ivMidRad (nxtPtIv.getD j.1 (0, 0))).1 := by
        rw [hrec1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
          (by simp [hj_lt]), List.getElem?_eq_getElem hj_lt, List.getElem_map]; simp
      unfold decodeCenterReal; rw [hc_get]; exact memIvInt_sub_center_sq_le (hpt.2 j)
    have hsum_le : swLNormSq (fun j ↦ fc j - decodeCenterReal L cNext j) ≤ (∑ j : Fin (2 * L),
      (((ivMidRad (nxtPtIv.getD j.1 (0, 0))).2 : ℝ)) ^ 2) / (swScale : ℝ) ^ 2 := by
      unfold swLNormSq; rw [div_eq_mul_inv, Finset.sum_mul]; refine Finset.sum_le_sum fun j _ ↦ ?_
      exact (hcoord j).trans_eq (by rw [div_pow, div_eq_mul_inv])
    have hrad_sum : ∑ j : Fin (2 * L), (((ivMidRad (nxtPtIv.getD j.1 (0, 0))).2 : ℝ)) ^ 2 =
      (radSqSum : ℝ) := by
      rw [hrec2, hpt.1, Nat.cast_sum]; push_cast; exact Fin.sum_univ_eq_sum_range (fun i ↦
        (((ivMidRad (nxtPtIv.getD i (0, 0))).2 : ℝ)) ^ 2) (2 * L)
    rw [hrad_sum] at hsum_le; refine hsum_le.trans ?_; rw [div_pow]
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _); exact_mod_cast le_ceilIsqrtNat_sq radSqSum
  have htri := swLNormSq_add_le_sq (div_nonneg (Nat.cast_nonneg rho) hS.le) (div_nonneg
    (Nat.cast_nonneg drho) hS.le) hlip hpt_err; have heq_vec : (fun j ↦ outR.1 j - decodeCenterReal
    L cNext j) = (fun j ↦ (outR.1 j - fc j) + (fc j - decodeCenterReal L cNext j)) :=
    (by ext j; ring); have heq_rad : (rho : ℝ) / (swScale : ℝ) + (drho : ℝ) / (swScale : ℝ) = ((rho
    + drho : ℕ) : ℝ) / (swScale : ℝ) := (by push_cast; ring)
  rw [← heq_vec, heq_rad] at htri; exact ⟨hcNext_len, hin_next, htri, hsurv_next⟩
theorem swLEvolutionL2Aux_sound {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} {trigIvs : List (IvInt ×
  IvInt)} (hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (htrig : ∀ w : Fin L, memIvInt (cs
  w).1 (trigIvs.getD w.1 ((0, 0), (0, 0))).1 ∧ memIvInt (cs w).2 (trigIvs.getD w.1 ((0, 0), (0,
  0))).2) (pulses : List (SwLPulseRat L)) (hp : pulses.all swLPulseValid = true) {st : Fin (2 * L) →
  ℝ} {cum surv : ℝ} {cVec : List ℤ} {rho : ℕ} {survUb : ℤ} (hclen : cVec.length = 2 * L) (hin :
  swLNormSq st + cum = 1 ∧ 0 ≤ cum ∧ cum ≤ 1 ∧ 0 ≤ surv) (hball : swLNormSq (fun j ↦ st j -
  decodeCenterReal L cVec j) ≤ ((rho : ℝ) / (swScale : ℝ)) ^ 2) (hsurv : surv ≤ (survUb : ℝ) /
  (swScale : ℝ)) :
    let outR := swLEvolutionRealAux L hL cs st cum surv pulses
    let outL2 := swLEvolutionL2Aux L trigIvs cVec rho survUb pulses
    outL2.1.length = 2 * L ∧ (swLNormSq outR.1 + outR.2.1 = 1 ∧ 0 ≤ outR.2.1 ∧ outR.2.1 ≤ 1 ∧ 0 ≤
      outR.2.2) ∧ swLNormSq (fun j ↦ outR.1 j - decodeCenterReal L outL2.1 j) ≤ ((outL2.2.1 : ℝ) /
      (swScale : ℝ)) ^ 2 ∧ outR.2.2 ≤ (outL2.2.2 : ℝ) / (swScale : ℝ) := by
  induction pulses generalizing st cum surv cVec rho survUb with
  | nil => exact ⟨hclen, hin, hball, hsurv⟩
  | cons p ps ih =>
    rw [List.all_cons, Bool.and_eq_true] at hp; unfold swLEvolutionRealAux swLEvolutionL2Aux
    rw [withForcedL2State_eq]
    rcases swLPulseStepL2_sound hL hcs htrig hp.1 hclen hin hball hsurv with ⟨hlen', hin', hball',
      hsurv'⟩; exact ih hp.2 hlen' hin' hball' hsurv'
theorem swLTerminalStateL2_sound {L : ℕ} {st : Fin (2 * L) → ℝ} {cum surv : ℝ} {cVec : List ℤ} {rho
  : ℕ} {survUb : ℤ} (hclen : cVec.length = 2 * L) (hin : swLNormSq st + cum = 1 ∧ 0 ≤ cum ∧ cum ≤ 1
  ∧ 0 ≤ surv) (hball : swLNormSq (fun j ↦ st j - decodeCenterReal L cVec j) ≤ ((rho : ℝ) / (swScale
  : ℝ)) ^ 2) (hsurv : surv ≤ (survUb : ℝ) / (swScale : ℝ)) :
    let outIv := swLTerminalStateL2 cVec rho survUb
    memIvIntVec st outIv.1 ∧ memIvInt cum outIv.2.1 ∧ memIvInt surv outIv.2.2 := by
  intro outIv; have hS_pos : (0 : ℤ) < swScale := (by unfold swScale; omega); have hS : (0 : ℝ) <
    (swScale : ℝ) := (by unfold swScale; norm_num)
  have hvec : memIvIntVec st (cVec.map fun cj ↦ (cj - (rho : ℤ), cj + (rho : ℤ))) := by
    refine ⟨by simp [hclen], fun j ↦ ?_⟩; have hj_lt : j.1 < cVec.length :=
      (by rw [hclen]; exact j.2)
    have hget : (cVec.map fun cj ↦ (cj - (rho : ℤ), cj + (rho : ℤ))).getD j.1 (0, 0) = (cVec.getD
      j.1 0 - (rho : ℤ), cVec.getD j.1 0 + (rho : ℤ)) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
        (by simp [hj_lt]), List.getElem?_eq_getElem hj_lt, List.getElem_map]; simp
    rw [hget]
    have hsq_j : (st j - decodeCenterReal L cVec j) ^ 2 ≤ ((rho : ℝ) / (swScale : ℝ)) ^ 2 := by
      have hle_sum : (st j - decodeCenterReal L cVec j) ^ 2 ≤ swLNormSq (fun i ↦ st i -
        decodeCenterReal L cVec i) := by
        unfold swLNormSq; exact Finset.single_le_sum (f := fun i ↦ (st i - decodeCenterReal L cVec
          i) ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
      exact hle_sum.trans hball
    rw [sq_le_sq, abs_of_nonneg (div_nonneg (Nat.cast_nonneg rho) hS.le), abs_le] at hsq_j
    unfold decodeCenterReal at hsq_j; unfold memIvInt; dsimp only; push_cast; rw [sub_div, add_div]
    exact ⟨by linarith [hsq_j.1], by linarith [hsq_j.2]⟩
  have h1_sub_le := l2Ball_oneMinusCum_le hclen ⟨hin.1, hin.2.1⟩ hball; set normSqK : ℕ :=
    swLSumSqAbs cVec 0; set normKLb : ℕ := Nat.sqrt normSqK - rho
  have hlb_norm : ((normKLb : ℝ) / (swScale : ℝ)) ^ 2 ≤ swLNormSq st := by
    have hst_nn : 0 ≤ swLNormSq st := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    by_cases hle_r : rho ≤ Nat.sqrt normSqK
    · set rSt : ℝ := √(swLNormSq st); have hrSt_sq : swLNormSq st ≤ rSt ^ 2 := (Real.sq_sqrt
        hst_nn).symm.le
      have hball_rev : swLNormSq (fun j ↦ decodeCenterReal L cVec j - st j) ≤ ((rho : ℝ) / (swScale
        : ℝ)) ^ 2 := by
        have heq_sq : swLNormSq (fun j ↦ decodeCenterReal L cVec j - st j) =
            swLNormSq (fun j ↦ st j - decodeCenterReal L cVec j) :=
          Finset.sum_congr rfl fun _ _ ↦ by ring
        rwa [heq_sq]
      have htri := swLNormSq_add_le_sq (Real.sqrt_nonneg _) (div_nonneg (Nat.cast_nonneg rho) hS.le)
        hrSt_sq hball_rev; have heq_c : decodeCenterReal L cVec = fun j ↦ st j + (decodeCenterReal L
        cVec j - st j) := (by ext j; ring); rw [← heq_c, swLCenter_normSq_eq hclen] at htri
      have hsqrt_le : ((Nat.sqrt normSqK : ℝ) / (swScale : ℝ)) ^ 2 ≤ (normSqK : ℝ) / (swScale : ℝ) ^
        2 := by
        rw [div_pow]; refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
        have hnat : Nat.sqrt normSqK * Nat.sqrt normSqK ≤ normSqK := Nat.sqrt_le normSqK; rw [sq]
        exact_mod_cast hnat
      have hsq_both := hsqrt_le.trans htri; have hlhs_nn : 0 ≤ (Nat.sqrt normSqK : ℝ) / (swScale :
        ℝ) := div_nonneg (Nat.cast_nonneg _) hS.le; have hrhs_nn : 0 ≤ rSt + (rho : ℝ) / (swScale :
        ℝ) := add_nonneg (Real.sqrt_nonneg _) (div_nonneg (Nat.cast_nonneg _) hS.le)
      have hlin : (Nat.sqrt normSqK : ℝ) / (swScale : ℝ) ≤ rSt + (rho : ℝ) / (swScale : ℝ) :=
        (by rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]; exact Real.sqrt_le_sqrt hsq_both)
      have hlb_le : (normKLb : ℝ) / (swScale : ℝ) ≤ rSt :=
        (by dsimp [normKLb]; rw [Nat.cast_sub hle_r, sub_div]; linarith); exact (pow_le_pow_left₀
        (div_nonneg (Nat.cast_nonneg _) hS.le) hlb_le 2).trans_eq (Real.sq_sqrt hst_nn)
    · have hz : normKLb = 0 := (by dsimp [normKLb]; omega); rw [hz]; simpa using hst_nn
  set oneMinusCumUb : ℤ := min swScale (-((-(((ceilIsqrtNat normSqK + rho : ℕ) : ℤ) ^ 2)) /
    swScale))
  have hcum_lo : ((max 0 (swScale - oneMinusCumUb) : ℤ) : ℝ) / (swScale : ℝ) ≤ cum := by
    rw [Int.cast_max, Int.cast_zero]
    rcases le_total (0 : ℝ) ((swScale - oneMinusCumUb : ℤ) : ℝ) with h | h
    · rw [max_eq_right h]; push_cast; rw [sub_div, div_self hS.ne']; linarith [h1_sub_le]
    · rw [max_eq_left h, zero_div]; exact hin.2.1
  set qLb : ℤ := ((normKLb * normKLb : ℕ) : ℤ)
  have hqLb_le : ((qLb / swScale : ℤ) : ℝ) / (swScale : ℝ) ≤ 1 - cum := by
    have hd := div_le_div_of_nonneg_right (ediv_pos_le_real qLb swScale hS_pos) hS.le
    have hq_eq : (qLb : ℝ) / (swScale : ℝ) / (swScale : ℝ) = ((normKLb : ℝ) / (swScale : ℝ)) ^ 2 :=
      (by dsimp [qLb]; push_cast; rw [div_pow, sq (swScale : ℝ), sq (normKLb : ℝ), div_div])
    rw [hq_eq] at hd; linarith [hd.trans hlb_norm, hin.1]
  have hcum_hi : cum ≤ ((min swScale (swScale - qLb / swScale) : ℤ) : ℝ) / (swScale : ℝ) := by
    rw [Int.cast_min]; rcases le_total (swScale : ℝ) ((swScale - qLb / swScale : ℤ) : ℝ) with h | h
    · rw [min_eq_left h, div_self hS.ne']; exact hin.2.2.1
    · rw [min_eq_right h]; push_cast; rw [sub_div, div_self hS.ne']; linarith [hqLb_le]
  have hsurv_mem : memIvInt surv (0, survUb) :=
    (by unfold memIvInt; dsimp only; rw [Int.cast_zero, zero_div]; exact ⟨hin.2.2.2, hsurv⟩)
  have houtIv_eq : outIv = (cVec.map fun cj ↦ (cj - (rho : ℤ), cj + (rho : ℤ)), (max 0 (swScale -
    oneMinusCumUb), min swScale (swScale - qLb / swScale)), (0, survUb)) := by
    dsimp only [outIv, oneMinusCumUb, qLb, normKLb, normSqK]; unfold swLTerminalStateL2; dsimp only
    simp only [withForcedNat_eq, withForcedInt_eq, withForcedState_eq, id_eq, minZ_eq, maxZ_eq,
      ceilDivScaleP_eq]; rw [ofNat_mul_self_eq_sq]; simp only [Int.ofNat_eq_natCast]; rfl
  rw [houtIv_eq]; exact ⟨hvec, ⟨hcum_lo, hcum_hi⟩, hsurv_mem⟩
theorem memIvInt_evolutionL2 {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} {trigIvs : List (IvInt ×
  IvInt)} (hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (htrig : ∀ w : Fin L, memIvInt (cs
  w).1 (trigIvs.getD w.1 ((0, 0), (0, 0))).1 ∧ memIvInt (cs w).2 (trigIvs.getD w.1 ((0, 0), (0,
  0))).2) (pulses : List (SwLPulseRat L)) (hp : pulses.all swLPulseValid = true) :
    let outR := swLEvolutionReal L hL cs pulses; let evol := swLEvolutionL2 L trigIvs pulses
    let outIv := swLTerminalStateL2 evol.1 evol.2.1 evol.2.2
    memIvIntVec outR.1 outIv.1 ∧ memIvInt outR.2.1 outIv.2.1 ∧ memIvInt outR.2.2 outIv.2.2 := by
  have hS : (swScale : ℝ) ≠ 0 := by unfold swScale; norm_num
  set cInit : List ℤ := swScale :: List.replicate (2 * L - 1) 0
  have hc_len : cInit.length = 2 * L := (by simp [cInit]; omega); set stInit : Fin (2 * L) → ℝ :=
    fun j ↦ if j.1 = 0 then 1 else 0
  have hin0 : swLNormSq stInit + 0 = 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 0 := by
    refine ⟨?_, le_rfl, zero_le_one, le_rfl⟩; unfold swLNormSq; rw [sum_fin_interior_pairs hL]
    have hn0 : 2 * L - 1 ≠ 0 := (by omega); simp [stInit, hn0]
  have hball0 : swLNormSq (fun j ↦ stInit j - decodeCenterReal L cInit j) ≤ (((0 : ℕ) : ℝ) /
    (swScale : ℝ)) ^ 2 := by
    have hz : (fun j : Fin (2 * L) ↦ stInit j - decodeCenterReal L cInit j) = fun _ ↦ 0 := by
      ext ⟨_ | k, hk⟩
      · unfold decodeCenterReal; simp [stInit, cInit, div_self hS]
      · have hk_lt : k < 2 * L - 1 := (by omega); unfold decodeCenterReal; simp [stInit, cInit,
          List.getD_eq_getElem?_getD, hk_lt]
    rw [hz]; simp [swLNormSq]
  have hsurv0 : (0 : ℝ) ≤ ((0 : ℤ) : ℝ) / (swScale : ℝ) := by simp
  have hevol_eq : swLEvolutionL2 L trigIvs pulses = swLEvolutionL2Aux L trigIvs cInit 0 0 pulses :=
    (by unfold swLEvolutionL2; rw [forceListId_eq]; rfl)
  rcases swLEvolutionL2Aux_sound hL hcs htrig pulses hp hc_len hin0 hball0 hsurv0 with ⟨hlenF, hinF,
    hballF, hsurvF⟩; intro outR evol outIv; dsimp only [outR, outIv, evol, swLEvolutionReal]
  rw [hevol_eq]; exact swLTerminalStateL2_sound hlenF hinF hballF hsurvF
/-! ## 4. Top-Level `L2Ball` Bucket, `m = 1` Stage & `MultiSW_L` Stage Soundness -/
theorem checkSwLBucketCertL2_sound {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb : ℤ}
  (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk : checkSwLBucketCertL2 L rMin rMax
  tauNum tauDen ratios trigIvs pulses tailLbs survUb = true) : ∃ (hL2 : 2 ≤ L), L ≤ 8 ∧ L ≤ r ∧ r ≤
  1024 ∧ 1 ≤ pulses.length ∧ pulses.length ≤ 250 ∧ pulses.all swLPulseValid = true ∧ tailLbs.length
  = L ∧ 0 ≤ survUb ∧ 0 < tailLbs.getD 0 0 ∧ tailLbs.getD 0 0 ≤ swScale ∧ 0 ≤ tailLbs.getD (L - 1) 0
  ∧ (∀ i : ℕ, i + 1 < L → tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0) ∧ ∀ (M : Fin (2 * L) → Fin (2 *
  L) → ℝ), IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs pulses
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        0 ≤ out.2.2 ∧ out.2.2 ≤ (survUb : ℝ) / (swScale : ℝ) ∧ ∀ c ∈ Finset.Icc 1 L, ((tailLbs.getD
          (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ ∑ h ∈ Finset.Icc c L, p h := by
  unfold checkSwLBucketCertL2 at hchk
  simp only [withForcedL2State_eq, withForcedState_eq, withForcedIv_eq, withForcedList_eq,
    forceListId_eq, ivAddIntP_eq, swLOrbSqIvP_eq, ivMulIntP_eq, ivSubIntP_eq, swLTailSuffixIvsP_eq,
    swLClampTailLbsP_eq, Bool.and_eq_true, decide_eq_true_eq] at hchk; rcases hchk with ⟨⟨⟨⟨⟨hp1,
    hp250, htl_len, hsurv0, htl0_pos, htl0_le, htlL0⟩, hp_val⟩, htl_mono⟩, hang⟩, ⟨hsurv_ub,
    hcl_len⟩, htl_le⟩
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at htl_mono htl_le
  rcases checkSwLBucketAngles_sound hn96 hmin hmax hang with ⟨hL2, hL8, hLr, hr1024, _, htrig⟩
  refine ⟨hL2, hL8, hLr, hr1024, hp1, hp250, hp_val, htl_len, hsurv0, htl0_pos, htl0_le, htlL0, fun
    i hi ↦ htl_mono i (by omega), ?_⟩; intro M hM K_blk cs out p
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); have hcs_unit : ∀ w : Fin L,
    (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum hL2 hcs_unit pulses hp_val with ⟨hcons, hcum0, _, hsurv_nn⟩
  rcases memIvInt_evolutionL2 (cs := cs) hL2 hcs_unit htrig pulses hp_val with ⟨hst_mem, hcum_mem,
    hsurv_mem⟩; set evol := swLEvolutionL2 L trigIvs pulses
  set outIv := swLTerminalStateL2 evol.1 evol.2.1 evol.2.2; have hsurv_le : out.2.2 ≤ (survUb : ℝ) /
    (swScale : ℝ) := hsurv_mem.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hsurv_ub)
    hS.le); have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg hL2 M out.1 hcum0 h
  have hp_sum1 : ∑ h ∈ Finset.range (L + 1), p h = 1 := swLAttemptProbReal_sum_one hL2 hM hcons
  have hp0_mem : memIvInt (p 0) (ivAddInt (swLOrbSqIv outIv.1 0) (ivMulInt outIv.2.1 (0, swOrbPad)))
    := by
    dsimp [p]; unfold swLAttemptProbReal; simp only [↓reduceIte]; have ho0 : memIvInt ((swLOrbitProj
      M out.1 ⟨0, by omega⟩) ^ 2) (swLOrbSqIv outIv.1 0) := memIvInt_swLOrbSqIv hM hst_mem ⟨0,
      by omega⟩
    have hoff0 : |M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩| ≤ (1 : ℝ) / 10 ^ 9 :=
      hM.2.2.2 _ _ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
    have hsq0 : (M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 ≤ (1 : ℝ) / 10 ^ 18 :=
      (by rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hoff0 2).trans_eq (by norm_num))
    have hpad0 : memIvInt ((M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2) (0, swOrbPad) := by
      unfold memIvInt swScale swOrbPad; dsimp only
      exact ⟨by linarith [sq_nonneg (M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩)], by linarith⟩
    exact memIvInt_ivAddInt ho0 (memIvInt_ivMulInt hcum_mem hpad0)
  have ht1_eq : ∑ h ∈ Finset.Icc 1 L, p h = 1 - p 0 := by
    have hsplit : ∑ h ∈ Finset.range (L + 1), p h = p 0 + ∑ h ∈ Finset.Icc 1 L, p h := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < L + 1),
        Finset.Ico_add_one_right_eq_Icc]
    linarith [hp_sum1, hsplit]
  have ht1_mem : memIvInt (∑ h ∈ Finset.Icc 1 L, p h) (ivSubInt (swScale, swScale) (ivAddInt
    (swLOrbSqIv outIv.1 0) (ivMulInt outIv.2.1 (0, swOrbPad)))) :=
    (by rw [ht1_eq]; exact memIvInt_ivSubInt memIvInt_one hp0_mem)
  rcases memIvInt_swLTailSuffixIvs hL2 hM hst_mem hcum_mem (L - 1) le_rfl with ⟨hsfx_len, hsfx⟩
  set tailIvs := ivSubInt (swScale, swScale) (ivAddInt (swLOrbSqIv outIv.1 0) (ivMulInt outIv.2.1
    (0, swOrbPad))) :: swLTailSuffixIvs L outIv.1 outIv.2.1 (L - 1)
  have htailIvs_len : tailIvs.length = L := by dsimp [tailIvs]; simp [hsfx_len]; omega
  set tReal : ℕ → ℝ := fun c ↦ ∑ h ∈ Finset.Icc c L, p h
  have hclamp := swLClampTailLbs_sound tailIvs tReal 1
    (fun i hi ↦ by
      rw [htailIvs_len] at hi; have ht0 : 0 ≤ tReal (1 + i) := Finset.sum_nonneg fun h _ ↦ hp_nn h
      have ht1 : tReal (1 + i) ≤ 1 := by
        have hsub : Finset.Icc (1 + i) L ⊆ Finset.range (L + 1) := fun h hh ↦ by
          rw [Finset.mem_Icc] at hh; rw [Finset.mem_range]; omega
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun h _ _ ↦ hp_nn h).trans_eq hp_sum1
      refine ⟨ht0, ht1, ?_⟩; rcases i with _ | i'
      · simpa [tailIvs, tReal] using ht1_mem.1
      · have hi' : i' < L - 1 := (by omega); have hmem := hsfx i' hi'
        have hcc_eq : L + 1 - (L - 1) + i' = 1 + (i' + 1) := (by omega); rw [hcc_eq] at hmem
        simpa [tailIvs, tReal] using hmem.1)
    (fun i hi ↦ by
      rw [htailIvs_len] at hi; dsimp [tReal]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_left (by omega)) fun h _ _ ↦ hp_nn h)
  refine ⟨hsurv_nn, hsurv_le, fun c hc ↦ ?_⟩; rw [Finset.mem_Icc] at hc; have hidx : c - 1 < L :=
    (by omega); have hle_cert := htl_le (c - 1) hidx
  have hcert_real := hclamp.2 (c - 1) (by rw [htailIvs_len]; exact hidx)
  have h1c : 1 + (c - 1) = c := (by omega); rw [h1c] at hcert_real
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hle_cert) hS.le).trans hcert_real
/-- Drop-in `m = 1` Bellman stage soundness under `checkSwLBucketCertL2`, matching the exact
  signature and conclusion of `checkSwLM1Stage_sound`. -/
theorem checkSwLM1StageL2_sound {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt} {trigIvs :
  List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb vScale : ℤ}
  {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hbkt : checkSwLBucketCertL2
  L rMin rMax tauNum tauDen ratios trigIvs pulses tailLbs survUb = true) (hstep :
  checkSwLM1StepTable L r tauNum tauDen L tailLbs survUb vScale vTable = true) : ∃ (hL2 : 2 ≤ L), L
  ≤ 8 ∧ L ≤ r ∧ pulses.all swLPulseValid = true ∧ ∀ (M : Fin (2 * L) → Fin (2 * L) → ℝ),
  IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs pulses
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (L : ℝ) + ∑ h ∈ Finset.Icc 1 L, p h * V (r - h)) /
          pSucc ≤ V r := by
  rcases checkSwLBucketCertL2_sound hn96 hmin hmax hbkt with ⟨hL2, hL8, hLr, hr1024, _, _, hp_val,
    _, _, htl0_pos, _, _, _, hbkt_M⟩; unfold checkSwLM1StepTable checkSwLM1Step at hstep
  simp only [withForcedInt_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hstep; rcases hstep with ⟨⟨⟨_, _, _, _, htau, hden, _, _, hsurv0, hvsc_pos,
    _, _, _, _, hrem0, hsq_ineq⟩, _⟩, hchain_mono⟩; refine ⟨hL2, hL8, hLr, hp_val, ?_⟩
  intro M hM K_blk cs out p pSucc V; rcases hbkt_M M hM with ⟨_, hsurv_le, htail_lbs⟩; have hS : (0
    : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); have hvsc_r : (0 : ℝ) < (vScale : ℝ) :=
    (by exact_mod_cast hvsc_pos); have hbden_r : (0 : ℝ) < (swBden49 : ℝ) :=
    (by unfold swBden49; norm_num); set N : ℝ := (2 ^ n : ℝ); have hsqrtN_pos : 0 < √N :=
    (by dsimp [N]; positivity)
  have hsqrtN_ge : (swBden49 : ℝ) / 2 ≤ √N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ N := (by dsimp [N]; exact_mod_cast hpow); have h1 : (281474976710656 : ℝ) ^ 2 ≤ N :=
      (by have : ((2 ^ 96 : ℕ) : ℝ) = (281474976710656 : ℝ) ^ 2 := (by norm_num); linarith)
    have h2 : (281474976710656 : ℝ) ≤ √N :=
      (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 281474976710656)]; exact Real.sqrt_le_sqrt h1)
    have h3 : (swBden49 : ℝ) / 2 = 281474976710656 := (by unfold swBden49; norm_num); linarith
  have hpSucc_pos : 0 < pSucc := by
    have hlb1 := htail_lbs 1 (by rw [Finset.mem_Icc]; omega); have hpos : 0 < ((tailLbs.getD 0 0 :
      ℤ) : ℝ) / (swScale : ℝ) := div_pos (by exact_mod_cast htl0_pos) hS; exact hpos.trans_le hlb1
  refine ⟨hpSucc_pos, ?_⟩; set chain : List ℤ := vTable r :: (List.range L).map fun i ↦ vTable (r -
    (i + 1))
  have hchain_eq : ∀ c ≤ L, chain.getD c 0 = vTable (r - c) := by
    intro c hc; rcases c with _ | c'
    · simp [chain]
    · have hc' : c' < L := (by omega); simp [chain, List.getD_eq_getElem?_getD, hc']
  set rhsInt : ℤ := ∑ c ∈ Finset.range L, tailLbs.getD c 0 * (chain.getD c 0 - chain.getD (c + 1) 0)
  have hfold_eq : (List.range L).foldl (fun acc c ↦ acc + tailLbs.getD c 0 * (chain.getD c 0 -
    chain.getD (c + 1) 0)) 0 = rhsInt := foldl_range_add_eq_sum L _; rw [hfold_eq] at hrem0 hsq_ineq
  have hgain_ge : ((rhsInt : ℝ) / ((swScale : ℝ) * (vScale : ℝ))) * √N ≤ ∑ h ∈ Finset.Icc 1 L, p h *
    (V r - V (r - h)) := by
    have habel := sum_Icc_abel L p (fun k ↦ V (r - k)); simp only [Nat.sub_zero] at habel
    rw [habel, show ((rhsInt : ℝ) / ((swScale : ℝ) * (vScale : ℝ))) * √N = ∑ c ∈ Finset.range L,
        (((tailLbs.getD c 0 : ℤ) : ℝ) / (swScale : ℝ)) *
          ((((chain.getD c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) / (vScale : ℝ)) * √N) by
      dsimp [rhsInt]; push_cast; rw [sum_div_const, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring]
    refine Finset.sum_le_sum fun c hc ↦ ?_
    rw [Finset.mem_range] at hc; have hmono_c := hchain_mono c hc; have hdiff_nn : 0 ≤ (((chain.getD
      c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) / (vScale : ℝ)) * √N := mul_nonneg (div_nonneg
      (by exact_mod_cast sub_nonneg.2 hmono_c) hvsc_r.le) hsqrtN_pos.le; have hV_eq : (((chain.getD
      c 0 - chain.getD (c + 1) 0 : ℤ) : ℝ) / (vScale : ℝ)) * √N = V (r - c) - V (r - (c + 1)) :=
      (by rw [hchain_eq c (by omega), hchain_eq (c + 1) (by omega)]; dsimp [V]; push_cast; ring)
    have htl_c := htail_lbs (c + 1) (by rw [Finset.mem_Icc]; omega)
    simp only [Nat.add_sub_cancel] at htl_c; rw [← hV_eq]
    exact mul_le_mul_of_nonneg_right htl_c hdiff_nn
  have hK_ub := kBlk_le_main_add_three_halves hn96 (by omega) hr1024 htau hden; set bNum : ℤ := 3 *
    survUb + 2 * swScale * (L : ℤ)
  have hcost_ub : out.2.2 * (K_blk : ℝ) + (L : ℝ) ≤ (((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale :
    ℝ) * (tauDen : ℝ) * √(r : ℝ)) + (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
    have h1 : out.2.2 * (K_blk : ℝ) ≤ ((survUb : ℝ) / (swScale : ℝ)) * (((tauNum : ℝ) / (2 * (tauDen
      : ℝ) * √(r : ℝ))) * √N + 3 / 2) := mul_le_mul hsurv_le hK_ub (Nat.cast_nonneg K_blk)
      (div_nonneg (by exact_mod_cast hsurv0) hS.le)
    have hbNum_nn : 0 ≤ (bNum : ℝ) := by
      dsimp [bNum]; unfold swScale
      exact_mod_cast (by omega : (0 : ℤ) ≤ 3 * survUb + 2 * 1000000000 * (L : ℤ))
    have hoverh : (bNum : ℝ) / (2 * (swScale : ℝ)) ≤ ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ)))
      * √N := by
      have hmul := mul_le_mul_of_nonneg_left hsqrtN_ge (div_nonneg hbNum_nn (mul_pos hS hbden_r).le)
      refine (?_ : (bNum : ℝ) / (2 * (swScale : ℝ)) = ((bNum : ℝ) / ((swScale : ℝ) * (swBden49 :
        ℝ))) * ((swBden49 : ℝ) / 2)).trans_le hmul; field_simp [hS.ne', hbden_r.ne']
    have halg : ((survUb : ℝ) / (swScale : ℝ)) * (((tauNum : ℝ) / (2 * (tauDen : ℝ) * √(r : ℝ))) *
      √N + 3 / 2) + (L : ℝ) = (((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) *
      √(r : ℝ))) * √N + (bNum : ℝ) / (2 * (swScale : ℝ)) :=
      (by dsimp [bNum]; push_cast; field_simp [hS.ne']; ring); linarith
  set rem : ℤ := rhsInt * swBden49 - vScale * bNum
  have hcoef_le : ((survUb : ℝ) * (tauNum : ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ)) +
    (bNum : ℝ) / ((swScale : ℝ) * (swBden49 : ℝ)) ≤ (rhsInt : ℝ) / ((swScale : ℝ) * (vScale : ℝ))
    := by
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hsqrt_r_pos : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
    have hden_r : (0 : ℝ) < (tauDen : ℝ) := (by exact_mod_cast hden); have hrem_r : (0 : ℝ) ≤ (rem :
      ℝ) := (by exact_mod_cast hrem0)
    have hlhs_nn : 0 ≤ (survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ) :=
      (by have : (0 : ℝ) ≤ (survUb : ℝ) := (by exact_mod_cast hsurv0); positivity)
    have hrhs_nn : 0 ≤ 2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ) := by positivity
    have hsq_r : ((survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)) ^ 2 ≤ (2 * (tauDen :
      ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 := by
      have hcast : ((survUb * (tauNum : ℤ) * vScale * swBden49) ^ 2 : ℝ) ≤ ((4 * ((tauDen : ℤ) ^ 2)
        * (r : ℤ) * (rem ^ 2) : ℤ) : ℝ) := (by exact_mod_cast hsq_ineq); push_cast at hcast
      have hsq_rhs : (2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 = 4 * (tauDen : ℝ) ^ 2 * (r : ℝ)
        * (rem : ℝ) ^ 2 := by
        calc (2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2
          _ = 4 * (tauDen : ℝ) ^ 2 * (√(r : ℝ)) ^ 2 * (rem : ℝ) ^ 2 := by ring
          _ = 4 * (tauDen : ℝ) ^ 2 * (r : ℝ) * (rem : ℝ) ^ 2 := by rw [Real.sq_sqrt hr_pos.le]
      linarith
    have hroot : (survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ) ≤ 2 * (tauDen : ℝ) *
      √(r : ℝ) * (rem : ℝ) :=
      (by rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]; exact Real.sqrt_le_sqrt hsq_r)
    have hrem_def : (rem : ℝ) = (rhsInt : ℝ) * (swBden49 : ℝ) - (vScale : ℝ) * (bNum : ℝ) :=
      (by dsimp [rem]; push_cast; rfl); rw [hrem_def] at hroot; have hpos_prod : 0 < 2 * (swScale :
      ℝ) * (tauDen : ℝ) * √(r : ℝ) * (vScale : ℝ) * (swBden49 : ℝ) := (by positivity)
    rw [← sub_nonneg]; have hdiff : (rhsInt : ℝ) / ((swScale : ℝ) * (vScale : ℝ)) - (((survUb : ℝ) *
      (tauNum : ℝ)) / (2 * (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ)) + (bNum : ℝ) / ((swScale : ℝ) *
      (swBden49 : ℝ))) = (2 * (tauDen : ℝ) * √(r : ℝ) * ((rhsInt : ℝ) * (swBden49 : ℝ) - (vScale :
      ℝ) * (bNum : ℝ)) - (survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)) / (2 *
      (swScale : ℝ) * (tauDen : ℝ) * √(r : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)) :=
      (by field_simp [hS.ne', hden_r.ne', hsqrt_r_pos.ne', hvsc_r.ne', hbden_r.ne']; ring)
    rw [hdiff]; exact div_nonneg (by linarith) hpos_prod.le
  have hnet : out.2.2 * (K_blk : ℝ) + (L : ℝ) ≤ ∑ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) :=
    (hcost_ub.trans (mul_le_mul_of_nonneg_right hcoef_le hsqrtN_pos.le)).trans hgain_ge
  have hexpand : ∑ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) = pSucc * V r - ∑ h ∈ Finset.Icc 1 L,
    p h * V (r - h) := by
    dsimp [pSucc]; rw [Finset.sum_mul]; have hsub : ∀ h ∈ Finset.Icc 1 L, p h * (V r - V (r - h)) =
      p h * V r - p h * V (r - h) := fun _ _ ↦ mul_sub _ _ _; rw [Finset.sum_congr rfl hsub,
      Finset.sum_sub_distrib]
  rw [div_le_iff₀ hpSucc_pos]; linarith [hnet, hexpand]
/-- Drop-in `m ≥ 1` `MultiSW_L` stage soundness under `checkSwLBucketCertL2`, matching the
  exact
  signature and conclusion of `checkMultiSWLStage_sound`. -/
private theorem checkMultiSWLStageL2_aux {L mEff m n r rMin rMax tauNum tauDen : ℕ} {ratios : List
  IvInt} {trigIvs : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb
  vScale : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hmEff : mEff ≤
  m) (hMono : ∀ j : ℕ, j < r → vTable j ≤ vTable (j + 1)) (hbkt : checkSwLBucketCertL2 L rMin rMax
  tauNum tauDen ratios trigIvs pulses tailLbs survUb = true) (hstep : checkMultiSWLStep L mEff r
  pulses.length tauNum tauDen L tailLbs vScale vTable = true) : ∃ (hL2 : 2 ≤ L), L ≤ 8 ∧ L ≤ r ∧ ∀
  (M : Fin (2 * L) → Fin (2 * L) → ℝ), IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs pulses
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        let tailP : ℕ → ℝ := fun c ↦ ∑ h ∈ Finset.Icc c L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        ∀ (q : ℕ → ℝ), (∀ u : ℕ, 0 ≤ q u) → ∑ u ∈ Finset.range (r + 1), q u = 1 → (∀ u_thr : ℕ, 1 ≤
          u_thr → u_thr ≤ r → swLUnionTailReal L r tailP m u_thr ≤ ∑ u ∈ Finset.Ico u_thr (r + 1), q
          u) → 0 < 1 - q 0 ∧ (((pulses.length : ℝ) * (K_blk : ℝ) + (L : ℝ)) + ∑ u ∈ Finset.Ico 1 (r
          + 1), q u * V (r - u)) / (1 - q 0) ≤ V r := by
  rcases checkSwLBucketCertL2_sound hn96 hmin hmax hbkt with ⟨hL2, hL8, hLr, hr1024, _, _, hp_val,
    _, _, _, htl0_le, htlL0, htl_mono, hbkt_M⟩; unfold checkMultiSWLStep at hstep
  simp only [forceListId_eq, withForcedNat_eq, withForcedInt_eq, id_eq, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hstep; rcases hstep with ⟨⟨⟨_, _, _, _,
    _, _, htau, hden, hvsc_pos, _, _, _⟩, _⟩, htail1_pos, hrem0, hsq_ineq⟩; refine ⟨hL2, hL8, hLr,
    ?_⟩; intro M hM K_blk cs out p tailP V q hq0 hq_sum hq_dom; rcases hbkt_M M hM with ⟨_, _,
    htail_lbs⟩
  have hcs_unit : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum hL2 hcs_unit pulses hp_val with ⟨hcons, hcum0, _, _⟩
  have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg hL2 M out.1 hcum0 h
  have hp_sum1 : ∑ h ∈ Finset.range (L + 1), p h = 1 := swLAttemptProbReal_sum_one hL2 hM hcons
  have htail0 : ∀ c ∈ Finset.Icc 1 L, 0 ≤ tailP c := fun _ _ ↦ Finset.sum_nonneg fun h _ ↦ hp_nn h
  have htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c + 1) ≤ tailP c := fun _ _ _ ↦
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (by omega)) fun h _ _ ↦ hp_nn
    h
  have htail1 : tailP 1 ≤ 1 := by
    have hsub : Finset.Icc 1 L ⊆ Finset.range (L + 1) := fun h hh ↦ by
      rw [Finset.mem_Icc] at hh; rw [Finset.mem_range]; omega
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun h _ _ ↦ hp_nn h).trans_eq hp_sum1
  have hU : (0 : ℝ) < (swUnionScale : ℝ) := (by unfold swUnionScale; norm_num); have hvsc_r : (0 :
    ℝ) < (vScale : ℝ) := (by exact_mod_cast hvsc_pos); have hbden_r : (0 : ℝ) < (swBden49 : ℝ) :=
    (by unfold swBden49; norm_num); have hr_pos : (0 : ℝ) < (r : ℝ) :=
    (by exact_mod_cast (by omega : 0 < r)); have hsr_pos : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
  have hden_r : (0 : ℝ) < (tauDen : ℝ) := (by exact_mod_cast hden); set N : ℝ := (2 ^ n : ℝ)
  have hsqrtN_pos : 0 < √N := by dsimp [N]; positivity
  have hsqrtN_ge : (swBden49 : ℝ) / 2 ≤ √N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ N := (by dsimp [N]; exact_mod_cast hpow); have h1 : (281474976710656 : ℝ) ^ 2 ≤ N :=
      (by have : ((2 ^ 96 : ℕ) : ℝ) = (281474976710656 : ℝ) ^ 2 := (by norm_num); linarith)
    have h2 : (281474976710656 : ℝ) ≤ √N :=
      (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 281474976710656)]; exact Real.sqrt_le_sqrt h1)
    have h3 : (swBden49 : ℝ) / 2 = 281474976710656 := (by unfold swBden49; norm_num); linarith
  set tailL := swLUnionTailLbList L r tailLbs mEff; set maxS : ℕ := min (L * mEff) r
  set abSum : ℤ := ∑ s ∈ Finset.range maxS, tailL.getD (s + 1) 0 * (vTable (r - s) - vTable (r - s -
    1)); have hfold_eq : (List.range maxS).foldl (fun acc s ↦ acc + tailL.getD (s + 1) 0 * (vTable
    (r - s) - vTable (r - s - 1))) 0 = abSum := foldl_range_add_eq_sum maxS _
  rw [hfold_eq] at hrem0 hsq_ineq; set numPulses : ℕ := pulses.length; set bNum : ℤ := 3 *
    (numPulses : ℤ) + 2 * (L : ℤ); set rem : ℤ := abSum * swBden49 - swUnionScale * vScale * bNum
  set Q : ℝ := (numPulses : ℝ) * (K_blk : ℝ) + (L : ℝ)
  have hK_le := kBlk_le_main_add_three_halves hn96 (by omega) hr1024 htau hden
  have hQ_step1 : Q ≤ (((numPulses : ℝ) * (tauNum : ℝ)) / (2 * (tauDen : ℝ) * √(r : ℝ))) * √N +
    (bNum : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_left hK_le (Nat.cast_nonneg numPulses); have halg : (numPulses :
      ℝ) * ((((tauNum : ℝ) / (2 * (tauDen : ℝ) * √(r : ℝ))) * √N) + 3 / 2) + (L : ℝ) = (((numPulses
      : ℝ) * (tauNum : ℝ)) / (2 * (tauDen : ℝ) * √(r : ℝ))) * √N + (bNum : ℝ) / 2 :=
      (by dsimp [bNum]; push_cast; ring); dsimp [Q, N] at hm halg ⊢; linarith
  have hbNum_nn : (0 : ℝ) ≤ (bNum : ℝ) :=
    (by dsimp [bNum]; exact_mod_cast (by omega : (0 : ℤ) ≤ 3 * (numPulses : ℤ) + 2 * (L : ℤ)))
  have hfin_le : (bNum : ℝ) / 2 ≤ ((bNum : ℝ) / (swBden49 : ℝ)) * √N := by
    have h1 := mul_le_mul_of_nonneg_left hsqrtN_ge (div_nonneg hbNum_nn hbden_r.le)
    have h2 : ((bNum : ℝ) / (swBden49 : ℝ)) * ((swBden49 : ℝ) / 2) = (bNum : ℝ) / 2 :=
      (by field_simp [hbden_r.ne']); linarith
  have hmain_le : ((numPulses : ℝ) * (tauNum : ℝ)) / (2 * (tauDen : ℝ) * √(r : ℝ)) ≤ (rem : ℝ) /
    ((swUnionScale : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)) := by
    have hcast : ((((numPulses : ℤ) * (tauNum : ℤ) * swUnionScale * vScale * swBden49) ^ 2 : ℤ) : ℝ)
      ≤ ((4 * (tauDen : ℤ) ^ 2 * (r : ℤ) * rem ^ 2 : ℤ) : ℝ) := (by exact_mod_cast hsq_ineq)
    push_cast at hcast
    have hrhs_sq : 4 * (tauDen : ℝ) ^ 2 * (r : ℝ) * (rem : ℝ) ^ 2 = (2 * (tauDen : ℝ) * √(r : ℝ) *
      (rem : ℝ)) ^ 2 := by
      calc 4 * (tauDen : ℝ) ^ 2 * (r : ℝ) * (rem : ℝ) ^ 2
        _ = 4 * (tauDen : ℝ) ^ 2 * (√(r : ℝ)) ^ 2 * (rem : ℝ) ^ 2 := by rw [Real.sq_sqrt hr_pos.le]
        _ = (2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 := by ring
    rw [hrhs_sq] at hcast; have hlhs_nn : 0 ≤ (numPulses : ℝ) * (tauNum : ℝ) * (swUnionScale : ℝ) *
      (vScale : ℝ) * (swBden49 : ℝ) := (by positivity); have hrhs_nn : 0 ≤ 2 * (tauDen : ℝ) * √(r :
      ℝ) * (rem : ℝ) := (by have : (0 : ℝ) ≤ (rem : ℝ) := (by exact_mod_cast hrem0); positivity)
    have hlin : (numPulses : ℝ) * (tauNum : ℝ) * (swUnionScale : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)
      ≤ 2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ) :=
      (by rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]; exact Real.sqrt_le_sqrt hcast)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [show ((numPulses : ℝ) * (tauNum : ℝ)) *
        ((swUnionScale : ℝ) * (vScale : ℝ) * (swBden49 : ℝ)) =
      (numPulses : ℝ) * (tauNum : ℝ) * (swUnionScale : ℝ) * (vScale : ℝ) *
        (swBden49 : ℝ) by ring,
      show (rem : ℝ) * (2 * (tauDen : ℝ) * √(r : ℝ)) =
        2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ) by ring]
  have hQ_ab : Q ≤ ((abSum : ℝ) / ((swUnionScale : ℝ) * (vScale : ℝ))) * √N := by
    have hm := mul_le_mul_of_nonneg_right hmain_le hsqrtN_pos.le
    have hsum : ((rem : ℝ) / ((swUnionScale : ℝ) * (vScale : ℝ) * (swBden49 : ℝ))) * √N + ((bNum :
      ℝ) / (swBden49 : ℝ)) * √N = ((abSum : ℝ) / ((swUnionScale : ℝ) * (vScale : ℝ))) * √N :=
      (by dsimp [rem]; push_cast; field_simp [hU.ne', hvsc_r.ne', hbden_r.ne']; ring)
    linarith [hQ_step1, hfin_le, hm, hsum]
  have hab_expand : ((abSum : ℝ) / ((swUnionScale : ℝ) * (vScale : ℝ))) * √N = ∑ s ∈ Finset.range
    maxS, (((tailL.getD (s + 1) 0 : ℤ) : ℝ) / (swUnionScale : ℝ)) * (V (r - s) - V (r - s - 1))
    := by
    dsimp [abSum, V, N]; push_cast; rw [sum_div_const, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_; field_simp [hU.ne', hvsc_r.ne']
  have hdv_nn : ∀ s < r, 0 ≤ V (r - s) - V (r - s - 1) := by
    intro s hsr; dsimp [V]; have hj : r - s - 1 < r := (by omega)
    have hm : (vTable (r - s - 1) : ℝ) ≤ (vTable (r - s) : ℝ) :=
      (by rw [show r - s = (r - s - 1) + 1 by omega]; exact_mod_cast hMono (r - s - 1) hj)
    rw [← sub_mul, ← sub_div]
    exact mul_nonneg (div_nonneg (by linarith) hvsc_r.le) (Real.sqrt_nonneg _)
  have hlb_dom : ∀ u_thr : ℕ, 1 ≤ u_thr → u_thr ≤ r → (((tailL.getD u_thr 0 : ℤ) : ℝ) /
    (swUnionScale : ℝ)) ≤ ∑ u ∈ Finset.Ico u_thr (r + 1), q u := by
    intro u_thr hu1 hur
    have h1 := swLUnionTailLb_le_real (by omega) hLr htl0_le htlL0 htl_mono htail_lbs htail0
      htail_anti htail1 mEff u_thr
    have h2 := swLUnionTailReal_mono_copies (r := r) htail0 htail_anti htail1 hmEff u_thr
    exact (h1.trans h2).trans (hq_dom u_thr hu1 hur)
  have hmaxS_le_r : maxS ≤ r := Nat.min_le_right _ _
  have hab_le_full : ∑ s ∈ Finset.range maxS, (((tailL.getD (s + 1) 0 : ℤ) : ℝ) / (swUnionScale :
    ℝ)) * (V (r - s) - V (r - s - 1)) ≤ ∑ s ∈ Finset.range r, (∑ u ∈ Finset.Ico (s + 1) (r + 1), q
    u) * (V (r - s) - V (r - s - 1)) := by
    refine (Finset.sum_le_sum fun s hs ↦ ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hmaxS_le_r) fun s hs _ ↦ mul_nonneg (Finset.sum_nonneg fun u _ ↦ hq0 u)
      (hdv_nn s (Finset.mem_range.1 hs)))
    have hsr : s < r := (Finset.mem_range.1 hs).trans_le hmaxS_le_r
    exact mul_le_mul_of_nonneg_right (hlb_dom (s + 1) (by omega) (by omega)) (hdv_nn s hsr)
  have habel_eq : ∑ s ∈ Finset.range r, (∑ u ∈ Finset.Ico (s + 1) (r + 1), q u) * (V (r - s) - V (r
    - s - 1)) = V r - ∑ u ∈ Finset.range (r + 1), q u * V (r - u) := by
    have hgen := sum_range_mul_sub_eq_sum_Ico r q (fun u ↦ V (r - u))
    have hlhs : ∑ u ∈ Finset.range (r + 1), q u * (V (r - 0) - V (r - u)) = V r - ∑ u ∈ Finset.range
      (r + 1), q u * V (r - u) := by
      simp_rw [Nat.sub_zero, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq_sum, one_mul]
    rw [← hlhs, hgen]; refine Finset.sum_congr rfl fun s _ ↦ ?_; rw [show r - (s + 1) = r - s - 1
      by omega]
  have hQ_bell : Q + ∑ u ∈ Finset.range (r + 1), q u * V (r - u) ≤ V r :=
    (by linarith [hQ_ab, hab_expand, hab_le_full, habel_eq])
  have hsplit_q : ∑ u ∈ Finset.range (r + 1), q u = q 0 + ∑ u ∈ Finset.Ico 1 (r + 1), q u :=
    (by rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < r + 1)])
  have hsplit_qv : ∑ u ∈ Finset.range (r + 1), q u * V (r - u) = q 0 * V r + ∑ u ∈ Finset.Ico 1 (r +
    1), q u * V (r - u) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < r + 1), Nat.sub_zero]
  have h1_sub_q0_pos : 0 < 1 - q 0 := by
    have hpos : 0 < ((tailL.getD 1 0 : ℤ) : ℝ) / (swUnionScale : ℝ) := div_pos
      (by exact_mod_cast htail1_pos) hU; have hdom1 := hlb_dom 1 le_rfl (by omega)
    linarith [hq_sum, hsplit_q, hpos.trans_le hdom1]
  refine ⟨h1_sub_q0_pos, ?_⟩; rw [div_le_iff₀ h1_sub_q0_pos]; linarith [hQ_bell, hsplit_qv]
theorem checkMultiSWLStageL2_sound {L mEff m n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb vScale
  : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hmEff : mEff ≤ m)
  (hMono : ∀ j : ℕ, j < r → vTable j ≤ vTable (j + 1)) (hunit : pulses.all (fun p ↦ swLPulseValid p
  && decide (p.vNum = 0)) = true) (hbkt : checkSwLBucketCertL2 L rMin rMax tauNum tauDen ratios
  trigIvs pulses tailLbs survUb = true) (hstep : checkMultiSWLStep L mEff r pulses.length tauNum
  tauDen L tailLbs vScale vTable = true) : ∃ (hL2 : 2 ≤ L), L ≤ 8 ∧ L ≤ r ∧ pulses.all (fun p ↦
  swLPulseValid p && decide (p.vNum = 0)) = true ∧ ∀ (M : Fin (2 * L) → Fin (2 * L) → ℝ),
  IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs pulses
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        let tailP : ℕ → ℝ := fun c ↦ ∑ h ∈ Finset.Icc c L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        ∀ (q : ℕ → ℝ), (∀ u : ℕ, 0 ≤ q u) → ∑ u ∈ Finset.range (r + 1), q u = 1 → (∀ u_thr : ℕ, 1 ≤
          u_thr → u_thr ≤ r → swLUnionTailReal L r tailP m u_thr ≤ ∑ u ∈ Finset.Ico u_thr (r + 1), q
          u) → 0 < 1 - q 0 ∧ (((pulses.length : ℝ) * (K_blk : ℝ) + (L : ℝ)) + ∑ u ∈ Finset.Ico 1 (r
          + 1), q u * V (r - u)) / (1 - q 0) ≤ V r := by
  rcases checkMultiSWLStageL2_aux hn96 hmin hmax hmEff hMono hbkt hstep with ⟨hL2, hL8, hLr, hm⟩
  exact ⟨hL2, hL8, hLr, hunit, hm⟩
end SchurWeylLCert
end QuantumComputation.Specs.GroverFindAll
