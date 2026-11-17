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
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import QuantumComputation.Maths.Trigonometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
/-!
# Pure-Integer Certificate Checkers & Real Soundness for `H_dist(2 ≤ L ≤ 8)` Conveyors
Self-contained, QHL-free real-analytic and fixed-point integer certificate infrastructure for
`L`-register (`2 ≤ L ≤ 8`) Schur-Weyl harmonic distinct-tuple conveyors on `H_dist(L, N)`,
supporting both `m = 1` multi-step (`h ∈ {1,..., L}`) Bellman cascades and `m ≥ 1` synchronous
`MultiSW_L` union-hit tail recurrences with cold-entry stage splicing.
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
namespace SchurWeylLCert
open Real
open scoped BigOperators
/-! ## 1. Locked Real-Evolution, Overlap & Hypergeometric Tail API -/
/-- Rational Cayley parameters `(u_1,..., u_{L-1}, v)` over common denominator `uvDen > 0`. -/
structure SwLPulseRat (L : ℕ) where
  uNum : Fin (L - 1) → ℤ
  vNum : ℤ
  uvDen : ℕ
/-- Positivity check `0 < uvDen` for rational Cayley parameters. -/
def swLPulseValid {L : ℕ} (p : SwLPulseRat L) : Bool :=
  decide (0 < p.uvDen)
/-- Rational Pythagorean cosine `(den^2 - num^2) / (den^2 + num^2)`. -/
noncomputable def swLCayleyCos (num : ℤ) (den : ℕ) : ℝ :=
  ((den : ℝ) ^ 2 - (num : ℝ) ^ 2) / ((den : ℝ) ^ 2 + (num : ℝ) ^ 2)
/-- Rational Pythagorean sine `(2 * num * den) / (den^2 + num^2)`. -/
noncomputable def swLCayleySin (num : ℤ) (den : ℕ) : ℝ :=
  (2 * (num : ℝ) * (den : ℝ)) / ((den : ℝ) ^ 2 + (num : ℝ) ^ 2)
/-- Exact finite-`N` Grover angle `2 arcsin √((r - w) / (N - 2w))` on plane `(2w, 2w + 1)`. -/
noncomputable def swLThetaShiftReal (N r w : ℕ) : ℝ :=
  2 * Real.arcsin √((r - w : ℝ) / (N - 2 * w : ℝ))
/-- Parallel Grover plane rotation on `(2w, 2w + 1)` (`w: Fin L`) by `(cos, sin) = cs w`. -/
noncomputable def swLGroverRotVec (L : ℕ) (cs : Fin L → ℝ × ℝ)
    (st : Fin (2 * L) → ℝ) : Fin (2 * L) → ℝ :=
  fun j ↦
    let w : Fin L := ⟨j.1 / 2, by omega⟩
    let cw := (cs w).1
    let sw := (cs w).2
    let ae := st ⟨2 * w.1, by omega⟩
    let ao := st ⟨2 * w.1 + 1, by omega⟩
    if j.1 % 2 = 0 then cw * ae - sw * ao else sw * ae + cw * ao
/-- Parallel Pieri `SO(2)` rotations on `(2w - 1, 2w)` (`1 ≤ w < L`) + weak survival on `2L
  - 1`. -/
noncomputable def swLPieriAndWeakVec (L : ℕ) (hL : 2 ≤ L) (p : SwLPulseRat L)
    (na : Fin (2 * L) → ℝ) : Fin (2 * L) → ℝ :=
  fun j ↦
    if _hj0 : j.1 = 0 then
      na ⟨0, by omega⟩
    else if _hjl : j.1 < 2 * L - 1 then
      let w0 : Fin (L - 1) := ⟨(j.1 - 1) / 2, by omega⟩
      let cu := swLCayleyCos (p.uNum w0) p.uvDen
      let su := swLCayleySin (p.uNum w0) p.uvDen
      let lv := na ⟨2 * w0.1 + 1, by omega⟩
      let rv := na ⟨2 * w0.1 + 2, by omega⟩
      if (j.1 - 1) % 2 = 0 then cu * lv - su * rv else su * lv + cu * rv
    else
      swLCayleyCos p.vNum p.uvDen * na ⟨2 * L - 1, by omega⟩
/-- One conveyor pulse: Grover rotations `cs`, Pieri intertwiners `uNum`, weak measurement
  `vNum`. -/
noncomputable def swLPulseStepReal (L : ℕ) (hL : 2 ≤ L) (cs : Fin L → ℝ × ℝ)
    (st : Fin (2 * L) → ℝ) (cum surv : ℝ) (p : SwLPulseRat L) :
    (Fin (2 * L) → ℝ) × ℝ × ℝ :=
  let na := swLGroverRotVec L cs st
  let nxt := swLPieriAndWeakVec L hL p na
  let sv := swLCayleySin p.vNum p.uvDen
  (nxt, cum + (sv * na ⟨2 * L - 1, by omega⟩) ^ 2, surv + (1 - cum))
/-- Euclidean norm squared `∑_{j=0}^{2L-1} st_j^2` of a `2L`-component real amplitude
  vector. -/
noncomputable def swLNormSq {L : ℕ} (st : Fin (2 * L) → ℝ) : ℝ :=
  ∑ j : Fin (2 * L), (st j) ^ 2
/-- Orbit projection `(M *ᵥ st) o = ∑_j M o j * st j`. -/
noncomputable def swLOrbitProj {L : ℕ} (M : Fin (2 * L) → Fin (2 * L) → ℝ)
    (st : Fin (2 * L) → ℝ) (o : Fin (2 * L)) : ℝ :=
  ∑ j : Fin (2 * L), M o j * st j
/-- Exact terminal attempt hit-count probability `P(H = h)` (`0 ≤ h ≤ L`) under overlap `M`. -/
noncomputable def swLAttemptProbReal (L : ℕ) (hL : 2 ≤ L)
    (M : Fin (2 * L) → Fin (2 * L) → ℝ) (st : Fin (2 * L) → ℝ) (cum : ℝ) (h : ℕ) : ℝ :=
  if h = 0 then
    (swLOrbitProj M st ⟨0, by omega⟩) ^ 2 +
      cum * (M ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2
  else if _hh : h < L then
    (swLOrbitProj M st ⟨2 * h - 1, by omega⟩) ^ 2 +
      (swLOrbitProj M st ⟨2 * h, by omega⟩) ^ 2 +
      cum * ((M ⟨2 * h - 1, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 +
        (M ⟨2 * h, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2)
  else if h = L then
    (swLOrbitProj M st ⟨2 * L - 1, by omega⟩) ^ 2 +
      cum * (M ⟨2 * L - 1, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2
  else 0
/-- Orthogonality and `10⁻⁹` finite-`N` diagonal dominance of the `2L × 2L` overlap matrix
  `M`. -/
def IsValidSwLOverlap {L : ℕ} (M : Fin (2 * L) → Fin (2 * L) → ℝ) : Prop :=
  (∀ i j : Fin (2 * L), ∑ o : Fin (2 * L), M o i * M o j = if i = j then 1 else 0) ∧
  (∀ o j : Fin (2 * L), ∑ k : Fin (2 * L), M o k * M j k = if o = j then 1 else 0) ∧
  (∀ j : Fin (2 * L),
    1 - (1 : ℝ) / 10 ^ 9 ≤ M j j ∧ M j j ≤ 1 ∧ 1 - (1 : ℝ) / 10 ^ 18 ≤ (M j j) ^ 2) ∧
  (∀ o j : Fin (2 * L), o ≠ j → |M o j| ≤ (1 : ℝ) / 10 ^ 9)
/-- Compact part constructor building `SwLPulseRat L` from `us: List ℤ` and `v: ℤ`. -/
def mkSwLPulse (L : ℕ) (us : List ℤ) (v : ℤ) (uvDen : ℕ := 65536) : SwLPulseRat L :=
  ⟨fun i ↦ us.getD i.1 0, v, uvDen⟩
/-- Grover block length per pulse targeting head angle `tauNum / tauDen`. -/
noncomputable def swLKBlk (n r tauNum tauDen : ℕ) : ℕ :=
  let α := Real.arcsin (1 / √((2 ^ n : ℝ) / (r : ℝ)))
  (round (((tauNum : ℝ) / (tauDen : ℝ)) / (2 * α))).toNat + 1
/-- Multi-pulse real evolution from `(st, cum, surv)`. -/
noncomputable def swLEvolutionRealAux (L : ℕ) (hL : 2 ≤ L) (cs : Fin L → ℝ × ℝ)
    (st : Fin (2 * L) → ℝ) (cum surv : ℝ) :
    List (SwLPulseRat L) → (Fin (2 * L) → ℝ) × ℝ × ℝ
  | [] => (st, cum, surv)
  | p :: ps =>
      let nxt := swLPulseStepReal L hL cs st cum surv p
      swLEvolutionRealAux L hL cs nxt.1 nxt.2.1 nxt.2.2 ps
/-- Multi-pulse real evolution starting from `(|b_0, 0⟩, cum = 0, surv = 0)`. -/
noncomputable def swLEvolutionReal (L : ℕ) (hL : 2 ≤ L) (cs : Fin L → ℝ × ℝ)
    (pulses : List (SwLPulseRat L)) : (Fin (2 * L) → ℝ) × ℝ × ℝ :=
  swLEvolutionRealAux L hL cs (fun j ↦ if j.1 = 0 then 1 else 0) 0 0 pulses
/-- Exact single-copy hypergeometric tail `Pr(|H \ U| ≥ j)` when `|U| = u` (`|R| = r`, `L ≤
  r`)
  and `tailP c = Pr(|H| ≥ c)` (`1 ≤ c ≤ L`). -/
noncomputable def swLGReal (L r : ℕ) (tailP : ℕ → ℝ) (j u : ℕ) : ℝ :=
  if r < L ∨ j = 0 ∨ L < j ∨ r ≤ u then 0
  else
    (∑ c ∈ Finset.Icc j L,
      tailP c * ((Nat.choose (c - 1) (j - 1) *
        Nat.descFactorial (r - u) j *
        Nat.descFactorial u (c - j) *
        Nat.descFactorial (r - c) (L - c) : ℕ) : ℝ)) /
    (Nat.descFactorial r L : ℝ)
/-- One-copy real union-hit tail update `T_{t+1}(s)` from `prev = T_t`. -/
noncomputable def swLUnionTailStepReal (L r : ℕ) (tailP : ℕ → ℝ)
    (prev : ℕ → ℝ) (s : ℕ) : ℝ :=
  if s = 0 then 1
  else if r < s ∨ r < L then 0
  else
    prev s + ∑ j ∈ Finset.Icc 1 (min L s),
      swLGReal L r tailP j (s - j) * (prev (s - j) - prev (s - j + 1))
/-- Exact `t`-copy union-hit tail `Pr(|U_t| ≥ s)` under independent uniform `H_i ⊆ R`. -/
noncomputable def swLUnionTailReal (L r : ℕ) (tailP : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, s => if s = 0 then 1 else 0
  | t + 1, s => swLUnionTailStepReal L r tailP (swLUnionTailReal L r tailP t) s
/-! ## 2. Real Norm Conservation & Orbit Probability Simplex Lemmas -/
theorem swLCayleyCos_sq_add_sin_sq {num : ℤ} {den : ℕ} (hd : 0 < den) : swLCayleyCos num den ^ 2 +
  swLCayleySin num den ^ 2 = 1 := by
  unfold swLCayleyCos swLCayleySin; have hd_r : (0 : ℝ) < (den : ℝ) := (by exact_mod_cast hd)
  have hden_pos : (0 : ℝ) < (den : ℝ) ^ 2 + (num : ℝ) ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos
    hd_r) (sq_nonneg _); field_simp [hden_pos.ne']; ring
theorem rot2_sq_sum {c s x y : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : (c * x - s * y) ^ 2 + (s * x + c * y)
  ^ 2 = x ^ 2 + y ^ 2 := by linear_combination (x ^ 2 + y ^ 2) * hcs
theorem probe_sq_sum {c s x : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : (c * x) ^ 2 + (s * x) ^ 2 = x ^ 2 := by
  linear_combination (x ^ 2) * hcs
theorem sum_range_two_mul : ∀ (L : ℕ) (g : ℕ → ℝ), ∑ j ∈ Finset.range (2 * L), g j = ∑ w ∈
  Finset.range L, (g (2 * w) + g (2 * w + 1))
  | 0, _ => by simp
  | L + 1, g => by
    rw [show 2 * (L + 1) = 2 * L + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, sum_range_two_mul L g,
      Finset.sum_range_succ]
    ring
theorem sum_fin_two_mul (L : ℕ) (f : Fin (2 * L) → ℝ) :
    ∑ j : Fin (2 * L), f j = ∑ w : Fin L, (f ⟨2 * w.1, by omega⟩ + f ⟨2 * w.1 + 1, by omega⟩) := by
  set g : ℕ → ℝ := fun i ↦ if hi : i < 2 * L then f ⟨i, hi⟩ else 0
  have hl : ∑ j : Fin (2 * L), f j = ∑ j ∈ Finset.range (2 * L), g j := by
    rw [← Fin.sum_univ_eq_sum_range g (2 * L)]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [g, j.2]
  have hr : ∑ w : Fin L, (f ⟨2 * w.1, by omega⟩ + f ⟨2 * w.1 + 1, by omega⟩) = ∑ w ∈ Finset.range L,
    (g (2 * w) + g (2 * w + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun w ↦ g (2 * w) + g (2 * w + 1)) L]
    refine Finset.sum_congr rfl fun w _ ↦ ?_; have h0 : 2 * w.1 < 2 * L := (by omega); have h1 : 2 *
      w.1 + 1 < 2 * L := (by omega); simp [g, h0, h1]
  rw [hl, hr, sum_range_two_mul]
theorem sum_range_interior_pairs {L : ℕ} (hL : 2 ≤ L) (g : ℕ → ℝ) : ∑ j ∈ Finset.range (2 * L), g j
  = g 0 + (∑ w0 ∈ Finset.range (L - 1), (g (2 * w0 + 1) + g (2 * w0 + 2))) + g (2 * L - 1) := by
  induction L, hL using Nat.le_induction with
  | base =>
    rw [show 2 * 2 = 3 + 1 from rfl, show 2 - 1 = 1 from rfl, Finset.sum_range_succ, show (3 : ℕ) =
      2 + 1 from rfl, Finset.sum_range_succ, show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ,
      Finset.sum_range_one, Finset.sum_range_one]; norm_num; ring
  | succ m hm ih =>
    have hl : ∑ j ∈ Finset.range (2 * (m + 1)), g j = (∑ j ∈ Finset.range (2 * m), g j) + g (2 * m)
      + g (2 * m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
    have hr : ∑ w0 ∈ Finset.range (m + 1 - 1), (g (2 * w0 + 1) + g (2 * w0 + 2)) = (∑ w0 ∈
      Finset.range (m - 1), (g (2 * w0 + 1) + g (2 * w0 + 2))) + (g (2 * m - 1) + g (2 * m)) := by
      rw [show m + 1 - 1 = (m - 1) + 1 by omega, Finset.sum_range_succ, show 2 * (m - 1) + 1 = 2 *
        m - 1 by omega, show 2 * (m - 1) + 2 = 2 * m by omega]
    rw [hl, ih, hr, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]; ring
theorem sum_fin_interior_pairs {L : ℕ} (hL : 2 ≤ L) (f : Fin (2 * L) → ℝ) : ∑ j : Fin (2 * L), f j =
    f ⟨0, by omega⟩ + (∑ w0 : Fin (L - 1), (f ⟨2 * w0.1 + 1, by omega⟩ + f ⟨2 * w0.1 + 2, by
    omega⟩)) + f ⟨2 * L - 1, by omega⟩ := by
  set g : ℕ → ℝ := fun i ↦ if hi : i < 2 * L then f ⟨i, hi⟩ else 0
  have hl : ∑ j : Fin (2 * L), f j = ∑ j ∈ Finset.range (2 * L), g j := by
    rw [← Fin.sum_univ_eq_sum_range g (2 * L)]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [g, j.2]
  have h0 : g 0 = f ⟨0, by omega⟩ := (by have hlt : 0 < 2 * L := (by omega); simp [g, hlt])
  have hlast : g (2 * L - 1) = f ⟨2 * L - 1, by omega⟩ :=
    (by have hlt : 2 * L - 1 < 2 * L := (by omega); simp [g, hlt])
  have hmid : ∑ w0 ∈ Finset.range (L - 1), (g (2 * w0 + 1) + g (2 * w0 + 2)) = ∑ w0 : Fin (L - 1),
    (f ⟨2 * w0.1 + 1, by omega⟩ + f ⟨2 * w0.1 + 2, by omega⟩) := by
    rw [← Fin.sum_univ_eq_sum_range (fun w0 ↦ g (2 * w0 + 1) + g (2 * w0 + 2)) (L - 1)]
    refine Finset.sum_congr rfl fun w0 _ ↦ ?_; have h1 : 2 * w0.1 + 1 < 2 * L := (by omega)
    have h2 : 2 * w0.1 + 2 < 2 * L := (by omega); simp [g, h1, h2]
  rw [hl, sum_range_interior_pairs hL g, h0, hmid, hlast]
theorem swLGroverRotVec_normSq {L : ℕ} {cs : Fin L → ℝ × ℝ} (hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs
  w).2 ^ 2 = 1) (st : Fin (2 * L) → ℝ) : swLNormSq (swLGroverRotVec L cs st) = swLNormSq st := by
  unfold swLNormSq; rw [sum_fin_two_mul L, sum_fin_two_mul L]
  refine Finset.sum_congr rfl fun w _ ↦ ?_; unfold swLGroverRotVec
  have he0 : (2 * w.1) / 2 = w.1 := (by omega); have he1 : (2 * w.1 + 1) / 2 = w.1 := (by omega)
  have hm0 : (2 * w.1) % 2 = 0 := (by omega); have hm1 : (2 * w.1 + 1) % 2 = 1 := (by omega)
  dsimp only; simp only [he0, he1, hm0, hm1, ↓reduceIte, one_ne_zero]; exact rot2_sq_sum (hcs w)
theorem swLPieriAndWeakVec_normSq {L : ℕ} (hL : 2 ≤ L) {p : SwLPulseRat L} (hp : 0 < p.uvDen) (na :
    Fin (2 * L) → ℝ) : swLNormSq (swLPieriAndWeakVec L hL p na) + (swLCayleySin p.vNum p.uvDen * na
    ⟨2 * L - 1, by omega⟩) ^ 2 = swLNormSq na := by
  unfold swLNormSq; rw [sum_fin_interior_pairs hL, sum_fin_interior_pairs hL]
  have h0 : swLPieriAndWeakVec L hL p na ⟨0, by omega⟩ = na ⟨0, by omega⟩ :=
    (by unfold swLPieriAndWeakVec; simp); have htop : swLPieriAndWeakVec L hL p na ⟨2 * L - 1,
    by omega⟩ = swLCayleyCos p.vNum p.uvDen * na ⟨2 * L - 1, by omega⟩ :=
    (by unfold swLPieriAndWeakVec; have hn0 : 2 * L - 1 ≠ 0 := (by omega); simp [hn0])
  have hmid : ∑ w0 : Fin (L - 1), ((swLPieriAndWeakVec L hL p na ⟨2 * w0.1 + 1, by omega⟩) ^ 2 +
    (swLPieriAndWeakVec L hL p na ⟨2 * w0.1 + 2, by omega⟩) ^ 2) = ∑ w0 : Fin (L - 1), ((na ⟨2 *
    w0.1 + 1, by omega⟩) ^ 2 + (na ⟨2 * w0.1 + 2, by omega⟩) ^ 2) := by
    refine Finset.sum_congr rfl fun w0 _ ↦ ?_
    have hl1 : swLPieriAndWeakVec L hL p na ⟨2 * w0.1 + 1, by omega⟩ = swLCayleyCos (p.uNum w0)
      p.uvDen * na ⟨2 * w0.1 + 1, by omega⟩ - swLCayleySin (p.uNum w0) p.uvDen * na ⟨2 * w0.1 + 2,
      by omega⟩ := by
      unfold swLPieriAndWeakVec; have hn0 : 2 * w0.1 + 1 ≠ 0 := (by omega)
      have hlt : 2 * w0.1 + 1 < 2 * L - 1 := (by omega)
      have hdiv : ((2 * w0.1 + 1) - 1) / 2 = w0.1 := (by omega)
      have hmod : ((2 * w0.1 + 1) - 1) % 2 = 0 := (by omega); have hw0_eq : (⟨((2 * w0.1 + 1) - 1) /
        2, by omega⟩ : Fin (L - 1)) = w0 := (by ext; exact hdiv); have ha1 : (⟨2 * (((2 * w0.1 + 1)
        - 1) / 2) + 1, by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 1, by omega⟩ := (by ext; dsimp; omega)
      have ha2 : (⟨2 * (((2 * w0.1 + 1) - 1) / 2) + 2, by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 2,
        by omega⟩ := (by ext; dsimp; omega); simp only [hn0, ↓reduceDIte, hlt, hw0_eq, hmod,
        ↓reduceIte, ha1, ha2]
    have hl2 : swLPieriAndWeakVec L hL p na ⟨2 * w0.1 + 2, by omega⟩ = swLCayleySin (p.uNum w0)
      p.uvDen * na ⟨2 * w0.1 + 1, by omega⟩ + swLCayleyCos (p.uNum w0) p.uvDen * na ⟨2 * w0.1 + 2,
      by omega⟩ := by
      unfold swLPieriAndWeakVec; have hn0 : 2 * w0.1 + 2 ≠ 0 := (by omega)
      have hlt : 2 * w0.1 + 2 < 2 * L - 1 := (by omega)
      have hdiv : ((2 * w0.1 + 2) - 1) / 2 = w0.1 := (by omega)
      have hmod : ((2 * w0.1 + 2) - 1) % 2 = 1 := (by omega); have hw0_eq : (⟨((2 * w0.1 + 2) - 1) /
        2, by omega⟩ : Fin (L - 1)) = w0 := (by ext; exact hdiv); have ha1 : (⟨2 * (((2 * w0.1 + 2)
        - 1) / 2) + 1, by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 1, by omega⟩ := (by ext; dsimp; omega)
      have ha2 : (⟨2 * (((2 * w0.1 + 2) - 1) / 2) + 2, by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 2,
        by omega⟩ := (by ext; dsimp; omega); simp only [hn0, ↓reduceDIte, hlt, hw0_eq, hmod,
        one_ne_zero, ↓reduceIte, ha1, ha2]
    rw [hl1, hl2]; exact rot2_sq_sum (swLCayleyCos_sq_add_sin_sq hp)
  have hprobe := probe_sq_sum (x := na ⟨2 * L - 1, by omega⟩) (swLCayleyCos_sq_add_sin_sq (num :=
    p.vNum) hp); rw [h0, htop, hmid]; linarith
theorem swLPulseStepReal_normSq_add_cum {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} (hcs : ∀ w : Fin
  L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (st : Fin (2 * L) → ℝ) (cum surv : ℝ) {p : SwLPulseRat L} (hp
  : swLPulseValid p = true) (hin : swLNormSq st + cum = 1 ∧ 0 ≤ cum ∧ cum ≤ 1 ∧ 0 ≤ surv) :
    let out := swLPulseStepReal L hL cs st cum surv p
    swLNormSq out.1 + out.2.1 = 1 ∧ 0 ≤ out.2.1 ∧ out.2.1 ≤ 1 ∧ 0 ≤ out.2.2 := by
  intro out; unfold swLPulseValid at hp; rw [decide_eq_true_eq] at hp; rcases hin with ⟨hsum, hcum0,
    hcum1, hsurv0⟩; dsimp only [out, swLPulseStepReal]; have hg := swLGroverRotVec_normSq hcs st
  have hpieri := swLPieriAndWeakVec_normSq hL hp (swLGroverRotVec L cs st)
  have hnorm_nn : 0 ≤ swLNormSq (swLPieriAndWeakVec L hL p (swLGroverRotVec L cs st)) :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _; have hclick_nn : 0 ≤ (swLCayleySin p.vNum p.uvDen *
    (swLGroverRotVec L cs st) ⟨2 * L - 1, by omega⟩) ^ 2 := sq_nonneg _
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
theorem swLEvolutionRealAux_normSq_add_cum {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} (hcs : ∀ w :
  Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (pulses : List (SwLPulseRat L)) (hp : pulses.all
  swLPulseValid = true) (st : Fin (2 * L) → ℝ) (cum surv : ℝ) (hin : swLNormSq st + cum = 1 ∧ 0 ≤
  cum ∧ cum ≤ 1 ∧ 0 ≤ surv) :
    let out := swLEvolutionRealAux L hL cs st cum surv pulses
    swLNormSq out.1 + out.2.1 = 1 ∧ 0 ≤ out.2.1 ∧ out.2.1 ≤ 1 ∧ 0 ≤ out.2.2 := by
  induction pulses generalizing st cum surv with
  | nil => exact hin
  | cons p ps ih =>
    rw [List.all_cons, Bool.and_eq_true] at hp; exact ih hp.2 _ _ _ (swLPulseStepReal_normSq_add_cum
      hL hcs st cum surv hp.1 hin)
theorem swLEvolutionReal_normSq_add_cum {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} (hcs : ∀ w : Fin
  L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (pulses : List (SwLPulseRat L)) (hp : pulses.all swLPulseValid
  = true) :
    let out := swLEvolutionReal L hL cs pulses
    swLNormSq out.1 + out.2.1 = 1 ∧ 0 ≤ out.2.1 ∧ out.2.1 ≤ 1 ∧ 0 ≤ out.2.2 := by
  refine swLEvolutionRealAux_normSq_add_cum hL hcs pulses hp (fun j ↦ if j.1 = 0 then 1 else 0) 0 0
    ⟨?_, le_rfl, zero_le_one, le_rfl⟩; unfold swLNormSq; rw [sum_fin_interior_pairs hL]
  have hn0 : 2 * L - 1 ≠ 0 := (by omega); simp [hn0]
theorem isValidSwLOverlap_col_sq_sum {L : ℕ} {M : Fin (2 * L) → Fin (2 * L) → ℝ} (hM :
  IsValidSwLOverlap M) (j : Fin (2 * L)) : ∑ o : Fin (2 * L), (M o j) ^ 2 = 1 := by
  have h := hM.1 j j; simp only [↓reduceIte, sq] at h ⊢; exact h
theorem isValidSwLOverlap_parseval {L : ℕ} {M : Fin (2 * L) → Fin (2 * L) → ℝ} (hM :
  IsValidSwLOverlap M) (st : Fin (2 * L) → ℝ) : ∑ o : Fin (2 * L), (swLOrbitProj M st o) ^ 2 =
  swLNormSq st := by
  have horth := hM.1; unfold swLOrbitProj swLNormSq
  calc ∑ o : Fin (2 * L), (∑ j : Fin (2 * L), M o j * st j) ^ 2
    _ = ∑ o : Fin (2 * L), (∑ i : Fin (2 * L), M o i * st i) *
          (∑ j : Fin (2 * L), M o j * st j) :=
        Finset.sum_congr rfl fun _ _ ↦ sq _
    _ = ∑ o : Fin (2 * L), ∑ i : Fin (2 * L), ∑ j : Fin (2 * L),
          (st i * st j) * (M o i * M o j) := by
        refine Finset.sum_congr rfl fun o _ ↦ ?_; rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ∑ i : Fin (2 * L), ∑ j : Fin (2 * L),
          (st i * st j) * (∑ o : Fin (2 * L), M o i * M o j) := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ (Finset.mul_sum _ _ _).symm
    _ = ∑ i : Fin (2 * L), (st i) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_; simp only [horth i, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, sq]
theorem swLAttemptProbReal_nonneg {L : ℕ} (hL : 2 ≤ L) (M : Fin (2 * L) → Fin (2 * L) → ℝ) (st : Fin
  (2 * L) → ℝ) {cum : ℝ} (hcum0 : 0 ≤ cum) (h : ℕ) : 0 ≤ swLAttemptProbReal L hL M st cum h := by
  unfold swLAttemptProbReal; split_ifs <;> positivity
theorem swLAttemptProbReal_sum_one {L : ℕ} (hL : 2 ≤ L) {M : Fin (2 * L) → Fin (2 * L) → ℝ} (hM :
  IsValidSwLOverlap M) {st : Fin (2 * L) → ℝ} {cum : ℝ} (hcons : swLNormSq st + cum = 1) : ∑ h ∈
  Finset.range (L + 1), swLAttemptProbReal L hL M st cum h = 1 := by
  set q : Fin (2 * L) → ℝ := fun o ↦ (swLOrbitProj M st o) ^ 2 + cum * (M o ⟨2 * L - 1, by omega⟩) ^
    2
  have hq_sum : ∑ o : Fin (2 * L), q o = 1 := by
    dsimp only [q]; rw [Finset.sum_add_distrib, ← Finset.mul_sum, isValidSwLOverlap_parseval hM st,
      isValidSwLOverlap_col_sq_sum hM, mul_one, hcons]
  rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < L)]
  have h0 : swLAttemptProbReal L hL M st cum 0 = q ⟨0, by omega⟩ :=
    (by unfold swLAttemptProbReal; simp [q])
  have htop : swLAttemptProbReal L hL M st cum L = q ⟨2 * L - 1, by omega⟩ :=
    (by unfold swLAttemptProbReal; have hn0 : L ≠ 0 := (by omega); simp [hn0, q])
  have hmid : ∑ h ∈ Finset.Ico 1 L, swLAttemptProbReal L hL M st cum h = ∑ w0 : Fin (L - 1), (q ⟨2 *
    w0.1 + 1, by omega⟩ + q ⟨2 * w0.1 + 2, by omega⟩) := by
    rw [Finset.sum_Ico_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun i ↦ swLAttemptProbReal L hL M
      st cum (1 + i)) (L - 1)]; refine Finset.sum_congr rfl fun w0 _ ↦ ?_; unfold swLAttemptProbReal
    have hn0 : 1 + w0.1 ≠ 0 := (by omega); have hlt : 1 + w0.1 < L := (by omega); have hi1 : (⟨2 *
      (1 + w0.1) - 1, by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 1, by omega⟩ := (by ext; dsimp; omega)
    have hi2 : (⟨2 * (1 + w0.1), by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 2, by omega⟩ :=
      (by ext; dsimp; omega); simp only [hn0, ↓reduceIte, hlt, ↓reduceDIte, hi1, hi2, q]; ring
  rw [h0, htop, hmid, ← sum_fin_interior_pairs hL q, hq_sum]
/-! ## 3. WHNF-Forcing Combinators & `10^9`-Scale `IvInt` Interval Arithmetic -/
/-- Fixed-point scale `10^9` for amplitude, probability, and survival intervals. -/
def swScale : ℤ := 1000000000
/-- Finite-`N` (`n ≥ 96`) overlap padding `1` at `10^9` scale (`10⁻⁹`). -/
def swOrbPad : ℤ := 1
/-- Fixed-point scale `10^12` for multi-copy union-hit tail probabilities. -/
def swUnionScale : ℤ := 1000000000000
/-- Fixed-point scale `10^16` for stage value-function certificates. -/
def multiUnitScale : ℤ := 10000000000000000
/-- Closed integer interval `(lo, hi)` representing `[lo / 10^9, hi / 10^9]`. -/
abbrev IvInt : Type := ℤ × ℤ
/-- Force a `ℕ` value to its GMP literal in the Lean kernel before invoking `k`. -/
def withForcedNat {α : Type*} (x : ℕ) (k : ℕ → α) : α :=
  match x with
  | 0 => k 0
  | n + 1 => k (n + 1)
theorem withForcedNat_eq {α : Type*} (x : ℕ) (k : ℕ → α) : withForcedNat x k = k x := by
  cases x <;> rfl
/-- WHNF-forcing integer wrapper preventing call-by-name thunk duplication in `decide
  +kernel`. -/
def withForcedInt {α : Type*} : ℤ → (ℤ → α) → α
  | Int.ofNat n, k => withForcedNat n fun n' ↦ k (Int.ofNat n')
  | Int.negSucc n, k => withForcedNat n fun n' ↦ k (Int.negSucc n')
theorem withForcedInt_eq {α : Type*} (x : ℤ) (k : ℤ → α) : withForcedInt x k = k x := by
  cases x <;> simp only [withForcedInt, withForcedNat_eq]
/-- WHNF-forcing wrapper for a single `IvInt` pair. -/
def withForcedIv {α : Type*} (iv : IvInt) (k : IvInt → α) : α :=
  withForcedInt iv.1 fun a ↦ withForcedInt iv.2 fun b ↦ k (a, b)
theorem withForcedIv_eq {α : Type*} (iv : IvInt) (k : IvInt → α) : withForcedIv iv k = k iv := by
  unfold withForcedIv; rw [withForcedInt_eq, withForcedInt_eq]
/-- WHNF-forcing wrapper for a list of `IvInt` intervals. -/
def withForcedList {α : Type*} : List IvInt → (List IvInt → α) → α
  | [], k => k []
  | x :: xs, k => withForcedIv x fun x' ↦ withForcedList xs fun xs' ↦ k (x' :: xs')
theorem withForcedList_eq {α : Type*} (xs : List IvInt) (k : List IvInt → α) : withForcedList xs k =
  k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => unfold withForcedList; rw [withForcedIv_eq, ih]
/-- WHNF-forcing wrapper for a list of `ℕ` values. -/
def withForcedNatList {α : Type*} : List ℕ → (List ℕ → α) → α
  | [], k => k []
  | x :: xs, k => withForcedNat x fun x' ↦ withForcedNatList xs fun xs' ↦ k (x' :: xs')
theorem withForcedNatList_eq {α : Type*} (xs : List ℕ) (k : List ℕ → α) : withForcedNatList xs k = k
  xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => unfold withForcedNatList; rw [withForcedNat_eq, ih]
/-- WHNF-forcing wrapper for a conveyor trajectory state `(stIv, cumIv, survIv)`. -/
def withForcedState {α : Type*} (s : List IvInt × IvInt × IvInt)
    (k : List IvInt × IvInt × IvInt → α) : α :=
  withForcedList s.1 fun st ↦
    withForcedIv s.2.1 fun cum ↦
      withForcedIv s.2.2 fun surv ↦ k (st, cum, surv)
theorem withForcedState_eq {α : Type*} (s : List IvInt × IvInt × IvInt) (k : List IvInt × IvInt ×
  IvInt → α) : withForcedState s k = k s := by
  unfold withForcedState; rw [withForcedList_eq, withForcedIv_eq, withForcedIv_eq]
/-- Membership of `x: ℝ` in `[iv.1 / 10^9, iv.2 / 10^9]`. -/
def memIvInt (x : ℝ) (iv : IvInt) : Prop :=
  (iv.1 : ℝ) / (swScale : ℝ) ≤ x ∧ x ≤ (iv.2 : ℝ) / (swScale : ℝ)
/-- Componentwise `memIvInt` between `st: Fin (2 * L) → ℝ` and `stIv: List IvInt`. -/
def memIvIntVec {L : ℕ} (st : Fin (2 * L) → ℝ) (stIv : List IvInt) : Prop :=
  stIv.length = 2 * L ∧ ∀ j : Fin (2 * L), memIvInt (st j) (stIv.getD j.1 (0, 0))
/-- Certified interval addition at `10^9` scale. -/
def ivAddInt (a b : IvInt) : IvInt :=
  (a.1 + b.1, a.2 + b.2)
/-- Certified interval subtraction at `10^9` scale. -/
def ivSubInt (a b : IvInt) : IvInt :=
  (a.1 - b.2, a.2 - b.1)
/-- Certified interval multiplication at `10^9` scale with WHNF-forced endpoints. -/
def ivMulInt (a b : IvInt) : IvInt :=
  withForcedInt (a.1 * b.1) fun p1 ↦
    withForcedInt (a.1 * b.2) fun p2 ↦
      withForcedInt (a.2 * b.1) fun p3 ↦
        withForcedInt (a.2 * b.2) fun p4 ↦
          withForcedInt (min (min p1 p2) (min p3 p4)) fun lo ↦
            withForcedInt (max (max p1 p2) (max p3 p4)) fun hi ↦
              (lo / swScale, -((-hi) / swScale))
/-- Certified interval squaring at `10^9` scale exploiting `0 ≤ x^2`. -/
def ivSqInt (a : IvInt) : IvInt :=
  if 0 ≤ a.1 then
    ((a.1 * a.1) / swScale, -((-(a.2 * a.2)) / swScale))
  else if a.2 ≤ 0 then
    ((a.2 * a.2) / swScale, -((-(a.1 * a.1)) / swScale))
  else
    withForcedInt (max (-a.1) a.2) fun m ↦ (0, -((-(m * m)) / swScale))
/-- Outward-rounded `10^9`-scale interval enclosing `(num: ℝ) / (den: ℝ)` for `0 < den`. -/
def ivRatDiv (num den : ℤ) : IvInt :=
  withForcedInt (num * swScale) fun sc ↦ (sc / den, -((-sc) / den))
/-- Outward-rounded `10^9`-scale Pythagorean `(cos, sin)` intervals for `(uNum, uDen)`. -/
def ivPythag (uNum uDen : ℤ) : IvInt × IvInt :=
  withForcedInt (uDen * uDen + uNum * uNum) fun d ↦
    (ivRatDiv (uDen * uDen - uNum * uNum) d, ivRatDiv (2 * uNum * uDen) d)
theorem ediv_pos_le_real (x d : ℤ) (hd : 0 < d) : ((x / d : ℤ) : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
  have hd_r : (0 : ℝ) < (d : ℝ) := (by exact_mod_cast hd); rw [le_div_iff₀ hd_r]
  exact_mod_cast Int.ediv_mul_le x hd.ne'
theorem real_le_neg_ediv_neg_pos (x d : ℤ) (hd : 0 < d) : (x : ℝ) / (d : ℝ) ≤ ((-((-x) / d) : ℤ) :
  ℝ) := by
  have hd_r : (0 : ℝ) < (d : ℝ) := (by exact_mod_cast hd); rw [div_le_iff₀ hd_r]; have h1 : ((-x) /
    d) * d ≤ -x := Int.ediv_mul_le (-x) hd.ne'; have h2 : x ≤ -(((-x) / d) * d) := (by omega)
  rw [← neg_mul] at h2; exact_mod_cast h2
theorem ediv_scale_le_div (num den sc : ℤ) (hd : 0 < den) (hsc : 0 < sc) : (((num * sc) / den : ℤ) :
  ℝ) / (sc : ℝ) ≤ (num : ℝ) / (den : ℝ) := by
  have hd_r : (0 : ℝ) < (den : ℝ) := (by exact_mod_cast hd); have hsc_r : (0 : ℝ) < (sc : ℝ) :=
    (by exact_mod_cast hsc); have h1 := div_le_div_of_nonneg_right (ediv_pos_le_real (num * sc) den
    hd) hsc_r.le; refine h1.trans_eq ?_; rw [Int.cast_mul]; field_simp [hd_r.ne', hsc_r.ne']
theorem div_le_ceil_ediv_scale (num den sc : ℤ) (hd : 0 < den) (hsc : 0 < sc) : (num : ℝ) / (den :
  ℝ) ≤ ((-((-(num * sc)) / den) : ℤ) : ℝ) / (sc : ℝ) := by
  have hd_r : (0 : ℝ) < (den : ℝ) := (by exact_mod_cast hd); have hsc_r : (0 : ℝ) < (sc : ℝ) :=
    (by exact_mod_cast hsc); have h1 := div_le_div_of_nonneg_right (real_le_neg_ediv_neg_pos (num *
    sc) den hd) hsc_r.le; refine (?_ : (num : ℝ) / (den : ℝ) = ((num * sc : ℤ) : ℝ) / (den : ℝ) /
    (sc : ℝ)).trans_le h1; rw [Int.cast_mul]; field_simp [hd_r.ne', hsc_r.ne']
theorem memIvInt_one : memIvInt 1 (swScale, swScale) := by
  have hS : (swScale : ℝ) ≠ 0 := (by unfold swScale; norm_num)
  unfold memIvInt; dsimp only; rw [div_self hS]; exact ⟨le_rfl, le_rfl⟩
theorem memIvInt_zero : memIvInt 0 (0, 0) := by
  unfold memIvInt; dsimp only; rw [Int.cast_zero, zero_div]; exact ⟨le_rfl, le_rfl⟩
theorem memIvInt_ivRatDiv (num den : ℤ) (hden : 0 < den) : memIvInt ((num : ℝ) / (den : ℝ))
  (ivRatDiv num den) := by
  have hS_pos : (0 : ℤ) < swScale := (by unfold swScale; norm_num); unfold ivRatDiv
  rw [withForcedInt_eq]; exact ⟨ediv_scale_le_div num den swScale hden hS_pos,
    div_le_ceil_ediv_scale num den swScale hden hS_pos⟩
theorem memIvInt_ivPythag (num : ℤ) {den : ℕ} (hden : 0 < den) : memIvInt (swLCayleyCos num den)
  (ivPythag num (den : ℤ)).1 ∧ memIvInt (swLCayleySin num den) (ivPythag num (den : ℤ)).2 := by
  have hd_z : (0 : ℤ) < (den : ℤ) := (by exact_mod_cast hden); have hsum_pos : 0 < (den : ℤ) * (den
    : ℤ) + num * num := (by nlinarith); unfold ivPythag swLCayleyCos swLCayleySin
  rw [withForcedInt_eq]
  have hc : ((den : ℝ) ^ 2 - (num : ℝ) ^ 2) / ((den : ℝ) ^ 2 + (num : ℝ) ^ 2) = (((den : ℤ) * (den :
    ℤ) - num * num : ℤ) : ℝ) / (((den : ℤ) * (den : ℤ) + num * num : ℤ) : ℝ) := (by push_cast; ring)
  have hs : (2 * (num : ℝ) * (den : ℝ)) / ((den : ℝ) ^ 2 + (num : ℝ) ^ 2) = ((2 * num * (den : ℤ) :
    ℤ) : ℝ) / (((den : ℤ) * (den : ℤ) + num * num : ℤ) : ℝ) := (by push_cast; ring); rw [hc, hs];
    exact ⟨memIvInt_ivRatDiv _ _ hsum_pos, memIvInt_ivRatDiv _ _ hsum_pos⟩
theorem memIvInt_ivAddInt {x y : ℝ} {a b : IvInt} (hx : memIvInt x a) (hy : memIvInt y b) : memIvInt
  (x + y) (ivAddInt a b) := by
  rcases hx with ⟨hx1, hx2⟩; rcases hy with ⟨hy1, hy2⟩; unfold memIvInt ivAddInt; dsimp only;
    push_cast; rw [add_div, add_div]; exact ⟨by linarith, by linarith⟩
theorem memIvInt_ivSubInt {x y : ℝ} {a b : IvInt} (hx : memIvInt x a) (hy : memIvInt y b) : memIvInt
  (x - y) (ivSubInt a b) := by
  rcases hx with ⟨hx1, hx2⟩; rcases hy with ⟨hy1, hy2⟩; unfold memIvInt ivSubInt; dsimp only;
    push_cast; rw [sub_div, sub_div]; exact ⟨by linarith, by linarith⟩
theorem memIvInt_ivMulInt {x y : ℝ} {a b : IvInt} (hx : memIvInt x a) (hy : memIvInt y b) : memIvInt
  (x * y) (ivMulInt a b) := by
  have hS_pos : (0 : ℤ) < swScale := (by unfold swScale; norm_num); have hS : (0 : ℝ) < (swScale :
    ℝ) := (by unfold swScale; norm_num); unfold ivMulInt; simp only [withForcedInt_eq]
  unfold memIvInt at hx hy ⊢; dsimp only; set X : ℝ := x * (swScale : ℝ); set Y : ℝ := y * (swScale
    : ℝ); have hX1 : (a.1 : ℝ) ≤ X := (div_le_iff₀ hS).1 hx.1; have hX2 : X ≤ (a.2 : ℝ) :=
    (le_div_iff₀ hS).1 hx.2; have hY1 : (b.1 : ℝ) ≤ Y := (div_le_iff₀ hS).1 hy.1; have hY2 : Y ≤
    (b.2 : ℝ) := (le_div_iff₀ hS).1 hy.2; set loZ : ℤ := min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2
    * b.1) (a.2 * b.2)); set hiZ : ℤ := max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 *
    b.2)); have hlo11 : (loZ : ℝ) ≤ (a.1 : ℝ) * (b.1 : ℝ) :=
    (by exact_mod_cast (min_le_left _ _).trans (min_le_left _ _)); have hlo12 : (loZ : ℝ) ≤ (a.1 :
    ℝ) * (b.2 : ℝ) := (by exact_mod_cast (min_le_left _ _).trans (min_le_right _ _))
  have hlo21 : (loZ : ℝ) ≤ (a.2 : ℝ) * (b.1 : ℝ) :=
    (by exact_mod_cast (min_le_right _ _).trans (min_le_left _ _)); have hlo22 : (loZ : ℝ) ≤ (a.2 :
    ℝ) * (b.2 : ℝ) := (by exact_mod_cast (min_le_right _ _).trans (min_le_right _ _))
  have hhi11 : (a.1 : ℝ) * (b.1 : ℝ) ≤ (hiZ : ℝ) :=
    (by exact_mod_cast (le_max_left _ _).trans (le_max_left _ _)); have hhi12 : (a.1 : ℝ) * (b.2 :
    ℝ) ≤ (hiZ : ℝ) := (by exact_mod_cast (le_max_right _ _).trans (le_max_left _ _))
  have hhi21 : (a.2 : ℝ) * (b.1 : ℝ) ≤ (hiZ : ℝ) :=
    (by exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)); have hhi22 : (a.2 : ℝ) * (b.2 :
    ℝ) ≤ (hiZ : ℝ) := (by exact_mod_cast (le_max_right _ _).trans (le_max_right _ _))
  have hXY_lo : (loZ : ℝ) ≤ X * Y := by
    rcases le_or_gt 0 X with hX | hX
    · rcases le_or_gt 0 (b.1 : ℝ) with hb1 | hb1 <;> nlinarith
    · rcases le_or_gt 0 (b.2 : ℝ) with hb2 | hb2 <;> nlinarith
  have hXY_hi : X * Y ≤ (hiZ : ℝ) := by
    rcases le_or_gt 0 X with hX | hX
    · rcases le_or_gt 0 (b.2 : ℝ) with hb2 | hb2 <;> nlinarith
    · rcases le_or_gt 0 (b.1 : ℝ) with hb1 | hb1 <;> nlinarith
  have hXY_eq : X * Y / (swScale : ℝ) / (swScale : ℝ) = x * y :=
    (by dsimp [X, Y]; field_simp [hS.ne']); constructor
  · have hd := ediv_pos_le_real loZ swScale hS_pos; have hd2 := div_le_div_of_nonneg_right (hd.trans
      (div_le_div_of_nonneg_right hXY_lo hS.le)) hS.le; linarith [hd2, hXY_eq]
  · have hd := real_le_neg_ediv_neg_pos hiZ swScale hS_pos; have hd1 : X * Y / (swScale : ℝ) ≤
      ((-((-hiZ) / swScale) : ℤ) : ℝ) := (div_le_div_of_nonneg_right hXY_hi hS.le).trans hd
    have hd2 := div_le_div_of_nonneg_right hd1 hS.le; linarith [hd2, hXY_eq]
theorem memIvInt_ivSqInt {x : ℝ} {a : IvInt} (hx : memIvInt x a) : memIvInt (x ^ 2) (ivSqInt a) :=
  by
  have hS_pos : (0 : ℤ) < swScale := (by unfold swScale; norm_num); have hS : (0 : ℝ) < (swScale :
    ℝ) := (by unfold swScale; norm_num); unfold memIvInt at hx ⊢; set X : ℝ := x * (swScale : ℝ)
  have hX1 : (a.1 : ℝ) ≤ X := (div_le_iff₀ hS).1 hx.1; have hX2 : X ≤ (a.2 : ℝ) := (le_div_iff₀
    hS).1 hx.2; have hX_eq : X ^ 2 / (swScale : ℝ) / (swScale : ℝ) = x ^ 2 :=
    (by dsimp [X]; field_simp [hS.ne']); unfold ivSqInt; by_cases ha1 : 0 ≤ a.1
  · simp only [ha1, ↓reduceIte]; have ha1_r : (0 : ℝ) ≤ (a.1 : ℝ) := (by exact_mod_cast ha1)
    have hlo_sq : ((a.1 * a.1 : ℤ) : ℝ) ≤ X ^ 2 := (by push_cast; nlinarith); have hhi_sq : X ^ 2 ≤
      ((a.2 * a.2 : ℤ) : ℝ) := (by push_cast; nlinarith); constructor
    · have hd := ediv_pos_le_real (a.1 * a.1) swScale hS_pos
      have hd2 := div_le_div_of_nonneg_right (hd.trans (div_le_div_of_nonneg_right hlo_sq hS.le))
        hS.le; linarith [hd2, hX_eq]
    · have hd := real_le_neg_ediv_neg_pos (a.2 * a.2) swScale hS_pos; have hd2 :=
        div_le_div_of_nonneg_right ((div_le_div_of_nonneg_right hhi_sq hS.le).trans hd) hS.le
      linarith [hd2, hX_eq]
  · simp only [ha1, ↓reduceIte]; by_cases ha2 : a.2 ≤ 0
    · simp only [ha2, ↓reduceIte]; have ha2_r : (a.2 : ℝ) ≤ 0 := (by exact_mod_cast ha2)
      have hlo_sq : ((a.2 * a.2 : ℤ) : ℝ) ≤ X ^ 2 := (by push_cast; nlinarith)
      have hhi_sq : X ^ 2 ≤ ((a.1 * a.1 : ℤ) : ℝ) := (by push_cast; nlinarith); constructor
      · have hd := ediv_pos_le_real (a.2 * a.2) swScale hS_pos; have hd2 :=
          div_le_div_of_nonneg_right (hd.trans (div_le_div_of_nonneg_right hlo_sq hS.le)) hS.le
        linarith [hd2, hX_eq]
      · have hd := real_le_neg_ediv_neg_pos (a.1 * a.1) swScale hS_pos; have hd2 :=
          div_le_div_of_nonneg_right ((div_le_div_of_nonneg_right hhi_sq hS.le).trans hd) hS.le
        linarith [hd2, hX_eq]
    · simp only [ha2, ↓reduceIte, withForcedInt_eq]; set m : ℤ := max (-a.1) a.2
      have hm1 : -(m : ℝ) ≤ (a.1 : ℝ) := by
        have h : -a.1 ≤ m := le_max_left (-a.1) a.2; have hr : (-(a.1 : ℝ)) ≤ (m : ℝ) :=
          (by exact_mod_cast h); linarith
      have hm2 : (a.2 : ℝ) ≤ (m : ℝ) := (by exact_mod_cast le_max_right (-a.1) a.2)
      have hhi_sq : X ^ 2 ≤ ((m * m : ℤ) : ℝ) := (by push_cast; nlinarith); constructor
      · rw [Int.cast_zero, zero_div]; exact sq_nonneg x
      · have hd := real_le_neg_ediv_neg_pos (m * m) swScale hS_pos; have hd2 :=
          div_le_div_of_nonneg_right ((div_le_div_of_nonneg_right hhi_sq hS.le).trans hd) hS.le
        linarith [hd2, hX_eq]
/-! ## 4. Shifted Grover Angle Ratios (`n ≥ 96, L ≤ r ≤ 1024`) & Trig Bucket Checker -/
/-- Pure-integer `10^18`-stepped double-angle trig checker on `[a / d, b / e] ⊆ (0, 1]`. -/
def checkSwLTrigRat (a d b e cLo cHi sLo sHi : ℤ) : Bool :=
  let s18 : ℤ := 1000000000000000000
  withForcedInt ((a * s18) / d) fun qLoLo ↦
    withForcedInt (-((-(a * s18)) / d)) fun qLoHi ↦
      withForcedInt (-((-(b * s18)) / e)) fun qHiHi ↦
        withForcedInt ((qLoLo * (24 * s18 * s18 - qLoLo * qLoLo)) / (48 * s18 * s18)) fun s2Lo ↦
          withForcedInt (s18 - (-((-(qLoHi * qLoHi)) / (32 * s18)))) fun c4Lo ↦
            withForcedInt ((2 * c4Lo * c4Lo) / s18 - s18) fun c2Lo ↦
              withForcedInt (s18 - (-((-(qHiHi * qHiHi)) / (128 * s18)))) fun c8H ↦
                withForcedInt ((2 * c8H * c8H) / s18 - s18) fun c4H ↦
                  withForcedInt ((2 * c4H * c4H) / s18 - s18) fun c2H ↦
                    withForcedInt ((2 * c2H * c2H) / s18 - s18) fun c1H ↦
                      decide (0 < a ∧ 0 < d ∧ 0 ≤ b ∧ 0 < e ∧ b ≤ e ∧
                        0 ≤ cLo ∧ 0 ≤ cHi ∧ 0 ≤ sLo ∧ 0 ≤ sHi ∧
                        0 < qLoLo ∧ qLoHi ≤ s18 ∧ qHiHi ≤ s18 ∧
                        0 ≤ s2Lo ∧ 0 ≤ c4Lo ∧ 0 ≤ c2Lo ∧
                        sLo * s18 * s18 ≤ 2 * s2Lo * c2Lo * swScale ∧
                        0 ≤ c8H ∧ 0 ≤ c4H ∧ 0 ≤ c2H ∧
                        cLo * s18 ≤ c1H * swScale ∧
                        swScale * swScale ≤ cLo * cLo + sHi * sHi ∧
                        swScale * swScale ≤ sLo * sLo + cHi * cHi)
theorem sq_bound_of_sin_cos_ge {u v a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : u ^ 2 + v ^ 2 = 1) (hab
  : 1 ≤ a ^ 2 + b ^ 2) (hu : a ≤ u) : v ≤ b := by
  by_contra hlt
  have h_a2 : a ^ 2 ≤ u ^ 2 := (by nlinarith); have h_b2 : b ^ 2 < v ^ 2 := (by nlinarith); linarith
theorem checkSwLTrigRat_sound {a d b e cLo cHi sLo sHi : ℤ} {φ : ℝ} (hlo : (a : ℝ) / (d : ℝ) ≤ φ)
  (hhi : φ ≤ (b : ℝ) / (e : ℝ)) (hchk : checkSwLTrigRat a d b e cLo cHi sLo sHi = true) : memIvInt
  (Real.cos φ) (cLo, cHi) ∧ memIvInt (Real.sin φ) (sLo, sHi) := by
  unfold checkSwLTrigRat at hchk; simp only [withForcedInt_eq, decide_eq_true_eq] at hchk
  rcases hchk with ⟨ha, hd, hb0, he, hbe, hcLo0, hcHi0, hsLo0, hsHi0, hqLoLo_pos, hqLoHi_le,
    hqHiHi_le, hs2Lo0, hc4Lo0, hc2Lo0, hsin_ineq, hc8H0, hc4H0, hc2H0, hcos_ineq, hcs_hi, hsc_hi⟩
  set s18 : ℤ := 1000000000000000000; have hs18_pos : (0 : ℤ) < s18 := (by dsimp [s18]; norm_num)
  have hs18_r : (0 : ℝ) < (s18 : ℝ) := (by dsimp [s18]; norm_num)
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); set qLoLo : ℤ := (a * s18) /
    d; set qLoHi : ℤ := -((-(a * s18)) / d); set qHiHi : ℤ := -((-(b * s18)) / e); set s2Lo : ℤ :=
    (qLoLo * (24 * s18 * s18 - qLoLo * qLoLo)) / (48 * s18 * s18); set c4Lo : ℤ := s18 - (-((-(qLoHi
    * qLoHi)) / (32 * s18))); set c2Lo : ℤ := (2 * c4Lo * c4Lo) / s18 - s18; set c8H : ℤ := s18 -
    (-((-(qHiHi * qHiHi)) / (128 * s18)))
  set c4H : ℤ := (2 * c8H * c8H) / s18 - s18; set c2H : ℤ := (2 * c4H * c4H) / s18 - s18
  set c1H : ℤ := (2 * c2H * c2H) / s18 - s18; set qLo : ℝ := (a : ℝ) / (d : ℝ); set qHi : ℝ := (b :
    ℝ) / (e : ℝ); set xLo : ℝ := (qLoLo : ℝ) / (s18 : ℝ); set xHi : ℝ := (qLoHi : ℝ) / (s18 : ℝ);
    set yHi : ℝ := (qHiHi : ℝ) / (s18 : ℝ)
  have hxLo_le_qLo : xLo ≤ qLo := ediv_scale_le_div a d s18 hd hs18_pos; have hqLo_le_xHi : qLo ≤
    xHi := div_le_ceil_ediv_scale a d s18 hd hs18_pos; have hqHi_le_yHi : qHi ≤ yHi :=
    div_le_ceil_ediv_scale b e s18 he hs18_pos
  have hxLo_pos : 0 < xLo := div_pos (by exact_mod_cast hqLoLo_pos) hs18_r
  have hxHi_le1 : xHi ≤ 1 := (div_le_one hs18_r).2 (by exact_mod_cast hqLoHi_le)
  have hyHi_le1 : yHi ≤ 1 := (div_le_one hs18_r).2 (by exact_mod_cast hqHiHi_le)
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hs2_le : (s2Lo : ℝ) / (s18 : ℝ) ≤ Real.sin (qLo / 2) := by
    have hsin_mono : Real.sin (xLo / 2) ≤ Real.sin (qLo / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have hcube : xLo / 2 - (xLo / 2) ^ 3 / 6 ≤ Real.sin (xLo / 2) := Real.sin_ge_sub_cube
      (by positivity); have hd48 : (0 : ℤ) < 48 * s18 * s18 := (by dsimp [s18]; norm_num)
    have hdiv := ediv_pos_le_real (qLoLo * (24 * s18 * s18 - qLoLo * qLoLo)) (48 * s18 * s18) hd48
    have hdiv2 := div_le_div_of_nonneg_right hdiv hs18_r.le; have halg : ((qLoLo * (24 * s18 * s18 -
      qLoLo * qLoLo) : ℤ) : ℝ) / ((48 * s18 * s18 : ℤ) : ℝ) / (s18 : ℝ) = xLo / 2 - (xLo / 2) ^ 3 /
      6 := (by dsimp [xLo]; push_cast; field_simp [hs18_r.ne']; ring); dsimp [s2Lo]; linarith
  have hc2_le : (c2Lo : ℝ) / (s18 : ℝ) ≤ Real.cos (qLo / 2) := by
    have hcos_mono : Real.cos (xHi / 2) ≤ Real.cos (qLo / 2) := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith) (by linarith); have hd32 : (0 : ℤ) < 32 * s18 :=
      (by dsimp [s18]; norm_num)
    have hceil := real_le_neg_ediv_neg_pos (qLoHi * qLoHi) (32 * s18) hd32
    have h1 : (c4Lo : ℝ) / (s18 : ℝ) ≤ 1 - (xHi / 4) ^ 2 / 2 := by
      have hsub : (c4Lo : ℝ) ≤ (s18 : ℝ) - ((qLoHi * qLoHi : ℤ) : ℝ) / ((32 * s18 : ℤ) : ℝ) :=
        (by dsimp [c4Lo]; rw [Int.cast_sub]; linarith [hceil]); have hdiv :=
        div_le_div_of_nonneg_right hsub hs18_r.le; have halg : ((s18 : ℝ) - ((qLoHi * qLoHi : ℤ) :
        ℝ) / ((32 * s18 : ℤ) : ℝ)) / (s18 : ℝ) = 1 - (xHi / 4) ^ 2 / 2 :=
        (by dsimp [xHi]; push_cast; field_simp [hs18_r.ne']; ring); linarith
    have hc4_cos : (c4Lo : ℝ) / (s18 : ℝ) ≤ Real.cos ((xHi / 2) / 2) :=
      (by rw [show (xHi / 2) / 2 = xHi / 4 by ring]; exact h1.trans Real.one_sub_sq_div_two_le_cos)
    have hc4_nn : 0 ≤ (c4Lo : ℝ) / (s18 : ℝ) := div_nonneg (by exact_mod_cast hc4Lo0) hs18_r.le
    have hstep := two_mul_sq_sub_one_le_cos hc4_nn hc4_cos; have hd_c2 := ediv_pos_le_real (2 * c4Lo
      * c4Lo) s18 hs18_pos
    have hc2_alg : (c2Lo : ℝ) / (s18 : ℝ) ≤ 2 * ((c4Lo : ℝ) / (s18 : ℝ)) ^ 2 - 1 := by
      have hsub : (c2Lo : ℝ) ≤ ((2 * c4Lo * c4Lo : ℤ) : ℝ) / (s18 : ℝ) - (s18 : ℝ) :=
        (by dsimp [c2Lo]; rw [Int.cast_sub]; linarith [hd_c2]); have hdiv :=
        div_le_div_of_nonneg_right hsub hs18_r.le; have halg : (((2 * c4Lo * c4Lo : ℤ) : ℝ) / (s18 :
        ℝ) - (s18 : ℝ)) / (s18 : ℝ) = 2 * ((c4Lo : ℝ) / (s18 : ℝ)) ^ 2 - 1 :=
        (by push_cast; field_simp [hs18_r.ne']); linarith
    exact (hc2_alg.trans hstep).trans hcos_mono
  have hsin_φ : (sLo : ℝ) / (swScale : ℝ) ≤ Real.sin φ := by
    have hsin_qlo : 2 * ((s2Lo : ℝ) / (s18 : ℝ)) * ((c2Lo : ℝ) / (s18 : ℝ)) ≤ Real.sin qLo := by
      have h2s : Real.sin qLo = 2 * Real.sin (qLo / 2) * Real.cos (qLo / 2) := by
        conv_lhs => rw [show qLo = 2 * (qLo / 2) by ring]
        exact Real.sin_two_mul (qLo / 2)
      rw [h2s]
      have hs2_nn : 0 ≤ (s2Lo : ℝ) / (s18 : ℝ) := div_nonneg (by exact_mod_cast hs2Lo0) hs18_r.le
      have hc2_nn : 0 ≤ (c2Lo : ℝ) / (s18 : ℝ) := div_nonneg (by exact_mod_cast hc2Lo0) hs18_r.le
      nlinarith
    have hsin_ineq_r : (sLo : ℝ) / (swScale : ℝ) ≤ 2 * ((s2Lo : ℝ) / (s18 : ℝ)) * ((c2Lo : ℝ) / (s18
      : ℝ)) := by
      rw [mul_assoc, div_mul_div_comm, ← mul_div_assoc, div_le_div_iff₀ hS (mul_pos hs18_r hs18_r)]
      have hcast : ((sLo * s18 * s18 : ℤ) : ℝ) ≤ ((2 * s2Lo * c2Lo * swScale : ℤ) : ℝ) :=
        (by exact_mod_cast hsin_ineq); push_cast at hcast; linarith
    have hsin_mono : Real.sin qLo ≤ Real.sin φ := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith) (by linarith) hlo; exact (hsin_ineq_r.trans hsin_qlo).trans hsin_mono
  have hcos_φ : (cLo : ℝ) / (swScale : ℝ) ≤ Real.cos φ := by
    have hd128 : (0 : ℤ) < 128 * s18 := (by dsimp [s18]; norm_num); have hceil :=
      real_le_neg_ediv_neg_pos (qHiHi * qHiHi) (128 * s18) hd128
    have hc8_le : (c8H : ℝ) / (s18 : ℝ) ≤ Real.cos (yHi / 8) := by
      have hsub : (c8H : ℝ) ≤ (s18 : ℝ) - ((qHiHi * qHiHi : ℤ) : ℝ) / ((128 * s18 : ℤ) : ℝ) :=
        (by dsimp [c8H]; rw [Int.cast_sub]; linarith [hceil]); have hdiv :=
        div_le_div_of_nonneg_right hsub hs18_r.le; have halg : ((s18 : ℝ) - ((qHiHi * qHiHi : ℤ) :
        ℝ) / ((128 * s18 : ℤ) : ℝ)) / (s18 : ℝ) = 1 - (yHi / 8) ^ 2 / 2 :=
        (by dsimp [yHi]; push_cast; field_simp [hs18_r.ne']; ring)
      exact (hdiv.trans_eq halg).trans Real.one_sub_sq_div_two_le_cos
    have hstep_div : ∀ (u v : ℤ) (θ : ℝ), 0 ≤ u → v = (2 * u * u) / s18 - s18 → (u : ℝ) / (s18 : ℝ)
      ≤ Real.cos (θ / 2) → (v : ℝ) / (s18 : ℝ) ≤ Real.cos θ := by
      intro u v θ hu0 hv hcos_u; have hd_u := ediv_pos_le_real (2 * u * u) s18 hs18_pos
      have hv_alg : (v : ℝ) / (s18 : ℝ) ≤ 2 * ((u : ℝ) / (s18 : ℝ)) ^ 2 - 1 := by
        rw [hv]
        have hsub : (((2 * u * u) / s18 - s18 : ℤ) : ℝ) ≤ ((2 * u * u : ℤ) : ℝ) / (s18 : ℝ) - (s18 :
          ℝ) := (by rw [Int.cast_sub]; linarith [hd_u])
        have hdiv := div_le_div_of_nonneg_right hsub hs18_r.le; have halg : (((2 * u * u : ℤ) : ℝ) /
          (s18 : ℝ) - (s18 : ℝ)) / (s18 : ℝ) = 2 * ((u : ℝ) / (s18 : ℝ)) ^ 2 - 1 :=
          (by push_cast; field_simp [hs18_r.ne']); linarith
      exact hv_alg.trans (two_mul_sq_sub_one_le_cos (div_nonneg (by exact_mod_cast hu0) hs18_r.le)
        hcos_u)
    have hc4_le : (c4H : ℝ) / (s18 : ℝ) ≤ Real.cos (yHi / 4) := hstep_div c8H c4H (yHi / 4) hc8H0
      rfl (by rwa [show (yHi / 4) / 2 = yHi / 8 by ring])
    have hc2_le' : (c2H : ℝ) / (s18 : ℝ) ≤ Real.cos (yHi / 2) := hstep_div c4H c2H (yHi / 2) hc4H0
      rfl (by rwa [show (yHi / 2) / 2 = yHi / 4 by ring]); have hc1_le : (c1H : ℝ) / (s18 : ℝ) ≤
      Real.cos yHi := hstep_div c2H c1H yHi hc2H0 rfl hc2_le'
    have hcos_ineq_r : (cLo : ℝ) / (swScale : ℝ) ≤ (c1H : ℝ) / (s18 : ℝ) :=
      (by rw [div_le_div_iff₀ hS hs18_r]; exact_mod_cast hcos_ineq); have hcos_mono : Real.cos yHi ≤
      Real.cos φ := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (hhi.trans
      hqHi_le_yHi); exact (hcos_ineq_r.trans hc1_le).trans hcos_mono
  have hcs_hi_r : 1 ≤ ((cLo : ℝ) / (swScale : ℝ)) ^ 2 + ((sHi : ℝ) / (swScale : ℝ)) ^ 2 := by
    have hcast : ((swScale * swScale : ℤ) : ℝ) ≤ ((cLo * cLo + sHi * sHi : ℤ) : ℝ) :=
      (by exact_mod_cast hcs_hi); push_cast at hcast; rw [div_pow, div_pow, ← add_div, one_le_div
      (sq_pos_of_pos hS)]; nlinarith
  have hsc_hi_r : 1 ≤ ((sLo : ℝ) / (swScale : ℝ)) ^ 2 + ((cHi : ℝ) / (swScale : ℝ)) ^ 2 := by
    have hcast : ((swScale * swScale : ℤ) : ℝ) ≤ ((sLo * sLo + cHi * cHi : ℤ) : ℝ) :=
      (by exact_mod_cast hsc_hi); push_cast at hcast; rw [div_pow, div_pow, ← add_div, one_le_div
      (sq_pos_of_pos hS)]; nlinarith
  have hsin_ub : Real.sin φ ≤ (sHi : ℝ) / (swScale : ℝ) := sq_bound_of_sin_cos_ge (div_nonneg
    (by exact_mod_cast hcLo0) hS.le) (div_nonneg (by exact_mod_cast hsHi0) hS.le)
    (Real.cos_sq_add_sin_sq φ) hcs_hi_r hcos_φ; have hcos_ub : Real.cos φ ≤ (cHi : ℝ) / (swScale :
    ℝ) := sq_bound_of_sin_cos_ge (div_nonneg (by exact_mod_cast hsLo0) hS.le) (div_nonneg
    (by exact_mod_cast hcHi0) hS.le) (Real.sin_sq_add_cos_sq φ) hsc_hi_r hsin_φ; exact ⟨⟨hcos_φ,
    hcos_ub⟩, ⟨hsin_φ, hsin_ub⟩⟩
/-- Pure-integer ratio-bound check for stratum `1 ≤ shiftW ≤ 7` on `[rMin, rMax]`. -/
def checkSwLStratumRatio (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) : Bool :=
  let s20 : ℤ := 100000000000000000000
  decide (shiftW + 1 ≤ rMin ∧ rMin ≤ rMax ∧ rMax ≤ 1024 ∧ 1 ≤ shiftW ∧ shiftW ≤ 7 ∧
    0 < ratioLo ∧ 1 < ratioHi ∧ ratioHi ≤ swScale ∧
    (ratioLo + 1) * (ratioLo + 1) * (rMin : ℤ) ≤
      swScale * swScale * ((rMin : ℤ) - (shiftW : ℤ)) ∧
    swScale * swScale * ((rMax : ℤ) - (shiftW : ℤ)) ≤
      ((ratioHi - 1) * (ratioHi - 1) - (shiftW : ℤ)) * (rMax : ℤ) ∧
    ratioLo * s20 ≤ (ratioLo + 1) * (s20 - 1) ∧
    (ratioHi - 1) * s20 ≤ ratioHi * (s20 - 1))
/-- Pure-integer `2 ≤ L ≤ 8` bucket angle checker for `r ∈ [rMin, rMax]`. -/
def checkSwLBucketAngles (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  let s11 : ℤ := 100000000000
  withForcedInt ((tauNum : ℤ) * s11 + (tauDen : ℤ)) fun q1HiNum ↦
    withForcedInt ((tauDen : ℤ) * s11) fun q1HiDen ↦
      decide (2 ≤ L ∧ L ≤ 8 ∧ L ≤ rMin ∧ rMin ≤ rMax ∧ rMax ≤ 1024 ∧
        0 < tauNum ∧ 0 < tauDen ∧ ratios.length = L - 1 ∧ trigIvs.length = L) &&
      match trigIvs with
      | [] => false
      | (c0, s0) :: restTrig =>
          checkSwLTrigRat (tauNum : ℤ) (tauDen : ℤ) q1HiNum q1HiDen
            c0.1 c0.2 s0.1 s0.2 &&
          (List.range (L - 1)).all fun idx ↦
            let w := idx + 1
            let rat := ratios.getD idx (0, 0)
            let cs := restTrig.getD idx ((0, 0), (0, 0))
            checkSwLStratumRatio rMin rMax w rat.1 rat.2 &&
            checkSwLTrigRat ((tauNum : ℤ) * rat.1) ((tauDen : ℤ) * swScale)
              (q1HiNum * rat.2) (q1HiDen * swScale) cs.1.1 cs.1.2 cs.2.1 cs.2.2
theorem arcsin_small_boundsL {x : ℝ} (hx0 : 0 < x) (hx_ub : x ≤ 1 / 8000000000000) : 0 < Real.arcsin
  x ∧ Real.arcsin x ≤ 1 / 400000000000 ∧ x ≤ Real.arcsin x ∧ (1 - 1 / 100000000000000000000) *
  Real.arcsin x ≤ x := by
  have hx1 : x ≤ 1 := (by linarith)
  have hsin_x : Real.sin (Real.arcsin x) = x := Real.sin_arcsin (by linarith) hx1; have hα_pos : 0 <
    Real.arcsin x := Real.arcsin_pos.2 hx0
  have hα_lb : x ≤ Real.arcsin x := self_le_arcsin hx0.le hx1; set u : ℝ := 1 / 400000000000
  have hu_pos : 0 < u := (by dsimp [u]; norm_num)
  have hx_le_sinu : x ≤ Real.sin u := by
    have hcube := (Real.sin_gt_sub_cube hu_pos).le
    have hnum : (1 : ℝ) / 8000000000000 ≤ u - u ^ 3 / 6 := (by dsimp [u]; norm_num); linarith
  have hα_le : Real.arcsin x ≤ u := by
    have h1 := Real.arcsin_le_arcsin hx_le_sinu
    have h2 : Real.arcsin (Real.sin u) = u := Real.arcsin_sin
      (by dsimp [u]; linarith [Real.pi_gt_three]) (by dsimp [u]; linarith [Real.pi_gt_three])
    linarith
  have hα_ub : (1 - 1 / 100000000000000000000) * Real.arcsin x ≤ x := by
    have hcube := (Real.sin_gt_sub_cube hα_pos).le; rw [hsin_x] at hcube
    have hsq : (Real.arcsin x) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hα_pos.le hα_le 2
    have hu_sq : u ^ 2 / 6 ≤ 1 / 100000000000000000000 := (by dsimp [u]; norm_num)
    have hmul : (Real.arcsin x) ^ 3 / 6 ≤ (1 / 100000000000000000000) * Real.arcsin x := by
      have h1 : (Real.arcsin x) ^ 3 / 6 = ((Real.arcsin x) ^ 2 / 6) * Real.arcsin x := (by ring)
      rw [h1]; exact mul_le_mul_of_nonneg_right ((div_le_div_of_nonneg_right hsq
        (by norm_num)).trans hu_sq) hα_pos.le
    linarith
  exact ⟨hα_pos, hα_le, hα_lb, hα_ub⟩
theorem stratum_angle_ratio_boundsL {N r rMin rMax shiftW : ℕ} {ratioLo ratioHi : ℤ} (hN96 :
  (79228162514264337593543950336 : ℝ) ≤ (N : ℝ)) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk :
  checkSwLStratumRatio rMin rMax shiftW ratioLo ratioHi = true) :
    let α₀ := Real.arcsin (1 / √((N : ℝ) / (r : ℝ))); let θ := swLThetaShiftReal N r shiftW
    ((ratioLo : ℝ) / (swScale : ℝ)) * (2 * α₀) ≤ θ ∧ θ ≤ ((ratioHi : ℝ) / (swScale : ℝ)) * (2 * α₀)
      := by
  intro α₀ θ; unfold checkSwLStratumRatio at hchk; rw [decide_eq_true_eq] at hchk; rcases hchk with
    ⟨hsw_min, _, hrMax_1024, hsw1, hsw7, hrat_lo0, hrat_hi1, hrat_hi_le, hsq_lo, hsq_hi, hc_lo20,
    hc_hi20⟩; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hr_ge : shiftW + 1 ≤ r := hsw_min.trans hmin; have hr1024 : r ≤ 1024 := hmax.trans hrMax_1024
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r)); have hrMin_pos : (0 :
    ℝ) < (rMin : ℝ) := (by exact_mod_cast (by omega : 0 < rMin)); have hrMax_pos : (0 : ℝ) < (rMax :
    ℝ) := (by exact_mod_cast (by omega : 0 < rMax)); have hN_pos : (0 : ℝ) < (N : ℝ) :=
    (by linarith); set d : ℕ := 2 * shiftW; have hd_r : (d : ℝ) ≤ 14 :=
    (by exact_mod_cast (by omega : d ≤ 14)); have hNd_eq : (N : ℝ) - 2 * (shiftW : ℝ) = (N : ℝ) - (d
    : ℝ) := (by dsimp [d]; push_cast; ring); have hNd_pos : (0 : ℝ) < (N : ℝ) - (d : ℝ) :=
    (by linarith); have hrk_pos : (0 : ℝ) < (r : ℝ) - (shiftW : ℝ) :=
    (by have : (shiftW : ℝ) + 1 ≤ (r : ℝ) := (by exact_mod_cast hr_ge); linarith); set c₁ : ℝ := (N
    : ℝ) / (r : ℝ)
  have hc1_ge : (8796093022208 : ℝ) ^ 2 ≤ c₁ := by
    dsimp [c₁]; rw [le_div_iff₀ hr_pos]; have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
    calc (8796093022208 : ℝ) ^ 2 * (r : ℝ)
      _ ≤ (8796093022208 : ℝ) ^ 2 * 1024 := mul_le_mul_of_nonneg_left hr_le (by norm_num)
      _ = 79228162514264337593543950336 := by norm_num
      _ ≤ (N : ℝ) := hN96
  have hsqrt_c1_ge : (8796093022208 : ℝ) ≤ √c₁ :=
    (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8796093022208)]; exact Real.sqrt_le_sqrt hc1_ge)
  have hx0_pos : 0 < 1 / √c₁ := (by positivity); have hx0_ub : 1 / √c₁ ≤ 1 / 8000000000000 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  rcases arcsin_small_boundsL hx0_pos hx0_ub with ⟨hα_pos, _, hα_lb, hα_ub⟩; set xk : ℝ := √(((r :
    ℝ) - (shiftW : ℝ)) / ((N : ℝ) - (d : ℝ))); have hxk_pos : 0 < xk := Real.sqrt_pos.2 (div_pos
    hrk_pos hNd_pos); have hxk_sq : xk ^ 2 = ((r : ℝ) - (shiftW : ℝ)) / ((N : ℝ) - (d : ℝ)) :=
    Real.sq_sqrt (div_nonneg hrk_pos.le hNd_pos.le)
  have hxk_ub : xk ≤ 1 / 8000000000000 := by
    have hsq : xk ^ 2 ≤ (1 / 8000000000000 : ℝ) ^ 2 := by
      rw [hxk_sq, div_le_iff₀ hNd_pos]; have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
      have hsw_nn : (0 : ℝ) ≤ (shiftW : ℝ) := (by positivity)
      have hN_ge : (65536000000000000000000000014 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hN96
      have h1 : (r : ℝ) - (shiftW : ℝ) ≤ 1024 := (by linarith)
      have h2 : (1024 : ℝ) ≤ (1 / 8000000000000 : ℝ) ^ 2 * ((N : ℝ) - (d : ℝ)) := by
        have hsub : (65536000000000000000000000000 : ℝ) ≤ (N : ℝ) - (d : ℝ) :=
          (by linarith [hN_ge, hd_r])
        have hmul := mul_le_mul_of_nonneg_left hsub
          (by norm_num : (0 : ℝ) ≤ (1 / 8000000000000 : ℝ) ^ 2)
        have hval : (1 / 8000000000000 : ℝ) ^ 2 * 65536000000000000000000000000 = 1024 :=
          (by norm_num); linarith
      exact h1.trans h2
    rw [← Real.sqrt_sq hxk_pos.le, ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 8000000000000)]
    exact Real.sqrt_le_sqrt hsq
  rcases arcsin_small_boundsL hxk_pos hxk_ub with ⟨_, _, hβ_lb, hβ_ub⟩; set β : ℝ := Real.arcsin xk
  have hx0_sq : (1 / √c₁) ^ 2 = (r : ℝ) / (N : ℝ) :=
    (by dsimp [c₁]; rw [one_div_pow, Real.sq_sqrt (div_nonneg hN_pos.le hr_pos.le), one_div_div])
  have hlo_sq_real : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) ^ 2 * (1 / √c₁) ^ 2 ≤ xk ^ 2 := by
    rw [hx0_sq, hxk_sq]
    have h1 : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) ^ 2 ≤ ((rMin : ℝ) - (shiftW : ℝ)) / (rMin :
      ℝ) := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hS) hrMin_pos]; have hcast : (((ratioLo + 1) *
        (ratioLo + 1) * (rMin : ℤ) : ℤ) : ℝ) ≤ ((swScale * swScale * ((rMin : ℤ) - (shiftW : ℤ)) :
        ℤ) : ℝ) := (by exact_mod_cast hsq_lo); have hl_eq : (((ratioLo + 1 : ℤ) : ℝ) ^ 2) * (rMin :
        ℝ) = (((ratioLo + 1) * (ratioLo + 1) * (rMin : ℤ) : ℤ) : ℝ) := (by push_cast; ring)
      have hr_eq : ((rMin : ℝ) - (shiftW : ℝ)) * (swScale : ℝ) ^ 2 = ((swScale * swScale * ((rMin :
        ℤ) - (shiftW : ℤ)) : ℤ) : ℝ) := (by push_cast; ring); rw [hl_eq, hr_eq]; exact hcast
    have h2 : ((rMin : ℝ) - (shiftW : ℝ)) / (rMin : ℝ) ≤ ((r : ℝ) - (shiftW : ℝ)) / (r : ℝ) := by
      rw [div_le_div_iff₀ hrMin_pos hr_pos]; have hr_min_r : (rMin : ℝ) ≤ (r : ℝ) :=
        (by exact_mod_cast hmin); have hsw_nn : (0 : ℝ) ≤ (shiftW : ℝ) := (by positivity); nlinarith
    have h3 : (((r : ℝ) - (shiftW : ℝ)) / (r : ℝ)) * ((r : ℝ) / (N : ℝ)) = ((r : ℝ) - (shiftW : ℝ))
      / (N : ℝ) := (by field_simp [hr_pos.ne', hN_pos.ne'])
    have h4 : ((r : ℝ) - (shiftW : ℝ)) / (N : ℝ) ≤ ((r : ℝ) - (shiftW : ℝ)) / ((N : ℝ) - (d : ℝ))
      := by
      rw [div_le_div_iff₀ hN_pos hNd_pos]; have hd_nn : (0 : ℝ) ≤ (d : ℝ) := (by positivity)
      nlinarith
    exact (mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)).trans (h3.trans_le h4)
  have hxk_ge : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 / √c₁) ≤ xk := by
    have hnn : 0 ≤ (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 / √c₁) := mul_nonneg (div_nonneg
      (by exact_mod_cast (by omega : 0 ≤ ratioLo + 1)) hS.le) hx0_pos.le; rw [← Real.sqrt_sq hnn, ←
      Real.sqrt_sq hxk_pos.le]; exact Real.sqrt_le_sqrt (by rwa [mul_pow])
  have hhi_sq_real : xk ^ 2 ≤ (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) ^ 2 * (1 / √c₁) ^ 2 := by
    rw [hx0_sq, hxk_sq]; set a : ℝ := ((ratioHi - 1 : ℤ) : ℝ); have ha_nn : 0 ≤ a :=
      (by dsimp [a]; exact_mod_cast (by omega : 0 ≤ ratioHi - 1))
    have ha_le_S : a ≤ (swScale : ℝ) :=
      (by dsimp [a]; exact_mod_cast (by omega : ratioHi - 1 ≤ swScale))
    have h1 : ((r : ℝ) - (shiftW : ℝ)) / (r : ℝ) ≤ ((rMax : ℝ) - (shiftW : ℝ)) / (rMax : ℝ) := by
      rw [div_le_div_iff₀ hr_pos hrMax_pos]; have hr_max_r : (r : ℝ) ≤ (rMax : ℝ) :=
        (by exact_mod_cast hmax); have hsw_nn : (0 : ℝ) ≤ (shiftW : ℝ) := (by positivity); nlinarith
    have h2 : ((rMax : ℝ) - (shiftW : ℝ)) / (rMax : ℝ) ≤ (a ^ 2 - (shiftW : ℝ)) / (swScale : ℝ) ^ 2
      := by
      rw [div_le_div_iff₀ hrMax_pos (sq_pos_of_pos hS)]; have hcast : ((swScale * swScale * ((rMax :
        ℤ) - (shiftW : ℤ)) : ℤ) : ℝ) ≤ ((((ratioHi - 1) * (ratioHi - 1) - (shiftW : ℤ)) * (rMax : ℤ)
        : ℤ) : ℝ) := (by exact_mod_cast hsq_hi); have hl_eq : ((rMax : ℝ) - (shiftW : ℝ)) * (swScale
        : ℝ) ^ 2 = ((swScale * swScale * ((rMax : ℤ) - (shiftW : ℤ)) : ℤ) : ℝ) :=
        (by push_cast; ring); have hr_eq : (a ^ 2 - (shiftW : ℝ)) * (rMax : ℝ) = ((((ratioHi - 1) *
        (ratioHi - 1) - (shiftW : ℤ)) * (rMax : ℤ) : ℤ) : ℝ) := (by dsimp [a]; push_cast; ring)
      rw [hl_eq, hr_eq]; exact hcast
    have hsw1_r : (1 : ℝ) ≤ (shiftW : ℝ) := (by exact_mod_cast hsw1)
    have hN_ratio : (N : ℝ) / ((N : ℝ) - (d : ℝ)) ≤ (swScale : ℝ) ^ 2 / ((swScale : ℝ) ^ 2 - 1)
      := by
      have hS2_1 : (0 : ℝ) < (swScale : ℝ) ^ 2 - 1 := (by unfold swScale; norm_num)
      rw [div_le_div_iff₀ hNd_pos hS2_1]
      have hdS : (d : ℝ) * (swScale : ℝ) ^ 2 ≤ (N : ℝ) :=
        calc (d : ℝ) * (swScale : ℝ) ^ 2
          _ ≤ 14 * (swScale : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hd_r (sq_nonneg _)
          _ ≤ 79228162514264337593543950336 := by unfold swScale; norm_num
          _ ≤ (N : ℝ) := hN96
      have hsub : 0 ≤ (swScale : ℝ) ^ 2 * ((N : ℝ) - (d : ℝ)) - (N : ℝ) * ((swScale : ℝ) ^ 2 - 1)
        := by
        have hid : (swScale : ℝ) ^ 2 * ((N : ℝ) - (d : ℝ)) - (N : ℝ) * ((swScale : ℝ) ^ 2 - 1) = (N
          : ℝ) - (d : ℝ) * (swScale : ℝ) ^ 2 := (by ring); rw [hid]; exact sub_nonneg.2 hdS
      exact sub_nonneg.1 hsub
    have hprod_le : ((a ^ 2 - (shiftW : ℝ)) / (swScale : ℝ) ^ 2) * ((swScale : ℝ) ^ 2 / ((swScale :
      ℝ) ^ 2 - 1)) ≤ (a / (swScale : ℝ)) ^ 2 := by
      have hS2_1 : (0 : ℝ) < (swScale : ℝ) ^ 2 - 1 := (by unfold swScale; norm_num); have hS2 : (0 :
        ℝ) < (swScale : ℝ) ^ 2 := sq_pos_of_pos hS; have ha2_le : a ^ 2 ≤ (swScale : ℝ) ^ 2 :=
        pow_le_pow_left₀ ha_nn ha_le_S 2; have hsw_mul : (swScale : ℝ) ^ 2 ≤ (shiftW : ℝ) * (swScale
        : ℝ) ^ 2 := (by simpa using mul_le_mul_of_nonneg_right hsw1_r hS2.le)
      rw [div_mul_div_cancel₀ hS2.ne', div_pow, div_le_div_iff₀ hS2_1 hS2]
      have hring1 : (a ^ 2 - (shiftW : ℝ)) * (swScale : ℝ) ^ 2 = a ^ 2 * (swScale : ℝ) ^ 2 - (shiftW
        : ℝ) * (swScale : ℝ) ^ 2 := (by ring)
      have hring2 : a ^ 2 * ((swScale : ℝ) ^ 2 - 1) = a ^ 2 * (swScale : ℝ) ^ 2 - a ^ 2 := (by ring)
      linarith
    have hrew : ((r : ℝ) - (shiftW : ℝ)) / ((N : ℝ) - (d : ℝ)) = (((r : ℝ) - (shiftW : ℝ)) / (r :
      ℝ)) * ((N : ℝ) / ((N : ℝ) - (d : ℝ))) * ((r : ℝ) / (N : ℝ)) :=
      (by field_simp [hr_pos.ne', hN_pos.ne', hNd_pos.ne']); rw [hrew]
    have hm1 : (((r : ℝ) - (shiftW : ℝ)) / (r : ℝ)) * ((N : ℝ) / ((N : ℝ) - (d : ℝ))) ≤ ((a ^ 2 -
      (shiftW : ℝ)) / (swScale : ℝ) ^ 2) * ((swScale : ℝ) ^ 2 / ((swScale : ℝ) ^ 2 - 1)) :=
      mul_le_mul (h1.trans h2) hN_ratio (by positivity) (le_trans (by positivity) (h1.trans h2))
    exact mul_le_mul_of_nonneg_right (hm1.trans hprod_le) (by positivity)
  have hxk_le : xk ≤ (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 / √c₁) := by
    have hnn : 0 ≤ (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 / √c₁) := mul_nonneg (div_nonneg
      (by exact_mod_cast (by omega : 0 ≤ ratioHi - 1)) hS.le) hx0_pos.le; rw [← Real.sqrt_sq
      hxk_pos.le, ← Real.sqrt_sq hnn]; exact Real.sqrt_le_sqrt (by rwa [mul_pow])
  set s20 : ℝ := 100000000000000000000; have hs20_pos : 0 < s20 := (by dsimp [s20]; norm_num)
  have hβ_ge_α : ((ratioLo : ℝ) / (swScale : ℝ)) * α₀ ≤ β := by
    have hcast0 : ((ratioLo * 100000000000000000000 : ℤ) : ℝ) ≤ (((ratioLo + 1) *
      (100000000000000000000 - 1) : ℤ) : ℝ) := Int.cast_le.2 hc_lo20; have hl_eq : ((ratioLo *
      100000000000000000000 : ℤ) : ℝ) = (ratioLo : ℝ) * s20 := (by dsimp [s20]; push_cast; ring)
    have hr_eq : (((ratioLo + 1) * (100000000000000000000 - 1) : ℤ) : ℝ) = ((ratioLo + 1 : ℤ) : ℝ) *
      (s20 - 1) := (by dsimp [s20]; push_cast; ring); rw [hl_eq, hr_eq] at hcast0
    have h1 : (ratioLo : ℝ) / (swScale : ℝ) ≤ (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 - 1 /
      s20) := by
      rw [div_mul_eq_mul_div]; have hdiv := div_le_div_of_nonneg_right hcast0 hs20_pos.le
      have hrew : ((ratioLo + 1 : ℤ) : ℝ) * (s20 - 1) / s20 = ((ratioLo + 1 : ℤ) : ℝ) * (1 - 1 /
        s20) := (by field_simp [hs20_pos.ne']); have hrew0 : (ratioLo : ℝ) * s20 / s20 = (ratioLo :
        ℝ) := mul_div_cancel_right₀ _ hs20_pos.ne'
      rw [hrew0, hrew] at hdiv; exact div_le_div_of_nonneg_right hdiv hS.le
    have h2 : ((ratioLo : ℝ) / (swScale : ℝ)) * α₀ ≤ (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * ((1
      - 1 / s20) * α₀) := (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hα_pos.le)
    have h3 : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * ((1 - 1 / s20) * α₀) ≤ (((ratioLo + 1 : ℤ)
      : ℝ) / (swScale : ℝ)) * (1 / √c₁) := mul_le_mul_of_nonneg_left hα_ub (div_nonneg
      (by exact_mod_cast (by omega : 0 ≤ ratioLo + 1)) hS.le); exact ((h2.trans h3).trans
      hxk_ge).trans hβ_lb
  have hβ_le_α : β ≤ ((ratioHi : ℝ) / (swScale : ℝ)) * α₀ := by
    have hcast0 : (((ratioHi - 1) * 100000000000000000000 : ℤ) : ℝ) ≤ ((ratioHi *
      (100000000000000000000 - 1) : ℤ) : ℝ) := Int.cast_le.2 hc_hi20; have hl_eq : (((ratioHi - 1) *
      100000000000000000000 : ℤ) : ℝ) = ((ratioHi - 1 : ℤ) : ℝ) * s20 :=
      (by dsimp [s20]; push_cast; ring); have hr_eq : ((ratioHi * (100000000000000000000 - 1) : ℤ) :
      ℝ) = (ratioHi : ℝ) * (s20 - 1) := (by dsimp [s20]; push_cast; ring)
    rw [hl_eq, hr_eq] at hcast0
    have h1 : ((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ) ≤ ((ratioHi : ℝ) / (swScale : ℝ)) * (1 - 1 /
      s20) := by
      rw [div_mul_eq_mul_div]; have hdiv := div_le_div_of_nonneg_right hcast0 hs20_pos.le
      have hrew : (ratioHi : ℝ) * (s20 - 1) / s20 = (ratioHi : ℝ) * (1 - 1 / s20) :=
        (by field_simp [hs20_pos.ne']); have hrew0 : ((ratioHi - 1 : ℤ) : ℝ) * s20 / s20 = ((ratioHi
        - 1 : ℤ) : ℝ) := mul_div_cancel_right₀ _ hs20_pos.ne'
      rw [hrew0, hrew] at hdiv; exact div_le_div_of_nonneg_right hdiv hS.le
    have h2 : xk ≤ (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) * α₀ := hxk_le.trans
      (mul_le_mul_of_nonneg_left hα_lb (div_nonneg (by exact_mod_cast (by omega : 0 ≤ ratioHi - 1))
      hS.le))
    have h3 : (((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ)) * α₀ ≤ (1 - 1 / s20) * (((ratioHi : ℝ) /
      (swScale : ℝ)) * α₀) := by
      have hm := mul_le_mul_of_nonneg_right h1 hα_pos.le; have hcomm : (((ratioHi : ℝ) / (swScale :
        ℝ)) * (1 - 1 / s20)) * α₀ = (1 - 1 / s20) * (((ratioHi : ℝ) / (swScale : ℝ)) * α₀) :=
        (by ring); exact hm.trans_eq hcomm
    have h4 : (1 - 1 / s20) * β ≤ (1 - 1 / s20) * (((ratioHi : ℝ) / (swScale : ℝ)) * α₀) :=
      (hβ_ub.trans h2).trans h3; have h1s20 : (0 : ℝ) < 1 - 1 / s20 := (by dsimp [s20]; norm_num)
    exact le_of_mul_le_mul_left h4 h1s20
  have hθ_eq : θ = 2 * β := (by dsimp [θ, swLThetaShiftReal, β, xk]; rw [hNd_eq]); rw [hθ_eq]
  exact ⟨by linarith, by linarith⟩
theorem checkSwLBucketAngles_sound {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk :
  checkSwLBucketAngles L rMin rMax tauNum tauDen ratios trigIvs = true) : 2 ≤ L ∧ L ≤ 8 ∧ L ≤ r ∧ r
  ≤ 1024 ∧ trigIvs.length = L ∧
    let K_blk := swLKBlk n r tauNum tauDen; let N : ℕ := 2 ^ n
    ∀ w : Fin L, memIvInt (Real.cos ((K_blk : ℝ) * swLThetaShiftReal N r w.1)) (trigIvs.getD w.1
      ((0, 0), (0, 0))).1 ∧ memIvInt (Real.sin ((K_blk : ℝ) * swLThetaShiftReal N r w.1))
      (trigIvs.getD w.1 ((0, 0), (0, 0))).2 := by
  unfold checkSwLBucketAngles at hchk; simp only [withForcedInt_eq, Bool.and_eq_true,
    decide_eq_true_eq] at hchk; rcases hchk with ⟨⟨hL2, hL8, hLrMin, _, hrMax1024, htau_pos,
    hden_pos, hlen_rat, hlen_trig⟩, hm⟩; have hLr : L ≤ r := hLrMin.trans hmin; have hr1024 : r ≤
    1024 := hmax.trans hrMax1024; rcases trigIvs with _ | ⟨⟨c0, s0⟩, restTrig⟩
  · simp at hm
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hm; rcases hm with ⟨htrig0,
    hrest⟩; refine ⟨hL2, hL8, hLr, hr1024, hlen_trig, ?_⟩; intro K_blk N w; have hS : (0 : ℝ) <
    (swScale : ℝ) := (by unfold swScale; norm_num); have hr_pos : (0 : ℝ) < (r : ℝ) :=
    (by exact_mod_cast (by omega : 0 < r))
  have hN96 : (79228162514264337593543950336 : ℝ) ≤ (N : ℝ) := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ (N : ℝ) := (by exact_mod_cast hpow); have hval : ((2 ^ 96 : ℕ) : ℝ) =
      79228162514264337593543950336 := (by norm_num); linarith
  set c₁ : ℝ := (N : ℝ) / (r : ℝ)
  have hc1_ge : (8796093022208 : ℝ) ^ 2 ≤ c₁ := by
    dsimp [c₁]; rw [le_div_iff₀ hr_pos]; have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
    calc (8796093022208 : ℝ) ^ 2 * (r : ℝ)
      _ ≤ (8796093022208 : ℝ) ^ 2 * 1024 := mul_le_mul_of_nonneg_left hr_le (by norm_num)
      _ = 79228162514264337593543950336 := by norm_num
      _ ≤ (N : ℝ) := hN96
  have hsqrt_c1_ge : (8796093022208 : ℝ) ≤ √c₁ :=
    (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8796093022208)]; exact Real.sqrt_le_sqrt hc1_ge)
  set α₀ : ℝ := Real.arcsin (1 / √c₁)
  rcases arcsin_small_boundsL (by positivity) (one_div_le_one_div_of_le (by norm_num)
    (by linarith : (8000000000000 : ℝ) ≤ √c₁)) with ⟨hα_pos, hα_le, _, _⟩; set tauR : ℝ := (tauNum :
    ℝ) / (tauDen : ℝ); have htau_nn : 0 ≤ tauR := (by positivity); set K₀ : ℕ := (round (tauR / (2 *
    α₀))).toNat; have hK_eq : K_blk = K₀ + 1 :=
    (by simp only [K_blk, swLKBlk, K₀, tauR, α₀, c₁, N, Nat.cast_pow, Nat.cast_ofNat])
  rcases odd_round_div_sub_mem_Icc hα_pos htau_nn with ⟨hodd_lo, hodd_hi⟩; have hφ0_lo : tauR ≤ 2 *
    (K_blk : ℝ) * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith); have hφ0_hi : 2 *
    (K_blk : ℝ) * α₀ ≤ tauR + 3 * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith)
  set s11 : ℤ := 100000000000; set q1HiNum : ℤ := (tauNum : ℤ) * s11 + (tauDen : ℤ)
  set q1HiDen : ℤ := (tauDen : ℤ) * s11
  have hq1_eq : (q1HiNum : ℝ) / (q1HiDen : ℝ) = tauR + 1 / (100000000000 : ℝ) := by
    dsimp [q1HiNum, q1HiDen, s11, tauR]; have hden_ne : (tauDen : ℝ) ≠ 0 := (by positivity)
    push_cast; field_simp [hden_ne]
  have hφ0_hi_q1 : 2 * (K_blk : ℝ) * α₀ ≤ (q1HiNum : ℝ) / (q1HiDen : ℝ) :=
    (by rw [hq1_eq]; linarith [hφ0_hi, hα_le]); rcases w with ⟨_ | idx, hw_lt⟩
  · -- Head plane `w = 0`: `swLThetaShiftReal N r 0 = 2 * α₀`.
    have hN_pos : (0 : ℝ) < (N : ℝ) := (by linarith)
    have hθ0_eq : swLThetaShiftReal N r 0 = 2 * α₀ := by
      unfold swLThetaShiftReal; simp only [Nat.cast_zero, mul_zero, sub_zero, α₀, c₁]
      congr 2; rw [Real.sqrt_div hr_pos.le, Real.sqrt_div hN_pos.le, one_div_div]
    have hφ_eq : (K_blk : ℝ) * swLThetaShiftReal N r 0 = 2 * (K_blk : ℝ) * α₀ :=
      (by rw [hθ0_eq]; ring); rw [hφ_eq]
    simpa using checkSwLTrigRat_sound (by simpa [tauR] using hφ0_lo) hφ0_hi_q1 htrig0
  · -- Shifted plane `w = idx + 1` (`idx < L - 1`):
    have hidx : idx < L - 1 := (by omega); rcases hrest idx hidx with ⟨hrat_w, htrig_w⟩
    rcases stratum_angle_ratio_boundsL hN96 hmin hmax hrat_w with ⟨hr_lo, hr_hi⟩; set rat :=
      ratios.getD idx (0, 0)
    have hrat_lo_nn : 0 ≤ (rat.1 : ℝ) / (swScale : ℝ) := by
      unfold checkSwLStratumRatio at hrat_w; rw [decide_eq_true_eq] at hrat_w
      exact div_nonneg (by exact_mod_cast hrat_w.2.2.2.2.2.1.le) hS.le
    have hrat_hi_nn : 0 ≤ (rat.2 : ℝ) / (swScale : ℝ) := by
      unfold checkSwLStratumRatio at hrat_w; rw [decide_eq_true_eq] at hrat_w
      exact div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ rat.2)) hS.le
    have hφ_lo : (((tauNum : ℤ) * rat.1 : ℤ) : ℝ) / (((tauDen : ℤ) * swScale : ℤ) : ℝ) ≤ (K_blk : ℝ)
      * swLThetaShiftReal N r (idx + 1) := by
      have hm1 := mul_le_mul_of_nonneg_left hr_lo (Nat.cast_nonneg K_blk); have hm2 :=
        mul_le_mul_of_nonneg_left hφ0_lo hrat_lo_nn; have hrew1 : (K_blk : ℝ) * (((rat.1 : ℝ) /
        (swScale : ℝ)) * (2 * α₀)) = ((rat.1 : ℝ) / (swScale : ℝ)) * (2 * (K_blk : ℝ) * α₀) :=
        (by ring); have hrew2 : (((tauNum : ℤ) * rat.1 : ℤ) : ℝ) / (((tauDen : ℤ) * swScale : ℤ) :
        ℝ) = ((rat.1 : ℝ) / (swScale : ℝ)) * tauR :=
        (by dsimp [tauR]; push_cast; rw [div_mul_div_comm]; congr 1 <;> ring); linarith
    have hφ_hi : (K_blk : ℝ) * swLThetaShiftReal N r (idx + 1) ≤ ((q1HiNum * rat.2 : ℤ) : ℝ) /
      ((q1HiDen * swScale : ℤ) : ℝ) := by
      have hm1 := mul_le_mul_of_nonneg_left hr_hi (Nat.cast_nonneg K_blk); have hm2 :=
        mul_le_mul_of_nonneg_left hφ0_hi_q1 hrat_hi_nn; have hrew1 : (K_blk : ℝ) * (((rat.2 : ℝ) /
        (swScale : ℝ)) * (2 * α₀)) = ((rat.2 : ℝ) / (swScale : ℝ)) * (2 * (K_blk : ℝ) * α₀) :=
        (by ring)
      have hrew2 : ((q1HiNum * rat.2 : ℤ) : ℝ) / ((q1HiDen * swScale : ℤ) : ℝ) = ((rat.2 : ℝ) /
        (swScale : ℝ)) * ((q1HiNum : ℝ) / (q1HiDen : ℝ)) := by
        rw [Int.cast_mul, Int.cast_mul, div_mul_div_comm, mul_comm (q1HiNum : ℝ), mul_comm (q1HiDen
          : ℝ)]
      linarith
    simpa using checkSwLTrigRat_sound hφ_lo hφ_hi htrig_w
/-! ## 5. `2L`-State `IvInt` Trajectory & Bucket Certificate Checker (`swScale = 10^9`) -/
/-- WHNF-forcing wrapper for a pair of `IvInt` intervals. -/
def withForcedPair {α : Type*} (p : IvInt × IvInt) (k : IvInt × IvInt → α) : α :=
  withForcedIv p.1 fun a ↦ withForcedIv p.2 fun b ↦ k (a, b)
theorem withForcedPair_eq {α : Type*} (p : IvInt × IvInt) (k : IvInt × IvInt → α) : withForcedPair p
  k = k p := by unfold withForcedPair; rw [withForcedIv_eq, withForcedIv_eq]
/-- WHNF-forcing wrapper for a list of `(cosIv, sinIv)` interval pairs. -/
def withForcedPairList {α : Type*} :
    List (IvInt × IvInt) → (List (IvInt × IvInt) → α) → α
  | [], k => k []
  | x :: xs, k => withForcedPair x fun x' ↦ withForcedPairList xs fun xs' ↦ k (x' :: xs')
theorem withForcedPairList_eq {α : Type*} (xs : List (IvInt × IvInt)) (k : List (IvInt × IvInt) → α)
  : withForcedPairList xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => unfold withForcedPairList; rw [withForcedPair_eq, ih]
theorem sum_Icc_bot {M : Type*} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (f : ℕ → M) : ∑ k ∈
  Finset.Icc a b, f k = f a + ∑ k ∈ Finset.Icc (a + 1) b, f k := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc h, Finset.sum_insert]; simp
theorem sum_Icc_top {M : Type*} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b + 1) (f : ℕ → M) : ∑ k ∈
  Finset.Icc a (b + 1), f k = (∑ k ∈ Finset.Icc a b, f k) + f (b + 1) := by
  rw [← Finset.insert_Icc_right_eq_Icc_add_one h, Finset.sum_insert, add_comm]; simp
theorem getD_map_finRange {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (j : Fin n) : ((List.finRange
  n).map f).getD j.1 d = f j := by
  have hlen : j.1 < ((List.finRange n).map f).length := (by simp [j.2])
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, List.getElem_map,
    List.getElem_finRange]; simp
/-- Interval Grover plane rotation on `(2w, 2w + 1)` (`w < L`). -/
def swLGroverRotIv (L : ℕ) (trigIvs : List (IvInt × IvInt)) (stIv : List IvInt) : List IvInt :=
  (List.finRange (2 * L)).map fun j ↦
    let w := j.1 / 2
    match trigIvs.getD w ((0, 0), (0, 0)),
        stIv.getD (2 * w) (0, 0), stIv.getD (2 * w + 1) (0, 0) with
    | (cw, sw), ae, ao =>
        if j.1 % 2 = 0 then ivSubInt (ivMulInt cw ae) (ivMulInt sw ao)
        else ivAddInt (ivMulInt sw ae) (ivMulInt cw ao)
/-- Interval Pieri `SO(2)` rotations on `(2w - 1, 2w)` + weak survival on `2L - 1`. -/
def swLPieriAndWeakIv (L : ℕ) (p : SwLPulseRat L) (cv : IvInt) (naIv : List IvInt) : List IvInt :=
  withForcedPairList ((List.finRange (L - 1)).map fun w0 ↦ ivPythag (p.uNum w0) (p.uvDen : ℤ))
    fun uPythags ↦
      (List.finRange (2 * L)).map fun j ↦
        if j.1 = 0 then
          naIv.getD 0 (0, 0)
        else if j.1 < 2 * L - 1 then
          let idx := (j.1 - 1) / 2
          match uPythags.getD idx ((0, 0), (0, 0)),
              naIv.getD (2 * idx + 1) (0, 0), naIv.getD (2 * idx + 2) (0, 0) with
          | (cu, su), lv, rv =>
              if (j.1 - 1) % 2 = 0 then ivSubInt (ivMulInt cu lv) (ivMulInt su rv)
              else ivAddInt (ivMulInt su lv) (ivMulInt cu rv)
        else
          ivMulInt cv (naIv.getD (2 * L - 1) (0, 0))
/-- One interval conveyor pulse matching `SwLIntChecker._run_trajectory` bit-for-bit. -/
noncomputable def swLPulseStepIv (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (stIv : List IvInt) (cumIv survIv : IvInt) (p : SwLPulseRat L) :
    List IvInt × IvInt × IvInt :=
  withForcedList (swLGroverRotIv L trigIvs stIv) fun naIv ↦
    withForcedPair
      (if p.vNum = 0 then ((swScale, swScale), (0, 0)) else ivPythag p.vNum (p.uvDen : ℤ))
      fun cvsv ↦
        match cvsv, naIv.getD (2 * L - 1) (0, 0) with
        | (cv, sv), topIv =>
            withForcedState
              (swLPieriAndWeakIv L p cv naIv,
               ivAddInt cumIv (ivSqInt (ivMulInt sv topIv)),
               ivAddInt survIv (ivSubInt (swScale, swScale) cumIv))
              id
/-- Multi-pulse `IvInt` trajectory from `(stIv, cumIv, survIv)`. -/
noncomputable def swLEvolutionIvAux (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (stIv : List IvInt) (cumIv survIv : IvInt) :
    List (SwLPulseRat L) → List IvInt × IvInt × IvInt
  | [] => (stIv, cumIv, survIv)
  | p :: ps =>
      withForcedState (swLPulseStepIv L trigIvs stIv cumIv survIv p) fun nxt ↦
        swLEvolutionIvAux L trigIvs nxt.1 nxt.2.1 nxt.2.2 ps
/-- Multi-pulse `IvInt` trajectory starting from `(|b_0, 0⟩, cum = 0, surv = 0)`. -/
noncomputable def swLEvolutionIv (L : ℕ) (trigIvs : List (IvInt × IvInt))
    (pulses : List (SwLPulseRat L)) : List IvInt × IvInt × IvInt :=
  swLEvolutionIvAux L trigIvs ((swScale, swScale) :: List.replicate (2 * L - 1) (0, 0)) (0, 0)
  (0, 0) pulses
/-- Tail-recursive linear accumulator enclosing `∑_j M_{o, j} st_j` under
  `IsValidSwLOverlap`. -/
def swLOrbLinAux (o : ℕ) : ℕ → IvInt → List IvInt → IvInt
  | _, acc, [] => acc
  | j, acc, sj :: sjs =>
      let mIv : IvInt :=
        if j = o then (swScale - swOrbPad, swScale) else (-swOrbPad, swOrbPad)
      withForcedIv (ivAddInt acc (ivMulInt sj mIv)) fun acc' ↦
        swLOrbLinAux o (j + 1) acc' sjs
/-- Squared orbit projection interval `(M *ᵥ st)_o^2` matching `SwLIntChecker.orb_sq_iv`. -/
def swLOrbSqIv (stIv : List IvInt) (o : ℕ) : IvInt :=
  ivSqInt (swLOrbLinAux o 0 (0, 0) stIv)
/-- Descending suffix tail intervals `[tailIv_2,..., tailIv_L]` from `c = k` (`2 ≤ k ≤ L`). -/
def swLTailSuffixIvs (L : ℕ) (stIv : List IvInt) (cumIv : IvInt) : ℕ → List IvInt
  | 0 => []
  | m + 1 =>
      let c := L - m
      if c = L then
        [ivAddInt (swLOrbSqIv stIv (2 * L - 1))
          (ivMulInt cumIv (ivSqInt (swScale - swOrbPad, swScale)))]
      else
        match swLTailSuffixIvs L stIv cumIv m with
        | [] => []
        | nextIv :: rest =>
            let phIv := ivAddInt
              (ivAddInt (swLOrbSqIv stIv (2 * c - 1)) (swLOrbSqIv stIv (2 * c)))
              (ivMulInt cumIv (0, 2 * swOrbPad))
            withForcedIv (ivAddInt phIv nextIv) fun curIv ↦ curIv :: nextIv :: rest
/-- Clamped monotone lower bounds `[lb_1,..., lb_L]` matching
  `SwLIntChecker.eval_bucket_cert`. -/
def swLClampTailLbs : List IvInt → List ℤ
  | [] => []
  | [ivL] => [max 0 ivL.1]
  | iv :: rest =>
      match swLClampTailLbs rest with
      | [] => [max 0 iv.1]
      | nextLb :: lbs =>
          withForcedInt (max nextLb (min swScale iv.1)) fun curLb ↦ curLb :: nextLb :: lbs
/-- Pure-integer bucket certificate checker (`swScale = 10^9`) for `2 ≤ L ≤ 8`. -/
noncomputable def checkSwLBucketCert (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt))
    (pulses : List (SwLPulseRat L))
    (tailLbs : List ℤ) (survUb : ℤ) : Bool :=
  decide (1 ≤ pulses.length ∧ pulses.length ≤ 250 ∧ tailLbs.length = L ∧ 0 ≤ survUb ∧
    0 < tailLbs.getD 0 0 ∧ tailLbs.getD 0 0 ≤ swScale ∧ 0 ≤ tailLbs.getD (L - 1) 0) &&
  pulses.all swLPulseValid &&
  (List.range (L - 1)).all (fun i ↦ decide (tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0)) &&
  checkSwLBucketAngles L rMin rMax tauNum tauDen ratios trigIvs &&
  withForcedState (swLEvolutionIv L trigIvs pulses) fun outIv ↦
    let p0Iv := ivAddInt (swLOrbSqIv outIv.1 0) (ivMulInt outIv.2.1 (0, swOrbPad))
    let t1Iv := ivSubInt (swScale, swScale) p0Iv
    let tailIvs := t1Iv :: swLTailSuffixIvs L outIv.1 outIv.2.1 (L - 1)
    let certLbs := swLClampTailLbs tailIvs
    decide (outIv.2.2.2 ≤ survUb ∧ certLbs.length = L) &&
    (List.range L).all fun i ↦ decide (tailLbs.getD i 0 ≤ certLbs.getD i 0)
theorem memIvIntVec_groverRot {L : ℕ} {cs : Fin L → ℝ × ℝ} {trigIvs : List (IvInt × IvInt)} {st :
  Fin (2 * L) → ℝ} {stIv : List IvInt} (htrig : ∀ w : Fin L, memIvInt (cs w).1 (trigIvs.getD w.1
  ((0, 0), (0, 0))).1 ∧ memIvInt (cs w).2 (trigIvs.getD w.1 ((0, 0), (0, 0))).2) (hst : memIvIntVec
  st stIv) : memIvIntVec (swLGroverRotVec L cs st) (swLGroverRotIv L trigIvs stIv) := by
  refine ⟨by simp [swLGroverRotIv], fun j ↦ ?_⟩
  unfold swLGroverRotIv swLGroverRotVec; rw [getD_map_finRange]; dsimp only; set w : Fin L := ⟨j.1 /
    2, by omega⟩; rcases htrig w with ⟨hcw, hsw⟩; have hae := hst.2 ⟨2 * w.1, by omega⟩; have hao :=
    hst.2 ⟨2 * w.1 + 1, by omega⟩; rcases hpair : trigIvs.getD w.1 ((0, 0), (0, 0)) with ⟨cwIv,
    swIv⟩; rw [hpair] at hcw hsw; change memIvInt _ (if j.1 % 2 = 0 then ivSubInt (ivMulInt cwIv _)
    (ivMulInt swIv _) else ivAddInt (ivMulInt swIv _) (ivMulInt cwIv _))
  split_ifs
  · exact memIvInt_ivSubInt (memIvInt_ivMulInt hcw hae) (memIvInt_ivMulInt hsw hao)
  · exact memIvInt_ivAddInt (memIvInt_ivMulInt hsw hae) (memIvInt_ivMulInt hcw hao)
theorem memIvIntVec_pieriAndWeak {L : ℕ} (hL : 2 ≤ L) {p : SwLPulseRat L} (hp : 0 < p.uvDen) {cv :
  IvInt} (hcv : memIvInt (swLCayleyCos p.vNum p.uvDen) cv) {na : Fin (2 * L) → ℝ} {naIv : List
  IvInt} (hna : memIvIntVec na naIv) : memIvIntVec (swLPieriAndWeakVec L hL p na) (swLPieriAndWeakIv
  L p cv naIv) := by
  unfold swLPieriAndWeakIv; rw [withForcedPairList_eq]; refine ⟨by simp, fun j ↦ ?_⟩
  rw [getD_map_finRange]; unfold swLPieriAndWeakVec; dsimp only; by_cases hj0 : j.1 = 0
  · simp only [hj0, ↓reduceDIte, ↓reduceIte]; exact hna.2 ⟨0, by omega⟩
  · simp only [hj0, ↓reduceDIte, ↓reduceIte]; by_cases hjl : j.1 < 2 * L - 1
    · simp only [hjl, ↓reduceDIte, ↓reduceIte]; set w0 : Fin (L - 1) := ⟨(j.1 - 1) / 2, by omega⟩
      have hget : ((List.finRange (L - 1)).map fun w0 ↦ ivPythag (p.uNum w0) (p.uvDen : ℤ)).getD
        w0.1 ((0, 0), (0, 0)) = ivPythag (p.uNum w0) (p.uvDen : ℤ) := getD_map_finRange _ _ w0
      change memIvInt _
        (match ((List.finRange (L - 1)).map fun w0 ↦ ivPythag (p.uNum w0) (p.uvDen : ℤ)).getD
            w0.1 ((0, 0), (0, 0)),
          naIv.getD (2 * w0.1 + 1) (0, 0), naIv.getD (2 * w0.1 + 2) (0, 0) with
        | (cu, su), lv, rv =>
            if (j.1 - 1) % 2 = 0 then ivSubInt (ivMulInt cu lv) (ivMulInt su rv)
            else ivAddInt (ivMulInt su lv) (ivMulInt cu rv))
      rw [hget]; rcases memIvInt_ivPythag (p.uNum w0) hp with ⟨hcu, hsu⟩; have hlv := hna.2 ⟨2 *
        w0.1 + 1, by omega⟩; have hrv := hna.2 ⟨2 * w0.1 + 2, by omega⟩
      rcases hpy : ivPythag (p.uNum w0) (p.uvDen : ℤ) with ⟨cu, su⟩; rw [hpy] at hcu hsu; dsimp only
      split_ifs
      · exact memIvInt_ivSubInt (memIvInt_ivMulInt hcu hlv) (memIvInt_ivMulInt hsu hrv)
      · exact memIvInt_ivAddInt (memIvInt_ivMulInt hsu hlv) (memIvInt_ivMulInt hcu hrv)
    · simp only [hjl, ↓reduceDIte, ↓reduceIte]; exact memIvInt_ivMulInt hcv (hna.2 ⟨2 * L - 1,
        by omega⟩)
theorem memIvInt_pulseStep {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} {trigIvs : List (IvInt ×
  IvInt)} (htrig : ∀ w : Fin L, memIvInt (cs w).1 (trigIvs.getD w.1 ((0, 0), (0, 0))).1 ∧ memIvInt
  (cs w).2 (trigIvs.getD w.1 ((0, 0), (0, 0))).2) {st : Fin (2 * L) → ℝ} {stIv : List IvInt} {cum
  surv : ℝ} {cumIv survIv : IvInt} {p : SwLPulseRat L} (hp : swLPulseValid p = true) (hst :
  memIvIntVec st stIv) (hcum : memIvInt cum cumIv) (hsurv : memIvInt surv survIv) :
    let outR := swLPulseStepReal L hL cs st cum surv p
    let outIv := swLPulseStepIv L trigIvs stIv cumIv survIv p
    memIvIntVec outR.1 outIv.1 ∧ memIvInt outR.2.1 outIv.2.1 ∧ memIvInt outR.2.2 outIv.2.2 := by
  intro outR outIv; unfold swLPulseValid at hp; rw [decide_eq_true_eq] at hp
  simp only [outR, outIv, swLPulseStepReal, swLPulseStepIv, withForcedList_eq, withForcedPair_eq,
    withForcedState_eq, id_eq]; have hna := memIvIntVec_groverRot htrig hst
  have hcvsv : memIvInt (swLCayleyCos p.vNum p.uvDen) (if p.vNum = 0 then ((swScale, swScale), (0,
    0)) else ivPythag p.vNum (p.uvDen : ℤ)).1 ∧ memIvInt (swLCayleySin p.vNum p.uvDen) (if p.vNum =
    0 then ((swScale, swScale), (0, 0)) else ivPythag p.vNum (p.uvDen : ℤ)).2 := by
    by_cases hv0 : p.vNum = 0
    · simp only [hv0, ↓reduceIte]; have hd_ne : (p.uvDen : ℝ) ^ 2 ≠ 0 := (by positivity)
      have hc0 : swLCayleyCos 0 p.uvDen = 1 := (by unfold swLCayleyCos; simp [div_self hd_ne])
      have hs0 : swLCayleySin 0 p.uvDen = 0 := (by unfold swLCayleySin; simp)
      rw [hc0, hs0]; exact ⟨memIvInt_one, memIvInt_zero⟩
    · simp only [hv0, ↓reduceIte]; exact memIvInt_ivPythag p.vNum hp
  rcases hcvsv with ⟨hcv, hsv⟩; refine ⟨memIvIntVec_pieriAndWeak hL hp hcv hna, ?_, ?_⟩
  · exact memIvInt_ivAddInt hcum (memIvInt_ivSqInt (memIvInt_ivMulInt hsv (hna.2 ⟨2 * L - 1,
      by omega⟩)))
  · exact memIvInt_ivAddInt hsurv (memIvInt_ivSubInt memIvInt_one hcum)
theorem memIvInt_evolutionAux {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} {trigIvs : List (IvInt ×
  IvInt)} (htrig : ∀ w : Fin L, memIvInt (cs w).1 (trigIvs.getD w.1 ((0, 0), (0, 0))).1 ∧ memIvInt
  (cs w).2 (trigIvs.getD w.1 ((0, 0), (0, 0))).2) (pulses : List (SwLPulseRat L)) (hp : pulses.all
  swLPulseValid = true) {st : Fin (2 * L) → ℝ} {stIv : List IvInt} {cum surv : ℝ} {cumIv survIv :
  IvInt} (hst : memIvIntVec st stIv) (hcum : memIvInt cum cumIv) (hsurv : memIvInt surv survIv) :
    let outR := swLEvolutionRealAux L hL cs st cum surv pulses
    let outIv := swLEvolutionIvAux L trigIvs stIv cumIv survIv pulses
    memIvIntVec outR.1 outIv.1 ∧ memIvInt outR.2.1 outIv.2.1 ∧ memIvInt outR.2.2 outIv.2.2 := by
  induction pulses generalizing st stIv cum cumIv surv survIv with
  | nil => exact ⟨hst, hcum, hsurv⟩
  | cons p ps ih =>
    rw [List.all_cons, Bool.and_eq_true] at hp; unfold swLEvolutionRealAux swLEvolutionIvAux
    rw [withForcedState_eq]; rcases memIvInt_pulseStep hL htrig hp.1 hst hcum hsurv with ⟨h1, h2,
      h3⟩; exact ih hp.2 h1 h2 h3
theorem memIvInt_evolution {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} {trigIvs : List (IvInt ×
  IvInt)} (htrig : ∀ w : Fin L, memIvInt (cs w).1 (trigIvs.getD w.1 ((0, 0), (0, 0))).1 ∧ memIvInt
  (cs w).2 (trigIvs.getD w.1 ((0, 0), (0, 0))).2) (pulses : List (SwLPulseRat L)) (hp : pulses.all
  swLPulseValid = true) :
    let outR := swLEvolutionReal L hL cs pulses; let outIv := swLEvolutionIv L trigIvs pulses
    memIvIntVec outR.1 outIv.1 ∧ memIvInt outR.2.1 outIv.2.1 ∧ memIvInt outR.2.2 outIv.2.2 := by
  refine memIvInt_evolutionAux hL htrig pulses hp ⟨?_, ?_⟩ memIvInt_zero memIvInt_zero
  · simp; omega
  · intro j; rcases j with ⟨_ | k, hk⟩
    · simpa using memIvInt_one
    · have hk_lt : k < 2 * L - 1 := (by omega); simp [List.getD_eq_getElem?_getD, hk_lt,
        memIvInt_zero]
theorem memIvInt_swLOrbLinAux (o : ℕ) (mReal fReal : ℕ → ℝ) : ∀ (xs : List IvInt) (j0 : ℕ) (accR :
  ℝ) (accIv : IvInt), memIvInt accR accIv → (∀ i < xs.length, memIvInt (fReal (j0 + i)) (xs.getD i
  (0, 0)) ∧ memIvInt (mReal (j0 + i)) (if j0 + i = o then (swScale - swOrbPad, swScale) else
  (-swOrbPad, swOrbPad))) → memIvInt (accR + ∑ i ∈ Finset.range xs.length, mReal (j0 + i) * fReal
  (j0 + i)) (swLOrbLinAux o j0 accIv xs)
  | [], _, accR, accIv, hacc, _ => by unfold swLOrbLinAux; simpa using hacc
  | sj :: sjs, j0, accR, accIv, hacc, hxs => by
    unfold swLOrbLinAux; rw [withForcedIv_eq, List.length_cons, Finset.sum_range_succ']
    rcases hxs 0 (by simp) with ⟨hf0, hm0⟩; simp only [add_zero] at hf0 hm0 ⊢
    have hstep : memIvInt (accR + mReal j0 * fReal j0) (ivAddInt accIv (ivMulInt sj (if j0 = o then
      (swScale - swOrbPad, swScale) else (-swOrbPad, swOrbPad)))) :=
      (by rw [mul_comm (mReal j0)]; exact memIvInt_ivAddInt hacc (memIvInt_ivMulInt hf0 hm0))
    have hih := memIvInt_swLOrbLinAux o mReal fReal sjs (j0 + 1) (accR + mReal j0 * fReal j0) _
      hstep fun i hi ↦ by
        rcases hxs (i + 1) (by simp; omega) with ⟨hfi, hmi⟩; rw [show j0 + (i + 1) = j0 + 1 + i
          by omega] at hfi hmi; exact ⟨hfi, hmi⟩
    refine (?_ : accR + (∑ k ∈ Finset.range sjs.length, mReal (j0 + (k + 1)) * fReal (j0 + (k + 1))
      + mReal j0 * fReal j0) = (accR + mReal j0 * fReal j0) + ∑ i ∈ Finset.range sjs.length, mReal
      (j0 + 1 + i) * fReal (j0 + 1 + i)) ▸ hih
    have hsum_eq : ∑ k ∈ Finset.range sjs.length, mReal (j0 + (k + 1)) * fReal (j0 + (k + 1)) =
      ∑ i ∈ Finset.range sjs.length, mReal (j0 + 1 + i) * fReal (j0 + 1 + i) :=
      Finset.sum_congr rfl fun k _ ↦ by rw [show j0 + (k + 1) = j0 + 1 + k by omega]
    rw [hsum_eq]; ring
theorem memIvInt_swLOrbSqIv {L : ℕ} {M : Fin (2 * L) → Fin (2 * L) → ℝ} (hM : IsValidSwLOverlap M)
  {st : Fin (2 * L) → ℝ} {stIv : List IvInt} (hst : memIvIntVec st stIv) (o : Fin (2 * L)) :
  memIvInt ((swLOrbitProj M st o) ^ 2) (swLOrbSqIv stIv o.1) := by
  unfold swLOrbSqIv; refine memIvInt_ivSqInt ?_
  set fReal : ℕ → ℝ := fun k ↦ if hk : k < 2 * L then st ⟨k, hk⟩ else 0
  set mReal : ℕ → ℝ := fun k ↦ if hk : k < 2 * L then M o ⟨k, hk⟩ else 0
  have hlin := memIvInt_swLOrbLinAux o.1 mReal fReal stIv 0 0 (0, 0) memIvInt_zero fun i hi ↦ by
    have hi_lt : i < 2 * L := hst.1 ▸ hi; have hf_eq : fReal (0 + i) = st ⟨i, hi_lt⟩ :=
      (by simp [fReal, hi_lt]); have hm_eq : mReal (0 + i) = M o ⟨i, hi_lt⟩ :=
      (by simp [mReal, hi_lt]); rw [hf_eq, hm_eq, zero_add]; refine ⟨hst.2 ⟨i, hi_lt⟩, ?_⟩
    by_cases hio : i = o.1
    · have ho_eq : (⟨i, hi_lt⟩ : Fin (2 * L)) = o := (by ext; exact hio)
      rw [ho_eq]; simp only [hio, ↓reduceIte]; rcases hM.2.2.1 o with ⟨hd1, hd2, _⟩
      unfold memIvInt swScale swOrbPad; dsimp only; exact ⟨by linarith, by linarith⟩
    · simp only [hio, ↓reduceIte]; have hne : o ≠ ⟨i, hi_lt⟩ := fun h ↦ hio (congrArg Fin.val
        h).symm; have habs := abs_le.1 (hM.2.2.2 o ⟨i, hi_lt⟩ hne); unfold memIvInt swScale swOrbPad
      dsimp only; exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  have hproj_eq : 0 + ∑ i ∈ Finset.range stIv.length, mReal (0 + i) * fReal (0 + i) = swLOrbitProj M
    st o := by
    rw [zero_add, hst.1]; unfold swLOrbitProj; rw [← Fin.sum_univ_eq_sum_range (fun i ↦ mReal (0 +
      i) * fReal (0 + i)) (2 * L)]
    exact Finset.sum_congr rfl fun j _ ↦ by simp [fReal, mReal, j.2]
  rwa [hproj_eq] at hlin
theorem memIvInt_swLTailSuffixIvs {L : ℕ} (hL : 2 ≤ L)
    {M : Fin (2 * L) → Fin (2 * L) → ℝ} (hM : IsValidSwLOverlap M)
    {st : Fin (2 * L) → ℝ} {stIv : List IvInt} (hst : memIvIntVec st stIv)
    {cum : ℝ} {cumIv : IvInt} (hcum : memIvInt cum cumIv) :
    ∀ m : ℕ, m ≤ L - 1 →
      let sfx := swLTailSuffixIvs L stIv cumIv m
      sfx.length = m ∧
      ∀ idx < m,
        memIvInt (∑ h ∈ Finset.Icc (L + 1 - m + idx) L, swLAttemptProbReal L hL M st cum h)
          (sfx.getD idx (0, 0))
  | 0, _ => ⟨rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | 1, hm => by
      have hsub : L - 0 = L := Nat.sub_zero L; unfold swLTailSuffixIvs; simp only [Nat.sub_zero,
        ↓reduceIte, List.length_singleton, true_and]; intro idx hidx; have hidx0 : idx = 0 :=
        (by omega); subst hidx0; have hcc : L + 1 - 1 + 0 = L := (by omega); rw [hcc,
        Finset.Icc_self, Finset.sum_singleton]; unfold swLAttemptProbReal; have hn0 : L ≠ 0 :=
        (by omega); simp only [hn0, ↓reduceIte, lt_irrefl]
      have hd_mem : memIvInt (M ⟨2 * L - 1, by omega⟩ ⟨2 * L - 1, by omega⟩) (swScale - swOrbPad,
        swScale) := by
        rcases hM.2.2.1 ⟨2 * L - 1, by omega⟩ with ⟨h1, h2, _⟩; unfold memIvInt swScale swOrbPad;
          dsimp only; exact ⟨by linarith, by linarith⟩
      simpa using memIvInt_ivAddInt (memIvInt_swLOrbSqIv hM hst ⟨2 * L - 1, by omega⟩)
        (memIvInt_ivMulInt hcum (memIvInt_ivSqInt hd_mem))
  | m + 2, hm => by
      have hm1 : m + 1 ≤ L - 1 := (by omega); rcases memIvInt_swLTailSuffixIvs hL hM hst hcum (m +
        1) hm1 with ⟨hlen, hih⟩; unfold swLTailSuffixIvs; have hc_ne : L - (m + 1) ≠ L := (by omega)
      simp only [hc_ne, ↓reduceIte]
      rcases hsfx : swLTailSuffixIvs L stIv cumIv (m + 1) with _ | ⟨nextIv, rest⟩
      · rw [hsfx] at hlen; simp at hlen
      rw [hsfx] at hlen hih; dsimp only; rw [withForcedIv_eq]
      refine ⟨by simp at hlen ⊢; omega, fun idx hidx ↦ ?_⟩; rcases idx with _ | idx'
      · -- Head index `0`: `c = L - (m + 1)` (`2 ≤ c < L`)
        set c : ℕ := L - (m + 1); have hc2 : 2 ≤ c := (by dsimp [c]; omega); have hcL : c < L :=
          (by dsimp [c]; omega); have hcc0 : L + 1 - (m + 2) + 0 = c := (by dsimp [c]; omega)
        have hcc1 : L + 1 - (m + 1) = c + 1 := (by dsimp [c]; omega); have hnext : memIvInt (∑ h ∈
          Finset.Icc (c + 1) L, swLAttemptProbReal L hL M st cum h) nextIv :=
          (by have h0 := hih 0 (by omega); simpa [hcc1] using h0)
        have hpc : memIvInt (swLAttemptProbReal L hL M st cum c) (ivAddInt (ivAddInt (swLOrbSqIv
          stIv (2 * c - 1)) (swLOrbSqIv stIv (2 * c))) (ivMulInt cumIv (0, 2 * swOrbPad))) := by
          unfold swLAttemptProbReal; have hcn0 : c ≠ 0 := (by omega); simp only [hcn0, ↓reduceIte,
            hcL, ↓reduceDIte]
          have ho1 : memIvInt ((swLOrbitProj M st ⟨2 * c - 1, by omega⟩) ^ 2) (swLOrbSqIv stIv (2 *
            c - 1)) := memIvInt_swLOrbSqIv hM hst ⟨2 * c - 1, by omega⟩
          have ho2 : memIvInt ((swLOrbitProj M st ⟨2 * c, by omega⟩) ^ 2) (swLOrbSqIv stIv (2 * c))
            := memIvInt_swLOrbSqIv hM hst ⟨2 * c, by omega⟩
          have hoff1 : |M ⟨2 * c - 1, by omega⟩ ⟨2 * L - 1, by omega⟩| ≤ (1 : ℝ) / 10 ^ 9 :=
            hM.2.2.2 _ _ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
          have hoff2 : |M ⟨2 * c, by omega⟩ ⟨2 * L - 1, by omega⟩| ≤ (1 : ℝ) / 10 ^ 9 :=
            hM.2.2.2 _ _ (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
          have hsq1 : (M ⟨2 * c - 1, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 ≤ (1 : ℝ) / 10 ^ 18 := by
            rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hoff1 2).trans_eq (by norm_num)
          have hsq2 : (M ⟨2 * c, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 ≤ (1 : ℝ) / 10 ^ 18 := by
            rw [← sq_abs]; exact (pow_le_pow_left₀ (abs_nonneg _) hoff2 2).trans_eq (by norm_num)
          have hpad : memIvInt ((M ⟨2 * c - 1, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 + (M ⟨2 * c,
            by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2) (0, 2 * swOrbPad) := by
            unfold memIvInt swScale swOrbPad; dsimp only
            exact ⟨by linarith [sq_nonneg (M ⟨2 * c - 1, by omega⟩ ⟨2 * L - 1, by omega⟩),
              sq_nonneg (M ⟨2 * c, by omega⟩ ⟨2 * L - 1, by omega⟩)], by linarith⟩
          exact memIvInt_ivAddInt (memIvInt_ivAddInt ho1 ho2) (memIvInt_ivMulInt hcum hpad)
        rw [hcc0, sum_Icc_bot (by omega : c ≤ L)]; simpa using memIvInt_ivAddInt hpc hnext
      · -- Tail index `idx' + 1`
        have hlt' : idx' < m + 1 := (by omega); have hcc_eq : L + 1 - (m + 2) + (idx' + 1) = L + 1 -
          (m + 1) + idx' := (by omega); rw [hcc_eq]; simpa using hih idx' hlt'
theorem max_div_nonneg_right (a b c : ℝ) (hc : 0 ≤ c) : max a b / c = max (a / c) (b / c) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (div_le_div_of_nonneg_right h hc)]
  · rw [max_eq_left h, max_eq_left (div_le_div_of_nonneg_right h hc)]
theorem swLClampTailLbs_sound : ∀ (ivs : List IvInt) (tReal : ℕ → ℝ) (c0 : ℕ), (∀ i < ivs.length, 0
  ≤ tReal (c0 + i) ∧ tReal (c0 + i) ≤ 1 ∧ ((ivs.getD i (0, 0)).1 : ℝ) / (swScale : ℝ) ≤ tReal (c0 +
  i)) → (∀ i : ℕ, i + 1 < ivs.length → tReal (c0 + i + 1) ≤ tReal (c0 + i)) → (swLClampTailLbs
  ivs).length = ivs.length ∧ ∀ i < ivs.length, (((swLClampTailLbs ivs).getD i 0 : ℤ) : ℝ) / (swScale
  : ℝ) ≤ tReal (c0 + i)
  | [], _, _, _, _ => ⟨rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | [ivL], tReal, c0, hb, _ => by
    have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); rcases hb 0 (by simp) with
      ⟨ht0, _, hlo⟩; unfold swLClampTailLbs; simp only [List.length_singleton, true_and]; intro i hi
    have hi0 : i = 0 := (by omega); subst hi0; simp only [add_zero, List.getD_cons_zero] at hlo ⊢
    rw [Int.cast_max, Int.cast_zero, max_div_nonneg_right _ _ _ hS.le, zero_div]
    exact max_le ht0 hlo
  | iv :: iv2 :: rest, tReal, c0, hb, hmono => by
    have hS : (0 : ℝ) < (swScale : ℝ) := by unfold swScale; norm_num
    rcases swLClampTailLbs_sound (iv2 :: rest) tReal (c0 + 1)
      (fun i hi ↦ by
        rcases hb (i + 1) (by simp at hi ⊢; omega) with ⟨h1, h2, h3⟩; rw [show c0 + (i + 1) = c0 + 1
          + i by omega] at h1 h2 h3
        exact ⟨h1, h2, h3⟩)
      (fun i hi ↦ by
        have hm := hmono (i + 1) (by simp at hi ⊢; omega)
        rwa [show c0 + (i + 1) + 1 = c0 + 1 + i + 1 by omega,
          show c0 + (i + 1) = c0 + 1 + i by omega] at hm)
      with ⟨hlen, hih⟩
    unfold swLClampTailLbs; rcases hcl : swLClampTailLbs (iv2 :: rest) with _ | ⟨nextLb, lbs⟩
    · rw [hcl] at hlen; simp at hlen
    rw [hcl] at hlen hih; dsimp only; rw [withForcedInt_eq]
    refine ⟨by simp at hlen ⊢; omega, fun i hi ↦ ?_⟩; rcases i with _ | i'
    · rcases hb 0 (by simp) with ⟨_, ht1, hlo⟩
      simp only [add_zero, List.getD_cons_zero] at ht1 hlo ⊢
      have h1 : (nextLb : ℝ) / (swScale : ℝ) ≤ tReal (c0 + 1) := (by simpa using hih 0 (by simp))
      have h2 : tReal (c0 + 1) ≤ tReal c0 := (by simpa using hmono 0 (by simp))
      have hnext_le : (nextLb : ℝ) / (swScale : ℝ) ≤ tReal c0 := h1.trans h2; have hmin_le : ((min
        swScale iv.1 : ℤ) : ℝ) / (swScale : ℝ) ≤ tReal c0 := (div_le_div_of_nonneg_right
        (by exact_mod_cast min_le_right swScale iv.1) hS.le).trans hlo; rw [Int.cast_max,
        max_div_nonneg_right _ _ _ hS.le]; exact max_le hnext_le hmin_le
    · have hi' : i' < (iv2 :: rest).length := (by simp at hi ⊢; omega); rw [show c0 + (i' + 1) = c0
        + 1 + i' by omega]; simpa using hih i' hi'
theorem checkSwLBucketCert_sound {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt} {trigIvs
  : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb : ℤ} (hn96 : 96
  ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk : checkSwLBucketCert L rMin rMax tauNum tauDen
  ratios trigIvs pulses tailLbs survUb = true) : ∃ (hL2 : 2 ≤ L), L ≤ 8 ∧ L ≤ r ∧ r ≤ 1024 ∧ 1 ≤
  pulses.length ∧ pulses.length ≤ 250 ∧ pulses.all swLPulseValid = true ∧ tailLbs.length = L ∧ 0 ≤
  survUb ∧ 0 < tailLbs.getD 0 0 ∧ tailLbs.getD 0 0 ≤ swScale ∧ 0 ≤ tailLbs.getD (L - 1) 0 ∧ (∀ i :
  ℕ, i + 1 < L → tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0) ∧ ∀ (M : Fin (2 * L) → Fin (2 * L) → ℝ),
  IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs pulses
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        0 ≤ out.2.2 ∧ out.2.2 ≤ (survUb : ℝ) / (swScale : ℝ) ∧ ∀ c ∈ Finset.Icc 1 L, ((tailLbs.getD
          (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ ∑ h ∈ Finset.Icc c L, p h := by
  unfold checkSwLBucketCert at hchk; simp only [withForcedState_eq, Bool.and_eq_true,
    decide_eq_true_eq] at hchk; rcases hchk with ⟨⟨⟨⟨⟨hp1, hp250, htl_len, hsurv0, htl0_pos,
    htl0_le, htlL0⟩, hp_val⟩, htl_mono⟩, hang⟩, ⟨hsurv_ub, hcl_len⟩, htl_le⟩
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at htl_mono htl_le
  rcases checkSwLBucketAngles_sound hn96 hmin hmax hang with ⟨hL2, hL8, hLr, hr1024, _, htrig⟩
  refine ⟨hL2, hL8, hLr, hr1024, hp1, hp250, hp_val, htl_len, hsurv0, htl0_pos, htl0_le, htlL0, fun
    i hi ↦ htl_mono i (by omega), ?_⟩; intro M hM K_blk cs out p
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); have hcs_unit : ∀ w : Fin L,
    (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun w ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum hL2 hcs_unit pulses hp_val with ⟨hcons, hcum0, _, hsurv_nn⟩
  rcases memIvInt_evolution (cs := cs) hL2 htrig pulses hp_val with ⟨hst_mem, hcum_mem, hsurv_mem⟩
  have hsurv_le : out.2.2 ≤ (survUb : ℝ) / (swScale : ℝ) := hsurv_mem.2.trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hsurv_ub) hS.le)
  have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg hL2 M out.1 hcum0 h
  have hp_sum1 : ∑ h ∈ Finset.range (L + 1), p h = 1 := swLAttemptProbReal_sum_one hL2 hM hcons
  set outIv := swLEvolutionIv L trigIvs pulses
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
  have htailIvs_len : tailIvs.length = L := (by dsimp [tailIvs]; simp [hsfx_len]; omega)
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
      rw [htailIvs_len] at hi; dsimp [tReal]; exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_left (by omega)) fun h _ _ ↦ hp_nn h)
  refine ⟨hsurv_nn, hsurv_le, fun c hc ↦ ?_⟩; rw [Finset.mem_Icc] at hc; have hidx : c - 1 < L :=
    (by omega); have hle_cert := htl_le (c - 1) hidx
  have hcert_real := hclamp.2 (c - 1) (by rw [htailIvs_len]; exact hidx)
  have h1c : 1 + (c - 1) = c := (by omega); rw [h1c] at hcert_real
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hle_cert) hS.le).trans hcert_real
/-! ## 6. `m = 1` Multi-Step (`1 ≤ h ≤ L`) Bellman Cascade Checker & Soundness -/
/-- Asymptotic floor `2^49 = 562949953421312 = 2 * 2^48 ≤ 2 * √(2^n)` for `n ≥ 96`. -/
def swBden49 : ℤ := 562949953421312
/-- Pure-integer `m = 1` multi-step Bellman recurrence check matching
  `SwLIntChecker.check_m1_step`. -/
def checkSwLM1Step (L r tauNum tauDen verCalls : ℕ)
    (tailLbs : List ℤ) (survUb vScale vCur : ℤ) (vPrevs : List ℤ) : Bool :=
  let chain := vCur :: vPrevs
  let rhsInt := (List.range L).foldl
    (fun acc c ↦ acc + tailLbs.getD c 0 * (chain.getD c 0 - chain.getD (c + 1) 0)) 0
  let bNum := 3 * survUb + 2 * swScale * (verCalls : ℤ)
  withForcedInt (rhsInt * swBden49 - vScale * bNum) fun rem ↦
    decide (2 ≤ L ∧ L ≤ 8 ∧ L ≤ r ∧ r ≤ 1024 ∧ 0 < tauNum ∧ 0 < tauDen ∧
      tailLbs.length = L ∧ vPrevs.length = L ∧ 0 ≤ survUb ∧ 0 < vScale ∧
      0 < tailLbs.getD 0 0 ∧ tailLbs.getD 0 0 ≤ swScale ∧ 0 ≤ tailLbs.getD (L - 1) 0 ∧
      0 ≤ chain.getD L 0 ∧ 0 ≤ rem ∧
      (survUb * (tauNum : ℤ) * vScale * swBden49) ^ 2 ≤
        4 * ((tauDen : ℤ) ^ 2) * (r : ℤ) * (rem ^ 2)) &&
    (List.range (L - 1)).all (fun i ↦ decide (tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0)) &&
    (List.range L).all (fun i ↦ decide (chain.getD (i + 1) 0 ≤ chain.getD i 0))
/-- Table-indexed wrapper around `checkSwLM1Step`. -/
def checkSwLM1StepTable (L r tauNum tauDen verCalls : ℕ)
    (tailLbs : List ℤ) (survUb vScale : ℤ) (vTable : ℕ → ℤ) : Bool :=
  checkSwLM1Step L r tauNum tauDen verCalls tailLbs survUb vScale
    (vTable r) ((List.range L).map fun i ↦ vTable (r - (i + 1)))
theorem kBlk_le_main_add_three_halves {n r tauNum tauDen : ℕ} (hn96 : 96 ≤ n) (hr1 : 1 ≤ r) (hr1024
  : r ≤ 1024) (htau : 0 < tauNum) (hden : 0 < tauDen) : (swLKBlk n r tauNum tauDen : ℝ) ≤ ((tauNum :
  ℝ) / (2 * (tauDen : ℝ) * √(r : ℝ))) * √(2 ^ n : ℝ) + 3 / 2 := by
  set N : ℝ := (2 ^ n : ℝ); have hr_pos : (0 : ℝ) < (r : ℝ) := (by exact_mod_cast hr1)
  have hsqrt_r_pos : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
  have hN96 : (79228162514264337593543950336 : ℝ) ≤ N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96; have hpow_r : ((2 ^ 96 : ℕ)
      : ℝ) ≤ N := (by dsimp [N]; exact_mod_cast hpow); have hval : ((2 ^ 96 : ℕ) : ℝ) =
      79228162514264337593543950336 := (by norm_num); linarith
  have hN_pos : 0 < N := (by linarith)
  have hsqrt_N_pos : 0 < √N := Real.sqrt_pos.2 hN_pos; set c₁ : ℝ := N / (r : ℝ)
  have hc1_ge : (8796093022208 : ℝ) ^ 2 ≤ c₁ := by
    dsimp [c₁]; rw [le_div_iff₀ hr_pos]; have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
    calc (8796093022208 : ℝ) ^ 2 * (r : ℝ)
      _ ≤ (8796093022208 : ℝ) ^ 2 * 1024 := mul_le_mul_of_nonneg_left hr_le (by norm_num)
      _ = 79228162514264337593543950336 := by norm_num
      _ ≤ N := hN96
  have hsqrt_c1_ge : (8796093022208 : ℝ) ≤ √c₁ :=
    (by rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8796093022208)]; exact Real.sqrt_le_sqrt hc1_ge)
  set α₀ : ℝ := Real.arcsin (1 / √c₁)
  rcases arcsin_small_boundsL (by positivity) (one_div_le_one_div_of_le (by norm_num)
    (by linarith : (8000000000000 : ℝ) ≤ √c₁)) with ⟨hα_pos, _, hα_lb, _⟩; set tauR : ℝ := (tauNum :
    ℝ) / (tauDen : ℝ); have htau_nn : 0 ≤ tauR := div_nonneg (by positivity) (by positivity)
  rcases odd_round_div_sub_mem_Icc hα_pos htau_nn with ⟨_, hodd_hi⟩
  have hK_mul : 2 * (swLKBlk n r tauNum tauDen : ℝ) * α₀ ≤ tauR + 3 * α₀ := by
    unfold swLKBlk; rw [Nat.cast_add, Nat.cast_one]; dsimp [tauR, α₀, c₁, N] at hodd_hi ⊢; linarith
  have hK_div : (swLKBlk n r tauNum tauDen : ℝ) ≤ tauR / (2 * α₀) + 3 / 2 := by
    have h2α : 0 < 2 * α₀ := (by linarith)
    have h1 : (swLKBlk n r tauNum tauDen : ℝ) = (2 * (swLKBlk n r tauNum tauDen : ℝ) * α₀) / (2 *
      α₀) := by
      calc (swLKBlk n r tauNum tauDen : ℝ)
        _ = (swLKBlk n r tauNum tauDen : ℝ) * ((2 * α₀) / (2 * α₀)) := by
              rw [div_self h2α.ne', mul_one]
        _ = (2 * (swLKBlk n r tauNum tauDen : ℝ) * α₀) / (2 * α₀) := by ring
    have h2 : (tauR + 3 * α₀) / (2 * α₀) = tauR / (2 * α₀) + 3 / 2 := by
      rw [add_div, show 3 * α₀ / (2 * α₀) = (3 / 2 : ℝ) * (α₀ / α₀) by ring,
        div_self hα_pos.ne', mul_one]
    rw [h1, ← h2]; exact div_le_div_of_nonneg_right hK_mul h2α.le
  have hc1_inv : 1 / √c₁ = √(r : ℝ) / √N := by dsimp [c₁]; rw [Real.sqrt_div hN_pos.le, one_div_div]
  have hα_ge : √(r : ℝ) / √N ≤ α₀ := hc1_inv ▸ hα_lb
  have hdiv_le : tauR / (2 * α₀) ≤ ((tauNum : ℝ) / (2 * (tauDen : ℝ) * √(r : ℝ))) * √N := by
    have h1 : 1 / (2 * α₀) ≤ 1 / (2 * (√(r : ℝ) / √N)) := one_div_le_one_div_of_le (by positivity)
      (by linarith); have h2 := mul_le_mul_of_nonneg_left h1 htau_nn; refine (div_eq_mul_one_div
      tauR (2 * α₀)).trans_le (h2.trans_eq ?_); dsimp [tauR]; have hden_ne : (tauDen : ℝ) ≠ 0 :=
      (by positivity); field_simp [hden_ne, hsqrt_r_pos.ne', hsqrt_N_pos.ne']
  linarith
theorem sum_div_const {ι : Type*} (s : Finset ι) (f : ι → ℝ) (d : ℝ) : (∑ i ∈ s, f i) / d = ∑ i ∈ s,
  f i / d := by simp_rw [div_eq_mul_inv, Finset.sum_mul]
theorem sum_Icc_eq_sum_range_local {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ → M) : ∑ i ∈
  Finset.Icc a b, f i = ∑ d ∈ Finset.range (b + 1 - a), f (a + d) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
theorem sum_Icc_abel : ∀ (L : ℕ) (p g : ℕ → ℝ), ∑ h ∈ Finset.Icc 1 L, p h * (g 0 - g h) = ∑ c ∈
  Finset.range L, (∑ h ∈ Finset.Icc (c + 1) L, p h) * (g c - g (c + 1))
  | 0, _, _ => by simp
  | m + 1, p, g => by
    have h1 : ∑ h ∈ Finset.Icc 1 (m + 1), p h * (g 0 - g h) = (∑ h ∈ Finset.Icc 1 m, p h * (g 0 - g
      h)) + p (m + 1) * (g 0 - g (m + 1)) := sum_Icc_top (by omega) _; rw [h1, sum_Icc_abel m p g,
      Finset.sum_range_succ]; have hlast : ∑ h ∈ Finset.Icc (m + 1) (m + 1), p h = p (m + 1) :=
      (by simp); rw [hlast]
    have hsplit : ∑ c ∈ Finset.range m, (∑ h ∈ Finset.Icc (c + 1) (m + 1), p h) * (g c - g (c + 1))
      = (∑ c ∈ Finset.range m, (∑ h ∈ Finset.Icc (c + 1) m, p h) * (g c - g (c + 1))) + p (m + 1) *
      (∑ c ∈ Finset.range m, (g c - g (c + 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun c hc ↦ ?_
      rw [Finset.mem_range] at hc; rw [sum_Icc_top (by omega)]; ring
    rw [hsplit, Finset.sum_range_sub']; ring
theorem foldl_range_add_eq_sum (n : ℕ) (f : ℕ → ℤ) : (List.range n).foldl (fun acc i ↦ acc + f i) 0
  = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Finset.sum_range_succ]
theorem checkSwLM1Stage_sound {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt} {trigIvs :
  List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb vScale : ℤ}
  {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hbkt : checkSwLBucketCert L
  rMin rMax tauNum tauDen ratios trigIvs pulses tailLbs survUb = true) (hstep : checkSwLM1StepTable
  L r tauNum tauDen L tailLbs survUb vScale vTable = true) : ∃ (hL2 : 2 ≤ L), L ≤ 8 ∧ L ≤ r ∧
  pulses.all swLPulseValid = true ∧ ∀ (M : Fin (2 * L) → Fin (2 * L) → ℝ), IsValidSwLOverlap M →
        let K_blk := swLKBlk n r tauNum tauDen
        let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
          Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := swLEvolutionReal L hL2 cs pulses
        let p : ℕ → ℝ := swLAttemptProbReal L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + (L : ℝ) + ∑ h ∈ Finset.Icc 1 L, p h * V (r - h)) /
          pSucc ≤ V r := by
  rcases checkSwLBucketCert_sound hn96 hmin hmax hbkt with ⟨hL2, hL8, hLr, hr1024, _, _, hp_val, _,
    _, htl0_pos, _, _, _, hbkt_M⟩; unfold checkSwLM1StepTable checkSwLM1Step at hstep
  simp only [withForcedInt_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hstep; rcases hstep with ⟨⟨⟨_, _, _, _, htau, hden, _, _, hsurv0, hvsc_pos,
    _, _, _, _, hrem0, hsq_ineq⟩, _⟩, hchain_mono⟩; refine ⟨hL2, hL8, hLr, hp_val, ?_⟩
  intro M hM K_blk cs out p pSucc V; rcases hbkt_M M hM with ⟨hsurv_nn, hsurv_le, htail_lbs⟩
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); have hvsc_r : (0 : ℝ) <
    (vScale : ℝ) := (by exact_mod_cast hvsc_pos); have hbden_r : (0 : ℝ) < (swBden49 : ℝ) :=
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
      (div_nonneg (by exact_mod_cast hsurv0) hS.le); have hsurv0_r : (0 : ℝ) ≤ (survUb : ℝ) :=
      (by exact_mod_cast hsurv0)
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
    have hr_pos : (0 : ℝ) < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r))
    have hsqrt_r_pos : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
    have hden_r : (0 : ℝ) < (tauDen : ℝ) := (by exact_mod_cast hden); have hrem_r : (0 : ℝ) ≤ (rem :
      ℝ) := (by exact_mod_cast hrem0)
    have hlhs_nn : 0 ≤ (survUb : ℝ) * (tauNum : ℝ) * (vScale : ℝ) * (swBden49 : ℝ) :=
      (by have : (0 : ℝ) ≤ (survUb : ℝ) := (by exact_mod_cast hsurv0); positivity)
    have hrhs_nn : 0 ≤ 2 * (tauDen : ℝ) * √(r : ℝ) * (rem : ℝ) := (by positivity)
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
/-! ## 7. `MultiSW_L` Hypergeometric Union-Hit Tail, Stage Cascade & Relative Cost -/
/-! ### 7.1 Falling-Factorial Identities & `swLGReal` Convexity -/
/-- Kernel-friendly binomial coefficient avoiding exponential `Nat.choose` recursion. -/
def swLBinomSmall (n k : ℕ) : ℕ :=
  n.descFactorial k / k.descFactorial k
theorem swLBinomSmall_eq_choose (n k : ℕ) : swLBinomSmall n k = n.choose k := by
  rw [swLBinomSmall, Nat.descFactorial_self, ← Nat.choose_eq_descFactorial_div_factorial]
theorem succ_descFactorial_eq_add (n m : ℕ) : (n + 1).descFactorial (m + 1) = n.descFactorial (m +
  1) + (m + 1) * n.descFactorial m := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_succ_succ, Nat.factorial_succ]; ring
theorem descFact_split_step {r u h i : ℕ} (hi : i ≤ h) (hu : u ≤ r) : (r - h) * ((r -
  u).descFactorial i * u.descFactorial (h - i)) = (r - u).descFactorial (i + 1) * u.descFactorial (h
  - i) + (r - u).descFactorial i * u.descFactorial (h + 1 - i) := by
  rw [Nat.descFactorial_succ, show h + 1 - i = (h - i) + 1 by omega, Nat.descFactorial_succ]
  by_cases h1 : i ≤ r - u
  · by_cases h2 : h - i ≤ u
    · have hsplit : r - h = (r - u - i) + (u - (h - i)) := (by omega); rw [hsplit]; ring
    · have hz : u.descFactorial (h - i) = 0 := Nat.descFactorial_of_lt (by omega); simp [hz]
  · have hz : (r - u).descFactorial i = 0 := Nat.descFactorial_of_lt (by omega); simp [hz]
/-- Combinatorial summand of `swLGReal` at marked hit count `c`. -/
noncomputable def swLATerm (L r j u c : ℕ) : ℕ :=
  (c - 1).choose (j - 1) * (r - u).descFactorial j * u.descFactorial (c - j) *
    (r - c).descFactorial (L - c)
/-- Closed-form hypergeometric prefix sum of `swLATerm L r j u c` over `j ≤ c ≤ h`. -/
noncomputable def swLARhs (L r j u h : ℕ) : ℕ :=
  (r - h).descFactorial (L - h) *
    ∑ i ∈ Finset.Icc j h, h.choose i * (r - u).descFactorial i * u.descFactorial (h - i)
theorem swLA_prefix_sum {L r j u : ℕ} (hj1 : 1 ≤ j) (hLr : L ≤ r) (hu : u ≤ r) : ∀ h : ℕ, h ≤ L → ∑
  c ∈ Finset.Icc j h, swLATerm L r j u c = swLARhs L r j u h
  | 0, _ => by have hlt : 0 < j := hj1; simp [swLARhs, Finset.Icc_eq_empty_of_lt hlt]
  | h + 1, hh1 => by
      by_cases hlt : h + 1 < j
      · simp [swLARhs, Finset.Icc_eq_empty_of_lt hlt]
      · by_cases heq : h + 1 = j
        · subst heq; simp [swLATerm, swLARhs]; ring
        · have hjh : j ≤ h := (by omega); rw [sum_Icc_top (by omega : j ≤ h + 1), swLA_prefix_sum
            hj1 hLr hu h (by omega)]; unfold swLARhs swLATerm
          have hdesc : (r - h).descFactorial (L - h) = (r - h) * (r - (h + 1)).descFactorial (L - (h
            + 1)) := by
            have hr_eq : r - h = (r - (h + 1)) + 1 := by omega
            have hL_eq : L - h = (L - (h + 1)) + 1 := (by omega); rw [hr_eq, hL_eq,
              Nat.succ_descFactorial_succ]
          rw [hdesc]; set fac := (r - (h + 1)).descFactorial (L - (h + 1))
          have hlhs : (r - h) * fac * (∑ i ∈ Finset.Icc j h, h.choose i * (r - u).descFactorial i *
            u.descFactorial (h - i)) + (h + 1 - 1).choose (j - 1) * (r - u).descFactorial j *
            u.descFactorial (h + 1 - j) * fac = fac * ((∑ i ∈ Finset.Icc j h, h.choose i * ((r - h)
            * ((r - u).descFactorial i * u.descFactorial (h - i)))) + h.choose (j - 1) * (r -
            u).descFactorial j * u.descFactorial (h + 1 - j)) := by
            rw [Nat.add_sub_cancel]
            have hmul : (r - h) * (∑ i ∈ Finset.Icc j h, h.choose i * (r - u).descFactorial i *
              u.descFactorial (h - i)) = ∑ i ∈ Finset.Icc j h, h.choose i * ((r - h) * ((r -
              u).descFactorial i * u.descFactorial (h - i))) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ ↦ by ring
            calc (r - h) * fac *
                  (∑ i ∈ Finset.Icc j h,
                    h.choose i * (r - u).descFactorial i * u.descFactorial (h - i)) +
                h.choose (j - 1) * (r - u).descFactorial j * u.descFactorial (h + 1 - j) * fac
              _ = fac * ((r - h) *
                  (∑ i ∈ Finset.Icc j h,
                    h.choose i * (r - u).descFactorial i * u.descFactorial (h - i))) +
                  fac * (h.choose (j - 1) * (r - u).descFactorial j *
                    u.descFactorial (h + 1 - j)) := by ring
              _ = _ := by rw [hmul, ← mul_add]
          rw [hlhs]; congr 1
          have hstep_sum : ∑ i ∈ Finset.Icc j h, h.choose i * ((r - h) * ((r - u).descFactorial i *
            u.descFactorial (h - i))) = (∑ i ∈ Finset.Icc j h, h.choose i * (r - u).descFactorial (i
            + 1) * u.descFactorial (h - i)) + ∑ i ∈ Finset.Icc j h, h.choose i * (r -
            u).descFactorial i * u.descFactorial (h + 1 - i) := by
            rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [Finset.mem_Icc] at hi; rw [descFact_split_step hi.2 hu]; ring
          rw [hstep_sum]
          have hrhs_bot : ∑ i ∈ Finset.Icc j (h + 1), (h + 1).choose i * (r - u).descFactorial i *
            u.descFactorial (h + 1 - i) = (h + 1).choose j * (r - u).descFactorial j *
            u.descFactorial (h + 1 - j) + ∑ i ∈ Finset.Icc (j + 1) (h + 1), (h + 1).choose i * (r -
            u).descFactorial i * u.descFactorial (h + 1 - i) := sum_Icc_bot (by omega) _
          have hcj : (h + 1).choose j = h.choose (j - 1) + h.choose j := by
            obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
            rw [hk]; exact Nat.choose_succ_succ h k
          have hrhs_rest : ∑ i ∈ Finset.Icc (j + 1) (h + 1), (h + 1).choose i * (r -
            u).descFactorial i * u.descFactorial (h + 1 - i) = (∑ i ∈ Finset.Icc j h, h.choose i *
            (r - u).descFactorial (i + 1) * u.descFactorial (h - i)) + ∑ i ∈ Finset.Icc (j + 1) h,
            h.choose i * (r - u).descFactorial i * u.descFactorial (h + 1 - i) := by
            have hshift : ∑ i ∈ Finset.Icc (j + 1) (h + 1), (h + 1).choose i * (r - u).descFactorial
              i * u.descFactorial (h + 1 - i) = (∑ i ∈ Finset.Icc (j + 1) (h + 1), h.choose (i - 1)
              * (r - u).descFactorial i * u.descFactorial (h + 1 - i)) + ∑ i ∈ Finset.Icc (j + 1) (h
              + 1), h.choose i * (r - u).descFactorial i * u.descFactorial (h + 1 - i) := by
              rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i hi ↦ ?_
              rw [Finset.mem_Icc] at hi
              have hci : (h + 1).choose i = h.choose (i - 1) + h.choose i := by
                obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
                rw [hk]; exact Nat.choose_succ_succ h k
              rw [hci]; ring
            have hs1 : ∑ i ∈ Finset.Icc (j + 1) (h + 1), h.choose (i - 1) * (r - u).descFactorial i
              * u.descFactorial (h + 1 - i) = ∑ k ∈ Finset.Icc j h, h.choose k * (r -
              u).descFactorial (k + 1) * u.descFactorial (h - k) := by
              rw [sum_Icc_eq_sum_range_local, sum_Icc_eq_sum_range_local, show h + 1 + 1 - (j + 1) =
                h + 1 - j by omega]; refine Finset.sum_congr rfl fun d _ ↦ ?_
              rw [show j + 1 + d - 1 = j + d by omega,
                show j + 1 + d = j + d + 1 by omega,
                show h + 1 - (j + d + 1) = h - (j + d) by omega]
            have hs2 : ∑ i ∈ Finset.Icc (j + 1) (h + 1), h.choose i * (r - u).descFactorial i *
              u.descFactorial (h + 1 - i) = ∑ i ∈ Finset.Icc (j + 1) h, h.choose i * (r -
              u).descFactorial i * u.descFactorial (h + 1 - i) := by
              rw [sum_Icc_top (by omega : j + 1 ≤ h + 1), Nat.choose_eq_zero_of_lt
                (by omega : h < h + 1)]; simp
            rw [hshift, hs1, hs2]
          have hbot2 : ∑ i ∈ Finset.Icc j h, h.choose i * (r - u).descFactorial i * u.descFactorial
            (h + 1 - i) = h.choose j * (r - u).descFactorial j * u.descFactorial (h + 1 - j) + ∑ i ∈
            Finset.Icc (j + 1) h, h.choose i * (r - u).descFactorial i * u.descFactorial (h + 1 - i)
            := sum_Icc_bot hjh _; rw [hrhs_bot, hcj, hrhs_rest, hbot2]; ring
theorem sum_Icc_abel_prefix {j : ℕ} : ∀ {L : ℕ}, j ≤ L → ∀ (f a : ℕ → ℝ), ∑ c ∈ Finset.Icc j L, f c
  * a c = (∑ h ∈ Finset.Ico j L, (f h - f (h + 1)) * (∑ c ∈ Finset.Icc j h, a c)) + f L * (∑ c ∈
  Finset.Icc j L, a c)
  | 0, hj0, f, a => by have rfl_j : j = 0 := (by omega); subst rfl_j; simp
  | m + 1, hjm1, f, a => by
    by_cases hjm : j ≤ m
    · rw [sum_Icc_top hjm1, sum_Icc_abel_prefix hjm f a, Finset.sum_Ico_succ_top hjm, sum_Icc_top
        hjm1]; ring
    · have heq : j = m + 1 := (by omega); subst heq; simp
theorem swLARhs_shift_le {L r j u h : ℕ} (hj1 : 1 ≤ j) (hu1 : u + 1 ≤ r) : swLARhs L r (j + 1) u h ≤
  swLARhs L r j (u + 1) h := by
  unfold swLARhs; refine Nat.mul_le_mul_left _ ?_; by_cases hlt : h < j
  · simp [Finset.Icc_eq_empty_of_lt hlt, Finset.Icc_eq_empty_of_lt (by omega : h < j + 1)]
  · obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩; set w := r - (u + 1); have hrw : r - u =
      w + 1 := (by omega); rw [hrw]
    have hlhs : ∑ i ∈ Finset.Icc (j + 1) (m + 1), (m + 1).choose i * (w + 1).descFactorial i *
      u.descFactorial (m + 1 - i) = (∑ i ∈ Finset.Icc (j + 1) (m + 1), (m + 1).choose i *
      w.descFactorial i * u.descFactorial (m + 1 - i)) + ∑ k ∈ Finset.Icc j m, (m + 1) * m.choose k
      * w.descFactorial k * u.descFactorial (m - k) := by
      have h1 : ∑ i ∈ Finset.Icc (j + 1) (m + 1), (m + 1).choose i * (w + 1).descFactorial i *
        u.descFactorial (m + 1 - i) = (∑ i ∈ Finset.Icc (j + 1) (m + 1), (m + 1).choose i *
        w.descFactorial i * u.descFactorial (m + 1 - i)) + ∑ i ∈ Finset.Icc (j + 1) (m + 1), ((m +
        1).choose i * i) * w.descFactorial (i - 1) * u.descFactorial (m + 1 - i) := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [Finset.mem_Icc] at hi
        have hwd : (w + 1).descFactorial i = w.descFactorial i + i * w.descFactorial (i - 1) := by
          conv_lhs => rw [show i = (i - 1) + 1 by omega]
          rw [succ_descFactorial_eq_add, show (i - 1) + 1 = i by omega]
        rw [hwd]; ring
      have h2 : ∑ i ∈ Finset.Icc (j + 1) (m + 1), ((m + 1).choose i * i) * w.descFactorial (i - 1) *
        u.descFactorial (m + 1 - i) = ∑ k ∈ Finset.Icc j m, (m + 1) * m.choose k * w.descFactorial k
        * u.descFactorial (m - k) := by
        by_cases hjm : j ≤ m
        · rw [sum_Icc_eq_sum_range_local, sum_Icc_eq_sum_range_local, show m + 1 + 1 - (j + 1) = m +
            1 - j by omega]; refine Finset.sum_congr rfl fun d _ ↦ ?_; set k := j + d
          have hid : j + 1 + d = k + 1 := (by omega); rw [hid, Nat.add_sub_cancel,
            Nat.succ_sub_succ_eq_sub, ← Nat.add_one_mul_choose_eq]
        · have heq : j = m + 1 := (by omega); simp [Finset.Icc_eq_empty_of_lt (by omega : m < j),
            Finset.Icc_eq_empty_of_lt (by omega : m + 1 < j + 1)]
      rw [h1, h2]
    have hrhs : ∑ i ∈ Finset.Icc j (m + 1), (m + 1).choose i * w.descFactorial i * (u +
      1).descFactorial (m + 1 - i) = (∑ i ∈ Finset.Icc j (m + 1), (m + 1).choose i * w.descFactorial
      i * u.descFactorial (m + 1 - i)) + ∑ i ∈ Finset.Icc j m, (m + 1) * m.choose i *
      w.descFactorial i * u.descFactorial (m - i) := by
      by_cases hjm : j ≤ m
      · rw [sum_Icc_top (by omega : j ≤ m + 1), sum_Icc_top (by omega : j ≤ m + 1)]
        simp only [Nat.sub_self, Nat.descFactorial_zero, mul_one]
        have hmid : ∑ i ∈ Finset.Icc j m, (m + 1).choose i * w.descFactorial i * (u +
          1).descFactorial (m + 1 - i) = (∑ i ∈ Finset.Icc j m, (m + 1).choose i * w.descFactorial i
          * u.descFactorial (m + 1 - i)) + ∑ i ∈ Finset.Icc j m, ((m + 1).choose i * (m + 1 - i)) *
          w.descFactorial i * u.descFactorial (m - i) := by
          rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [Finset.mem_Icc] at hi
          have hud : (u + 1).descFactorial (m + 1 - i) = u.descFactorial (m + 1 - i) + (m + 1 - i) *
            u.descFactorial (m - i) := by
            conv_lhs => rw [show m + 1 - i = (m - i) + 1 by omega]
            rw [succ_descFactorial_eq_add, show (m - i) + 1 = m + 1 - i by omega]
          rw [hud]; ring
        have hch : ∑ i ∈ Finset.Icc j m, ((m + 1).choose i * (m + 1 - i)) * w.descFactorial i *
          u.descFactorial (m - i) = ∑ i ∈ Finset.Icc j m, (m + 1) * m.choose i * w.descFactorial i *
          u.descFactorial (m - i) :=
          (by refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [← Nat.choose_mul_succ_eq]; ring)
        rw [hmid, hch]; omega
      · have heq : j = m + 1 := (by omega); subst heq; simp
    have hbot : ∑ i ∈ Finset.Icc (j + 1) (m + 1), (m + 1).choose i * w.descFactorial i *
      u.descFactorial (m + 1 - i) ≤ ∑ i ∈ Finset.Icc j (m + 1), (m + 1).choose i * w.descFactorial i
      * u.descFactorial (m + 1 - i) := Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_left
      (by omega)); omega
theorem swLGReal_nonneg {L r : ℕ} {tailP : ℕ → ℝ} (htail0 : ∀ c ∈ Finset.Icc 1 L, 0 ≤ tailP c) (j u
  : ℕ) : 0 ≤ swLGReal L r tailP j u := by
  unfold swLGReal; split_ifs with hbad
  · exact le_rfl
  · push Not at hbad
    rcases hbad with ⟨_, hj0, _, _⟩
    refine div_nonneg (Finset.sum_nonneg fun c hc ↦ ?_) (Nat.cast_nonneg _)
    rw [Finset.mem_Icc] at hc
    exact mul_nonneg (htail0 c (Finset.mem_Icc.2 ⟨by omega, hc.2⟩)) (Nat.cast_nonneg _)
theorem swLGReal_mono_tailP {L r : ℕ} {tailP₁ tailP₂ : ℕ → ℝ} (hle : ∀ c ∈ Finset.Icc 1 L, tailP₁ c
  ≤ tailP₂ c) (j u : ℕ) : swLGReal L r tailP₁ j u ≤ swLGReal L r tailP₂ j u := by
  unfold swLGReal; split_ifs with hbad
  · exact le_rfl
  · push Not at hbad
    rcases hbad with ⟨_, hj0, _, _⟩; refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun c hc ↦
      ?_) (Nat.cast_nonneg _); rw [Finset.mem_Icc] at hc; exact mul_le_mul_of_nonneg_right (hle c
      (Finset.mem_Icc.2 ⟨by omega, hc.2⟩)) (Nat.cast_nonneg _)
theorem swLGReal_anti_j {L r : ℕ} {tailP : ℕ → ℝ} (htail0 : ∀ c ∈ Finset.Icc 1 L, 0 ≤ tailP c)
  (htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c + 1) ≤ tailP c) {j : ℕ} (hj1 : 1 ≤ j) (u : ℕ) :
  swLGReal L r tailP (j + 1) u ≤ swLGReal L r tailP j u := by
  by_cases hbad : r < L ∨ L < j + 1 ∨ r ≤ u
  · have hz : swLGReal L r tailP (j + 1) u = 0 := by
      unfold swLGReal; have hc : r < L ∨ j + 1 = 0 ∨ L < j + 1 ∨ r ≤ u := (by omega); simp only [hc,
        ↓reduceIte]
    rw [hz]; exact swLGReal_nonneg htail0 j u
  · push Not at hbad
    rcases hbad with ⟨hLr, hj1L, hur⟩; have hb1 : ¬(r < L ∨ j + 1 = 0 ∨ L < j + 1 ∨ r ≤ u) :=
      (by omega); have hb2 : ¬(r < L ∨ j = 0 ∨ L < j ∨ r ≤ u) := (by omega)
    unfold swLGReal; simp only [hb1, hb2, ↓reduceIte]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have hlhs_ext : ∑ c ∈ Finset.Icc (j + 1) L, tailP c * (swLATerm L r (j + 1) u c : ℝ) = ∑ c ∈
      Finset.Icc j L, tailP c * (swLATerm L r (j + 1) u c : ℝ) := by
      rw [sum_Icc_bot (by omega : j ≤ L)]
      have hz : swLATerm L r (j + 1) u j = 0 := by
        unfold swLATerm; rw [Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt (by omega : j - 1 < j)]
        simp
      simp [hz]
    have h1 : (∑ c ∈ Finset.Icc (j + 1) L, tailP c * (((c - 1).choose ((j + 1) - 1) * (r -
      u).descFactorial (j + 1) * u.descFactorial (c - (j + 1)) * (r - c).descFactorial (L - c) : ℕ)
      : ℝ)) = ∑ c ∈ Finset.Icc j L, tailP c * (swLATerm L r (j + 1) u c : ℝ) := hlhs_ext
    have h2 : (∑ c ∈ Finset.Icc j L, tailP c * (((c - 1).choose (j - 1) * (r - u).descFactorial j *
      u.descFactorial (c - j) * (r - c).descFactorial (L - c) : ℕ) : ℝ)) = ∑ c ∈ Finset.Icc j L,
      tailP c * (swLATerm L r j u c : ℝ) := rfl; rw [h1, h2, sum_Icc_abel_prefix (by omega : j ≤ L),
      sum_Icc_abel_prefix (by omega : j ≤ L)]
    have hpref_le : ∀ h : ℕ, j ≤ h → h ≤ L → (∑ c ∈ Finset.Icc j h, (swLATerm L r (j + 1) u c : ℝ))
      ≤ ∑ c ∈ Finset.Icc j h, (swLATerm L r j u c : ℝ) := by
      intro h hjh hhL
      have hl : ∑ c ∈ Finset.Icc j h, swLATerm L r (j + 1) u c = swLARhs L r (j + 1) u h := by
        rw [sum_Icc_bot hjh]
        have hz : swLATerm L r (j + 1) u j = 0 := by
          unfold swLATerm; rw [Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt (by omega : j - 1 < j)]
          simp
        rw [hz, zero_add]; exact swLA_prefix_sum (by omega) hLr hur.le h hhL
      have hr := swLA_prefix_sum hj1 hLr hur.le h hhL; exact_mod_cast (hl.trans_le
        (Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_left
        (by omega))))).trans_eq hr.symm
    refine add_le_add (Finset.sum_le_sum fun h hh ↦ ?_) ?_
    · rw [Finset.mem_Ico] at hh
      exact mul_le_mul_of_nonneg_left (hpref_le h hh.1 hh.2.le) (sub_nonneg.2 (htail_anti h
        (by omega) hh.2))
    · exact mul_le_mul_of_nonneg_left (hpref_le L (by omega) le_rfl) (htail0 L (Finset.mem_Icc.2
        ⟨by omega, le_rfl⟩))
theorem swLGReal_succ_le_shift {L r : ℕ} {tailP : ℕ → ℝ} (htail0 : ∀ c ∈ Finset.Icc 1 L, 0 ≤ tailP
  c) (htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c + 1) ≤ tailP c) {j : ℕ} (hj1 : 1 ≤ j) (u : ℕ) :
  swLGReal L r tailP (j + 1) u ≤ swLGReal L r tailP j (u + 1) := by
  by_cases hbad : r < L ∨ L < j + 1 ∨ r ≤ u
  · have hz : swLGReal L r tailP (j + 1) u = 0 := by
      unfold swLGReal; have hc : r < L ∨ j + 1 = 0 ∨ L < j + 1 ∨ r ≤ u := (by omega); simp only [hc,
        ↓reduceIte]
    rw [hz]; exact swLGReal_nonneg htail0 j (u + 1)
  · push Not at hbad
    rcases hbad with ⟨hLr, hj1L, hur⟩; by_cases hu1r : r ≤ u + 1
    · have hr_sub : r - u = 1 := (by omega)
      have hz : swLGReal L r tailP (j + 1) u = 0 := by
        unfold swLGReal; by_cases hc : r < L ∨ j + 1 = 0 ∨ L < j + 1 ∨ r ≤ u
        · simp only [hc, ↓reduceIte]
        · simp only [hc, ↓reduceIte]
          have hsum0 : ∑ c ∈ Finset.Icc (j + 1) L, tailP c * (((c - 1).choose ((j + 1) - 1) * (r -
            u).descFactorial (j + 1) * u.descFactorial (c - (j + 1)) * (r - c).descFactorial (L - c)
            : ℕ) : ℝ) = 0 := by
            refine Finset.sum_eq_zero fun c _ ↦ ?_; rw [hr_sub, Nat.descFactorial_of_lt
              (by omega : 1 < j + 1)]; push_cast; ring
          rw [hsum0, zero_div]
      rw [hz]; exact swLGReal_nonneg htail0 j (u + 1)
    · push Not at hu1r
      have hb1 : ¬(r < L ∨ j + 1 = 0 ∨ L < j + 1 ∨ r ≤ u) := (by omega); have hb2 : ¬(r < L ∨ j = 0
        ∨ L < j ∨ r ≤ u + 1) := (by omega); unfold swLGReal; simp only [hb1, hb2, ↓reduceIte]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have hlhs_ext : (∑ c ∈ Finset.Icc (j + 1) L, tailP c * (((c - 1).choose ((j + 1) - 1) * (r -
        u).descFactorial (j + 1) * u.descFactorial (c - (j + 1)) * (r - c).descFactorial (L - c) :
        ℕ) : ℝ)) = ∑ c ∈ Finset.Icc j L, tailP c * (swLATerm L r (j + 1) u c : ℝ) := by
        change ∑ c ∈ Finset.Icc (j + 1) L, tailP c * (swLATerm L r (j + 1) u c : ℝ) = _
        rw [sum_Icc_bot (by omega : j ≤ L)]
        have hz : swLATerm L r (j + 1) u j = 0 := by
          unfold swLATerm; rw [Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt (by omega : j - 1 < j)]
          simp
        simp [hz]
      have hrhs_eq : (∑ c ∈ Finset.Icc j L, tailP c * (((c - 1).choose (j - 1) * (r - (u +
        1)).descFactorial j * (u + 1).descFactorial (c - j) * (r - c).descFactorial (L - c) : ℕ) :
        ℝ)) = ∑ c ∈ Finset.Icc j L, tailP c * (swLATerm L r j (u + 1) c : ℝ) := rfl; rw [hlhs_ext,
        hrhs_eq, sum_Icc_abel_prefix (by omega : j ≤ L), sum_Icc_abel_prefix (by omega : j ≤ L)]
      have hpref_le : ∀ h : ℕ, j ≤ h → h ≤ L → (∑ c ∈ Finset.Icc j h, (swLATerm L r (j + 1) u c :
        ℝ)) ≤ ∑ c ∈ Finset.Icc j h, (swLATerm L r j (u + 1) c : ℝ) := by
        intro h hjh hhL
        have hl : ∑ c ∈ Finset.Icc j h, swLATerm L r (j + 1) u c = swLARhs L r (j + 1) u h := by
          rw [sum_Icc_bot hjh]
          have hz : swLATerm L r (j + 1) u j = 0 := by
            unfold swLATerm; rw [Nat.add_sub_cancel, Nat.choose_eq_zero_of_lt
              (by omega : j - 1 < j)]; simp
          rw [hz, zero_add]; exact swLA_prefix_sum (by omega) hLr hur.le h hhL
        have hr := swLA_prefix_sum hj1 hLr hu1r.le h hhL; exact_mod_cast (hl.trans_le
          (swLARhs_shift_le hj1 hu1r.le)).trans_eq hr.symm
      refine add_le_add (Finset.sum_le_sum fun h hh ↦ ?_) ?_
      · rw [Finset.mem_Ico] at hh
        exact mul_le_mul_of_nonneg_left (hpref_le h hh.1 hh.2.le) (sub_nonneg.2 (htail_anti h
          (by omega) hh.2))
      · exact mul_le_mul_of_nonneg_left (hpref_le L (by omega) le_rfl) (htail0 L (Finset.mem_Icc.2
          ⟨by omega, le_rfl⟩))
theorem swLGReal_one_le_one {L r : ℕ} {tailP : ℕ → ℝ} (htail_le1 : ∀ c ∈ Finset.Icc 1 L, tailP c ≤
  1) (u : ℕ) : swLGReal L r tailP 1 u ≤ 1 := by
  unfold swLGReal; by_cases hbad : r < L ∨ 1 = 0 ∨ L < 1 ∨ r ≤ u
  · simp only [hbad, ↓reduceIte]; norm_num
  · simp only [hbad, ↓reduceIte]; have hLr : L ≤ r := (by omega); have h1L : 1 ≤ L := (by omega)
    have hur : u < r := (by omega); have hd_pos : (0 : ℝ) < (r.descFactorial L : ℝ) :=
      (by exact_mod_cast Nat.descFactorial_pos.2 hLr); rw [div_le_one hd_pos]
    have hsum_le : (∑ c ∈ Finset.Icc 1 L, tailP c * (((c - 1).choose 0 * (r - u).descFactorial 1 *
      u.descFactorial (c - 1) * (r - c).descFactorial (L - c) : ℕ) : ℝ)) ≤ ∑ c ∈ Finset.Icc 1 L,
      (((r - u) * u.descFactorial (c - 1) * (r - c).descFactorial (L - c) : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun c hc ↦ ?_
      have h1 := mul_le_mul_of_nonneg_right (htail_le1 c hc) (Nat.cast_nonneg ((c - 1).choose 0 * (r
        - u).descFactorial 1 * u.descFactorial (c - 1) * (r - c).descFactorial (L - c)))
      simpa [Nat.choose_zero_right, Nat.descFactorial_one] using h1
    refine hsum_le.trans ?_; set F : ℕ → ℕ := fun k ↦ u.descFactorial k * (r - k).descFactorial (L -
      k)
    have htele : ∀ k < L, (r - u) * u.descFactorial k * (r - (k + 1)).descFactorial (L - (k + 1)) +
      F (k + 1) = F k := by
      intro k hkL; change (r - u) * u.descFactorial k * (r - (k + 1)).descFactorial (L - (k + 1)) +
        u.descFactorial (k + 1) * (r - (k + 1)).descFactorial (L - (k + 1)) = u.descFactorial k * (r
        - k).descFactorial (L - k)
      have hrd : (r - k).descFactorial (L - k) = (r - k) * (r - (k + 1)).descFactorial (L - (k + 1))
        := by
        rw [show r - k = (r - (k + 1)) + 1 by omega, show L - k = (L - (k + 1)) + 1 by omega,
          Nat.succ_descFactorial_succ]
      rw [hrd, Nat.descFactorial_succ]; by_cases hku : k ≤ u
      · have hsplit : (r - u) + (u - k) = r - k := (by omega)
        calc (r - u) * u.descFactorial k * (r - (k + 1)).descFactorial (L - (k + 1)) +
              (u - k) * u.descFactorial k * (r - (k + 1)).descFactorial (L - (k + 1))
          _ = ((r - u) + (u - k)) * u.descFactorial k *
                (r - (k + 1)).descFactorial (L - (k + 1)) := by ring
          _ = u.descFactorial k * ((r - k) * (r - (k + 1)).descFactorial (L - (k + 1))) := by
                rw [hsplit]; ring
      · have hz : u.descFactorial k = 0 := Nat.descFactorial_of_lt (by omega); simp [hz]
    have hsum_nat : (∑ c ∈ Finset.Icc 1 L, (r - u) * u.descFactorial (c - 1) * (r - c).descFactorial
      (L - c)) + F L = F 0 := by
      rw [sum_Icc_eq_sum_range_local, show L + 1 - 1 = L by omega]
      have hre : ∑ d ∈ Finset.range L, (r - u) * u.descFactorial (1 + d - 1) * (r - (1 +
        d)).descFactorial (L - (1 + d)) = ∑ k ∈ Finset.range L, (r - u) * u.descFactorial k * (r -
        (k + 1)).descFactorial (L - (k + 1)) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_; rw [show 1 + k - 1 = k
          by omega, show 1 + k = k + 1 by omega]
      rw [hre]
      have hind : ∀ m ≤ L, (∑ k ∈ Finset.range m, (r - u) * u.descFactorial k * (r - (k +
        1)).descFactorial (L - (k + 1))) + F m = F 0 := by
        intro m hm
        induction m with
        | zero => simp
        | succ m' ih =>
            rw [Finset.sum_range_succ, add_assoc, htele m' (by omega)]; exact ih (by omega)
      exact hind L le_rfl
    have hF0 : F 0 = r.descFactorial L := (by simp [F]); have hnat_le : ∑ c ∈ Finset.Icc 1 L, (r -
      u) * u.descFactorial (c - 1) * (r - c).descFactorial (L - c) ≤ r.descFactorial L := (by omega)
    exact_mod_cast hnat_le
/-! ### 7.2 `swLUnionTailReal` Convexity, Bounds, Antitonicity & Copy Monotonicity -/
theorem htail_le_one_of_anti {L : ℕ} {tailP : ℕ → ℝ} (htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c
  + 1) ≤ tailP c) (htail1 : tailP 1 ≤ 1) : ∀ c ∈ Finset.Icc 1 L, tailP c ≤ 1 := by
  intro c hc; rw [Finset.mem_Icc] at hc; obtain ⟨d, rfl⟩ : ∃ d, c = 1 + d := ⟨c - 1, by omega⟩
  induction d with
  | zero => simpa using htail1
  | succ d' ih =>
    have hstep := htail_anti (1 + d') (by omega) (by omega); rw [show 1 + (d' + 1) = (1 + d') + 1
      by omega]; exact hstep.trans (ih ⟨by omega, by omega⟩)
theorem swLUnionTailStepReal_eq_convex {L r s : ℕ} (hs1 : 1 ≤ s) (hsr : s ≤ r) (hL1 : 1 ≤ L) (hLr :
  L ≤ r) (tailP prev : ℕ → ℝ) :
    let mS := min L s; let c := fun j ↦ swLGReal L r tailP j (s - j)
    swLUnionTailStepReal L r tailP prev s = (1 - c 1) * prev s + (∑ j ∈ Finset.Ico 1 mS, (c j - c (j
      + 1)) * prev (s - j)) + c mS * prev (s - mS) := by
  intro mS c; unfold swLUnionTailStepReal; simp only [show ¬s = 0
    by omega, show ¬(r < s ∨ r < L) by omega, ↓reduceIte]; have hmS1 : 1 ≤ mS := le_min hL1 hs1;
    have hmSs : mS ≤ s := Nat.min_le_right L s
  have hind : ∀ k : ℕ, 1 ≤ k → k ≤ s → prev s + (∑ j ∈ Finset.Icc 1 k, c j * (prev (s - j) - prev (s
    - j + 1))) = (1 - c 1) * prev s + (∑ j ∈ Finset.Ico 1 k, (c j - c (j + 1)) * prev (s - j)) + c k
    * prev (s - k) := by
    intro k hk1 hks; obtain ⟨d, rfl⟩ : ∃ d, k = 1 + d := ⟨k - 1, by omega⟩
    induction d with
    | zero =>
      simp only [add_zero, Finset.Icc_self, Finset.sum_singleton, Finset.Ico_self,
        Finset.sum_empty, show s - 1 + 1 = s by omega]; ring
    | succ d' ih =>
      have hk' : 1 + (d' + 1) = (1 + d') + 1 := (by omega)
      rw [hk', sum_Icc_top (by omega : 1 ≤ (1 + d') + 1), ← add_assoc, ih (by omega) (by omega),
        Finset.sum_Ico_succ_top (by omega : 1 ≤ 1 + d'), show s - ((1 + d') + 1) + 1 = s - (1 +
        d') by omega]; ring
  exact hind mS hmS1 hmSs
theorem swLUnionTailStepReal_mono_prev {L r : ℕ} {tailP prev₁ prev₂ : ℕ → ℝ} (htail0 : ∀ c ∈
  Finset.Icc 1 L, 0 ≤ tailP c) (htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c + 1) ≤ tailP c)
  (htail1 : tailP 1 ≤ 1) (hprev : ∀ k : ℕ, prev₁ k ≤ prev₂ k) (s : ℕ) : swLUnionTailStepReal L r
  tailP prev₁ s ≤ swLUnionTailStepReal L r tailP prev₂ s := by
  rcases Nat.eq_zero_or_pos L with rfl | hL1
  · unfold swLUnionTailStepReal; split_ifs
    · exact le_rfl
    · exact le_rfl
    · simpa using hprev s
  · by_cases hs0 : s = 0
    · simp [swLUnionTailStepReal, hs0]
    · by_cases hbad : r < s ∨ r < L
      · simp [swLUnionTailStepReal, hs0, hbad]
      · push Not at hbad
        rw [swLUnionTailStepReal_eq_convex (by omega) hbad.1 hL1 hbad.2 tailP prev₁,
          swLUnionTailStepReal_eq_convex (by omega) hbad.1 hL1 hbad.2 tailP prev₂]
        set mS := min L s; set c := fun j ↦ swLGReal L r tailP j (s - j); have hle1 :=
          htail_le_one_of_anti htail_anti htail1
        have hw0 : 0 ≤ 1 - c 1 := sub_nonneg.2 (swLGReal_one_le_one hle1 (s - 1)); have hw_end : 0 ≤
          c mS := swLGReal_nonneg htail0 mS (s - mS); refine add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hprev s) hw0) ?_) (mul_le_mul_of_nonneg_left (hprev (s - mS))
          hw_end); refine Finset.sum_le_sum fun j hj ↦ ?_; rw [Finset.mem_Ico] at hj; have hjs : j +
          1 ≤ s := hj.2.trans_le (Nat.min_le_right L s); have hsh : s - (j + 1) + 1 = s - j :=
          (by omega)
        have hcj : c (j + 1) ≤ c j := by
          dsimp [c]; rw [← hsh]; exact swLGReal_succ_le_shift htail0 htail_anti hj.1 (s - (j + 1))
        exact mul_le_mul_of_nonneg_left (hprev (s - j)) (sub_nonneg.2 hcj)
theorem swLUnionTailReal_bounds_and_anti {L r : ℕ} {tailP : ℕ → ℝ} (htail0 : ∀ c ∈ Finset.Icc 1 L, 0
  ≤ tailP c) (htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c + 1) ≤ tailP c) (htail1 : tailP 1 ≤ 1)
  : ∀ t : ℕ, swLUnionTailReal L r tailP t 0 = 1 ∧ (∀ s : ℕ, 0 ≤ swLUnionTailReal L r tailP t s ∧
  swLUnionTailReal L r tailP t s ≤ 1) ∧ (∀ s : ℕ, r < s → s ≠ 0 → swLUnionTailReal L r tailP t s =
  0) ∧ (∀ s : ℕ, swLUnionTailReal L r tailP t (s + 1) ≤ swLUnionTailReal L r tailP t s)
  | 0 => by
    refine ⟨by simp [swLUnionTailReal], fun s ↦ ?_, fun s _ hs0 ↦ by simp [swLUnionTailReal, hs0],
      fun s ↦ ?_⟩
    · by_cases hs : s = 0 <;> simp [swLUnionTailReal, hs]
    · by_cases hs : s = 0 <;> simp [swLUnionTailReal, hs]
  | t + 1 => by
    rcases swLUnionTailReal_bounds_and_anti htail0 htail_anti htail1 t with ⟨h0, hbnd, hgt, hanti⟩
    set prev := swLUnionTailReal L r tailP t; have h0_next : swLUnionTailReal L r tailP (t + 1) 0 =
      1 := (by simp [swLUnionTailReal, swLUnionTailStepReal])
    have hbnd_next : ∀ s : ℕ, 0 ≤ swLUnionTailStepReal L r tailP prev s ∧ swLUnionTailStepReal L r
      tailP prev s ≤ 1 := by
      intro s; by_cases hs0 : s = 0
      · simp [swLUnionTailStepReal, hs0]
      · by_cases hbad : r < s ∨ r < L
        · simp [swLUnionTailStepReal, hs0, hbad]
        · have hm0 := swLUnionTailStepReal_mono_prev (r := r) htail0 htail_anti htail1 (prev₁ := fun
            _ ↦ 0) (prev₂ := prev) (fun k ↦ (hbnd k).1) s; have hm1 :=
            swLUnionTailStepReal_mono_prev (r := r) htail0 htail_anti htail1 (prev₁ := prev) (prev₂
            := fun _ ↦ 1) (fun k ↦ (hbnd k).2) s; have hc0 : swLUnionTailStepReal L r tailP (fun _ ↦
            0) s = 0 := (by simp [swLUnionTailStepReal, hs0, hbad])
          have hc1 : swLUnionTailStepReal L r tailP (fun _ ↦ 1) s = 1 :=
            (by simp [swLUnionTailStepReal, hs0, hbad]); exact ⟨hc0.symm.trans_le hm0, hm1.trans_eq
            hc1⟩
    have hgt_next : ∀ s : ℕ, r < s → s ≠ 0 → swLUnionTailStepReal L r tailP prev s = 0 :=
      (by intro s hrs hs0; simp [swLUnionTailStepReal, hs0, hrs]); refine ⟨h0_next, hbnd_next,
      hgt_next, fun s ↦ ?_⟩; change swLUnionTailStepReal L r tailP prev (s + 1) ≤
      swLUnionTailStepReal L r tailP prev s; by_cases hs0 : s = 0
    · subst hs0; simpa [swLUnionTailStepReal] using (hbnd_next 1).2
    · by_cases hrs : r ≤ s
      · rw [hgt_next (s + 1) (by omega) (by omega)]; exact (hbnd_next s).1
      · by_cases hrL : r < L
        · simp [swLUnionTailStepReal, hs0, hrL]
        · rcases Nat.eq_zero_or_pos L with rfl | hL1
          · simp only [swLUnionTailStepReal, show s + 1 ≠ 0 by omega, hs0, ↓reduceIte,
              show ¬(r < s + 1 ∨ r < 0) by omega, show ¬(r < s ∨ r < 0) by omega,
              Nat.zero_min, Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty,
              add_zero]
            exact hanti s
          · push Not at hrs hrL
            unfold swLUnionTailStepReal
            simp only [show ¬(s + 1 = 0) by omega, show ¬(r < s + 1 ∨ r < L) by omega,
              hs0, show ¬(r < s ∨ r < L) by omega, ↓reduceIte]
            set m1 := min L (s + 1); set m0 := min L s
            have hm1_ge1 : 1 ≤ m1 := le_min hL1 (by omega); have hm1_sub : m1 - 1 ≤ m0 :=
              (by dsimp [m1, m0]; omega); rw [sum_Icc_bot hm1_ge1, show s + 1 - 1 = s by omega]
            have hle1 := htail_le_one_of_anti htail_anti htail1
            have hg1_le1 : swLGReal L r tailP 1 s ≤ 1 := swLGReal_one_le_one hle1 s
            have hp1 : prev (s + 1) + swLGReal L r tailP 1 s * (prev s - prev (s + 1)) ≤ prev s
              := by
              have hnonneg : 0 ≤ (1 - swLGReal L r tailP 1 s) * (prev s - prev (s + 1)) :=
                mul_nonneg (sub_nonneg.2 hg1_le1) (sub_nonneg.2 (hanti s)); linarith
            have hreidx : ∑ j ∈ Finset.Icc 2 m1, swLGReal L r tailP j (s + 1 - j) * (prev (s + 1 -
              j) - prev (s + 1 - j + 1)) = ∑ k ∈ Finset.Icc 1 (m1 - 1), swLGReal L r tailP (k + 1)
              (s - k) * (prev (s - k) - prev (s - k + 1)) := by
              by_cases hm2 : 2 ≤ m1
              · rw [sum_Icc_eq_sum_range_local, sum_Icc_eq_sum_range_local, show m1 + 1 - 2 = m1 - 1
                  + 1 - 1 by omega]; refine Finset.sum_congr rfl fun d _ ↦ ?_
                rw [show 2 + d = (1 + d) + 1 by omega,
                  show s + 1 - ((1 + d) + 1) = s - (1 + d) by omega]
              · simp [Finset.Icc_eq_empty_of_lt (by omega : m1 < 2), Finset.Icc_eq_empty_of_lt
                  (by omega : m1 - 1 < 1)]
            have hrest : ∑ k ∈ Finset.Icc 1 (m1 - 1), swLGReal L r tailP (k + 1) (s - k) * (prev (s
              - k) - prev (s - k + 1)) ≤ ∑ k ∈ Finset.Icc 1 m0, swLGReal L r tailP k (s - k) * (prev
              (s - k) - prev (s - k + 1)) := by
              refine (Finset.sum_le_sum fun k hk ↦ ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.Icc_subset_Icc_right hm1_sub) fun k _ _ ↦ mul_nonneg (swLGReal_nonneg htail0
                k (s - k)) (sub_nonneg.2 (hanti (s - k)))); rw [Finset.mem_Icc] at hk
              exact mul_le_mul_of_nonneg_right (swLGReal_anti_j htail0 htail_anti hk.1 (s - k))
                (sub_nonneg.2 (hanti (s - k)))
            linarith [hp1, hreidx, hrest]
theorem swLUnionTailReal_mono_copies {L r : ℕ} {tailP : ℕ → ℝ} (htail0 : ∀ c ∈ Finset.Icc 1 L, 0 ≤
  tailP c) (htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c + 1) ≤ tailP c) (htail1 : tailP 1 ≤ 1)
  {mEff m : ℕ} (hm : mEff ≤ m) (s : ℕ) : swLUnionTailReal L r tailP mEff s ≤ swLUnionTailReal L r
  tailP m s := by
  have hstep : ∀ t : ℕ, swLUnionTailReal L r tailP t s ≤ swLUnionTailReal L r tailP (t + 1) s := by
    intro t; rcases swLUnionTailReal_bounds_and_anti htail0 htail_anti htail1 t with ⟨_, hbnd, hgt,
      hanti⟩
    change swLUnionTailReal L r tailP t s ≤ swLUnionTailStepReal L r tailP (swLUnionTailReal L r
      tailP t) s; unfold swLUnionTailStepReal; by_cases hs0 : s = 0
    · subst hs0; simp [(swLUnionTailReal_bounds_and_anti htail0 htail_anti htail1 t).1]
    · simp only [hs0, ↓reduceIte]; by_cases hbad : r < s ∨ r < L
      · simp only [hbad, ↓reduceIte]; rcases hbad with hrs | hrL
        · rw [hgt s hrs hs0]
        · have hz_rL : ∀ k : ℕ, swLUnionTailReal L r tailP k s = 0 := by
            intro k
            induction k with
            | zero => simp [swLUnionTailReal, hs0]
            | succ k' _ => simp [swLUnionTailReal, swLUnionTailStepReal, hs0, hrL]
          rw [hz_rL t]
      · simp only [hbad, ↓reduceIte]; refine le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ ?_)
        exact mul_nonneg (swLGReal_nonneg htail0 j (s - j)) (sub_nonneg.2 (hanti (s - j)))
  induction hm with
  | refl => exact le_rfl | step _ ih => exact ih.trans (hstep _)
/-! ### 7.3 WHNF-Forced `10^12`-Scale `swLUnionTailLbList` & Lower-Bound Soundness -/
/-- Precomputed integer hypergeometric numerator row `[k_1,..., k_{min L s}]` at threshold
  `s`. -/
abbrev SwLKRow : Type := List ℤ
/-- WHNF-forcing wrapper for a list of `ℤ` values. -/
def forceListId {α : Type*} : List ℤ → (List ℤ → α) → α
  | [], k => k []
  | x :: xs, k => withForcedInt x fun x' ↦ forceListId xs fun xs' ↦ k (x' :: xs')
theorem forceListId_eq {α : Type*} (xs : List ℤ) (k : List ℤ → α) : forceListId xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => unfold forceListId; rw [withForcedInt_eq, ih]
/-- WHNF-forcing wrapper for precomputed `SwLKRow` tables. -/
def withForcedGrid {α : Type*} : List SwLKRow → (List SwLKRow → α) → α
  | [], k => k []
  | r :: rs, k => forceListId r fun r' ↦ withForcedGrid rs fun rs' ↦ k (r' :: rs')
theorem withForcedGrid_eq {α : Type*} (rs : List SwLKRow) (k : List SwLKRow → α) : withForcedGrid rs
  k = k rs := by
  induction rs generalizing k with
  | nil => rfl
  | cons r rs ih => unfold withForcedGrid; rw [forceListId_eq, ih]
/-- Integer numerator `k_j(u)` of `swLGReal L r (tailLbs / 10^9) j u` over `10^9 * r^(L)`. -/
def swLKNumInt (L r : ℕ) (tailLbs : List ℤ) (j u : ℕ) : ℤ :=
  withForcedNat (r - u) fun wJ ↦
    (List.range (L + 1 - j)).foldl (fun acc dC ↦
      withForcedNat (j + dC) fun c ↦
        acc + tailLbs.getD (c - 1) 0 *
          ((swLBinomSmall (c - 1) (j - 1) * wJ.descFactorial j *
            u.descFactorial (c - j) * (r - c).descFactorial (L - c) : ℕ) : ℤ)) 0
/-- Precomputed row `[k_1,..., k_{min L s}]` at threshold `s`. -/
def swLKRowBuild (L r : ℕ) (tailLbs : List ℤ) (s : ℕ) : SwLKRow :=
  if s == 0 then []
  else (List.range (min L s)).map fun jIdx ↦ swLKNumInt L r tailLbs (jIdx + 1) (s - (jIdx + 1))
/-- One WHNF-forced `10^12`-scale integer union-tail step up to active cap `curMax`. -/
def swLUnionTailStepInt (r : ℕ) (den : ℤ) (kByS : List SwLKRow) (curMax : ℕ)
    (prev : List ℤ) : List ℤ :=
  forceListId ((List.range (r + 1)).map fun s ↦
    if s == 0 then swUnionScale
    else if curMax < s then 0
    else
      forceListId (kByS.getD s []) fun row ↦
        withForcedInt ((List.range row.length).foldl (fun acc jIdx ↦
          withForcedNat (jIdx + 1) fun j ↦
            acc + row.getD jIdx 0 * (prev.getD (s - j) 0 - prev.getD (s - j + 1) 0))
          (den * prev.getD s 0)) fun num ↦
          num / den) id
/-- `10^12`-scale lower-bound list `[T(m, 0),..., T(m, r)]` matching `SwLIntChecker`
  bit-for-bit. -/
def swLUnionTailLbList (L r : ℕ) (tailLbs : List ℤ) (mCopies : ℕ) : List ℤ :=
  withForcedInt (swScale * (r.descFactorial L : ℤ)) fun den ↦
    withForcedNat (min (mCopies * L) r) fun maxS ↦
      withForcedGrid ((List.range (maxS + 1)).map (swLKRowBuild L r tailLbs)) fun kByS ↦
        forceListId (swUnionScale :: List.replicate r (0 : ℤ)) fun init ↦
          (List.range mCopies).foldl (fun prev tIdx ↦
            swLUnionTailStepInt r den kByS (min ((tIdx + 1) * L) maxS) prev) init
theorem swLKNumInt_div_eq_swLGReal {L r : ℕ} (hLr : L ≤ r) (tailLbs : List ℤ) {j u : ℕ} (hj1 : 1 ≤
  j) (hjL : j ≤ L) (hur : u < r) : (swLKNumInt L r tailLbs j u : ℝ) / ((swScale * (r.descFactorial L
  : ℤ) : ℤ) : ℝ) = swLGReal L r (fun c ↦ ((tailLbs.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ)) j u :=
  by
  have hS : (swScale : ℝ) ≠ 0 := (by unfold swScale; norm_num); unfold swLKNumInt swLGReal
  rw [withForcedNat_eq]; simp only [show ¬(r < L ∨ j = 0 ∨ L < j ∨ r ≤ u)
    by omega, ↓reduceIte, withForcedNat_eq]
  rw [foldl_range_add_eq_sum]; push_cast; rw [sum_Icc_eq_sum_range_local]
  have hsum : (∑ dC ∈ Finset.range (L + 1 - j), ((tailLbs.getD (j + dC - 1) 0 : ℝ) * ((swLBinomSmall
    (j + dC - 1) (j - 1) : ℝ) * ((r - u).descFactorial j : ℝ) * (u.descFactorial (j + dC - j) : ℝ) *
    ((r - (j + dC)).descFactorial (L - (j + dC)) : ℝ)))) = (swScale : ℝ) * ∑ dC ∈ Finset.range (L +
    1 - j), (((tailLbs.getD (j + dC - 1) 0 : ℝ) / (swScale : ℝ)) * (((j + dC - 1).choose (j - 1) :
    ℝ) * ((r - u).descFactorial j : ℝ) * (u.descFactorial (j + dC - j) : ℝ) * ((r - (j +
    dC)).descFactorial (L - (j + dC)) : ℝ))) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun dC _ ↦ ?_; rw [swLBinomSmall_eq_choose];
      field_simp [hS]
  rw [hsum, mul_div_mul_left _ _ hS]
theorem tailLbs_scaled_props {L : ℕ} (hL1 : 1 ≤ L) {tailLbs : List ℤ} (htl0_le : tailLbs.getD 0 0 ≤
  swScale) (htlL0 : 0 ≤ tailLbs.getD (L - 1) 0) (htl_mono : ∀ i : ℕ, i + 1 < L → tailLbs.getD (i +
  1) 0 ≤ tailLbs.getD i 0) :
    let tailPL : ℕ → ℝ := fun c ↦ ((tailLbs.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ)
    (∀ c ∈ Finset.Icc 1 L, 0 ≤ tailPL c) ∧ (∀ c : ℕ, 1 ≤ c → c < L → tailPL (c + 1) ≤ tailPL c) ∧
      tailPL 1 ≤ 1 := by
  intro tailPL; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hge_last : ∀ i < L, tailLbs.getD (L - 1) 0 ≤ tailLbs.getD i 0 := by
    intro i hi; obtain ⟨d, hd⟩ : ∃ d, i + d = L - 1 := ⟨L - 1 - i, by omega⟩; rw [← hd]
    induction d generalizing i with
    | zero => simp
    | succ d' ih =>
      have h1 := ih (i + 1) (by omega) (by omega)
      rw [show i + 1 + d' = i + (d' + 1) by omega] at h1; exact h1.trans (htl_mono i (by omega))
  refine ⟨fun c hc ↦ ?_, fun c hc1 hcL ↦ ?_, ?_⟩
  · rw [Finset.mem_Icc] at hc
    exact div_nonneg (by exact_mod_cast htlL0.trans (hge_last (c - 1) (by omega))) hS.le
  · have hm := htl_mono (c - 1) (by omega); rw [show c - 1 + 1 = c by omega] at hm
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) hS.le
  · dsimp [tailPL]; rw [div_le_one hS]; exact_mod_cast htl0_le
theorem swLUnionTailLb_le_real {L r : ℕ} (hL1 : 1 ≤ L) (hLr : L ≤ r) {tailLbs : List ℤ} {tailP : ℕ →
  ℝ} (htl0_le : tailLbs.getD 0 0 ≤ swScale) (htlL0 : 0 ≤ tailLbs.getD (L - 1) 0) (htl_mono : ∀ i :
  ℕ, i + 1 < L → tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0) (htl_le : ∀ c ∈ Finset.Icc 1 L,
  ((tailLbs.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤ tailP c) (htail0 : ∀ c ∈ Finset.Icc 1 L, 0 ≤
  tailP c) (htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c + 1) ≤ tailP c) (htail1 : tailP 1 ≤ 1)
  (mCopies s : ℕ) : (((swLUnionTailLbList L r tailLbs mCopies).getD s 0 : ℤ) : ℝ) / (swUnionScale :
  ℝ) ≤ swLUnionTailReal L r tailP mCopies s := by
  have hU : (0 : ℝ) < (swUnionScale : ℝ) := (by unfold swUnionScale; norm_num)
  have hS_i : (0 : ℤ) < swScale := (by unfold swScale; norm_num); set den : ℤ := swScale *
    (r.descFactorial L : ℤ)
  have hden_pos : 0 < den := mul_pos hS_i (by exact_mod_cast Nat.descFactorial_pos.2 hLr)
  set maxS : ℕ := min (mCopies * L) r
  set kByS : List SwLKRow := (List.range (maxS + 1)).map (swLKRowBuild L r tailLbs)
  set init : List ℤ := swUnionScale :: List.replicate r (0 : ℤ)
  set tailPL : ℕ → ℝ := fun c ↦ ((tailLbs.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ)
  rcases tailLbs_scaled_props hL1 htl0_le htlL0 htl_mono with ⟨htailPL0, htailPL_anti, htailPL1⟩
  unfold swLUnionTailLbList; rw [withForcedInt_eq, withForcedNat_eq, withForcedGrid_eq,
    forceListId_eq]; change ((((List.range mCopies).foldl (fun prev tIdx ↦ swLUnionTailStepInt r den
    kByS (min ((tIdx + 1) * L) maxS) prev) init).getD s 0 : ℤ) : ℝ) / (swUnionScale : ℝ) ≤
    swLUnionTailReal L r tailP mCopies s
  suffices hind : ∀ t ≤ mCopies,
      let cur := (List.range t).foldl (fun prev tIdx ↦
        swLUnionTailStepInt r den kByS (min ((tIdx + 1) * L) maxS) prev) init
      cur.length = r + 1 ∧
      ∀ k : ℕ, ((cur.getD k 0 : ℤ) : ℝ) / (swUnionScale : ℝ) ≤ swLUnionTailReal L r tailP t k from
    (hind mCopies le_rfl).2 s
  intro t ht
  induction t with
  | zero =>
      refine ⟨by simp [init], fun k ↦ ?_⟩; rcases k with _ | k'
      · simp [init, swLUnionTailReal, div_self hU.ne']
      · simp [init, swLUnionTailReal, List.getD_eq_getElem?_getD]
        by_cases hk : k' < r <;> simp [hk]
  | succ t' ih =>
      rcases ih (by omega) with ⟨hlen, hle_prev⟩; dsimp only at hlen hle_prev ⊢
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]; set prevList :=
        (List.range t').foldl (fun prev tIdx ↦ swLUnionTailStepInt r den kByS (min ((tIdx + 1) * L)
        maxS) prev) init; set curMax := min ((t' + 1) * L) maxS; refine ⟨?_, fun k ↦ ?_⟩
      · rw [swLUnionTailStepInt, forceListId_eq, id_eq]; simp
      · rw [swLUnionTailStepInt, forceListId_eq, id_eq]; rcases swLUnionTailReal_bounds_and_anti (r
          := r) htail0 htail_anti htail1 (t' + 1) with ⟨_, hbnd_next, _, _⟩
        rcases swLUnionTailReal_bounds_and_anti (r := r) htail0 htail_anti htail1 t' with ⟨_, _, _,
          hanti_prev⟩; by_cases hk_lt : k < r + 1
        · have hget : ((List.range (r + 1)).map fun s ↦ if s == 0 then swUnionScale else if curMax <
            s then 0 else forceListId (kByS.getD s []) fun row ↦ withForcedInt ((List.range
            row.length).foldl (fun acc jIdx ↦ withForcedNat (jIdx + 1) fun j ↦ acc + row.getD jIdx 0
            * (prevList.getD (s - j) 0 - prevList.getD (s - j + 1) 0)) (den * prevList.getD s 0))
            fun num ↦ num / den).getD k 0 = if k == 0 then swUnionScale else if curMax < k then 0
            else forceListId (kByS.getD k []) fun row ↦ withForcedInt ((List.range row.length).foldl
            (fun acc jIdx ↦ withForcedNat (jIdx + 1) fun j ↦ acc + row.getD jIdx 0 * (prevList.getD
            (k - j) 0 - prevList.getD (k - j + 1) 0)) (den * prevList.getD k 0)) fun num ↦ num / den
            := (by simp [List.getD_eq_getElem?_getD, hk_lt]); rw [hget]; by_cases hk0 : k = 0
          · subst hk0; simp [swLUnionTailReal, swLUnionTailStepReal, div_self hU.ne']
          · simp only [beq_false_of_ne hk0, Bool.false_eq_true, ↓reduceIte]
            by_cases hcur : curMax < k
            · simp only [hcur, ↓reduceIte, Int.cast_zero, zero_div]; exact (hbnd_next k).1
            · simp only [hcur, ↓reduceIte, forceListId_eq, withForcedInt_eq, withForcedNat_eq]
              have hk_maxS : k ≤ maxS := (by have : curMax ≤ maxS := Nat.min_le_right _ _; omega)
              have hk_lt_maxS1 : k < maxS + 1 := (by omega)
              have hrow_eq : kByS.getD k [] = swLKRowBuild L r tailLbs k :=
                (by simp [kByS, List.getD_eq_getElem?_getD, hk_lt_maxS1])
              rw [hrow_eq]; unfold swLKRowBuild; simp only [beq_false_of_ne hk0, Bool.false_eq_true,
                ↓reduceIte, List.length_map, List.length_range]
              set prevL : ℕ → ℝ := fun idx ↦ ((prevList.getD idx 0 : ℤ) : ℝ) / (swUnionScale : ℝ)
              set prevR : ℕ → ℝ := swLUnionTailReal L r tailP t'
              have hstep3 : (((((List.range (min L k)).foldl (fun acc jIdx ↦ acc + ((List.range (min
                L k)).map fun jIdx ↦ swLKNumInt L r tailLbs (jIdx + 1) (k - (jIdx + 1))).getD jIdx 0
                * (prevList.getD (k - (jIdx + 1)) 0 - prevList.getD (k - (jIdx + 1) + 1) 0)) (den *
                prevList.getD k 0)) / den : ℤ) : ℝ) / (swUnionScale : ℝ)) ≤ swLUnionTailStepReal L r
                tailPL prevL k := by
                have hfold_sh : ∀ (n : ℕ) (initA : ℤ) (g : ℕ → ℤ), (List.range n).foldl (fun acc i ↦
                  acc + g i) initA = initA + ∑ i ∈ Finset.range n, g i := by
                  intro n initA g
                  induction n with
                  | zero => simp
                  | succ n' ihn =>
                      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ihn,
                        Finset.sum_range_succ, add_assoc]
                rw [hfold_sh]; refine (div_le_div_of_nonneg_right (ediv_pos_le_real _ den hden_pos)
                  hU.le).trans_eq ?_; unfold swLUnionTailStepReal; simp only [hk0, show ¬(r < k ∨ r
                  < L) by omega, ↓reduceIte]; have hden_r : (den : ℝ) ≠ 0 :=
                  (by exact_mod_cast hden_pos.ne'); have hS_r : (swScale : ℝ) ≠ 0 :=
                  (by unfold swScale; norm_num); have hdr : (r.descFactorial L : ℝ) ≠ 0 :=
                  (by exact_mod_cast (Nat.descFactorial_pos.2 hLr).ne'); push_cast
                rw [add_div, add_div, mul_div_cancel_left₀ _ hden_r, sum_div_const, sum_div_const,
                  sum_Icc_eq_sum_range_local, show min L k + 1 - 1 = min L k by omega]; congr 1
                refine Finset.sum_congr rfl fun jIdx hjIdx ↦ ?_; rw [Finset.mem_range] at hjIdx
                have hmget : ((List.range (min L k)).map fun i ↦ swLKNumInt L r tailLbs (i + 1) (k -
                  (i + 1))).getD jIdx 0 = swLKNumInt L r tailLbs (jIdx + 1) (k - (jIdx + 1)) :=
                  (by simp [List.getD_eq_getElem?_getD, hjIdx]); rw [hmget, show 1 + jIdx = jIdx + 1
                  by omega]; have hj1 : 1 ≤ jIdx + 1 := (by omega); have hjL : jIdx + 1 ≤ L :=
                  (by have : min L k ≤ L := Nat.min_le_left L k; omega); have hur : k - (jIdx + 1) <
                  r := (by omega); have hk_eq := swLKNumInt_div_eq_swLGReal hLr tailLbs hj1 hjL hur
                dsimp [den] at hden_r ⊢; dsimp [prevL]; push_cast at hk_eq ⊢; rw [← hk_eq]
                field_simp [hS_r, hdr, hU.ne']
              -- Step 2: `prevL ≤ prevR` via nonnegative convex weights on `tailPL`
              have hstep2 : swLUnionTailStepReal L r tailPL prevL k ≤ swLUnionTailStepReal L r
                tailPL prevR k := swLUnionTailStepReal_mono_prev htailPL0 htailPL_anti htailPL1
                hle_prev k
              -- Step 1: `tailPL ≤ tailP` via antitonicity of `prevR`
              have hstep1 : swLUnionTailStepReal L r tailPL prevR k ≤ swLUnionTailStepReal L r tailP
                prevR k := by
                unfold swLUnionTailStepReal; simp only [hk0, show ¬(r < k ∨ r < L)
                  by omega, ↓reduceIte]; refine add_le_add le_rfl (Finset.sum_le_sum fun j _ ↦ ?_)
                exact mul_le_mul_of_nonneg_right (swLGReal_mono_tailP htl_le j (k - j))
                  (sub_nonneg.2 (hanti_prev (k - j)))
              exact (hstep3.trans hstep2).trans hstep1
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          simp only [Option.getD_none, Int.cast_zero, zero_div]; exact (hbnd_next k).1
/-! ### 7.4 `MultiSW_L` Stage Cascade Checker & Soundness -/
/-- Verify `0 ≤ vTable 0` and `vTable j ≤ vTable (j + 1)` for all `j < kMax`. -/
def checkSwLTableMono (kMax : ℕ) (vTable : ℕ → ℤ) : Bool :=
  decide (0 ≤ vTable 0) &&
    (List.range kMax).all fun j ↦ decide (vTable j ≤ vTable (j + 1))
theorem checkSwLTableMono_sound {kMax : ℕ} {vTable : ℕ → ℤ} (h : checkSwLTableMono kMax vTable =
  true) : 0 ≤ vTable 0 ∧ ∀ j : ℕ, j < kMax → vTable j ≤ vTable (j + 1) := by
  unfold checkSwLTableMono at h; simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h; exact h
theorem sum_range_mul_sub_eq_sum_Ico (N : ℕ) (q f : ℕ → ℝ) : ∑ u ∈ Finset.range (N + 1), q u * (f 0
  - f u) = ∑ s ∈ Finset.range N, (∑ u ∈ Finset.Ico (s + 1) (N + 1), q u) * (f s - f (s + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hsplit : ∑ s ∈ Finset.range N, (∑ u ∈ Finset.Ico (s + 1) (N + 2), q u) * (f s - f (s + 1))
      = (∑ s ∈ Finset.range N, (∑ u ∈ Finset.Ico (s + 1) (N + 1), q u) * (f s - f (s + 1))) + ∑ s ∈
      Finset.range N, q (N + 1) * (f s - f (s + 1)) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun s hs ↦ ?_; have hsN : s < N :=
        Finset.mem_range.1 hs; rw [Finset.sum_Ico_succ_top (by omega : s + 1 ≤ N + 1)]; ring
    have hlast : ∑ u ∈ Finset.Ico (N + 1) (N + 2), q u = q (N + 1) := by
      rw [Finset.sum_Ico_succ_top (le_refl (N + 1)), Finset.Ico_self, Finset.sum_empty, zero_add]
    have htele : ∑ s ∈ Finset.range N, q (N + 1) * (f s - f (s + 1)) = q (N + 1) * (f 0 - f N) :=
      (by rw [← Finset.mul_sum, Finset.sum_range_sub']); rw [hsplit, hlast, htele]; ring
/-- Pure-integer `mEff`-copy `MultiSW_L` Bellman step checker (`n ≥ 96`, scale `vScale`). -/
def checkMultiSWLStep (L mEff r numPulses tauNum tauDen verCalls : ℕ)
    (tailLbs : List ℤ) (vScale : ℤ) (vTable : ℕ → ℤ) : Bool :=
  decide (2 ≤ L ∧ L ≤ 8 ∧ 1 ≤ mEff ∧ L ≤ r ∧ r ≤ 1024 ∧ 1 ≤ numPulses ∧
    0 < tauNum ∧ 0 < tauDen ∧ 0 < vScale ∧ tailLbs.length = L ∧
    0 ≤ tailLbs.getD (L - 1) 0 ∧ tailLbs.getD 0 0 ≤ swScale) &&
  ((List.range (L - 1)).all fun i ↦ decide (tailLbs.getD (i + 1) 0 ≤ tailLbs.getD i 0)) &&
  forceListId (swLUnionTailLbList L r tailLbs mEff) fun tailL ↦
    withForcedNat (min (L * mEff) r) fun maxS ↦
      withForcedInt ((List.range maxS).foldl (fun acc s ↦
        withForcedInt (acc + tailL.getD (s + 1) 0 * (vTable (r - s) - vTable (r - s - 1))) id)
        0) fun abSum ↦
        withForcedInt (3 * (numPulses : ℤ) + 2 * (verCalls : ℤ)) fun bNum ↦
          withForcedInt (abSum * swBden49 - swUnionScale * vScale * bNum) fun rem ↦
            decide (0 < tailL.getD 1 0 ∧ 0 ≤ rem ∧
              ((numPulses : ℤ) * (tauNum : ℤ) * swUnionScale * vScale * swBden49) ^ 2 ≤
                4 * ((tauDen : ℤ) ^ 2) * (r : ℤ) * (rem ^ 2))
private theorem checkMultiSWLStage_inner {L mEff m n r rMin rMax tauNum tauDen : ℕ} {ratios : List
    IvInt} {trigIvs : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ}
    {survUb vScale : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hmEff
    : mEff ≤ m) (hMono : ∀ j : ℕ, j < r → vTable j ≤ vTable (j + 1)) (hbkt : checkSwLBucketCert L
    rMin rMax tauNum tauDen ratios trigIvs pulses tailLbs survUb = true) (hstep : checkMultiSWLStep
    L mEff r pulses.length tauNum tauDen L tailLbs vScale vTable = true) : ∃ (hL2 : 2 ≤ L), L ≤ 8 ∧
    L ≤ r ∧ ∀ (M : Fin (2 * L) → Fin (2 * L) → ℝ), IsValidSwLOverlap M →
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
  rcases checkSwLBucketCert_sound hn96 hmin hmax hbkt with ⟨hL2, hL8, hLr, hr1024, _, _, hp_val, _,
    _, _, htl0_le, htlL0, htl_mono, hbkt_M⟩; unfold checkMultiSWLStep at hstep
  simp only [forceListId_eq, withForcedNat_eq, withForcedInt_eq, id_eq, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hstep; rcases hstep with ⟨⟨⟨_, _, hm1,
    _, _, hp_pos, htau, hden, hvsc_pos, _, _, _⟩, _⟩, htail1_pos, hrem0, hsq_ineq⟩; refine ⟨hL2,
    hL8, hLr, ?_⟩; intro M hM K_blk cs out p tailP V q hq0 hq_sum hq_dom
  rcases hbkt_M M hM with ⟨_, _, htail_lbs⟩
  have hcs_unit : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun w ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum hL2 hcs_unit pulses hp_val with ⟨hcons, hcum0, _, _⟩
  have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg hL2 M out.1 hcum0 h
  have hp_sum1 : ∑ h ∈ Finset.range (L + 1), p h = 1 := swLAttemptProbReal_sum_one hL2 hM hcons
  have htail0 : ∀ c ∈ Finset.Icc 1 L, 0 ≤ tailP c := fun c _ ↦ Finset.sum_nonneg fun h _ ↦ hp_nn h
  have htail_anti : ∀ c : ℕ, 1 ≤ c → c < L → tailP (c + 1) ≤ tailP c := fun c _ _ ↦
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
  have hsqrtN_pos : 0 < √N := (by dsimp [N]; positivity)
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
    refine Finset.sum_congr rfl fun s _ ↦ ?_; field_simp [hU.ne', hvsc_r.ne']
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
theorem checkMultiSWLStage_sound {L mEff m n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} {pulses : List (SwLPulseRat L)} {tailLbs : List ℤ} {survUb vScale
  : ℤ} {vTable : ℕ → ℤ} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hmEff : mEff ≤ m)
  (hMono : ∀ j : ℕ, j < r → vTable j ≤ vTable (j + 1)) (hunit : pulses.all (fun p ↦ swLPulseValid p
  && decide (p.vNum = 0)) = true) (hbkt : checkSwLBucketCert L rMin rMax tauNum tauDen ratios
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
  rcases checkMultiSWLStage_inner hn96 hmin hmax hmEff hMono hbkt hstep with ⟨hL2, hL8, hLr, hmain⟩
  exact ⟨hL2, hL8, hLr, hunit, hmain⟩
/-! ### 7.5 Dyadic Grid Relative-Cost Checkers & Kernel Smoke Certificate -/
/-- Certified lower bound `⌊(π / 4) * 10^12⌋ = 785398163397`. -/
def swLPi4Lo12 : ℕ := 785398163397
/-- Certified `10^12`-scale lower bounds on `∑_{r=1}^{2^kIdx} 1 / √r` for `0 ≤ kIdx ≤ 10`. -/
def swLHarmPow2 : ℕ → ℕ
  | 0 => 1000000000000
  | 1 => 1707106781186
  | 2 => 2784457050375
  | 3 => 4371436799939
  | 4 => 6663994608230
  | 5 => 9941512173863
  | 6 => 14602064112190
  | 7 => 21211227890778
  | 8 => 30570885318540
  | 9 => 43816572977247
  | 10 => 62555269219112
  | _ => 0
/-- Certified `10^12`-scale upper bounds on `√(2^mIdx)` for `0 ≤ mIdx ≤ 10`. -/
def swLSqrtMUp12 : ℕ → ℕ
  | 0 => 1000000000000
  | 1 => 1414213562374
  | 2 => 2000000000000
  | 3 => 2828427124747
  | 4 => 4000000000000
  | 5 => 5656854249493
  | 6 => 8000000000000
  | 7 => 11313708498985
  | 8 => 16000000000000
  | 9 => 22627416997970
  | 10 => 32000000000000
  | _ => 0
/-- General `vScale` relative-cost checker against `(π / 4) * H_{1/2}(2^kIdx) * √(2^n /
  2^mIdx)`. -/
def checkSwLRelCostScaled (mIdx kIdx : ℕ) (vTop vScale : ℤ) (relNum relDen : ℕ) : Bool :=
  decide (mIdx ≤ 10 ∧ kIdx ≤ 10 ∧ 0 < vTop ∧ 0 < vScale ∧ 0 < relNum ∧ 0 < relDen ∧
    vTop * (swLSqrtMUp12 mIdx : ℤ) * swUnionScale * (relDen : ℤ) ≤
      vScale * (swLPi4Lo12 : ℤ) * (swLHarmPow2 kIdx : ℤ) * (relNum : ℤ))
/-- `10^16`-scale (`multiUnitScale`) relative-cost cell checker matching
  `p07_hdist2l_checks.py`. -/
def checkSwLRelCostCell (mIdx kIdx : ℕ) (vTop16 : ℤ) (relNum relDen : ℕ) : Bool :=
  checkSwLRelCostScaled mIdx kIdx vTop16 multiUnitScale relNum relDen
theorem swLSqrtMUp12_sq_ge_cert : ((List.range 11).all fun mIdx ↦ decide (2 ^ mIdx *
  1000000000000000000000000 ≤ (swLSqrtMUp12 mIdx) ^ 2)) = true := by
  rw [List.all_eq_true]; intro mIdx hm; rw [List.mem_range] at hm
  rw [decide_eq_true_eq]; match mIdx with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => simp only [swLSqrtMUp12]; norm_num
  | _ + 11 => omega
theorem swLHarmPow2_eq_foldl_cert : ((List.range 11).all fun kIdx ↦ decide (swLHarmPow2 kIdx =
  (List.range (2 ^ kIdx)).foldl (fun acc i ↦ acc + Nat.sqrt (1000000000000000000000000 / (i + 1)))
  0)) = true := by decide +kernel
theorem swLHarmPow2_le_real {kIdx : ℕ} (hk : kIdx ≤ 10) : (swLHarmPow2 kIdx : ℝ) / (swUnionScale :
  ℝ) ≤ ∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ) := by
  have hcert := swLHarmPow2_eq_foldl_cert; simp only [List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hcert; have heq := hcert kIdx (by omega)
  have hfold_nat : ∀ (n : ℕ) (g : ℕ → ℕ), (List.range n).foldl (fun acc i ↦ acc + g i) 0 = ∑ i ∈
    Finset.range n, g i := by
    intro n g
    induction n with
    | zero => simp
    | succ m ih =>
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
          Finset.sum_range_succ]
  rw [heq, hfold_nat, Nat.cast_sum, sum_div_const, sum_Icc_eq_sum_range_local, Nat.add_sub_cancel (2
    ^ kIdx) 1]; refine Finset.sum_le_sum fun i _ ↦ ?_; set r := i + 1; have hr_pos : (0 : ℝ) < (r :
    ℝ) := (by dsimp [r]; positivity); have hsr_pos : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
  set s := Nat.sqrt (1000000000000000000000000 / r); have hsq_nat : (s * s) * r ≤
    1000000000000000000000000 := (Nat.mul_le_mul_right r (Nat.sqrt_le _)).trans (Nat.div_mul_le_self
    _ r)
  have hsq_r : ((s : ℝ) * √(r : ℝ)) ^ 2 ≤ (swUnionScale : ℝ) ^ 2 := by
    have hcast : (((s * s) * r : ℕ) : ℝ) ≤ (1000000000000000000000000 : ℝ) :=
      (by exact_mod_cast hsq_nat); push_cast at hcast; have hlhs : ((s : ℝ) * √(r : ℝ)) ^ 2 = (s :
      ℝ) * (s : ℝ) * (r : ℝ) := (by rw [mul_pow, Real.sq_sqrt hr_pos.le]; ring)
    have hrhs : (swUnionScale : ℝ) ^ 2 = 1000000000000000000000000 :=
      (by unfold swUnionScale; norm_num); linarith
  have hU_pos : (0 : ℝ) < (swUnionScale : ℝ) := (by unfold swUnionScale; norm_num)
  have hlin : (s : ℝ) * √(r : ℝ) ≤ (swUnionScale : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (s : ℝ) * √(r : ℝ)), ← Real.sqrt_sq hU_pos.le]
    exact Real.sqrt_le_sqrt hsq_r
  rw [show 1 + i = r by dsimp [r]; omega, div_le_div_iff₀ hU_pos hsr_pos]; linarith
theorem checkSwLRelCostScaled_sound {mIdx kIdx : ℕ} {vTop vScale : ℤ} {relNum relDen n : ℕ} (hchk :
  checkSwLRelCostScaled mIdx kIdx vTop vScale relNum relDen = true) : ((vTop : ℝ) / (vScale : ℝ)) *
  √(2 ^ n : ℝ) ≤ ((relNum : ℝ) / (relDen : ℝ)) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1
  / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 ^ mIdx : ℝ))) := by
  unfold checkSwLRelCostScaled at hchk; rw [decide_eq_true_eq] at hchk; rcases hchk with ⟨hm_le,
    hk_le, hv_pos, hvsc_pos, hrn_pos, hrd_pos, hineq⟩; have hU_pos : (0 : ℝ) < (swUnionScale : ℝ) :=
    (by unfold swUnionScale; norm_num); have hvsc_r : (0 : ℝ) < (vScale : ℝ) :=
    (by exact_mod_cast hvsc_pos); have hrd_r : (0 : ℝ) < (relDen : ℝ) := (by exact_mod_cast hrd_pos)
  have hrn_r : (0 : ℝ) < (relNum : ℝ) := (by exact_mod_cast hrn_pos); have hm_cert :=
    swLSqrtMUp12_sq_ge_cert
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hm_cert
  have hsq_m_r : (√(2 ^ mIdx : ℝ) * (swUnionScale : ℝ)) ^ 2 ≤ (swLSqrtMUp12 mIdx : ℝ) ^ 2 := by
    have hcast : ((2 ^ mIdx * 1000000000000000000000000 : ℕ) : ℝ) ≤ (((swLSqrtMUp12 mIdx) ^ 2 : ℕ) :
      ℝ) := (by exact_mod_cast hm_cert mIdx (by omega)); push_cast at hcast
    have hlhs : (√(2 ^ mIdx : ℝ) *
      (swUnionScale : ℝ)) ^ 2 = (2 ^ mIdx : ℝ) * 1000000000000000000000000 :=
      (by unfold swUnionScale; rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num); linarith
  have hsqrt_m_pos : (0 : ℝ) < √(2 ^ mIdx : ℝ) := (by positivity)
  have hup_m : √(2 ^ mIdx : ℝ) * (swUnionScale : ℝ) ≤ (swLSqrtMUp12 mIdx : ℝ) := by
    have hr_nn : (0 : ℝ) ≤ (swLSqrtMUp12 mIdx : ℝ) := Nat.cast_nonneg _; rw [← Real.sqrt_sq
      (by positivity : 0 ≤ √(2 ^ mIdx : ℝ) * (swUnionScale : ℝ)), ← Real.sqrt_sq hr_nn]
    exact Real.sqrt_le_sqrt hsq_m_r
  have hup_m_pos : (0 : ℝ) < (swLSqrtMUp12 mIdx : ℝ) := lt_of_lt_of_le (mul_pos hsqrt_m_pos hU_pos)
    hup_m; have hinv_m : (swUnionScale : ℝ) / (swLSqrtMUp12 mIdx : ℝ) ≤ 1 / √(2 ^ mIdx : ℝ) :=
    (by rw [div_le_div_iff₀ hup_m_pos hsqrt_m_pos]; linarith)
  have hpi4_le : (swLPi4Lo12 : ℝ) / (swUnionScale : ℝ) ≤ π / 4 :=
    (by unfold swLPi4Lo12 swUnionScale; have hpi := Real.pi_gt_d20; linarith); have hharm_le :=
    swLHarmPow2_le_real hk_le; have hineq_r : (vTop : ℝ) * (swLSqrtMUp12 mIdx : ℝ) * (swUnionScale :
    ℝ) * (relDen : ℝ) ≤ (vScale : ℝ) * (swLPi4Lo12 : ℝ) * (swLHarmPow2 kIdx : ℝ) * (relNum : ℝ) :=
    (by exact_mod_cast hineq)
  have hv_div : (vTop : ℝ) / (vScale : ℝ) ≤ ((relNum : ℝ) / (relDen : ℝ)) * (((swLPi4Lo12 : ℝ) /
    (swUnionScale : ℝ)) * ((swLHarmPow2 kIdx : ℝ) / (swUnionScale : ℝ)) * ((swUnionScale : ℝ) /
    (swLSqrtMUp12 mIdx : ℝ))) := by
    have hpos_den : 0 < (vScale : ℝ) * (relDen : ℝ) * (swUnionScale : ℝ) * (swLSqrtMUp12 mIdx : ℝ)
      := (by positivity); rw [← sub_nonneg]; have hdiff : ((relNum : ℝ) / (relDen : ℝ)) *
      (((swLPi4Lo12 : ℝ) / (swUnionScale : ℝ)) * ((swLHarmPow2 kIdx : ℝ) / (swUnionScale : ℝ)) *
      ((swUnionScale : ℝ) / (swLSqrtMUp12 mIdx : ℝ))) - (vTop : ℝ) / (vScale : ℝ) = ((vScale : ℝ) *
      (swLPi4Lo12 : ℝ) * (swLHarmPow2 kIdx : ℝ) * (relNum : ℝ) - (vTop : ℝ) * (swLSqrtMUp12 mIdx :
      ℝ) * (swUnionScale : ℝ) * (relDen : ℝ)) / ((vScale : ℝ) * (relDen : ℝ) * (swUnionScale : ℝ) *
      (swLSqrtMUp12 mIdx : ℝ)) := (by field_simp [hvsc_r.ne', hrd_r.ne', hU_pos.ne', hup_m_pos.ne'])
    rw [hdiff]; exact div_nonneg (by linarith) hpos_den.le
  have hprod_le : ((swLPi4Lo12 : ℝ) / (swUnionScale : ℝ)) * ((swLHarmPow2 kIdx : ℝ) / (swUnionScale
    : ℝ)) * ((swUnionScale : ℝ) / (swLSqrtMUp12 mIdx : ℝ)) ≤ (π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2
    ^ kIdx), 1 / √(r : ℝ)) * (1 / √(2 ^ mIdx : ℝ)) := by
    have h12 : ((swLPi4Lo12 : ℝ) / (swUnionScale : ℝ)) * ((swLHarmPow2 kIdx : ℝ) / (swUnionScale :
      ℝ)) ≤ (π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) := mul_le_mul hpi4_le
      hharm_le (by positivity) (by linarith [Real.pi_gt_d20])
    exact mul_le_mul h12 hinv_m (by positivity) (mul_nonneg (by linarith [Real.pi_gt_d20])
      (Finset.sum_nonneg fun r _ ↦ by positivity))
  have hcoef : (vTop : ℝ) / (vScale : ℝ) ≤ ((relNum : ℝ) / (relDen : ℝ)) * ((π / 4) * (∑ r ∈
    Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) * (1 / √(2 ^ mIdx : ℝ))) := hv_div.trans
    (mul_le_mul_of_nonneg_left hprod_le (by positivity))
  refine (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (2 ^ n : ℝ))).trans_eq ?_
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (2 ^ n : ℝ))]; ring
theorem checkSwLRelCostCell_sound {mIdx kIdx : ℕ} {vTop16 : ℤ} {relNum relDen n : ℕ} (hchk :
  checkSwLRelCostCell mIdx kIdx vTop16 relNum relDen = true) : ((vTop16 : ℝ) / (multiUnitScale : ℝ))
  * √(2 ^ n : ℝ) ≤ ((relNum : ℝ) / (relDen : ℝ)) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx),
  1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 ^ mIdx : ℝ))) := checkSwLRelCostScaled_sound hchk
end SchurWeylLCert
end QuantumComputation.Specs.GroverFindAll
