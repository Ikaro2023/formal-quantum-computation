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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLCertDefs
/-!
# Closed-Form Diagonal Dominance for `2 ≤ L ≤ 8` `H_dist` Overlap (`SchurWeylHdistOverlap2L`)

Self-contained arithmetic and combinatorial bounds proving `0 ≤ swLDiagOverlap L (2 ^ n) r j`
and `1 - 1 / 10 ^ 18 ≤ (swLDiagOverlap L (2 ^ n) r j) ^ 2` across all `2 ≤ L ≤ 8`, `96 ≤ n`,
`L ≤ r ≤ 1024`, and `j: Fin (2 * L)`, together with `isValidSwLOverlap_of_orth_and_diag`
deducing `SchurWeylLCert.IsValidSwLOverlap` from orthogonality and diagonal square bounds.
-/
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open Real
/-- Cardinality of injective `L`-tuple orbit `o: Fin (2 * L)` (`b = o % 2`, `h = o / 2`). -/
noncomputable def swLOrbitCardNat (L N r : ℕ) (o : Fin (2 * L)) : ℕ :=
  let b := o.1 % 2
  let h := o.1 / 2
  if b = 0 then
    (N - r) * (L - 1).choose h * (h.factorial * r.choose h) *
      ((L - 1 - h).factorial * (N - r - 1).choose (L - 1 - h))
  else
    r * (L - 1).choose h * (h.factorial * (r - 1).choose h) *
      ((L - 1 - h).factorial * (N - r).choose (L - 1 - h))
/-- Normalization factor `(L - 1)! * m * C(N - 2m + 1, L - m)` of `rawLiftA m`. -/
noncomputable def swLCaaNat (L N m : ℕ) : ℕ :=
  (L - 1).factorial * m * (N - 2 * m + 1).choose (L - m)
/-- Squared norm `r! (N - r)! (r - m)! (N - r - m)! C(N - m + 1, m)` of `qVecRaw R m`. -/
noncomputable def swLQNormSqNat (N r m : ℕ) : ℕ :=
  r.factorial * (N - r).factorial * (r - m).factorial * (N - r - m).factorial *
    (N - m + 1).choose m
/-- Value of `rawLiftA m (qVecRaw R m)` on an injective tuple with grid hit `b` and tail
  hits
  `h`. -/
noncomputable def swLRawLiftAOnOrbit (L N r m b h : ℕ) : ℝ :=
  ∑ u ∈ Finset.range m, ((h.choose u * (L - 1 - h).choose (m - 1 - u) : ℕ) : ℝ) * (-1 : ℝ) ^ (m +
  (b + u)) * (((r - (b + u)).factorial * (N - r - m + (b + u)).factorial : ℕ) : ℝ)
/-- Closed-form diagonal value `M j j` of `swLOverlapMatFn L R` (`N = 2 ^ n`, `r = R.card`). -/
noncomputable def swLDiagOverlap (L N r : ℕ) (j : Fin (2 * L)) : ℝ :=
  let oc : ℝ := (swLOrbitCardNat L N r j : ℝ)
  if j.1 = 0 then
    √(oc / ((L.factorial * N.choose L : ℕ) : ℝ))
  else if j.1 % 2 = 1 then
    let m := (j.1 + 1) / 2
    √oc * swLRawLiftAOnOrbit L N r m 1 (m - 1) /
      √((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)
  else
    let w := j.1 / 2
    (-√(((N - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ))) *
      (√oc * swLRawLiftAOnOrbit L N r (w + 1) 0 w /
        √((swLCaaNat L N (w + 1) * swLQNormSqNat N r (w + 1) : ℕ) : ℝ))
namespace SwLOverlapInternal
theorem bounds_of_sq_le_sq {x c : ℝ} (hc : 0 ≤ c) (h : x ^ 2 ≤ c ^ 2) : -c ≤ x ∧ x ≤ c := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have hp : 0 < (-x - c) * (-x + c) := mul_pos (by linarith) (by linarith)
    have heq : (-x - c) * (-x + c) = x ^ 2 - c ^ 2 := (by ring); linarith
  · by_contra hgt
    have hp : 0 < (x - c) * (x + c) := mul_pos (by linarith) (by linarith)
    have heq : (x - c) * (x + c) = x ^ 2 - c ^ 2 := (by ring); linarith
theorem le_div_of_mul_le {a b c : ℝ} (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := by
  have h1 : (a * c) * (1 / c) ≤ b * (1 / c) := mul_le_mul_of_nonneg_right h (by positivity)
  have h2 : (a * c) * (1 / c) = a * (c / c) := (by ring); rw [h2, div_self hc.ne', mul_one] at h1
  simpa [div_eq_mul_inv] using h1
theorem div_le_of_le_mul {a b c : ℝ} (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := by
  have h1 : a * (1 / c) ≤ (b * c) * (1 / c) := mul_le_mul_of_nonneg_right h (by positivity)
  have h2 : (b * c) * (1 / c) = b * (c / c) := (by ring); rw [h2, div_self hc.ne', mul_one] at h1
  simpa [div_eq_mul_inv] using h1
theorem mul_sq_le_sq_of_nonneg {a b c : ℝ} (hab : 0 ≤ a * b) (hle : a * b ≤ c) :
    a ^ 2 * b ^ 2 ≤ c ^ 2 := by
  have hmul := mul_self_le_mul_self hab hle
  linarith [hmul, show a ^ 2 * b ^ 2 = (a * b) * (a * b) by ring, show c ^ 2 = c * c by ring]
/-- Falling factorial product `M * (M - 1) * ⋯ * (M - (k - 1))` in `ℕ`. -/
def swLFallProd (M : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (M - k) * swLFallProd M k
theorem swLFallProd_mul_sub_factorial (M : ℕ) :
    ∀ {k : ℕ}, k ≤ M → swLFallProd M k * (M - k).factorial = M.factorial
  | 0, _ => by simp [swLFallProd]
  | k + 1, hk => by
    have hsub : M - (k + 1) = M - k - 1 := by omega
    have hne : M - k ≠ 0 := by omega
    calc
      swLFallProd M (k + 1) * (M - (k + 1)).factorial
          = swLFallProd M k * ((M - k) * (M - k - 1).factorial) := by
            rw [swLFallProd, hsub]; ring
      _ = swLFallProd M k * (M - k).factorial := by
            rw [Nat.mul_factorial_pred hne]
      _ = M.factorial := swLFallProd_mul_sub_factorial M (by omega)
theorem factorial_mul_choose_eq_swLFallProd {M k : ℕ} (hk : k ≤ M) :
    k.factorial * M.choose k = swLFallProd M k := by
  apply Nat.mul_right_cancel (Nat.factorial_pos (M - k))
  calc
    k.factorial * M.choose k * (M - k).factorial
        = M.choose k * k.factorial * (M - k).factorial := by ring
    _ = M.factorial := Nat.choose_mul_factorial_mul_factorial hk
    _ = swLFallProd M k * (M - k).factorial := (swLFallProd_mul_sub_factorial M hk).symm
theorem swLFallProd_le_pow {M U : ℕ} (hMU : M ≤ U) :
    ∀ k : ℕ, swLFallProd M k ≤ U ^ k
  | 0 => by simp [swLFallProd]
  | k + 1 => by
    calc
      swLFallProd M (k + 1) = (M - k) * swLFallProd M k := rfl
      _ ≤ U * U ^ k := Nat.mul_le_mul (by omega) (swLFallProd_le_pow hMU k)
      _ = U ^ (k + 1) := by ring
theorem pow_le_swLFallProd (B M : ℕ) :
    ∀ (k : ℕ), (∀ i < k, B ≤ M - i) → B ^ k ≤ swLFallProd M k
  | 0, _ => by simp [swLFallProd]
  | k + 1, hB => by
    calc
      B ^ (k + 1) = B * B ^ k := by ring
      _ ≤ (M - k) * swLFallProd M k :=
        Nat.mul_le_mul (hB k (by omega))
          (pow_le_swLFallProd B M k (fun i hi ↦ hB i (by omega)))
      _ = swLFallProd M (k + 1) := rfl
theorem choose_le_two_pow : ∀ n k : ℕ, n.choose k ≤ 2 ^ n
  | 0, k => by cases k <;> simp
  | n + 1, 0 => by
    rw [Nat.choose_zero_right]
    exact Nat.one_le_pow (n + 1) 2 (by omega)
  | n + 1, k + 1 => by
    calc
      (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) := Nat.choose_succ_succ n k
      _ ≤ 2 ^ n + 2 ^ n :=
        Nat.add_le_add (choose_le_two_pow n k) (choose_le_two_pow n (k + 1))
      _ = 2 ^ (n + 1) := by ring
/-- Factorial product `(r - (b + u))! * (N - r - m + (b + u))!` at index `u`. -/
def swLTermFac (N r m b u : ℕ) : ℕ :=
  (r - (b + u)).factorial * (N - r - m + (b + u)).factorial
theorem swLTermFac_step_bound {L N r m b u : ℕ} (hb : b ≤ 1) (hmL : m ≤ L) (hr : m ≤ r)
    (hN : 2 * r + L ≤ N) (hu : u < m - 1) :
    (N - r - L) * swLTermFac N r m b u ≤ r * swLTermFac N r m b (u + 1) := by
  have hpred : (r - (b + u)) * (r - (b + (u + 1))).factorial = (r - (b + u)).factorial := by
    have hsub : r - (b + u) - 1 = r - (b + (u + 1)) := (by omega); rw [← hsub]
    exact Nat.mul_factorial_pred (by omega)
  have hsucc : (N - r - m + (b + (u + 1))).factorial = (N - r - m + (b + u) + 1) * (N - r - m +
    (b + u)).factorial := by
    have hadd : N - r - m + (b + (u + 1)) = (N - r - m + (b + u)) + 1 := (by omega)
    rw [hadd, Nat.factorial_succ]
  have hid : (N - r - m + (b + u) + 1) * swLTermFac N r m b u = (r - (b + u)) * swLTermFac N r m b
    (u + 1) := by
    unfold swLTermFac; rw [← hpred, hsucc]; ring
  calc (N - r - L) * swLTermFac N r m b u ≤ (N - r - m + (b + u) + 1) * swLTermFac N r m b u :=
        Nat.mul_le_mul_right _ (by omega)
    _ = (r - (b + u)) * swLTermFac N r m b (u + 1) := hid
    _ ≤ r * swLTermFac N r m b (u + 1) := Nat.mul_le_mul_right _ (by omega)
theorem swLTermFac_mono_step {L N r m b u : ℕ} (hb : b ≤ 1) (_hL : 2 ≤ L) (hmL : m ≤ L)
    (hr : m ≤ r) (hN : 2 * r + L ≤ N) (hu : u < m - 1) :
    swLTermFac N r m b u ≤ swLTermFac N r m b (u + 1) := by
  have hBpos : 0 < N - r - L := (by omega); apply Nat.le_of_mul_le_mul_left _ hBpos
  calc (N - r - L) * swLTermFac N r m b u ≤ r * swLTermFac N r m b (u + 1) :=
        swLTermFac_step_bound hb hmL hr hN hu
    _ ≤ (N - r - L) * swLTermFac N r m b (u + 1) := Nat.mul_le_mul_right _ (by omega)
theorem swLTermFac_le_add {L N r m b : ℕ} (hb : b ≤ 1) (hL : 2 ≤ L) (hmL : m ≤ L)
    (hr : m ≤ r) (hN : 2 * r + L ≤ N) :
    ∀ (d u : ℕ), u + d < m → swLTermFac N r m b u ≤ swLTermFac N r m b (u + d)
  | 0, u, _ => by simp
  | d + 1, u, hud => by
    have h1 := swLTermFac_le_add hb hL hmL hr hN d u (by omega)
    have h2 := swLTermFac_mono_step hb hL hmL hr hN (show u + d < m - 1 by omega)
    simpa [Nat.add_assoc] using h1.trans h2
theorem swLTermFac_tail_bound {L N r m b u : ℕ} (hb : b ≤ 1) (hL : 2 ≤ L) (hmL : m ≤ L)
    (hr : m ≤ r) (hN : 2 * r + L ≤ N) (hu : u < m - 1) :
    (N - r - L) * swLTermFac N r m b u ≤ r * swLTermFac N r m b (m - 1) := by
  have hmono : swLTermFac N r m b u ≤ swLTermFac N r m b (m - 2) := by
    have h := swLTermFac_le_add hb hL hmL hr hN (m - 2 - u) u (by omega)
    rwa [show u + (m - 2 - u) = m - 2 by omega] at h
  have htop : (N - r - L) * swLTermFac N r m b (m - 2) ≤ r * swLTermFac N r m b ((m - 2) + 1) :=
    swLTermFac_step_bound hb hmL hr hN (show m - 2 < m - 1 by omega)
  rw [show (m - 2) + 1 = m - 1 by omega] at htop
  exact (Nat.mul_le_mul_left (N - r - L) hmono).trans htop
theorem swLRawLiftAOnOrbit_signed_ge {L N r m b : ℕ} (hb : b ≤ 1) (hL : 2 ≤ L) (hL8 : L ≤ 8) (hm1
    : 1 ≤ m) (hmL : m ≤ L) (hr : m ≤ r) (hN : 2 * r + L ≤ N) : (1 - (1024 * (r : ℝ)) / ((N - r - L
    : ℕ) : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ) ≤ (-1 : ℝ) ^ (b + 1) * swLRawLiftAOnOrbit L N r
    m b (m - 1) := by
  let B : ℕ := N - r - L
  have hBpos : (0 : ℝ) < (B : ℝ) := (by have : 0 < B := (by omega); exact_mod_cast this)
  let term : ℕ → ℝ := fun u ↦ (((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) : ℕ) :
    ℝ) * (-1 : ℝ) ^ (m + (b + u)) * ((swLTermFac N r m b u : ℕ) : ℝ)
  have hdef : swLRawLiftAOnOrbit L N r m b (m - 1) = ∑ u ∈ Finset.range m, term u := rfl
  have hrange : Finset.range m = Finset.range ((m - 1) + 1) := congrArg Finset.range (by omega)
  rw [hdef, hrange, Finset.sum_range_succ, mul_add]
  have htop : (-1 : ℝ) ^ (b + 1) * term (m - 1) = (swLTermFac N r m b (m - 1) : ℝ) := by
    dsimp [term]; rw [Nat.choose_self, Nat.sub_self, Nat.choose_zero_right]
    have hsgn : (-1 : ℝ) ^ (b + 1) * (-1 : ℝ) ^ (m + (b + (m - 1))) = 1 := by
      rw [← pow_add, show (b + 1) + (m + (b + (m - 1))) = 2 * (b + m) by omega, pow_mul]; norm_num
    calc
      (-1 : ℝ) ^ (b + 1) *
          (((1 * 1 : ℕ) : ℝ) * (-1 : ℝ) ^ (m + (b + (m - 1))) * (swLTermFac N r m b (m - 1) : ℝ))
          = ((-1 : ℝ) ^ (b + 1) * (-1 : ℝ) ^ (m + (b + (m - 1)))) *
              (swLTermFac N r m b (m - 1) : ℝ) := by push_cast; ring
      _ = (swLTermFac N r m b (m - 1) : ℝ) := by rw [hsgn, one_mul]
  have htail_term : ∀ u ∈ Finset.range (m - 1),
      (B : ℝ) * |term u| ≤ (128 * (r : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ) := by
    intro u hu; have hu_lt : u < m - 1 := Finset.mem_range.mp hu
    have habs : |term u| =
        (((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) : ℕ) : ℝ) *
          (swLTermFac N r m b u : ℝ) := by
      dsimp [term]
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    have hc_prod : (m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) ≤ 128 := by
      have hc1 := choose_le_two_pow (m - 1) u
      have hc2 := choose_le_two_pow (L - 1 - (m - 1)) (m - 1 - u)
      have hpow : 2 ^ (m - 1) * 2 ^ (L - 1 - (m - 1)) ≤ 128 := by
        rw [← pow_add, show m - 1 + (L - 1 - (m - 1)) = L - 1 by omega]
        exact le_trans (Nat.pow_le_pow_right (by omega) (show L - 1 ≤ 7 by omega)) (by norm_num)
      exact (Nat.mul_le_mul hc1 hc2).trans hpow
    have hfac : B * swLTermFac N r m b u ≤ r * swLTermFac N r m b (m - 1) :=
      swLTermFac_tail_bound hb hL hmL hr hN hu_lt
    have hnat : ((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u)) * (B * swLTermFac N r m
      b u) ≤ 128 * (r * swLTermFac N r m b (m - 1)) := Nat.mul_le_mul hc_prod hfac
    have hreal : (((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) : ℕ) : ℝ) * ((B : ℝ) *
      (swLTermFac N r m b u : ℝ)) ≤ (128 : ℝ) * ((r : ℝ) * (swLTermFac N r m b (m - 1) : ℝ)) := by
      exact_mod_cast hnat
    rw [habs]; linarith
  have htail_sum : (B : ℝ) * |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤
      (1024 * (r : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ) := by
    have habs_sgn : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| =
        |∑ u ∈ Finset.range (m - 1), term u| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [habs_sgn]
    have h1 : (B : ℝ) * |∑ u ∈ Finset.range (m - 1), term u| ≤
        (B : ℝ) * ∑ u ∈ Finset.range (m - 1), |term u| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hBpos.le
    have h2 : (B : ℝ) * ∑ u ∈ Finset.range (m - 1), |term u| ≤
        ((m - 1 : ℕ) : ℝ) * ((128 * (r : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ)) := by
      rw [Finset.mul_sum]; refine (Finset.sum_le_sum htail_term).trans ?_
      simp [Finset.sum_const, nsmul_eq_mul]
    have hm7 : ((m - 1 : ℕ) : ℝ) ≤ 7 := (by have : m - 1 ≤ 7 := (by omega); exact_mod_cast this)
    have hnn : 0 ≤ (128 * (r : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ) := (by positivity)
    have h3 : ((m - 1 : ℕ) : ℝ) * ((128 * (r : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ)) ≤ 7 *
      ((128 * (r : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ)) := mul_le_mul_of_nonneg_right hm7 hnn
    linarith
  have htail_div : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤
      ((1024 * (r : ℝ)) / (B : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ) := by
    have h2 : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤
        ((1024 * (r : ℝ)) * (swLTermFac N r m b (m - 1) : ℝ)) / (B : ℝ) := by
      apply le_div_of_mul_le hBpos; linarith [htail_sum]
    simpa [mul_div_right_comm] using h2
  have hneg := neg_le_abs ((-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u); rw [htop]
  linarith
theorem nat_scaled_ratio_ge {scale num den common bPow nPow : ℕ} (hc : 0 < common) (hden : 0 <
    den) (hnPow : 0 < nPow) (h1 : common * bPow ≤ scale * num) (h2 : scale * den ≤ common * nPow)
    : (bPow : ℝ) / (nPow : ℝ) ≤ (num : ℝ) / (den : ℝ) := by
  have hcross : bPow * den ≤ num * nPow := by
    apply Nat.le_of_mul_le_mul_left _ hc
    calc
      common * (bPow * den) = (common * bPow) * den := by ring
      _ ≤ (scale * num) * den := Nat.mul_le_mul_right den h1
      _ = num * (scale * den) := by ring
      _ ≤ num * (common * nPow) := Nat.mul_le_mul_left num h2
      _ = common * (num * nPow) := by ring
  have hcrossR : (bPow : ℝ) * (den : ℝ) ≤ (num : ℝ) * (nPow : ℝ) := (by exact_mod_cast hcross)
  have hdenR : (0 : ℝ) < (den : ℝ) := (by exact_mod_cast hden)
  have hnPowR : (0 : ℝ) < (nPow : ℝ) := (by exact_mod_cast hnPow); apply le_div_of_mul_le hdenR
  have hmul : ((bPow : ℝ) / (nPow : ℝ)) * (den : ℝ) =
      ((bPow : ℝ) * (den : ℝ)) / (nPow : ℝ) := by ring
  rw [hmul]; exact div_le_of_le_mul hnPowR hcrossR
theorem one_sub_mul_le_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ k : ℕ, 1 - (k : ℝ) * x ≤ (1 - x) ^ k
  | 0 => by simp
  | k + 1 => by
    have hk : 1 - (k : ℝ) * x ≤ (1 - x) ^ k := one_sub_mul_le_pow hx0 hx1 k
    have hmul : (1 - x) * (1 - (k : ℝ) * x) ≤ (1 - x) * (1 - x) ^ k :=
      mul_le_mul_of_nonneg_left hk (by linarith)
    have hkx : 0 ≤ (k : ℝ) * x ^ 2 := by positivity
    have hid : 1 - ((k + 1 : ℕ) : ℝ) * x =
        (1 - x) * (1 - (k : ℝ) * x) - (k : ℝ) * x ^ 2 := by
      push_cast; ring
    have hp : (1 - x) * (1 - x) ^ k = (1 - x) ^ (k + 1) := by ring
    linarith
theorem ratio_pow_ge_half_tol {L n r : ℕ} (hL8 : L ≤ 8) (hn : 96 ≤ n) (hr1024 : r ≤ 1024) : 1 - (1
    : ℝ) / (2 * 10 ^ 18) ≤ (((2 ^ n - r - L : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ)) ^ L := by
  let N : ℕ := 2 ^ n
  have hN28 : 10 ^ 28 ≤ N :=
    le_trans (by norm_num : 10 ^ 28 ≤ 2 ^ 96) (Nat.pow_le_pow_right (by omega) hn)
  have hNpos : (0 : ℝ) < (N : ℝ) := (by have : 0 < N := (by omega); exact_mod_cast this)
  have hsub_eq : ((N - r - L : ℕ) : ℝ) / (N : ℝ) = 1 - ((r + L : ℕ) : ℝ) / (N : ℝ) := by
    have hle : r + L ≤ N := (by omega); have hsub : N - r - L = N - (r + L) := (by omega)
    rw [hsub, Nat.cast_sub hle, sub_div, div_self hNpos.ne']
  have hx0 : 0 ≤ ((r + L : ℕ) : ℝ) / (N : ℝ) := (by positivity)
  have hx1 : ((r + L : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
    apply div_le_of_le_mul hNpos; have : r + L ≤ N := (by omega)
    have hR : ((r + L : ℕ) : ℝ) ≤ (N : ℝ) := (by exact_mod_cast this); linarith
  have hbern := one_sub_mul_le_pow hx0 hx1 L; rw [hsub_eq]
  have herr : (L : ℝ) * (((r + L : ℕ) : ℝ) / (N : ℝ)) ≤ (1 : ℝ) / (2 * 10 ^ 18) := by
    have hnum_le : L * (r + L) ≤ 10 ^ 5 :=
      le_trans (Nat.mul_le_mul hL8 (show r + L ≤ 1032 by omega)) (by norm_num)
    have hnumR : (L : ℝ) * ((r + L : ℕ) : ℝ) ≤ (10 ^ 5 : ℝ) := (by exact_mod_cast hnum_le)
    have hNR : (10 ^ 28 : ℝ) ≤ (N : ℝ) := (by exact_mod_cast hN28)
    have hdiv : ((L : ℝ) * ((r + L : ℕ) : ℝ)) / (N : ℝ) ≤ (1 : ℝ) / (2 * 10 ^ 18) := by
      apply div_le_of_le_mul hNpos; linarith
    simpa [mul_div_assoc] using hdiv
  linarith
theorem tail_factor_ge_half_tol {L n r : ℕ} (hL8 : L ≤ 8) (hn : 96 ≤ n) (hr1024 : r ≤ 1024) : 0 ≤
    1 - (1024 * (r : ℝ)) / ((2 ^ n - r - L : ℕ) : ℝ) ∧ 1 - (1 : ℝ) / (2 * 10 ^ 18) ≤ (1 - (1024 *
    (r : ℝ)) / ((2 ^ n - r - L : ℕ) : ℝ)) ^ 2 := by
  let B : ℕ := 2 ^ n - r - L
  have hN28 : 10 ^ 28 ≤ 2 ^ n :=
    le_trans (by norm_num : 10 ^ 28 ≤ 2 ^ 96) (Nat.pow_le_pow_right (by omega) hn)
  have hB27 : 10 ^ 27 ≤ B := (by omega)
  have hBpos : (0 : ℝ) < (B : ℝ) := (by have : 0 < B := (by omega); exact_mod_cast this)
  have hy : (1024 * (r : ℝ)) / (B : ℝ) ≤ (1 : ℝ) / (4 * 10 ^ 18) := by
    apply div_le_of_le_mul hBpos; have hrR : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
    have hBR : (10 ^ 27 : ℝ) ≤ (B : ℝ) := (by exact_mod_cast hB27); linarith
  refine ⟨by linarith, ?_⟩
  have hsq : 1 - 2 * ((1024 * (r : ℝ)) / (B : ℝ)) ≤ (1 - (1024 * (r : ℝ)) / (B : ℝ)) ^ 2 := by
    have hnn : 0 ≤ ((1024 * (r : ℝ)) / (B : ℝ)) ^ 2 := sq_nonneg _
    linarith [show (1 - (1024 * (r : ℝ)) / (B : ℝ)) ^ 2 =
      1 - 2 * ((1024 * (r : ℝ)) / (B : ℝ)) + ((1024 * (r : ℝ)) / (B : ℝ)) ^ 2 by ring]
  linarith
theorem swLOrbitCardNat_odd {L N r : ℕ} {j : Fin (2 * L)} (hodd : j.1 % 2 = 1) :
    let m := (j.1 + 1) / 2
    swLOrbitCardNat L N r j = r * (L - 1).choose (m - 1) * ((m - 1).factorial * (r - 1).choose
      (m - 1)) * ((L - m).factorial * (N - r).choose (L - m)) := by
  intro m; have hb : j.1 % 2 ≠ 0 := (by omega); have hh : j.1 / 2 = m - 1 := (by omega)
  have hsub : L - 1 - (m - 1) = L - m := (by omega); unfold swLOrbitCardNat
  simp only [hb, ↓reduceIte, hh, hsub]
theorem swLOrbitCardNat_even {L N r : ℕ} {j : Fin (2 * L)} (heven : j.1 % 2 = 0) :
    let w := j.1 / 2
    swLOrbitCardNat L N r j = (N - r) * (L - 1).choose w * (w.factorial * r.choose w) * ((L - 1 -
      w).factorial * (N - r - 1).choose (L - 1 - w)) := by
  intro w; simp [swLOrbitCardNat, heven, w]
theorem branch2_ratio_ge {L N r : ℕ} (hL : 2 ≤ L) (hrL : L ≤ r) (hN : 2 * r + L ≤ N)
    {j : Fin (2 * L)} (hodd : j.1 % 2 = 1) :
    let m := (j.1 + 1) / 2; let a0 := swLTermFac N r m 1 (m - 1)
    let den := swLCaaNat L N m * swLQNormSqNat N r m
    0 < den ∧ (((N - r - L) ^ L : ℕ) : ℝ) / ((N ^ L : ℕ) : ℝ) ≤ ((swLOrbitCardNat L N r j * a0 ^ 2
      : ℕ) : ℝ) / (den : ℝ) := by
  intro m a0 den
  have ha0_eq : a0 = (r - m).factorial * (N - r).factorial := by
    dsimp [a0, swLTermFac]; rw [show 1 + (m - 1) = m by omega, show N - r - m + m = N - r by omega]
  have hden_pos : 0 < den := by
    dsimp [den, swLCaaNat, swLQNormSqNat]; refine Nat.mul_pos ?_ ?_
    · exact Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (by omega)) (Nat.choose_pos (by omega))
    · exact Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
            (Nat.factorial_pos _))
          (Nat.factorial_pos _))
        (Nat.choose_pos (by omega))
  refine ⟨hden_pos, ?_⟩
  let scale : ℕ := (m - 1).factorial * (L - m).factorial
  let common : ℕ := (L - 1).factorial * r.factorial * (r - m).factorial * (N - r).factorial * (N -
    r - m).factorial
  have hcommon_pos : 0 < common := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
    (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)) (Nat.factorial_pos _))
    (Nat.factorial_pos _)
  have hc1 : (L - 1).choose (m - 1) * (m - 1).factorial * (L - m).factorial =
      (L - 1).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m - 1 ≤ L - 1 by omega)
    rwa [show L - 1 - (m - 1) = L - m by omega] at h
  have hc2 : r * ((r - 1).choose (m - 1) * (m - 1).factorial * (r - m).factorial) =
      r.factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m - 1 ≤ r - 1 by omega)
    rw [show r - 1 - (m - 1) = r - m by omega] at h; rw [h]; exact Nat.mul_factorial_pred (by omega)
  have hc3 : (L - m).factorial * (N - r).choose (L - m) = swLFallProd (N - r) (L - m) :=
    factorial_mul_choose_eq_swLFallProd (by omega)
  have hc4 : (N - r).factorial = swLFallProd (N - r) m * (N - r - m).factorial :=
    (swLFallProd_mul_sub_factorial (N - r) (by omega)).symm
  have ha0_sq : a0 ^ 2 = (r - m).factorial * (r - m).factorial * (N - r).factorial *
      (swLFallProd (N - r) m * (N - r - m).factorial) := by
    calc
      a0 ^ 2 = (r - m).factorial * (r - m).factorial * (N - r).factorial *
          (N - r).factorial := by rw [ha0_eq]; ring
      _ = (r - m).factorial * (r - m).factorial * (N - r).factorial *
          (swLFallProd (N - r) m * (N - r - m).factorial) :=
        congrArg ((r - m).factorial * (r - m).factorial * (N - r).factorial * ·) hc4
  have hnum_eq : scale * (swLOrbitCardNat L N r j * a0 ^ 2) =
      common * (swLFallProd (N - r) (L - m) * swLFallProd (N - r) m) := by
    rw [swLOrbitCardNat_odd hodd]; dsimp [scale, common]; rw [hc3, ha0_sq]
    calc
      ((m - 1).factorial * (L - m).factorial) *
          (r * (L - 1).choose (m - 1) * ((m - 1).factorial * (r - 1).choose (m - 1)) *
            swLFallProd (N - r) (L - m) *
            ((r - m).factorial * (r - m).factorial * (N - r).factorial *
              (swLFallProd (N - r) m * (N - r - m).factorial)))
          = ((L - 1).choose (m - 1) * (m - 1).factorial * (L - m).factorial) *
              (r * ((r - 1).choose (m - 1) * (m - 1).factorial * (r - m).factorial)) *
              (r - m).factorial * (N - r).factorial * (N - r - m).factorial *
              (swLFallProd (N - r) (L - m) * swLFallProd (N - r) m) := by ring
      _ = (L - 1).factorial * r.factorial * (r - m).factorial * (N - r).factorial *
            (N - r - m).factorial *
            (swLFallProd (N - r) (L - m) * swLFallProd (N - r) m) := by rw [hc1, hc2]
  have hd1 : m * (m - 1).factorial = m.factorial := Nat.mul_factorial_pred (by omega)
  have hd2 : m.factorial * (N - m + 1).choose m = swLFallProd (N - m + 1) m :=
    factorial_mul_choose_eq_swLFallProd (by omega)
  have hd3 : (L - m).factorial * (N - 2 * m + 1).choose (L - m) = swLFallProd (N - 2 * m + 1) (L -
    m) := factorial_mul_choose_eq_swLFallProd (by omega)
  have hden_eq : scale * den =
      common * (swLFallProd (N - 2 * m + 1) (L - m) * swLFallProd (N - m + 1) m) := by
    dsimp [scale, den, swLCaaNat, swLQNormSqNat, common]
    calc
      ((m - 1).factorial * (L - m).factorial) *
          ((L - 1).factorial * m * (N - 2 * m + 1).choose (L - m) *
            (r.factorial * (N - r).factorial * (r - m).factorial * (N - r - m).factorial *
              (N - m + 1).choose m))
          = (L - 1).factorial * r.factorial * (r - m).factorial * (N - r).factorial *
              (N - r - m).factorial *
              (((L - m).factorial * (N - 2 * m + 1).choose (L - m)) *
                ((m * (m - 1).factorial) * (N - m + 1).choose m)) := by ring
      _ = (L - 1).factorial * r.factorial * (r - m).factorial * (N - r).factorial *
            (N - r - m).factorial *
            (swLFallProd (N - 2 * m + 1) (L - m) * swLFallProd (N - m + 1) m) := by
          rw [hd3, hd1, hd2]
  have hnum_ge : common * (N - r - L) ^ L ≤ scale * (swLOrbitCardNat L N r j * a0 ^ 2) := by
    rw [hnum_eq]; refine Nat.mul_le_mul_left common ?_
    have hp1 := pow_le_swLFallProd (N - r - L) (N - r) (L - m) (fun _ _ ↦ by omega)
    have hp2 := pow_le_swLFallProd (N - r - L) (N - r) m (fun _ _ ↦ by omega)
    calc
      (N - r - L) ^ L = (N - r - L) ^ (L - m) * (N - r - L) ^ m := by
        rw [← pow_add, show L - m + m = L by omega]
      _ ≤ swLFallProd (N - r) (L - m) * swLFallProd (N - r) m := Nat.mul_le_mul hp1 hp2
  have hden_le : scale * den ≤ common * N ^ L := by
    rw [hden_eq]; refine Nat.mul_le_mul_left common ?_
    have hp1 := swLFallProd_le_pow (show N - 2 * m + 1 ≤ N by omega) (L - m)
    have hp2 := swLFallProd_le_pow (show N - m + 1 ≤ N by omega) m
    calc swLFallProd (N - 2 * m + 1) (L - m) * swLFallProd (N - m + 1) m ≤ N ^ (L - m) * N ^ m :=
          Nat.mul_le_mul hp1 hp2
      _ = N ^ L := by rw [← pow_add, show L - m + m = L by omega]
  exact nat_scaled_ratio_ge hcommon_pos hden_pos (Nat.pow_pos (by omega)) hnum_ge hden_le
theorem branch3_ratio_ge {L N r : ℕ} (hL : 2 ≤ L) (hrL : L ≤ r) (hN : 2 * r + L ≤ N)
    {j : Fin (2 * L)} (_hne0 : j.1 ≠ 0) (heven : j.1 % 2 = 0) :
    let w := j.1 / 2; let m := w + 1; let b0 := swLTermFac N r m 0 w
    let den := swLCaaNat L N m * swLQNormSqNat N r m
    0 < den ∧ 0 < r - w ∧ (((N - r - L) ^ L : ℕ) : ℝ) / ((N ^ L : ℕ) : ℝ) ≤ (((N - r - w) *
      swLOrbitCardNat L N r j * b0 ^ 2 : ℕ) : ℝ) / (((r - w) * den : ℕ) : ℝ) := by
  intro w m b0 den; have hwL : w ≤ L - 1 := (by omega); have hrw_pos : 0 < r - w := (by omega)
  have hb0_eq : b0 = (r - w).factorial * (N - r - 1).factorial := by
    dsimp [b0, swLTermFac]; rw [Nat.zero_add, show N - r - m + w = N - r - 1 by omega]
  have hden_pos : 0 < den := by
    dsimp [den, swLCaaNat, swLQNormSqNat]; refine Nat.mul_pos ?_ ?_
    · exact Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (by omega)) (Nat.choose_pos (by omega))
    · exact Nat.mul_pos
        (Nat.mul_pos
          (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
            (Nat.factorial_pos _))
          (Nat.factorial_pos _))
        (Nat.choose_pos (by omega))
  refine ⟨hden_pos, hrw_pos, ?_⟩
  let scale : ℕ := w.factorial * (L - 1 - w).factorial
  let common : ℕ := (r - w) * (L - 1).factorial * r.factorial * (r - m).factorial * (N -
    r).factorial * (N - r - m).factorial
  have hcommon_pos : 0 < common := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
    hrw_pos (Nat.factorial_pos _)) (Nat.factorial_pos _)) (Nat.factorial_pos _))
    (Nat.factorial_pos _)) (Nat.factorial_pos _)
  have hc1 : (L - 1).choose w * w.factorial * (L - 1 - w).factorial = (L - 1).factorial :=
    Nat.choose_mul_factorial_mul_factorial hwL
  have hc2 : r.choose w * w.factorial * (r - w).factorial = r.factorial :=
    Nat.choose_mul_factorial_mul_factorial (by omega)
  have hc2' : (r - w).factorial = (r - w) * (r - m).factorial := by
    have hsub : r - w - 1 = r - m := (by omega); rw [← hsub]
    exact (Nat.mul_factorial_pred (by omega)).symm
  have hc3 : (L - 1 - w).factorial * (N - r - 1).choose (L - 1 - w) = swLFallProd (N - r - 1) (L -
    1 - w) := factorial_mul_choose_eq_swLFallProd (by omega)
  have hc4 : (N - r) * (N - r - 1).factorial = (N - r).factorial :=
    Nat.mul_factorial_pred (by omega)
  have hc4' : (N - r - 1).factorial = swLFallProd (N - r - 1) w * (N - r - m).factorial := by
    have h := (swLFallProd_mul_sub_factorial (N - r - 1) (show w ≤ N - r - 1 by omega)).symm
    rwa [show N - r - 1 - w = N - r - m by omega] at h
  have hb0_sq : b0 ^ 2 = (r - w).factorial * ((r - w) * (r - m).factorial) *
      ((N - r - 1).factorial * (swLFallProd (N - r - 1) w * (N - r - m).factorial)) := by
    have hp1 : (r - w).factorial * (r - w).factorial =
        (r - w).factorial * ((r - w) * (r - m).factorial) :=
      congrArg ((r - w).factorial * ·) hc2'
    have hp2 : (N - r - 1).factorial * (N - r - 1).factorial =
        (N - r - 1).factorial * (swLFallProd (N - r - 1) w * (N - r - m).factorial) :=
      congrArg ((N - r - 1).factorial * ·) hc4'
    calc
      b0 ^ 2 = ((r - w).factorial * (r - w).factorial) *
          ((N - r - 1).factorial * (N - r - 1).factorial) := by rw [hb0_eq]; ring
      _ = (r - w).factorial * ((r - w) * (r - m).factorial) *
          ((N - r - 1).factorial * (swLFallProd (N - r - 1) w * (N - r - m).factorial)) := by
        rw [hp1, hp2]
  have hnum_eq : scale * ((N - r - w) * swLOrbitCardNat L N r j * b0 ^ 2) = common * (swLFallProd
    (N - r - 1) (L - 1 - w) * (N - r - w) * swLFallProd (N - r - 1) w) := by
    rw [swLOrbitCardNat_even heven]; dsimp [scale, common]; rw [hc3, hb0_sq]
    calc
      (w.factorial * (L - 1 - w).factorial) *
          ((N - r - w) *
            ((N - r) * (L - 1).choose w * (w.factorial * r.choose w) *
              swLFallProd (N - r - 1) (L - 1 - w)) *
            ((r - w).factorial * ((r - w) * (r - m).factorial) *
              ((N - r - 1).factorial *
                (swLFallProd (N - r - 1) w * (N - r - m).factorial))))
          = (r - w) * ((L - 1).choose w * w.factorial * (L - 1 - w).factorial) *
              (r.choose w * w.factorial * (r - w).factorial) * (r - m).factorial *
              ((N - r) * (N - r - 1).factorial) * (N - r - m).factorial *
              (swLFallProd (N - r - 1) (L - 1 - w) * (N - r - w) *
                swLFallProd (N - r - 1) w) := by ring
      _ = (r - w) * (L - 1).factorial * r.factorial * (r - m).factorial *
            (N - r).factorial * (N - r - m).factorial *
            (swLFallProd (N - r - 1) (L - 1 - w) * (N - r - w) *
              swLFallProd (N - r - 1) w) := by rw [hc1, hc2, hc4]
  have hd1 : m * w.factorial = m.factorial := (Nat.factorial_succ w).symm
  have hd2 : m.factorial * (N - m + 1).choose m = swLFallProd (N - w) m := by
    rw [show N - m + 1 = N - w by omega]; exact factorial_mul_choose_eq_swLFallProd (by omega)
  have hd3 : (L - 1 - w).factorial * (N - 2 * m + 1).choose (L - m) =
      swLFallProd (N - 2 * m + 1) (L - m) := by
    rw [show L - 1 - w = L - m by omega]; exact factorial_mul_choose_eq_swLFallProd (by omega)
  have hden_eq : scale * ((r - w) * den) =
      common * (swLFallProd (N - 2 * m + 1) (L - m) * swLFallProd (N - w) m) := by
    dsimp [scale, den, swLCaaNat, swLQNormSqNat, common]
    calc
      (w.factorial * (L - 1 - w).factorial) *
          ((r - w) *
            ((L - 1).factorial * m * (N - 2 * m + 1).choose (L - m) *
              (r.factorial * (N - r).factorial * (r - m).factorial * (N - r - m).factorial *
                (N - m + 1).choose m)))
          = (r - w) * (L - 1).factorial * r.factorial * (r - m).factorial *
              (N - r).factorial * (N - r - m).factorial *
              (((L - 1 - w).factorial * (N - 2 * m + 1).choose (L - m)) *
                ((m * w.factorial) * (N - m + 1).choose m)) := by ring
      _ = (r - w) * (L - 1).factorial * r.factorial * (r - m).factorial *
            (N - r).factorial * (N - r - m).factorial *
            (swLFallProd (N - 2 * m + 1) (L - m) * swLFallProd (N - w) m) := by
          rw [hd3, hd1, hd2]
  have hnum_ge : common * (N - r - L) ^ L ≤
      scale * ((N - r - w) * swLOrbitCardNat L N r j * b0 ^ 2) := by
    rw [hnum_eq]; refine Nat.mul_le_mul_left common ?_
    have hp1 := pow_le_swLFallProd (N - r - L) (N - r - 1) (L - 1 - w) (fun _ _ ↦ by omega)
    have hp2 : N - r - L ≤ N - r - w := (by omega)
    have hp3 := pow_le_swLFallProd (N - r - L) (N - r - 1) w (fun _ _ ↦ by omega)
    calc (N - r - L) ^ L = (N - r - L) ^ (L - 1 - w) * (N - r - L) * (N - r - L) ^ w := by
            have hexp : (L - 1 - w) + 1 + w = L := (by omega)
            calc
              (N - r - L) ^ L = (N - r - L) ^ ((L - 1 - w) + 1 + w) := by rw [hexp]
              _ = (N - r - L) ^ (L - 1 - w) * (N - r - L) * (N - r - L) ^ w := by ring
      _ ≤ swLFallProd (N - r - 1) (L - 1 - w) * (N - r - w) * swLFallProd (N - r - 1) w :=
        Nat.mul_le_mul (Nat.mul_le_mul hp1 hp2) hp3
  have hden_le : scale * ((r - w) * den) ≤ common * N ^ L := by
    rw [hden_eq]; refine Nat.mul_le_mul_left common ?_
    have hp1 := swLFallProd_le_pow (show N - 2 * m + 1 ≤ N by omega) (L - m)
    have hp2 := swLFallProd_le_pow (show N - w ≤ N by omega) m
    calc swLFallProd (N - 2 * m + 1) (L - m) * swLFallProd (N - w) m ≤ N ^ (L - m) * N ^ m :=
          Nat.mul_le_mul hp1 hp2
      _ = N ^ L := by rw [← pow_add, show L - m + m = L by omega]
  exact nat_scaled_ratio_ge hcommon_pos (Nat.mul_pos hrw_pos hden_pos)
    (Nat.pow_pos (by omega)) hnum_ge hden_le
end SwLOverlapInternal
theorem isValidSwLOverlap_of_orth_and_diag {L : ℕ} {M : Fin (2 * L) → Fin (2 * L) → ℝ} (hcol : ∀ i
    j : Fin (2 * L), ∑ o : Fin (2 * L), M o i * M o j = if i = j then 1 else 0) (hrow : ∀ o j :
    Fin (2 * L), ∑ k : Fin (2 * L), M o k * M j k = if o = j then 1 else 0) (hnonneg : ∀ j : Fin
    (2 * L), 0 ≤ M j j) (hsq : ∀ j : Fin (2 * L), 1 - (1 : ℝ) / 10 ^ 18 ≤ (M j j) ^ 2) :
    SchurWeylLCert.IsValidSwLOverlap M := by
  refine ⟨hcol, hrow, fun j ↦ ?_, fun o j hoj ↦ ?_⟩
  · have hcol_j : ∑ o : Fin (2 * L), (M o j) ^ 2 = 1 := (by simpa [sq] using hcol j j)
    have hle1_sq : (M j j) ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [one_pow, ← hcol_j]
      exact Finset.single_le_sum (fun o _ ↦ sq_nonneg (M o j)) (Finset.mem_univ j)
    have hle1 : M j j ≤ 1 := (SwLOverlapInternal.bounds_of_sq_le_sq zero_le_one hle1_sq).2
    have hge_sq : (1 - (1 : ℝ) / 10 ^ 9) ^ 2 ≤ (M j j) ^ 2 := by
      have hnum : (1 - (1 : ℝ) / 10 ^ 9) ^ 2 ≤ 1 - (1 : ℝ) / 10 ^ 18 := (by norm_num)
      exact hnum.trans (hsq j)
    have hge : 1 - (1 : ℝ) / 10 ^ 9 ≤ M j j := by
      by_contra hlt
      have hp : 0 < (1 - (1 : ℝ) / 10 ^ 9 - M j j) * (1 - (1 : ℝ) / 10 ^ 9 + M j j) :=
        mul_pos (by linarith) (by linarith [hnonneg j])
      have heq : (1 - (1 : ℝ) / 10 ^ 9 - M j j) * (1 - (1 : ℝ) / 10 ^ 9 + M j j) =
          (1 - (1 : ℝ) / 10 ^ 9) ^ 2 - (M j j) ^ 2 := by ring
      linarith
    exact ⟨hge, hle1, hsq j⟩
  · have hcol_j : ∑ k : Fin (2 * L), (M k j) ^ 2 = 1 := (by simpa [sq] using hcol j j)
    have hpair : (M o j) ^ 2 + (M j j) ^ 2 ≤ 1 := by
      rw [← hcol_j]
      have hsub : ({o, j} : Finset (Fin (2 * L))) ⊆ Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ ↦ sq_nonneg (M k j))
      rwa [Finset.sum_pair hoj] at hle
    have hoff_sq : (M o j) ^ 2 ≤ ((1 : ℝ) / 10 ^ 9) ^ 2 := by
      have h18 : ((1 : ℝ) / 10 ^ 9) ^ 2 = (1 : ℝ) / 10 ^ 18 := (by norm_num)
      linarith [hsq j, hpair, h18]
    exact abs_le.mpr (SwLOverlapInternal.bounds_of_sq_le_sq (by norm_num) hoff_sq)
theorem swLDiagOverlap_bounds {L n r : ℕ} (hL : 2 ≤ L) (hL8 : L ≤ 8) (hn : 96 ≤ n) (hrL : L ≤ r)
    (hr1024 : r ≤ 1024) (j : Fin (2 * L)) : 0 ≤ swLDiagOverlap L (2 ^ n) r j ∧ 1 - (1 : ℝ) / 10 ^
    18 ≤ (swLDiagOverlap L (2 ^ n) r j) ^ 2 := by
  let N : ℕ := 2 ^ n
  have hN28 : 10 ^ 28 ≤ N :=
    le_trans (by norm_num : 10 ^ 28 ≤ 2 ^ 96) (Nat.pow_le_pow_right (by omega) hn)
  have hN_bound : 2 * r + L ≤ N := (by omega); have hrat_tol : 1 - (1 : ℝ) / (2 * 10 ^ 18) ≤
      (((N - r - L) ^ L : ℕ) : ℝ) / ((N ^ L : ℕ) : ℝ) := by
    have h := SwLOverlapInternal.ratio_pow_ge_half_tol hL8 hn hr1024 (r := r)
    simpa [N, div_pow] using h
  have htail_tol := SwLOverlapInternal.tail_factor_ge_half_tol (L := L) hL8 hn hr1024
  unfold swLDiagOverlap; dsimp only; split_ifs with hj0 hjodd
  · -- Branch 1: j.1 = 0
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    rw [Real.sq_sqrt (by positivity)]; have hoc_eq : swLOrbitCardNat L N r j =
        (N - r) * SwLOverlapInternal.swLFallProd (N - r - 1) (L - 1) := by
      have hev : j.1 % 2 = 0 := (by omega); have hdiv : j.1 / 2 = 0 := (by omega)
      rw [SwLOverlapInternal.swLOrbitCardNat_even hev, hdiv]
      simp [SwLOverlapInternal.factorial_mul_choose_eq_swLFallProd
        (show L - 1 ≤ N - r - 1 by omega)]
    have hoc_ge : (N - r - L) ^ L ≤ swLOrbitCardNat L N r j := by
      rw [hoc_eq]; have hp1 : N - r - L ≤ N - r := (by omega)
      have hp2 := SwLOverlapInternal.pow_le_swLFallProd (N - r - L) (N - r - 1) (L - 1)
        (fun _ _ ↦ by omega)
      calc
        (N - r - L) ^ L = (N - r - L) * (N - r - L) ^ (L - 1) := by
          have hexp : (L - 1) + 1 = L := (by omega)
          calc
            (N - r - L) ^ L = (N - r - L) ^ ((L - 1) + 1) := by rw [hexp]
            _ = (N - r - L) * (N - r - L) ^ (L - 1) := by ring
        _ ≤ (N - r) * SwLOverlapInternal.swLFallProd (N - r - 1) (L - 1) := Nat.mul_le_mul hp1 hp2
    have hden_le : L.factorial * N.choose L ≤ N ^ L := by
      rw [SwLOverlapInternal.factorial_mul_choose_eq_swLFallProd (show L ≤ N by omega)]
      exact SwLOverlapInternal.swLFallProd_le_pow le_rfl L
    have hden_pos : 0 < L.factorial * N.choose L :=
      Nat.mul_pos (Nat.factorial_pos L) (Nat.choose_pos (by omega))
    have hbr1 : (((N - r - L) ^ L : ℕ) : ℝ) / ((N ^ L : ℕ) : ℝ) ≤
        (swLOrbitCardNat L N r j : ℝ) / ((L.factorial * N.choose L : ℕ) : ℝ) :=
      SwLOverlapInternal.nat_scaled_ratio_ge (scale := 1) (common := 1) (by omega) hden_pos
        (Nat.pow_pos (by omega)) (by simpa using hoc_ge) (by simpa using hden_le)
    linarith
  · -- Branch 2: j.1 % 2 = 1
    let m : ℕ := (j.1 + 1) / 2; have hm1 : 1 ≤ m := (by omega); have hmL : m ≤ L := (by omega)
    have hraw_ge : (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) * (SwLOverlapInternal.swLTermFac
      N r m 1 (m - 1) : ℝ) ≤ swLRawLiftAOnOrbit L N r m 1 (m - 1) := by
      have h := SwLOverlapInternal.swLRawLiftAOnOrbit_signed_ge (L := L) (N := N) (r := r)
        (m := m) (b := 1) le_rfl hL hL8 hm1 hmL (by omega) hN_bound
      simpa using h
    have hlhs_nn : 0 ≤ (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) :=
      mul_nonneg htail_tol.1 (Nat.cast_nonneg _)
    have hraw_nn : 0 ≤ swLRawLiftAOnOrbit L N r m 1 (m - 1) := hlhs_nn.trans hraw_ge
    refine ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hraw_nn) (Real.sqrt_nonneg _), ?_⟩
    have hraw_sq : (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
      (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) ^ 2 ≤ (swLRawLiftAOnOrbit L N r m 1 (m -
      1)) ^ 2 := SwLOverlapInternal.mul_sq_le_sq_of_nonneg hlhs_nn hraw_ge
    obtain ⟨hden_pos, hrat2⟩ := SwLOverlapInternal.branch2_ratio_ge hL hrL hN_bound hjodd
    have hdenR_pos : (0 : ℝ) < ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) := by
      exact_mod_cast hden_pos
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    have hstep1 : (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * (((swLOrbitCardNat L N r
      j * (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) / ((swLCaaNat L N m *
      swLQNormSqNat N r m : ℕ) : ℝ)) ≤ ((swLOrbitCardNat L N r j : ℝ) * (swLRawLiftAOnOrbit L N r
      m 1 (m - 1)) ^ 2) / ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) := by
      apply SwLOverlapInternal.le_div_of_mul_le hdenR_pos
      have h1 : (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * (((swLOrbitCardNat L N r j *
        (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) / ((swLCaaNat L N m *
        swLQNormSqNat N r m : ℕ) : ℝ)) * ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) =
        (swLOrbitCardNat L N r j : ℝ) * ((1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
        (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) ^ 2) := by
        rw [mul_assoc, div_mul_cancel₀ _ hdenR_pos.ne']; push_cast; ring
      rw [h1]; exact mul_le_mul_of_nonneg_left hraw_sq (Nat.cast_nonneg _)
    have hstep2 : (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) ≤
        (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
          (((swLOrbitCardNat L N r j *
            (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) /
            ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) :=
      mul_le_mul htail_tol.2 (hrat_tol.trans hrat2) (by norm_num) (sq_nonneg _)
    have hcomb : 1 - (1 : ℝ) / 10 ^ 18 ≤
        (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) := by norm_num
    exact hcomb.trans (hstep2.trans hstep1)
  · -- Branch 3: j.1 ≠ 0 and j.1 % 2 = 0
    have heven : j.1 % 2 = 0 := (by omega); let w : ℕ := j.1 / 2; let m : ℕ := w + 1
    have hmL : m ≤ L := (by omega)
    have hraw_ge : (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) * (SwLOverlapInternal.swLTermFac
      N r m 0 w : ℝ) ≤ -swLRawLiftAOnOrbit L N r m 0 w := by
      have h := SwLOverlapInternal.swLRawLiftAOnOrbit_signed_ge (L := L) (N := N) (r := r)
        (m := m) (b := 0) (by omega) hL hL8 (by omega) hmL (by omega) hN_bound
      simpa [m] using h
    have hlhs_nn : 0 ≤ (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
      (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) := mul_nonneg htail_tol.1 (Nat.cast_nonneg _)
    have hraw_nn : 0 ≤ -swLRawLiftAOnOrbit L N r m 0 w := hlhs_nn.trans hraw_ge
    have hrew : (-√(((N - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ))) *
        (√(swLOrbitCardNat L N r j : ℝ) * swLRawLiftAOnOrbit L N r m 0 w /
          √((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) =
        √(((N - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ)) *
          (√(swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) /
            √((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) := by ring
    rw [hrew]
    refine ⟨mul_nonneg (Real.sqrt_nonneg _)
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hraw_nn) (Real.sqrt_nonneg _)), ?_⟩
    have hraw_sq : (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
      (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) ^ 2 ≤ (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 :=
      SwLOverlapInternal.mul_sq_le_sq_of_nonneg hlhs_nn hraw_ge
    obtain ⟨hden_pos, hrw_pos, hrat3⟩ :=
      SwLOverlapInternal.branch3_ratio_ge hL hrL hN_bound hj0 heven
    have htot_den_pos : (0 : ℝ) <
        (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hrw_pos hden_pos
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    have hsq_eq : (((N - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ)) * ((swLOrbitCardNat L N r j : ℝ) *
      (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 / ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) =
      (((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) ^
      2) / (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
      rw [div_mul_div_comm]; have hnum_r : ((N - r - w : ℕ) : ℝ) *
          ((swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2) =
          ((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) *
            (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 := by ring
      have hden_r : ((r - w : ℕ) : ℝ) * ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) =
          (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
        push_cast; ring
      rw [hnum_r, hden_r]
    rw [hsq_eq]
    have hstep1 : (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * ((((N - r - w) *
      swLOrbitCardNat L N r j * (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) / (((r -
      w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ)) ≤ (((N - r - w : ℕ) : ℝ) *
      (swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2) / (((r - w) *
      (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
      apply SwLOverlapInternal.le_div_of_mul_le htot_den_pos
      have h1 : (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * ((((N - r - w) *
        swLOrbitCardNat L N r j * (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) / (((r -
        w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ)) * (((r - w) * (swLCaaNat L N m *
        swLQNormSqNat N r m) : ℕ) : ℝ) = ((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) *
        ((1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * (SwLOverlapInternal.swLTermFac N r m
        0 w : ℝ) ^ 2) := by
        rw [mul_assoc, div_mul_cancel₀ _ htot_den_pos.ne']; push_cast; ring
      rw [h1]; exact mul_le_mul_of_nonneg_left hraw_sq (by positivity)
    have hstep2 : (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) ≤
        (1 - (1024 * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
          ((((N - r - w) * swLOrbitCardNat L N r j *
            (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) /
            (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ)) :=
      mul_le_mul htail_tol.2 (hrat_tol.trans hrat3) (by norm_num) (sq_nonneg _)
    have hcomb : 1 - (1 : ℝ) / 10 ^ 18 ≤
        (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) := by norm_num
    exact hcomb.trans (hstep2.trans hstep1)
end QuantumComputation.Specs.GroverFindAll
