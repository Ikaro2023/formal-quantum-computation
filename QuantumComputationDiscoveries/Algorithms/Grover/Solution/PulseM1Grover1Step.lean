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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistBasis2L
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLQHL
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistOverlap2L
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylL2BallCertDefs
/-
# Multi-pulse Overlap/Angle Bridge & Head-Plane Grover Step (`PulseM1Grover1Step`)
-/
section Sec_PulseHdistOverlapAndAngles
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll
open Real
open scoped BigOperators
/-
 ## 1. Multi-pulse-Rank (`2 ≤ L ≤ 1024`, `1152 ≤ n`) Diagonal Dominance for `H_dist` Overlap
-/
namespace SwLOverlapPulseInternal
theorem swLRawLiftAOnOrbit_signed_ge_of_bounds {L N r m b K M : ℕ} (hb : b ≤ 1) (hL : 2 ≤ L) (hm1 :
  1 ≤ m) (hmL : m ≤ L) (hr : m ≤ r) (hN : 2 * r + L ≤ N) (hK : 2 ^ (L - 1) ≤ K) (hM : (m - 1) * K ≤
  M) : (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m
  - 1) : ℝ) ≤ (-1 : ℝ) ^ (b + 1) * swLRawLiftAOnOrbit L N r m b (m - 1) := by
  let B : ℕ := N - r - L
  have hBpos : (0 : ℝ) < (B : ℝ) := (by have : 0 < B := (by omega); exact_mod_cast this)
  let term : ℕ → ℝ := fun u ↦ (((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) : ℕ) : ℝ) *
    (-1 : ℝ) ^ (m + (b + u)) * ((SwLOverlapInternal.swLTermFac N r m b u : ℕ) : ℝ)
  have hdef : swLRawLiftAOnOrbit L N r m b (m - 1) = ∑ u ∈ Finset.range m, term u := rfl
  have hrange : Finset.range m = Finset.range ((m - 1) + 1) := congrArg Finset.range (by omega)
  rw [hdef, hrange, Finset.sum_range_succ, mul_add]; have htop : (-1 : ℝ) ^ (b + 1) * term (m - 1) =
      (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
    dsimp [term]; rw [Nat.choose_self, Nat.sub_self, Nat.choose_zero_right]
    have hsgn : (-1 : ℝ) ^ (b + 1) * (-1 : ℝ) ^ (m + (b + (m - 1))) = 1 := by
      rw [← pow_add, show (b + 1) + (m + (b + (m - 1))) = 2 * (b + m) by omega, pow_mul]; norm_num
    calc
      (-1 : ℝ) ^ (b + 1) * (((1 * 1 : ℕ) : ℝ) * (-1 : ℝ) ^ (m + (b + (m - 1))) *
            (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ))
          = ((-1 : ℝ) ^ (b + 1) * (-1 : ℝ) ^ (m + (b + (m - 1)))) *
              (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by push_cast; ring
      _ = (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by rw [hsgn, one_mul]
  have htail_term : ∀ u ∈ Finset.range (m - 1), (B : ℝ) * |term u| ≤
        ((K : ℝ) * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
    intro u hu; have hu_lt : u < m - 1 := Finset.mem_range.mp hu
    have habs : |term u| = (((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) : ℕ) : ℝ) *
          (SwLOverlapInternal.swLTermFac N r m b u : ℝ) := by
      dsimp [term]; rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_nonneg
        (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    have hc_prod : (m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u) ≤ K := by
      have hc1 := SwLOverlapInternal.choose_le_two_pow (m - 1) u; have hc2 :=
        SwLOverlapInternal.choose_le_two_pow (L - 1 - (m - 1)) (m - 1 - u); refine (Nat.mul_le_mul
        hc1 hc2).trans ?_; rw [← pow_add, show m - 1 + (L - 1 - (m - 1)) = L - 1 by omega]; exact hK
    have hfac : B * SwLOverlapInternal.swLTermFac N r m b u ≤ r * SwLOverlapInternal.swLTermFac N r
      m b (m - 1) := SwLOverlapInternal.swLTermFac_tail_bound hb hL hmL hr hN hu_lt
    have hnat : ((m - 1).choose u * (L - 1 - (m - 1)).choose (m - 1 - u)) * (B *
      SwLOverlapInternal.swLTermFac N r m b u) ≤ K * (r * SwLOverlapInternal.swLTermFac N r m b (m -
      1)) := Nat.mul_le_mul hc_prod hfac; have hreal : (((m - 1).choose u * (L - 1 - (m - 1)).choose
      (m - 1 - u) : ℕ) : ℝ) * ((B : ℝ) * (SwLOverlapInternal.swLTermFac N r m b u : ℝ)) ≤ (K : ℝ) *
      ((r : ℝ) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) := (by exact_mod_cast hnat)
    rw [habs]; linarith
  have htail_sum : (B : ℝ) * |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤
      ((M : ℝ) * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
    have habs_sgn : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| =
        |∑ u ∈ Finset.range (m - 1), term u| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [habs_sgn]
    have h1 : (B : ℝ) * |∑ u ∈ Finset.range (m - 1), term u| ≤
        (B : ℝ) * ∑ u ∈ Finset.range (m - 1), |term u| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hBpos.le
    have h2 : (B : ℝ) * ∑ u ∈ Finset.range (m - 1), |term u| ≤ ((m - 1 : ℕ) : ℝ) *
          (((K : ℝ) * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) := by
      rw [Finset.mul_sum]; refine (Finset.sum_le_sum htail_term).trans ?_; simp [Finset.sum_const,
        nsmul_eq_mul]
    have hmK : ((m - 1 : ℕ) : ℝ) * (K : ℝ) ≤ (M : ℝ) := (by exact_mod_cast hM)
    have h3 : ((m - 1 : ℕ) : ℝ) * (((K : ℝ) * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m -
      1) : ℝ)) ≤ ((M : ℝ) * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
      have hrew1 : ((m - 1 : ℕ) : ℝ) * (((K : ℝ) * (r : ℝ)) * (SwLOverlapInternal.swLTermFac N r m b
        (m - 1) : ℝ)) = (((m - 1 : ℕ) : ℝ) * (K : ℝ)) * ((r : ℝ) * (SwLOverlapInternal.swLTermFac N
        r m b (m - 1) : ℝ)) := (by ring); have hrew2 : ((M : ℝ) * (r : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) = (M : ℝ) * ((r : ℝ) *
        (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) := (by ring)
      rw [hrew1, hrew2]; exact mul_le_mul_of_nonneg_right hmK (by positivity)
    exact (h1.trans h2).trans h3
  have htail_div : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤
      (((M : ℝ) * (r : ℝ)) / (B : ℝ)) *
        (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ) := by
    have h2 : |(-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u| ≤ (((M : ℝ) * (r : ℝ)) *
          (SwLOverlapInternal.swLTermFac N r m b (m - 1) : ℝ)) / (B : ℝ) := by
      apply SwLOverlapInternal.le_div_of_mul_le hBpos; linarith [htail_sum]
    simpa [mul_div_right_comm] using h2
  have hneg := neg_le_abs ((-1 : ℝ) ^ (b + 1) * ∑ u ∈ Finset.range (m - 1), term u); rw [htop]
  linarith
theorem ratio_pow_ge_half_tol_of_le {L N r : ℕ} (hN_pos : 0 < N) (hrL : r + L ≤ N) (hbound : 2 * 10
  ^ 18 * (L * (r + L)) ≤ N) : 1 - (1 : ℝ) / (2 * 10 ^ 18) ≤ (((N - r - L : ℕ) : ℝ) / (N : ℝ)) ^ L :=
  by
  have hNR_pos : (0 : ℝ) < (N : ℝ) := (by exact_mod_cast hN_pos)
  have hsub_eq : ((N - r - L : ℕ) : ℝ) / (N : ℝ) = 1 - ((r + L : ℕ) : ℝ) / (N : ℝ) :=
    (by rw [Nat.sub_sub, Nat.cast_sub hrL, sub_div, div_self hNR_pos.ne']); have hx0 : 0 ≤ ((r + L :
    ℕ) : ℝ) / (N : ℝ) := (by positivity)
  have hx1 : ((r + L : ℕ) : ℝ) / (N : ℝ) ≤ 1 := by
    apply SwLOverlapInternal.div_le_of_le_mul hNR_pos; have hR : ((r + L : ℕ) : ℝ) ≤ (N : ℝ) :=
      (by exact_mod_cast hrL); linarith
  have hbern := SwLOverlapInternal.one_sub_mul_le_pow hx0 hx1 L; rw [hsub_eq]
  have herr : (L : ℝ) * (((r + L : ℕ) : ℝ) / (N : ℝ)) ≤ (1 : ℝ) / (2 * 10 ^ 18) := by
    set X : ℝ := (L : ℝ) * ((r + L : ℕ) : ℝ)
    have hboundR : (2 * 10 ^ 18 : ℝ) * X ≤ (N : ℝ) := by
      have h1 : (((2 * 10 ^ 18) * (L * (r + L)) : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 hbound
      have heq : (((2 * 10 ^ 18) * (L * (r + L)) : ℕ) : ℝ) = (2 * 10 ^ 18 : ℝ) * X :=
        (by dsimp [X]; rw [Nat.cast_mul, Nat.cast_mul]; norm_num)
      rwa [heq] at h1
    have hdiv : X / (N : ℝ) ≤ (1 : ℝ) / (2 * 10 ^ 18) :=
      (by apply SwLOverlapInternal.div_le_of_le_mul hNR_pos; linarith)
    rw [← mul_div_assoc]; exact hdiv
  linarith
theorem tail_factor_ge_half_tol_of_le {M r B : ℕ} (hB0 : 0 < B) (hMB : 4 * 10 ^ 18 * (M * r) ≤ B) :
  0 ≤ 1 - ((M : ℝ) * (r : ℝ)) / (B : ℝ) ∧ 1 - (1 : ℝ) / (2 * 10 ^ 18) ≤ (1 - ((M : ℝ) * (r : ℝ)) /
  (B : ℝ)) ^ 2 := by
  have hBpos : (0 : ℝ) < (B : ℝ) := (by exact_mod_cast hB0)
  have hy : ((M : ℝ) * (r : ℝ)) / (B : ℝ) ≤ (1 : ℝ) / (4 * 10 ^ 18) := by
    apply SwLOverlapInternal.div_le_of_le_mul hBpos; have hMBR : ((4 * 10 ^ 18 : ℕ) : ℝ) * ((M : ℝ)
      * (r : ℝ)) ≤ (B : ℝ) := (by exact_mod_cast hMB); push_cast at hMBR; linarith
  refine ⟨by linarith, ?_⟩
  have hsq : 1 - 2 * (((M : ℝ) * (r : ℝ)) / (B : ℝ)) ≤ (1 - ((M : ℝ) * (r : ℝ)) / (B : ℝ)) ^ 2 := by
    have hnn : 0 ≤ (((M : ℝ) * (r : ℝ)) / (B : ℝ)) ^ 2 := sq_nonneg _; linarith [show (1 - ((M : ℝ)
      * (r : ℝ)) / (B : ℝ)) ^ 2 = 1 - 2 * (((M : ℝ) * (r : ℝ)) / (B : ℝ)) + (((M : ℝ) * (r : ℝ)) /
      (B : ℝ)) ^ 2 by ring]
  linarith
theorem pulse_nat_budget {L n r : ℕ} (hL1024 : L ≤ 1024) (hn : 1152 ≤ n) (hr1024 : r ≤ 1024) : 2 *
  r + L ≤ 2 ^ n ∧ 0 < 2 ^ n - r - L ∧ 2 * 10 ^ 18 * (L * (r + L)) ≤ 2 ^ n ∧ ∃ K M : ℕ, 2 ^ (L - 1) ≤
  K ∧ (∀ m, m ≤ L → (m - 1) * K ≤ M) ∧ 4 * 10 ^ 18 * (M * r) ≤ 2 ^ n - r - L := by
  have h2rL : 2 * r + L ≤ 2 ^ 12 := (by omega : 2 * r + L ≤ 3072).trans (by norm_num)
  have h12_n : 2 ^ 12 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
  have h2rL_N : 2 * r + L ≤ 2 ^ n := h2rL.trans h12_n
  have hB_pos : 0 < 2 ^ n - r - L := by
    have hrL_lt : r + L < 2 ^ 12 := (by omega : r + L < 4096); have hrL_lt_N : r + L < 2 ^ n :=
      hrL_lt.trans_le h12_n; rw [Nat.sub_sub]; exact Nat.sub_pos_of_lt hrL_lt_N
  have hrat_N : 2 * 10 ^ 18 * (L * (r + L)) ≤ 2 ^ n := by
    have h1 : L * (r + L) ≤ 1024 * 2048 := Nat.mul_le_mul hL1024 (by omega); have h2 : 2 * 10 ^ 18 *
      (L * (r + L)) ≤ 2 ^ 83 := (Nat.mul_le_mul_left _ h1).trans (by norm_num)
    exact h2.trans (Nat.pow_le_pow_right (by omega) (by omega))
  set e : ℕ := L - 1
  have htail_B : 4 * 10 ^ 18 * ((L * 2 ^ e) * r) ≤ 2 ^ n - r - L := by
    have hLr : L * r ≤ 1024 * 1024 := Nat.mul_le_mul hL1024 hr1024; have hcLr : 4 * 10 ^ 18 * (L *
      r) ≤ 2 ^ 83 := (Nat.mul_le_mul_left _ hLr).trans (by norm_num); have hrew : 4 * 10 ^ 18 * ((L
      * 2 ^ e) * r) = (4 * 10 ^ 18 * (L * r)) * 2 ^ e := (by ring)
    have hprod : 4 * 10 ^ 18 * ((L * 2 ^ e) * r) ≤ 2 ^ (83 + e) :=
      (by rw [hrew, Nat.pow_add]; exact Nat.mul_le_mul_right (2 ^ e) hcLr)
    have hrL_pow : r + L ≤ 2 ^ (83 + e) := ((by omega : r + L ≤ 2048).trans
      (by norm_num : 2048 ≤ 2 ^ 12)).trans (Nat.pow_le_pow_right (by omega) (Nat.le_trans
      (by omega : 12 ≤ 83) (Nat.le_add_right 83 e)))
    have hsum : 4 * 10 ^ 18 * ((L * 2 ^ e) * r) + (r + L) ≤ 2 ^ (83 + e + 1) := by
      rw [Nat.pow_succ 2 (83 + e), Nat.mul_two (2 ^ (83 + e))]; exact Nat.add_le_add hprod hrL_pow
    rw [Nat.sub_sub]; exact Nat.le_sub_of_add_le (hsum.trans (Nat.pow_le_pow_right (by omega)
      (by omega)))
  refine ⟨h2rL_N, hB_pos, hrat_N, 2 ^ e, L * 2 ^ e, le_rfl, ?_, htail_B⟩
  intro m hmL; exact Nat.mul_le_mul_right (2 ^ e) (by omega)
end SwLOverlapPulseInternal
theorem swLDiagOverlap_bounds_pulse {L n r : ℕ} (hL : 2 ≤ L) (hL1024 : L ≤ 1024) (hn : 1152 ≤ n)
  (hrL : L ≤ r) (hr1024 : r ≤ 1024) (j : Fin (2 * L)) : 0 ≤ swLDiagOverlap L (2 ^ n) r j ∧ 1 - (1 :
  ℝ) / 10 ^ 18 ≤ (swLDiagOverlap L (2 ^ n) r j) ^ 2 := by
  let N : ℕ := 2 ^ n
  rcases SwLOverlapPulseInternal.pulse_nat_budget hL1024 hn hr1024 with ⟨hN_bound, hB_pos,
    hrat_N, K, M, hK, hKM, htail_B⟩; have hN_pos : 0 < N := Nat.two_pow_pos n; have hrL_N : r + L ≤
    N := (by omega)
  have hrat_tol : 1 - (1 : ℝ) / (2 * 10 ^ 18) ≤ (((N - r - L) ^ L : ℕ) : ℝ) / ((N ^ L : ℕ) : ℝ)
    := by
    have h := SwLOverlapPulseInternal.ratio_pow_ge_half_tol_of_le hN_pos hrL_N hrat_N; simpa [N,
      div_pow] using h
  have htail_tol := SwLOverlapPulseInternal.tail_factor_ge_half_tol_of_le hB_pos htail_B
  unfold swLDiagOverlap; dsimp only; split_ifs with hj0 hjodd
  · refine ⟨Real.sqrt_nonneg _, ?_⟩; rw [Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg _))]
    have hoc_eq : swLOrbitCardNat L N r j = (N - r) * SwLOverlapInternal.swLFallProd (N - r - 1) (L
      - 1) := by
      have hev : j.1 % 2 = 0 := (by omega); have hdiv : j.1 / 2 = 0 := (by omega)
      rw [SwLOverlapInternal.swLOrbitCardNat_even hev, hdiv]
      simp [SwLOverlapInternal.factorial_mul_choose_eq_swLFallProd (show L - 1 ≤ N - r - 1
        by omega)]
    have hoc_ge : (N - r - L) ^ L ≤ swLOrbitCardNat L N r j := by
      rw [hoc_eq]; have hp1 : N - r - L ≤ N - r := (by omega); have hp2 :=
        SwLOverlapInternal.pow_le_swLFallProd (N - r - L) (N - r - 1) (L - 1) (fun _ _ ↦ by omega)
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
    have hden_pos : 0 < L.factorial * N.choose L := Nat.mul_pos (Nat.factorial_pos L)
      (Nat.choose_pos (by omega))
    have hbr1 : (((N - r - L) ^ L : ℕ) : ℝ) / ((N ^ L : ℕ) : ℝ) ≤ (swLOrbitCardNat L N r j : ℝ) /
      ((L.factorial * N.choose L : ℕ) : ℝ) := SwLOverlapInternal.nat_scaled_ratio_ge (scale := 1)
      (common := 1) (by omega) hden_pos (Nat.pow_pos hN_pos) (by simpa using hoc_ge)
      (by simpa using hden_le); linarith
  · let m : ℕ := (j.1 + 1) / 2; have hm1 : 1 ≤ m := (by omega); have hmL : m ≤ L := (by omega)
    have hmK : (m - 1) * K ≤ M := hKM m hmL
    have hraw_ge : (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
      (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) ≤ swLRawLiftAOnOrbit L N r m 1 (m - 1)
      := by
      have h := SwLOverlapPulseInternal.swLRawLiftAOnOrbit_signed_ge_of_bounds (L := L) (N := N)
        (r := r) (m := m) (b := 1) le_rfl hL hm1 hmL (by omega) hN_bound hK hmK
      have hs : (-1 : ℝ) ^ (1 + 1) = 1 := (by norm_num); rw [hs, one_mul] at h; exact h
    have hlhs_nn : 0 ≤ (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
      (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) := mul_nonneg htail_tol.1 (Nat.cast_nonneg
      _); have hraw_nn : 0 ≤ swLRawLiftAOnOrbit L N r m 1 (m - 1) := hlhs_nn.trans hraw_ge
    refine ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hraw_nn) (Real.sqrt_nonneg _), ?_⟩
    have hraw_sq : (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
      (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) ^ 2 ≤ (swLRawLiftAOnOrbit L N r m 1 (m -
      1)) ^ 2 := SwLOverlapInternal.mul_sq_le_sq_of_nonneg hlhs_nn hraw_ge
    obtain ⟨hden_pos, hrat2⟩ := SwLOverlapInternal.branch2_ratio_ge hL hrL hN_bound hjodd
    have hdenR_pos : (0 : ℝ) < ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) :=
      (by exact_mod_cast hden_pos); rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    have hstep1 : (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * (((swLOrbitCardNat L N r j
      * (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) / ((swLCaaNat L N m *
      swLQNormSqNat N r m : ℕ) : ℝ)) ≤ ((swLOrbitCardNat L N r j : ℝ) * (swLRawLiftAOnOrbit L N r m
      1 (m - 1)) ^ 2) / ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) := by
      apply SwLOverlapInternal.le_div_of_mul_le hdenR_pos
      have h1 : (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * (((swLOrbitCardNat L N r j *
        (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) / ((swLCaaNat L N m *
        swLQNormSqNat N r m : ℕ) : ℝ)) * ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) =
        (swLOrbitCardNat L N r j : ℝ) * ((1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
        (SwLOverlapInternal.swLTermFac N r m 1 (m - 1) : ℝ) ^ 2) :=
        (by rw [mul_assoc, div_mul_cancel₀ _ hdenR_pos.ne']; push_cast; ring)
      rw [h1]; exact mul_le_mul_of_nonneg_left hraw_sq (Nat.cast_nonneg _)
    have hstep2 : (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) ≤ (1 - ((M : ℝ) * (r
      : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * (((swLOrbitCardNat L N r j *
      (SwLOverlapInternal.swLTermFac N r m 1 (m - 1)) ^ 2 : ℕ) : ℝ) / ((swLCaaNat L N m *
      swLQNormSqNat N r m : ℕ) : ℝ)) := mul_le_mul htail_tol.2 (hrat_tol.trans hrat2) (by norm_num)
      (sq_nonneg _); have hcomb : 1 - (1 : ℝ) / 10 ^ 18 ≤ (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 :
      ℝ) / (2 * 10 ^ 18)) := (by norm_num); exact hcomb.trans (hstep2.trans hstep1)
  · have heven : j.1 % 2 = 0 := (by omega); let w : ℕ := j.1 / 2; let m : ℕ := w + 1; have hmL : m ≤
      L := (by omega); have hmK : (m - 1) * K ≤ M := hKM m hmL
    have hraw_ge : (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
      (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) ≤ -swLRawLiftAOnOrbit L N r m 0 w := by
      have h := SwLOverlapPulseInternal.swLRawLiftAOnOrbit_signed_ge_of_bounds (L := L) (N := N)
        (r := r) (m := m) (b := 0) (by omega) hL (by omega) hmL (by omega) hN_bound hK hmK
      have hs : (-1 : ℝ) ^ (0 + 1) = -1 := (by norm_num); have hmw : m - 1 = w := (by omega)
      rw [hs, hmw, neg_one_mul] at h; exact h
    have hlhs_nn : 0 ≤ (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) *
      (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) := mul_nonneg htail_tol.1 (Nat.cast_nonneg _)
    have hraw_nn : 0 ≤ -swLRawLiftAOnOrbit L N r m 0 w := hlhs_nn.trans hraw_ge; have hrew : (-√(((N
      - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ))) * (√(swLOrbitCardNat L N r j : ℝ) * swLRawLiftAOnOrbit
      L N r m 0 w / √((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) = √(((N - r - w : ℕ) : ℝ) /
      ((r - w : ℕ) : ℝ)) * (√(swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) /
      √((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) := (by ring); rw [hrew]
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hraw_nn)
      (Real.sqrt_nonneg _)), ?_⟩
    have hraw_sq : (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 *
      (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) ^ 2 ≤ (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 :=
      SwLOverlapInternal.mul_sq_le_sq_of_nonneg hlhs_nn hraw_ge
    obtain ⟨hden_pos, hrw_pos, hrat3⟩ := SwLOverlapInternal.branch3_ratio_ge hL hrL hN_bound hj0
      heven; have htot_den_pos : (0 : ℝ) < (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ)
      : ℝ) := (by exact_mod_cast Nat.mul_pos hrw_pos hden_pos); rw [mul_pow, div_pow, mul_pow,
      Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), Real.sq_sqrt
      (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    have hsq_eq : (((N - r - w : ℕ) : ℝ) / ((r - w : ℕ) : ℝ)) * ((swLOrbitCardNat L N r j : ℝ) *
      (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 / ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ)) =
      (((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) ^
      2) / (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
      rw [div_mul_div_comm]; have hnum_r : ((N - r - w : ℕ) : ℝ) *
          ((swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2) =
          ((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) *
            (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2 := by ring
      have hden_r : ((r - w : ℕ) : ℝ) * ((swLCaaNat L N m * swLQNormSqNat N r m : ℕ) : ℝ) = (((r -
        w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := (by push_cast; ring); rw [hnum_r,
        hden_r]
    rw [hsq_eq]
    have hstep1 : (1 - ((M : ℝ) * (r : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * ((((N - r - w) *
      swLOrbitCardNat L N r j * (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) / (((r - w)
      * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ)) ≤ (((N - r - w : ℕ) : ℝ) *
      (swLOrbitCardNat L N r j : ℝ) * (-swLRawLiftAOnOrbit L N r m 0 w) ^ 2) / (((r - w) *
      (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) : ℝ) := by
      apply SwLOverlapInternal.le_div_of_mul_le htot_den_pos; have h1 : (1 - ((M : ℝ) * (r : ℝ)) /
        ((N - r - L : ℕ) : ℝ)) ^ 2 * ((((N - r - w) * swLOrbitCardNat L N r j *
        (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) / (((r - w) * (swLCaaNat L N m *
        swLQNormSqNat N r m) : ℕ) : ℝ)) * (((r - w) * (swLCaaNat L N m * swLQNormSqNat N r m) : ℕ) :
        ℝ) = ((N - r - w : ℕ) : ℝ) * (swLOrbitCardNat L N r j : ℝ) * ((1 - ((M : ℝ) * (r : ℝ)) / ((N
        - r - L : ℕ) : ℝ)) ^ 2 * (SwLOverlapInternal.swLTermFac N r m 0 w : ℝ) ^ 2) :=
        (by rw [mul_assoc, div_mul_cancel₀ _ htot_den_pos.ne']; push_cast; ring); rw [h1]
      exact mul_le_mul_of_nonneg_left hraw_sq (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hstep2 : (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 : ℝ) / (2 * 10 ^ 18)) ≤ (1 - ((M : ℝ) * (r
      : ℝ)) / ((N - r - L : ℕ) : ℝ)) ^ 2 * ((((N - r - w) * swLOrbitCardNat L N r j *
      (SwLOverlapInternal.swLTermFac N r m 0 w) ^ 2 : ℕ) : ℝ) / (((r - w) * (swLCaaNat L N m *
      swLQNormSqNat N r m) : ℕ) : ℝ)) := mul_le_mul htail_tol.2 (hrat_tol.trans hrat3) (by norm_num)
      (sq_nonneg _); have hcomb : 1 - (1 : ℝ) / 10 ^ 18 ≤ (1 - (1 : ℝ) / (2 * 10 ^ 18)) * (1 - (1 :
      ℝ) / (2 * 10 ^ 18)) := (by norm_num); exact hcomb.trans (hstep2.trans hstep1)
theorem isValidSwLOverlap_swLOverlapMatFn_pulse {L n r : ℕ} (hL : 2 ≤ L) (hL1024 : L ≤ 1024) (hn :
  1152 ≤ n) {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hr1024 : r ≤ 1024) (hR : R.card = r) :
  SchurWeylLCert.IsValidSwLOverlap (swLOverlapMatFn L R) := by
  have : NeZero L := ⟨by omega⟩; have : NeZero (2 ^ n) := ⟨Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos
    n)⟩; have hL0 : L ≠ 0 := (by omega)
  rcases SwLOverlapPulseInternal.pulse_nat_budget hL1024 hn hr1024 with ⟨h2rL, _, _, _⟩
  have hrN : r + L ≤ 2 ^ n := (by omega); have hM : swLOverlapMatFn L R =
    SwLInternal.overlapTupleMat L (2 ^ n) R := (by unfold swLOverlapMatFn; rw [dite_eq_right hL0])
  rw [hM]; refine isValidSwLOverlap_of_orth_and_diag (SwLInternal.overlapTupleMat_col_orth hL hrL
    hrN hR) (SwLInternal.overlapTupleMat_row_orth hL hrL hrN hR) (fun j ↦ ?_) (fun j ↦ ?_)
  · rw [SwLInternal.overlapTupleMat_diag_eq hL hrL hrN hR j]; exact (swLDiagOverlap_bounds_pulse
      hL hL1024 hn hrL hr1024 j).1
  · rw [SwLInternal.overlapTupleMat_diag_eq hL hrL hrN hR j]; exact (swLDiagOverlap_bounds_pulse
      hL hL1024 hn hrL hr1024 j).2
namespace SchurWeylLCert
/- ## 2. `O(L)` Parseval + Frobenius Suffix `L2`-Norm & `p_0` Bounds (`swScale = 10^9`) -/
theorem swLOrbitProj_sub_linear {L : ℕ} (M : Fin (2 * L) → Fin (2 * L) → ℝ) (u v : Fin (2 * L) → ℝ)
  (o : Fin (2 * L)) : swLOrbitProj M u o - swLOrbitProj M v o = swLOrbitProj M (fun j ↦ u j - v j) o
  := by
  unfold swLOrbitProj; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ ↦ (mul_sub
    _ _ _).symm
theorem swLOrbitProj_sub_id_normSq_le {L : ℕ} (hL1024 : L ≤ 1024) {M : Fin (2 * L) → Fin (2 * L) →
  ℝ} (hM : IsValidSwLOverlap M) (v : Fin (2 * L) → ℝ) : swLNormSq (fun o ↦ swLOrbitProj M v o - v o)
  ≤ ((64 : ℝ) / (swScale : ℝ)) ^ 2 * swLNormSq v := by
  have hv_nn : 0 ≤ swLNormSq v := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hrow : ∀ o : Fin (2 * L), (swLOrbitProj M v o - v o) ^ 2 ≤ ((2 : ℝ) / 10 ^ 18) * swLNormSq v
    := by
    intro o; let w : Fin (2 * L) → ℝ := fun j ↦ M o j - if j = o then 1 else 0
    have hdiff : swLOrbitProj M v o - v o = ∑ j : Fin (2 * L), w j * v j := by
      unfold swLOrbitProj
      have hvo : v o = ∑ j : Fin (2 * L), (if j = o then (1 : ℝ) else 0) * v j := (by simp)
      conv_lhs => rw [hvo]
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ ↦ (sub_mul (M o j) _ (v
        j)).symm
    rw [hdiff]; have hcs := sum_mul_sq_le_normSq_mul w v
    have hw_sq : swLNormSq w = 2 * (1 - M o o) := by
      unfold swLNormSq; have hpt : ∀ j : Fin (2 * L),
          (w j) ^ 2 = (M o j) ^ 2 - if j = o then 2 * M o o - 1 else 0 := by
        intro j; dsimp [w]; split_ifs with hjo
        · subst hjo; ring
        · ring
      simp_rw [hpt, Finset.sum_sub_distrib]; have hro : ∑ j : Fin (2 * L), (M o j) ^ 2 = 1 :=
        (by simpa [sq] using hM.2.1 o o); have hite : ∑ j : Fin (2 * L), (if j = o then 2 * M o o -
        1 else 0) = 2 * M o o - 1 := (by simp); rw [hro, hite]; ring
    rcases hM.2.2.1 o with ⟨hd_lo, hd_hi, hd_sq⟩; have hd_nn : 0 ≤ M o o := (by linarith [hd_lo])
    have hmoo_sq_le : (M o o) ^ 2 ≤ M o o := (by rw [sq]; exact mul_le_of_le_one_right hd_nn hd_hi)
    have hw_le : swLNormSq w ≤ (2 : ℝ) / 10 ^ 18 := (by linarith [hw_sq, hd_sq, hmoo_sq_le])
    exact hcs.trans (mul_le_mul_of_nonneg_right hw_le hv_nn)
  unfold swLNormSq; have hsum : ∑ o : Fin (2 * L), (swLOrbitProj M v o - v o) ^ 2 ≤
      (2 * L : ℝ) * (((2 : ℝ) / 10 ^ 18) * swLNormSq v) := by
    have hcard := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin (2 * L))) (fun o ↦
      (swLOrbitProj M v o - v o) ^ 2) (((2 : ℝ) / 10 ^ 18) * swLNormSq v) (fun o _ ↦ hrow o)
    simpa [nsmul_eq_mul, Nat.cast_mul] using hcard
  have h2L : (2 * L : ℝ) ≤ 2048 := (by exact_mod_cast (by omega : 2 * L ≤ 2048)); have hmul : (2 * L
    : ℝ) * (((2 : ℝ) / 10 ^ 18) * swLNormSq v) ≤ 2048 * (((2 : ℝ) / 10 ^ 18) * swLNormSq v) :=
    mul_le_mul_of_nonneg_right h2L (by positivity); have hconst : (2048 : ℝ) * ((2 : ℝ) / 10 ^ 18) =
    ((64 : ℝ) / (swScale : ℝ)) ^ 2 := (by unfold swScale; norm_num)
  calc ∑ o : Fin (2 * L), (swLOrbitProj M v o - v o) ^ 2
    _ ≤ (2 * L : ℝ) * (((2 : ℝ) / 10 ^ 18) * swLNormSq v) := hsum
    _ ≤ 2048 * (((2 : ℝ) / 10 ^ 18) * swLNormSq v) := hmul
    _ = ((2048 : ℝ) * ((2 : ℝ) / 10 ^ 18)) * swLNormSq v := by ring
    _ = ((64 : ℝ) / (swScale : ℝ)) ^ 2 * swLNormSq v := by rw [hconst]
/- ### 2a. Pure-GMP Kernel WHNF Forcing & Self-Certifying Heron Square Roots -/
theorem solIntAdd_eq (a b : ℤ) : Int.add a b = a + b := rfl
theorem solIntSub_eq (a b : ℤ) : Int.sub a b = a - b := rfl
theorem solIntMul_eq (a b : ℤ) : Int.mul a b = a * b := rfl
theorem solIntEdiv_eq (a b : ℤ) : Int.ediv a b = a / b := rfl
theorem solNatAdd_eq (a b : ℕ) : Nat.add a b = a + b := rfl
theorem solNatSub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem solNatMul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem solNatDiv_eq (a b : ℕ) : Nat.div a b = a / b := rfl
theorem solNatBle_eq_decide : ∀ (a b : ℕ), Nat.ble a b = decide (a ≤ b)
  | 0, _ => rfl | _ + 1, 0 => rfl
  | a + 1, b + 1 => by simp only [Nat.ble, solNatBle_eq_decide a b, Nat.add_le_add_iff_right]
/-- Pure-GMP WHNF-forcing `ℕ` wrapper (`@Nat.casesOn` binds bare `Literal.natVal`). -/
def solForceNat {α : Type} (x : ℕ) (k : ℕ → α) : α :=
  @Nat.casesOn (fun _ ↦ α) (Nat.add 1 x) (k 0) k
theorem solForceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) : solForceNat x k = k x := by
  unfold solForceNat; rw [solNatAdd_eq, Nat.one_add]
/-- Pure-GMP WHNF-forcing `ℤ` wrapper (`0` `HAdd.hAdd`, `0` `Nat.succ`, `0` thunks). -/
def solForceInt {α : Type} (x : ℤ) (k : ℤ → α) : α :=
  Int.casesOn x (fun n ↦ solForceNat n fun v ↦ k (Int.ofNat v))
    (fun n ↦ solForceNat n fun v ↦ k (Int.negSucc v))
theorem solForceInt_eq {α : Type} (x : ℤ) (k : ℤ → α) : solForceInt x k = k x := by
  cases x with
  | ofNat n => exact solForceNat_eq n fun v ↦ k (Int.ofNat v)
  | negSucc n => exact solForceNat_eq n fun v ↦ k (Int.negSucc v)
/-- Strict `O(N)` spine-and-element pure-GMP WHNF forcing for `List ℤ`. -/
def solForceIntList : List ℤ → List ℤ
  | [] => []
  | x :: xs =>
      solForceInt x fun x' ↦
        match solForceIntList xs with
        | [] => [x']
        | hd :: tl => x' :: hd :: tl
theorem solForceIntList_eq : ∀ (xs : List ℤ), solForceIntList xs = xs
  | [] => rfl
  | x :: xs => by
    unfold solForceIntList; rw [solForceInt_eq, solForceIntList_eq xs]; cases xs <;> rfl
/-- Continuation wrapper strictly forcing a `List ℤ` before passing to `k`. -/
def solWithIntList {α : Type} (xs : List ℤ) (k : List ℤ → α) : α :=
  match solForceIntList xs with
  | [] => k []
  | hd :: tl => k (hd :: tl)
theorem solWithIntList_eq {α : Type} (xs : List ℤ) (k : List ℤ → α) : solWithIntList xs k = k xs :=
  by unfold solWithIntList; rw [solForceIntList_eq]; cases xs <;> rfl
/-- Pure-GMP `≤` on `ℤ` via constructor pattern-matching and `Nat.ble`. -/
def solBleZ : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.ble m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.ble n m
theorem solBleZ_eq (a b : ℤ) : solBleZ a b = bleZ a b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      rw [bleZ_eq_decide, Bool.eq_iff_iff]; simp only [solBleZ, solNatBle_eq_decide,
        decide_eq_true_eq, Int.ofNat_eq_natCast]; omega
    | negSucc n =>
      unfold solBleZ; symm
      rw [bleZ_eq_decide, decide_eq_false_iff_not, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc m =>
    cases b with
    | ofNat n =>
      unfold solBleZ; symm
      rw [bleZ_eq_decide, decide_eq_true_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
    | negSucc n =>
      rw [bleZ_eq_decide, Bool.eq_iff_iff]; simp only [solBleZ, solNatBle_eq_decide,
        decide_eq_true_eq, Int.negSucc_eq]; omega
/-- Pure-GMP `min` on `ℤ` via `solBleZ`. -/
def solMinZ (a b : ℤ) : ℤ :=
  cond (solBleZ a b) a b
theorem solMinZ_eq (a b : ℤ) : solMinZ a b = min a b := by
  unfold solMinZ; rw [solBleZ_eq]; exact minZ_eq a b
/-- Pure-GMP `max` on `ℤ` via `solBleZ`. -/
def solMaxZ (a b : ℤ) : ℤ :=
  cond (solBleZ a b) b a
theorem solMaxZ_eq (a b : ℤ) : solMaxZ a b = max a b := by
  unfold solMaxZ; rw [solBleZ_eq]; exact maxZ_eq a b
/-- Initial Heron overestimate `g₀ ≥ ⌊√n⌋` for `1 ≤ n ≤ 2^64`. -/
def solIsqrtInit (n : ℕ) : ℕ :=
  cond (Nat.ble n 256) 16
    (cond (Nat.ble n 65536) 256
      (cond (Nat.ble n 16777216) 4096
        (cond (Nat.ble n 4294967296) 65536
          (cond (Nat.ble n 281474976710656) 16777216
            (cond (Nat.ble n 18446744073709551616) 4294967296 n)))))
/-- Pure-GMP structural-fuel Heron loop (`≤ 6` divisions; zero `WellFounded.fix`). -/
def solIsqrtLoop : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, n, g =>
      solForceNat (Nat.div (Nat.add g (Nat.div n g)) 2) fun g' ↦
        cond (Nat.ble g g') g (solIsqrtLoop fuel n g')
/-- Self-certifying pure-GMP `⌊√n⌋` (`O(1)` GMP ops in WHNF; lazy `Nat.sqrt` fallback). -/
def solFloorIsqrt (n : ℕ) : ℕ :=
  Nat.casesOn n 0 fun nPred ↦
    let n1 := Nat.add nPred 1
    solForceNat (solIsqrtLoop 40 n1 (solIsqrtInit n1)) fun s ↦
      cond (Nat.ble (Nat.mul s s) n1 &&
            Nat.ble (Nat.add n1 1) (Nat.mul (Nat.add s 1) (Nat.add s 1)))
        s (Nat.sqrt n1)
theorem solFloorIsqrt_eq (n : ℕ) : solFloorIsqrt n = Nat.sqrt n := by
  cases n with
  | zero => rfl
  | succ nPred =>
    unfold solFloorIsqrt; dsimp only; rw [solForceNat_eq]; set s := solIsqrtLoop 40 (Nat.add nPred
      1) (solIsqrtInit (Nat.add nPred 1)); cases hcond : (Nat.ble (Nat.mul s s) (Nat.add nPred 1) &&
      Nat.ble (Nat.add (Nat.add nPred 1) 1) (Nat.mul (Nat.add s 1) (Nat.add s 1)))
    · rfl
    · change s = Nat.sqrt (nPred + 1); simp only [Bool.and_eq_true, solNatBle_eq_decide,
        decide_eq_true_eq, solNatAdd_eq, solNatMul_eq] at hcond; exact Nat.eq_sqrt.mpr ⟨hcond.1,
        by omega⟩
/-- Self-certifying pure-GMP `⌈√n⌉` (`= ceilIsqrtNat n`). -/
def solCeilIsqrt (n : ℕ) : ℕ :=
  solForceNat (solFloorIsqrt n) fun s ↦
    cond (Nat.beq (Nat.mul s s) n) s (Nat.add s 1)
theorem solCeilIsqrt_eq (n : ℕ) : solCeilIsqrt n = ceilIsqrtNat n := by
  unfold solCeilIsqrt ceilIsqrtNat; rw [solForceNat_eq, withForcedNat_eq, solFloorIsqrt_eq]
/-- Tail-recursive sum of squared magnitudes `acc + ∑ |c_j|^2` forced to bare
  `Literal.natVal`. -/
def solSumSqAbs : List ℤ → ℕ → ℕ
  | [], acc => acc
  | cj :: cjs, acc =>
      solForceNat cj.natAbs fun m ↦
        solForceNat (Nat.add acc (Nat.mul m m)) fun acc' ↦
          solSumSqAbs cjs acc'
theorem solSumSqAbs_eq : ∀ (xs : List ℤ) (acc : ℕ), solSumSqAbs xs acc = swLSumSqAbs xs acc
  | [], _ => rfl
  | x :: xs, acc => by
    unfold solSumSqAbs swLSumSqAbs; simp only [solForceNat_eq, withForcedNat_eq]
    exact solSumSqAbs_eq xs (Nat.add acc (Nat.mul x.natAbs x.natAbs))
/-- Overlap-padded Euclidean radius `rho + ⌈64 * ceilIsqrtNat(∑ c_j^2) / 10^9⌉` (`≤ rho +
  65`). -/
def pulseRadTot (cVec : List ℤ) (rho : ℕ) : ℕ :=
  solForceNat (solSumSqAbs cVec 0) fun normSqC ↦
    solForceNat (solCeilIsqrt normSqC) fun normCUb ↦
      Nat.add rho (Nat.div (Nat.add (Nat.mul 64 normCUb) 999999999) 1000000000)
theorem pulseRadTot_eq (cVec : List ℤ) (rho : ℕ) : pulseRadTot cVec rho = rho + (64 *
  ceilIsqrtNat (swLSumSqAbs cVec 0) + 999999999) / 1000000000 := by
  unfold pulseRadTot; simp only [solForceNat_eq, solSumSqAbs_eq, solCeilIsqrt_eq, solNatAdd_eq,
    solNatMul_eq, solNatDiv_eq]
theorem swLOrbitProj_distSq_le_pulseRadTot {L : ℕ} (hL1024 : L ≤ 1024) {M : Fin (2 * L) → Fin (2 *
  L) → ℝ} (hM : IsValidSwLOverlap M) {st : Fin (2 * L) → ℝ} {cVec : List ℤ} {rho : ℕ} (hclen :
  cVec.length = 2 * L) (hball : swLNormSq (fun j ↦ st j - decodeCenterReal L cVec j) ≤ ((rho : ℝ) /
  (swScale : ℝ)) ^ 2) : swLNormSq (fun o ↦ swLOrbitProj M st o - decodeCenterReal L cVec o) ≤
  ((pulseRadTot cVec rho : ℝ) / (swScale : ℝ)) ^ 2 := by
  have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  set cR := decodeCenterReal L cVec; set normCUb := ceilIsqrtNat (swLSumSqAbs cVec 0)
  set ovlpPad : ℕ := (64 * normCUb + 999999999) / 1000000000
  have hrad_eq : pulseRadTot cVec rho = rho + ovlpPad := pulseRadTot_eq cVec rho
  have hc_norm : swLNormSq cR ≤ ((normCUb : ℝ) / (swScale : ℝ)) ^ 2 := by
    rw [swLCenter_normSq_eq hclen, div_pow]; refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    exact_mod_cast le_ceilIsqrtNat_sq (swLSumSqAbs cVec 0)
  have hu_norm : swLNormSq (fun o ↦ swLOrbitProj M (fun j ↦ st j - cR j) o) ≤ ((rho : ℝ) / (swScale
    : ℝ)) ^ 2 := by
    have hp := isValidSwLOverlap_parseval hM (fun j ↦ st j - cR j)
    rwa [show swLNormSq (fun o ↦ swLOrbitProj M (fun j ↦ st j - cR j) o) =
      ∑ o : Fin (2 * L), (swLOrbitProj M (fun j ↦ st j - cR j) o) ^ 2 from rfl, hp]
  have hovlp_le : ((64 : ℝ) / (swScale : ℝ)) * ((normCUb : ℝ) / (swScale : ℝ)) ≤ (ovlpPad : ℝ) /
    (swScale : ℝ) := by
    have hnat : 64 * normCUb ≤ 1000000000 * ovlpPad := (by dsimp [ovlpPad]; omega)
    have hreal : (64 : ℝ) * (normCUb : ℝ) ≤ (swScale : ℝ) * (ovlpPad : ℝ) :=
      (by unfold swScale; exact_mod_cast hnat); rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hS
      hS) hS]; nlinarith
  have hw_norm : swLNormSq (fun o ↦ swLOrbitProj M cR o - cR o) ≤ ((ovlpPad : ℝ) / (swScale : ℝ)) ^
    2 := by
    have h1 := swLOrbitProj_sub_id_normSq_le hL1024 hM cR
    have h2 : ((64 : ℝ) / (swScale : ℝ)) ^ 2 * swLNormSq cR ≤ (((64 : ℝ) / (swScale : ℝ)) *
      ((normCUb : ℝ) / (swScale : ℝ))) ^ 2 := by
      calc ((64 : ℝ) / (swScale : ℝ)) ^ 2 * swLNormSq cR
        _ ≤ ((64 : ℝ) / (swScale : ℝ)) ^ 2 * ((normCUb : ℝ) / (swScale : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hc_norm (sq_nonneg _)
        _ = (((64 : ℝ) / (swScale : ℝ)) * ((normCUb : ℝ) / (swScale : ℝ))) ^ 2 := by ring
    have h3 : (((64 : ℝ) / (swScale : ℝ)) * ((normCUb : ℝ) / (swScale : ℝ))) ^ 2 ≤ ((ovlpPad : ℝ) /
      (swScale : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hovlp_le 2
    exact (h1.trans h2).trans h3
  have htri := swLNormSq_add_le_sq (div_nonneg (Nat.cast_nonneg rho) hS.le) (div_nonneg
    (Nat.cast_nonneg ovlpPad) hS.le) hu_norm hw_norm; have hfun : (fun o ↦ swLOrbitProj M st o - cR
    o) = fun o ↦ swLOrbitProj M (fun j ↦ st j - cR j) o + (swLOrbitProj M cR o - cR o) :=
    (by ext o; rw [← swLOrbitProj_sub_linear]; ring); have hr_sum : (rho : ℝ) / (swScale : ℝ) +
    (ovlpPad : ℝ) / (swScale : ℝ) = ((pulseRadTot cVec rho : ℝ) / (swScale : ℝ)) :=
    (by rw [hrad_eq]; push_cast; ring)
  rwa [← hfun, hr_sum] at htri
theorem masked_normSq_ge_of_distSq_le {L : ℕ} (mask : Fin (2 * L) → Bool) {y cR : Fin (2 * L) → ℝ}
  {rad lb : ℝ} (hrad : 0 ≤ rad) (hlb0 : 0 ≤ lb) (hdist : swLNormSq (fun o ↦ y o - cR o) ≤ rad ^ 2)
  (hc_ge : (lb + rad) ^ 2 ≤ ∑ o : Fin (2 * L), if mask o then (cR o) ^ 2 else 0) : lb ^ 2 ≤ ∑ o :
  Fin (2 * L), if mask o then (y o) ^ 2 else 0 := by
  let yM : Fin (2 * L) → ℝ := fun o ↦ if mask o then y o else 0
  let dM : Fin (2 * L) → ℝ := fun o ↦ if mask o then cR o - y o else 0
  have hyM_sq : swLNormSq yM = ∑ o : Fin (2 * L), if mask o then (y o) ^ 2 else 0 := by
    unfold swLNormSq; refine Finset.sum_congr rfl fun o _ ↦ ?_; dsimp [yM]; cases mask o <;> simp
  have hcM_sq : swLNormSq (fun o ↦ yM o + dM o) = ∑ o : Fin (2 * L), if mask o then (cR o) ^ 2 else
    0 := by
    unfold swLNormSq; refine Finset.sum_congr rfl fun o _ ↦ ?_; dsimp [yM, dM]; cases mask o <;>
      simp
  have hdM_le : swLNormSq dM ≤ rad ^ 2 := by
    refine (?_ : swLNormSq dM ≤ swLNormSq (fun o ↦ y o - cR o)).trans hdist; unfold swLNormSq;
      refine Finset.sum_le_sum fun o _ ↦ ?_; dsimp [dM]; cases mask o
    · simp [sq_nonneg]
    · simp only [↓reduceIte]; exact le_of_eq (by ring)
  have hyM_nn : 0 ≤ swLNormSq yM := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _; have htri :=
    swLNormSq_add_le_sq (Real.sqrt_nonneg _) hrad (le_of_eq (Real.sq_sqrt hyM_nn).symm) hdM_le
  rw [hcM_sq] at htri
  have hsq_le : (lb + rad) ^ 2 ≤ (√(swLNormSq yM) + rad) ^ 2 := hc_ge.trans htri; have habs :=
    sq_le_sq.1 hsq_le; rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at habs
  have hlb_le : lb ≤ √(swLNormSq yM) := (by linarith)
  have hlb_sq : lb ^ 2 ≤ (√(swLNormSq yM)) ^ 2 := pow_le_pow_left₀ hlb0 hlb_le 2
  rwa [Real.sq_sqrt hyM_nn, hyM_sq] at hlb_sq
theorem swLAttemptProbReal_tail_eq_orbit_suffix {L : ℕ} (hL : 2 ≤ L)
    (M : Fin (2 * L) → Fin (2 * L) → ℝ) (st : Fin (2 * L) → ℝ) (cum : ℝ)
    {c : ℕ} (hc1 : 1 ≤ c) (hcL : c ≤ L) :
    ∑ h ∈ Finset.Icc c L, swLAttemptProbReal L hL M st cum h =
      ∑ o : Fin (2 * L),
        if 2 * c - 1 ≤ o.1 then
          (swLOrbitProj M st o) ^ 2 + cum * (M o ⟨2 * L - 1, by omega⟩) ^ 2
        else 0 := by
  set q : Fin (2 * L) → ℝ := fun o ↦ (swLOrbitProj M st o) ^ 2 + cum * (M o ⟨2 * L - 1, by omega⟩) ^
    2; set f : Fin (2 * L) → ℝ := fun o ↦ if 2 * c - 1 ≤ o.1 then q o else 0
  rw [sum_fin_interior_pairs hL f]; have hf0 : f ⟨0, by omega⟩ = 0 :=
    (by dsimp [f]; rw [ite_eq_right (by omega)])
  have hftop : f ⟨2 * L - 1, by omega⟩ = swLAttemptProbReal L hL M st cum L := by
    dsimp [f, q]; rw [ite_eq_left (by omega)]; unfold swLAttemptProbReal; have hn0 : L ≠ 0 :=
      (by omega); simp [hn0]
  have hfmid : ∑ w0 : Fin (L - 1), (f ⟨2 * w0.1 + 1, by omega⟩ + f ⟨2 * w0.1 + 2, by omega⟩) = ∑ h ∈
    Finset.Ico c L, swLAttemptProbReal L hL M st cum h := by
    have hfilt : ∑ h ∈ Finset.Ico c L, swLAttemptProbReal L hL M st cum h = ∑ h ∈ Finset.Ico 1 L, if
      c ≤ h then swLAttemptProbReal L hL M st cum h else 0 := by
      rw [← Finset.sum_filter]; refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      ext h; simp only [Finset.mem_Ico, Finset.mem_filter]; omega
    rw [hfilt, Finset.sum_Ico_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun i ↦ if c ≤ 1 + i then
      swLAttemptProbReal L hL M st cum (1 + i) else 0) (L - 1)]
    refine Finset.sum_congr rfl fun w0 _ ↦ ?_; dsimp [f, q]; by_cases hcw : c ≤ 1 + w0.1
    · have h1 : 2 * c - 1 ≤ 2 * w0.1 + 1 := (by omega); have h2 : 2 * c - 1 ≤ 2 * w0.1 + 2 :=
        (by omega); rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left hcw]; unfold swLAttemptProbReal
      have hn0 : 1 + w0.1 ≠ 0 := (by omega); have hlt : 1 + w0.1 < L := (by omega)
      have hi1 : (⟨2 * (1 + w0.1) - 1, by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 + 1, by omega⟩ :=
        (by ext; dsimp; omega); have hi2 : (⟨2 * (1 + w0.1), by omega⟩ : Fin (2 * L)) = ⟨2 * w0.1 +
        2, by omega⟩ := (by ext; dsimp; omega); simp only [hn0, ↓reduceIte, hlt, ↓reduceDIte, hi1,
        hi2]; ring
    · have h1 : ¬(2 * c - 1 ≤ 2 * w0.1 + 1) := (by omega); have h2 : ¬(2 * c - 1 ≤ 2 * w0.1 + 2) :=
        (by omega); rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right hcw, add_zero]
  have hicc : ∑ h ∈ Finset.Icc c L, swLAttemptProbReal L hL M st cum h = (∑ h ∈ Finset.Ico c L,
    swLAttemptProbReal L hL M st cum h) + swLAttemptProbReal L hL M st cum L :=
    (by rw [← Finset.Ico_insert_right hcL, Finset.sum_insert Finset.right_notMem_Ico, add_comm])
  rw [hf0, zero_add, hfmid, hftop, hicc]
/-- Single-pass `O(m)` accumulator returning `(suffixSqs, headSq)` for orbit pairs `1 ≤ c ≤
  m + 1`. -/
def pulsePairSuffixSq : ℕ → List ℤ → List ℕ × ℕ
  | 0, x :: _ =>
      let sq0 := Nat.mul x.natAbs x.natAbs
      solForceNat sq0 fun sq' ↦ ([sq'], sq')
  | 0, [] => ([0], 0)
  | m + 1, x1 :: x2 :: xs =>
      match pulsePairSuffixSq m xs with
      | (restSqs, tailSq) =>
          let pairSq := Nat.add (Nat.mul x1.natAbs x1.natAbs) (Nat.mul x2.natAbs x2.natAbs)
          solForceNat (Nat.add pairSq tailSq) fun curSq ↦ (curSq :: restSqs, curSq)
  | m + 1, _ => (List.replicate (Nat.succ (Nat.succ m)) 0, 0)
theorem pulsePairSuffixSq_spec : ∀ (m : ℕ) (xs : List ℤ), xs.length = 2 * m + 1 →
  (pulsePairSuffixSq m xs).1.length = m + 1 ∧ (pulsePairSuffixSq m xs).2 = (∑ i ∈ Finset.range
  (2 * m + 1), (xs.getD i 0).natAbs ^ 2) ∧ (∀ idx < m + 1, ((pulsePairSuffixSq m xs).1).getD idx 0
  = ∑ i ∈ Finset.Ico (2 * idx) (2 * m + 1), (xs.getD i 0).natAbs ^ 2)
  | 0, x :: [], _ => by
    simp only [pulsePairSuffixSq, solForceNat_eq, Nat.mul_zero, Nat.zero_add,
      List.length_singleton, Finset.range_one, Finset.sum_singleton]; refine ⟨trivial, ?_, fun idx
      hidx ↦ ?_⟩
    · simp [sq]
    · have h0 : idx = 0 := (by omega); subst h0; rw [Nat.mul_zero, Finset.sum_Ico_eq_sum_range];
        simp [sq]
  | 0, [], hlen => (by simp at hlen) | 0, _ :: _ :: _, hlen => (by simp at hlen)
  | m + 1, x1 :: x2 :: xs, hlen => by
    have hlen' : xs.length = 2 * m + 1 :=
      (by rw [List.length_cons, List.length_cons] at hlen; omega)
    rcases pulsePairSuffixSq_spec m xs hlen' with ⟨ih_len, ih_tot, ih_idx⟩
    unfold pulsePairSuffixSq; rcases hrec : pulsePairSuffixSq m xs with ⟨restSqs, tailSq⟩
    rw [hrec] at ih_len ih_tot ih_idx; dsimp only at ih_len ih_tot ih_idx ⊢; rw [solForceNat_eq]
    have htot_eq : Nat.add (Nat.add (Nat.mul x1.natAbs x1.natAbs) (Nat.mul x2.natAbs x2.natAbs))
      tailSq = ∑ i ∈ Finset.range (2 * (m + 1) + 1), ((x1 :: x2 :: xs).getD i 0).natAbs ^ 2 := by
      rw [ih_tot, show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega,
        ← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ (2 * m + 1) + 2)]
      have hhead : ∑ i ∈ Finset.range 2, ((x1 :: x2 :: xs).getD i 0).natAbs ^ 2 = x1.natAbs ^ 2 +
        x2.natAbs ^ 2 :=
        (by rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]; simp)
      have htail : ∑ i ∈ Finset.Ico 2 ((2 * m + 1) + 2), ((x1 :: x2 :: xs).getD i 0).natAbs ^ 2 = ∑
        j ∈ Finset.range (2 * m + 1), (xs.getD j 0).natAbs ^ 2 := by
        rw [Finset.sum_Ico_eq_sum_range]; refine Finset.sum_congr rfl fun j _ ↦ ?_; rw [show 2 + j =
          j + 1 + 1 by omega]; rfl
      rw [hhead, htail]; simp only [solNatAdd_eq, solNatMul_eq, sq]
    refine ⟨by simp [ih_len], htot_eq, fun idx hidx ↦ ?_⟩; rcases idx with _ | idx'
    · simp only [List.getD_cons_zero, Nat.mul_zero]; rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.sub_zero, Nat.zero_add]; exact htot_eq
    · simp only [List.getD_cons_succ]; rw [ih_idx idx' (by omega), Finset.sum_Ico_eq_sum_range,
        Finset.sum_Ico_eq_sum_range]; have hcnt : 2 * (m + 1) + 1 - 2 * (idx' + 1) = 2 * m + 1 - 2 *
        idx' := (by omega); rw [hcnt]; refine Finset.sum_congr rfl fun j _ ↦ ?_; rw [show 2 * (idx'
        + 1) + j = (2 * idx' + j) + 1 + 1 by omega]; rfl
  | m + 1, [], hlen => (by simp at hlen) | m + 1, [_], hlen => (by simp at hlen)
/-- Convert suffix square sums into certified `10^9`-scale tail lower bounds. -/
def pulseTailLbsFromSqs : List ℕ → ℕ → ℤ → List ℤ
  | [], _, _ => []
  | s0 :: sqs, radTot, cumPad =>
      let lb := Nat.sub (solFloorIsqrt s0) radTot
      let sqLb := Int.ofNat (Nat.div (Nat.mul lb lb) 1000000000)
      solForceInt (solMinZ swScale (Int.add sqLb cumPad)) fun tLb ↦
        tLb :: pulseTailLbsFromSqs sqs radTot cumPad
/-- `O(L)` terminal extractor returning `(certTailLbs, p0Lb, survUb)` from `(cVec, rho,
  survUb)`. -/
def pulseTerminalBoundsL2 (L : ℕ) (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) :
    List ℤ × ℤ × ℤ :=
  solForceNat (solSumSqAbs cVec 0) fun normSqK ↦
    solForceNat (solCeilIsqrt normSqK) fun normKUb ↦
      solForceNat (Nat.add rho (Nat.div (Nat.add (Nat.mul 64 normKUb) 999999999) 1000000000))
        fun radTot ↦
          solForceNat (Nat.add normKUb rho) fun sumR ↦
            solForceInt (solMinZ swScale (ceilDivScaleP (Int.ofNat (Nat.mul sumR sumR))))
              fun oneMinusCumUb ↦
                solForceInt (solMaxZ 0 (Int.sub swScale oneMinusCumUb)) fun cumLo ↦
                  solForceInt (solMaxZ 0 (Int.sub cumLo 1)) fun cumPad ↦
                    let c0Abs := (cVec.headD 0).natAbs
                    let p0AmpLb := Nat.sub c0Abs radTot
                    solForceInt
                      (Int.ofNat (Nat.div (Nat.mul p0AmpLb p0AmpLb) 1000000000))
                      fun p0Lb ↦
                        let sqs := (pulsePairSuffixSq (Nat.sub L 1) cVec.tail).1
                        solWithIntList (pulseTailLbsFromSqs sqs radTot cumPad) fun tailLbs ↦
                          (tailLbs, p0Lb, survUb)
theorem pulseTerminalBoundsL2_eq (L : ℕ) (cVec : List ℤ) (rho : ℕ) (survUb : ℤ) :
  pulseTerminalBoundsL2 L cVec rho survUb =
      let radTot := pulseRadTot cVec rho; let normKUb := ceilIsqrtNat (swLSumSqAbs cVec 0)
      let oneMinusCumUb : ℤ := min swScale (-((-(((normKUb + rho : ℕ) : ℤ) ^ 2)) / swScale))
      let cumLo : ℤ := max 0 (swScale - oneMinusCumUb); let cumPad : ℤ := max 0 (cumLo - 1)
      let p0AmpLb := (cVec.headD 0).natAbs - radTot
      let p0Lb : ℤ := Int.ofNat ((p0AmpLb ^ 2) / 1000000000)
      let sqs := (pulsePairSuffixSq (L - 1) cVec.tail).1
      (pulseTailLbsFromSqs sqs radTot cumPad, p0Lb, survUb) := by
  unfold pulseTerminalBoundsL2; rw [pulseRadTot_eq]; simp only [solForceNat_eq, solForceInt_eq,
    solWithIntList_eq, solSumSqAbs_eq, solCeilIsqrt_eq, ofNat_mul_self_eq_sq]
  simp only [solMinZ_eq, solMaxZ_eq, ceilDivScaleP_eq, solNatAdd_eq, solNatSub_eq, solNatMul_eq,
    solNatDiv_eq, solIntSub_eq, sq]
theorem pulseTailLbsFromSqs_length (sqs : List ℕ) (radTot : ℕ) (cumPad : ℤ) :
  (pulseTailLbsFromSqs sqs radTot cumPad).length = sqs.length := by
  induction sqs with
  | nil => rfl | cons s0 sqs ih => simp [pulseTailLbsFromSqs, solForceInt_eq, ih]
theorem pulseTailLbsFromSqs_getD : ∀ (sqs : List ℕ) (radTot : ℕ) (cumPad : ℤ) (idx : ℕ), idx <
  sqs.length → (pulseTailLbsFromSqs sqs radTot cumPad).getD idx 0 = min swScale (Int.ofNat
  (((Nat.sqrt (sqs.getD idx 0) - radTot) ^ 2) / 1000000000) + cumPad)
  | [], _, _, _, h => by simp at h
  | s0 :: sqs, radTot, cumPad, 0, _ => by
    simp only [pulseTailLbsFromSqs, solForceInt_eq, solMinZ_eq, solFloorIsqrt_eq,
      List.getD_cons_zero, sq, solNatSub_eq, solNatMul_eq, solNatDiv_eq, solIntAdd_eq]
  | s0 :: sqs, radTot, cumPad, idx + 1, h => by
    simp only [pulseTailLbsFromSqs, solForceInt_eq, List.getD_cons_succ]
    exact pulseTailLbsFromSqs_getD sqs radTot cumPad idx (by rw [List.length_cons] at h; omega)
theorem pulseTerminalBoundsL2_sound {L : ℕ} (hL : 2 ≤ L) (hL1024 : L ≤ 1024) {M : Fin (2 * L) →
  Fin (2 * L) → ℝ} (hM : IsValidSwLOverlap M) {st : Fin (2 * L) → ℝ} {cum surv : ℝ} {cVec : List ℤ}
  {rho : ℕ} {survUb : ℤ} (hclen : cVec.length = 2 * L) (hcons : swLNormSq st + cum = 1 ∧ 0 ≤ cum ∧
  cum ≤ 1 ∧ 0 ≤ surv) (hball : swLNormSq (fun j ↦ st j - decodeCenterReal L cVec j) ≤ ((rho : ℝ) /
  (swScale : ℝ)) ^ 2) (hsurv : surv ≤ (survUb : ℝ) / (swScale : ℝ)) :
    let bnds := pulseTerminalBoundsL2 L cVec rho survUb; let p := swLAttemptProbReal L hL M st cum
    bnds.1.length = L ∧ 0 ≤ bnds.2.1 ∧ ((bnds.2.1 : ℝ) / (swScale : ℝ)) ≤ p 0 ∧ surv ≤ (bnds.2.2 :
      ℝ) / (swScale : ℝ) ∧ ∀ c ∈ Finset.Icc 1 L, ((bnds.1.getD (c - 1) 0 : ℤ) : ℝ) / (swScale : ℝ) ≤
      ∑ h ∈ Finset.Icc c L, p h := by
  intro bnds p; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num); set cR :=
    decodeCenterReal L cVec; set radTot := pulseRadTot cVec rho; have hdist :=
    swLOrbitProj_distSq_le_pulseRadTot hL1024 hM hclen hball; have hcum_ub :=
    l2Ball_oneMinusCum_le hclen ⟨hcons.1, hcons.2.1⟩ hball; set normKUb := ceilIsqrtNat (swLSumSqAbs
    cVec 0); set oneMinusCumUb : ℤ := min swScale (-((-(((normKUb + rho : ℕ) : ℤ) ^ 2)) / swScale))
  set cumLo : ℤ := max 0 (swScale - oneMinusCumUb); set cumPad : ℤ := max 0 (cumLo - 1)
  have hcumLo_le : (cumLo : ℝ) / (swScale : ℝ) ≤ cum := by
    dsimp [cumLo]; rw [Int.cast_max, Int.cast_zero]; rcases le_total (0 : ℝ) (((swScale -
      oneMinusCumUb : ℤ) : ℝ)) with h0 | h0
    · rw [max_eq_right h0, Int.cast_sub, sub_div, div_self hS.ne']; linarith [hcum_ub]
    · rw [max_eq_left h0, zero_div]; exact hcons.2.1
  have hcumPad_le : (cumPad : ℝ) / (swScale : ℝ) ≤ cum * (1 - (1 : ℝ) / 10 ^ 18) := by
    dsimp [cumPad]; rw [Int.cast_max, Int.cast_zero]; rcases le_total (0 : ℝ) (((cumLo - 1 : ℤ) :
      ℝ)) with h0 | h0
    · rw [max_eq_right h0, Int.cast_sub, Int.cast_one, sub_div]; have hcum_m1 : cum * ((1 : ℝ) / 10
        ^ 18) ≤ (1 : ℝ) / (swScale : ℝ) := (by unfold swScale; linarith [hcons.2.1, hcons.2.2.1])
      linarith [hcumLo_le, hcum_m1]
    · rw [max_eq_left h0, zero_div]; exact mul_nonneg hcons.2.1 (by norm_num)
  have hbnds_eq : bnds = (pulseTailLbsFromSqs (pulsePairSuffixSq (L - 1) cVec.tail).1 radTot
    cumPad, Int.ofNat ((((cVec.headD 0).natAbs - radTot) ^ 2) / 1000000000), survUb) := by
    dsimp only [bnds, radTot, cumPad, cumLo, oneMinusCumUb, normKUb]
    exact pulseTerminalBoundsL2_eq L cVec rho survUb
  rw [hbnds_eq]; dsimp only; rcases cVec with _ | ⟨c0, xs⟩
  · rw [List.length_nil] at hclen; omega
  dsimp only [List.tail_cons, List.headD_cons]; have hxs_len : xs.length = 2 * (L - 1) + 1 :=
    (by rw [List.length_cons] at hclen; omega)
  rcases pulsePairSuffixSq_spec (L - 1) xs hxs_len with ⟨hsqs_len, _, hsqs_idx⟩; set sqs :=
    (pulsePairSuffixSq (L - 1) xs).1; have hsqs_L : sqs.length = L := (by omega)
  have hdiv_sq_le : ∀ (m : ℕ), ((Int.ofNat ((m ^ 2) / 1000000000) : ℤ) : ℝ) / (swScale : ℝ) ≤ ((m :
    ℝ) / (swScale : ℝ)) ^ 2 := by
    intro m; have h1 : (((m ^ 2) / 1000000000 : ℕ) : ℝ) * 1000000000 ≤ ((m ^ 2 : ℕ) : ℝ) :=
      (by exact_mod_cast Nat.div_mul_le_self (m ^ 2) 1000000000); rw [Int.ofNat_eq_natCast,
      Int.cast_natCast, div_pow, div_le_div_iff₀ hS (sq_pos_of_pos hS)]; unfold swScale at h1 ⊢;
      push_cast at h1 ⊢; nlinarith
  refine ⟨by rw [pulseTailLbsFromSqs_length, hsqs_L],
    by rw [Int.ofNat_eq_natCast]; exact Int.natCast_nonneg _, ?_, hsurv, ?_⟩
  · let mask0 : Fin (2 * L) → Bool := fun o ↦ Nat.ble o.1 0; set lb0 : ℕ := c0.natAbs - radTot
    have hm0_ne {k : ℕ} (hk : k ≠ 0) : ¬(Nat.ble k 0 = true) := by
      rw [solNatBle_eq_decide, decide_eq_true_eq]; omega
    have hc0_sum : ∑ o : Fin (2 * L), (if mask0 o then (cR o) ^ 2 else 0) = ((c0.natAbs : ℝ) /
      (swScale : ℝ)) ^ 2 := by
      rw [sum_fin_interior_pairs hL]; have hmid0 : ∑ w0 : Fin (L - 1),
          ((if mask0 ⟨2 * w0.1 + 1, by omega⟩ then (cR ⟨2 * w0.1 + 1, by omega⟩) ^ 2 else 0) +
            (if mask0 ⟨2 * w0.1 + 2, by omega⟩ then (cR ⟨2 * w0.1 + 2, by omega⟩) ^ 2 else 0)) =
          0 := Finset.sum_eq_zero fun w0 _ ↦ by dsimp [mask0]; simp
      have hlast0 : (if mask0 ⟨2 * L - 1, by omega⟩ then (cR ⟨2 * L - 1, by omega⟩) ^ 2 else 0) = 0
        := (by dsimp [mask0]; exact ite_eq_right (hm0_ne (by omega)))
      rw [hmid0, hlast0, add_zero, add_zero]
      have hm0 : mask0 ⟨0, by omega⟩ = true := rfl; rw [ite_eq_left hm0]
      dsimp [cR, decodeCenterReal]; simp only [List.getD_cons_zero, div_pow]; congr 1
      rcases c0 with n | n
      · simp
      · simp [Int.negSucc_eq]
    have hlb0_sq : ((lb0 : ℝ) / (swScale : ℝ)) ^ 2 ≤ (swLOrbitProj M st ⟨0, by omega⟩) ^ 2 := by
      by_cases hle : radTot ≤ c0.natAbs
      · have hsum_ge : (((lb0 : ℝ) / (swScale : ℝ)) + ((radTot : ℝ) / (swScale : ℝ))) ^ 2 ≤ ∑ o :
          Fin (2 * L), if mask0 o then (cR o) ^ 2 else 0 := by
          rw [hc0_sum, ← add_div]; have hadd : (lb0 : ℝ) + (radTot : ℝ) = (c0.natAbs : ℝ) :=
            (by dsimp [lb0]; exact_mod_cast Nat.sub_add_cancel hle); rw [hadd]
        have hm := masked_normSq_ge_of_distSq_le mask0 (div_nonneg (Nat.cast_nonneg radTot) hS.le)
          (div_nonneg (Nat.cast_nonneg lb0) hS.le) hdist hsum_ge
        have hy0_sum : ∑ o : Fin (2 * L), (if mask0 o then (swLOrbitProj M st o) ^ 2 else 0) =
          (swLOrbitProj M st ⟨0, by omega⟩) ^ 2 := by
          rw [sum_fin_interior_pairs hL]; have hmid0 : ∑ w0 : Fin (L - 1),
              ((if mask0 ⟨2 * w0.1 + 1, by omega⟩ then
                  (swLOrbitProj M st ⟨2 * w0.1 + 1, by omega⟩) ^ 2 else 0) +
                (if mask0 ⟨2 * w0.1 + 2, by omega⟩ then
                  (swLOrbitProj M st ⟨2 * w0.1 + 2, by omega⟩) ^ 2 else 0)) = 0 :=
            Finset.sum_eq_zero fun w0 _ ↦ by dsimp [mask0]; simp
          have hlast0 : (if mask0 ⟨2 * L - 1, by omega⟩ then (swLOrbitProj M st ⟨2 * L - 1,
            by omega⟩) ^ 2 else 0) = 0 :=
            (by dsimp [mask0]; exact ite_eq_right (hm0_ne (by omega)))
          rw [hmid0, hlast0, add_zero, add_zero]
          have hm0 : mask0 ⟨0, by omega⟩ = true := rfl; rw [ite_eq_left hm0]
        rwa [hy0_sum] at hm
      · have h0 : lb0 = 0 := (by dsimp [lb0]; omega); rw [h0]; simp [sq_nonneg]
    dsimp only [p]; unfold swLAttemptProbReal; rw [ite_eq_left rfl]; have hcum_term : 0 ≤ cum * (M
      ⟨0, by omega⟩ ⟨2 * L - 1, by omega⟩) ^ 2 := mul_nonneg hcons.2.1 (sq_nonneg _)
    exact (hdiv_sq_le lb0).trans (hlb0_sq.trans (le_add_of_nonneg_right hcum_term))
  · intro c hc; rw [Finset.mem_Icc] at hc; rcases hc with ⟨hc1, hcL⟩; have hidx_lt : c - 1 <
      sqs.length := (by omega); rw [pulseTailLbsFromSqs_getD sqs radTot cumPad (c - 1) hidx_lt]
    set sqNat := sqs.getD (c - 1) 0; set lb := Nat.sqrt sqNat - radTot
    let maskC : Fin (2 * L) → Bool := fun o ↦ Nat.ble (2 * c - 1) o.1
    have hsq_eq : ∑ o : Fin (2 * L), (if maskC o then (cR o) ^ 2 else 0) = (sqNat : ℝ) / (swScale :
      ℝ) ^ 2 := by
      let g : ℕ → ℝ := fun k ↦
        if 2 * c - 1 ≤ k then ((((c0 :: xs).getD k 0 : ℤ) : ℝ) / (swScale : ℝ)) ^ 2 else 0
      have hfin : ∑ o : Fin (2 * L), (if maskC o then (cR o) ^ 2 else 0) = ∑ k ∈ Finset.range (2 *
        L), g k := by
        rw [← Fin.sum_univ_eq_sum_range g (2 * L)]; refine Finset.sum_congr rfl fun o _ ↦ ?_
        dsimp [maskC, cR, decodeCenterReal, g]
        simp only [solNatBle_eq_decide, decide_eq_true_eq]
      rw [hfin, show 2 * L = (2 * (L - 1) + 1) + 1 by omega, Finset.sum_range_succ']
      have hg0 : g 0 = 0 := (by dsimp [g]; rw [ite_eq_right (by omega)]); rw [hg0, add_zero]
      have hshift : ∑ i ∈ Finset.range (2 * (L - 1) + 1), g (i + 1) = ∑ i ∈ Finset.Ico (2 * (c - 1))
        (2 * (L - 1) + 1), (((xs.getD i 0).natAbs : ℝ) ^ 2) / (swScale : ℝ) ^ 2 := by
        have hfilt : ∑ i ∈ Finset.Ico (2 * (c - 1)) (2 * (L - 1) + 1), (((xs.getD i 0).natAbs : ℝ) ^
          2) / (swScale : ℝ) ^ 2 = ∑ i ∈ Finset.range (2 * (L - 1) + 1), if 2 * (c - 1) ≤ i then
          (((xs.getD i 0).natAbs : ℝ) ^ 2) / (swScale : ℝ) ^ 2 else 0 := by
          rw [← Finset.sum_filter]; refine Finset.sum_congr ?_ fun _ _ ↦ rfl
          ext i; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega
        rw [hfilt]; refine Finset.sum_congr rfl fun i _ ↦ ?_
        dsimp [g]; simp only [List.getD_cons_succ, div_pow]; by_cases hi : 2 * (c - 1) ≤ i
        · have hi' : 2 * c - 1 ≤ i + 1 := (by omega); rw [ite_eq_left hi', ite_eq_left hi]; congr 1
          rcases xs.getD i 0 with n | n
          · simp
          · simp [Int.negSucc_eq]
        · have hi' : ¬(2 * c - 1 ≤ i + 1) := (by omega); rw [ite_eq_right hi', ite_eq_right hi]
      rw [hshift]; simp_rw [div_eq_mul_inv, ← Finset.sum_mul, ← div_eq_mul_inv]; congr 1
      have hspec := hsqs_idx (c - 1) (by omega); dsimp [sqNat]; rw [hspec, Nat.cast_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by push_cast; rfl
    have hlb_orb : ((lb : ℝ) / (swScale : ℝ)) ^ 2 ≤ ∑ o : Fin (2 * L), if 2 * c - 1 ≤ o.1 then
      (swLOrbitProj M st o) ^ 2 else 0 := by
      have hmask_orb : (∑ o : Fin (2 * L), if maskC o then (swLOrbitProj M st o) ^ 2 else 0) =
          ∑ o : Fin (2 * L), if 2 * c - 1 ≤ o.1 then (swLOrbitProj M st o) ^ 2 else 0 :=
        Finset.sum_congr rfl fun o _ ↦ by
          dsimp [maskC]; simp only [solNatBle_eq_decide, decide_eq_true_eq]
      rw [← hmask_orb]; by_cases hle : radTot ≤ Nat.sqrt sqNat
      · have hsum_ge : (((lb : ℝ) / (swScale : ℝ)) + ((radTot : ℝ) / (swScale : ℝ))) ^ 2 ≤ ∑ o : Fin
          (2 * L), if maskC o then (cR o) ^ 2 else 0 := by
          rw [hsq_eq, ← add_div, div_pow]; refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
          have hadd : (lb : ℝ) + (radTot : ℝ) = (Nat.sqrt sqNat : ℝ) :=
            (by dsimp [lb]; exact_mod_cast Nat.sub_add_cancel hle)
          rw [hadd, sq]; exact_mod_cast Nat.sqrt_le sqNat
        exact masked_normSq_ge_of_distSq_le maskC (div_nonneg (Nat.cast_nonneg radTot) hS.le)
          (div_nonneg (Nat.cast_nonneg lb) hS.le) hdist hsum_ge
      · have h0 : lb = 0 := (by dsimp [lb]; omega); rw [h0]
        simpa using Finset.sum_nonneg fun o (_ : o ∈ Finset.univ) ↦ show (0 : ℝ) ≤ if maskC o then
          (swLOrbitProj M st o) ^ 2 else 0 by
            cases maskC o
            · simp
            · simp [sq_nonneg]
    have htail_eq := swLAttemptProbReal_tail_eq_orbit_suffix hL M st cum hc1 hcL
    have hcum_tail : cum * (1 - (1 : ℝ) / 10 ^ 18) ≤ ∑ o : Fin (2 * L), if 2 * c - 1 ≤ o.1 then cum
      * (M o ⟨2 * L - 1, by omega⟩) ^ 2 else 0 := by
      have htop_le := Finset.single_le_sum
        (f := fun o : Fin (2 * L) ↦
          if 2 * c - 1 ≤ o.1 then cum * (M o ⟨2 * L - 1, by omega⟩) ^ 2 else 0)
        (fun o _ ↦ by
          split_ifs
          · exact mul_nonneg hcons.2.1 (sq_nonneg _)
          · exact le_rfl)
        (Finset.mem_univ (⟨2 * L - 1, by omega⟩ : Fin (2 * L)))
      dsimp only at htop_le; rw [ite_eq_left (by omega)] at htop_le; rcases hM.2.2.1 ⟨2 * L - 1,
        by omega⟩ with ⟨_, _, hd_sq⟩
      exact (mul_le_mul_of_nonneg_left hd_sq hcons.2.1).trans htop_le
    have htail_split : (∑ o : Fin (2 * L), if 2 * c - 1 ≤ o.1 then (swLOrbitProj M st o) ^ 2 + cum *
      (M o ⟨2 * L - 1, by omega⟩) ^ 2 else 0) = (∑ o : Fin (2 * L), if 2 * c - 1 ≤ o.1 then
      (swLOrbitProj M st o) ^ 2 else 0) + ∑ o : Fin (2 * L), if 2 * c - 1 ≤ o.1 then cum * (M o ⟨2 *
      L - 1, by omega⟩) ^ 2 else 0 := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun o _ ↦ ?_
      split_ifs <;> ring
    have hmin_le : ((min swScale (Int.ofNat ((lb ^ 2) / 1000000000) + cumPad) : ℤ) : ℝ) / (swScale :
      ℝ) ≤ ((Int.ofNat ((lb ^ 2) / 1000000000) : ℤ) : ℝ) / (swScale : ℝ) + (cumPad : ℝ) / (swScale :
      ℝ) := by
      rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hS.le; rw [← Int.cast_add];
        exact_mod_cast min_le_right swScale _
    dsimp only [p]; rw [htail_eq, htail_split]; exact hmin_le.trans (add_le_add ((hdiv_sq_le
      lb).trans hlb_orb) (hcumPad_le.trans hcum_tail))
/-
 ## 3. 1-ULP `1024`-Subdivision Trig & Multi-pulse Angle Checkers (`2 ≤ L ≤ 1024`, `96 ≤ n`)
-/
/-- Fixed-point `10^18` internal precision scale for double-angle trig bounding. -/
def pulseTbl : ℤ := 1000000000000000000
/-- Perform `k` guarded double-angle cosine steps `u ↦ ⌊2 u^2 / 10^18⌋ - 10^18`. -/
def cosDoubleLoopPulse : ℕ → ℤ → ℤ
  | 0, u => u
  | k + 1, u =>
      cond (solBleZ 0 u)
        (solForceInt
          (Int.sub (Int.ediv (Int.mul 2 (Int.mul u u)) pulseTbl) pulseTbl)
          (cosDoubleLoopPulse k))
        (-1)
/-- Perform `k` guarded double-angle `(sin, cos)` steps at scale `10^18`. -/
def sinCosDoubleLoopPulse : ℕ → ℤ → ℤ → ℤ × ℤ
  | 0, s, c => (s, c)
  | k + 1, s, c =>
      cond (solBleZ 0 s && solBleZ 0 c)
        (solForceInt (Int.ediv (Int.mul 2 (Int.mul s c)) pulseTbl) fun s' ↦
          solForceInt
            (Int.sub (Int.ediv (Int.mul 2 (Int.mul c c)) pulseTbl) pulseTbl)
            fun c' ↦ sinCosDoubleLoopPulse k s' c')
        (-1, -1)
theorem cosDoubleLoopPulse_sound : ∀ (k : ℕ) (u : ℤ) (θ : ℝ), (u : ℝ) / (pulseTbl : ℝ) ≤
  Real.cos (θ / (2 : ℝ) ^ k) → 0 ≤ cosDoubleLoopPulse k u → ((cosDoubleLoopPulse k u : ℤ) : ℝ) /
  (pulseTbl : ℝ) ≤ Real.cos θ
  | 0, u, θ, hu, _ => by
    unfold cosDoubleLoopPulse
    rwa [pow_zero, div_one] at hu
  | k + 1, u, θ, hu, hnn => by
    have hs18_pos : (0 : ℤ) < pulseTbl := (by unfold pulseTbl; omega); have hs18_r : (0 : ℝ) <
      (pulseTbl : ℝ) := (by unfold pulseTbl; norm_num); unfold cosDoubleLoopPulse at hnn ⊢
    cases hble : solBleZ 0 u
    · rw [hble] at hnn; simp at hnn
    · rw [hble] at hnn; simp only [Bool.cond_true, solForceInt_eq] at hnn ⊢; have hu0 : 0 ≤ u :=
        (by rwa [solBleZ_eq, bleZ_eq_decide, decide_eq_true_eq] at hble)
      set u' : ℤ := Int.sub (Int.ediv (Int.mul 2 (Int.mul u u)) pulseTbl) pulseTbl
      have hu_cos : (u : ℝ) / (pulseTbl : ℝ) ≤ Real.cos ((θ / (2 : ℝ) ^ k) / 2) :=
        (by rwa [div_div, ← pow_succ]); have hstep := two_mul_sq_sub_one_le_cos (div_nonneg
        (by exact_mod_cast hu0) hs18_r.le) hu_cos
      have hd_u := ediv_pos_le_real (2 * (u * u)) pulseTbl hs18_pos
      have hu'_le : (u' : ℝ) / (pulseTbl : ℝ) ≤ 2 * ((u : ℝ) / (pulseTbl : ℝ)) ^ 2 - 1 := by
        have hdef : u' = (2 * (u * u)) / pulseTbl - pulseTbl := rfl; rw [hdef, Int.cast_sub,
          sub_div, div_self hs18_r.ne']; have hdiv := div_le_div_of_nonneg_right hd_u hs18_r.le
        have halg : ((2 * (u * u) : ℤ) : ℝ) / (pulseTbl : ℝ) / (pulseTbl : ℝ) = 2 * ((u : ℝ) /
          (pulseTbl : ℝ)) ^ 2 := (by push_cast; field_simp [hs18_r.ne']); linarith
      exact cosDoubleLoopPulse_sound k u' θ (hu'_le.trans hstep) hnn
theorem sinCosDoubleLoopPulse_sound : ∀ (k : ℕ) (s c : ℤ) (θ : ℝ), (s : ℝ) / (pulseTbl : ℝ) ≤
  Real.sin (θ / (2 : ℝ) ^ k) → (c : ℝ) / (pulseTbl : ℝ) ≤ Real.cos (θ / (2 : ℝ) ^ k) → 0 ≤
  (sinCosDoubleLoopPulse k s c).1 → 0 ≤ (sinCosDoubleLoopPulse k s c).2 →
  (((sinCosDoubleLoopPulse k s c).1 : ℤ) : ℝ) / (pulseTbl : ℝ) ≤ Real.sin θ ∧
  (((sinCosDoubleLoopPulse k s c).2 : ℤ) : ℝ) / (pulseTbl : ℝ) ≤ Real.cos θ
  | 0, s, c, θ, hs, hc, _, _ =>
      ⟨by unfold sinCosDoubleLoopPulse; rwa [pow_zero, div_one] at hs,
       by unfold sinCosDoubleLoopPulse; rwa [pow_zero, div_one] at hc⟩
  | k + 1, s, c, θ, hs, hc, hnn1, hnn2 => by
      have hs18_pos : (0 : ℤ) < pulseTbl := (by unfold pulseTbl; omega); have hs18_r : (0 : ℝ) <
        (pulseTbl : ℝ) := (by unfold pulseTbl; norm_num)
      unfold sinCosDoubleLoopPulse at hnn1 hnn2 ⊢; cases hble : (solBleZ 0 s && solBleZ 0 c)
      · rw [hble] at hnn1; simp at hnn1
      · rw [hble] at hnn1 hnn2; simp only [Bool.cond_true, solForceInt_eq] at hnn1 hnn2 ⊢
        have hsc0 : 0 ≤ s ∧ 0 ≤ c := by simpa [solBleZ_eq, bleZ_eq_decide] using hble
        set α : ℝ := (θ / (2 : ℝ) ^ k) / 2; have hα_eq : θ / (2 : ℝ) ^ (k + 1) = α :=
          (by dsimp [α]; rw [div_div, ← pow_succ]); rw [hα_eq] at hs hc; have hs_nn : 0 ≤ (s : ℝ) /
          (pulseTbl : ℝ) := div_nonneg (by exact_mod_cast hsc0.1) hs18_r.le; have hc_nn : 0 ≤ (c :
          ℝ) / (pulseTbl : ℝ) := div_nonneg (by exact_mod_cast hsc0.2) hs18_r.le; set s' : ℤ :=
          Int.ediv (Int.mul 2 (Int.mul s c)) pulseTbl; set c' : ℤ := Int.sub (Int.ediv (Int.mul 2
          (Int.mul c c)) pulseTbl) pulseTbl
        have hs'_le : (s' : ℝ) / (pulseTbl : ℝ) ≤ Real.sin (θ / (2 : ℝ) ^ k) := by
          have hd_s := ediv_pos_le_real (2 * (s * c)) pulseTbl hs18_pos; have hdiv :=
            div_le_div_of_nonneg_right hd_s hs18_r.le; have halg : ((2 * (s * c) : ℤ) : ℝ) /
            (pulseTbl : ℝ) / (pulseTbl : ℝ) = 2 * ((s : ℝ) / (pulseTbl : ℝ)) * ((c : ℝ) /
            (pulseTbl : ℝ)) := (by push_cast; field_simp [hs18_r.ne']); have hdef : s' = (2 * (s *
            c)) / pulseTbl := rfl; have hm : ((s : ℝ) / (pulseTbl : ℝ)) * ((c : ℝ) / (pulseTbl
            : ℝ)) ≤ Real.sin α * Real.cos α := mul_le_mul hs hc hc_nn (hs_nn.trans hs)
          have h2s : Real.sin (θ / (2 : ℝ) ^ k) = 2 * Real.sin α * Real.cos α := by
            conv_lhs => rw [show θ / (2 : ℝ) ^ k = 2 * α by dsimp [α]; ring]
            exact Real.sin_two_mul α
          rw [hdef, h2s]; linarith
        have hc'_le : (c' : ℝ) / (pulseTbl : ℝ) ≤ Real.cos (θ / (2 : ℝ) ^ k) := by
          have hstep := two_mul_sq_sub_one_le_cos hc_nn hc; have hd_c := ediv_pos_le_real (2 * (c *
            c)) pulseTbl hs18_pos; have hdiv := div_le_div_of_nonneg_right hd_c hs18_r.le
          have halg : ((2 * (c * c) : ℤ) : ℝ) / (pulseTbl : ℝ) / (pulseTbl : ℝ) = 2 * ((c : ℝ) /
            (pulseTbl : ℝ)) ^ 2 := (by push_cast; field_simp [hs18_r.ne']); have hdef : c' = (2 *
            (c * c)) / pulseTbl - pulseTbl := rfl
          have hc'_alg : (c' : ℝ) / (pulseTbl : ℝ) ≤ 2 * ((c : ℝ) / (pulseTbl : ℝ)) ^ 2 - 1 :=
            (by rw [hdef, Int.cast_sub, sub_div, div_self hs18_r.ne']; linarith)
          exact hc'_alg.trans hstep
        exact sinCosDoubleLoopPulse_sound k s' c' θ hs'_le hc'_le hnn1 hnn2
/-- Pure-integer 1-ULP `1024`-subdivision trig checker with pre-truncation `10^18`
  Pythagorean
  upper bounds on `[a / d, b / e] ⊆ (0, 1]`. -/
def checkSwLTrigRatPulse (a d b e cLo cHi sLo sHi : ℤ) : Bool :=
  let cNum1024 : ℤ := 6291456000000000000000000000000000000000000
  let cDen1024 : ℤ := 6442450944000000000000000000000000000000000000
  let cCosDen1024 : ℤ := 2097152000000000000000000
  solForceInt (Int.ediv (Int.mul a pulseTbl) d) fun qLoLo ↦
    solForceInt (Int.neg (Int.ediv (Int.neg (Int.mul a pulseTbl)) d)) fun qLoHi ↦
      solForceInt (Int.neg (Int.ediv (Int.neg (Int.mul b pulseTbl)) e)) fun qHiHi ↦
        solForceInt
          (Int.ediv (Int.mul qLoLo (Int.sub cNum1024 (Int.mul qLoLo qLoLo))) cDen1024)
          fun s1024Lo ↦
            solForceInt
              (Int.sub pulseTbl
                (Int.neg (Int.ediv (Int.neg (Int.mul qLoHi qLoHi)) cCosDen1024)))
              fun c1024Lo ↦
                solForceInt
                  (Int.sub pulseTbl
                    (Int.neg (Int.ediv (Int.neg (Int.mul qHiHi qHiHi)) cCosDen1024)))
                  fun c1024H ↦
                    match sinCosDoubleLoopPulse 10 s1024Lo c1024Lo with
                    | (s1Lo, c1Lo) =>
                        solForceInt (cosDoubleLoopPulse 10 c1024H) fun c1H ↦
                          let sHiS := Int.mul sHi swScale
                          let cHiS := Int.mul cHi swScale
                          let s18Sq := Int.mul pulseTbl pulseTbl
                          solBleZ 1 a && solBleZ 1 d && solBleZ 0 b && solBleZ 1 e &&
                          solBleZ b e && solBleZ 0 cLo && solBleZ 0 cHi && solBleZ 0 sLo &&
                          solBleZ 0 sHi && solBleZ 1 qLoLo && solBleZ qLoHi pulseTbl &&
                          solBleZ qHiHi pulseTbl && solBleZ 0 s1Lo && solBleZ 0 c1Lo &&
                          solBleZ 0 c1H &&
                          solBleZ (Int.mul sLo pulseTbl) (Int.mul s1Lo swScale) &&
                          solBleZ (Int.mul cLo pulseTbl) (Int.mul c1H swScale) &&
                          solBleZ s18Sq (Int.add (Int.mul c1H c1H) (Int.mul sHiS sHiS)) &&
                          solBleZ s18Sq (Int.add (Int.mul s1Lo s1Lo) (Int.mul cHiS cHiS))
theorem checkSwLTrigRatPulse_sound {a d b e cLo cHi sLo sHi : ℤ} {φ : ℝ} (hlo : (a : ℝ) / (d : ℝ)
  ≤ φ) (hhi : φ ≤ (b : ℝ) / (e : ℝ)) (hchk : checkSwLTrigRatPulse a d b e cLo cHi sLo sHi = true)
  : memIvInt (Real.cos φ) (cLo, cHi) ∧ memIvInt (Real.sin φ) (sLo, sHi) := by
  unfold checkSwLTrigRatPulse at hchk; simp only [solForceInt_eq] at hchk; set cNum1024 : ℤ :=
    6291456000000000000000000000000000000000000; set cDen1024 : ℤ :=
    6442450944000000000000000000000000000000000000; set cCosDen1024 : ℤ :=
    2097152000000000000000000; set qLoLo : ℤ := (a * pulseTbl) / d; set qLoHi : ℤ := -((-(a *
    pulseTbl)) / d); set qHiHi : ℤ := -((-(b * pulseTbl)) / e); set s1024Lo : ℤ := (qLoLo *
    (cNum1024 - qLoLo * qLoLo)) / cDen1024; set c1024Lo : ℤ := pulseTbl - (-((-(qLoHi * qLoHi)) /
    cCosDen1024)); set c1024H : ℤ := pulseTbl - (-((-(qHiHi * qHiHi)) / cCosDen1024)); set sc1 :=
    sinCosDoubleLoopPulse 10 s1024Lo c1024Lo; set c1H := cosDoubleLoopPulse 10 c1024H
  change (solBleZ 1 a && solBleZ 1 d && solBleZ 0 b && solBleZ 1 e && solBleZ b e && solBleZ 0 cLo
    && solBleZ 0 cHi && solBleZ 0 sLo && solBleZ 0 sHi && solBleZ 1 qLoLo && solBleZ qLoHi
    pulseTbl && solBleZ qHiHi pulseTbl && solBleZ 0 sc1.1 && solBleZ 0 sc1.2 && solBleZ 0 c1H &&
    solBleZ (Int.mul sLo pulseTbl) (Int.mul sc1.1 swScale) && solBleZ (Int.mul cLo pulseTbl)
    (Int.mul c1H swScale) && solBleZ (Int.mul pulseTbl pulseTbl) (Int.add (Int.mul c1H c1H)
    (Int.mul (Int.mul sHi swScale) (Int.mul sHi swScale))) && solBleZ (Int.mul pulseTbl
    pulseTbl) (Int.add (Int.mul sc1.1 sc1.1) (Int.mul (Int.mul cHi swScale) (Int.mul cHi
    swScale)))) = true at hchk; simp only [solBleZ_eq, bleZ_eq_decide, Bool.and_eq_true,
    decide_eq_true_eq, solIntMul_eq, solIntAdd_eq] at hchk; rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_,
    hd1⟩, _⟩, he1⟩, _⟩, _⟩, hcHi0⟩, _⟩, hsHi0⟩, hqLoLo1⟩, hqLoHi_le⟩, hqHiHi_le⟩, hs1Lo0⟩, hc1Lo0⟩,
    hc1H0⟩, hsin_ineq⟩, hcos_ineq⟩, hcs_hi⟩, hsc_hi⟩; have hs18_pos : (0 : ℤ) < pulseTbl :=
    (by unfold pulseTbl; omega); have hs18_r : (0 : ℝ) < (pulseTbl : ℝ) :=
    (by unfold pulseTbl; norm_num); have hS : (0 : ℝ) < (swScale : ℝ) :=
    (by unfold swScale; norm_num); have hd : 0 < d := (by omega)
  have he : 0 < e := (by omega); set qLo : ℝ := (a : ℝ) / (d : ℝ); set qHi : ℝ := (b : ℝ) / (e : ℝ)
  set xLo : ℝ := (qLoLo : ℝ) / (pulseTbl : ℝ); set xHi : ℝ := (qLoHi : ℝ) / (pulseTbl : ℝ)
  set yHi : ℝ := (qHiHi : ℝ) / (pulseTbl : ℝ)
  have hxLo_le_qLo : xLo ≤ qLo := ediv_scale_le_div a d pulseTbl hd hs18_pos
  have hqLo_le_xHi : qLo ≤ xHi := div_le_ceil_ediv_scale a d pulseTbl hd hs18_pos
  have hqHi_le_yHi : qHi ≤ yHi := div_le_ceil_ediv_scale b e pulseTbl he hs18_pos
  have hxLo_pos : 0 < xLo := div_pos (by exact_mod_cast (by omega : 0 < qLoLo)) hs18_r
  have hxHi_le1 : xHi ≤ 1 := (div_le_one hs18_r).2 (by exact_mod_cast hqLoHi_le)
  have hyHi_le1 : yHi ≤ 1 := (div_le_one hs18_r).2 (by exact_mod_cast hqHiHi_le)
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hs1024_le : (s1024Lo : ℝ) / (pulseTbl : ℝ) ≤ Real.sin (qLo / (2 : ℝ) ^ 10) := by
    have hmono : Real.sin (xLo / 1024) ≤ Real.sin (qLo / 1024) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have hcube : xLo / 1024 - (xLo / 1024) ^ 3 / 6 ≤ Real.sin (xLo / 1024) := Real.sin_ge_sub_cube
      (by positivity); have hd_den : (0 : ℤ) < cDen1024 := (by dsimp [cDen1024]; norm_num)
    have hdiv := ediv_pos_le_real (qLoLo * (cNum1024 - qLoLo * qLoLo)) cDen1024 hd_den
    have hdiv2 := div_le_div_of_nonneg_right hdiv hs18_r.le; have halg : ((qLoLo * (cNum1024 - qLoLo
      * qLoLo) : ℤ) : ℝ) / (cDen1024 : ℝ) / (pulseTbl : ℝ) = xLo / 1024 - (xLo / 1024) ^ 3 / 6 :=
      (by dsimp [xLo, cNum1024, cDen1024]; unfold pulseTbl; push_cast; ring)
    have h2_10 : (2 : ℝ) ^ 10 = 1024 := (by norm_num); rw [h2_10]; dsimp [s1024Lo]; linarith
  have hc1024Lo_le : (c1024Lo : ℝ) / (pulseTbl : ℝ) ≤ Real.cos (qLo / (2 : ℝ) ^ 10) := by
    have hmono : Real.cos (xHi / 1024) ≤ Real.cos (qLo / 1024) := Real.cos_le_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith) (by linarith); have hd_cd : (0 : ℤ) < cCosDen1024 :=
      (by dsimp [cCosDen1024]; norm_num)
    have hceil := real_le_neg_ediv_neg_pos (qLoHi * qLoHi) cCosDen1024 hd_cd
    have hsub : (c1024Lo : ℝ) ≤ (pulseTbl : ℝ) - ((qLoHi * qLoHi : ℤ) : ℝ) / (cCosDen1024 : ℝ) :=
      (by dsimp [c1024Lo]; rw [Int.cast_sub]; linarith [hceil]); have hdiv :=
      div_le_div_of_nonneg_right hsub hs18_r.le; have halg : ((pulseTbl : ℝ) - ((qLoHi * qLoHi :
      ℤ) : ℝ) / (cCosDen1024 : ℝ)) / (pulseTbl : ℝ) = 1 - (xHi / 1024) ^ 2 / 2 :=
      (by dsimp [xHi, cCosDen1024]; unfold pulseTbl; push_cast; ring); have h2_10 : (2 : ℝ) ^ 10 =
      1024 := (by norm_num); rw [h2_10]; exact ((hdiv.trans_eq halg).trans
      Real.one_sub_sq_div_two_le_cos).trans hmono
  have hc1024H_le : (c1024H : ℝ) / (pulseTbl : ℝ) ≤ Real.cos (yHi / (2 : ℝ) ^ 10) := by
    have hd_cd : (0 : ℤ) < cCosDen1024 := (by dsimp [cCosDen1024]; norm_num); have hceil :=
      real_le_neg_ediv_neg_pos (qHiHi * qHiHi) cCosDen1024 hd_cd
    have hsub : (c1024H : ℝ) ≤ (pulseTbl : ℝ) - ((qHiHi * qHiHi : ℤ) : ℝ) / (cCosDen1024 : ℝ) :=
      (by dsimp [c1024H]; rw [Int.cast_sub]; linarith [hceil]); have hdiv :=
      div_le_div_of_nonneg_right hsub hs18_r.le; have halg : ((pulseTbl : ℝ) - ((qHiHi * qHiHi :
      ℤ) : ℝ) / (cCosDen1024 : ℝ)) / (pulseTbl : ℝ) = 1 - (yHi / 1024) ^ 2 / 2 :=
      (by dsimp [yHi, cCosDen1024]; unfold pulseTbl; push_cast; ring); have h2_10 : (2 : ℝ) ^ 10 =
      1024 := (by norm_num); rw [h2_10]
    exact (hdiv.trans_eq halg).trans Real.one_sub_sq_div_two_le_cos
  rcases sinCosDoubleLoopPulse_sound 10 s1024Lo c1024Lo qLo hs1024_le hc1024Lo_le hs1Lo0 hc1Lo0
    with ⟨hs1Lo_qLo, _⟩; have hc1H_yHi := cosDoubleLoopPulse_sound 10 c1024H yHi hc1024H_le hc1H0
  have hs1Lo_φ : (sc1.1 : ℝ) / (pulseTbl : ℝ) ≤ Real.sin φ := hs1Lo_qLo.trans
    (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hlo); have hc1H_φ : (c1H :
    ℝ) / (pulseTbl : ℝ) ≤ Real.cos φ := hc1H_yHi.trans (Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith) (by linarith) (hhi.trans hqHi_le_yHi))
  have hsin_φ : (sLo : ℝ) / (swScale : ℝ) ≤ Real.sin φ := by
    have hineq : (sLo : ℝ) / (swScale : ℝ) ≤ (sc1.1 : ℝ) / (pulseTbl : ℝ) :=
      (by rw [div_le_div_iff₀ hS hs18_r]; exact_mod_cast hsin_ineq); exact hineq.trans hs1Lo_φ
  have hcos_φ : (cLo : ℝ) / (swScale : ℝ) ≤ Real.cos φ := by
    have hineq : (cLo : ℝ) / (swScale : ℝ) ≤ (c1H : ℝ) / (pulseTbl : ℝ) :=
      (by rw [div_le_div_iff₀ hS hs18_r]; exact_mod_cast hcos_ineq); exact hineq.trans hc1H_φ
  have hcs_hi_r : 1 ≤ ((c1H : ℝ) / (pulseTbl : ℝ)) ^ 2 + ((sHi : ℝ) / (swScale : ℝ)) ^ 2 := by
    have hcast : ((pulseTbl * pulseTbl : ℤ) : ℝ) ≤ ((c1H * c1H + (sHi * swScale) * (sHi *
      swScale) : ℤ) : ℝ) := Int.cast_le.2 hcs_hi
    have hsHi_eq : (sHi : ℝ) / (swScale : ℝ) = ((sHi * swScale : ℤ) : ℝ) / (pulseTbl : ℝ) :=
      (by push_cast; unfold pulseTbl swScale; norm_num; ring); rw [hsHi_eq, div_pow, div_pow, ←
      add_div, one_le_div (sq_pos_of_pos hs18_r)]; have hid1 : ((pulseTbl * pulseTbl : ℤ) : ℝ) =
      (pulseTbl : ℝ) ^ 2 := (by push_cast; ring)
    have hid2 : ((c1H * c1H + (sHi * swScale) * (sHi * swScale) : ℤ) : ℝ) = (c1H : ℝ) ^ 2 + ((sHi *
      swScale : ℤ) : ℝ) ^ 2 := by
      rw [Int.cast_add, Int.cast_mul c1H c1H, Int.cast_mul (sHi * swScale) (sHi * swScale), sq, sq]
    rwa [hid1, hid2] at hcast
  have hsc_hi_r : 1 ≤ ((sc1.1 : ℝ) / (pulseTbl : ℝ)) ^ 2 + ((cHi : ℝ) / (swScale : ℝ)) ^ 2 := by
    have hcast : ((pulseTbl * pulseTbl : ℤ) : ℝ) ≤ ((sc1.1 * sc1.1 + (cHi * swScale) * (cHi *
      swScale) : ℤ) : ℝ) := Int.cast_le.2 hsc_hi
    have hcHi_eq : (cHi : ℝ) / (swScale : ℝ) = ((cHi * swScale : ℤ) : ℝ) / (pulseTbl : ℝ) :=
      (by push_cast; unfold pulseTbl swScale; norm_num; ring); rw [hcHi_eq, div_pow, div_pow, ←
      add_div, one_le_div (sq_pos_of_pos hs18_r)]; have hid1 : ((pulseTbl * pulseTbl : ℤ) : ℝ) =
      (pulseTbl : ℝ) ^ 2 := (by push_cast; ring)
    have hid2 : ((sc1.1 * sc1.1 + (cHi * swScale) * (cHi * swScale) : ℤ) : ℝ) = (sc1.1 : ℝ) ^ 2 +
      ((cHi * swScale : ℤ) : ℝ) ^ 2 := by
      rw [Int.cast_add, Int.cast_mul sc1.1 sc1.1, Int.cast_mul (cHi * swScale) (cHi * swScale), sq,
        sq]
    rwa [hid1, hid2] at hcast
  have hsin_ub : Real.sin φ ≤ (sHi : ℝ) / (swScale : ℝ) := sq_bound_of_sin_cos_ge (div_nonneg
    (by exact_mod_cast hc1H0) hs18_r.le) (div_nonneg (by exact_mod_cast hsHi0) hS.le)
    (Real.cos_sq_add_sin_sq φ) hcs_hi_r hc1H_φ; have hcos_ub : Real.cos φ ≤ (cHi : ℝ) / (swScale :
    ℝ) := sq_bound_of_sin_cos_ge (div_nonneg (by exact_mod_cast hs1Lo0) hs18_r.le) (div_nonneg
    (by exact_mod_cast hcHi0) hS.le) (Real.sin_sq_add_cos_sq φ) hsc_hi_r hs1Lo_φ; exact ⟨⟨hcos_φ,
    hcos_ub⟩, ⟨hsin_φ, hsin_ub⟩⟩
/-- Pure-integer ratio-bound check for stratum `1 ≤ shiftW ≤ 1023` on `[rMin, rMax]` (`≤
  1024`). -/
def checkSwLStratumRatioPulse (rMin rMax shiftW : ℕ) (ratioLo ratioHi : ℤ) : Bool :=
  let s20 : ℤ := 100000000000000000000
  let lo1 := Int.add ratioLo 1
  let hi1 := Int.sub ratioHi 1
  let rMinZ := Int.ofNat rMin
  let rMaxZ := Int.ofNat rMax
  let wZ := Int.ofNat shiftW
  let sSq := Int.mul swScale swScale
  (Nat.ble (Nat.add shiftW 1) rMin &&
    (Nat.ble rMin rMax &&
      (Nat.ble rMax 1024 && (Nat.ble 1 shiftW && Nat.ble shiftW 1023)))) &&
  solBleZ 1 ratioLo && solBleZ 2 ratioHi && solBleZ ratioHi swScale &&
  solBleZ (Int.mul (Int.mul lo1 lo1) rMinZ) (Int.mul sSq (Int.sub rMinZ wZ)) &&
  solBleZ (Int.mul sSq (Int.sub rMaxZ wZ)) (Int.mul (Int.sub (Int.mul hi1 hi1) wZ) rMaxZ) &&
  solBleZ (Int.mul ratioLo s20) (Int.mul lo1 (Int.sub s20 1)) &&
  solBleZ (Int.mul hi1 s20) (Int.mul ratioHi (Int.sub s20 1))
theorem stratum_angle_ratio_boundsPulse {N r rMin rMax shiftW : ℕ} {ratioLo ratioHi : ℤ} (hN96 :
  (79228162514264337593543950336 : ℝ) ≤ (N : ℝ)) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk :
  checkSwLStratumRatioPulse rMin rMax shiftW ratioLo ratioHi = true) :
    let α₀ := Real.arcsin (1 / √((N : ℝ) / (r : ℝ))); let θ := swLThetaShiftReal N r shiftW
    ((ratioLo : ℝ) / (swScale : ℝ)) * (2 * α₀) ≤ θ ∧ θ ≤ ((ratioHi : ℝ) / (swScale : ℝ)) * (2 * α₀)
      := by
  intro α₀ θ; unfold checkSwLStratumRatioPulse at hchk; simp only [solBleZ_eq, bleZ_eq_decide,
    solNatBle_eq_decide, Bool.and_eq_true, decide_eq_true_eq, solNatAdd_eq, solIntAdd_eq,
    solIntSub_eq, solIntMul_eq, Int.ofNat_eq_natCast] at hchk; rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨hsw_min, _,
    hrMax_1024, hsw1, hsw1023⟩, hrat_lo1⟩, hrat_hi2⟩, hrat_hi_le⟩, hsq_lo⟩, hsq_hi⟩, hc_lo20⟩,
    hc_hi20⟩; have hS : (0 : ℝ) < (swScale : ℝ) := (by unfold swScale; norm_num)
  have hr_ge : shiftW + 1 ≤ r := hsw_min.trans hmin; have hr1024 : r ≤ 1024 := hmax.trans hrMax_1024
  have hr_pos : (0 : ℝ) < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r)); have hrMin_pos : (0 :
    ℝ) < (rMin : ℝ) := (by exact_mod_cast (by omega : 0 < rMin)); have hrMax_pos : (0 : ℝ) < (rMax :
    ℝ) := (by exact_mod_cast (by omega : 0 < rMax)); have hN_pos : (0 : ℝ) < (N : ℝ) :=
    (by linarith); set d : ℕ := 2 * shiftW; have hd_r : (d : ℝ) ≤ 2046 :=
    (by exact_mod_cast (by omega : d ≤ 2046)); have hNd_eq : (N : ℝ) - 2 * (shiftW : ℝ) = (N : ℝ) -
    (d : ℝ) := (by dsimp [d]; push_cast; ring); have hNd_pos : (0 : ℝ) < (N : ℝ) - (d : ℝ) :=
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
      have hN_ge : (65536000000000000000000002046 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hN96
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
    rw [hx0_sq, hxk_sq]; have h1 : (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) ^ 2 ≤
        ((rMin : ℝ) - (shiftW : ℝ)) / (rMin : ℝ) := by
      rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos hS) hrMin_pos]; have hcast : (((ratioLo + 1) *
        (ratioLo + 1) * (rMin : ℤ) : ℤ) : ℝ) ≤ ((swScale * swScale * ((rMin : ℤ) - (shiftW : ℤ)) :
        ℤ) : ℝ) := Int.cast_le.2 hsq_lo; have hl_eq : (((ratioLo + 1 : ℤ) : ℝ) ^ 2) * (rMin : ℝ) =
        (((ratioLo + 1) * (ratioLo + 1) * (rMin : ℤ) : ℤ) : ℝ) := (by push_cast; ring)
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
        : ℤ) : ℝ) := Int.cast_le.2 hsq_hi
      have hl_eq : ((rMax : ℝ) - (shiftW : ℝ)) * (swScale : ℝ) ^ 2 = ((swScale * swScale * ((rMax :
        ℤ) - (shiftW : ℤ)) : ℤ) : ℝ) := (by push_cast; ring); have hr_eq : (a ^ 2 - (shiftW : ℝ)) *
        (rMax : ℝ) = ((((ratioHi - 1) * (ratioHi - 1) - (shiftW : ℤ)) * (rMax : ℤ) : ℤ) : ℝ) :=
        (by dsimp [a]; push_cast; ring); rw [hl_eq, hr_eq]; exact hcast
    have hsw1_r : (1 : ℝ) ≤ (shiftW : ℝ) := (by exact_mod_cast hsw1)
    have hN_ratio : (N : ℝ) / ((N : ℝ) - (d : ℝ)) ≤ (swScale : ℝ) ^ 2 / ((swScale : ℝ) ^ 2 - 1)
      := by
      have hS2_1 : (0 : ℝ) < (swScale : ℝ) ^ 2 - 1 := (by unfold swScale; norm_num)
      rw [div_le_div_iff₀ hNd_pos hS2_1]
      have hdS : (d : ℝ) * (swScale : ℝ) ^ 2 ≤ (N : ℝ) :=
        calc (d : ℝ) * (swScale : ℝ) ^ 2
          _ ≤ 2046 * (swScale : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hd_r (sq_nonneg _)
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
      (s20 - 1) := (by dsimp [s20]; push_cast; ring)
    rw [hl_eq, hr_eq] at hcast0; have h1 : (ratioLo : ℝ) / (swScale : ℝ) ≤
        (((ratioLo + 1 : ℤ) : ℝ) / (swScale : ℝ)) * (1 - 1 / s20) := by
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
    rw [hl_eq, hr_eq] at hcast0; have h1 : ((ratioHi - 1 : ℤ) : ℝ) / (swScale : ℝ) ≤
        ((ratioHi : ℝ) / (swScale : ℝ)) * (1 - 1 / s20) := by
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
  have hθ_eq : θ = 2 * β := (by dsimp [θ, swLThetaShiftReal, β, xk]; rw [hNd_eq])
  rw [hθ_eq]; exact ⟨by linarith, by linarith⟩
/-- Linear `O(L)` zipper walking strata `w.. w + rem - 1` of `(ratios, restTrig)`. -/
def checkSwLBucketAnglesWalkPulse :
    ℕ → ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → List IvInt → List (IvInt × IvInt) → Bool
  | 0, _, _, _, _, _, _, _, [], [] => true
  | rem + 1, w, rMin, rMax, tauNumZ, tauDenS, q1HiNum, q1HiDenS, rat :: rs, (cIv, sIv) :: ts =>
      checkSwLStratumRatioPulse rMin rMax w rat.1 rat.2 &&
      checkSwLTrigRatPulse (Int.mul tauNumZ rat.1) tauDenS
        (Int.mul q1HiNum rat.2) q1HiDenS cIv.1 cIv.2 sIv.1 sIv.2 &&
      solForceNat (Nat.add w 1) fun w' ↦
        checkSwLBucketAnglesWalkPulse rem w' rMin rMax tauNumZ tauDenS q1HiNum q1HiDenS
          rs ts
  | _, _, _, _, _, _, _, _, _, _ => false
/-- Pure-integer `2 ≤ L ≤ 1024` bucket angle checker on `[rMin, rMax]` in `O(L)` kernel
  time. -/
def checkSwLBucketAnglesPulse (L rMin rMax tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  let s11 : ℤ := 100000000000
  let tauNumZ := Int.ofNat tauNum
  let tauDenZ := Int.ofNat tauDen
  solForceInt (Int.add (Int.mul tauNumZ s11) tauDenZ) fun q1HiNum ↦
    solForceInt (Int.mul tauDenZ s11) fun q1HiDen ↦
      solForceInt (Int.mul tauDenZ swScale) fun tauDenS ↦
        solForceInt (Int.mul q1HiDen swScale) fun q1HiDenS ↦
          (Nat.ble 2 L &&
            (Nat.ble L 1024 &&
              (Nat.ble L rMin &&
                (Nat.ble rMin rMax &&
                  (Nat.ble rMax 1024 && (Nat.ble 1 tauNum && Nat.ble 1 tauDen)))))) &&
          match trigIvs with
          | [] => false
          | (c0, s0) :: restTrig =>
              checkSwLTrigRatPulse tauNumZ tauDenZ q1HiNum q1HiDen c0.1 c0.2 s0.1 s0.2 &&
              checkSwLBucketAnglesWalkPulse (Nat.sub L 1) 1 rMin rMax tauNumZ tauDenS
                q1HiNum q1HiDenS ratios restTrig
/-- Singleton `[rGrid, rGrid]` multi-pulse angle checker alias (`2 ≤ L ≤ 1024`, `L ≤ rGrid ≤
  1024`). -/
def checkPulseBucketAngles (L rGrid tauNum tauDen : ℕ)
    (ratios : List IvInt) (trigIvs : List (IvInt × IvInt)) : Bool :=
  checkSwLBucketAnglesPulse L rGrid rGrid tauNum tauDen ratios trigIvs
theorem checkSwLBucketAnglesWalkPulse_spec :
    ∀ (rem w rMin rMax : ℕ) (tauNumZ tauDenS q1HiNum q1HiDenS : ℤ)
      (ratios : List IvInt) (restTrig : List (IvInt × IvInt)),
      checkSwLBucketAnglesWalkPulse rem w rMin rMax tauNumZ tauDenS q1HiNum q1HiDenS
        ratios restTrig = true →
      ratios.length = rem ∧ restTrig.length = rem ∧
      ∀ idx < rem,
        let rat := ratios.getD idx (0, 0)
        let cs := restTrig.getD idx ((0, 0), (0, 0))
        checkSwLStratumRatioPulse rMin rMax (w + idx) rat.1 rat.2 = true ∧
        checkSwLTrigRatPulse (tauNumZ * rat.1) tauDenS (q1HiNum * rat.2) q1HiDenS
          cs.1.1 cs.1.2 cs.2.1 cs.2.2 = true
  | 0, _, _, _, _, _, _, _, [], [], _ => ⟨rfl, rfl, fun _ h ↦ by simp at h⟩
  | 0, _, _, _, _, _, _, _, _ :: _, _, h => by simp [checkSwLBucketAnglesWalkPulse] at h
  | 0, _, _, _, _, _, _, _, [], _ :: _, h => by simp [checkSwLBucketAnglesWalkPulse] at h
  | _ + 1, _, _, _, _, _, _, _, [], _, h => by simp [checkSwLBucketAnglesWalkPulse] at h
  | _ + 1, _, _, _, _, _, _, _, _ :: _, [], h => by simp [checkSwLBucketAnglesWalkPulse] at h
  | rem + 1, w, rMin, rMax, tauNumZ, tauDenS, q1HiNum, q1HiDenS,
    rat :: rs, (cIv, sIv) :: ts, h => by
    simp only [checkSwLBucketAnglesWalkPulse, solForceNat_eq, solNatAdd_eq, solIntMul_eq,
      Bool.and_eq_true] at h; rcases h with ⟨⟨hrat0, htrig0⟩, hrec⟩
    rcases checkSwLBucketAnglesWalkPulse_spec rem (w + 1) rMin rMax tauNumZ tauDenS q1HiNum
      q1HiDenS rs ts hrec with ⟨hl_r, hl_t, hih⟩
    refine ⟨by simp [hl_r], by simp [hl_t], fun idx hidx ↦ ?_⟩; rcases idx with _ | idx'
    · simpa using ⟨hrat0, htrig0⟩
    · have hsub := hih idx' (by omega); rw [show w + (idx' + 1) = (w + 1) + idx' by omega]
      simpa using hsub
theorem checkSwLBucketAnglesPulse_sound {L n r rMin rMax tauNum tauDen : ℕ} {ratios : List IvInt}
  {trigIvs : List (IvInt × IvInt)} (hn96 : 96 ≤ n) (hmin : rMin ≤ r) (hmax : r ≤ rMax) (hchk :
  checkSwLBucketAnglesPulse L rMin rMax tauNum tauDen ratios trigIvs = true) : 2 ≤ L ∧ L ≤ 1024 ∧
  L ≤ r ∧ r ≤ 1024 ∧ trigIvs.length = L ∧
    let K_blk := swLKBlk n r tauNum tauDen; let N : ℕ := 2 ^ n
    ∀ w : Fin L, memIvInt (Real.cos ((K_blk : ℝ) * swLThetaShiftReal N r w.1)) (trigIvs.getD w.1
      ((0, 0), (0, 0))).1 ∧ memIvInt (Real.sin ((K_blk : ℝ) * swLThetaShiftReal N r w.1))
      (trigIvs.getD w.1 ((0, 0), (0, 0))).2 := by
  unfold checkSwLBucketAnglesPulse at hchk; simp only [solForceInt_eq, solNatBle_eq_decide,
    Bool.and_eq_true, decide_eq_true_eq, solIntAdd_eq, solIntMul_eq, solNatSub_eq,
    Int.ofNat_eq_natCast] at hchk; rcases hchk with ⟨⟨hL2, hL1024, hLrMin, _, hrMax1024, _,
    hden_pos⟩, hm⟩
  have hLr : L ≤ r := hLrMin.trans hmin; have hr1024 : r ≤ 1024 := hmax.trans hrMax1024
  rcases trigIvs with _ | ⟨⟨c0, s0⟩, restTrig⟩
  · simp at hm
  simp only [Bool.and_eq_true] at hm; rcases hm with ⟨htrig0, hwalk⟩
  rcases checkSwLBucketAnglesWalkPulse_spec (L - 1) 1 rMin rMax (tauNum : ℤ) ((tauDen : ℤ) *
    swScale) ((tauNum : ℤ) * 100000000000 + (tauDen : ℤ)) (((tauDen : ℤ) * 100000000000) * swScale)
    ratios restTrig hwalk with ⟨_, hlen_rest, hrest⟩
  have hlen_trig : ((c0, s0) :: restTrig).length = L := (by rw [List.length_cons, hlen_rest]; omega)
  refine ⟨hL2, hL1024, hLr, hr1024, hlen_trig, ?_⟩; intro K_blk N w; have hS : (0 : ℝ) < (swScale :
    ℝ) := (by unfold swScale; norm_num); have hr_pos : (0 : ℝ) < (r : ℝ) :=
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
  set α₀ : ℝ := Real.arcsin (1 / √c₁); rcases arcsin_small_boundsL (by positivity)
    (one_div_le_one_div_of_le (by norm_num) (by linarith : (8000000000000 : ℝ) ≤ √c₁)) with
    ⟨hα_pos, hα_le, _, _⟩; set tauR : ℝ := (tauNum : ℝ) / (tauDen : ℝ); have htau_nn : 0 ≤ tauR :=
    (by positivity); set K₀ : ℕ := (round (tauR / (2 * α₀))).toNat; have hK_eq : K_blk = K₀ + 1 :=
    (by simp only [K_blk, swLKBlk, K₀, tauR, α₀, c₁, N, Nat.cast_pow, Nat.cast_ofNat])
  rcases odd_round_div_sub_mem_Icc hα_pos htau_nn with ⟨hodd_lo, hodd_hi⟩; have hφ0_lo : tauR ≤ 2 *
    (K_blk : ℝ) * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith); have hφ0_hi : 2 *
    (K_blk : ℝ) * α₀ ≤ tauR + 3 * α₀ := (by rw [hK_eq, Nat.cast_add, Nat.cast_one]; linarith)
  set s11 : ℤ := 100000000000; set q1HiNum : ℤ := (tauNum : ℤ) * s11 + (tauDen : ℤ)
  set q1HiDen : ℤ := (tauDen : ℤ) * s11
  have hq1_eq : (q1HiNum : ℝ) / (q1HiDen : ℝ) = tauR + 1 / (100000000000 : ℝ) := by
    dsimp [q1HiNum, q1HiDen, s11, tauR]
    have hden_ne : (tauDen : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega); push_cast
    field_simp [hden_ne]
  have hφ0_hi_q1 : 2 * (K_blk : ℝ) * α₀ ≤ (q1HiNum : ℝ) / (q1HiDen : ℝ) :=
    (by rw [hq1_eq]; linarith [hφ0_hi, hα_le]); rcases w with ⟨_ | idx, hw_lt⟩
  · have hN_pos : (0 : ℝ) < (N : ℝ) := (by linarith)
    have hθ0_eq : swLThetaShiftReal N r 0 = 2 * α₀ := by
      unfold swLThetaShiftReal; simp only [Nat.cast_zero, mul_zero, sub_zero, α₀, c₁]; congr 2
      rw [Real.sqrt_div hr_pos.le, Real.sqrt_div hN_pos.le, one_div_div]
    have hφ_eq : (K_blk : ℝ) * swLThetaShiftReal N r 0 = 2 * (K_blk : ℝ) * α₀ :=
      (by rw [hθ0_eq]; ring); rw [hφ_eq]
    simpa using checkSwLTrigRatPulse_sound (by simpa [tauR] using hφ0_lo) hφ0_hi_q1 htrig0
  · have hidx : idx < L - 1 := (by omega); rcases hrest idx hidx with ⟨hrat_w, htrig_w⟩; rw [show 1
      + idx = idx + 1 by omega] at hrat_w
    rcases stratum_angle_ratio_boundsPulse hN96 hmin hmax hrat_w with ⟨hr_lo, hr_hi⟩; set rat :=
      ratios.getD idx (0, 0)
    have hrat_bounds : 1 ≤ rat.1 ∧ 2 ≤ rat.2 := by
      unfold checkSwLStratumRatioPulse at hrat_w
      simp only [solBleZ_eq, bleZ_eq_decide, solNatBle_eq_decide, Bool.and_eq_true,
        decide_eq_true_eq] at hrat_w; exact ⟨hrat_w.1.1.1.1.1.1.2, hrat_w.1.1.1.1.1.2⟩
    have hrat_lo_nn : 0 ≤ (rat.1 : ℝ) / (swScale : ℝ) := div_nonneg
      (by exact_mod_cast (by omega : (0 : ℤ) ≤ rat.1)) hS.le; have hrat_hi_nn : 0 ≤ (rat.2 : ℝ) /
      (swScale : ℝ) := div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ rat.2)) hS.le
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
    simpa [List.getD_cons_succ] using checkSwLTrigRatPulse_sound hφ_lo hφ_hi htrig_w
theorem checkPulseBucketAngles_sound {L n rGrid tauNum tauDen : ℕ} {ratios : List IvInt} {trigIvs
  : List (IvInt × IvInt)} (hn96 : 96 ≤ n) (hchk : checkPulseBucketAngles L rGrid tauNum tauDen
  ratios trigIvs = true) : 2 ≤ L ∧ L ≤ 1024 ∧ L ≤ rGrid ∧ rGrid ≤ 1024 ∧ trigIvs.length = L ∧
    let K_blk := swLKBlk n rGrid tauNum tauDen; let N : ℕ := 2 ^ n
    ∀ w : Fin L, memIvInt (Real.cos ((K_blk : ℝ) * swLThetaShiftReal N rGrid w.1)) (trigIvs.getD w.1
      ((0, 0), (0, 0))).1 ∧ memIvInt (Real.sin ((K_blk : ℝ) * swLThetaShiftReal N rGrid w.1))
      (trigIvs.getD w.1 ((0, 0), (0, 0))).2 :=
  checkSwLBucketAnglesPulse_sound hn96 le_rfl le_rfl hchk
end SchurWeylLCert
end QuantumComputation.Specs.GroverFindAll
end
end Sec_PulseHdistOverlapAndAngles
section Sec_PulseM1Grover1Step
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.PulseM1
open Real
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert
open scoped BigOperators
/-- Single zero-intertwiner, zero-probe pulse `[⟨fun _ ↦ 0, 0, 1⟩]` on `L = 2`. -/
def solGrover1Pulses : List (SwLPulseRat 2) :=
  [⟨fun _ ↦ 0, 0, 1⟩]
/-- Single-pulse `L = 2` head-plane Grover stage targeting `τ = 1.57079632 ≈ π / 2`. -/
def solGrover1Stage : SwLM1StageSpec :=
  ⟨2, 157079632, 100000000, solGrover1Pulses⟩
theorem solGrover1Pulses_valid : solGrover1Pulses.all swLPulseValid = true := rfl
theorem solGrover1Evolution_eq (hL2 : 2 ≤ 2) (cs : Fin 2 → ℝ × ℝ) :
    let out := hdistLEvolutionReal 2 hL2 cs solGrover1Pulses
    out.1 ⟨0, by decide⟩ = (cs ⟨0, by decide⟩).1 ∧
    out.1 ⟨1, by decide⟩ = (cs ⟨0, by decide⟩).2 ∧
    out.1 ⟨2, by decide⟩ = 0 ∧
    out.1 ⟨3, by decide⟩ = 0 ∧
    out.2.1 = 0 ∧
    out.2.2 = 1 := by
  intro out
  have hc0 : swLCayleyCos 0 1 = 1 := by unfold swLCayleyCos; norm_num
  have hs0 : swLCayleySin 0 1 = 0 := by unfold swLCayleySin; norm_num
  set st0 : Fin (2 * 2) → ℝ := fun j ↦ if j.1 = 0 then 1 else 0
  set na : Fin (2 * 2) → ℝ := swLGroverRotVec 2 cs st0
  have hna0 : na ⟨0, by omega⟩ = (cs ⟨0, by omega⟩).1 := by
    dsimp only [na, swLGroverRotVec, st0]
    rw [ite_eq_left (by omega : (0 : ℕ) % 2 = 0),
      ite_eq_left (by omega : 2 * ((0 : ℕ) / 2) = 0),
      ite_eq_right (by omega : 2 * ((0 : ℕ) / 2) + 1 ≠ 0)]
    change (cs ⟨0, by omega⟩).1 * 1 - (cs ⟨0, by omega⟩).2 * 0 = (cs ⟨0, by omega⟩).1
    ring
  have hna1 : na ⟨1, by omega⟩ = (cs ⟨0, by omega⟩).2 := by
    dsimp only [na, swLGroverRotVec, st0]
    rw [ite_eq_right (by omega : (1 : ℕ) % 2 ≠ 0),
      ite_eq_left (by omega : 2 * ((1 : ℕ) / 2) = 0),
      ite_eq_right (by omega : 2 * ((1 : ℕ) / 2) + 1 ≠ 0)]
    change (cs ⟨0, by omega⟩).2 * 1 + (cs ⟨0, by omega⟩).1 * 0 = (cs ⟨0, by omega⟩).2
    ring
  have hna2 : na ⟨2, by omega⟩ = 0 := by
    dsimp only [na, swLGroverRotVec, st0]
    rw [ite_eq_left rfl, ite_eq_right (by omega : (2 : ℕ) ≠ 0),
      ite_eq_right (by omega : (3 : ℕ) ≠ 0)]
    ring
  have hna3 : na ⟨3, by omega⟩ = 0 := by
    dsimp only [na, swLGroverRotVec, st0]
    rw [ite_eq_right (by omega : (1 : ℕ) ≠ 0), ite_eq_right (by omega : (2 : ℕ) ≠ 0),
      ite_eq_right (by omega : (3 : ℕ) ≠ 0)]
    ring
  set p0 : SwLPulseRat 2 := ⟨fun _ ↦ 0, 0, 1⟩
  have hout_eq : out = swLPulseStepReal 2 hL2 cs st0 0 0 p0 := rfl; rw [hout_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [swLPulseStepReal, swLPieriAndWeakVec]; rw [dite_eq_left rfl]; exact hna0
  · dsimp only [swLPulseStepReal, swLPieriAndWeakVec, p0]
    rw [dite_eq_right (by omega : (1 : ℕ) ≠ 0), dite_eq_left (by omega : 1 < 2 * 2 - 1),
      ite_eq_left rfl, hc0, hs0]
    change 1 * na ⟨1, by omega⟩ - 0 * na ⟨2, by omega⟩ = _
    rw [hna1, hna2]; ring
  · dsimp only [swLPulseStepReal, swLPieriAndWeakVec, p0]
    rw [dite_eq_right (by omega : (2 : ℕ) ≠ 0), dite_eq_left (by omega : 2 < 2 * 2 - 1),
      ite_eq_right (by omega : (2 - 1) % 2 ≠ 0), hc0, hs0]
    change 0 * na ⟨1, by omega⟩ + 1 * na ⟨2, by omega⟩ = 0
    rw [hna1, hna2]; ring
  · dsimp only [swLPulseStepReal, swLPieriAndWeakVec, p0]
    rw [dite_eq_right (by omega : (3 : ℕ) ≠ 0), dite_eq_right (by omega : ¬(3 < 2 * 2 - 1)),
      hc0]
    change 1 * na ⟨3, by omega⟩ = 0
    rw [hna3]; ring
  · dsimp only [swLPulseStepReal, p0]; rw [hs0]; ring
  · dsimp only [swLPulseStepReal]; ring
theorem kBlk_two_mul_angle_mem_Icc {n r tauNum tauDen : ℕ}
    (hn96 : 96 ≤ n) (hr1 : 1 ≤ r) (hr1024 : r ≤ 1024) :
    Real.arcsin (1 / √((2 ^ n : ℝ) / (r : ℝ))) ≤ 1 / 400000000000 ∧
    (tauNum : ℝ) / (tauDen : ℝ) ≤
      2 * (swLKBlk n r tauNum tauDen : ℝ) *
        Real.arcsin (1 / √((2 ^ n : ℝ) / (r : ℝ))) ∧
    2 * (swLKBlk n r tauNum tauDen : ℝ) *
        Real.arcsin (1 / √((2 ^ n : ℝ) / (r : ℝ))) ≤
      (tauNum : ℝ) / (tauDen : ℝ) +
        3 * Real.arcsin (1 / √((2 ^ n : ℝ) / (r : ℝ))) := by
  set N : ℝ := (2 ^ n : ℝ)
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hN96 : (281474976710656 : ℝ) ^ 2 ≤ N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96
    have hpow_r : ((2 ^ 96 : ℕ) : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hpow
    have hval : ((2 ^ 96 : ℕ) : ℝ) = (281474976710656 : ℝ) ^ 2 := by norm_num
    linarith [hpow_r, hval]
  set c₁ : ℝ := N / (r : ℝ)
  have hc1_ge : (8796093022208 : ℝ) ^ 2 ≤ c₁ := by
    dsimp [c₁]; rw [le_div_iff₀ hr_pos]
    have hr_le : (r : ℝ) ≤ 1024 := by exact_mod_cast hr1024
    calc (8796093022208 : ℝ) ^ 2 * (r : ℝ)
      _ ≤ (8796093022208 : ℝ) ^ 2 * 1024 := mul_le_mul_of_nonneg_left hr_le (by norm_num)
      _ = (281474976710656 : ℝ) ^ 2 := by norm_num
      _ ≤ N := hN96
  have hsqrt_c1_ge : (8796093022208 : ℝ) ≤ √c₁ := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8796093022208)]
    exact Real.sqrt_le_sqrt hc1_ge
  set α₀ : ℝ := Real.arcsin (1 / √c₁)
  rcases arcsin_small_boundsL (by positivity)
    (one_div_le_one_div_of_le (by norm_num)
      (by linarith [hsqrt_c1_ge] : (8000000000000 : ℝ) ≤ √c₁)) with
    ⟨hα_pos, hα_le, _, _⟩
  set tauR : ℝ := (tauNum : ℝ) / (tauDen : ℝ)
  have htau_nn : 0 ≤ tauR := div_nonneg (by positivity) (by positivity)
  rcases odd_round_div_sub_mem_Icc hα_pos htau_nn with ⟨hodd_lo, hodd_hi⟩
  have hK_lo : tauR ≤ 2 * (swLKBlk n r tauNum tauDen : ℝ) * α₀ := by
    unfold swLKBlk; rw [Nat.cast_add, Nat.cast_one]
    dsimp [tauR, α₀, c₁, N] at hodd_lo ⊢; linarith [hodd_lo, hα_pos]
  have hK_hi : 2 * (swLKBlk n r tauNum tauDen : ℝ) * α₀ ≤ tauR + 3 * α₀ := by
    unfold swLKBlk; rw [Nat.cast_add, Nat.cast_one]
    dsimp [tauR, α₀, c₁, N] at hodd_hi ⊢; linarith [hodd_hi]
  exact ⟨hα_le, hK_lo, hK_hi⟩
theorem sin_ge_of_angle_near_pi_div_two {φ α₀ : ℝ}
    (hα_le : α₀ ≤ 1 / 400000000000)
    (hφ_lo : (157079632 : ℝ) / 100000000 ≤ φ)
    (hφ_hi : φ ≤ (157079632 : ℝ) / 100000000 + 3 * α₀) :
    1 - 1 / (swScale : ℝ) ≤ Real.sin φ := by
  have hpi_lo : (314159265358 : ℝ) / 100000000000 < π := by linarith [Real.pi_gt_d20]
  have hpi_hi : π < (314159265359 : ℝ) / 100000000000 := by linarith [Real.pi_lt_d20]
  have hdiff_nn : 0 ≤ π / 2 - φ := by linarith [hα_le, hφ_hi, hpi_lo]
  have hdiff_ub : π / 2 - φ ≤ 1 / 100000000 := by linarith [hφ_lo, hpi_hi]
  have hsq_ub : (π / 2 - φ) ^ 2 ≤ 1 / 10000000000000000 :=
    (pow_le_pow_left₀ hdiff_nn hdiff_ub 2).trans_eq (by norm_num)
  have hcos_lb : 1 - (π / 2 - φ) ^ 2 / 2 ≤ Real.cos (π / 2 - φ) := Real.one_sub_sq_div_two_le_cos
  rw [Real.cos_pi_div_two_sub] at hcos_lb
  have hS_val : (swScale : ℝ) = 1000000000 := by unfold swScale; norm_num
  rw [hS_val]; linarith [hsq_ub, hcos_lb]
theorem solGrover1_sin_ge {n r : ℕ} (hn96 : 96 ≤ n) (hr1 : 1 ≤ r) (hr1024 : r ≤ 1024) :
    let K_blk := hdistLKBlk n r 157079632 100000000
    1 - 1 / (swScale : ℝ) ≤ Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r 0) := by
  intro K_blk
  rcases @kBlk_two_mul_angle_mem_Icc n r 157079632 100000000 hn96 hr1 hr1024 with
    ⟨hα_le, hK_lo, hK_hi⟩
  have hr_nn : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hN_nn : (0 : ℝ) ≤ (2 ^ n : ℝ) := by positivity
  have hθ0 : swLThetaShiftReal (2 ^ n) r 0 =
      2 * Real.arcsin (1 / √((2 ^ n : ℝ) / (r : ℝ))) := by
    unfold swLThetaShiftReal; push_cast; rw [mul_zero, sub_zero, sub_zero]; congr 2
    rw [Real.sqrt_div hr_nn, Real.sqrt_div hN_nn, one_div_div]
  have hφ_eq : (K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r 0 =
      2 * (swLKBlk n r 157079632 100000000 : ℝ) *
        Real.arcsin (1 / √((2 ^ n : ℝ) / (r : ℝ))) := by
    dsimp only [K_blk, hdistLKBlk]; rw [hθ0]; ring
  have htau_eq : ((157079632 : ℕ) : ℝ) / ((100000000 : ℕ) : ℝ) =
      (157079632 : ℝ) / 100000000 := by norm_num
  rw [htau_eq] at hK_lo hK_hi; rw [← hφ_eq] at hK_lo hK_hi
  exact sin_ge_of_angle_near_pi_div_two hα_le hK_lo hK_hi
/-- Pure-GMP Bellman step checker for `solGrover1Stage` (`2 ≤ r ≤ 1024`, `vPrev1 ≤ vCur`)
  at `multiUnitScale = 10^16` bounding `p(2) ≤ 1 / 10^9` and `p(1) + p(2) ≥ 999999870 /
  10^9`. -/
def checkPulseGrover1Step (r : ℕ) (vCur vPrev1 vPrev2 : ℤ) : Bool :=
  Nat.ble 2 r && Nat.ble r 1024 && bleZ vPrev1 vCur &&
  solForceInt (Int.sub vCur vPrev1) fun dv0 ↦
    solForceInt (Int.sub vPrev1 vPrev2) fun dv1 ↦
      let pen1 : ℤ := cond (bleZ 0 dv1) 0 dv1
      solForceInt (Int.add (Int.mul 999999870 dv0) pen1) fun rhsInt ↦
        solForceInt (Int.sub (Int.mul rhsInt swBden49) (Int.mul multiUnitScale 7000000000))
          fun rem ↦
            bleZ 0 rem &&
            bleZ
              (let lhs := Int.mul (Int.mul (Int.mul swScale 157079632) multiUnitScale) swBden49
               Int.mul lhs lhs)
              (Int.mul (Int.mul 40000000000000000 (Int.ofNat r)) (Int.mul rem rem))
/-- Table-indexed wrapper around `checkPulseGrover1Step` at remaining count `r`. -/
def checkPulseGrover1StepTable (r : ℕ) (vTable : ℕ → ℤ) : Bool :=
  checkPulseGrover1Step r (vTable r) (vTable (Nat.sub r 1)) (vTable (Nat.sub r 2))
private theorem solGrover1_cost_ub {r : ℕ} {K_blk N : ℝ}
    (hsqrtN_ge : (swBden49 : ℝ) / 2 ≤ √N)
    (hK_ub : K_blk ≤ ((157079632 : ℝ) / (2 * 100000000 * √(r : ℝ))) * √N + 3 / 2) :
    K_blk + 2 ≤
      (((swScale : ℝ) * 157079632) / (2 * (swScale : ℝ) * 100000000 * √(r : ℝ)) +
        7000000000 / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
  have hS_val : (swScale : ℝ) = 1000000000 := by unfold swScale; norm_num
  have hS : (0 : ℝ) < (swScale : ℝ) := by rw [hS_val]; norm_num
  have hbden_r : (0 : ℝ) < (swBden49 : ℝ) := by unfold swBden49; norm_num
  have hc_nn : (0 : ℝ) ≤ 7000000000 / ((swScale : ℝ) * (swBden49 : ℝ)) :=
    div_nonneg (by norm_num) (mul_pos hS hbden_r).le
  have hoverh : (7000000000 : ℝ) / (2 * (swScale : ℝ)) ≤
      (7000000000 / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtN_ge hc_nn
    refine (?_ : (7000000000 : ℝ) / (2 * (swScale : ℝ)) =
      (7000000000 / ((swScale : ℝ) * (swBden49 : ℝ))) * ((swBden49 : ℝ) / 2)).trans_le hmul
    field_simp [hS.ne', hbden_r.ne']
  have halg1 : ((swScale : ℝ) * 157079632) / (2 * (swScale : ℝ) * 100000000 * √(r : ℝ)) =
      (157079632 : ℝ) / (2 * 100000000 * √(r : ℝ)) := by
    rw [show 2 * (swScale : ℝ) * 100000000 * √(r : ℝ) =
      (swScale : ℝ) * (2 * 100000000 * √(r : ℝ)) by ring]
    exact mul_div_mul_left 157079632 (2 * 100000000 * √(r : ℝ)) hS.ne'
  have halg2 : (3 : ℝ) / 2 + 2 = 7000000000 / (2 * (swScale : ℝ)) := by rw [hS_val]; norm_num
  have halg : ((157079632 : ℝ) / (2 * 100000000 * √(r : ℝ))) * √N + 3 / 2 + 2 =
      (((swScale : ℝ) * 157079632) / (2 * (swScale : ℝ) * 100000000 * √(r : ℝ))) * √N +
        7000000000 / (2 * (swScale : ℝ)) := by
    rw [halg1, add_assoc, halg2]
  linarith [hoverh, halg, hK_ub]
private theorem solGrover1_coef_le {r : ℕ} {rhsInt : ℤ} (hr2 : 2 ≤ r)
    (hrem0 : 0 ≤ rhsInt * swBden49 - multiUnitScale * 7000000000)
    (hsq_ineq :
      (swScale * 157079632 * multiUnitScale * swBden49) *
          (swScale * 157079632 * multiUnitScale * swBden49) ≤
        40000000000000000 * (r : ℤ) *
          ((rhsInt * swBden49 - multiUnitScale * 7000000000) *
            (rhsInt * swBden49 - multiUnitScale * 7000000000))) :
    ((swScale : ℝ) * 157079632) / (2 * (swScale : ℝ) * 100000000 * √(r : ℝ)) +
      7000000000 / ((swScale : ℝ) * (swBden49 : ℝ)) ≤
    (rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) := by
  set rem : ℤ := rhsInt * swBden49 - multiUnitScale * 7000000000
  have hS : (0 : ℝ) < (swScale : ℝ) := by unfold swScale; norm_num
  have hvsc_r : (0 : ℝ) < (multiUnitScale : ℝ) := by
    unfold SchurWeylLCert.multiUnitScale; norm_num
  have hbden_r : (0 : ℝ) < (swBden49 : ℝ) := by unfold swBden49; norm_num
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hsqrt_r_pos : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
  have hrem_r : (0 : ℝ) ≤ (rem : ℝ) := by exact_mod_cast hrem0
  have hlhs_nn : 0 ≤ (swScale : ℝ) * 157079632 * (multiUnitScale : ℝ) * (swBden49 : ℝ) := by
    positivity
  have hrhs_nn : 0 ≤ 2 * (100000000 : ℝ) * √(r : ℝ) * (rem : ℝ) :=
    mul_nonneg (by positivity) hrem_r
  have hsq_ineq' : (swScale * 157079632 * multiUnitScale * swBden49) ^ 2 ≤
      40000000000000000 * (r : ℤ) * rem ^ 2 := by
    rw [sq, sq]; exact hsq_ineq
  have hsq_r : ((swScale : ℝ) * 157079632 * (multiUnitScale : ℝ) * (swBden49 : ℝ)) ^ 2 ≤
      (2 * (100000000 : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 := by
    have hcast : (((swScale * 157079632 * multiUnitScale * swBden49) ^ 2 : ℤ) : ℝ) ≤
        ((40000000000000000 * (r : ℤ) * rem ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast hsq_ineq'
    push_cast at hcast
    have hsq_rhs : (2 * (100000000 : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2 =
        40000000000000000 * (r : ℝ) * (rem : ℝ) ^ 2 := by
      calc (2 * (100000000 : ℝ) * √(r : ℝ) * (rem : ℝ)) ^ 2
        _ = 40000000000000000 * (√(r : ℝ)) ^ 2 * (rem : ℝ) ^ 2 := by ring
        _ = 40000000000000000 * (r : ℝ) * (rem : ℝ) ^ 2 := by rw [Real.sq_sqrt hr_pos.le]
    linarith [hcast, hsq_rhs]
  have hroot : (swScale : ℝ) * 157079632 * (multiUnitScale : ℝ) * (swBden49 : ℝ) ≤
      2 * (100000000 : ℝ) * √(r : ℝ) * (rem : ℝ) := by
    rw [← Real.sqrt_sq hlhs_nn, ← Real.sqrt_sq hrhs_nn]; exact Real.sqrt_le_sqrt hsq_r
  have hrem_def :
      (rem : ℝ) = (rhsInt : ℝ) * (swBden49 : ℝ) - (multiUnitScale : ℝ) * 7000000000 := by
    dsimp [rem]; push_cast; rfl
  rw [hrem_def] at hroot
  have hpos_prod : 0 < 2 * (swScale : ℝ) * 100000000 * √(r : ℝ) * (multiUnitScale : ℝ) *
      (swBden49 : ℝ) := by positivity
  rw [← sub_nonneg]
  have hdiff : (rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) -
      (((swScale : ℝ) * 157079632) / (2 * (swScale : ℝ) * 100000000 * √(r : ℝ)) +
        7000000000 / ((swScale : ℝ) * (swBden49 : ℝ))) =
      (2 * (100000000 : ℝ) * √(r : ℝ) *
          ((rhsInt : ℝ) * (swBden49 : ℝ) - (multiUnitScale : ℝ) * 7000000000) -
        (swScale : ℝ) * 157079632 * (multiUnitScale : ℝ) * (swBden49 : ℝ)) /
      (2 * (swScale : ℝ) * 100000000 * √(r : ℝ) *
        (multiUnitScale : ℝ) * (swBden49 : ℝ)) := by
    field_simp [hS.ne', hsqrt_r_pos.ne', hvsc_r.ne', hbden_r.ne']; ring
  rw [hdiff]
  exact div_nonneg (by linarith [hroot]) hpos_prod.le
theorem checkPulseGrover1Step_sound {n r : ℕ} {vCur vPrev1 vPrev2 : ℤ} {vTable : ℕ → ℤ}
    (hn96 : 96 ≤ n)
    (hstep : checkPulseGrover1Step r vCur vPrev1 vPrev2 = true)
    (hcur : vCur ≤ vTable r)
    (hprev1 : vTable (r - 1) ≤ vPrev1)
    (hprev2 : vTable (r - 2) ≤ vPrev2) :
    let s := solGrover1Stage
    ∃ (hL2 : 2 ≤ s.L),
      s.L ≤ 1024 ∧ s.L ≤ r ∧
      s.pulses.all swLPulseValid = true ∧
      ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ),
        IsValidSwLOverlap M →
        let K_blk := hdistLKBlk n r s.tauNum s.tauDen
        let cs : Fin s.L → ℝ × ℝ := fun w ↦
          (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
           Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := hdistLEvolutionReal s.L hL2 cs s.pulses
        let p : ℕ → ℝ := swLAttemptProbReal s.L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧
        (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) +
          ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r := by
  intro s; set dv0 : ℤ := vCur - vPrev1
  set dv1 : ℤ := vPrev1 - vPrev2; set pen1 : ℤ := cond (bleZ 0 dv1) 0 dv1
  set rhsInt : ℤ := 999999870 * dv0 + pen1
  set rem : ℤ := rhsInt * swBden49 - multiUnitScale * 7000000000
  have hstep_eq : checkPulseGrover1Step r vCur vPrev1 vPrev2 =
      (Nat.ble 2 r && Nat.ble r 1024 && bleZ vPrev1 vCur && (bleZ 0 rem &&
          bleZ ((swScale * 157079632 * multiUnitScale * swBden49) *
              (swScale * 157079632 * multiUnitScale * swBden49))
            (40000000000000000 * (r : ℤ) * (rem * rem)))) := by
    unfold checkPulseGrover1Step
    simp only [solForceInt_eq, solIntSub_eq, solIntAdd_eq, solIntMul_eq, Int.ofNat_eq_natCast,
      dv0, dv1, pen1, rhsInt, rem]
  rw [hstep_eq] at hstep
  simp only [Bool.and_eq_true, solNatBle_eq_decide, bleZ_eq_decide, decide_eq_true_eq] at hstep
  rcases hstep with ⟨⟨⟨hr2, hr1024⟩, hv_mono⟩, hrem0, hsq_ineq⟩
  dsimp only [s, solGrover1Stage]
  refine ⟨le_rfl, by omega, hr2, solGrover1Pulses_valid, ?_⟩
  intro M hM; have hL2 : 2 ≤ 2 := le_rfl
  let K_blk := hdistLKBlk n r 157079632 100000000
  let cs : Fin 2 → ℝ × ℝ := fun w ↦
    (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
     Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
  let out := hdistLEvolutionReal 2 hL2 cs solGrover1Pulses
  let p : ℕ → ℝ := swLAttemptProbReal 2 hL2 M out.1 out.2.1
  let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 2, p h
  let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
  change 0 < pSucc ∧ (out.2.2 * (K_blk : ℝ) + ((2 : ℕ) : ℝ) +
      ∑ h ∈ Finset.Icc 1 2, p h * V (r - h)) / pSucc ≤ V r
  have hout_def : hdistLEvolutionReal 2 hL2 cs solGrover1Pulses = out := rfl
  have hout_def' : swLEvolutionReal 2 hL2 cs solGrover1Pulses = out := rfl
  rcases solGrover1Evolution_eq hL2 cs with ⟨_, hout1, _, hout3, hout_cum, hout_surv⟩
  rw [hout_def] at hout1 hout3 hout_cum hout_surv
  have hcs_unit : ∀ w : Fin 2, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 :=
    fun _ ↦ Real.cos_sq_add_sin_sq _
  rcases swLEvolutionReal_normSq_add_cum hL2 hcs_unit solGrover1Pulses solGrover1Pulses_valid with
    ⟨hcons, hcum0, _, _⟩
  rw [hout_def'] at hcons hcum0
  have hnorm1 : swLNormSq out.1 = 1 := by linarith [hcons, hout_cum]
  have herr_sq : swLNormSq (fun o ↦ swLOrbitProj M out.1 o - out.1 o) ≤
      ((64 : ℝ) / (swScale : ℝ)) ^ 2 := by
    have h64 := swLOrbitProj_sub_id_normSq_le (by omega : 2 ≤ 1024) hM out.1
    rw [hnorm1, mul_one] at h64; exact h64
  have hterm_le : ∀ o : Fin (2 * 2),
      (swLOrbitProj M out.1 o - out.1 o) ^ 2 ≤ ((64 : ℝ) / (swScale : ℝ)) ^ 2 := by
    intro o
    have hle : (swLOrbitProj M out.1 o - out.1 o) ^ 2 ≤
        swLNormSq (fun i ↦ swLOrbitProj M out.1 i - out.1 i) := by
      unfold swLNormSq
      exact Finset.single_le_sum
        (fun i _ ↦ sq_nonneg (swLOrbitProj M out.1 i - out.1 i)) (Finset.mem_univ o)
    linarith [hle, herr_sq]
  have hp_nn : ∀ h : ℕ, 0 ≤ p h := fun h ↦ swLAttemptProbReal_nonneg hL2 M out.1 hcum0 h
  have hp1_eq : p 1 = (swLOrbitProj M out.1 ⟨1, by omega⟩) ^ 2 +
      (swLOrbitProj M out.1 ⟨2, by omega⟩) ^ 2 := by
    dsimp only [p, swLAttemptProbReal]
    rw [ite_eq_right (by omega : (1 : ℕ) ≠ 0), dite_eq_left (by omega : 1 < 2), hout_cum]
    change (swLOrbitProj M out.1 ⟨1, by omega⟩) ^ 2 +
      (swLOrbitProj M out.1 ⟨2, by omega⟩) ^ 2 + 0 * _ = _
    ring
  have hp2_eq : p 2 = (swLOrbitProj M out.1 ⟨3, by omega⟩) ^ 2 := by
    dsimp only [p, swLAttemptProbReal]
    rw [ite_eq_right (by omega : (2 : ℕ) ≠ 0), dite_eq_right (by omega : ¬(2 < 2)),
      ite_eq_left rfl, hout_cum]
    change (swLOrbitProj M out.1 ⟨3, by omega⟩) ^ 2 + 0 * _ = _
    ring
  have hp2_ub : p 2 ≤ 1 / (swScale : ℝ) := by
    have ho3 := hterm_le ⟨3, by omega⟩
    rw [hout3, sub_zero] at ho3; rw [hp2_eq]
    have h64_1 : ((64 : ℝ) / (swScale : ℝ)) ^ 2 ≤ 1 / (swScale : ℝ) := by unfold swScale; norm_num
    exact ho3.trans h64_1
  have hS_val : (swScale : ℝ) = 1000000000 := by unfold swScale; norm_num
  have hsin_lb : 1 - 1 / (swScale : ℝ) ≤ (cs ⟨0, by omega⟩).2 :=
    solGrover1_sin_ge hn96 (by omega) hr1024
  have ho1_abs : |swLOrbitProj M out.1 ⟨1, by omega⟩ - (cs ⟨0, by omega⟩).2| ≤
      |(64 : ℝ) / (swScale : ℝ)| := by
    have ho1 := hterm_le ⟨1, by omega⟩
    rw [hout1] at ho1; exact sq_le_sq.1 ho1
  rw [abs_of_nonneg (a := (64 : ℝ) / (swScale : ℝ)) (by rw [hS_val]; norm_num)] at ho1_abs
  have ho1_lb : (999999935 : ℝ) / (swScale : ℝ) ≤ swLOrbitProj M out.1 ⟨1, by omega⟩ := by
    have hleft := (abs_le.1 ho1_abs).1; rw [hS_val] at hleft hsin_lb ⊢; linarith [hleft, hsin_lb]
  have ho1_sq_lb : (999999870 : ℝ) / (swScale : ℝ) ≤
      (swLOrbitProj M out.1 ⟨1, by omega⟩) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by rw [hS_val]; norm_num) ho1_lb 2
    have hnum : (999999870 : ℝ) / (swScale : ℝ) ≤ ((999999935 : ℝ) / (swScale : ℝ)) ^ 2 := by
      rw [hS_val]; norm_num
    exact hnum.trans hsq
  have hicc : (Finset.Icc 1 2 : Finset ℕ) = {1, 2} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  have hpSucc_eq : pSucc = p 1 + p 2 := by
    dsimp only [pSucc]
    rw [hicc, Finset.sum_pair (by omega : (1 : ℕ) ≠ 2)]
  have hpSucc_lb : (999999870 : ℝ) / (swScale : ℝ) ≤ pSucc := by
    rw [hpSucc_eq, hp1_eq]
    linarith [ho1_sq_lb, sq_nonneg (swLOrbitProj M out.1 ⟨2, by omega⟩), hp_nn 2]
  have hS : (0 : ℝ) < (swScale : ℝ) := by rw [hS_val]; norm_num
  have hpSucc_pos : 0 < pSucc :=
    (div_pos (by norm_num : (0 : ℝ) < 999999870) hS).trans_le hpSucc_lb
  refine ⟨hpSucc_pos, ?_⟩
  have hvsc_r : (0 : ℝ) < (multiUnitScale : ℝ) := by unfold SchurWeylLCert.multiUnitScale; norm_num
  have hbden_r : (0 : ℝ) < (swBden49 : ℝ) := by unfold swBden49; norm_num
  set N : ℝ := (2 ^ n : ℝ)
  have hsqrtN_pos : 0 < √N := by dsimp [N]; positivity
  have hsqrtN_ge : (swBden49 : ℝ) / 2 ≤ √N := by
    have hpow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn96
    have hpow_r : ((2 ^ 96 : ℕ) : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hpow
    have h296 : ((2 ^ 96 : ℕ) : ℝ) = (281474976710656 : ℝ) ^ 2 := by norm_num
    have h1 : (281474976710656 : ℝ) ^ 2 ≤ N := by linarith [hpow_r, h296]
    have h2 : (281474976710656 : ℝ) ≤ √N := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 281474976710656)]
      exact Real.sqrt_le_sqrt h1
    have h3 : (swBden49 : ℝ) / 2 = 281474976710656 := by unfold swBden49; norm_num
    linarith [h2, h3]
  have hpen1_eq : pen1 = if 0 ≤ dv1 then 0 else dv1 := by
    dsimp only [pen1]; rw [bleZ_eq_decide]
    by_cases h0 : 0 ≤ dv1
    · rw [decide_eq_true h0, ite_eq_left h0]; rfl
    · rw [decide_eq_false h0, ite_eq_right h0]; rfl
  set Vc : ℝ := ((vCur : ℝ) / (multiUnitScale : ℝ)) * √N
  set Vp1 : ℝ := ((vPrev1 : ℝ) / (multiUnitScale : ℝ)) * √N
  set Vp2 : ℝ := ((vPrev2 : ℝ) / (multiUnitScale : ℝ)) * √N
  have hgain_vp : ((rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ))) * √N ≤
      p 1 * (Vc - Vp1) + p 2 * (Vc - Vp2) := by
    have hab : p 1 * (Vc - Vp1) + p 2 * (Vc - Vp2) =
        pSucc * (Vc - Vp1) + p 2 * (Vp1 - Vp2) := by
      rw [hpSucc_eq]; ring
    rw [hab]
    have hdv0_r : Vc - Vp1 = ((dv0 : ℝ) / (multiUnitScale : ℝ)) * √N := by
      dsimp [Vc, Vp1, dv0]; push_cast; ring
    have hdv1_r : Vp1 - Vp2 = ((dv1 : ℝ) / (multiUnitScale : ℝ)) * √N := by
      dsimp [Vp1, Vp2, dv1]; push_cast; ring
    have hdv0_nn : 0 ≤ Vc - Vp1 := by
      rw [hdv0_r]
      exact mul_nonneg
        (div_nonneg (by exact_mod_cast (by dsimp [dv0]; omega : 0 ≤ dv0)) hvsc_r.le) hsqrtN_pos.le
    have ht0 : ((999999870 * dv0 : ℤ) : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) * √N ≤
        pSucc * (Vc - Vp1) := by
      have hmul := mul_le_mul_of_nonneg_right hpSucc_lb hdv0_nn
      refine (?_ : ((999999870 * dv0 : ℤ) : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) * √N =
        ((999999870 : ℝ) / (swScale : ℝ)) * (Vc - Vp1)).trans_le hmul
      rw [hdv0_r]; push_cast; rw [← mul_assoc ((999999870 : ℝ) / (swScale : ℝ)), div_mul_div_comm]
    have ht1 : (pen1 : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) * √N ≤
        p 2 * (Vp1 - Vp2) := by
      rw [hpen1_eq]
      by_cases h0 : 0 ≤ dv1
      · simp only [h0, ↓reduceIte, Int.cast_zero, zero_div, zero_mul]; rw [hdv1_r]
        exact mul_nonneg (hp_nn 2)
          (mul_nonneg (div_nonneg (by exact_mod_cast h0) hvsc_r.le) hsqrtN_pos.le)
      · simp only [h0, ↓reduceIte]
        have hnp : Vp1 - Vp2 ≤ 0 := by
          rw [hdv1_r]
          exact mul_nonpos_of_nonpos_of_nonneg
            (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (by omega : dv1 ≤ 0)) hvsc_r.le)
            hsqrtN_pos.le
        have hmul := mul_le_mul_of_nonpos_right hp2_ub hnp
        refine (?_ : (dv1 : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) * √N =
          (1 / (swScale : ℝ)) * (Vp1 - Vp2)).trans_le hmul
        rw [hdv1_r, ← mul_assoc (1 / (swScale : ℝ)), div_mul_div_comm, one_mul]
    have hsplit : ((rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ))) * √N =
        ((999999870 * dv0 : ℤ) : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) * √N +
          (pen1 : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ)) * √N := by
      dsimp [rhsInt]; push_cast; ring
    linarith [ht0, ht1, hsplit]
  have hVc_le : Vc ≤ V r := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by exact_mod_cast hcur) hvsc_r.le) hsqrtN_pos.le
  have hVp1_ge : V (r - 1) ≤ Vp1 := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by exact_mod_cast hprev1) hvsc_r.le) hsqrtN_pos.le
  have hVp2_ge : V (r - 2) ≤ Vp2 := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by exact_mod_cast hprev2) hvsc_r.le) hsqrtN_pos.le
  have hgain_ge : ((rhsInt : ℝ) / ((swScale : ℝ) * (multiUnitScale : ℝ))) * √N ≤
      p 1 * (V r - V (r - 1)) + p 2 * (V r - V (r - 2)) :=
    hgain_vp.trans (add_le_add
      (mul_le_mul_of_nonneg_left (by linarith [hVc_le, hVp1_ge]) (hp_nn 1))
      (mul_le_mul_of_nonneg_left (by linarith [hVc_le, hVp2_ge]) (hp_nn 2)))
  have hK_ub := kBlk_le_main_add_three_halves hn96 (by omega) hr1024
    (by omega : 0 < 157079632) (by omega : 0 < 100000000)
  have hK_ub' : (K_blk : ℝ) ≤ ((157079632 : ℝ) / (2 * 100000000 * √(r : ℝ))) * √N + 3 / 2 := by
    have hn1 : ((157079632 : ℕ) : ℝ) = 157079632 := by norm_num
    have hn2 : ((100000000 : ℕ) : ℝ) = 100000000 := by norm_num
    dsimp only [K_blk, N]; rw [hn1, hn2] at hK_ub; exact hK_ub
  have hcost_ub : out.2.2 * (K_blk : ℝ) + ((2 : ℕ) : ℝ) ≤
      (((swScale : ℝ) * 157079632) / (2 * (swScale : ℝ) * 100000000 * √(r : ℝ)) +
        7000000000 / ((swScale : ℝ) * (swBden49 : ℝ))) * √N := by
    have hL_val : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hout_surv, one_mul, hL_val]; exact solGrover1_cost_ub hsqrtN_ge hK_ub'
  have hcoef_le := solGrover1_coef_le hr2 hrem0 hsq_ineq
  have hnet : out.2.2 * (K_blk : ℝ) + ((2 : ℕ) : ℝ) ≤
      p 1 * (V r - V (r - 1)) + p 2 * (V r - V (r - 2)) :=
    (hcost_ub.trans (mul_le_mul_of_nonneg_right hcoef_le hsqrtN_pos.le)).trans hgain_ge
  have hsum_V : ∑ h ∈ Finset.Icc 1 2, p h * V (r - h) =
      p 1 * V (r - 1) + p 2 * V (r - 2) := by
    rw [hicc, Finset.sum_pair (by omega : (1 : ℕ) ≠ 2)]
  rw [hsum_V, div_le_iff₀ hpSucc_pos]
  have hexpand : p 1 * (V r - V (r - 1)) + p 2 * (V r - V (r - 2)) =
      V r * pSucc - (p 1 * V (r - 1) + p 2 * V (r - 2)) := by
    rw [hpSucc_eq]; ring
  linarith [hnet, hexpand]
theorem checkPulseGrover1StepTable_sound {n r : ℕ} {vTable : ℕ → ℤ}
    (hn96 : 96 ≤ n)
    (hstep : checkPulseGrover1StepTable r vTable = true) :
    let s := solGrover1Stage
    ∃ (hL2 : 2 ≤ s.L),
      s.L ≤ 1024 ∧ s.L ≤ r ∧
      s.pulses.all swLPulseValid = true ∧
      ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ),
        IsValidSwLOverlap M →
        let K_blk := hdistLKBlk n r s.tauNum s.tauDen
        let cs : Fin s.L → ℝ × ℝ := fun w ↦
          (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
           Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := hdistLEvolutionReal s.L hL2 cs s.pulses
        let p : ℕ → ℝ := swLAttemptProbReal s.L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (multiUnitScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧
        (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) +
          ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r := by
  unfold checkPulseGrover1StepTable at hstep; rw [solNatSub_eq, solNatSub_eq] at hstep
  exact checkPulseGrover1Step_sound hn96 hstep le_rfl le_rfl le_rfl
end QuantumComputation.Specs.GroverFindAll.PulseM1
end
end Sec_PulseM1Grover1Step
