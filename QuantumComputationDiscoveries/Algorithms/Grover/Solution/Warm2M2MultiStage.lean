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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.CswapWarmR1
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Warm2M2CertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Warm2M2Part0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonP01
/-!
# Multi-Stage Piecewise-Linear `m = 2` Potential with CSWAP Warm Readout (`Warm2M2MultiStage`)

Bridges `checkWarm2CellCert` (`Warm2M2CertDefs`) and the 5 certified `m = 2` cells to
`ValidCswapWarmM2Potential` (`CswapWarmR1`) and the top-level `GroverFindAll` specification.
-/
@[expose] public section
@[local simp] private theorem _fin4_mk_eq_zero {v : ℕ} (h : v < 2 ^ 2) : (⟨v, h⟩ : Fin (2 ^ 2)) = 0
  ↔ v = 0 := ⟨fun e => congrArg Fin.val e, fun hv => Fin.ext hv⟩
@[local simp] private theorem _fin4_zero_eq_mk {v : ℕ} (h : v < 2 ^ 2) : (0 : Fin (2 ^ 2)) = ⟨v, h⟩
  ↔ 0 = v := ⟨fun e => congrArg Fin.val e, fun hv => Fin.ext hv⟩
namespace QuantumComputation.Specs.GroverFindAll.Warm2
open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal NNRat ENNReal
open PipeFuseCert
  (withForcedNat_eq allRange of_allRange
   checkClickRow checkFuseDriftCert
   harmSumPow2 sqrtMUpNat sq_le_imp_le pade56_le_arctan
   fuseDriftCert_sound clickRow_sound harmSumPow2_le_sum sqrtMUpNat_bounds)
open PipeFuseM2Cert
  (M2BinCert M2StageScalar checkPsiHi minDiffNat checkM2KnotSlope
   psiPiecewise psiPiecewise_nonneg psiPiecewise_mono psiPiecewise_sub_le
   psiPiecewise_knot checkPsiHi_sound exists_bin_of_le psiPiecewise_step_ge_minDiff)
open PipeFuse
  (pow_two_bounds_100 halfAngleSet_bounds_100 two_mul_le_pow_100
   tan_five_div_four_le_five phi_and_lockedAlpha_bounds_fuse_100)
/-! ## 1. `Fin 2` Outcome Algebra & Symmetric 2-Slot Piecewise-Linear Potential `wmPotVal` -/
/-- Certified stage threshold schedule `r ↦ arctan ((stFn r).tNum / 10^5)`. -/
noncomputable def phiFnOfWmSt (stFn : ℕ → M2StageScalar) (r : ℕ) : ℝ :=
  Real.arctan (((stFn r).tNum : ℝ) / 100000)
theorem prod_fin_two {M : Type*} [CommMonoid M] (f : Fin 2 → M) : (∏ i : Fin 2, f i) = f s0 * f s1
  := by
  have huniv : (Finset.univ : Finset (Fin 2)) = {s0, s1} := by ext i; fin_cases i <;> simp [s0, s1]
  rw [huniv, Finset.prod_pair (by simp)]
theorem sum_erase_zero_fin_four {M : Type*} [AddCommMonoid M] (g : Fin (2 ^ 2) → M) :
    (∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ 2)), g o) =
      g ⟨1, by decide⟩ + g ⟨2, by decide⟩ + g ⟨3, by decide⟩ := by
  have herase : Finset.univ.erase (0 : Fin (2 ^ 2)) = {⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩,
    ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩} :=
    (by ext x; fin_cases x <;> simp); rw [herase, Finset.sum_insert (by simp), Finset.sum_pair
    (by simp), ← add_assoc]
theorem stepWeight_fin2_zero (n r : ℕ) (φ : ℝ) (betas : Fin 2 → ℝ) : stepWeight n r φ betas 0 =
  stepAlpha n r φ (betas s0) ^ 2 * stepAlpha n r φ (betas s1) ^ 2 := by
  dsimp only [stepWeight]; rw [prod_fin_two]; rfl
theorem stepWeight_fin2_one (n r : ℕ) (φ : ℝ) (betas : Fin 2 → ℝ) :
    stepWeight n r φ betas ⟨1, by decide⟩ =
      (1 - stepAlpha n r φ (betas s0) ^ 2) * stepAlpha n r φ (betas s1) ^ 2 := by
  dsimp only [stepWeight]; rw [prod_fin_two]; rfl
theorem stepWeight_fin2_two (n r : ℕ) (φ : ℝ) (betas : Fin 2 → ℝ) :
    stepWeight n r φ betas ⟨2, by decide⟩ =
      stepAlpha n r φ (betas s0) ^ 2 * (1 - stepAlpha n r φ (betas s1) ^ 2) := by
  dsimp only [stepWeight]; rw [prod_fin_two]; rfl
theorem stepWeight_fin2_three (n r : ℕ) (φ : ℝ) (betas : Fin 2 → ℝ) :
    stepWeight n r φ betas ⟨3, by decide⟩ =
      (1 - stepAlpha n r φ (betas s0) ^ 2) * (1 - stepAlpha n r φ (betas s1) ^ 2) := by
  dsimp only [stepWeight]; rw [prod_fin_two]; rfl
/-- Joint symmetric 2-slot potential `min(x, y) + SN * psiPiecewise B dNat w (|x - y| /
  SN)`. -/
noncomputable def wmPotVal (B dNat : ℕ) (w : ℕ → ℕ) (SN x y : ℝ) : ℝ :=
  min x y + SN * psiPiecewise B dNat w (|x - y| / SN)
theorem wmPotVal_nonneg {B dNat : ℕ} {w : ℕ → ℕ} {SN x y : ℝ} (hSN : 0 ≤ SN) (hx : 0 ≤ x) (hy : 0 ≤
  y) : 0 ≤ wmPotVal B dNat w SN x y := by
  dsimp only [wmPotVal]; exact add_nonneg (le_min hx hy) (mul_nonneg hSN (psiPiecewise_nonneg B dNat
    w _))
theorem wmPotVal_comm (B dNat : ℕ) (w : ℕ → ℕ) (SN x y : ℝ) : wmPotVal B dNat w SN x y = wmPotVal B
  dNat w SN y x := by dsimp only [wmPotVal]; rw [min_comm, abs_sub_comm]
theorem wmPotVal_diag {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ i < B, w i ≤ w (i + 1) ∧ w (i
  + 1) ≤ w i + dNat) (SN s : ℝ) : wmPotVal B dNat w SN s s = s + ((w 0 : ℝ) / 1000000000000) * SN :=
  by
  dsimp only [wmPotVal]; rw [min_self, sub_self, abs_zero, zero_div]
  have hk0 := psiPiecewise_knot hd hw (Nat.zero_le B); simp only [Nat.cast_zero, zero_mul] at hk0
  rw [hk0]; ring
theorem wmPotVal_zero_left (B dNat : ℕ) (w : ℕ → ℕ) (SN : ℝ) {y : ℝ} (hy : 0 ≤ y) : wmPotVal B dNat
  w SN 0 y = SN * psiPiecewise B dNat w (y / SN) := by
  dsimp only [wmPotVal]; rw [min_eq_left hy, zero_add, zero_sub, abs_neg, abs_of_nonneg hy]
theorem wmPotVal_sub_one (B dNat : ℕ) (w : ℕ → ℕ) (SN x y : ℝ) : wmPotVal B dNat w SN (x - 1) (y -
  1) = wmPotVal B dNat w SN x y - 1 := by
  dsimp only [wmPotVal]
  have hmin : min (x - 1) (y - 1) = min x y - 1 := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]
  have habs : |(x - 1) - (y - 1)| = |x - y| := (by congr 1; ring); rw [hmin, habs]; ring
theorem wmPotVal_mono_above {B dNat : ℕ} {w : ℕ → ℕ} {SN x₁ x₂ y : ℝ} (hSN : 0 < SN) (hy1 : y ≤ x₁)
  (hx : x₁ ≤ x₂) : wmPotVal B dNat w SN x₁ y ≤ wmPotVal B dNat w SN x₂ y := by
  dsimp only [wmPotVal]; rw [min_eq_right hy1, min_eq_right (hy1.trans hx), abs_of_nonneg
    (sub_nonneg.2 hy1), abs_of_nonneg (sub_nonneg.2 (hy1.trans hx))]; have hdiv : (x₁ - y) / SN ≤
    (x₂ - y) / SN := div_le_div_of_nonneg_right (by linarith) hSN.le
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (psiPiecewise_mono (B := B) (dNat := dNat) (w
    := w) hdiv) hSN.le)
theorem wmPotVal_mono_below {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ i < B, w i ≤ w (i + 1)
  ∧ w (i + 1) ≤ w i + dNat) {SN x₁ x₂ y : ℝ} (hSN : 0 < SN) (hx : x₁ ≤ x₂) (h2y : x₂ ≤ y) : wmPotVal
  B dNat w SN x₁ y ≤ wmPotVal B dNat w SN x₂ y := by
  dsimp only [wmPotVal]; rw [min_eq_left (hx.trans h2y), min_eq_left h2y, abs_sub_comm x₁ y,
    abs_sub_comm x₂ y, abs_of_nonneg (sub_nonneg.2 (hx.trans h2y)), abs_of_nonneg (sub_nonneg.2
    h2y)]; set z₁ : ℝ := (y - x₂) / SN; set z₂ : ℝ := (y - x₁) / SN; have hz1_nn : 0 ≤ z₁ :=
    div_nonneg (sub_nonneg.2 h2y) hSN.le
  have hz12 : z₁ ≤ z₂ := div_le_div_of_nonneg_right (by linarith) hSN.le; have hlip :=
    psiPiecewise_sub_le hd hw hz1_nn hz12; have hmul := mul_le_mul_of_nonneg_left hlip hSN.le
  have hrhs : SN * (z₂ - z₁) = x₂ - x₁ := (by dsimp only [z₁, z₂]; field_simp [hSN.ne']; ring)
  linarith [hmul, hrhs, show SN * (psiPiecewise B dNat w z₂ - psiPiecewise B dNat w z₁) = SN *
    psiPiecewise B dNat w z₂ - SN * psiPiecewise B dNat w z₁ by ring]
theorem wmPotVal_mono_left {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ i < B, w i ≤ w (i + 1) ∧
  w (i + 1) ≤ w i + dNat) {SN x₁ x₂ y : ℝ} (hSN : 0 < SN) (hx : x₁ ≤ x₂) : wmPotVal B dNat w SN x₁ y
  ≤ wmPotVal B dNat w SN x₂ y := by
  by_cases hy1 : y ≤ x₁
  · exact wmPotVal_mono_above hSN hy1 hx
  · by_cases h2y : x₂ ≤ y
    · exact wmPotVal_mono_below hd hw hSN hx h2y
    · exact (wmPotVal_mono_below hd hw hSN (not_le.1 hy1).le le_rfl).trans (wmPotVal_mono_above hSN
        le_rfl (not_le.1 h2y).le)
theorem wmPotVal_mono {B dNat : ℕ} {w : ℕ → ℕ} (hd : 1 ≤ dNat) (hw : ∀ i < B, w i ≤ w (i + 1) ∧ w (i
  + 1) ≤ w i + dNat) {SN x₁ x₂ y₁ y₂ : ℝ} (hSN : 0 < SN) (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) : wmPotVal B
  dNat w SN x₁ y₁ ≤ wmPotVal B dNat w SN x₂ y₂ :=
  (wmPotVal_mono_left hd hw hSN hx).trans
    (by
      rw [wmPotVal_comm _ _ _ _ x₂ y₁, wmPotVal_comm _ _ _ _ x₂ y₂]
      exact wmPotVal_mono_left hd hw hSN hy)
theorem wmPotVal_hit_single_le {B dNat cNat uNat psiHi hHi : ℕ} {w : ℕ → ℕ} {SN sReset sPeer : ℝ}
  (hd : 1 ≤ dNat) (hw : ∀ i < B, w i ≤ w (i + 1) ∧ w (i + 1) ≤ w i + dNat) (hSN : 0 < SN) (huc :
  uNat ≤ cNat) (hpsi : checkPsiHi B dNat w (cNat - uNat) psiHi = true) (hh : uNat + psiHi ≤ hHi)
  (hsR : sReset ≤ ((cNat : ℝ) / 1000000000000) * SN) (hsP : sPeer ≤ ((uNat : ℝ) / 1000000000000) *
  SN) : wmPotVal B dNat w SN sReset sPeer ≤ ((hHi : ℝ) / 1000000000000) * SN := by
  set C_hi : ℝ := ((cNat : ℝ) / 1000000000000) * SN; set U_hi : ℝ := ((uNat : ℝ) / 1000000000000) *
    SN; have hUC : U_hi ≤ C_hi := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    (by exact_mod_cast huc) (by norm_num)) hSN.le; refine (wmPotVal_mono hd hw hSN hsR hsP).trans ?_
  dsimp only [wmPotVal]; rw [min_eq_right hUC, abs_of_nonneg (sub_nonneg.2 hUC)]
  have hdiff : (C_hi - U_hi) / SN = ((cNat - uNat : ℕ) : ℝ) / 1000000000000 :=
    (by dsimp only [C_hi, U_hi]; rw [Nat.cast_sub huc]; field_simp [hSN.ne'])
  rw [hdiff]; have hpsi_le := checkPsiHi_sound hd hw hpsi
  have hm := mul_le_mul_of_nonneg_left hpsi_le hSN.le; have hh_r : (uNat : ℝ) + psiHi ≤ hHi :=
    (by exact_mod_cast hh); have hh_sn := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    hh_r (by norm_num : (0 : ℝ) ≤ 1000000000000)) hSN.le; dsimp only [U_hi]; linarith [hm, hh_sn,
    show ((uNat : ℝ) / 1000000000000) * SN + SN * ((psiHi : ℝ) / 1000000000000) = (((uNat : ℝ) +
    psiHi) / 1000000000000) * SN by ring]
theorem wmPotVal_hit_both_le {B dNat cNat hBoth : ℕ} {w : ℕ → ℕ} {SN sReset : ℝ} (hd : 1 ≤ dNat) (hw
  : ∀ i < B, w i ≤ w (i + 1) ∧ w (i + 1) ≤ w i + dNat) (hSN : 0 < SN) (hh : cNat + w 0 ≤ hBoth) (hsR
  : sReset ≤ ((cNat : ℝ) / 1000000000000) * SN) : wmPotVal B dNat w SN sReset sReset ≤ ((hBoth : ℝ)
  / 1000000000000) * SN := by
  set C_hi : ℝ := ((cNat : ℝ) / 1000000000000) * SN
  refine (wmPotVal_mono hd hw hSN hsR hsR).trans ?_; rw [wmPotVal_diag hd hw SN C_hi]
  have hh_r : (cNat : ℝ) + w 0 ≤ hBoth := (by exact_mod_cast hh)
  have hh_sn := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh_r
    (by norm_num : (0 : ℝ) ≤ 1000000000000)) hSN.le; dsimp only [C_hi]; linarith [hh_sn, show ((cNat
    : ℝ) / 1000000000000) * SN + ((w 0 : ℝ) / 1000000000000) * SN = (((cNat : ℝ) + w 0) /
    1000000000000) * SN by ring]
/-- Stage-`r` (`r ≥ 2`) 2-slot piecewise-linear potential over `Fin 2`. -/
noncomputable def wmStagePot (B : ℕ) (phiFn : ℕ → ℝ) (stFn : ℕ → M2StageScalar)
    (wFn : ℕ → ℕ → ℕ) (n r : ℕ) (betas : Fin 2 → ℝ) : ℝ :=
  wmPotVal B (stFn r).dNat (wFn r) √((2 : ℝ) ^ n)
    (remStepsSlot n r (phiFn r) (betas s0) : ℝ)
    (remStepsSlot n r (phiFn r) (betas s1) : ℝ)
/-- Full `m = 2` Bellman potential: `cswapWarmR1Cost1` at `r = 1` and `wmStagePot` at `r ≥
  2`. -/
noncomputable def wmPotential (B : ℕ) (stFn : ℕ → M2StageScalar)
    (wFn : ℕ → ℕ → ℕ) (n r : ℕ) (betas : Fin 2 → ℝ) : ℝ :=
  if r ≤ 1 then
    cswapWarmR1Cost1 n betas
  else
    wmStagePot B (phiFnOfWmSt stFn) stFn wFn n r betas
/-! ## 2. Step-Count, Locked-Click, and Stage-`2` CSWAP Hit Helpers -/
theorem remStepsSlot_mono_beta {n r : ℕ} (hr1 : 1 ≤ r) (φ : ℝ) {β₁ β₂ : ℝ} (hβ : β₁ ≤ β₂) :
  remStepsSlot n r φ β₂ ≤ remStepsSlot n r φ β₁ := by
  dsimp only [remStepsSlot]; have hθ : 0 < halfAngleSet n r := Real.arcsin_pos.2 (Real.sqrt_pos.2
    (div_pos (Nat.cast_pos.2 hr1) (by positivity))); exact Nat.ceil_mono (div_le_div_of_nonneg_right
    (by linarith) (by positivity))
theorem remStepsSlot_halfAngleSet_le_of_atan200Hi_sq {n r tn phiHi c : ℕ} (hn : 100 ≤ n) (hr1 : 1 ≤
  r) (hr1024 : r ≤ 1024) (ht_lo : 500 ≤ tn) (ht_hi : tn ≤ 200000) (hat : checkAtan200Hi tn phiHi =
  true) (hc_pos : 1 ≤ c) (hsq : phiHi * phiHi ≤ 4 * r * (c - 1) * (c - 1)) : (remStepsSlot n r
  (Real.arctan ((tn : ℝ) / 100000)) (halfAngleSet n r) : ℝ) ≤ ((c : ℝ) / 1000000000000) * √((2 : ℝ)
  ^ n) := by
  obtain ⟨hSN_ge, _⟩ := pow_two_bounds_100 hn; have hSN_pos : (0 : ℝ) < √((2 : ℝ) ^ n) :=
    lt_of_lt_of_le (by positivity) hSN_ge; rcases halfAngleSet_bounds_100 hn hr1 hr1024 with ⟨hθ_lo,
    -⟩
  rcases phi_and_lockedAlpha_bounds_fuse_100 (m := 1) le_rfl (by omega) hn hr1 hr1024 ht_lo ht_hi
    with ⟨h2θ_φ, -⟩; have hphi := atan200Hi_sound hat; have hθ_pos : 0 < halfAngleSet n r :=
    lt_of_lt_of_le (by positivity) hθ_lo; set φ : ℝ := Real.arctan ((tn : ℝ) / 100000)
  have h1 : (remStepsSlot n r φ (halfAngleSet n r) : ℝ) ≤ 1 + (φ - halfAngleSet n r) / (2 *
    halfAngleSet n r) := by
    dsimp only [remStepsSlot]; have hz : 0 ≤ (φ - halfAngleSet n r) / (2 * halfAngleSet n r) :=
      div_nonneg (by linarith) (by positivity); linarith [Nat.ceil_lt_add_one hz]
  have h2 : (φ - halfAngleSet n r) / (2 * halfAngleSet n r) ≤ ((phiHi : ℝ) / 1000000000000) / (2 *
    (√(r : ℝ) / √((2 : ℝ) ^ n))) := by
    have hnum : φ - halfAngleSet n r ≤ (phiHi : ℝ) / 1000000000000 := (by linarith [hphi, hθ_pos])
    exact (div_le_div_of_nonneg_right hnum (by positivity)).trans (div_le_div_of_nonneg_left
      (by positivity) (by positivity) (by linarith [hθ_lo]))
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 hr1; have hsr_pos : (0 : ℝ) < √(r : ℝ) :=
    Real.sqrt_pos.2 hr_pos
  have h3 : ((phiHi : ℝ) / 1000000000000) / (2 * (√(r : ℝ) / √((2 : ℝ) ^ n))) ≤ (((c - 1 : ℕ) : ℝ) /
    1000000000000) * √((2 : ℝ) ^ n) := by
    have hrew : ((phiHi : ℝ) / 1000000000000) / (2 * (√(r : ℝ) / √((2 : ℝ) ^ n))) = ((phiHi : ℝ) /
      (2 * √(r : ℝ)) / 1000000000000) * √((2 : ℝ) ^ n) := (by field_simp [hsr_pos.ne', hSN_pos.ne'])
    rw [hrew]
    refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (by norm_num)) hSN_pos.le
    rw [div_le_iff₀ (by positivity)]; refine sq_le_imp_le (by positivity) (by positivity) ?_
    have hcsq : (phiHi : ℝ) * phiHi ≤ 4 * (r : ℝ) * ((c - 1 : ℕ) : ℝ) * (c - 1 : ℕ) :=
      (by exact_mod_cast hsq); rw [mul_pow, mul_pow (2 : ℝ), Real.sq_sqrt hr_pos.le]
    linarith [hcsq, show (phiHi : ℝ) ^ 2 - ((c - 1 : ℕ) : ℝ) ^ 2 * ((2 : ℝ) ^ 2 * (r : ℝ)) = (phiHi
      : ℝ) * phiHi - 4 * (r : ℝ) * ((c - 1 : ℕ) : ℝ) * (c - 1 : ℕ) by ring]
  rw [Nat.cast_sub hc_pos, Nat.cast_one] at h3; have h1_sn : (1 : ℝ) ≤ (1 / 1000000000000) * √((2 :
    ℝ) ^ n) := (by linarith [hSN_ge]); linarith [h1, h2, h3, h1_sn, show (((c : ℝ) - 1) /
    1000000000000) * √((2 : ℝ) ^ n) + (1 / 1000000000000) * √((2 : ℝ) ^ n) = ((c : ℝ) /
    1000000000000) * √((2 : ℝ) ^ n) by ring]
theorem remStepsSlot_le_of_three_add_max {n rp : ℕ} (hrp1 : 1 ≤ rp) {φp y U : ℝ} (hU_nn : 0 ≤ U) (hb
  : 3 + max 0 ((φp - y) / (2 * halfAngleSet n rp)) ≤ U) : (remStepsSlot n rp φp y : ℝ) ≤ U := by
  have hθp : 0 < halfAngleSet n rp := Real.arcsin_pos.2 (Real.sqrt_pos.2 (div_pos (Nat.cast_pos.2
    hrp1) (by positivity))); by_cases hge : φp ≤ y
  · rw [(remStepsSlot_eq_zero_iff hrp1 φp y).2 hge]; simpa using hU_nn
  · have hlt : y < φp := not_le.1 hge; dsimp only [remStepsSlot]; have hq_nn : 0 ≤ (φp - y) / (2 *
      halfAngleSet n rp) := div_nonneg (by linarith) (by positivity); have hq_le : (φp - y) / (2 *
      halfAngleSet n rp) ≤ max 0 ((φp - y) / (2 * halfAngleSet n rp)) := le_max_right _ _
    linarith [Nat.ceil_lt_add_one hq_nn]
theorem knotSlope_of_allRange {B dNat : ℕ} {w : ℕ → ℕ} (hall : allRange (checkM2KnotSlope dNat w) B
  = true) : ∀ j < B, w j ≤ w (j + 1) ∧ w (j + 1) ≤ w j + dNat := fun j hj ↦ by
  have hj_chk := of_allRange hall hj
  simp only [checkM2KnotSlope, withForcedNat_eq, Bool.and_eq_true] at hj_chk
  exact ⟨of_decide_eq_true hj_chk.1, of_decide_eq_true hj_chk.2⟩
theorem two_locked_one_sub_q0_bounds {p0 p1 p_min : ℝ} (hp_min : 0 < p_min) (hp0_lo : p_min ≤ p0)
  (hp1_lo : p_min ≤ p1) (hp0_hi : p0 ≤ 1 / (100000000 * (2 : ℝ))) (hp1_hi : p1 ≤ 1 / (100000000 * (2
  : ℝ))) :
    let q0 := (1 - p0) * (1 - p1); let p_max : ℝ := 1 / (100000000 * (2 : ℝ))
    0 < 1 - q0 ∧ 2 * p_min * (1 - 2 * p_max) ≤ 1 - q0 ∧ p0 * p1 ≤ (1 / 200000000) * (1 - q0) := by
  intro q0 p_max; have hp0_nn : 0 ≤ p0 := le_trans hp_min.le hp0_lo; have hp1_nn : 0 ≤ p1 :=
    le_trans hp_min.le hp1_lo; have hpmax_val : p_max = 1 / 200000000 :=
    (by dsimp only [p_max]; norm_num); have hident : (1 - q0) - (p0 + p1) * (1 - 2 * p_max) = p0 *
    (2 * p_max - p1) + 2 * p_max * p1 := (by dsimp only [q0]; ring)
  have hsum_rho : (p0 + p1) * (1 - 2 * p_max) ≤ 1 - q0 := by
    have hpmax_nn : 0 ≤ 2 * p_max := (by rw [hpmax_val]; positivity)
    have hp1_le_2pmax : p1 ≤ 2 * p_max := by
      have hp1_hi' : p1 ≤ 1 / 200000000 :=
        (by linarith [hp1_hi, show (1 : ℝ) / (100000000 * 2) = 1 / 200000000 by norm_num])
      rw [hpmax_val]; linarith [hp1_hi']
    have hnn : 0 ≤ p0 * (2 * p_max - p1) + 2 * p_max * p1 := add_nonneg (mul_nonneg hp0_nn
      (sub_nonneg.2 hp1_le_2pmax)) (mul_nonneg hpmax_nn hp1_nn); linarith [hident]
  have hrho_pos : 0 < 1 - 2 * p_max := (by rw [hpmax_val]; norm_num); have h2p_rho : 2 * p_min * (1
    - 2 * p_max) ≤ 1 - q0 := (mul_le_mul_of_nonneg_right (by linarith [hp0_lo, hp1_lo])
    hrho_pos.le).trans hsum_rho
  have h1q0_pos : 0 < 1 - q0 := lt_of_lt_of_le (by positivity) h2p_rho
  have hp1_le : p1 ≤ 1 - q0 := by
    have : (1 - q0) - p1 = p0 * (1 - p1) := (by dsimp only [q0]; ring); linarith [mul_nonneg hp0_nn
      (by linarith [hp1_hi, hpmax_val] : 0 ≤ 1 - p1)]
  have hprod_le : p0 * p1 ≤ (1 / 200000000) * (1 - q0) := by
    calc p0 * p1 ≤ (1 / 200000000) * p1 :=
          mul_le_mul_of_nonneg_right (by linarith [hp0_hi, hpmax_val]) hp1_nn
      _ ≤ (1 / 200000000) * (1 - q0) := mul_le_mul_of_nonneg_left hp1_le (by positivity)
  exact ⟨h1q0_pos, h2p_rho, hprod_le⟩
theorem two_locked_one_sub_q0_bounds_r2_tight {p0 p1 p_min : ℝ} (hp_min : 0 < p_min) (hp0_lo : p_min
  ≤ p0) (hp1_lo : p_min ≤ p1) (hp0_hi : p0 ≤ 1 / (2000000000000 * (2 : ℝ))) (hp1_hi : p1 ≤ 1 /
  (2000000000000 * (2 : ℝ))) :
    let q0 := (1 - p0) * (1 - p1); let p_max : ℝ := 1 / (2000000000000 * (2 : ℝ))
    0 < 1 - q0 ∧ 2 * p_min * (1 - 2 * p_max) ≤ 1 - q0 ∧ p0 * p1 ≤ (1 / 4000000000000) * (1 - q0) :=
      by
  intro q0 p_max; have hp0_nn : 0 ≤ p0 := le_trans hp_min.le hp0_lo; have hp1_nn : 0 ≤ p1 :=
    le_trans hp_min.le hp1_lo; have hp0_hi' : p0 ≤ 1 / 4000000000000 := hp0_hi.trans (by norm_num)
  have hp1_hi' : p1 ≤ 1 / 4000000000000 := hp1_hi.trans (by norm_num); have hpmax_val : p_max = 1 /
    4000000000000 := (by dsimp only [p_max]; norm_num); have hident : (1 - q0) - (p0 + p1) * (1 - 2
    * p_max) = p0 * (2 * p_max - p1) + 2 * p_max * p1 := (by dsimp only [q0]; ring)
  have hsum_rho : (p0 + p1) * (1 - 2 * p_max) ≤ 1 - q0 := by
    have hpmax_nn : 0 ≤ 2 * p_max := (by rw [hpmax_val]; positivity); have hp1_le_2pmax : p1 ≤ 2 *
      p_max := (by rw [hpmax_val]; exact hp1_hi'.trans (by norm_num))
    have hnn : 0 ≤ p0 * (2 * p_max - p1) + 2 * p_max * p1 := add_nonneg (mul_nonneg hp0_nn
      (sub_nonneg.2 hp1_le_2pmax)) (mul_nonneg hpmax_nn hp1_nn)
    exact sub_nonneg.1 (by rw [hident]; exact hnn)
  have hrho_pos : 0 < 1 - 2 * p_max := (by rw [hpmax_val]; norm_num); have h2p_rho : 2 * p_min * (1
    - 2 * p_max) ≤ 1 - q0 := (mul_le_mul_of_nonneg_right (by linarith only [hp0_lo, hp1_lo])
    hrho_pos.le).trans hsum_rho
  have h1q0_pos : 0 < 1 - q0 := lt_of_lt_of_le (by positivity) h2p_rho
  have hp1_le : p1 ≤ 1 - q0 := by
    have hq1 : (1 - q0) - p1 = p0 * (1 - p1) := by dsimp only [q0]; ring
    have h1p1 : 0 ≤ 1 - p1 := sub_nonneg.2 (hp1_hi'.trans (by norm_num))
    exact sub_nonneg.1 (by rw [hq1]; exact mul_nonneg hp0_nn h1p1)
  have hprod_le : p0 * p1 ≤ (1 / 4000000000000) * (1 - q0) := by
    calc p0 * p1 ≤ (1 / 4000000000000) * p1 := mul_le_mul_of_nonneg_right hp0_hi' hp1_nn
      _ ≤ (1 / 4000000000000) * (1 - q0) := mul_le_mul_of_nonneg_left hp1_le (by positivity)
  exact ⟨h1q0_pos, h2p_rho, hprod_le⟩
theorem lockedAlpha_m2_r2_tight_bounds_100 {n tNum : ℕ} (hn : 100 ≤ n) (ht_lo : 500 ≤ tNum) {β : ℝ}
  (hβ_lo : Real.arctan ((tNum : ℝ) / 100000) ≤ β) (hβ_hi : β ≤ 5 / 4) :
    let t : ℝ := (tNum : ℝ) / 100000; let θ₂ : ℝ := halfAngleSet n 2; let N : ℝ := (2 : ℝ) ^ n
    4 * t * (999999999998 / 1000000000000) * √(2 : ℝ) / √N ≤ 1 - lockedAlpha β θ₂ ^ 2 ∧ 1 -
      lockedAlpha β θ₂ ^ 2 ≤ 1 / (2000000000000 * (2 : ℝ)) := by
  intro t θ₂ N; obtain ⟨htan5, h54_lt⟩ := tan_five_div_four_le_five; obtain ⟨_, _, _, hcos2,
    hsin2_lo, hsin2_hi⟩ := halfAngleSet_bounds_100 hn (by omega : 1 ≤ 2) (by omega : 2 ≤ 1024)
  simp only [Nat.cast_ofNat] at hcos2 hsin2_lo hsin2_hi; obtain ⟨hSN_ge, hN_ge⟩ :=
    pow_two_bounds_100 hn; have hSN_pos : 0 < √N := lt_of_lt_of_le (by positivity) hSN_ge
  have hN_pos : 0 < N := lt_of_lt_of_le (by positivity) hN_ge; have ht_ge : (1 : ℝ) / 200 ≤ t :=
    (by dsimp only [t]; have : (500 : ℝ) ≤ tNum := (by exact_mod_cast ht_lo); linarith)
  have hφ_pos : 0 < Real.arctan t := Real.arctan_pos.2 (lt_of_lt_of_le (by norm_num) ht_ge)
  have hβ_nn : 0 ≤ β := le_trans hφ_pos.le hβ_lo
  have hβ_lt : β < π / 2 := lt_of_le_of_lt hβ_hi h54_lt; have hcβ : 0 < Real.cos β :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ_lt⟩; have htan_lo : t ≤ Real.tan β :=
    (by rw [← Real.tan_arctan t]; exact PipeFuse.tan_mono_nonneg hφ_pos.le hβ_lo hβ_lt)
  have htan_hi : Real.tan β ≤ 5 := (PipeFuse.tan_mono_nonneg hβ_nn hβ_hi h54_lt).trans htan5
  have hs2_le2 : √(2 : ℝ) ≤ 2 := sq_le_imp_le (Real.sqrt_nonneg _) (by norm_num)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
  set u : ℝ := Real.tan β * Real.sin (2 * θ₂) - 2 * 2 / N
  have hu_lo : (9999999999986 / 10000000000000) * (2 * t * √(2 : ℝ) / √N) ≤ u := by
    have hts : t * ((999999999999 / 1000000000000) * (2 * √(2 : ℝ) / √N)) ≤ Real.tan β * Real.sin (2
      * θ₂) := mul_le_mul htan_lo hsin2_lo (by positivity) (by linarith)
    have h4N : 2 * (2 : ℝ) / N ≤ (4 / 10000000000000) * (2 * t * √(2 : ℝ) / √N) := by
      have hfac : √(2 : ℝ) / √N ≤ 2 / 1000000000000000 := (div_le_div_of_nonneg_right hs2_le2
        hSN_pos.le).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hSN_ge)
      have hft : √(2 : ℝ) / √N ≤ (4 / 10000000000000) * t := (by linarith [hfac, ht_ge])
      have hsq_eq : 2 * (2 : ℝ) / N = (√(2 : ℝ) / √N) * (2 * √(2 : ℝ) / √N) := by
        rw [div_mul_div_comm, Real.mul_self_sqrt hN_pos.le]; have hs2 : √(2 : ℝ) * (2 * √(2 : ℝ)) =
          2 * (√(2 : ℝ) * √(2 : ℝ)) := (by ring); rw [hs2, Real.mul_self_sqrt (by norm_num)]
      calc 2 * (2 : ℝ) / N = (√(2 : ℝ) / √N) * (2 * √(2 : ℝ) / √N) := hsq_eq
        _ ≤ ((4 / 10000000000000) * t) * (2 * √(2 : ℝ) / √N) :=
            mul_le_mul_of_nonneg_right hft (by positivity)
        _ = (4 / 10000000000000) * (2 * t * √(2 : ℝ) / √N) := by ring
    have hts_eq : t * ((999999999999 / 1000000000000) * (2 * √(2 : ℝ) / √N)) = (999999999999 /
      1000000000000) * (2 * t * √(2 : ℝ) / √N) := (by ring); rw [hts_eq] at hts
    have hpos_x : 0 ≤ 2 * t * √(2 : ℝ) / √N := (by positivity); have hsub : (9999999999986 /
      10000000000000) * (2 * t * √(2 : ℝ) / √N) ≤ (999999999999 / 1000000000000 - 4 /
      10000000000000) * (2 * t * √(2 : ℝ) / √N) := mul_le_mul_of_nonneg_right (by norm_num) hpos_x
    have hsub' : (999999999999 / 1000000000000 - 4 / 10000000000000) * (2 * t * √(2 : ℝ) / √N) =
      (999999999999 / 1000000000000) * (2 * t * √(2 : ℝ) / √N) - (4 / 10000000000000) * (2 * t * √(2
      : ℝ) / √N) := (by ring); dsimp only [u]; linarith only [hts, h4N, hsub, hsub']
  have hu_pos : 0 < u := lt_of_lt_of_le (by positivity) hu_lo
  have hu_hi : u ≤ 1 / 10000000000000 := by
    have hs2_small : Real.sin (2 * θ₂) ≤ 4 / 1000000000000000 := hsin2_hi.trans
      ((div_le_div_of_nonneg_right (by linarith only [hs2_le2]) hSN_pos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hSN_ge)); dsimp only [u]
    have h1 : Real.tan β * Real.sin (2 * θ₂) ≤ 1 / 50000000000000 := (mul_le_mul htan_hi hs2_small
      (le_trans (by positivity) hsin2_lo) (by positivity)).trans (by norm_num); have h2 : 0 ≤ 2 * (2
      : ℝ) / N := (by positivity); linarith only [h1, h2]
  have hlock_eq : lockedAlpha β θ₂ = 1 / (1 + u) := by
    dsimp only [lockedAlpha, u]; rw [Real.cos_sub, Real.tan_eq_sin_div_cos, hcos2]
    have h1u : 0 < 1 + (Real.sin β / Real.cos β * Real.sin (2 * θ₂) - 2 * 2 / N) :=
      (by rw [← Real.tan_eq_sin_div_cos]; change 0 < 1 + u; linarith only [hu_pos])
    have hden_c : Real.cos β * (1 - 2 * 2 / N) + Real.sin β * Real.sin (2 * θ₂) = Real.cos β * (1 +
      (Real.sin β / Real.cos β * Real.sin (2 * θ₂) - 2 * 2 / N)) :=
      (by field_simp [hcβ.ne', hN_pos.ne']; ring); rw [hden_c]; field_simp [hcβ.ne', h1u.ne']
  have hclick_eq : 1 - lockedAlpha β θ₂ ^ 2 = (2 * u + u ^ 2) / (1 + u) ^ 2 :=
    (by rw [hlock_eq]; field_simp [(by linarith only [hu_pos] : (0 : ℝ) < 1 + u).ne']; ring)
  rw [hclick_eq]; constructor
  · have h1 : 2 * u * (9999999999997 / 10000000000000) ≤ (2 * u + u ^ 2) / (1 + u) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; have hu2 : u ^ 2 ≤ (1 / 10000000000000) * u :=
        (by rw [sq]; exact mul_le_mul_of_nonneg_right hu_hi hu_pos.le); have hu1 : u ≤ 1 :=
        hu_hi.trans (by norm_num)
      have hu2_s : u ^ 2 ≤ 1 / 10000000000000 := by
        calc u ^ 2 = u * u := sq u
          _ ≤ (1 / 10000000000000) * 1 := mul_le_mul hu_hi hu1 hu_pos.le (by positivity)
          _ = 1 / 10000000000000 := mul_one _
      have hu3 : u ^ 2 * u ≤ (1 / 10000000000000) * u := mul_le_mul_of_nonneg_right hu2_s hu_pos.le
      have hexp : 2 * u * (9999999999997 / 10000000000000) * (1 + u) ^ 2 = (9999999999997 /
        5000000000000) * u + (9999999999997 / 2500000000000) * u ^ 2 + (9999999999997 /
        5000000000000) * (u ^ 2 * u) := (by ring); linarith only [hexp, hu2, hu3, hu_pos]
    have hm := mul_le_mul_of_nonneg_right hu_lo
      (by norm_num : (0 : ℝ) ≤ 2 * (9999999999997 / 10000000000000)); have hfac : 4 * (999999999998
      / 1000000000000 : ℝ) ≤ 2 * (9999999999986 / 10000000000000) * 2 * (9999999999997 /
      10000000000000) := (by norm_num); have hpos_ts : 0 ≤ t * √(2 : ℝ) / √N := (by positivity)
    have h2 : 4 * t * (999999999998 / 1000000000000) * √(2 : ℝ) / √N ≤ 2 * u * (9999999999997 /
      10000000000000) := by
      calc 4 * t * (999999999998 / 1000000000000) * √(2 : ℝ) / √N
          = (4 * (999999999998 / 1000000000000)) * (t * √(2 : ℝ) / √N) := by ring
        _ ≤ (2 * (9999999999986 / 10000000000000) * 2 * (9999999999997 / 10000000000000)) *
              (t * √(2 : ℝ) / √N) := mul_le_mul_of_nonneg_right hfac hpos_ts
        _ = (9999999999986 / 10000000000000) * (2 * t * √(2 : ℝ) / √N) *
              (2 * (9999999999997 / 10000000000000)) := by ring
        _ ≤ u * (2 * (9999999999997 / 10000000000000)) := hm
        _ = 2 * u * (9999999999997 / 10000000000000) := by ring
    exact h2.trans h1
  · have h1 : (2 * u + u ^ 2) / (1 + u) ^ 2 ≤ 2 * u := by
      rw [div_le_iff₀ (by positivity)]; have hpos3 : 0 ≤ u ^ 3 := pow_nonneg hu_pos.le 3
      have hexp : 2 * u * (1 + u) ^ 2 - (2 * u + u ^ 2) = 3 * u ^ 2 + 2 * u ^ 3 := (by ring)
      linarith only [sq_nonneg u, hpos3, hexp]
    have h2 : 2 * u ≤ 1 / (2000000000000 * (2 : ℝ)) := (mul_le_mul_of_nonneg_left hu_hi
      (by norm_num)).trans (by norm_num); exact h1.trans h2
theorem clickRowM2R2Tight_sound {n tn stepNum : ℕ} (ht : 500 ≤ tn) (hchk : checkClickRowM2R2Tight tn
  stepNum = true) : 1 / (2 * (4 * ((tn : ℝ) / 100000) * (999999999998 / 1000000000000) * √(2 : ℝ) /
  √((2 : ℝ) ^ n)) * (1 - 2 * (1 / (2000000000000 * (2 : ℝ))))) ≤ ((stepNum : ℝ) / 1000000000000) *
  √((2 : ℝ) ^ n) := by
  set p_min : ℝ := 4 * ((tn : ℝ) / 100000) * (999999999998 / 1000000000000) * √(2 : ℝ) / √((2 : ℝ) ^
    n); set p_max : ℝ := 1 / (2000000000000 * (2 : ℝ)); have hsq_nat := of_decide_eq_true hchk
  have hsr_pos : (0 : ℝ) < √(2 : ℝ) := Real.sqrt_pos.2 (by positivity)
  have ht_pos : (0 : ℝ) < tn := Nat.cast_pos.2 (lt_of_lt_of_le (by omega : 0 < 500) ht)
  have hSN_pos : (0 : ℝ) < √((2 : ℝ) ^ n) := Real.sqrt_pos.2 (by positivity); have hrho : 1 - 2 *
    p_max = 1999999999999 / 2000000000000 := (by dsimp only [p_max]; norm_num)
  have hden_ge : ((4 * 2 * 999999999997 * (tn : ℝ)) / (100000 * 1000000000000)) * (√(2 : ℝ) / √((2 :
    ℝ) ^ n)) ≤ 2 * p_min * (1 - 2 * p_max) := by
    rw [hrho]; dsimp only [p_min]; have h97 : (999999999997 / 1000000000000 : ℝ) ≤ (999999999998 /
      1000000000000) * (1999999999999 / 2000000000000) := (by norm_num); have hfac_nn : 0 ≤ 4 * 2 *
      ((tn : ℝ) / 100000) * (√(2 : ℝ) / √((2 : ℝ) ^ n)) := (by positivity); have hm_le :=
      mul_le_mul_of_nonneg_left h97 hfac_nn; have heq1 : 4 * 2 * ((tn : ℝ) / 100000) * (√(2 : ℝ) /
      √((2 : ℝ) ^ n)) * (999999999997 / 1000000000000) = ((4 * 2 * 999999999997 * (tn : ℝ)) /
      (100000 * 1000000000000)) * (√(2 : ℝ) / √((2 : ℝ) ^ n)) := (by ring); have heq2 : 4 * 2 * ((tn
      : ℝ) / 100000) * (√(2 : ℝ) / √((2 : ℝ) ^ n)) * ((999999999998 / 1000000000000) *
      (1999999999999 / 2000000000000)) = 2 * (4 * ((tn : ℝ) / 100000) * (999999999998 /
      1000000000000) * √(2 : ℝ) / √((2 : ℝ) ^ n)) * (1999999999999 / 2000000000000) := (by ring)
    rw [← heq1, ← heq2]; exact hm_le
  have hlhs_le : 1 / (2 * p_min * (1 - 2 * p_max)) ≤ ((100000 * 1000000000000 : ℝ) / (4 * 2 *
    999999999997 * (tn : ℝ) * √(2 : ℝ))) * √((2 : ℝ) ^ n) := by
    have h1 := one_div_le_one_div_of_le (by positivity) hden_ge; refine h1.trans (le_of_eq ?_)
    field_simp [ht_pos.ne', hsr_pos.ne', hSN_pos.ne']
  refine hlhs_le.trans (mul_le_mul_of_nonneg_right ?_ hSN_pos.le); rw [div_le_div_iff₀
    (by positivity) (by norm_num)]; refine sq_le_imp_le (by positivity) (by positivity) ?_
  have hcast : ((1000000000000 * 100000 * 1000000000000 : ℝ)) * (1000000000000 * 100000 *
    1000000000000) ≤ 2 * (4 * 2 * 999999999997 * (tn : ℝ) * stepNum) * (4 * 2 * 999999999997 * (tn :
    ℝ) * stepNum) := (by exact_mod_cast hsq_nat); have hlhs_sq : ((100000 * 1000000000000 : ℝ) *
    1000000000000) ^ 2 = ((1000000000000 * 100000 * 1000000000000 : ℝ)) * (1000000000000 * 100000 *
    1000000000000) := (by ring)
  have hr_sq : ((stepNum : ℝ) * (4 * 2 * 999999999997 * (tn : ℝ) * √(2 : ℝ))) ^ 2 = 2 * (4 * 2 *
    999999999997 * (tn : ℝ) * stepNum) * (4 * 2 * 999999999997 * (tn : ℝ) * stepNum) := by
    calc ((stepNum : ℝ) * (4 * 2 * 999999999997 * (tn : ℝ) * √(2 : ℝ))) ^ 2
        = (√(2 : ℝ)) ^ 2 * (4 * 2 * 999999999997 * (tn : ℝ) * stepNum) *
            (4 * 2 * 999999999997 * (tn : ℝ) * stepNum) := by ring
      _ = 2 * (4 * 2 * 999999999997 * (tn : ℝ) * stepNum) *
            (4 * 2 * 999999999997 * (tn : ℝ) * stepNum) := by rw [Real.sq_sqrt (by norm_num)]
  rw [hlhs_sq, hr_sq]; exact hcast
theorem cswapR1CostUpper_le_of_zeroHit {n hHi : ℕ} {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ_hi : γ ≤ 4 / 5) (hh :
  cswapZeroHitNat ≤ hHi) : cswapR1CostUpper n γ ≤ ((hHi : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) := by
  refine (cswapR1CostUpper_anti n le_rfl hγ0 hγ_hi).trans ?_; change cswapCoeffUpper 0 * √((2 : ℝ) ^
    n) ≤ _; refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine cswapZeroHit_sound.trans ?_
  exact div_le_div_of_nonneg_right (by exact_mod_cast hh) (by norm_num)
theorem cswapR1CostUpper_fuseNextAngle_le_of_sound {n tc hHi : ℕ} {x : ℝ} (hn : 100 ≤ n) (htc1 : 1 ≤
  tc) (hx_lo : Real.arctan ((tc : ℝ) / 100000) ≤ x) (hx_hi : x ≤ 5 / 4) (hsnd : 0 ≤ Real.arcsin
  (√((1 : ℝ) / 2) * Real.sin (Real.arctan ((tc : ℝ) / 100000))) ∧ cswapCoeffUpper (Real.arcsin (√((1
  : ℝ) / 2) * Real.sin (Real.arctan ((tc : ℝ) / 100000)))) ≤ (hHi : ℝ) / 1000000000000) :
  cswapR1CostUpper n (fuseNextAngle n 2 x) ≤ ((hHi : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) := by
  have h2r : 2 * 2 ≤ 2 ^ n := two_mul_le_pow_100 hn (by omega); have h54_lt : (5 / 4 : ℝ) < π / 2 :=
    tan_five_div_four_le_five.2
  rcases halfAngleSet_bounds_100 hn (by omega : 1 ≤ 2) (by omega : 2 ≤ 1024) with ⟨_, _, hθ2_13, -⟩
  have hatan_tc_ge_θ : halfAngleSet n 2 ≤ Real.arctan ((tc : ℝ) / 100000) := by
    have h1 : (1 : ℝ) / 100000 ≤ (tc : ℝ) / 100000 :=
      (by have : (1 : ℝ) ≤ tc := (by exact_mod_cast htc1); linarith); have hp : (1 : ℝ) /
      10000000000000 ≤ Real.arctan ((1 : ℝ) / 100000) := le_trans (by norm_num) (pade56_le_arctan
      (by norm_num : (0 : ℝ) ≤ 1 / 100000)); linarith [hθ2_13, hp, Real.arctan_mono h1]
  obtain ⟨hγ_nn, hc_le⟩ := hsnd; set γ₀ : ℝ := Real.arcsin (√((1 : ℝ) / 2) * Real.sin (Real.arctan
    ((tc : ℝ) / 100000)))
  have hγ_le_fx : γ₀ ≤ fuseNextAngle n 2 x := by
    have h12 : √(((2 - 1 : ℕ) : ℝ) / (2 : ℕ)) = √((1 : ℝ) / 2) := (by norm_num)
    have harc := arcsin_sqrt_nat_sub_ratio_le_fuseNextAngle (n := n) (r := 2) (by omega) h2r
      hatan_tc_ge_θ (Real.arctan_lt_pi_div_two _); rw [h12] at harc
    exact harc.trans (fuseNextAngle_mono (by omega) h2r hatan_tc_ge_θ hx_lo (hx_hi.trans h54_lt.le))
  have hfx_hi : fuseNextAngle n 2 x ≤ 4 / 5 := (fuseNextAngle_mono (by omega) h2r
    (hatan_tc_ge_θ.trans hx_lo) hx_hi h54_lt.le).trans
    (fuseNextAngle_two_five_div_four_le_four_div_five hn); refine (cswapR1CostUpper_anti n hγ_nn
    hγ_le_fx hfx_hi).trans ?_; change cswapCoeffUpper γ₀ * √((2 : ℝ) ^ n) ≤ _
  exact mul_le_mul_of_nonneg_right hc_le (Real.sqrt_nonneg _)
theorem cswapR1CostUpper_fuseNextAngle_le {n tc tSymLo8 symAtanLo hHi : ℕ} {x : ℝ} (hn : 100 ≤ n)
  (htc1 : 1 ≤ tc) (hx_lo : Real.arctan ((tc : ℝ) / 100000) ≤ x) (hx_hi : x ≤ 5 / 4) (hchk :
  checkCswapHitSingle tc tSymLo8 symAtanLo hHi = true) : cswapR1CostUpper n (fuseNextAngle n 2 x) ≤
  ((hHi : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) :=
  cswapR1CostUpper_fuseNextAngle_le_of_sound hn htc1 hx_lo hx_hi (cswapHitSingle_sound hchk)
theorem cswapR1CostUpper_fuseNextAngle_lock_le {n tc tSym symAtanLo hHi : ℕ} {x : ℝ} (hn : 100 ≤ n)
  (htc1 : 1 ≤ tc) (hx_lo : Real.arctan ((tc : ℝ) / 100000) ≤ x) (hx_hi : x ≤ 5 / 4) (hchk :
  checkCswapHitLock tc tSym symAtanLo hHi = true) : cswapR1CostUpper n (fuseNextAngle n 2 x) ≤ ((hHi
  : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) :=
  cswapR1CostUpper_fuseNextAngle_le_of_sound hn htc1 hx_lo hx_hi (cswapHitLock_sound hchk)
/-! ## 3. Stage-`2` (`r = 2 → r = 1` CSWAP Warm Readout) Step Soundness -/
theorem warm2_stage2_single_locked_step {B n tn phiLo cSelf dNat : ℕ} {w : ℕ → ℕ} {binR : ℕ →
  M2BinCert} (hB : 1 ≤ B) (hn : 100 ≤ n) (ht_lo : 500 ≤ tn) (ht_hi : tn ≤ 200000) (hphiLo_chk :
  checkAtan200Lo tn phiLo = true) (hd1000 : 1000 ≤ dNat) (hcB : cSelf ≤ B * dNat) (hw : ∀ i < B, w i
  ≤ w (i + 1) ∧ w (i + 1) ≤ w i + dNat) (hbins : allRange (fun j ↦ checkWarm2Stage2Bin B tn phiLo
  dNat w (binR j) j) B = true) {p βRamp : ℝ} (hp_lo : 4 * ((tn : ℝ) / 100000) * (99999999 /
  100000000) * √(2 : ℝ) / √((2 : ℝ) ^ n) ≤ p) (hβ_lo : halfAngleSet n 2 ≤ βRamp) (hβ_lt : βRamp <
  Real.arctan ((tn : ℝ) / 100000)) (hd_cap : (remStepsSlot n 2 (Real.arctan ((tn : ℝ) / 100000))
  βRamp : ℝ) ≤ ((cSelf : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)) :
    let SN := √((2 : ℝ) ^ n); let φ := Real.arctan ((tn : ℝ) / 100000)
    let d := remStepsSlot n 2 φ βRamp
    1 + (1 - p) * wmPotVal B dNat w SN 0 ((d - 1 : ℕ) : ℝ) + p * cswapR1CostUpper n (fuseNextAngle n
      2 (βRamp + 2 * halfAngleSet n 2)) ≤ wmPotVal B dNat w SN 0 (d : ℝ) := by
  intro SN φ d; obtain ⟨hSN_ge, hN_ge⟩ := pow_two_bounds_100 hn; have hSN_pos : 0 < SN :=
    lt_of_lt_of_le (by positivity) hSN_ge
  have hN_pos : (0 : ℝ) < (2 : ℝ) ^ n := lt_of_lt_of_le (by positivity) hN_ge
  have h2r : 2 * 2 ≤ 2 ^ n := two_mul_le_pow_100 hn (by omega)
  have hd1 : 1 ≤ d := by
    by_contra h0
    have hez : d = 0 := (by omega); linarith [(remStepsSlot_eq_zero_iff (n := n) (r := 2) (by omega)
      φ βRamp).1 hez]
  have hd_ge1 : 1 ≤ dNat := (by omega)
  have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd_ge1; set δ : ℝ := (dNat : ℝ) / 1000000000000
  have hδ_pos : 0 < δ := (by positivity); set x' : ℝ := ((d - 1 : ℕ) : ℝ) / SN
  have hx'0 : 0 ≤ x' := (by positivity)
  have hx'B : x' ≤ (B : ℝ) * δ := by
    have h1 : ((d - 1 : ℕ) : ℝ) ≤ d := (by exact_mod_cast Nat.sub_le d 1); have h2 : (d : ℝ) / SN ≤
      (cSelf : ℝ) / 1000000000000 := (div_le_iff₀ hSN_pos).2 hd_cap
    have h3 : (cSelf : ℝ) / 1000000000000 ≤ (B : ℝ) * δ := by
      dsimp only [δ]; have hcB_r : (cSelf : ℝ) ≤ (B : ℝ) * dNat := (by exact_mod_cast hcB); linarith
    exact (div_le_div_of_nonneg_right h1 hSN_pos.le).trans (h2.trans h3)
  obtain ⟨j, hj, hx'_lo, hx'_hi⟩ := exists_bin_of_le hB hδ_pos hx'0 hx'B
  have h_invSN_le_δ : 1 / SN ≤ δ := by
    have h1 : 1 / SN ≤ 1 / 1000000000000000 := one_div_le_one_div_of_le (by positivity) hSN_ge
    have h2 : (1000 : ℝ) ≤ dNat := (by exact_mod_cast hd1000); dsimp only [δ]; linarith
  have hd_split : (d : ℝ) / SN = x' + 1 / SN :=
    (by dsimp only [x']; rw [Nat.cast_sub hd1, Nat.cast_one]; field_simp [hSN_pos.ne']; ring)
  rw [wmPotVal_zero_left B dNat w SN (by positivity : (0 : ℝ) ≤ (d - 1 : ℕ)), wmPotVal_zero_left B
    dNat w SN (by positivity : (0 : ℝ) ≤ d), hd_split]; have hstep_psi :=
    psiPiecewise_step_ge_minDiff hd_ge1 hw hj hx'_lo hx'_hi (by positivity) h_invSN_le_δ
  have hstep_sn : (minDiffNat B w j : ℝ) / dNat ≤ SN * psiPiecewise B dNat w (x' + 1 / SN) - SN *
    psiPiecewise B dNat w x' := by
    have hm := mul_le_mul_of_nonneg_left hstep_psi hSN_pos.le; have hl : SN * (((minDiffNat B w j :
      ℝ) / dNat) * (1 / SN)) = (minDiffNat B w j : ℝ) / dNat := (by field_simp [hSN_pos.ne'])
    linarith [hm, hl, show SN * (psiPiecewise B dNat w (x' + 1 / SN) - psiPiecewise B dNat w x') =
      SN * psiPiecewise B dNat w (x' + 1 / SN) - SN * psiPiecewise B dNat w x' by ring]
  have hpost_ge : ((w j : ℝ) / 1000000000000) * SN ≤ SN * psiPiecewise B dNat w x' := by
    have hm := psiPiecewise_mono (B := B) (dNat := dNat) (w := w) hx'_lo; dsimp only [δ] at hm
    rw [psiPiecewise_knot hd_ge1 hw hj.le] at hm; linarith [mul_le_mul_of_nonneg_left hm hSN_pos.le]
  have hbin_chk := of_allRange hbins hj; rcases hbc : binR j with ⟨tcLo, bLoHi, dropHi, tSymLo8,
    symAtanLo, u1, u2, u3, hHi⟩; rw [hbc] at hbin_chk; simp only [checkWarm2Stage2Bin,
    withForcedNat_eq, Bool.and_eq_true] at hbin_chk; rcases hbin_chk with ⟨hbr_tc, hhw_d, hsq_d⟩
  have hhw : hHi ≤ w j := of_decide_eq_true hhw_d; have hsq_nat := of_decide_eq_true hsq_d
  rcases halfAngleSet_bounds_100 hn (by omega : 1 ≤ 2) (by omega : 2 ≤ 1024) with ⟨hθc_lo, hθc_hi,
    -⟩
  rcases phi_and_lockedAlpha_bounds_fuse_100 (m := 1) le_rfl (by omega) hn (by omega : 1 ≤ 2)
    (by omega : 2 ≤ 1024) ht_lo ht_hi with ⟨_, hφ2θ, h54_lt, -⟩
  have hθc_pos : 0 < halfAngleSet n 2 := lt_of_lt_of_le (by positivity) hθc_lo
  set β' : ℝ := βRamp + 2 * halfAngleSet n 2; have hβ'_θ : halfAngleSet n 2 ≤ β' :=
    (by dsimp only [β']; linarith); have hβ'_54 : β' ≤ 5 / 4 :=
    (by dsimp only [β']; linarith [hβ_lt, hφ2θ])
  have hhit_le : cswapR1CostUpper n (fuseNextAngle n 2 β') ≤ ((hHi : ℝ) / 1000000000000) * SN := by
    by_cases htc0 : tcLo = 0
    · subst htc0; simp only [beq_self_eq_true, ↓reduceIte] at hbr_tc
      have hθ1_nn : 0 ≤ halfAngleSet n 1 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
      have hfg_lo : 0 ≤ fuseNextAngle n 2 β' := hθ1_nn.trans (halfAngleSet_le_fuseNextAngle
        (by omega) h2r hβ'_θ (hβ'_54.trans h54_lt.le))
      have hfg_hi : fuseNextAngle n 2 β' ≤ 4 / 5 := (fuseNextAngle_mono (by omega) h2r hβ'_θ hβ'_54
        h54_lt.le).trans (fuseNextAngle_two_five_div_four_le_four_div_five hn)
      exact cswapR1CostUpper_le_of_zeroHit hfg_lo hfg_hi (of_decide_eq_true hbr_tc)
    · have htc0_b : (tcLo == 0) = false := beq_false_of_ne htc0; rw [htc0_b] at hbr_tc
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, and_assoc] at hbr_tc
      rcases hbr_tc with ⟨htc1_d, _, hat_tc, hdrop_sq_d, hbdrop_d, hcswap_tc⟩
      have htc1 : 1 ≤ tcLo := of_decide_eq_true htc1_d
      have hdrop_sq := of_decide_eq_true hdrop_sq_d; have hbdrop := of_decide_eq_true hbdrop_d
      have hceil_le : φ - βRamp ≤ (d : ℝ) * (2 * halfAngleSet n 2) :=
        (by dsimp only [d, remStepsSlot]; exact (div_le_iff₀ (by positivity)).1 (Nat.le_ceil _))
      have hφ_sub_β' : φ - β' ≤ 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n 2 :=
        (by dsimp only [β']; rw [Nat.cast_sub hd1, Nat.cast_one]; linarith); have hd1_le : ((d - 1 :
        ℕ) : ℝ) ≤ (((j + 1 : ℕ) : ℝ) * δ) * SN := (div_le_iff₀ hSN_pos).1 hx'_hi
      have hrN : (2 : ℝ) / (2 : ℝ) ^ n ≤ 1 / 1000000000000 := by
        have h1 : (2 : ℝ) / (2 : ℝ) ^ n ≤ 1024 / (1000000000000000 * 1000000000000000) :=
          (div_le_div_of_nonneg_right (by norm_num) hN_pos.le).trans (div_le_div_of_nonneg_left
          (by positivity) (by positivity) hN_ge); linarith
      have hfac_up : 1 + (2 : ℕ) / (2 : ℝ) ^ n ≤ 1000000000001 / 1000000000000 := by
        push_cast at *
        linarith [hrN]
      have hθc_up : halfAngleSet n 2 ≤ (√(2 : ℝ) / SN) * (1000000000001 / 1000000000000) :=
        hθc_hi.trans (mul_le_mul_of_nonneg_left hfac_up (by positivity))
      have hdrop_prod : 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n 2 ≤ (2 * √(2 : ℝ) * (((j + 1) * dNat
        * 1000000000001 : ℕ) : ℝ)) / (1000000000000 * 1000000000000) := by
        have hm := mul_le_mul (mul_le_mul_of_nonneg_left hd1_le (by norm_num : (0 : ℝ) ≤ 2)) hθc_up
          hθc_pos.le (by positivity); have heq : (2 * ((((j + 1 : ℕ) : ℝ) * δ) * SN)) * ((√(2 : ℝ) /
          SN) * (1000000000001 / 1000000000000)) = (2 * √(2 : ℝ) * (((j + 1) * dNat * 1000000000001
          : ℕ) : ℝ)) / (1000000000000 * 1000000000000) :=
          (by dsimp only [δ]; push_cast; field_simp [hSN_pos.ne']); linarith [hm, heq]
      have hdrop_le : 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n 2 ≤ (dropHi : ℝ) / 1000000000000 := by
        refine hdrop_prod.trans ?_
        have hroot_le : 2 * √(2 : ℝ) * (((j + 1) * dNat * 1000000000001 : ℕ) : ℝ) ≤ (dropHi : ℝ) *
          1000000000000 := by
          refine sq_le_imp_le (by positivity) (by positivity) ?_; set dr : ℕ := (j + 1) * dNat *
            1000000000001; have hcast : 4 * 2 * (dr : ℝ) * dr ≤ ((dropHi : ℝ) * 1000000000000) *
            ((dropHi : ℝ) * 1000000000000) := (by exact_mod_cast hdrop_sq)
          have hlhs_sq : (2 * √(2 : ℝ) * (dr : ℝ)) ^ 2 = 4 * 2 * (dr : ℝ) * dr := by
            calc (2 * √(2 : ℝ) * (dr : ℝ)) ^ 2 = 4 * (√(2 : ℝ)) ^ 2 * (dr : ℝ) * dr := by ring
              _ = 4 * 2 * (dr : ℝ) * dr := by rw [Real.sq_sqrt (by norm_num)]
          linarith [hcast, hlhs_sq, show ((dropHi : ℝ) * 1000000000000) ^ 2 = ((dropHi : ℝ) *
            1000000000000) * ((dropHi : ℝ) * 1000000000000) by ring]
        have hrhs : (dropHi : ℝ) / 1000000000000 = ((dropHi : ℝ) * 1000000000000) / (1000000000000 *
          1000000000000) := (by ring); rw [hrhs]
        exact div_le_div_of_nonneg_right hroot_le (by norm_num)
      have hphiLo_le := atan200Lo_sound hphiLo_chk; have hbLo_ge := atan200Hi_sound hat_tc
      have hbdrop_r : (bLoHi : ℝ) + dropHi ≤ phiLo := (by exact_mod_cast hbdrop)
      have hatan_tc_le_β' : Real.arctan ((tcLo : ℝ) / 100000) ≤ β' := by
        have hbd_div : (bLoHi : ℝ) / 1000000000000 + (dropHi : ℝ) / 1000000000000 ≤ (phiLo : ℝ) /
          1000000000000 := (by linarith [hbdrop_r]); linarith [hbLo_ge, hphiLo_le, hφ_sub_β',
          hdrop_le, hbd_div]
      exact cswapR1CostUpper_fuseNextAngle_le hn htc1 hatan_tc_le_β' hβ'_54 hcswap_tc
  have hp_nn : 0 ≤ p := le_trans (by positivity) hp_lo
  have hdiff_ge : (((w j - hHi : ℕ) : ℝ) / 1000000000000) * SN ≤ SN * psiPiecewise B dNat w x' -
    cswapR1CostUpper n (fuseNextAngle n 2 β') := by
    rw [Nat.cast_sub hhw]; linarith [hpost_ge, hhit_le, show ((w j : ℝ) / 1000000000000) * SN -
      ((hHi : ℝ) / 1000000000000) * SN = (((w j : ℝ) - hHi) / 1000000000000) * SN by ring]
  have hp_diff : (√(2 : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 *
    100000000 * 1000000000000) ≤ p * (SN * psiPiecewise B dNat w x' - cswapR1CostUpper n
    (fuseNextAngle n 2 β')) := by
    have hm := mul_le_mul hp_lo hdiff_ge (by positivity) hp_nn; have heq : (4 * ((tn : ℝ) / 100000)
      * (99999999 / 100000000) * √(2 : ℝ) / SN) * ((((w j - hHi : ℕ) : ℝ) / 1000000000000) * SN) =
      (√(2 : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 * 100000000 *
      1000000000000) := (by field_simp [hSN_pos.ne']); linarith
  have hmd_le_d : minDiffNat B w j ≤ dNat := by
    have hsub : w (j + 1) - w j ≤ dNat := (by have := (hw j hj).2; omega); dsimp only [minDiffNat]
    rw [withForcedNat_eq]; split_ifs
    · exact hsub
    · exact (Nat.min_le_left _ _).trans hsub
  have hbin_div : 1 - (minDiffNat B w j : ℝ) / dNat ≤ (√(2 : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j -
    hHi : ℕ) : ℝ))) / (100000 * 100000000 * 1000000000000) := by
    set lhsN : ℕ := (dNat - minDiffNat B w j) * 100000 * 100000000 * 1000000000000; set rhsN : ℕ :=
      dNat * 4 * tn * 99999999 * (w j - hHi)
    have hlin : (lhsN : ℝ) ≤ √(2 : ℝ) * (rhsN : ℝ) := by
      refine sq_le_imp_le (by positivity) (by positivity) ?_; have hcast : (lhsN : ℝ) * lhsN ≤ 2 *
        (rhsN : ℝ) * rhsN := (by exact_mod_cast hsq_nat)
      have hrsq : (√(2 : ℝ) * (rhsN : ℝ)) ^ 2 = 2 * (rhsN : ℝ) * rhsN := by
        calc (√(2 : ℝ) * (rhsN : ℝ)) ^ 2 = (√(2 : ℝ)) ^ 2 * (rhsN : ℝ) * rhsN := by ring
          _ = 2 * (rhsN : ℝ) * rhsN := by rw [Real.sq_sqrt (by norm_num)]
      linarith [hcast, hrsq, show (lhsN : ℝ) ^ 2 = (lhsN : ℝ) * lhsN by ring]
    have hlhs : 1 - (minDiffNat B w j : ℝ) / dNat = (lhsN : ℝ) / ((dNat : ℝ) * (100000 * 100000000 *
      1000000000000)) := by
      dsimp only [lhsN]; rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hmd_le_d]
      field_simp [hd_pos.ne']; ring
    have hrhs : (√(2 : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 * 100000000
      * 1000000000000) = (√(2 : ℝ) * (rhsN : ℝ)) / ((dNat : ℝ) * (100000 * 100000000 *
      1000000000000)) := (by dsimp only [rhsN]; push_cast; field_simp [hd_pos.ne']); rw [hlhs, hrhs]
    exact div_le_div_of_nonneg_right hlin (by positivity)
  linarith [hstep_sn, hp_diff, hbin_div, show 1 + (1 - p) * (SN * psiPiecewise B dNat w x') + p *
    cswapR1CostUpper n (fuseNextAngle n 2 β') - SN * psiPiecewise B dNat w (x' + 1 / SN) = (1 - (SN
    * psiPiecewise B dNat w (x' + 1 / SN) - SN * psiPiecewise B dNat w x')) - p * (SN * psiPiecewise
    B dNat w x' - cswapR1CostUpper n (fuseNextAngle n 2 β')) by ring]
theorem warm2_stage2_step {B n : ℕ} {stFn : ℕ → M2StageScalar} {wFn : ℕ → ℕ → ℕ} {binFn : ℕ → ℕ →
  M2BinCert} (hB : 1 ≤ B) (hn : 100 ≤ n) (hst : checkWarm2StageIdx B stFn wFn binFn 0 = true) (betas
  : Fin 2 → ℝ) (hbetas : ValidStageBetas n 2 (5 / 4) betas) :
    let phiFn := phiFnOfWmSt stFn; let Φ := wmPotential B stFn wFn n
    1 + stepWeight n 2 (phiFn 2) betas 0 * Φ 2 (nextBetasRamp n 2 (phiFn 2) betas) + (∑ o ∈
      Finset.univ.erase 0, stepWeight n 2 (phiFn 2) betas o * expOnHitFuse Φ n 2 o (nextBetasRamp n
      2 (phiFn 2) betas)) ≤ Φ 2 betas := by
  intro phiFn Φ
  have hΦ2 : ∀ b, Φ 2 b = wmStagePot B phiFn stFn wFn n 2 b := fun b ↦ by
    dsimp only [Φ, phiFn, wmPotential]; simp
  have hexp : ∀ o b, expOnHitFuse Φ n 2 o b = cswapWarmR1Cost1 n (nextStageFuseBetas n 2 o b) := fun
    o b ↦ by
    dsimp only [expOnHitFuse, Φ, wmPotential]; simp
  rw [hΦ2, hΦ2, sum_erase_zero_fin_four, hexp, hexp, hexp]; dsimp only [checkWarm2StageIdx,
    Nat.zero_add] at hst; rcases hsr : stFn 2 with ⟨tn, phiHi, phiLo, cSelf, dNat, stepNum, cNat,
    ⟨tBfLo, tdHi, numU, uLock, psiLock, hLock, hBoth⟩⟩; rw [hsr] at hst
  simp only [beq_self_eq_true, ↓reduceIte, withForcedNat_eq, Bool.and_eq_true, and_assoc] at hst
  rcases hst with ⟨ht_lo_d, ht_hi_d, hat_hi, hat_lo, hcS_pos_d, hcS_sq_d, hd1000_d, hcSB_d,
    hclick_chk, hslope_all, hcswap_lock, hboth_zero_d, hstep_w0_d, hlock_comb_d, hbins⟩
  have ht_lo := of_decide_eq_true ht_lo_d; have ht_hi := of_decide_eq_true ht_hi_d; have hd1000 :=
    of_decide_eq_true hd1000_d; have hd1 : 1 ≤ dNat := (by omega)
  have hcSB := of_decide_eq_true hcSB_d; have hw := knotSlope_of_allRange hslope_all; set SN : ℝ :=
    √((2 : ℝ) ^ n); obtain ⟨hSN_ge, _⟩ := pow_two_bounds_100 hn; have hSN_pos : 0 < SN :=
    lt_of_lt_of_le (by positivity) hSN_ge
  rcases phi_and_lockedAlpha_bounds_fuse_100 (m := 2) (by omega) (by omega) hn (by omega : 1 ≤ 2)
    (by omega : 2 ≤ 1024) ht_lo ht_hi with ⟨_, hφ2θ, h54_lt, hlock_bds⟩
  set φ : ℝ := Real.arctan ((tn : ℝ) / 100000); have hφ_eq : phiFn 2 = φ :=
    (by dsimp only [phiFn, phiFnOfWmSt]; rw [hsr]); have hdNat_eq : (stFn 2).dNat = dNat :=
    (by rw [hsr])
  have hs_cap : ∀ i : Fin 2, (remStepsSlot n 2 φ (betas i) : ℝ) ≤ ((cSelf : ℝ) / 1000000000000) * SN
    := fun i ↦ by
    have hm : (remStepsSlot n 2 φ (betas i) : ℝ) ≤ (remStepsSlot n 2 φ (halfAngleSet n 2) : ℝ) :=
      (by exact_mod_cast remStepsSlot_mono_beta (n := n) (r := 2) (by omega) φ (hbetas i).1)
    exact hm.trans (remStepsSlot_halfAngleSet_le_of_atan200Hi_sq hn (by omega) (by omega) ht_lo
      ht_hi hat_hi (of_decide_eq_true hcS_pos_d) (of_decide_eq_true hcS_sq_d))
  rw [hφ_eq]; set postB := nextBetasRamp n 2 φ betas; have hθ2_nn : 0 ≤ halfAngleSet n 2 :=
    Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hpost_valid : ValidStageBetas n 2 (5 / 4) postB := fun i ↦ by
    dsimp only [postB, nextBetasRamp, nextBetaSlot]; split_ifs with hlt
    · refine ⟨by linarith [(hbetas i).1, hθ2_nn], ?_⟩; linarith [hlt, hφ2θ]
    · exact hbetas i
  obtain ⟨⟨hg1, hmax1⟩, ⟨hg2, hmax2⟩, ⟨hg3, hmax3⟩⟩ := cswapWarmGuard_nextStageFuseBetas hn
    hpost_valid; have hc1 : cswapWarmR1Cost1 n (nextStageFuseBetas n 2 ⟨1, (Nat.lt_of_sub_eq_succ
    rfl : 1 < 2 ^ 2)⟩ postB) = cswapR1CostUpper n (fuseNextAngle n 2 (postB s1)) :=
    (by dsimp only [cswapWarmR1Cost1]; rw [ite_eq_left hg1, hmax1])
  have hc2 : cswapWarmR1Cost1 n (nextStageFuseBetas n 2 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩
    postB) = cswapR1CostUpper n (fuseNextAngle n 2 (postB s0)) :=
    (by dsimp only [cswapWarmR1Cost1]; rw [ite_eq_left hg2, hmax2])
  have hc3 : cswapWarmR1Cost1 n (nextStageFuseBetas n 2 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩
    postB) = cswapR1CostUpper n (halfAngleSet n 1) :=
    (by dsimp only [cswapWarmR1Cost1]; rw [ite_eq_left hg3, hmax3]); dsimp only [wmStagePot]
  rw [hφ_eq, hdNat_eq, hc1, hc2, hc3, stepWeight_fin2_zero, stepWeight_fin2_one,
    stepWeight_fin2_two, stepWeight_fin2_three]; by_cases h0 : betas s0 < φ
  · have hα0 : stepAlpha n 2 φ (betas s0) ^ 2 = 1 :=
      (by dsimp only [stepAlpha]; rw [ite_eq_left h0, one_pow])
    have hd0_pos : 1 ≤ remStepsSlot n 2 φ (betas s0) := by
      by_contra hz; have hez : remStepsSlot n 2 φ (betas s0) = 0 := (by omega)
      linarith [(remStepsSlot_eq_zero_iff (n := n) (r := 2) (by omega) φ (betas s0)).1 hez]
    have hs0_post : remStepsSlot n 2 φ (postB s0) = remStepsSlot n 2 φ (betas s0) - 1 := by
      dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 2) (by omega),
        ite_eq_left h0]
    have hpb0 : postB s0 = betas s0 + 2 * halfAngleSet n 2 :=
      (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; rw [ite_eq_left h0])
    by_cases h1 : betas s1 < φ
    · have hα1 : stepAlpha n 2 φ (betas s1) ^ 2 = 1 :=
        (by dsimp only [stepAlpha]; rw [ite_eq_left h1, one_pow])
      have hd1_pos : 1 ≤ remStepsSlot n 2 φ (betas s1) := by
        by_contra hz; have hez : remStepsSlot n 2 φ (betas s1) = 0 := (by omega)
        linarith [(remStepsSlot_eq_zero_iff (n := n) (r := 2) (by omega) φ (betas s1)).1 hez]
      have hs1_post : remStepsSlot n 2 φ (postB s1) = remStepsSlot n 2 φ (betas s1) - 1 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 2)
          (by omega), ite_eq_left h1]
      rw [hα0, hα1, hs0_post, hs1_post, Nat.cast_sub hd0_pos, Nat.cast_sub hd1_pos, Nat.cast_one,
        wmPotVal_sub_one]; exact le_of_eq (by ring)
    · have h1_ge : φ ≤ betas s1 := not_lt.1 h1; have hs1_z : remStepsSlot n 2 φ (betas s1) = 0 :=
        (remStepsSlot_eq_zero_iff (n := n) (r := 2) (by omega) φ (betas s1)).2 h1_ge
      have hs1_post : remStepsSlot n 2 φ (postB s1) = 0 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 2)
          (by omega)]; simp only [h1, ↓reduceIte]
      set p1 : ℝ := 1 - lockedAlpha (betas s1) (halfAngleSet n 2) ^ 2
      have hα1 : stepAlpha n 2 φ (betas s1) ^ 2 = 1 - p1 :=
        (by dsimp only [stepAlpha, p1]; simp only [h1, ↓reduceIte]; ring); have hp1_lo := (hlock_bds
        (betas s1) h1_ge (hbetas s1).2).1; rw [Nat.cast_ofNat] at hp1_lo; rw [hα0, hα1, hs0_post,
        hs1_post, hs1_z, hpb0, Nat.cast_zero, wmPotVal_comm _ _ _ _ _ 0, wmPotVal_comm _ _ _ _ _ 0]
      have hstep := warm2_stage2_single_locked_step hB hn ht_lo ht_hi hat_lo hd1000 hcSB hw hbins
        hp1_lo (hbetas s0).1 h0 (hs_cap s0); dsimp only at hstep
      exact le_of_eq_of_le (by ring) hstep
  · have h0_ge : φ ≤ betas s0 := not_lt.1 h0; have hs0_z : remStepsSlot n 2 φ (betas s0) = 0 :=
      (remStepsSlot_eq_zero_iff (n := n) (r := 2) (by omega) φ (betas s0)).2 h0_ge
    have hs0_post : remStepsSlot n 2 φ (postB s0) = 0 := by
      dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 2) (by omega)]
      simp only [h0, ↓reduceIte]
    have hpb0 : postB s0 = betas s0 :=
      (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [h0, ↓reduceIte])
    set p0 : ℝ := 1 - lockedAlpha (betas s0) (halfAngleSet n 2) ^ 2
    have hα0 : stepAlpha n 2 φ (betas s0) ^ 2 = 1 - p0 :=
      (by dsimp only [stepAlpha, p0]; simp only [h0, ↓reduceIte]; ring); obtain ⟨hp0_lo, hp0_hi⟩ :=
      hlock_bds (betas s0) h0_ge (hbetas s0).2; rw [Nat.cast_ofNat] at hp0_lo hp0_hi
    by_cases h1 : betas s1 < φ
    · have hα1 : stepAlpha n 2 φ (betas s1) ^ 2 = 1 :=
        (by dsimp only [stepAlpha]; rw [ite_eq_left h1, one_pow])
      have hs1_post : remStepsSlot n 2 φ (postB s1) = remStepsSlot n 2 φ (betas s1) - 1 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 2)
          (by omega), ite_eq_left h1]
      have hpb1 : postB s1 = betas s1 + 2 * halfAngleSet n 2 :=
        (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; rw [ite_eq_left h1]); rw [hα0, hα1,
        hs0_post, hs1_post, hs0_z, hpb1, Nat.cast_zero]; have hstep :=
        warm2_stage2_single_locked_step hB hn ht_lo ht_hi hat_lo hd1000 hcSB hw hbins hp0_lo (hbetas
        s1).1 h1 (hs_cap s1); dsimp only at hstep; exact le_of_eq_of_le (by ring) hstep
    · have h1_ge : φ ≤ betas s1 := not_lt.1 h1; have hs1_z : remStepsSlot n 2 φ (betas s1) = 0 :=
        (remStepsSlot_eq_zero_iff (n := n) (r := 2) (by omega) φ (betas s1)).2 h1_ge
      have hs1_post : remStepsSlot n 2 φ (postB s1) = 0 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 2)
          (by omega)]; simp only [h1, ↓reduceIte]
      have hpb1 : postB s1 = betas s1 :=
        (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [h1, ↓reduceIte])
      set p1 : ℝ := 1 - lockedAlpha (betas s1) (halfAngleSet n 2) ^ 2
      have hα1 : stepAlpha n 2 φ (betas s1) ^ 2 = 1 - p1 :=
        (by dsimp only [stepAlpha, p1]; simp only [h1, ↓reduceIte]; ring); obtain ⟨_, hp1_hi⟩ :=
        hlock_bds (betas s1) h1_ge (hbetas s1).2; rw [Nat.cast_ofNat] at hp1_hi; rw [hα0, hα1,
        hs0_post, hs1_post, hs0_z, hs1_z, hpb0, hpb1, Nat.cast_zero, wmPotVal_diag hd1 hw SN 0,
        zero_add]; simp only [sub_sub_cancel]; obtain ⟨hp0_tlo, hp0_thi⟩ :=
        lockedAlpha_m2_r2_tight_bounds_100 hn ht_lo h0_ge (hbetas s0).2
      obtain ⟨hp1_tlo, hp1_thi⟩ := lockedAlpha_m2_r2_tight_bounds_100 hn ht_lo h1_ge (hbetas s1).2
      set p_min : ℝ := 4 * ((tn : ℝ) / 100000) * (999999999998 / 1000000000000) * √(2 : ℝ) / SN
      have ht_pos : (0 : ℝ) < tn := Nat.cast_pos.2 (by omega); have hp_min_pos : 0 < p_min :=
        (by dsimp only [p_min]; positivity); obtain ⟨h1q0_pos, h2p_rho, hprod_le⟩ :=
        two_locked_one_sub_q0_bounds_r2_tight hp_min_pos hp0_tlo hp1_tlo hp0_thi hp1_thi
      have hhit1 : cswapR1CostUpper n (fuseNextAngle n 2 (betas s1)) ≤ ((hLock : ℝ) / 1000000000000)
        * SN := cswapR1CostUpper_fuseNextAngle_lock_le hn (by omega) h1_ge (hbetas s1).2 hcswap_lock
      have hhit2 : cswapR1CostUpper n (fuseNextAngle n 2 (betas s0)) ≤ ((hLock : ℝ) / 1000000000000)
        * SN := cswapR1CostUpper_fuseNextAngle_lock_le hn (by omega) h0_ge (hbetas s0).2 hcswap_lock
      set extra : ℕ := if hLock ≤ hBoth then hBoth - hLock else 0
      have hboth_le_ex : hBoth ≤ hLock + extra := by
        dsimp only [extra]; split_ifs
        · omega
        · omega
      rcases halfAngleSet_bounds_100 hn (by omega : 1 ≤ 1) (by omega : 1 ≤ 1024) with ⟨_, _, hθ1_13,
        -⟩; have hθ1_nn : 0 ≤ halfAngleSet n 1 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
      have hhit3 : cswapR1CostUpper n (halfAngleSet n 1) ≤ (((hLock : ℝ) + extra) / 1000000000000) *
        SN := by
        refine (cswapR1CostUpper_le_of_zeroHit hθ1_nn (by linarith [hθ1_13]) (of_decide_eq_true
          hboth_zero_d)).trans ?_; have hex_r : (hBoth : ℝ) ≤ (hLock : ℝ) + extra :=
          (by exact_mod_cast hboth_le_ex)
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hex_r (by norm_num)) hSN_pos.le
      have hp0_nn : 0 ≤ p0 := le_trans hp_min_pos.le hp0_tlo
      have hp1_nn : 0 ≤ p1 := le_trans hp_min_pos.le hp1_tlo
      have hp0_le1 : p0 ≤ 1 := hp0_hi.trans (by norm_num)
      have hp1_le1 : p1 ≤ 1 := hp1_hi.trans (by norm_num); set q0 : ℝ := (1 - p0) * (1 - p1)
      have hhit_sum : p0 * (1 - p1) * cswapR1CostUpper n (fuseNextAngle n 2 (betas s1)) + (1 - p0) *
        p1 * cswapR1CostUpper n (fuseNextAngle n 2 (betas s0)) + p0 * p1 * cswapR1CostUpper n
        (halfAngleSet n 1) ≤ (1 - q0) * ((((hLock : ℝ) + (extra : ℝ) / 4000000000000) /
        1000000000000) * SN) := by
        have hm1 := mul_le_mul_of_nonneg_left hhit1 (mul_nonneg hp0_nn (sub_nonneg.2 hp1_le1))
        have hm2 := mul_le_mul_of_nonneg_left hhit2 (mul_nonneg (sub_nonneg.2 hp0_le1) hp1_nn)
        have hm3 := mul_le_mul_of_nonneg_left hhit3 (mul_nonneg hp0_nn hp1_nn); have hm_ex : (p0 *
          p1) * (((extra : ℝ) / 1000000000000) * SN) ≤ ((1 / 4000000000000) * (1 - q0)) * (((extra :
          ℝ) / 1000000000000) * SN) := mul_le_mul_of_nonneg_right hprod_le (by positivity)
        have hsum_w : p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1 = 1 - q0 := (by dsimp only [q0]; ring)
        linarith [hm1, hm2, hm3, hm_ex, show p0 * (1 - p1) * (((hLock : ℝ) / 1000000000000) * SN) +
              (1 - p0) * p1 * (((hLock : ℝ) / 1000000000000) * SN) +
              p0 * p1 * ((((hLock : ℝ) + extra) / 1000000000000) * SN) =
            (p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1) * (((hLock : ℝ) / 1000000000000) * SN) +
              (p0 * p1) * (((extra : ℝ) / 1000000000000) * SN) by ring,
          show (p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1) * (((hLock : ℝ) / 1000000000000) * SN) =
            (1 - q0) * (((hLock : ℝ) / 1000000000000) * SN) by rw [hsum_w],
          show (1 - q0) * (((hLock : ℝ) / 1000000000000) * SN) +
              ((1 / 4000000000000) * (1 - q0)) * (((extra : ℝ) / 1000000000000) * SN) =
            (1 - q0) * ((((hLock : ℝ) + (extra : ℝ) / 4000000000000) / 1000000000000) * SN) by ring]
      have hclick := clickRowM2R2Tight_sound (n := n) ht_lo hclick_chk; have hclick' : 1 / (2 *
        p_min * (1 - 2 * (1 / (2000000000000 * (2 : ℝ))))) ≤ ((stepNum : ℝ) / 1000000000000) * SN :=
        (by simpa [p_min, SN] using hclick)
      have h1_le : 1 ≤ (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) := by
        have hden_pos : 0 < 2 * p_min * (1 - 2 * (1 / (2000000000000 * (2 : ℝ)))) :=
          (by have : (0 : ℝ) < 1 - 2 * (1 / (2000000000000 * (2 : ℝ))) := (by norm_num); positivity)
        calc (1 : ℝ) = (2 * p_min * (1 - 2 * (1 / (2000000000000 * (2 : ℝ))))) *
              (1 / (2 * p_min * (1 - 2 * (1 / (2000000000000 * (2 : ℝ)))))) := by
              field_simp [hden_pos.ne']
          _ ≤ (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) :=
              mul_le_mul h2p_rho hclick' (by positivity) h1q0_pos.le
      have hstep_w0 := of_decide_eq_true hstep_w0_d; have hcomb_r : 4000000000000 * (hLock : ℝ) +
        extra ≤ 4000000000000 * ((wFn 2 0 - stepNum : ℕ) : ℝ) :=
        (by exact_mod_cast of_decide_eq_true hlock_comb_d); rw [Nat.cast_sub hstep_w0] at hcomb_r
      have hcomb_sn : (((hLock : ℝ) + (extra : ℝ) / 4000000000000) / 1000000000000) * SN ≤ (((wFn 2
        0 : ℝ) - stepNum) / 1000000000000) * SN := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hSN_pos.le; have hm_comb :=
        mul_le_mul_of_nonneg_left hcomb_sn h1q0_pos.le; linarith [hhit_sum, h1_le, hm_comb, show (1
        - q0) * (((stepNum : ℝ) / 1000000000000) * SN) + (1 - q0) * ((((wFn 2 0 : ℝ) - stepNum) /
        1000000000000) * SN) + q0 * (((wFn 2 0 : ℝ) / 1000000000000) * SN) = ((wFn 2 0 : ℝ) /
        1000000000000) * SN by ring]
/-! ## 4. Stage-`≥ 3` (`r ≥ 3` Piecewise-Linear Transition) Step Soundness -/
theorem warm2_stageGe3_single_locked_step {B n r tn phiLo cSelf dNat tp phiHiP dNatP cNat : ℕ} {w wP
  : ℕ → ℕ} {binR : ℕ → M2BinCert} (hB : 1 ≤ B) (hn : 100 ≤ n) (hr2 : 2 ≤ r) (hr1024 : r ≤ 1024)
  (ht_lo : 500 ≤ tn) (ht_hi : tn ≤ 200000) (hphiLo_chk : checkAtan200Lo tn phiLo = true) (hd1000 :
  1000 ≤ dNat) (hcB : cSelf ≤ B * dNat) (hdP1 : 1 ≤ dNatP) (hphiP_chk : checkAtan200Hi tp phiHiP =
  true) (hw : ∀ i < B, w i ≤ w (i + 1) ∧ w (i + 1) ≤ w i + dNat) (hwP : ∀ i < B, wP i ≤ wP (i + 1) ∧
  wP (i + 1) ≤ wP i + dNatP) (hbins : allRange (fun j ↦ checkWarm2StageGe3Bin B r tn phiLo dNat tp
  phiHiP dNatP cNat w wP (binR j) j) B = true) {p βRamp : ℝ} (hp_lo : 4 * ((tn : ℝ) / 100000) *
  (99999999 / 100000000) * √(r : ℝ) / √((2 : ℝ) ^ n) ≤ p) (hβ_lo : halfAngleSet n r ≤ βRamp) (hβ_lt
  : βRamp < Real.arctan ((tn : ℝ) / 100000)) (hc_cap : (remStepsSlot n (r - 1) (Real.arctan ((tp :
  ℝ) / 100000)) (halfAngleSet n (r - 1)) : ℝ) ≤ ((cNat : ℝ) / 1000000000000) * √((2 : ℝ) ^ n))
  (hd_cap : (remStepsSlot n r (Real.arctan ((tn : ℝ) / 100000)) βRamp : ℝ) ≤ ((cSelf : ℝ) /
  1000000000000) * √((2 : ℝ) ^ n)) :
    let SN := √((2 : ℝ) ^ n); let φ := Real.arctan ((tn : ℝ) / 100000)
    let φp := Real.arctan ((tp : ℝ) / 100000); let d := remStepsSlot n r φ βRamp
    let sReset := (remStepsSlot n (r - 1) φp (halfAngleSet n (r - 1)) : ℝ)
    let sFuse := (remStepsSlot n (r - 1) φp (fuseNextAngle n r (βRamp + 2 * halfAngleSet n r)) : ℝ)
    1 + (1 - p) * wmPotVal B dNat w SN 0 ((d - 1 : ℕ) : ℝ) + p * wmPotVal B dNatP wP SN sReset sFuse
      ≤ wmPotVal B dNat w SN 0 (d : ℝ) := by
  intro SN φ φp d sReset sFuse; obtain ⟨hSN_ge, hN_ge⟩ := pow_two_bounds_100 hn; have hSN_pos : 0 <
    SN := lt_of_lt_of_le (by positivity) hSN_ge; have hN_pos : (0 : ℝ) < (2 : ℝ) ^ n :=
    lt_of_lt_of_le (by positivity) hN_ge; have hr1 : 1 ≤ r := (by omega); have hrp1 : 1 ≤ r - 1 :=
    (by omega); have hrp1024 : r - 1 ≤ 1024 := (by omega); have h2r : 2 * r ≤ 2 ^ n :=
    two_mul_le_pow_100 hn hr1024
  have hd1 : 1 ≤ d := by
    by_contra h0
    have hez : d = 0 := (by omega); linarith [(remStepsSlot_eq_zero_iff hr1 φ βRamp).1 hez]
  have hd_ge1 : 1 ≤ dNat := (by omega)
  have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd_ge1; set δ : ℝ := (dNat : ℝ) / 1000000000000
  have hδ_pos : 0 < δ := (by positivity); set x' : ℝ := ((d - 1 : ℕ) : ℝ) / SN
  have hx'0 : 0 ≤ x' := (by positivity)
  have hx'B : x' ≤ (B : ℝ) * δ := by
    have h1 : ((d - 1 : ℕ) : ℝ) ≤ d := (by exact_mod_cast Nat.sub_le d 1); have h2 : (d : ℝ) / SN ≤
      (cSelf : ℝ) / 1000000000000 := (div_le_iff₀ hSN_pos).2 hd_cap
    have h3 : (cSelf : ℝ) / 1000000000000 ≤ (B : ℝ) * δ := by
      dsimp only [δ]; have hcB_r : (cSelf : ℝ) ≤ (B : ℝ) * dNat := (by exact_mod_cast hcB); linarith
    exact (div_le_div_of_nonneg_right h1 hSN_pos.le).trans (h2.trans h3)
  obtain ⟨j, hj, hx'_lo, hx'_hi⟩ := exists_bin_of_le hB hδ_pos hx'0 hx'B
  have h_invSN_le_δ : 1 / SN ≤ δ := by
    have h1 : 1 / SN ≤ 1 / 1000000000000000 := one_div_le_one_div_of_le (by positivity) hSN_ge
    have h2 : (1000 : ℝ) ≤ dNat := (by exact_mod_cast hd1000); dsimp only [δ]; linarith
  have hd_split : (d : ℝ) / SN = x' + 1 / SN :=
    (by dsimp only [x']; rw [Nat.cast_sub hd1, Nat.cast_one]; field_simp [hSN_pos.ne']; ring)
  rw [wmPotVal_zero_left B dNat w SN (by positivity : (0 : ℝ) ≤ (d - 1 : ℕ)), wmPotVal_zero_left B
    dNat w SN (by positivity : (0 : ℝ) ≤ d), hd_split]; have hstep_psi :=
    psiPiecewise_step_ge_minDiff hd_ge1 hw hj hx'_lo hx'_hi (by positivity) h_invSN_le_δ
  have hstep_sn : (minDiffNat B w j : ℝ) / dNat ≤ SN * psiPiecewise B dNat w (x' + 1 / SN) - SN *
    psiPiecewise B dNat w x' := by
    have hm := mul_le_mul_of_nonneg_left hstep_psi hSN_pos.le; have hl : SN * (((minDiffNat B w j :
      ℝ) / dNat) * (1 / SN)) = (minDiffNat B w j : ℝ) / dNat := (by field_simp [hSN_pos.ne'])
    linarith [hm, hl, show SN * (psiPiecewise B dNat w (x' + 1 / SN) - psiPiecewise B dNat w x') =
      SN * psiPiecewise B dNat w (x' + 1 / SN) - SN * psiPiecewise B dNat w x' by ring]
  have hpost_ge : ((w j : ℝ) / 1000000000000) * SN ≤ SN * psiPiecewise B dNat w x' := by
    have hm := psiPiecewise_mono (B := B) (dNat := dNat) (w := w) hx'_lo; dsimp only [δ] at hm
    rw [psiPiecewise_knot hd_ge1 hw hj.le] at hm; linarith [mul_le_mul_of_nonneg_left hm hSN_pos.le]
  have hbin_chk := of_allRange hbins hj; rcases hbc : binR j with ⟨tcLo, bLoHi, dropHi, tBfLo, tdHi,
    numU, uNat, psiHi, hHi⟩; rw [hbc] at hbin_chk; simp only [checkWarm2StageGe3Bin,
    withForcedNat_eq, Bool.and_eq_true, and_assoc] at hbin_chk; rcases hbin_chk with ⟨hbr_tc,
    hpsi_chk, huh_d, hhw_d, hsq_d⟩; have huh : uNat + psiHi ≤ hHi := of_decide_eq_true huh_d
  have hhw : hHi ≤ w j := of_decide_eq_true hhw_d; have hsq_nat := of_decide_eq_true hsq_d
  rcases halfAngleSet_bounds_100 hn hr1 hr1024 with ⟨hθc_lo, hθc_hi, hθc_13, -⟩
  rcases halfAngleSet_bounds_100 hn hrp1 hrp1024 with ⟨hθp_lo, -⟩
  rcases phi_and_lockedAlpha_bounds_fuse_100 (m := 1) le_rfl (by omega) hn hr1 hr1024 ht_lo ht_hi
    with ⟨_, hφ2θ, h54_lt, -⟩
  have hθc_pos : 0 < halfAngleSet n r := lt_of_lt_of_le (by positivity) hθc_lo
  set β' : ℝ := βRamp + 2 * halfAngleSet n r; have hβ'_θ : halfAngleSet n r ≤ β' :=
    (by dsimp only [β']; linarith); have hβ'_lt : β' < π / 2 :=
    (by dsimp only [β']; linarith [hβ_lt, hφ2θ, h54_lt])
  have hu_and_sFuse : uNat ≤ cNat ∧ sFuse ≤ ((uNat : ℝ) / 1000000000000) * SN := by
    by_cases htc0 : tcLo = 0
    · subst htc0; simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq] at hbr_tc; subst hbr_tc
      refine ⟨le_rfl, ?_⟩; have hfg := halfAngleSet_le_fuseNextAngle hr2 h2r hβ'_θ hβ'_lt.le
      have hmono : sFuse ≤ sReset :=
        (by dsimp only [sFuse, sReset]; exact Nat.cast_le.2 (remStepsSlot_mono_beta hrp1 φp hfg))
      exact hmono.trans hc_cap
    · have htc0_b : (tcLo == 0) = false := beq_false_of_ne htc0; rw [htc0_b] at hbr_tc
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, and_assoc] at hbr_tc
      rcases hbr_tc with ⟨htc1_d, _, hat_tc, hdrop_sq_d, hbdrop_d, hdrift_tc⟩
      have htc1 : 1 ≤ tcLo := of_decide_eq_true htc1_d
      have hdrop_sq := of_decide_eq_true hdrop_sq_d; have hbdrop := of_decide_eq_true hbdrop_d
      have hceil_le : φ - βRamp ≤ (d : ℝ) * (2 * halfAngleSet n r) :=
        (by dsimp only [d, remStepsSlot]; exact (div_le_iff₀ (by positivity)).1 (Nat.le_ceil _))
      have hφ_sub_β' : φ - β' ≤ 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n r :=
        (by dsimp only [β']; rw [Nat.cast_sub hd1, Nat.cast_one]; linarith); have hd1_le : ((d - 1 :
        ℕ) : ℝ) ≤ (((j + 1 : ℕ) : ℝ) * δ) * SN := (div_le_iff₀ hSN_pos).1 hx'_hi; have hr_le : (r :
        ℝ) ≤ 1024 := (by exact_mod_cast hr1024)
      have hrN : (r : ℝ) / (2 : ℝ) ^ n ≤ 1 / 1000000000000 := by
        have h1 : (r : ℝ) / (2 : ℝ) ^ n ≤ 1024 / (1000000000000000 * 1000000000000000) :=
          (div_le_div_of_nonneg_right hr_le hN_pos.le).trans (div_le_div_of_nonneg_left
          (by positivity) (by positivity) hN_ge); linarith
      have hθc_up : halfAngleSet n r ≤ (√(r : ℝ) / SN) * (1000000000001 / 1000000000000) :=
        hθc_hi.trans (mul_le_mul_of_nonneg_left (by linarith [hrN]) (by positivity))
      have hdrop_prod : 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n r ≤ (2 * √(r : ℝ) * (((j + 1) * dNat
        * 1000000000001 : ℕ) : ℝ)) / (1000000000000 * 1000000000000) := by
        have hm := mul_le_mul (mul_le_mul_of_nonneg_left hd1_le (by norm_num : (0 : ℝ) ≤ 2)) hθc_up
          hθc_pos.le (by positivity); have heq : (2 * ((((j + 1 : ℕ) : ℝ) * δ) * SN)) * ((√(r : ℝ) /
          SN) * (1000000000001 / 1000000000000)) = (2 * √(r : ℝ) * (((j + 1) * dNat * 1000000000001
          : ℕ) : ℝ)) / (1000000000000 * 1000000000000) :=
          (by dsimp only [δ]; push_cast; field_simp [hSN_pos.ne']); linarith [hm, heq]
      have hdrop_le : 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n r ≤ (dropHi : ℝ) / 1000000000000 := by
        refine hdrop_prod.trans ?_
        have hroot_le : 2 * √(r : ℝ) * (((j + 1) * dNat * 1000000000001 : ℕ) : ℝ) ≤ (dropHi : ℝ) *
          1000000000000 := by
          refine sq_le_imp_le (by positivity) (by positivity) ?_; set dr : ℕ := (j + 1) * dNat *
            1000000000001
          have hcast : 4 * (r : ℝ) * (dr : ℝ) * dr ≤ ((dropHi : ℝ) * 1000000000000) * ((dropHi : ℝ)
            * 1000000000000) := (by exact_mod_cast hdrop_sq); have hr_nn : (0 : ℝ) ≤ r :=
            (by positivity)
          have hlhs_sq : (2 * √(r : ℝ) * (dr : ℝ)) ^ 2 = 4 * (r : ℝ) * (dr : ℝ) * dr := by
            calc (2 * √(r : ℝ) * (dr : ℝ)) ^ 2 = 4 * (√(r : ℝ)) ^ 2 * (dr : ℝ) * dr := by ring
              _ = 4 * (r : ℝ) * (dr : ℝ) * dr := by rw [Real.sq_sqrt hr_nn]
          linarith [hcast, hlhs_sq, show ((dropHi : ℝ) * 1000000000000) ^ 2 = ((dropHi : ℝ) *
            1000000000000) * ((dropHi : ℝ) * 1000000000000) by ring]
        have hrhs : (dropHi : ℝ) / 1000000000000 = ((dropHi : ℝ) * 1000000000000) / (1000000000000 *
          1000000000000) := (by ring); rw [hrhs]
        exact div_le_div_of_nonneg_right hroot_le (by norm_num)
      have hphiLo_le := atan200Lo_sound hphiLo_chk; have hbLo_ge := atan200Hi_sound hat_tc
      have hbdrop_r : (bLoHi : ℝ) + dropHi ≤ phiLo := (by exact_mod_cast hbdrop)
      have hatan_tc_le_β' : Real.arctan ((tcLo : ℝ) / 100000) ≤ β' := by
        have hbd_div : (bLoHi : ℝ) / 1000000000000 + (dropHi : ℝ) / 1000000000000 ≤ (phiLo : ℝ) /
          1000000000000 := (by linarith [hbdrop_r]); linarith [hbLo_ge, hphiLo_le, hφ_sub_β',
          hdrop_le, hbd_div]
      have hatan_tc_ge_θ : halfAngleSet n r ≤ Real.arctan ((tcLo : ℝ) / 100000) := by
        have h1 : (1 : ℝ) / 100000 ≤ (tcLo : ℝ) / 100000 :=
          (by have : (1 : ℝ) ≤ tcLo := (by exact_mod_cast htc1); linarith)
        have hp : (1 : ℝ) / 10000000000000 ≤ Real.arctan ((1 : ℝ) / 100000) := le_trans
          (by norm_num) (pade56_le_arctan (by norm_num : (0 : ℝ) ≤ 1 / 100000)); linarith [hθc_13,
          hp, Real.arctan_mono h1]
      have hβFuse_tc : Real.arcsin (√(((r - 1 : ℕ) : ℝ) / r) * Real.sin (Real.arctan ((tcLo : ℝ) /
        100000))) ≤ fuseNextAngle n r β' := (arcsin_sqrt_nat_sub_ratio_le_fuseNextAngle hr2 h2r
        hatan_tc_ge_θ (Real.arctan_lt_pi_div_two _)).trans (fuseNextAngle_mono hr2 h2r hatan_tc_ge_θ
        hatan_tc_le_β' hβ'_lt.le)
      obtain ⟨hu_le_c, _, hu_bound⟩ := fuseDriftCert_sound hr2 hSN_ge hθp_lo (atan200Hi_sound
        hphiP_chk) hβFuse_tc hdrift_tc; exact ⟨hu_le_c, remStepsSlot_le_of_three_add_max hrp1
        (by positivity) hu_bound⟩
  have hhit_le : wmPotVal B dNatP wP SN sReset sFuse ≤ ((hHi : ℝ) / 1000000000000) * SN :=
    wmPotVal_hit_single_le hdP1 hwP hSN_pos hu_and_sFuse.1 hpsi_chk huh hc_cap hu_and_sFuse.2
  have hp_nn : 0 ≤ p := le_trans (by positivity) hp_lo
  have hdiff_ge : (((w j - hHi : ℕ) : ℝ) / 1000000000000) * SN ≤ SN * psiPiecewise B dNat w x' -
    wmPotVal B dNatP wP SN sReset sFuse := by
    rw [Nat.cast_sub hhw]; linarith [hpost_ge, hhit_le, show ((w j : ℝ) / 1000000000000) * SN -
      ((hHi : ℝ) / 1000000000000) * SN = (((w j : ℝ) - hHi) / 1000000000000) * SN by ring]
  have hp_diff : (√(r : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 *
    100000000 * 1000000000000) ≤ p * (SN * psiPiecewise B dNat w x' - wmPotVal B dNatP wP SN sReset
    sFuse) := by
    have hm := mul_le_mul hp_lo hdiff_ge (by positivity) hp_nn; have heq : (4 * ((tn : ℝ) / 100000)
      * (99999999 / 100000000) * √(r : ℝ) / SN) * ((((w j - hHi : ℕ) : ℝ) / 1000000000000) * SN) =
      (√(r : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 * 100000000 *
      1000000000000) := (by field_simp [hSN_pos.ne']); linarith
  have hmd_le_d : minDiffNat B w j ≤ dNat := by
    have hsub : w (j + 1) - w j ≤ dNat := (by have := (hw j hj).2; omega); dsimp only [minDiffNat]
    rw [withForcedNat_eq]; split_ifs
    · exact hsub
    · exact (Nat.min_le_left _ _).trans hsub
  have hbin_div : 1 - (minDiffNat B w j : ℝ) / dNat ≤ (√(r : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j -
    hHi : ℕ) : ℝ))) / (100000 * 100000000 * 1000000000000) := by
    set lhsN : ℕ := (dNat - minDiffNat B w j) * 100000 * 100000000 * 1000000000000; set rhsN : ℕ :=
      dNat * 4 * tn * 99999999 * (w j - hHi)
    have hlin : (lhsN : ℝ) ≤ √(r : ℝ) * (rhsN : ℝ) := by
      refine sq_le_imp_le (by positivity) (by positivity) ?_; have hcast : (lhsN : ℝ) * lhsN ≤ (r :
        ℝ) * (rhsN : ℝ) * rhsN := (by exact_mod_cast hsq_nat); have hr_nn : (0 : ℝ) ≤ r :=
        (by positivity)
      have hrsq : (√(r : ℝ) * (rhsN : ℝ)) ^ 2 = (r : ℝ) * (rhsN : ℝ) * rhsN := by
        calc (√(r : ℝ) * (rhsN : ℝ)) ^ 2 = (√(r : ℝ)) ^ 2 * (rhsN : ℝ) * rhsN := by ring
          _ = (r : ℝ) * (rhsN : ℝ) * rhsN := by rw [Real.sq_sqrt hr_nn]
      linarith [hcast, hrsq, show (lhsN : ℝ) ^ 2 = (lhsN : ℝ) * lhsN by ring]
    have hlhs : 1 - (minDiffNat B w j : ℝ) / dNat = (lhsN : ℝ) / ((dNat : ℝ) * (100000 * 100000000 *
      1000000000000)) := by
      dsimp only [lhsN]; rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hmd_le_d]
      field_simp [hd_pos.ne']; ring
    have hrhs : (√(r : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 * 100000000
      * 1000000000000) = (√(r : ℝ) * (rhsN : ℝ)) / ((dNat : ℝ) * (100000 * 100000000 *
      1000000000000)) := (by dsimp only [rhsN]; push_cast; field_simp [hd_pos.ne']); rw [hlhs, hrhs]
    exact div_le_div_of_nonneg_right hlin (by positivity)
  linarith [hstep_sn, hp_diff, hbin_div, show 1 + (1 - p) * (SN * psiPiecewise B dNat w x') + p *
    wmPotVal B dNatP wP SN sReset sFuse - SN * psiPiecewise B dNat w (x' + 1 / SN) = (1 - (SN *
    psiPiecewise B dNat w (x' + 1 / SN) - SN * psiPiecewise B dNat w x')) - p * (SN * psiPiecewise B
    dNat w x' - wmPotVal B dNatP wP SN sReset sFuse) by ring]
theorem warm2_stageGe3_step {B n r : ℕ} {stFn : ℕ → M2StageScalar} {wFn : ℕ → ℕ → ℕ} {binFn : ℕ → ℕ
  → M2BinCert} (hB : 1 ≤ B) (hn : 100 ≤ n) (hr3 : 3 ≤ r) (hr1024 : r ≤ 1024) (hst_cur :
  checkWarm2StageIdx B stFn wFn binFn (r - 2) = true) (hst_prev : checkWarm2StageIdx B stFn wFn
  binFn (r - 3) = true) (betas : Fin 2 → ℝ) (hbetas : ValidStageBetas n r (5 / 4) betas) :
    let phiFn := phiFnOfWmSt stFn; let Φ := wmPotential B stFn wFn n
    1 + stepWeight n r (phiFn r) betas 0 * Φ r (nextBetasRamp n r (phiFn r) betas) + (∑ o ∈
      Finset.univ.erase 0, stepWeight n r (phiFn r) betas o * expOnHitFuse Φ n r o (nextBetasRamp n
      r (phiFn r) betas)) ≤ Φ r betas := by
  intro phiFn Φ; have hr2 : 2 ≤ r := (by omega); have hr1 : 1 ≤ r := (by omega); have hrp2 : 2 ≤ r -
    1 := (by omega); have hrp1 : 1 ≤ r - 1 := (by omega); have hrp1024 : r - 1 ≤ 1024 := (by omega)
  have h2r : 2 * r ≤ 2 ^ n := two_mul_le_pow_100 hn hr1024
  have hΦr : ∀ b, Φ r b = wmStagePot B phiFn stFn wFn n r b := fun b ↦ by
    dsimp only [Φ, wmPotential]; rw [ite_eq_right (by omega : ¬ r ≤ 1)]
  have hΦp : ∀ b, Φ (r - 1) b = wmStagePot B phiFn stFn wFn n (r - 1) b := fun b ↦ by
    dsimp only [Φ, wmPotential]; rw [ite_eq_right (by omega : ¬ r - 1 ≤ 1)]
  have hexp : ∀ o b, expOnHitFuse Φ n r o b = wmStagePot B phiFn stFn wFn n (r - 1)
    (nextStageFuseBetas n r o b) := fun o b ↦ by
    dsimp only [expOnHitFuse]; rw [ite_eq_left hr2]; exact hΦp _
  rw [hΦr, hΦr, sum_erase_zero_fin_four, hexp, hexp, hexp]; have hr_sub : r - 2 + 2 = r :=
    (by omega); have hrp_sub1 : r - 2 + 1 = r - 1 := (by omega); have hidx_ne0 : (r - 2 == 0) =
    false := beq_false_of_ne (by omega); dsimp only [checkWarm2StageIdx] at hst_cur; rw [hr_sub,
    hrp_sub1] at hst_cur; rcases hsr : stFn r with ⟨tn, phiHi, phiLo, cSelf, dNat, stepNum, cNat,
    ⟨tBfLo, tdHi, numU, uLock, psiLock, hLock, hBoth⟩⟩; rcases hsp : stFn (r - 1) with ⟨tp, phiHiP,
    phiLoP, cSelfP, dNatP, stepNumP, cNatP, ⟨tBfLoP, tdHiP, numUP, uLockP, psiLockP, hLockP,
    hBothP⟩⟩; rw [hsr, hsp] at hst_cur; simp only [hidx_ne0, Bool.false_eq_true, ↓reduceIte,
    withForcedNat_eq, Bool.and_eq_true, and_assoc] at hst_cur; rcases hst_cur with ⟨ht_lo_d,
    ht_hi_d, hat_hi, hat_lo, hcS_pos_d, hcS_sq_d, hd1000_d, hcSB_d, hclick_chk, hslope_all,
    hdrift_lock, hpsi_lock, huh_lock_d, hcb_lock_d, hstep_w0_d, hlock_comb_d, hbins⟩
  have hrp_sub2 : r - 3 + 2 = r - 1 := (by omega)
  dsimp only [checkWarm2StageIdx] at hst_prev; rw [hrp_sub2, hsp] at hst_prev
  simp only [Bool.and_eq_true, and_assoc] at hst_prev; rcases hst_prev with ⟨_, _, hat_prev, _, _,
    _, hdP1000_d, _, _, hslopeP_all, _⟩; have ht_lo := of_decide_eq_true ht_lo_d; have ht_hi :=
    of_decide_eq_true ht_hi_d; have hd1000 := of_decide_eq_true hd1000_d; have hd1 : 1 ≤ dNat :=
    (by omega); have hdP1 : 1 ≤ dNatP := (by have := of_decide_eq_true hdP1000_d; omega)
  have hcSB := of_decide_eq_true hcSB_d; have hw := knotSlope_of_allRange hslope_all; have hwP :=
    knotSlope_of_allRange hslopeP_all; set SN : ℝ := √((2 : ℝ) ^ n); obtain ⟨hSN_ge, _⟩ :=
    pow_two_bounds_100 hn; have hSN_pos : 0 < SN := lt_of_lt_of_le (by positivity) hSN_ge
  rcases halfAngleSet_bounds_100 hn hrp1 hrp1024 with ⟨hθp_lo, -⟩
  rcases phi_and_lockedAlpha_bounds_fuse_100 (m := 2) (by omega) (by omega) hn hr1 hr1024 ht_lo
    ht_hi with ⟨h2θ_φ, _, h54_lt, hlock_bds⟩
  set φ : ℝ := Real.arctan ((tn : ℝ) / 100000); set φp : ℝ := Real.arctan ((tp : ℝ) / 100000)
  have hφ_eq : phiFn r = φ := (by dsimp only [phiFn, phiFnOfWmSt]; rw [hsr]); have hφp_eq : phiFn (r
    - 1) = φp := (by dsimp only [phiFn, phiFnOfWmSt]; rw [hsp]); have hdNat_eq : (stFn r).dNat =
    dNat := (by rw [hsr]); have hdNatP_eq : (stFn (r - 1)).dNat = dNatP := (by rw [hsp])
  have hθc_nn : 0 ≤ halfAngleSet n r := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hβFuse_φ : Real.arcsin (√(((r - 1 : ℕ) : ℝ) / r) * Real.sin φ) ≤ fuseNextAngle n r φ :=
    arcsin_sqrt_nat_sub_ratio_le_fuseNextAngle hr2 h2r (by linarith) (Real.arctan_lt_pi_div_two _)
  obtain ⟨huLock_le_c, hc_bound, huLock_bound⟩ := fuseDriftCert_sound hr2 hSN_ge hθp_lo
    (atan200Hi_sound hat_prev) hβFuse_φ hdrift_lock; set sReset : ℝ := (remStepsSlot n (r - 1) φp
    (halfAngleSet n (r - 1)) : ℝ)
  have hc_cap : sReset ≤ ((cNat : ℝ) / 1000000000000) * SN := by
    dsimp only [sReset, remStepsSlot]
    have hθp_pos : 0 < halfAngleSet n (r - 1) := lt_of_lt_of_le (by positivity) hθp_lo
    by_cases hge : halfAngleSet n (r - 1) ≤ φp
    · linarith [Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.2 hge) (by positivity :
        0 ≤ 2 * halfAngleSet n (r - 1))), hc_bound]
    · have hz : ⌈(φp - halfAngleSet n (r - 1)) / (2 * halfAngleSet n (r - 1))⌉₊ = 0 :=
        Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)); rw [hz,
        Nat.cast_zero]; exact mul_nonneg (by positivity) hSN_pos.le
  have hs_cap : ∀ i : Fin 2, (remStepsSlot n r φ (betas i) : ℝ) ≤ ((cSelf : ℝ) / 1000000000000) * SN
    := fun i ↦ by
    have hm : (remStepsSlot n r φ (betas i) : ℝ) ≤ (remStepsSlot n r φ (halfAngleSet n r) : ℝ) :=
      (by exact_mod_cast remStepsSlot_mono_beta hr1 φ (hbetas i).1)
    exact hm.trans (remStepsSlot_halfAngleSet_le_of_atan200Hi_sq hn hr1 hr1024 ht_lo ht_hi hat_hi
      (of_decide_eq_true hcS_pos_d) (of_decide_eq_true hcS_sq_d))
  have hsLock_le : ∀ β, φ ≤ β → β ≤ 5 / 4 → (remStepsSlot n (r - 1) φp (fuseNextAngle n r β) : ℝ) ≤
    ((uLock : ℝ) / 1000000000000) * SN := fun β hβ_ge hβ_hi ↦ by
    have hf_mono : fuseNextAngle n r φ ≤ fuseNextAngle n r β := fuseNextAngle_mono hr2 h2r
      (by linarith) hβ_ge (hβ_hi.trans h54_lt.le); have hm : (remStepsSlot n (r - 1) φp
      (fuseNextAngle n r β) : ℝ) ≤ (remStepsSlot n (r - 1) φp (fuseNextAngle n r φ) : ℝ) :=
      (by exact_mod_cast remStepsSlot_mono_beta hrp1 φp hf_mono)
    exact hm.trans (remStepsSlot_le_of_three_add_max hrp1 (by positivity) huLock_bound)
  dsimp only [wmStagePot]; rw [hφ_eq, hφp_eq, hdNat_eq, hdNatP_eq]
  set postB := nextBetasRamp n r φ betas; have hns1_0 : nextStageFuseBetas n r ⟨1,
    (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postB s0 = halfAngleSet n (r - 1) := (by rfl)
  have hns1_1 : nextStageFuseBetas n r ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postB s1 =
    fuseNextAngle n r (postB s1) := rfl; have hns2_0 : nextStageFuseBetas n r ⟨2,
    (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postB s0 = fuseNextAngle n r (postB s0) := rfl
  have hns2_1 : nextStageFuseBetas n r ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postB s1 =
    halfAngleSet n (r - 1) := (by rfl); have hns3_0 : nextStageFuseBetas n r ⟨3,
    (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postB s0 = halfAngleSet n (r - 1) := (by rfl)
  have hns3_1 : nextStageFuseBetas n r ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postB s1 =
    halfAngleSet n (r - 1) := (by rfl); have hsR_eq : (remStepsSlot n (r - 1) φp (halfAngleSet n (r
    - 1)) : ℝ) = sReset := rfl; rw [hns1_0, hns1_1, hns2_0, hns2_1, hns3_0, hns3_1, hsR_eq,
    stepWeight_fin2_zero, stepWeight_fin2_one, stepWeight_fin2_two, stepWeight_fin2_three]
  by_cases h0 : betas s0 < φ
  · have hα0 : stepAlpha n r φ (betas s0) ^ 2 = 1 :=
      (by dsimp only [stepAlpha]; rw [ite_eq_left h0, one_pow])
    have hd0_pos : 1 ≤ remStepsSlot n r φ (betas s0) := by
      by_contra hz; have hez : remStepsSlot n r φ (betas s0) = 0 := (by omega)
      linarith [(remStepsSlot_eq_zero_iff hr1 φ (betas s0)).1 hez]
    have hs0_post : remStepsSlot n r φ (postB s0) = remStepsSlot n r φ (betas s0) - 1 :=
      (by dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1, ite_eq_left h0])
    have hpb0 : postB s0 = betas s0 + 2 * halfAngleSet n r :=
      (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; rw [ite_eq_left h0])
    by_cases h1 : betas s1 < φ
    · have hα1 : stepAlpha n r φ (betas s1) ^ 2 = 1 :=
        (by dsimp only [stepAlpha]; rw [ite_eq_left h1, one_pow])
      have hd1_pos : 1 ≤ remStepsSlot n r φ (betas s1) := by
        by_contra hz; have hez : remStepsSlot n r φ (betas s1) = 0 := (by omega)
        linarith [(remStepsSlot_eq_zero_iff hr1 φ (betas s1)).1 hez]
      have hs1_post : remStepsSlot n r φ (postB s1) = remStepsSlot n r φ (betas s1) - 1 :=
        (by dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1, ite_eq_left h1])
      rw [hα0, hα1, hs0_post, hs1_post, Nat.cast_sub hd0_pos, Nat.cast_sub hd1_pos, Nat.cast_one,
        wmPotVal_sub_one]; exact le_of_eq (by ring)
    · have h1_ge : φ ≤ betas s1 := not_lt.1 h1; have hs1_z : remStepsSlot n r φ (betas s1) = 0 :=
        (remStepsSlot_eq_zero_iff hr1 φ (betas s1)).2 h1_ge
      have hs1_post : remStepsSlot n r φ (postB s1) = 0 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1]; simp only [h1,
          ↓reduceIte]
      set p1 : ℝ := 1 - lockedAlpha (betas s1) (halfAngleSet n r) ^ 2
      have hα1 : stepAlpha n r φ (betas s1) ^ 2 = 1 - p1 :=
        (by dsimp only [stepAlpha, p1]; simp only [h1, ↓reduceIte]; ring); have hp1_lo := (hlock_bds
        (betas s1) h1_ge (hbetas s1).2).1; rw [hα0, hα1, hs0_post, hs1_post, hs1_z, hpb0,
        Nat.cast_zero, wmPotVal_comm _ _ _ _ _ 0, wmPotVal_comm _ _ _ _ _ 0, wmPotVal_comm B dNatP
        (wFn (r - 1)) SN _ sReset]
      have hstep := warm2_stageGe3_single_locked_step hB hn hr2 hr1024 ht_lo ht_hi hat_lo hd1000
        hcSB hdP1 hat_prev hw hwP hbins hp1_lo (hbetas s0).1 h0 hc_cap (hs_cap s0)
      dsimp only at hstep; exact le_of_eq_of_le (by ring) hstep
  · have h0_ge : φ ≤ betas s0 := not_lt.1 h0; have hs0_z : remStepsSlot n r φ (betas s0) = 0 :=
      (remStepsSlot_eq_zero_iff hr1 φ (betas s0)).2 h0_ge
    have hs0_post : remStepsSlot n r φ (postB s0) = 0 := by
      dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1]; simp only [h0,
        ↓reduceIte]
    have hpb0 : postB s0 = betas s0 :=
      (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [h0, ↓reduceIte])
    set p0 : ℝ := 1 - lockedAlpha (betas s0) (halfAngleSet n r) ^ 2
    have hα0 : stepAlpha n r φ (betas s0) ^ 2 = 1 - p0 :=
      (by dsimp only [stepAlpha, p0]; simp only [h0, ↓reduceIte]; ring); obtain ⟨hp0_lo, hp0_hi⟩ :=
      hlock_bds (betas s0) h0_ge (hbetas s0).2; rw [Nat.cast_ofNat] at hp0_hi
    by_cases h1 : betas s1 < φ
    · have hα1 : stepAlpha n r φ (betas s1) ^ 2 = 1 :=
        (by dsimp only [stepAlpha]; rw [ite_eq_left h1, one_pow])
      have hs1_post : remStepsSlot n r φ (postB s1) = remStepsSlot n r φ (betas s1) - 1 :=
        (by dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1, ite_eq_left h1])
      have hpb1 : postB s1 = betas s1 + 2 * halfAngleSet n r :=
        (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; rw [ite_eq_left h1]); rw [hα0, hα1,
        hs0_post, hs1_post, hs0_z, hpb1, Nat.cast_zero]
      have hstep := warm2_stageGe3_single_locked_step hB hn hr2 hr1024 ht_lo ht_hi hat_lo hd1000
        hcSB hdP1 hat_prev hw hwP hbins hp0_lo (hbetas s1).1 h1 hc_cap (hs_cap s1)
      dsimp only at hstep; exact le_of_eq_of_le (by ring) hstep
    · have h1_ge : φ ≤ betas s1 := not_lt.1 h1; have hs1_z : remStepsSlot n r φ (betas s1) = 0 :=
        (remStepsSlot_eq_zero_iff hr1 φ (betas s1)).2 h1_ge
      have hs1_post : remStepsSlot n r φ (postB s1) = 0 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1]; simp only [h1,
          ↓reduceIte]
      have hpb1 : postB s1 = betas s1 :=
        (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [h1, ↓reduceIte])
      set p1 : ℝ := 1 - lockedAlpha (betas s1) (halfAngleSet n r) ^ 2
      have hα1 : stepAlpha n r φ (betas s1) ^ 2 = 1 - p1 :=
        (by dsimp only [stepAlpha, p1]; simp only [h1, ↓reduceIte]; ring)
      obtain ⟨hp1_lo, hp1_hi⟩ := hlock_bds (betas s1) h1_ge (hbetas s1).2
      rw [Nat.cast_ofNat] at hp1_hi; rw [hα0, hα1, hs0_post, hs1_post, hs0_z, hs1_z, hpb0, hpb1,
        Nat.cast_zero, wmPotVal_diag hd1 hw SN 0, zero_add]; simp only [sub_sub_cancel]
      set p_min : ℝ := 4 * ((tn : ℝ) / 100000) * (99999999 / 100000000) * √(r : ℝ) / SN
      have ht_pos : (0 : ℝ) < tn := Nat.cast_pos.2 (by omega); have hr_pos : (0 : ℝ) < r :=
        Nat.cast_pos.2 hr1; have hp_min_pos : 0 < p_min := (by dsimp only [p_min]; positivity)
      obtain ⟨h1q0_pos, h2p_rho, hprod_le⟩ := two_locked_one_sub_q0_bounds hp_min_pos hp0_lo hp1_lo
        hp0_hi hp1_hi; have huh_lock := of_decide_eq_true huh_lock_d; have hcb_lock :=
        of_decide_eq_true hcb_lock_d
      have hhit1 : wmPotVal B dNatP (wFn (r - 1)) SN sReset (remStepsSlot n (r - 1) φp
        (fuseNextAngle n r (betas s1)) : ℝ) ≤ ((hLock : ℝ) / 1000000000000) * SN :=
        wmPotVal_hit_single_le hdP1 hwP hSN_pos huLock_le_c hpsi_lock huh_lock hc_cap (hsLock_le
        (betas s1) h1_ge (hbetas s1).2)
      have hhit2 : wmPotVal B dNatP (wFn (r - 1)) SN (remStepsSlot n (r - 1) φp (fuseNextAngle n r
        (betas s0)) : ℝ) sReset ≤ ((hLock : ℝ) / 1000000000000) * SN := by
        rw [wmPotVal_comm]
        exact wmPotVal_hit_single_le hdP1 hwP hSN_pos huLock_le_c hpsi_lock huh_lock hc_cap
          (hsLock_le (betas s0) h0_ge (hbetas s0).2)
      set extra : ℕ := if hLock ≤ hBoth then hBoth - hLock else 0
      have hboth_le_ex : hBoth ≤ hLock + extra := by
        dsimp only [extra]; split_ifs
        · omega
        · omega
      have hhit3 : wmPotVal B dNatP (wFn (r - 1)) SN sReset sReset ≤ (((hLock : ℝ) + extra) /
        1000000000000) * SN := by
        refine (wmPotVal_hit_both_le hdP1 hwP hSN_pos hcb_lock hc_cap).trans ?_; have hex_r : (hBoth
          : ℝ) ≤ (hLock : ℝ) + extra := (by exact_mod_cast hboth_le_ex)
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hex_r (by norm_num)) hSN_pos.le
      have hp0_nn : 0 ≤ p0 := le_trans hp_min_pos.le hp0_lo
      have hp1_nn : 0 ≤ p1 := le_trans hp_min_pos.le hp1_lo
      have hp0_le1 : p0 ≤ 1 := hp0_hi.trans (by norm_num)
      have hp1_le1 : p1 ≤ 1 := hp1_hi.trans (by norm_num); set q0 : ℝ := (1 - p0) * (1 - p1)
      have hhit_sum : p0 * (1 - p1) * wmPotVal B dNatP (wFn (r - 1)) SN sReset (remStepsSlot n (r -
        1) φp (fuseNextAngle n r (betas s1)) : ℝ) + (1 - p0) * p1 * wmPotVal B dNatP (wFn (r - 1))
        SN (remStepsSlot n (r - 1) φp (fuseNextAngle n r (betas s0)) : ℝ) sReset + p0 * p1 *
        wmPotVal B dNatP (wFn (r - 1)) SN sReset sReset ≤ (1 - q0) * ((((hLock : ℝ) + (extra : ℝ) /
        200000000) / 1000000000000) * SN) := by
        have hm1 := mul_le_mul_of_nonneg_left hhit1 (mul_nonneg hp0_nn (sub_nonneg.2 hp1_le1))
        have hm2 := mul_le_mul_of_nonneg_left hhit2 (mul_nonneg (sub_nonneg.2 hp0_le1) hp1_nn)
        have hm3 := mul_le_mul_of_nonneg_left hhit3 (mul_nonneg hp0_nn hp1_nn); have hm_ex : (p0 *
          p1) * (((extra : ℝ) / 1000000000000) * SN) ≤ ((1 / 200000000) * (1 - q0)) * (((extra : ℝ)
          / 1000000000000) * SN) := mul_le_mul_of_nonneg_right hprod_le (by positivity)
        have hsum_w : p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1 = 1 - q0 := (by dsimp only [q0]; ring)
        linarith [hm1, hm2, hm3, hm_ex, show p0 * (1 - p1) * (((hLock : ℝ) / 1000000000000) * SN) +
              (1 - p0) * p1 * (((hLock : ℝ) / 1000000000000) * SN) +
              p0 * p1 * ((((hLock : ℝ) + extra) / 1000000000000) * SN) =
            (p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1) * (((hLock : ℝ) / 1000000000000) * SN) +
              (p0 * p1) * (((extra : ℝ) / 1000000000000) * SN) by ring,
          show (p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1) * (((hLock : ℝ) / 1000000000000) * SN) =
            (1 - q0) * (((hLock : ℝ) / 1000000000000) * SN) by rw [hsum_w],
          show (1 - q0) * (((hLock : ℝ) / 1000000000000) * SN) +
              ((1 / 200000000) * (1 - q0)) * (((extra : ℝ) / 1000000000000) * SN) =
            (1 - q0) * ((((hLock : ℝ) + (extra : ℝ) / 200000000) / 1000000000000) * SN) by ring]
      have hclick := clickRow_sound (m := 2) (n := n) (r := r) (by omega) hr1 ht_lo hclick_chk
      have hclick' : 1 / (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ))))) ≤ ((stepNum : ℝ) /
        1000000000000) * SN := (by simpa [p_min, SN] using hclick)
      have h1_le : 1 ≤ (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) := by
        have hden_pos : 0 < 2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ)))) :=
          (by have : (0 : ℝ) < 1 - 2 * (1 / (100000000 * (2 : ℝ))) := (by norm_num); positivity)
        calc (1 : ℝ) = (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ))))) *
              (1 / (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ)))))) := by
              field_simp [hden_pos.ne']
          _ ≤ (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) :=
              mul_le_mul h2p_rho hclick' (by positivity) h1q0_pos.le
      have hstep_w0 := of_decide_eq_true hstep_w0_d
      have hcomb_r : 200000000 * (hLock : ℝ) + extra ≤ 200000000 * ((wFn r 0 - stepNum : ℕ) : ℝ) :=
        (by exact_mod_cast of_decide_eq_true hlock_comb_d); rw [Nat.cast_sub hstep_w0] at hcomb_r
      have hcomb_sn : (((hLock : ℝ) + (extra : ℝ) / 200000000) / 1000000000000) * SN ≤ (((wFn r 0 :
        ℝ) - stepNum) / 1000000000000) * SN := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hSN_pos.le; have hm_comb :=
        mul_le_mul_of_nonneg_left hcomb_sn h1q0_pos.le; linarith [hhit_sum, h1_le, hm_comb, show (1
        - q0) * (((stepNum : ℝ) / 1000000000000) * SN) + (1 - q0) * ((((wFn r 0 : ℝ) - stepNum) /
        1000000000000) * SN) + q0 * (((wFn r 0 : ℝ) / 1000000000000) * SN) = ((wFn r 0 : ℝ) /
        1000000000000) * SN by ring]
/-! ## 5. Cell Certificate Bridge & Certified `m = 2, k ∈ {2, 4, 8, 16, 32}` Family -/
theorem wmStageIdx_tNum_bounds {B r : ℕ} {stFn : ℕ → M2StageScalar} {wFn : ℕ → ℕ → ℕ} {binFn : ℕ → ℕ
  → M2BinCert} (hr2 : 2 ≤ r) (hst : checkWarm2StageIdx B stFn wFn binFn (r - 2) = true) : 500 ≤
  (stFn r).tNum ∧ (stFn r).tNum ≤ 200000 := by
  have hr_sub : r - 2 + 2 = r := (by omega)
  dsimp only [checkWarm2StageIdx] at hst; rw [hr_sub] at hst; rcases hsr : stFn r with ⟨tn, phiHi,
    phiLo, cSelf, dNat, stepNum, cNat, ld⟩; rcases ld with ⟨tBfLo, tdHi, numU, uLock, psiLock,
    hLock, hBoth⟩; rw [hsr] at hst; simp only [Bool.and_eq_true, and_assoc] at hst; rcases hst with
    ⟨ht_lo, ht_hi, _⟩; exact ⟨of_decide_eq_true ht_lo, of_decide_eq_true ht_hi⟩
theorem wm_top_le_vanilla_of_rcNum {kIdx baseNat topR rcNum n : ℕ} (hkIdx : kIdx < 11) (hn : 100 ≤
  n) (hrc_nat : (baseNat + topR) * 10000000000 * sqrtMUpNat 1 ≤ rcNum * 785398163397 * harmSumPow2
  kIdx) : (((baseNat + topR : ℕ) : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) ≤ (((rcNum : ℚ≥0) /
  10000000000 : ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) * √((2 ^
  n : ℝ) / (2 : ℕ))) := by
  set m : ℕ := 2; set k : ℕ := 2 ^ kIdx; obtain ⟨hSN_ge, _⟩ := pow_two_bounds_100 hn
  have hSN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hSN_ge
  obtain ⟨hsm_pos_nat, hsm_sq⟩ := sqrtMUpNat_bounds (by omega : 1 < 11); have hsm_pos : (0 : ℝ) <
    sqrtMUpNat 1 := Nat.cast_pos.2 hsm_pos_nat; have hsqrtm_pos : (0 : ℝ) < √(m : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hsqrtm_le : √(m : ℝ) ≤ (sqrtMUpNat 1 : ℝ) / 1000000000000 := by
    refine sq_le_imp_le hsqrtm_pos.le (by positivity) ?_; rw [Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ m), div_pow, le_div_iff₀ (by norm_num)]
    have h2pow1 : (2 ^ 1 : ℕ) = m := rfl; rw [h2pow1] at hsm_sq
    have hcast : (m : ℝ) * 1000000000000 * 1000000000000 ≤ (sqrtMUpNat 1 : ℝ) * sqrtMUpNat 1 :=
      (by exact_mod_cast hsm_sq); linarith [hcast, show (m : ℝ) * (1000000000000 : ℝ) ^ 2 -
      (sqrtMUpNat 1 : ℝ) ^ 2 = (m : ℝ) * 1000000000000 * 1000000000000 - (sqrtMUpNat 1 : ℝ) *
      sqrtMUpNat 1 by ring]
  have hharm := harmSumPow2_le_sum hkIdx; have hpi : (785398163397 : ℝ) / 1000000000000 ≤ π / 4 :=
    (by linarith [Real.pi_gt_d20]); have hrc_cast : (((rcNum : ℚ≥0) / 10000000000 : ℚ≥0) : ℝ) =
    (rcNum : ℝ) / 10000000000 := (by push_cast; rfl)
  have hsn_cast : √((2 : ℝ) ^ n) = √(2 ^ n : ℝ) := (by norm_num); rw [hrc_cast, hsn_cast]
  have hcell_r : ((baseNat + topR : ℕ) : ℝ) * 10000000000 * sqrtMUpNat 1 ≤ (rcNum : ℝ) *
    785398163397 * harmSumPow2 kIdx := (by exact_mod_cast hrc_nat)
  have hcoeff : ((baseNat + topR : ℕ) : ℝ) / 1000000000000 ≤ ((rcNum : ℝ) / 10000000000) *
    ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat 1
    : ℝ) / 1000000000000) := by
    have hlhs : ((baseNat + topR : ℕ) : ℝ) / 1000000000000 = (((baseNat + topR : ℕ) : ℝ) *
      10000000000 * sqrtMUpNat 1) / (10000000000 * 1000000000000 * (sqrtMUpNat 1 : ℝ)) :=
      (by field_simp [hsm_pos.ne']); have hrhs : ((rcNum : ℝ) / 10000000000) * ((785398163397 : ℝ) /
      1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat 1 : ℝ) /
      1000000000000) = ((rcNum : ℝ) * 785398163397 * harmSumPow2 kIdx) / (10000000000 *
      1000000000000 * (sqrtMUpNat 1 : ℝ)) := (by field_simp [hsm_pos.ne']); rw [hlhs, hrhs]
    exact div_le_div_of_nonneg_right hcell_r (by positivity)
  have hm_prod : ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) ≤
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) := mul_le_mul hpi hharm (by positivity)
    (by linarith [Real.pi_pos])
  have hnum_le : ((rcNum : ℝ) / 10000000000) * ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2
    kIdx : ℝ) / 1000000000000) ≤ ((rcNum : ℝ) / 10000000000) * ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 /
    √(r : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left hm_prod (by positivity : 0 ≤ (rcNum : ℝ) / 10000000000)
    linarith [hm, show ((rcNum : ℝ) / 10000000000) * (((785398163397 : ℝ) / 1000000000000) *
      ((harmSumPow2 kIdx : ℝ) / 1000000000000)) = ((rcNum : ℝ) / 10000000000) * ((785398163397 : ℝ)
      / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) by ring]
  have hmono : ((rcNum : ℝ) / 10000000000) * ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2
    kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat 1 : ℝ) / 1000000000000) ≤ ((rcNum : ℝ) / 10000000000)
    * ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ))) / √(m : ℝ) := (div_le_div_of_nonneg_right
    hnum_le (by positivity)).trans (div_le_div_of_nonneg_left (mul_nonneg (by positivity)
    (mul_nonneg (by linarith [Real.pi_pos]) (Finset.sum_nonneg fun _ _ ↦ by positivity))) hsqrtm_pos
    hsqrtm_le); rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n) m]
  calc (((baseNat + topR : ℕ) : ℝ) / 1000000000000) * √(2 ^ n : ℝ) ≤ (((rcNum : ℝ) / 10000000000) *
        ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ))) / √(m : ℝ)) * √(2 ^ n : ℝ) :=
        mul_le_mul_of_nonneg_right (hcoeff.trans hmono) hSN_pos.le
    _ = ((rcNum : ℝ) / 10000000000) *
          ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * (√(2 ^ n : ℝ) / √(m : ℝ))) := by
        ring
theorem validCswapWarmM2Potential_of_checkWarm2CellCert {B : ℕ} {stFn : ℕ → M2StageScalar} {wFn : ℕ
  → ℕ → ℕ} {binFn : ℕ → ℕ → M2BinCert} {kIdx topR rcNum n : ℕ} (hcell : checkWarm2CellCert B stFn
  wFn binFn kIdx topR rcNum = true) (hn : 100 ≤ n) : ValidCswapWarmM2Potential (phiFnOfWmSt stFn)
  (fun _ ↦ 5 / 4) n (2 ^ kIdx) (wmPotential B stFn wFn n) ∧ wmPotential B stFn wFn n (2 ^ kIdx) (fun
  _ ↦ halfAngleSet n (2 ^ kIdx)) ≤ (((rcNum : ℚ≥0) / 10000000000 : ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈
  Finset.Icc (1 : ℕ) (2 ^ kIdx), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ))) := by
  dsimp only [checkWarm2CellCert] at hcell; set k : ℕ := 2 ^ kIdx; set phiFn := phiFnOfWmSt stFn;
    set Φ := wmPotential B stFn wFn n; simp only [Bool.and_eq_true, and_assoc] at hcell
  rcases hcell with ⟨hB_d, hk1_d, hk11_d, hall_st, htop1_d, htail_k⟩
  have hB := of_decide_eq_true hB_d; have hkIdx1 := of_decide_eq_true hk1_d; have hkIdx11 :=
    of_decide_eq_true hk11_d; have htop1 := of_decide_eq_true htop1_d
  have hk2 : 2 ≤ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ kIdx := Nat.pow_le_pow_right (by positivity) hkIdx1
  have hk1024 : k ≤ 1024 := by
    calc 2 ^ kIdx ≤ 2 ^ 10 := Nat.pow_le_pow_right (by positivity) (by omega)
      _ = 1024 := by norm_num
  have ht_bds : ∀ r, 2 ≤ r → r ≤ k → 500 ≤ (stFn r).tNum ∧ (stFn r).tNum ≤ 200000 := fun r hr2 hrk ↦
    wmStageIdx_tNum_bounds hr2 (of_allRange hall_st (by omega : r - 2 < k - 1)); have h54_lt : (5 /
    4 : ℝ) < π / 2 := tan_five_div_four_le_five.2; refine ⟨?_, ?_⟩
  · refine
      { nonneg := fun r _ _ betas _ ↦ by
          dsimp only [Φ, wmPotential]; split_ifs
          · exact cswapWarmR1Cost1_nonneg n betas
          · exact wmPotVal_nonneg (Real.sqrt_nonneg _) (by positivity) (by positivity)
        phi_lb := fun r hr2 hrk ↦
          (phi_and_lockedAlpha_bounds_fuse_100 (m := 2) (by omega) (by omega) hn
            (by omega) (hrk.trans hk1024) (ht_bds r hr2 hrk).1 (ht_bds r hr2 hrk).2).1
        ub_lb := fun r hr1 hrk ↦ by
          split_ifs with hr_eq1
          · rcases halfAngleSet_bounds_100 hn (by omega : 1 ≤ 1) (by omega : 1 ≤ 1024) with ⟨_, _,
              hθ1_13, -⟩; linarith [hθ1_13]
          · have hr2 : 2 ≤ r := (by omega); exact (phi_and_lockedAlpha_bounds_fuse_100 (m := 2)
              (by omega) (by omega) hn hr1 (hrk.trans hk1024) (ht_bds r hr2 hrk).1 (ht_bds r hr2
              hrk).2).2.1
        ub_lt := fun _ _ _ ↦ h54_lt
        ub_fuse := fun r hr2 hrk ↦ by
          rcases halfAngleSet_bounds_100 hn (by omega : 1 ≤ r) (hrk.trans hk1024) with ⟨_, _, hθ_13,
            -⟩
          exact fuseNextAngle_le_self hr2 (two_mul_le_pow_100 hn (hrk.trans hk1024))
            (by linarith [hθ_13]) h54_lt.le
        base1_le := fun _ betas _ ↦ by dsimp only [Φ, wmPotential]; simp
        step_le := fun r hr2 hrk betas hbetas ↦ ?_ }
    by_cases hr3 : 3 ≤ r
    · exact warm2_stageGe3_step hB hn hr3 (hrk.trans hk1024) (of_allRange hall_st
        (by omega : r - 2 < k - 1)) (of_allRange hall_st (by omega : r - 3 < k - 1)) betas hbetas
    · have hr_eq2 : r = 2 := (by omega); subst hr_eq2; exact warm2_stage2_step hB hn (of_allRange
        hall_st (by omega : 0 < k - 1)) betas hbetas
  · have hst_k := of_allRange hall_st (by omega : k - 2 < k - 1)
    dsimp only [checkWarm2StageIdx] at hst_k; rw [show k - 2 + 2 = k by omega] at hst_k
    rcases hsk : stFn k with ⟨tK, phiHiK, phiLoK, cSelfK, dNatK, stepNumK, cNatK, ldK⟩
    rcases ldK with ⟨_, _, _, _, _, _, _⟩; rw [hsk] at hst_k htail_k; simp only [Bool.and_eq_true,
      and_assoc] at hst_k htail_k; rcases hst_k with ⟨htK_lo, htK_hi, hatK, _, _, _, hdK1000, _, _,
      hslK, _⟩; have hdK1 : 1 ≤ dNatK := (by have := of_decide_eq_true hdK1000; omega); have hwK :=
      knotSlope_of_allRange hslK; have hφk : phiFnOfWmSt stFn k = Real.arctan ((tK : ℝ) / 100000) :=
      (by dsimp only [phiFnOfWmSt]; rw [hsk])
    have hrem_k := remStepsSlot_halfAngleSet_le_of_atan200Hi_sq hn (by omega) hk1024
      (of_decide_eq_true htK_lo) (of_decide_eq_true htK_hi) hatK htop1 (of_decide_eq_true htail_k.1)
    have hΦk : Φ k (fun _ : Fin 2 ↦ halfAngleSet n k) ≤ (((wFn k 0 + topR : ℕ) : ℝ) / 1000000000000)
      * √((2 : ℝ) ^ n) := by
      dsimp only [Φ, wmPotential]; rw [ite_eq_right (by omega : ¬ k ≤ 1)]; dsimp only [wmStagePot]
      have hdK_eq : (stFn k).dNat = dNatK := (by rw [hsk]); rw [hdK_eq, hφk, wmPotVal_diag hdK1 hwK
        √((2 : ℝ) ^ n) _, Nat.cast_add]; linarith only [hrem_k, show ((topR : ℝ) / 1000000000000) *
        √((2 : ℝ) ^ n) + ((wFn k 0 : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) = (((wFn k 0 : ℝ) + topR)
        / 1000000000000) * √((2 : ℝ) ^ n) by ring]
    exact hΦk.trans (wm_top_le_vanilla_of_rcNum hkIdx11 hn (of_decide_eq_true htail_k.2))
/-- Dyadic exponent `kIdx` (`k = 2 ^ kIdx`) for `k ∈ {2, 4, 8, 16, 32}`, or `0` otherwise. -/
def wmKIdx (k : ℕ) : ℕ :=
  if k == 2 then 1
  else if k == 4 then 2
  else if k == 8 then 3
  else if k == 16 then 4
  else if k == 32 then 5
  else 0
def validCellWarm2 (m k : ℕ) : Bool :=
  m == 2 && (k == 2 || k == 4 || k == 8 || k == 16)
def wmCellSt (kIdx : ℕ) : ℕ → M2StageScalar :=
  match kIdx with
  | 1 => wmSt_1
  | 2 => wmSt_2
  | 3 => wmSt_3
  | 4 => wmSt_4
  | _ => wmSt_1
def wmCellW (kIdx : ℕ) : ℕ → ℕ → ℕ :=
  match kIdx with
  | 1 => wmW_1
  | 2 => wmW_2
  | 3 => wmW_3
  | 4 => wmW_4
  | _ => wmW_1
def wmCellBin (kIdx : ℕ) : ℕ → ℕ → M2BinCert :=
  match kIdx with
  | 1 => wmBin_1
  | 2 => wmBin_2
  | 3 => wmBin_3
  | 4 => wmBin_4
  | _ => wmBin_1
/-- Per-cell piecewise-linear bin count `B` across `kIdx ∈ {1..5}` (`128` at `kIdx = 5`). -/
def wmCellB (kIdx : ℕ) : ℕ :=
  match kIdx with
  | 1 => 128
  | 2 => 1200
  | 3 => 576
  | 4 => 128
  | _ => 128
/-- Certified top-stage ramp bound `topR` (`10^12` scale) for `kIdx ∈ {1..5}`. -/
def topRampWarm2 (kIdx : ℕ) : ℕ :=
  match kIdx with
  | 1 => 314244595243
  | 2 => 195623691551
  | 3 => 135204382171
  | 4 => 96604110174
  | 5 => 68878469409
  | _ => 0
/-- Certified numerator `rcNum` (`relCost = rcNum / 10^10`) for `kIdx ∈ {1..5}`. -/
def relCostNumWarm2 (kIdx : ℕ) : ℕ :=
  match kIdx with
  | 1 => 6765864022
  | 2 => 6468190582
  | 3 => 6243042174
  | 4 => 6105043326
  | 5 => 6009023920
  | _ => 10000000000
/-- Claimed relative cost `ℚ≥0` on `(m = 2, k ∈ {2, 4, 8, 16, 32})`. -/
def relCostWarm2 (m k : ℕ) : ℚ≥0 :=
  if m == 2 then (relCostNumWarm2 (wmKIdx k) : ℚ≥0) / 10000000000 else 1
theorem cert_warm2_by_kIdx {kIdx : ℕ} (hk : kIdx = 1 ∨ kIdx = 2 ∨ kIdx = 3 ∨ kIdx = 4) :
  checkWarm2CellCert (wmCellB kIdx) (wmCellSt kIdx) (wmCellW kIdx) (wmCellBin kIdx) kIdx
  (topRampWarm2 kIdx) (relCostNumWarm2 kIdx) = true := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact cert_warm2Cell_1
  · exact cert_warm2Cell_2
  · exact cert_warm2Cell_3
  · exact cert_warm2Cell_4
attribute [irreducible] wmCellSt wmCellW wmCellBin
noncomputable def findAllWarm2M2Circuit {Var : Type} (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  match m with
  | 2 =>
      if 100 ≤ n ∧ validCellWarm2 2 k = true then
        cswapWarmM2FindAllCircuit res (phiFnOfWmSt (wmCellSt (wmKIdx k))) n k
      else
        findAllLockCircuit res n 2 k
  | m =>
      findAllLockCircuit res n m k
theorem validCellWarm2_cases {m k : ℕ} (hmk : validCellWarm2 m k = true) : m = 2 ∧ ((k = 2 ∧ wmKIdx
  k = 1) ∨ (k = 4 ∧ wmKIdx k = 2) ∨ (k = 8 ∧ wmKIdx k = 3) ∨ (k = 16 ∧ wmKIdx k = 4)) := by
  simp only [validCellWarm2, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hmk; refine ⟨hmk.1,
    ?_⟩; rcases hmk.2 with ((rfl | rfl) | rfl) | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
theorem findAllWarm2M2_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ} (hn : 1 ≤
  n) (hmk : validCellWarm2 m k = true) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))} (hS : S ∈
  (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) : ⦃ (⊤ : CQAssertion (Store Var) (2 ^
    findAllQubits n
  m k)) ⦄ (QProg.qSet ;; (findAllWarm2M2Circuit res n m k).compile QProg.qAssign
  (parallelMarkingOracle m S)) ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S) ⦄ := by
  cases Nat.eq_zero_or_pos n with
  | inl hn0 => exact absurd (hn0 ▸ hn) (by omega)
  | inr _ =>
  obtain ⟨rfl, hk_cases⟩ := validCellWarm2_cases hmk; have hScard : S.card = k :=
    (Finset.mem_powersetCard.1 hS).2; dsimp only [findAllWarm2M2Circuit]; by_cases hc : 100 ≤ n ∧
    validCellWarm2 2 k = true
  · rw [ite_eq_left hc]; rcases hk_cases with ⟨rfl, hkI⟩ | ⟨rfl, hkI⟩ | ⟨rfl, hkI⟩ | ⟨rfl, hkI⟩
    · rw [hkI]
      obtain ⟨hΦ, hB⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inl
        rfl)) hc.1; have hB_nn : 0 ≤ (((relCostNumWarm2 1 : ℚ≥0) / 10000000000 : ℚ≥0) : ℝ) * ((π /
        4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ 1), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ))) :=
        mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by linarith [Real.pi_pos])
        (Finset.sum_nonneg fun _ _ ↦ by positivity)) (Real.sqrt_nonneg _))
      exact (cswapWarmM2FindAllProgram_correctness_and_costBound res hc.1 (by omega) (by omega) hΦ
        hScard (B := ⟨_, hB_nn⟩) hB).1
    · rw [hkI]
      obtain ⟨hΦ, hB⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inr
        (Or.inl rfl))) hc.1
      have hB_nn : 0 ≤ (((relCostNumWarm2 2 : ℚ≥0) / 10000000000 : ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈
        Finset.Icc (1 : ℕ) (2 ^ 2), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ))) := mul_nonneg
        (by positivity) (mul_nonneg (mul_nonneg (by linarith [Real.pi_pos]) (Finset.sum_nonneg fun _
        _ ↦ by positivity)) (Real.sqrt_nonneg _))
      exact (cswapWarmM2FindAllProgram_correctness_and_costBound res hc.1 (by omega) (by omega) hΦ
        hScard (B := ⟨_, hB_nn⟩) hB).1
    · rw [hkI]
      obtain ⟨hΦ, hB⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inr
        (Or.inr (Or.inl rfl)))) hc.1; have hB_nn : 0 ≤ (((relCostNumWarm2 3 : ℚ≥0) / 10000000000 :
        ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ 3), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2
        : ℕ))) := mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by linarith [Real.pi_pos])
        (Finset.sum_nonneg fun _ _ ↦ by positivity)) (Real.sqrt_nonneg _))
      exact (cswapWarmM2FindAllProgram_correctness_and_costBound res hc.1 (by omega) (by omega) hΦ
        hScard (B := ⟨_, hB_nn⟩) hB).1
    · rw [hkI]
      obtain ⟨hΦ, hB⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inr
        (Or.inr (Or.inr rfl)))) hc.1; have hB_nn : 0 ≤ (((relCostNumWarm2 4 : ℚ≥0) / 10000000000 :
        ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ 4), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2
        : ℕ))) := mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by linarith [Real.pi_pos])
        (Finset.sum_nonneg fun _ _ ↦ by positivity)) (Real.sqrt_nonneg _))
      exact (cswapWarmM2FindAllProgram_correctness_and_costBound res hc.1 (by omega) (by omega) hΦ
        hScard (B := ⟨_, hB_nn⟩) hB).1
  · rw [ite_eq_right hc]
    have hgrid : isGridCell 2 k = true := by
      rcases hk_cases with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
    exact findAllLock_correctness res hgrid hkN hS
theorem findAllWarm2M2_costBound_uniform {Var : Type} [DecidableEq Var] (res : Var) {m k n : ℕ} (hmk
  : validCellWarm2 m k = true) (hn : 100 ≤ n) : ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0, (∀ S ∈
  (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, CostBound (CostModel.ofEmbeddedOracle
  (parallelMarkingOracle m S)) (QProg.qSet ;; (findAllWarm2M2Circuit res n m k).compile
  QProg.qAssign (parallelMarkingOracle m S)) (q S)) ∧ (∑ S ∈ (Finset.univ : Finset (Fin (2 ^
  n))).powersetCard k, (q S : ℝ)) / ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
  ((relCostWarm2 m k : ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) /
  m)) := by
  obtain ⟨rfl, hk_cases⟩ := validCellWarm2_cases hmk
  have hc : 100 ≤ n ∧ validCellWarm2 2 k = true := ⟨hn, hmk⟩; set bound : ℝ := ((relCostWarm2 2 k :
    ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ)))
  have hbound_nn : 0 ≤ bound := mul_nonneg (by positivity) (mul_nonneg (mul_nonneg
    (by linarith [Real.pi_pos]) (Finset.sum_nonneg fun _ _ ↦ by positivity)) (Real.sqrt_nonneg _))
  let B : ℝ≥0 := ⟨bound, hbound_nn⟩; refine ⟨fun _ ↦ B, fun S hS ↦ ?_, ?_⟩
  · have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2; dsimp only [findAllWarm2M2Circuit]
    rw [ite_eq_left hc]; rcases hk_cases with ⟨rfl, hkI⟩ | ⟨rfl, hkI⟩ | ⟨rfl, hkI⟩ | ⟨rfl, hkI⟩
    · rw [hkI]
      obtain ⟨hΦ, hB⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inl
        rfl)) hn; exact (cswapWarmM2FindAllProgram_correctness_and_costBound res hn (by omega)
        (by omega) hΦ hScard (B := B) hB).2
    · rw [hkI]
      obtain ⟨hΦ, hB⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inr
        (Or.inl rfl))) hn; exact (cswapWarmM2FindAllProgram_correctness_and_costBound res hn
        (by omega) (by omega) hΦ hScard (B := B) hB).2
    · rw [hkI]
      obtain ⟨hΦ, hB⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inr
        (Or.inr (Or.inl rfl)))) hn; exact (cswapWarmM2FindAllProgram_correctness_and_costBound res
        hn (by omega) (by omega) hΦ hScard (B := B) hB).2
    · rw [hkI]
      obtain ⟨hΦ, hB⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inr
        (Or.inr (Or.inr rfl)))) hn; exact (cswapWarmM2FindAllProgram_correctness_and_costBound res
        hn (by omega) (by omega) hΦ hScard (B := B) hB).2
  · rw [Finset.sum_const, nsmul_eq_mul]; by_cases h0 : (((Finset.univ : Finset (Fin (2 ^
      n))).powersetCard k).card : ℝ) = 0
    · rw [h0, zero_mul, zero_div]; exact hbound_nn
    · rw [mul_div_cancel_left₀ _ h0]; exact le_rfl
end QuantumComputation.Specs.GroverFindAll.Warm2
namespace QuantumComputation.Specs.GroverFindAll
open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal QHLExpectation
/-- Computable cost profile for the 5 certified `m = 2` CSWAP warm-readout cells (`n ≥
  100`). -/
def warm2Profile : FindAllCostProfile where
  validCell := Warm2.validCellWarm2
  relCost := Warm2.relCostWarm2
  n0 _ _ := 100
/-- Composable `ValidFindAllFamily` instance for `Warm2M2MultiStage` (5 cells). -/
theorem validFamily_warm2 {Var : Type} [DecidableEq Var] (res : Var) :
    ValidFindAllFamily res warm2Profile (Warm2.findAllWarm2M2Circuit res) where
  correctness hn _hgrid hvalid hkN hS := Warm2.findAllWarm2M2_correctness res hn hvalid hkN hS
  costBound_uniform _hgrid hvalid _n hn _hkN := Warm2.findAllWarm2M2_costBound_uniform res hvalid hn
end QuantumComputation.Specs.GroverFindAll
end
public section
namespace QuantumComputation.Specs.GroverFindAll.Warm2
open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal QHLExpectation
open PipeFuseCert
  (withForcedNat_eq allRange of_allRange
   checkClickRow checkFuseDriftCert
   harmSumPow2 sqrtMUpNat sq_le_imp_le pade56_le_arctan
   fuseDriftCert_sound clickRow_sound harmSumPow2_le_sum sqrtMUpNat_bounds)
open PipeFuseM2Cert
  (M2BinCert M2StageScalar checkPsiHi minDiffNat checkM2KnotSlope
   psiPiecewise psiPiecewise_nonneg psiPiecewise_mono psiPiecewise_sub_le
   psiPiecewise_knot checkPsiHi_sound exists_bin_of_le psiPiecewise_step_ge_minDiff)
open PipeFuse
  (pow_two_bounds_100 halfAngleSet_bounds_100 two_mul_le_pow_100
   tan_five_div_four_le_five phi_and_lockedAlpha_bounds_fuse_100)
/-! ### Private Warm-Entry `r = 2` Jordan-Block Checkers & Soundness (`m = 2`) -/
private structure WarmJP01Row where
  sLo : ℕ
  sHi : ℕ
  c0Lo : ℕ
  c0Hi : ℕ
  tau1_12 : ℕ
  tau2_12 : ℕ
  rawV2_12 : ℕ
private abbrev SNat : Type := Bool × ℕ
private abbrev SNIVal : Type := SNat × SNat
private abbrev jp01Scale : ℕ := 1000000000000000
private def withForcedSNat {α : Type} (a : SNat) (k : SNat → α) : α :=
  Bool.rec
    (PipeFuseCert.withForcedNat a.2 fun m => k (false, m))
    (PipeFuseCert.withForcedNat a.2 fun m => k (true, m))
    a.1
private def withForcedSNIVal {α : Type} (iv : SNIVal) (k : SNIVal → α) : α :=
  withForcedSNat iv.1 fun lo =>
  withForcedSNat iv.2 fun hi =>
    k (lo, hi)
private def snZero : SNat := (false, 0)
private def snScaleOne : SNat := (false, jp01Scale)
private def snNeg (a : SNat) : SNat := (!a.1, a.2)
private def snAdd (a b : SNat) : SNat :=
  cond (a.1 == b.1)
    (a.1, a.2 + b.2)
    (cond (Nat.ble b.2 a.2) (a.1, a.2 - b.2) (b.1, b.2 - a.2))
private def snSub (a b : SNat) : SNat := snAdd a (snNeg b)
private def snMul (a b : SNat) : SNat := (bne a.1 b.1, a.2 * b.2)
private def snScaleNat (c : ℕ) (a : SNat) : SNat := (a.1, c * a.2)
private def _nEq : ℕ → ℕ → Bool
  | 0, 0 => true
  | a + 1, b + 1 => _nEq a b
  | _, _ => false
private theorem _nEq_eq {a b : ℕ} : _nEq a b = true ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp [_nEq, *]
@[local simp] private theorem _nEq_self (a : ℕ) : _nEq a a = true := _nEq_eq.mpr rfl
private def snLe (a b : SNat) : Bool :=
  match a, b with
  | (false, ma), (false, mb) => Nat.ble ma mb
  | (true, ma), (true, mb) => Nat.ble mb ma
  | (true, _), (false, _) => true
  | (false, ma), (true, mb) => _nEq ma 0 && _nEq mb 0
private def snMin (a b : SNat) : SNat := cond (snLe a b) a b
private def snMax (a b : SNat) : SNat := cond (snLe a b) b a
private def snMaxZero (a : SNat) : SNat := cond a.1 snZero a
private def snDivFloor (a : SNat) (d : ℕ) : SNat :=
  cond a.1 (true, (a.2 + d - 1) / d) (false, a.2 / d)
private def snDivCeil (a : SNat) (d : ℕ) : SNat := snNeg (snDivFloor (snNeg a) d)
private def snAddIV (x y : SNIVal) : SNIVal :=
  withForcedSNat (snAdd x.1 y.1) fun lo =>
  withForcedSNat (snAdd x.2 y.2) fun hi => (lo, hi)
private def snSubIV (x y : SNIVal) : SNIVal :=
  withForcedSNat (snSub x.1 y.2) fun lo =>
  withForcedSNat (snSub x.2 y.1) fun hi => (lo, hi)
private def snScaleNatIV (c : ℕ) (x : SNIVal) : SNIVal :=
  withForcedSNat (snScaleNat c x.1) fun lo =>
  withForcedSNat (snScaleNat c x.2) fun hi => (lo, hi)
private def snMulIV (x y : SNIVal) : SNIVal :=
  withForcedSNat (snMul x.1 y.1) fun p1 =>
  withForcedSNat (snMul x.1 y.2) fun p2 =>
  withForcedSNat (snMul x.2 y.1) fun p3 =>
  withForcedSNat (snMul x.2 y.2) fun p4 =>
  withForcedSNat (snDivFloor (snMin (snMin p1 p2) (snMin p3 p4)) jp01Scale) fun lo =>
  withForcedSNat (snDivCeil (snMax (snMax p1 p2) (snMax p3 p4)) jp01Scale) fun hi =>
    (lo, hi)
private def snSqIV (x : SNIVal) : SNIVal :=
  withForcedSNat (snMul x.1 x.1) fun p1 =>
  withForcedSNat (snMul x.2 x.2) fun p2 =>
  withForcedSNat
    (cond (snLe x.1 snZero && snLe snZero x.2)
  snZero
  (snDivFloor (snMin p1 p2) jp01Scale)) fun lo =>
  withForcedSNat (snDivCeil (snMax p1 p2) jp01Scale) fun hi =>
    (lo, hi)
private def snTrigBase (u : SNIVal) : SNIVal × SNIVal :=
  let bS : SNat := snScaleOne
  withForcedSNat (snDivCeil (snMul u.2 u.2) jp01Scale) fun uh2 =>
  withForcedSNat (snDivFloor (snMul u.1 u.1) jp01Scale) fun ul2 =>
  withForcedSNat (snDivCeil (snMul uh2 uh2) jp01Scale) fun uh4 =>
  withForcedSNat (snSub bS (snDivCeil (snMul u.2 u.2) (2 * jp01Scale))) fun cLo =>
  withForcedSNat
    (snAdd (snSub bS (snDivFloor (snMul u.1 u.1) (2 * jp01Scale))) (snDivCeil uh4 24))
    fun cHi =>
  withForcedSNat (snDivCeil (snMul uh2 u.2) jp01Scale) fun uh3 =>
  withForcedSNat (snDivFloor (snMul ul2 u.1) jp01Scale) fun ul3 =>
  withForcedSNat (snDivCeil (snMul uh4 u.2) jp01Scale) fun uh5 =>
  withForcedSNat (snMaxZero (snSub u.1 (snDivCeil uh3 6))) fun sLo =>
  withForcedSNat (snAdd (snSub u.2 (snDivFloor ul3 6)) (snDivCeil uh5 120)) fun sHi =>
    ((cLo, cHi), (sLo, sHi))
private def snDoubleAngleIter : ℕ → SNIVal × SNIVal → SNIVal × SNIVal
  | 0, cs => cs
  | k + 1, (c, s) =>
      withForcedSNIVal (snSubIV (snSqIV c) (snSqIV s)) fun c' =>
      withForcedSNIVal (snScaleNatIV 2 (snMulIV s c)) fun s' =>
        snDoubleAngleIter k (c', s')
private def snTrig (x : SNIVal) : SNIVal × SNIVal :=
  withForcedSNat (snDivFloor x.1 1024) fun uLo =>
  withForcedSNat (snDivCeil x.2 1024) fun uHi =>
    snDoubleAngleIter 10 (snTrigBase (uLo, uHi))
private def jp01Sq2Lo : ℕ := 1414213562373095
private def jp01Sq2Hi : ℕ := 1414213562373096
private def jp01Sq3Lo : ℕ := 1732050807568877
private def jp01Sq3Hi : ℕ := 1732050807568878
private def jp01Sq6Lo : ℕ := 2449489742783178
private def jp01Sq6Hi : ℕ := 2449489742783179
private def jp01Sq2IV : SNIVal := ((false, jp01Sq2Lo), (false, jp01Sq2Hi))
private def jp01Sq3IV : SNIVal := ((false, jp01Sq3Lo), (false, jp01Sq3Hi))
private def jp01Sq6IV : SNIVal := ((false, jp01Sq6Lo), (false, jp01Sq6Hi))
private def jp01AngleIV (wIV : SNIVal) (tau12 : ℕ) : SNIVal :=
  cond (_nEq tau12 0)
    (snZero, snZero)
    (
    let omIV : SNIVal := snScaleNatIV 2 wIV
    let tIV : SNIVal := ((false, tau12 * 1000 - 1), (false, tau12 * 1000 + 1))
    withForcedSNIVal (snMulIV omIV tIV) fun thRaw =>
    withForcedSNat (snMaxZero (snSub thRaw.1 (false, 1))) fun lo =>
    withForcedSNat (snAdd thRaw.2 (false, 1)) fun hi =>
      (lo, hi)
    )
private def jp01EvalInterval (sLo sHi c0Lo c0Hi tau1_12 tau2_12 : ℕ) : Bool × (ℕ × ℕ × ℕ) :=
  cond (!(Nat.ble tau1_12 4000000000000 && Nat.ble tau2_12 4000000000000))
    (false, (0, 0, 0))
    (
    withForcedSNIVal (jp01AngleIV jp01Sq6IV tau1_12) fun th1IV =>
    withForcedSNIVal (jp01AngleIV jp01Sq2IV tau2_12) fun th2IV =>
    let cap : SNat := (false, 1024 * jp01Scale)
    cond (!(snLe th1IV.2 cap && snLe th2IV.2 cap))
      (false, (0, 0, 0))
      (
      let cs1 := snTrig th1IV
      let cs2 : SNIVal × SNIVal := cond (Nat.blt 0 tau2_12) (snTrig th2IV) ((snScaleOne,
        snScaleOne), (snZero, snZero))
      let sIV : SNIVal := ((false, sLo), (false, sHi))
      let c0IV : SNIVal := ((false, c0Lo), (false, c0Hi))
      let invSq2 : SNIVal := (snDivFloor jp01Sq2IV.1 2, snDivCeil jp01Sq2IV.2 2)
      withForcedSNIVal (snMulIV sIV invSq2) fun c1IV =>
      let oneIV : SNIVal := (snScaleOne, snScaleOne)
      let numQ : SNIVal := snAddIV oneIV (snScaleNatIV 2 cs1.1)
      let kQ02 : SNIVal := (snDivFloor numQ.1 3, snDivCeil numQ.2 3)
      let kS23 : SNIVal := (snDivFloor jp01Sq6IV.1 3, snDivCeil jp01Sq6IV.2 3)
      let kR23 : SNIVal := (snDivFloor jp01Sq2IV.1 3, snDivCeil jp01Sq2IV.2 3)
      let kR13 : SNIVal := (snDivFloor jp01Sq3IV.1 3, snDivCeil jp01Sq3IV.2 3)
      withForcedSNIVal
        (snSubIV (snMulIV kQ02 c0IV) (snMulIV (snMulIV kS23 cs1.2) c1IV)) fun x0IV =>
      withForcedSNIVal
        (snAddIV (snMulIV (snMulIV kS23 cs1.2) c0IV) (snMulIV cs1.1 c1IV)) fun x1IV =>
      let oneSubC1 : SNIVal := snSubIV oneIV cs1.1
      withForcedSNIVal
        (snAddIV (snMulIV (snMulIV kR23 oneSubC1) c0IV) (snMulIV (snMulIV kR13 cs1.2) c1IV))
        fun x2IV =>
      let f0IV : SNIVal := (snSub x0IV.1 (false, 1), snAdd x0IV.2 (false, 1))
      withForcedSNIVal (snAddIV (snMulIV cs2.2 x1IV) (snMulIV cs2.1 x2IV)) fun y2IV =>
      let f2IV : SNIVal := (snSub y2IV.1 (false, 1), snAdd y2IV.2 (false, 1))
      withForcedSNIVal (snSqIV f0IV) fun p0Sq =>
      withForcedSNIVal (snSqIV f2IV) fun p2Sq =>
      cond (!(snLe snZero p0Sq.2))
        (false, (0, 0, 0))
        (
        let p0Hi15 : ℕ := cond p0Sq.2.1 0 p0Sq.2.2
        let p2Lo15 : ℕ := (snMaxZero p2Sq.1).2
        let sLoPad : ℕ := sLo - 1
        let w0Hi15 : ℕ := jp01Scale - (sLoPad * sLoPad) / (2 * jp01Scale)
        (true, (p0Hi15, p2Lo15, w0Hi15))
        )
      )
    )
private def checkWarmJP01RowAt (cv2 : ℕ) (rows : ℕ → WarmJP01Row) (v2m : ℕ → ℕ) (idx : ℕ) : Bool :=
  match rows idx with
  | ⟨sLo, sHi, c0Lo, c0Hi, t1, t2, rawV2⟩ =>
    Nat.ble sLo sHi && Nat.ble c0Lo c0Hi &&
    Nat.ble (512 * sLo) (idx * jp01Scale) &&
    Nat.ble ((idx + 1) * jp01Scale) (512 * sHi) &&
    PipeFuseCert.withForcedNat
      ((512 * 512 - (idx + 1) * (idx + 1)) * jp01Scale * jp01Scale) fun numLo =>
    PipeFuseCert.withForcedNat
      ((512 * 512 - idx * idx) * jp01Scale * jp01Scale) fun numHi =>
    Nat.ble (512 * 512 * c0Lo * c0Lo) numLo &&
    Nat.ble numHi (512 * 512 * c0Hi * c0Hi) &&
    Nat.ble 1 rawV2 &&
    match jp01EvalInterval sLo sHi c0Lo c0Hi t1 t2 with
    | (ok, (p0Hi, p2Lo, w0Hi)) =>
      ok &&
      Nat.ble (p0Hi + 1 + p2Lo) jp01Scale &&
      PipeFuseCert.withForcedNat
        (w0Hi * (t1 + t2) + (jp01Scale - p2Lo) * cswapZeroHitNat +
          (p0Hi + 1) * (cv2 - cswapZeroHitNat)) fun num27 =>
      Nat.ble num27 ((rawV2 - 1) * jp01Scale) &&
      PipeFuseCert.withForcedNat (v2m idx) fun vmCur =>
      Nat.ble rawV2 vmCur &&
      (cond (Nat.blt (idx + 1) 420) (Nat.ble (v2m (idx + 1)) vmCur) true)
private def checkWarmJP01R2Table (ct1 ct2 cv2 : ℕ) (rows : ℕ → WarmJP01Row) (v2m : ℕ → ℕ) : Bool :=
  Nat.blt cswapZeroHitNat cv2 &&
  Nat.ble cv2 700000000000 &&
  Nat.ble (jp01Sq2Lo * jp01Sq2Lo) (2 * jp01Scale * jp01Scale) &&
  Nat.ble (2 * jp01Scale * jp01Scale) (jp01Sq2Hi * jp01Sq2Hi) &&
  Nat.ble (jp01Sq3Lo * jp01Sq3Lo) (3 * jp01Scale * jp01Scale) &&
  Nat.ble (3 * jp01Scale * jp01Scale) (jp01Sq3Hi * jp01Sq3Hi) &&
  Nat.ble (jp01Sq6Lo * jp01Sq6Lo) (6 * jp01Scale * jp01Scale) &&
  Nat.ble (6 * jp01Scale * jp01Scale) (jp01Sq6Hi * jp01Sq6Hi) &&
  (match jp01EvalInterval 0 1 (jp01Scale - 1) jp01Scale ct1 ct2 with
   | (okC, (p0C, p2C, _)) =>
     okC &&
     Nat.ble (p0C + 1) 200000000000000 &&
     Nat.ble (p0C + 1 + p2C) jp01Scale &&
     Nat.ble
       (jp01Scale * (ct1 + ct2) + (jp01Scale - (p0C + 1) - p2C) * cswapZeroHitNat + jp01Scale)
       ((jp01Scale - (p0C + 1)) * (cv2 - 1))) &&
  PipeFuseCert.allRange (checkWarmJP01RowAt cv2 rows v2m) 420
private def checkS3Idx (v2m : ℕ → ℕ) (tc sIdx hh : ℕ) : Bool :=
  Nat.ble 1 tc && Nat.ble tc 200000 && Nat.blt sIdx 420 &&
  PipeFuseCert.withForcedNat (tc * tc) fun t2 =>
  Nat.ble (3 * sIdx * sIdx * (10000000000 + t2)) (524288 * t2) &&
  Nat.ble (v2m sIdx) hh
private def checkWarmJP01Stage3Bin (B tn phiLo dNat : ℕ) (v2m w : ℕ → ℕ)
    (bc : M2BinCert) (j : ℕ) : Bool :=
  match bc with
  | ⟨tcLo, bLoHi, dropHi, sIdx, _, _, _, _, hh⟩ =>
    (cond (_nEq tcLo 0)
  (Nat.ble (v2m 0) hh)
  (
      Nat.ble 1 tcLo && Nat.ble tcLo 200000 &&
      checkAtan200Hi tcLo bLoHi &&
      PipeFuseCert.withForcedNat ((j + 1) * dNat * 1000000000001) fun dr =>
      Nat.ble (4 * 3 * dr * dr) ((dropHi * 1000000000000) * (dropHi * 1000000000000)) &&
      Nat.ble (bLoHi + dropHi) phiLo &&
      checkS3Idx v2m tcLo sIdx hh
  )) &&
    PipeFuseCert.withForcedNat (w j) fun wj =>
    Nat.ble hh wj &&
    PipeFuseCert.withForcedNat (minDiffNat B w j) fun md =>
    PipeFuseCert.withForcedNat ((dNat - md) * 100000 * 100000000 * 1000000000000) fun lhsR =>
    PipeFuseCert.withForcedNat (dNat * 4 * tn * 99999999 * (wj - hh)) fun rhsR =>
    Nat.ble (lhsR * lhsR) (3 * rhsR * rhsR)
private def checkWarmJP01Stage3 (B : ℕ) (v2m : ℕ → ℕ) (stFn : ℕ → M2StageScalar)
    (wFn : ℕ → ℕ → ℕ) (binFn : ℕ → ℕ → M2BinCert) : Bool :=
  let w := wFn 3
  match stFn 3 with
  | ⟨tn, phiHi, phiLo, cSelf, dNat, stepNum, _, ⟨sLk, _, _, _, _, hLk, hBoth⟩⟩ =>
    Nat.ble 500 tn && Nat.ble tn 200000 &&
    checkAtan200Hi tn phiHi &&
    checkAtan200Lo tn phiLo &&
    Nat.ble 1 cSelf &&
    Nat.ble (phiHi * phiHi) (4 * 3 * (cSelf - 1) * (cSelf - 1)) &&
    Nat.ble 1000 dNat && Nat.ble cSelf (B * dNat) &&
    checkClickRow 2 3 tn stepNum &&
    PipeFuseCert.allRange (checkM2KnotSlope dNat w) B &&
    checkS3Idx v2m tn sLk hLk &&
    Nat.ble (v2m 0) hBoth &&
    PipeFuseCert.withForcedNat (cond (Nat.ble hLk hBoth) (hBoth - hLk) 0) fun extra =>
    PipeFuseCert.withForcedNat (w 0) fun w0 =>
    Nat.ble stepNum w0 &&
    Nat.ble (200000000 * hLk + extra) (200000000 * (w0 - stepNum)) &&
    PipeFuseCert.allRange (fun j => checkWarmJP01Stage3Bin B tn phiLo dNat v2m w (binFn 3 j) j) B
private def checkWarmJP01StageIdx (B : ℕ) (v2m : ℕ → ℕ) (stFn : ℕ → M2StageScalar)
    (wFn : ℕ → ℕ → ℕ) (binFn : ℕ → ℕ → M2BinCert) (idx : ℕ) : Bool :=
  match idx with
  | 0 => checkWarmJP01Stage3 B v2m stFn wFn binFn
  | s' + 1 => checkWarm2StageIdx B stFn wFn binFn (s' + 2)
private def checkWarmJP01CellHT (B cv2 : ℕ) (stFn : ℕ → M2StageScalar) (wFn : ℕ → ℕ → ℕ)
    (kIdx topR rcNum12 : ℕ) : Bool :=
  let k := 2 ^ kIdx
  Nat.ble 1 B && Nat.ble 2 kIdx && Nat.ble kIdx 4 &&
  Nat.ble 1 topR && Nat.blt cswapZeroHitNat cv2 &&
  match stFn k with
  | ⟨_, phiHiK, _, _, _, _, _, _⟩ =>
    Nat.ble (phiHiK * phiHiK) (4 * k * (topR - 1) * (topR - 1)) &&
    Nat.ble ((wFn k 0 + topR) * 1000000000000 * sqrtMUpNat 1)
      (rcNum12 * 785398163397 * harmSumPow2 kIdx)
private def checkWarmJP01CellCert (B cv2 : ℕ) (v2m : ℕ → ℕ) (stFn : ℕ → M2StageScalar)
    (wFn : ℕ → ℕ → ℕ) (binFn : ℕ → ℕ → M2BinCert) (kIdx topR rcNum12 : ℕ) : Bool :=
  checkWarmJP01CellHT B cv2 stFn wFn kIdx topR rcNum12 &&
  PipeFuseCert.allRange (checkWarmJP01StageIdx B v2m stFn wFn binFn) (2 ^ kIdx - 2)
/-! ### Bit-Packed WarmJP01 Certificate Tables & `decide +kernel` Seals -/
private def jp01ListGet : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => jp01ListGet xs k
private def jp01PairListGet : List (ℕ × ℕ) → ℕ → ℕ × ℕ
  | [], _ => (0, 0)
  | x :: _, 0 => x
  | _ :: xs, k + 1 => jp01PairListGet xs k
private def jp01Cdiv (a b : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat a fun a =>
  PipeFuseCert.withForcedNat b fun b =>
  PipeFuseCert.withForcedNat ((a + b - 1) / b) fun q => q
private def jp01MinAtan200Hi (tn : ℕ) : ℕ :=
  let pi4Hi12 := 785398163398
  let s10 := 10000000000
  let s12 := 1000000000000
  let s20 := 100000000000000000000
  PipeFuseCert.withForcedNat tn fun tn =>
  cond (Nat.blt 100000 tn)
    (
    PipeFuseCert.withForcedNat (tn - 100000) fun a =>
    PipeFuseCert.withForcedNat (100000 + tn) fun b =>
    PipeFuseCert.withForcedNat (a * a) fun aa =>
    PipeFuseCert.withForcedNat (b * b) fun bb =>
    PipeFuseCert.withForcedNat (a * (945 * bb * bb + 735 * aa * bb + 64 * aa * aa)) fun p54 =>
    PipeFuseCert.withForcedNat (b * (945 * bb * bb + 1050 * aa * bb + 225 * aa * aa)) fun q54 =>
      jp01Cdiv (pi4Hi12 * q54 + s12 * p54) q54
    )
    (
 cond (Nat.blt 500000 (12 * tn))
   (
    PipeFuseCert.withForcedNat (100000 - tn) fun a =>
    PipeFuseCert.withForcedNat (100000 + tn) fun b =>
    PipeFuseCert.withForcedNat (a * a) fun aa =>
    PipeFuseCert.withForcedNat (b * b) fun bb =>
    PipeFuseCert.withForcedNat
      (a * b * (1155 * bb * bb + 1190 * aa * bb + 231 * aa * aa)) fun pHom =>
    PipeFuseCert.withForcedNat
      (1155 * bb * bb * bb + 1575 * aa * bb * bb +
        525 * aa * aa * bb + 25 * aa * aa * aa) fun qHom =>
      jp01Cdiv (pi4Hi12 * qHom - s12 * pHom) qHom
   )
   (
    PipeFuseCert.withForcedNat (tn * tn) fun tt =>
    PipeFuseCert.withForcedNat
      (tn * (945 * s20 + 735 * tt * s10 + 64 * tt * tt) * s12) fun lhs =>
    PipeFuseCert.withForcedNat
      (100000 * (945 * s20 + 1050 * tt * s10 + 225 * tt * tt)) fun q =>
      jp01Cdiv lhs q
   )
    )
private def jp01MinPade54Scale8 (td : ℕ) : ℕ :=
  let s16 := 10000000000000000
  let s32 := 100000000000000000000000000000000
  PipeFuseCert.withForcedNat td fun td =>
  PipeFuseCert.withForcedNat (td * td) fun td2 =>
  PipeFuseCert.withForcedNat
    (td * 10000 * (945 * s32 + 735 * td2 * s16 + 64 * td2 * td2)) fun lhs =>
  PipeFuseCert.withForcedNat
    (945 * s32 + 1050 * td2 * s16 + 225 * td2 * td2) fun q =>
    jp01Cdiv lhs q
private def jp01EvalPsiHi (B dNat : ℕ) (wFn : ℕ → ℕ) (y : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat y fun y =>
  PipeFuseCert.withForcedNat (y / dNat) fun q =>
  PipeFuseCert.withForcedNat (y % dNat) fun rem =>
  cond (Nat.blt q B)
    (
    PipeFuseCert.withForcedNat (wFn q) fun wq =>
    PipeFuseCert.withForcedNat (wFn (q + 1)) fun wq1 =>
    PipeFuseCert.withForcedNat (wq + jp01Cdiv ((wq1 - wq) * rem) dNat) fun res => res
    )
    (PipeFuseCert.withForcedNat (wFn B + (y - B * dNat)) fun res => res)
private def jp01UnpackQuad42 (word sub : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat word fun w =>
    PipeFuseCert.withForcedNat sub fun s =>
      let y :=
        cond (_nEq s 0)
          w
          (
 cond (_nEq s 1)
   (w / 4398046511104)
   (
 cond (_nEq s 2)
   (w / 19342813113834066795298816)
   (w / 85070591730234615865843651857942052864)
   )
          )
      PipeFuseCert.withForcedNat y fun y => y % 4398046511104
private def jp01UnpackWarmRow (p : ℕ × ℕ) : WarmJP01Row :=
  let d51 := 2251799813685248
  let d40 := 1099511627776
  PipeFuseCert.withForcedNat p.1 fun lo0 =>
  PipeFuseCert.withForcedNat (lo0 % d51) fun sLo =>
  PipeFuseCert.withForcedNat (lo0 / d51) fun lo1 =>
  PipeFuseCert.withForcedNat (lo1 % d51) fun sHi =>
  PipeFuseCert.withForcedNat (lo1 / d51) fun lo2 =>
  PipeFuseCert.withForcedNat (lo2 % d51) fun c0Lo =>
  PipeFuseCert.withForcedNat (lo2 / d51) fun c0Hi =>
  PipeFuseCert.withForcedNat p.2 fun hi0 =>
  PipeFuseCert.withForcedNat (hi0 % d40) fun t1 =>
  PipeFuseCert.withForcedNat (hi0 / d40) fun hi1 =>
  PipeFuseCert.withForcedNat (hi1 % d40) fun t2 =>
  PipeFuseCert.withForcedNat (hi1 / d40) fun rv2 =>
    ⟨sLo, sHi, c0Lo, c0Hi, t1, t2, rv2⟩
private def jp01UnpackTriple67 (word sub : ℕ) : ℕ :=
  let p67 := 147573952589676412928
  let p134 := 21778071482940061661655974875633165533184
  PipeFuseCert.withForcedNat word fun w =>
  PipeFuseCert.withForcedNat sub fun s =>
    let y := cond (_nEq s 0) w (cond (_nEq s 1) (w / p67) (w / p134))
    PipeFuseCert.withForcedNat (y % p67) fun z => z
private def jp01UnpackPair137 (word sub : ℕ) : ℕ :=
  let p137 := 174224571863520493293247799005065324265472
  PipeFuseCert.withForcedNat word fun w =>
  PipeFuseCert.withForcedNat sub fun s =>
    let y := cond (_nEq s 0) w (w / p137)
    PipeFuseCert.withForcedNat (y % p137) fun z => z
private def jp01UnpackBinR3 (v2m : ℕ → ℕ) (w : ℕ) : M2BinCert :=
  let d18 := 262144
  let d40 := 1099511627776
  PipeFuseCert.withForcedNat w fun w0 =>
  PipeFuseCert.withForcedNat (w0 % d18) fun tc =>
  cond (_nEq tc 0)
    (PipeFuseCert.withForcedNat (v2m 0) fun hh => ⟨0, 0, 0, 0, 0, 0, 0, 0, hh⟩)
    (
    PipeFuseCert.withForcedNat (w0 / d18) fun w1 =>
    PipeFuseCert.withForcedNat (w1 % d40) fun dr =>
    PipeFuseCert.withForcedNat (w1 / d40) fun si =>
    PipeFuseCert.withForcedNat (jp01MinAtan200Hi tc) fun bl =>
    PipeFuseCert.withForcedNat (v2m si) fun hh =>
      ⟨tc, bl, dr, si, 0, 0, 0, 0, hh⟩
    )
private def jp01UnpackBinR4 (B tp dp cNat : ℕ) (wPrev : ℕ → ℕ) (w : ℕ) : M2BinCert :=
  let d18 := 262144
  let d40 := 1099511627776
  PipeFuseCert.withForcedNat w fun w0 =>
  PipeFuseCert.withForcedNat (w0 % d18) fun tc =>
  cond (_nEq tc 0)
    (
    PipeFuseCert.withForcedNat (jp01EvalPsiHi B dp wPrev 0) fun ps =>
    PipeFuseCert.withForcedNat (cNat + ps) fun hh =>
      ⟨0, 0, 0, 0, 0, 0, cNat, ps, hh⟩
    )
    (
    PipeFuseCert.withForcedNat (w0 / d18) fun w1 =>
    PipeFuseCert.withForcedNat (w1 % d40) fun dr =>
    PipeFuseCert.withForcedNat (w1 / d40) fun w2 =>
    PipeFuseCert.withForcedNat (w2 % d40) fun tbf =>
    PipeFuseCert.withForcedNat (w2 / d40) fun un =>
    PipeFuseCert.withForcedNat (jp01MinAtan200Hi tc) fun bl =>
    PipeFuseCert.withForcedNat (jp01EvalPsiHi B dp wPrev (cNat - un)) fun ps =>
    PipeFuseCert.withForcedNat (un + ps) fun hh =>
    cond (Nat.blt tbf (tp * 10000000))
      (
      PipeFuseCert.withForcedNat
        (jp01Cdiv ((tp * 10000000 - tbf) * 10000000000000) (100000000000000000 + tp * tbf))
        fun td =>
      PipeFuseCert.withForcedNat (jp01MinPade54Scale8 td) fun nu =>
        ⟨tc, bl, dr, tbf, td, nu, un, ps, hh⟩
      )
      ⟨tc, bl, dr, tbf, 0, 0, un, ps, hh⟩
    )
private def warmJP01ColdTau1 : ℕ := 427516799900
private def warmJP01ColdTau2 : ℕ := 120096398980
private def warmJP01ColdV2 : ℕ := 632073520054
private def jp01Rows_c0 : List (ℕ × ℕ) := [
 (nat_lit 11417981541647684119059017252732277937312887894658864950280192,
  nat_lit 764398169122435419219598462229103224),
 (nat_lit 11417959763555441147654086699282483580672819563651007417312064,
  nat_lit 763973235411869920740444695237182072),
 (nat_lit 11417894429029446278442269999388979926846516750448794299319936,
  nat_lit 763549393925887892031467512509973112),
 (nat_lit 11417785537322015826131851632469867597490245359071581764528576,
  nat_lit 763126649575146012367290621703963256),
 (nat_lit 11417633087186888523433528303215205662063696626334205643164928,
  nat_lit 762705007269092035202923101300933240),
 (nat_lit 11417437076879259775005033884537956795877734310428478795411520,
  nat_lit 762284471918382639812988658957369976),
 (nat_lit 11417197504155587551764931407009880943598897889160695806579584,
  nat_lit 761865048431256653832881743980348024),
 (nat_lit 11416914366273546718966446468043929406080121823987532482787008,
  nat_lit 761446819472852696691330693603476088),
 (nat_lit 11416587659991800676566634278257498888195581547128369670461952,
  nat_lit 761030050028830095538518940848177784),
 (nat_lit 11416217381569875761429421536886274514454384801055594879745344,
  nat_lit 760614407219046567847073972019479160),
 (nat_lit 11415803526767898633750148535069773658764847496875758415503488,
  nat_lit 760199895956576644530848753123279480),
 (nat_lit 11415346090846379335406277849832801229746140286131146504946624,
  nat_lit 759786521156912708142925508514890360),
 (nat_lit 11414845068565948676381936447320287476483435243121069300426496,
  nat_lit 759374287734338215416771833374917240),
 (nat_lit 11414300454187027113303207899967976201358344806668576136038976,
  nat_lit 758963200604345548905469952058671736),
 (nat_lit 11413712241469516463936507899010927495851220243385405656886656,
  nat_lit 758553264686053868620945976445583992),
 (nat_lit 11413080423672445949760793176255544201588776056668624449163456,
  nat_lit 758133183407882491342689679278540828)]
private def jp01Rows_c1 : List (ℕ × ℕ) := [
 (nat_lit 11412404993553572566613603835130333903839779094246914609525760,
  nat_lit 757702241629762482322892512045500444),
 (nat_lit 11411685943368970037355564034047481253921156224553796626847552,
  nat_lit 757272436941880960611389860772775964),
 (nat_lit 11410923264872594928571799374375899744623113315542749263100544,
  nat_lit 756843774522067211617638480726919196),
 (nat_lit 11410116949315784259384104402360275097511372308159730313682368,
  nat_lit 756416259554195149849168273048012828),
 (nat_lit 11409266987446798782189276701705596491371301497600193487421696,
  nat_lit 755989897220929763993894509701433372),
 (nat_lit 11408373369510252083582034509371203127774489854955194666853440,
  nat_lit 755564692708562820198576350176675868),
 (nat_lit 11407436085246539685277934331390183808649885936887432232601472,
  nat_lit 755140712598683833738915591416383516),
 (nat_lit 11406455123891325234943996796987677399676369340598993254017728,
  nat_lit 754718268222332352511519707977943068),
 (nat_lit 11405430474174809755380041206873311470221659599628171694657024,
  nat_lit 754296997344229342106590565951014940),
 (nat_lit 11404362124321172163423144796648379493984778172578837167845696,
  nat_lit 753876905159129049408189729048037404),
 (nat_lit 11403250062047849937110518932721551328812670841212489263092864,
  nat_lit 753457996864203572939608019330861084),
 (nat_lit 11402094274564854036787010251221164276172793555575690555848640,
  nat_lit 753040277659042862863365517210748956),
 (nat_lit 11400894748573992482360268615500479422328218099468705185585920,
  nat_lit 752623752744445795161596932273670172),
 (nat_lit 11399651470268151020463623311977333082140560724447750989889088,
  nat_lit 752208427327255874914510119979124764),
 (nat_lit 11398364425330436775840459473875912671428972808354027023081856,
  nat_lit 751783023224863230963402778966115688),
 (nat_lit 11397033598933436082544010981657605194188429121333915438154944,
  nat_lit 751346588353782573383854165304690024)]
private def jp01Rows_c2 : List (ℕ × ℕ) := [
 (nat_lit 11395658975738243955506320409962147247269336689545124760020992,
  nat_lit 750911340403653761808000019817448808),
 (nat_lit 11394240539893699085774948632655023563015747281224775579388736,
  nat_lit 750477284844866129992037358049838440),
 (nat_lit 11392778275035356222174226531322668658497059114530220387937920,
  nat_lit 750044427152644714970621712246130024),
 (nat_lit 11391272164284606986726548123539521920070499219208192278106560,
  nat_lit 749612772805841331237252502174713192),
 (nat_lit 11389722190247675092276705566660478956377381325085965148353792,
  nat_lit 749182327288143496563887664302802280),
 (nat_lit 11388128335014600142134682513929223882650695236995436033628224,
  nat_lit 748753138986807141026059916245091688),
 (nat_lit 11386490580158210011736905822887230729131288943312169122577280,
  nat_lit 748325571266248014553631041087489384),
 (nat_lit 11384808906733047558381330673046288574729376670226128275578560,
  nat_lit 747899229033792231430796565580498280),
 (nat_lit 11383083295274251659036359092844832815535024552168045294879232,
  nat_lit 747474117788843345084504605462513000),
 (nat_lit 11381313725796438248149758486589064626125897549417827756270912,
  nat_lit 747050243033222760580932534821340520),
 (nat_lit 11379500177792547101512955218306218998002610401769825526630528,
  nat_lit 746627610273587586264716244443612520),
 (nat_lit 11377642630232574440309911718873265946358390551465015228410816,
  nat_lit 746206225020221707939335512640079208),
 (nat_lit 11375741061562453968926045012861688525769479626285658627706624,
  nat_lit 745786092789453640506343263595021672),
 (nat_lit 11373795449702686717163228996509112418766779740383786225594944,
  nat_lit 745355925059940072437324717823802466),
 (nat_lit 11371805772047119316214838135462788959738280448938009714087296,
  nat_lit 744914520170295619696932082078104674),
 (nat_lit 11369772005461596676843833038033262620062522476814385499093184,
  nat_lit 744474357201683176327788217764068450)]
private def jp01Rows_c3 : List (ℕ × ℕ) := [
 (nat_lit 11367694126282568995634679437757197640095603651412848039599104,
  nat_lit 744035441942439566644737613374864482),
 (nat_lit 11365572110315755851152975414304740968587833639259230368497472,
  nat_lit 743597780186946244060697903277194338),
 (nat_lit 11363405932834696120289662137591329936821919805380387180864128,
  nat_lit 743161377735629291086659867711290466),
 (nat_lit 11361195568579286476623692964185098454458832888688292796155328,
  nat_lit 742726240394959419331687432790916194),
 (nat_lit 11358940991754262798876994295349464488350372203194604687468800,
  nat_lit 742292397587773226576625452514983010),
 (nat_lit 11356642176027750087258676321078878700663657733295984377498688,
  nat_lit 741860267853860869963011243559271522),
 (nat_lit 11354299094529629692104577401310362445608836034529855845494656,
  nat_lit 741429420959492739216999482315160674),
 (nat_lit 11351911719849997886369141628511656870058788808353037488968384,
  nat_lit 740999862734109136520332049215831138),
 (nat_lit 11349480024037498840320338265815050692206268674166332842161664,
  nat_lit 740571599013194993152823970567994466),
 (nat_lit 11347003978597691850179206128163000367079737141192460416325952,
  nat_lit 740144635639488795311978047726599266),
 (nat_lit 11344483554491361476851689725012872499012208342094646914743424,
  nat_lit 739718978459355806654140969570712674),
 (nat_lit 11341918722132724922826600573991097286331247414217242643849152,
  nat_lit 739294633327623771572961829202345058),
 (nat_lit 11339309451387776424852078286579279706281038927421732973134592,
  nat_lit 738860259648469871481452765512025022),
 (nat_lit 11336655711572369033036593757263325613740683286513444374816320,
  nat_lit 738414416300108804854205709288817598),
 (nat_lit 11333957471450479077654618715445931252528324316925971198642560,
  nat_lit 737969875332368912345427080727839678),
 (nat_lit 11331214699232242276321462323838950669761119942455622961097920,
  nat_lit 737526642881757654318974570637640638)]
private def jp01Rows_c4 : List (ℕ × ℕ) := [
 (nat_lit 11328427362572126856946607548923215087253673332833175373139968,
  nat_lit 737084725093244971876008274049713086),
 (nat_lit 11325595428566923992982381168574000426717852021554085253296960,
  nat_lit 736644128120263286854990690218492862),
 (nat_lit 11322718863753806746561873665720220813481837258627357310031488,
  nat_lit 736204858119871798553228205922534334),
 (nat_lit 11319797634108297667784525940556022542704389842817721989855680,
  nat_lit 735766924358486914316853445284676542),
 (nat_lit 11316831705042202140057091079715232646725849166004540139527424,
  nat_lit 735330804705142314694945102860993470),
 (nat_lit 11313821041401541725434596125405242643211828916692813165674560,
  nat_lit 734896030929569878925862894027752382),
 (nat_lit 11310765607464396166108970663103433950593955098229477885813632,
  nat_lit 734462609225096580895352080804692926),
 (nat_lit 11307665366938733967916133761564413632421022615846636691752640,
  nat_lit 734030545792302949406845700259791806),
 (nat_lit 11304520282960220147879997617443800197130076083752671524940288,
  nat_lit 733599846840231994001079193683968958),
 (nat_lit 11301330318089966891848762961511555259175973899599942103485760,
  nat_lit 733170518588807056595319664940499902),
 (nat_lit 11298095434312249958186589521797746186892208025433290086330496,
  nat_lit 732742567263996108204907363766191038),
 (nat_lit 11294815593032156573576016600664017952625190192871996865582016,
  nat_lit 732304335149391196857057026416280854),
 (nat_lit 11291490755073233328820383651869994380467625190685754546026240,
  nat_lit 731854622647242637624897243998553366),
 (nat_lit 11288120880675122656664709209889642494091347709925730483165760,
  nat_lit 731406278794192980506718729936798998),
 (nat_lit 11284705929491039457874986751761523155758884186448251456208256,
  nat_lit 730959310112397022323445881770837270),
 (nat_lit 11281245860585339071169813740325794014028843152673335021445312,
  nat_lit 730513723131263114813690872088724758)]
private def jp01Rows_c5 : List (ℕ × ℕ) := [
 (nat_lit 11277740632430982481318145838319352640466027720057480430945280,
  nat_lit 730069524393497793731826794400285974),
 (nat_lit 11274190202906933019347801236416971278228666156223860430694208,
  nat_lit 729626720447852223930299888088876310),
 (nat_lit 11270594529295598734680131571922707624594796917059048739949184,
  nat_lit 729185317857584680096931942634325270),
 (nat_lit 11266953568280126333504651427648897358950569684133524163407296,
  nat_lit 728745816159306307733800350851499286),
 (nat_lit 11263267275941729371098292773801868455236335684369527012364544,
  nat_lit 728307734128005351041615829199979798),
 (nat_lit 11259535607756947936255409523768011684661639845912435089929280,
  nat_lit 727871073683456011568409507113174294),
 (nat_lit 11255758518594851245810073851499538184580522056590697553549184,
  nat_lit 727435841430020041868900566010922262),
 (nat_lit 11251935962714228821176830861180623741871759485566783212993216,
  nat_lit 727002043984148452693954479060124950),
 (nat_lit 11248067893760690321039120075466235948417977054905387145371136,
  nat_lit 726569687974381512990583011174745366),
 (nat_lit 11244154264763776792019238571364515606066123083860820682375488,
  nat_lit 726138780037721972443100331491689750),
 (nat_lit 11240195028133991993477512582335395253168178255800843086783616,
  nat_lit 725697272495769365602924385625792446),
 (nat_lit 11236190135659765214422219214330138700598069762181907295586240,
  nat_lit 725244207954225876464637470056210366),
 (nat_lit 11232139538504448344364133104797037533019071387923863469533952,
  nat_lit 724792584607001872874999338610810814),
 (nat_lit 11228043187203153092429490014205782094127189841359321739169344,
  nat_lit 724342409399376188520054599976574910),
 (nat_lit 11223901031659645296380658655926509984126025723140575758152064,
  nat_lit 723893689293552618560452671286370238),
 (nat_lit 11219713021143147887784479344635902007692286386609903258227904,
  nat_lit 723446431260197438894145373896007614)]
private def jp01Rows_c6 : List (ℕ × ℕ) := [
 (nat_lit 11215479104285052513328269463321314006044731536117058985342976,
  nat_lit 723000642288110812713303966781890494),
 (nat_lit 11211199229075699664025078816272999245924132801801538189630272,
  nat_lit 722556329374555383947402113143365566),
 (nat_lit 11206873342860964698732736971557859893685952771066226125962880,
  nat_lit 722113990291110601461158610724282302),
 (nat_lit 11202501392338900957580608841847876001624498659008608361800128,
  nat_lit 721673170617067981950842237569556414),
 (nat_lit 11198083323556291531544017083795864354391379540739305337963776,
  nat_lit 721233848686058986283068924595101630),
 (nat_lit 11193619081905155360092497906669690438258376611826308617414720,
  nat_lit 720796031552165771909199906211454910),
 (nat_lit 11189108612119196238930348642581096874139709633721788198521728,
  nat_lit 720359726283977606115971966925627326),
 (nat_lit 11184551858270228991774092021305728894029663011206849576169152,
  nat_lit 719924939967008717664726699690516414),
 (nat_lit 11179948763764491462314523968322816359364481745437353808777728,
  nat_lit 719491679697653667693337360031375294),
 (nat_lit 11175299271338979342141844698162246687950649402852051581056320,
  nat_lit 719047731382828477386691670159300280),
 (nat_lit 11170603323057666818855373330956082515614697206863819834202240,
  nat_lit 718591868309785494719859889835251384),
 (nat_lit 11165860860307715806191720861265395469957041275135926018735040,
  nat_lit 718137525768027835631331112902891192),
 (nat_lit 11161071823795582412319088297795663747516019493208472789573376,
  nat_lit 717684711182777884194157730407552696),
 (nat_lit 11156236153543123408131564803071604871724625047276948198539840,
  nat_lit 717233431993765134316767683491043000),
 (nat_lit 11151353788883611351691092651659338310961543518858100139795840,
  nat_lit 716783695656435115562579092566349496),
 (nat_lit 11146424668457704040743265597631789412243864254763552044812480,
  nat_lit 716335509643158318969614886492346040)]
private def jp01Rows_c7 : List (ℕ × ℕ) := [
 (nat_lit 11141448730209322621380794060616917411820485722202650520022016,
  nat_lit 715888881443230197050502802573792952),
 (nat_lit 11136425911381563950651595254807029808615093887678783978065728,
  nat_lit 715444307199807119649056140225320632),
 (nat_lit 11131356148512441689443758602782369743352806656469335339446912,
  nat_lit 715001361477386054541892770247120568),
 (nat_lit 11126239377430627395370511149314420968083166641681687482897856,
  nat_lit 714559996875194540459017381584737976),
 (nat_lit 11121075533251145943729016384402312926542982373404996319639808,
  nat_lit 714120220953854653270320832850597560),
 (nat_lit 11115864550370956768643756589518741171641613548251053247913024,
  nat_lit 713682041290913430320298791103010488),
 (nat_lit 11110606362464535104209915183805181758937127102835279479291776,
  nat_lit 713245465478425018788822473496762040),
 (nat_lit 11105300902479339045821342593451267965230332739616875681161920,
  nat_lit 712810501130204230608826422331348664),
 (nat_lit 11099948102631219521590813882678924675720040472933516309333504,
  nat_lit 712364733784593011037473844059278008),
 (nat_lit 11094547894399830263770286384650443735144624410946241748330816,
  nat_lit 711906639237586557460443257484970680),
 (nat_lit 11089100208523866510448032617206044111809991350985944960552064,
  nat_lit 711450152015485720874402643157551800),
 (nat_lit 11083604974996337961190398141582800834070774069117276380311488,
  nat_lit 710995280077858097622070487342484152),
 (nat_lit 11078062123059716134886601296638687785641648466100613062071040,
  nat_lit 710542031403614097159999343100529336),
 (nat_lit 11072471581201024637685824694661095759866221063124625267521088,
  nat_lit 710090413993424793697805088637160120),
 (nat_lit 11066833277146883759008140126408450624825764937634610676554112,
  nat_lit 709640435864886222919708410603735736),
 (nat_lit 11061147137858440887740016989361346825570399699549917978508480,
  nat_lit 709192105059772936902222579145738936)]
private def jp01Rows_c8 : List (ℕ × ℕ) := [
 (nat_lit 11055413089526300928429830715912833657539316456209528709554176,
  nat_lit 708745917416591998946274341651843768),
 (nat_lit 11049631057565319701704871429394908137325196872966585907938112,
  nat_lit 708301476597475929132991174925191864),
 (nat_lit 11043800966609363090743727657027297655368062105051755080738432,
  nat_lit 707858708237770785507688655264778936),
 (nat_lit 11037922740505974843896336861408501886342512373717922610727360,
  nat_lit 707417620466293779159133353394932408),
 (nat_lit 11031996302310987287396327733560886344097059386519570725154048,
  nat_lit 706978221431204934289925906835278520),
 (nat_lit 11026021574283017858257946009195432478517728633193215470440512,
  nat_lit 706540519303633865675344907424860856),
 (nat_lit 11019998477877988473136063580238243259349827438946277367214976,
  nat_lit 706104522274053001204503013798021816),
 (nat_lit 11013926933743427955536896300475410310156008364909169139144384,
  nat_lit 705657563715803478174895878724105912),
 (nat_lit 11007806861712820134954888381848157076213487063553919122979328,
  nat_lit 705197811986581680879953525845505720),
 (nat_lit 11001638180799803512249555370894998918665872798588676808842560,
  nat_lit 704739762615924180482000568866289336),
 (nat_lit 10995420809192313835114618886763166660429830561804855380902016,
  nat_lit 704283424167861483131070081405007544),
 (nat_lit 10989154664246646747676349825431196651281063594954729134482368,
  nat_lit 703828805231811537189102349749040824),
 (nat_lit 10982839662481440514221120030142687352119616316659485769615104,
  nat_lit 703375914420161881590715614505187000),
 (nat_lit 10976475719571578817052162428030940028810845983923786309741120,
  nat_lit 702924760373105349121664587298485944),
 (nat_lit 10970062750341967956549373042274066316861082798078323338710400,
  nat_lit 702475351755013288959996563248101048),
 (nat_lit 10963600668761314051229113004179107352480509164238563858280640,
  nat_lit 702028184185577191056390409120888504)]
private def jp01Rows_c9 : List (ℕ × ℕ) := [
 (nat_lit 10957089387935740386062427497723980158811070184066309588243456,
  nat_lit 701582893381597682573866169054246584),
 (nat_lit 10950528820102324834922473170325802358536443306379672581453632,
  nat_lit 701139375217084994284798396430530232),
 (nat_lit 10943918876622591611105778952842316997331856417858818462751360,
  nat_lit 700697638464004873312936382917752504),
 (nat_lit 10937259467975888838038090402732126680427220798080930919939520,
  nat_lit 700257691919710508993936632852756152),
 (nat_lit 10930550503752651940164797570399090034288143526914331510923520,
  nat_lit 699819544405733607055748234066507448),
 (nat_lit 10923791892647609943933654627095840415249945653653262845592640,
  nat_lit 699383204775037944536300632932333240),
 (nat_lit 10916983542452889016943624663660091795151837908836997268907904,
  nat_lit 698935724883244960207577158528541374),
 (nat_lit 10910125360050990409296766364776340915404871942890957049465536,
  nat_lit 698474900142897744277759694990484158),
 (nat_lit 10903217251407756976968579035452038324352964699081020436835840,
  nat_lit 698015881970520476025966487024181950),
 (nat_lit 10896259121565099927565973026264165236996532776920836294398272,
  nat_lit 697558679621649230421798496180118206),
 (nat_lit 10889250874633794073974490044573618542023489101619962034762880,
  nat_lit 697103302378416450466378525852312254),
 (nat_lit 10882192413786033310393148864464366209594633325531128815294400,
  nat_lit 696649759553177724651195108802437822),
 (nat_lit 10875083641247951834424666093599821878657559183260352232323840,
  nat_lit 696198060490929638597331765509235390),
 (nat_lit 10867924458292042607331802110922147826062545224673342142209600,
  nat_lit 695748214565682997596623116644393662),
 (nat_lit 10860714765229473052459832175153921498273125584950317106676096,
  nat_lit 695300717185567273167187923401188030),
 (nat_lit 10853454461402206647972809522786401730590293128938191661540544,
  nat_lit 694855239671457405942490054188606142)]
private def jp01Rows_c10 : List (ℕ × ℕ) := [
 (nat_lit 10846143445175193027479078352010250101679500313513652823918592,
  nat_lit 694411644870719160642849638590980798),
 (nat_lit 10838781613928261213136703966996062767016927472563855800953664,
  nat_lit 693969942290345182717710506497680062),
 (nat_lit 10831368864048024266740444569782962325010725851444395381018240,
  nat_lit 693530141463924485648038329641607870),
 (nat_lit 10823905090919624089067139984614875733485466039528121141899712,
  nat_lit 693092251962522783322852284171559614),
 (nat_lit 10816390188918373457387225553114670005567656863044264973014272,
  nat_lit 692656283388637860941151904778691262),
 (nat_lit 10808824051401283883160829552601885411481840389428829411211328,
  nat_lit 692208972096057753201161273663504958),
 (nat_lit 10801206570698445035973829194547344401799473760938884481178496,
  nat_lit 691747670081468359972662669524812350),
 (nat_lit 10793537638104324241603115089228785845065305598085345786642112,
  nat_lit 691288289147929325778707636650983998),
 (nat_lit 10785817143868963218247980881163509816013867852084223161737728,
  nat_lit 690830839336778508338406100151517758),
 (nat_lit 10778044977188923617167596635642520944662647887011760461546816,
  nat_lit 690375330725621539959306860377096766),
 (nat_lit 10770221026198323907170815406544941423679917801468699463772288,
  nat_lit 689921773427122901717782963744883262),
 (nat_lit 10762345177959533719659730373775899424718982953805825098402752,
  nat_lit 689470177593841626737490219437343294),
 (nat_lit 10754417318453856775691690332964521819653719880116577861545728,
  nat_lit 689020553410977745271679424354009662),
 (nat_lit 10746437332572076797262815412937286270347353296606771293262400,
  nat_lit 688573397166758725517919378874253886),
 (nat_lit 10738405104104832148868388077949869697694857068882088584770944,
  nat_lit 688128417685356284194700209142055486),
 (nat_lit 10730320515732864881266286005403828199891827367209696188553408,
  nat_lit 687685442149615581571166761734849086)]
private def jp01Rows_c11 : List (ℕ × ℕ) := [
 (nat_lit 10722183449017167013406540134375781738099861694040235678383104,
  nat_lit 687244480906732707728930142962795070),
 (nat_lit 10713993784388955544637767998879742189380997290417660674613056,
  nat_lit 686805544341380453157654963551945278),
 (nat_lit 10705751401139464779208940698254524734226234171799643152253568,
  nat_lit 686368642880544012033517855343067710),
 (nat_lit 10697456177409715814808066572071367853886636949412114117387712,
  nat_lit 685933786989894204760363583767527998),
 (nat_lit 10689107990180011999543875330708895919991911925295711106484480,
  nat_lit 685487325689431323871992168412601266),
 (nat_lit 10680706715259354463056710652098683484141001251534786059578432,
  nat_lit 685026157238175407487339414986939314),
 (nat_lit 10672252227274686377906298063224245344365388138798205509996416,
  nat_lit 684567036036304088398389421861493682),
 (nat_lit 10663744399660000205181013049385244775323815314045282212442816,
  nat_lit 684109973033058514854838624350100402),
 (nat_lit 10655183104645250834420941152872242409996942088439277402150400,
  nat_lit 683654979218783312973280849706605490),
 (nat_lit 10646568213245165961707063242438738081575768544703320865487168,
  nat_lit 683202065632180141654895092173102002),
 (nat_lit 10637899595247850944082691124479351838557678150692876515548288,
  nat_lit 682751243353054137667757737931692978),
 (nat_lit 10629177119203233802233320086640479203002947018241091346268096,
  nat_lit 682302523508358544744915710978022322),
 (nat_lit 10620400652411373207387981669191093990121753493563289012069120,
  nat_lit 681856406331045780486472808757713842),
 (nat_lit 10611570060910560944552846778109831505870632009089982538139200,
  nat_lit 681412636703917983256463551375858610),
 (nat_lit 10602685209465287359966329025937289908280340184465018469067136,
  nat_lit 680971004942418518356301473570347954),
 (nat_lit 10593745961554012702867980061988166196274535361691423520328896,
  nat_lit 680531522365719834837759538115107762)]
private def jp01Rows_c12 : List (ℕ × ℕ) := [
 (nat_lit 10584752179356721525618093596636118327016530228986586988179456,
  nat_lit 680094200342560340356810503947017138),
 (nat_lit 10575703723742419993909601187036055122587144183834423026570048,
  nat_lit 679659050290035475354012296991202226),
 (nat_lit 10566600454256256403589093649458109198770271699745475130242688,
  nat_lit 679226083673597713054508010161036210),
 (nat_lit 10557442229106687369404009062155262072556608043045859604142528,
  nat_lit 678781184299249396727321999602819598),
 (nat_lit 10548228905152232966414321451759871471283608947036996737694976,
  nat_lit 678320767495203974099129361392673294),
 (nat_lit 10538960337888174781496521241183544262318413954230150412787776,
  nat_lit 677862537415523883526021998508974606),
 (nat_lit 10529636381433025605216762743854910418571051157663357467149184,
  nat_lit 677406506061215736322423728259932686),
 (nat_lit 10520256888514816435999345294955715258578903631479256119977664,
  nat_lit 676952685482852102406958164116709902),
 (nat_lit 10510821710457075198793569895317532494420861852947468911479296,
  nat_lit 676501087787825065220136490761658894),
 (nat_lit 10501330697164794045759054207446745922109029659498395693215040,
  nat_lit 676051725139137295904742834913616398),
 (nat_lit 10491783697109962773652464939740618790644804641629559450652800,
  nat_lit 675604609752984201666605006978490894),
 (nat_lit 10482180557317090823232708582862055427957989576459283053458368,
  nat_lit 675160246409088207676447130471834126),
 (nat_lit 10472521123348363903256789420318894114425856861647623455971072,
  nat_lit 674718420299465055708884297726763534),
 (nat_lit 10462805239288652180715626119109087244232218932097399022778944,
  nat_lit 674278880534530475320309252795867662),
 (nat_lit 10453032747730278693457493719004451646665372809352568296430976,
  nat_lit 673841639567429334361017124327465486),
 (nat_lit 10443203489757559403180632668136825726439935626837090830794944,
  nat_lit 673406709910543865842419870530478606)]
private def jp01Rows_c13 : List (ℕ × ℕ) := [
 (nat_lit 10433317304931080634850399961890052843386607683898891406713856,
  nat_lit 672974104134284742117431649999725070),
 (nat_lit 10423374031271805246393295566469331433000952785075814371886912,
  nat_lit 672543834869508926519698080065331726),
 (nat_lit 10413373505244870512889364355029773886803606218686396238228096,
  nat_lit 672101259714286451703523286144676238),
 (nat_lit 10403315561743146233152223442473959207044834373753910598290880,
  nat_lit 671642225822246751002706919473967502),
 (nat_lit 10393200034070632984567506452560265446947650979659612912496896,
  nat_lit 671185533422464735241417403189064078),
 (nat_lit 10383026753925449330595808468514751340582602715136838937121856,
  nat_lit 670731195739379945184083279400825230),
 (nat_lit 10372795551382704848460214506685223390634872576656627709441920,
  nat_lit 670279226068758544952396211527774606),
 (nat_lit 10362506254876996363442953616725856339864493568825497733913280,
  nat_lit 669829637766812989648779321723744654),
 (nat_lit 10352158691184767167403553209435478553477891456616644724637184,
  nat_lit 669382444258664506093689595100819854),
 (nat_lit 10341752685406220936016869125062261192267830099058719802663232,
  nat_lit 668937659037134167006003250554630542),
 (nat_lit 10331288060947121466195699224640451638843848707104158624810112,
  nat_lit 668495793747434127147923494757101966),
 (nat_lit 10320764639500192784159439312453927953372081973133600274180032,
  nat_lit 668056675621975505392794970448621966),
 (nat_lit 10310182241026279475890364457112970477249389745127723528702720,
  nat_lit 667620009147304177681818324927410574),
 (nat_lit 10299540683735221568051369120507774309957122191238189008531008,
  nat_lit 667185808107592339260995408193286542),
 (nat_lit 10288839784066398287438999503937720601146236823731283392860544,
  nat_lit 666754086355920957094361933204320654),
 (nat_lit 10278079356668974952916403054468763864019772923005499330557120,
  nat_lit 666324857819115473142445992575660430)]
private def jp01Rows_c14 : List (ℕ × ℕ) := [
 (nat_lit 10267259214381887253770820074485092275263169303082508851009536,
  nat_lit 665898136495327952723038800230117774),
 (nat_lit 10256379168213403062754034367014582674309366674418031225551680,
  nat_lit 665458712874317810038200451490338574),
 (nat_lit 10245439027320455889491990927311026960019584724099301579136640,
  nat_lit 665001698838612559985204375452604174),
 (nat_lit 10234438598987612958485080908559760096529445514714007947051456,
  nat_lit 664547198788327714945869684401985294),
 (nat_lit 10223377688605712165643718804733693922321884154561996336948480,
  nat_lit 664095227396195947582950671747340046),
 (nat_lit 10212256099650145077396128555267012841955900135317495736354880,
  nat_lit 663645799414739034653767156428134158),
 (nat_lit 10201073633658843062276046809860644093475320635251529370381184,
  nat_lit 663198929676267857010204482914440974),
 (nat_lit 10189830090209783867285676990676421588515396275180738725777088,
  nat_lit 662754633096509177057557408731059982),
 (nat_lit 10178525266898292670590893696100482660792366525271109133791744,
  nat_lit 662312924669769935476071587758692110),
 (nat_lit 10167158959313874996973239549508489022366745231651370614674752,
  nat_lit 661874323420545489955646709075760910),
 (nat_lit 10155730961016695675854130969807944783355143469629024165083264,
  nat_lit 661438705096649026324310825556203278),
 (nat_lit 10144241063513669587946647920725536738628275853231707115297728,
  nat_lit 661005723357758186465410192326481678),
 (nat_lit 10132689056234175618516449286513474785381992979429001805397760,
  nat_lit 660575393558439805304349957329737486),
 (nat_lit 10121074726505382399270272226365360390888106905437675641496128,
  nat_lit 660147731142721228418017827437369102),
 (nat_lit 10109397859527117330982765621497715927103953588979727037121920,
  nat_lit 659722751640463534575940180924913422),
 (nat_lit 10097658238346347394750907500981606874669051702471757237233856,
  nat_lit 659300470672197239018740584170870542)]
private def jp01Rows_c15 : List (ℕ × ℕ) := [
 (nat_lit 10085855643831294587839089741601324190449762331372061143665664,
  nat_lit 658865046417166004420744563249090190),
 (nat_lit 10073989854645003296410203678966622221244292538215742781222720,
  nat_lit 658410708383492726675167978796060302),
 (nat_lit 10062060647218565128810476288040537328016688508365652766085760,
  nat_lit 657959077572360712784809322714730126),
 (nat_lit 10050067795723864193629557160918993818004012373128094594381248,
  nat_lit 657510170371968373445581687322021518),
 (nat_lit 10038011072045808568591231338906181424248042604045815570143488,
  nat_lit 657064003266019259102953869736644238),
 (nat_lit 10025890245754230647979424361618644130731851655990082230877248,
  nat_lit 656620592843393466508867405276745358),
 (nat_lit 10013705084075159501079416693559161665256960798577222103031680,
  nat_lit 656179955787267306345204904887553678),
 (nat_lit 10001455351861682183283558834026850302722038035928454275121856,
  nat_lit 655742108888411487239550976063147662),
 (nat_lit 9989140811564314073990695576600002509987024107833397729043968,
  nat_lit 655307583226729640078887438051937934),
 (nat_lit 9976761223200855405336216122803144885341697874759154428709184,
  nat_lit 654876302598791651274678892424826510),
 (nat_lit 9964316344325665473863480163970223835667667110240196612123776,
  nat_lit 654447866603530361183284159797497486),
 (nat_lit 9951805929998548640822827941710836653360981056625962394275776,
  nat_lit 654022292470556550952398238082371214),
 (nat_lit 9939229732752943835596549799756752656066047840568410889630464,
  nat_lit 653599597540702177134262009264836238),
 (nat_lit 9926587502563668757843731476061872816339611930515711650960960,
  nat_lit 653179799263602520046432981053836942),
 (nat_lit 9913878986814070344604933715322927217103055971111897806043520,
  nat_lit 652762915201322961230629174405992078),
 (nat_lit 9901103930262570084385164554287497288203487656995273145638080,
  nat_lit 652331930970567247003820475074076528)]
private def jp01Rows_c16 : List (ℕ × ℕ) := [
 (nat_lit 9888262075008706940049019108874598779857892410343616902545408,
  nat_lit 651882235475587118110263922422833008),
 (nat_lit 9875353160458483774841778852619778172498548824493493109236544,
  nat_lit 651435464869033148866293574815571824),
 (nat_lit 9862376923289142879333428510914255652185018429205666215757440,
  nat_lit 650991637576143756018472683949121392),
 (nat_lit 9849333097413370599285590570951914410767190178274847149943232,
  nat_lit 650550772140632086635598160641515376),
 (nat_lit 9836221413942736958755169396962006801529444550688905274117376,
  nat_lit 650112887231939573026388349880229744),
 (nat_lit 9823041601150644309991704494877693071595596957830114153803840,
  nat_lit 649678001644027006919868401647476592),
 (nat_lit 9809793384434453888663725143854489799168879443572513410487168,
  nat_lit 649246251538209451511722263099858800),
 (nat_lit 9796476486277030052026480995847939803640699016398430831638208,
  nat_lit 648818428051259298270272041230131056),
 (nat_lit 9783090626207588020215632166424524648884226230681346428525056,
  nat_lit 648393665152240704781303626823229296),
 (nat_lit 9769635520761765194796107283103186499727654021467329136213312,
  nat_lit 647971982181548933239654556828557168),
 (nat_lit 9756110883441030234381545967962167368074640658700101834449024,
  nat_lit 647553398611352160178156948238491504),
 (nat_lit 9742516424671304289527367630072056233912102770953653884650432,
  nat_lit 647137934049218253926481385612500848),
 (nat_lit 9728851851760862904786716453803981826927327426409013490738944,
  nat_lit 646725608242950477889595437775970160),
 (nat_lit 9715116868857461498021574344572073315687409032815843258550848,
  nat_lit 646316441076960713088919770296082288),
 (nat_lit 9701311176904581655135167003000164755809469044908775652502912,
  nat_lit 645893436063682297932817069254341692),
 (nat_lit 9687434473597026599856496080936523948448469952714718391505088,
  nat_lit 645447840797779748604008325310805052)]
private def jp01Rows_c17 : List (ℕ × ℕ) := [
 (nat_lit 9673486453335511881149206341387797711804110098500990370673664,
  nat_lit 645005417038752708669908168121742396),
 (nat_lit 9659466807180525309801787366593277720539239861340671403874112,
  nat_lit 644566185696182154185142803405173820),
 (nat_lit 9645375222805284874475985099063901123595291105090773483141760,
  nat_lit 644130167833182640295396342066803772),
 (nat_lit 9631211384447817473176506510903518053772927740857521176354240,
  nat_lit 643697384666402301237410800200021052),
 (nat_lit 9616974972862067116289684220056097334789566400349814859694336,
  nat_lit 643267857570858553617444615784723516),
 (nat_lit 9602665665268203870914225768527691115305452384175598768317504,
  nat_lit 642841716392437978964358927312450620),
 (nat_lit 9588283135301825260982423075365473695369886899069371886847872,
  nat_lit 642419859714821964455487631311467580),
 (nat_lit 9573827052962312736747279960920698426689551774248173474294464,
  nat_lit 642001329134261716742416008442508348),
 (nat_lit 9559297084560137689967808084177770895940243847202390920695296,
  nat_lit 641586146711235592152897238743872572),
 (nat_lit 9544692892663128432774032940848769267013426285306428248748352,
  nat_lit 641174334673053710121503328363312188),
 (nat_lit 9530014136041743812137876512888758418537664215821757754463360,
  nat_lit 640765915422320433926927513780974652),
 (nat_lit 9515260469613216444171416797334022305231006688819130171373504,
  nat_lit 640360911532098667413525745110578236),
 (nat_lit 9500431544384679748067940691187781374750003003753025411357440,
  nat_lit 639959345753163409909004461147649084),
 (nat_lit 9485527007395130345925748812510553171091791899376199637958208,
  nat_lit 639543279538876695045350300841917378),
 (nat_lit 9470546501656191574510087314748999159298777665594870865781120,
  nat_lit 639102467206640578054676905677798338),
 (nat_lit 9455489666091837960694789761673030034669822745358174007411904,
  nat_lit 638665108189142077546460496326015938)]
private def jp01Rows_c18 : List (ℕ × ℕ) := [
 (nat_lit 9440356135476772375082004575678131769924988252540189325371392,
  nat_lit 638231226441246309184578169589447618),
 (nat_lit 9425145540373661387467757717609866962291555204236354837941056,
  nat_lit 637800846114873297230091577748077506),
 (nat_lit 9409857507069080390393309178272780213968677884768105247567488,
  nat_lit 637373991554162271262788411860171714),
 (nat_lit 9394491657508145654819219986285893022998809819897502519185856,
  nat_lit 636950687305143072738099435159927746),
 (nat_lit 9379047609227878989848296322929993616084143898612406976853248,
  nat_lit 636531054962783564315041668769233858),
 (nat_lit 9363524975289145154755827676500325604923139969450861302356032,
  nat_lit 636116120062483302542387903461309378),
 (nat_lit 9347923364207207695253285626891010536019988130421025309326208,
  nat_lit 635704816296610538548381802322443202),
 (nat_lit 9332242379880926039948566555683101025726999305137067798847168,
  nat_lit 635297169086457407189445651074104258),
 (nat_lit 9316481621520399751316570271243146577637207149892335571223040,
  nat_lit 634893204064878061754561841011342274),
 (nat_lit 9300640683573174110995531025551768311591956404796894834140480,
  nat_lit 634492947087169006341804531575143362),
 (nat_lit 9284719155648847187667517855301199497883115603978051454994560,
  nat_lit 634096424226233392579881133653605314),
 (nat_lit 9268716622442181149356979076281957250023281991585906984348608,
  nat_lit 633703661783461352004663972154293186),
 (nat_lit 9252632663654512296479581272886479006913507092364179463229184,
  nat_lit 633295638117439692490662853695035370),
 (nat_lit 9236466853913573995456759259434008226470579297095423816020544,
  nat_lit 632860289451700848820052163436271594),
 (nat_lit 9220218762691538407209769002813470183029321672429998277989760,
  nat_lit 632428718878621061102026243804026858),
 (nat_lit 9203887954221368354385576687826019574812820586727637225011392,
  nat_lit 632000954140630037853095395955628010)]
private def jp01Rows_c19 : List (ℕ × ℕ) := [
 (nat_lit 9187473987411365147499167448411422266588464604270785721654272,
  nat_lit 631577023225569428971539643513755626),
 (nat_lit 9170976415757855280084565526373170040872841503256214103408448,
  nat_lit 631156954372737454835481878439974890),
 (nat_lit 9154394787256038828817649152864083844643659174973345273389696,
  nat_lit 630740776077724609581346377733560298),
 (nat_lit 9137728644308782616961468846836967322510505350634287605286336,
  nat_lit 630328598541372906000270190910691306),
 (nat_lit 9120977523633597918746443731537786741954448637222960492407040,
  nat_lit 629921599939264811003720336321075178),
 (nat_lit 9104140956167391657349936552707185777097363595095744193875008,
  nat_lit 629518586220203994500919473373501418),
 (nat_lit 9087218466969242292069123647333059963714257533963907897765760,
  nat_lit 629119587010126591967970157417519082),
 (nat_lit 9070209575120983453037868557026916954016678115967151759594176,
  nat_lit 628724632211812751572725024810391530),
 (nat_lit 9053113793625538233579891047643992046971162538850768044750336,
  nat_lit 628333752010931263272859938790627306),
 (nat_lit 9035930629303038394142856478108205357002301323039892368480576,
  nat_lit 627946976882084187913947135351511018),
 (nat_lit 9018659582684557208090260803241021819561344010376518665354368,
  nat_lit 627564337588806857229455223241103338),
 (nat_lit 9001300147903421695406486267582421646701644574665938766405568,
  nat_lit 627165602727290306759729370305342616),
 (nat_lit 8983851812584161334222736028447105492072336995658457509167872,
  nat_lit 626736381706376643351963008824978584),
 (nat_lit 8966314057728750710717598277971245396720396057783321841952320,
  nat_lit 626311316743943835132134373158235288),
 (nat_lit 8948686357600431556930781055923169076858456568422667958831488,
  nat_lit 625890440351633948996465858678303896),
 (nat_lit 8930968179604657457228351846247874564511903015037501119769792,
  nat_lit 625473785363872245678285850404924568)]
private def jp01Rows_c20 : List (ℕ × ℕ) := [
 (nat_lit 8913158984167458090939564796823164240494923039924537318445056,
  nat_lit 625061384941493957206872610528504984),
 (nat_lit 8895258224610823381811317893716478566054120967631574569743168,
  nat_lit 624653272578997841825142053458357400),
 (nat_lit 8877265347025233152077198214346044811133135011725566931949184,
  nat_lit 624249541106170810281624617357618328),
 (nat_lit 8859179790139183847381073839688287103111957907783296581056960,
  nat_lit 623851557747997149184268402778385560),
 (nat_lit 8841000985185643824665982539355794950276169044718361308929280,
  nat_lit 623457973930800116939624216535444632),
 (nat_lit 8822728355765208843397484276061222359878311609736405649457216,
  nat_lit 623068824631221526638143341227879576),
 (nat_lit 8804361317706174701770768835151002507019515613121892858880896,
  nat_lit 622684145193416640533124328565451928),
 (nat_lit 8785899278921036044695227729131488361599786189073185593149120,
  nat_lit 622303971331472021679942257718013080),
 (nat_lit 8767341639259685375113489921317352585012965194654555946560000,
  nat_lit 621928339137868014673351139538447512),
 (nat_lit 8748687790358935475264046995198717911491344357755106619395392,
  nat_lit 621557285091941226384786320785616024),
 (nat_lit 8729937115488376655869009417160431058779469311561812961128576,
  nat_lit 621169219324775471216089154137405970),
 (nat_lit 8711088989392466071413119063376126140335466223019037764768704,
  nat_lit 620746768367031828006652043598543378),
 (nat_lit 8692142778128700667753976590998741493309939091720466878478080,
  nat_lit 620328918319829661039093963029002770),
 (nat_lit 8673097838901759582248067176806299235415752583562686886517312,
  nat_lit 619915707811975684459660931815225874),
 (nat_lit 8653953519893501816577168146441474454198363593065678860287360,
  nat_lit 619507175903863130017021584713759250),
 (nat_lit 8634709160088659330533555426717993091074471520481006060560576,
  nat_lit 619103362086262821242652542676548114)]
private def jp01Rows_c21 : List (ℕ × ℕ) := [
 (nat_lit 8615364089096179884837842230166111402167880692511621460935680,
  nat_lit 618704306297248134925443221296822802),
 (nat_lit 8595917626965968437395533722852757725607387227469357665003328,
  nat_lit 618310078411522518971345289416849938),
 (nat_lit 8576369084000970003084589436994893983032392765762868089391744,
  nat_lit 617922277243153820284359329352038930),
 (nat_lit 8556717760564399871387785417761425759603444923105629605293504,
  nat_lit 617539367782761099581383341429537298),
 (nat_lit 8536962946881984166091376332059302740654595221245058953761024,
  nat_lit 617161391949847151999683958585997842),
 (nat_lit 8517103922839085149253099414712581918200352918097057745351744,
  nat_lit 616788392155947581259681887863486994),
 (nat_lit 8497139957772437237882520707742360978792013351825787369592704,
  nat_lit 616420411308257577123795797933603346),
 (nat_lit 8477070310256505151315265240249159254979164278620226427484864,
  nat_lit 616057492824139025231817869193951762),
 (nat_lit 8456894227884064559927173480136120522705837263135310330813952,
  nat_lit 615699680638374062018601568816380434),
 (nat_lit 8436610947041016653169925705230391653307149695015060622524736,
  nat_lit 615323648747304384453678995578608894),
 (nat_lit 8416219692675162595371134749378748869177480188281848210269312,
  nat_lit 614908580519411180662032068625358078),
 (nat_lit 8395719678058652419760365931531118741114461629352540338161600,
  nat_lit 614498643667828767635014370139102462),
 (nat_lit 8375110104544085524758000872301778922735893153579744788146944,
  nat_lit 614093884832915266105019460284112126),
 (nat_lit 8354390161313920233080695767535372585318644819365683195366976,
  nat_lit 613694351234104264399848273908915454),
 (nat_lit 8333559025122964054032601165225778793691662214143056858558848,
  nat_lit 613300090681994076638855412293360894),
 (nat_lit 8312615860033784797240760178139183427928930955799999418864832,
  nat_lit 612911151584392371831022289022147838)]
private def jp01Rows_c22 : List (ℕ × ℕ) := [
 (nat_lit 8291559817144722834351518997067146365974289391366724917950464,
  nat_lit 612527582983792874283010634400718078),
 (nat_lit 8270390034310367492909449932348118030906679801979332353252160,
  nat_lit 612151252132614898868385386726743294),
 (nat_lit 8249105635854018027194037781142440321161016001360928940310144,
  nat_lit 611780405770472513816195749097299198),
 (nat_lit 8227705732272140583995671167921844486753167466723730192835008,
  nat_lit 611415095022838630629109519836568830),
 (nat_lit 8206189419930330190124648007847596841112746435615550835131648,
  nat_lit 611055371688557842335142947580075262),
 (nat_lit 8184555780750492312114653900985021615316114305593607805233216,
  nat_lit 610701288251935681683807023021743358),
 (nat_lit 8162803881889072718397588741960779261965843775463810093468544,
  nat_lit 610352897893618953522639141486255358),
 (nat_lit 8140932775405867506706533990115430440499486023955078806318784,
  nat_lit 610010254514774251189495686423174398),
 (nat_lit 8118941497923173519094485998688443795848258706406312641270272,
  nat_lit 609647264601281056257481692641906604),
 (nat_lit 8096829070274822425307189495797649842921737166932554101421376,
  nat_lit 609240162880218399772292493964890028),
 (nat_lit 8074594497144927204786946501743460228151091540718729002244224,
  nat_lit 608838834962273854724519850140913580),
 (nat_lit 8052236766695701620341068412530008617561949690924070794869696,
  nat_lit 608443338226693597483308280249208748),
 (nat_lit 8029754850184169995770304886500119437929889317338392511717120,
  nat_lit 608053730851823771183072187849789356),
 (nat_lit 8007147701567230652324792093026849688268484533651295662735936,
  nat_lit 607670071839289002115788444477575084),
 (nat_lit 7984414257094753300504354187954151826339801005276531203368320,
  nat_lit 607292421028499509566371939738865580),
 (nat_lit 7961553434890048144273742450330858251884734235504415600298176,
  nat_lit 606920839117202844746124277281345452)]
private def jp01Rows_c23 : List (ℕ × ℕ) := [
 (nat_lit 7938564134517546845951229012566225485678882588895976604216320,
  nat_lit 606557444576230415907396786870177708),
 (nat_lit 7915445236536873257099556550998924616474555037782575572651840,
  nat_lit 606200268474038997849008533195345836),
 (nat_lit 7892195602043041301843786039941915339953021115588742709736064,
  nat_lit 605849367071618383796572048732868524),
 (nat_lit 7868814072192060679778918765250749731927361332825936682669504,
  nat_lit 605504804978800077234328946479615916),
 (nat_lit 7845299467711562177094876575977786336349236478267042423126272,
  nat_lit 605166647768929459879380291673280428),
 (nat_lit 7821650588395654745192466684045005093426097144534877698956352,
  nat_lit 604834962015133566270125477033562028),
 (nat_lit 7797866212583534791565581809131433789311975061803622335315840,
  nat_lit 604509815302410341962408514509229996),
 (nat_lit 7773945096621208275983303398388459144792725715767006904410816,
  nat_lit 604162123357472885991900061471951660),
 (nat_lit 7749885974305514935282450935496768906885777385912507591411200,
  nat_lit 603763229519787772709258871255681836),
 (nat_lit 7725687556309838065767328364112354029364461036267368371988800,
  nat_lit 603370901642326554087103366337219372),
 (nat_lit 7701348529590860456250335355198220204406793429832590625770624,
  nat_lit 602985211906423141856097680898214700),
 (nat_lit 7676867556775293181468528536188146408679519071698910596100032,
  nat_lit 602606233647935605478876810964716332),
 (nat_lit 7652243275526074864688300183622650719109437585988010751251200,
  nat_lit 602234041377797911083495310377175852),
 (nat_lit 7627474297886956701251717849412899342544982348320184513443392,
  nat_lit 601868710818287696051866166031633196),
 (nat_lit 7602559209604719656282776173428582253828540950201710234573184,
  nat_lit 601510318928413711231668010548546348),
 (nat_lit 7577496569427927710325562704866160510591076050648115571752128,
  nat_lit 601161240305658285889433014467644204)]
private def jp01Rows_c24 : List (ℕ × ℕ) := [
 (nat_lit 7552284908381417894206422394306326340525733961108408514174976,
  nat_lit 600819358932100499770892443502594860),
 (nat_lit 7526922729015271135150539511334343505409727411461379154461504,
  nat_lit 600484679064368163739155621793844012),
 (nat_lit 7501408504627293385721896934502158669724887997398537467438720,
  nat_lit 600157283366390971403336257400294188),
 (nat_lit 7475740678457876655413989692813225130482272949145214860921280,
  nat_lit 599837255922586454419737338660604716),
 (nat_lit 7449917662855904041050919979728672690883913475019612650106112,
  nat_lit 599524682277754534539133896958495532),
 (nat_lit 7423937838414454196010834042161339407563227124260216792731712,
  nat_lit 599219649476972075654055769488050988),
 (nat_lit 7397799553075140604154452880403707675510608234556347763602304,
  nat_lit 598890677784620186108343575770965932),
 (nat_lit 7371501121199304453338199720581547284108509239388879495468736,
  nat_lit 598500063684027630643350021851719596),
 (nat_lit 7345040822604987818247009376930566000269964986608835755506176,
  nat_lit 598117014298933770284349465912289196),
 (nat_lit 7318416901567723259721656102486188586676134532621796946632000,
  nat_lit 597741622946322621084567903522400172),
 (nat_lit 7291627565783758264814060558190021040544714813504261532205184,
  nat_lit 597373984653808233851931612461017004),
 (nat_lit 7264670985293841978597745680227613992789415803263164243452864,
  nat_lit 597014196212827430212110836403414956),
 (nat_lit 7237545291365724514723694520714459513596155867706080411879168,
  nat_lit 596662356225787909573490322734720940),
 (nat_lit 7210248575333393533914905012392834248479063219635604525673024,
  nat_lit 596318565161678836829442264586397612),
 (nat_lit 7182778887391107033537561550861776123710684052755125846297984,
  nat_lit 595985521426345473385694019198003116),
 (nat_lit 7155134235339881662032785619146491563958481249094904880607424,
  nat_lit 595660939543107986146561546194397100)]
private def jp01Rows_c25 : List (ℕ × ℕ) := [
 (nat_lit 7127312583284210051808344156102562779819005162258528867128320,
  nat_lit 595344752525386710265442275106367404),
 (nat_lit 7099311850276552304558861416533861140379615636326095505946432,
  nat_lit 595037069517422492190287356756895660),
 (nat_lit 7071129908907066837112288536987474105094131885131258717526656,
  nat_lit 594738001849194060232297489837729708),
 (nat_lit 7042764583835680420491052295565884918469779055600079301918144,
  nat_lit 594447663095655389727039750469986220),
 (nat_lit 7014213650263837022488679155062567123852718592875300527579392,
  nat_lit 594166169150480178030939971861227436),
 (nat_lit 6985474832342602821133275113479251172734273734568031030805568,
  nat_lit 593859582157092541425649583163282644),
 (nat_lit 6956545801514113041910866372987839839710022908039133246613376,
  nat_lit 593476832625496497541967117120804052),
 (nat_lit 6927424174782604102821398739439269928551772183351235012446912,
  nat_lit 593102941993503265895560272212497620),
 (nat_lit 6898107512911674180694151332923230702058133725539418631974400,
  nat_lit 592738035064569834402671899230442708),
 (nat_lit 6868593318543593217518321557082430738847466797557847854977344,
  nat_lit 592382239319923881425948470940898516),
 (nat_lit 6838879034236688909212287932854447193390892712259891703772288,
  nat_lit 592035685008024286425922641012561108),
 (nat_lit 6808962040416264320177975018361768121195315333714750977955776,
  nat_lit 591698505242484121349798207167763668),
 (nat_lit 6778839653234502766986744636346119977387952001380437248686848,
  nat_lit 591370836087904383824088782586614996),
 (nat_lit 6748509122334084863724572179210835614560344549292796507987520,
  nat_lit 591055793331769557205244291815937236),
 (nat_lit 6717967628510528071062807953270087354044286159736693472395648,
  nat_lit 590750905693963814366378946364282068),
 (nat_lit 6687212281267265726726700175716451932955537107038576523011264,
  nat_lit 590456001716164936823480785178825940)]
private def jp01Rows_c26 : List (ℕ × ℕ) := [
 (nat_lit 6656240116257459699070772942333412136742868315047790819493888,
  nat_lit 590171231416395732195113355898361044),
 (nat_lit 6625048092606255355931611291572187065708483756337851486415680,
  nat_lit 589896748356040585390318317225481428),
 (nat_lit 6593633090106217012497565437954010578317602075737990256529024,
  nat_lit 589632709767991595487766131445437652),
 (nat_lit 6561991906278819037713386019481628447891359893435489422176704,
  nat_lit 589379276689630415893365273643816148)]
private def warmJP01Rows (idx : ℕ) : WarmJP01Row :=
  PipeFuseCert.withForcedNat idx fun idx =>
    PipeFuseCert.withForcedNat (idx / 16) fun c =>
    PipeFuseCert.withForcedNat (idx % 16) fun rem =>
      let L := cond (Nat.blt c 13) ( cond (Nat.blt c 6) ( cond (Nat.blt c 3) ( cond (Nat.blt c 1)
        jp01Rows_c0 (cond (Nat.blt c 2) jp01Rows_c1 jp01Rows_c2) ) ( cond (Nat.blt c 4) jp01Rows_c3
        (cond (Nat.blt c 5) jp01Rows_c4 jp01Rows_c5) ) ) ( cond (Nat.blt c 9) ( cond (Nat.blt c 7)
        jp01Rows_c6 (cond (Nat.blt c 8) jp01Rows_c7 jp01Rows_c8) ) ( cond (Nat.blt c 11) (cond
        (Nat.blt c 10) jp01Rows_c9 jp01Rows_c10) (cond (Nat.blt c 12) jp01Rows_c11 jp01Rows_c12) ) )
        ) ( cond (Nat.blt c 20) ( cond (Nat.blt c 16) ( cond (Nat.blt c 14) jp01Rows_c13 (cond
        (Nat.blt c 15) jp01Rows_c14 jp01Rows_c15) ) ( cond (Nat.blt c 18) (cond (Nat.blt c 17)
        jp01Rows_c16 jp01Rows_c17) (cond (Nat.blt c 19) jp01Rows_c18 jp01Rows_c19) ) ) ( cond
        (Nat.blt c 23) ( cond (Nat.blt c 21) jp01Rows_c20 (cond (Nat.blt c 22) jp01Rows_c21
        jp01Rows_c22) ) ( cond (Nat.blt c 25) (cond (Nat.blt c 24) jp01Rows_c23 jp01Rows_c24) (cond
        (Nat.blt c 26) jp01Rows_c25 jp01Rows_c26) ) ) )
      jp01UnpackWarmRow (jp01PairListGet L rem)
private def jp01V2M_c0 : List ℕ := [
 nat_lit 53700263979114237787137798628001363858224733572713,
 nat_lit 53582056444383993358603233751031168220108022782310,
 nat_lit 53465223336930979302634820661571510490332174068394,
 nat_lit 53348880035830158761420775599153477428856780161573,
 nat_lit 53228062260397477860438458471095733841695222714828,
 nat_lit 53108576742749706450486738867257861278530043510427,
 nat_lit 52990498654069027116657110965471424807563857139734,
 nat_lit 52871315864630669557700929290423522599535793096497,
 nat_lit 52749309441886308138998118040368362144212374362240,
 nat_lit 52628729518553728136875657069396555658933721260496,
 nat_lit 52509594952230998410916171990427100192471614865212,
 nat_lit 52387725588758668182824115798628698607979226193995,
 nat_lit 52264712804393621173418566432044792627842823720531,
 nat_lit 52143229776423185927892976315680237065476400168514,
 nat_lit 52023234924553960097811089755155536413062120584751,
 nat_lit 51898823657160177162193363832847841044547093107319]
private def jp01V2M_c1 : List ℕ := [
 nat_lit 51774994474571413544299770193895407254501345012966,
 nat_lit 51652807695452007223077627794608337074826124170873,
 nat_lit 51531336420324102067022198585318183463034510627830,
 nat_lit 51405333301298967876798435599677368185051871182965,
 nat_lit 51280927907859402332194420785717196337515769160938,
 nat_lit 51158220849761562539956310635775323089779065092491,
 nat_lit 51034524135865559180830079812137864842729386065801,
 nat_lit 50908016847594876672813035736405428767521174490333,
 nat_lit 50783234723038151504225723904705965450887345147636,
 nat_lit 50660213927660551832411473600815616645060241849582,
 nat_lit 50534435835152827320194337437868822331941465209171,
 nat_lit 50407630223457829945251022280085080761519601783592,
 nat_lit 50282689619704782196211703633410941076842528638032,
 nat_lit 50159579801185619293508995878387295709819315970573,
 nat_lit 50031844975327035613836470886341440356632897455381,
 nat_lit 49904957813771817327071146122803451801949814212621]
private def jp01V2M_c2 : List ℕ := [
 nat_lit 49780089561366047868054167692011826586034976531137,
 nat_lit 49656236578152483097070900655957464017516767980793,
 nat_lit 49527549140229692418908844878567003155273526263754,
 nat_lit 49400841698466281085171863853729542265936539298625,
 nat_lit 49276254381140947415654067716594727400044234084304,
 nat_lit 49150801562676209705559289549820994884259855759354,
 nat_lit 49022368711429901516290495755161012746459926694996,
 nat_lit 48896090600951363707850174899047677020312226425431,
 nat_lit 48772031369872948958460568203822306238663479209512,
 nat_lit 48645088772066630100224104724545289374293550393166,
 nat_lit 48517150545230548467351724347835735633945974738805,
 nat_lit 48391560953330967685255427170708636337449882487336,
 nat_lit 48268299179509020790434866213439252489344662166114,
 nat_lit 48139959681752607143125881421227183910067456077737,
 nat_lit 48012771728534925504613836574956203557449999513829,
 nat_lit 47888148602190203011846566145382139677374668458614]
private def jp01V2M_c3 : List ℕ := [
 nat_lit 47764979510566111060310466875781171233750637060049,
 nat_lit 47636310345125859327029923092666543137053012115772,
 nat_lit 47510178658490089976353522872391190677766542732029,
 nat_lit 47386784497217798297186017296629409461728283966892,
 nat_lit 47262619967802634548048418594633505889598206599210,
 nat_lit 47135070422630297589557881843726544855519748714625,
 nat_lit 47010309303023517656926940560776438994131356369202,
 nat_lit 46888443459091708034224800439352289800835344708151,
 nat_lit 46763351825518844267497496016065608439729044331420,
 nat_lit 46637211228929579445002702660088784028360636117535,
 nat_lit 46514142646933557644858756878303603448260416266090,
 nat_lit 46394146156945017369203810428106701946640327091609,
 nat_lit 46268164973116749358114380502033250279503805941741,
 nat_lit 46143748706889925281881861993395961825437008636836,
 nat_lit 46022727385349317063666181287538641319077912021096,
 nat_lit 45903778769388532794971949189270424776464649074946]
private def jp01V2M_c4 : List ℕ := [
 nat_lit 45778440859345009815617964150566843566829345345765,
 nat_lit 45656537981292219844101217949790688014480630759521,
 nat_lit 45538283728770467745154915489878483287390793670204,
 nat_lit 45419353989123282898041270399439052772954927056812,
 nat_lit 45296176589420131686510964194055948422454768626206,
 nat_lit 45176827291567791749180187830732450875249221555373,
 nat_lit 45061393164976616668716761059712957733091871533010,
 nat_lit 44942061613360135958466704828540043427752413399661,
 nat_lit 44821419968761137765307137406254976307274551303110,
 nat_lit 44705063968237312782235608811399935175087641554289,
 nat_lit 44592930860487518326175216963011936222407293327300,
 nat_lit 44473113461959395229705674537677317210797984889289,
 nat_lit 44355431898621159135908738584201292765211308507538,
 nat_lit 44242562802306727983396289391994272477909147476082,
 nat_lit 44132855855344525571308018334098996027308273232660,
 nat_lit 44013804792102803243681454868402167453334191818049]
private def jp01V2M_c5 : List ℕ := [
 nat_lit 43899650672003320540983883005072353585088696932047,
 nat_lit 43790748959366011034624473285403373699745367847529,
 nat_lit 43681170542328171993445241288910638320222263524820,
 nat_lit 43565526106176744907173812571252573850936620070512,
 nat_lit 43455469791138283109716804201592489277273465829856,
 nat_lit 43351192111271695904559674411939831579795274590397,
 nat_lit 43241497853779239035885763833955131344438242477251,
 nat_lit 43129788029475810729922928396096747599031452731053,
 nat_lit 43024512408020495565132808203430095285645783139442,
 nat_lit 42925655545698070888676979330105109454972622936369,
 nat_lit 42815393614273762921952981382904301390564657351118,
 nat_lit 42708257263927262147811275507629941885388501880975,
 nat_lit 42608612719895135853853733503472685466178312160985,
 nat_lit 42514129900371304750831854707973085842617254867966,
 nat_lit 42404643895432191516945165588278372052491148940047,
 nat_lit 42302961528591027542299404106293934810080232751535]
private def jp01V2M_c6 : List ℕ := [
 nat_lit 42209794410243401889994179102417035637382523548715,
 nat_lit 42115697871691217939464141964122765529552497759815,
 nat_lit 42011139243728394237076176714513680653622493450682,
 nat_lit 41915912271330166917424544772607333694340299600894,
 nat_lit 41830535531382570200770446409305541273568067925202,
 nat_lit 41735909196154150203197872231788485939470147216524,
 nat_lit 41637080745707951372263200334413583754919004720752,
 nat_lit 41549647332924530711073011831671860388329979991113,
 nat_lit 41473879544982616634330026823789028193024930230410]
private def warmJP01V2Mono (idx : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat idx fun idx =>
    PipeFuseCert.withForcedNat (idx / 4) fun q =>
    PipeFuseCert.withForcedNat (idx % 4) fun sub =>
    PipeFuseCert.withForcedNat (q / 16) fun c =>
    PipeFuseCert.withForcedNat (q % 16) fun rem =>
      let L := cond (Nat.blt c 3) ( cond (Nat.blt c 1) jp01V2M_c0 (cond (Nat.blt c 2) jp01V2M_c1
        jp01V2M_c2) ) ( cond (Nat.blt c 5) (cond (Nat.blt c 4) jp01V2M_c3 jp01V2M_c4) (cond (Nat.blt
        c 6) jp01V2M_c5 jp01V2M_c6) )
      jp01UnpackQuad42 (jp01ListGet L rem) sub
private def jp01B_2 : ℕ := 8192
private def jp01TopR_2 : ℕ := 187519210336
private def jp01RcNum12_2 : ℕ := 635653074817
private def jp01St_2 (r : ℕ) : M2StageScalar :=
  PipeFuseCert.withForcedNat r fun r =>
    cond (Nat.blt r 3)
      ⟨0, 0, 0, 0, 0, 0, 0, ⟨0, 0, 0, 0, 0, 0, 0⟩⟩
      (cond (_nEq r 3)
        ⟨93800, 753417326850, 753417326848, 217492848236, 26549420, 76939003297, 0,
          ⟨286, 0, 0, 0, 0, 528653170308, 632295345769⟩⟩
        ⟨93174, 750076841339, 750076841337, 187519210336, 22890529, 67078800149,
          217502903232, ⟨731431843099, 12251363, 121906131899, 35191269035,
            693170072180, 728361341215, 823095077356⟩⟩)
private theorem jp01St_2_eq3 : jp01St_2 3 =
    ⟨93800, 753417326850, 753417326848, 217492848236, 26549420, 76939003297, 0,
      ⟨286, 0, 0, 0, 0, 528653170308, 632295345769⟩⟩ := rfl
private theorem jp01St_2_eq4 : jp01St_2 4 =
    ⟨93174, 750076841339, 750076841337, 187519210336, 22890529, 67078800149,
      217502903232, ⟨731431843099, 12251363, 121906131899, 35191269035,
        693170072180, 728361341215, 823095077356⟩⟩ := rfl
private def jp01Shr (w b s : ℕ) : ℕ :=
  match s with
  | 0 => w
  | s' + 1 => PipeFuseCert.withForcedNat (w / b) fun w1 => jp01Shr w1 b s'
private def jp01Slot (w b s : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat w fun w =>
  PipeFuseCert.withForcedNat s fun s =>
  PipeFuseCert.withForcedNat (jp01Shr w b s) fun q =>
  PipeFuseCert.withForcedNat (q % b) fun r => r
private def jp01UnpackWK (dMin rad word sub : ℕ) : ℕ :=
  let d40 := 1099511627776
  PipeFuseCert.withForcedNat word fun w =>
  PipeFuseCert.withForcedNat sub fun s =>
  PipeFuseCert.withForcedNat (w % d40) fun anc =>
  cond (_nEq s 0) anc
    (PipeFuseCert.withForcedNat (w / d40) fun hi =>
     PipeFuseCert.withForcedNat (jp01Slot hi rad (s - 1)) fun dl =>
     PipeFuseCert.withForcedNat (anc + s * dMin + dl) fun res => res)
private def jp01Heron (n x : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat ((x + n / x) / 2) fun y => y
private def jp01Isqrt5 (n g0 : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat n fun n =>
  cond (_nEq n 0) 0
    (PipeFuseCert.withForcedNat (cond (_nEq g0 0) 1 g0) fun x0 =>
     PipeFuseCert.withForcedNat (jp01Heron n x0) fun x1 =>
     PipeFuseCert.withForcedNat (jp01Heron n x1) fun x2 =>
     PipeFuseCert.withForcedNat (jp01Heron n x2) fun x3 =>
     PipeFuseCert.withForcedNat (jp01Heron n x3) fun x4 =>
     PipeFuseCert.withForcedNat (jp01Heron n x4) fun x5 =>
     cond (Nat.ble (x5 * x5) n)
       (cond (Nat.ble ((x5 + 1) * (x5 + 1)) n) (x5 + 1) x5) (x5 - 1))
private def jp01CeilSqrt5 (n g0 : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat n fun n =>
  PipeFuseCert.withForcedNat (jp01Isqrt5 n g0) fun r =>
  cond (Nat.ble n (r * r)) r (r + 1)
private def jp01UnpackBinR3C (v2m : ℕ → ℕ) (j raw26 : ℕ) : M2BinCert :=
  let s9 := 1000000000
  let s12 := 1000000000000
  PipeFuseCert.withForcedNat raw26 fun rw =>
  PipeFuseCert.withForcedNat (rw % 131072) fun tc =>
  PipeFuseCert.withForcedNat ((j + 1) * 26549420 * 1000000000001) fun dRoot =>
  PipeFuseCert.withForcedNat
    (jp01Cdiv (jp01CeilSqrt5 (12 * dRoot * dRoot) ((3464101615 * dRoot) / s9)) s12)
    fun dr =>
  cond (_nEq tc 0)
    (PipeFuseCert.withForcedNat (v2m 0) fun hh => ⟨0, 0, dr, 0, 0, 0, 0, 0, hh⟩)
    (PipeFuseCert.withForcedNat (rw / 131072) fun si =>
     PipeFuseCert.withForcedNat (jp01MinAtan200Hi tc) fun bl =>
     PipeFuseCert.withForcedNat (v2m si) fun hh => ⟨tc, bl, dr, si, 0, 0, 0, 0, hh⟩)
private def jp01UnpackBinR4C (wPrev : ℕ → ℕ) (j tc : ℕ) : M2BinCert :=
  let s9 := 1000000000
  let s12 := 1000000000000
  let s24 := s12 * s12
  let cNat := 217502903232
  PipeFuseCert.withForcedNat tc fun tc =>
  PipeFuseCert.withForcedNat
    (jp01Cdiv (4 * (j + 1) * 22890529 * 1000000000001) s12) fun dr =>
  cond (_nEq tc 0)
    (PipeFuseCert.withForcedNat (wPrev 0) fun ps =>
     PipeFuseCert.withForcedNat (cNat + ps) fun hh => ⟨0, 0, dr, 0, 0, 0, cNat, ps, hh⟩)
    (PipeFuseCert.withForcedNat
       ((3 * tc * tc * s24) / (4 * 10000000000 + tc * tc)) fun qTbf =>
     PipeFuseCert.withForcedNat (jp01Isqrt5 qTbf (8660254 * tc)) fun tbf =>
     PipeFuseCert.withForcedNat
       (cond (Nat.blt tbf (93800 * 10000000))
         (jp01Cdiv ((93800 * 10000000 - tbf) * 10000000000000)
           (s12 * 100000 + 93800 * tbf)) 0) fun td =>
     PipeFuseCert.withForcedNat (cond (_nEq td 0) 0 (jp01MinPade54Scale8 td)) fun nu =>
     PipeFuseCert.withForcedNat
       (cond (_nEq nu 0) 1
         (1 + jp01CeilSqrt5 (jp01Cdiv (nu * nu) 12) ((nu * 288675135) / s9))) fun un =>
     PipeFuseCert.withForcedNat (jp01MinAtan200Hi tc) fun bl =>
     PipeFuseCert.withForcedNat (jp01EvalPsiHi 8192 26549420 wPrev (cNat - un)) fun ps =>
     PipeFuseCert.withForcedNat (un + ps) fun hh =>
       ⟨tc, bl, dr, tbf, td, nu, un, ps, hh⟩)
private def jp01W2r3_c0 : List ℕ := [
 nat_lit 1851083747006836952791497660041160257368474206307475048282017503051833974812524076,
 nat_lit 1794430652023545761264585015067200386517221673087676806084337514578282757381183166,
 nat_lit 1737365499984780107622863607896501009695300877870576214226443264832690195279198752,
 nat_lit 1787276870916506744801458815278874298876368983390091257540012053238093469469499747,
 nat_lit 1757563080092565867481918421111757675850353310668656599235748092143681932655225888,
 nat_lit 1700567358083525651248226646569837242348891115781310231343292346857527636003164953,
 nat_lit 1707956566948587012906739080596849397797320927941661341855676772412955648978222917,
 nat_lit 1716301062209672691875076496319021151305311614699965317605407358021067236330530976,
 nat_lit 1659384042644724428193237476143816786654119204817610720346321104465966046458445749,
 nat_lit 1641273659303574120518524734394951401207471693700302963282709203709467258439556476,
 nat_lit 1676427192608035281933506705234749086395837172077148308717752728269477008382722594,
 nat_lit 1619585483140437157016914890116120907594530786427936062785583561602606634930643889,
 nat_lit 1575519123936214917951427971017514048163151913800331181185838004674535599997554016,
 nat_lit 1637925414179776534983866047446004142585869396191493477402815724713547939112222649,
 nat_lit 1581156300932167449735380926707749246198133521054834594346731148451970608074081748,
 nat_lit 1524495968936316298194304364181654025217187819568922192706030981558599591643141488]
private def jp01W2r3_c1 : List ℕ := [
 nat_lit 1600266068516253963132454316285388247301287114368327559988084305549857271157764254,
 nat_lit 1544084283571682520631262438451455674576613208872023316010017280545574200641104938,
 nat_lit 1487493833918459309667579812572814609779966392835849418767695910413561905997871996,
 nat_lit 1524268002750898501999161157705230290624428410749814071860242459271765727966468020,
 nat_lit 1508376894221819752036637795086119598910107221959655423039386564049597254112261338,
 nat_lit 1451853613033809462653446540955856584280368072033557477474862911533140036192427470,
 nat_lit 1462456278843826851541168955734998876691546784559903700688129847952820459723379951,
 nat_lit 1473996364755624528880797609637025263802216829858528246960185889035065164931926787,
 nat_lit 1417539347407049114698891776127276071601198676001907999032832981378728350502561486,
 nat_lit 1415134172596598743908643968031378528875483549721800195133567886007609363819401736,
 nat_lit 1440907188610708671817118933377965121591341310738756484095887233795712879069060490,
 nat_lit 1384512138129021312714378239229757377970126690496073503775226600165835441394681013,
 nat_lit 1355222841314696693690840723454184268041298890791313194059576939224187706013285500,
 nat_lit 1409433900290735969319295113115494412982079516176662145026010524525190617012340421,
 nat_lit 1353099007424353612577784999546737304019341792748349445544659242902374651979094019,
 nat_lit 1296870634245243633672453963364459378643393578032293736354360352001837936497130241]
private def jp01W2r3_c2 : List ℕ := [
 nat_lit 1379279330222293595075499917844191240136853339484343148143177755891064571321702508,
 nat_lit 1323000976468050135278634524971182768289717205846126026090452076176979013754350794,
 nat_lit 1266830499339786562809971738799345721878928416937152983799404358341968828264403964,
 nat_lit 1349857054728175872630263616280162377702092123170120101479488124821405069133910030,
 nat_lit 1294146353665926847474693222890379428792882275538837967431978512715326980470765144,
 nat_lit 1238029927928865364486728833400168211154949588617310314120579278192994889860004188,
 nat_lit 1294045487548353153499747360052429151921952136886948163315481297481596658450551367,
 nat_lit 1266545542214606522225160283909847824471314663807936715770827641868492379712767194,
 nat_lit 1210481358617164076006387484879331468003551505032589834684671989057099025753275266,
 nat_lit 1253217237562345861500021816562782882578413112628022859280488176946431480854022416,
 nat_lit 1240160547830737212772799285032586817522042466942760354069699543173819148774804690,
 nat_lit 1184146570964852539078755029354881102619042697526033458202672091099526157050957368,
 nat_lit 1199115865437716944338799900708708235656501779804053753889789906364395158024841079,
 nat_lit 1215003130649622241728593548099174368040654226269376150946735609439692046735939910,
 nat_lit 1159037325107287996211362966418626411910536718787032707460466395650671276050382011,
 nat_lit 1160191174273047077271601445072367059703994228913928959080551626939574328607258868]
private def jp01W2r3_c3 : List ℕ := [
 nat_lit 1191035748700812165495029324716358862441503018212035645474200687872456408284307713,
 nat_lit 1135114495978862242734812680677624756101904715756295902900129699644917601285750049,
 nat_lit 1119750330344164369429735768608225355162728443325561740490224936219913264092197598,
 nat_lit 1159946474030481459029570941542262560782447264485008419742115919637477091107416745,
 nat_lit 1104084700454509743837668016817149469790436297309955511358097025351343069685741608,
 nat_lit 1074235666482325834007133955424930584502687830312879146756116401185223862775947365,
 nat_lit 1124596411869336519108003110144922902828468495665797720452497339105566804047022317,
 nat_lit 1068801580602126473913516343394671188455220399168703278387379467216115331902666456,
 nat_lit 1025915305731930487025914022753140837907129843127586901771833499488092046223343814,
 nat_lit 1090488627080115510766268382757875004254970121017446259988712214935367736900103099,
 nat_lit 1034758250400730328111679203294769611925113288343622179824058448750237275042304428,
 nat_lit 979133941095741980070571947839262903005224310001331375619877001167474212873950426,
 nat_lit 1057609097963002595578700682163583818026217616528060052462052120529538443555182127,
 nat_lit 1001941366619886182699169434022364516263754112285963366827834908830629007798520699,
 nat_lit 946379024181785889737227318311523141140140882147845624125239884632577514483834677,
 nat_lit 1025922544112033885828657370209403819679254917955319351370700060202963174707704835]
private def jp01W2r3_c4 : List ℕ := [
 nat_lit 970315422697124978479721006283186480222636381057341432881724576865402637432917845,
 nat_lit 914812785561427184719286796164922238979850519828310407730425407152609525373848123,
 nat_lit 994933230585931111656223088459058173631506711940751554562258840760212047545984689,
 nat_lit 939889238733964647337196421434296262023406727264775457795645755261319390031836710,
 nat_lit 884444723805564511596505675099989618965851253865660778690274214538060296111156995,
 nat_lit 951925963226165237488890422921619356935778175786131001566005890871128753600187019,
 nat_lit 910651733064428661459956971077981481983544908520338703089059628365443613901602974,
 nat_lit 855262626465911164748534876954964039189276317968074670057621907613986438828363271,
 nat_lit 923688069058085671553067427900805383638331204309146842268706774412667266405809961,
 nat_lit 882565589874491868893324723281120195473977880295789368362661714054313702644849905,
 nat_lit 827229856197849666863256411630615139262705774949445990853283094325262361642030278,
 nat_lit 882930832200790891385588253510070896977370438034405651720636983874798529301147992,
 nat_lit 855927526424691552729642632141895711594949844783757980582561778347959208910577946,
 nat_lit 800642451792509626390453291774358574933129100840572509430719292269528455064592094,
 nat_lit 857203048453986940227067822675531301248494471805699857704110100234243798644507220,
 nat_lit 830450550181759448183327416375453328104761236556817448021010189239297229250808233]
private def jp01W2r3_c5 : List ℕ := [
 nat_lit 775213420716676698441090412320075257218761883300580269173444913893541158215230314,
 nat_lit 832597226848631715681752225108468839208630471201740683589114901391895085676585927,
 nat_lit 806084680570615994269034525690971616543541524090528378398152782026295934554413051,
 nat_lit 750893234708146865242878748090270361855235083739644508445044736487153229693362901,
 nat_lit 809093013304193455141798563272163978327096617294436592217778084435545140235998506,
 nat_lit 782816122047842684231555536918115240301157377278646815948079808001157302642674475,
 nat_lit 727669455162209129545488910732744508951514937386484132111324169108323418185915384,
 nat_lit 772367693606323351102154950662633928222752470841439870475778632566481448079562009,
 nat_lit 760659348626211779572110638459251576081087143819918037691441266246336100785121911,
 nat_lit 705554294527096277063080171626225845844831719882050776802297284329069523070817877,
 nat_lit 750959045713111984694359978914041103042804589944944364011953448492382496246410065,
 nat_lit 739575913709414910470764802019114847842497706958786919541121494355002919396239988,
 nat_lit 684510889301685659013552777795413965671625396751230675302010971141513135059994055,
 nat_lit 745116520190721211296679027585997863438395768016677981512087646152796617358445307,
 nat_lit 719528953796356388085657672702039423746338933265404260254570711185328251922498188,
 nat_lit 664502602141359798078360987347166386486859674955943421188978295581441687156973830]
private def jp01W2r3_c6 : List ℕ := [
 nat_lit 720317334838525690204081922723481835306486025610393516317036744306722624910223900,
 nat_lit 693570490474479093131307904648037058609976148281785865007855791221576640969754741,
 nat_lit 638592762455881514570427142702999905189671516818032437698636009190585829243353542,
 nat_lit 690817940012405626832119053982502552223804247560903603439214021617031486527837857,
 nat_lit 663217581200634596453020751916991653574688871900441975304891560811281927216841466,
 nat_lit 608297523076459132698827929791957195465455945690817690673469036556318610491519911,
 nat_lit 661332793029477076217869052241254874122863889227682705553233842661570150781292790,
 nat_lit 633975778558578750403542047796264963356951130286359497464916368065200014153944442,
 nat_lit 579111807233639680424629642731427860387877889927149460481907471705576892862157470,
 nat_lit 646576763390801730506300253158629409396639954417112020354151995914505970891392373,
 nat_lit 605809575985869455739700666574666102274239674971033179818797230570614095505281640,
 nat_lit 550998977582778720492261016870904807433593594822084885433023432063529278245240947,
 nat_lit 619353180894561375582483863816920191753087598375462759921988942733169840594459956,
 nat_lit 578730055148456280316826535828939232570659327809831044443562101491910161956300062,
 nat_lit 523970568102755283873083435211849940502437393859477504007906620062746594473283764,
 nat_lit 607017251415225104727784626253919211858873865677344393969649030594772169811340281]
private def jp01W2r3_c7 : List ℕ := [
 nat_lit 552702614109756051117383686221549405442576839104295048739881994571806771387396562,
 nat_lit 497992429169834780819163177446282596312533243291660288829999432059152884479700721,
 nat_lit 582006609769220014145009994441149595036158333663464566108855207708455194997218478,
 nat_lit 527738560692169587586205012046041233889274825763294322669175523653353215152473952,
 nat_lit 473075868606418030768905385307587495872592085957367885121106775681515102826965563,
 nat_lit 558658444182534854807232199849692120628646105319162397435290164827771540657694793,
 nat_lit 503936725263707593587769281344650714360665621096784096260220189994855990063896206,
 nat_lit 462955592226755469400293306766896118783156701254019659258210167870013494502536505,
 nat_lit 535993949533856215690523717635454159594790314024641184819533804663548961029727718,
 nat_lit 481315426496732727679504481625687116843370468559048084172582771405712100374160790,
 nat_lit 440467273441820315279040185943258323111434287875746320004738857561365715595073151,
 nat_lit 514357788256805666058393013585405673019325387461544281271585575516950786207243607,
 nat_lit 459720425693297727061473385852592241396422328078752647132326146289654264312873469,
 nat_lit 433315075858010007110483677579629973185313898128080010266865792581960576929470627,
 nat_lit 493714001476011643554851383035279899331549259786683117034075843978589806786396226,
 nat_lit 439115990134563160807191707614159847361159606577279247094436306025349898845985975]
private def jp01W2r3_c8 : List ℕ := [
 nat_lit 427326227107076260369667968220413020796796023456497373900708676721063853992635372,
 nat_lit 474051507525497620371473994442130209832970041976635829668724159780075301582604828,
 nat_lit 419490585841623037995417037946863245048379233633245982132426779692674167606735109,
 nat_lit 422488062368517795555282039720870130797253288277807923550702308723666604685577059,
 nat_lit 455358998582862777069855706455695768731338116744565949001665242125761834745886128,
 nat_lit 400833809617854585573377939188465672722658324960664117757472831404372585979443579,
 nat_lit 418787916881253236609800530636286000343251385994046319415468258791002061760852328,
 nat_lit 437625392982103625894904536510111395096591471809751674339783007696812956722838820,
 nat_lit 383132996702149474601004110875964433207259407534127965873466128937880791055790088,
 nat_lit 416212899727615163216980728352422535603867867318140356209252009142380774821664686,
 nat_lit 420839156744368095828354005570117605811367563302716658098296277809433217814370794,
 nat_lit 366379553149441024783936017985975242475383651509282563777004958770272634776128999,
 nat_lit 409870568480930413861358764689789185446239586545416551679723989543538354165905221,
 nat_lit 398031052750870138453744754538107837675959513496650330300443157452394375082566790,
 nat_lit 343613966568266125921877657105771264980553508980428131208272962821352578903942964,
 nat_lit 411409563453437516929200180606767213557912389677143419891533836140387361620025362]
private def jp01W2r3_c9 : List ℕ := [
 nat_lit 371070942518315881330434613495014388652429511286186554683276421516537584921295180,
 nat_lit 316705420005977150818533465201822656482758648620441709233832875563553837933558730,
 nat_lit 399033830437872168860416200685005557334931179613695685361228801074926847989233011,
 nat_lit 345110443788377322131621798334127849582592198624243338340958167178114053313596425,
 nat_lit 290793997225394026128835179132160524706445723992947110948328388679578056552898901,
 nat_lit 374508520536387775322524846286905776214548933812633162525726986119319395388265635,
 nat_lit 320135987174168085541243933553099184758755023447417639426807335546726985215907952,
 nat_lit 293154164591793038265595750703256337415034980520615662379787671908693333876249414,
 nat_lit 350441855906691452004998577954615639756225321356104492594554772053013545938046538,
 nat_lit 296115232303509674576206954809207916703113710807571129622395396762785555216435423,
 nat_lit 283322465462198480606663763463515935402306668563821052165849776340239759636118364,
 nat_lit 327342462407459289578756597890124629011887233906679246941737313675262321978287263,
 nat_lit 273059713155281120207872244337668087538689498273041166765104187668059475346499677,
 nat_lit 288674910458527716971253800970462008593387381841323597992194451841529426100659417,
 nat_lit 305176416571407949875726523470450591008987610007363847514071358813515209258976317,
 nat_lit 250935280105774792634973232853417586215171020834940889533108226989667966737752799]
private def jp01W2r3_c10 : List ℕ := [
 nat_lit 295365297008032780435272509315461639721853996919022505957023438187473513745152777,
 nat_lit 284048202677802466387386438814937898437392866386372553577371127782672983903234420,
 nat_lit 229847095903582520145118741830148293940518625164521006101070029461059015368619698,
 nat_lit 289261334627833417284075012004928979735641251113475750801843623360950523599683130,
 nat_lit 264015942933913537180384904507589544804737641547004962427491725742336877601218710,
 nat_lit 209853282755948040858290181595192513767620811462284012107988290314143251591016770,
 nat_lit 298617427244462211822719293745618422075090756344552816970520043607010853051071731,
 nat_lit 244881976603692794572669480497731207772610479544928295147997862064256619456258004,
 nat_lit 204687867975982255217745938861378809110170876254569851417814870354573804312085758,
 nat_lit 280829996414829492528047881995704583058930579505555888534143172631314981202825123,
 nat_lit 226635448177614962335676672544291112095045203640377719378177815045671214266884029,
 nat_lit 215568028838063408450481441870091502017062625398977537132502294979048420578634306,
 nat_lit 263427483854766505823353697029846250676864115654877523593335749325206859607151294,
 nat_lit 209266180615481559049829229647112636802104233019628987125951810263041973405538364,
 nat_lit 227641843498351570791734338499136459851230409573080947528251154261254882661374150,
 nat_lit 246893638213608227725326369974549740555942603783225908794783738305622733784560951]
private def jp01W2r3_c11 : List ℕ := [
 nat_lit 192763770720669811652714084729033377183775545000391621967577544308670446097744025,
 nat_lit 240895742511052671393271061272030964656976584406302204484479790619176160411731872,
 nat_lit 231218056294731885171552833369528671425807695364510408611085095119020107870318052,
 nat_lit 177117136827203192342334159956638434869265679276926915411704094189556049534390136,
 nat_lit 255316382645596786769484600068646227043172119434961996615499615366829756032937278,
 nat_lit 216389882588612201939897346300119021807856205570537767264435581033862352834245364,
 nat_lit 162317684990041980774210947034856173397946749821533941628515455788159401040902868,
 nat_lit 250069553220709394655189250032370053625505008747881179225570974131625515530464242,
 nat_lit 195933579503668065698830904800510903816633230953439675333659514676098500289131434,
 nat_lit 168955827748523047561498041540993340022948340783740224421525965890056345401603817,
 nat_lit 225546278721355075684095947031377714469683206873275798045853953528374422838425805,
 nat_lit 171456214763378619030107918499353920174199831672703435229760192862819088414027424,
 nat_lit 172388204491088546410795838871993250055441879765210206651543301701908288360718554,
 nat_lit 201922428417925201224450946340692871655284813785816220860766613305558185629300015,
 nat_lit 147877821906084153753587903378392687226711842172705771750609527342573156027886133,
 nat_lit 190950900124961801125757465346368816555494505557511525758814036156320573013302398]
private def jp01W2r3_c12 : List ℕ := [
 nat_lit 179164304999560724741376051999413741334933349638903010178581633782285108835600922,
 nat_lit 125162894369396490529075664420951341968351691786918848749090747903220642681343684,
 nat_lit 196837074342793899551705138956732751809485021096327001622740727092808718489440644,
 nat_lit 157286156322528736250040307558751890411131863279290690814314074725117474134408952,
 nat_lit 103326132322458262584795768759072423287377286239061671246032382172100232004576254,
 nat_lit 190300474682996957714622206308269148196479337921568143956808812100294715020767967,
 nat_lit 136277579190233422641125549524623449739835239940956735991084155566954584267770650,
 nat_lit 124385367310576479851230593860387256160183698325399780523928450202785720158462210,
 nat_lit 170088872875395359426687439403835432222357742565176109393349536692842905610928431,
 nat_lit 116104650135337525856438970466098980773615851152514709496571755551907946469726575,
 nat_lit 133027710168565035577813995192380200328750499613372564560014192404726371648237592,
 nat_lit 150828258933983487666953047860336118236253273806702343358287554630223183060501567,
 nat_lit 96880221225667588189339292114591392765649470420729234241178677691244459238387350,
 nat_lit 157343147399544101849078524763348751937402040580670077900285615386593495846967302,
 nat_lit 132543962380978000309131879660492960400380933331150520313016934186091245841608844,
 nat_lit 78630300452874902112408085107682195886309794266896347321647950595010499726311301]
private def jp01W2r3_c13 : List ℕ := [
 nat_lit 168580183201201067671548237482137561463963610612566335202715439766884298688433727,
 nat_lit 115089433837747228421535194863222282724181312348087602077140095938208651739810479,
 nat_lit 89741817693420017308722214523514030656341048279870153957324476587044539052494351,
 nat_lit 152380822953331077655191482237408038529535573485614123421802045325226706164365631,
 nat_lit 98429845211202827503789754985227513281520794122579405560877364419241482963697941,
 nat_lit 117017416686388296949344101148669001571158848185515305322313666602594321185359862,
 nat_lit 136477049177837883091231521629075892761470777761562647552185820283817237024911044,
 nat_lit 82556376399826865678460811995855647618121182477049162939489605687424061138700406,
 nat_lit 130862262499334996090427779593768429806260489648252257938900194784009518221648326,
 nat_lit 121375678481868441832415052150541018518501817868609139819204723271032359367351706,
 nat_lit 67483727572815896079962740576430180970700858737992997487553716692125300805523559,
 nat_lit 160518610435918490299739871174743708551264706326279452443660692813055772245857118,
 nat_lit 107042787398058535857812733372869707368732796142839887742708823261765119030015655,
 nat_lit 82320946117813718670521906983699451528839920771307070872873618734197795884294440,
 nat_lit 147410130370476590244690940749822345724778838610371159123855788787903483958363027,
 nat_lit 93468651199193066766854699648890332241738670094601076267322088195225473774529786]
private def jp01W2r3_c14 : List ℕ := [
 nat_lit 110550020745061490269490889509423130081407319377392290577915587245947514599953818,
 nat_lit 128507295930685050320949911866586954219599603226961786344777447274357440647741164,
 nat_lit 74601549478267917719478983905173874633318138195233360640558861569964718130757941,
 nat_lit 131360259192389615987939855188717817611250482715108479544068709169996220776432485,
 nat_lit 105674314727845978292111089375970272458633074971231591689049155860861902514777262,
 nat_lit 51811990313556910532278030188787674922152282324688249951564543177482906017135920,
 nat_lit 137574586422686238504215540897296391522513658245771373111928220254457167489234728,
 nat_lit 83651652080189665213787597495111877352119509364345230139713907362150553054176692,
 nat_lit 71454355162757110816673207357197183819331556773627216251834093098856146308387795,
 nat_lit 116312714068008666600904477210811731261714782008767857580929358056351072581125321,
 nat_lit 62429583260447092776005886555917365385548860650785764091715757088522793784270694,
 nat_lit 92812570663240751439213738360161545882611607795550263242535396759715468323175000,
 nat_lit 95842389283248691927744205933508582900344165167195563091057957517183049136126162,
 nat_lit 41998835854170865988513630724029648881675592374761275648975649040893197612191371,
 nat_lit 115382532420175270454818823741220716428489971839310128956090431314373554250868057,
 nat_lit 76156601218552315168449865441602760941459794612987330442445889947030018517288865]
private def jp01W2r3_c15 : List ℕ := [
 nat_lit 36122837530011519443476570668248526772577038453905461174642423143456183401588572,
 nat_lit 111118126601084147302337792595763404779547241103426396974815681432724925532040469,
 nat_lit 57245172833694094950349302301230992858215547374882709054899296522043532113569026,
 nat_lit 74684548034210187829001264887831101345768944382669793421265890584805649957477750,
 nat_lit 92997115003941186298774006836739052547684600539585220945106536687252076823911912,
 nat_lit 39158763173188226864083540868862562444011735824968351300149648261022196331691411,
 nat_lit 100334082158262445028254899611796546159255816075962441707009486019197123666271852,
 nat_lit 75791584710572812533334373927412729955042920694133069164176012006669823372803110,
 nat_lit 21985799408422641714932158964336858094675967954829293904757601283499291549308146,
 nat_lit 113209395280896539335934415061722789166235137673809939075667321910491430629499297,
 nat_lit 59333049166791633147221402185363141810690626987474719984131781033273848904384841,
 nat_lit 63366774534853576484492820509311582752796419230879751009188415055980004031439207,
 nat_lit 97432947585948228670005186835939729557099729636873704763734676465742550558746120,
 nat_lit 43586227966606800470697550257990341661786016732707263153222562956334848976984568,
 nat_lit 91850275123738746090641032369619642073677598683536078095712299473155777399131886,
 nat_lit 82387211376312678020318706870568817686069253620863508205604302892177203626468742]
private def jp01W2r3_c16 : List ℕ := [
 nat_lit 28569213625929721481329467968604952169837406799527424288663639844937499558099872,
 nat_lit 121465462586086612367884601305750469238715443816536025033260914912628844416668491,
 nat_lit 68062688081118200760214585431283051894106579381480018244027045400140949290471589,
 nat_lit 58151380482917364706690551321662908058090604113489234809285672365711281809299100,
 nat_lit 108292980245695392989207484029279553010547689108893882973640439939544674949223407,
 nat_lit 54426132702435213474059957304168417419977789269823298886495879375634306240943665,
 nat_lit 89311442647454023345087799361014763727799111263699486276723000458380475145443607,
 nat_lit 95336024994935426915599055075905063502105129337439182357837381023309820004899384,
 nat_lit 41493828504565110471605886419008144549284349324622705872445801130247855760107090,
 nat_lit 130774288165166736244204842796915992905278086586674069293634978980876326913782664,
 nat_lit 77354325770091923997696784753364539082317205595800349029564258132348279119061436,
 nat_lit 64978817576487109238412531789976530758058464784519520596825735255617366057818168,
 nat_lit 109405896129040136379641712133216587864612853902712986271513042867053326917258596,
 nat_lit 55536560864843149403761737865624555370790660663017033915999893779837257154110666,
 nat_lit 85527845301968332434292319564670818837907715158142083479290820568960229726026952,
 nat_lit 88301880975448972746186584727197412400648583058447754615665027756584572808032358]
private def jp01W2r3_c17 : List ℕ := [
 nat_lit 34472349246186985239049840061661370528940748406003850453757153061092201455007453,
 nat_lit 121322531710594088909328446313968173438618976387692920455921689595563274680663726,
 nat_lit 67920209518528180467808857986534103190299702816871884229738687163402726863059281,
 nat_lit 56193996471151264764562400997084328589773517960831818846836720727159296652311699,
 nat_lit 102108053690548650856633745526632223903118892889876062085444248524390811227262309,
 nat_lit 48252287813264999146697174255949690788030791298828821443755971536168418309397030,
 nat_lit 93754738591128102126527977080174904046486470087464194087875218858984689270564802,
 nat_lit 83109102760107506159126706334080053521167615994370910609213747824026349135962239,
 nat_lit 29289521914592748491705875366825824838792371944190645949493169012329549980337232,
 nat_lit 118229389963680443070363387725195744303637697898905153020086745141413772956232107,
 nat_lit 64832947839266195929514645610587786943872903388405039269663201271477029239777675,
 nat_lit 53755125312042573415842213367343615298102558943354098194383637642264871146910246,
 nat_lit 101171313680626014340388537628391499610384113172501925220155431852777721453664058,
 nat_lit 47317130898474163758883558806123260549843234509770625358767023952437672007701039,
 nat_lit 94422352419073763463925437217759769093704912469194006659902653025874998589083142,
 nat_lit 84460839853143126202021762820365331831842625360170373503340019952306955514959009]
private def jp01W2r3_c18 : List ℕ := [
 nat_lit 30638545130240309490793270153989601809666466778424532440893571662617562732057120,
 nat_lit 122316263151408435354749086649284191109295144180980786119780296295917334384034817,
 nat_lit 68422276834321585307714754696601827194190601187395785041992901902385044453068973,
 nat_lit 72609110115028058829823183774894344110660506684119991873102666064524850387279225,
 nat_lit 106912973596603804452144457414042099417080404523849995764305469297148807807930913,
 nat_lit 53047709148475426065428523137345257881057727613095352457460777821120782571551275,
 nat_lit 116229035826171718268426719410796713000015649117986110688479730316619108606141153,
 nat_lit 92165537742583418120256594067001447113216882786861396000010966673287105660481397,
 nat_lit 52592454687035565371350497939136802525620440882161691759407820207732212506885971,
 nat_lit 131979023572491534060973864966459005063600514019595193918631649557883475175507349,
 nat_lit 78066944739520236992681662862062534604071153365137189507459015152063585018382803,
 nat_lit 97847717623551587383648464764391973128977030363248960274612013308920121511677401,
 nat_lit 118496028422375094872435919355398036552288184131632232340584673671311427681127030,
 nat_lit 64609052955196164041448502483125153266462097358306542961495781185174107435077262,
 nat_lit 144229013581830715570892843428905697271178025391595524039406511667660867446575848,
 nat_lit 105646045171763049848062092135581518721266030237808482171541672595548225483545194]
private def jp01W2r3_c19 : List ℕ := [
 nat_lit 94522765197460419789729160183259621798979821094360154957580944298386517211687522,
 nat_lit 141940536662119260201028714560434049807857920588490313126404124767830249239385625,
 nat_lit 88009008374556006616241236517989228171000378671416933630933883311316300026140566,
 nat_lit 131905522219014611320788096219703494890670288398101263493986299674647683609335933,
 nat_lit 120532793398082894262397594064340156509323582251711198126771145285925324445246689,
 nat_lit 66641973271259646475440323863252177359262560549512264762825020760473717324746666,
 nat_lit 153761960384651964157749550225668304848816628908359025733690866413861641726928323,
 nat_lit 99808268765162614909207312680408807052884717005687307181978869990407237721540566,
 nat_lit 102130442159758891231098067697476136743221231220382655246821711428817010264205542,
 nat_lit 133674744623755939140962640614269385362145481346466155785880157721022568109525434,
 nat_lit 79759047287618536646442949594369113929686834234560798843330380327752104466116143,
 nat_lit 153483335464597673244791506923924850391177784809399152762350416778641639802442331,
 nat_lit 114231622428367796040217955105214300829861113068471758156691796312670913830045837,
 nat_lit 88459284494013347680647586561085118886709938171500880112244235506305783918492577,
 nat_lit 149394653206565352865461024999069650183576319693505318595310716067371973617322880,
 nat_lit 95449103219213220798460743524118514854332809150620241099336078036594133002738330]
private def jp01W2r3_c20 : List ℕ := [
 nat_lit 127267279432640516123644657959677124156851771889262499112714460989282364091836634,
 nat_lit 131230219571321286973354273665769283563708478224868136953072956922052869807290272,
 nat_lit 77319497677030539450418450236270387938649933956723584868103353100546899054407076,
 nat_lit 167725990300865010487933674417005179602690869128184530080816189894507919760036941,
 nat_lit 113746743002653831889269073452794034849752906258106657894450429739862321694916521,
 nat_lit 117421784247846669131285044310628918270651707048551063688098205899511140433684871,
 nat_lit 151004434807405594544355944537674340237071408766652357771376341832871847193964655,
 nat_lit 97055944786214151850472788356332846124752784030622963293515401011508270872813087,
 nat_lit 173834475796852068331037600175584212328133593342839771952151486059291235023669990,
 nat_lit 134887395500943352681271395437587509408890569321531724075407726402680375595369553,
 nat_lit 109758924943023991419476446815679418269673928662129246515114043238474543386836944,
 nat_lit 173383746174425981543296730977461151860593881985661131952103019687593800356882701,
 nat_lit 119392738740911480340076560732831893330718329784208868530835325949233819754495974,
 nat_lit 167892893228378166992745219994907884687970588857581594564792383546069088749065479,
 nat_lit 158450183563263218444171084366237042821148959682766828459415813958138329014866063,
 nat_lit 104487671842255937321407974878842429778170442605119242295647677225184220551416755]
private def jp01W2r3_c21 : List ℕ := [
 nat_lit 198162803617099366272732663644932564620600480188043926184547943074749456248077371,
 nat_lit 144125207955166238021130412234683772260788270160827101738178936748820438837127636,
 nat_lit 163821172170490483864481347571341650537196120922480761809992791516193237314229459,
 nat_lit 184387162022541212537324583598180039755853130235931662838040704773234366423709407,
 nat_lit 130375348195754205269038881885839012886292449323040647665044013527053066667335362,
 nat_lit 209908464746105667158898703695942285216498682515029495509972436135713616966845577,
 nat_lit 171206538044162466155511348819217678678656809983639940322407521041047171707792340,
 nat_lit 160040288342315718458743112933553578238126055282236113857305548987201455253477712,
 nat_lit 207526132900284082795901729747881149372781030400098123882515516117627709401735695,
 nat_lit 153470218566015255939966394029277600360069214990351894180624228119588138980295050,
 nat_lit 211549003465980319606437825687839226546338535894064179956585662024468481204051474,
 nat_lit 186080395352895770103248062343304144494301212682965890486143021700854063700638570,
 nat_lit 159841948993702332177539605081417829703650103405424140915100500712977804438373240,
 nat_lit 219331047202091100812891191292894036145982163238817996731430324454086521059401010,
 nat_lit 165253421848771721509470496507072533943984632601515445022150849491133521616297202,
 nat_lit 195934483446820099702212922347240888571913726546262928542783912570102872792750421]
private def jp01W2r3_c22 : List ℕ := [
 nat_lit 199101352878605055500484677765104256516021833746682679804241679794848180302020477,
 nat_lit 145061721808637622954300406359407823005378254446083753399313581558977612556205802,
 nat_lit 233580712712810982527231384582842250497329773369384502642093008377190911616117114,
 nat_lit 179475948585664932691923884569449519970797599577567534019541961263325394497927153,
 nat_lit 196557544286016531198493422199076983075770653067924573736680332097248045421855367,
 nat_lit 214517533350996226872901972259784362508535853782198234584443798059468047401045529,
 nat_lit 160448728099167819497034998776303262866566297579961947277543371323695760189354598,
 nat_lit 249687801129675684722578105992304202419392072703030670379902780084850868075008897,
 nat_lit 196044622319911555287110573253276759689961152602474598181853671289280267669525714,
 nat_lit 199287930909694222993061602366741546209938270378389349195351542557998092157131309,
 nat_lit 232305868812311222274563303352778651888812744681490878906601354361384508405199785,
 nat_lit 178203140093199476733837823717957493401510321343358962895337717445988586904037863,
 nat_lit 254318128084411553606023857797112446833427112503888470892810027568135322759863375,
 nat_lit 215163436168060201550569975089498610050699000585772986721773987625783599640792744,
 nat_lit 204338230378821428758325674723125861866725031022679177231535309494458175193775931,
 nat_lit 252731188463784371027773086296000445691266141214552272831931763075356344980476738]
private def jp01W2r3_c23 : List ℕ := [
 nat_lit 198589786991966923983799418432146109307663130127518360914304817346750391484976523,
 nat_lit 261118200003769720416878855443572494431315477605024321081012161637896924266169152,
 nat_lit 236689006941796724710452465345251166303700365878248623109506459535387334721556548,
 nat_lit 211482964716407038641057013290140105728817428687956853577103814652393404781271496,
 nat_lit 275385958385140071937959841474036642957427756715512680036844177090247534399967330,
 nat_lit 221201813344575274751454972884814447062692347726597326896480309753057886799395087,
 nat_lit 269889225369445559557714591162798676158802156582503802331546778047482185968262233,
 nat_lit 260418924619596473840126115875381845608598676813730220099966585078864878830889442,
 nat_lit 220586892423995565188128496663343889549202276574814228816409698034724152824510007,
 nat_lit 300225625756047922147871685467946596477848647257673154494097346142664190031574273,
 nat_lit 245993761704808239997608667228645384228935706909681152370848738708115572869182869,
 nat_lit 280591400646584951415858670396576467085211863084302299377112238594910410337955806,
 nat_lit 286309314850482800831564684198376044840054827991501180022555647269052142286086917,
 nat_lit 232104815729521040796263684577038803575417500531967394425960313243332213123717944,
 nat_lit 322322467718825076022733464560716453268946716375846767102602715004338503930609310,
 nat_lit 268048764724589130162478046084116987903932639645782943748021752205483622052635390]
private def jp01W2r3_c24 : List ℕ := [
 nat_lit 283789931168271183767717923070597586199537487372155271849086260321583861336326215,
 nat_lit 300416727955063913836574363817091938363808745880990108242517708439309855532811024,
 nat_lit 246185316216726734852461772741700187994707737288477510509951037145507701542258502,
 nat_lit 332896186308780460534102932479884072511401467098989317718013720524031521401374003,
 nat_lit 279096507236637432327230746101491140602078547607683679468815352721337692776362830,
 nat_lit 281205641254316477110839550263067426074264735407436406906328849133013314221204089,
 nat_lit 312609048253254741678962564703902937966575180092987572589369992647328591500709299,
 nat_lit 258354342400735209118933022112878940353646677864420558638595006244529347829791114,
 nat_lit 346199613238732979055418555248701139365546492263541268608333687611072177760919206,
 nat_lit 292375283113700087777392011185217921706878278645453282717531040005620025387501950,
 nat_lit 294919994443063624919386491499437300848262029180344239689999641735993923899438318,
 nat_lit 326988527565456314748852061447239223940622165946309412390940858735596237684041190,
 nat_lit 272706004469729396961042921285175425127165400046615131750318172307600157829587691,
 nat_lit 347318182862055470051285572347427363412077248358896674902334377283815166405859502,
 nat_lit 307841670317675991624418875761021362502258242963531713869523489489613949364007317,
 nat_lit 310827839026186962757019427148934594460123314333033962973567350974236958274454234]
private def jp01W2r3_c25 : List ℕ := [
 nat_lit 343572353781748073741627621664908237644150957732863454175050454257283313298629442,
 nat_lit 289259073409028379995704187359769455205161873329794332970345489068486315310455638,
 nat_lit 365034826727568834937874579891498807634878973771843279135821671927564655960738707,
 nat_lit 325657370709241949191161199126790906189043628634749335221699220054836177764234570,
 nat_lit 314568014189524519389987012140708769949116289913251114935529198531580167535859973,
 nat_lit 362631010014591717640642566450037587578861214646042252083143245820469430295059194,
 nat_lit 308281092297200626686052964677561084499273507537342944370939677921616776475475233,
 nat_lit 385031127594792124027476512504046411006836135784457029903275311311586710299285183,
 nat_lit 345729207831641586230497899519349404366220277297445070643802420662748612970380427,
 nat_lit 334936568563079375847853965163400264129043706419100180018816142052310598853123481,
 nat_lit 383743619113249561568457228496317070509288878525305683077559092809616077437150174,
 nat_lit 329353445548020967982187846046393141150784971849273441928635013651784652356474653,
 nat_lit 392353394752891888682660754607571068833752985792390269915859648179602153327984912,
 nat_lit 367857485540765270809485737604102353987797301331191894418401991147979408447605655,
 nat_lit 357354552673585160388371906536233217492237790692847926092623023830928729244340489,
 nat_lit 406893219344066456469308778641931461728424521367178808274738278146773523188777610]
private def jp01W2r3_c26 : List ℕ := [
 nat_lit 352459623740709798044615403889418870415744469970994599086447385573712886543642005,
 nat_lit 416296125646170026441770031617454576152031073200167499262677675981163527895338624,
 nat_lit 391975035371400081350847217721189685437961847846986687288263572225623542657720389,
 nat_lit 380352175800838936352405838787482473710406922137681676317857644025364702611959782,
 nat_lit 427344546987136977792124201528219606008756547811019735428051044624476315708658171,
 nat_lit 372872278631074617860968762458155901920618151071967398993503459634485525158101390,
 nat_lit 430538780325260837138408198912265565959605918600289745759730208931900821772723781,
 nat_lit 404659924414566547306242979806614564294726144694397282387298102305803860723909625,
 nat_lit 392115703497490150431911743819291608823656798592086188779122072893536003546809494,
 nat_lit 436997130368021595072343976285077952674495162912050921115412995027631854483112587,
 nat_lit 382506091026747993323799929325828565619628470504869929882512480403958432747727231,
 nat_lit 455197522703694087690821470917110285671794483285304039444291061210294755891856700,
 nat_lit 415328402562368256823925020847104962639246665266183431301562325824235474484027212,
 nat_lit 403092659032020001493987015484935775556571019081031186432898807322953740895120023,
 nat_lit 448717236001633747650520747005390027049307875260599601527913894744176865662876264,
 nat_lit 394204711797733885087685527257878896682253278954214331656645789271835266996453381]
private def jp01W2r3_c27 : List ℕ := [
 nat_lit 467851428312095488409805184451554335744903626361045346707820137629205617594087938,
 nat_lit 428066890683834309093868752450246208389055132344910973804875306390817981402367144,
 nat_lit 416131482908130898042613458990252866095685891232302057484435187953896409556468212,
 nat_lit 462488580623645081263808546176294108953530699419603650326513033926051421929704138,
 nat_lit 407949143802369799755375611446370335249574005273677459696686928112774068242454023,
 nat_lit 482562905289450234630721199813325922443857680954455420265951131713394044301841697,
 nat_lit 442861140922670654160665732985191822601338318194929297529075220595362482828162933,
 nat_lit 445738980689630199436090003761324738089266254467590345798625128838356609713688017,
 nat_lit 478455225891831337239234501240234351822046599376177331678980591289089322495193509,
 nat_lit 423885484106438822985742796331190406022847602566320836707278060915121788775722040,
 nat_lit 514072604969243184209627472357848482094818679419739567068123904000470698194999828,
 nat_lit 459932334285613184761908745926120087748750749345359267001437451707415993714178603,
 nat_lit 463202329326749236484905244718248123297536317153099329706127173866720882644571352,
 nat_lit 496521507628418454009660372525441034540994223991836584141785907627883707852653962,
 nat_lit 441917616219291350011448823780058291227469877689413334246613335556519746306611029,
 nat_lit 533125154977983915224896357156635045592824217321311147834140168426371584581245892]
private def jp01W2r3_c28 : List ℕ := [
 nat_lit 478949151575460564947717414385433204016275945692432955657841587827632839550330320,
 nat_lit 497276643129172478265854947415420357776892768957680569342958227699834093062302149,
 nat_lit 516489538940906812309958506590847137784163647733931302388514242453853128218691976,
 nat_lit 461848105561330264720660962012372672875569496440519625551937622386367421549041325,
 nat_lit 554534933655958815189107343101282575884442592825568218895716735767346725609917356,
 nat_lit 499821356369322691047734559184028639329609061469083819535878943904783901600689050,
 nat_lit 518628525744195952847358049198311725964982245782666281956221943217501535899188246,
 nat_lit 538320873233068922169836956092372735657957514244296344551058450447958267930227300,
 nat_lit 483638279379876825566439803236944659620846576868083201206790226349932222499380809,
 nat_lit 572826241058872221759761549909893302910100195120003570489022929044357066957417284,
 nat_lit 518078061835572044757637467497830688962014009520943536045154144331652809160697521,
 nat_lit 547148663370813453670263018835196164838209989930685218441676731840189009754247684,
 nat_lit 549030738010964392231360969440004154805822810262203322361442280339402926845822834,
 nat_lit 507922052741518444135060792930306417438310854374860751263119100711072569908526799,
 nat_lit 580507644834130160105293305729415197170657049686038695915052259929832616852079902,
 nat_lit 525744086972333595122505137626870204801657004194391475637657047087999860495159929]
private def jp01W2r3_c29 : List ℕ := [
 nat_lit 569553304423751333731959659950563061210334518955259399935228380101832592197668720,
 nat_lit 557679412916713451414844164167119796123520598356130506037677502522508905672480461,
 nat_lit 530852055159593209281253651897766344646459969379845683298019745645844243352859256,
 nat_lit 590130375563800047813032490414346610828020071573432656024553464557289767665341817,
 nat_lit 535349177499021538975136879707120813338947743657391664711465798147664245894322596,
 nat_lit 594089922319694967359933269152436519806487007891099348761331099619812056089365781,
 nat_lit 568249286852955708644694897995607094359240581426748175893017562430054314425847430,
 nat_lit 555900465093288148206362043574504414114554719667306829688303706292525187685413631,
 nat_lit 601657343590334944458043535678629169383398157620339561593030658379144057442900627,
 nat_lit 546854208350054631592801228602310656596383068928778848233593739998805953173387707,
 nat_lit 620733187536346816830827915591289236203227841991043100298847157314444092319090622,
 nat_lit 580720231895772412605073280012056485712845087734819086349069810314807112577592047,
 nat_lit 583114775336058988059955213155183433321175099017714990740777591667335582810045524,
 nat_lit 615243466081008907636394406679416443072687151832022844539396161973965934930071923,
 nat_lit 560414322849131222201546459660031579807798877747553333044763552278950950681178807,
 nat_lit 649762403287740432911621476323306801937262400148727727885654023222059024663528023]
private def jp01W2r3_c30 : List ℕ := [
 nat_lit 595366575817269579241730237581694543101159488722646743850773029725835669115057218,
 nat_lit 612643344520816438708099967601308990330275087057621436809795698182269580485663720,
 nat_lit 630811397530356614445040550356782668970756288735139818112433173801980536551295480,
 nat_lit 575952853960166702600648563957738377465884992200420508492179064692361000625722110,
 nat_lit 666743812546545672839893528862398903727500038736697053503358723786824926420319438,
 nat_lit 611816969728913541449515129341953703657981138662835546130285170778001686655266936,
 nat_lit 644164125863350721720828719272840201355931044770077065849926758584327332006662308,
 nat_lit 648165738766896132919588211582153978706623684583934682148761167113049488753360165,
 nat_lit 607441293242182587322621824177340492293521576790431905845845358427210667262922718,
 nat_lit 684995542570948371578212569202675646664106502764493014424954170674690792751137217,
 nat_lit 630033871660227895693888684525341628435827866902361333623264904614299841246728234,
 nat_lit 677637315828645957770113527435260785597452136620261972796545040577305860776757867,
 nat_lit 667270757071707152283910024142510165483455796180299472441041445843300248042068509,
 nat_lit 640502878447678260168194251545542066179313594776613313450028276323776763821103050,
 nat_lit 700651222722357214399221429434051595975192964053315156332875834843397079649820620,
 nat_lit 645660603786227015271503932924091496603226341123039382984031331995702658847528866]
private def jp01W2r3_c31 : List ℕ := [
 nat_lit 702098849810327137880108016905395366049472646144316855132821539922699918356282051,
 nat_lit 675532930606850448021200431038815898270104945231086235300577763806567668316405567,
 nat_lit 662188794339032451649861336436788082322946020105393168971551006592301712504150499,
 nat_lit 705904158553003683353939640966779481503722501999300617256869011040396002198020491,
 nat_lit 650903588733126254383292354670019542719402308654972178120122850041154563963092269,
 nat_lit 736245986154886542639947158512696592962780670600622222153149261732022935191028713,
 nat_lit 681688004510809420527960730109330961384245167867140467677964488339795946560708823,
 nat_lit 696875766121945403969059442704046825168572316518884350497161552570628185342128234,
 nat_lit 712964084407636258506668661396518828983828958572920804847770745220061846471220070,
 nat_lit 657949945200845494270077972485973276037235999132490866461941211453232767235865895,
 nat_lit 744729340702696920808564727717414896181061442150653276572492288054317086441911821,
 nat_lit 689654365411247399458303940818350753052415775561742823947882420566472230141539144,
 nat_lit 719530310050739408160092195419607878313478813811186606803663646735543127803468339,
 nat_lit 721843665047363268794264914331506538936284397807969830388246076208318427249908693,
 nat_lit 680590691944063484538012561570821675641260235460030527600718658208356854457656904,
 nat_lit 754523271863942260418909064634517313703950920572557712511482129851693020943384534]
private def jp01W2r3_c32 : List ℕ := [
 nat_lit 699430656369483835263659808019335787000658202045074803648881014821486040785762081,
 nat_lit 758618512486651976662296005271817091554295630424523297849746127177405265167898567,
 nat_lit 732658466417372355610441509034124449066198126949774865964508118412075359309008705,
 nat_lit 720270745740864255450523750751756710788298800223973424826600090255649708467824426,
 nat_lit 766360300381449563886036350020421402512577644739698204313191177806737394198250125,
 nat_lit 711244843085711288321020569053517090445274808849511018638479097801998695823481529,
 nat_lit 785588799929171539853435302673172203708985812742722294723372169111605413371911121,
 nat_lit 745351497092676038747379227956105552166458476555266584932260555167544990651726612,
 nat_lit 762177309839733388850491668041217422649829643609703769434266698558871446529524769,
 nat_lit 779900286956607403182155567402622443796293405398486665747667107601569539207531200,
 nat_lit 724759047825723006630609359883044523910852909330814709273666246735367203262211112,
 nat_lit 814911566757821464621288761002355094789873281123869387175736925824587597754472530,
 nat_lit 759704289943953444451532346635780026023851139900317446145987224512434457848662750,
 nat_lit 791537392472622002602786795809916662943616278743615108039620257195362328699823255,
 nat_lit 795108855809202977023162878733420725614531740345477586970926857329600554025369759,
 nat_lit 754061458880648475305597546680038917969273080287106334987790074318310522598390517]
private def jp01W2r3_c33 : List ℕ := [
 nat_lit 830969353074756750499134804179213698602139366130833915252972846627562031798259120,
 nat_lit 775731092827444702791402758750812769318394630927010718130282306648789573400064333,
 nat_lit 834048698932679210802770768717642116999462403363657682237943521931082196814281600,
 nat_lit 807766832234967064079866022636478402128735245654486250826688925428000769418988463,
 nat_lit 793794207207049287147405115549579175808128278683995019592886018715110945789818495,
 nat_lit 836387156956397546939755867455940480445174902352249187310757005212320961422098655,
 nat_lit 781138493512462726172824631422019057890895005313250054529310228876262743607659369,
 nat_lit 864957727253133730951022985278162551723079843975830524986764909061723860601306199,
 nat_lit 810158210522031593045743998637213990690050737038546492885117347690845111045219976,
 nat_lit 824451523386827293482001837957365672682413901252720171229105299172768348107062982,
 nat_lit 839652177604240399430551719597433934090122468189770621436072292227226591286501457,
 nat_lit 784398086405529460579219037403159236400593643222515319301994638761909549605169378,
 nat_lit 869618133194576629496495656950636129170003125773624122931858156300759600538878391,
 nat_lit 814306824414373038954506489594828616048335344820768330712761501150908668462285715,
 nat_lit 857220236174730915520505271922831160932571121782977911269447786435108074216549026,
 nat_lit 844659507531739324099837401824044699969306881955287809892050204914558782271425235]
private def jp01W2r3_c34 : List ℕ := [
 nat_lit 817173582201569169513673282060722546166806105719218227839669121616071418727035525,
 nat_lit 875476715994449570497202091401878697738581817834977075984649924052811949247042635,
 nat_lit 820154099391818200566926755201249839481691268900803177891403389978259450277447028,
 nat_lit 892037474077959252048710584086927584744966602990722370105190060973591387981831065,
 nat_lit 851350798375226291194437317529484265152741832120595251010102071969109901885530300,
 nat_lit 852553045030719595088252768696272462056215071989345914661885458093373703694993293,
 nat_lit 883163999837386130093285720545663329014204976602618510092036202076557117710784947,
 nat_lit 827827135378487670147841340410698835950612719795159466289921648095566683834096871,
 nat_lit 915406898551801585743794663576535481791112324562291728998634155889795998928417538,
 nat_lit 860008971851793117104818848151177682108736481647806890337181733622575263544302274,
 nat_lit 890212391023584953953439105461896536046369153565760365916544714484162705092011536,
 nat_lit 892641085814202395248542116417375340091110537295801447003403838663811322401952528,
 nat_lit 865547541899158025669883821146209350601367859612751496758905909205096644643949135,
 nat_lit 925696112335383662564287072368454773348178401558670216348519086293911297094927984,
 nat_lit 870278510024358945772407917871326615955416601581424228835042394272863714520707497,
 nat_lit 929824597953947045834999272822078648970689728721553054951877159578769066663739408]
private def jp01W2r3_c35 : List ℕ := [
 nat_lit 903714836317821110029805553177861329933407992578856671532719886812390989547629671,
 nat_lit 905712701343313367551230030694008143709879419702632884641128638745360279183668743,
 nat_lit 937566612007271801030122437124913481354587664504352778062458732910509420154010732,
 nat_lit 882126846364294028627821372102052004227334482620646860445646769642770666544859433,
 nat_lit 971350540756143746157344846685121654632649180193873782109955610643975218181945512,
 nat_lit 916351554037437147808387641266128450017295472011052623558416561186858922997680152,
 nat_lit 945291663296720719528206495017335069066524648605486948486996407709119750378308042,
 nat_lit 946847168030295956412274708487126829738363476574415207315044490267574608751854554,
 nat_lit 904699293910296185316064423823824320726063983886980068227309874118786030503166183,
 nat_lit 974035696275891357178965460195611450493393392007504721590038594170265696253719768,
 nat_lit 918525822133861352569290148334857679199690659748862513618751981040756525141276267,
 nat_lit 973426656623624616427684106138326688881729420400520315583275083680918227061250412,
 nat_lit 946098137872674457741579903412920434690326645346921627883272248959305161291546661,
 nat_lit 945736965023963252506858308363229860968170616625277733050772355201931479023431415,
 nat_lit 974101960115326232380250880816125272922119832594853154242624753024105008746964951,
 nat_lit 918592764442623022569920183164484898146339661490628978725628836806765878304287405]
private def jp01W2r3_c36 : List ℕ := [
 nat_lit 1002054444838124947088772634041225527501551640828264504179531190005406721537969907,
 nat_lit 946997109755696399086877778176194675279334574524694900660879099175429942726993330,
 nat_lit 974947558403498529869918906482952051742672506428252571958432125925803043350881688,
 nat_lit 975827986130707870198870674082895887653403817408231081200945736527150855130454524,
 nat_lit 933844075412361384325085648786201752125655562643907735744695147683403782950239644,
 nat_lit 1005105295335205815491520504297937440113994799780357727273294267350272037369028266,
 nat_lit 949537298985878152862101728653226070635061679691799173333451286909937152154168959,
 nat_lit 1006131366800765743389221672230182558668839476414110611603585627638301992939855527,
 nat_lit 979178493916099342877704858369640174341168745513756391329776441977758928284758901,
 nat_lit 979688475690541442738209259984133991201403728288389021853758995540082858492270268,
 nat_lit 1009389829253131865642792235166924834971165807661927391991695845165504575613867786,
 nat_lit 953813238958764482668894951993389736480338619533380514530792191786165053329061957,
 nat_lit 1039532186867302424672741918453111413590632097963165177349423151682532818533464489,
 nat_lit 984404064816467889714247174429638246557531094989604902001096359081591755410806888,
 nat_lit 1013672553235419973192703316407240273719710154719500710080465323217803503564316406,
 nat_lit 1015404233846056910618772585903185292857679346951223455841645795249443950474605734]
private def jp01W2r3_c37 : List ℕ := [
 nat_lit 987839606059959384113873474310424323941618701953138651835737898921524345999444004,
 nat_lit 1046811710639524201034556316292130085140162985487767268782582911541957420821616110,
 nat_lit 991164559533202082687134358733669299714665045011462201523587323289703133918461465,
 nat_lit 1049514732165664421710164394283739318792356868035277217265852820912331806592746774,
 nat_lit 1022938862086204968499659360513546373908479568673071880800460609299543787475964640,
 nat_lit 1024217775770476733311907598705295829464398589890060752105033540855248858299610498,
 nat_lit 1055113461553178204607395766128411713455356467207218242494438496743743890801165821,
 nat_lit 999450253339005943530084081942042505524851161869201031937589475379836699047889888,
 nat_lit 1087684965587353017267429246596529010581686258331882230731010405709231507551477787,
 nat_lit 1031960242819168244330435699572733057592244553804781359960694193672155250264854728,
 nat_lit 1073940759231835956836483784941512641670530142261532023254216174526668764589039310,
 nat_lit 1060751315659271675926780269460456769238256512980229453444598327338153919859348445,
 nat_lit 1031964764635674926705886279320268086024291775543129483420871036825918150652314843,
 nat_lit 1086320789889633359924085829252604861722956079406505006620557729576207521404604697,
 nat_lit 1030598554842412354397705756882726429763278493421963927431524448092049091674187739,
 nat_lit 1098059440182265638047846745256843261800088433936540282910471111692015188578622466]
private def jp01W2r3_c38 : List ℕ := [
 nat_lit 1056539151804883413860540019198325983246516664698264475705547550646319442001701471,
 nat_lit 1069258415800807800701605455782308495129514898296946311440522105215450120444365656,
 nat_lit 1082897459727828555947164640395049108967538364753992581594292038333428859784811985,
 nat_lit 1027181783217612966470681055558546856212775810716841074513374276737120765574540170,
 nat_lit 1109694737317422789879153950072715188043860508033475632623700650570156251066614990,
 nat_lit 1053927497136941918382704416097068049091431201037259843019489794694853698759776159,
 nat_lit 1094778362094587780410085971811365577758223403243815922072500932294477785050334970,
 nat_lit 1081084363479739536862193895040052949139768977231894626912118814943664168916518682,
 nat_lit 1066582532362282564420438883197614172023163022466745906223714066670883634713754209,
 nat_lit 1108649216055742219652286307490672876904842360263330194007676398770290836768293671,
 nat_lit 1052884237439746904033494007283990052651394662491133763843653597471086483063308827,
 nat_lit 1136110488972245845789943001720414869953322316735732041855938638712752062443019684,
 nat_lit 1080800763293240045822738819208576557455029866187814533985205724013688041745409838,
 nat_lit 1108577523787882878368164651785574885123220223592531446760074007541925093993862418,
 nat_lit 1109260516936196061368965066431575534851306217550860367056345654039144520273245249,
 nat_lit 1067033261878190068954662250276762628769714715237344661442603929922356495434399442]
private def jp01W2r3_c39 : List ℕ := [
 nat_lit 1138149063205602687337764875046842909753804007283582971137165306702161457852449377,
 nat_lit 1082329128572600275905973323064467562534921025795471210867392287929623215139467717,
 nat_lit 1138742271228400756639446552956818464547947789518222788394687850625869213450386610,
 nat_lit 1111558040297096541435520389420316702123406471135583403457204385198011607217645790,
 nat_lit 1111779220287334362676426273656030779993770931669740144026125779122633469323566869,
 nat_lit 1141180238085628278097564793890950005092514982087366486378834210351160328463428800,
 nat_lit 1085353292602717947449726327211289108132757370077169100233248945310893976245900730,
 nat_lit 1171190972652773122550502979459528118833469335321844197673117252956445933464929805,
 nat_lit 1115307940370626398127384095719669958077415259679704495854884939683098554974726443,
 nat_lit 1158436200753014170200394683236503159461566718099801843270771322328460250888038048,
 nat_lit 1145647732570433102755997246655650448480553861532345666645081985293370407284793828,
 nat_lit 1117800183068726557319416963373872521915170050536045792866173093797284609737564093,
 nat_lit 1176395511003444871691999454244500215616394272340061046919964435146141768928891465,
 nat_lit 1120502527837550917429164656806360195999070550468551004596246131387522362224252999,
 nat_lit 1189101206268337662172800686939860656979283087106731236341297697171001862621001835,
 nat_lit 1147555136057561713953346168986595932471686280392528485952748212748631828672579748]
private def jp01W2r3_c40 : List ℕ := [
 nat_lit 1158998425383859579783585687396656617860278653497904616442281225723462468510771898,
 nat_lit 1171367600839097732590842427212257776491089311262524134591380644613960538156145708,
 nat_lit 1128577668584809940465536953457881069842282995809067934824031069942345316138369701,
 nat_lit 1195586921071582557626779426549613328941786555020595123541013766322248902515527814,
 nat_lit 1139657300561044166101945612283930255698951230073479494669531285293780327512605469,
 nat_lit 1192406934917236718277096677867612279119509722451475181482637087557791995461062440,
 nat_lit 1164234626451600574553737312349672308844106793043636793739206361785052653031241040,
 nat_lit 1162575541760349199781167759600922729920897963981403384862999558137721109903430726,
 nat_lit 1189213153881905379683160244233032743080318254062933449719636320646549372359696987,
 nat_lit 1133296198132448357145301826847273968464021104962660745076655613518019380701322204,
 nat_lit 1214590621287446065662676147053610710925971734540095965463741524087660109689590602,
 nat_lit 1158624815745111820145445565373062754795848782539232749777368781172645814635523817,
 nat_lit 1184799483969714944898654055492305648169089216961751936133865335134010763817821004,
 nat_lit 1184372501256956875261403192477791331775353261720278090404144060809303766003656927,
 nat_lit 1155557454510931643253266422971308634333785876122686122150722355791134303019353705,
 nat_lit 1210512115894156851961287902933888471077999899350633312936392999153396095501893657]
private def jp01W2r3_c41 : List ℕ := [
 nat_lit 1154553999671084280409329877271176085333185964168208178970408803126601480671071804,
 nat_lit 1222803492545667853004779707416946952317605675402727088893543085218767417307919689,
 nat_lit 1181163115095474873332832233432540330396412143675903472836586812057561601410336186,
 nat_lit 1194205330493245179138767734103636555030782809612771643079671603392725275153229387,
 nat_lit 1208170944338677055470019497397400102536022566840020778406708434279160924387161977,
 nat_lit 1165641996590553902030177227458497587616610997210825237701319478621109852600637730,
 nat_lit 1235562787231548193592667101650588840631492280018897398337173553240169995915537487,
 nat_lit 1179557178154278948609907166839626805318742719314287182592443051014229660831848027,
 nat_lit 1234869391221212215403162251885300595137194739414038202763636903431501048117680234,
 nat_lit 1207276043271750682663766689353333746142922153433002440923218838605553059018761833,
 nat_lit 1206848832732264427366407641224134085986904761294955932713356420854117399086774034,
 nat_lit 1235373041971212751452534678831106915907894573364870704932981175798016587195879849,
 nat_lit 1179367885206846009635925171567178227691434603524495459673930269750322159018407963,
 nat_lit 1263844329593020838017027405089365422093475968743668395899621361688305907362275440,
 nat_lit 1207785121437452006719719501143810950776091508024434690541488408705496656844891079,
 nat_lit 1249894773179821260056763768158848562047755381658967436711540296477662995871464988]
private def jp01W2r3_c42 : List ℕ := [
 nat_lit 1236573932713042922488525810151133769268552532980853548767697338079095909841715784,
 nat_lit 1207519386294632167505999238095020910576199564988726173070101176532637804256345994,
 nat_lit 1261818646283289566435490561923369885163011737574165833779350993630665581685560175,
 nat_lit 1205763282787338092144271484578317816471754212341342708975938360623564932830736458,
 nat_lit 1269889943610064410527066358389346342015462695922350082764235194230154672798262326,
 nat_lit 1227713349215005365554488282078802929164697267435675707649189009493610104212386413,
 nat_lit 1238421630090426279091517144889510059545510930315906158947975225390770881729546074,
 nat_lit 1250059641740547420720871417078192399575130618438551068071508435594017440383786155,
 nat_lit 1207000809481762666707249893477037790314948479459742858021151411527861290073774625,
 nat_lit 1272798768017222443850387586173690729158478083196770371478894556076623938625533964,
 nat_lit 1216722598127998463497316853832568849238949345726080699662092095438732010475169153,
 nat_lit 1268363387419772635896043674865904584930179479787576371950325355173264310428314017,
 nat_lit 1239808874553219793823765858447183662028905876763336465898777468161984393106371171,
 nat_lit 1237516777971172089739900045628476298770718722329464880069845231819734776526597402,
 nat_lit 1263281878505471179229601837937812455003816509569730141949474774371657620672154022,
 nat_lit 1207223574975680394311499885120122211424607829855353220523766686031390650036159053]
private def jp01W2r3_c43 : List ℕ := [
 nat_lit 1287139574576718315420242771542759679564110612364998214084706685042300052263056393,
 nat_lit 1231036265913667664532071357502424659880559481856289077296756398851406252093075952,
 nat_lit 1269941733109001834399051222208282794428060344244681488769753311303954802352129534,
 nat_lit 1255230256623908871747628357834139905937477045191225262760208940136444721986225325,
 nat_lit 1239730623273886821962892048160681005115192633903273915117015568642810232413103198,
 nat_lit 1279921565364548080414582601059038173739030199485042029537232208584199305939157996,
 nat_lit 1223831826088410764792354589632488768217746390553265582613573650902625006323972274,
 nat_lit 1304497308153879738338494411931484628917997761107358280303124429811804660394738657,
 nat_lit 1248871189603374327035447619504367792636016003240211562140204335288070475494607980,
 nat_lit 1274877371273736139023668810391908388797921887336030009838405443338742160564335438,
 nat_lit 1274283258945552105925833793708317905092284424073526766108771070695920968335976493,
 nat_lit 1245292940952017613210685607574641001253607517922196584116012720683985617028362709,
 nat_lit 1300065772550485505538950782441577165998099333299240627141368342059304953003152457,
 nat_lit 1243938038990996243162700224106544603224943878396394867955819247059017568232196034,
 nat_lit 1311863223518529038592529097959775616002174104338880368500494132398010642727489771,
 nat_lit 1270038528562588015193186319169699148423404163113084884056173981279744039545863497]
private def jp01W2r3_c44 : List ℕ := [
 nat_lit 1282807094658792297741986185546917163667398599759760595890307028995214698498487885,
 nat_lit 1296503356172805535109562264809617680524176927741815622385576424297415573346933390,
 nat_lit 1253782175445998287222081082187362992835439613654260038335730358020192419746105945,
 nat_lit 1323330034100711995451095613866943187840476648953028699340503016046126028793898919,
 nat_lit 1267158426190192165070270635299164730800388688395378054149750579680493408194843929,
 nat_lit 1319004791692784032350717657538614302954630521810807857067416904846371039151691622,
 nat_lit 1290430377059680328947688022742366323028069576349084435869170262206167502754832991,
 nat_lit 1286730682765240061868193497546884393200392739637312282338552135244557606144564938,
 nat_lit 1310438438063581898246471750440015826568181348041750564697931892213079600242990823,
 nat_lit 1254291255049500679353725916166934912617697711877587504720090149524565948167788399,
 nat_lit 1330833226594513522627856329102197245172399534579000962403124048505431935683936682,
 nat_lit 1274646918514851059015592906547610361244230481605418537953521055375027799218372007,
 nat_lit 1311162590530034000544385544843106969964302045921769655172441587657773919747509816,
 nat_lit 1295386595629816474763158183376865549805876828019123275180217841785930004028349006,
 nat_lit 1278782866526491243843044668259524682927208349891975963549530431655255088721966306,
 nat_lit 1316506894047735992656245401440980557449681897607588821907138936608793610038113846]
private def jp01W2r3_c45 : List ℕ := [
 nat_lit 1260347950898324491205849094304403085500129763823603603499474764469745850765992456,
 nat_lit 1337493533998436552831937413417851156032414037465348078844680572466912821581456114,
 nat_lit 1281806353206821132835359185700340967459717082382588637019227444181467602548629082,
 nat_lit 1305674225672575873812985747276455500539524771420223008964098382620259189932029679,
 nat_lit 1303639722907044506939700682308750739266990921089798272477478506452866150011171454,
 nat_lit 1273899470163163371675431168151454841617075116575191834736403584658801782246566365,
 nat_lit 1325846476903808892487466060986703129862629990324175119791908954086110036910040830,
 nat_lit 1269670119707893658718132428602039970563281277835712345640310133430606807361684543,
 nat_lit 1334516862661672474548361502345832525688293220205205548923308039655132162859890243,
 nat_lit 1292313129493919077073882587388221475597930534491119676408021819887214255394869355,
 nat_lit 1303364715852661270558015434530553594931750025943860913643173839750857298451951771,
 nat_lit 1315348068405326376963440856637208167082222885701380805333345105765318656204331140,
 nat_lit 1272255764982509126022258622344963257096108184886949837183017973839603786922012242,
 nat_lit 1338747797668234967951944500426913656999134066217388434940856311753911298065573213,
 nat_lit 1282546563262951659578500269472206959947720494656496179848517098913190778992670647,
 nat_lit 1334767443843154558281571467752749926733103244836406770540663175639637621764791900]
private def jp01W2r3_c46 : List ℕ := [
 nat_lit 1306264268492545582937467923174886178379397069915537224425816058827523795952538871,
 nat_lit 1304186568217576314759250786949712878912234516101931171030030068784049767496531506,
 nat_lit 1330339753223759838132428939920953250180397259729945612989198239258169040493923897,
 nat_lit 1274154802082777924065521896424387871975102848841499363563887609992556921377734870,
 nat_lit 1354772112830789418831082464999465457718488208215700600468795986409836504402258825,
 nat_lit 1298541025774291380881943767501189916219205849039146299617987516167416159053983313,
 nat_lit 1337878904096384511560023232299309048528372106364782254177052352845867815554958546,
 nat_lit 1323280731994932269308786898113638685453382235000641281204462609026084518293802646,
 nat_lit 14463347009181250392391673776322278814936664628767134482501596347160]
private def jp01W2r3Get (q : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat (q / 16) fun c =>
  PipeFuseCert.withForcedNat (q % 16) fun rem =>
    let L :=
      cond (Nat.blt c 23) (
        cond (Nat.blt c 11) (
          cond (Nat.blt c 5) (
            cond (Nat.blt c 2) (
              cond (Nat.blt c 1) jp01W2r3_c0 jp01W2r3_c1
            ) (
              cond (Nat.blt c 3) (
                jp01W2r3_c2
              ) (
                cond (Nat.blt c 4) jp01W2r3_c3 jp01W2r3_c4
              )
            )
          ) (
            cond (Nat.blt c 8) (
              cond (Nat.blt c 6) (
                jp01W2r3_c5
              ) (
                cond (Nat.blt c 7) jp01W2r3_c6 jp01W2r3_c7
              )
            ) (
              cond (Nat.blt c 9) (
                jp01W2r3_c8
              ) (
                cond (Nat.blt c 10) jp01W2r3_c9 jp01W2r3_c10
              )
            )
          )
        ) (
          cond (Nat.blt c 17) (
            cond (Nat.blt c 14) (
              cond (Nat.blt c 12) (
                jp01W2r3_c11
              ) (
                cond (Nat.blt c 13) jp01W2r3_c12 jp01W2r3_c13
              )
            ) (
              cond (Nat.blt c 15) (
                jp01W2r3_c14
              ) (
                cond (Nat.blt c 16) jp01W2r3_c15 jp01W2r3_c16
              )
            )
          ) (
            cond (Nat.blt c 20) (
              cond (Nat.blt c 18) (
                jp01W2r3_c17
              ) (
                cond (Nat.blt c 19) jp01W2r3_c18 jp01W2r3_c19
              )
            ) (
              cond (Nat.blt c 21) (
                jp01W2r3_c20
              ) (
                cond (Nat.blt c 22) jp01W2r3_c21 jp01W2r3_c22
              )
            )
          )
        )
      ) (
        cond (Nat.blt c 35) (
          cond (Nat.blt c 29) (
            cond (Nat.blt c 26) (
              cond (Nat.blt c 24) (
                jp01W2r3_c23
              ) (
                cond (Nat.blt c 25) jp01W2r3_c24 jp01W2r3_c25
              )
            ) (
              cond (Nat.blt c 27) (
                jp01W2r3_c26
              ) (
                cond (Nat.blt c 28) jp01W2r3_c27 jp01W2r3_c28
              )
            )
          ) (
            cond (Nat.blt c 32) (
              cond (Nat.blt c 30) (
                jp01W2r3_c29
              ) (
                cond (Nat.blt c 31) jp01W2r3_c30 jp01W2r3_c31
              )
            ) (
              cond (Nat.blt c 33) (
                jp01W2r3_c32
              ) (
                cond (Nat.blt c 34) jp01W2r3_c33 jp01W2r3_c34
              )
            )
          )
        ) (
          cond (Nat.blt c 41) (
            cond (Nat.blt c 38) (
              cond (Nat.blt c 36) (
                jp01W2r3_c35
              ) (
                cond (Nat.blt c 37) jp01W2r3_c36 jp01W2r3_c37
              )
            ) (
              cond (Nat.blt c 39) (
                jp01W2r3_c38
              ) (
                cond (Nat.blt c 40) jp01W2r3_c39 jp01W2r3_c40
              )
            )
          ) (
            cond (Nat.blt c 44) (
              cond (Nat.blt c 42) (
                jp01W2r3_c41
              ) (
                cond (Nat.blt c 43) jp01W2r3_c42 jp01W2r3_c43
              )
            ) (
              cond (Nat.blt c 45) (
                jp01W2r3_c44
              ) (
                cond (Nat.blt c 46) jp01W2r3_c45 jp01W2r3_c46
              )
            )
          )
        )
      )
    jp01ListGet L rem
private def jp01W_2_r3 (j : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat j fun j =>
    jp01UnpackWK 12510843 8388608 (jp01W2r3Get (j / 11)) (j % 11)
private def jp01W2r4_c0 : List ℕ := [
 nat_lit 2687716536074796263546559554879257386179021641252327355485455759257278079812263302670,
 nat_lit 2653141937066305281211705844736133279314845176818288357038324035720922030176911310359,
 nat_lit 2616907342307838102976570955634083566998960668251924447871662078639959216672163550887,
 nat_lit 2581393437655015197258862709681802743464228300951188363853547291019677452918331284458,
 nat_lit 2547887831442286437418985904073348680643735858792634315962937296886029866067607359408,
 nat_lit 2513259504902622495410924210805059462673803380587755242795634197912532554147836835450,
 nat_lit 2478851646561380921305096591684667211166082813307570864660858713550344009318264212886,
 nat_lit 2445510928297419172904522002183272034547591033574851219504642365594179322544062338416,
 nat_lit 2411449519983910551242911602924684974788489177066589827005629050284274807926528659574,
 nat_lit 2378225520162685066894277075555642342806417921514657854001677752212109268717099105593,
 nat_lit 2345255336696035828018128088037873865030913975686910663671439622545526066579546988019,
 nat_lit 2312157318764193724622694477814056686686793325332292442215040393661877287911405859545,
 nat_lit 2280074566018757886267613369566453515690316698588567649673042661513277643121805998948,
 nat_lit 2247980697268975636809779223162899675232378473091788804121825143025854568373338503705,
 nat_lit 2215312499641731218433647797864536253151288983830165741612473014526681776645467008775,
 nat_lit 2183994901229580139735245204216788113681961614644700577393532111746873504278433732923]
private def jp01W2r4_c1 : List ℕ := [
 nat_lit 2152532794246773124805720141202552505706979789776358974020316726603883137741208615785,
 nat_lit 2121031781129491478294512655582618395071183507997045416684487843673995133715244782826,
 nat_lit 2090436725505246707445300273623437074435023515344714488529156978488737364652618212857,
 nat_lit 2059556358144851627607877739083834659368247930430922234442093174530346902298275836089,
 nat_lit 2028794561869700782088529006930676980606393906157868135047461505089301965025357968548,
 nat_lit 1998859058122240739429384769253554742827894422329065746706496575381565514918466925044,
 nat_lit 1968514113488931565868399099328592942193662333782444019542284115267257917711455709720,
 nat_lit 1939154791303845989947433537898911196642409001594529768434311202496376836213110136002,
 nat_lit 1909934419650139355661339491603451612766045985331847186251029423966738775891229805456,
 nat_lit 1880113781696281915340733250506097115735530031051396351629647174982686548851102381904,
 nat_lit 1851297292934643716535482999784541253777658083586243334808768192413030047596640050811,
 nat_lit 1822573437908001866387653107865678676594158628927443705960823317406242388554168796045,
 nat_lit 1793856993549010210165538496005894180880685936890429218185365302699009216195398870617,
 nat_lit 1765879766030382506080194391016138559879514296722000377825578923928773953021938894635,
 nat_lit 1738082247918618094192634803834880957122243139092852267040138329770445887818521225174,
 nat_lit 1710218033508238995707850502856160076129533736598134270221704275958367350292743260252]
private def jp01W2r4_c2 : List ℕ := [
 nat_lit 1682470537580350237398428952143548554458017673078782247550464538032014322175927920891,
 nat_lit 1656614621614482404454356322179228009917890067881568102398986186083334396339428461083,
 nat_lit 1629698976245610617276787700144049241986018579125372966452526564532308445876803972957,
 nat_lit 1602196033199589981538128805426043356911936216134086487870497978310096245283770603142,
 nat_lit 1575925118314780003619533792658383403711117675946921450875412943114163686358350184158,
 nat_lit 1550124782544678687660786294939678060469795917939669024001098999745726422335555644080,
 nat_lit 1524272571949960607244089229659958430917910191416603067707505782558741880496178715486,
 nat_lit 1498540785132466449541331368362599902899736680412815217679509828093723308569844207721,
 nat_lit 1473459286807391255420833608345941550049262688066234827592629122027461371322140494418,
 nat_lit 1448359261787792169675918572591906195774885674845276492659280835761179915065326668481,
 nat_lit 1423264794753139517700032995306476280779891721192299379727820246966508078360400384328,
 nat_lit 1399350480950395030584773699375146661645388609315662929474318742453655668738040979012,
 nat_lit 1374960030007357946189200332465651789059429204879285506221748172685040163059205354474,
 nat_lit 1350630717258726883618753644044154650873817813843514265624079630617425296869631676862,
 nat_lit 1327005420616729583518935727206777154780126941054650543801364375603571858341357631447,
 nat_lit 1303511663756744342376668803940653691423359152489778459786720930403280723793639040854]
private def jp01W2r4_c3 : List ℕ := [
 nat_lit 1280153152093650359669504846660110166585238298542899758335102909058566935090683338915,
 nat_lit 1257155911880165227644614891150421916874827325889207224925479431292731119009191011435,
 nat_lit 1233999341690933318165293994751438656776639821737323765080380039020026187730161546113,
 nat_lit 1211859889421166564487336477897416747873665801936527263082593953536078184934372773204,
 nat_lit 1189440683390036583292061734208828606120842834245806317316994303705635227525491078225,
 nat_lit 1167040004120128990531239121943641667349739953398137603613296732653844429980623742840,
 nat_lit 1145389657739986371166455910803651492670898605948984330217795765026099053316858898209,
 nat_lit 1123505874498665371470371470130789698720806969151820106602649291345870853981691770134,
 nat_lit 1102074143638658502682725956090946268782517776510339258815645670308103338601947779184,
 nat_lit 1081277879901758412896411693720827514561812013858826638991773201935166633985580235525,
 nat_lit 1059877644476772744814019039899630969770156931278336929004815478659773330800485987667,
 nat_lit 1039098054801164527688562404814269153543616794719504842997665770433868751779896966819,
 nat_lit 1018764959521482306994119778761231995525780523029578900816080664900797820026910693430,
 nat_lit 997916820941413538876276135789792190685214073158819663040187047736649643986059084555,
 nat_lit 978022809356878701679165368509907540474532560535898925339960426883773463670005562839,
 nat_lit 958275159020844712906756114148130961551897903106121609556151792576736919956291488576]
private def jp01W2r4_c4 : List ℕ := [
 nat_lit 938371884038692763276296666363166663666777125464845127320642680965358534414077192917,
 nat_lit 919111486919296825946313374916317152588040760927798214441833648382086101355154840801,
 nat_lit 899765866795719510237023094044619364534279546912951217908120912401988681166685151882,
 nat_lit 879834801688739879952915096741503807961106415846095507371587942237104989243076705199,
 nat_lit 862566028970673507280218887857780143278183662464368338603021377606604299781546616696,
 nat_lit 843376033441975566698565100097283674938502055001131676765561540479774649052498897699,
 nat_lit 824862263880507217543220138509102560595950251620963080208248417131435872499762823871,
 nat_lit 806711618336948077546590972633647789389806860567796851704848474944631402274360700835,
 nat_lit 788218228165958728313815573181038320497344494777022758330182183593378133772270285597,
 nat_lit 770867937786591158428389039043860823848104381218365911079562136824828888726376713255,
 nat_lit 753538026759715384260599920913633805950009625100969107581782844418625552207830924543,
 nat_lit 735913540612323548607700926535341342791220771999139878519329458887972496725562607161,
 nat_lit 719684117862169218165003910857362145053640674952209184588578895117864274862022731527,
 nat_lit 702661750746220230768479454506704717110947610173654455931366142229930712772086882831,
 nat_lit 685880231194436737967390490805479366467629512993992376055643040286284038267580610095,
 nat_lit 669804580369267694466484408971605625210965598679095141533885157193682185912613102540]
private def jp01W2r4_c5 : List ℕ := [
 nat_lit 653758572319385101250016871523206047709696479467926916331453924321811065749305175170,
 nat_lit 638073835680682429264713869511632712236471874031300142817148758308456316413330837498,
 nat_lit 622724433007502041452538232899666343571182682486132130455037860421273184094416621533,
 nat_lit 606745121202786987007229318846409868403298844979826224910211804688819176511391050859,
 nat_lit 591844065606911184362041956667615516565288602849968568833375597889078504613414167550,
 nat_lit 576911514550836610022580189115587913858292828797974352979398230481606452237738506541,
 nat_lit 561906709183373061935687237309869879931965180384964334186563065594932799838842383345,
 nat_lit 547748575805194919413887570451698142420072577032543785039927089136167210133712190577,
 nat_lit 533208791605922542764838702570718464850157705033174334717508593328690962897121012901,
 nat_lit 518970993204534061847923405705778870162007532185096775182725800545435245179660139337,
 nat_lit 505739196708104971541178708967583068029728087692499821665946320859274432339559082337,
 nat_lit 491566241920418858655081528688537003043476423215054156687495831847320605838365997235,
 nat_lit 478254780444508890067434093351329668191960656748662441748604726556916714131323676611,
 nat_lit 465310148401829089378101327580972858508383365445482529792115163827578466271549519952,
 nat_lit 451776366083663641004758838788113912534679725869286994212688298390717873464155892415,
 nat_lit 439044791528909967284207029492124018052318022857311580851480969904162530811099528786]
private def jp01W2r4_c6 : List ℕ := [
 nat_lit 426400292641606093535246102519510110058713010352444924995483433518435738255624271003,
 nat_lit 413878070215113311024330096048555074705325965417437678452517186059040787593676197331,
 nat_lit 401917207990958776401029674890730385412148172973746074577183522310786649889820871175,
 nat_lit 389402396275403951750065531958032954263894463133242163447481728661354575924414311104,
 nat_lit 377506377592069320882702534923361664502241966126419503201798510946535087892996173485,
 nat_lit 366158750394428089682210571626923673334418248323319040020913313586929264435904730959,
 nat_lit 354292374500956418024919040732467905189514126345218575754353053653787821226766657042,
 nat_lit 342744658526733352559580412771288043085432147076014438568390395279027814238364064110,
 nat_lit 331802766906072851711069475681502100285293068283809828817382389474034370207955956338,
 nat_lit 320225408122993221615855518354484141603327343219435381405817382244030942137116062184,
 nat_lit 309893046157254558106274849005109821830632497600980299843294645601508981623764260658,
 nat_lit 299023408849749881545278829368239028048730294272537588808321878481829354291168158894,
 nat_lit 289039349563086373015883880357748949908191312686625551293722309992634475791553697978,
 nat_lit 278264198569921220280451634809262582265180657597424495175832094255678645933851997703,
 nat_lit 267665051590825720245978217616683992044482761311843327477060650195776012462683929232,
 nat_lit 258242352473372058499326036672141514473425582380555528672647478356012412856498874044]
private def jp01W2r4_c7 : List ℕ := [
 nat_lit 249629271888574099674322129159345579560503419355527005264208083996947579887055371637,
 nat_lit 239439565771916973549374594173155134391740186029820229635476932298725175126087139315,
 nat_lit 230352200622635867310200534443510895571742818511817505570832166841388346834770029447,
 nat_lit 221342647832854981272637482708147358812143141395426655182400303560249428361453715921,
 nat_lit 212394233201701446937838587669788708357368838142072229610853573940825158228399948683,
 nat_lit 203994210061541849988942062101750907421551290313028432025954094149823164859695411329,
 nat_lit 195546017398566460748848664274301098493358459684037215275652503116644302250383526569,
 nat_lit 186919968075038053493076697030116737219077820446382662456812653994410262623720427741,
 nat_lit 179533357485844132416273624033344756510983498235711580330178144873629687963973272466,
 nat_lit 171368623929762441413458914428639506238318165032114863931317280058419579391533425927,
 nat_lit 163735607729616903738456413405361129900669489247007541175519279622384241876822520873,
 nat_lit 156975200971040089286690015332145069815785977700743085758240529814705086513208045945,
 nat_lit 149355153475613191307353121757064472670024037424364493826091255565351494977736171353,
 nat_lit 142628094799424368619501796244478743952361929183256957566842566669264622662341720979,
 nat_lit 135812107827412560110574471524212555626178394496464097223757367786175811761896327257,
 nat_lit 128590385201562147919662702061427452300589630283827821425564535836327985045450753410]
private def jp01W2r4_c8 : List ℕ := [
 nat_lit 122613659449591822288520668764947974373014888211776970213767138808731742932790702674,
 nat_lit 116162649184818662115413296603757723101823608943806156927561042538850889251409449296,
 nat_lit 110096995046032707344328837942081757208216933976533561636206153124775415483056136548,
 nat_lit 104475982641229444175590229614568918579284281259591307954847032513910682729629803414,
 nat_lit 98727135762840787243006525514398983840908789573474863138871296082137285652250073261,
 nat_lit 92726325208604220774525681536458724284435427126380787232657229677896318839932600487,
 nat_lit 87742632606519495865471584763406258798335736265172013944505285758479329876350917379,
 nat_lit 82312445614251058131818113163297579470739607756708151742890692690803348724580968939,
 nat_lit 77584421992023780075126114792010685244254941253361115545740963921194433099946650684,
 nat_lit 72380261210068579864325022473074168828937969616523708374882362988943734607452464089,
 nat_lit 67572572611010709920745880711794444108496565603572140712442152985516342420510003059,
 nat_lit 63292896070946851198240458712858282395515877283375100591182955542502310068956114969,
 nat_lit 58627863365583422611171287544451767666522563049748509534307068536968263452093810392,
 nat_lit 54149950715298142425699699862096656788284698245849039952976202586333676217680777957,
 nat_lit 50416812947745803026280238847362703918548221553296276168290464333989691392060560560,
 nat_lit 46100082944868252395838337745644891600461261391084104426977426120036486895279295976]
private def jp01W2r4_c9 : List ℕ := [
 nat_lit 42529980452655126534094199655620175808214906451512918735261867373487102914783378730,
 nat_lit 39297064619269107065554533449122241236045356208945425829668931091895838295877526598,
 nat_lit 35182276034156215978776105536836683133000636407159418576610597433194180390955041728,
 nat_lit 32197618493983859287362866481747586963844281573477241406408921075064582517506234851,
 nat_lit 28940617918404408135495955998965168626234348971357481364822008056261658346536102231,
 nat_lit 25516876688826909006989891105762781840331924091510943946343610851928241913723154684,
 nat_lit 23312194841533838539401938832294745114112495429489175030715982136339032114579960104,
 nat_lit 20433139704414381390693038990250521722938806122336482583625168279551580391408462893,
 nat_lit 17831985609292322906886773272766306586786262945123428260425404265839920941860970547,
 nat_lit 15695852707980730200503060488828175525352679268761814300756983508194004992260361885,
 nat_lit 13304050810468345393199216352523548389468561003954044281173155952213973975141496808,
 nat_lit 11490283112537853973689048556369064515510144466632640428458122301605047849750666135,
 nat_lit 10058166230401065597074636348374427495250290657401618731219705340559573138681920325,
 nat_lit 7442190796444948932870257731357646797067424615223497865199352553068153396514805699,
 nat_lit 5402396900569150497079443188433314103680761798428462641987118439520459263926087208,
 nat_lit 6851187835163583793145615722447457189117816336959096159816764854403191283987513472]
private def jp01W2r4_c10 : List ℕ := [
 nat_lit 2738251915969387107377485277824605187519282503582611481726306709060237922801538316,
 nat_lit 3321844169404781068315917676115287670315967816849715685099522417387533704727077096,
 nat_lit 2697493124410300871699665986428432789894432059171320467744680500835028911508909603,
 nat_lit 2254704076665059027163721266656487806545755009631390985426252771615554489631848861,
 nat_lit 1949012888637797449427566668251548026460750861421494973349600220599565739363075105,
 nat_lit 1430264198549618272829066150017265604591218967913099652725055331200332296746094080,
 nat_lit 1823031076995689031468259593447092507463993642471991794285432082959726332048217822,
 nat_lit 1873053222884126188440181253816543251016378188842897343590860659650866751017738344,
 nat_lit 1576625401995850432896407884338594127189320641551544260817484149167860777050843749,
 nat_lit 2630796816961373579651736363328279397054082877058679299923107247777756497030804422,
 nat_lit 2930930005907422447951838248105902683926258885411854767395333264388468613741920045,
 nat_lit 3733137746791876488915517456665406305771000931520573348358573624181084099932425084,
 nat_lit 5107821728814516761536356101284039490203286179163787578506331921290741307704695162,
 nat_lit 5652507834523918993721361668379754412871922477686463207820057357739405603757959912,
 nat_lit 6891946619655279136903133258862861087954991317951486489423103868411895570977324439,
 nat_lit 8774263257383275692467579096019703417762691267733080854023269567360117952526471929]
private def jp01W2r4_c11 : List ℕ := [
 nat_lit 9758033039688173771176454218609063091267049158910799953804990905772483188777069785,
 nat_lit 11501399112467135514203551730243083531028451427739637836272782505635872432009021654,
 nat_lit 13278113314897258008637094262469640018983571583205279749274755992751642915395627224,
 nat_lit 15027037430045207347821965875312678250297539949753787335378042887503036324884008176,
 nat_lit 17296562834943245115461627913019379067227706839101284106014534742294157643588580680,
 nat_lit 19214080273099924040025850707755141171082789265361160120480705089573619283701801702,
 nat_lit 21348360520419048562951496242131045723425060319014814346228182105573754968408069368,
 nat_lit 24199625542870192099866224985959585169960847423072397641586029991292506819718548485,
 nat_lit 26663681726593969134339744748904767927780346260743392387048591435818196165072521559,
 nat_lit 29413049678271306114279998751816413195002883276521443279725593264944587489675316329,
 nat_lit 32238377289518347416924314291138179782791688040218545587692229478930518438577706486,
 nat_lit 35169307261855659731926991846410861794116744207135719162849201011534105286531884498,
 nat_lit 38431865902773109479573971414247970751626176474268598133371162552041588859792276631,
 nat_lit 41470250964400768146347907172816966587335164201602952365982580703890275156749212351,
 nat_lit 44545689505627170575508207358021871762468978325270109391775880942752018116113891342,
 nat_lit 48660478084997800698020911582869210893232248784666171864273843082448283170405133427]
private def jp01W2r4_c12 : List ℕ := [
 nat_lit 52058281900720926679151207867910612837815915820992028803461450635831286007159382544,
 nat_lit 55748808152931217531683850498770338961329095337032019862153509260794582489714728902,
 nat_lit 60054422137769295993271774035264526806509008482427802516413773010665065406770275776,
 nat_lit 63630082648498963229496869749160040580406936774744511695294855559600421669824476610,
 nat_lit 67980160759383793223444139128987759751827224404207001346947666434947245537007111708,
 nat_lit 72467336787409147517270563935515642415721089391925430492961014200243855125152690311,
 nat_lit 76409826684989230877968464375244322404779741545404053482121560485999340308265622822,
 nat_lit 81697357835685229040738207371508445806690032079344086065878006245904744853194101488,
 nat_lit 86514309766986842429039391371289591018001812067292347609482173433940797949733491947,
 nat_lit 91049655318269698779319750578712762326036134983852512747737424995297652872034148785,
 nat_lit 96637319542183232948085259175296283461001418732023738429653693307109746117862816083,
 nat_lit 101756257339392381759626595946471273152707177419553510973094727960275944898395741630,
 nat_lit 107073431267141691067523802648272103651539453405373728634760823534720975120091729376,
 nat_lit 113103884562652900033145337728245672024394777455630894214275130086456073184206064241,
 nat_lit 118467375270883165676764125111533325864255943147889124671658546822601907379214734455,
 nat_lit 124110619751961152331904148683674546822813934653078545452028066135146360294673525534]
private def jp01W2r4_c13 : List ℕ := [
 nat_lit 130393036720670006133740893985607708049239418260740194639008734154130342946672840388,
 nat_lit 135839897762745822191551282215921714986637936729795156737465368953213547351588372670,
 nat_lit 142259412624742767762192451375113592579111554752764463491907924412556014452228718445,
 nat_lit 149042051494931259633404056280787199570115104621554874219350633796046070296776314143,
 nat_lit 155035451341763569427414351509724525406037080697912026995568508317438148453476968948,
 nat_lit 162275700685106909622628837500958349235657129805660106521299545740056422656569693319,
 nat_lit 168624813898983302090315479923981483155447620063061234267125541150503335903371989049,
 nat_lit 175911380051077136387415268803376370808241996177554719340214890816985110793114704516,
 nat_lit 183390624281182778859727333777816267402865821435982538252809189755552757031204730147,
 nat_lit 189285832423973914540008518137337506100461966172766994217591491909825714424315650336,
 nat_lit 197398691073722125794561226352337506877253623132133610811187855177222957906046851725,
 nat_lit 205891347941368991595537208908194757061811816701359807424496706540905644144825149201,
 nat_lit 212972267304990134118091118832858213800658906917826213560049626463022943266393867985,
 nat_lit 219736379481538158107905149089918599327247073943969929457288121082764127883012765439,
 nat_lit 227163748832696463078811780326703103464445667552342198076875890632462699229221238402,
 nat_lit 235361830562600513568082004038925531485343513013934678024654694474960204304523069279]
private def jp01W2r4_c14 : List ℕ := [
 nat_lit 243654398587408749634446001794212112216915128865630923702668420527840428155646503632,
 nat_lit 251129937472425650740149207987209094641126941538875536173931753139280246905220751659,
 nat_lit 259253912216187788068350650200304450398878363099196815209151664899334052132329089322,
 nat_lit 267681725497076710948243813509007224721141629839591648142239605149784075996124021655,
 nat_lit 276037284442724207750911866206111951883386777174450537103985242839348953947996959120,
 nat_lit 284415075510584480895732680874848908846817016542792832620251437285579543075747427074,
 nat_lit 293130053224903939405290903232070446448224580891799987809285817016893054106357516191,
 nat_lit 301578245888321031144094016432196501195125518453006384974685600688547440991433338904,
 nat_lit 310369183188444304378777231355629237563516487911765478762357052666817518558942702596,
 nat_lit 319404673441993017997416813430777615610026013713243979589792116827180878516144323669,
 nat_lit 328110387791823754857895066071349569975291349892804849909289201885829188200212390282,
 nat_lit 337683153423358870261801806334527920770236290646729036127343990227876879058009168532,
 nat_lit 346453711346254492979133767707706977906511086647748323264893466251840325382570273212,
 nat_lit 356185806968996309765197184372361575999434699804008735980865401749745302287723482426,
 nat_lit 365706697765313563789381825033988959684209180320944416360206951404685593641186117418,
 nat_lit 375142365600295492339488509682616279325751742935520938656297322554522251830005946057]
private def jp01W2r4_c15 : List ℕ := [
 nat_lit 385031938487369081629992254174207135856619319628314629271229380951950213383369817081,
 nat_lit 395334657656177382821351530705507155526279048389355764543656360913749430862701377621,
 nat_lit 404862959172708543269947313922145284659478140683075063692266150719859622848575769612,
 nat_lit 415041549183867228132704673742829265061732071691786495326374472562949899407985898915,
 nat_lit 425464692148893075676843921241853234831096449111880030788220810425787701647776806579,
 nat_lit 435487657566497526502724869053513422971309869235727575500850810970366819365056778169,
 nat_lit 446451781259457350418126354156164636199387040099087028882884768482558405979791507482,
 nat_lit 456797111958184198234838525494734016156149268665449354268719079768205653250147420554,
 nat_lit 467368468806709749174221470945250792155987538282360316136082563378976258588272290528,
 nat_lit 478693863940002478261496748463885843175337067285150845092199687653213382779546952840,
 nat_lit 489246694073243679089078742044798521125094489837032008810991051592738773855870711835,
 nat_lit 500338652280868099554720593276789354395735486953381462282507094498384158053533557758,
 nat_lit 511856725458602527421445153420127935475946055504654278547688947282504210960002935212,
 nat_lit 522353975383267556248146134485738873767912707410890845709302015854553596120509565321,
 nat_lit 534048052613058866716972034594162779048754167593632283956766281921355541978960773587,
 nat_lit 545319720147596712839866318709101267372487569541428709063211331920776027218755376342]
private def jp01W2r4_c16 : List ℕ := [
 nat_lit 557528840693676180835121720407306320953096247681828795775597793488972029800334983633,
 nat_lit 568433678878909122755067865334324188841472741879866546348274435658185456557356763849,
 nat_lit 580537197000291796655676948318307076478100292505975695687023688951657819331828985090,
 nat_lit 591914466948483638927108617406258951383131862888259583502837295458179297225067604765,
 nat_lit 604234747936451292138558123130557409862615614631337982767419460770383000868917298005,
 nat_lit 615776905915568549947711294255621825130443678666243178974321033178290016693092644755,
 nat_lit 627684040608108413131607453941920096627024853535650397520145018269715675590021727937,
 nat_lit 640428583888782889008292529984268946015343119530762396108372005705224314001651609967,
 nat_lit 652124513753131342470839929201959333924267475631808931450830997219630439689962961241,
 nat_lit 664885731065944727603576954864732847719017093640713816473846744466173741336406416328,
 nat_lit 677361636670435639542124490564794521247570303796220741827258917513194879467157461974,
 nat_lit 689259508018363827932227713552781398580142423544983710288378654107822117160930637873,
 nat_lit 702658045103859345536553896075367585169350405487503997939738966867749748566771363957,
 nat_lit 714772679275968176416267791028582247389105296060818446512984069272572626242133428057,
 nat_lit 727287490974296235761591011834800741556545971943502513958200237115861315448424118806,
 nat_lit 740493350093533038571969100903343131797968208611394256555885873967298462447527692743]
private def jp01W2r4_c17 : List ℕ := [
 nat_lit 752895148680520508057749773014157449482651112478740442426392707344907458213646497779,
 nat_lit 765869423532056891280051393825736151707892665170358811008980266920689250573415318068,
 nat_lit 779440259291392129637527563687912515156617436260819135461419327411529760313335753421,
 nat_lit 791871700696070412662364551910013140366539871325137828591078623548493662936151421512,
 nat_lit 805033095567347983402608287652313315578793756812615245231568223817107019744520951374,
 nat_lit 818650248214941870846932234317879693543737110671739329262124305023926672342823131317,
 nat_lit 831937624900070117050466179117024869190110918252309252570903662952753064058151893609,
 nat_lit 845788214493209341120806459503534228823323678613433885671246760690609135033423837920,
 nat_lit 859748111770441998738500977381467442047033353149407178184288621167699933573649832652,
 nat_lit 872994729662686004030302457947285514596235616449139915099139432723374443236629158672,
 nat_lit 887054671367742797651681525139538224701918977284834473264158868810521605356136675768,
 nat_lit 900671824022404076830425889606567127660945517047142829562018684070827169176151357591,
 nat_lit 914620605265253921243197879277631752431667906630524903918547320066728112903908448101,
 nat_lit 929401237070654442817673546515256450443688921329512179245573956174911718017967543752,
 nat_lit 942972072842799328818845204956744718454272944495797097038393506328942982742625187381,
 nat_lit 957352527132140000027358859933232411770940412981534432748235568397873162389223880224]
private def jp01W2r4_c18 : List ℕ := [
 nat_lit 972068315317654193688662729843611960806990523870097885680213528760819434498725779171,
 nat_lit 986317229760051152297808127243907775771841988957116336713797039803515233188871969243,
 nat_lit 1001012638573638230633291279246919392954473506208035548245873324668316651758668561779,
 nat_lit 1015950747668989810732111964689140893324737324190654146517462563201107911215717417689,
 nat_lit 1029979193876302315893325062819206871102203260459495033964076371959039119400055794309,
 nat_lit 1044822816645829866350837504516959370186179719129933182768304215612866318017679848126,
 nat_lit 1060970721744400668020506738060515264554505113121709226156597658169290910704056212652,
 nat_lit 1073852362862707527113332276392063303949601150797900544190165000644612759704937327545,
 nat_lit 1091721401948506607101438178332801280828777192917294404678188789873220739036506216598,
 nat_lit 1105681299254892255083886698180606608521658777854278538078186641321840198197539597960,
 nat_lit 1120528627305460315850770356354936509856191735286048862857247563879681639552727590033,
 nat_lit 1136228185337769331668617128321956770589610474729692851578935309309849145538698345712,
 nat_lit 1151718391221056991365391164588144011399132004847460420961384491604598109124284053862,
 nat_lit 1166675027074980699727415263712485554772321894953791906540959053966373553294600640910,
 nat_lit 1181939206716151854515358545202519828358446966394725310970650778019801132043890547673,
 nat_lit 1197570215851509422946749004472520844235114868822116448880645508988335328879585902998]
private def jp01W2r4_c19 : List ℕ := [
 nat_lit 1213897830257116609842432174241842624621192590598033723383233813210965844394929310459,
 nat_lit 1228772948435162630601057088167962895486505855067255981021261087659049203673146784280,
 nat_lit 1244429894963172398240309236254343128338157597459148802598697002521557301219794209714,
 nat_lit 1260879785894080627938391756967716312390060309724500764497747194071367918557711090016,
 nat_lit 1276151376330998426339667377520630549739225167353800640171996768683201559388420824209,
 nat_lit 1291858345016822851877204259637760564302091629466099659655246583004723687177476053672,
 nat_lit 1308760288341854846226197816518552978209667955445270558863843128868289550242787523905,
 nat_lit 1323707660821572178190041613258073768610274833904860578682513954543806844057322129039,
 nat_lit 1339735142127900851618909706173565248186188420645040399697825886634842701363177173603,
 nat_lit 1356327688968405146256506627001131277640130614325349862780333774647515353285532156676,
 nat_lit 1372351464890332706800302739092820016382566636976847624984989307413206782331743467925,
 nat_lit 1388336334702521507412105997228001034740336745375459488121636033583511524221111866613,
 nat_lit 1404958524294459837179598346253722751615283465832095851091058578540225491863819375953,
 nat_lit 1420533953134665693841333665683433454532776311676506174558100749539381732043485756402,
 nat_lit 1437274713898865487240962770639418112079868140673408126522767662804839981159170098789,
 nat_lit 1454323018448987608091345760692518668671112461562939169228819634730107313450268981093]
private def jp01W2r4_c20 : List ℕ := [
 nat_lit 1470152263653045674060311153722810429316728944945032146743287561370347731999299751791,
 nat_lit 1487224653008967728297898669250599163132479989754975674322476569147883893999269399621,
 nat_lit 1503652311864042938166726707119602534919889519880464757046027392302465574481222856758,
 nat_lit 1520291175506672057785154197768669616034567411441755014909572485186135495876077140439,
 nat_lit 1538065728228218166043364376394286290810110166610991810897451481681913164214643010032,
 nat_lit 1554517471813118872981766918884056485638753882469871083987057543486815248274342986469,
 nat_lit 1571471290031674687850971666048564287638476554918792213615182008900544722812494184807,
 nat_lit 1588916066801356236098628371610272282758265118146682950153889352563820082773830035225,
 nat_lit 1605404863908260018986902730924517338613985181981764089192404246194836746707560068285,
 nat_lit 1622949685060711060645533357192244285900276270124208469268745507120893572385251698841,
 nat_lit 1640022074408240595327293995086910030552525350497481892066907918477394580407373857967,
 nat_lit 1656568304371970761964075148366150874374891419318817175951825404244913823679069259760,
 nat_lit 1674528124466774692320194429964725503833454761093255026546097963712687072465619923295,
 nat_lit 1692595399653519244258995011724597302991866003011440678155450142304108894877946807337,
 nat_lit 1709356539765351994259385120591074211742933673886728543963191464662155998674683428986,
 nat_lit 1727501627282002053526987457285546910454885949102598485925179715486696456839234528056]
private def jp01W2r4_c21 : List ℕ := [
 nat_lit 1745135376775772421885622709784158718317265176067917924545952019788049779544821231561,
 nat_lit 1762359685362049776058893249137763918694987700719042483095275595227304478036599891114,
 nat_lit 1780228724464633911376754435487302906779770514799571524776132793621037699131223933346,
 nat_lit 1798014393185225891333692512199701750355732845334598298757242703845742477384616855431,
 nat_lit 1815611089198072376313553653613340219195406202245931147048971332595249585477182109256,
 nat_lit 1833728386639808193880288798146178126042760792257520021945320105993339989106527915436,
 nat_lit 1851454769834121390605671166058108589537057250424930791397081204951585094600113884830,
 nat_lit 1869186711022656985145450125962072745275968001331323263776513440071125712204081264752,
 nat_lit 1887428137589355745077707592103792193088145942152733091591064440850850224583789152977,
 nat_lit 1905043360328529398124816772971393518761556228160838310695008196082928455714907047749,
 nat_lit 1923197711192441398570882859108728077964637668548066472433357476402137998181632846851,
 nat_lit 1940572086375400345224103909271890900965581278795423369612704379027305682852667013879,
 nat_lit 1959561993085553835963982027411753930110224154366309725432835465826308223328142913989,
 nat_lit 1977829357041371112558899083419226463418197259101227483619711625308250484857047864341,
 nat_lit 1995989265919824262911482537510854987601613769723712742032196589739551325801035948141,
 nat_lit 2013235806637148628224235900407142922157260023554597348889427061342257181123270874755]
private def jp01W2r4_c22 : List ℕ := [
 nat_lit 2031740312821760329647046966544802588701419675997463661127500245707193706650976449675,
 nat_lit 2049644552688994497010263950032016585600404326505673941567404230789664063775646088532,
 nat_lit 2067533971208560334009880704958390772817925734402562622712701485251383577198114189018,
 nat_lit 2086190396631478170433895564987078324833736147487858860913552703567057846959477852667,
 nat_lit 2104170596180367624532058030472382114578727425512206488593953717017498561307399032755,
 nat_lit 2122445370834313191649830885637572334063347773812489422178553827983811895384675237495,
 nat_lit 2140905412880951924906154491619381770379986602068163018041707380163568517395949524981,
 nat_lit 2158666996882761199104950488117266664842718582462288532740718552554753388524725771213,
 nat_lit 2177254873391500802406277855119842857441871451188010807355024789660329348749661161616,
 nat_lit 2195868687344131214025215638774418462542678952184330994736549062157547058734678744961,
 nat_lit 2214262033097014092850572913659323169357186641220501764804689199613959860477817037149,
 nat_lit 2232933279990396118002815232440079519769161890299279409325808303984015729449609219524,
 nat_lit 2252039905164488051262575532082532179710007797948806899840419161484821036156395464066,
 nat_lit 2270012694001556107118425353647780520479508992020131292783533205539075792047799543982,
 nat_lit 2289386104264979319118202379711374374705242637919219645098804270255377965714455155982,
 nat_lit 2307521928391963092908932933653050311051118645612908696793971992573743425811428978300]
private def jp01W2r4_c23 : List ℕ := [
 nat_lit 2326904601924023540436123561616483451568777376738489493632088219484344663307005014406,
 nat_lit 2346146472317092323600084452410708335140985746075570173446948670826527883128243085577,
 nat_lit 2364728790907583981938684757194681061848333981438243513522804378322422417363886324937,
 nat_lit 2383016534236653491886782350587829097947092975184114113218366068819577355760475816784,
 nat_lit 2402758626549753815619966170500337768361651386281952900593203029565128974969986413643,
 nat_lit 2421403935940055688852585899294952525593337208928707721405817997825647224343470952965,
 nat_lit 2440075182814444099949411617213575788724612312135862023856780204386635324615800642272,
 nat_lit 2459867297384744265518029322925402177311132175476935759782606912029993022451237359234,
 nat_lit 2478566334288992311318571059401293945856840844302322297233406551715056594722685415419,
 nat_lit 2497952713249625046875917652784213963741441881596295370583511726783522852154299481141,
 nat_lit 2517392819760424356899080245035920256368568873611471365986969576165590747420626236655,
 nat_lit 2535795428901648394959584556378189530201546006039335654096227127630315568614316055090,
 nat_lit 2555457856244985514433115898091242649494006558709429865800960242943377000470538660317,
 nat_lit 2575240707398233241852090637969266061012097362695650592738243056897658525355732330193,
 nat_lit 2593747066245671653522245666339304504917571520307489542232834829712829464715470459196,
 nat_lit 2613211257549902978010397629477465651716856711127534632145839255539558696523221264013]
private def jp01W2r4_c24 : List ℕ := [
 nat_lit 2632579109733411682172824588829593490891563149979074039392361094051043677774124722417,
 nat_lit 2651092879338609518402336591283779953160359359877702029950398131035813029724750616409,
 nat_lit 2670923899958575616845843188750339256729543951731804310287201889235901254956813103332,
 nat_lit 2690212087231952233513904643231897868951728089446732452461133469025509485126168573875,
 nat_lit 2709218668056844742739775824823672318977292411793971564632660188372891530567896754829,
 nat_lit 2728721765468164557089314825067761184539467892861346414426012674009730099753016068568,
 nat_lit 2748267474299416653949938131081027348451165135127009154256553086182339604672580670952,
 nat_lit 2766696020936211760649409792912831389021185834897535283494485986538453083968097242814,
 nat_lit 2786886460331917213376723553600456722026394537422709759579176053143303577629590090312,
 nat_lit 2805933799958969895439435682190391320495546605157883689715068574137872476190242358129,
 nat_lit 2825292388761646544499209867721757617364282408599084677799506141248685923475777831044,
 nat_lit 2844599102789619881639101342748924002457547655866673975319471889626790107029617240704,
 nat_lit 2863852089195869303963155025763351887555598262333028846001545870356823943598011138157,
 nat_lit 2882801237138757851922128377802191162786824270216135944154901319179594579647989990119,
 nat_lit 2902296923792318262880086101241555922695532935937682503364661166461173657762910728403,
 nat_lit 2921401696350846627393483074343179880123544374366147146925662177588685787990995127308]
private def jp01W2r4_c25 : List ℕ := [
 nat_lit 2940880708998329129724917800132517567845812433986016808422237967650573305929034388218,
 nat_lit 2960231887157649755484325277713327654387383812291779160506676464960430133935279867559,
 nat_lit 2978925366087994167989440736254681695532973949643748612256786794866775984643061900986,
 nat_lit 2998952770177882290993846403657182443466490764048247117423747070607573716319048528358,
 nat_lit 3018222430664858924859096442329313675238521315908760064552436070476172832324945849133,
 nat_lit 3036513879339458914268082861498708658313153906630850355427225138240627427320604201185,
 nat_lit 3057284205718602029531538790160297893392136611315372043816373223637745558982684057871,
 nat_lit 3076440853077011307915664089032624048928313278924871437299843190420314662510635737168,
 nat_lit 3095193617605191828416140217655726179846124423059901367733430515684482870286434618355,
 nat_lit 3115263633150349171120014535215378935592812739736449477096879503784847648178855109250,
 nat_lit 3135413313771280592625469815026913824907160074542644067103674723670712714743246628774,
 nat_lit 3153367575836966893426259631929787204042022506422448099529843834379330504789385681578,
 nat_lit 3172576098101267939897764903969809806741703378227872847957423440308823828793278215970,
 nat_lit 3191441875709869209458255727378513103740562822692954566230321561408921563066160283587,
 nat_lit 3210465130574409716486444915252359213367566725653490822956074911739675967956903195581,
 nat_lit 3230662980664709780877342584545595880388782218444706261641854270152537906424116908963]
private def jp01W2r4_c26 : List ℕ := [
 nat_lit 3250464358556652597707966541151844199534949060953294342592086759340559702936520253942,
 nat_lit 3270745578950320102014686615275009184522088373292820029257083290748533593206869024202,
 nat_lit 3291921640823843842823306138480841458312133283358886786272286109774489109457157654641,
 nat_lit 3309827733418394651672940585316296710234464011070684997888738295194521431758645748673,
 nat_lit 3329814378643399501448108082296348232388284246863214593495741367707341614359656622068,
 nat_lit 3349817698028639717433501877601335892421077011805163201545889721139113743354463197838,
 nat_lit 3369322648062590451297328675563585558498772526660169411290232414382495334855945550520,
 nat_lit 3387728962545369539438318458584166371176912601698349936847075074735269306032689448992,
 nat_lit 3408399244505081067425431927746414533123891608534096663815652273537565818586749288444,
 nat_lit 3427492901005815904182459681160665540059608237420474778235825879471959119347463202554,
 nat_lit 3447255372741198489642630162879819080057248183430585067330632799688209307095465605576,
 nat_lit 3466860367207390479594275477233426958617694253524577135929428277293266628741364775438,
 nat_lit 3486063331444782456394547633626743973923909754580897727190909661099730177866455836512,
 nat_lit 3505627567058459107204148393954066290616998973214340896704257025418641038403719069933,
 nat_lit 3525284436375770580012273801457197439807038427469823393050273309153520418308995565488,
 nat_lit 3544589297654783373110074629617420356162575585651267355475597732315293347845503302595]
private def jp01W2r4_c27 : List ℕ := [
 nat_lit 3563529182248201414424934717359277009951841802595768916551431014051341946621605534734,
 nat_lit 3583593639799578084876520988745312170808523720928101564327677009494080274137095677952,
 nat_lit 3602001806996864183920825754429740103731498702765901061993862362269019920934588195397,
 nat_lit 3622403451165547049056459184238374886275145369678470128031990647426379257896338015911,
 nat_lit 3640932042153750140200482818304846467454745199019843867137715183309596319299365870052,
 nat_lit 3659786703734152564336835080708314260583351629698049290942099303317054355134129510393,
 nat_lit 3679664041272855428157732207032917502943195623344008815363111445082673275843468247369,
 nat_lit 3698939259770839500107475886226138873052500288709292447531699210652424198177197365273,
 nat_lit 3717273319977566570961577143322959188810608563290196937684764401724516527659613723405,
 nat_lit 3736791238769241369417835891539332469055750226864947171451686962047694032303772256334,
 nat_lit 3756010877078968029462551894050856492247462116278592576041770788259589971431851762289,
 nat_lit 3774394959500048883454684196412910404211439112814233618503719393366500945879989266620,
 nat_lit 3793962900470740513011553105495132631922607159814819035402082331005009384639109159324,
 nat_lit 3812787919230360139455177594438085663373195085820783925496799238342336867713259943838,
 nat_lit 3830899658620892735786856747125239275697321194255485191401162577887389230297001902246,
 nat_lit 3850595434070028578320419243012225717066491730109197893431141858054646260664311772035]
private def jp01W2r4_c28 : List ℕ := [
 nat_lit 3869642773728442798205129774118989409867796968442048584209263999006200467005624996848,
 nat_lit 3888167659317668295551520173440204303755790667660580059637504187110990440370344124326,
 nat_lit 3907711515584595423613352073492865659970062114641633258225138160143504262707110221470,
 nat_lit 3926627315381931174916373337435062932962401564680702019478272430536837662667865782827,
 nat_lit 3945328204966674422147938549603278965335363685801279573878795972056471213934879836386,
 nat_lit 3964362575902701548223238511174054194430397351081795972436640365797407748949791818473,
 nat_lit 3983283933743289716973543438025655506016031973326354973112326186756082129325784082586,
 nat_lit 4001866252238813321779722119041380659417257414712417690255089166176412605497943538204,
 nat_lit 4021260041888740125278826234257531268532339891180183821781769036352883922860585252481,
 nat_lit 4039775664136004206949551607044374469787694610242763240610983380174864534815147024245,
 nat_lit 4058574745453941605811498490466081581651881500592195594081459252965069151924360573574,
 nat_lit 4077703602783374679974911226080962930719536815093546620170498711400575004830047416597,
 nat_lit 4096171055528141726290923609349194140335065662705932195104536494052648114035885644669,
 nat_lit 4114829333613002839635848055379610784262316881664905339787670463283821588738659922060,
 nat_lit 4133750691488044534784940196949378508118110429751636226903975358344171680728874086517,
 nat_lit 4152534951415025868941808696495022596830812184874105078235730366760663103278444108781]
private def jp01W2r4_c29 : List ℕ := [
 nat_lit 4170681891590968945590937415901522749159752477079968930615357862222847642967940526675,
 nat_lit 4190023806388009410954424102623772873318186761997910051343141876269065194889277944540,
 nat_lit 4208183715237751297452169637243589833453593331336253714778260647924803978403271581550,
 nat_lit 4226901278947392934002822330728052804685900102625879406492430255518736283635600864844,
 nat_lit 4245602168572331949430600685915384389226579361334266895801132248938955229324309035036,
 nat_lit 4263771340838242835696566642963112305837279895264463225591890778408845121372811158716,
 nat_lit 4281779330446144894643234734641565633226076778300065136179556702019179257153187609335,
 nat_lit 4300322742808519002218508575362141064584117041943801616051072336322354549343871843013,
 nat_lit 4318332585107517337191761091213705141672935178259427348382300919130112677484162622764,
 nat_lit 4337131666440914654399883105401880077185546948822307377204037412102785084879728621823,
 nat_lit 4356275345123758296195894862200661717092086990267888578567564347990452503053233289261,
 nat_lit 4373314386331035591212883018305084744915024391837866878112529342694684076202003981142,
 nat_lit 4391872620047703683634406844116748457918420819145034437112983421530664389327306749435,
 nat_lit 4410019560243523789867606511813869381040829937278942800067470083736516592574567625470,
 nat_lit 4427627372315930679577316084263415572714789147019155863169335642573508465698461227457,
 nat_lit 4445642772644930060055801227393802487915433431872290080291756356188024332384533227853]
private def jp01W2r4_c30 : List ℕ := [
 nat_lit 4463847145678582955464868436512149965951235828248347812325543947959681188572758794736,
 nat_lit 4481323417932757411279087449852401116890112067197785668342741684514567439781803050185,
 nat_lit 4499437009921185075379398326741246240950647921821764120251598545544629388503288106868,
 nat_lit 4517083728177096617567426298809629005497749847855365110939800933825295639805347234750,
 nat_lit 4534283952014996578805952606275521116350868725533878104142627392919659733149287735538,
 nat_lit 4552486472337676166287498344868722968751336702280646546810990050239736244422156019066,
 nat_lit 4569445848576957096105882885349313221351936813024909148423794423995837252792233595879,
 nat_lit 4586657188471325474550590171614626064630848246276670570657283622985629775829929453898,
 nat_lit 4604274263909987916861374484920280554777313912853694816317041245851096567508505159191,
 nat_lit 4621783884276586775493220492507811468549214699523941683174549518153218351045839194996,
 nat_lit 4638737702492050618951544815369079419281571750151130169449319715237912053396119607563,
 nat_lit 4655737837518473521556158103609355898879581370905646922368297970739775271950714883482,
 nat_lit 4673171498314286766250682707640686200921581193801746066589412980747507701065187125643,
 nat_lit 4689953017847960055680642896383041991815019967344742773756120652523091564300733427063,
 nat_lit 4707132862249001282388662122316398180297295588281253769552542025215860074318787549218,
 nat_lit 4724599871090098722167085590073855452999084221677853011324750282018619276533505894917]
private def jp01W2r4_c31 : List ℕ := [
 nat_lit 4740877463390896682169369688040194198751407787383867759213291042387643973101091611719,
 nat_lit 4758212932383725300272602890431605205846617943711119977099347080623981850156415271970,
 nat_lit 4775155634580707947790275933141275772058658756534757232411587394573876672773443144611,
 nat_lit 4791520302489766332252509995660153347872935594262912922579536958287387423869948951124,
 nat_lit 4808594544508956803764580734877305630262497557265402417752334432825639405195354918509,
 nat_lit 4825765125600281590263177345934696090052987491654679118475742860258566301676976884281,
 nat_lit 4842189079061238037447506535411440092019025139039543029868539682526478101741921725730,
 nat_lit 4858581537104400051549101409618251766953946741468405607324150487555395917168158225834,
 nat_lit 4876191201873203738365080088609257149955189075102787512748252953899348370691368690660,
 nat_lit 4892103817408457096893860061981504064035072357828836106394361981989659606654379866863,
 nat_lit 4908166499495337416472983010179727160487528142951968975426788870300817289632479934069,
 nat_lit 4924696055405726514131361225348525827869784284616701423572425560410344682257432139537,
 nat_lit 4940623492321334856661548604807662141589880025372024579242375431187248572380683656610,
 nat_lit 4957141932170396709686535687422291122364575162690928343611667249641725729084189673678,
 nat_lit 4974140214559612191328394612228623251977320978215191733421407162966932267204047264285,
 nat_lit 4990528967259010594096347170981124769662696917787817544958447772097736791303294308981]
private def jp01W2r4_c32 : List ℕ := [
 nat_lit 5006867697754214607306827342635798821004545749610808382780463320184330734464948564079,
 nat_lit 5022632099337944613060522210556881092833316768661732191757292118237400312871487910794,
 nat_lit 5039132012537978889222571582511395771082550604334502765356564362564787426768768637740,
 nat_lit 5054281326384222287522493498213486636656294893667683332711149632006072634794786400411,
 nat_lit 5070516307137433256685031766494078065936066503344332365505145810740144373248063232367,
 nat_lit 5086163990349542613174709561673936782664566266053490171870978662151529728664766132007,
 nat_lit 5101694955019088830339679342625120784107834860659573110229466649216105632620284193014,
 nat_lit 5117924377806346951143658481767617958750849960444070000258043749587027803508163298900,
 nat_lit 5133144093284367569935453397987812665168470015158178739361699235376154914608606808375,
 nat_lit 5148039590878070158130372029700204272556687332910904922566601841541787230217668718288,
 nat_lit 5164202317332701800662612440927919603418450720054333463790834945211420124655119431480,
 nat_lit 5178982949175647839740162173247229424805914759292182304421280990060823050845295289470,
 nat_lit 5193809897829552917638721724318610398290825572999369118628188525063340909126213399418,
 nat_lit 5209161153202222109142360092681437679510385203376950875168327199977257330879840511281,
 nat_lit 5224215980689954802468824987300688217519724316641023883931342647014088873505966553599,
 nat_lit 5238789113035221684591277828930790340732841134882693537381239682140829320210992542024]
private def jp01W2r4_c33 : List ℕ := [
 nat_lit 5253532691373833114470180125821462528856693687112907174399306654432083661853816392206,
 nat_lit 5268543054762905189770222912551192956364742453435046135665197034808696625703187186867,
 nat_lit 5282467751252518810240426642303338561140953544495474389990710079988200095050505920937,
 nat_lit 5297411418362853237057610158801219837142062535423603311502814720313081688807833558721,
 nat_lit 5311491739463247861504072633600144838590493022521787710061364284920716147407816408626,
 nat_lit 5325294159471289924876983106596964089202263896778762832582478138473322284801784167948,
 nat_lit 5339815417014467331875550753571922536259229288666306124452102548045605149632583032276,
 nat_lit 5353827189173739313886442800473886409255882867943699698455850112759544342789932031748,
 nat_lit 5367436931099352447104389420985508733074743978448601822163789243503066466773424767109,
 nat_lit 5382147161296828222527053215203980853563703214342129044565697413167622198561611808987,
 nat_lit 5395423422004554459884793690683218949585445414707648398638904155635831951804481250097,
 nat_lit 5408944235580897471777143326944645836881241384565948049044671033340672631938755716163,
 nat_lit 5423104221629853143604334496338446170732832514931879661346036409284458653864900838400,
 nat_lit 5436763985820616916863938760617898219089788877053482104157649966376438186930564154535,
 nat_lit 5449793840828165756850305370573681926842900008061451621314056115946159714697736578285,
 nat_lit 5463403582804575749183435609858061036527567249305230726244700373723981081497448751835]
private def jp01W2r4_c34 : List ℕ := [
 nat_lit 5477372743452039392468527132302470815081513974708024152132739780330233594187651547267,
 nat_lit 5489917197976892485617141811275361038102367938329221871338395593325166920274253315552,
 nat_lit 5503682564560549803804440678303505159694696918792309416209210164571941217619422156744,
 nat_lit 5517184851384946383725220868912297790839690531127179936045228900987645194803705303504,
 nat_lit 5529632966864167892396754044818083356224594504369148479625278847449941575722476612256,
 nat_lit 5542701728069356156956543802714602347187038573447758561201297089607156050533741436875,
 nat_lit 5556105823171601372029942714659423348977592929983593535191160274740438091711305003950,
 nat_lit 5568455746941922891903329843421333765970797619368045803936391651400913610866888959538,
 nat_lit 5581185468815297936132038710631062285242280839951100751461360433572341309099397625064,
 nat_lit 5594476550890127818406577738162039361588864372285867204343758113201516539389714243811,
 nat_lit 5606300315274883122854269696130070657158856648551414038979357964356323772285045975865,
 nat_lit 5618085173490710260685884476578693756158475790009889425142928992762750529855820026034,
 nat_lit 5631989490611047052856155653548503464582299709458454419866708138685494371133384593768,
 nat_lit 5644104124787573003504062095949231885530793539735178531988443380599585147083581485715,
 nat_lit 5654723651139479026599898584594662073592161131839050963624650286677069574620055695048,
 nat_lit 5667583060192553952569944984131898734064931229668893304056852003671555870305815364550]
private def jp01W2r4_c35 : List ℕ := [
 nat_lit 5679869993034527114209216581752085258049954518973610478614550473064460018781712201294,
 nat_lit 5691004562730549164009500873633532519293424985423080082734222993720749812179863176458,
 nat_lit 5703172924427205274383572145788391877844845624453103598140672684450171582857081548196,
 nat_lit 5714489056243714163207328553108256173273328236937127920725630568481058588114680246876,
 nat_lit 5725619920589346906646089183644771150657228647232905767918253146554120663404676026669,
 nat_lit 5737684532544451685791535989867324971342199737164146919134820767398026689811896453389,
 nat_lit 5748715352505548082330486890628952707700762309510710659627957757843970982540572433627,
 nat_lit 5759179254345174847953604152474857985948944011130176145123209621200118705479984908872,
 nat_lit 5770424984455698955993516608665358341618697523550184733644796553740878729882169773888,
 nat_lit 5781237188973959159775634316750049585705525414892569098758401619110020234250181914228,
 nat_lit 5791727028166484068808475777034604657380378995441075785874183927603857911559297132224,
 nat_lit 5802366934008695993322407116180724257278506578065820431572465572109841201154082682543,
 nat_lit 5813247687370460519412382174332186422908070068988059481665436410346337290548689182595,
 nat_lit 5823042773955562513698895001033021433937213249447745929728992608223970679359508521196,
 nat_lit 5833158372999060476391562926019069112911428108788925128818666670747269322492394027309,
 nat_lit 5843323994341720913873126461912534066366968090889917445974166877186333193821506201735]
private def jp01W2r4_c36 : List ℕ := [
 nat_lit 5853191335121158231534624800788138680232917025767618951415284948574581422965931356071,
 nat_lit 5862593654817654750845395906946220803295684736896764517472868291144654157623359966493,
 nat_lit 5872781508245424159669417748046059101399283233161157305438948358355149194930931924996,
 nat_lit 5881892958085218409573420269921588668696554807758538111710331452646345874978402273983,
 nat_lit 5891074809598310757767890367684171900143892647883081850838557268659788000353505618490,
 nat_lit 5900430812456462096747977312641082139046428519046252739821490461627726945264853737119,
 nat_lit 5909664538854244055624346158968681284711554599302119143831411133662810126033941637210,
 nat_lit 5917944138121769965824432425644692948064128575677586498412500540400745047961060771783,
 nat_lit 5927261234816293664954995145067521241720142532007530020424801164659355896225734130242,
 nat_lit 5936281903715106689227741484976180860014357185745763633943161679115975012152756011527,
 nat_lit 5944278043969823528768393614322414852755470887827941188992649150899558490941852425812,
 nat_lit 5953619225428626270850096581498432736500949551642602189631783731970192484957087878395,
 nat_lit 5962008132533961341669444465360633508754347760325872650537783206636338227946004779266,
 nat_lit 5969689318236603920175396687151096376647799765467553773957116244884924203141499906116,
 nat_lit 5978018939760446226984195036462295904539689369553545751530123899230614593698575700264,
 nat_lit 5986541239381293957076746158645672557153081796007055749015924576963765863254628355409]
private def jp01W2r4_c37 : List ℕ := [
 nat_lit 5994357670273318703681222966867060327238661849798835950724600997350873724820146576644,
 nat_lit 6002179659167958363127496309903354776348275388440924116167377539150610330666293591713,
 nat_lit 6010805708523290033346125456204633912794071153771795386999191583221011322958413214303,
 nat_lit 6017925534038170864675739001105813379512893087423834920227737021309964518261585902052,
 nat_lit 6025132435215642662020368529632771168538975960761473903626363091644066192045850907104,
 nat_lit 6032511635064303944274043398465259798389281330436095170448615630719301872356136598176,
 nat_lit 6040157620042933988284202279542738936277160020260380759629739579875145674291676329099,
 nat_lit 6046816129762981958375880030471470614160616316595638363931450930388392790867014860788,
 nat_lit 6054415797791071985208891333467498781598409398682124735182267865960053600478049491495,
 nat_lit 6061270690939962767596971705705526238692078297373339809942561222637679235402942940670,
 nat_lit 6067443800122101047563083049083778724628310240791956373815717677629256109873213129156,
 nat_lit 6074461728643065932501678583894625764373075915239767561067178930927741169276246625276,
 nat_lit 6081303653073986728421685143955123501728499670755445344543630910982821793651015247302,
 nat_lit 6087052499949725124761770486578040239438865347872386182219602329218707040953504747385,
 nat_lit 6093088511323383974279998958186172915619491650353298279696112687538023749113549702819,
 nat_lit 6099930435754304770200005518246670652974915405868976063172564667593104373488318335813]
private def jp01W2r4_c38 : List ℕ := [
 nat_lit 6105316158635986383699020319849153493162082037171042178726867852882324737556408786896,
 nat_lit 6110929760292747892959658906206723098019463646284967244802814111193452575891748028658,
 nat_lit 6116873137908441386717406847422740839516070570593081483112394309329124969962476056238,
 nat_lit 6122225512650754158177210666914198271149553176668350087050410485286206042672334727788,
 nat_lit 6127359271789447639873503320148249132455172155776771996526972620990762628898289889775,
 nat_lit 6132698677810698459141215900007817114259715626957513079509985976786342375029855684006,
 nat_lit 6137899133211344533885299519252449870643992436660538211991754374772195141271043040573,
 nat_lit 6142056533332559934007281958275010371478206554075073648953503412108442729837111071005,
 nat_lit 6146808641653692881287434290396753042134559642219322635308453662019616135203400435238,
 nat_lit 6151199478660380789714581600916813151917055138600001689025634467588558957350450808487,
 nat_lit 6155955292364589712159042078730425465048847943956968348857648812714780103752231014623,
 nat_lit 6159897782283813661426727978857132245206201642600942548682002227480589316948291282503,
 nat_lit 6164127436677547384390109468134837851273357107352853284841394636894459860105756411024,
 nat_lit 6167604905414887128429746993676213141800730481882130616902046316456629984848209194223,
 nat_lit 6170441349049915877379925479409213270898958226557955435327069080345217321606082354441,
 nat_lit 6174439419213052967851830502509443908284835938293578129530373093126941015088281260938]
private def jp01W2r4_c39 : List ℕ := [
 nat_lit 6178170704259914331831837754993531464675546170432300935713593438050726099679324459933,
 nat_lit 6180104895750528662205214566144293668943778797768108485658961922958922397639109516269,
 nat_lit 6183676850927654106422744157959908161572202498635066145111241169411147115412052732056,
 nat_lit 6186426218841785944223956504192180243783476128413528687410141300665764481361801821669,
 nat_lit 6188427106594794566668534247032474464765930515614195303464219962084856961419006843222,
 nat_lit 6191015291949419325760233753101365289027874331880987833955585998179145331568914823455,
 nat_lit 6193247763937883428132834060176731678403636221388945076632887809247879542505609158327,
 nat_lit 6195107848415853153590637752178192582085490478726326177389294342338909579503520729583,
 nat_lit 6197025365826181972078102099119273831675414776284971371901432720136252020526351628610,
 nat_lit 6199224489685436622516741142878630154260028943313548495462439257293921856622696279271,
 nat_lit 6200671427970013993419787793959529558660872229483608581208935708461885269135170643298,
 nat_lit 6201684840563384019803712755805100301115263082131035243232072678052105330274460115191,
 nat_lit 6203663496152217262124190269627078622485047585329739330752255996948126990492609650574,
 nat_lit 6204671350732371287906719356260362474182299261122399519463553873372954319897558065824,
 nat_lit 6205338313315235112408344600606398502163760443789915729275532385797645164885693736925,
 nat_lit 6206288734989091015355480025318168076317594916976080408044916379040863163464088563322]
private def jp01W2r4_c40 : List ℕ := [
 nat_lit 6207222482614464684333910955013197722655177828910843910146231075740735149827317806918,
 nat_lit 6207774579439946280697751676420122360847627823892614831383195265779132302625223426577,
 nat_lit 6208046922489046430642754703281696638124920826455039171887790117256606336622768082407,
 nat_lit 6208875067706066650459161501653075896702266593735371290054242299200249856949285706348,
 nat_lit 6208523059684994736581039453429844252214834380808347764218340267334494523418399336627,
 nat_lit 6208133998183882373177139354671461705392796368674934448139478921244263214716045063879,
 nat_lit 6208195136421576167572114048637593417571902293173680779352015409098909111994812793852,
 nat_lit 6208045069778514845328596130458290767356141245326274443799316023912877060251888947531,
 nat_lit 6207229893301108499792218231003750773116977379084121961606668122156453325303791754820,
 nat_lit 6206735229382808446426160753185094353328615564400679530503886175507585500012168325452,
 nat_lit 6206090498898746648646232158340724678886231122704786162880410146517450769264996987710,
 nat_lit 6204658382036928610466116995868460651712452664645206498781422655887535674904225692577,
 nat_lit 6203222559804844245607887158113237854010357439538544401875041248373019298428272918694,
 nat_lit 6202381445894148197100653803628926701796145550787449035305079432048316340014410744446,
 nat_lit 6200756650954318349902827429111100245629905134563045029099199837124251944392308376149,
 nat_lit 6198561232458262634197254343451299815139508417794512390505299968534733476712053522012]
private def jp01W2r4_c41 : List ℕ := [
 nat_lit 6196514027939791257363196529002524004471203531905234793971672217620174198222289384809,
 nat_lit 6194670617486451340609578885814661240109859518642962873871200516729496895668945397683,
 nat_lit 6192047231347299524206254157212899837486372392193358226177423603013209898974848161193,
 nat_lit 6190061164994081196419722707159344148909700974518211221155018191584219955008786824602,
 nat_lit 6187482243020288489903180422479824108457554993727558844341604918634807650138258792538,
 nat_lit 6184571692441522163770665501685964708844357842735959231975142331918745227199748324656,
 nat_lit 6181149803858869742565570274370717723320508558567432857381818041036937776113869689666,
 nat_lit 6178357824395825764830116293818920287135952309654743880244707707454719154044007080359,
 nat_lit 6175163814721208539986116370197358469122628056227108864942743767843631281939276310945,
 nat_lit 6170476549913951085779956651639983376259138251001931670416847163888885552656035768879,
 nat_lit 6166939795562431914613862792471507497784714370353573171280125384241413560751074418725,
 nat_lit 6163039917150157467271965068986096999414709305016327224983524626199036337530564300303,
 nat_lit 6158328567625442468829014488311427764283378329272706667870984712937183986931469906689,
 nat_lit 6153769137309438875559177280289535106751968287629194356563973104756035955806978903325,
 nat_lit 6149233791839431003250228748105481913403267646230303000469506670279208219650670599406,
 nat_lit 6144578022513132782701039163869382503903626672837674042312038991329553232884482253352]
private def jp01W2r4_c42 : List ℕ := [
 nat_lit 6138932925336983098010779386674494924967281785232697194140941829940585477692351323130,
 nat_lit 6133771376034591275908568829384702183426236266262700785900088333256601828613830150399,
 nat_lit 6128341189039672561574946402930573930461212146958436917436826181954402431111468804672,
 nat_lit 6122118057640971961439478146082832932945807564851694430326796489666516203407031713539,
 nat_lit 6116082046281006169512044762844780191260085183451741853960955610200524947467392746888,
 nat_lit 6109853356883666074436134067535361454060029271851096981533834123054304997699942760029,
 nat_lit 6103318976356162960628349278674667074339373304352836066697632570449231092738224351474,
 nat_lit 6096395534237438256468949515794563827323021209621016985167528972939692674144897041464,
 nat_lit 6090164992146351603500870129885857263315941163530318466665640167558378761304022847431,
 nat_lit 6083058135333097417392644820817852632615746305103067270595553466172005440854976662634,
 nat_lit 59884065217717490284558244983121794367716564524948103939678992569]
private def jp01W2r4Get (q : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat (q / 16) fun c =>
  PipeFuseCert.withForcedNat (q % 16) fun rem =>
    let L :=
      cond (Nat.blt c 21) (
        cond (Nat.blt c 10) (
          cond (Nat.blt c 5) (
            cond (Nat.blt c 2) (
              cond (Nat.blt c 1) jp01W2r4_c0 jp01W2r4_c1
            ) (
              cond (Nat.blt c 3) (
                jp01W2r4_c2
              ) (
                cond (Nat.blt c 4) jp01W2r4_c3 jp01W2r4_c4
              )
            )
          ) (
            cond (Nat.blt c 7) (
              cond (Nat.blt c 6) jp01W2r4_c5 jp01W2r4_c6
            ) (
              cond (Nat.blt c 8) (
                jp01W2r4_c7
              ) (
                cond (Nat.blt c 9) jp01W2r4_c8 jp01W2r4_c9
              )
            )
          )
        ) (
          cond (Nat.blt c 15) (
            cond (Nat.blt c 12) (
              cond (Nat.blt c 11) jp01W2r4_c10 jp01W2r4_c11
            ) (
              cond (Nat.blt c 13) (
                jp01W2r4_c12
              ) (
                cond (Nat.blt c 14) jp01W2r4_c13 jp01W2r4_c14
              )
            )
          ) (
            cond (Nat.blt c 18) (
              cond (Nat.blt c 16) (
                jp01W2r4_c15
              ) (
                cond (Nat.blt c 17) jp01W2r4_c16 jp01W2r4_c17
              )
            ) (
              cond (Nat.blt c 19) (
                jp01W2r4_c18
              ) (
                cond (Nat.blt c 20) jp01W2r4_c19 jp01W2r4_c20
              )
            )
          )
        )
      ) (
        cond (Nat.blt c 32) (
          cond (Nat.blt c 26) (
            cond (Nat.blt c 23) (
              cond (Nat.blt c 22) jp01W2r4_c21 jp01W2r4_c22
            ) (
              cond (Nat.blt c 24) (
                jp01W2r4_c23
              ) (
                cond (Nat.blt c 25) jp01W2r4_c24 jp01W2r4_c25
              )
            )
          ) (
            cond (Nat.blt c 29) (
              cond (Nat.blt c 27) (
                jp01W2r4_c26
              ) (
                cond (Nat.blt c 28) jp01W2r4_c27 jp01W2r4_c28
              )
            ) (
              cond (Nat.blt c 30) (
                jp01W2r4_c29
              ) (
                cond (Nat.blt c 31) jp01W2r4_c30 jp01W2r4_c31
              )
            )
          )
        ) (
          cond (Nat.blt c 37) (
            cond (Nat.blt c 34) (
              cond (Nat.blt c 33) jp01W2r4_c32 jp01W2r4_c33
            ) (
              cond (Nat.blt c 35) (
                jp01W2r4_c34
              ) (
                cond (Nat.blt c 36) jp01W2r4_c35 jp01W2r4_c36
              )
            )
          ) (
            cond (Nat.blt c 40) (
              cond (Nat.blt c 38) (
                jp01W2r4_c37
              ) (
                cond (Nat.blt c 39) jp01W2r4_c38 jp01W2r4_c39
              )
            ) (
              cond (Nat.blt c 41) (
                jp01W2r4_c40
              ) (
                cond (Nat.blt c 42) jp01W2r4_c41 jp01W2r4_c42
              )
            )
          )
        )
      )
    jp01ListGet L rem
private def jp01W_2_r4 (j : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat j fun j =>
    jp01UnpackWK 11314635 4194304 (jp01W2r4Get (j / 12)) (j % 12)
private def jp01W_2 (r j : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat r fun r =>
    cond (_nEq r 3) (jp01W_2_r3 j) (jp01W_2_r4 j)
private def jp01B2r3_c0 : List ℕ := [
 nat_lit 69381009078975750252747381093304598917615719332203387773167186337339020160459620445782,
 nat_lit 69380657071019223484211571141400398158668209637096682014281471759834575234549325458840,
 nat_lit 69380306915736152119720686505020307597097749890634876147564478097703342473840133106907,
 nat_lit 69137123145306361778778843885536500181479540209541091029244262327966345144809033526301,
 nat_lit 69136772990023290414287959249162539602255231724540210883095084662744080546233534999393,
 nat_lit 69136424687413674453841999928324949184643556443995657017294183377423457373417090149028,
 nat_lit 68893242769657339516945082624377511930820667676110607923462559670483038145210450799080,
 nat_lit 68892896319721178960544048619076291675095657161102654622758022224237500583289055308076,
 nat_lit 68892548017111563000098089298238701257575325734252411677311014698466813952875430373488,
 nat_lit 68649369804702138871290611249218556016199324059352169308509240497280481787488549431221,
 nat_lit 68649023354765978314889988620062784071618068275049305484322162438212004725647081826043,
 nat_lit 68648678757503273162533879930297933977688378671888958720140053597257876419671915587136,
 nat_lit 68405500545093849087646707395193550738906891093432407515282610484736465409003052426630,
 nat_lit 68405157800504599285415218507049296831556416884952365102892178851103605878176057877708,
 nat_lit 68404815055915321930118647970565667160398599085535156655330245227604771423872663905299,
 nat_lit 68404472311326099788792851758592336967287679502321567816640089269429837677019981374298]
private def jp01B2r3_c1 : List ℕ := [
 nat_lit 68161295951590131064031121777399470482616099620030958727220822059922825527645246153377,
 nat_lit 68160955059674336719764863718707360712185707988227326752480701413506743016188894339561,
 nat_lit 68160616020431970172557732437151011080853185861076630860377335700456776823670739919153,
 nat_lit 67917441513369484458826314933743534514836912444660475755742763783323693790950092529785,
 nat_lit 67917102474127145518604570814448464604782646833378204508854028195892020402195876765634,
 nat_lit 67916763434884806578383649447432055297749458709409470872585291684690460985581907173131,
 nat_lit 67673592633169204065755872660563508713096612816604160145697863607752976807224595668564,
 nat_lit 67673255446600320529579465232944139266348206860820947328579188336836444114120055020958,
 nat_lit 67672918260031436993403057805324769819599800905040392987774106583164821950634524499175,
 nat_lit 67429749310989262277835230547870643977157424261135196184114951155053843514099313237042,
 nat_lit 67429413977093834145703748435787644692204160811235343222784797893740973711924073814908,
 nat_lit 67429078643198406013572266323704645407251075767299737003035780039070866050207143647943,
 nat_lit 67185911546829714309034340971377873248305600891244792265249587961673073132960209394195,
 nat_lit 67185576212934313783888656594226449884024581913771251211875269241294881363420613531998,
 nat_lit 67185244584385768852861226574815580899873343434000347722866520709644291482187855386794,
 nat_lit 66942077491635579990910148416055342214895817190684940948762270533274905766986909308918]
private def jp01B2r3_c2 : List ℕ := [
 nat_lit 66941745859468559824282491690288176280561117482922154278335074268253707739424230954819,
 nat_lit 66941414230920042500240860209277917319198674262676444239850955400631617809402680530576,
 nat_lit 66941084455044980580243742667658568235957549656546609556123234001775358774543802389981,
 nat_lit 66697919211349771886736951741939072460990000501094317463676460547520534477412812281130,
 nat_lit 66697591288148137763799372353600943800429403845013310176215020606569632751822752273528,
 nat_lit 66697261512273075843802666188127055000862281537973677706188309888150885329349690872774,
 nat_lit 66454099973924750351399927355079689526787922799019269776869535756728891606570235155221,
 nat_lit 66453772050723143835448146505142170889016121402463455939932725479806485319795662344804,
 nat_lit 66453444127521537319496365655204652251244320005907642102995915202884088049016571646387,
 nat_lit 66210284441846667231138552137693656938965282180159311762416959127138853468149093978370,
 nat_lit 66209958371318516119231696603292508462988801695448446026253803144975999952436859064402,
 nat_lit 66209632300790365007324841068891359987012321210737580290090647163403442255879422955426,
 nat_lit 65966474467788922716026154328516124813739809037311663055791899631982496088139046670066,
 nat_lit 65966148397260799211105097332515586360552123812123332314122189400845202740720753921603,
 nat_lit 65965826032079531300302293890786568185377489891577169328981712345943833248594741120404,
 nat_lit 65722668199078144222975204227212553057682746641802097752751192668589439909237650050277]
private def jp01B2r3_c3 : List ℕ := [
 nat_lit 65722345833896903919158199323878014923041922167050266696622697539597910934141435464758,
 nat_lit 65722023468715663615341194420549606770656083506029297162006850148725036889627070122888,
 nat_lit 65478867488387704335073231534117493736752742480125249036686269710953592419299119418074,
 nat_lit 65478546975879919435300740570179983489866631012499202231224353977716639963183415249453,
 nat_lit 65478226463372134535528660982387945499276113263323180797382160882193614500090026346879,
 nat_lit 65235072335717630659306035591094425076010306107107332892934180448105439933857317734610,
 nat_lit 65234753675883273556593081976975243104473048373982500721548255752058493276049999743014,
 nat_lit 65234435016048944060865927704719575275677851536651427388479716951885311890777892800377,
 nat_lit 64991282741067895642607709587124374302030856724024149574171024370610047545660665317069,
 nat_lit 64990964081233593699946048339353542520899693481386807354750458240366969259194125338145,
 nat_lit 64990647274072692001278432220379095114785024595465690865349545148300968685371097826678,
 nat_lit 64747496855383601775731270525306857584454847815098048192898184092260268342269755999434,
 nat_lit 64747180044604252448448403486085802683506164511557785600779864725437546520701465609247,
 nat_lit 64746865090116806153825712682641595457114696833020235809030390441598404351102060675957,
 nat_lit 64503716524101171332323476303105728088579840964497541217070274077255873158275189261002,
 nat_lit 64503401565995249802100147417165893610403029464700416921289720324236774764431352742432]
private def jp01B2r3_c4 : List ℕ := [
 nat_lit 64503086611507858721448230938238115844221923559161049614486788399961177112445784899958,
 nat_lit 64502773509693867830870465450336408761789240349263010759020914200639632382993951310029,
 nat_lit 64259626792733185570827129141580004581986105054096135691469807889708247342592317014052,
 nat_lit 64259313690919249894220137978188596977691663912734897897545850959175586529609715367803,
 nat_lit 64259002441778714407686886429683929755452419018691856925438310516759426884847849782994,
 nat_lit 64015857577491487551688475436457765755372484932269677982657577962836508230560007667242,
 nat_lit 64015546328350979672141022426353708555922035297751830440792257580797178113062098386305,
 nat_lit 64015235079210471792593980792382851675818660850096188868726991249641451857988543266010,
 nat_lit 63772092067596700340640083738553727536023508933223318689093667004870509479299359128626,
 nat_lit 63771782671129647865137556043979910516113572802783804427505669379401780794405501614987,
 nat_lit 63771473274662595389635028349406093496386324377010653030693132358022587486968702909156,
 nat_lit 63528330263048851544667341210123039662962626163697738127247800542082762301285889555005,
 nat_lit 63528022719255226866223940292684982782241903391605470868650451911761541372594317113750,
 nat_lit 63527715175461629794766337913647535924127288173010904707836108581642656765521875908848,
 nat_lit 63284574016521341353843576089900852252590254723876119337552161363097443346388840298570,
 nat_lit 63284268325401172079445100487999165533573509009934489259374572966344670545858875963300]
private def jp01B2r3_c5 : List ℕ := [
 nat_lit 63283962634281030412032423424498088837345558555518052631721614233620397705336279611135,
 nat_lit 63040823328014169768168788377887165304815050760064151399652855406133156673744630527578,
 nat_lit 63040517636894028100756111314386088608587100305647714771999896673408883824425941022133,
 nat_lit 63040213798447341837388359566421382074154470763076226224838182330151325230520454296848,
 nat_lit 62797076344853936597569649835340698721164476470339528805362992405381187201805851243628,
 nat_lit 62796772506407250334201898087382122168895310483201473666592289204741233386797245215688,
 nat_lit 62796468667960564070834146339417415634554024794324296039784468923265070742551566562084,
 nat_lit 62553333067040614235060361923873102443359351413432546721082933294435072602017018229376,
 nat_lit 62553031081267383375737124115305435769211504040410366957351037467853779199416789578205,
 nat_lit 62552729095494152516414709059016429698084734151979465868871633009795602909502728515898,
 nat_lit 62309593494574202680640924643484376471399675587982075658846514312377592992729340784791,
 nat_lit 62309293361474427225363023526586280278302880461333868513018186624101854514041841594357,
 nat_lit 62308993228374651770084711033554983765950354000156636829777535489809035088070204010322,
 nat_lit 62065859480128157338356263309692501020316347682533219237655985232337734684908439285424,
 nat_lit 62065561199701809680137488969942424930644349171404814970964024857370483576099856920079,
 nat_lit 62065261066602061831845386391444938760427693156614982687765647834338097539816529800557]
private def jp01B2r3_c6 : List ℕ := [
 nat_lit 61822129171029022804161452606979495875078469007179744391107752334396729886183576775884,
 nat_lit 61821832743276130549987603582759659965038327853823984284482189268246675904487430630443,
 nat_lit 61821534462849838105740014943665343637178573710322583252468337635202479485435487529866,
 nat_lit 61578404419950226875115619312474991192437757809197049864039606512330260303038253968105,
 nat_lit 61578107992197362227927568826655765305186411914005353740254918954123752939169016130121,
 nat_lit 61577811564444497580739518340836539417935066018813657616470231698148700487753165121961,
 nat_lit 61334681521544941564085897034168746415568075447480869548497988421776328785238257510665,
 nat_lit 61334386946465504713957384701624610968925137799237748865258711386785471462877599180906,
 nat_lit 61334092371386095470814259531341755243469112815891000842247678426160258585683469871050,
 nat_lit 61090964181159967251220176377949052681710530491506788214820845370772082012223822178091,
 nat_lit 61090669606080585615062438369927476677441418171695283384354302328427573748814577084045,
 nat_lit 61090376883674604168978851352919711392593801436658240249290024141219838918908915951086,
 nat_lit 60847250546121931353429693515063378992539196171785794290249115079136738734542054434128,
 nat_lit 60846957823715977514331493660316893428878492100283994368011736413861374438768901432498,
 nat_lit 60846665101310051282218680967825557604332580989217185682597976732176998481821139543060,
 nat_lit 60603540616430806263729061283250445627049847528087878019894832981666062317921877828470]
private def jp01B2r3_c7 : List ℕ := [
 nat_lit 60603249746698307828675375367900999923673925624774257393121109073920635275277096919769,
 nat_lit 60602958876965809393622100828690884521808542465117405571657384703995115057325293118012,
 nat_lit 60359834392086619589103666844765402324174589814820538287839994604819255684571075781023,
 nat_lit 60359545375027548951109519082691047061407076161177752016696779022113350215284609327362,
 nat_lit 60116422746440289786236237120664361957915369206151149423462502094275538847175313268838,
 nat_lit 60116133725762743912641862652233709744873050472183298538513108476154257542830363713481,
 nat_lit 60115844708703700881633513428559964504802988224371394817823038401578581402699908980525,
 nat_lit 59872722076497938928094511735692146403646474151325540794297801372298143766854652337810,
 nat_lit 59872434912112351247210782313638997350246971151888252305188482755058872689123698482678,
 nat_lit 59872147747726763620247358405501622271880885962226985785200582819934774508359024188763,
 nat_lit 59629026968194457070752870652024714048754346652324955172010176717112028339879055006912,
 nat_lit 59628741656482324793914477921653395440824166861100558021443195556186856430492776602661,
 nat_lit 59628454492096737166951054013516020362549425525133602401526779776961024368183670938507,
 nat_lit 59385335565237885967581598241274202711884176951676129074151985270553478885590757481200,
 nat_lit 59385050253525753744663098845204163693288027335852122758825456714446080199343011863126,
 nat_lit 59384764941813621521744600252603158776808606911730115239682695230570092214855255267772]
private def jp01B2r3_c8 : List ℕ := [
 nat_lit 59141647867628225726420068992428689158443541479136543842500253758410893918687206119714,
 nat_lit 59141364408589548907546495715357912448883043137010787490066185460238965295508751849609,
 nat_lit 59141080949550872088672511062153947392688404882438088734070832587746412993876507170800,
 nat_lit 58897963875365476293348391178118796103212465177383450749928487187763126071274970224471,
 nat_lit 58897680416326799474474817901060291330782994668269888918723149192530306450588686423742,
 nat_lit 58897398809961578059646169939525896755639408658710033312947610906721265546799324927525,
 nat_lit 58654283588449637668366152618748455024937533974947476509341296148408820221595720422797,
 nat_lit 58654001982084416253537504657220190432048755374512706735714659039407829887021236819189,
 nat_lit 58653720375719194838709268071831256140670515516376234755745452132429393356799309190237,
 nat_lit 58410607006880682244488788904335034832740512634993028304519169396438144591467674538949,
 nat_lit 58410325400515488436645939481207380262549185441752929005021001783398144533554129867566,
 nat_lit 58410045646823722425862216835209355849292264197732332400090601646605758922384392393367,
 nat_lit 58166932277985237438627536206107614581896249168107704578853002954606630790650335924735,
 nat_lit 58166654376966899224902940337257610271972780687273729400388830526477153207227930055017,
 nat_lit 58166374623275160821105016229660195881504654702778326225700650450061597123322149015762,
 nat_lit 57923263107110131237914849539955494474393421841341877699926706515002105921962105573436]
private def jp01B2r3_c9 : List ℕ := [
 nat_lit 57922985206091820631176052209499970205095285064599662583878562212525494248759745122213,
 nat_lit 57922707305073510024437254879044445935797148287857447467830417910048882575557384802063,
 nat_lit 57679597641581908238307037718754165270713518566054291202925497681950553653792862834298,
 nat_lit 57679319740563625238553627550559920722693638305180500732091983203451080203451573669348,
 nat_lit 57436210080690553901994822797287826751769177733068534823990876739410511459744097176911,
 nat_lit 57435934028727195856714925537611765671294105382015320644457063188738134196548963732666,
 nat_lit 57435657980382340654021053522692611563791289517118053649464982785263041528714831137829,
 nat_lit 57192550169564194271935762481407735162711053749833896246221460372937236645533070199696,
 nat_lit 57192275973892794473286403602416586813284947010450757745240471999266051414972207401723,
 nat_lit 57191999925547966877578330125898042728570926405078684180490611656167783770802470980199,
 nat_lit 56948892114729848102478425443405423919182465531709853287176441660757805863741167176147,
 nat_lit 56948619771731876100889016897297718441370443552551975734948410453138721057393912121663,
 nat_lit 56948345576060503909225457360170084234777741559934648077553603328604456302606892206251,
 nat_lit 56705239617915812931185090830958673875448217217257479858335777143764985502302855301144,
 nat_lit 56704967274917868536580658070972929790025504433751811250951165827546807161869279889284,
 nat_lit 56704694931919924141977048063265846307623869134840079774850230095086136117096803927793]
private def jp01B2r3_c10 : List ℕ := [
 nat_lit 56461588973775260770922068696309585687409137752595244356707248584486384296648143734366,
 nat_lit 56461318483450771780362561251860211763781745879576052818161312321347271363336525120972,
 nat_lit 56461046140452854992744338406408278020403559690127260634462428727937994325934962967865,
 nat_lit 56217942034981619418748897192733237822960700111625563512657212830551565619252423623847,
 nat_lit 56217671544657130428189801124423194200843846980902011332019931855620831818812293579797,
 nat_lit 56217401054332669044616092218368300317750442961002527891186047269943315536719297577859,
 nat_lit 55974298801534888874665164944090299980592365550689010044562076224203703250364119450353,
 nat_lit 55974030163883855288150994191310496538016025925404920611885871859697064817451579802208,
 nat_lit 55730926058412674982046632816061529793836170078910357420815476371344418441120881377742,
 nat_lit 55730657420761641341612567925517542642063878495651622644895138024652801069110805594429,
 nat_lit 55730390635784035552157523949879629320748871930453902703246699433898424335572516143276,
 nat_lit 55487288382986282989192395214002250979001181201747660400433577717170719736919629692956,
 nat_lit 55487021598008704806723149776758805725598571066226436954962398379378847221390238089099,
 nat_lit 55486754813031126624253904339521502427072359760553910443556179546769840607858984025851,
 nat_lit 55243654412906829465333700919174352292243591113846577783765344835222560803791703703146,
 nat_lit 55243387627929251282864455481937048993717379808171392816327942391251777995445306326490]
private def jp01B2r3_c11 : List ℕ := [
 nat_lit 55243120842951673100395210044699745695191168502498866304921723860874235292770734898507,
 nat_lit 55000022295500831345519931939888965722157720767633823289873359531673855280007776500923,
 nat_lit 54999755510523253163050686502651662423631509461961296778467141302937471661835699944492,
 nat_lit 54999490578219130384626366380950729286900619068133718367834576765678309126125794950044,
 nat_lit 54756392030768288629751088276139949313867171333268675352786212435887637797807732357901,
 nat_lit 54756128951137621255371693469975386338931601851286045042927302496209774243576469977726,
 nat_lit 54513030407305282343082440609921513338870410602576949192138261709964712583072596556272,
 nat_lit 54512767324056112126117020559000043390962584634438371718020027924509788960969545808225,
 nat_lit 54512504244425444751737625752835480415935671298761430487807224225281993367935158122707,
 nat_lit 54269407549648058400907273767030104706814273667443334369716281263072576819198433491013,
 nat_lit 54269144470017391026527878157396507629853318846091886696061334553208074755535372482487,
 nat_lit 54268881390386723652148483351231944654917749365470385874168588373266839462235422521129,
 nat_lit 54025786548282792705363055877493905005383778006565174841329954771733881632464123655836,
 nat_lit 54025525321325580735028175010720251908569348732734173205493536007365562015635459601934,
 nat_lit 54025264094368368764693705520092059095429100162596490996408280060806092139167947224449,
 nat_lit 53782169252264437817908278046354019445986294251421344182907224322305404785647381443828]
private def jp01B2r3_c12 : List ℕ := [
 nat_lit 53781908025307225847574219931871286916520047979012734699556815900319432248794229175399,
 nat_lit 53781648651023441674298877218378854242477668913527988573108315189357533594922274976730,
 nat_lit 53538553808919538334499248283041424615732314409544853777744158812250278181129995088718,
 nat_lit 53538294434635781768209704107943471982223923195818686281323955924306177425995097240258,
 nat_lit 53295201448823809068055227194498709467548694682644434712573468420458973071408325259829,
 nat_lit 53294942070921549659179657774649979843231510538195753460284953131586867436152212091305,
 nat_lit 53294684549311220889949240376700047313056572087656207390330977952895970527919444783390,
 nat_lit 53051591559880772954194536756892869838656010213138721345339660841695644910546928988306,
 nat_lit 53051334038270471791949506521198075074974273302313213906889248439117492954723299684359,
 nat_lit 53051076516660143022719500499387472846309873595430436662527682099666722895073094463355,
 nat_lit 52807985379903122884023923656722173520457709507947844506605118864868663480112559484656,
 nat_lit 52807727858292849328764691959421870770022895721932391279859606881238089399698298433125,
 nat_lit 52807470336682548166520484476005748581983827717780244609947905813807625881153908698586,
 nat_lit 52564381052598983431869421572737489116325101947511121328753836672523543963386990751056,
 nat_lit 52564125383662110066684340866457127067383903449373040209162644392312690681112217840837,
 nat_lit 52563869714725264308484647322438044739629617613409072834714597780180709512038973500475]
private def jp01B2r3_c13 : List ℕ := [
 nat_lit 52320780430641699573833995795309115575572774437768770323534504624907803669170362444721,
 nat_lit 52320524761704853815634302251296163229981952159960495272562567259448749219697291881255,
 nat_lit 52077435477621316687969038689891417907065287284124001362002130160184929632342858721949,
 nat_lit 52077181661357898726828882495678391917802680504767740099599480550659231329087984036372,
 nat_lit 52076927845094508372674114267195679751843715582009850293608842087730588163963534240138,
 nat_lit 51833840413684399042068388055603120749490849465883972886563447537935778791969950329089,
 nat_lit 51833586597421008687913619827120408583531884543123424624541625161413904528372996434040,
 nat_lit 51833332781157618333758851598637696417664263472698716250938717000530033555576669792239,
 nat_lit 51590245349747536610138512549306417136589653872438605053359177965361093047474008549222,
 nat_lit 51589993386157574053043282474098795411147753345657238702927563973214864421754665232094,
 nat_lit 51589741422567639102933028185013123105473570592448657660084333819438206539428061046357,
 nat_lit 51346653991157557379313100511821174126000843586817367232518771071921596695922667349453,
 nat_lit 51346403880241050226262384376010592260843725228224180177550811535664146238829268231493,
 nat_lit 51103318301504396299701584283423437522494253067975772664101794345553794157020638012605,
 nat_lit 51103066337914461349592151943147391717724418609017600968011042643563500199849713001525,
 nat_lit 51102816226997981803526822969598089573845556766292838537975303629862967941727732949934]
private def jp01B2r3_c14 : List ℕ := [
 nat_lit 50859730648261355483951820611936380773913343266103669314402001104132243162567996138278,
 nat_lit 50859480537344848330901515852271259192521571058931207449491598636763831900917217813151,
 nat_lit 50859230426428368784836598254861287350153247959863213845048268764534881395035093525016,
 nat_lit 50616146700365197869306109836596618410505816627859565440625027479089183348180811702673,
 nat_lit 50615898442122146120300319016322406707235363033444507918818452540226349152440791654666,
 nat_lit 50372814719677450440370880056704955285210741377224069599953493339712373866019881541763,
 nat_lit 50372566457815923455764451153928986347991480406116004206289646996355319515033118892029,
 nat_lit 50372318199572899313744458872055384667327134366559777270232241117431445398243780779895,
 nat_lit 50129234473509728398214381829936187984066640605339335669816452771744442024344283963120,
 nat_lit 50128988067940132053253516325198334469878572649715092190793336015056765912530011610730,
 nat_lit 50128739809697107911233524043324732789305570463853176154807414292031157914196309237220,
 nat_lit 49885657936307364792762985154486744556195357085654920204884129924982162314405093367135,
 nat_lit 49885411530737796054787506812004052753652329658853439176142163485006322506303889136857,
 nat_lit 49885165125168227316812439845666821234874648383475341752963732297593930324860290653268,
 nat_lit 49642083251778484198341900956828833001764435006638215290966997608434134998048682204110,
 nat_lit 49641836846208915460366833990491601482986753731260117888070976326904872647809255922505]
private def jp01B2r3_c15 : List ℕ := [
 nat_lit 49398758678166083203905217118205746697387249241007380478902124180792762538378862844612,
 nat_lit 49398512272596514412010256014098201487158808599888022932548046981950944524172227172927,
 nat_lit 49398265867026945674035189047760969968381127325871055017618189460158310434864113310139,
 nat_lit 49155187698984113363654089413850261775096209619941970079145042533072531303721709525302,
 nat_lit 49154943146088000029723947763049400418113849256406162320991491633299877429231500974258,
 nat_lit 49154698593191886695793806112248539061131488892873013018869124647120459156813423892526,
 nat_lit 48911620425149054385412706478337830867846571188302399112330957566178072693326294079402,
 nat_lit 48911375872252941051482564827536969510864210824769249810208590579998654412112123844390,
 nat_lit 48668297707828611583687490438383168290551549606354583067929747042601873104043395700386,
 nat_lit 48668055003987450811216248858361770122392253667149305214355547048490065484300860577310,
 nat_lit 48667810451091337477286107207560908765409893304977285400199343822047275472814095783323,
 nat_lit 48424734135721960570949932889186570733920474918215866295451147235794149867316334089495,
 nat_lit 48424491435499302641064716553922079538733257060563418393086118043393699476498505716884,
 nat_lit 48424248735276644711179500218657588343546217608875217191737405352564125281901777703953,
 nat_lit 48181172419907267804843325900283250312056620816149551385972892869793333610251996287886,
 nat_lit 48180931572358065279002623504409668994899556124882914639309093491241032876807133385483]
private def jp01B2r3_c16 : List ℕ := [
 nat_lit 48180688872135407349117818545290638083477862824618097063766711877010608152120545563273,
 nat_lit 47937614409439485846826569542446540231528779534609635070595767994135168760535717696006,
 nat_lit 47937373561890255714000479984323939157603073144368932827958574930911350191440618246532,
 nat_lit 47694299099194334211709230981485983260530388684209167748570182251798565685163664789762,
 nat_lit 47694058251645131685868939961757850254517078723644962022392658045188921758024714473600,
 nat_lit 47693817404095956767014036104284878960148809291903518726253488331255412291346230726654,
 nat_lit 47450742941400035264723198477592371374128535708751873747037091145792480217769141915516,
 nat_lit 47450503946524260535942034235000010479834686674922686196742927455684936861707529539322,
 nat_lit 47450263098975085617087541753672499469140419540910315646621014568335436074088162315897,
 nat_lit 47207190488952619518841218066364771779078001016441112654295208834476651975122958470648,
 nat_lit 47206951494076872397045440986033690605971064646147168296585149446728687117255840157046,
 nat_lit 46963878884054406298799117298732104870693701097832351317970411062965746688800235769077,
 nat_lit 46963639889178659177004162970679672327986250791408733030192786835672355234448471673972,
 nat_lit 46963400894302912055208797266494051438553316718843861438782393575928614575930427493363,
 nat_lit 46720330136953901361006987518583363608775680362562837721677447380026975694155581410163,
 nat_lit 46720092994751582036271159967672833159859810685974489585786464207577062502588645165810]
private def jp01B2r3_c17 : List ℕ := [
 nat_lit 46719853999875862521461592801875562328888744762067944628118678931089531034409837316722,
 nat_lit 46476783242526851827259783053971004481274571961220354319365129493726609545119473256946,
 nat_lit 46476546100324560109509342665315623771473495245066997420337379688946567583986792450417,
 nat_lit 46233475342975549415307944293550408197991452608597128542496295600533471233352537131249,
 nat_lit 46233238200773257697557915281034345817079323214018458355492325668589923856822122104946,
 nat_lit 46233002911244393776866601669520855228448235706979418962505955585719203912114950162418,
 nat_lit 45989932153895410689650590460010777421459394610223588716168434274009148333044631652210,
 nat_lit 45989696864366574375945075386891766873362294953581998465244198858292216517902686930675,
 nat_lit 45989461574837710455254173151511476604169626485738346474445613430581318524406098216563,
 nat_lit 45746392670162155165097700095282619219861313339031343604091963972534654011502547748340,
 nat_lit 45746157380633318851392185022163608671855557534722934805837868160873001224533922334069,
 nat_lit 45503088475957763561235711965934763260168835810098014028770438670041203855378309760246,
 nat_lit 45502853186428954854515584055077020460728401249965025265142121121615286198016109102199,
 nat_lit 45502619749573546337869607135233100353331053692605191907433435833169283452556063196153,
 nat_lit 45259550844898018654698521241265522690209653212155691164991784303932062128504447615866,
 nat_lit 45259317408042610138052544321421602582812305654795857807283099014895763563889602904828]
private def jp01B2r3_c18 : List ℕ := [
 nat_lit 45016250359659013094527021825486022333180226055117698216976041343901604106473594733181,
 nat_lit 45016016919185129342279995447007144672486995934202651017610030902309236741803280089599,
 nat_lit 45015783482329748432619405689424504286276561041739190320129589688228882936313297420673,
 nat_lit 44772716430327648546508269324871347365365629808831332489263640564736153803616681115907,
 nat_lit 44772482993472295243833066729543856718178465618505434915485181436514274283206665617541,
 nat_lit 44772251409290342131231603749103106453138019935156291724046119944343242494142191812616,
 nat_lit 44529184357288242245120467384549949532226910296284187192163854923742551484934850133898,
 nat_lit 44528952773106316739504802942503679307720452463332493163069337400735819156084266811149,
 nat_lit 44285887573777672311357663278978545636943001763761007300094806766734990067824786849423,
 nat_lit 44285655989595746751822104699161961721077128417401234559929963930691920172589316357650,
 nat_lit 44285424405413821246206440257115691496662014436782721963223177011961410444920682757525,
 nat_lit 44042359206085176764139817831959574435944343115129403218131773912061172623058662112536,
 nat_lit 44042127621903251258524564766052634513039767878165000970703802617557334118010807041179,
 nat_lit 44041896037721353359894287486261514027739446857981479610820634984649267632824858098719,
 nat_lit 43798832691066136674887203214386617389702303487735459273648082980683186037030115785634,
 nat_lit 43798602959557666573316052711737387025571971675305125952122541215830943138542602730278]
private def jp01B2r3_c19 : List ℕ := [
 nat_lit 43555537760229049698235228824975761978101223478461861439018448138529949112437641362089,
 nat_lit 43555308028720579596664489698465849942768495136634162885095119401974601963498289674797,
 nat_lit 43555078297212109495093750571955949880148702067860598389161986778593936313651005143473,
 nat_lit 43312014950556920417072053462336202981317695510382750721200784363085365971821869316405,
 nat_lit 43311787071721878112560441112962063057704428093928940875516676370435748629429860219065,
 nat_lit 43068723728685191877125180624244683415428336468002931685444324022421728622991041148990,
 nat_lit 43068495846231674337012930192368786257957605527189295380008265324261288704091866970050,
 nat_lit 43068266114723204235442602442004346479011814756144803630092389527464636236903326332742,
 nat_lit 42825204620741470561465419271781639440374424921847329973624771714160729531406042183371,
 nat_lit 42824976741906455863939605460801979557386310803521033489340375950056011710327565629008,
 nat_lit 42824748863071441166413791649828449656470494794259235661793167319980422449573067273685,
 nat_lit 42581687369089707492437019855745072919434809148626336094605619199231400366410481841498,
 nat_lit 42581459490254692794911206044777673000773800547131153087554742107935053750873280656607,
 nat_lit 42338397996272959120934846430302660667274038983162710221789476441339087579307719963748,
 nat_lit 42338171970111399827453545755251006542362812394953659505413554259827545409833309877225,
 nat_lit 42337944091276385129928143320422936925303686389448426736060407008395873307717514605423]
private def jp01B2r3_c20 : List ℕ := [
 nat_lit 42094884449968106859995885465730470066206631653265039679175819740053704561416285762292,
 nat_lit 42094658423806547566514996970293310327177480406820241896784217865788675321928510780026,
 nat_lit 41851598786116772139169175736503210724818028306855056162241917281890330288473578844672,
 nat_lit 41851372756336710003102261996309144012816620575615440703596769705663747630054497628549,
 nat_lit 41851146730175150709621373500871984273787469330531772409210945672982770135849911234827,
 nat_lit 41608087088866872439689527022324977698455939150374886211425637744878241230744358269074,
 nat_lit 41607861062705313146208638526887817959426609499326971236305907418740976778779832004632,
 nat_lit 41607636889217209256772675346987028382192779166088251022411327775526713531192355237790,
 nat_lit 41364577247908930986840828868440021806861070579967118123609703648082767837122690199333,
 nat_lit 41364353074420827097404865688539232229627240246728397929997533910751634420739385634475,
 nat_lit 41121295285786004231517945328997629918207581764154211928153331150888943506250991447602,
 nat_lit 41121069259624444938037056030091436077061701327368544837583740045976555310286483140025,
 nat_lit 41120845086136341048601092850190646499827870994129824643971570308645421893903178706239,
 nat_lit 40877787297501518182714171687180010086291483319853639845943600477141616096809594301638,
 nat_lit 40877564976686869697323133822815590670852973898459867753105085034570030939092907240525,
 nat_lit 40634507191670549674022237904561861230288842710339630119336438746021534487059018853333]
private def jp01B2r3_c21 : List ℕ := [
 nat_lit 40634283014563942942000249479904164680082755890944962761464945465144795906461286706012,
 nat_lit 40634060693749294456609211615539745264644246469551190668626430023163506567899331341027,
 nat_lit 40391004757787899387781417229664868990114384447597418976878668735983984680333220948587,
 nat_lit 40390780584299823105331252588164689435669349373881233777759944749088115613089126984179,
 nat_lit 40390558263485174619940214723800270020230839952487461684921429307106821770927544248698,
 nat_lit 40147502327523807158098218876326003768489773190056224967384703864479438904895965276418,
 nat_lit 40147280006709158672707181011961584353051263768662452874546188422498149566334076889226,
 nat_lit 39904224070747791210865185164487330073931788426952168823176748300535476262217865406482,
 nat_lit 39904001749933142725474147300122898685871687584837444104735767349655732520549326825370,
 nat_lit 39903781281791949644128034751288719449973691666160875804208410904508416353660312266531,
 nat_lit 39660725345830582182286038903820583180487432312857383395134180760396899898973674317483,
 nat_lit 39660504877689389100939926354986403944589436394180815114889234221132713554492738938419,
 nat_lit 39417448941728021639097931310987301777219906232579321522281180752904278216717248144828,
 nat_lit 39417228473586828557751817958690218421459988529967369246066389076536253400542395802949,
 nat_lit 39417008005445635476405705409862169167725456168085363821613797627860040451073360831693,
 nat_lit 39173953922157723418608634877924273077779710317499075225172750468313054978419179430998]
private def jp01B2r3_c22 : List ℕ := [
 nat_lit 39173733454016530337262522329096223824136521807950251233068275239834181729727069463519,
 nat_lit 38930679374347121122051477041915234707254376295853091233234667844030141122064442106728,
 nat_lit 38930460755260852995178466025466038619645456953829204194843261639027933253446555181810,
 nat_lit 38930240287119687520818152015032469406536256294677829365122944461560787461715999629947,
 nat_lit 38687186203831775463021081483100703298845317851860814045169798974770311655656597266948,
 nat_lit 38686967588364037785719894249802894224742642846387664877351076368884772818191124439438,
 nat_lit 38686748972896272501432908478116735092360787396925210356031571694585373736534810730775,
 nat_lit 38443694889608388050621636484579449025112492953530933777687809815174688034812277334177,
 nat_lit 38443476274140650373320449251287769933264625355827057886396602661661631948235793539115,
 nat_lit 38200424043526193719568304034880114022950915267616530703597310678222004397926902439861,
 nat_lit 38200205428058456042267116801588434931102869263948408111289787627600986426043533008703,
 nat_lit 38199986812590718364965929568302885821418465221677965608107182013053860199613077298889,
 nat_lit 37956936434649689508272911129037120032365909787589561195036930302606857535824605126227,
 nat_lit 37956717819181979437957111058000590679541491299348624575865365986724979936329010290141,
 nat_lit 37713667441240950581264503994880297146693185731377064102027106007484222265920209853799,
 nat_lit 37713448825773240510948703923843755821338519673387226821957052630895150515120133020914]
private def jp01B2r3_c23 : List ℕ := [
 nat_lit 37713232062978930630707054843833297152171180027093307794615880789140950167539607313532,
 nat_lit 37470179832364501583940708165826251264646086792443727341042492666738735364326586489863,
 nat_lit 37469963069570219310684446248070942334593540106584799550524940110806973746833024916370,
 nat_lit 37226912691629218060976815774535490368844626527733637146465354994523752318937117006621,
 nat_lit 37226695928834935787720553053311147336675350650172710559764035366360584512079286934184,
 nat_lit 37226479166040653514464702511695168708133342706609422106872728494395235801947283036723,
 nat_lit 36983428788099652264757482610830012941778238681074159179623129698144304745866167753150,
 nat_lit 36983213877978797788560347470216594132895681202968419427463203009678075408311963916617,
 nat_lit 36740163500037824199758408869376901797106129502248278433093934863538564530088895879380,
 nat_lit 36739948589916969669641790967126369616119887846624613954677350861666957615984123222112,
 nat_lit 36739731827122715003370916211632340407345597676634110809374428129712338733747286218731,
 nat_lit 36496683301855141550723234464048405063671021601147675258148315268972222228184949495671,
 nat_lit 36496468391734314681511897861823336313250332270339132712572447835954907826741079480066,
 nat_lit 36253418017411843881376501744115697542656279989123880932423048090602832733546568521358,
 nat_lit 36253203103672514169579139897139851801426797728953954078419826286475314542055514609178,
 nat_lit 36252988193551687300367803294920913033169571954939974388675928025893401514779022628262]
private def jp01B2r3_c24 : List ℕ := [
 nat_lit 36009941520957569251764635486727887567616314492210943200796438215463100016319590470962,
 nat_lit 36009726610836742382553298884508948799359088718194305055021356041287951386970967020734,
 nat_lit 36009511700715943120327349444551289752288775609076698025505701855071687299664538276938,
 nat_lit 35766463175448397274665054859222504147728992494025253731346003499726806072522900411351,
 nat_lit 35766250118000998202513256410278655820080174966959849482147515460129088183097694262115,
 nat_lit 35523201592733479963836348987211149936707482922769024549232377378489272684890298946287,
 nat_lit 35522988535286108498669937700528581330245399653274616791562063057832833613086543090300,
 nat_lit 35522775477838709426518139251584733002596582127570342010047329174320069057045770572297,
 nat_lit 35279728805244618984900769981792317559740776072030664363991145208628589291450107335061,
 nat_lit 35279515747797247519733947318970418651768332467565993437394655559430111947029127270690,
 nat_lit 35036469075203157078116578049178003209004048670323743945024927698774491586673017786543,
 nat_lit 35036256017755785612950166762495434602541965402190465655038367534203005848253695561788,
 nat_lit 35036042960308414147784166851952196297590599282317073403694369252937345293764389801929,
 nat_lit 34792996287714323706166797582159780854917480931443758662978465098638746257119848206166,
 nat_lit 34792783230266979847985773457738491969642488732809970266552711051687377417849962139364,
 nat_lit 34549738410346317203427942341221166967395269331544244229742007662404462912454130568817]
private def jp01B2r3_c25 : List ℕ := [
 nat_lit 34549525352898973345246918216793748100047979023845957196861476085075640440407145090558,
 nat_lit 34549314148125029677140045083392399916266602113086882451558857827950752302401014500748,
 nat_lit 34306267475530966842508062975861264194780396425748810903387443591932853375941796990233,
 nat_lit 34306056270757050781386577004708935767950348919991294027082252685316149044219641236647,
 nat_lit 34063011450836388136828745888197752720579349941248888735354030446602978709040059288629,
 nat_lit 34062800246062472075707259917051542303199830717870671189167244663546072338314198289347,
 nat_lit 34062589041288556014585773945905343858533246767546587700970654993663847466680404446033,
 nat_lit 33819544221367920977013329991649298577564105476185039608358265229018654395181464849119,
 nat_lit 33819333016594032522877231182758249872012314486295947356985294542727417862373061855853,
 nat_lit 33576288196673397485304787228502216563664764615655351910257780192863809025185011894779,
 nat_lit 33576078844572909221242428034497896267546578452363503834816350579907489426286455327113,
 nat_lit 33575867639799020767106740601746177863413982353797998956365649129391396533042094049559,
 nat_lit 33332824672551813526593423424632022703706174122522820354781025440729915569771163977894,
 nat_lit 33332613467777925072457735991880304299573578023957315476330323990213822667730709547060,
 nat_lit 33089570500530717831944830190905491413997899955698728837974411796648663900993094846403,
 nat_lit 33089361148430257174867858159156320856994506754203001467040355323368290477903923152722]
private def jp01B2r3_c26 : List ℕ := [
 nat_lit 33089149943656368720732170726404602452953254507970678041259793778548635697335376053984,
 nat_lit 32846106976409189087204652087684927333688090276120896617033328007208519023725382764143,
 nat_lit 32845897624308728430128091432075099050816827237641761229610392632676133717517217465854,
 nat_lit 32602854657061548796600572793355435904264598278846113863374122974510698534203198178701,
 nat_lit 32602645304961088139524012137745595648771743819646025850348721788848408433626809402652,
 nat_lit 32602437805534055279506578259271527504998350285819826545562541347682139455152934651051,
 nat_lit 32359394838286875645979059620557982367987993461736659941832407417352720330417465230394,
 nat_lit 32359185486186414988902910341087484386627269165553163912318127330438418346722015740874,
 nat_lit 32116144371612690759419905641758731118196358820873391900838255141038818562170228999001,
 nat_lit 32115935019512230102343756362294351146377506659402376633830110781960532637053329375976,
 nat_lit 32115727520085224849311709646075432741627562235039116601163572876193987242003117146744,
 nat_lit 31872684552838072822769989545756367645151193261353399159777982915028867577481538339336,
 nat_lit 31872477053411039962752967043427759785051802026617402048410403550648439787446296019351,
 nat_lit 31629435938837315733269962344105136498784355237371063445321542201634985383330494972199,
 nat_lit 31629228439410310480238327004025536422923358134582490144961194074588055396887466115255,
 nat_lit 31629020939983305227206691663952078301847416007948302858311912995405518680896303300679]
private def jp01B2r3_c27 : List ℕ := [
 nat_lit 31385979825409580997724098340768773344468916540276650967246831821460013765040061841367,
 nat_lit 31385772325982575744692463000695315223392974413642463680597550742277477049048966004583,
 nat_lit 31142731211408851515209869677518152220799529922125197803243536616196360900045097303799,
 nat_lit 31142523711981846262178645713584012428612535117065697228618035409850323272255894748807,
 nat_lit 31142318065228296413191524312901464185566567750853074416936077549418476660576313441815,
 nat_lit 30899276950654572183708930989718159228279412136875733425942480531371237863175640612263,
 nat_lit 30899071303901022334722220965181071268907447068392183319712959685757153778945780251960,
 nat_lit 30656030189327298105239627641997766311620469860379089050018088772932457098113831566536,
 nat_lit 30655824542573748256252917617460678352248326385931292242772252030210411128577085701209,
 nat_lit 30655617043146743003221693653532680514937730410720488602211711631278694306443381472234,
 nat_lit 30412577781246474177783614269740285435680549557164712086185437831982150116953917389690,
 nat_lit 30412372134492924328796904245203197476308584488681162000238326892251191360328602123019,
 nat_lit 30169332872592655503359236237556262680725584338818704890680806609343276887310637628060,
 nat_lit 30169127225839105654372526213019174721444784718065219003788863323939712556519418001965,
 nat_lit 30168921579085555805385816188482086762164163503275979817913236540107019918349671365054,
 nat_lit 29925882317185286979948148180835151966580984947449276027621809661511359080314778843471]
private def jp01B2r3_c28 : List ℕ := [
 nat_lit 29925676670431737130961438156298064007300363732660036862028592783561791769749577169120,
 nat_lit 29682637408531468305523770148657259193971992585963735815948435211192107608731119155313,
 nat_lit 29682433614451373860581985439650411414231884873889041966352783510600152540162047637506,
 nat_lit 29439394356169607877730342676760383591620962804218285340320680175550096866341717047188,
 nat_lit 29439188705797582793143405945866998682156880362798292440710359512200299015168683308837,
 nat_lit 29438984911717460741215822698465670861882784800328807905083757359688950503609010910902,
 nat_lit 29195947502490647319823080006355106228094927156349710671597168690036369345467598927432,
 nat_lit 29195741855737097470836369981818018268814305941557813029690357992610441105225787930074,
 nat_lit 28952704450128786892029652534464360607998704783732004504431908952910229509226672190827,
 nat_lit 28952500652430189604501842580706735837541147994631766255070612920881775784663779800317,
 nat_lit 28952296858350095159560057871706018040055847691687475169968640432398927224315382232207,
 nat_lit 28709259449123281738167315179595453406267990047705719480490481931000538452053409559585,
 nat_lit 28709053802369731889180605155058365446987368832916480294575241065320417825932092142514,
 nat_lit 28466018245816373925752681916254484666445591466520932849289178392505541400250119123780,
 nat_lit 28465814451736279426891003069483453177509531797835381620729150288941596583191500190423,
 nat_lit 28465610657656184981949218360482735380024231494891090535627177800458748022843102622313]
private def jp01B2r3_c29 : List ℕ := [
 nat_lit 28222573248429371560556475668372170746236373850909334846109405217803227081784357974523,
 nat_lit 28222369454349277115614690959371452948751073547965043761007432728730082702281161601421,
 nat_lit 27979333897795919098266874386266292578875266007530234968447081513065516218049261760799,
 nat_lit 27979130103715824653325088873796540679273236512883945087161341952351261459540569649330,
 nat_lit 27978928162309185612428229480332193043583257120423472614866859999481628716082208862276,
 nat_lit 27735890753082372191035486788221628409795399477802846413315251175972440225596070850519,
 nat_lit 27735688811675733150138627394757280774105420086703503428986932680607976327015941042025,
 nat_lit 27492653255122375132790398642037637990969128623864264819756539523591097561129926553340,
 nat_lit 27492449461042280687849025309182368504627583051622404755140842206460614491532337245839,
 nat_lit 27492247519635641646952165915718020868937603660523061770812524013327610009005221637665,
 nat_lit 27249211963082283629604348539143826396945066928386254182068405423200177919356106337716,
 nat_lit 27249010021675644588707489145679478761255087537286911177457677626415503012881806421319,
 nat_lit 27005974465122286571359671769105284289262729211114350289729875537858947119453791349978,
 nat_lit 27005772523715647530462812375640936653572571414050760604385241145386525847962563538029,
 nat_lit 27005570582309008489565952982176589017882592022951417640339332555905191789382766324736,
 nat_lit 26762535025755650472218135605602394545890055290814610051595214570240674010647865617299]
private def jp01B2r3_c30 : List ℕ := [
 nat_lit 26762334937022439228380402989273807049206601552035021717515921008429018158330585836326,
 nat_lit 26519299380469108818018384151100222599911516225731755114973722236373385079561989679802,
 nat_lit 26519097439062469777121524757635874964312880688324064594968113889197081537365629626957,
 nat_lit 26276063738801070006404246565209497343322575202764768625168232759945738203151887657440,
 nat_lit 26275861793775928122921773303133703018425685476932862102386922099866278026320484526452,
 nat_lit 26275661705042744486069427849060265260765680846255083593025927125483968151704577796359,
 nat_lit 26032626148489386468722021848631531072538490265541659630127753996034572927174161492123,
 nat_lit 26032426059756202831870087770703553598552487932592953846461991860505718416061322651694,
 nat_lit 25789392355876300272486678471290582696132029180313281776214736864571257620403420817346,
 nat_lit 25789190414469661177670336316201381652756636574896062294517103434376521871366248752982,
 nat_lit 25788990325736477540818402238273404178861978094280537922996276079088192612986225190634,
 nat_lit 25545956621856574927515510177235579868664762273988678435025812087132359827570178680445,
 nat_lit 25545756533123391290663576099307602394678759942401102119083417886714135914981184661009,
 nat_lit 25302722829243488677360684841738812186598273313811241427296720966399418012170328368549,
 nat_lit 25302522740510305040508749960341800610586885642854847747558289996384846905704639915321,
 nat_lit 25302322651777121403656815882413823136783571015933634296391356400646454189727436268749]
private def jp01B2r3_c31 : List ℕ := [
 nat_lit 25059290800570646587413050598511758965592880849322658926353670893275168150289831191650,
 nat_lit 25059090711837490557546503682838931230721671478170073867517305280689898810832185091062,
 nat_lit 24816057007957587944244022997940449194656585820894806342775553085471547315248041976714,
 nat_lit 24815856919224404307392088920018589730395143328686073654114754915337720248995628737310,
 nat_lit 24815658683164676074584668781481522134530459611214372692928758184275623050724038697651,
 nat_lit 24572624979284773461282188096589158108007246088651585950975551018313503125212309905991,
 nat_lit 24572426743225045228474767958052090512233906223513066422177284589296178119268843020763,
 nat_lit 24329393039345142615172287273159726485710692700952938136255261336927293795829245698416,
 nat_lit 24329194803285414382364867134622658889937352835811760151425810994316733187813647343877,
 nat_lit 24086162955697442408707538471622961975484265304057856656368682305266334745454610768025,
 nat_lit 24085962863345783536255377687338687551314801745839526626691594225921296935417568190510,
 nat_lit 24085764627286055303448368924940950257052000622996646455801983084522050748387189743555,
 nat_lit 23842732776079608094189990803300165807139566972254095710736132181555115390676175839063,
 nat_lit 23842534540019879861382982040908558495040229403483519460231754643420872646113114742508,
 nat_lit 23599502688813405099059522270922268299065644752676058412057112181990923133233932820097,
 nat_lit 23599304452753676812332619370760347295515547819525351485818046662245051142382372937238]
private def jp01B2r3_c32 : List ℕ := [
 nat_lit 23599106216693948579525610608368739983416210252115904703037037059811734815498022575531,
 nat_lit 23356074365487528977253031025122435574037764451770803120276116044161670947641514679616,
 nat_lit 23355876129427800744446022262730828261938426885722485805178860295581853041688144010453,
 nat_lit 23112844278221353535188466893368716387668662140292166381210762093481890720268123397226,
 nat_lit 23112646042161625302381458130983227085111196707595200381218297520304805963456187358207,
 nat_lit 23112449658775324866633576145727379912018384792505508248686312851424288666839204912021,
 nat_lit 22869417807568905264360996562481075502731282845854717565996875991672495412241799994154,
 nat_lit 22869219571509177031554399176234928474305947576174343529233122913591732860759339457215,
 nat_lit 22626189572976185226340946370124384204025371280484836485140141047132471305174733576789,
 nat_lit 22625991336916456993534348983872107193436572456729500051637947068925830704510856223210,
 nat_lit 22382961342001968030906921422524599878291716202626715124164115672805084091504599390592,
 nat_lit 22382764954997164752573425568657306015900650100471278041073817536353563435744418617621,
 nat_lit 22382566718937464126751803968520848442916105493496822495116427219742690351342752913579,
 nat_lit 22139536720404444714553375376300614717194738536459867971909266613921234647883491858496,
 nat_lit 22139340337018171885791291929445377566890721880895369289862297224990334410868919785430,
 nat_lit 21896308485811752337439017860108717150564918042281478088257162268748960118861855086444]
private def jp01B2r3_c33 : List ℕ := [
 nat_lit 21896112102425479454756628899343836007299603277318950457481751506533020877539106903810,
 nat_lit 21895915719039206625994545452488598856995586621754451775474396199449548628476105610904,
 nat_lit 21652885720506214820781504022523514870389012625152488489051240495371653284686757910061,
 nat_lit 21652689337119941992019420575668277720084995969587989807043885188288181026827663463875,
 nat_lit 21409659338586950186806379145703205706100013393706979146223195597571654388263087658329,
 nat_lit 21409462955200677358044295698847956583174405317421527838613374479358268328836514993391,
 nat_lit 21409266571814404529282212251992719432870388661857029156606019474506250983430807377029,
 nat_lit 21166236573281412724069582198166965747774353407550705207809109756626218929468497351708,
 nat_lit 21166042042568567692366625528447488736476862405667090643734532934717589236742643143602,
 nat_lit 20923012044035575887153584098488534732033751964501219201451162683198863849974989214536,
 nat_lit 20922815660649330665376887813888447320844528269369053320518652049764814761612565828318,
 nat_lit 20679785665734841702750283004819600608720749501218676535981066177661842775522044301940,
 nat_lit 20679591131403493828461301090349346606614465568612548195755767048942087378670057050635,
 nat_lit 20679394748017248606684604805749259195425241873483040770854440329101273892379765133729,
 nat_lit 20436366602157684598531101529065395631499195828291034328098910635952310074055429083448,
 nat_lit 20436170218771439376754405244465308220309972133161526903197583915521205272209965732046]
private def jp01B2r3_c34 : List ℕ := [
 nat_lit 20193142072911875368600902771250478758500655279671519256625821294013360840090447269989,
 nat_lit 20192945689525630146824617059320687546705241135135652373166973488138999950663297159163,
 nat_lit 20192751158812812722107047551862490256594662796787281021919296188162740792069951213458,
 nat_lit 19949723012953248713953544275178626692759960603928456011551496796468248843319379382057,
 nat_lit 19949528482240431289236386143853629722087801303414342574525440694146647285861919772351,
 nat_lit 19706498483707467091008731876149825456759662230006180102016985169470260278486028799574,
 nat_lit 19706303952994649666291573744830958468159444227989201387379237656352447629551701478893,
 nat_lit 19463275810753616107709482875159151616320447629388133345706650489749781495112519536004,
 nat_lit 19463081276422268233420912336828227915816046291410825795777737252924327509559477292314,
 nat_lit 19462886745709450808703754205509360927307350547691275214544036241190699338317825068209,
 nat_lit 19219858599849914407535638091074517120332633907500826640825547979807055998673863330888,
 nat_lit 19219664069137096982818479959761780113987401719214709447660834122960474795969374735327,
 nat_lit 18976635923277560581650364648802100391292877826159693058195100088695289126622565649270,
 nat_lit 18976441392564770763918592876269349039690901998839953485213520686276470903717819599629,
 nat_lit 18976246861851953339201434744950482051182206255120402903979819674542842732476167375525,
 nat_lit 18733218715992416938033318630521768226462297022696569171000458473742688986440836860476]
private def jp01B2r3_c35 : List ℕ := [
 nat_lit 18733026037953027310375698652477991678470665673592412577642027777296813327979002874323,
 nat_lit 18489997892093490909207582538049277853659590996160773560692597026224587079220817709418,
 nat_lit 18489803361380701091475811568991690586337629510012219470987069733432237725600615778561,
 nat_lit 18489610683341311463818191590947914038437342013241244330298778942682804692210249386137,
 nat_lit 18246582537481802669635462638780479934813001593380601804877521910551857261073514514480,
 nat_lit 18246388006768985244918304507461612946304305849661051223643820898818229089831862290375,
 nat_lit 18003361713582876640809726546307989562101461011852611478579344095153255844527920793439,
 nat_lit 18003167182870086823077955577250402294779677933029433557534273075937848625304761026294,
 nat_lit 17760140889683978272889271753867092602027592460962253955888238107738003056016458270350,
 nat_lit 17759948211644616198297144800314282083863458263346391331970135474041658795029318223397,
 nat_lit 17759753680931826380565373831256694816541675184523213410964678536673684067357356606909,
 nat_lit 17516727387745717776456795870103071432338830346714773665860587651161282842897937483093,
 nat_lit 17516534709706355755784151678181244304023572920211350395104155345114647729440329581804,
 nat_lit 17273506563846846961601834102153140502001293500943775360995600101985968098508985615492,
 nat_lit 17273313885807484940929601286364513693124276706310363323726881793443338926251335107612,
 nat_lit 17273121207768095313271981308326867127387452766333951038830946395513334182734136755124]
private def jp01B2r3_c36 : List ℕ := [
 nat_lit 17030094914582014316148790509434523464371520593421883953955099584366577385849060344651,
 nat_lit 17029902236542652295476557693652026637566801909214100020824912962286355179753010119395,
 nat_lit 16786874090683143501293828741484592534033805341686638948113409917699278352843220468347,
 nat_lit 16786681412643781480621595925702095707320430509812036467613749119468066271471346532883,
 nat_lit 16543655119457700537418299264580065735755257702641229526195958225633869642153107014059,
 nat_lit 16543462441418338462826172311027255217591123505025366902277855591937529884765594337603,
 nat_lit 16543271616052404239213066272380518529884274325470519072066833506875089917955365421275,
 nat_lit 16300245322866323242090286849627505168378880894854091324817232379694746028431846686835,
 nat_lit 16300052644826961221418054033845008341756849915312670276744915965355729614943946162187,
 nat_lit 16057026351640880224294863234952664678741096148364849913167794957200064534569927720867,
 nat_lit 16056833673601545810608017581425317591050992018627810536127320723023088805881967820603,
 nat_lit 16056640995562183789935784765648950746501080742186641443775875243373779668950399074004,
 nat_lit 15813616555049530589871720743892367222491674222955458476832807219633324835659390795372,
 nat_lit 15813423877010168569199899304249200697380181985709676766386736489260716825933487685124,
 nat_lit 15570397583824115179062095667612006773387698920899419506268802045159288098243383279004,
 nat_lit 15570206758458180955448989628971400067844313298139134531810521271068848433354684513589]
private def jp01B2r3_c37 : List ℕ := [
 nat_lit 15327180465272099958326211009687420808546992911557887013132417518164682925523624541389,
 nat_lit 15326987787232765544639364552697169600903801551516528949315503251481858664475840625766,
 nat_lit 15326796961866831321026669890189763214798834967951631356802211308515548114744378276862,
 nat_lit 15083770668680777930888866253558699272969815458574807484753264019301166364387530652566,
 nat_lit 15083579843314843707276171591051292886864848875009909892239972076334855805859975150383,
 nat_lit 14840553550128790317138367954420228945036007771597332721207340986459890835671213685447,
 nat_lit 14840362724762856093525673291912822558930862782068188427677732844154163496975572023904,
 nat_lit 14597338287868733343033021677174425729080625412528195837820887583660229458374273153529,
 nat_lit 14597145606210896086760562155029501970020325797228276787833791897171362262135315380625,
 nat_lit 14596954780844961863147867492528225566078822769096812583429101190939531172492147702058,
 nat_lit 14353930340332336270069190633032921763256328913400872829312932387490287788831219923139,
 nat_lit 14353737662293001856382756355651034959331749339690334331693761480691209397740319946843,
 nat_lit 14110713221780376263304491675757965578064403714891780735384325196739562000000595933172,
 nat_lit 14110522396414442039691796209787655072006171495058317755078277021927990632544690517901,
 nat_lit 14110331571048535423064488709541528406996773722695481943004153996617828024559946970918,
 nat_lit 13867307130535909829985811850046224604265623719332723621275715796854511414130009978558]
private def jp01B2r3_c38 : List ℕ := [
 nat_lit 13867116305170003213358504349800097939347569797941939773905569521967072968803982915159,
 nat_lit 13624090011983949823221112089308364299120432884557724595585536288442051725202312803824,
 nat_lit 13623899186618043206593804589062237634202378964525411759867959953814876107531227248009,
 nat_lit 13380874749723920456101564350457041123790560634180806551916489744829098099792887690530,
 nat_lit 13380683920739510996888231605454007485900250227995205007970773780249552919979438781627,
 nat_lit 13380493095373604380260924105214010803145659863398984016392982595950087860869219103828,
 nat_lit 13137468654860978787182658621858037301925048602331865032290790080743475464559917937645,
 nat_lit 13137279682168499967614477898747670776013520334621965302853422290440583756416239285126,
 nat_lit 12894255241655874374536212415391709247414500494275798944353695585773589351315710685983,
 nat_lit 12894064416289967757909316291284900911385393897181960744374836891429646853645722596024,
 nat_lit 12893873590924061141282008791038774246467339977152306364688444470395706838046768509521,
 nat_lit 12650849150411463155189130469937950484361521676520178617409871240421241865065353196011,
 nat_lit 12650658325045556538561822969691823819443467756490524237723478819387301849466399109508,
 nat_lit 12407635737206358742542684263477740439392845703176593312300935857145311128999996961053,
 nat_lit 12407444911840452125915788139370944075985330526803707737884928892083854453742009462966,
 nat_lit 12164420471327854193742803956040434005330271591912840134064411579421945144727803670608]
private def jp01B2r3_c39 : List ℕ := [
 nat_lit 12164231498635375320254729095165883770131447513895113669559998712782938972207767105513,
 nat_lit 12164040673269468703627832971059087406723932337522228095183605829568910284901350387586,
 nat_lit 11921016232756870717534954649958263644618114036890100347905032599594445320716028227356,
 nat_lit 11920827260064391897966773926854027100870049324613634026858675650267994803367108030133,
 nat_lit 11677802819551766304888919819637383901160155213167530549082798871630414705159724740174,
 nat_lit 11677613846859315092306126258782167114363241499928375355452734168400845269689350237672,
 nat_lit 11434589409965192341814297396328560869788889024107405749310875574355598927168335261057,
 nat_lit 11434398580980810489586351813580676971013371578356795442188778895598496989837571009819,
 nat_lit 11434209608288331670018582466615770728775845609737097926452421484091957809577281334452,
 nat_lit 11191187020449161480984830922650707105676552961424724829422872886029132782360739064910,
 nat_lit 11190996195083254864357934798550040724432501340485272663437490842610953656335576345575,
 nat_lit 10947973607244084675324184058060141185613401439308331770982720156575388892160209988481,
 nat_lit 10947782781878205665682674292739460459203950031668438637246179184720937841919262337818,
 nat_lit 10947593809185726846114904945774554216966424061687611653826068221592350631989566122676,
 nat_lit 10704571221346556657081153401809490593867131414736368024480273476792732718944925395534,
 nat_lit 10704380395980677647439644439963973951646528901898725662930780115511070062171456547303]
private def jp01B2r3_c40 : List ℕ := [
 nat_lit 10461357808141479851420917109889220873197789443216273963513783273257517943177241700737,
 nat_lit 10461168835449028638838123549040134068564517692733269870661205946362107584414349666587,
 nat_lit 10218144394936430706665550741848954299419997501499171092433097472940325123982705961140,
 nat_lit 10217955422243951833177887257113734365731712167138213433238684446352685183412500441166,
 nat_lit 10217766449551500620595505072403977862608979157592377686642192466815086312308195207144,
 nat_lit 9974743861712330431561753528445044221673150066074567465687408562401613788495633196930,
 nat_lit 9974554889019879218979371343729157736386953502456427778383659596331372461485949331227,
 nat_lit 9731530448507281232886904398773794257955315906878748945822412641670926082540009825973,
 nat_lit 9731341475814830020304522214064037754741060640396614533505628014602645667069729711695,
 nat_lit 9488318891594135066871820128746191649264577669228581010000524656154961539944951064041,
 nat_lit 9488129915283181011703412699279528173169588174887927566828462986925260437952851223939,
 nat_lit 9487940942590729799121030514569771670046855165342091820231971007387666070448173360413,
 nat_lit 9244918354751559610087690346750168330621564816119920936943046868788029920756926129335,
 nat_lit 9244729382059108397505308162040411827498831807935214657990694661256505995027750331473,
 nat_lit 9001706794219938208471557421550512288679731908119403233219677829074444164179151299563,
 nat_lit 9001517821527486995889174433371721683440269708232698158123172631158937524641557259141]
private def jp01B2r3_c41 : List ℕ := [
 nat_lit 9001328848835035783307203624801295481828075442343631216836680189441249981829789393695,
 nat_lit 8758306260995865594273863456981692142402785093121460333508141968994185844187038622393,
 nat_lit 8758117288303414381691481272271935639280052084936754054595403843310089906409433473619,
 nat_lit 8515094700464244192658141104452332299854761735717241627298049536456261370838881149421,
 nat_lit 8514905727771820587061146081997725535755477836992816164473770032578648910813112705415,
 nat_lit 8271883139932650451947700051948435887780946853511905424603287729444140437137571324193,
 nat_lit 8271694167240199185445423729468365693298798331919120434620223988492261027720879939771,
 nat_lit 8271507047221175769922168321894369329182590976054168805956510494129509216553349161045,
 nat_lit 8028484459382005580888828154080895971920764182265431310736573812648374947852719497199,
 nat_lit 8028295486689554368306445969371139468798031174080725052106245290615949425226272612234,
 nat_lit 7785272898850384179273517177690866430883457973118440207420268953474710471513538174756,
 nat_lit 7785083926157960573676522155236259666783995668432426499610857163850916824595788996286,
 nat_lit 7542063194610721024288334009309323439428831310019138863178397420315574170105730309720,
 nat_lit 7541874218299766969119926579848789945497305371111918808114937290051802928259658554866,
 nat_lit 7541685245607315756537955771278363743885111105222851887110854451985785809395141975437,
 nat_lit 7298662657768173174490002765713910143483269865463620275901958767528736570731225029927]
private def jp01B2r3_c42 : List ℕ := [
 nat_lit 7298475537749149758966747358139913779458406361931850079625975574620461132737018600641,
 nat_lit 7055452949909979569933407993795474524313308759845111380589805965370737557000284806235,
 nat_lit 7055263977217555964336823544011163959607834411716984935521598590473028816199814355958,
 nat_lit 7055076857198532548813568136437167595582970908185214739245615398155049197360406731664,
 nat_lit 6812054269359362359780227968623694238321144114396477244025678716673914919863684045610,
 nat_lit 6811865296666938754183644322308417775732398957970349595141238414007616880823202486981,
 nat_lit 6568844561501196362209430931624574575404978113403773250480639040519904664190780447327,
 nat_lit 6568655588808745149627460123060278355956247402945481261553973827826581803400160483834,
 nat_lit 6325634853643030418558528032401898586011691181247264444052158691413136536158728493460,
 nat_lit 6325445880950579152056251709927958373693006215087912842177696489427186986888065194286,
 nat_lit 6325256908258155546459668063612681911104261058661785193293256186760888947847516657865,
 nat_lit 6082236173092413154485454672934968692940303769525983780710074136414416094427857819747,
 nat_lit 6082047200399989548888871026619692230351558611738726664141880282126074520521436960766,
 nat_lit 5839026465234247156914657635935849030024316174494868032150167048238041920508202719128,
 nat_lit 5838837492541795944332686827371552810575407058074987798238369549798537872825534912307,
 nat_lit 5595816760994584001929885843699766322243691809124639433925552341662914298159511377613]
private def jp01B2r3_c43 : List ℕ := [
 nat_lit 5595627784683629946761889790378563129822704612513058736770747499017221875226528061032,
 nat_lit 5595440664664634138224021545059716504821290218444227812614406842098961336211155588610,
 nat_lit 5352418076825491556176479915640723188093451275052939479739014130372422346879215211933,
 nat_lit 5352230956806468140653224508066726824068587772882298751146784791317645338612148737335,
 nat_lit 5109208368967325558605682878647745479962340250211963043873857890130724340488980927698,
 nat_lit 5109021248948302143082427471079867125479348882753803077787763977270804297501876294764,
 nat_lit 5108834128929306334544970601900350801897129378647430079152348608157305288728695673863,
 nat_lit 4865811541090136145512041810226207746237185179487513353946387912687351598526000272289,
 nat_lit 4865624421071140336974173564907361121235770785418682450072456859420756979858251715388,
 nat_lit 4622601833231970147941244773233218065484482733925584312800789547405134012825815487190,
 nat_lit 4622414713212974339403376527920501422646531895290186776713436045373920442347606643313,
 nat_lit 4379393978047259554414962479100172364878484241848347969845987653728863935469269160460,
 nat_lit 4379205005354808341832990867066842043404368192023897052872059980790467743371730620838,
 nat_lit 4379017885335812533295122621747995418402953797955066148998128927523873124703982063937,
 nat_lit 4135995297496669951247580992329002101675114854563777816122736215207042819816870383836,
 nat_lit 4135808177477646535724736960900466021324253650122209813265354099674899885816467820662]
private def jp01B2r3_c44 : List ℕ := [
 nat_lit 3892787442311931750735910732471772560020281915018572761006806865238572669355704848401,
 nat_lit 3892598469619508145139327086162626079595000312662090576516030334091474962261607452588,
 nat_lit 3649577734453765807085419209394556854392341132924318112700904041108919492363268656966,
 nat_lit 3649390614434769944627656826305396537940167373114227065368917070529769209728310578913,
 nat_lit 3649201641742346339031073179996250057514885772121532804593078306829405534433417498236,
 nat_lit 3406180906576603947057271165457867140861467225281370729636142242680795979636889488918,
 nat_lit 3405993786557608138519402920145150498023516386645973213870812426148680812261409557937,
 nat_lit 3162973051391893353530988067855787338138917947466382311835913161611630392587262365004,
 nat_lit 3162784078699469747934404421546640857804801791481493314747734646763119187329680018662,
 nat_lit 2919763347152230198546216275625834612613100989862768534107630296047204822712789372033,
 nat_lit 2919576223514731547422734161689411316149968851933629803600621383201413434796383144988,
 nat_lit 2919389103495735738885277292516024974731212903260690193073807250822393886111564303287,
 nat_lit 2676366515656593156837735663097031658094717812202583292586144841140627089107814189905,
 nat_lit 2676179395637569741314480255529165276233317865465375952102517041051779940986775800556,
 nat_lit 2433158660471854956326065403239814089061476293375672407041497388118539327783289883271,
 nat_lit 2432971540452859147788608534066415775021128923981780170912217444609605968734899669538]
private def jp01B2r3_c45 : List ℕ := [
 nat_lit 2432782567760435542192024887757269294687191173961137874840355129100511552441496635836,
 nat_lit 2189761832594693150218222873218886378033772628482105267567172918805400418575948319063,
 nat_lit 2189574712575697341680354627906169735195821789846707751801843102273285259996561541362,
 nat_lit 1946553977409982556691939775616806575402388797036051581177972022289013728038368708749,
 nat_lit 1946366857390986748154482906443420233983632848363111970611543808062566191401979086888,
 nat_lit 1703344269551844166106942080493461019463866949007003866307648470021914277003419191234,
 nat_lit 1703157149532820750584097245595890836996276552863437067266499282258360641243027736413,
 nat_lit 1702970029513824942046229000283174194158325714228039551501169465726245482663640958712,
 nat_lit 1459949294348110157057814147993811034364892721417383380837684303894545962753877477011,
 nat_lit 1459762174329114348520357278820424692946136772744443770310870171515526414069058504238,
 nat_lit 1216739586489971766472815649401431376309641681688995325854391674836699399982641055176,
 nat_lit 1216552466470948350949971617972895295958780477244768866965825645711320863910107153763,
 nat_lit 973531731305233619881039527320645508269031663313166890242751651728793169432784012542,
 nat_lit 973344611286237757423688520370815493327396645798715180537010667347506185420956763289,
 nat_lit 973157491267241948886231651197429151908640697125775570010196534968486636736137921588,
 nat_lit 730134903428099366838690021778435835272145606067668669522534124696424029373682156494]
private def jp01B2r3_c46 : List ℕ := [
 nat_lit 729947783409075951315845990349899754921284401626100666665152009164281086577186571113,
 nat_lit 486927048243361166327019761927336275780954627917485247500338297208614517096833221380,
 nat_lit 486739928224365357789562892753949934453364125613480368344938267534941364576770589343,
 nat_lit 243719196677153415387173285221493747632187618958771361940776649248851512481129169466,
 nat_lit 243532073039654764263691171291200433241175184129884587154638973324226799581815505365,
 nat_lit 243343100347231158667107524982053952907237434109242291082776657815132383288412471663,
 nat_lit 322365181488766693305510443671036253818888630209683809594448110317068577662959882,
 nat_lit 135245162492958155437265130954393415868049994812168044264630987906090843477377189,
 nat_lit 822094695498963857422212266693561573869053018176]
private def jp01B2r3Get (q : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat (q / 16) fun c =>
  PipeFuseCert.withForcedNat (q % 16) fun rem =>
    let L :=
      cond (Nat.blt c 23) (
        cond (Nat.blt c 11) (
          cond (Nat.blt c 5) (
            cond (Nat.blt c 2) (
              cond (Nat.blt c 1) jp01B2r3_c0 jp01B2r3_c1
            ) (
              cond (Nat.blt c 3) (
                jp01B2r3_c2
              ) (
                cond (Nat.blt c 4) jp01B2r3_c3 jp01B2r3_c4
              )
            )
          ) (
            cond (Nat.blt c 8) (
              cond (Nat.blt c 6) (
                jp01B2r3_c5
              ) (
                cond (Nat.blt c 7) jp01B2r3_c6 jp01B2r3_c7
              )
            ) (
              cond (Nat.blt c 9) (
                jp01B2r3_c8
              ) (
                cond (Nat.blt c 10) jp01B2r3_c9 jp01B2r3_c10
              )
            )
          )
        ) (
          cond (Nat.blt c 17) (
            cond (Nat.blt c 14) (
              cond (Nat.blt c 12) (
                jp01B2r3_c11
              ) (
                cond (Nat.blt c 13) jp01B2r3_c12 jp01B2r3_c13
              )
            ) (
              cond (Nat.blt c 15) (
                jp01B2r3_c14
              ) (
                cond (Nat.blt c 16) jp01B2r3_c15 jp01B2r3_c16
              )
            )
          ) (
            cond (Nat.blt c 20) (
              cond (Nat.blt c 18) (
                jp01B2r3_c17
              ) (
                cond (Nat.blt c 19) jp01B2r3_c18 jp01B2r3_c19
              )
            ) (
              cond (Nat.blt c 21) (
                jp01B2r3_c20
              ) (
                cond (Nat.blt c 22) jp01B2r3_c21 jp01B2r3_c22
              )
            )
          )
        )
      ) (
        cond (Nat.blt c 35) (
          cond (Nat.blt c 29) (
            cond (Nat.blt c 26) (
              cond (Nat.blt c 24) (
                jp01B2r3_c23
              ) (
                cond (Nat.blt c 25) jp01B2r3_c24 jp01B2r3_c25
              )
            ) (
              cond (Nat.blt c 27) (
                jp01B2r3_c26
              ) (
                cond (Nat.blt c 28) jp01B2r3_c27 jp01B2r3_c28
              )
            )
          ) (
            cond (Nat.blt c 32) (
              cond (Nat.blt c 30) (
                jp01B2r3_c29
              ) (
                cond (Nat.blt c 31) jp01B2r3_c30 jp01B2r3_c31
              )
            ) (
              cond (Nat.blt c 33) (
                jp01B2r3_c32
              ) (
                cond (Nat.blt c 34) jp01B2r3_c33 jp01B2r3_c34
              )
            )
          )
        ) (
          cond (Nat.blt c 41) (
            cond (Nat.blt c 38) (
              cond (Nat.blt c 36) (
                jp01B2r3_c35
              ) (
                cond (Nat.blt c 37) jp01B2r3_c36 jp01B2r3_c37
              )
            ) (
              cond (Nat.blt c 39) (
                jp01B2r3_c38
              ) (
                cond (Nat.blt c 40) jp01B2r3_c39 jp01B2r3_c40
              )
            )
          ) (
            cond (Nat.blt c 44) (
              cond (Nat.blt c 42) (
                jp01B2r3_c41
              ) (
                cond (Nat.blt c 43) jp01B2r3_c42 jp01B2r3_c43
              )
            ) (
              cond (Nat.blt c 45) (
                jp01B2r3_c44
              ) (
                cond (Nat.blt c 46) jp01B2r3_c45 jp01B2r3_c46
              )
            )
          )
        )
      )
    jp01ListGet L rem
private def jp01Bin_2_r3 (j : ℕ) : M2BinCert :=
  PipeFuseCert.withForcedNat j fun j =>
    jp01UnpackBinR3C warmJP01V2Mono j (jp01Slot (jp01B2r3Get (j / 11)) 67108864 (j % 11))
private def jp01B2r4_c0 : List ℕ := [
 nat_lit 5378583587918706131036889540958768037904624331172739114256375489892104873599003620,
 nat_lit 5362835743635914078349018629191892464608178961561133445109079060774673981863455443,
 nat_lit 5347087899353122025661147717426513480406429091135998226476963255712169035666123203,
 nat_lit 5331397951556663767258918067379437548721221362113901006988824736543629734308047027,
 nat_lit 5315708003760205508908110827070500945710295157491881773757364196935872326868101028,
 nat_lit 5300133848936411469135252716368196114355567358886723402704350182291820718045488789,
 nat_lit 5284559694112620799381439204364935280714779087981816003442853736471633167922455944,
 nat_lit 5269043435333452157744382076551726199647422818105431224372111772369554249453233275,
 nat_lit 5253527177437710418489850507363133369099646914420787864027009642413234327427834735,
 nat_lit 5238068815586587337358741928534617969166311563672585278090337142588597157633679971,
 nat_lit 5222668350221798050538985816291978708410032271606914647492907972174631167708979545,
 nat_lit 5207325780901627421842652498252980791369604698516744581217544146584497693556301903,
 nat_lit 5191983212464883695528844934995035200329364784596186022577953708388561704385732421,
 nat_lit 5176698540072761997331793755928637950957078144989529018327403629028424616590794301,
 nat_lit 5161471763725262327225787952344148621167359430674365558531390853960147347559767349,
 nat_lit 5146244988261186189560396330969092308243156718102038654610332985760783874240764974]
private def jp01B2r4_c1 : List ℕ := [
 nat_lit 5131134004886350738083761870569944836532162521358487523758665583518618489721936679,
 nat_lit 5115965125908611764697345297065017537940257911819196795780128859500953228798024225,
 nat_lit 5100912039020110107557774311961386627491705125439036551247009926558742524869564700,
 nat_lit 5085858952573323586606132999244480245534062989952607890837311135025116849577613335,
 nat_lit 5070863762612870859940132948247373505187745606677000371838558323116029142731544340,
 nat_lit 5055868572652418133325555306985412915326318750757768075094525862776967419563955728,
 nat_lit 5040931279178299200970907918735108122667458141950585626330610143110699288465593614,
 nat_lit 5026051882190514062953323809619394071342482461501363450671154960808198785635800076,
 nat_lit 5011172485202728924935739896664605851364044804705250936730761387413419721953334027,
 nat_lit 4996350984701277581229508450297190325403152742648070265477585008876499149035753994,
 nat_lit 4981587380686160031834629470517147527714012239124505998009976441630400761975755018,
 nat_lit 4966881672715661140537462276229609073978798370593274550824387603174054514486890507,
 nat_lit 4952175965186877385453935763036938993143340770340477741362322926230897212773846797,
 nat_lit 4937470258099808766584049734778211465279170071305082849430974674404818631549472271,
 nat_lit 4922822447057358805811875884332343332131169245520711110281118932453375714477296913,
 nat_lit 4908232532501242639351054108154989454169303583270267878696341995780980099699657749]
private def jp01B2r4_c2 : List ℕ := [
 nat_lit 4893700514431456897182540592184822757014641926035100458478957319651870134899002137,
 nat_lit 4879168496361674525033071478754270826740233037588468299275245164998058699319364125,
 nat_lit 4864694374336514181000358553355838007299916442630609384156866497216042228592888098,
 nat_lit 4850220253194777369356837988908483169064920087740848723603605974740464968072906792,
 nat_lit 4835804028097662585830073808652676661079895466181924566904241323038643784878343983,
 nat_lit 4821445699045169830394355003878778084095420310232945007302100527238821731537602102,
 nat_lit 4807087370434388841178943290210344304382060134257086425608112587328890734001341757,
 nat_lit 4792786938309941646274883846969853999270627450035901848816206486990591474780685381,
 nat_lit 4778486506627206217565420878444046553848435218468399291586075206453654673374004046,
 nat_lit 4764243970989092816972714097950358196424459308715629643901575624978299266276606552,
 nat_lit 4750059331395598074503430111657318050199044510728019656276828652370511836211396962,
 nat_lit 4735874692243818468222075797751002421046733046558320654200106695602400801771438188,
 nat_lit 4721747949578372656226362941723915652921364438912933697668097233343303035716190072,
 nat_lit 4707621206912926844282072103113116585031494384442011584017465514277589755007417987,
 nat_lit 4693552360733814826623422722381546389586461615192539876879816319254120471072030096,
 nat_lit 4679483514996417945152702817875774902704131465968933104635687178138174285347110045]
private def jp01B2r4_c3 : List ℕ := [
 nat_lit 4665530461348258379903117689224081768066795347933112504565792996856487222875470762,
 nat_lit 4651519511655480156555820775081380878570228094756038461980430812994194562767600312,
 nat_lit 4637566458449035727545587532392129192075093509673763642939994251519563313980717511,
 nat_lit 4623671301728925092795284346553607482854055802648648746163604224839765385167190230,
 nat_lit 4609834041495144882363000233472484157109815122105086171283250041636431233645754342,
 nat_lit 4595938884775037617657452851202076109939944817598502533940135582836309983591741175,
 nat_lit 4582159521027594571555565803405872909668718181790038767121853629351692210130859528,
 nat_lit 4568380157280151525453678559451737067658413175299625975579176501573235746360603929,
 nat_lit 4554600793532708479351791707817956264992282753134292707784352444304436212029535275,
 nat_lit 4540937222316217885658968912103126714623361155440018738302359209564615276748550974,
 nat_lit 4527215755496823770082074815829735384689868476575186537753594020828802540785447505,
 nat_lit 4513552184722048312602892701209774207220703147823966274528670013495158543349526884,
 nat_lit 4499946510433606649409352044469041890778480675597058056848458205520370835131805817,
 nat_lit 4486340836145164986241522396436453430162998250781224320162622859232498953125572493,
 nat_lit 4472793058343053747391711821159766775347686007194088334211663651011406246628109987,
 nat_lit 4459303176585567906626279819038526286593325843348048722258690985949501849119043001]
private def jp01B2r4_c4 : List ℕ := [
 nat_lit 4445755399225175173983443318686682338054568634536482884814979509026375499857865935,
 nat_lit 4432323413954019757536030389321343655100465764869686781735987837528309737379015654,
 nat_lit 4418891429124579477302258141050873345045944939574075793818370642421747684908935933,
 nat_lit 4405459444736850963263081975176227410177240855521272610968706018810600898769660437,
 nat_lit 4392085355952032711146066111097305441790760417490114006181634950956754993823033646,
 nat_lit 4378711268050637991443953420518176068184410630850155951550099862521824941882550343,
 nat_lit 4365395076193865299832886105422451191837342725046640849628564258796752754996225888,
 nat_lit 4352136780381714636312863969650701570497714177606761341724404174378847548600821370,
 nat_lit 4338878485011272369019815727310878499950816453696557988468888271397874435500090773,
 nat_lit 4325620190082548607908030355029821626696673804156603161040701858766390738106393776,
 nat_lit 4312419791198443504919667973108842184056971706223861112236029203362782732663595979,
 nat_lit 4299277288358957060029017572839796316204970114481099354737867652855845183380726503,
 nat_lit 4286134785961185751352007461346760359585177050615319286630307242386299249501086212,
 nat_lit 4272992283563417812694042144710701042418488998082295114382565666073168938885521697,
 nat_lit 4259907677651976928335051302134492700109266831231100841264388912502929835528626238,
 nat_lit 4246880968226873208255035115106561743693472683236783842613014427771158768956284764]
private def jp01B2r4_c5 : List ℕ := [
 nat_lit 4233854258801769488200730132947700451614819297774815371279379770587952709260353147,
 nat_lit 4220827549376665768146425150788839159536165912312846899984431034782571779501530521,
 nat_lit 4207858736437895842403472635217350584311195430786264955228570960025214764986080441,
 nat_lit 4194889923499125916660520119645862009086224949259683010472710885267857750470630361,
 nat_lit 4181979007046689785228920070661746150714937371003868523722394700811190004308450041,
 nat_lit 4169068090594253653797320021677630292343649794077287103398081223553760435176544794,
 nat_lit 4156215070628151316677072439279390561731349621235012831846304681132956422359423291,
 nat_lit 4143362050662048979556824856884143997890371792167444513437323402283774896074856541,
 nat_lit 4130566927182280436722218536205703920307377914512898427509010251463798527929685887,
 nat_lit 4117771803702511893939034429104477340052127537605320666118313471299134414368872098,
 nat_lit 4105034576709073775422447377344361443038262746955381212483779674388499483849725381,
 nat_lit 4092297349715639026924904728122363735228023881170340303281873330905632126314943721,
 nat_lit 4079560122722207648420695472730340372212652434486822788394109386425498005778928653,
 nat_lit 4066880792215106694234505290095715369838114930989489357265003948394693472425677618,
 nat_lit 4054259357752624398171737901661738578662138539257315586195650824083551753931526743,
 nat_lit 4041637923731857238296900185614486293141283939695368681605634047098519353187832188]
private def jp01B2r4_c6 : List ℕ := [
 nat_lit 4029016490152801844616658551963058405642122052385655918769498433755668471517614242,
 nat_lit 4016452952176656712832866211399210617380549333660157037569253011707782810282954696,
 nat_lit 4003889415083935113489688053043299279725760202115610354407587925489851304568491759,
 nat_lit 3991383773594123776017248179065327642059137972763613641987427845906366185566572054,
 nat_lit 3978878132546024204765115396192820801663630722720123909544277059533200492998102334,
 nat_lit 3966372491939636399733289704425778758539151339699204326229087734403088711041616998,
 nat_lit 3953924747377870622792509388139148057320700149002860547056324135263567458978696079,
 nat_lit 3941534898860723503949440857348014855409429282475330734702983212544809112956111544,
 nat_lit 3929087154740672863222301222156252527090734360057426663856144982981736138661235169,
 nat_lit 3916755202709859538690585157950995464356519553541656802665649183948525763284502795,
 nat_lit 3904365355076142692249086980639958574741481444522237110956242503911275587334899765,
 nat_lit 3892033403487044503931011597529569884907022906284906958091672074454513489726080864,
 nat_lit 3879759347942564973736359008619829394853143938165047275693135629741577426649810571,
 nat_lit 3867485292839800579729636092096813410454386762215424600901366105736878153222260151,
 nat_lit 3855211237737039555716246569403771782268478547014994227723910536723329350640534755,
 nat_lit 3842995079120605586027542725638154181346431285260992114620215563373102493447029775]
private def jp01B2r4_c7 : List ℕ := [
 nat_lit 3830778920504174986332172275702510925219338554229821016980050145788152829775381308,
 nat_lit 3818620658374078180922443087485170733026856619864526722981712266496439529307177577,
 nat_lit 3806462396243981375538425104136900182335378139499745341060159066915953687294837143,
 nat_lit 3794304134113884570154407120788629654480036967002185576564474626326395109910708421,
 nat_lit 3782203768470121559081741604027731820642241389908171652687151238424423683368746995,
 nat_lit 3770103402826358548009076087266833998222514467412387605978935158011852084560461602,
 nat_lit 3758060933668929331247763037093308892656470448851990085848493660020625896945286737,
 nat_lit 3746018464511496744467405388220739789376399790305409833679887969306033135148400001,
 nat_lit 3733975995354070897725136936746258681524382411731195045587610664042677155702308017,
 nat_lit 3721991422682975475249465148291036628474880534573835524601146451947668429920074721,
 nat_lit 3710006850011880052825215573413028084171190813426283132650148862907242659906779922,
 nat_lit 3698022277340784630375255185987801515387299067856156994172465318924394672818027075,
 nat_lit 3686095601156023002236647068989021832110552202568307720514808827084100978819004788,
 nat_lit 3674226821015880032195750737482746515623869280804626882457498759478642018973186214,
 nat_lit 3662300145272833540270783301577338627570251840536204739680667367383987142522370009,
 nat_lit 3650431365574405706443527651165931672565256533781966799128806226311416384040400651]
private def jp01B2r4_c8 : List ℕ := [
 nat_lit 3638620482362308296908579868644350014376544335565173226423942279828715074551608895,
 nat_lit 3626809598708502491198080602422994823362875459201205194321162673544033002073027954,
 nat_lit 3614998715938120217876773500994784960397292685339224754565980559277555842748183718,
 nat_lit 3603187832726029548354203711002221644717474546210132237572336665377932041030136794,
 nat_lit 3591434846000269303149652993765560112001863505678983231068649804115510151570846479,
 nat_lit 3579739755319127716068525070729546790484813576912993884624715256572751076970656324,
 nat_lit 3567986769035082607051904025878113208583660566594585411576582374251636293774143865,
 nat_lit 3556291678795656156158705775228824404139713971646507050680672842550805397433020591,
 nat_lit 3544654484600848363388930318781680365734992249756460684975839761354630852305285093,
 nat_lit 3533017290847755706781373526010123856059430320678069675671276542759251577514422043,
 nat_lit 3521380097094663050199527741948207768469079517379446081067809048206942080934276690,
 nat_lit 3509742903783282159837989048991756478149930805675256156085596262696691560290643337,
 nat_lit 3498163606074811531347188640411748310142235039289448938893255967949352068341886145,
 nat_lit 3486584309249764435297002414042669736676769231520645540450131548339220266408799224,
 nat_lit 3475062908027627601117554472050034274104774826757926732797047683444514148284164913,
 nat_lit 3463541507247199163165080031173460056011217196293754271635775518969682040867973737]
private def jp01B2r4_c9 : List ℕ := [
 nat_lit 3452020106466777465199272574116263735505205190605669695000184787984483045388118434,
 nat_lit 3440498706128064163460439010492490543468463742078793011179122717253027604880877787,
 nat_lit 3429035201833972889786939617484548762030577368730188156906754645391864154008250389,
 nat_lit 3417629593584500274262574027385399013363960417993447324089574734575657577750128463,
 nat_lit 3406166089732124136802715315472325593407848772604826054898044567758693575834658441,
 nat_lit 3394760481924366657466279201600471142398455715179329091172670587972203949956588996,
 nat_lit 3383412770161227836227555265539979497010711257054867418740446217401606775740228863,
 nat_lit 3372007162353473726910163750367169043715344838950939189199463824966343199681209402,
 nat_lit 3360659451032050041885080299240619962716868823026934343666983872823922133063492470,
 nat_lit 3349311740152338123054592930512888412257376125236286689493212520753763970609636018,
 nat_lit 3338021924875533096152932469747913328131985965189289213735290908503476730948018670,
 nat_lit 3326732110040443205439201485210233541663732585502984778366355380237058908834685227,
 nat_lit 3315442295647068450913399976898352463758181824513317282106024032974357141831344232,
 nat_lit 3304210376856597218297380974014102841172411560495548284486966509058053543254220709,
 nat_lit 3292978458507841121895002259904366540724154327162142660664190467392649367372357347,
 nat_lit 3281746540159085025492623938113488701943444833565575987320565727274617449659162145]
private def jp01B2r4_c10 : List ℕ := [
 nat_lit 3270572518296662723401597690589628529254175004981091510162784852047899322218896735,
 nat_lit 3259398496434240421310571639226694176493374545451486817477586435483852580678065310,
 nat_lit 3248224474571818119219545587863759823732574085921887195433474853215236938707164125,
 nat_lit 3237050452709395817154230741369895135308914388924636100784474646100679549960379164,
 nat_lit 3225934327333307309348845951725263835064656070798074477884340349726029552828734043,
 nat_lit 3214818201957218801569172366949702199157538515203861382379317428505437826101205403,
 nat_lit 3203759973067464088100851248761513280104103863545034813413383168332870014617049308,
 nat_lit 3192701744177709374632530130571827771955973712699737793932268284105376257594677276,
 nat_lit 3181643515287954661164209012385135430579165905629151798235035497744936121034528605,
 nat_lit 3170585286398199947695887894196946522943799908568550035874493553519735463414650526,
 nat_lit 3159584953994779028538919242594633731649352661658644613573554164635696738385450463,
 nat_lit 3148584621591358109381950394834388298615827044066785095907133062310293385650033953,
 nat_lit 3137584289187937190224981939394497904926476010800005101988564440198736603648021603,
 nat_lit 3126641853270850065353654549511984766661335059077827865311088442915525523290772390,
 nat_lit 3115699417353762940508038364498541281315266214625160351530873568387102012153058024,
 nat_lit 3104756981436675815662422179485097795969197370837106835643116630310582013975777835]
private def jp01B2r4_c11 : List ℕ := [
 nat_lit 3093872441564207348940228984833228307496127270640123858680870495306835523466088814,
 nat_lit 3082930006088835360308253284753727386539413981338458929939504599557994182729322674,
 nat_lit 3072103362702700687871701547979590192834728545681930238219973618065954383087325174,
 nat_lit 3061218823713659123532033911950840377204699080038988794251369490834142872534306618,
 nat_lit 3050392180327527821114526381555392141869865700043563310822149926710473347968716414,
 nat_lit 3039565537383108284891615129716694090231075551840351087727238060602830531205189059,
 nat_lit 3028738894880400514863300156433249644611963127034292834661470937478538236771486984,
 nat_lit 3017912251935984348633722298426022504026772813823701147656103844481562608629238861,
 nat_lit 3007143505477898606722163513173200591565125836588952640224453184137177988944808851,
 nat_lit 2996374759019812864810604727921875256780105704607058703953962229204729736497646297,
 nat_lit 2985663908606345781022468736872694688034310446347810760767005661228841365404043807,
 nat_lit 2974895162589975175298839624006597304063748344578657357913383354157937247802149221,
 nat_lit 2964184312618223227698633305342644686132324004246213117332933523456404408303143084,
 nat_lit 2953531358691089938196138772171196412154913411192043598485951871281590031656863731,
 nat_lit 2942820509161049756816239544612708591494691162454038098129157662541973954720876346,
 nat_lit 2932167555233919837307078601432160470822635815908587639077584042272395514438534786]
private def jp01B2r4_c12 : List ℕ := [
 nat_lit 2921514602190213450212820831749908367253997163880160325986425843189255269049484745,
 nat_lit 2910861648704795296949677988382968888261728190120675448552216764030520940565415186,
 nat_lit 2900266591263999171751869511788296906766641790636434111921982499031825024594789466,
 nat_lit 2889671534264914812774368126299089711124688828148406708871326208967915780264870819,
 nat_lit 2879076477265830453796866740809882538318698949620351400684388992775500381789668075,
 nat_lit 2868481420708457861039672446424643573689128552543560617782881944869953658080641589,
 nat_lit 2857944259753995530153216436418840875306457471556590165450739659502905030364021118,
 nat_lit 2847407099241244965487067321357577177102395085447817789494626932646338829756186824,
 nat_lit 2836869939170206167015514681010996315751610068032760408838970864634995445286617106,
 nat_lit 2826390674702074260472788556309810048161901121909888119715898199100738590797250396,
 nat_lit 2815853514631038831994569309794700097864715939487451275149786904200062412128698022,
 nat_lit 2805374250604622061639772857480238347348023214896558211289407004380563069645667825,
 nat_lit 2794952882622823949382688190658280940785431349869861488281711333607409033412787516,
 nat_lit 2784473618596410549046936140881937379472364550143877110058760417900732292733123719,
 nat_lit 2774052251056324203010158761324874001014574422672784009272374316943632182329392083,
 nat_lit 2763630883516241226966714775597784967351651714303209232236415328299327438522333983]
private def jp01B2r4_c13 : List ℕ := [
 nat_lit 2753209515976158250923270789870695933688729005933634455200456339655022694715275883,
 nat_lit 2742846044922409069165468065863406541636956825203017299082149492540440495324182967,
 nat_lit 2732424677382329463141068678833864916593452370583705632310679545838092080942987523,
 nat_lit 2722061206328580281408977159694148599784212566149517381813809218239559452565616720,
 nat_lit 2711697735716542865871481722950256669578683932319879154002131385771893065200744349,
 nat_lit 2701392160707412342237102185463970505233771477334683772334243685353924820570388202,
 nat_lit 2691086586139996954816362936750701096767813862379221999829499120417107480067880504,
 nat_lit 2680781011572581567395623884198357485394275420232741227405429698272889458505594246,
 nat_lit 2670475437005166179974884831646013896856700061381618551913935787320593636247254228,
 nat_lit 2660169862437754162573190377792714283197101146270769682747839163255156877848130594,
 nat_lit 2649922184356669199444759193128699402381287622671722582071173359676142633788027760,
 nat_lit 2639674506275587606335372607163728519279326513157761626513375793824503572908782271,
 nat_lit 2629426828194506013225986021198757636177452517258960426987140724776174104972014094,
 nat_lit 2619237046599758214427951901821159469929261423966312687573991609576630375248343389,
 nat_lit 2608989368518676621318565315856188586827387427402897490155298604076397377171402924,
 nat_lit 2598799586923928822520531196478590420579196334774868819275694259624188294337835004]
private def jp01B2r4_c14 : List ℕ := [
 nat_lit 2588609805329181023722497077100992254331005242146840148396089915171979211504267084,
 nat_lit 2578420023734433224924462957723394088082814149518811477516485570719770128670699164,
 nat_lit 2568288138626019220437781304933168638688305960826169333175969887315584961080503788,
 nat_lit 2558156253517605215951099652142943177875729117535297311588975053668601522876099901,
 nat_lit 2548024368409191211464417999351221150804594084254414593979757896452288680361897102,
 nat_lit 2537892483300777206977736346562492290504694281797692071374231442456192278757682143,
 nat_lit 2527818494236981860588766479264771185064199841047933576095926587340691250938030896,
 nat_lit 2517686609570282992315725507569414108569360808347794309232288736695845858820663938,
 nat_lit 2507612620948202782140396321365064786933927137354619069695872484931595840487729619,
 nat_lit 2497538632326122571965067135163708632069728697185604025163146936387562245885045029,
 nat_lit 2487522539748661019887449734453360254900898701354292036356674022318868591007148151,
 nat_lit 2477448551568295945925761033184450075331360317149819267591104280562371362843174858,
 nat_lit 2467432459432549530036073304860826215235546542850486504047324132208435219971352348,
 nat_lit 2457416367296803114172096585245346199548404161364003414892527834448394335547860591,
 nat_lit 2447400275161056698333830874338010028269933174684206923163002657492685231129273794,
 nat_lit 2437442079069928940567566136374463587370491298723095198024660441092765476904674581]
private def jp01B2r4_c15 : List ℕ := [
 nat_lit 2427425987375897660917229901694422713749331316311241269284956659470279125032019049,
 nat_lit 2417467791726485039338894639958171570507113333661368342674704792262233305792160700,
 nat_lit 2407509596077072417786270386930064271673653856774885777951455092002119883932082960,
 nat_lit 2397551400427659796259357142610100817248865773365861814868560639642531147436827236,
 nat_lit 2387651101264577598999040953629751468388923543247548278024915766402742114120933817,
 nat_lit 2377750801659787005563172888633763280389556358520616032243169628962332175524733197,
 nat_lit 2367792606452089520224189316700524354455853150577187173738303234730570561572741218,
 nat_lit 2357950203333629351080629315752294116430003212618423955836161924310485011520855991,
 nat_lit 2348049904612262290033953807866813140469817250778550127395813377954575378160983820,
 nat_lit 2338149605449186832786015415257549469543553400534142865015864861725982393912696417,
 nat_lit 2328307202772438429862762701572716693363947008811744577527894334350752129400479159,
 nat_lit 2318464800095693396932843185559925597403992357641683830396599829088576365863935244,
 nat_lit 2308622397418948364002924061865992963111672558494393793991102954120866614177995874,
 nat_lit 2298779994742206701066338135842605431362551879218450247235730017430115493231762360,
 nat_lit 2288995488110080326259841610191388332275683083925386728712877652450277899622718223,
 nat_lit 2279210981919669087615563748215758761917974080114750570766693650942012182293289573]
private def jp01B2r4_c16 : List ℕ := [
 nat_lit 2269368579684639190899285109457265269691549567756163005132043581132212217122560444,
 nat_lit 2259641969538846610378430041683780465373065437668172840308079592808174497557420307,
 nat_lit 2249857463348435371759863188419287894777368629462022188717443973403763029013600362,
 nat_lit 2240072957599735899361603426257266977517340429128321825868151561996432143178176449,
 nat_lit 2230346347895658455054389039578650534680631025671092320903825187650629827685029657,
 nat_lit 2220619737749869244526867561794569305990788185217648882359920838374544440178808432,
 nat_lit 2210893128045791800219653175115952874572060324072712423793025782306526679292220872,
 nat_lit 2201166518783426122132745879542801240424360329950346114354092187481562829017617696,
 nat_lit 2191497805123967335923243278356689152959646216083679306918264692170562740703499385,
 nat_lit 2181771195861605027829669572771444516763960667007619150490689262581423547563807697,
 nat_lit 2172102482202149611613500561576232582604514687363739642564937253900583532828201770,
 nat_lit 2162433768984405961617638641484988868039469729489575712644672922428686157044814466,
 nat_lit 2152765055766662311621776721393745153474424772280025780616866527408692311401599451,
 nat_lit 2143096342990630427846221892406469658503780838169419422379463682499196365177131317,
 nat_lit 2133485525817508805941405347798630429780036220148633394634054347672862247763873934,
 nat_lit 2123874709086095580263562304305355867857927307266279478413660756111364220622901224]
private def jp01B2r4_c17 : List ℕ := [
 nat_lit 2114205996310067066481341065307483948516011774411542679335536193307594507963764545,
 nat_lit 2104653075623275868894543397296117294758576355465098096236380251675725003988569755,
 nat_lit 2095042258891866013210033943793742874723841147443789261908821927967786278652906997,
 nat_lit 2085431442602171293713454162675099816408955582734682270806969504423556359461178703,
 nat_lit 2075878521915380096152367503371877018478173099577994406309315415659933948679457962,
 nat_lit 2066267705625685376655787722254730537839914380121741986368622697527640413904866308,
 nat_lit 2056714785380609315282630735338232256982235230782965107418993624603694398748396383,
 nat_lit 2047219761180151912007185533914238320078482716436521048751384280471752322976877242,
 nat_lit 2037666840935075850659739555705883895047456502222881819908398211044292101427071509,
 nat_lit 2028113921131714925474512045016680900429019703883055763691829081954293236095551857,
 nat_lit 2018618896931257522224778048460260038767799565833035540081940970648462878115662028,
 nat_lit 2009123873172515255137262519422990630355044814666254825745712765596940247232055336,
 nat_lit 1999628849413772988075457999093865066351048569262864473335172353721018147318957955,
 nat_lit 1990133825655030721013653478764739502347052323859474120924631941845096047405860575,
 nat_lit 1980638801896288453977559967143757782751814584219474130401093401769201165519717947,
 nat_lit 1971143778579261323103684923040430938728415386874468005357484223966775157886453144]
private def jp01B2r4_c18 : List ℕ := [
 nat_lit 1961706650865137714165303393072879371597417885062148191872454615165878348274762996,
 nat_lit 1952269523592729241389140330622982680038433149452071766468189679983300131106489425,
 nat_lit 1942832396320320768638688080721800602054345938115643394754761513039188320122733486,
 nat_lit 1933395269047912295888236026980047754904032596647639568883309762211290135453008650,
 nat_lit 1923958141775503823137784169397724138587493125048060288853834427499605577097183848,
 nat_lit 1914521014944810486600972600589913844408553796418766001623800042025599828869153221,
 nat_lit 1905141783717020671948232528501591161140549346047434093008933047746559002597687586,
 nat_lit 1895762552930945993509132745186285210915536652410477696702004930209831348517765248,
 nat_lit 1886383322144871315070033158031905080618819102591928637122995216530454529249279966,
 nat_lit 1877004091358796636630933570877524950322188665059311337790632126750580259822927675,
 nat_lit 1867624860572721958191833983723144820025645339812625798704915660870208523058708121,
 nat_lit 1858245629786647279752734396570261278823623288515928121107541800498423019618467320,
 nat_lit 1848924295486906395624987276001757276285980255732226897799087042861803716243651926,
 nat_lit 1839545064700831717185887885008302965917819187254499524221479785185306035510082740,
 nat_lit 1830223730401090833058140568280369732546402285266997894206993999947256743177911315,
 nat_lit 1820902396101349948930393447713362319103454751005148052918860721845896872041937778]
private def jp01B2r4_c19 : List ℕ := [
 nat_lit 1811581061801609064802646327146354905660507217407917280125586293114046517858958033,
 nat_lit 1802259727501868180674899206579347492217646796761237336073817337651208213291104816,
 nat_lit 1792996289688461090858504552599712795628295054148842261039440175320544594799262095,
 nat_lit 1783674955388720206730757432032705382185347520551611488246165746588694240616413423,
 nat_lit 1774411517575313116914362778053070685596082890889767241991979978904867801676675150,
 nat_lit 1765148079761906027097968124073435989006818261227922995737794211221041362737067950,
 nat_lit 1755884641948498937281573470093801292417553631566078749483608443537214923797460750,
 nat_lit 1746621204135091847465178816114166595828289001904234503229422675853388484857853550,
 nat_lit 1737357766321684757648784162134531899239024372242390256975236908169562045918246350,
 nat_lit 1728094328508277667832389508154897202649759742580546010721051140485735606978639150,
 nat_lit 1718888787181204372327347320762635222914178016854083220364867199554501966532473998,
 nat_lit 1709625349367797282510952666783000526324913387192244044751768266166106644342797295,
 nat_lit 1700419808040723987005910479390738546589331661465786325036671159530304120646562639,
 nat_lit 1691214266713650691500868291998476566853749935739328605321574052892249779956642480,
 nat_lit 1682008725386577395995826104606214587118168210012870885606476651108542076907581969,
 nat_lit 1672803184059504100490783917213952607382586484286413165891379839622896532377858418]
private def jp01B2r4_c20 : List ℕ := [
 nat_lit 1663655539218764599297094000248137524572218293440452046960615266781584356065702100,
 nat_lit 1654449997891691303792052009016801364765105936104265184466729516651980770518659125,
 nat_lit 1645302353050951802598362092050986281954737745922923134069509714558003223916474262,
 nat_lit 1636154707768497165191031886312154466101552024243688160352502542589913111887376120,
 nat_lit 1626949166883139005899630380014760859265726567460279076292073455292524560056872538,
 nat_lit 1617801522042399504705940659209871596383827745004593885223607073252842421463838140,
 nat_lit 1608711773246278661609962723897486677455855558205855512329618356457067769575795998,
 nat_lit 1599564128847254296604202479318396123136572243490108566510426317340760366350363776,
 nat_lit 1590416484006514795436223963381079935497118685044915450253034544227687395706825698,
 nat_lit 1581326735652105718534842110466015980849571625724899433559586420272157409783737156,
 nat_lit 1572179090811369587360196988360170704263630789986400163708807787912281768968481447,
 nat_lit 1563089342456963880477859537981728349725014157674055448524925104986218448390482442,
 nat_lit 1553999594102558173569811275056067959288126846340907109645249159628333083003218284,
 nat_lit 1544909845748152466687474020838551413259910927820608445115871438636674859653556431,
 nat_lit 1535820097393746759830847775329178711640366404106996378011764838449348381949061170,
 nat_lit 1526730349039341052948510717271091396445924356119736257216821470025807315053602709]
private def jp01B2r4_c21 : List ℕ := [
 nat_lit 1517698497171265770358481330943400147233991546801495958388213253848253937246693113,
 nat_lit 1508608748816863433495188479264001790409401553810714906747636209426204670243923548,
 nat_lit 1499576896948788150905159289095739772031242615025513151653462345816768466071086527,
 nat_lit 1490545044639004472139578419068274989994353127560098393426938469837234342454256931,
 nat_lit 1481455296726313901470881649786197586032119608779047957807512114354891951242372231,
 nat_lit 1472423444858241988899896862156053756857586594194135819817223054409005843322397675,
 nat_lit 1463391592990170076328912074525909927683053580273837679719391930917275065356280655,
 nat_lit 1454417637166716821855639268547699673296221071878905833035613975870311213409919667,
 nat_lit 1445385785740356675479250563314876796984044531503724311027789978638715647503786519,
 nat_lit 1436353933872288132927310178222851157013050330162398025718340302442698934686343547,
 nat_lit 1427379978490546644648633454641961855488661407598509486768815479785672020002103520,
 nat_lit 1418406022667096760194404855042440559471680953535452852590433069198767783224434756,
 nat_lit 1409374171240739983811349739799021258788145702794818056823983379935361612319186857,
 nat_lit 1400400215859001865551717418756250135049314051162227394798953161895693641354600206,
 nat_lit 1391426260477263747292085097713479022728463941177310710637809786532128992005348979,
 nat_lit 1382452305095525629032452776670707910407613831192399097079067324090673929096289752]
private def jp01B2r4_c22 : List ℕ := [
 nat_lit 1373536245758406168896243249828584997867343291324963024511388506853062786177981757,
 nat_lit 1364562290818379816831207207341067491566083792451273620696458537265535796712070306,
 nat_lit 1355588335436645068564908280129767290298746405173050782941928597805325456357743623,
 nat_lit 1346672276099525608428698753287644377758475865305614710374249780569966113253120877,
 nat_lit 1337698321159502626356996104631597782510729089138614082363532333965935646155496146,
 nat_lit 1328782262264094932415382856344728475990049160382400219539666009586756159127968312,
 nat_lit 1319866203368690608467103001889330080522794842046943372234679958063902545395866014,
 nat_lit 1310950144473286284518822951274502454221853766128998809975450653467360158601730307,
 nat_lit 1302034085577881960570543096819104058754686560079473722955796852071677211122358377,
 nat_lit 1293118026682477636622263438523134894121293223898368111175718553874601903144064975,
 nat_lit 1284201967787076682667316977897710832031099007588608989045764193952233426091792181,
 nat_lit 1275343804936291016816748908936313358194485281119657295615517221388350260871714460,
 nat_lit 1266427746482598459088776341744312424573474509685174306053444897817970989136369154,
 nat_lit 1257569583631816163231541666612889284113833772955993648115298279645008263976473961,
 nat_lit 1248653525178123605503569099420888350492823001521515729155626868992234996233819343,
 nat_lit 1239795362769053075866641515393433429627583287891273574366797261784496067269121078]
private def jp01B2r4_c23 : List ℕ := [
 nat_lit 1230937199918270780035118045129583375828369356155650041774869445454531937389925276,
 nat_lit 1222079037509200250372479648553413852806213660564052879615263430978680086198506243,
 nat_lit 1213220875100129720735552260685388174192729358449914319134698290631021053962506858,
 nat_lit 1204362712691059191124335881525506339987916449813234360294488398183886707091329489,
 nat_lit 1195504550723700427682004576053305036560161777320580771963971560046200888909254968,
 nat_lit 1186646388314633268038410778174682933575318764176374939832322496064670725187588256,
 nat_lit 1177846121950181396499195175800658176592475053928746603751526390286157040448065543,
 nat_lit 1168987959982822633082574879036600717573391774913551617061364800051247707444629358,
 nat_lit 1160187693618374131536692866651979536219189353635856009329484770638862891219439318,
 nat_lit 1151387427695637396211117945369829996782673998582926571270258985562086383295155773,
 nat_lit 1142529265728278632794497648607269115440304675777294990766703138422494977678921125,
 nat_lit 1133728999805541897468922727326616153680503277598542956825226659122859860686163213,
 nat_lit 1124928733882805162143347806045963191920701879419790922883750179823224743693536373,
 nat_lit 1116128467960068426817772884765310230160900481241038888942273700523589626700909533,
 nat_lit 1107328202037331691492197963484657268401099083062286855000797221223954509708282693,
 nat_lit 1098527936114594956166623042204004306641297684883534821059320741924319392715655853]
private def jp01B2r4_c24 : List ℕ := [
 nat_lit 1089785566236480248932093496405259264464064210667048335748780067782817100802181653,
 nat_lit 1080985300313743513606518575124606302704262813152910299738447151165005447354141053,
 nat_lit 1072185034832718544501250744949418138215576394282665245773979965073437956981147877,
 nat_lit 1063442664954603837266721199150673096038342920730792758394582853613759128612128846,
 nat_lit 1054700295518197526259165154467989275503583136852880524712135396314195594804086710,
 nat_lit 1045900030037175927147230914280708108966824050743004792909978543493439045558355743,
 nat_lit 1037157660159061219912701368483459644466304534065309709609645111580981674716710536,
 nat_lit 1028415290722658278898478913790179388142204497509651155848511601281505851765310961,
 nat_lit 1019672921286255337884256262937469912402312133397866173206548279831286993335108953,
 nat_lit 1010930551849852396870033808244189667496193639154500665804160461579675791585854658,
 nat_lit 1002188182413449455855811549710338653423849014779554633641348146526672229337678891,
 nat_lit 993445812977046514841589095017058408517730520536189126238960328275061027588424596,
 nat_lit 984703443982355340021962722719602550215323197561987639414222941601716014544339710,
 nat_lit 975961074545952399033451276735962727394502941384321306959577471290425306674512487,
 nat_lit 967276601154171486110274001365161159819284071873059655331309736221738518730129872,
 nat_lit 958534232159480311316358833935278376759322012244736245386503395795431009904771385]
private def jp01B2r4_c25 : List ℕ := [
 nat_lit 949849758767699398393181558565973386860729987321710096463221847848934043662041251,
 nat_lit 941107389773008223599266391136090603800767927693391757120816420340232521649635340,
 nat_lit 932422916381227310676089311926214844735949772638790154039511288509949181720936310,
 nat_lit 923738443431158163973219127660878085849740312462386627334235715187896469087338208,
 nat_lit 915053970481085647277015745724996224420331732414641681542551490285578378377444937,
 nat_lit 906311601486397842476433972125087774737342662526089307128531130477859443202866611,
 nat_lit 897627128536328695773563984019180246684907071553496328372774036822368626556812573,
 nat_lit 888942655586259549070693995913272718632471481245517347509474879618781340050930823,
 nat_lit 880316078680809060465535793299869534533962525929871186928195451207198010109869041,
 nat_lit 871631605730739913762665805193962006481526936286506203957354230455514253744159579,
 nat_lit 862947132780674137053129210919525389482604068020602001005809364635614797293435589,
 nat_lit 854262660272316756544855501368871467449759088823845229886322700288207366864517680,
 nat_lit 845578187322247609867696521971107795223976433641008969732067459500963643411937690,
 nat_lit 836951610416800491255871713189175522178980201032051584955000554072876835839293700,
 nat_lit 828267137908443110747598003638521600146135221835294813835513889727721222403930223,
 nat_lit 819640561002995992161484203564733182927791924351480149767490900713726178070902745]
private def jp01B2r4_c26 : List ℕ := [
 nat_lit 811013984539257269776633288214727460675526515272198919639067881574666284439975748,
 nat_lit 802329511589191493067096693940290843676603647670908714579981247354575520302511790,
 nat_lit 793702935125456140675579172421756032477850961298316260255770456051106969687045657,
 nat_lit 785076358661717418290728257071750310225585552219035030127347732059952255409075588,
 nat_lit 776391886153363407775787941352567299246253295728967034812073590696041364528444654,
 nat_lit 767765309689628055384270419834032488047500609356374580487863094540477993265935449,
 nat_lit 759138733225892702992752898315497676848747922983782126124966972157246471232959428,
 nat_lit 750512156762157350601235376796962865649995236611189671800756476001683099970450223,
 nat_lit 741885580298421998209717855278428054451242550238597217476545979846119728707941018,
 nat_lit 733316899879305303915912119252397587206416498858337583473040838710228447600849413,
 nat_lit 724690323415569951550105606442006631834316747610882779255473346051150869945004400,
 nat_lit 716063746951837969151921478753446154012449938692129600176716580387005423260283099,
 nat_lit 707437170929814382955000039632232295676053726529262691232570234025874807385108551,
 nat_lit 698868490510697688661194499765631059265088657303354292676601888908330744203587506,
 nat_lit 690241914046965706288721380785214437269874783509738763743173752966087424902442781,
 nat_lit 681615338024942120091800137823429809767252441215291330038603204953721427694857865]
private def jp01B2r4_c27 : List ℕ := [
 nat_lit 673046657605825425823705410505543198349166437246101106388387691213818472856694260,
 nat_lit 664420081583805209620117561373732904223429972405492947929270873690618600413212000,
 nat_lit 655851401164691885345356227885820626182229845890141999524509090439881770339151051,
 nat_lit 647282721187286957271857779124684187042292644351417747988960143019546947723340855,
 nat_lit 638656145165266741068269733833444673500763851290069162795240908973463498258525090,
 nat_lit 630087464746153416793508596504961626293337594643137689630054924069239487038368526,
 nat_lit 621518784768748488720010147743825187153400393104413438133191602876572798013287034,
 nat_lit 612950104791346930639845092812663092808330610667207510309384141541365208403421670,
 nat_lit 604381424813945372533969029173357154054502322466611220637260139485893355004504401,
 nat_lit 595812744836543814453803974242195059709432540029405292852138304378353898985367741,
 nat_lit 587244064859142256373638919311032965364362757592199365067016469270814442966231081,
 nat_lit 578675384881740698293473864379870871019292975154993437281894634163274986947094421,
 nat_lit 570106704904339140213308809448708776674223192717787509496772799055735530927957761,
 nat_lit 561538024926937582133143754517546682329153410280581581711650963948196074908821101,
 nat_lit 552969344949536024078689708294528432392842133606766015813531000640683836916639193,
 nat_lit 544400664972137835991858047193340671424658228623394292671462278252609698201609542]
private def jp01B2r4_c28 : List ℕ := [
 nat_lit 535831984994736277911692992262178588497569987833867413391313824968699466835174578,
 nat_lit 527321201503665144123835805220841790968783313934110923978218844913299196620710942,
 nat_lit 518752521526263586069381955157252771866158795507397070965485697359047395421332362,
 nat_lit 510183841548865397982550294056065022316043544457636156536351354466436880430408439,
 nat_lit 501673058057794264194693107014728224787256870557879667161942000638704726626804323,
 nat_lit 493104378080392706140239256951139205684719464417097574395855476983955475269427663,
 nat_lit 484535698544706284248003678247272408996873574626516447246366349762039786454262076,
 nat_lit 476024914611923384291261613676187733848175691192140485118053843917397945812394152,
 nat_lit 467456235076236962399026034972320937160416913687491118215211340594984789659230229,
 nat_lit 458945451143454062442283970401236262011806142539046916333545458649845481679626113,
 nat_lit 450434667652386298647760177189873809277886887740803680068476973137539736242101998,
 nat_lit 441865987674988110586639720956259123552235359053855791945443562202255802188832346,
 nat_lit 433355204183916976824493738782495412683875490812270425809710651521520611633143239,
 nat_lit 424844420692849213029969945571132959950043348299953879188887876993363211858484532,
 nat_lit 416275741157162791163445571733342660828102990217561084353447874102047906003295392,
 nat_lit 407764957224379891206703507163754563356031951371425695532522468297201873876163597]
private def jp01B2r4_c29 : List ℕ := [
 nat_lit 399254173733312127412179910111821341455973678727533694753676109883006300601850746,
 nat_lit 390743390242244363643367125608602733130812930357289747665666519707277133512055527,
 nat_lit 382232606751176599874554537264813355639426051855470346419633345647761592736291411,
 nat_lit 373663927215490178008030163427023056517485693773077551584193342756446286881102272,
 nat_lit 365153143724422414239217575083233667608117273623579101871872117953064475690539309,
 nat_lit 356642359791642884275808904343619914931000766164888726406934204363147384591620250,
 nat_lit 348131576300575120506996315999830537439613887663069325160901030301380044002170887,
 nat_lit 339620792809507356738183727656041159948227009161249923914867856241864503226406772,
 nat_lit 331110009318439592969371139312251782456840130659430522668834682182348962450642657,
 nat_lit 322599225827371829200558550968462404965453252157611121422801508122833421674878542,
 nat_lit 314088442336304065431745962624673027474066373655791720176768334063317880899114427,
 nat_lit 305577659286948067857529456676708025168409124110843293149639899536455690260190504,
 nat_lit 297066875795880304088716868332918659095003787256702940369894481072901240546399381,
 nat_lit 288613988349431198417616065481633625557543543747216359405881330953294835688281090,
 nat_lit 280103204858363434648803477139340825742783509833637531467235256933575103427122031,
 nat_lit 271592421367295670879991084954980679085170501200242676063178498990273188965257949]
private def jp01B2r4_c30 : List ℕ := [
 nat_lit 263081637876227907136889505319335146002455016840495874349958509283185863694619210,
 nat_lit 254570854385163513361410310805520101888041128078442437993624776694733010712138167,
 nat_lit 246117967380426173884905590350059454954292055173505879714803826555835867700007204,
 nat_lit 237607183889358410116093002007766655139532021259927051776158047684021314791674001,
 nat_lit 229096400398290646372991618531550352890590406103990798012456537641244085694631935,
 nat_lit 220585616907226252597512424017735308776176518006551359548580741504694762852454252,
 nat_lit 212132729902488913121007703562274661842427445101614801269759791365797619840323289,
 nat_lit 203621946411421149352195311379411092861441281056455448570689515692590706433068614,
 nat_lit 195111162920356755602427125573739893155611674150547922102923256474669505926532532,
 nat_lit 186658275915619416125922405118279246221949713531543124070748930235274912756403489,
 nat_lit 178147492424551652357110012935415677240963549486383771371678654562067999349148814,
 nat_lit 169636708933487258607341827129744477535133942580476244903912395344146798842612732,
 nat_lit 161183821928749919130837106675780408278098826549712020140439838064785059949316969,
 nat_lit 152673038437682155387735723199564106029157211393775766415423954249675964442872535,
 nat_lit 144220151432948185904564396574077781054399587245540122452472626435532148488669764,
 nat_lit 135709367941880422135752004391214223491394964848059818219690106360538125957073329]
private def jp01B2r4_c31 : List ℕ := [
 nat_lit 127198584892527794580579900981367398971294986899023265970828586673018475773692191,
 nat_lit 118745697446078688909479098131578954528530241911388066988451289863255186557241484,
 nat_lit 110234913955014295159711108485336985656474504209286017906488223619706229002078202,
 nat_lit 101782026950276955683206388029876338722812544254895217766771833832215165972252519,
 nat_lit 93271243459209191940105004555156614150497773687199537310457718977138924742641365,
 nat_lit 84818356454475222456933677929670300593721691186642941813794146758956199850411586,
 nat_lit 76307572963407458713832294454950576021406920618942190755079118988525771621664175,
 nat_lit 67854685958673489230660967829464251046649296470711617394528704091987942480282909,
 nat_lit 59343902467605725487559584354744537892316067550689914802101431917518605313508490,
 nat_lit 50891015462871756004388257729258212917558443402459341441551017020980776172127224,
 nat_lit 42380231971803992235575865546394655354553821004979037208768496945986753640530789,
 nat_lit 33927344967070022778115547629052174788467590334207065488573329949973609863971539,
 nat_lit 25416561476002259009303155446188617225462967936726761255790809874979587332375104,
 nat_lit 16905778426649631454131052036341792705450102273621969253575914086962486990995886,
 nat_lit 8452890980200525783030445345982579096372114868474485302813122803972421024219419,
 nat_lit 3975466556325570127428640098530285884197702513582617955807959277247660169]
private def jp01B2r4Get (q : ℕ) : ℕ :=
  PipeFuseCert.withForcedNat (q / 16) fun c =>
  PipeFuseCert.withForcedNat (q % 16) fun rem =>
    let L :=
      cond (Nat.blt c 16) (
        cond (Nat.blt c 8) (
          cond (Nat.blt c 4) (
            cond (Nat.blt c 2) (
              cond (Nat.blt c 1) jp01B2r4_c0 jp01B2r4_c1
            ) (
              cond (Nat.blt c 3) jp01B2r4_c2 jp01B2r4_c3
            )
          ) (
            cond (Nat.blt c 6) (
              cond (Nat.blt c 5) jp01B2r4_c4 jp01B2r4_c5
            ) (
              cond (Nat.blt c 7) jp01B2r4_c6 jp01B2r4_c7
            )
          )
        ) (
          cond (Nat.blt c 12) (
            cond (Nat.blt c 10) (
              cond (Nat.blt c 9) jp01B2r4_c8 jp01B2r4_c9
            ) (
              cond (Nat.blt c 11) jp01B2r4_c10 jp01B2r4_c11
            )
          ) (
            cond (Nat.blt c 14) (
              cond (Nat.blt c 13) jp01B2r4_c12 jp01B2r4_c13
            ) (
              cond (Nat.blt c 15) jp01B2r4_c14 jp01B2r4_c15
            )
          )
        )
      ) (
        cond (Nat.blt c 24) (
          cond (Nat.blt c 20) (
            cond (Nat.blt c 18) (
              cond (Nat.blt c 17) jp01B2r4_c16 jp01B2r4_c17
            ) (
              cond (Nat.blt c 19) jp01B2r4_c18 jp01B2r4_c19
            )
          ) (
            cond (Nat.blt c 22) (
              cond (Nat.blt c 21) jp01B2r4_c20 jp01B2r4_c21
            ) (
              cond (Nat.blt c 23) jp01B2r4_c22 jp01B2r4_c23
            )
          )
        ) (
          cond (Nat.blt c 28) (
            cond (Nat.blt c 26) (
              cond (Nat.blt c 25) jp01B2r4_c24 jp01B2r4_c25
            ) (
              cond (Nat.blt c 27) jp01B2r4_c26 jp01B2r4_c27
            )
          ) (
            cond (Nat.blt c 30) (
              cond (Nat.blt c 29) jp01B2r4_c28 jp01B2r4_c29
            ) (
              cond (Nat.blt c 31) jp01B2r4_c30 jp01B2r4_c31
            )
          )
        )
      )
    jp01ListGet L rem
private def jp01Bin_2_r4 (j : ℕ) : M2BinCert :=
  PipeFuseCert.withForcedNat j fun j =>
    jp01UnpackBinR4C jp01W_2_r3 j (jp01Slot (jp01B2r4Get (j / 16)) 131072 (j % 16))
private def jp01Bin_2 (r j : ℕ) : M2BinCert :=
  PipeFuseCert.withForcedNat r fun r =>
    cond (_nEq r 3) (jp01Bin_2_r3 j) (jp01Bin_2_r4 j)
private def jp01RSeg (p : ℕ → Bool) (lo cnt : ℕ) : Bool :=
  match cnt with
  | 0 => true
  | k + 1 => jp01RSeg p lo k && p (lo + k)
private theorem jp01AllR_add {p : ℕ → Bool} {a b : ℕ}
    (ha : PipeFuseCert.allRange p a = true) (hb : jp01RSeg p a b = true) :
    PipeFuseCert.allRange p (a + b) = true := by
  induction b with
  | zero => exact ha
  | succ k ih =>
    simp only [jp01RSeg, Bool.and_eq_true] at hb
    simp only [PipeFuseCert.allRange, Bool.and_eq_true]
    exact ⟨ih hb.1, hb.2⟩
private theorem jp01AllR_zero {p : ℕ → Bool} {b : ℕ} (hb : jp01RSeg p 0 b = true) :
    PipeFuseCert.allRange p b = true := by
  have h := jp01AllR_add (a := 0) (b := b) rfl hb; rwa [Nat.zero_add] at h
private theorem jp01AllR_step {p : ℕ → Bool} {a b c : ℕ} (hc : a + b = c)
    (ha : PipeFuseCert.allRange p a = true) (hb : jp01RSeg p a b = true) :
    PipeFuseCert.allRange p c = true := hc ▸ jp01AllR_add ha hb
private theorem jp01AllR_and {p q : ℕ → Bool} {n : ℕ}
    (h : PipeFuseCert.allRange (fun j => p j && q j) n = true) :
    PipeFuseCert.allRange p n = true ∧ PipeFuseCert.allRange q n = true := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [PipeFuseCert.allRange, Bool.and_eq_true] at h ⊢
    exact ⟨⟨(ih h.1).1, h.2.1⟩, ⟨(ih h.1).2, h.2.2⟩⟩
private def jp01P3 (j : ℕ) : Bool :=
  checkM2KnotSlope 26549420 (jp01W_2 3) j &&
  checkWarmJP01Stage3Bin jp01B_2 93800 753417326848 26549420 warmJP01V2Mono
    (jp01W_2 3) (jp01Bin_2 3 j) j
private def jp01P4 (j : ℕ) : Bool :=
  checkM2KnotSlope 22890529 (jp01W_2 4) j &&
  checkWarm2StageGe3Bin jp01B_2 4 93174 750076841337 22890529
    93800 753417326850 26549420 217502903232 (jp01W_2 4) (jp01W_2 3) (jp01Bin_2 4 j) j
private def jp01P34 (j : ℕ) : Bool := jp01P3 j && jp01P4 j
private theorem _jp01Seg_0 : jp01RSeg jp01P34 0 631 = true := by
  decide +kernel
private theorem _jp01Seg_1 : jp01RSeg jp01P34 631 631 = true := by
  decide +kernel
private theorem _jp01Seg_2 : jp01RSeg jp01P34 1262 631 = true := by
  decide +kernel
private theorem _jp01Seg_3 : jp01RSeg jp01P34 1893 631 = true := by
  decide +kernel
private theorem _jp01Seg_4 : jp01RSeg jp01P34 2524 631 = true := by
  decide +kernel
private theorem _jp01Seg_5 : jp01RSeg jp01P34 3155 631 = true := by
  decide +kernel
private theorem _jp01Seg_6 : jp01RSeg jp01P34 3786 631 = true := by
  decide +kernel
private theorem _jp01Seg_7 : jp01RSeg jp01P34 4417 631 = true := by
  decide +kernel
private theorem _jp01Seg_8 : jp01RSeg jp01P34 5048 631 = true := by
  decide +kernel
private theorem _jp01Seg_9 : jp01RSeg jp01P34 5679 631 = true := by
  decide +kernel
private theorem _jp01Seg_10 : jp01RSeg jp01P34 6310 631 = true := by
  decide +kernel
private theorem _jp01Seg_11 : jp01RSeg jp01P34 6941 631 = true := by
  decide +kernel
private theorem _jp01Seg_12 : jp01RSeg jp01P34 7572 620 = true := by
  decide +kernel
private theorem cert_jp01P34 : PipeFuseCert.allRange jp01P34 jp01B_2 = true := by
  have h0 := jp01AllR_zero _jp01Seg_0
  have h1 := jp01AllR_step (c := 1262) rfl h0 _jp01Seg_1
  have h2 := jp01AllR_step (c := 1893) rfl h1 _jp01Seg_2
  have h3 := jp01AllR_step (c := 2524) rfl h2 _jp01Seg_3
  have h4 := jp01AllR_step (c := 3155) rfl h3 _jp01Seg_4
  have h5 := jp01AllR_step (c := 3786) rfl h4 _jp01Seg_5
  have h6 := jp01AllR_step (c := 4417) rfl h5 _jp01Seg_6
  have h7 := jp01AllR_step (c := 5048) rfl h6 _jp01Seg_7
  have h8 := jp01AllR_step (c := 5679) rfl h7 _jp01Seg_8
  have h9 := jp01AllR_step (c := 6310) rfl h8 _jp01Seg_9
  have h10 := jp01AllR_step (c := 6941) rfl h9 _jp01Seg_10
  have h11 := jp01AllR_step (c := 7572) rfl h10 _jp01Seg_11
  exact jp01AllR_step (c := jp01B_2) rfl h11 _jp01Seg_12
private theorem _cS3W :
    PipeFuseCert.allRange (checkM2KnotSlope 26549420 (jp01W_2 3)) jp01B_2 = true :=
  (jp01AllR_and (jp01AllR_and cert_jp01P34).1).1
private theorem _cS3B :
    PipeFuseCert.allRange (fun j => checkWarmJP01Stage3Bin jp01B_2 93800 753417326848
      26549420 warmJP01V2Mono (jp01W_2 3) (jp01Bin_2 3 j) j) jp01B_2 = true :=
  (jp01AllR_and (jp01AllR_and cert_jp01P34).1).2
private theorem _cS4W :
    PipeFuseCert.allRange (checkM2KnotSlope 22890529 (jp01W_2 4)) jp01B_2 = true :=
  (jp01AllR_and (jp01AllR_and cert_jp01P34).2).1
private theorem _cS4B :
    PipeFuseCert.allRange (fun j => checkWarm2StageGe3Bin jp01B_2 4 93174
      750076841337 22890529 93800 753417326850 26549420 217502903232
      (jp01W_2 4) (jp01W_2 3) (jp01Bin_2 4 j) j) jp01B_2 = true :=
  (jp01AllR_and (jp01AllR_and cert_jp01P34).2).2
private theorem _cert_warmJP01_b0 :
    (checkWarmJP01R2Table warmJP01ColdTau1 warmJP01ColdTau2 warmJP01ColdV2
       warmJP01Rows warmJP01V2Mono &&
     checkWarmJP01CellHT jp01B_2 warmJP01ColdV2 jp01St_2 jp01W_2 2
       jp01TopR_2 jp01RcNum12_2) = true := by
  decide +kernel
private def _jp01S01 : Bool :=
  checkWarmJP01StageIdx jp01B_2 warmJP01V2Mono jp01St_2 jp01W_2 jp01Bin_2 0 &&
  checkWarmJP01StageIdx jp01B_2 warmJP01V2Mono jp01St_2 jp01W_2 jp01Bin_2 1
private theorem _cert_warmJP01_s01 : _jp01S01 = true := by
  dsimp only [_jp01S01, checkWarmJP01StageIdx, checkWarmJP01Stage3, checkWarm2StageIdx]
  have h0 : ((2 : ℕ) == 0) = false := rfl; rw [jp01St_2_eq3, jp01St_2_eq4]
  dsimp only; simp only [h0, Bool.false_eq_true, ↓reduceIte, PipeFuseCert.withForcedNat_eq]
  rw [_cS3W, _cS3B, _cS4W, _cS4B]; decide +kernel
private theorem cert_warmJP01_r2Table :
    checkWarmJP01R2Table warmJP01ColdTau1 warmJP01ColdTau2 warmJP01ColdV2
      warmJP01Rows warmJP01V2Mono = true :=
  ((Bool.and_eq_true _ _).mp _cert_warmJP01_b0).1
private theorem cert_warmJP01CellHT_2 :
    checkWarmJP01CellHT jp01B_2 warmJP01ColdV2 jp01St_2 jp01W_2 2
      jp01TopR_2 jp01RcNum12_2 = true :=
  ((Bool.and_eq_true _ _).mp _cert_warmJP01_b0).2
private theorem cert_warmJP01_k2_s0 :
    checkWarmJP01StageIdx jp01B_2 warmJP01V2Mono jp01St_2 jp01W_2 jp01Bin_2 0 = true :=
  ((Bool.and_eq_true _ _).mp _cert_warmJP01_s01).1
private theorem cert_warmJP01_k2_s1 :
    checkWarmJP01StageIdx jp01B_2 warmJP01V2Mono jp01St_2 jp01W_2 jp01Bin_2 1 = true :=
  ((Bool.and_eq_true _ _).mp _cert_warmJP01_s01).2
private theorem cert_warmJP01Cell_2 :
    checkWarmJP01CellCert jp01B_2 warmJP01ColdV2 warmJP01V2Mono jp01St_2 jp01W_2 jp01Bin_2
      2 jp01TopR_2 jp01RcNum12_2 = true := by
  dsimp only [checkWarmJP01CellCert]
  refine Bool.and_eq_true_iff.2 ⟨cert_warmJP01CellHT_2, ?_⟩
  change PipeFuseCert.allRange _ 2 = true
  simp only [PipeFuseCert.allRange, cert_warmJP01_k2_s0, cert_warmJP01_k2_s1, Bool.and_self]
attribute [irreducible] warmJP01Rows
attribute [irreducible] warmJP01V2Mono
attribute [irreducible] jp01St_2
attribute [irreducible] jp01W_2
attribute [irreducible] jp01Bin_2
/-! ### Homomorphism from `SNat`/`SNIVal` to `DickeSol.WDIVal` & Trigonometric Enclosure -/
private theorem withForcedSNat_eq {α : Type} (a : SNat) (k : SNat → α) : withForcedSNat a k = k a :=
  by rcases a with ⟨b, m⟩; cases b <;> simp [withForcedSNat, PipeFuseCert.withForcedNat_eq]
private theorem withForcedSNIVal_eq {α : Type} (iv : SNIVal) (k : SNIVal → α) : withForcedSNIVal iv
  k = k iv := by rcases iv with ⟨lo, hi⟩; simp [withForcedSNIVal, withForcedSNat_eq]
private def snToInt (a : SNat) : ℤ := if a.1 then -(a.2 : ℤ) else (a.2 : ℤ)
private def snToWDIVal (iv : SNIVal) : DickeSol.WDIVal := (snToInt iv.1, snToInt iv.2)
private def snMem (x : ℝ) (iv : SNIVal) : Prop := DickeSol.wdMem x (snToWDIVal iv)
private theorem snToInt_neg (a : SNat) : snToInt (snNeg a) = -snToInt a := by
  rcases a with ⟨b, m⟩; cases b <;> simp [snNeg, snToInt]
private theorem snToInt_add (a b : SNat) : snToInt (snAdd a b) = snToInt a + snToInt b := by
  rcases a with ⟨sa, ma⟩; rcases b with ⟨sb, mb⟩; cases sa <;> cases sb
  · simp [snAdd, snToInt]
  · by_cases h : mb ≤ ma
    · have hb : Nat.ble mb ma = true := Nat.ble_eq.mpr h; simp [snAdd, snToInt, hb]; omega
    · have hb : Nat.ble mb ma = false := Bool.eq_false_iff.mpr fun hh => h (Nat.ble_eq.mp hh)
      simp [snAdd, snToInt, hb]; omega
  · by_cases h : mb ≤ ma
    · have hb : Nat.ble mb ma = true := Nat.ble_eq.mpr h; simp [snAdd, snToInt, hb]; omega
    · have hb : Nat.ble mb ma = false := Bool.eq_false_iff.mpr fun hh => h (Nat.ble_eq.mp hh)
      simp [snAdd, snToInt, hb]; omega
  · simp [snAdd, snToInt]; omega
private theorem snToInt_sub (a b : SNat) : snToInt (snSub a b) = snToInt a - snToInt b := by
  rw [snSub, snToInt_add, snToInt_neg]; ring
private theorem snToInt_mul (a b : SNat) : snToInt (snMul a b) = snToInt a * snToInt b := by
  rcases a with ⟨sa, ma⟩; rcases b with ⟨sb, mb⟩; cases sa <;> cases sb <;> simp [snMul, snToInt]
private theorem snToInt_scaleNat (c : ℕ) (a : SNat) : snToInt (snScaleNat c a) = (c : ℤ) * snToInt a
  := by rcases a with ⟨sa, ma⟩; cases sa <;> simp [snScaleNat, snToInt]
private theorem snLe_iff (a b : SNat) : snLe a b = true ↔ snToInt a ≤ snToInt b := by
  rcases a with ⟨sa, ma⟩; rcases b with ⟨sb, mb⟩; cases sa <;> cases sb <;> simp [snLe, snToInt,
    Nat.ble_eq, Bool.and_eq_true, _nEq_eq]; omega
private theorem snToInt_min (a b : SNat) : snToInt (snMin a b) = min (snToInt a) (snToInt b) := by
  dsimp only [snMin]; by_cases h : snLe a b = true
  · rw [h, Bool.cond_true, min_eq_left ((snLe_iff a b).1 h)]
  · rw [Bool.eq_false_iff.2 h, Bool.cond_false, min_eq_right (le_of_not_ge (mt (snLe_iff a b).2 h))]
private theorem snToInt_max (a b : SNat) : snToInt (snMax a b) = max (snToInt a) (snToInt b) := by
  dsimp only [snMax]; by_cases h : snLe a b = true
  · rw [h, Bool.cond_true, max_eq_right ((snLe_iff a b).1 h)]
  · rw [Bool.eq_false_iff.2 h, Bool.cond_false, max_eq_left (le_of_not_ge (mt (snLe_iff a b).2 h))]
private theorem snToInt_maxZero (a : SNat) : snToInt (snMaxZero a) = max 0 (snToInt a) := by
  rcases a with ⟨sa, ma⟩; cases sa <;> simp [snMaxZero, snZero, snToInt]
private theorem neg_nat_ediv_eq {m d : ℕ} (hd : 0 < d) : (-(m : ℤ)) / (d : ℤ) = -(((m + d - 1) / d :
  ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hlt : d - 1 < d := (by omega); simp [Nat.div_eq_of_lt hlt]
  · set q := (m - 1) / d; set r := (m - 1) % d
    have hr_lt : r < d := Nat.mod_lt _ hd; have hm1 : d * q + r = m - 1 := Nat.div_add_mod (m - 1) d
    have hdq : d * (q + 1) = d * q + d := (by ring); have hm_eq : m + d - 1 = r + d * (q + 1) :=
      (by omega); have hdiv_nat : (m + d - 1) / d = q + 1 :=
      (by rw [hm_eq, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr_lt, zero_add]); rw [hdiv_nat]
    have hneg_eq : -(m : ℤ) = ((d - 1 - r : ℕ) : ℤ) + (d : ℤ) * (-(q + 1 : ℤ)) := by
      have hm_nat : m + (d - 1 - r) = d * (q + 1) := (by omega); have hm_int : (m : ℤ) + ((d - 1 - r
        : ℕ) : ℤ) = (d : ℤ) * ((q : ℤ) + 1) := (by exact_mod_cast hm_nat); linarith
    rw [hneg_eq, Int.add_mul_ediv_left _ _ (by omega : (d : ℤ) ≠ 0)]; have hr'_lt : ((d - 1 - r : ℕ)
      : ℤ) < d := (by exact_mod_cast (by omega : d - 1 - r < d)); have hr'_nn : (0 : ℤ) ≤ ((d - 1 -
      r : ℕ) : ℤ) := Nat.cast_nonneg _; rw [Int.ediv_eq_zero_of_lt hr'_nn hr'_lt, zero_add];
      push_cast; ring
private theorem snToInt_divFloor (a : SNat) {d : ℕ} (hd : 0 < d) : snToInt (snDivFloor a d) =
  DickeSol.wdDivFloor (snToInt a) (d : ℤ) := by
  rcases a with ⟨sa, ma⟩; cases sa
  · simp [snDivFloor, snToInt, DickeSol.wdDivFloor]
  · simp only [snDivFloor, Bool.cond_true, snToInt, DickeSol.wdDivFloor]; exact (neg_nat_ediv_eq
      hd).symm
private theorem snToInt_divCeil (a : SNat) {d : ℕ} (hd : 0 < d) : snToInt (snDivCeil a d) =
  DickeSol.wdDivCeil (snToInt a) (d : ℤ) := by
  rw [snDivCeil, snToInt_neg, snToInt_divFloor _ hd, snToInt_neg]
  unfold DickeSol.wdDivCeil DickeSol.wdDivFloor; rfl
private theorem snToWDIVal_addIV (x y : SNIVal) : snToWDIVal (snAddIV x y) = DickeSol.wdAdd
  (snToWDIVal x) (snToWDIVal y) := by
  simp [snAddIV, withForcedSNat_eq, snToWDIVal, DickeSol.wdAdd, snToInt_add]
private theorem snToWDIVal_subIV (x y : SNIVal) : snToWDIVal (snSubIV x y) = DickeSol.wdSub
  (snToWDIVal x) (snToWDIVal y) := by
  simp [snSubIV, withForcedSNat_eq, snToWDIVal, DickeSol.wdSub, snToInt_sub]
private theorem snToWDIVal_scaleNatIV (c : ℕ) (x : SNIVal) : snToWDIVal (snScaleNatIV c x) =
  DickeSol.wdScaleNat c (snToWDIVal x) := by
  simp [snScaleNatIV, withForcedSNat_eq, snToWDIVal, DickeSol.wdScaleNat, snToInt_scaleNat]
private theorem jp01Scale_eq_wdScale : (jp01Scale : ℤ) = (DickeSol.wdScale : ℤ) := rfl
private theorem jp01WdScaleR_eq : DickeSol.wdScaleR = 1000000000000000 := by
  unfold DickeSol.wdScaleR DickeSol.wdScale; norm_num
private theorem jp01WdScaleR_pos : 0 < DickeSol.wdScaleR := by rw [jp01WdScaleR_eq]; norm_num
private theorem snToWDIVal_mulIV (x y : SNIVal) : snToWDIVal (snMulIV x y) = DickeSol.wdMul
  (snToWDIVal x) (snToWDIVal y) := by
  have hd : 0 < jp01Scale := (by norm_num [jp01Scale]); simp only [snMulIV, withForcedSNat_eq,
    snToWDIVal, DickeSol.wdMul, snToInt_divFloor _ hd, snToInt_divCeil _ hd, snToInt_min,
    snToInt_max, snToInt_mul, jp01Scale_eq_wdScale]
private theorem snToWDIVal_sqIV (x : SNIVal) : snToWDIVal (snSqIV x) = DickeSol.wdSq (snToWDIVal x)
  := by
  have hd : 0 < jp01Scale := (by norm_num [jp01Scale]); dsimp only [snSqIV, DickeSol.wdSq,
    snToWDIVal]; simp only [withForcedSNat_eq, snToInt_divCeil _ hd, snToInt_max, snToInt_mul,
    jp01Scale_eq_wdScale]; apply Prod.ext
  · split_ifs with hz
    · have hb : (snLe x.1 snZero && snLe snZero x.2) = true :=
        (by rw [Bool.and_eq_true, snLe_iff, snLe_iff]; simpa [snZero, snToInt] using hz); rw [hb,
        Bool.cond_true]; rfl
    · have hb : (snLe x.1 snZero && snLe snZero x.2) = false := by
        rw [Bool.eq_false_iff]; intro ht; rw [Bool.and_eq_true, snLe_iff, snLe_iff] at ht
        exact hz (by simpa [snZero, snToInt] using ht)
      rw [hb, Bool.cond_false, snToInt_divFloor _ hd, snToInt_min, snToInt_mul, snToInt_mul,
        jp01Scale_eq_wdScale]
  · rfl
private theorem snToWDIVal_trigBase (u : SNIVal) : (snToWDIVal (snTrigBase u).1, snToWDIVal
  (snTrigBase u).2) = DickeSol.wdTrigBase (snToWDIVal u) := by
  have hB : 0 < jp01Scale := (by norm_num [jp01Scale]); have h2B : 0 < 2 * jp01Scale :=
    (by norm_num [jp01Scale]); simp only [snTrigBase, withForcedSNat_eq, snToWDIVal,
    DickeSol.wdTrigBase, snToInt_add, snToInt_sub, snToInt_maxZero, snToInt_divFloor _ hB,
    snToInt_divCeil _ hB, snToInt_divFloor _ h2B, snToInt_divCeil _ h2B, snToInt_divCeil _
    (by norm_num : 0 < 24), snToInt_divCeil _ (by norm_num : 0 < 6), snToInt_divFloor _
    (by norm_num : 0 < 6), snToInt_divCeil _ (by norm_num : 0 < 120), snToInt_mul]; rfl
private theorem snToWDIVal_doubleAngleIter : ∀ (k : ℕ) (cs : SNIVal × SNIVal), (snToWDIVal
  (snDoubleAngleIter k cs).1, snToWDIVal (snDoubleAngleIter k cs).2) = DickeSol.wdDoubleAngleIter k
  (snToWDIVal cs.1, snToWDIVal cs.2)
  | 0, cs => rfl
  | k + 1, (c, s) => by
    simp only [snDoubleAngleIter, withForcedSNIVal_eq, DickeSol.wdDoubleAngleIter]
    rw [snToWDIVal_doubleAngleIter k]; simp only [snToWDIVal_subIV, snToWDIVal_sqIV,
      snToWDIVal_scaleNatIV, snToWDIVal_mulIV]
private theorem snToWDIVal_trig (x : SNIVal) : (snToWDIVal (snTrig x).1, snToWDIVal (snTrig x).2) =
  DickeSol.wdTrig (snToWDIVal x) := by
  have h1024 : 0 < (1024 : ℕ) := (by norm_num); have hu : snToWDIVal (snDivFloor x.1 1024, snDivCeil
    x.2 1024) = (DickeSol.wdDivFloor (snToWDIVal x).1 1024, DickeSol.wdDivCeil (snToWDIVal x).2
    1024) := Prod.ext (snToInt_divFloor x.1 h1024) (snToInt_divCeil x.2 h1024); dsimp only [snTrig,
    DickeSol.wdTrig]; simp only [withForcedSNat_eq]; rw [snToWDIVal_doubleAngleIter,
    snToWDIVal_trigBase, hu]
private theorem snTrig_mem {x : ℝ} {iv : SNIVal} (h0 : 0 ≤ (snToWDIVal iv).1) (hhi : (snToWDIVal
  iv).2 ≤ 1024 * (DickeSol.wdScale : ℤ)) (hx : snMem x iv) : snMem (Real.cos x) (snTrig iv).1 ∧
  snMem (Real.sin x) (snTrig iv).2 := by
  unfold snMem at hx ⊢; have h1 : snToWDIVal (snTrig iv).1 = (DickeSol.wdTrig (snToWDIVal iv)).1 :=
    congrArg Prod.fst (snToWDIVal_trig iv); have h2 : snToWDIVal (snTrig iv).2 = (DickeSol.wdTrig
    (snToWDIVal iv)).2 := congrArg Prod.snd (snToWDIVal_trig iv)
  rw [h1, h2]; exact DickeSol.wdTrig_mem h0 hhi hx
private theorem snMem_add {x y : ℝ} {ix iy : SNIVal} (hx : snMem x ix) (hy : snMem y iy) : snMem (x
  + y) (snAddIV ix iy) := by
  unfold snMem at hx hy ⊢; rw [snToWDIVal_addIV]; exact DickeSol.wdMem_add hx hy
private theorem snMem_sub {x y : ℝ} {ix iy : SNIVal} (hx : snMem x ix) (hy : snMem y iy) : snMem (x
  - y) (snSubIV ix iy) := by
  unfold snMem at hx hy ⊢; rw [snToWDIVal_subIV]; exact DickeSol.wdMem_sub hx hy
private theorem snMem_scaleNat (c : ℕ) {x : ℝ} {ix : SNIVal} (hx : snMem x ix) : snMem ((c : ℝ) * x)
  (snScaleNatIV c ix) := by
  unfold snMem at hx ⊢; rw [snToWDIVal_scaleNatIV]; exact DickeSol.wdMem_scaleNat c hx
private theorem snMem_mul {x y : ℝ} {ix iy : SNIVal} (hx : snMem x ix) (hy : snMem y iy) : snMem (x
  * y) (snMulIV ix iy) := by
  unfold snMem at hx hy ⊢; rw [snToWDIVal_mulIV]; exact DickeSol.wdMem_mul hx hy
private theorem snMem_sq {x : ℝ} {ix : SNIVal} (hx : snMem x ix) : snMem (x ^ 2) (snSqIV ix) := by
  unfold snMem at hx ⊢; rw [snToWDIVal_sqIV]; exact DickeSol.wdMem_sq hx
private theorem snDiv_nat_mem {x : ℝ} {iv : SNIVal} {d : ℕ} (hd : 0 < d) (hx : snMem x iv) : snMem
  (x / (d : ℝ)) (snDivFloor iv.1 d, snDivCeil iv.2 d) := by
  unfold snMem DickeSol.wdMem at hx ⊢; simp only [snToWDIVal, snToInt_divFloor _ hd, snToInt_divCeil
    _ hd]; have hB : 0 < DickeSol.wdScaleR := jp01WdScaleR_pos; have hdR : (0 : ℝ) < d :=
    Nat.cast_pos.mpr hd; have hdZ : (0 : ℤ) < (d : ℤ) := Nat.cast_pos.mpr hd; constructor
  · calc ((DickeSol.wdDivFloor (snToInt iv.1) (d : ℤ) : ℝ) / DickeSol.wdScaleR)
        ≤ (((snToInt iv.1 : ℝ) / (d : ℝ)) / DickeSol.wdScaleR) :=
          div_le_div_of_nonneg_right (DickeSol.wdDivFloor_le hdZ) hB.le
      _ = ((snToInt iv.1 : ℝ) / DickeSol.wdScaleR) / (d : ℝ) := div_right_comm _ _ _
      _ ≤ x / (d : ℝ) := div_le_div_of_nonneg_right hx.1 hdR.le
  · calc x / (d : ℝ) ≤ ((snToInt iv.2 : ℝ) / DickeSol.wdScaleR) / (d : ℝ) :=
      div_le_div_of_nonneg_right hx.2 hdR.le
      _ = (((snToInt iv.2 : ℝ) / (d : ℝ)) / DickeSol.wdScaleR) := (div_right_comm _ _ _).symm
      _ ≤ ((DickeSol.wdDivCeil (snToInt iv.2) (d : ℤ) : ℝ) / DickeSol.wdScaleR) :=
          div_le_div_of_nonneg_right (DickeSol.le_wdDivCeil hdZ) hB.le
/-! ### Finite-`N` (`200 ≤ n`) `m = 2, r = 2` Jordan Basis & Walk Enclosure -/
private theorem pow_two_200_bounds {n : ℕ} (hn : 200 ≤ n) : (2 : ℝ) ^ 100 ≤ √((2 : ℝ) ^ n) ∧ (2 : ℝ)
  ^ 200 ≤ (2 : ℝ) ^ n := by
  have hN : (2 : ℝ) ^ 200 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn; refine ⟨?_, hN⟩
  have hsq : ((2 : ℝ) ^ 100) ^ 2 ≤ (2 : ℝ) ^ n := by
    calc ((2 : ℝ) ^ 100) ^ 2 = (2 : ℝ) ^ 200 := by norm_num
      _ ≤ (2 : ℝ) ^ n := hN
  simpa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 100)] using Real.sqrt_le_sqrt hsq
private lemma abs_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |√a - √b| ≤ |a - b| / √b := by
  have hsum_pos : 0 < √a + √b := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg a) (Real.sqrt_pos.2 hb)
  have hprod : (√a - √b) * (√a + √b) = a - b := (by nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb.le])
  have habs : |√a - √b| * (√a + √b) = |a - b| := (by rw [← abs_of_pos hsum_pos, ← abs_mul, hprod])
  rw [le_div_iff₀ (Real.sqrt_pos.2 hb), ← habs]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg a)) (abs_nonneg _)
private lemma arcsin_approx_small {s : ℝ} (hs0 : 0 ≤ s) (hs_hi : s ≤ 1 / 4) : s ≤ Real.arcsin s ∧
  Real.arcsin s ≤ s + s ^ 3 := by
  have hs1 : s ≤ 1 := (by linarith)
  have hsin_arc : Real.sin (Real.arcsin s) = s := Real.sin_arcsin (by linarith) hs1
  have harc_nn : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.2 hs0; refine ⟨?_, ?_⟩
  · have h := Real.sin_le harc_nn; rwa [hsin_arc] at h
  · set u : ℝ := s + s ^ 3; have hu0 : 0 ≤ u := (by dsimp [u]; positivity)
    have hu_pi2 : u ≤ π / 2 := by
      dsimp [u]; have : s ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hs0 hs_hi 3
      linarith [Real.pi_gt_three]
    suffices hle : s ≤ Real.sin u by
      have hm := Real.arcsin_le_arcsin hle
      rwa [Real.arcsin_sin (by linarith [Real.pi_gt_three]) hu_pi2] at hm
    rcases hs0.eq_or_lt with rfl | hs_pos
    · simp [u]
    · have hu_pos : 0 < u := (by dsimp [u]; positivity); have hdeg3 : u - u ^ 3 / 6 < Real.sin u :=
        Real.sin_gt_sub_cube hu_pos; have hu_le : u ≤ (17 / 16) * s :=
        (by dsimp [u]; have hs2 : s ^ 2 ≤ 1 / 16 := (by nlinarith); nlinarith)
      have hu3_le : u ^ 3 ≤ 6 * s ^ 3 := by
        have hp := pow_le_pow_left₀ hu0 hu_le 3
        linarith [hp, show ((17 / 16 : ℝ) * s) ^ 3 = ((17 / 16 : ℝ) ^ 3) * s ^ 3 by ring,
          show (17 / 16 : ℝ) ^ 3 ≤ 6 by norm_num, pow_pos hs_pos 3]
      dsimp [u] at hdeg3; linarith
private lemma nat_choose_two_real {M : ℕ} (hM : 2 ≤ M) : (M.choose 2 : ℝ) = ((M : ℝ) * ((M : ℝ) -
  1)) / 2 := by
  have h2 := Nat.choose_two_right M; have hmul : 2 * M.choose 2 = M * (M - 1) :=
    (by rw [h2]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self M).two_dvd)
  have hR : (2 : ℝ) * (M.choose 2 : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    have hc : ((2 * M.choose 2 : ℕ) : ℝ) = ((M * (M - 1) : ℕ) : ℝ) := (by exact_mod_cast hmul)
    simpa [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M)] using hc
  linarith
private theorem jp01_m2r2_basis_closed {N : ℕ} (hN : 16 ≤ N) :
    let u1 := DickeSol.u1OrbVec N 2 2; let u2 := DickeSol.u2OrbVec N 2 2
    let s1 := √((u1 0) ^ 2 + (u1 2) ^ 2); let s2 := √((u2 0) ^ 2 + (u2 2) ^ 2)
    DickeSol.dot3 u1 u1 = 1 ∧ DickeSol.dot3 u2 u2 = 1 ∧ 0 ≤ u1 1 ∧ u2 1 ≤ 0 ∧ 0 < s1 ∧ 0 < s2 ∧ s1 ^
      2 = (6 * (N : ℝ) - 16) / ((N : ℝ) * ((N : ℝ) - 2)) ∧ u1 0 / s1 = -2 * √(((N : ℝ) - 3) / (6 *
      (N : ℝ) - 16)) ∧ u1 2 / s1 = √((2 * ((N : ℝ) - 2)) / (6 * (N : ℝ) - 16)) ∧ (-u2 1) = √((2 *
      ((N : ℝ) - 3)) / (((N : ℝ) - 1) * ((N : ℝ) - 2))) ∧ u2 0 = √(2 / (((N : ℝ) - 1) * ((N : ℝ) -
      2))) ∧ u2 2 = √(((N : ℝ) - 3) / ((N : ℝ) - 1)) := by
  intro u1 u2 s1 s2; let u0 := DickeSol.u0OrbVec N 2 2
  have hNR : (16 : ℝ) ≤ (N : ℝ) := (by exact_mod_cast hN); have hN0 : (0 : ℝ) < N :=
    (by linarith only [hNR]); have hN1 : (0 : ℝ) < (N : ℝ) - 1 := (by linarith only [hNR])
  have hN2 : (0 : ℝ) < (N : ℝ) - 2 := (by linarith only [hNR]); have hN3 : (0 : ℝ) < (N : ℝ) - 3 :=
    (by linarith only [hNR]); have hN4 : (0 : ℝ) ≤ (N : ℝ) - 4 := (by linarith only [hNR])
  have h6N16 : (0 : ℝ) < 6 * (N : ℝ) - 16 := (by linarith only [hNR])
  have hNN2 : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 2) := mul_pos hN0 hN2
  have hdu0 : DickeSol.dot3 u0 u0 = 1 := DickeSol.dot3_u0_self (by norm_num) (by norm_num)
    (by norm_num) (by omega)
  have hdu1 : DickeSol.dot3 u1 u1 = 1 := DickeSol.dot3_u1_self (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by omega)
  have hdu01 : DickeSol.dot3 u0 u1 = 0 := DickeSol.dot3_u0_u1 (by norm_num) (by norm_num)
    (by norm_num) (by omega)
  have hdu2 : DickeSol.dot3 u2 u2 = 1 := DickeSol.dot3_cross3_self hdu0 hdu1 hdu01
  have horb0 : (DickeSol.orbCard N 2 2 0 : ℝ) = (((N : ℝ) - 2) * ((N : ℝ) - 3)) / 2 := by
    unfold DickeSol.orbCard; simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero]
    rw [nat_choose_two_real (by omega), Nat.cast_sub (by omega : 2 ≤ N)]; ring
  have horb1 : (DickeSol.orbCard N 2 2 1 : ℝ) = 2 * ((N : ℝ) - 2) := by
    unfold DickeSol.orbCard; rw [show (2 : ℕ).choose 1 = 2 from rfl, show 2 - 1 = 1 from rfl,
      Nat.choose_one_right, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ N)]; push_cast; rfl
  have horb2 : (DickeSol.orbCard N 2 2 2 : ℝ) = 1 := (by unfold DickeSol.orbCard; simp)
  have hchN2 : (N.choose 2 : ℝ) = ((N : ℝ) * ((N : ℝ) - 1)) / 2 := nat_choose_two_real (by omega)
  have hchNm2 : ((N - 2).choose 1 : ℝ) = (N : ℝ) - 2 :=
    (by simp [Nat.choose_one_right, Nat.cast_sub (by omega : 2 ≤ N)])
  have hu0_0 : u0 0 = √((((N : ℝ) - 2) * ((N : ℝ) - 3)) / ((N : ℝ) * ((N : ℝ) - 1))) :=
    (by dsimp only [u0, DickeSol.u0OrbVec]; rw [Fin.val_zero, horb0, hchN2]; congr 1; field_simp)
  have hu0_1 : u0 1 = √((4 * ((N : ℝ) - 2)) / ((N : ℝ) * ((N : ℝ) - 1))) := by
    dsimp only [u0, DickeSol.u0OrbVec]; rw [Fin.val_one, horb1, hchN2]; congr 1; field_simp; ring
  have hu0_2 : u0 2 = √(2 / ((N : ℝ) * ((N : ℝ) - 1))) :=
    (by dsimp only [u0, DickeSol.u0OrbVec]; rw [Fin.val_two, horb2, hchN2]; congr 1; field_simp)
  have hden1 : (((N - 2).choose (2 - 1) : ℝ) * (2 : ℕ) * ((N - 2 : ℕ) : ℝ) * (N : ℝ)) = 2 * (N : ℝ)
    * ((N : ℝ) - 2) ^ 2 :=
    (by rw [show 2 - 1 = 1 from rfl, hchNm2, Nat.cast_sub (by omega : 2 ≤ N), Nat.cast_ofNat]; ring)
  have hu1_0 : u1 0 = -2 * √(((N : ℝ) - 3) / ((N : ℝ) * ((N : ℝ) - 2))) := by
    dsimp only [u1, DickeSol.u1OrbVec]; rw [Fin.val_zero, horb0, hden1]; simp only [Nat.cast_zero,
      zero_mul, Nat.cast_ofNat]; have hrad : ((((N : ℝ) - 2) * ((N : ℝ) - 3) / 2) / (2 * (N : ℝ) *
      ((N : ℝ) - 2) ^ 2)) = ((1 / 2 : ℝ) ^ 2) * (((N : ℝ) - 3) / ((N : ℝ) * ((N : ℝ) - 2))) :=
      (by field_simp [hN2.ne', hN0.ne']); rw [hrad, Real.sqrt_mul (by positivity), Real.sqrt_sq
      (by positivity)]; ring
  have hu1_1 : u1 1 = ((N : ℝ) - 4) / √((N : ℝ) * ((N : ℝ) - 2)) := by
    dsimp only [u1, DickeSol.u1OrbVec]; rw [Fin.val_one, horb1, hden1]; simp only [Nat.cast_one,
      one_mul, Nat.cast_ofNat]
    have hrad : (2 * ((N : ℝ) - 2)) / (2 * (N : ℝ) * ((N : ℝ) - 2) ^ 2) = 1 / ((N : ℝ) * ((N : ℝ) -
      2)) := (by field_simp [hN2.ne', hN0.ne']); rw [hrad, Real.sqrt_div zero_le_one, Real.sqrt_one,
      mul_one_div]; ring
  have hu1_2 : u1 2 = √(2 / (N : ℝ)) := by
    dsimp only [u1, DickeSol.u1OrbVec]; rw [Fin.val_two, horb2, hden1]; simp only [Nat.cast_ofNat]
    have hrad : 1 / (2 * (N : ℝ) * ((N : ℝ) - 2) ^ 2) = ((1 / (2 * ((N : ℝ) - 2))) ^ 2) * (2 / (N :
      ℝ)) := (by field_simp [hN2.ne', hN0.ne']); rw [hrad, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]; field_simp [hN2.ne']
  have hs1_sq : s1 ^ 2 = (6 * (N : ℝ) - 16) / ((N : ℝ) * ((N : ℝ) - 2)) := by
    dsimp only [s1]
    have hnn3 : (0 : ℝ) ≤ ((N : ℝ) - 3) / ((N : ℝ) * ((N : ℝ) - 2)) := div_nonneg hN3.le hNN2.le
    rw [Real.sq_sqrt (by positivity), hu1_0, hu1_2, mul_pow, Real.sq_sqrt hnn3, Real.sq_sqrt
      (by positivity), ← mul_div_assoc, div_add_div _ _ hNN2.ne' hN0.ne', div_eq_div_iff
      (mul_ne_zero hNN2.ne' hN0.ne') hNN2.ne']; ring
  have hs1_pos : 0 < s1 := by
    dsimp only [s1]; apply Real.sqrt_pos.2; rw [hu1_2]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (Real.sqrt_pos.2 (div_pos
      (by norm_num) hN0)))
  have hu1_1_nn : 0 ≤ u1 1 := (by rw [hu1_1]; exact div_nonneg hN4 (Real.sqrt_nonneg _))
  have hu1_0_div : u1 0 / s1 = -2 * √(((N : ℝ) - 3) / (6 * (N : ℝ) - 16)) := by
    have hs1_eq : s1 = √((6 * (N : ℝ) - 16) / ((N : ℝ) * ((N : ℝ) - 2))) :=
      (by rw [← Real.sqrt_sq hs1_pos.le, hs1_sq]); rw [hu1_0, hs1_eq, mul_div_assoc, ← Real.sqrt_div
      (div_nonneg hN3.le hNN2.le)]; congr 2; field_simp [hN2.ne', hN0.ne', h6N16.ne']
  have hu1_2_div : u1 2 / s1 = √((2 * ((N : ℝ) - 2)) / (6 * (N : ℝ) - 16)) := by
    have hs1_eq : s1 = √((6 * (N : ℝ) - 16) / ((N : ℝ) * ((N : ℝ) - 2))) :=
      (by rw [← Real.sqrt_sq hs1_pos.le, hs1_sq]); rw [hu1_2, hs1_eq, ← Real.sqrt_div
      (by positivity)]; congr 1; field_simp [hN2.ne', hN0.ne', h6N16.ne']
  have hu2_0 : u2 0 = √(2 / (((N : ℝ) - 1) * ((N : ℝ) - 2))) := by
    have h_u20 : u2 0 = u0 1 * u1 2 - u0 2 * u1 1 := rfl; rw [h_u20, hu0_1, hu1_2, hu0_2, hu1_1]
    have ht1 : √((4 * ((N : ℝ) - 2)) / ((N : ℝ) * ((N : ℝ) - 1))) * √(2 / (N : ℝ)) = (2 * ((N : ℝ) -
      2) / (N : ℝ)) * √(2 / (((N : ℝ) - 1) * ((N : ℝ) - 2))) := by
      have hl : (0 : ℝ) ≤ √((4 * ((N : ℝ) - 2)) / ((N : ℝ) * ((N : ℝ) - 1))) * √(2 / (N : ℝ)) :=
        (by positivity); have hr : (0 : ℝ) ≤ (2 * ((N : ℝ) - 2) / (N : ℝ)) * √(2 / (((N : ℝ) - 1) *
        ((N : ℝ) - 2))) := (by positivity); rw [← Real.sqrt_sq hl, ← Real.sqrt_sq hr]; congr 1
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt
        (by positivity), div_pow, div_mul_div_comm, div_mul_div_comm, div_eq_div_iff (by positivity)
        (by positivity)]; ring
    have ht2 : √(2 / ((N : ℝ) * ((N : ℝ) - 1))) * (((N : ℝ) - 4) / √((N : ℝ) * ((N : ℝ) - 2))) =
      (((N : ℝ) - 4) / (N : ℝ)) * √(2 / (((N : ℝ) - 1) * ((N : ℝ) - 2))) := by
      have hl : (0 : ℝ) ≤ √(2 / ((N : ℝ) * ((N : ℝ) - 1))) * (((N : ℝ) - 4) / √((N : ℝ) * ((N : ℝ) -
        2))) := mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hN4 (Real.sqrt_nonneg _))
      have hr : (0 : ℝ) ≤ (((N : ℝ) - 4) / (N : ℝ)) * √(2 / (((N : ℝ) - 1) * ((N : ℝ) - 2))) :=
        mul_nonneg (div_nonneg hN4 hN0.le) (Real.sqrt_nonneg _); rw [← Real.sqrt_sq hl, ←
        Real.sqrt_sq hr]; congr 1; rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by positivity),
        Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; field_simp [hN0.ne', hN1.ne',
        hN2.ne']
    rw [ht1, ht2]; have hcoef : 2 * ((N : ℝ) - 2) / (N : ℝ) - ((N : ℝ) - 4) / (N : ℝ) = 1 :=
      (by rw [← sub_div, div_eq_iff hN0.ne']; ring)
    linear_combination √(2 / (((N : ℝ) - 1) * ((N : ℝ) - 2))) * hcoef
  have hu2_1 : -u2 1 = √((2 * ((N : ℝ) - 3)) / (((N : ℝ) - 1) * ((N : ℝ) - 2))) := by
    have h_u21 : -u2 1 = -(u0 2 * u1 0 - u0 0 * u1 2) := rfl; rw [h_u21, hu0_2, hu1_0, hu0_0, hu1_2]
    have ht1 : √((((N : ℝ) - 2) * ((N : ℝ) - 3)) / ((N : ℝ) * ((N : ℝ) - 1))) * √(2 / (N : ℝ)) =
      (((N : ℝ) - 2) / (N : ℝ)) * √((2 * ((N : ℝ) - 3)) / (((N : ℝ) - 1) * ((N : ℝ) - 2))) := by
      have hl : (0 : ℝ) ≤ √((((N : ℝ) - 2) * ((N : ℝ) - 3)) / ((N : ℝ) * ((N : ℝ) - 1))) * √(2 / (N
        : ℝ)) := (by positivity); have hr : (0 : ℝ) ≤ (((N : ℝ) - 2) / (N : ℝ)) * √((2 * ((N : ℝ) -
        3)) / (((N : ℝ) - 1) * ((N : ℝ) - 2))) := (by positivity); rw [← Real.sqrt_sq hl, ←
        Real.sqrt_sq hr]; congr 1; rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt
        (by positivity), Real.sq_sqrt (by positivity), div_pow, div_mul_div_comm, div_mul_div_comm,
        div_eq_div_iff (by positivity) (by positivity)]; ring
    have ht2 : √(2 / ((N : ℝ) * ((N : ℝ) - 1))) * (-2 * √(((N : ℝ) - 3) / ((N : ℝ) * ((N : ℝ) -
      2)))) = -(2 / (N : ℝ)) * √((2 * ((N : ℝ) - 3)) / (((N : ℝ) - 1) * ((N : ℝ) - 2))) := by
      have hl : (0 : ℝ) ≤ √(2 / ((N : ℝ) * ((N : ℝ) - 1))) * (2 * √(((N : ℝ) - 3) / ((N : ℝ) * ((N :
        ℝ) - 2)))) := (by positivity); have hr : (0 : ℝ) ≤ (2 / (N : ℝ)) * √((2 * ((N : ℝ) - 3)) /
        (((N : ℝ) - 1) * ((N : ℝ) - 2))) := (by positivity)
      have hpos_eq : √(2 / ((N : ℝ) * ((N : ℝ) - 1))) * (2 * √(((N : ℝ) - 3) / ((N : ℝ) * ((N : ℝ) -
        2)))) = (2 / (N : ℝ)) * √((2 * ((N : ℝ) - 3)) / (((N : ℝ) - 1) * ((N : ℝ) - 2))) := by
        rw [← Real.sqrt_sq hl, ← Real.sqrt_sq hr]; congr 1; rw [mul_pow, mul_pow, mul_pow, div_pow,
          Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
          ← mul_div_assoc (2 ^ 2), div_mul_div_comm, div_mul_div_comm, div_eq_div_iff
          (by positivity) (by positivity)]; ring
      linarith only [hpos_eq]
    rw [ht2, ht1]; have hcoef : ((N : ℝ) - 2) / (N : ℝ) + 2 / (N : ℝ) = 1 :=
      (by rw [← add_div, div_eq_iff hN0.ne']; ring)
    linear_combination √((2 * ((N : ℝ) - 3)) / (((N : ℝ) - 1) * ((N : ℝ) - 2))) * hcoef
  have hu2_2 : u2 2 = √(((N : ℝ) - 3) / ((N : ℝ) - 1)) := by
    have h_u22 : u2 2 = u0 0 * u1 1 - u0 1 * u1 0 := rfl; rw [h_u22, hu0_0, hu1_1, hu0_1, hu1_0]
    have ht1 : √((((N : ℝ) - 2) * ((N : ℝ) - 3)) / ((N : ℝ) * ((N : ℝ) - 1))) * (((N : ℝ) - 4) /
      √((N : ℝ) * ((N : ℝ) - 2))) = (((N : ℝ) - 4) / (N : ℝ)) * √(((N : ℝ) - 3) / ((N : ℝ) - 1))
      := by
      have hl : (0 : ℝ) ≤ √((((N : ℝ) - 2) * ((N : ℝ) - 3)) / ((N : ℝ) * ((N : ℝ) - 1))) * (((N : ℝ)
        - 4) / √((N : ℝ) * ((N : ℝ) - 2))) := mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hN4
        (Real.sqrt_nonneg _)); have hr : (0 : ℝ) ≤ (((N : ℝ) - 4) / (N : ℝ)) * √(((N : ℝ) - 3) / ((N
        : ℝ) - 1)) := mul_nonneg (div_nonneg hN4 hN0.le) (Real.sqrt_nonneg _); rw [← Real.sqrt_sq
        hl, ← Real.sqrt_sq hr]; congr 1; rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt
        (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      field_simp [hN0.ne', hN1.ne', hN2.ne']
    have ht2 : √((4 * ((N : ℝ) - 2)) / ((N : ℝ) * ((N : ℝ) - 1))) * (-2 * √(((N : ℝ) - 3) / ((N : ℝ)
      * ((N : ℝ) - 2)))) = -(4 / (N : ℝ)) * √(((N : ℝ) - 3) / ((N : ℝ) - 1)) := by
      have hl : (0 : ℝ) ≤ √((4 * ((N : ℝ) - 2)) / ((N : ℝ) * ((N : ℝ) - 1))) * (2 * √(((N : ℝ) - 3)
        / ((N : ℝ) * ((N : ℝ) - 2)))) := (by positivity); have hr : (0 : ℝ) ≤ (4 / (N : ℝ)) * √(((N
        : ℝ) - 3) / ((N : ℝ) - 1)) := (by positivity)
      have hpos_eq : √((4 * ((N : ℝ) - 2)) / ((N : ℝ) * ((N : ℝ) - 1))) * (2 * √(((N : ℝ) - 3) / ((N
        : ℝ) * ((N : ℝ) - 2)))) = (4 / (N : ℝ)) * √(((N : ℝ) - 3) / ((N : ℝ) - 1)) := by
        rw [← Real.sqrt_sq hl, ← Real.sqrt_sq hr]; congr 1; rw [mul_pow, mul_pow, mul_pow, div_pow,
          Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
          ← mul_div_assoc (2 ^ 2), div_mul_div_comm, div_mul_div_comm, div_eq_div_iff
          (by positivity) (by positivity)]; ring
      linarith only [hpos_eq]
    rw [ht1, ht2]; have hcoef : ((N : ℝ) - 4) / (N : ℝ) + 4 / (N : ℝ) = 1 :=
      (by rw [← add_div, div_eq_iff hN0.ne']; ring)
    linear_combination √(((N : ℝ) - 3) / ((N : ℝ) - 1)) * hcoef
  have hu2_1_le : u2 1 ≤ 0 :=
    (by have hnn : 0 ≤ -u2 1 := (by rw [hu2_1]; exact Real.sqrt_nonneg _); linarith only [hnn])
  have hs2_pos : 0 < s2 := by
    dsimp only [s2]; apply Real.sqrt_pos.2; have hpos2 : 0 < u2 2 :=
      (by rw [hu2_2]; exact Real.sqrt_pos.2 (div_pos hN3 hN1))
    exact add_pos_of_nonneg_of_pos (sq_nonneg (u2 0)) (sq_pos_of_pos hpos2)
  exact ⟨hdu1, hdu2, hu1_1_nn, hu2_1_le, hs1_pos, hs2_pos, hs1_sq, hu1_0_div, hu1_2_div, hu2_1,
    hu2_0, hu2_2⟩
private theorem jp01_m2r2_angles_and_axes_err {n : ℕ} (hn : 200 ≤ n) :
    let N := 2 ^ n; let u1 := DickeSol.u1OrbVec N 2 2; let u2 := DickeSol.u2OrbVec N 2 2
    let s1 := √((u1 0) ^ 2 + (u1 2) ^ 2); let s2 := √((u2 0) ^ 2 + (u2 2) ^ 2)
    |Real.arcsin s1 - √6 / √((2 : ℝ) ^ n)| ≤ 32 / ((2 : ℝ) ^ n * √((2 : ℝ) ^ n)) ∧
      |Real.arcsin (-u2 1) - √2 / √((2 : ℝ) ^ n)| ≤ 32 / ((2 : ℝ) ^ n * √((2 : ℝ) ^ n)) ∧
      |(u1 0 / s1) - (-√(2 / 3 : ℝ))| ≤ 1 / √((2 : ℝ) ^ n) ∧
      |(u1 2 / s1) - √(1 / 3 : ℝ)| ≤ 1 / √((2 : ℝ) ^ n) ∧
      |u2 0 / s2| ≤ 1 / √((2 : ℝ) ^ n) ∧
      |u2 2 / s2 - 1| ≤ 1 / √((2 : ℝ) ^ n) := by
  intro N u1 u2 s1 s2; obtain ⟨hSN_ge, hN_ge⟩ := pow_two_200_bounds hn
  have hN16 : 16 ≤ N := by
    calc 16 ≤ 2 ^ 200 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by positivity) hn
  set NR : ℝ := (2 : ℝ) ^ n; have hN_cast : ((N : ℕ) : ℝ) = NR := Nat.cast_pow 2 n
  obtain ⟨_, _, _, _, hs1_pos_r, hs2_pos_r, hs1_sq_r, hu1_0_r, hu1_2_r, hu2_1_r, hu2_0_r, hu2_2_r⟩
    := jp01_m2r2_basis_closed hN16; rw [hN_cast] at hs1_sq_r hu1_0_r hu1_2_r hu2_1_r hu2_0_r hu2_2_r
  have hs1_pos : 0 < s1 := hs1_pos_r; have hs2_pos : 0 < s2 := hs2_pos_r; have hs1_sq : s1 ^ 2 = (6
    * NR - 16) / (NR * (NR - 2)) := hs1_sq_r; have hu1_0_d : u1 0 / s1 = -2 * √((NR - 3) / (6 * NR -
    16)) := hu1_0_r; have hu1_2_d : u1 2 / s1 = √((2 * (NR - 2)) / (6 * NR - 16)) := hu1_2_r
  have hu2_1 : -u2 1 = √((2 * (NR - 3)) / ((NR - 1) * (NR - 2))) := hu2_1_r; have hu2_0 : u2 0 = √(2
    / ((NR - 1) * (NR - 2))) := hu2_0_r; have hu2_2 : u2 2 = √((NR - 3) / (NR - 1)) := hu2_2_r
  clear hs1_pos_r hs2_pos_r hs1_sq_r hu1_0_r hu1_2_r hu2_1_r hu2_0_r hu2_2_r
  have hSN_pos : 0 < √NR := lt_of_lt_of_le (by positivity) hSN_ge; have hNR_pos : 0 < NR :=
    lt_of_lt_of_le (by positivity) hN_ge; have hNR16 : (16 : ℝ) ≤ NR := le_trans (by norm_num) hN_ge
  have hNR1 : 0 < NR - 1 := (by linarith only [hNR16]); have hNR2 : 0 < NR - 2 :=
    (by linarith only [hNR16]); have hNR3 : 0 < NR - 3 := (by linarith only [hNR16])
  have h6NR16 : 0 < 6 * NR - 16 := (by linarith only [hNR16]); have hNN2 : 0 < NR * (NR - 2) :=
    mul_pos hNR_pos hNR2; have hN1N2 : 0 < (NR - 1) * (NR - 2) := mul_pos hNR1 hNR2
  have hNN1N2 : 0 < NR * (NR - 1) * (NR - 2) := mul_pos (mul_pos hNR_pos hNR1) hNR2
  have hSN_le_NR : √NR ≤ NR := by
    have hm : 1 * √NR ≤ √NR * √NR := mul_le_mul_of_nonneg_right (le_trans (by norm_num) hSN_ge)
      hSN_pos.le
    rwa [one_mul, Real.mul_self_sqrt hNR_pos.le] at hm
  -- 1. `|arcsin s1 - √6 / √NR|`
  have hs1_le_3 : s1 ≤ 3 / √NR := by
    refine sq_le_imp_le hs1_pos.le (by positivity) ?_; rw [hs1_sq, div_pow, Real.sq_sqrt hNR_pos.le,
      div_le_div_iff₀ hNN2 hNR_pos]; nlinarith only [hNR16]
  have hs1_14 : s1 ≤ 1 / 4 := hs1_le_3.trans (by
    rw [div_le_div_iff₀ hSN_pos (by norm_num)]; have h12 : (12 : ℝ) ≤ (2 : ℝ) ^ 100 := (by norm_num)
    linarith only [hSN_ge, h12])
  have hs1_diff : |s1 - √6 / √NR| ≤ 4 / (NR * √NR) := by
    have hb_eq : √(6 / NR) = √6 / √NR := Real.sqrt_div (by norm_num) NR; rw [← hb_eq, ← Real.sqrt_sq
      hs1_pos.le]; refine (abs_sqrt_sub_sqrt_le (sq_nonneg s1) (div_pos (by norm_num)
      hNR_pos)).trans ?_; rw [hb_eq, hs1_sq]
    have hsub : |(6 * NR - 16) / (NR * (NR - 2)) - 6 / NR| ≤ 8 / (NR ^ 2) := by
      have heq : (6 * NR - 16) / (NR * (NR - 2)) - 6 / NR = -4 / (NR * (NR - 2)) :=
        (by field_simp [hNR_pos.ne', hNR2.ne']; ring); rw [heq, abs_div, abs_neg, abs_of_pos
        (by norm_num : (0 : ℝ) < 4), abs_of_pos hNN2, div_le_div_iff₀ hNN2 (by positivity)]
      nlinarith only [hNR16]
    have hsq6_ge : 2 / √NR ≤ √6 / √NR := div_le_div_of_nonneg_right (sq_le_imp_le (by norm_num)
      (Real.sqrt_nonneg 6) (by rw [Real.sq_sqrt (by norm_num)]; norm_num)) hSN_pos.le
    calc |(6 * NR - 16) / (NR * (NR - 2)) - 6 / NR| / (√6 / √NR) ≤ (8 / NR ^ 2) / (2 / √NR) :=
          (div_le_div_of_nonneg_right hsub (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq6_ge)
      _ = 4 / (NR * √NR) := by
          field_simp [hNR_pos.ne', hSN_pos.ne']; ring_nf; rw [Real.sq_sqrt hNR_pos.le]
  have harc1 : |Real.arcsin s1 - √6 / √NR| ≤ 32 / (NR * √NR) := by
    obtain ⟨ha_lo, ha_hi⟩ := arcsin_approx_small hs1_pos.le hs1_14
    have hc3 : s1 ^ 3 ≤ 27 / (NR * √NR) := by
      have hp := pow_le_pow_left₀ hs1_pos.le hs1_le_3 3
      have heq : (3 / √NR) ^ 3 = 27 / (NR * √NR) :=
        (by rw [div_pow, show (3 : ℝ) ^ 3 = 27 by norm_num, pow_succ, Real.sq_sqrt hNR_pos.le])
      linarith only [hp, heq]
    obtain ⟨hd1, hd2⟩ := abs_sub_le_iff.1 hs1_diff
    have hpad_nn : 0 ≤ 1 / (NR * √NR) := div_nonneg zero_le_one (mul_nonneg hNR_pos.le hSN_pos.le)
    have h31 : 4 / (NR * √NR) + 27 / (NR * √NR) + 1 / (NR * √NR) = 32 / (NR * √NR) := (by ring)
    have h28 : 4 / (NR * √NR) + 28 * (1 / (NR * √NR)) = 32 / (NR * √NR) := (by ring)
    exact abs_sub_le_iff.2 ⟨by linarith only [ha_hi, hc3, hd1, hpad_nn, h31],
      by linarith only [ha_lo, hd2, hpad_nn, h28]⟩
  -- 2. `|arcsin (-u2 1) - √2 / √NR|`
  have hu2_nn : 0 ≤ -u2 1 := (by rw [hu2_1]; exact Real.sqrt_nonneg _)
  have hu2_sq : (-u2 1) ^ 2 = (2 * (NR - 3)) / ((NR - 1) * (NR - 2)) :=
    (by rw [hu2_1, Real.sq_sqrt (div_nonneg (by linarith only [hNR3]) hN1N2.le)])
  have hu2_le_2 : -u2 1 ≤ 2 / √NR := by
    refine sq_le_imp_le hu2_nn (by positivity) ?_; rw [hu2_sq, div_pow, Real.sq_sqrt hNR_pos.le,
      div_le_div_iff₀ hN1N2 hNR_pos]; nlinarith only [hNR16]
  have hu2_14 : -u2 1 ≤ 1 / 4 := hu2_le_2.trans (by
    rw [div_le_div_iff₀ hSN_pos (by norm_num)]; have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ 100 := (by norm_num)
    linarith only [hSN_ge, h8])
  have hu2_diff : |(-u2 1) - √2 / √NR| ≤ 4 / (NR * √NR) := by
    have hb_eq : √(2 / NR) = √2 / √NR := Real.sqrt_div (by norm_num) NR; rw [← hb_eq, ← Real.sqrt_sq
      hu2_nn]; refine (abs_sqrt_sub_sqrt_le (sq_nonneg _) (div_pos (by norm_num) hNR_pos)).trans ?_
    rw [hb_eq, hu2_sq]
    have hsub : |(2 * (NR - 3)) / ((NR - 1) * (NR - 2)) - 2 / NR| ≤ 4 / (NR ^ 2) := by
      have heq : (2 * (NR - 3)) / ((NR - 1) * (NR - 2)) - 2 / NR = -4 / (NR * (NR - 1) * (NR - 2))
        := (by field_simp [hNR_pos.ne', hNR1.ne', hNR2.ne']; ring); rw [heq, abs_div, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hNN1N2, div_le_div_iff₀ hNN1N2
        (by positivity)]; have hq : NR ≤ (NR - 1) * (NR - 2) := (by nlinarith only [hNR16])
      have hcub : NR ^ 2 ≤ NR * (NR - 1) * (NR - 2) := by
        calc NR ^ 2 = NR * NR := sq NR
          _ ≤ NR * ((NR - 1) * (NR - 2)) := mul_le_mul_of_nonneg_left hq hNR_pos.le
          _ = NR * (NR - 1) * (NR - 2) := (mul_assoc _ _ _).symm
      linarith only [hcub]
    have hsq2_ge : 1 / √NR ≤ √2 / √NR := div_le_div_of_nonneg_right (sq_le_imp_le (by norm_num)
      (Real.sqrt_nonneg 2) (by rw [Real.sq_sqrt (by norm_num)]; norm_num)) hSN_pos.le
    calc |(2 * (NR - 3)) / ((NR - 1) * (NR - 2)) - 2 / NR| / (√2 / √NR)
        ≤ (4 / NR ^ 2) / (1 / √NR) :=
          (div_le_div_of_nonneg_right hsub (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq2_ge)
      _ = 4 / (NR * √NR) := by field_simp [hNR_pos.ne', hSN_pos.ne']; exact Real.sq_sqrt hNR_pos.le
  have harc2 : |Real.arcsin (-u2 1) - √2 / √NR| ≤ 32 / (NR * √NR) := by
    obtain ⟨ha_lo, ha_hi⟩ := arcsin_approx_small hu2_nn hu2_14
    have hc3 : (-u2 1) ^ 3 ≤ 8 / (NR * √NR) := by
      have hp := pow_le_pow_left₀ hu2_nn hu2_le_2 3; have heq : (2 / √NR) ^ 3 = 8 / (NR * √NR) :=
        (by rw [div_pow, show (2 : ℝ) ^ 3 = 8 by norm_num, pow_succ, Real.sq_sqrt hNR_pos.le])
      linarith only [hp, heq]
    obtain ⟨hd1, hd2⟩ := abs_sub_le_iff.1 hu2_diff
    have hpad_nn : 0 ≤ 1 / (NR * √NR) := div_nonneg zero_le_one (mul_nonneg hNR_pos.le hSN_pos.le)
    have h20 : 4 / (NR * √NR) + 8 / (NR * √NR) + 20 * (1 / (NR * √NR)) = 32 / (NR * √NR) :=
      (by ring); have h28 : 4 / (NR * √NR) + 28 * (1 / (NR * √NR)) = 32 / (NR * √NR) := (by ring)
    exact abs_sub_le_iff.2 ⟨by linarith only [ha_hi, hc3, hd1, hpad_nn, h20],
      by linarith only [ha_lo, hd2, hpad_nn, h28]⟩
  -- 3. Axis perturbation bounds `≤ 1 / √NR`
  have h_2N_le : 2 / NR ≤ 1 / √NR := by
    rw [div_le_div_iff₀ hNR_pos hSN_pos, one_mul]
    have hm : 2 * √NR ≤ √NR * √NR := mul_le_mul_of_nonneg_right (le_trans
      (by norm_num : (2 : ℝ) ≤ (2 : ℝ) ^ 100) hSN_ge) hSN_pos.le
    rwa [Real.mul_self_sqrt hNR_pos.le] at hm
  have hax1_0 : |(u1 0 / s1) - (-√(2 / 3 : ℝ))| ≤ 1 / √NR := by
    have heq_neg : (u1 0 / s1) - (-√(2 / 3 : ℝ)) = -(√(4 * (NR - 3) / (6 * NR - 16)) - √(2 / 3 : ℝ))
      := by
      rw [hu1_0_d]
      have h4 : (2 : ℝ) * √((NR - 3) / (6 * NR - 16)) = √(4 * (NR - 3) / (6 * NR - 16)) := by
        rw [show 4 * (NR - 3) / (6 * NR - 16) = (2 : ℝ) ^ 2 * ((NR - 3) / (6 * NR - 16)) by ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      linarith only [h4]
    rw [heq_neg, abs_neg]; refine (abs_sqrt_sub_sqrt_le (div_nonneg (by linarith only [hNR3])
      h6NR16.le) (by norm_num)).trans ?_
    have hdiff : |4 * (NR - 3) / (6 * NR - 16) - (2 / 3 : ℝ)| ≤ 1 / NR := by
      have hsub : 4 * (NR - 3) / (6 * NR - 16) - (2 / 3 : ℝ) = -4 / (3 * (6 * NR - 16)) := by
        have h3ne : (3 : ℝ) ≠ 0 := (by norm_num); rw [div_sub_div _ _ h6NR16.ne' h3ne,
          div_eq_div_iff (mul_ne_zero h6NR16.ne' h3ne) (mul_ne_zero h3ne h6NR16.ne')]; ring
      have h3_6 : 0 < 3 * (6 * NR - 16) := (by linarith only [h6NR16]); rw [hsub, abs_div, abs_neg,
        abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos h3_6, div_le_div_iff₀ h3_6 hNR_pos]
      linarith only [hNR16]
    have hsq_ge : (1 / 2 : ℝ) ≤ √(2 / 3 : ℝ) := sq_le_imp_le (by norm_num) (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
    calc |4 * (NR - 3) / (6 * NR - 16) - (2 / 3 : ℝ)| / √(2 / 3 : ℝ)
        ≤ (1 / NR) / (1 / 2) := (div_le_div_of_nonneg_right hdiff (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq_ge)
      _ = 2 / NR := by ring
      _ ≤ 1 / √NR := h_2N_le
  have hax1_2 : |(u1 2 / s1) - √(1 / 3 : ℝ)| ≤ 1 / √NR := by
    rw [hu1_2_d]; refine (abs_sqrt_sub_sqrt_le (div_nonneg (by linarith only [hNR2]) h6NR16.le)
      (by norm_num)).trans ?_
    have hdiff : |(2 * (NR - 2)) / (6 * NR - 16) - (1 / 3 : ℝ)| ≤ 1 / NR := by
      have hsub : (2 * (NR - 2)) / (6 * NR - 16) - (1 / 3 : ℝ) = 4 / (3 * (6 * NR - 16)) := by
        have h3ne : (3 : ℝ) ≠ 0 := (by norm_num); rw [div_sub_div _ _ h6NR16.ne' h3ne,
          div_eq_div_iff (mul_ne_zero h6NR16.ne' h3ne) (mul_ne_zero h3ne h6NR16.ne')]; ring
      have h3_6 : 0 < 3 * (6 * NR - 16) := (by linarith only [h6NR16]); rw [hsub, abs_of_pos
        (div_pos (by norm_num) h3_6), div_le_div_iff₀ h3_6 hNR_pos]; linarith only [hNR16]
    have hsq_ge : (1 / 2 : ℝ) ≤ √(1 / 3 : ℝ) := sq_le_imp_le (by norm_num) (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
    calc |(2 * (NR - 2)) / (6 * NR - 16) - (1 / 3 : ℝ)| / √(1 / 3 : ℝ)
        ≤ (1 / NR) / (1 / 2) := (div_le_div_of_nonneg_right hdiff (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq_ge)
      _ = 2 / NR := by ring
      _ ≤ 1 / √NR := h_2N_le
  have hs2_ge_half : (1 / 2 : ℝ) ≤ s2 := by
    have hu22_ge : (1 / 2 : ℝ) ≤ u2 2 := by
      rw [hu2_2]; refine sq_le_imp_le (by norm_num) (Real.sqrt_nonneg _) ?_; rw [div_pow,
        Real.sq_sqrt (div_nonneg hNR3.le hNR1.le), div_le_div_iff₀ (by norm_num) hNR1]
      linarith only [hNR16]
    have hs2_ge_u : u2 2 ≤ s2 := by
      dsimp only [s2]; refine sq_le_imp_le (by linarith only [hu22_ge]) (Real.sqrt_nonneg _) ?_
      rw [Real.sq_sqrt (by positivity)]; linarith only [sq_nonneg (u2 0)]
    exact hu22_ge.trans hs2_ge_u
  have hu2_0_le : u2 0 ≤ 1 / (2 * √NR) := by
    rw [hu2_0]; refine sq_le_imp_le (Real.sqrt_nonneg _) (by positivity) ?_
    rw [Real.sq_sqrt (div_nonneg (by norm_num) hN1N2.le), div_pow, mul_pow, Real.sq_sqrt hNR_pos.le,
      div_le_div_iff₀ hN1N2 (by positivity)]; nlinarith only [hNR16]
  have hax2_0 : |u2 0 / s2| ≤ 1 / √NR := by
    have hnn : 0 ≤ u2 0 / s2 := div_nonneg (by rw [hu2_0]; exact Real.sqrt_nonneg _) hs2_pos.le
    rw [abs_of_nonneg hnn]
    calc u2 0 / s2 ≤ (1 / (2 * √NR)) / (1 / 2) := (div_le_div_of_nonneg_right hu2_0_le
          hs2_pos.le).trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) hs2_ge_half)
      _ = 1 / √NR := by field_simp [hSN_pos.ne']
  have hax2_2 : |u2 2 / s2 - 1| ≤ 1 / √NR := by
    have hu22_nn : 0 ≤ u2 2 / s2 := div_nonneg (by rw [hu2_2]; exact Real.sqrt_nonneg _) hs2_pos.le
    have hsq_sum : (u2 0 / s2) ^ 2 + (u2 2 / s2) ^ 2 = 1 := by
      have hs2_2 : (u2 0) ^ 2 + (u2 2) ^ 2 = s2 ^ 2 :=
        (by dsimp only [s2]; exact (Real.sq_sqrt (by positivity)).symm); rw [div_pow, div_pow, ←
        add_div, hs2_2, div_self (pow_ne_zero 2 hs2_pos.ne')]
    have hu22_le1 : u2 2 / s2 ≤ 1 := sq_le_imp_le hu22_nn zero_le_one
      (by linarith only [hsq_sum, sq_nonneg (u2 0 / s2)])
    have h1_sub : 1 - u2 2 / s2 ≤ (u2 0 / s2) ^ 2 := by nlinarith only [hu22_nn, hu22_le1, hsq_sum]
    have hsq_le : (u2 0 / s2) ^ 2 ≤ 1 / NR := by
      have habs := hax2_0
      have hnn0 : 0 ≤ u2 0 / s2 := div_nonneg (by rw [hu2_0]; exact Real.sqrt_nonneg _) hs2_pos.le
      rw [abs_of_nonneg hnn0] at habs
      calc (u2 0 / s2) ^ 2 ≤ (1 / √NR) ^ 2 := pow_le_pow_left₀ hnn0 habs 2
        _ = 1 / NR := by rw [div_pow, one_pow, Real.sq_sqrt hNR_pos.le]
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [hu22_le1])]; have h1N_le : 1 / NR ≤ 2 / NR :=
      div_le_div_of_nonneg_right (by norm_num) hNR_pos.le
    exact (h1_sub.trans hsq_le).trans (h1N_le.trans h_2N_le)
  exact ⟨harc1, harc2, hax1_0, hax1_2, hax2_0, hax2_2⟩
private theorem jp01AngleIV_mem {wIV : SNIVal} {wReal θWalk : ℝ} {n tau12 : ℕ} (hn : 200 ≤ n) (htau
    : tau12 ≤ 4000000000000) (hw1 : 1 ≤ wReal) (hw_mem : snMem wReal wIV) (hθ_err :
    |θWalk - wReal / √((2 : ℝ) ^ n)| ≤ 32 / ((2 : ℝ) ^ n * √((2 : ℝ) ^ n))) :
    let K := DickeSol.p01StepCount tau12 (2 ^ n)
    0 ≤ (snToWDIVal (jp01AngleIV wIV tau12)).1 ∧ snMem (2 * (K : ℝ) * θWalk) (jp01AngleIV wIV tau12)
      := by
  intro K; obtain ⟨hSN_ge, hN_ge⟩ := pow_two_200_bounds hn
  have hSN_pos : (0 : ℝ) < √((2 : ℝ) ^ n) := lt_of_lt_of_le (by positivity) hSN_ge; have hN_pos : (0
    : ℝ) < (2 : ℝ) ^ n := lt_of_lt_of_le (by positivity) hN_ge; by_cases htau0 : tau12 = 0
  · subst htau0; have hK0 : K = 0 := (by simp [K]); rw [hK0]; simp [jp01AngleIV, snMem, snToWDIVal,
      snZero, snToInt, DickeSol.wdMem]
  · have hb_false : _nEq tau12 0 = false :=
      Bool.eq_false_iff.mpr fun h => htau0 (_nEq_eq.mp h)
    dsimp only [jp01AngleIV]; rw [hb_false, Bool.cond_false, withForcedSNIVal_eq, withForcedSNat_eq,
      withForcedSNat_eq]; set omIV := snScaleNatIV 2 wIV; set tIV : SNIVal := ((false, tau12 * 1000
      - 1), (false, tau12 * 1000 + 1)); set thRaw := snMulIV omIV tIV; refine ⟨?_, ?_⟩
    · simp only [snToWDIVal, snToInt_maxZero]; exact le_max_left 0 _
    · have ht_wd := DickeSol.p01StepCount_div_sqrt_mem hn htau
      have ht_mem : snMem ((K : ℝ) / √((2 : ℝ) ^ n)) tIV := by
        unfold snMem
        have hmax_eq : max 0 ((tau12 : ℤ) * 1000 - 1) = ((tau12 * 1000 - 1 : ℕ) : ℤ) := (by omega)
        have htIV_eq : snToWDIVal tIV = (max 0 ((tau12 : ℤ) * 1000 - 1), (tau12 : ℤ) * 1000 + 1) :=
          (by simp only [tIV, snToWDIVal, snToInt, hmax_eq]; push_cast; rfl)
        rw [htIV_eq]; simpa [K, Nat.cast_pow] using ht_wd
      have hom_mem : snMem (2 * wReal) omIV := by
        have h := snMem_scaleNat 2 hw_mem; rwa [Nat.cast_ofNat] at h
      have hraw_mem : snMem ((2 * wReal) * ((K : ℝ) / √((2 : ℝ) ^ n))) thRaw := snMem_mul hom_mem
        ht_mem; have hK_hi : (K : ℝ) ≤ ((tau12 : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) :=
        (by simpa [K, Nat.cast_pow] using DickeSol.p01StepCount_le_tau_sqrt tau12 (2 ^ n))
      have hK_4SN : (K : ℝ) ≤ 4 * √((2 : ℝ) ^ n) := by
        have htau_r : (tau12 : ℝ) ≤ 4000000000000 := (by exact_mod_cast htau); have hdiv4 : (tau12 :
          ℝ) / 1000000000000 ≤ 4 := (by linarith only [htau_r]); have hm :=
          mul_le_mul_of_nonneg_right hdiv4 hSN_pos.le; linarith only [hK_hi, hm]
      have hdiff : |2 * (K : ℝ) * θWalk - (2 * wReal) * ((K : ℝ) / √((2 : ℝ) ^ n))| ≤
          1 / DickeSol.wdScaleR := by
        have heq : 2 * (K : ℝ) * θWalk - (2 * wReal) * ((K : ℝ) / √((2 : ℝ) ^ n)) = 2 * (K : ℝ) *
          (θWalk - wReal / √((2 : ℝ) ^ n)) := (by ring); rw [heq, abs_mul, abs_of_nonneg
          (by positivity : (0 : ℝ) ≤ 2 * K)]
        calc 2 * (K : ℝ) * |θWalk - wReal / √((2 : ℝ) ^ n)|
            ≤ (8 * √((2 : ℝ) ^ n)) * (32 / ((2 : ℝ) ^ n * √((2 : ℝ) ^ n))) :=
              mul_le_mul (by linarith only [hK_4SN]) hθ_err (abs_nonneg _) (by positivity)
          _ = 256 / (2 : ℝ) ^ n := by field_simp [hSN_pos.ne', hN_pos.ne']; ring
          _ ≤ 256 / (2 : ℝ) ^ 200 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hN_ge
          _ ≤ 1 / DickeSol.wdScaleR := by rw [jp01WdScaleR_eq]; norm_num
      have hnn_angle : 0 ≤ 2 * (K : ℝ) * θWalk := by
        have hl := (abs_sub_le_iff.1 hθ_err).2
        have h1 : 32 / ((2 : ℝ) ^ n * √((2 : ℝ) ^ n)) ≤ wReal / √((2 : ℝ) ^ n) := by
          rw [← div_div]; refine div_le_div_of_nonneg_right ?_ hSN_pos.le
          have h32 : 32 / (2 : ℝ) ^ n ≤ 32 / (2 : ℝ) ^ 200 := div_le_div_of_nonneg_left
            (by norm_num) (by positivity) hN_ge; have h32_1 : (32 : ℝ) / (2 : ℝ) ^ 200 ≤ 1 :=
            (by norm_num); linarith only [hw1, h32, h32_1]
        have hθ_nn : 0 ≤ θWalk := (by linarith only [hl, h1]); positivity
      unfold snMem DickeSol.wdMem at hraw_mem ⊢; dsimp only [snToWDIVal] at hraw_mem ⊢
      simp only [snToInt_maxZero, snToInt_sub, snToInt_add]; have hsn1 : snToInt (false, 1) = 1 :=
        rfl; rw [hsn1]; have hB : 0 < DickeSol.wdScaleR := jp01WdScaleR_pos; obtain ⟨hd1, hd2⟩ :=
        abs_sub_le_iff.1 hdiff; obtain ⟨hr1, hr2⟩ := hraw_mem; constructor
      · rw [div_le_iff₀ hB, Int.cast_max, Int.cast_zero]
        refine max_le (mul_nonneg hnn_angle hB.le) ?_; rw [← div_le_iff₀ hB, Int.cast_sub,
          Int.cast_one, sub_div]; linarith only [hr1, hd2]
      · rw [Int.cast_add, Int.cast_one, add_div]; linarith only [hr2, hd1]
/-! ### Perturbation & Enclosure of `jp01EvalInterval` and `checkWarmJP01R2Table` -/
private noncomputable def jp01InitOrbVec (n : ℕ) (γ : ℝ) : Fin 3 → ℝ :=
  DickeSol.vec3
    (√(((2 : ℝ) ^ n - 3) / (2 : ℝ) ^ n) * Real.cos γ)
    (√(((2 : ℝ) ^ n - 2) / (2 : ℝ) ^ n) * (Real.sin γ / √2) +
      Real.cos γ / √((2 : ℝ) ^ n))
    (Real.sin γ / √((2 : ℝ) ^ n))
private noncomputable def rotFrameEval (p q c s : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let x1 := x 1
  let x2 := p * x 0 + q * x 2
  let x3 := q * x 0 - p * x 2
  let y1 := x1 * c - x2 * s
  let y2 := x1 * s + x2 * c
  DickeSol.vec3 (y2 * p + x3 * q) y1 (y2 * q - x3 * p)
private lemma abs_bilinear_diff {a a' b b' M_a M_b δa δb : ℝ}
    (ha' : |a'| ≤ M_a) (hb : |b| ≤ M_b)
    (hda : |a - a'| ≤ δa) (hdb : |b - b'| ≤ δb) :
    |a * b - a' * b'| ≤ M_b * δa + M_a * δb := by
  have h0_b : 0 ≤ M_b := (abs_nonneg b).trans hb; have h0_a : 0 ≤ M_a := (abs_nonneg a').trans ha'
  have heq : a * b - a' * b' = (a - a') * b + a' * (b - b') := (by ring); rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, mul_comm]; exact mul_le_mul hb hda (abs_nonneg _) h0_b
  · rw [abs_mul]; exact mul_le_mul ha' hdb (abs_nonneg _) h0_a
private lemma rotFrameEval_lipschitz {p q p' q' c s δx δu : ℝ} {x x' : Fin 3 → ℝ}
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hp' : |p'| ≤ 1) (hq' : |q'| ≤ 1)
    (hc : |c| ≤ 1) (hs : |s| ≤ 1)
    (hx' : ∀ i, |x' i| ≤ 3)
    (hdx : ∀ i, |x i - x' i| ≤ δx)
    (hdp : |p - p'| ≤ δu) (hdq : |q - q'| ≤ δu) :
    ∀ i : Fin 3, |rotFrameEval p q c s x i - rotFrameEval p' q' c s x' i| ≤
      5 * δx + 27 * δu := by
  have hδx0 : 0 ≤ δx := (abs_nonneg _).trans (hdx 0); have hδu0 : 0 ≤ δu := (abs_nonneg _).trans hdp
  set x2 := p * x 0 + q * x 2; set x2' := p' * x' 0 + q' * x' 2
  set x3 := q * x 0 - p * x 2; set x3' := q' * x' 0 - p' * x' 2
  have hx2_err : |x2 - x2'| ≤ 2 * δx + 6 * δu := by
    have h1 : |x 0 * p - x' 0 * p'| ≤ 1 * δx + 3 * δu := abs_bilinear_diff (hx' 0) hp (hdx 0) hdp
    rw [mul_comm (x 0), mul_comm (x' 0)] at h1
    have h2 : |x 2 * q - x' 2 * q'| ≤ 1 * δx + 3 * δu := abs_bilinear_diff (hx' 2) hq (hdx 2) hdq
    rw [mul_comm (x 2), mul_comm (x' 2)] at h2; have heq : x2 - x2' = (p * x 0 - p' * x' 0) + (q * x
      2 - q' * x' 2) := (by dsimp [x2, x2']; ring); rw [heq]; linarith [abs_add_le (p * x 0 - p' *
      x' 0) (q * x 2 - q' * x' 2)]
  have hx3_err : |x3 - x3'| ≤ 2 * δx + 6 * δu := by
    have h1 : |x 0 * q - x' 0 * q'| ≤ 1 * δx + 3 * δu := abs_bilinear_diff (hx' 0) hq (hdx 0) hdq
    rw [mul_comm (x 0), mul_comm (x' 0)] at h1
    have h2 : |x 2 * p - x' 2 * p'| ≤ 1 * δx + 3 * δu := abs_bilinear_diff (hx' 2) hp (hdx 2) hdp
    rw [mul_comm (x 2), mul_comm (x' 2)] at h2; have heq : x3 - x3' = (q * x 0 - q' * x' 0) + -(p *
      x 2 - p' * x' 2) := (by dsimp [x3, x3']; ring); rw [heq]; have hsub := abs_add_le (q * x 0 -
      q' * x' 0) (-(p * x 2 - p' * x' 2)); rw [abs_neg] at hsub; linarith
  have hx2'_bd : |x2'| ≤ 6 := by
    dsimp only [x2']
    have h1 : |p' * x' 0| ≤ 1 * 3 := by
      rw [abs_mul]; exact mul_le_mul hp' (hx' 0) (abs_nonneg _) zero_le_one
    have h2 : |q' * x' 2| ≤ 1 * 3 := by
      rw [abs_mul]; exact mul_le_mul hq' (hx' 2) (abs_nonneg _) zero_le_one
    linarith [abs_add_le (p' * x' 0) (q' * x' 2)]
  have hx3'_bd : |x3'| ≤ 6 := by
    dsimp only [x3']
    have h1 : |q' * x' 0| ≤ 1 * 3 := by
      rw [abs_mul]; exact mul_le_mul hq' (hx' 0) (abs_nonneg _) zero_le_one
    have h2 : |p' * x' 2| ≤ 1 * 3 := by
      rw [abs_mul]; exact mul_le_mul hp' (hx' 2) (abs_nonneg _) zero_le_one
    have hsub := abs_add_le (q' * x' 0) (-(p' * x' 2)); rw [abs_neg] at hsub; rw [sub_eq_add_neg]
    exact hsub.trans (by linarith)
  set y1 := x 1 * c - x2 * s; set y1' := x' 1 * c - x2' * s; set y2 := x 1 * s + x2 * c; set y2' :=
    x' 1 * s + x2' * c
  have hy1_err : |y1 - y1'| ≤ 3 * δx + 6 * δu := by
    have heq : y1 - y1' = (x 1 - x' 1) * c + (-(x2 - x2')) * s := (by dsimp [y1, y1']; ring)
    rw [heq]
    have h1 : |(x 1 - x' 1) * c| ≤ δx * 1 := by
      rw [abs_mul]; exact mul_le_mul (hdx 1) hc (abs_nonneg _) hδx0
    have h2 : |(-(x2 - x2')) * s| ≤ (2 * δx + 6 * δu) * 1 := by
      rw [abs_mul, abs_neg]; exact mul_le_mul hx2_err hs (abs_nonneg _) (by positivity)
    linarith [abs_add_le ((x 1 - x' 1) * c) ((-(x2 - x2')) * s)]
  have hy2_err : |y2 - y2'| ≤ 3 * δx + 6 * δu := by
    have heq : y2 - y2' = (x 1 - x' 1) * s + (x2 - x2') * c := (by dsimp [y2, y2']; ring); rw [heq]
    have h1 : |(x 1 - x' 1) * s| ≤ δx * 1 := by
      rw [abs_mul]; exact mul_le_mul (hdx 1) hs (abs_nonneg _) hδx0
    have h2 : |(x2 - x2') * c| ≤ (2 * δx + 6 * δu) * 1 := by
      rw [abs_mul]; exact mul_le_mul hx2_err hc (abs_nonneg _) (by positivity)
    linarith [abs_add_le ((x 1 - x' 1) * s) ((x2 - x2') * c)]
  have hy2'_bd : |y2'| ≤ 9 := by
    dsimp only [y2']
    have h1 : |x' 1 * s| ≤ 3 * 1 := by
      rw [abs_mul]; exact mul_le_mul (hx' 1) hs (abs_nonneg _) (by norm_num)
    have h2 : |x2' * c| ≤ 6 * 1 := by
      rw [abs_mul]; exact mul_le_mul hx2'_bd hc (abs_nonneg _) (by norm_num)
    linarith [abs_add_le (x' 1 * s) (x2' * c)]
  intro i; fin_cases i
  · dsimp only [rotFrameEval, DickeSol.vec3, Fin.isValue]
    have h1 := abs_bilinear_diff hy2'_bd hp hy2_err hdp
    have h2 := abs_bilinear_diff hx3'_bd hq hx3_err hdq; have heq : (y2 * p + x3 * q) - (y2' * p' +
      x3' * q') = (y2 * p - y2' * p') + (x3 * q - x3' * q') := (by ring)
    change |(y2 * p + x3 * q) - (y2' * p' + x3' * q')| ≤ _; rw [heq]; linarith [abs_add_le (y2 * p -
      y2' * p') (x3 * q - x3' * q')]
  · dsimp only [rotFrameEval, DickeSol.vec3, Fin.isValue]; change |y1 - y1'| ≤ _; linarith
  · dsimp only [rotFrameEval, DickeSol.vec3, Fin.isValue]
    have h1 := abs_bilinear_diff hy2'_bd hq hy2_err hdq
    have h2 := abs_bilinear_diff hx3'_bd hp hx3_err hdp; have heq : (y2 * q - x3 * p) - (y2' * q' -
      x3' * p') = (y2 * q - y2' * q') + (-(x3 * p - x3' * p')) := (by ring)
    change |(y2 * q - x3 * p) - (y2' * q' - x3' * p')| ≤ _; rw [heq]; have hab := abs_add_le (y2 * q
      - y2' * q') (-(x3 * p - x3' * p')); rw [abs_neg] at hab; linarith
private lemma rotFrameEval_u1_asymp (c1 s1 c0 d1 : ℝ) : rotFrameEval (-√(2 / 3 : ℝ)) (√(1 / 3 : ℝ))
  c1 s1 (DickeSol.vec3 c0 d1 0) = DickeSol.vec3 (((1 + 2 * c1) / 3) * c0 - (√6 / 3) * s1 * d1) ((√6
  / 3) * s1 * c0 + c1 * d1) ((√2 / 3) * (1 - c1) * c0 + (√3 / 3) * s1 * d1) := by
  have h23_eq : √(2 / 3 : ℝ) = √6 / 3 := by
    have heq : (2 / 3 : ℝ) = 6 / (3 : ℝ) ^ 2 := (by ring); rw [heq, Real.sqrt_div (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h13_eq : √(1 / 3 : ℝ) = √3 / 3 := by
    have heq : (1 / 3 : ℝ) = 3 / (3 : ℝ) ^ 2 := (by ring); rw [heq, Real.sqrt_div (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h63 : (√6 : ℝ) * √3 = 3 * √2 := by
    rw [← Real.sqrt_mul (by norm_num), show (6 : ℝ) * 3 = 3 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hsq6 : (√6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num); have hsq3 : (√3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num); rw [h23_eq, h13_eq]; refine DickeSol.fin3_ext ?_ ?_ ?_
  · simp only [rotFrameEval, DickeSol.vec3_zero, DickeSol.vec3_one, DickeSol.vec3_two]
    linear_combination (norm := ring) (c1 * c0 / 9) * hsq6 + (c0 / 9) * hsq3
  · simp only [rotFrameEval, DickeSol.vec3_zero, DickeSol.vec3_one, DickeSol.vec3_two]; ring
  · simp only [rotFrameEval, DickeSol.vec3_zero, DickeSol.vec3_one, DickeSol.vec3_two]
    linear_combination (norm := ring) ((1 - c1) * c0 / 9) * h63
private theorem jp01_sq_consts_mem (h2lo : jp01Sq2Lo * jp01Sq2Lo ≤ 2 * jp01Scale * jp01Scale) (h2hi
  : 2 * jp01Scale * jp01Scale ≤ jp01Sq2Hi * jp01Sq2Hi) (h3lo : jp01Sq3Lo * jp01Sq3Lo ≤ 3 * jp01Scale
  * jp01Scale) (h3hi : 3 * jp01Scale * jp01Scale ≤ jp01Sq3Hi * jp01Sq3Hi) (h6lo : jp01Sq6Lo *
  jp01Sq6Lo ≤ 6 * jp01Scale * jp01Scale) (h6hi : 6 * jp01Scale * jp01Scale ≤ jp01Sq6Hi * jp01Sq6Hi)
  : snMem √2 jp01Sq2IV ∧ snMem √3 jp01Sq3IV ∧ snMem √6 jp01Sq6IV := by
  have helper : ∀ (k lo hi : ℕ), lo * lo ≤ k * jp01Scale * jp01Scale → k * jp01Scale * jp01Scale ≤
    hi * hi → snMem √(k : ℝ) ((false, lo), (false, hi)) := by
    intro k lo hi hlo hhi; unfold snMem DickeSol.wdMem
    simp only [snToWDIVal, snToInt]; have hB : 0 < DickeSol.wdScaleR := jp01WdScaleR_pos
    have hBeq : (jp01Scale : ℝ) = DickeSol.wdScaleR := rfl; push_cast; constructor
    · rw [div_le_iff₀ hB]; refine sq_le_imp_le (by positivity) (by positivity) ?_; rw [mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg k), ← hBeq]; have hc : (lo : ℝ) * lo ≤ (k : ℝ) * jp01Scale *
        jp01Scale := (by exact_mod_cast hlo); nlinarith
    · rw [le_div_iff₀ hB]; refine sq_le_imp_le (by positivity) (by positivity) ?_; rw [mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg k), ← hBeq]; have hc : (k : ℝ) * jp01Scale * jp01Scale ≤ (hi :
        ℝ) * hi := (by exact_mod_cast hhi); nlinarith
  refine ⟨?_, ?_, ?_⟩
  · simpa [jp01Sq2IV] using helper 2 jp01Sq2Lo jp01Sq2Hi h2lo h2hi
  · simpa [jp01Sq3IV] using helper 3 jp01Sq3Lo jp01Sq3Hi h3lo h3hi
  · simpa [jp01Sq6IV] using helper 6 jp01Sq6Lo jp01Sq6Hi h6lo h6hi
private theorem jp01InitOrbVec_rot1_err {n : ℕ} (hn : 200 ≤ n) (γ : ℝ) (K1 : ℕ) :
    let u1 := DickeSol.u1OrbVec (2 ^ n) 2 2
    let s1 := √((u1 0) ^ 2 + (u1 2) ^ 2)
    let θ1 := Real.arcsin s1
    let C1 := Real.cos (2 * (K1 : ℝ) * θ1)
    let S1 := Real.sin (2 * (K1 : ℝ) * θ1)
    let c0 := Real.cos γ
    let d1 := Real.sin γ / √2
    let x0_as := ((1 + 2 * C1) / 3) * c0 - (√6 / 3) * S1 * d1
    let x1_as := (√6 / 3) * S1 * c0 + C1 * d1
    let x2_as := (√2 / 3) * (1 - C1) * c0 + (√3 / 3) * S1 * d1
    let x_mid := ((DickeSol.rot3Pos u1)^[K1]) (jp01InitOrbVec n γ)
    let z_id := DickeSol.vec3 x0_as x1_as x2_as
    (∀ i, |x_mid i - z_id i| ≤ 37 / √((2 : ℝ) ^ n)) ∧ (∀ i, |z_id i| ≤ 3) := by
  intro u1 s1 θ1 C1 S1 c0 d1 x0_as x1_as x2_as x_mid z_id
  obtain ⟨hSN_ge, hN_ge⟩ := pow_two_200_bounds hn; set NR : ℝ := (2 : ℝ) ^ n
  have hSN_pos : 0 < √NR := lt_of_lt_of_le (by positivity) hSN_ge
  have hNR_pos : 0 < NR := lt_of_lt_of_le (by positivity) hN_ge
  have hN16 : 16 ≤ 2 ^ n :=
    le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right (by positivity) hn)
  have hNR16 : (16 : ℝ) ≤ NR := le_trans (by norm_num) hN_ge
  obtain ⟨hdu1_r, _, hu1_1_r, _, hs1_pos_r, _, _⟩ := jp01_m2r2_basis_closed hN16
  obtain ⟨_, _, hax1_0_r, hax1_2_r, _, _⟩ := jp01_m2r2_angles_and_axes_err hn
  have hdu1 : DickeSol.dot3 u1 u1 = 1 := hdu1_r
  have hu1_1_nn : 0 ≤ u1 1 := hu1_1_r
  have hs1_pos : 0 < s1 := hs1_pos_r
  have hax1_0 : |(u1 0 / s1) - (-√(2 / 3 : ℝ))| ≤ 1 / √NR := hax1_0_r
  have hax1_2 : |(u1 2 / s1) - √(1 / 3 : ℝ)| ≤ 1 / √NR := hax1_2_r
  clear hdu1_r hu1_1_r hs1_pos_r hax1_0_r hax1_2_r
  have hsq2_ge1 : (1 : ℝ) ≤ √2 := sq_le_imp_le zero_le_one (Real.sqrt_nonneg 2)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
  -- Finite-N perturbation from `jp01InitOrbVec n γ` to `vec3 c0 d1 0`
  have hs_abs : |Real.sin γ| ≤ 1 := Real.abs_sin_le_one γ
  have hc_abs : |c0| ≤ 1 := Real.abs_cos_le_one γ
  have hd1_abs : |d1| ≤ 1 := by
    dsimp only [d1]; rw [abs_div, abs_of_pos (show (0 : ℝ) < √2 by positivity)]
    exact (div_le_div_of_nonneg_right hs_abs (by positivity)).trans
      (div_le_one_of_le₀ hsq2_ge1 (by positivity))
  let x_id := DickeSol.vec3 c0 d1 0
  have hx_id_bd : ∀ i, |x_id i| ≤ 3 := by
    intro i; fin_cases i
    · change |c0| ≤ 3; linarith only [hc_abs]
    · change |d1| ≤ 3; linarith only [hd1_abs]
    · change |(0 : ℝ)| ≤ 3; norm_num
  have hinit_diff : ∀ i, |jp01InitOrbVec n γ i - x_id i| ≤ 2 / √NR := by
    have h_3N_le : 3 / NR ≤ 1 / √NR := by
      rw [div_le_div_iff₀ hNR_pos hSN_pos, one_mul]
      have hm : 3 * √NR ≤ √NR * √NR := mul_le_mul_of_nonneg_right
        (le_trans (by norm_num : (3 : ℝ) ≤ (2 : ℝ) ^ 100) hSN_ge) hSN_pos.le
      rwa [Real.mul_self_sqrt hNR_pos.le] at hm
    have h12 : 1 / √NR + 1 / √NR = 2 / √NR := by ring
    have hNR3_nn : 0 ≤ NR - 3 := by linarith only [hNR16]
    have hNR2_nn : 0 ≤ NR - 2 := by linarith only [hNR16]
    intro i; fin_cases i
    · dsimp only [jp01InitOrbVec, x_id, DickeSol.vec3, Fin.isValue]
      change |√((NR - 3) / NR) * c0 - c0| ≤ 2 / √NR
      have hr1 : √((NR - 3) / NR) ≤ 1 :=
        Real.sqrt_le_one.2 (by rw [div_le_one hNR_pos]; linarith only [hNR16])
      have hsub1 : 1 - √((NR - 3) / NR) ≤ 3 / NR := by
        have hnn : 0 ≤ √((NR - 3) / NR) := Real.sqrt_nonneg _
        have hsq : (√((NR - 3) / NR)) ^ 2 = 1 - 3 / NR := by
          rw [Real.sq_sqrt (div_nonneg hNR3_nn hNR_pos.le)]; field_simp [hNR_pos.ne']
        nlinarith only [hnn, hsq, hr1]
      have hge0 : 0 ≤ 1 - √((NR - 3) / NR) := sub_nonneg.2 hr1
      have heq : √((NR - 3) / NR) * c0 - c0 = -(1 - √((NR - 3) / NR)) * c0 := by ring
      rw [heq, abs_mul, abs_neg, abs_of_nonneg hge0]
      have h1SN_pos : 0 < 1 / √NR := div_pos zero_lt_one hSN_pos
      calc (1 - √((NR - 3) / NR)) * |c0| ≤ (3 / NR) * 1 :=
            mul_le_mul hsub1 hc_abs (abs_nonneg _) (by positivity)
        _ ≤ 2 / √NR := by rw [mul_one]; linarith only [h_3N_le, h1SN_pos, h12]
    · dsimp only [jp01InitOrbVec, x_id, DickeSol.vec3, Fin.isValue]
      change |(√((NR - 2) / NR) * d1 + c0 / √NR) - d1| ≤ 2 / √NR
      have hr1 : √((NR - 2) / NR) ≤ 1 :=
        Real.sqrt_le_one.2 (by rw [div_le_one hNR_pos]; linarith only [hNR16])
      have hsub2' : 1 - √((NR - 2) / NR) ≤ 2 / NR := by
        have hnn : 0 ≤ √((NR - 2) / NR) := Real.sqrt_nonneg _
        have hsq : (√((NR - 2) / NR)) ^ 2 = 1 - 2 / NR := by
          rw [Real.sq_sqrt (div_nonneg hNR2_nn hNR_pos.le)]; field_simp [hNR_pos.ne']
        nlinarith only [hnn, hsq, hr1]
      have hsub2 : 1 - √((NR - 2) / NR) ≤ 3 / NR := by
        have h1N_pos : 0 ≤ 1 / NR := div_nonneg zero_le_one hNR_pos.le
        have h23 : 2 / NR + 1 / NR = 3 / NR := by ring
        linarith only [hsub2', h1N_pos, h23]
      have hge0 : 0 ≤ 1 - √((NR - 2) / NR) := sub_nonneg.2 hr1
      have heq : (√((NR - 2) / NR) * d1 + c0 / √NR) - d1 =
          -(1 - √((NR - 2) / NR)) * d1 + c0 / √NR := by ring
      rw [heq]
      have hp1 : |-(1 - √((NR - 2) / NR)) * d1| ≤ 1 / √NR := by
        rw [abs_mul, abs_neg, abs_of_nonneg hge0]
        have hm := mul_le_mul hsub2 hd1_abs (abs_nonneg _) (by positivity)
        linarith only [hm, h_3N_le]
      have hp2 : |c0 / √NR| ≤ 1 / √NR := by
        rw [abs_div, abs_of_pos hSN_pos]; exact div_le_div_of_nonneg_right hc_abs hSN_pos.le
      have hab := abs_add_le (-(1 - √((NR - 2) / NR)) * d1) (c0 / √NR)
      linarith only [hab, hp1, hp2, h12]
    · dsimp only [jp01InitOrbVec, x_id, DickeSol.vec3, Fin.isValue]
      change |Real.sin γ / √NR - 0| ≤ 2 / √NR; rw [sub_zero, abs_div, abs_of_pos hSN_pos]
      have h1SN_pos : 0 < 1 / √NR := div_pos zero_lt_one hSN_pos
      have hd := div_le_div_of_nonneg_right hs_abs hSN_pos.le; linarith only [hd, h1SN_pos, h12]
  have hu1_norm : |u1 0 / s1| ≤ 1 ∧ |u1 2 / s1| ≤ 1 := by
    have hsum : (u1 0 / s1) ^ 2 + (u1 2 / s1) ^ 2 = 1 := by
      have hs1_2 : (u1 0) ^ 2 + (u1 2) ^ 2 = s1 ^ 2 := by
        dsimp only [s1]; exact (Real.sq_sqrt (by positivity)).symm
      rw [div_pow, div_pow, ← add_div, hs1_2, div_self (pow_ne_zero 2 hs1_pos.ne')]
    exact ⟨abs_le.2 ⟨by nlinarith only [hsum, sq_nonneg (u1 2 / s1)],
      by nlinarith only [hsum, sq_nonneg (u1 2 / s1)]⟩,
      abs_le.2 ⟨by nlinarith only [hsum, sq_nonneg (u1 0 / s1)],
      by nlinarith only [hsum, sq_nonneg (u1 0 / s1)]⟩⟩
  have ha1_bd : |-√(2 / 3 : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_one.2 (by norm_num)
  have hb1_bd : |√(1 / 3 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_one.2 (by norm_num)
  have hx_mid_eq : x_mid = rotFrameEval (u1 0 / s1) (u1 2 / s1) C1 S1 (jp01InitOrbVec n γ) := by
    dsimp only [x_mid]
    have hcl := DickeSol.rot3Pos_iter_closed hdu1 hu1_1_nn hs1_pos K1 (jp01InitOrbVec n γ)
    dsimp only at hcl; rw [hcl]
    refine DickeSol.fin3_ext ?_ ?_ ?_ <;>
      (dsimp only [rotFrameEval, DickeSol.vec3_zero, DickeSol.vec3_one, DickeSol.vec3_two,
        s1, θ1, C1, S1]; ring)
  have hz_id_eq : rotFrameEval (-√(2 / 3 : ℝ)) (√(1 / 3 : ℝ)) C1 S1 x_id = z_id :=
    rotFrameEval_u1_asymp C1 S1 c0 d1
  have hmid_err : ∀ i, |x_mid i - z_id i| ≤ 37 / √NR := by
    intro i; rw [hx_mid_eq, ← hz_id_eq]
    refine (rotFrameEval_lipschitz hu1_norm.1 hu1_norm.2 ha1_bd hb1_bd
      (Real.abs_cos_le_one _) (Real.abs_sin_le_one _) hx_id_bd hinit_diff hax1_0 hax1_2 i).trans ?_
    exact le_of_eq (by ring)
  have hz_id_bd : ∀ i, |z_id i| ≤ 3 := by
    have hC1 : |C1| ≤ 1 := Real.abs_cos_le_one _; have hS1 : |S1| ≤ 1 := Real.abs_sin_le_one _
    have hsq6_3 : √6 / 3 ≤ 1 := by
      have h : √6 ≤ 3 := sq_le_imp_le (Real.sqrt_nonneg 6) (by norm_num)
        (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
      linarith only [h]
    have hsq2_3 : √2 / 3 ≤ 1 := by
      have h : √2 ≤ 3 := sq_le_imp_le (Real.sqrt_nonneg 2) (by norm_num)
        (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
      linarith only [h]
    have hsq3_3 : √3 / 3 ≤ 1 := by
      have h : √3 ≤ 3 := sq_le_imp_le (Real.sqrt_nonneg 3) (by norm_num)
        (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
      linarith only [h]
    intro i; fin_cases i
    · change |x0_as| ≤ 3; dsimp only [x0_as]
      have hq1 : |((1 + 2 * C1) / 3) * c0| ≤ 1 := by
        rw [abs_mul]; obtain ⟨hc1_lo, hc1_hi⟩ := abs_le.1 hC1
        have hb : |(1 + 2 * C1) / 3| ≤ 1 := abs_le.2
          ⟨by linarith only [hc1_lo], by linarith only [hc1_hi]⟩
        exact (mul_le_mul hb hc_abs (abs_nonneg _) zero_le_one).trans (by norm_num)
      have hq2 : |(√6 / 3) * S1 * d1| ≤ 1 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ √6 / 3)]
        have hb : (√6 / 3) * |S1| ≤ 1 := (mul_le_mul hsq6_3 hS1 (abs_nonneg _) zero_le_one).trans
          (by norm_num)
        exact (mul_le_mul hb hd1_abs (abs_nonneg _) zero_le_one).trans (by norm_num)
      have hsub := abs_add_le (((1 + 2 * C1) / 3) * c0) (-((√6 / 3) * S1 * d1))
      rw [abs_neg] at hsub; rw [sub_eq_add_neg]; linarith only [hsub, hq1, hq2]
    · change |x1_as| ≤ 3; dsimp only [x1_as]
      have hq1 : |(√6 / 3) * S1 * c0| ≤ 1 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ √6 / 3)]
        have hb : (√6 / 3) * |S1| ≤ 1 := (mul_le_mul hsq6_3 hS1 (abs_nonneg _) zero_le_one).trans
          (by norm_num)
        exact (mul_le_mul hb hc_abs (abs_nonneg _) zero_le_one).trans (by norm_num)
      have hq2 : |C1 * d1| ≤ 1 := by
        rw [abs_mul]; exact (mul_le_mul hC1 hd1_abs (abs_nonneg _) zero_le_one).trans (by norm_num)
      have hab := abs_add_le ((√6 / 3) * S1 * c0) (C1 * d1); linarith only [hab, hq1, hq2]
    · change |x2_as| ≤ 3; dsimp only [x2_as]
      have hq1 : |(√2 / 3) * (1 - C1) * c0| ≤ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ √2 / 3)]
        obtain ⟨hc1_lo, hc1_hi⟩ := abs_le.1 hC1; have h1c : |1 - C1| ≤ 2 := abs_le.2
          ⟨by linarith only [hc1_hi], by linarith only [hc1_lo]⟩
        have hb : (√2 / 3) * |1 - C1| ≤ 2 :=
          (mul_le_mul hsq2_3 h1c (abs_nonneg _) zero_le_one).trans (by norm_num)
        exact (mul_le_mul hb hc_abs (abs_nonneg _) (by norm_num)).trans (by norm_num)
      have hq2 : |(√3 / 3) * S1 * d1| ≤ 1 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ √3 / 3)]
        have hb : (√3 / 3) * |S1| ≤ 1 := (mul_le_mul hsq3_3 hS1 (abs_nonneg _) zero_le_one).trans
          (by norm_num)
        exact (mul_le_mul hb hd1_abs (abs_nonneg _) zero_le_one).trans (by norm_num)
      have hab := abs_add_le ((√2 / 3) * (1 - C1) * c0) ((√3 / 3) * S1 * d1)
      linarith only [hab, hq1, hq2]
  exact ⟨hmid_err, hz_id_bd⟩

private theorem jp01FinalOrbVec_coord_err {n : ℕ} (hn : 200 ≤ n) (γ : ℝ) (t1 t2 : ℕ) :
    let u1 := DickeSol.u1OrbVec (2 ^ n) 2 2
    let u2 := DickeSol.u2OrbVec (2 ^ n) 2 2
    let K1 := DickeSol.p01StepCount t1 (2 ^ n)
    let K2 := DickeSol.p01StepCount t2 (2 ^ n)
    let θ1 := Real.arcsin √((u1 0) ^ 2 + (u1 2) ^ 2)
    let φ2 := Real.arcsin (-u2 1)
    let C1 := Real.cos (2 * (K1 : ℝ) * θ1)
    let S1 := Real.sin (2 * (K1 : ℝ) * θ1)
    let C2 := Real.cos (2 * (K2 : ℝ) * φ2)
    let S2 := Real.sin (2 * (K2 : ℝ) * φ2)
    let c0 := Real.cos γ
    let d1 := Real.sin γ / √2
    let x0_as := ((1 + 2 * C1) / 3) * c0 - (√6 / 3) * S1 * d1
    let x1_as := (√6 / 3) * S1 * c0 + C1 * d1
    let x2_as := (√2 / 3) * (1 - C1) * c0 + (√3 / 3) * S1 * d1
    let y2_as := S2 * x1_as + C2 * x2_as
    let y_final :=
      ((DickeSol.rot3Neg u2)^[K2]) (((DickeSol.rot3Pos u1)^[K1]) (jp01InitOrbVec n γ))
    |y_final 0 - x0_as| ≤ 1 / DickeSol.wdScaleR ∧
      |y_final 2 - y2_as| ≤ 1 / DickeSol.wdScaleR := by
  intro u1 u2 K1 K2 θ1 φ2 C1 S1 C2 S2 c0 d1 x0_as x1_as x2_as y2_as y_final
  obtain ⟨hSN_ge, _⟩ := pow_two_200_bounds hn; set NR : ℝ := (2 : ℝ) ^ n
  have hSN_pos : 0 < √NR := lt_of_lt_of_le (by positivity) hSN_ge
  have hN16 : 16 ≤ 2 ^ n :=
    le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right (by positivity) hn)
  set s2 := √((u2 0) ^ 2 + (u2 2) ^ 2)
  obtain ⟨_, hdu2_r, _, hu2_1_r, _, hs2_pos_r, _⟩ := jp01_m2r2_basis_closed hN16
  obtain ⟨_, _, _, _, hax2_0_r, hax2_2_r⟩ := jp01_m2r2_angles_and_axes_err hn
  have hdu2 : DickeSol.dot3 u2 u2 = 1 := hdu2_r
  have hu2_1_le : u2 1 ≤ 0 := hu2_1_r
  have hs2_pos : 0 < s2 := hs2_pos_r
  have hax2_0 : |u2 0 / s2| ≤ 1 / √NR := hax2_0_r
  have hax2_2 : |u2 2 / s2 - 1| ≤ 1 / √NR := hax2_2_r
  clear hdu2_r hu2_1_r hs2_pos_r hax2_0_r hax2_2_r
  obtain ⟨hmid_err_r, hz_id_bd_r⟩ := jp01InitOrbVec_rot1_err hn γ K1
  set x_mid := ((DickeSol.rot3Pos u1)^[K1]) (jp01InitOrbVec n γ)
  set z_id := DickeSol.vec3 x0_as x1_as x2_as
  have hmid_err : ∀ i, |x_mid i - z_id i| ≤ 37 / √NR := hmid_err_r
  have hz_id_bd : ∀ i, |z_id i| ≤ 3 := hz_id_bd_r
  clear hmid_err_r hz_id_bd_r
  have hu2_norm : |u2 0 / s2| ≤ 1 ∧ |u2 2 / s2| ≤ 1 := by
    have hsum : (u2 0 / s2) ^ 2 + (u2 2 / s2) ^ 2 = 1 := by
      have hs2_2 : (u2 0) ^ 2 + (u2 2) ^ 2 = s2 ^ 2 := by
        dsimp only [s2]; exact (Real.sq_sqrt (by positivity)).symm
      rw [div_pow, div_pow, ← add_div, hs2_2, div_self (pow_ne_zero 2 hs2_pos.ne')]
    exact ⟨abs_le.2 ⟨by nlinarith only [hsum, sq_nonneg (u2 2 / s2)],
      by nlinarith only [hsum, sq_nonneg (u2 2 / s2)]⟩,
      abs_le.2 ⟨by nlinarith only [hsum, sq_nonneg (u2 0 / s2)],
      by nlinarith only [hsum, sq_nonneg (u2 0 / s2)]⟩⟩
  have hy_fin_eq : y_final = rotFrameEval (u2 0 / s2) (u2 2 / s2) C2 S2 x_mid := by
    dsimp only [y_final]; have hcl := DickeSol.rot3Neg_iter_closed hdu2 hu2_1_le hs2_pos K2 x_mid
    dsimp only at hcl; rw [hcl, DickeSol.p01StepCount_even t2 (2 ^ n)]
    refine DickeSol.fin3_ext ?_ ?_ ?_ <;>
      (dsimp only [rotFrameEval, DickeSol.vec3_zero, DickeSol.vec3_one, DickeSol.vec3_two,
        s2, φ2, C2, S2]; ring)
  have hax2_0' : |u2 0 / s2 - 0| ≤ 1 / √NR := by rw [sub_zero]; exact hax2_0
  have hy_err := fun i => rotFrameEval_lipschitz hu2_norm.1 hu2_norm.2
    (by rw [abs_zero]; exact zero_le_one) (by rw [abs_one])
    (show |C2| ≤ 1 from Real.abs_cos_le_one _)
    (show |S2| ≤ 1 from Real.abs_sin_le_one _) hz_id_bd hmid_err
    hax2_0' hax2_2 i
  have h212_le : 212 / √NR ≤ 1 / DickeSol.wdScaleR := by
    rw [jp01WdScaleR_eq, div_le_div_iff₀ hSN_pos (by norm_num)]
    have h212 : (212 : ℝ) * 1000000000000000 ≤ (2 : ℝ) ^ 100 := by norm_num
    linarith only [hSN_ge, h212]
  refine ⟨?_, ?_⟩
  · have h0 := hy_err 0; rw [← hy_fin_eq] at h0
    have has0 : rotFrameEval 0 1 C2 S2 z_id 0 = x0_as := by
      simp only [rotFrameEval, z_id, DickeSol.vec3_zero]; ring
    rw [has0] at h0; exact (h0.trans (le_of_eq (by ring))).trans h212_le
  · have h2 := hy_err 2; rw [← hy_fin_eq] at h2
    have has2 : rotFrameEval 0 1 C2 S2 z_id 2 = y2_as := by
      simp only [rotFrameEval, z_id, y2_as, DickeSol.vec3_one, DickeSol.vec3_two]; ring
    rw [has2] at h2; exact (h2.trans (le_of_eq (by ring))).trans h212_le

private theorem jp01EvalInterval_w0Hi_bound {n sLo : ℕ} {γ : ℝ} (hn : 200 ≤ n)
    (hs_lo : (sLo : ℝ) / DickeSol.wdScaleR ≤ Real.sin γ) :
    1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 ≤
      ((jp01Scale - ((sLo - 1) * (sLo - 1)) / (2 * jp01Scale) : ℕ) : ℝ) /
        DickeSol.wdScaleR := by
  obtain ⟨hSN_ge, hN_ge⟩ := pow_two_200_bounds hn; set NR : ℝ := (2 : ℝ) ^ n
  have hSN_pos : 0 < √NR := lt_of_lt_of_le (by positivity) hSN_ge
  have hNR16 : (16 : ℝ) ≤ NR := le_trans (by norm_num) hN_ge
  have hB : 0 < DickeSol.wdScaleR := jp01WdScaleR_pos
  have hBeq : (jp01Scale : ℝ) = DickeSol.wdScaleR := rfl
  rcases Nat.eq_zero_or_pos sLo with rfl | hsLo_pos
  · simp only [Nat.zero_sub, zero_mul, Nat.zero_div, Nat.sub_zero, hBeq, div_self hB.ne']
    linarith only [sq_nonneg (Real.sin (γ - halfAngleSet n 2))]
  · set sLoPad : ℕ := sLo - 1
    have hsLo_le : sLo ≤ jp01Scale := by
      have hsin1 : Real.sin γ ≤ 1 := Real.sin_le_one γ
      have hm : (sLo : ℝ) ≤ DickeSol.wdScaleR := by
        have hd := (div_le_iff₀ hB).1 (hs_lo.trans hsin1); linarith only [hd]
      rw [← hBeq] at hm; exact_mod_cast hm
    have hpad_le : sLoPad ≤ jp01Scale := by omega
    have hq_le : (sLoPad * sLoPad) / (2 * jp01Scale) ≤ jp01Scale := by
      apply Nat.div_le_of_le_mul; have hsc_pos : 0 < jp01Scale := by norm_num [jp01Scale]
      nlinarith only [hpad_le, hsc_pos]
    have hθ2_le : halfAngleSet n 2 ≤ 1 / DickeSol.wdScaleR := by
      have hn100 : 100 ≤ n := by omega
      obtain ⟨_, hθ2_hi, -⟩ :=
        halfAngleSet_bounds_100 hn100 (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 1024)
      rw [Nat.cast_ofNat] at hθ2_hi
      have hsq2_2 : √(2 : ℝ) ≤ 2 := sq_le_imp_le (Real.sqrt_nonneg 2) (by norm_num)
        (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
      have h1 : halfAngleSet n 2 ≤ 4 / √NR := by
        have h2_16 : (2 : ℝ) / NR ≤ 2 / 16 :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hNR16
        have hf : (1 : ℝ) + (2 : ℝ) / NR ≤ 2 := by linarith only [h2_16]
        calc halfAngleSet n 2 ≤ (√(2 : ℝ) / √NR) * (1 + (2 : ℝ) / NR) := hθ2_hi
          _ ≤ (2 / √NR) * 2 := mul_le_mul (div_le_div_of_nonneg_right hsq2_2 hSN_pos.le) hf
              (by positivity) (by positivity)
          _ = 4 / √NR := by ring
      refine h1.trans ?_
      rw [jp01WdScaleR_eq, div_le_div_iff₀ hSN_pos (by norm_num)]
      have h4 : (4 : ℝ) * 1000000000000000 ≤ (2 : ℝ) ^ 100 := by norm_num
      linarith only [hSN_ge, h4]
    have hpad_sin : (sLoPad : ℝ) / DickeSol.wdScaleR ≤ Real.sin (γ - halfAngleSet n 2) := by
      have hsub_cast : (sLoPad : ℝ) = (sLo : ℝ) - 1 := by
        dsimp [sLoPad]; rw [Nat.cast_sub hsLo_pos, Nat.cast_one]
      have hlip := Real.abs_sin_sub_sin_le (γ - halfAngleSet n 2) γ
      have hdiff_eq : (γ - halfAngleSet n 2) - γ = -halfAngleSet n 2 := by ring
      have hθ2_nn : 0 ≤ halfAngleSet n 2 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
      rw [hdiff_eq, abs_neg, abs_of_nonneg hθ2_nn] at hlip; have hl2 := (abs_sub_le_iff.1 hlip).2
      have hsin_ge : Real.sin γ - halfAngleSet n 2 ≤ Real.sin (γ - halfAngleSet n 2) := by
        linarith only [hl2]
      rw [hsub_cast, sub_div]; linarith only [hs_lo, hθ2_le, hsin_ge]
    have hpad_sq : (((sLoPad * sLoPad) / (2 * jp01Scale) : ℕ) : ℝ) / DickeSol.wdScaleR ≤
        Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 := by
      have hdiv_le : (((sLoPad * sLoPad) / (2 * jp01Scale) : ℕ) : ℝ) ≤
          ((sLoPad : ℝ) * sLoPad) / (2 * DickeSol.wdScaleR) := by
        rw [le_div_iff₀ (by positivity), ← hBeq]
        exact_mod_cast Nat.div_mul_le_self (sLoPad * sLoPad) (2 * jp01Scale)
      calc (((sLoPad * sLoPad) / (2 * jp01Scale) : ℕ) : ℝ) / DickeSol.wdScaleR
          ≤ (((sLoPad : ℝ) * sLoPad) / (2 * DickeSol.wdScaleR)) / DickeSol.wdScaleR :=
            div_le_div_of_nonneg_right hdiv_le hB.le
        _ = ((sLoPad : ℝ) / DickeSol.wdScaleR) ^ 2 / 2 := by rw [div_div, div_pow]; ring
        _ ≤ Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 := div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hpad_sin 2) (by norm_num)
    rw [Nat.cast_sub hq_le, sub_div, hBeq, div_self hB.ne']; linarith only [hpad_sq]

private lemma peel_wfSNIVal {α : Type} {lhs : α} {v : SNIVal} {f : SNIVal → α}
    (h : lhs = withForcedSNIVal v f) : ∃ x : SNIVal, x = v ∧ lhs = f x :=
  ⟨v, rfl, h.trans (withForcedSNIVal_eq v f)⟩

private theorem jp01EvalInterval_sound {n sLo sHi c0Lo c0Hi t1 t2 : ℕ} {γ : ℝ} (hn : 200 ≤ n) (hsq :
  snMem √2 jp01Sq2IV ∧ snMem √3 jp01Sq3IV ∧ snMem √6 jp01Sq6IV) (_hγ0 : 0 ≤ γ) (_hγ_hi : γ ≤ 5 / 4)
  (hs_lo : (sLo : ℝ) / DickeSol.wdScaleR ≤ Real.sin γ) (hs_hi : Real.sin γ ≤ (sHi : ℝ) /
  DickeSol.wdScaleR) (hc_lo : (c0Lo : ℝ) / DickeSol.wdScaleR ≤ Real.cos γ) (hc_hi : Real.cos γ ≤
  (c0Hi : ℝ) / DickeSol.wdScaleR) (heval : (jp01EvalInterval sLo sHi c0Lo c0Hi t1 t2).1 = true) :
    let out := (jp01EvalInterval sLo sHi c0Lo c0Hi t1 t2).2; let p0Hi := out.1; let p2Lo := out.2.1
    let w0Hi := out.2.2; let u1 := DickeSol.u1OrbVec (2 ^ n) 2 2
    let u2 := DickeSol.u2OrbVec (2 ^ n) 2 2; let K1 := DickeSol.p01StepCount t1 (2 ^ n)
    let K2 := DickeSol.p01StepCount t2 (2 ^ n)
    let y_final :=
      ((DickeSol.rot3Neg u2)^[K2]) (((DickeSol.rot3Pos u1)^[K1]) (jp01InitOrbVec n γ))
    t1 ≤ 4000000000000 ∧ t2 ≤ 4000000000000 ∧ (y_final 0) ^ 2 ≤ (p0Hi : ℝ) / DickeSol.wdScaleR ∧
      (p2Lo : ℝ) / DickeSol.wdScaleR ≤ (y_final 2) ^ 2 ∧
      1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 ≤ (w0Hi : ℝ) / DickeSol.wdScaleR := by
  intro out p0Hi p2Lo w0Hi u1 u2 K1 K2 y_final
  obtain ⟨ev, hev⟩ : ∃ x, x = jp01EvalInterval sLo sHi c0Lo c0Hi t1 t2 := ⟨_, rfl⟩
  have hev1 : ev.1 = true := by rw [hev]; exact heval
  have hout_ev : out = ev.2 := by
    change (jp01EvalInterval sLo sHi c0Lo c0Hi t1 t2).2 = ev.2; rw [← hev]
  have hp0_out : p0Hi = ev.2.1 := congrArg Prod.fst hout_ev
  have hp2_out : p2Lo = ev.2.2.1 := congrArg (fun z => z.2.1) hout_ev
  have hw0_out : w0Hi = ev.2.2.2 := congrArg (fun z => z.2.2) hout_ev
  rw [jp01EvalInterval.eq_def] at hev
  by_cases htau_b : (Nat.ble t1 4000000000000 && Nat.ble t2 4000000000000) = true
  swap
  · rw [Bool.eq_false_iff.2 htau_b, Bool.not_false, Bool.cond_true] at hev
    rw [hev] at hev1; simp at hev1
  rw [htau_b, Bool.not_true, Bool.cond_false] at hev
  obtain ⟨ht1_le, ht2_le⟩ : t1 ≤ 4000000000000 ∧ t2 ≤ 4000000000000 := by
    simpa [Bool.and_eq_true, Nat.ble_eq] using htau_b
  obtain ⟨th1IV, hth1IV, hev⟩ := peel_wfSNIVal hev
  obtain ⟨th2IV, hth2IV, hev⟩ := peel_wfSNIVal hev
  obtain ⟨cap, hcap⟩ : ∃ x : SNat, x = (false, 1024 * jp01Scale) := ⟨_, rfl⟩
  obtain ⟨cs1, hcs1⟩ : ∃ x, x = snTrig th1IV := ⟨_, rfl⟩
  obtain ⟨cs2, hcs2⟩ : ∃ x : SNIVal × SNIVal, x = cond (Nat.blt 0 t2) (snTrig th2IV)
    ((snScaleOne, snScaleOne), (snZero, snZero)) := ⟨_, rfl⟩
  obtain ⟨sIV, hsIV⟩ : ∃ x : SNIVal, x = ((false, sLo), (false, sHi)) := ⟨_, rfl⟩
  obtain ⟨c0IV, hc0IV⟩ : ∃ x : SNIVal, x = ((false, c0Lo), (false, c0Hi)) := ⟨_, rfl⟩
  obtain ⟨invSq2, hinvSq2⟩ : ∃ x : SNIVal, x =
    (snDivFloor jp01Sq2IV.1 2, snDivCeil jp01Sq2IV.2 2) := ⟨_, rfl⟩
  obtain ⟨oneIV, honeIV⟩ : ∃ x : SNIVal, x = (snScaleOne, snScaleOne) := ⟨_, rfl⟩
  obtain ⟨kS23, hkS23⟩ : ∃ x : SNIVal, x =
    (snDivFloor jp01Sq6IV.1 3, snDivCeil jp01Sq6IV.2 3) := ⟨_, rfl⟩
  obtain ⟨kR23, hkR23⟩ : ∃ x : SNIVal, x =
    (snDivFloor jp01Sq2IV.1 3, snDivCeil jp01Sq2IV.2 3) := ⟨_, rfl⟩
  obtain ⟨kR13, hkR13⟩ : ∃ x : SNIVal, x =
    (snDivFloor jp01Sq3IV.1 3, snDivCeil jp01Sq3IV.2 3) := ⟨_, rfl⟩
  rw [← hcap, ← hcs1, ← hcs2, ← hsIV, ← hc0IV, ← hinvSq2, ← honeIV,
    ← hkS23, ← hkR23, ← hkR13] at hev
  dsimp -zetaDelta only at hev
  by_cases hcap_b : (snLe th1IV.2 cap && snLe th2IV.2 cap) = true
  swap
  · rw [Bool.eq_false_iff.2 hcap_b, Bool.not_false, Bool.cond_true] at hev
    rw [hev] at hev1; simp at hev1
  rw [hcap_b, Bool.not_true, Bool.cond_false] at hev
  obtain ⟨c1IV, hc1IV, hev⟩ := peel_wfSNIVal hev
  obtain ⟨x0IV, hx0IV, hev⟩ := peel_wfSNIVal hev
  obtain ⟨numQ, hnumQ⟩ : ∃ x : SNIVal, x = snAddIV oneIV (snScaleNatIV 2 cs1.1) := ⟨_, rfl⟩
  rw [← hnumQ] at hx0IV
  obtain ⟨kQ02, hkQ02⟩ : ∃ x : SNIVal, x = (snDivFloor numQ.1 3, snDivCeil numQ.2 3) := ⟨_, rfl⟩
  rw [← hkQ02] at hx0IV
  obtain ⟨x1IV, hx1IV, hev⟩ := peel_wfSNIVal hev
  obtain ⟨x2IV, hx2IV, hev⟩ := peel_wfSNIVal hev
  obtain ⟨oneSubC1, honeSubC1⟩ : ∃ x : SNIVal, x = snSubIV oneIV cs1.1 := ⟨_, rfl⟩
  rw [← honeSubC1] at hx2IV
  obtain ⟨y2IV, hy2IV, hev⟩ := peel_wfSNIVal hev
  obtain ⟨p0Sq, hp0Sq, hev⟩ := peel_wfSNIVal hev
  obtain ⟨f0IV, hf0IV⟩ : ∃ x : SNIVal, x =
    (snSub x0IV.1 (false, 1), snAdd x0IV.2 (false, 1)) := ⟨_, rfl⟩
  rw [← hf0IV] at hp0Sq
  obtain ⟨p2Sq, hp2Sq, hev⟩ := peel_wfSNIVal hev
  obtain ⟨f2IV, hf2IV⟩ : ∃ x : SNIVal, x =
    (snSub y2IV.1 (false, 1), snAdd y2IV.2 (false, 1)) := ⟨_, rfl⟩
  rw [← hf2IV] at hp2Sq
  by_cases hp0_b : snLe snZero p0Sq.2 = true
  swap
  · rw [Bool.eq_false_iff.2 hp0_b, Bool.not_false, Bool.cond_true] at hev
    rw [hev] at hev1; simp at hev1
  rw [hp0_b, Bool.not_true, Bool.cond_false] at hev
  rw [hev] at hp0_out hp2_out hw0_out
  set NR : ℝ := (2 : ℝ) ^ n
  set θ1 := Real.arcsin √((u1 0) ^ 2 + (u1 2) ^ 2); set φ2 := Real.arcsin (-u2 1)
  obtain ⟨harc1_r, harc2_r, _, _, _, _⟩ := jp01_m2r2_angles_and_axes_err hn
  have harc1 : |θ1 - √6 / √NR| ≤ 32 / (NR * √NR) := harc1_r
  have harc2 : |φ2 - √2 / √NR| ≤ 32 / (NR * √NR) := harc2_r
  clear harc1_r harc2_r
  have hsq6_ge1 : (1 : ℝ) ≤ √6 := sq_le_imp_le zero_le_one (Real.sqrt_nonneg 6)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
  have hsq2_ge1 : (1 : ℝ) ≤ √2 := sq_le_imp_le zero_le_one (Real.sqrt_nonneg 2)
    (by rw [Real.sq_sqrt (by norm_num)]; norm_num)
  have hth1_pair := jp01AngleIV_mem hn ht1_le hsq6_ge1 hsq.2.2 harc1
  rw [← hth1IV] at hth1_pair; obtain ⟨hth1_0, hth1_mem⟩ := hth1_pair
  have hth2_pair := jp01AngleIV_mem hn ht2_le hsq2_ge1 hsq.1 harc2
  rw [← hth2IV] at hth2_pair; obtain ⟨hth2_0, hth2_mem⟩ := hth2_pair
  obtain ⟨hcap1, hcap2⟩ : snToInt th1IV.2 ≤ 1024 * (DickeSol.wdScale : ℤ) ∧
      snToInt th2IV.2 ≤ 1024 * (DickeSol.wdScale : ℤ) := by
    rw [hcap, Bool.and_eq_true, snLe_iff, snLe_iff] at hcap_b
    simpa [snToInt, jp01Scale, DickeSol.wdScale] using hcap_b
  have hcs1_pair := snTrig_mem hth1_0 hcap1 hth1_mem
  rw [← hcs1] at hcs1_pair; obtain ⟨hc1_mem, hs1_mem⟩ := hcs1_pair
  set C1 := Real.cos (2 * (K1 : ℝ) * θ1); set S1 := Real.sin (2 * (K1 : ℝ) * θ1)
  set C2 := Real.cos (2 * (K2 : ℝ) * φ2); set S2 := Real.sin (2 * (K2 : ℝ) * φ2)
  have hone_mem : snMem 1 oneIV := by
    rw [honeIV]; unfold snMem snToWDIVal snScaleOne snToInt; rw [jp01Scale_eq_wdScale]
    exact DickeSol.wdMem_one
  have hcs2_mem : snMem C2 cs2.1 ∧ snMem S2 cs2.2 := by
    rw [hcs2]; by_cases ht2_pos : 0 < t2
    · rw [Nat.blt_eq.mpr ht2_pos, Bool.cond_true]; exact snTrig_mem hth2_0 hcap2 hth2_mem
    · have ht2_z : t2 = 0 := by omega
      rw [Bool.eq_false_iff.2 (mt Nat.blt_eq.mp ht2_pos), Bool.cond_false]
      have hK2_z : K2 = 0 := by simp [K2, ht2_z]
      have hc2_1 : C2 = 1 := by simp [C2, hK2_z]
      have hs2_0 : S2 = 0 := by simp [S2, hK2_z]
      rw [hc2_1, hs2_0]
      refine ⟨?_, by simp [snMem, snToWDIVal, snZero, snToInt, DickeSol.wdMem]⟩
      change snMem 1 (snScaleOne, snScaleOne); rw [← honeIV]; exact hone_mem
  have hsIV_mem : snMem (Real.sin γ) sIV := by
    rw [hsIV]; unfold snMem DickeSol.wdMem; simpa [snToWDIVal, snToInt] using ⟨hs_lo, hs_hi⟩
  have hc0IV_mem : snMem (Real.cos γ) c0IV := by
    rw [hc0IV]; unfold snMem DickeSol.wdMem; simpa [snToWDIVal, snToInt] using ⟨hc_lo, hc_hi⟩
  have hinvSq2_mem : snMem (1 / √2) invSq2 := by
    rw [hinvSq2]
    have heq : (1 : ℝ) / √2 = √2 / 2 := by
      field_simp [show (√2 : ℝ) ≠ 0 by positivity]; rw [Real.sq_sqrt (by norm_num)]
    rw [heq]; exact snDiv_nat_mem (by norm_num : 0 < 2) hsq.1
  have hc1IV_mem : snMem (Real.sin γ / √2) c1IV := by
    rw [hc1IV, div_eq_mul_one_div]; exact snMem_mul hsIV_mem hinvSq2_mem
  have h2c1 : snMem (2 * C1) (snScaleNatIV 2 cs1.1) := by
    have h := snMem_scaleNat 2 hc1_mem; rwa [Nat.cast_ofNat] at h
  have hnumQ_mem : snMem (1 + 2 * C1) numQ := by
    rw [hnumQ]; exact snMem_add hone_mem h2c1
  have hkQ02_mem : snMem ((1 + 2 * C1) / 3) kQ02 := by
    rw [hkQ02]; exact snDiv_nat_mem (by norm_num : 0 < 3) hnumQ_mem
  have hkS23_mem : snMem (√6 / 3) kS23 := by
    rw [hkS23]; exact snDiv_nat_mem (by norm_num : 0 < 3) hsq.2.2
  have hkR23_mem : snMem (√2 / 3) kR23 := by
    rw [hkR23]; exact snDiv_nat_mem (by norm_num : 0 < 3) hsq.1
  have hkR13_mem : snMem (√3 / 3) kR13 := by
    rw [hkR13]; exact snDiv_nat_mem (by norm_num : 0 < 3) hsq.2.1
  have honeSubC1_mem : snMem (1 - C1) oneSubC1 := by
    rw [honeSubC1]; exact snMem_sub hone_mem hc1_mem
  set d1 := Real.sin γ / √2; set c0 := Real.cos γ
  set x0_as := ((1 + 2 * C1) / 3) * c0 - (√6 / 3) * S1 * d1 with hx0_as_def
  set x1_as := (√6 / 3) * S1 * c0 + C1 * d1 with hx1_as_def
  set x2_as := (√2 / 3) * (1 - C1) * c0 + (√3 / 3) * S1 * d1 with hx2_as_def
  set y2_as := S2 * x1_as + C2 * x2_as with hy2_as_def
  have hx0_mem : snMem x0_as x0IV := by
    rw [hx0_as_def, hx0IV]; exact snMem_sub (snMem_mul hkQ02_mem hc0IV_mem)
      (snMem_mul (snMem_mul hkS23_mem hs1_mem) hc1IV_mem)
  have hx1_mem : snMem x1_as x1IV := by
    rw [hx1_as_def, hx1IV]; exact snMem_add (snMem_mul (snMem_mul hkS23_mem hs1_mem) hc0IV_mem)
      (snMem_mul hc1_mem hc1IV_mem)
  have hx2_mem : snMem x2_as x2IV := by
    rw [hx2_as_def, hx2IV]
    have h1sub : (√2 / 3) * (1 - C1) * c0 = ((√2 / 3) * (1 - C1)) * c0 := by ring
    rw [h1sub]
    exact snMem_add (snMem_mul (snMem_mul hkR23_mem honeSubC1_mem) hc0IV_mem)
      (snMem_mul (snMem_mul hkR13_mem hs1_mem) hc1IV_mem)
  have hy2_mem : snMem y2_as y2IV := by
    rw [hy2_as_def, hy2IV]
    exact snMem_add (snMem_mul hcs2_mem.2 hx1_mem) (snMem_mul hcs2_mem.1 hx2_mem)
  obtain ⟨hd0_r, hd2_r⟩ := jp01FinalOrbVec_coord_err hn γ t1 t2
  have hd0 : |y_final 0 - x0_as| ≤ 1 / DickeSol.wdScaleR := hd0_r
  have hd2 : |y_final 2 - y2_as| ≤ 1 / DickeSol.wdScaleR := hd2_r
  clear hd0_r hd2_r
  have hy0_mem : snMem (y_final 0) f0IV := by
    rw [hf0IV]; unfold snMem DickeSol.wdMem at hx0_mem ⊢
    dsimp -zetaDelta only [snToWDIVal] at hx0_mem ⊢
    have hsn1 : snToInt (false, 1) = 1 := rfl; rw [snToInt_sub, snToInt_add, hsn1]
    obtain ⟨hd1, hd2'⟩ := abs_sub_le_iff.1 hd0; obtain ⟨hx1, hx2⟩ := hx0_mem; constructor
    · rw [Int.cast_sub, Int.cast_one, sub_div]; linarith only [hx1, hd2']
    · rw [Int.cast_add, Int.cast_one, add_div]; linarith only [hx2, hd1]
  have hy2f_mem : snMem (y_final 2) f2IV := by
    rw [hf2IV]; unfold snMem DickeSol.wdMem at hy2_mem ⊢
    dsimp -zetaDelta only [snToWDIVal] at hy2_mem ⊢
    have hsn1 : snToInt (false, 1) = 1 := rfl; rw [snToInt_sub, snToInt_add, hsn1]
    obtain ⟨hd1, hd2'⟩ := abs_sub_le_iff.1 hd2; obtain ⟨hy1, hy2⟩ := hy2_mem; constructor
    · rw [Int.cast_sub, Int.cast_one, sub_div]; linarith only [hy1, hd2']
    · rw [Int.cast_add, Int.cast_one, add_div]; linarith only [hy2, hd1]
  have hp0Sq_mem : snMem ((y_final 0) ^ 2) p0Sq := by rw [hp0Sq]; exact snMem_sq hy0_mem
  have hp2Sq_mem : snMem ((y_final 2) ^ 2) p2Sq := by rw [hp2Sq]; exact snMem_sq hy2f_mem
  refine ⟨ht1_le, ht2_le, ?_, ?_, ?_⟩
  · -- `(y_final 0)^2 ≤ p0Hi / 10^15`
    have hhi := hp0Sq_mem.2
    have h0_le : 0 ≤ snToInt p0Sq.2 := by
      simpa [snZero, snToInt] using (snLe_iff snZero p0Sq.2).1 hp0_b
    have heq_p0 : (p0Hi : ℝ) = (snToInt p0Sq.2 : ℝ) := by
      rw [hp0_out]; change ((cond p0Sq.2.1 0 p0Sq.2.2 : ℕ) : ℝ) = _
      rcases hq : p0Sq.2 with ⟨b, m⟩; rw [hq] at h0_le
      cases b
      · simp [snToInt]
      · have hneg : snToInt (true, m) = -(m : ℤ) := by simp [snToInt]
        rw [hneg] at h0_le ⊢
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero (Nat.cast_le.mp
          (show (m : ℤ) ≤ ((0 : ℕ) : ℤ) by rw [Nat.cast_zero]; linarith only [h0_le]))
        simp [hm0]
    rw [heq_p0]; exact hhi
  · -- `p2Lo / 10^15 ≤ (y_final 2)^2`
    have hlo := hp2Sq_mem.1; have hB : 0 < DickeSol.wdScaleR := jp01WdScaleR_pos
    have heq_p2 : (p2Lo : ℝ) = (max 0 (snToInt p2Sq.1) : ℤ) := by
      rw [hp2_out]; change (((snMaxZero p2Sq.1).2 : ℕ) : ℝ) = _
      rcases p2Sq.1 with ⟨b, m⟩
      cases b <;> simp [snMaxZero, snZero, snToInt]
    rw [heq_p2, Int.cast_max, Int.cast_zero, div_le_iff₀ hB]
    exact max_le (mul_nonneg (sq_nonneg _) hB.le) ((div_le_iff₀ hB).1 hlo)
  · -- `1 - sin(γ - θ₂)^2 / 2 ≤ w0Hi / 10^15`
    have hw0_eq : w0Hi = jp01Scale - ((sLo - 1) * (sLo - 1)) / (2 * jp01Scale) := hw0_out
    rw [hw0_eq]; exact jp01EvalInterval_w0Hi_bound hn hs_lo
private noncomputable def warmJP01BinIdx (γ : ℝ) : ℕ := min 419 ⌊512 * Real.sin γ⌋₊
private noncomputable def warmJP01Guard (n : ℕ) (betas : Fin 2 → ℝ) : Prop :=
  (betas s0 = halfAngleSet n 2 ∨ betas s1 = halfAngleSet n 2) ∧
    halfAngleSet n 2 ≤ betas s0 ∧ halfAngleSet n 2 ≤ betas s1 ∧
    Real.sin (max (betas s0) (betas s1)) < 420 / 512 ∧
    max (betas s0) (betas s1) ≤ 5 / 4
private noncomputable def warmJP01R2Cost2 (v2m : ℕ → ℕ) (n : ℕ) (betas : Fin 2 → ℝ) : ℝ :=
  open Classical in
  if warmJP01Guard n betas then
    ((v2m (warmJP01BinIdx (max (betas s0) (betas s1))) : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)
  else
    2 * √((2 : ℝ) ^ n)
private theorem warmJP01R2Cost2_nonneg (v2m : ℕ → ℕ) (n : ℕ) (betas : Fin 2 → ℝ) : 0 ≤
  warmJP01R2Cost2 v2m n betas := by dsimp only [warmJP01R2Cost2]; split_ifs <;> positivity
private theorem warmJP01V2Mono_anti {cv2 : ℕ} {rows : ℕ → WarmJP01Row} {v2m : ℕ → ℕ} (hall :
  allRange (checkWarmJP01RowAt cv2 rows v2m) 420 = true) : ∀ {i j : ℕ}, i ≤ j → j < 420 → v2m j ≤
  v2m i := by
  intro i j hij hj
  induction j with
  | zero => have hi0 : i = 0 := (by omega); subst hi0; exact le_rfl
  | succ m ih =>
    by_cases hij' : i ≤ m
    · have hm_lt : m < 420 := (by omega)
      have hrow := of_allRange hall hm_lt; dsimp only [checkWarmJP01RowAt] at hrow
      rcases hm_r : rows m with ⟨sLo, sHi, c0Lo, c0Hi, t1, t2, rawV2⟩; rw [hm_r] at hrow
      rcases hev : jp01EvalInterval sLo sHi c0Lo c0Hi t1 t2 with ⟨ok, p0Hi, p2Lo, w0Hi⟩
      rw [hev] at hrow; simp only [withForcedNat_eq, Bool.and_eq_true, and_assoc] at hrow
      rcases hrow with ⟨_, _, _, _, _, _, _, _, _, _, _, hstep_b⟩
      have hlt_b : Nat.blt (m + 1) 420 = true := Nat.blt_eq.mpr hj; rw [hlt_b, Bool.cond_true,
        Nat.ble_eq] at hstep_b; exact hstep_b.trans (ih hij' hm_lt)
    · have hieq : i = m + 1 := (by omega); subst hieq; exact le_rfl
private theorem warmJP01Table_cold_and_warm_sound {ct1 ct2 cv2 n : ℕ} {rows : ℕ → WarmJP01Row} {v2m
  : ℕ → ℕ} (htbl : checkWarmJP01R2Table ct1 ct2 cv2 rows v2m = true) (hn : 200 ≤ n) :
    let u1 := DickeSol.u1OrbVec (2 ^ n) 2 2; let u2 := DickeSol.u2OrbVec (2 ^ n) 2 2
    let B_fuel := fun f : ℕ => ((cv2 - 1 : ℕ) : ℝ) / 1000000000000 + (1 / 5 : ℝ) ^ f * 2
    (∀ i < 420, ∀ j < 420, i ≤ j → v2m j ≤ v2m i) ∧
    2 ≤ B_fuel 0 ∧
    B_fuel 25 ≤ (cv2 : ℝ) / 1000000000000 ∧
    (∀ f : ℕ,
      let yC := ((DickeSol.rot3Neg u2)^[DickeSol.p01StepCount ct2 (2 ^ n)])
        (((DickeSol.rot3Pos u1)^[DickeSol.p01StepCount ct1 (2 ^ n)])
          (jp01InitOrbVec n (halfAngleSet n 2)))
      ((DickeSol.p01StepCount ct1 (2 ^ n) + DickeSol.p01StepCount ct2 (2 ^ n) : ℕ) : ℝ) + 2 +
        ((1 - (yC 2) ^ 2 - (yC 0) ^ 2) * ((cswapZeroHitNat : ℝ) / 1000000000000) +
          (yC 0) ^ 2 * B_fuel f) * √((2 : ℝ) ^ n) ≤
        B_fuel (f + 1) * √((2 : ℝ) ^ n)) ∧
    (∀ γ : ℝ, halfAngleSet n 2 ≤ γ → γ ≤ 5 / 4 → Real.sin γ < 420 / 512 →
      let idx := warmJP01BinIdx γ; let r := rows idx
      let yW := ((DickeSol.rot3Neg u2)^[DickeSol.p01StepCount r.tau2_12 (2 ^ n)])
        (((DickeSol.rot3Pos u1)^[DickeSol.p01StepCount r.tau1_12 (2 ^ n)]) (jp01InitOrbVec n γ))
      (1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2) * ((DickeSol.p01StepCount r.tau1_12 (2 ^ n) +
        DickeSol.p01StepCount r.tau2_12 (2 ^ n) : ℕ) : ℝ) + 2 + ((1 - (yW 2) ^ 2 - (yW 0) ^ 2) *
        ((cswapZeroHitNat : ℝ) / 1000000000000) + (yW 0) ^ 2 * ((cv2 : ℝ) / 1000000000000)) * √((2 :
        ℝ) ^ n) ≤ ((v2m idx : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)) := by
  intro u1 u2 B_fuel; dsimp only [checkWarmJP01R2Table] at htbl
  rcases hce : jp01EvalInterval 0 1 (jp01Scale - 1) jp01Scale ct1 ct2 with ⟨okC, p0C, p2C, w0C⟩
  rw [hce] at htbl; simp only [Bool.and_eq_true, and_assoc, Nat.blt_eq, Nat.ble_eq] at htbl
  rcases htbl with ⟨hzh_lt, hcv2_hi, h2lo, h2hi, h3lo, h3hi, h6lo, h6hi, hokC, hpm_cap, hsumC_le,
    hrecC, hall⟩; have hsq := jp01_sq_consts_mem h2lo h2hi h3lo h3hi h6lo h6hi; obtain ⟨hSN_ge,
    hN_ge⟩ := pow_two_200_bounds hn; set SN : ℝ := √((2 : ℝ) ^ n); have hSN_pos : 0 < SN :=
    lt_of_lt_of_le (by positivity) hSN_ge
  have h2_le_pad : (2 : ℝ) ≤ (1 / 1000000000000) * SN := by
    have h2 : (2 : ℝ) * 1000000000000 ≤ (2 : ℝ) ^ 100 := (by norm_num); linarith only [hSN_ge, h2]
  have hcv2_pos : 1 ≤ cv2 := (by omega); refine ⟨fun i _ j hj hij => warmJP01V2Mono_anti hall hij
    hj, ?_, ?_, ?_, ?_⟩
  · dsimp only [B_fuel]; rw [pow_zero]; have h0 : (0 : ℝ) ≤ ((cv2 - 1 : ℕ) : ℝ) / 1000000000000 :=
      (by positivity); linarith only [h0]
  · dsimp only [B_fuel]; rw [Nat.cast_sub hcv2_pos, Nat.cast_one]; have h25 : (1 / 5 : ℝ) ^ 25 * 2 ≤
      1 / 1000000000000 := (by norm_num); linarith only [h25]
  · -- Cold recurrence step
    intro f yC; set θ2 := halfAngleSet n 2
    have hθ2_0 : 0 ≤ θ2 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); have hn100 : 100 ≤ n :=
      (by omega)
    obtain ⟨_, _, hθ2_13, -⟩ := halfAngleSet_bounds_100 hn100 (by norm_num : 1 ≤ 2)
      (by norm_num : 2 ≤ 1024)
    have hsin_θ2 : Real.sin θ2 = √(2 / (2 : ℝ) ^ n) := by
      dsimp only [θ2, halfAngleSet]; rw [Nat.cast_ofNat]
      have hrt0 : (0 : ℝ) ≤ √(2 / (2 : ℝ) ^ n) := Real.sqrt_nonneg _
      have hdiv1 : (2 : ℝ) / (2 : ℝ) ^ n ≤ 1 := by
        rw [div_le_one (by positivity)]; have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ 200 := (by norm_num)
        linarith only [hN_ge, h2]
      exact Real.sin_arcsin (by linarith only [hrt0]) (Real.sqrt_le_one.2 hdiv1)
    have hsC_hi : Real.sin θ2 ≤ 1 / DickeSol.wdScaleR := by
      rw [hsin_θ2]; refine sq_le_imp_le (Real.sqrt_nonneg _) (by positivity) ?_; rw [Real.sq_sqrt
        (by positivity), div_pow, one_pow, jp01WdScaleR_eq, div_le_div_iff₀ (by positivity)
        (by norm_num)]; have h2 : (2 : ℝ) * 1000000000000000 ^ 2 ≤ (2 : ℝ) ^ 200 := (by norm_num)
      linarith only [hN_ge, h2]
    have hcC_lo : ((jp01Scale - 1 : ℕ) : ℝ) / DickeSol.wdScaleR ≤ Real.cos θ2 := by
      have hc_pos : 0 ≤ Real.cos θ2 := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith only [Real.pi_gt_three, hθ2_0],
         by linarith only [Real.pi_gt_three, hθ2_13]⟩
      have hcsq : Real.cos θ2 ^ 2 = 1 - 2 / (2 : ℝ) ^ n := by
        have h1 := Real.sin_sq_add_cos_sq θ2; rw [hsin_θ2, Real.sq_sqrt (by positivity)] at h1
        linarith only [h1]
      have hlhs_le : ((jp01Scale - 1 : ℕ) : ℝ) / DickeSol.wdScaleR = 1 - 1 / DickeSol.wdScaleR := by
        have h1 : 1 ≤ jp01Scale := (by norm_num [jp01Scale]); rw [Nat.cast_sub h1, Nat.cast_one,
          sub_div]; have hBeq : (jp01Scale : ℝ) = DickeSol.wdScaleR := rfl; rw [hBeq, div_self
          jp01WdScaleR_pos.ne']
      rw [hlhs_le]
      have h2N : 2 / (2 : ℝ) ^ n ≤ 1 / DickeSol.wdScaleR := by
        rw [jp01WdScaleR_eq, div_le_div_iff₀ (by positivity) (by norm_num)]; have h2 : (2 : ℝ) *
          1000000000000000 ≤ (2 : ℝ) ^ 200 := (by norm_num); linarith only [hN_ge, h2]
      have hcsq_le : Real.cos θ2 ^ 2 ≤ Real.cos θ2 :=
        (by have hc1 := Real.cos_le_one θ2; nlinarith only [hc_pos, hc1]); linarith only [hcsq, h2N,
        hcsq_le]
    have hθ2_54 : θ2 ≤ 5 / 4 := (by linarith only [hθ2_13])
    obtain ⟨_, _, hp0_le, hp2_ge, _⟩ := jp01EvalInterval_sound hn hsq hθ2_0 hθ2_54
      (by rw [Nat.cast_zero, zero_div]
          exact Real.sin_nonneg_of_nonneg_of_le_pi hθ2_0
            (by linarith only [Real.pi_gt_three, hθ2_54]))
      (show Real.sin θ2 ≤ ((1 : ℕ) : ℝ) / DickeSol.wdScaleR by rw [Nat.cast_one]; exact hsC_hi)
      hcC_lo (by
        have hBeq : (jp01Scale : ℝ) = DickeSol.wdScaleR := rfl; rw [hBeq, div_self
          jp01WdScaleR_pos.ne']
        exact Real.cos_le_one θ2)
      (by rw [hce]; exact hokC)
    rw [hce] at hp0_le hp2_ge; dsimp only at hp0_le hp2_ge; set pmR : ℝ := ((p0C + 1 : ℕ) : ℝ) /
      DickeSol.wdScaleR; set p2R : ℝ := (p2C : ℝ) / DickeSol.wdScaleR; set zhR : ℝ :=
      (cswapZeroHitNat : ℝ) / 1000000000000; set bsR : ℝ := ((cv2 - 1 : ℕ) : ℝ) / 1000000000000
    have hq0_le_pm : (yC 0) ^ 2 ≤ pmR := hp0_le.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.le_succ p0C) jp01WdScaleR_pos.le)
    have hpm_le_15 : pmR ≤ 1 / 5 := by
      dsimp only [pmR]; rw [jp01WdScaleR_eq, div_le_div_iff₀ (by norm_num) (by norm_num)]
      have hc : ((p0C + 1 : ℕ) : ℝ) ≤ 200000000000000 := (by exact_mod_cast hpm_cap)
      linarith only [hc]
    have hzh_le_bs : zhR ≤ bsR := by
      dsimp only [zhR, bsR]
      exact div_le_div_of_nonneg_right (by exact_mod_cast (by omega : cswapZeroHitNat ≤ cv2 - 1))
        (by norm_num)
    have hzh_le_Bf : zhR ≤ B_fuel f := by
      dsimp only [B_fuel, bsR] at hzh_le_bs ⊢; have h0 : 0 ≤ (1 / 5 : ℝ) ^ f * 2 := (by positivity)
      linarith only [hzh_le_bs, h0]
    have hK_sum : ((DickeSol.p01StepCount ct1 (2 ^ n) + DickeSol.p01StepCount ct2 (2 ^ n) : ℕ) : ℝ)
      ≤ (((ct1 + ct2 : ℕ) : ℝ) / 1000000000000) * SN := by
      have h1 : (DickeSol.p01StepCount ct1 (2 ^ n) : ℝ) ≤ ((ct1 : ℝ) / 1000000000000) * SN :=
        (by simpa [SN, Nat.cast_pow] using DickeSol.p01StepCount_le_tau_sqrt ct1 (2 ^ n))
      have h2 : (DickeSol.p01StepCount ct2 (2 ^ n) : ℝ) ≤ ((ct2 : ℝ) / 1000000000000) * SN :=
        (by simpa [SN, Nat.cast_pow] using DickeSol.p01StepCount_le_tau_sqrt ct2 (2 ^ n))
      push_cast; linarith only [h1, h2]
    have hrec_real : ((ct1 + ct2 : ℕ) : ℝ) / 1000000000000 + 1 / 1000000000000 + (1 - pmR - p2R) *
      zhR ≤ (1 - pmR) * bsR := by
      have hs1 : p0C + 1 ≤ jp01Scale := (by omega); have hs2 : p2C ≤ jp01Scale - (p0C + 1) :=
        (by omega); have hc : ((jp01Scale * (ct1 + ct2) + (jp01Scale - (p0C + 1) - p2C) *
        cswapZeroHitNat + jp01Scale : ℕ) : ℝ) ≤ (((jp01Scale - (p0C + 1)) * (cv2 - 1) : ℕ) : ℝ) :=
        (by exact_mod_cast hrecC); rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_add,
        Nat.cast_mul, Nat.cast_sub hs2, Nat.cast_sub hs1, Nat.cast_mul, Nat.cast_sub hs1] at hc
      have hsc : (jp01Scale : ℝ) = 1000000000000000 := rfl; rw [hsc] at hc; dsimp only [pmR, p2R,
        zhR, bsR]; rw [jp01WdScaleR_eq, Nat.cast_add ct1 ct2]; have hid : (1 - ((p0C + 1 : ℕ) : ℝ) /
        1000000000000000) * (((cv2 - 1 : ℕ) : ℝ) / 1000000000000) - (((ct1 : ℝ) + ct2) /
        1000000000000 + 1 / 1000000000000 + (1 - ((p0C + 1 : ℕ) : ℝ) / 1000000000000000 - (p2C : ℝ)
        / 1000000000000000) * ((cswapZeroHitNat : ℝ) / 1000000000000)) = ((1000000000000000 - ((p0C
        + 1 : ℕ) : ℝ)) * ((cv2 - 1 : ℕ) : ℝ) - (1000000000000000 * ((ct1 : ℝ) + ct2) +
        (1000000000000000 - ((p0C + 1 : ℕ) : ℝ) - p2C) * cswapZeroHitNat + 1000000000000000)) /
        1000000000000000000000000000 := (by ring); rw [← sub_nonneg, hid]
      exact div_nonneg (sub_nonneg.2 hc) (by norm_num)
    have hmono_q0 : (1 - (yC 2) ^ 2 - (yC 0) ^ 2) * zhR + (yC 0) ^ 2 * B_fuel f ≤ (1 - pmR - p2R) *
      zhR + pmR * B_fuel f := by
      have hp2_term : p2R * zhR ≤ (yC 2) ^ 2 * zhR := mul_le_mul_of_nonneg_right hp2_ge
        (by dsimp only [zhR]; positivity); have hq0_term : (yC 0) ^ 2 * (B_fuel f - zhR) ≤ pmR *
        (B_fuel f - zhR) := mul_le_mul_of_nonneg_right hq0_le_pm (by linarith only [hzh_le_Bf])
      linarith only [hp2_term, hq0_term]
    have hcoef_step : ((ct1 + ct2 : ℕ) : ℝ) / 1000000000000 + 1 / 1000000000000 + ((1 - (yC 2) ^ 2 -
      (yC 0) ^ 2) * zhR + (yC 0) ^ 2 * B_fuel f) ≤ B_fuel (f + 1) := by
      have hpm_pow : pmR * ((1 / 5 : ℝ) ^ f * 2) ≤ (1 / 5 : ℝ) ^ (f + 1) * 2 := by
        rw [pow_succ']
        have hm := mul_le_mul_of_nonneg_right hpm_le_15 (by positivity : 0 ≤ (1 / 5 : ℝ) ^ f * 2)
        linarith only [hm]
      have hrec' := hrec_real; dsimp only [B_fuel, bsR] at hmono_q0 hrec' ⊢
      have hdist : (1 - pmR) * (((cv2 - 1 : ℕ) : ℝ) / 1000000000000) + pmR * (((cv2 - 1 : ℕ) : ℝ) /
        1000000000000 + (1 / 5 : ℝ) ^ f * 2) = ((cv2 - 1 : ℕ) : ℝ) / 1000000000000 + pmR * ((1 / 5 :
        ℝ) ^ f * 2) := (by ring); linarith only [hmono_q0, hrec', hpm_pow, hdist]
    calc ((DickeSol.p01StepCount ct1 (2 ^ n) + DickeSol.p01StepCount ct2 (2 ^ n) : ℕ) : ℝ) + 2 +
          ((1 - (yC 2) ^ 2 - (yC 0) ^ 2) * zhR + (yC 0) ^ 2 * B_fuel f) * SN
        ≤ (((ct1 + ct2 : ℕ) : ℝ) / 1000000000000 + 1 / 1000000000000 +
            ((1 - (yC 2) ^ 2 - (yC 0) ^ 2) * zhR + (yC 0) ^ 2 * B_fuel f)) * SN := by
          linarith only [hK_sum, h2_le_pad]
      _ ≤ B_fuel (f + 1) * SN := mul_le_mul_of_nonneg_right hcoef_step hSN_pos.le
  · -- Warm row bound for any `γ` in `[θ₂, 5/4]` with `sin γ < 420 / 512`
    intro γ hγ_lo hγ_hi hsin_lt idx r yW; have hγ0 : 0 ≤ γ := (Real.arcsin_nonneg.2
      (Real.sqrt_nonneg _)).trans hγ_lo; have hsin_nn : 0 ≤ Real.sin γ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hγ0 (by linarith only [hγ_hi, Real.pi_gt_three])
    have hcos_nn : 0 ≤ Real.cos γ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hγ0, Real.pi_gt_three],
        by linarith only [hγ_hi, Real.pi_gt_three]⟩
    have hfl_lt : ⌊512 * Real.sin γ⌋₊ < 420 := (Nat.floor_lt (by positivity)).2
      (by rw [Nat.cast_ofNat]; linarith only [hsin_lt]); have hidx_eq : idx = ⌊512 * Real.sin γ⌋₊ :=
      (by dsimp only [idx, warmJP01BinIdx]; exact min_eq_right (by omega))
    have hidx_lt : idx < 420 := hidx_eq ▸ hfl_lt; have hsin_bin_lo : (idx : ℝ) / 512 ≤ Real.sin γ :=
      (by rw [hidx_eq, div_le_iff₀ (by norm_num), mul_comm]; exact Nat.floor_le (by positivity))
    have hsin_bin_hi : Real.sin γ ≤ ((idx + 1 : ℕ) : ℝ) / 512 := by
      rw [hidx_eq, le_div_iff₀ (by norm_num), mul_comm, Nat.cast_add, Nat.cast_one]
      exact (Nat.lt_floor_add_one _).le
    have hrow := of_allRange hall hidx_lt; dsimp only [checkWarmJP01RowAt] at hrow
    rcases hr_eq : rows idx with ⟨sLo, sHi, c0Lo, c0Hi, t1, t2, rawV2⟩
    have hr_def : r = rows idx := rfl; rw [hr_eq] at hrow hr_def
    rcases hev : jp01EvalInterval sLo sHi c0Lo c0Hi t1 t2 with ⟨okW, p0Hi, p2Lo, w0Hi⟩
    rw [hev] at hrow; simp only [withForcedNat_eq, Bool.and_eq_true, and_assoc, Nat.ble_eq] at hrow
    rcases hrow with ⟨_, _, hsLo_b, hsHi_b, hcLo_b, hcHi_b, hraw1, hokW, hsumW, hnum27, hraw_vm, _⟩
    have hB : 0 < DickeSol.wdScaleR := jp01WdScaleR_pos; have hBeq : (jp01Scale : ℝ) =
      DickeSol.wdScaleR := rfl
    have hs_lo : (sLo : ℝ) / DickeSol.wdScaleR ≤ Real.sin γ := by
      refine le_trans ?_ hsin_bin_lo; rw [div_le_div_iff₀ hB (by norm_num), ← hBeq]; have hc : (512
        : ℝ) * sLo ≤ (idx : ℝ) * jp01Scale := (by exact_mod_cast hsLo_b); linarith only [hc]
    have hs_hi : Real.sin γ ≤ (sHi : ℝ) / DickeSol.wdScaleR := by
      refine hsin_bin_hi.trans ?_; rw [div_le_div_iff₀ (by norm_num) hB, ← hBeq]; have hc : ((idx +
        1 : ℕ) : ℝ) * jp01Scale ≤ (512 : ℝ) * sHi := (by exact_mod_cast hsHi_b); linarith only [hc]
    have hc_lo : (c0Lo : ℝ) / DickeSol.wdScaleR ≤ Real.cos γ := by
      refine sq_le_imp_le (by positivity) hcos_nn ?_
      have hcsq : Real.cos γ ^ 2 = 1 - Real.sin γ ^ 2 := by linarith only [Real.sin_sq_add_cos_sq γ]
      have h512_sin : 512 * Real.sin γ ≤ (idx : ℝ) + 1 :=
        (by have h := hsin_bin_hi; rw [Nat.cast_add, Nat.cast_one] at h; linarith only [h])
      have hsin_512 : (512 * Real.sin γ) * (512 * Real.sin γ) ≤ ((idx : ℝ) + 1) * ((idx : ℝ) + 1) :=
        mul_self_le_mul_self (by positivity) h512_sin
      have hsub_ok : (idx + 1) * (idx + 1) ≤ 512 * 512 := (Nat.mul_le_mul (by omega : idx + 1 ≤ 420)
        (by omega : idx + 1 ≤ 420)).trans (by norm_num); have hc : ((512 * 512 * c0Lo * c0Lo : ℕ) :
        ℝ) ≤ (((512 * 512 - (idx + 1) * (idx + 1)) * jp01Scale * jp01Scale : ℕ) : ℝ) :=
        (by exact_mod_cast hcLo_b); simp only [Nat.cast_mul, Nat.cast_sub hsub_ok, Nat.cast_add,
        Nat.cast_one, Nat.cast_ofNat] at hc; rw [div_pow, hcsq, jp01WdScaleR_eq, div_le_iff₀
        (by norm_num)]; have hid : 512 * 512 * ((1 - Real.sin γ ^ 2) * 1000000000000000 ^ 2 - (c0Lo
        : ℝ) ^ 2) = ((512 * 512 - ((idx : ℝ) + 1) * ((idx : ℝ) + 1)) * 1000000000000000 *
        1000000000000000 - 512 * 512 * (c0Lo : ℝ) * c0Lo) + 1000000000000000 * 1000000000000000 *
        (((idx : ℝ) + 1) * ((idx : ℝ) + 1) - (512 * Real.sin γ) * (512 * Real.sin γ)) := (by ring)
      linarith only [hc, hsin_512, hid]
    have hc_hi : Real.cos γ ≤ (c0Hi : ℝ) / DickeSol.wdScaleR := by
      refine sq_le_imp_le hcos_nn (by positivity) ?_
      have hcsq : Real.cos γ ^ 2 = 1 - Real.sin γ ^ 2 := by linarith only [Real.sin_sq_add_cos_sq γ]
      have h512_sin : (idx : ℝ) ≤ 512 * Real.sin γ := (by linarith only [hsin_bin_lo])
      have hsin_512 : (idx : ℝ) * idx ≤ (512 * Real.sin γ) * (512 * Real.sin γ) :=
        mul_self_le_mul_self (Nat.cast_nonneg idx) h512_sin; have hsub_ok : idx * idx ≤ 512 * 512 :=
        (Nat.mul_le_mul (by omega : idx ≤ 420) (by omega : idx ≤ 420)).trans (by norm_num)
      have hc : (((512 * 512 - idx * idx) * jp01Scale * jp01Scale : ℕ) : ℝ) ≤ ((512 * 512 * c0Hi *
        c0Hi : ℕ) : ℝ) := (by exact_mod_cast hcHi_b); simp only [Nat.cast_mul, Nat.cast_sub hsub_ok,
        Nat.cast_ofNat] at hc; rw [div_pow, hcsq, jp01WdScaleR_eq, le_div_iff₀ (by norm_num)]
      have hid : 512 * 512 * ((c0Hi : ℝ) ^ 2 - (1 - Real.sin γ ^ 2) * 1000000000000000 ^ 2) = (512 *
        512 * (c0Hi : ℝ) * c0Hi - (512 * 512 - (idx : ℝ) * idx) * 1000000000000000 *
        1000000000000000) + 1000000000000000 * 1000000000000000 * ((512 * Real.sin γ) * (512 *
        Real.sin γ) - (idx : ℝ) * idx) := (by ring); linarith only [hc, hsin_512, hid]
    obtain ⟨_, _, hp0_le, hp2_ge, hw0_le⟩ := jp01EvalInterval_sound hn hsq hγ0 hγ_hi hs_lo hs_hi
      hc_lo hc_hi (by rw [hev]; exact hokW)
    rw [hev] at hp0_le hp2_ge hw0_le; dsimp only at hp0_le hp2_ge hw0_le
    have hyW_eq : yW = ((DickeSol.rot3Neg u2)^[DickeSol.p01StepCount t2 (2 ^ n)])
      (((DickeSol.rot3Pos u1)^[DickeSol.p01StepCount t1 (2 ^ n)]) (jp01InitOrbVec n γ)) :=
      (by dsimp only [yW]; rw [hr_def]); rw [← hyW_eq] at hp0_le hp2_ge
    have hK_sum : ((DickeSol.p01StepCount r.tau1_12 (2 ^ n) + DickeSol.p01StepCount r.tau2_12 (2 ^
      n) : ℕ) : ℝ) ≤ (((t1 + t2 : ℕ) : ℝ) / 1000000000000) * SN := by
      rw [hr_def]; dsimp only
      have h1 : (DickeSol.p01StepCount t1 (2 ^ n) : ℝ) ≤ ((t1 : ℝ) / 1000000000000) * SN :=
        (by simpa [SN, Nat.cast_pow] using DickeSol.p01StepCount_le_tau_sqrt t1 (2 ^ n))
      have h2 : (DickeSol.p01StepCount t2 (2 ^ n) : ℝ) ≤ ((t2 : ℝ) / 1000000000000) * SN :=
        (by simpa [SN, Nat.cast_pow] using DickeSol.p01StepCount_le_tau_sqrt t2 (2 ^ n)); push_cast;
        linarith only [h1, h2]
    have hw0_nn : 0 ≤ 1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 := by
      linarith only [Real.sin_sq_add_cos_sq (γ - halfAngleSet n 2), sq_nonneg (Real.cos (γ -
        halfAngleSet n 2))]
    have hw0_K : (1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2) * ((DickeSol.p01StepCount r.tau1_12
      (2 ^ n) + DickeSol.p01StepCount r.tau2_12 (2 ^ n) : ℕ) : ℝ) ≤ (((w0Hi : ℝ) /
      DickeSol.wdScaleR) * (((t1 + t2 : ℕ) : ℝ) / 1000000000000)) * SN := by
      calc (1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2) * _
          ≤ ((w0Hi : ℝ) / DickeSol.wdScaleR) * ((((t1 + t2 : ℕ) : ℝ) / 1000000000000) * SN) :=
            mul_le_mul hw0_le hK_sum (by positivity) (by positivity)
        _ = _ := by ring
    set zhR : ℝ := (cswapZeroHitNat : ℝ) / 1000000000000; set cvR : ℝ := (cv2 : ℝ) / 1000000000000
    have hzh_le_cv : zhR ≤ cvR := div_le_div_of_nonneg_right (by exact_mod_cast hzh_lt.le)
      (by norm_num); have hq0_le : (yW 0) ^ 2 ≤ ((p0Hi + 1 : ℕ) : ℝ) / DickeSol.wdScaleR :=
      hp0_le.trans (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ p0Hi) hB.le)
    have hcont_le : (1 - (yW 2) ^ 2 - (yW 0) ^ 2) * zhR + (yW 0) ^ 2 * cvR ≤ (1 - (p2Lo : ℝ) /
      DickeSol.wdScaleR) * zhR + (((p0Hi + 1 : ℕ) : ℝ) / DickeSol.wdScaleR) * (cvR - zhR) := by
      have hp2_t : ((p2Lo : ℝ) / DickeSol.wdScaleR) * zhR ≤ (yW 2) ^ 2 * zhR :=
        mul_le_mul_of_nonneg_right hp2_ge (by dsimp only [zhR]; positivity)
      have hq0_t : (yW 0) ^ 2 * (cvR - zhR) ≤ (((p0Hi + 1 : ℕ) : ℝ) / DickeSol.wdScaleR) * (cvR -
        zhR) := mul_le_mul_of_nonneg_right hq0_le (by linarith only [hzh_le_cv])
      linarith only [hp2_t, hq0_t]
    have hnum_real : ((w0Hi : ℝ) / DickeSol.wdScaleR) * (((t1 + t2 : ℕ) : ℝ) / 1000000000000) + (1 -
      (p2Lo : ℝ) / DickeSol.wdScaleR) * zhR + (((p0Hi + 1 : ℕ) : ℝ) / DickeSol.wdScaleR) * (cvR -
      zhR) + 1 / 1000000000000 ≤ (v2m idx : ℝ) / 1000000000000 := by
      have hp2_le_sc : p2Lo ≤ jp01Scale := (by omega); have hzh_le_cv_nat : cswapZeroHitNat ≤ cv2 :=
        hzh_lt.le; have hrw : ((w0Hi * (t1 + t2) + (jp01Scale - p2Lo) * cswapZeroHitNat + (p0Hi + 1)
        * (cv2 - cswapZeroHitNat) : ℕ) : ℝ) ≤ (((rawV2 - 1) * jp01Scale : ℕ) : ℝ) :=
        (by exact_mod_cast hnum27); rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_add,
        Nat.cast_mul, Nat.cast_sub hp2_le_sc, Nat.cast_mul, Nat.cast_sub hzh_le_cv_nat,
        Nat.cast_mul, Nat.cast_sub hraw1, Nat.cast_one] at hrw
      have hvm_r : (rawV2 : ℝ) ≤ v2m idx := (by exact_mod_cast hraw_vm)
      have hsc : (jp01Scale : ℝ) = 1000000000000000 := rfl; rw [hsc] at hrw; dsimp only [zhR, cvR];
        rw [jp01WdScaleR_eq, Nat.cast_add t1 t2]; have hid : (v2m idx : ℝ) / 1000000000000 - (((w0Hi
        : ℝ) / 1000000000000000) * (((t1 : ℝ) + t2) / 1000000000000) + (1 - (p2Lo : ℝ) /
        1000000000000000) * ((cswapZeroHitNat : ℝ) / 1000000000000) + (((p0Hi + 1 : ℕ) : ℝ) /
        1000000000000000) * ((cv2 : ℝ) / 1000000000000 - (cswapZeroHitNat : ℝ) / 1000000000000) + 1
        / 1000000000000) = ((((rawV2 : ℝ) - 1) * 1000000000000000 - ((w0Hi : ℝ) * ((t1 : ℝ) + t2) +
        (1000000000000000 - p2Lo) * cswapZeroHitNat + ((p0Hi + 1 : ℕ) : ℝ) * ((cv2 : ℝ) -
        cswapZeroHitNat))) + 1000000000000000 * ((v2m idx : ℝ) - rawV2)) /
        1000000000000000000000000000 := (by ring); rw [← sub_nonneg, hid]
      exact div_nonneg (add_nonneg (sub_nonneg.2 hrw) (mul_nonneg (by norm_num) (sub_nonneg.2
        hvm_r))) (by norm_num)
    have hcomb_sn := mul_le_mul_of_nonneg_right
      (by linarith only [hcont_le, hnum_real] :
        ((w0Hi : ℝ) / DickeSol.wdScaleR) * (((t1 + t2 : ℕ) : ℝ) / 1000000000000) +
          1 / 1000000000000 +
          ((1 - (yW 2) ^ 2 - (yW 0) ^ 2) * zhR + (yW 0) ^ 2 * cvR) ≤
          (v2m idx : ℝ) / 1000000000000) hSN_pos.le
    linarith only [hw0_K, h2_le_pad, hcomb_sn]
/-! ### Stage-`3`, Stage-`≥ 4`, and Cell Certificate Soundness for `warmJP01` -/
private noncomputable def warmJP01Potential (B : ℕ) (v2m : ℕ → ℕ)
    (stFn : ℕ → M2StageScalar) (wFn : ℕ → ℕ → ℕ) (n r : ℕ) (betas : Fin 2 → ℝ) : ℝ :=
  if r ≤ 1 then cswapWarmR1Cost1 n betas
  else if r = 2 then warmJP01R2Cost2 v2m n betas
  else wmStagePot B (phiFnOfWmSt stFn) stFn wFn n r betas
private theorem fuseNextAngle_three_sin_lt {n : ℕ} (hn : 200 ≤ n) {β : ℝ} (hβ_lo : halfAngleSet n 3
  ≤ β) (hβ_hi : β ≤ 5 / 4) : halfAngleSet n 2 ≤ fuseNextAngle n 3 β ∧ fuseNextAngle n 3 β ≤ 5 / 4 ∧
  Real.sin (fuseNextAngle n 3 β) < 420 / 512 := by
  obtain ⟨hSN_ge, hN_ge⟩ := pow_two_200_bounds hn; have hn100 : 100 ≤ n := (by omega); set NR : ℝ :=
    (2 : ℝ) ^ n; have h2r : 2 * 3 ≤ 2 ^ n := two_mul_le_pow_100 hn100 (by norm_num)
  have h54_lt : (5 / 4 : ℝ) < π / 2 := tan_five_div_four_le_five.2; have hf_lo : halfAngleSet n (3 -
    1) ≤ fuseNextAngle n 3 β := halfAngleSet_le_fuseNextAngle (by norm_num) h2r hβ_lo (hβ_hi.trans
    h54_lt.le)
  have hf_le_self : fuseNextAngle n 3 β ≤ β := fuseNextAngle_le_self (by norm_num) h2r hβ_lo
    (hβ_hi.trans h54_lt.le); refine ⟨hf_lo, hf_le_self.trans hβ_hi, ?_⟩; have h3N : 3 < 2 ^ n :=
    (by omega)
  have hlam_sq : fuseLamFin n 3 ^ 2 ≤ 667 / 1000 := by
    rw [fuseLamFin_sq (by norm_num : 2 ≤ 3) h3N]
    have hN_cast : (2 ^ n : ℝ) = NR := rfl; rw [hN_cast]; simp only [Nat.cast_ofNat]
    rw [div_le_div_iff₀ (by linarith only [hN_ge]) (by norm_num)]
    have h2003 : (2003 : ℝ) ≤ (2 : ℝ) ^ 200 := (by norm_num); linarith only [hN_ge, h2003]
  have hlam_nn : 0 ≤ fuseLamFin n 3 := (fuseLamFin_pos_and_lt_one (by norm_num) h2r).1.le
  have hlam_le : fuseLamFin n 3 ≤ 817 / 1000 := sq_le_imp_le hlam_nn (by norm_num) (hlam_sq.trans
    (by norm_num)); set u := fuseLamFin n 3 * Real.sin (β - halfAngleSet n 3); have hθ3_nn : 0 ≤
    halfAngleSet n 3 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hsin_diff_nn : 0 ≤ Real.sin (β - halfAngleSet n 3) := Real.sin_nonneg_of_nonneg_of_le_pi
    (sub_nonneg.2 hβ_lo) (by linarith only [hβ_hi, Real.pi_gt_three, hθ3_nn]); have hu_nn : 0 ≤ u :=
    mul_nonneg hlam_nn hsin_diff_nn; have hu_le : u ≤ 817 / 1000 := (mul_le_of_le_one_right hlam_nn
    (Real.sin_le_one _)).trans hlam_le; have hsin_arc : Real.sin (Real.arcsin u) = u :=
    Real.sin_arcsin (by linarith only [hu_nn]) (by linarith only [hu_le])
  obtain ⟨_, _, hθ2_13, -⟩ := halfAngleSet_bounds_100 hn100 (by norm_num : 1 ≤ 2)
    (by norm_num : 2 ≤ 1024); have hθ2_le : halfAngleSet n 2 ≤ 1 / 1000 :=
    (by linarith only [hθ2_13])
  have hθ2_nn : 0 ≤ halfAngleSet n 2 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); have hlip :=
    Real.abs_sin_sub_sin_le (fuseNextAngle n 3 β) (Real.arcsin u)
  have hfg_eq : fuseNextAngle n 3 β - Real.arcsin u = halfAngleSet n 2 :=
    (by dsimp [fuseNextAngle]; ring)
  rw [hfg_eq, abs_of_nonneg hθ2_nn, hsin_arc] at hlip; have hlip1 := (abs_sub_le_iff.1 hlip).1
  linarith only [hlip1, hu_le, hθ2_le]
private theorem warmJP01Guard_nextStageFuseBetas {n : ℕ} (hn : 200 ≤ n) {postBetas : Fin 2 → ℝ}
  (hpost : ValidStageBetas n 3 (5 / 4) postBetas) : (warmJP01Guard n (nextStageFuseBetas n 3 ⟨1,
  (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas) ∧ max (nextStageFuseBetas n 3 ⟨1,
  (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas s0) (nextStageFuseBetas n 3 ⟨1,
  (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas s1) = fuseNextAngle n 3 (postBetas s1)) ∧
  (warmJP01Guard n (nextStageFuseBetas n 3 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas) ∧
  max (nextStageFuseBetas n 3 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas s0)
  (nextStageFuseBetas n 3 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas s1) = fuseNextAngle
  n 3 (postBetas s0)) ∧ (warmJP01Guard n (nextStageFuseBetas n 3 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3
  < 2 ^ 2)⟩ postBetas) ∧ max (nextStageFuseBetas n 3 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩
  postBetas s0) (nextStageFuseBetas n 3 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postBetas s1) =
  halfAngleSet n 2) := by
  have hf_bds (i : Fin 2) := fuseNextAngle_three_sin_lt hn (hpost i).1 (hpost i).2; obtain ⟨_,
    hN_ge⟩ := pow_two_200_bounds hn
  have hθ2_54 : halfAngleSet n 2 ≤ 5 / 4 := (hf_bds s0).1.trans (hf_bds s0).2.1
  have hsin_θ2_lt : Real.sin (halfAngleSet n 2) < 420 / 512 := by
    dsimp only [halfAngleSet]; have hrt0 : (0 : ℝ) ≤ √(2 / (2 : ℝ) ^ n) := Real.sqrt_nonneg _
    have hdiv1 : (2 : ℝ) / (2 : ℝ) ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ 200 := (by norm_num)
      linarith only [hN_ge, h2]
    rw [Nat.cast_ofNat, Real.sin_arcsin (by linarith only [hrt0]) (Real.sqrt_le_one.2 hdiv1)]
    have hle : √(2 / (2 : ℝ) ^ n) ≤ 1 / 2 := by
      refine sq_le_imp_le (Real.sqrt_nonneg _) (by norm_num) ?_; rw [Real.sq_sqrt (by positivity),
        div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
      have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ 200 := (by norm_num); linarith only [hN_ge, h8]
    linarith only [hle]
  refine ⟨?_, ?_, ?_⟩
  · have hb0 : nextStageFuseBetas n 3 ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas s0 =
      halfAngleSet n 2 := by
      dsimp only [nextStageFuseBetas, s0]; rw [show (1 : ℕ).testBit (0 : Fin 2).val = true from
        rfl]; simp
    have hb1 : nextStageFuseBetas n 3 ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas s1 =
      fuseNextAngle n 3 (postBetas s1) := by
      dsimp only [nextStageFuseBetas, s1]; rw [show (1 : ℕ).testBit (1 : Fin 2).val = false from
        rfl]; simp
    have hmax : max (nextStageFuseBetas n 3 ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas
      s0) (nextStageFuseBetas n 3 ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postBetas s1) =
      fuseNextAngle n 3 (postBetas s1) := (by rw [hb0, hb1]; exact max_eq_right (hf_bds s1).1)
    exact ⟨⟨Or.inl hb0, by rw [hb0], by rw [hb1]; exact (hf_bds s1).1,
      by rw [hmax]; exact (hf_bds s1).2.2, by rw [hmax]; exact (hf_bds s1).2.1⟩, hmax⟩
  · have hb0 : nextStageFuseBetas n 3 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas s0 =
      fuseNextAngle n 3 (postBetas s0) := by
      dsimp only [nextStageFuseBetas, s0]; rw [show (2 : ℕ).testBit (0 : Fin 2).val = false from
        rfl]; simp
    have hb1 : nextStageFuseBetas n 3 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas s1 =
      halfAngleSet n 2 := by
      dsimp only [nextStageFuseBetas, s1]; rw [show (2 : ℕ).testBit (1 : Fin 2).val = true from
        rfl]; simp
    have hmax : max (nextStageFuseBetas n 3 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas
      s0) (nextStageFuseBetas n 3 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postBetas s1) =
      fuseNextAngle n 3 (postBetas s0) := (by rw [hb0, hb1]; exact max_eq_left (hf_bds s0).1)
    exact ⟨⟨Or.inr hb1, by rw [hb0]; exact (hf_bds s0).1, by rw [hb1],
      by rw [hmax]; exact (hf_bds s0).2.2, by rw [hmax]; exact (hf_bds s0).2.1⟩, hmax⟩
  · have hb0 : nextStageFuseBetas n 3 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postBetas s0 =
      halfAngleSet n 2 := by
      dsimp only [nextStageFuseBetas, s0]; rw [show (3 : ℕ).testBit (0 : Fin 2).val = true from
        rfl]; simp
    have hb1 : nextStageFuseBetas n 3 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postBetas s1 =
      halfAngleSet n 2 := by
      dsimp only [nextStageFuseBetas, s1]; rw [show (3 : ℕ).testBit (1 : Fin 2).val = true from
        rfl]; simp
    have hmax : max (nextStageFuseBetas n 3 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postBetas
      s0) (nextStageFuseBetas n 3 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postBetas s1) =
      halfAngleSet n 2 := (by rw [hb0, hb1, max_self])
    exact ⟨⟨Or.inl hb0, by rw [hb0], by rw [hb1],
      by rw [hmax]; exact hsin_θ2_lt, by rw [hmax]; exact hθ2_54⟩, hmax⟩
private theorem checkS3Idx_sound {n tc sIdx hh : ℕ} {v2m : ℕ → ℕ} {β : ℝ} (hn : 200 ≤ n) (hv_anti :
  ∀ {i j : ℕ}, i ≤ j → j < 420 → v2m j ≤ v2m i) (hβ_lo : Real.arctan ((tc : ℝ) / 100000) ≤ β) (hβ_hi
  : β ≤ 5 / 4) (hchk : checkS3Idx v2m tc sIdx hh = true) : v2m (warmJP01BinIdx (fuseNextAngle n 3
  β)) ≤ hh := by
  dsimp only [checkS3Idx] at hchk; simp only [withForcedNat_eq, Bool.and_eq_true, and_assoc,
    Nat.ble_eq, Nat.blt_eq] at hchk; rcases hchk with ⟨htc1, _, hsIdx_lt, hsq_b, hvm_hh⟩
  have hn100 : 100 ≤ n := (by omega)
  have h2r : 2 * 3 ≤ 2 ^ n := two_mul_le_pow_100 hn100 (by norm_num)
  have h54_lt : (5 / 4 : ℝ) < π / 2 := tan_five_div_four_le_five.2; obtain ⟨_, _, hθ3_13, -⟩ :=
    halfAngleSet_bounds_100 hn100 (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 1024)
  have hatan_ge_θ3 : halfAngleSet n 3 ≤ Real.arctan ((tc : ℝ) / 100000) := by
    have h1 : (1 : ℝ) / 100000 ≤ (tc : ℝ) / 100000 :=
      (by have htc_r : (1 : ℝ) ≤ tc := (by exact_mod_cast htc1); linarith only [htc_r])
    have hp : (1 : ℝ) / 10000000000000 ≤ Real.arctan ((1 : ℝ) / 100000) := le_trans (by norm_num)
      (pade56_le_arctan (by norm_num : (0 : ℝ) ≤ 1 / 100000)); have hmono_at := Real.arctan_mono h1;
      linarith only [hθ3_13, hp, hmono_at]
  obtain ⟨hf_lo, hf_hi, hsin_lt⟩ := fuseNextAngle_three_sin_lt hn (hatan_ge_θ3.trans hβ_lo) hβ_hi
  have hf_ge : Real.arcsin (√(((3 - 1 : ℕ) : ℝ) / 3) * Real.sin (Real.arctan ((tc : ℝ) / 100000))) ≤
    fuseNextAngle n 3 β := (arcsin_sqrt_nat_sub_ratio_le_fuseNextAngle (by norm_num) h2r hatan_ge_θ3
    (Real.arctan_lt_pi_div_two _)).trans (fuseNextAngle_mono (by norm_num) h2r hatan_ge_θ3 hβ_lo
    (hβ_hi.trans h54_lt.le)); set x : ℝ := (tc : ℝ) / 100000; have hx_pos : 0 < x :=
    (by dsimp [x]; have : (0 : ℝ) < tc := Nat.cast_pos.2 htc1; positivity)
  have hsin_at : Real.sin (Real.arctan x) = x / √(1 + x ^ 2) := Real.sin_arctan x
  have harg_le1 : √(((3 - 1 : ℕ) : ℝ) / 3) * Real.sin (Real.arctan x) ≤ 1 := by
    have h1 : √(((3 - 1 : ℕ) : ℝ) / 3) ≤ 1 := Real.sqrt_le_one.2 (by norm_num)
    exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.sin_le_one _)).trans h1
  have harg_nn : 0 ≤ √(((3 - 1 : ℕ) : ℝ) / 3) * Real.sin (Real.arctan x) :=
    (by rw [hsin_at]; positivity)
  have hsin_fg_ge : √(2 / 3 : ℝ) * (x / √(1 + x ^ 2)) ≤ Real.sin (fuseNextAngle n 3 β) := by
    have harc_nn : 0 ≤ Real.arcsin (√(((3 - 1 : ℕ) : ℝ) / 3) * Real.sin (Real.arctan x)) :=
      Real.arcsin_nonneg.2 harg_nn
    have hm := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith only [Real.pi_gt_three, harc_nn])
      (hf_hi.trans h54_lt.le) hf_ge
    rwa [Real.sin_arcsin (by linarith only [harg_nn]) harg_le1,
      show ((3 - 1 : ℕ) : ℝ) / 3 = 2 / 3 by norm_num, hsin_at] at hm
  have hsIdx_le_sin : (sIdx : ℝ) / 512 ≤ Real.sin (fuseNextAngle n 3 β) := by
    refine le_trans ?_ hsin_fg_ge; refine sq_le_imp_le (by positivity) (by positivity) ?_
    rw [mul_pow, div_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
    have hcast : (3 : ℝ) * sIdx * sIdx * (10000000000 + (tc : ℝ) * tc) ≤ 524288 * ((tc : ℝ) * tc) :=
      (by exact_mod_cast hsq_b); dsimp only [x]; rw [div_mul_div_comm, div_le_div_iff₀ (by norm_num)
      (by positivity)]; have hpoly : (sIdx : ℝ) ^ 2 * (3 * (1 + ((tc : ℝ) / 100000) ^ 2)) - 2 * ((tc
      : ℝ) / 100000) ^ 2 * 512 ^ 2 = ((3 : ℝ) * sIdx * sIdx * (10000000000 + (tc : ℝ) * tc) - 524288
      * ((tc : ℝ) * tc)) / 10000000000 := (by ring); linarith only [hcast, hpoly]
  have hsin_fg_nn : 0 ≤ Real.sin (fuseNextAngle n 3 β) := Real.sin_nonneg_of_nonneg_of_le_pi
    ((Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)).trans hf_lo)
    (by linarith only [hf_hi, Real.pi_gt_three])
  have hfl_lt : ⌊512 * Real.sin (fuseNextAngle n 3 β)⌋₊ < 420 := (Nat.floor_lt (mul_nonneg
    (by norm_num) hsin_fg_nn)).2 (by rw [Nat.cast_ofNat]; linarith only [hsin_lt])
  have hidx_eq : warmJP01BinIdx (fuseNextAngle n 3 β) = ⌊512 * Real.sin (fuseNextAngle n 3 β)⌋₊ :=
    min_eq_right (by omega)
  have hsIdx_le_idx : sIdx ≤ warmJP01BinIdx (fuseNextAngle n 3 β) := by
    rw [hidx_eq]; have h512 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).1 hsIdx_le_sin
    exact Nat.le_floor (by linarith only [h512])
  exact (hv_anti hsIdx_le_idx (hidx_eq ▸ hfl_lt)).trans hvm_hh
private theorem warmJP01_stage3_single_locked_step {B n tn phiLo cSelf dNat : ℕ} {v2m w : ℕ → ℕ}
  {binR : ℕ → M2BinCert} (hB : 1 ≤ B) (hn : 200 ≤ n) (hv_anti : ∀ {i j : ℕ}, i ≤ j → j < 420 → v2m j
  ≤ v2m i) (ht_lo : 500 ≤ tn) (ht_hi : tn ≤ 200000) (hphiLo_chk : checkAtan200Lo tn phiLo = true)
  (hd1000 : 1000 ≤ dNat) (hcB : cSelf ≤ B * dNat) (hw : ∀ i < B, w i ≤ w (i + 1) ∧ w (i + 1) ≤ w i +
  dNat) (hbins : allRange (fun j => checkWarmJP01Stage3Bin B tn phiLo dNat v2m w (binR j) j) B =
  true) {p βRamp : ℝ} (hp_lo : 4 * ((tn : ℝ) / 100000) * (99999999 / 100000000) * √(3 : ℝ) / √((2 :
  ℝ) ^ n) ≤ p) (hβ_lo : halfAngleSet n 3 ≤ βRamp) (hβ_lt : βRamp < Real.arctan ((tn : ℝ) / 100000))
  (hd_cap : (remStepsSlot n 3 (Real.arctan ((tn : ℝ) / 100000)) βRamp : ℝ) ≤ ((cSelf : ℝ) /
  1000000000000) * √((2 : ℝ) ^ n)) :
    let SN := √((2 : ℝ) ^ n); let φ := Real.arctan ((tn : ℝ) / 100000)
    let d := remStepsSlot n 3 φ βRamp; let β' := βRamp + 2 * halfAngleSet n 3
    1 + (1 - p) * wmPotVal B dNat w SN 0 ((d - 1 : ℕ) : ℝ) + p * (((v2m (warmJP01BinIdx
      (fuseNextAngle n 3 β')) : ℝ) / 1000000000000) * SN) ≤ wmPotVal B dNat w SN 0 (d : ℝ) := by
  intro SN φ d β'; obtain ⟨hSN_ge, hN_ge⟩ := pow_two_200_bounds hn; have hSN_pos : 0 < SN :=
    lt_of_lt_of_le (by positivity) hSN_ge
  have hd1 : 1 ≤ d := by
    by_contra h0
    have hez : d = 0 := (by omega); have h0' := (remStepsSlot_eq_zero_iff (by norm_num : 1 ≤ 3) φ
      βRamp).1 hez; linarith only [h0', hβ_lt]
  have hd_ge1 : 1 ≤ dNat := (by omega)
  have hd_pos : (0 : ℝ) < dNat := Nat.cast_pos.2 hd_ge1; set δ : ℝ := (dNat : ℝ) / 1000000000000
  have hδ_pos : 0 < δ := (by positivity); set x' : ℝ := ((d - 1 : ℕ) : ℝ) / SN
  have hx'0 : 0 ≤ x' := (by positivity)
  have hx'B : x' ≤ (B : ℝ) * δ := by
    have h1 : ((d - 1 : ℕ) : ℝ) ≤ d := (by exact_mod_cast Nat.sub_le d 1); have h2 : (d : ℝ) / SN ≤
      (cSelf : ℝ) / 1000000000000 := (div_le_iff₀ hSN_pos).2 hd_cap
    have h3 : (cSelf : ℝ) / 1000000000000 ≤ (B : ℝ) * δ := by
      dsimp only [δ]; have hcB_r : (cSelf : ℝ) ≤ (B : ℝ) * dNat := (by exact_mod_cast hcB)
      linarith only [hcB_r]
    exact (div_le_div_of_nonneg_right h1 hSN_pos.le).trans (h2.trans h3)
  obtain ⟨j, hj, hx'_lo, hx'_hi⟩ := exists_bin_of_le hB hδ_pos hx'0 hx'B
  have h_invSN_le_δ : 1 / SN ≤ δ := by
    have h1 : 1 / SN ≤ 1 / (2 : ℝ) ^ 100 := one_div_le_one_div_of_le (by positivity) hSN_ge
    have h2 : (1000 : ℝ) ≤ dNat := (by exact_mod_cast hd1000); dsimp only [δ]
    have h2_100 : (1 : ℝ) / (2 : ℝ) ^ 100 ≤ 1 / 1000000000000 := (by norm_num); linarith only [h1,
      h2, h2_100]
  have hd_split : (d : ℝ) / SN = x' + 1 / SN :=
    (by dsimp only [x']; rw [Nat.cast_sub hd1, Nat.cast_one]; field_simp [hSN_pos.ne']; ring)
  rw [wmPotVal_zero_left B dNat w SN (by positivity : (0 : ℝ) ≤ (d - 1 : ℕ)), wmPotVal_zero_left B
    dNat w SN (by positivity : (0 : ℝ) ≤ d), hd_split]; have hstep_psi :=
    psiPiecewise_step_ge_minDiff hd_ge1 hw hj hx'_lo hx'_hi (by positivity) h_invSN_le_δ
  have hstep_sn : (minDiffNat B w j : ℝ) / dNat ≤ SN * psiPiecewise B dNat w (x' + 1 / SN) - SN *
    psiPiecewise B dNat w x' := by
    have hm := mul_le_mul_of_nonneg_left hstep_psi hSN_pos.le; have hl : SN * (((minDiffNat B w j :
      ℝ) / dNat) * (1 / SN)) = (minDiffNat B w j : ℝ) / dNat := (by field_simp [hSN_pos.ne'])
    linarith only [hm, hl]
  have hpost_ge : ((w j : ℝ) / 1000000000000) * SN ≤ SN * psiPiecewise B dNat w x' := by
    have hm := psiPiecewise_mono (B := B) (dNat := dNat) (w := w) hx'_lo; dsimp only [δ] at hm
    rw [psiPiecewise_knot hd_ge1 hw hj.le] at hm
    have hm_sn := mul_le_mul_of_nonneg_left hm hSN_pos.le; have hcomm : SN * ((w j : ℝ) /
      1000000000000) = ((w j : ℝ) / 1000000000000) * SN := (by ring); linarith only [hm_sn, hcomm]
  have hbin_j := of_allRange hbins hj; dsimp only [checkWarmJP01Stage3Bin] at hbin_j
  rcases hbr_eq : binR j with ⟨tcLo, bLoHi, dropHi, sIdx, _, _, _, _, hHi⟩; rw [hbr_eq] at hbin_j;
    dsimp only at hbin_j; simp only [withForcedNat_eq, Bool.and_eq_true] at hbin_j
  rcases hbin_j with ⟨hbr_tc, hhw_d, hsq_d⟩
  have hhw : hHi ≤ w j := Nat.ble_eq.mp hhw_d; have hsq_nat := Nat.ble_eq.mp hsq_d
  have hn100 : 100 ≤ n := (by omega)
  obtain ⟨_, hθ3_hi, -⟩ := halfAngleSet_bounds_100 hn100 (by norm_num : 1 ≤ 3)
    (by norm_num : 3 ≤ 1024)
  rcases phi_and_lockedAlpha_bounds_fuse_100 (m := 1) le_rfl (by omega) hn100 (by omega : 1 ≤ 3)
    (by omega : 3 ≤ 1024) ht_lo ht_hi with ⟨_, hφ2θ, -, -⟩; have hθ3_pos : 0 < halfAngleSet n 3 :=
    Real.arcsin_pos.2 (Real.sqrt_pos.2 (div_pos (by norm_num) (by positivity)))
  have hβ'_lo : halfAngleSet n 3 ≤ β' := (by dsimp [β']; linarith only [hβ_lo, hθ3_pos])
  have hβ'_54 : β' ≤ 5 / 4 := (by dsimp [β']; linarith only [hβ_lt, hφ2θ])
  have hhit_v2m : v2m (warmJP01BinIdx (fuseNextAngle n 3 β')) ≤ hHi := by
    by_cases htc0 : tcLo = 0
    · subst htc0; simp only [_nEq_self, Bool.cond_true, Nat.ble_eq] at hbr_tc
      obtain ⟨hf'_lo, hf'_hi, hsin_lt⟩ := fuseNextAngle_three_sin_lt hn hβ'_lo hβ'_54
      have hidx_lt : warmJP01BinIdx (fuseNextAngle n 3 β') < 420 := by
        have hsin_nn : 0 ≤ Real.sin (fuseNextAngle n 3 β') := Real.sin_nonneg_of_nonneg_of_le_pi
          ((Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)).trans hf'_lo)
          (by linarith only [hf'_hi, Real.pi_gt_three])
        have hfl_lt : ⌊512 * Real.sin (fuseNextAngle n 3 β')⌋₊ < 420 := (Nat.floor_lt (mul_nonneg
          (by norm_num) hsin_nn)).2 (by rw [Nat.cast_ofNat]; linarith only [hsin_lt])
        dsimp [warmJP01BinIdx]; omega
      exact (hv_anti (Nat.zero_le _) hidx_lt).trans hbr_tc
    · have hb_f : _nEq tcLo 0 = false := Bool.eq_false_iff.mpr fun h => htc0 (_nEq_eq.mp h)
      rw [hb_f, Bool.cond_false] at hbr_tc; simp only [Bool.and_eq_true, and_assoc] at hbr_tc
      rcases hbr_tc with ⟨_, _, hat_tc, hdrop_sq_d, hbdrop_d, hs3_chk⟩; have hdrop_sq :=
        Nat.ble_eq.mp hdrop_sq_d; have hbdrop := Nat.ble_eq.mp hbdrop_d
      have hceil_le : φ - βRamp ≤ (d : ℝ) * (2 * halfAngleSet n 3) :=
        (by dsimp only [d, remStepsSlot]; exact (div_le_iff₀ (by positivity)).1 (Nat.le_ceil _))
      have hφ_sub_β' : φ - β' ≤ 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n 3 :=
        (by dsimp only [β']; rw [Nat.cast_sub hd1, Nat.cast_one]; linarith only [hceil_le])
      have hd1_le : ((d - 1 : ℕ) : ℝ) ≤ (((j + 1 : ℕ) : ℝ) * δ) * SN := (div_le_iff₀ hSN_pos).1
        hx'_hi
      have hfac_up : 1 + (3 : ℕ) / (2 : ℝ) ^ n ≤ 1000000000001 / 1000000000000 := by
        push_cast; have h3n : (3 : ℝ) / (2 : ℝ) ^ n ≤ 3 / (2 : ℝ) ^ 200 := div_le_div_of_nonneg_left
          (by norm_num) (by positivity) hN_ge; have h3_200 : (3 : ℝ) / (2 : ℝ) ^ 200 ≤ 1 /
          1000000000000 := (by norm_num); linarith only [h3n, h3_200]
      have hθ3_up : halfAngleSet n 3 ≤ (√(3 : ℝ) / SN) * (1000000000001 / 1000000000000) :=
        hθ3_hi.trans (mul_le_mul_of_nonneg_left hfac_up (by positivity))
      have hdrop_prod : 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n 3 ≤ (2 * √(3 : ℝ) * (((j + 1) * dNat
        * 1000000000001 : ℕ) : ℝ)) / (1000000000000 * 1000000000000) := by
        have hm := mul_le_mul (mul_le_mul_of_nonneg_left hd1_le (by norm_num : (0 : ℝ) ≤ 2)) hθ3_up
          hθ3_pos.le (by positivity); have heq : (2 * ((((j + 1 : ℕ) : ℝ) * δ) * SN)) * ((√(3 : ℝ) /
          SN) * (1000000000001 / 1000000000000)) = (2 * √(3 : ℝ) * (((j + 1) * dNat * 1000000000001
          : ℕ) : ℝ)) / (1000000000000 * 1000000000000) :=
          (by dsimp only [δ]; push_cast; field_simp [hSN_pos.ne']); linarith only [hm, heq]
      have hdrop_le : 2 * ((d - 1 : ℕ) : ℝ) * halfAngleSet n 3 ≤ (dropHi : ℝ) / 1000000000000 := by
        refine hdrop_prod.trans ?_
        have hroot_le : 2 * √(3 : ℝ) * (((j + 1) * dNat * 1000000000001 : ℕ) : ℝ) ≤ (dropHi : ℝ) *
          1000000000000 := by
          refine sq_le_imp_le (by positivity) (by positivity) ?_; set dr : ℕ := (j + 1) * dNat *
            1000000000001; have hcast : 4 * 3 * (dr : ℝ) * dr ≤ ((dropHi : ℝ) * 1000000000000) *
            ((dropHi : ℝ) * 1000000000000) := (by exact_mod_cast hdrop_sq)
          have hlhs_sq : (2 * √(3 : ℝ) * (dr : ℝ)) ^ 2 = 4 * 3 * (dr : ℝ) * dr := by
            calc (2 * √(3 : ℝ) * (dr : ℝ)) ^ 2 = 4 * (√(3 : ℝ)) ^ 2 * (dr : ℝ) * dr := by ring
              _ = 4 * 3 * (dr : ℝ) * dr := by rw [Real.sq_sqrt (by norm_num)]
          have hrhs_sq : ((dropHi : ℝ) * 1000000000000) ^ 2 = ((dropHi : ℝ) * 1000000000000) *
            ((dropHi : ℝ) * 1000000000000) := (by ring); linarith only [hcast, hlhs_sq, hrhs_sq]
        have hrhs : (dropHi : ℝ) / 1000000000000 = ((dropHi : ℝ) * 1000000000000) / (1000000000000 *
          1000000000000) := (by ring); rw [hrhs]
        exact div_le_div_of_nonneg_right hroot_le (by norm_num)
      have hphiLo_le := atan200Lo_sound hphiLo_chk; have hbLo_ge := atan200Hi_sound hat_tc
      have hbdrop_r : (bLoHi : ℝ) + dropHi ≤ phiLo := (by exact_mod_cast hbdrop)
      have hatan_tc_le_β' : Real.arctan ((tcLo : ℝ) / 100000) ≤ β' := by
        have hbdrop_div : (bLoHi : ℝ) / 1000000000000 + (dropHi : ℝ) / 1000000000000 ≤ (phiLo : ℝ) /
          1000000000000 := (by linarith only [hbdrop_r]); linarith only [hbLo_ge, hphiLo_le,
          hφ_sub_β', hdrop_le, hbdrop_div]
      exact checkS3Idx_sound hn hv_anti hatan_tc_le_β' hβ'_54 hs3_chk
  have hhit_le : ((v2m (warmJP01BinIdx (fuseNextAngle n 3 β')) : ℝ) / 1000000000000) * SN ≤ ((hHi :
    ℝ) / 1000000000000) * SN := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
    (by exact_mod_cast hhit_v2m) (by norm_num)) hSN_pos.le
  have hp_nn : 0 ≤ p := le_trans (by positivity) hp_lo
  have hdiff_ge : (((w j - hHi : ℕ) : ℝ) / 1000000000000) * SN ≤ SN * psiPiecewise B dNat w x' -
    ((v2m (warmJP01BinIdx (fuseNextAngle n 3 β')) : ℝ) / 1000000000000) * SN := by
    rw [Nat.cast_sub hhw]; have hsub_eq : ((w j : ℝ) / 1000000000000) * SN - ((hHi : ℝ) /
      1000000000000) * SN = (((w j : ℝ) - hHi) / 1000000000000) * SN := (by ring)
    linarith only [hpost_ge, hhit_le, hsub_eq]
  have hp_diff : (√(3 : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 *
    100000000 * 1000000000000) ≤ p * (SN * psiPiecewise B dNat w x' - ((v2m (warmJP01BinIdx
    (fuseNextAngle n 3 β')) : ℝ) / 1000000000000) * SN) := by
    have hm := mul_le_mul hp_lo hdiff_ge (by positivity) hp_nn; have heq : (4 * ((tn : ℝ) / 100000)
      * (99999999 / 100000000) * √(3 : ℝ) / SN) * ((((w j - hHi : ℕ) : ℝ) / 1000000000000) * SN) =
      (√(3 : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 * 100000000 *
      1000000000000) := (by field_simp [hSN_pos.ne']); linarith only [hm, heq]
  have hmd_le_d : minDiffNat B w j ≤ dNat := by
    have hsub : w (j + 1) - w j ≤ dNat := (by have := (hw j hj).2; omega); dsimp only [minDiffNat];
      rw [withForcedNat_eq]
    split_ifs
    · exact hsub
    · exact (Nat.min_le_left _ _).trans hsub
  have hbin_div : 1 - (minDiffNat B w j : ℝ) / dNat ≤ (√(3 : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j -
    hHi : ℕ) : ℝ))) / (100000 * 100000000 * 1000000000000) := by
    set lhsN : ℕ := (dNat - minDiffNat B w j) * 100000 * 100000000 * 1000000000000; set rhsN : ℕ :=
      dNat * 4 * tn * 99999999 * (w j - hHi)
    have hlin : (lhsN : ℝ) ≤ √(3 : ℝ) * (rhsN : ℝ) := by
      refine sq_le_imp_le (by positivity) (by positivity) ?_; have hcast : ((lhsN * lhsN : ℕ) : ℝ) ≤
        ((3 * rhsN * rhsN : ℕ) : ℝ) := Nat.cast_le.2 hsq_nat; push_cast at hcast
      have hrsq : (√(3 : ℝ) * (rhsN : ℝ)) ^ 2 = 3 * (rhsN : ℝ) * rhsN := by
        calc (√(3 : ℝ) * (rhsN : ℝ)) ^ 2 = (√(3 : ℝ)) ^ 2 * (rhsN : ℝ) * rhsN := by ring
          _ = 3 * (rhsN : ℝ) * rhsN := by rw [Real.sq_sqrt (by norm_num)]
      have hlsq : (lhsN : ℝ) ^ 2 = (lhsN : ℝ) * lhsN := (by ring); linarith only [hcast, hrsq, hlsq]
    have hlhs : 1 - (minDiffNat B w j : ℝ) / dNat = (lhsN : ℝ) / ((dNat : ℝ) * (100000 * 100000000 *
      1000000000000)) := by
      dsimp only [lhsN]; rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hmd_le_d]
      field_simp [hd_pos.ne']; ring
    have hrhs : (√(3 : ℝ) * (4 * (tn : ℝ) * 99999999 * ((w j - hHi : ℕ) : ℝ))) / (100000 * 100000000
      * 1000000000000) = (√(3 : ℝ) * (rhsN : ℝ)) / ((dNat : ℝ) * (100000 * 100000000 *
      1000000000000)) := (by dsimp only [rhsN]; push_cast; field_simp [hd_pos.ne']); rw [hlhs, hrhs]
    exact div_le_div_of_nonneg_right hlin (by positivity)
  linarith only [hstep_sn, hp_diff, hbin_div]
private theorem warmJP01_stage3_step {B n : ℕ} {v2m : ℕ → ℕ} {stFn : ℕ → M2StageScalar} {wFn : ℕ → ℕ
  → ℕ} {binFn : ℕ → ℕ → M2BinCert} (hB : 1 ≤ B) (hn : 200 ≤ n) (hv_anti : ∀ {i j : ℕ}, i ≤ j → j <
  420 → v2m j ≤ v2m i) (hst : checkWarmJP01Stage3 B v2m stFn wFn binFn = true) (betas : Fin 2 → ℝ)
  (hbetas : ValidStageBetas n 3 (5 / 4) betas) :
    let phiFn := phiFnOfWmSt stFn; let Φ := warmJP01Potential B v2m stFn wFn n
    1 + stepWeight n 3 (phiFn 3) betas 0 * Φ 3 (nextBetasRamp n 3 (phiFn 3) betas) + (∑ o ∈
      Finset.univ.erase 0, stepWeight n 3 (phiFn 3) betas o * expOnHitFuse Φ n 3 o (nextBetasRamp n
      3 (phiFn 3) betas)) ≤ Φ 3 betas := by
  intro phiFn Φ
  have hΦ3 : ∀ b, Φ 3 b = wmStagePot B phiFn stFn wFn n 3 b := fun _ => by
    dsimp only [Φ, phiFn, warmJP01Potential]; simp
  have hexp : ∀ o b, expOnHitFuse Φ n 3 o b =
      warmJP01R2Cost2 v2m n (nextStageFuseBetas n 3 o b) := fun _ _ => by
    dsimp only [expOnHitFuse, Φ, warmJP01Potential]; simp
  rw [hΦ3, hΦ3, sum_erase_zero_fin_four, hexp, hexp, hexp]; dsimp only [checkWarmJP01Stage3] at hst
  rcases hsr : stFn 3 with ⟨tn, phiHi, phiLo, cSelf, dNat, stepNum, cNat, ⟨sLk, _, _, _, _, hLk,
    hBoth⟩⟩; rw [hsr] at hst
  simp only [withForcedNat_eq, Bool.and_eq_true, and_assoc, Nat.ble_eq] at hst; rcases hst with
    ⟨ht_lo, ht_hi, hat_hi, hat_lo, hcS_pos, hcS_sq, hd1000, hcSB, hclick_chk, hslope_all, hs3_lock,
    hboth_v2m0, hstep_w0, hlock_comb, hbins⟩; have hd1 : 1 ≤ dNat := (by omega); have hw :=
    knotSlope_of_allRange hslope_all; set SN : ℝ := √((2 : ℝ) ^ n); obtain ⟨hSN_ge, hN_ge⟩ :=
    pow_two_200_bounds hn; have hn100 : 100 ≤ n := (by omega); have hSN_pos : 0 < SN :=
    lt_of_lt_of_le (by positivity) hSN_ge
  rcases phi_and_lockedAlpha_bounds_fuse_100 (m := 2) (by omega) (by omega) hn100 (by omega : 1 ≤ 3)
    (by omega : 3 ≤ 1024) ht_lo ht_hi with ⟨_, hφ2θ, _, hlock_bds⟩; set φ : ℝ := Real.arctan ((tn :
    ℝ) / 100000); have hφ_eq : phiFn 3 = φ := (by dsimp only [phiFn, phiFnOfWmSt]; rw [hsr])
  have hdNat_eq : (stFn 3).dNat = dNat := (by rw [hsr]); have hs_cap : ∀ i : Fin 2,
      (remStepsSlot n 3 φ (betas i) : ℝ) ≤ ((cSelf : ℝ) / 1000000000000) * SN := fun i => by
    have hm : (remStepsSlot n 3 φ (betas i) : ℝ) ≤ (remStepsSlot n 3 φ (halfAngleSet n 3) : ℝ) :=
      (by exact_mod_cast remStepsSlot_mono_beta (n := n) (r := 3) (by omega) φ (hbetas i).1)
    exact hm.trans (remStepsSlot_halfAngleSet_le_of_atan200Hi_sq hn100 (by omega) (by omega) ht_lo
      ht_hi hat_hi hcS_pos hcS_sq)
  rw [hφ_eq]; set postB := nextBetasRamp n 3 φ betas; have hθ3_nn : 0 ≤ halfAngleSet n 3 :=
    Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hpost_valid : ValidStageBetas n 3 (5 / 4) postB := fun i => by
    dsimp only [postB, nextBetasRamp, nextBetaSlot]; split_ifs with hlt
    · exact ⟨by linarith [(hbetas i).1, hθ3_nn], by linarith [hlt, hφ2θ]⟩
    · exact hbetas i
  obtain ⟨⟨hg1, hmax1⟩, ⟨hg2, hmax2⟩, ⟨hg3, hmax3⟩⟩ := warmJP01Guard_nextStageFuseBetas hn
    hpost_valid; have hc1 : warmJP01R2Cost2 v2m n (nextStageFuseBetas n 3 ⟨1, (Nat.lt_of_sub_eq_succ
    rfl : 1 < 2 ^ 2)⟩ postB) = ((v2m (warmJP01BinIdx (fuseNextAngle n 3 (postB s1))) : ℝ) /
    1000000000000) * SN := (by dsimp only [warmJP01R2Cost2, SN]; rw [ite_eq_left hg1, hmax1])
  have hc2 : warmJP01R2Cost2 v2m n (nextStageFuseBetas n 3 ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^
    2)⟩ postB) = ((v2m (warmJP01BinIdx (fuseNextAngle n 3 (postB s0))) : ℝ) / 1000000000000) * SN :=
    (by dsimp only [warmJP01R2Cost2, SN]; rw [ite_eq_left hg2, hmax2])
  have hc3 : warmJP01R2Cost2 v2m n (nextStageFuseBetas n 3 ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^
    2)⟩ postB) = ((v2m (warmJP01BinIdx (halfAngleSet n 2)) : ℝ) / 1000000000000) * SN :=
    (by dsimp only [warmJP01R2Cost2, SN]; rw [ite_eq_left hg3, hmax3]); dsimp only [wmStagePot]
  rw [hφ_eq, hdNat_eq, hc1, hc2, hc3, stepWeight_fin2_zero, stepWeight_fin2_one,
    stepWeight_fin2_two, stepWeight_fin2_three]; by_cases h0 : betas s0 < φ
  · have hα0 : stepAlpha n 3 φ (betas s0) ^ 2 = 1 :=
      (by dsimp only [stepAlpha]; rw [ite_eq_left h0, one_pow])
    have hd0_pos : 1 ≤ remStepsSlot n 3 φ (betas s0) := by
      by_contra hz; have hez : remStepsSlot n 3 φ (betas s0) = 0 := (by omega)
      linarith [(remStepsSlot_eq_zero_iff (n := n) (r := 3) (by omega) φ (betas s0)).1 hez]
    have hs0_post : remStepsSlot n 3 φ (postB s0) = remStepsSlot n 3 φ (betas s0) - 1 := by
      dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 3) (by omega),
        ite_eq_left h0]
    have hpb0 : postB s0 = betas s0 + 2 * halfAngleSet n 3 :=
      (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; rw [ite_eq_left h0])
    by_cases h1 : betas s1 < φ
    · have hα1 : stepAlpha n 3 φ (betas s1) ^ 2 = 1 :=
        (by dsimp only [stepAlpha]; rw [ite_eq_left h1, one_pow])
      have hd1_pos : 1 ≤ remStepsSlot n 3 φ (betas s1) := by
        by_contra hz; have hez : remStepsSlot n 3 φ (betas s1) = 0 := (by omega)
        linarith [(remStepsSlot_eq_zero_iff (n := n) (r := 3) (by omega) φ (betas s1)).1 hez]
      have hs1_post : remStepsSlot n 3 φ (postB s1) = remStepsSlot n 3 φ (betas s1) - 1 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 3)
          (by omega), ite_eq_left h1]
      rw [hα0, hα1, hs0_post, hs1_post, Nat.cast_sub hd0_pos, Nat.cast_sub hd1_pos, Nat.cast_one,
        wmPotVal_sub_one]; exact le_of_eq (by ring)
    · have h1_ge : φ ≤ betas s1 := not_lt.1 h1; have hs1_z : remStepsSlot n 3 φ (betas s1) = 0 :=
        (remStepsSlot_eq_zero_iff (n := n) (r := 3) (by omega) φ (betas s1)).2 h1_ge
      have hs1_post : remStepsSlot n 3 φ (postB s1) = 0 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 3)
          (by omega)]; simp only [h1, ↓reduceIte]
      set p1 : ℝ := 1 - lockedAlpha (betas s1) (halfAngleSet n 3) ^ 2
      have hα1 : stepAlpha n 3 φ (betas s1) ^ 2 = 1 - p1 :=
        (by dsimp only [stepAlpha, p1]; simp only [h1, ↓reduceIte]; ring); have hp1_lo := (hlock_bds
        (betas s1) h1_ge (hbetas s1).2).1; rw [Nat.cast_ofNat] at hp1_lo; rw [hα0, hα1, hs0_post,
        hs1_post, hs1_z, hpb0, Nat.cast_zero, wmPotVal_comm _ _ _ _ _ 0, wmPotVal_comm _ _ _ _ _ 0]
      have hstep := warmJP01_stage3_single_locked_step hB hn hv_anti ht_lo ht_hi hat_lo hd1000 hcSB
        hw hbins hp1_lo (hbetas s0).1 h0 (hs_cap s0); dsimp only at hstep
      exact le_of_eq_of_le (by ring) hstep
  · have h0_ge : φ ≤ betas s0 := not_lt.1 h0; have hs0_z : remStepsSlot n 3 φ (betas s0) = 0 :=
      (remStepsSlot_eq_zero_iff (n := n) (r := 3) (by omega) φ (betas s0)).2 h0_ge
    have hs0_post : remStepsSlot n 3 φ (postB s0) = 0 := by
      dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 3) (by omega)]
      simp only [h0, ↓reduceIte]
    have hpb0 : postB s0 = betas s0 :=
      (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [h0, ↓reduceIte])
    set p0 : ℝ := 1 - lockedAlpha (betas s0) (halfAngleSet n 3) ^ 2
    have hα0 : stepAlpha n 3 φ (betas s0) ^ 2 = 1 - p0 :=
      (by dsimp only [stepAlpha, p0]; simp only [h0, ↓reduceIte]; ring); obtain ⟨hp0_lo, hp0_hi⟩ :=
      hlock_bds (betas s0) h0_ge (hbetas s0).2; rw [Nat.cast_ofNat] at hp0_lo hp0_hi
    by_cases h1 : betas s1 < φ
    · have hα1 : stepAlpha n 3 φ (betas s1) ^ 2 = 1 :=
        (by dsimp only [stepAlpha]; rw [ite_eq_left h1, one_pow])
      have hs1_post : remStepsSlot n 3 φ (postB s1) = remStepsSlot n 3 φ (betas s1) - 1 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 3)
          (by omega), ite_eq_left h1]
      have hpb1 : postB s1 = betas s1 + 2 * halfAngleSet n 3 :=
        (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; rw [ite_eq_left h1]); rw [hα0, hα1,
        hs0_post, hs1_post, hs0_z, hpb1, Nat.cast_zero]
      have hstep := warmJP01_stage3_single_locked_step hB hn hv_anti ht_lo ht_hi hat_lo hd1000 hcSB
        hw hbins hp0_lo (hbetas s1).1 h1 (hs_cap s1); dsimp only at hstep
      exact le_of_eq_of_le (by ring) hstep
    · have h1_ge : φ ≤ betas s1 := not_lt.1 h1; have hs1_z : remStepsSlot n 3 φ (betas s1) = 0 :=
        (remStepsSlot_eq_zero_iff (n := n) (r := 3) (by omega) φ (betas s1)).2 h1_ge
      have hs1_post : remStepsSlot n 3 φ (postB s1) = 0 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot (n := n) (r := 3)
          (by omega)]; simp only [h1, ↓reduceIte]
      have hpb1 : postB s1 = betas s1 :=
        (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [h1, ↓reduceIte])
      set p1 : ℝ := 1 - lockedAlpha (betas s1) (halfAngleSet n 3) ^ 2
      have hα1 : stepAlpha n 3 φ (betas s1) ^ 2 = 1 - p1 :=
        (by dsimp only [stepAlpha, p1]; simp only [h1, ↓reduceIte]; ring)
      obtain ⟨hp1_lo, hp1_hi⟩ := hlock_bds (betas s1) h1_ge (hbetas s1).2
      rw [Nat.cast_ofNat] at hp1_lo hp1_hi; rw [hα0, hα1, hs0_post, hs1_post, hs0_z, hs1_z, hpb0,
        hpb1, Nat.cast_zero, wmPotVal_diag hd1 hw SN 0, zero_add]; simp only [sub_sub_cancel]
      set p_min : ℝ := 4 * ((tn : ℝ) / 100000) * (99999999 / 100000000) * √(3 : ℝ) / SN
      have ht_pos : (0 : ℝ) < tn := Nat.cast_pos.2 (by omega); have hp_min_pos : 0 < p_min :=
        (by dsimp only [p_min]; positivity); obtain ⟨h1q0_pos, h2p_rho, hprod_le⟩ :=
        two_locked_one_sub_q0_bounds hp_min_pos hp0_lo hp1_lo hp0_hi hp1_hi; have hhit1_v :=
        checkS3Idx_sound hn hv_anti h1_ge (hbetas s1).2 hs3_lock
      have hhit2_v := checkS3Idx_sound hn hv_anti h0_ge (hbetas s0).2 hs3_lock
      have hhit1 : ((v2m (warmJP01BinIdx (fuseNextAngle n 3 (betas s1))) : ℝ) / 1000000000000) * SN
        ≤ ((hLk : ℝ) / 1000000000000) * SN := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (by exact_mod_cast hhit1_v) (by norm_num)) hSN_pos.le; have hhit2 : ((v2m (warmJP01BinIdx
        (fuseNextAngle n 3 (betas s0))) : ℝ) / 1000000000000) * SN ≤ ((hLk : ℝ) / 1000000000000) *
        SN := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by exact_mod_cast hhit2_v)
        (by norm_num)) hSN_pos.le; set extra : ℕ := cond (Nat.ble hLk hBoth) (hBoth - hLk) 0
      have hboth_le_ex : hBoth ≤ hLk + extra := by
        dsimp only [extra]; by_cases h : hLk ≤ hBoth
        · rw [Nat.ble_eq.mpr h, Bool.cond_true]; omega
        · rw [Bool.eq_false_iff.2 fun hh => h (Nat.ble_eq.mp hh), Bool.cond_false]; omega
      have hsin_θ2_lt : Real.sin (halfAngleSet n 2) < 420 / 512 := by
        dsimp only [halfAngleSet]; have hrt0 : (0 : ℝ) ≤ √(2 / (2 : ℝ) ^ n) := Real.sqrt_nonneg _
        have hdiv1 : (2 : ℝ) / (2 : ℝ) ^ n ≤ 1 := by
          rw [div_le_one (by positivity)]; have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ 200 := (by norm_num)
          linarith only [hN_ge, h2]
        rw [Nat.cast_ofNat, Real.sin_arcsin (by linarith only [hrt0]) (Real.sqrt_le_one.2 hdiv1)]
        have hle : √(2 / (2 : ℝ) ^ n) ≤ 1 / 2 := by
          refine sq_le_imp_le (Real.sqrt_nonneg _) (by norm_num) ?_; rw [Real.sq_sqrt
            (by positivity), div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]; have h8 : (8 :
            ℝ) ≤ (2 : ℝ) ^ 200 := (by norm_num); linarith only [hN_ge, h8]
        linarith only [hle]
      have hidx2_lt : warmJP01BinIdx (halfAngleSet n 2) < 420 := by
        obtain ⟨_, _, hθ2_13, -⟩ := halfAngleSet_bounds_100 hn100 (by norm_num : 1 ≤ 2)
          (by norm_num : 2 ≤ 1024)
        have hsin2_nn : 0 ≤ Real.sin (halfAngleSet n 2) := Real.sin_nonneg_of_nonneg_of_le_pi
          (Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)) (by linarith only [hθ2_13, Real.pi_gt_three])
        have hfl_lt : ⌊512 * Real.sin (halfAngleSet n 2)⌋₊ < 420 := (Nat.floor_lt (mul_nonneg
          (by norm_num) hsin2_nn)).2 (by rw [Nat.cast_ofNat]; linarith only [hsin_θ2_lt])
        dsimp [warmJP01BinIdx]; omega
      have hhit3_v : v2m (warmJP01BinIdx (halfAngleSet n 2)) ≤ hLk + extra := ((hv_anti (Nat.zero_le
        _) hidx2_lt).trans hboth_v2m0).trans hboth_le_ex
      have hhit3 : ((v2m (warmJP01BinIdx (halfAngleSet n 2)) : ℝ) / 1000000000000) * SN ≤ (((hLk :
        ℝ) + extra) / 1000000000000) * SN := by
        have hr : (v2m (warmJP01BinIdx (halfAngleSet n 2)) : ℝ) ≤ (hLk : ℝ) + extra :=
          (by exact_mod_cast hhit3_v); exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          hr (by norm_num)) hSN_pos.le
      have hp0_nn : 0 ≤ p0 := le_trans hp_min_pos.le hp0_lo
      have hp1_nn : 0 ≤ p1 := le_trans hp_min_pos.le hp1_lo
      have hp0_le1 : p0 ≤ 1 := hp0_hi.trans (by norm_num)
      have hp1_le1 : p1 ≤ 1 := hp1_hi.trans (by norm_num); set q0 : ℝ := (1 - p0) * (1 - p1)
      have hhit_sum : p0 * (1 - p1) * (((v2m (warmJP01BinIdx (fuseNextAngle n 3 (betas s1))) : ℝ) /
        1000000000000) * SN) + (1 - p0) * p1 * (((v2m (warmJP01BinIdx (fuseNextAngle n 3 (betas
        s0))) : ℝ) / 1000000000000) * SN) + p0 * p1 * (((v2m (warmJP01BinIdx (halfAngleSet n 2)) :
        ℝ) / 1000000000000) * SN) ≤ (1 - q0) * ((((hLk : ℝ) + (extra : ℝ) / 200000000) /
        1000000000000) * SN) := by
        have hm1 := mul_le_mul_of_nonneg_left hhit1 (mul_nonneg hp0_nn (sub_nonneg.2 hp1_le1))
        have hm2 := mul_le_mul_of_nonneg_left hhit2 (mul_nonneg (sub_nonneg.2 hp0_le1) hp1_nn)
        have hm3 := mul_le_mul_of_nonneg_left hhit3 (mul_nonneg hp0_nn hp1_nn); have hm_ex : (p0 *
          p1) * (((extra : ℝ) / 1000000000000) * SN) ≤ ((1 / 200000000) * (1 - q0)) * (((extra : ℝ)
          / 1000000000000) * SN) := mul_le_mul_of_nonneg_right hprod_le (by positivity)
        have hsum_w : p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1 = 1 - q0 := (by dsimp only [q0]; ring)
        linarith [hm1, hm2, hm3, hm_ex, show p0 * (1 - p1) * (((hLk : ℝ) / 1000000000000) * SN) +
              (1 - p0) * p1 * (((hLk : ℝ) / 1000000000000) * SN) +
              p0 * p1 * ((((hLk : ℝ) + extra) / 1000000000000) * SN) =
            (p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1) * (((hLk : ℝ) / 1000000000000) * SN) +
              (p0 * p1) * (((extra : ℝ) / 1000000000000) * SN) by ring,
          show (p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1) * (((hLk : ℝ) / 1000000000000) * SN) =
            (1 - q0) * (((hLk : ℝ) / 1000000000000) * SN) by rw [hsum_w],
          show (1 - q0) * (((hLk : ℝ) / 1000000000000) * SN) +
              ((1 / 200000000) * (1 - q0)) * (((extra : ℝ) / 1000000000000) * SN) =
            (1 - q0) * ((((hLk : ℝ) + (extra : ℝ) / 200000000) / 1000000000000) * SN) by ring]
      have hclick := clickRow_sound (m := 2) (n := n) (r := 3) (by omega) (by omega) ht_lo
        hclick_chk; have hclick' : 1 / (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ))))) ≤
        ((stepNum : ℝ) / 1000000000000) * SN := (by simpa [p_min, SN] using hclick)
      have h1_le : 1 ≤ (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) := by
        have hden_pos : 0 < 2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ)))) :=
          (by have : (0 : ℝ) < 1 - 2 * (1 / (100000000 * (2 : ℝ))) := (by norm_num); positivity)
        calc (1 : ℝ) = (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ))))) *
              (1 / (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ)))))) := by
              field_simp [hden_pos.ne']
          _ ≤ (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) :=
              mul_le_mul h2p_rho hclick' (by positivity) h1q0_pos.le
      have hcomb_r : 200000000 * (hLk : ℝ) + extra ≤ 200000000 * ((wFn 3 0 - stepNum : ℕ) : ℝ) := by
        exact_mod_cast (show 200000000 * hLk + extra ≤ 200000000 * (wFn 3 0 - stepNum) from
          hlock_comb)
      rw [Nat.cast_sub hstep_w0] at hcomb_r
      have hcomb_sn : (((hLk : ℝ) + (extra : ℝ) / 200000000) / 1000000000000) * SN ≤ (((wFn 3 0 : ℝ)
        - stepNum) / 1000000000000) * SN := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (by linarith) (by norm_num)) hSN_pos.le
      have hm_comb := mul_le_mul_of_nonneg_left hcomb_sn h1q0_pos.le; linarith [hhit_sum, h1_le,
        hm_comb, show (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) + (1 - q0) * ((((wFn 3 0 :
        ℝ) - stepNum) / 1000000000000) * SN) + q0 * (((wFn 3 0 : ℝ) / 1000000000000) * SN) = ((wFn 3
        0 : ℝ) / 1000000000000) * SN by ring]
private theorem warmJP01StageIdx_props {B r : ℕ} {v2m : ℕ → ℕ} {stFn : ℕ → M2StageScalar} {wFn : ℕ →
  ℕ → ℕ} {binFn : ℕ → ℕ → M2BinCert} (hr3 : 3 ≤ r) (hst : checkWarmJP01StageIdx B v2m stFn wFn binFn
  (r - 3) = true) : 500 ≤ (stFn r).tNum ∧ (stFn r).tNum ≤ 200000 ∧ checkAtan200Hi (stFn r).tNum
  (stFn r).phiHi = true ∧ 1000 ≤ (stFn r).dNat ∧ allRange (checkM2KnotSlope (stFn r).dNat (wFn r)) B
  = true := by
  cases hidx : r - 3 with
  | zero =>
    have hr_eq3 : r = 3 := (by omega); subst hr_eq3
    rw [hidx] at hst; dsimp only [checkWarmJP01StageIdx, checkWarmJP01Stage3] at hst
    rcases hsr : stFn 3 with ⟨tn, phiHi, phiLo, cSelf, dNat, stepNum, cNat, ⟨sLk, _, _, _, _, hLk,
      hBoth⟩⟩; rw [hsr] at hst; simp only [withForcedNat_eq, Bool.and_eq_true, and_assoc,
      Nat.ble_eq] at hst; rcases hst with ⟨ht_lo, ht_hi, hat_hi, _, _, _, hd1000, _, _, hslope, _⟩
    exact ⟨ht_lo, ht_hi, hat_hi, hd1000, hslope⟩
  | succ s' =>
    rw [hidx] at hst; dsimp only [checkWarmJP01StageIdx, checkWarm2StageIdx] at hst
    have hr_eq : s' + 2 + 2 = r := (by omega); rw [hr_eq] at hst; rcases hsr : stFn r with ⟨tn,
      phiHi, phiLo, cSelf, dNat, stepNum, cNat, ⟨tBfLo, tdHi, numU, uLock, psiLock, hLock, hBoth⟩⟩
    rw [hsr] at hst; simp only [Bool.and_eq_true, and_assoc] at hst; rcases hst with ⟨ht_lo_d,
      ht_hi_d, hat_hi, _, _, _, hd1000_d, _, _, hslope, _⟩; exact ⟨of_decide_eq_true ht_lo_d,
      of_decide_eq_true ht_hi_d, hat_hi, of_decide_eq_true hd1000_d, hslope⟩
private theorem warmJP01_stageGe4_step {B n r : ℕ} {v2m : ℕ → ℕ} {stFn : ℕ → M2StageScalar} {wFn : ℕ
  → ℕ → ℕ} {binFn : ℕ → ℕ → M2BinCert} (hB : 1 ≤ B) (hn : 200 ≤ n) (hr4 : 4 ≤ r) (hr1024 : r ≤ 1024)
  (hst_cur : checkWarmJP01StageIdx B v2m stFn wFn binFn (r - 3) = true) (hst_prev :
  checkWarmJP01StageIdx B v2m stFn wFn binFn (r - 4) = true) (betas : Fin 2 → ℝ) (hbetas :
  ValidStageBetas n r (5 / 4) betas) :
    let phiFn := phiFnOfWmSt stFn; let Φ := warmJP01Potential B v2m stFn wFn n
    1 + stepWeight n r (phiFn r) betas 0 * Φ r (nextBetasRamp n r (phiFn r) betas) + (∑ o ∈
      Finset.univ.erase 0, stepWeight n r (phiFn r) betas o * expOnHitFuse Φ n r o (nextBetasRamp n
      r (phiFn r) betas)) ≤ Φ r betas := by
  intro phiFn Φ; have hr2 : 2 ≤ r := (by omega); have hr1 : 1 ≤ r := (by omega); have hrp3 : 3 ≤ r -
    1 := (by omega); have hrp1 : 1 ≤ r - 1 := (by omega); have hrp1024 : r - 1 ≤ 1024 := (by omega)
  have hn100 : 100 ≤ n := (by omega); have h2r : 2 * r ≤ 2 ^ n := two_mul_le_pow_100 hn100 hr1024
  have hΦr : ∀ b, Φ r b = wmStagePot B phiFn stFn wFn n r b := fun _ => by
    dsimp only [Φ, warmJP01Potential]; rw [ite_eq_right (by omega : ¬ r ≤ 1), ite_eq_right
      (by omega : r ≠ 2)]
  have hΦp : ∀ b, Φ (r - 1) b = wmStagePot B phiFn stFn wFn n (r - 1) b := fun _ => by
    dsimp only [Φ, warmJP01Potential]; rw [ite_eq_right (by omega : ¬ r - 1 ≤ 1), ite_eq_right
      (by omega : r - 1 ≠ 2)]
  have hexp : ∀ o b, expOnHitFuse Φ n r o b =
      wmStagePot B phiFn stFn wFn n (r - 1) (nextStageFuseBetas n r o b) := fun o b => by
    dsimp only [expOnHitFuse]; rw [ite_eq_left hr2]; exact hΦp _
  rw [hΦr, hΦr, sum_erase_zero_fin_four, hexp, hexp, hexp]
  have hprev_props := warmJP01StageIdx_props hrp3 (by simpa [show r - 1 - 3 = r - 4 by omega]
    using hst_prev)
  have hcur_eq : r - 3 = (r - 4) + 1 := (by omega)
  rw [hcur_eq] at hst_cur; dsimp only [checkWarmJP01StageIdx, checkWarm2StageIdx] at hst_cur
  have hr_sub : r - 4 + 2 + 2 = r := (by omega); have hrp_sub1 : r - 4 + 2 + 1 = r - 1 := (by omega)
  have hidx_ne0 : (r - 4 + 2 == 0) = false := beq_false_of_ne (by omega)
  rw [hr_sub, hrp_sub1] at hst_cur; rcases hsr : stFn r with ⟨tn, phiHi, phiLo, cSelf, dNat,
    stepNum, cNat, ⟨tBfLo, tdHi, numU, uLock, psiLock, hLock, hBoth⟩⟩
  rcases hsp : stFn (r - 1) with ⟨tp, phiHiP, phiLoP, cSelfP, dNatP, stepNumP, cNatP, ⟨tBfLoP,
    tdHiP, numUP, uLockP, psiLockP, hLockP, hBothP⟩⟩
  rw [hsr, hsp] at hst_cur; rw [hsp] at hprev_props; dsimp only at hprev_props
  rcases hprev_props with ⟨_, _, hat_prev, hdP1000, hslopeP_all⟩; simp only [hidx_ne0,
    Bool.false_eq_true, ↓reduceIte, withForcedNat_eq, Bool.and_eq_true, and_assoc] at hst_cur
  rcases hst_cur with ⟨ht_lo_d, ht_hi_d, hat_hi, hat_lo, hcS_pos_d, hcS_sq_d, hd1000_d, hcSB_d,
    hclick_chk, hslope_all, hdrift_lock, hpsi_lock, huh_lock_d, hcb_lock_d, hstep_w0_d,
    hlock_comb_d, hbins⟩
  have ht_lo := of_decide_eq_true ht_lo_d; have ht_hi := of_decide_eq_true ht_hi_d; have hd1000 :=
    of_decide_eq_true hd1000_d; have hd1 : 1 ≤ dNat := (by omega); have hdP1 : 1 ≤ dNatP :=
    (by omega); have hcSB := of_decide_eq_true hcSB_d; have hw := knotSlope_of_allRange hslope_all
  have hwP := knotSlope_of_allRange hslopeP_all; set SN : ℝ := √((2 : ℝ) ^ n); obtain ⟨hSN_ge, _⟩ :=
    pow_two_bounds_100 hn100; have hSN_pos : 0 < SN := lt_of_lt_of_le (by positivity) hSN_ge
  rcases halfAngleSet_bounds_100 hn100 hrp1 hrp1024 with ⟨hθp_lo, -⟩
  rcases phi_and_lockedAlpha_bounds_fuse_100 (m := 2) (by omega) (by omega) hn100 hr1 hr1024 ht_lo
    ht_hi with ⟨h2θ_φ, _, h54_lt, hlock_bds⟩
  set φ : ℝ := Real.arctan ((tn : ℝ) / 100000); set φp : ℝ := Real.arctan ((tp : ℝ) / 100000)
  have hφ_eq : phiFn r = φ := (by dsimp only [phiFn, phiFnOfWmSt]; rw [hsr]); have hφp_eq : phiFn (r
    - 1) = φp := (by dsimp only [phiFn, phiFnOfWmSt]; rw [hsp]); have hdNat_eq : (stFn r).dNat =
    dNat := (by rw [hsr]); have hdNatP_eq : (stFn (r - 1)).dNat = dNatP := (by rw [hsp])
  have hθc_nn : 0 ≤ halfAngleSet n r := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hβFuse_φ : Real.arcsin (√(((r - 1 : ℕ) : ℝ) / r) * Real.sin φ) ≤ fuseNextAngle n r φ :=
    arcsin_sqrt_nat_sub_ratio_le_fuseNextAngle hr2 h2r (by linarith) (Real.arctan_lt_pi_div_two _)
  obtain ⟨huLock_le_c, hc_bound, huLock_bound⟩ := fuseDriftCert_sound hr2 hSN_ge hθp_lo
    (atan200Hi_sound hat_prev) hβFuse_φ hdrift_lock; set sReset : ℝ := (remStepsSlot n (r - 1) φp
    (halfAngleSet n (r - 1)) : ℝ)
  have hc_cap : sReset ≤ ((cNat : ℝ) / 1000000000000) * SN := by
    dsimp only [sReset, remStepsSlot]
    have hθp_pos : 0 < halfAngleSet n (r - 1) := lt_of_lt_of_le (by positivity) hθp_lo
    by_cases hge : halfAngleSet n (r - 1) ≤ φp
    · linarith [Nat.ceil_lt_add_one (div_nonneg (sub_nonneg.2 hge) (by positivity :
        0 ≤ 2 * halfAngleSet n (r - 1))), hc_bound]
    · have hz : ⌈(φp - halfAngleSet n (r - 1)) / (2 * halfAngleSet n (r - 1))⌉₊ = 0 :=
        Nat.ceil_eq_zero.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)); rw [hz,
        Nat.cast_zero]; exact mul_nonneg (by positivity) hSN_pos.le
  have hs_cap : ∀ i : Fin 2,
      (remStepsSlot n r φ (betas i) : ℝ) ≤ ((cSelf : ℝ) / 1000000000000) * SN := fun i => by
    have hm : (remStepsSlot n r φ (betas i) : ℝ) ≤ (remStepsSlot n r φ (halfAngleSet n r) : ℝ) :=
      (by exact_mod_cast remStepsSlot_mono_beta hr1 φ (hbetas i).1)
    exact hm.trans (remStepsSlot_halfAngleSet_le_of_atan200Hi_sq hn100 hr1 hr1024 ht_lo ht_hi hat_hi
      (of_decide_eq_true hcS_pos_d) (of_decide_eq_true hcS_sq_d))
  have hsLock_le : ∀ β, φ ≤ β → β ≤ 5 / 4 → (remStepsSlot n (r - 1) φp (fuseNextAngle n r β) : ℝ) ≤
        ((uLock : ℝ) / 1000000000000) * SN := fun β hβ_ge hβ_hi => by
    have hf_mono : fuseNextAngle n r φ ≤ fuseNextAngle n r β := fuseNextAngle_mono hr2 h2r
      (by linarith) hβ_ge (hβ_hi.trans h54_lt.le); have hm : (remStepsSlot n (r - 1) φp
      (fuseNextAngle n r β) : ℝ) ≤ (remStepsSlot n (r - 1) φp (fuseNextAngle n r φ) : ℝ) :=
      (by exact_mod_cast remStepsSlot_mono_beta hrp1 φp hf_mono)
    exact hm.trans (remStepsSlot_le_of_three_add_max hrp1 (by positivity) huLock_bound)
  dsimp only [wmStagePot]; rw [hφ_eq, hφp_eq, hdNat_eq, hdNatP_eq]
  set postB := nextBetasRamp n r φ betas; have hns1_0 : nextStageFuseBetas n r ⟨1,
    (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postB s0 = halfAngleSet n (r - 1) := (by rfl)
  have hns1_1 : nextStageFuseBetas n r ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ postB s1 =
    fuseNextAngle n r (postB s1) := rfl; have hns2_0 : nextStageFuseBetas n r ⟨2,
    (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postB s0 = fuseNextAngle n r (postB s0) := rfl
  have hns2_1 : nextStageFuseBetas n r ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ postB s1 =
    halfAngleSet n (r - 1) := (by rfl); have hns3_0 : nextStageFuseBetas n r ⟨3,
    (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postB s0 = halfAngleSet n (r - 1) := (by rfl)
  have hns3_1 : nextStageFuseBetas n r ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ postB s1 =
    halfAngleSet n (r - 1) := (by rfl); have hsR_eq : (remStepsSlot n (r - 1) φp (halfAngleSet n (r
    - 1)) : ℝ) = sReset := rfl; rw [hns1_0, hns1_1, hns2_0, hns2_1, hns3_0, hns3_1, hsR_eq,
    stepWeight_fin2_zero, stepWeight_fin2_one, stepWeight_fin2_two, stepWeight_fin2_three]
  by_cases h0 : betas s0 < φ
  · have hα0 : stepAlpha n r φ (betas s0) ^ 2 = 1 :=
      (by dsimp only [stepAlpha]; rw [ite_eq_left h0, one_pow])
    have hd0_pos : 1 ≤ remStepsSlot n r φ (betas s0) := by
      by_contra hz; have hez : remStepsSlot n r φ (betas s0) = 0 := (by omega)
      linarith [(remStepsSlot_eq_zero_iff hr1 φ (betas s0)).1 hez]
    have hs0_post : remStepsSlot n r φ (postB s0) = remStepsSlot n r φ (betas s0) - 1 :=
      (by dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1, ite_eq_left h0])
    have hpb0 : postB s0 = betas s0 + 2 * halfAngleSet n r :=
      (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; rw [ite_eq_left h0])
    by_cases h1 : betas s1 < φ
    · have hα1 : stepAlpha n r φ (betas s1) ^ 2 = 1 :=
        (by dsimp only [stepAlpha]; rw [ite_eq_left h1, one_pow])
      have hd1_pos : 1 ≤ remStepsSlot n r φ (betas s1) := by
        by_contra hz; have hez : remStepsSlot n r φ (betas s1) = 0 := (by omega)
        linarith [(remStepsSlot_eq_zero_iff hr1 φ (betas s1)).1 hez]
      have hs1_post : remStepsSlot n r φ (postB s1) = remStepsSlot n r φ (betas s1) - 1 :=
        (by dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1, ite_eq_left h1])
      rw [hα0, hα1, hs0_post, hs1_post, Nat.cast_sub hd0_pos, Nat.cast_sub hd1_pos, Nat.cast_one,
        wmPotVal_sub_one]; exact le_of_eq (by ring)
    · have h1_ge : φ ≤ betas s1 := not_lt.1 h1; have hs1_z : remStepsSlot n r φ (betas s1) = 0 :=
        (remStepsSlot_eq_zero_iff hr1 φ (betas s1)).2 h1_ge
      have hs1_post : remStepsSlot n r φ (postB s1) = 0 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1]; simp only [h1,
          ↓reduceIte]
      set p1 : ℝ := 1 - lockedAlpha (betas s1) (halfAngleSet n r) ^ 2
      have hα1 : stepAlpha n r φ (betas s1) ^ 2 = 1 - p1 :=
        (by dsimp only [stepAlpha, p1]; simp only [h1, ↓reduceIte]; ring); have hp1_lo := (hlock_bds
        (betas s1) h1_ge (hbetas s1).2).1; rw [hα0, hα1, hs0_post, hs1_post, hs1_z, hpb0,
        Nat.cast_zero, wmPotVal_comm _ _ _ _ _ 0, wmPotVal_comm _ _ _ _ _ 0, wmPotVal_comm B dNatP
        (wFn (r - 1)) SN _ sReset]
      have hstep := warm2_stageGe3_single_locked_step hB hn100 hr2 hr1024 ht_lo ht_hi hat_lo hd1000
        hcSB hdP1 hat_prev hw hwP hbins hp1_lo (hbetas s0).1 h0 hc_cap (hs_cap s0)
      dsimp only at hstep; exact le_of_eq_of_le (by ring) hstep
  · have h0_ge : φ ≤ betas s0 := not_lt.1 h0; have hs0_z : remStepsSlot n r φ (betas s0) = 0 :=
      (remStepsSlot_eq_zero_iff hr1 φ (betas s0)).2 h0_ge
    have hs0_post : remStepsSlot n r φ (postB s0) = 0 := by
      dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1]; simp only [h0,
        ↓reduceIte]
    have hpb0 : postB s0 = betas s0 :=
      (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [h0, ↓reduceIte])
    set p0 : ℝ := 1 - lockedAlpha (betas s0) (halfAngleSet n r) ^ 2
    have hα0 : stepAlpha n r φ (betas s0) ^ 2 = 1 - p0 :=
      (by dsimp only [stepAlpha, p0]; simp only [h0, ↓reduceIte]; ring); obtain ⟨hp0_lo, hp0_hi⟩ :=
      hlock_bds (betas s0) h0_ge (hbetas s0).2; rw [Nat.cast_ofNat] at hp0_hi
    by_cases h1 : betas s1 < φ
    · have hα1 : stepAlpha n r φ (betas s1) ^ 2 = 1 :=
        (by dsimp only [stepAlpha]; rw [ite_eq_left h1, one_pow])
      have hs1_post : remStepsSlot n r φ (postB s1) = remStepsSlot n r φ (betas s1) - 1 :=
        (by dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1, ite_eq_left h1])
      have hpb1 : postB s1 = betas s1 + 2 * halfAngleSet n r :=
        (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; rw [ite_eq_left h1]); rw [hα0, hα1,
        hs0_post, hs1_post, hs0_z, hpb1, Nat.cast_zero]
      have hstep := warm2_stageGe3_single_locked_step hB hn100 hr2 hr1024 ht_lo ht_hi hat_lo hd1000
        hcSB hdP1 hat_prev hw hwP hbins hp0_lo (hbetas s1).1 h1 hc_cap (hs_cap s1)
      dsimp only at hstep; exact le_of_eq_of_le (by ring) hstep
    · have h1_ge : φ ≤ betas s1 := not_lt.1 h1; have hs1_z : remStepsSlot n r φ (betas s1) = 0 :=
        (remStepsSlot_eq_zero_iff hr1 φ (betas s1)).2 h1_ge
      have hs1_post : remStepsSlot n r φ (postB s1) = 0 := by
        dsimp only [postB, nextBetasRamp]; rw [remStepsSlot_nextBetaSlot hr1]; simp only [h1,
          ↓reduceIte]
      have hpb1 : postB s1 = betas s1 :=
        (by dsimp only [postB, nextBetasRamp, nextBetaSlot]; simp only [h1, ↓reduceIte])
      set p1 : ℝ := 1 - lockedAlpha (betas s1) (halfAngleSet n r) ^ 2
      have hα1 : stepAlpha n r φ (betas s1) ^ 2 = 1 - p1 :=
        (by dsimp only [stepAlpha, p1]; simp only [h1, ↓reduceIte]; ring)
      obtain ⟨hp1_lo, hp1_hi⟩ := hlock_bds (betas s1) h1_ge (hbetas s1).2
      rw [Nat.cast_ofNat] at hp1_hi; rw [hα0, hα1, hs0_post, hs1_post, hs0_z, hs1_z, hpb0, hpb1,
        Nat.cast_zero, wmPotVal_diag hd1 hw SN 0, zero_add]; simp only [sub_sub_cancel]
      set p_min : ℝ := 4 * ((tn : ℝ) / 100000) * (99999999 / 100000000) * √(r : ℝ) / SN
      have ht_pos : (0 : ℝ) < tn := Nat.cast_pos.2 (by omega); have hr_pos : (0 : ℝ) < r :=
        Nat.cast_pos.2 hr1; have hp_min_pos : 0 < p_min := (by dsimp only [p_min]; positivity)
      obtain ⟨h1q0_pos, h2p_rho, hprod_le⟩ := two_locked_one_sub_q0_bounds hp_min_pos hp0_lo hp1_lo
        hp0_hi hp1_hi; have huh_lock := of_decide_eq_true huh_lock_d; have hcb_lock :=
        of_decide_eq_true hcb_lock_d
      have hhit1 : wmPotVal B dNatP (wFn (r - 1)) SN sReset (remStepsSlot n (r - 1) φp
        (fuseNextAngle n r (betas s1)) : ℝ) ≤ ((hLock : ℝ) / 1000000000000) * SN :=
        wmPotVal_hit_single_le hdP1 hwP hSN_pos huLock_le_c hpsi_lock huh_lock hc_cap (hsLock_le
        (betas s1) h1_ge (hbetas s1).2)
      have hhit2 : wmPotVal B dNatP (wFn (r - 1)) SN (remStepsSlot n (r - 1) φp (fuseNextAngle n r
        (betas s0)) : ℝ) sReset ≤ ((hLock : ℝ) / 1000000000000) * SN := by
        rw [wmPotVal_comm]
        exact wmPotVal_hit_single_le hdP1 hwP hSN_pos huLock_le_c hpsi_lock huh_lock hc_cap
          (hsLock_le (betas s0) h0_ge (hbetas s0).2)
      set extra : ℕ := if hLock ≤ hBoth then hBoth - hLock else 0
      have hboth_le_ex : hBoth ≤ hLock + extra := (by dsimp only [extra]; split_ifs <;> omega)
      have hhit3 : wmPotVal B dNatP (wFn (r - 1)) SN sReset sReset ≤ (((hLock : ℝ) + extra) /
        1000000000000) * SN := by
        refine (wmPotVal_hit_both_le hdP1 hwP hSN_pos hcb_lock hc_cap).trans ?_; have hex_r : (hBoth
          : ℝ) ≤ (hLock : ℝ) + extra := (by exact_mod_cast hboth_le_ex)
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hex_r (by norm_num)) hSN_pos.le
      have hp0_nn : 0 ≤ p0 := le_trans hp_min_pos.le hp0_lo
      have hp1_nn : 0 ≤ p1 := le_trans hp_min_pos.le hp1_lo
      have hp0_le1 : p0 ≤ 1 := hp0_hi.trans (by norm_num)
      have hp1_le1 : p1 ≤ 1 := hp1_hi.trans (by norm_num); set q0 : ℝ := (1 - p0) * (1 - p1)
      have hhit_sum : p0 * (1 - p1) * wmPotVal B dNatP (wFn (r - 1)) SN sReset (remStepsSlot n (r -
        1) φp (fuseNextAngle n r (betas s1)) : ℝ) + (1 - p0) * p1 * wmPotVal B dNatP (wFn (r - 1))
        SN (remStepsSlot n (r - 1) φp (fuseNextAngle n r (betas s0)) : ℝ) sReset + p0 * p1 *
        wmPotVal B dNatP (wFn (r - 1)) SN sReset sReset ≤ (1 - q0) * ((((hLock : ℝ) + (extra : ℝ) /
        200000000) / 1000000000000) * SN) := by
        have hm1 := mul_le_mul_of_nonneg_left hhit1 (mul_nonneg hp0_nn (sub_nonneg.2 hp1_le1))
        have hm2 := mul_le_mul_of_nonneg_left hhit2 (mul_nonneg (sub_nonneg.2 hp0_le1) hp1_nn)
        have hm3 := mul_le_mul_of_nonneg_left hhit3 (mul_nonneg hp0_nn hp1_nn); have hm_ex : (p0 *
          p1) * (((extra : ℝ) / 1000000000000) * SN) ≤ ((1 / 200000000) * (1 - q0)) * (((extra : ℝ)
          / 1000000000000) * SN) := mul_le_mul_of_nonneg_right hprod_le (by positivity)
        have hsum_w : p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1 = 1 - q0 := (by dsimp only [q0]; ring)
        linarith [hm1, hm2, hm3, hm_ex, show p0 * (1 - p1) * (((hLock : ℝ) / 1000000000000) * SN) +
              (1 - p0) * p1 * (((hLock : ℝ) / 1000000000000) * SN) +
              p0 * p1 * ((((hLock : ℝ) + extra) / 1000000000000) * SN) =
            (p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1) * (((hLock : ℝ) / 1000000000000) * SN) +
              (p0 * p1) * (((extra : ℝ) / 1000000000000) * SN) by ring,
          show (p0 * (1 - p1) + (1 - p0) * p1 + p0 * p1) * (((hLock : ℝ) / 1000000000000) * SN) =
            (1 - q0) * (((hLock : ℝ) / 1000000000000) * SN) by rw [hsum_w],
          show (1 - q0) * (((hLock : ℝ) / 1000000000000) * SN) +
              ((1 / 200000000) * (1 - q0)) * (((extra : ℝ) / 1000000000000) * SN) =
            (1 - q0) * ((((hLock : ℝ) + (extra : ℝ) / 200000000) / 1000000000000) * SN) by ring]
      have hclick := clickRow_sound (m := 2) (n := n) (r := r) (by omega) hr1 ht_lo hclick_chk
      have hclick' : 1 / (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ))))) ≤ ((stepNum : ℝ) /
        1000000000000) * SN := (by simpa [p_min, SN] using hclick)
      have h1_le : 1 ≤ (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) := by
        have hden_pos : 0 < 2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ)))) :=
          (by have : (0 : ℝ) < 1 - 2 * (1 / (100000000 * (2 : ℝ))) := (by norm_num); positivity)
        calc (1 : ℝ) = (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ))))) *
              (1 / (2 * p_min * (1 - 2 * (1 / (100000000 * (2 : ℝ)))))) := by
              field_simp [hden_pos.ne']
          _ ≤ (1 - q0) * (((stepNum : ℝ) / 1000000000000) * SN) :=
              mul_le_mul h2p_rho hclick' (by positivity) h1q0_pos.le
      have hstep_w0 := of_decide_eq_true hstep_w0_d
      have hcomb_r : 200000000 * (hLock : ℝ) + extra ≤ 200000000 * ((wFn r 0 - stepNum : ℕ) : ℝ) :=
        (by exact_mod_cast of_decide_eq_true hlock_comb_d); rw [Nat.cast_sub hstep_w0] at hcomb_r
      have hcomb_sn : (((hLock : ℝ) + (extra : ℝ) / 200000000) / 1000000000000) * SN ≤ (((wFn r 0 :
        ℝ) - stepNum) / 1000000000000) * SN := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) (by norm_num)) hSN_pos.le; have hm_comb :=
        mul_le_mul_of_nonneg_left hcomb_sn h1q0_pos.le; linarith [hhit_sum, h1_le, hm_comb, show (1
        - q0) * (((stepNum : ℝ) / 1000000000000) * SN) + (1 - q0) * ((((wFn r 0 : ℝ) - stepNum) /
        1000000000000) * SN) + q0 * (((wFn r 0 : ℝ) / 1000000000000) * SN) = ((wFn r 0 : ℝ) /
        1000000000000) * SN by ring]
private structure ValidWarmJP01M2Potential (v2m : ℕ → ℕ) (phiFn ubFn : ℕ → ℝ) (n k : ℕ)
    (Φ : ℕ → (Fin 2 → ℝ) → ℝ) : Prop where
  nonneg : ∀ r, 2 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas → 0 ≤ Φ r betas
  phi_lb : ∀ r, 3 ≤ r → r ≤ k → 2 * halfAngleSet n r ≤ phiFn r
  ub_lb : ∀ r, 2 ≤ r → r ≤ k →
    (if r = 2 then halfAngleSet n 2 else phiFn r + 2 * halfAngleSet n r) ≤ ubFn r
  ub_lt : ∀ r, 2 ≤ r → r ≤ k → ubFn r < π / 2
  ub_fuse : ∀ r, 3 ≤ r → r ≤ k → fuseNextAngle n r (ubFn r) ≤ ubFn (r - 1)
  base2_le : 2 ≤ k → ∀ betas, ValidStageBetas n 2 (ubFn 2) betas →
    warmJP01R2Cost2 v2m n betas ≤ Φ 2 betas
  step_le : ∀ r, 3 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas →
    1 + stepWeight n r (phiFn r) betas 0 * Φ r (nextBetasRamp n r (phiFn r) betas) +
      (∑ o ∈ Finset.univ.erase 0,
        stepWeight n r (phiFn r) betas o *
          expOnHitFuse Φ n r o (nextBetasRamp n r (phiFn r) betas)) ≤
      Φ r betas
private theorem warmJP01_top_le_vanilla_of_rcNum12 {kIdx baseNat topR rcNum12 n : ℕ} (hkIdx : kIdx <
  11) (hn : 200 ≤ n) (hrc_nat : (baseNat + topR) * 1000000000000 * sqrtMUpNat 1 ≤ rcNum12 *
  785398163397 * harmSumPow2 kIdx) : (((baseNat + topR : ℕ) : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) ≤
  (((rcNum12 : ℚ≥0) / 1000000000000 : ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ kIdx), 1
  / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ))) := by
  set m : ℕ := 2; set k : ℕ := 2 ^ kIdx; obtain ⟨hSN_ge, _⟩ := pow_two_200_bounds hn
  have hSN_pos : (0 : ℝ) < √(2 ^ n : ℝ) := lt_of_lt_of_le (by positivity) hSN_ge
  obtain ⟨hsm_pos_nat, hsm_sq⟩ := sqrtMUpNat_bounds (by omega : 1 < 11); have hsm_pos : (0 : ℝ) <
    sqrtMUpNat 1 := Nat.cast_pos.2 hsm_pos_nat; have hsqrtm_pos : (0 : ℝ) < √(m : ℝ) :=
    Real.sqrt_pos.2 (by positivity)
  have hsqrtm_le : √(m : ℝ) ≤ (sqrtMUpNat 1 : ℝ) / 1000000000000 := by
    refine sq_le_imp_le hsqrtm_pos.le (by positivity) ?_; rw [Real.sq_sqrt
      (by positivity : (0 : ℝ) ≤ m), div_pow, le_div_iff₀ (by norm_num)]
    have h2pow1 : (2 ^ 1 : ℕ) = m := rfl; rw [h2pow1] at hsm_sq
    have hcast : (m : ℝ) * 1000000000000 * 1000000000000 ≤ (sqrtMUpNat 1 : ℝ) * sqrtMUpNat 1 :=
      (by exact_mod_cast hsm_sq); linarith [hcast, show (m : ℝ) * (1000000000000 : ℝ) ^ 2 -
      (sqrtMUpNat 1 : ℝ) ^ 2 = (m : ℝ) * 1000000000000 * 1000000000000 - (sqrtMUpNat 1 : ℝ) *
      sqrtMUpNat 1 by ring]
  have hharm := harmSumPow2_le_sum hkIdx; have hpi : (785398163397 : ℝ) / 1000000000000 ≤ π / 4 :=
    (by linarith [Real.pi_gt_d20]); have hrc_cast : (((rcNum12 : ℚ≥0) / 1000000000000 : ℚ≥0) : ℝ) =
    (rcNum12 : ℝ) / 1000000000000 := (by push_cast; rfl); have hsn_cast : √((2 : ℝ) ^ n) = √(2 ^ n :
    ℝ) := (by norm_num); rw [hrc_cast, hsn_cast]; have hcell_r : ((baseNat + topR : ℕ) : ℝ) *
    1000000000000 * sqrtMUpNat 1 ≤ (rcNum12 : ℝ) * 785398163397 * harmSumPow2 kIdx :=
    (by exact_mod_cast hrc_nat)
  have hcoeff : ((baseNat + topR : ℕ) : ℝ) / 1000000000000 ≤ ((rcNum12 : ℝ) / 1000000000000) *
    ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat 1
    : ℝ) / 1000000000000) := by
    have hlhs : ((baseNat + topR : ℕ) : ℝ) / 1000000000000 = (((baseNat + topR : ℕ) : ℝ) *
      1000000000000 * sqrtMUpNat 1) / (1000000000000 * 1000000000000 * (sqrtMUpNat 1 : ℝ)) :=
      (by field_simp [hsm_pos.ne']); have hrhs : ((rcNum12 : ℝ) / 1000000000000) * ((785398163397 :
      ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat 1 : ℝ) /
      1000000000000) = ((rcNum12 : ℝ) * 785398163397 * harmSumPow2 kIdx) / (1000000000000 *
      1000000000000 * (sqrtMUpNat 1 : ℝ)) := (by field_simp [hsm_pos.ne']); rw [hlhs, hrhs]
    exact div_le_div_of_nonneg_right hcell_r (by positivity)
  have hm_prod : ((785398163397 : ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) ≤
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) := mul_le_mul hpi hharm (by positivity)
    (by linarith [Real.pi_pos])
  have hnum_le : ((rcNum12 : ℝ) / 1000000000000) * ((785398163397 : ℝ) / 1000000000000) *
    ((harmSumPow2 kIdx : ℝ) / 1000000000000) ≤ ((rcNum12 : ℝ) / 1000000000000) * ((π / 4) * (∑ r ∈
    Finset.Icc 1 k, 1 / √(r : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left hm_prod (by positivity : 0 ≤ (rcNum12 : ℝ) / 1000000000000)
    linarith [hm, show ((rcNum12 : ℝ) / 1000000000000) * (((785398163397 : ℝ) / 1000000000000) *
      ((harmSumPow2 kIdx : ℝ) / 1000000000000)) = ((rcNum12 : ℝ) / 1000000000000) * ((785398163397 :
      ℝ) / 1000000000000) * ((harmSumPow2 kIdx : ℝ) / 1000000000000) by ring]
  have hmono : ((rcNum12 : ℝ) / 1000000000000) * ((785398163397 : ℝ) / 1000000000000) *
    ((harmSumPow2 kIdx : ℝ) / 1000000000000) / ((sqrtMUpNat 1 : ℝ) / 1000000000000) ≤ ((rcNum12 : ℝ)
    / 1000000000000) * ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ))) / √(m : ℝ) :=
    (div_le_div_of_nonneg_right hnum_le (by positivity)).trans (div_le_div_of_nonneg_left
    (mul_nonneg (by positivity) (mul_nonneg (by linarith [Real.pi_pos]) (Finset.sum_nonneg fun _ _
    => by positivity))) hsqrtm_pos hsqrtm_le); rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n)
    m]
  calc (((baseNat + topR : ℕ) : ℝ) / 1000000000000) * √(2 ^ n : ℝ) ≤ (((rcNum12 : ℝ) /
        1000000000000) * ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ))) / √(m : ℝ)) * √(2 ^ n : ℝ)
        := mul_le_mul_of_nonneg_right (hcoeff.trans hmono) hSN_pos.le
    _ = ((rcNum12 : ℝ) / 1000000000000) *
          ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * (√(2 ^ n : ℝ) / √(m : ℝ))) := by
        ring
private theorem validWarmJP01M2Potential_of_checkWarmJP01CellCert {B ct1 ct2 cv2 : ℕ} {rows : ℕ →
  WarmJP01Row} {v2m : ℕ → ℕ} {stFn : ℕ → M2StageScalar} {wFn : ℕ → ℕ → ℕ} {binFn : ℕ → ℕ →
  M2BinCert} {kIdx topR rcNum12 n : ℕ} (htbl : checkWarmJP01R2Table ct1 ct2 cv2 rows v2m = true)
  (hcell : checkWarmJP01CellCert B cv2 v2m stFn wFn binFn kIdx topR rcNum12 = true) (hn : 200 ≤ n) :
  ValidWarmJP01M2Potential v2m (phiFnOfWmSt stFn) (fun _ => 5 / 4) n (2 ^ kIdx) (warmJP01Potential B
  v2m stFn wFn n) ∧ warmJP01Potential B v2m stFn wFn n (2 ^ kIdx) (fun _ => halfAngleSet n (2 ^
  kIdx)) ≤ (((rcNum12 : ℚ≥0) / 1000000000000 : ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^
  kIdx), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ))) := by
  have hn100 : 100 ≤ n := (by omega)
  have hv_anti : ∀ {i j : ℕ}, i ≤ j → j < 420 → v2m j ≤ v2m i := by
    obtain ⟨hanti, -⟩ := warmJP01Table_cold_and_warm_sound htbl hn; intro i j hij hj
    exact hanti i (lt_of_le_of_lt hij hj) j hj hij
  dsimp only [checkWarmJP01CellCert, checkWarmJP01CellHT] at hcell; set k : ℕ := 2 ^ kIdx
  set phiFn := phiFnOfWmSt stFn; set Φ := warmJP01Potential B v2m stFn wFn n
  rcases Bool.and_eq_true_iff.1 hcell with ⟨hht, hall_st⟩; rcases hsk : stFn k with ⟨tK, phiHiK,
    phiLoK, cSelfK, dNatK, stepNumK, cNatK, ldK⟩; rw [hsk] at hht; simp only [Bool.and_eq_true,
    and_assoc, Nat.ble_eq, Nat.blt_eq] at hht; rcases hht with ⟨hB, hkIdx2, hkIdx4, htop1, _,
    htop_sq, hrc_nat⟩
  have hk4 : 4 ≤ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ kIdx := Nat.pow_le_pow_right (by positivity) hkIdx2
  have hk1024 : k ≤ 1024 := by
    calc 2 ^ kIdx ≤ 2 ^ 4 := Nat.pow_le_pow_right (by positivity) hkIdx4
      _ ≤ 1024 := by norm_num
  have ht_bds : ∀ r, 3 ≤ r → r ≤ k → 500 ≤ (stFn r).tNum ∧ (stFn r).tNum ≤ 200000 :=
    fun r hr3 hrk => by
      have hp := warmJP01StageIdx_props hr3 (of_allRange hall_st (by omega : r - 3 < k - 2))
      exact ⟨hp.1, hp.2.1⟩
  have h54_lt : (5 / 4 : ℝ) < π / 2 := tan_five_div_four_le_five.2; refine ⟨?_, ?_⟩
  · refine
      { nonneg := fun r _ _ betas _ => by
          dsimp only [Φ, warmJP01Potential]; split_ifs
          · exact cswapWarmR1Cost1_nonneg n betas
          · exact warmJP01R2Cost2_nonneg v2m n betas
          · exact wmPotVal_nonneg (Real.sqrt_nonneg _) (by positivity) (by positivity)
        phi_lb := fun r hr3 hrk =>
          (phi_and_lockedAlpha_bounds_fuse_100 (m := 2) (by omega) (by omega) hn100
            (by omega) (hrk.trans hk1024) (ht_bds r hr3 hrk).1 (ht_bds r hr3 hrk).2).1
        ub_lb := fun r hr2 hrk => by
          split_ifs with hr_eq2
          · rcases halfAngleSet_bounds_100 hn100 (by omega : 1 ≤ 2) (by omega : 2 ≤ 1024) with ⟨_,
              _, hθ2_13, -⟩; linarith [hθ2_13]
          · have hr3 : 3 ≤ r := (by omega); exact (phi_and_lockedAlpha_bounds_fuse_100 (m := 2)
              (by omega) (by omega) hn100 (by omega) (hrk.trans hk1024) (ht_bds r hr3 hrk).1 (ht_bds
              r hr3 hrk).2).2.1
        ub_lt := fun _ _ _ => h54_lt
        ub_fuse := fun r hr3 hrk => by
          rcases halfAngleSet_bounds_100 hn100 (by omega : 1 ≤ r) (hrk.trans hk1024) with ⟨_, _,
            hθ_13, -⟩; exact fuseNextAngle_le_self (by omega) (two_mul_le_pow_100 hn100 (hrk.trans
            hk1024)) (by linarith [hθ_13]) h54_lt.le
        base2_le := fun _ betas _ => by dsimp only [Φ, warmJP01Potential]; simp
        step_le := fun r hr3 hrk betas hbetas => ?_ }
    by_cases hr4 : 4 ≤ r
    · exact warmJP01_stageGe4_step hB hn hr4 (hrk.trans hk1024) (of_allRange hall_st
        (by omega : r - 3 < k - 2)) (of_allRange hall_st (by omega : r - 4 < k - 2)) betas hbetas
    · have hr_eq3 : r = 3 := (by omega); subst hr_eq3
      exact warmJP01_stage3_step hB hn hv_anti (of_allRange hall_st (by omega : 0 < k - 2)) betas
        hbetas
  · have hprops_k := warmJP01StageIdx_props (by omega : 3 ≤ k) (of_allRange hall_st
      (by omega : k - 3 < k - 2)); rw [hsk] at hprops_k; dsimp only at hprops_k
    rcases hprops_k with ⟨htK_lo, htK_hi, hatK, hdK1000, hslK⟩; have hdK1 : 1 ≤ dNatK := (by omega)
    have hwK := knotSlope_of_allRange hslK; have hφk : phiFnOfWmSt stFn k = Real.arctan ((tK : ℝ) /
      100000) := (by dsimp only [phiFnOfWmSt]; rw [hsk])
    have hrem_k := remStepsSlot_halfAngleSet_le_of_atan200Hi_sq hn100 (by omega) hk1024 htK_lo
      htK_hi hatK htop1 htop_sq
    have hΦk : Φ k (fun _ : Fin 2 => halfAngleSet n k) ≤ (((wFn k 0 + topR : ℕ) : ℝ) /
      1000000000000) * √((2 : ℝ) ^ n) := by
      dsimp only [Φ, warmJP01Potential]; rw [ite_eq_right (by omega : ¬ k ≤ 1), ite_eq_right
        (by omega : k ≠ 2)]; dsimp only [wmStagePot]; have hdK_eq : (stFn k).dNat = dNatK :=
        (by rw [hsk]); rw [hdK_eq, hφk, wmPotVal_diag hdK1 hwK √((2 : ℝ) ^ n) _, Nat.cast_add]
      linarith only [hrem_k, show ((topR : ℝ) / 1000000000000) * √((2 : ℝ) ^ n) + ((wFn k 0 : ℝ) /
        1000000000000) * √((2 : ℝ) ^ n) = (((wFn k 0 : ℝ) + topR) / 1000000000000) * √((2 : ℝ) ^ n)
        by ring]
    exact hΦk.trans (warmJP01_top_le_vanilla_of_rcNum12 (by omega) hn hrc_nat)
/-! ### Symmetric Off-Diagonal Pair Lift, `1`-Query Readout, and `WarmJP01` QHL Transitions -/
private noncomputable def symPairInj (n : ℕ) :
    Matrix (Fin (2 ^ (2 * n))) (DickeSol.P01Subset (2 ^ n) 2) ℝ :=
  fun u E =>
    if addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1 ∧
        ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) = E.1 then
      1 / √2
    else
      0
private theorem symPairInj_transpose_mul_self (n : ℕ) : (symPairInj n)ᵀ * symPairInj n = 1 := by
  ext E F; simp only [Matrix.mul_apply, Matrix.transpose_apply, symPairInj, Matrix.one_apply]
  by_cases hEF : E = F
  · subst hEF; simp only [↓reduceIte]; obtain ⟨a, b, hab, hE_eq⟩ := Finset.card_eq_two.1 E.2
    let uab := (addrEquiv n 2).symm ![a, b]; let uba := (addrEquiv n 2).symm ![b, a]
    have hu_ne : uab ≠ uba := by
      intro h; have h0 := congrFun (congrArg (addrEquiv n 2) h) s0; simp only [uab, uba,
        Equiv.apply_symm_apply, s0] at h0; exact hab h0
    have hiff (u : Fin (2 ^ (2 * n))) :
        (addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1 ∧
          ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) = E.1) ↔
          (u = uab ∨ u = uba) := by
      rw [hE_eq]; constructor
      · rintro ⟨hne, hset⟩; have hx0 : addrEquiv n 2 u s0 ∈ ({a, b} : Finset (Fin (2 ^ n))) :=
          (by rw [← hset]; simp); have hx1 : addrEquiv n 2 u s1 ∈ ({a, b} : Finset (Fin (2 ^ n))) :=
          (by rw [← hset]; simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hx0 hx1
        rcases hx0 with hx0a | hx0b <;> rcases hx1 with hx1a | hx1b
        · exact (hne (hx0a.trans hx1a.symm)).elim
        · left; apply (addrEquiv n 2).injective; funext i; fin_cases i
          · simpa [uab, s0] using hx0a
          · simpa [uab, s1] using hx1b
        · right; apply (addrEquiv n 2).injective; funext i; fin_cases i
          · simpa [uba, s0] using hx0b
          · simpa [uba, s1] using hx1a
        · exact (hne (hx0b.trans hx1b.symm)).elim
      · rintro (rfl | rfl)
        · simp [uab, s0, s1, hab]
        · refine ⟨by simpa [uba, s0, s1] using hab.symm, ?_⟩; simp [uba, s0, s1, Finset.pair_comm]
    have hterm (u : Fin (2 ^ (2 * n))) :
        (if addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1 ∧
            ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) = E.1 then
          1 / √2 else (0 : ℝ)) *
        (if addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1 ∧
            ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) = E.1 then
          1 / √2 else (0 : ℝ)) =
        if u ∈ ({uab, uba} : Finset (Fin (2 ^ (2 * n)))) then (1 / 2 : ℝ) else 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, ← hiff]
      by_cases hc : addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1 ∧
          ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) = E.1
      · rw [ite_eq_left hc, ite_eq_left hc]; rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt
          (by norm_num)]
      · rw [ite_eq_right hc, zero_mul, ite_eq_right hc]
    simp_rw [hterm]; rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hu_ne]; norm_num
  · simp only [hEF, ↓reduceIte]; refine Finset.sum_eq_zero fun u _ => ?_
    by_cases hE : addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1 ∧
        ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) = E.1
    · have hF : ¬ (addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1 ∧
          ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) = F.1) :=
        (by rintro ⟨_, hF1⟩; exact hEF (Subtype.ext (hE.2.symm.trans hF1))); rw [ite_eq_right hF,
        mul_zero]
    · rw [ite_eq_right hE, zero_mul]
private noncomputable def liftSymPairReal (n : ℕ)
    (v : DickeSol.P01Subset (2 ^ n) 2 → ℝ) : Fin (2 ^ (2 * n)) → ℝ := symPairInj n *ᵥ v
private noncomputable def liftSymPairVec (n : ℕ)
    (v : DickeSol.P01Subset (2 ^ n) 2 → ℝ) : Fin (2 ^ (2 * n)) → ℂ :=
  fun u => ((liftSymPairReal n v u : ℝ) : ℂ)
private theorem liftSymPairReal_diag_zero {n : ℕ} (v : DickeSol.P01Subset (2 ^ n) 2 → ℝ) {u : Fin (2
  ^ (2 * n))} (hdiag : addrEquiv n 2 u s0 = addrEquiv n 2 u s1) : liftSymPairReal n v u = 0 := by
  dsimp only [liftSymPairReal, Matrix.mulVec, dotProduct, symPairInj]
  refine Finset.sum_eq_zero fun E _ => ?_
  simp [hdiag]
private theorem liftSymPairReal_apply_offDiag {n : ℕ} (v : DickeSol.P01Subset (2 ^ n) 2 → ℝ) {u :
  Fin (2 ^ (2 * n))} (hne : addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1) : liftSymPairReal n v u = (1 /
  √2) * v ⟨{addrEquiv n 2 u s0, addrEquiv n 2 u s1}, Finset.card_pair hne⟩ := by
  let Eu : DickeSol.P01Subset (2 ^ n) 2 :=
    ⟨{addrEquiv n 2 u s0, addrEquiv n 2 u s1}, Finset.card_pair hne⟩
  dsimp only [liftSymPairReal, Matrix.mulVec, dotProduct, symPairInj]; rw [Finset.sum_eq_single Eu]
  · simp [Eu, hne]
  · intro F _ hF
    have hset : ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) ≠ F.1 :=
      fun h => hF (Subtype.ext h.symm)
    simp [hset]
  · intro habs; exact (habs (Finset.mem_univ Eu)).elim
private theorem dotProduct_liftSymPairReal (n : ℕ) (v w : DickeSol.P01Subset (2 ^ n) 2 → ℝ) :
  liftSymPairReal n v ⬝ᵥ liftSymPairReal n w = v ⬝ᵥ w := by
  dsimp only [liftSymPairReal]; rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    symPairInj_transpose_mul_self, Matrix.vecMul_one]
private theorem dotProduct_liftSymPairVec (n : ℕ) (v : DickeSol.P01Subset (2 ^ n) 2 → ℝ) : star
  (liftSymPairVec n v) ⬝ᵥ liftSymPairVec n v = ((v ⬝ᵥ v : ℝ) : ℂ) := by
  have hr : ((liftSymPairReal n v ⬝ᵥ liftSymPairReal n v : ℝ) : ℂ) = ((v ⬝ᵥ v : ℝ) : ℂ) := congrArg
    Complex.ofReal (dotProduct_liftSymPairReal n v v); rw [← hr]; simp [dotProduct, liftSymPairVec,
    Complex.ofReal_sum, Complex.ofReal_mul]
private noncomputable def liftSymPairRealMat (n : ℕ) (D : Matrix (DickeSol.P01Subset (2 ^ n) 2)
    (DickeSol.P01Subset (2 ^ n) 2) ℝ) : Matrix (Fin (2 ^ (2 * n))) (Fin (2 ^ (2 * n))) ℝ :=
  1 + symPairInj n * (D - 1) * (symPairInj n)ᵀ
private noncomputable def liftSymPairOrthogonal (n : ℕ) (D : Matrix (DickeSol.P01Subset (2 ^ n) 2)
    (DickeSol.P01Subset (2 ^ n) 2) ℝ) (hD : Dᵀ * D = 1) : Unitary (2 ^ (2 * n)) :=
  ⟨(liftSymPairRealMat n D).map Complex.ofRealHom, by
    let J := symPairInj n; let A := D - 1; let L := liftSymPairRealMat n D
    have hJtJ : Jᵀ * J = 1 := symPairInj_transpose_mul_self n
    have hAA : Aᵀ + A + Aᵀ * A = 0 := by
      dsimp only [A]
      simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.one_mul, Matrix.mul_one, hD]; abel
    have hLt : Lᵀ = 1 + J * Aᵀ * Jᵀ := by
      dsimp only [L, liftSymPairRealMat, J, A]
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    have hmid : (J * Aᵀ * Jᵀ) * (J * A * Jᵀ) = J * (Aᵀ * A) * Jᵀ := by
      calc (J * Aᵀ * Jᵀ) * (J * A * Jᵀ)
          = (J * Aᵀ) * ((Jᵀ * J) * (A * Jᵀ)) := by simp only [Matrix.mul_assoc]
        _ = J * (Aᵀ * A) * Jᵀ := by rw [hJtJ, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    have hLtL : Lᵀ * L = 1 := by
      change Lᵀ * (1 + J * A * Jᵀ) = 1
      rw [hLt, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hmid]
      have hsum : J * A * Jᵀ + (J * Aᵀ * Jᵀ + J * (Aᵀ * A) * Jᵀ) = J * (Aᵀ + A + Aᵀ * A) * Jᵀ := by
        simp only [Matrix.mul_add, Matrix.add_mul]; abel
      rw [add_assoc (1 : Matrix _ _ ℝ), hsum, hAA, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    rw [Matrix.mem_unitaryGroup_iff']
    have hstar : star (L.map Complex.ofRealHom) = Lᵀ.map Complex.ofRealHom := (by ext i j; simp)
    rw [hstar, ← Matrix.map_mul, hLtL]; ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]⟩
private theorem isRealMatrix_liftSymPairOrthogonal (n : ℕ) (D : Matrix (DickeSol.P01Subset (2 ^ n)
  2) (DickeSol.P01Subset (2 ^ n) 2) ℝ) (hD : Dᵀ * D = 1) : IsRealMatrix (liftSymPairOrthogonal n D
  hD).1 := by intro i j; simp [liftSymPairOrthogonal]
private theorem liftSymPairOrthogonal_mulVec (n : ℕ) (D : Matrix (DickeSol.P01Subset (2 ^ n) 2)
  (DickeSol.P01Subset (2 ^ n) 2) ℝ) (hD : Dᵀ * D = 1) (v : DickeSol.P01Subset (2 ^ n) 2 → ℝ) :
  (liftSymPairOrthogonal n D hD).1 *ᵥ liftSymPairVec n v = liftSymPairVec n (D *ᵥ v) := by
  let J := symPairInj n; let L := liftSymPairRealMat n D
  have hLJ : L * J = J * D := by
    dsimp only [L, liftSymPairRealMat, J]; rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (J *
      (D - 1)) Jᵀ J, symPairInj_transpose_mul_self, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one,
      add_sub_cancel]
  have hreal : L *ᵥ (J *ᵥ v) = J *ᵥ (D *ᵥ v) :=
    (by rw [Matrix.mulVec_mulVec, hLJ, ← Matrix.mulVec_mulVec]); funext u; have hmap : ((L.map
    Complex.ofRealHom) *ᵥ (fun y => Complex.ofRealHom ((J *ᵥ v) y))) u = Complex.ofRealHom ((L *ᵥ (J
    *ᵥ v)) u) := (RingHom.map_mulVec Complex.ofRealHom L (J *ᵥ v) u).symm
  exact hmap.trans (congrArg Complex.ofRealHom (congrFun hreal u))
private theorem setOracleMatrix_mulVec_liftSymPairVec {n : ℕ} (A : Finset (Fin (2 ^ n))) (v :
  DickeSol.P01Subset (2 ^ n) 2 → ℝ) : setOracleMatrix (oddSet n 2 A) *ᵥ liftSymPairVec n v =
  liftSymPairVec n (fun E => (-1 : ℝ) ^ (E.1 ∩ A).card * v E) := by
  funext u; rw [setOracleMatrix, Matrix.mulVec_diagonal]; by_cases hdiag : addrEquiv n 2 u s0 =
    addrEquiv n 2 u s1
  · dsimp only [liftSymPairVec]; rw [liftSymPairReal_diag_zero v hdiag, liftSymPairReal_diag_zero _
      hdiag]; simp
  · dsimp only [liftSymPairVec]; rw [liftSymPairReal_apply_offDiag v hdiag,
      liftSymPairReal_apply_offDiag _ hdiag]; dsimp only; set x0 := addrEquiv n 2 u s0; set x1 :=
      addrEquiv n 2 u s1; have hmem_odd : u ∈ oddSet n 2 A ↔ ((if x0 ∈ A then (-1 : ℤ) else 1) * (if
      x1 ∈ A then (-1 : ℤ) else 1) = -1) := (by simp [oddSet, x0, x1]); by_cases hx0 : x0 ∈ A <;>
      by_cases hx1 : x1 ∈ A
    · have hodd : u ∉ oddSet n 2 A := (by simp [hmem_odd, hx0, hx1])
      have hcard : (({x0, x1} : Finset (Fin (2 ^ n))) ∩ A).card = 2 := by
        have hsub : ({x0, x1} : Finset (Fin (2 ^ n))) ⊆ A := by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> assumption
        rw [Finset.inter_eq_left.2 hsub, Finset.card_pair hdiag]
      rw [ite_eq_right hodd, hcard]; push_cast; ring
    · have hodd : u ∈ oddSet n 2 A := (by simp [hmem_odd, hx0, hx1])
      have hcard : (({x0, x1} : Finset (Fin (2 ^ n))) ∩ A).card = 1 := by
        have hi : ({x0, x1} : Finset (Fin (2 ^ n))) ∩ A = {x0} := by
          ext y; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]; constructor
          · rintro ⟨rfl | rfl, hyA⟩
            · rfl
            · exact (hx1 hyA).elim
          · rintro rfl; exact ⟨Or.inl rfl, hx0⟩
        rw [hi, Finset.card_singleton]
      rw [ite_eq_left hodd, hcard]; push_cast; ring
    · have hodd : u ∈ oddSet n 2 A := (by simp [hmem_odd, hx0, hx1])
      have hcard : (({x0, x1} : Finset (Fin (2 ^ n))) ∩ A).card = 1 := by
        have hi : ({x0, x1} : Finset (Fin (2 ^ n))) ∩ A = {x1} := by
          ext y; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]; constructor
          · rintro ⟨rfl | rfl, hyA⟩
            · exact (hx0 hyA).elim
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl, hx1⟩
        rw [hi, Finset.card_singleton]
      rw [ite_eq_left hodd, hcard]; push_cast; ring
    · have hodd : u ∉ oddSet n 2 A := (by simp [hmem_odd, hx0, hx1])
      have hcard : (({x0, x1} : Finset (Fin (2 ^ n))) ∩ A).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro y hy
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hy; rcases hy with
          ⟨rfl | rfl, hyA⟩
        · exact hx0 hyA
        · exact hx1 hyA
      rw [ite_eq_right hodd, hcard]; push_cast; ring
private noncomputable def jp01WalkStepCircuit {Var : Type} (n k : ℕ) (Udiff : Unitary (2 ^ (2 * n)))
    : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var (findAllQubits n 2 k) ((n + 1) *
    2) :=
  rawPrePostOracleCircuit n 2 k (flagConj n 2)
    ((localAddrReg n 2).embedUnitary Udiff * flagConj n 2)
private noncomputable def jp01WalkRec {Var : Type} (n k : ℕ)
    (Udiff : Unitary (2 ^ (2 * n))) (T : Finset (Fin (2 ^ n))) :
    ℕ → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
      (findAllQubits n 2 k) ((n + 1) * 2)
  | 0 => .skip
  | K + 1 =>
      .seq (deflateCirc n 2 T (jp01WalkStepCircuit n k Udiff))
        (jp01WalkRec n k Udiff T K)
private theorem jp01WalkRec_pureStateAt {Var : Type} [DecidableEq Var] {n k : ℕ} (hn : 200 ≤ n) {S T
  : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hA2 : (S \ T).card = 2) (D : Matrix (DickeSol.P01Subset (2
  ^ n) 2) (DickeSol.P01Subset (2 ^ n) 2) ℝ) (hD : Dᵀ * D = 1) (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hDF :
  ∀ x : Fin 3 → ℝ, D *ᵥ DickeSol.orbEmbed3 (2 ^ n) 2 (S \ T) (DickeSol.zOrb3 x) = DickeSol.orbEmbed3
  (2 ^ n) 2 (S \ T) (F x)) (hF_norm : ∀ x : Fin 3 → ℝ, DickeSol.dot3 (F x) (F x) = DickeSol.dot3 x
  x) : ∀ (K : ℕ) (x : Fin 3 → ℝ) (_ : DickeSol.dot3 x x = 1) {Δ : CQState (Store Var) (2 ^
    findAllQubits n 2
  k)}, PureStateAt ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState (liftSymPairVec n
  (DickeSol.orbEmbed3 (2 ^ n) 2 (S \ T) x)) (Pi.single 0 1)) (Pi.single ((oracleReg n 2
  k).basisSplitEquiv 0).2 1)) Δ →
      let prog := (jp01WalkRec (Var := Var) n k (liftSymPairOrthogonal n D hD) T K).compile
        QProg.qAssign (parallelMarkingOracle 2 S)
      PureStateAt ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState (liftSymPairVec n
        (DickeSol.orbEmbed3 (2 ^ n) 2 (S \ T) ((F^[K]) x))) (Pi.single 0 1)) (Pi.single ((oracleReg
        n 2 k).basisSplitEquiv 0).2 1)) ((interp prog).toStateFun Δ) ∧ ((interp prog).toStateFun
        Δ).trace = Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S))
        prog Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (K : ℝ) := by
  set A := S \ T; let Udiff := liftSymPairOrthogonal n D hD
  let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ :=
    Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 1
  have hN16 : 16 ≤ 2 ^ n := by
    calc 16 ≤ 2 ^ 200 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by positivity) hn
  have hmrN : 2 + A.card < 2 ^ n := (by omega)
  have hmin2 : min 2 A.card ≤ 2 := Nat.min_le_left 2 A.card; have hpre_real : IsRealMatrix (flagConj
    n 2).1 := isRealMatrix_flagConj n 2; have hpost_real : IsRealMatrix (((localAddrReg n
    2).embedUnitary Udiff * flagConj n 2)).1 := isRealMatrix_mul (isRealMatrix_embedMatrix _
    (isRealMatrix_liftSymPairOrthogonal n D hD)) hpre_real; intro K
  induction K with
  | zero => intro x _ Δ hΔ; simp [jp01WalkRec, hΔ]
  | succ K ih =>
      intro x hx Δ hΔ; dsimp only [jp01WalkRec]; rw [OracleDynamicCircuit.compile_seq, interp_qSeq,
        QMonad.Q.toStateFun_bind, expectedCost_qSeq, interp_deflateCirc n 2 hTS (jp01WalkStepCircuit
        n k Udiff), congrFun (expectedCost_deflateCirc n 2 hTS (c := jp01WalkStepCircuit n k Udiff)
        (zeroStepCost_rawPrePostOracleCircuit hpre_real hpost_real)) Δ]
      have hcost1 : expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 A))
        ((jp01WalkStepCircuit (Var := Var) n k Udiff).compile QProg.qAssign (parallelMarkingOracle 2
        A)) Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
        simpa [jp01WalkStepCircuit, ENNReal.ofReal_one] using costBound_rawPrePostOracleCircuit (Var
          := Var) (k := k) hpre_real hpost_real A Δ
      set Δ1 := (interp ((jp01WalkStepCircuit (Var := Var) n k Udiff).compile QProg.qAssign
        (parallelMarkingOracle 2 A))).toStateFun Δ
      let Ustep := ((localAddrReg n 2).embedUnitary Udiff * flagConj n 2) *
        parallelMarkingOracle 2 A * flagConj n 2
      have hΔ1_eq : Δ1 = CQState.qAssign ((oracleReg n 2 k).embedUnitary Ustep) Δ := by
        dsimp only [Δ1, jp01WalkStepCircuit]; rw [interp_rawPrePostOracleCircuit, interp_qAssign]
        rfl
      have horb_dot : DickeSol.orbEmbed3 (2 ^ n) 2 A x ⬝ᵥ DickeSol.orbEmbed3 (2 ^ n) 2 A x = 1 := by
        change ∑ E, DickeSol.orbEmbed3 (2 ^ n) 2 A x E * DickeSol.orbEmbed3 (2 ^ n) 2 A x E = 1
        rw [DickeSol.dot_orbEmbed3 (by omega) (by omega) hmin2 hmrN, hx]
      have hψ_in : star ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState
        (liftSymPairVec n (DickeSol.orbEmbed3 (2 ^ n) 2 A x)) (Pi.single 0 1)) env0) ⬝ᵥ (oracleReg n
        2 k).tensorState ((localAddrReg n 2).tensorState (liftSymPairVec n (DickeSol.orbEmbed3 (2 ^
        n) 2 A x)) (Pi.single 0 1)) env0 = 1 := by
        rw [dotProduct_tensorState, dotProduct_tensorState, dotProduct_liftSymPairVec, horb_dot,
          Complex.ofReal_one, dotProduct_env_single, dotProduct_env_single, mul_one, mul_one]
      obtain ⟨hP1, htr1⟩ := pureStateAt_qAssign ((oracleReg n 2 k).embedUnitary Ustep) hψ_in hΔ
      rw [← hΔ1_eq] at hP1 htr1
      have hvec1 : (((oracleReg n 2 k).embedUnitary Ustep).1 *ᵥ (oracleReg n 2 k).tensorState
        ((localAddrReg n 2).tensorState (liftSymPairVec n (DickeSol.orbEmbed3 (2 ^ n) 2 A x))
        (Pi.single 0 1)) env0) = (oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState
        (liftSymPairVec n (DickeSol.orbEmbed3 (2 ^ n) 2 A (F x))) (Pi.single 0 1)) env0 := by
        rw [QRegister.embedUnitary_val, (oracleReg n 2 k).embedMatrix_mulVec_tensorState]; congr 1
        have hU_mat : Ustep.1 = ((localAddrReg n 2).embedUnitary Udiff).1 * sDiagM n 2 A := by
          dsimp only [Ustep]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]; have hf :=
            flagConj_mul_parallelMarkingOracle_mul_flagConj n 2 A
          simp only [Matrix.mul_assoc] at hf; rw [hf]
        rw [hU_mat, ← Matrix.mulVec_mulVec, sDiagM_mulVec_env_zero,
          setOracleMatrix_mulVec_liftSymPairVec, DickeSol.symZ_orbEmbed3 hmin2 x,
          QRegister.embedUnitary_val, (localAddrReg n 2).embedMatrix_mulVec_tensorState,
          liftSymPairOrthogonal_mulVec, hDF x]
      rw [hvec1] at hP1; have hFx_norm : DickeSol.dot3 (F x) (F x) = 1 := (hF_norm x).trans hx
      obtain ⟨hPK, htrK, hcostK⟩ := ih (F x) hFx_norm hP1
      rw [← Function.iterate_succ_apply F K x] at hPK
      have hmass1 : (Δ1.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) := congrArg ENNReal.ofNNReal htr1
      rw [hmass1] at hcostK
      refine ⟨hPK, htrK.trans htr1, ?_⟩
      calc _ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 + (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (K : ℝ) :=
            add_le_add hcost1 hcostK
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (1 + (K : ℝ)) := by
            rw [← mul_add, ← ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg K)]
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((K + 1 : ℕ) : ℝ) := by push_cast; ring_nf
private theorem dot3_rot3Pos {u x : Fin 3 → ℝ} (hu : DickeSol.dot3 u u = 1) : DickeSol.dot3
  (DickeSol.rot3Pos u x) (DickeSol.rot3Pos u x) = DickeSol.dot3 x x := by
  dsimp only [DickeSol.rot3Pos, DickeSol.refl3, DickeSol.zOrb3, DickeSol.dot3, DickeSol.vec3,
    Fin.isValue] at hu ⊢
  calc (x 0 - 2 * (u 0 * x 0 + u 1 * -x 1 + u 2 * x 2) * u 0) *
        (x 0 - 2 * (u 0 * x 0 + u 1 * -x 1 + u 2 * x 2) * u 0) +
        (-x 1 - 2 * (u 0 * x 0 + u 1 * -x 1 + u 2 * x 2) * u 1) *
        (-x 1 - 2 * (u 0 * x 0 + u 1 * -x 1 + u 2 * x 2) * u 1) +
        (x 2 - 2 * (u 0 * x 0 + u 1 * -x 1 + u 2 * x 2) * u 2) *
        (x 2 - 2 * (u 0 * x 0 + u 1 * -x 1 + u 2 * x 2) * u 2)
      = (x 0 * x 0 + x 1 * x 1 + x 2 * x 2) + 4 * (u 0 * x 0 + u 1 * -x 1 + u 2 * x 2) ^ 2 *
            ((u 0 * u 0 + u 1 * u 1 + u 2 * u 2) - 1) := by ring
    _ = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 := by rw [hu]; ring
private theorem dot3_rot3Neg {u x : Fin 3 → ℝ} (hu : DickeSol.dot3 u u = 1) : DickeSol.dot3
  (DickeSol.rot3Neg u x) (DickeSol.rot3Neg u x) = DickeSol.dot3 x x := by
  have hp := dot3_rot3Pos (x := x) hu; dsimp only [DickeSol.rot3Neg, DickeSol.rot3Pos,
    DickeSol.dot3] at hp ⊢; simp only [Pi.neg_apply, neg_mul_neg]; exact hp
private theorem r1SymMat_orth {n : ℕ} (hn : 200 ≤ n) : (DickeSol.r1SymMat (2 ^ n) 2)ᵀ *
  DickeSol.r1SymMat (2 ^ n) 2 = 1 := by
  have h4 : 2 * 2 < 2 ^ n := by
    have : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right (by positivity)
      hn); omega
  rw [DickeSol.r1SymMat_transpose]; exact DickeSol.r1SymMat_mul_self (by omega) h4
private theorem r01SymMat_orth {n : ℕ} (hn : 200 ≤ n) : (DickeSol.r01SymMat (2 ^ n) 2)ᵀ *
  DickeSol.r01SymMat (2 ^ n) 2 = 1 := by
  have h4 : 2 * 2 < 2 ^ n := by
    have : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right (by positivity)
      hn); omega
  rw [DickeSol.r01SymMat_transpose]; exact DickeSol.r01SymMat_mul_self (by omega) h4
private noncomputable def zeroHitCleanR1Circuit {Var : Type} (res : Var) (n k : ℕ) (T : Finset (Fin
    (2 ^ n))) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var (findAllQubits n 2 k)
    ((n + 1) * 2) :=
  .seq (prepSlotsListCircuit res n 2 k (fun _ => true) (List.finRange 2))
    (cswapWarmR1Circuit res n k T (fun _ => halfAngleSet n 1))
private theorem zeroHitCleanR1_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn :
  200 ≤ n) (hk1024 : k ≤ 1024) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA1
  : (S \ T).card = 1) {Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k)} (hΔ : PureStateAt
    (Pi.single 0 1)
  Δ) :
    let prog := (zeroHitCleanR1Circuit res n k T).compile QProg.qAssign (parallelMarkingOracle 2 S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (((cswapZeroHitNat : ℝ) / 1000000000000) *
      √((2 : ℝ) ^ n)) := by
  intro prog; have hn100 : 100 ≤ n := (by omega); let oracle := parallelMarkingOracle 2 S
  have horacle := isRealMatrix_parallelMarkingOracle (m := 2) S
  have hN16 : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right
    (by positivity) hn); have hA_pos : 1 ≤ (S \ T).card := (by omega)
  have hA_lt : (S \ T).card < 2 ^ n := (by omega); have hP0 : PureStateAt (prodSlotState n 2 k fun _
    => Pi.single 0 1) Δ := (by rwa [prodSlotState_single_zero])
  obtain ⟨hPprep, htr_prep⟩ := prepSlotsListCircuit_pureStateAt oracle res (fun _ => true)
    (List.finRange 2) (List.nodup_finRange 2) hA_pos hA_lt (fun _ => dotProduct_single_one 0) hP0
  set Ξ_prep := (interp ((prepSlotsListCircuit res n 2 k (fun _ => true) (List.finRange 2)).compile
    QProg.qAssign oracle)).toStateFun Δ
  have hPprep' : PureStateAt (prodSlotState n 2 k fun _ => slotPairVec (planeVec (S \ T)
    (halfAngleSet n 1)) (Pi.single 0 1)) Ξ_prep := by
    convert hPprep using 2
    funext _; simp [List.mem_finRange, hA1]
  obtain ⟨_, _, hθ1_13, -⟩ := halfAngleSet_bounds_100 hn100 (by omega : 1 ≤ 1) (by omega : 1 ≤ 1024)
  have hθ1_nn : 0 ≤ halfAngleSet n 1 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hθ1_45 : halfAngleSet n 1 ≤ 4 / 5 := (by linarith [hθ1_13]); have hθ1_lt : halfAngleSet n 1 <
    π / 2 := (by linarith [Real.pi_gt_three, hθ1_13])
  obtain ⟨hexp, hcost⟩ := cswapWarmR1_transition res hn100 hk1024 hScard hTS hA1 (fun _ => hθ1_nn)
    (fun _ => hθ1_lt) hPprep'; have hg : cswapWarmGuard n (fun _ : Fin 2 => halfAngleSet n 1) :=
    Or.inl ⟨rfl, le_rfl, hθ1_45⟩
  have hub : cswapWarmR1Cost1 n (fun _ : Fin 2 => halfAngleSet n 1) ≤ ((cswapZeroHitNat : ℝ) /
    1000000000000) * √((2 : ℝ) ^ n) := by
    dsimp only [cswapWarmR1Cost1]; rw [ite_eq_left hg, max_self]
    exact cswapR1CostUpper_le_of_zeroHit hθ1_nn hθ1_45 le_rfl
  have hmass_prep : (Ξ_prep.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) := congrArg ENNReal.ofNNReal htr_prep
  dsimp only [prog, zeroHitCleanR1Circuit]; rw [OracleDynamicCircuit.compile_seq, interp_qSeq,
    QMonad.Q.toStateFun_bind, expectedCost_qSeq, expectedCost_prepSlotsListCircuit_eq_zero res n 2 k
    _ _ horacle, zero_add]; refine ⟨by rw [hexp, htr_prep], ?_⟩; rw [hmass_prep] at hcost
  exact hcost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hub) zero_le)
private noncomputable def fallbackCleanR2Circuit {Var : Type} (res : Var) (n k : ℕ) (T : Finset (Fin
    (2 ^ n))) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var (findAllQubits n 2 k)
    ((n + 1) * 2) :=
  .seq (prepSlotsListCircuit res n 2 k (fun _ => true) (List.finRange 2))
    (cswapWarmM2StageRec res (phiFnOfWmSt (wmCellSt 1)) n k 1 T (fun _ => halfAngleSet n 2))
private theorem fallbackCleanR2_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn
  : 200 ≤ n) (hk1024 : k ≤ 1024) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S)
  (hA2 : (S \ T).card = 2) {Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k)} (hΔ : PureStateAt
    (Pi.single
  0 1) Δ) :
    let prog := (fallbackCleanR2Circuit res n k T).compile QProg.qAssign (parallelMarkingOracle 2 S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (2 * √((2 : ℝ) ^ n)) := by
  intro prog; have hn100 : 100 ≤ n := (by omega); let oracle := parallelMarkingOracle 2 S
  have horacle := isRealMatrix_parallelMarkingOracle (m := 2) S
  have hN16 : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right
    (by positivity) hn); have hA_pos : 1 ≤ (S \ T).card := (by omega)
  have hA_lt : (S \ T).card < 2 ^ n := (by omega); have hP0 : PureStateAt (prodSlotState n 2 k fun _
    => Pi.single 0 1) Δ := (by rwa [prodSlotState_single_zero])
  obtain ⟨hPprep, htr_prep⟩ := prepSlotsListCircuit_pureStateAt oracle res (fun _ => true)
    (List.finRange 2) (List.nodup_finRange 2) hA_pos hA_lt (fun _ => dotProduct_single_one 0) hP0
  set Ξ_prep := (interp ((prepSlotsListCircuit res n 2 k (fun _ => true) (List.finRange 2)).compile
    QProg.qAssign oracle)).toStateFun Δ
  have hPprep' : PureStateAt (prodSlotState n 2 k fun _ => slotPairVec (planeVec (S \ T)
    (halfAngleSet n 2)) (Pi.single 0 1)) Ξ_prep := by
    convert hPprep using 2
    funext _; simp [List.mem_finRange, hA2]
  obtain ⟨hΦ1, hB1⟩ := validCswapWarmM2Potential_of_checkWarm2CellCert (cert_warm2_by_kIdx (Or.inl
    rfl)) hn100
  have hvalid2 : ValidStageBetas n 2 (5 / 4) (fun _ : Fin 2 => halfAngleSet n 2) := by
    intro _; have hub := hΦ1.ub_lb 2 (by omega) (by omega)
    have h1 := hΦ1.phi_lb 2 (by omega) (by omega); have h0 : 0 ≤ halfAngleSet n 2 :=
      Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
    simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte] at hub; exact ⟨le_rfl, by linarith⟩
  obtain ⟨hexp, hcost⟩ := cswapWarmM2StageRec_rMax_transition res hn100 hk1024 (by omega : 2 ≤ 1024)
    hΦ1 hScard 1 le_rfl T hTS hA2 _ hvalid2 Ξ_prep hPprep'
  have hub_2 : wmPotential (wmCellB 1) (wmCellSt 1) (wmCellW 1) n 2 (fun _ => halfAngleSet n 2) ≤ 2
    * √((2 : ℝ) ^ n) := by
    refine hB1.trans ?_; have hrc : (((relCostNumWarm2 1 : ℚ≥0) / 10000000000 : ℚ≥0) : ℝ) ≤ 1 :=
      (by dsimp only [relCostNumWarm2]; push_cast; norm_num); have hpi4 : π / 4 ≤ 1 :=
      (by linarith [Real.pi_lt_four])
    have hsum2 : (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ 1), 1 / √(r : ℝ)) ≤ 2 := by
      have hI : Finset.Icc (1 : ℕ) (2 ^ 1) = {1, 2} := (by ext x; simp; omega); rw [hI,
        Finset.sum_pair (by simp)]
      have hsq2 : (1 : ℝ) ≤ √2 := sq_le_imp_le zero_le_one (Real.sqrt_nonneg 2)
        (by rw [Real.sq_sqrt (by norm_num)]; norm_num); have hinv : 1 / √(2 : ℝ) ≤ 1 :=
        div_le_one_of_le₀ hsq2 (by positivity); simp only [Nat.cast_one, Real.sqrt_one, div_one,
        Nat.cast_ofNat]; linarith
    have hdiv_le : √((2 ^ n : ℝ) / (2 : ℕ)) ≤ √((2 : ℝ) ^ n) := by
      rw [show (2 ^ n : ℝ) = (2 : ℝ) ^ n by norm_num]; exact Real.sqrt_le_sqrt (div_le_self
        (by positivity) (by norm_num))
    calc (((relCostNumWarm2 1 : ℚ≥0) / 10000000000 : ℚ≥0) : ℝ) *
          ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) (2 ^ 1), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ)))
        ≤ 1 * ((1 * 2) * √((2 : ℝ) ^ n)) :=
          mul_le_mul hrc (mul_le_mul (mul_le_mul hpi4 hsum2 (by positivity) zero_le_one)
            hdiv_le (by positivity) (by positivity)) (by positivity) zero_le_one
      _ = 2 * √((2 : ℝ) ^ n) := by ring
  have hmass_prep : (Ξ_prep.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) := congrArg ENNReal.ofNNReal htr_prep
  dsimp only [prog, fallbackCleanR2Circuit]; rw [OracleDynamicCircuit.compile_seq, interp_qSeq,
    QMonad.Q.toStateFun_bind, expectedCost_qSeq, expectedCost_prepSlotsListCircuit_eq_zero res n 2 k
    _ _ horacle, zero_add]; refine ⟨by rw [hexp, htr_prep], ?_⟩; rw [hmass_prep] at hcost
  exact hcost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hub_2) zero_le)
private def maskOfSetR2 {n : ℕ} (A : Finset (Fin (2 ^ n))) (u : Fin (2 ^ (2 * n))) : Fin (2 ^ 2) :=
  if addrEquiv n 2 u s0 ∈ A then
    if addrEquiv n 2 u s1 ∈ A then ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ else ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩
  else
    if addrEquiv n 2 u s1 ∈ A then ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ else 0
private theorem parallelMarkingOracle_mulVec_localReal {n : ℕ} (A : Finset (Fin (2 ^ n))) (v : Fin
  (2 ^ (2 * n)) → ℝ) : (parallelMarkingOracle 2 A).1 *ᵥ (localAddrReg n 2).tensorState (fun u => ((v
  u : ℝ) : ℂ)) (Pi.single 0 1) = fun z =>
        let u := (localAddrReg n 2).extractIndex z
        if ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n (maskOfSetR2 A u) then ((v u : ℝ)
          : ℂ) else 0 := by
  have hexpand : (localAddrReg n 2).tensorState (fun u => ((v u : ℝ) : ℂ)) (Pi.single 0 1) = ∑ z :
    Fin (2 ^ ((n + 1) * 2)), ((localAddrReg n 2).tensorState (fun u => ((v u : ℝ) : ℂ)) (Pi.single 0
    1) z) • Pi.single z (1 : ℂ) := (by funext w; simp [Finset.sum_apply, Pi.single_apply])
  rw [hexpand, Matrix.mulVec_sum]; simp_rw [Matrix.mulVec_smul,
    parallelMarkingOracle_mulVec_single_local]; have hfin2 : List.finRange 2 = [s0, s1] := rfl;
    simp_rw [hfin2]; set markMap := localAppMark n 2 A [s0, s1]
  have haddr (z : Fin (2 ^ ((n + 1) * 2))) (i : Fin 2) : localSlotAddr n 2 (markMap z) i =
    localSlotAddr n 2 z i := by
    dsimp only [markMap, localAppMark, localSlotAddr]; rcases fin2_eq_s0_or_s1 i with rfl | rfl
    · rw [(localSlotReg n 2 s0).extractIndex_replaceIndex, extractIndex_localIdxReg_slotMarkPerm,
        (localSlotReg n 2 s0).extractIndex_replaceIndex_of_disjoint (localSlotReg n 2 s1)
        (localSlotReg_disjoint (by simp))]
    · rw [(localSlotReg n 2 s1).extractIndex_replaceIndex_of_disjoint (localSlotReg n 2 s0)
        (localSlotReg_disjoint (by simp)), (localSlotReg n 2 s1).extractIndex_replaceIndex,
        extractIndex_localIdxReg_slotMarkPerm]
  have hexA (z : Fin (2 ^ ((n + 1) * 2))) : (localAddrReg n 2).extractIndex (markMap z) =
    (localAddrReg n 2).extractIndex z := by
    apply (addrEquiv n 2).injective; funext i; rw [addrEquiv_extractIndex_localAddrReg,
      addrEquiv_extractIndex_localAddrReg, haddr]
  have hflag (z : Fin (2 ^ ((n + 1) * 2))) (i : Fin 2) : basisBits 1 (localSlotFlag n 2 (markMap z)
    i) 0 = basisBits 1 (localSlotFlag n 2 z i) 0 + (if localSlotAddr n 2 z i ∈ A then 1 else 0)
    := by
    dsimp only [markMap, localAppMark, localSlotFlag, localSlotAddr]; have hmw : (localMarkerReg
      n).wires 0 = 0 := Fin.ext (by simp [localMarkerReg]); rcases fin2_eq_s0_or_s1 i with rfl | rfl
    · rw [(localMarkerReg n).basisBits_extractIndex, (localMarkerReg n).basisBits_extractIndex, hmw,
        (localSlotReg n 2 s0).extractIndex_replaceIndex, (localSlotReg n 2
        s0).extractIndex_replaceIndex_of_disjoint (localSlotReg n 2 s1) (localSlotReg_disjoint
        (by simp)), basisBits_slotMarkPerm]
      by_cases hm : (localIdxReg n).extractIndex ((localSlotReg n 2 s0).extractIndex z) ∈ A <;> simp
        [hm]
    · rw [(localMarkerReg n).basisBits_extractIndex, (localMarkerReg n).basisBits_extractIndex, hmw,
        (localSlotReg n 2 s1).extractIndex_replaceIndex_of_disjoint (localSlotReg n 2 s0)
        (localSlotReg_disjoint (by simp)), (localSlotReg n 2 s1).extractIndex_replaceIndex,
        basisBits_slotMarkPerm]; by_cases hm : (localIdxReg n).extractIndex ((localSlotReg n 2
        s1).extractIndex z) ∈ A <;> simp [hm]
  have hmark_inv (z : Fin (2 ^ ((n + 1) * 2))) : markMap (markMap z) = z := by
    apply (localAddrReg n 2).basisSplitEquiv.injective; ext1
    · rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst, hexA, hexA]
    · funext ew; rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl <;> rw [←
        basisBits_localSlotFlag, ← basisBits_localSlotFlag, hflag, hflag, haddr, add_assoc,
        CharTwo.add_self_eq_zero, add_zero]
  funext w; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; rw [Finset.sum_eq_single
    (markMap w)]
  · rw [hmark_inv w, Pi.single_eq_same, mul_one]; dsimp only [QRegister.tensorState]
    rw [hexA]; set u := (localAddrReg n 2).extractIndex w; have h0_addr : localSlotAddr n 2 w s0 =
      addrEquiv n 2 u s0 := (addrEquiv_extractIndex_localAddrReg n 2 w s0).symm
    have h1_addr : localSlotAddr n 2 w s1 = addrEquiv n 2 u s1 :=
      (addrEquiv_extractIndex_localAddrReg n 2 w s1).symm
    have henv_iff : ((localAddrReg n 2).basisSplitEquiv (markMap w)).2 = 0 ↔ ((localAddrReg n
      2).basisSplitEquiv w).2 = envOfMask n (maskOfSetR2 A u) := by
      constructor
      · intro h0; funext ew
        have hi (i : Fin 2) : ((localAddrReg n 2).basisSplitEquiv w).2 (localFlagEnvWire n 2 i) = if
          addrEquiv n 2 u i ∈ A then 1 else 0 := by
          have h := congrFun h0 (localFlagEnvWire n 2 i); rw [← basisBits_localSlotFlag, hflag,
            Pi.zero_apply] at h
          have hadd := congrArg (· + if localSlotAddr n 2 w i ∈ A then 1 else 0) h
          simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add,
            basisBits_localSlotFlag] at hadd; rcases fin2_eq_s0_or_s1 i with rfl | rfl
          · rwa [h0_addr] at hadd
          · rwa [h1_addr] at hadd
        rcases localAddrEnv_eq_flag0_or_flag1 n ew with rfl | rfl
        · rw [hi s0, envOfMask_s0]; dsimp only [maskOfSetR2]
          by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A <;>
            (simp only [hx0, hx1, ↓reduceIte]; rfl)
        · rw [hi s1, envOfMask_s1]; dsimp only [maskOfSetR2]
          by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A <;>
            (simp only [hx0, hx1, ↓reduceIte]; rfl)
      · intro hwE; funext ew; rw [Pi.zero_apply]; rcases localAddrEnv_eq_flag0_or_flag1 n ew with
          rfl | rfl
        · rw [← basisBits_localSlotFlag, hflag, basisBits_localSlotFlag, hwE, envOfMask_s0, h0_addr]
          dsimp only [maskOfSetR2]
          by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A <;>
            (simp only [hx0, hx1, ↓reduceIte]; rfl)
        · rw [← basisBits_localSlotFlag, hflag, basisBits_localSlotFlag, hwE, envOfMask_s1, h1_addr]
          dsimp only [maskOfSetR2]
          by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A <;>
            (simp only [hx0, hx1, ↓reduceIte]; rfl)
    by_cases hE : ((localAddrReg n 2).basisSplitEquiv w).2 = envOfMask n (maskOfSetR2 A u)
    · rw [ite_eq_left hE, henv_iff.2 hE, Pi.single_eq_same, mul_one]
    · rw [ite_eq_right hE, Pi.single_eq_of_ne (mt henv_iff.1 hE), mul_zero]
  · intro z _ hz; have hne : w ≠ markMap z := fun h => hz (by rw [h, hmark_inv])
    simp [Pi.single_eq_of_ne hne]
  · intro habs; exact (habs (Finset.mem_univ _)).elim
private noncomputable def jp01ReadoutCircuit {Var : Type} (res : Var) (n k : ℕ) (T : Finset (Fin (2
    ^ n))) (cont0 : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var (findAllQubits n 2
    k) ((n + 1) * 2)) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var (findAllQubits
    n 2 k) ((n + 1) * 2) :=
  .seq (deflateCirc n 2 T (.oracle (oracleReg n 2 k)))
    (.seq (.measure res (oracleReg n 2 k))
      (dispBits res ((n + 1) * 2) 0 fun zVal =>
        let z : Fin (2 ^ ((n + 1) * 2)) := ⟨zVal % 2 ^ ((n + 1) * 2), Nat.mod_lt _ (by positivity)⟩
        let u := (localAddrReg n 2).extractIndex z
        let x0 := addrEquiv n 2 u s0
        let x1 := addrEquiv n 2 u s1
        let o := (localAllMarkersReg n 2).extractIndex z
        let f0 := o.val.testBit 0
        let f1 := o.val.testBit 1
        .seq (resetRegCircuit res (oracleReg n 2 k))
          (if f0 && f1 then
            writeFinsetCircuit res n 2 k (insert x0 (insert x1 T))
          else if f0 then
            zeroHitCleanR1Circuit res n k (insert x0 T)
          else if f1 then
            zeroHitCleanR1Circuit res n k (insert x1 T)
          else
            cont0)))
private theorem jp01Readout_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn :
  200 ≤ n) (hk1024 : k ≤ 1024) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA2
  : (S \ T).card = 2) {v : Fin (2 ^ (2 * n)) → ℝ} (hv_norm : v ⬝ᵥ v = 1) (hv_off : ∀ u, addrEquiv n
  2 u s0 = addrEquiv n 2 u s1 → v u = 0) {B0 : ℝ} (hB0_nn : 0 ≤ B0) {cont0 : OracleDynamicCircuit
  (Unitary (2 ^ findAllQubits n 2 k)) Var (findAllQubits n 2 k) ((n + 1) * 2)} (hcont0 : ∀ Υ :
  CQState (Store Var) (2 ^ findAllQubits n 2 k), PureStateAt (Pi.single 0 1) Υ → 𝔼[(interp
    (cont0.compile
  QProg.qAssign (parallelMarkingOracle 2 S))).toStateFun Υ, liftPureProp (fun τ =>
  decodeTargetsLocal n k (τ res) = S)] = Υ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle
  (parallelMarkingOracle 2 S)) (cont0.compile QProg.qAssign (parallelMarkingOracle 2 S)) Υ ≤
  (Υ.trace : ℝ≥0∞) * ENNReal.ofReal B0) {Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k)} (hΔ :
  PureStateAt
  ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState (fun u => ((v u : ℝ) : ℂ))
  (Pi.single 0 1)) (Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 1)) Δ) :
    let A := S \ T
    let p0 := ∑ u ∈ Finset.univ.filter (fun u => addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A),
      (v u) ^ 2
    let p2 := ∑ u ∈ Finset.univ.filter (fun u => addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈ A),
      (v u) ^ 2
    let zh := ((cswapZeroHitNat : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)
    let prog := (jp01ReadoutCircuit res n k T cont0).compile QProg.qAssign (parallelMarkingOracle 2
      S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (1 + (1 - p2 - p0) * zh + p0 * B0) := by
  intro A p0 p2 zh prog; let oracleS := parallelMarkingOracle 2 S
  let oracleA := parallelMarkingOracle 2 A
  let modelS := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracleS
  let modelA := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracleA
  have horacleS := isRealMatrix_parallelMarkingOracle (m := 2) S
  let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ :=
    Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 1
  let ψ_in := (oracleReg n 2 k).tensorState
    ((localAddrReg n 2).tensorState (fun u => ((v u : ℝ) : ℂ)) (Pi.single 0 1)) env0
  have hv_c : star (fun u => ((v u : ℝ) : ℂ)) ⬝ᵥ (fun u => ((v u : ℝ) : ℂ)) = 1 := by
    have hr : ((v ⬝ᵥ v : ℝ) : ℂ) = 1 := (by rw [hv_norm, Complex.ofReal_one])
    rw [← hr]; simp [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  have hψ_in : star ψ_in ⬝ᵥ ψ_in = 1 := by
    dsimp only [ψ_in]; rw [dotProduct_tensorState, dotProduct_tensorState, hv_c,
      dotProduct_env_single, dotProduct_env_single, mul_one, mul_one]
  have hcost_q : expectedCost modelS ((deflateCirc (Var := Var) n 2 T (.oracle (oracleReg n 2
    k))).compile QProg.qAssign oracleS) Δ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 := by
    rw [congrFun (expectedCost_deflateCirc n 2 hTS (c := .oracle (oracleReg n 2 k)) trivial) Δ]
    simp only [OracleDynamicCircuit.compile_oracle, expectedCost_qAssign]
    have hex : ∃ r : QRegister ((n + 1) * 2) (findAllQubits n 2 k), (oracleReg n 2 k).embedUnitary
      oracleA = r.embedUnitary oracleA := ⟨oracleReg n 2 k, rfl⟩
    have h1 : modelA.unitaryCost ((oracleReg n 2 k).embedUnitary oracleA) = 1 :=
      (by simp [modelA, CostModel.ofEmbeddedOracle, hex]); rw [h1]; simp
  set Δq := (interp ((deflateCirc (Var := Var) n 2 T (.oracle (oracleReg n 2 k))).compile
    QProg.qAssign oracleS)).toStateFun Δ
  have hΔq_eq : Δq = CQState.qAssign ((oracleReg n 2 k).embedUnitary oracleA) Δ := by
    dsimp only [Δq]; rw [interp_deflateCirc n 2 hTS (.oracle (oracleReg n 2 k)),
      OracleDynamicCircuit.compile_oracle, interp_qAssign]; rfl
  obtain ⟨hPq, htr_q⟩ := pureStateAt_qAssign ((oracleReg n 2 k).embedUnitary oracleA) hψ_in hΔ
  rw [← hΔq_eq] at hPq htr_q; let ψ_q := ((oracleReg n 2 k).embedUnitary oracleA).1 *ᵥ ψ_in
  have hψ_q : star ψ_q ⬝ᵥ ψ_q = 1 := dotProduct_unitary_mulVec ((oracleReg n 2 k).embedUnitary
    oracleA) hψ_in
  let locAmp : Fin (2 ^ ((n + 1) * 2)) → ℝ := fun z =>
    let u := (localAddrReg n 2).extractIndex z
    if ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n (maskOfSetR2 A u) then v u else 0
  let wz : Fin (2 ^ ((n + 1) * 2)) → ℝ := fun z => (locAmp z) ^ 2
  have hwz_nn (z : Fin (2 ^ ((n + 1) * 2))) : 0 ≤ wz z := sq_nonneg _
  let sgnZ (z : Fin (2 ^ ((n + 1) * 2))) : ℝ := if 0 ≤ locAmp z then 1 else -1
  let ψ_out (z : Fin (2 ^ ((n + 1) * 2))) : Fin (2 ^ findAllQubits n 2 k) → ℂ :=
    (oracleReg n 2 k).tensorState (((sgnZ z : ℝ) : ℂ) • Pi.single z 1) env0
  have h_sgn_norm (z : Fin (2 ^ ((n + 1) * 2))) : star (((sgnZ z : ℝ) : ℂ) • (Pi.single z 1 : Fin (2
    ^ ((n + 1) * 2)) → ℂ)) ⬝ᵥ (((sgnZ z : ℝ) : ℂ) • Pi.single z 1) = 1 := by
    dsimp only [sgnZ]; split_ifs
    · rw [Complex.ofReal_one, one_smul]; exact dotProduct_single_one z
    · rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_smul, star_neg, neg_dotProduct,
        dotProduct_neg, neg_neg]; exact dotProduct_single_one z
  have hψ_out (z : Fin (2 ^ ((n + 1) * 2))) : star (ψ_out z) ⬝ᵥ ψ_out z = 1 := by
    dsimp only [ψ_out]; rw [dotProduct_tensorState, h_sgn_norm z, dotProduct_env_single, mul_one]
  have hproj (z : Fin (2 ^ ((n + 1) * 2))) : (oracleReg n 2 k).basisOutcomeProjector z *ᵥ ψ_q =
    ((√(wz z) : ℝ) : ℂ) • ψ_out z := by
    have hψq_eq : ψ_q = (oracleReg n 2 k).tensorState (fun y => ((locAmp y : ℝ) : ℂ)) env0 := by
      dsimp only [ψ_q, ψ_in, oracleA, locAmp]; rw [QRegister.embedUnitary_val, (oracleReg n 2
        k).embedMatrix_mulVec_tensorState, parallelMarkingOracle_mulVec_localReal]
      apply congrArg (fun f => (oracleReg n 2 k).tensorState f env0); funext y; dsimp only
      by_cases h : ((localAddrReg n 2).basisSplitEquiv y).2 = envOfMask n (maskOfSetR2 A
        ((localAddrReg n 2).extractIndex y)) <;> simp [h]
    have hamp_eq : ((locAmp z : ℝ) : ℂ) = ((√(wz z) : ℝ) : ℂ) * ((sgnZ z : ℝ) : ℂ) := by
      dsimp only [wz, sgnZ]; rw [Real.sqrt_sq_eq_abs]; by_cases h0 : 0 ≤ locAmp z
      · rw [ite_eq_left h0, abs_of_nonneg h0]; push_cast; ring
      · rw [ite_eq_right h0, abs_of_neg (lt_of_not_ge h0)]; push_cast; ring
    rw [hψq_eq]; funext w; rw [(oracleReg n 2 k).basisOutcomeProjector_mulVec]
    dsimp only [QRegister.tensorState, ψ_out, Pi.smul_apply, smul_eq_mul]; by_cases hw : (oracleReg
      n 2 k).extractIndex w = z
    · rw [ite_eq_left hw, hw, Pi.single_eq_same, mul_one, hamp_eq, mul_assoc]
    · rw [ite_eq_right hw, Pi.single_eq_of_ne hw, mul_zero, zero_mul, mul_zero]
  set Δm := (interp (QProg.measureRegister res (oracleReg n 2 k))).toStateFun Δq; have hmeas :=
    measure_sliceState_of_pureStateAt res (oracleReg n 2 k) hψ_q wz hwz_nn ψ_out hψ_out hproj hPq
  let branchCirc (z : Fin (2 ^ ((n + 1) * 2))) :=
    let u := (localAddrReg n 2).extractIndex z; let x0 := addrEquiv n 2 u s0
    let x1 := addrEquiv n 2 u s1; let o := (localAllMarkersReg n 2).extractIndex z
    let f0 := o.val.testBit 0; let f1 := o.val.testBit 1
    OracleDynamicCircuit.seq (resetRegCircuit res (oracleReg n 2 k))
      (if f0 && f1 then
        writeFinsetCircuit res n 2 k (insert x0 (insert x1 T))
      else if f0 then zeroHitCleanR1Circuit res n k (insert x0 T)
      else if f1 then zeroHitCleanR1Circuit res n k (insert x1 T)
      else
        cont0)
  let branchCost (z : Fin (2 ^ ((n + 1) * 2))) : ℝ :=
    let o := (localAllMarkersReg n 2).extractIndex z; let f0 := o.val.testBit 0
    let f1 := o.val.testBit 1
    if f0 && f1 then 0 else if f0 || f1 then zh else B0
  have hzh_nn : 0 ≤ zh := (by dsimp only [zh]; positivity)
  have hbc_nn (z : Fin (2 ^ ((n + 1) * 2))) : 0 ≤ branchCost z := by
    dsimp only [branchCost]; split_ifs
    · exact le_rfl
    · exact hzh_nn
    · exact hB0_nn
  let Post : CQAssertion (Store Var) (2 ^ findAllQubits n 2 k) :=
    liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)
  have hϕ0 : star ((oracleReg n 2 k).tensorState (Pi.single 0 1) env0) ⬝ᵥ (oracleReg n 2
    k).tensorState (Pi.single 0 1) env0 = 1 :=
    (by rw [dotProduct_tensorState, dotProduct_single_one, dotProduct_env_single, mul_one])
  have hz_zero_eq : (oracleReg n 2 k).tensorState (Pi.single 0 1) env0 = Pi.single 0 1 :=
    (by rw [← prodSlotLocalVec_single_zero n 2]; exact prodSlotState_single_zero n 2 k)
  have hbranch (z : Fin (2 ^ ((n + 1) * 2))) :
      let fz := (branchCirc z).compile QProg.qAssign oracleS
      let Ξ_z := sliceState res 0 ((n + 1) * 2) z.val Δm
      𝔼[(interp fz).toStateFun Ξ_z, Post] = wz z * Δ.trace ∧
        expectedCost modelS fz Ξ_z ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (wz z * branchCost z) := by
    intro fz Ξ_z; obtain ⟨hPz, htrz⟩ := hmeas z; rw [htr_q] at htrz; by_cases hwz0 : wz z = 0
    · have htr0 : Ξ_z.trace = 0 := NNReal.coe_inj.mp (by push_cast; rw [htrz, hwz0, zero_mul])
      have hto0 : ((interp fz).toStateFun Ξ_z).trace = 0 :=
        nonpos_iff_eq_zero.mp (((interp fz).trace_toStateFun_le _).trans_eq htr0)
      refine ⟨?_, ?_⟩
      · rw [expect_eq_zero_of_trace_eq_zero hto0 Post, hwz0, zero_mul]
      · rw [expectedCost_eq_zero_of_trace_eq_zero modelS oracleS (branchCirc z) htr0]; exact zero_le
    · have hamp_ne : locAmp z ≠ 0 := fun h => hwz0 (by simp [wz, h])
      dsimp only [locAmp] at hamp_ne; set u := (localAddrReg n 2).extractIndex z
      by_cases hE : ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n (maskOfSetR2 A u)
      swap
      · exact (hamp_ne (ite_eq_right hE)).elim
      rw [ite_eq_left hE] at hamp_ne
      have hne_addr : addrEquiv n 2 u s0 ≠ addrEquiv n 2 u s1 :=
        fun hd => hamp_ne (hv_off u hd)
      have ho_eq : (localAllMarkersReg n 2).extractIndex z = maskOfSetR2 A u :=
        (basisSplit_snd_eq_envOfMask_iff n z (maskOfSetR2 A u)).1 hE; obtain ⟨hPrst, htr_rst⟩ :=
        resetRegCircuit_pureStateAt oracleS res (oracleReg n 2 k) (h_sgn_norm z) hϕ0 hPz
      set Ξ_rst := (interp ((resetRegCircuit res (oracleReg n 2 k)).compile QProg.qAssign
        oracleS)).toStateFun Ξ_z; rw [hz_zero_eq] at hPrst
      have hmass_z : (Ξ_z.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (wz z) := by
        nth_rw 1 [← ENNReal.ofReal_coe_nnreal]
        rw [htrz, mul_comm (wz z), ENNReal.ofReal_mul Δ.trace.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      have hmass_rst : (Ξ_rst.trace : ℝ≥0∞) = (Ξ_z.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal htr_rst
      dsimp only [fz,
        branchCirc, branchCost]; rw [ho_eq, OracleDynamicCircuit.compile_seq, interp_qSeq,
        QMonad.Q.toStateFun_bind, expectedCost_qSeq, expectedCost_resetRegCircuit_eq_zero res _
        horacleS, zero_add]
      by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A
      · have hm3 : maskOfSetR2 A u = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ :=
          (by simp only [maskOfSetR2, hx0, hx1, ↓reduceIte]); rw [hm3]; simp only [show (3 :
          ℕ).testBit 0 = true from rfl, show (3 : ℕ).testBit 1 = true from rfl, Bool.and_self,
          ↓reduceIte, mul_zero, ENNReal.ofReal_zero]
        have hpair_eq : ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) = A := by
          apply Finset.eq_of_subset_of_card_le
          · intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy; rcases hy with
              rfl | rfl <;> assumption
          · rw [hA2, Finset.card_pair hne_addr]
        have hins_S : insert (addrEquiv n 2 u s0) (insert (addrEquiv n 2 u s1) T) = S := by
          calc insert (addrEquiv n 2 u s0) (insert (addrEquiv n 2 u s1) T)
              = ({addrEquiv n 2 u s0, addrEquiv n 2 u s1} : Finset (Fin (2 ^ n))) ∪ T := by
                ext y; simp
            _ = (S \ T) ∪ T := by rw [hpair_eq]
            _ = S := Finset.sdiff_union_of_subset hTS
        rw [hins_S]; have hsupp0 := supportedOn_of_pureStateAt
          (pred := (· = (0 : Fin (2 ^ findAllQubits n 2 k))))
          (fun y hy => Pi.single_eq_of_ne hy 1) hPrst
        have hexp_w : 𝔼[(interp ((writeFinsetCircuit res n 2 k S).compile QProg.qAssign
          oracleS)).toStateFun Ξ_rst, Post] = Ξ_rst.trace := by
          rw [← wp_expectation_eq, expect_of_supportedOn hsupp0 (diagProj_zero_wp_writeFinsetCircuit
            res hScard oracleS), one_mul]
        refine ⟨by rw [hexp_w, htr_rst, htrz], ?_⟩; rw [expectedCost_writeFinsetCircuit res n 2
          k S horacleS]
      · have hm1 : maskOfSetR2 A u = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ :=
          (by simp only [maskOfSetR2, hx0, hx1, ↓reduceIte]); rw [hm1]; simp only [show (1 :
          ℕ).testBit 0 = true from rfl, show (1 : ℕ).testBit 1 = false from rfl, Bool.and_false,
          Bool.true_or, Bool.false_eq_true, ↓reduceIte]
        have hTS' : insert (addrEquiv n 2 u s0) T ⊆ S := Finset.insert_subset (Finset.mem_sdiff.1
          hx0).1 hTS
        have hcard1 : (S \ insert (addrEquiv n 2 u s0) T).card = 1 := by
          have hsdiff : S \ insert (addrEquiv n 2 u s0) T = A \ {addrEquiv n 2 u s0} := by
            ext y; simp only [A, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [hsdiff, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hx0),
            Finset.card_singleton, hA2]
        obtain ⟨hexp1, hcost1⟩ := zeroHitCleanR1_transition res hn hk1024 hScard hTS' hcard1 hPrst
        refine ⟨by rw [hexp1, htr_rst, htrz], ?_⟩
        calc _ ≤ (Ξ_rst.trace : ℝ≥0∞) * ENNReal.ofReal zh := hcost1
          _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (wz z * zh) := by
              rw [hmass_rst, hmass_z, mul_assoc, ← ENNReal.ofReal_mul (hwz_nn z)]
      · have hm2 : maskOfSetR2 A u = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ :=
          (by simp only [maskOfSetR2, hx0, hx1, ↓reduceIte]); rw [hm2]; simp only [show (2 :
          ℕ).testBit 0 = false from rfl, show (2 : ℕ).testBit 1 = true from rfl, Bool.false_and,
          Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        have hTS' : insert (addrEquiv n 2 u s1) T ⊆ S := Finset.insert_subset (Finset.mem_sdiff.1
          hx1).1 hTS
        have hcard1 : (S \ insert (addrEquiv n 2 u s1) T).card = 1 := by
          have hsdiff : S \ insert (addrEquiv n 2 u s1) T = A \ {addrEquiv n 2 u s1} := by
            ext y; simp only [A, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
          rw [hsdiff, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hx1),
            Finset.card_singleton, hA2]
        obtain ⟨hexp1, hcost1⟩ := zeroHitCleanR1_transition res hn hk1024 hScard hTS' hcard1 hPrst
        refine ⟨by rw [hexp1, htr_rst, htrz], ?_⟩
        calc _ ≤ (Ξ_rst.trace : ℝ≥0∞) * ENNReal.ofReal zh := hcost1
          _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (wz z * zh) := by
              rw [hmass_rst, hmass_z, mul_assoc, ← ENNReal.ofReal_mul (hwz_nn z)]
      · have hm0 : maskOfSetR2 A u = 0 := (by simp only [maskOfSetR2, hx0, hx1, ↓reduceIte])
        rw [hm0]; simp only [Fin.val_zero, Nat.zero_testBit, Bool.false_and, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte]; obtain ⟨hexp0, hcost0⟩ := hcont0 Ξ_rst hPrst
        refine ⟨by rw [hexp0, htr_rst, htrz], ?_⟩
        calc _ ≤ (Ξ_rst.trace : ℝ≥0∞) * ENNReal.ofReal B0 := hcost0
          _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (wz z * B0) := by
              rw [hmass_rst, hmass_z, mul_assoc, ← ENNReal.ofReal_mul (hwz_nn z)]
  have hwz_eq (z : Fin (2 ^ ((n + 1) * 2))) : wz z = if ((localAddrReg n 2).basisSplitEquiv z).2 =
    envOfMask n (maskOfSetR2 A ((localAddrReg n 2).extractIndex z)) then (v ((localAddrReg n
    2).extractIndex z)) ^ 2 else 0 := by
    dsimp only [wz, locAmp]; split_ifs <;> simp
  have hsum_fiber (g : Fin (2 ^ (2 * n)) → ℝ) : (∑ z : Fin (2 ^ ((n + 1) * 2)), wz z * g
    ((localAddrReg n 2).extractIndex z)) = ∑ u : Fin (2 ^ (2 * n)), (v u) ^ 2 * g u := by
    rw [← (localAddrReg n 2).basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single (envOfMask n (maskOfSetR2 A u))]
    · simp [wz, locAmp, ← QRegister.basisSplitEquiv_apply_fst]
    · intro e _ he; have hne : e ≠ envOfMask n (maskOfSetR2 A u) := he; simp [wz, locAmp, ←
        QRegister.basisSplitEquiv_apply_fst, hne]
    · intro habs; exact (habs (Finset.mem_univ _)).elim
  have hwz_sum : ∑ z : Fin (2 ^ ((n + 1) * 2)), wz z = 1 := by
    have h1 := hsum_fiber (fun _ => 1)
    simp only [mul_one] at h1; rw [h1]; simpa [dotProduct, sq] using hv_norm
  have hcost_sum : (∑ z : Fin (2 ^ ((n + 1) * 2)), wz z * branchCost z) = (1 - p2 - p0) * zh + p0 *
    B0 := by
    let gCost : Fin (2 ^ (2 * n)) → ℝ := fun u =>
      if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈ A then 0
      else if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A then B0
      else zh
    have hbc_u (z : Fin (2 ^ ((n + 1) * 2))) : wz z * branchCost z = wz z * gCost ((localAddrReg n
      2).extractIndex z) := by
      by_cases hE : ((localAddrReg n 2).basisSplitEquiv z).2 = envOfMask n (maskOfSetR2 A
        ((localAddrReg n 2).extractIndex z))
      · have ho : (localAllMarkersReg n 2).extractIndex z = maskOfSetR2 A ((localAddrReg n
          2).extractIndex z) := (basisSplit_snd_eq_envOfMask_iff n z _).1 hE
        dsimp only [branchCost, gCost]; rw [ho]; set u := (localAddrReg n 2).extractIndex z
        by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A
        · have hm : maskOfSetR2 A u = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ :=
            (by simp only [maskOfSetR2, hx0, hx1, ↓reduceIte]); rw [hm]; simp [hx0, hx1, show (3 :
            ℕ).testBit 0 = true from rfl, show (3 : ℕ).testBit 1 = true from rfl]
        · have hm : maskOfSetR2 A u = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ :=
            (by simp only [maskOfSetR2, hx0, hx1, ↓reduceIte]); rw [hm]; simp [hx0, hx1, show (1 :
            ℕ).testBit 0 = true from rfl, show (1 : ℕ).testBit 1 = false from rfl]
        · have hm : maskOfSetR2 A u = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ :=
            (by simp only [maskOfSetR2, hx0, hx1, ↓reduceIte]); rw [hm]; simp [hx0, hx1, show (2 :
            ℕ).testBit 0 = false from rfl, show (2 : ℕ).testBit 1 = true from rfl]
        · have hm : maskOfSetR2 A u = 0 := (by simp only [maskOfSetR2, hx0, hx1, ↓reduceIte])
          rw [hm]; simp [hx0, hx1]
      · rw [hwz_eq, ite_eq_right hE, zero_mul, zero_mul]
    simp_rw [hbc_u]; rw [hsum_fiber gCost]; dsimp only [gCost]; have hv_sum1 : (∑ u : Fin (2 ^ (2 *
      n)), (v u) ^ 2) = 1 := (by simpa [dotProduct, sq] using hv_norm)
    have hp0_eq : p0 = ∑ u : Fin (2 ^ (2 * n)), if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A
      then (v u) ^ 2 else 0 := (by dsimp only [p0]; rw [Finset.sum_filter])
    have hp2_eq : p2 = ∑ u : Fin (2 ^ (2 * n)), if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈ A
      then (v u) ^ 2 else 0 := (by dsimp only [p2]; rw [Finset.sum_filter])
    have hpt (u : Fin (2 ^ (2 * n))) : (v u) ^ 2 * (if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈
      A then 0 else if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A then B0 else zh) = ((v u) ^ 2
      - (if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈ A then (v u) ^ 2 else 0) - (if addrEquiv n
      2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A then (v u) ^ 2 else 0)) * zh + (if addrEquiv n 2 u s0 ∉ A
      ∧ addrEquiv n 2 u s1 ∉ A then (v u) ^ 2 else 0) * B0 := by
      by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A <;> simp [hx0,
        hx1]
    simp_rw [hpt]; rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, hv_sum1, ← hp2_eq, ← hp0_eq]
  have hprog_unfold : prog = ((deflateCirc n 2 T (.oracle (oracleReg n 2 k))).compile QProg.qAssign
    oracleS ;; (QProg.measureRegister res (oracleReg n 2 k) ;; (dispBits res ((n + 1) * 2) 0 fun
    zVal => branchCirc ⟨zVal % 2 ^ ((n + 1) * 2), Nat.mod_lt _ (by positivity)⟩).compile
    QProg.qAssign oracleS)) := by
    dsimp only [prog, jp01ReadoutCircuit, branchCirc]; rw [OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure]
  rw [hprog_unfold]; refine ⟨?_, ?_⟩
  · rw [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSeq, QMonad.Q.toStateFun_bind,
      expect_dispBits, ← Fin.sum_univ_eq_sum_range]
    have hsum_eq :
        (∑ z : Fin (2 ^ ((n + 1) * 2)), 𝔼[(interp ((branchCirc ⟨z.val % 2 ^ ((n + 1) * 2),
              Nat.mod_lt _ (by positivity)⟩).compile QProg.qAssign oracleS)).toStateFun
              (sliceState res 0 ((n + 1) * 2) z.val Δm), Post]) =
        ∑ z : Fin (2 ^ ((n + 1) * 2)), wz z * Δ.trace :=
      Finset.sum_congr rfl fun z _ => by simpa only [fin_mk_mod_pow] using (hbranch z).1
    rw [hsum_eq, ← Finset.sum_mul, hwz_sum, one_mul]
  · rw [expectedCost_qSeq, expectedCost_qSeq]; have hm0 : expectedCost modelS (QProg.measureRegister
      res (oracleReg n 2 k)) Δq = 0 := (by simp [QProg.measureRegister, modelS]); rw [hm0, zero_add,
      expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range]
    have hdisp_le : (∑ z : Fin (2 ^ ((n + 1) * 2)), expectedCost modelS ((branchCirc ⟨z.val % 2 ^
      ((n + 1) * 2), Nat.mod_lt _ (by positivity)⟩).compile QProg.qAssign oracleS) (sliceState res 0
      ((n + 1) * 2) z.val Δm)) ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - p2 - p0) * zh +
      p0 * B0) := by
      calc _ ≤ ∑ z : Fin (2 ^ ((n + 1) * 2)),
              (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (wz z * branchCost z) :=
            Finset.sum_le_sum fun z _ => by simpa only [fin_mk_mod_pow] using (hbranch z).2
        _ = (Δ.trace : ℝ≥0∞) *
              ENNReal.ofReal (∑ z : Fin (2 ^ ((n + 1) * 2)), wz z * branchCost z) := by
            rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (hwz_nn z)
              (hbc_nn z))]
        _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - p2 - p0) * zh + p0 * B0) := by rw [hcost_sum]
    have hcont_nn : 0 ≤ (1 - p2 - p0) * zh + p0 * B0 := by
      rw [← hcost_sum]; exact Finset.sum_nonneg fun z _ => mul_nonneg (hwz_nn z) (hbc_nn z)
    calc _ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal 1 + (Δ.trace : ℝ≥0∞) *
          ENNReal.ofReal ((1 - p2 - p0) * zh + p0 * B0) := add_le_add hcost_q hdisp_le
      _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (1 + (1 - p2 - p0) * zh + p0 * B0) := by
          rw [← mul_add, ← ENNReal.ofReal_add zero_le_one hcont_nn, add_assoc]
private theorem orbEmbed3_filter_zero_two_sq {n : ℕ} (hn : 200 ≤ n) {A : Finset (Fin (2 ^ n))} (hA2
  : A.card = 2) (x : Fin 3 → ℝ) :
    let v := liftSymPairReal n (DickeSol.orbEmbed3 (2 ^ n) 2 A x)
    v ⬝ᵥ v = DickeSol.dot3 x x ∧ (∑ u ∈ Finset.univ.filter (fun u => addrEquiv n 2 u s0 ∉ A ∧
      addrEquiv n 2 u s1 ∉ A), (v u) ^ 2) = (x 0) ^ 2 ∧ (∑ u ∈ Finset.univ.filter (fun u =>
      addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈ A), (v u) ^ 2) = (x 2) ^ 2 := by
  intro v; have hN16 : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right
    (by positivity) hn); have hmrN : 2 + A.card < 2 ^ n := (by omega)
  have hmin2 : min 2 A.card ≤ 2 := Nat.min_le_left 2 A.card
  have hdot : ∀ y : Fin 3 → ℝ, liftSymPairReal n (DickeSol.orbEmbed3 (2 ^ n) 2 A y) ⬝ᵥ
    liftSymPairReal n (DickeSol.orbEmbed3 (2 ^ n) 2 A y) = DickeSol.dot3 y y := by
    intro y; rw [dotProduct_liftSymPairReal]
    exact DickeSol.dot_orbEmbed3 (by omega) (by omega) hmin2 hmrN y y
  refine ⟨hdot x, ?_, ?_⟩
  · let g0 := DickeSol.orbEmbed3 (2 ^ n) 2 A (DickeSol.vec3 (x 0) 0 0)
    have hpt (u : Fin (2 ^ (2 * n))) : (if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A then (v
      u) ^ 2 else 0) = (liftSymPairReal n g0 u) ^ 2 := by
      by_cases hdiag : addrEquiv n 2 u s0 = addrEquiv n 2 u s1
      · dsimp only [v]; rw [liftSymPairReal_diag_zero _ hdiag, liftSymPairReal_diag_zero _ hdiag]
        simp
      · dsimp only [v]; rw [liftSymPairReal_apply_offDiag _ hdiag, liftSymPairReal_apply_offDiag _
          hdiag]
        set Eu : DickeSol.P01Subset (2 ^ n) 2 :=
          ⟨{addrEquiv n 2 u s0, addrEquiv n 2 u s1}, Finset.card_pair hdiag⟩
        have hlt3 : (Eu.1 ∩ A).card < 3 :=
          DickeSol.inter_card_lt_three hmin2 Eu
        by_cases hc : addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A
        · rw [ite_eq_left hc]
          have h0 : (Eu.1 ∩ A).card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro y hy; simp only [Eu,
              Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hy; rcases hy with ⟨rfl
              | rfl, hyA⟩
            · exact hc.1 hyA
            · exact hc.2 hyA
          have hw : (⟨(Eu.1 ∩ A).card, hlt3⟩ : Fin 3) = 0 := Fin.ext h0; dsimp only [g0,
            DickeSol.orbEmbed3]; simp only [hlt3, ↓reduceDIte]; rw [hw]; simp [DickeSol.vec3]
        · rw [ite_eq_right hc]
          have hpos : 1 ≤ (Eu.1 ∩ A).card := by
            apply Finset.card_pos.2; by_cases hx0 : addrEquiv n 2 u s0 ∈ A
            · exact ⟨addrEquiv n 2 u s0, Finset.mem_inter.2 ⟨by simp [Eu], hx0⟩⟩
            · have hx1 : addrEquiv n 2 u s1 ∈ A := (by by_contra hx1; exact hc ⟨hx0, hx1⟩)
              exact ⟨addrEquiv n 2 u s1, Finset.mem_inter.2 ⟨by simp [Eu], hx1⟩⟩
          dsimp only [g0, DickeSol.orbEmbed3]; simp only [hlt3, ↓reduceDIte]
          rcases (by omega : (Eu.1 ∩ A).card = 1 ∨ (Eu.1 ∩ A).card = 2) with h1 | h2
          · have hw : (⟨(Eu.1 ∩ A).card, hlt3⟩ : Fin 3) = 1 := Fin.ext h1
            rw [hw]; simp [DickeSol.vec3]
          · have hw : (⟨(Eu.1 ∩ A).card, hlt3⟩ : Fin 3) = 2 := Fin.ext h2
            rw [hw]; simp [DickeSol.vec3]
    rw [Finset.sum_filter]; simp_rw [hpt]; have hsum_dot : (∑ u : Fin (2 ^ (2 * n)),
      (liftSymPairReal n g0 u) ^ 2) = liftSymPairReal n g0 ⬝ᵥ liftSymPairReal n g0 :=
      (by simp [dotProduct, sq])
    rw [hsum_dot, hdot (DickeSol.vec3 (x 0) 0 0)]; simp [DickeSol.dot3, DickeSol.vec3, sq]
  · let g2 := DickeSol.orbEmbed3 (2 ^ n) 2 A (DickeSol.vec3 0 0 (x 2))
    have hpt (u : Fin (2 ^ (2 * n))) : (if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈ A then (v
      u) ^ 2 else 0) = (liftSymPairReal n g2 u) ^ 2 := by
      by_cases hdiag : addrEquiv n 2 u s0 = addrEquiv n 2 u s1
      · dsimp only [v]; rw [liftSymPairReal_diag_zero _ hdiag, liftSymPairReal_diag_zero _ hdiag]
        simp
      · dsimp only [v]; rw [liftSymPairReal_apply_offDiag _ hdiag, liftSymPairReal_apply_offDiag _
          hdiag]
        set Eu : DickeSol.P01Subset (2 ^ n) 2 :=
          ⟨{addrEquiv n 2 u s0, addrEquiv n 2 u s1}, Finset.card_pair hdiag⟩
        have hlt3 : (Eu.1 ∩ A).card < 3 :=
          DickeSol.inter_card_lt_three hmin2 Eu
        by_cases hc : addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈ A
        · rw [ite_eq_left hc]
          have hsub : Eu.1 ⊆ A := by
            intro y hy; simp only [Eu, Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact hc.1
            · exact hc.2
          have h2 : (Eu.1 ∩ A).card = 2 := (by rw [Finset.inter_eq_left.2 hsub, Eu.2])
          have hw : (⟨(Eu.1 ∩ A).card, hlt3⟩ : Fin 3) = 2 := Fin.ext h2; dsimp only [g2,
            DickeSol.orbEmbed3]; simp only [hlt3, ↓reduceDIte]; rw [hw]; simp [DickeSol.vec3]
        · rw [ite_eq_right hc]
          have hlt2 : (Eu.1 ∩ A).card < 2 := by
            by_contra hge2
            have heq2 : (Eu.1 ∩ A).card = Eu.1.card := (by rw [Eu.2]; omega); have hinter :=
              Finset.eq_of_subset_of_card_le Finset.inter_subset_left heq2.ge
            have hx0 : addrEquiv n 2 u s0 ∈ Eu.1 ∩ A := (by rw [hinter]; simp [Eu])
            have hx1 : addrEquiv n 2 u s1 ∈ Eu.1 ∩ A := (by rw [hinter]; simp [Eu])
            exact hc ⟨(Finset.mem_inter.1 hx0).2, (Finset.mem_inter.1 hx1).2⟩
          dsimp only [g2, DickeSol.orbEmbed3]; simp only [hlt3, ↓reduceDIte]
          rcases (by omega : (Eu.1 ∩ A).card = 0 ∨ (Eu.1 ∩ A).card = 1) with h0 | h1
          · have hw : (⟨(Eu.1 ∩ A).card, hlt3⟩ : Fin 3) = 0 := Fin.ext h0
            rw [hw]; simp [DickeSol.vec3]
          · have hw : (⟨(Eu.1 ∩ A).card, hlt3⟩ : Fin 3) = 1 := Fin.ext h1
            rw [hw]; simp [DickeSol.vec3]
    rw [Finset.sum_filter]; simp_rw [hpt]; have hsum_dot : (∑ u : Fin (2 ^ (2 * n)),
      (liftSymPairReal n g2 u) ^ 2) = liftSymPairReal n g2 ⬝ᵥ liftSymPairReal n g2 :=
      (by simp [dotProduct, sq])
    rw [hsum_dot, hdot (DickeSol.vec3 0 0 (x 2))]; simp [DickeSol.dot3, DickeSol.vec3, sq]
private theorem orbEmbed3_smul {N m : ℕ} (R : Finset (Fin N)) (c : ℝ) (x : Fin 3 → ℝ) :
  DickeSol.orbEmbed3 N m R (c • x) = c • DickeSol.orbEmbed3 N m R x := by
  ext E; dsimp only [DickeSol.orbEmbed3, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring
private theorem rot3Pos_smul (u : Fin 3 → ℝ) (c : ℝ) (x : Fin 3 → ℝ) : DickeSol.rot3Pos u (c • x) =
  c • DickeSol.rot3Pos u x := by
  refine DickeSol.fin3_ext ?_ ?_ ?_ <;> simp only [DickeSol.rot3Pos, DickeSol.refl3, DickeSol.zOrb3,
    DickeSol.dot3, Pi.smul_apply, smul_eq_mul, DickeSol.vec3_zero, DickeSol.vec3_one,
    DickeSol.vec3_two] <;> ring
private theorem rot3Neg_smul (u : Fin 3 → ℝ) (c : ℝ) (x : Fin 3 → ℝ) : DickeSol.rot3Neg u (c • x) =
  c • DickeSol.rot3Neg u x := by
  refine DickeSol.fin3_ext ?_ ?_ ?_ <;> simp only [DickeSol.rot3Neg, DickeSol.refl3, DickeSol.zOrb3,
    DickeSol.dot3, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, DickeSol.vec3_zero, DickeSol.vec3_one,
    DickeSol.vec3_two] <;> ring
private theorem iter_smul_vec3 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hsmul : ∀ c : ℝ, ∀ x : Fin 3 → ℝ, F
  (c • x) = c • F x) (K : ℕ) (c : ℝ) (x : Fin 3 → ℝ) : (F^[K]) (c • x) = c • (F^[K]) x := by
  induction K generalizing x with
  | zero => rfl
  | succ K ih => rw [Function.iterate_succ_apply, hsmul, ih, ← Function.iterate_succ_apply]
private noncomputable def oddPairRealR2 (n : ℕ) (A : Finset (Fin (2 ^ n)))
    (sgn : ℝ) (u : Fin (2 ^ (2 * n))) : ℝ :=
  if addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∉ A then
    sgn / √(4 * ((2 ^ n : ℝ) - 2))
  else if addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∈ A then
    -(sgn / √(4 * ((2 ^ n : ℝ) - 2)))
  else
    0
private def fin2PairEquiv (α : Type*) : (Fin 2 → α) ≃ α × α where
  toFun f := (f s0, f s1)
  invFun p i := if i = s0 then p.1 else p.2
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by cases p; rfl
private theorem oddPairRealR2_props {n : ℕ} (hn : 200 ≤ n) {A : Finset (Fin (2 ^ n))} (hA2 : A.card
  = 2) {sgn : ℝ} (hsgn : sgn ^ 2 = 1) : oddPairRealR2 n A sgn ⬝ᵥ oddPairRealR2 n A sgn = 1 ∧ (∀ u,
  addrEquiv n 2 u s0 = addrEquiv n 2 u s1 → oddPairRealR2 n A sgn u = 0) ∧ (∑ u ∈ Finset.univ.filter
  (fun u => addrEquiv n 2 u s0 ∉ A ∧ addrEquiv n 2 u s1 ∉ A), (oddPairRealR2 n A sgn u) ^ 2) = 0 ∧
  (∑ u ∈ Finset.univ.filter (fun u => addrEquiv n 2 u s0 ∈ A ∧ addrEquiv n 2 u s1 ∈ A),
  (oddPairRealR2 n A sgn u) ^ 2) = 0 := by
  obtain ⟨_, hN_ge⟩ := pow_two_200_bounds hn; have hN_cast : (2 ^ n : ℝ) = (2 : ℝ) ^ n := rfl
  have h4N2_pos : 0 < 4 * ((2 ^ n : ℝ) - 2) := (by rw [hN_cast]; linarith [hN_ge])
  have hsum_mem : (∑ x : Fin (2 ^ n), if x ∈ A then (1 : ℝ) else 0) = 2 :=
    (by rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hA2]; norm_num)
  have hsum_not : (∑ x : Fin (2 ^ n), if x ∉ A then (1 : ℝ) else 0) = (2 ^ n : ℝ) - 2 := by
    have hpt (x : Fin (2 ^ n)) : (if x ∉ A then (1 : ℝ) else 0) = 1 - (if x ∈ A then (1 : ℝ) else 0)
      := (by by_cases hx : x ∈ A <;> simp [hx]); simp_rw [hpt]; rw [Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsum_mem,
      Nat.cast_pow, Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [dotProduct]; let e := (addrEquiv n 2).trans (fin2PairEquiv (Fin (2 ^ n)))
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    have hterm (x0 x1 : Fin (2 ^ n)) : oddPairRealR2 n A sgn (e.symm (x0, x1)) * oddPairRealR2 n A
      sgn (e.symm (x0, x1)) = ((if x0 ∈ A then 1 else 0) * (if x1 ∉ A then 1 else 0) + (if x0 ∉ A
      then 1 else 0) * (if x1 ∈ A then 1 else 0)) * (1 / (4 * ((2 ^ n : ℝ) - 2))) := by
      have he0 : addrEquiv n 2 (e.symm (x0, x1)) s0 = x0 := (by simp [e, fin2PairEquiv, s0])
      have he1 : addrEquiv n 2 (e.symm (x0, x1)) s1 = x1 := (by simp [e, fin2PairEquiv, s0, s1])
      dsimp only [oddPairRealR2]; rw [he0, he1]
      have hsq : (sgn / √(4 * ((2 ^ n : ℝ) - 2))) * (sgn / √(4 * ((2 ^ n : ℝ) - 2))) = 1 / (4 * ((2
        ^ n : ℝ) - 2)) := by
        rw [div_mul_div_comm, show sgn * sgn = 1 by linarith [hsgn], Real.mul_self_sqrt h4N2_pos.le]
      by_cases h0 : x0 ∈ A <;> by_cases h1 : x1 ∈ A
      · simp [h0, h1]
      · simp only [h0, h1, not_true_eq_false, not_false_eq_true, and_self, ↓reduceIte]; rw [hsq];
          ring
      · simp only [h0, h1, not_true_eq_false, not_false_eq_true, and_self, ↓reduceIte, neg_mul_neg]
        rw [hsq]; ring
      · simp [h0, h1]
    simp_rw [hterm, ← Finset.sum_mul]
    have h2d : (∑ x0 : Fin (2 ^ n), ∑ x1 : Fin (2 ^ n), ((if x0 ∈ A then (1 : ℝ) else 0) * (if x1 ∉
      A then 1 else 0) + (if x0 ∉ A then 1 else 0) * (if x1 ∈ A then 1 else 0))) = 4 * ((2 ^ n : ℝ)
      - 2) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsum_mem, hsum_not]; ring
    rw [h2d, mul_one_div_cancel h4N2_pos.ne']
  · intro u hd; dsimp only [oddPairRealR2]; rw [hd]
    by_cases h : addrEquiv n 2 u s1 ∈ A <;> simp [h]
  · refine Finset.sum_eq_zero fun u hu => ?_
    rcases (Finset.mem_filter.1 hu).2 with ⟨h0, h1⟩; simp [oddPairRealR2, h0, h1]
  · refine Finset.sum_eq_zero fun u hu => ?_
    rcases (Finset.mem_filter.1 hu).2 with ⟨h0, h1⟩; simp [oddPairRealR2, h0, h1]
private noncomputable def diagNormVecR2 (n : ℕ) (A : Finset (Fin (2 ^ n))) (γ : ℝ)
    (u : Fin (2 ^ (2 * n))) : ℂ :=
  if addrEquiv n 2 u s0 = addrEquiv n 2 u s1 then planeVec A γ (addrEquiv n 2 u s0) else 0
private theorem dotProduct_diagNormVecR2 {n : ℕ} (hn : 200 ≤ n) {A : Finset (Fin (2 ^ n))} (hA2 :
  A.card = 2) (γ : ℝ) : star (diagNormVecR2 n A γ) ⬝ᵥ diagNormVecR2 n A γ = 1 := by
  have hN16 : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right
    (by positivity) hn)
  let e := (addrEquiv n 2).trans (fin2PairEquiv (Fin (2 ^ n)))
  dsimp only [dotProduct]; rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hrow (x0 : Fin (2 ^ n)) : (∑ x1 : Fin (2 ^ n), (star (diagNormVecR2 n A γ)) (e.symm (x0, x1))
    * diagNormVecR2 n A γ (e.symm (x0, x1))) = star (planeVec A γ x0) * planeVec A γ x0 := by
    rw [Finset.sum_eq_single x0]
    · have he0 : addrEquiv n 2 (e.symm (x0, x0)) s0 = x0 := (by simp [e, fin2PairEquiv, s0])
      have he1 : addrEquiv n 2 (e.symm (x0, x0)) s1 = x0 := (by simp [e, fin2PairEquiv, s0, s1])
      simp [diagNormVecR2, he0, he1]
    · intro x1 _ hne; have he0 : addrEquiv n 2 (e.symm (x0, x1)) s0 = x0 :=
        (by simp [e, fin2PairEquiv, s0]); have he1 : addrEquiv n 2 (e.symm (x0, x1)) s1 = x1 :=
        (by simp [e, fin2PairEquiv, s0, s1]); simp [diagNormVecR2, he0, he1, hne.symm]
    · intro habs; exact (habs (Finset.mem_univ x0)).elim
  simp_rw [hrow]; exact dotProduct_planeVec (by omega) (by omega) γ
private theorem planeVec_halfAngleSet_two {n : ℕ} (hn : 200 ≤ n) {A : Finset (Fin (2 ^ n))} (hA2 :
  A.card = 2) (x : Fin (2 ^ n)) : planeVec A (halfAngleSet n 2) x = ((1 / √(2 ^ n : ℝ) : ℝ) : ℂ) :=
  by
  obtain ⟨_, hN_ge⟩ := pow_two_200_bounds hn; have hN_cast : (2 ^ n : ℝ) = (2 : ℝ) ^ n := rfl
  have hN_pos : (0 : ℝ) < 2 ^ n := (by rw [hN_cast]; linarith [hN_ge]); have hN2_pos : (0 : ℝ) < (2
    ^ n : ℝ) - 2 := (by rw [hN_cast]; linarith [hN_ge])
  have hdiv_le1 : (2 : ℝ) / (2 ^ n : ℝ) ≤ 1 := by rw [div_le_one hN_pos, hN_cast]; linarith [hN_ge]
  have hsin : Real.sin (halfAngleSet n 2) = √((2 : ℝ) / (2 ^ n : ℝ)) := by
    dsimp only [halfAngleSet]; rw [Nat.cast_ofNat]
    have hrt0 : (0 : ℝ) ≤ √((2 : ℝ) / (2 ^ n : ℝ)) := Real.sqrt_nonneg _
    exact Real.sin_arcsin (by linarith only [hrt0]) (Real.sqrt_le_one.2 hdiv_le1)
  have hcos : Real.cos (halfAngleSet n 2) = √(((2 ^ n : ℝ) - 2) / (2 ^ n : ℝ)) := by
    dsimp only [halfAngleSet]; rw [Nat.cast_ofNat, Real.cos_arcsin]; congr 1; rw [Real.sq_sqrt
      (by positivity)]; field_simp [hN_pos.ne']
  simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hA2,
    Nat.cast_ofNat, hsin, hcos]; by_cases hx : x ∈ A
  · simp only [hx, ↓reduceIte, mul_zero, add_zero]; rw [← Complex.ofReal_mul]; congr 1
    rw [Real.sqrt_div (by norm_num)]; field_simp [show (√(2 : ℝ)) ≠ 0 by positivity]
  · simp only [hx, ↓reduceIte, mul_zero, zero_add]; rw [← Complex.ofReal_mul]
    congr 1; rw [Real.sqrt_div hN2_pos.le]; field_simp [show (√((2 ^ n : ℝ) - 2)) ≠ 0 by positivity]
private theorem cswapFilter_twoSlot_r2_outcomes {n : ℕ} (hn : 200 ≤ n) {A : Finset (Fin (2 ^ n))}
  (hA2 : A.card = 2) {betas : Fin 2 → ℝ} {γ : ℝ} (hγ_lo : halfAngleSet n 2 ≤ γ) (hγ_hi : γ ≤ 5 / 4)
  (hslots : (betas s0 = halfAngleSet n 2 ∧ betas s1 = γ) ∨ (betas s0 = γ ∧ betas s1 = halfAngleSet n
  2)) :
    let w : Fin (2 ^ 2) → ℝ := fun o =>
      if o = 0 then 1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 - 1 / (2 : ℝ) ^ n
      else if o = ⟨1,
        (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then Real.sin (γ - halfAngleSet n 2) ^ 2 / 2
      else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then 1 / (2 : ℝ) ^ n
      else 0
    let sgn : ℝ := if betas s0 = γ ∧ betas s1 = halfAngleSet n 2 then 1 else -1
    0 < w 0 ∧ DickeSol.dot3 (jp01InitOrbVec n γ) (jp01InitOrbVec n γ) = w 0 ∧ (∑ o : Fin (2 ^ 2), w
      o) = 1 ∧ (cswapFilterUnitary n).1 *ᵥ prodSlotLocalVec ![slotPairVec (planeVec A (betas s0))
      (Pi.single 0 1), slotPairVec (planeVec A (betas s1)) (Pi.single 0 1)] = ∑ o : Fin (2 ^ 2),
      ((√(w o) : ℝ) : ℂ) • (localAddrReg n 2).tensorState (if o = 0 then liftSymPairVec n
      (DickeSol.orbEmbed3 (2 ^ n) 2 A ((1 / √(w 0)) • jp01InitOrbVec n γ)) else if o = ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then fun u => ((oddPairRealR2 n A sgn u : ℝ) : ℂ)
      else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then diagNormVecR2 n A γ else 0)
      (Pi.single (envOfMask n o) 1) := by
  intro w sgn; obtain ⟨hSN_ge, hN_ge⟩ := pow_two_200_bounds hn
  set NR : ℝ := (2 : ℝ) ^ n; have hN_cast : (2 ^ n : ℝ) = NR := rfl; have hNR_pos : 0 < NR :=
    lt_of_lt_of_le (by positivity) hN_ge
  have hSN_pos : 0 < √NR := lt_of_lt_of_le (by positivity) hSN_ge; have hN2_pos : 0 < NR - 2 :=
    (by linarith [hN_ge]); have hN3_nn : 0 ≤ NR - 3 := (by linarith [hN_ge]); have hdiv_le1 : (2 :
    ℝ) / NR ≤ 1 := (by rw [div_le_one hNR_pos]; linarith [hN_ge])
  have hsin_θ2 : Real.sin (halfAngleSet n 2) = √(2 / NR) := by
    dsimp only [halfAngleSet]; rw [Nat.cast_ofNat, hN_cast]; have hrt0 : (0 : ℝ) ≤ √(2 / NR) :=
      Real.sqrt_nonneg _; exact Real.sin_arcsin (by linarith only [hrt0]) (Real.sqrt_le_one.2
      hdiv_le1)
  have hcos_θ2 : Real.cos (halfAngleSet n 2) = √((NR - 2) / NR) := by
    dsimp only [halfAngleSet]; rw [Nat.cast_ofNat, hN_cast, Real.cos_arcsin]
    congr 1; rw [Real.sq_sqrt (by positivity)]; field_simp [hNR_pos.ne']
  have hw0_pos : 0 < w 0 := by
    dsimp only [w]; simp only [↓reduceIte]
    have hs2 : Real.sin (γ - halfAngleSet n 2) ^ 2 ≤ 1 := by
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one (γ - halfAngleSet n
        2)) 2
    have hinv : 1 / NR ≤ 1 / 16 := div_le_div_of_nonneg_left zero_le_one (by norm_num) (le_trans
      (by norm_num) hN_ge); linarith only [hs2, hinv]
  have hdot_init : DickeSol.dot3 (jp01InitOrbVec n γ) (jp01InitOrbVec n γ) = w 0 := by
    dsimp only [DickeSol.dot3, jp01InitOrbVec, DickeSol.vec3, w]; simp only [Fin.isValue,
      ↓reduceIte]; rw [Real.sin_sub, hsin_θ2, hcos_θ2]; have hs3 : √((NR - 3) / NR) * √((NR - 3) /
      NR) = (NR - 3) / NR := Real.mul_self_sqrt (div_nonneg hN3_nn hNR_pos.le); have hs2 : √((NR -
      2) / NR) * √((NR - 2) / NR) = (NR - 2) / NR := Real.mul_self_sqrt (div_nonneg hN2_pos.le
      hNR_pos.le); have h2N : √(2 / NR) * √(2 / NR) = 2 / NR := Real.mul_self_sqrt (div_nonneg
      (by norm_num) hNR_pos.le); have hsq2 : (√(2 : ℝ)) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsqN : √NR * √NR = NR := Real.mul_self_sqrt hNR_pos.le
    have hcross : √((NR - 2) / NR) / √2 / √NR = √(2 / NR) * √((NR - 2) / NR) / 2 := by
      rw [Real.sqrt_div hN2_pos.le, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [hSN_pos.ne', show (√(2 : ℝ)) ≠ 0 by positivity]; ring_nf; rw [Real.sq_sqrt
        (by norm_num : (0 : ℝ) ≤ 2)]
    have hc_id := Real.sin_sq_add_cos_sq γ
    calc (√((NR - 3) / NR) * Real.cos γ) * (√((NR - 3) / NR) * Real.cos γ) +
          (√((NR - 2) / NR) * (Real.sin γ / √2) + Real.cos γ / √NR) *
            (√((NR - 2) / NR) * (Real.sin γ / √2) + Real.cos γ / √NR) +
          Real.sin γ / √NR * (Real.sin γ / √NR)
        = (√((NR - 3) / NR) * √((NR - 3) / NR)) * Real.cos γ ^ 2 +
          (√((NR - 2) / NR) * √((NR - 2) / NR)) * (Real.sin γ ^ 2 / (√2 * √2)) +
          2 * (√((NR - 2) / NR) / √2 / √NR) * Real.sin γ * Real.cos γ +
          Real.cos γ ^ 2 / (√NR * √NR) + Real.sin γ ^ 2 / (√NR * √NR) := by ring
      _ = ((NR - 3) / NR) * Real.cos γ ^ 2 + ((NR - 2) / NR) * (Real.sin γ ^ 2 / 2) +
          2 * (√(2 / NR) * √((NR - 2) / NR) / 2) * Real.sin γ * Real.cos γ +
          Real.cos γ ^ 2 / NR + Real.sin γ ^ 2 / NR := by rw [hs3, hs2, hsq2, hsqN, hcross]
      _ = (Real.sin γ ^ 2 + Real.cos γ ^ 2) -
          ((Real.sin γ ^ 2 * ((NR - 2) / NR) -
            2 * Real.sin γ * Real.cos γ * √(2 / NR) * √((NR - 2) / NR) +
            Real.cos γ ^ 2 * (2 / NR)) / 2) -
          (Real.sin γ ^ 2 + Real.cos γ ^ 2) / NR := by field_simp [hNR_pos.ne']; ring
      _ = 1 - (Real.sin γ * √((NR - 2) / NR) - Real.cos γ * √(2 / NR)) ^ 2 / 2 - 1 / NR := by
          rw [hc_id]; have hsq_diff : (Real.sin γ * √((NR - 2) / NR) - Real.cos γ * √(2 / NR)) ^ 2 =
            Real.sin γ ^ 2 * (√((NR - 2) / NR) * √((NR - 2) / NR)) - 2 * Real.sin γ * Real.cos γ *
            √(2 / NR) * √((NR - 2) / NR) + Real.cos γ ^ 2 * (√(2 / NR) * √(2 / NR)) := (by ring)
          rw [hsq_diff, hs2, h2N]
  have hw_sum : (∑ o : Fin (2 ^ 2), w o) = 1 := by
    have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2
      ^ 2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^
      2)⟩} := (by ext x; fin_cases x <;> simp); rw [huniv4, Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    dsimp only [w]
    simp only [
      show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
      show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
      show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
        (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
      show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
      show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
        (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
      show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
        (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp, ↓reduceIte]; ring
  refine ⟨hw0_pos, hdot_init, hw_sum, ?_⟩; rw [prodSlotLocalVec_zero_flags_eq_tensorState, ←
    envOfMask_zero n, cswapFilterUnitary_mulVec_zero]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← (localAddrReg n 2).tensorState_smul_left]; congr 1
  have ho_cases : o = 0 ∨ o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2,
    (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨ o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ :=
    (by fin_cases o <;> simp)
  have hprod_sym (u : Fin (2 ^ (2 * n))) : planeVec A (betas s0) (addrEquiv n 2 u s0) * planeVec A
    (betas s1) (addrEquiv n 2 u s1) + planeVec A (betas s0) (addrEquiv n 2 u s1) * planeVec A (betas
    s1) (addrEquiv n 2 u s0) = ((1 / √NR : ℝ) : ℂ) * (planeVec A γ (addrEquiv n 2 u s0) + planeVec A
    γ (addrEquiv n 2 u s1)) := by
    rcases hslots with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · rw [hb0, hb1, planeVec_halfAngleSet_two hn hA2, planeVec_halfAngleSet_two hn hA2, hN_cast]
      ring
    · rw [hb0, hb1, planeVec_halfAngleSet_two hn hA2, planeVec_halfAngleSet_two hn hA2, hN_cast]
      ring
  have hprod_diag (u : Fin (2 ^ (2 * n))) (hd : addrEquiv n 2 u s0 = addrEquiv n 2 u s1) : planeVec
    A (betas s0) (addrEquiv n 2 u s0) * planeVec A (betas s1) (addrEquiv n 2 u s1) = ((1 / √NR : ℝ)
    : ℂ) * planeVec A γ (addrEquiv n 2 u s0) := by
    rw [← hd]; rcases hslots with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · rw [hb0, hb1, planeVec_halfAngleSet_two hn hA2, hN_cast]
    · rw [hb0, hb1, planeVec_halfAngleSet_two hn hA2, hN_cast]; ring
  rcases ho_cases with rfl | rfl | rfl | rfl
  · simp only [↓reduceIte, w]
    have hsmul_cancel : ((√(1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 - 1 / NR) : ℝ) : ℂ) •
      liftSymPairVec n (DickeSol.orbEmbed3 (2 ^ n) 2 A ((1 / √(1 - Real.sin (γ - halfAngleSet n 2) ^
      2 / 2 - 1 / NR)) • jp01InitOrbVec n γ)) = liftSymPairVec n (DickeSol.orbEmbed3 (2 ^ n) 2 A
      (jp01InitOrbVec n γ)) := by
      have hw0_pos' : 0 < 1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 - 1 / NR := hw0_pos
      rw [orbEmbed3_smul]; funext u; dsimp only [liftSymPairVec, liftSymPairReal, Pi.smul_apply,
        smul_eq_mul]; rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, ←
        mul_assoc, ← Complex.ofReal_mul, mul_one_div_cancel (Real.sqrt_ne_zero'.2 hw0_pos'),
        Complex.ofReal_one, one_mul]
    change _ = ((√(1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 - 1 / NR) : ℝ) : ℂ) • liftSymPairVec
      n (DickeSol.orbEmbed3 (2 ^ n) 2 A ((1 / √(1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 - 1 /
      NR)) • jp01InitOrbVec n γ)); rw [hsmul_cancel]; funext u; by_cases hd : addrEquiv n 2 u s0 =
      addrEquiv n 2 u s1
    · rw [swapAddrPerm_eq_self_of_diag hd]; dsimp only [liftSymPairVec]
      rw [liftSymPairReal_diag_zero _ hd]; simp [hd]
    · have hd' : addrEquiv n 2 u s1 ≠ addrEquiv n 2 u s0 := Ne.symm hd
      simp only [addrEquiv_swapAddrPerm_s0, addrEquiv_swapAddrPerm_s1, hd, hd', ↓reduceIte]
      rw [hprod_sym u]; dsimp only [liftSymPairVec]; rw [liftSymPairReal_apply_offDiag _ hd]
      set Eu : DickeSol.P01Subset (2 ^ n) 2 := ⟨{addrEquiv n 2 u s0, addrEquiv n 2 u s1},
        Finset.card_pair hd⟩
      have hN16 : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right
        (by positivity) hn); have hmin2 : min 2 A.card ≤ 2 := Nat.min_le_left 2 A.card
      have hlt3 : (Eu.1 ∩ A).card < 3 := DickeSol.inter_card_lt_three hmin2 Eu
      dsimp only [DickeSol.orbEmbed3]; simp only [hlt3, ↓reduceDIte]; simp only [planeVec,
        unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hA2, Nat.cast_ofNat,
        hN_cast]; have hsub2_cast : ((2 ^ n - 2 : ℕ) : ℝ) = NR - 2 :=
        (by rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ n)]; push_cast; rfl)
      by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A
      · have hsub : Eu.1 ⊆ A := by
          intro y hy; simp only [Eu, Finset.mem_insert, Finset.mem_singleton] at hy; rcases hy with
            rfl | rfl <;> assumption
        have hc2 : (Eu.1 ∩ A).card = 2 := (by rw [Finset.inter_eq_left.2 hsub, Eu.2])
        have hw : (⟨(Eu.1 ∩ A).card, hlt3⟩ : Fin 3) = 2 := Fin.ext hc2
        have horb2 : (DickeSol.orbCard (2 ^ n) 2 2 2 : ℝ) = 1 :=
          (by unfold DickeSol.orbCard; norm_num); rw [hw, hc2, horb2]; simp only [hx0, hx1,
          ↓reduceIte, mul_zero, add_zero, jp01InitOrbVec, DickeSol.vec3, Fin.isValue, hN_cast,
          Real.sqrt_one, div_one]; push_cast; ring
      · have hi : Eu.1 ∩ A = {addrEquiv n 2 u s0} := by
          ext y; simp only [Eu, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun ⟨h, hyA⟩ => h.resolve_right (fun h1 => hx1 (h1 ▸ hyA)), fun hy => ⟨Or.inl hy,
            hy.symm ▸ hx0⟩⟩
        have hc1 : (Eu.1 ∩ A).card = 1 := (by rw [hi, Finset.card_singleton]); have hw : (⟨(Eu.1 ∩
          A).card, hlt3⟩ : Fin 3) = 1 := Fin.ext hc1
        have horb1 : (DickeSol.orbCard (2 ^ n) 2 2 1 : ℝ) = 2 * (NR - 2) := by
          unfold DickeSol.orbCard; rw [show (2 : ℕ).choose 1 = 2 from rfl, Nat.choose_one_right,
            Nat.cast_mul, Nat.cast_ofNat, hsub2_cast]
        rw [hw, hc1, horb1]; simp only [hx0, hx1, ↓reduceIte, mul_zero, add_zero, zero_add,
          jp01InitOrbVec, DickeSol.vec3, Fin.isValue, hN_cast]
        have hrad1 : (1 / √(2 : ℝ)) * ((√((NR - 2) / NR) * (Real.sin γ / √2) + Real.cos γ / √NR) /
          √(2 * (NR - 2))) = (1 / 2) * ((1 / √NR) * (Real.sin γ * (1 / √2) + Real.cos γ * (1 / √(NR
          - 2)))) := by
          rw [Real.sqrt_div hN2_pos.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp [hSN_pos.ne', show (√(2 : ℝ)) ≠ 0 by positivity,
            show (√(NR - 2)) ≠ 0 by positivity]; ring_nf
          rw [show (√2 : ℝ) ^ 3 = (√2) ^ 2 * √2 by ring, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
        exact_mod_cast hrad1.symm
      · have hi : Eu.1 ∩ A = {addrEquiv n 2 u s1} := by
          ext y; simp only [Eu, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun ⟨h, hyA⟩ => h.resolve_left (fun h0 => hx0 (h0 ▸ hyA)), fun hy => ⟨Or.inr hy,
            hy.symm ▸ hx1⟩⟩
        have hc1 : (Eu.1 ∩ A).card = 1 := (by rw [hi, Finset.card_singleton]); have hw : (⟨(Eu.1 ∩
          A).card, hlt3⟩ : Fin 3) = 1 := Fin.ext hc1
        have horb1 : (DickeSol.orbCard (2 ^ n) 2 2 1 : ℝ) = 2 * (NR - 2) := by
          unfold DickeSol.orbCard; rw [show (2 : ℕ).choose 1 = 2 from rfl, Nat.choose_one_right,
            Nat.cast_mul, Nat.cast_ofNat, hsub2_cast]
        rw [hw, hc1, horb1]; simp only [hx0, hx1, ↓reduceIte, mul_zero, add_zero, zero_add,
          jp01InitOrbVec, DickeSol.vec3, Fin.isValue, hN_cast]
        have hrad1 : (1 / √(2 : ℝ)) * ((√((NR - 2) / NR) * (Real.sin γ / √2) + Real.cos γ / √NR) /
          √(2 * (NR - 2))) = (1 / 2) * ((1 / √NR) * (Real.cos γ * (1 / √(NR - 2)) + Real.sin γ * (1
          / √2))) := by
          rw [Real.sqrt_div hN2_pos.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp [hSN_pos.ne', show (√(2 : ℝ)) ≠ 0 by positivity,
            show (√(NR - 2)) ≠ 0 by positivity]; ring_nf
          rw [show (√2 : ℝ) ^ 3 = (√2) ^ 2 * √2 by ring, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
        exact_mod_cast hrad1.symm
      · have hc0 : (Eu.1 ∩ A).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]; intro y hy; simp only [Eu,
            Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hy; rcases hy with ⟨rfl |
            rfl, hyA⟩
          · exact hx0 hyA
          · exact hx1 hyA
        have hw : (⟨(Eu.1 ∩ A).card, hlt3⟩ : Fin 3) = 0 := Fin.ext hc0
        have horb0 : (DickeSol.orbCard (2 ^ n) 2 2 0 : ℝ) = (NR - 2) * (NR - 3) / 2 := by
          unfold DickeSol.orbCard; rw [Nat.choose_zero_right, one_mul]; have hch2 :=
            nat_choose_two_real (by omega : 2 ≤ 2 ^ n - 2); rw [hch2, hsub2_cast]; ring
        rw [hw, hc0, horb0]; simp only [hx0, hx1, ↓reduceIte, mul_zero, zero_add, jp01InitOrbVec,
          DickeSol.vec3, Fin.isValue, hN_cast]; have hN3_pos : 0 < NR - 3 :=
          (by linarith only [hN_ge])
        have hrad0 : (1 / √(2 : ℝ)) * ((√((NR - 3) / NR) * Real.cos γ) / √((NR - 2) * (NR - 3) / 2))
          = (1 / 2) * ((1 / √NR) * (Real.cos γ * (1 / √(NR - 2)) + Real.cos γ * (1 / √(NR - 2))))
          := by
          rw [Real.sqrt_div hN3_nn, Real.sqrt_div (mul_nonneg hN2_pos.le hN3_nn), Real.sqrt_mul
            hN2_pos.le]
          field_simp [hSN_pos.ne', show (√(2 : ℝ)) ≠ 0 by positivity,
            show (√(NR - 2)) ≠ 0 by positivity, show (√(NR - 3)) ≠ 0 by positivity]; ring
        exact_mod_cast hrad0.symm
  · simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
      ↓reduceIte, w]
    have hθ2_nn : 0 ≤ halfAngleSet n 2 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
    have hdiff_nn : 0 ≤ Real.sin (γ - halfAngleSet n 2) := Real.sin_nonneg_of_nonneg_of_le_pi
      (sub_nonneg.2 hγ_lo) (by linarith only [hγ_hi, Real.pi_gt_three, hθ2_nn])
    have hsqrt_w1 : √(Real.sin (γ - halfAngleSet n 2) ^ 2 / 2) = Real.sin (γ - halfAngleSet n 2) /
      √2 := (by rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hdiff_nn])
    have hcoef_anti : (Real.sin (γ - halfAngleSet n 2) / √2) / √(4 * (NR - 2)) = (1 / 2) * ((1 /
      √NR) * (Real.sin γ / √2 - Real.cos γ / √(NR - 2))) := by
      rw [Real.sin_sub, hsin_θ2, hcos_θ2, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_div hN2_pos.le,
        show √(4 * (NR - 2)) = 2 * √(NR - 2) by
          rw [Real.sqrt_mul (by norm_num), show √(4 : ℝ) = 2 by norm_num]]
      field_simp [hSN_pos.ne', show (√(2 : ℝ)) ≠ 0 by positivity,
        show (√(NR - 2)) ≠ 0 by positivity]
    have hp_mem {y : Fin (2 ^ n)} (hy : y ∈ A) : planeVec A γ y = (Real.sin γ : ℂ) * ((1 / √2 : ℝ) :
      ℂ) := by
      simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hy,
        ↓reduceIte, mul_zero, add_zero, hA2, Nat.cast_ofNat]
    have hp_not {y : Fin (2 ^ n)} (hy : y ∉ A) : planeVec A γ y = (Real.cos γ : ℂ) * ((1 / √(NR - 2)
      : ℝ) : ℂ) := by
      simp only [planeVec, unifSetVec, unifComplVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hy,
        ↓reduceIte, mul_zero, zero_add, hA2, Nat.cast_ofNat, hN_cast]
    have hcoef_c : ((Real.sin (γ - halfAngleSet n 2) / √2 : ℝ) : ℂ) * ((1 / √(4 * (NR - 2)) : ℝ) :
      ℂ) = ((1 / 2 : ℝ) : ℂ) * (((1 / √NR : ℝ) : ℂ) * ((Real.sin γ : ℂ) * ((1 / √2 : ℝ) : ℂ) -
      (Real.cos γ : ℂ) * ((1 / √(NR - 2) : ℝ) : ℂ))) :=
      (by rw [← Complex.ofReal_mul, mul_one_div, hcoef_anti]; push_cast; ring); funext u
    dsimp only [Pi.smul_apply, smul_eq_mul]; rw [hsqrt_w1]; by_cases hd : addrEquiv n 2 u s0 =
      addrEquiv n 2 u s1
    · rw [swapAddrPerm_eq_self_of_diag hd, oddPairRealR2]; by_cases hx : addrEquiv n 2 u s1 ∈ A <;>
        simp [hd, hx]
    · have hd' : addrEquiv n 2 u s1 ≠ addrEquiv n 2 u s0 := Ne.symm hd
      simp only [addrEquiv_swapAddrPerm_s0, addrEquiv_swapAddrPerm_s1, hd, hd', ↓reduceIte]
      dsimp only [oddPairRealR2, sgn]
      have hsgn_split : (betas s0 = γ ∧ betas s1 = halfAngleSet n 2) ∨ (¬ (betas s0 = γ ∧ betas s1 =
        halfAngleSet n 2) ∧ betas s0 = halfAngleSet n 2 ∧ betas s1 = γ) := by
        by_cases hc : betas s0 = γ ∧ betas s1 = halfAngleSet n 2
        · exact Or.inl hc
        · exact Or.inr ⟨hc, hslots.resolve_right hc⟩
      rcases hsgn_split with ⟨hb0, hb1⟩ | ⟨hnc, hb0, hb1⟩
      · simp only [hb0, hb1, and_self, ↓reduceIte]; rw [planeVec_halfAngleSet_two hn hA2,
          planeVec_halfAngleSet_two hn hA2, hN_cast]; by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;>
          by_cases hx1 : addrEquiv n 2 u s1 ∈ A
        · rw [hp_mem hx0, hp_mem hx1, ite_eq_right (fun h => h.2 hx1), ite_eq_right (fun h => h.1
            hx0), Complex.ofReal_zero]; push_cast; ring
        · rw [hp_mem hx0, hp_not hx1, ite_eq_left ⟨hx0, hx1⟩, hcoef_c]; push_cast; ring
        · rw [hp_not hx0, hp_mem hx1, ite_eq_right (fun h => hx0 h.1), ite_eq_left ⟨hx0, hx1⟩,
            Complex.ofReal_neg, mul_neg, hcoef_c]; push_cast; ring
        · rw [hp_not hx0, hp_not hx1, ite_eq_right (fun h => hx0 h.1), ite_eq_right (fun h => hx1
            h.2), Complex.ofReal_zero]; push_cast; ring
      · rw [ite_eq_right hnc, hb0, hb1, planeVec_halfAngleSet_two hn hA2, planeVec_halfAngleSet_two
          hn hA2, hN_cast]
        by_cases hx0 : addrEquiv n 2 u s0 ∈ A <;> by_cases hx1 : addrEquiv n 2 u s1 ∈ A
        · rw [hp_mem hx1, hp_mem hx0, ite_eq_right (fun h => h.2 hx1), ite_eq_right (fun h => h.1
            hx0), Complex.ofReal_zero]; push_cast; ring
        · rw [hp_not hx1, hp_mem hx0, ite_eq_left ⟨hx0, hx1⟩, neg_div, Complex.ofReal_neg, mul_neg,
            hcoef_c]; push_cast; ring
        · rw [hp_mem hx1, hp_not hx0, ite_eq_right (fun h => hx0 h.1), ite_eq_left ⟨hx0, hx1⟩,
            neg_div, neg_neg, hcoef_c]; push_cast; ring
        · rw [hp_not hx1, hp_not hx0, ite_eq_right (fun h => hx0 h.1), ite_eq_right (fun h => hx1
            h.2), Complex.ofReal_zero]; push_cast; ring
  · simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
      show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
        (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte, w]
    have hsq_inv : √(1 / NR) = 1 / √NR := (by rw [Real.sqrt_div zero_le_one, Real.sqrt_one])
    funext u; dsimp only [diagNormVecR2, Pi.smul_apply, smul_eq_mul]; rw [hsq_inv]
    by_cases hd : addrEquiv n 2 u s0 = addrEquiv n 2 u s1
    · rw [ite_eq_left hd, ite_eq_left hd, hprod_diag u hd]
    · rw [ite_eq_right hd, ite_eq_right hd, mul_zero]
  · simp [w]
private noncomputable def jp01CoreBodyCircuit {Var : Type} (res : Var) (n k : ℕ) (hn : 200 ≤ n) (T :
    Finset (Fin (2 ^ n))) (K1 K2 : ℕ) (cont0 : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2
    k)) Var (findAllQubits n 2 k) ((n + 1) * 2)) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits
    n 2 k)) Var (findAllQubits n 2 k) ((n + 1) * 2) :=
  let U1 := liftSymPairOrthogonal n (DickeSol.r1SymMat (2 ^ n) 2) (r1SymMat_orth hn)
  let U2 := liftSymPairOrthogonal n (DickeSol.r01SymMat (2 ^ n) 2) (r01SymMat_orth hn)
  .seq (.step (phaseI ((oracleReg n 2 k).embedUnitary (cswapFilterUnitary n))))
    (.seq (.measure res (allMarkersReg n 2 k))
      (dispBits res 2 0 fun oVal =>
        let o : Fin (2 ^ 2) := ⟨oVal % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩
        if o = 0 then
          .seq (jp01WalkRec n k U1 T K1)
            (.seq (jp01WalkRec n k U2 T K2)
              (jp01ReadoutCircuit res n k T cont0))
        else if o = ⟨1, by omega⟩ then
          .seq (.step (phaseI
              ((oracleReg n 2 k).embedUnitary (permutationUnitary (flipFlag0Perm n)))))
            (jp01ReadoutCircuit res n k T cont0)
        else if o = ⟨2, by omega⟩ then
          .seq (resetRegCircuit res (oracleReg n 2 k))
            (fallbackCleanR2Circuit res n k T)
        else
          .skip))
private theorem jp01CoreBody_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn :
  200 ≤ n) (hk1024 : k ≤ 1024) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA2
  : (S \ T).card = 2) {betas : Fin 2 → ℝ} {γ : ℝ} (hγ_lo : halfAngleSet n 2 ≤ γ) (hγ_hi : γ ≤ 5 / 4)
  (hslots : (betas s0 = halfAngleSet n 2 ∧ betas s1 = γ) ∨ (betas s0 = γ ∧ betas s1 = halfAngleSet n
  2)) (K1 K2 : ℕ) {B0 : ℝ} (hB0_nn : 0 ≤ B0) {cont0 : OracleDynamicCircuit (Unitary (2 ^
  findAllQubits n 2 k)) Var (findAllQubits n 2 k) ((n + 1) * 2)} (hcont0 : ∀ Υ : CQState (Store Var)
    (2 ^
  findAllQubits n 2 k), PureStateAt (Pi.single 0 1) Υ → 𝔼[(interp (cont0.compile QProg.qAssign
  (parallelMarkingOracle 2 S))).toStateFun Υ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res)
  = S)] = Υ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S))
  (cont0.compile QProg.qAssign (parallelMarkingOracle 2 S)) Υ ≤ (Υ.trace : ℝ≥0∞) *
  ENNReal.ofReal B0) {Δ
  : CQState (Store Var) (2 ^ findAllQubits n 2 k)} (hΔ : PureStateAt (prodSlotState n 2 k fun i =>
  slotPairVec (planeVec (S \ T) (betas i)) (Pi.single 0 1)) Δ) :
    let u1 := DickeSol.u1OrbVec (2 ^ n) 2 2; let u2 := DickeSol.u2OrbVec (2 ^ n) 2 2
    let y := ((DickeSol.rot3Neg u2)^[K2]) (((DickeSol.rot3Pos u1)^[K1]) (jp01InitOrbVec n γ))
    let zh := ((cswapZeroHitNat : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)
    let prog := (jp01CoreBodyCircuit res n k hn T K1 K2 cont0).compile QProg.qAssign
      (parallelMarkingOracle 2 S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal ((1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2) *
      ((K1 + K2 : ℕ) : ℝ) + 2 + (1 - (y 2) ^ 2 - (y 0) ^ 2) * zh + (y 0) ^ 2 * B0) := by
  intro u1 u2 y zh prog; set A := S \ T; let oracleS := parallelMarkingOracle 2 S
  let modelS := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracleS
  have horacleS := isRealMatrix_parallelMarkingOracle (m := 2) S
  let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ :=
    Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 1
  obtain ⟨hSN_ge, _⟩ := pow_two_200_bounds hn
  have hN16 : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right
    (by positivity) hn); have hmrN : 2 + A.card < 2 ^ n := (by omega); have h2mN : 2 * 2 < 2 ^ n :=
    (by omega); have hmin2 : min 2 A.card ≤ 2 := Nat.min_le_left 2 A.card; obtain ⟨hdu1, hdu2, -, -,
    -, -, -⟩ := jp01_m2r2_basis_closed hN16
  let Ucswap := (oracleReg n 2 k).embedUnitary (cswapFilterUnitary n)
  set Δu := (interp ((OracleDynamicCircuit.step (phaseI Ucswap)).compile QProg.qAssign
    oracleS)).toStateFun Δ
  have hΔu_eq : Δu = CQState.qAssign Ucswap Δ := by
    dsimp only [Δu]; rw [OracleDynamicCircuit.compile_step, interp_qAssign]
    exact cqState_qAssign_phaseI Ucswap Δ
  let ψ_in := prodSlotState n 2 k fun i => slotPairVec (planeVec A (betas i)) (Pi.single 0 1)
  have hψ_in : star ψ_in ⬝ᵥ ψ_in = 1 :=
    dotProduct_prodSlotState fun i =>
      dotProduct_slotPairVec (dotProduct_planeVec (by omega) (by omega) (betas i))
        (dotProduct_single_one 0)
  obtain ⟨hPu, htr_u⟩ := pureStateAt_qAssign Ucswap hψ_in hΔ; rw [← hΔu_eq] at hPu htr_u
  let ψ_u := Ucswap.1 *ᵥ ψ_in
  have hψ_u : star ψ_u ⬝ᵥ ψ_u = 1 := dotProduct_unitary_mulVec Ucswap hψ_in
  let w : Fin (2 ^ 2) → ℝ := fun o =>
    if o = 0 then 1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 - 1 / (2 : ℝ) ^ n
    else if o = ⟨1,
      (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then Real.sin (γ - halfAngleSet n 2) ^ 2 / 2
    else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then 1 / (2 : ℝ) ^ n
    else 0
  let sgn : ℝ := if betas s0 = γ ∧ betas s1 = halfAngleSet n 2 then 1 else -1
  have hsgn_sq : sgn ^ 2 = 1 := (by dsimp only [sgn]; split_ifs <;> norm_num)
  obtain ⟨hw0_pos_raw, hdot_init_raw, hw_sum_raw, hcswap_out_raw⟩ := cswapFilter_twoSlot_r2_outcomes
    hn hA2 hγ_lo hγ_hi hslots; have hw0_pos : 0 < w 0 := hw0_pos_raw
  have hdot_init : DickeSol.dot3 (jp01InitOrbVec n γ) (jp01InitOrbVec n γ) = w 0 := hdot_init_raw
  have hw_sum : (∑ o : Fin (2 ^ 2), w o) = 1 := hw_sum_raw
  have hw_nn (o : Fin (2 ^ 2)) : 0 ≤ w o := by
    dsimp only [w]; split_ifs
    · exact hw0_pos.le
    · positivity
    · positivity
    · exact le_rfl
  let x_norm := (1 / √(w 0)) • jp01InitOrbVec n γ
  have hcswap_out : (cswapFilterUnitary n).1 *ᵥ prodSlotLocalVec ![slotPairVec (planeVec A (betas
    s0)) (Pi.single 0 1), slotPairVec (planeVec A (betas s1)) (Pi.single 0 1)] = ∑ o : Fin (2 ^ 2),
    ((√(w o) : ℝ) : ℂ) • (localAddrReg n 2).tensorState (if o = 0 then liftSymPairVec n
    (DickeSol.orbEmbed3 (2 ^ n) 2 A x_norm) else if o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩
    then fun u => ((oddPairRealR2 n A sgn u : ℝ) : ℂ) else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2
    < 2 ^ 2)⟩ then diagNormVecR2 n A γ else 0) (Pi.single (envOfMask n o) 1) := hcswap_out_raw
  have hx_norm : DickeSol.dot3 x_norm x_norm = 1 := by
    have hmul : DickeSol.dot3 x_norm x_norm = (1 / √(w 0)) ^ 2 * DickeSol.dot3 (jp01InitOrbVec n γ)
      (jp01InitOrbVec n γ) :=
      (by dsimp only [x_norm, DickeSol.dot3, Pi.smul_apply, smul_eq_mul]; ring); rw [hmul,
      hdot_init, div_pow, one_pow, Real.sq_sqrt hw0_pos.le]; exact one_div_mul_cancel hw0_pos.ne'
  let ψ_out : Fin (2 ^ 2) → Fin (2 ^ findAllQubits n 2 k) → ℂ := fun o =>
    if o = 0 then
      (oracleReg n 2 k).tensorState
        ((localAddrReg n 2).tensorState
          (liftSymPairVec n (DickeSol.orbEmbed3 (2 ^ n) 2 A x_norm)) (Pi.single 0 1)) env0
    else if o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then
      (oracleReg n 2 k).tensorState
        ((localAddrReg n 2).tensorState
          (fun u => ((oddPairRealR2 n A sgn u : ℝ) : ℂ)) (Pi.single (envOfMask n ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩) 1))
        env0
    else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then
      (oracleReg n 2 k).tensorState
        ((localAddrReg n 2).tensorState (diagNormVecR2 n A γ)
          (Pi.single (envOfMask n ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩) 1)) env0
    else ψ_in
  obtain ⟨hodd_norm, hodd_off, hodd_p0, hodd_p2⟩ := oddPairRealR2_props hn hA2 hsgn_sq
  have hψ_out (o : Fin (2 ^ 2)) : star (ψ_out o) ⬝ᵥ ψ_out o = 1 := by
    dsimp only [ψ_out]; by_cases h0 : o = 0
    · rw [ite_eq_left h0, dotProduct_tensorState, dotProduct_tensorState, dotProduct_liftSymPairVec]
      obtain ⟨horb, -, -⟩ := orbEmbed3_filter_zero_two_sq hn hA2 x_norm
      rw [dotProduct_liftSymPairReal] at horb; rw [horb, hx_norm, Complex.ofReal_one,
        dotProduct_env_single, dotProduct_env_single, mul_one, mul_one]
    · rw [ite_eq_right h0]; by_cases h1 : o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩
      · rw [ite_eq_left h1, dotProduct_tensorState, dotProduct_tensorState, dotProduct_env_single,
          dotProduct_env_single, mul_one, mul_one]
        have hc : star (fun u => ((oddPairRealR2 n A sgn u : ℝ) : ℂ)) ⬝ᵥ (fun u => ((oddPairRealR2 n
          A sgn u : ℝ) : ℂ)) = 1 := by
          have hr : ((oddPairRealR2 n A sgn ⬝ᵥ oddPairRealR2 n A sgn : ℝ) : ℂ) = 1 :=
            (by rw [hodd_norm, Complex.ofReal_one]); rw [← hr]; simp [dotProduct,
            Complex.ofReal_sum, Complex.ofReal_mul]
        exact hc
      · rw [ite_eq_right h1]; by_cases h2 : o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩
        · rw [ite_eq_left h2, dotProduct_tensorState, dotProduct_tensorState,
            dotProduct_diagNormVecR2 hn hA2 γ, dotProduct_env_single, dotProduct_env_single,
            mul_one, mul_one]
        · rw [ite_eq_right h2]; exact hψ_in
  have hproj (o : Fin (2 ^ 2)) : (allMarkersReg n 2 k).basisOutcomeProjector o *ᵥ ψ_u = ((√(w o) :
    ℝ) : ℂ) • ψ_out o := by
    have hslot_fn : (fun i : Fin 2 => slotPairVec (planeVec A (betas i)) (Pi.single 0 1)) =
      ![slotPairVec (planeVec A (betas s0)) (Pi.single 0 1), slotPairVec (planeVec A (betas s1))
      (Pi.single 0 1)] := (by funext i; fin_cases i <;> rfl)
    have hψu_eq : ψ_u = (oracleReg n 2 k).tensorState ((cswapFilterUnitary n).1 *ᵥ prodSlotLocalVec
      ![slotPairVec (planeVec A (betas s0)) (Pi.single 0 1), slotPairVec (planeVec A (betas s1))
      (Pi.single 0 1)]) env0 := by
      dsimp only [ψ_u, Ucswap, ψ_in, prodSlotState]; rw [hslot_fn, QRegister.embedUnitary_val,
        (oracleReg n 2 k).embedMatrix_mulVec_tensorState]
    rw [hψu_eq, hcswap_out]; have hsmul_pull :
        (∑ m : Fin (2 ^ 2), ((√(w m) : ℝ) : ℂ) • (localAddrReg n 2).tensorState
              (if m = 0 then liftSymPairVec n (DickeSol.orbEmbed3 (2 ^ n) 2 A x_norm)
               else if m = ⟨1,
                 (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then fun u => ((oddPairRealR2 n A sgn u :
                 ℝ) : ℂ)
               else if m = ⟨2,
                 (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then diagNormVecR2 n A γ else 0)
              (Pi.single (envOfMask n m) 1)) =
        ∑ m : Fin (2 ^ 2), (localAddrReg n 2).tensorState
            (((√(w m) : ℝ) : ℂ) •
              (if m = 0 then liftSymPairVec n (DickeSol.orbEmbed3 (2 ^ n) 2 A x_norm)
               else if m = ⟨1,
                 (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then fun u => ((oddPairRealR2 n A sgn u :
                 ℝ) : ℂ)
               else if m = ⟨2,
                 (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then diagNormVecR2 n A γ else 0))
            (Pi.single (envOfMask n m) 1) :=
      Finset.sum_congr rfl fun m _ => ((localAddrReg n 2).tensorState_smul_left _ _ _).symm
    rw [hsmul_pull, basisOutcomeProjector_allMarkers_oracle_tensorState]
    have ho_cases : o = 0 ∨ o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨ o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ :=
      (by fin_cases o <;> simp); rcases ho_cases with rfl | rfl | rfl | rfl
    · simp only [↓reduceIte, w, ψ_out, envOfMask_zero]; rw [(localAddrReg n
        2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
    · simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        ↓reduceIte, w, ψ_out]
      rw [(localAddrReg n 2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
    · simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
          (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte, w, ψ_out]
      rw [(localAddrReg n 2).tensorState_smul_left, (oracleReg n 2 k).tensorState_smul_left]
    · simp only [show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
          (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
        show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
          (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp, ↓reduceIte, w,
        Real.sqrt_zero, Complex.ofReal_zero, zero_smul]; funext z; simp [QRegister.tensorState]
  set Δm := (interp (QProg.measureRegister res (allMarkersReg n 2 k))).toStateFun Δu; have hmeas :=
    measure_sliceState_of_pureStateAt res (allMarkersReg n 2 k) hψ_u w hw_nn ψ_out hψ_out hproj hPu
  let U1 := liftSymPairOrthogonal n (DickeSol.r1SymMat (2 ^ n) 2) (r1SymMat_orth hn)
  let U2 := liftSymPairOrthogonal n (DickeSol.r01SymMat (2 ^ n) 2) (r01SymMat_orth hn)
  let branchCirc (o : Fin (2 ^ 2)) := if o = 0 then OracleDynamicCircuit.seq (jp01WalkRec n k U1 T
    K1) (.seq (jp01WalkRec n k U2 T K2) (jp01ReadoutCircuit res n k T cont0)) else if o = ⟨1,
    (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ then .seq (.step (phaseI ((oracleReg n 2
    k).embedUnitary (permutationUnitary (flipFlag0Perm n))))) (jp01ReadoutCircuit res n k T cont0)
    else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then .seq (resetRegCircuit res
    (oracleReg n 2 k)) (fallbackCleanR2Circuit res n k T) else .skip
  let y_norm := (1 / √(w 0)) • y
  have hy_norm_eq : ((DickeSol.rot3Neg u2)^[K2]) (((DickeSol.rot3Pos u1)^[K1]) x_norm) = y_norm
    := by
    dsimp only [x_norm, y_norm, y]; rw [iter_smul_vec3 (rot3Pos_smul u1), iter_smul_vec3
      (rot3Neg_smul u2)]
  let branchVal (o : Fin (2 ^ 2)) : ℝ := if o = 0 then ((K1 + K2 : ℕ) : ℝ) + 1 + (1 - (y_norm 2) ^
    2 - (y_norm 0) ^ 2) * zh + (y_norm 0) ^ 2 * B0 else if o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 <
    2 ^ 2)⟩ then 1 + zh else if o = ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ then 2 * √((2 : ℝ)
    ^ n) else 0
  have hzh_nn : 0 ≤ zh := (by dsimp only [zh]; positivity)
  have hy_norm_dot : DickeSol.dot3 y_norm y_norm = 1 := by
    rw [← hy_norm_eq]
    have h1 : ∀ z, DickeSol.dot3 (DickeSol.rot3Pos u1 z) (DickeSol.rot3Pos u1 z) =
        DickeSol.dot3 z z := fun _ => dot3_rot3Pos hdu1
    have h2 : ∀ z, DickeSol.dot3 (DickeSol.rot3Neg u2 z) (DickeSol.rot3Neg u2 z) =
        DickeSol.dot3 z z := fun _ => dot3_rot3Neg hdu2
    have hi1 : ∀ m z, DickeSol.dot3 (((DickeSol.rot3Pos u1)^[m]) z) (((DickeSol.rot3Pos u1)^[m]) z)
      = DickeSol.dot3 z z := by
      intro m; induction m with
      | zero => intro _; rfl
      | succ m ih => intro z; rw [Function.iterate_succ_apply, ih, h1]
    have hi2 : ∀ m z, DickeSol.dot3 (((DickeSol.rot3Neg u2)^[m]) z) (((DickeSol.rot3Neg u2)^[m]) z)
      = DickeSol.dot3 z z := by
      intro m; induction m with
      | zero => intro _; rfl
      | succ m ih => intro z; rw [Function.iterate_succ_apply, ih, h2]
    rw [hi2, hi1, hx_norm]
  have hy_rem_nn : 0 ≤ 1 - (y_norm 2) ^ 2 - (y_norm 0) ^ 2 :=
    (by have hd := hy_norm_dot; dsimp only [DickeSol.dot3] at hd; nlinarith [sq_nonneg (y_norm 1)])
  have hbv_nn (o : Fin (2 ^ 2)) : 0 ≤ branchVal o := by
    dsimp only [branchVal]; split_ifs
    · exact add_nonneg (add_nonneg (by positivity) (mul_nonneg hy_rem_nn hzh_nn)) (mul_nonneg
        (sq_nonneg _) hB0_nn)
    · positivity
    · positivity
    · exact le_rfl
  let Post : CQAssertion (Store Var) (2 ^ findAllQubits n 2 k) :=
    liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)
  have hbranch (o : Fin (2 ^ 2)) :
      let fo := (branchCirc o).compile QProg.qAssign oracleS; let Ξ_o := sliceState res 0 2 o.val Δm
      𝔼[(interp fo).toStateFun Ξ_o, Post] = w o * Δ.trace ∧
        expectedCost modelS fo Ξ_o ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w o * branchVal o) := by
    intro fo Ξ_o; obtain ⟨hPo, htro⟩ := hmeas o; rw [htr_u] at htro
    have hmass_o : (Ξ_o.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w o) := by
      nth_rw 1 [← ENNReal.ofReal_coe_nnreal]
      rw [htro, mul_comm (w o), ENNReal.ofReal_mul Δ.trace.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    have ho_cases : o = 0 ∨ o = ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ∨ o = ⟨2,
      (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ ∨ o = ⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ :=
      (by fin_cases o <;> simp); rcases ho_cases with rfl | rfl | rfl | rfl
    · dsimp only [ψ_out] at hPo; simp only [↓reduceIte] at hPo
      have hDF1 (z : Fin 3 → ℝ) : DickeSol.r1SymMat (2 ^ n) 2 *ᵥ DickeSol.orbEmbed3 (2 ^ n) 2 A
        (DickeSol.zOrb3 z) = DickeSol.orbEmbed3 (2 ^ n) 2 A (DickeSol.rot3Pos u1 z) := by
        have hr1 := DickeSol.r1SymMat_mulVec_orbEmbed3 (N := 2 ^ n) (m := 2) (R := A) (by omega)
          (by omega) hmin2 hmrN (DickeSol.zOrb3 z); simpa [u1, hA2, DickeSol.rot3Pos] using hr1
      have hDF2 (z : Fin 3 → ℝ) : DickeSol.r01SymMat (2 ^ n) 2 *ᵥ DickeSol.orbEmbed3 (2 ^ n) 2 A
        (DickeSol.zOrb3 z) = DickeSol.orbEmbed3 (2 ^ n) 2 A (DickeSol.rot3Neg u2 z) := by
        have hr2 := DickeSol.r01SymMat_mulVec_orbEmbed3 (N := 2 ^ n) (m := 2) (R := A) (by omega)
          (by omega) hmin2 hmrN h2mN (DickeSol.zOrb3 z); simpa [u2, hA2, DickeSol.rot3Neg] using hr2
      obtain ⟨hP1, htr1, hcost1⟩ := jp01WalkRec_pureStateAt hn hTS hA2 (DickeSol.r1SymMat (2 ^ n) 2)
        (r1SymMat_orth hn) (DickeSol.rot3Pos u1) hDF1 (fun _ => dot3_rot3Pos hdu1) K1 x_norm hx_norm
        hPo
      set Ξ1 := (interp ((jp01WalkRec n k U1 T K1).compile QProg.qAssign oracleS)).toStateFun Ξ_o
      have hx1_norm : DickeSol.dot3 (((DickeSol.rot3Pos u1)^[K1]) x_norm) (((DickeSol.rot3Pos
        u1)^[K1]) x_norm) = 1 := by
        have hi1 : ∀ m z, DickeSol.dot3 (((DickeSol.rot3Pos u1)^[m]) z) (((DickeSol.rot3Pos u1)^[m])
          z) = DickeSol.dot3 z z := by
          intro m; induction m with
          | zero => intro _; rfl
          | succ m ih => intro z; rw [Function.iterate_succ_apply, ih, dot3_rot3Pos hdu1]
        rw [hi1, hx_norm]
      obtain ⟨hP2, htr2, hcost2⟩ := jp01WalkRec_pureStateAt hn hTS hA2 (DickeSol.r01SymMat (2 ^ n)
        2) (r01SymMat_orth hn) (DickeSol.rot3Neg u2) hDF2 (fun _ => dot3_rot3Neg hdu2) K2 _ hx1_norm
        hP1
      set Ξ2 := (interp ((jp01WalkRec n k U2 T K2).compile QProg.qAssign oracleS)).toStateFun Ξ1
      rw [hy_norm_eq] at hP2
      obtain ⟨hv_yn, hp0_yn, hp2_yn⟩ := orbEmbed3_filter_zero_two_sq hn hA2 y_norm
      rw [hy_norm_dot] at hv_yn
      obtain ⟨hexp_r, hcost_r⟩ := jp01Readout_transition res hn hk1024 hScard hTS hA2 hv_yn (fun _
        hd => liftSymPairReal_diag_zero _ hd) hB0_nn hcont0 hP2; rw [hp0_yn, hp2_yn] at hcost_r
      have hmass1 : (Ξ1.trace : ℝ≥0∞) = (Ξ_o.trace : ℝ≥0∞) := congrArg ENNReal.ofNNReal htr1
      have hmass2 : (Ξ2.trace : ℝ≥0∞) = (Ξ_o.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal (htr2.trans htr1)
      rw [hmass1] at hcost2; rw [hmass2] at hcost_r; refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]; simp only [↓reduceIte, OracleDynamicCircuit.compile_seq,
          interp_qSeq, QMonad.Q.toStateFun_bind]; rw [hexp_r, htr2, htr1, htro]
      · dsimp only [fo, branchCirc, branchVal]; simp only [↓reduceIte,
          OracleDynamicCircuit.compile_seq, expectedCost_qSeq]; have hr_nn : 0 ≤ 1 + (1 - (y_norm 2)
          ^ 2 - (y_norm 0) ^ 2) * zh + (y_norm 0) ^ 2 * B0 := add_nonneg (add_nonneg zero_le_one
          (mul_nonneg hy_rem_nn hzh_nn)) (mul_nonneg (sq_nonneg _) hB0_nn)
        calc _ ≤ (Ξ_o.trace : ℝ≥0∞) * ENNReal.ofReal (K1 : ℝ) + ((Ξ_o.trace : ℝ≥0∞) *
              ENNReal.ofReal (K2 : ℝ) + (Ξ_o.trace : ℝ≥0∞) * ENNReal.ofReal
              (1 + (1 - (y_norm 2) ^ 2 - (y_norm 0) ^ 2) * zh + (y_norm 0) ^ 2 * B0)) :=
              add_le_add hcost1 (add_le_add hcost2 hcost_r)
          _ = (Ξ_o.trace : ℝ≥0∞) * ENNReal.ofReal (((K1 + K2 : ℕ) : ℝ) + 1 +
                (1 - (y_norm 2) ^ 2 - (y_norm 0) ^ 2) * zh + (y_norm 0) ^ 2 * B0) := by
              rw [← mul_add, ← ENNReal.ofReal_add (Nat.cast_nonneg K2) hr_nn, ← mul_add, ←
                ENNReal.ofReal_add (Nat.cast_nonneg K1) (add_nonneg (Nat.cast_nonneg K2) hr_nn)]
              congr 2; push_cast; ring
          _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w 0 * (((K1 + K2 : ℕ) : ℝ) + 1 +
                (1 - (y_norm 2) ^ 2 - (y_norm 0) ^ 2) * zh + (y_norm 0) ^ 2 * B0)) := by
              rw [hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn 0)]
    · dsimp only [ψ_out] at hPo
      simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        ↓reduceIte] at hPo
      let Uf0 := (oracleReg n 2 k).embedUnitary (permutationUnitary (flipFlag0Perm n))
      set Ξ_f0 := (interp ((OracleDynamicCircuit.step (phaseI Uf0)).compile QProg.qAssign
        oracleS)).toStateFun Ξ_o
      have hΞ_f0_eq : Ξ_f0 = CQState.qAssign Uf0 Ξ_o := by
        dsimp only [Ξ_f0]; rw [OracleDynamicCircuit.compile_step, interp_qAssign]
        exact cqState_qAssign_phaseI Uf0 Ξ_o
      have hψ1_norm := hψ_out ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩
      dsimp only [ψ_out] at hψ1_norm
      simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        ↓reduceIte] at hψ1_norm
      obtain ⟨hPf0, htr_f0⟩ := pureStateAt_qAssign Uf0 hψ1_norm hPo; rw [← hΞ_f0_eq] at hPf0 htr_f0
      have hf0_vec : Uf0.1 *ᵥ ((oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState (fun u
        => ((oddPairRealR2 n A sgn u : ℝ) : ℂ)) (Pi.single (envOfMask n ⟨1, (Nat.lt_of_sub_eq_succ
        rfl : 1 < 2 ^ 2)⟩) 1)) env0) = (oracleReg n 2 k).tensorState ((localAddrReg n 2).tensorState
        (fun u => ((oddPairRealR2 n A sgn u : ℝ) : ℂ)) (Pi.single 0 1)) env0 := by
        dsimp only [Uf0]; rw [QRegister.embedUnitary_val, (oracleReg n 2
          k).embedMatrix_mulVec_tensorState, flipFlag0Perm_mulVec_one]
      rw [hf0_vec] at hPf0
      obtain ⟨hexp_r, hcost_r⟩ := jp01Readout_transition res hn hk1024 hScard hTS hA2 hodd_norm
        hodd_off hB0_nn hcont0 hPf0; rw [hodd_p0, hodd_p2] at hcost_r; simp only [sub_zero, one_mul,
        zero_mul, add_zero] at hcost_r; have hmass_f0 : (Ξ_f0.trace : ℝ≥0∞) = (Ξ_o.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal htr_f0
      rw [hmass_f0] at hcost_r; refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte,
          OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
        rw [hexp_r, htr_f0, htro]
      · dsimp only [fo, branchCirc, branchVal]
        simp only [show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          ↓reduceIte,
          OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
          expectedCost_qSeq, expectedCost_qAssign]
        have hc0 := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacleS (isRealMatrix_embedUnitary
          (oracleReg n 2 k) (isRealMatrix_permutationUnitary (flipFlag0Perm n)))
        have hstep0 : (Ξ_o.trace : ℝ≥0∞) * ↑(modelS.unitaryCost (phaseI Uf0)) = 0 :=
          (by dsimp [Uf0]; rw [hc0]; simp); rw [hstep0, zero_add]
        calc _ ≤ (Ξ_o.trace : ℝ≥0∞) * ENNReal.ofReal (1 + zh) := hcost_r
          _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ * (1 + zh)) := by
              rw [hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1
                < 2 ^ 2)⟩)]
    · dsimp only [ψ_out] at hPo
      simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
        show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
          (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte] at hPo
      let v_diag := (localAddrReg n 2).tensorState (diagNormVecR2 n A γ)
        (Pi.single (envOfMask n ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩) 1)
      have hv_diag : star v_diag ⬝ᵥ v_diag = 1 := by
        dsimp only [v_diag]; rw [dotProduct_tensorState, dotProduct_diagNormVecR2 hn hA2 γ,
          dotProduct_env_single, mul_one]
      have hϕ0 : star ((oracleReg n 2 k).tensorState (Pi.single 0 1) env0) ⬝ᵥ (oracleReg n 2
        k).tensorState (Pi.single 0 1) env0 = 1 :=
        (by rw [dotProduct_tensorState, dotProduct_single_one, dotProduct_env_single, mul_one])
      obtain ⟨hPrst, htr_rst⟩ := resetRegCircuit_pureStateAt oracleS res (oracleReg n 2 k) hv_diag
        hϕ0 hPo; set Ξ_rst := (interp ((resetRegCircuit res (oracleReg n 2 k)).compile QProg.qAssign
        oracleS)).toStateFun Ξ_o
      have hPrst0 : PureStateAt (Pi.single 0 1) Ξ_rst := by
        have hz_eq : (oracleReg n 2 k).tensorState (Pi.single 0 1) env0 = Pi.single 0 1 :=
          (by rw [← prodSlotLocalVec_single_zero n 2]; exact prodSlotState_single_zero n 2 k)
        rwa [hz_eq] at hPrst
      obtain ⟨hexp_fb, hcost_fb⟩ := fallbackCleanR2_transition res hn hk1024 hScard hTS hA2 hPrst0
      have hmass_rst : (Ξ_rst.trace : ℝ≥0∞) = (Ξ_o.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal htr_rst
      refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte,
          OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
        rw [hexp_fb, htr_rst, htro]
      · dsimp only [fo, branchCirc, branchVal]
        simp only [show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp, ↓reduceIte,
          OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
        rw [expectedCost_resetRegCircuit_eq_zero res _ horacleS, zero_add]
        calc _ ≤ (Ξ_rst.trace : ℝ≥0∞) * ENNReal.ofReal (2 * √((2 : ℝ) ^ n)) := hcost_fb
          _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w ⟨2,
            (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ * (2 * √((2 : ℝ) ^ n))) := by
              rw [hmass_rst, hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn ⟨2,
                (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩)]
    · have htr0 : Ξ_o.trace = 0 := NNReal.coe_inj.mp (by push_cast; simpa [w] using htro)
      refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
          show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
          show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
            (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp, ↓reduceIte,
          OracleDynamicCircuit.compile_skip, interp_skip, QMonad.Q.toStateFun_pure, w, zero_mul]
        exact expect_eq_zero_of_trace_eq_zero htr0 Post
      · dsimp only [fo, branchCirc, branchVal]; simp [w]
  have hprog_unfold : prog = ((OracleDynamicCircuit.step (phaseI Ucswap)).compile QProg.qAssign
    oracleS ;; (QProg.measureRegister res (allMarkersReg n 2 k) ;; (dispBits res 2 0 fun oVal =>
    branchCirc ⟨oVal % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile QProg.qAssign oracleS)) := by
    dsimp only [prog, jp01CoreBodyCircuit, Ucswap, branchCirc, U1, U2]
    rw [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_measure]
  rw [hprog_unfold]; refine ⟨?_, ?_⟩
  · rw [interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSeq, QMonad.Q.toStateFun_bind,
      expect_dispBits, ← Fin.sum_univ_eq_sum_range]
    have hsum_eq :
        (∑ o : Fin (2 ^ 2),
          𝔼[(interp ((branchCirc ⟨o.val % 2 ^ 2, Nat.mod_lt _ (by positivity)⟩).compile
              QProg.qAssign oracleS)).toStateFun (sliceState res 0 2 o.val Δm), Post]) =
        ∑ o : Fin (2 ^ 2), w o * Δ.trace :=
      Finset.sum_congr rfl fun o _ => by simpa only [fin_mk_mod_pow] using (hbranch o).1
    rw [hsum_eq, ← Finset.sum_mul, hw_sum, one_mul]
  · rw [expectedCost_qSeq, expectedCost_qSeq]
    have hc_u : expectedCost modelS ((OracleDynamicCircuit.step (phaseI Ucswap)).compile
      QProg.qAssign oracleS) Δ = 0 := by
      dsimp [Ucswap]; rw [ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacleS
        (isRealMatrix_embedUnitary (oracleReg n 2 k) (isRealMatrix_cswapFilterUnitary n))]; simp
    have hc_m : expectedCost modelS (QProg.measureRegister res (allMarkersReg n 2 k)) Δu = 0 :=
      (by simp [QProg.measureRegister, modelS]); rw [hc_u, zero_add, hc_m, zero_add,
      expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range]
    calc _ ≤ ∑ o : Fin (2 ^ 2), (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (w o * branchVal o) :=
            Finset.sum_le_sum fun o _ => by simpa only [fin_mk_mod_pow] using (hbranch o).2
      _ = (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (∑ o : Fin (2 ^ 2), w o * branchVal o) := by
          rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun o _ => mul_nonneg (hw_nn o)
            (hbv_nn o))]
      _ ≤ (Δ.trace : ℝ≥0∞) * ENNReal.ofReal
            ((1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2) * ((K1 + K2 : ℕ) : ℝ) + 2 +
              (1 - (y 2) ^ 2 - (y 0) ^ 2) * zh + (y 0) ^ 2 * B0) := by
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
          have huniv4 : (Finset.univ : Finset (Fin (2 ^ 2))) = {0, ⟨1, (Nat.lt_of_sub_eq_succ rfl :
            1 < 2 ^ 2)⟩, ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩, ⟨3, (Nat.lt_of_sub_eq_succ
            rfl : 3 < 2 ^ 2)⟩} := (by ext x; fin_cases x <;> simp); rw [huniv4, Finset.sum_insert
            (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
            Finset.sum_singleton]
          have hy0_sq : w 0 * (y_norm 0) ^ 2 = (y 0) ^ 2 := by
            dsimp only [y_norm, Pi.smul_apply, smul_eq_mul]; rw [mul_pow, div_pow, one_pow,
              Real.sq_sqrt hw0_pos.le, ← mul_assoc, mul_one_div_cancel hw0_pos.ne', one_mul]
          have hy2_sq : w 0 * (y_norm 2) ^ 2 = (y 2) ^ 2 := by
            dsimp only [y_norm, Pi.smul_apply, smul_eq_mul]; rw [mul_pow, div_pow, one_pow,
              Real.sq_sqrt hw0_pos.le, ← mul_assoc, mul_one_div_cancel hw0_pos.ne', one_mul]
          have hdiag_le : (1 / (2 : ℝ) ^ n) * (2 * √((2 : ℝ) ^ n)) ≤ 1 := by
            have hSN_pos : 0 < √((2 : ℝ) ^ n) := lt_of_lt_of_le (by positivity) hSN_ge
            have heq : (1 / (2 : ℝ) ^ n) * (2 * √((2 : ℝ) ^ n)) = 2 / √((2 : ℝ) ^ n) := by
              field_simp [hSN_pos.ne']; rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
            rw [heq, div_le_one hSN_pos]; linarith [hSN_ge]
          have hrem_w0 : w 0 * (1 - (y_norm 2) ^ 2 - (y_norm 0) ^ 2) = w 0 - (y 2) ^ 2 - (y 0) ^ 2
            := (by linarith [hy0_sq, hy2_sq]); dsimp only [branchVal]
          simp only [
            show (⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
            show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
            show (⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
              (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
            show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
            show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨1,
              (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ by simp,
            show (⟨3, (Nat.lt_of_sub_eq_succ rfl : 3 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ ⟨2,
              (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ by simp,
            ↓reduceIte, mul_zero, add_zero]
          have hw0_le : w 0 ≤ 1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2 := by
            dsimp only [w]; simp only [↓reduceIte]; have : 0 ≤ 1 / (2 : ℝ) ^ n := (by positivity)
            linarith
          have hw01_le1 : w 0 + w ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ ≤ 1 := by
            dsimp only [w]; simp only [show (⟨1,
              (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ : Fin (2 ^ 2)) ≠ 0 by simp,
              ↓reduceIte]; have : 0 ≤ 1 / (2 : ℝ) ^ n := (by positivity); linarith
          have hw2_eq : w ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ = 1 / (2 : ℝ) ^ n := by
            dsimp only [w]; rw [ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_left rfl]
          have hK_le : w 0 * ((K1 + K2 : ℕ) : ℝ) ≤ (1 - Real.sin (γ - halfAngleSet n 2) ^ 2 / 2) *
            ((K1 + K2 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hw0_le (Nat.cast_nonneg _)
          have hzh_le : (w 0 + w ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ - (y 2) ^ 2 - (y 0) ^
            2) * zh ≤ (1 - (y 2) ^ 2 - (y 0) ^ 2) * zh := mul_le_mul_of_nonneg_right
            (by linarith [hw01_le1]) hzh_nn
          have hexp0 : w 0 * (((K1 + K2 : ℕ) : ℝ) + 1 + (1 - (y_norm 2) ^ 2 - (y_norm 0) ^ 2) * zh +
            (y_norm 0) ^ 2 * B0) + (w ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ * (1 + zh) + w
            ⟨2, (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ * (2 * √((2 : ℝ) ^ n))) = w 0 * ((K1 + K2 :
            ℕ) : ℝ) + (w 0 + w ⟨1, (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩) + w ⟨2,
            (Nat.lt_of_sub_eq_succ rfl : 2 < 2 ^ 2)⟩ * (2 * √((2 : ℝ) ^ n)) + (w 0 + w ⟨1,
            (Nat.lt_of_sub_eq_succ rfl : 1 < 2 ^ 2)⟩ - (y 2) ^ 2 - (y 0) ^ 2) * zh + (y 0) ^ 2 * B0
            := (by linear_combination zh * hrem_w0 + B0 * hy0_sq)
          rw [hexp0, hw2_eq]; linarith [hK_le, hw01_le1, hdiag_le, hzh_le]
private noncomputable def coldJP01R2Rec {Var : Type} (res : Var) (n k : ℕ)
    (hn : 200 ≤ n) (T : Finset (Fin (2 ^ n))) :
    ℕ → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
      (findAllQubits n 2 k) ((n + 1) * 2)
  | 0 => fallbackCleanR2Circuit res n k T
  | f + 1 =>
      .seq (prepSlotsListCircuit res n 2 k (fun _ => true) (List.finRange 2))
        (jp01CoreBodyCircuit res n k hn T
          (DickeSol.p01StepCount warmJP01ColdTau1 (2 ^ n))
          (DickeSol.p01StepCount warmJP01ColdTau2 (2 ^ n))
          (coldJP01R2Rec res n k hn T f))
private theorem coldJP01R2Rec_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn :
  200 ≤ n) (hk1024 : k ≤ 1024) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA2
  : (S \ T).card = 2) :
    let B_fuel := fun f : ℕ =>
      ((warmJP01ColdV2 - 1 : ℕ) : ℝ) / 1000000000000 + (1 / 5 : ℝ) ^ f * 2
    ∀ (f : ℕ) (Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k)), PureStateAt (Pi.single 0 1) Δ →
        let prog := (coldJP01R2Rec res n k hn T f).compile QProg.qAssign
          (parallelMarkingOracle 2 S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
          (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (B_fuel f * √((2 : ℝ) ^ n)) := by
  intro B_fuel
  obtain ⟨_, h2_le_B0, _, hcold_step, _⟩ := warmJP01Table_cold_and_warm_sound cert_warmJP01_r2Table
    hn; dsimp only at h2_le_B0 hcold_step; have hSN_nn : 0 ≤ √((2 : ℝ) ^ n) := Real.sqrt_nonneg _
  let oracle := parallelMarkingOracle 2 S
  have horacle := isRealMatrix_parallelMarkingOracle (m := 2) S
  have hN16 : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right
    (by positivity) hn); have hA_pos : 1 ≤ (S \ T).card := (by omega)
  have hA_lt : (S \ T).card < 2 ^ n := (by omega); have hn100 : 100 ≤ n := (by omega); obtain ⟨_, _,
    hθ2_13, -⟩ := halfAngleSet_bounds_100 hn100 (by omega : 1 ≤ 2) (by omega : 2 ≤ 1024)
  have hθ2_54 : halfAngleSet n 2 ≤ 5 / 4 := (by linarith [hθ2_13]); intro f
  induction f with
  | zero =>
      intro Δ hΔ; obtain ⟨hexp, hcost⟩ := fallbackCleanR2_transition res hn hk1024 hScard hTS hA2 hΔ
      refine ⟨hexp, hcost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right h2_le_B0 hSN_nn)) zero_le)⟩
  | succ f ih =>
      intro Δ hΔ; have hP0 : PureStateAt (prodSlotState n 2 k fun _ => Pi.single 0 1) Δ :=
        (by rwa [prodSlotState_single_zero])
      obtain ⟨hPprep, htr_prep⟩ := prepSlotsListCircuit_pureStateAt oracle res (fun _ => true)
        (List.finRange 2) (List.nodup_finRange 2) hA_pos hA_lt (fun _ => dotProduct_single_one 0)
        hP0; set Ξ_prep := (interp ((prepSlotsListCircuit res n 2 k (fun _ => true) (List.finRange
        2)).compile QProg.qAssign oracle)).toStateFun Δ
      have hPprep' : PureStateAt (prodSlotState n 2 k fun _ => slotPairVec (planeVec (S \ T)
        (halfAngleSet n 2)) (Pi.single 0 1)) Ξ_prep := by
        convert hPprep using 2
        funext _; simp [List.mem_finRange, hA2]
      have hBf_nn : 0 ≤ B_fuel f * √((2 : ℝ) ^ n) := (by dsimp only [B_fuel]; positivity)
      obtain ⟨hexp_c, hcost_c⟩ := jp01CoreBody_transition res hn hk1024 hScard hTS hA2 (γ :=
        halfAngleSet n 2) le_rfl hθ2_54 (Or.inl ⟨rfl, rfl⟩) (DickeSol.p01StepCount warmJP01ColdTau1
        (2 ^ n)) (DickeSol.p01StepCount warmJP01ColdTau2 (2 ^ n)) hBf_nn ih hPprep'; have hstep_f :=
        hcold_step f
      have hub_step : (1 - Real.sin (halfAngleSet n 2 - halfAngleSet n 2) ^ 2 / 2) *
        ((DickeSol.p01StepCount warmJP01ColdTau1 (2 ^ n) + DickeSol.p01StepCount warmJP01ColdTau2 (2
        ^ n) : ℕ) : ℝ) + 2 + (1 - (((DickeSol.rot3Neg (DickeSol.u2OrbVec (2 ^ n) 2 2))^[
        DickeSol.p01StepCount warmJP01ColdTau2 (2 ^ n)]) (((DickeSol.rot3Pos (DickeSol.u1OrbVec (2 ^
        n) 2 2))^[ DickeSol.p01StepCount warmJP01ColdTau1 (2 ^ n)]) (jp01InitOrbVec n (halfAngleSet
        n 2))) 2) ^ 2 - (((DickeSol.rot3Neg (DickeSol.u2OrbVec (2 ^ n) 2 2))^[ DickeSol.p01StepCount
        warmJP01ColdTau2 (2 ^ n)]) (((DickeSol.rot3Pos (DickeSol.u1OrbVec (2 ^ n) 2 2))^[
        DickeSol.p01StepCount warmJP01ColdTau1 (2 ^ n)]) (jp01InitOrbVec n (halfAngleSet n 2))) 0) ^
        2) * (((cswapZeroHitNat : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)) + (((DickeSol.rot3Neg
        (DickeSol.u2OrbVec (2 ^ n) 2 2))^[ DickeSol.p01StepCount warmJP01ColdTau2 (2 ^ n)])
        (((DickeSol.rot3Pos (DickeSol.u1OrbVec (2 ^ n) 2 2))^[ DickeSol.p01StepCount
        warmJP01ColdTau1 (2 ^ n)]) (jp01InitOrbVec n (halfAngleSet n 2))) 0) ^ 2 * (B_fuel f * √((2
        : ℝ) ^ n)) ≤ B_fuel (f + 1) * √((2 : ℝ) ^ n) := by
        dsimp only [B_fuel]; rw [sub_self, Real.sin_zero]; refine (le_of_eq ?_).trans hstep_f; ring
      have hmass_prep : (Ξ_prep.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal htr_prep
      dsimp only [coldJP01R2Rec]; rw [OracleDynamicCircuit.compile_seq, interp_qSeq,
        QMonad.Q.toStateFun_bind, expectedCost_qSeq, expectedCost_prepSlotsListCircuit_eq_zero res n
        2 k _ _ horacle, zero_add]
      refine ⟨by rw [hexp_c, htr_prep], ?_⟩; rw [hmass_prep] at hcost_c
      exact hcost_c.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hub_step) zero_le)
private noncomputable def warmJP01R2Circuit {Var : Type} (res : Var) (n k : ℕ) (T : Finset (Fin (2 ^
    n))) (betas : Fin 2 → ℝ) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
    (findAllQubits n 2 k) ((n + 1) * 2) :=
  open Classical in
  if hc : warmJP01Guard n betas ∧ 200 ≤ n then
    let γ := max (betas s0) (betas s1)
    let r := warmJP01Rows (warmJP01BinIdx γ)
    jp01CoreBodyCircuit res n k hc.2 T
      (DickeSol.p01StepCount r.tau1_12 (2 ^ n))
      (DickeSol.p01StepCount r.tau2_12 (2 ^ n))
      (coldJP01R2Rec res n k hc.2 T 25)
  else
    .seq (resetRegCircuit res (oracleReg n 2 k)) (fallbackCleanR2Circuit res n k T)
private theorem warmJP01R2_transition {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (hn : 200
  ≤ n) (hk1024 : k ≤ 1024) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA2 :
  (S \ T).card = 2) (betas : Fin 2 → ℝ) {Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k)} (hΔ :
  PureStateAt (prodSlotState n 2 k fun i => slotPairVec (planeVec (S \ T) (betas i)) (Pi.single 0
  1)) Δ) :
    let prog := (warmJP01R2Circuit res n k T betas).compile QProg.qAssign (parallelMarkingOracle 2
      S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
      (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (warmJP01R2Cost2 warmJP01V2Mono n betas) := by
  intro prog; by_cases hg : warmJP01Guard n betas
  · have hc : warmJP01Guard n betas ∧ 200 ≤ n := ⟨hg, hn⟩; rcases hg with ⟨hor, hb0_lo, hb1_lo,
      hsin_lt, hγ_hi⟩; set γ := max (betas s0) (betas s1); have hγ_lo : halfAngleSet n 2 ≤ γ :=
      le_max_of_le_left hb0_lo
    have hslots : (betas s0 = halfAngleSet n 2 ∧ betas s1 = γ) ∨ (betas s0 = γ ∧ betas s1 =
      halfAngleSet n 2) := by
      rcases hor with hb0 | hb1
      · exact Or.inl ⟨hb0, (max_eq_right (hb0.symm ▸ hb1_lo)).symm⟩
      · exact Or.inr ⟨(max_eq_left (hb1.symm ▸ hb0_lo)).symm, hb1⟩
    obtain ⟨_, _, hB25_le, _, hwarm_sound⟩ := warmJP01Table_cold_and_warm_sound
      cert_warmJP01_r2Table hn; dsimp only at hB25_le hwarm_sound
    have hcold25 : ∀ Υ : CQState (Store Var) (2 ^ findAllQubits n 2 k), PureStateAt (Pi.single 0 1)
      Υ →
      𝔼[(interp ((coldJP01R2Rec res n k hn T 25).compile QProg.qAssign (parallelMarkingOracle 2
      S))).toStateFun Υ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)] = Υ.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) ((coldJP01R2Rec res n k
      hn T 25).compile QProg.qAssign (parallelMarkingOracle 2 S)) Υ ≤ (Υ.trace : ℝ≥0∞) *
      ENNReal.ofReal (((warmJP01ColdV2 : ℝ) / 1000000000000) * √((2 : ℝ) ^ n)) := by
      intro Υ hΥ; obtain ⟨he, hco⟩ := coldJP01R2Rec_transition res hn hk1024 hScard hTS hA2 25 Υ hΥ
      refine ⟨he, hco.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hB25_le (Real.sqrt_nonneg _))) zero_le)⟩
    set r := warmJP01Rows (warmJP01BinIdx γ); have hcv2_nn : 0 ≤ ((warmJP01ColdV2 : ℝ) /
      1000000000000) * √((2 : ℝ) ^ n) := (by positivity); obtain ⟨hexp, hcost⟩ :=
      jp01CoreBody_transition res hn hk1024 hScard hTS hA2 hγ_lo hγ_hi hslots (DickeSol.p01StepCount
      r.tau1_12 (2 ^ n)) (DickeSol.p01StepCount r.tau2_12 (2 ^ n)) hcv2_nn hcold25 hΔ
    have hw_row := hwarm_sound γ hγ_lo hγ_hi hsin_lt; have hprog_eq : prog = (jp01CoreBodyCircuit
      res n k hn T (DickeSol.p01StepCount r.tau1_12 (2 ^ n)) (DickeSol.p01StepCount r.tau2_12 (2 ^
      n)) (coldJP01R2Rec res n k hn T 25)).compile QProg.qAssign (parallelMarkingOracle 2 S) :=
      (by dsimp only [prog, warmJP01R2Circuit]; rw [dite_eq_left hc])
    have hcost_eq : warmJP01R2Cost2 warmJP01V2Mono n betas = ((warmJP01V2Mono (warmJP01BinIdx γ) :
      ℝ) / 1000000000000) * √((2 : ℝ) ^ n) :=
      (by dsimp only [warmJP01R2Cost2, γ]; exact ite_eq_left ⟨hor, hb0_lo, hb1_lo, hsin_lt, hγ_hi⟩)
    rw [hprog_eq, hcost_eq]; refine ⟨hexp, hcost.trans (mul_le_mul_of_nonneg_left
      (ENNReal.ofReal_le_ofReal ?_) zero_le)⟩; dsimp only [r]; refine (le_of_eq ?_).trans hw_row
    ring
  · have hnc : ¬ (warmJP01Guard n betas ∧ 200 ≤ n) := fun h => hg h.1
    let oracleS := parallelMarkingOracle 2 S
    have horacleS := isRealMatrix_parallelMarkingOracle (m := 2) S
    let env0 : ((oracleReg n 2 k).Environment → ZMod 2) → ℂ :=
      Pi.single ((oracleReg n 2 k).basisSplitEquiv 0).2 1
    have hN16 : 16 ≤ 2 ^ n := le_trans (by norm_num : 16 ≤ 2 ^ 200) (Nat.pow_le_pow_right
      (by positivity) hn)
    let v_loc := prodSlotLocalVec fun i => slotPairVec (planeVec (S \ T) (betas i)) (Pi.single 0 1)
    have hv_loc : star v_loc ⬝ᵥ v_loc = 1 :=
      dotProduct_prodSlotLocalVec fun i =>
        dotProduct_slotPairVec (dotProduct_planeVec (by omega) (by omega) (betas i))
          (dotProduct_single_one 0)
    have hϕ0 : star ((oracleReg n 2 k).tensorState (Pi.single 0 1) env0) ⬝ᵥ (oracleReg n 2
      k).tensorState (Pi.single 0 1) env0 = 1 :=
      (by rw [dotProduct_tensorState, dotProduct_single_one, dotProduct_env_single, mul_one])
    obtain ⟨hPrst, htr_rst⟩ := resetRegCircuit_pureStateAt oracleS res (oracleReg n 2 k) hv_loc hϕ0
      hΔ; set Ξ_rst := (interp ((resetRegCircuit res (oracleReg n 2 k)).compile QProg.qAssign
      oracleS)).toStateFun Δ
    have hPrst0 : PureStateAt (Pi.single 0 1) Ξ_rst := by
      have hz_eq : (oracleReg n 2 k).tensorState (Pi.single 0 1) env0 = Pi.single 0 1 :=
        (by rw [← prodSlotLocalVec_single_zero n 2]; exact prodSlotState_single_zero n 2 k)
      rwa [hz_eq] at hPrst
    obtain ⟨hexp_fb, hcost_fb⟩ := fallbackCleanR2_transition res hn hk1024 hScard hTS hA2 hPrst0
    have hmass_rst : (Ξ_rst.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) := congrArg ENNReal.ofNNReal htr_rst
    have hprog_eq : prog = ((OracleDynamicCircuit.seq (resetRegCircuit res (oracleReg n 2 k))
      (fallbackCleanR2Circuit res n k T)).compile QProg.qAssign oracleS) :=
      (by dsimp only [prog, warmJP01R2Circuit]; rw [dite_eq_right hnc])
    have hcost_eq : warmJP01R2Cost2 warmJP01V2Mono n betas = 2 * √((2 : ℝ) ^ n) :=
      (by dsimp only [warmJP01R2Cost2]; exact ite_eq_right hg); rw [hprog_eq, hcost_eq,
      OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind, expectedCost_qSeq,
      expectedCost_resetRegCircuit_eq_zero res _ horacleS, zero_add]; rw [hmass_rst] at hcost_fb;
      exact ⟨by rw [hexp_fb, htr_rst], hcost_fb⟩
private noncomputable def cswapWarmJP01StageRec {Var : Type} (res : Var)
    (phiFn : ℕ → ℝ) (n k : ℕ) :
    ℕ → Finset (Fin (2 ^ n)) → (Fin 2 → ℝ) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var
        (findAllQubits n 2 k) ((n + 1) * 2)
  | 0, T, betas =>
      warmJP01R2Circuit res n k T betas
  | rem2 + 1, T, betas =>
      let r := rem2 + 3
      stageRampRec res n k T r (phiFn r)
        (fun postBetas o =>
          onHitFuseCircuit res n k (by omega) r o postBetas fun xStar =>
            cswapWarmJP01StageRec res phiFn n k rem2 (insert xStar T)
              (nextStageFuseBetas n r o postBetas))
        (maxRemSteps n r (phiFn r) betas) betas
private theorem cswapWarmJP01StageRec_rMax_transition {Var : Type} [DecidableEq Var] {n k rMax : ℕ}
  (res : Var) (hn : 200 ≤ n) (hk1024 : k ≤ 1024) (hrMax1024 : rMax ≤ 1024) {phiFn ubFn : ℕ → ℝ} {Φ :
  ℕ → (Fin 2 → ℝ) → ℝ} (hΦ : ValidWarmJP01M2Potential warmJP01V2Mono phiFn ubFn n rMax Φ) {S :
  Finset (Fin (2 ^ n))} (hScard : S.card = k) : ∀ rem2 : ℕ, rem2 + 2 ≤ rMax → ∀ T : Finset (Fin (2 ^
  n)), T ⊆ S → (S \ T).card = rem2 + 2 → ∀ betas : Fin 2 → ℝ, ValidStageBetas n (rem2 + 2) (ubFn
  (rem2 + 2)) betas → ∀ Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k), PureStateAt
    (prodSlotState n 2 k
  fun i => slotPairVec (planeVec (S \ T) (betas i)) (Pi.single 0 1)) Δ →
        let prog := (cswapWarmJP01StageRec res phiFn n k rem2 T betas).compile QProg.qAssign
          (parallelMarkingOracle 2 S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ => decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 2 S)) prog Δ ≤
          (Δ.trace : ℝ≥0∞) * ENNReal.ofReal (Φ (rem2 + 2) betas) := by
  have hn100 : 100 ≤ n := (by omega)
  have h2k : 2 * rMax ≤ 2 ^ n := two_mul_le_pow_100 hn100 hrMax1024; intro rem2
  induction rem2 with
  | zero =>
    intro h2rMax T hTS hA2 betas hbetas Δ hΔ
    obtain ⟨hexp, hcost⟩ := warmJP01R2_transition res hn hk1024 hScard hTS hA2 betas hΔ
    refine ⟨hexp, hcost.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hΦ.base2_le
      h2rMax betas hbetas)) zero_le)⟩
  | succ rem2 ih =>
    intro hrk T hTS hAr betas hbetas Δ hΔ; set r := rem2 + 3; have hr3 : 3 ≤ r := (by omega)
    have hr2 : 2 ≤ r := (by omega); have hr1 : 1 ≤ r := (by omega); have h2r : 2 * r ≤ 2 ^ n :=
      (by omega); have hrN : r < 2 ^ n := (by omega); have hprev2 : 2 ≤ r - 1 := (by omega)
    have hprev_k : r - 1 ≤ rMax := (by omega)
    have hθ_prev : halfAngleSet n (r - 1) ≤ ubFn (r - 1) := by
      have hub := hΦ.ub_lb (r - 1) hprev2 hprev_k; by_cases hp2 : r - 1 = 2
      · simpa [hp2] using hub
      · have hp3 : 3 ≤ r - 1 := (by omega); have h1 := hΦ.phi_lb (r - 1) hp3 hprev_k; have h0 : 0 ≤
          halfAngleSet n (r - 1) := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); simp only [hp2,
          ↓reduceIte] at hub; linarith
    have hr_ne2 : r ≠ 2 := (by omega); have hub_r : phiFn r + 2 * halfAngleSet n r ≤ ubFn r :=
      (by simpa [hr_ne2] using hΦ.ub_lb r hr2 hrk)
    have hH_nn : ∀ postBetas, ValidStageBetas n r (ubFn r) postBetas → ∀ o : Fin (2 ^ 2), o ≠ 0 → 0
      ≤ expOnHitFuse Φ n r o postBetas := by
      intro postBetas hpost o _; simp only [expOnHitFuse, hr2, ↓reduceIte]
      exact hΦ.nonneg (r - 1) hprev2 hprev_k _ (validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt
        r hr2 hrk) (hΦ.ub_fuse r hr3 hrk) hθ_prev o hpost)
    exact stageRampRec_transition res (by omega) hTS hAr hr1 hrN
      (hΦ.phi_lb r hr3 hrk) hub_r (hΦ.ub_lt r hr2 hrk)
      (Φ r) (hΦ.nonneg r hr2 hrk)
      (fun postBetas o => expOnHitFuse Φ n r o postBetas) hH_nn
      (hΦ.step_le r hr3 hrk)
      (fun postBetas o =>
        onHitFuseCircuit res n k (by omega) r o postBetas fun xStar =>
          cswapWarmJP01StageRec res phiFn n k rem2 (insert xStar T)
            (nextStageFuseBetas n r o postBetas))
      (fun postBetas hpost o ho Ξ hΞ =>
        onHitFuseCircuit_transition res (by omega) hTS hAr hr2 h2r (hΦ.ub_lt r hr2 hrk) hpost
          ho Φ
          (hΦ.nonneg (r - 1) hprev2 hprev_k _
            (validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt r hr2 hrk)
              (hΦ.ub_fuse r hr3 hrk) hθ_prev o hpost))
          _
          (fun xStar hxStar Υ hΥ => by
            have hT'_sub : insert xStar T ⊆ S := Finset.insert_subset (Finset.mem_sdiff.1 hxStar).1
              hTS
            have hcard_T' : (S \ insert xStar T).card = rem2 + 2 := by
              have hsdiff_eq : S \ insert xStar T = (S \ T) \ {xStar} := by
                ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
                tauto
              rw [hsdiff_eq, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hxStar),
                Finset.card_singleton, hAr]; omega
            have hvalid_next : ValidStageBetas n (rem2 + 2) (ubFn (rem2 + 2)) (nextStageFuseBetas n
              r o postBetas) := validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt r hr2 hrk)
              (hΦ.ub_fuse r hr3 hrk) hθ_prev o hpost
            exact ih hprev_k (insert xStar T) hT'_sub hcard_T' _ hvalid_next Υ hΥ)
          hΞ)
      (maxRemSteps n r (phiFn r) betas) betas hbetas le_rfl Δ hΔ
private noncomputable def cswapWarmJP01FindAllCircuit {Var : Type} (res : Var) (phiFn : ℕ → ℝ) (n k
    : ℕ) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 2 k)) Var (findAllQubits n 2 k) ((n +
    1) * 2) :=
  .seq (prepSlotsListCircuit res n 2 k (fun _ => true) (List.finRange 2))
    (cswapWarmJP01StageRec res phiFn n k (k - 2) ∅ (fun _ => halfAngleSet n k))
private theorem cswapWarmJP01FindAllProgram_correctness_and_costBound {Var : Type} [DecidableEq Var]
  {n k : ℕ} (res : Var) (hn : 200 ≤ n) (hk3 : 3 ≤ k) (hk1024 : k ≤ 1024) {phiFn ubFn : ℕ → ℝ} {Φ : ℕ
  → (Fin 2 → ℝ) → ℝ} (hΦ : ValidWarmJP01M2Potential warmJP01V2Mono phiFn ubFn n k Φ) {S : Finset
  (Fin (2 ^ n))} (hScard : S.card = k) {B : ℝ≥0} (hB : Φ k (fun _ => halfAngleSet n k) ≤ B) :
    let prog := QProg.qSet ;; (cswapWarmJP01FindAllCircuit (Var := Var) res phiFn n k).compile
      QProg.qAssign (parallelMarkingOracle 2 S)
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n 2 k)) ⦄ prog ⦃ liftPureProp (fun σ =>
      decodeTargetsLocal n k (σ res) = S) ⦄ ∧ CostBound (CostModel.ofEmbeddedOracle
      (parallelMarkingOracle 2 S)) prog B := by
  intro prog; have hk_sub : k - 2 + 2 = k := (by omega); have hn100 : 100 ≤ n := (by omega)
  have h2k : 2 * k ≤ 2 ^ n := two_mul_le_pow_100 hn100 hk1024; have hkN : k < 2 ^ n := (by omega)
  let oracle := parallelMarkingOracle 2 S
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n 2 k) oracle
  have horacle := isRealMatrix_parallelMarkingOracle (m := 2) S; have hS1 : 1 ≤ (S \ ∅).card :=
    (by simp [hScard]; omega); have hSN : (S \ ∅).card < 2 ^ n := (by simp [hScard, hkN])
  have hvalid_init : ValidStageBetas n (k - 2 + 2) (ubFn (k - 2 + 2)) (fun _ : Fin 2 => halfAngleSet
    n k) := by
    rw [hk_sub]; intro _; have hub := hΦ.ub_lb k (by omega) le_rfl
    have h0 : 0 ≤ halfAngleSet n k := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); have h1 :=
      hΦ.phi_lb k hk3 le_rfl; simp only [show k ≠ 2 by omega, ↓reduceIte] at hub; exact ⟨le_rfl,
      by linarith⟩
  have hmain (Δ : CQState (Store Var) (2 ^ findAllQubits n 2 k)) : 𝔼[(interp prog).toStateFun Δ,
    liftPureProp (fun σ => decodeTargetsLocal n k (σ res) = S)] = Δ.trace ∧ expectedCost model prog
    Δ ≤ (Δ.trace : ℝ≥0∞) * B := by
    dsimp only [prog, cswapWarmJP01FindAllCircuit]; simp only [OracleDynamicCircuit.compile_seq,
      interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet,
      expectedCost_qSeq]; have hqset : expectedCost model QProg.qSet Δ = 0 := (by simp [model])
    rw [hqset, zero_add, expectedCost_prepSlotsListCircuit_eq_zero res n 2 k _ _ horacle, zero_add]
    have hPqset : PureStateAt (prodSlotState n 2 k fun _ => Pi.single 0 1) Δ.qSet :=
      (by rw [prodSlotState_single_zero]; exact pureStateAt_qSet Δ)
    obtain ⟨hPprep, htr_prep⟩ := prepSlotsListCircuit_pureStateAt oracle res (fun _ => true)
      (List.finRange 2) (List.nodup_finRange 2) hS1 hSN (fun _ => dotProduct_single_one 0) hPqset
    set Ξ_prep := (interp ((prepSlotsListCircuit res n 2 k (fun _ => true) (List.finRange
      2)).compile QProg.qAssign oracle)).toStateFun Δ.qSet
    have hPprep' : PureStateAt (prodSlotState n 2 k fun _ => slotPairVec (planeVec (S \ ∅)
      (halfAngleSet n k)) (Pi.single 0 1)) Ξ_prep := by
      convert hPprep using 2
      funext _; simp [List.mem_finRange, hScard]
    obtain ⟨hexp, hcost⟩ := cswapWarmJP01StageRec_rMax_transition res hn hk1024 hk1024 hΦ hScard (k
      - 2) (by omega) ∅ (Finset.empty_subset S) (by simp [hScard]; omega) (fun _ : Fin 2 =>
      halfAngleSet n k) hvalid_init Ξ_prep hPprep'; refine ⟨?_, ?_⟩
    · rw [hexp, htr_prep, CQState.trace_qSet]
    · rw [hk_sub] at hcost; have hmass : (Ξ_prep.trace : ℝ≥0∞) = (Δ.trace : ℝ≥0∞) :=
        congrArg ENNReal.ofNNReal (htr_prep.trans (CQState.trace_qSet Δ))
      rw [hmass] at hcost; refine hcost.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hB
  refine ⟨fun Δ => ?_, fun Δ => (hmain Δ).2⟩; rw [expect_top, (hmain Δ).1]
/-- Computable cell-validity predicate for the certified `(m = 2, k = 4)` `WarmJP01` cell. -/
@[expose] def validCellWarmJP01 (m k : ℕ) : Bool :=
  (m == 2) && (k == 4)
/-- Claimed relative cost `ℚ≥0` on `(m = 2, k = 4)` (`B = 8192`). -/
@[expose] def relCostWarmJP01 (m k : ℕ) : ℚ≥0 :=
  if m == 2 then
    if k == 4 then NNRat.divNat 635653074817 1000000000000
    else 1
  else 1
/-- Top-level `m = 2` `WarmJP01` `FindAll` circuit (`n ≥ 200`, `k = 4`). -/
noncomputable def findAllWarmJP01M2Circuit {Var : Type} (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  match m with
  | 2 =>
      if 200 ≤ n ∧ validCellWarmJP01 2 k = true then
        cswapWarmJP01FindAllCircuit res (phiFnOfWmSt jp01St_2) n k
      else
        findAllLockCircuit res n 2 k
  | m =>
      findAllLockCircuit res n m k
private theorem validCellWarmJP01_cases {m k : ℕ} (hmk : validCellWarmJP01 m k = true) :
    m = 2 ∧ k = 4 := by
  dsimp only [validCellWarmJP01] at hmk
  simp only [Bool.and_eq_true, beq_iff_eq] at hmk; exact hmk
theorem findAllWarmJP01M2_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
  (hn : 1 ≤ n) (hmk : validCellWarmJP01 m k = true) (hkN : k ≤ 2 ^ n)
  {S : Finset (Fin (2 ^ n))} (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
  ⦃ (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) ⦄
    (QProg.qSet ;; (findAllWarmJP01M2Circuit res n m k).compile QProg.qAssign
      (parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ => decodeTargetsLocal n k (σ res) = S) ⦄ := by
  cases Nat.eq_zero_or_pos n with
  | inl hn0 => exact absurd (hn0 ▸ hn) (by omega)
  | inr _ =>
  obtain ⟨rfl, rfl⟩ := validCellWarmJP01_cases hmk; have hScard : S.card = 4 :=
    (Finset.mem_powersetCard.1 hS).2; dsimp only [findAllWarmJP01M2Circuit]
  by_cases hc : 200 ≤ n ∧ validCellWarmJP01 2 4 = true
  · rw [ite_eq_left hc]
    obtain ⟨hΦ, hB⟩ := validWarmJP01M2Potential_of_checkWarmJP01CellCert cert_warmJP01_r2Table
      cert_warmJP01Cell_2 hc.1
    have hB_nn : 0 ≤ (((jp01RcNum12_2 : ℚ≥0) / 1000000000000 : ℚ≥0) : ℝ) * ((π / 4) * (∑ r ∈
      Finset.Icc (1 : ℕ) (2 ^ 2), 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ))) := mul_nonneg
      (by positivity) (mul_nonneg (mul_nonneg (by linarith [Real.pi_pos]) (Finset.sum_nonneg fun _
      _ => by positivity)) (Real.sqrt_nonneg _))
    exact (cswapWarmJP01FindAllProgram_correctness_and_costBound res hc.1 (by omega) (by omega) hΦ
      hScard (B := ⟨_, hB_nn⟩) hB).1
  · rw [ite_eq_right hc]
    have hgrid : isGridCell 2 4 = true := rfl
    exact findAllLock_correctness res hgrid hkN hS
theorem findAllWarmJP01M2_costBound_uniform {Var : Type} [DecidableEq Var] (res : Var)
  {m k n : ℕ} (hmk : validCellWarmJP01 m k = true) (hn : 200 ≤ n) :
  ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
    (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
      CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
        (QProg.qSet ;; (findAllWarmJP01M2Circuit res n m k).compile QProg.qAssign
          (parallelMarkingOracle m S)) (q S)) ∧
    (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
      ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
      ((relCostWarmJP01 m k : ℚ≥0) : ℝ) *
        ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  obtain ⟨rfl, rfl⟩ := validCellWarmJP01_cases hmk
  have hc : 200 ≤ n ∧ validCellWarmJP01 2 4 = true := ⟨hn, hmk⟩
  set bound : ℝ := ((relCostWarmJP01 2 4 : ℚ≥0) : ℝ) *
    ((π / 4) * (∑ r ∈ Finset.Icc (1 : ℕ) 4, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (2 : ℕ)))
  have hbound_nn : 0 ≤ bound := mul_nonneg (by positivity) (mul_nonneg (mul_nonneg
    (by linarith [Real.pi_pos]) (Finset.sum_nonneg fun _ _ => by positivity)) (Real.sqrt_nonneg _))
  let B : ℝ≥0 := ⟨bound, hbound_nn⟩; refine ⟨fun _ => B, fun S hS => ?_, ?_⟩
  · have hScard : S.card = 4 := (Finset.mem_powersetCard.1 hS).2
    dsimp only [findAllWarmJP01M2Circuit]; rw [ite_eq_left hc]
    obtain ⟨hΦ, hB⟩ := validWarmJP01M2Potential_of_checkWarmJP01CellCert cert_warmJP01_r2Table
      cert_warmJP01Cell_2 hn
    have hrc_eq : (relCostWarmJP01 2 4 : ℚ≥0) = (jp01RcNum12_2 : ℚ≥0) / 1000000000000 := by
      apply NNRat.ext; dsimp only [relCostWarmJP01, jp01RcNum12_2]
      simp only [NNRat.divNat_eq_div]; push_cast; norm_num
    have hB' : warmJP01Potential jp01B_2 warmJP01V2Mono jp01St_2 jp01W_2 n 4
      (fun _ => halfAngleSet n 4) ≤ B :=
      by change _ ≤ bound; dsimp only [bound]; rw [hrc_eq]; exact hB
    exact (cswapWarmJP01FindAllProgram_correctness_and_costBound res hn (by omega) (by omega) hΦ
      hScard (B := B) hB').2
  · rw [Finset.sum_const, nsmul_eq_mul]
    by_cases h0 : (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard 4).card : ℝ) = 0
    · rw [h0, zero_mul, zero_div]; exact hbound_nn
    · rw [mul_div_cancel_left₀ _ h0]; exact le_rfl
end QuantumComputation.Specs.GroverFindAll.Warm2
namespace QuantumComputation.Specs.GroverFindAll
open Operator ResourceCounting Real QProg QProg.Notation
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal QHLExpectation
/-- Computable cost profile for the certified `(m = 2, k = 4)` `WarmJP01` cell (`n ≥ 200`). -/
@[expose] def warmJP01Profile : FindAllCostProfile where
  validCell := Warm2.validCellWarmJP01
  relCost := Warm2.relCostWarmJP01
  n0 _ _ := 200
/-- Composable `ValidFindAllFamily` instance for `WarmJP01` (`k = 4`). -/
theorem validFamily_warmJP01 {Var : Type} [DecidableEq Var] (res : Var) :
    ValidFindAllFamily res warmJP01Profile (Warm2.findAllWarmJP01M2Circuit res) where
  correctness hn _hgrid hvalid hkN hS := Warm2.findAllWarmJP01M2_correctness res hn hvalid hkN hS
  costBound_uniform _hgrid hvalid _n hn _hkN :=
    Warm2.findAllWarmJP01M2_costBound_uniform res hvalid hn
end QuantumComputation.Specs.GroverFindAll
end
