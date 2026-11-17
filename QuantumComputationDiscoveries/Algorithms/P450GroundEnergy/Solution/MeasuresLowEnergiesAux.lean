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

public import Mathlib.Analysis.Matrix.Spectrum
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs

/-!
# Parametric End-to-End `MeasuresLowEnergies` Proof

Provides a self-contained proof of `MeasuresLowEnergies_local` (definitionally equal
to `QuantumComputation.Specs.MeasuresLowEnergies`) parametric over any system width `k`, ancilla
width `m_anc`, QPE register width `b_qpe`, Hamiltonian `H : Operator (2 ^ k)`, spectral bounds
`(E_LB, Λ, E_ref, E_UB, E_gap)`, QPE chordal standard deviation `σ_qpe`, and implementation
perturbation `δ_tot`:

1. **Sector Equivalence Bridge (`MeasuresLowEnergies_of_agreesOnSector`):** Any effective
   Hamiltonian `H_eff` that agrees with `H` on `electronSectorProjector k η` (such as native
   `thcHamiltonian dfthc` or a `63`-electron BLISS-shifted Hamiltonian) transfers
   `MeasuresLowEnergies_local` identically.
2. **Symmetric Doubled-Phase Decoder & Global `S¹` Chordal Lipschitz Inequality:** Maps QPE outcome
   `y : Fin (2 ^ b_qpe)` with angle `θ(y) = 2π y / 2^b_qpe` via `foldAngle θ = min θ (2π - θ)` and
   `φ_hat(y) = foldAngle(θ(y)) / 2` to `E_LB + Λ (1 - cos φ_hat(y))`. Proves globally on all of
   `θ ∈ [0, 2π]` and for all `E ∈ [E_LB, E_LB + 2Λ - E_gap]` on **both** `+2φ` and `-2φ` walk
   branches that
   `|min (decode y) T - min E T| ≤ (√(E_gap (2Λ - E_gap)) / 2) * (2 |sin((θ(y) ∓ 2φ) / 2)|)`.
3. **Rayleigh–Ritz & SOS Bridges:** Converts any normalized `η`-electron variational witness
   `ψ_ref` with `(star ψ_ref ⬝ᵥ (H *ᵥ ψ_ref)).re ≤ E_ref` into an `η`-electron eigenstate bound
   `E₀ ≤ E_ref` (hence `T ≤ E_ref + Δ`), and converts any SOS decomposition
   `H - E_LB • 1 = (2Λ) • (Bᴴ * B)` with `‖B‖ ≤ 1` into `E_LB ≤ E ≤ E_LB + 2Λ`.
4. **Orthogonal Branch Additivity & `E_gap * δ_tot` Hilbert-Space Perturbation Bridge:** Combines
   orthogonal `+2φ` / `-2φ` walk branches on `W_ideal` with the `EuclideanSpace` triangle inequality
   on the capped error vector (`|min (estimate a) T - min E T| ≤ E_gap` for all `T : ℝ`), bounding
   total root-mean-square error by `(√(E_gap (2Λ - E_gap)) / 2) * σ_qpe + E_gap * δ_tot ≤ ε`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix
open scoped Matrix BigOperators Real

/-! ## Sector Equivalence Bridge -/

/-- Discrete QPE grid angle `θ(y) = 2π y / 2^b_qpe ∈ [0, 2π)`. -/
noncomputable def qpeAngle (b_qpe : ℕ) (y : Fin (2 ^ b_qpe)) : ℝ :=
  2 * π * (y.val : ℝ) / (2 ^ b_qpe : ℝ)

/-- Symmetric circle fold `ψ_fold(θ) = min θ (2π - θ)` mapping `[0, 2π]` into `[0, π]`. -/
noncomputable def foldAngle (θ : ℝ) : ℝ :=
  min θ (2 * π - θ)

/-- Estimated walk half-phase `φ_hat(y) = foldAngle(θ(y)) / 2 ∈ [0, π/2]`. -/
noncomputable def qpeHalfPhase (b_qpe : ℕ) (y : Fin (2 ^ b_qpe)) : ℝ :=
  foldAngle (qpeAngle b_qpe y) / 2

/-- Decoded energy `E_LB + Λ (1 - cos φ_hat(y))` for doubled-phase spectral-amplification QPE. -/
noncomputable def qpeDecodeEnergy (E_LB Λ : ℝ) (b_qpe : ℕ) (y : Fin (2 ^ b_qpe)) : ℝ :=
  E_LB + Λ * (1 - Real.cos (qpeHalfPhase b_qpe y))

/-- Ancilla-register energy estimator extracting QPE outcome via `extractQPE`. -/
noncomputable def qpeEstimate {m_anc : ℕ} (E_LB Λ : ℝ) (b_qpe : ℕ)
    (extractQPE : Fin (2 ^ m_anc) → Fin (2 ^ b_qpe)) (a : Fin (2 ^ m_anc)) : ℝ :=
  qpeDecodeEnergy E_LB Λ b_qpe (extractQPE a)

/-- Effective spectral-amplification scale `λ_eff = √(E_gap * (2Λ - E_gap))` (Low et al. 2025,
Eq. 11). -/
noncomputable def spectralAmpEffNorm (Λ E_gap : ℝ) : ℝ :=
  √(E_gap * (2 * Λ - E_gap))

/-! ## Global `S¹` Chordal Lipschitz Inequality on Both `±2φ` Walk Branches -/

/-- On `[0, 2π]`, `cos (foldAngle θ / 2)` equals `|cos (θ / 2)|`. -/
theorem cos_foldAngle_div_two {θ : ℝ} (h0 : 0 ≤ θ) (h2pi : θ ≤ 2 * π) :
    Real.cos (foldAngle θ / 2) = |Real.cos (θ / 2)| := by
  unfold foldAngle
  by_cases hle : θ ≤ 2 * π - θ
  · rw [min_eq_left hle]
    have hnonneg : 0 ≤ Real.cos (θ / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
    exact (abs_of_nonneg hnonneg).symm
  · rw [min_eq_right (le_of_not_ge hle), show (2 * π - θ) / 2 = π - θ / 2 by ring]
    have hnonneg : 0 ≤ Real.cos (π - θ / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    rw [Real.cos_pi_sub] at hnonneg ⊢
    exact (abs_of_nonpos (by linarith)).symm

theorem qpeAngle_nonneg (b_qpe : ℕ) (y : Fin (2 ^ b_qpe)) : 0 ≤ qpeAngle b_qpe y := by
  unfold qpeAngle
  positivity

theorem qpeAngle_le_two_pi (b_qpe : ℕ) (y : Fin (2 ^ b_qpe)) :
    qpeAngle b_qpe y ≤ 2 * π := by
  unfold qpeAngle
  have hy : (y.val : ℝ) ≤ (2 ^ b_qpe : ℝ) := by exact_mod_cast le_of_lt y.isLt
  have hpow : (0 : ℝ) < 2 ^ b_qpe := by positivity
  rw [div_le_iff₀ hpow]
  nlinarith [Real.pi_pos]

theorem le_qpeDecodeEnergy {E_LB Λ : ℝ} (hΛ : 0 ≤ Λ) (b_qpe : ℕ) (y : Fin (2 ^ b_qpe)) :
    E_LB ≤ qpeDecodeEnergy E_LB Λ b_qpe y := by
  unfold qpeDecodeEnergy
  nlinarith [Real.cos_le_one (qpeHalfPhase b_qpe y)]

private lemma max_abs_cos_sub_le_of_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {x y : ℝ}
    (hxy : |Real.cos y| ≤ |Real.cos x|) :
    max |Real.cos x| γ - max |Real.cos y| γ ≤ √(1 - γ ^ 2) * |Real.sin (x - y)| := by
  by_cases hx : |Real.cos x| ≤ γ
  · rw [max_eq_right hx, max_eq_right (hxy.trans hx), sub_self]
    positivity
  · push Not at hx
    rw [max_eq_left hx.le]
    by_cases hy : γ ≤ |Real.cos y|
    · rw [max_eq_left hy]
      have hcos_eq : Real.cos x =
          Real.cos y * Real.cos (x - y) - Real.sin y * Real.sin (x - y) := by
        calc Real.cos x = Real.cos (y + (x - y)) := by ring_nf
          _ = Real.cos y * Real.cos (x - y) - Real.sin y * Real.sin (x - y) :=
              Real.cos_add y (x - y)
      have htri : |Real.cos x| ≤ |Real.cos y| * |Real.cos (x - y)| +
          |Real.sin y| * |Real.sin (x - y)| := by
        rw [hcos_eq]
        exact (abs_sub _ _).trans (by rw [abs_mul, abs_mul])
      have hcos_le : |Real.cos y| * |Real.cos (x - y)| ≤ |Real.cos y| :=
        mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
      have hsin_sq : Real.sin y ^ 2 ≤ 1 - γ ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq y, sq_abs (Real.cos y)]
      have hsin_le : |Real.sin y| ≤ √(1 - γ ^ 2) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsin_sq
      nlinarith [abs_nonneg (Real.sin (x - y))]
    · push Not at hy
      rw [max_eq_right hy.le]
      let s := √(1 - γ ^ 2)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs_sq : s ^ 2 = 1 - γ ^ 2 := Real.sq_sqrt (by nlinarith)
      have hsin_eq : Real.cos x * Real.sin y =
          Real.sin x * Real.cos y - Real.sin (x - y) := by
        linarith [Real.sin_sub x y]
      have htri : |Real.cos x| * |Real.sin y| ≤
          |Real.sin x| * |Real.cos y| + |Real.sin (x - y)| := by
        calc |Real.cos x| * |Real.sin y|
            = |Real.cos x * Real.sin y| := (abs_mul _ _).symm
          _ = |Real.sin x * Real.cos y - Real.sin (x - y)| := by rw [hsin_eq]
          _ ≤ |Real.sin x * Real.cos y| + |Real.sin (x - y)| := abs_sub _ _
          _ = |Real.sin x| * |Real.cos y| + |Real.sin (x - y)| := by rw [abs_mul]
      have hsin_ge : s ≤ |Real.sin y| := by
        have hsq : 1 - γ ^ 2 ≤ Real.sin y ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq y, sq_abs (Real.cos y), abs_nonneg (Real.cos y)]
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsq
      have hstep : |Real.cos x| * s ≤ |Real.sin x| * γ + |Real.sin (x - y)| := by
        nlinarith [abs_nonneg (Real.cos x), abs_nonneg (Real.sin x)]
      have hcs_sq : (γ * |Real.cos x| + s * |Real.sin x|) ^ 2 +
          (s * |Real.cos x| - γ * |Real.sin x|) ^ 2 = 1 := by
        nlinarith [sq_abs (Real.cos x), sq_abs (Real.sin x), Real.sin_sq_add_cos_sq x, hs_sq]
      have hcs : γ * |Real.cos x| + s * |Real.sin x| ≤ 1 := by
        nlinarith [sq_nonneg (s * |Real.cos x| - γ * |Real.sin x|),
          abs_nonneg (Real.cos x), abs_nonneg (Real.sin x)]
      nlinarith

/-- Universal chordal Lipschitz inequality for `max |cos ·| γ`: for every `γ ∈ [0, 1]` and all real
`x, y`, `|max |cos x| γ - max |cos y| γ| ≤ √(1 - γ²) * |sin (x - y)|`. -/
theorem abs_max_abs_cos_sub_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (x y : ℝ) :
    |max |Real.cos x| γ - max |Real.cos y| γ| ≤ √(1 - γ ^ 2) * |Real.sin (x - y)| := by
  rcases le_total |Real.cos y| |Real.cos x| with hxy | hyx
  · have hnonneg : 0 ≤ max |Real.cos x| γ - max |Real.cos y| γ :=
      sub_nonneg.mpr (max_le_max_right γ hxy)
    rw [abs_of_nonneg hnonneg]
    exact max_abs_cos_sub_le_of_le hγ0 hγ1 hxy
  · have hnonneg : 0 ≤ max |Real.cos y| γ - max |Real.cos x| γ :=
      sub_nonneg.mpr (max_le_max_right γ hyx)
    rw [abs_sub_comm, abs_of_nonneg hnonneg]
    have h := max_abs_cos_sub_le_of_le hγ0 hγ1 hyx
    rwa [show y - x = -(x - y) by ring, Real.sin_neg, abs_neg] at h

/-- Global chordal Lipschitz inequality for doubled-phase energy decoding across `[0, 2π]` and all
non-aliased energies `E ≤ E_LB + 2Λ - E_gap`, simultaneously covering every target phase `α` with
`|cos (α / 2)| = |cos φ|` (in particular `α = +2φ` and `α = -2φ`). -/
theorem abs_min_foldAngle_energy_sub_min_le {E_LB Λ E_gap T E φ θ α : ℝ}
    (hΛ : 0 < Λ) (hgap0 : 0 ≤ E_gap) (hgapΛ : E_gap ≤ Λ)
    (hT : T ≤ E_LB + E_gap) (hφ : E = E_LB + Λ * (1 - Real.cos φ))
    (hE_ub : E ≤ E_LB + 2 * Λ - E_gap)
    (hθ0 : 0 ≤ θ) (hθ2pi : θ ≤ 2 * π)
    (hα : |Real.cos (α / 2)| = |Real.cos φ|) :
    |min (E_LB + Λ * (1 - Real.cos (foldAngle θ / 2))) T - min E T| ≤
      spectralAmpEffNorm Λ E_gap * |Real.sin ((θ - α) / 2)| := by
  rw [cos_foldAngle_div_two hθ0 hθ2pi]
  have hminE : min E T = min (E_LB + Λ * (1 - |Real.cos φ|)) T := by
    by_cases hcos : 0 ≤ Real.cos φ
    · rw [abs_of_nonneg hcos, ← hφ]
    · push Not at hcos
      rw [abs_of_neg hcos, min_eq_right (by nlinarith), min_eq_right (by nlinarith)]
  rw [hminE, ← hα]
  by_cases hT_low : T ≤ E_LB
  · have hest_ge : T ≤ E_LB + Λ * (1 - |Real.cos (θ / 2)|) := by
      nlinarith [Real.abs_cos_le_one (θ / 2)]
    have htar_ge : T ≤ E_LB + Λ * (1 - |Real.cos (α / 2)|) := by
      nlinarith [Real.abs_cos_le_one (α / 2)]
    rw [min_eq_right hest_ge, min_eq_right htar_ge, sub_self, abs_zero]
    unfold spectralAmpEffNorm
    positivity
  · push Not at hT_low
    let g := T - E_LB
    have hg0 : 0 ≤ g := by linarith
    have hg_le : g ≤ E_gap := by linarith
    let γ := 1 - g / Λ
    have hγ0 : 0 ≤ γ := by
      rw [sub_nonneg, div_le_one hΛ]
      linarith
    have hγ1 : γ ≤ 1 := by
      have : 0 ≤ g / Λ := div_nonneg hg0 hΛ.le
      linarith
    have hΛγ : Λ * (1 - γ) = g := by
      dsimp [γ]
      field_simp
      ring
    have hmin_eq (c : ℝ) : min (E_LB + Λ * (1 - c)) T = E_LB + Λ * (1 - max c γ) := by
      have hT_eq : T = E_LB + Λ * (1 - γ) := by linarith
      rw [hT_eq]
      by_cases hc : c ≤ γ
      · rw [max_eq_right hc, min_eq_right (by nlinarith)]
      · push Not at hc
        rw [max_eq_left hc.le, min_eq_left (by nlinarith)]
    rw [hmin_eq |Real.cos (θ / 2)|, hmin_eq |Real.cos (α / 2)|,
      show (E_LB + Λ * (1 - max |Real.cos (θ / 2)| γ)) -
        (E_LB + Λ * (1 - max |Real.cos (α / 2)| γ)) =
        -(Λ * (max |Real.cos (θ / 2)| γ - max |Real.cos (α / 2)| γ)) by ring,
      abs_neg, abs_mul, abs_of_pos hΛ]
    have htrig := abs_max_abs_cos_sub_le hγ0 hγ1 (θ / 2) (α / 2)
    rw [show θ / 2 - α / 2 = (θ - α) / 2 by ring] at htrig
    have hscale : Λ * √(1 - γ ^ 2) ≤ spectralAmpEffNorm Λ E_gap := by
      unfold spectralAmpEffNorm
      have hnonneg : 0 ≤ Λ * √(1 - γ ^ 2) := by positivity
      have hsq : (Λ * √(1 - γ ^ 2)) ^ 2 ≤ E_gap * (2 * Λ - E_gap) := by
        rw [mul_pow, Real.sq_sqrt (by nlinarith)]
        have h1 : Λ * γ = Λ - g := by linarith
        have h2 : Λ ^ 2 * (1 - γ ^ 2) = g * (2 * Λ - g) := by nlinarith
        have h3 : 0 ≤ (E_gap - g) * (2 * Λ - E_gap - g) :=
          mul_nonneg (sub_nonneg.mpr hg_le) (by linarith)
        nlinarith
      rw [← Real.sqrt_sq hnonneg]
      exact Real.sqrt_le_sqrt hsq
    calc Λ * |max |Real.cos (θ / 2)| γ - max |Real.cos (α / 2)| γ|
        ≤ Λ * (√(1 - γ ^ 2) * |Real.sin ((θ - α) / 2)|) :=
          mul_le_mul_of_nonneg_left htrig hΛ.le
      _ = (Λ * √(1 - γ ^ 2)) * |Real.sin ((θ - α) / 2)| := by ring
      _ ≤ spectralAmpEffNorm Λ E_gap * |Real.sin ((θ - α) / 2)| :=
          mul_le_mul_of_nonneg_right hscale (abs_nonneg _)

/-- Squared chordal error bound on the `+2φ` walk branch for `qpeDecodeEnergy`. -/
theorem sq_min_qpeDecodeEnergy_sub_min_le_pos {E_LB Λ E_gap T E φ : ℝ} {b_qpe : ℕ}
    (y : Fin (2 ^ b_qpe)) (hΛ : 0 < Λ) (hgap0 : 0 ≤ E_gap) (hgapΛ : E_gap ≤ Λ)
    (hT : T ≤ E_LB + E_gap) (hφ : E = E_LB + Λ * (1 - Real.cos φ))
    (hE_ub : E ≤ E_LB + 2 * Λ - E_gap) :
    (min (qpeDecodeEnergy E_LB Λ b_qpe y) T - min E T) ^ 2 ≤
      (spectralAmpEffNorm Λ E_gap / 2) ^ 2 *
        (4 * Real.sin ((qpeAngle b_qpe y - 2 * φ) / 2) ^ 2) := by
  have habs := abs_min_foldAngle_energy_sub_min_le hΛ hgap0 hgapΛ hT hφ hE_ub
    (qpeAngle_nonneg b_qpe y) (qpeAngle_le_two_pi b_qpe y)
    (α := 2 * φ) (by rw [mul_div_cancel_left₀ φ two_ne_zero])
  have hsq : |min (qpeDecodeEnergy E_LB Λ b_qpe y) T - min E T| ^ 2 ≤
      (spectralAmpEffNorm Λ E_gap * |Real.sin ((qpeAngle b_qpe y - 2 * φ) / 2)|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs, mul_pow, sq_abs] at hsq
  linarith

/-- Pointwise worst-case bound `|min est T - min E T| ≤ E_gap` for all `T : ℝ` (including
`T < E_LB`) whenever `E_LB ≤ est`, `E_LB ≤ E`, and `T ≤ E_LB + E_gap`. -/
theorem abs_min_sub_min_le_gap {E_LB E_gap T est E : ℝ}
    (hgap0 : 0 ≤ E_gap) (hest : E_LB ≤ est) (hE : E_LB ≤ E) (hT : T ≤ E_LB + E_gap) :
    |min est T - min E T| ≤ E_gap := by
  by_cases hT_low : T ≤ E_LB
  · rw [min_eq_right (hT_low.trans hest), min_eq_right (hT_low.trans hE), sub_self, abs_zero]
    exact hgap0
  · push Not at hT_low
    have h1 : E_LB ≤ min est T := le_min hest hT_low.le
    have h2 : min est T ≤ E_LB + E_gap := (min_le_right est T).trans hT
    have h3 : E_LB ≤ min E T := le_min hE hT_low.le
    have h4 : min E T ≤ E_LB + E_gap := (min_le_right E T).trans hT
    exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem electronSectorProjector_isHermitian (k η : ℕ) :
    (electronSectorProjector k η).IsHermitian := by
  ext i j
  simp only [electronSectorProjector, conjTranspose_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    split_ifs <;> simp
  · simp [hij, Ne.symm hij]

private theorem electronSectorProjector_mul_self (k η : ℕ) :
    electronSectorProjector k η * electronSectorProjector k η = electronSectorProjector k η := by
  ext i j
  simp only [electronSectorProjector, diagonal_mul_diagonal, diagonal_apply]
  split_ifs <;> simp

/-- Rayleigh–Ritz theorem restricted to the `η`-electron sector: if a Hermitian Hamiltonian `H`
commutes with `electronSectorProjector k η` and admits a normalized `η`-electron state `ψ_ref` with
variational energy `(star ψ_ref ⬝ᵥ (H *ᵥ ψ_ref)).re ≤ E_ref`, then `H` has a nonzero `η`-electron
eigenvector with eigenvalue `E₀ ≤ E_ref`. -/
theorem exists_isEigen_le_of_variational {k η : ℕ} {H : Operator (2 ^ k)} {E_ref : ℝ}
    (hH : H.IsHermitian)
    (hHP : H * electronSectorProjector k η = electronSectorProjector k η * H)
    (ψ_ref : Fin (2 ^ k) → ℂ)
    (hψ_sec : electronSectorProjector k η *ᵥ ψ_ref = ψ_ref)
    (hψ_norm : ∑ i, Complex.normSq (ψ_ref i) = 1)
    (hψ_energy : (star ψ_ref ⬝ᵥ (H *ᵥ ψ_ref)).re ≤ E_ref) :
    ∃ (E₀ : ℝ) (φ₀ : Fin (2 ^ k) → ℂ),
      (H *ᵥ φ₀ = (E₀ : ℂ) • φ₀ ∧ electronSectorProjector k η *ᵥ φ₀ = φ₀ ∧ φ₀ ≠ 0) ∧
        E₀ ≤ E_ref := by
  let P := electronSectorProjector k η
  have hP_herm : P.IsHermitian := electronSectorProjector_isHermitian k η
  have hP_idem : P * P = P := electronSectorProjector_mul_self k η
  let M_pen : ℝ := E_ref + 1
  let H_pen : Operator (2 ^ k) := P * H * P + (M_pen : ℂ) • (1 - P)
  have hH_pen : H_pen.IsHermitian := by
    change H_penᴴ = H_pen
    simp [H_pen, hP_herm.eq, hH.eq, Matrix.mul_assoc]
  have h1mP_ψ : (1 - P) *ᵥ ψ_ref = 0 := by
    rw [sub_mulVec, one_mulVec, hψ_sec, sub_self]
  have hPHP_ψ : (P * H * P) *ᵥ ψ_ref = H *ᵥ ψ_ref := by
    calc ((P * H) * P) *ᵥ ψ_ref
        = (P * H) *ᵥ (P *ᵥ ψ_ref) := (mulVec_mulVec ψ_ref (P * H) P).symm
      _ = (P * H) *ᵥ ψ_ref := by rw [hψ_sec]
      _ = (H * P) *ᵥ ψ_ref := by rw [← hHP]
      _ = H *ᵥ (P *ᵥ ψ_ref) := (mulVec_mulVec ψ_ref H P).symm
      _ = H *ᵥ ψ_ref := by rw [hψ_sec]
  have hH_pen_ψ : H_pen *ᵥ ψ_ref = H *ᵥ ψ_ref := by
    dsimp [H_pen]
    rw [add_mulVec, hPHP_ψ, smul_mulVec, h1mP_ψ, smul_zero, add_zero]
  let U : Unitary (2 ^ k) := hH_pen.eigenvectorUnitary
  let c : Fin (2 ^ k) → ℂ := U.1ᴴ *ᵥ ψ_ref
  have hc_norm : ∑ j, Complex.normSq (c j) = 1 := by
    have h := sum_normSq_unitary_mulVec U⁻¹ ψ_ref
    have hinv : (U⁻¹).1 = U.1ᴴ := by
      rw [← Matrix.star_eq_conjTranspose]
      rfl
    rwa [hinv, hψ_norm] at h
  have hUc : U.1 *ᵥ c = ψ_ref := by
    dsimp [c]
    rw [mulVec_mulVec]
    have hUU : U.1 * U.1ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem U.2
    rw [hUU, one_mulVec]
  have hH_pen_diag : H_pen =
      U.1 * diagonal (RCLike.ofReal ∘ hH_pen.eigenvalues) * U.1ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hH_pen.spectral_theorem
  have hexp : (star ψ_ref ⬝ᵥ (H_pen *ᵥ ψ_ref)).re =
      ∑ j, Complex.normSq (c j) * hH_pen.eigenvalues j := by
    have h1 : H_pen *ᵥ ψ_ref =
        U.1 *ᵥ (diagonal (RCLike.ofReal ∘ hH_pen.eigenvalues) *ᵥ c) := by
      calc H_pen *ᵥ ψ_ref
          = (U.1 * diagonal (RCLike.ofReal ∘ hH_pen.eigenvalues) * U.1ᴴ) *ᵥ ψ_ref := by
              rw [← hH_pen_diag]
        _ = (U.1 * diagonal (RCLike.ofReal ∘ hH_pen.eigenvalues)) *ᵥ c :=
              (mulVec_mulVec ψ_ref _ U.1ᴴ).symm
        _ = U.1 *ᵥ (diagonal (RCLike.ofReal ∘ hH_pen.eigenvalues) *ᵥ c) :=
              (mulVec_mulVec c U.1 _).symm
    rw [h1, ← hUc, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    have hUU : U.1ᴴ * U.1 = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
    rw [hUU, Matrix.vecMul_one]
    simp only [dotProduct, Pi.star_apply, mulVec_diagonal, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show star (c j) * ((hH_pen.eigenvalues j : ℂ) * c j) =
      (star (c j) * c j) * (hH_pen.eigenvalues j : ℂ) by ring,
      Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hexists_j : ∃ j, hH_pen.eigenvalues j ≤ E_ref := by
    by_contra! hall
    have hc_ne : ∃ j₀, 0 < Complex.normSq (c j₀) := by
      by_contra! hzero
      have hsum0 : ∑ j, Complex.normSq (c j) = 0 :=
        Finset.sum_eq_zero fun j _ ↦ le_antisymm (hzero j) (Complex.normSq_nonneg _)
      linarith
    obtain ⟨j₀, hj₀⟩ := hc_ne
    have hlt : ∑ j, Complex.normSq (c j) * E_ref <
        ∑ j, Complex.normSq (c j) * hH_pen.eigenvalues j := by
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨j₀, Finset.mem_univ j₀, ?_⟩
      · exact mul_le_mul_of_nonneg_left (hall j).le (Complex.normSq_nonneg _)
      · exact mul_lt_mul_of_pos_left (hall j₀) hj₀
    rw [← Finset.sum_mul, hc_norm, one_mul] at hlt
    rw [hH_pen_ψ] at hexp
    linarith
  obtain ⟨j, hj⟩ := hexists_j
  let φ₀ : Fin (2 ^ k) → ℂ := ⇑(hH_pen.eigenvectorBasis j)
  let E₀ : ℝ := hH_pen.eigenvalues j
  have hφ₀_ne : φ₀ ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hH_pen.eigenvectorBasis.orthonormal.ne_zero j)
  have hφ₀_eig : H_pen *ᵥ φ₀ = (E₀ : ℂ) • φ₀ := by
    have h := hH_pen.mulVec_eigenvectorBasis j
    dsimp only [φ₀, E₀]
    rw [h]
    ext i
    simp [Complex.real_smul]
  have h1mP_Hpen : (1 - P) * H_pen = (M_pen : ℂ) • (1 - P) := by
    dsimp [H_pen]
    have h1mP_P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP_idem, sub_self]
    have h1mP_PHP : (1 - P) * (P * H * P) = 0 := by
      calc (1 - P) * ((P * H) * P)
          = (((1 - P) * P) * H) * P := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [h1mP_P, zero_mul, zero_mul]
    have h1mP_idem : (1 - P) * (1 - P) = 1 - P := by
      rw [mul_sub, mul_one, sub_mul, one_mul, hP_idem, sub_self, sub_zero]
    rw [mul_add, h1mP_PHP, zero_add, mul_smul_comm, h1mP_idem]
  have h1mP_φ₀ : (1 - P) *ᵥ φ₀ = 0 := by
    have hpen : (M_pen : ℂ) • ((1 - P) *ᵥ φ₀) = (E₀ : ℂ) • ((1 - P) *ᵥ φ₀) := by
      calc (M_pen : ℂ) • ((1 - P) *ᵥ φ₀)
          = ((M_pen : ℂ) • (1 - P)) *ᵥ φ₀ := (smul_mulVec _ _ _).symm
        _ = ((1 - P) * H_pen) *ᵥ φ₀ := by rw [h1mP_Hpen]
        _ = (1 - P) *ᵥ (H_pen *ᵥ φ₀) := (mulVec_mulVec _ _ _).symm
        _ = (1 - P) *ᵥ ((E₀ : ℂ) • φ₀) := by rw [hφ₀_eig]
        _ = (E₀ : ℂ) • ((1 - P) *ᵥ φ₀) := mulVec_smul _ _ _
    have hdiff : ((M_pen - E₀ : ℝ) : ℂ) • ((1 - P) *ᵥ φ₀) = 0 := by
      rw [Complex.ofReal_sub, sub_smul, hpen, sub_self]
    have hne : ((M_pen - E₀ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by dsimp [M_pen]; linarith)
    exact (smul_eq_zero.mp hdiff).resolve_left hne
  have hP_φ₀ : P *ᵥ φ₀ = φ₀ := by
    rw [sub_mulVec, one_mulVec] at h1mP_φ₀
    exact (sub_eq_zero.mp h1mP_φ₀).symm
  have hH_φ₀ : H *ᵥ φ₀ = (E₀ : ℂ) • φ₀ := by
    have hPHP_φ₀ : (P * H * P) *ᵥ φ₀ = H *ᵥ φ₀ := by
      calc ((P * H) * P) *ᵥ φ₀
          = (P * H) *ᵥ (P *ᵥ φ₀) := (mulVec_mulVec φ₀ (P * H) P).symm
        _ = (P * H) *ᵥ φ₀ := by rw [hP_φ₀]
        _ = (H * P) *ᵥ φ₀ := by rw [← hHP]
        _ = H *ᵥ (P *ᵥ φ₀) := (mulVec_mulVec φ₀ H P).symm
        _ = H *ᵥ φ₀ := by rw [hP_φ₀]
    have hEq : H_pen *ᵥ φ₀ = H *ᵥ φ₀ := by
      dsimp [H_pen]
      rw [add_mulVec, hPHP_φ₀, smul_mulVec, h1mP_φ₀, smul_zero, add_zero]
    rwa [hEq] at hφ₀_eig
  exact ⟨E₀, φ₀, ⟨hH_φ₀, hP_φ₀, hφ₀_ne⟩, hj⟩

/-- Immediate threshold corollary of `exists_isEigen_le_of_variational`: any threshold `T`
satisfying `∀ E' φ, IsEigen E' φ → T ≤ E' + Δ` obeys `T ≤ E_ref + Δ`. -/
theorem threshold_le_add_of_variational {k η : ℕ} {H : Operator (2 ^ k)} {E_ref Δ T : ℝ}
    (hH : H.IsHermitian)
    (hHP : H * electronSectorProjector k η = electronSectorProjector k η * H)
    (ψ_ref : Fin (2 ^ k) → ℂ)
    (hψ_sec : electronSectorProjector k η *ᵥ ψ_ref = ψ_ref)
    (hψ_norm : ∑ i, Complex.normSq (ψ_ref i) = 1)
    (hψ_energy : (star ψ_ref ⬝ᵥ (H *ᵥ ψ_ref)).re ≤ E_ref)
    (hT : ∀ (E' : ℝ) (φ : Fin (2 ^ k) → ℂ),
      (H *ᵥ φ = (E' : ℂ) • φ ∧ electronSectorProjector k η *ᵥ φ = φ ∧ φ ≠ 0) → T ≤ E' + Δ) :
    T ≤ E_ref + Δ := by
  obtain ⟨E₀, φ₀, hEig, hle⟩ :=
    exists_isEigen_le_of_variational hH hHP ψ_ref hψ_sec hψ_norm hψ_energy
  linarith [hT E₀ φ₀ hEig]

/-- The initial state `sys.tensorState ψ (Pi.single 0 1)` preserves the squared norm of `ψ`. -/
theorem sum_normSq_sys_tensorState_zero {k m : ℕ} (ψ : Fin (2 ^ k) → ℂ) :
    let sys : QRegister k (k + m) := .block 0 k (by omega)
    ∑ g : Fin (2 ^ (k + m)), Complex.normSq (sys.tensorState ψ (Pi.single 0 1) g) =
      ∑ i : Fin (2 ^ k), Complex.normSq (ψ i) := by
  intro sys
  let f : Fin (2 ^ (k + m)) → ℝ := fun g ↦ Complex.normSq (sys.tensorState ψ (Pi.single 0 1) g)
  rw [show (∑ g, Complex.normSq (sys.tensorState ψ (Pi.single 0 1) g)) = ∑ g, f g from rfl,
    ← sys.basisSplitEquiv.symm.sum_comp f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Fintype.sum_eq_single (0 : sys.Environment → ZMod 2)]
  · dsimp [f, QRegister.tensorState]
    have hx : sys.extractIndex (sys.basisSplitEquiv.symm (x, 0)) = x := by
      rw [← sys.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
    rw [hx, Equiv.apply_symm_apply, Pi.single_eq_same, mul_one]
  · intro env henv
    dsimp [f, QRegister.tensorState]
    rw [Equiv.apply_symm_apply, Pi.single_eq_of_ne henv, mul_zero, map_zero]

/-- Pointwise rewrite for `∑ a, anc.basisOutcomeProbability a state * w a` as a global coordinate
sum. -/
theorem sum_basisOutcomeProbability_mul {n m : ℕ} (r : QRegister m n)
    (state : Fin (2 ^ n) → ℂ) (w : Fin (2 ^ m) → ℝ) :
    ∑ a : Fin (2 ^ m), r.basisOutcomeProbability a state * w a =
      ∑ g : Fin (2 ^ n), Complex.normSq (state g) * w (r.extractIndex g) := by
  simp only [QRegister.basisOutcomeProbability, QRegister.basisOutcomeProjector_mulVec,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [Fintype.sum_eq_single (r.extractIndex g)]
  · simp
  · intro a ha
    simp [ha.symm]

/-- Marginalizing an ancilla expectation whose observable factors through `rQPE : QRegister b m`
yields the expectation over `(anc.compose rQPE).basisOutcomeProbability`. -/
theorem sum_basisOutcomeProbability_mul_comp {n m b : ℕ} (anc : QRegister m n)
    (rQPE : QRegister b m) (state : Fin (2 ^ n) → ℂ) (f : Fin (2 ^ b) → ℝ) :
    ∑ a : Fin (2 ^ m), anc.basisOutcomeProbability a state * f (rQPE.extractIndex a) =
      ∑ y : Fin (2 ^ b), (anc.compose rQPE).basisOutcomeProbability y state * f y := by
  rw [sum_basisOutcomeProbability_mul, sum_basisOutcomeProbability_mul]
  simp only [QRegister.extractIndex_compose]

/-- Hilbert-space triangle inequality for capped energy MSE: if `u_ideal` achieves MSE at most
`ε_qpe²` and `‖u_impl - u_ideal‖₂ ≤ δ_tot`, then since `|min (estimate a) T - min E T| ≤ E_gap`
for every ancilla outcome `a`, `u_impl` achieves MSE at most `(ε_qpe + E_gap * δ_tot)²` — with
multiplier `E_gap` rather than `2Λ`. -/
theorem mse_impl_le_of_ideal_and_perturbation {n m_anc : ℕ} (anc : QRegister m_anc n)
    (estimate : Fin (2 ^ m_anc) → ℝ) {T E E_LB E_gap ε_qpe δ_tot : ℝ}
    {u_ideal u_impl : Fin (2 ^ n) → ℂ}
    (hgap0 : 0 ≤ E_gap) (hε0 : 0 ≤ ε_qpe)
    (hest_lb : ∀ a, E_LB ≤ estimate a) (hE_lb : E_LB ≤ E) (hT : T ≤ E_LB + E_gap)
    (hideal : ∑ a, anc.basisOutcomeProbability a u_ideal * (min (estimate a) T - min E T) ^ 2 ≤
      ε_qpe ^ 2)
    (hpert : ‖WithLp.toLp 2 (u_impl - u_ideal)‖ ≤ δ_tot) :
    ∑ a, anc.basisOutcomeProbability a u_impl * (min (estimate a) T - min E T) ^ 2 ≤
      (ε_qpe + E_gap * δ_tot) ^ 2 := by
  let D : Fin (2 ^ m_anc) → ℝ := fun a ↦ min (estimate a) T - min E T
  have hD_le (a : Fin (2 ^ m_anc)) : |D a| ≤ E_gap :=
    abs_min_sub_min_le_gap hgap0 (hest_lb a) hE_lb hT
  let scaleVec : (Fin (2 ^ n) → ℂ) → EuclideanSpace ℂ (Fin (2 ^ n)) :=
    fun v ↦ WithLp.toLp 2 (fun g ↦ (D (anc.extractIndex g) : ℂ) * v g)
  have hnorm_sq (v : Fin (2 ^ n) → ℂ) :
      ‖scaleVec v‖ ^ 2 =
        ∑ a, anc.basisOutcomeProbability a v * (min (estimate a) T - min E T) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, sum_basisOutcomeProbability_mul]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    change ‖(D (anc.extractIndex g) : ℂ) * v g‖ ^ 2 =
      Complex.normSq (v g) * (D (anc.extractIndex g)) ^ 2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Complex.normSq_eq_norm_sq]
    ring
  have hideal_norm : ‖scaleVec u_ideal‖ ≤ ε_qpe := by
    have hsq : ‖scaleVec u_ideal‖ ^ 2 ≤ ε_qpe ^ 2 := (hnorm_sq u_ideal).trans_le hideal
    nlinarith [norm_nonneg (scaleVec u_ideal)]
  have hdiff_norm : ‖scaleVec (u_impl - u_ideal)‖ ≤ E_gap * δ_tot := by
    have hsq : ‖scaleVec (u_impl - u_ideal)‖ ^ 2 ≤
        (E_gap * ‖WithLp.toLp 2 (u_impl - u_ideal)‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun g _ ↦ ?_
      change ‖(D (anc.extractIndex g) : ℂ) * (u_impl - u_ideal) g‖ ^ 2 ≤
        E_gap ^ 2 * ‖(u_impl - u_ideal) g‖ ^ 2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      have hDa : D (anc.extractIndex g) ^ 2 ≤ E_gap ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hD_le (anc.extractIndex g)) 2
      exact mul_le_mul_of_nonneg_right hDa (sq_nonneg _)
    have hle1 : ‖scaleVec (u_impl - u_ideal)‖ ≤ E_gap * ‖WithLp.toLp 2 (u_impl - u_ideal)‖ := by
      nlinarith [norm_nonneg (scaleVec (u_impl - u_ideal)),
        mul_nonneg hgap0 (norm_nonneg (WithLp.toLp 2 (u_impl - u_ideal)))]
    exact hle1.trans (mul_le_mul_of_nonneg_left hpert hgap0)
  have hsplit : scaleVec u_impl = scaleVec u_ideal + scaleVec (u_impl - u_ideal) := by
    ext g
    dsimp [scaleVec]
    ring
  have himpl_norm : ‖scaleVec u_impl‖ ≤ ε_qpe + E_gap * δ_tot := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hideal_norm hdiff_norm)
  rw [← hnorm_sq u_impl]
  exact pow_le_pow_left₀ (norm_nonneg _) himpl_norm 2

open scoped Matrix.Norms.L2Operator in
/-- Converts an `L2Operator` norm bound `‖W_impl.1 - W_ideal.1‖ ≤ δ_tot` into the statewise
Euclidean perturbation bound `‖WithLp.toLp 2 (W_impl.1 *ᵥ init - W_ideal.1 *ᵥ init)‖ ≤ δ_tot` on
any normalized input vector `init`. -/
theorem norm_mulVec_sub_le_of_opNorm {d : ℕ} (W_impl W_ideal : Unitary d)
    {init : Fin d → ℂ} {δ_tot : ℝ}
    (hnorm : ∑ g, Complex.normSq (init g) = 1) (hop : ‖W_impl.1 - W_ideal.1‖ ≤ δ_tot) :
    ‖WithLp.toLp 2 (W_impl.1 *ᵥ init - W_ideal.1 *ᵥ init)‖ ≤ δ_tot := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) (W_impl.1 - W_ideal.1)
  let v : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 init
  have hv : ‖v‖ = 1 := by
    have hv_sq : ‖v‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa only [v, Complex.normSq_eq_norm_sq] using hnorm
    nlinarith [norm_nonneg v]
  have heq : WithLp.toLp 2 (W_impl.1 *ᵥ init - W_ideal.1 *ᵥ init) = T v := by
    rw [← Matrix.sub_mulVec]
    rfl
  rw [heq]
  calc ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
    _ = ‖W_impl.1 - W_ideal.1‖ * 1 := by rw [Matrix.l2_opNorm_toEuclideanCLM, hv]
    _ ≤ δ_tot := by linarith

/-! ## Master Parametric End-to-End `MeasuresLowEnergies_local` Theorems -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
