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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MeasuresLowEnergiesAux

/-!
# Perturbed Hamiltonian & Walk-Synthesis QPE Closure
Unified standalone `MeasuresLowEnergies_local` closure when the block-encoded Hamiltonian `H_eff`
approximates `H` on the `η`-electron sector up to `δ_H` and `W_impl` approximates `W_ideal` up to
`L²` synthesis error `δ_W`. Evaluating all three stages at the fixed threshold `T` of
`MeasuresLowEnergies_local H η Δ ε W_impl` gives:
1. **Zero `δ_H` penalty on `E_gap`**: `E_ref + Δ - E_LB ≤ E_gap` implies `T ≤ E_LB + E_gap`, giving
   ideal capped MSE `((spectralAmpEffNorm Λ E_gap / 2) * σ_qpe) ^ 2` on each `H_eff` sector
   eigenstate `(Ẽ_j, φ̃_j)`.
2. **Zero-`M`-blowup sector Parseval `(H_eff, W_ideal) → (H, W_ideal)`**: Outcome-branch
   orthogonality `horth` on `W_ideal` plus `‖P (H_eff - H) P ψ‖₂ ≤ δ_H` yields capped MSE
   `(ε_qpe + δ_H) ^ 2` on `W_ideal |ψ, 0⟩` and `E_LB - δ_H ≤ E` without requiring `H * P = P * H`.
3. **Tight synthesis transfer `(H, W_ideal) → (H, W_impl)`**: Total RMS error at most
   `(spectralAmpEffNorm Λ E_gap / 2) * σ_qpe + δ_H + (E_gap + δ_H) * δ_W` (sharpening to
   `E_gap * δ_W` when `E_LB ≤ E` holds on `H`).

References: G. H. Low et al., Phys. Rev. X 15, 041016 (2025);
J. Lee et al., PRX Quantum 2, 030305 (2021).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PerturbedQPEClosure
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Real QuantumComputation.Specs Solution
open scoped Matrix Matrix.Norms.L2Operator

private local instance (priority := 100000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-! ## Section 1: Shifted Capped-MSE Hilbert-Space Perturbation Bridge -/

private lemma dotProduct_star_self {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    dotProduct (star v) v = ((∑ i : ι, Complex.normSq (v i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_sum]

private lemma dotProduct_star_self_re {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (dotProduct (star v) v).re = ∑ i : ι, Complex.normSq (v i) := by
  rw [dotProduct_star_self, Complex.ofReal_re]

/-- Mutual orthogonality of two-projector Jordan subspaces `span {e₁, P₂ *ᵥ e₁}` and
`span {e₂, P₂ *ᵥ e₂}` for Hermitian `P₁, P₂` with idempotent `P₂ * P₂ = P₂` (covering
spectral-amplification SOS and pulled-reflection walks `(2 • P₁ - 1) * (1 - 2 • P₂)`). -/
theorem jordan_two_subspace_orth {d : ℕ} {P₁ P₂ : Operator d}
    (hP₁_herm : P₁ᴴ = P₁) (hP₂_herm : P₂ᴴ = P₂) (hP₂_idem : P₂ * P₂ = P₂)
    {e₁ e₂ : Fin d → ℂ} {c₂ : ℂ}
    (he₁ : P₁ *ᵥ e₁ = e₁)
    (hproj₂ : P₁ *ᵥ (P₂ *ᵥ e₂) = c₂ • e₂)
    (horth : dotProduct (star e₁) e₂ = 0) :
    dotProduct (star e₁) e₂ = 0 ∧
      dotProduct (star e₁) (P₂ *ᵥ e₂) = 0 ∧
      dotProduct (star (P₂ *ᵥ e₁)) e₂ = 0 ∧
      dotProduct (star (P₂ *ᵥ e₁)) (P₂ *ᵥ e₂) = 0 := by
  have h12 : dotProduct (star e₁) (P₂ *ᵥ e₂) = 0 := by
    calc dotProduct (star e₁) (P₂ *ᵥ e₂)
        = dotProduct (star (P₁ *ᵥ e₁)) (P₂ *ᵥ e₂) := by rw [he₁]
      _ = dotProduct (star e₁) (P₁ *ᵥ (P₂ *ᵥ e₂)) := by
            rw [Matrix.star_mulVec, hP₁_herm, ← Matrix.dotProduct_mulVec]
      _ = dotProduct (star e₁) (c₂ • e₂) := by rw [hproj₂]
      _ = c₂ * dotProduct (star e₁) e₂ := by rw [dotProduct_smul, smul_eq_mul]
      _ = 0 := by rw [horth, mul_zero]
  have h21 : dotProduct (star (P₂ *ᵥ e₁)) e₂ = 0 := by
    rw [Matrix.star_mulVec, hP₂_herm, ← Matrix.dotProduct_mulVec]
    exact h12
  have h22 : dotProduct (star (P₂ *ᵥ e₁)) (P₂ *ᵥ e₂) = 0 := by
    rw [Matrix.star_mulVec, hP₂_herm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hP₂_idem]
    exact h12
  exact ⟨horth, h12, h21, h22⟩

/-- Linear-combination corollary of `jordan_two_subspace_orth` for arbitrary vectors in
`span {e₁, P₂ *ᵥ e₁}` and `span {e₂, P₂ *ᵥ e₂}`. -/
theorem jordan_span_cross_ortho {d : ℕ} {P₁ P₂ : Operator d}
    (hP₁_herm : P₁ᴴ = P₁) (hP₂_herm : P₂ᴴ = P₂) (hP₂_idem : P₂ * P₂ = P₂)
    {e₁ e₂ : Fin d → ℂ} {c₂ : ℂ}
    (he₁ : P₁ *ᵥ e₁ = e₁) (hproj₂ : P₁ *ᵥ (P₂ *ᵥ e₂) = c₂ • e₂)
    (horth : dotProduct (star e₁) e₂ = 0)
    (a₁ b₁ a₂ b₂ : ℂ) :
    dotProduct (star (a₁ • e₁ + b₁ • (P₂ *ᵥ e₁))) (a₂ • e₂ + b₂ • (P₂ *ᵥ e₂)) = 0 := by
  obtain ⟨h11, h12, h21, h22⟩ :=
    jordan_two_subspace_orth hP₁_herm hP₂_herm hP₂_idem he₁ hproj₂ horth
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    h11, h12, h21, h22, smul_zero, add_zero]

/-! ## Section 3: Projected `η`-Electron Sector Error & Rayleigh Spectral Transfer -/

/-- `electronSectorProjector k η` is Hermitian. -/
theorem electronSectorProjector_isHermitian (k η : ℕ) :
    (electronSectorProjector k η).IsHermitian := by
  ext i j
  simp only [electronSectorProjector, conjTranspose_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    split_ifs <;> simp
  · simp [hij, Ne.symm hij]

/-- `electronSectorProjector k η` is idempotent. -/
@[simp]
theorem electronSectorProjector_mul_self (k η : ℕ) :
    electronSectorProjector k η * electronSectorProjector k η = electronSectorProjector k η := by
  ext i j
  simp only [electronSectorProjector, diagonal_mul_diagonal, diagonal_apply]
  split_ifs <;> simp

/-- Pointwise contraction of `electronSectorProjector k η` on computational-basis amplitudes. -/
theorem sum_normSq_electronSectorProjector_mulVec_le (k η : ℕ) (w : Fin (2 ^ k) → ℂ) :
    ∑ i : Fin (2 ^ k), Complex.normSq ((electronSectorProjector k η *ᵥ w) i) ≤
      ∑ i : Fin (2 ^ k), Complex.normSq (w i) := by
  refine Finset.sum_le_sum fun i _ ↦ ?_
  simp only [electronSectorProjector, mulVec_diagonal]
  split_ifs
  · rw [one_mul]
  · rw [zero_mul, map_zero]
    exact Complex.normSq_nonneg _

/-- Converts a spectral-norm bound `‖M‖ ≤ δ` (`0 ≤ δ`) into the `L²` vector-norm bound
`∑ i, Complex.normSq ((M *ᵥ φ) i) ≤ δ ^ 2 * ∑ i, Complex.normSq (φ i)`. -/
theorem sum_normSq_mulVec_le_of_opNorm {d : ℕ} {M : Operator d} {δ : ℝ}
    (hop : ‖M‖ ≤ δ) (φ : Fin d → ℂ) :
    ∑ i : Fin d, Complex.normSq ((M *ᵥ φ) i) ≤ δ ^ 2 * ∑ i : Fin d, Complex.normSq (φ i) := by
  let v : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 φ
  let mv : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (M *ᵥ φ)
  have hle : ‖mv‖ ≤ δ * ‖v‖ :=
    (Matrix.l2_opNorm_mulVec M v).trans (mul_le_mul_of_nonneg_right hop (norm_nonneg v))
  have hsq : ‖mv‖ ^ 2 ≤ (δ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg mv) hle 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq] at hsq
  simpa only [mv, v, Complex.normSq_eq_norm_sq] using hsq

/-- Converts `AgreesOnElectronSector N η H_eff H δ_H` into `H_eff` sector commutativity and the
projected sector vector-error bound, without requiring `H` to commute with the projector. -/
theorem projected_sector_err_of_agreesOnElectronSector {N η : ℕ}
    {H_eff H : Operator (2 ^ (2 * N))} {δ_H : ℝ}
    (hagree : AgreesOnElectronSector N η H_eff H δ_H) :
    let P := electronSectorProjector (2 * N) η
    H_eff * P = P * H_eff ∧
      ∀ φ : Fin (2 ^ (2 * N)) → ℂ,
        ∑ i, Complex.normSq (((P * (H_eff - H) * P) *ᵥ φ) i) ≤
          δ_H ^ 2 * ∑ i, Complex.normSq (φ i) :=
  ⟨hagree.1, sum_normSq_mulVec_le_of_opNorm hagree.2⟩

private lemma sum_normSq_pos_of_ne_zero {d : ℕ} {φ : Fin d → ℂ} (hne : φ ≠ 0) :
    0 < ∑ i : Fin d, Complex.normSq (φ i) := by
  by_contra hle
  have hle' : ∑ i : Fin d, Complex.normSq (φ i) ≤ 0 := not_lt.mp hle
  apply hne
  ext i
  have hi : Complex.normSq (φ i) ≤ 0 :=
    (Finset.single_le_sum (fun _ _ ↦ Complex.normSq_nonneg _) (Finset.mem_univ i)).trans hle'
  exact Complex.normSq_eq_zero.mp (le_antisymm hi (Complex.normSq_nonneg _))

private lemma abs_re_dotProduct_mulVec_le {d : ℕ} {M : Operator d} {δ : ℝ} (hδ : 0 ≤ δ)
    {φ : Fin d → ℂ}
    (hM : ∑ i, Complex.normSq ((M *ᵥ φ) i) ≤ δ ^ 2 * ∑ i, Complex.normSq (φ i)) :
    |(dotProduct (star φ) (M *ᵥ φ)).re| ≤ δ * ∑ i, Complex.normSq (φ i) := by
  by_cases hδ0 : δ = 0
  · subst hδ0
    have hz : M *ᵥ φ = 0 := by
      ext i
      have hi : Complex.normSq ((M *ᵥ φ) i) ≤ 0 :=
        (Finset.single_le_sum (fun _ _ ↦ Complex.normSq_nonneg _)
          (Finset.mem_univ i)).trans (by simpa only [sq, zero_mul] using hM)
      exact Complex.normSq_eq_zero.mp (le_antisymm hi (Complex.normSq_nonneg _))
    simp only [hz, dotProduct_zero, Complex.zero_re, abs_zero, zero_mul, le_refl]
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
    have hquad (t : ℝ) : 0 ≤ t ^ 2 * (∑ i, Complex.normSq (φ i)) +
        (∑ i, Complex.normSq ((M *ᵥ φ) i)) + 2 * t * (dotProduct (star φ) (M *ᵥ φ)).re := by
      have hnn : 0 ≤ ∑ i, Complex.normSq ((t : ℂ) * φ i + (M *ᵥ φ) i) :=
        Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
      refine hnn.trans_eq ?_
      simp only [dotProduct, Pi.star_apply, Complex.re_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    have hsub := hquad (-δ)
    have hadd := hquad δ
    rw [abs_le]
    constructor <;> nlinarith

private lemma abs_eigen_rayleigh_sub_le {k η : ℕ} {H_eff H : Operator (2 ^ k)}
    {δ_H E_tilde : ℝ} {φ : Fin (2 ^ k) → ℂ} (hδ : 0 ≤ δ_H)
    (hdiff : ∑ i, Complex.normSq
        (((electronSectorProjector k η * (H_eff - H) * electronSectorProjector k η) *ᵥ φ) i) ≤
      δ_H ^ 2 * ∑ i, Complex.normSq (φ i))
    (heig : H_eff *ᵥ φ = (E_tilde : ℂ) • φ)
    (hsec : electronSectorProjector k η *ᵥ φ = φ) :
    |E_tilde * (∑ i, Complex.normSq (φ i)) - (dotProduct (star φ) (H *ᵥ φ)).re| ≤
      δ_H * ∑ i, Complex.normSq (φ i) := by
  let P := electronSectorProjector k η
  have hcs := abs_re_dotProduct_mulVec_le hδ hdiff
  have hdot_proj : dotProduct (star φ) ((P * (H_eff - H) * P) *ᵥ φ) =
      dotProduct (star φ) ((H_eff - H) *ᵥ φ) := by
    have hPherm : Pᴴ = P := (electronSectorProjector_isHermitian k η).eq
    calc dotProduct (star φ) ((P * (H_eff - H) * P) *ᵥ φ)
        = dotProduct (star (P *ᵥ φ)) ((H_eff - H) *ᵥ (P *ᵥ φ)) := by
            rw [Matrix.star_mulVec, hPherm, ← Matrix.dotProduct_mulVec,
              Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = dotProduct (star φ) ((H_eff - H) *ᵥ φ) := by rw [hsec]
  have hHeff : (dotProduct (star φ) (H_eff *ᵥ φ)).re =
      E_tilde * ∑ i, Complex.normSq (φ i) := by
    rw [heig, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, dotProduct_star_self_re]
  rwa [hdot_proj, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hHeff] at hcs

/-- Transfers a Rayleigh-quotient upper bound `≤ B` from `H` to `Ẽ ≤ B + δ_H` on every nonzero
`η`-electron eigenstate `(Ẽ, φ)` of `H_eff` using only the projected sector error
`‖P (H_eff - H) P φ‖₂ ≤ δ_H ‖φ‖₂`. -/
theorem sector_eigen_ub_of_projected_approx {k η : ℕ} {H_eff H : Operator (2 ^ k)}
    {B δ_H E_tilde : ℝ} {φ : Fin (2 ^ k) → ℂ} (hδ : 0 ≤ δ_H)
    (hray_ub : ∀ ψ : Fin (2 ^ k) → ℂ, electronSectorProjector k η *ᵥ ψ = ψ →
      (dotProduct (star ψ) (H *ᵥ ψ)).re ≤ B * ∑ i, Complex.normSq (ψ i))
    (hdiff : ∑ i, Complex.normSq
        (((electronSectorProjector k η * (H_eff - H) * electronSectorProjector k η) *ᵥ φ) i) ≤
      δ_H ^ 2 * ∑ i, Complex.normSq (φ i))
    (hEig : IsEigenSector H_eff η E_tilde φ) :
    E_tilde ≤ B + δ_H := by
  rcases hEig with ⟨heig, hsec, hne⟩
  have hpos := sum_normSq_pos_of_ne_zero hne
  have hcs := (abs_le.mp (abs_eigen_rayleigh_sub_le hδ hdiff heig hsec)).2
  have hHub := hray_ub φ hsec
  nlinarith

/-- Specialization of `sector_eigen_ub_of_projected_approx` to `AgreesOnElectronSector`. -/
theorem sector_eigen_ub_of_agreesOnElectronSector {N η : ℕ}
    {H_eff H : Operator (2 ^ (2 * N))} {B δ_H E_tilde : ℝ} {φ : Fin (2 ^ (2 * N)) → ℂ}
    (hδ : 0 ≤ δ_H) (hagree : AgreesOnElectronSector N η H_eff H δ_H)
    (hray_ub : ∀ ψ : Fin (2 ^ (2 * N)) → ℂ, electronSectorProjector (2 * N) η *ᵥ ψ = ψ →
      (dotProduct (star ψ) (H *ᵥ ψ)).re ≤ B * ∑ i, Complex.normSq (ψ i))
    (hEig : IsEigenSector H_eff η E_tilde φ) :
    E_tilde ≤ B + δ_H :=
  sector_eigen_ub_of_projected_approx hδ hray_ub
    (sum_normSq_mulVec_le_of_opNorm hagree.2 φ) hEig

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.PerturbedQPEClosure
