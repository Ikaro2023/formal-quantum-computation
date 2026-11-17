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

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DataArrays
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SumOfSquares

/-!
# High-Energy Non-Aliasing Upper Bound for `P450.dfthc` (`SpectralUpperBound`)

Proves an unconditional upper bound of `+48` Ha (`dfthcUpperBound := 48`) on the quadratic form and
all eigenvalues of `thcHamiltonian P450.dfthc` across the `116`-qubit Hilbert space (and in
particular on every `63`-electron eigenstate `IsEigen63`).

In doubled-phase spectral-amplification quantum phase estimation (G. H. Low et al., Phys. Rev. X
15, 041016 (2025), Eq. 11), the walk phase is $2\phi(E) \in [0, 2\pi)$ where
$E = E_{\text{LB}} + \Lambda (1 - \cos\phi(E))$ with $E_{\text{LB}} \approx -134.8874$ Ha and
$\Lambda = 97.3864$ Ha ($E_{\text{LB}} + 2\Lambda \approx +59.885$ Ha). Bounding every
`63`-electron eigenvalue below `+48` Ha keeps the spectrum strictly below the non-aliasing ceiling
$E_{\text{LB}} + 2\Lambda - E_{\text{gap}} \approx +54.3$ Ha with more than `6` Ha of margin.

## Proof Architecture
1. **Centered-Shift Completion of the Square:** Rewrites each two-body fragment $(r, c)$ around
   $\alpha_{rc} = \sum_{b < 29} w^{(rc)}_b$, expressing $\alpha_{rc} I - M_{rc}$ as a real linear
   combination of commuting involutory Hermitian orbital reflections $I - 2\tilde{n}_{u,\sigma}$
   (two-body scalar contribution `27.31964` Ha) and folding the linear term $w^{(rc)}_{29} M_{rc}$
   into a `58 × 58` symmetric one-body matrix $H_1$.
2. **Certified Givens-Leaf Interval Arithmetic:** Encloses every `givensLeaf 15` vector of
   `oneBodyAngleTable` (`58` rows) and `leafAngleTable` (`261` rows) at scale $S = 2^{20}$ using
   `Mathlib.Analysis.Real.Pi.Bounds`, Taylor polynomials, and two double-angle steps (midpoint
   radius $\le 77 / 2^{20}$, rank-1 approximation error `0.09964` Ha).
3. **`96`-Bit `Nat` SIMD Positive/Negative Gram Certificate:** Decomposes the midpoint matrix
   $\widehat{H}_1 \approx L_+ L_+^T - L_- L_-^T$ (`22` positive and `36` negative integer columns
   at scale $2^{16}$), verified in the kernel via `evalWeightedGram` (`L_-` term $\ge 0$, `L_+`
   trace bound `19.46798` Ha, residual error `0.12556` Ha; certified total `47.01281 < 48` Ha).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Real Operator Matrix DataArrays
open scoped Matrix

namespace UpperBound

/-! ### 1. Vector Norm-Squared & Quadratic Form Inequalities -/

/-- Squared $\ell_2$ norm $\sum_i \|\psi_i\|^2$ of a complex state vector. -/
abbrev vecNormSq {d : ℕ} (ψ : Fin d → ℂ) : ℝ := ∑ i : Fin d, Complex.normSq (ψ i)

lemma vecNormSq_nonneg {d : ℕ} (ψ : Fin d → ℂ) : 0 ≤ vecNormSq ψ :=
  Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

lemma vecNormSq_pos_of_ne_zero {d : ℕ} {ψ : Fin d → ℂ} (hψ : ψ ≠ 0) : 0 < vecNormSq ψ := by
  obtain ⟨i, hi⟩ : ∃ i, ψ i ≠ 0 := Function.ne_iff.mp hψ
  exact Finset.sum_pos' (fun _ _ ↦ Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

lemma re_star_dotProduct_self {d : ℕ} (ψ : Fin d → ℂ) :
    (star ψ ⬝ᵥ ψ).re = vecNormSq ψ := by
  simp [dotProduct, vecNormSq, Complex.normSq_apply]

lemma star_dotProduct_conjTranspose_mul_mulVec {d : ℕ} (A B : Operator d) (x y : Fin d → ℂ) :
    star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) = star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

lemma re_quadForm_conjTranspose_mul_self {d : ℕ} (A : Operator d) (ψ : Fin d → ℂ) :
    (star ψ ⬝ᵥ ((Aᴴ * A) *ᵥ ψ)).re = vecNormSq (A *ᵥ ψ) := by
  rw [star_dotProduct_conjTranspose_mul_mulVec, re_star_dotProduct_self]

lemma abs_re_star_dotProduct_le {d : ℕ} (x y : Fin d → ℂ) :
    |(star x ⬝ᵥ y).re| ≤ √(vecNormSq x) * √(vecNormSq y) := by
  simp only [dotProduct, Complex.re_sum]
  calc |∑ i : Fin d, (star (x i) * y i).re|
      ≤ ∑ i : Fin d, |(star (x i) * y i).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, √(Complex.normSq (x i)) * √(Complex.normSq (y i)) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        calc |(star (x i) * y i).re|
            ≤ ‖star (x i) * y i‖ := Complex.abs_re_le_norm _
          _ = ‖x i‖ * ‖y i‖ := by rw [norm_mul, norm_star]
          _ = √(Complex.normSq (x i)) * √(Complex.normSq (y i)) := by
              rw [Complex.norm_def, Complex.norm_def]
    _ ≤ √(vecNormSq x) * √(vecNormSq y) :=
        Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun i ↦ Complex.normSq_nonneg (x i)) (fun i ↦ Complex.normSq_nonneg (y i))

lemma vecNormSq_sum_smul_le {ι : Type*} {d : ℕ} (s : Finset ι) (c : ι → ℝ)
    (φ : ι → Fin d → ℂ) {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ m ∈ s, vecNormSq (φ m) ≤ B) :
    vecNormSq (∑ m ∈ s, (c m : ℂ) • φ m) ≤ (∑ m ∈ s, |c m|) ^ 2 * B := by
  rw [← re_star_dotProduct_self]
  have hexp : star (∑ m ∈ s, (c m : ℂ) • φ m) ⬝ᵥ (∑ m ∈ s, (c m : ℂ) • φ m) =
      ∑ m₁ ∈ s, ∑ m₂ ∈ s, ((c m₁ * c m₂ : ℝ) : ℂ) * (star (φ m₁) ⬝ᵥ φ m₂) := by
    rw [star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun m₂ _ ↦ ?_
    simp only [star_smul, RCLike.star_def, Complex.conj_ofReal, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, Complex.ofReal_mul]
    ring
  rw [hexp, Complex.re_sum]
  simp_rw [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc ∑ m₁ ∈ s, ∑ m₂ ∈ s, c m₁ * c m₂ * (star (φ m₁) ⬝ᵥ φ m₂).re
      ≤ ∑ m₁ ∈ s, ∑ m₂ ∈ s, |c m₁| * |c m₂| * B := by
        refine Finset.sum_le_sum fun m₁ hm₁ ↦ Finset.sum_le_sum fun m₂ hm₂ ↦ ?_
        have hcs : |(star (φ m₁) ⬝ᵥ φ m₂).re| ≤ B := by
          calc |(star (φ m₁) ⬝ᵥ φ m₂).re|
              ≤ √(vecNormSq (φ m₁)) * √(vecNormSq (φ m₂)) :=
                abs_re_star_dotProduct_le _ _
            _ ≤ √B * √B := by
                gcongr
                · exact hφ m₁ hm₁
                · exact hφ m₂ hm₂
            _ = B := Real.mul_self_sqrt hB
        calc c m₁ * c m₂ * (star (φ m₁) ⬝ᵥ φ m₂).re
            ≤ |c m₁ * c m₂ * (star (φ m₁) ⬝ᵥ φ m₂).re| := le_abs_self _
          _ = |c m₁| * |c m₂| * |(star (φ m₁) ⬝ᵥ φ m₂).re| := by rw [abs_mul, abs_mul]
          _ ≤ |c m₁| * |c m₂| * B := by gcongr
    _ = (∑ m ∈ s, |c m|) ^ 2 * B := by
        rw [sq, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m₁ _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]

/-! ### 2. Quadratic Form Bounds on `oneBodyHamiltonian` -/

/-- Real-orbital fermionic annihilation mode $b_{v,\sigma} = \sum_p v_p a_{p,\sigma}$. -/
noncomputable abbrev jwMode {N : ℕ} (v : Fin N → ℝ) (σ : Fin 2) : Operator (2 ^ (2 * N)) :=
  jwLinearMode (fun p ↦ spinOrbital N p σ) v

lemma orbitalNumberOp_eq_jwMode {N : ℕ} (v : Fin N → ℝ) (σ : Fin 2) :
    orbitalNumberOp N v σ = (jwMode v σ)ᴴ * jwMode v σ := rfl

lemma jwMode_anti_conj {N : ℕ} (v : Fin N → ℝ) (σ : Fin 2) :
    (jwMode v σ)ᴴ * jwMode v σ + jwMode v σ * (jwMode v σ)ᴴ =
      ((∑ p : Fin N, v p ^ 2 : ℝ) : ℂ) • 1 := by
  simpa only [sq] using jwLinearMode_conjTranspose_anticomm (spinOrbital_injective N σ) v v

lemma jwMode_vecNormSq_le {N : ℕ} (v : Fin N → ℝ) (σ : Fin 2)
    (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    vecNormSq (jwMode v σ *ᵥ ψ) ≤ (∑ p : Fin N, v p ^ 2) * vecNormSq ψ := by
  have hid := congrArg (fun M : Operator (2 ^ (2 * N)) ↦ (star ψ ⬝ᵥ (M *ᵥ ψ)).re)
    (jwMode_anti_conj v σ)
  simp only [Matrix.add_mulVec, dotProduct_add, Complex.add_re,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    re_star_dotProduct_self] at hid
  have h1 : (star ψ ⬝ᵥ (((jwMode v σ)ᴴ * jwMode v σ) *ᵥ ψ)).re = vecNormSq (jwMode v σ *ᵥ ψ) :=
    re_quadForm_conjTranspose_mul_self _ _
  have h2 : 0 ≤ (star ψ ⬝ᵥ ((jwMode v σ * (jwMode v σ)ᴴ) *ᵥ ψ)).re := by
    have hc : jwMode v σ * (jwMode v σ)ᴴ = ((jwMode v σ)ᴴ)ᴴ * (jwMode v σ)ᴴ := by
      rw [Matrix.conjTranspose_conjTranspose]
    rw [hc, re_quadForm_conjTranspose_mul_self]
    exact vecNormSq_nonneg _
  linarith

lemma jwAnnihilate_vecNormSq_le {k : ℕ} (j : Fin k) (ψ : Fin (2 ^ k) → ℂ) :
    vecNormSq (jwAnnihilate k j *ᵥ ψ) ≤ vecNormSq ψ := by
  have hid := congrArg (fun M : Operator (2 ^ k) ↦ (star ψ ⬝ᵥ (M *ᵥ ψ)).re)
    (jwAnnihilate_conjTranspose_anticomm k j j)
  simp only [↓reduceIte, Matrix.add_mulVec, dotProduct_add, Complex.add_re,
    Matrix.one_mulVec, re_star_dotProduct_self] at hid
  have h1 : (star ψ ⬝ᵥ (((jwAnnihilate k j)ᴴ * jwAnnihilate k j) *ᵥ ψ)).re =
      vecNormSq (jwAnnihilate k j *ᵥ ψ) := re_quadForm_conjTranspose_mul_self _ _
  have h2 : 0 ≤ (star ψ ⬝ᵥ ((jwAnnihilate k j * (jwAnnihilate k j)ᴴ) *ᵥ ψ)).re := by
    have hc : jwAnnihilate k j * (jwAnnihilate k j)ᴴ =
        ((jwAnnihilate k j)ᴴ)ᴴ * (jwAnnihilate k j)ᴴ := by
      rw [Matrix.conjTranspose_conjTranspose]
    rw [hc, re_quadForm_conjTranspose_mul_self]
    exact vecNormSq_nonneg _
  linarith

lemma oneBodyHamiltonian_vecMulVec_pair {N : ℕ} (x y : Fin N → ℝ) :
    oneBodyHamiltonian (Matrix.vecMulVec x y) =
      ∑ σ : Fin 2, (jwMode x σ)ᴴ * jwMode y σ := by
  simp only [oneBodyHamiltonian, Matrix.vecMulVec_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  have hconj : (jwMode x σ)ᴴ =
      ∑ p : Fin N, (x p : ℂ) • (jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ := by
    simp [jwMode, jwLinearMode, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul]
  rw [hconj, jwMode, jwLinearMode, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  simp [smul_smul, mul_comm, -Complex.ofReal_mul]

lemma re_oneBody_vecMulVec_self_nonneg {N : ℕ} (u : Fin N → ℝ) (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    0 ≤ (star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec u u) *ᵥ ψ)).re := by
  rw [oneBodyHamiltonian_vecMulVec, Matrix.add_mulVec, dotProduct_add, Complex.add_re,
    orbitalNumberOp_eq_jwMode, orbitalNumberOp_eq_jwMode,
    re_quadForm_conjTranspose_mul_self, re_quadForm_conjTranspose_mul_self]
  linarith [vecNormSq_nonneg (jwMode u 0 *ᵥ ψ), vecNormSq_nonneg (jwMode u 1 *ᵥ ψ)]

lemma re_oneBody_vecMulVec_self_le {N : ℕ} (u : Fin N → ℝ) (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    (star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec u u) *ᵥ ψ)).re ≤
      (2 * ∑ p : Fin N, u p ^ 2) * vecNormSq ψ := by
  rw [oneBodyHamiltonian_vecMulVec, Matrix.add_mulVec, dotProduct_add, Complex.add_re,
    orbitalNumberOp_eq_jwMode, orbitalNumberOp_eq_jwMode,
    re_quadForm_conjTranspose_mul_self, re_quadForm_conjTranspose_mul_self]
  linarith [jwMode_vecNormSq_le u 0 ψ, jwMode_vecNormSq_le u 1 ψ]

lemma abs_re_oneBody_vecMulVec_le {N : ℕ} (x y : Fin N → ℝ) (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    |(star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec x y) *ᵥ ψ)).re| ≤
      (2 * √(∑ p : Fin N, x p ^ 2) * √(∑ p : Fin N, y p ^ 2)) * vecNormSq ψ := by
  rw [oneBodyHamiltonian_vecMulVec_pair, Fin.sum_univ_two, Matrix.add_mulVec, dotProduct_add,
    Complex.add_re, star_dotProduct_conjTranspose_mul_mulVec,
    star_dotProduct_conjTranspose_mul_mulVec]
  have hσ : ∀ σ : Fin 2, |(star (jwMode x σ *ᵥ ψ) ⬝ᵥ (jwMode y σ *ᵥ ψ)).re| ≤
      √(∑ p : Fin N, x p ^ 2) * √(∑ p : Fin N, y p ^ 2) * vecNormSq ψ := by
    intro σ
    calc |(star (jwMode x σ *ᵥ ψ) ⬝ᵥ (jwMode y σ *ᵥ ψ)).re|
        ≤ √(vecNormSq (jwMode x σ *ᵥ ψ)) * √(vecNormSq (jwMode y σ *ᵥ ψ)) :=
          abs_re_star_dotProduct_le _ _
      _ ≤ √((∑ p, x p ^ 2) * vecNormSq ψ) * √((∑ p, y p ^ 2) * vecNormSq ψ) := by
          gcongr
          · exact jwMode_vecNormSq_le x σ ψ
          · exact jwMode_vecNormSq_le y σ ψ
      _ = √(∑ p, x p ^ 2) * √(∑ p, y p ^ 2) * vecNormSq ψ := by
          rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
            Real.sqrt_mul (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
          have hsq : √(vecNormSq ψ) * √(vecNormSq ψ) = vecNormSq ψ :=
            Real.mul_self_sqrt (vecNormSq_nonneg ψ)
          linear_combination √(∑ p, x p ^ 2) * √(∑ p, y p ^ 2) * hsq
  calc |(star (jwMode x 0 *ᵥ ψ) ⬝ᵥ (jwMode y 0 *ᵥ ψ)).re +
          (star (jwMode x 1 *ᵥ ψ) ⬝ᵥ (jwMode y 1 *ᵥ ψ)).re|
      ≤ |(star (jwMode x 0 *ᵥ ψ) ⬝ᵥ (jwMode y 0 *ᵥ ψ)).re| +
          |(star (jwMode x 1 *ᵥ ψ) ⬝ᵥ (jwMode y 1 *ᵥ ψ)).re| := abs_add_le _ _
    _ ≤ _ := by linarith [hσ 0, hσ 1]

lemma abs_re_oneBody_matrix_le {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ)
    (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    |(star ψ ⬝ᵥ (oneBodyHamiltonian E *ᵥ ψ)).re| ≤
      (2 * ∑ p : Fin N, ∑ q : Fin N, |E p q|) * vecNormSq ψ := by
  simp only [oneBodyHamiltonian, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hterm : ∀ (σ : Fin 2) (p q : Fin N),
      |E p q * (star ψ ⬝ᵥ (((jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ *
        jwAnnihilate (2 * N) (spinOrbital N q σ)) *ᵥ ψ)).re| ≤
      |E p q| * vecNormSq ψ := by
    intro σ p q
    rw [abs_mul, star_dotProduct_conjTranspose_mul_mulVec]
    have hcs : |(star (jwAnnihilate (2 * N) (spinOrbital N p σ) *ᵥ ψ) ⬝ᵥ
        (jwAnnihilate (2 * N) (spinOrbital N q σ) *ᵥ ψ)).re| ≤ vecNormSq ψ := by
      calc |(star (jwAnnihilate (2 * N) (spinOrbital N p σ) *ᵥ ψ) ⬝ᵥ
              (jwAnnihilate (2 * N) (spinOrbital N q σ) *ᵥ ψ)).re|
          ≤ √(vecNormSq (jwAnnihilate (2 * N) (spinOrbital N p σ) *ᵥ ψ)) *
              √(vecNormSq (jwAnnihilate (2 * N) (spinOrbital N q σ) *ᵥ ψ)) :=
            abs_re_star_dotProduct_le _ _
        _ ≤ √(vecNormSq ψ) * √(vecNormSq ψ) := by
            gcongr <;> exact jwAnnihilate_vecNormSq_le _ ψ
        _ = vecNormSq ψ := Real.mul_self_sqrt (vecNormSq_nonneg ψ)
    gcongr
  calc |∑ σ : Fin 2, ∑ p : Fin N, ∑ q : Fin N, E p q *
          (star ψ ⬝ᵥ (((jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ *
            jwAnnihilate (2 * N) (spinOrbital N q σ)) *ᵥ ψ)).re|
      ≤ ∑ σ : Fin 2, ∑ p : Fin N, ∑ q : Fin N, |E p q *
          (star ψ ⬝ᵥ (((jwAnnihilate (2 * N) (spinOrbital N p σ))ᴴ *
            jwAnnihilate (2 * N) (spinOrbital N q σ)) *ᵥ ψ)).re| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ ↦ ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ ↦
          Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _σ : Fin 2, ∑ p : Fin N, ∑ q : Fin N, |E p q| * vecNormSq ψ :=
        Finset.sum_le_sum fun σ _ ↦ Finset.sum_le_sum fun p _ ↦
          Finset.sum_le_sum fun q _ ↦ hterm σ p q
    _ = (2 * ∑ p : Fin N, ∑ q : Fin N, |E p q|) * vecNormSq ψ := by
        rw [Fin.sum_univ_two]
        simp_rw [← Finset.sum_mul]
        ring

lemma re_oneBody_add {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ)
    (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    (star ψ ⬝ᵥ (oneBodyHamiltonian (A + B) *ᵥ ψ)).re =
      (star ψ ⬝ᵥ (oneBodyHamiltonian A *ᵥ ψ)).re +
        (star ψ ⬝ᵥ (oneBodyHamiltonian B *ᵥ ψ)).re := by
  rw [oneBodyHamiltonian_add, Matrix.add_mulVec, dotProduct_add, Complex.add_re]

lemma re_oneBody_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ)
    (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    (star ψ ⬝ᵥ (oneBodyHamiltonian (A - B) *ᵥ ψ)).re =
      (star ψ ⬝ᵥ (oneBodyHamiltonian A *ᵥ ψ)).re -
        (star ψ ⬝ᵥ (oneBodyHamiltonian B *ᵥ ψ)).re := by
  rw [oneBodyHamiltonian_sub, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

lemma re_oneBody_sum {ι : Type*} [Fintype ι] {N : ℕ} (f : ι → Matrix (Fin N) (Fin N) ℝ)
    (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    (star ψ ⬝ᵥ (oneBodyHamiltonian (∑ i, f i) *ᵥ ψ)).re =
      ∑ i, (star ψ ⬝ᵥ (oneBodyHamiltonian (f i) *ᵥ ψ)).re := by
  rw [oneBodyHamiltonian_sum, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

/-! ### 3. 96-Bit `Nat` SIMD Packing Soundness -/

/-- Forces strict evaluation of a `Nat` argument before applying `f` during kernel reduction. -/
def forceNat {α : Type*} (x : ℕ) (f : ℕ → α) : α :=
  Nat.casesOn (Nat.add x 1) (f 0) f

@[simp]
lemma forceNat_eq {α : Type*} (x : ℕ) (f : ℕ → α) : forceNat x f = f x := rfl

/-- Forces strict evaluation of an `Int` argument before applying `f` during kernel reduction. -/
def forceInt {α : Type*} (z : ℤ) (f : ℤ → α) : α :=
  match z with
  | Int.ofNat n => forceNat n fun n' ↦ f (Int.ofNat n')
  | Int.negSucc n => forceNat n fun n' ↦ f (Int.negSucc n')

@[simp]
lemma forceInt_eq {α : Type*} (z : ℤ) (f : ℤ → α) : forceInt z f = f z := by
  cases z <;> rfl

/-- Forces strict evaluation of both endpoints of a `Nat × Nat`
interval during kernel reduction. -/
def forceNatIv {α : Type*} (iv : ℕ × ℕ) (f : ℕ → ℕ → α) : α :=
  match iv with
  | (lo0, hi0) => forceNat lo0 fun lo ↦ forceNat hi0 fun hi ↦ f lo hi

@[simp]
lemma forceNatIv_eq {α : Type*} (iv : ℕ × ℕ) (f : ℕ → ℕ → α) :
    forceNatIv iv f = f iv.1 iv.2 := by
  rcases iv with ⟨lo0, hi0⟩
  rfl

/-- Forces strict evaluation of a pair of `Nat × Nat` intervals
during kernel reduction. -/
def forcePairNatIv {α : Type*} (sc : (ℕ × ℕ) × (ℕ × ℕ))
    (f : (ℕ × ℕ) → (ℕ × ℕ) → α) : α :=
  match sc with
  | (s0, c0) =>
      forceNatIv s0 fun slo shi ↦
      forceNatIv c0 fun clo chi ↦ f (slo, shi) (clo, chi)

@[simp]
lemma forcePairNatIv_eq {α : Type*} (sc : (ℕ × ℕ) × (ℕ × ℕ))
    (f : (ℕ × ℕ) → (ℕ × ℕ) → α) : forcePairNatIv sc f = f sc.1 sc.2 := by
  rcases sc with ⟨⟨slo, shi⟩, ⟨clo, chi⟩⟩
  rfl

/-- Strictly evaluates all elements and spine cells of a `List ℕ` during kernel reduction. -/
def evalListNat : List ℕ → List ℕ
  | [] => []
  | x :: xs => forceNat x fun x' ↦
      match evalListNat xs with
      | [] => [x']
      | y :: ys => x' :: y :: ys

lemma evalListNat_eq (xs : List ℕ) : evalListNat xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [evalListNat, forceNat_eq, ih]
      cases xs <;> rfl

/-- Binds a strictly evaluated `List ℕ` before applying `f` during kernel reduction. -/
def withListNat {α : Type*} (xs : List ℕ) (f : List ℕ → α) : α :=
  match evalListNat xs with
  | [] => f []
  | y :: ys => f (y :: ys)

@[simp]
lemma withListNat_eq {α : Type*} (xs : List ℕ) (f : List ℕ → α) :
    withListNat xs f = f xs := by
  unfold withListNat
  rw [evalListNat_eq]
  cases xs <;> rfl

/-- Strictly evaluates all elements and spine cells of a `List ℤ` during kernel reduction. -/
def evalListInt : List ℤ → List ℤ
  | [] => []
  | x :: xs => forceInt x fun x' ↦
      match evalListInt xs with
      | [] => [x']
      | y :: ys => x' :: y :: ys

lemma evalListInt_eq (xs : List ℤ) : evalListInt xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [evalListInt, forceInt_eq, ih]
      cases xs <;> rfl

/-- Binds a strictly evaluated `List ℤ` before applying `f` during kernel reduction. -/
def withListInt {α : Type*} (xs : List ℤ) (f : List ℤ → α) : α :=
  match evalListInt xs with
  | [] => f []
  | y :: ys => f (y :: ys)

@[simp]
lemma withListInt_eq {α : Type*} (xs : List ℤ) (f : List ℤ → α) :
    withListInt xs f = f xs := by
  unfold withListInt
  rw [evalListInt_eq]
  cases xs <;> rfl

/-- Strictly evaluates all rows and entries of a `List (List ℤ)` during kernel reduction. -/
def evalMatInt : List (List ℤ) → List (List ℤ)
  | [] => []
  | r :: rs => withListInt r fun r' ↦
      match evalMatInt rs with
      | [] => [r']
      | s :: ss => r' :: s :: ss

lemma evalMatInt_eq (rs : List (List ℤ)) : evalMatInt rs = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [evalMatInt, withListInt_eq, ih]
      cases rs <;> rfl

/-- Binds a strictly evaluated `List (List ℤ)` before applying `f` during kernel reduction. -/
def withMatInt {α : Type*} (rs : List (List ℤ)) (f : List (List ℤ) → α) : α :=
  match evalMatInt rs with
  | [] => f []
  | s :: ss => f (s :: ss)

@[simp]
lemma withMatInt_eq {α : Type*} (rs : List (List ℤ)) (f : List (List ℤ) → α) :
    withMatInt rs f = f rs := by
  unfold withMatInt
  rw [evalMatInt_eq]
  cases rs <;> rfl

/-- Packs a list of `Nat` lanes `< B` into a single `Nat` in radix `B`. -/
def packBase (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => forceNat (packBase B xs) fun hi ↦ forceNat (x + hi * B) id

lemma packBase_cons (B x : ℕ) (xs : List ℕ) :
    packBase B (x :: xs) = x + packBase B xs * B := rfl

/-- Unpacks `k` `Nat` lanes from a radix-`B` packed `Nat` word. -/
def unpackBase (B : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, w =>
      forceNat (w % B) fun lane ↦
      forceNat (w / B) fun w' ↦
        lane :: unpackBase B k w'

lemma unpackBase_packBase (B : ℕ) (xs : List ℕ) (hxs : ∀ x ∈ xs, x < B) :
    unpackBase B xs.length (packBase B xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xt ih =>
      have hx : x < B := hxs x List.mem_cons_self
      have hB : 0 < B := Nat.zero_lt_of_lt hx
      have hm1 : (x + packBase B xt * B) % B = x := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      have hm2 : (x + packBase B xt * B) / B = packBase B xt := by
        rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hx, zero_add]
      simp only [List.length_cons, unpackBase, packBase_cons, forceNat_eq, hm1, hm2]
      congr 1
      exact ih fun a ha ↦ hxs a (List.mem_cons_of_mem x ha)

lemma packBase_replicate_zero (B n : ℕ) : packBase B (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, packBase_cons, ih]

lemma packBase_zipWith_add (B : ℕ) (xs : List ℕ) : ∀ (ys : List ℕ), xs.length = ys.length →
    packBase B (List.zipWith (· + ·) xs ys) = packBase B xs + packBase B ys := by
  induction xs with
  | nil =>
      intro ys hlen
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons x xs ih =>
      intro ys hlen
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simp only [List.zipWith_cons_cons, packBase_cons, ih ys hlen]
          ring

lemma packBase_map_mul (B c : ℕ) (xs : List ℕ) :
    packBase B (xs.map (c * ·)) = c * packBase B xs := by
  induction xs with
  | nil => simp [packBase]
  | cons x xs ih => simp only [List.map_cons, packBase_cons, ih]; ring

/-- Computes a weighted dot product over radix-packed `Nat` words. -/
def dotPacked : List ℕ → List ℕ → ℕ → ℕ
  | c :: cs, p :: ps, acc =>
      forceNat (acc + c * p) fun acc' ↦ dotPacked cs ps acc'
  | _, _, acc => acc

/-- Reference lane-wise linear combination $\text{acc} + \sum_j c_j v_j$ over `List ℕ`. -/
def vecLinearComb : List ℕ → List (List ℕ) → List ℕ → List ℕ
  | c :: cs, v :: vs, acc =>
      vecLinearComb cs vs (List.zipWith (fun a x ↦ a + c * x) acc v)
  | _, _, acc => acc

lemma dotPacked_eq_packBase_vecLinearComb {K : ℕ} (B : ℕ) (cs : List ℕ) :
    ∀ (vs : List (List ℕ)) (acc : List ℕ),
      (∀ v ∈ vs, v.length = K) → acc.length = K →
      dotPacked cs (vs.map (packBase B)) (packBase B acc) =
        packBase B (vecLinearComb cs vs acc) := by
  induction cs with
  | nil => intro _ _ _ _; rfl
  | cons c cs ih =>
      intro vs acc hvs hacc
      cases vs with
      | nil => rfl
      | cons v vs =>
          have hv : v.length = K := hvs v List.mem_cons_self
          have hcomb : List.zipWith (fun a x ↦ a + c * x) acc v =
              List.zipWith (· + ·) acc (v.map (c * ·)) := by
            clear hvs cs vs ih hacc hv
            induction acc generalizing v with
            | nil => simp
            | cons a as iha =>
                cases v with
                | nil => simp
                | cons x xs => simp [iha xs]
          have hpack : packBase B acc + c * packBase B v =
              packBase B (List.zipWith (fun a x ↦ a + c * x) acc v) := by
            rw [hcomb, packBase_zipWith_add B acc (v.map (c * ·)) (by simp [hacc, hv]),
              packBase_map_mul]
          simp only [List.map_cons, dotPacked, forceNat_eq, vecLinearComb, hpack]
          exact ih vs _ (fun u hu ↦ hvs u (List.mem_cons_of_mem v hu)) (by simp [hacc, hv])

/-! ### 5b. List Indexing & `evalWeightedGram` Soundness -/

private lemma zipWith_getD {α β γ : Type*} (f : α → β → γ) (da : α) (db : β) (dc : γ) :
    ∀ (as : List α) (bs : List β) (q : ℕ), q < as.length → q < bs.length →
      (List.zipWith f as bs).getD q dc = f (as.getD q da) (bs.getD q db) := by
  intro as
  induction as with
  | nil => intro _ _ hq; simp at hq
  | cons a as ih =>
      intro bs q hqa hqb
      cases bs with
      | nil => simp at hqb
      | cons b bs =>
          cases q with
          | zero => rfl
          | succ q =>
              exact ih bs q (Nat.lt_of_succ_lt_succ hqa) (Nat.lt_of_succ_lt_succ hqb)

private lemma map_getD {α β : Type*} (f : α → β) (da : α) (db : β) :
    ∀ (as : List α) (q : ℕ), q < as.length → (as.map f).getD q db = f (as.getD q da) := by
  intro as
  induction as with
  | nil => intro _ hq; simp at hq
  | cons a as ih =>
      intro q hq
      cases q with
      | zero => rfl
      | succ q => exact ih q (Nat.lt_of_succ_lt_succ hq)

private lemma replicate_getD {α : Type*} (n : ℕ) (v d : α) :
    ∀ q < n, (List.replicate n v).getD q d = v := by
  induction n with
  | zero => intro _ hq; omega
  | succ n ih =>
      intro q hq
      cases q with
      | zero => rfl
      | succ q => exact ih q (Nat.lt_of_succ_lt_succ hq)

private lemma getD_mem_of_lt {α : Type*} :
    ∀ (xs : List α) (d : α) {q : ℕ}, q < xs.length → xs.getD q d ∈ xs := by
  intro xs d
  induction xs with
  | nil => intro _ hq; simp at hq
  | cons x xt ih =>
      intro q hq
      cases q with
      | zero => exact List.mem_cons_self
      | succ q => exact List.mem_cons_of_mem x (ih (Nat.lt_of_succ_lt_succ hq))

lemma vecLinearComb_length {K : ℕ} (cs : List ℕ) :
    ∀ (vs : List (List ℕ)) (acc : List ℕ),
      (∀ v ∈ vs, v.length = K) → acc.length = K →
      (vecLinearComb cs vs acc).length = K := by
  induction cs with
  | nil => intro _ acc _ hacc; exact hacc
  | cons c cs ih =>
      intro vs acc hvs hacc
      cases vs with
      | nil => exact hacc
      | cons v vs =>
          have hv : v.length = K := hvs v List.mem_cons_self
          exact ih vs _ (fun u hu ↦ hvs u (List.mem_cons_of_mem v hu)) (by simp [hacc, hv])

lemma vecLinearComb_bound {K : ℕ} (Bw Bu : ℕ) (cs : List ℕ) :
    ∀ (vs : List (List ℕ)) (acc : List ℕ) (Bacc : ℕ),
      (∀ v ∈ vs, v.length = K ∧ ∀ x ∈ v, x ≤ Bu) →
      acc.length = K → (∀ a ∈ acc, a ≤ Bacc) →
      (∀ w ∈ cs, w ≤ Bw) →
      ∀ y ∈ vecLinearComb cs vs acc, y ≤ Bacc + cs.length * (Bw * Bu) := by
  induction cs with
  | nil =>
      intro _ acc Bacc _ _ hacc _ y hy
      simpa using hacc y hy
  | cons c cs ih =>
      intro vs acc Bacc hvs haccL haccB hcs y hy
      cases vs with
      | nil =>
          have := haccB y hy
          exact le_trans this (Nat.le_add_right _ _)
      | cons v vs =>
          have hv := hvs v List.mem_cons_self
          have hc : c ≤ Bw := hcs c List.mem_cons_self
          have hzB : ∀ z ∈ List.zipWith (fun a x ↦ a + c * x) acc v, z ≤ Bacc + Bw * Bu := by
            have hv2 : ∀ x ∈ v, x ≤ Bu := hv.2
            clear ih hy hvs vs cs hcs haccL hv
            revert hv2 haccB
            induction acc generalizing v with
            | nil => simp
            | cons a as iha =>
                intro haccB hv2
                cases v with
                | nil => simp
                | cons x xs =>
                    intro z hz
                    simp only [List.zipWith_cons_cons, List.mem_cons] at hz
                    rcases hz with rfl | hz
                    · have ha : a ≤ Bacc := haccB a List.mem_cons_self
                      have hx : x ≤ Bu := hv2 x List.mem_cons_self
                      exact Nat.add_le_add ha (Nat.mul_le_mul hc hx)
                    · exact iha (v := xs)
                        (fun t ht ↦ haccB t (List.mem_cons_of_mem a ht))
                        (fun t ht ↦ hv2 t (List.mem_cons_of_mem x ht)) z hz
          have hstep := ih vs (List.zipWith (fun a x ↦ a + c * x) acc v) (Bacc + Bw * Bu)
            (fun u hu ↦ hvs u (List.mem_cons_of_mem v hu))
            (by simp [haccL, hv.1]) hzB
            (fun w hw ↦ hcs w (List.mem_cons_of_mem c hw)) y hy
          simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm (Bw * Bu)] using hstep

lemma vecLinearComb_getD {K : ℕ} (cs : List ℕ) :
    ∀ (vs : List (List ℕ)) (acc : List ℕ),
      cs.length = vs.length → (∀ v ∈ vs, v.length = K) → acc.length = K →
      ∀ q < K, (vecLinearComb cs vs acc).getD q 0 =
        acc.getD q 0 + (List.zipWith (fun w v ↦ w * v.getD q 0) cs vs).sum := by
  induction cs with
  | nil =>
      intro vs acc _ _ _ q _
      simp [vecLinearComb]
  | cons c cs ih =>
      intro vs acc hlen hvs hacc q hq
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hv : v.length = K := hvs v List.mem_cons_self
          have hstep := ih vs (List.zipWith (fun a x ↦ a + c * x) acc v) hlen
            (fun u hu ↦ hvs u (List.mem_cons_of_mem v hu)) (by simp [hacc, hv]) q hq
          rw [vecLinearComb, hstep, zipWith_getD _ 0 0 0 acc v q (hacc ▸ hq) (hv ▸ hq),
            List.zipWith_cons_cons, List.sum_cons, Nat.add_assoc]

/-- Strictly evaluates `packBase B` across each vector in a list. -/
def mapPackBase (B : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | u :: us => forceNat (packBase B u) fun p ↦ p :: mapPackBase B us

lemma mapPackBase_eq_map (B : ℕ) (us : List (List ℕ)) : mapPackBase B us = us.map (packBase B) := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [mapPackBase, forceNat_eq, ih]

/-- Shifts a bounded signed integer `z` (`|z| ≤ m`) to a nonnegative `Nat`
`z + m` without typeclass overhead during kernel reduction. -/
def shiftToNat (m : ℕ) : ℤ → ℕ
  | Int.ofNat n => forceNat (m + n) fun k ↦ k
  | Int.negSucc n => forceNat (m - (n + 1)) fun k ↦ k

private lemma shiftToNat_spec {m : ℕ} {z : ℤ} (h : z.natAbs ≤ m) :
    shiftToNat m z ≤ 2 * m ∧ ((shiftToNat m z : ℕ) : ℤ) = z + (m : ℤ) := by
  cases z <;> simp only [Int.natAbs, shiftToNat, forceNat_eq, Int.ofNat_eq_natCast] at h ⊢ <;>
    omega

/-- Tail-recursive integer list sum helper avoiding `HAdd` typeclass overhead. -/
def fastIntSumAux : List ℤ → ℤ → ℤ
  | [], acc => acc
  | x :: xs, acc => forceInt (Int.add acc x) fun acc' ↦ fastIntSumAux xs acc'

private lemma fastIntSumAux_eq :
    ∀ (xs : List ℤ) (acc : ℤ), fastIntSumAux xs acc = acc + xs.sum
  | [], acc => by simp [fastIntSumAux]
  | x :: xs, acc => by
      simp only [fastIntSumAux, forceInt_eq]
      change fastIntSumAux xs (acc + x) = acc + (x :: xs).sum
      rw [fastIntSumAux_eq xs (acc + x), List.sum_cons, add_assoc]

/-- Fast integer list sum equivalent to `List.sum`. -/
def fastIntSum (xs : List ℤ) : ℤ :=
  fastIntSumAux xs 0

@[simp]
private lemma fastIntSum_eq (xs : List ℤ) : fastIntSum xs = xs.sum := by
  rw [fastIntSum, fastIntSumAux_eq, zero_add]

/-- Extracts `K` coordinate slices `(vs.map fun v ↦ v.getD p 0)` in $O(K \cdot |vs|)$ time. -/
def transposeCols : ℕ → List (List ℤ) → List (List ℤ)
  | 0, _ => []
  | k + 1, vs =>
      withListInt (vs.map fun v ↦ v.headD 0) fun row ↦
        row :: transposeCols k (vs.map List.tail)

private lemma headD_eq_getD_zero (v : List ℤ) : v.headD 0 = v.getD 0 0 := by
  cases v <;> rfl

private lemma tail_getD_eq_getD_succ (v : List ℤ) (q : ℕ) :
    v.tail.getD q 0 = v.getD (q + 1) 0 := by
  cases v <;> rfl

private lemma transposeCols_eq :
    ∀ (K : ℕ) (vs : List (List ℤ)),
      transposeCols K vs = (List.range K).map fun p ↦ vs.map fun v ↦ v.getD p 0
  | 0, _ => rfl
  | k + 1, vs => by
      rw [transposeCols, withListInt_eq, List.range_succ_eq_map, List.map_cons, List.map_map,
        transposeCols_eq k (vs.map List.tail)]
      congr 1
      · exact List.map_congr_left fun v _ ↦ headD_eq_getD_zero v
      · refine List.map_congr_left fun q _ ↦ ?_
        rw [Function.comp_apply, List.map_map]
        exact List.map_congr_left fun v _ ↦ tail_getD_eq_getD_succ v q

private lemma zipWith_intMul_map_getD :
    ∀ (cs : List ℤ) (vs : List (List ℤ)) (p : ℕ),
      List.zipWith Int.mul cs (vs.map fun v ↦ v.getD p 0) =
        List.zipWith (fun c v ↦ c * v.getD p 0) cs vs
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | c :: cs, v :: vs, p => by
      simp only [List.map_cons, List.zipWith_cons_cons, zipWith_intMul_map_getD cs vs p]
      rfl

private lemma map_zipWith_transposeCols (K : ℕ) (cs : List ℤ) (vs : List (List ℤ)) :
    (transposeCols K vs).map (fun colP ↦ List.zipWith Int.mul cs colP) =
      (List.range K).map fun p ↦ List.zipWith (fun c v ↦ c * v.getD p 0) cs vs := by
  rw [transposeCols_eq, List.map_map]
  refine List.map_congr_left fun p _ ↦ ?_
  exact zipWith_intMul_map_getD cs vs p

/-- Kernel boolean precondition checking lane bounds and non-overflow
for `evalWeightedGram`. -/
def checkGramPrecond (B K shiftU biasC : ℕ) (cs : List ℤ) (vs sRows : List (List ℤ)) : Bool :=
  Nat.ble 1 B && Nat.beq cs.length vs.length &&
    vs.all (fun v ↦ Nat.beq v.length K &&
      v.all fun x ↦ Nat.ble x.natAbs shiftU) &&
    sRows.all (fun r ↦ r.all fun z ↦ Nat.ble z.natAbs biasC) &&
    Nat.ble (cs.length * ((2 * biasC) * (2 * shiftU)) + 1) B &&
    Nat.ble (cs.length * (1 * (2 * shiftU)) + 1) B

/-- Evaluates the integer weighted Gram matrix $\sum_j c_j v_j v_j^T$
via radix-`B` SIMD packing. -/
def evalWeightedGram (B0 K shiftU0 biasC0 : ℕ) (cs0 : List ℤ) (vs0 : List (List ℤ)) :
    Option (List (List ℤ)) :=
  forceNat B0 fun B ↦
  forceNat shiftU0 fun shiftU ↦
  forceNat biasC0 fun biasC ↦
  withListInt cs0 fun cs ↦
  withMatInt vs0 fun vs ↦
  withMatInt ((transposeCols K vs).map fun colP ↦ List.zipWith Int.mul cs colP) fun sRows ↦
  if checkGramPrecond B K shiftU biasC cs vs sRows then
    let uVecs : List (List ℕ) := vs.map fun v ↦ v.map (shiftToNat shiftU)
    withListNat (mapPackBase B uVecs) fun packedU ↦
    withListNat (unpackBase B K (dotPacked (List.replicate cs.length 1) packedU 0))
      fun colSumU ↦
    withListInt (colSumU.map fun colSum ↦ Int.mul (Int.ofNat biasC) (Int.ofNat colSum))
      fun biasColTerms ↦
    withMatInt (sRows.map fun sRowList ↦
      withListNat (sRowList.map (shiftToNat biasC)) fun wRow ↦
      withListNat (unpackBase B K (dotPacked wRow packedU 0)) fun lanes ↦
      forceInt (Int.mul (Int.ofNat shiftU) (fastIntSum sRowList)) fun shiftTerm ↦
        List.zipWith
          (fun (lane : ℕ) (bTerm : ℤ) ↦ Int.sub (Int.sub (Int.ofNat lane) shiftTerm) bTerm)
          lanes biasColTerms)
      fun outRows ↦ some outRows
  else
    none

private lemma gram_row_combine (shiftU biasC : ℕ) :
    ∀ (cs : List ℤ) (vs : List (List ℤ)) (p q : ℕ),
      cs.length = vs.length →
      (∀ v ∈ vs, q < v.length ∧ (v.getD q 0).natAbs ≤ shiftU) →
      (∀ z ∈ List.zipWith (fun c v ↦ c * v.getD p 0) cs vs, z.natAbs ≤ biasC) →
      (((List.zipWith (fun w (u : List ℕ) ↦ w * u.getD q 0)
          ((List.zipWith (fun c (v : List ℤ) ↦ c * v.getD p 0) cs vs).map
            (shiftToNat biasC))
          (vs.map fun v ↦ v.map (shiftToNat shiftU))).sum : ℕ) : ℤ) -
        (shiftU : ℤ) * (List.zipWith (fun c (v : List ℤ) ↦ c * v.getD p 0) cs vs).sum -
        (biasC : ℤ) * (((List.zipWith (fun w (u : List ℕ) ↦ w * u.getD q 0)
          (List.replicate cs.length 1)
          (vs.map fun v ↦ v.map (shiftToNat shiftU))).sum : ℕ) : ℤ) =
        (List.zipWith (fun c (v : List ℤ) ↦ c * v.getD p 0 * v.getD q 0) cs vs).sum := by
  intro cs
  induction cs with
  | nil =>
      intro vs _ _ hlen _ _
      cases vs with
      | nil => simp
      | cons _ _ => simp at hlen
  | cons c cs ih =>
      intro vs p q hlen hvq hzp
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hv0 := hvq v List.mem_cons_self
          have hz0 := hzp (c * v.getD p 0) List.mem_cons_self
          have hstep := ih vs p q hlen
            (fun u hu ↦ hvq u (List.mem_cons_of_mem v hu))
            (fun z hz ↦ hzp z (List.mem_cons_of_mem _ hz))
          have hmap_v : (v.map (shiftToNat shiftU)).getD q 0 =
              shiftToNat shiftU (v.getD q 0) :=
            map_getD (shiftToNat shiftU) 0 0 v q hv0.1
          simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons,
            List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, hmap_v] at hstep ⊢
          have hto1 : ((shiftToNat biasC (c * v.getD p 0) : ℕ) : ℤ) =
              c * v.getD p 0 + (biasC : ℤ) := (shiftToNat_spec hz0).2
          have hto2 : ((shiftToNat shiftU (v.getD q 0) : ℕ) : ℤ) =
              v.getD q 0 + (shiftU : ℤ) := (shiftToNat_spec hv0.2).2
          rw [hto1, hto2]
          linear_combination hstep

theorem evalWeightedGram_sound {B K shiftU biasC : ℕ} {cs : List ℤ} {vs : List (List ℤ)}
    {rows : List (List ℤ)}
    (heval : evalWeightedGram B K shiftU biasC cs vs = some rows)
    {p q : ℕ} (hp : p < K) (hq : q < K) :
    (rows.getD p []).getD q 0 =
      (List.zipWith (fun c v ↦ c * v.getD p 0 * v.getD q 0) cs vs).sum := by
  unfold evalWeightedGram at heval
  simp only [forceNat_eq, forceInt_eq, withListInt_eq, withMatInt_eq, withListNat_eq,
    map_zipWith_transposeCols, fastIntSum_eq] at heval
  split_ifs at heval with hcond
  simp only [checkGramPrecond, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    Nat.ble_eq, Nat.beq_eq, and_assoc] at hcond
  rcases hcond with ⟨_hBpos, hlen, hvs, hbias0, hboundW, hbound1⟩
  have hbias : ∀ r ∈ List.range K,
      ∀ z ∈ List.zipWith (fun c (v : List ℤ) ↦ c * v.getD r 0) cs vs, z.natAbs ≤ biasC :=
    fun r hr z hz ↦ hbias0 _ ⟨r, hr, rfl⟩ z hz
  injection heval with hrows
  subst hrows
  let uVecs : List (List ℕ) := vs.map fun v ↦ v.map (shiftToNat shiftU)
  have huLen : uVecs.length = cs.length := by simp [uVecs, hlen]
  have huSpec : ∀ u ∈ uVecs, u.length = K ∧ ∀ y ∈ u, y ≤ 2 * shiftU := by
    intro u hu
    rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
    refine ⟨by simp [(hvs v hv).1], ?_⟩
    intro y hy
    rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
    exact (shiftToNat_spec ((hvs v hv).2 x hx)).1
  have hdot : ∀ (ws : List ℕ) (Bw : ℕ), ws.length = cs.length → (∀ w ∈ ws, w ≤ Bw) →
      cs.length * (Bw * (2 * shiftU)) + 1 ≤ B →
      (unpackBase B K (dotPacked ws (mapPackBase B uVecs) 0)).length = K ∧
      ∀ r < K, (unpackBase B K (dotPacked ws (mapPackBase B uVecs) 0)).getD r 0 =
        (List.zipWith (fun w u ↦ w * u.getD r 0) ws uVecs).sum := by
    intro ws Bw hwlen hwB hBwLt
    have hdot_eq : dotPacked ws (mapPackBase B uVecs) 0 =
        packBase B (vecLinearComb ws uVecs (List.replicate K 0)) := by
      conv_lhs => rw [mapPackBase_eq_map, ← packBase_replicate_zero B K]
      exact dotPacked_eq_packBase_vecLinearComb B ws uVecs (List.replicate K 0)
        (fun u hu ↦ (huSpec u hu).1) List.length_replicate
    rw [hdot_eq]
    have hvlen : (vecLinearComb ws uVecs (List.replicate K 0)).length = K :=
      vecLinearComb_length ws uVecs (List.replicate K 0)
        (fun u hu ↦ (huSpec u hu).1) List.length_replicate
    have hvlt : ∀ y ∈ vecLinearComb ws uVecs (List.replicate K 0), y < B := by
      intro y hy
      have hle := vecLinearComb_bound Bw (2 * shiftU) ws uVecs (List.replicate K 0) 0
        huSpec List.length_replicate (by simp) hwB y hy
      rw [hwlen] at hle
      omega
    have hunp : unpackBase B K (packBase B (vecLinearComb ws uVecs (List.replicate K 0))) =
        vecLinearComb ws uVecs (List.replicate K 0) := by
      have h := unpackBase_packBase B (vecLinearComb ws uVecs (List.replicate K 0)) hvlt
      rwa [hvlen] at h
    rw [hunp]
    refine ⟨hvlen, fun r hr ↦ ?_⟩
    rw [vecLinearComb_getD ws uVecs (List.replicate K 0) (by omega)
      (fun u hu ↦ (huSpec u hu).1) List.length_replicate r hr,
      replicate_getD K 0 0 r hr, zero_add]
  have hcol := hdot (List.replicate cs.length 1) 1 List.length_replicate
    (fun w hw ↦ by simp [List.mem_replicate] at hw; omega) hbound1
  let sRowList : List ℤ := List.zipWith (fun c v ↦ c * v.getD p 0) cs vs
  let wRow : List ℕ := sRowList.map (shiftToNat biasC)
  have hwRowLen : wRow.length = cs.length := by simp [wRow, sRowList, hlen]
  have hwRowB : ∀ w ∈ wRow, w ≤ 2 * biasC := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨z, hz, rfl⟩
    exact (shiftToNat_spec (hbias p (List.mem_range.mpr hp) z hz)).1
  have hlanes := hdot wRow (2 * biasC) hwRowLen hwRowB hboundW
  rw [List.map_map]
  have hpRange : p < (List.range K).length := by simpa using hp
  rw [map_getD _ 0 [] (List.range K) p hpRange]
  have hrp : (List.range K).getD p 0 = p := by
    simp [List.getD_eq_getElem?_getD, hp]
  rw [hrp]
  dsimp only [Function.comp_def]
  rw [List.zipWith_map_right]
  change (List.zipWith
      (fun (lane colSum : ℕ) ↦
        (lane : ℤ) - (shiftU : ℤ) * sRowList.sum - (biasC : ℤ) * (colSum : ℤ))
      (unpackBase B K (dotPacked wRow (mapPackBase B uVecs) 0))
      (unpackBase B K (dotPacked (List.replicate cs.length 1) (mapPackBase B uVecs) 0))).getD q 0 =
        _
  have hq1 : q < (unpackBase B K (dotPacked wRow (mapPackBase B uVecs) 0)).length := by
    rw [hlanes.1]; exact hq
  have hq2 : q <
      (unpackBase B K (dotPacked (List.replicate cs.length 1) (mapPackBase B uVecs) 0)).length := by
    rw [hcol.1]; exact hq
  rw [zipWith_getD _ 0 0 0 _ _ q hq1 hq2, hlanes.2 q hq, hcol.2 q hq]
  exact gram_row_combine shiftU biasC cs vs p q hlen
    (fun v hv ↦ by
      have hqv : q < v.length := (hvs v hv).1 ▸ hq
      exact ⟨hqv, (hvs v hv).2 _ (getD_mem_of_lt v 0 hqv)⟩)
    (hbias p (List.mem_range.mpr hp))

/-! ### 4. Rank-1 Difference Bound & Trig Interval Soundness -/

lemma abs_re_oneBody_vecMulVec_diff_le {N : ℕ} {v vHat : Fin N → ℝ} {ε : ℝ}
    (hv : ∑ p : Fin N, v p ^ 2 = 1) (hε : 0 ≤ ε)
    (hdiff : ∑ p : Fin N, (v p - vHat p) ^ 2 ≤ ε ^ 2)
    (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    |(star ψ ⬝ᵥ (oneBodyHamiltonian
        (Matrix.vecMulVec v v - Matrix.vecMulVec vHat vHat) *ᵥ ψ)).re| ≤
      (4 * ε + 2 * ε ^ 2) * vecNormSq ψ := by
  let δ : Fin N → ℝ := v - vHat
  have hdecomp : Matrix.vecMulVec v v - Matrix.vecMulVec vHat vHat =
      Matrix.vecMulVec δ v + Matrix.vecMulVec v δ - Matrix.vecMulVec δ δ := by
    ext p q
    simp [δ, Matrix.vecMulVec_apply]
    ring
  have hsqrt_v : √(∑ p : Fin N, v p ^ 2) = 1 := by rw [hv, Real.sqrt_one]
  have hsqrt_δ : √(∑ p : Fin N, δ p ^ 2) ≤ ε :=
    (Real.sqrt_le_sqrt hdiff).trans_eq (Real.sqrt_sq hε)
  rw [hdecomp, oneBodyHamiltonian_sub, oneBodyHamiltonian_add,
    Matrix.sub_mulVec, Matrix.add_mulVec, dotProduct_sub, dotProduct_add,
    Complex.sub_re, Complex.add_re]
  have b1 := abs_re_oneBody_vecMulVec_le δ v ψ
  have b2 := abs_re_oneBody_vecMulVec_le v δ ψ
  have b3 := abs_re_oneBody_vecMulVec_le δ δ ψ
  rw [hsqrt_v, mul_one] at b1
  rw [hsqrt_v, mul_one] at b2
  have b1' : |(star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec δ v) *ᵥ ψ)).re| ≤
      (2 * ε) * vecNormSq ψ :=
    b1.trans (mul_le_mul_of_nonneg_right (by linarith) (vecNormSq_nonneg ψ))
  have b2' : |(star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec v δ) *ᵥ ψ)).re| ≤
      (2 * ε) * vecNormSq ψ :=
    b2.trans (mul_le_mul_of_nonneg_right (by linarith) (vecNormSq_nonneg ψ))
  have hδsq : √(∑ p : Fin N, δ p ^ 2) * √(∑ p : Fin N, δ p ^ 2) ≤ ε * ε :=
    mul_le_mul hsqrt_δ hsqrt_δ (Real.sqrt_nonneg _) hε
  have b3' : |(star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec δ δ) *ᵥ ψ)).re| ≤
      (2 * ε ^ 2) * vecNormSq ψ :=
    b3.trans (mul_le_mul_of_nonneg_right (by nlinarith) (vecNormSq_nonneg ψ))
  have htri : ∀ a b c : ℝ, |a + b - c| ≤ |a| + |b| + |c| := fun a b c ↦ by
    linarith [abs_sub (a + b) c, abs_add_le a b]
  linarith [htri (star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec δ v) *ᵥ ψ)).re
    (star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec v δ) *ᵥ ψ)).re
    (star ψ ⬝ᵥ (oneBodyHamiltonian (Matrix.vecMulVec δ δ) *ᵥ ψ)).re]

lemma abs_re_oneBody_smul_vecMulVec_diff_le {N : ℕ} (c : ℝ) {v vHat : Fin N → ℝ} {ε : ℝ}
    (hv : ∑ p : Fin N, v p ^ 2 = 1) (hε : 0 ≤ ε)
    (hdiff : ∑ p : Fin N, (v p - vHat p) ^ 2 ≤ ε ^ 2)
    (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    |(star ψ ⬝ᵥ (oneBodyHamiltonian
        (c • (Matrix.vecMulVec v v - Matrix.vecMulVec vHat vHat)) *ᵥ ψ)).re| ≤
      |c| * ((4 * ε + 2 * ε ^ 2) * vecNormSq ψ) := by
  have h1 := abs_re_oneBody_vecMulVec_diff_le hv hε hdiff ψ
  rw [oneBodyHamiltonian_smul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, abs_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

/-- Fixed-point denominator $S = 2^{20} = 1048576$ for interval trigonometric bounds. -/
def ivScale : ℤ := 1048576

private lemma nat_div_le_div (a : ℕ) {d : ℕ} (hd : 0 < d) :
    ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / (d : ℝ) := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast Nat.div_mul_le_self a d

private lemma div_le_nat_ceilDiv (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (a : ℝ) / (d : ℝ) ≤ ((((d - 1) + a) / d : ℕ) : ℝ) := by
  have hmod := Nat.div_add_mod ((d - 1) + a) d
  have hlt := Nat.mod_lt ((d - 1) + a) hd
  rw [Nat.mul_comm] at hmod
  have hle : a ≤ (((d - 1) + a) / d) * d := by omega
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast hle

private lemma nat_sub_le_of_nonneg (a b : ℕ) {z : ℝ} (hz0 : 0 ≤ z)
    (hz : (a : ℝ) - (b : ℝ) ≤ z) : ((a - b : ℕ) : ℝ) ≤ z := by
  rcases le_or_gt b a with h | h
  · rwa [Nat.cast_sub h]
  · simp [Nat.sub_eq_zero_of_le h.le, hz0]

private lemma sub_le_nat_sub (a b : ℕ) : (a : ℝ) - (b : ℝ) ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_or_gt b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    have hab : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h.le
    linarith

/-- Clamps a `Nat` upper endpoint to `1048576` (`= 2^{20}`). -/
def capScale (x : ℕ) : ℕ :=
  if Nat.ble x 1048576 then x else 1048576

private lemma capScale_le (x : ℕ) : capScale x ≤ 1048576 := by
  unfold capScale
  split_ifs with h
  · exact Nat.ble_eq.mp h
  · exact le_rfl

private lemma le_capScale_div {x : ℕ} {z : ℝ} (hz1 : z ≤ 1)
    (hzx : z ≤ (x : ℝ) / 1048576) : z ≤ (capScale x : ℝ) / 1048576 := by
  unfold capScale
  split_ifs with h
  · exact hzx
  · push_cast; linarith

private lemma cos_le_deg4 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t ↦ 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hdf : ∀ t : ℝ, HasDerivAt f (Real.sin t - (t - t ^ 3 / 6)) t := fun t ↦ by
    have h1 : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 t := hasDerivAt_const t 1
    have h2 : HasDerivAt (fun t : ℝ ↦ t ^ 2 / 2) (2 * t ^ 1 / 2) t :=
      (hasDerivAt_pow 2 t).div_const 2
    have h4 : HasDerivAt (fun t : ℝ ↦ t ^ 4 / 24) (4 * t ^ 3 / 24) t :=
      (hasDerivAt_pow 4 t).div_const 24
    convert ((h1.sub h2).add h4).sub (Real.hasDerivAt_cos t) using 1
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun t _ ↦ (hdf t).continuousAt.continuousWithinAt
    · exact fun t _ ↦ (hdf t).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := Set.mem_Ici.mp (interior_subset ht)
      linarith [Real.sin_ge_sub_cube ht0]
  have h0 : f 0 ≤ f x := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  dsimp [f] at h0
  linarith [Real.cos_zero]

private lemma sin_le_deg5 {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let g : ℝ → ℝ := fun t ↦ t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t
  have hdg : ∀ t : ℝ, HasDerivAt g (1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) t := fun t ↦ by
    have h1 : HasDerivAt (fun t : ℝ ↦ t) 1 t := hasDerivAt_id t
    have h3 : HasDerivAt (fun t : ℝ ↦ t ^ 3 / 6) (3 * t ^ 2 / 6) t :=
      (hasDerivAt_pow 3 t).div_const 6
    have h5 : HasDerivAt (fun t : ℝ ↦ t ^ 5 / 120) (5 * t ^ 4 / 120) t :=
      (hasDerivAt_pow 5 t).div_const 120
    convert ((h1.sub h3).add h5).sub (Real.hasDerivAt_sin t) using 1
    ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun t _ ↦ (hdg t).continuousAt.continuousWithinAt
    · exact fun t _ ↦ (hdg t).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := Set.mem_Ici.mp (interior_subset ht)
      linarith [cos_le_deg4 ht0]
  have h0 : g 0 ≤ g x := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  dsimp [g] at h0
  linarith [Real.sin_zero]

/-- Membership of $x \in \mathbb{R}$ in the scaled integer interval
$[\text{iv}.1 / S, \text{iv}.2 / S]$. -/
def InIv (iv : ℤ × ℤ) (x : ℝ) : Prop :=
  (iv.1 : ℝ) / (ivScale : ℝ) ≤ x ∧ x ≤ (iv.2 : ℝ) / (ivScale : ℝ)

/-- Membership of $x \in [0, 1]$ in a `1048576`-bounded `Nat × Nat` interval. -/
def InNatUnitIv (iv : ℕ × ℕ) (x : ℝ) : Prop :=
  iv.2 ≤ 1048576 ∧ (iv.1 : ℝ) / 1048576 ≤ x ∧ x ≤ (iv.2 : ℝ) / 1048576

lemma InNatUnitIv.nonneg_x {iv : ℕ × ℕ} {x : ℝ} (h : InNatUnitIv iv x) : 0 ≤ x :=
  le_trans (by positivity) h.2.1

/-- Sound `Nat` interval propagation for $(\sin 2z, \cos 2z)$ from
$(\sin z, \cos z)$ on $[0, \pi/4]$. -/
def doubleAngleNat (sc : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
  forcePairNatIv sc fun s c ↦
  forceNat ((2 * s.1 * c.1) / 1048576) fun s2_lo ↦
  forceNat (capScale ((1048575 + 2 * s.2 * c.2) / 1048576)) fun s2_hi ↦
  forceNat (1048576 - (1048575 + 2 * s.2 * s.2) / 1048576) fun c2_lo ↦
  forceNat (1048576 - (2 * s.1 * s.1) / 1048576) fun c2_hi ↦
    ((s2_lo, s2_hi), (c2_lo, c2_hi))

lemma doubleAngleNat_sound {z : ℝ} {sc : (ℕ × ℕ) × (ℕ × ℕ)}
    (hz0 : 0 ≤ z) (hz : 2 * z ≤ π / 2)
    (hs : InNatUnitIv sc.1 (Real.sin z)) (hc : InNatUnitIv sc.2 (Real.cos z)) :
    InNatUnitIv (doubleAngleNat sc).1 (Real.sin (2 * z)) ∧
      InNatUnitIv (doubleAngleNat sc).2 (Real.cos (2 * z)) := by
  rcases sc with ⟨⟨slo, shi⟩, ⟨clo, chi⟩⟩
  simp only [doubleAngleNat, forcePairNatIv_eq, forceNat_eq]
  have hS : 0 < (1048576 : ℕ) := by norm_num
  have hcos2 : Real.cos (2 * z) = 1 - 2 * Real.sin z ^ 2 := by
    linear_combination Real.cos_two_mul z + 2 * Real.sin_sq_add_cos_sq z
  have hsin_nn : 0 ≤ Real.sin z := hs.nonneg_x
  have hcos_nn : 0 ≤ Real.cos z := hc.nonneg_x
  refine ⟨⟨capScale_le _, ?_, ?_⟩, ⟨Nat.sub_le _ _, ?_, ?_⟩⟩
  · calc (((2 * slo * clo) / 1048576 : ℕ) : ℝ) / 1048576
        ≤ ((2 * slo * clo : ℕ) : ℝ) / 1048576 / 1048576 := by
          gcongr; exact nat_div_le_div _ hS
      _ = 2 * ((slo : ℝ) / 1048576) * ((clo : ℝ) / 1048576) := by push_cast; ring
      _ ≤ 2 * Real.sin z * Real.cos z := by
          have := mul_le_mul hs.2.1 hc.2.1 (by positivity) hsin_nn
          linarith
      _ = Real.sin (2 * z) := (Real.sin_two_mul z).symm
  · refine le_capScale_div (Real.sin_le_one _) ?_
    calc Real.sin (2 * z) = 2 * Real.sin z * Real.cos z := Real.sin_two_mul z
      _ ≤ 2 * ((shi : ℝ) / 1048576) * ((chi : ℝ) / 1048576) := by
          have := mul_le_mul hs.2.2 hc.2.2 hcos_nn (by positivity)
          linarith
      _ = ((2 * shi * chi : ℕ) : ℝ) / 1048576 / 1048576 := by push_cast; ring
      _ ≤ (((1048575 + 2 * shi * chi) / 1048576 : ℕ) : ℝ) / 1048576 := by
          gcongr; exact div_le_nat_ceilDiv (2 * shi * chi) hS
  · have hcos2_nn : 0 ≤ Real.cos (2 * z) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hz⟩
    have hsq : Real.sin z ^ 2 ≤ ((shi : ℝ) / 1048576) ^ 2 :=
      pow_le_pow_left₀ hsin_nn hs.2.2 2
    have hceil : 2 * ((shi : ℝ) / 1048576) ^ 2 ≤
        (((1048575 + 2 * shi * shi) / 1048576 : ℕ) : ℝ) / 1048576 := by
      calc 2 * ((shi : ℝ) / 1048576) ^ 2
          = ((2 * shi * shi : ℕ) : ℝ) / 1048576 / 1048576 := by push_cast; ring
        _ ≤ (((1048575 + 2 * shi * shi) / 1048576 : ℕ) : ℝ) / 1048576 := by
            gcongr; exact div_le_nat_ceilDiv (2 * shi * shi) hS
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1048576)]
    refine nat_sub_le_of_nonneg _ _ (by positivity) ?_
    linarith [hcos2]
  · have hsq : ((slo : ℝ) / 1048576) ^ 2 ≤ Real.sin z ^ 2 :=
      pow_le_pow_left₀ (by positivity) hs.2.1 2
    have hfl : (((2 * slo * slo) / 1048576 : ℕ) : ℝ) / 1048576 ≤
        2 * ((slo : ℝ) / 1048576) ^ 2 := by
      calc (((2 * slo * slo) / 1048576 : ℕ) : ℝ) / 1048576
          ≤ ((2 * slo * slo : ℕ) : ℝ) / 1048576 / 1048576 := by
            gcongr; exact nat_div_le_div _ hS
        _ = 2 * ((slo : ℝ) / 1048576) ^ 2 := by push_cast; ring
    have hsub := sub_le_nat_sub 1048576 ((2 * slo * slo) / 1048576)
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1048576)]
    linarith [hcos2]

/-- Certified `Nat` enclosure of $(\sin(\pi m / 8192), \cos(\pi m / 8192))$
via two halvings and Taylor bounds. -/
def baseSimpleNat (m : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  forceNat ((100530944 * m) / 1000000) fun ylo ↦
  forceNat ((999999 + 100530976 * m) / 1000000) fun yhi ↦
  forceNat ((ylo * ylo) / 1048576) fun y2lo ↦
  forceNat ((1048575 + yhi * yhi) / 1048576) fun y2hi ↦
  forceNat ((1048575 + y2hi * y2hi) / 1048576) fun y4hi ↦
  let slo := ylo - (5 + (1048575 + y2hi * yhi) / 1048576) / 6
  let shi := capScale (yhi + (119 + (1048575 + y4hi * yhi) / 1048576) / 120 -
    ((y2lo * ylo) / 1048576) / 6)
  let clo := 1048576 - (1 + y2hi) / 2
  let chi := capScale (1048576 + (23 + y4hi) / 24 - y2lo / 2)
  doubleAngleNat (doubleAngleNat ((slo, shi), (clo, chi)))

lemma baseSimpleNat_sound {m : ℕ} (hm : m ≤ 2048) :
    InNatUnitIv (baseSimpleNat m).1 (Real.sin (π * (m : ℝ) / 8192)) ∧
      InNatUnitIv (baseSimpleNat m).2 (Real.cos (π * (m : ℝ) / 8192)) := by
  let y : ℝ := π * (m : ℝ) / 32768
  have hy_eq : π * (m : ℝ) / 8192 = 2 * (2 * y) := by dsimp [y]; ring
  rw [hy_eq]
  have hpi_lo : (3141592 : ℝ) / 1000000 < π := by linarith [Real.pi_gt_d6]
  have hpi_hi : π < (3141593 : ℝ) / 1000000 := by linarith [Real.pi_lt_d6]
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hm_real : (m : ℝ) ≤ 2048 := by exact_mod_cast hm
  have hy2_pi : 2 * y ≤ π / 2 := by dsimp [y]; nlinarith [Real.pi_pos]
  have hy4_pi : 2 * (2 * y) ≤ π / 2 := by dsimp [y]; nlinarith [Real.pi_pos]
  have hS : 0 < (1048576 : ℕ) := by norm_num
  have hM : 0 < (1000000 : ℕ) := by norm_num
  let ylo := (100530944 * m) / 1000000
  let yhi := (999999 + 100530976 * m) / 1000000
  let y2lo := (ylo * ylo) / 1048576
  let y2hi := (1048575 + yhi * yhi) / 1048576
  let y3lo := (y2lo * ylo) / 1048576
  let y3hi := (1048575 + y2hi * yhi) / 1048576
  let y4hi := (1048575 + y2hi * y2hi) / 1048576
  let y5hi := (1048575 + y4hi * yhi) / 1048576
  have hylo : (ylo : ℝ) / 1048576 ≤ y := by
    have h1 : (ylo : ℝ) ≤ ((100530944 * m : ℕ) : ℝ) / 1000000 := by
      simpa [ylo] using nat_div_le_div (100530944 * m) hM
    have h2 : ((100530944 * m : ℕ) : ℝ) / 1000000 / 1048576 =
        ((3141592 : ℝ) / 1000000) * (m : ℝ) / 32768 := by push_cast; ring
    have h3 : (ylo : ℝ) / 1048576 ≤ ((100530944 * m : ℕ) : ℝ) / 1000000 / 1048576 := by gcongr
    dsimp [y]
    linarith [mul_le_mul_of_nonneg_right hpi_lo.le m.cast_nonneg]
  have hyhi : y ≤ (yhi : ℝ) / 1048576 := by
    have h1 : ((100530976 * m : ℕ) : ℝ) / 1000000 ≤ (yhi : ℝ) := by
      simpa [yhi] using div_le_nat_ceilDiv (100530976 * m) hM
    have h2 : ((100530976 * m : ℕ) : ℝ) / 1000000 / 1048576 =
        ((3141593 : ℝ) / 1000000) * (m : ℝ) / 32768 := by push_cast; ring
    have h3 : ((100530976 * m : ℕ) : ℝ) / 1000000 / 1048576 ≤ (yhi : ℝ) / 1048576 := by gcongr
    dsimp [y]
    linarith [mul_le_mul_of_nonneg_right hpi_hi.le m.cast_nonneg]
  have hy2lo : (y2lo : ℝ) / 1048576 ≤ y ^ 2 := by
    calc (y2lo : ℝ) / 1048576 ≤ ((ylo * ylo : ℕ) : ℝ) / 1048576 / 1048576 := by
          gcongr; exact nat_div_le_div _ hS
      _ = ((ylo : ℝ) / 1048576) ^ 2 := by push_cast; ring
      _ ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hylo 2
  have hy2hi : y ^ 2 ≤ (y2hi : ℝ) / 1048576 := by
    calc y ^ 2 ≤ ((yhi : ℝ) / 1048576) ^ 2 := pow_le_pow_left₀ hy0 hyhi 2
      _ = ((yhi * yhi : ℕ) : ℝ) / 1048576 / 1048576 := by push_cast; ring
      _ ≤ (y2hi : ℝ) / 1048576 := by gcongr; exact div_le_nat_ceilDiv (yhi * yhi) hS
  have hy3lo : (y3lo : ℝ) / 1048576 ≤ y ^ 3 := by
    calc (y3lo : ℝ) / 1048576 ≤ ((y2lo * ylo : ℕ) : ℝ) / 1048576 / 1048576 := by
          gcongr; exact nat_div_le_div _ hS
      _ = ((y2lo : ℝ) / 1048576) * ((ylo : ℝ) / 1048576) := by push_cast; ring
      _ ≤ y ^ 2 * y := mul_le_mul hy2lo hylo (by positivity) (sq_nonneg y)
      _ = y ^ 3 := by ring
  have hy3hi : y ^ 3 ≤ (y3hi : ℝ) / 1048576 := by
    calc y ^ 3 = y ^ 2 * y := by ring
      _ ≤ ((y2hi : ℝ) / 1048576) * ((yhi : ℝ) / 1048576) :=
          mul_le_mul hy2hi hyhi hy0 (le_trans (sq_nonneg y) hy2hi)
      _ = ((y2hi * yhi : ℕ) : ℝ) / 1048576 / 1048576 := by push_cast; ring
      _ ≤ (y3hi : ℝ) / 1048576 := by gcongr; exact div_le_nat_ceilDiv (y2hi * yhi) hS
  have hy4hi : y ^ 4 ≤ (y4hi : ℝ) / 1048576 := by
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ ≤ ((y2hi : ℝ) / 1048576) ^ 2 := pow_le_pow_left₀ (sq_nonneg y) hy2hi 2
      _ = ((y2hi * y2hi : ℕ) : ℝ) / 1048576 / 1048576 := by push_cast; ring
      _ ≤ (y4hi : ℝ) / 1048576 := by gcongr; exact div_le_nat_ceilDiv (y2hi * y2hi) hS
  have hy5hi : y ^ 5 ≤ (y5hi : ℝ) / 1048576 := by
    have hy40 : 0 ≤ y ^ 4 := by positivity
    calc y ^ 5 = y ^ 4 * y := by ring
      _ ≤ ((y4hi : ℝ) / 1048576) * ((yhi : ℝ) / 1048576) :=
          mul_le_mul hy4hi hyhi hy0 (le_trans hy40 hy4hi)
      _ = ((y4hi * yhi : ℕ) : ℝ) / 1048576 / 1048576 := by push_cast; ring
      _ ≤ (y5hi : ℝ) / 1048576 := by gcongr; exact div_le_nat_ceilDiv (y4hi * yhi) hS
  have hs0 : InNatUnitIv
      (ylo - (5 + y3hi) / 6, capScale (yhi + (119 + y5hi) / 120 - y3lo / 6))
      (Real.sin y) := by
    refine ⟨capScale_le _, ?_, ?_⟩
    · have hsin0 : 0 ≤ Real.sin y :=
        Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith [Real.pi_pos])
      have hc6 : (y3hi : ℝ) / 6 ≤ (((5 + y3hi) / 6 : ℕ) : ℝ) :=
        div_le_nat_ceilDiv y3hi (by norm_num : 0 < 6)
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1048576)]
      refine nat_sub_le_of_nonneg _ _ (by positivity) ?_
      linarith [Real.sin_ge_sub_cube hy0]
    · refine le_capScale_div (Real.sin_le_one y) ?_
      have hc120 : (y5hi : ℝ) / 120 ≤ (((119 + y5hi) / 120 : ℕ) : ℝ) :=
        div_le_nat_ceilDiv y5hi (by norm_num : 0 < 120)
      have hf6 : ((y3lo / 6 : ℕ) : ℝ) ≤ (y3lo : ℝ) / 6 :=
        nat_div_le_div y3lo (by norm_num : 0 < 6)
      have hsub := sub_le_nat_sub (yhi + (119 + y5hi) / 120) (y3lo / 6)
      rw [Nat.cast_add] at hsub
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1048576)]
      linarith [sin_le_deg5 hy0]
  have hc0 : InNatUnitIv
      (1048576 - (1 + y2hi) / 2, capScale (1048576 + (23 + y4hi) / 24 - y2lo / 2))
      (Real.cos y) := by
    refine ⟨capScale_le _, ?_, ?_⟩
    · have hcos0 : 0 ≤ Real.cos y :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
      have hc2 : (y2hi : ℝ) / 2 ≤ (((1 + y2hi) / 2 : ℕ) : ℝ) :=
        div_le_nat_ceilDiv y2hi (by norm_num : 0 < 2)
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1048576)]
      refine nat_sub_le_of_nonneg _ _ (by positivity) ?_
      linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
    · refine le_capScale_div (Real.cos_le_one y) ?_
      have hc24 : (y4hi : ℝ) / 24 ≤ (((23 + y4hi) / 24 : ℕ) : ℝ) :=
        div_le_nat_ceilDiv y4hi (by norm_num : 0 < 24)
      have hf2 : ((y2lo / 2 : ℕ) : ℝ) ≤ (y2lo : ℝ) / 2 :=
        nat_div_le_div y2lo (by norm_num : 0 < 2)
      have hsub := sub_le_nat_sub (1048576 + (23 + y4hi) / 24) (y2lo / 2)
      rw [Nat.cast_add] at hsub
      push_cast at hsub
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1048576)]
      linarith [cos_le_deg4 hy0]
  simp only [baseSimpleNat, forceNat_eq]
  let sc0 : (ℕ × ℕ) × (ℕ × ℕ) :=
    ((ylo - (5 + y3hi) / 6, capScale (yhi + (119 + y5hi) / 120 - y3lo / 6)),
      (1048576 - (1 + y2hi) / 2, capScale (1048576 + (23 + y4hi) / 24 - y2lo / 2)))
  change InNatUnitIv (doubleAngleNat (doubleAngleNat sc0)).1 _ ∧
    InNatUnitIv (doubleAngleNat (doubleAngleNat sc0)).2 _
  have hd1 := doubleAngleNat_sound (sc := sc0) hy0 hy2_pi hs0 hc0
  generalize doubleAngleNat sc0 = sc1 at hd1 ⊢
  exact doubleAngleNat_sound (sc := sc1) (by linarith) hy4_pi hd1.1 hd1.2

/-- Signed unit-interval enclosure (`pos = true` for $y \ge 0$,
`pos = false` for $-y \ge 0$). -/
def InSignedNatIv (pos : Bool) (cAbs : ℕ × ℕ) (y : ℝ) : Prop :=
  if pos then InNatUnitIv cAbs y else InNatUnitIv cAbs (-y)

/-- Quarter-wave symmetry reduction of $(\sin(\pi k / 8192), \cos(\pi k / 8192))$
for $k < 8192$. -/
def sincosSignIv (k : ℕ) : (ℕ × ℕ) × Bool × (ℕ × ℕ) :=
  if Nat.ble k 4096 then
    if Nat.ble k 2048 then
      forcePairNatIv (baseSimpleNat k) fun s c ↦ (s, true, c)
    else
      forcePairNatIv (baseSimpleNat (4096 - k)) fun s c ↦ (c, true, s)
  else
    let k1 := 8192 - k
    if Nat.ble k1 2048 then
      forcePairNatIv (baseSimpleNat k1) fun s c ↦ (s, false, c)
    else
      forcePairNatIv (baseSimpleNat (4096 - k1)) fun s c ↦ (c, false, s)

lemma sincosSignIv_sound {k : ℕ} (hk : k < 8192) :
    InNatUnitIv (sincosSignIv k).1 (Real.sin (π * (k : ℝ) / 8192)) ∧
      InSignedNatIv (sincosSignIv k).2.1 (sincosSignIv k).2.2
        (Real.cos (π * (k : ℝ) / 8192)) := by
  by_cases h1 : k ≤ 4096
  · have hb1 : Nat.ble k 4096 = true := Nat.ble_eq.mpr h1
    by_cases h2 : k ≤ 2048
    · have hb2 : Nat.ble k 2048 = true := Nat.ble_eq.mpr h2
      have hb := baseSimpleNat_sound h2
      unfold sincosSignIv
      rw [hb1, hb2]
      generalize baseSimpleNat k = b at hb ⊢
      rcases b with ⟨s, c⟩
      simpa [InSignedNatIv] using hb
    · have hb2 : Nat.ble k 2048 = false := Bool.eq_false_iff.mpr fun h ↦ h2 (Nat.ble_eq.mp h)
      have hm : 4096 - k ≤ 2048 := by omega
      have hb := baseSimpleNat_sound hm
      have hang : π * (k : ℝ) / 8192 = π / 2 - π * ((4096 - k : ℕ) : ℝ) / 8192 := by
        rw [Nat.cast_sub h1]; push_cast; ring
      rw [hang, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      unfold sincosSignIv
      rw [hb1, hb2]
      generalize baseSimpleNat (4096 - k) = b at hb ⊢
      rcases b with ⟨s, c⟩
      simpa [InSignedNatIv] using ⟨hb.2, hb.1⟩
  · have hb1 : Nat.ble k 4096 = false := Bool.eq_false_iff.mpr fun h ↦ h1 (Nat.ble_eq.mp h)
    by_cases h3 : 8192 - k ≤ 2048
    · have hb3 : Nat.ble (8192 - k) 2048 = true := Nat.ble_eq.mpr h3
      have hb := baseSimpleNat_sound h3
      have hang : π * (k : ℝ) / 8192 = π - π * ((8192 - k : ℕ) : ℝ) / 8192 := by
        rw [Nat.cast_sub hk.le]; push_cast; ring
      rw [hang, Real.sin_pi_sub, Real.cos_pi_sub]
      unfold sincosSignIv
      rw [hb1]
      dsimp only
      rw [hb3]
      generalize baseSimpleNat (8192 - k) = b at hb ⊢
      rcases b with ⟨s, c⟩
      simpa [InSignedNatIv] using hb
    · have hb3 : Nat.ble (8192 - k) 2048 = false :=
        Bool.eq_false_iff.mpr fun h ↦ h3 (Nat.ble_eq.mp h)
      have hk1le : 8192 - k ≤ 4096 := by omega
      have hm : 4096 - (8192 - k) ≤ 2048 := by omega
      have hb := baseSimpleNat_sound hm
      have hang : π * (k : ℝ) / 8192 =
          π - (π / 2 - π * ((4096 - (8192 - k) : ℕ) : ℝ) / 8192) := by
        rw [Nat.cast_sub hk1le, Nat.cast_sub hk.le]; push_cast; ring
      rw [hang, Real.sin_pi_sub, Real.cos_pi_sub,
        Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      unfold sincosSignIv
      rw [hb1]
      dsimp only
      rw [hb3]
      generalize baseSimpleNat (4096 - (8192 - k)) = b at hb ⊢
      rcases b with ⟨s, c⟩
      simpa [InSignedNatIv] using ⟨hb.2, hb.1⟩

/-- Interval product enclosure for two `[0, 1]` `Nat × Nat` enclosures. -/
def mulUnitNat (a b : ℕ × ℕ) : ℕ × ℕ :=
  forceNat ((a.1 * b.1) / 1048576) fun nlo ↦
  forceNat ((1048575 + a.2 * b.2) / 1048576) fun nhi ↦
    (nlo, nhi)

lemma mulUnitNat_sound {a b : ℕ × ℕ} {x y : ℝ}
    (ha : InNatUnitIv a x) (hb : InNatUnitIv b y) : InNatUnitIv (mulUnitNat a b) (x * y) := by
  have hS : 0 < (1048576 : ℕ) := by norm_num
  simp only [mulUnitNat, forceNat_eq]
  refine ⟨?_, ?_, ?_⟩
  · have hprod : a.2 * b.2 ≤ 1048576 * 1048576 := Nat.mul_le_mul ha.1 hb.1
    omega
  · calc (((a.1 * b.1) / 1048576 : ℕ) : ℝ) / 1048576
        ≤ ((a.1 * b.1 : ℕ) : ℝ) / 1048576 / 1048576 := by
          gcongr; exact nat_div_le_div _ hS
      _ = ((a.1 : ℝ) / 1048576) * ((b.1 : ℝ) / 1048576) := by push_cast; ring
      _ ≤ x * y := mul_le_mul ha.2.1 hb.2.1 (by positivity) ha.nonneg_x
  · calc x * y ≤ ((a.2 : ℝ) / 1048576) * ((b.2 : ℝ) / 1048576) :=
          mul_le_mul ha.2.2 hb.2.2 hb.nonneg_x (by positivity)
      _ = ((a.2 * b.2 : ℕ) : ℝ) / 1048576 / 1048576 := by push_cast; ring
      _ ≤ (((1048575 + a.2 * b.2) / 1048576 : ℕ) : ℝ) / 1048576 := by
          gcongr; exact div_le_nat_ceilDiv (a.2 * b.2) hS

/-- Interval product enclosure for a `[0, 1]` `Nat × Nat` factor and a signed factor. -/
def mulUnitSignedNat (p : ℕ × ℕ) (pos : Bool) (cAbs : ℕ × ℕ) : ℤ × ℤ :=
  if pos then
    forceNat ((p.1 * cAbs.1) / 1048576) fun olo ↦
    forceNat ((1048575 + p.2 * cAbs.2) / 1048576) fun ohi ↦
      ((olo : ℤ), (ohi : ℤ))
  else
    forceNat ((1048575 + p.2 * cAbs.2) / 1048576) fun negLo ↦
    forceNat ((p.1 * cAbs.1) / 1048576) fun negHi ↦
      (-(negLo : ℤ), -(negHi : ℤ))

lemma mulUnitSignedNat_sound {p : ℕ × ℕ} {pos : Bool} {cAbs : ℕ × ℕ} {x y : ℝ}
    (hp : InNatUnitIv p x) (hc : InSignedNatIv pos cAbs y) :
    InIv (mulUnitSignedNat p pos cAbs) (x * y) := by
  cases pos
  · have hm := mulUnitNat_sound hp (by simpa [InSignedNatIv] using hc)
    simp only [mulUnitNat, forceNat_eq, InNatUnitIv] at hm
    simp only [mulUnitSignedNat, Bool.false_eq_true, ↓reduceIte, forceNat_eq, InIv, ivScale]
    rw [Int.cast_neg, Int.cast_neg, Int.cast_natCast, Int.cast_natCast]
    exact ⟨by linarith [hm.2.2], by linarith [hm.2.1]⟩
  · have hm := mulUnitNat_sound hp (by simpa [InSignedNatIv] using hc)
    simp only [mulUnitNat, forceNat_eq, InNatUnitIv] at hm
    simp only [mulUnitSignedNat, ↓reduceIte, forceNat_eq, InIv, ivScale]
    rw [Int.cast_natCast, Int.cast_natCast]
    exact ⟨by linarith [hm.2.1], by linarith [hm.2.2]⟩

/-- Recursive prefix-sine / cosine interval sweep for `givensLeaf 15`. -/
def givensLeafIvAux : List ℕ → (ℕ × ℕ) → List (ℤ × ℤ)
  | [], prod => forceNatIv prod fun plo phi ↦ [((plo : ℤ), (phi : ℤ))]
  | k :: ks, prod =>
      forceNatIv prod fun plo phi ↦
      match sincosSignIv k with
      | (sIv, pos, cAbs) =>
          mulUnitSignedNat (plo, phi) pos cAbs ::
            givensLeafIvAux ks (mulUnitNat (plo, phi) sIv)

/-- Certified integer interval enclosure of `givensLeaf 15` entries from `57` angle indices. -/
def givensLeafIv (ks : List ℕ) : List (ℤ × ℤ) :=
  givensLeafIvAux ks (1048576, 1048576)

private lemma givensLeafIvAux_sound (ks : List ℕ) :
    ∀ (prod : ℕ × ℕ) (P : ℝ),
      (∀ k ∈ ks, k < 8192) → InNatUnitIv prod P →
      (givensLeafIvAux ks prod).length = ks.length + 1 ∧
      ∀ i < ks.length + 1,
        InIv ((givensLeafIvAux ks prod).getD i (0, 0))
          (P * (∏ q ∈ Finset.range i, Real.sin (π * (ks.getD q 0 : ℝ) / 8192)) *
            if i = ks.length then 1 else Real.cos (π * (ks.getD i 0 : ℝ) / 8192)) := by
  induction ks with
  | nil =>
      intro prod P _ hP
      rcases prod with ⟨plo, phi⟩
      refine ⟨by simp [givensLeafIvAux], fun i hi ↦ ?_⟩
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp only [givensLeafIvAux, forceNatIv_eq, List.getD_cons_zero, Finset.range_zero,
        Finset.prod_empty, mul_one, List.length_nil, ↓reduceIte, InIv, ivScale]
      push_cast
      exact hP.2
  | cons k kt ih =>
      intro prod P hks hP
      rcases prod with ⟨plo, phi⟩
      have hk : k < 8192 := hks k List.mem_cons_self
      have hsc := sincosSignIv_sound hk
      generalize hsk : sincosSignIv k = sc at hsc
      rcases sc with ⟨sIv, pos, cAbs⟩
      have hprod' := mulUnitNat_sound hP hsc.1
      have hstep := ih (mulUnitNat (plo, phi) sIv)
        (P * Real.sin (π * (k : ℝ) / 8192))
        (fun x hx ↦ hks x (List.mem_cons_of_mem k hx)) hprod'
      have hhead : givensLeafIvAux (k :: kt) (plo, phi) =
          mulUnitSignedNat (plo, phi) pos cAbs ::
            givensLeafIvAux kt (mulUnitNat (plo, phi) sIv) := by
        simp only [givensLeafIvAux, forceNatIv_eq, hsk]
      refine ⟨by simp [hhead, hstep.1], fun i hi ↦ ?_⟩
      rw [hhead]
      cases i with
      | zero =>
          simpa using mulUnitSignedNat_sound hP hsc.2
      | succ j =>
          have hj : j < kt.length + 1 := Nat.lt_of_succ_lt_succ hi
          have hsub := hstep.2 j hj
          have hprod_eq : (∏ q ∈ Finset.range (j + 1),
              Real.sin (π * ((k :: kt).getD q 0 : ℝ) / 8192)) =
              Real.sin (π * (k : ℝ) / 8192) *
                ∏ q ∈ Finset.range j, Real.sin (π * (kt.getD q 0 : ℝ) / 8192) := by
            rw [Finset.prod_range_succ']
            simp [mul_comm]
          have hif_eq : (if j + 1 = (k :: kt).length then (1 : ℝ)
              else Real.cos (π * ((k :: kt).getD (j + 1) 0 : ℝ) / 8192)) =
              (if j = kt.length then 1 else Real.cos (π * (kt.getD j 0 : ℝ) / 8192)) := by
            simp [Nat.add_right_cancel_iff]
          rw [List.getD_cons_succ, hprod_eq, hif_eq, ← mul_assoc]
          exact hsub

theorem givensLeafIv_sound {N : ℕ} (row : Array ℕ)
    (hlen : row.size = N) (hrange : ∀ k ∈ row.toList, k < 8192) (p : Fin (N + 1)) :
    (givensLeafIv row.toList).length = N + 1 ∧
      InIv ((givensLeafIv row.toList).getD p.val (0, 0))
        (givensLeaf 15 (fun q : Fin (N + 1) ↦ (row.getD q.val 0 : ℤ)) p) := by
  have h1 : InNatUnitIv (1048576, 1048576) 1 := by
    refine ⟨le_rfl, ?_, ?_⟩ <;> norm_num
  have haux := givensLeafIvAux_sound row.toList (1048576, 1048576) 1 hrange h1
  have hrlen : row.toList.length = N := by simpa using hlen
  refine ⟨by simpa [givensLeafIv, hrlen] using haux.1, ?_⟩
  have hp : p.val < row.toList.length + 1 := by omega
  have hiv := haux.2 p.val hp
  rw [hrlen] at hiv
  have hangle : ∀ q : ℕ, 2 * (2 * π * ((row.getD q 0 : ℤ) : ℝ) / 2 ^ 15) =
      π * (row.toList.getD q 0 : ℝ) / 8192 := by
    intro q
    have hget : row.getD q 0 = row.toList.getD q 0 := by
      by_cases hq : q < row.size <;> simp [Array.getD, List.getD_eq_getElem?_getD, hq]
    rw [hget]
    push_cast
    ring
  have hmap : (Finset.univ.filter (· < p)).map Fin.valEmbedding = Finset.range p.val := by
    rw [Finset.filter_gt_eq_Iio, Fin.map_valEmbedding_Iio, Nat.Iio_eq_range]
  have hprod : (∏ q ∈ Finset.univ.filter (· < p),
      Real.sin (2 * (2 * π * ((row.getD q.val 0 : ℤ) : ℝ) / 2 ^ 15))) =
      ∏ q ∈ Finset.range p.val, Real.sin (π * (row.toList.getD q 0 : ℝ) / 8192) := by
    rw [← hmap, Finset.prod_map]
    refine Finset.prod_congr rfl fun q _ ↦ ?_
    exact congrArg Real.sin (hangle q.val)
  have hif : (if p.val + 1 = N + 1 then (1 : ℝ)
      else Real.cos (2 * (2 * π * ((row.getD p.val 0 : ℤ) : ℝ) / 2 ^ 15))) =
      (if p.val = N then 1
        else Real.cos (π * (row.toList.getD p.val 0 : ℝ) / 8192)) := by
    by_cases hpN : p.val = N
    · simp [hpN]
    · have hp1 : p.val + 1 ≠ N + 1 := by omega
      simp only [hp1, hpN, ↓reduceIte]
      exact congrArg Real.cos (hangle p.val)
  have hrhs : givensLeaf 15 (fun q : Fin (N + 1) ↦ (row.getD q.val 0 : ℤ)) p =
      1 * (∏ q ∈ Finset.range p.val, Real.sin (π * (row.toList.getD q 0 : ℝ) / 8192)) *
        if p.val = N then 1
        else Real.cos (π * (row.toList.getD p.val 0 : ℝ) / 8192) := by
    dsimp [givensLeaf]
    rw [one_mul, hprod, hif]
  rw [givensLeafIv, hrhs]
  exact hiv

/-! ### 5. Centered-Shift THC Algebraic Decomposition & Eigenvalue Bound -/

private def equivFin261 : Fin 9 × Fin 29 ≃ Fin 261 where
  toFun rb := ⟨29 * rb.1.val + rb.2.val, by omega⟩
  invFun μ := (⟨μ.val / 29, by omega⟩, ⟨μ.val % 29, by omega⟩)
  left_inv rb := by
    rcases rb with ⟨r, b⟩
    ext
    · simp; omega
    · simp
  right_inv μ := by
    ext; simp; omega

private lemma sum_fin261_eq {M : Type*} [AddCommMonoid M] (f : Fin 261 → M) :
    (∑ μ : Fin 261, f μ) = ∑ r : Fin 9, ∑ b : Fin 29, f (equivFin261 (r, b)) := by
  rw [← Equiv.sum_comp equivFin261, Fintype.sum_prod_type]

private lemma complete_square_op {d : ℕ} (w29 α : ℝ) (M : Operator d) :
    ((w29 - α : ℝ) : ℂ) • M + (2 : ℂ)⁻¹ • (M * M) =
      (w29 : ℂ) • M - ((α ^ 2 / 2 : ℝ) : ℂ) • 1 +
        (2 : ℂ)⁻¹ • (((α : ℂ) • (1 : Operator d) - M) * ((α : ℂ) • 1 - M)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
    sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  ring

theorem thcHamiltonian_dfthc_shape_quadForm_le {N L : ℕ}
    (thc : THCFactorization N 261)
    (t : Fin L → ℝ) (uOne : Fin L → Fin N → ℝ) (w : Fin 9 → Fin 14 → Fin 30 → ℝ)
    (hh1 : thc.h1eMod =
      (∑ ℓ : Fin L, t ℓ • Matrix.vecMulVec (uOne ℓ) (uOne ℓ)) +
        ∑ μ : Fin 261,
          (∑ r : Fin 9, ∑ c : Fin 14,
            (w r c 29 - ∑ b : Fin 29, w r c b.castSucc) *
              (if μ.val / 29 = r.val then w r c ⟨μ.val % 29, by omega⟩ else 0)) •
            Matrix.vecMulVec (thc.chi μ) (thc.chi μ))
    (hzeta : thc.zeta =
      ∑ r : Fin 9, ∑ c : Fin 14,
        Matrix.vecMulVec
          (fun μ : Fin 261 ↦ if μ.val / 29 = r.val then w r c ⟨μ.val % 29, by omega⟩ else 0)
          (fun μ : Fin 261 ↦ if μ.val / 29 = r.val then w r c ⟨μ.val % 29, by omega⟩ else 0))
    (ψ : Fin (2 ^ (2 * N)) → ℂ) :
    (star ψ ⬝ᵥ (thcHamiltonian thc *ᵥ ψ)).re ≤
      (star ψ ⬝ᵥ (oneBodyHamiltonian
        ((∑ ℓ : Fin L, t ℓ • Matrix.vecMulVec (uOne ℓ) (uOne ℓ)) +
          ∑ μ : Fin 261,
            (∑ c : Fin 14,
              w ⟨μ.val / 29, by omega⟩ c 29 *
                w ⟨μ.val / 29, by omega⟩ c ⟨μ.val % 29, by omega⟩) •
              Matrix.vecMulVec (thc.chi μ) (thc.chi μ)) *ᵥ ψ)).re +
      ((1 / 2 : ℝ) * ∑ r : Fin 9, ∑ c : Fin 14,
        ((∑ b : Fin 29, |w r c b.castSucc|) ^ 2 -
          (∑ b : Fin 29, w r c b.castSucc) ^ 2)) * vecNormSq ψ := by
  let nOp : Fin 261 → Operator (2 ^ (2 * N)) :=
    fun μ ↦ orbitalNumberOp N (thc.chi μ) 0 + orbitalNumberOp N (thc.chi μ) 1
  let fv : Fin 9 → Fin 14 → Fin 261 → ℝ :=
    fun r c μ ↦ if μ.val / 29 = r.val then w r c ⟨μ.val % 29, by omega⟩ else 0
  let Mop : Fin 9 → Fin 14 → Operator (2 ^ (2 * N)) :=
    fun r c ↦ ∑ μ : Fin 261, (fv r c μ : ℂ) • nOp μ
  have hnOp_eq : ∀ μ : Fin 261, oneBodyHamiltonian (Matrix.vecMulVec (thc.chi μ) (thc.chi μ)) =
      nOp μ := fun μ ↦ oneBodyHamiltonian_vecMulVec (thc.chi μ)
  have htwoBody_eq :
      (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin 261, ∑ ν : Fin 261,
        (thc.zeta μ ν : ℂ) •
          (orbitalNumberOp N (thc.chi μ) σ * orbitalNumberOp N (thc.chi ν) τ)) =
      ∑ r : Fin 9, ∑ c : Fin 14, Mop r c * Mop r c := by
    have hspin : (∑ σ : Fin 2, ∑ τ : Fin 2, ∑ μ : Fin 261, ∑ ν : Fin 261,
        (thc.zeta μ ν : ℂ) •
          (orbitalNumberOp N (thc.chi μ) σ * orbitalNumberOp N (thc.chi ν) τ)) =
        ∑ μ : Fin 261, ∑ ν : Fin 261, (thc.zeta μ ν : ℂ) • (nOp μ * nOp ν) := by
      rw [Fin.sum_univ_two]
      simp_rw [Fin.sum_univ_two, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ν _ ↦ ?_
      dsimp only [nOp]
      simp only [add_mul, mul_add, smul_add, add_assoc, add_left_comm]
    rw [hspin]
    have hzeta_apply : ∀ μ ν : Fin 261, (thc.zeta μ ν : ℂ) =
        ∑ r : Fin 9, ∑ c : Fin 14, (fv r c μ : ℂ) * (fv r c ν : ℂ) := by
      intro μ ν
      rw [hzeta]
      simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Complex.ofReal_sum, Complex.ofReal_mul]
      rfl
    simp_rw [hzeta_apply, Finset.sum_smul]
    have hswap1 : ∀ (f : Fin 261 → Fin 261 → Fin 9 → Fin 14 → Operator (2 ^ (2 * N))),
        (∑ μ, ∑ ν, ∑ r, ∑ c, f μ ν r c) = ∑ r, ∑ c, ∑ μ, ∑ ν, f μ ν r c := by
      intro f
      conv_lhs =>
        arg 2; ext μ; rw [Finset.sum_comm]
        arg 2; ext r; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [Finset.sum_comm]
    rw [hswap1]
    refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    dsimp only [Mop]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ ↦ ?_
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  have hh1_split : oneBodyHamiltonian thc.h1eMod =
      oneBodyHamiltonian (∑ ℓ : Fin L, t ℓ • Matrix.vecMulVec (uOne ℓ) (uOne ℓ)) +
        ∑ r : Fin 9, ∑ c : Fin 14,
          ((w r c 29 - ∑ b : Fin 29, w r c b.castSucc : ℝ) : ℂ) • Mop r c := by
    rw [hh1, oneBodyHamiltonian_add]
    congr 1
    rw [oneBodyHamiltonian_sum]
    simp_rw [oneBodyHamiltonian_smul, hnOp_eq, Complex.ofReal_sum, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    dsimp only [Mop, fv]
    simp_rw [Finset.smul_sum, smul_smul, Complex.ofReal_mul]
  have hw29_sum : (∑ r : Fin 9, ∑ c : Fin 14, (w r c 29 : ℂ) • Mop r c) =
      oneBodyHamiltonian (∑ μ : Fin 261,
        (∑ c : Fin 14,
          w ⟨μ.val / 29, by omega⟩ c 29 *
            w ⟨μ.val / 29, by omega⟩ c ⟨μ.val % 29, by omega⟩) •
          Matrix.vecMulVec (thc.chi μ) (thc.chi μ)) := by
    rw [oneBodyHamiltonian_sum]
    simp_rw [oneBodyHamiltonian_smul, hnOp_eq]
    dsimp only [Mop, fv]
    simp_rw [Finset.smul_sum]
    have hswap2 : ∀ (g : Fin 9 → Fin 14 → Fin 261 → Operator (2 ^ (2 * N))),
        (∑ r, ∑ c, ∑ μ, g r c μ) = ∑ μ, ∑ c, ∑ r, g r c μ := by
      intro g
      conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ _ ↦ ?_
      rw [Finset.sum_comm]
    rw [hswap2]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    rw [Complex.ofReal_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    let r₀ : Fin 9 := ⟨μ.val / 29, by omega⟩
    rw [Finset.sum_eq_single r₀]
    · have hr₀ : μ.val / 29 = r₀.val := rfl
      simp only [hr₀, ↓reduceIte, smul_smul, Complex.ofReal_mul]
    · intro r _ hne
      have hval : μ.val / 29 ≠ r.val := fun h ↦ hne (Fin.ext h.symm)
      simp only [hval, ↓reduceIte, Complex.ofReal_zero, zero_smul, smul_zero]
    · intro hr₀; exact (hr₀ (Finset.mem_univ r₀)).elim
  have hMop_b : ∀ (r : Fin 9) (c : Fin 14),
      Mop r c = ∑ b : Fin 29, (w r c b.castSucc : ℂ) • nOp (equivFin261 (r, b)) := by
    intro r c
    dsimp only [Mop]
    rw [sum_fin261_eq, Finset.sum_eq_single r]
    · refine Finset.sum_congr rfl fun b _ ↦ ?_
      have hdiv : (equivFin261 (r, b)).val / 29 = r.val := by dsimp [equivFin261]; omega
      have hmod : (⟨(equivFin261 (r, b)).val % 29, by omega⟩ : Fin 30) = b.castSucc := by
        ext; dsimp [equivFin261]; omega
      simp only [fv, hdiv, hmod, ↓reduceIte]
    · intro r' _ hne
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      have hdiv : (equivFin261 (r', b)).val / 29 ≠ r.val := by
        have : r'.val ≠ r.val := fun h ↦ hne (Fin.ext h)
        dsimp [equivFin261]; omega
      simp only [fv, hdiv, ↓reduceIte, Complex.ofReal_zero, zero_smul]
    · intro hr; exact (hr (Finset.mem_univ r)).elim
  have hY_bound : ∀ (r : Fin 9) (c : Fin 14),
      let α := ∑ b : Fin 29, w r c b.castSucc
      let Y := (α : ℂ) • (1 : Operator (2 ^ (2 * N))) - Mop r c
      (star ψ ⬝ᵥ ((Y * Y) *ᵥ ψ)).re ≤
        (∑ b : Fin 29, |w r c b.castSucc|) ^ 2 * vecNormSq ψ := by
    intro r c α Y
    have hY_eq : Y = ∑ x : Fin 29 × Fin 2,
        (w r c x.1.castSucc / 2 : ℂ) •
          orbitalReflection N (thc.chi (equivFin261 (r, x.1))) x.2 := by
      have hα_cast : (α : ℂ) = ∑ b : Fin 29, (w r c b.castSucc : ℂ) := by
        dsimp only [α]; push_cast; rfl
      change (α : ℂ) • (1 : Operator (2 ^ (2 * N))) - Mop r c = _
      rw [hα_cast, hMop_b, Finset.sum_smul, ← Finset.sum_sub_distrib, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [Fin.sum_univ_two]
      dsimp only [nOp, orbitalReflection]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hY_herm : Yᴴ = Y := by
      rw [hY_eq, Matrix.conjTranspose_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Matrix.conjTranspose_smul, orbitalReflection_conjTranspose]
      have hc : star (w r c x.1.castSucc / 2 : ℂ) = (w r c x.1.castSucc / 2 : ℂ) := by
        rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_div, RCLike.star_def, Complex.conj_ofReal]
      rw [hc]
    have hYY_mul : Y * Y = Yᴴ * Y := by rw [hY_herm]
    have hYY : (star ψ ⬝ᵥ ((Y * Y) *ᵥ ψ)).re = vecNormSq (Y *ᵥ ψ) := by
      rw [hYY_mul, re_quadForm_conjTranspose_mul_self]
    rw [hYY, hY_eq, Matrix.sum_mulVec]
    have hcast : ∀ x : Fin 29 × Fin 2,
        (w r c x.1.castSucc / 2 : ℂ) •
          (orbitalReflection N (thc.chi (equivFin261 (r, x.1))) x.2 *ᵥ ψ) =
        (((w r c x.1.castSucc / 2 : ℝ) : ℂ)) •
          (orbitalReflection N (thc.chi (equivFin261 (r, x.1))) x.2 *ᵥ ψ) := by
      intro x
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    simp_rw [Matrix.smul_mulVec, hcast]
    have hunit : ∀ x ∈ (Finset.univ : Finset (Fin 29 × Fin 2)),
        vecNormSq (orbitalReflection N (thc.chi (equivFin261 (r, x.1))) x.2 *ᵥ ψ) ≤
          vecNormSq ψ := by
      intro x _
      let R := orbitalReflection N (thc.chi (equivFin261 (r, x.1))) x.2
      have hRR : Rᴴ * R = 1 := by
        rw [orbitalReflection_conjTranspose]
        exact orbitalReflection_mul_self N (thc.chi_norm _) x.2
      rw [← re_quadForm_conjTranspose_mul_self R ψ, hRR, Matrix.one_mulVec,
        re_star_dotProduct_self]
    have hbnd := vecNormSq_sum_smul_le Finset.univ
      (fun x : Fin 29 × Fin 2 ↦ w r c x.1.castSucc / 2)
      (fun x ↦ orbitalReflection N (thc.chi (equivFin261 (r, x.1))) x.2 *ᵥ ψ)
      (vecNormSq_nonneg ψ) hunit
    have hsum_abs :
        (∑ x : Fin 29 × Fin 2, |w r c x.1.castSucc / 2|) =
          ∑ b : Fin 29, |w r c b.castSucc| := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [Fin.sum_univ_two, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    rwa [hsum_abs] at hbnd
  have hfull : thcHamiltonian thc =
      oneBodyHamiltonian
        ((∑ ℓ : Fin L, t ℓ • Matrix.vecMulVec (uOne ℓ) (uOne ℓ)) +
          ∑ μ : Fin 261,
            (∑ c : Fin 14,
              w ⟨μ.val / 29, by omega⟩ c 29 *
                w ⟨μ.val / 29, by omega⟩ c ⟨μ.val % 29, by omega⟩) •
              Matrix.vecMulVec (thc.chi μ) (thc.chi μ)) +
      ∑ r : Fin 9, ∑ c : Fin 14,
        (-(((∑ b : Fin 29, w r c b.castSucc) ^ 2 / 2 : ℝ) : ℂ) •
            (1 : Operator (2 ^ (2 * N))) +
          (2 : ℂ)⁻¹ •
            ((((∑ b : Fin 29, w r c b.castSucc : ℝ) : ℂ) • 1 - Mop r c) *
              (((∑ b : Fin 29, w r c b.castSucc : ℝ) : ℂ) • 1 - Mop r c))) := by
    rw [thcHamiltonian, hh1_split, htwoBody_eq, Finset.smul_sum]
    simp_rw [Finset.smul_sum]
    rw [add_assoc, ← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, complete_square_op]
    simp_rw [sub_eq_add_neg (_ • Mop _ _), neg_smul, add_assoc, Finset.sum_add_distrib]
    rw [← add_assoc, hw29_sum, ← oneBodyHamiltonian_add]
  rw [hfull, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  suffices hrem : (star ψ ⬝ᵥ ((∑ r : Fin 9, ∑ c : Fin 14,
      (-(((∑ b : Fin 29, w r c b.castSucc) ^ 2 / 2 : ℝ) : ℂ) •
          (1 : Operator (2 ^ (2 * N))) +
        (2 : ℂ)⁻¹ •
          ((((∑ b : Fin 29, w r c b.castSucc : ℝ) : ℂ) • 1 - Mop r c) *
            (((∑ b : Fin 29, w r c b.castSucc : ℝ) : ℂ) • 1 - Mop r c)))) *ᵥ ψ)).re ≤
      ((1 / 2 : ℝ) * ∑ r : Fin 9, ∑ c : Fin 14,
        ((∑ b : Fin 29, |w r c b.castSucc|) ^ 2 -
          (∑ b : Fin 29, w r c b.castSucc) ^ 2)) * vecNormSq ψ by
    linarith
  have hrhs_sum : ((1 / 2 : ℝ) * ∑ r : Fin 9, ∑ c : Fin 14,
        ((∑ b : Fin 29, |w r c b.castSucc|) ^ 2 -
          (∑ b : Fin 29, w r c b.castSucc) ^ 2)) * vecNormSq ψ =
      ∑ r : Fin 9, ∑ c : Fin 14,
        (1 / 2 : ℝ) *
          (((∑ b : Fin 29, |w r c b.castSucc|) ^ 2 -
            (∑ b : Fin 29, w r c b.castSucc) ^ 2) * vecNormSq ψ) := by
    generalize vecNormSq ψ = Nψ
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [hrhs_sum]
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun r _ ↦ Finset.sum_le_sum fun c _ ↦ ?_
  have hb := hY_bound r c
  have h2inv : ((2 : ℂ)⁻¹ : ℂ) = (((1 / 2 : ℝ) : ℂ)) := by norm_num
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, h2inv,
    Complex.add_re, Complex.neg_re, Complex.neg_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero,
    re_star_dotProduct_self]
  linarith

theorem eigenvalue_le_of_quadForm_re_le {d : ℕ} {H : Operator d} {B : ℝ}
    (hquad : ∀ ψ : Fin d → ℂ, (star ψ ⬝ᵥ (H *ᵥ ψ)).re ≤ B * vecNormSq ψ)
    {E : ℝ} {ψ : Fin d → ℂ} (heig : H *ᵥ ψ = (E : ℂ) • ψ) (hψ : ψ ≠ 0) :
    E ≤ B := by
  have hq := hquad ψ
  rw [heig, dotProduct_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    re_star_dotProduct_self] at hq
  exact le_of_mul_le_mul_right hq (vecNormSq_pos_of_ne_zero hψ)

/-! ### 6. `P450.dfthc` Integer Certificate & Main Eigenvalue Bounds -/

/-- Unpacks a `58`-entry witness column from four radix-`262144` `Nat` words (`15+15+15+13`
lanes, offset `+ 131072`) without typeclass subtraction overhead. -/
def decodeWitCol : List ℕ → List ℤ
  | [w0, w1, w2, w3] =>
      (unpackBase 262144 15 w0 ++ unpackBase 262144 15 w1 ++
        unpackBase 262144 15 w2 ++ unpackBase 262144 13 w3).map
          fun u ↦ Int.subNatNat u 131072
  | _ => []

/-- Packed radix-`262144` unsigned witness words (`+ 131072`) for the `22` positive columns. -/
def lPosRaw : List (List ℕ) := [
  [0x2003c8056a00d380139ff687fea200008082dfed0809bdffee80036001e8015dffc3,
   0x1fe3c7ff520072801bdffad8015200027ffa20077804bdffab7fc2dfff97fc6dfe71,
   0x1ff8e7fe82040483bf9e18580cb1f8ac76d59ec547e366c10f7fd1e00d47fbd5fdf4,
   0x200317ee11fe3a7f665fd538070a012e7fac5fe5e80a92012c7ff1601c7],
  [0x1fffa7fd81ff217fc2dfefb7faee00ac807d5ff3580111faab806e1ffb87fe4dffb4,
   0x1ff5680152008b800ea00557fff9ffdf800be00677fe3a003b800d2007e7ff2a002a,
   0x20099801aa00ac84809f7fc82e1df5f07f83211cdcdab609b280071ffba80232000b,
   0x1fdb88055601a68074a008980f06038680611ffc080251ffcf8002e00cd],
  [0x200508095dfdf17fe46011a8006a012a804d6002a7ff5600a6802d9fd2f7ffd5fdbb,
   0x1fe6380039ffdf8024dffd9800020086800a5ffdf7fe86001d7fb0dfce5802e2017a,
   0x202be806bdfe2f8b7b62afa81321fb4679492c7267c7b2119c80461ffa8808e2030c,
   0x200d07fde603297eb9a00c7804d2085c7e24602cd80041fc7d80ed1fff2],
  [0x2004a7fc4200877ff3a008c7ffa600418044600ae7ea4e00c8801ae00668007dffcc,
   0x207a67ffd2013d80011ff267ffe1ffde8020e00b27ff29feb480779ffed802ea000d,
   0x2023f808d5fece8e0d9b96f80995fc26b62ee1c4e7e5da1beb8015dff9a804cdff92,
   0x1f7957da65fea07fe41fb078319e00187f641ff427f609ff067fa61fe00],
  [0x200187fbe6002e800edffd77f672003b7f57600b07f6ee00397ffe2006e7fd12007a,
   0x202ef804b5fed5804e600137ff21ffe97fdc9ffc0801b9ffa2801da0072800fa0010,
   0x2007880169ff8f9a07edaf080dd5fee28c769bbe980a5e1d097ff75fffe7f27dfb07,
   0x205e7808ee0cf47c96e056e7fe7613248101200537fd5200807fd69ff6b],
  [0x1fffa7fff9ffb5800d5fff28038dff91805ea01cf8112a006e7fafa0013802da0042,
   0x1fb727ffd60164800fdfece8015dffeb7ff5a00858043dfff57fc9e001c7ff0e002d,
   0x1ffc87ff11fff6b7cd1a1d17fa86021b6c425d9547cf19cbac7ff75ffe27f9c203ae,
   0x1f62e7c44201657d689f97f849420c3381a4600358033e0043801e6004f],
  [0x1ff517c1a5fef781755f90d80095ffde7fefe002e80045ffd87fe25ffe87ffe200b9,
   0x200027ffedfec280055ff8980019ffec800ba0002800ce01a181c0a0c358252201df,
   0x1a3d6815a6281480282007e7fc120124802de027b80051ff727e0321ef58054e0010,
   0x206447e6920028807f9ffff80659ffd27f932005875d2e27d082f3a16cf],
  [0x200477fc5e06b4803a6060e8018dfff980069ffe780192002d8002dfc9980022035a,
   0x2007f7fe4600178003e00057ff0dffff7ffde0000800d5f6a5803f1ff45806160063,
   0x2052990dcdfbc97ffd6007a7fa12014f7fc42004e80009ff9a81711fe2b80071fe9e,
   0x1ffb3801a9fcfb7fd31ffd280272000f7fc91bedb7efa603447e84a091d],
  [0x1ffbd7e5e9fc6d816b2006c7ffae00127fff600647fdde00197ff5dfe9b8004a019e,
   0x200147fff1ffeb8001200078001dfff780021ffb480056032683679fdf0843ae0892,
   0x2126f7c9dde7888002600097fffa00077fed2007d7ff660059831a9f94b8022a00e6,
   0x200378033e00157fffa0020809fdff6a7fe4205067c43219c576f8a400c],
  [0x1ff3d8364600627ff25f8577fefe00267ff62004c7fb62001d80101fdf97ffc601c3,
   0x1ff2d7fffe00137ff8a0005800ae00267ffa9ffd97fee201c07dc5e06c67f206017b,
   0x1e0267d2a5f0ea7ffe2006b804b9ff53802be004c7ffb1ffb77fbc9f77e7fe7a00ec,
   0x1ff537f951ff89800c1fcfc80251ffde803c9f1d486be9e7337d56e0fd5],
  [0x1fffd7f74e00617eaf600647ff95fec77fcadff6880101ffe87fff1ffe37ffe9fff3,
   0x200677ff8dfd7a80021f8767ff5a0049803de01837fffdffdd80db2012480019ff3d,
   0x202517fca5b84b7ee1e01907f586020b7fee5fd868033600777fea1fc737fe4dffac,
   0x20c137287dff187f1fe01a883e0a019a7f42dfef77d2fe02a49d59e21cb],
  [0x1ffda7e3bdffa07b335fe0c80121ffa27ffddffad8050dff807fcb9ffbd7ffa9ff7a,
   0x2010b7ff71fe817ff85ffec80022002a80075ffdb8000e00738118a03107bab600d2,
   0x1e30780741a68f802d5ff4f7fd6e00cc7fa3600c38017e022f7fe660e907fdc60096,
   0x207207fb4dff38806b9ff757eca20070801ea027a793061f7d75c1dc295],
  [0x200f081fa9ffdc7f4ea02487ff75fffc7ff79ffe67ff16002480189ffac80025ffb9,
   0x1ffa08003dff427fd25ffb07fff600508007e00eb7ff9dff6781fb1f7f78034200ff,
   0x203a68151a01d07ffd200d9800e1ffb08074201b77ff61fe187ee1a24a07ff3e005f,
   0x203037f88e0058800fe004f81cd5fc577ff4e009f9ee3e696582a15fc42],
  [0x1ff8780525fdf08018600027ffa200067ff9600077fece00077ffd6016f80005fe88,
   0x1ffda80015ffff8000e00058002200047fff1fffe80011fff980706024c80f8201b9,
   0x1fcac82cf9feb97ff9dffed7ff1600117ffc9ffb98000e002880e6dfa447ff4a00aa,
   0x1ffe87ff76002d7ff6e00148003e00027ff860b7780ad9fe727fdea0019],
  [0x1ffec7feadffa07fea201138025e009c80089ffde7ff6a00077f2f1fffd80055ffae,
   0x200287f9c2013780229ff3b7feb5fff67fd1e005b7db49ffbc801cdffd87ff3e0067,
   0x1ffe9804fe00ed7f40200a67ec7204978038205157fe8201c88021200fc80086004e,
   0x1fab47e959f4307e016010280a9e02899e54600c77fa9e014b80132009b],
  [0x1ffeb8003200337fe1a0007802e9ffb5803b5fc798003e0013800ea00168009e0021,
   0x1ffc87fd6e003d860b201267ff61ffd680271ff248001e0017802e1fff780129ffd4,
   0x1ff557ff2dfff37c871f80082a01f8d180141fda27f789fe157ffa200317ff2e0011,
   0x1ff69829a1fbaf82aa6014485d22a7d17f481ffe8807da02397fee9fff9],
  [0x1ffee7ff5600637fa35ffe47fd35ffe87fc89fc8280141ffc78005a003280075fff6,
   0x1ffd580155fe8a7e4f201e97ff0e00378004e14ae80049ffff7fe7e00417ff49fe55,
   0x1ff1f7fe2203217dd82070681a95fb927efcdffe27fa11ffe67fc21fe4b7fe31ff4a,
   0x2064c83e0a0192816f60650a870de8557faf200217ec21fb0c7d58df60e],
  [0x1fff0802d600e4800a9ffbe7ff56002980232005b7ffb2001280011ffce8027e0040,
   0x1fff47fb19ff7c7feaa00597e98e00127ff2dff7c800a5ffd77fdce004b7ff6a0009,
   0x1fe367fe11ff1880651fd7d817a5f918801e1ffb67fd92001a7fe2dff96800260120,
   0x2021580405fb6b7fca6446f7f3bdff277ff05ff3680545febd7fd9600dd],
  [0x2002c8013dffde8018a004b7fc91ffc08014600aa7ffaa00317fdfdfff67fea20031,
   0x2000f808f6020a7fb39fba580095ff9083d09ff797feee00907fefdffb58009a002a,
   0x202c4809b600b481c4604b882821f9167fb6e00567f8d601307ff31ff8f7ffe9fff1,
   0x1f6d87bec61389a1ed201df7ee55f9b782ad9ffb28019dff257fcb2004a],
  [0x1ffe98003200398005a00437fc16003a801cdffd28000a00157fed5ffc77ff720025,
   0x2002883755ff21803260039806ba001d7f7e1ffc67fc95ffbe8002600307ffc9fff1,
   0x1ff8a80611ff527ef61f9c681229f8f57ff9a00107fc89ffe08020dffe38001a012c,
   0x203d67fdf26c2e7be5606097fd7602cb827f9fc5e7fefe00177fe96000d],
  [0x1ffac7fb79fffe7f8f5fe328014a02bf808b601197ff5dffef7fdd5ffef800620029,
   0x2003e8015206107fada12f380189ff4d7f79dfeae8004e00678064dff94800f6000d,
   0x1f668801d9e3c2821adfbb982275f9db806a1ff0f7f89602807fc22002c801ae0059,
   0x1e2e3a20aa0271833d1fcbd7dcddf7cf81d41ffa57ee1605508be920e44],
  [0x1ffe8805bdffd480385ffd47fffa00507e82dfffa7fe9a002c7fefe000780071fffc,
   0x2008f7feb5e349800a203d18010e03ae8026dfee17fe4600157fd49ffb4801fa000f,
   0x2048d80082031981b15f9577f27e038880b86008d8023dfff88014dfc8b7fe720081,
   0x2813886a3dfd02830edfb537e49dffc781f69ff9580c45fa5c8065602f5]
]

/-- Packed radix-`262144` unsigned witness words (`+ 131072`) for the `36` negative columns. -/
def lNegRaw : List (List ℕ) := [
  [0x220957faee28f984331e67c7fe85fdcc80111fc9280215ff907c625b22b8028e55bb,
   0x2043680319ffe780621ffb080261fff17ff2e00fb857c216927f7be013c7f559be70,
   0x1ffed82675fe5f7fffe002f7e031f808800be0081800f1ff8a8a552072b8071e0320,
   0x2000e7ffd5ffbf7ffb1ff567ff61ffed806ca144880495ff38800cdff27],
  [0x1f9a383ac604447ec9debfe81539fcc0813de03c880d0e094288a1dda5ea905dd6af,
   0x1f5ca8131dfa0389761edb381a6a070283c8dd981884f9fc018038dfe778006600f1,
   0x20299805be011b7ff06014c7fac5fdf680269fe72800d5ff887fb4a00f18a455fd3b,
   0x1fec480a01ff9d7f9d5ff1a81679f99780d7600e47efb202da80105ffb3],
  [0x205c67fad61a457f48a1f457d38e1ec980116617685d5e04fc89d52469886e863bd6,
   0x1bb1681a8e00d87411a059380ae5fed3838e9e5a18e58a0657800a6032e8017e054a,
   0x1fc527f5e1ff4c7f69e005479cc9ebdf80bd602c280211ffbf7ff8dfd79707a5f91b,
   0x200837fd99ff4c7fbbdff25812ae0881814f20112800fa00487fe16000e],
  [0x20b818033a0d697c18214197f83e0362805d9fdb7805320094878e9cee67fba63075,
   0x203a6801ea00148029600cc8002e002880296008079e99a2df7fdbe0bb0807123c18,
   0x1ff257ed66017a80061ffa27e90dfee67fd49ffaa8002e004677e2df72e7ff75f552,
   0x1fff18025e00968031dffd9800d6000b7faae0e8a800960071800160094],
  [0x1ffd97edf9fb797f0adfc917e18e006d81f21cdbd7fe3ef6a37ddde00517cec600fa,
   0x200f081b4606f2714660a2c7e826064382ed5c2807fd75fea97fbc9ff00800bdfe57,
   0x1ffdf7ff1e00147fce1ffe77f8b201867fdb1ff7b810ae000f80015ffd181231ff2d,
   0x201337fc71ff3a7fb0dffa68169e066b7fee5fff6800d1ffd57ffb9ff9b],
  [0x1ff5887639e6cb83ea9e95e82c62083e8465201c8b0afe001580d2de39c7ed69e777,
   0x237a97f1e605767fa15fd9b80476025182275fdb37fac5fbd980d91ffb980221fe5b,
   0x201808013e010e7fa4600fc801a200628109a00d580011fe8d8061e005b70a5a012c,
   0x201c98022a00567fcd200688008200068007dfe5a7ed3603e5802fdffa7],
  [0x1f7d8858820bc37d2b9e8667e9fe10b4827ae0395828bdfd4b94a65cb566c521c37d,
   0x1cfb57f98a05aa7ace20b797f4e9ff947fa82102b98291fd9780c4dfe437fcb60250,
   0x203a68086202037feba000f808720460808edfe087fce5ff3c80006013b8f8e1f517,
   0x202447f6ee007d7ffda00687f79203a9825ee01b87e76a043b8018a012c],
  [0x1ffcb76c1df8bb7ffa9ff04689820ba0acc59fa967d609f40b7c549fb8a817c9fb5a,
   0x1fbcd8d2c241778191604597ccaa3b5382f4e0ca27ef9200477f731ff968000dffc1,
   0x1fe9d80131fea87ff3601297d75a051980129ff4c7fbb9fe798010dfec47dffe008f,
   0x2149b7fe89f89d7fee1ff1e7fcc1ff797fcd5ff2782151f97b7fd920071],
  [0x1fe198646d58a77dd25f1bf80eee3c0c7e729ed59761d5fdd486489ea6a84b3e2869,
   0x1fdde7f391fded7ba62119c7f7d9fe3b85932202a85f89eea08040e008e7fc91e005,
   0x204897f58604d17fe21fece8333e0a027fe99fed77fd3a000c8272202be767a20348,
   0x1ff397f2b600247f576016b7ec2a02d680799f0037df12069080f0dfb5b],
  [0x1ffec797720d6280725fc38abc9dfb8596522049a78ad2041683c65fb8e7f7d5f91a,
   0x202b16c27e1d2c7bbe9e6ff8770e1c2383ee608fb8176201317f705feab8019602b7,
   0x1fecf80369feb87feea018d80ca206367ffe1ff52801ca00137fbc1ff3977c4a03dd,
   0x209e580cda0b657fa9e01a27fe4a017f800fe026181841fb3e7fc8e00fc],
  [0x231497fa8df489868fa73ce80b222d738016a32b97c48200da7e2e9db167f9cdde80,
   0x2557c7ffca00497a6f60cba80469fef9843f9f2038317a1afc804de11d47fb9dffa4,
   0x1f2e47d941fc657fefdff9f7ba41f0f07f081fe5280302008d8147df97688f0dff17,
   0x200107fa4dff8b7fb2dffae80cfa04707fe85fbda813e5fd0a80075fc11],
  [0x1f24f7f4f5f82d9dffdff5a811f207497fa15d0137f34e00637f4aa0a137fae60466,
   0x1edce7f309fe7a85bae03f6804e1fe9580e960aac85e79f94184f7dfd737bb0e1f35,
   0x1ff207f909f2a48018e00ea71ca9b81f8013e0005800a1fe2e7dbae07957f705fe3b,
   0x1ffd67feb9fe2c80259fdb17fd75fc9d80915fd1b80941fb7180561f233],
  [0x1fe99777aa3fc07e1c9f58482f2693747b9fdc80885a49fcb07929a15ad860220060,
   0x1efeb80c3dfd7e7e69e2a1a817f1fe768eaa633767dbaa04017f4b5fdcd7fd920c56,
   0x1ff9780d05fe3780069ffc98859e1ba7803adffde7fdcdfff47f129ff12854c600a7,
   0x1ff547e0c600077e5b5ff9c7e01200d17f8d6072881f85f9eb7f81a0437],
  [0x20247ae76630c8814ea0768801e2124187bfdf6be768a2032678ffe049c80c69f664,
   0x2004380aaa05af7eaf20a1e8052e02b280e6a0ee17cc8603d18457e07ec8016207ec,
   0x2078f7f65607b580089fff780a9e05a17fec9ff0f8033dfedf7f91206707776e018b,
   0x2028e7f981ffb27ff31ff8e7f7d600ce7f71602ab7579e1f8780ee1fd75],
  [0x28de780269f61f813b1ccab7fa1a00e480135feaa7f69a00548640616b77fdc1ef2c,
   0x1f4037fee5fff8802ea00287fee5ffcb7ff160058797c20fb280f6606277fade12ed,
   0x2070781941ff7780031fff57f141f88a80031ffbd7fe05ff967c53e013880519fc9e,
   0x2001980005ffda7fea1fff580021ffe07fd25fc507f89e006e80041ff42],
  [0x1f4a380aa9f50c7c091fb457ff41ff598007601c58025a00177ee8de178800a21d91,
   0x200247ff51fff67fd8e000a80001ffee7ff79ff5f8098e4d467e681d3cd7f22e45b8,
   0x1fe2282b3a04d17fe81ffd280851fd3280259fe8b7ff62008078ca1f27e800ea069e,
   0x2002a7fb79ffb27fbb5ff9380189ffec80075feb47f37e028e80d15fc46],
  [0x20011805b600a7815be02967f915ff2780d0601fb7ffda006980c6dff827ffd2013d,
   0x1ff827fd49ff627f68dfec78027dfff97fafdfeff7f93dfea57d535fc998837202a8,
   0x200f97fdcdfbeb7fc49ffd68b249dd2f7fd69fe237f6b5fd8c80ea60f2680215fed9,
   0x202ea7f181fb347ec91f81a7f595fcdf80a5dfe6b7fdfdfb5080111f9fe],
  [0x1fa6e7fa65ff4784449f7848000e0075800c9ff567fda5ffde8042e007c7fe0e0040,
   0x1fe2d80009ffcb8011200057ff95ffe680049ffff7fafe084268d2e2d9b7f45e08ae,
   0x208ce7f3ca029480029fffb7f71a01c68031200e180035fff681cf9dba780319faca,
   0x1ffcd801c6001f800c2007b801ba004480051fd227d59223fd80af9fc2f],
  [0x1f5f97f299ff947f4d5fb647ffadff637ffca002b802be004f7fcb5f9907fffa06b0,
   0x1ff417fff5ffdf7fec1ff8a800b600157ff720026803f215808610e3dc7825e1f3eb,
   0x20e3381885fd128005a00228119dfc1d7fec600ea7fe19ffd3729a204527ff9603a2,
   0x1ffed801b9ff877fc71fef57fcf1ffab80291ffa880a99fc2e7f2f201b2],
  [0x1e4f480fe208da83fba0f067ec6a0be380a55f9f88000602eb98831fcac7fc520529,
   0x1fb5280262003b8091602807fc86005180892015e6a63a263c81be9ffbb7eec9e8e4,
   0x1fd6180465fe4480495ff757dc5a00c37feb5ffb57fed60014852f6055b7fc71ea87,
   0x1fff18021e006b803b201537ff99ffe87ef79fffd7ffbdfeb180181fe2c],
  [0x1f91d7e11223ab7ec59dc0f7b869fc8e7eff9df9f7740e00a19116a353080536178d,
   0x2826681b41feb88470200d37f415ff147f8b203879169a01ca7f765fbde8097a0be4,
   0x202ea80e79ffbb803cdfe4e826660c6c7e6ea02cc7fefdff997e3b2028676131f29c,
   0x1feab7fdedff777feb600257fc45fd2081d0a037080681fe697fb560259],
  [0x1ffc77f9edfea280741ff7c804bdfcc87f9d2721980b6662f8804f202067e6be02b4,
   0x201307e8d5f963a598a00477f8ae01f3800229cc4808d1ff247fc21ff6c800fe003f,
   0x1ffea7ffadfef7801a2001f80881ff457fe15fff3807b600317ff7a009b807f5ff9b,
   0x1fedc7ffc200627ff9a00007c96def4e7ffd600048009dffce80089ffdb],
  [0x1ff9f80141fff98027a000980de186687f2b205c07f899f2bf814a1fe687f881fe81,
   0x1ff727fae5ff94802d6a38e82831f8a8aef9e00b37f291ff9b7ff86009b8007dffd5,
   0x200697ff4a00137fbc6001f80e85ffe87ff8200517ff5dffea801e2000e7fd560088,
   0x1ffa97c05a00567b68a009e7ffb9ffe280359ffd5800220004800260004],
  [0x200208313600b28013a008281eb1fb825ffea04248033dfb9b809fdfe8e7f9edff36,
   0x2016d812eea23b80be603007ea76d7fb80261ffe37fe09ffb5800f6001980021ffc2,
   0x200b07ff2a00ad80225fe76808d5f5ff7ffc200178013a00377ff9600547f87dfef8,
   0x2182f80045ff717fe71ffab7fde1ffe280065ffd77f0ea03028016dffb9],
  [0x1fff87ffadfecc7fe9600026297605b27ffbdfbfa803ca047b7eb49fe5b80371fe77,
   0x200b45421206a580125feefb3d3e08b07edb5fd1a7fe2e000c8008600157ffd5ff64,
   0x200187ff1e001d7ff65fe957fc2e052a8008a00427ff61ffa2800be00027fbfdfdfc,
   0x201028016e11748008e0f547ffd6006f7ffe5feae7ff0e00358009dffb7],
  [0x200c37e2aa00678023201a985f2dfe8083c1a004c81e9e01e280a32004c880820000,
   0x201617f8bdfd5d7e1369ef4825be09695d1860689807e600807fd3200d07ffee005c,
   0x200ec80095ffa580096017e801c6015680166003e80015fff780012002f8048e0122,
   0x1ff72797d2001d84759ffe97fcde0114800c6004b806e5fea87ff4a003f],
  [0x1ff9281d29f3667db71fd1383a7a37de827be0a837eb41fbf87f22605f4728fa0c0f,
   0x1f34d7dfe208cfa053a1cb87fa31fcd1825217d2680a8dfe0b80076003d80395fae0,
   0x201498001a01777ff2a0102829c206a47ffc5ffaa7fede000d8022200107e3e6017d,
   0x202967eb2a00737fc7e002b84bf5ea0d7fed5fef17f73e01bd80101fec1],
  [0x1ffea7fdc9ff8f7ff02007182075fc4c7ae2dff917fcf602e180559ff1a837adff62,
   0x200d984a0ab6038062a0079852b966267da2a07f17fe36000e7ff3a007f7ffea0001,
   0x1fff37ffc5ffc580381ff6c802c9fee680102007a80011ffa680041ff3a80801ffdd,
   0x22bb380175fd4f8036e01de7fbedffac8009dffe680389ffcb7ffb2001e],
  [0x1fffb805b9f8f77ff7dff7b8c97dfc8c7ed5e006a7f9ce023c810de00267b86a014e,
   0x2011aa9385e7bb811ddf39aaa5ba0eaf80035ff7d7fe6dff9a80021ffe48001dff8d,
   0x2000c7ff5a003780256007f803f9fe818009dffe68004600258030a00218020e020d,
   0x1fa248059de7cd800f20f697ff5dff3780035febe7fe86003f800b9ffb7],
  [0x1d6fc802f5fea385cbd94107ff062715800065f3b7a005fe107ae2df7827dd99f4fe,
   0x22f6180196011d74b520cdc804f5fdbc82b25e926757e1e71880b39f0517fd7e03b0,
   0x20c7882291fdc77fc41fffb79509e5817f39dfef680062005f7dafa0a2088cea0370,
   0x2005b7f341ff8f7fce5ff438149208927f28a02577f4c6002c80165fc7b],
  [0x2041c80aee060a833ca090a7f532019d7ff91fdc37ffae00638417e02b67fda1fdd4,
   0x1ffc680126001e801ca005a7ff61ffe68015e00d67ef79f5007b081d84682efdda3a,
   0x1f9bf81a75fa197fe5e012c7f6160154802fdfece8016a009f7362dea557fee242c0,
   0x1ffd47fd25ffc980041fec77ff32001d8006206797f1ba08827ebc604f8],
  [0x200168b069df487e15a0a4486099f0b98858df56e8d795fbf5816b25a387ffe65dfa,
   0x214937cb9a0a55800e1f71080eca0a728034e041f80e5dfe7b80abe03267fcf9fb67,
   0x200867fb86017d804d602437f8d6020e801c5ff417ff8e004480909fff7a6c06028e,
   0x203f98050e01f67ffce00a47ff19fff4800f5fda07e5560515803cdff63],
  [0x2001980785fe337fcfe03057ffddfff8800360005800fdffff7ffc600887fffdff1b,
   0x1ffdb80026000c8001dfff88003dfffb8002dffe58004e002c7ce95ff3d7cfda002a,
   0x20365821e1fd717ff95fff07fe6a0009800c5ffb380021ffe57edc2156d7feddffad,
   0x200128011e00387ff6e000a801ae001a7ff0e08f17fe99f98d7f43e0908],
  [0x1fcfc7f47202637e461fc887f48e007d7fd1200b87fdaa00d7830c5ff2f7fdee0133,
   0x201b17fefe000b7fe4dff967fe1dffe77ffd9ffae7f7a20204829f2200e7c5d21d96,
   0x2063d7e52206227fe2a016280cadfcdd801b9fe947fece01188aa1210c67fcda51fe,
   0x1ffe5800f1feb480029fe6a80255ffac7ff59f89f80209fc0d81449fba5],
  [0x202557f8c9fcab98b05ff9e7e7fdf2667fcbe1bc57f44601ab80931fbb8809fe0bba,
   0x1f6de8103601f47d4b1fa187f86e01ce7e945f396813c1fcb483ec9ff4f7c0f21361,
   0x1ffc9802c5f55d7fd81febc933ba67b58011e00c6802f203317ea0205d28105dff1b,
   0x1ffed801fa02957fd1e037c808fe01bb80076012780879fc71803e9f4b3],
  [0x1ff977f6e600cd7f31200557fbd5ff348097e027d7feda005280386016180021ff04,
   0x201c67fe21ff7b7f8c1ff2e8021200047fc29ff2c7fb11fd06830f9ff7072c61f8ef,
   0x1fdab81072069c7fdce001387cede6207fe65ff747f899fdd17f53de6837ff0dfd0b,
   0x201f27f4adfcb17f22dfa6e7fa11fdad8062204717f7160ad67fe120926]
]

/-- `22` integer witness columns at scale `2^16` for the positive part of `h1Hat`. -/
def lPosCols : List (List ℤ) := lPosRaw.map decodeWitCol

/-- `36` integer witness columns at scale `2^16` for the negative part of `h1Hat`. -/
def lNegCols : List (List ℤ) := lNegRaw.map decodeWitCol

/-- Fast primitive offset subtraction `x - 16384` equal to `P450.fromOffset x`. -/
def fastFromOffset (x : ℕ) : ℤ :=
  Int.subNatNat x 16384

@[simp]
private lemma fastFromOffset_eq (x : ℕ) : fastFromOffset x = P450.fromOffset x := by
  change (x : ℤ) - 16384 = (x : ℤ) - 2 ^ 14
  norm_num

/-- Decoded integer list of `oneBodyWeightsArr`. -/
def oneBodyIntList : List ℤ :=
  oneBodyWeightsArr.toList.map fastFromOffset

/-- Decoded integer matrix of `fragmentWeightsArr`. -/
def fragIntMat : List (List ℤ) :=
  fragmentWeightsArr.toList.map fun row ↦ row.toList.map Int.ofNat

/-- Decoded integer matrix of `innerWeightsArr`. -/
def innerIntMat : List (List ℤ) :=
  innerWeightsArr.toList.map fun row ↦ row.toList.map fastFromOffset

/-- Scaled integer one-body weight helper on a pre-decoded weight list. -/
def cOneIntAux (ob : List ℤ) (ℓ : ℕ) : ℤ :=
  Int.mul 58982400 (ob.getD ℓ 0)

/-- Scaled integer one-body weight $58982400 \cdot n_\ell$ at index `ℓ`. -/
def cOneInt (ℓ : ℕ) : ℤ :=
  cOneIntAux oneBodyIntList ℓ

/-- Scaled integer centered-shift leaf coefficient helper on pre-decoded weight matrices. -/
def cLeafIntAux (fw iw : List (List ℤ)) (μ : ℕ) : ℤ :=
  let r := μ / 29
  let b := μ % 29
  let frow := fw.getD r []
  fastIntSum ((List.range 14).map fun c ↦
    let mrow := iw.getD (14 * r + c) []
    Int.mul (Int.mul (frow.getD c 0) (mrow.getD 29 0)) (mrow.getD b 0))

/-- Scaled integer centered-shift leaf coefficient at leaf `μ = 29 * r + b`. -/
def cLeafInt (μ : ℕ) : ℤ :=
  cLeafIntAux fragIntMat innerIntMat μ

/-- Combined list of all `58 + 261 = 319` scaled integer rank-1 weights of $H_1$. -/
def allCoeffsList : List ℤ :=
  withListInt oneBodyIntList fun ob ↦
  withMatInt fragIntMat fun fw ↦
  withMatInt innerIntMat fun iw ↦
    (List.range 58).map (cOneIntAux ob) ++ (List.range 261).map (cLeafIntAux fw iw)

/-- Slice `0` of `allCoeffsList` (`58` one-body weights). -/
def coeffsSlice0 : List ℤ :=
  withListInt oneBodyIntList fun ob ↦ (List.range 58).map (cOneIntAux ob)

/-- Slice `1` of `allCoeffsList` (leaves `0..65`). -/
def coeffsSlice1 : List ℤ :=
  withMatInt fragIntMat fun fw ↦
  withMatInt innerIntMat fun iw ↦
    ((List.range 261).take 66).map (cLeafIntAux fw iw)

/-- Slice `2` of `allCoeffsList` (leaves `66..130`). -/
def coeffsSlice2 : List ℤ :=
  withMatInt fragIntMat fun fw ↦
  withMatInt innerIntMat fun iw ↦
    (((List.range 261).drop 66).take 65).map (cLeafIntAux fw iw)

/-- Slice `3` of `allCoeffsList` (leaves `131..195`). -/
def coeffsSlice3 : List ℤ :=
  withMatInt fragIntMat fun fw ↦
  withMatInt innerIntMat fun iw ↦
    (((List.range 261).drop 131).take 65).map (cLeafIntAux fw iw)

/-- Slice `4` of `allCoeffsList` (leaves `196..260`). -/
def coeffsSlice4 : List ℤ :=
  withMatInt fragIntMat fun fw ↦
  withMatInt innerIntMat fun iw ↦
    ((List.range 261).drop 196).map (cLeafIntAux fw iw)

/-- Fast integer interval midpoint `(lo + hi) / 2` without typeclass overhead. -/
def fastMidpoint : ℤ × ℤ → ℤ
  | (lo, hi) => Int.ediv (Int.add lo hi) 2

@[simp]
private lemma fastMidpoint_eq (iv : ℤ × ℤ) : fastMidpoint iv = (iv.1 + iv.2) / 2 := by
  rcases iv with ⟨lo, hi⟩
  rfl

/-- Integer midpoint vector `(lo + hi) / 2` at scale `2^20` for an angle-table row. -/
def midVecOfRow (row : Array ℕ) : List ℤ :=
  (givensLeafIv row.toList).map fastMidpoint

/-- Combined list of all `58 + 261 = 319` integer midpoint vectors at scale `2^20`. -/
def midVecsList : List (List ℤ) :=
  (oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList).map midVecOfRow

/-- Slice `0` of `midVecsList` (`58` one-body midpoint vectors). -/
def midVecsSlice0 : List (List ℤ) :=
  oneBodyAngleTableArr.toList.map midVecOfRow

/-- Slice `1` of `midVecsList` (leaves `0..65`). -/
def midVecsSlice1 : List (List ℤ) :=
  (leafAngleTableArr.toList.take 66).map midVecOfRow

/-- Slice `2` of `midVecsList` (leaves `66..130`). -/
def midVecsSlice2 : List (List ℤ) :=
  ((leafAngleTableArr.toList.drop 66).take 65).map midVecOfRow

/-- Slice `3` of `midVecsList` (leaves `131..195`). -/
def midVecsSlice3 : List (List ℤ) :=
  ((leafAngleTableArr.toList.drop 131).take 65).map midVecOfRow

/-- Slice `4` of `midVecsList` (leaves `196..260`). -/
def midVecsSlice4 : List (List ℤ) :=
  (leafAngleTableArr.toList.drop 196).map midVecOfRow

/-- Scaled integer centered-reflection two-body scalar helper on pre-decoded matrices. -/
def twoBodyTermIntAux (fw iw : List (List ℤ)) (r c : ℕ) : ℤ :=
  let nrc := (fw.getD r []).getD c 0
  let mrow := iw.getD (14 * r + c) []
  forceInt (fastIntSum ((List.range 29).map fun b ↦ Int.ofNat (mrow.getD b 0).natAbs)) fun sAbs ↦
  forceInt (fastIntSum ((List.range 29).map fun b ↦ mrow.getD b 0)) fun sSig ↦
    nrc * (sAbs * sAbs - sSig * sSig)

/-- Scaled integer centered-reflection two-body scalar for fragment `(r, c)`. -/
def twoBodyTermInt (r c : ℕ) : ℤ :=
  twoBodyTermIntAux fragIntMat innerIntMat r c

/-- Sum of `twoBodyTermInt r c` over all `9 × 14 = 126` fragments. -/
def twoBodyTotalInt : ℤ :=
  withMatInt fragIntMat fun fw ↦
  withMatInt innerIntMat fun iw ↦
    fastIntSum ((List.range 9).map fun r ↦
      fastIntSum ((List.range 14).map fun c ↦ twoBodyTermIntAux fw iw r c))

/-- $\ell_1$ sum $\sum_{j < 319} |C_j|$ of all scaled rank-1 weights. -/
def sumAbsC : ℤ :=
  withListInt allCoeffsList fun cs ↦ fastIntSum (cs.map fun x ↦ Int.ofNat x.natAbs)

/-- Squared Frobenius sum $\sum_{k < 22} \sum_{p < 58} (L_+)_{p,k}^2$ at scale `2^16`. -/
def sumSqPos : ℤ :=
  withMatInt lPosCols fun cols ↦
    fastIntSum (cols.map fun col ↦ fastIntSum (col.map fun x ↦ Int.mul x x))

/-- Signed weights `+1` (`22` columns) and `-1` (`36` columns) for $L_+ L_+^T - L_- L_-^T$. -/
def witnessWeights : List ℤ :=
  List.replicate 22 (1 : ℤ) ++ List.replicate 36 (-1 : ℤ)

/-- Radix $2^{96}$ for SIMD Gram packing. -/
def base96 : ℕ := 79228162514264337593543950336

/-- Weight bias $2^{58}$ for SIMD Gram packing. -/
def bias58 : ℕ := 288230376151711744

/-- Radix $2^{84}$ for packing upper-triangle symmetric `58 × 58` Gram entries. -/
def base84 : ℕ := 19342813113834066795298816

/-- Unsigned offset $2^{83}$ for packing signed symmetric Gram entries. -/
def offset83 : ℕ := 9671406556917033397649408

/-- Unpacks `4` signed Gram entries per radix-`B` `Nat` word with offset `off`. -/
def unpackGramWords (B off : ℕ) : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
      forceNat (w % B) fun u0 ↦
      forceNat (w / B) fun w1 ↦
      forceNat (w1 % B) fun u1 ↦
      forceNat (w1 / B) fun w2 ↦
      forceNat (w2 % B) fun u2 ↦
      forceNat (w2 / B) fun u3 ↦
        Int.subNatNat u0 off :: Int.subNatNat u1 off ::
          Int.subNatNat u2 off :: Int.subNatNat u3 off :: unpackGramWords B off ws

/-- Single-pass `List.splitAt` helper for `List ℤ`. -/
def splitAtNat : ℕ → List ℤ → List ℤ × List ℤ
  | 0, xs => ([], xs)
  | _ + 1, [] => ([], [])
  | k + 1, x :: xs =>
      match splitAtNat k xs with
      | (pre, suf) => (x :: pre, suf)

/-- Splits `1711` upper-triangle entries into rows of lengths `58, 57, ..., 1`. -/
def splitTriRows : ℕ → List ℤ → List (List ℤ)
  | 0, _ => []
  | k + 1, xs =>
      match splitAtNat (k + 1) xs with
      | (row, rest) => row :: splitTriRows k rest

/-- Reconstructs a full symmetric matrix from its upper-triangle rows. -/
def buildSymFromUpper : List (List ℤ) → List (List ℤ)
  | [] => []
  | [] :: us => buildSymFromUpper us
  | (d :: rest) :: us =>
      (d :: rest) :: List.zipWith List.cons rest (buildSymFromUpper us)

/-- Unpacks `428` radix-`2^84` words into a strictly evaluated `58 × 58` symmetric matrix. -/
def decodeSymGram (words : List ℕ) : List (List ℤ) :=
  forceNat base84 fun B ↦
  forceNat offset83 fun off ↦
  withListInt ((unpackGramWords B off words).take 1711) fun flat ↦
  withMatInt (buildSymFromUpper (splitTriRows 58 flat)) fun M ↦ M

/-- Packed radix-`2^84` upper-triangle words (`+ 2^83`) for partial Gram slice `0`. -/
def gramSlice0Raw : List ℕ := [
  0x80011b01e451ea8c800008004a05fb6c6d16c400007ffef1b8b740e296400007fd138f6bc3c65d940000,
  0x7ffe51268927ce65000007ffc924f84270e19400008001721f3f1bf36dc00007fffca776bb56ce500000,
  0x8002bb7cc0ee5d31000007ff84472004b6a7d000007ffd56c05d746763400007ffda0d056035a9980000,
  0x800910ef8c543eb5400007fffefd82d6c5cf6000007ffa02ffe95d92e940000801b282b8c62bb17c0000,
  0x8007a96d4a3305578000080013cdad0382ba0400008000c0f62a0e82ccc00008002500d22a3132200000,
  0x7fffcf06884f169e8000080001fc1944f4b7ac00007fff5ec0a6d3326d400007ffdb29aece85317c0000,
  0x8000b73a84c73ace400007ffffda437b8fe9c000008000a9d4dc5e0b4dc0000800088ecbe7f872a40000,
  0x7fec5226293d7d3f000007fff3bdb8e06c0d00000080010c0600bcc34a40000800030afc5337c4c40000,
  0x7ffd5d96f90ee7010000080001b4520a6f2a5400007ffe6c5adc737bc540000800142f64fd7c4fac0000,
  0x8002405093035c32c00007ffedcf20f2fdf08c00007fff256d844276f0400007ff0eacae26a5899c0000,
  0x8000fb24fd8c8b72c00007fff322b3c7eef74c00008000d0bd4cec17fe400007fff6aad156e4901c0000,
  0x7ffed67037e783f5400007ffffcf0d6175ec6000007ffebc9b8934c7240000080012db91eb8d3ce80000,
  0x7fff86099d559568800007ffeb92178a386ad400007ffff5ae736d0312c00008000e18029284096c0000,
  0x7fff4f3c8e76f352c000080006a4cd4e735f0c00007fffd7b0eeeb15e2000007fffe441375801be40000,
  0x7ffedb5dea90a2fc800007ff7601e36364e66000007fffece43f6744b0c0000800035a3e3e437f180000,
  0x80010dd0aec90545400008000f65312124c1f800008006ad7d9966d80c800007ffe861ccccefab900000,
  0x80002aef1ae68979000008002e91f772186ef400007ffc6aa768cec569400007ffe698ec63fb08b40000,
  0x80000a01574730d6400008000d64967e86c62c00007ffff5558b1bf830400008000258eff5a0a2040000,
  0x8000bcfedf29f4eec00007fff926a50589d6a80000800005c20beb0a76c00007fff41d8fbd424b8c0000,
  0x800657c1ba74e7a7400007ffa5309f101b2acc00007fff24060d5a1a60400008000b5e416ad0f7b80000,
  0x80061d10e1012454800007ffa4094748d5adf400008005cf0b75fad807c0000800691ac54cb90e480000,
  0x7fff79f1aa0f45ce400008000bd4e65eda71700000800687126acbf453000007ffa4087602ed58e00000,
  0x800103665c6c4be28000080000ac2739b3c94800007ffff94ed57dcaff4000080004a525c7cd152c0000,
  0x8001201e087c2d3fc00007ffecd5b7082d6f0000008000e3f7955774a7c00007ffdbc3758980c3000000,
  0x80003984bba2a846400008002ac2b837ca3af000007fff5d005a353bdf800008000a6fd23d5deb3c0000,
  0x7fffcbc1795afed4800007fffb5ea8c3a9b79c00007fffd4fd44b3d239c000080001ae369ed984680000,
  0x7fffdc58f1912f82000007ffff0e0185cdd98800007fff909427060fc0c0000800024758ad3bf4bc0000,
  0x7ffc5dfe0cf157778000080044523915892e9000008003ef4bf999869f800007ffc62f2648c02c640000,
  0x7fce55dc3131c9f1000007ffc51824491d659c0000800492e7ce883a91400007ffc9bf46c0f7c9180000,
  0x7ffcfc92fc13c2e8400007fff22f156ade9f6800007fff1c8f9b4be5e9800007ffefdc3d2b9842780000,
  0x7ffcb0eb2534be34c00007ffd0ce662067f5c800007ffdfe997dbf418d400007ffd0223aa3d3e5d00000,
  0x80022b1220fbfc58400007ffb21b596bf6365000007fef0804788b4f4440000800700c8b1dc1c6ac0000,
  0x7ffee2d5bc2a6dd6000007ffe6a30ca765f8dc00007fffb8c197aca6d7000007ff8282a3e1f984ac0000,
  0x800031ce1f40b064400007fff8518220623d3800007ffdfe925864fdc5000007ff82c55e39f4f20c0000,
  0x800058bfe0bdbca6400008000c1208d3c746e800008000f0023bc1193300000800005baccffe2bd00000,
  0x8003426abd43fbf8000007ffe7e18ac6ff25840000800029d15b884ece40000800104af536763ac80000,
  0x8000cbe749b4a72e000007ffea8229e3920ef4000080017d8e3105c66e000007feb0da53cebeded40000,
  0x8000bb3235cc20d8800008000729fc04fead0400007fef923414dd908ec00007ffdbc652383da3200000,
  0x7ffe9db5051f2fa9c0000800050cb5abe7e8bc00007fff0259973292c10000080025e6f41e958afc0000,
  0x7fffea70ebfd7d5fc000080000ef249de04654000080002b6e1dd0c532800008001b86dd71020c880000,
  0x7ffeb3f0282072c0000008002f51ed753237d00000800141558840c471000007ffe8aaea8809d2000000,
  0x80008033e54f3c1ac000080001f910caa09b0c00008000018b6790e85d800007fff94766c8ea9ee80000,
  0x7fc7f40c8a7bee64c00007ffff8bd7d67ae05c000080003c91614b76d200000800013732749248dc0000,
  0x8009180574c1bb9fc00007ff62d31c0de7a4d800007ffeef52d3fa8cd840000800987d88b3d05ed80000,
  0x800660edb1095bdc400008008b9aedc717be6c00007ff2261eafdb506600000800c4610225959c440000,
  0x7fff3d4e7e8b4d25800007ffeb5ffea6001d5c0000800750e753cc08db80000800a5cd1a483d8a080000,
  0x7fff516abdac8eed400007fff6fe87b48747b400007fff9907dc3ea7ef800008001311b4da653d7c0000,
  0x7ffffb47ce4290c4c00007ffedf819651ef75800007fff964545e32291c00007fd87735c55a2a2d40000,
  0x7fffaffde8a4a93280000800025968b12c53b000007fff5bcfb2bb3ed1c00008000d48d8123186080000,
  0x7ffffaac1da0f40c400008004237d04aafd72000007ffe9af158e38412c00007fff00cd7729bbb440000,
  0x800403bcbd505c89c0000800667a6b1737f74000007fffe935cd86d586400007fffd16d3cd4b84a80000,
  0x80053be17d64681ec00007ffb26f99d8070dd000007fffb9c90e86be57000008001c1ef79c2d84e80000,
  0x7ffea985d379f3eb000007ffedd54e5df1f75c0000800128d9783e31b6400007fff80dfe0494b3a00000,
  0x8000fb0dd5fe929a4000080000dcd331a962a800007ffeb617b3b0b694c00007ffeb01a4ce41cbfc0000,
  0x7fff16fa8f0259d7000007ffb3f4dc413184fc000080013bf07f3c5e2d400007ffefb5fbf20b72940000,
  0x7fff1f1c29a8dbc8400007fff74925550245d000007fff2af0231de961000007fff2f4daa5264bcc0000,
  0x7ffcb173990ea91c800007f8c9454f79703f0800008000c222a1e3ad76800007fff017023014bc8c0000,
  0x8004fcb0bfcb0935c00007ffa840efbb5eb37800007ffafbf927c178bd00000800482693d7a9115c0000,
  0x80041cea61689d150000080030ca9d27c37e5800008003a275af2996c78000080040f7a2485670ac0000,
  0x7fffd8bac9f63abd00000800078f029ae9a27c0000800000b70ffcd4df000007fff6307fae8e692c0000,
  0x7fffa62b72a9032a400007fff5be2d81b221240000800055da11299840800008000768253d67876c0000,
  0x7fff5f51c3b80937c0000800061604448db4a400008000a4cdf0d010778000080006df0b6251fc400000,
  0x7fffd43a2c29b535c0000800082c59fd409b2000007fff8b69b899ff7580000800096a2b1b50206c0000,
  0x800016f623b14af8800007fffc9cf4373e1efc00007ffffa06ce156322000007fff0a5aa8308bf380000,
  0x8000de6e6caf29bbc000080038eb97c75d03d000007ffd1c119f47e12740000800199837bc6f71880000,
  0x8002c078988b8494000007fff1f6be31a6e9c400007ffcd8b2fff8b1e74000080028b50986d833a40000,
  0x7fff868f8d3f3741000007fff675fe43b0b8ac00007fff702685df901a000007fffb165b665819ac0000,
  0x800042ce5d4959aa800007fff5da41c7eb1b980000800079960e652f50c00007ffff55e8a52aeef40000,
  0x800058c742f5e6534000080004e49d6af729c000007ffff757b66b591bc00007fffe0f9fecb3d9240000,
  0x7fff991048048c060000080009b7220a04acbc000080001eacdd11da4d000008000237afccf3cbe40000,
  0x7ffbee448b148503400008004591f83388f03800007ffc8a85cf9fafc8c00007fd4c5d22a0742e6c0000,
  0x800669352fd7af7ac00007ff9dc0380acc906c0000800648784a4d5269400008003ccbdd69d46af80000,
  0x7ffe62085e5327c940000800006bc770e785d000007ffe4323630abf01400007ff982ef67be9b8340000,
  0x8000943cc31505240000080012bbb9642f6b8800007fff1e3e0519d7cc000007fffec99c9810d1300000,
  0x80005def06d0e2f8000007fff4bce2ab117eb800008000914949d448e38000080004f696bcd2eb980000,
  0x8000aebb3c7903604000080008d29ace179bcc00007fff36d36c171b9f400007fff7f5a353cb14b40000,
  0x7fff2f43a577ea6f80000800079a96a49995e400008000765479e115b5000007fe310a1b1f2c75900000,
  0x7fffd76e2d6d6563c00007fffe60b1736705c40000800138a30a495c640000080010c92bd4db91040000,
  0x7ffbff5e3501f787000007fff66a9bf23665fc00007fffec3779d064de400008009b3ef20a35bd180000,
  0x7ffec50d4b7f9a27c00007fffbbfc80b6c0a280000800013319a884097c000080039d6c34e1a04740000,
  0x8000da676f168fa8000007fff7b5ec17434e9000007ffff8ab57ba4033400008000e36b13a40506c0000,
  0x7fff75b8628562c7c00007fff72a59ad612074000080001b242f27f24dc000080007dea757e632200000,
  0x800121c12799669dc00008000966b0f6881e24000080006b2d04d53905400008000c7ec7a1067cd40000,
  0x800904c6d4c59d468000080076e97b9cbd4ae800007f84ed1ee6835e49400008001024ad174de6f00000,
  0x7fff07318c22fe26400007ffa0646c91f6509800007ffea186f16a224fc00007ff820ded117b32100000,
  0x7fff8ff7153fa67e00000800057c6c1984c9140000800073ac483e0d88000008000d0ab6e6c0c3e40000,
  0x7ffd3e8c6643c5668000080008db8deb44e4c4000080000392374901ebc0000800066ba8df3b79240000,
  0x8002ac501fd2cf64800007ffce585459fa5ab800007fffe25db0134771800007fcb379ab3ad6bc300000,
  0x8001e6ff55000395c00008001a30b902ce801400007fc9e807691ba8f7400008000083d1ff8a1c400000,
  0x7fffb88c83ad664d40000800404cc79fe25a7400007fffe17b4c54dac1c000080036fc01d081e4580000,
  0x8000696aba152735000007fff687186b84674000008000d1e44c13a99dc00008000c655a805dab8c0000,
  0x8000d5b17abbc36780000800afc3f5fa26a728000080037f85730734e2c0000800040b1327d2c9b00000,
  0x80003337462e692c4000080001eebfb23d3cd80000800139bede371e61800008001fb0586e05b8600000,
  0x7fffd340c997090dc00008000391b0c6670b18000080000be5ff1d215f800008001cd9b23b132dcc0000,
  0x8002c18c7bff327dc000080057b346d96e168c00007fff7401bb9bb0ac4000080000ac57b52435740000,
  0x7ffff2d1e5938f11400007ffec639476d83e34000080001dc279c37032400008000004ebac7d93340000,
  0x8008aa8bbaa2b78a400007ff8cd6a097335a5000007f89e2bf277699e0800008001289290545b7840000,
  0x8003f4972f904c8980000800216cf61a49b3a000007fff8c894c51634b800008001338abb193c4a40000,
  0x7fff59de6215c05b800007fff9e556cc2cfe3c00007fff750a77ef2e91000007fffdc9d94e0938fc0000,
  0x7ffe6c958322c3d2000007fff5877663dc974400007fff746a88262856400007fffe0c4ca6350ab40000,
  0x800320df1b43d61a800007fffc0c78f0097eac00008038d81a7ee2402f400007ffe5d6ea019a1fbc0000,
  0x7ffc5b5a3b54d50340000800006dff13023a7000008035c94d32dcfe65400008002c4196526dc6480000,
  0x80002ced60ecc152c00007fffea8caa0bae03400008004698c19b13ccd4000080023dd22095bf8ac0000,
  0x7ffe209f27fe24070000080005a4dd36f5970000008000a547fd6fc0300000080014d0ae144bc4480000,
  0x80007a79c213a3a4c00008005531a99564c54c000080033ca7189500cc80000800f0793bffd427040000,
  0x8000101c7b94ae510000080000b917261c158c00007fffcdd254798055800008000170562646d1900000,
  0x800024356dd3a547000007ffef0ffb77198f0400008001269ceb67527800000800008f87d8e58f400000,
  0x7ffff7c0f7a13fb640000800126b05d11899cc000080004214f450c448c00007fffb23a80aa6fa9c0000,
  0x80057cc330e19c6d800007fffe42e6d5cd39ec00007fffc9943d23ed018000080017499400e923d00000,
  0x8001e9e755b7ed6680000800276f845450f9280000800828dd7b8eb98f800007f814fc82b67f299c0000,
  0x7fffbbe4c93c8778000007fffbaacfb2988514000080014437b5d61a28000007fff2bc56b6f6f14c0000,
  0x7fffd1993143895b000007fff9b662851705100000800043eeef12bc168000080007833bc3a272340000,
  0x7ffdc3d1cd8f5ffec000080341610d5773f67c00007ffffe7755d35bdbc00007ffae09bff9168fbc0000,
  0x8002d0bc4132733a400007fffbdb308a4057f400008033bf349df284e8800008001f74ea8195cbbc0000,
  0x8004300adc328b01800007fff01c16f872fc48000080049823c4f8f16e400008003898010ce6a5680000,
  0x7fffe1c88b24c393400008001396c1005c833c0000800024064da3d39f8000080000cc6b631ddfd00000,
  0x7ff302ddf1dce6d8800007ffc179ffabd150700000800016d302a27c658000080012999cb31acb780000,
  0x7fff7ba075bc5a3dc00007fffd8fa3e4efd8040000800362be4f0e97f50000080011ec0633d5a82c0000,
  0x7ffffa15e9af89d0c000080000bd7cc40c7a2000007fffcd52aec55789400007ffff6582feef23ac0000,
  0x800000a921fd9673000007ffe31d0a5eb609c800008000022884b22a308000080001cc9d1a820c640000,
  0x7ffff6998e4a79ac800007ffa3e7449c563e3c00008001a14d58c23883c00007fffacf19fd7b29200000,
  0x8000b9bebef6b7ce000007f8077f33136751640000800003889dc48b7e800007ffcd8bbd47c985800000,
  0x7fffca835d7e062b000007ffe1006f6670ba0000007ffe6109f39e0ad0c00007ffef0617f07b7cb00000,
  0x80005b0e80483ac3c000080002305daeb5e6e800007fff99a94acfaf4a400007fff89ef31a6239b00000,
  0x7ffce4e0ea47454e000007ffcf115e71aa371400007fffa7c5297e4540c00007fffc0682b23307700000,
  0x80021ae46dcb05ad4000080020822df104fb98000080347219db002f96800008000866c3503e4f2c0000,
  0x800496ca7208e0f6c00007ffbcd8e6bdfdb97800007fc9a82fe9e46653400007ffff87f370c705840000,
  0x7fff48e9b3bf64a3800007fffd2a4eacad08a000007fffd378bddef45f00000800441d34eb66f7200000,
  0x7ff38618afd7d59f800007ffe92dac1b22684c000080001459653a21be400007fff2876b93475d880000,
  0x800048b640f15ccc000008000a8a4a997e9ce40000800130bce813f9bd400007ffe0c42bc1edf9680000,
  0x800008f78495b26f00000800016066477eeab40000800014ee72b4ab53400007fffba88a82022e880000,
  0x80000b6eae983c8a000007ffec5fc483077f7c0000800007c75d4aff32c000080000640f1fd8bbd80000,
  0x800007adc321f2fa000008007a549f784320c400007ffff192accd66f8c00007ffea138be65f52fc0000,
  0x7fbe978dd8459907400007fffd8162325996fc00007ffe275d0ce7d040000008004001bf729b77880000,
  0x7fe44cae80a94b3e40000800217df6d35aa93800008000eb8a1585c27ac00008001624a48b2727b00000,
  0x7ffd9446ddd777c5800007febceff9ad4a655800007ffeccb642ad6f62800007ffd92b425a04eb240000,
  0x8001e3b87297dfff00000800008423246de16c00007ffc33b24c8be22e800007feab1aa1185926300000,
  0x7fffe32fae21fa26c00007ffded9ce336e79b800008000410eebe22ca2400007ffffa2a6719de9640000,
  0x7ffeb2eb6af307b5c000080039df9559a8fa5400007fffe88f557bb8c5c00007fffa951b403b7e100000,
  0x7ffec76b42a04d83c000080041abacfad9361000007ffcaf3ce0f1d3e1800007ffdd47ddedecfcf80000,
  0x7fffb71c3f1b776dc00007ffdce0c011ab548000007ffebf2b91393f3dc00007fff207d8ea38c9c80000,
  0x7ffff7c2568be6b5400007ffeeffd3a8d3e2840000800029605795328f4000080023ef4b8bfb0c2c0000,
  0x7ffffd44aaf792f9800007fffece43d495b7dc00007ffce518c7b14db3400007ffaea73470ca3ac40000,
  0x7ffdc4fa06cdd3f8c00007ffe9aa9e3ddc377c00008000edcbfc45a39c000007fffa3de8b229d9fc0000,
  0x7fff9e9b99d6069b0000080001fd376589a5f8000080000ed03ed14c08800007ffffd368ae5b0ba00000,
  0x7fc510365e3470574000080001cef1f19c175c0000800052423093ac3ac00007fffc74dd5a0c83b80000,
  0x7fedbd270e8a9a280000080012580cf0aad02c00008001dc310931bda5800008001fb7bf752a8f1c0000,
  0x7ffd7074a17104b7400007feb2e4ea34b9703000007ffd95de83f1018100000801b9cf545ee5d8400000,
  0x7fff9a25cd2c068fc00008000026d5d920917800007fffdf5c561f840ac00008001b26064fc4f2fc0000,
  0x8000213995f6441c40000800306801a120557c000080000de366e62c3ec000080000c788c812caa00000,
  0x80025f8a680ab44e800007fff3545f79cd3c3000007ffbc92e73a6a35e0000080003667ffd1767f40000,
  0x7ffed9da6a53c2c8400007ffdbb934ac83918400007ffc4f30da91145a400008004d31cf24faa22c0000,
  0x8001c0e79fe4e1a7c00007fff8e2b1042d55ec00008000dd608d637a8e400008000c15455e8ebca40000,
  0x800002990dcb1c33000007ffbc20208cf40f2800007ffed36223590825400008000247daa2b77b600000,
  0x7ffe96511ba7c3f0c00008000d7200f0c52c7000007ffc8f838cc8a4f9c00007ffff0e4024e06bd80000,
  0x800109b61ddd141d40000800021558e6e1812800007fffb681dc301fe7000008000b3bb1a64a28940000,
  0x80003e0187feffe2c00007fffee1da01698c3000007fffe5112be7a095c00007ffd11111828a62ac0000,
  0x800143fb94c198c4c00007fb632ad2aa330c9c0000800003298e04e0ee800007fffe489fd9c291640000,
  0x7ffe83e775f65fc2800007ffcfd29a630d2eac00007fecfb65781bc976c00008002ca3735e746b240000,
  0x8000102aeb156f2080000800198044e90a255400007feef0e4a9ab7ca9c00007ffe0688dbff5b6540000,
  0x7fffa6d097c238ccc00007fff5976b14169d400000800003bb8632b686000007fffd37cb8514daf40000,
  0x8003df1245a68887000008003811c2aae429e000008000168ae99d8e5bc000080000409458691e3c0000,
  0x800181f73f006fe50000080003c145272bc7180000800195df539f159f000007ffa1e978d8f037740000,
  0x7ffe1400ef90ecda00000800041421f11cef8c00007fff07374802fd02000007ffdd07909ea8e5040000,
  0x800033240d3f60f7400007fff5335ee117946400007fffe2fae7784e6c800007fff534d6ac823af00000,
  0x80006edeac14b390800007fff2faef03403fa00000800189e68029374f400007fffa63ed087ffd5c0000,
  0x8003361b1bc466a10000080005e4c29fe7d55000007fffab7ed5b13008800007fffb7708b79f8b840000,
  0x7fffbcbac9e4c9ee40000800009e3155a03f2800007ffff3d5781a1b1c4000080004260d08c32fa00000,
  0x8000221702cd579b4000080001e39a4acc90d800007fffa0637187dd29c0000800005f25118107780000,
  0x7ffc8e7976cd5ac9c00007ffdd37d9e32c5a5c000080030670b2f102a3000007fc0567f8b2772a2c0000,
  0x7fffb720c2b01173400007ffdcee6f445183e800007fed0816d197e18b000007fefa3b9bd4f63ebc0000,
  0x7fffeb8b48588f5cc00007ffd2cb6283ba4360000080001abbe86798e9c00007fffe0ac387380e480000,
  0x8000140f8378936ec000080019484414f5c00800007fff506e67b7a253000007fffda31e0c388d600000,
  0x7ffe105745c8bf57c00007ffde1df842842cdc000080016949f2a17b00000007ffb4ca0c0a0d70fc0000,
  0x7ffcf3e7b5fe0015400007fff2b09ecdb1de9c00007ffdbee8093fc851800007fffcb4de300055cc0000,
  0x7fffc634b38ca208c000080007d43b61933ce400007ffd8c754e2b5910000008002bb94e58acf3880000,
  0x800273b2a745bd9d800007fff416436b431030000080009b322a86b2e0c00007ffe6d43732d38e100000,
  0x800038e7f56449618000080016c90f3ccbffcc000080007d4167716289400007fff53235503ad00c0000,
  0x800003c4342e0e92800007fffe2587d763ff3800007fffbc1885390429400007fffa1eacebca834c0000,
  0x80000f2b474302930000080000907ea2f2995800007fffdfd17cf5dcfb400007fffef9ba9be71fc80000,
  0x7fff3cee174223e7800007ffe23f5769bab0d000007fce8c78cb9eb00a8000080007e6db4f8dca340000,
  0x80009cf9f553082e800007ff321dc54f052cd400007ffe07d58fc25c72400007ff142b504d6cece80000,
  0x7ffffbac347f4e92000007fffe2f1e502c48a400007fffff5de7ca3130800007ffffe7657c8495e00000,
  0x8000046283e2bd0fc00007ffff260a683c9cf800007ffffada0cd7044e40000800044968e7374c0c0000,
  0x7ffbb147ae163e27000008000dca15f1efaae000008000580d9ea537de400007ffe986eccbd8a2980000,
  0x8000d133a5cb39d340000800001fb75275536800008000115d4bd35c52000008002f0f45742e8b6c0000,
  0x800008ce66db7630400007ffef83558e22486c00007ffff7a436ed6270400008000c19c4072e30380000,
  0x7ff8aca1e3d9d16d800007ff8ad2cefb01a2f800007fff9ec4e7600bc98000080003310bf46634400000,
  0x800129c127da573e400007fff8a1b04c5bd17800007fffe5de448dde96400007fffd80f7358e7f380000,
  0x8000133220416bb4c00007ffffea02239c01f800008000a0b397c383c4800007ffea4a79b832a6fc0000,
  0x7fffcf9edcc46c26400007fffe58756fadf6d400007ffff26712e4ec20c00007ffffc3202832d7540000,
  0x800227ed926dd07200000800c7ec0912d27efc00007fc4d6fcfe2b7de5800007ffff8caa119d96480000,
  0x7fff27594618b5030000080001e7a7fe0471dc0000800623ce8d3f4f5c80000800440139c06706800000,
  0x80001f89929c54f880000800042028ec14947800008000298d09b3fd8e00000800006ca1f81bd0940000,
  0x7ffff8b17064e4f9c00007fff6d340597affb800007ffff73fb1ece6cb000007fff1b41d185dc1240000,
  0x80071dda3dba1609800007ffe1461c380d3560000080003f3b5c44e704800008001fd33604dbd6d40000,
  0x800062d81c3a6d718000080016f41363b408580000800036985e13985b800007ffe276b899abeed80000,
  0x8000973b612a27d4000008000804f3bf3f3904000080002fc895f82dd6c000080003de4c39b4c8480000,
  0x7ffdbe2b9c117ff28000080005275a6dcb155800007fffc229198c7b0a80000800128df38ae2a0f40000,
  0x7fff7457870d0e52400007fffc0f76e12b902c00008000c1fd73345435000007ffffc24b8de8bb840000,
  0x7ffff968891dd479400007ffeedcdd8f933ce80000800039bbc1d8ce614000080005c93025f2b68c0000,
  0x7fffe9b468f3e71a40000800012cc658b5f14800007fffa509209fe9f30000080000ae442220c8980000,
  0x8001e3bfee978c5ac0000800cd2da66010530400008001dfcb8fc50b50c00007fda3d5e221bca9880000,
  0x8000090d9984c9c1400007ffff80e7eafede84000080004417f79d9296400008000ad1fc2ec78e0c0000,
  0x7fffcc495171c668800007fff8dd49e9971d9c000080000baa028c0028c00008000016c33c24dce80000,
  0x800115d4e95041a08000080009eb712a64ee5800007ffe4cec89cf3783000007ffff76b87e1a39b40000,
  0x7fffad4fd79dce47000007fff39154e20283dc000080040492f21d167ec00007ffbccdb17bb772c40000,
  0x8000d30e0a68c4fc80000800039aca55d7fb500000800106fbd01d5028000008000bea353a228bb00000,
  0x80003aaf3818155d800008007fc5e910b5b3fc00007fffbd50ab43cfbec000080006df9d312babec0000,
  0x8001b99defc9096840000800042f0232fe60c000008009210a99eed96180000800033c15c5c50ee40000,
  0x800009725d7084de800007fffd60f6d6260dec0000800046b799650aa1c00007fff7122d64a795a00000,
  0x7ffff10fd101e71bc00007ffff84189346e38800007fffefee4999211a4000080005b8cdb9ad17500000,
  0x8005d93be66fdd44400007fca0a8cd7118695400007fffe3d6ca68283240000800001f51d78a549c0000,
  0x7fff2baae6712850000008000082289ae52a1400007fff9967c515d066c000080056f3c01146ff700000,
  0x80002f6efc7584db800007ffff96a6858cf00c00007fffdb801448c3750000080001ea5d5902748c0000,
  0x800147648c3a0c04400007fffba5424e92f4ec00007ffff1eea075687f400008000a09f55922ac380000,
  0x7fffe69a728f0709400007ffd1e37a14a387dc000080059dbca6b707eb400007fffcff48615712f00000,
  0x80001658aadfc544c000080008201caec910d800007ffe1e23d227c6c3000008000a8ae7bae0d3140000,
  0x80001736bca5d2b90000080003e75a7f9262a00000800045f3c5963a99000007fffafd0b5ca194c40000,
  0x7ffffe0b4c787d2940000800069c89d0a8a01400007ff7b429524a1d5e400008002de945aa664c640000,
  0x7fffc84658c8d29b80000800102f9149a9a8fc00007ffcd06faaefccae800008000134d96aba51200000,
  0x80005a159b2abe44400007ffff4705c0d45bb400008000049b137b9d7b4000080002e7597029a8d40000,
  0x7fcc8667f26e9af6800007fffe9de2a98ae8dc00007fff92da3416bf7640000800029cc4daa78e400000,
  0x8000016f90798f1f400007ffff1c13d6fce1d000008000405c8580f5b980000800261a0b33eca3000000,
  0x8002876459805588000008000124fbfdb7cdc400007ffff89e033631b30000080009ce0525452c140000,
  0x8000ddb3e63f4d2f80000800091042917f05ac00007ffffa70e3482947800007fff46fa52d62a5d00000,
  0x7ffedcd6f6e901828000080033cf1aadb861c000007ff642d0d88d4268400007ffff0e30046a72780000,
  0x80003bea0f7d9ebd00000800261eb306b4dff400007fff283e1203cc964000080004f8ca042fd3400000,
  0x7ffbf538492d9dfe000007fff755d6bcb622ec00007fffe1ee70f67333400007fff82ffcf286d4d80000,
  0x7ffea66ac931da13800008004411c6e79368b400007fffe7ceb142b43080000800040ab7501693f40000,
  0x80000ddf2936b411c000080005feaa38b406b800007ffe932cfde6e34c000008005d16078b6673d40000,
  0x80001115afb87d9540000800008ab9b934b0a4000080007ad0fd2e6dd6800008001bd9aec8f91bd80000,
  0x7fc99e1bf7b6adc2400007fff9974e7e82a55c00007ffffdce5f92e721c0000800008a731a06bc700000,
  0x80003e0386d641c1400008000eba5f9b22029000007ffffe32bdcd9d0c400007fff456a3553759a40000,
  0x80002232bd6061a0400007ffffe79051d60240000080001fe001d85d6680000800004d6486ed56380000,
  0x800030742d5b40d9400007fffe95198a07522400007fff1c44e840aaf54000080008d2d7bfb43c9c0000,
  0x80009789a75d6eb9c00007fff630c5265f15c400007ff9ce943081773a400008003222cb9d7fb24c0000,
  0x7fffe13c6472e35c800008000011f4b76dee0400007ffdfe2404e0cb05c00007ffffbd10d3463d900000,
  0x7ffa9f279ecf474d0000080007078a7b24b96800007fffb10b8bac4689000007ffff8abde0f06dc40000,
  0x80008a3c54c170c880000800022584c9920a4800007fffb98eb4ba949600000800378dd7390e0ea40000,
  0x800017d7d56e92c1000007fffc1d490294e2600000800501cc08e66941c00007fff368f0b51cec400000,
  0x80010148d6dc2e3d000007fffc1b41114e27a800007ffffd2f9d6d9d0d0000080000933a666ea0080000,
  0x7fffb6864e99ae87000007f8492351a3ed667000007fffeab34d56b712400007ffffb3ce083aab540000,
  0x8001117b75a3753a4000080009f023afb9fb5000008000114172189ea980000800163935184d62680000,
  0x8001a15c69be3e22000008000e3923f3cdb32000008000c09517103fd54000080003703774de839c0000,
  0x7ffef376932e3e4fc00008000be43ab0ff48a00000800073f59baf718a4000080021a52a61256a3c0000,
  0x7ffee7a9d07b782b800007ffe828b072ffc80400007fffd5d8be44408700000800143632c0bce4a80000,
  0x80016a7d6301a73bc00007fff5bd6a149c354800007fffb5d8082373f88000080006d9f13f25e8680000,
  0x7fffc6b935b7ce718000080008530dae4ae324000080006cf03753a024800007fffddbbf256c3c300000,
  0x800033fb3eb757fb000007fffdce2af54ae16000007fffe263d7ac0b79c000080000384949fdb5180000,
  0x80002f65a2c6bc41400007fffe06f655548da000007fffbeb5ab0703dd800007ffdcd164a6d132340000,
  0x8000094d74c48c2f000008000b30f4208978f800007fffefbc0fc81bb38000080006c8eb4817c0ac0000,
  0x8000e6e0a48f64edc00008000fc8d62ba1e88c00008000636c51002786400007f192eb2b7b4a642c0000,
  0x8000decef92a25090000080001ff1233ecab3000007fbca5344ca37809800008000a8c5dd7dcd4280000,
  0x7fffd2bbe581cdda800007fff49178d95c9ba800007ffff59e537ca1b2c00007fff12bb23a85ce840000,
  0x7fffc8d4fa5cb69c40000800047d957b236e540000800089c8d51b7e5fc00007fff82fdb720500940000,
  0x8000f9edd686c32b800007ffdd7d6c35c1bab400007ffee90be689544bc00007fffd8c7427c070b80000,
  0x7ffff9f157119c0c400007fffeba582efacb1800007fffaaeb5dda156bc00007fff8f11dace8c1ec0000,
  0x80000154859c3067000007fffebe5e5a029b3800007fffad884ccd1042400007ffe3585abdea41080000,
  0x800da9dae9d60cdd0000080035ad7fad7ecca400007ffffd2051dd7c0a0000080000daaf62c04fe40000,
  0x7fffde693576debc800007fffd1ed6f60630680000800029a2d8e36b69c0000800039004955e94940000,
  0x7fff1ae509a65748c000080003a6354de1507400007f0c95571b724c2e000007fffb5b9e267143a80000,
  0x7ffec4cc9c07ecc1000008000eaa6266a086c0000080009a28105f0c01c00007fbbba5bd216d33d80000,
  0x7fffa1c8e23f9481400008000e83c0e2eb1e480000800000643a3f1498c00008000c37417dbefc9c0000,
  0x80004d1d51b78b2e0000080005e6fa76c7a1480000800040005f775f3e000007fff94c6631658c400000,
  0x8001008ed782857d400007ffec5093e4a1c46c00007ffe6e1f6fbea13ec00007fffccd3753b869200000,
  0x7fff8bc980dc83a0c00008000c8113ad24bcd000007fffecf871757a10400008000c47015d2112fc0000,
  0x7ffff7274b5ca1c1400007ffff77d286a85ba400007ffff3cc5ad451dd000008000088d01fb667b40000,
  0x800004dca03136b8400008000029baaec0a2a000007fffe516a7a464aa40000800016164475a13840000,
  0x80016e1c0b34d40d8000080003ca0c5257c5980000800e0c54d75230d8400007fffa3ac4e9fa9a3c0000,
  0x8000f5635373d4c6800007fff948fb2038219400007f3bcce6169b3d44c0000800016bcaa987d9cc0000,
  0x7ffef218568c4eb6000008000a0d577b98925400007fbbee896a78bb62800007ffef2a17898ff3680000,
  0x80003fe2b2009aa2c00007fffaee8eba37870000008001bca23fa7d0df800008000d68439abd40540000,
  0x7fffcd469e3f8889c0000800041862eaa4044800007ffff447b9636428c0000800067f56df3722cc0000,
  0x800171191b866500400008000a18030b81b4e400008001311326aa8f29400008004da664392b1ee80000,
  0x80001ed9cfbb28a6800007fffdef1c3e6e98fc00008000068f1e261617800007fff6b23b7401d4680000,
  0x80000d71961ef138c00008001b8e4377b01c3800007ffea759905c042a400007fffda7fc501cbe9c0000,
  0x80000bba47d61c38400007fffcc98ae0be92c8000080005d623139a047c00007fffdd5fa3a5a88600000,
  0x7ff97b9034692f26800007fffc762f8b1e95c400007ffffe9723d1acc44000080009edfcb2c860a80000,
  0x7fff4e9f726b5948c00007fff266270c68a50c0000800006c5519d1cf7400007f04b933a896805780000,
  0x80008457267b9129400008000d1baef16d33b400007ffee46da049f1754000080458129111b7d2dc0000,
  0x7ffffe63683507d7400007fffa78da7828b68800007fff5c6c330637cac00007ffff29521413ab580000,
  0x7fff07d6fbf96c53400007ffd5e0fa3fbdcdc0000080002b3c72342ba800000800045f417a675ec00000,
  0x7fffe58f0ff15b05c00007fffec236ff2e3b9000007fffaf3215163b1e4000080001817e0f1d6c0c0000,
  0x7ffff195711503fe000007fffe2765b5d005bc0000800059c81cb0994dc00007ffff744f371acf940000,
  0x8000024530c85a038000080002fa2f25627ae0000080007b4a5c8fdfd70000080000929574ac42380000,
  0x7ffc556e09cceaf340000800023b456736745c00007ffa32d63645ff72000007ffffaa0f4d1e5f400000,
  0x80007203d4974dbd400007f16fe78a8e41514800007fffdfc590d7fed1400007fff5e5a8dbf07b340000,
  0x7fffa2a7086997ad000008000e4f0d12a2faf4000080013437623cb911c00007fff10727fdbbbaa80000,
  0x800014817f792fb6400007fff611c75bb028840000800042ef1efc57de400008000b326ca6a7fa940000,
  0x7ffed53db90c0da6c0000800067c8682dc7900000080003d87628a3e53800008000635aef696fa600000,
  0x7ffff949206b14a50000080006038fa8cbf11000007fffa745243136bc800007ffcb62d8303ddc640000,
  0x7ffffccb078d0f58000008000013a3533547c40000800060c20f46d4a6c0000800106ae48d76b6400000,
  0x7fffe64e25f4e0ae4000080002edbcd919a5d800007fffd6ab50d51ab2400008000107e4911ca7900000,
  0x8001c916ab14ba3b00000800094381cb86f45400007fffc42061e48c6ac00007fffe793fd0af4b8c0000,
  0x7f14ec120c1bc2c7000007fffd62d6f6e1a9b00000800d19ff52fd0d4b400007fffab478539911f80000,
  0x7fffb950bbc436ce800007ffeef5784bfc51a0000080001f38b0bae445400008000db12ec1b10fcc0000,
  0x80002aa25937104ac00007fff7acde6d67d26c00007ffef1bb9406e45c000007ffee70c01f838ae00000,
  0x7fff1da763b0070e4000080008b28e9a1e3b2c00007ffffc861ac0259ec00007fffff3029f9ba5840000,
  0x800275a12e092013400007fff2fd18d63eed7c00007fff541c8fde454d800007ffc9fde031a617000000,
  0x7fff4b473f776393c00007fff7bea75c952b5800008000102f512076eac00007fffec0c4aa9433640000,
  0x80000af1112f22fec00007ffffaef12094d26000007fffdbe25b58702d000008000450a7bc103bb00000,
  0x7fffe26a104c6a2cc00007fffc5d14d06aa3a40000800323ccdb24817840000800971fe11c8f8b6c0000,
  0x7f1aa744fcb6a63700000800009894de1caeec0000800009fca1b8444840000800090ff0e7d919d00000,
  0x80009a1ee409ed67400008000a0546a785075800007fff000d5a073edb0000080006d76723d065e80000,
  0x800011ea851ac2290000080001c2f42ea2b1c400007fffefb214ad7a8ec00007ffebd9c40f0c9a480000,
  0x8000844f9df1652800000800313302d6b9dd1c00007fff3118f62c44dac000080003b0a3ecd7fc500000,
  0x7ffff38c62c52936800007fffa40969c22a0c000007ffe6b97d59b1b9f0000080019354960dd1c680000,
  0x8001d879db10c38f400007fffd9d17e6f3d80400008000117837ad6d5880000800042ec87c09712c0000,
  0x7fffe343a77618850000080000e3c4566f3b38000080000a971c96fb730000080001a7de9cbb0ee40000,
  0x7fffffebbba6501e8000080000c67ac10192f000007fffeef36eae50308000080005ae174fab13cc0000,
  0x8000ed35e52088cd800007f1047d157db1699400007ff1f8e396342f47000008000364793a0c9ed00000,
  0x80008bef14534aca800008000067f09be453c400007fff03ba3fd27453000007fff065ef0014199c0000,
  0x80002e05c113a689400008000256a2604b494c00008000be60a4b914fc800007fffb6946aff25a1c0000,
  0x7ffedda07ff7463e0000080003c554fc3a2c70000080018da5ceec7050400008001befda284efc880000,
  0x7fffe1e862c17729800007fffe7785b1fc94d00000800071c23224c21c000007ffff334a34f73f180000,
  0x7fff19e6418a017000000800001d85033081e400007ffff88d0cd8982a0000080000f42879d6be880000,
  0x8003c6d91a5229198000080001376b0c974ff00000800042e058db9ffcc00008000356ed2fa5b7680000,
  0x7fffe8e554320f51000007fff9ff8b844c8b880000801148b2e1b1e14200000800017f366d42150c0000,
  0x7ffe0ac538277de38000080007d1f61fc3b3a8000080022dd17ffc26fd400007ff1f95f7353e06f80000,
  0x7ffdbe783d14af95800007ffe925cecbae9978000080004e9c171da97e4000080021af81422808e00000,
  0x80049c8131f8f167000008000e2993ec72213c00007fff4ab97c204cf8c0000801929cf001d03e740000,
  0x7ffe5ab5babafea2800007fff2377556a80f0800008000ecd7e16f257cc00007ff9482361590287c0000,
  0x800160bbf343e102400007ffee3cf020e28f3400007fffc2d2cc4c35e3c00008001d3aed3addd11c0000,
  0x800114f39fc80c5c800008000cea6eb449ce28000080014b00d97a90614000080014c70d541889e40000,
  0x7ffee01876630126800007fff95e10f2f0d2f000007fff57466ba74bc8000007ffeb9e20c9e886e00000,
  0x800021a40183c46cc00007fff74bd215f4091400007ffe4e0d71748694000007fff269c91411cb080000,
  0x800336f90e728a88c00007ffeb8e2af4d955b00000800003902e186fc8c00007fffa603b91f027840000,
  0x7ffc535723afcf18800007fffe1de35237321800007fff39b298e9a565000007ffdb5b36bbd3043c0000,
  0x80011d22e995cd48c00007fff67a9bc41ce39800008000c64aefa88f24c000080023b7fbbccce6040000,
  0x7fffee95ce0f1d1080000800086245152e2f380000800059cce3ec8646000007fff78313365cf9040000,
  0x7fffd1c14d5fc4bf000008000054b46e7b9568000080002d604624159f800007ffeab5afb4915a880000,
  0x800077423d5e9842c000080014ee91ab7b72e000008000244d073a8a89c00008002019854d90dc680000,
  0x7fff1ec650f342c2000008000e6cec166354e800007ff1b74e6e02e257400008000b4c03c877a04c0000,
  0x800015f131d43ae5000007ff8c53d7b3a3ad8000007fffc10bb852fd184000080010fb6dacf1fd440000,
  0x7ff8c9db72b67f10400007ff9438cdbe1f624400007fffdc1110bc198e8000080005566e84b602f80000,
  0x800031508747c46e400007ffffa64b48fbe710000080008e8b7c6ddaa0800007fff9882c852ff55c0000,
  0x800075bced3e0cb6c00007fffc03e37f6005ec00007fffa2229bf00cc8800008000132096289ab680000,
  0x8000f75aafd8af8f400008000b2d3db40f7c2c000080014d934ccf0c2e400008000877a74ba7c5200000,
  0x8000bc78a8501850000007fff044c9d6d924b4000080012996ff5446d8800007ffe8b7f33b4a1ce80000,
  0x7fff7bdee30174ee4000080002217724c202b800007fee6e4124731ac680000800b8e63fd90aaba00000,
  0x7fffab4af2ddb14840000800007090035e622c000080005f84a14c7d7f400007ffff801c1fd447ec0000,
  0x800352a09aa7c4d500000800385802f5eac7c400007fff8d9afb43cc48c00007fffd8c6e0d66c1b40000,
  0x800056edcaced8ae4000080021a5719b7e474800007ffc0ef409fd34d7c00007ff7ac32851b0401c0000,
  0x7fff4a19142d622340000800075cb2f1271f8400008000b2afc39a9eeb00000800069e3dda9739540000,
  0x800007d190f5301d80000800018b5c80d1d59400007fffdd499f22320f400007fff760a4c257434c0000,
  0x7fffe2a1e75a123700000800ec100b857d15d000007fff8c3a0c6f1fd3800007fffa75cb39fdad940000,
  0x7fffb6ff248272acc000080001466211e3990400008000b5d462e495ea80000800034de1a9d4d0600000,
  0x80030f8b9ff90ee70000080006d02c7570fff800007ffff685c08a0c6900000800068400a4bda1bc0000,
  0x8002152b364055ad800007ff97b09d2ac2907000007ffbd0bd48776ea980000800789ccfa853883c0000,
  0x7fff8e6790aaeaeb80000800313c9538e137d80000800081579996845b8000080014a601a0283b400000,
  0x80004e9543c56bae800007ffffc806006494c000007fffd25685602f11c000080001b8fae49c08940000,
  0x812fb814e4b177ce80000800010d684b3f5720000080002984402015b2c0000800168f1e0ff93ef40000,
  0x80018b7f88aa7e5c400008020551f62037caac00007ffc3592af380a4280000800814928d07cc8600000,
  0x800382365a1b9900800007fe104370c5c73b0c0000801ed535fed410e3000007ff3eefb79ca27d040000,
  0x800035c7c619b5c34000080022f945dde5eaa400008000441c31e17ad1400008000237404be53b740000,
  0x7ffb83d33b436056000007ffd69073bde598bc000080018cc5a9da49084000080001ccbf8c3f82d80000,
  0x7ffe3d1b50097fc1000007fffeecf6c19a50f800007ffe08d9e31ea00c800007fffd000e1cb746440000,
  0x82ea3444d84224d6c00008001c02e286b6ee3c00007fffe6b4e2579de70000080008868635ee37080000,
  0x800d085e73b9a105400007ff2b5093c83211b800008000823f47e0545080000800d44cf94c8d5ccc0000,
  0x800093df80d0492e0000080013b0f5d36f37bc0000800b0f0455b3d83c000007ffb3d9bbb5aaf1380000,
  0x7fffc7c9b73cfec7000007fffe46b8143904840000800180abf1fedc9b000008000b11893eb6338c0000,
  0x8002aa2bb9f025d3c00008003bc5fc11087bb800007ffee3e7ae9419bec000080008706dd4df52400000,
  0x8002a944d3751dbf8000080025b2b5d1e5aec000008002012f1fc8df678000080036e76b30db08f80000,
  0x7ff9980a909437b48000081962d44a01cfcf8800007ffd43c1f47428abc000080021f96dda4c16d00000,
  0x7fe4eda6e901ba7f800007feb1dd0cf2f8702800007fff48bafc44aad1400007fff6591b5443d7080000,
  0x7ffe0afcc61cf5658000080039dec4568f8b0c000080042740fcf6dff8400007ffd4231e199507440000,
  0x80050e493a33cbb8c00008004a5467b2c258e000007ff9a00f3445b4920000080017c78097d432980000,
  0x7fffbaaab72a35c0000007ffe7b074a170e2e000007ffcff26e0af1fbc800007ff9d835014e4f3480000,
  0x7fff3557268f76b4c0000800094b07b0f703f800007ffcd83fb81ed68540000800300a1ada52aac40000,
  0x8011a7b24dc26867000008003537585eb5813c00007ffb3b99020bde74c000081d3f642e47cbe3380000,
  0x8003a21dd8c706ff0000080032b0cfad0c0b8800007ffd2966d316123b000007ff3d9748fa43cc600000,
  0x7ffb707ce68395c0c000080018f5cb41f9ee7400007ffeff0d93726ff3400007ffce23b6639af3840000,
  0x8002093d8eb67674000007fff708f8638f4a7000007ffdd052110c43c2800007ffda1bab52c238e40000,
  0x7ffda7ed5a992a31000007fffddb5a8360f700000080006f882201b361c00007ffe744ef448133640000,
  0x7ffe56383dad1c15c00007fc6dfff0cdf942500000805753ab48d4c0b4800007ffcf7909d87f086c0000,
  0x8000041fa8c222ce800008000429ad223b852400007fffda9648bea28ec0000800234a73c046defc0000,
  0x800208c0a6fd8022c00007ffde7e46e3d905b800007fffe61472ef1d42800007fff9e67f299d802c0000,
  0x7ffb3f4fddafb536c00007ffa7f395fefcfd6c00008003d2b5f662e3dc000007ffd25a3980e1d2380000,
  0x7ffaeac77ee162edc00007ff255c965a5b9ed000007ffb5e33d396aeb0400007ff24ded9f90376740000,
  0x8001e5864d0390228000080021c9d8bdd5f64800008059f847e0da233c00000800e5856dc0d77e880000,
  0x7ffdf274ca3e8703800007ffd219a7d346daf000007ffcf992cc461450000007ffd60e3fb75eeff40000,
  0x7fffa2d7bcd35492000008000e55f75f7bffd800007fff6a89756dabb640000800045ccf2f1dca040000,
  0x800481f7bf14134c40000800d8226882438c680000800f4d896b970d11800007ffcd6133e9f49c8c0000,
  0x7ffafcf4084c05d800000800ea2cbe500391cc00008004fbf8895d9d67c0000800eb79647113f7140000,
  0x800022e8196062af000007ffecb5568bbeec1c00007ffbeecb9307c405400008240b0d8001ff72840000,
  0x80000ef2b4b8f5adc000080000558d4b04d39000007ffec7f77afe395e400008000d4abd4b13edf80000,
  0x800a6b0ec9123fe44000080007b20477d46a7c0000800209cbcb6f9ae5400007fffd25f48c4739900000,
  0x800f777fbd4b611e800007ff638c23cad654340000800ec11c09858f71c00007ff61d2de76beb0f80000,
  0x7fff74a806b165e7c00008242cb4dbe28f72580000801097266944b6fdc0000800b7dc2cf82367700000,
  0x800034d1fa8fa941c00007fffbe34d99548704000080019bbc757ed5dfc0000800219c7be8965d440000,
  0x80042d500d4f04f3c00008000e4c71e5d1b92c000080015e88ac5fac66800007fff04007eb92f3ec0000,
  0x7fee4649ef5d8b69400007ff6f2c29698800a400008010ab5390ffb1db0000080101bd9c3ad41bc40000,
  0x80787121d63611bf800007ff5f93880020f38000007ff0c1f21ebfcad7800008009640f5a564c20c0000,
  0x7fe43d416c8b2050800008010207a9cd2f84e800007ffa9317c3ffab370000080033f8a5306e9eb40000,
  0x80000d343a7e6657c0000800238e0272624b68000080071cda0981c978800007fe7b5903ca83c8b80000,
  0x7ffffd8bdac230c7000008000208ecf44395a4000080015adaf7101cd98000080009eb9d6ebfae540000,
  0x8073f7f87a1982b9800007fffef20f8fa37b240000800010172a53730d8000080003578513a0d53c0000,
  0x8002f58cdc3ec02ac00008002a47e2879a3fe000007ffa6860164989bd00000800d5879a54d6913c0000,
  0x7ffff52f21e9ae52c00008001f6c75311ca49400007fe6e453c99a9bfb400007ffea17608ceddf080000,
  0x8000585d16bf3289400007fff7c478295c73b40000800011cdb4efe75f800007ffff6f913aafa4bc0000,
  0x80035c1ee468821fc0000806f0469d5c24f28400007fffebfd11c4f3b2400007fffcb2fb969928fc0000,
  0x8002626022e819224000080183893c3c92710c00007ff98aae12f36d03c00007ffd57816f4905af80000,
  0x800008f93267e88a00000800005837dd1111e80000800018013cb4f9dd000008001cbec6f57db1fc0000,
  0x8000ae6be7e8ac5cc00007ffe94d3b392ddffc0000800007330683a797c00008000f9ccb72526cc00000,
  0x7ffdb0bfd9d82b4b00000800324a26a670742c0000801aeac999e31f3a00000806ef76e06b47a0c80000,
  0x7ffecc22af884cb3800008000cf141851caba000008000598cab452d5d800007ff96a1a6cecbdb600000,
  0x800001f75cf24df1000007fffc916afaa63b94000080001673a0225f1bc00007fff86fd203d0f04c0000,
  0x80020569d583ea5dc00007ffc4f2de4ac6aec800008074b06d79815b00800008000086cebaddaf080000,
  0x7fff4755e7931a4ac00007fffbdf9d1a6bb02400007fffdff907bfdc7f400008001ac93d7beb188c0000,
  0x8000013875d798cd4000080001b09fdb641964000080000bc912dc3d64400007ffff8ff3a5ad03180000,
  0x8000fe7d3a518d6a000008007e30d71223a1c00000807d986d32d5365c000007ffffdf28125509100000,
  0x7ffffffcfd94405680000800036f714840276c00008000860829b0faaec00007fff6acc33b26b8340000,
  0x80017b0be130aee0400008000053f21b326cb4000080001d734bc67545c000080001817d1bee134c0000,
  0x7fffe0585956d92b400007fffb9034aa75472400007fff619142082e3ec000080836b12b80d0e7240000,
  0x80000e94e166253b000007fffe5e231d3e145c00007ffff3fe95746490000007fffdc9071bcea0d40000,
  0x8000ee534e94b069c000080802b36b83e0e33400007fff8a71496962d1000007fffd1d55871582080000,
  0x7fffe5e7973292cac00007fff0f06877209ac000007fffebd27c6af9a0c00007fffeeac4b990c5240000,
  0x809edaa2f7c58d6ec00007ffff9e0ca810981400007fffda205eed4ee6c00007ffcefb7b913757f40000,
  0x8002b723ae1f6dd8000008000930d579b2cf4000007fff5901b2941ee9c00007fff247a1c6def6c40000,
  0x80fa5106511b44c000000800016180b80382fc00008002e6d3ad0f4505000007fff3df4bc9d3a7d80000,
  0x7ffc9527dcd2c412c000080011830fc7fccf0400008000281c01b65638c00007ffa3506ee411a47c0000,
  0x8004007ecbf8599740000810d209470b01e1fc0000800004b6ef8afde28000080009e8f18bf5be900000,
  0x80036196e11b956a80000800140a73bfe4aac400007ffffeea2642a8150000080007210c103341740000,
  0x7ffc5bd7a09bd726000007ff8e0d83dcda843c00007ffff5dd977373d38000080e9a4438c24172640000,
  0x7ffbace5584c77bf0000080041c7c20a51810c000080f67e095ed2a9a2400007ffed1e307e4a8a440000,
  0x7fff7be16e3afcb98000080001008b1ab7d094000080fc631615598b35000007fffe525f884242700000,
  0x810634403f6bbc3ec00007ffbc3e6a0a5a7030000080f76b8a965b24a4c0000]

/-- Packed radix-`2^84` upper-triangle words (`+ 2^83`) for partial Gram slice `1`. -/
def gramSlice1Raw : List ℕ := [
  0x7ffff597918372a84a5e98032a7e1e367efa364f66800068c5e8f95da2287227fcb905f472fcae4bf0ee,
  0x7fff405dc4d6c8760468380005a9260061e6023b417fff65c5757fbb6ba46047ffff1fa8f4450c3a311b,
  0x7ffff2b1f82de8f7e58c48000d3ef5461f1d9229817fff7f9e1575ba0f3f442800011881fc72ed5845ea,
  0x8003fda42135b63800017800033db7697a18c399027ffff4c88852925d575768000048674c00cbf49ca4,
  0x800084ddba8469b6e5bca7fffe4fe512ddfa1c36e37fff34775d0202cab29f880004694d1e96092a6256,
  0x800003cdd8b28f9f1bc2880000902708109b31850a7ffffed237e9394c3f68c7fffd98290efe565b4608,
  0x7fffe48c0b1a2dde495857fffe589c0326b0f86a878000151c96cc85575ef228000c5efa084a8bb85d81,
  0x7ffec063f111558039dab8001f4361ac7918b05c507fff23a2074534eadacd27fffe6961aae419dabfdb,
  0x800147769ab90591be8f28000ccf1e8fd636bda38a7ff82abc63d7b7adce21e8000eff3954196256d33c,
  0x7fff86d97a233122dee348000b9b7f0e96c44af0a080017905c925472a2a9587ffb9060047461f51bf36,
  0x8000936139de527d572d17ffe98f3f7e84e54d32397fff1409675c678ddd5cb7fff9f3d2f24f1756b1a2,
  0x7ffef656b748af390e5de7ffe43fdef8e828999b6480047905e55724ef491bd7fffc4feb9b0c5f721e92,
  0x800022b09e03f6a96d0f57fff9d974aa5ca4d2de6e7ff7b1f029df282ac3ae7800095beec1a4f8e592ac,
  0x7fffc6dd860384367c5c280000cd5f4301a28fe3877fff897f5ab154290826f7ffff3b50ac32d5d6c2d6,
  0x80007cafcb68eb380e6fa7ffd1d24ec7f3237b21837fffe1b20d10d2eb7b0e67ffffcd5dcfef05e98115,
  0x7fff62033b3318cadaf7f8000171a007d02bb965c080004dd4782f033eeb7ef80001b65e30d2f66e0d63,
  0x7fffc89a2fee9e91c7bd6800109cf13dfb289c47bf7fff52b0179b2c6226ac47ffefe0effe9fa2e0b608,
  0x80000ca153ebc1e093a887fffa154bf577137c29e67fff673499d9337db88857fff99de77caa70918503,
  0x8000229c1c5a7be39a1cc800010de8b6385eb9f21f7fffef242639f08a792367fffee816b692e4107f29,
  0x8000596f7ac83d10457977fff87417688b15d0bc568000065186256734e790d8000036639a1c5454ccac,
  0x80008116c72f6bd0c95f17fffac77c2569084d80a67ffffe3065668596029707fff51c8c399cfcc67110,
  0x7fff971dee81a19224c6180004edad7c7ee328b2b880000bc5e9c844e93675a7fff9e51195b261a65ab9,
  0x7ffefc262b52edeecf2f1800035bd099c55e7c407380002bea3722185d9ac90800086a2aa46ebe0d0428,
  0x8000830aae6c4f4065c26800007b40be565465174d8001802ab6d9c5d2f4ed07fff3d9d294ab9910e1da,
  0x80002164b88477dbdbe238001bb8e1323007975958800028458ac8ad27adaa280012acf63b9e138db498,
  0x8000057c73077574a47f77fffff985f2ec309aba1c80000822b56154c1d2ab1800016c7ed37c6892becb,
  0x7ffffa2272ca3aeda777d7fffe55a173c4db1a5baa80001e4408fbc14da47e07fffb8ae14e8c06e5c303,
  0x7ffff00c7cceb33c0400b8002369cafc8044edca14800072b447f963de9bf4f7fff72dc6b56ccf1db203,
  0x7fcb27bb747619731cfcb7ffe44bce1f707ff8e38d80004432e6b2ca77407577ffe209baac830353db4b,
  0x800053b662fe94b2884597fffa4628721fb43355e67fff5a04d7e4ec3c283187fff24b1e91dfcea1424a,
  0x7fff61b4a5209f22d9e3b7fff1dd4bba55c38abc4d7ffff9d6a457fbbb252757fff8071e64c9fa019ae8,
  0x7fffe1051a12e7faf02127ffef7b81e1fa96db697c8000fbfb9182c78714f6580008087f530118a718d5,
  0x80007e15254f50ba25b74800065a9a453b5d037f7b800004a6d0030af33fd4c7ffc7bfb7ca106516995b,
  0x7fffe8678fdc9ec70cb8a80001b88224967fe5e80e7ffffae574d991f4d5e527ffe7c4093c25b98e9e85,
  0x80000370bbaf4ee4813558000035ac490e72cbbf627fff4e4fca2e3cfcebf7d80000e22605f4d8391913,
  0x7ffe3e3ecbbb2b6b1589980009db39cda3b9cd00fc7fffb491156945e4233d080000883fb73e463ed044,
  0x8000a2810cad63180e5078006b334ebfe9c5abde5f7fffd977a06b6692209af7fff9245bb606e26d83be,
  0x7fff79f6c3ed943d7ffe780007f79fe9012644b3cf7ffc744f425529a4c406680008f7090b076955113e,
  0x800121ffbb1d972181ad17fff0b4a7d654026bf3bf7fffb5042a4fb7b82cb217fff3bf866148f99ba373,
  0x8001b95e1feb8bceb3fec7ffbc28177a6ec2ed35a28000040b0413da7e0158a7fff5ca54a70ea657176d,
  0x7fffd61baceb6f9207281800a2f7295e0b1403498580008f0fa9950b951ea3c7fff3779af46efce37dc1,
  0x7ffff086b4f8d30507f808000465fc0d5394e2f399800007ec1f20c98177e018000080e6d19d3f4cff36,
  0x7ff05ebf7e6a7834378127ffffa52ff854a966eeba7ffff41d17b5bdcc821a37fffa8a8a21c9dc01774d,
  0x7fff21026e9741edafc027fffff76f2a382fd8fb417fffd08a2caeee7f109917fff9412fdf0f362e16c9,
  0x800041bde2152535b3dbd8000550d17941825c0ea97fff9ef32906fb3686b4180008e251d45b9f057df3,
  0x7fffca24127d375ea3de78000317c842cda2b96f297ffe8ef0dc33bfe4128c07fff80a1ecc18dd6a0f7b,
  0x8000055c607d4233f5b2e7fffe4f3957880e5349ba7ffff3d06ddd4bf769b5b800003aebfaf2936721e8,
  0x8000112569a77d200c5db7ffffeb14c26c6b5f402b80000095b013376b9a29b7ff48b6f822c24c422259,
  0x8000746d36162171b9430800050821753af645228f80002e34a536a1cde9b1280000ad762d98f4cdb88a,
  0x7fff9b0db6fb109164d8580069cc074c6559c2d9d07fffdb63ea754ff574d5e7fff82271bf923affb66e,
  0x8000b12843824ed96828a80016d1fddd7672303bd57fffe9dca274d2b0a664e7fffc387423bba0eba754,
  0x800127f6408843a7da45d7ffcf847f648b7d6b837d80008a8fc7d82d2eb3b1b80002842ca73f4672c66b,
  0x7fffc1fdf5f4ba90e6d6f7ffff0d1330887041d6297ffeefef95647f4b02bf5800060a7871838443284d,
  0x80000d5df8533b46307dd8000041264d6e0c4495fc7fffd0b8d3751d4cee65b80000a8edbfd510e59b50,
  0x7ffff82805882e91353667ff48eeea7d888959acd58000ab0bd9a12e1fdacf28000628240ff36855fd1b,
  0x7fff9f1f85256fd97182a7fffe4e0551eb9a7129317fff6139a4eba6a7ae1af8000274c88215edd6e6c0,
  0x7fffda59b273f10ab31fc7fff12161a59bf76247c78000965ecd2fbc6e64fe77fffdef15fd04b343dd5f,
  0x80007f81c9fdebb5d70a47fffdfe5e60f10d26cd807ffff91841222816e291e8000bcfdfa3ce9c4cbd9f,
  0x80000397e7d896be6216c80003b7713b8a4e4397d580006945a0d690e9dc29d80003ced415206f2b623e,
  0x7ffff2f89b1c17e620028800013de29c6d0ad05c3f7fffe82ad17a13855b6bb7ffffde9d225ed0fd5f18,
  0x80001db292d97b47d4bbd80006e437665c36e288b77fffc098bf4e5829ca45f7fffd2e4b92f15e21b9e0,
  0x800003cfc21bf64576ac07fffd6c5241e4ed2a80a27fffa7c7138191a436f107ffffa848c1cdb3e5f1ee,
  0x7ffffe488098214495fce7fffc0ea88437499e1f928000245875aeb2adc6b757fffdaff6f3cc8425f89d,
  0x7ffffa0c7a746f6bb837e800001e1478ad80f264887fff7e8f2973dc82b94667fffb751c849a34e4576e,
  0x7fffe5cea2c713c309aea7fff42b02d876e7efc0e57fffd2ac93629341606437fffdeabb3ecaf840db49,
  0x7fff37d2504de69aff19b7fffcd8cbdfefc68cbe197ffe6cb78868c85146a0f8002dd6967ef65cfe13ed,
  0x7ffffdf3c8f467c797ad07fffe8c19f99aea2c15f87ffff480dd3b7148b449c7fffe031b624fe18e8f20,
  0x800066f84778addd05d947fffe877b69357f9c5f94800020f07f3193c0ac9ea800005448edd69f6ffb42,
  0x800048c3c6b5b683515807ffff5365ef914c88f54f80002ecf0445ca2110ffc80000a291f3a04cfe83de,
  0x7ffffc91a4ddad1a3c2087fffebfd7384549910413800008ac4ef75249f66ca8000067385f405bcbb3a8,
  0x800000bc30d35648a8b337fff60d6939585811e357800071ab13f6354b9a1b37fff0da727dcbbca802e5,
  0x7ffe17367206570d1878c8000785de7752a0ef80347fffcfd077ac38af579757fff4d5bdb5a52704db66,
  0x7fffea6708e722093bc9e7fff4656cbe18d21b5d638000595b9c9d1a89633e58000ffeb74e19122f61c1,
  0x7fffeaf7be216488bc2f4800007a9673e9686874747fffe2afb20eeb7650aee80000fb74adda9a4f2d1f,
  0x7fffef44cdb74a3efc16d8000e27d95289136e0b438000023dfd7c7e6dcd88f80001675a49b98327e283,
  0x7fff0729a7db497e402027fffc1fd4bf37bf5bd1547fffd831af32a662447987ffff5c0e1dd722ffc550,
  0x7fffdaa4e15e870950f387fff1d91b16a118f3eaa07fffd542e4896ca5c678b7fffefbb1e4f5ca913b2b,
  0x7ffd6c65751a3e1386560800057c1478ca574e8a817fffe8ec544e8a91e30288000eda376ef9b6f52d1b,
  0x7ffe8097d4e0126ccf7997fff92fd4a5c2edffb721800089ef92a8547fb00ad8001915b948fc950519aa,
  0x7ffffa09c147c7b0fee7880000df186d52509836947ffff9b3119a97d84a4547fff64847a56eed1a5cf5,
  0x80001720678a5e14818388000007f6b62c4cf4afda8000230a1004a2f7370227ffff29afc8b910fc10a5,
  0x7ffff5c21c748ac93ca6780003fbb27597c965920e7fffd79455d94f60264a38000649095ef0441e84a8,
  0x800003120c1d05d2891bf800054334a61d0628f41e8000077cf08c3f9b51bf98000808720c7b772a7286,
  0x7fff7955b91b4ef4b8ac57fff9e5aa3ad44197ba2b7ff6c86862d6b34e513fd80003e114a184552b3940,
  0x80000652cf0db42cf78ca7fffdb1e8698231ce1b147fffd4db8c607f2f66877800118a7b71ab1dea6f29,
  0x7fffe5cbec31e43bd00d57fffeea11c74629cdc0fd7fffec968a5ba90f93fd17ffff8508030c4c673504,
  0x800075c7dbfdd7c83142a800006457a14921d3bec97fffed1bb18114b27a0f4800008907f5b8f0acd7e0,
  0x7fff250f7682f7501a8bc80013f14c0d04a68a2c227ffff6b70c3a825f935678002737d561eb2d1c36c9,
  0x7ffe8c32d4007c75d028e7fff7f9e1d7c7603771517ff9e8c95dd4ddae8a3d07fffe5f6c00bf36c7e082,
  0x7fffe7a2002e4fc258cf580007bc0433ed7aa3aca180000e34c612d5e705b5f8000250aafff4d5672bb4,
  0x80012636da2011f13299b80008f486498b4d9964b37fffe7a4b939cd4dcf38d800011dcae443e50f0175,
  0x8000043c6a3b56e5c66857fffb6bd30fcb5cdaf9a27ffcbaec2c975d625c83d7ffee5ef0d87a9fbe0212,
  0x800011c54c7acf90090fc80001e6d8dc109ecfa0d180000ee1628d2dd61133f800286f1fd3e4b8fa8687,
  0x7fffe9b447c863dacaf3c8000431907644d9269e097ffffa1f955818626ba768000703aea4b38f5e64c0,
  0x7ffb2e5726f4b9340266880054cda79b58fd5307787fffdafaab4432bdade067fffeba31c2b984163972,
  0x80002b5680ce7702dac7e7ffeaf1f204556cc04bf68000041162d7745af8ae0800055a7544e54bd05db8,
  0x7ffba6534d34e5c158d3580010235432a29b4dda8e7f7b12ea936c2c66be4688000851be382fb4959931,
  0x7ffbd5d1e2b85ce531baf7ffe675e11f7ab18ada83800027c63365b6c9c8a127fffaa0ed9ff94ad6958b,
  0x8000672a61c91579c9c578000265e1e31fb1dd8085800017e89d17a932acdd480000212a2f58814a4cbc,
  0x7fff759abe42fec8544aa7fffd94400dbc07fc9fb68000287f9d31bf1a656e98000221c8cfff09b789c9,
  0x7fffb8d405a46cd3fbb2b7fff00019e691ac66bc917ffb55d807f7450b638e97fff9a9a314f41a024e23,
  0x8005a10133a32b1bd86cd8000f528c465fd9ba4a988009dc91222501e9f9bbe7ffff3faf196d3bf05600,
  0x7fffb062b7e196ca906a4800094202e1239a334a387ff9f156c6fa30f2d28857ffc3f55e0019394d394b,
  0x8001427ed9528c45ed32e80020a8071b8bee75b8398001aabdf98413cf0ccdb7ffe6d104c4014111082d,
  0x800006e0463fc46457e4e7fedd3354b9970d565a408003cecd0667778f33ea17fd98489b2a974d7dfb1b,
  0x7fffdf2ce26cbad61e5e57fffea58b7a1ab2f88584800025d65fb0a6dd44a0580001a0a4f473c5f5d902,
  0x7fffc7149b1e92c19f9318002dc20cfb85f79b63717ffd14f2401b7e04efcb6800002b9d41c427d451b0,
  0x8000a6edc2917bc08ba2f7ffe4df7609c6f0ceccc78000c7c7b539de1dc5c658000a91fe9bfdd2177080,
  0x8004f47061b5ce6f14ab38000fd41f97bf8e9c3f738000d13ecc37590310c0e7ffd98c7092ae6bb631de,
  0x7fffdcd3466e67a8d2d8a7fffb3207b1628f8b5f3b7fff7862f19ff8abd50d17ffc4c3ed8f181388df0c,
  0x80001a109a9643139560680003da95dad10b8229737fffa7db8e087e71ff0e180000e479c793dce2f8c2,
  0x8000137338f4561c582fb7fffff6f62f58769ae601800013e33476b69bd766e8000025c5997e920265a2,
  0x800247ac9e4785395e7b78003600edd3962655ae868000294f4f4ccf7e70e078000189307bdc81d11a74,
  0x7fff739953028f1c1d292800007dcfc15e58bdbc027fff4edfb31cda2af32d17ffeadf2e45803eac1333,
  0x800022013fb27a27d4fbe7fffab297ee2abec0452980006334773f957dbb71f7ffee0613beff62dab789,
  0x7ffeec230f7d6a1dba2c080005d24ca50602c8c49a7ffff027fe7d1313e88bd7ffff5be012cd01985251,
  0x7fff7f403e14e15882ea58003eb7580e865a70ecf07ffeb5e6053527af4e9528000477a712e5da90562c,
  0x7ffff8f563b28711ddc097ffff31712a828d88c8268002262c8218cfc08d2387fffa60e77ca9af749e71,
  0x80001add12396052dfa487ffff91beff6feeb6fafe7fffff0caa20ef7a205b080001753467db1babf5cf,
  0x7fffebd03d9d3ad765da37ffebc289f23775f05e187ffff8b23f4620b342fa7800004429e290a00dfd3f,
  0x7ffffcdfb2ab47d529e4c7ffecf1ad4192a63caf2f80011ad31bef78ff693097fffc2c60f510552342d8,
  0x80002042dc6bc9182a8117f5b2ffc13429eda923c180001c907e89f980b5f018001b3e9da594b2c7f839,
  0x800030420bbbb5c2926f0800196502c3c6eb18dffe80031cdec937fa5438d6f80003536412bfb33f25f3,
  0x7fffff64e72cb2b2d6ab77fffec5f051c3e82e3bff7fffeb45faed6957272aa7fff38b0fdda2e53e06ef,
  0x80002c7dda07fd8a34ff880001b249b48273d57be5800092164b36d018fde0c80002c4e0848232a13103,
  0x800080fef3a9fefa599108000be2ecc704237f1d367ffe253935e4bcb4f3df87ffe9228e0412f5ffadc7,
  0x7ff424ca46c480f9862868007005e4ffd21f93652a7ffab4e69a38784df33ec7fff7bc7dcc16a46352c5,
  0x8001515626cd04232e5b580008261ab5c18abab3ec8000556f3e8cb9ed2ad397ff928936d6fc03360f93,
  0x802d666069cdcbc31495a80011f1a0c19d88bec19b8003143e99c32fdca672c7ffcf0e21a8ca811acd48,
  0x7fffe376e6f0958c1629f7fffe862c9a84f60be3807fe8d8fca0fdcfdc590257ffc569889699bce68d34,
  0x80001271d6ab89b4cb3027fffa8687b9b2bab14fbd7fffe3a197bad5489e44a800035d3d0469b74c166a,
  0x8000da929ff6e6d9c95148000d38e3eb5659fdf33d7fff61b1397c7b9c1337e800058aa9700c7cb2f378,
  0x7ffeef0733010e3a11e6c7ffc6b646c12d5d80d7807fff4fb4518ef488114e08002c44d8b6ae425ac445,
  0x7ffd55ace962f6e53afa480007c2748343ac65c7f58002bbb61ea994019179f800606b888a6a8e5a8dad,
  0x8002a98b6335b5960ff827ffde9f4f16a0947a2f9e7fffe28c120f279b3a44f8000706af1997e741d8a7,
  0x7fff68f83b4f9fad3b76f8000a8ea68266939c895a7fffadc30c2599a4442d97ffea8aaeb833b7d097d7,
  0x80005e51361f974af6fdd7ffffab4dc03908802aa17fffb253d1966d4897802800664f7926c5538bce4b,
  0x80001d8c59d0a790491c77fff83d7b78d5cf759e5a7fffe370145edde67f7a280005b7e965e93e8b22fa,
  0x7fff1c5a4a9b956088f5d800018d33de6cc77d55597fffe6885140b7e039eb77ffffcda508208ed8e42b,
  0x7fffa1ea82bd8dcc09bda800692ece445d4b33d54b7ffdcc89959d1f417aa7e80001b135b39306087e57,
  0x7fffe13ba0176d6f38cbe7fffd01d95af83abe58657fffb337cb2bb8f276f29800012999d1ae3a2a557c,
  0x7fffeb04d10f877124ead80006083159929c4b8b607fff82470e096cf42bd91800036bfc0fadcb79f365,
  0x8000786e1256e0c6438167ffe64ab954fbaf737c0c7ffe8c14cbd2aab126a887ffe5c18601c91250b6a3,
  0x7ffe4eda1e7c80138d4c17ffc4333c42caf79de92480016a17362a1e1e13df0800014df60506081c609d,
  0x8000354c46cf0fade316480003a84ee7a5acd62dce80000306c79ff3903fe1b7fffde4ca631bdb9b0900,
  0x7ff27bdf8f799d9019b3d80003736bd4cc9690fae87fffb030af534026383758000147e3b8f8e1154351,
  0x8004f29ff7f4ad364cd018000010d728fdd0ffd3c27fff9c909c4bd8e6305057fff6c94acc67154df63f,
  0x7ffe80a6715507f0f361c80028eda9dd996947c2be7fff569bc90bb1a0e414080016df5b3de1033fb672,
  0x7fff7f167ddd92157ca427ffffaab11317f96590d880014eab9070f346712aa7fff5f1769135a98fe47f,
  0x80004006d27122bb884a8800863369613c5e7fe74a800008b4a91cd26c0efcd8000648cef7d94ea6514f,
  0x7ffffc860fccc5fdc5600800051c11c0660c0c918b800055c09c96fe58cad0f800006936fd6000777f49,
  0x7fff887f2b18b239e743d7fff223215018f2be50b57ffac1bbf30a758c1b24a8001997f9b6971b10e1ae,
  0x7fff5b9874445ffa501f87ffffb691d177239f19a67fffe798957dbe5c3f70f8001291c74e0228643876,
  0x7ffe934b9b1d3e990a5c4800020cf1a7f3b0e36bdc7fff881c5503426fba9de8000e1e0a27cedd8159fc,
  0x7ffc79dd7bfc59a379e307fffd26885380d0aa7b6d7fff7810a316c9c596225800013de53187544844f0,
  0x7ff8debba19658d86c3947fffde642ed50562184ba7ffe7b865b3ccd63c343f800106564c3df4d1b9ed4,
  0x7fffe9108cac1008f0e017ffff56ab4520532f0aa77fff9502062ccd206f04e7ffd02589d5265f89798b,
  0x7ffde0b814b749056a7237f64ea568beb967896a06800014e8221ad008fae0d800005fa1fd6362b5aab2,
  0x800058bb6a13ce5f8acb88000839dfb8f8272464d17ffc17338c4faf67b68587fffde5e921fb5cfeeb31,
  0x800012b712300a54b529e7ffffac1176e860917d887ff9f2da24c41c1f2692b800131623d4d6c53e1eff,
  0x800001e5faa4895af1c5a7ffda91c57878bbe215937fffcb8cf70b588ca3e6b8000022eaba235d9b2620,
  0x7ffb087b1128658096f938001ead32f76487a9908f80000688f910e40fc9f5b80003945b0992c084852e,
  0x7ffe0745cd68957c7ce857fffc3c282888c15f72e57ffcb0dc3276e6700f4d980100a9c16b1a9d7312c6,
  0x8007159bd186198d773997ff8c1f9e439da2dbaca98000a5e99b2edc7b00e6d80051b2cede0c7a313b7f,
  0x7fff7b86619cb4ffcd5987ffe82895053672373cf77ffebe239b69bcef0150d80065cd7653302a891c8f,
  0x7ff80efa69cd199a6f2f88002d01348cb5b0f1c5cc7ff70b5cc037fe5ad64cc8002a05698a916d4af477,
  0x7fe8f58dca4fb66c3f43a7fff181e493af3b3ae6b88000c2db3609b0b17756f80042d6a5f21fa8fc0eca,
  0x8003ea18e3daca463f72c80002266a3417311f03a07fffc89cd3ed48bb13ebc7fff6f360766ccf4bbf49,
  0x8000236ff4fcc43187baa7fffeb67e5b7b399009727ffed2254a9dacad0be937fffe3819e8ed5f52ac1f,
  0x8000a1d8e6b6f83e5784c8001af3a63a2ae3533cf77ffd36a8fa439dba9d1967f7caf5b1e69931a4ebb9,
  0x8000044c38c4e6d011f7a800275273dba13844553b7ffc226128d1d22bab5cc8003502faf38c4f5822b9,
  0x80003e0c1f96e26a1cf03800f82db81b2f40cf40d48000095ca34b6bc94956a7fffe73173a8e0c257f04,
  0x7fffdad10ce728124e9c1800f03b4354657325459c80002bce4bafbef459b2b800029e76249b5b639026,
  0x7ff8f8b9223c0c55421ce80031d72aa582b901b1f37ffe4124f348a39e7d7ff8003f87cb27fc7e079f9d,
  0x80095f8070e864153f9e17ffff9b0ed29945c55c7580034c7180225516970ba7fff8043ceb18b3cf408f,
  0x80007b88d7a17d68de7d37fff26062cff94d0a4b82800594eceef77ad7e1a417ff95da41881efd264482,
  0x7ffa70fbd970b0e8b3ab180024fdd457b4b6edeb437ff83fd1c810e9984c98480019b8eaa8e1682c34c2,
  0x802d207c5ca3ebfdf94aa7fe1d806868715154a95f7ffb9fef86001e2d04c868002418ddacd5ea124a8d,
  0x7fffed5af66787d4070b88000056ba78270089cd928000cd91b6968ba14c70480005cceef4e5e2165025,
  0x80001d93c3e5228ba58bc7ffff52a48115bd7e9a6880001acfabcdd3b494ee17fffea25fb053f476a85a,
  0x7ffffed7f66703b6c8a6d7fff4f14ca5c714e1d6dd7fd1e14cdbc6e6e16773d800964d7ac019588a1527,
  0x7ffff444c14668101d70380007b08694469702db5e80006e527ffa581a4ccd48004160f44c3f13bf9d86,
  0x7fffe9c7c85f33c037f468000508f742d85b02f3bf80002d87bc192b3ce78058000097796f3b4ca009b4,
  0x7fffe5652b27f3fd2d45d7ffff4a87d2298b981c8d80000b8e7904b0d4396a77fffd73ec64673865d803,
  0x80058cda07a5ba5030f5c7fffab4cf77cb3e7ac15b7fffc4cc7f602b34ecdc48000a77749dd2ba496f09,
  0x7fff437d37e64a773c7a5800008d3db0ec14c7b44c80000e420a607c4ddc7d88003227a49af1de84168d,
  0x80000da7e3c07cc05e49780005d344373e85cfa1a8800013d05fe658bbc08d97fff548748c04c7f3ebe7,
  0x8005f63b516a11c45ab7c8008e28617a61b31c21b58000e07d7277afa98131e7fffb93aa7f8970851184,
  0x80006875156a66eb1323f800194ac43e85d50cad6a8000b74c2dfcc602a0eeb7ffedc74408a7bed69c76,
  0x7ffffbb6196c7d27d46ff7ffffd02b0c75c8f019eb7fffcdc53132b9117ed1a7fff072b394ea9f0a90db,
  0x7fffcdf8ca68147ef0f7f7ffff57a0496666e499cd80003dc20a1b5a301f21e80000a8f4e7fdc6e1c2f3,
  0x80008f0cfe23a81b98be07ffd502070f0c7d7090667fd039a48b8b21f9323ca800020977033d48b6a4e0,
  0x7fff0d41a3cfe464736b98000394047146686e7efd80068b4078858358f7af97ffb56b71ea9648410792,
  0x800005c1ef803f983a2147ffe39f3f8859b7fffceb80003aca643d275bff11e80000bef7586757134564,
  0x7fff8179bec3c95796d117fff9fb25b919da093fe77fffb94a03dd3b1fcb8727fffcae41424854ce9435,
  0x8013463b5cf40990aceaf800342f7d01073d397be6800003c728e1dfb7d427b7fff74f4d89c495ba776a,
  0x7fffccfd97e0685793c717fffea953dc6a65797ab47fff8d30cc269755e45237fffdf53fd2531202f234,
  0x80004bfbddb425c725be880005749feead2e1f022a800074e27c26be8f74d60800018081032ce2b91b2e,
  0x8008a2fc6b3cd76c9a9907ffe6ad03a0f00ab6e2e7800528ae8d6ced0f37c597ffe5ac6be9e3272b37c0,
  0x8003568ca937c706f5b477fffe233eb9ed269953bd80019c93cad60ed6459537ffd153e4d27d6e3bafa6,
  0x800173c09abaf677a5e867fff420e04f8a8424b0748000481a74a95e1a1c0af800001c695026edf67869,
  0x7fffd4243dbee297274f0800004528f46c9f6e5662800036f2de21068cd2ed980000db413436f235d5b6,
  0x8000e030c0000ff762e927ffdecac631ca7ab775388000652c8861f4424e8f27fff3c5b02570c2d3151b,
  0x80002bbd683ffc1ff9181800001af5dd99292f71e780006ab7896af0c431ad47fffd9798149cae434b78,
  0x7fffa9ae0ecf8c287e36d80004dedf55eaf3f1aaf47ffffd839b0dacbb90e077fffcfa00916a068649d6,
  0x80001f70e5b3e18f168d3800007da939a12c06c97d7fffe3f02e9e8637a77717ffff434f6279108c0956,
  0x7fffd9ca7dddab6b5677a8000042c2c8291f3892c78003644ac0e79b9826a627ffec54736de7ee068c72,
  0x8000155462568f0e328137fffe20e75a646f60e9507fffdbeb308bfdd6d1e07800032aba5042853e4934,
  0x8000d027f980e0f9cfff380014b10a445717a687e97ffffefa0c64de657b94b80003cabaf0c488a74266,
  0x80021b758d3229ab842058000065e419fa9d69dfe18001f3bb15b0060a74d8c800009cd7564c4e241756,
  0x7fffb82234ee631d28c627fffd9212f951abc25f4d8000bf092f628f4ee53b27fff4c7513f78e7f10b2b,
  0x80000508c60e31fff18fb800003854fd5574386ff0800024e005503d9fb1db480003dc2b03259f721a11,
  0x80023da84ad52232520ea7ff7d3aa817b3d33dd6fb7fffcfa3ea5948d84d2107ffffd65a15799ab940df,
  0x7ffff0c383276144b49df7ffffd03db4af174a448480001d04cfca484c1c5287ffcb189e9ca5d8b19495,
  0x7ffff1905cf6889f8e4de7fff604c1cf86bebc101e80000f7d2e9a777afeb9e7ffe8c1166ea99db061f0,
  0x80004c1db18d1380e9f3b7fffccfb59c9b75020724800016f2a197db9ce44a8800123505beef3b5b528d,
  0x7fffc4897e9973eb110fc7ffcc1464ac3487bd449d80056aa89dad282be04197fffd6e2ce1b28314fc94,
  0x7fffcd6a14230ba07fb6d80008f6b81c7050ee6ef87fff342a83d5a1672705080000a721cb37b83853b9,
  0x80011a2bd19803b64b4707fffb8132db625aafdac07ffff592d8fa3c90de1628000089460cd4c074bade,
  0x800043a4eaea6ae341a278000f246301a9b6e015907ffdc4f5d09c47d2115487fff7a602fc2410dcbdff,
  0x80003f845478759ce5a0d800272e8a3448655dc8707ffc187d5043f5923abf17ffd78b8dccd41d117728,
  0x7fffd85d908f87fee80e87fffea9838f85bd8eda6580001257f2fc7095eeeeb80000636b4a5d570b5fab,
  0x7fe59fec28200f677dc367fff28cafafc2497f89167fff38d8373847505003580000d37ca344085d9dcf,
  0x800000c89c43490ed9a8780005823bb8fd82f26667800029e92916e7cdde55280004eae989e38bf2960c,
  0x80006daf09fe5794b995a7ffff52d8dbff9cdc90c17fffc6420bd785c86994780025076c648b732c31e1,
  0x7fff4c20c63556b07a3f87ffffd379513be96e9ef87ffff20451eaafdb234a37fff098b1277d6b0bbb6c,
  0x80009c127f7b273c96e6080009577a3bb1cf13d7277ff7c5d6a28a21c2b06de80001c8d1ff37c86cd610,
  0x80000bff919e97516d97a7fffa6ac69ac59a308b2d7fffae6eb0f89082e79d47fffc738a64cbdba208ac,
  0x8003fcd821ccf9850cdab7fffef0f6ffa8b0eda4798000045f9764762271846800011b593733f58f9236,
  0x80026a7e06a347f75d7e280002f9c128fca23ed963800177b5fa7e8e77859de800016b9e1cfd9d9c2e00,
  0x80000bc51aeece4eb79da8000f3caeb4a5c4f323a37ffd55292b46b4de68551800c4e3088be68f998ce8,
  0x800005e2476e94201e31d800030fc67f4229be1484800022a88ca8f1bcbc03a7fffb2571d7680a90e236,
  0x7fd5650843b49a94b90bb7fff8705bff2a7e911bd37fffecd860a77385d20c78000196ce03d8f8c1d695,
  0x7fffc1a13bdda3c3cbd18800095178ad47b085066b7fffe401fad0e4116c86c7fffa10ca8fc577aa905f,
  0x7ffff4c1bdf756a9d69777fffdf6cb8d2af7f4377780001e0fd44b9cd9aad178000a162ecea667825da2,
  0x7fff81c10feca9978a22b8000a76b0203ddd76494080000b37a186d41cd9d52800054c12b07cf9680ace,
  0x7fff941455e88ca6e94758000109ee97085a0034187fe9594bfee2cc52bc0247ffce93781d484e0e4ce7,
  0x80001d59d1a72d4fca2d0800017f854a2791e44e368000f9fc7007f9df0951a80000ec70a293489dfb4c,
  0x800a2a2f1ece01e6af5537ffe665903934038f19f87fffe9845b16f9a2d6d527fffdc43770e802d920b7,
  0x7fff7f354e6dd9874ef0d7ffd765694b3fa12ea3e98005643a2e27d6b0cfffd7ffeb2f0d879bc1f74729,
  0x8000158a7d190a58c878e7fffdf2cad64cb4aa4feb800d92d96bd15aea7fb887fff990f422ccc3a89c0e,
  0x8000018a28f37414747c08000a032f8303e3309c2e7fffaab5a385aa05ec5157ffff4d7f783ef18b19bb,
  0x7fffeb64941052909e5107fc4376c88bb15a7771b67fffd6bc4dc161fdafe02800037c20f79a69ce75ec,
  0x7fffe81a0cc30e32a5f307ffff85710d0744e674278000030cc52c6a12ca0f57fffff887f1d945d750e4,
  0x7fffba88b37c1dc44927a80000aa6099abd1091bec7fffd53cc8df6015ede2c7ffff72c8d3e3cb59f782,
  0x7fffe372210a4df1b339c7ffff2e7747d6a5aca2377fffe8b1842d5d98ed0c180009fd2c0609b6a2cf58,
  0x80006926dfd655f80b042800187f7ffa1efaac9b547fff2b1d3803a683f88737ffe9daca742b6f719a37,
  0x7fff0328af6495349198d7fffb282d542480d0848c7fffaf11ba17a0ba429938000868366bb0287ac4a8,
  0x800052fbab676c750ec0e7ffff785bacc1655c0bee7fffcdc902e38d1ed4af3800046782e90c5d748841,
  0x7fffe17e80ebe45163c898000144c41e9fa1ab88147fffeab162351dd66bfb57ffff356a5eb5f492b704,
  0x8000319f5a07b4562845a80002e54bbeed08094eee80002b271adf1fa4ade427fec7c0b3beb6d29e1b2b,
  0x7fffdf95fb5f659bbac7f7ffff383290b91683f69f8000200f737481fbe5e327fffeee072fc0becb51b3,
  0x80001fd65f1cf63f275e97fffa9808737d430d9678800007604fee26f0a72a37ff76cff58adcec0b37f0,
  0x80000222ed51bd1e227097fffedd5ee8433f43bf048001ef86ed685fbc070777fffff7f040f461a4b6c7,
  0x80000c04b83239e3513c48000588732e0f9415e7e37fffe104b9aed92c8b3ef80000aa5bbc20732842ed,
  0x7fffd76d2c4f0c84b75ca7ffffbd50ae85b30762717fffc2e594e9e62880f087fff2dd45e059ce055a00,
  0x8000ae2c7078522b99fd68001d155c937afb6952547fff6bd95f8e7d53deae080003cfad5158cdf3bd46,
  0x80000326cc7853a1bc3887fffee7a290e5f15e55277fff6d67a866dcb41df1d80002d8ab624fcfdd4833,
  0x800011361c5efa7446c6b7fffd436772e9ce12c9f57fffbb9549484b17cc8907ffd801fefd28df88e979,
  0x7ffb866fbf09fdcbbe1297fffa742131c936dc962f7ffffe07a1b1bc39728be7fffe07f1cf76bcc1f794,
  0x800000862dc8dadb044957fffdfb0df0ab584bd0ab7ffff48e72aeb5c9eb746800070158b2db6d8d31d6,
  0x8000119c940b9daca916880003921c078d674d50f77ff9cbddde1904fbcf5367fff9c9f9c267bf9974ed,
  0x7ffffab00a9a2bcfdd7b87ffffe3a94a6ac78923ec800004cf1cdecea7e71158000fdf220802477bacfe,
  0x7ffff24ca080210e2721a8000325aaa85b06057143800019cfb6db95dd9d80c80002a3c4ffb5bfb40a01,
  0x800016db25b18d6689b347ffff74ba20dc39000057800014e6d64d192461ece7fffb33c6bc9cce39d8ad,
  0x800013095dd6fc35829a27fffa628391af0e89b21a7ffff753eba97f0603388800068a42cab07f503621,
  0x800013a1d686e43994f7c800093d6eb235cde68aa27ffff950355fc3e3afc658000eb3567dcd7e90fa56,
  0x7ffff76728d1fefdeccc4800004ac42bf39310f0f17ffffa437c7da172e8f79800001b4439d4d4953834,
  0x7ffff76222ffb5c0c9daf7ffff30c66ad19e9c565b7fffe898dd4dd7c478be2800008aeab1865dec929e,
  0x7ffdf9821e14abf1bd5fd80007591d8dc20ddcfa5880003c6a4df44aebca75c8000139c6061a0ab1ed2c,
  0x7fffdff3341514ef811367fffcc1891da3e902ea4f7f2e7f7b4b2ba00aa8194800026c4e35aaee7713ad,
  0x8000a696b714fff05796d800028b3d076ea90d4dde7ff87db754825226822308000049a987292f17da3c,
  0x80000897e7c3c636a94e58004a4426a2db7e49eb717ffded2d6b43e42f2ef0d7fff6632352da992e3724,
  0x80008c6de93b0a46358167fff92f0793e697ae9b267fff27eb8e56aa889115d7ffe13d6bbd3704d8717d,
  0x7ffdeba36b35f996b34c67ffc4babcebcdad37a8397ffe45442e956d3273ffe7ff8c6519c797dd7eda75,
  0x7fff6558ccd7d2735db047fffdc5f26c036b7a85658000050471a563b3fd30680025695e18b68745401d,
  0x7fffda063464da0b325f37ffc124c96f6c1f826b587ffdb43c655b76dc47e8a8000df6da6682b65699f7,
  0x7ffff5d5f5fc7860f3721800063bcd4db6abf5637e7fff881de1a363bac6704800055a0279f5afcf96c6,
  0x7fff7857c1ee4f1f3ac9680003e53d0ea551a69ed57ffff791996cd2fa117377ffe743c5e01502538b86,
  0x7fffd9c5dd259419df63f8000236e74ae10e47d9927fffe23bac6ddb654cdce7f5d9c0f12bf9ce2e1eff,
  0x7fff484254795ffb055827ffeac2786a15a6270c1680012fd012d838639fe108008bd61496a156d70fe2,
  0x80003d9e84c2c210f2c66800124fc7b784609cdb2f8002025cc4ffd5347233480002e08710a181a195e9,
  0x800142b98485151f6d3b180054119d8521ae7289d480002fea9a6a5d8c0abb67fffa80e9b47c11a34479,
  0x8000774cd1bed71e8ab42800019152cd64ef0384db80012c854cdef905f69bb7ffc77923763bf59b1f52,
  0x800012bbae2895a2a6bbc8000373c635cb7c5c80977fff3e49d1664958762037fffeb84b9fe8ea895be4,
  0x7fffc265bcef445948a6b7fffae0e32cfc0366fd9d80007de1262d7f65fab117ffff267d8184cf390bab,
  0x7ffd5d00d8e3c2c67db3a7fffbd7828ffd9aa988b17fdd5e7e5888622d631a98000561c185d3aecc5424,
  0x800002cec43bdb0e14c1f7fff74c1c1c41162c5c4780000bcb3346aa187643780013b0f15fa571bc1a49,
  0x7fffe9482b49412ca629b80001b7bcca14abd83bbc7fffc1c09d0e6765ad0497fffd89f4e98872ca66b0,
  0x800023751d12dc43a63907ffff7693ec53a5463b757fffa25c76c4b60b383e67ffff940e7f5353373088,
  0x7fffec2fb1aa8befecbe57fffbb41aa97161876e7480001ec98c175aff3331e7ffff077e16b39e5602f6,
  0x7ffff4c8c9b20164824fa8000447c55b79a016d1f47fff366df67284644d5c68000236a4354515872f23,
  0x7ffffbb49bf956926ce30800003393722acad42eb67fff1baf58eac3263e3167fffe656e81c2943ef8f2,
  0x7fffd793d6b793a246efe8000007eba6627623af6280001c02b9a423e09079d7fffe6f06ed74b09fb757,
  0x7fffd9f6b839fd5621a3b80008a979d234a4ed49d57ffffbcc78d10eda3e3527ffff69e6abc0ee48129c,
  0x7fed4d07ad54011fd5a5d7fffa7719ec15215922b28000036f41ffd710933227fffc7c002260a0e4e4c6,
  0x7fffbb88702e167af4fc97fff6f0cc402085e6af0780002379afcc2a2250aef80000950b7d105420fb05,
  0x7fffa667324c89e45fd3c7ffe9e63f500af3b9692c8000cf11d574e83a267487fffd36e3b39ec677f804,
  0x8000d9a46123b9955691a8000aca98c361e6aea133800025350c1b1826c7db37fffd8495e16d4a30f745,
  0x7ffdcd076c2657d906e3c7ffef93ffcdec06035d5e7fffdbbfd0432f5a830007ffe3eb08d6367fee65ab,
  0x7ffff96b6e42efa7e9fd17ffce0008ca6de29bc4c07ffff4d4f0c051d7eace57fffd74392fae41e7dcac,
  0x800018283eff11499701e7fffcc74268ba1130f3cc8000327fd14b5e78ed1737fff8ccc8a0b6218e7076,
  0x7ffffb46cb32552674eda7fffc00a1814ae5b881ab7ffdd63c9932ebe18432d80079c65549cba8731eed,
  0x7f7f08ac5c197d75fdca2800003eaf4e8c5fd328537ffff0e5af2ee34314bb6800081349c37bca93f617,
  0x7fffd0b5e5144b2cead6a8000667ded927836e987f7fff8c7bc81b9f03b4ec280001ced1a641ec60ca25,
  0x7fffc90078462150692807ffef2fd30ebcb9979c3d800000b2c68b5650c72b57ffdcddb79e0fb9140c50,
  0x7ffe9675313430ea68ddd7fff2c867ba2ae6539a5a8001a914688e4a49b1c8b7ffe14ecccd286b099cef,
  0x7fff8153f392d3b8a778c80006d1d17cd4d38115378001e984e1113a99d0daa7ffe82aa309e105bb3e20,
  0x800505e4768bb275b990c80004c18a9faa7c11bc447fffbc1f6c61e7db88fb7800176e86b1a80e9c50e9,
  0x8000184dee4dced2307757fffa830ee7de873437b07fffc07a8b3d8381387647ffc37b9907a3f1f0b209,
  0x7ffff6e26726c7d128fce800051053a0317c40574a8000040222967d406dc367fff5bf2d085255c39505,
  0x7fff2b58120844f39cb147f49cc1f3e97a3c81f1c87fc92c69e7525797b52bc7fff8a2a146b0a093baf2,
  0x800049be367698b006b1f7fffff4da9d83465bf2418000f8b2892551d4d0da080000fd92209ad0e3d02b,
  0x8000790c04d88cf2198867ffedffcfdda6b765e18d7fffbc4591d73ba4689b07fff6899a418ab5e7afba,
  0x80022a2d94583e9b9816480029a5945450f1c4f5577ffe9748e5f9b719e90e87ffc7a33243ba5258753e,
  0x7ffffcf8f5589ebfde8717ffffd61ccb479fb386da7ffffbdc70948e42cfc7a7fffffbc29b108a786238,
  0x800050e50e5d00fbfcfa480001a01f2f6a287eb5357ffff1e11b21f15ea7d5d7ffffae1b1f60ed18506a,
  0x80009a34ceb8c211ef64280001f9906692cd599c8e7ffee19e4984e9a5207997fffab9eb3c5e464e0c92,
  0x80000408dc3f19276ee8b80008bc02b309cd0fd0cc8019dbcd02dd1b89b3bf07fff969eddc43e57b8697,
  0x80002813393048d8836d280006a347d4510e0d94138001e716f2dd6c873a9557ffe49fb727506ed6e9a7,
  0x7ffe3388f88938fca57cf800053091c9acbf6a02a2800001e93da6b3b715ebe80000213ef75e55913f6d,
  0x80056cc1baa3cfa99d6917fffc65a4b03e472707e67ffeec757ca263e18d657800177862ac7ee527b2c5,
  0x80000fcb43034d4386dce7fff579b4a43ebfa53da980005abfe93b9d64cca337ffe0931a444bcfe851ad,
  0x7ffebd60b453099459a7e8000bfa1dee85e219ca3480004229e5341963f86427ffff020e3ab314dcb693,
  0x8000479d60d85f9d378dc8000756cad23e0f9deed1800022a2c09ea72703aa97fff899e371d0fad4cb5b,
  0x7fffa749d23a0e8569a957fff68fdd0a415c0108c07fffff2c6d78e2ffcf32c7fffc99f93e7cead6c4f6,
  0x7fffdc80e2f221b86cb2b7fff1b025b40b04cb7e427fedafdab3906ce56d5f27fff1c710e32c38d5d775,
  0x8001f7e326cc5db3d735e7fffd03445f701771730e7ffc0b1d774f96001d003800119821f17f843a4990,
  0x7ffcec600e35a88c977e57fff36d0d362ee5c634c28002c65726d8ad6ecdd9e7ffeadeec58e5b5b04c62,
  0x7fff783065cee8eb0f34580017d4a43f9878c38c007fff96908156d7a27feca80005af3fcda0bb7699e1,
  0x8000c30fbe9f51fc39b487fffd273a6b0e9b1bc7287fff656d7f10f33d689b98001215f229b19722c4e9,
  0x7fffc65df5a96ee3f09dc8000710b855520e09e7497fffc315e6fe865b7307980025aafe4032213ec97e,
  0x800031cd69454e0bc67ec800121e90f924058974ff7fffee0371f4041c54b377fffc2e05b5f81a207555,
  0x7ffff0892bc40dc603f018000645a83de8313341307ffde2d59031ceee2292680007e548a5556ec7b0ab,
  0x8001a51259e28d129a3d07ffc4763e4ff043d0b0b58000cb9750c70602ab4bd7fffb49852cdb96559ff3,
  0x7ffdb4b91c15860b54e1f7ffb138e0503eb34c144c7fff0c72a6bd780e1c2e78000c981d3f8ef660ce95,
  0x7fffda617d8d6bdd786cd80002df56034f5b7c956d7ffff453882f0851f55ca80002b97e9015d8eb08aa,
  0x7fffd61024f804081a3967fff02c163254a1d34954800073026c4427db6ad8c8000419dab0fc8b52fa72,
  0x8000380c9f4bc7d7cc5b67fff8dd637df4e77a48fa800090110ff46a93ee0ba8000156a0beb51395f779,
  0x8000247226a59df7dfd55800029231f57c9d61f24280009dd24b4ef76706d7d7fffa7170244ebe4a7822,
  0x7ffff1d16ce5df4ee0fc780006ed7ba56dd8f12e4e7ffffca63c7eeb99933d37fe4c1646cec50bdb3d94,
  0x80000fa58540dbf4ef59180002475b63a6722f47d17fff4908b6326eb655cc6800069550ec001a023941,
  0x7fffd93e87636b5f09cfa7ffb0de86c385a713501080002b4dba74f680694438000852753f029e7dcc28,
  0x8012b499e86c452b8a55d7ffd5b3b0e9a833eb773f7ffdec9fae98dadd12d6e8002d16e0826cfcb60288,
  0x7fff5c47ab61a884ba99780003b63525e7bfeaa7d3800265f7c8c58820b031b7ffed0af33f20abd4364a,
  0x7ffffd0e4fc0e51a2d6d47ffff1fff1a68046d76637fffe2d8342d23b41e3357fff8712b86b679372d6d,
  0x7fffec5f1780dc708c4aa7fb7006ef354e6fe2c7a880003a0eecd35d75cab2e7fff76e5c8f2731b393b8,
  0x8000081ccd7472a5118f180014485a914dc0a6c10f8000dd19796aed562b3997fffd8b21f757afb644cb,
  0x7ffc9a9416f1558960848800059bd4447b97bc40417fffe67b57fa873b68494800029106d113a1aa3723,
  0x7ff82de569a92636dad3f801081f099baf484bf8818004b78c585036d712fdd7fecae23fa7c37d205d34,
  0x8000535877ce8dd46e1ba7fff08e2fded393008a8e7fffd28f8440805a72aac7fff8e394f0a1b93c6483,
  0x7fff9ee447f4eb90e51957ffe055f6aca4fd4977287fffd3ee998c51a109885800119c2ae9fae8e645d0,
  0x7fef4d84b1c72dfec3a9a80000b24a244eb42669fd7fffe8e855370db29b8577fffacda240df7eb377d7,
  0x7fff04a6462adc968afc18000e70d4cf3500ca456680031ccbe7c00d5a92df5800175ac4ff5b26e0d861,
  0x80000bbe311d4472c60b47fff74a45ac7c832ba99780013f308b4d585d2fe9a800096a8456e60ed3a262,
  0x7fffbca81c6d6c5a3f30f80002fb716832a337b116800003c550a1e9279c56880000c318f9f6996a8fa8,
  0x7fffb55d383c54219369380013f3c90a82fda5bde17ffee8699d03c8e0ba047800044a5f787e01ceb8c8,
  0x7fffd81ca99a93e08e42d7fffa23af4134d54530a58000686965b7ecb65ecf5800036a79ae2f17caba1c,
  0x7ffc1a8df7c4760eb1cd9800014ac30dbb6f92da13800003edad8000df61f697fff268b060335eac541f,
  0x7ffe682802b1e530bd77980086bf7f76c61a4329387ffeedd72372bcc4ea57b800408269bc9a90fbecb8,
  0x800020c43903fb9f3cc1080000b78e9dd92d5a9da780011e1a4baf91e7a0ce27fffdcefe87e58ba21b87,
  0x8000344aa4777b0bd8f3d7fffe8c3cb5beddb328c6800024f1f03d76158bdb880000e11f4d2b41456252,
  0x800023ebced5398c268af7fffa03fd4d90a2caff618000cc6ed7079512fbd7d7fffddd7456b462a4f81e,
  0x7ffea75f37dc19fdde4e58000292ae98b69eef2bd27ffeea1b1b151b75c507b7fffe1ab720b4174f5c85,
  0x8007600f97c2c8fd4f0d87fe93d7627f0935b4441980009945776f09817b72280003c252c0606412699c,
  0x7ffab2beaf8c9ac5576ff7ffeb033f1857a5ff1fb67ffed041ba55c1d3be1f07fff16fa33dd01dc8e88a,
  0x7fff79c860fd8338af1508000a0c0154bdcbcc169d7fffbf2021542849d16be80008d939b69211f01495,
  0x7ffd4826000175e5fa7107ffb5d00f74861613468f8003e51e7e2d0b8bc567b8000da05d6b70257d830c,
  0x7fffbdfbcddc33fea5dbf80005102e22e79ed8b4ea7fffd474f10858cd535708000d017e247c8bbc44b6,
  0x7ffe6e839040a34d7799f7fffc87b8a374f931037380012ce578eaaf58ef65f7fffef8d5dd62b38fffe8,
  0x7ffe86e51cd595a57d8d8800025f124c4bfd0d81658001161ea0d7f4fbf3a407ffa399456b9090f5bf8f,
  0x7fff8c48c5a10ceb6ab938000a973e0c5008305fa07fffb7e0b4be12ea3f80d80044ec7d9144f90b1b99,
  0x8002d39e28c0d06c382b37ffe6473ec81a75e22e3b7fff9813452792797d674800069057b0d41a40c82d,
  0x7fff97914c42012921cf87fff0b6800376cecdced580007689819c336f7f7a28001d15b1f31cb0b7d8bb,
  0x800066f591d3bc3b1cb83800138213d6588507e5df7ffffb99b36750e2871378000e87631df2c73949ac,
  0x800335ca827118314fd11800ad01ee799e2bde4a657fcca12a35199872cd4f08001c69f6e89c0e0588a7,
  0x80002bf2e85f3442f2a1e80006eb2e6c17c6951761800071a380dd8f320cf187ffe5d6d86c92e15810d3,
  0x7ffe390e1b4139c4a1e9e8001283057dc0d0ed3fc980000396e21da7d017e5b800047c90714393182fb4,
  0x80005e3897f407e0ba8a77ffe8cb08efff28d9371f80009d0358e5ceed2b32e800195c875b67e13b118f,
  0x7ffefbbea765ed5aacf718002732f8a4ce091e9d5c7fff022ee342067b6c8b58004d7fd816d69c19ae1b,
  0x7ffe9c6d82495b3d9670f800134ac10a04f784c8e57ffa1054400ac027862917ffdaa54b1e6b36c150e9,
  0x8000349465059e687ebf77fffe3239f5d37b1f83177fff969f0e87bd9984cfe800010e3ec5dee4392cf1,
  0x7fffa35f888eb3381ce8c800047d49a9a5d210f0fd7fff9dc52e6ec2d55dcbb8000191e59e774836b13b,
  0x7ffec4e5c4a6ec0c1b2297ffdeb68dd8f0d755d0a5800223280696d67358d3d7fffb7680a4be2aaf0ebd,
  0x800031b719ee5ce6960177fffd9c2cad8f0e2f63c87ffec841e7d1eac295de8800069a1a6344340a4b0f,
  0x800003b9573366ebbcf0180000d003cd8b46fa07c5800038e7618f539b587aa7fdb495ab513656ba5b7d,
  0x7fffc622dd88c4323d3f28000344cac4acafee9f427fffe6e97d61fe59f0cad800019a0d3a824a5428d2,
  0x80004902b106ecb8d72017ffffb164282aa871561f7fff75edbe59bf5ec986b7fffefa8085d01225ed32,
  0x7ffc999ebf091724718487fff33392c6060f0ba2ef7ffacf7ef2131f6938d8b7fff678f156a5b43fe9a1,
  0x80004de98db31783b5f337ff2ada378eea3ef2a02d7ffd7f4d7db5e43c6c417800122e43cf845659f403,
  0x80003f7e24fcc89a290cd80005106cdf58474738627fffdc89a3022885f02d17fffd6a91ef4accf49db2,
  0x7fffc9710ba783206eeb87fffb16d51c7010bc4bbc7ffef5a724f91be4a84518000836c7c1a9ee9757ef,
  0x7fff109c05f20d388d3e08002a5537d8b958cd30617fffcf89e6dd740aa6b8b80014f477eeaa355cdcd2,
  0x7fee804269d8a100e2d768001dbdf7ce18b178ecc17fff55b924be548c4d6dc7ffd8b8c078292bc73a17,
  0x7ffcef14a66873ec4dcf580053da2596036dfdc8b98000a7ea637eeed35f28b7fff10209c72d3dbc6839,
  0x80003b16212b2e82101aa8000c1394e930dff9e3e080015429a0947466ca0258004cfa300aa5e700f2ac,
  0x8000028cfba9c47c8868b7fffd4a1ae1a0b798d6298000adabc3c6c1beabb05800206d28d1f711f8e77b,
  0x7feafd4ffadcc4ba0095b80009ccd3002c2e1922367fffef6a7e792e3e7ec9a7fffff5f59b627bcb1f16,
  0x800221dfba38125bff9ca7ffe6096a5b8a7b4ed4578003b06b8260dbc22d5718002ff909b9645d209b44,
  0x80001d1dff858656a22208000711018f68dd615b018000ee506d43c4102116f7ffdc63c053f8b28ab77b,
  0x7ffff3dfc496e4cb049c68000b15c33634c50a39fb7fffc4a81208eab2f11037ffff73ef0047f30ebcf8,
  0x7fff6957b88faacdf606a7ff8d97caa9222e097fed7fffc3fb5853feed966af800006ad6fca824152901,
  0x8001bfe99bf1d4aca57868002ced1a91ebd21cd06b7ffa091d9a725660b0bb08000897102324e9f1f571,
  0x800014a9bfda44b97d889800010c933efde709e57680000d31245cb78f0dbf880005db4efb474b3beb09,
  0x800046d06477190f0f7077ffeeaa607118a6bdfba68000060818c8585041b7b7ffff2888bac746f15755,
  0x7ffe80afd47b289b24ce98000dbe365a3976e7e9048004a3b221631642348aa7fe32fffd7d75c87c6ae7,
  0x7fff1a5b8b4eba5f9c8bf8002bd80d897ee7f763197ffff763e66781496634e8000eb37be96bf6fa6962,
  0x80000d1ae3785111c45a27ffff8e08ade6a34f0def80001050019671b9929228000c60bd546a94129e77,
  0x8001321c2a0db80b8fb7d8000c1d5338131f7688367ffd49c05c86563dfcb1c7fffc1111db108d10c1e5,
  0x7fffbd4c9f131bb501928800007618109663560884800017eb7b3038f195a26800042474cdedcc4f24be,
  0x7ffff7b3c155d4b55618d800003f26babb6a0756217ffffc267f209840d2b167fffbdc2323f221e8c94e,
  0x800180a7afbe2f21eb967801b7c7e7ef9f75d8efa77fc271a7cee4fd21b367f80005f05663a40aa7b12b,
  0x7fffff1712723b64fcebd80001d343b07dcfa077638000540bae53ab2ab678480009e54b40f35af4d6c5,
  0x8004ce9b56d31986826e17fffe19124d01f9ab66ea800008c10c6d51f180b167fffe6af426a8b2f6211f,
  0x7fffcacb41d14f5ec9eb17fff8e4a9cb5949b4b08d7ffe8ea989509bd5c7e717fd7c4aaeb240b2524365,
  0x7fffef2d60e7e770b548180000a0836a25e7935a0d7ffffbce7998229e2bb737ffff8c3fd4ae9449fb90,
  0x7fffe7b12410be92a99c17f9578f46bc06089449757ff9ef509125f8d7099db800026cb6abe015fe320b,
  0x80001cbfbaf588c791df380006dcb40c26cc07d1e4800008cc7d8f3d4bf12e580002e5854b13d6676f17,
  0x7fd169c1df4416039e80a7fffd53a2ead107fd26d880000306c920d881508f37fffae7902880d7c03a83,
  0x8000177796e4f2a877f1f80000b253bc72a88f17da800022d5960fa0a741f447ffff9c2e80a5804d0dec,
  0x7feff52efa050baaafc147fffbac59486e83ef171d800013076063f8f220588800069c9b25ba1f3c9df5,
  0x80006606205591155afc780000f95e965d8c1a5bc9800039014dfb3b6c056f9800175ca632e11872fb35,
  0x80003353a029f472bfcd37ff4b671eb775828d754880003f52ab4d3598695e980000742130a1dc9f22c7,
  0x7fff8ea0ec729ba04ac3f800009b11f8986c3d5aee7fffee052596b7c0ef3bd80000499a176550bc313e,
  0x8000a95354751ac6856738003659aab5e858f580077fffaf56b708bc93272f57f614975eef0a6f5de513,
  0x8000943dc38efffdd5fa680001ed68ed9c658be0d37ffd040e7f5d6779c1da08000454d80e54882f26f1,
  0x80002e83cb9f7487448117fffe65ead875e5761beb7f586478a099e8635520680000b32a93b5c22c13e8,
  0x7f8413186c0a51de48f957fffcd1981b300027a5717ffe9d03a3f2ec708b1b1]

/-- Packed radix-`2^84` upper-triangle words (`+ 2^83`) for partial Gram slice `2`. -/
def gramSlice2Raw : List ℕ := [
  0x7fffbb3319f943acb5d347ff18fa0d723d3e83d0a57ffd048d44245bbc0037b7ff419981188a23e78fc3,
  0x8002e4057df8e327c817d8003b0702d18c65ee011380002b37d005dcc56188f7ffdc208a6411f39ade40,
  0x8000b21577cb1a4dcde3380001b4907bebc666bac880024995524882c869cba800198ef93b3b96e3e774,
  0x7fffebf2430f541e8a8e180002273c43f604cb27967fff1ef3f230acada46c47fffbb93d456b84eb76c3,
  0x7ffed7c10a2da1381705780002f6e9fd77137ab5968000159f3cc397093d35a80003260bcbfaa566bb21,
  0x80007fabd8226a3615e5180002710dca1b49b63dba7fffbb815831923e3e15280002dbb784f8d75caef3,
  0x7fffed7511047f2e778947fffe716f7b250f1336d580008bf8fe9dc893589187ffff97bb5214dfe8ddcf,
  0x7fef9047d871b2105f20a7fff69ec3e9ec925ee32c7ffd0c7565b1d355fdc207fff6a079148c931975b6,
  0x8002ff0c955397ce7d7238000720a0d7ceb2122d4b7ffe8b6f63905b0ab738a7fffcd8e977d13e74f608,
  0x7fff0f88b577000b2cb54800119dd06e4ec118d36f8000f1e7b153e5b53c00f7ffe90ffe5f63848f4b0b,
  0x7fff07602a15ea5297fe880001b4d45de0ea923acf7ff8f9b03e9271d6cde0f7ff4554911ba1f76451ea,
  0x8000143fcf4e9c5c7fbe27fffbfaa805c43deaf2fe80001754670503ccf358d80000074a8f564c37b76d,
  0x8000172535d1f19c02bf6800032325549ad9b22d147fffe4768e001c7a9e0e57ffff166dad0c5df7d9ed,
  0x800076c1b6c832fc827927ffff195578adbb7158ef8000756d4871643424df28000832fa269894db45f9,
  0x7ffd0e22c0d0c2306bd9a7ff4dc5b14e68a75e19908000421782589fe691ef87fffec46af15a6426fe9a,
  0x7ffefed2ed92ec6cdad08800051d8af46e75f4ace17ffc84efb5b40ba5a6415800148dc41a6a4e4ab591,
  0x7fff5004804871fea15e180005c6c326324911b4f7800367e899dce73191b7180000f528c84b06aa561c,
  0x800022518de0c0faa6e277fff90986bfd0d30a92547ffeff84b9373500c6b1e7fff77426733e1f433443,
  0x8000a5fc6b7bb3baf27ca7fffee272bf8668b163f27ffff283ff85d9229591c7fffb6694cdaf7635d162,
  0x8000f2de0fdf78c95acc27fffbcc6cb756538948e67fffc2f4fbc880ae093458000298fedaedafba4129,
  0x8000d8bd36e91340fead280006414824d7f0699654800004d60cb69dcecce3380007fee268c4ce4819f1,
  0x7fffb2f3548afa3f6ab6a7ff97028bef5f185c071b80007ef73ecdbbc18c2457fffa3076c6d17d7c1d5c,
  0x7ffff76f6103d42e702367fffe9f8e3737b86c42b4800021ad86173010743d580007de119800e0975f68,
  0x7ffdc1b04f452c164acf67ff8e1d69743354b8abc980007211af9cc1b7c35637ffe0deca80681f200321,
  0x8000199e86fbbc2bcbd927ffda6af1168d734245427fff2897942d4e5e2c43c800a3cdf344f363792b9a,
  0x7fffdf7aacb900ce22eb57fffa87b959f3d6ceb0f37ffff90ed363701d95f71800009cd467ee323c865c,
  0x7fffd00172799ca20725d7ffff20a4a5c23236fc357fffb212a8132df9861c780000742f5ee28846dd29,
  0x7fff8a76c6a5f68f09213800005bf7af6bb336325f8000a605cc6c9176306b980000e64db15ece41c9ef,
  0x7ff380b8a0ba183664f797fffb27e68695e39db15e7fffe57598faaea3262a18000269062803408eabd5,
  0x80039c111cae143172fea7fffbcb08b10b4514018b7ffda6805a10766ee1efb800012c6f2568bb99dbd7,
  0x7fffb41d3ce540bcd627e800425f39fa35f25899f08001aac2088cc0551b154800280d0cf68feb8e6554,
  0x7ffff64e533764b194dbc7fff105bb6c58164134be8001c9ef68b626a7bd51c8000c3187b5752adc1b00,
  0x80001678525f9d2fb07e0800035aefc27fccdfb9bd7ffff734643494662e7e87fff5011b304759bc343c,
  0x80001505fc472ed7ff52c7fff92b3c4cfff4e0cf4380001f91921cbac9f90768000a9cb11fd6ea5912c4,
  0x7fffa496688aa280ae3578000a569c1d42fdb4153a80005d2175bacf8ed4858800078d778d0522b38d54,
  0x80013894c13322149abe37ffc0cc49eeb1a945cf5d7fffa482d8ae80217ed797fffe0b019446f3a40769,
  0x80009fbe4867a41eef22f8001b6815672a532250ea7fffcde0a5cd833a0de357fee4d820bc63a1e993d5,
  0x80021835f36fbb586fdf7800175de04492249ac4857ffe7849c085a3fdcdfde80038146c03227fc78681,
  0x8000ae2275aa4c92404b47ff8ebdc73873b83114087ff45aad09bc3c0c3d8ca7fff3cd864e531d88ce3f,
  0x800019eba725322db10247fffbe85af9f1b6a335c87fffe784ecd37cfa0808680005b883b30f93e3a412,
  0x8000119f8f0a354285bcd7fffb019d9d84377d7d877ffff5ee171a0980a4ad6800014a7a941ad7b6a0df,
  0x7ffff2b0a21e98f3a2f7d7fffcaee0343e995b667b80004bcaccc47e2b0309b80001b6c060cce93b27e4,
  0x7fd38598862cf8d4e9dea800042b51ff4c8abb847a7fffc0d8b2e89b54c214380008ed24e4d8f9d25c84,
  0x7ffeb94781f0f127793f68001b544b30a0f4f9bbc27fffe582b7d8c069e8e217fff2e0eb844f218cedb3,
  0x7fff8f51a772f8a3824237fff7ac90b8d5c3b3cbb88001a71c2caa72a31d65f7ffeb0b1e1dd8e053a674,
  0x80004fa662f232fc120aa800021e7c4e8fc20d6b2d7fff9719f0144cd8cd1537fff923e529b0f33272ee,
  0x80003136467651ff6ba098000226344b97b3047f7280004ebbc910cf0ca794a7fffef1b9d7a14a1106f3,
  0x7fffb85e11dc7c80e9208800019ef2ddbdc22698f87ffff9a42f8922aa1663e8008b142b1c73d8541007,
  0x80000676b3ee1812436867fffae1377aa9a9a1ba9080004c692dd29add5286c800016159ffe7c3e56626,
  0x7fff1b9f6f9b450631c807ffbbb8cc74edd08979347ffff30dba10809cb7cdc80001b8881db6c1c23338,
  0x8001a364d1be27f976aa47ffeb2953a40d923f50ae8000103cf7249e186e35c7ffff10d688e9c8b00c49,
  0x7ffb2c9fbdc5f1e2685b680056eb182473dd7d2653800051cc36b3360927a397fff5696b5565de8cbabd,
  0x8000b9893d48e128093858000a42485127859b280e7fff2eaaf23b82fc4b73e8000d4522e5b261d6b0cb,
  0x7fffad436ea596a80d2577ffff561b733359deac3e80008f0fdb4a57ba89d908000bd0ada4d074b4dfd4,
  0x800083ddb220bca9c53d8800b27cc2571b6226e1237fff63a2a4a0b8846e71f80006afb05674ba34ce92,
  0x800032ad45d16f279716b800052ff329b2b2357751800057b1e8bc2ffc99e44800078876a4f8d23527b8,
  0x8003098786c0bf4ce7fe47feabb121ed9984afe9337fffc17fd353344a671ab800028793f9522f8f042a,
  0x80008826a790985fe0e3c80008d38d24896b5a3cb67fffaaf5d619e061772ef8000cd354c5714202c80f,
  0x8000dd1a8b268163c194c8000bfe97209b2cd6f543800121f8f6440f099fdea8000333fed2fe2ee0c913,
  0x7fffb6008c9f22cd0296b80001c4d3b6ae4e2532807fff9e17e6a9a4bfe5443800001e053bc2a9bd07c3,
  0x7fffa4ff962222cf26a3d80000d12cab51978060fe800054afd45f412c3e301800056c15ce4e2be1e864,
  0x7fffc94d509ec7c7025ca8000180029445a9819c8c80002c8f26ed4676c54be80004d3d5a5cb24932242,
  0x8000c6966346965af70f380002b4d93beafb4408097fffd823389d6cfd3592980002b3d950c91fd8377d,
  0x80002ef57e52af8b6a9377fffe5140219f73f6d3ba7fee8a73f161fa2dc3b9d7fff9f020bf9d498de21b,
  0x7ffe0c18955cf31bc492f80046e6ed8185b44c462080124741231d8b33c69147fff50e61ee47e323be12,
  0x8001d6d8de1c6c8c4a6d7800266375e5aa1d5917ec7ffcaf666bcbb543da2a98000bc36dc46830c39a67,
  0x7fffea43ee6a2e65a2caa7fffd0af1e07eb4d394ce7fffeaa4667fe1aa286cb8000423dc7927f13eead0,
  0x7fffe46aed3a73eaedcbd7fff8d70f9bb88a1dc7ac80005d6fac0862342e8d97fffdd1bcdda8f2247feb,
  0x7fffb85e539c1f1ded2aa7ffff3fd17f311c10ef507fffa3514d31cf1e3f518800070fb3033a2f39b5a2,
  0x7fffa301ecf7f4eed0a4e7fffe17e879a5c5dbe2a77fffa326a00d24d496c877fffd3991de88ba3eff01,
  0x80013d27496b92a6d07c78000184a5f3c8963ad21a7ffed4a6fb56fe2a3b6497fed73ac86bdda9d90b30,
  0x800179e3f24d759997a827ffe6b53d3802347c1a678000f9e51b2cc73b77c868000670b409d47c316535,
  0x7fffb5417bb495dde0da77ffff08961b125b8e679a7fffc0e98e2cbce49b5127ffe256d09e7d72b962d3,
  0x8000341ca0550caf6e1c77fffbdc14f173cc2c45c77fffa01ceaae99c5e480980000551bd619c71ed289,
  0x7fffef86076de3215ec5c7fffd34f74c05c6edbcf37fffb788bfd014c1244117fffffcb29662f2aa213d,
  0x80006bcaa791409754bb47ffff434cada7d9d6433f80008c9b56ffb008856f5800079d0d77a5fc132cae,
  0x8000595edfe507ac6596080149646116136787d38a7ffffa930edb4463e2a8c7ff2a69273c9f0e9db085,
  0x7ffa52e0ffbcafa7b858a8002ee16431b1b3c7971380011ecca6b60ac1d5efa7fffde87f6164c7bbe36a,
  0x7ffdc9c3f485e8491709f80040bc0dff82f53505d27fff8f0449e796ec835d0800d513a3bc40f7fdbee7,
  0x8000445401442dec7558380002ea997c5cdb2753107fff9353b1377078d70257fff44195bb29cbb65d76,
  0x8000342b09dd5d200a8507fffb2ab16299c2ac1ace80001a1b01ead1bf2c40b7fffb930b155a367a384e,
  0x7fffed3679fe03d8416b37fffb2961e0aca76124e07fffdc4e67e68a16b87018000477d62a2d55947e6e,
  0x7fff9e56c277ab6173f57800062192b390c7d962ce80002cab23830a912b27480002efa098334375bd0c,
  0x8000c4576ae3265dd326b800046a50857600e2fbfe7fe454bf8c613b84d431880007a89f85614e7aa756,
  0x7fff8310538729b6e82487ff689b35ed531aad0dd87fff64b7858b893da6ba58000e61a6686bc273ac00,
  0x7ffebaa4ae20544e5c437800090bab7ecd983610d48000083607ba037b5a87d7fff24ebb6718b246ffb4,
  0x7fffa7254e53fd672cc8a800042e8c07c49a0c0ac78000ad37d4dd7f17ddff880000716857c213d1fcf5,
  0x800001e1094c467280fdc80001d1178b24e466e33280006a92a337ec2f5f00a7ffe7aa7c7b0d77380019,
  0x800028252ad37a1d2170580003d0451640e340eecc7ffd865153f69f59a45a380001a418e73fb92fc77a,
  0x7ffe9b5756a74480f0800800436add22402e09273f800046b3e16dfc8f40cd98000fea0f4bf2518b1479,
  0x7ffe8894d79f0a097a2b17fffbd14e9152847c944d7ffeb6931f5498d7f25ee800177fb5af0cd5b7e420,
  0x7ffde214a943df03889228005b4827f2a45b81d9708002304d6ca050c88c61b800205fd2ad1c1080046d,
  0x7fffe63276d5f104d1fff80002f2ca4c4ccc7b8b718003db48374f0396944a6800222310e7923bc69c17,
  0x7ffffa876ce57559d6984800021b4a04aeb6c3d09e7fffd991f8e17695b20578003b9fecdedc8ba4db71,
  0x7fff64bec0329701bff8a7ffea033d486c8f2b68bd7fffc702ffc80c6f3b2b1800067a7585df99ba66fa,
  0x800012ccae04e562953b88000c030cb6871ef515d780000f924e587ad286cd57ffffe7edadb88f54a8d4,
  0x8001da64a0218a57ee78080005aeb40f37f6b3dfd27ff1747ca1756d3c70d977fffe91e86e319c22b429,
  0x7ffeed6bbad84484a14fb80013b967d05bb300598680008114f6dd48429cef98000d49ed54e050b65ada,
  0x7fff9bc0a4a613ccbedc9800031063255ca9e9df7b80000351812dbeb0f1e8d7ffff156179374b28e03a,
  0x7fffc3fc63f7b25bcdacf80002c8bb80444332e7447fffb429afcdf14037c4c8000fd38e9060d2bbe7d2,
  0x80001d13bc3603796ea9180004bd81af2c6e381e0b8008e05cbfc19082e56927fffea8b94e90eec3eade,
  0x7ffc27cd9276518ab26fc7fff855fef64d3d091c3a7ffc9bbf254e1fb89506b8000178612cb9d7d3a364,
  0x7fffe59d448cd4ef4db1d800189cdfbdbb45467d1d800576899ed9e16abcb1c8000b148a43550db6443e,
  0x7ffa3a4f1bf86ab77f6758003d891ef287bc0e2c6b8001b9c546cdb4d984e43800211dc3b82fb5fa51b7,
  0x80005e53ef5d9d541f2ee8004ed5702e479e39747c7fffac2e0c73e7408079f800d17f254f3e92fd8d1f,
  0x7fffc1aae8ab2a35f4a4c7fffb0dbb34abdb263d11800023fbd29968f6380558000221e5a69b7ecdcf07,
  0x80001ed80c41ccdfee3f18001c06f720b5dc71869f7ffcbf98a5bc5cf881f4b8000035fa51274772a0b1,
  0x7ffff0317b39e32a938f380001fd71afd158ab35d98000310695e2b36677c588000491493aa9c0954c70,
  0x7ffbc10eb1696fff4f3027ffffa8f6d60358ac9b997fffd01c1ac3c71ac192c7fffef448506d203d1857,
  0x800059a505dfdb3e6cea87ffa7b50b3d83ba9b9f307fffbb5080348eff6215d7fdf77f39f75362947762,
  0x80000fd0c7beac1165c05800093ef7e343febca7e08000dad3d1b7c49ff388180000860e5d52de17807b,
  0x80001e67a1a29be945a587fffe6c21f82fa5aac5dd80009784f64d846c44aa780001bfda483fb216e9b2,
  0x800038130bca0f5a3b1368000b6b5ecd52b197a72c7fffe5baf8794fddb41087ffff9fcc15c94bdaef15,
  0x800014c75890d50136d797fffdd88a2a043290be9f8003d55daf221a48943037fffdad7d6b126cfda7f4,
  0x8004509b92e36c4a93abb80001d622e92f7076bbda80063f28debf09fbd8ada80003fb1b35c29777b572,
  0x8000fb3df35dc717defcb8000749f8e0bfe2326c267fff027f7d61ddb71c3c88000ebf1720b4fc87ae76,
  0x8000ddc18d3dfe0a5c5e67ffcfe934d61fd8401b638001a7ec2c478d91cd4db8004a6727a6e463cd025f,
  0x8002dacd6be1ec590310a8000282becfa3bd7af27c7fff03bb487c8a018b8398001c827aac4db3adb056,
  0x80001fc9717ecb9a52ce77ffffaf9a123bca41763180003614b4089b70aa98a80030b68bab3edf3b164f,
  0x800006941e938f99f653a800234d04f3ddf70aa4ca8000a6f137d9e441dd2ed7fffbe564295915e964d0,
  0x800029a06a98da0ccd3788001e7a09aa538e5897ac7fff71525a826dc3c38fc8000249f5fc19e8647170,
  0x7fffdba6a81906ba08e637fe37f346e1063e56afe77fffab5621dac0c2741947ffe7c10b0ccad420042d,
  0x7fffe04d5dbcf64194d677fff043e73dbafda860307ff5c40d73fc273cd43c57fff8614823225d173f67,
  0x80004049fff2f74f342da8000307810ce45f8272b7800024e14dd5eff668f3d80004d54e6a30ca97a7f5,
  0x7ffffd0b3762187be9e617fffe8ca9e73f3fa76e637fffbb223b2bbd22178d98000811c63af44666527a,
  0x7fffd7107dca918b7b293800025ab0598a7f3c570f7fff4bf1e2b56b1e932b280009cf1654fe27090b78,
  0x80023ad1f4bd21e99027f7ffe6cc127db5101307327ffc9403ce85766a2e0d580005c53a255e697c638d,
  0x80002ab3859d95514ef6a7fffdde0058388d26bd55800033f112d7aad7df2678004921bd6d3e38e3c7ec,
  0x7ff63189ac0cd569eff0c80002297ed7ae35c6910c80013680b662ca4212ccc7ffed907f9f44117994e7,
  0x8000027803c9ff52df6af7ffe9cab27375ca702b498003d65e9a8c43f701a907ffe47c075cc629272a01,
  0x8000612f01538d030d5b07fff432f989c03afcb73e80004c8315bf4d7beca307fffb4d21b80913a6c722,
  0x7fffc247c2e673df24ac57ffbdad447c0ca28d50677fffeb4e04cde9cf8e9da7ffffb4248d5265d8e688,
  0x7fffc803308c1eed06b7d7ffd22447cbcf4c219a2880000446a56e3da695d0f8000c9cab412133e6789b,
  0x7fe24b1434751a324a6be7fffdd7ae5b0fcb3aaad28000432bdac3ed82ada777ffe843a73c3fdd7ce1c9,
  0x80020122115303b42166a7ffeb5cacdac4e59ae7537ffebf7620c29323a911a7fff50d575c144eb256c7,
  0x80001d995122d971181e88000d79b4513325ba986f80001f9db4a0bedcec094800091830760bfc191a17,
  0x8005518e8ce2a093d6a5680000c5808fa4d1415ffa7fffec74e8fa5c585546b7ffeefb36046cd76af045,
  0x7fffe9f8b94afe6fa9b4f80038f1d79aa59942801780004a5fd9776aa08e0697fff8954586d4e539e40c,
  0x7fffb29691314eca38cd28000671e298e01c879b6c7ffffa74e4587cd3d021a80003442903bc2f9dcd47,
  0x7fff330d468fa6862fe8f7ffbd9ce753400908fcf3800463f00d7077cca618c7ffd01f6ed320fb1948e2,
  0x7ffeb71919005b04f6e40800007634ffcbfc6de5ec7fff5c22249e8ce25cb557ffe2f7c9d90afab91814,
  0x800066a217ab2c1ccc70c7ffe207fa310f5aa213ad7ffef466d747da0ee532a8002fc9a3f7c093e88562,
  0x80000ee06dd4b5d0662cd80007aff31e5b15f11f23800bc01734bcdfdc783118009ca9dc36ebaf69f612,
  0x80021c09b56e3547f856a800241dec7b341820b05a7ffe87f1770fac20c731f8001056acfb3f53b991da,
  0x7ffd5e1b6ec9d6a9629e680000918bfb086f6f9ec87ffffcc4d3a2c93f318cb800027d98e55b2a8bf2ec,
  0x7fe2ce110e21a03d0b2f1800039322c95a4aa4b9c97ffc6edcf3771525b2f1c8000075532d9403898e0d,
  0x7fffeb7f67e9ee99d2a9e7fffdee6e7016076004f07fff098c2546a33b3febf7fff68ec1e27ac9f97996,
  0x80006de60b1198e34f90c800266a5a49da10456ad280007044af7d3184369bc7ffe0c0afd41386d30dec,
  0x8000d04fda2f2acf83c438000390a8c30c86a4bb688002bbcdb7f27919476f680003455763fff9494da2,
  0x8000129efe6b91b58f65e7ff614b47c0864dd7983580003530a306ef62082847fffc15cfbc75829134cb,
  0x800265a81c8d44b5ea6a67fff9e7b460907a10ec957ffd9d92b1157e7d8f2a38000224dfbb88ce48131f,
  0x7fff513ba7e5dba4571bf80013aec43839c07e1cbf8003eedf2659baa3dbb487ffb643793a3ae7b53f3d,
  0x800087576d3abe3a06f4f7ffe3ff9f0430afd5e9ba80006125128998b0ab0997ffd8cf0d72a4973549c4,
  0x80008f18d854351b24750800d72008b1de3b68b9e27fff8cbe41b22314093b67fff61b585a1c032ac447,
  0x800082325f7d6abb4c6d97fff1dc345e118b40fcb78009623198bee2772d37080006a9718ac682a1710b,
  0x800476fdc48e163f0babe8000022e41a5411d5b181800088da936342bb908c07fff0f4f6e20ee47cf61b,
  0x80002ac6245e37bb1dcb87ffff7552902731aaeaa980004175b6c7a460aa6ab7fff528df950a360c1ad2,
  0x7fff8decc2d23a46a81e87ff66517a6047715388d47fffe2fe6d601bc614f387ffff54656da459334893,
  0x80008d8af194e47d22ac87fffe4a7a956a7ae8577b7fffc43b85f86011a9b117fffcccc9fcb8d8be8fd9,
  0x7fffed80331fb2a394db580002b7bf6d4fc4ed98f88002671e77ce20d53c1358000280c356149ecf8c0e,
  0x80001bc56582c6c33d55d80099c53f7d85a63f4c6780003980f75c0e35c2b017ffff1a6b5f4a2b60f2c8,
  0x80021602537c6e4a0a873800152b3703285646e36f800049138189f3b35ed497fffdec4cb6584cf89c53,
  0x80029a6e716754cf9211e80002a75a929df63148928002c50079dc40f7cad887ffa8a3e6cc4e89dd7036,
  0x7ffe339c115f0134abc3380005bda22976c60584777ffdd185c1b855e7d82ca7fff68219d9a38c4a989b,
  0x7fffd51052bba8820b43b7fff7edc3f6d6c4edf6dc80019069fdaf7f2e32a547ffc7616bc8bb34af0e90,
  0x7fff4b62e903a86b5e3e280002ed203aeec7864aee8000d5724139636d631328000bf8810cc1f1207cd9,
  0x7ff917747d50cfa72990780000d72d8f3ac8c764137ffff6abc531c5d7301e980009b20bed2b8b07af2a,
  0x8003f7bb77d4fe2d0236e7fffb92a20e55f3dd62958000619d8acaaf4f0fd408000474d9a8edd8a92ea7,
  0x8000000d5a9f99ba386c97ffff8821be768002cc207ffd79166f65aa5fe39e97fffef2619cfc2e3af787,
  0x7fffba9cb8ae7bc99b4327fffe794064186f025aed7fffcaf1822b590d76f3e7ff282507b486de69678d,
  0x800020eca1038b0da5a7c80002a60a684ec7a338f37ffbf7acb5d4bda70cf18800153368bac96951290a,
  0x7ffff7a96d5c2c9823f707ff48ec01cc24aff5f46e80005bc02928f2e8dfd57800024a1435392abac0fd,
  0x8000354fa922e522d74f88004bb1b507fe5d665e1c80001f5681921e4e5e3f7800038d4cdf279131781e,
  0x7ffbf82b38cb8ed623e357ffc0ffcae2ca3b51cc7f800030b7124641c5420dd7ffdc00653c60e3e8680e,
  0x7ffe3eca3ba1625da5b227ffe2213532d2988d47b97fff6c1bd13168b4bdf0e7fffb09c721fc3139b8f1,
  0x7ffd53afb3de4b17347dc8002defaf846291ffcd777ff8b4165ebf0841ddc5e8003d2eeef8d51b70e051,
  0x80005706b723f87a0722180002a3964cfa78d26e117ffde0057b10970424b987fff15907868d36d4d52e,
  0x8003d1827994b92b2d50c80024a0571d95d4d1dd2f7fff71b9ee83e7f62975980008268e5292b970fcbe,
  0x7fffe1fae2736b71e4b1d800010ea01e04892fef50800019cb3a0f1a545fdb48000159b88945d2922db0,
  0x800031c62f7a254b30937800016bdd8119064c27dc7fffc2296d507cfebca4980003397c2d77e4a9d955,
  0x7ffffa5cb26558b13461a8000002609a56d5a33adb7ffdfce514e1c995551138004d180597b7fc414ca4,
  0x7fffffc8701e391789e0b7fff3f56fdf79b1c082d57fffc35f26f823361bc0580000d2b665a57d4c67f6,
  0x80002d68b764d3cba71ff7fff8861d619e033c7e7c7fffee1f6692a679212d27ffffe4b481342fb00b86,
  0x80000dada1a7edd4a104380002d8f2c0b0173723d97ffffbb96dd9cd18c46f77fff95db7fe0a3fe295de,
  0x7fffc17420b33389a86cb8000e13aaa4cc789ae73b80000ec66a9605b7f20687fffcf223c2033e587a39,
  0x800051c91199407fa9060800046609b049657b05de80001f981db32c22dadcc8000250247868a9356636,
  0x800033750ad2226e05a037fff64057454f0bfa5aae80000579654d07137b412800050d7f36f1d5f10bf2,
  0x7fff6b93c0710fdcd5c137ffecbfdd97d3b99f2b367ffff70f4d5cb92f3ba5380005f78b30caf596fe69,
  0x80002efcee50d674a3c4180002b7530f2a755ae85f8000027381ce4dcf6702c800005120d5af20c06f08,
  0x7ffff7c5988681fea947c800004c4e9509c85510077fffd2a93aed1656d5eff800044853ed360c3dad4a,
  0x7fffe2d65ef20fb7333f97ffff18d591ed3bd29ba58000356b8033ba27ccfed80000af4961b117eb9800,
  0x7ffff09b9c65abde999f680006bce42837ef8f65f37ffd737e580dc9e2c35e080002f0585ac161e9e89e,
  0x8001241b02d83b4acea707fffea727f093a69c7be27fff51b3ea4f02068a59a7fff96174bfb59b71558d,
  0x7ffffe3a635bf3dfc37ce800138aeec685216fe0e27fff90536d79cce6b1d337ffffd5414998e00f4716,
  0x7fffc8aa085ab30ff5830800037d844dcd6bf03e2280000676a3b4345a2c5078001252f39ac5c9589954,
  0x7ffeb916d6ebf6f547f6c80001a41895769df711677fffec9075b6ebf42c2f28001cfac2de8025072acf,
  0x80000f649590fce2c8a3580008531b3d6c9e9cc14e800066d3e85410d647ece80001d0a2ae65f4b16dbb,
  0x80000d7501d31acad833180001599919c114ec95c17fff8dbed5e3dc2feb43f80002f23a26dbfd849c8a,
  0x800008c70b5e0882c2a287fffebc43fefe74ef22257fff5442bfeab70817de07ffe60215cfcc4c9c32e5,
  0x800077293dd84f55213a280000c744792771fa849d80008d33935b06c4763177fff322c122c013c46d16,
  0x7fff6bd4f7e54ed96d7e7800171a5711fd551750077fffba6724dcc29b6cd9d7fffe54d6f04846d4f95b,
  0x800016940d114dd2036f480000b05c8244def8dc257fffd181620f71fb5e3c380000bea32b75ae4a97e2,
  0x8000012c020976fcf38457fff011634930000530fe800004a086f24a76c92ef80020858d497e60b392b8,
  0x7fff7bcf57f46977a7705800002e544c0c7535d3b67fffc659bc69ca5b1f5bf800004b78b5fbab6de389,
  0x800019848c1cf7328adb17ffff91ad6b6dc49830b07ffffed1e037318309f5f80000f33cded5f03c0142,
  0x8000ded84fccf9fd564bb8000611a29cb28e81c08c7fff9129829970a3cb94c8000038cce40bfaa80fe7,
  0x80000cf1406f8fe308f6580000d85e3aecb2d3dc6780009e91113ef7e3f4b1f7fffe7f6434722eb8a07d,
  0x800048a7ae3bb3396236280002a0a602f5030b761a80003bf0b1f7c648896287fffcf916680ab5ae55ba,
  0x7ffff3a8a08045a7171ad7fff30495cbe351cc64a87fffea812983e86d9cefb7fffd35ba37dfe222b9e5,
  0x8000c957115a1063011847fffa74be0150aaf51bc380015e2e21c4629df34be7ffff3b0a2d0556a08e34,
  0x80005399c0632b09eb12d7fffff051adb37328ed8f800033574848136b832fe80001003411bbcedd6885,
  0x80000aac854f2deaa387380000115a111f8be4e0287fffe5b8764a7b60c83e87fff48b57d9f3296f2601,
  0x800132c44d05110e81c9d7fffb11f8bbbeb38b2932800027390f408c0f56cd17ffffe9a64ee28d3bd2f8,
  0x7fff92e9f5dccf0d8872b7ffff00ed193c0b4464937ffff4dcd69785bd6d24f8000ab74331e443fef07e,
  0x7fffef7eac7cbf5a0b1d87fff80f9afca9aa74f24b7fffd36b48cf5e6d967528002a09b3548d444a3c03,
  0x8000d686aebe40e32956d800020fe154535da3315e7fffff893881d6b172eb57fff1200f71bc5d0feda3,
  0x7ffff440be3402c3b59b9800049b09826dda3c8ea4800057f97fe7029a910197fffe8db5cac697c68a77,
  0x7fffc6eeecedc63557c5d7fffda00964c7e17a480b7ffea92ec6fdac0aa442180007ecf005d07fc22ba1,
  0x80005b6f080de958fbebe7fff7fc2809f05409922d7fffd87be5aabc15dc0ec800064ff248b3e69fac6c,
  0x7ffff956cacbe6fede9ea7fffee96bea6d22c702267fffc6c917a1430fe5c9e80002ee1b52e12d858b23,
  0x7fffdeef379932364a7c17fffa0e84c4d28a62b4687fff520a4cbcc19c888b47ffe41e4dd76085d70478,
  0x80001a4e60d8815e55792800000567ab2f4ccc210780000886d8de8b7e624dc7fffedc3c1018a5766dfd,
  0x8006397a2a35765a1671e7ffefbf39b63f6e014b767ffef078b489897183a388000100ac4b5863416540,
  0x7fffd78ee7468a005c4d97fffb136f4addfd4a5a5e800003cc10a959b5850988000270bff28f5c9070bd,
  0x7ffdd8d77e214e51759ba7fffe8b6813b4f7cdbbc080000e04474e8a33101817ffc0570fcbe2a6c84887,
  0x8000873e7348011ecad5d7fffba2841ccd0b6b66f08000082cba4b624e95f958000d4112a221a9c57cd9,
  0x7fffff6ad5ebb37490d298000447570f903d9550ce7ffa19cad366eb878819180002ab44ef312ecefd4a,
  0x8000346e83f22f5d8c5fe80010d85d1869bf69172380008f52876d809ee0c9d80001ea889dc98aa40e9f,
  0x7fff4e1912a9ce85044ba80005d5415a3d964605ee80000e4a587f1a2682db17fffc2381e3b07fde6783,
  0x7ffe0bcf9786db29753fc80018174f432a9826745b80009a9e04fc12f90febb7fffa630b73a3ad0bcfc6,
  0x7fffe26750db38d2ded028000183d4687532b552037fffacb51398710e54f56800756293a1cba69cece0,
  0x80001b0d11582681a364f7fffed873de38fa526f5f7fff9b1be3e5415b503287ffefa311f8fe0bb4f55b,
  0x8002c303a27524ec7b5e280013d1bd04f83889b9ec8000064cefebf503fa11a7ffffe1ac5dc309ea19ba,
  0x80004c7c7c221875a19f98000b8c443a6bef9c933580000fc30f4c7a68faac87ffffbe6f952f11d7906c,
  0x7fffd5b6cffa5019212a68000316189bfa3b22bcc67fffe3e789c51c2213e7c7fff4c5066550166e5a77,
  0x8000809663a8b46863e25800024ae726b58fb263497fffb7b8f60545c55dacf7ffff1f720291548e7150,
  0x7fffe8bfc4891c0171b95800017cd28fd31cc586d88002d374e3d41522076e18000a8ff47631987c07e3,
  0x7fffd90555db60ace5c2d8000f8779c438aa3162888000429aec83ad335ca338000674758be606dfbe38,
  0x7ffce3b528a3c03b77ba17ffff38c52002331219ee800053deabe51c1c2abec7fffc329dc5f0ef2af976,
  0x7ffff7fb174b4fe93f08d8000296dab06918d6d4647fff5bf82c1d2468881527ffff8ebb882cdc379532,
  0x7fffe82de650a864f01ce7fffe71dd665f1b7d73f07ffce2f58e431265ca7987fffd992de7355c1cc679,
  0x800033be9f13d3a2d020a80000f6b53309be61ab4f7ffff9493ca0f09e0efc180002a31d8f7009f32d17,
  0x7ffff4aa8c488f731ac6e7ffe45fdb58ff6bd7b17a7fffd99b169e7c8fc352a80007ac826364c1a4934e,
  0x7fffe3501802953c926517ffff81a56326026a5d1480000fcb4351325dee6717ffff3c90095b79bc3cb6,
  0x8000a20fedae9347860e080000229ac6e12ecb2d757ffffb6c2022c5320bd0a80000d6bd16bbb64d4cdc,
  0x7ffff5abe89c53da3ca5880000cb1ade33dd7b9b6f800061107b0dac4096c188001567148507f13c6866,
  0x7fffbcdda4795b49decc9800037cf39bcdca065e9d7fffabd8a56a4036eb3e28000488d8cbfafc0906b9,
  0x80006df7cea062966dfc97fffe70205253556864f98000fd393b5c6b4af71b17fff0251a5efb92c4d5d4,
  0x7fffda5f0534cd2a3171c7ffff78ef10bf8a3c37347ffff5ec2de2c52b55c7d7fffe42f1ef52ec594c0c,
  0x80001a19e7a69b61b57567fffe901fa85b22c7f71d80000b898718c7429dd417fffffa7db9df947ef92a,
  0x7fffface5a031c8042a777ffffc741bc0f6e62b44e7fffe8e1df63eda4e1e787ffdd64288d1f62e92d5e,
  0x800005dbac46f7c87bac37ffff8984c302b326f0b47ffff9a0324c3f20306497ffff7daeddc73d2818e9,
  0x7ffffb6f4196730e44d7280001d685cb81fb43d06f7ffff33d739d185cb752e7feaf12816b107fd28afc,
  0x80000b7807db18bc9628f7fffdde272aeb81ad69737ffd97f5ab7cfb328d99f800000fc18473510ca351,
  0x80007a85ad5d9841bfc1b7fff609fbd00b99cae9fa80000ddf4d25485491bb17fff9e6f32a4205333047,
  0x80005c2b4e88ac53f5f5480004e415e594e3a0272e800044a5b699f3e0153b78000700383782e5b7a6d8,
  0x80003de4386f83f94d7f37ffee360981f8f2f62e5f7fff42a14c5521c0dfc307ffff1bd9ae9d55c82197,
  0x7ffff5b821afa0978213c80000e7ab1b4997eb254f7fff9cccc9d6841d612de7fff9c60f57a38b695067,
  0x8000015931491decb2c537fffffa7d867456fc798980005c2c6b9f880fdafe28001a084b57faaa84bf1d,
  0x800d71b5761b15d5624638000761374e3902c8f428800004c8059e63ef4e6eb80000b86a2a2456d72aec,
  0x7ffffbc1fb55ea9cda55080000340d0601e35e35bb8000016df8ebd9274717c7fffebd88fa34868c61a1,
  0x800002d74afe4a470a4ae7ffff993b63a78c720bc17fe24b84af3175cce99a07fffeabba1d8cfad10503,
  0x7fffed3db17d49f69bcbf800001152faf16cbf1e308000011b1df0464f827247ffe63f8277883f3bf7db,
  0x7fff0f9004b2c670048ed8000dede14e7e72db40e27fffce40ba2c5adf7dbcb8000da0773306b70febef,
  0x8000ef4d03eb25483d0d6800021fda00c1fbe2ccf480005477177d61f30361a80001647490922a22ea48,
  0x80005dcf8be0aa3c07af57ffecc452ee20b447d9be800050a14297b28aa19f7800051742f81e9736f808,
  0x7ffe2699dbbd275097e5f7fffe8c8f2b8d9a2fcb0b7fffe21f817526e02abe37fffed074376b1950a157,
  0x80004b17d3dcc2edcba2d7fffe8b7395d443707f887ffff67fed20380225c2d7ffffddec0b8c989aa513,
  0x80000418903da3803826680000013d14a8dec9e14b7fffa7883bf9360745fb87fffe20195000e0f18f9f,
  0x7fffb9db4ea34608c9f0d7fffcef633e18bff78423801479ec4a89528766f9a7ffffe32082d09ea595d4,
  0x80000cbab479342e907e5800012638f16cc939f0e07fd48413625dbb6be3a637ffff471496c55d1ef2bf,
  0x7fff9d568205ebf1acf3a7fffff39d77867b431a69800f4ff8d3b2a923accff7ffff2b5b4c54ff42ea79,
  0x7fffa88fbc6b65ed872ed7ff8a467ac4960b73bc1d80018861a1e5943f8154480000346760a44391d858,
  0x7fffc569a1e2572e4fc4380015e3393fa53ba9bb457fffd3f441c484638bd2b8000956f28008b007050c,
  0x8000005f1af392ef84f908001dd2eb40867153aae97fffb19bdc8f913926927800491300524a73b30cc3,
  0x80009c8be573d3d8ac0518000c97c1e4f5f36a7ed17fffd3e58b9c71e4019937ffd4c27460a5007fe076,
  0x80001479bea0d3e87eabd8003268b8c0fcf59a4bdf8005ce8b131c03860f4c67ffefedcf4b735d75f5c3,
  0x7ffffba1d80f06f947a39800052752772b417401d37fffb2f20ea3265f300698000135ba8c3b0ecba431,
  0x80110ea742f1dabb3153b8000262ddf786bf00166f7ffffae0138906b0c50137fffed04e5745e713e489,
  0x8000073c2a03384e1fc9d7ffffb1d30c1ee02ffd8280000639fe5400ad0e60d7fed53a68622b894c509a,
  0x8000f3040d563d9fd9e9e7fff146e5e1ddeeefe6de7fffd2c16bfa66352c6a97ffcb1a95bc4745604c87,
  0x7fffb4db869915cbdf9627fffc3526642311536ac97ffe137bfc09842b1ed7b7ffff008520bcc544c479,
  0x7fff6ec4db131ea7912467ffe6a938c1894cf82ed37fffdcef894603312589680002df43cd122e086745,
  0x80000d5c10582d357c3b47fffb4f365bbc18b2c814800022c33b80d1352e6b0800053a0ff9e6641875a8,
  0x7fffd98093328e28c68e87fff92b1567f7a8528c6b8000fa93bf1428484cd867fffe80895755f7ea8da6,
  0x7ffff1f7ba194c7adebc77ffffb0b53638461554ba80037073d9e6e787701ff80001706cf2999a285a64,
  0x8004b2f0752fac54177227ffff40de9657439d38427ffb9b02440decf08a26e8000087a18cb23a5fc304,
  0x7fffef71fed8d342819a57feb451176fcd1febe8f88000024dfbea359e342d1800010a6647860458ed46,
  0x7fffa494887423a8ee64d80019b219f8c0d5114a668000201c89ed7b08732457ffff72e57c28e1132e30,
  0x7fffeaaf9f5b09c7440f0800091ddd60874c9c3f4b7fff2a5386f7d01c52d868000debaab624f8d832cd,
  0x7fff85ee02ac262d977ca7fff14763cadfd4086a6b7ffeed0332df7720f3bb080007d504697c47ce8139,
  0x7fffe65aaa2057581cabc7fff3dc914fcf23a62e097ffff3b56f79e54daeb567ffe0887a64b641c16fdb,
  0x7ffffaa58583fdddaacb980000006cfa2fc6f0da857ffd61aaefd782bde1a4c7ffe325b46e8ca0fd4f3f,
  0x7fff8532303d6d1cd02ff7fffd366681bba67a016c80004e89f040a2c0282c87fffde5bac744db5b3e10,
  0x7fffe00e08cf1f0b672407fffe9ff5813d98f101bb7ffff8bca2e03cf8668737ffffac0b3825b09033f4,
  0x7fdcc55062e63d2845ccb80001e990da0ee240ddcb80166f87f9ca4e166a7db8000102c6f0912ba70327,
  0x800057b2547ebf810e0ce80004eabf5ac17351663b7ffffae463bd2531f827c80000c458d4c9cd7c8101,
  0x8000de101fb82b23e71348001f78e6a492bd7d3e737ffff27e8991ba8f890237ffea1b3a8b50cd7a6cbe,
  0x7fff6df778ec03706a4f77fff618e042902e0b740d7fff33676809b82d7e855800051fbbb500eeab2f0d,
  0x8000611cd34245a14cb8280003e79b0574e120235a8000a963143c634e7c4f97ffee11ced5a71eb6c7f4,
  0x8000af907ab788e181d02800408ec9d972e70c61ea7ffffb8f80d4313eec7ec80003994cb8b775a93e55,
  0x7ffffdd81187ea8d847e180004380516cb58d6c6f87fffe6634127ee7d93043800042fb40156740d1dee,
  0x8000028df690cdf20e6ce80000e8f3ef63359380857ffe91e7647439dc71ed5801375351eb40e78ce978,
  0x7ff8242763f549cf69edf7ffff9334fba2d86af3e1800011af21c5b8feec5527fffc01dc5cc23e272cdf,
  0x80007b93765d0156ffd1180002d861c2abd732235d7fff467de0564b65d55207fffec93e461b8d9e5151,
  0x8000423b01e58ca35fcf28000393a8f854c01830df80000613ea7f31e45226c8001ec3b0dca554c942e4,
  0x8000654c2c03f99c087f68000b1d5aff436efebf697fff55d689faef8ae8dcb7ffee6ab4a523e9e68cc4,
  0x8000030ce7c5b60afd1c68000b2a84fbfe3dc420dc7fff237cf522805e38ac87fffd69227a65c7fb4bfc,
  0x7fffc7837fe9755767efc80004b647fc58f53a71297fffbdf8d8a1b9d8c72ae7fffeb0cd497c7a5760a5,
  0x80002a3ccdc4604c421697ffff28ba87eb53f96e0b7ffffc823be1c26d274917ffde41f825b0003ac6fe,
  0x800006913b14b7c894ee280000a06ce8df2becd9f2800001e641e6c2e2ef09180000979bf236797339a4,
  0x80005d678e64553b2d44f8004886732da59c0f79387ff7d8ae79bdb2aa6e3897fffebd748f2fdace1a07,
  0x7fffce33813be498e07bd7ffffc001e3bd055e377b7ffe9fcf6eedb8f8d3e9d7fff1d2dc58690f8bfd75,
  0x7fff718c45f5cb6300cd37fffae8c06f82ea52cee0800042628c7ac8c5628dc80002e5ee5bdc5e81d9f4,
  0x7fffe99017a69938f6ae27fff0d0ff5e74d709ab888000c94b5f95bbf9ce3508002983a266b5ac25685b,
  0x800020827ab84ea6b686b7fffff893ddeb1dddcd1c8000027ab967ecb58e1557fffff88a7750cd653e6e,
  0x800040362a4cdf1406d147ffff4f92692139638a75800008c0474ab2d04e1cf7ffff43a71c7cd5bd3867,
  0x7ffd959fd467ac0728f687ffffdc8b72b3b8f128138000149faeb0af49eeca87ffffadd0575056c10543,
  0x7ffff5d1a6c6b494a3bb5800007ff3de30e8936ac08009a494fbecffd9cff4a8000106376f0c5742d53d,
  0x80007881967cfbbd8a34c7ffde542efa2557c6a66a7fff82b4c72307245fede7fc9e280487c0c16c6de1,
  0x8002e10de73781d66fcb08002a3190805e99cd17dd8003181e53d6aee6dea7e7fffba4c0a6ffa834aed5,
  0x8008e1eb4ebe39aea59dd800b857f4cefa3d56eb99800691e5854e85a26da0d80068dc2749146c0717d5,
  0x80010009944059d97f9298000b7a5c5dcd113e13f67fff5feccdc7ef6db99b87ff52957a6e95b27cbd5b,
  0x7fff4e4c9fb39bac4aefa8000ab1adb353dc5d903680003e0ee815212104fbb7fff429d88a6eb4d868e4,
  0x7fffd58d869754cce76217ffff574fc5b96878ab647fffbd3dce43f7448356a7fffa1ef5caa4de21a929,
  0x7fff4b3670862d6f4aea180003b6e4f8e18560e3fa80000ab543a9861cd9db17fffd954b11313af73779,
  0x7fffb9473c46c355566178000509bbe3495b502ee77fced8fd8ad6e9267ccce80004343f3e837878d625,
  0x7ffdd5a61ff0b43ab1e0580008212380e1d26a18ae7fff085570c4b77c423307fffb4d36c73881911096,
  0x80016e5e8a405c442034780000c8b35b0dbc5062567fffe512aeba4da68e2058000bba666c27986ffe56,
  0x7fff1187e7acdaecba3b57fffd46910ecaa55e850d7fff153b4dc397b417f877fffb320e1938d315d9e7,
  0x80008b47bb436a05410347fff89515167cd0431aa57fff9c0e6d44c0784c6668000590a028123fee7cc2,
  0x8000291d65745db9f92b77fffcbf9e4a1f7d04b2578001721a7d691a03aafe280016c88096df6d979fff,
  0x7ffff5dfb9d591d3ff7d97fffd1eb4ddaf7f717c4d80001a841d99b2dd5306e7ffeba8b310d3ceaee687,
  0x80017629202bc9d26e0f67ffeee14dcfd6d08eb0c67f1fd04571b731683913a7fffc7cfcd0039bc369e0,
  0x8005746f6bb08750da9d88018e16ea57a5264312247ffa062f37031ff7ba2a07ffdbfe36ed6fb5c95658,
  0x800cb457a038fd4b452b3800be7f556c31016600438001c8db47ee0befc1bce7ffef45fa383ff7bf5d5b,
  0x800122bb38b5b131edc217fff5716b60d563e0d4887ffe5b8c371388d54c8d680027a99dbebf70b201d5,
  0x7ffe0e69c63cdc45eaaa67fff6e7a88dbe884c6d288001545d0a7c31cf162d17ffff3de97eda431e4443,
  0x7fff0ea5a37c5127e64237ffe778c64c156b95284b7ffde20e4fd8af413abcb7fff16710e7ce323d272b,
  0x7ffecf6382fe39767b20c8001398b55f9f056cafb27ffe32790c1a07039c40580025a941739f53440331,
  0x80000a9749fd0be66080d80007d27fc121b00f28238000c4a7e37ae0ba94e1c7ffe763c94086537f08f4,
  0x7fff38a8e0dda4d6c1c5e80008b38cb5c9ef79cede7ffffe4dbba357ec22e4a80002e1a8374d1cba518e,
  0x7ffe749ce076c54067cc07ffeffdf88d29c6c4966580002617f0ab0f453cf637ffff143fd50ea128e68e,
  0x80079841037e5693f32ad800069f65a909f167aef1800094576b4f430484e497ffe488b477900b44aac1,
  0x8000fa2819975d04ebdad7fffb755a2263f75684427fff8874a40f10a31f5188002849dd868ed4541a3b,
  0x8000075866a583637d86b80006d133862afb530b8d800013826ecabc62963e880001a607ee248272d856,
  0x7fffd0447b26a61b6918c80018c0763356a96cafcf8002651567fe4d1cf30cd7fffd08d73a6e3d4f7c99,
  0x80001871f44d99740a68d7fffeb2523d3845d7c5e38000061a900bc77b8d8a87fffcb44a30069e4073bf,
  0x7ffd389b7a1dce507bf627fff9e683bb34e666ce8a80000e5ceadc48eca85c4800086ef5e16bf3cee819,
  0x7fffabd6d217c1a4d1be37ffdcc039a3393bc050898001a537c42c3637b17a280040c4aeb8e37429cb10,
  0x8000432607352c789f2337ffcc420331ea3c5552637fffb87f91fcaa71d973b800050bc6590867a9a37b,
  0x7fffa5a83bd38156f640a8000721d54724a7dde405800110ccafecb2218d1a07fff2ac01c41f40f0bdce,
  0x7ffcebc4de51e24b78d0b80001705040e213a24fc97fff3ab485e60a32d27ac80006abd7afeda342df87,
  0x7ffcd51fafcd30cdc8a47800188522d6c7a11695bb8000824c073206173fe2c80015a43f993a8345e335,
  0x7fff650089896ca7d760880034730f42cb8fc5e15f7ffdb3e280a1835166633800551969859afcad961b,
  0x8000117ec6451ecf1eda27fff74b9b553371a8fe4e7ffff97f830dfcdf5906180002bffb39dfc4c282c1,
  0x800052be5483bfae74d5580000096d60a04926a4428000428a49b891df2554e7fff5ee844ee4083a0eb7,
  0x800002804aa07ed6c39c07fffd79d1ddf735bb9ace7fffb9bbcc36d830b03c17fffbb6f68b67580ff9fd,
  0x7fcdd33ccad366d6ca0ce8000292e117adc7b924be8000203830bee133fdcac800043fdd6ebcc6ebe56c,
  0x8008366148f2223fabfd47ff5a4e246fea80d33fd77ff945beb4e2af8bcd4417ffd66b972549fc37af7e,
  0x7ffff8d54a3ad7afdf2677fffff2184b7de44f6f087ffd1cc4222b2772374df80036d99c2560c7e38889,
  0x7fffbd76d2b26c47bb62c80000c8e7407856f66d7280000e0c548b66d237bcb800039ef7d20f7e7e9f01,
  0x80003f2f7d8466b3c9cac7ffebc68fe5d5f17569e37fffcabd108226f243e9f80009ae01e66bd85ccef4,
  0x80005609fbaa32390288d80005191fd5570fd1ec077fffce3ab6020f974e99c8000513370b9028292cfa,
  0x8005c262c4acc1854cc767fe3058c77f8616fe0e1b7fffffe8b9fe1fec0920a80005075b61c10f6da837,
  0x7ff1f22e9ad4119b88e397ff2b1630efe9ef51f8378007d6eb283441a2426d77ffadf2dc98cf5f1199f3,
  0x8000ddd056e616e33c2877fff28876229f79a8619b800005942efc82227070e8000a601ccc7633c32d4a,
  0x800061b9ed2cb47497cc77fffdb1779d4e54be12067fff76caf2d5562643daa7ffff9358cb5bdb082cf2,
  0x8000d97f60e18916bd9148000d3bf5a7b2c9812e138000f8550030814073d697fffebd7f8507862874d9,
  0x8000075acf0b97a2c20347fffd171e2098bed74c3e8000b9b46593b9317e8ab7ffe30689fe50139ed44e,
  0x8004a97697eba33e081717ffe5d97764137973d0cb8008a0962e0944e91ecc77fe170c883a330d4c2bb7,
  0x7fffb9aeb6c22bba59dcf7fffd2034d6f7cb823d1f8000b8f2febc7fd71c7b77ff78ed27c08cbf2a498e,
  0x7fff6768a8547a4fbda4480004741a27818c4f940a7fffe6d56b3eadb110fec80005e816b133d5f61add,
  0x8000c17fd892d7373fa3a800133be9311eb412e2058000221565dc457457d8d7fffb3b854ef8efe63774,
  0x800020a7ec6c670aadc5c7fffd23f5e4f6eff359867fff79a0a3ac913b518c37fffa35cbac637a07d520,
  0x8001deade93ee66da338b7ff8e47900d7f4fb37d6f7fc8e48ca88e5bb0b0a157fff01e071638def18e80,
  0x7fff4e81d20af08f74ad7800027c9876f3b2f082147fffbbbc37b84af4fd0c37ffd563acad2b5e04730f,
  0x8001972c2bf44e824622b7ffe16eba17e6f76e02557ffffe0e8c6aefca1574580000d15a428573ad6ffa,
  0x80001ed6f1cce3a6388f87ffff99bb4f46a57ea5177fff0229728f18da1ac99800041ba776b9243010b5,
  0x7fffeba479a3e05f5c2ac7fff9469b9e165ab348c47ffffd217cc52c1b9ebe88000309203595adede726,
  0x7ffc9a4b3218eae2268698007747a7c1eecd9137cc7fce602e36ae4bda4aa347fff755066cb229b23f1e,
  0x8001149aa2f4795b0c54680000130a70a072360ea97fffaa16123e0738d738d80016b552f25bb9c01fc1,
  0x80004a9437e1f5b4762b97fffcab31c33e8629f8d38000a7a9ea6039463401e7fffe2a84fe289958a159,
  0x7fffd86f8cba93702ec917fffefbcdfe4e4dbc00307fff8773617bb816aa0bd800156463cd5a1e9cb84f,
  0x7fff6e93d4a89ca61f6687fffa7903ab7c3ac5fd3f80000474afb37cdd82bfe7ffe356b50f91d5587f73,
  0x7fffc62d2f109880e648680006b9a693e7e07497747ffa357429008757dd3897fe37649d39aba46a28ff,
  0x7fff347ed5b048e33afb57ffff5fba3d95d578715380006b7dbb510e0b71a6e7fffcd5fbf94cc48427db,
  0x8000372d8916d8607eb947fffef6b4720d492463ad7fffee0006e21bde66fff8000cccbf9b6f4cf72053,
  0x8001ba5c3a6ac0ba3b7a07fff94c7c9a57de8e15768000846dcce0aa17f1d2b80005a31577d4a6d8fb99,
  0x800080cae81e39f3ee2bf7fe6f7138eced215ddb948000c297c6f9e3aa876db7fffc877efc974f512146,
  0x7ffffc0a5c596442f4ade800059e6e795a925270a98000c2db316f0c5ad9ffb8000dd2adbb612998cfb1,
  0x8000bca0734cff81de1757fffc7a10c19425dc6ca57fff6c47a813ba74169f580006f2a1408afd93d319,
  0x7fffd544b4e7863b4bc25800003d13f8396f9c75548000bd3c5d0f4fdbef57a80007286b0375e6363a7a,
  0x8007672a7647608551b717fffd0397d982af2df0827fffdb54aa6157e1bc1808000f6f87971aba67a4b4,
  0x7fff2f248a2bd20647c327ffc5793b13e02669576680000410afd673110a4d17fffb1c1a2b2e04231e50,
  0x7fffdb917eda84368fd447fff7d14015c535b04a688000e59285bd5dc0d7f17800127cbcdb258026a192,
  0x80000789a572e66781e7e7fffe2f57964ce2a700e0800096ab31c9106dca97a7ffd5a4cac8dc986af3e3,
  0x7ff99e0b256666d5358cd8000f0e0e09acb8f731b37fffff3ce9d3c10fff2107fffffe8e0cd2e04a3dfe,
  0x80003629d8a72a329011b80001dae872b5453daf837fff5d092ac0f922e3aa07ffafd94c6e8d33dec125,
  0x7fffe52bb20753f687f487fff0884250bd32b2d6537ffd8ec40af6ea3a5dfca8000c8b22a723779b91c3,
  0x7fffe9ea39628ccb601f68001af44f46f3cba1726c80004fe6f92d47b65fe068000167c045ef444f1c17,
  0x7ffff4a38d8b4e3cc67fc7ffb6427b649cc6acf02180000a0e48179dab65137800164ab3fcfc08d2ed38,
  0x7fff8aa1c8f5c57d358e980005fb2e7e2bce99e2857ffe31b5a25d8cd53eed07fffe34f1c8d2edcd03ee,
  0x7fffe6155aa8ec3fca63d7fffee502782d9d27274f7fffe122907c626161edf7fff07ba5ecd45e727b5f,
  0x7fffceee6058b825fe0fe7fff9ad6e843b949966807ffffe89d95bb0fd2b67480011c216af368946d83e,
  0x7fffd63e04c98ee6da6e87fff3ddf4bc75899d88c57fffad0bcc8a42bb23aea7ff9606859843a995c333,
  0x8002cc564758001c8bbe77ffdceae90b30cfc41d237fffda75730dd09e07c06800010d5bd237a972d595,
  0x800012189b56b25814d287fffb812f7ed8e07fdff1800008135ae92beda8a7a80000caac21bbb0b73881,
  0x80008ebec7b389487cd518000711ffd31041a090ed80028409fe5984d39a4087fffcb526dd7f731c44e4,
  0x80006cfd892b08f4392008000530a1d2e0899fa029800004befde3145f069707fffcaf4b9a43066ec263,
  0x7ffff2ae0427a22bb3f7e80001ca6a3ebbabcd8dfa7ffffe0d5512033573a937fffe0dee35ea4fe81980,
  0x800019825dc56294185838004762a99b42c21a33d47ffb8f31922ffbc4ee6ae800054678bbcbfd1e48a2,
  0x7ffff5c0bd5ed6efb14d77fffef6c1719f039e19e67fff89e9ae32726d0a4f080002a6ec51156a8b9b8d,
  0x7ffef977aa6fe1f117e017ffff93a1906512cabdfe800011738dec0218a73c5800002228a24c2892f8ef,
  0x800043011ac58c7bebd32800000a3e0d444ee117577ffffe8aa50199b6cecff7fffe84e5945ee9bbecbb,
  0x7ffff35fb313148c2148d7fffdb97cfcf15897cbc48000062177734626f9e1a80001519d48e49a3d401e,
  0x800006b6ed864b057f349800674df27cb638c984187ffe260a632c5708f608d7fffe52d3791619c3532f,
  0x80002449dc0fd13861ebd80026db5c2011a6cae55d800018950008ab368350c7ffff7f8de0a91e302e7d,
  0x7ffcf332f8940fb4c409e7ffff6ca50ff73a43231880003c68ff7a38a8f079a7ffed3385bf0c24866046,
  0x7ffff4b265dc72756dba77fffefe03366890d56ed07fffe6fd09b89d5efc67a7fffeb49ffee8bb240e7f,
  0x7ff9bee06cf7fb365429c80000ccd88b5c113d2bae80001c41653c9e9fe8cd17ffff8151c95133a93d58,
  0x80003fa6daf4639452c428000009b5421d324034127ffff70d8584f8ddd89d1800096876e9c20a129e30,
  0x80001c63bf426bc57701f7fefe090d346d5b5da7838000234f49c5446f112e37fffff0fb9ad9e5cd4d26,
  0x7fffdee826e2e84b0ba8b80000591d8e766f6254e17ffff384c77522d243572800004521102fd0bd78a6,
  0x8000603d65e86e6c8439c8003b0b0566e93d26210280000be073b7b495ad3767fef10e30458797698712,
  0x80028a9bfaedfed13726580003129fa78e8a2e16af7fdfcc73f7f8d9514c4dc7ffffac758c4d2a81f1c2,
  0x7fffee9ac75844b962d8c7fffe030e7bbfc1767f5e800972eeff39bceecdc2c8000152cfc210e288e783,
  0x7ff745d79b932f4f414df7fffc6ff9afc11857a47f7fe5f8a2383212fc4eff8]

/-- Packed radix-`2^84` upper-triangle words (`+ 2^83`) for partial Gram slice `3`. -/
def gramSlice3Raw : List ℕ := [
  0x8000714b94b92058baef17fd4119edfe768d8663a78001dfba359c58e97400c7fd32097849b5269bf8ee,
  0x7fff4d882f439043585037ffcc4d22d7f50bc9da9e7ffed98f660122bf4c61f8003648085bae3374351b,
  0x7ffeccf98f70d421810cd7fff591b646288591069c7ffebabb9fe1729d401a18000fdbaa2ae90f4b5532,
  0x7fffd76d5a3a3c6634e787fffd6dc9282a1dcb699d8000906654502d7feb5b97ffed3cd7fc88e67aa50a,
  0x7fffb0b31184385223e5680002f79f358c9881fa02800074287d14c6747889a7fffabb4283669f17cd39,
  0x7ffff797bb7ff65ae9a1180007a75222d4debacb7a80002b5aa0adef68b1b9280003a507d980a40eb378,
  0x7ffffbbc836f7de59e75e800001a69f78e4a287c6a7fff570afd65688dc3b6a7fff8f970891ce588271f,
  0x800140c676d0656a7ccd07ffee7960d80a7b0441048005148b3a3f5cba75b58800036e8a690ebc96ce79,
  0x7ffac37e5ef2e80169b2d7ffdc77cf4fbe2e82eced80020cf8ccad664f0e6337fff478c13ac264ed39b1,
  0x8003b875aa652daeafcac7ffdbf3b8ed11241513fd7fffdb14440fcd64f8d5980071bc82f2c9a4553cac,
  0x7ffe4eb616f667b11ba5b8001068091928e5b688228004987e9cc118d208d12800a815f76d32854ab482,
  0x8000d35263dcc0627839280000a5155ec3048250f3800062b8681fd81411ecd7fffbc0d8d8c53aef3a8a,
  0x8000136130b92fb7e32628000927d05d5744c371747ffe417e144bd9583aed67fff206201e48e5344984,
  0x80000c0edf16e7f435aca7fffdc9f5fd1078fb43617fffb1dee7793504159cc7fffc72c62e4b3f4561de,
  0x8001a3e4c5bf0cea35f777f891c8cf7864c07909eb7fffd19b4f67f1ecef42880000528fab75063fc9bb,
  0x8002d9b5ab540d1faae297fff117c8e80e1ec47b7280079cc488ae88f0a8fae7ffea2f38f458713a9325,
  0x8000e91230219d4bf5167800078af0cf152104b94d7ffc250432771f10e887b800188210d225d3906b27,
  0x7fffd22fa0ab7dacbe11480001ed4d184f91a7177980018ea9b510d86d6df888000d3e06c169b12187f6,
  0x7fff301d0ca85086d4bc17fffcf117bc7b579290ee80001cf3aa22ce653500580008c304887765770226,
  0x7fff1ca422d332d6595118000a0bfbd7e0f61b0a668000a450cbd21d59291927fffa60589355103206e3,
  0x7ffe10705229f0d7ed8367fffba34a80dc8ce81b0a7fff7355522f398484e427fff56732ed041433b0f3,
  0x80006a7188c977508c26180049c251627690088e5b7ffed8dafb302e10366ba800088fae5c10e7cd9fec,
  0x8000d22aa3b0210237b527ffffad19455600d32a347fffdb0d1e1708d0a0a8d7ffe303a6419147fcc757,
  0x8001ec144e2d2cd36c8c18007e4646237ab642b1437ffc2cc73978205f993058004c9fb14f486bd36217,
  0x7fffbbc33f1695ceaf34d7fff70ac9dc0aa6f93f1c7ffc591d3792f4fda0f2f7ff26388dfeeb5300b4d8,
  0x8000431e38f5c7b0a7ed18000a543ee266cee4a0bd800005bc02e37c117041c7ffff3d749fee89c615e6,
  0x80006f10c9a349e41261e8000524afbe40d9b7b5f28000901c413933905a79b7ffff6c59023580ae1459,
  0x800122da0b815e2c3fc027ffdfb201644abcac275e7ffd4606eba4d5bfe11748002bf922f543d4f080db,
  0x7fd463391a02047ee0d0980032baa65f87d186cb5e7ffe6171ec74f9fd473d380029c9d2efdd4accd2b6,
  0x7ffcfbc2758a4f044eef67fff7e2f29b8a1bc7d2f280048bcc3b6e5e5cae43c8000a0b5abd51a166a2a2,
  0x7fff64b97ae0a26e032f27ffe8c2190ca4139105988000b601eee065213d58d7fff5600c2c3a70c4f27d,
  0x7fffe28e6cda08217f084800088e630261c6e670517fff2f43861a8811b06447ffe710d62a2e4ce71779,
  0x800030ac86d4e5b91bfd47fff839a27e591903a9be7fffaa848dac8f83ea33f800018fabfc32b972988d,
  0x7fffbc5b641ebd88b0fc58000295adcf0a791fa5d18000483cfa5efb0cdad16800258339ce968e0aa1f0,
  0x80001063dfef2a42142277fff6541f52c9f108d76f800030d170df5f8b6c8df7fffe49484f3b423b60c0,
  0x7fff0ac13e8088e9d9e0e800458971affd8708cf857fffd8816b232eb16a4f97fffe47e1ef9b9bbcb764,
  0x7ffdecfb10fe9594cc23a7ffffc63d831c748704127ffec10df82e5443ad6368000ae4c268b5e9d19966,
  0x7ffe69bbc90aee74fd02080006c6d75fb74e80540b800717de26333713a83967ffae96fe76aea18b44ee,
  0x8000f46cd3eadefc8906a8004c5353c98bdf20f26e8009dd6024e26daa937578003b459256808bc09fef,
  0x8000362be9bc0df8d6c928000d539b9f8f1378435b80001a137010ac272fb178001abbd78192527d5e0e,
  0x8000b03ca1c94f1d6b21e7fff6ec8feafd2dd321a17fff0ce24275df3058f0a8000b0e6eff4d83f31d6c,
  0x7fff9d9fdb1de1f2aada780002e5bd0fe0ee86bb047fffce246433ca250de9d80000929344cd7e132ec4,
  0x7ffd0b9fa1c8f50a8b5797fffb06a3f3b85cf7431080000bf69581b43711abf7fff5fd65e8f07fdeb1fd,
  0x7fff86650c07f78d47ce580004d11a906d2f7cabb38000828dffe4fa9932b837ff99bb77721168b4d0ea,
  0x7fffcf08ef75a0299113e7fffccee7d980c54f900780001f8cab3c7e7f00f9f7fff2404d649e7741a6f6,
  0x80002a37cac336413eff17fffc1e6ccd6c5be8554e7ffff94c7b78231e5ba217fffb24d2b46a4e8e7c7b,
  0x7fffe4697c7998c917a978000040bef03af35193af8000144297c7caf66851680000ce95a8b35ad4b6a8,
  0x7fff8d4a5b222541ab22f800015b4eecc3278e7c757ffff707fb57b0b4065a47ffe74d5b9db87f34025b,
  0x7fff7adda3c0631c71daf7ffff38ea1f26df0cc3037ffffb9705fd719f513257ffff004dde6d7a79b1b7,
  0x8000de2104493402458277ffd6106975ae1336b4937fff80521a9723e0232c67fffa9b10ff4a5f580462,
  0x80008f526a50fc8acb27d7fffc982b6ae8968977078000380b9ae7e1b18eec47ffffb19f3a4c52e113f6,
  0x7fffc364c5704511569ae7fffb9ec1b53b2d8f47437fffeb7c6a9dac766627c8000ed763b9ec4bdd71f3,
  0x7fff8107f9cac976be04580001a6bab69b310b18e77fff8ec744a97d2629147800010ee33bbd0e1cd471,
  0x7ffff9f301f8f89e985be80000619d9d5e3d0429fe800029f6073be1630c37d7fffbe72bdd09b5f0fbca,
  0x800006536d2bf126cf5f17ffe82a075d8c53f022027fffdaccf42ede374d5ea800022bb60e3fbae7ab02,
  0x7ffffc00c739069e04c517fffbe479abad242c5c207fffd271abaf3f6bc85367fffeb5a30b7f881ec883,
  0x7ffa325c4cf16ccb211497ee246034537588eb3e2b7fff9991a34ca74922d537fffdedf72eca0af7f3bc,
  0x7fffd5f121da5ad8305f77ffe6101f7fefdfb0a4547fff1810d5d27c32089537ffdef1660ad303a607f8,
  0x7fff6bad743b4e5c9bf127fffa5a16878adef8d5387ffdfd21d5c0d936fdd2c800015affa9e92aeaa9ec,
  0x8000fc076ced64fea2ea67fff3921a1143c7febca18000f6066036bf4b45a14800040e97d15a5aafec25,
  0x80000e73891aff23aea3a7fffaadafde480d947c6d800041b1ab8f840e10c86800053ec1f4393dfc6a57,
  0x7ffff20c40bcf198db5b780005e0e4906460ca9ff27fff1add3eaf6f029449e7fff47ee67c05dc00b195,
  0x7ffdb3c862e504449f45f7fffb8edb1f216ffa3e917fffbb0bcdd95c44729fa7fff62c60e65fcd764ca0,
  0x7fffec63453c6306b16577ffff35872ebc30c33efe8013675c44e9b3be76e0a80043598439b79860b65a,
  0x800746cc1c863c9f913f47ffcbbee2321bf2ba7c377fd72c8ea964e1e9accca7ffc1cedc06dfff05e490,
  0x80001071ed1fd6b8b2d43800039f03850c710127a4800650f06bf551cc82ca47ffdef28d522ba95851f7,
  0x8001c3cfb53dfa3a79c1b8001748680aac1afd42d880014d667c0383a89053380012d2e51a995c889687,
  0x7fff2c8d6ca1eb13091848001e31399fc9cb3527c47ffe98ec837a8ac6c93f3800016f782bd42212ad7f,
  0x7fff96242e923cff201e17ffee86ec0a4547a115018000354bc3cc9bc4434a37ffffa02a4c886de9cc79,
  0x80010dec35b58d4b4f6fb7fff72269371a60e479d9800098f7189e9d5916cf680002f6a1b4459adcdeaf,
  0x7ffef1c7d05f108b5d71c7fff9551ea79b9e7d541580030266816b482349d2a7f0ef6a273a1082d687a8,
  0x7fff1ab13b36b2fda78ea80023df936502f50a653d7ffeb5a18bacb301f220d7fffc5485462d5fd5c6e4,
  0x80012f3192ba81e8a02c37fffe31bcbb51c72cbf7a80013d3ae1faa96cbbb2e80020c9757e35c0c00589,
  0x7fffa2435457c15ef4dbb7ffffe666c5d29f40d5dd8000958a6c632a426e5af7fffa63fd94b8fe5d93bb,
  0x8000477c001c1ecc72a4b80004dc202fea63996d888000a5914a8e0c9b527c87fffcade9afb60f3815ff,
  0x7ffff5a17540e8323605580009bde10488cc90f5637fff4958b1995ac7b55467fff78b8451a85095aea1,
  0x80045e9f827a9fdd2192c7fea326e328413f26da847fff3a6c2a83e4f164bf280311da697a401fd5bac1,
  0x8005a67c4f98679947cc17fff2321d01df815e08c580000690a0862e2e732607ffb3a51e7ba37ddb042b,
  0x8003e11451f784f9ff0a87ff9ed5a8196352c3c7718001098f264b8891586937fd3beff11526bb82d655,
  0x80030952898a3e34190598000039d8675152c1b2747fffe8768169d7a003e697fff46c7de23fd5600908,
  0x7ffc0218e278f595b101780024172145562bf8fb1780005a8ca8b6856fa00f67ffc42fcc247f51793bc1,
  0x8001f1ba41bace4602dab8001135de8754ea10f9af80004f0e15c06c47ea41e7ffdb669c4a4e5fcd0f97,
  0x7ffe9c922d173ac962b0b7ffe9ec3e51aad4e205b37fff26b3ae887ce13eeb77ffe0b72babf82618f6b2,
  0x7fffe69bf4440ffdf07cc7ffe21588a595b58853657fded06e47ecf68ea84ae7ffde3b8b93b41b523dc2,
  0x7ffff6a946fe720154451800b78e52f852d864ac3280007037cc6829913b9e180008381df084a6b0cea3,
  0x80011425ba7436a8cd1697fff913a4705c2ee72b878000047ca804fc1b103878000a62275e15ff7cf7b2,
  0x7fffd51f75db6c662b7d68000001112ebadd73f5e77fffd74a236ccb69216147fffd2e821e90710b8431,
  0x7ffffa4a07e6a8ef804437fffc7805ce8806013546800059764cb9ba39418f17ffea31ae2aa3a2cca26f,
  0x800000d402ab11bf3050a7fffdc1a24d7e71453f277ffcc7a771b1afd604448800048322bda2046a4efa,
  0x80017dade31c74ffc02fe800140139fec2bb02856f7fffaa18645e78269eeb380002fcde84a98e7d41f6,
  0x8001b07ad9ef04803c1397ffd20390fd9370827d2c7fffc87d1166d9fdafed37ffe290e07cd2f7ce1f22,
  0x800187241e622de6d004a7ffb73757591a9408995a800337374d2462d2ff47280015ad9da3249adb0e10,
  0x7fffb8c0b5674f54b8c3a7fffde75a40d79bcc5ab07ffb7f456535eb428b57b7ffb85fe4e8a06ed34945,
  0x80002f48ef0bf750e706d7fff6ab37d5387fd8cfa08000162d44e7071027e487ffb1687595798c2158ac,
  0x7ffdb097e51a06c5f3a097fffd9704b3aa63c46bdc80008482f2666c876f5417fffb2201c9ec00266ef3,
  0x7fff93eea20599e9f145b80009ec84a118a8c8f7fa7fff482ab02af22db266a7fffdcbc02fa54edbda81,
  0x7ffff3e2bd80cab056ebd8000346be61266202d2317fd11c3b3acf10ecf69d07ffeedbe6547255e126f0,
  0x8012c362ccc9fef36997d80000a02f49f7c9b2e6737ffffa90870687c85655880005488ce3f36d04adcd,
  0x7fffd0023dc72c8b633777fff9fb53d63c2c3e77947fff836cca88f987eb7938000284218946f01c64fa,
  0x80000e8c2984beea13d9b7ffff1f3a80372bd3a10b7fff99ad85f137bd6ba227ffe3b292145df60872f9,
  0x7fffff9ae4255e3b298e480005c98420c70e10235e7ffabe6e75286fe56696e7fff99aba1e40d26a3dec,
  0x8002f5bc1367aef95503a7fffe2cbf1a94023114428006045e0d6b4d0fb602e7fffd268a791cd7ab3d95,
  0x80000bd50061c433630c27ffea57e6a89f724d031a80012a94a19336e3b68c27fff039b5fb81264ff8a3,
  0x800328c56990f6fee9d9a80014d8f7f6e7473b883c800008b1e494c74f20f8e7fff76d1f03ddba7166cc,
  0x8001f5f8d6432f63e68ad7ffdcf2b98e0ce24f132b80026e0ddfac7d146cd867ff95445479e0f605d05d,
  0x7fffbb1599eb32ef43a668001417aeb00d0be87e507fff4ec2738b1845ed9e7800049e420cf154ea3716,
  0x7fff9ea8a1a623993720d7ff5c321f1e0e7c57e789800af3b49cf685ed564a9800077a6cbf832b94f389,
  0x7ffffe50d0b06a3ba0f847ffecd176b16482c161e880001a68bc2f78b71073d800002833f0c558694b87,
  0x7ffd5113843e556359608800020966f707bc51fd757ffffb15f84cb3572683e800051ed8f393fe07a15c,
  0x8000434e33931fb519e0a80114d9fcb4b3492298ff7fffb21380b26374042217fa0de56720bb6a1b0c05,
  0x7fffb81ba8000230d21e77ffe3789eadcbf9e909e18000419d52a18dbcef6d08000b8a9e0056d77b46e5,
  0x8001012a7dec19fca1e9e7fffb7c07f1405975a7a27ffe7a22258ec554dc6f77fffed5ad71af529fbbb6,
  0x7fff460f2e661ce3ba18c8018679da0e5affe2091a7fff7026e41179333cb507fff4928a943aa755c219,
  0x7fffedd02147ac9e97a007fff468c19f29431f6bc2801417f4f2783e41d5ad08000b42bb87d5393000f2,
  0x7fff874f54419cd708efe8000e9e1af49bc7c044fc7ff74b954da501dbcda767ffffcc8bea69dbd6766a,
  0x80008919098b4b246bebe7fff2b359b9ee3c517fe3800228de54895ccb6850b7ffcabea714c839e36280,
  0x80068947fed49b05f450b7fffca144bda225fed4a680031d241b6c71dd21014800236a4f0fbaf2e78a24,
  0x7ffbe48be4108caf315667fffdf162d6808e7e88f07fff2b5a911a1a3d108fe7fff53f3e7c6dd4c7cfc9,
  0x7fff5db381b37b48b713f7fffecc03523193b4fa62800017f8f31bf1bb493817ff88e4b5488c3342718f,
  0x7fffdc99ee0fd7bb137a980023c305e3c1e681d5297fff0de3124711885f84080011768d70c8d3af863c,
  0x80008158c0cd87f3dac187ff119354a45abc85bbd17ffee535ad7d35f7f38fe7fff96ce34774693e7abd,
  0x7fffef19b3e869ee4925b7ffae8c95f51d728c153e7fffc245c8095d92c1c2f7ff9f3908441a93407123,
  0x80001268478023d07576980002a6c6650b703a3b1380037fb20565c9f6bc9b97fffb3d6057950289568e,
  0x8000077eed10e7642a0ec7ffffaf8f8d3625ba13107fffe66316aa24c1acf4c80002cbb97c60d88d8822,
  0x7ffff20ffdac7c514ea477ffffcb5e0dacc49e11fd80002849032ccb9fae6197fff8665884647257b337,
  0x800024dd10fca2916e26a800009678435ba98c76da8003844c8e3c98e940cbc7ffffd16ff167ae9c1f91,
  0x7fff614c422dba54216b97ffedca836374dab4bc038000032f501a0b86097ff80002c01e9daa6868b769,
  0x7ffe1ea80b76db5daa7c67fffcb221417472dff56b7fffe1f6246627e3ec08580026ce3f48ed5e5c83f2,
  0x7ffa48602cc66924031df7ffabb0016a76bcce764e8000741c8a3d75d764faf7ffffda988cee8e81aa0f,
  0x800007ef385e0db8b41647fff9d67835436426996580030aa0c40746a7bb01a7fff797c31267ec055b4a,
  0x7fffe4eeeb21b0536871080005b33984cfb55b1f3a7fffe653c8a571802ca968000007e416ee42dc52ac,
  0x800029d4d3a60007105398001a1c1e1e2129bddd227fffecf5b85b18e6f6be18000293740ef77f307a50,
  0x80002565bde3db8f02a248002e0e8ea121e7c5e7a080000a60c2099af678d4f80000e7dfa3e4746954d0,
  0x7f9be8877480753b69a927fffb9ee1e06359882e647fff3f069ae049bf9e55680007cf797fc22f72b5ee,
  0x8003df6d63c84b44a1da37ffeafeabfa29ae163ebc7fffce8716fa1e140dcbf7fff4db2fa21f998430bc,
  0x8000fcc8a5fb6048660337ffe7625f1a8565ba460a8000383e42cd42a0f7f2980008b436b0a8171c607f,
  0x7ffa9b84ccaf8ea30c852800031789da053bcc0bb27fff2beb94f7dd106cf1e7ffb47d1f0d159808ffd0,
  0x8000468134a6b656239d57fffd7eea05edcfaba29f7fffafe0920faadacb5707fffe225bf28fa15c3e80,
  0x800271e908e5c1aa07afe7ffffb776b8029355db1480001a2aa0c6d2567e30d7ffffed3c215b3dd74f26,
  0x8000533f74e533f5605597ff69ea424dc5c6bf7090800c7ff7777f527ba97f3800151d243bdb73a0bfb7,
  0x7fffa42dc91301cedaa6d80029d4b1815e90c332af80046092a2416fcf34d3f7fff2492ab98600b33fe3,
  0x80012c72136dcaefb520d800161e80cf817176e39080011fcf76eabf0992eff7ffc99154e2541de7fb35,
  0x80004a65783bce8985bcb80005d2fbe54187a7b7fd8014e70bbc743b6c8fa5c800e64eb40979991195e0,
  0x800402d646a34797f484080041c3ad1b45cfc18eaf7ffd09ec3c17752d38f78800318e7bace7e66e7ed4,
  0x80053025d7be5f0e7af247ffff8387c15a12bb0d14800022b89c7554d72af7c80001b0761e0ab9a5923a,
  0x7feb8a98205fc1f33fe107fff3ff353f948387561780004aaaf095d00108780800032564368dd1ec7aea,
  0x8000bdc407fd8fe774e7e7fffa29bba33ce1df8cba7fff1ad7492473a76c09b7fff51293530a915c2f79,
  0x800105bd0f5471098b4c67ffff5b9410ee4b6b835c8000778f0bdcbe6c060f47fff6a2a4db63dfa9bc5c,
  0x7fffbb51c79e2fbcc72f67fffffd60a628a97ae7f6800192a1f2b08a2984abc800006e69221b65660b35,
  0x7fff6a094256213d0f9f0800360ef47694683c378b800014569f99010e3fd9980000206caa38e6a726dc,
  0x800125a233223e039227880007c8f3fd35eadf613a8000b267dcf139cb4af817fffeae70dc44bd0a5953,
  0x80000be597a786809075c80004f2cca283fb14a42980030338aa307743d33177ffc792aad6bba8227e1c,
  0x8003f91a99b4d49a8248c80003515494c251bedd197fffaafa28185a80d227c7ffecdb2bcd140fa458ae,
  0x8000e68f45e2c64987a1d8007d356aa656f0ce2bdf800227e05da81b2dc07b380003f0da9c1a735ff29d,
  0x7fffe97680963041e584f7fffe7d5baed27903199b80093e6fb19d3bfce5de98000e0d9f88490ebc8eca,
  0x7ffe5b6b53c02d5dba1c67fffc1b1e8e490e9aea948000b157bdcca1cec943c7ffe6058c50bcfd7b907a,
  0x7fffcf2a9ef253d1bfe2d7fffe335926b96482deb2800009ecddfd5c321122c80000e83db24618dbb578,
  0x7fff8b64198c8fb10dd2d7ff397f8b8ea050cd6a9c7ffffffdbe10e17e5991180000c137a5b7c9b713d3,
  0x7ffefb7212e23d7e4c40180000f1596d5d8a4b62fa8000820158ebf8fec02737fff7b32817838f9054bf,
  0x80000a9e64add0c83c2267fffc9dc2084536ef952a8002e484353cb83a2c68780002a0ae4ceda0eb7000,
  0x80003963e54f3a5e1adf97ffb001f692663bcecd9f7fffc0ee84767f162984d7fff2722816d9f741f3c2,
  0x800178e51372766b444947ff9b2f2e929adcd210c07fff9f1d1678dc8f408fa800028e784aa50ee9b88b,
  0x7ffd71fbaa015524aa9577fff2d363489adfccba228000b72e05f45719a99e880017966a6dd748142843,
  0x7ffe7b2e55759d1a1adfd7fff076df33b605a5b4df8000355e35e0ec53978137ffff45fd9f8f270f6ea1,
  0x7ffea5e9a2455b39b88bd800217cbd5bdb31cdfc90800175c91b1f16f64a7457ffdd980159fdd0fc22b8,
  0x7ffff1863047eeb03cc868000fd30ab3e3c2fb3cee8002dd6df52fbc6a164cf80003783e3241d0ed37c1,
  0x7ffc85dd72faab73d4a777fffb6b6a30638f9f203f7fffd7ab2667117c482f08000934773b49dbf56d05,
  0x7ffbfde9b7495cde4fd478000363edf25cef6f3b437fffcf78f2988e25b86267fffc30f1d240633c31c8,
  0x7fff90ca2e6c0656b699f7fffce9a4ac4d7f3b88a68003c7fba76acffe85e657fffb806657379b51ec90,
  0x8000564989ea4c5d24bde8000ab7ec82b4a830c7717fffd1acf4822b05081cd7fd6865dc8f5b1887987a,
  0x80000f95a948df1b1b3447fffa6623f7bc1f6a3168800210ea3768586ea4fad8000757d6430aa0e86137,
  0x7fffcbc12cda48d6e56cf7fee1fd2b0de35e3702aa80002cd25667ad937c88280000f5a61b85828fa1ff,
  0x7ffffc273062f166588527fdf993c4199aae084b8a8000160e8fe643df160457fffe033d3ad4d136a8b5,
  0x8004a7130365167fffdf4800005efa4a5bd1cd3f3e7fffc8ecd450b795c75547fff957d41e005a62534e,
  0x80009b651ba4a7355a61e80006598add7b2ca08742800180a2e38a94ad655ae800093d45653c8b0acded,
  0x80004fa19d56d6c9ce8ce7ffff4a6e54296c0e67088003de3a79de9571073e57ffd1d60bddc847cdd40a,
  0x7ffea26f2a02f6e0df14a80008c906ed87dcd5c5cc7fff0c11173fdbb214f6c7fff59a9ef9e0fbe4725a,
  0x800f359b568e3feb7272b7fefbb37b6144b76441057ffea8133b0aace45a087800094493d2dcfd0779ae,
  0x80002814e1871e48cb4cc7fffeb3e4f984ee8c250880005508f5ebcf2a3f95d8000af5811369b591529b,
  0x7fffc552d82537d87621280001fc4f77ba603abd7b80004d8f29039669856417ffff0f810e9cb02b52ab,
  0x800013682deed9322da2280006046d4fa3d129591f7fb3bebdbdadce9b0a59c7febe92481b95c9439b5a,
  0x8000410d773b26137ad3e7ffeea46515f61b7a6384800043b01aba8400beae37ffdb0e9fbd7e7e77770c,
  0x7ffff3d0bc25954cf30887fffcc6233f1ca7ede6578002aac011ce9d555f4f67ffffd688c6e322a8f193,
  0x8000097047c73086c743c7ffff66fcc063ad9b55a57ffffc76cfbd285a8de7e8000498663437a68d2f77,
  0x8002a7391a5b6bbf0018e7fffdabcb63df7a30e41b7fffce66a561560e7ceb17fffe97fb68ef8b1c18a6,
  0x7fffc3ce08474c01e77f67fffe0406026c84c66c5780007ac480487fbd152f97ffbec4940a53ff6a41c4,
  0x7fffe9091b4210b24648080003bbbfd6d07fa5ba2f80001c09f9a95d7a49eec7fffeeffca6de91f2a928,
  0x800664a29fea1cb892d397fffe001d25339b3bb836800022c603573015f7b648000601a7d45035d80205,
  0x7ffe744b322c8b78ac913800032e3fcb681f8950e97fffd9d5b7330a1c4821980007d0d362a1a946ff3d,
  0x7ffff453127651a02b8327ffff6a08720cf91f22257fff62f1c98a35177469c80014eab20d2513fe7547,
  0x80002ab71229b58a1f308800021f02867e678fc3798000079dd78a1a6498f3a7ffff5ff191c481500409,
  0x800054aebe85060f0a9c57fffb82aebccafea4ae4b7fffe8b39704e831bddbc7fff920b9d84f9f9f94b9,
  0x80001134ff220057cabd1800023cb5987d4d2c9ad07ffe41fa4108dc2219bde7fffc79b38594724f7766,
  0x7ffff69fa69e8863089847fffe8735f34eb66d246a800036cacf7d2e852903c80008fb736bea41b62d54,
  0x800016633e71a0be586be80005624708776c1937ee800077e7a01e5ea00848b7fffc2d41a1f238fb5ea6,
  0x80016d7c0d265366b86278000d0fecea45b5787d527fffe0f006f3e81d4ea1f8000142a8bcf687f9540a,
  0x80007b52bc4582a249e1f80001d4af0baf48cd15c9800026aa1ee01505b741480000b26ef783d7264858,
  0x8000175d4b879b54567b47fffeaad05f7e306ea9c17fffb28db4956b878df4880003482a6a352180edc5,
  0x7fff376657077b66a22f07fff3d2e439bfd22430527ffe1f922a44154cba6cd7ffff3f14027cb4fa69e3,
  0x7fff74d276ed278a6b844800076ce79c45e582f5bf8000d89b36dca18354e667ffe311a9edd9e2522353,
  0x7ffff0e2d53f93c39ab657fffbe46457cbea9a7eae80002a0cbab50603f1ccd800017f858327292ed970,
  0x800032aede5e00489e62580001114cedccb4ea4c0c800023b305e42206dd8f18000140a070ff85c300e5,
  0x7fffcf8374779edca588f800093e1bcefffc1ccc6c8000164fcee5c9cf468d5800e90da65c54434bd0c3,
  0x800034bab0843f15ec40f80001a6568552f5232a5b80001ea93014f300afa7680000c21965bf120adb33,
  0x80007996374f35cc96a238000507542b87b17d5b847fffff49887f817fdf435800005f92f2202fcf7fe9,
  0x80009508e0545b8b83b0a800017e9022be4ffd2d5a7fff557548c49915b076080001df34082118615daf,
  0x7fffc56d472aa6bc558ed7fffb83814c7fd5749629800135b4f5f72462ebcda7ffe6bd69be76774e8441,
  0x800091a947db74650396e7ffffb52cb60c239dc70c8000670ab1da3da20e5378000326b5b0bc02e2a7fb,
  0x7fffd2b17b6b591512b2080033016277107992234e80006f9c111f3561127e780000f298ff27f1861fcb,
  0x800158139f1ed0ea8148e8003a8f11b281f8a50fb68003a198b8da1f980c4227fffcb7804b9995bbe3e2,
  0x7fffd4c2143f7bb12a2c97ffff2bbc64e0b557cd8380001221891bc16befd218000120e9bff8e1e2fe04,
  0x7ffff6d5b14b7ab2ad2bd7ffffe7d094c6f9fc330980000a3637a915daa8caf80000f75eb36dd1b0c1bf,
  0x7ffec6a1e0bdd6796819d7ff61018409316f834e9d80003415202539de619b38000079f7869ce250a804,
  0x7fffaa6f5f171b8a0df437ffff756ad667e57444dd80000588b185dc69dfc958004dd4b9b48ea41f8bb9,
  0x7fffecd355da3a4c5d04b800060e1456b9960e1f93800026769785e5081b141800032a1d8102a15316b0,
  0x8000277f53b08e10edd8b7fff78990082c6f0b22d37ffff64c873a5a8734f5d7ffe2f78301c13ab778d9,
  0x80002822bb2a42d2c3e9c7ffc2b9bbc1043c6ea3227ff712aab4bc246a0d8bf7fffd835ac917827cbc2e,
  0x7fffefd661f6aff5479c17ffff5ea998fa7be0adbb7fff4c82f88e49243920d80005b915090a5db94ec9,
  0x7ffe2425825c6811092ed7fffc048458075251151b7fff83955ace0ade195998000347b600cf5312c0d4,
  0x7fff3fe4b66aa67436fab8000edbdcf012775302287ff99c05354610d98fdb1800406053843e16cc0805,
  0x8000029386ecd20edd328800038b79696d28070a0f7ffc834954148d0276e187ffa61403ac728e135f3c,
  0x7fff2fc19b67741b7462080001835b816438d04d93800004d34c120e0a1c99d8000078bcd574a6a12574,
  0x80009e642dd01d16027a380024eea6c89f5b868b6c80007087954c61d5059557fffe54e84c75e7475c44,
  0x80001880a7a8ead2cb0a77fffcccad57440d2ef4fe800011cb11188aaa0631d7fffdd49842a73732ff9c,
  0x8000027b4d6546bcb8830800017fb28283ee2e6ad48000112d8ef2d4165ed5d80004635f34a0f7ecd679,
  0x8000003d04f7021fd1489800115e5529e4584afaa680000db7d68515a8e5d688001526f406e48ef1f0ca,
  0x7ffff0db71a90c84d1f257fff803849e39f4aa58f48001de3be827ae6c00d3480000d5d48c146daf8302,
  0x800011d2598da82fdda3f80009a8096a90afcfe845800054712abb7501025c1800034d3b1ed090cfab7c,
  0x8000dc4d6ef272595c3027fff8c0b7820908bd0c9b800038b650c76606f372b80000f29abc9aed5703d4,
  0x8002892c823a3481d67c47ffff83edca1af837b5097ffe559700c82cbc6ee158000211629c063cfa6652,
  0x80001216bc82b1d3c3b937ffff1591f973f43e454b80034ada009ccc5768ba88005163d03f66176d976c,
  0x7ffff0f55ae90ba8fc42b8000024b217d5c4814f6780002bfe29702415bfe938000088980d31e1cf872b,
  0x7fe2787377dba6ad7a8207fffd113604e988f6b02e80000bbfb3ddda4fc406c7ffffc45a3a631f53f055,
  0x80002c76f43f7b9e1642d80049bc738c056b0ea2947fffed6f92bc3225b092680001d12bcd2929860a3d,
  0x80003622d1195a504dae27ffffefee35b8af25699580001237d485623f48a59800019bf456ea3b8fa92c,
  0x800010871f3d155f410aa7fff699d9a5c7c690e7b57fffcf149eedb5efc8eb37fff2e570a5e27c2e7b9d,
  0x80005c3b7c81a610897567fffee014502f3a8508fd800d2afdc6e122f2e98ea8001175c237e0408a0c7f,
  0x7fff5569637add9e872107fff0ab65780740924e847ffe5ea802a8205845bcc7fffd01da28975372c1bf,
  0x7ff3d794ab24483ca00b980005204ffa55968229c57fffedc409ecdd5efaa078000e811401235a1567d5,
  0x7fffaa92b1dd478160a5880007c3aeefdacc8b09bc7ffe773ba1e6d874a48fc7ffe0d6ccf69e0a4340c9,
  0x7fffff671b42538698c5a7ffffcc55bd8e9163ca617ffb1613d7ce22bf085c480001a29f8ca6ae8b660f,
  0x7fff546d3b94b01c70c1f800187c23c1ccddf19c05800008a0db2224ab563a48000026e9b49b24d364e5,
  0x7ffff6dacf945ead1aaf87ffe96aa4cece85cc15fe80007dc1eb10f82daa2e07ffff018e92dadc752653,
  0x800051e5c6662dca04f80800012dafede0f7c5ea4a800010835a0307bf5470480003b2786b339bb4cb38,
  0x8000245f93b514c69b6d87ffffd8b5c5c546eae1cc80001a6b1974a9473f9167ffffa7614247b4e1df7d,
  0x7fffca4575dea3b9dff50800016ae2c4373bbc3e9e7ffffd242484aa1b3ecc77ffdc362419257a5c4cc9,
  0x8000079f560e669e87b9e7fff669cbec022575149f7fffdfd4dab9577d65b7a80002b20a2395a81e587a,
  0x80001d0e36cea876aa5f57ffff97e623533fc6e4f980000a19d1f569528e61e8000171b8dca7af734f2d,
  0x8000007c5969a3a162edf80004cba3b5fd3b11e65b8000695cc7f44ddaa3fa57ffff3aef75420180f544,
  0x800015f8ce285d258255f7fffe50bdae72b96140ad7ffff528f333630d79c977ffffc7a4fc5a3004ac25,
  0x7ffffd70139630c34422f8000030f53c0f3f1cf8167ffffe102a923e4136f287ffeaf4208345c895ffa6,
  0x800011032dd2c00d09c3d7fffeaa7d4638f89aba617ffff9218035297a07cf48000110e89965dd5c1a58,
  0x7ffffd9a1109d9e9c93377fffffc7178495ed03f698000152d4071cb907c9997ff46054e21491b5c085f,
  0x8000047e0d54bae15163580000d726b288d811a64c7fff881aee5c0edbaf76e80000ecdf97960fb3222c,
  0x8000449a275e249f475487fffcdbbb92e3b86cc1047ffff5df39a3a8268859b7fff790e723a247a53d1e,
  0x80000a5b0d0c318f297ea800020f8b97845ef510e57fffc08f910dd28d1ced07fffd39f77082667afeb0,
  0x80001827eb1b45c5cfb337fff3d223aca08e6dd2367fffa6f2fab77c8d9367e7fffe562a716973520fdb,
  0x7fffec0758b73cb288b1a7fffe8d6d607ec494123d7fff33428849a8849ba7280005ad09c7d912868a02,
  0x80000c2871977ab5751eb7fffe3df1d3f3eb49dfc780000d50d0fc3f84203727fff4379f9d246178413b,
  0x800bc880c58a44c2977ad7fffa024893083302a6a97fffefc173cd6073484dc7ffff8efbdeaa1a654aee,
  0x8000056c02f7f2597f8118000091218a74c25512857ffff7f20cd4c5d6f50687ffff309b91f358b42596,
  0x7fffd40da6904a4da78bc7fffe65350f72139841eb7fdfadd55e859d061823480001a27b9e13a7218fd3,
  0x800006c3501ff3010694d800012fe03306ecc8a25a80001246fc7a490387d877ffa84e8250c0e479b4c6,
  0x8000ef52707b12f446cdf8001c2d1a03974ff9f73c7fffe88d132f7cbfd0a3180005fd97e9f16fd44516,
  0x8000cf8e3fe5ec26c4c617ffee253ef22e3a2efe368000641c270b814dcd44f7ffbbe05f72470f303e48,
  0x8000da241ebdb4748711e7ff83f28d772b2d900d7b7fffa5c7cf117bf58164b7fffd7cecce11eefe5f9d,
  0x8004695025b90ca890d2a800c1f110700ccb3298627fffeb57509a9d24f7a3b800601a5bbe378bec5410,
  0x7fff7fbc1e30c34935bf28000424194d7f78ab72ec7fffd9bf38227fd16ca098000551a0db9c14189c6d,
  0x7fffcf1beaf44ff4849137fffdf58e1d65df303bf17fffc3b4d3900596ccb718001311a40e935c34e9e3,
  0x7fff60b07fedc5650d8047fff9d6f2d003ed0407de7ffff013998caadbc395f80005ab7e5d8bf8d30448,
  0x800001bd750f804a18b9980000d51b00e5bbc0602d7ff0d2860bf6745e9129a80000acd09964324c4e3d,
  0x80015086f0a204448a4a07fffef1c2714ce8b403937febb4207f99ded1c443f7fffedb0ba5a71ff6247d,
  0x8000007ae22f7e8fef2d580005c097f77fcbb8c3a68000e6f25c602415d35e77fff75d4356b2dc9a169d,
  0x7fff3a68fa3a1d97d7076800222d5c4dfb0086657a800026c00f03633d5fc73800084f4aac06749da598,
  0x80010256b7b10192a799e7ffeb362fc3ee18b893ee80000d0b82276421453747fff2db2ee67e2caaaf88,
  0x8000639dae09d3b4cc9a97ffeee2639ed703877367800063620940255c77b557fff227c02cdbc798ee6a,
  0x80002fac0bb34435a687980076cdbb3120191136707ff9a4169022db23763d27fff7d00e41858dc1144a,
  0x7ffffca6e28e5581606827fff9dd27e2b9b4cd379380000445442979dfd081880004a19d5d99bf079145,
  0x7feed3914513134e40fd07fffd2a3efd6da1c3aa6a80000a131c6720237190d80002d6e5eaa68fbca712,
  0x80000b0675bdb8b979f5f80000594cd1cacc5308277ffff1a1ce7af069a73a67ff9c91763618fc2fa7aa,
  0x800031ada1a3a44a1434e8000e2b521c3e9de689657fffaf2803a0974bbca448002a4f322f325fe88dd1,
  0x8000656a9b0e08f38ae037fffd24de48814a754915800060132f3d2a2a58b8780000f7ba32350f18b431,
  0x8000159e9195e650b192b7ffddfee05747292026397ffecb79221d4e0081f3b7fff9d8da80712f41b168,
  0x7fffc55a6b15a58039c188000232fae733d47721b87fff658d3f281aae3583e80011494e369b1db2b673,
  0x80000a37e44955b88fbff80002cec6c176366bee327fffb042f2f0bc48803f980001e495c2b17abc41b1,
  0x7ffff1587204b69292e027ffffc649c7d0ddc772357ffde00565e72e26b7e708000018b9c594b69e97c8,
  0x7ffdabc989a8f0e62e4ea80003a22ccdb633672eee7ffb1605d1c33163121d4800011c202ec164dceece,
  0x800000ea2bc83a6c139bd7fe69aed91ff23c9607d07ffffdc3c336e6220fcf67fffbc0bf22ebe8474917,
  0x7fffd5e9abd2094a7e86a7fffd0ba6f583e8f51e327ffff9a251768e2349ad97ffff76a6e980efc5bafe,
  0x800110fe9b64ecf0dc195800009d6fbbcd9400e66c800070d8999aab87eead38000ba9c376ec7bb16fbb,
  0x7fffc5ffac9cbe5320962800210cecbf3610117bd97fff5bad2accad637e2ee7ffebd1604d8fe30bbd81,
  0x8000057c2d48eeff2ab2a800615faa5454d12a1ea67ffe0e5c1ca77c776c6a97ff9b75951b44ca7f3fd8,
  0x800004f346ba01c30ace67fffebbda3b9ec558298480010d8fe740de4578143800065022cd1b232b99d2,
  0x7fff9869ae98280d4b7387ffff1787b73dbfbb50b17fffe92747f3ebcef8cb180000e7a3795dd81994b4,
  0x8000c87394750f6fafdb28000600b4d840b01d9b3b7fffde3dba23e58943a547fffe5ed913153fad6815,
  0x7ff301aa5b3c7b8ecbc668000611eb0b52e2f4dd397ff670a5e3ad59b492ba07fffcb00e35e9d17e9b33,
  0x7fffe7c4aed05a2702fc97fff9a2f4bed32883754b7ffff6eb3fc35a2cab0427ffff3bd47bbca218e8e3,
  0x80000520fb6b9f6bb038f7fff707f90ce2e6dda6b380006a3f0b4757d7b23057fff919879f3713c96564,
  0x8000152665cd2186ecbf08000bd5dfd4839f9e10388000487691b2b1532703f7fffc3a06c1b14f026585,
  0x7ffed3482c5b2acae83cc7ffff27d5109c17a3ed0a7fff7dc81705161e85cf47ffe55215a28f07eb0f3d,
  0x8000030b90431d287795c7ffe868259c9dc72874027fffebc0c51c2231f57577fffe7857fe9d900f832d,
  0x80000d1da7101855410927fffdc1b4f017d0356cc480001570351a71117977f7fffd6f4cb1e3d84f227d,
  0x800006bb3ee00945de4707ffffc48e775b44d2d0e77fffbe7c4e38100007151800be0cfd8117eacf6283,
  0x7fd30c228c620a04a4fa87fffef72ee3d93b8c2e557ffffc3b8186e72c559127ffffc41065bf60a7178f,
  0x8001010b25518b7c7e30c7fff64ffe0c457eed24f38001569d89ca7a0c0176b7ffff56005d8acf57d40d,
  0x8001029aed4b3eb407779800140817a612b09834e580001645af241c626a096800356427f82fbbf120d1,
  0x8000f6bdf8888075dad0a800080361f02e43feff157ffeb65c425a5ea14184e8002b3bd36853bece88c8,
  0x8000e7124804e3d6310b67fff128498c6ef5baea6980015962ce9a1f73b1e547ffe9dca45dc05a63b76e,
  0x7ff4ede3ef7b563d9a7777fff58bb30a20e7936a1180007e596337006fa288c7ffd5e082ea71177bbe0f,
  0x800003c599ff3656f1f6480005c891206f07e84d1a8000672c0b8c5e0f4ef3c80092ae02eea204744185,
  0x8000073214587893b22797fffe929eb1c20e2e60b880001816f8801088f75b37fffb9fb5f043f22ee506,
  0x800035491f1c4ff1e71457fefdbda5fd3855dcddef7fe34f7a42115206792677fffe860aeed0c9811d98,
  0x7ffecc5b666671f150e657fffee565665c97433c2c7fffa81eeaad967089deb8000ed55ca7fd8a017ac4,
  0x8000837f58d12c680d7827fffbb0873ca5430c958d80009db279f2cf85d2ee88000580a8fe3018dfc1e8,
  0x7fff9ecec2b93bd2478d680006753bddf6c2b96b2d800005169aaaf06f2e011800069d34942d3d7eab75,
  0x7fffe16023fe9cbd24f4f80003269e3366623be4967fff5802d297e1561280b800012fd1e6644dba5dfa,
  0x7fff94290d448a56d12687fffec16efa7bcbc205f78000131753cf3769d49d280001b3dc2df5b19d8c1a,
  0x8001bd1467dd6179726e47ffffd142f380059985f97fffe9bf2714c1532c08a7ffff4ef931084edf4842,
  0x80000a2adce1a8e1ef68a7ffff554fdcd1a2b67da38006dac56cbad86c06ac48000120682e77ae06f9ae,
  0x7fff6985404df63dc6d00800135bcdb2af7d63ae147fff46158d885cd9181c37fbb1d0c6fb9f24cf61fb,
  0x7ffd734674ba3806983137ffe27bff925056920eba7ffe226353faaac14a80f80006d2bd796b17d38b2c,
  0x7ff1322ebbad52f2b325f7ff2ba1e671578faac0eb7ff8f861717512f25cb2280025abcde7e0ab653358,
  0x7fffe4bd1d26b63b2e846800080b72b2e3aaf260dc7fff771b035319333716b80109396b8d301d5e32bc,
  0x7fffdba36ec4b24306a917ffff984c84f07f819bc87fffe67825bfc2dc488ee7fff9715b6576baa36eed,
  0x7ffebbd242f2cf17c85bf7fff2aaad8d6fe6f57e5e7fffac26ea44ef0c37f447fffd73511fc7fc4a6b1d,
  0x800142bdab5cb72133e418000afbab7ad358b6137f7ffffd8180b0875ee583b80013b43b587ab9293403,
  0x7fffc40e712a80d001aaa7fffaff0f3d12e0cd4ace7ffb5543b3dbbe09e9c4a8002037f9b4b6f436840d,
  0x80006c84d9d21b406a5cd80003014d8bc4473f45137fffb47220bf4e47f227c8000aa2412bcc9eda3a61,
  0x7fffd83ccf811359a4ca47fff43592912b557b64197fff8116ae7cb8735768c7fff8bc7fcd32ad010bde,
  0x7fff50003764491f3d5c87fff0868f7d63f0bcc7e97fffb676b3fb640664ce780005f7a4fd8a4ca6d1c0,
  0x800010a97838f37fff6d97fffd9e0483ccdcb0a1597fffc94550e35e6c5de367fffd25fdc803c33565ed,
  0x7ffff8c519bd03fe8dec58000148ca5b97eb62bc977ffd9e1f81f79c736c9df80005db017befec0ccd98,
  0x80002cbe16ef9ee086c7a7fff737d9b7267bcda887800036034bb986a5d33108000af6a85c1c1dbd9235,
  0x7fff615c05a175b12781780000b2f63a64e1e183d47fcd8eaed485573fcb5767fff5698ee00aedc5f4cd,
  0x7ffb36a63ca84172a23217ffe35df82ee11cb3d87d800530cca7f37ff5ae3f27ffe94735d9876c6a402a,
  0x7ffb10364e215efebcbe17ffd0bc799e831a7fcd39800186bfb06392856690e7fff0e218b23dfb4e5b6a,
  0x7fff9f4a5c08ee486f13b7fffb22d21fd08914b1e47fffb69cca492d3c6f8b48000193d425f197fa62c6,
  0x7fffc2a15a2aa48e43e347ffef56a8a984fffeb1c780013793ace4d03dd51c480000df5d7aa22366163b,
  0x7fffd6e3dacfad1a42fed7fffff99a4282ec5fda437fffd59491ec7c099f6a17fffe242b5227940d3928,
  0x8000110d627d9132f5f2b7fffa579568fa04051fb47ffffd0bca82d568eea047ffe956b84bd5075c2ff7,
  0x80002e44e09b3b22b3c8b7fff977aa69c83bf9e6857ffe7be334ee3fafaeab38007fe7030e98f7b5c8a8,
  0x800162d20b8ebe741938b7fff9667ccf6665d1030e80004acbc9b6c4d686e5e7fff71436a442ca434cc8,
  0x8000f601388abacd0d3948004b7b363844aefb98077fffdef6e564f31935cc98000048462b6bb58120aa,
  0x801574db8acdfc7fd09487fff86585feffdc30dc787fffde403022af52521437ff3a68ff524b6083adee,
  0x7fffc0bbe634f094250527fffb0c071d2c2be8226b7fff500ea1dce60a31cef80132df8245bdaca8c052,
  0x7ffff52b97821dc2fcfad7ffee7de0ea87df4d5e4b800004fbb418bba5661e87fffd858ae8554ec15ce4,
  0x7fffc3bd2c80db5a4cb857ff4e659740a73ccf268c7ffdd9a3d18a664a162578000417715105c4c7951c,
  0x7ffff2cd5318aa2eafb667ffee9bc416cf0f5285d980008c9f4fdd8c138ea877fffeb1f71b616920c8d0,
  0x7ffdf225c0281704e4f1a7fff31225a6f1e7fae6597ffff9a4327c3eb6912097fff564b245aca653917b,
  0x7ffdbc07e7ecdd888fd7d7fffdd1da18b6489a3e41800641e7f511edc9190c4800f2fcc5fd5d84b932fc,
  0x8000765512e47471b08fb80038c56c5934df3963fb7ffcd10d5d0627b61d9457ffd8ee2de5243e01c5d7,
  0x7fffbfb6cf16fb3e0728580003b423dbfa8bf4fdd97fffef5cf6107409834c280005ce96d491378f6d01,
  0x7ffbd93c2ce95fc97010f7fffa85872e5daa50d9467fffda29ba74b1860babc7fff32802c1a3746821e4,
  0x7ff9e9eb8f2b5e8c338287ff8cf4229d7c4613eae37fff94bf39514a0c7afc0800020b888ecf2f24e73b,
  0x7ffff49d74e88196d57847fffb9609fc7011deeb8b800153a3afdb9616644498001861e97aa822dfda5e,
  0x7ffff8b4ab948276964b47fffef80b6b94a11eaedf80002bcfee122c1e5d3ab80002e296a16af1f2ac6a,
  0x800005b7638a45a28694b80001bdd08a584b8fb6317fff51d2f5efb82b191b38000af06f15f37e812267,
  0x7ffff67413f6e9f26e6367fffe0059f7a75b51014780005e92b3506ef96ee2280001c30ff7dd7b6a23f9,
  0x7fead7b8180b18993bd588000276c8ef9449193f8c7fff794f21fe59d1a940c7fffd5af85f99637f02ff,
  0x7fff7da4ccb06d7641a9880006a63232bac49eb8aa80052fbaa704c464d8b7480006fd3f8b78f35a8e52,
  0x800065e50297f6ce099eb7ffff58d3300b9e4352f58006d4fc2788b08b90a757fffe5893d1ac40bb3daa,
  0x80000122ccb187ad87c5f800004565643c43c378587fffea4fd40b3d01c47db80008140f8d766c0eee0f,
  0x7fffef6b53441bccc1d9b800035f70b935da849a7d800000d2b662be00ece80800005d54abfb9f335ff8,
  0x8000063a70397134ede89800090b78dcb1d6d1d6f080008144a3cac9e7faaca7fff740b37140e23de4cf,
  0x7ffdf35dc39ee2eda6af87feb18e2f732e0863096a80006bd97460e0b3df0758000a106b8ce80672272e,
  0x7ffbde8eae5a3b954583a7ff9d2d835c3ef85facb780032cdb2af8d6a3bf0e17ffbf752bfe56e58e59ef,
  0x800091b9d53aa4015aa497ffec7803b417a1bfb77e7ffe99080d1e6e29f747a80008702f9bdeb98969ec,
  0x7fffaa0d8747f221b05817fffd573dc9fdf8030f3c80000bc3705a08d682ac380001b57ed22c98fe6e3f,
  0x7fffe5d9fc67de7987388800022993ac70737195ae7ffff43ab9d2ee38b1d2f7ffe6a8b7b93fbddb1202,
  0x800259686f5a72334807a800008fd6a1140c8337138000af995486402eaf4767ffef47e7ae486467bd05,
  0x80098f1bed8764887cb9f80048dd4b11684b22e58e7ff2b6935e00c610bcc4b7fd7301272d3012119286,
  0x7fff93f3d8b0d538025f47ffec87b329ec419335d280005cb1f94e291b0e93d7ff94c38f8ca2a20b84eb,
  0x8000711169d7e9969790f7fff1d738a6b266d3e8647fffdc492b55fcfcb2a6a7fffdb7485a8515c9fcc0,
  0x800111579d0d5079be2e77fffb673960917a8abb407fff4865572117aef34398000362adab2717fc4189,
  0x7ffddd58d4827fa94617d7fff51d268c1b02570e8c7fffb3786d00e6e0e0c5a7ffe8cfd78441242839ac,
  0x7ffb43bfd6f258729f27b7ff8b284b499eb8543e527fdfec0a6d8b5d44c8ce77ffe111058c608d85edc8,
  0x800057db8c0cd3bfc32427fff8d86449ab9edf9def800046a4c8a5b2cd28d4c7ffda5711413e8f18655d,
  0x7ffcf4b3f4480d8e57d88800346faff5732610987980001f6e97033e762c14f7ffff58fbeb3258f6d3b7,
  0x800024d9c72ac9a02513d7ffff233c0e4891814cff7fffe7b100d5852741d207fff9efee47a1333a6748,
  0x800030073ea589435598280001e5442ca08ee8a74b7fff87157a5b8964b73067ffeff90a1312433b86b3,
  0x8014fabcacd042aeba3d37ffa938b27ff11bd002b57fd0e7782088fb0861a837ffe72691ffbfd4bab458,
  0x7ffeb3434900530d82ae980023aa457e0e3bdc61fc8000d4591af1f15c8859e7ffee8675705af7b21572,
  0x7fffdf84ecad852e26b5c7fffdabd2c567ecbf6e957fffbd9c7ee717213790a80001852d83c6a03ffa09,
  0x8000be12090110393c9357ffd8e76fcf77dd78f1a07ffedf2c26d4ad5368bdf7fffa9a0ef0b210539929,
  0x800058ea8a75f236446328002a922b3e738377d777800023125ef8f39bfc235800588f7ca7a471283415,
  0x8000a6ee60e86e7c96de17fffc7a6508ca877ab8c580023e57a35a849f131de7fe3e26aadc431b1026a5,
  0x8000ca4b7ef40e7c28ddb7fffedd30a7fbeb031f677fffe4ea7e5960f3f418e800014fe9aa8bd1cae2ff,
  0x80001cd4ff45e87127b067fffdcbece77c835dd26a80001dc75aca77460e3957fff23c336515fd9ee4ea,
  0x7ffff3f6fef1d964231357fffd71db572e8c1fc6328001c1599466a479c518a7fff8d84d1503d51b6cd2,
  0x7ffefff30e68b6d7d5f227fdcd78204ababe3322dd7ffed64dd2770a2fac90a800080595aba243176758,
  0x80000b0959358d2322ade7fff3742ae44bb5c42e8e7ffe8aa11c42d59198c4b7fff43e77352e7a7d3d1f,
  0x8000598d6493701d05a58800054a7f4c1105f67ce18000c6732440b2b2c14597fff833528839eac34093,
  0x7ffd28fd69c27f238855d7fff092d7484c51f5a34780005de453a94eeff49b780008d3e352e2eff2cfb8,
  0x7ffe84980f5f8aa0f239d7fff33c468520fc8e3ff57ffd07458c4c4c827a7e4800068a4c26d72c944c5d,
  0x8000876ddfea9f190f7e97ffcae572695d41404e8a7ffe161289121798880a88000a7fce3670567eb97f,
  0x80001815bb9c0ab16813a800013539396b76248a98800664dada85d74e809c88005580b592963ba8b6ff,
  0x7ffff00dceff94cc1f6b580001a2c488ae1b3bc41a80001fae4119fbf47dbe38000ae00d9e3fe0f76152,
  0x7fc8dbf21000251ff2db47ffe713dab7bf9dde172f800000c806c520422e9b07fffecc8a9b18b5338454,
  0x8001a0a7858fcc1cf66558000b4c881f5eefc36fd37ffe45d5d0485716de24e7ff46cdb034f9d14e2574,
  0x7ffffb5401ed99799ebec7fff084733f072814ea427ffd9f712be5b16311fff8002c3894613d7fbd0815,
  0x7ffff0a9602bb4852750a80008a1bcb95e3c9e2ab07fffca84ac5d41ebfc5ef7ffffa741a26a6c784a79,
  0x800004d80b54ad80097187fe44544340adddac901a800065cc4316adefba78b80002069f202e4206cde7,
  0x7ffd9f6f0434d657ffe9b7fff0f51603d50896cd4e7ff8513d6d8cc5edcecf37fff830ee48c93ca27e58,
  0x800002ef981f010a5e1538000036514666c72c685a7ffffa94ff11a63540fe87fff12c3e691cf0f7a051,
  0x7fff8aee8ea0d0e252ef38000520cf35fbf77d0acc7ffff92431cade3b417637ffd8a12e953efdc740b5,
  0x7ffe56957f5f33ea77b437ffe07465f988ade42e3f80017094835cbd988ebde7ffc534ebb26f17f48afc,
  0x7fffcf941ee17821044fb8000d11951c39936c86e780000d81c807c889881897fff15c53b27ed7520b17,
  0x8000026c179a33ca4ba1d800073e86f354b94ef96480000bf7f11b6aa8cb7527fffc1233d75eeb24d0fc,
  0x8002ad0cd977ead984b9780027e79f567e2745e6718010190496ed5a64630b680007ce4bdd87dabe564c,
  0x7fffe770c6337bc09a46d800000e0b5af91fc52e3b7ffffe42cfd598fefc2b680003d6932c3cabf12920,
  0x80000329317aaa2ceda0d7fffc53bb5155fa639efa7fffefe30a00e35e88d5d8000245545fd6242cba0b,
  0x8000931b34cbb69686ee88020b93971f60dab5827b801639c2de2dcfbe2e2557fff23fa7ec5ec6c77f23,
  0x80000c3410f0fde185e0480001f6c04fd92576801c8000160b83dfbb6d9f57880003c9a711f2d21a174d,
  0x7ff7623e892c4ea1519ed7ffff1b5802cd9e5880bb7fffefc5f647bb09ab928800013f3d18a8281d8f1e,
  0x8000086a5e56b530cba6d8000438504a5cf69b12f88000837a1b568c45d2a4e800c4c2af49429114c1b3,
  0x800004799a6e1f27a86d780002c4931e7d1740a4d4800001f99a7bebf762eb47fffe415b795e245c3076,
  0x7fffd03b535955a211f027ffb8b1bd0ebec9239c2f800d128e3ac7577fe740480001054fbceaa2e43ee5,
  0x7fffde7445dccf90312097ffe615bf2a9a4b7a68e97ffff80f65f3ca8d8a1557ffffeb10bc3c17f9643b,
  0x7ffe4849f44c5ee471d80800036b0bdf111340134780000c6140f626bfd85e0800340477b5b31e9b80a7,
  0x800013a0ff2d46bd2c20a7ffffd2ff4dd953387d4580001f6967870f82288fe7ffffbc919d64f18ce5f7,
  0x7fef7eb0f00c83ad406ed8000575a86af1d974a6ea7fffe717ef01abdbf0ebb7ffff805e2fd56ff4ee55,
  0x800038f60f060e93193cf80000a6dbb59e16c2f57180000078783d4b96a93ad8001739818c6bae538c0a,
  0x80001b88f46b37f1f4bde7ff09cae8ba0a612b802d7ffff3cf5aef2c1059ff8800019fb5c11c0f1e6c57,
  0x7fff78fcf0a2f79243a42800002dd1c41b8d022bca80001d083256d9fcf196d800027279eae6f91ec353,
  0x7fffa3b97a7fb84756d107ffe3e25aa015a98299d67fffe4794716004069bca7ffbf50246b6864fa47bc,
  0x8002ead18725c4bea120780000ef14405ce9dc5be07fc0e83411eaa2927fdec800001e4801efc58ba38b,
  0x7ffff160074f03cc50c9b80001eaee734a945ff8d87ff1e97f0e24ddd6767607fffdf05f7967c9868a15,
  0x7fed9a88c042a57d314367fffd705ffa67bce755507fdc7debb14a5b55b0bcf]

/-- Packed radix-`2^84` upper-triangle words (`+ 2^83`) for partial Gram slice `4`. -/
def gramSlice4Raw : List ℕ := [
  0x7fffe0a7590b3bfd15fe37fc521b044dda043754dc8001e31ed8b528ec76c7d7fc49b861827f740ed8e9,
  0x7fff597b834439a6d8cc2800048be2288d903895e7800065e8542220df8de677ffe5cd83f60d4b25b4c2,
  0x800002b1164b76e0094558001283de8e1d26203efa7ffeb16831ca211f240437ffddb6bfec02ca89161a,
  0x8001001b89dbc8b67cafb7fffa63ea7a58fd9e896d8000ce1a9c43e13164da1800060e43743d70638916,
  0x7fff6a9fda04df35da85780001e394a95729ec22fc8000643ef6198980a93be7fffe81ca944b42bb1fe9,
  0x7fffbac26d00f1bc2fe187fff40112f9e37ae259de7ffffebc486f2d3ec1f618000079a9bdb982b8e3ba,
  0x80000400ccad36ed2e454800024c38f162ff6b4e847ffff89fafb3c1cabc56a7fffc0266d6d58f158f63,
  0x800d2f531eb08c7a424ab7fff0b0abeacd6ba6f5c17fff465971ea359ee7f158000987fac51e52996340,
  0x8003070657ca142cf495a7fff6f63c7a5890ee9dc27ffeb06b1631d5379dd987ffeda1ec400f47040320,
  0x7ffc515b39eb0c603ac317ffeeb421252de689a8857fff095d369ebe0d09b9b80084a04c4210527224b5,
  0x7ffe49bf00bb3f42da478800092f1a0cca7adcfea68002165435a94840ca5328001ce2077e8436c0cf37,
  0x80011f2b72bec3343c49c7ffff32bf5acb5ffe4f3e80008bb349c5ae11e9cb87fffdc419020f60edd87a,
  0x80001189fbb9610df13ee80009c4e23804dd02da4a7ffdb0a7f6902f58ea08a7fff0cb11ee71688bc7de,
  0x8000185cecd86499fbb1080001b0a541c51bac3bbf8000517acf7abafe4597b7fffcbe2f3007581f451b,
  0x800209ef8f16359797d707f8c9b7cb7f4b0c50f14d80001855fe180c3a8e9cd80000900ff7cab6847959,
  0x7fff3f52403d1b46fd7a380007928947319043ec377fffa07ad05379478fe7b7fffc48a64673354dc7a7,
  0x7fffd8263fdca25cfaa917ffe71fda51b0b398606180016131980d1762689977fff628265181c1621e21,
  0x8000020f43fe138a0ca2f80005cb460a260f97fabf7fffdb84a31a7b08998dc8000028f1c7e0266e1d03,
  0x7fffeb578afc4299efa7280003a8b94b5b6bd5571480000459244ffe668e27180002478f1bcbfd80fe45,
  0x7fff4dcc36a843dae45487fffb26e4a2218c4e354d7ffff967d2fe12bed14a67ffff84d8bf220dbd8954,
  0x8000e9deef11e7ea4d9688000128777146066886967fffd22508b33b0216b5c80004c7153fc75d1c05e5,
  0x8000098ffe843174994258001df0d19b8b1eec216f7fffda264623c743540207fffdcd5d0525dc6a8d23,
  0x7fff806e299fdd29419a780001e74e61778eee399f80000584f5bfad93cc3bb7ffff180407bbe9621a3c,
  0x7ffedfbed1f15fee75b6d7fff8e6a05f68ac7046478000ffcefbe77273cd5f17fff0ade337d9ffa391fb,
  0x7fffef8b7b7dcb560b45a7fff5781948df318c28008002511653ca6c277a38b80022163bcd575d66a605,
  0x8000110372f1953c19e0d800022a92f5dfb09291128000354a7afcc353492277fffe3a4e31fca2a802d1,
  0x7ffff7d559fec711dcb2a7fffde13ee6a6a66fb32680000db06e78f806af184800023b1dabd87a65ef67,
  0x80017721d4fc4d66c71117ffe76b14e0f1482f5b027ffefb959f6fcdfc9072880008e881e25ef5c4729f,
  0x7fc55370a64fd38e00dc780012f1fe47d4b08a1e2b7ffe40306711927f917978000d3bc77cb8b11fb66b,
  0x800055dd6f5f6b735337f7fffcade0c90bda7f08a17ffebf54bd3603c5fe9d67ffedeac69109033c3b65,
  0x8000ecf6d097ca9e097f87ffea53d42d415c2e4a617ffe271d49cf9d060ef9c7ffe9e15b448ddb308bbc,
  0x7fff93358b5158801ebe78000d2426084eb605dca97ffee6b99bb98a825a0bf8000bc18e8a006ef60212,
  0x7fff83924ddabaf5f43bc80003e5bf4ffa04c649017fff85d2825bf5dcf04887ffe0d7539646847c21de,
  0x80003b1eab8063119df108000405d6469f3300c2e880001ac550d48ea8c2794800062baaa23df023075f,
  0x8000144a7366a9381bba47ffff7d4eddfdd0f1aa9d7fffdb1aac2e8bc559e177fffb78048834d288f23d,
  0x7fffac5c47173e8f5264b7ffdb3626ec2a2ad37ddd80008b033d93e8e851b437ffff4d381563cd6b61ec,
  0x7fffcac213be2cc3519ae80034e7ff03fc55bddb627fff1e1c12c260dc58bc0800cec049d82b5f71ae2d,
  0x800025132b01b2aee92437fff38186fe01f7219a4a80073f2ce56354f0b990d8002ed0f3ebbf5f4acb7d,
  0x8000cc62aea007ef7ca888001f429249a571d8ac408001e277c970ac55983ed7ffc9f38819fd621f180a,
  0x80004150ee8185c858b497fffc0ca685642bbc29237fff67aff5842a885b4717fffa329c5afb747f8065,
  0x800086b7157ffe6b4672280009bc3c62d5f06910f57fff0d6583cda8417cdb0800122ad5edb3a8a1374c,
  0x800021190540e7408eb687fffa9822e5185bdd712080001a3ef898da6d85c5b8000267c41bd3dbd793af,
  0x7fb8d79ee9751dcd3736b80000f6e69b628341932280000a8ca0fd4eed1277e80001a6cafd81c6fce6db,
  0x800004e3f58cd99de60157fff8e848b382b383b73c7fffa9dbb2aa41d5e46c88005ba970a05c7a9ae425,
  0x8001b3fde1117c92ea0c88001653a006a39efbb5687ffdb675b29e11ed8f8cc800112c691ad6ac6ca2e8,
  0x7ffee7fa9b6e66da4e34e800018a59fae5577d42d28000a090dc0dacc4ae57f80031fcc6a42c7bf3c868,
  0x7fff4064b04fbc1022c7a7fff3d0efc71e0a0959c87fff673497dba395e25c47fffdf96b7efe43bac0e2,
  0x80007fbf4a50023128e5a7ffff55c6da0788e5e0f680003db6a075463ba1ffc7ff8985d3a6c1680e1ecf,
  0x800022c6e05979c4742ef80005484b507582e44e0180000c728879e753c86637fff6bf7e65f4a74f5d5b,
  0x800028008bf2ecac3c751800d3aaffebc49648ad3b7fff4fd9baf4bd87462ed8000f0af7c9b1b191175a,
  0x7ffd84793bc5c7799764a7ffa996f7acd315977aa97fffe65e0877afa00f7ac800021b677c15956c8dec,
  0x80023edb9f0728c2a1c897ffeddc03bc356ed7e3f48000f7d28daf34457df137ffefce24515d1abd54c0,
  0x800062e38a878ef931a0280009b1cef0352453ddd07fff8c6891f9750a24766800063c8c04d42f77ba0a,
  0x7fffc11cf7d776da49474800012c4302a1319909248000678defce6977652048000a3429b25dcb32f6ca,
  0x80003c02f8e66959a576a7ffae3a824e9e2c760bc07fff996fa54e2cb0c5588800072d4461dbce990f25,
  0x80004322dd223dfa435127ffff7740e42326ad2eed8000346b12ff78b999e0e80002bdcf5cfcfce26d54,
  0x8005df70c315f86d82ae97fd9a0745ff3e100f97c07fffbd27d4282637ff55c800050d1c4f21ca23b88c,
  0x7ffdf5f86efaab49019fc8002c878589aaa700b00780027b0c07dc6f38d57727fffc9ce33d4818872324,
  0x7ffed9548ff3a31f75b397fff802d25e37db36cfbc7fffe0e3c8dd17be33db17ffe8e07a7ec002a805f0,
  0x8000df0944b6ddfe631a8800000eeeb536be7521e28000c4174a07c15ea88c380002dc41d6936d14b571,
  0x8000279a64ef7edea7d5c7ffe9ed294e3d25069c6b8000cb007e10aa624cd28800071406db5502fda6e0,
  0x80007dbf6e6a2f43da0377fffa39ceddbc2dc31a5b80007b7f142d4abe4f57a800063eaaaf1f46e73486,
  0x8000a2e7e94a314b7596d800014248f890a8eb074280003f1acd98408f49cf8800050bc977b89b5bae0e,
  0x80001371c5b3d86d5c92880000f30a8a5c07b0f32f7ffbb160fc4c4583861bd7fff439c61f2f09fa848b,
  0x7ffc069fdf5f2ca65c49c7ffcf7e64d5797edc51c18006a9b557c6ca6c68e6580027c780e559f959fbba,
  0x7ffdb9540c01179d00c3f7ffeb87978a4c93e5b6b480036a7c1cb6d29f66c1f7ffaae4d3c06f82fdf3cb,
  0x7ffff3dc142f2bff730a480000a31bf6707a529f5f80001415a78af55154d437fffd1bebfe357f3c77ff,
  0x7ffff2b2d51aa1fd5478580002e21b37850ad5370a7fffffe77e62746c54fc480000e892ba5b398b03bc,
  0x7ffff062d005d013d5b4a80001f3894ee1c7ac9b9180002d649829ba8e4d5237ffff153bdd16c0ec29e9,
  0x800018902c83b2375938f7fffc43e6eed2e5e876ca7fffcb2179e8c7edb91db800003d3e19a90b70f14c,
  0x800162ff34f26c7eca6bc7ffeee8e3c4d4b12c412a7fff4005c32cc576fb6657ff80ff04419a68003c08,
  0x8000d73e61c29bbda15b07ffec67f766c701b3fd6f8000896fd8cf50ae2a4197fff2fc69b27309f8ac60,
  0x7fffb8e1e155827f9f1c57fffe7feec443c2b660377fffc3d235b684f9ca76c7fff22b609299f867c541,
  0x800020751950a055a4ea57fffb1aa3a803cbae7ae0800024e65023c3886168d7fffcdb5751f56ff69010,
  0x7fffecb52802ee348a6977fffd824c25cddeb5eff27fffabdfb964feb96a0c28000236728d6805942c55,
  0x80002bdc82eb2bdab565a7fffc5a7789ede37833db7ffffe7a86b8124cf4cac80002e988a8c37026cc3c,
  0x800029f307ea735116fac8000ff9d2cc7fdcbf9bf17fffb0439128dff603daa7fe723a29e987bf6c77aa,
  0x7fffc18425ff7263246c27ffe152baf86372385d0c7fff70b3d754994ad6aca80003ea6aaa2bae5afd9c,
  0x7ffd7dad2e31396f1d21b8002ab69bcc8cb3a71eb37fffdbbe71426e9895ae47ffff4abe7513224e966d,
  0x80001f3f8a471d5ad21d980000e5e3eccf5eca4bd07ffffd59897e68675573d8002ed43422d11bb8b55c,
  0x7fff828936ed1e8fdfd7280003b6bda10b4f33f0968000160a73da01da558e17fffe11c43d839e18df76,
  0x7fff846ef5d82e8b07c517fffdfaee18456493d5267fff836f6b265cdffd0567fffed818db78c3242c4f,
  0x7fffed2507a38525d3e897ffff2f2a203bf5e3cdef7fffc3d05aa1be48afbbc80004e055a9aae7a6b714,
  0x8001565caebe762084d0e7fffc3e0d1a5b8bc3dc697f9eaedfd3ce4519bb14b800008cf2cd400771a23e,
  0x7fffdb73b0df16cd8e3de7ffcf6d6ea461c8d44db17fff40287d88c1ec895c67ffff8166155f607154fd,
  0x7fff3fd33cb930106956180007777de5775c2664b1800016b204e1cb7626ec880002f0a4a99c0e1abfe1,
  0x7fffcd2aabe5c109dfaa180005550d3a26a4ea228f80004276a0a745a452ace800055f1229f90ae73b10,
  0x80007bbab285ba52d24ed7fffaba0a5f3ba063ec4b8000199ea3eb6f7fa70dc7ff7d85e003dbf1c9b355,
  0x8000ed87f14a45741029f8000ba7fe2d2a674e597c800011325ffe8391f66fc7fffe3ea7defb430f5b49,
  0x7fff6f861132fa73e12677ffd297e25ea222ccf55f800016dcf270d378a0bac8000be713b9ab7b025822,
  0x7ffd8305f0e2b55b00615800074fa988a89135cf987ffd565ef0a702b18e2208000f605184fe4e769d01,
  0x7fff63fb463a2f53a6631800492de43181338a83ee8003a4eb9ed1000ce2bc27ffe82c15a9106752b06c,
  0x7fffd7769c2e85b56389e7fffe3de893cf0a009bd38000f5b729d2dbee8bcae8003de115af0609c65507,
  0x800031d657ef24542325480001170a2a054ea11fbe7ffff899a21367b1feab68001e691c830a5267da6d,
  0x7fffdb49dc8605771fbfc7ff62fdaac2118a07acc6800080e8753230ae0db98800018113836e906d96dd,
  0x800099de87b42baa4e0788000a40521f21ff9bd9d8800068e6f8feb57e340b47fffe9f09c0b9db000c94,
  0x800228194908ed666aad48000c0052bfa7fca7d2137fb2961b96328febf33dd7fff06a943462858c69ca,
  0x7ffbe3b27d2de960dc1b1800076f0363b919e595d77fff8c619f1ced30f97da7fff9e427e28cb309dad1,
  0x7fffb8c6312f0b342ed6a800009041905402a3b5c58000047f32b7959178eca80000d698c786cf17af0f,
  0x7fffafb5289b1b974687a7fff8207c7b5d605070ab800018ca56af16d47623b80003e2d441f47c20ce0f,
  0x7ffff2d1e45140deb1fd18000b0ba54a54f794df25800d84510ec900419a679800088441e27aa6012838,
  0x7ffde5596b71ef16fe4d97fff007a77bef201ddd027ffae72229b6d8b66136d80007bb07ef43853b9e95,
  0x7fffd9d27b7d4701e65d6800062c0b7e6f7ab8b7347ffd248a76fa5a1bd5aa87ffead260ac5a38f1aeeb,
  0x8001497e64605dda940707ffccedbcfbee0545903980005a799bdd4e5203add80031ed438f4651033b39,
  0x7fff77de3431534af43f680005e53781ece63ff4248005d05229a7d49801fb98000e95eaee621ffcf930,
  0x80001933d0ec5ea720a4c7fffe291e5b89a5b95e5980006f46965d912ce6d7c7fffb096dc8e0b4aea348,
  0x7fffcb5cd79519a5f2b2d80020114d027097e2363e7ffe2b2856296f348d4ef7fffe2d9b70cc85016e12,
  0x80004de6e142efc88e1fa7fff9b267535f71b7d7dd800000df9b52b8e5fbf8a7fffe2b2d00459157a334,
  0x7ff09de6fe7ce1123c0138000472efdca9df6824358000018e7de10d2028db27fff1dc209e4760febfbb,
  0x800019a3733c8f8dbf9537ff69929ea0dd4d7510f57fff309e3e9ad578f18257fc1d252963a4dae2751f,
  0x7fffe66e6ab995265ddaa80007fb903bcd7bac84de7fff5e629fc3c7199533d7fffa03149abf670f9c2b,
  0x7fff11a98b701f410a0ae7ffff43108c41f2e1ed86800061040009de4d3262280003175c55775998ce9b,
  0x7fff202860baf83b66b647ff1b2a3d3cced840589e7fff87f7d1a179b216e917ffe5a90f8cc4e1a81370,
  0x80007cbd8fe00527060397fff880ddb832895b47167ff098bed5eee6006be457fffe6fa25c0ca6c7ac35,
  0x7ffd990f49c5dcd44f8218001197178d36fc3eba5f8002569b836eaaf7960f27fffefb40cd3881fe970b,
  0x8001842516d23758cbd7f7fffbb62823aad40e13fe7fff6f63784c46861159f8001845b287401762e6e3,
  0x7ffc7982f1278d7879aba7ffbf84150aead7b0e0827ffcf16f2245aceae37027ffae3af68414db4a1897,
  0x8001161f457cf9d77ce9b80005fa6f0672b30ce1997ffcc65057a663f78234e7fff41254876620a26c12,
  0x80001d65f8a909ce3928e800007a6b8653c574d981800046797dcd772e41dc6800365e1576386023fd5c,
  0x7fffe3fae907651241f458000be5fd4bbb401cf97680002d4d8f655dc3fcf897fffaa53507526b3ca4e4,
  0x7ffff60b840dba2d17a2e800dc51f35d04cc9bdcd17fffda3fdc2b4e21bbfc080004bf5d166765cfb55b,
  0x80002a68f292a0eb235117fcc088eeda2a470353d07fffa2c75cf78482e0527800bd3be1c0870fb34892,
  0x7fffeb5a69a81e25bdff17fff5a183e5a5e301293580011b86dbf6f13bca7bc80001f7799a1d27a84c8f,
  0x80002193bd4fea7af0516800004e24c41d8377bbff7ffffcc41a6dce0abb19b7fffe3fc0e2d49114c30d,
  0x8000202c093b7d9a6e8f27fffc2743d81a3af535ea80001194f8d97eba5f7a9800020b334a9f24ab3a5f,
  0x8000ecc9946a7dde50a247fffb75c59822d60d161d800377640d7438af243ac8000e1e81ec4d51f357c6,
  0x7ffe16b4e916bd9757e517ffcb9b5e3d592b4b3a5c8001037c4711504e5b2438000a41edae2d825d227a,
  0x7ffeac5aaaa23095f09038000075ee9fffbbc28ab980002068d0a5f87500f6c7ffed4bcad5bcbb769c9b,
  0x7ff24166f582d6d51a30380038ce1c1edaa9a6733a7ffd1caf1d6b4ed4a0706800151f1d93d85d131ca8,
  0x7fffdce52e7689a45430680004895cd59fbd2c1c2680081dedf1267ec729d787ffd7b9333b3a8e06aafe,
  0x8000030681fca73534d9b7fffdf38ca286bb62855b800008f2b41bf3d212a528000319f27207cf197cdc,
  0x7ffff711108bafcac0db4800046ef0d4efe7092d3a7fffcb53c0df86729310080001e68df1e810eedcc4,
  0x80002b79348fdf3ab345a7fffbf1de8ec7e52d1ee17fffad6949cd46cd201a77fffeaf35ef5211a5de79,
  0x7fede7069e2fc82ad72e17fff98c061caf5888fd8c8000c8ebed3677f7c5c557ff96945d8ea60ddd37c1,
  0x80009ed0e5274239463717ffedee92e370c0d0d96e7ffefd6159a2de4822f0c7fff38c33f0ec90ec02c1,
  0x80003f73f98e181f177d07ffec09c419ecb2f0b8da80000f121ed3139d203b180003b13844ecbc05cefe,
  0x8000286615e579bf2e7857fffff28fa1948a5186757ffec67643c4a05e6752780002483e3e955fd17abd,
  0x80000f01ecba9e4713f437fff100e405db13b3e0a6800020e3df052f197741a800040a64db613d2eda41,
  0x80008bb593fc2549f4aa180026a05ca22a552fbe397ffff898963a0fd1a365c8000185aff6941c6e8fe6,
  0x8000a819e2ba5f50763247ffe24d72335662022ebf80023f055fc0074a628177fffe9b5f67a979df8ace,
  0x8001c682c032938323d368000448cf76b86ea1e3fc7fffaee19358a99e98239800070f17ed53f96c22b3,
  0x800071d28f685d60e1f758000df28c8c0581b5f3a8800056b17f60f0bc2e2448001b2f339170118a8934,
  0x800013fb6180d3f5554f080002f1c1df6aab1c81df80038451dfa326e74b4488004cdc6718a26e825d24,
  0x7fffb0d8caaab2ddc094f8000c4a08f2130a78f77b7ffe9f8231e5fa7dec3d7800034bc5407d26ff94e4,
  0x7ffc67a3265f04d2fa8c17fffc335dcb417c4f9d277ffffe15025dbdcae06007ffff721a36a89eda26e6,
  0x7fc9426dbbae277368b9180000206bee883a05fbaf80000ce0da9d8e9b57cf97ffff639008ecbb9b9aae,
  0x7fffca14ee5abbd4d3c7a7fffc9e75114a086efe817ffe94f547e1e06a5d14f7fff881ff0fa0dd08ac72,
  0x80006bae657669732404780011e557096d18b8c3248000e87861f09b43174077ffd73e8560139daa9df1,
  0x7ffff8698f06c2dd4cf25800015346a0ab2a3fee6f7ff8054af38aa48378f83800021668c7d1145b2823,
  0x80000f247b26591f1c75e7ffd6b2723e54af5ce1fd7fffff97bee6b4b615e4e7fffe926c0d888e1e5cf4,
  0x7fff335c9997d4942a6fb8000ecd94e272cb397bab7ffd9336b0c81126ee3d17fffeba39aa43a087329b,
  0x7fff7b1c076417c2e1c108001063ed31321f01719280055ad48f9c12d9d53717ff848d5d527ad49a22d5,
  0x800016dab1cd6e35c3a5b80016752dd7dce3f6c2007fff57358d64f460ff653800068edc047f6137cbe9,
  0x800058aee454a87af107a80115f0cdf04da41d7f5a8000905d2f9eef2cb07227fff9cd526c2e53a0ba6d,
  0x8002ac48a72a3546239f37ffea17a0ef45a49c5cf6800ea59d20f3965355c098000d2987655f199ee633,
  0x8001d135cc7d522cba5e17ffff5928849aa6f5cdad80007bd7e9b8a8d51772e7ffeb73ada9126782e288,
  0x7fffff307d58d9ca08729800022c13893612d3659e800015285d02e33837afa8003d3c77d5884e20c172,
  0x7fff90ff0092ebb7f82ba7ff075a7798e2ba51dd9e800015eefe306f7e236a98000143a1ad61d5f8a28f,
  0x8000487a4ada36a8e87da7fffb3ff3cfc7276518307ffcfe90fdb50ba72fe3f7fffd1c01330f9bcf7ba8,
  0x800029cc1270ccc6398047fffec91f1e54a7c3f8638001601c83e1243cd869d7fffcf5708fdbe08f5f78,
  0x7fffc6b6af41f8b4e185180005e0104d4870cd6e1680005882e27ce5761d98a800106b43a96913f064de,
  0x80032d2cefe28ad3aeb788002aa3b839c40138fe80800020935d77a05e12ee67ffff69e8a45dc01f7976,
  0x8004322835a6e1fa731a4800029ff8127a43c82e2d80005b84dcb8f1cd4e2fa7fffd00ae4bc456139afe,
  0x7fffd98d1f47e398c84138002aca48e20a759fd3c27fffeecfce5754eb799cb7fff252b02038e9efc71c,
  0x800096b38fcec96e63ad87fffc2bda2079eab56b337fff28ebe2b2c440aaacb7ffdc2a1cd738acc2e108,
  0x7ffeebcab9f78281e75a77ffff24b632a9ecf7b12e80009686e5e1b9d1fc9938000b84d6087414858381,
  0x7ffc15716e6dfe64070627fffea061887a83dcf0b180001cc5c8f3e9fe7976d80007aa09590f82b4e1de,
  0x7fffb742ae157abdf393280003baa581bbab997cca80001593fd78bce4b847a800003845b2759dec688c,
  0x7ffff8368970778e37ec5800016fe1c19bc8fffbfc7ffed61971be1c4974f0e80001bfaba5b9f4e48ca5,
  0x800003b44056adf25d12480008c49dfacdab9d41117fff9674cc6e6823f9b5b7feb482d13efa7400521b,
  0x7fff46e8acbbed84dce63800099a089bf155fa10527fff2621d9fed6c3646ac8002fcf96ba09ff5dbb95,
  0x7fffe1899098c3856483d800b32bdaa4b1d95d51547fff8da4b257f136af1677fff9cbc39623aa1a4ccc,
  0x80001984ad528f10b901f8007c12c273a172e971828000016b8adf1913929bc80002c9ece484b3ef4407,
  0x7ffcd599124a37fe0b694800044118f831dafe6d2e8000002da628b69baf5fc7ffd45eb623fb2382a8bb,
  0x7fff754adbfb7f284151d7fffdddf529b76836ba5f8000ad3b43f6ac25a41197fffc0485c475b48a0a17,
  0x80015614e0aca63ea21747ffe19052f8b5620aecbd7fffa1400d4e2c3ab6f677fffdeefda445f712f715,
  0x800031a6806d65933590780007590202065c05ff057fff0a76e448a414e399380010b0d5a2659cc29fe0,
  0x800c648750e7be966d8697ff8f6d0e6ec442ad00c37fff69fa36c30b51edf9f8000b7a6ad45da6d4ccb0,
  0x80001b2462c1392345ec87ffffc6005ded44f38b2e7fff9ff2d9c1b737a56d28000021037dd75422974b,
  0x8000159d2b806ac8771897fffcc627901623660558800027342892ea03e64f97fffe25aa4c5e60efa9a7,
  0x7ffff950898402dd097b37fffec311817b90f861227fffaaebde380ff589e698005b4935a0eba0f5c00c,
  0x80002b5cd4a67554d91c17fffd31b8f655a294d7ac7ffff58a793d7fe30eeca7fff5378c7fade865120d,
  0x80000339a574b8cfeab0f80003feeadc5e61673ec07ffd9694783868f850eee7ffff77e44ff660f22aca,
  0x8000044a8fbb24941db258000065cd80c8a390c4517ffff8c226a0e4bc6af177fffd7a1c18d3942376a9,
  0x7fffd996a8cf7bbb21c4780001f3507215ed94350b7fffe816a0ea87bff8cf67fff436a13e9abd080029,
  0x80006b27d352a4bea61427fffb60e30d89eb6da1cf7fffd053d555e96fca7b1800074e17fac104f7ae06,
  0x7ffffa530661f73015eea7fffa5d0802883a00e0517fff9f72127c0ba00175680002b1b50fa2ad18457a,
  0x7ffeaa87d86586e9114887fff1e4010f840000761680001d49e29c2ab439ef37fffabf726cf6c995cbca,
  0x7fffb6ec2bed9598882107ffff89f60503028d149180000a72c88a108f867ae7ffff367043a9767039f3,
  0x800011bff94f5be51329b8000031d09efaac848fd2800039411fd2e876a8db17fffe3ecb7f2bcf1e08a0,
  0x7fff946382a6070929cfa800007168d2c70eb725f37fffef6a1cdaf02ed7ba27ffffce0b008b45a3b246,
  0x7fffe826b59a4e3df03f07fff0f614819e1cb6f03a7ff267c6d3bc9ebaeff4a80000ab868a535ad34537,
  0x7ffe437223aa6e412563080001760c670e89b9528e80008c4bd81bc71540a597fff6c44f675a3c0ad425,
  0x800004589478860592aa4800081636571bfb033ff77ffff28f444d878fb46c47fff6849e72c373473e00,
  0x80000bbbd373e787f681a7fffdb1974d1a7cf58f607fffe18b3a072627821f680004da7fa02270e12407,
  0x8002d411553edf119e117800141b4e1e6a24c3384e80001ec2633a878fe8e5280000350757e04ba85bbd,
  0x7fffb7174aec42241e4de8000a1300f259acbb1cef7fffede427b35290caa557fff81e698fbfbfc60f62,
  0x7ffff480fcf436c0d8fc67ffff6ead53b99c8176917fff93e4e095a11bf9c0c80003304b66efe045abe6,
  0x8004a05441dd964ebbdc37fff9c51de923c37dd50a8000710b1a67e4048ee5f7fff9d796eb339d8035d5,
  0x8000a82929b3582ee87b1800010d460f51ff844c177fffe3ec02b386e836c587fff7f76c48a470f13235,
  0x7fff9e5124057253b748a7ffe70e1f6bcdc1c16aa67fffaf99add722b1ed42080000c403204552efbbe6,
  0x7ffff01b2f76322f067427ffff4d3eead4dac8a92a8000266efe5bbe8f1fee57fffff540591692f9d1d4,
  0x80001539c1fb9a62e5acb8000194aab911048c70f77fffe8cacf87942625a067ff99bbf2cf2045fc620c,
  0x800000f79cc0e838e2a537fffea10777ea35baeedd800007507db7886506ae27ffff5e0c4a75785dc81d,
  0x7fffe02e086507b800c5f7fffab2ea50c6aace3f3e7fffffef19e9f4baebc7e80000d6ab9a0ac49b9e36,
  0x8000024388955c0edc524800008585c7b8eb8703cc7fff353215e05e5198a2b7ffff2f3a858944331cfb,
  0x80000b99b96ab637785f87fffeaf150f3f2d7508ae80008c24e432f301c1db2800044438248c191af9d8,
  0x80009bd797ff75775c7c480004a29e7f9653acb0058000206578569a15650c2800054dfb487104a38ce0,
  0x8000090a823bbd76723167fffec3271664e41fe75080001191df66bd50cffdb80001ea3289fb2a2f8fe9,
  0x80000676862a5b13b7a777fff2037f2b5e522a946080002fff3d53fbbcfba0e7fffdeb0c2b2aee813f20,
  0x80003b4ba4d1977d2510b7ffffac9a164b035c8b9780001a9679a63d697adb87fffd9507e38f1ccdd5ed,
  0x800005c50e4cf5882ec177ffffe9c9bd76dd1229af7ffff4f9b0eeee683c56380011563b9c72a4a7dc63,
  0x7fff687c350e2c3d6d6a18000c50d8d3647d55da9f7ffff256d58077eede4d27ffff77e974c96f87e912,
  0x80017328b8e92f9c68c2c8000189fadf6eb4a2d0cf80001b7dbd54f1cb77faa8000b8f4b935866c56e9e,
  0x7ffffe2e632a3b13748a37fff2e0f745e238101a4c80000a728ae5483be57127ffed2bc3ecf4f03b2d4f,
  0x8000524e98370edd5cea27fffde868b05831261faf7ffff7fd76d12e47c1ad180003ee2c03c9c2116eb9,
  0x80000e011f83bdcfcd7f77fff1d707ad1aac8f5dc37ffcb83a27f61873f08707ffff283ba3ed9a9e9f58,
  0x80008d9b6944bdd7e6a047fffc34a9d951617fd41d7fffaff905f0eb81fe76d7fffe456abbbea05b27e5,
  0x7fff2baa14805993b84e3800018e4fae46901aa95c800010a552c0a3b69b3107fff3f8ab68b6a2d71bd0,
  0x7fff9b56216883910684180002b363e0857ab20f7b7ffdf2983f6d354c17fff80003534648465c04421a,
  0x800005e326565bd62913780000a88db60424f8fe6c800438dcc88960a0c61df7fff9ad5aef0037098a30,
  0x800032f3082e392d3572380000079e42e1ef698c797ffffad70a73ef12b930e7ffff7fbbdb825bc8dc17,
  0x8000f565d1b66509a81d47ffffb6db0a192ce7cbd87fff9728be4af5e73253880000615a201e4db9105b,
  0x8000086a781c7c45e81388000abdddae0863ca65ae8000186e250d51107b2f780001767b2942c14b50af,
  0x7ffff11d2e9d4cea3ca267fffecab9236e0814058780001067a6d44113d43048000ed347d2dabc0874d5,
  0x8000399109019467f4fbe8000e6860e6796f03494d7fffef1ffcb16a6718c657fffa92328edd40fc17c0,
  0x8000105f2fe7fef0494548000f012111bad1cd7bff800087263a7aa9c49dcd27ffffd5062a46012a65d1,
  0x80008ccc12b3a07b1d8c280006ee9ca6d62f6ddb487fffa77286f93110d991c80002b0de6af62898c3d7,
  0x7ffde5f655d9f390c33017fffe5104272f11f34be27ffff6ff705760c1b49427fff5b7376c8ebef66536,
  0x7ffef9d823dacce7a7b718000366db98fc161bdfd17fff7de7942a3c37b7abc800019b3ce480f0a3ff53,
  0x80002a803890e0027f0f6800044203fbdb90807db47fff6fb67349a14c312fe80004e4fc23f727dfeb8b,
  0x7ffff72c20c98a534d5127ffffb29f5a6c83243c3c800038880127d680f0a11800026bf4abf2a3585252,
  0x7ffedefbc000c96b5733a7fffcd173b45085d7fb7c7fffe7138231734da977a800003a759d0234bdd18a,
  0x7fffb6241c55f7f541deb7ff9fbabc7bfb676cb4287ffff0918fdf4ce1a755680003914bde994471727d,
  0x7fffd4d7b14872a0b17e68000017b0f24c1192a3a58000272c6802e6aadd8307fffef72f62e511ce8ced,
  0x7fffebdd33984c0988bdb800004d5a0de752ca95fb7fff06d940625f9d9b30d80002079ec60178064814,
  0x800023b9440cf6efda8a87fffd55d73fcbbbc439e07fff35fab60edf1fc56f97fffffd5de6e29ec1522d,
  0x7fffecc9ae5d9e83da35080008256dd7e6b7bf79a28000391730d2eb525520580000536cfee00e0dbdc0,
  0x7ffe39d71bc863f6fc21b7fffb658175b77b20b9b77fff3cbcde2430e6e0df37fffb96ecaf2178a7754d,
  0x800012bd94d3a3d96e1117ffff81139bf0619f18df80001888db661d36134da8000aa841009e836225fa,
  0x800004a7f1be3df03e872800031b1b73cae6c1b78a7fffd645a3cc5627e83a480004f377e3c003e823ff,
  0x7fffe11e010103ec100b77fff6755e4688ee3ba7c780002eb7a5fc7d12cd0f67fffcc2b988e465c13394,
  0x80001edcfe5df57e35ffa7ff021f077dca004729a07fffe15a753daa52d4a0e7ffff7701b4f06d097e4e,
  0x7fffb7e371bd9f33f7d5a7ffff931db57941559df17ffff6ea93fc46b781eef7fffde9a4ae439a3aa55e,
  0x8000e1206e81671db49b2800007e911c3acda9e0f680000a32ef15087c751d0800026c57ad607822757d,
  0x7fffdc47dfd9bd644f9d280003e422f7ac293f0d17800014199c8e3926826ff8002e53367b6ded8914d1,
  0x7fff627932097034463967ffdb5bf672fbcf7186c48000901a67b86c614d8f58001a3f8229b2f07a8f4a,
  0x8001fd7c7e8d0e4067eb48000c68008f68896c68bb7ffeff0008a14d2426ddc8000d67344ffb747f5933,
  0x80000e1d9e2e53721de7580005dfc9441bcb6e893580005374bdc4dacad40cc8000102acd8a8941b6b2d,
  0x7fffb44c6f8a96a2c8ac38000283b12711f3e54c287fffd6e55918f3665f142800006e509028b04a54eb,
  0x80003730a2a81d39158dd7ffff224e5fe324d632957ffff3531e318d1e07605800157d11aa586b3a876b,
  0x7fffdad3ae285f34e9f17800081ad64282a7be1cb57ffff88c45eea231b2688800079b03147ff61ec393,
  0x80003eccd6eb14a1e88ce80004d595719694bb16127ffff382bc6a820799bda7fb9c7586d5b8bc6842d6,
  0x8000262ae0bf2fffb7eca7fffd63eb27df703ec9697fff643837cfa1fd7c0b67fffe52ea26603c2da27f,
  0x7ffe826e54e024ff073f07fff705eaf5a626cf99b58000039ca094320c3307b7fff6d2f9ca21557d5dcf,
  0x7fffe53c18b4bd04e608e7ffffa5e98f8e69b53ae68000a04076c59990b6df17ffff390151f12af0da40,
  0x7ffee5facbf45ed588b7c7ffba7b4a42e32a882d937fffa73280aeaafa308647fffcf02f675cdff5061e,
  0x80002ddc14643f1c4eef57ffffae5aef1df59150fb800306da9f70ee09727997ffe49334c985b6c3777a,
  0x7fffaf06d89a74364e36680007677a18dab7ba28917fff659fe4bd2d563777e7fffb19e15a81d5d97427,
  0x801babe9c8762a6f229737ffa5b6b6b5bdf76961438000143e59d5f43006a037ffff8eb3a12a45899bde,
  0x80001993e2dd251df76648000177b0604acece71407ffffa068ec54b7c535777ffff9f904228bbc4fa15,
  0x7fffd19be9e6b78bd00bc7fffc5cd5b3ccb47910557fb12663ebe7bcc9bf9e77ffff3484753abe6124c5,
  0x7fffc8f620ad8600beed7800021024cda5d68800d27fffe8e1cd2aa7ff444a47ffe118ba261fe8d56014,
  0x8000aac6fb6a4dc5ec5987ffeb5098e1b26e2a310f7fffe82a41586b794f6c37fffaf64c58e158f7ce48,
  0x7ffeed524bf64c49c97e48000eb2492862dd3298147fff532b450c3ccd3aa8f800463d7123a3e7050e18,
  0x7ffe395ff29308378536a8003ee193f2195472bdf87fffaaace459122d9ab0880005e3abb29925af6aa5,
  0x7ffeb087d4a6f009e96ce7ff2fb5a284f8ce4e6ef880003d12400e01fbef2c17ffa92f2af258cfdaddf4,
  0x8000441b93d317864319a7fffe2c9f133f83dc7f9180003bd4fe561079364f87fffa648d1b924c2b6f8c,
  0x800020800f90c3c33d17b80002794fc3f98ff1b14a80005f1452fb4be38bb337fff054a44bcf6b4e5912,
  0x7ffd5a44ec0de38d21cde800007d86332b4cfd4023801518d442b43c94128e77fffde8178600da9712d6,
  0x800027a0096280a65577880000407d88b209e4da117fe7f97a5abfce0aa4bc47fffbf4b36eac4bc95dc6,
  0x7ffe3de20897a4f81cca77fffe308726898a5198478005128ccfe9ea91ee8d07fffbe9284ca6568cecc1,
  0x8000229f458dcb46c941f8001f54201c60f1e7ba2280003d93abd8ea566627880009ded32526601a5f4f,
  0x8000797bae17cf9ea4b477ffe3bb1c1ab690b33b468000534aaee7d4c54610880005f33992dc8755642b,
  0x7fffba6413853026cbd7a80031b1403969566a81958000854b742c2fcf990c280063535da1ef1c9d5d70,
  0x7fffa9d5af67e357482cc80004270b56182477e4607fffd6b1245cdd1ecb7da80010db7cb25e9dd8f3c0,
  0x7ffff459521e6a0f7f6037ffb1d844f5a4e75e817b800236c8476ef1fc418b280007a8a0348217d54f13,
  0x7ffffd134c9bb8f8a1e4780003d2e29e3ca6fc5d157ffff4386eff1d5ef0e7c7fffc5befeb761de9c175,
  0x800ab4c0e54973c16cf8980000b7905e2718e2eea7800004ae2ec29d3602ef780006a09c9b2f5dc06806,
  0x80001c74d60d378ac59647fffc30de85b6c3d9459c80001ce7d1801720bf05c7fd9a7865b8d85c745bea,
  0x800032ff9757e9e1b4a3f80000a4a71dba9e6e03577fff2beb6ecf7a61864337ffb1cb15f7faf828aeb3,
  0x7fffc32d8686a83c956228000376faa0b3abf244f57fff8ef5b0a610b0f0c087ffffa19b6ab96f5ba3a0,
  0x7fff970a6e56c6cd2b32e7ffd211f2d36fc52e0afa80000b864c136ba9afda78000083b3d7c019b365c4,
  0x800002c5e91efe181ba1d800003d579c77addca9347fff87041fad713ea39848002601c1f2eeaff29061,
  0x800004be13700200342847ffffb02497a7ad453947800018a0f35fa647d1eee8000072c850f4e2d70cad,
  0x80001c8606c5be62370b2800000e0faa44ecd679397fffee3728fd69b36dead7ffffecebba212e89e9a0,
  0x8005f9238e71df8420d4b80000748d3fae974edd7d8009375b0d6ba65fb47a27fffece01da9091f56349,
  0x7fffe9771b1ff741681917fa97ee3950e14116b5a180000fbae81ae9491c8a87fffe8073d639a593358e,
  0x80006cf00a1405585f0607fffba991d15cfb96362e7fffe577a0baa192d72a87fff9f44aae40348cdb8e,
  0x7fff361d8cd97f4042f4f7fffb49626e7e15d6deb27fff80f959cc0c279ad9e7fff27ac609e9d8bae954,
  0x7fff8e17f08634bb9bf8f7ffea7e22384f5e6e0cef80010211a54302de6dd3280013a699b2d9ef8cf82c,
  0x8000082d165d4a02c67fe7ffa42322497fe41f489980025b152c00c50ac5598800598ff26946c05dd8f3,
  0x7ffff26b1d7b7e8bd410280002063090a93d1dd6b47ffec4601eb4d25eb9819800068c13981ae91bd279,
  0x8000bff8d2f66e95006538000140abcab68c7500e58000068da9818bf36d96d7ffff946260f5f3bcefa8,
  0x7fff57b4b53a8e677b3937fff69abdbcebf45ae8fb800052534183bc6de76a880003a0ae8df777c21295,
  0x7fe5ade23d37f9d3d566e7fffdd371a552e52273e6802bf68710c539c3b0974800091d1b3b9e97479bd6,
  0x800013a679bdb94ff8a427fffaa280595edd311c797fff92e23069125243d1c800040c9f508060fa6866,
  0x80002a514e0f82d95e14f80009c5d67c9cefa753337fffb060a5be76a44ea017fffd3517ea14e1bc443b,
  0x7fff4d03d9ce61b3aa4927fff92916ae3824fcbd87800031fb61f50930d06738000523f7d268ee41c034,
  0x80011c20b67634cd4647d7fff3a87e0601333e20fe7fff7e78911a025a285947ffdebba704dd55744348,
  0x800018d844a1427d3fc4c8001d907c104abd22248a80000b3c29e5dc7e7956880000d82c766eecdaa9ac,
  0x80000fc18be07ec6cd98680002096f0564fd89c3ac7fffd8d89a822b9dcd69880002fc71765a0cd86add,
  0x80001f3e813c17e7589797ffff857f526b6c9f7c847ffe021ad19adbe27c5368019dcbcd3d46efc29876,
  0x7ff7016607751630c299880002110744b623e3b32980001e241c792aa010b6f80004679256bee459ab9c,
  0x7fffafcd02743380d5fd37ffff0f0d575c1816e9d97fff0576fdd4e13572c0a7fffe180b62cecb694354,
  0x7fff80a776cc515aa807a80008f5556b06e6c3629e800004edf7f1a7879bbde7fff52d0c718b452cd2f7,
  0x8000c0926c58c1409962f800152980882ffa88d5b28000a8274b975aa9ec065800010652fa633254389f,
  0x7fffc6f3f7ba6913d5510800014ea03cb2ed43dd8c7ffee71a9d3f8492fe1048000cc709932918d4349f,
  0x800389f753644c33a20ba800028b1abd6b4be9476b7fffea4d20fb8e9a5553e800085aed423ff27dfb6c,
  0x7fffee3dc1b4f8326d6eb7fffeb9d6e950a631b1517fffec59b39e652f056447ffcb6aee634cb776cfff,
  0x800012e158e9388d1c1647fffbc0816ad38895024a800007086236e30e7847880003e0b125c90c3aa64a,
  0x80010fe3630d3144f70d07ffa389583d3686e1f8d47ff6384b8543a90e1da4b800035b5730eeffa3e794,
  0x800026a588fa2ca0648b67ffffecb55d7850e886bd7fffdfe850b12fd17357e7fff9d1a33c29d2bbcf93,
  0x7fffd594d92db51a961ea80011928bc1cc66a366077fff5ce145ea81afd0fca80005538ece8f30bf5d6c,
  0x7fff285d5a1e01e1212537ffdc17de05eece4af06a80008ad8e383036debd1d80036cf8f7e7f368f0d3d,
  0x80001eef283c5c25406857fffefef4ad5e5203ab818000227740178688654d97ffff5a0ecb04f7e687ca,
  0x8000b49b9fefb62a4dabe8000119062dcf3c6f627a7ffff5dce09ff984957277fffe7540e1ee68c4b8ae,
  0x7ffe46f7277b02f8b263780001695ae8ca66c3c6ff8000878fb673ef57390a9800004397bcc967cfb4ca,
  0x7ffffdabcd373ade3eb9380000286d5d9b3ced6197800552b04f222d045fbce8000155243b0e747b2011,
  0x8000ad307cd372b74dc86800062b523ede5f0a14317ffe94671df0aabfab39d7f92a64139a9bb8745fda,
  0x80023928a60ebd3e971307ffeeda0d4b41173fbb3d7fff77de5cc48862b109d7fffb1517dd61334a3181,
  0x800088c1147c9ab8fa70e800208730e84df7b80651800139ed5153e94d2f5f07ff4454d6dacd155a4a0d,
  0x800168bb815b762490c298000866b2f6aebf5b334c7fff4359d48d15001223d7fff47edaaab9b14212ea,
  0x7ffdef167d549ec5a851380014ed216ec2082b15f1800033fe374026a7ccbe47ffe95037425f674774d7,
  0x7fffd3eb736a155681f407fff3a74f5a1a158a73497fff9af721d96442350897fff19c8c44d8ad60ce4d,
  0x8000fbaf82cb3b11b11a28000493bae390945fb5448000b8285adc0356629cf7ffffd7f2572a8e0c31f1,
  0x7fffec4d22b36b7846eb5800031bc67f893ef424cb7ffa7f435ee5e6cf149878000a92231be9b65831a8,
  0x80037ee8e5c4cc2589706800037bb2b77d268187757fffbe676faa0de8c37bf7fff9b602c1f39924d976,
  0x7ffbe89b341297f51157b7fff9c6faed60b080c5e17fff5373330c3098d163a7ffe5a5bae784fe0d4c8c,
  0x7fffbfe84768f895ab4747fff9f4e4faf6a4d1bd157fff48499bd40fd8159b580007d4536800b4d6fda6,
  0x80003b4970b42f0312b987fffecaf972b91825b3197fffe69778fe6ea5e49587fffb8b88c952093d0bd2,
  0x7fff9a52e35feda988af47fffe7262398987841fcb80024f36a3fe5927776d780002d7def546de2f8e1c,
  0x7fffb6ae9389579fb485a7fffc4b7897d8d9186fb87fffad0a158efe4c1e2318000638c629d5432c4e67,
  0x7ffffe7273362f9072ffd800047ff742b0b754639e7ffb29b56dc178490452c7fffbcd7d14187da714e3,
  0x7fffed14a0844e98fa0b97ffd1c2091c3c287b702c800178c752efe5d4c6b998000c7d70955add2a81c8,
  0x7ffc265ad3339767ccfe77ffcd3fadbec0750fcb357ffedca4035d58a6de3f3800068fedff381649df39,
  0x8000405a437d0ceef65c0800026110a9440b17e73380001802d11edcc615fa68000264a1b0cbe7a726ba,
  0x800047118f1c2d3b380e17fffdbb5a4c9f1d666e7a7ffffac83c7c52545b085800002f7092f7ae64f081,
  0x7fffef480f41703b190ae8000264b1799624c35eee7fffcc9c5615fb032ec08800060b8a4e9657d3fcbb,
  0x7fff1ca1976fd54ceb9098000b18419bd7bd6415cd7fffdc40be1feeef7d3ae8001016f6248a4f46d1d6,
  0x7fffd0b4830fa6e8bac2d7fffe573ba688fa60b7f68000d5aca39b49c4606d98000479675b5b5c9498f2,
  0x7fff9393ca3aea9dd0af180003841d86faf08adce080003bd542b455dee475a800094a5a763803d9fb7e,
  0x7fff87472a41d10b2595980038e0142e1e0b10a386800005e94d05b3016b1fc7ffff63660fc1a12b12f3,
  0x8000acc253ce46e0d088a8000f6a81a78a00666650800138822f25758933dcf7ffd2279eee532e2a279c,
  0x8000300aa395f9d4b7f1b80004578f7877a6fabc927fffe25c37e11de3fb52a7ffba83346f506977a65f,
  0x7fffffd80958a549c00a2800083b6029f31ef0a4ff800010dad6ca474f2dea6800087eec3ea513e1442f,
  0x800013c439cf9b964e7ee7ff81cdd92c230763d1017fffae03e2a4167c9af137fffb529e0ba4bee3ccab,
  0x800014d134c7a30ba69687fffd1e866eff7a340cd37fff755546b11eeb3b895800068a985fd39ff11d38,
  0x7ffd3b868eedd555d8faf800053bb0fce6da1c21c18000257563c57fdd64f027fffd70c0baf80c804c60,
  0x7fffe60a0583776320de47fffec09b1bcd2458ff25800089db4eb5ab2a3bb538000a27534a66c4b824b6,
  0x7fffe80ef003ec17497457fff13d3510bd7aa96e747fffaf7374f47133709a07fffa4a63e46853a803da,
  0x7fffc8eb8c2d7e459e74f80008132fc2c50e3a1c2c7ffe486d6aeb04426b2a37fff83d3f99222f4a4ff1,
  0x7ff8d248bd782e6dc91678000048ad9abf378edc6d8000302510300989b77c87fffd0b7cc7b8e0dbef0f,
  0x7ff90a1b3ea39b68fc8247ffec688027332f374f84800544e5024306faa1d9d80014ec2c3c6d2edc73dd,
  0x7fffadfacf60dea8441b98008052601b89c0e32eac7ffba55776d21cc32228c800a54f5774ea8187585f,
  0x7fffeee8e50033940fa9f7fff9d5e59f18848d971d7fffe0f80ee038a4d14fe7fffa70691b344e725f9e,
  0x8001ed7fbc6c870a134447fffaa95eb6c760d6f7408000256ce15c86039d0a67fffec9f78dd552f1cb15,
  0x800042ddba8aa3cc593e27fff89dcd5b50d76c19267fff2fd1e259e0d6a81f07fffef086f6f137bb2664,
  0x7fd5e33b4fbe9f23695978000cbb18cfa0b7b3d11180004b3f6cf7459807fc07ffff95e31c6cc0c53023,
  0x800428c71900df5dbca3a7ffab6032d2974ce43be4800047096c670c87db1af80042be48452184df7716,
  0x7fffabf2c40e1fbf6c9e880000af15dd8f2467ac097ffd103a31fdc257ff7787ffd1decae18e870da6dc,
  0x7fffff53d4f58c2b936b87fffff213fd351ad3e3897ffffb88146c4958efd6a7fff9430dbc903b4f0bd7,
  0x80009e61194511c4e408a8000bd38bdc5f3bc07eaf7fffc855146e7ea5e42b980000490b4e5564ca59f1,
  0x8000a947741af8a20864a7fff8c1450216d311d4fc80002a6c3d227b977ac618000845d4c9b7ebc52362,
  0x8002b7feeef12565a075f7fe54c95ccb9cdfa2a0387fff5257d7f02cc7f8a457fff34d231a922c91cec3,
  0x80129411c2717caacb984800e57c982dc02ad3759a7ffd30e4d1985165ed2078002e45339d0bd3c52fb9,
  0x800032f7190ce5fa67119800030dcbcc5402afcd4580005546e0981e378ee957fffdb57d7cbf0a2d03ef,
  0x8000c6562b5ed6b88180e80000cd2c5038191c87d67fffd9ce19981d84ea96e80003c6692c327e4efdc2,
  0x7fff347869daa65145c3f7fff52673ec79a93d62107fff3be173758a6b11eb87ffddc9641a001b8a3ee5,
  0x7fff915531527d1e87df1800068ba270a570a95d827ffe684074134e9ae743f800234c772a0557c94a41,
  0x7ff4c20b405cdb9fa92b57ffcd14dbccc163c3f0b98003d62d9b220a3fb1b3d7fef74fd0da522b29a644,
  0x80003b86a282e0913c13080005409a101511e84a3680004e078102e57c58538800a03259995e766a7199,
  0x7fff3c3d4687c75be545d80004893f97edcab693127fffd0f5fbc4b141a22327fffc74c75fb42147e976,
  0x7fff959de7605cdff49ed7fffb11c6bddf09e6fbb17fff398fdf18cc21ddc877fffdb8744dc7989c64f5,
  0x8001e847cdfd4ab58a0988000c5ed6fbabe4c8e2d48001432dc700a9469b0c68000dcd2c336dfe30edb3,
  0x8002965d85d1ee48dd1427fe8c1804d8e4a47bf05e7fb0af21d48f545f165ff8000e08340064c3f4c088,
  0x7fffd8a7dc80b8ed8741f7fffc6252a60f7dccd6897fffbd488ff84d4294b94800238526f325d46c661a,
  0x7fffb9f3631a2f024e94d80001a7b9da9eb1d6626180000811b176ff51dfa507fffaeb06f5f13ee2af93,
  0x7fff0ce06f92c47b443087fff8b8d746f45a25781380011fb2042b747bd4b277fffb7a06fc7db7786618,
  0x7fffc7a1a565fa0969b147fffbcf7dfe93e0a37cbc7fffaf02456f6247d83fb7fff2adda47189515190d,
  0x7ff217d45202286efe38f800046c4b8af6078b747f7fab616ce47aa9df1cc927ffc28d32d35ed3d413a4,
  0x8000d4b31e06274dedf7a7fff73c986c2b29d1a4ba800080e4afa2ca235eedd8000b503178f04365ce1f,
  0x8000249a09e40ec7f7df28000623dd36fa22ce43f07fffbe0a9ff7ffdf4b1d07fffe89f2a119a8971bd0,
  0x7fffcecd9e5381be197e08001e14ec09dad50613af7ffe87d9c3ddce2a99eb27ffed9d9a61efeb383794,
  0x7fffe859f494442e4c3dc7ffafe0dec76d28efaae48000aa88b55c0f90a5f597ffb5370d84d55fecddf2,
  0x7fffc7469c4a57007ff5580002c08713eabd9cdcfb80022fa20124aba28a61a7fc149b31c5b7ba3ee151,
  0x800040e8875d76a0421317ffff5fceb809250ecd0d80003b890131d77f7af8a7fffc7b604bd80f02dd4a,
  0x8000f2a61638db48a9cc680009e7fa4217917b65578000273d4d11f867ec3977fffb7a50242a341abffe,
  0x8002570c51c869ce1a3318000b06029b7f6615e67780023bea8dc61d80282ba7fffa5a6ac7b12dc0fcc8,
  0x800025ae7ca09078e856a7fb8f7b06c734b044c55e8000203482d37ca84e8317ffeb22ef30a2d753b58d,
  0x80000d4c279b50aee90d3800034b49336910523d5280003e87344b2207680c37fff5180847bd17c962a0,
  0x8003397566c1f858c64fa80003f7c3207578418a227fffa731a86c719f22a068000321983c0b2824438c,
  0x8002629453ccfb6a8d3de7fff6611d3fe8faecc2688001b2e618135128674ec8000c1c24b9ce1f9306e4,
  0x7ff9e3c49ba4625892a757ffeb60395bdaa9d4c407800294eafb44783c7f9d280017c2b1d87d75873268,
  0x8000aadafd1e7aef45a387ffb1ecac4ed50ef5759a7fff5ce39154460234a807fffd6a6f83d2160bcda0,
  0x800013711e9124254eeb87fffbeba8d873f5aeeca180005c8a334c814d2bf3c7ffe658a6bb451594bd17,
  0x7ffff7c1d29c5c3b1044e80000be7e4c53f4a0b99a7ffda8b6818a606acf3b27fff41be7a4a997ec3f19,
  0x7ffac3de02b24fd320df8800001e1dac7d053f07c27fffe9f690ced16b281167ffffb0e651d66dd1ebeb,
  0x80000f86d29ed4e664ca180000db73140da71b7a947fffe9a1588fe4cf8b4857ffdf4773619613870f53,
  0x7ffff86a50841ba2d88858000141b0cedc276536ae7fff3687b4db9fac3558d7ffff32a49e602d4bd798,
  0x7ffff0b04d8f0e34469dd7fff853805fe7fe969e5880003e5c22ff93426f83c7fffd65f06ca1318e56cd,
  0x7ffff472884acf340c7737ff946ae2967edcf079877fffd17f2136ac9bd20b57fff2f7ca2fa5a1c67ccc,
  0x7fffd3cdf1c65804feb648002268a0e742a95807617fff4f42811ee08da4b617fffc027f05871ebee3d0,
  0x7fffff1e46b9de329dc457fffffe14d0b983d9fee77ffff0c7d2e64af78d3c77ffffdc080147c2a896f1,
  0x80005863e5e5603de05a97ffe668c2888d163b009c80000893355c7ee56fa7f8000bcda578c8e0792286,
  0x80006568d80ef3a1c26aa7fff8db03ebf74f0caa428000bc76fa3f0087838977ff5e743796daa3ff496d,
  0x7ffb14ac45882578848e47ffe8bbee30c95e894b517ffffb9382f8aade05c4d7fffc52d19d3f0d4fc413,
  0x7ffff0498f30c364827cf7ffff4f51140f6c94d3037fffee1e3221f55edf7407ffff30e1bee76a8b0304,
  0x7ffff58441ce88073dfc67fffc55f3151ee25342dc7ff981de2e5e22f8917bd7ffff3e3c529817b88d2e,
  0x7fffbe8260a214a84c5727fffddc4f25e9cf6710d0800009ed6ab0e4e51fa40800012c25a11ca87cc47b,
  0x800003a75ce566270d74380000ba63ad01d434e1f4800007dde565d5586eb8680000ad3ea6b99e4085fe,
  0x80000a901a06ed52f692080024cee82178235c5acb7ffd912a7f235781273d7800021044ec4fab9dc61e,
  0x7ffff8047dc9beb296cf37fffaa3b813e2f0889bbf7fffe02182fe9a8f2131a7ffff0b980948ddb9afec,
  0x8002e9463909cf4abb82f800006b7629731a51b9357ffffa256558a2a4d4e7480001c6723fb36de77575,
  0x800013eef5742ad1678a77ffffce463ca1808b0a577fffe69fda8cc269cc85480039ac71c39457451387,
  0x800007260edd7a4ba7df07fffd58492cc935a83d21800005ab1f6f1ed5f300980002b2402d0e5a49ba1d,
  0x7fffc56d07dac8a6c1ff67ffe7711dac05e5ecc99e7ffcf935100aabc7c0b0a800016dff71317993f2ed,
  0x800032d7d81ed534f1e0b80002904ddb784bfb179d7fffcd004bbb423fadaa97fffea71602b9173e838c,
  0x7ff57e3359c87689a2fde7fffe27e94d0e4ff53bea7ffff1288a313aab3b1e07fffd2c400e0ffaf0b2f2,
  0x8000063b40034ba2906c480004b1c1216d67a536197ffff7b732428c3280f9d800006f3d36683a448de2,
  0x7fe49bff5acc9dde503947fffdc7ca3a8d47ea3d9f7fffcde4318faf5f88cac7ffff62b851ed877d7bef,
  0x80000297914962b8a2d007fffdd5bf579f766ea6b77fffde5929f0d009126408005b1fbc5907bde1b127,
  0x80003ed7ba70240cee1357fcc4515a7aaadd1b599f7fffe9e30e18383c3bb507fffd81247818626fad49,
  0x7fffae64ba6e256a2d9267fffca08417578403bebc7fffc231cc8181e9208d27ffff981bc9b358470a9e,
  0x800042110c575170227158004c5afa24f15567c01f80004a4a89351873dc1ec7fe602e3ffee067fc35bb,
  0x8001b366c516022222f218000355b836d5e98223177fe5c39e3f4283a273e0d800009496182a41296fad,
  0x7ffffaa8e088c7eb8d7c97fffcf9fb3fb342810a487ff970d5f01e0eb5a19ec7fffff420d6569154e8f1,
  0x7ff28864355d1794a12947fffee22ca12d797bf9ac7fd6c61c3285e5f1b53ae]

/-- Packed radix-`2^84` upper-triangle words (`+ 2^83`) for the full `h1Hat` Gram matrix. -/
def gramTotalRaw : List ℕ := [
  0x80011dbf7d92fd37511f17fc20b3196179e13bd88e800021e4f2b01dca537267f289f0bb1b81ca725288,
  0x7fff1c8d7e7f43ecfd9c57ffdaae2614e1c986acd9800042943ec4cf3da03197fff3fd3665694cbef938,
  0x80022feed6a3ab783dc197ff9b503a9b07377a29df7ffc8c1796de37f74d2e07ffe246eaaed007a898aa,
  0x800dd20ed4af4e287c26b7fffc342a26b90858b3a27ffa753d5474e0a58bf94801a1cf78c85e593a4187,
  0x8006215efa6e27ce7b2ce80019efaff2bb8a0909778000e37437026c95d19aa80025cd382c73c2840a99,
  0x800004da61a4f88acb2a280000a5b333d8f630e81c7fff432b200b1a9f312d17ffdfbc40f9b685fb8c2d,
  0x800088f8f1029cadcd9cb7ffff0af1e2ccf35f6c4a80009a951ee18390f790e800098158a24a52e2f1d2,
  0x7fe912eb884176b4581307ffe8c9eb39a99eba76418001970219dd5de47635f800050b5c40d580e8674a,
  0x7fff6e9edfd8808f9a49c7ffe9121d3c2ad2955b847ff5dfea86baca047197380002223544389c690615,
  0x8000e083a6edc76fb62657ffd5b04a8222808e8091800074cc796a2f41a925b7ffa71f7c022924446ba2,
  0x7ffd2e5b79326f36a518c7fff7fdeaca4827bef3d07fff8d49c5455275be61e7fffaeb34508c5ae28745,
  0x7fffd384951a5321829ee7ffdfe16919b0b7652e9380043b6187767606382cf80008b7b9f0c4846ee903,
  0x7fffe4ca9d9e0e73c433b7fffb7b641e8c0b1f57407ff37e3b3628506946b2c7fff95b910defae097dfb,
  0x7fffb1479731f713f032e80006061d48f851b4bb967fffd9f74901be41883a87fffee353a69e1dfaafc8,
  0x80001404cb9f92e6c817b7eff11a7e71707e03364b7ffffa9f1c50b5aa4add380002cea6a2cca5ecc2c3,
  0x800187aec32032e39e2538000e9eae4ca312ae7a4a800abd81204be9294aa2d7ffe51dce52f896d11dc0,
  0x800004c63b1bd9b258daf80033a076f70bb53f16647ffcab75e4cb0f70498477ffe6193c4e8d4731956c,
  0x80000d331dbd44e8453f2800083bfc56444df1ce727fffc63d3657b424c6c0780000d1f66ed309685e3f,
  0x8000a10bfea4b7ae10fc97fff9b0d1831f617b3e13800008b7001da0ef91dc87fff976cee5c808ca50f6,
  0x80060e7f9e9814321deb27ff9ea403a9ff168f44ef7fff8b052e18325b2b28a8000812d5325219b69e0c,
  0x8006713420557c28832617ffa1ddcd853939fbb89a8005178c42fa6ff32b14180060647c1be64aa641d9,
  0x7fff380474698a64f4e518000f7842c8ba1be9699d8005c4d0d4b5ea514d0797ff9e7b09c0a7fc3aa524,
  0x80004994b6130c2b38a20800043bedb17e6ff1e6fa80002778a68dc9d1bbead7fff7090c4d89e52f4523,
  0x800030ac264c355852d4a7fff29b47bd9a7ad0baa0800002ca312d8f05ded297ffedc9a725b6e6a7d90d,
  0x80001fd6b5b73d72a235c8000d696da5718e4f05b67ffd58110488988a751988000939858a3212aa3b0f,
  0x800004da4502d2040938a800025eb9e8d03e7c9cde800011354b58d67de2065800012f4cac2f4ba55dde,
  0x80000d62fa7718079db227ffff8a36443c6700c0f77ffffeb787c72a9ef42c67ffffede008b87efca3ec,
  0x7ffe727d30e3acd593f318002f351206b12b8f7ed3800149a299141fb0bdea47fff324df872e94786f6c,
  0x7f26b4fa06b3d3a763a147ffea387d96804b437e7480015e32a1bc40287f5627ffe537a2021408e71041,
  0x7ffe3dfa60aa2643dd6b87ffdcd119f29f8ef633047fff6835c5e5aab7370257ffdb49ec313b7155fc28,
  0x7ffc186d52b30b207cba37ffd820d90ed91b6aa6367ffe80516353ffc4cc8f27ffcf77cd6ff617557e75,
  0x800178298671a9a662c397ffa84f1fc4f96058eb347fefe3ec949850071cb848007718f6da66c60c4d60,
  0x7fff2ba20888fc6ee66e47ffec77f87d7440892bf77ffee4f3dbeccb9148cfb7ff21aa766eca816d8802,
  0x800026b5bb039e9d9af8b7fff9d0c4a7a25e1f200a7ffe7c0baa8ed4396c3727ffa0d4fd06c614215a98,
  0x80002575584d81859f4778000c6fbf6ae0796256a88000a75f98b8110f86ecb800028c973a683b80f964,
  0x8001705bcfca10f0dc8d57ffd348a71f7c3a731dbb7fffe669f2572c6d9e1858000c735086faddd2f0fd,
  0x7fffc5e3c38670bd1b31e800a5cbca91bef2070ebd7fff0410822f655a349da7fe687bdc820aac6e5f26,
  0x8000dc2de13611925604180020c7da904b3d8566a97ff8d5d8234eea35b3ce77fffa39b9a8d58d12a82a,
  0x80022ea6b871fa4987a777fff0150acde0f452a6757ffed1e2b991a08595f2f80012ad1b3eaf900029ab,
  0x800235378b4bcf1d547eb7ffc25fd93733ff18d7e87fff98c1744cf35a145988002bf829a7ae0dbf99f2,
  0x7fffd29f1b5f651d3e78e800cdf380be94a18cf9a27fffe09b0f3360f8991cc7fffaa644fd94d32e7358,
  0x800022241cc57146a480c800008bcd012c13ae863880003da5b042d49c8e9947fffe79655bf6215ae98d,
  0x7f41bba31a517245a3ee07ffff59e45d36f4b749668000080a6268d317685237fffc531261a7658b6ca9,
  0x80067d9866debfe016cf27ff7bd839acb0acab19f27ffed1c96b117830509fd8007a048c299c99e2b98b,
  0x8007b5040b189671f13e68009bbad7d95368c71fd07ff1423063674eac34a0b800bbbb28973f3f4b6e45,
  0x7ffe694b5a2c549bc31d07ffee3f09ffaf35887276800610cf7799e57b699b3800c41cb7969e2526c74c,
  0x7ffeaccb916977f9dbc487ffeb85a40f000666b6a37fff570b42d0317fdbf7f80011065bd4aab983a065,
  0x7fffd1d4ef38b1d88986c7fff03336cc13d552368e7fffc53dc14c739718e797fccc11aed952aeac538a,
  0x7fffc88656c2bf9762b5480006c3f710ad5587ee237fffde77143bd47015d06800051774841460842dc2,
  0x7fffb77ad4736a525897d80111780d6d75aaebb4d27ffd398ed2f5360c55fed7fff38dda18e0c8ef0562,
  0x80046c1578a79761015f58000ea4dfb077a7d07e33800001b90a7fd7a0f301a7fffa2d253052d691557f,
  0x800392b7e02a0b7cfb04a7ffc259f6d277051fd50780017974055f024abf6e380012b217a41c108247db,
  0x7fff08f88b09e813dfb3b800027d3386724297f4ee7ffe62a3d681262ddbbe080012a9089c5bd74e6793,
  0x800070bf36c7d4015f4668000201f5924a3768755c7fffa764597a7676a996c7fffd9695c24ed2ba6db8,
  0x7fffd556acbd9f926f4997ff45c512c1fff0e2bbba8000bedb96fb4fb99bf8380005e6cac88f1e9f85d4,
  0x7fff300c98faff6190af87fff622d86070dd502b8f7ffeeab86f74782aaa3377fffe658c34b190d9444f,
  0x7fffa721e24abeacbee127e3247f4d5f59541506e5800070bab9db6bb06e4417fff388bfa457747a8dd1,
  0x8003d042c22e936ca9ed37ffc1aa804a73b2aa5e917ffc33241cac6ca037cd28003c581189040bd8b0ca,
  0x8003429ed896a6b33550380032dd8e69abb3a2320c80030bb9e4e227b02db648003235ef591e3c4adb2d,
  0x80015cc4a355b86d289e17fffe32c1b47f81e56d4280014117725f0dce2edd57fffd17fbb49dabab0871,
  0x7fff9eeb89af1f4391d907ffe20e6abfe52222028d800177d4ce776006e610e80016554f6e355269b37b,
  0x7fff9c3a8599e820ee678800051d0c88d8d9ddd77b80000f807e1ba2535fde68000618baf50ff7a0fa4b,
  0x7ffeefc95c37a26561e8d80003c0ffd514f8e76d6e7fff820c0257bbf438b90800050625bdfe2d3c2ac8,
  0x80003fcd2768a563b0c347fffb34da8aa34c596a6f7ffd1bc72a21331479fca8001d9e322026e005746e,
  0x80021dc1a0b899e07bca98000f3acf28ef11a2d4fd7fed0c4356f3abf27ca867fff627b1d5bc454c79a5,
  0x800198e9c016c610fd1f480004599b0699d290b45d8001b03d7cd953e84a57b7ffec266edcd1edbbf416,
  0x800126730e0af3a82743980009f88e1ee6ecfb8cfd8000b0c7ed295c06c1ddd8000d2c245a9ec83e8876,
  0x7fffad71d3b90882d135a8000e4c21a427fb5c860e7fff90ca3b7c2478b967a7ffffd3f956d9dc262c68,
  0x7fffe0705bdfc907745557fff3f24a32e0a1a7953180002c2863d948ada0eda80004774b0d2d84322fe2,
  0x80005f203c136d91b56e07fff9f531e1dd02f5d75d80002e985e9db6b25d222800030c59d8ab883c82a4,
  0x7ffd80ef0aa4eafce10d2800256209cd1a2e2e4ab07ffe13442384f0d8dab8b7ec84db8905c87fc3d1c5,
  0x8005ec3f3124cadcb90a87ff9c42de85eb5c95fd478006513f41a256042bc2180027633e21ee77fcb3df,
  0x7ffee9c456fee4189becd7fff08b75c9a83d5ce4ae7fff5e75a585c4d5c4b917ff9d7954794ff6448f5e,
  0x800076098f33d810c411b8000a136f37630b0c0af87fff5b7b5e5e4ad304f337fff7598202b3a0f22373,
  0x800070eb04151d5957eab80002781f9f589b6325b080009c810b13e7672e52a800053effda0d76364614,
  0x8000432d8411a182c04658000a4e14c96de5073dd17ffee373aa9adf1eb407f7fff963cbe3b3f4836cdb,
  0x8003ebd9f1208c536f1707fff5f8c8c60f3246349f7fff30da28f28ba611bb37fede8387a4892e011e1b,
  0x7ffcfeb517dc2d1b6ae6d8000643021826047087658001b7a07d28b93102c4c7ffd51b6bcb093beb124c,
  0x7ff9a87b7e90b0a602afb7fff9e2c27d6c4f9ba3178000ea78edee4774617f47fec4a2fe99ad27ec4553,
  0x80022bfd21dceb541f62d80000a936493be77387e87fff8608684288f03aa1f80047a152b3c3ae5d78cf,
  0x7ffcaa54f9e45f021ce118001ab673166ad95db6558000a667863a3c3398e047ffcb34fc7a568774642a,
  0x8000ceda308aee3a48b1680005803aa33fdfdf85c37fffa1846dce94ec860187ffecde3c06caeec43efc,
  0x7fff4ce12ae8d7c0f3aaa7fffde6e0c21cb6ec2a8e7fff89d9220ebe5bab8e07fffd0e5b9b584533dd58,
  0x800a7f6c9bc698b78120a800538d0c1cf8ceaee5f77edd8994f17688c4c8d0e7fffa76df9f27ad59c096,
  0x7ffe62b1a69564d9023417ff8dad4c85803e4c22cf7ffd8b7a4d47163a923c37ffa9b392f17619903ec9,
  0x7ffe8460a6bf45c162bd68000dfd4bb56c16256209800083a7873a81a425a9d8000c31465897d029ec4b,
  0x7ffcfdc3b256c805e932b80012c48ffd342301e2068000b7a681bba6c38c1ce80009f3ad753ff9959416,
  0x800249455a0e70696e1c87ffdb4cc81fe78c0e30e58000b6bc502adfb95af3e7fc2a138b464ef51a8ca6,
  0x800189b347c9515bf213c8001f64806b7f9c1ff8c07fbe2ffbec975967694b7800034921842653b1523f,
  0x7fff28b9ced26a042aa5a800720cc55374e0f04eae7ffff7594aa4f8d746297800581aae5abe14c9da45,
  0x7fff4bb736a5fd0ae939a7ffd4a027cc9e3b0e45c47ffc8ef826afec72bfa6e80016f40d157fac97a1b8,
  0x7fffa721f2d7568b4562280106dd2c87322717f05a800946e1f83445ed8ae8c80010a389f99e7c1bc4fb,
  0x7fffbb665b14fecb375d380002eda5af414df022c5800198e5071c16ff3ca0e800608383c12325bac0ea,
  0x8000189bc53ffde76bb8180001a0cd4098697c5e057fffee5e74511f19c43cb8002f4edfd7272758734a,
  0x7ffae08424c68ef095bf77fff718db32ef90d688d780001b6ace408d0ea61908000284144b17e3d8a63c,
  0x80005ec23e20b10aef5097fff78569f1ef724e339f7fffe277d41d070ba5ed380001b2188f7a9834eda1,
  0x8008473fae82dfba48e467ffb1efb9f9dc4afc5ea47e7a1c7d2d59d45c98fac7fff8b34a347be3a9de14,
  0x800d5eea1718d64798bd880023ab71b7d0fbc3b0537fffbc569cb7d7513563d8001a503b6ced803f7903,
  0x7ffee591d77b21619ab017fff9e7313b3988e58d597fff18309375258e032be800005b1f4766c4a340ff,
  0x7ffd646df77d4f777c58e7ffed2428ed716e9798b07fff038bb1c62742bef927fff7970a5ce75950b2a3,
  0x8002e933a594e581c5e71800019f3df0e39eefdd1f8045510eca8c85e489f627ffe0484265daa0ed9f25,
  0x7ffeff3e8047efba1e2dc7fff64af0e63273825816803d2d1db17245cde5fc480031db3900f536f2d58e,
  0x7fffa894d93a3841e7859800110b9f66a8acb381a38002208b9812e02a5b70b7ffcdf320f4a59ef12517,
  0x7ffe0fb0eb3a6fddea7ad800459cb837de8e04fd1980046cf6be339e79b65898004619d923a0c6c7fbe9,
  0x80024d850225880c11ddf7ff64125f8d3d396ad60b800ef60234c4b148a337f7fefe1b3be1ed1d8251c7,
  0x7fff853db18424f3774e38000cad2ae079554c9f3e7fffd5ad90ac399bd11bd80004da9097281fec8267,
  0x7fff74278e6f4227b7a5c7ffb51c6bb3d4774b07d780041a04c45f2297555998000699279c20af1d53fc,
  0x8000db17e75ff8a58e4a07ffdfcbcb8f74d7bf3c658001562b96ef876a09f84800089a50d2597709abab,
  0x7ff4213cc6bc1151793d0800143c541741bceefcb6800067939a4ccd96a1b2a7ffe6c54675e00ec9ab4c,
  0x80027d5148d5df909938f80048c33298c7d9e6a85f80063f42acb07a27acc747ebfc4a3ac14ae4b6d792,
  0x7fff84503e4b0df42b19c7fff4388c5a4704e86012800166e707fbb2107736f7fff9b49176f3ead15c4d,
  0x800016481536b49e49c9f7fff2d8932a216dad41067fffca7d3f6f9ac0aae2e8000b55e56c876285d9a5,
  0x7ffea9c906c209b17a5dd8042471714386a68bb76a7fff05a0534c6e1d388f07ff896e56abbbe665df12,
  0x8002c3aa9ded891d31a447ffe71b29ccfeafbd2d79803b9425c8989d9e48ee980011b3f4160a575d684e,
  0x8005c3064ccfeb1f411988000cda04519fef7e005e8004dcb1ec0b3dbb37d618002960fcb94afd8f7a70,
  0x8001d667ae5d774610ec88000f1c8863bb7896c4a18000aeef965867bbfe72f7fff1ebbc32a82f364a2a,
  0x7ff662aaad2beeb9cd4507ff8c3fe6590480d0bd7b8000833871d1506ea0543800331db100b4d806fb46,
  0x7fff4a0e6ede542f4f114800032fa5bc096493252b80007e5102646febab6bd8001220fb60a100b88aa2,
  0x7fffafd5e7c43ad4e2afc7ffff4544ae3d8c424512800060e67dd84b5d960817fff0d40dd0cdb1f97b09,
  0x7fffb3a255459db1b19cb80021d59c74489d61d1817fffdcfc9d7e9e71fca5d8000a11ed9e8701478d2f,
  0x8000947df069ddaf6980a7ff9d3843899bfbf2df7d8000ece858dca3609c4c37fff771b14c8135b5e460,
  0x8000cf2ae9f692799fde07e86187bff7df36f33cb67fff307c632a27d74c1eb8002d004ffecaaf5bb61b,
  0x7fffd8d5781ef4255abb17ffe2f1a3b2a3f5fca4767ffbdd2f122ee794542a97ffe7ef9e180fb7380877,
  0x8000c3d011c8b6a4e539380003fb835eb1d7ca7dc57fff8cf7c4aafb64382ce7fff20acbc16b5327fa13,
  0x7ffd20a60299553fdc1927ffcb42f3f332ea24322f80002edbabe71cd5e34a7800014eb540ad177a7113,
  0x8003849a84a6b6a2d38318002acc08ed121ded013c8038def58f4b29026c11280009485987046cc43096,
  0x7ff86e67d8cefbc54fa0f7ffcd10bfdc52ef1e62bb7fc1f7c5e9cdb0dfc5f038000a0bb7ae13fe299035,
  0x7ffd8ff616430a0b985e88000056799c1b4f23f16580005f38044f797cf6f9180033e2334e4b4d0cf80c,
  0x8003a7c9e7fbb6c5a1d487ffe1c6e93dbf8d463c2f8001efe45d08e088feaad7ffc41fc2fc1cdbb128e6,
  0x8000137992808907fddb87fff13afeb25c7eb2c4547ff908a6d8cbd2ff7f8477ff59fab202f05981bd7d,
  0x8000648dc9b320af75d5d7fff3c0adb248511fab90800034599cf0336a0a3627fffd74bfc76b0b70ad14,
  0x8000c92ef5a74714bf2c67ffd5d0fbdd7b8cce4e007fff0d1014d003f7eba398000a1cdf1e172e833114,
  0x7fff0f971922daeace8678003d2f9b3529975978297ffefd57afa17aeb000e5800228c2571654f4c7029,
  0x7f2807dd08cde785063d57fff8466d0dbfc0ad9eb780012e318e6c137ba33c18002714c647ae20af5d25,
  0x7fed759a3e219206597007ffc46731a25a92342f1b7ffe5974b8f47995d41347fffaa00e93df881462eb,
  0x7ffe571509d3694b5115a7fea86477b556375a20ad7ffee16765141e21c86477ffd933907dd9722fe16b,
  0x80025783182f204008a0a80003ff0aefe5814b1cc27ff9c4dcdfd9293e410b27feb72aad8f364901391d,
  0x80004037e29ef4c3ea62e7fffe88ef52b2c5cfa1b680003fa34acd4f1d90195800001c962c4cebb41fc7,
  0x80007f7ae3a1d2d47e1ce80068367f2b22c6de8a127fffdc4fc215cfa1eba3a7ffff19d5640796cc907e,
  0x7ffe97bc638d151bd02e67ffb4af171392b30e718d800d9eb35b3ec4b5acc147ffc2d1061825eb9a11be,
  0x7fffba218178d533ee2a180008764f64868b1154fc8001ddf9b69d9e80609f67ffcf817f3bcbf8cad026,
  0x8001e7ade21cc293c873b7fffb210c8efccc9e76458000168f33322958121fe8003be574072d9b00fd30,
  0x8000e2f404dfcc0f04b9e7fff58dae0c98b004d50b801f9ca264583a94b9c3d801643db1cb9b04129fb9,
  0x8001e38cec0683c9fabba80020097d093421751fa87ffc8943177cdd860045e80040bccc9fd44340062f,
  0x7ffec9cc4d8c50d3bb32f80001edf7d4d3514876d180002f6978e71b79fcc6280001585c4b856a46b50c,
  0x7f4f272cd7dd978b0d7cf7fffcf521bddfb61f06777ffcc8db9e9160230b70a80000bb088013f5dee6f6,
  0x7ff3231f64c181b468297800071f833e4592da63ed7ffe321a5bca8dd8b95ae7fffaa45e86b7dcc84bc0,
  0x7ffdd06c92a28008324357ff137dd976884de174107ffebcc66a473e5537ff78017f5089ac51dfa71eab,
  0x7fff9d477bddb60ed48a080004b2d6f618e53d22a57ffd81c284be1f17763df80016e1a62ee70f966579,
  0x7fffed0d244f72e983c5480024a81977cc196c990780005fb71189a3d12ce3880001d9003423109d09ea,
  0x80051ab7611ed199ec61980008eeae7a6c78665b057ff802204f0c6b2693304800035d413c8894451e56,
  0x7ffd3a96dc5deee9f09687fff6e1d4088c5ed6832f80035dd92dc1cea7df41a7ff692d4a3f0321aec1dc,
  0x8005b3cccce642ac5d02e7fff65f6446745f16a2798000284deae8207cfc0777ffeae021f0c8ed19a6d1,
  0x8000643bab73feaba77ab8022873537d6a905fd0f78000a07a4755780374c69800043f6a2ceb230ccb4d,
  0x7ffe28201ee1edd78f74b7ffe509ba406fa5faeeb5801d4dd29b2f2386bef87800222cbdced66b1d2af8,
  0x7ffe8c10a43f02bf2c5f97fffb92c701699eafee7c7fffe81272557aaa348697ffde0f474607bf2b07f1,
  0x80002033555475429700f7fffe0d4486a0886039a07fffda9e23dc51812241f7ffd4843074895f3e0b47,
  0x7ffdcf03866a9779d88f27ef58fbb8f0b6f0983b14800010fcd9c11dba0ccff80000018097e3ecfca9a7,
  0x7ffeae1a2f5b86c66235b7ffd28841ee94826937767fe65766e104dd961041b8001c254fc7bbcc414b71,
  0x800044cca783c9a73fa7d800174af6f3dc2986a40d7fef8f7dff5b9615277847fff59593c7aa9bdc7a85,
  0x7fffc4968c7abbfdeb8018001fd076e9c3abfd9daf8000223adb8d81d4adb437ffff528d5ec56f227188,
  0x8005a3a1ada05d909481280031bd1371cfe5db833e800025d7d828e30c3c48480003b99d0756fac25382,
  0x8003c7cf5d7891502ca9e7fff818233d67a23da3c680021e6ee29f85edd1f438005fce39c9f4fcec463d,
  0x8001b1f44733884f061dc7ffb1328a73f1d3b2b9c17ffda2d4a92270a3ea31580016d5271620fc7f09d7,
  0x7ffec057f3abe32134d687fff2f24f5979e80c9b968000d03d7e6365c0a91717ffdc25d6f9a417e72edf,
  0x7ff6a68ce924e6c87190780031e104b172680afed67ffcdeaa5cac0f538c4608003f5eebda89413a2c92,
  0x7fddde6c44cd968c4481a7fff249a07bafecce5bbb80005976c047a20be91b580058de3b2b441e320cd7,
  0x800353bb8af369fdc51138000575d10c25ff2d1e428000031cc6e35e30d469c7fffbf77eacd3d8bd8844,
  0x7fffce950a46336beead77fffe7bc0d2a792a65a347ffe89b444b4207eaa5ef7fffac9b2945c253c1cdb,
  0x7ffd44ece073c921349808000a214afef2007fa0667fff702cf0508c9415dfc7ef156b601becc6c23ddb,
  0x7fff32d7f27d4ff0efb9d8000ae71a1beef933cfe87fe65930c1a5a08fc1b3d7ff7b996c806097ab688f,
  0x7fffce8b92beaabb4ad7f7ffa90e221da36bb9894080003a4fbd9b966614caa7fff98958a8a871d22ecc,
  0x800039dc1738211af772a7ffcadbc2fe95b18560c47fffb30d4fbedc8860923800049c0b2f54ff1af500,
  0x7ff47de7b67fa9013148b7ffd595010d5ecdfb2ade7fffa44072a9ce953642c7ff9e08c6b06650d103b4,
  0x8004a2e25a27ece5c103e7ffd8a462da5051c5e5cf8002a5538214c6efde68f7fff504ad66c77a69d184,
  0x7fff3b23bd0fe791439f180008ff0f02cdea076cbe7fff54f3230e9dd57d9eb7ffce87885baf4affeff2,
  0x7ffc0fcae24ac3744f7238002bd9b6ff8078cc1e257ff4d1916930b34429e1b7fff8319dfe88c5b81c2a,
  0x804cc5097312ed0c8694a7fce40a5892dc2003c8567ff9a0f84dc320e2b640580036309ff6de176b8da9,
  0x80001653515159447cf697fffe04c7c501bc716d1880009871458c3080d14e78000c5bd8fb3741a867bb,
  0x800039753e47ed0ac358e800001177acf1e0c385178000318de7aaae1bfd4647fffe0ac1d4ae0a037e01,
  0x7fff42db77815c5eb425c7ffdbfa837af7fd76cbf97f51d454582d3f11d0c558000527d963e08938bd31,
  0x8000fd71729944be7b40d7ff1999d9cf1133a699637ffe72c1caacdba6762867ff26a5273c7de4d08e95,
  0x800009e715dda43abccdc7fffc8341101db038975280005c59947d093438ebb7ffffb20083cd95cb3197,
  0x800005302834f3fc7340180001164f3c4290f35a5c7ffff75aea138f5236b337fffd2d8f96b3ff051401,
  0x80038065999a137afb3fc8001631abe47cc9bac1bc7fffe21dcee74699949d37ffe3bf21d338e35e0211,
  0x8000956fcae4b58ab313d7fffe77e7c3a13ddec85080008a4fc9856def9704e8002999ba8c9e17876c8d,
  0x80002d4777121d41002047ffe9afb8e40893dc96d67fffcc6a08462b59c732d80008116980a60d27e67b,
  0x80031d9b6e0496b0549507fff59f2c41eeaaef7b378000b6618d27cf6c6e7c8800057d5be60199c9ddbc,
  0x7fffec6a89afb5af2b9a3800175bfd6a773df5fb43800083e674160d14168de7fff2a09fba307e8644ae,
  0x80000cc0ddfa18607c6487ffffa254d62338e0dbe97fffdd54ed4070baf20667fff22efec6a43560bc0c,
  0x7fff3f889aee4cefad37a7ffff5956a4470fd21ede80005c9c91990b0c1cce780000495b04317d151142,
  0x8002e46ba11678b92d38b8009023b78880075794de7f84d49a4c85f0ae236b07fffe52b9d23f3b5b676e,
  0x7ffdad5d0f8d434b3232a80007d5965f6a57cce83d800acf09093877f35c6ca7ffe60c2357a1988ca8aa,
  0x80001e7e208f96d918e0a80001e7c3855e1f58422e80001e04ef35a7e58e5518000080ec78c9bcb3f7ce,
  0x7fff64f44968e9a79b4197fff75fc8b5f42ec045578000107333a3db0c823fa80001bd1337808927b036,
  0x801d5eb9d3ff4907cb5598003844ecd73aeacc42ed80002f45650c225db7dde8003594f681f765375200,
  0x800071a450dd9772449a380029d8327b9401f66eba80003f2b5921a81e2e25a7ffdb0d73a1a88c78b7a9,
  0x8000fc8a892d3a7b2d6938000cecaa7ae548ffb83d7fff78dc7d2dd539a7cf38000ec97d34e2aa4c5163,
  0x800a41a9ab9171973b46b7ffd828a4309d2aa00a688002cfb7ab90187318f657ffd75320324267360a5d,
  0x80035f090ebda467aaede800037427bfd80dc71a308003a84c0af5923b477287ff9f4207b9a490c77244,
  0x8000683215031fe1a565c7ffdd0a98b4b4c27fe9cf800015e3c3eb17cca7f39800067df909ce6776071a,
  0x7ffff736c19849fb0f94b8000280d7a808ff6227bd7ffff79f651043112ea72800037e094be381d54051,
  0x8002a9d9e7144c8ea1a31800a6dc96631bce69e399800248b33d86a7ff43ebc7fe3aeab8bc205656daa2,
  0x7fffe64ca6fe56a7af6e880000119011e1a7c75ed580009b22eb3ec91b475eb80008d532a9947225d251,
  0x7fffe9402c128748207a07fffd0815273e3271766680000738203a54a225e197ffff3a3f388fc8156937,
  0x8002ab6a87bad4c74cdbc800127ed2eb2fe464bb2f7ffc4cad99ac25c5bc2488000001435249a17c93e7,
  0x7fff6512968066892d5c47ffeedf0c40d758d20e058009c9489e6dc15f8900d7ff92a32b01141fecab08,
  0x80025e8afad5f12074ca780008b422e8d3e506d67b8001a647dcd1ebfecea288001482b6eb9cce22d3c9,
  0x8000da3bcfc05289ebfd6800b94012ae657b20f72f800027f9d1b28943bb0088000abcdde2f3326babff,
  0x8005fcf4b39e6f74fe28e8002b9c352c29f3ee9fba8010448bc7915d5ef007a7fffdb683bfdb37e5c88c,
  0x8000253c0bd32633e31637fff9bbb1f856e58ba5f6800165d013d1ac31931897ffeb8fa459644b1f47a1,
  0x7ffffd5fdbf7b741310427ffff9f61f3f9bab3acd07ffff9b6adcbde5d9f3ae800106deae6a65689de34,
  0x800778c69416133be95c57fb8647cb2120dcf629698000011fb9a7aee723d667ffffd133374cce69a4ed,
  0x7fffccf07775a3c8b3c798000052b91ea6e6b9bec37fffcc4fda526ca5a13b68008627a727b827057f6a,
  0x7ffffb7fbeed4234eafa47ffe69a0eee59275b3c487fffef51ae1dc6a195b43800050b088a30e814e1f2,
  0x8002e3d6d86cfd569e0d57ffeff6d1f80667c27b047ffff6b4789aa39c8dd8b7fff444b98f59416c27c2,
  0x7fffd5888a0a7e5a981487ff5723abb164d2d3d4267fff2b43a0fd6f8faf5617fff5a6c17ad54ae6e291,
  0x80002823772c04e7c5b8f8000a4a31a24d20a138db7ffaf7f91b7a48db02deb800171d7950b20922f608,
  0x7ffedca12d28816d08afe7fff4f7896b32f3c52b647fffa83d31c9e1d46eaf77fff916a51bb031c243ee,
  0x7fff1641da01f9109dbfd8002639998d576bc029597fecce85af3aee65def968006c30fdc5effd969341,
  0x7fffef30921da853b662d80035a0a76235e5bc85537ff8f71d648e71808049c7ff5ca013aa61b925650c,
  0x7fffaf76302874ea275bd7ffff80eabfcf8e48d57880001f2435dc96ac67072800021f797b96a7bfcf33,
  0x7fb9f398444aa2d7beccb800058f4de24528cb2bd07ffdc3db736fe7f44b8fa80003273035d82edf6fae,
  0x7ffffab233c8c9472913f800073c49e024d3061b718000984af56712f764bfe8002cc0c81c4984015714,
  0x8000c1835da28f152456a7ffff4da8935e58b0bcdc7fffee798c2356d8acb298000263285d2ef9fdc5b6,
  0x8000eae12db53b868b59c800244cf60fe5c1d449db7ffff179c2b4bb8137e0580002028f8cc38a8f40cf,
  0x7fff798eede0e7a8c2f02800487291a8ef34e0fce87fea87d47120a7e317275800042d21a92dd88dbc2d,
  0x80011af6914fae16f527980041f87ccb4b18cb65dd7fff61e2fc1e83c9e454e8000954f6908bf2ee869e,
  0x7ffe026d4270cbf2308687fff32dcabfd484d002e48000244e21f8ca44dc6647ffec18aa3694f69362c3,
  0x80009fbd0d70fe9dd0f13800620da0b6d1b16ce2987fffcda145afbe953c16a800038600613f0c3a636b,
  0x800038a28a144d09993658001a16c34b1e831f38a57ffe4f9bb0ac76dc5734d801eda4701c75e957fcbf,
  0x80001a268431ce334b2a9800024a4588f21c5a0f8680009d1b98549b853cc068000996bf5283b745b10e,
  0x7f831d9715bcdd5c461f77ffffbc113bdf6b4581697fffe3c6e6359d48f99c78000201bd5308132db22e,
  0x80002ebc4f6b718e059298000d0f4c8ad6752cf05c7fffcff8ea867a8dff1b07fff3885525ee511d9d85,
  0x7ffff7a5cdb3d55436ee580000fc13a2fff60f017780005b3b9c715f4c64e1c7ffffbbbd74b32186ee32,
  0x80002f2ff3c60041f7cd5800023de484a9d8a82a397ffdb5235f1cda64db9e1800022b6bdea67ec73fcf,
  0x80009452825db4627f0087fff4ed71dd3582d2fdcd7ff25c4d90285ac1b26e88001cb9584fbc7821b376,
  0x7fff19ce9dcded7b9145d80009e9c715bc226b78e47ffdd27a94e77dc2c0d1e80004733e2936ee8e3903,
  0x7ff3be77ad2db5a2c33c87ffed2bb1446801ac17627fff18ef7ab96a8ddd138800039993c80e3284f74f,
  0x7fffbebd012b8593dcb037ffe3668b5105f2779ae8800309858c4c855a0ff258000dcaae40133a78431e,
  0x8000199f45d8d6f58fe287fffb6962709a2aad45c6800a63f47e954f78fac887fff1292a2f85be78ec95,
  0x80006c1cdb7929fcc56a08001606a7cfb195678b497fffd886feb2d96f1e9707ffff6d7aab9d261adf4b,
  0x7fffac4d3ce4e4b609c707f35c83a1d536b2d262ce7ffffa27120538203201a800095501ab052045addb,
  0x8000e6aed28ce5a77525b80009b807c3417bbc597680002b87689589910ed59800170a6a2cf957eafe30,
  0x800303750d1f6b121f3e48000f5d66365ac7890c238000b5dc089c16e0ee61c80005cd764f2632479958,
  0x7ffe7321f28d4139df716800112cd292ed30c3895b8000cef55bfd5ea58509f8004b92c580ca7a009958,
  0x7ffe77c6dce3004037c3f7ffd5eae667ea819d95547fff1cbdde23eb20970c48001f8b624e2be8bb88b4,
  0x8002f628966255bdd1dff7fffb559e6dcfd4b437397fff6b3cd82e36746ef3e8000e402f3674c79a42dc,
  0x800002adddebff244107e80011efc565e4d93cb2b28000ed76edd31b14227e180000c3d04bb61b9a34be,
  0x7ffff9d8e4fccb76644017fffe777d91ca531a0c067fffa4ad0d464706a2acf7ffff9e26ef161e78b13e,
  0x800090740d0fdb14049dd8000006c76c4367ff2de77fffc421ee0ddc864e1e77fe82677320459b8bcf9a,
  0x7fffda95f86608d52a29680010b7fefd00e2fbbe697ffffb197baca87b507f78000de08d0385901a4887,
  0x80013e8d2d37bcc6ddf6080011096b54811a68bc62800066ba1167b46bb4d447ea9b48776839a7ce0e21,
  0x80011712dc6ae5c4c1e977fffcf5aa2183b471982c7fbb19040bb483d14023a80009d3d95b3ad2ba1ec3,
  0x7fff204ec74fe99ddf9177ffe4058e6001a8c52c967fffddfe34889d66985b67ffda20e20eabe4020e21,
  0x7fffec049af55e08fcd968000ad4713650cda5d56a8000f2242872c48629f807ffee80524c5545bcd9c8,
  0x8000e421367e3debbfe787ff9716403ab96209807c7ffce5ac0dd31ae8425f27fffbbe55007ce7baf4d6,
  0x80000cb3b2550c1455ed37fffcc56e2ac70e86ddae8000ef3cf7d20ccb4d4067ffdfd016f83ae67c9a16,
  0x7fffcf131d7637b3bce0f80001a1af402f634b4bd67fff383ab76e50443f3627ffc4b4260ab402675df8,
  0x803e166aacfb8fafda6ac7ffd73bd7764730b59243800003efc6d0f0d60fe887fffeb8badc2fc36c094c,
  0x7ffff9b1446abbabd585a7fffd56c3d772fd358a2b80001197e0180bae3aea1800081f12168a9d26b322,
  0x7ffed50279274115eaf8e8000193977c550c44aef87e7980f2f32a20c690af17fff4a85219b463952e88,
  0x7ffe7c73c8ecdb893ec9b80011df63aca97e58e54880009b3b14d311fbf5a647fb3b2b9e17d887deb9b3,
  0x80003dbef357dcb99ed7e8002714ffbf0e554cda707fffb92bffceed8efb4cb8001d6f61f34e3c2c094e,
  0x800110260730764d5504f800045316b2f6ed8c6395800060a5b95998706d3c67fff80272147f7ad20f55,
  0x800084ebd28ae89ad691f7ff964b8bcdb60940574b7ffe0689516a60f280ed28000bcf5597329454f86b,
  0x8000dfdd2d808bdd671d380005f1c47fedbe675d077ffff0d1b8f303f501544800231452c2ea06a4cdb1,
  0x7ffffd7dfa0f3e7c7147d800009ec2a92f2ead62f67ffffa23faeabb9cb1aa780000382e5c463527e940,
  0x7fffeff34df3a3b103aa37ffffca9c0f9a8f2824e17fff9800e776c3f05723e8000372b0a34419e56532,
  0x7ffbdc6ee3e86efa369ec8000267062161cd6dc67c8037cb934c10b5bb4793c7fffeeb41567216fd9a1e,
  0x80010b6eba741ed4ffc2c7fff84655b8e09976156d7e179c752adadb2481a557ffffc0b17e08a377b26f,
  0x7ffec46e88e0e3d4ab9ee80009ae7b926429aa04217fb482e6e231801061c3e7ffe963504f5b9845d5f3,
  0x800014247ded109da8ec67fff48de83589ce5e2556800256b7550a57ba69cb0800053be4ca1559c88568,
  0x7fffd302d1aed734c101680019131c26e168d9f72b7fff6a324769cb1782c037ffff56395b59d39e804c,
  0x800019d66ce6233febb6e800098d1b352d429268a57fffba4a28232185b8d5b800794d0adb7ab961f430,
  0x80002e31df7885fe9e7ca7fffb563f84571fe05bfd8000198c4904ee2ac1fc87fff3e14acc97c19f02bd,
  0x80001ff6e6f64d7196f2c80037c1c5cede31c46f227ffe04ffe0654bac4efd47fffb0554781a77fef317,
  0x7ffff6ec450baa0c7d62380005dcb52696dbfaf9f97fff90efd4a8c1a077e01800056344899b23ec8db1,
  0x80038ae163a5e0109a12a80000a019ecdf61114e557fffffca1bf143c88af4e7fff979936ff9378c7f27,
  0x7fff571cc55f15f4feb9f7fff0d90cbaea23b024d77ffffdc49c5a0094017dd7e2319870067eb596732d,
  0x8001244ac146bcefe81ad7fff7f506775a051f7fb07ffec212918ca1bb4f3308048b1d838bcdc72498ed,
  0x80001975952590e4329ed8000999a17d051edfd4027fff614dd3f2cc059a83e80001a3b3e26070b2b233,
  0x7fff65fe5b7e4d381b2507ffc0aca3b11fb778e9da7fff0f160415460f6212e7fffc1bfd5426e760c2ea,
  0x80003258463d02f21c52b7fffe1312abfac59a17db7fffeb0bfc4b91463e22d800057fc1a8c99364dbce,
  0x7fffecc7aa297f82313277fffd452cacb10e1c347b80005b89937b6d7ed52707ffff048242000f9b37e8,
  0x7fffc481209b5fcc714e67fffd6020faac8efa3dc5800237dbeb88de9e90a2d800012f25688090c1e777,
  0x80020a4c6ffb2a7824491800016a609af01d58cd5e7fd779b7b20b2652b3d8d800057d9468f63f3e693f,
  0x80004ea5de942dbb521127e91d21d08b23050d02b07ffffb5d6b5aadf316ca680004e2337c417f238634,
  0x7fff735d720d0b25721b2800226e1c9c596068da828000f52e7b69cb360100f7ffe76ef3fb2e32d82b6c,
  0x800069c2642581f2495647fffa8d0ad2d6c43e3fde7fff0171101f95b5549dd80016d6af5cf69b0fbc64,
  0x7ffd9b730a85b2d300ca07ffff0313eeb31d0f61a77fffa712f190c0b592eee8000c8a2b7730b31d39dc,
  0x7fffe215d7e3a663902de80003aab2f1e96a16673c7fff3ad9d2c5e1f0add5d7ffa3277e4ec4be89b7c9,
  0x7fffea838d3fe416f68d18000109ae8bd7dbff09737ffcb00c5dfecb2f116be7fffed23de2fbf7c3b47c,
  0x7fff9b76ae78780fa2f88800008442832c0ea60264800030ecec2f59155f0837fffdd8ac2029ff6179c3,
  0x8001a343b5cd7473b3dc08000d2863b425d6aacfc67fffe93a793d7a348fcc17ffff8eb955a2a1d3c13a,
  0x7eb7adf6b4ca7671bc9fc7fffda8de6dab7561519c8045f4238339c5ea810117fffe0068d813474a1ef6,
  0x7fffc7f6a8ff20417eaa27ffdf1678ff10508ca7067fffc7643470a01877ac9800125306dfc8347ccd4f,
  0x8000de8bf4b6e7981534e80001d9d3eb855a27a1857fffcdeba41355a1b04717ffcc117de7bf14580e61,
  0x7ffec76d7d5b474e97e938000e94fe22cc1480e2ff7fffcf94828cb076fdcba80003f552ca241ba44c0b,
  0x8000932e50431d25c22077ffd94906c03d1f818ec07ffed5801c7cf06f2d7817ff60087484f013048024,
  0x80001026fd563bc2e327b8000c461bad5e794abf367ffff790b1b6f8b2061907ffff1ecf080667df47da,
  0x80003dd094a6b5f1ea21780000795c95970a26eb347fffe30e3d6859d2c6fcd80001b8e2865ab6731bbe,
  0x80000638922bae727a3917fff890b80adf70624f9b7ffd4c87f89e9318b9889804a412530ffaf5fe035e,
  0x7e5be1a1509c8db1cf4c18000172af50db4699fdb2800026f110acf256a75898001150b9c495678be621,
  0x800197406740f8e87ed5a80008a492a6f9f8fccaa87ffe2f1b8a188485fe75780004dd82d0877aa832d7,
  0x8000a068635e002b787658001183dd46cdc2cf649f800011ac6ccdc6addf195800120c60f37ca94342fc,
  0x80013761600ad164e590c8004c45a8088670f62e8a7fff8e8776a737fa883097ffffac4bc1db4262eb1a,
  0x800025f37ddcffe42af187fffeb3d6de179503fe087fffb91717a87a9db97ca7fff56cbcd60d5d567629,
  0x7fff1dbd14658dcd9e0397ffff2bb84a837cccdee97ffff43700e39e16c802f7fff8898ca3df04196b09,
  0x800017d1bf3c762cd1f2d7ffff11f5cff8c47fa42680001b19a2e1049fb4175800017e611bfdbcfa8a8b,
  0x80001772cb2380d90c28d80000ca5b66a7d1e0943e800013fb2de283eb4c6f27fffb85476040e16c59f9,
  0x8001bb2207b6a433281787e48b0c7acf401ee441c37f8c85c1be99349dba2f77fffca5f12face356da25,
  0x7fff96e1bb6666a51c9f77fffeeee7e0f987a9eca57ffe244373444562a1fa67ffebdd5d5d3f56c917f7,
  0x800071b23de0e060fdec57fff88245abe694b4ac018000b79c82e86a9bef13e7ffffad071a18b824a902,
  0x7fffb88a48cd5bc5f776f80000c90292e58642fc7680017e2992a9d741111668004a8372e56b6f13964b,
  0x7fffffb31f0d5d727a6b0800006bc93bf406a0e40d7fffea936ed0a4f2d5ab37ffffb177f8c1dc96866a,
  0x7ffff3c627682201229de80000e7abc406ebf7a81b7ffffc22a3b46d4760025800000f07c5989bbfcd99,
  0x8001fab94ccafba4bd2c5800044824c228429811997fffaa6d2e99e996345747fffd5139b1260b260ee1,
  0x7fffea968150c0cd40c5d80002b93f4ff420cf1ac68040f68a9c590215ea1cc7fffe64e82218744c7593,
  0x7ffec20fc4f62b6ea23a480006508cdfc7f5e9fcc280017219e575a2419dd937f07e928d7a8a147f195d,
  0x7ffe7f7e379e5fadc48c27ffe9ddfdf34b6080e476800102e5595a3f40301e88001f5d56375251c3aaef,
  0x8004a61e0b84e86af09db8000f1044c5502d1cbabb7ffefb6340da32bc471768017cf21eba11506247ff,
  0x8000b8033080d21f45b66800039dac02464a38e5c77fff61f97052e0828f7937ffc56311005b798154ae,
  0x7ffd37233363d74b9391c800196e29b66ed5580c2380005d81f69559ecd2acf7fff32866a7d5bcbc033b,
  0x7fffc1dc3d94a534e93fc7fff9ea8633cb42be8bdc800071ff747b821b33fe07fff68fc3f52f0c85adee,
  0x80001105e74b2f4e199198000334395477a167b57d800016d1f8563f99f12e77fff95992c93bf3e36263,
  0x7fff67c7b49a95c2cbaa17ffec208969e488f11cc27fb0ab6cc29d8178e8891800132f36066226e5634f,
  0x8006eff014c683dd3ce367fff72f93186cad4c58447ffa89dca6961975d4d6e8000b9dd83868654e6dfd,
  0x7ff66eedbfb97f37edd4b7ffe0503161ffda2ac1128000b9a65005898684c697ffb056c43597fd6aa322,
  0x7ffeb6c3b5ded2d5721367fff611458ada9748960b7ffe70d70e927259d24ed8003265420931760e432e,
  0x800188e030defb950cded7fffa87928d3f8f6d363f7fff0b259a24070df77ad80007db2c19769c87b36a,
  0x7fff5454a59a83050064c80003e037a30e935d760280014fe6d081ab99821118002fdc0efcd9b39ac531,
  0x8000825c0af26ea2c149980017af29d14e4cc1098b80000fe1f810c675590e6800191fac9a4e26213c78,
  0x7fffe54715babf9c0c80b80008c6cfa137efdfd9687ed822cdb232b2366b50280000e55531f41644243b,
  0x8002532dd493df5411182800940101a6565cc30b8280013c663b0088dd1a6e87ffde07d0361f92f7b83d,
  0x7ffa697d5059f8cd63c9a7ffa1ed2ad7d2a685acfd800114c2b32888b8a2bb67fff8a68cadfb02b06693,
  0x80010e11dd10dcb50b9e97fff57aef76353a9a030c7ffead0ad71875ca476fa80027e3beaac2be9a93ff,
  0x7ffe63e9c1b9bece40d517ffd029a535974d70d6bd80029bddfc118905312a680005989b9ffa4ba44571,
  0x80000438dcb1e5e44ea747ffede1b33a32e05eaa767fff61e3949e9d1036f2e7ffff650e92e8f6d45487,
  0x7ffeddfd4be1563e3c7958000bdf8830c688ebd7757fffd32edf60099b8ef34800024053439785197d20,
  0x7fff7740fd8f422ef008c80008b0589ba2c212f4ec7fee811f1cf6708eb737b7ff70c0ba524a5f44a822,
  0x7fffe9ff2ec5db25db06b80008561273301a30f69d80002d7c1f8d5ed7240c88000955a65d9c4cc5d315,
  0x80021dc4654e814ca46a78005d8fccacfcefa822027fffc3e0d8ce78290726b800049ecf5ca55806e653,
  0x8030c5669555b7ce5e9dc80005c88fd4ba493268f87ffba6ad832d7794ddac97fe98f35b8c4bd6c482d3,
  0x7fff914f62f15215c36b180005ebd8cf16a9a80b128001d3870a2d3b9cfca4c8010955c55554cf9cb736,
  0x8000013be8365ba7e7f8e7fffe35d035dfd392853a7fffe97accfd151a887ab7fff77c4f5e2ca198a6d6,
  0x7fff76c6e0520bb3909a97fb450ae15aec73526f047fffb306156f472ceed657ffee570e603da0427218,
  0x7fffdf2c6e24cc003244c7fffffb5966382909199e80019afd02e9f5bb02f5d80002c9dd4c6827689e92,
  0x7ff81067801e1f1b9a6737fffea05b18fa403216e580000a7799a29b2506b6380004597057e1ea08fd17,
  0x7ff790f95f719274dd4838007922559e2e816f86708008f944a8bb74ab993968008167d750bec2f77ff6,
  0x8000834a129705c18742d800180f69b3916110af607ffc8ce781ce48115a4cc7ffe5cdeeb35eedcfd1af,
  0x7fff1bc422d2521a00f737fff3072592edd41675327ffeeedc2fd4ab204518a800040cfe00699944c090,
  0x81109ce35f2c164ff5a1b7fffdfe37798d00c86f797fff576fe5e1e8a7f1287800083c178a22b62e6851,
  0x7ff0594c4c7185b5c3a54801a5a4908ae3e1d815888004ae4ed9be6ebb6f97e800c53fe2344ed08816ae,
  0x8002958d590baa5a36ff97feb7e92fcd0920bfa52d801ac14431709f6b1cba28005b24e668b62cec6b3a,
  0x7fffeb8c3960f6f744004800160e43a5f92530f56080004e290283c59b63e72800030d543c5ada061e71,
  0x7ffd7f25e7fa40d2a21777ffe6f4d96a288bef0f9480002ef967e2e1f6d57ee80005c009f76a5e53b4fb,
  0x7ffe510a12c62037198057ffed289f33be8eb5e5e07ffdb963aab7b4c3a60c87fffcd515451c6943fe76,
  0x8274dd0302a3b978e10968002f12686b5526550f6e7fffcf694f8c1f6410fe17fffc1fef80e480e46cad,
  0x80174d53a50ef549a7c1f7febe649cb434be515d9d7ffe2c9933a1918deb6df80134f681ff0c6239a19e,
  0x8000bf50cab5330a9224a800146285ca610c110bad800d2f191d150479683ae7ffb8b9b5162c0c868896,
  0x7fffba01d00df9f3af8807fffdd3556be197c4f219800199821f3f3fdd77ec880010e8bda7f79aadfb39,
  0x80039b1372d2f3a55638080030c385da04263d82707fff443b60ef126ad0d5580010a2440c50913f80fb,
  0x8002562feb4fd3cd572458002f2b421ebc0764c3c580016535d1cd4ff409142800399be19818167391b0,
  0x800765d99f93ca8a62fa58132d5c003f2a043ffbd67ffd9b2172325f951c3e68002820aaa3e7bd5407c4,
  0x7fe00534a42e1f20716f67fe4aa098853928ac3a3e80064da7db5fd650ecbaf7ff8375fac6460d360c25,
  0x7fff27466c48197d2cf3980025f90b4e5874effcfb8002da443afe16c6080db7ffed8221b53b10adafba,
  0x8003288cda08beed841667fffbfa58deccd4d0efa77ffce18a2f3a3c9f768568002a771eccff4a6b1bff,
  0x7fff6c784c2a77a03069a7fff14ca004f567e8dabb7ffcfc0cff30726e0aec07ff6db46991a8de920a76,
  0x7fff95f32688a0f6c983e8000a055786be392ce4467ffdd6b35f36cdd9447bf800249dd98e532e23db7c,
  0x801329353067e172ab89d800336208ed3ea6a428777ffb7f0eca0fe8aa40e8f817645af3f511beb52410,
  0x8002b78fd05df56e030868002c308fca5532b61cc77ffe44f400e1b393c2e397ff3066d772169d0b5bab,
  0x7ffd58d267f8916f32a637fffa119c703622303dbb7ffe2b356af35e5c232fc7ffd4c8347fdc1accc940,
  0x8003094437f8fc2e144067fff17461b69551c267cb7ffceae62ebea077285ef7fff388048dc68a1ab6ad,
  0x7ffdf52b7b5917d59a9f48000ffd61c677531b30c58000db68ad1725a71471a7ffe69f21c68696fe462b,
  0x800144ce062161702f4597fac089bf779a1ab1f6847f7d748e6897667bdd1eb7ffcb1a41641946ddc577,
  0x7fffaf17cbb9d44e31b5680002cc2af5021b560ded80000be359f27cc5878bb7ffdc61310e6981dd4f59,
  0x7ffe87a2459544fa4e79e8000887704992a5fa3cf880000f3a29f1f2a4b913f7fff9786cbe8a1ecb22f8,
  0x7ffaee199e2e2ed91c5e47ff88346d937fb76aa14880047945c6d8c5465c80e7ffe53c5d9721c255efa4,
  0x7ff9c9d383f6b3f4886b37ff438aecc874722e0a277ff9939bf368ccf3dab9e7ff580eb69f9a98cc3501,
  0x80042ed00038415ff56da8005a013f94b0deb977e57f9eb1af5c96d4254f3da8006133841f13878a5803,
  0x7ffec39a393f19227bba07ffeb45ca23f42df398767ffd8f85b7a094a2435067ffe7a87858e4c9053043,
  0x7fff94ea73d59174b1a93800134e22c8c267a09c557fff2b9fad1bbed2547b3800042859f09df46a686d,
  0x8003ac2cb7ca24bfdffcf800acd12032d563f8d624800e5f2abe5c17198588b7ffc673c1aeaee16397c9,
  0x7ffade8375ed35c94608d800bcb4f8aeef8728e3628004964a353808347ab74800e330be1063d18bdc89,
  0x80005b039cd72798ba0bd7fff379ed09e758a234f97ffacb20c216cf3a1332b81a49c9a52edc42f78c72,
  0x800014c86e4387dfa32b3800013711ad4c6908fd097fff3ad2333c7e37118338000986107546dd9e10f6,
  0x800bfaba18aec8b7675618000e0e043ba070eaf18d8001b2be3887e5d06af967fff6a3b836c6ca66b26d,
  0x8010167e07797c2f6a44e7ff5884111de23403650e800e124ceaa61aecd7efa7ff51219d21ee0eed4ed4,
  0x7fff68fe078bfeb02267e81b23f3737056412063fc800dcf8e033f05bcaec2d800b9ba74a0842786322e,
  0x800088affcb6b3f0e975c7fffd519d09bc26b414eb800104499a7e02598afda80016303b102de6180d22,
  0x800846645798f00bd8f7f8000f1f9a305c6dfcbf6480002e1c4619a71122ca57fffabe5bb20cf2feaf27,
  0x7fecb7bc67c6996b2e9407ff80b269c2b015f00b64801348e440a915d9f1fa880132ca8739a546dcede8,
  0x8066c0eb615a003f396f97ff58f19788b7fa89e13f7fef8f3075703c0483a128009cb63bb3fd4a565d90,
  0x7fe18dc37a28804b6ab48800982d292f456984e4437ff8b208f1bb6ab626284800280106dd0c4d1e0da8,
  0x80004f62b4b147e716ee08002493b98337cce5a581801017fb3da5f43bce8407ff16a94cfe2a811d0854,
  0x7fffef721d7accb23a00c7ffffe3a241333fc054bd80006796af444b65434147fffef9864c7cd19b7bc9,
  0x801c3323ad0f233bc9dd47fffefee8fdb9055172da7fffe97d2a3454095497080001c979a8c55456cd53,
  0x8006fdc4c74c9dbcaaddb8001e54308946974b6e417ffba54bec439a887a6e47ffdb6f14135807109130,
  0x7fffeb3725e83dbc615d980008cbdd1f26042252447fe2376122969b55066c57fffe717c87a7b63728eb,
  0x80001780c27366d912aa38001ec3c7bfcb3f94756f80002f3d8f82eef73cd347fffd58728ff27a207a55,
  0x8002b364be22f7de926f18040ce0094110a1d779af7ffff152167dead6c80268000866efe01139b160ec,
  0x800120287dcae1a919a6e801c9cf3c37c1c3b1879f7fe966013e6ef6b5232d47ffd077862ed88e185b87,
  0x800005c62bc3f8c043c5e800007e33ab5ce11f74067ffff1b1c38604fa3de86800041e0247fe0f4a9daa,
  0x8000a77d213eaeb200ca17ffbd2e9bed0b290b6d8e80000d7c5fcf0e05de3d180004f63eea581b3892ce,
  0x7ffac3ac0a8b0a59395be8000d35bba29f71a24a4a80216893056c36576a809803dc2686ca4acece0283,
  0x7ffb9714e698a4c9312858000b81bb66cf555152748000347b4fbaf2ac7bd2a7ff9411a3da2d606f0e21,
  0x800013e0828c4889a74b67fffe2e7b2ec9e546ba47800028ed1fdf5ccaa622e80000de51103d8ac5aaf8,
  0x800668d5e28b9e928f42b7fffc5fc3c18719784270807e191a99acb36f0b79780000598fa38da1abea43,
  0x7fff179336a6cf5ce15077ffff70b17ec58c45e7b8800004d3bb59a7b3f808c800209fb6b1753fb7d4bc,
  0x7ffff26ac9b520024525b80000c84fd332fdd165097ffffdbdd67591917de8c7fffc6c980619375622d7,
  0x8003365296a7c309816f2804adbde7ddded7c500c1804f6433f13b5681f73597ffff65e40a73833b3f0e,
  0x7ffff90d5c200f3f4ae8b80000d3eece1910a9ad2480005a2a8d156e4341506800060e39e86b2d88398b,
  0x7fff8ea3a4a9c843e76fe7fffd877424da31d45ed88000219341c026fe686778000314493d3e84da1ea1,
  0x80000a7e09b8950828ef77fff885b30a1156dfe5337ffe58df663db27af5e12806afefe0d4476b8c055a,
  0x7ffffcc19eacbaab26dd57fffcd4ffcf9ba17007c67ffffd93406ad8227b84a7ffff9a7fdfce4e012641,
  0x80007263bb5fd84abcc0280161b37f7761d3a2335a8001ab8f888db5f8a797680000502eda27ce41b70c,
  0x8000383d4c33918fd6cc4800074e85a96ba50837c77fffd243abb1eef06c3ef7ffffe1fea442e8f3855b,
  0x8060fe151db28895376067fffdf149cef83d89992180001719f2afc17c1484d7ffe847493c876dc6ce62,
  0x8002dd29ea116555a23948000d65ecdbd4c3823a087fff79f4ec25f8a4a7e597fff0c43f1a3a5e069044,
  0x80b81fc602f16d2c94931800011825314d398727548002cb18934137d282dc07fff8e04f3aa1f2304591,
  0x7ffd7662786c2a0829cd88001102beadb51a902c03800036fc7764a62259ab7800366ec9e6283336d696,
  0x8004aa96da4015ce59a0580ae995b62b99fe2df6978000450b4da4dc3690414800096ee890a5f28a898d,
  0x8001f6819f82365247a3280011ccf9226697699a557fffbfae1226de8e44b6e80009ba5cec62b45377d5,
  0x7ffd4b32e1d06a1082e348002faf88beb31941fafe7fffdfd8927efdb09a421801bf682c611c4621e99c,
  0x800369f763053d6ed13338004b0c9716af442476798079fa5e275610a241e757fff1d25c330643aa2beb,
  0x7fff8508e90a81b205a017fffc4e6e21eb4e619e69804994d2b3701d133af7e7fffe3cda2dc742006e71,
  0x8061b01d3ca8fa7e1cb3e7ffb1d28870e0bf1298ec808f45385650655900126]

/-- Decoded `58 × 58` partial Gram matrix for slice `0`. -/
def gramSlice0 : List (List ℤ) := decodeSymGram gramSlice0Raw

/-- Decoded `58 × 58` partial Gram matrix for slice `1`. -/
def gramSlice1 : List (List ℤ) := decodeSymGram gramSlice1Raw

/-- Decoded `58 × 58` partial Gram matrix for slice `2`. -/
def gramSlice2 : List (List ℤ) := decodeSymGram gramSlice2Raw

/-- Decoded `58 × 58` partial Gram matrix for slice `3`. -/
def gramSlice3 : List (List ℤ) := decodeSymGram gramSlice3Raw

/-- Decoded `58 × 58` partial Gram matrix for slice `4`. -/
def gramSlice4 : List (List ℤ) := decodeSymGram gramSlice4Raw

/-- Decoded full `58 × 58` integer Gram matrix for `h1Hat`. -/
def gramTotal : List (List ℤ) := decodeSymGram gramTotalRaw

/-- Fast primitive boolean equality on `ℤ` without `DecidableEq` overhead. -/
def intBeq : ℤ → ℤ → Bool
  | Int.ofNat a, Int.ofNat b => Nat.beq a b
  | Int.negSucc a, Int.negSucc b => Nat.beq a b
  | _, _ => false

private lemma intBeq_eq {x y : ℤ} : intBeq x y = true ↔ x = y := by
  cases x <;> cases y <;> simp [intBeq, Nat.beq_eq]

/-- Fast boolean equality on `List ℤ`. -/
def listIntBeq : List ℤ → List ℤ → Bool
  | [], [] => true
  | x :: xs, y :: ys => intBeq x y && listIntBeq xs ys
  | _, _ => false

private lemma listIntBeq_eq : ∀ {xs ys : List ℤ}, listIntBeq xs ys = true ↔ xs = ys
  | [], [] => by simp [listIntBeq]
  | [], _ :: _ => by simp [listIntBeq]
  | _ :: _, [] => by simp [listIntBeq]
  | x :: xs, y :: ys => by simp [listIntBeq, intBeq_eq, listIntBeq_eq]

/-- Fast boolean equality on `List (List ℤ)`. -/
def matIntBeq : List (List ℤ) → List (List ℤ) → Bool
  | [], [] => true
  | r :: rs, s :: ss => listIntBeq r s && matIntBeq rs ss
  | _, _ => false

private lemma matIntBeq_eq : ∀ {A B : List (List ℤ)}, matIntBeq A B = true ↔ A = B
  | [], [] => by simp [matIntBeq]
  | [], _ :: _ => by simp [matIntBeq]
  | _ :: _, [] => by simp [matIntBeq]
  | r :: rs, s :: ss => by simp [matIntBeq, listIntBeq_eq, matIntBeq_eq]

/-- Checks that `evalWeightedGram` on `(cs, vs)` equals `target`. -/
def checkGramSlice (cs : List ℤ) (vs target : List (List ℤ)) : Bool :=
  match evalWeightedGram base96 58 1048576 bias58 cs vs with
  | none => false
  | some rows => matIntBeq rows target

/-- Entrywise integer row addition for `List ℤ`. -/
def addRowInt : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => forceInt (Int.add x y) fun z ↦ z :: addRowInt xs ys

/-- Entrywise integer matrix addition for `List (List ℤ)`. -/
def addMatInt : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], Bs => Bs
  | As, [] => As
  | r :: rs, s :: ss => withListInt (addRowInt r s) fun u ↦ u :: addMatInt rs ss

/-- Checks `n` entries of two integer rows against the scaled residual bound. -/
def checkRowDiff : ℕ → List ℤ → List ℤ → ℤ → ℤ → ℕ → Bool
  | 0, _, _, _, _, _ => true
  | n + 1, h :: hs, l :: ls, cH, cL, bnd =>
      Nat.ble (Int.sub (Int.mul h cH) (Int.mul l cL)).natAbs bnd &&
        checkRowDiff n hs ls cH cL bnd
  | _ + 1, _, _, _, _, _ => false

/-- Checks `m × n` entries of two integer matrices against the scaled residual bound. -/
def checkRowsDiff : ℕ → ℕ → List (List ℤ) → List (List ℤ) → ℤ → ℤ → ℕ → Bool
  | 0, _, _, _, _, _, _ => true
  | m + 1, n, hr :: hrs, lr :: lrs, cH, cL, bnd =>
      checkRowDiff n hr lr cH cL bnd && checkRowsDiff m n hrs lrs cH cL bnd
  | _ + 1, _, _, _, _, _, _ => false

/-- Compares two `Option` integer Gram matrices entrywise against the scaled residual bound. -/
def checkGramDiffAux (oH oL : Option (List (List ℤ))) : Bool :=
  forceInt 121733 fun cH ↦
  forceInt 3556232921088000000 fun cL ↦
  forceNat 285044355550348197604220 fun bnd ↦
  match oH with
  | none => false
  | some hRows =>
      match oL with
      | none => false
      | some lRows => checkRowsDiff 58 58 hRows lRows cH cL bnd

/-- Kernel boolean certificate checking uniform residual bound between `gramTotal` and witness. -/
def checkGramWitDiff : Bool :=
  withMatInt gramTotal fun hRows ↦
    checkGramDiffAux (some hRows)
      (evalWeightedGram base96 58 1048576 bias58 witnessWeights (lPosCols ++ lNegCols))

theorem shapes_ok :
    oneBodyAngleTableArr.size = 58 ∧ leafAngleTableArr.size = 261 ∧
      ∀ row ∈ oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList,
        row.size = 57 ∧ ∀ k ∈ row.toList, k < 8192 := by
  obtain ⟨hleaf, hone, hrows, _⟩ := table_shapes_and_bounds
  refine ⟨hone, hleaf, fun row hmem ↦ ?_⟩
  have hmem' : row ∈ leafAngleTableArr.toList ++ oneBodyAngleTableArr.toList := by
    rcases List.mem_append.mp hmem with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h
  exact hrows row hmem'

/-- Kernel boolean check for scalar totals and witness dimensions. -/
def checkScalarTotals : Bool :=
  intBeq twoBodyTotalInt 6235149250440 &&
    intBeq sumAbsC 4837203501784 &&
    intBeq sumSqPos 41807165163 &&
    Nat.beq lPosCols.length 22 &&
    Nat.beq lNegCols.length 36 &&
    (lPosCols ++ lNegCols).all fun col ↦ Nat.beq col.length 58

private theorem scalar_totals_ok_bool : checkScalarTotals = true := by
  decide +kernel

theorem scalar_totals_ok :
    twoBodyTotalInt = 6235149250440 ∧ sumAbsC = 4837203501784 ∧ sumSqPos = 41807165163 ∧
      lPosCols.length = 22 ∧ lNegCols.length = 36 ∧
      ∀ col ∈ lPosCols ++ lNegCols, col.length = 58 := by
  have h := scalar_totals_ok_bool
  simpa only [checkScalarTotals, Bool.and_eq_true, List.all_eq_true, intBeq_eq, Nat.beq_eq,
    and_assoc] using h

/-- Kernel boolean check that every Givens-leaf interval in `rows` has midpoint radius `≤ 77`. -/
def checkRadiiOn (rows : List (Array ℕ)) : Bool :=
  rows.all fun row ↦
    (givensLeafIv row.toList).all fun iv ↦
      decide (iv.2 - (iv.1 + iv.2) / 2 ≤ 77 ∧ (iv.1 + iv.2) / 2 - iv.1 ≤ 77)

private theorem radii_ok_bool0 : checkRadiiOn oneBodyAngleTableArr.toList = true := by
  decide +kernel

private theorem radii_ok_bool1 :
    checkRadiiOn (leafAngleTableArr.toList.take 131) = true := by
  decide +kernel

private theorem radii_ok_bool2 :
    checkRadiiOn (leafAngleTableArr.toList.drop 131) = true := by
  decide +kernel

theorem radii_ok :
    ∀ row ∈ oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList,
      ∀ iv ∈ givensLeafIv row.toList,
        iv.2 - (iv.1 + iv.2) / 2 ≤ 77 ∧ (iv.1 + iv.2) / 2 - iv.1 ≤ 77 := by
  have h0 := radii_ok_bool0
  have h1 := radii_ok_bool1
  have h2 := radii_ok_bool2
  have hall : checkRadiiOn
      (oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList) = true := by
    rw [← List.take_append_drop 131 leafAngleTableArr.toList]
    simp only [checkRadiiOn, List.all_append, Bool.and_eq_true] at h0 h1 h2 ⊢
    exact ⟨h0, h1, h2⟩
  simpa only [checkRadiiOn, List.all_eq_true, decide_eq_true_eq] using hall

private theorem gram_slice0_ok :
    checkGramSlice coeffsSlice0 midVecsSlice0 gramSlice0 = true := by
  decide +kernel

private theorem gram_slice1_ok :
    checkGramSlice coeffsSlice1 midVecsSlice1 gramSlice1 = true := by
  decide +kernel

private theorem gram_slice2_ok :
    checkGramSlice coeffsSlice2 midVecsSlice2 gramSlice2 = true := by
  decide +kernel

private theorem gram_slice3_ok :
    checkGramSlice coeffsSlice3 midVecsSlice3 gramSlice3 = true := by
  decide +kernel

private theorem gram_slice4_ok :
    checkGramSlice coeffsSlice4 midVecsSlice4 gramSlice4 = true := by
  decide +kernel

private theorem gram_total_ok :
    matIntBeq
      (addMatInt gramSlice0
        (addMatInt gramSlice1
          (addMatInt gramSlice2 (addMatInt gramSlice3 gramSlice4))))
      gramTotal = true := by
  decide +kernel

private theorem gram_wit_diff_ok : checkGramWitDiff = true := by
  decide +kernel

-- Seal large data tables so downstream elaboration never unfolds literal arrays/lists.
private lemma list_split_66_65_65 {α : Type*} (L : List α) :
    L = L.take 66 ++ ((L.drop 66).take 65 ++ (((L.drop 131).take 65) ++ L.drop 196)) := by
  have h1 : L.drop 131 = (L.drop 66).drop 65 := by simp [List.drop_drop]
  have h2 : L.drop 196 = (L.drop 131).drop 65 := by simp [List.drop_drop]
  rw [h2, List.take_append_drop, h1, List.take_append_drop, List.take_append_drop]

private lemma allCoeffsList_eq_slices :
    allCoeffsList =
      coeffsSlice0 ++ (coeffsSlice1 ++ (coeffsSlice2 ++ (coeffsSlice3 ++ coeffsSlice4))) := by
  simp only [allCoeffsList, coeffsSlice0, coeffsSlice1, coeffsSlice2, coeffsSlice3,
    coeffsSlice4, withListInt_eq, withMatInt_eq]
  conv_lhs => rw [list_split_66_65_65 (List.range 261)]
  simp only [List.map_append]

private lemma midVecsList_eq_slices :
    midVecsList =
      midVecsSlice0 ++
        (midVecsSlice1 ++ (midVecsSlice2 ++ (midVecsSlice3 ++ midVecsSlice4))) := by
  dsimp only [midVecsList, midVecsSlice0, midVecsSlice1, midVecsSlice2, midVecsSlice3,
    midVecsSlice4]
  conv_lhs => rw [list_split_66_65_65 leafAngleTableArr.toList]
  simp only [List.map_append]

private lemma slice_lengths_eq :
    coeffsSlice0.length = midVecsSlice0.length ∧
      coeffsSlice1.length = midVecsSlice1.length ∧
      coeffsSlice2.length = midVecsSlice2.length ∧
      coeffsSlice3.length = midVecsSlice3.length := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [coeffsSlice0, midVecsSlice0, shapes_ok.1]
  · simp [coeffsSlice1, midVecsSlice1, shapes_ok.2.1]
  · simp [coeffsSlice2, midVecsSlice2, shapes_ok.2.1]
  · simp [coeffsSlice3, midVecsSlice3, shapes_ok.2.1]

attribute [local irreducible] leafAngleTableArr oneBodyAngleTableArr oneBodyWeightsArr
  fragmentWeightsArr innerWeightsArr lPosRaw lNegRaw lPosCols lNegCols gramSlice0Raw gramSlice1Raw
  gramSlice2Raw gramSlice3Raw gramSlice4Raw gramTotalRaw gramSlice0 gramSlice1 gramSlice2
  gramSlice3 gramSlice4 gramTotal

/-- Common rational unit $q / 7680^2 = \Lambda / (188416 \cdot 58982400)$ for integer weights. -/
noncomputable def uScale : ℝ := P450.coefficientUnit / 58982400

private lemma coefficientUnit_nonneg : 0 ≤ P450.coefficientUnit :=
  le_of_lt coefficientUnit_pos

private lemma uScale_eq : uScale = 121733 / 13891534848000000 := by
  unfold uScale P450.coefficientUnit
  norm_num

private lemma uScale_nonneg : 0 ≤ uScale := by
  rw [uScale_eq]
  norm_num

private lemma sum_fin_eq_map_range_sum {M : Type*} [AddCommMonoid M] :
    ∀ (n : ℕ) (f : ℕ → M), (∑ i : Fin n, f i.val) = ((List.range n).map f).sum
  | 0, _ => by simp
  | n + 1, f => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [sum_fin_eq_map_range_sum n f, List.range_succ, List.map_append, List.sum_append]
      simp

private lemma int_cast_list_sum :
    ∀ (xs : List ℤ), ((xs.sum : ℤ) : ℝ) = (xs.map fun x : ℤ ↦ (x : ℝ)).sum
  | [] => by simp
  | x :: xs => by
      rw [List.sum_cons, List.map_cons, List.sum_cons, Int.cast_add, int_cast_list_sum xs]

private lemma zipWith_sum_eq_sum_fin :
    ∀ (cs : List ℤ) (vs : List (List ℤ)) (g : ℤ → List ℤ → ℤ),
      cs.length = vs.length →
      (List.zipWith g cs vs).sum =
        ∑ j : Fin cs.length, g (cs.getD j.val 0) (vs.getD j.val [])
  | [], [], _, _ => by simp
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | c :: cs, v :: vs, g, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.length_cons, List.zipWith_cons_cons, List.sum_cons]
      rw [Fin.sum_univ_succ, zipWith_sum_eq_sum_fin cs vs g h]
      simp

private lemma map_sum_eq_sum_fin {α : Type*} (inh : α) :
    ∀ (xs : List α) (f : α → ℤ),
      (xs.map f).sum = ∑ j : Fin xs.length, f (xs.getD j.val inh)
  | [], _ => by simp
  | x :: xs, f => by
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rw [Fin.sum_univ_succ, map_sum_eq_sum_fin inh xs f]
      simp

private lemma sum_fin_add_eq {M : Type*} [AddCommMonoid M] (m : ℕ) :
    ∀ (n : ℕ) (F : ℕ → M),
      (∑ j : Fin (m + n), F j.val) =
        (∑ i : Fin m, F i.val) + ∑ k : Fin n, F (m + k.val)
  | 0, F => by simp
  | n + 1, F => by
      rw [Nat.add_succ, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [sum_fin_add_eq m n F, add_assoc]

private lemma sum_fin_cast {M : Type*} [AddCommMonoid M] {a b : ℕ} (h : a = b) (f : ℕ → M) :
    (∑ j : Fin a, f j.val) = ∑ j : Fin b, f j.val := by
  subst h
  rfl

private lemma getD_append_left {α : Type*} (xs ys : List α) (d : α) {i : ℕ}
    (hi : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  induction xs generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons _ xs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih (Nat.lt_of_succ_lt_succ hi)

private lemma getD_append_right {α : Type*} :
    ∀ (xs ys : List α) (d : α) (k : ℕ), (xs ++ ys).getD (xs.length + k) d = ys.getD k d
  | [], _, _, k => by simp
  | _ :: xs, ys, d, k => by
      rw [List.cons_append, List.length_cons, Nat.succ_add, List.getD_cons_succ]
      exact getD_append_right xs ys d k

private lemma array_getD_eq_toList_getD {α : Type*} (arr : Array α) (d : α) (i : ℕ) :
    arr.getD i d = arr.toList.getD i d := by
  by_cases hi : i < arr.size <;> simp [Array.getD, List.getD_eq_getElem?_getD, hi]

private lemma arr_getD_mem_toList {α : Type*} (arr : Array α) (d : α) {i : ℕ}
    (hi : i < arr.size) : arr.getD i d ∈ arr.toList := by
  rw [array_getD_eq_toList_getD]
  exact getD_mem_of_lt arr.toList d (by simpa using hi)

private lemma oneBodyIntList_getD {ℓ : ℕ} (hℓ : ℓ < 58) :
    oneBodyIntList.getD ℓ 0 = P450.fromOffset (oneBodyWeightsArr.getD ℓ (2 ^ 14)) := by
  have hlt : ℓ < oneBodyWeightsArr.toList.length := by simpa [oneBodyWeightsArr_size] using hℓ
  rw [oneBodyIntList, map_getD fastFromOffset (2 ^ 14) 0 _ ℓ hlt, fastFromOffset_eq,
    ← array_getD_eq_toList_getD]

private lemma fragIntMat_getD {r c : ℕ} (hr : r < 9) (hc : c < 14) :
    (fragIntMat.getD r []).getD c 0 =
      (((fragmentWeightsArr.getD r #[]).getD c 0 : ℕ) : ℤ) := by
  have hrLt : r < fragmentWeightsArr.toList.length := by simpa [fragmentWeightsArr_size] using hr
  have hsz : (fragmentWeightsArr.getD r #[]).size = 14 := fragmentWeightsArr_row_size ⟨r, hr⟩
  have hcLt : c < (fragmentWeightsArr.getD r #[]).toList.length := by
    rw [Array.length_toList, hsz]; exact hc
  rw [fragIntMat, map_getD (fun row : Array ℕ ↦ row.toList.map Int.ofNat) #[] [] _ r hrLt,
    ← array_getD_eq_toList_getD fragmentWeightsArr #[] r,
    map_getD Int.ofNat 0 0 _ c hcLt,
    ← array_getD_eq_toList_getD (fragmentWeightsArr.getD r #[]) 0 c]
  rfl

private lemma innerIntMat_getD {k b : ℕ} (hk : k < 126) (hb : b < 30) :
    (innerIntMat.getD k []).getD b 0 =
      P450.fromOffset ((innerWeightsArr.getD k #[]).getD b (2 ^ 14)) := by
  have hkLt : k < innerWeightsArr.toList.length := by simpa [innerWeightsArr_size] using hk
  have hsz : (innerWeightsArr.getD k #[]).size = 30 := innerWeightsArr_row_size ⟨k, hk⟩
  have hbLt : b < (innerWeightsArr.getD k #[]).toList.length := by
    rw [Array.length_toList, hsz]; exact hb
  rw [innerIntMat,
    map_getD (fun row : Array ℕ ↦ row.toList.map fastFromOffset) #[] [] _ k hkLt,
    ← array_getD_eq_toList_getD innerWeightsArr #[] k,
    map_getD fastFromOffset (2 ^ 14) 0 _ b hbLt, fastFromOffset_eq,
    ← array_getD_eq_toList_getD (innerWeightsArr.getD k #[]) (2 ^ 14) b]

private lemma allCoeffsList_eq :
    allCoeffsList = (List.range 58).map cOneInt ++ (List.range 261).map cLeafInt := by
  simp only [allCoeffsList, withListInt_eq, withMatInt_eq]
  rfl

private lemma int_natAbs_cast (z : ℤ) : (((z.natAbs : ℕ) : ℤ) : ℝ) = |(z : ℝ)| := by
  rcases le_or_gt 0 z with hz | hz
  · have h1 : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hz
    rw [h1, abs_of_nonneg (by exact_mod_cast hz)]
  · have h1 : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hz.le
    rw [h1, Int.cast_neg, abs_of_neg (by exact_mod_cast hz)]

/-- Scale factor $S_{rc} / 15360 = \sqrt{4 n_{rc} q} / 15360$ of fragment `(r, c)`. -/
noncomputable def weightScale (r c : ℕ) : ℝ :=
  √(4 * (((fragmentWeightsArr.getD r #[]).getD c 0 : ℕ) : ℝ) * P450.coefficientUnit) / 15360

private lemma weightScale_nonneg (r c : ℕ) : 0 ≤ weightScale r c :=
  div_nonneg (Real.sqrt_nonneg _) (by norm_num)

private lemma weightScale_sq (r c : ℕ) :
    weightScale r c ^ 2 =
      (((fragmentWeightsArr.getD r #[]).getD c 0 : ℕ) : ℝ) * uScale := by
  unfold weightScale uScale
  have hnn : 0 ≤ 4 * (((fragmentWeightsArr.getD r #[]).getD c 0 : ℕ) : ℝ) *
      P450.coefficientUnit :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) coefficientUnit_nonneg
  rw [div_pow, Real.sq_sqrt hnn]
  ring

private lemma weight_eq_mul_scale (r : Fin 9) (c : Fin 14) (b : Fin 30) :
    P450.weight r c b =
      (P450.fromOffset
          ((innerWeightsArr.getD (14 * r.val + c.val) #[]).getD b.val (2 ^ 14)) : ℝ) *
        weightScale r.val c.val := by
  rw [weight_eq_arr]
  dsimp only [weightScale]
  ring

private lemma oneBodyEigenvalue_eq (ℓ : Fin 58) :
    P450.oneBodyEigenvalue ℓ = (cOneInt ℓ.val : ℝ) * uScale := by
  rw [oneBodyEigenvalue_eq_arr]
  simp only [cOneInt, cOneIntAux, Int.mul_def, uScale]
  rw [oneBodyIntList_getD ℓ.isLt]
  push_cast
  ring

private lemma leafCoeff_eq (μ : Fin 261) :
    (∑ c : Fin 14,
      P450.weight ⟨μ.val / 29, by omega⟩ c 29 *
        P450.weight ⟨μ.val / 29, by omega⟩ c ⟨μ.val % 29, by omega⟩) =
      (cLeafInt μ.val : ℝ) * uScale := by
  let r : Fin 9 := ⟨μ.val / 29, by omega⟩
  let b : Fin 30 := ⟨μ.val % 29, by omega⟩
  have hterm : ∀ c : Fin 14,
      P450.weight r c 29 * P450.weight r c b =
        ((((fragIntMat.getD r.val []).getD c.val 0 *
          (innerIntMat.getD (14 * r.val + c.val) []).getD 29 0 *
          (innerIntMat.getD (14 * r.val + c.val) []).getD b.val 0 : ℤ)) : ℝ) *
          uScale := by
    intro c
    have hk : 14 * r.val + c.val < 126 := by omega
    rw [fragIntMat_getD r.isLt c.isLt, innerIntMat_getD hk (by norm_num),
      innerIntMat_getD hk b.isLt, weight_eq_mul_scale, weight_eq_mul_scale]
    have h29 : (29 : Fin 30).val = 29 := rfl
    rw [h29]
    push_cast
    linear_combination
      (P450.fromOffset ((innerWeightsArr.getD (14 * r.val + c.val) #[]).getD 29 (2 ^ 14)) : ℝ) *
        (P450.fromOffset
          ((innerWeightsArr.getD (14 * r.val + c.val) #[]).getD b.val (2 ^ 14)) : ℝ) *
        weightScale_sq r.val c.val
  change (∑ c : Fin 14, P450.weight r c 29 * P450.weight r c b) = _
  simp_rw [hterm, ← Finset.sum_mul]
  congr 1
  rw [sum_fin_eq_map_range_sum 14 fun c ↦
    ((((fragIntMat.getD r.val []).getD c 0 *
      (innerIntMat.getD (14 * r.val + c) []).getD 29 0 *
      (innerIntMat.getD (14 * r.val + c) []).getD b.val 0 : ℤ)) : ℝ)]
  simp only [cLeafInt, cLeafIntAux, fastIntSum_eq, Int.mul_def, r, b]
  rw [int_cast_list_sum, List.map_map, Function.comp_def]

private lemma twoBodyTerm_eq (r : Fin 9) (c : Fin 14) :
    ((∑ b : Fin 29, |P450.weight r c b.castSucc|) ^ 2 -
      (∑ b : Fin 29, P450.weight r c b.castSucc) ^ 2) =
      (twoBodyTermInt r.val c.val : ℝ) * uScale := by
  have hk : 14 * r.val + c.val < 126 := by omega
  let mrow := innerIntMat.getD (14 * r.val + c.val) []
  have hw : ∀ b : Fin 29,
      P450.weight r c b.castSucc = (mrow.getD b.val 0 : ℝ) * weightScale r.val c.val := by
    intro b
    have hb30 : b.val < 30 := by omega
    dsimp only [mrow]
    rw [innerIntMat_getD hk hb30, weight_eq_mul_scale, Fin.val_castSucc]
  have habs : ∀ b : Fin 29,
      |P450.weight r c b.castSucc| =
        (((mrow.getD b.val 0).natAbs : ℤ) : ℝ) * weightScale r.val c.val := by
    intro b
    rw [hw b, abs_mul, abs_of_nonneg (weightScale_nonneg r.val c.val), int_natAbs_cast]
  have hs1 : (∑ b : Fin 29, |P450.weight r c b.castSucc|) =
      (((List.range 29).map fun b ↦ ((mrow.getD b 0).natAbs : ℤ)).sum : ℝ) *
        weightScale r.val c.val := by
    simp_rw [habs, ← Finset.sum_mul]
    congr 1
    rw [sum_fin_eq_map_range_sum 29 fun b ↦ (((mrow.getD b 0).natAbs : ℤ) : ℝ),
      int_cast_list_sum, List.map_map, Function.comp_def]
  have hs2 : (∑ b : Fin 29, P450.weight r c b.castSucc) =
      (((List.range 29).map fun b ↦ mrow.getD b 0).sum : ℝ) * weightScale r.val c.val := by
    simp_rw [hw, ← Finset.sum_mul]
    congr 1
    rw [sum_fin_eq_map_range_sum 29 fun b ↦ (mrow.getD b 0 : ℝ),
      int_cast_list_sum, List.map_map, Function.comp_def]
  rw [hs1, hs2]
  simp only [twoBodyTermInt, twoBodyTermIntAux, forceInt_eq, fastIntSum_eq,
    Int.ofNat_eq_natCast]
  rw [fragIntMat_getD r.isLt c.isLt]
  dsimp only [mrow]
  generalize ((List.range 29).map fun b ↦
    (((innerIntMat.getD (14 * r.val + c.val) []).getD b 0).natAbs : ℤ)).sum = s1
  generalize ((List.range 29).map fun b ↦
    (innerIntMat.getD (14 * r.val + c.val) []).getD b 0).sum = s2
  push_cast
  linear_combination ((s1 : ℝ) ^ 2 - (s2 : ℝ) ^ 2) * weightScale_sq r.val c.val

private lemma twoBody_sum_eq :
    (∑ r : Fin 9, ∑ c : Fin 14,
      ((∑ b : Fin 29, |P450.weight r c b.castSucc|) ^ 2 -
        (∑ b : Fin 29, P450.weight r c b.castSucc) ^ 2)) =
      (6235149250440 : ℝ) * uScale := by
  simp_rw [twoBodyTerm_eq, ← Finset.sum_mul]
  congr 1
  have htot : (∑ r : Fin 9, ∑ c : Fin 14, (twoBodyTermInt r.val c.val : ℝ)) =
      (twoBodyTotalInt : ℝ) := by
    have hbody : twoBodyTotalInt =
        ((List.range 9).map fun r ↦
          ((List.range 14).map fun c ↦ twoBodyTermInt r c).sum).sum := by
      simp only [twoBodyTotalInt, withMatInt_eq, fastIntSum_eq]
      rfl
    rw [hbody, int_cast_list_sum, List.map_map, Function.comp_def, ← sum_fin_eq_map_range_sum 9]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [int_cast_list_sum, List.map_map, Function.comp_def, ← sum_fin_eq_map_range_sum 14]
  rw [htot, scalar_totals_ok.1]
  norm_num

/-- Real midpoint vector `(midVecOfRow row)[p] / 2^20` approximating a `givensLeaf 15`. -/
noncomputable def midVecReal (row : Array ℕ) (p : Fin 58) : ℝ :=
  ((midVecOfRow row).getD p.val 0 : ℝ) / (ivScale : ℝ)

private lemma row_midVec_diff_sq_le (row : Array ℕ)
    (hmem : row ∈ oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList) :
    ∑ p : Fin 58,
      (givensLeaf 15 (fun q : Fin 58 ↦ (row.getD q.val 0 : ℤ)) p - midVecReal row p) ^ 2 ≤
        (616 / 1048576 : ℝ) ^ 2 := by
  obtain ⟨hlen, hrange⟩ := shapes_ok.2.2 row hmem
  have hcomp : ∀ p : Fin 58,
      (givensLeaf 15 (fun q : Fin 58 ↦ (row.getD q.val 0 : ℤ)) p - midVecReal row p) ^ 2 ≤
        (77 / 1048576 : ℝ) ^ 2 := by
    intro p
    obtain ⟨hivLen, hiv⟩ := givensLeafIv_sound row hlen hrange p
    have hpLt : p.val < (givensLeafIv row.toList).length := by omega
    let iv := (givensLeafIv row.toList).getD p.val (0, 0)
    have hivMem : iv ∈ givensLeafIv row.toList := getD_mem_of_lt _ (0, 0) hpLt
    obtain ⟨hhi, hlo⟩ := radii_ok row hmem iv hivMem
    have hmid : (midVecOfRow row).getD p.val 0 = (iv.1 + iv.2) / 2 := by
      rw [midVecOfRow, map_getD fastMidpoint (0, 0) 0 (givensLeafIv row.toList) p.val hpLt,
        fastMidpoint_eq]
    have hSr : (ivScale : ℝ) = 1048576 := by norm_num [ivScale]
    have hmidR : midVecReal row p = (((iv.1 + iv.2) / 2 : ℤ) : ℝ) / 1048576 := by
      simp only [midVecReal, hmid, hSr]
    have hiv1 : (iv.1 : ℝ) / 1048576 ≤
        givensLeaf 15 (fun q : Fin 58 ↦ (row.getD q.val 0 : ℤ)) p := by
      simpa [iv, hSr] using hiv.1
    have hiv2 : givensLeaf 15 (fun q : Fin 58 ↦ (row.getD q.val 0 : ℤ)) p ≤
        (iv.2 : ℝ) / 1048576 := by
      simpa [iv, hSr] using hiv.2
    have hhiR : (iv.2 : ℝ) - (((iv.1 + iv.2) / 2 : ℤ) : ℝ) ≤ 77 := by exact_mod_cast hhi
    have hloR : (((iv.1 + iv.2) / 2 : ℤ) : ℝ) - (iv.1 : ℝ) ≤ 77 := by exact_mod_cast hlo
    have habs : |givensLeaf 15 (fun q : Fin 58 ↦ (row.getD q.val 0 : ℤ)) p - midVecReal row p| ≤
        77 / 1048576 := by
      rw [hmidR, abs_le]
      constructor <;> linarith
    calc (givensLeaf 15 (fun q : Fin 58 ↦ (row.getD q.val 0 : ℤ)) p - midVecReal row p) ^ 2
        = |givensLeaf 15 (fun q : Fin 58 ↦ (row.getD q.val 0 : ℤ)) p - midVecReal row p| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (77 / 1048576 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc ∑ p : Fin 58,
        (givensLeaf 15 (fun q : Fin 58 ↦ (row.getD q.val 0 : ℤ)) p - midVecReal row p) ^ 2
      ≤ ∑ _p : Fin 58, (77 / 1048576 : ℝ) ^ 2 := Finset.sum_le_sum fun p _ ↦ hcomp p
    _ ≤ (616 / 1048576 : ℝ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- Exact `58 × 58` one-body matrix $H_1$ arising from centered-shift completion of the square. -/
noncomputable def h1Exact : Matrix (Fin 58) (Fin 58) ℝ :=
  (∑ ℓ : Fin 58, P450.oneBodyEigenvalue ℓ •
      Matrix.vecMulVec (P450.oneBodyVector ℓ) (P450.oneBodyVector ℓ)) +
    ∑ μ : Fin 261,
      (∑ c : Fin 14,
        P450.weight ⟨μ.val / 29, by omega⟩ c 29 *
          P450.weight ⟨μ.val / 29, by omega⟩ c ⟨μ.val % 29, by omega⟩) •
        Matrix.vecMulVec (P450.leafVector μ) (P450.leafVector μ)

/-- Midpoint `58 × 58` approximation $\widehat{H}_1$ replacing each `givensLeaf` by `midVecReal`. -/
noncomputable def h1Hat : Matrix (Fin 58) (Fin 58) ℝ :=
  (∑ ℓ : Fin 58, ((cOneInt ℓ.val : ℝ) * uScale) •
      Matrix.vecMulVec (midVecReal (oneBodyAngleTableArr.getD ℓ.val #[]))
        (midVecReal (oneBodyAngleTableArr.getD ℓ.val #[]))) +
    ∑ μ : Fin 261, ((cLeafInt μ.val : ℝ) * uScale) •
      Matrix.vecMulVec (midVecReal (leafAngleTableArr.getD μ.val #[]))
        (midVecReal (leafAngleTableArr.getD μ.val #[]))

private lemma sum_abs_coeffs_eq :
    (∑ ℓ : Fin 58, |(cOneInt ℓ.val : ℝ)|) + (∑ μ : Fin 261, |(cLeafInt μ.val : ℝ)|) =
      (4837203501784 : ℝ) := by
  have h1 : (∑ ℓ : Fin 58, |(cOneInt ℓ.val : ℝ)|) =
      (((List.range 58).map fun ℓ ↦ ((cOneInt ℓ).natAbs : ℤ)).sum : ℝ) := by
    simp_rw [← int_natAbs_cast]
    rw [sum_fin_eq_map_range_sum 58 (fun ℓ ↦ (((cOneInt ℓ).natAbs : ℤ) : ℝ)),
      int_cast_list_sum, List.map_map, Function.comp_def]
  have h2 : (∑ μ : Fin 261, |(cLeafInt μ.val : ℝ)|) =
      (((List.range 261).map fun μ ↦ ((cLeafInt μ).natAbs : ℤ)).sum : ℝ) := by
    simp_rw [← int_natAbs_cast]
    rw [sum_fin_eq_map_range_sum 261 (fun μ ↦ (((cLeafInt μ).natAbs : ℤ) : ℝ)),
      int_cast_list_sum, List.map_map, Function.comp_def]
  have h3 : (sumAbsC : ℝ) =
      (((List.range 58).map fun ℓ ↦ ((cOneInt ℓ).natAbs : ℤ)).sum : ℝ) +
        (((List.range 261).map fun μ ↦ ((cLeafInt μ).natAbs : ℤ)).sum : ℝ) := by
    simp only [sumAbsC, withListInt_eq, fastIntSum_eq, Int.ofNat_eq_natCast]
    rw [allCoeffsList_eq, List.map_append, List.sum_append,
      List.map_map, List.map_map, Function.comp_def, Function.comp_def, Int.cast_add]
  rw [h1, h2, ← h3, scalar_totals_ok.2.1]
  norm_num

private lemma oneBody_h1Exact_sub_h1Hat_le (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    |(star ψ ⬝ᵥ (oneBodyHamiltonian (h1Exact - h1Hat) *ᵥ ψ)).re| ≤
      ((4 * (616 / 1048576 : ℝ) + 2 * (616 / 1048576 : ℝ) ^ 2) *
        4837203501784 * uScale) * vecNormSq ψ := by
  let εVec : ℝ := 616 / 1048576
  have hε0 : 0 ≤ εVec := by norm_num [εVec]
  let errBnd : ℝ := 4 * εVec + 2 * εVec ^ 2
  have hsub : h1Exact - h1Hat =
      (∑ ℓ : Fin 58, ((cOneInt ℓ.val : ℝ) * uScale) •
          (Matrix.vecMulVec (P450.oneBodyVector ℓ) (P450.oneBodyVector ℓ) -
            Matrix.vecMulVec (midVecReal (oneBodyAngleTableArr.getD ℓ.val #[]))
              (midVecReal (oneBodyAngleTableArr.getD ℓ.val #[])))) +
        ∑ μ : Fin 261, ((cLeafInt μ.val : ℝ) * uScale) •
          (Matrix.vecMulVec (P450.leafVector μ) (P450.leafVector μ) -
            Matrix.vecMulVec (midVecReal (leafAngleTableArr.getD μ.val #[]))
              (midVecReal (leafAngleTableArr.getD μ.val #[]))) := by
    dsimp only [h1Exact, h1Hat]
    rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    simp_rw [oneBodyEigenvalue_eq, leafCoeff_eq, ← smul_sub]
  have hone : ∀ ℓ : Fin 58,
      |(star ψ ⬝ᵥ (oneBodyHamiltonian
          (((cOneInt ℓ.val : ℝ) * uScale) •
            (Matrix.vecMulVec (P450.oneBodyVector ℓ) (P450.oneBodyVector ℓ) -
              Matrix.vecMulVec (midVecReal (oneBodyAngleTableArr.getD ℓ.val #[]))
                (midVecReal (oneBodyAngleTableArr.getD ℓ.val #[])))) *ᵥ ψ)).re| ≤
        |(cOneInt ℓ.val : ℝ)| * (uScale * (errBnd * vecNormSq ψ)) := by
    intro ℓ
    rw [oneBodyVector_eq_arr ℓ]
    have hlt : ℓ.val < oneBodyAngleTableArr.size := by rw [shapes_ok.1]; exact ℓ.isLt
    have hmem : oneBodyAngleTableArr.getD ℓ.val #[] ∈
        oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList :=
      List.mem_append_left _ (arr_getD_mem_toList oneBodyAngleTableArr #[] hlt)
    have hdiff := abs_re_oneBody_smul_vecMulVec_diff_le ((cOneInt ℓ.val : ℝ) * uScale)
      (givensLeaf_sum_sq 15 _) hε0 (row_midVec_diff_sq_le _ hmem) ψ
    rwa [abs_mul, abs_of_nonneg uScale_nonneg, mul_assoc] at hdiff
  have hleaf : ∀ μ : Fin 261,
      |(star ψ ⬝ᵥ (oneBodyHamiltonian
          (((cLeafInt μ.val : ℝ) * uScale) •
            (Matrix.vecMulVec (P450.leafVector μ) (P450.leafVector μ) -
              Matrix.vecMulVec (midVecReal (leafAngleTableArr.getD μ.val #[]))
                (midVecReal (leafAngleTableArr.getD μ.val #[])))) *ᵥ ψ)).re| ≤
        |(cLeafInt μ.val : ℝ)| * (uScale * (errBnd * vecNormSq ψ)) := by
    intro μ
    rw [leafVector_eq_arr μ]
    have hlt : μ.val < leafAngleTableArr.size := by rw [shapes_ok.2.1]; exact μ.isLt
    have hmem : leafAngleTableArr.getD μ.val #[] ∈
        oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList :=
      List.mem_append_right _ (arr_getD_mem_toList leafAngleTableArr #[] hlt)
    have hdiff := abs_re_oneBody_smul_vecMulVec_diff_le ((cLeafInt μ.val : ℝ) * uScale)
      (givensLeaf_sum_sq 15 _) hε0 (row_midVec_diff_sq_le _ hmem) ψ
    rwa [abs_mul, abs_of_nonneg uScale_nonneg, mul_assoc] at hdiff
  rw [hsub, re_oneBody_add, re_oneBody_sum, re_oneBody_sum]
  refine ((abs_add_le _ _).trans (add_le_add
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ _ ↦ hone ℓ))
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun μ _ ↦ hleaf μ)))).trans_eq ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, sum_abs_coeffs_eq]
  ring

/-- Scaled witness column vector `col[p] / 2^16`. -/
noncomputable def colVecReal (col : List ℤ) (p : Fin 58) : ℝ :=
  (col.getD p.val 0 : ℝ) / 65536

/-- Positive PSD part $L_+ L_+^T$ (`22` rank-1 terms) of the spectral split witness. -/
noncomputable def h1Pos : Matrix (Fin 58) (Fin 58) ℝ :=
  ∑ k : Fin 22, Matrix.vecMulVec (colVecReal (lPosCols.getD k.val []))
    (colVecReal (lPosCols.getD k.val []))

/-- Negative PSD part $L_- L_-^T$ (`36` rank-1 terms) of the spectral split witness. -/
noncomputable def h1Neg : Matrix (Fin 58) (Fin 58) ℝ :=
  ∑ k : Fin 36, Matrix.vecMulVec (colVecReal (lNegCols.getD k.val []))
    (colVecReal (lNegCols.getD k.val []))

/-- Witness difference $L_+ L_+^T - L_- L_-^T$ approximating $\widehat{H}_1$. -/
noncomputable def h1Wit : Matrix (Fin 58) (Fin 58) ℝ :=
  h1Pos - h1Neg

private lemma sum_pos_col_sq_eq :
    (∑ k : Fin 22, ∑ p : Fin 58, colVecReal (lPosCols.getD k.val []) p ^ 2) =
      (41807165163 : ℝ) / 65536 ^ 2 := by
  obtain ⟨_, _, hsq, hposLen, _, hcolLen⟩ := scalar_totals_ok
  have hcol : ∀ k : Fin 22,
      (∑ p : Fin 58, colVecReal (lPosCols.getD k.val []) p ^ 2) =
        ((((lPosCols.getD k.val []).map fun x : ℤ ↦ x * x).sum : ℤ) : ℝ) / 65536 ^ 2 := by
    intro k
    let col := lPosCols.getD k.val []
    have hkLt : k.val < lPosCols.length := by rw [hposLen]; exact k.isLt
    have hmem : col ∈ lPosCols ++ lNegCols :=
      List.mem_append_left _ (getD_mem_of_lt lPosCols [] hkLt)
    have hlen : col.length = 58 := hcolLen col hmem
    have h1 : (((col.map fun x : ℤ ↦ x * x).sum : ℤ) : ℝ) =
        ∑ p : Fin 58, (col.getD p.val 0 : ℝ) ^ 2 := by
      have hint : (col.map fun x : ℤ ↦ x * x).sum =
          ∑ p : Fin 58, col.getD p.val 0 * col.getD p.val 0 := by
        rw [map_sum_eq_sum_fin 0 col (fun x : ℤ ↦ x * x),
          sum_fin_cast hlen (fun i ↦ col.getD i 0 * col.getD i 0)]
      rw [hint]
      push_cast
      exact Finset.sum_congr rfl fun p _ ↦ by ring
    dsimp only [colVecReal, col] at h1 ⊢
    simp_rw [div_pow, ← Finset.sum_div, h1]
  simp_rw [hcol, ← Finset.sum_div]
  have htot : (∑ k : Fin 22, ((((lPosCols.getD k.val []).map fun x : ℤ ↦ x * x).sum : ℤ) : ℝ)) =
      41807165163 := by
    have hint : (∑ k : Fin 22, ((lPosCols.getD k.val []).map fun x : ℤ ↦ x * x).sum) =
        sumSqPos := by
      simp only [sumSqPos, withMatInt_eq, fastIntSum_eq, Int.mul_def]
      rw [map_sum_eq_sum_fin [] lPosCols (fun col ↦ (col.map fun x : ℤ ↦ x * x).sum),
        sum_fin_cast hposLen (fun i ↦ ((lPosCols.getD i []).map fun x : ℤ ↦ x * x).sum)]
    have hcast : (∑ k : Fin 22, ((((lPosCols.getD k.val []).map fun x : ℤ ↦ x * x).sum : ℤ) : ℝ)) =
        ((sumSqPos : ℤ) : ℝ) := by
      rw [← hint]
      push_cast
      rfl
    rw [hcast, hsq]
    norm_num
  rw [htot]

private lemma oneBody_h1Wit_le (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    (star ψ ⬝ᵥ (oneBodyHamiltonian h1Wit *ᵥ ψ)).re ≤
      (2 * 41807165163 / 65536 ^ 2 : ℝ) * vecNormSq ψ := by
  rw [h1Wit, re_oneBody_sub]
  have hneg : 0 ≤ (star ψ ⬝ᵥ (oneBodyHamiltonian h1Neg *ᵥ ψ)).re := by
    rw [h1Neg, re_oneBody_sum]
    exact Finset.sum_nonneg fun k _ ↦ re_oneBody_vecMulVec_self_nonneg _ ψ
  have hpos : (star ψ ⬝ᵥ (oneBodyHamiltonian h1Pos *ᵥ ψ)).re ≤
      (2 * 41807165163 / 65536 ^ 2 : ℝ) * vecNormSq ψ := by
    rw [h1Pos, re_oneBody_sum]
    calc ∑ k : Fin 22, (star ψ ⬝ᵥ (oneBodyHamiltonian _ *ᵥ ψ)).re
        ≤ ∑ k : Fin 22,
            (2 * ∑ p : Fin 58, colVecReal (lPosCols.getD k.val []) p ^ 2) * vecNormSq ψ :=
          Finset.sum_le_sum fun k _ ↦ re_oneBody_vecMulVec_self_le _ ψ
      _ = (2 * ∑ k : Fin 22, ∑ p : Fin 58, colVecReal (lPosCols.getD k.val []) p ^ 2) *
            vecNormSq ψ := by
          simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = (2 * 41807165163 / 65536 ^ 2 : ℝ) * vecNormSq ψ := by
          rw [sum_pos_col_sq_eq]
          ring
  linarith

private lemma h1Hat_eq_gram_sum (p q : Fin 58) :
    h1Hat p q =
      (((List.zipWith (fun c v ↦ c * v.getD p.val 0 * v.getD q.val 0)
          allCoeffsList midVecsList).sum : ℤ) : ℝ) *
        (uScale / (ivScale : ℝ) ^ 2) := by
  have hcLen : allCoeffsList.length = 58 + 261 := by simp [allCoeffsList_eq]
  have hvLen : midVecsList.length = 58 + 261 := by
    simp [midVecsList, shapes_ok.1, shapes_ok.2.1]
  have hcv : allCoeffsList.length = midVecsList.length := by omega
  have hsum : (List.zipWith (fun c v ↦ c * v.getD p.val 0 * v.getD q.val 0)
        allCoeffsList midVecsList).sum =
      (∑ ℓ : Fin 58, allCoeffsList.getD ℓ.val 0 *
          (midVecsList.getD ℓ.val []).getD p.val 0 *
          (midVecsList.getD ℓ.val []).getD q.val 0) +
        ∑ μ : Fin 261, allCoeffsList.getD (58 + μ.val) 0 *
          (midVecsList.getD (58 + μ.val) []).getD p.val 0 *
          (midVecsList.getD (58 + μ.val) []).getD q.val 0 := by
    rw [zipWith_sum_eq_sum_fin _ _ _ hcv,
      sum_fin_cast hcLen (fun j ↦ allCoeffsList.getD j 0 *
        (midVecsList.getD j []).getD p.val 0 * (midVecsList.getD j []).getD q.val 0),
      sum_fin_add_eq 58 261 (fun j ↦ allCoeffsList.getD j 0 *
        (midVecsList.getD j []).getD p.val 0 * (midVecsList.getD j []).getD q.val 0)]
  have hleft : ∀ ℓ : Fin 58,
      allCoeffsList.getD ℓ.val 0 *
          (midVecsList.getD ℓ.val []).getD p.val 0 *
          (midVecsList.getD ℓ.val []).getD q.val 0 =
        cOneInt ℓ.val *
          (midVecOfRow (oneBodyAngleTableArr.getD ℓ.val #[])).getD p.val 0 *
          (midVecOfRow (oneBodyAngleTableArr.getD ℓ.val #[])).getD q.val 0 := by
    intro ℓ
    have h1 : allCoeffsList.getD ℓ.val 0 = cOneInt ℓ.val := by
      rw [allCoeffsList_eq, getD_append_left _ _ 0 (by simp [ℓ.isLt]),
        map_getD cOneInt 0 0 (List.range 58) ℓ.val (by simp [ℓ.isLt])]
      simp [List.getD_eq_getElem?_getD, ℓ.isLt]
    have h2 : midVecsList.getD ℓ.val [] =
        midVecOfRow (oneBodyAngleTableArr.getD ℓ.val #[]) := by
      dsimp only [midVecsList]
      have hlt : ℓ.val < (oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList).length := by
        simp [shapes_ok.1]; omega
      rw [map_getD midVecOfRow #[] [] _ ℓ.val hlt,
        getD_append_left _ _ #[] (by rw [Array.length_toList, shapes_ok.1]; exact ℓ.isLt),
        ← array_getD_eq_toList_getD oneBodyAngleTableArr #[] ℓ.val]
    rw [h1, h2]
  have hright : ∀ μ : Fin 261,
      allCoeffsList.getD (58 + μ.val) 0 *
          (midVecsList.getD (58 + μ.val) []).getD p.val 0 *
          (midVecsList.getD (58 + μ.val) []).getD q.val 0 =
        cLeafInt μ.val *
          (midVecOfRow (leafAngleTableArr.getD μ.val #[])).getD p.val 0 *
          (midVecOfRow (leafAngleTableArr.getD μ.val #[])).getD q.val 0 := by
    intro μ
    have h1 : allCoeffsList.getD (58 + μ.val) 0 = cLeafInt μ.val := by
      rw [allCoeffsList_eq]
      have happ := getD_append_right ((List.range 58).map cOneInt)
        ((List.range 261).map cLeafInt) 0 μ.val
      simp only [List.length_map, List.length_range] at happ
      rw [happ, map_getD cLeafInt 0 0 (List.range 261) μ.val (by simp [μ.isLt])]
      simp [List.getD_eq_getElem?_getD, μ.isLt]
    have h2 : midVecsList.getD (58 + μ.val) [] =
        midVecOfRow (leafAngleTableArr.getD μ.val #[]) := by
      dsimp only [midVecsList]
      have hlt : 58 + μ.val <
          (oneBodyAngleTableArr.toList ++ leafAngleTableArr.toList).length := by
        simp [shapes_ok.1, shapes_ok.2.1]; omega
      have happ := getD_append_right oneBodyAngleTableArr.toList
        leafAngleTableArr.toList #[] μ.val
      rw [Array.length_toList, shapes_ok.1] at happ
      rw [map_getD midVecOfRow #[] [] _ (58 + μ.val) hlt, happ,
        ← array_getD_eq_toList_getD leafAngleTableArr #[] μ.val]
    rw [h1, h2]
  dsimp only [h1Hat]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, midVecReal]
  rw [hsum, Finset.sum_congr rfl fun ℓ _ ↦ hleft ℓ, Finset.sum_congr rfl fun μ _ ↦ hright μ]
  push_cast
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  · exact Finset.sum_congr rfl fun ℓ _ ↦ by ring
  · exact Finset.sum_congr rfl fun μ _ ↦ by ring

private lemma h1Wit_eq_gram_sum (p q : Fin 58) :
    h1Wit p q =
      (((List.zipWith (fun c v ↦ c * v.getD p.val 0 * v.getD q.val 0)
          witnessWeights (lPosCols ++ lNegCols)).sum : ℤ) : ℝ) / 65536 ^ 2 := by
  obtain ⟨_, _, _, hposLen, hnegLen, _⟩ := scalar_totals_ok
  have hwLen : witnessWeights.length = 22 + 36 := by simp [witnessWeights]
  have hvLen : (lPosCols ++ lNegCols).length = 22 + 36 := by simp [hposLen, hnegLen]
  have hwv : witnessWeights.length = (lPosCols ++ lNegCols).length := by omega
  have hsum : (List.zipWith (fun c v ↦ c * v.getD p.val 0 * v.getD q.val 0)
        witnessWeights (lPosCols ++ lNegCols)).sum =
      (∑ k : Fin 22, witnessWeights.getD k.val 0 *
          ((lPosCols ++ lNegCols).getD k.val []).getD p.val 0 *
          ((lPosCols ++ lNegCols).getD k.val []).getD q.val 0) +
        ∑ k : Fin 36, witnessWeights.getD (22 + k.val) 0 *
          ((lPosCols ++ lNegCols).getD (22 + k.val) []).getD p.val 0 *
          ((lPosCols ++ lNegCols).getD (22 + k.val) []).getD q.val 0 := by
    rw [zipWith_sum_eq_sum_fin _ _ _ hwv,
      sum_fin_cast hwLen (fun j ↦ witnessWeights.getD j 0 *
        ((lPosCols ++ lNegCols).getD j []).getD p.val 0 *
        ((lPosCols ++ lNegCols).getD j []).getD q.val 0),
      sum_fin_add_eq 22 36 (fun j ↦ witnessWeights.getD j 0 *
        ((lPosCols ++ lNegCols).getD j []).getD p.val 0 *
        ((lPosCols ++ lNegCols).getD j []).getD q.val 0)]
  have hleft : ∀ k : Fin 22,
      witnessWeights.getD k.val 0 *
          ((lPosCols ++ lNegCols).getD k.val []).getD p.val 0 *
          ((lPosCols ++ lNegCols).getD k.val []).getD q.val 0 =
        (lPosCols.getD k.val []).getD p.val 0 *
          (lPosCols.getD k.val []).getD q.val 0 := by
    intro k
    have h1 : witnessWeights.getD k.val 0 = 1 := by
      dsimp only [witnessWeights]
      rw [getD_append_left _ _ 0 (by simp [k.isLt]), replicate_getD 22 1 0 k.val k.isLt]
    have h2 : (lPosCols ++ lNegCols).getD k.val [] = lPosCols.getD k.val [] :=
      getD_append_left _ _ [] (by rw [hposLen]; exact k.isLt)
    rw [h1, h2, one_mul]
  have hright : ∀ k : Fin 36,
      witnessWeights.getD (22 + k.val) 0 *
          ((lPosCols ++ lNegCols).getD (22 + k.val) []).getD p.val 0 *
          ((lPosCols ++ lNegCols).getD (22 + k.val) []).getD q.val 0 =
        -((lNegCols.getD k.val []).getD p.val 0 *
          (lNegCols.getD k.val []).getD q.val 0) := by
    intro k
    have h1 : witnessWeights.getD (22 + k.val) 0 = -1 := by
      dsimp only [witnessWeights]
      have happ := getD_append_right (List.replicate 22 (1 : ℤ))
        (List.replicate 36 (-1 : ℤ)) 0 k.val
      simp only [List.length_replicate] at happ
      rw [happ, replicate_getD 36 (-1) 0 k.val k.isLt]
    have h2 : (lPosCols ++ lNegCols).getD (22 + k.val) [] = lNegCols.getD k.val [] := by
      have happ := getD_append_right lPosCols lNegCols [] k.val
      rwa [hposLen] at happ
    rw [h1, h2]
    ring
  dsimp only [h1Wit, h1Pos, h1Neg]
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, colVecReal]
  rw [hsum, Finset.sum_congr rfl fun k _ ↦ hleft k, Finset.sum_congr rfl fun k _ ↦ hright k]
  push_cast
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_div, Finset.sum_div, Finset.sum_div]
  refine congrArg₂ HSub.hSub ?_ ?_
  · exact Finset.sum_congr rfl fun k _ ↦ by ring
  · exact Finset.sum_congr rfl fun k _ ↦ by ring

private lemma addRowInt_getD :
    ∀ (r s : List ℤ) (q : ℕ), (addRowInt r s).getD q 0 = r.getD q 0 + s.getD q 0
  | [], ys, q => by simp [addRowInt]
  | x :: xs, [], q => by simp [addRowInt]
  | x :: xs, y :: ys, 0 => by simp [addRowInt, Int.add_def]
  | x :: xs, y :: ys, q + 1 => by
      simp only [addRowInt, forceInt_eq, List.getD_cons_succ, addRowInt_getD xs ys q]

private lemma addMatInt_getD :
    ∀ (A B : List (List ℤ)) (p q : ℕ),
      ((addMatInt A B).getD p []).getD q 0 =
        (A.getD p []).getD q 0 + (B.getD p []).getD q 0
  | [], Bs, p, q => by simp [addMatInt]
  | r :: rs, [], p, q => by simp [addMatInt]
  | r :: rs, s :: ss, 0, q => by
      simp only [addMatInt, withListInt_eq, List.getD_cons_zero, addRowInt_getD]
  | r :: rs, s :: ss, p + 1, q => by
      simp only [addMatInt, withListInt_eq, List.getD_cons_succ, addMatInt_getD rs ss p q]

private lemma zipWith_append_sum {α β : Type*} (f : α → β → ℤ) :
    ∀ (as1 as2 : List α) (bs1 bs2 : List β),
      as1.length = bs1.length →
      (List.zipWith f (as1 ++ as2) (bs1 ++ bs2)).sum =
        (List.zipWith f as1 bs1).sum + (List.zipWith f as2 bs2).sum
  | [], _, [], _, _ => by simp
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | a :: as1, as2, b :: bs1, bs2, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons,
        zipWith_append_sum f as1 as2 bs1 bs2 h, add_assoc]

private lemma checkGramSlice_sound {cs : List ℤ} {vs target : List (List ℤ)}
    (h : checkGramSlice cs vs target = true) {p q : ℕ} (hp : p < 58) (hq : q < 58) :
    (target.getD p []).getD q 0 =
      (List.zipWith (fun c v ↦ c * v.getD p 0 * v.getD q 0) cs vs).sum := by
  unfold checkGramSlice at h
  cases hev : evalWeightedGram base96 58 1048576 bias58 cs vs with
  | none => rw [hev] at h; cases h
  | some rows =>
      rw [hev, matIntBeq_eq] at h
      subst h
      exact evalWeightedGram_sound hev hp hq

private lemma gramTotal_entry_eq {p q : ℕ} (hp : p < 58) (hq : q < 58) :
    (gramTotal.getD p []).getD q 0 =
      (List.zipWith (fun c v ↦ c * v.getD p 0 * v.getD q 0) allCoeffsList midVecsList).sum := by
  have htot :
      addMatInt gramSlice0
        (addMatInt gramSlice1
          (addMatInt gramSlice2 (addMatInt gramSlice3 gramSlice4))) = gramTotal :=
    matIntBeq_eq.mp gram_total_ok
  obtain ⟨hl0, hl1, hl2, hl3⟩ := slice_lengths_eq
  let g : ℤ → List ℤ → ℤ := fun c v ↦ c * v.getD p 0 * v.getD q 0
  rw [← htot, addMatInt_getD, addMatInt_getD, addMatInt_getD, addMatInt_getD,
    checkGramSlice_sound gram_slice0_ok hp hq,
    checkGramSlice_sound gram_slice1_ok hp hq,
    checkGramSlice_sound gram_slice2_ok hp hq,
    checkGramSlice_sound gram_slice3_ok hp hq,
    checkGramSlice_sound gram_slice4_ok hp hq,
    allCoeffsList_eq_slices, midVecsList_eq_slices,
    zipWith_append_sum g _ _ _ _ hl0,
    zipWith_append_sum g _ _ _ _ hl1,
    zipWith_append_sum g _ _ _ _ hl2,
    zipWith_append_sum g _ _ _ _ hl3]

private lemma checkRowDiff_getD {cH cL : ℤ} {bnd : ℕ} :
    ∀ {n q : ℕ} {hr lr : List ℤ},
      checkRowDiff n hr lr cH cL bnd = true → q < n →
      (hr.getD q 0 * cH - lr.getD q 0 * cL).natAbs ≤ bnd
  | 0, _, _, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | _ + 1, _, [], _, h, _ => by simp [checkRowDiff] at h
  | _ + 1, _, _ :: _, [], h, _ => by simp [checkRowDiff] at h
  | _ + 1, 0, h :: _, l :: _, hok, _ => by
      simp only [checkRowDiff, Bool.and_eq_true, Nat.ble_eq] at hok
      simp only [List.getD_cons_zero]
      exact hok.1
  | _ + 1, q + 1, _ :: hs, _ :: ls, hok, hq => by
      simp only [checkRowDiff, Bool.and_eq_true] at hok
      simpa only [List.getD_cons_succ] using
        checkRowDiff_getD hok.2 (Nat.lt_of_succ_lt_succ hq)

private lemma checkRowsDiff_getD {cH cL : ℤ} {bnd : ℕ} :
    ∀ {m n p q : ℕ} {hRows lRows : List (List ℤ)},
      checkRowsDiff m n hRows lRows cH cL bnd = true → p < m → q < n →
      ((hRows.getD p []).getD q 0 * cH - (lRows.getD p []).getD q 0 * cL).natAbs ≤ bnd
  | 0, _, _, _, _, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | _ + 1, _, _, _, [], _, h, _, _ => by simp [checkRowsDiff] at h
  | _ + 1, _, _, _, _ :: _, [], h, _, _ => by simp [checkRowsDiff] at h
  | _ + 1, _, 0, _, hr :: _, lr :: _, hok, _, hq => by
      simp only [checkRowsDiff, Bool.and_eq_true] at hok
      simpa only [List.getD_cons_zero] using checkRowDiff_getD hok.1 hq
  | _ + 1, _, p + 1, _, _ :: hrs, _ :: lrs, hok, hp, hq => by
      simp only [checkRowsDiff, Bool.and_eq_true] at hok
      simpa only [List.getD_cons_succ] using
        checkRowsDiff_getD hok.2 (Nat.lt_of_succ_lt_succ hp) hq

attribute [local irreducible]
  evalWeightedGram base96 bias58 allCoeffsList midVecsList witnessWeights
  coeffsSlice0 coeffsSlice1 coeffsSlice2 coeffsSlice3 coeffsSlice4
  midVecsSlice0 midVecsSlice1 midVecsSlice2 midVecsSlice3 midVecsSlice4
  checkGramSlice addMatInt checkRowDiff checkRowsDiff

private lemma entry_h1Hat_sub_h1Wit_le (p q : Fin 58) :
    |(h1Hat - h1Wit) p q| ≤
      (285044355550348197604220 : ℝ) / (3556232921088000000 * 65536 ^ 2 : ℝ) := by
  have hg : checkGramDiffAux (some gramTotal)
      (evalWeightedGram base96 58 1048576 bias58 witnessWeights (lPosCols ++ lNegCols)) = true := by
    have h := gram_wit_diff_ok
    simpa only [checkGramWitDiff, withMatInt_eq] using h
  cases hL : evalWeightedGram base96 58 1048576 bias58 witnessWeights
      (lPosCols ++ lNegCols) with
  | none => rw [hL] at hg; cases hg
  | some lRows =>
      rw [hL] at hg
      simp only [checkGramDiffAux, forceInt_eq, forceNat_eq] at hg
      have hbnd := checkRowsDiff_getD hg p.isLt q.isLt
      have hsH := gramTotal_entry_eq p.isLt q.isLt
      have hsL := evalWeightedGram_sound hL p.isLt q.isLt
      have hscale : uScale / (ivScale : ℝ) ^ 2 =
          (121733 : ℝ) / (3556232921088000000 * 65536 ^ 2 : ℝ) := by
        rw [uScale_eq]
        norm_num [ivScale]
      have hsub : (h1Hat - h1Wit) p q =
          ((((gramTotal.getD p.val []).getD q.val 0 * 121733 -
            (lRows.getD p.val []).getD q.val 0 * 3556232921088000000 : ℤ)) : ℝ) /
            (3556232921088000000 * 65536 ^ 2 : ℝ) := by
        rw [Matrix.sub_apply, h1Hat_eq_gram_sum p q, h1Wit_eq_gram_sum p q,
          ← hsH, ← hsL, hscale]
        push_cast
        ring
      have habsInt :
          |(((gramTotal.getD p.val []).getD q.val 0 * 121733 -
              (lRows.getD p.val []).getD q.val 0 * 3556232921088000000 : ℤ) : ℝ)| ≤
            285044355550348197604220 := by
        rw [← int_natAbs_cast]
        exact_mod_cast hbnd
      rw [hsub, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3556232921088000000 * 65536 ^ 2)]
      exact div_le_div_of_nonneg_right habsInt (by norm_num)

private lemma oneBody_h1Hat_sub_h1Wit_le (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    |(star ψ ⬝ᵥ (oneBodyHamiltonian (h1Hat - h1Wit) *ᵥ ψ)).re| ≤
      (2 * 58 * 58 * 285044355550348197604220 /
        (3556232921088000000 * 65536 ^ 2) : ℝ) * vecNormSq ψ := by
  have hsum : (∑ p : Fin 58, ∑ q : Fin 58, |(h1Hat - h1Wit) p q|) ≤
      58 * 58 * (285044355550348197604220 : ℝ) / (3556232921088000000 * 65536 ^ 2 : ℝ) := by
    calc ∑ p : Fin 58, ∑ q : Fin 58, |(h1Hat - h1Wit) p q|
        ≤ ∑ _p : Fin 58, ∑ _q : Fin 58,
            (285044355550348197604220 : ℝ) / (3556232921088000000 * 65536 ^ 2 : ℝ) :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun q _ ↦ entry_h1Hat_sub_h1Wit_le p q
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  refine (abs_re_oneBody_matrix_le (h1Hat - h1Wit) ψ).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg ψ)
  linarith

theorem dfthc_quadForm_re_le_48 (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    (star ψ ⬝ᵥ (thcHamiltonian P450.dfthc *ᵥ ψ)).re ≤ 48 * vecNormSq ψ := by
  have hthc := thcHamiltonian_dfthc_shape_quadForm_le P450.dfthc
    P450.oneBodyEigenvalue P450.oneBodyVector P450.weight rfl rfl ψ
  have hh1Eq : ((∑ ℓ : Fin 58, P450.oneBodyEigenvalue ℓ •
        Matrix.vecMulVec (P450.oneBodyVector ℓ) (P450.oneBodyVector ℓ)) +
      ∑ μ : Fin 261,
        (∑ c : Fin 14, P450.weight ⟨μ.val / 29, by omega⟩ c 29 *
          P450.weight ⟨μ.val / 29, by omega⟩ c ⟨μ.val % 29, by omega⟩) •
          Matrix.vecMulVec (P450.dfthc.chi μ) (P450.dfthc.chi μ)) = h1Exact := rfl
  rw [hh1Eq] at hthc
  rw [twoBody_sum_eq] at hthc
  have hsplit : h1Exact = (h1Exact - h1Hat) + (h1Hat - h1Wit) + h1Wit := by abel
  have hone : (star ψ ⬝ᵥ (oneBodyHamiltonian h1Exact *ᵥ ψ)).re =
      (star ψ ⬝ᵥ (oneBodyHamiltonian (h1Exact - h1Hat) *ᵥ ψ)).re +
        (star ψ ⬝ᵥ (oneBodyHamiltonian (h1Hat - h1Wit) *ᵥ ψ)).re +
        (star ψ ⬝ᵥ (oneBodyHamiltonian h1Wit *ᵥ ψ)).re := by
    conv_lhs => rw [hsplit]
    rw [re_oneBody_add, re_oneBody_add]
  have bVec := (le_abs_self _).trans (oneBody_h1Exact_sub_h1Hat_le ψ)
  have bMat := (le_abs_self _).trans (oneBody_h1Hat_sub_h1Wit_le ψ)
  have bWit := oneBody_h1Wit_le ψ
  have hnum :
      (1 / 2 : ℝ) * (6235149250440 * uScale) +
        (4 * (616 / 1048576 : ℝ) + 2 * (616 / 1048576 : ℝ) ^ 2) *
          4837203501784 * uScale +
        2 * 58 * 58 * 285044355550348197604220 /
          (3556232921088000000 * 65536 ^ 2 : ℝ) +
        2 * 41807165163 / 65536 ^ 2 ≤ 48 := by
    rw [uScale_eq]
    norm_num
  have hmul := mul_le_mul_of_nonneg_right hnum (vecNormSq_nonneg ψ)
  linarith

end UpperBound
/-- Certified upper bound (`+48` Ha) on all eigenvalues of `thcHamiltonian P450.dfthc`, strictly
below the doubled-phase spectral-amplification non-aliasing threshold (`~ +54.3` Ha). -/
noncomputable abbrev dfthcUpperBound : ℝ := 48

/-- Non-aliasing margin: `dfthcUpperBound ≤ dfthcLowerBound + 2 * p450Lambda - E_gap` for any
spectral-amplification gap window `E_gap ≤ 11` Ha (e.g. `E_gap ≈ 5.6` Ha). -/
theorem dfthcUpperBound_le_nonAliasing {E_gap : ℝ} (hgap : E_gap ≤ 11) :
    dfthcUpperBound ≤ dfthcLowerBound + 2 * p450Lambda - E_gap := by
  rw [dfthcLowerBound_eq_rat]
  unfold dfthcUpperBound p450Lambda
  linarith

/-- Global quadratic-form upper bound $\operatorname{Re}\langle \psi, H_{\text{DFTHC}}\psi\rangle
\le 48 \|\psi\|_2^2$ on all `116`-qubit states. -/
theorem thcHamiltonian_dfthc_quadForm_re_le (ψ : Fin (2 ^ (2 * 58)) → ℂ) :
    (star ψ ⬝ᵥ (thcHamiltonian dfthc *ᵥ ψ)).re ≤
      dfthcUpperBound * ∑ i, Complex.normSq (ψ i) :=
  UpperBound.dfthc_quadForm_re_le_48 ψ

/-- Every eigenvalue `E` of `thcHamiltonian P450.dfthc` (on any non-zero `116`-qubit eigenvector,
regardless of electron number) satisfies `E ≤ 48`. -/
theorem thcHamiltonian_dfthc_eigenvalue_le {E : ℝ} {ψ : Fin (2 ^ (2 * 58)) → ℂ}
    (heig : thcHamiltonian dfthc *ᵥ ψ = (E : ℂ) • ψ) (hψ : ψ ≠ 0) :
    E ≤ dfthcUpperBound :=
  UpperBound.eigenvalue_le_of_quadForm_re_le thcHamiltonian_dfthc_quadForm_re_le heig hψ
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
