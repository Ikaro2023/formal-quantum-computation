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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.QubitizationFoundations
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
@[expose] public section

set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.DiagShiftSpecBridge
set_option exponentiation.threshold 8192
open scoped Matrix Matrix.Norms.L2Operator
open Operator Matrix NormedSpace PhotochemistrySolution.QubitizationCore PhotochemistrySolution.GQSP
theorem approximatesTimeEvolution_sub_smul_one {k m : ℕ} (H : Operator (2 ^ k)) (c t ε : ℝ)
    (P : Operator (2 ^ k)) (W : Unitary (2 ^ (k + m)))
    (h : ApproximatesTimeEvolution (H - (c : ℂ) • 1) t ε P W) :
    ApproximatesTimeEvolution H t ε P W := by
  obtain ⟨φ, hφ⟩ := h; refine ⟨φ + c * t, ?_⟩
  set sys : QRegister k (k + m) := .block 0 k (by omega)
  have hexp := exp_sub_smul_one_eq_smul_exp H c t
  have hphase : Complex.exp (((φ + c * t : ℝ) : ℂ) * Complex.I) = Complex.exp ((φ : ℂ) *
      Complex.I) * Complex.exp (((c * t : ℝ) : ℂ) * Complex.I)
      := by rw [← Complex.exp_add]; push_cast; ring_nf
  simpa only [hexp, sys.embedMatrix_smul, smul_smul, ← hphase] using hφ
theorem approximatesTimeEvolution_sub_smul_one_iff {k m : ℕ} (H : Operator (2 ^ k)) (c t ε : ℝ)
    (P : Operator (2 ^ k)) (W : Unitary (2 ^ (k + m))) : ApproximatesTimeEvolution (H -
    (c : ℂ) • 1) t ε P W ↔ ApproximatesTimeEvolution H t ε P W := by
  refine ⟨approximatesTimeEvolution_sub_smul_one H c t ε P W, fun h ↦ ?_⟩
  have hsub : H - (c : ℂ) • (1 : Operator (2 ^ k)) - ((-c : ℝ) : ℂ) • 1 = H := by
    simp [sub_eq_add_neg, add_assoc]
  exact approximatesTimeEvolution_sub_smul_one (H - (c : ℂ) • 1) (-c) t ε P W (by rwa [hsub])
theorem approximatesTimeEvolution_of_rescaled_blockEncoding {k m : ℕ} {H A : Operator (2 ^ k)}
    (hH : Hᴴ = H) (hA : Aᴴ = A) {α' c t ε_walk ε_block ε : ℝ} (hα' : 0 < α') (ht : 0 ≤ t)
    (W : Unitary (2 ^ (k + m))) (hwalk : ApproximatesTimeEvolution A (α' * t) ε_walk 1 W)
    (hblock : ‖A - (α' : ℂ)⁻¹ • (H - (c : ℂ) • (1 : Operator (2 ^ k)))‖ ≤ ε_block)
    (htot : ε_walk + (α' * t) * ε_block ≤ ε) : ApproximatesTimeEvolution H t ε 1 W := by
  rw [← approximatesTimeEvolution_sub_smul_one_iff H c t ε 1 W]
  obtain ⟨φ, hφ⟩ := hwalk; refine ⟨φ, ?_⟩
  set sys : QRegister k (k + m) := .block 0 k (by omega)
  set anc : QRegister m (k + m) := .block k m le_rfl
  set H' : Operator (2 ^ k) := H - (c : ℂ) • 1; set B : Operator (2 ^ k) := (α' : ℂ)⁻¹ • H'
  have hB : Bᴴ = B := by simp [B, H', Matrix.conjTranspose_sub, hH]
  have hsmul : (-Complex.I * ((α' * t : ℝ) : ℂ)) • B = (-Complex.I * (t : ℂ)) • H' := by
    dsimp [B]; rw [smul_smul]; congr 1
    have hα0 : (α' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα'.ne'
    push_cast; field_simp [hα0]
  have hpert := norm_exp_neg_mul_I_sub_le hA hB (mul_nonneg hα'.le ht); rw [hsmul] at hpert
  set UA := sys.embedMatrix (NormedSpace.exp ((-Complex.I * ((α' * t : ℝ) : ℂ)) • A))
  set UH' := sys.embedMatrix (NormedSpace.exp ((-Complex.I * (t : ℂ)) • H'))
  set inp := sys.embedMatrix 1 * anc.basisOutcomeProjector 0
  have hdiff : ‖UA - UH'‖ ≤ (α' * t) * ε_block := by
    rw [← embedMatrix_sub];
    exact (opNorm_embedMatrix_le sys _).trans (hpert.trans (mul_le_mul_of_nonneg_left hblock
        (mul_nonneg hα'.le ht)))
  have hP0 : ‖inp‖ ≤ 1 := by
    dsimp [inp]; rw [sys.embedMatrix_one, Matrix.one_mul]
    exact norm_projector_le_one (anc.basisOutcomeProjector_conjTranspose 0)
        (anc.basisOutcomeProjector_mul_self 0)
  have htri : (W.1 - Complex.exp ((φ : ℂ) * Complex.I) • UH') * inp =
      (W.1 - Complex.exp ((φ : ℂ) * Complex.I) • UA) * inp +
      (Complex.exp ((φ : ℂ) * Complex.I) • (UA - UH')) * inp := by
    simp only [sub_mul, smul_sub]; abel
  have hrem : ‖(Complex.exp ((φ : ℂ) * Complex.I) • (UA - UH')) * inp‖ ≤ (α' * t) * ε_block := by
    rw [smul_mul_assoc, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul];
    exact (norm_mul_le _ _).trans ((mul_le_mul hdiff hP0 (norm_nonneg _)
        (mul_nonneg (mul_nonneg hα'.le ht) ((norm_nonneg _).trans hblock))).trans (mul_one _).le)
  exact (htri ▸ norm_add_le _ _).trans ((add_le_add hφ hrem).trans htot)
end QuantumComputation.Specs.PhotochemistrySolution.DiagShiftSpecBridge
end
end
