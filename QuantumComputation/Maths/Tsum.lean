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

public import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumComputation.Maths.Matrix

/-!
# Miscellaneous lemmas about `tsum`
-/

@[expose] public section

open Operator Matrix
open scoped Matrix ComplexOrder MatrixOrder NNReal ENNReal Int InnerProductSpace

theorem NNReal.summable_of_sum_le {ι : Type*} {f : ι → ℝ≥0} {c : ℝ≥0}
    (h : ∀ u : Finset ι, ∑ x ∈ u, f x ≤ c) : Summable f := by
  rw [← NNReal.summable_coe]
  exact _root_.summable_of_sum_le (fun _ ↦ NNReal.coe_nonneg _) fun u ↦ by exact_mod_cast h u

/--
A more general version of `tprod_mem`,
from https://github.com/leanprover-community/mathlib4/pull/44511
-/
@[to_additive]
theorem tprod_mem'
    {ι S α : Type*} {s : S} [TopologicalSpace α] [CommMonoid α] [SetLike S α] [SubmonoidClass S α]
    (h_closed : IsClosed (s : Set α)) {f : ι → α} (h : ∀ i, f i ∈ s)
    (L := SummationFilter.unconditional ι) :
    ∏'[L] i, f i ∈ s := by
  by_cases hL : L.NeBot
  · by_cases hf : Multipliable f L
    · exact h_closed.mem_of_tendsto hf.hasProd <| .of_forall fun _ => prod_mem fun i _ => h i
    · simp [tprod_eq_one_of_not_multipliable hf, one_mem]
  · rw [tprod_bot hL]
    exact finprod_induction _ (one_mem _) (fun _ _ => mul_mem) h

/-- A sequence with constant ratio `q` sums to `f 0 / (1 - q)`. -/
theorem ENNReal.tsum_eq_mul_inv_of_succ {f : ℕ → ℝ≥0∞} {q : ℝ≥0∞}
    (h : ∀ n, f (n + 1) = q * f n) : ∑' n, f n = f 0 * (1 - q)⁻¹ := by
  have hpow (n : ℕ) : f n = q ^ n * f 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [h n, ih, pow_succ', mul_assoc]
  rw [tsum_congr hpow, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

namespace Matrix
variable {α n R : Type*}

lemma IsHermitian.of_hasSum
    [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [StarRing R] [ContinuousStar R] [T2Space R]
    {f : α → Matrix n n R} {a : Matrix n n R} {L : SummationFilter α} [L.NeBot]
    (h : HasSum f a L) (hf : ∀ i, (f i).IsHermitian) :
    a.IsHermitian :=
  h.star.unique (by simpa only [show ∀ i, star (f i) = f i from hf] using h)

lemma isClosed_isHermitian [TopologicalSpace R] [Star R] [ContinuousStar R] [T2Space R] :
    IsClosed {A : Matrix n n R | IsHermitian A} :=
  isClosed_eq continuous_star continuous_id

lemma IsHermitian.tsum
    [AddCommMonoid R] [TopologicalSpace R] [StarAddMonoid R] [ContinuousStar R] [T2Space R]
    {L : SummationFilter α} {f : α → Matrix n n R} (hf : ∀ i, (f i).IsHermitian) :
    (∑'[L] a, f a).IsHermitian :=
  conjTranspose_tsum.trans (tsum_congr hf)

lemma PosSemidef.of_hasSum
    [Ring R] [TopologicalSpace R] [StarRing R] [IsTopologicalSemiring R] [PartialOrder R]
    [IsOrderedAddMonoid R] [OrderClosedTopology R] [ContinuousStar R]
    {f : α → Matrix n n R} {a : Matrix n n R} {L : SummationFilter α} [L.NeBot] (h : HasSum f a L)
    (hf : ∀ i, (f i).PosSemidef) :
    a.PosSemidef :=
  ⟨.of_hasSum h fun i ↦ (hf i).1, fun x ↦
    (hasSum_sum fun r _ ↦ hasSum_sum fun c _ ↦
      (((Pi.hasSum.mp (Pi.hasSum.mp h r) c).mul_left _).mul_right _)).nonneg fun i ↦ (hf i).2 x⟩

lemma isClosed_posSemidef
    [Ring R] [TopologicalSpace R] [StarRing R] [IsTopologicalSemiring R] [PartialOrder R]
    [OrderClosedTopology R] [ContinuousStar R] :
    IsClosed {A : Matrix n n R | PosSemidef A} := by
  simp only [PosSemidef, Set.ofPred_and, Set.ofPred_forall]
  refine isClosed_isHermitian.inter (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  fun_prop

lemma PosSemidef.tsum
    [Ring R] [TopologicalSpace R] [StarRing R] [IsTopologicalSemiring R] [PartialOrder R]
    [IsOrderedAddMonoid R] [OrderClosedTopology R] [ContinuousStar R]
    {L : SummationFilter α} {f : α → Matrix n n R} (hf : ∀ i, (f i).PosSemidef) :
    (∑'[L] a, f a).PosSemidef :=
  let : AddSubmonoid (Matrix n n R) :=
    { carrier := .ofPred PosSemidef, add_mem' := .add, zero_mem' := .zero }
  tsum_mem' (s := this) isClosed_posSemidef hf L

open scoped MatrixOrder in
/-- A specialization of `tsum_nonneg`, to avoid elaboration issues downstream. -/
protected lemma tsum_nonneg {𝕜 : Type*} [RCLike 𝕜] {f : α → Matrix n n 𝕜} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ ∑' a, f a :=
  tsum_nonneg hf

section trace
variable [Fintype n] [TopologicalSpace R] [AddCommMonoid R] [ContinuousAdd R]

lemma _root_.HasSum.matrix_trace {f : α → Matrix n n R} {a : Matrix n n R} (hf : HasSum f a) :
    HasSum (fun a => (f a).trace) a.trace :=
  hf.map (traceAddMonoidHom n R) (.matrix_trace <| continuous_id)

lemma _root_.Summable.matrix_trace {f : α → Matrix n n R} (hf : Summable f) :
    Summable (fun a => (f a).trace) :=
  hf.hasSum.matrix_trace.summable

lemma trace_tsum [T2Space R] {f : α → Matrix n n R} (hf : Summable f) :
    (∑' a, f a).trace = ∑' a, (f a).trace :=
  hf.hasSum.matrix_trace.tsum_eq.symm

end trace

end Matrix

theorem Summable.hermitianMatMat
    {α n R : Type*} [AddCommGroup R] [StarAddMonoid R] [TopologicalSpace R]
    {f : α → HermitianMat n R} (hf : Summable f) :
    Summable (fun a ↦ (f a).mat) :=
  (HermitianMat.matₗ (R := ℕ)).summable hf

namespace HermitianMat

@[simp, norm_cast]
lemma mat_tsum
    {α n R : Type*} [AddCommGroup R] [StarAddMonoid R] [TopologicalSpace R]
    [ContinuousStar R] [T2Space R]
    (f : α → HermitianMat n R) (L := SummationFilter.unconditional α) :
    (∑'[L] a, f a).mat = ∑'[L] a, (f a).mat :=
  Matrix.isClosed_isHermitian.isClosedEmbedding_subtypeVal.map_tsum
    (g := HermitianMat.matₗ (R := ℕ)) f

lemma conj_tsum
    {α m n R : Type*} [CommRing R] [StarRing R] [Fintype n]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (B : Matrix m n R) {f : α → HermitianMat n R} {L : SummationFilter α} [L.NeBot]
    (hf : Summable f L) :
    (∑'[L] a, f a).conj B = ∑'[L] a, (f a).conj B :=
  hf.map_tsum (HermitianMat.conj B) (continuous_conj_right B)

variable {n α 𝕜 : Type*} [Fintype n] [RCLike 𝕜]

lemma inner_tsum (A : HermitianMat n 𝕜) {f : α → HermitianMat n 𝕜} (hf : Summable f) :
    ⟪A, ∑' a, f a⟫_ℝ = ∑' a, ⟪A, f a⟫_ℝ :=
  (A.innerₗ.toContinuousLinearMap).map_tsum hf

lemma trace_tsum {f : α → HermitianMat n 𝕜} (hf : Summable f) :
    (∑' a, f a).trace = ∑' a, (f a).trace := by
  classical
  simpa only [HermitianMat.one_inner] using HermitianMat.inner_tsum 1 hf

end HermitianMat

section norms

lemma Matrix.norm_le_frobenius_norm {m n α : Type*} [Fintype m] [Fintype n]
    [SeminormedAddCommGroup α] (A : Matrix m n α) :
    open scoped Matrix.Norms.Elementwise in ‖A‖ ≤ open scoped Matrix.Norms.Frobenius in ‖A‖ :=
  norm_le_iff (norm_nonneg _) |>.2 fun i j =>
    (PiLp.norm_apply_le (WithLp.toLp 2 (A i)) j).trans
      (PiLp.norm_apply_le (WithLp.toLp 2 fun i ↦ WithLp.toLp 2 (A i)) i)

variable {ι 𝕜 : Type*} [RCLike 𝕜]

lemma Matrix.PosSemidef.norm_apply_sq_le {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) (i j : ι) :
    ‖A i j‖ ^ 2 ≤ RCLike.re (A i i) * RCLike.re (A j j) := by
  have hcs : A i j * A j i ≤ A i i * A j j := by
    have hdet := (hA.submatrix ![i, j]).det_nonneg
    rwa [Matrix.det_fin_two, sub_nonneg] at hdet
  rw [← hA.isHermitian.apply j i, RCLike.star_def, RCLike.mul_conj] at hcs
  simpa [RCLike.mul_re, (RCLike.nonneg_iff.mp hA.diag_nonneg).2, ← map_pow] using
    RCLike.re_le_re hcs

variable [Fintype ι]

lemma Matrix.PosSemidef.frobenius_norm_le_re_trace {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    (open scoped Matrix.Norms.Frobenius in ‖A‖) ≤ RCLike.re A.trace := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow,
    Real.sqrt_le_left (RCLike.nonneg_iff.mp hA.trace_nonneg).1]
  calc ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)
    _ ≤ ∑ i, ∑ j, RCLike.re (A i i) * RCLike.re (A j j) := by
        gcongr with i _ j _
        exact_mod_cast hA.norm_apply_sq_le i j
    _ = RCLike.re A.trace ^ 2 := by simp [Matrix.trace, Fintype.sum_mul_sum, sq]

lemma Matrix.PosSemidef.norm_le_re_trace {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    open scoped Matrix.Norms.Elementwise in ‖A‖ ≤ RCLike.re A.trace := by
  grw [norm_le_frobenius_norm, hA.frobenius_norm_le_re_trace]

lemma HermitianMat.norm_le_trace {A : HermitianMat ι 𝕜} (hA : 0 ≤ A) :
    ‖A‖ ≤ A.trace :=
  (HermitianMat.zero_le_iff.mp hA).frobenius_norm_le_re_trace

lemma HermitianMat.summable_of_summable_trace
    {α : Type*} (f : α → HermitianMat ι 𝕜) (hf_pos : ∀ a, 0 ≤ f a)
    (hf_tr : Summable (fun a ↦ (f a).trace)) :
    Summable f :=
  .of_norm_bounded hf_tr fun a ↦ HermitianMat.norm_le_trace (hf_pos a)

end norms
