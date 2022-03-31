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

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Algebra.Star.Pi
public import QuantumInfo.ForMathlib.HermitianMat.Unitary

/-!
# Basic theorems about matrices

These can be upstreamed easily to mathlib.
-/

@[expose] public section


open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace

/-- A linear operator on a `d`-dimensional quantum state space, represented in the chosen basis.

Rows name output basis coordinates and columns name input basis coordinates.  For an `n`-qubit
system we normally use `Operator (2 ^ n)`.  An operator need not be unitary: projectors and
individual measurement Kraus operators are operators too. -/
abbrev Operator (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- The type of unitary matrices. -/
abbrev Operator.Unitary (n : ℕ) : Type := 𝐔[Fin n]

@[simp]
lemma Unitary.neg_mem_iff {α} [Ring α] [StarRing α] {x : α} : -x ∈ unitary α ↔ x ∈ unitary α := by
  simp [Unitary.mem_iff]

@[simp]
theorem default_subtype_eq {α} (y : α) : (default : { x : α // x = y }) = y := rfl

@[simp]
theorem default_subtype_eq' {α} (y : α) : (default : { x : α // y = x }) = y := rfl

namespace Matrix
variable {α m n p : Type*}

/-! ### Results about constant matrices. -/

@[simp]
theorem of_const_mul_of_const [Fintype n] [NonUnitalNonAssocSemiring α] (a b : α) :
    (.of fun _ _ => a : Matrix m n α) * (.of fun _ _ => b : Matrix n p α) =
        Fintype.card n • .of fun _ _ => a * b := by
  ext
  simp [Matrix.mul_apply]

theorem isIdempotentElem_of_const [Fintype n] [Semiring α] (k : α)
    (h_eq_one : Fintype.card n * k = 1) :
    IsIdempotentElem (Matrix.of fun _ _ ↦ k : Matrix n n α) := show _ = _ by
  simp [Matrix.of_const_mul_of_const, Pi.mul_def, ← mul_assoc]
  grind

theorem isSelfAdjoint_of_const [Star α] (k : α) (h : IsSelfAdjoint k) :
    IsSelfAdjoint (Matrix.of fun _ _ ↦ k : Matrix n n α) :=
  show _ = _ by ext; simp [h.star_eq]

theorem isStarProjection_of_const [Fintype n] [Semiring α] [StarRing α] (k : α)
    (h_eq_one : Fintype.card n * k = 1) (h2 : IsSelfAdjoint k) :
    IsStarProjection (Matrix.of fun _ _ ↦ k : Matrix n n α) where
  isIdempotentElem := isIdempotentElem_of_const _ h_eq_one
  isSelfAdjoint := isSelfAdjoint_of_const _ h2

/-- A more general version of `Matrix.PosSemidef.conjTranspose_mul_mul_same` without
`[Finite m]`. -/
lemma PosSemidef.conjTranspose_mul_mul_same' [Ring α] [PartialOrder α] [StarRing α] [Fintype n]
    {A : Matrix n n α} (hA : A.PosSemidef) (B : Matrix n m α) :
    (Bᴴ * A * B).PosSemidef := by
  refine ⟨isHermitian_conjTranspose_mul_mul B hA.1, fun x ↦ ?_⟩
  simpa only [Finsupp.sum, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, Finset.univ_eq_attach, mul_apply, conjTranspose_apply, submatrix_apply, id_eq,
    ← Finset.sum_attach x.support] using
    (hA.conjTranspose_mul_mul_same
      (B.submatrix id ((↑) : x.support → m))).dotProduct_mulVec_nonneg (fun i ↦ x i)

/-- A more general version of `Matrix.PosSemidef.mul_mul_conjTranspose_same` without
`[Finite m]`. -/
lemma PosSemidef.mul_mul_conjTranspose_same' [Ring α] [PartialOrder α] [StarRing α] [Fintype n]
    {A : Matrix n n α} (hA : A.PosSemidef) (B : Matrix m n α) :
    (B * A * Bᴴ).PosSemidef := by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same' Bᴴ

/-- A more general version of `Matrix.PosSemidef.mul_mul_conjTranspose_mono` without
`[Fintype m]`. -/
lemma PosSemidef.mul_mul_conjTranspose_mono' {𝕜 : Type*} [RCLike 𝕜] [Fintype n]
    {A B : Matrix n n 𝕜} (C : Matrix m n 𝕜) (hAB : A ≤ B) :
    C * A * Cᴴ ≤ C * B * Cᴴ := by
  rw [Matrix.le_iff, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact (Matrix.le_iff.mp hAB).mul_mul_conjTranspose_same' C

theorem mul_conjTranspose_self_mul_le_one {𝕜 : Type*} [RCLike 𝕜]
    [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n]
    {A : Matrix m n 𝕜} {B : Matrix n p 𝕜}
    (hA : A * Aᴴ ≤ 1) (hB : B * Bᴴ ≤ 1) :
    (A * B) * (A * B)ᴴ ≤ 1 :=
  calc (A * B) * (A * B)ᴴ
    _ = A * (B * Bᴴ) * Aᴴ := by simp [Matrix.mul_assoc]
    _ ≤ A * 1 * Aᴴ := PosSemidef.mul_mul_conjTranspose_mono' A hB
    _ ≤ 1 := by simpa using hA

theorem conjTranspose_mul_self_mul_le_one {𝕜 : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq p]
    {A : Matrix m n 𝕜} {B : Matrix n p 𝕜}
    (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1) :
    (A * B)ᴴ * (A * B) ≤ 1 := by
  simpa using mul_conjTranspose_self_mul_le_one (A := Bᴴ) (B := Aᴴ)
    (by simpa using hB) (by simpa using hA)

end Matrix

namespace HermitianMat

instance {n α : Type*} [AddGroup α] [StarAddMonoid α] [IsEmpty n] :
    Subsingleton (HermitianMat n α) where
  allEq _ _ := Subtype.ext <| Subsingleton.elim _ _

instance {m R : Type*} [AddGroup R] [StarAddMonoid R] [TopologicalSpace R] [T2Space R] :
    T2Space (HermitianMat m R) :=
  inferInstanceAs <| T2Space (selfAdjoint (Matrix m m R))

@[simp, nontriviality]
theorem trace_of_isEmpty {R n α : Type*} [Star R] [TrivialStar R] [Fintype n] [IsEmpty n]
    [Ring α] [StarAddMonoid α] [CommSemiring R] [Algebra R α] [IsMaximalSelfAdjoint R α]
    (A : HermitianMat n α) : A.trace = 0 := by
  simp [Subsingleton.elim A 0]

@[simp]
theorem trace_sum {ι n : Type*} [Fintype n] (s : Finset ι)
    (f : ι → HermitianMat n ℂ) :
    (∑ i ∈ s, f i).trace = ∑ i ∈ s, (f i).trace :=
  map_sum (AddMonoidHom.mk' HermitianMat.trace HermitianMat.trace_add) f s

section diagonal
variable {n 𝕜 : Type*} [DecidableEq n] [RCLike 𝕜]

lemma smul_one_eq_diagonal (c : ℝ) : c • (1 : HermitianMat n 𝕜) = diagonal 𝕜 (fun _ => c) := by
  ext : 1; simp [← Matrix.smul_one_eq_diagonal]

@[simp]
lemma diagonal_eq_zero {f : n → ℝ} : diagonal 𝕜 f = 0 ↔ f = 0 := by
  simp [HermitianMat.ext_iff, funext_iff]

@[simp]
lemma diagonal_eq_one {f : n → ℝ} : diagonal 𝕜 f = 1 ↔ f = 1 := by
  simp [HermitianMat.ext_iff, funext_iff]

@[simp, gcongr]
lemma diagonal_le_diagonal {f g : n → ℝ} : diagonal 𝕜 f ≤ diagonal 𝕜 g ↔ f ≤ g := by
  rw [HermitianMat.le_iff, ← diagonal_sub, diagonal_mat, Matrix.posSemidef_diagonal_iff]
  simp [Pi.le_def, sub_nonneg]

@[simp]
lemma diagonal_nonneg {f : n → ℝ} : 0 ≤ diagonal 𝕜 f ↔ 0 ≤ f := by
  rw [← diagonal_zero, diagonal_le_diagonal]

end diagonal

section single
variable {n : Type*} [DecidableEq n]

/-- The Hermitian matrix `r |i⟩⟨i|` with a single real diagonal entry `r` at `(i, i)`. -/
def single (i : n) (r : ℝ) : HermitianMat n ℂ :=
  ⟨Matrix.single i i (r : ℂ), by
    simp [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single,
      RCLike.star_def]⟩

@[simp] lemma single_mat (i : n) (r : ℝ) : (single i r).mat = Matrix.single i i (r : ℂ) := rfl

@[simp] lemma single_val (i : n) (r : ℝ) : (single i r).1 = Matrix.single i i (r : ℂ) := rfl

theorem diagonal_single (i : n) (r : ℝ) : diagonal ℂ (Pi.single i r) = single i r := by
  ext1
  rw [diagonal_mat, single_mat, ← Matrix.diagonal_single, ← RCLike.ofReal_eq_complex_ofReal]
  congr with j
  grind

@[simp] theorem single_zero (i : n) : single i 0 = 0 := by ext; simp [single]

theorem single_add (i : n) (r s : ℝ) : single i (r + s) = single i r + single i s := by
  ext : 1
  simp [Matrix.single_add]

theorem single_sub (i : n) (r s : ℝ) : single i (r - s) = single i r - single i s := by
  ext : 1
  simp [Matrix.single_neg, Matrix.single_add, sub_eq_add_neg]

@[simp]
lemma trace_single [Fintype n] (i : n) (r : ℝ) : (single i r).trace = r := by
  simp [HermitianMat.trace_eq_re_trace]

lemma single_nonneg (i : n) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ single i r := by
  grw [← diagonal_single, diagonal_nonneg, Pi.single_nonneg, hr]

@[simp, gcongr]
lemma single_le_single {i : n} {r s : ℝ} : single i r ≤ single i s ↔ r ≤ s := by
  rw [← diagonal_single, ← diagonal_single, diagonal_le_diagonal, Pi.single_le_single]

lemma single_le_one (i : n) {r : ℝ} (hr : r ≤ 1) : single i r ≤ 1 := by
  rw [← diagonal_single, ← diagonal_one, diagonal_le_diagonal]
  intro j
  rcases eq_or_ne j i with rfl | hj
  · simp only [Pi.single_eq_same]
    exact_mod_cast hr
  · simp [hj]

end single

theorem inner_conj_left {n m : Type*} [Fintype n] [Fintype m]
    (A : HermitianMat n ℂ) (B : HermitianMat m ℂ) (M : Matrix m n ℂ) :
    ⟪A.conj M, B⟫_ℝ = ⟪A, B.conj Mᴴ⟫_ℝ := by
  simp only [HermitianMat.inner_eq_re_trace, HermitianMat.conj_apply_mat,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

/-- A more general version of `HermitianMat.conj_mono` without `[Fintype m]`. -/
@[gcongr]
lemma conj_mono' {𝕜 m n : Type*} [RCLike 𝕜] [Fintype n]
    {A B : HermitianMat n 𝕜} {M : Matrix m n 𝕜} (h : A ≤ B) :
    A.conj M ≤ B.conj M :=
  Matrix.PosSemidef.mul_mul_conjTranspose_mono' M h

/-- A more general version of `HermitianMat.conj_nonneg` without `[Fintype m]`. -/
theorem conj_nonneg' {𝕜 m n : Type*} [RCLike 𝕜] [Fintype n]
    {A : HermitianMat n 𝕜} (M : Matrix m n 𝕜) (hA : 0 ≤ A) :
    0 ≤ A.conj M := by
  simpa using conj_mono' (M := M) hA

lemma conj_one_le_one {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype n]
    (M : Matrix m n ℂ) (hM : M * Mᴴ ≤ 1) :
    (1 : HermitianMat n ℂ).conj M ≤ 1 := by
  rw [HermitianMat.le_iff, HermitianMat.mat_sub, HermitianMat.mat_one, HermitianMat.conj_apply_mat,
    HermitianMat.mat_one, Matrix.mul_one]
  exact hM

@[gcongr]
theorem trace_mono {n : Type*} [Fintype n] {A B : HermitianMat n ℂ} (h : A ≤ B) :
    A.trace ≤ B.trace := by
  have h1 : 0 ≤ B - A := sub_nonneg.mpr h
  have h2 : 0 ≤ (B - A).trace := HermitianMat.trace_nonneg h1
  rw [HermitianMat.trace_sub] at h2
  exact sub_nonneg.mp h2

lemma trace_conj_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) (hM : Mᴴ * M ≤ 1) {A : HermitianMat n ℂ} (hA : 0 ≤ A) :
    (A.conj M).trace ≤ A.trace := by
  classical
  rw [← HermitianMat.inner_one (A.conj M), HermitianMat.inner_conj_left,
    ← HermitianMat.inner_one A]
  exact HermitianMat.inner_mono hA (HermitianMat.conj_one_le_one Mᴴ (by simpa using hM))

@[fun_prop]
lemma continuous_trace {n : Type*} [Fintype n] :
    Continuous (HermitianMat.trace (α := ℂ) (n := n)) :=
  RCLike.continuous_re.comp HermitianMat.continuous_mat.matrix_trace

/-- conj is continuous in its right argument. -/
@[fun_prop]
lemma continuous_conj_right {α m n : Type*} [CommRing α] [StarRing α] [Fintype n]
    [TopologicalSpace α] [IsTopologicalRing α] (B : Matrix m n α) :
    Continuous (HermitianMat.conj B) := by
  suffices Continuous (fun A : HermitianMat _ α ↦ B * A.mat * Bᴴ) by
    exact this.subtype_mk _
  fun_prop

end HermitianMat

@[simp]
theorem unitInterval.toNNReal_mk (x : ℝ) (hx : x ∈ Set.Icc _ _) :
    unitInterval.toNNReal ⟨x, hx⟩ = NNReal.mk x hx.1 := rfl

@[fun_prop]
theorem Continuous.nnRealMk {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (h : Continuous f) (hf : ∀ x, 0 ≤ f x) : Continuous fun x ↦ NNReal.mk (f x) (hf x) :=
  .subtype_mk h _

@[gcongr]
theorem NNReal.mk_le_mk {a b : ℝ} {ha : 0 ≤ a} {hb : 0 ≤ b} :
    NNReal.mk a ha ≤ NNReal.mk b hb ↔ a ≤ b :=
  Iff.rfl
