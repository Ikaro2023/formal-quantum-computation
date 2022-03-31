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

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import QuantumInfo.ForMathlib.HermitianMat.Unitary
public import QuantumInfo.ForMathlib.Isometry
public import QuantumComputation.Maths.Matrix

/-!
# Miscellaneous results and aliases in Linear Algebra
-/

@[expose] public section

open scoped Matrix

/-- The state space of a quantum system. This is a Hilbert Space of dimension `d`.
This is isomorphic to `ℂ^d`, the complex inner product space of dimension `d`. -/
abbrev StateSpace (d : ℕ) : Type := EuclideanSpace ℂ (Fin d)

@[inherit_doc] notation "ℋ" => StateSpace

/-- An unbundled pure-state amplitude vector for `n` qubits. -/
abbrev StateVector (n : ℕ) := Fin (2 ^ n) → ℂ

/-- A computational-basis state `|index⟩` with amplitude `1` at `index` and `0` elsewhere. -/
abbrev basisState {α : Type*} [DecidableEq α] (index : α) : α → ℂ :=
  Pi.single index 1

theorem complex_one_div_sqrt_mul_self (x : ℝ) (hx : 0 ≤ x) :
    (1 / √x : ℂ) * (1 / √x : ℂ) = (x : ℂ)⁻¹ := by
  norm_cast
  rw [one_div_mul_one_div, ← pow_two, Real.sq_sqrt hx]
  simp [one_div]

/-- Matrix-vector multiplication distributes over a finite linear combination. -/
theorem Matrix.mulVec_sum_smul {Rows Columns Index : Type*}
    [Fintype Columns] [Fintype Index]
    (A : Matrix Rows Columns ℂ) (coefficient : Index → ℂ)
    (state : Index → Columns → ℂ) :
    A *ᵥ (∑ index, coefficient index • state index) =
      ∑ index, coefficient index • A *ᵥ state index := by
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [Matrix.mulVec_smul]

/-- Conjugating by `K * U` is conjugating by `K` and then by `U`. -/
theorem Matrix.conjTranspose_mul_mul_mul {n α : Type*} [Fintype n] [CommSemiring α] [StarRing α]
    (K A U : Matrix n n α) : (K * U)ᴴ * A * (K * U) = Uᴴ * (Kᴴ * A * K) * U := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Conjugating by Kraus operators `K o * U` is conjugating by `K o` and then by `U`. -/
theorem Matrix.sum_conjTranspose_mul_mul_mul {ι n α : Type*} [Fintype n] [CommSemiring α]
    [StarRing α] (s : Finset ι) (K A : ι → Matrix n n α) (U : Matrix n n α) :
    ∑ o ∈ s, (K o * U)ᴴ * A o * (K o * U) = Uᴴ * (∑ o ∈ s, (K o)ᴴ * A o * K o) * U := by
  simp only [Matrix.conjTranspose_mul_mul_mul, Finset.mul_sum, Finset.sum_mul]

/-- Conjugating by `M ^ (k + 1)` is conjugating by `M ^ k` and then by `M`. -/
theorem Matrix.conjTranspose_pow_succ_mul_mul_pow_succ {n α : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring α] [StarRing α] (M A : Matrix n n α) (k : ℕ) :
    (M ^ (k + 1))ᴴ * A * M ^ (k + 1) = Mᴴ * ((M ^ k)ᴴ * A * M ^ k) * M := by
  rw [pow_succ, Matrix.conjTranspose_mul_mul_mul]

/-- Kraus operators `K o` forming a complete measurement, followed by a unitary `U`, again form a
complete measurement. -/
theorem Matrix.sum_mul_conjTranspose_mul_mul_eq_one {ι n α : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] [CommSemiring α] [StarRing α] (K : ι → Matrix n n α) (U : Matrix n n α)
    (hK : ∑ o, (K o)ᴴ * K o = 1) (hU : Uᴴ * U = 1) :
    ∑ o, (K o * U)ᴴ * (K o * U) = 1 := by
  simpa [hK, hU] using Matrix.sum_conjTranspose_mul_mul_mul Finset.univ K (fun _ ↦ 1) U

/-- Rank-one density matrix `|ψ⟩⟨ψ|` associated with a (possibly unnormalized) state
vector.  Unnormalized vectors represent measurement branches whose trace is their probability. -/
noncomputable def pureStateDensity {d : ℕ} (ψ : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  .vecMulVec ψ (star ψ)

/-- Applying a matrix to a pure vector and applying the corresponding density-matrix
transformation are exactly the same semantics. -/
theorem matrix_conj_pureStateDensity {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) :
    M * pureStateDensity ψ * Mᴴ = pureStateDensity (M *ᵥ ψ) := by
  rw [pureStateDensity, pureStateDensity, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec]

/-- The trace of an unnormalized pure density matrix is the vector's squared norm, hence the Born
probability of that branch. -/
theorem trace_pureStateDensity {d : ℕ} (ψ : Fin d → ℂ) :
    Matrix.trace (pureStateDensity ψ) =
      ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) := by
  simp [pureStateDensity, dotProduct, Complex.normSq_eq_conj_mul_self, mul_comm]

/-- A unitary matrix preserves the total squared norm of every (possibly unnormalized) vector. -/
theorem sum_normSq_unitary_mulVec {d : ℕ} (U : 𝐔[Fin d])
    (ψ : Fin d → ℂ) :
    (∑ i, Complex.normSq ((U.1 *ᵥ ψ) i)) = ∑ i, Complex.normSq (ψ i) := by
  have hunit : U.1ᴴ * U.1 = 1 := by
    have h := U.2.1
    rw [← Matrix.star_eq_conjTranspose]
    exact h
  have hcomplex :
      ((∑ i, Complex.normSq ((U.1 *ᵥ ψ) i) : ℝ) : ℂ) =
        ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) := by
    calc
      ((∑ i, Complex.normSq ((U.1 *ᵥ ψ) i) : ℝ) : ℂ) =
          Matrix.trace (pureStateDensity (U.1 *ᵥ ψ)) :=
        (trace_pureStateDensity _).symm
      _ = Matrix.trace (U.1 * pureStateDensity ψ * U.1ᴴ) := by
        rw [matrix_conj_pureStateDensity]
      _ = Matrix.trace (U.1ᴴ * U.1 * pureStateDensity ψ) :=
        Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (pureStateDensity ψ) := by rw [hunit, one_mul]
      _ = ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) := trace_pureStateDensity _
  exact_mod_cast hcomplex

@[simp]
theorem complex_inv_sqrt_two_mul_self :
    (√2 : ℂ)⁻¹ * (√2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [show (√2 : ℂ)⁻¹ = 1 / √2 by simp]
  exact complex_one_div_sqrt_mul_self 2 (by norm_num)

namespace Operator

open Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

/-- Package a permutation as the unitary with forward basis action `|x⟩ ↦ |e x⟩`.

This uses the inverse permutation matrix because `Matrix.permMatrix` acts on amplitude vectors by
precomposition. -/
def permutationUnitary {d : ℕ} (e : Equiv.Perm (Fin d)) : Unitary d :=
  ⟨Equiv.Perm.permMatrix ℂ (e⁻¹), Equiv.Perm.permMatrix_mem_unitaryGroup (e⁻¹)⟩

@[simp]
theorem permutationUnitary_smul_col {d : ℕ}
    (e : Equiv.Perm (Fin d)) (index : Fin d) (r : ℂ) :
    r • (permutationUnitary e).1.col index = Pi.single (e index) r := by
  rw [← op_smul_eq_smul, ← Matrix.mulVec_single]
  change (e⁻¹).permMatrix ℂ *ᵥ Pi.single index r = _
  rw [Matrix.permMatrix_mulVec]
  ext output
  simp [Pi.single_apply, Equiv.symm_apply_eq]

theorem permutationUnitary_mulVec_single {d : ℕ}
    (e : Equiv.Perm (Fin d)) (index : Fin d) (r : ℂ) :
    (permutationUnitary e).1 *ᵥ Pi.single index r =
      Pi.single (e index) r := by
  rw [Matrix.mulVec_single, op_smul_eq_smul, permutationUnitary_smul_col]

@[simp]
theorem permutationUnitary_swap_mul_self {d : ℕ} (i j : Fin d) :
    permutationUnitary (Equiv.swap i j) * permutationUnitary (Equiv.swap i j) = 1 := by
  apply Subtype.ext
  simp [permutationUnitary, ← Matrix.permMatrix_mul]

/-- If `A` dominates `B - q ^ n • R` in the Loewner order for every `n`, where
`0 ≤ q < 1`, then it dominates the limit `B`. -/
lemma hermitian_le_of_geometric_sub_smul_le {d : ℕ}
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (R B A : HermitianMat (Fin d) ℂ)
    (h : ∀ n : ℕ, B - q ^ n • R ≤ A) : B ≤ A := by
  have hpow : Filter.Tendsto (fun n : ℕ ↦ q ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hcorr : Filter.Tendsto (fun n : ℕ ↦ q ^ n • R)
      Filter.atTop (nhds ((0 : ℝ) • R)) :=
    hpow.smul_const R
  have ht : Filter.Tendsto
      (fun n : ℕ ↦ B - q ^ n • R)
      Filter.atTop (nhds (B - (0 : ℝ) • R)) :=
    tendsto_const_nhds.sub hcorr
  have hle := le_of_tendsto ht (Filter.Eventually.of_forall h)
  simpa using hle

/-- A finite quantum measurement with `i` labelled outcomes on a `d`-dimensional system.

It is a family of Kraus operators `M o`.  The condition
`∑ o, (M o)† * M o ≤ I` says the total probability of all outcomes cannot exceed the input
state's weight.  Ordinary complete measurements satisfy equality; the weaker condition also
allows trace-decreasing operations used by the QHL semantics.  In branch `o`, QHL updates a
density operator `ρ` to `M o * ρ * (M o)†`. -/
def Measurement (d : ℕ) (i : ℕ) : Type :=
  {M : Fin i → Operator d // ∑ o : Fin i, (M o)ᴴ * (M o) ≤ 1}

/-- A variant of `Measurement` with the inequality tightened to an equality, such that the
measurement preserves the states's weight.

See `Basic.CQState.trace_qMeasurement_of_complete` for this property. -/
def CompleteMeasurement (d : ℕ) (i : ℕ) : Type :=
  {M : Fin i → Operator d // ∑ o : Fin i, (M o)ᴴ * (M o) = 1}

/-- Forget the completeness of a measurement. -/
@[coe, simps (attr := simp, norm_cast)]
def CompleteMeasurement.toMeasurement {d i : ℕ} (measurement : CompleteMeasurement d i) :
    Measurement d i :=
  ⟨measurement.1, le_of_eq measurement.2⟩

instance {d i : ℕ} : Coe (CompleteMeasurement d i) (Measurement d i) :=
  ⟨CompleteMeasurement.toMeasurement⟩

lemma Measurement.le_one {d i : ℕ} (ℳ : Measurement d i) (o : Fin i) :
    (ℳ.1 o)ᴴ * (ℳ.1 o) ≤ 1 := by
  have h_pos : ∀ j : Fin i, 0 ≤ ((ℳ.1 j)ᴴ * (ℳ.1 j)) := fun j ↦ by
    change ((ℳ.1 j)ᴴ * (ℳ.1 j) - 0).PosSemidef
    rw [sub_zero]
    exact Matrix.posSemidef_conjTranspose_mul_self (ℳ.1 j)
  have h_single : (ℳ.1 o)ᴴ * (ℳ.1 o) ≤ ∑ j, (ℳ.1 j)ᴴ * (ℳ.1 j) :=
    Finset.single_le_sum (fun j _ ↦ h_pos j) (Finset.mem_univ o)
  exact h_single.trans ℳ.2

lemma Measurement.sum_conj_one_le_one {d i : ℕ} (ℳ : Measurement d i) :
    (∑ o : Fin i, (1 : HermitianMat (Fin d) ℂ).conj (ℳ.1 o)ᴴ) ≤ 1 := by
  rw [HermitianMat.le_iff, HermitianMat.mat_sub, HermitianMat.mat_one, HermitianMat.mat_finset_sum]
  simp only [HermitianMat.conj_apply_mat, HermitianMat.mat_one, mul_one,
    Matrix.conjTranspose_conjTranspose]
  exact ℳ.2

lemma Measurement.sum_conj_le_one {d i : ℕ} (ℳ : Measurement d i)
    {A : Fin i → HermitianMat (Fin d) ℂ} (hA : ∀ o, A o ≤ 1) :
    (∑ o : Fin i, (A o).conj (ℳ.1 o)ᴴ) ≤ 1 :=
  (Finset.sum_le_sum fun o _ ↦ HermitianMat.conj_mono (hA o)).trans ℳ.sum_conj_one_le_one

lemma Measurement.sum_trace_conj_le {d i : ℕ} (ℳ : Measurement d i)
    {A : HermitianMat (Fin d) ℂ} (hA : 0 ≤ A) :
    (∑ o : Fin i, (A.conj (ℳ.1 o)).trace) ≤ A.trace := by
  simp_rw [← HermitianMat.inner_one (A.conj _), HermitianMat.inner_conj_left]
  rw [← inner_sum, ← HermitianMat.inner_one A]
  exact HermitianMat.inner_mono hA ℳ.sum_conj_one_le_one

@[simp]
lemma CompleteMeasurement.sum_conj_one {d i : ℕ} (ℳ : CompleteMeasurement d i) :
    ∑ i, conj (ℳ.1 i)ᴴ 1 = 1 := by
  ext : 1
  erw [HermitianMat.mat_finset_sum]
  simpa using ℳ.2

lemma CompleteMeasurement.sum_trace_conj
    {d i : ℕ} (ℳ : CompleteMeasurement d i) {A : HermitianMat (Fin d) ℂ} :
    (∑ o : Fin i, (A.conj (ℳ.1 o)).trace) = A.trace := by
  simp_rw [← HermitianMat.inner_one (A.conj _), HermitianMat.inner_conj_left]
  simp_rw [← inner_sum, ← HermitianMat.inner_one A, CompleteMeasurement.sum_conj_one]

/-- Heisenberg-picture action `A ↦ ∑ o ∈ s, (L o)ᴴ * A * L o` of the Kraus operators `L o` with
`o ∈ s`. -/
noncomputable def krausConj {d i : ℕ} (L : Fin i → Operator d) (s : Finset (Fin i))
    (A : Operator d) : Operator d :=
  ∑ o ∈ s, (L o)ᴴ * A * L o

/-- A Kraus sum whose middle factors are `A` on `s` and `0` off `s` is `krausConj L s A`. -/
lemma sum_conj_eq_krausConj {d i : ℕ} (L : Fin i → Operator d) (s : Finset (Fin i))
    {B : Fin i → Operator d} {A : Operator d} (hs : ∀ o ∈ s, B o = A)
    (hsc : ∀ o ∉ s, B o = 0) :
    ∑ o, (L o)ᴴ * B o * L o = krausConj L s A := by
  rw [krausConj, ← Finset.sum_subset s.subset_univ fun o _ ho ↦ by simp [hsc o ho]]
  exact Finset.sum_congr rfl fun o ho ↦ by rw [hs o ho]

/-- For complete Kraus operators, a Kraus sum whose middle factors are `1 - A` on `s`, and act as
`1` off `s`, is `1 - krausConj L s A`. -/
lemma sum_conj_eq_one_sub_krausConj {d i : ℕ} {L : Fin i → Operator d} (s : Finset (Fin i))
    {B : Fin i → Operator d} {A : Operator d} (hL : ∑ o, (L o)ᴴ * L o = 1)
    (hs : ∀ o ∈ s, B o = 1 - A) (hsc : ∀ o ∉ s, (L o)ᴴ * B o * L o = (L o)ᴴ * L o) :
    ∑ o, (L o)ᴴ * B o * L o = 1 - krausConj L s A := by
  have h (o : Fin i) :
      (L o)ᴴ * B o * L o = (L o)ᴴ * L o - (L o)ᴴ * (if o ∈ s then A else 0) * L o := by
    split_ifs with ho
    · rw [hs o ho, mul_sub, sub_mul, mul_one]
    · rw [hsc o ho, mul_zero, zero_mul, sub_zero]
  rw [Finset.sum_congr rfl fun o _ ↦ h o, Finset.sum_sub_distrib, hL,
    sum_conj_eq_krausConj (A := A) L s (fun o ho ↦ by simp [ho]) fun o ho ↦ by simp [ho]]

lemma krausConj_mul_right {d i : ℕ} (K : Fin i → Operator d) (U : Operator d)
    (s : Finset (Fin i)) (A : Operator d) :
    krausConj (fun o ↦ K o * U) s A = Uᴴ * krausConj K s A * U :=
  Matrix.sum_conjTranspose_mul_mul_mul s K (fun _ ↦ A) U

/-- The matrix unit `|i⟩⟨0|`. -/
def elementaryMatrix {d : ℕ} [NeZero d] (i : Fin d) : Operator d := Matrix.single i 0 1

lemma elementaryMatrix_apply {d : ℕ} [NeZero d] (i i' j' : Fin d) :
    elementaryMatrix i i' j' = if i' = i ∧ j' = 0 then 1 else 0 := by
  simp only [elementaryMatrix, Matrix.single_apply]
  refine if_congr ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl

@[simp]
lemma conjTranspose_elementaryMatrix_mulVec {d : ℕ} [NeZero d] (o : Fin d) (v : Fin d → ℂ) :
    (elementaryMatrix o)ᴴ *ᵥ v = Pi.single 0 (v o) := by
  simp [elementaryMatrix, Matrix.conjTranspose_single, Matrix.single_mulVec_eq, ← Pi.single_smul']

/-- The Kraus operators `|0⟩⟨o| = (elementaryMatrix o)ᴴ` of quantum state reset as a complete
measurement. -/
@[simps]
def resetMeasurement {d : ℕ} [NeZero d] : CompleteMeasurement d d :=
  ⟨fun o ↦ (elementaryMatrix o)ᴴ, by
    simp [elementaryMatrix, Matrix.conjTranspose_single, Matrix.single_mul_single_same,
      Matrix.sum_single_one]⟩

lemma elementaryMatrix_mul_conjTranspose_le_one {d : ℕ} [NeZero d] (o : Fin d) :
    elementaryMatrix o * (elementaryMatrix o)ᴴ ≤ 1 := by
  simpa using resetMeasurement.toMeasurement.le_one o

lemma sum_conj_elementaryMatrix_le_one {d : ℕ} [NeZero d]
    {A : Fin d → HermitianMat (Fin d) ℂ} (hA : ∀ o, A o ≤ 1) :
    (∑ o : Fin d, (A o).conj (elementaryMatrix o)) ≤ 1 := by
  simpa using resetMeasurement.toMeasurement.sum_conj_le_one hA

/-- Conjugating by every matrix unit `E_o` collapses `A` to its `(0,0)` entry times `1`. -/
lemma sum_elementaryMatrix_mul_mul_conjTranspose {d : ℕ} [NeZero d]
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (∑ o : Fin d, elementaryMatrix o * A * (elementaryMatrix o)ᴴ) =
      A 0 0 • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simp only [elementaryMatrix, Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single,
    one_mul, mul_one, Matrix.sum_single_eq_diagonal]
  rw [Matrix.smul_one_eq_diagonal]

end Operator
