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

public import QuantumComputation.Maths.Matrix
public import QuantumComputation.Maths.OmegaCompletePartialOrder

/-!
# Partial density operators, with notation `𝒟 d`

This file provides `Operator.PartialDensityOperator d`.

## Main definitions

* `Operator.PartialDensityOperator`
* `Operator.PartialDensityOperator.trace`
* `Operator.PartialDensityOperator.single`
* `Operator.PartialDensityOperator.add`
* `Operator.PartialDensityOperator.sum`
* `Operator.PartialDensityOperator.conj`
* `Operator.PartialDensityOperator.instOmegaCompletePartialOrder`
-/

@[expose] public section

open scoped ComplexOrder Matrix MatrixOrder NNReal

namespace Operator

variable {d : Type*} [Fintype d]

variable (d) in
private def pdoSet : Set (HermitianMat d ℂ) :=
  {A | 0 ≤ A ∧ A.trace ≤ 1}

private lemma pdoSet_subset_Icc [DecidableEq d] : pdoSet d ⊆ Set.Icc 0 1 := fun _ hA ↦
  ⟨hA.1, (HermitianMat.le_trace_smul_one hA.1).trans <| by
    rw [HermitianMat.smul_one_eq_diagonal, ← HermitianMat.diagonal_one,
      HermitianMat.diagonal_le_diagonal]
    exact fun _ ↦ hA.2⟩

variable (d) in
private lemma pdoSet_isCompact : IsCompact (pdoSet d) := by
  have hclosed : IsClosed (pdoSet d) := by
    apply HermitianMat.isClosed_nonneg.inter
    exact isClosed_Iic.preimage HermitianMat.continuous_trace
  classical
  exact IsCompact.of_isClosed_subset HermitianMat.unitInterval_IsCompact hclosed pdoSet_subset_Icc

variable (d) in
/-- The type of partial density operators: Hermitian operators
which are positive and have trace less than or equal to `1`.

This has notation `𝒟` -/
noncomputable abbrev PartialDensityOperator : Type _ :=
  {B : HermitianMat d ℂ // 0 ≤ B ∧ B.trace ≤ 1}

@[inherit_doc]
notation "𝒟" => PartialDensityOperator

namespace PartialDensityOperator
variable {α : Type*} {d d' d'' : Type*}
variable [Fintype d] [Fintype d'] [Fintype d'']

/-- The zero in the type of partial density operator is the zero matrix. -/
noncomputable instance : Zero (𝒟 d) where
  zero := ⟨0, by simp⟩

instance : IsBotZeroClass (𝒟 d) where
  isBot_zero a := a.2.1

@[simp] theorem val_zero : (0 : 𝒟 d).1 = 0 := rfl

lemma trace_val_nonneg (A : 𝒟 d) : 0 ≤ A.1.trace :=
  HermitianMat.trace_nonneg A.2.1

lemma trace_val_le_one (A : 𝒟 d) : A.1.trace ≤ 1 :=
  A.2.2

/-- The trace of the operator, in `ℝ≥0`. -/
noncomputable def trace (A : 𝒟 d) : ℝ≥0 :=
  NNReal.mk A.val.trace A.trace_val_nonneg

@[simp]
theorem coe_trace (A : 𝒟 d) : (A.trace : ℝ) = A.val.trace := rfl

theorem trace_le_one (A : 𝒟 d) : A.trace ≤ 1 :=
  A.2.2

@[gcongr]
theorem trace_mono {A B : 𝒟 d} (h : A ≤ B) : A.trace ≤ B.trace :=
  HermitianMat.trace_mono h

@[simp]
theorem trace_zero : trace (0 : 𝒟 d) = 0 := by
  ext; simp

/-- The partial density operator `r |i⟩⟨i|` supported on a single computational basis state `i`,
for `0 ≤ r ≤ 1`. -/
@[simps]
noncomputable def single [DecidableEq d] (i : d) (r : unitInterval) : 𝒟 d :=
  ⟨HermitianMat.single i r, HermitianMat.single_nonneg i r.2.1, by simpa using r.2.2⟩

@[simp] theorem single_zero [DecidableEq d] (i : d) : single i 0 = 0 := by
  ext; simp

@[simp, gcongr] theorem single_le_single [DecidableEq d] {i : d} {r s : unitInterval} :
    single i r ≤ single i s ↔ r ≤ s :=
  HermitianMat.single_le_single

@[simp]
theorem trace_single [DecidableEq d] (i : d) (r : unitInterval) :
    trace (single i r) = unitInterval.toNNReal r := by
  ext; simp

/-- Add together two partial density operators, when the sum of the traces is less than one. -/
@[simps]
noncomputable def add (x y : 𝒟 d) (h_trace : x.trace + y.trace ≤ 1) : 𝒟 d :=
  ⟨x.1 + y.1, add_nonneg x.2.1 y.2.1, by rwa [HermitianMat.trace_add]⟩

@[gcongr]
theorem add_mono {x₁ y₁ x₂ y₂ : 𝒟 d}
    {h₁ : x₁.trace + y₁.trace ≤ 1} {h₂ : x₂.trace + y₂.trace ≤ 1}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    x₁.add y₁ h₁ ≤ x₂.add y₂ h₂ :=
  Subtype.coe_le_coe.mp <| add_le_add (Subtype.coe_le_coe.mpr hx) (Subtype.coe_le_coe.mpr hy)

@[simp]
theorem trace_add (x y : 𝒟 d) (h_trace : x.trace + y.trace ≤ 1) :
    (x.add y h_trace).trace = x.trace + y.trace := by
  ext; simp

/-- Sum a finite family of partial density operators, when the sum of the traces is at most one. -/
@[simps]
noncomputable def sum {ι : Type*} [Fintype ι] (x : ι → 𝒟 d) (h_trace : ∑ i, (x i).trace ≤ 1) :
    𝒟 d :=
  ⟨∑ i, (x i).1, Finset.sum_nonneg fun i _ ↦ (x i).2.1, by
    simpa using NNReal.coe_le_coe.mpr h_trace⟩

@[gcongr]
theorem sum_mono {ι : Type*} [Fintype ι] {x₁ x₂ : ι → 𝒟 d}
    {h₁ : ∑ i, (x₁ i).trace ≤ 1} {h₂ : ∑ i, (x₂ i).trace ≤ 1}
    (h : ∀ i, x₁ i ≤ x₂ i) :
    sum x₁ h₁ ≤ sum x₂ h₂ :=
  Subtype.coe_le_coe.mp <| Finset.sum_le_sum fun i _ ↦ Subtype.coe_le_coe.mpr (h i)

@[simp]
theorem trace_sum {ι : Type*} [Fintype ι] (x : ι → 𝒟 d)
    (h_trace : ∑ i, (x i).trace ≤ 1) :
    (sum x h_trace).trace = ∑ i, (x i).trace := by
  ext; simp

instance : CompactSpace (𝒟 d) :=
  isCompact_iff_compactSpace.mp (pdoSet_isCompact d)

/-- Partial density operators form an omega-complete partial order (Selinger). -/
noncomputable instance : OmegaCompletePartialOrder (𝒟 d) :=
  .ofCompactSpace

@[fun_prop]
theorem continuous_trace : Continuous (trace (d := d)) := by
  unfold trace
  fun_prop

theorem tendsto_trace_ωSup (c : OmegaCompletePartialOrder.Chain (𝒟 d)) :
    Filter.Tendsto (fun i ↦ (c i).trace) Filter.atTop
      (nhds (OmegaCompletePartialOrder.ωSup c).trace) :=
  (continuous_trace.tendsto _).comp (OmegaCompletePartialOrder.tendsto_ωSup c)

/-- Monotone convergence property for trace of chain suprema in `𝒟 d`. -/
theorem finsetSum_trace_ωSup_le (s : Finset α)
    (ch : α → OmegaCompletePartialOrder.Chain (𝒟 d)) (c : ℝ≥0)
    (h : ∀ i, ∑ a ∈ s, (ch a i).trace ≤ c) :
    ∑ a ∈ s, (OmegaCompletePartialOrder.ωSup (ch a)).trace ≤ c :=
  le_of_tendsto' (tendsto_finsetSum s fun a _ ↦ tendsto_trace_ωSup (ch a)) h

lemma posSemidef_val (D : 𝒟 d) : D.1.mat.PosSemidef :=
  HermitianMat.zero_le_iff.1 D.2.1

@[simp]
theorem trace_eq_zero {D : 𝒟 d} : D.trace = 0 ↔ D = 0 := by
  rw [← NNReal.coe_inj, coe_trace, NNReal.coe_zero, HermitianMat.trace_eq_zero_iff,
    D.posSemidef_val.trace_zero_iff, Subtype.ext_iff, HermitianMat.ext_iff]
  rfl

@[simp]
lemma support_trace (f : α → 𝒟 d) : (Function.support fun a ↦ (f a).trace) = f.support := by
  ext a
  simp

/-- Conjugate a partial density operator `ρ` by a contracting operator `M` (`Mᴴ * M ≤ 1`). -/
@[simps]
noncomputable def conj [DecidableEq d'] (M : Matrix d d' ℂ) (hM : Mᴴ * M ≤ 1) (ρ : 𝒟 d') : 𝒟 d :=
  ⟨HermitianMat.conj M ρ.1, ρ.1.conj_nonneg M ρ.2.1,
    (HermitianMat.trace_conj_le M hM ρ.2.1).trans ρ.trace_val_le_one⟩

theorem trace_conj_le [DecidableEq d'] (M : Matrix d d' ℂ) (hM : Mᴴ * M ≤ 1) (ρ : 𝒟 d') :
    (ρ.conj M hM).trace ≤ ρ.trace :=
  HermitianMat.trace_conj_le M hM ρ.2.1

@[simp]
theorem conj_one [DecidableEq d] (ρ : 𝒟 d) : ρ.conj 1 (by simp) = ρ :=
  Subtype.ext <| HermitianMat.conj_one _

@[simp]
theorem conj_conj [DecidableEq d'] [DecidableEq d''] (M : Matrix d' d'' ℂ) (N : Matrix d d' ℂ)
    (hM : Mᴴ * M ≤ 1) (hN : Nᴴ * N ≤ 1) (ρ : 𝒟 d'') :
    (ρ.conj M hM).conj N hN = ρ.conj (N * M) (Matrix.conjTranspose_mul_self_mul_le_one hN hM) :=
  Subtype.ext <| HermitianMat.conj_conj _ _ _

@[gcongr]
theorem conj_mono [DecidableEq d'] {M : Matrix d d' ℂ} {hM : Mᴴ * M ≤ 1}
    {ρ₁ ρ₂ : 𝒟 d'} (h : ρ₁ ≤ ρ₂) :
    ρ₁.conj M hM ≤ ρ₂.conj M hM :=
  HermitianMat.conj_mono h

end PartialDensityOperator

end Operator
