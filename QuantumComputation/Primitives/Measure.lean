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

public import QuantumComputation.Maths.LinearAlgebra
public import QuantumComputation.Maths.Observable

/-!
# Computational-basis measurement primitive

This module defines computational-basis projectors and packages them as a measurement.
-/

@[expose] public section

open Operator
open scoped Matrix MatrixOrder ComplexOrder

variable {d : ℕ}

/-- Computational-basis projector `|o⟩⟨o|`. -/
def compProj (o : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.single o o 1

lemma compProj_apply (o i j : Fin d) :
    compProj o i j = if i = o ∧ j = o then 1 else 0 := by
  simp only [compProj, Matrix.single_apply]
  refine if_congr ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩ rfl rfl

/-- Computational-basis projectors are diagonal matrices. -/
lemma compProj_eq_diagonal (o : Fin d) :
    compProj o = Matrix.diagonal (fun i ↦ if i = o then 1 else 0) := by
  ext i j
  by_cases hi : i = o <;> by_cases hj : j = o <;>
    simp_all [compProj_apply, Matrix.diagonal_apply, eq_comm]

@[simp]
lemma compProj_conjTranspose (o : Fin d) : (compProj o)ᴴ = compProj o := by
  simp [compProj, Matrix.conjTranspose_single]

lemma compProj_isHermitian (o : Fin d) : (compProj o).IsHermitian :=
  compProj_conjTranspose o

@[simp]
lemma compProj_mul_self (o : Fin d) : compProj o * compProj o = compProj o := by
  simp [compProj, Matrix.single_mul_single_same]

/-- The computational-basis projectors resolve the identity. -/
@[simp]
lemma compProj_sum : (∑ o : Fin d, compProj o) = 1 := by
  simp [compProj, Matrix.sum_single_one]

lemma compProj_mul (o₁ o₂ : Fin d) :
    compProj o₁ * compProj o₂ = if o₁ = o₂ then compProj o₁ else 0 := by
  by_cases h : o₁ = o₂ <;>
    simp [compProj, h, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne]

@[simp]
lemma compProj_mul_of_ne {o₁ o₂ : Fin d} (h : o₁ ≠ o₂) :
    compProj o₁ * compProj o₂ = 0 := by
  rw [compProj_mul, ite_eq_right h]

@[simp]
lemma compProj_mulVec (o : Fin d) (v : Fin d → ℂ) :
    compProj o *ᵥ v = Pi.single o (v o) := by
  simp [compProj, Matrix.single_mulVec_eq, ← Pi.single_smul']

lemma compProj_mulVec_single (o i : Fin d) (c : ℂ) :
    compProj o *ᵥ Pi.single i c = if o = i then Pi.single o c else 0 := by
  rw [compProj_mulVec]
  by_cases h : o = i <;> simp [h]

/-- Projecting on both sides retains just the selected diagonal entry. -/
lemma compProj_mul_mul (o : Fin d) (A : Matrix (Fin d) (Fin d) ℂ) :
    compProj o * A * compProj o = A o o • compProj o := by
  ext i j
  by_cases hi : i = o <;> simp [compProj_apply, Matrix.mul_apply, ite_and, hi]

/-- The complete projective measurement in the computational basis. -/
@[simps]
noncomputable def compCompleteMeasurement : CompleteMeasurement d d :=
  ⟨compProj, by simp⟩

/-- The projective measurement in the computational basis. -/
@[simps]
noncomputable def compMeasurement : Measurement d d :=
  ⟨compProj, by simp⟩

@[simp]
theorem compProj_nonneg (o : Fin d) : 0 ≤ compProj o := by
  simpa [Matrix.nonneg_iff_posSemidef] using Matrix.posSemidef_conjTranspose_mul_self (compProj o)

@[simp]
theorem compProj_le_one (o : Fin d) : compProj o ≤ 1 := by simpa using compMeasurement.le_one o

/-- Computational-basis projector `|o⟩⟨o|`, as an `Observable`. -/
abbrev compProjObs (o : Fin d) : Observable (Fin d) := .single o 1

/-- Pure-state observable `|ψ⟩⟨ψ|` for the state `|ψ⟩ = U |o⟩`. -/
abbrev pureStateObs (U : Unitary d) (o : Fin d) : Observable (Fin d) :=
  (compProjObs o).conjUnitary U

/-- The matrix of `pureStateObs U o` equals `pureStateDensity (U |o⟩)`. -/
theorem pureStateObs_eq_pureStateDensity (U : Unitary d) (o : Fin d) :
    (pureStateObs U o).1.mat = pureStateDensity (U.1 *ᵥ basisState o) := by
  rw [← matrix_conj_pureStateDensity]
  simp [pureStateObs, compProjObs, pureStateDensity,
    Matrix.single_eq_single_vecMulVec_single]

/-- Matrix entries of `pureStateObs U o` match the outer product `(U |o⟩)(U |o⟩)ᴴ`. -/
theorem pureStateObs_apply (U : Unitary d) (o : Fin d) (i j : Fin d) :
    (pureStateObs U o).1.mat i j =
      (U.1 *ᵥ basisState o) i *
        starRingEnd ℂ ((U.1 *ᵥ basisState o) j) := by
  simpa [pureStateDensity, Matrix.vecMulVec] using
    congr_fun₂ (pureStateObs_eq_pureStateDensity U o) i j

/-- Matrix entries after conjugating a computational-basis projector. -/
@[simp]
lemma conjTranspose_compProj_mul_apply (target : Fin d)
    (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (Mᴴ * compProj target * M) i j =
      starRingEnd ℂ (M target i) * M target j := by
  simp [Matrix.mul_apply, compProj_apply, ite_and]

/-- Applying `U` and keeping the computational-basis outcomes other than `target` maps an operator
with constant diagonal `a` to `a` times the effect `1 - Uᴴ |target⟩⟨target| U`. -/
lemma krausConj_compProj_mul_erase (U : Unitary d) (target : Fin d)
    (A : Matrix (Fin d) (Fin d) ℂ) {a : ℂ} (hA : ∀ o, A o o = a) :
    krausConj (fun o ↦ compProj o * U.1) (Finset.univ.erase target) A =
      a • (1 - U.1ᴴ * compProj target * U.1) := by
  have hunit : U.1ᴴ * U.1 = 1 := Matrix.UnitaryGroup.star_mul_self U
  rw [krausConj_mul_right, krausConj,
    Finset.sum_congr rfl fun o _ ↦ by rw [compProj_conjTranspose, compProj_mul_mul, hA],
    ← Finset.smul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _), compProj_sum]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_one, hunit]
