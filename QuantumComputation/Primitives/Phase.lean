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

public import Mathlib.Analysis.Complex.Exponential
public import QuantumInfo.ForMathlib.HermitianMat.Unitary
import Mathlib.Analysis.SpecialFunctions.Exponential
import QuantumComputation.Maths.Matrix

/-!
# Diagonal phase primitive

This module defines diagonal phase matrices with entries `exp(2πi f(j))` and packages them as
unitary operators.
-/

@[expose] public section

open scoped Matrix Real

lemma Complex.exp_two_pi_I_mem_unitary (x : ℝ) :
    Complex.exp (2 * π * Complex.I * (x : ℂ)) ∈ unitary ℂ := by
  simp [Complex.exp_eq_exp_ℂ, skewAdjoint.mem_iff, NormedSpace.exp_mem_unitary_of_mem_skewAdjoint]

variable {ι : Type*} [DecidableEq ι]

/-- Diagonal phase matrix with diagonal entries `exp(2πi f(j))`. -/
noncomputable def diagPhaseMatrix (f : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun j ↦ Complex.exp (2 * π * Complex.I * (f j : ℂ)))

variable [Fintype ι]

lemma diagPhaseMatrix_mem_unitaryGroup (f : ι → ℝ) :
    diagPhaseMatrix f ∈ Matrix.unitaryGroup ι ℂ := by
  rw [diagPhaseMatrix, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  intro i
  exact Complex.exp_two_pi_I_mem_unitary _

/-- Unitary operator for a diagonal phase gate. -/
@[simps]
noncomputable def diagPhaseUnitary (f : ι → ℝ) : 𝐔[ι] :=
  ⟨diagPhaseMatrix f, diagPhaseMatrix_mem_unitaryGroup f⟩
