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

/-!
# Grover operators

This module defines the marked-state phase oracle and Grover diffuser.
-/

@[expose] public section

open Operator

namespace Grover

variable {n : ℕ}

local notation "d" => 2 ^ n
open scoped Matrix

/-- Oracle phase flip: `- 1` on the marked basis state and `1` elsewhere. -/
def oracleMatrix (target : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i ↦ if i = target then -1 else 1)

@[simps]
noncomputable def oracleUnitary (target : Fin d) : Unitary d :=
  ⟨oracleMatrix target, by
    rw [oracleMatrix, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    split <;> simp⟩

/-- Diffuser `2|+⟩⟨+| - I`. -/
noncomputable def diffuserMatrix : Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.of fun _ _ ↦ 2 / d) - 1

/-- `diffuserMatrix` as a unitary matrix. -/
@[simps]
noncomputable def diffuserUnitary : Unitary d :=
  ⟨diffuserMatrix, by
    convert
        (Matrix.isStarProjection_of_const (n := Fin d) (d⁻¹ : ℂ) _ _).two_mul_sub_one_mem_unitary
    · rw [diffuserMatrix, ← smul_eq_mul, ofNat_smul_eq_nsmul]
      ext; simp; field_simp
    · simp
    · simp [IsSelfAdjoint]⟩

@[simp]
lemma oracleMatrix_conjTranspose_mul_self (target : Fin d) :
    (oracleMatrix target)ᴴ * oracleMatrix target = 1 :=
  Matrix.UnitaryGroup.star_mul_self (oracleUnitary target)

@[simp]
lemma diffuserMatrix_conjTranspose_mul_self : (diffuserMatrix (n := n))ᴴ * diffuserMatrix = 1 :=
  Matrix.UnitaryGroup.star_mul_self diffuserUnitary

/-- The Grover diffuser is not the oracle, for every number of qubits and every target. -/
theorem diffuserMatrix_ne_oracleMatrix (target : Fin d) :
    diffuserMatrix (n := n) ≠ oracleMatrix target := by
  intro heq
  cases n with
  | zero =>
      obtain rfl : target = 0 := Fin.ext (by omega)
      have h := congr($heq 0 0)
      norm_num [diffuserMatrix, oracleMatrix] at h
  | succ n =>
      have h := congr($heq 0 1)
      simp [diffuserMatrix, oracleMatrix] at h

theorem diffuserUnitary_ne_oracleUnitary (target : Fin d) :
    diffuserUnitary (n := n) ≠ oracleUnitary target :=
  fun h ↦ diffuserMatrix_ne_oracleMatrix target congr(($h).1)

end Grover
