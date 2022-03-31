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

public import QuantumComputation.Registers.Assertions

/-!
# Resetting a selected register

For every old computational-basis value `o`, reset has the register-local Kraus operator
`|0><o|`, tensored with the identity on all unselected wires.  Every resulting quantum branch has
the selected register in `|0>`; the branch may also record its former value in a classical
variable.
-/

@[expose] public section

open Operator
open scoped Matrix MatrixOrder ComplexOrder QProg.Notation

namespace QRegister

variable {n k : ℕ}

/-- Whole-machine reset branch `|0⟩⟨outcome|` for one former value of the selected register. -/
noncomputable def resetKraus (register : QRegister k n)
    (outcome : Fin (2 ^ k)) : Operator (2 ^ n) :=
  register.embedMatrix (elementaryMatrix outcome)ᴴ

/-- A reset branch extracts the selected amplitude and places it at local basis value zero;
the environment factor is untouched. -/
theorem resetKraus_mulVec_tensorState (register : QRegister k n)
    (outcome : Fin (2 ^ k)) (localState : Fin (2 ^ k) → ℂ)
    (environmentState : (register.Environment → ZMod 2) → ℂ) :
    register.resetKraus outcome *ᵥ
        register.tensorState localState environmentState =
      register.tensorState (Pi.single 0 (localState outcome)) environmentState := by
  rw [resetKraus, register.embedMatrix_mulVec_tensorState,
    conjTranspose_elementaryMatrix_mulVec]

/-- Each reset branch has the same effect operator as measuring the corresponding old value. -/
@[simp]
theorem resetKraus_conjTranspose_mul (register : QRegister k n)
    (outcome : Fin (2 ^ k)) :
    (register.resetKraus outcome)ᴴ * register.resetKraus outcome =
      register.basisOutcomeProjector outcome := by
  rw [resetKraus, basisOutcomeProjector, ← register.embedMatrix_conjTranspose,
    ← register.embedMatrix_mul]
  simp [elementaryMatrix, compProj, Matrix.conjTranspose_single,
    Matrix.single_mul_single_same]

/-- Computational-basis reset of exactly the selected register.  Outcomes label the value that
was present before reset. -/
noncomputable def resetMeasurement (register : QRegister k n) :
    CompleteMeasurement (2 ^ n) (2 ^ k) :=
  register.embedCompleteMeasurement Operator.resetMeasurement

@[simp]
theorem resetMeasurement_apply (register : QRegister k n)
    (outcome : Fin (2 ^ k)) :
    register.resetMeasurement.1 outcome = register.resetKraus outcome := rfl

/-- Algebraic form of branch cleanliness: the zero projector fixes the range of every reset
Kraus operator. -/
theorem basisOutcomeProjector_zero_mul_resetKraus (register : QRegister k n)
    (outcome : Fin (2 ^ k)) :
    register.basisOutcomeProjector 0 * register.resetKraus outcome =
      register.resetKraus outcome := by
  rw [basisOutcomeProjector, resetKraus, ← register.embedMatrix_mul]
  simp [elementaryMatrix, compProj, Matrix.conjTranspose_single,
    Matrix.single_mul_single_same]

/-- Every pure-state reset branch is supported entirely on local basis value zero. -/
theorem resetKraus_isClean (register : QRegister k n)
    (outcome : Fin (2 ^ k)) (state : Fin (2 ^ n) → ℂ) :
    register.IsClean (register.resetKraus outcome *ᵥ state) := by
  rw [IsClean, HasBasisValue, Matrix.mulVec_mulVec,
    register.basisOutcomeProjector_zero_mul_resetKraus]

/-- The adjoint reset branch is likewise fixed by the zero projector on its right. -/
theorem resetKraus_conjTranspose_mul_basisOutcomeProjector_zero
    (register : QRegister k n) (outcome : Fin (2 ^ k)) :
    (register.resetKraus outcome)ᴴ * register.basisOutcomeProjector 0 =
      (register.resetKraus outcome)ᴴ := by
  have h := congr($(register.basisOutcomeProjector_zero_mul_resetKraus outcome)ᴴ)
  simpa using h

/-- Left projection onto the all-zero register subspace fixes a reset branch density matrix. -/
theorem basisOutcomeProjector_zero_mul_resetBranch (register : QRegister k n)
    (outcome : Fin (2 ^ k)) (density : Operator (2 ^ n)) :
    register.basisOutcomeProjector 0 *
        (register.resetKraus outcome * density *
          (register.resetKraus outcome)ᴴ) =
      register.resetKraus outcome * density *
        (register.resetKraus outcome)ᴴ := by
  rw [← mul_assoc, ← mul_assoc, register.basisOutcomeProjector_zero_mul_resetKraus]

/-- Right projection onto the all-zero register subspace fixes a reset branch density matrix. -/
theorem resetBranch_mul_basisOutcomeProjector_zero (register : QRegister k n)
    (outcome : Fin (2 ^ k)) (density : Operator (2 ^ n)) :
    (register.resetKraus outcome * density *
        (register.resetKraus outcome)ᴴ) * register.basisOutcomeProjector 0 =
      register.resetKraus outcome * density *
        (register.resetKraus outcome)ᴴ := by
  rw [mul_assoc, register.resetKraus_conjTranspose_mul_basisOutcomeProjector_zero]

/-- A reset branch has the selected register fixed at the all-zero basis value.

More precisely, projecting the output of `register.resetKraus outcome` onto the subspace where
`register` equals `|0...0⟩`, on either side of its density matrix, leaves that output unchanged.
The displayed equation is the density-matrix form of this fact. -/
theorem resetBranch_projector_eq (register : QRegister k n)
    (outcome : Fin (2 ^ k)) (density : Operator (2 ^ n)) :
    register.basisOutcomeProjector 0 *
        (register.resetKraus outcome * density *
          (register.resetKraus outcome)ᴴ) *
        register.basisOutcomeProjector 0 =
      register.resetKraus outcome * density *
        (register.resetKraus outcome)ᴴ := by
  rw [register.basisOutcomeProjector_zero_mul_resetBranch,
    register.resetBranch_mul_basisOutcomeProjector_zero]

end QRegister

namespace QProg
variable {Var : Type} {n k : ℕ}

/-- Reset a selected register and retain its former little-endian value in `result`. -/
noncomputable def resetRegisterWithOutcome
    (result : Var) (register : QRegister k n) : QProg Var (2 ^ n) :=
  .qMeasure result register.resetMeasurement.toMeasurement

/-- Reset a selected register and overwrite the temporary classical outcome afterward.

The quantum reset is performed by `resetRegisterWithOutcome`; the following assignment restores
the scratch variable to zero. -/
noncomputable def resetRegister (scratch : Var) (register : QRegister k n) : QProg Var (2 ^ n) :=
  .qSeq (resetRegisterWithOutcome scratch register) (.assign scratch 0)

@[simp]
theorem resetRegisterWithOutcome_eq (result : Var) (register : QRegister k n) :
    resetRegisterWithOutcome result register =
      (QProg.qMeasure result register.resetMeasurement.toMeasurement : QProg Var (2 ^ n)) := rfl

@[simp]
theorem resetRegister_eq (scratch : Var) (register : QRegister k n) :
    resetRegister scratch register =
      QProg.qSeq (resetRegisterWithOutcome scratch register) (.assign scratch 0) := rfl

end QProg
