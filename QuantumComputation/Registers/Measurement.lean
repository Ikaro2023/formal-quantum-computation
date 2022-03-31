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

public import QuantumComputation.Registers.Embed
public import QuantumComputation.QuantumHoareLogic.Syntax
public import QuantumComputation.Primitives.Measure

/-!
# Computational-basis measurement of a register

Measuring a `k`-wire register inside an `n`-wire state has `2^k` outcomes.  The Kraus operator for
outcome `o` keeps exactly those global computational-basis states whose bits on the selected
register encode `o`; all other amplitudes are removed.  Wires outside the register are preserved.

The resulting outcome-indexed measurement is packaged for use by `QProg.measureRegister`.
-/

@[expose] public section

open Operator
open scoped Matrix MatrixOrder ComplexOrder

namespace QRegister

variable {n k : ℕ}

/-- Whole-system projector for one computational-basis outcome on a selected register.

This is the local primitive projector `compProj outcome`, embedded into the selected wires. -/
noncomputable def basisOutcomeProjector (r : QRegister k n) (outcome : Fin (2 ^ k)) :
    Operator (2 ^ n) :=
  r.embedMatrix (compProj outcome)

theorem basisOutcomeProjector_eq_diagonal (r : QRegister k n) (outcome : Fin (2 ^ k)) :
    r.basisOutcomeProjector outcome =
      Matrix.diagonal fun global ↦ if r.extractIndex global = outcome then 1 else 0 := by
  rw [basisOutcomeProjector, compProj_eq_diagonal, r.embedMatrix_diagonal]

@[simp]
theorem basisOutcomeProjector_apply (r : QRegister k n) (outcome : Fin (2 ^ k))
    (i j : Fin (2 ^ n)) :
    r.basisOutcomeProjector outcome i j =
      if i = j then (if r.extractIndex i = outcome then 1 else 0) else 0 := by
  rw [basisOutcomeProjector_eq_diagonal, Matrix.diagonal_apply]

@[simp]
theorem basisOutcomeProjector_conjTranspose (r : QRegister k n)
    (outcome : Fin (2 ^ k)) :
    (r.basisOutcomeProjector outcome)ᴴ = r.basisOutcomeProjector outcome := by
  rw [basisOutcomeProjector, ← r.embedMatrix_conjTranspose, compProj_conjTranspose]

@[simp]
theorem basisOutcomeProjector_mul_self (r : QRegister k n)
    (outcome : Fin (2 ^ k)) :
    r.basisOutcomeProjector outcome * r.basisOutcomeProjector outcome =
      r.basisOutcomeProjector outcome := by
  rw [basisOutcomeProjector, ← r.embedMatrix_mul, compProj_mul_self]

/-- On a computational-basis state, the outcome projector either keeps that state or removes it. -/
@[simp 1100]
theorem basisOutcomeProjector_mulVec_single (r : QRegister k n)
    (outcome : Fin (2 ^ k)) (global : Fin (2 ^ n)) :
    r.basisOutcomeProjector outcome *ᵥ Pi.single global 1 =
      if r.extractIndex global = outcome then Pi.single global 1 else 0 := by
  rw [basisOutcomeProjector, r.embedMatrix_mulVec_single_factors, compProj_mulVec_single]
  by_cases h : outcome = r.extractIndex global
  · simp [h, r.tensorState_single_factors]
  · simp [h, Ne.symm h]

/-- Register measurement acts pointwise: the selected outcome keeps precisely the amplitudes
whose local register index is that outcome. -/
theorem basisOutcomeProjector_mulVec (r : QRegister k n)
    (outcome : Fin (2 ^ k)) (state : Fin (2 ^ n) → ℂ)
    (global : Fin (2 ^ n)) :
    (r.basisOutcomeProjector outcome *ᵥ state) global =
      if r.extractIndex global = outcome then state global else 0 := by
  rw [basisOutcomeProjector_eq_diagonal, Matrix.mulVec_diagonal]
  by_cases h : r.extractIndex global = outcome <;> simp [h]

/-- Measuring a definite local basis state returns that value with certainty, while retaining
the complete (possibly entangled among itself) state of the register environment. -/
theorem basisOutcomeProjector_mulVec_tensorBasis (r : QRegister k n)
    (outcome value : Fin (2 ^ k))
    (environmentState : (r.Environment → ZMod 2) → ℂ) :
    r.basisOutcomeProjector outcome *ᵥ
        r.tensorState (Pi.single value 1) environmentState =
      if outcome = value then
        r.tensorState (Pi.single value 1) environmentState
      else 0 := by
  rw [basisOutcomeProjector, r.embedMatrix_mulVec_tensorState, compProj_mulVec_single]
  by_cases hov : outcome = value <;> simp [hov]

/-- Measuring an arbitrary selected-register factor keeps only the requested local amplitude and
leaves the complete environment factor unchanged. -/
theorem basisOutcomeProjector_mulVec_tensorState (r : QRegister k n)
    (outcome : Fin (2 ^ k)) (localState : Fin (2 ^ k) → ℂ)
    (environmentState : (r.Environment → ZMod 2) → ℂ) :
    r.basisOutcomeProjector outcome *ᵥ
        r.tensorState localState environmentState =
      r.tensorState (Pi.single outcome (localState outcome)) environmentState := by
  rw [basisOutcomeProjector, r.embedMatrix_mulVec_tensorState, compProj_mulVec]

/-- The outcome projectors form a complete projective measurement. -/
@[simp]
theorem sum_basisOutcomeProjector (r : QRegister k n) :
    (∑ outcome : Fin (2 ^ k), r.basisOutcomeProjector outcome) = 1 := by
  simp only [basisOutcomeProjector, ← r.embedMatrix_sum, compProj_sum, r.embedMatrix_one]

/-- Standard computational-basis measurement of exactly the selected register. -/
noncomputable def computationalBasisMeasurement (r : QRegister k n) :
    CompleteMeasurement (2 ^ n) (2 ^ k) :=
  r.embedCompleteMeasurement compCompleteMeasurement

@[simp]
theorem computationalBasisMeasurement_apply (r : QRegister k n)
    (outcome : Fin (2 ^ k)) :
    (r.computationalBasisMeasurement.1 outcome) = r.basisOutcomeProjector outcome := rfl

end QRegister

namespace QProg

/-- Measure a selected register in the computational basis and store its little-endian numeric
outcome in classical variable `result`. -/
noncomputable def measureRegister {Var : Type}
    {n k : ℕ} (result : Var) (r : QRegister k n) : QProg Var (2 ^ n) :=
  .qMeasure result r.computationalBasisMeasurement.toMeasurement

end QProg
