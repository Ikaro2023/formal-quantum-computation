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

public import QuantumComputation.Registers.Measurement
public import QuantumComputation.QuantumHoareLogic.Expectation

/-!
# Register-local basis assertions

These are proof observables, not executable checks.  `basisAssertion r value` asks whether the
selected logical register lies in the computational-basis subspace `value`; `cleanAssertion r`
is the special case `value = 0`.  Evaluating the assertion does not measure or collapse a state.
-/

@[expose] public section

open Operator Matrix
open scoped MatrixOrder ComplexOrder QHLExpectation

namespace QRegister

variable {n k : ℕ}

/-! ## QHL observable assertions

QHL assertions are observables, so this section turns a register-outcome projector into the
bundled Hermitian, positive, bounded observable required by `CQAssertion`.  These definitions
apply to density matrices and can be used in assertions that depend on the classical store. -/

/-- Projector onto a finite set of computational-basis outcomes of `register`. -/
noncomputable def basisOutcomesProjector (register : QRegister k n)
    (outcomes : Finset (Fin (2 ^ k))) : Operator (2 ^ n) :=
  Matrix.diagonal fun global ↦
    if register.extractIndex global ∈ outcomes then 1 else 0

@[simp]
theorem basisOutcomesProjector_conjTranspose (register : QRegister k n)
    (outcomes : Finset (Fin (2 ^ k))) :
    (register.basisOutcomesProjector outcomes)ᴴ =
      register.basisOutcomesProjector outcomes := by
  simp [basisOutcomesProjector]

@[simp]
theorem basisOutcomesProjector_mul_self (register : QRegister k n)
    (outcomes : Finset (Fin (2 ^ k))) :
    register.basisOutcomesProjector outcomes * register.basisOutcomesProjector outcomes =
      register.basisOutcomesProjector outcomes := by
  simp [basisOutcomesProjector]

/-- A finite union of computational-basis outcomes, bundled as an observable. -/
noncomputable def basisOutcomesObservable (register : QRegister k n)
    (outcomes : Finset (Fin (2 ^ k))) : Observable (Fin (2 ^ n)) :=
  .diagonal fun global ↦ if register.extractIndex global ∈ outcomes then 1 else 0

@[simp]
theorem basisOutcomesObservable_mat (register : QRegister k n) (outcomes : Finset (Fin (2 ^ k))) :
    (register.basisOutcomesObservable outcomes).1.mat =
      register.basisOutcomesProjector outcomes := by
  simp [basisOutcomesObservable, basisOutcomesProjector, apply_ite]

@[simp]
theorem basisOutcomesProjector_le_one (register : QRegister k n)
    (outcomes : Finset (Fin (2 ^ k))) :
    register.basisOutcomesProjector outcomes ≤ 1 := by
  simpa [HermitianMat.le_iff, ← Matrix.le_iff] using
    (register.basisOutcomesObservable outcomes).2.2

/-- The register projector is an observable: it is positive and at most the identity. -/
noncomputable def basisOutcomeObservable (register : QRegister k n) (outcome : Fin (2 ^ k)) :
    Observable (Fin (2 ^ n)) :=
  register.basisOutcomesObservable {outcome}

@[simp]
theorem basisOutcomeObservable_mat (register : QRegister k n) (outcome : Fin (2 ^ k)) :
    (register.basisOutcomeObservable outcome).1.mat =
      register.basisOutcomeProjector outcome := by
  simp [basisOutcomeObservable, basisOutcomesProjector,
    register.basisOutcomeProjector_eq_diagonal]

@[simp]
theorem basisOutcomeProjector_le_one (register : QRegister k n) (outcome : Fin (2 ^ k)) :
    register.basisOutcomeProjector outcome ≤ 1 := by
  simpa [HermitianMat.le_iff, ← Matrix.le_iff] using
    (register.basisOutcomeObservable outcome).2.2

/-- Assertion that every qubit in `register` is zero. -/
noncomputable def cleanObservable (register : QRegister k n) : Observable (Fin (2 ^ n)) :=
  register.basisOutcomeObservable 0

section
variable {State : Type*}

/-- State-independent QHL assertion that `register` has the selected computational-basis value.

Its expectation on a density matrix is the probability of obtaining `outcome` by a computational
basis measurement of `register`.  The definition is general in `outcome`; `cleanAssertion` below
is its all-zero special case. -/
noncomputable def basisAssertion (register : QRegister k n) (outcome : Fin (2 ^ k)) :
    CQAssertion State (2 ^ n) :=
  fun _ ↦ register.basisOutcomeObservable outcome

/-- State-independent QHL assertion that every qubit in `register` is zero. -/
noncomputable def cleanAssertion (register : QRegister k n) : CQAssertion State (2 ^ n) :=
  fun _ ↦ register.cleanObservable

@[simp]
theorem basisAssertion_apply
    (register : QRegister k n) (outcome : Fin (2 ^ k)) (store : State) :
    (register.basisAssertion outcome : CQAssertion State (2 ^ n)) store =
      register.basisOutcomeObservable outcome := rfl

@[simp]
theorem cleanAssertion_apply (register : QRegister k n) (store : State) :
    (register.cleanAssertion : CQAssertion State (2 ^ n)) store =
      register.cleanObservable := rfl

/-- Expectation of a basis assertion is the sum of its local projector expectation over classical
states. -/
theorem expect_basisAssertion
    (register : QRegister k n) (outcome : Fin (2 ^ k)) (state : CQState State (2 ^ n)) :
    𝔼[state ⊨ register.basisAssertion outcome] =
      ∑' store : State,
        (Matrix.trace (register.basisOutcomeProjector outcome *
          (state.1 store).1.mat)).re := by
  simp [expect_eq_tsum, HermitianMat.inner_eq_re_trace]

end

/-- Pure-state probability associated with one register-local basis assertion. -/
noncomputable def basisOutcomeProbability (register : QRegister k n)
    (outcome : Fin (2 ^ k)) (state : Fin (2 ^ n) → ℂ) : ℝ :=
  ∑ index, Complex.normSq
    ((register.basisOutcomeProjector outcome *ᵥ state) index)

/-- The observable expectation on a pure density matrix is the projected branch probability. -/
theorem trace_basisOutcomeProjector_mul_pureStateDensity
    (register : QRegister k n) (outcome : Fin (2 ^ k)) (state : Fin (2 ^ n) → ℂ) :
    Matrix.trace (register.basisOutcomeProjector outcome * pureStateDensity state) =
      (register.basisOutcomeProbability outcome state : ℂ) := by
  let projector := register.basisOutcomeProjector outcome
  have htrace :
      Matrix.trace (projector * pureStateDensity state * projector) =
        Matrix.trace (projector * pureStateDensity state) := by
    calc
      Matrix.trace (projector * pureStateDensity state * projector) =
          Matrix.trace (projector * (projector * pureStateDensity state)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((projector * projector) * pureStateDensity state) := by
        rw [mul_assoc]
      _ = Matrix.trace (projector * pureStateDensity state) := by
        rw [register.basisOutcomeProjector_mul_self]
  calc
    Matrix.trace (projector * pureStateDensity state) =
        Matrix.trace (projector * pureStateDensity state * projector) := htrace.symm
    _ = Matrix.trace
        (projector * pureStateDensity state * projectorᴴ) := by
      rw [register.basisOutcomeProjector_conjTranspose]
    _ = Matrix.trace (pureStateDensity (projector *ᵥ state)) := by
      rw [matrix_conj_pureStateDensity]
    _ = (register.basisOutcomeProbability outcome state : ℂ) := by
      rw [trace_pureStateDensity]
      rfl

/-! ## Pure-vector support predicates

The circuit layer often proves exact action on vectors `Fin (2^n) → ℂ` before transporting the
result to QHL's density-matrix semantics.  The following `Prop`-valued predicates are convenient
for those vector proofs; they are not QHL assertions and do not inspect the classical store. -/

/-- A pure vector definitely has a register value when projecting onto that value leaves it
unchanged. -/
def HasBasisValue (register : QRegister k n) (outcome : Fin (2 ^ k)) (state : Fin (2 ^ n) → ℂ) :
    Prop :=
  register.basisOutcomeProjector outcome *ᵥ state = state

/-- A pure vector has clean ancillas when their joint register has value zero.

This is the `Prop`-valued, pure-vector companion of `cleanObservable` / `cleanAssertion`; it is
used by unitary circuit proofs.  The observable forms are the appropriate versions for general
QHL density-matrix states. -/
def IsClean (register : QRegister k n) (state : Fin (2 ^ n) → ℂ) : Prop :=
  register.HasBasisValue 0 state

theorem HasBasisValue.probability_eq_weight {register : QRegister k n}
    {outcome : Fin (2 ^ k)} {state : Fin (2 ^ n) → ℂ}
    (h : register.HasBasisValue outcome state) :
    register.basisOutcomeProbability outcome state =
      ∑ index, Complex.normSq (state index) := by
  unfold HasBasisValue at h
  rw [basisOutcomeProbability, h]

end QRegister
