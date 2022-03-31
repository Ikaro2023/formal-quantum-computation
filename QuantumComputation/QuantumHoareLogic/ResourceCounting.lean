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

/-!
# Semantic Resource Counting for Quantum Hoare Logic

Defines a user-supplied `CostModel d` and the semantic expected-cost functor
`expectedCost model program state` directly on `QProg Var d` and `CQState (Store Var) d`.
Primitive operations charge their model weight scaled by the current branch trace mass
`state.trace`, sequential composition and conditionals sum branch costs, and `qWhile`
takes the supremum of finite loop-unrolling costs `whileRecCost`.
-/

@[expose] public section

open Operator QProg QProg.Notation
open scoped NNReal ENNReal
open Store (Expr)

namespace ResourceCounting

/-- A user-supplied policy of natural-number weights for primitive operations.
Gate and measurement weights may depend on the operator being executed;
assignments and resets each have a fixed weight. -/
structure CostModel (d : ℕ) where
  /-- The cost of `QProg.assign`. -/
  assignmentCost : ℕ
  /-- The cost of `QProg.qMeasure measurement`. -/
  measurementCost {outcomes : ℕ} (measurement : Measurement d outcomes) : ℕ
  /-- The cost of `QProg.qSet`. -/
  resetCost : ℕ
  /-- The cost of `QProg.qAssign U`. -/
  unitaryCost (U : Unitary d) : ℕ

/-- Zero-cost policy charging `0` for all operations. -/
def CostModel.zero (d : ℕ) : CostModel d where
  assignmentCost := 0
  measurementCost := fun _ ↦ 0
  resetCost := 0
  unitaryCost := fun _ ↦ 0

/-- Charge one for each unitary application and nothing for other operations. -/
@[simps]
def CostModel.unitaryCount (d : ℕ) : CostModel d where
  assignmentCost := 0
  measurementCost := fun _ ↦ 0
  resetCost := 0
  unitaryCost := fun _ ↦ 1

/-- Charge one for each application of the selected unitary, in any dimension. -/
noncomputable def CostModel.ofOracle {d : ℕ} (oracle : Unitary d) : CostModel d where
  assignmentCost := 0
  measurementCost := fun _ ↦ 0
  resetCost := 0
  unitaryCost := fun unitary ↦ if unitary = oracle then 1 else 0

/-- Alias of `CostModel.ofOracle`. -/
noncomputable abbrev oracleCalls {d : ℕ} (oracle : Unitary d) : CostModel d :=
  CostModel.ofOracle oracle

@[simp] theorem oracleCalls_assignmentCost {d : ℕ} (oracle : Unitary d) :
    (oracleCalls oracle).assignmentCost = 0 := rfl

@[simp] theorem oracleCalls_measurementCost {d outcomes : ℕ}
    (oracle : Unitary d) (measurement : Measurement d outcomes) :
    (oracleCalls oracle).measurementCost measurement = 0 := rfl

@[simp] theorem oracleCalls_resetCost {d : ℕ} (oracle : Unitary d) :
    (oracleCalls oracle).resetCost = 0 := rfl

@[simp] theorem oracleCalls_unitaryCost_self {d : ℕ} (oracle : Unitary d) :
    (oracleCalls oracle).unitaryCost oracle = 1 := by
  simp [CostModel.ofOracle]

theorem oracleCalls_unitaryCost_of_ne {d : ℕ} {oracle unitary : Unitary d}
    (h : unitary ≠ oracle) :
    (oracleCalls oracle).unitaryCost unitary = 0 := by
  simp [CostModel.ofOracle, h]

open Classical in
/-- Charge one for each application of `oracle` to a `k`-qubit register of an `n`-qubit system,
and nothing for other operations, so that `expectedCost` under it is the expected number of oracle
calls.  Any other unitary that coincides with such an application is charged too. -/
@[simps assignmentCost measurementCost resetCost]
noncomputable def CostModel.ofEmbeddedOracle {k n : ℕ} (oracle : Unitary (2 ^ k)) :
    CostModel (2 ^ n) where
  assignmentCost := 0
  measurementCost := fun _ ↦ 0
  resetCost := 0
  unitaryCost unitary := if ∃ r : QRegister k n, unitary = r.embedUnitary oracle then 1 else 0

@[simp]
theorem CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary {k n : ℕ} (oracle : Unitary (2 ^ k))
    (r : QRegister k n) : (ofEmbeddedOracle oracle).unitaryCost (r.embedUnitary oracle) = 1 :=
  ite_eq_left ⟨r, rfl⟩

variable {State : Type*} {d : ℕ}

/-- Expected cost accumulated during the first `n` unrollings of a `qWhile` loop. -/
noncomputable def whileRecCost
    (bodyCost : CQState State d → ℝ≥0∞) (bodySem : CQState State d → CQState State d)
    (condition : State → Prop) [DecidablePred condition] : ℕ → CQState State d → ℝ≥0∞
  | 0, _ => 0
  | n + 1, state =>
      let active := state.restrict condition
      bodyCost active + whileRecCost bodyCost bodySem condition n (bodySem active)

@[simp] theorem whileRecCost_zero
    (bodyCost : CQState State d → ℝ≥0∞) (bodySem : CQState State d → CQState State d)
    (condition : State → Prop) [DecidablePred condition] (state : CQState State d) :
    whileRecCost bodyCost bodySem condition 0 state = 0 := rfl

@[simp] theorem whileRecCost_succ
    (bodyCost : CQState State d → ℝ≥0∞) (bodySem : CQState State d → CQState State d)
    (condition : State → Prop) [DecidablePred condition] (n : ℕ) (state : CQState State d) :
    whileRecCost bodyCost bodySem condition (n + 1) state =
      bodyCost (state.restrict condition) +
        whileRecCost bodyCost bodySem condition n (bodySem (state.restrict condition)) := rfl

section
variable {Var : Type} [DecidableEq Var] [NeZero d]

/-- Branch-weighted expected resource cost of executing `program` from `state`
under `model`. Costs accumulate as operations execute, including across loop iterations. -/
noncomputable def expectedCost (model : CostModel d) : QProg Var d → CQState (Store Var) d → ℝ≥0∞
  | .skip, _ => 0
  | .abort, _ => 0
  | .assign _ _, state => state.trace * model.assignmentCost
  | .qMeasure _ measurement, state =>
      state.trace * model.measurementCost measurement
  | .qSet, state => state.trace * model.resetCost
  | .qAssign unitary, state => state.trace * model.unitaryCost unitary
  | .qSeq first second, state =>
      expectedCost model first state +
        expectedCost model second ((interp first).toStateFun state)
  | @QProg.qIf _ _ condition _ yes no, state =>
      expectedCost model yes (state.restrict condition) +
        expectedCost model no (state.restrict (¬ condition ·))
  | @QProg.qWhile _ _ condition _ body, state =>
      ⨆ n, whileRecCost (expectedCost model body) ((interp body).toStateFun) condition n state

@[simp] theorem expectedCost_skip (model : CostModel d) (state : CQState (Store Var) d) :
    expectedCost model (.skip : QProg Var d) state = 0 := rfl

@[simp] theorem expectedCost_abort (model : CostModel d) (state : CQState (Store Var) d) :
    expectedCost model (.abort : QProg Var d) state = 0 := rfl

@[simp] theorem expectedCost_assign
    (model : CostModel d) (x : Var) (e : Expr Var) (state : CQState (Store Var) d) :
    expectedCost model (.assign x e) state = state.trace * model.assignmentCost := rfl

@[simp] theorem expectedCost_qMeasure {outcomes : ℕ} (model : CostModel d)
    (x : Var) (measurement : Measurement d outcomes) (state : CQState (Store Var) d) :
    expectedCost model (.qMeasure x measurement) state =
      state.trace * model.measurementCost measurement := rfl

@[simp] theorem expectedCost_qSet (model : CostModel d) (state : CQState (Store Var) d) :
    expectedCost model (.qSet : QProg Var d) state = state.trace * model.resetCost := rfl

@[simp] theorem expectedCost_qAssign
    (model : CostModel d) (unitary : Unitary d) (state : CQState (Store Var) d) :
    expectedCost model (.qAssign unitary : QProg Var d) state =
      state.trace * model.unitaryCost unitary := rfl

@[simp] theorem expectedCost_qSeq
    (model : CostModel d) (first second : QProg Var d) (state : CQState (Store Var) d) :
    expectedCost model (first ;; second) state =
      expectedCost model first state +
        expectedCost model second ((interp first).toStateFun state) := rfl

@[simp] theorem expectedCost_qIf
    (model : CostModel d) (condition : Store Var → Prop) [DecidablePred condition]
    (yes no : QProg Var d) (state : CQState (Store Var) d) :
    expectedCost model (.qIf condition yes no) state =
      expectedCost model yes (state.restrict condition) +
        expectedCost model no (state.restrict (¬ condition ·)) := rfl

@[simp] theorem expectedCost_qWhile
    (model : CostModel d) (condition : Store Var → Prop) [DecidablePred condition]
    (body : QProg Var d) (state : CQState (Store Var) d) :
    expectedCost model (.qWhile condition body) state =
      ⨆ n, whileRecCost (expectedCost model body)
        ((interp body).toStateFun) condition n state := rfl

/-- Bundled total-resource specification pairing almost-sure termination (output mass conservation)
with a finite upper bound on the expected cost. -/
def TotalExpectedCostLe
    (model : CostModel d) (program : QProg Var d) (initial : CQState (Store Var) d)
    (bound : ℝ≥0) : Prop :=
  ((interp program).toStateFun initial).trace = initial.trace ∧
  expectedCost model program initial ≤ initial.trace * bound

end

end ResourceCounting
