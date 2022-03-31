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

public import QuantumComputation.QuantumHoareLogic.ResourceCounting

/-!
# Compositional Cost Bounds for QHL Programs

Provides `CostBound model program bound` (bounding `expectedCost model program state` by
`state.trace * bound` for every input state) and compositional rules for straight-line
and branching `QProg` constructs.
-/

@[expose] public section

open Operator QProg QProg.Notation
open scoped NNReal
open Store (Expr)

namespace ResourceCounting

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- A finite bound on the expected cost of `program`, valid for every input state `state`. -/
def CostBound (model : CostModel d) (program : QProg Var d) (bound : ℝ≥0) : Prop :=
  ∀ state : CQState (Store Var) d,
    expectedCost model program state ≤ state.trace * bound

namespace CostBound

theorem expectedCost_le {model : CostModel d} {program : QProg Var d} {bound : ℝ≥0}
    (h : CostBound model program bound) (initial : CQState (Store Var) d) :
    expectedCost model program initial ≤ initial.trace * bound :=
  h initial

@[gcongr]
theorem mono {model : CostModel d} {program : QProg Var d} {a b : ℝ≥0}
    (h : CostBound model program a) (hab : a ≤ b) : CostBound model program b := by
  intro state
  exact (h state).trans (by gcongr)

theorem skip_zero (model : CostModel d) : CostBound model (.skip : QProg Var d) 0 := by
  intro state
  simp

theorem abort_zero (model : CostModel d) : CostBound model (.abort : QProg Var d) 0 := by
  intro state
  simp

theorem assign (model : CostModel d) (x : Var) (e : Expr Var) :
    CostBound model (.assign x e) model.assignmentCost := by
  intro state
  simp

theorem qAssign (model : CostModel d) (unitary : Unitary d) :
    CostBound model (.qAssign unitary : QProg Var d) (model.unitaryCost unitary) := by
  intro state
  simp

theorem qSet (model : CostModel d) :
    CostBound model (.qSet : QProg Var d) model.resetCost := by
  intro state
  simp

theorem qMeasure (model : CostModel d) {outcomes : ℕ}
    (x : Var) (measurement : Measurement d outcomes) :
    CostBound model (.qMeasure x measurement) (model.measurementCost measurement) := by
  intro state
  simp

theorem seq {model : CostModel d} {first second : QProg Var d} {a b : ℝ≥0}
    (hfirst : CostBound model first a) (hsecond : CostBound model second b) :
    CostBound model (first ;; second) (a + b) := fun state ↦ by
  rw [expectedCost_qSeq, ENNReal.coe_add, mul_add]
  refine (add_le_add (hfirst state) (hsecond _)).trans ?_
  grw [(interp first).trace_toStateFun_le]

theorem qIf {model : CostModel d} (condition : Store Var → Prop) [DecidablePred condition]
    {yes no : QProg Var d} {a b : ℝ≥0}
    (hyes : CostBound model yes a) (hno : CostBound model no b) :
    CostBound model (.qIf condition yes no) (max a b) := fun state ↦ by
  rw [expectedCost_qIf, ← state.trace_restrict_add_trace_restrict_not condition, ENNReal.coe_add,
    add_mul]
  exact add_le_add ((hyes.mono (le_max_left _ _)) _) ((hno.mono (le_max_right _ _)) _)

end CostBound

end ResourceCounting
