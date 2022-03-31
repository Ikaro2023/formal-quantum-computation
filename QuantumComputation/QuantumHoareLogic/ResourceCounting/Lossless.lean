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

public import QuantumComputation.QuantumHoareLogic.Syntax
public import QuantumComputation.QuantumHoareLogic.WP

/-!
# Lossless Programs for QHL Resource Counting

Defines `Lossless` programs, which terminate with probability `1` from every input (preserving
`CQState.trace`), along with primitive trace conservation (`Lossless.assign`, `Lossless.qAssign`,
`Lossless.qSet`, `Lossless.qMeasure`), composition rules (`Lossless.seq`, `Lossless.qIf`), and
`Lossless.of_wp_top` for total correctness.

`Lossless.qWhile` is defined in another file.
-/

@[expose] public section

open Operator QProg.Notation
open scoped NNReal
open Store (Expr)

namespace QProg
variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- A program is lossless if it terminates with probability `1` from every input, i.e. it
preserves the trace of every state. -/
@[mk_iff lossless_if_trace_eq]
structure Lossless (program : QProg Var d) : Prop where of_trace_eq ::
  trace_eq (Δ : CQState (Store Var) d) : ((interp program).toStateFun Δ).trace = Δ.trace

namespace Lossless

theorem «skip» : Lossless (.skip : QProg Var d) := .of_trace_eq fun _ ↦ rfl

theorem assign (x : Var) (e : Expr Var) : Lossless (.assign x e : QProg Var d) :=
  .of_trace_eq <| CQState.trace_assign x e

theorem qAssign (unitary : Unitary d) : Lossless (.qAssign unitary : QProg Var d) :=
  .of_trace_eq <| CQState.trace_qAssign unitary

theorem qSet : Lossless (.qSet : QProg Var d) :=
  .of_trace_eq <| CQState.trace_qSet

/-- Complete measurements preserve trace. -/
theorem qMeasure {outcomes : ℕ} (x : Var) (measurement : CompleteMeasurement d outcomes) :
  Lossless (.qMeasure x measurement.toMeasurement : QProg Var d) :=
  .of_trace_eq <| CQState.trace_qMeasurement_of_complete x measurement

theorem seq {first second : QProg Var d} (hfirst : Lossless first) (hsecond : Lossless second) :
    Lossless (first ;; second) :=
  .of_trace_eq <| fun state ↦ (hsecond.trace_eq _).trans (hfirst.trace_eq state)

theorem qIf (condition : Store Var → Prop) [DecidablePred condition]
    {yes no : QProg Var d} (hyes : Lossless yes)
    (hno : Lossless no) : Lossless (.qIf condition yes no) :=
  .of_trace_eq <| fun state ↦ by
    simp [hyes.trace_eq, hno.trace_eq, state.trace_restrict_add_trace_restrict_not condition]

/-- Total correctness for `⊤` makes a program lossless. -/
theorem of_wp_top {program : QProg Var d} (h : wp program (⊤ : CQAssertion (Store Var) d) = ⊤) :
    Lossless program := .of_trace_eq fun state ↦ by
  have he := expect_wp program state (⊤ : CQAssertion (Store Var) d)
  rw [h, expect_top, expect_top] at he
  exact NNReal.coe_inj.mp he.symm

/-- A program establishing any postcondition with certainty is lossless. -/
theorem of_wp_eq_top {program : QProg Var d} {post : CQAssertion (Store Var) d}
    (h : wp program post = ⊤) : Lossless program :=
  of_wp_top (top_unique (h.ge.trans (wp_mono program le_top)))

end Lossless

end QProg
