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

public import QuantumComputation.QuantumHoareLogic.CQState
public import QuantumComputation.QuantumHoareLogic.Syntax
import QuantumComputation.QuantumHoareLogic.WP

/-! This file contains some basic tests for the vc generator. -/

@[expose] public section
open Operator QProg QProg.Notation QMonad

namespace QHLExamples

/-- The names of the classical variables. -/
inductive TestVar where
  | x | y | z
  deriving DecidableEq, Inhabited

open TestVar (x)

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- A program that sets the variable `x` to `0`, if it is not already. -/
def exampleProg' : QProg TestVar 1 :=
  qif (fun σ ↦ σ x ≠ 0) then x ::= 0 else skip

example : ⦃⊤⦄ exampleProg' ⦃fun σ ↦ ⌜σ x = 0⌝⦄ := by
  apply Triple.infer
  intros Δ
  unfold exampleProg'
  simp +contextual [← Pi.top_def, - Observable.top_eq_one]

/-- A program that sets the variable `x` to `2`, if it is zero. -/
def exampleProg'' : QProg TestVar 1 :=
  qif (fun σ ↦ σ x ≠ 0) then skip else x ::= 2

example : ⦃fun σ ↦ ⌜σ x = 0 ∨ σ x = 2⌝⦄ exampleProg''
          ⦃fun σ ↦ ⌜σ x = 2⌝⦄ := by
  apply Triple.infer
  intros Δ
  simp [Observable.ofProp, exampleProg'']
  grind

/-- A program that applies a unitary matrix. -/
def exampleProgQAssign (U : Unitary 1) : QProg TestVar 1 :=
  .qAssign U

example (U : Unitary 1) (θ : CQAssertion (Store TestVar) 1) :
    wp (exampleProgQAssign U) θ = θ.qAssign U := by
  rfl

end QHLExamples
