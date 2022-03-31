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

public import QuantumComputation.Algorithms.Grover.Operators
public import QuantumComputation.Primitives.Hadamard
public import QuantumComputation.Primitives.Measure
public import QuantumComputation.QuantumHoareLogic.Syntax

/-!
# Simple Grover program

The while-based Grover search program: a single iteration (`groverStep`), the `K`-iteration
loop (`groverLoop`), and the complete algorithm (`groverAlgo`). Its correctness proof is in
`QuantumComputation.Algorithms.Grover.Verification`.
-/

@[expose] public section

open Operator QProg.Notation

namespace Grover

variable {Var : Type} [DecidableEq Var]
         {n : ℕ}

local notation "d" => 2 ^ n

/-- A single iteration of the Grover loop. -/
noncomputable def groverStep (k : Var) (target : Fin d) : QProg Var d :=
  apply (oracleUnitary target) ;;
  apply diffuserUnitary ;;
  k ≔ (fun σ ↦ σ k + 1)

/-- The while-loop running for `K` iterations. -/
noncomputable def groverLoop (k : Var) (K : ℕ) (target : Fin d) : QProg Var d :=
  qwhile (fun σ ↦ σ k < K) loop (groverStep k target)

/-- The complete Grover search algorithm. -/
noncomputable def groverAlgo (k res : Var) (K : ℕ) (target : Fin d) : QProg Var d :=
  qset ;;
  apply hadamardUnitary ;;
  k ≔ 0 ;;
  groverLoop k K target ;;
  res ≔ measure compMeasurement

end Grover
