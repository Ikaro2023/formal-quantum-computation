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

public import QuantumInfo.States.Pure.Qubit
public import QuantumComputation.Maths.LinearAlgebra

/-!
# Primitive gates

This module defines the finite `PrimitiveGate` vocabulary, its readable aliases, and the unitary
denotation of each gate.

Wire order is little-endian.  For CNOT, local wire `0` is the control and local wire `1` the
target.  For Toffoli, local wires `0` and `1` are controls and local wire `2` is the target.
-/

@[expose] public section

open Operator

/-- Fixed, named gates admitted by executable circuits. -/
inductive PrimitiveGate : ℕ → Type where
  | x : PrimitiveGate 1
  | y : PrimitiveGate 1
  | z : PrimitiveGate 1
  | h : PrimitiveGate 1
  | s : PrimitiveGate 1
  | t : PrimitiveGate 1
  | cnot : PrimitiveGate 2
  | swap : PrimitiveGate 2
  | toffoli : PrimitiveGate 3
  deriving DecidableEq, Repr

namespace PrimitiveGate

/-! Readable names for primitive gates in circuit expressions. -/
@[reducible] alias X := PrimitiveGate.x
@[reducible] alias Y := PrimitiveGate.y
@[reducible] alias Z := PrimitiveGate.z
@[reducible] alias H := PrimitiveGate.h
@[reducible] alias S := PrimitiveGate.s
@[reducible] alias T := PrimitiveGate.t
@[reducible] alias CNOT := PrimitiveGate.cnot
@[reducible] alias SWAP := PrimitiveGate.swap
@[reducible] alias TOFF := PrimitiveGate.toffoli

/-- Little-endian CNOT: swap `01` and `11`. -/
def cnotUnitary : 𝐔[Fin (2 ^ 2)] :=
  permutationUnitary (Equiv.swap (1 : Fin 4) (3 : Fin 4))

/-- Two-wire SWAP: swap `01` and `10`. -/
def swapUnitary : 𝐔[Fin (2 ^ 2)] :=
  permutationUnitary (Equiv.swap (1 : Fin 4) (2 : Fin 4))

/-- Little-endian Toffoli: swap `011` and `111`. -/
def toffoliUnitary : 𝐔[Fin (2 ^ 3)] :=
  permutationUnitary (Equiv.swap (3 : Fin 8) (7 : Fin 8))

/-- Exact unitary denotation of a finite primitive gate. -/
noncomputable def eval : {k : ℕ} → PrimitiveGate k → 𝐔[Fin (2 ^ k)]
  | _, .x => Qubit.X
  | _, .y => Qubit.Y
  | _, .z => Qubit.Z
  | _, .h => Qubit.H
  | _, .s => Qubit.S
  | _, .t => Qubit.T
  | _, .cnot => cnotUnitary
  | _, .swap => swapUnitary
  | _, .toffoli => toffoliUnitary

@[simp]
theorem eval_s_val : (eval .s).1 =
    Matrix.diagonal (fun i : Fin 2 ↦ if i = 1 then Complex.I else 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eval, Qubit.S]

@[simp]
theorem eval_t_val : (eval .t).1 =
    Matrix.diagonal (fun i : Fin 2 ↦
      if i = 1 then (1 + Complex.I) / (√2 : ℂ) else 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eval, Qubit.T]

@[simp]
theorem eval_cnot_val : (eval .cnot).1 =
    (Equiv.swap (1 : Fin 4) (3 : Fin 4)).permMatrix ℂ := rfl

@[simp]
theorem eval_swap_val : (eval .swap).1 =
    (Equiv.swap (1 : Fin 4) (2 : Fin 4)).permMatrix ℂ := rfl

@[simp]
theorem eval_toffoli_val : (eval .toffoli).1 =
    (Equiv.swap (3 : Fin 8) (7 : Fin 8)).permMatrix ℂ := rfl

end PrimitiveGate

namespace Qubit

/-- The inverse phase gate is `S† = Z·S`. -/
theorem Z_mul_S_eq_S_inv : Z * S = S⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [mul_assoc, S_sq, Z_sq]

/-- The inverse `T` gate is `T† = Z·S·T`, which uses a single `T`. -/
theorem Z_mul_S_mul_T_eq_T_inv : Z * S * T = T⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [mul_assoc, T_sq, mul_assoc, S_sq, Z_sq]

end Qubit
