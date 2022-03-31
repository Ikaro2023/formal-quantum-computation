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

public import QuantumComputation.Circuits.Gates
public import QuantumComputation.QuantumHoareLogic.Syntax
public import QuantumComputation.Registers.Embed

/-!
# Restricted circuit syntax

This module defines `Circuit n`: identity circuits, applications of `PrimitiveGate`s to ordered
registers, and sequential composition.  It also provides circuit evaluation, state evolution,
list sequencing, and translations to QHL programs.
-/

@[expose] public section

open Operator
open scoped Matrix

/-- A unitary circuit of `n` wires made exclusively from the admitted primitive gates. -/
inductive Circuit (n : ℕ) : Type where
  /-- The identity circuit, connecting inputs directly to outputs. -/
  | identity : Circuit n
  /-- `gate g r` is the `k`-wire gate `g` arranged via `r` onto the `n` wires of the circuit. -/
  | gate {k : ℕ} (g : PrimitiveGate k) (r : QRegister k n) : Circuit n
  /-- A sequence of two circuits, with notation `c₁ ;;ᶜ c₂` for `seq c₁ c₂`. -/
  | seq : Circuit n → Circuit n → Circuit n

namespace Circuit

variable {n : ℕ}

/-- Exact whole-system unitary denoted by a restricted circuit.

For `c₁ ;;ᶜ c₂`, states encounter `c₁` first and `c₂` second, hence the denotation is
`eval c₂ * eval c₁`. -/
noncomputable def eval : Circuit n → Unitary (2 ^ n)
  | .identity => 1
  | .gate g r => r.embedUnitary g.eval
  | .seq c₁ c₂ => eval c₂ * eval c₁

/-- Evolve a state vector through a circuit. -/
noncomputable abbrev evolve (circuit : Circuit n)
    (state : StateVector n) : StateVector n :=
  circuit.eval.1 *ᵥ state

/-- Execute a list of circuits from left to right. -/
def sequence : List (Circuit n) → Circuit n
  | [] => .identity
  | c :: cs => .seq c (sequence cs)

/-- Apply a one-qubit primitive to a physical wire. -/
abbrev single (g : PrimitiveGate 1) (q : Wire n) : Circuit n :=
  .gate g (QRegister.singleton q)

/-- Place an `X` gate on wire `q`. -/ abbrev X (q : Wire n) : Circuit n := single .X q
/-- Place an `Y` gate on wire `q`. -/ abbrev Y (q : Wire n) : Circuit n := single .Y q
/-- Place a `Z` gate on wire `q`. -/ abbrev Z (q : Wire n) : Circuit n := single .Z q
/-- Place an `H` gate on wire `q`. -/ abbrev H (q : Wire n) : Circuit n := single .H q
/-- Place an `S` gate on wire `q`. -/ abbrev S (q : Wire n) : Circuit n := single .S q
/-- Place a `T` gate on wire `q`. -/ abbrev T (q : Wire n) : Circuit n := single .T q

/-- CNOT with the first wire as control and the second as target. -/
abbrev CNOT (control target : Wire n) (hct : control ≠ target) : Circuit n :=
  .gate PrimitiveGate.CNOT (QRegister.pair control target hct)

/-- Swap two distinct physical wires. -/
abbrev SWAP (left right : Wire n) (hlr : left ≠ right) : Circuit n :=
  .gate PrimitiveGate.SWAP (QRegister.pair left right hlr)

/-- Toffoli with two controls followed by its target. -/
abbrev TOFF (control₁ control₂ target : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target)
    (h₂t : control₂ ≠ target) : Circuit n :=
  .gate PrimitiveGate.TOFF (QRegister.triple control₁ control₂ target h₁₂ h₁t h₂t)


/-- Compile a circuit to one whole-system unitary assignment. -/
noncomputable def toQProg {Var : Type} (circuit : Circuit n) : QProg Var (2 ^ n) :=
  .qAssign circuit.eval

/-- Compile a circuit while preserving primitive gates and sequencing boundaries. -/
noncomputable def compile {Var : Type} :
    Circuit n → QProg Var (2 ^ n)
  | .identity => .skip
  | .gate primitive register => .qAssign (register.embedUnitary primitive.eval)
  | .seq first second => .qSeq first.compile second.compile

section
variable {Var : Type}

@[simp]
theorem toQProg_eq_qAssign (circuit : Circuit n) :
    circuit.toQProg = (QProg.qAssign circuit.eval : QProg Var (2 ^ n)) := rfl

@[simp]
theorem compile_identity : (identity : Circuit n).compile = (QProg.skip : QProg Var (2 ^ n)) := rfl

@[simp]
theorem compile_gate {arity : ℕ} (gate : PrimitiveGate arity) (register : QRegister arity n) :
    (Circuit.gate gate register).compile =
      (QProg.qAssign (register.embedUnitary gate.eval) : QProg Var (2 ^ n)) := rfl

@[simp]
theorem compile_seq (first second : Circuit n) :
    ((seq first second).compile : QProg Var (2 ^ n)) =
      QProg.qSeq (first.compile : QProg Var (2 ^ n)) second.compile := rfl

end

@[simp] theorem eval_identity : (identity : Circuit n).eval = 1 := rfl

@[simp] theorem eval_gate {k : ℕ} (g : PrimitiveGate k) (r : QRegister k n) :
    (gate g r).eval = r.embedUnitary g.eval := rfl

@[simp]
theorem eval_single (g : PrimitiveGate 1) (q : Wire n) :
    (single g q).eval = (QRegister.singleton q).embedUnitary g.eval := rfl

@[simp] theorem eval_seq (c₁ c₂ : Circuit n) :
    (seq c₁ c₂).eval = c₂.eval * c₁.eval := rfl

@[simp]
theorem evolve_identity (state : StateVector n) :
    (identity : Circuit n).evolve state = state := by
  exact Matrix.one_mulVec state

@[simp]
theorem evolve_seq (first second : Circuit n) (state : StateVector n) :
    (seq first second).evolve state = second.evolve (first.evolve state) := by
  unfold evolve
  rw [eval_seq]
  exact (Matrix.mulVec_mulVec state second.eval.1 first.eval.1).symm

@[simp] theorem sequence_nil : sequence ([] : List (Circuit n)) = .identity := rfl

@[simp] theorem sequence_cons (c : Circuit n) (cs : List (Circuit n)) :
    sequence (c :: cs) = .seq c (sequence cs) := rfl

@[simp]
theorem eval_sequence (cs : List (Circuit n)) :
    (sequence cs).eval = (cs.map eval).reverse.prod := by
  induction cs <;> simp_all

end Circuit

open QMonad QMonad.Q

namespace Circuit.QHLBridge

/-- Structural and flattened compilation have identical QHL semantics. -/
theorem compile_interp_eq_toQProg {Var : Type} [DecidableEq Var]
    {n : ℕ} (circuit : Circuit n) :
    interp (circuit.compile : QProg Var (2 ^ n)) =
      interp (circuit.toQProg : QProg Var (2 ^ n)) := by
  induction circuit with
  | identity =>
      change (pure () : Q (Store Var) (2 ^ n) Unit) = qAssign 1
      exact qAssign_one.symm
  | gate gate register => rfl
  | seq first second ihFirst ihSecond =>
      change (do
          (_ : Unit) ← interp (first.compile : QProg Var (2 ^ n))
          interp (second.compile : QProg Var (2 ^ n))) =
        qAssign (second.eval * first.eval)
      rw [ihFirst, ihSecond]
      change (do
          (_ : Unit) ← qAssign (State := Store Var) first.eval
          qAssign second.eval) = _
      exact qAssign_compose first.eval second.eval

end Circuit.QHLBridge

namespace Circuit.Notation

@[inherit_doc] scoped infixr:60 " ;;ᶜ " => Circuit.seq

end Circuit.Notation
