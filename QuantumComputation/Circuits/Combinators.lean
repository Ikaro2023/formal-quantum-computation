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

public import QuantumComputation.Circuits.Basic

/-!
# Structural circuit combinators

This module manipulates restricted circuit syntax without collapsing a subcircuit into an
arbitrary unitary.  In particular, `onRegister` relocates every primitive gate of a smaller
circuit through an ordered ambient register, preserving its decomposition and gate count.
-/

@[expose] public section

namespace Circuit

variable {m n k : ℕ}

/-- Relocate a `k`-wire circuit onto an ordered `k`-wire register in an `n`-wire circuit.

Every primitive register inside `c` is composed with `placement`; no evaluated matrix or
arbitrary-unitary syntax node is introduced. -/
def onRegister (placement : QRegister k n) : Circuit k → Circuit n
  | .identity => .identity
  | .gate g r => .gate g (placement.compose r)
  | .seq c₁ c₂ => .seq (onRegister placement c₁) (onRegister placement c₂)

/-- Implement the inverse of one primitive without adding inverse constructors.

`S† = Z·S` and `T† = Z·S·T`, so each inverse uses its phase gate once; every other admitted
primitive is self-inverse. -/
def inverseGate {arity : ℕ} (primitive : PrimitiveGate arity)
    (register : QRegister arity n) : Circuit n :=
  match primitive with
  | .s => sequence [.gate PrimitiveGate.S register, .gate PrimitiveGate.Z register]
  | .t => sequence [.gate PrimitiveGate.T register, .gate PrimitiveGate.S register,
      .gate PrimitiveGate.Z register]
  | .x => .gate PrimitiveGate.X register
  | .y => .gate PrimitiveGate.Y register
  | .z => .gate PrimitiveGate.Z register
  | .h => .gate PrimitiveGate.H register
  | .cnot => .gate PrimitiveGate.CNOT register
  | .swap => .gate PrimitiveGate.SWAP register
  | .toffoli => .gate PrimitiveGate.TOFF register

/-- Reverse a circuit and finitely implement every primitive inverse. -/
def inverse : Circuit n → Circuit n
  | .identity => .identity
  | .gate g r => inverseGate g r
  | .seq c₁ c₂ => .seq c₂.inverse c₁.inverse

/-- Physical wires mentioned syntactically by a circuit. -/
def support : Circuit n → Finset (Fin n)
  | .identity => ∅
  | .gate _ r => r.image
  | .seq c₁ c₂ => c₁.support ∪ c₂.support

@[simp]
theorem onRegister_identity (placement : QRegister k n) :
    onRegister placement .identity = .identity := rfl

/-- Relocating one primitive gate composes its local register with the ambient placement. -/
@[simp]
theorem onRegister_relocates_gate (placement : QRegister k n) {m : ℕ}
    (primitive : PrimitiveGate m) (localRegister : QRegister m k) :
    onRegister placement (.gate primitive localRegister) =
      .gate primitive (placement.compose localRegister) := rfl

@[simp]
theorem onRegister_seq (placement : QRegister k n) (c₁ c₂ : Circuit k) :
    onRegister placement (.seq c₁ c₂) =
      .seq (onRegister placement c₁) (onRegister placement c₂) := rfl

@[simp]
theorem onRegister_whole (c : Circuit n) : onRegister (QRegister.whole n) c = c := by
  induction c <;> simp_all [onRegister]

@[simp]
theorem onRegister_compose (outer : QRegister k n) (inner : QRegister m k)
    (c : Circuit m) :
    onRegister outer (onRegister inner c) = onRegister (outer.compose inner) c := by
  induction c <;> simp_all [onRegister]

/-- Relocating syntax and then evaluating is exactly semantic register embedding. -/
@[simp]
theorem eval_onRegister (placement : QRegister k n) (c : Circuit k) :
    (onRegister placement c).eval = placement.embedUnitary c.eval := by
  induction c with
  | identity => simp
  | gate g r => simp
  | seq c₁ c₂ ih₁ ih₂ =>
      simp only [onRegister_seq, eval_seq, ih₁, ih₂, ← placement.embedUnitary_mul]

@[simp]
theorem inverse_identity : (identity : Circuit n).inverse = .identity := rfl

@[simp]
theorem inverse_gate {m : ℕ} (g : PrimitiveGate m) (r : QRegister m n) :
    (gate g r).inverse = inverseGate g r := rfl

@[simp]
theorem inverse_seq (c₁ c₂ : Circuit n) :
    (seq c₁ c₂).inverse = .seq c₂.inverse c₁.inverse := rfl

/-- Expanding a primitive inverse does not introduce any new wires. -/
@[simp]
theorem support_inverseGate {arity : ℕ} (primitive : PrimitiveGate arity)
    (register : QRegister arity n) :
    (inverseGate primitive register).support = register.image := by
  cases primitive <;> simp [inverseGate, sequence, support]

/-- A circuit and its uncomputation mention exactly the same physical wires. -/
@[simp]
theorem support_inverse (c : Circuit n) : c.inverse.support = c.support := by
  induction c <;> simp_all [inverse, support, Finset.union_comm]

private theorem embedUnitary_eq_embedUnitary_inv_of_mul_self {arity : ℕ}
    (register : QRegister arity n) (unitary : Operator.Unitary (2 ^ arity))
    (h : unitary * unitary = 1) :
    register.embedUnitary unitary = register.embedUnitary unitary⁻¹ := by
  apply congrArg register.embedUnitary
  exact eq_inv_of_mul_eq_one_left h

/-- The finite implementation of a primitive inverse has the expected denotation. -/
@[simp]
theorem eval_inverseGate {arity : ℕ} (primitive : PrimitiveGate arity)
    (register : QRegister arity n) :
    (inverseGate primitive register).eval = register.embedUnitary primitive.eval⁻¹ := by
  cases primitive with
  | x =>
      simpa [inverseGate, PrimitiveGate.eval] using
        embedUnitary_eq_embedUnitary_inv_of_mul_self register Qubit.X Qubit.X_sq
  | y =>
      simpa [inverseGate, PrimitiveGate.eval] using
        embedUnitary_eq_embedUnitary_inv_of_mul_self register Qubit.Y Qubit.Y_sq
  | z =>
      simpa [inverseGate, PrimitiveGate.eval] using
        embedUnitary_eq_embedUnitary_inv_of_mul_self register Qubit.Z Qubit.Z_sq
  | h =>
      simpa [inverseGate, PrimitiveGate.eval] using
        embedUnitary_eq_embedUnitary_inv_of_mul_self register Qubit.H Qubit.H_sq
  | cnot =>
      simpa [inverseGate, PrimitiveGate.eval, PrimitiveGate.cnotUnitary] using
        embedUnitary_eq_embedUnitary_inv_of_mul_self register
          (Operator.permutationUnitary (Equiv.swap (1 : Fin 4) 3))
          (Operator.permutationUnitary_swap_mul_self 1 3)
  | swap =>
      simpa [inverseGate, PrimitiveGate.eval, PrimitiveGate.swapUnitary] using
        embedUnitary_eq_embedUnitary_inv_of_mul_self register
          (Operator.permutationUnitary (Equiv.swap (1 : Fin 4) 2))
          (Operator.permutationUnitary_swap_mul_self 1 2)
  | toffoli =>
      simpa [inverseGate, PrimitiveGate.eval, PrimitiveGate.toffoliUnitary] using
        embedUnitary_eq_embedUnitary_inv_of_mul_self register
          (Operator.permutationUnitary (Equiv.swap (3 : Fin 8) 7))
          (Operator.permutationUnitary_swap_mul_self 3 7)
  | s =>
      simp only [inverseGate, sequence, eval_seq, eval_gate, eval_identity, one_mul,
        PrimitiveGate.eval]
      rw [← register.embedUnitary_mul]
      exact congrArg register.embedUnitary Qubit.Z_mul_S_eq_S_inv
  | t =>
      simp only [inverseGate, sequence, eval_seq, eval_gate, eval_identity, one_mul,
        PrimitiveGate.eval]
      rw [← register.embedUnitary_mul, ← register.embedUnitary_mul]
      exact congrArg register.embedUnitary Qubit.Z_mul_S_mul_T_eq_T_inv

/-- The denotation of syntactic uncomputation is the inverse whole-system unitary. -/
@[simp]
theorem eval_inverse (c : Circuit n) : c.inverse.eval = c.eval⁻¹ := by
  induction c with
  | identity => simp [inverse]
  | gate primitive register =>
      simp only [inverse_gate, eval_inverseGate, eval_gate, register.embedUnitary_inv]
  | seq first second ihFirst ihSecond =>
      rw [inverse_seq, eval_seq, ihSecond, ihFirst, eval_seq, mul_inv_rev]

@[simp]
theorem inverse_onRegister (placement : QRegister k n) (c : Circuit k) :
    (onRegister placement c).inverse = onRegister placement c.inverse := by
  induction c with
  | identity => rfl
  | gate primitive register =>
      cases primitive <;> simp [onRegister, inverse, inverseGate, sequence]
  | seq first second ihFirst ihSecond =>
      simp [onRegister, inverse, ihFirst, ihSecond]

@[simp]
theorem support_identity : (identity : Circuit n).support = ∅ := rfl

@[simp]
theorem support_gate {m : ℕ} (g : PrimitiveGate m) (r : QRegister m n) :
    (gate g r).support = r.image := rfl

theorem support_single (g : PrimitiveGate 1) (q : Wire n) :
    (single g q).support = {q} := by
  simp [single]

theorem support_cnot (control target : Wire n) (hct : control ≠ target) :
    (CNOT control target hct).support = {control, target} := by
  simp [CNOT]

theorem support_swap (left right : Wire n) (hlr : left ≠ right) :
    (SWAP left right hlr).support = {left, right} := by
  simp [SWAP]

theorem support_toffoli (control₁ control₂ target : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target)
    (h₂t : control₂ ≠ target) :
    (TOFF control₁ control₂ target h₁₂ h₁t h₂t).support =
      {control₁, control₂, target} := by
  simp [TOFF]

@[simp]
theorem support_seq (c₁ c₂ : Circuit n) :
    (seq c₁ c₂).support = c₁.support ∪ c₂.support := rfl

@[simp]
theorem support_sequence (cs : List (Circuit n)) :
    (sequence cs).support = (cs.map support).foldr (· ∪ ·) ∅ := by
  induction cs <;> simp_all

/-- If every member of a sequence stays inside `wires`, so does the complete sequence. -/
theorem support_sequence_subset {cs : List (Circuit n)} {wires : Finset (Fin n)}
    (h : ∀ c ∈ cs, c.support ⊆ wires) : (sequence cs).support ⊆ wires := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      simp only [sequence_cons, support_seq, Finset.union_subset_iff]
      exact ⟨h c (by simp), ih (fun d hd ↦ h d (by simp [hd]))⟩

/-- Relocating a circuit can mention only wires selected by its placement register. -/
theorem support_onRegister_subset (placement : QRegister k n) (c : Circuit k) :
    (onRegister placement c).support ⊆ placement.image := by
  induction c with
  | identity => simp
  | gate g r =>
      simpa only [onRegister_relocates_gate, support_gate] using
        QRegister.image_compose_subset placement r
  | seq c₁ c₂ ih₁ ih₂ =>
      simpa only [onRegister_seq, support_seq, Finset.union_subset_iff] using ⟨ih₁, ih₂⟩

end Circuit
