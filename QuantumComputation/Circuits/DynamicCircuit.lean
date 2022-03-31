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

public import QuantumComputation.Circuits.Combinators
public import QuantumComputation.Registers.Measurement

/-!
# Dynamic circuits

Circuits extended with mid-circuit measurement and classically controlled branching,
compiled to `QProg`.  `OracleDynamicCircuit` adds classical `qWhile` loops and calls to an opaque
oracle, which `ResourceCounting.CostModel.ofEmbeddedOracle` counts.
-/

@[expose] public section

open Operator

/-- A circuit on `n` qubits with mid-circuit measurements into classical variables `Var`.

Compared to `QProg`:
- No `assign`: the `qIf` condition is an arbitrary decidable predicate on the classical store, so a
  separate classical-assignment instruction isn't needed.
- No `skip`: `DynamicCircuit.identity` (`.circuit .identity`) compiles to `QProg.skip`.
- No `qWhile`: it can be added when an algorithm needs repeat-until-success. -/
inductive DynamicCircuit (Var : Type) (n : ℕ) : Type where
  | circuit : Circuit n → DynamicCircuit Var n
  | measure : Var → QRegister 1 n → DynamicCircuit Var n
  | qIf (b : Store Var → Prop) [DecidablePred b] :
      DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n
  | seq : DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n

/-- A dynamic circuit with access to one opaque oracle acting on `oracleWidth` qubits.  Its other
unitaries come in blocks of type `Step` (see `OracleDynamicCircuit.step`).

The source syntax records an oracle call only by the register to which it is applied; it does not
contain the oracle unitary itself.  `compile` supplies that unitary later, so a circuit can use the
oracle only through `.oracle` calls.

As with `DynamicCircuit`, there is no classical assignment.  A loop with a fixed number of
iterations can be written with `sequence`, e.g. `sequence (List.replicate K body)`, while
`qWhile` handles repeat-until-success loops conditioned on measurement outcomes. -/
inductive OracleDynamicCircuit (Step Var : Type) (n oracleWidth : ℕ) : Type where
  | skip : OracleDynamicCircuit Step Var n oracleWidth
  /-- A block of non-oracle unitaries.  With `Step = Circuit n` a block is built from primitive
  gates, each of which can be counted.  With `Step = Unitary (2 ^ n)` a block is any fixed unitary,
  as in the query model, where only oracle calls are counted. -/
  | step : Step → OracleDynamicCircuit Step Var n oracleWidth
  | oracle : QRegister oracleWidth n → OracleDynamicCircuit Step Var n oracleWidth
  | measure {k : ℕ} : Var → QRegister k n → OracleDynamicCircuit Step Var n oracleWidth
  | qIf (b : Store Var → Prop) [DecidablePred b] : OracleDynamicCircuit Step Var n oracleWidth →
      OracleDynamicCircuit Step Var n oracleWidth → OracleDynamicCircuit Step Var n oracleWidth
  | qWhile (b : Store Var → Prop) [DecidablePred b] : OracleDynamicCircuit Step Var n oracleWidth →
      OracleDynamicCircuit Step Var n oracleWidth
  | seq : OracleDynamicCircuit Step Var n oracleWidth →
      OracleDynamicCircuit Step Var n oracleWidth → OracleDynamicCircuit Step Var n oracleWidth

namespace DynamicCircuit

variable {Var : Type} {n : ℕ}

/-! Helper shorthands to match `Circuit`. -/

/-- The empty dynamic circuit. -/
abbrev identity : DynamicCircuit Var n := .circuit .identity

/-- Apply a primitive gate to a register. -/
abbrev gate {k : ℕ} (g : PrimitiveGate k) (r : QRegister k n) : DynamicCircuit Var n :=
  .circuit <| .gate g r

/-- Physical wires mentioned syntactically by a dynamic circuit. -/
def support : DynamicCircuit Var n → Finset (Wire n)
  | .circuit c => c.support
  | .measure _ r => r.image
  | @DynamicCircuit.qIf _ _ _ _ t f => t.support ∪ f.support
  | .seq p₁ p₂ => p₁.support ∪ p₂.support

@[simp]
theorem support_identity : (identity : DynamicCircuit Var n).support = ∅ := rfl

@[simp]
theorem support_circuit (c : Circuit n) : (circuit c : DynamicCircuit Var n).support = c.support :=
  rfl

@[simp]
theorem support_measure (v : Var) (r : QRegister 1 n) : (measure v r).support = r.image := rfl

@[simp]
theorem support_qIf (cond : Store Var → Prop) [DecidablePred cond] (t f : DynamicCircuit Var n) :
    (qIf cond t f).support = t.support ∪ f.support := rfl

@[simp]
theorem support_seq (p₁ p₂ : DynamicCircuit Var n) :
    (seq p₁ p₂).support = p₁.support ∪ p₂.support := rfl

/-- Compile a dynamic circuit to a quantum program. -/
noncomputable def compile : DynamicCircuit Var n → QProg Var (2 ^ n)
  | .circuit c => c.compile
  | .measure v r => QProg.measureRegister v r
  | @DynamicCircuit.qIf _ _ cond _ t f => .qIf cond t.compile f.compile
  | .seq p₁ p₂ => .qSeq p₁.compile p₂.compile

@[simp]
theorem compile_identity :
    (identity : DynamicCircuit Var n).compile = (QProg.skip : QProg Var (2 ^ n)) := rfl

@[simp]
theorem compile_circuit (c : Circuit n) :
    (circuit c : DynamicCircuit Var n).compile = c.compile := rfl

@[simp]
theorem compile_measure (v : Var) (r : QRegister 1 n) :
    (measure v r).compile = QProg.measureRegister v r := rfl

@[simp]
theorem compile_qIf (cond : Store Var → Prop) [DecidablePred cond] (t f : DynamicCircuit Var n) :
    (qIf cond t f).compile = .qIf cond t.compile f.compile := rfl

@[simp]
theorem compile_seq (p₁ p₂ : DynamicCircuit Var n) :
    (seq p₁ p₂).compile = .qSeq p₁.compile p₂.compile := rfl

end DynamicCircuit

namespace OracleDynamicCircuit

variable {Step Var : Type} {n oracleWidth : ℕ}

/-- Apply a primitive gate to a register. -/
abbrev gate {k : ℕ} (g : PrimitiveGate k) (r : QRegister k n) :
    OracleDynamicCircuit (Circuit n) Var n oracleWidth :=
  .step (.gate g r)

/-- A dynamic circuit of primitive gates, as an oracle dynamic circuit that never calls the
oracle. -/
def ofDynamicCircuit : DynamicCircuit Var n → OracleDynamicCircuit (Circuit n) Var n oracleWidth
  | .circuit c => .step c
  | .measure v r => .measure v r
  | @DynamicCircuit.qIf _ _ cond _ t f => .qIf cond (ofDynamicCircuit t) (ofDynamicCircuit f)
  | .seq p₁ p₂ => .seq (ofDynamicCircuit p₁) (ofDynamicCircuit p₂)

/-- Execute a list of oracle dynamic circuits from left to right;
`sequence (List.replicate K body)` runs `body` `K` times. -/
def sequence :
    List (OracleDynamicCircuit Step Var n oracleWidth) →
      OracleDynamicCircuit Step Var n oracleWidth
  | [] => skip
  | c :: cs => .seq c (sequence cs)

@[simp]
theorem sequence_nil :
    sequence ([] : List (OracleDynamicCircuit Step Var n oracleWidth)) = skip := rfl

@[simp]
theorem sequence_cons (c : OracleDynamicCircuit Step Var n oracleWidth)
    (cs : List (OracleDynamicCircuit Step Var n oracleWidth)) :
    sequence (c :: cs) = .seq c (sequence cs) := rfl

/-- The circuit never branches on classical data: it has neither `.qIf` nor `.qWhile`. Its
measurement outcomes are then never read, so every run applies the same unitaries and oracle calls,
and any classical processing has to be built from unitary steps. -/
@[simp]
def IsBranchFree : OracleDynamicCircuit Step Var n oracleWidth → Prop
  | .skip => True
  | .step _ => True
  | .oracle _ => True
  | .measure _ _ => True
  | @OracleDynamicCircuit.qIf _ _ _ _ _ _ _ _ => False
  | @OracleDynamicCircuit.qWhile _ _ _ _ _ _ _ => False
  | .seq p₁ p₂ => p₁.IsBranchFree ∧ p₂.IsBranchFree

@[simp]
theorem isBranchFree_sequence (cs : List (OracleDynamicCircuit Step Var n oracleWidth)) :
    (sequence cs).IsBranchFree ↔ ∀ c ∈ cs, c.IsBranchFree := by
  induction cs <;> simp [*]

/-- Compile an oracle dynamic circuit after supplying its opaque oracle unitary; `compileStep`
compiles the other unitary steps.

An `.oracle register` source node becomes one unitary assignment of `oracleUnitary` embedded in
`register`; no other source node has access to `oracleUnitary`. -/
noncomputable def compile (compileStep : Step → QProg Var (2 ^ n))
    (oracleUnitary : Unitary (2 ^ oracleWidth)) :
    OracleDynamicCircuit Step Var n oracleWidth → QProg Var (2 ^ n)
  | .skip => .skip
  | .step s => compileStep s
  | .oracle register => .qAssign (register.embedUnitary oracleUnitary)
  | .measure v r => QProg.measureRegister v r
  | @OracleDynamicCircuit.qIf _ _ _ _ cond _ t f =>
      .qIf cond (compile compileStep oracleUnitary t) (compile compileStep oracleUnitary f)
  | @OracleDynamicCircuit.qWhile _ _ _ _ cond _ body =>
      .qWhile cond (compile compileStep oracleUnitary body)
  | .seq p₁ p₂ =>
      .qSeq (compile compileStep oracleUnitary p₁) (compile compileStep oracleUnitary p₂)

section compile

variable (compileStep : Step → QProg Var (2 ^ n)) (oracleUnitary : Unitary (2 ^ oracleWidth))

@[simp]
theorem compile_skip :
    (skip : OracleDynamicCircuit Step Var n oracleWidth).compile compileStep oracleUnitary =
      .skip := rfl

@[simp]
theorem compile_step (s : Step) :
    (.step s : OracleDynamicCircuit Step Var n oracleWidth).compile compileStep oracleUnitary =
      compileStep s := rfl

@[simp]
theorem compile_oracle (register : QRegister oracleWidth n) :
    (oracle register : OracleDynamicCircuit Step Var n oracleWidth).compile compileStep
      oracleUnitary = .qAssign (register.embedUnitary oracleUnitary) := rfl

@[simp]
theorem compile_measure {k : ℕ} (v : Var) (r : QRegister k n) :
    (measure v r : OracleDynamicCircuit Step Var n oracleWidth).compile compileStep
      oracleUnitary = QProg.measureRegister v r := rfl

@[simp]
theorem compile_qIf (cond : Store Var → Prop) [DecidablePred cond]
    (t f : OracleDynamicCircuit Step Var n oracleWidth) :
    (qIf cond t f).compile compileStep oracleUnitary =
      .qIf cond (t.compile compileStep oracleUnitary) (f.compile compileStep oracleUnitary) :=
  rfl

@[simp]
theorem compile_qWhile (cond : Store Var → Prop) [DecidablePred cond]
    (body : OracleDynamicCircuit Step Var n oracleWidth) :
    (qWhile cond body).compile compileStep oracleUnitary =
      .qWhile cond (body.compile compileStep oracleUnitary) :=
  rfl

@[simp]
theorem compile_seq (p₁ p₂ : OracleDynamicCircuit Step Var n oracleWidth) :
    (seq p₁ p₂).compile compileStep oracleUnitary =
      .qSeq (p₁.compile compileStep oracleUnitary) (p₂.compile compileStep oracleUnitary) :=
  rfl

/-- A lifted dynamic circuit compiles, with any oracle, to the dynamic circuit's own program. -/
@[simp]
theorem compile_ofDynamicCircuit (p : DynamicCircuit Var n) :
    (ofDynamicCircuit p : OracleDynamicCircuit (Circuit n) Var n oracleWidth).compile
      Circuit.compile oracleUnitary = p.compile := by
  induction p with
  | circuit c => rfl
  | measure v r => rfl
  | qIf cond t f iht ihf => simp [ofDynamicCircuit, iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ => simp [ofDynamicCircuit, ih₁, ih₂]

end compile

end OracleDynamicCircuit
