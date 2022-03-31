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

public import QuantumComputation.QuantumHoareLogic.Semantics

/-! This file defines the syntax of the cq-language following Y. Feng and M. Ying,
"Quantum Hoare Logic with classical variables". -/

@[expose] public section

open Operator QMonad
open Store (Expr)

/-- `QProg Var d` is the syntax of the cq-language defined in §4.1, with classical variables indexed
by `Var`.

Note two shallow-embedding simplifications relative to §3.1 and §4.1 of the paper:
- We omit random assignment $x :=_{\$} g$.
- Whereas the paper gives classical variables both `Boolean` and `Integer` sorts and treats
  integer expressions $e$ and Boolean guards $b$ as syntactic first-order expressions, here
  `Store Var := Var → ℤ` stores integers while `assign` takes shallowly embedded expressions
  `Expr Var := Store Var → ℤ` and `qIf`/`qWhile` take decidable predicates
  `(b : Store Var → Prop) [DecidablePred b]`. Using decidable `Store Var → Prop` guards directly
  matches the paper's satisfaction relation $\sigma \models b$ without encoding truth values as
  nonzero integers (`if ... then 1 else 0` / `b σ ≠ 0`), and aligns guards directly with
  `ofProp` and Lean's propositional tactics while keeping branch conditions decidable. -/
inductive QProg (Var : Type) (d : ℕ) : Type where
  /-- The no-op statement ($\mathbf{skip}$ in Section 4.1), which terminates immediately and leaves
  the state unchanged.

  `skip` is notation for `QProg.skip`. -/
  | skip : QProg Var d
  /-- The abort statement ($\mathbf{abort}$ in Section 4.1), which halts computation with no proper
  state reached.

  `abort` is notation for `QProg.abort`. -/
  | abort : QProg Var d
  /-- Deterministic classical assignment ($x := e$ in Section 4.1), updating the classical variable
  `x` to the value of `e`.

  `x ::= e` and `x ≔ e` are both notation for `QProg.assign x e`. -/
  | assign (x : Var) (e : Expr Var) : QProg Var d
  /-- Quantum measurement ($x := \mathbf{meas}\ \mathcal{M}[\bar{q}]$ in Section 4.1), applying the
  `i`-outcome measurement `ℳ` to the `d`-dimensional quantum system and storing the outcome in `x`.

  `x ::= measure ℳ` and `x ≔ measure ℳ` are both notation for `QProg.qMeasure x ℳ`. -/
  | qMeasure {i : ℕ} (x : Var) (ℳ : Measurement d i) : QProg Var d
  /-- Quantum initialization ($q := 0$ or $\bar{q} := 0$ in Section 4.1), resetting the
  `d`-dimensional quantum system to $|0⟩$.

  `qset` is notation for `QProg.qSet`. -/
  | qSet : QProg Var d
  /-- Unitary transformation ($\bar{q} \mathrel{{*}=} U$ in Section 4.1), applying the unitary
  operator `U` to the `d`-dimensional quantum system.

  `qapply U` and `apply U` are both notation for `QProg.qAssign U`. -/
  | qAssign (U : Unitary d) : QProg Var d
  /-- Sequential composition ($S_0; S_1$ in Section 4.1), executing `c₁` followed by `c₂`.

  `c₁ ;; c₂` is notation for `QProg.qSeq c₁ c₂`. -/
  | qSeq (c₁ c₂ : QProg Var d) : QProg Var d
  /-- Classical conditional ($\mathbf{if}\ b\ \mathbf{then}\ S_1\ \mathbf{else}\ S_0\ \mathbf{end}$
  in Section 4.1), executing `S₁` on stores `σ` satisfying `b σ` and `S₀` otherwise.

  `qif b then S₁ else S₀` and `QIF b THEN S₁ ELSE S₀` are both notation for `QProg.qIf b S₁ S₀`. -/
  | qIf (b : Store Var → Prop) [DecidablePred b] (S₁ S₀ : QProg Var d) : QProg Var d
  /-- Classical while loop ($\mathbf{while}\ b\ \mathbf{do}\ S\ \mathbf{end}$ in Section 4.1),
  repeatedly executing `c` while `b` holds on the classical store.

  `qwhile b loop c` and `QWHILE b DO c` are both notation for `QProg.qWhile b c`. -/
  | qWhile (b : Store Var → Prop) [DecidablePred b] (c : QProg Var d) : QProg Var d

namespace QProg.Notation

@[inherit_doc] scoped notation "skip" => QProg.skip
@[inherit_doc] scoped notation "abort" => QProg.abort

@[inherit_doc] scoped notation x:71 unicode(" ≔ ", " ::= ") e:71 => QProg.assign x e

@[inherit_doc QProg.qMeasure]
scoped macro (priority := high) x:term:71 unicode(" ≔ ", " ::= ") &"measure " m:term:71 : term =>
  `(QProg.qMeasure $x $m)

/-- Unexpander for `QProg.qMeasure`. -/
@[scoped app_unexpander QProg.qMeasure]
meta def qMeasureUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $x $m) => `($x ≔ measure $m)
  | _ => throw ()

@[inherit_doc] scoped notation "qset" => QProg.qSet
@[inherit_doc] scoped notation:70 "qapply " U:71 => QProg.qAssign U
@[inherit_doc] scoped notation:70 "apply " U:71 => QProg.qAssign U
@[inherit_doc] scoped infixr:60 " ;; " => QProg.qSeq

@[inherit_doc] scoped notation "QIF " b:71 " THEN " c₁:71 " ELSE " c₂:71 => QProg.qIf b c₁ c₂
@[inherit_doc] scoped notation "qif " b:71 " then " c₁:71 " else " c₂:71 => QProg.qIf b c₁ c₂

@[inherit_doc] scoped notation "QWHILE " b:71 " DO " c₁:71 => QProg.qWhile b c₁
@[inherit_doc] scoped notation "qwhile " b:71 " loop " c₁:71 => QProg.qWhile b c₁

@[inherit_doc QProg.qWhile]
scoped macro "QWHILE " b:term:71 " DO " c₁:term:71 " STEP " c₂:term:71 : term =>
  `(QProg.qWhile $b ($c₁ ;; $c₂))
@[inherit_doc QProg.qWhile]
scoped macro "qwhile " b:term:71 " loop " c₁:term:71 " step " c₂:term:71 : term =>
  `(QProg.qWhile $b ($c₁ ;; $c₂))

end QProg.Notation

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

open QMonad.Q

/-- Interpret an abstract `QProg` syntax as an executable program in `Q`. -/
noncomputable def interp : QProg Var d → Q (Store Var) d Unit
  | .skip => pure ()
  | .abort => abort d
  | .assign x e => assign x e
  | .qMeasure x ℳ => qMeasurement x ℳ
  | .qSet => qSet
  | .qAssign U => qAssign U
  | .qSeq c₁ c₂ => do interp c₁; interp c₂
  | @QProg.qIf _ _ b _ c₁ c₂ => cqIf b (interp c₁) (interp c₂)
  | @QProg.qWhile _ _ b _ c => OmegaCompletePartialOrder.ωSup
      ⟨whileRec (interp c) b, whileRec_monotone (interp c) b⟩

@[simp] theorem interp_skip : interp (.skip : QProg Var d) = pure () := rfl
@[simp] theorem interp_abort : interp (.abort : QProg Var d) = abort d := rfl
@[simp] theorem interp_assign (x : Var) (e : Expr Var) :
    interp (.assign x e : QProg Var d) = assign x e := rfl
@[simp] theorem interp_qMeasure {i : ℕ} (x : Var) (ℳ : Measurement d i) :
    interp (.qMeasure x ℳ : QProg Var d) = qMeasurement x ℳ := rfl
@[simp] theorem interp_qSet : interp (.qSet : QProg Var d) = qSet := rfl
@[simp] theorem interp_qAssign (U : Unitary d) :
    interp (.qAssign U : QProg Var d) = qAssign U := rfl
@[simp] theorem interp_qSeq (c₁ c₂ : QProg Var d) :
    interp (.qSeq c₁ c₂) = (do interp c₁; interp c₂) := rfl
@[simp] theorem interp_qIf (b : Store Var → Prop) [DecidablePred b] (c₁ c₂ : QProg Var d) :
    interp (.qIf b c₁ c₂) = cqIf b (interp c₁) (interp c₂) := rfl
@[simp] theorem interp_qWhile (b : Store Var → Prop) [DecidablePred b] (c : QProg Var d) :
    interp (.qWhile b c) = OmegaCompletePartialOrder.ωSup
      ⟨whileRec (interp c) b, whileRec_monotone (interp c) b⟩ := rfl

end
