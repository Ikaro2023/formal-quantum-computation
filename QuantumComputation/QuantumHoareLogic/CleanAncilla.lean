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

public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputation.Registers.Embed
public import QuantumComputation.Registers.Assertions

/-!
# Clean-Ancilla Subroutine Predicates

Predicates for specifying quantum subroutines that act on a target register `rTarget` while using
a disjoint ancilla register `rAnc` that starts in `|0^m⟩` and must be returned to `|0^m⟩`:
- `M.restrictToZeroAncilla rAnc` conjugates an assertion `M` branchwise by the clean
  ancilla projector `|0^m⟩⟨0^m|` (`rAnc.basisOutcomeProjector 0`).
- `RealizesCleanSubroutine` states via a Hoare triple that for every quantum observable `M`,
  `P` implements `U` on `rTarget` while preserving clean ancillas `rAnc`.
- `M.restrictToBasisOutcomes rTarget outcomes` restricts an assertion to a specified finite set of
  computational-basis values of a register.
- `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace` restricts the target to selected
  computational-basis outcomes and the workspace to zero.
- `RealizesCleanSubroutineOnEncoding` specifies the action on valid encoded data with zero
  workspace at input and output, while leaving invalid inputs unspecified.
-/

@[expose] public section

open Operator QProg Matrix

/-- Restrict a classical-quantum assertion `M` branchwise onto the zero-ancilla subspace
`|0^m⟩⟨0^m|` of `rAnc`. -/
noncomputable def CQAssertion.restrictToZeroAncilla {State : Type*} {n m : ℕ}
    (M : CQAssertion State (2 ^ n)) (rAnc : QRegister m n) : CQAssertion State (2 ^ n) :=
  M.conj (rAnc.basisOutcomeProjector 0) (by simp)

@[simp]
theorem CQAssertion.restrictToZeroAncilla_coe {State : Type*} {n m : ℕ}
    (M : CQAssertion State (2 ^ n)) (rAnc : QRegister m n) (σ : State) :
    (M.restrictToZeroAncilla rAnc σ).1 =
      (M σ).1.conj (rAnc.basisOutcomeProjector 0) := rfl

/-- Restrict a classical-quantum assertion to a finite set of computational-basis outcomes of
`register`, using one projector onto their joint span rather than one assertion per outcome. -/
noncomputable def CQAssertion.restrictToBasisOutcomes {State : Type*} {n k : ℕ}
    (M : CQAssertion State (2 ^ n)) (register : QRegister k n)
    (outcomes : Finset (Fin (2 ^ k))) : CQAssertion State (2 ^ n) :=
  M.conj (register.basisOutcomesProjector outcomes) (by simp)

/-- `P` implements `U` on `rTarget` while preserving clean ancillas `rAnc`. -/
def RealizesCleanSubroutine {Var : Type} [DecidableEq Var] {n k m : ℕ}
    (rTarget : QRegister k n) (rAnc : QRegister m n)
    (_hdisj : rTarget.DisjointWires rAnc) (U : Unitary (2 ^ k))
    (P : QProg Var (2 ^ n)) : Prop :=
  ∀ (M : Observable (Fin (2 ^ n))),
    let post : CQAssertion (Store Var) (2 ^ n) := .restrictToZeroAncilla (fun _ ↦ M) rAnc
    ⦃ (post.qAssign (rTarget.embedUnitary U)).restrictToZeroAncilla rAnc ⦄
    P
    ⦃ post ⦄

/-- `P` implements `U` from inputs where `rTarget` lies in the span of `outcomes` and `rAnc`
starts in zero.

The two assertion restrictions describe independent input requirements: valid target data and
clean workspace. Inputs violating either requirement are unconstrained. -/
def RealizesUnitaryFromBasisOutcomesAndZeroWorkspace
    {Var : Type} [DecidableEq Var]
    {n k m : ℕ}
    (rTarget : QRegister k n) (outcomes : Finset (Fin (2 ^ k)))
    (rAnc : QRegister m n) (hdisj : rTarget.DisjointWires rAnc)
    (U : Unitary (2 ^ (k + m)))
    (P : QProg Var (2 ^ n)) : Prop :=
  let combined := rTarget.concat rAnc hdisj
  let restrict (A : CQAssertion (Store Var) (2 ^ n)) :=
    (A.restrictToBasisOutcomes rTarget outcomes).restrictToZeroAncilla rAnc
  ∀ M : Observable (Fin (2 ^ n)),
    restrict (CQAssertion.qAssign (combined.embedUnitary U) (fun _ ↦ M)) ≤
      restrict (wp P (fun _ ↦ M))

/-- `P` realizes `basisPermutation` on `validInputs`, with workspace starting and ending in zero.

The prescribed basis action is a partial isometry on the valid-data, zero-workspace subspace.
An existentially chosen total unitary extends it to the combined data and workspace registers, as
required by the QHL unitary-assignment API. The extension on invalid encodings is unspecified, and
inputs with nonzero workspace are unconstrained. -/
noncomputable def RealizesCleanSubroutineOnEncoding
    {Var : Type} [DecidableEq Var] {n k m : ℕ}
    (rTarget : QRegister k n) (rAnc : QRegister m n)
    (hdisj : rTarget.DisjointWires rAnc) (validInputs : Set (Fin (2 ^ k)))
    (basisPermutation : Equiv.Perm (Fin (2 ^ k))) (P : QProg Var (2 ^ n)) : Prop :=
  -- Embed a data basis index with zero workspace.
  let withZeroWorkspace :=
    (Function.Embedding.refl (Fin (2 ^ k))).trans
      (Fin.castLEEmb (Nat.pow_le_pow_right (by decide) (Nat.le_add_right k m)))
  -- Enumerate the valid target-register basis indices.
  let validOutcomes :=
    @Finset.filter _ validInputs
      (fun outcome ↦ Classical.propDecidable (outcome ∈ validInputs))
      Finset.univ
  -- There exists a unitary extension, arbitrary outside valid data with zero workspace.
  ∃ extension : Unitary (2 ^ (k + m)),
    -- Map valid data with zero workspace to the specified output.
    (∀ input, input ∈ validInputs →
      extension.1 *ᵥ basisState (withZeroWorkspace input) =
        basisState (withZeroWorkspace (basisPermutation input))) ∧
    -- Independently require valid target data and zero workspace.
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace
      rTarget validOutcomes rAnc hdisj extension P
