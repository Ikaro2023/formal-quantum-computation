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

public import QuantumComputation.Maths.LinearAlgebra
public import QuantumComputation.Registers.Basis
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Embedding register-local operators

A local matrix is tensored with the identity on the environment and then reindexed through the
register's computational-basis split.  Consequently, gates may act on arbitrary noncontiguous
ordered wires while the QHL core continues to see one whole-system matrix.
-/

@[expose] public section

open Operator
open scoped Matrix Kronecker

namespace QRegister

variable {n k : ℕ}

/-- Embed a `k`-qubit matrix into the selected wires of an `n`-qubit system. -/
noncomputable def embedMatrix (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex r.basisSplitEquiv.symm r.basisSplitEquiv.symm
    (A ⊗ₖ (1 : Matrix (r.Environment → ZMod 2) (r.Environment → ZMod 2) ℂ))

@[simp]
theorem embedMatrix_apply (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (i j : Fin (2 ^ n)) :
    r.embedMatrix A i j =
      A (r.extractIndex i) (r.extractIndex j) *
        if (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2 then 1 else 0 := by
  simp [embedMatrix, Matrix.reindex_apply, Matrix.one_apply]

/-- Two global computational-basis kets agree on every physical wire outside `r`.

This is a predicate about the labels of two basis kets, not about arbitrary quantum states.  It
allows their bits on `r` itself to differ, but requires every environment wire to have the same
`0`/`1` label. -/
def AgreeOutside (r : QRegister k n) (i j : Fin (2 ^ n)) : Prop :=
  ∀ q : Wire n, q ∉ Set.range r.wires → basisBits n i q = basisBits n j q

/-- The environment components of two global basis indices coincide exactly when they agree on
every wire outside the register.

`(r.basisSplitEquiv i).2` is the assignment of basis labels to wires not selected by `r`; this
lemma lets later proofs state that fact as the more readable `r.AgreeOutside i j`. -/
theorem basisSplit_environment_eq_iff (r : QRegister k n) (i j : Fin (2 ^ n)) :
    (r.basisSplitEquiv i).2 = (r.basisSplitEquiv j).2 ↔ r.AgreeOutside i j := by
  constructor
  · intro h q hq
    simpa only [basisSplitEquiv_apply_snd] using congrFun h ⟨q, hq⟩
  · intro h
    funext q
    simp only [basisSplitEquiv_apply_snd]
    exact h q.1 q.2

/-- A replacement is characterized completely by its selected local value and unchanged
environment.

If `expected` reads as `localIndex` through `r`, and `expected` agrees with `global` outside
`r`, then replacing `r`'s part of `global` by `localIndex` produces exactly `expected`. -/
theorem replaceIndex_eq_of_extractIndex_eq_of_agreeOutside
    (r : QRegister k n) (global expected : Fin (2 ^ n))
    (localIndex : Fin (2 ^ k))
    (hlocal : r.extractIndex expected = localIndex)
    (henvironment : r.AgreeOutside expected global) :
    r.replaceIndex global localIndex = expected := by
  apply r.basisSplitEquiv.injective
  rw [basisSplitEquiv_replaceIndex]
  apply Prod.ext
  · simpa using hlocal.symm
  · exact ((r.basisSplit_environment_eq_iff expected global).2 henvironment).symm

/-- For a one-wire register, agreement outside the register simply means agreement at every
physical wire other than the selected wire. -/
@[simp]
theorem singleton_agreeOutside (q : Wire n) (i j : Fin (2 ^ n)) :
    (singleton q).AgreeOutside i j ↔
      ∀ p, p ≠ q → basisBits n i p = basisBits n j p := by
  simp [AgreeOutside, ne_comm]

/-! ### Two-wire evaluation conveniences

These concrete facts support exact `2`-qubit matrix regression tests.  They are not part of the
general embedding construction: for a singleton in a two-wire system, its environment has just
the other wire. -/

/-- In a two-wire system, the environment of the singleton register selecting wire `0` consists
only of wire `1`.  Thus the environment components of `i` and `j` agree exactly when their wire-1
basis labels agree. -/
theorem singleton_zero_basisSplit_environment_eq_iff (i j : Fin 4) :
    ((singleton (0 : Fin 2)).basisSplitEquiv i).2 =
        ((singleton (0 : Fin 2)).basisSplitEquiv j).2 ↔
      basisBits 2 i 1 = basisBits 2 j 1 := by
  rw [basisSplit_environment_eq_iff, singleton_agreeOutside]
  constructor
  · intro h
    exact h 1 (by decide)
  · intro h p hp
    fin_cases p
    · exact (hp rfl).elim
    · exact h

/-- The forward-use form of `singleton_zero_basisSplit_environment_eq_iff`. -/
theorem singleton_zero_environment_eq_of_bit_eq {i j : Fin 4}
    (h : basisBits 2 i 1 = basisBits 2 j 1) :
    ((singleton (0 : Fin 2)).basisSplitEquiv i).2 =
      ((singleton (0 : Fin 2)).basisSplitEquiv j).2 :=
  (singleton_zero_basisSplit_environment_eq_iff i j).2 h

/-- The inequality form of `singleton_zero_basisSplit_environment_eq_iff`. -/
theorem singleton_zero_environment_ne_of_bit_ne {i j : Fin 4}
    (h : basisBits 2 i 1 ≠ basisBits 2 j 1) :
    ((singleton (0 : Fin 2)).basisSplitEquiv i).2 ≠
      ((singleton (0 : Fin 2)).basisSplitEquiv j).2 :=
  mt (singleton_zero_basisSplit_environment_eq_iff i j).1 h

/-- In a two-wire system, the environment of the singleton register selecting wire `1` consists
only of wire `0`.  Thus the environment components of `i` and `j` agree exactly when their wire-0
basis labels agree. -/
theorem singleton_one_basisSplit_environment_eq_iff (i j : Fin 4) :
    ((singleton (1 : Fin 2)).basisSplitEquiv i).2 =
        ((singleton (1 : Fin 2)).basisSplitEquiv j).2 ↔
      basisBits 2 i 0 = basisBits 2 j 0 := by
  rw [basisSplit_environment_eq_iff, singleton_agreeOutside]
  constructor
  · intro h
    exact h 0 (by decide)
  · intro h p hp
    fin_cases p
    · exact h
    · exact (hp rfl).elim

/-- The forward-use form of `singleton_one_basisSplit_environment_eq_iff`. -/
theorem singleton_one_environment_eq_of_bit_eq {i j : Fin 4}
    (h : basisBits 2 i 0 = basisBits 2 j 0) :
    ((singleton (1 : Fin 2)).basisSplitEquiv i).2 =
      ((singleton (1 : Fin 2)).basisSplitEquiv j).2 :=
  (singleton_one_basisSplit_environment_eq_iff i j).2 h

/-- The inequality form of `singleton_one_basisSplit_environment_eq_iff`. -/
theorem singleton_one_environment_ne_of_bit_ne {i j : Fin 4}
    (h : basisBits 2 i 0 ≠ basisBits 2 j 0) :
    ((singleton (1 : Fin 2)).basisSplitEquiv i).2 ≠
      ((singleton (1 : Fin 2)).basisSplitEquiv j).2 :=
  mt (singleton_one_basisSplit_environment_eq_iff i j).1 h

open Classical in
theorem embedMatrix_apply_of_agreeOutside (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (i j : Fin (2 ^ n)) :
    r.embedMatrix A i j =
      A (r.extractIndex i) (r.extractIndex j) * if r.AgreeOutside i j then 1 else 0 := by
  simpa only [basisSplit_environment_eq_iff] using embedMatrix_apply r A i j

/-- Agreement outside a nested register splits into two independent requirements.

For `outer.compose inner`, the two global indices must agree (1) outside `outer` altogether and
(2) on those logical positions of `outer` that `inner` does not select.  The latter comparison is
expressed by extracting `outer`'s local basis index first. -/
theorem agreeOutside_compose_iff {m : ℕ} (outer : QRegister k n)
    (inner : QRegister m k) (i j : Fin (2 ^ n)) :
    (outer.compose inner).AgreeOutside i j ↔
      outer.AgreeOutside i j ∧
        inner.AgreeOutside (outer.extractIndex i) (outer.extractIndex j) := by
  constructor
  · intro h
    constructor
    · intro q hq
      apply h q
      intro hcomposed
      obtain ⟨logical, hlogical⟩ := hcomposed
      apply hq
      exact ⟨inner logical, hlogical⟩
    · intro q hq
      rw [basisBits_extractIndex, basisBits_extractIndex]
      apply h (outer q)
      intro hcomposed
      obtain ⟨logical, hlogical⟩ := hcomposed
      apply hq
      refine ⟨logical, ?_⟩
      exact outer.wires.injective hlogical
  · rintro ⟨houter, hinner⟩ q hq
    by_cases hqouter : q ∈ Set.range outer.wires
    · obtain ⟨logical, rfl⟩ := hqouter
      have hlogical : logical ∉ Set.range inner.wires := by
        intro hmem
        obtain ⟨selected, hselected⟩ := hmem
        apply hq
        exact ⟨selected, congrArg outer hselected⟩
      have hbits := hinner logical hlogical
      simpa only [basisBits_extractIndex] using hbits
    · exact houter q hqouter

/-- Embedding through nested registers agrees exactly with successive embedding. -/
theorem embedMatrix_compose {m : ℕ} (outer : QRegister k n) (inner : QRegister m k)
    (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    (outer.compose inner).embedMatrix A = outer.embedMatrix (inner.embedMatrix A) := by
  ext i j
  rw [embedMatrix_apply_of_agreeOutside, embedMatrix_apply_of_agreeOutside,
    embedMatrix_apply_of_agreeOutside, extractIndex_compose, extractIndex_compose,
    agreeOutside_compose_iff]
  by_cases houter : outer.AgreeOutside i j
  · by_cases hinner : inner.AgreeOutside (outer.extractIndex i) (outer.extractIndex j)
    · simp [houter, hinner]
    · simp [houter, hinner]
  · simp [houter]

/-- Applying an embedded operator can be computed entirely in the local register: the
environment component of the global output index is held fixed.  This is the operational form of
the `A ⊗ I` definition and is useful for scalable circuit proofs. -/
theorem embedMatrix_mulVec_apply (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (state : Fin (2 ^ n) → ℂ) (output : Fin (2 ^ n)) :
    (r.embedMatrix A *ᵥ state) output =
      ∑ localIndex : Fin (2 ^ k),
        A (r.extractIndex output) localIndex *
          state (r.basisSplitEquiv.symm
            (localIndex, (r.basisSplitEquiv output).2)) := by
  unfold Matrix.mulVec dotProduct
  let summand : Fin (2 ^ n) → ℂ := fun input ↦
    r.embedMatrix A output input * state input
  rw [show (∑ input, r.embedMatrix A output input * state input) =
      ∑ input, summand input by rfl]
  rw [← r.basisSplitEquiv.symm.sum_comp summand, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro localIndex _
  simp only [summand, embedMatrix_apply, Equiv.apply_symm_apply]
  have hlocal (environment : r.Environment → ZMod 2) :
      r.extractIndex (r.basisSplitEquiv.symm (localIndex, environment)) = localIndex := by
    rw [← basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  simp_rw [hlocal]
  simp

/-- Tensor a state on the selected register with a state on its physical-wire environment. -/
noncomputable def tensorState (r : QRegister k n)
    (localState : Fin (2 ^ k) → ℂ)
    (environmentState : (r.Environment → ZMod 2) → ℂ) : Fin (2 ^ n) → ℂ :=
  fun global ↦ localState (r.extractIndex global) *
    environmentState (r.basisSplitEquiv global).2

/-- Every global computational-basis vector factors canonically into the selected register's
local basis value and the complementary physical-wire environment. -/
theorem tensorState_single_factors (r : QRegister k n) (global : Fin (2 ^ n)) :
    r.tensorState (Pi.single (r.extractIndex global) 1)
        (Pi.single (r.basisSplitEquiv global).2 1) =
      (Pi.single global 1 : Fin (2 ^ n) → ℂ) := by
  funext index
  by_cases heq : index = global
  · subst index
    simp [tensorState]
  · have hsplit : ¬(r.extractIndex index = r.extractIndex global ∧
        (r.basisSplitEquiv index).2 = (r.basisSplitEquiv global).2) := by
      rintro ⟨hlocal, henv⟩
      apply heq
      apply r.basisSplitEquiv.injective
      exact Prod.ext hlocal henv
    rcases not_and_or.mp hsplit with hlocal | henv
    · simp [tensorState, Pi.single_apply, heq, hlocal]
    · simp [tensorState, Pi.single_apply, heq, henv]

/-- Replacing the local basis index gives the corresponding tensor-product basis vector while
retaining the original environment assignment. -/
theorem tensorState_single_replaceIndex (r : QRegister k n) (global : Fin (2 ^ n))
    (localIndex : Fin (2 ^ k)) :
    r.tensorState (Pi.single localIndex 1)
        (Pi.single (r.basisSplitEquiv global).2 1) =
      (Pi.single (r.replaceIndex global localIndex) 1 : Fin (2 ^ n) → ℂ) := by
  simpa using r.tensorState_single_factors (r.replaceIndex global localIndex)

/-- `tensorState` is linear in its selected-register factor. -/
theorem tensorState_smul_left (r : QRegister k n) (scalar : ℂ)
    (localState : Fin (2 ^ k) → ℂ)
    (environmentState : (r.Environment → ZMod 2) → ℂ) :
    r.tensorState (scalar • localState) environmentState =
      scalar • r.tensorState localState environmentState := by
  funext global
  simp [tensorState]
  ring

/-- `tensorState` preserves addition in its selected-register factor. -/
theorem tensorState_add_left (r : QRegister k n)
    (left right : Fin (2 ^ k) → ℂ)
    (environmentState : (r.Environment → ZMod 2) → ℂ) :
    r.tensorState (left + right) environmentState =
      r.tensorState left environmentState + r.tensorState right environmentState := by
  funext global
  simp [tensorState]
  ring

/-- `tensorState` preserves subtraction in its selected-register factor. -/
theorem tensorState_sub_left (r : QRegister k n)
    (left right : Fin (2 ^ k) → ℂ)
    (environmentState : (r.Environment → ZMod 2) → ℂ) :
    r.tensorState (left - right) environmentState =
      r.tensorState left environmentState - r.tensorState right environmentState := by
  funext global
  simp [tensorState]
  ring

/-- `tensorState` distributes over finite sums in its selected-register factor. -/
theorem tensorState_sum_left {Index : Type*} [Fintype Index]
    (r : QRegister k n) (localState : Index → Fin (2 ^ k) → ℂ)
    (environmentState : (r.Environment → ZMod 2) → ℂ) :
    r.tensorState (∑ index, localState index) environmentState =
      ∑ index, r.tensorState (localState index) environmentState := by
  funext global
  simp [tensorState, Finset.sum_mul]

/-- A register-local matrix acts only on the local factor of a tensor state. -/
theorem embedMatrix_mulVec_tensorState (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (localState : Fin (2 ^ k) → ℂ)
    (environmentState : (r.Environment → ZMod 2) → ℂ) :
    r.embedMatrix A *ᵥ r.tensorState localState environmentState =
      r.tensorState (A *ᵥ localState) environmentState := by
  funext output
  rw [embedMatrix_mulVec_apply]
  unfold tensorState Matrix.mulVec dotProduct
  have hlocal (localIndex : Fin (2 ^ k)) :
      r.extractIndex
          (r.basisSplitEquiv.symm (localIndex, (r.basisSplitEquiv output).2)) =
        localIndex := by
    rw [← basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  have henv (localIndex : Fin (2 ^ k)) :
      (r.basisSplitEquiv
          (r.basisSplitEquiv.symm (localIndex, (r.basisSplitEquiv output).2))).2 =
        (r.basisSplitEquiv output).2 := by
    rw [Equiv.apply_symm_apply]
  simp_rw [hlocal, henv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro localIndex _
  ring

/-- A register-local matrix acting on a global basis vector can be calculated entirely on the
selected local basis factor; the complementary physical wires remain fixed.

This is the common one-step form of `tensorState_single_factors` followed by
`embedMatrix_mulVec_tensorState`. -/
theorem embedMatrix_mulVec_single_factors (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (global : Fin (2 ^ n)) :
    r.embedMatrix A *ᵥ Pi.single global 1 =
      r.tensorState (A *ᵥ Pi.single (r.extractIndex global) 1)
        (Pi.single (r.basisSplitEquiv global).2 1) := by
  rw [← r.tensorState_single_factors global,
    r.embedMatrix_mulVec_tensorState]

/-- Register-local operators on disjoint wire sets commute on every state vector. -/
theorem embedMatrix_mulVec_comm_of_disjoint {m : ℕ}
    (left : QRegister k n) (right : QRegister m n) (hdisjoint : left.DisjointWires right)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (B : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)
    (state : Fin (2 ^ n) → ℂ) :
    left.embedMatrix A *ᵥ right.embedMatrix B *ᵥ state =
      right.embedMatrix B *ᵥ left.embedMatrix A *ᵥ state := by
  funext output
  rw [left.embedMatrix_mulVec_apply, right.embedMatrix_mulVec_apply]
  simp_rw [right.embedMatrix_mulVec_apply, left.embedMatrix_mulVec_apply]
  change
    (∑ leftIndex, A (left.extractIndex output) leftIndex *
      ∑ rightIndex,
        B (right.extractIndex (left.replaceIndex output leftIndex)) rightIndex *
          state (right.replaceIndex (left.replaceIndex output leftIndex) rightIndex)) =
    ∑ rightIndex, B (right.extractIndex output) rightIndex *
      ∑ leftIndex,
        A (left.extractIndex (right.replaceIndex output rightIndex)) leftIndex *
          state (left.replaceIndex (right.replaceIndex output rightIndex) leftIndex)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rightIndex _
  apply Finset.sum_congr rfl
  intro leftIndex _
  rw [right.extractIndex_replaceIndex_of_disjoint left (disjoint_comm.mp hdisjoint),
    left.extractIndex_replaceIndex_of_disjoint right hdisjoint,
    left.replaceIndex_comm_of_disjoint right hdisjoint]
  ring

/-- The algebraic frame law: embedded operators on disjoint registers commute. -/
theorem embedMatrix_comm_of_disjoint {m : ℕ}
    (left : QRegister k n) (right : QRegister m n) (hdisjoint : left.DisjointWires right)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
    (B : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    left.embedMatrix A * right.embedMatrix B =
      right.embedMatrix B * left.embedMatrix A := by
  ext output input
  have h := left.embedMatrix_mulVec_comm_of_disjoint right hdisjoint A B
    (Pi.single input 1)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact congrFun h output

/-- Embedding a diagonal register operator is the corresponding diagonal whole-system operator. -/
theorem embedMatrix_diagonal (r : QRegister k n) (diagonal : Fin (2 ^ k) → ℂ) :
    r.embedMatrix (Matrix.diagonal diagonal) =
      Matrix.diagonal (fun global ↦ diagonal (r.extractIndex global)) := by
  ext output input
  rw [embedMatrix_apply]
  by_cases heq : output = input
  · subst input
    simp
  · have hsplit : r.extractIndex output ≠ r.extractIndex input ∨
        (r.basisSplitEquiv output).2 ≠ (r.basisSplitEquiv input).2 := by
      by_contra h
      push Not at h
      apply heq
      apply r.basisSplitEquiv.injective
      exact Prod.ext h.1 h.2
    rcases hsplit with hlocal | henvironment
    · simp [heq, hlocal]
    · simp [Matrix.diagonal_apply, heq, henvironment]

/-- Pointwise action of an embedded diagonal operator. -/
theorem embedMatrix_diagonal_mulVec (r : QRegister k n)
    (diagonal : Fin (2 ^ k) → ℂ) (state : Fin (2 ^ n) → ℂ)
    (global : Fin (2 ^ n)) :
    (r.embedMatrix (Matrix.diagonal diagonal) *ᵥ state) global =
      diagonal (r.extractIndex global) * state global := by
  rw [embedMatrix_diagonal, Matrix.mulVec_diagonal]

@[simp]
theorem tensorState_zero_left (r : QRegister k n)
    (environmentState : (r.Environment → ZMod 2) → ℂ) :
    r.tensorState 0 environmentState = 0 := by
  funext global
  simp [tensorState]

@[simp]
theorem embedMatrix_zero (r : QRegister k n) : r.embedMatrix 0 = 0 := by
  simp [embedMatrix]

@[simp]
theorem embedMatrix_one (r : QRegister k n) : r.embedMatrix 1 = 1 := by
  simp [embedMatrix]

@[simp]
theorem embedMatrix_add (r : QRegister k n)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix (A + B) = r.embedMatrix A + r.embedMatrix B := by
  simp [embedMatrix, Matrix.add_kronecker, Matrix.submatrix_add]

@[simp]
theorem embedMatrix_smul (r : QRegister k n) (c : ℂ)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix (c • A) = c • r.embedMatrix A := by
  simp [embedMatrix, Matrix.smul_kronecker, Matrix.submatrix_smul]

@[simp]
theorem embedMatrix_sum {ι : Type*} (r : QRegister k n) (s : Finset ι)
    (f : ι → Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix (∑ i ∈ s, f i) = ∑ i ∈ s, r.embedMatrix (f i) := by
  induction s using Finset.cons_induction <;> simp [*]

@[simp]
theorem embedMatrix_mul (r : QRegister k n)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix (A * B) = r.embedMatrix A * r.embedMatrix B := by
  change Matrix.reindex r.basisSplitEquiv.symm r.basisSplitEquiv.symm
      ((A * B) ⊗ₖ (1 : Matrix (r.Environment → ZMod 2) (r.Environment → ZMod 2) ℂ)) = _
  rw [show (1 : Matrix (r.Environment → ZMod 2) (r.Environment → ZMod 2) ℂ) = 1 * 1 by simp]
  rw [Matrix.mul_kronecker_mul]
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ r.basisSplitEquiv.symm) _ _

@[simp]
theorem embedMatrix_conjTranspose (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix Aᴴ = (r.embedMatrix A)ᴴ := by
  simp [embedMatrix, Matrix.conjTranspose_kronecker]

@[simp]
theorem whole_embedMatrix (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    (whole n).embedMatrix A = A := by
  ext i j
  rw [embedMatrix_apply, whole_extractIndex, whole_extractIndex]
  have henv : ((whole n).basisSplitEquiv i).2 =
      ((whole n).basisSplitEquiv j).2 := by
    funext q
    exact (q.2 ⟨q.1, rfl⟩).elim
  rw [ite_eq_left henv, mul_one]

/-- Embed a proved local unitary into the whole system.  Unitarity follows once, generically,
from Kronecker-product unitarity and invariance under reindexing. -/
noncomputable def embedUnitary (r : QRegister k n) (U : Unitary (2 ^ k)) :
    Unitary (2 ^ n) :=
  ⟨r.embedMatrix U.1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      ← embedMatrix_conjTranspose, ← embedMatrix_mul]
    have hU : U.1 * U.1ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact U.2.2
    rw [hU, embedMatrix_one]⟩

@[simp]
theorem embedUnitary_val (r : QRegister k n) (U : Unitary (2 ^ k)) :
    (r.embedUnitary U).1 = r.embedMatrix U.1 := rfl

/-- Nested unitary placement is associative. -/
@[simp]
theorem embedUnitary_compose {m : ℕ} (outer : QRegister k n) (inner : QRegister m k)
    (U : Unitary (2 ^ m)) :
    (outer.compose inner).embedUnitary U = outer.embedUnitary (inner.embedUnitary U) := by
  apply Subtype.ext
  exact embedMatrix_compose outer inner U.1

@[simp]
theorem embedUnitary_one (r : QRegister k n) :
    r.embedUnitary (1 : Unitary (2 ^ k)) = 1 := by
  apply Subtype.ext
  exact r.embedMatrix_one

@[simp]
theorem embedUnitary_mul (r : QRegister k n) (U V : Unitary (2 ^ k)) :
    r.embedUnitary (U * V) = r.embedUnitary U * r.embedUnitary V := by
  apply Subtype.ext
  exact r.embedMatrix_mul U.1 V.1

@[simp]
theorem embedUnitary_inv (r : QRegister k n) (U : Unitary (2 ^ k)) :
    r.embedUnitary U⁻¹ = (r.embedUnitary U)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← r.embedUnitary_mul, inv_mul_cancel, r.embedUnitary_one]

@[simp]
theorem whole_embedUnitary (U : Unitary (2 ^ n)) :
    (whole n).embedUnitary U = U := by
  apply Subtype.ext
  exact whole_embedMatrix U.1

/-- Embed a local complete measurement into the selected wires of an `n`-qubit system. -/
@[simps]
noncomputable def embedCompleteMeasurement {m : ℕ} (r : QRegister k n)
    (ℳ : CompleteMeasurement (2 ^ k) m) : CompleteMeasurement (2 ^ n) m :=
  ⟨fun o ↦ r.embedMatrix (ℳ.1 o), by
    simp only [← r.embedMatrix_conjTranspose, ← r.embedMatrix_mul, ← r.embedMatrix_sum, ℳ.2,
      r.embedMatrix_one]⟩

end QRegister
