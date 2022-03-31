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

public import QuantumComputation.Registers.Basic
public import QuantumComputation.Maths.Basis
public import Mathlib.Logic.Equiv.Fintype

/-!
# Computational-basis views for registers

This module fixes the common little-endian basis convention and splits a whole-system basis
index into the bits selected by a register and the untouched environment bits.  The environment
is indexed by physical wires outside the register; no arithmetic identification with
`Fin (2^(n-k))` is needed for local gate embedding.
-/

@[expose] public section

namespace QRegister

variable {n k : ℕ}

/-- Split physical wires into the ordered logical register and its physical-wire complement. -/
noncomputable def wireEquiv (r : QRegister k n) :
    Fin k ⊕ r.Environment ≃ Wire n :=
  (Equiv.sumCongr r.wires.toEquivRange (Equiv.refl r.Environment)).trans
    (Equiv.Set.sumCompl (Set.range r.wires))

@[simp]
theorem wireEquiv_apply_left (r : QRegister k n) (i : Fin k) :
    r.wireEquiv (Sum.inl i) = r i := rfl

@[simp]
theorem wireEquiv_apply_right (r : QRegister k n) (i : r.Environment) :
    r.wireEquiv (Sum.inr i) = i.1 := rfl

/-- Split a global bit vector into ordered register bits and untouched environment bits. -/
noncomputable def bitSplitEquiv (r : QRegister k n) :
    BitAssignment n ≃ BitAssignment k × (r.Environment → ZMod 2) :=
  ((r.wireEquiv.arrowCongr (Equiv.refl (ZMod 2))).symm).trans
    (Equiv.sumArrowEquivProdArrow (Fin k) r.Environment (ZMod 2))

@[simp]
theorem bitSplitEquiv_apply_fst (r : QRegister k n) (b : BitAssignment n)
    (i : Fin k) : (r.bitSplitEquiv b).1 i = b (r i) := by
  rfl

@[simp]
theorem bitSplitEquiv_apply_snd (r : QRegister k n) (b : BitAssignment n)
    (i : r.Environment) : (r.bitSplitEquiv b).2 i = b i.1 := by
  rfl

/-- Split a whole-system basis index into a local basis index and environment bits. -/
noncomputable def basisSplitEquiv (r : QRegister k n) :
    Fin (2 ^ n) ≃ Fin (2 ^ k) × (r.Environment → ZMod 2) :=
  (basisBits n).trans <|
    r.bitSplitEquiv.trans <|
      Equiv.prodCongr (basisBits k).symm
        (Equiv.refl (r.Environment → ZMod 2))

/-- Extract the computational-basis index seen by an ordered register. -/
def extractIndex (r : QRegister k n) (j : Fin (2 ^ n)) : Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ basisBits n j (r i))

@[simp]
theorem basisBits_extractIndex (r : QRegister k n) (j : Fin (2 ^ n)) (i : Fin k) :
    basisBits k (r.extractIndex j) i = basisBits n j (r i) := by
  simp [extractIndex]

/-- Extracting through a nested register is the same as extracting at each level. -/
@[simp]
theorem extractIndex_compose {m : ℕ} (outer : QRegister k n) (inner : QRegister m k)
    (j : Fin (2 ^ n)) :
    (outer.compose inner).extractIndex j = inner.extractIndex (outer.extractIndex j) := by
  simp [extractIndex]

@[simp]
theorem basisSplitEquiv_apply_fst (r : QRegister k n) (j : Fin (2 ^ n)) :
    (r.basisSplitEquiv j).1 = r.extractIndex j := by
  rfl

@[simp]
theorem basisSplitEquiv_apply_snd (r : QRegister k n) (j : Fin (2 ^ n))
    (i : r.Environment) :
    (r.basisSplitEquiv j).2 i = basisBits n j i.1 := by
  rfl

/-- Replace the local basis value selected by a register while retaining every environment bit. -/
noncomputable def replaceIndex (r : QRegister k n) (global : Fin (2 ^ n))
    (localIndex : Fin (2 ^ k)) : Fin (2 ^ n) :=
  r.basisSplitEquiv.symm (localIndex, (r.basisSplitEquiv global).2)

@[simp]
theorem basisSplitEquiv_replaceIndex (r : QRegister k n) (global : Fin (2 ^ n))
    (localIndex : Fin (2 ^ k)) :
    r.basisSplitEquiv (r.replaceIndex global localIndex) =
      (localIndex, (r.basisSplitEquiv global).2) := by
  simp [replaceIndex]

@[simp]
theorem extractIndex_replaceIndex (r : QRegister k n) (global : Fin (2 ^ n))
    (localIndex : Fin (2 ^ k)) :
    r.extractIndex (r.replaceIndex global localIndex) = localIndex := by
  rw [← basisSplitEquiv_apply_fst, basisSplitEquiv_replaceIndex]

/-- Replacing a register sets each selected physical bit to the corresponding logical bit. -/
theorem basisBits_replaceIndex_apply (r : QRegister k n) (global : Fin (2 ^ n))
    (localIndex : Fin (2 ^ k)) (i : Fin k) :
    basisBits n (r.replaceIndex global localIndex) (r i) =
      basisBits k localIndex i := by
  rw [← basisBits_extractIndex, extractIndex_replaceIndex]

/-- Replacing a register leaves every unselected physical bit unchanged. -/
theorem basisBits_replaceIndex_of_not_mem (r : QRegister k n)
    (global : Fin (2 ^ n)) (localIndex : Fin (2 ^ k)) (q : Wire n)
    (houtside : q ∉ Set.range r.wires) :
    basisBits n (r.replaceIndex global localIndex) q = basisBits n global q :=
  congr($(r.basisSplitEquiv_replaceIndex global localIndex).2 ⟨q, houtside⟩)

/-- Replacing a register by the value it already has leaves the global basis index unchanged. -/
@[simp]
theorem replaceIndex_extractIndex (r : QRegister k n) (global : Fin (2 ^ n)) :
    r.replaceIndex global (r.extractIndex global) = global := by
  simp [replaceIndex, ← basisSplitEquiv_apply_fst]

/-- A second replacement of the same register supersedes the first one. -/
@[simp]
theorem replaceIndex_replaceIndex (r : QRegister k n) (global : Fin (2 ^ n))
    (first second : Fin (2 ^ k)) :
    r.replaceIndex (r.replaceIndex global first) second =
      r.replaceIndex global second := by
  simp [replaceIndex]

/-- Updates of disjoint logical registers commute exactly. -/
theorem replaceIndex_comm_of_disjoint {m : ℕ}
    (left : QRegister k n) (right : QRegister m n) (hdisjoint : left.DisjointWires right)
    (global : Fin (2 ^ n)) (leftIndex : Fin (2 ^ k)) (rightIndex : Fin (2 ^ m)) :
    left.replaceIndex (right.replaceIndex global rightIndex) leftIndex =
      right.replaceIndex (left.replaceIndex global leftIndex) rightIndex := by
  apply (basisBits n).injective
  funext q
  by_cases hleft : q ∈ Set.range left.wires
  · rcases hleft with ⟨i, rfl⟩
    rw [left.basisBits_replaceIndex_apply,
      right.basisBits_replaceIndex_of_not_mem _ _ _ (Set.disjoint_left.mp hdisjoint ⟨i, rfl⟩),
      left.basisBits_replaceIndex_apply]
  · by_cases hright : q ∈ Set.range right.wires
    · rcases hright with ⟨j, rfl⟩
      rw [left.basisBits_replaceIndex_of_not_mem _ _ _ hleft,
        right.basisBits_replaceIndex_apply, right.basisBits_replaceIndex_apply]
    · simp [left.basisBits_replaceIndex_of_not_mem _ _ _ hleft,
        right.basisBits_replaceIndex_of_not_mem _ _ _ hright]

/-- Replacing one register's local basis value does not change the value read through a disjoint
register. -/
theorem extractIndex_replaceIndex_of_disjoint {m : ℕ}
    (left : QRegister k n) (right : QRegister m n) (hdisjoint : left.DisjointWires right)
    (global : Fin (2 ^ n)) (localIndex : Fin (2 ^ m)) :
    left.extractIndex (right.replaceIndex global localIndex) = left.extractIndex global := by
  apply (basisBits k).injective
  funext i
  rw [basisBits_extractIndex, basisBits_extractIndex]
  exact right.basisBits_replaceIndex_of_not_mem global localIndex (left i)
    (Set.disjoint_left.mp hdisjoint ⟨i, rfl⟩)

@[simp]
theorem whole_extractIndex (j : Fin (2 ^ n)) :
    (whole n).extractIndex j = j := by
  simp [extractIndex]

end QRegister
