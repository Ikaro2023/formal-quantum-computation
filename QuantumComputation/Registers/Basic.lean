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

public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Basic

import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Ordered quantum registers

A `QRegister k n` is an ordered view of `k` distinct logical wires inside an `n`-qubit
system.  Register order is semantically significant.  Logical wire `0` is consistently treated
as the least-significant computational-basis bit by the basis and circuit layers.
-/

@[expose] public section

/-- A physical qubit-wire label in an `n`-qubit machine.

This is an abbreviation, rather than a new wrapper type, so every theorem and constructor for
`Fin n` remains directly available.  `QRegister k n` maps logical positions to these labels. -/
abbrev Wire (n : ℕ) := Fin n

/-- An ordered selection of `k` distinct wires from an `n`-qubit system. -/
@[ext]
structure QRegister (k n : ℕ) where
  /-- The mapping from `k`-indexed wires to `n`-indexed wires. -/
  wires : Fin k ↪ Wire n

namespace QRegister

variable {n k m : ℕ}

instance : CoeFun (QRegister k n) (fun _ ↦ Fin k → Wire n) where
  coe r := r.wires

/-- The one-wire register selecting `q`. -/
@[simps -fullyApplied]
def singleton (q : Wire n) : QRegister 1 n where
  wires :=
    ⟨fun _ ↦ q, fun a b _ ↦ Subsingleton.elim a b⟩

/-- The register containing every physical wire in its existing order. -/
@[simps -fullyApplied]
def whole (n : ℕ) : QRegister n n where
  wires := Function.Embedding.refl _

/-- Select and reorder logical wires of an existing register.

`inner` is expressed in the logical coordinates of `outer`; the result is expressed in the
physical coordinates of the ambient `n`-wire system. -/
@[simps -fullyApplied]
def compose (outer : QRegister k n) (inner : QRegister m k) : QRegister m n where
  wires := inner.wires.trans outer.wires

/-- Select logical positions of an existing register using an arbitrary finite embedding. -/
abbrev subregister (r : QRegister k n) (selection : Fin m ↪ Fin k) : QRegister m n :=
  r.compose ⟨selection⟩

/-- A logical register whose entries select a contiguous ordered block of physical wires.
This is a convenience constructor for large generated layouts; algorithms remain free to relocate
the resulting local circuit onto arbitrary noncontiguous registers with `Circuit.onRegister`. -/
def block (offset width : ℕ) (h : offset + width ≤ n) : QRegister width n where
  wires := (Fin.natAddEmb offset).trans (Fin.castLEEmb h)

@[simp]
theorem block_apply_val (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (block offset width h i).val = offset + i.val := rfl

/-- An ordered two-wire register. -/
@[simps -fullyApplied]
def pair (a b : Wire n) (hab : a ≠ b) : QRegister 2 n where
  wires := ⟨![a, b], by exact Matrix.injective_pair_iff_ne.2 hab⟩

/-- An ordered three-wire register. -/
@[simps -fullyApplied]
def triple (a b c : Wire n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    QRegister 3 n where
  wires :=
    ⟨![a, b, c], by
      change Function.Injective (Fin.cons a (Fin.cons b (Fin.cons c _)))
      simp_rw [Fin.cons_injective_iff, Function.injective_of_subsingleton, Fin.range_cons,
        Matrix.range_empty]
      grind⟩

/-- The set of physical wires selected by a register. -/
def image (r : QRegister k n) : Finset (Fin n) :=
  Finset.univ.map r.wires

@[simp]
theorem mem_image (r : QRegister k n) (q : Wire n) :
    q ∈ r.image ↔ ∃ i, r i = q := by
  simp [image]

/-- The physical-wire labels not selected by a register.

This is structural register data: it does not depend on a computational-basis convention. -/
abbrev Environment (r : QRegister k n) : Type :=
  {q : Wire n // q ∉ Set.range r.wires}

instance (r : QRegister k n) : Fintype r.Environment :=
  inferInstance

/-- A physical wire outside a register is distinct from every wire selected by that register. -/
theorem ne_apply_of_not_mem_image (r : QRegister k n) (q : Wire n)
    (houtside : q ∉ r.image) (i : Fin k) : q ≠ r i := by
  intro heq
  apply houtside
  rw [mem_image]
  exact ⟨i, heq.symm⟩

/-- Two registers are disjoint when they select no common physical wire. -/
def DisjointWires (r : QRegister k n) (s : QRegister m n) : Prop :=
  Disjoint (Set.range r.wires) (Set.range s.wires)

theorem disjoint_comm {r : QRegister k n} {s : QRegister m n} :
    r.DisjointWires s ↔ s.DisjointWires r :=
  _root_.disjoint_comm

theorem disjoint_iff {r : QRegister k n} {s : QRegister m n} :
    r.DisjointWires s ↔ ∀ i j, r i ≠ s j :=
  Set.disjoint_range_iff

theorem DisjointWires.ne {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (i : Fin k) (j : Fin m) : r i ≠ s j :=
  disjoint_iff.1 h i j

/-- For `h : r.DisjointWires s`, a wire selected by the first argument `r` is outside the image of
the second argument `s`. -/
theorem DisjointWires.apply_not_mem_right {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (i : Fin k) : r i ∉ s.image := by
  intro hmem
  rw [mem_image] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact h.ne i j hj.symm

/-- For `h : r.DisjointWires s`, a wire selected by the second argument `s` is outside the image of
the first argument `r`. -/
theorem DisjointWires.apply_not_mem_left {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (j : Fin m) : s j ∉ r.image := by
  exact (disjoint_comm.mp h).apply_not_mem_right j

theorem DisjointWires.compose_right {ℓ} {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (inner : QRegister ℓ m) : r.DisjointWires (s.compose inner) := by
  rw [DisjointWires, Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  exact h.ne i (inner j) hj.symm

theorem DisjointWires.compose_left {ℓ} {r : QRegister k n} {s : QRegister m n}
    (h : r.DisjointWires s) (inner : QRegister ℓ k) :
    (r.compose inner).DisjointWires s := by
  rw [DisjointWires, Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  exact h.ne (inner i) j hj.symm


/-- Two distinct physical wires form disjoint one-wire registers. -/
theorem singleton_disjoint {left right : Wire n} (h : left ≠ right) :
    (singleton left).DisjointWires (singleton right) := by
  rw [disjoint_iff]
  intro i j hij
  fin_cases i
  fin_cases j
  exact h hij

theorem block_disjoint_of_le (leftOffset leftWidth rightOffset rightWidth : ℕ)
    (hleft : leftOffset + leftWidth ≤ n) (hright : rightOffset + rightWidth ≤ n)
    (horder : leftOffset + leftWidth ≤ rightOffset) :
    (block leftOffset leftWidth hleft).DisjointWires
      (block rightOffset rightWidth hright) := by
  rw [disjoint_iff]
  intro i j heq
  have hval := congrArg (fun q : Fin n ↦ q.val) heq
  simp only [block_apply_val] at hval
  omega

/-- A contiguous slice in the logical coordinates of an existing ordered register. -/
abbrev slice (r : QRegister k n) (offset width : ℕ) (h : offset + width ≤ k) :
    QRegister width n :=
  r.compose (block offset width h)

theorem slice_apply (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    r.slice offset width h i = r ⟨offset + i.val, by omega⟩ := rfl

theorem slice_disjoint_of_le (r : QRegister k n)
    (leftOffset leftWidth rightOffset rightWidth : ℕ)
    (hleft : leftOffset + leftWidth ≤ k) (hright : rightOffset + rightWidth ≤ k)
    (horder : leftOffset + leftWidth ≤ rightOffset) :
    (r.slice leftOffset leftWidth hleft).DisjointWires
      (r.slice rightOffset rightWidth hright) := by
  rw [disjoint_iff]
  intro i j heq
  change r (block leftOffset leftWidth hleft i) =
    r (block rightOffset rightWidth hright j) at heq
  have hindex := r.wires.injective heq
  have hval := congrArg (fun q : Fin k ↦ q.val) hindex
  change leftOffset + i.val = rightOffset + j.val at hval
  omega

/-- Concatenate two disjoint ordered registers.  Wires of `r` come first, followed by wires of
`s`; this order determines the logical bit positions of multi-qubit gates. -/
def concat (r : QRegister k n) (s : QRegister m n) (h : r.DisjointWires s) :
    QRegister (k + m) n where
  wires :=
    ⟨Sum.elim r s ∘ finSumFinEquiv.symm,
      (r.wires.injective.sumElim s.wires.injective h.ne).comp
        finSumFinEquiv.symm.injective⟩

@[simp]
theorem concat_apply_left (r : QRegister k n) (s : QRegister m n) (h : r.DisjointWires s)
    (i : Fin k) : r.concat s h (Fin.castAdd m i) = r i := by
  simp [concat]

@[simp]
theorem concat_apply_right (r : QRegister k n) (s : QRegister m n) (h : r.DisjointWires s)
    (i : Fin m) : r.concat s h (Fin.natAdd k i) = s i := by
  simp [concat]

@[simp]
theorem singleton_apply (q : Wire n) (i : Fin 1) : singleton q i = q := rfl

@[simp]
theorem whole_apply (i : Fin n) : whole n i = i := rfl

@[simp]
theorem image_singleton (q : Wire n) : (singleton q).image = {q} := by
  ext p
  simp [eq_comm]

@[simp]
theorem image_whole : (whole n).image = Finset.univ := by
  ext p
  simp

@[simp]
theorem singleton_eq_whole (q : Fin 1) : singleton q = whole 1 := by
  ext i
  fin_cases q
  fin_cases i
  rfl

@[simp]
theorem pair_zero_one_eq_whole (h : (0 : Fin 2) ≠ 1) : pair 0 1 h = whole 2 := by
  ext i
  fin_cases i <;> rfl

@[simp]
theorem compose_apply (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    outer.compose inner i = outer (inner i) := rfl

/-- A physical wire belongs to a composed register exactly when it is selected by `outer` at a
logical position selected by `inner`. -/
theorem mem_range_compose_iff (outer : QRegister k n) (inner : QRegister m k) (q : Wire n) :
    q ∈ Set.range (outer.compose inner).wires ↔
      ∃ i : Fin k, q = outer i ∧ i ∈ Set.range inner.wires := by
  constructor
  · rintro ⟨selected, rfl⟩
    exact ⟨inner selected, rfl, ⟨selected, rfl⟩⟩
  · rintro ⟨i, rfl, selected, rfl⟩
    exact ⟨selected, rfl⟩

@[simp]
theorem whole_compose (r : QRegister k n) : (whole n).compose r = r := by
  ext i
  rfl

@[simp]
theorem compose_whole (r : QRegister k n) : r.compose (whole k) = r := by
  ext i
  rfl

@[simp]
theorem compose_assoc {ℓ} (outer : QRegister k n) (middle : QRegister m k)
    (inner : QRegister ℓ m) :
    (outer.compose middle).compose inner = outer.compose (middle.compose inner) := by
  ext i
  rfl

/-- Every physical wire selected by a composed register belongs to the outer register. -/
theorem image_compose_subset (outer : QRegister k n) (inner : QRegister m k) :
    (outer.compose inner).image ⊆ outer.image := by
  intro q hq
  rw [mem_image] at hq ⊢
  obtain ⟨i, rfl⟩ := hq
  exact ⟨inner i, rfl⟩

@[simp]
theorem pair_apply_zero (a b : Wire n) (h : a ≠ b) : pair a b h 0 = a := rfl

@[simp]
theorem pair_apply_one (a b : Wire n) (h : a ≠ b) : pair a b h 1 = b := rfl

@[simp]
theorem triple_apply_zero (a b c : Wire n) (hab hac hbc) :
    triple a b c hab hac hbc 0 = a := rfl

@[simp]
theorem triple_apply_one (a b c : Wire n) (hab hac hbc) :
    triple a b c hab hac hbc 1 = b := rfl

@[simp]
theorem triple_apply_two (a b c : Wire n) (hab hac hbc) :
    triple a b c hab hac hbc 2 = c := rfl

@[simp]
theorem image_pair (a b : Wire n) (hab : a ≠ b) :
    (pair a b hab).image = {a, b} := by
  apply Finset.coe_injective
  suffices Set.range ![a, b] = {a, b} by
    convert this <;> simp [image]
  rw [Matrix.range_cons_cons_empty]

@[simp]
theorem image_triple (a b c : Wire n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (triple a b c hab hac hbc).image = {a, b, c} := by
  apply Finset.coe_injective
  suffices Set.range ![a, b, c] = {a, b, c} by
    convert this <;> simp [image]
  rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]

end QRegister
