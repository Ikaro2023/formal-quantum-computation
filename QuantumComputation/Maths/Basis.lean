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

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Computational-basis indices

This module provides the common little-endian view of computational-basis indices.
-/

@[expose] public section

/-- An assignment of computational-basis bits to `n` positions, viewed algebraically. -/
abbrev BitAssignment (n : ℕ) := Fin n → ZMod 2

/-- The binary expansion of a computational-basis index, least-significant bit first. -/
def basisBits (q : ℕ) : Fin (2 ^ q) ≃ BitAssignment q :=
  (finFunctionFinEquiv (m := 2) (n := q)).symm.trans (Equiv.piCongrRight fun _ ↦ ZMod.finEquiv 2)

/-- The bit at position `i` is the usual radix-two digit
`⌊j / 2^i⌋ mod 2`, viewed as an element of `ZMod 2`. -/
theorem basisBits_eq_div_mod (q : ℕ) (j : Fin (2 ^ q)) (i : Fin q) :
    basisBits q j i = (j.val / 2 ^ i.val % 2 : ℕ) := by
  apply ZMod.val_injective 2
  simp [basisBits, finFunctionFinEquiv, ZMod.finEquiv, ZMod.val_natCast]
  rfl

/-- `basisBits` agrees with Lean's standard natural-number bit test. -/
theorem basisBits_eq_testBit (q : ℕ) (j : Fin (2 ^ q)) (i : Fin q) :
    basisBits q j i = if j.val.testBit i.val then 1 else 0 := by
  rw [basisBits_eq_div_mod, ← Nat.toNat_testBit]
  cases j.val.testBit i.val <;> rfl

/-- `basisBits` agrees with the least-significant-bit view of Lean's fixed-width `BitVec`. -/
theorem basisBits_eq_bitVec_getLsb (q : ℕ) (j : Fin (2 ^ q)) (i : Fin q) :
    basisBits q j i = if (BitVec.ofFin j).getLsb i then 1 else 0 :=
  basisBits_eq_testBit q j i

@[simp]
theorem basisBits_zero (q : ℕ) : basisBits q 0 = 0 := by
  ext
  simp [basisBits_eq_testBit]

@[simp]
theorem basisBits_symm_zero (q : ℕ) : (basisBits q).symm 0 = 0 :=
  (basisBits q).symm_apply_eq.2 (basisBits_zero _).symm

/-- Bit-reversal permutation on `Fin (2 ^ n)`, mapping `|i₁, ..., iₙ⟩ ↦ |iₙ, ..., i₁⟩`. -/
def bitRevEquiv (n : ℕ) : Equiv.Perm (Fin (2 ^ n)) :=
  (basisBits n).symm.permCongr (Equiv.piCongrLeft' _ Fin.revPerm)

@[simp]
lemma basisBits_bitRevEquiv (n : ℕ) (j : Fin (2 ^ n)) (k : Fin n) :
    basisBits n (bitRevEquiv n j) k = basisBits n j (Fin.rev k) := by
  simp [bitRevEquiv]

/-- Reversible out-of-place addition `(x, y) ↦ (x, y + f x)` on a product type, with inverse
`(x, y) ↦ (x, y - f x)`. -/
abbrev addRightShear {α β : Type*} [AddGroup β] (f : α → β) : Equiv.Perm (α × β) :=
  Equiv.prodShear (.refl α) fun x ↦ (Equiv.subRight (f x)).symm

/-- Split an `(m + n)`-qubit computational-basis index into a pair of `m`-qubit and `n`-qubit
basis indices. -/
abbrev splitBasisEquiv (m n : ℕ) : Fin (2 ^ (m + n)) ≃ Fin (2 ^ m) × Fin (2 ^ n) :=
  (finCongr (by rw [pow_add])).trans finProdFinEquiv.symm

/-- Split a `2k`-qubit computational-basis index into a pair of `k`-qubit basis indices. -/
abbrev splitEqualBasisEquiv (k : ℕ) : Fin (2 ^ (2 * k)) ≃ Fin (2 ^ k) × Fin (2 ^ k) :=
  (finCongr (by rw [two_mul])).trans (splitBasisEquiv k k)

/-- Basis permutation on `Fin (2 ^ (m + n))` for reversible out-of-place addition
`|x⟩|b⟩ ↦ |x⟩|(b + f x) mod 2^n⟩` of a lookup table `f : Fin (2 ^ m) → Fin (2 ^ n)`. -/
abbrev tableAddPerm {m n : ℕ} (f : Fin (2 ^ m) → Fin (2 ^ n)) :
    Equiv.Perm (Fin (2 ^ (m + n))) :=
  (splitBasisEquiv m n).trans ((addRightShear f).trans (splitBasisEquiv m n).symm)

/-- Basis permutation on `Fin (2 ^ (2 * k))` for reversible out-of-place addition
`|x⟩|b⟩ ↦ |x⟩|(b + f x) mod 2^k⟩` of a lookup table `f : Fin (2 ^ k) → Fin (2 ^ k)`. -/
abbrev equalTableAddPerm {k : ℕ} (f : Fin (2 ^ k) → Fin (2 ^ k)) :
    Equiv.Perm (Fin (2 ^ (2 * k))) :=
  (splitEqualBasisEquiv k).trans ((addRightShear f).trans (splitEqualBasisEquiv k).symm)
