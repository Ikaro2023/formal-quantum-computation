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
public import QuantumComputation.Maths.Basis
public import QuantumComputation.Registers.Embed
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Hadamard primitive

This module defines the Walsh character `walshChar`, the unnormalized integer Walsh--Hadamard
matrix `walshMatrix`, and the normalized complex Walsh--Hadamard transform `hadamardMatrix`, and
proves that the latter is unitary.
-/

@[expose] public section

open scoped Matrix


section walsh
variable (m : Type*) [Fintype m]

/-- The Walsh character `(a, b) ↦ (-1) ^ (a ⬝ᵥ b)` on `m → ZMod 2`, curried as an `AddChar`. -/
@[simps]
def walshChar : AddChar (m → ZMod 2) (AddChar (m → ZMod 2) ℤˣ) where
  toFun a :=
    { toFun b := (-1 : ℤˣ) ^ (a ⬝ᵥ b)
      map_zero_eq_one' := by simp
      map_add_eq_mul' x y := by rw [dotProduct_add, uzpow_add] }
  map_zero_eq_one' := by ext; simp
  map_add_eq_mul' x y := by ext; simp [add_dotProduct, uzpow_add]

lemma walshChar_injective : Function.Injective (walshChar m) := by
  have hinj : Function.Injective ((-1 : ℤˣ) ^ · : ZMod 2 → ℤˣ) := by decide
  intro a b h
  funext i
  apply hinj
  classical
  simpa using congr($h (Pi.single i 1))

/-- The unnormalized Walsh--Hadamard matrix with entries `±1 : ℤ`, indexed by `m → ZMod 2`. -/
def walshMatrix : Matrix (m → ZMod 2) (m → ZMod 2) ℤ :=
  .of fun i j ↦ ↑(walshChar m i j)

@[simp] theorem walshMatrix_apply (i j : m → ZMod 2) : walshMatrix m i j = walshChar m i j := rfl

@[simp]
theorem walshMatrix_transpose : (walshMatrix m)ᵀ = walshMatrix m := by
  ext j k
  simp [dotProduct_comm]

theorem walshMatrix_mul_transpose [DecidableEq m] :
    walshMatrix m * (walshMatrix m)ᵀ = 2 ^ Fintype.card m := by
  rw [← Matrix.diagonal_ofNat, Matrix.diagonal_pow]
  ext j k
  trans ∑ x, walshChar m (j + k) x
  · simp_rw [Matrix.mul_apply, Matrix.transpose_apply, walshMatrix_apply, ← Units.val_mul,
      ← AddChar.mul_apply, ← AddChar.map_add_eq_mul]
  · have h0 : (Units.coeHom ℤ).compAddChar (walshChar m 0) = 0 := by ext; simp
    have hsum := ((Units.coeHom ℤ).compAddChar (walshChar m (j + k))).sum_eq_ite
    simp_rw [((Units.coeHom ℤ).compAddChar_injective_right Units.val_injective).eq_iff' h0,
      (walshChar_injective m).eq_iff, add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hsum
    simpa [Matrix.diagonal_apply] using hsum

@[simp]
theorem walshMatrix_mul_self [DecidableEq m] :
    walshMatrix m * walshMatrix m = 2 ^ Fintype.card m := by
  simpa only [walshMatrix_transpose] using walshMatrix_mul_transpose m

end walsh

/-- The normalized Walsh--Hadamard matrix `H^{⊗q}`, indexed by `Fin (2 ^ q)`. -/
noncomputable def hadamardMatrix (q : ℕ) : Matrix (Fin (2 ^ q)) (Fin (2 ^ q)) ℂ :=
  (1 / √(2 ^ q) : ℂ) • ((walshMatrix (Fin q)).submatrix (basisBits q) (basisBits q)).map Int.cast

@[simp]
theorem hadamardMatrix_apply (q : ℕ) (i j : Fin (2 ^ q)) :
    hadamardMatrix q i j = (1 / √(2 ^ q) : ℂ) • walshMatrix _ (basisBits q i) (basisBits q j) := by
  simp [hadamardMatrix]

@[simp]
theorem hadamardMatrix_conjTranspose (q : ℕ) : (hadamardMatrix q)ᴴ = hadamardMatrix q := by
  ext j k
  simp [dotProduct_comm]

@[simp]
theorem hadamardMatrix_mul_self (q : ℕ) : hadamardMatrix q * hadamardMatrix q = 1 := by
  rw [hadamardMatrix, smul_mul_smul, complex_one_div_sqrt_mul_self (2 ^ q) (by positivity)]
  simp [← Int.coe_castRingHom, ← Matrix.map_mul, ← Matrix.diagonal_ofNat, Matrix.diagonal_pow,
    Matrix.smul_eq_diagonal_mul]

theorem hadamardMatrix_mem_unitaryGroup (q : ℕ) :
    hadamardMatrix q ∈ Matrix.unitaryGroup (Fin (2 ^ q)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hadamardMatrix_conjTranspose,
    hadamardMatrix_mul_self]

/-- `hadamardMatrix q` bundled as a `Unitary (2 ^ q)`. -/
@[simps]
noncomputable def hadamardUnitary {q : ℕ} : Operator.Unitary (2 ^ q) :=
  ⟨hadamardMatrix q, hadamardMatrix_mem_unitaryGroup q⟩

open Operator in
/-- Unitary operator for single-qubit Hadamard gate acting on qubit `x : Fin q`. -/
noncomputable abbrev hadamardAt (q : ℕ) (x : Fin q) : Unitary (2 ^ q) :=
  (QRegister.singleton x).embedUnitary hadamardUnitary

lemma hadamardAt_apply (q : ℕ) (x : Fin q) (i j : Fin (2 ^ q)) :
    (hadamardAt q x).1 i j =
      if ∀ m ≠ x, basisBits q i m = basisBits q j m then
        (1 / √2 : ℂ) * ↑((-1 : ℤˣ) ^ (basisBits q i x * basisBits q j x))
      else 0 := by
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside,
    QRegister.singleton_agreeOutside]
  simp [dotProduct, QRegister.basisBits_extractIndex (k := 1)]

/-- The first Hadamard column is the uniform superposition. -/
theorem hadamardMatrix_apply_zero (q : ℕ) (i : Fin (2 ^ q)) :
    hadamardMatrix q i 0 = (1 / √(2 ^ q) : ℂ) := by
  simp

/-- The first Hadamard row is the uniform superposition. -/
theorem hadamardMatrix_zero_apply (q : ℕ) (j : Fin (2 ^ q)) :
    hadamardMatrix q 0 j = (1 / √(2 ^ q) : ℂ) := by
  simp

/-- Every Hadamard entry has squared modulus `1 / 2^q`, independently of its sign. -/
theorem hadamardMatrix_star_mul_self (q : ℕ) (i j : Fin (2 ^ q)) :
    star (hadamardMatrix q i j) * hadamardMatrix q i j = (1 / (2 ^ q : ℝ) : ℂ) := by
  rw [hadamardMatrix_apply, star_smul, star_intCast, smul_mul_smul, ← Int.cast_mul,
    walshMatrix_apply, ← Units.val_mul, Int.units_mul_self]
  simpa [one_div] using complex_one_div_sqrt_mul_self (2 ^ q) (by positivity)
