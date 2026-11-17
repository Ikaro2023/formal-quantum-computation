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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanSimulates

/-!
# Zero-Extra-Ancilla Binary-Tree One-Hot(`D`) Decoder
Zero-Toffoli (`TOFF = 0`, `Var = PUnit`-polymorphic) in-place binary-tree unary/one-hot
decoder (`oneHotDecodeCircuit`, `oneHotTreeProg`, `oneHotActiveCircuit`, `oneHotActiveProg`)
parameterized over any `1 ≤ D ≤ 2 ^ m` (`4 * (D - 1)` `T`-gates, `0 T` uncomputation, `0` extra
ancilla wires beyond `rOneHot`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OneHotSimulates
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat QuantumComputation.Specs Solution
open Solution.CircuitModular
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 3: In-Place Binary-Tree One-Hot(`D`) Decoder (`4 * (D - 1)` `T`, `0 TOFF`) -/

section OneHotTree

@[simp]
theorem count_cnot_t {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).count PrimitiveGate.T = 0 := by
  simp

/-- Little-endian binary evaluation of a bit vector `Fin m → ZMod 2`. -/
def bitsToNat : {m : ℕ} → (Fin m → ZMod 2) → ℕ
  | 0, _ => 0
  | k + 1, f => bitsToNat (fun i : Fin k ↦ f ⟨i.val, by omega⟩) + 2 ^ k * (f ⟨k, by omega⟩).val

theorem bitsToNat_lt_two_pow : ∀ {m : ℕ} (f : Fin m → ZMod 2), bitsToNat f < 2 ^ m
  | 0, _ => by simp [bitsToNat]
  | k + 1, f => by
      simp only [bitsToNat]
      have hlo := bitsToNat_lt_two_pow (fun i : Fin k ↦ f ⟨i.val, by omega⟩)
      have hbit : (f ⟨k, by omega⟩).val < 2 := (f ⟨k, by omega⟩).val_lt
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
      nlinarith [Nat.two_pow_pos k]

private theorem add_mul_pow_div_mod_two' {x y k i : ℕ} (hi : i < k) :
    (x + 2 ^ k * y) / 2 ^ i % 2 = x / 2 ^ i % 2 := by
  have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hi)]
  have hdiv : (x + 2 ^ k * y) / 2 ^ i = x / 2 ^ i + 2 ^ (k - i) * y := by
    rw [hpow, mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show 1 ≤ k - i by omega)
  have h2 : 2 ^ (k - i) = 2 * 2 ^ d := by
    rw [hd, Nat.pow_add, pow_one]
  rw [hdiv, h2, mul_assoc, Nat.add_mul_mod_self_left]

theorem bitsToNat_basisBits : ∀ {m : ℕ} (x : Fin (2 ^ m)), bitsToNat (basisBits m x) = x.val
  | 0, x => by
      have hx : x.val = 0 := by have := x.isLt; omega
      rw [hx]; simp [bitsToNat]
  | k + 1, x => by
      simp only [bitsToNat]
      let lo : ℕ := x.val % 2 ^ k
      let hi : ℕ := x.val / 2 ^ k
      have hlo_lt : lo < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hhi_lt : hi < 2 := by
        have hx := x.isLt
        have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
        exact Nat.div_lt_of_lt_mul (by omega)
      have hsplit : lo + 2 ^ k * hi = x.val := Nat.mod_add_div x.val (2 ^ k)
      have hfun : (fun i : Fin k ↦ basisBits (k + 1) x ⟨i.val, by omega⟩) =
          basisBits k ⟨lo, hlo_lt⟩ := by
        funext i
        simp only [basisBits_eq_div_mod]
        congr 1
        rw [← hsplit]
        exact add_mul_pow_div_mod_two' i.isLt
      have htop : (basisBits (k + 1) x ⟨k, by omega⟩).val = hi := by
        simp only [basisBits_eq_div_mod]
        have hmod : hi % 2 = hi := Nat.mod_eq_of_lt hhi_lt
        change (((hi % 2 : ℕ) : ZMod 2)).val = hi
        rw [hmod]
        exact ZMod.val_natCast_of_lt hhi_lt
      rw [hfun, bitsToNat_basisBits ⟨lo, hlo_lt⟩, htop, hsplit]

theorem bitsToNat_reg_eq_extractIndex_val {m n : ℕ} (r : QRegister m n) (β : BitAssignment n) :
    bitsToNat (fun i ↦ β (r i)) = (r.extractIndex ((basisBits n).symm β)).val := by
  let x := r.extractIndex ((basisBits n).symm β)
  have hx : basisBits m x = fun i ↦ β (r i) := by
    funext i
    simp [x, QRegister.basisBits_extractIndex]
  rw [← hx, bitsToNat_basisBits]

end OneHotTree

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OneHotSimulates

end
