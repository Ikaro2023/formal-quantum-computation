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

public import QuantumComputation.Primitives.Hadamard
public import QuantumComputation.Primitives.Phase
import QuantumInfo.States.Mixed.MState


/-!
# Quantum Fourier Transform operators

This module defines:
1. Bit-reversal unitary (`swapAllUnitary`).
2. Controlled-$R_k$ gates (`controlledPhaseAt`).
3. Composite circuit unitaries (`loopUnitary`, `innerLoopUnitary`, `outerLoopUnitary`, `qftUnitary`)
   and the mathematical QFT matrix (`qftMatrix`).
-/

@[expose] public section

open Operator
open scoped Matrix ComplexOrder Real

namespace QFT

/-- The `SWAP_n` unitary operator reversing the order of `n` qubits. -/
noncomputable abbrev swapAllUnitary (n : ℕ) : Unitary (2 ^ n) :=
  Operator.permutationUnitary (bitRevEquiv n)

/-- Phase exponent for the controlled-$R_k$ gate with control qubit `y` and target qubit `x`. -/
noncomputable def crPhase (n : ℕ) (y x : Fin n) (k : ℕ) (j : Fin (2 ^ n)) : ℝ :=
  ((basisBits n j y).val * (basisBits n j x).val : ℝ) / (2 ^ k : ℝ)

/-- Unitary operator for controlled-$R_k$ gate acting on control qubit `y` and target qubit `x`. -/
noncomputable abbrev controlledPhaseAt (n : ℕ) (y x : Fin n) (k : ℕ) : Unitary (2 ^ n) :=
  diagPhaseUnitary (crPhase n y x k)

/-!
## Composite QFT circuit unitaries and mathematical QFT matrix
-/

/-- Ordered product `f ⟨n - 1, _⟩ * ⋯ * f ⟨k, _⟩` for `k < n` (and `1` for `k ≥ n`). -/
noncomputable def loopUnitary {d : ℕ} (n : ℕ) (f : Fin n → Unitary d) (k : ℕ) : Unitary d :=
  if hk : k < n then
    loopUnitary n f (k + 1) * f ⟨k, hk⟩
  else 1
termination_by n - k

@[simp]
lemma loopUnitary_of_ge {d : ℕ} (n : ℕ) (f : Fin n → Unitary d) {k : ℕ} (hk : n ≤ k) :
    loopUnitary n f k = 1 := by
  rw [loopUnitary, dite_eq_right (by omega)]

lemma loopUnitary_step {d : ℕ} (n : ℕ) (f : Fin n → Unitary d) {k : ℕ} (hk : k < n) :
    loopUnitary n f k = loopUnitary n f (k + 1) * f ⟨k, hk⟩ := by
  rw [loopUnitary, dite_eq_left hk]

lemma loopUnitary_mulVec {d : ℕ} (n : ℕ) (f : Fin n → Unitary d)
    (state : ℕ → Fin d → ℂ) {m₀ m : ℕ} (hm₀ : m₀ ≤ m) (hm : m ≤ n)
    (hstep : ∀ k (hk : k < n), m₀ ≤ k → (f ⟨k, hk⟩).1 *ᵥ state k = state (k + 1)) :
    (loopUnitary n f m).1 *ᵥ state m = state n := by
  have haux : ∀ rem m : ℕ, n - m = rem → m₀ ≤ m → m ≤ n →
      (loopUnitary n f m).1 *ᵥ state m = state n := by
    intro rem
    induction rem with
    | zero =>
        intro m hrem _ hm
        have hmn : m = n := by omega
        subst m
        simp
    | succ r ih =>
        intro m hrem hm₀ hm
        have hlt : m < n := by omega
        rw [loopUnitary_step n f hlt, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          hstep m hlt hm₀]
        exact ih (m + 1) (by omega) (by omega) (by omega)
  exact haux (n - m) m rfl hm₀ hm

lemma embedUnitary_loopUnitary {n m : ℕ} (r : QRegister n m)
    (f : Fin n → Unitary (2 ^ n)) (k : ℕ) :
    loopUnitary n (fun idx ↦ r.embedUnitary (f idx)) k =
      r.embedUnitary (loopUnitary n f k) := by
  have haux : ∀ rem k : ℕ, n - k = rem →
      loopUnitary n (fun idx ↦ r.embedUnitary (f idx)) k =
        r.embedUnitary (loopUnitary n f k) := by
    intro rem
    induction rem with
    | zero =>
        intro k hrem
        simp [loopUnitary_of_ge n _ (by omega : n ≤ k)]
    | succ rem ih =>
        intro k hrem
        have hk : k < n := by omega
        rw [loopUnitary_step n _ hk, loopUnitary_step n f hk, r.embedUnitary_mul,
          ih (k + 1) (by omega)]
  exact haux (n - k) k rfl

/-- Generic inner loop unitary starting at index `m`. -/
noncomputable def innerLoopUnitaryGen {d : ℕ} (n : ℕ)
    (crGate : Fin n → Fin n → ℕ → Unitary d) (ℓ : Fin n) (m : ℕ) : Unitary d :=
  loopUnitary n (fun idx ↦ crGate idx ℓ (idx.val - ℓ.val + 1)) m

/-- Generic outer loop unitary starting at index `ℓ`. -/
noncomputable def outerLoopUnitaryGen {d : ℕ} (n : ℕ)
    (hGate : Fin n → Unitary d) (crGate : Fin n → Fin n → ℕ → Unitary d) (ℓ : ℕ) : Unitary d :=
  loopUnitary n (fun idx ↦ innerLoopUnitaryGen n crGate idx (idx.val + 1) * hGate idx) ℓ

/-- Generic QFT circuit unitary: `swapGate` first, then the outer loop. -/
noncomputable def qftCircuitUnitaryGen {d : ℕ} (n : ℕ)
    (hGate : Fin n → Unitary d) (crGate : Fin n → Fin n → ℕ → Unitary d)
    (swapGate : Unitary d) : Unitary d :=
  outerLoopUnitaryGen n hGate crGate 0 * swapGate

/-- Unitary transformation performed by the remaining inner loop starting at index `m` (0-indexed).
-/
noncomputable abbrev innerLoopUnitary (n : ℕ) (ℓ : Fin n) (m : ℕ) : Unitary (2 ^ n) :=
  innerLoopUnitaryGen n (controlledPhaseAt n) ℓ m

/-- Unitary transformation performed by the remaining outer loop starting at index `ℓ` (0-indexed).
-/
noncomputable abbrev outerLoopUnitary (n : ℕ) (ℓ : ℕ) : Unitary (2 ^ n) :=
  outerLoopUnitaryGen n (hadamardAt n) (controlledPhaseAt n) ℓ

/-- Complete $n$-qubit Quantum Fourier Transform circuit unitary: `SWAP_n` followed by the outer
loop from `0` to `n - 1`.

Qubit `0` is the least significant bit of a basis index (`basisBits`). The textbook circuit (outer
loop, then `SWAP_n`) reads qubit `0` as the most significant bit instead; applying `SWAP_n` first
makes this unitary equal to `qftMatrix n` (`val_qftUnitary`) in the library's bit order. -/
noncomputable abbrev qftUnitary (n : ℕ) : Unitary (2 ^ n) :=
  qftCircuitUnitaryGen n (hadamardAt n) (controlledPhaseAt n) (swapAllUnitary n)

/-- The mathematical $n$-qubit Quantum Fourier Transform matrix:
$(\text{QFT}_n)_{k, j} = \frac{1}{\sqrt{2^n}} e^{2\pi i j k / 2^n}$. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun k j ↦
    (1 / √(2 ^ n) : ℂ) *
      Complex.exp (2 * π * Complex.I * ((j.val * k.val : ℝ) / (2 ^ n : ℝ)))

end QFT
