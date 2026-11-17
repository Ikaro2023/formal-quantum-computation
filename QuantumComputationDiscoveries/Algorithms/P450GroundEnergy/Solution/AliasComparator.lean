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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasTreeSwap

/-!
# Gidney Ripple-Borrow Comparator & Controlled-SWAP

Provides `TOFF = 0` clean-ancilla dynamic circuits (`CleanRealizes`) for Section 3 of coherent
alias-sampling state preparation:
1. Basis-ket permutation algebra (`bitPermUnitary`, `ket_X`, `ket_CNOT`, `ket_TOFF`,
   `CleanRealizes.absorb_clean_buffer`) and little-endian binary step lemmas.
2. `b`-bit Gidney ripple-borrow comparator `coinGeKeepProg` (`4 * b` `T` gates, `0` `TOFF`, `b`
   clean scratch wires) realizing the self-inverse `coinGeKeepUnitary b` (`out ⊕= [coin ≥ keep]`),
   plus `(b + 1)`-bit threshold variant `coinGeKeepExtProg` (`4 * (b + 1)` `T` gates).
3. `d`-pair controlled-SWAP `cSwapPairsProg` (`4 * d` `T` gates, `0` `TOFF`, `1` clean scratch
   wire) realizing the self-inverse `cSwapPairsUnitary d`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450
namespace CoherentAlias

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ### Basis-Ket Permutation Algebra & Buffer Absorption -/

theorem qreg_ext {k n : ℕ} {r₁ r₂ : QRegister k n}
    (h : ∀ i : Fin k, (r₁ i).val = (r₂ i).val) : r₁ = r₂ :=
  QRegister.ext (Function.Embedding.ext fun i ↦ Fin.ext (h i))

/-- Construct a `QRegister A B` from an injective wire-index function. -/
def mkReg {A B : ℕ} (f : Fin A → ℕ) (hb : ∀ i : Fin A, f i < B)
    (hi : ∀ i j : Fin A, f i = f j → i.val = j.val) : QRegister A B where
  wires := ⟨fun i ↦ ⟨f i, hb i⟩, fun i j hij ↦ Fin.ext (hi i j (congrArg Fin.val hij))⟩

@[simp]
theorem mkReg_apply_val {A B : ℕ} (f : Fin A → ℕ) (hb : ∀ i : Fin A, f i < B)
    (hi : ∀ i j : Fin A, f i = f j → i.val = j.val) (i : Fin A) :
    (mkReg f hb hi i).val = f i := rfl

theorem zmod2_add_cancel_right (a b : ZMod 2) : a + b + b = a := by
  rw [add_assoc, zmod2_add_self, add_zero]

@[simp]
theorem writeReg_whole {n : ℕ} (β γ : BitAssignment n) :
    writeReg β (QRegister.whole n) γ = γ :=
  funext fun w ↦ writeReg_apply_reg β (QRegister.whole n) γ w

@[simp] theorem count_X_t {n : ℕ} (q : Wire n) : (Circuit.X q).count .T = 0 := rfl
@[simp] theorem count_X_toff {n : ℕ} (q : Wire n) : (Circuit.X q).count .TOFF = 0 := rfl
@[simp] theorem count_CNOT_t {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).count .T = 0 := rfl
@[simp] theorem count_CNOT_toff {n : ℕ} (c t : Wire n) (h : c ≠ t) :
    (Circuit.CNOT c t h).count .TOFF = 0 := rfl
@[simp] theorem count_TOFF_t {n : ℕ} (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t)
    (h₂t : c₂ ≠ t) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).count .T = 0 := rfl
@[simp] theorem count_TOFF_toff {n : ℕ} (c₁ c₂ t : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t)
    (h₂t : c₂ ≠ t) : (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).count .TOFF = 1 := rfl

/-- Unitary on `k` qubits induced by a classical reversible `BitAssignment k` permutation. -/
noncomputable abbrev bitPermUnitary {k : ℕ} (e : Equiv.Perm (BitAssignment k)) :
    Unitary (2 ^ k) :=
  Operator.permutationUnitary (((basisBits k).trans e).trans (basisBits k).symm)

theorem bitPermUnitary_mul_self {k : ℕ} (e : Equiv.Perm (BitAssignment k))
    (he : ∀ γ, e (e γ) = γ) :
    bitPermUnitary e * bitPermUnitary e = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  change ((bitPermUnitary e).1 * (bitPermUnitary e).1) *ᵥ ket β =
    (1 : Operator (2 ^ k)) *ᵥ ket β
  rw [← Matrix.mulVec_mulVec, ket, basisState, Operator.permutationUnitary_mulVec_single,
    Operator.permutationUnitary_mulVec_single, Matrix.one_mulVec]
  simp [he]

theorem bitPermUnitary_inv_of_involutive {k : ℕ} (e : Equiv.Perm (BitAssignment k))
    (he : ∀ γ, e (e γ) = γ) :
    (bitPermUnitary e)⁻¹ = bitPermUnitary e :=
  (eq_inv_of_mul_eq_one_left (bitPermUnitary_mul_self e he)).symm

theorem embedUnitary_bitPermUnitary_mulVec_ket {n k : ℕ} (r : QRegister k n)
    (e : Equiv.Perm (BitAssignment k)) (β : BitAssignment n) :
    (r.embedUnitary (bitPermUnitary e)).1 *ᵥ ket β =
      ket (writeReg β r (e (fun i ↦ β (r i)))) := by
  have hext : r.extractIndex ((basisBits n).symm β) =
      (basisBits k).symm (fun i ↦ β (r i)) := by
    simp [QRegister.extractIndex]
  rw [ket, basisState, QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
    hext, Operator.permutationUnitary_mulVec_single]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [r.tensorState_single_replaceIndex]
  simp [writeReg, ket, basisState]

/-! ### Little-Endian Cons Split & Ripple-Borrow Step Identity -/

end CoherentAlias
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
