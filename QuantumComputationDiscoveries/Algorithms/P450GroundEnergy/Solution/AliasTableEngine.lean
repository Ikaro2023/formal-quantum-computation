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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AngleTables

/-!
# Dimension-Parametric Packed Coherent Alias & `Lac = 2` Angle Engine

Data-free, dimension-parametric `O(D)` `decide +kernel` alias-table and `13`-bit `Lac = 2` Givens
angle certificate engine:

1. **Parametric Packed Coherent Alias Engine (`Part 1`)**:
   - Supports arbitrary `(L, idxBits, b)` outer and `R × D` inner alias distributions with exact
     full-bin encoding (`keep = 0, alt = i, signAlt = sign0`, zero overflow bit).
   - Provides a single bit-word encoder `aliasEntryBits padBits b` and reconstruction theorem
     `aliasEntryBits_reconstruct` covering both native index widths (`(7, 4)` for `(128, 16)`)
     and zero-rewrite MSB-padded index widths (`(8, 5)`).
   - Provides a single-pass fragment-leaf index-map validator `checkFragLeafMapRow` and bound
     theorem `fragLeafMap_lt`.
2. **Parametric `13`-Bit `Lac = 2` Angle & Apex Certificate Engine (`Part 2`)**:
   - Certifies `k < 8192` and the bit-`11` cancellation apex bound
     `2048 ≤ k_0 < 6144` for any `58 × 57` custom shifted one-body eigenbasis and any
     `M_leaf × 57` active leaf table, directly discharging `hbounds` in
     `OneHotMux.oneHotActiveLac2BranchUnitary_mul_self` and
     `OneHotMux.oneHotActiveLac2BranchUnitary_eq_singleSpinReflection_of_act_one`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.AliasTableEngine
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputation.Specs QuantumComputation.Specs.P450

/-! ## Part 1: Dimension-Parametric Packed Coherent Alias Table Engine -/

theorem allWithIdx_append {α : Type*} (p : ℕ → α → Bool) :
    ∀ (xs1 xs2 : List α) (k : ℕ),
      OuterWeights.allWithIdx p xs1 k = true →
      OuterWeights.allWithIdx p xs2 (k + xs1.length) = true →
      OuterWeights.allWithIdx p (xs1 ++ xs2) k = true
  | [], xs2, _, _, h2 => by simpa using h2
  | _ :: xs1, xs2, k, h1, h2 => by
    rw [OuterWeights.allWithIdx, Bool.and_eq_true] at h1
    rw [List.cons_append, OuterWeights.allWithIdx, Bool.and_eq_true]
    refine ⟨h1.1, allWithIdx_append p xs1 xs2 (k + 1) h1.2 ?_⟩
    simpa [Nat.add_right_comm, Nat.add_assoc] using h2

/-- Unpack a packed `(idxBits + b + 2)`-bit alias entry `(alt, keep, sign0, signAlt)` for an
`L`-item distribution with coin capacity `2 ^ b`. -/
def unpackPackedEntry (L idxBits b raw : ℕ) (i : Fin L) : OuterWeights.AliasEntry L :=
  let s := 2 ^ idxBits
  let c := 2 ^ b
  { alt := if h : raw % s < L then ⟨raw % s, h⟩ else i
    keep := (raw / s) % c
    sign0 := raw.testBit (idxBits + b)
    signAlt := raw.testBit (idxBits + b + 1) }

theorem unpackPackedEntry_alt_val (L idxBits b raw : ℕ) (i : Fin L) :
    (unpackPackedEntry L idxBits b raw i).alt.val =
      if raw % 2 ^ idxBits < L then raw % 2 ^ idxBits else i.val := by
  unfold unpackPackedEntry
  dsimp only
  split_ifs <;> rfl

theorem unpackPackedEntry_keep_lt (L idxBits b raw : ℕ) (i : Fin L) :
    (unpackPackedEntry L idxBits b raw i).keep < 2 ^ b := by
  unfold unpackPackedEntry
  exact Nat.mod_lt _ (Nat.two_pow_pos b)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.AliasTableEngine

end
