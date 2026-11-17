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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputation.Maths.Basis

/-!
# Classical Angle & Alias Lookup Tables

`1 MB`-stack-safe packaging of all classical Givens rotation angles and Robin-Hood / Walker
coherent alias-sampling tables for `P450DFTHCData`, with `decide +kernel`
bridge theorems:

1. **Unified & Group-Factored `13`-Bit Angle Tables**: `leafAngleBits`, `oneBodyAngleBits`,
   `combinedAngleBits` (+ `ℕ`, `Fin (2 ^ 13)`, `BitVec 13`, `basisBits 13`, and `givensLeaf 15`
   bridges to `leafVector` and `oneBodyVector`).
2. **Micro-Batched Turnaround Schedule (`batchSlice`)**: parametric `K`-batching (`K = 19, 12,
   10, 6`) loading turnaround batch `0` (`p = 0 .. K - 1`) once across `G(u)† (±Z_{0,σ}) G(u)`.
3. **Precomputed Robin-Hood / Walker Exact Integer Alias Tables**: `outerAliasTable` (`184` items,
   coin capacity `1024`, sum `188,416`) and `innerAliasTable` (`126 × 30` items, coin capacity
   `512`, sum `15,360`), with exact bin-sum, coin-counting, and sign identities.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OuterWeights
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputation.Specs QuantumComputation.Specs.P450

/-! ## Part 1: Bit Reconstruction, `givensLeaf`, and Single-Pass Array Helpers -/

/-- Single-pass indexed sum `∑_{i < xs.length} f (k + i) xs[i]` avoiding repeated `Array.getD` list
walks during `decide +kernel` reduction. -/
def sumWithIdx {α : Type*} (f : ℕ → α → ℕ) : List α → ℕ → ℕ
  | [], _ => 0
  | x :: rest, k => f k x + sumWithIdx f rest (k + 1)

/-- Single-pass indexed universal check `∀ i < xs.length, p (k + i) xs[i]`. -/
def allWithIdx {α : Type*} (p : ℕ → α → Bool) : List α → ℕ → Bool
  | [], _ => true
  | x :: rest, k => p k x && allWithIdx p rest (k + 1)

theorem sumWithIdx_eq_map_finRange {α : Type*} (f : ℕ → α → ℕ) (xs : List α) (k : ℕ) :
    sumWithIdx f xs k =
      ((List.finRange xs.length).map fun i ↦ f (k + i.val) (xs.get i)).sum := by
  induction xs generalizing k with
  | nil => simp [sumWithIdx]
  | cons x rest ih =>
    change f k x + sumWithIdx f rest (k + 1) =
      ((List.finRange (rest.length + 1)).map fun i ↦ f (k + i.val) ((x :: rest).get i)).sum
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, ih (k + 1)]
    simp only [Fin.val_zero, Nat.add_zero, List.get_eq_getElem, List.getElem_cons_zero]
    congr 1
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Fin.val_succ, List.getElem_cons_succ]
    have hk : k + (i.val + 1) = k + 1 + i.val := by omega
    rw [hk]

theorem sumWithIdx_array_eq_fin_sum {α : Type*} (f : ℕ → α → ℕ) (arr : Array α) (d : α)
    {L : ℕ} (hL : arr.size = L) :
    sumWithIdx f arr.toList 0 = ∑ i : Fin L, f i.val (arr.getD i.val d) := by
  subst hL
  rw [sumWithIdx_eq_map_finRange, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  have hi : i.val < arr.size := i.isLt
  simp only [Nat.zero_add, Array.getD, Array.getInternal, hi, ↓reduceDIte, List.get_eq_getElem]

theorem allWithIdx_getElem {α : Type*} {p : ℕ → α → Bool} {xs : List α} {k : ℕ}
    (hall : allWithIdx p xs k = true) {i : ℕ} (hi : i < xs.length) :
    p (k + i) (xs[i]'hi) = true := by
  induction xs generalizing k i with
  | nil => contradiction
  | cons x rest ih =>
    rw [allWithIdx, Bool.and_eq_true] at hall
    cases i with
    | zero => simpa using hall.1
    | succ i =>
      have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
      have h := ih hall.2 hi'
      have hk : k + (i + 1) = k + 1 + i := by omega
      simpa [hk] using h

theorem allWithIdx_array_getD {α : Type*} {p : ℕ → α → Bool} {arr : Array α}
    (hall : allWithIdx p arr.toList 0 = true) {i : ℕ} (hi : i < arr.size) (d : α) :
    p i (arr.getD i d) = true := by
  simp only [Array.getD, Array.getInternal, hi, ↓reduceDIte, List.get_eq_getElem]
  simpa using allWithIdx_getElem hall hi

/-- Pure-`ℕ` kernel-primitive equivalent of `(fromOffset w).natAbs`. -/
def natAbsOffset (w : ℕ) : ℕ := (16384 - w) + (w - 16384)

theorem natAbsOffset_eq (w : ℕ) : natAbsOffset w = (fromOffset w).natAbs := by
  unfold natAbsOffset fromOffset
  omega

/-! ## Part 2: Unified & Group-Factored `13`-Bit Angle Tables -/

/-- Precomputed coherent alias-sampling row `(alt, keep, sign0, signAlt)` for an `L`-item
distribution with power-of-two integer coin capacity (`1024` for outer, `512` for inner). -/
structure AliasEntry (L : ℕ) where
  /-- Alternate item index selected when `coin ≥ keep`. -/
  alt : Fin L
  /-- Integer threshold strictly below `capacity` (`< 1024` for outer, `< 512` for inner). -/
  keep : ℕ
  /-- Sign bit (`true` iff negative) of primary item `i`. -/
  sign0 : Bool
  /-- Sign bit (`true` iff negative) of alternate item `alt`. -/
  signAlt : Bool
  deriving DecidableEq

/-- Unpack a packed `20`-bit outer alias integer (`capacity = 1024`) at index `i : Fin 184`. -/
def unpackOuterEntry (raw : ℕ) (i : Fin 184) : AliasEntry 184 :=
  { alt := if h : raw % 256 < 184 then ⟨raw % 256, h⟩ else i
    keep := (raw / 256) % 1024
    sign0 := raw.testBit 18
    signAlt := raw.testBit 19 }

/-- Flat fragment index `14 * r + c ∈ Fin 126` for `(r : Fin 9, c : Fin 14)`. -/
abbrev fragFlatIdx (r : Fin 9) (c : Fin 14) : Fin 126 := ⟨14 * r.val + c.val, by omega⟩

/-- Outer item index `58 + 14 * r + c ∈ Fin 184` for two-body fragment `(r, c)`. -/
abbrev outerFragIdx (r : Fin 9) (c : Fin 14) : Fin 184 := ⟨58 + 14 * r.val + c.val, by omega⟩

/-- Outer item index `ℓ ∈ Fin 184` (`0..57`) for one-body eigencomponent `ℓ : Fin 58`. -/
abbrev outerOneBodyIdx (ℓ : Fin 58) : Fin 184 := ⟨ℓ.val, by omega⟩

/-- Exact unsigned integer weight of outer item `x : Fin 184` (`oneBodyWeights` on `0..57`,
`fragmentWeights` on `58..183`). -/
def outerTargetWeight (x : Fin 184) : ℕ :=
  if h : x.val < 58 then
    (fromOffset (oneBodyWeights.getChunk ⟨x.val, h⟩).toNat).natAbs
  else
    (fragmentWeights.getChunk₂ ⟨(x.val - 58) / 14, by omega⟩ ⟨(x.val - 58) % 14, by omega⟩).toNat

/-- Exact unsigned integer weight of inner item `(idx : Fin 126, b : Fin 30)`. -/
def innerTargetWeight (idx : Fin 126) (b : Fin 30) : ℕ :=
  (fromOffset (innerWeights.getChunk₂ idx b).toNat).natAbs

theorem unpackOuterEntry_alt_val (raw : ℕ) (i : Fin 184) :
    (unpackOuterEntry raw i).alt.val = if raw % 256 < 184 then raw % 256 else i.val := by
  unfold unpackOuterEntry
  dsimp only
  split_ifs <;> rfl

/-- Tail-recursive list reversal in CPS so the Lean kernel materializes a literal `List.cons`
spine once instead of re-evaluating `Array.toList #[...]` (`O(n^2)` `Array.push`) per lookup. -/
def revK {α β : Type*} : List α → List α → (List α → β) → β
  | [], acc, k => k acc
  | x :: xs, acc, k => revK xs (x :: acc) k

/-- Force a list spine once in CPS before passing it to `k`; equals `k xs`. -/
def withForcedList {α β : Type*} (xs : List α) (k : List α → β) : β :=
  revK xs [] (fun rev ↦ revK rev [] k)

/-- Pre-unpack `(alt, C - keep)` pairs once per row so bin-sum checks avoid repeated division. -/
def unpackAltPairs (S M C : ℕ) : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | raw :: rest, j =>
    (cond (Nat.blt (raw % S) M) (raw % S) j, C - (raw / S) % C) ::
      unpackAltPairs S M C rest (j + 1)

/-- Sum `rem` across pre-unpacked `(alt, rem)` pairs matching target index `b`. -/
def sumAltPairs (b : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: rest =>
    match Nat.beq p.1 b with
    | true => p.2 + sumAltPairs b rest
    | false => sumAltPairs b rest

/-- Pure-`ℕ` kernel-primitive outer weight for `x < 184`. -/
def outerWeightFast (x : ℕ) : ℕ :=
  cond (Nat.blt x 58)
    (natAbsOffset (oneBodyWeights.extractLsb' (x * 15) 15).toNat)
    (fragmentWeights.extractLsb' ((((x - 58) / 14) * 14 + (x - 58) % 14) * 13) 13).toNat

/-- Alternate-branch coin contribution of packed outer entry `raw` at index `i` to target `x`. -/
def outerAltTerm (x i raw : ℕ) : ℕ :=
  cond (Nat.beq (cond (Nat.blt (raw % 256) 184) (raw % 256) i) x) (1024 - (raw / 256) % 1024) 0

/-- Alternate-branch coin contribution of packed inner entry `raw` at index `j` to target `b`. -/
def innerAltTerm (b j raw : ℕ) : ℕ :=
  cond (Nat.beq (cond (Nat.blt (raw % 32) 30) (raw % 32) j) b) (512 - (raw / 32) % 512) 0

/-- Pure-`ℕ` kernel-primitive lookup of `innerWeights` at row `r` and column `b`. -/
def innerWeightAt (r b : ℕ) : ℕ :=
  (innerWeights.extractLsb' ((r * 30 + b) * 15) 15).toNat

attribute [local irreducible] instDecidableEqAliasEntry oneBodyWeights fragmentWeights
  innerWeights

theorem outerTargetWeight_oneBody (ℓ : Fin 58) :
    outerTargetWeight (outerOneBodyIdx ℓ) =
      (fromOffset (oneBodyWeights.getChunk ℓ).toNat).natAbs := by
  simp [outerTargetWeight, ℓ.isLt]

theorem outerTargetWeight_frag (r : Fin 9) (c : Fin 14) :
    outerTargetWeight (outerFragIdx r c) =
      (fragmentWeights.getChunk₂ r c).toNat := by
  have hlt : ¬ (58 + 14 * r.val + c.val < 58) := by omega
  have hdiv : (58 + 14 * r.val + c.val - 58) / 14 = r.val := by omega
  have hmod : (58 + 14 * r.val + c.val - 58) % 14 = c.val := by omega
  simp only [outerTargetWeight, hlt, ↓reduceDIte]
  congr 1; congr 1 <;> ext <;> assumption

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OuterWeights
