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

/-!
# Fast Unpacked Array Compatibility Views for Bit-Packed P450 DFTHC Tables

Unpacks `P450.leafAngleTable`, `P450.oneBodyAngleTable`, `P450.oneBodyWeights`,
`P450.fragmentWeights`, and `P450.innerWeights` in `O(N log N)` GMP bit-shifts via structural
recursion on `fuel` (zero `WellFounded.fix`, zero large `2 ^ K` powers), keeping `decide +kernel`
evaluations sub-second and low-RSS while providing exact bridge lemmas to `P450.leafVector`,
`P450.oneBodyVector`, `P450.oneBodyEigenvalue`, and `P450.weight`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DataArrays
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution

/-- Extract `len` consecutive `w`-bit words from the low `len * w` bits of `x` in `O(len log len)`
GMP bit-shifts using structural recursion on `fuel` (`len ≤ 2 ^ fuel`). -/
def unpackWordsAux (w : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | _, 0, _ => []
  | _, 1, x => [x % (2 ^ w)]
  | 0, _, _ => []
  | fuel + 1, len, x =>
      let half := len / 2
      let k := half * w
      let hi := x >>> k
      let lo := x - (hi <<< k)
      unpackWordsAux w fuel half lo ++ unpackWordsAux w fuel (len - half) hi

/-- Slice a flat list into `m` rows of length `n` via structural recursion on `m`. -/
def chunkRows (n : ℕ) : ℕ → List ℕ → List (Array ℕ)
  | 0, _ => []
  | m + 1, xs => (xs.take n).toArray :: chunkRows n m (xs.drop n)

/-- Kernel-computable `1D` unpacker for `BitVec (n * w)` (`n ≤ 2 ^ 16`). -/
def unpack1D {n w : ℕ} (bv : BitVec (n * w)) : Array ℕ :=
  (unpackWordsAux w 16 n bv.toNat).toArray

/-- Kernel-computable `2D` unpacker for `BitVec (m * n * w)` (`m * n ≤ 2 ^ 16`). -/
def unpack2D {m n w : ℕ} (bv : BitVec (m * n * w)) : Array (Array ℕ) :=
  (chunkRows n m (unpackWordsAux w 16 (m * n) bv.toNat)).toArray

/-- Unpacked `261 × 57` array view of `P450.leafAngleTable`. -/
def leafAngleTableArr : Array (Array ℕ) := unpack2D P450.leafAngleTable

/-- Unpacked `58 × 57` array view of `P450.oneBodyAngleTable`. -/
def oneBodyAngleTableArr : Array (Array ℕ) := unpack2D P450.oneBodyAngleTable

/-- Unpacked `58`-entry array view of `P450.oneBodyWeights`. -/
def oneBodyWeightsArr : Array ℕ := unpack1D P450.oneBodyWeights

/-- Unpacked `9 × 14` array view of `P450.fragmentWeights`. -/
def fragmentWeightsArr : Array (Array ℕ) := unpack2D P450.fragmentWeights

/-- Unpacked `126 × 30` array view of `P450.innerWeights`. -/
def innerWeightsArr : Array (Array ℕ) := unpack2D P450.innerWeights

section UnpackProofs

private theorem shift_sub_eq_mod (x k : ℕ) : x - ((x >>> k) <<< k) = x % (2 ^ k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mul_comm (x / 2 ^ k), Nat.mod_def]

private theorem mod_high_div_mod (x w half i : ℕ) (hi : i < half) :
    (x % (2 ^ (half * w))) / (2 ^ (i * w)) % (2 ^ w) = x / (2 ^ (i * w)) % (2 ^ w) := by
  have hsplit : half * w = i * w + (w + (half - 1 - i) * w) := by
    have h1 : half = i + 1 + (half - 1 - i) := by omega
    calc half * w = (i + 1 + (half - 1 - i)) * w := by rw [← h1]
      _ = i * w + (w + (half - 1 - i) * w) := by ring
  have hpow : 2 ^ (half * w) = 2 ^ (i * w) * (2 ^ w * 2 ^ ((half - 1 - i) * w)) := by
    rw [hsplit, Nat.pow_add, Nat.pow_add]
  have hdiv_eq : x / 2 ^ (i * w) =
      x % 2 ^ (half * w) / 2 ^ (i * w) +
        (2 ^ w * 2 ^ ((half - 1 - i) * w)) * (x / 2 ^ (half * w)) := by
    conv_lhs => rw [← Nat.div_add_mod x (2 ^ (half * w)), hpow]
    rw [Nat.mul_assoc (2 ^ (i * w)), Nat.add_comm _ (x % _),
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos (i * w)), ← hpow]
  rw [hdiv_eq, Nat.mul_assoc (2 ^ w), Nat.add_mul_mod_self_left]

private theorem unpackWordsAux_eq (w : ℕ) :
    ∀ (fuel len x : ℕ), len ≤ 2 ^ fuel →
      unpackWordsAux w fuel len x =
        (List.range len).map (fun i ↦ (x / 2 ^ (i * w)) % 2 ^ w)
  | 0, 0, _, _ => rfl
  | fuel + 1, 0, _, _ => rfl
  | 0, 1, x, _ => by simp [unpackWordsAux]
  | fuel + 1, 1, x, _ => by simp [unpackWordsAux]
  | 0, len + 2, _, hle => by simp at hle
  | fuel + 1, len + 2, x, hle => by
      have hpow : 2 ^ (fuel + 1) = 2 ^ fuel + 2 ^ fuel := by ring
      simp only [unpackWordsAux, shift_sub_eq_mod]
      set n := len + 2
      have hhalf : n / 2 ≤ 2 ^ fuel := by omega
      have hrem : n - n / 2 ≤ 2 ^ fuel := by omega
      rw [unpackWordsAux_eq w fuel (n / 2) _ hhalf,
        unpackWordsAux_eq w fuel (n - n / 2) _ hrem]
      apply List.ext_getElem
      · simp; omega
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        by_cases hi : i < n / 2
        · rw [List.getElem_append_left (by simp [hi])]
          simp only [List.getElem_map, List.getElem_range]
          exact mod_high_div_mod x w (n / 2) i hi
        · have hge : ((List.range (n / 2)).map
              (fun j ↦ (x % 2 ^ (n / 2 * w)) / 2 ^ (j * w) % 2 ^ w)).length ≤ i := by
            simp only [List.length_map, List.length_range]; omega
          rw [List.getElem_append_right hge]
          simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range,
            Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
          have hadd : n / 2 * w + (i - n / 2) * w = i * w := by
            calc n / 2 * w + (i - n / 2) * w = (n / 2 + (i - n / 2)) * w := by ring
              _ = i * w := by rw [Nat.add_sub_of_le (by omega)]
          rw [hadd]

private theorem chunkRows_length (n : ℕ) :
    ∀ (m : ℕ) (xs : List ℕ), (chunkRows n m xs).length = m
  | 0, _ => rfl
  | m + 1, xs => by simp [chunkRows, chunkRows_length n m]

private theorem chunkRows_getElem (n : ℕ) :
    ∀ (m : ℕ) (xs : List ℕ) (i : ℕ) (hi : i < m),
      (chunkRows n m xs)[i]'(by rw [chunkRows_length]; exact hi) =
        ((xs.drop (i * n)).take n).toArray
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, xs, 0, _ => by simp [chunkRows]
  | m + 1, xs, i + 1, hi => by
      simp only [chunkRows, List.getElem_cons_succ]
      rw [chunkRows_getElem n m (xs.drop n) i (by omega), List.drop_drop]
      have hmul : n + i * n = (i + 1) * n := by ring
      rw [hmul]

private theorem unpack1D_size {n w : ℕ} (bv : BitVec (n * w)) (hle : n ≤ 2 ^ 16) :
    (unpack1D bv).size = n := by
  simp [unpack1D, unpackWordsAux_eq w 16 n bv.toNat hle]

private theorem array_getD_of_lt {α : Type*} (a : Array α) (i : ℕ) (d : α) (h : i < a.size) :
    a.getD i d = a[i] := by
  simp [Array.getD, h]

private theorem array_getD_of_not_lt {α : Type*} (a : Array α) (i : ℕ) (d : α)
    (h : ¬ i < a.size) : a.getD i d = d := by
  simp [Array.getD, h]

private theorem unpack1D_getD {n w : ℕ} (bv : BitVec (n * w)) (hle : n ≤ 2 ^ 16)
    (i : Fin n) (d : ℕ) :
    (unpack1D bv).getD i.val d = (bv.getChunk i).toNat := by
  have hi : i.val < (unpack1D bv).size := (unpack1D_size bv hle).symm ▸ i.isLt
  rw [array_getD_of_lt _ _ _ hi]
  simp only [unpack1D, unpackWordsAux_eq w 16 n bv.toNat hle, List.getElem_toArray,
    List.getElem_map, List.getElem_range, BitVec.getChunk, BitVec.extractLsb',
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

private theorem unpack2D_size {m n w : ℕ} (bv : BitVec (m * n * w)) :
    (unpack2D bv).size = m := by
  simp [unpack2D, chunkRows_length]

private theorem unpack2D_row_size {m n w : ℕ} (bv : BitVec (m * n * w))
    (hle : m * n ≤ 2 ^ 16) (i : Fin m) :
    ((unpack2D bv).getD i.val #[]).size = n := by
  have hi : i.val < (unpack2D bv).size := (unpack2D_size bv).symm ▸ i.isLt
  rw [array_getD_of_lt _ _ _ hi]
  simp only [unpack2D, List.getElem_toArray, chunkRows_getElem _ _ _ _ i.isLt,
    List.size_toArray, List.length_take, List.length_drop,
    unpackWordsAux_eq w 16 (m * n) bv.toNat hle, List.length_map, List.length_range]
  have hbound : n ≤ m * n - i.val * n := by
    have h1 : (i.val + 1) * n ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    have h2 : (i.val + 1) * n = i.val * n + n := by ring
    omega
  exact Nat.min_eq_left hbound

private theorem unpack2D_getD {m n w : ℕ} (bv : BitVec (m * n * w))
    (hle : m * n ≤ 2 ^ 16) (i : Fin m) (j : Fin n) (d : ℕ) :
    ((unpack2D bv).getD i.val #[]).getD j.val d = (bv.getChunk₂ i j).toNat := by
  have hi : i.val < (unpack2D bv).size := (unpack2D_size bv).symm ▸ i.isLt
  have hj : j.val < ((unpack2D bv).getD i.val #[]).size :=
    (unpack2D_row_size bv hle i).symm ▸ j.isLt
  rw [array_getD_of_lt _ _ _ hj]
  have hrow : (unpack2D bv).getD i.val #[] =
      (((unpackWordsAux w 16 (m * n) bv.toNat).drop (i.val * n)).take n).toArray := by
    rw [array_getD_of_lt _ _ _ hi]
    simp [unpack2D, chunkRows_getElem _ _ _ _ i.isLt]
  simp only [hrow, List.getElem_toArray, List.getElem_take, List.getElem_drop,
    unpackWordsAux_eq w 16 (m * n) bv.toNat hle, List.getElem_map, List.getElem_range,
    BitVec.getChunk₂, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

end UnpackProofs

section BridgeLemmas

attribute [local irreducible]
  P450.leafAngleTable P450.oneBodyAngleTable
  P450.oneBodyWeights P450.fragmentWeights P450.innerWeights

@[simp]
theorem leafAngleTableArr_size : leafAngleTableArr.size = 261 :=
  unpack2D_size _

theorem leafAngleTableArr_row_size (μ : Fin 261) :
    (leafAngleTableArr.getD μ.val #[]).size = 57 :=
  unpack2D_row_size _ (by decide) μ

theorem leafAngleTableArr_getD (μ : Fin 261) (p : Fin 57) (d : ℕ) :
    (leafAngleTableArr.getD μ.val #[]).getD p.val d =
      (P450.leafAngleTable.getChunk₂ μ p).toNat :=
  unpack2D_getD _ (by decide) μ p d

theorem leafAngleTableArr_entry_lt (μ : Fin 261) (p : Fin 57) (d : ℕ) :
    (leafAngleTableArr.getD μ.val #[]).getD p.val d < 8192 := by
  rw [leafAngleTableArr_getD]
  exact (P450.leafAngleTable.getChunk₂ μ p).isLt

@[simp]
theorem oneBodyAngleTableArr_size : oneBodyAngleTableArr.size = 58 :=
  unpack2D_size _

theorem oneBodyAngleTableArr_row_size (ℓ : Fin 58) :
    (oneBodyAngleTableArr.getD ℓ.val #[]).size = 57 :=
  unpack2D_row_size _ (by decide) ℓ

theorem oneBodyAngleTableArr_getD (ℓ : Fin 58) (p : Fin 57) (d : ℕ) :
    (oneBodyAngleTableArr.getD ℓ.val #[]).getD p.val d =
      (P450.oneBodyAngleTable.getChunk₂ ℓ p).toNat :=
  unpack2D_getD _ (by decide) ℓ p d

theorem oneBodyAngleTableArr_entry_lt (ℓ : Fin 58) (p : Fin 57) (d : ℕ) :
    (oneBodyAngleTableArr.getD ℓ.val #[]).getD p.val d < 8192 := by
  rw [oneBodyAngleTableArr_getD]
  exact (P450.oneBodyAngleTable.getChunk₂ ℓ p).isLt

@[simp]
theorem oneBodyWeightsArr_size : oneBodyWeightsArr.size = 58 :=
  unpack1D_size _ (by decide)

theorem oneBodyWeightsArr_getD (ℓ : Fin 58) (d : ℕ) :
    oneBodyWeightsArr.getD ℓ.val d = (P450.oneBodyWeights.getChunk ℓ).toNat :=
  unpack1D_getD _ (by decide) ℓ d

@[simp]
theorem fragmentWeightsArr_size : fragmentWeightsArr.size = 9 :=
  unpack2D_size _

theorem fragmentWeightsArr_row_size (r : Fin 9) :
    (fragmentWeightsArr.getD r.val #[]).size = 14 :=
  unpack2D_row_size _ (by decide) r

theorem fragmentWeightsArr_getD (r : Fin 9) (c : Fin 14) (d : ℕ) :
    (fragmentWeightsArr.getD r.val #[]).getD c.val d =
      (P450.fragmentWeights.getChunk₂ r c).toNat :=
  unpack2D_getD _ (by decide) r c d

@[simp]
theorem innerWeightsArr_size : innerWeightsArr.size = 126 :=
  unpack2D_size _

theorem innerWeightsArr_row_size (rc : Fin 126) :
    (innerWeightsArr.getD rc.val #[]).size = 30 :=
  unpack2D_row_size _ (by decide) rc

theorem innerWeightsArr_getD (rc : Fin 126) (b : Fin 30) (d : ℕ) :
    (innerWeightsArr.getD rc.val #[]).getD b.val d =
      (P450.innerWeights.getChunk₂ rc b).toNat :=
  unpack2D_getD _ (by decide) rc b d

theorem leafVector_eq_arr (μ : Fin 261) :
    P450.leafVector μ =
      givensLeaf 15
        (fun p ↦ ((leafAngleTableArr.getD μ.val #[]).getD p.val 0 : ℤ)) := by
  unfold P450.leafVector
  congr 1
  ext p
  by_cases hp : p.val < 57
  · simp only [hp, ↓reduceDIte]
    rw [leafAngleTableArr_getD μ ⟨p.val, hp⟩ 0]
  · simp only [hp, ↓reduceDIte]
    have hsz := leafAngleTableArr_row_size μ
    rw [array_getD_of_not_lt _ _ _ (by omega)]; rfl

theorem oneBodyVector_eq_arr (ℓ : Fin 58) :
    P450.oneBodyVector ℓ =
      givensLeaf 15
        (fun p ↦ ((oneBodyAngleTableArr.getD ℓ.val #[]).getD p.val 0 : ℤ)) := by
  unfold P450.oneBodyVector
  congr 1
  ext p
  by_cases hp : p.val < 57
  · simp only [hp, ↓reduceDIte]
    rw [oneBodyAngleTableArr_getD ℓ ⟨p.val, hp⟩ 0]
  · simp only [hp, ↓reduceDIte]
    have hsz := oneBodyAngleTableArr_row_size ℓ
    rw [array_getD_of_not_lt _ _ _ (by omega)]; rfl

theorem oneBodyEigenvalue_eq_arr (ℓ : Fin 58) :
    P450.oneBodyEigenvalue ℓ =
      (P450.fromOffset (oneBodyWeightsArr.getD ℓ.val (2 ^ 14)) : ℝ) * P450.coefficientUnit := by
  unfold P450.oneBodyEigenvalue
  rw [oneBodyWeightsArr_getD]

theorem weight_eq_arr (r : Fin 9) (c : Fin 14) (b : Fin 30) :
    P450.weight r c b =
      (P450.fromOffset
          ((innerWeightsArr.getD (14 * r.val + c.val) #[]).getD b.val (2 ^ 14)) : ℝ) *
        √(4 * ((fragmentWeightsArr.getD r.val #[]).getD c.val 0 : ℝ) * P450.coefficientUnit) /
        15360 := by
  unfold P450.weight
  have hrc : 14 * r.val + c.val < 126 := by omega
  have hi := innerWeightsArr_getD ⟨14 * r.val + c.val, hrc⟩ b (2 ^ 14)
  have hf := fragmentWeightsArr_getD r c 0
  simp only at hi hf
  rw [hi, hf]

end BridgeLemmas

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DataArrays
