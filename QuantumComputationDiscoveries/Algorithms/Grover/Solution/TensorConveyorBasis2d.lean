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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SpecDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.StageLoop
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.TensorConveyorCertDefs
public import QuantumComputation.Algorithms.Grover.Amplitude
public import QuantumComputation.Algorithms.Grover.EarlyStoppingAnalysis
public import QuantumComputation.Algorithms.Grover.Operators
public import QuantumComputation.Maths.Trigonometry
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

section Sec_Interfaces
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs

namespace QuantumComputation.Specs

open Operator ResourceCounting Real
open scoped NNReal NNRat

/-- Number of active parallel oracle slots used in a batch round:
  `m` for `1 ≤ m`, and `1` otherwise. -/
def activeSlots (m _k : ℕ) : ℕ :=
  if 1 ≤ m then m else 1

theorem activeSlots_pos (m k : ℕ) : 0 < activeSlots m k := by
  unfold activeSlots
  split_ifs with h <;> omega

instance (m k : ℕ) : NeZero (activeSlots m k) :=
  ⟨(activeSlots_pos m k).ne'⟩

theorem activeSlots_le (m k : ℕ) (hm : 1 ≤ m) : activeSlots m k ≤ m := by
  unfold activeSlots
  split_ifs; omega

theorem activeSlots_eq_of_pos {m k : ℕ} (hm1 : 1 ≤ m) :
    activeSlots m k = m := by
  simp [activeSlots, hm1]

theorem activeSlots_eq_self {m k : ℕ} (hm1 : 1 ≤ m) (_hm10 : m ≤ 10)
    (_hk1 : 1 ≤ k) (_hk10 : k ≤ 10) :
    activeSlots m k = m := by
  simp [activeSlots, hm1]

/-- Frobenius `{2, 3}`-monoid stage stride selector for slot count `w` and remaining targets
  `r`. -/
def stageStride (w r : ℕ) : ℕ :=
  if (6 ≤ w ∧ 3 ≤ r ∧ r % 3 ≠ 1) ∨ ((w = 4 ∨ w = 5) ∧ 5 ≤ r ∧ r ≠ 6 ∧ r % 3 ≠ 1) then 3
  else if (3 ≤ w ∧ 2 ≤ r) ∨ (w = 2 ∧ 3 ≤ r) then 2
  else 1

theorem stageStride_bounds {w r : ℕ} (hw : 1 ≤ w) (hr : 1 ≤ r) :
    1 ≤ stageStride w r ∧ stageStride w r ≤ 3 ∧ stageStride w r ≤ w ∧ stageStride w r ≤ r := by
  unfold stageStride
  split_ifs <;> omega

theorem stageStride_one (r : ℕ) : stageStride 1 r = 1 := by
  unfold stageStride
  split_ifs <;> omega

/-- Total qubit count of `groverFindAllCircuit`: accommodates `activeSlots m k` disjoint
  `(n + 1)`-qubit oracle slots as well as `k * n + 1` qubits so any `s`-tuple of `n`-bit
  targets
  (`s ≤ k`) encodes as a basis state in `Fin (2 ^ findAllQubits n m k)`. -/
def findAllQubits (n m k : ℕ) : ℕ :=
  max (activeSlots m k * (n + 1)) (k * n) + 1

theorem slot_offset_add_width_le {n m k : ℕ} (j : Fin (activeSlots m k)) :
    j.val * (n + 1) + (n + 1) ≤ findAllQubits n m k := by
  have hj : (j.val + 1) * (n + 1) ≤ activeSlots m k * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) j.isLt
  unfold findAllQubits
  have hmax : activeSlots m k * (n + 1) ≤ max (activeSlots m k * (n + 1)) (k * n) :=
    le_max_left _ _
  calc
    j.val * (n + 1) + (n + 1) = (j.val + 1) * (n + 1) := by ring
    _ ≤ activeSlots m k * (n + 1) := hj
    _ ≤ max (activeSlots m k * (n + 1)) (k * n) + 1 := by omega

theorem mul_lt_findAllQubits (n m k : ℕ) :
    k * n < findAllQubits n m k := by
  unfold findAllQubits
  have : k * n ≤ max (activeSlots m k * (n + 1)) (k * n) := le_max_right _ _
  omega

/-- The `j`-th `(n + 1)`-qubit slot register inside `findAllQubits n m k`. -/
def slotReg (n m k : ℕ) (j : Fin (activeSlots m k)) :
    QRegister (n + 1) (findAllQubits n m k) :=
  QRegister.block (j.val * (n + 1)) (n + 1) (slot_offset_add_width_le j)

theorem slotReg_disjoint {n m k : ℕ} {i j : Fin (activeSlots m k)} (hij : i ≠ j) :
    (slotReg n m k i).DisjointWires (slotReg n m k j) := by
  have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine QRegister.block_disjoint_of_le _ _ _ _ _ _ ?_
    have : (i.val + 1) * (n + 1) ≤ j.val * (n + 1) :=
      Nat.mul_le_mul_right (n + 1) hlt
    linarith
  · rw [QRegister.disjoint_comm]
    refine QRegister.block_disjoint_of_le _ _ _ _ _ _ ?_
    have : (j.val + 1) * (n + 1) ≤ i.val * (n + 1) :=
      Nat.mul_le_mul_right (n + 1) hgt
    linarith

/-- Ordered list of all `activeSlots m k` slot registers. -/
def slotRegList (n m k : ℕ) : List (QRegister (n + 1) (findAllQubits n m k)) :=
  (List.finRange (activeSlots m k)).map (slotReg n m k)

theorem slotRegList_pairwise_disjoint (n m k : ℕ) :
    (slotRegList n m k).Pairwise QRegister.DisjointWires := by
  rw [slotRegList, List.pairwise_map]
  exact (List.nodup_finRange (activeSlots m k)).imp fun hij ↦ slotReg_disjoint hij

theorem slotRegList_length (n m k : ℕ) :
    (slotRegList n m k).length = activeSlots m k := by
  simp [slotRegList]

/-- Register holding the `activeSlots m k` parallel oracle slots inside `findAllQubits n m
  k`. -/
def batchOracleReg (n m k : ℕ) :
    QRegister ((n + 1) * activeSlots m k) (findAllQubits n m k) :=
  QRegister.block 0 ((n + 1) * activeSlots m k) (by
    unfold findAllQubits
    have := le_max_left (activeSlots m k * (n + 1)) (k * n)
    nlinarith)

/-- Base-`2 ^ n` integer encoding of an `s`-tuple of `n`-bit target indices. -/
def encodeTuple (n : ℕ) {s : ℕ} (xs : Fin s → Fin (2 ^ n)) : ℕ :=
  ∑ i : Fin s, (xs i).val * (2 ^ n) ^ i.val

theorem encodeTuple_zero (n : ℕ) (xs : Fin 0 → Fin (2 ^ n)) :
    encodeTuple n xs = 0 := by
  simp [encodeTuple]

theorem encodeTuple_succ (n : ℕ) {s : ℕ} (xs : Fin (s + 1) → Fin (2 ^ n)) :
    encodeTuple n xs =
      encodeTuple n (xs ∘ Fin.castSucc) + (xs (Fin.last s)).val * (2 ^ n) ^ s := by
  simp [encodeTuple, Fin.sum_univ_castSucc]

theorem encodeTuple_lt_pow (n : ℕ) {s : ℕ} (xs : Fin s → Fin (2 ^ n)) :
    encodeTuple n xs < (2 ^ n) ^ s := by
  induction s with
  | zero => simp [encodeTuple]
  | succ s ih =>
      rw [encodeTuple_succ, pow_succ']
      have hlow := ih (xs ∘ Fin.castSucc)
      have hlast : (xs (Fin.last s)).val + 1 ≤ 2 ^ n := (xs (Fin.last s)).isLt
      have hmul : ((xs (Fin.last s)).val + 1) * (2 ^ n) ^ s ≤ 2 ^ n * (2 ^ n) ^ s :=
        Nat.mul_le_mul_right ((2 ^ n) ^ s) hlast
      linarith

theorem encodeTuple_lt_two_pow_qubits (n m k : ℕ) {s : ℕ} (hs : s ≤ k)
    (xs : Fin s → Fin (2 ^ n)) :
    encodeTuple n xs < 2 ^ findAllQubits n m k := by
  refine (encodeTuple_lt_pow n xs).trans_le ?_
  rw [← pow_mul]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have h1 : n * s ≤ k * n := by
    rw [mul_comm n s]
    exact Nat.mul_le_mul_right n hs
  exact h1.trans (mul_lt_findAllQubits n m k).le

/-- Base-`2 ^ n` encoded `s`-tuple packaged as a basis index in `Fin (2 ^ findAllQubits n m
  k)`. -/
def encodeTupleFin (n m k : ℕ) {s : ℕ} (hs : s ≤ k) (xs : Fin s → Fin (2 ^ n)) :
    Fin (2 ^ findAllQubits n m k) :=
  ⟨encodeTuple n xs, encodeTuple_lt_two_pow_qubits n m k hs xs⟩

theorem encodeTuple_div_mod (n : ℕ) {s : ℕ} (xs : Fin s → Fin (2 ^ n)) (i : Fin s) :
    (encodeTuple n xs / (2 ^ n) ^ i.val) % 2 ^ n = (xs i).val := by
  induction s with
  | zero => exact i.elim0
  | succ s ih =>
      rw [encodeTuple_succ]
      rcases Fin.lastCases (motive := fun i : Fin (s + 1) ↦
          i = Fin.last s ∨ ∃ j : Fin s, i = Fin.castSucc j)
          (Or.inl rfl) (fun j ↦ Or.inr ⟨j, rfl⟩) i with rfl | ⟨j, rfl⟩
      · simp only [Fin.val_last]
        have hpos : 0 < (2 ^ n) ^ s := by positivity
        rw [Nat.add_mul_div_right _ _ hpos,
          Nat.div_eq_of_lt (encodeTuple_lt_pow n (xs ∘ Fin.castSucc)), zero_add,
          Nat.mod_eq_of_lt (xs (Fin.last s)).isLt]
      · simp only [Fin.val_castSucc]
        have hpow : (2 ^ n) ^ s = ((2 ^ n) ^ (s - 1 - j.val) * 2 ^ n) * (2 ^ n) ^ j.val := by
          rw [← pow_succ, ← pow_add]
          congr 1
          have := j.isLt
          omega
        have hpos : 0 < (2 ^ n) ^ j.val := by positivity
        rw [hpow, ← mul_assoc, Nat.add_mul_div_right _ _ hpos, ← mul_assoc,
          Nat.add_mul_mod_self_right]
        exact ih (xs ∘ Fin.castSucc) j

theorem decodeTargets_encodeTuple_eq (n : ℕ) {s : ℕ} (xs : Fin s → Fin (2 ^ n)) :
    decodeTargets n s (encodeTuple n xs : ℤ) = Finset.univ.image xs := by
  unfold decodeTargets
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    ext
    simp only [Int.toNat_natCast]
    exact (encodeTuple_div_mod n xs ⟨i, hi⟩).symm
  · rintro ⟨i, rfl⟩
    refine ⟨i.val, i.isLt, ?_⟩
    ext
    simp only [Int.toNat_natCast]
    exact encodeTuple_div_mod n xs i

theorem encodeTuple_injective (n : ℕ) {s : ℕ} :
    Function.Injective (encodeTuple n (s := s)) := by
  intro xs ys h
  funext i
  ext
  rw [← encodeTuple_div_mod n xs i, ← encodeTuple_div_mod n ys i, h]

/-- Append a `d`-tuple `ys` of newly discovered targets to an existing `p`-tuple `xs`. -/
def appendTuple {α : Type*} {p d : ℕ} (xs : Fin p → α) (ys : Fin d → α) (i : Fin (p + d)) : α :=
  if h : i.val < p then xs ⟨i.val, h⟩ else ys ⟨i.val - p, by omega⟩

theorem appendTuple_injective {α : Type*} {p d : ℕ} {xs : Fin p → α} {ys : Fin d → α}
    (hxs : Function.Injective xs) (hys : Function.Injective ys)
    (hdisj : ∀ i : Fin p, ∀ j : Fin d, xs i ≠ ys j) :
    Function.Injective (appendTuple xs ys) := by
  intro i j hij
  dsimp [appendTuple] at hij
  split_ifs at hij with hi hj hj
  · have h := Fin.mk.inj_iff.mp (hxs hij)
    exact Fin.ext h
  · exact (hdisj _ _ hij).elim
  · exact (hdisj _ _ hij.symm).elim
  · have h := Fin.mk.inj_iff.mp (hys hij)
    exact Fin.ext (by omega)

theorem image_appendTuple_subset {α : Type*} [DecidableEq α] {p d : ℕ}
    {xs : Fin p → α} {ys : Fin d → α} {S : Finset α}
    (hxs : Finset.univ.image xs ⊆ S) (hys : ∀ j : Fin d, ys j ∈ S) :
    Finset.univ.image (appendTuple xs ys) ⊆ S := by
  rw [Finset.image_subset_iff]
  intro i _
  dsimp [appendTuple]
  split_ifs with hi
  · exact hxs (Finset.mem_image_of_mem xs (Finset.mem_univ _))
  · exact hys _

/-- Monadic (`s = 1`) target rotation phases `φ_{1,m} ∈ ℚ≥0`. -/
def phiMonadicQ (m : ℕ) : ℚ≥0 :=
  match m with
  | 1 => 7 / 6 | 2 => 4 / 5 | 3 => 13 / 20 | 4 => 14 / 25 | 5 => 1 / 2
  | 6 => 23 / 50 | 7 => 17 / 40 | 8 => 2 / 5 | 9 => 3 / 8 | 10 => 7 / 20
  | _ => 7 / 6

/-- Dyadic (`s = 2`) target rotation phases `φ_{2,m} ∈ ℚ≥0`. -/
def phiDyadicQ (m : ℕ) : ℚ≥0 :=
  match m with
  | 2 => 67 / 50 | 3 => 29 / 25 | 4 => 1 | 5 => 22 / 25 | 6 => 4 / 5
  | 7 => 37 / 50 | 8 => 7 / 10 | 9 => 16 / 25 | 10 => 31 / 50
  | _ => 7 / 6

/-- Triadic (`s = 3`) target rotation phases `φ_{3,m} ∈ ℚ≥0`. -/
def phiTriadicQ (m : ℕ) : ℚ≥0 :=
  match m with
  | 4 => 34 / 25 | 5 => 61 / 50 | 6 => 28 / 25 | 7 => 26 / 25
  | 8 => 24 / 25 | 9 => 9 / 10 | 10 => 17 / 20
  | _ => 7 / 6

/-- Target rotation phase `stagePhiQ w r` selected according to `stageStride w r`. -/
def stagePhiQ (w r : ℕ) : ℚ≥0 :=
  match stageStride w r with
  | 3 => phiTriadicQ w
  | 2 => phiDyadicQ w
  | _ => phiMonadicQ w

noncomputable def stagePhiReal (w r : ℕ) : ℝ :=
  (stagePhiQ w r : ℝ)

/-- Multi-target Grover half-angle `θ_{r,d} = arcsin(√r / √d)`. -/
noncomputable def multiHalfAngle (r d : ℕ) : ℝ :=
  Real.arcsin (Real.sqrt (r : ℝ) / Real.sqrt (d : ℝ))

/-- Single-slot success probability `sin²((2K + 1) θ_{r,d})` after `K` Grover iterations. -/
noncomputable def multiP_succ (K r d : ℕ) : ℝ :=
  (Real.sin ((2 * (K : ℝ) + 1) * multiHalfAngle r d)) ^ 2

/-- Exact binomial occupancy tail polynomial `T_s(w, r, p) = P(|H_w| ≥ s)`
  for `s ∈ {0, 1, 2, 3}`. -/
noncomputable def occupancyTail (s w r : ℕ) (p : ℝ) : ℝ :=
  match s with
  | 0 => 1
  | 1 => 1 - (1 - p) ^ w
  | 2 =>
      1 - (r : ℝ) * (1 - ((r : ℝ) - 1) / (r : ℝ) * p) ^ w +
        ((r : ℝ) - 1) * (1 - p) ^ w
  | 3 =>
      1 - ((r : ℝ) * ((r : ℝ) - 1) / 2) * (1 - ((r : ℝ) - 2) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 2)) * (1 - ((r : ℝ) - 1) / (r : ℝ) * p) ^ w -
        (((r : ℝ) - 1) * ((r : ℝ) - 2) / 2) * (1 - p) ^ w
  | _ => 0

/-- Guarded stage iteration count `K` for target rotation phase `φ`, qubit count `n`, and
  `r`
  remaining targets. -/
noncomputable def stageIterations (φ : ℝ) (n r : ℕ) : ℕ :=
  if 16384 * r ≤ 2 ^ n then
    Int.toNat (round (φ / (2 * multiHalfAngle r (2 ^ n))))
  else 0

/-- Expected wall-clock query cost bound for a stage with `r` remaining targets. -/
noncomputable def stageWallCostNNReal (n m k r : ℕ) : ℝ≥0 :=
  let w := activeSlots m k
  let s := stageStride w r
  let K := stageIterations (stagePhiReal w r) n r
  (Real.toNNReal (occupancyTail s w r (multiP_succ K r (2 ^ n))))⁻¹ * ((K + 1 : ℕ) : ℝ≥0)

/-- Fuel-recursing sum of expected wall-clock query costs along the Frobenius `{2, 3}`
  trajectory
  `r ↦ r - stageStride (activeSlots m k) r`. -/
noncomputable def frobeniusCascadeCostAux (n m k : ℕ) : ℕ → ℕ → ℝ≥0
  | 0, _ => 0
  | fuel + 1, r =>
      if r = 0 then 0
      else
        let s := stageStride (activeSlots m k) r
        stageWallCostNNReal n m k r + frobeniusCascadeCostAux n m k fuel (r - s)

/-- Total expected wall-clock query cost bound over all stages starting from `r = k`. -/
noncomputable def allStagesWallCost (n m k : ℕ) : ℝ≥0 :=
  frobeniusCascadeCostAux n m k k k

/-- Numerators (`× 1000`) of the certified `10 × 10` relative wall-clock cost table. -/
def relCostGridNat (m k : ℕ) : ℕ :=
  match m, k with
  | 1, 1 => 880 | 1, 2 => 880 | 1, 3 => 880 | 1, 4 => 880 | 1, 5 => 880
  | 1, 6 => 880 | 1, 7 => 880 | 1, 8 => 880 | 1, 9 => 880 | 1, 10 => 880
  | 2, 1 => 945 | 2, 2 => 945 | 2, 3 => 924 | 2, 4 => 902 | 2, 5 => 886
  | 2, 6 => 871 | 2, 7 => 860 | 2, 8 => 850 | 2, 9 => 842 | 2, 10 => 834
  | 3, 1 => 965 | 3, 2 => 864 | 3, 3 => 853 | 3, 4 => 814 | 3, 5 => 814
  | 3, 6 => 790 | 3, 7 => 793 | 3, 8 => 776 | 3, 9 => 780 | 3, 10 => 766
  | 4, 1 => 974 | 4, 2 => 802 | 4, 3 => 839 | 4, 4 => 769 | 4, 5 => 759
  | 4, 6 => 753 | 4, 7 => 748 | 4, 8 => 726 | 4, 9 => 723 | 4, 10 => 722
  | 5, 1 => 979 | 5, 2 => 780 | 5, 3 => 835 | 5, 4 => 752 | 5, 5 => 713
  | 5, 6 => 740 | 5, 7 => 710 | 5, 8 => 682 | 5, 9 => 707 | 5, 10 => 684
  | 6, 1 => 982 | 6, 2 => 766 | 6, 3 => 770 | 6, 4 => 742 | 6, 5 => 692
  | 6, 6 => 705 | 6, 7 => 693 | 6, 8 => 664 | 6, 9 => 678 | 6, 10 => 668
  | 7, 1 => 985 | 7, 2 => 757 | 7, 3 => 720 | 7, 4 => 736 | 7, 5 => 680
  | 7, 6 => 670 | 7, 7 => 683 | 7, 8 => 655 | 7, 9 => 650 | 7, 10 => 660
  | 8, 1 => 986 | 8, 2 => 747 | 8, 3 => 695 | 8, 4 => 729 | 8, 5 => 671
  | 8, 6 => 652 | 8, 7 => 676 | 8, 8 => 646 | 8, 9 => 635 | 8, 10 => 653
  | 9, 1 => 988 | 9, 2 => 751 | 9, 3 => 678 | 9, 4 => 731 | 9, 5 => 670
  | 9, 6 => 639 | 9, 7 => 675 | 9, 8 => 645 | 9, 9 => 624 | 9, 10 => 651
  | 10, 1 => 990 | 10, 2 => 740 | 10, 3 => 665 | 10, 4 => 724 | 10, 5 => 663
  | 10, 6 => 630 | 10, 7 => 669 | 10, 8 => 639 | 10, 9 => 617 | 10, 10 => 646
  | _, _ => 880 * m

/-- Scaled numerator (`× 1000`) of `relCostTableQ m k`. -/
def relCostScaledNat (m k : ℕ) : ℕ :=
  if 1 ≤ m ∧ m ≤ 10 ∧ 1 ≤ k ∧ k ≤ 10 then relCostGridNat m k else 880 * m

/-- Certified `10 × 10` rational relative wall-clock query cost table `relCostTableQ m k`. -/
def relCostTableQ (m k : ℕ) : ℚ≥0 :=
  (relCostScaledNat m k : ℚ≥0) / 1000

end QuantumComputation.Specs
end
end Sec_Interfaces
section Sec_UnitPhaseFreeStepReset
section
open Operator QProg
open scoped Matrix
private theorem wp_measureReg_coe_aux {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (r :
    QRegister k n) (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) : (wp
      (QProg.measureRegister res r)
    Θ σ).1 = ∑ o : Fin (2 ^ k), HermitianMat.conj (r.basisOutcomeProjector o)ᴴ (Θ (Store.subst σ res
    ↑o.val)).1 := rfl
end
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
/-- Unit-modulus complex phase `3/5 + (4/5)i` whose square `-7/25 + (24/25)i` is not `1`,
  used to distinguish involution non-oracle `.step` unitaries from involutory oracle
  products. -/
noncomputable def freeStepPhase : ℂ :=
  3 / 5 + (4 / 5) * Complex.I
theorem star_freeStepPhase_mul_self : star freeStepPhase * freeStepPhase = 1 := by
  rw [freeStepPhase, Complex.ext_iff]; norm_num [RCLike.star_def, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
theorem freeStepPhase_mul_star_self : freeStepPhase * star freeStepPhase = 1 := by
  rw [mul_comm]; exact star_freeStepPhase_mul_self
theorem freeStepPhase_sq_ne_one : freeStepPhase * freeStepPhase ≠ 1 := by
  intro h; have him := congrArg Complex.im h; norm_num [freeStepPhase, Complex.mul_im,
    Complex.add_re, Complex.add_im] at him
/-- Tag a unitary `U` by multiplying by `freeStepPhase = 3/5 + (4/5)i`. -/
noncomputable def tagFreeStep {d : ℕ} (U : Unitary d) : Unitary d :=
  ⟨freeStepPhase • U.1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      freeStepPhase_mul_star_self, one_smul]
    have hU := U.2.2
    rwa [← Matrix.star_eq_conjTranspose]⟩
@[simp]
theorem tagFreeStep_val {d : ℕ} (U : Unitary d) : (tagFreeStep U).1 = freeStepPhase • U.1 := rfl
@[simp]
theorem wp_qAssign_tagFreeStep {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] (U : Unitary d) (Θ
  : CQAssertion (Store Var) d) : wp (.qAssign (tagFreeStep U) : QProg Var d) Θ = wp (.qAssign U) Θ
    := by
  funext σ; refine Subtype.ext (Subtype.ext ?_); rw [wp_qAssign, wp_qAssign,
    qhlQAssign_val, qhlQAssign_val, tagFreeStep_val,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    freeStepPhase_mul_star_self, one_smul]
private lemma fin2_zero_or_one_82 (c : Fin (2 ^ 1)) : c = 0 ∨ c = 1 := by
  rcases c with ⟨v, hv⟩; change v < 2 at hv; rcases (by omega : v = 0 ∨ v = 1) with rfl | rfl
  · exact Or.inl (Fin.ext rfl)
  · exact Or.inr (Fin.ext rfl)
private lemma tableAddPerm_mul_self {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) : tableAddPerm f *
  tableAddPerm f = 1 := by
  ext1 idx; apply (splitBasisEquiv n 1).injective
  have h2 : ∀ a b : Fin (2 ^ 1), b + a + a = b := fun a b ↦ by
    rcases fin2_zero_or_one_82 a with rfl | rfl <;> rcases fin2_zero_or_one_82 b with rfl | rfl <;>
      exact Fin.ext rfl
  simp [tableAddPerm, addRightShear, h2]
private lemma permutationUnitary_mul_self_of_mul_self {d : ℕ} {e : Equiv.Perm (Fin d)} (he : e * e =
  1) : permutationUnitary e * permutationUnitary e = 1 := by
  apply Subtype.ext; have he' : e⁻¹ * e⁻¹ = 1 := (by rw [← mul_inv_rev, he, inv_one])
  simp [permutationUnitary, ← Matrix.permMatrix_mul, he']
theorem groverSetMarkingOracle_mul_self {n : ℕ} (S : Finset (Fin (2 ^ n))) : groverSetMarkingOracle
  S * groverSetMarkingOracle S = 1 :=
  permutationUnitary_mul_self_of_mul_self (tableAddPerm_mul_self _)
private lemma embedUnitary_comm_of_disjoint {Q w₁ w₂ : ℕ} (r₁ : QRegister w₁ Q) (r₂ : QRegister w₂
  Q) (hdisj : r₁.DisjointWires r₂) (U : Unitary (2 ^ w₁)) (V : Unitary (2 ^ w₂)) : r₁.embedUnitary U
  * r₂.embedUnitary V = r₂.embedUnitary V * r₁.embedUnitary U := by
  apply Subtype.ext; exact r₁.embedMatrix_comm_of_disjoint r₂ hdisj U.1 V.1
private lemma embedUnitary_comm_list_prod {Q w : ℕ} (O : Unitary (2 ^ w)) (r : QRegister w Q) (regs
  : List (QRegister w Q)) (hdisj : ∀ r' ∈ regs, r.DisjointWires r') : r.embedUnitary O * (regs.map
  fun r' ↦ r'.embedUnitary O).prod = (regs.map fun r' ↦ r'.embedUnitary O).prod * r.embedUnitary O
  := by
  induction regs with
  | nil => simp
  | cons r₀ rs ih =>
    simp only [List.map_cons, List.prod_cons]; rw [← mul_assoc, embedUnitary_comm_of_disjoint r r₀
      (hdisj r₀ List.mem_cons_self), mul_assoc, ih (fun r' hr' ↦ hdisj r' (List.mem_cons_of_mem _
      hr')), ← mul_assoc]
private lemma list_prod_embedUnitary_mul_self {Q w : ℕ} (O : Unitary (2 ^ w)) (hO : O * O = 1) (regs
  : List (QRegister w Q)) (hpair : regs.Pairwise QRegister.DisjointWires) : (regs.map fun r ↦
  r.embedUnitary O).prod * (regs.map fun r ↦ r.embedUnitary O).prod = 1 := by
  induction regs with
  | nil => simp
  | cons r rs ih =>
      rcases List.pairwise_cons.mp hpair with ⟨hdisj, hpair'⟩; simp only [List.map_cons,
        List.prod_cons]; have hcomm := embedUnitary_comm_list_prod O r rs hdisj
      calc (r.embedUnitary O * (rs.map fun r' ↦ r'.embedUnitary O).prod) * (r.embedUnitary O *
            (rs.map fun r' ↦ r'.embedUnitary O).prod) = r.embedUnitary O * ((rs.map fun r' ↦
            r'.embedUnitary O).prod * r.embedUnitary O) * (rs.map fun r' ↦ r'.embedUnitary O).prod
            := by simp only [mul_assoc]
        _ = (r.embedUnitary O * r.embedUnitary O) * ((rs.map fun r' ↦ r'.embedUnitary O).prod *
                (rs.map fun r' ↦ r'.embedUnitary O).prod) := by
            rw [← hcomm]; simp only [mul_assoc]
        _ = 1 := by rw [← r.embedUnitary_mul, hO, r.embedUnitary_one, one_mul, ih hpair']
theorem groverParallelMarkingOracle_mul_self {n : ℕ} (w : ℕ) (S : Finset (Fin (2 ^ n))) :
  groverParallelMarkingOracle w S * groverParallelMarkingOracle w S = 1 := by
  let slotR : Fin w → QRegister (n + 1) ((n + 1) * w) := fun i ↦
    QRegister.block (i.val * (n + 1)) (n + 1) (by nlinarith [i.isLt])
  have hpair : ((List.finRange w).map slotR).Pairwise QRegister.DisjointWires := by
    rw [List.pairwise_map]; refine (List.nodup_finRange w).imp fun {i j} hij ↦ ?_
    have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h); rcases lt_or_gt_of_ne hne with hlt | hgt
    · refine QRegister.block_disjoint_of_le _ _ _ _ _ _ ?_; have : (i.val + 1) * (n + 1) ≤ j.val *
        (n + 1) := Nat.mul_le_mul_right (n + 1) hlt; linarith
    · rw [QRegister.disjoint_comm]; refine QRegister.block_disjoint_of_le _ _ _ _ _ _ ?_
      have : (j.val + 1) * (n + 1) ≤ i.val * (n + 1) := Nat.mul_le_mul_right (n + 1) hgt; linarith
  have heq : groverParallelMarkingOracle w S = (((List.finRange w).map slotR).map fun r ↦
    r.embedUnitary (groverSetMarkingOracle S)).prod := by
    simp [groverParallelMarkingOracle, List.ofFn_eq_map, List.map_map, Function.comp_def, slotR]
  rw [heq]; exact list_prod_embedUnitary_mul_self (groverSetMarkingOracle S)
    (groverSetMarkingOracle_mul_self S) _ hpair
private lemma tagFreeStep_mul_self_ne_one {Q : ℕ} (U : Unitary (2 ^ Q)) (hU : U * U = 1) :
  tagFreeStep U * tagFreeStep U ≠ 1 := by
  intro h; have hmat : ((tagFreeStep U * tagFreeStep U).1) (0 : Fin (2 ^ Q)) (0 : Fin (2 ^ Q)) =
      (1 : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) (0 : Fin (2 ^ Q)) (0 : Fin (2 ^ Q)) :=
    congrFun (congrFun (congrArg Subtype.val h) 0) 0
  have hUU : U.1 * U.1 = 1 := congrArg Subtype.val hU; change ((freeStepPhase • U.1) *
    (freeStepPhase • U.1)) 0 0 = 1 at hmat
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hUU, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at hmat; exact freeStepPhase_sq_ne_one hmat
/-- Every non-oracle involution `U` (`U * U = 1`) tagged by `tagFreeStep` has zero
  embedded-oracle
  cost against `groverParallelMarkingOracle w S`. -/
theorem ofEmbeddedOracle_tagFreeStep_eq_zero {n w Q : ℕ} (S : Finset (Fin (2 ^ n))) (U : Unitary (2
  ^ Q)) (hU : U * U = 1) : (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle w
  S)).unitaryCost (tagFreeStep U) = 0 := by
  have hne : ∀ r : QRegister ((n + 1) * w) Q, tagFreeStep U ≠ r.embedUnitary
    (groverParallelMarkingOracle w S) := by
    intro r hr; apply tagFreeStep_mul_self_ne_one U hU; rw [hr, ← r.embedUnitary_mul,
      groverParallelMarkingOracle_mul_self, r.embedUnitary_one]
  simp [CostModel.ofEmbeddedOracle, hne]
/-- Swap two computational-basis states `a` and `b` in `Fin d`. -/
noncomputable def swapUnitary {d : ℕ} (a b : Fin d) : Unitary d :=
  permutationUnitary (Equiv.swap a b)
@[simp]
theorem swapUnitary_mul_self {d : ℕ} (a b : Fin d) : swapUnitary a b * swapUnitary a b = 1 :=
  permutationUnitary_swap_mul_self a b
private lemma permutationUnitary_apply {d : ℕ} (e : Equiv.Perm (Fin d)) (k m : Fin d) :
  (permutationUnitary e).1 k m = (Pi.single (e m) (1 : ℂ) : Fin d → ℂ) k := by
  have h := permutationUnitary_mulVec_single e m 1; rw [Matrix.mulVec_single_one] at h
  exact congrFun h k
private lemma conj_permutationUnitary_apply {d : ℕ} (e : Equiv.Perm (Fin d)) (A : Matrix (Fin d)
  (Fin d) ℂ) (i j : Fin d) : ((permutationUnitary e).1ᴴ * A * (permutationUnitary e).1) i j = A (e
  i) (e j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, permutationUnitary_apply, Pi.single_apply]
/-- Finite `.qIf` dispatch over a list of indices `o: Fin d` matching `e σ = o.val`. -/
def branchOnFin {Step Var : Type} {Q w d : ℕ} (e : Expr Var)
    (f : Fin d → OracleDynamicCircuit Step Var Q w) :
    List (Fin d) → OracleDynamicCircuit Step Var Q w
  | [] => .skip
  | o :: rest =>
      .qIf (fun σ ↦ e σ = (o.val : ℤ)) (f o) (branchOnFin e f rest)
lemma wp_compile_branchOnFin {Step Var : Type} [DecidableEq Var] {Q w d : ℕ} (compileStep : Step →
  QProg Var (2 ^ Q)) (oracle : Unitary (2 ^ w)) (e : Expr Var) (f : Fin d → OracleDynamicCircuit
  Step Var Q w) (l : List (Fin d)) (o : Fin d) (ho : o ∈ l) (Θ : CQAssertion (Store Var) (2 ^ Q)) (τ
    : Store
  Var) (he : e τ = (o.val : ℤ)) : wp ((branchOnFin e f l).compile compileStep oracle) Θ τ = wp ((f
  o).compile compileStep oracle) Θ τ := by
  induction l with
  | nil => cases ho
  | cons hd tl ih =>
    simp only [branchOnFin, OracleDynamicCircuit.compile, wp_qIf]; by_cases hhd : o = hd
    · subst hhd; simp [he]
    · have hne : e τ ≠ (hd.val : ℤ) :=
        (by rw [he]; intro h; apply hhd; exact Fin.ext (Int.ofNat.inj h)); simp only [hne,
        ↓reduceIte]; exact ih (List.mem_of_ne_of_mem hhd ho)
/-- Simulate `qset` inside `OracleDynamicCircuit` by measuring the whole `Q`-qubit system
  into `res` and conditionally swapping the measured basis state `|o⟩` to `|0⟩`. -/
noncomputable def qsetSim {Var : Type} {ow : ℕ} (_n _m Q : ℕ) (res : Var) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ow :=
  .seq (.measure res (QRegister.whole Q))
    (branchOnFin (fun σ ↦ σ res) (fun o ↦ .step (tagFreeStep (swapUnitary o 0)))
      (List.finRange (2 ^ Q)))
/-- Reset the `Q`-qubit quantum state to `|0⟩` and deterministically set the classical
  variable
  `res` to `target.val` with zero oracle cost. -/
noncomputable def setResCircuit {Var : Type} {ow : ℕ} (n m Q : ℕ) (res : Var)
    (target : Fin (2 ^ Q)) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ow :=
  .seq (qsetSim n m Q res) (.seq (.step (tagFreeStep (swapUnitary 0 target))) (.seq (.measure res
  (QRegister.whole Q)) (.step (tagFreeStep (swapUnitary target 0)))))
private lemma wp_qAssign_tagFreeStep' {Var : Type} {d : ℕ} (U : Unitary d) (Θ : CQAssertion (Store
    Var) d) :
  CQAssertion.qAssign (tagFreeStep U) Θ = CQAssertion.qAssign U Θ := by
  funext σ; refine Subtype.ext (Subtype.ext ?_); rw [qhlQAssign_val,
    qhlQAssign_val, tagFreeStep_val, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, freeStepPhase_mul_star_self, one_smul]
private lemma wp_qAssign_mat {Var : Type} {d : ℕ} (U : Unitary d) (θ : CQAssertion (Store Var) d) (σ
    : Store
  Var) : (CQAssertion.qAssign U θ σ).1.mat = U.1ᴴ * (θ σ).1.mat * U.1 :=
  qhlQAssign_val U θ σ
theorem wp_qsetSim {Var : Type} [DecidableEq Var] {ow n m Q : ℕ} (res : Var)
    (oracle : Unitary (2 ^ ow)) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var)
    (Φ : Observable (Fin (2 ^ Q)))
    (hΘ : ∀ o : Fin (2 ^ Q), Θ (Store.subst σ res (o.val : ℤ)) = Φ) :
    ((wp ((qsetSim n m Q res).compile QProg.qAssign oracle) Θ) σ).1.1 =
      (Φ.1.1 0 0) • (1 : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) := by
  simp only [qsetSim, OracleDynamicCircuit.compile, wp_qSeq, wp_measureReg_coe_aux,
    HermitianMat.val_eq_coe, HermitianMat.mat_finset_sum]
  have hterm : ∀ o : Fin (2 ^ Q), (((wp ((branchOnFin (fun σ ↦ σ res) (fun o ↦ .step (tagFreeStep
    (swapUnitary o 0))) (List.finRange (2 ^ Q))).compile QProg.qAssign oracle) Θ)
      (Store.subst σ res (Int.ofNat o.val))).1.conj
      ((QRegister.whole Q).basisOutcomeProjector o)ᴴ).mat = (Φ.1.mat 0 0) •
    compProj o := by
    intro o; rw [HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
      QRegister.basisOutcomeProjector, QRegister.whole_embedMatrix, compProj_conjTranspose,
      wp_compile_branchOnFin QProg.qAssign oracle (fun τ ↦ τ res) (fun o ↦
      .step (tagFreeStep (swapUnitary o 0))) (List.finRange (2 ^ Q)) o (List.mem_finRange o) Θ
      (Store.subst σ res (Int.ofNat o.val)) (by simp)]; simp only [OracleDynamicCircuit.compile,
      wp_qAssign, wp_qAssign_tagFreeStep', wp_qAssign_mat]
    have hΘo : (Θ (Store.subst σ res (Int.ofNat o.val))).1.mat = Φ.1.mat :=
      congrArg (fun A : Observable (Fin (2 ^ Q)) ↦ A.1.mat) (hΘ o)
    rw [hΘo, compProj_mul_mul, swapUnitary, conj_permutationUnitary_apply, Equiv.swap_apply_left]
  exact (Finset.sum_congr rfl fun o _ ↦ hterm o).trans (by rw [← Finset.smul_sum, compProj_sum])
lemma wp_qMeasure_subst_same_const {Var : Type} [DecidableEq Var] {d i : ℕ} (ℳ : Measurement d i) (x
  : Var) (Ψ : CQAssertion (Store Var) d) (σ : Store Var) (val : ℤ) : CQAssertion.qMeasure ℳ x Ψ
    (Store.subst
  σ x val) = CQAssertion.qMeasure ℳ x Ψ σ := by
  refine Subtype.ext (Subtype.ext ?_); simp only [CQAssertion.qMeasure_coe, HermitianMat.val_eq_coe,
    HermitianMat.mat_finset_sum]; refine Finset.sum_congr rfl fun o _ ↦ ?_
  have h : Store.subst (Store.subst σ x val) x (Int.ofNat o.1) = Store.subst σ x (Int.ofNat o.1) :=
    Store.subst_subst_same_const σ x val (o.val : ℤ); exact congrArg (fun τ ↦ ((Ψ τ).1.conj (ℳ.1
    o)ᴴ).mat) h
private lemma sum_smul_compProj_apply {d : ℕ} (c : Fin d → ℂ) (i : Fin d) :
    (∑ o : Fin d, c o • compProj o) i i = c i := by simp [Matrix.sum_apply, compProj_apply]
theorem wp_setResCircuit {Var : Type} [DecidableEq Var] {ow n m Q : ℕ} (res : Var) (target : Fin (2
  ^ Q)) (oracle : Unitary (2 ^ ow)) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) : ((wp
  ((setResCircuit n m Q res target).compile QProg.qAssign oracle) Θ) σ).1.1 = (((Θ (Store.subst σ
  res (target.val : ℤ))).1.1 0 0) • (1 : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ)) := by
  let tail : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ow := .seq (.step (tagFreeStep
    (swapUnitary 0 target))) (.seq (.measure res (QRegister.whole Q)) (.step (tagFreeStep
    (swapUnitary target 0))))
  change ((wp ((qsetSim n m Q res).compile QProg.qAssign oracle) (wp (tail.compile QProg.qAssign
    oracle) Θ)) σ).1.1 = _
  let Φ : Observable (Fin (2 ^ Q)) := wp (tail.compile QProg.qAssign oracle) Θ σ
  have hΦ : ∀ o : Fin (2 ^ Q), wp (tail.compile QProg.qAssign oracle) Θ (Store.subst σ res (o.val :
    ℤ)) = Φ := by
    intro o; dsimp only [Φ, tail, OracleDynamicCircuit.compile, QProg.measureRegister]
    simp only [wp_qSeq, wp_qAssign, wp_qMeasure, CQAssertion.qAssign_apply]
    rw [wp_qMeasure_subst_same_const]
  have hmat : Φ.1.mat = (swapUnitary 0 target).1ᴴ * (∑ o' : Fin (2 ^ Q), (((Θ (Store.subst σ res
    (Int.ofNat o'.val))).1.mat (Equiv.swap target 0 o') (Equiv.swap target 0 o')) • compProj o')) *
    (swapUnitary 0 target).1 := by
    simp only [Φ, tail, OracleDynamicCircuit.compile, wp_qSeq, wp_qAssign, wp_qAssign_tagFreeStep',
      wp_qAssign_mat, wp_measureReg_coe_aux, HermitianMat.mat_finset_sum]
    congr 1; congr 1; refine Finset.sum_congr rfl fun o' _ ↦ ?_; rw [HermitianMat.conj_apply_mat,
      Matrix.conjTranspose_conjTranspose, QRegister.basisOutcomeProjector,
      QRegister.whole_embedMatrix, compProj_conjTranspose, wp_qAssign_mat, compProj_mul_mul,
      swapUnitary, conj_permutationUnitary_apply]; rfl
  rw [wp_qsetSim res oracle (wp (tail.compile QProg.qAssign oracle) Θ) σ Φ hΦ]; congr 1
  rw [HermitianMat.val_eq_coe, HermitianMat.val_eq_coe, hmat, swapUnitary,
    conj_permutationUnitary_apply, Equiv.swap_apply_left, sum_smul_compProj_apply,
    Equiv.swap_apply_left]; rfl
private noncomputable def registerCompleteMeasurement {n k : ℕ} (r : QRegister k n) :
    CompleteMeasurement (2 ^ n) (2 ^ k) :=
  ⟨r.basisOutcomeProjector, by
    simp [QRegister.basisOutcomeProjector_conjTranspose, QRegister.basisOutcomeProjector_mul_self]⟩
lemma lossless_measureRegister {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (r : QRegister k
  n) : Lossless (QProg.measureRegister res r) := by
  have h : QProg.measureRegister (Var := Var) res r = QProg.qMeasure res
    (registerCompleteMeasurement r).toMeasurement := congrArg (QProg.qMeasure res) (Subtype.ext rfl)
  rw [h]; exact Lossless.qMeasure res (registerCompleteMeasurement r)
private lemma lossless_compile_branchOnFin_swap {Var : Type} [DecidableEq Var] {Q w : ℕ} (oracle :
  Unitary (2 ^ w)) (e : Expr Var) (l : List (Fin (2 ^ Q))) : Lossless ((branchOnFin e (fun o ↦ .step
  (tagFreeStep (swapUnitary o 0))) l).compile QProg.qAssign oracle) := by
  induction l with
  | nil =>
    rw [show (branchOnFin e (fun o ↦ .step (tagFreeStep (swapUnitary o 0))) []).compile
      QProg.qAssign oracle = .skip from rfl]; exact Lossless.skip
  | cons o rest ih =>
    rw [show (branchOnFin e (fun o ↦ .step (tagFreeStep (swapUnitary o 0))) (o :: rest)).compile
      QProg.qAssign oracle = .qIf (fun σ ↦ e σ = (o.val : ℤ)) (.qAssign (tagFreeStep (swapUnitary o
      0))) ((branchOnFin e (fun o ↦ .step (tagFreeStep (swapUnitary o 0))) rest).compile
      QProg.qAssign oracle) from rfl]; exact Lossless.qIf _ (Lossless.qAssign (tagFreeStep
      (swapUnitary o 0))) ih
private lemma costBound_zero_step_tagFreeStep_swap {Var : Type} [DecidableEq Var] {n w Q : ℕ} (S :
  Finset (Fin (2 ^ n))) (a b : Fin (2 ^ Q)) : CostBound (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle w S)) (.qAssign (tagFreeStep (swapUnitary a b)) : QProg Var (2 ^ Q))
  0 := by
  intro state; rw [expectedCost_qAssign, ofEmbeddedOracle_tagFreeStep_eq_zero (w := w) S
    (swapUnitary a b) (swapUnitary_mul_self a b)]; simp
private lemma costBound_zero_compile_branchOnFin_swap {Var : Type} [DecidableEq Var] {n w Q : ℕ} (S
  : Finset (Fin (2 ^ n))) (e : Expr Var) (l : List (Fin (2 ^ Q))) : CostBound
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle w S)) ((branchOnFin e (fun o ↦ .step
  (tagFreeStep (swapUnitary o 0))) l).compile QProg.qAssign (groverParallelMarkingOracle w S)) 0 :=
  by
  induction l with
  | nil =>
    rw [show (branchOnFin e (fun o ↦ .step (tagFreeStep (swapUnitary o 0))) []).compile
      QProg.qAssign (groverParallelMarkingOracle w S) = .skip from rfl]; exact CostBound.skip_zero _
  | cons o rest ih =>
    rw [show (branchOnFin e (fun o ↦ .step (tagFreeStep (swapUnitary o 0))) (o :: rest)).compile
      QProg.qAssign (groverParallelMarkingOracle w S) = .qIf (fun σ ↦ e σ = (o.val : ℤ)) (.qAssign
      (tagFreeStep (swapUnitary o 0))) ((branchOnFin e (fun o ↦ .step (tagFreeStep (swapUnitary o
      0))) rest).compile QProg.qAssign (groverParallelMarkingOracle w S)) from rfl, ← max_self (0 :
      ℝ≥0)]; exact CostBound.qIf (fun σ ↦ e σ = (o.val : ℤ)) (costBound_zero_step_tagFreeStep_swap S
      o 0) ih
lemma costBound_zero_measureRegister {Var : Type} [DecidableEq Var] {n w Q k : ℕ} (S : Finset (Fin
  (2 ^ n))) (res : Var) (r : QRegister k Q) : CostBound (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle w S)) (QProg.measureRegister res r) 0 := by
  intro state; rw [QProg.measureRegister, expectedCost_qMeasure]; simp
lemma costBound_zero_seq {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {model : CostModel d} {p₁
    p₂ : QProg Var d} (h₁ : CostBound model p₁ 0) (h₂ : CostBound model p₂ 0) : CostBound model
    (.qSeq p₁ p₂) 0 := by rw [← add_zero (0 : ℝ≥0)]; exact CostBound.seq h₁ h₂
theorem lossless_And_costBound_qsetSim_setRes {Var : Type} [DecidableEq Var] {n m w Q : ℕ} (S :
  Finset (Fin (2 ^ n))) (res : Var) (target : Fin (2 ^ Q)) : Lossless ((qsetSim n m Q res).compile
  QProg.qAssign (groverParallelMarkingOracle w S)) ∧ Lossless ((setResCircuit n m Q res
  target).compile QProg.qAssign (groverParallelMarkingOracle w S)) ∧ CostBound
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle w S)) ((qsetSim n m Q res).compile
  QProg.qAssign (groverParallelMarkingOracle w S)) 0 ∧ CostBound (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle w S)) ((setResCircuit n m Q res target).compile QProg.qAssign
  (groverParallelMarkingOracle w S)) 0 := by
  have hqset_eq : (qsetSim n m Q res).compile QProg.qAssign (groverParallelMarkingOracle w S) =
    .qSeq (QProg.measureRegister res (QRegister.whole Q)) ((branchOnFin (fun σ ↦ σ res) (fun o ↦
    .step (tagFreeStep (swapUnitary o 0))) (List.finRange (2 ^ Q))).compile QProg.qAssign
    (groverParallelMarkingOracle w S)) := rfl; have hset_eq : (setResCircuit n m Q res
    target).compile QProg.qAssign (groverParallelMarkingOracle w S) = .qSeq ((qsetSim n m Q
    res).compile QProg.qAssign (groverParallelMarkingOracle w S)) (.qSeq (.qAssign (tagFreeStep
    (swapUnitary 0 target))) (.qSeq (QProg.measureRegister res (QRegister.whole Q)) (.qAssign
    (tagFreeStep (swapUnitary target 0))))) := rfl
  have hqset_loss : Lossless ((qsetSim n m Q res).compile QProg.qAssign (groverParallelMarkingOracle
    w S)) := by
    rw [hqset_eq]; exact Lossless.seq (lossless_measureRegister res (QRegister.whole Q))
      (lossless_compile_branchOnFin_swap (groverParallelMarkingOracle w S) (fun σ ↦ σ res)
        (List.finRange (2 ^ Q)))
  have hset_loss : Lossless ((setResCircuit n m Q res target).compile QProg.qAssign
    (groverParallelMarkingOracle w S)) := by
    rw [hset_eq]; exact Lossless.seq hqset_loss (Lossless.seq (Lossless.qAssign (tagFreeStep
      (swapUnitary 0 target))) (Lossless.seq (lossless_measureRegister res (QRegister.whole Q))
      (Lossless.qAssign (tagFreeStep (swapUnitary target 0)))))
  have hqset_cost : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle w S))
    ((qsetSim n m Q res).compile QProg.qAssign (groverParallelMarkingOracle w S)) 0 := by
    rw [hqset_eq]; exact costBound_zero_seq (costBound_zero_measureRegister S res (QRegister.whole
      Q)) (costBound_zero_compile_branchOnFin_swap S (fun σ ↦ σ res) (List.finRange (2 ^ Q)))
  have hset_cost : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle w S))
    ((setResCircuit n m Q res target).compile QProg.qAssign (groverParallelMarkingOracle w S)) 0
    := by
    rw [hset_eq]
    exact costBound_zero_seq hqset_cost (costBound_zero_seq (costBound_zero_step_tagFreeStep_swap S
      0 target) (costBound_zero_seq (costBound_zero_measureRegister S res (QRegister.whole Q))
      (costBound_zero_step_tagFreeStep_swap S target 0)))
  exact ⟨hqset_loss, hset_loss, hqset_cost, hset_cost⟩
end QuantumComputation.Specs
end
end Sec_UnitPhaseFreeStepReset
section Sec_EigenplaneGroverOperator
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix Kronecker NNReal
/-- Multi-target phase oracle matrix on `Fin (2 ^ n)` flipping the sign of every `x ∈ R`. -/
def multiOracleMatrix {n : ℕ} (R : Finset (Fin (2 ^ n))) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Matrix.diagonal (fun x ↦ if x ∈ R then -1 else 1)
@[simp]
theorem multiOracleMatrix_conjTranspose {n : ℕ} (R : Finset (Fin (2 ^ n))) : (multiOracleMatrix R)ᴴ
  = multiOracleMatrix R := by
  ext i j; simp only [multiOracleMatrix, Matrix.diagonal_conjTranspose]
  congr 1; funext x; by_cases hx : x ∈ R <;> simp [hx]
@[simp]
theorem multiOracleMatrix_mul_self {n : ℕ} (R : Finset (Fin (2 ^ n))) : multiOracleMatrix R *
  multiOracleMatrix R = 1 := by
  simp only [multiOracleMatrix, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one
  split_ifs <;> ring
/-- Pure state vector on `Fin (2 ^ n)` after `K` multi-target Grover iterations for subset
  `R`. -/
noncomputable def multiGroverState {n : ℕ} (R : Finset (Fin (2 ^ n))) :
    ℕ → Fin (2 ^ n) → ℂ
  | 0 => fun _ ↦ (1 / √(2 ^ n) : ℝ)
  | K + 1 => Grover.diffuserMatrix *ᵥ multiOracleMatrix R *ᵥ multiGroverState R K
/-- Ancilla reflection matrix `(1 / √2) * [[1, -1], [-1, -1]]` on `Fin (2 ^ 1)` mapping
  `|0⟩ ↔ |−⟩` with `Mᴴ = M` and `M * M = 1`. -/
noncomputable def ancToggleMatrix : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ :=
  fun i j ↦ if i = 0 ∧ j = 0 then (1 / √2 : ℂ) else -(1 / √2 : ℂ)
@[simp]
theorem ancToggleMatrix_conjTranspose : ancToggleMatrixᴴ = ancToggleMatrix := by
  ext i j; simp only [ancToggleMatrix, Matrix.conjTranspose_apply]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]
/-- Kronecker product of an `n`-qubit address matrix and a `1`-qubit ancilla matrix
  reindexed
  onto `Fin (2 ^ (n + 1))` via `splitBasisEquiv n 1`. -/
noncomputable def slotReindex (n : ℕ)
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (B : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) :
    Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ :=
  Matrix.reindex (splitBasisEquiv n 1).symm (splitBasisEquiv n 1).symm (A ⊗ₖ B)
@[simp]
theorem slotReindex_one (n : ℕ) : slotReindex n 1 1 = 1 := by
  rw [slotReindex, Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
@[simp]
theorem slotReindex_mul (n : ℕ) (A₁ A₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (B₁ B₂ : Matrix (Fin
  (2 ^ 1)) (Fin (2 ^ 1)) ℂ) : slotReindex n A₁ B₁ * slotReindex n A₂ B₂ = slotReindex n (A₁ * A₂)
  (B₁ * B₂) := by
  symm; change Matrix.reindex (splitBasisEquiv n 1).symm (splitBasisEquiv n 1).symm
    ((A₁ * A₂) ⊗ₖ (B₁ * B₂)) = _; rw [Matrix.mul_kronecker_mul]
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ (splitBasisEquiv n 1).symm) _ _
@[simp]
theorem slotReindex_conjTranspose (n : ℕ) (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (B : Matrix
  (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) : (slotReindex n A B)ᴴ = slotReindex n Aᴴ Bᴴ := by
  simp [slotReindex, Matrix.conjTranspose_kronecker]
theorem ancToggleMatrix_mul_self : ancToggleMatrix * ancToggleMatrix = 1 := by
  ext i j; change (∑ k : Fin 2, ancToggleMatrix i k * ancToggleMatrix k j) =
    (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
  rw [Fin.sum_univ_two]; fin_cases i <;> fin_cases j <;> simp [ancToggleMatrix] <;> ring
private lemma diffuserMatrix_conjTranspose (n : ℕ) : (Grover.diffuserMatrix (n := n))ᴴ =
  Grover.diffuserMatrix (n := n) := by
  ext i j; simp [Grover.diffuserMatrix, Matrix.sub_apply, Matrix.one_apply, eq_comm]
private lemma diffuserMatrix_mul_self (n : ℕ) : Grover.diffuserMatrix (n := n) *
  Grover.diffuserMatrix (n := n) = 1 := by
  have h : Grover.diffuserMatrix (n := n) * (Grover.diffuserMatrix (n := n))ᴴ = 1 :=
    (by have h0 := (Grover.diffuserUnitary (n := n)).2.2; rwa [← Matrix.star_eq_conjTranspose])
  rwa [diffuserMatrix_conjTranspose] at h
/-- Single-slot initial preparation unitary `(H^{⊗ n} ⊗ ancToggleMatrix)`
  mapping `|0⟩|0⟩ ↦ |u_n⟩|−⟩`. -/
noncomputable def prepSlotUnitary (n : ℕ) : Unitary (2 ^ (n + 1)) :=
  ⟨slotReindex n (hadamardMatrix n) ancToggleMatrix, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, slotReindex_conjTranspose,
      slotReindex_mul, hadamardMatrix_conjTranspose, hadamardMatrix_mul_self,
      ancToggleMatrix_conjTranspose, ancToggleMatrix_mul_self, slotReindex_one]⟩
/-- Single-slot phase-unmarking diagonal unitary on `T ⊆ S`. -/
noncomputable def unmarkSlotUnitary {n : ℕ} (T : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  ⟨slotReindex n (multiOracleMatrix T) 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, slotReindex_conjTranspose,
      slotReindex_mul, multiOracleMatrix_conjTranspose, multiOracleMatrix_mul_self,
      Matrix.conjTranspose_one, mul_one, slotReindex_one]⟩
/-- Single-slot Grover diffuser unitary `diffuserMatrix ⊗ I_2`. -/
noncomputable def diffuserSlotUnitary (n : ℕ) : Unitary (2 ^ (n + 1)) :=
  ⟨slotReindex n Grover.diffuserMatrix 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, slotReindex_conjTranspose,
      slotReindex_mul, diffuserMatrix_conjTranspose, diffuserMatrix_mul_self,
      Matrix.conjTranspose_one, mul_one, slotReindex_one]⟩
/-- Single-slot verification preparation unitary `I_{2^n} ⊗ ancToggleMatrix`
  mapping `|x⟩|−⟩ ↦ |x⟩|0⟩`. -/
noncomputable def verPrepSlotUnitary (n : ℕ) : Unitary (2 ^ (n + 1)) :=
  ⟨slotReindex n 1 ancToggleMatrix, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, slotReindex_conjTranspose,
      slotReindex_mul, Matrix.conjTranspose_one, mul_one, ancToggleMatrix_conjTranspose,
      ancToggleMatrix_mul_self, slotReindex_one]⟩
/-- Single-slot verification flag-clearing unitary on already-discovered targets `T`. -/
noncomputable abbrev clearSlotFlagsUnitary {n : ℕ} (T : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  groverSetMarkingOracle T
/-- Composite single-slot Grover iteration unitary. -/
noncomputable def singleSlotIterUnitary {n : ℕ} (S T : Finset (Fin (2 ^ n))) :
    Unitary (2 ^ (n + 1)) :=
  diffuserSlotUnitary n * unmarkSlotUnitary T * groverSetMarkingOracle S
/-- Total single-slot unitary for one `K`-iteration punctuated attempt followed by
  verification. -/
noncomputable def singleSlotAttemptUnitary {n : ℕ} (S T : Finset (Fin (2 ^ n))) (K : ℕ) :
    Unitary (2 ^ (n + 1)) :=
  clearSlotFlagsUnitary T * groverSetMarkingOracle S * verPrepSlotUnitary n *
    (singleSlotIterUnitary S T) ^ K * prepSlotUnitary n
/-- Single-slot subset-confinement diagonal indicator: `1` iff `b = 1 → x ∈ A`
  (equivalently `b = 0 ∨ (b = 1 ∧ x ∈ A)`). -/
def validSlotInd {n : ℕ} (A : Finset (Fin (2 ^ n))) (idx : Fin (2 ^ (n + 1))) : ℂ :=
  if (splitBasisEquiv n 1 idx).2 = 1 → (splitBasisEquiv n 1 idx).1 ∈ A then 1 else 0
theorem slotUnitaries_involution {n : ℕ} (T : Finset (Fin (2 ^ n))) : prepSlotUnitary n *
  prepSlotUnitary n = 1 ∧ unmarkSlotUnitary T * unmarkSlotUnitary T = 1 ∧ diffuserSlotUnitary n *
  diffuserSlotUnitary n = 1 ∧ verPrepSlotUnitary n * verPrepSlotUnitary n = 1 ∧
  clearSlotFlagsUnitary T * clearSlotFlagsUnitary T = 1 := by
  refine ⟨?_, ?_, ?_, ?_, groverSetMarkingOracle_mul_self T⟩
  · apply Subtype.ext; change slotReindex n (hadamardMatrix n) ancToggleMatrix *
      slotReindex n (hadamardMatrix n) ancToggleMatrix = 1; rw [slotReindex_mul,
      hadamardMatrix_mul_self, ancToggleMatrix_mul_self, slotReindex_one]
  · apply Subtype.ext
    change slotReindex n (multiOracleMatrix T) 1 * slotReindex n (multiOracleMatrix T) 1 = 1
    rw [slotReindex_mul, multiOracleMatrix_mul_self, mul_one, slotReindex_one]
  · apply Subtype.ext
    change slotReindex n Grover.diffuserMatrix 1 * slotReindex n Grover.diffuserMatrix 1 = 1
    rw [slotReindex_mul, diffuserMatrix_mul_self, mul_one, slotReindex_one]
  · apply Subtype.ext; change slotReindex n 1 ancToggleMatrix * slotReindex n 1 ancToggleMatrix = 1
    rw [slotReindex_mul, mul_one, ancToggleMatrix_mul_self, slotReindex_one]
private lemma phiMonadicQ_bounds (w : ℕ) : (7 / 20 : ℝ) ≤ (phiMonadicQ w : ℝ) ∧ (phiMonadicQ w : ℝ)
  ≤ 7 / 5 := by unfold phiMonadicQ; split <;> norm_num
private lemma phiDyadicQ_bounds (w : ℕ) : (7 / 20 : ℝ) ≤ (phiDyadicQ w : ℝ) ∧ (phiDyadicQ w : ℝ) ≤ 7
  / 5 := by unfold phiDyadicQ; split <;> norm_num
private lemma phiTriadicQ_bounds (w : ℕ) : (7 / 20 : ℝ) ≤ (phiTriadicQ w : ℝ) ∧ (phiTriadicQ w : ℝ)
  ≤ 7 / 5 := by unfold phiTriadicQ; split <;> norm_num
lemma stagePhiReal_bounds (w r : ℕ) : (7 / 20 : ℝ) ≤ stagePhiReal w r ∧ stagePhiReal w r ≤ 7 / 5 :=
  by
  unfold stagePhiReal stagePhiQ
  split
  · exact phiTriadicQ_bounds w
  · exact phiDyadicQ_bounds w
  · exact phiMonadicQ_bounds w
lemma sin_multiHalfAngle {r d : ℕ} (hrd : r ≤ d) : Real.sin (multiHalfAngle r d) = Real.sqrt (r : ℝ)
  / Real.sqrt (d : ℝ) := by
  apply Real.sin_arcsin
  · have : (0 : ℝ) ≤ Real.sqrt (r : ℝ) / Real.sqrt (d : ℝ) := (by positivity); linarith
  · rcases eq_zero_or_pos d with rfl | hd
    · have : r = 0 := (by omega); subst this; simp
    · have hd' : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd); exact (div_le_one
        hd').2 (Real.sqrt_le_sqrt (by exact_mod_cast hrd))
theorem multiP_succ_stageIterations_pos {n w r : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ 2 ^ n) : 0 <
  multiP_succ (stageIterations (stagePhiReal w r) n r) r (2 ^ n) ∧ multiP_succ (stageIterations
  (stagePhiReal w r) n r) r (2 ^ n) ≤ 1 := by
  refine ⟨?_, Real.sin_sq_le_one _⟩; unfold stageIterations; split_ifs with hge
  · unfold multiP_succ; set θ := multiHalfAngle r (2 ^ n); set φ := stagePhiReal w r; set K :=
      (round (φ / (2 * θ))).toNat; have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
    have hd_pos : 0 < ((2 ^ n : ℕ) : ℝ) := (by positivity)
    have hθ_pos : 0 < θ := Real.arcsin_pos.2 (by positivity); rcases stagePhiReal_bounds w r with
      ⟨hφ_lo, hφ_hi⟩; have hφ_pos : 0 < φ := (by linarith); obtain ⟨hK_lo, hK_hi⟩ :=
      odd_round_div_sub_mem_Icc hθ_pos hφ_pos.le; have h16384 : (16384 : ℝ) * (r : ℝ) ≤ ((2 ^ n : ℕ)
      : ℝ) := (by exact_mod_cast hge)
    let c : ℝ := ((2 ^ n : ℕ) : ℝ) / (r : ℝ)
    have hc64 : 64 ≤ c := (le_div_iff₀ hr_pos).2 (by linarith)
    have hθ_eq : θ = Real.arcsin (1 / Real.sqrt c) := by
      change Real.arcsin (Real.sqrt (r : ℝ) / Real.sqrt ((2 ^ n : ℕ) : ℝ)) = _; congr 1
      rw [Real.sqrt_div hd_pos.le, one_div_div]
    have hθ_le : θ ≤ 9 / 50 := by
      rw [hθ_eq]
      exact arcsin_one_div_sqrt_le (by linarith) (by norm_num) (by norm_num) (by nlinarith)
    have hsin_pos : 0 < Real.sin ((2 * (K : ℝ) + 1) * θ) := Real.sin_pos_of_pos_of_lt_pi
      (by linarith) (by linarith [Real.pi_gt_three]); exact sq_pos_of_pos hsin_pos
  · unfold multiP_succ; have hsin : Real.sin ((2 * ((0 : ℕ) : ℝ) + 1) * multiHalfAngle r (2 ^ n)) =
        Real.sqrt (r : ℝ) / Real.sqrt ((2 ^ n : ℕ) : ℝ) := by
      rw [Nat.cast_zero, mul_zero, zero_add, one_mul]; exact sin_multiHalfAngle hrd
    rw [hsin]; have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1); have hd_pos : 0 < ((2 ^ n : ℕ)
      : ℝ) := (by positivity); positivity
private noncomputable def slotVec {n : ℕ} (v : Fin (2 ^ n) → ℂ) (a : Fin (2 ^ 1) → ℂ) :
    Fin (2 ^ (n + 1)) → ℂ := fun idx ↦ v (splitBasisEquiv n 1 idx).1 * a (splitBasisEquiv n 1 idx).2
private noncomputable def minusVec : Fin (2 ^ 1) → ℂ :=
  fun b ↦ if b = 0 then (1 / √2 : ℂ) else -(1 / √2 : ℂ)
private lemma slotReindex_mulVec {n : ℕ} (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (B : Matrix (Fin
  (2 ^ 1)) (Fin (2 ^ 1)) ℂ) (v : Fin (2 ^ n) → ℂ) (a : Fin (2 ^ 1) → ℂ) : slotReindex n A B *ᵥ
  slotVec v a = slotVec (A *ᵥ v) (B *ᵥ a) := by
  ext idx; simp only [slotReindex, Matrix.mulVec, dotProduct, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, Matrix.kroneckerMap_apply, slotVec]
  let f : Fin (2 ^ n) × Fin (2 ^ 1) → ℂ := fun p ↦
    A (splitBasisEquiv n 1 idx).1 p.1 * B (splitBasisEquiv n 1 idx).2 p.2 * (v p.1 * a p.2)
  change (∑ j, f (splitBasisEquiv n 1 j)) = _; rw [(splitBasisEquiv n 1).sum_comp f,
    Fintype.sum_prod_type]; dsimp only [f]
  rw [Finset.sum_mul_sum]; refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring
private lemma splitBasisEquiv_zero (n : ℕ) : splitBasisEquiv n 1 (0 : Fin (2 ^ (n + 1))) = (0, 0) :=
  by apply finProdFinEquiv.injective; ext; simp [splitBasisEquiv, finProdFinEquiv]
private lemma single_zero_eq_slotVec (n : ℕ) : (Pi.single 0 1 : Fin (2 ^ (n + 1)) → ℂ) = slotVec
  (Pi.single 0 1) (Pi.single 0 1) := by
  ext idx; by_cases h : idx = 0
  · subst h; rw [slotVec, splitBasisEquiv_zero]; simp
  · simp only [slotVec, Pi.single_apply]; have hpair : splitBasisEquiv n 1 idx ≠ (0, 0) :=
      (by rw [← splitBasisEquiv_zero n]; exact (splitBasisEquiv n 1).injective.ne h)
    by_cases h1 : (splitBasisEquiv n 1 idx).1 = 0
    · have h2 : (splitBasisEquiv n 1 idx).2 ≠ 0 := fun h2 ↦ hpair (Prod.ext h1 h2); rw [ite_eq_right
        h, ite_eq_left h1, ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h, ite_eq_right h1, zero_mul]
private lemma ancToggleMatrix_mulVec_single_zero : ancToggleMatrix *ᵥ (Pi.single 0 1 : Fin (2 ^ 1) →
  ℂ) = minusVec := by ext b; rw [Matrix.mulVec_single_one]; simp [ancToggleMatrix, minusVec]
private lemma ancToggleMatrix_mulVec_minusVec : ancToggleMatrix *ᵥ minusVec = (Pi.single 0 1 : Fin
  (2 ^ 1) → ℂ) := by
  rw [← ancToggleMatrix_mulVec_single_zero, Matrix.mulVec_mulVec, ancToggleMatrix_mul_self,
    Matrix.one_mulVec]
private lemma hadamardMatrix_mulVec_single_zero {n : ℕ} (R : Finset (Fin (2 ^ n))) : hadamardMatrix
  n *ᵥ (Pi.single 0 1 : Fin (2 ^ n) → ℂ) = multiGroverState R 0 := by
  ext x; rw [Matrix.mulVec_single_one, Matrix.col_apply, hadamardMatrix_apply_zero,
    multiGroverState]; simp
private lemma prepSlotUnitary_mulVec_single_zero {n : ℕ} (R : Finset (Fin (2 ^ n))) :
  (prepSlotUnitary n).1 *ᵥ (Pi.single 0 1 : Fin (2 ^ (n + 1)) → ℂ) = slotVec (multiGroverState R 0)
  minusVec := by
  change slotReindex n (hadamardMatrix n) ancToggleMatrix *ᵥ Pi.single 0 1 = _
  rw [single_zero_eq_slotVec, slotReindex_mulVec, hadamardMatrix_mulVec_single_zero R,
    ancToggleMatrix_mulVec_single_zero]
private lemma splitBasisEquiv_tableAddPerm_symm {n : ℕ} (f : Fin (2 ^ n) → Fin (2 ^ 1)) (idx : Fin
  (2 ^ (n + 1))) : splitBasisEquiv n 1 ((tableAddPerm f).symm idx) = ((splitBasisEquiv n 1 idx).1,
  (splitBasisEquiv n 1 idx).2 - f (splitBasisEquiv n 1 idx).1) := by
  simp [tableAddPerm, addRightShear]
private lemma groverSetMarkingOracle_mulVec {n : ℕ} (S : Finset (Fin (2 ^ n))) (v : Fin (2 ^ (n +
  1)) → ℂ) (idx : Fin (2 ^ (n + 1))) : ((groverSetMarkingOracle S).1 *ᵥ v) idx = v ((tableAddPerm
  fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0).symm idx) := by
  let e : Equiv.Perm (Fin (2 ^ (n + 1))) :=
    tableAddPerm fun x ↦ if x ∈ S then (1 : Fin (2 ^ 1)) else 0
  change (Equiv.Perm.permMatrix ℂ (e⁻¹) *ᵥ v) idx = v (e.symm idx)
  rw [Matrix.permMatrix_mulVec]; rfl
private lemma minusVec_sub_one (b : Fin (2 ^ 1)) : minusVec (b - 1) = -minusVec b := by
  have hfin2 : ∀ c : Fin (2 ^ 1), c = 0 ∨ c = 1 := fin2_zero_or_one_82
  rcases hfin2 b with rfl | rfl
  · have h01 : (0 : Fin (2 ^ 1)) - 1 = 1 := Fin.ext rfl
    have h1ne : (1 : Fin (2 ^ 1)) ≠ 0 := fun h ↦ Nat.one_ne_zero (congrArg Fin.val h)
    simp [minusVec, h01, h1ne]
  · have h1ne : (1 : Fin (2 ^ 1)) ≠ 0 := fun h ↦ Nat.one_ne_zero (congrArg Fin.val h)
    simp [minusVec, h1ne]
private lemma multiOracleMatrix_mulVec {n : ℕ} (R : Finset (Fin (2 ^ n))) (v : Fin (2 ^ n) → ℂ) (i :
  Fin (2 ^ n)) : (multiOracleMatrix R *ᵥ v) i = if i ∈ R then -v i else v i := by
  simp [multiOracleMatrix, Matrix.mulVec_diagonal]
private lemma groverSetMarkingOracle_mulVec_slotVec_minusVec {n : ℕ} (S : Finset (Fin (2 ^ n))) (v :
  Fin (2 ^ n) → ℂ) : (groverSetMarkingOracle S).1 *ᵥ slotVec v minusVec = slotVec (multiOracleMatrix
  S *ᵥ v) minusVec := by
  ext idx; rw [groverSetMarkingOracle_mulVec, slotVec, splitBasisEquiv_tableAddPerm_symm, slotVec,
    multiOracleMatrix_mulVec]; dsimp only; by_cases hx : (splitBasisEquiv n 1 idx).1 ∈ S
  · rw [ite_eq_left hx, ite_eq_left hx, minusVec_sub_one]; ring
  · rw [ite_eq_right hx, ite_eq_right hx, sub_zero]
private lemma multiOracleMatrix_mul_of_subset {n : ℕ} {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) :
  multiOracleMatrix T * multiOracleMatrix S = multiOracleMatrix (S \ T) := by
  simp only [multiOracleMatrix, Matrix.diagonal_mul_diagonal]; congr 1; funext x
  by_cases hT : x ∈ T
  · simp [hT, hTS hT]
  · by_cases hS : x ∈ S <;> simp [hT, hS]
private lemma singleSlotIterUnitary_mulVec_slotVec_minusVec {n : ℕ} {S T : Finset (Fin (2 ^ n))}
  (hTS : T ⊆ S) (v : Fin (2 ^ n) → ℂ) : (singleSlotIterUnitary S T).1 *ᵥ slotVec v minusVec =
  slotVec (Grover.diffuserMatrix *ᵥ multiOracleMatrix (S \ T) *ᵥ v) minusVec := by
  change (slotReindex n Grover.diffuserMatrix 1 * slotReindex n (multiOracleMatrix T) 1 *
    (groverSetMarkingOracle S).1) *ᵥ slotVec v minusVec = _; rw [← Matrix.mulVec_mulVec,
    groverSetMarkingOracle_mulVec_slotVec_minusVec, slotReindex_mul, mul_one, slotReindex_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, multiOracleMatrix_mul_of_subset hTS,
    ← Matrix.mulVec_mulVec]
private lemma singleSlotIterUnitary_pow_mulVec {n : ℕ} {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (K
  : ℕ) : ((singleSlotIterUnitary S T) ^ K).1 *ᵥ ((prepSlotUnitary n).1 *ᵥ (Pi.single 0 1 : Fin (2 ^
  (n + 1)) → ℂ)) = slotVec (multiGroverState (S \ T) K) minusVec := by
  induction K with
  | zero =>
    rw [pow_zero]; change (1 : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ) *ᵥ _ = _
    rw [Matrix.one_mulVec, prepSlotUnitary_mulVec_single_zero]
  | succ K ih =>
    change ((singleSlotIterUnitary S T).1 ^ (K + 1)) *ᵥ _ = _; rw [pow_succ' (singleSlotIterUnitary
      S T).1 K, ← Matrix.mulVec_mulVec]
    change (singleSlotIterUnitary S T).1 *ᵥ (((singleSlotIterUnitary S T) ^ K).1 *ᵥ _) = _; rw [ih,
      singleSlotIterUnitary_mulVec_slotVec_minusVec hTS, multiGroverState]
private lemma finTwo_sub_sub_of_subset {n : ℕ} {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (x : Fin
  (2 ^ n)) (b : Fin (2 ^ 1)) : b - (if x ∈ T then (1 : Fin (2 ^ 1)) else 0) - (if x ∈ S then (1 :
  Fin (2 ^ 1)) else 0) = b - (if x ∈ S \ T then (1 : Fin (2 ^ 1)) else 0) := by
  have h11 : ∀ c : Fin (2 ^ 1), c - 1 - 1 = c := fun c ↦ by
    rcases fin2_zero_or_one_82 c with rfl | rfl <;> exact Fin.ext rfl
  by_cases hT : x ∈ T
  · simp [hT, hTS hT, h11]
  · by_cases hS : x ∈ S <;> simp [hT, hS]
private lemma singleSlotAttemptUnitary_mulVec_single_zero {n : ℕ} {S T : Finset (Fin (2 ^ n))} (hTS
  : T ⊆ S) (K : ℕ) (idx : Fin (2 ^ (n + 1))) : ((singleSlotAttemptUnitary S T K).1 *ᵥ (Pi.single 0 1
  : Fin (2 ^ (n + 1)) → ℂ)) idx = if (splitBasisEquiv n 1 idx).2 = (if (splitBasisEquiv n 1 idx).1 ∈
  S \ T then (1 : Fin (2 ^ 1)) else 0) then multiGroverState (S \ T) K (splitBasisEquiv n 1 idx).1
  else 0 := by
  have hchain : (singleSlotAttemptUnitary S T K).1 *ᵥ (Pi.single 0 1 : Fin (2 ^ (n + 1)) → ℂ) =
    (clearSlotFlagsUnitary T).1 *ᵥ ((groverSetMarkingOracle S).1 *ᵥ (slotVec (multiGroverState (S \
    T) K) (Pi.single 0 1))) := by
    change ((clearSlotFlagsUnitary T).1 * (groverSetMarkingOracle S).1 * (verPrepSlotUnitary n).1 *
      ((singleSlotIterUnitary S T) ^ K).1 * (prepSlotUnitary n).1) *ᵥ Pi.single 0 1 = _
    simp only [← Matrix.mulVec_mulVec]; rw [singleSlotIterUnitary_pow_mulVec hTS K]
    have hver : (verPrepSlotUnitary n).1 *ᵥ slotVec (multiGroverState (S \ T) K) minusVec = slotVec
      (multiGroverState (S \ T) K) (Pi.single 0 1) := by
      change slotReindex n 1 ancToggleMatrix *ᵥ _ = _; rw [slotReindex_mulVec, Matrix.one_mulVec,
        ancToggleMatrix_mulVec_minusVec]
    rw [hver]
  rw [hchain, clearSlotFlagsUnitary, groverSetMarkingOracle_mulVec, groverSetMarkingOracle_mulVec,
    slotVec, splitBasisEquiv_tableAddPerm_symm, splitBasisEquiv_tableAddPerm_symm]
  dsimp only; rw [finTwo_sub_sub_of_subset hTS, Pi.single_apply]; simp only [sub_eq_zero, mul_ite,
    mul_one, mul_zero]
private lemma sum_multiOracleMatrix_mulVec {n : ℕ} (R : Finset (Fin (2 ^ n))) (v : Fin (2 ^ n) → ℂ)
  : ∑ i, (multiOracleMatrix R *ᵥ v) i = ∑ i, v i - 2 * ∑ i ∈ R, v i := by
  simp_rw [multiOracleMatrix_mulVec]; have hfun : (fun i : Fin (2 ^ n) ↦ if i ∈ R then -v i else v
    i) = fun i ↦ v i - if i ∈ R then 2 * v i else 0 := (by funext i; split_ifs <;> ring); rw [hfun,
    Finset.sum_sub_distrib]; congr 1; rw [← Finset.sum_filter, Finset.filter_univ_mem,
    Finset.mul_sum]
private lemma multi_sin_step {r d : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ d) (k : ℕ) : Real.sin ((2 * (k : ℝ)
  + 3) * multiHalfAngle r d) / Real.sqrt (r : ℝ) = Real.sin ((2 * (k : ℝ) + 1) * multiHalfAngle r d)
  / Real.sqrt (r : ℝ) + 2 / (d : ℝ) * (Real.sqrt (d : ℝ) * Real.cos ((2 * (k : ℝ) + 2) *
  multiHalfAngle r d)) := by
  set θ := multiHalfAngle r d
  have hr_pos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr1); have htrig :=
    Real.sin_sub_sin ((2 * (k : ℝ) + 3) * θ) ((2 * (k : ℝ) + 1) * θ)
  rw [show ((2 * (k : ℝ) + 3) * θ - (2 * (k : ℝ) + 1) * θ) / 2 = θ by ring,
    show ((2 * (k : ℝ) + 3) * θ + (2 * (k : ℝ) + 1) * θ) / 2 = (2 * (k : ℝ) + 2) * θ by ring,
    sub_eq_iff_eq_add, sin_multiHalfAngle hrd] at htrig; rw [htrig, add_comm, add_div]; congr 1
  calc
    2 * (Real.sqrt (r : ℝ) / Real.sqrt (d : ℝ)) * Real.cos ((2 * (k : ℝ) + 2) * θ) /
        Real.sqrt (r : ℝ)
      = (Real.sqrt (r : ℝ) / Real.sqrt (r : ℝ)) * (1 / Real.sqrt (d : ℝ)) *
          (2 * Real.cos ((2 * (k : ℝ) + 2) * θ)) := by ring
    _ = 2 / (d : ℝ) * (Real.sqrt (d : ℝ) * Real.cos ((2 * (k : ℝ) + 2) * θ)) := by
        rw [div_self hr_pos.ne', ← Real.sqrt_div_self']; ring
private lemma multi_cos_step {r d : ℕ} (hrd : r ≤ d) (k : ℕ) : Real.sqrt (d : ℝ) * Real.cos ((2 * (k
  : ℝ) + 2) * multiHalfAngle r d) = Real.sqrt (d : ℝ) * Real.cos (2 * (k : ℝ) * multiHalfAngle r d)
  - 2 * (Real.sqrt (r : ℝ) * Real.sin ((2 * (k : ℝ) + 1) * multiHalfAngle r d)) := by
  set θ := multiHalfAngle r d; have htrig := Real.cos_sub_cos (2 * (k : ℝ) * θ) ((2 * (k : ℝ) + 2) *
    θ)
  rw [show (2 * (k : ℝ) * θ + (2 * (k : ℝ) + 2) * θ) / 2 = (2 * (k : ℝ) + 1) * θ by ring,
    show (2 * (k : ℝ) * θ - (2 * (k : ℝ) + 2) * θ) / 2 = -θ by ring, Real.sin_neg] at htrig
  have hy : Real.cos ((2 * (k : ℝ) + 2) * θ) = Real.cos (2 * (k : ℝ) * θ) - 2 * Real.sin ((2 * (k :
    ℝ) + 1) * θ) * Real.sin θ := (by linarith)
  rw [hy, mul_sub]; congr 1; rcases eq_zero_or_pos d with rfl | hd
  · have : r = 0 := (by omega); subst this; simp
  · have hd_sqrt : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
    rw [sin_multiHalfAngle hrd]
    calc
      Real.sqrt (d : ℝ) * (2 * Real.sin ((2 * (k : ℝ) + 1) * θ) *
          (Real.sqrt (r : ℝ) / Real.sqrt (d : ℝ)))
        = 2 * Real.sin ((2 * (k : ℝ) + 1) * θ) *
            (Real.sqrt (d : ℝ) * (Real.sqrt (r : ℝ) / Real.sqrt (d : ℝ))) := by ring
      _ = 2 * (Real.sqrt (r : ℝ) * Real.sin ((2 * (k : ℝ) + 1) * θ)) := by
          rw [mul_div_cancel₀ _ hd_sqrt]; ring
private lemma multi_sin_step_complex {n r : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ 2 ^ n) (k : ℕ) : (Real.sin
  ((2 * (k : ℝ) + 3) * multiHalfAngle r (2 ^ n)) / Real.sqrt (r : ℝ) : ℂ) = (Real.sin ((2 * (k : ℝ)
  + 1) * multiHalfAngle r (2 ^ n)) / Real.sqrt (r : ℝ) : ℂ) + (2 : ℂ) / (2 ^ n : ℂ) * (Real.sqrt (2
  ^ n : ℝ) * Real.cos ((2 * (k : ℝ) + 2) * multiHalfAngle r (2 ^ n)) : ℂ) := by
  have h := congrArg (fun x : ℝ ↦ (x : ℂ)) (multi_sin_step hr1 hrd k); push_cast at h; simpa using h
private lemma multi_cos_step_complex {n r : ℕ} (hrd : r ≤ 2 ^ n) (k : ℕ) : (Real.sqrt (2 ^ n : ℝ) *
  Real.cos ((2 * (k : ℝ) + 2) * multiHalfAngle r (2 ^ n)) : ℂ) = (Real.sqrt (2 ^ n : ℝ) * Real.cos
  (2 * (k : ℝ) * multiHalfAngle r (2 ^ n)) : ℂ) - 2 * (Real.sqrt (r : ℝ) * Real.sin ((2 * (k : ℝ) +
  1) * multiHalfAngle r (2 ^ n)) : ℂ) := by
  have h := congrArg (fun x : ℝ ↦ (x : ℂ)) (multi_cos_step hrd k); push_cast at h; simpa using h
theorem multiGroverState_amplitude_eq {n : ℕ} (R : Finset (Fin (2 ^ n))) (hr1 : 1 ≤ R.card) (k : ℕ)
  : (∀ x ∈ R, multiGroverState R k x = (Real.sin ((2 * (k : ℝ) + 1) * multiHalfAngle R.card (2 ^ n))
  / Real.sqrt (R.card : ℝ) : ℂ)) ∧ ∑ i, multiGroverState R k i = (Real.sqrt (2 ^ n : ℝ) * Real.cos
  (2 * (k : ℝ) * multiHalfAngle R.card (2 ^ n)) : ℂ) := by
  have hrd : R.card ≤ 2 ^ n := (by simpa using R.card_le_univ); have hr_sqrt : Real.sqrt (R.card :
    ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hr1)).ne'
  induction k with
  | zero =>
    constructor
    · intro x _; simp only [multiGroverState, Nat.cast_zero, mul_zero, zero_add, one_mul]
      rw [sin_multiHalfAngle hrd, ← Complex.ofReal_div]; congr 1; rw [div_right_comm, div_self
        hr_sqrt]; simp
    · simp only [multiGroverState, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_zero, mul_zero]; norm_cast
      simpa [div_eq_mul_inv] using Real.div_sqrt (x := ((2 ^ n : ℕ) : ℝ))
  | succ k ih =>
    rcases ih with ⟨htarget, hsum⟩
    have hsumR : ∑ i ∈ R, multiGroverState R k i = (Real.sqrt (R.card : ℝ) * Real.sin ((2 * (k : ℝ)
      + 1) * multiHalfAngle R.card (2 ^ n)) : ℂ) := by
      rw [Finset.sum_congr rfl htarget, Finset.sum_const, nsmul_eq_mul, ← Complex.ofReal_div, ←
        Complex.ofReal_natCast, ← Complex.ofReal_mul]
      have hcard : (R.card : ℝ) * (Real.sin ((2 * (k : ℝ) + 1) * multiHalfAngle R.card (2 ^ n)) /
        Real.sqrt (R.card : ℝ)) = Real.sqrt (R.card : ℝ) * Real.sin ((2 * (k : ℝ) + 1) *
        multiHalfAngle R.card (2 ^ n)) := by
        calc
          (R.card : ℝ) * (Real.sin ((2 * (k : ℝ) + 1) * multiHalfAngle R.card (2 ^ n)) /
                Real.sqrt (R.card : ℝ)) = ((R.card : ℝ) / Real.sqrt (R.card : ℝ)) *
              Real.sin ((2 * (k : ℝ) + 1) * multiHalfAngle R.card (2 ^ n)) := by ring
          _ = Real.sqrt (R.card : ℝ) *
              Real.sin ((2 * (k : ℝ) + 1) * multiHalfAngle R.card (2 ^ n)) := by
            rw [Real.div_sqrt]
      simpa only [Complex.ofReal_mul] using congrArg (fun x : ℝ ↦ (x : ℂ)) hcard
    constructor
    · intro x hx; rw [multiGroverState, Grover.diffuserMatrix_mulVec, sum_multiOracleMatrix_mulVec,
        multiOracleMatrix_mulVec, ite_eq_left_iff.2 (fun h ↦ (h hx).elim), htarget x hx, hsum,
        hsumR]; rw [← multi_cos_step_complex hrd k]; rw [show (2 * ((k + 1 : ℕ) : ℝ) + 1) *
        multiHalfAngle R.card (2 ^ n) = (2 * (k : ℝ) + 3) * multiHalfAngle R.card (2 ^ n)
        by push_cast; ring]; rw [multi_sin_step_complex hr1 hrd k]; ring
    · rw [multiGroverState, Grover.sum_diffuserMatrix_mulVec, sum_multiOracleMatrix_mulVec,
        hsum, hsumR, ← multi_cos_step_complex hrd k]; congr 2; push_cast; ring_nf
private lemma sum_star_mul_multiGroverState_subset {n : ℕ} (R B : Finset (Fin (2 ^ n))) (hBR : B ⊆
  R) (K : ℕ) : (∑ x ∈ B, star (multiGroverState R K x) * multiGroverState R K x) = ((B.card : ℝ) /
  (R.card : ℝ) * multiP_succ K R.card (2 ^ n) : ℂ) := by
  rcases R.eq_empty_or_nonempty with rfl | hne
  · have hB : B = ∅ := Finset.subset_empty.mp hBR; subst hB; simp
  · have hr1 : 1 ≤ R.card := hne.card_pos; have htarget := (multiGroverState_amplitude_eq R hr1 K).1
    have hterm : ∀ x ∈ B, star (multiGroverState R K x) * multiGroverState R K x = (multiP_succ K
      R.card (2 ^ n) / (R.card : ℝ) : ℂ) := by
      intro x hx; rw [htarget x (hBR hx), ← Complex.ofReal_div, Complex.star_def,
        Complex.conj_ofReal]; norm_cast; rw [div_mul_div_comm, ← sq, ← sq, Real.sq_sqrt
        (by positivity), multiP_succ]; push_cast; rfl
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]; push_cast; ring
private lemma conjTranspose_diagonal_mul_apply_zero {D : ℕ} [NeZero D] (M : Matrix (Fin D) (Fin D)
  ℂ) (d : Fin D → ℂ) : (Mᴴ * Matrix.diagonal d * M) 0 0 = ∑ idx : Fin D, star ((M *ᵥ Pi.single 0 1)
  idx) * d idx * (M *ᵥ Pi.single 0 1) idx := by
  have hcol : ∀ idx, (M *ᵥ Pi.single 0 1) idx = M idx 0 := fun idx ↦ by simp
  simp_rw [hcol]; simp [Matrix.mul_apply, Matrix.diagonal_apply]
private lemma sum_star_mul_singleSlotAttemptUnitary {n : ℕ} (S T : Finset (Fin (2 ^ n))) (K : ℕ) : ∑
  idx : Fin (2 ^ (n + 1)), star (((singleSlotAttemptUnitary S T K).1 *ᵥ Pi.single 0 1) idx) *
  ((singleSlotAttemptUnitary S T K).1 *ᵥ Pi.single 0 1) idx = 1 := by
  have h1 := conjTranspose_diagonal_mul_apply_zero (singleSlotAttemptUnitary S T K).1 (fun _ ↦ 1)
  simp only [Matrix.diagonal_one, mul_one] at h1; rw [← h1]
  have hunit : (singleSlotAttemptUnitary S T K).1ᴴ * (singleSlotAttemptUnitary S T K).1 = 1 :=
    (by have h := (singleSlotAttemptUnitary S T K).2.1; rwa [← Matrix.star_eq_conjTranspose])
  rw [hunit, Matrix.one_apply_eq]
theorem singleSlot_subsetConfinement_entry {n : ℕ} {S T A : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hAR
  : A ⊆ S \ T) (K : ℕ) : ((singleSlotAttemptUnitary S T K).1ᴴ * Matrix.diagonal (validSlotInd (S \
  T)) * (singleSlotAttemptUnitary S T K).1) 0 0 = 1 ∧ ((singleSlotAttemptUnitary S T K).1ᴴ *
  Matrix.diagonal (validSlotInd A) * (singleSlotAttemptUnitary S T K).1) 0 0 = (1 - (((S \ T).card -
  A.card : ℕ) : ℝ) / ((S \ T).card : ℝ) * multiP_succ K (S \ T).card (2 ^ n) : ℂ) := by
  let ψ := (singleSlotAttemptUnitary S T K).1 *ᵥ (Pi.single 0 1 : Fin (2 ^ (n + 1)) → ℂ)
  have hnorm : ∑ idx : Fin (2 ^ (n + 1)), star (ψ idx) * ψ idx = 1 :=
    sum_star_mul_singleSlotAttemptUnitary S T K; constructor
  · rw [conjTranspose_diagonal_mul_apply_zero]; have hvalid : ∀ idx : Fin (2 ^ (n + 1)),
        star (ψ idx) * validSlotInd (S \ T) idx * ψ idx = star (ψ idx) * ψ idx := by
      intro idx; dsimp only [ψ, validSlotInd]; rw [singleSlotAttemptUnitary_mulVec_single_zero hTS K
        idx]; by_cases hR : (splitBasisEquiv n 1 idx).1 ∈ S \ T
      · rw [ite_eq_left (fun _ ↦ hR)]; ring
      · by_cases hb : (splitBasisEquiv n 1 idx).2 = 1
        · have h10 : (1 : Fin (2 ^ 1)) ≠ 0 := fun h ↦ Nat.one_ne_zero (congrArg Fin.val h)
          rw [ite_eq_right hR, hb, ite_eq_right h10]; ring
        · rw [ite_eq_left (fun h ↦ (hb h).elim)]; ring
    rw [Finset.sum_congr rfl fun idx _ ↦ hvalid idx]; exact hnorm
  · rw [conjTranspose_diagonal_mul_apply_zero]
    have hsplit : ∀ idx : Fin (2 ^ (n + 1)), star (ψ idx) * validSlotInd A idx * ψ idx = star (ψ
      idx) * ψ idx - star (ψ idx) * (if (splitBasisEquiv n 1 idx).2 = 1 ∧ (splitBasisEquiv n 1
      idx).1 ∈ (S \ T) \ A then 1 else 0) * ψ idx := by
      intro idx; dsimp only [ψ, validSlotInd]; rw [singleSlotAttemptUnitary_mulVec_single_zero hTS K
        idx]; by_cases hb : (splitBasisEquiv n 1 idx).2 = 1
      · by_cases hR : (splitBasisEquiv n 1 idx).1 ∈ S \ T
        · by_cases hA : (splitBasisEquiv n 1 idx).1 ∈ A
          · have hnot : ¬ ((splitBasisEquiv n 1 idx).2 = 1 ∧ (splitBasisEquiv n 1 idx).1 ∈ (S \ T) \
              A) := fun h ↦ (Finset.mem_sdiff.mp h.2).2 hA; rw [ite_eq_left (fun _ ↦ hA),
              ite_eq_right hnot]; ring
          · have hmem : (splitBasisEquiv n 1 idx).2 = 1 ∧ (splitBasisEquiv n 1 idx).1 ∈ (S \ T) \ A
              := ⟨hb, Finset.mem_sdiff.mpr ⟨hR, hA⟩⟩; have hnotA : ¬ ((splitBasisEquiv n 1 idx).2 =
              1 → (splitBasisEquiv n 1 idx).1 ∈ A) := fun h ↦ hA (h hb); rw [ite_eq_right hnotA,
              ite_eq_left hmem]; ring
        · have h10 : (1 : Fin (2 ^ 1)) ≠ 0 := fun h ↦ Nat.one_ne_zero (congrArg Fin.val h)
          rw [ite_eq_right hR, hb, ite_eq_right h10]; ring
      · have hnot : ¬ ((splitBasisEquiv n 1 idx).2 = 1 ∧ (splitBasisEquiv n 1 idx).1 ∈ (S \ T) \ A)
          := fun h ↦ hb h.1; rw [ite_eq_left (fun h ↦ (hb h).elim), ite_eq_right hnot]; ring
    rw [Finset.sum_congr rfl fun idx _ ↦ hsplit idx, Finset.sum_sub_distrib, hnorm]; congr 1
    let g : Fin (2 ^ n) × Fin (2 ^ 1) → ℂ := fun p ↦
      let v : ℂ := if p.2 = (if p.1 ∈ S \ T then (1 : Fin (2 ^ 1)) else 0) then multiGroverState (S
        \ T) K p.1 else 0
      star v * (if p.2 = 1 ∧ p.1 ∈ (S \ T) \ A then 1 else 0) * v
    have hg : ∀ idx : Fin (2 ^ (n + 1)), star (ψ idx) * (if (splitBasisEquiv n 1 idx).2 = 1 ∧
      (splitBasisEquiv n 1 idx).1 ∈ (S \ T) \ A then 1 else 0) * ψ idx = g (splitBasisEquiv n 1 idx)
      :=
      (by intro idx; dsimp only [ψ, g]; rw [singleSlotAttemptUnitary_mulVec_single_zero hTS K idx])
    rw [Finset.sum_congr rfl fun idx _ ↦ hg idx, (splitBasisEquiv n 1).sum_comp g,
      Fintype.sum_prod_type]
    have hinner : ∀ x : Fin (2 ^ n), (∑ b : Fin (2 ^ 1), g (x, b)) = if x ∈ (S \ T) \ A then star
      (multiGroverState (S \ T) K x) * multiGroverState (S \ T) K x else 0 := by
      intro x; rw [show (∑ b : Fin (2 ^ 1), g (x, b)) = g (x, 0) + g (x, 1) from Fin.sum_univ_two
        fun b : Fin 2 ↦ g (x, b)]; dsimp only [g]
      have h01 : (0 : Fin (2 ^ 1)) ≠ 1 := fun h ↦ Nat.zero_ne_one (congrArg Fin.val h)
      by_cases hxB : x ∈ (S \ T) \ A
      · have hxR : x ∈ S \ T := (Finset.mem_sdiff.mp hxB).1; simp [hxB, hxR, h01]
      · simp [hxB, h01]
    simp_rw [hinner]; rw [← Finset.sum_filter, Finset.filter_univ_mem,
      sum_star_mul_multiGroverState_subset (S \ T) ((S \ T) \ A) Finset.sdiff_subset K,
      Finset.card_sdiff_of_subset hAR]
end QuantumComputation.Specs
end
end Sec_EigenplaneGroverOperator
section Sec_HomomorphicEmbedAndOccupancy
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
/-- Unital `*-`homomorphism embedding a local `d`-qubit matrix across a list of registers. -/
noncomputable def embedList {d Q : ℕ} (regs : List (QRegister d Q))
    (A : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℂ) : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ :=
  (regs.map (fun r ↦ r.embedMatrix A)).prod
/-- Apply a single-slot unitary `U` simultaneously across all `activeSlots m k`
  disjoint slot registers. -/
noncomputable def embedAllSlots (n m k : ℕ) (U : Unitary (2 ^ (n + 1))) :
    Unitary (2 ^ findAllQubits n m k) :=
  ((slotRegList n m k).map (fun r ↦ r.embedUnitary U)).prod
/-- Repeat an `OracleDynamicCircuit` `K` times sequentially. -/
def repeatCircuit {Step Var : Type} {Q w : ℕ} :
    ℕ → OracleDynamicCircuit Step Var Q w →
      OracleDynamicCircuit Step Var Q w
  | 0, _ => .skip
  | K + 1, c => .seq (repeatCircuit K c) c
/-- One parallel Grover iteration across all `activeSlots m k` slots
  for unmarked target set `S \ T`. -/
noncomputable def groverIterBatchCircuit {Var : Type} (n m k : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k))
      Var (findAllQubits n m k) ((n + 1) * activeSlots m k) :=
  .seq (.oracle (batchOracleReg n m k))
    (.seq (.step (tagFreeStep (embedAllSlots n m k (unmarkSlotUnitary T))))
      (.step (tagFreeStep (embedAllSlots n m k (diffuserSlotUnitary n)))))
/-- One full punctuated `w`-slot attempt: reset, prepare `|u_n⟩|−⟩^{⊗ w}`, run `K` parallel
  Grover
  iterations, run parallel verification round (`|−⟩ ↦ |0⟩`, parallel oracle, clear `T`
  flags), and
  measure the whole system into `res`. -/
noncomputable def attemptBody {Var : Type} (n m k r : ℕ) (T : Finset (Fin (2 ^ n))) (res : Var) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k))
      Var (findAllQubits n m k) ((n + 1) * activeSlots m k) :=
  let Q := findAllQubits n m k
  let K := stageIterations (stagePhiReal (activeSlots m k) r) n r
  .seq (qsetSim n m Q res)
    (.seq (.step (tagFreeStep (embedAllSlots n m k (prepSlotUnitary n))))
      (.seq (repeatCircuit K (groverIterBatchCircuit n m k T))
        (.seq (.step (tagFreeStep (embedAllSlots n m k (verPrepSlotUnitary n))))
          (.seq (.oracle (batchOracleReg n m k))
            (.seq (.step (tagFreeStep (embedAllSlots n m k (clearSlotFlagsUnitary T))))
              (.measure res (QRegister.whole Q)))))))
/-- Extract slot `j`'s `(address, flag)` pair from a global measurement outcome `o`. -/
def slotOutcome (n m k : ℕ) (j : Fin (activeSlots m k))
    (o : Fin (2 ^ findAllQubits n m k)) : Fin (2 ^ n) × Fin (2 ^ 1) :=
  splitBasisEquiv n 1 ((slotReg n m k j).extractIndex o)
/-- Distinct hit addresses (where verification flag is `1`) across all active slots
  on outcome `o`. -/
def hitSet (n m k : ℕ) (o : Fin (2 ^ findAllQubits n m k)) : Finset (Fin (2 ^ n)) :=
  ((Finset.univ : Finset (Fin (activeSlots m k))).filter
    (fun j ↦ (slotOutcome n m k j o).2 = 1)).image (fun j ↦ (slotOutcome n m k j o).1)
/-- True iff fewer than `s` distinct targets were hit on global outcome `o`. -/
def stageMissOutcome (n m k s : ℕ) (o : Fin (2 ^ findAllQubits n m k)) : Bool :=
  decide ((hitSet n m k o).card < s)
/-- Extend `stageMissOutcome` to `z: ℤ` (returning `true` outside `0.. 2^Q - 1`). -/
def stageMissZ (n m k s : ℕ) (z : ℤ) : Bool :=
  if _h0 : 0 ≤ z then
    if hlt : z.toNat < 2 ^ findAllQubits n m k then
      stageMissOutcome n m k s ⟨z.toNat, hlt⟩
    else true
  else true
/-- Stage retry loop guard: continues when `< s` distinct targets hit, exits when `≥ s`. -/
def stageRetryGuard {Var : Type} (n m k s : ℕ) (res : Var) : Store Var → Prop :=
  fun σ ↦ stageMissZ n m k s (σ res) = true
instance {Var : Type} (n m k s : ℕ) (res : Var) :
    DecidablePred (stageRetryGuard n m k s res) :=
  fun σ ↦ inferInstanceAs (Decidable (stageMissZ n m k s (σ res) = true))
/-- Sorted list of distinct hit addresses on outcome `o`. -/
def extractHitList (n m k : ℕ) (o : Fin (2 ^ findAllQubits n m k)) : List (Fin (2 ^ n)) :=
  (List.finRange (2 ^ n)).filter (fun x ↦ decide (x ∈ hitSet n m k o))
/-- Deterministic `s`-tuple of distinct hit addresses extracted from outcome `o`. -/
def extractHitTuple (n m k s : ℕ) (o : Fin (2 ^ findAllQubits n m k)) (i : Fin s) : Fin (2 ^ n) :=
  let l := extractHitList n m k o
  if h : i.val < l.length then l[i.val] else ⟨0, by positivity⟩
/-- Deterministic `s`-tuple of distinct hit addresses extracted from classical integer `z:
  ℤ`. -/
def extractHitTupleZ (n m k s : ℕ) (z : ℤ) : Fin s → Fin (2 ^ n) :=
  if _h0 : 0 ≤ z then
    if hlt : z.toNat < 2 ^ findAllQubits n m k then
      extractHitTuple n m k s ⟨z.toNat, hlt⟩
    else fun _ ↦ ⟨0, by positivity⟩
  else fun _ ↦ ⟨0, by positivity⟩
private lemma unitary_list_prod_val {d : ℕ} (l : List (Unitary d)) : l.prod.1 = (l.map
  Subtype.val).prod := by
  induction l with
  | nil => rfl
  | cons u us ih => exact congrArg (u.1 * ·) ih
private lemma embedUnitary_prod_val {Q w : ℕ} (U : Unitary (2 ^ w)) (regs : List (QRegister w Q)) :
  ((regs.map fun (r : QRegister w Q) ↦ r.embedUnitary U).prod).1 = embedList regs U.1 := by
  rw [embedList, unitary_list_prod_val, List.map_map]; rfl
private lemma embedMatrix_comm_list_prod {Q w : ℕ} (A B : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ) (r :
  QRegister w Q) (regs : List (QRegister w Q)) (hdisj : ∀ r' ∈ regs, r.DisjointWires r') :
  r.embedMatrix A * (regs.map fun r' ↦ r'.embedMatrix B).prod = (regs.map fun r' ↦ r'.embedMatrix
  B).prod * r.embedMatrix A := by
  induction regs with
  | nil => simp
  | cons r₀ rs ih =>
    simp only [List.map_cons, List.prod_cons]; rw [← mul_assoc, r.embedMatrix_comm_of_disjoint r₀
      (hdisj r₀ List.mem_cons_self) A B, mul_assoc, ih (fun r' hr' ↦ hdisj r' (List.mem_cons_of_mem
      _ hr')), ← mul_assoc]
theorem embedList_mul_and_diagonal {Q w : ℕ} (A B : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ) (f : Fin
  (2 ^ w) → ℂ) (regs : List (QRegister w Q)) (hpair : regs.Pairwise QRegister.DisjointWires) :
  embedList regs A * embedList regs B = embedList regs (A * B) ∧ (embedList regs A)ᴴ = embedList
  regs Aᴴ ∧ embedList regs (Matrix.diagonal f) = Matrix.diagonal (fun o : Fin (2 ^ Q) ↦ (regs.map
  fun r ↦ f (r.extractIndex o)).prod) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold embedList
    induction regs with
    | nil => simp
    | cons r rs ih =>
      rcases List.pairwise_cons.mp hpair with ⟨hdisj, hpair'⟩; simp only [List.map_cons,
        List.prod_cons]
      calc
        (r.embedMatrix A * (rs.map fun r' ↦ r'.embedMatrix A).prod) *
            (r.embedMatrix B * (rs.map fun r' ↦ r'.embedMatrix B).prod)
          = r.embedMatrix A * ((rs.map fun r' ↦ r'.embedMatrix A).prod * r.embedMatrix B) *
              (rs.map fun r' ↦ r'.embedMatrix B).prod := by simp only [mul_assoc]
        _ = (r.embedMatrix A * r.embedMatrix B) * ((rs.map fun r' ↦ r'.embedMatrix A).prod *
                (rs.map fun r' ↦ r'.embedMatrix B).prod) := by
            rw [← embedMatrix_comm_list_prod B A r rs hdisj]; simp only [mul_assoc]
        _ = r.embedMatrix (A * B) * (rs.map fun r' ↦ r'.embedMatrix (A * B)).prod := by
            rw [← r.embedMatrix_mul, ih hpair']
  · unfold embedList
    induction regs with
    | nil => simp
    | cons r rs ih =>
      rcases List.pairwise_cons.mp hpair with ⟨hdisj, hpair'⟩
      simp only [List.map_cons, List.prod_cons, Matrix.conjTranspose_mul, ih hpair', ←
        r.embedMatrix_conjTranspose]; exact (embedMatrix_comm_list_prod Aᴴ Aᴴ r rs hdisj).symm
  · unfold embedList; clear hpair
    induction regs with
    | nil => simp [Matrix.diagonal_one]
    | cons r rs ih =>
      simp only [List.map_cons, List.prod_cons, ih, r.embedMatrix_diagonal,
        Matrix.diagonal_mul_diagonal]
private lemma basisBits_zero_local (q : ℕ) (i : Fin q) : basisBits q 0 i = 0 := by
  rw [basisBits_eq_div_mod]; simp
lemma extractIndex_zero {Q w : ℕ} (r : QRegister w Q) : r.extractIndex 0 = 0 := by
  apply (basisBits w).injective; funext i; rw [r.basisBits_extractIndex, basisBits_zero_local,
    basisBits_zero_local]
private lemma embedMatrix_mulVec_apply_replaceIndex {Q w : ℕ} (r : QRegister w Q) (A : Matrix (Fin
  (2 ^ w)) (Fin (2 ^ w)) ℂ) (v : Fin (2 ^ Q) → ℂ) (g : Fin (2 ^ Q)) : (r.embedMatrix A *ᵥ v) g = ∑
  loc : Fin (2 ^ w), A (r.extractIndex g) loc * v (r.replaceIndex g loc) :=
  r.embedMatrix_mulVec_apply A v g
private lemma embedMatrix_mulVec_eq_zero_of_extractIndex_ne {Q w : ℕ} (A : Matrix (Fin (2 ^ w)) (Fin
  (2 ^ w)) ℂ) (r r' : QRegister w Q) (hdisj : r.DisjointWires r') (idx : Fin (2 ^ w)) (v : Fin (2 ^
  Q) → ℂ) (hv : ∀ g : Fin (2 ^ Q), r.extractIndex g ≠ idx → v g = 0) (g : Fin (2 ^ Q)) (hg :
  r.extractIndex g ≠ idx) : (r'.embedMatrix A *ᵥ v) g = 0 := by
  rw [embedMatrix_mulVec_apply_replaceIndex]; refine Finset.sum_eq_zero fun loc _ ↦ ?_
  have hrep : r.extractIndex (r'.replaceIndex g loc) ≠ idx :=
    (by rw [r.extractIndex_replaceIndex_of_disjoint r' hdisj]; exact hg); rw [hv (r'.replaceIndex g
    loc) hrep, mul_zero]
private lemma embedMatrix_prod_mulVec_eq_zero_of_extractIndex_ne {Q w : ℕ} (A : Matrix (Fin (2 ^ w))
  (Fin (2 ^ w)) ℂ) (r : QRegister w Q) (rs : List (QRegister w Q)) (hdisj : ∀ r' ∈ rs,
  r.DisjointWires r') (idx : Fin (2 ^ w)) (v : Fin (2 ^ Q) → ℂ) (hv : ∀ g : Fin (2 ^ Q),
  r.extractIndex g ≠ idx → v g = 0) : ∀ g : Fin (2 ^ Q), r.extractIndex g ≠ idx → ((rs.map fun r' ↦
  r'.embedMatrix A).prod *ᵥ v) g = 0 := by
  induction rs with
  | nil => intro g hg; rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]; exact hv g hg
  | cons r₁ rs' ih =>
    intro g hg; simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    exact embedMatrix_mulVec_eq_zero_of_extractIndex_ne A r r₁ (hdisj r₁ List.mem_cons_self) idx _
      (ih (fun r' hr' ↦ hdisj r' (List.mem_cons_of_mem _ hr'))) g hg
private lemma embedMatrix_prod_mulVec_single_self {Q w : ℕ} (A : Matrix (Fin (2 ^ w)) (Fin (2 ^ w))
  ℂ) (regs : List (QRegister w Q)) (hpair : regs.Pairwise QRegister.DisjointWires) (o : Fin (2 ^ Q))
  : ((embedList regs A) *ᵥ Pi.single o 1) o = (regs.map fun r ↦ A (r.extractIndex o) (r.extractIndex
  o)).prod := by
  unfold embedList
  induction regs with
  | nil => simp
  | cons r rs ih =>
    rcases List.pairwise_cons.mp hpair with ⟨hdisj, hpair'⟩; simp only [List.map_cons,
      List.prod_cons, ← Matrix.mulVec_mulVec]
    rw [embedMatrix_mulVec_apply_replaceIndex]; rw [Finset.sum_eq_single (r.extractIndex o)]
    · rw [r.replaceIndex_extractIndex, ih hpair']
    · intro loc _ hne
      have hzero := embedMatrix_prod_mulVec_eq_zero_of_extractIndex_ne A r rs hdisj (r.extractIndex
        o) (Pi.single o 1) (fun g hg ↦ Pi.single_eq_of_ne (fun (hgo : g = o) ↦ hg (congrArg
        r.extractIndex hgo)) 1) (r.replaceIndex o loc)
        (by rw [r.extractIndex_replaceIndex]; exact hne); rw [hzero, mul_zero]
    · intro habs; exact (habs (Finset.mem_univ _)).elim
theorem embedList_apply_zero_zero {Q w : ℕ} (A : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ) (regs : List
  (QRegister w Q)) (hpair : regs.Pairwise QRegister.DisjointWires) : (embedList regs A) 0 0 = (A 0
  0) ^ regs.length := by
  have h := embedMatrix_prod_mulVec_single_self A regs hpair 0; rw [Matrix.mulVec_single_one,
    Matrix.col_apply] at h; rw [h]; have hconst : (regs.map fun r ↦ A (r.extractIndex 0)
    (r.extractIndex 0)) = List.replicate regs.length (A 0 0) :=
    (by simp_rw [extractIndex_zero]; exact List.map_const'); rw [hconst, List.prod_replicate]
private lemma unitary_mul_val {d : ℕ} (u v : Unitary d) : (u * v).1 = u.1 * v.1 := rfl
private lemma embedUnitary_prod_mul {Q w : ℕ} (U V : Unitary (2 ^ w)) (regs : List (QRegister w Q))
  (hpair : regs.Pairwise QRegister.DisjointWires) : (regs.map fun r ↦ r.embedUnitary U).prod *
  (regs.map fun r ↦ r.embedUnitary V).prod = (regs.map fun r ↦ r.embedUnitary (U * V)).prod := by
  apply Subtype.ext; rw [unitary_mul_val, embedUnitary_prod_val, embedUnitary_prod_val,
    embedUnitary_prod_val]; exact (embedList_mul_and_diagonal U.1 V.1 (fun _ ↦ 0) regs hpair).1
private lemma embedAllSlots_one (n m k : ℕ) : embedAllSlots n m k 1 = 1 := by
  unfold embedAllSlots; induction slotRegList n m k <;> simp
private lemma embedAllSlots_mul (n m k : ℕ) (U V : Unitary (2 ^ (n + 1))) : embedAllSlots n m k (U *
  V) = embedAllSlots n m k U * embedAllSlots n m k V :=
  (embedUnitary_prod_mul U V (slotRegList n m k) (slotRegList_pairwise_disjoint n m k)).symm
private lemma embedAllSlots_mul_self (n m k : ℕ) {U : Unitary (2 ^ (n + 1))} (hU : U * U = 1) :
  embedAllSlots n m k U * embedAllSlots n m k U = 1 := by
  rw [← embedAllSlots_mul, hU, embedAllSlots_one]
private lemma embedUnitary_list_prod {Q K : ℕ} (outer : QRegister K Q) : ∀ l : List (Unitary (2 ^
  K)), outer.embedUnitary l.prod = (l.map outer.embedUnitary).prod
  | [] => outer.embedUnitary_one
  | u :: us => by
    simp only [List.prod_cons, List.map_cons, outer.embedUnitary_mul, embedUnitary_list_prod outer
      us]
private lemma embedUnitary_compose {w K Q : ℕ} (outer : QRegister K Q) (inner : QRegister w K) (U :
  Unitary (2 ^ w)) : (outer.compose inner).embedUnitary U = outer.embedUnitary (inner.embedUnitary
  U) := Subtype.ext (outer.embedMatrix_compose inner U.1)
private lemma batchOracleReg_compose_block (n m k : ℕ) (j : Fin (activeSlots m k)) :
    (batchOracleReg n m k).compose
        (QRegister.block (j.val * (n + 1)) (n + 1) (by nlinarith [j.isLt])) =
      slotReg n m k j := by
  ext i; simp [batchOracleReg, slotReg, QRegister.compose, QRegister.block]
theorem batchOracleReg_embedUnitary_eq (n m k : ℕ) (S : Finset (Fin (2 ^ n))) : (batchOracleReg n m
  k).embedUnitary (groverParallelMarkingOracle (activeSlots m k) S) = embedAllSlots n m k
  (groverSetMarkingOracle S) := by
  simp only [groverParallelMarkingOracle, List.ofFn_eq_map, embedUnitary_list_prod, List.map_map,
    Function.comp_def, ← embedUnitary_compose, batchOracleReg_compose_block, embedAllSlots,
    slotRegList]
theorem embedAllSlots_conj_prodDiag_zero_zero (n m k : ℕ) (U : Unitary (2 ^ (n + 1))) (f : Fin (2 ^
  (n + 1)) → ℂ) : ((embedAllSlots n m k U).1ᴴ * Matrix.diagonal (fun o ↦ ((slotRegList n m k).map
  fun r ↦ f (r.extractIndex o)).prod) * (embedAllSlots n m k U).1) 0 0 = ((U.1ᴴ * Matrix.diagonal f
  * U.1) 0 0) ^ (activeSlots m k) := by
  have hpair := slotRegList_pairwise_disjoint n m k
  rcases embedList_mul_and_diagonal U.1ᴴ (Matrix.diagonal f) f (slotRegList n m k) hpair with
    ⟨hmul1, _, hdiag⟩; have hconj := (embedList_mul_and_diagonal U.1 U.1 f (slotRegList n m k)
    hpair).2.1; have hmul2 := (embedList_mul_and_diagonal (U.1ᴴ * Matrix.diagonal f) U.1 f
    (slotRegList n m k) hpair).1; have hmat : (embedAllSlots n m k U).1ᴴ * Matrix.diagonal (fun o ↦
    ((slotRegList n m k).map fun r ↦ f (r.extractIndex o)).prod) * (embedAllSlots n m k U).1 =
    embedList (slotRegList n m k) (U.1ᴴ * Matrix.diagonal f * U.1) :=
    (by rw [embedAllSlots, embedUnitary_prod_val, hconj, ← hdiag, hmul1, hmul2]); rw [hmat,
    embedList_apply_zero_zero _ _ hpair, slotRegList_length]
/-- Product of `validSlotInd A` across all active slots on global outcome `o`. -/
def validAllInd (n m k : ℕ) (A : Finset (Fin (2 ^ n)))
    (o : Fin (2 ^ findAllQubits n m k)) : ℂ :=
  ((slotRegList n m k).map fun r ↦ validSlotInd A (r.extractIndex o)).prod
/-- Supported stratum exit indicator: `1` iff `hitSet n m k o ⊆ R` and
  `s ≤ (hitSet n m k o).card`. -/
def stratumExitInd (n m k s : ℕ) (R : Finset (Fin (2 ^ n)))
    (o : Fin (2 ^ findAllQubits n m k)) : ℂ :=
  if hitSet n m k o ⊆ R ∧ s ≤ (hitSet n m k o).card then 1 else 0
private lemma list_prod_ite_one_zero {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] :
  (l.map (fun x ↦ if P x then (1 : ℂ) else 0)).prod = if (∀ x ∈ l, P x) then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.prod_cons, ih]; by_cases ha : P a
    · by_cases has : (∀ x ∈ as, P x)
      · rw [ite_eq_left ha, ite_eq_left has, ite_eq_left (List.forall_mem_cons.mpr ⟨ha, has⟩),
          mul_one]
      · rw [ite_eq_left ha, ite_eq_right has, ite_eq_right (fun h ↦ has (List.forall_mem_cons.mp
          h).2), mul_zero]
    · rw [ite_eq_right ha, ite_eq_right (fun h ↦ ha (List.forall_mem_cons.mp h).1), zero_mul]
lemma validAllInd_eq_hitSet_subset (n m k : ℕ) (A : Finset (Fin (2 ^ n))) (o : Fin (2 ^
  findAllQubits n m k)) : validAllInd n m k A o = if hitSet n m k o ⊆ A then 1 else 0 := by
  unfold validAllInd slotRegList validSlotInd; rw [List.map_map, Function.comp_def,
    list_prod_ite_one_zero]
  have hall : (∀ j ∈ List.finRange (activeSlots m k), (splitBasisEquiv n 1 ((slotReg n m k
    j).extractIndex o)).2 = 1 → (splitBasisEquiv n 1 ((slotReg n m k j).extractIndex o)).1 ∈ A) ↔
    hitSet n m k o ⊆ A := by
    rw [hitSet, Finset.image_subset_iff]; dsimp only [slotOutcome]; exact ⟨fun h j hj ↦ h j
      (List.mem_finRange j) (Finset.mem_filter.mp hj).2, fun h j _ hb ↦ h j (Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hb⟩)⟩
  by_cases h : hitSet n m k o ⊆ A <;> simp only [hall, h, ↓reduceIte]
lemma conj_validAllInd_zero_zero {n m k : ℕ} {S T A : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hAR : A ⊆
  S \ T) (K : ℕ) :
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    (U_all.1ᴴ * Matrix.diagonal (validAllInd n m k A) * U_all.1) 0 0 = (1 - (((S \ T).card - A.card
      : ℕ) : ℝ) / ((S \ T).card : ℝ) * multiP_succ K (S \ T).card (2 ^ n) : ℂ) ^ (activeSlots m k)
      := by
  intro U_all; unfold validAllInd; rw [embedAllSlots_conj_prodDiag_zero_zero,
    (singleSlot_subsetConfinement_entry hTS hAR K).2]
lemma conj_validAllInd_self_zero_zero {n m k : ℕ} {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (K : ℕ)
  :
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    (U_all.1ᴴ * Matrix.diagonal (validAllInd n m k (S \ T)) * U_all.1) 0 0 = 1 := by
  intro U_all; unfold validAllInd; rw [embedAllSlots_conj_prodDiag_zero_zero,
    (singleSlot_subsetConfinement_entry hTS (Finset.Subset.refl _) K).1, one_pow]
private lemma extractHitList_nodup (n m k : ℕ) (o : Fin (2 ^ findAllQubits n m k)) :
    (extractHitList n m k o).Nodup := (List.nodup_finRange (2 ^ n)).filter _
private lemma extractHitList_toFinset (n m k : ℕ) (o : Fin (2 ^ findAllQubits n m k)) :
    (extractHitList n m k o).toFinset = hitSet n m k o := by ext x; simp [extractHitList]
private lemma extractHitList_length (n m k : ℕ) (o : Fin (2 ^ findAllQubits n m k)) :
  (extractHitList n m k o).length = (hitSet n m k o).card := by
  rw [← extractHitList_toFinset, List.toFinset_card_of_nodup (extractHitList_nodup n m k o)]
theorem extractHitTuple_injective_and_mem {n m k s : ℕ} {R : Finset (Fin (2 ^ n))} {o : Fin (2 ^
  findAllQubits n m k)} (hsub : hitSet n m k o ⊆ R) (hcard : s ≤ (hitSet n m k o).card) :
  Function.Injective (extractHitTuple n m k s o) ∧ ∀ i : Fin s, extractHitTuple n m k s o i ∈ R :=
  by
  have hlen : s ≤ (extractHitList n m k o).length := (by rwa [extractHitList_length])
  have hget : ∀ i : Fin s, extractHitTuple n m k s o i = (extractHitList n m k
    o)[i.val]'(i.isLt.trans_le hlen) :=
    (by intro i; dsimp [extractHitTuple]; exact dite_eq_left (i.isLt.trans_le hlen)); refine ⟨?_,
    ?_⟩
  · intro i j hij; rw [hget i, hget j, (extractHitList_nodup n m k o).getElem_inj_iff] at hij
    exact Fin.ext hij
  · intro i; rw [hget i]; have hmem : (extractHitList n m k o)[i.val]'(i.isLt.trans_le hlen) ∈
      (extractHitList n m k o).toFinset := List.mem_toFinset.mpr (List.getElem_mem _)
    rw [extractHitList_toFinset] at hmem; exact hsub hmem
private lemma occupancyTail_zero_w {s r : ℕ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (p : ℝ) : occupancyTail s 0
  r p = 0 := by
  rcases s with _ | _ | _ | _ | s
  · omega
  · simp [occupancyTail]
  · simp [occupancyTail]
  · simp only [occupancyTail, pow_zero]; ring
  · omega
private lemma occupancyTail_succ_w {s w r : ℕ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hr1 : 1 ≤ r) (p : ℝ) :
    let α : ℝ := ((r : ℝ) - (s : ℝ) + 1) / (r : ℝ)
    occupancyTail s (w + 1) r p = (1 - α * p) * occupancyTail s w r p + α * p * occupancyTail (s -
      1) w r p := by
  intro α; have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hr1))
  rcases s with _ | _ | _ | _ | s
  · omega
  · simp only [occupancyTail, Nat.add_sub_cancel, α]; rw [pow_succ]; field_simp [hr_ne]; ring
  · simp only [occupancyTail, Nat.add_sub_cancel, α]; rw [pow_succ, pow_succ]; field_simp [hr_ne];
      ring
  · simp only [occupancyTail, Nat.add_sub_cancel, α]; rw [pow_succ, pow_succ, pow_succ]
    field_simp [hr_ne]; ring
  · omega
private lemma occupancyTail_nonneg_and_le_one {w r : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∀ {s :
  ℕ}, s ≤ 3 → s ≤ r → 0 ≤ occupancyTail s w r p ∧ occupancyTail s w r p ≤ 1 := by
  induction w with
  | zero =>
    intro s hs3 _; rcases eq_zero_or_pos s with rfl | hs1
    · simp [occupancyTail]
    · rw [occupancyTail_zero_w hs1 hs3]; exact ⟨le_rfl, zero_le_one⟩
  | succ w ih =>
    intro s hs3 hsr; rcases eq_zero_or_pos s with rfl | hs1
    · simp [occupancyTail]
    · have hr1 : 1 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
      have hs_le_r : (s : ℝ) ≤ (r : ℝ) := (by exact_mod_cast hsr)
      have hs_ge_1 : (1 : ℝ) ≤ (s : ℝ) := (by exact_mod_cast (show 1 ≤ s by omega)); set α := ((r :
        ℝ) - (s : ℝ) + 1) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
      have hα1 : α ≤ 1 := (div_le_one hr_pos).mpr (by linarith)
      have hαp0 : 0 ≤ α * p := mul_nonneg hα0 hp0; have hαp1 : α * p ≤ 1 :=
        (by have := mul_le_mul_of_nonneg_right hα1 hp0; linarith); have h1αp : 0 ≤ 1 - α * p :=
        sub_nonneg.mpr hαp1; rcases ih hs3 hsr with ⟨hTs0, hTs1⟩
      rcases ih (by omega : s - 1 ≤ 3) (by omega : s - 1 ≤ r) with ⟨hTs'0, hTs'1⟩
      rw [occupancyTail_succ_w hs1 hs3 hr1 p]; refine ⟨add_nonneg (mul_nonneg h1αp hTs0) (mul_nonneg
        hαp0 hTs'0), ?_⟩; have hle1 := mul_le_mul_of_nonneg_left hTs1 h1αp; have hle2 :=
        mul_le_mul_of_nonneg_left hTs'1 hαp0; linarith
private lemma occupancyTail_pos {w r : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : ∀ {s : ℕ}, s ≤ 3 → s
  ≤ w → s ≤ r → 0 < occupancyTail s w r p := by
  induction w with
  | zero => intro s _ hsw _; have hs0 : s = 0 := (by omega); subst hs0; simp [occupancyTail]
  | succ w ih =>
    intro s hs3 hsw hsr; rcases eq_zero_or_pos s with rfl | hs1
    · simp [occupancyTail]
    · have hr1 : 1 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
      have hs_le_r : (s : ℝ) ≤ (r : ℝ) := (by exact_mod_cast hsr)
      have hs_ge_1 : (1 : ℝ) ≤ (s : ℝ) := (by exact_mod_cast (show 1 ≤ s by omega)); set α := ((r :
        ℝ) - (s : ℝ) + 1) / (r : ℝ); have hα0 : 0 < α := div_pos (by linarith) hr_pos
      have hα1 : α ≤ 1 := (div_le_one hr_pos).mpr (by linarith)
      have hαp0 : 0 < α * p := mul_pos hα0 hp0; have hαp1 : α * p ≤ 1 :=
        (by have := mul_le_mul_of_nonneg_right hα1 hp0.le; linarith); have h1αp : 0 ≤ 1 - α * p :=
        sub_nonneg.mpr hαp1; have hTs0 := (occupancyTail_nonneg_and_le_one (w := w) hp0.le hp1 hs3
        hsr).1
      have hTs'pos := ih (by omega : s - 1 ≤ 3) (by omega : s - 1 ≤ w) (by omega : s - 1 ≤ r)
      rw [occupancyTail_succ_w hs1 hs3 hr1 p]
      exact add_pos_of_nonneg_of_pos (mul_nonneg h1αp hTs0) (mul_pos hαp0 hTs'pos)
theorem occupancyTail_stage_bounds {n m k s r : ℕ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hsw : s ≤
  activeSlots m k) (hsr : s ≤ r) (hrd : r ≤ 2 ^ n) :
    let K := stageIterations (stagePhiReal (activeSlots m k) r) n r
    let p := multiP_succ K r (2 ^ n)
    0 < occupancyTail s (activeSlots m k) r p ∧ occupancyTail s (activeSlots m k) r p ≤ 1 := by
  intro K p; have hr1 : 1 ≤ r := hs1.trans hsr; rcases multiP_succ_stageIterations_pos (w :=
    activeSlots m k) hr1 hrd with ⟨hp0, hp1⟩; exact ⟨occupancyTail_pos hp0 hp1 hs3 hsw hsr,
    (occupancyTail_nonneg_and_le_one hp0.le hp1 hs3 hsr).2⟩
private lemma conjTranspose_diagonal_mul_apply_zero' {D : ℕ} [NeZero D] (M : Matrix (Fin D) (Fin D)
  ℂ) (d : Fin D → ℂ) : (Mᴴ * Matrix.diagonal d * M) 0 0 = ∑ idx : Fin D, star ((M *ᵥ Pi.single 0 1)
  idx) * d idx * (M *ᵥ Pi.single 0 1) idx := by
  have hcol : ∀ idx, (M *ᵥ Pi.single 0 1) idx = M idx 0 := fun idx ↦ by simp
  simp_rw [hcol]; simp [Matrix.mul_apply, Matrix.diagonal_apply]
private lemma conj_diagonal_mul_valid_eq {D : ℕ} [NeZero D] (U : Unitary D) (v d : Fin D → ℂ) (hv :
  ∀ o, v o = 1 ∨ v o = 0) (h1 : (U.1ᴴ * Matrix.diagonal v * U.1) 0 0 = 1) : (U.1ᴴ * Matrix.diagonal
  d * U.1) 0 0 = (U.1ᴴ * Matrix.diagonal (fun o ↦ d o * v o) * U.1) 0 0 := by
  let ψ : Fin D → ℂ := U.1 *ᵥ Pi.single 0 1
  have hnorm : (U.1ᴴ * Matrix.diagonal (fun _ : Fin D ↦ (1 : ℂ)) * U.1) 0 0 = 1 := by
    have hunit : U.1ᴴ * U.1 = 1 := (by have h := U.2.1; rwa [← Matrix.star_eq_conjTranspose])
    simp [Matrix.diagonal_one, hunit]
  rw [conjTranspose_diagonal_mul_apply_zero'] at h1 hnorm
  have hdiff : ∑ o : Fin D, (star (ψ o) * (1 : ℂ) * ψ o - star (ψ o) * v o * ψ o) = 0 :=
    (by rw [Finset.sum_sub_distrib, hnorm, h1, sub_self])
  let t : Fin D → ℝ := fun o ↦ (1 - (v o).re) * Complex.normSq (ψ o)
  have ht_eq : ∀ o : Fin D, star (ψ o) * (1 : ℂ) * ψ o - star (ψ o) * v o * ψ o = (t o : ℂ) := by
    intro o; have hconj : star (ψ o) * ψ o = (Complex.normSq (ψ o) : ℂ) :=
      (by rw [mul_comm, Complex.star_def, Complex.mul_conj]); rcases hv o with hvo | hvo
    · simp [t, hvo]
    · rw [hvo, mul_one, mul_zero, zero_mul, sub_zero, hconj]; simp [t, hvo]
  simp_rw [ht_eq] at hdiff; rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at hdiff
  have ht_nonneg : ∀ o ∈ (Finset.univ : Finset (Fin D)), 0 ≤ t o := by
    intro o _; rcases hv o with hvo | hvo <;> simp [t, hvo, Complex.normSq_nonneg]
  have ht_zero := (Finset.sum_eq_zero_iff_of_nonneg ht_nonneg).mp hdiff
  rw [conjTranspose_diagonal_mul_apply_zero', conjTranspose_diagonal_mul_apply_zero']
  refine Finset.sum_congr rfl fun o _ ↦ ?_; rcases hv o with hvo | hvo
  · rw [hvo, mul_one]
  · have hto := ht_zero o (Finset.mem_univ o); simp only [t, hvo, Complex.zero_re, sub_zero,
      one_mul, Complex.normSq_eq_zero] at hto; change star (ψ o) * d o * ψ o = star (ψ o) * (d o * v
      o) * ψ o; rw [hto, mul_zero, mul_zero]
private lemma wp_groverIterBatchCircuit {Var : Type} [DecidableEq Var] {n m k : ℕ} (_hm : 1 ≤ m) (S
  T : Finset (Fin (2 ^ n))) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
  ((groverIterBatchCircuit n m k T).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots
  m k) S)) Θ = CQAssertion.qAssign (embedAllSlots n m k (singleSlotIterUnitary S T)) Θ := by
  simp only [groverIterBatchCircuit, OracleDynamicCircuit.compile, wp_qSeq, wp_qAssign_tagFreeStep]
  simp only [wp_qAssign, batchOracleReg_embedUnitary_eq, CQAssertion.qAssign_qAssign, ←
    embedAllSlots_mul, singleSlotIterUnitary, mul_assoc]
private lemma wp_repeatCircuit_groverIterBatchCircuit {Var : Type} [DecidableEq Var] {n m k : ℕ} (hm
  : 1 ≤ m) (S T : Finset (Fin (2 ^ n))) (K : ℕ) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m
    k)) : wp
  ((repeatCircuit K (groverIterBatchCircuit n m k T)).compile QProg.qAssign
  (groverParallelMarkingOracle (activeSlots m k) S)) Θ = CQAssertion.qAssign (embedAllSlots n m k
  ((singleSlotIterUnitary S T) ^ K)) Θ := by
  induction K generalizing Θ with
  | zero =>
    simp only [repeatCircuit, OracleDynamicCircuit.compile, wp_skip, pow_zero, embedAllSlots_one]
    exact (CQAssertion.qAssign_one Θ).symm
  | succ K ih =>
    simp only [repeatCircuit, OracleDynamicCircuit.compile, wp_qSeq, wp_groverIterBatchCircuit hm S
      T, ih, CQAssertion.qAssign_qAssign, ← embedAllSlots_mul, ← pow_succ']
private lemma sum_smul_compProj_eq_diagonal {d : ℕ} (c : Fin d → ℂ) : ∑ o : Fin d, c o • compProj o
  = Matrix.diagonal c := by
  ext i j; rw [Matrix.sum_apply]; by_cases hij : i = j
  · subst hij; simp [compProj_apply]
  · rw [Matrix.diagonal_apply_ne _ hij]; refine Finset.sum_eq_zero fun x _ ↦ ?_
    rw [Matrix.smul_apply, compProj_apply, smul_eq_mul]; split_ifs with h
    · exact (hij (h.1.trans h.2.symm)).elim
    · ring
private noncomputable def attemptTail {Var : Type} (n m k r : ℕ) (T : Finset (Fin (2 ^ n))) (res :
    Var) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n +
    1) * activeSlots m k) :=
  let Q := findAllQubits n m k
  let K := stageIterations (stagePhiReal (activeSlots m k) r) n r
  .seq (.step (tagFreeStep (embedAllSlots n m k (prepSlotUnitary n))))
    (.seq (repeatCircuit K (groverIterBatchCircuit n m k T))
      (.seq (.step (tagFreeStep (embedAllSlots n m k (verPrepSlotUnitary n))))
        (.seq (.oracle (batchOracleReg n m k))
          (.seq (.step (tagFreeStep (embedAllSlots n m k (clearSlotFlagsUnitary T))))
            (.measure res (QRegister.whole Q))))))
private lemma attemptBody_eq_seq_attemptTail {Var : Type} (n m k r : ℕ) (T : Finset (Fin (2 ^ n)))
  (res : Var) : attemptBody n m k r T res = .seq (qsetSim n m (findAllQubits n m k) res)
  (attemptTail n m k r T res) := rfl
private lemma wp_attemptTail {Var : Type} [DecidableEq Var] {n m k r : ℕ} (hm : 1 ≤ m) (S T : Finset
  (Fin (2 ^ n))) (res : Var) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
    ((attemptTail n m
  k r T res).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Θ =
  CQAssertion.qAssign (embedAllSlots n m k (singleSlotAttemptUnitary S T (stageIterations
  (stagePhiReal (activeSlots m k) r) n r))) (wp (QProg.measureRegister res (QRegister.whole
  (findAllQubits n m k))) Θ) := by
  dsimp only [attemptTail, OracleDynamicCircuit.compile, singleSlotAttemptUnitary]; rw [wp_qSeq,
    wp_qSeq, wp_qSeq, wp_qSeq, wp_qSeq]; rw [wp_qAssign_tagFreeStep, wp_qAssign_tagFreeStep,
    wp_qAssign_tagFreeStep]; rw [batchOracleReg_embedUnitary_eq,
    wp_repeatCircuit_groverIterBatchCircuit hm S T]; rw [wp_qAssign, wp_qAssign, wp_qAssign,
    wp_qAssign]; rw [CQAssertion.qAssign_qAssign, CQAssertion.qAssign_qAssign,
    CQAssertion.qAssign_qAssign, CQAssertion.qAssign_qAssign]; rw [← embedAllSlots_mul, ←
    embedAllSlots_mul, ← embedAllSlots_mul, ← embedAllSlots_mul]; simp only [mul_assoc]
private lemma wp_attemptBody_apply {Var : Type} [DecidableEq Var] {n m k r : ℕ} (hm : 1 ≤ m) (S T :
  Finset (Fin (2 ^ n))) (res : Var) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ :
    Store Var)
  :
    let Q := findAllQubits n m k; let K := stageIterations (stagePhiReal (activeSlots m k) r) n r
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    let d_Θ : Fin (2 ^ Q) → ℂ := fun o ↦ (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o
    ((wp ((attemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)) Θ) σ).1.1 = ((U_all.1ᴴ * Matrix.diagonal d_Θ * U_all.1) 0 0) • (1 :
      Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) := by
  intro Q K U_all d_Θ; rw [attemptBody_eq_seq_attemptTail, OracleDynamicCircuit.compile, wp_qSeq,
    wp_attemptTail hm S T res Θ]
  let Ψ := CQAssertion.qAssign U_all (wp (QProg.measureRegister res (QRegister.whole Q)) Θ)
  have hΨ : ∀ o : Fin (2 ^ Q), Ψ (Store.subst σ res (o.val : ℤ)) = Ψ σ := by
    intro o; simp only [Ψ, QProg.measureRegister, wp_qMeasure, CQAssertion.qAssign_apply]
    rw [wp_qMeasure_subst_same_const]
  have hmeas : (wp (QProg.measureRegister res (QRegister.whole Q)) Θ σ).1.1 = Matrix.diagonal d_Θ
    := by
    simp only [wp_measureReg_coe_aux, HermitianMat.val_eq_coe, HermitianMat.mat_finset_sum]
    have hterm : ∀ o : Fin (2 ^ Q), (((Θ (Store.subst σ res (Int.ofNat o.val))).1.conj
      ((QRegister.whole Q).basisOutcomeProjector o)ᴴ).mat) = d_Θ o • compProj o := by
      intro o; rw [HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
        QRegister.basisOutcomeProjector, QRegister.whole_embedMatrix, compProj_conjTranspose,
        compProj_mul_mul]; rfl
    exact (Finset.sum_congr rfl fun o _ ↦ hterm o).trans (sum_smul_compProj_eq_diagonal d_Θ)
  have hΨ_mat : (Ψ σ).1.1 = U_all.1ᴴ * Matrix.diagonal d_Θ * U_all.1 :=
    (by dsimp only [Ψ]; rw [qhlQAssign_val, hmeas]); rw [wp_qsetSim res
    (groverParallelMarkingOracle (activeSlots m k) S) Ψ σ (Ψ σ) hΨ, hΨ_mat]
private lemma stageMissZ_natCast (n m k s : ℕ) (o : Fin (2 ^ findAllQubits n m k)) : stageMissZ n m
  k s (o.val : ℤ) = stageMissOutcome n m k s o := by
  unfold stageMissZ; rw [dite_eq_left (Int.natCast_nonneg o.val)]
  have hlt : (o.val : ℤ).toNat < 2 ^ findAllQubits n m k := by rw [Int.toNat_natCast]; exact o.isLt
  rw [dite_eq_left hlt]; have ho : (⟨(o.val : ℤ).toNat, hlt⟩ : Fin (2 ^ findAllQubits n m k)) = o :=
    Fin.ext (Int.toNat_natCast o.val); rw [ho]
theorem wp_attemptBody_of_stratumExitInd_entry {Var : Type} [DecidableEq Var] {n m k s r : ℕ} (hm :
    1 ≤ m) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hsw : s ≤ activeSlots m k) (hsr : s ≤ r) (hrd : r ≤ 2 ^ n)
    {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (res : Var) (hstratum :
      let K := stageIterations (stagePhiReal (activeSlots m k) r) n r
      let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
      (U_all.1ᴴ * Matrix.diagonal (stratumExitInd n m k s (S \ T)) * U_all.1) 0 0 =
        (occupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n)) : ℂ)) :
    let K := stageIterations (stagePhiReal (activeSlots m k) r) n r
    let p := occupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n))
    let body := (attemptBody n m k r T res).compile QProg.qAssign
      (groverParallelMarkingOracle (activeSlots m k) S)
    wp body (liftPureProp (fun σ ↦ ¬ stageRetryGuard n m k s res σ)) = constAssertion p ∧ ∀ (Θ :
      CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ : Store Var) (c : ℝ), 0 ≤ c → c ≤ 1 → (∀
        o : Fin
      (2 ^ findAllQubits n m k), hitSet n m k o ⊆ S \ T → if stageMissOutcome n m k s o = true then
      (Θ (Store.subst σ res (o.val : ℤ))).1 = c • 1 else (Θ (Store.subst σ res (o.val : ℤ))).1 = 1)
      → ((wp body Θ) σ).1 = (p + (1 - p) * c) • 1 := by
  intro K p body; let Q := findAllQubits n m k
  let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
  have hvalid_all : (U_all.1ᴴ * Matrix.diagonal (validAllInd n m k (S \ T)) * U_all.1) 0 0 = 1 :=
    conj_validAllInd_self_zero_zero hTS K
  have hvalid_oz : ∀ o, validAllInd n m k (S \ T) o = 1 ∨ validAllInd n m k (S \ T) o = 0 := by
    intro o; rw [validAllInd_eq_hitSet_subset]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hstep_aux : ∀ (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (c : ℝ), (∀ o : Fin (2 ^
    Q),
    hitSet n m k o ⊆ S \ T → stageMissOutcome n m k s o = true → (Θ (Store.subst σ res (o.val :
    ℤ))).1.mat o o = (c : ℂ)) → (∀ o : Fin (2 ^ Q), hitSet n m k o ⊆ S \ T → stageMissOutcome n m k
    s o = false → (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o = 1) → ((wp body Θ) σ).1 = (p + (1 -
    p) * c) • 1 := by
    intro Θ σ c hmiss_Θ hhit_Θ
    let d_Θ : Fin (2 ^ Q) → ℂ := fun o ↦ (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o
    have hconj := conj_diagonal_mul_valid_eq U_all (validAllInd n m k (S \ T)) d_Θ hvalid_oz
      hvalid_all
    have hdiag : Matrix.diagonal (fun o ↦ d_Θ o * validAllInd n m k (S \ T) o) = (c : ℂ) •
      Matrix.diagonal (validAllInd n m k (S \ T)) + (1 - (c : ℂ)) • Matrix.diagonal (stratumExitInd
      n m k s (S \ T)) := by
      ext i j; by_cases hij : i = j
      · subst hij; dsimp only [d_Θ]
        simp only [Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          validAllInd_eq_hitSet_subset, stratumExitInd]; by_cases hsub : hitSet n m k i ⊆ S \ T
        · by_cases hlt : (hitSet n m k i).card < s
          · have hmiss : stageMissOutcome n m k s i = true := decide_eq_true hlt
            have hnot_ge : ¬ (hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card) := (by omega)
            rw [ite_eq_left hsub, ite_eq_right hnot_ge, hmiss_Θ i hsub hmiss]; ring
          · have hmiss : stageMissOutcome n m k s i = false := decide_eq_false hlt
            have hge : hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card := ⟨hsub, by omega⟩
            rw [ite_eq_left hsub, ite_eq_left hge, hhit_Θ i hsub hmiss]; ring
        · have hnot_ge : ¬ (hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card) := fun h ↦ hsub h.1
          rw [ite_eq_right hsub, ite_eq_right hnot_ge]; ring
      · simp [hij]
    have hentry : (U_all.1ᴴ * Matrix.diagonal d_Θ * U_all.1) 0 0 = ((p + (1 - p) * c : ℝ) : ℂ) := by
      dsimp only at hstratum; rw [hconj, hdiag]
      simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, hvalid_all]; rw [hstratum]; push_cast; ring
    apply Subtype.ext; change ((wp body Θ) σ).1.1 = ((p + (1 - p) * c) • (1 : HermitianMat (Fin (2 ^
      Q)) ℂ)).1; rw [wp_attemptBody_apply hm S T res Θ σ, hentry, HermitianMat.val_eq_coe,
      HermitianMat.mat_smul, HermitianMat.mat_one]; ext i j; simp [Complex.real_smul]
  have hstep : ∀ (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (c : ℝ), 0 ≤ c → c ≤ 1 → (∀ o
    : Fin
    (2 ^ Q), hitSet n m k o ⊆ S \ T → if stageMissOutcome n m k s o = true then (Θ (Store.subst σ
    res (o.val : ℤ))).1 = c • 1 else (Θ (Store.subst σ res (o.val : ℤ))).1 = 1) → ((wp body Θ) σ).1
    = (p + (1 - p) * c) • 1 := by
    intro Θ σ c _ _ hΘ; refine hstep_aux Θ σ c (fun o hsub hmiss ↦ ?_) (fun o hsub hmiss ↦ ?_)
    · have ho := hΘ o hsub; rw [ite_eq_left hmiss] at ho; have hmat := congrFun (congrFun (congrArg
        HermitianMat.mat ho) o) o; simp only [HermitianMat.mat_smul, HermitianMat.mat_one,
        Matrix.smul_apply, Matrix.one_apply_eq, Complex.real_smul, mul_one] at hmat; exact hmat
    · have ho := hΘ o hsub; have hnot : ¬ stageMissOutcome n m k s o = true := (by simp [hmiss])
      rw [ite_eq_right hnot] at ho; have hmat := congrFun (congrFun (congrArg HermitianMat.mat ho)
        o) o; simp only [HermitianMat.mat_one, Matrix.one_apply_eq] at hmat; exact hmat
  refine ⟨?_, hstep⟩; rcases occupancyTail_stage_bounds (m := m) (k := k) hs1 hs3 hsw hsr hrd with
    ⟨hp0, hp1⟩; funext σ; apply Subtype.ext; rw [constAssertion_apply_of_bounds p hp0.le hp1 σ]
  have hexit := hstep_aux (liftPureProp (fun τ ↦ ¬ stageRetryGuard n m k s res τ)) σ 0
    (fun o _ hmiss ↦ by
      have hg : ¬ ¬ stageRetryGuard n m k s res (Store.subst σ res (o.val : ℤ)) :=
        (by simp [stageRetryGuard, Store.subst_self, stageMissZ_natCast, hmiss])
      rw [liftPureProp_apply, ite_eq_right hg]
      simp)
    (fun o _ hmiss ↦ by
      have hg : ¬ stageRetryGuard n m k s res (Store.subst σ res (o.val : ℤ)) :=
        (by simp [stageRetryGuard, Store.subst_self, stageMissZ_natCast, hmiss])
      rw [liftPureProp_apply, ite_eq_left hg]
      simp)
  rw [hexit]; congr 1; ring
private lemma costBound_zero_tagFreeStep {Var : Type} [DecidableEq Var] {n w Q : ℕ} (S : Finset (Fin
  (2 ^ n))) (U : Unitary (2 ^ Q)) (hU : U * U = 1) : CostBound (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle w S)) (.qAssign (tagFreeStep U) : QProg Var (2 ^ Q)) 0 := by
  intro state; rw [expectedCost_qAssign, ofEmbeddedOracle_tagFreeStep_eq_zero (w := w) S U hU]; simp
private lemma costBound_one_qAssign {Var : Type} [DecidableEq Var] {n w Q : ℕ} (S : Finset (Fin (2 ^
  n))) (U : Unitary (2 ^ Q)) : CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle w
  S)) (.qAssign U : QProg Var (2 ^ Q)) 1 := by
  refine (CostBound.qAssign (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle w S)) U).mono
    ?_; unfold CostModel.ofEmbeddedOracle; dsimp; split_ifs <;> norm_num
private lemma costBound_groverIterBatchCircuit {Var : Type} [DecidableEq Var] {n m k : ℕ} (S T :
  Finset (Fin (2 ^ n))) : Lossless ((groverIterBatchCircuit (Var := Var) n m k T).compile
  QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) ∧ CostBound
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
  ((groverIterBatchCircuit (Var := Var) n m k T).compile QProg.qAssign (groverParallelMarkingOracle
  (activeSlots m k) S)) 1 := by
  rcases slotUnitaries_involution (n := n) T with ⟨_, hunmark, hdiff, _, _⟩
  simp only [groverIterBatchCircuit, OracleDynamicCircuit.compile]; refine ⟨Lossless.seq
    (Lossless.qAssign _) (Lossless.seq (Lossless.qAssign _) (Lossless.qAssign _)), ?_⟩; have h1 :=
    costBound_one_qAssign (Var := Var) (w := activeSlots m k) S ((batchOracleReg n m k).embedUnitary
    (groverParallelMarkingOracle (activeSlots m k) S))
  have h2 := costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S (embedAllSlots n m k
    (unmarkSlotUnitary T)) (embedAllSlots_mul_self n m k hunmark)
  have h3 := costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S (embedAllSlots n m k
    (diffuserSlotUnitary n)) (embedAllSlots_mul_self n m k hdiff); have h23 := CostBound.seq h2 h3;
    rw [add_zero] at h23; have h123 := CostBound.seq h1 h23
  rwa [add_zero] at h123
private lemma lossless_and_costBound_repeatCircuit_groverIter {Var : Type} [DecidableEq Var] {n m k
  : ℕ} (S T : Finset (Fin (2 ^ n))) (K : ℕ) : Lossless ((repeatCircuit K (groverIterBatchCircuit
  (Var := Var) n m k T)).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) ∧
  CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
  ((repeatCircuit K (groverIterBatchCircuit (Var := Var) n m k T)).compile QProg.qAssign
  (groverParallelMarkingOracle (activeSlots m k) S)) (K : ℝ≥0) := by
  rcases costBound_groverIterBatchCircuit (Var := Var) (n := n) (m := m) (k := k) S T with
    ⟨hloss_iter, hcost_iter⟩
  induction K with
  | zero =>
      simp only [repeatCircuit, OracleDynamicCircuit.compile, Nat.cast_zero]; exact ⟨Lossless.skip,
        CostBound.skip_zero _⟩
  | succ K ih =>
      simp only [repeatCircuit, OracleDynamicCircuit.compile, Nat.cast_add, Nat.cast_one]
      exact ⟨Lossless.seq ih.1 hloss_iter, CostBound.seq ih.2 hcost_iter⟩
theorem lossless_and_costBound_attemptBody {Var : Type} [DecidableEq Var] {n m k r : ℕ} (hm : 1 ≤ m)
  (S T : Finset (Fin (2 ^ n))) (res : Var) :
    let body := (attemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)
    let K := stageIterations (stagePhiReal (activeSlots m k) r) n r
    Lossless body ∧ CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots
      m k) S)) body ((K + 1 : ℕ) : ℝ≥0) := by
  have _ := hm; intro body K; let Q := findAllQubits n m k
  rcases slotUnitaries_involution (n := n) T with ⟨hprep, _, _, hver, hclear⟩
  rcases lossless_And_costBound_qsetSim_setRes (n := n) (m := m) (w := activeSlots m k) (Q := Q) S
    res 0 with ⟨hloss_qset, _, hcost_qset, _⟩
  rcases lossless_and_costBound_repeatCircuit_groverIter (Var := Var) (n := n) (m := m) (k := k) S T
    K with ⟨hloss_rep, hcost_rep⟩; have hbody_eq : body = .qSeq ((qsetSim n m Q res).compile
    QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) (.qSeq (.qAssign (tagFreeStep
    (embedAllSlots n m k (prepSlotUnitary n)))) (.qSeq ((repeatCircuit K (groverIterBatchCircuit n m
    k T)).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) (.qSeq (.qAssign
    (tagFreeStep (embedAllSlots n m k (verPrepSlotUnitary n)))) (.qSeq (.qAssign ((batchOracleReg n
    m k).embedUnitary (groverParallelMarkingOracle (activeSlots m k) S))) (.qSeq (.qAssign
    (tagFreeStep (embedAllSlots n m k (clearSlotFlagsUnitary T)))) (QProg.measureRegister res
    (QRegister.whole Q))))))) := rfl; rw [hbody_eq]; refine ⟨?_, ?_⟩
  · exact Lossless.seq hloss_qset (Lossless.seq (Lossless.qAssign _) (Lossless.seq hloss_rep
      (Lossless.seq (Lossless.qAssign _) (Lossless.seq (Lossless.qAssign _) (Lossless.seq
      (Lossless.qAssign _) (lossless_measureRegister res (QRegister.whole Q)))))))
  · have hc_prep := costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S (embedAllSlots
      n m k (prepSlotUnitary n)) (embedAllSlots_mul_self n m k hprep)
    have hc_ver := costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S (embedAllSlots n
      m k (verPrepSlotUnitary n)) (embedAllSlots_mul_self n m k hver)
    have hc_ora := costBound_one_qAssign (Var := Var) (w := activeSlots m k) S ((batchOracleReg n m
      k).embedUnitary (groverParallelMarkingOracle (activeSlots m k) S))
    have hc_clr := costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S (embedAllSlots n
      m k (clearSlotFlagsUnitary T)) (embedAllSlots_mul_self n m k hclear); have hc_meas :=
      costBound_zero_measureRegister (Var := Var) (w := activeSlots m k) S res (QRegister.whole Q)
    have htot := CostBound.seq hcost_qset (CostBound.seq hc_prep (CostBound.seq hcost_rep
      (CostBound.seq hc_ver (CostBound.seq hc_ora (CostBound.seq hc_clr hc_meas)))))
    convert htot using 1
    push_cast; ring
end QuantumComputation.Specs
end
end Sec_HomomorphicEmbedAndOccupancy
section Sec_HomomorphicCharacterBasis
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
private noncomputable def slotDiagExp (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ)
    (d : Fin (2 ^ findAllQubits n m k) → ℂ) : ℂ :=
  let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
  (U_all.1ᴴ * Matrix.diagonal d * U_all.1) 0 0
private lemma mat_conj_diagonal_add {D : ℕ} [NeZero D] (M : Matrix (Fin D) (Fin D) ℂ) (d₁ d₂ : Fin D
  → ℂ) : (Mᴴ * Matrix.diagonal (fun o ↦ d₁ o + d₂ o) * M) 0 0 = (Mᴴ * Matrix.diagonal d₁ * M) 0 0 +
  (Mᴴ * Matrix.diagonal d₂ * M) 0 0 := by
  have h : Mᴴ * Matrix.diagonal (fun o ↦ d₁ o + d₂ o) * M = Mᴴ * Matrix.diagonal d₁ * M + Mᴴ *
    Matrix.diagonal d₂ * M := (by rw [← Matrix.diagonal_add, mul_add, add_mul])
  exact congrFun (congrFun h 0) 0
private lemma mat_conj_diagonal_sub {D : ℕ} [NeZero D] (M : Matrix (Fin D) (Fin D) ℂ) (d₁ d₂ : Fin D
  → ℂ) : (Mᴴ * Matrix.diagonal (fun o ↦ d₁ o - d₂ o) * M) 0 0 = (Mᴴ * Matrix.diagonal d₁ * M) 0 0 -
  (Mᴴ * Matrix.diagonal d₂ * M) 0 0 := by
  have h : Mᴴ * Matrix.diagonal (fun o ↦ d₁ o - d₂ o) * M = Mᴴ * Matrix.diagonal d₁ * M - Mᴴ *
    Matrix.diagonal d₂ * M := (by rw [← Matrix.diagonal_sub, mul_sub, sub_mul])
  exact congrFun (congrFun h 0) 0
private lemma mat_conj_diagonal_const_mul {D : ℕ} [NeZero D] (M : Matrix (Fin D) (Fin D) ℂ) (c : ℂ)
  (d : Fin D → ℂ) : (Mᴴ * Matrix.diagonal (fun o ↦ c * d o) * M) 0 0 = c * (Mᴴ * Matrix.diagonal d *
  M) 0 0 := by
  have h : Mᴴ * Matrix.diagonal (c • d) * M = c • (Mᴴ * Matrix.diagonal d * M) :=
    (by rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul])
  exact congrFun (congrFun h 0) 0
private lemma mat_conj_diagonal_zero {D : ℕ} [NeZero D] (M : Matrix (Fin D) (Fin D) ℂ) : (Mᴴ *
  Matrix.diagonal (fun _ : Fin D ↦ (0 : ℂ)) * M) 0 0 = 0 := by
  have h : Mᴴ * Matrix.diagonal (fun _ : Fin D ↦ (0 : ℂ)) * M = 0 :=
    (by rw [Matrix.diagonal_zero, mul_zero, zero_mul]); exact congrFun (congrFun h 0) 0
private lemma slotDiagExp_add (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ) (d₁ d₂ : Fin (2 ^
    findAllQubits n m k) → ℂ) : slotDiagExp n m k S T K (fun o ↦ d₁ o + d₂ o) = slotDiagExp n m k S
    T K d₁ + slotDiagExp n m k S T K d₂ := mat_conj_diagonal_add _ d₁ d₂
private lemma slotDiagExp_sub (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ) (d₁ d₂ : Fin (2 ^
    findAllQubits n m k) → ℂ) : slotDiagExp n m k S T K (fun o ↦ d₁ o - d₂ o) = slotDiagExp n m k S
    T K d₁ - slotDiagExp n m k S T K d₂ := mat_conj_diagonal_sub _ d₁ d₂
private lemma slotDiagExp_const_mul (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ) (c : ℂ) (d :
  Fin (2 ^ findAllQubits n m k) → ℂ) : slotDiagExp n m k S T K (fun o ↦ c * d o) = c * slotDiagExp n
  m k S T K d := mat_conj_diagonal_const_mul _ c d
private lemma slotDiagExp_sum {α : Type*} (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ) (B :
  Finset α) (f : α → Fin (2 ^ findAllQubits n m k) → ℂ) : slotDiagExp n m k S T K (fun o ↦ ∑ x ∈ B,
  f x o) = ∑ x ∈ B, slotDiagExp n m k S T K (f x) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]; exact mat_conj_diagonal_zero (embedAllSlots n m k
      (singleSlotAttemptUnitary S T K)).1
  | @insert a B ha ih => simp_rw [Finset.sum_insert ha]; rw [slotDiagExp_add, ih]
private lemma slotDiagExp_validAllInd_self {n m k : ℕ} {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (K
  : ℕ) : slotDiagExp n m k S T K (validAllInd n m k (S \ T)) = 1 :=
  conj_validAllInd_self_zero_zero hTS K
private lemma slotDiagExp_validAllInd_empty {n m k r : ℕ} (hr1 : 1 ≤ r) {S T : Finset (Fin (2 ^ n))}
  (hTS : T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) : slotDiagExp n m k S T K (validAllInd n m k ∅) = (1
  - (multiP_succ K r (2 ^ n) : ℂ)) ^ (activeSlots m k) := by
  have h := conj_validAllInd_zero_zero (n := n) (m := m) (k := k) hTS (Finset.empty_subset _) K
  dsimp only at h; change slotDiagExp n m k S T K (validAllInd n m k ∅) = _ at h; rw [h, hr,
    Finset.card_empty, Nat.sub_zero]; have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega);
    push_cast; rw [div_self hr_ne, one_mul]
private lemma slotDiagExp_sum_singletons {n m k r : ℕ} (hr1 : 1 ≤ r) {S T : Finset (Fin (2 ^ n))}
  (hTS : T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) : slotDiagExp n m k S T K (fun o ↦ ∑ x ∈ S \ T,
  validAllInd n m k {x} o) = (r : ℂ) * (1 - ((r : ℝ) - 1) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^
  (activeSlots m k) := by
  rw [slotDiagExp_sum]; have hterm : ∀ x ∈ S \ T, slotDiagExp n m k S T K (validAllInd n m k {x}) =
        (1 - ((r : ℝ) - 1) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
    intro x hx; have h := conj_validAllInd_zero_zero (n := n) (m := m) (k := k)
      hTS (Finset.singleton_subset_iff.mpr hx) K
    dsimp only at h; change slotDiagExp n m k S T K (validAllInd n m k {x}) = _ at h; rw [h, hr,
      Finset.card_singleton, Nat.cast_sub hr1]; push_cast; rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, hr, nsmul_eq_mul]
private lemma slotDiagExp_sum_pairs {n m k r : ℕ} (hr2 : 2 ≤ r) {S T : Finset (Fin (2 ^ n))} (hTS :
  T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) : slotDiagExp n m k S T K (fun o ↦ ∑ x ∈ S \ T, ∑ y ∈ (S \
  T).erase x, validAllInd n m k {x, y} o) = (r : ℂ) * ((r : ℂ) - 1) * (1 - ((r : ℝ) - 2) / (r : ℝ) *
  multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
  rw [slotDiagExp_sum]; have hr1 : 1 ≤ r := (by omega)
  have houter : ∀ x ∈ S \ T, slotDiagExp n m k S T K (fun o ↦ ∑ y ∈ (S \ T).erase x, validAllInd n m
    k {x, y} o) = ((r : ℂ) - 1) * (1 - ((r : ℝ) - 2) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^
    (activeSlots m k) := by
    intro x hx; rw [slotDiagExp_sum]
    have hinner : ∀ y ∈ (S \ T).erase x, slotDiagExp n m k S T K (validAllInd n m k {x, y}) = (1 -
      ((r : ℝ) - 2) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
      intro y hy; rcases Finset.mem_erase.mp hy with ⟨hyx, hyR⟩; have hsub : ({x, y} : Finset (Fin
        (2 ^ n))) ⊆ S \ T := Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hyR⟩
      have h := conj_validAllInd_zero_zero (n := n) (m := m) (k := k) hTS hsub K; dsimp only at h
      change slotDiagExp n m k S T K (validAllInd n m k {x, y}) = _ at h; rw [h, hr,
        Finset.card_pair hyx.symm, Nat.cast_sub hr2]; push_cast; rfl
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_erase_of_mem hx, hr,
      nsmul_eq_mul, Nat.cast_sub hr1, Nat.cast_one]
  rw [Finset.sum_congr rfl houter, Finset.sum_const, hr, nsmul_eq_mul, mul_assoc]
private lemma sum_ite_subset_singleton {α : Type*} [DecidableEq α] {R H : Finset α} (hHR : H ⊆ R) :
  (∑ x ∈ R, if H ⊆ {x} then (1 : ℂ) else 0) = if H.card = 0 then (R.card : ℂ) else if H.card = 1
  then 1 else 0 := by
  by_cases h0 : H.card = 0
  · have hH : H = ∅ := Finset.card_eq_zero.mp h0; subst hH; simp
  · by_cases h1 : H.card = 1
    · rw [ite_eq_right h0, ite_eq_left h1]; rcases Finset.card_eq_one.mp h1 with ⟨u, rfl⟩
      have huR : u ∈ R := Finset.singleton_subset_iff.mp hHR
      simp only [Finset.singleton_subset_iff, Finset.mem_singleton]; rw [Finset.sum_ite_eq R u (fun
        _ ↦ (1 : ℂ)), ite_eq_left huR]
    · rw [ite_eq_right h0, ite_eq_right h1]; refine Finset.sum_eq_zero fun x _ ↦ ite_eq_right (fun
        hsub ↦ ?_); have hle : H.card ≤ ({x} : Finset α).card := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle; omega
private lemma singleton_subset_pair_ite {α : Type*} [DecidableEq α] (u x y : α) (hyx : y ≠ x) : (if
  ({u} : Finset α) ⊆ {x, y} then (1 : ℂ) else 0) = (if u = x then 1 else 0) + (if u = y then 1 else
  0) := by
  simp only [Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hux : u = x
  · subst hux; simp [hyx.symm]
  · by_cases huy : u = y
    · subst huy; simp [hyx]
    · simp [hux, huy]
private lemma pair_subset_pair_ite {α : Type*} [DecidableEq α] {u v x y : α} (huv : u ≠ v) : (if
  ({u, v} : Finset α) ⊆ {x, y} then (1 : ℂ) else 0) = (if u = x then if v = y then 1 else 0 else 0)
  + (if v = x then if u = y then 1 else 0 else 0) := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Finset.mem_insert, Finset.mem_singleton]; by_cases hux : u = x
  · subst hux; have hvx : v ≠ u := huv.symm; by_cases hvy : v = y
    · subst hvy; simp [huv, hvx]
    · simp [hvx, hvy]
  · by_cases hvx : v = x
    · subst hvx; by_cases huy : u = y
      · subst huy; simp [hux, huv.symm]
      · simp [hux, huy]
    · by_cases huy : u = y
      · subst huy; simp [hux, hvx, huv.symm]
      · simp [hux, hvx, huy]
private lemma sum_ite_subset_pair {α : Type*} [DecidableEq α] {R H : Finset α} (hHR : H ⊆ R) (hr1 :
  1 ≤ R.card) : (∑ x ∈ R, ∑ y ∈ R.erase x, if H ⊆ {x, y} then (1 : ℂ) else 0) = if H.card = 0 then
  (R.card : ℂ) * ((R.card : ℂ) - 1) else if H.card = 1 then 2 * ((R.card : ℂ) - 1) else if H.card =
  2 then 2 else 0 := by
  by_cases h0 : H.card = 0
  · have hH : H = ∅ := Finset.card_eq_zero.mp h0; subst hH; simp only [Finset.card_empty,
      ↓reduceIte, Finset.empty_subset, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hterm : ∀ x ∈ R, ((R.erase x).card : ℂ) = (R.card : ℂ) - 1 :=
      (by intro x hx; rw [Finset.card_erase_of_mem hx, Nat.cast_sub hr1, Nat.cast_one])
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  · by_cases h1 : H.card = 1
    · rw [ite_eq_right h0, ite_eq_left h1]; rcases Finset.card_eq_one.mp h1 with ⟨u, rfl⟩
      have huR : u ∈ R := Finset.singleton_subset_iff.mp hHR
      have hinner : ∀ x ∈ R, (∑ y ∈ R.erase x, if ({u} : Finset α) ⊆ {x, y} then (1 : ℂ) else 0) =
        (if u = x then ((R.card : ℂ) - 1) else 1) := by
        intro x hx
        have hstep : ∀ y ∈ R.erase x, (if ({u} : Finset α) ⊆ {x, y} then (1 : ℂ) else 0) = (if u = x
          then 1 else 0) + (if u = y then 1 else 0) := fun y hy ↦ singleton_subset_pair_ite u x y
          (Finset.mem_erase.mp hy).1; rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_erase_of_mem hx, nsmul_eq_mul, Nat.cast_sub hr1,
          Nat.cast_one, Finset.sum_ite_eq (R.erase x) u (fun _ ↦ (1 : ℂ))]; by_cases hux : u = x
        · subst hux; simp
        · have hu_er : u ∈ R.erase x := Finset.mem_erase.mpr ⟨hux, huR⟩; simp [hux, hu_er]
      rw [Finset.sum_congr rfl hinner]; have hsplit : ∀ x ∈ R, (if u = x then ((R.card : ℂ) - 1)
        else (1 : ℂ)) = 1 + (if u = x then ((R.card : ℂ) - 2) else 0) :=
        (by intro x _; split_ifs <;> ring); rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_ite_eq R u (fun _ ↦ (R.card : ℂ) - 2),
        ite_eq_left huR]; ring
    · by_cases h2 : H.card = 2
      · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]; rcases Finset.card_eq_two.mp h2 with
          ⟨u, v, huv, rfl⟩; have huR : u ∈ R := hHR (Finset.mem_insert_self u {v})
        have hvR : v ∈ R := hHR (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
        have hinner : ∀ x ∈ R, (∑ y ∈ R.erase x, if ({u, v} : Finset α) ⊆ {x, y} then (1 : ℂ) else
          0) = (if u = x then (1 : ℂ) else 0) + (if v = x then 1 else 0) := by
          intro x hx; have hstep : ∀ y ∈ R.erase x, (if ({u, v} : Finset α) ⊆ {x, y} then (1 : ℂ)
            else 0) = (if u = x then if v = y then 1 else 0 else 0) + (if v = x then if u = y then 1
            else 0 else 0) := fun y _ ↦ pair_subset_pair_ite huv; rw [Finset.sum_congr rfl hstep,
            Finset.sum_add_distrib]; congr 1
          · by_cases hux : u = x
            · subst hux; have hv_er : v ∈ R.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvR⟩
              simp [Finset.sum_ite_eq (R.erase u) v (fun _ ↦ (1 : ℂ)), hv_er]
            · simp [hux]
          · by_cases hvx : v = x
            · subst hvx; have hu_er : u ∈ R.erase v := Finset.mem_erase.mpr ⟨huv, huR⟩
              simp [Finset.sum_ite_eq (R.erase v) u (fun _ ↦ (1 : ℂ)), hu_er]
            · simp [hvx]
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_ite_eq R u (fun _ ↦ (1 :
          ℂ)), Finset.sum_ite_eq R v (fun _ ↦ (1 : ℂ)), ite_eq_left huR, ite_eq_left hvR]; norm_num
      · rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2]
        refine Finset.sum_eq_zero fun x _ ↦ Finset.sum_eq_zero fun y _ ↦ ite_eq_right (fun hsub ↦
          ?_); have hle : H.card ≤ ({x, y} : Finset α).card := Finset.card_le_card hsub
        have hpair : ({x, y} : Finset α).card ≤ 2 := Finset.card_le_two; omega
private lemma ite_subset_empty {α : Type*} [DecidableEq α] (H : Finset α) : (if H ⊆ ∅ then (1 : ℂ)
  else 0) = if H.card = 0 then 1 else 0 := by by_cases h : H = ∅ <;> simp [h]
private lemma stratumExitInd_decomp_one (n m k : ℕ) (R : Finset (Fin (2 ^ n))) (o : Fin (2 ^
  findAllQubits n m k)) : stratumExitInd n m k 1 R o = validAllInd n m k R o - validAllInd n m k ∅ o
  := by
  simp only [stratumExitInd, validAllInd_eq_hitSet_subset, Finset.subset_empty]
  by_cases hsub : hitSet n m k o ⊆ R
  · by_cases h0 : hitSet n m k o = ∅
    · simp [h0]
    · have hcard : 1 ≤ (hitSet n m k o).card := Finset.Nonempty.card_pos
        (Finset.nonempty_iff_ne_empty.mpr h0); simp [hsub, h0, hcard]
  · have h0 : hitSet n m k o ≠ ∅ := fun h ↦ hsub (h ▸ Finset.empty_subset R); simp [hsub, h0]
private lemma stratumExitInd_decomp_two (n m k : ℕ) (R : Finset (Fin (2 ^ n))) (o : Fin (2 ^
  findAllQubits n m k)) : stratumExitInd n m k 2 R o = validAllInd n m k R o - (∑ x ∈ R, validAllInd
  n m k {x} o) + ((R.card : ℂ) - 1) * validAllInd n m k ∅ o := by
  simp only [stratumExitInd, validAllInd_eq_hitSet_subset]; set H := hitSet n m k o
  by_cases hHR : H ⊆ R
  · rw [ite_eq_left hHR, sum_ite_subset_singleton hHR, ite_subset_empty]
    rcases H.card with _ | _ | c
    · simp [hHR]
    · simp [hHR]
    · have h2 : 2 ≤ c + 2 := (by omega); simp [hHR, h2]
  · have hnot_ge : ¬ (H ⊆ R ∧ 2 ≤ H.card) := fun h ↦ hHR h.1
    have hnot_emp : ¬ (H ⊆ ∅) := fun h ↦ hHR (h.trans (Finset.empty_subset R)); have hsum0 : (∑ x ∈
      R, if H ⊆ {x} then (1 : ℂ) else 0) = 0 := Finset.sum_eq_zero fun x hx ↦ ite_eq_right (fun h ↦
      hHR (h.trans (Finset.singleton_subset_iff.mpr hx))); rw [ite_eq_right hnot_ge, ite_eq_right
      hHR, ite_eq_right hnot_emp, hsum0]; ring
private lemma stratumExitInd_decomp_three (n m k : ℕ) (R : Finset (Fin (2 ^ n))) (hr1 : 1 ≤ R.card)
  (o : Fin (2 ^ findAllQubits n m k)) : stratumExitInd n m k 3 R o = validAllInd n m k R o - (1 / 2
  : ℂ) * (∑ x ∈ R, ∑ y ∈ R.erase x, validAllInd n m k {x, y} o) + ((R.card : ℂ) - 2) * (∑ x ∈ R,
  validAllInd n m k {x} o) - (((R.card : ℂ) - 1) * ((R.card : ℂ) - 2) / 2) * validAllInd n m k ∅ o
  := by
  simp only [stratumExitInd, validAllInd_eq_hitSet_subset]; set H := hitSet n m k o
  by_cases hHR : H ⊆ R
  · rw [ite_eq_left hHR, sum_ite_subset_pair hHR hr1, sum_ite_subset_singleton hHR,
      ite_subset_empty]; rcases H.card with _ | _ | _ | c
    · norm_num [hHR]; ring
    · norm_num [hHR]; ring
    · simp [hHR]
    · have h3 : 3 ≤ c + 3 := (by omega); simp [hHR, h3]
  · have hnot_ge : ¬ (H ⊆ R ∧ 3 ≤ H.card) := fun h ↦ hHR h.1
    have hnot_emp : ¬ (H ⊆ ∅) := fun h ↦ hHR (h.trans (Finset.empty_subset R)); have hsum1 : (∑ x ∈
      R, if H ⊆ {x} then (1 : ℂ) else 0) = 0 := Finset.sum_eq_zero fun x hx ↦ ite_eq_right (fun h ↦
      hHR (h.trans (Finset.singleton_subset_iff.mpr hx)))
    have hsum2 : (∑ x ∈ R, ∑ y ∈ R.erase x, if H ⊆ {x, y} then (1 : ℂ) else 0) = 0 :=
      Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ ite_eq_right (fun h ↦ hHR (h.trans
      (Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr (Finset.mem_erase.mp
      hy).2⟩))); rw [ite_eq_right hnot_ge, ite_eq_right hHR, ite_eq_right hnot_emp, hsum1, hsum2];
      ring
private lemma conj_stratumExitInd_zero_zero {n m k s r : ℕ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hsr : s ≤
  r) {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) :
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    (U_all.1ᴴ * Matrix.diagonal (stratumExitInd n m k s (S \ T)) * U_all.1) 0 0 = (occupancyTail s
      (activeSlots m k) r (multiP_succ K r (2 ^ n)) : ℂ) := by
  change slotDiagExp n m k S T K (stratumExitInd n m k s (S \ T)) = _
  have hr1 : 1 ≤ r := hs1.trans hsr; rcases s with _ | _ | _ | _ | s
  · omega
  · have hfun : stratumExitInd n m k 1 (S \ T) = fun o ↦ validAllInd n m k (S \ T) o - validAllInd n
      m k ∅ o := funext (stratumExitInd_decomp_one n m k (S \ T))
    rw [hfun, slotDiagExp_sub, slotDiagExp_validAllInd_self hTS K, slotDiagExp_validAllInd_empty hr1
      hTS hr K]; simp only [occupancyTail]; push_cast; ring
  · have hfun : stratumExitInd n m k 2 (S \ T) = fun o ↦ (validAllInd n m k (S \ T) o - ∑ x ∈ S \ T,
      validAllInd n m k {x} o) + (((S \ T).card : ℂ) - 1) * validAllInd n m k ∅ o := funext
      (stratumExitInd_decomp_two n m k (S \ T)); rw [hfun, slotDiagExp_add, slotDiagExp_sub,
      slotDiagExp_const_mul, slotDiagExp_validAllInd_self hTS K, slotDiagExp_sum_singletons hr1 hTS
      hr K, slotDiagExp_validAllInd_empty hr1 hTS hr K, hr]; simp only [occupancyTail]; push_cast;
      ring
  · have hr1_card : 1 ≤ (S \ T).card := (by omega)
    have hfun : stratumExitInd n m k 3 (S \ T) = fun o ↦ ((validAllInd n m k (S \ T) o - (1 / 2 : ℂ)
      * (∑ x ∈ S \ T, ∑ y ∈ (S \ T).erase x, validAllInd n m k {x, y} o)) + (((S \ T).card : ℂ) - 2)
      * (∑ x ∈ S \ T, validAllInd n m k {x} o)) - ((((S \ T).card : ℂ) - 1) * (((S \ T).card : ℂ) -
      2) / 2) * validAllInd n m k ∅ o := funext (stratumExitInd_decomp_three n m k (S \ T) hr1_card)
    rw [hfun, slotDiagExp_sub, slotDiagExp_add, slotDiagExp_sub, slotDiagExp_const_mul,
      slotDiagExp_const_mul, slotDiagExp_const_mul, slotDiagExp_validAllInd_self hTS K,
      slotDiagExp_sum_pairs (by omega) hTS hr K, slotDiagExp_sum_singletons hr1 hTS hr K,
      slotDiagExp_validAllInd_empty hr1 hTS hr K, hr]; simp only [occupancyTail]; push_cast; ring
  · omega
theorem wp_attemptBody_occupancyStratum_eq {Var : Type} [DecidableEq Var] {n m k s r : ℕ} (hm : 1 ≤
  m) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hsw : s ≤ activeSlots m k) (hsr : s ≤ r) (hrd : r ≤ 2 ^ n) {S T :
  Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (res : Var) :
    let K := stageIterations (stagePhiReal (activeSlots m k) r) n r
    let p := occupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n))
    let body := (attemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)
    wp body (liftPureProp (fun σ ↦ ¬ stageRetryGuard n m k s res σ)) = constAssertion p ∧ ∀ (Θ :
      CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ : Store Var) (c : ℝ), 0 ≤ c → c ≤ 1 → (∀
        o : Fin
      (2 ^ findAllQubits n m k), hitSet n m k o ⊆ S \ T → if stageMissOutcome n m k s o = true then
      (Θ (Store.subst σ res (o.val : ℤ))).1 = c • 1 else (Θ (Store.subst σ res (o.val : ℤ))).1 = 1)
      → ((wp body Θ) σ).1 = (p + (1 - p) * c) • 1 :=
  wp_attemptBody_of_stratumExitInd_entry hm hs1 hs3 hsw hsr hrd hTS res
    (conj_stratumExitInd_zero_zero hs1 hs3 hsr hTS hr _)
end QuantumComputation.Specs
end
end Sec_HomomorphicCharacterBasis
section Sec_FrobeniusTriadicCascade
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal QHLExpectation ComplexOrder MatrixOrder
/-- Computably enumerate all `p`-tuples `Fin p → Fin (2 ^ n)`. -/
def enumTuples (n : ℕ) : (p : ℕ) → List (Fin p → Fin (2 ^ n))
  | 0 => [Fin.elim0]
  | p + 1 =>
      (enumTuples n p).flatMap fun xs ↦
        (List.finRange (2 ^ n)).map fun x ↦ Fin.snoc xs x
theorem mem_enumTuples (n : ℕ) {p : ℕ} (xs : Fin p → Fin (2 ^ n)) : xs ∈ enumTuples n p := by
  induction p with
  | zero => simp only [enumTuples, List.mem_singleton]; funext i; exact i.elim0
  | succ p ih =>
    simp only [enumTuples, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨Fin.init xs, ih (Fin.init xs), xs (Fin.last p), Fin.snoc_init_self xs⟩
/-- Finite `.qIf` dispatch over a list of `s`-tuples `xs: Fin s → Fin (2 ^ n)` matching
  `e σ = encodeTuple n xs`. -/
def branchOnTupleExpr {Step Var : Type} {Q w n s : ℕ} (e : Expr Var)
    (f : (Fin s → Fin (2 ^ n)) → OracleDynamicCircuit Step Var Q w) :
    List (Fin s → Fin (2 ^ n)) → OracleDynamicCircuit Step Var Q w
  | [] => .skip
  | xs :: rest =>
      .qIf (fun σ ↦ e σ = (encodeTuple n xs : ℤ))
        (f xs)
        (branchOnTupleExpr e f rest)
/-- Stage circuit branch for an already-discovered `p`-tuple `xs` and stage stride `s`:
  initializes `res` to `0`, runs the parallel batch retry `.qWhile` loop for
  `T = Finset.univ.image xs`
  and `r` remaining targets until `≥ s` distinct targets hit, and appends the `s` newly
  discovered
  targets `extractHitTupleZ n m k s (σ res)` to `xs`. -/
noncomputable def stageBranchCircuit {Var : Type} (n m k : ℕ) {p s : ℕ} (hps : p + s ≤ k)
    (r : ℕ) (xs : Fin p → Fin (2 ^ n)) (res : Var) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k))
      Var (findAllQubits n m k) ((n + 1) * activeSlots m k) :=
  let Q := findAllQubits n m k
  let T := Finset.univ.image xs
  .seq (setResCircuit n m Q res 0)
    (.seq (.qWhile (stageRetryGuard n m k s res) (attemptBody n m k r T res))
      (branchOnTupleExpr (fun σ ↦ (encodeTuple n (extractHitTupleZ n m k s (σ res)) : ℤ))
        (fun ys : Fin s → Fin (2 ^ n) ↦
          setResCircuit n m Q res (encodeTupleFin n m k hps (appendTuple xs ys)))
        (enumTuples n s)))
/-- Full circuit for a stage starting at tuple length `p` with `r = k - p` remaining targets
  and stride `s = stageStride (activeSlots m k) r`. -/
noncomputable def stageStratumCircuit {Var : Type} (n m k p r s : ℕ) (res : Var) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k))
      Var (findAllQubits n m k) ((n + 1) * activeSlots m k) :=
  if hps : p + s ≤ k then
    branchOnTupleExpr (fun σ ↦ σ res)
      (fun xs ↦ stageBranchCircuit n m k hps r xs res)
      (enumTuples n p)
  else
    .skip
/-- Stage invariant predicate: `σ res` encodes an injective `p`-tuple whose image
  is a subset of `S`. -/
def ValidStageStore {Var : Type} (n : ℕ) (S : Finset (Fin (2 ^ n))) (p : ℕ)
    (res : Var) (σ : Store Var) : Prop :=
  ∃ xs : Fin p → Fin (2 ^ n),
    Function.Injective xs ∧ Finset.univ.image xs ⊆ S ∧ σ res = (encodeTuple n xs : ℤ)
end QuantumComputation.Specs
end
end Sec_FrobeniusTriadicCascade
section Sec_MarkovTailQuarticBounds
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped NNReal NNRat
/-- Polynomial Markov recurrence for the occupancy tail `occupancyTail s w r p`
  (`s ∈ {1, 2, 3}`). -/
theorem occupancyTail_markov_succ {s w r : ℕ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hr1 : 1 ≤ r) (p : ℝ) :
    let α : ℝ := ((r : ℝ) - (s : ℝ) + 1) / (r : ℝ)
    occupancyTail s (w + 1) r p = (1 - α * p) * occupancyTail s w r p + α * p * occupancyTail (s -
      1) w r p := by
  intro α; have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hr1))
  rcases s with _ | _ | _ | _ | s
  · omega
  · simp only [occupancyTail, Nat.add_sub_cancel, α]; rw [pow_succ]; field_simp [hr_ne]; ring
  · simp only [occupancyTail, Nat.add_sub_cancel, α]; rw [pow_succ, pow_succ]; field_simp [hr_ne];
      ring
  · simp only [occupancyTail, Nat.add_sub_cancel, α]; rw [pow_succ, pow_succ, pow_succ]
    field_simp [hr_ne]; ring
  · omega
private lemma second_diff_pow_nonneg {a δ : ℝ} (haδ : 0 ≤ a - δ) (hδ : 0 ≤ δ) (w : ℕ) : 0 ≤ (a + δ)
  ^ w - 2 * a ^ w + (a - δ) ^ w := by
  have ha : 0 ≤ a := (by linarith)
  induction w with
  | zero => rw [pow_zero, pow_zero, pow_zero]; linarith
  | succ w ih =>
    have hpow : (a - δ) ^ w ≤ (a + δ) ^ w := pow_le_pow_left₀ haδ (by linarith) w; have hid : (a +
      δ) ^ (w + 1) - 2 * a ^ (w + 1) + (a - δ) ^ (w + 1) = a * ((a + δ) ^ w - 2 * a ^ w + (a - δ) ^
      w) + δ * ((a + δ) ^ w - (a - δ) ^ w) := (by ring); rw [hid]; nlinarith
private lemma occupancyTail_le_pred {s w r : ℕ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hsr : s ≤ r) {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : occupancyTail s w r p ≤ occupancyTail (s - 1) w r p := by
  have hr1 : 1 ≤ r := le_trans hs1 hsr; have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
  have hr_ne : (r : ℝ) ≠ 0 := hr_pos.ne'; rcases s with _ | _ | _ | _ | s
  · omega
  · simp only [occupancyTail]; have hpow : 0 ≤ (1 - p) ^ w := pow_nonneg (by linarith) w; linarith
  · simp only [occupancyTail]; have hr_ge : (1 : ℝ) ≤ r := (by exact_mod_cast hr1)
    have hfrac_le : ((r : ℝ) - 1) / (r : ℝ) ≤ 1 := (div_le_one hr_pos).2 (by linarith)
    have hmul_le : ((r : ℝ) - 1) / (r : ℝ) * p ≤ p := mul_le_of_le_one_left hp0 hfrac_le
    have hpow : (1 - p) ^ w ≤ (1 - ((r : ℝ) - 1) / (r : ℝ) * p) ^ w := pow_le_pow_left₀
      (by linarith) (by linarith) w; nlinarith
  · simp only [occupancyTail]; let a : ℝ := 1 - ((r : ℝ) - 1) / (r : ℝ) * p
    let δ : ℝ := p / (r : ℝ)
    have ha_plus : 1 - ((r : ℝ) - 2) / (r : ℝ) * p = a + δ :=
      (by dsimp [a, δ]; field_simp [hr_ne]; ring); have ha_minus : 1 - p = a - δ :=
      (by dsimp [a, δ]; field_simp [hr_ne]; ring); rw [ha_plus, ha_minus]; have h_a_eq : 1 - ((r :
      ℝ) - 1) / (r : ℝ) * p = a := rfl; rw [h_a_eq]; have hr3 : (3 : ℝ) ≤ r :=
      (by exact_mod_cast hsr); have hcoeff : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) / 2 := (by nlinarith)
    have haδ : 0 ≤ a - δ := (by rw [← ha_minus]; linarith)
    have hδ : 0 ≤ δ := div_nonneg hp0 hr_pos.le; have hsec := second_diff_pow_nonneg haδ hδ w
    have hid : (1 - (r : ℝ) * a ^ w + ((r : ℝ) - 1) * (a - δ) ^ w) - (1 - (r : ℝ) * ((r : ℝ) - 1) /
      2 * (a + δ) ^ w + (r : ℝ) * ((r : ℝ) - 2) * a ^ w - ((r : ℝ) - 1) * ((r : ℝ) - 2) / 2 * (a -
      δ) ^ w) = ((r : ℝ) * ((r : ℝ) - 1) / 2) * ((a + δ) ^ w - 2 * a ^ w + (a - δ) ^ w) := (by ring)
    nlinarith
  · omega
private lemma occupancyTail_zero_w_m44 {s r : ℕ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (p : ℝ) : occupancyTail
  s 0 r p = 0 := by
  rcases s with _ | _ | _ | _ | s <;> try omega
  · simp [occupancyTail]
  · simp [occupancyTail]
  · simp only [occupancyTail, pow_zero]; ring
private lemma occupancyTail_nonneg_and_le_one_m44 {s w r : ℕ} (hs3 : s ≤ 3) (hsr : s ≤ r) {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ occupancyTail s w r p ∧ occupancyTail s w r p ≤ 1 := by
  induction w generalizing s with
  | zero =>
    rcases eq_zero_or_pos s with rfl | hs1
    · simp [occupancyTail]
    · rw [occupancyTail_zero_w_m44 hs1 hs3 p]; exact ⟨le_rfl, zero_le_one⟩
  | succ w ih =>
    rcases eq_zero_or_pos s with rfl | hs1
    · simp [occupancyTail]
    · have hr1 : 1 ≤ r := le_trans hs1 hsr; have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
      have hs_le_r : (s : ℝ) ≤ r := (by exact_mod_cast hsr); have hs_ge_1 : (1 : ℝ) ≤ s :=
        (by exact_mod_cast hs1)
      let α : ℝ := ((r : ℝ) - (s : ℝ) + 1) / (r : ℝ)
      have h_α_eq : ((r : ℝ) - (s : ℝ) + 1) / (r : ℝ) = α := rfl
      have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le; have hα1 : α ≤ 1 := (div_le_one
        hr_pos).2 (by linarith)
      have hαp0 : 0 ≤ α * p := mul_nonneg hα0 hp0; have hαp1 : α * p ≤ 1 := (by nlinarith)
      rcases ih hs3 hsr with ⟨h_s0, h_s1⟩
      rcases ih (by omega : s - 1 ≤ 3) (by omega : s - 1 ≤ r) with ⟨h_p0, h_p1⟩; have hmarkov :=
        occupancyTail_markov_succ (w := w) hs1 hs3 hr1 p; dsimp only at hmarkov
      rw [h_α_eq] at hmarkov; rw [hmarkov]; constructor <;> nlinarith
private lemma occupancyTail_pos_m44 {s w r : ℕ} (hs3 : s ≤ 3) (hsw : s ≤ w) (hsr : s ≤ r) {p : ℝ}
  (hp0 : 0 < p) (hp1 : p ≤ 1) : 0 < occupancyTail s w r p := by
  induction w generalizing s with
  | zero => have hs0 : s = 0 := (by omega); subst hs0; simp [occupancyTail]
  | succ w ih =>
    rcases eq_zero_or_pos s with rfl | hs1
    · simp [occupancyTail]
    · have hr1 : 1 ≤ r := le_trans hs1 hsr; have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
      have hs_le_r : (s : ℝ) ≤ r := (by exact_mod_cast hsr); have hs_ge_1 : (1 : ℝ) ≤ s :=
        (by exact_mod_cast hs1)
      let α : ℝ := ((r : ℝ) - (s : ℝ) + 1) / (r : ℝ)
      have h_α_eq : ((r : ℝ) - (s : ℝ) + 1) / (r : ℝ) = α := rfl
      have hα0 : 0 < α := div_pos (by linarith) hr_pos
      have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
      have hαp0 : 0 < α * p := mul_pos hα0 hp0; have hαp1 : α * p ≤ 1 := (by nlinarith)
      have h_s0 := (occupancyTail_nonneg_and_le_one_m44 (w := w) hs3 hsr hp0.le hp1).1
      have h_p_pos := ih (by omega : s - 1 ≤ 3) (by omega : s - 1 ≤ w) (by omega : s - 1 ≤ r)
      have hmarkov := occupancyTail_markov_succ (w := w) hs1 hs3 hr1 p; dsimp only at hmarkov
      rw [h_α_eq] at hmarkov; rw [hmarkov]; nlinarith
private lemma occupancyTail_mono {s w r : ℕ} (hs3 : s ≤ 3) (hsr : s ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 ≤ p₁)
  (hp12 : p₁ ≤ p₂) (hp2 : p₂ ≤ 1) : occupancyTail s w r p₁ ≤ occupancyTail s w r p₂ := by
  induction w generalizing s with
  | zero =>
    rcases eq_zero_or_pos s with rfl | hs1
    · simp [occupancyTail]
    · rw [occupancyTail_zero_w_m44 hs1 hs3 p₁, occupancyTail_zero_w_m44 hs1 hs3 p₂]
  | succ w ih =>
    rcases eq_zero_or_pos s with rfl | hs1
    · simp [occupancyTail]
    · have hr1 : 1 ≤ r := le_trans hs1 hsr; have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
      have hs_le_r : (s : ℝ) ≤ r := (by exact_mod_cast hsr); have hs_ge_1 : (1 : ℝ) ≤ s :=
        (by exact_mod_cast hs1)
      let α : ℝ := ((r : ℝ) - (s : ℝ) + 1) / (r : ℝ)
      have h_α_eq : ((r : ℝ) - (s : ℝ) + 1) / (r : ℝ) = α := rfl
      have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le; have hα1 : α ≤ 1 := (div_le_one
        hr_pos).2 (by linarith); have hp2_0 : 0 ≤ p₂ := hp1.trans hp12; have hαp2_0 : 0 ≤ α * p₂ :=
        mul_nonneg hα0 hp2_0; have hαp2_1 : α * p₂ ≤ 1 := (by nlinarith); have ih_s := ih hs3 hsr
      have ih_pred := ih (by omega : s - 1 ≤ 3) (by omega : s - 1 ≤ r); have hle_pred :=
        occupancyTail_le_pred (w := w) hs1 hs3 hsr hp1 (hp12.trans hp2); have hm1 :=
        occupancyTail_markov_succ (w := w) hs1 hs3 hr1 p₁; have hm2 := occupancyTail_markov_succ (w
        := w) hs1 hs3 hr1 p₂; dsimp only at hm1 hm2; rw [h_α_eq] at hm1 hm2; rw [hm1, hm2]
      have hid : ((1 - α * p₂) * occupancyTail s w r p₂ + α * p₂ * occupancyTail (s - 1) w r p₂) -
        ((1 - α * p₁) * occupancyTail s w r p₁ + α * p₁ * occupancyTail (s - 1) w r p₁) = (1 - α *
        p₂) * (occupancyTail s w r p₂ - occupancyTail s w r p₁) + α * p₂ * (occupancyTail (s - 1) w
        r p₂ - occupancyTail (s - 1) w r p₁) + α * (p₂ - p₁) * (occupancyTail (s - 1) w r p₁ -
        occupancyTail s w r p₁) := (by ring); have ht1 : 0 ≤ (1 - α * p₂) * (occupancyTail s w r p₂
        - occupancyTail s w r p₁) := mul_nonneg (by linarith) (by linarith)
      have ht2 : 0 ≤ α * p₂ * (occupancyTail (s - 1) w r p₂ - occupancyTail (s - 1) w r p₁) :=
        mul_nonneg hαp2_0 (by linarith); have ht3 : 0 ≤ α * (p₂ - p₁) * (occupancyTail (s - 1) w r
        p₁ - occupancyTail s w r p₁) := mul_nonneg (mul_nonneg hα0 (by linarith)) (by linarith)
      linarith
theorem occupancyTail_pos_and_mono {s w r : ℕ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (hsw : s ≤ w) (hsr : s ≤
  r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤ p₂) (hp2 : p₂ ≤ 1) : 0 < occupancyTail s w r p₁ ∧
  occupancyTail s w r p₁ ≤ occupancyTail s w r p₂ ∧ occupancyTail s w r p₂ ≤ 1 := by
  have _ := hs1; exact ⟨occupancyTail_pos_m44 hs3 hsw hsr hp1 (hp12.trans hp2), occupancyTail_mono
    hs3 hsr hp1.le hp12 hp2, (occupancyTail_nonneg_and_le_one_m44 hs3 hsr (hp1.le.trans hp12)
    hp2).2⟩
end QuantumComputation.Specs
end
end Sec_MarkovTailQuarticBounds
section Sec_PowersetCardCharacter
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
/-- Rank-`j` Boolean-lattice symmetric character observable on unfound target set `R`:
  sums `validAllInd n m k A o` over all `j`-element subsets `A ∈ R.powersetCard j`. -/
def subsetCardSumInd (n m k j : ℕ) (R : Finset (Fin (2 ^ n)))
    (o : Fin (2 ^ findAllQubits n m k)) : ℂ :=
  ∑ A ∈ R.powersetCard j, validAllInd n m k A o
/-- Unconditional complex polynomial identity for `Nat.choose m 2`. -/
theorem choose_two_cast_complex (m : ℕ) :
    (Nat.choose m 2 : ℂ) = (m : ℂ) * ((m : ℂ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.choose_succ_succ m 1, Nat.choose_one_right]
      push_cast; rw [ih]; ring
/-- Unconditional complex polynomial identity for `Nat.choose m 3`. -/
theorem choose_three_cast_complex (m : ℕ) :
    (Nat.choose m 3 : ℂ) = (m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ) - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.choose_succ_succ m 2]
      push_cast; rw [choose_two_cast_complex m, ih]; ring
private lemma card_filter_powersetCard_subset {α : Type*} [DecidableEq α]
    {R H : Finset α} (hHR : H ⊆ R) (j : ℕ) :
    ((R.powersetCard j).filter (fun A ↦ H ⊆ A)).card =
      if H.card ≤ j then Nat.choose (R.card - H.card) (j - H.card) else 0 := by
  split_ifs with hj
  · have hbij :
        ((R.powersetCard j).filter (fun A ↦ H ⊆ A)).card =
          ((R \ H).powersetCard (j - H.card)).card := by
      refine Finset.card_bij (fun A _ ↦ A \ H) ?_ ?_ ?_
      · intro A hA
        rw [Finset.mem_filter, Finset.mem_powersetCard] at hA
        rcases hA with ⟨⟨hAR, hAcard⟩, hHA⟩
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Finset.mem_sdiff] at hx ⊢
          exact ⟨hAR hx.1, hx.2⟩
        · rw [Finset.card_sdiff_of_subset hHA, hAcard]
      · intro A₁ hA₁ A₂ hA₂ h_eq
        rw [Finset.mem_filter] at hA₁ hA₂
        rw [← Finset.sdiff_union_of_subset hA₁.2,
          ← Finset.sdiff_union_of_subset hA₂.2, h_eq]
      · intro B hB
        rw [Finset.mem_powersetCard] at hB
        rcases hB with ⟨hBRH, hBcard⟩
        have hdisj : Disjoint B H := by
          rw [Finset.disjoint_left]; intro x hxB hxH
          exact (Finset.mem_sdiff.mp (hBRH hxB)).2 hxH
        have hsdiff : (B ∪ H) \ H = B := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hx | hx, hnx⟩
            · exact hx
            · exact (hnx hx).elim
          · intro hx
            exact ⟨Or.inl hx, (Finset.mem_sdiff.mp (hBRH hx)).2⟩
        refine ⟨B ∪ H, ?_, hsdiff⟩
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, ?_⟩, Finset.subset_union_right⟩
        · intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (Finset.mem_sdiff.mp (hBRH hx)).1
          · exact hHR hx
        · rw [Finset.card_union_of_disjoint hdisj, hBcard, Nat.sub_add_cancel hj]
    rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset hHR]
  · refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
    intro A hA hHA
    rw [Finset.mem_powersetCard] at hA
    have hle := Finset.card_le_card hHA
    omega
/-- Pointwise evaluation of `subsetCardSumInd` on any supported outcome `hitSet n m k o ⊆
  R`. -/
theorem subsetCardSumInd_of_subset {n m k j : ℕ} {R : Finset (Fin (2 ^ n))}
    {o : Fin (2 ^ findAllQubits n m k)} (hHR : hitSet n m k o ⊆ R) :
    subsetCardSumInd n m k j R o =
      if (hitSet n m k o).card ≤ j then
        (Nat.choose (R.card - (hitSet n m k o).card) (j - (hitSet n m k o).card) : ℂ)
      else 0 := by
  unfold subsetCardSumInd; simp_rw [validAllInd_eq_hitSet_subset]
  rw [Finset.sum_boole, card_filter_powersetCard_subset hHR j]
  split_ifs <;> simp
/-- Pointwise evaluation of `subsetCardSumInd` outside `R` (`¬ hitSet n m k o ⊆ R`). -/
theorem subsetCardSumInd_of_not_subset {n m k j : ℕ} {R : Finset (Fin (2 ^ n))}
    {o : Fin (2 ^ findAllQubits n m k)} (hnot : ¬ hitSet n m k o ⊆ R) :
    subsetCardSumInd n m k j R o = 0 := by
  unfold subsetCardSumInd; simp_rw [validAllInd_eq_hitSet_subset]
  refine Finset.sum_eq_zero fun A hA ↦ ite_eq_right (fun hsub ↦ ?_)
  exact hnot (hsub.trans (Finset.mem_powersetCard.mp hA).1)
theorem quartic_stratumExitInd_decomp_one (n m k : ℕ) (R : Finset (Fin (2 ^ n)))
    (o : Fin (2 ^ findAllQubits n m k)) :
    stratumExitInd n m k 1 R o =
      validAllInd n m k R o - subsetCardSumInd n m k 0 R o := by
  by_cases hHR : hitSet n m k o ⊆ R
  · rw [subsetCardSumInd_of_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, true_and]
    rcases (hitSet n m k o).card with _ | c
    · simp
    · have h1 : 1 ≤ c + 1 := by omega
      have hn0 : ¬ (c + 1 ≤ 0) := by omega
      simp [h1, hn0]
  · rw [subsetCardSumInd_of_not_subset hHR]
    simp [stratumExitInd, validAllInd_eq_hitSet_subset, hHR]
theorem quartic_stratumExitInd_decomp_two (n m k : ℕ) (R : Finset (Fin (2 ^ n)))
    (o : Fin (2 ^ findAllQubits n m k)) :
    stratumExitInd n m k 2 R o =
      validAllInd n m k R o - subsetCardSumInd n m k 1 R o +
        ((R.card : ℂ) - 1) * subsetCardSumInd n m k 0 R o := by
  by_cases hHR : hitSet n m k o ⊆ R
  · rw [subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, true_and]
    rcases (hitSet n m k o).card with _ | _ | c
    · simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero,
        show ¬ (2 ≤ 0) by omega, Nat.choose_zero_right, Nat.cast_one,
        Nat.choose_one_right]
      ring
    · simp only [show 1 ≤ 1 by omega, show ¬ (1 ≤ 0) by omega,
        show ¬ (2 ≤ 1) by omega, ↓reduceIte, Nat.sub_self,
        Nat.choose_zero_right, Nat.cast_one]
      ring
    · have h2 : 2 ≤ c + 2 := by omega
      have hn1 : ¬ (c + 2 ≤ 1) := by omega
      have hn0 : ¬ (c + 2 ≤ 0) := by omega
      simp only [h2, hn1, hn0, ↓reduceIte]
      ring
  · rw [subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, false_and, ↓reduceIte]
    ring
theorem quartic_stratumExitInd_decomp_three (n m k : ℕ) (R : Finset (Fin (2 ^ n)))
    (o : Fin (2 ^ findAllQubits n m k)) :
    stratumExitInd n m k 3 R o =
      validAllInd n m k R o - subsetCardSumInd n m k 2 R o +
        ((R.card : ℂ) - 2) * subsetCardSumInd n m k 1 R o -
        (((R.card : ℂ) - 1) * ((R.card : ℂ) - 2) / 2) * subsetCardSumInd n m k 0 R o := by
  by_cases hHR : hitSet n m k o ⊆ R
  · rw [subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR,
      subsetCardSumInd_of_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, true_and]
    have hle : (hitSet n m k o).card ≤ R.card := Finset.card_le_card hHR
    generalize (hitSet n m k o).card = h at hle ⊢
    rcases h with _ | _ | _ | c
    · simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero,
        show ¬ (3 ≤ 0) by omega, Nat.choose_zero_right, Nat.cast_one,
        Nat.choose_one_right, choose_two_cast_complex]
      ring
    · simp only [show 1 ≤ 2 by omega, show 1 ≤ 1 by omega, show ¬ (1 ≤ 0) by omega,
        show ¬ (3 ≤ 1) by omega, ↓reduceIte, Nat.sub_self,
        Nat.choose_zero_right, Nat.cast_one]
      rw [show 2 - 1 = 1 from rfl, Nat.choose_one_right, Nat.cast_sub hle, Nat.cast_one]
      ring
    · simp only [show 2 ≤ 2 by omega, show ¬ (2 ≤ 1) by omega, show ¬ (2 ≤ 0) by omega,
        show ¬ (3 ≤ 2) by omega, ↓reduceIte, Nat.sub_self,
        Nat.choose_zero_right, Nat.cast_one]
      ring
    · have h3 : 3 ≤ c + 3 := by omega
      have hn2 : ¬ (c + 3 ≤ 2) := by omega
      have hn1 : ¬ (c + 3 ≤ 1) := by omega
      have hn0 : ¬ (c + 3 ≤ 0) := by omega
      simp only [h3, hn2, hn1, hn0, ↓reduceIte]
      ring
  · rw [subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, false_and, ↓reduceIte]
    ring
/-- Exact fourth-order Boolean-lattice Mobius decomposition of `stratumExitInd n m k 4 R`. -/
theorem stratumExitInd_decomp_four (n m k : ℕ) (R : Finset (Fin (2 ^ n)))
    (o : Fin (2 ^ findAllQubits n m k)) :
    stratumExitInd n m k 4 R o =
      validAllInd n m k R o -
        subsetCardSumInd n m k 3 R o +
        ((R.card : ℂ) - 3) * subsetCardSumInd n m k 2 R o -
        (((R.card : ℂ) - 2) * ((R.card : ℂ) - 3) / 2) * subsetCardSumInd n m k 1 R o +
        (((R.card : ℂ) - 1) * ((R.card : ℂ) - 2) * ((R.card : ℂ) - 3) / 6) *
          subsetCardSumInd n m k 0 R o := by
  by_cases hHR : hitSet n m k o ⊆ R
  · rw [subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR,
      subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, true_and]
    have hle : (hitSet n m k o).card ≤ R.card := Finset.card_le_card hHR
    generalize (hitSet n m k o).card = h at hle ⊢
    rcases h with _ | _ | _ | _ | c
    · simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero,
        show ¬ (4 ≤ 0) by omega, Nat.choose_zero_right, Nat.cast_one,
        Nat.choose_one_right, choose_two_cast_complex, choose_three_cast_complex]
      ring
    · simp only [show 1 ≤ 3 by omega, show 1 ≤ 2 by omega, show 1 ≤ 1 by omega,
        show ¬ (1 ≤ 0) by omega, show ¬ (4 ≤ 1) by omega, ↓reduceIte,
        Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 3 - 1 = 2 from rfl, show 2 - 1 = 1 from rfl,
        choose_two_cast_complex, Nat.choose_one_right, Nat.cast_sub hle, Nat.cast_one]
      ring
    · simp only [show 2 ≤ 3 by omega, show 2 ≤ 2 by omega, show ¬ (2 ≤ 1) by omega,
        show ¬ (2 ≤ 0) by omega, show ¬ (4 ≤ 2) by omega, ↓reduceIte,
        Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 3 - 2 = 1 from rfl, Nat.choose_one_right, Nat.cast_sub hle]
      push_cast; ring
    · simp only [show 3 ≤ 3 by omega, show ¬ (3 ≤ 2) by omega, show ¬ (3 ≤ 1) by omega,
        show ¬ (3 ≤ 0) by omega, show ¬ (4 ≤ 3) by omega, ↓reduceIte,
        Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      ring
    · have h4 : 4 ≤ c + 4 := by omega
      have hn3 : ¬ (c + 4 ≤ 3) := by omega
      have hn2 : ¬ (c + 4 ≤ 2) := by omega
      have hn1 : ¬ (c + 4 ≤ 1) := by omega
      have hn0 : ¬ (c + 4 ≤ 0) := by omega
      simp only [h4, hn3, hn2, hn1, hn0, ↓reduceIte]
      ring
  · rw [subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, false_and, ↓reduceIte]
    ring
noncomputable def quarticSlotDiagExp (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ)
    (d : Fin (2 ^ findAllQubits n m k) → ℂ) : ℂ :=
  let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
  (U_all.1ᴴ * Matrix.diagonal d * U_all.1) 0 0
lemma quarticSlotDiagExp_add (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ)
    (d₁ d₂ : Fin (2 ^ findAllQubits n m k) → ℂ) :
    quarticSlotDiagExp n m k S T K (fun o ↦ d₁ o + d₂ o) =
      quarticSlotDiagExp n m k S T K d₁ + quarticSlotDiagExp n m k S T K d₂ := by
  let M := (embedAllSlots n m k (singleSlotAttemptUnitary S T K)).1
  have h : Mᴴ * Matrix.diagonal (fun o ↦ d₁ o + d₂ o) * M =
      Mᴴ * Matrix.diagonal d₁ * M + Mᴴ * Matrix.diagonal d₂ * M := by
    rw [← Matrix.diagonal_add, mul_add, add_mul]
  exact congrFun (congrFun h 0) 0
lemma quarticSlotDiagExp_sub (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ)
    (d₁ d₂ : Fin (2 ^ findAllQubits n m k) → ℂ) :
    quarticSlotDiagExp n m k S T K (fun o ↦ d₁ o - d₂ o) =
      quarticSlotDiagExp n m k S T K d₁ - quarticSlotDiagExp n m k S T K d₂ := by
  let M := (embedAllSlots n m k (singleSlotAttemptUnitary S T K)).1
  have h : Mᴴ * Matrix.diagonal (fun o ↦ d₁ o - d₂ o) * M =
      Mᴴ * Matrix.diagonal d₁ * M - Mᴴ * Matrix.diagonal d₂ * M := by
    rw [← Matrix.diagonal_sub, mul_sub, sub_mul]
  exact congrFun (congrFun h 0) 0
lemma quarticSlotDiagExp_const_mul (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ)
    (c : ℂ) (d : Fin (2 ^ findAllQubits n m k) → ℂ) :
    quarticSlotDiagExp n m k S T K (fun o ↦ c * d o) =
      c * quarticSlotDiagExp n m k S T K d := by
  let M := (embedAllSlots n m k (singleSlotAttemptUnitary S T K)).1
  have h : Mᴴ * Matrix.diagonal (c • d) * M =
      c • (Mᴴ * Matrix.diagonal d * M) := by
    rw [Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  exact congrFun (congrFun h 0) 0
lemma quarticSlotDiagExp_sum {α : Type*}
    (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ)
    (B : Finset α) (f : α → Fin (2 ^ findAllQubits n m k) → ℂ) :
    quarticSlotDiagExp n m k S T K (fun o ↦ ∑ x ∈ B, f x o) =
      ∑ x ∈ B, quarticSlotDiagExp n m k S T K (f x) := by
  induction B using Finset.cons_induction with
  | empty =>
      simp only [Finset.sum_empty]
      let M := (embedAllSlots n m k (singleSlotAttemptUnitary S T K)).1
      have h : Mᴴ * Matrix.diagonal (fun _ : Fin (2 ^ findAllQubits n m k) ↦ (0 : ℂ)) * M = 0 := by
        rw [Matrix.diagonal_zero, mul_zero, zero_mul]
      exact congrFun (congrFun h 0) 0
  | cons a B ha ih =>
      simp_rw [Finset.sum_cons]; rw [quarticSlotDiagExp_add, ih]
/-- Exact `w`-slot expectation of the rank-`j` symmetric character observable
  `subsetCardSumInd`. -/
theorem slotDiagExp_subsetCardSumInd {n m k r j : ℕ} (hjr : j ≤ r)
    {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) :
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    (U_all.1ᴴ * Matrix.diagonal (subsetCardSumInd n m k j (S \ T)) * U_all.1) 0 0 =
      (Nat.choose r j : ℂ) *
        (1 - ((r : ℝ) - (j : ℝ)) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
  change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k j (S \ T)) = _
  unfold subsetCardSumInd
  rw [quarticSlotDiagExp_sum]
  have hterm : ∀ A ∈ (S \ T).powersetCard j,
      quarticSlotDiagExp n m k S T K (validAllInd n m k A) =
        (1 - ((r : ℝ) - (j : ℝ)) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
    intro A hA
    rcases Finset.mem_powersetCard.mp hA with ⟨hAR, hAcard⟩
    have h := conj_validAllInd_zero_zero (n := n) (m := m) (k := k) hTS hAR K
    dsimp only at h
    change quarticSlotDiagExp n m k S T K (validAllInd n m k A) = _ at h
    rw [h, hr, hAcard, Nat.cast_sub hjr]
    push_cast; rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, hr, nsmul_eq_mul]
end QuantumComputation.Specs
end
end Sec_PowersetCardCharacter
section Sec_ThreeHorizonZenoCascade
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs Operator ResourceCounting Real
open QuantumComputation.Specs
open scoped Matrix NNReal ENNReal NNRat QHLExpectation ComplexOrder MatrixOrder
/-- Commit `s` newly discovered targets `extractHitTupleZ n m k s (σ res)` to an existing
  `p`-tuple `xs` in classical register `res` with `0` oracle cost. -/
noncomputable def commitHitTuple {Var : Type} (n m k : ℕ) {p s : ℕ} (hps : p + s ≤ k) (xs : Fin p →
    Fin (2 ^ n)) (res : Var) : OracleDynamicCircuit (Unitary (2 ^
    QuantumComputation.Specs.findAllQubits n m k)) Var (QuantumComputation.Specs.findAllQubits n m
    k) ((n + 1) * activeSlots m k) := branchOnTupleExpr (fun σ ↦ (encodeTuple n (extractHitTupleZ n
    m k s (σ res)) : ℤ)) (fun ys : Fin s → Fin (2 ^ n) ↦ setResCircuit n m
    (QuantumComputation.Specs.findAllQubits n m k) res (encodeTupleFin n m k hps (appendTuple xs
    ys))) (enumTuples n s)
lemma wp_compile_branchOnTupleExpr_m20 {Step Var : Type} [DecidableEq Var] {Q w n s : ℕ}
    (compileStep : Step → QProg Var (2 ^ Q)) (oracle : Unitary (2 ^ w)) (e : Expr Var) (f : (Fin s →
    Fin (2 ^ n)) → OracleDynamicCircuit Step Var Q w) (l : List (Fin s → Fin (2 ^ n))) (xs : Fin s →
    Fin (2 ^ n)) (hxs : xs ∈ l) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (he : e σ =
    (encodeTuple n xs : ℤ)) : wp ((branchOnTupleExpr e f l).compile compileStep oracle) Θ σ = wp ((f
    xs).compile compileStep oracle) Θ σ := by
  induction l with
  | nil => cases hxs
  | cons hd tl ih =>
      simp only [branchOnTupleExpr, OracleDynamicCircuit.compile, wp_qIf]
      by_cases hhd : xs = hd
      · subst hhd; simp [he]
      · have hne : e σ ≠ (encodeTuple n hd : ℤ) := fun h ↦
          hhd (encodeTuple_injective n (Int.ofNat.inj (he.symm.trans h)))
        simp only [hne, ↓reduceIte]; exact ih (List.mem_of_ne_of_mem hhd hxs)
private lemma splitBasisEquiv_zero_m20 (n : ℕ) : splitBasisEquiv n 1 (0 : Fin (2 ^ (n + 1))) = (0,
    0) := by apply finProdFinEquiv.injective; ext; simp [splitBasisEquiv, finProdFinEquiv]
private lemma hitSet_zero_m20 (n m k : ℕ) : hitSet n m k (0 : Fin (2 ^
    QuantumComputation.Specs.findAllQubits n m k)) = ∅ := by
  unfold hitSet; rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]; intro j _
  rw [slotOutcome, QuantumComputation.Specs.extractIndex_zero, splitBasisEquiv_zero_m20]; simp
lemma stageRetryGuard_subst_zero_m20 {Var : Type} [DecidableEq Var] (n m k s : ℕ) (hs1 : 1 ≤ s) (res
    : Var) (σ : Store Var) : QuantumComputation.Specs.stageRetryGuard n m k s res (Store.subst σ res
    0) := by
  have h0 : stageMissOutcome n m k s (0 : Fin (2 ^ QuantumComputation.Specs.findAllQubits n m k)) =
      true := by rw [stageMissOutcome, hitSet_zero_m20, Finset.card_empty, decide_eq_true_eq]; omega
  have hz : stageMissZ n m k s 0 = true := by
    unfold stageMissZ; rw [dite_eq_left le_rfl, dite_eq_left (by positivity)]; exact h0
  simp [QuantumComputation.Specs.stageRetryGuard, hz]
lemma stageMissZ_of_fin_m20 (n m k s : ℕ) (o : Fin (2 ^ QuantumComputation.Specs.findAllQubits n m
    k)) : stageMissZ n m k s (o.val : ℤ) = stageMissOutcome n m k s o := by
  unfold stageMissZ; rw [dite_eq_left (Int.natCast_nonneg o.val), dite_eq_left (by simp)]
  exact congrArg (stageMissOutcome n m k s) (Fin.ext (Int.toNat_natCast o.val))
lemma extractHitTupleZ_of_fin_m20 (n m k s : ℕ) (o : Fin (2 ^ QuantumComputation.Specs.findAllQubits
    n m k)) : extractHitTupleZ n m k s (o.val : ℤ) = extractHitTuple n m k s o := by
  unfold extractHitTupleZ; rw [dite_eq_left (Int.natCast_nonneg o.val), dite_eq_left (by simp)]
  exact congrArg (extractHitTuple n m k s) (Fin.ext (Int.toNat_natCast o.val))
def ValidHitExit_m20 {Var : Type} (n m k s : ℕ) (R : Finset (Fin (2 ^ n))) (res : Var) (τ : Store
    Var) : Prop := Function.Injective (extractHitTupleZ n m k s (τ res)) ∧ ∀ i : Fin s,
    extractHitTupleZ n m k s (τ res) i ∈ R
lemma wp_commitHitTuple {Var : Type} [DecidableEq Var] {n m k p s : ℕ} (hps : p + s ≤ k)
    {S : Finset (Fin (2 ^ n))} {xs : Fin p → Fin (2 ^ n)} (hxs_inj : Function.Injective xs) (hxs_sub
    : Finset.univ.image xs ⊆ S) (res : Var) (τ : Store Var) (h_hit : ValidHitExit_m20 n m k s (S \
    Finset.univ.image xs) res τ) : wp ((commitHitTuple n m k hps xs res).compile QProg.qAssign
    (groverParallelMarkingOracle (activeSlots m k) S)) (liftPureProp (ValidStageStore n S (p + s)
    res)) τ = 1 := by
  unfold commitHitTuple; let ys := extractHitTupleZ n m k s (τ res)
  rw [wp_compile_branchOnTupleExpr_m20 QProg.qAssign (groverParallelMarkingOracle (activeSlots m k)
    S) _ _ _ ys (mem_enumTuples n ys) _ τ rfl]
  refine Subtype.ext (Subtype.ext ?_); rw [wp_setResCircuit]
  have hdisj : ∀ i j, xs i ≠ ys j := fun i j h ↦ (Finset.mem_sdiff.mp (h_hit.2
    j)).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h⟩)
  have hvalid : ValidStageStore n S (p + s) res (Store.subst τ res ((encodeTupleFin n m k hps
      (appendTuple xs ys)).val : ℤ)) :=
    ⟨appendTuple xs ys, appendTuple_injective hxs_inj h_hit.1 hdisj,
      image_appendTuple_subset hxs_sub (fun j ↦ (Finset.mem_sdiff.mp (h_hit.2 j)).1),
      by simp [encodeTupleFin]⟩
  rw [liftPureProp_apply, ite_eq_left hvalid]; simp
lemma costBound_zero_commitHitTuple {Var : Type} [DecidableEq Var] {n m k p s : ℕ} (hps : p + s ≤ k)
    (S : Finset (Fin (2 ^ n))) (xs : Fin p → Fin (2 ^ n)) (res : Var) :
    CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k)
    S)) ((commitHitTuple n m k hps xs res).compile QProg.qAssign (groverParallelMarkingOracle
    (activeSlots m k) S)) 0 := by
  unfold commitHitTuple; set G := groverParallelMarkingOracle (activeSlots m k) S
  set e : Expr Var := fun σ ↦ (encodeTuple n (extractHitTupleZ n m k s (σ res)) : ℤ)
  set f := fun ys : Fin s → Fin (2 ^ n) ↦ setResCircuit n m _ res (encodeTupleFin n m k hps
    (appendTuple xs ys))
  suffices ∀ l, CostBound (CostModel.ofEmbeddedOracle G) ((branchOnTupleExpr e f l).compile
    QProg.qAssign G) 0 from this (enumTuples n s)
  intro l; induction l with
  | nil => exact CostBound.skip_zero _
  | cons ys rest ih =>
      rw [← max_self (0 : ℝ≥0)]
      exact CostBound.qIf _ (lossless_And_costBound_qsetSim_setRes (w := activeSlots m k) S res
        _).2.2.2 ih
/-- Diagonal phase-oracle matrix on `Fin B` flipping the phase of marked buckets `i ∈ M`. -/
noncomputable def setOracleMatrix (B : ℕ) (M : Finset (Fin B)) : Matrix (Fin B) (Fin B) ℂ :=
    Matrix.diagonal (fun i ↦ if i ∈ M then -1 else 1)
@[simps]
noncomputable def setOracleUnitary (B : ℕ) (M : Finset (Fin B)) : Unitary B :=
  ⟨setOracleMatrix B M, by
    rw [setOracleMatrix, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    split <;> simp⟩
/-- Grover diffuser `2 |u_B⟩⟨u_B| - I` on `Fin B`. -/
noncomputable def setDiffuserMatrix (B : ℕ) : Matrix (Fin B) (Fin B) ℂ := (Matrix.of fun _ _ ↦ (2 :
    ℂ) / B) - 1
@[simps]
noncomputable def setDiffuserUnitary (B : ℕ) [NeZero B] : Unitary B :=
  ⟨setDiffuserMatrix B, by
    have hB : (B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne B)
    convert (Matrix.isStarProjection_of_const (n := Fin B) ((B : ℂ)⁻¹) _
      _).two_mul_sub_one_mem_unitary
    · rw [setDiffuserMatrix, ← smul_eq_mul, ofNat_smul_eq_nsmul]
      ext; simp; field_simp
    · simp [hB]
    · simp [IsSelfAdjoint]⟩
/-- Half-angle `θ = arcsin(1 / √c)` for inverse target density `c = B / r`. -/
noncomputable def halfAngleReal (c : ℝ) : ℝ := Real.arcsin (1 / √c)
/-- Closed-form multi-target Grover success probability `sin((2K + 1) * arcsin(1 / √c))^2`. -/
noncomputable def p_succ_real (K : ℕ) (c : ℝ) : ℝ := Real.sin ((2 * (K : ℝ) + 1) * halfAngleReal
    c) ^ 2
/-- Early-stopping iteration schedule `round(φ / (2 * arcsin(1 / √c)))` for `c ≥ 32`,
  and `0` for `c < 32`. -/
noncomputable def earlyStoppingIterReal (φ c : ℝ) : ℕ := if 32 ≤ c then Int.toNat (round (φ / (2 *
    halfAngleReal c))) else 0
lemma p_succ_real_nonneg (K : ℕ) (c : ℝ) : 0 ≤ p_succ_real K c := sq_nonneg _
lemma p_succ_real_le_one (K : ℕ) (c : ℝ) : p_succ_real K c ≤ 1 := Real.sin_sq_le_one _
lemma sin_halfAngleReal {c : ℝ} (hc : 1 ≤ c) : Real.sin (halfAngleReal c) = 1 / √c :=
  Real.sin_arcsin (by linarith [show (0 : ℝ) ≤ 1 / √c by positivity])
    ((div_le_one (by positivity)).2 (Real.one_le_sqrt.2 hc))
lemma sqrt_mul_sin_halfAngleReal {c : ℝ} (hc : 1 ≤ c) : √c * Real.sin (halfAngleReal c) = 1 := by
  rw [sin_halfAngleReal hc, mul_one_div_cancel (Real.sqrt_pos.2 (by linarith)).ne']
lemma sin_step_real {c : ℝ} (hc : 1 ≤ c) (k : ℕ) : Real.sin ((2 * (k : ℝ) + 3) * halfAngleReal c) =
    Real.sin ((2 * (k : ℝ) + 1) * halfAngleReal c) + 2 / c * (√c * Real.cos ((2 * (k : ℝ) + 2) *
    halfAngleReal c)) := by
  set θ := halfAngleReal c
  have h := Real.sin_sub_sin ((2 * (k : ℝ) + 3) * θ) ((2 * (k : ℝ) + 1) * θ)
  rw [show ((2 * (k : ℝ) + 3) * θ - (2 * (k : ℝ) + 1) * θ) / 2 = θ by ring,
    show ((2 * (k : ℝ) + 3) * θ + (2 * (k : ℝ) + 1) * θ) / 2 = (2 * (k : ℝ) + 2) * θ by ring,
    sub_eq_iff_eq_add] at h
  rw [h, sin_halfAngleReal hc, ← Real.sqrt_div_self']; ring
lemma cos_step_real {c : ℝ} (hc : 1 ≤ c) (k : ℕ) : √c * Real.cos ((2 * (k : ℝ) + 2) * halfAngleReal
    c) = √c * Real.cos (2 * (k : ℝ) * halfAngleReal c) - 2 * Real.sin ((2 * (k : ℝ) + 1) *
    halfAngleReal c) := by
  set θ := halfAngleReal c; have h := Real.cos_sub_cos (2 * (k : ℝ) * θ) ((2 * (k : ℝ) + 2) * θ)
  rw [show (2 * (k : ℝ) * θ + (2 * (k : ℝ) + 2) * θ) / 2 = (2 * (k : ℝ) + 1) * θ by ring,
    show (2 * (k : ℝ) * θ - (2 * (k : ℝ) + 2) * θ) / 2 = -θ by ring, Real.sin_neg] at h
  linear_combination -√c * h - 2 * Real.sin ((2 * (k : ℝ) + 1) * θ) * sqrt_mul_sin_halfAngleReal hc
lemma setOracleMatrix_mulVec (B : ℕ) (M : Finset (Fin B)) (v : Fin B → ℂ) (i : Fin B) :
    (setOracleMatrix B M *ᵥ v) i = if i ∈ M then -v i else v i := by
  simp [setOracleMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal]
lemma setDiffuserMatrix_mulVec (B : ℕ) (v : Fin B → ℂ) (i : Fin B) : (setDiffuserMatrix B *ᵥ v) i =
    (2 : ℂ) / B * ∑ j, v j - v i := by
  rw [setDiffuserMatrix, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.mulVec_eq_sum]
  simp [-op_smul_eq_smul, Finset.mul_sum]
lemma sum_setOracleMatrix_mulVec (B : ℕ) (M : Finset (Fin B)) (v : Fin B → ℂ) : ∑ i,
    (setOracleMatrix B M *ᵥ v) i = ∑ i, v i - 2 * ∑ i ∈ M, v i := by
  simp_rw [setOracleMatrix_mulVec]
  rw [show (fun i : Fin B ↦ if i ∈ M then -v i else v i) =
      fun i ↦ v i + if i ∈ M then -2 * v i else 0 by funext i; split_ifs <;> ring,
    Finset.sum_add_distrib, ← Finset.sum_filter,
    show Finset.filter (fun i ↦ i ∈ M) Finset.univ = M by ext; simp, ← Finset.mul_sum]; ring
lemma sum_setDiffuserMatrix_mulVec (B : ℕ) [NeZero B] (v : Fin B → ℂ) : ∑ i, (setDiffuserMatrix B *ᵥ
    v) i = ∑ i, v i := by
  simp_rw [setDiffuserMatrix_mulVec]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hB : (B : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne B); field_simp; ring
private lemma groverStep_mark_and_sum {B : ℕ} [NeZero B] {M : Finset (Fin B)} (hM : 1 ≤ M.card)
    {v : Fin B → ℂ} {a s : ℝ} (hm : ∀ i ∈ M, v i = (1 / √(M.card : ℝ) * a : ℝ))
    (hs : ∑ i, v i = (√(B : ℝ) * s : ℝ)) :
    let θ := halfAngleReal ((B : ℝ) / (M.card : ℝ)); let s' := s - 2 * Real.sin θ * a
    (∀ i ∈ M, (setDiffuserMatrix B *ᵥ setOracleMatrix B M *ᵥ v) i = (1 / √(M.card : ℝ) * (2 *
      Real.sin θ * s' + a) : ℝ)) ∧
    ∑ i, (setDiffuserMatrix B *ᵥ setOracleMatrix B M *ᵥ v) i = (√(B : ℝ) * s' : ℝ) := by
  intro θ s'; let r : ℝ := (M.card : ℝ); have hr0 : 0 < r := Nat.cast_pos.mpr hM
  have hB0 : 0 < (B : ℝ) := by exact_mod_cast NeZero.pos B
  have hcard : M.card ≤ B := by simpa using Finset.card_le_univ M
  have hc : 1 ≤ (B : ℝ) / r := (one_le_div hr0).mpr (Nat.cast_le.mpr hcard)
  have hsr := (Real.sqrt_pos.2 hr0).ne'; have hsB := (Real.sqrt_pos.2 hB0).ne'
  have hsq := Real.mul_self_sqrt hr0.le; have hBsq := Real.mul_self_sqrt hB0.le
  have hsin : Real.sin θ = √r / √(B : ℝ) := by
    rw [sin_halfAngleReal hc, Real.sqrt_div hB0.le r, one_div_div]
  have hsumM : ∑ j ∈ M, v j = (√r * a : ℝ) := by
    rw [Finset.sum_congr rfl fun j hj ↦ hm j hj, Finset.sum_const, nsmul_eq_mul]
    have hr_div : r * (1 / √r * a) = √r * a := by field_simp; linear_combination a * hsq.symm
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast, r] using congrArg Complex.ofReal hr_div
  have hdiff : √(B : ℝ) * s - 2 * (√r * a) = √(B : ℝ) * s' := by
    dsimp [s']; rw [← show √(B : ℝ) * Real.sin θ = √r by rw [hsin, mul_div_cancel₀ _ hsB]]; ring
  have h2B : (2 : ℝ) / (B : ℝ) * √(B : ℝ) = (1 / √r) * (2 * Real.sin θ) := by
    rw [hsin]
    calc (2 : ℝ) / (B : ℝ) * √(B : ℝ) = 2 / (√(B : ℝ) * √(B : ℝ)) * √(B : ℝ) := by rw [hBsq]
      _ = (1 / √r) * (2 * (√r / √(B : ℝ))) := by field_simp
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [setDiffuserMatrix_mulVec, sum_setOracleMatrix_mulVec, setOracleMatrix_mulVec,
      ite_eq_left hi, hm i hi, hs, hsumM]
    have hr1 : (2 : ℝ) / (B : ℝ) * (√(B : ℝ) * s - 2 * (√r * a)) - -(1 / √r * a) =
        1 / √r * (2 * Real.sin θ * s' + a) := by rw [hdiff]; linear_combination s' * h2B
    simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.ofReal_natCast] using congrArg Complex.ofReal hr1
  · rw [sum_setDiffuserMatrix_mulVec, sum_setOracleMatrix_mulVec, hs, hsumM]; exact_mod_cast hdiff
/-- State vector on `Fin B` after `K` multi-target Grover iterations from uniform
  superposition. -/
noncomputable def multiTargetState (B : ℕ) (M : Finset (Fin B)) : ℕ → Fin B → ℂ
  | 0 => fun _ ↦ (1 / √(B : ℝ) : ℝ)
  | k + 1 => setDiffuserMatrix B *ᵥ setOracleMatrix B M *ᵥ multiTargetState B M k
/-- Coupled two-invariant recurrence for multi-target Grover search on `Fin B`
  with marked set `M`. -/
theorem multiTargetState_sum_invariants (B : ℕ) [NeZero B] (M : Finset (Fin B)) (hM : 1 ≤ M.card) (K
    : ℕ) : (∀ i ∈ M, multiTargetState B M K i = ((1 / √(M.card : ℝ)) * Real.sin ((2 * (K : ℝ) + 1) *
    halfAngleReal ((B : ℝ) / (M.card : ℝ))) : ℝ)) ∧ ∑ i : Fin B, multiTargetState B M K i = (√(B :
    ℝ) * Real.cos (2 * (K : ℝ) * halfAngleReal ((B : ℝ) / (M.card : ℝ))) : ℝ) := by
  set r : ℝ := (M.card : ℝ); set c : ℝ := (B : ℝ) / r; have hr_pos : 0 < r := Nat.cast_pos.mpr hM
  have hB_pos : 0 < (B : ℝ) := by exact_mod_cast NeZero.pos B
  have hcard : M.card ≤ B := by simpa using Finset.card_le_univ M
  have hc : 1 ≤ c := (one_le_div hr_pos).mpr (Nat.cast_le.mpr hcard)
  have hsqrt_c : √c = √(B : ℝ) / √r := Real.sqrt_div hB_pos.le r
  induction K with
  | zero =>
      refine ⟨fun i _ ↦ ?_, ?_⟩
      · simp only [multiTargetState, Nat.cast_zero, mul_zero, zero_add, one_mul,
          sin_halfAngleReal hc, hsqrt_c]
        have hsr := (Real.sqrt_pos.2 hr_pos).ne'; have hsB := (Real.sqrt_pos.2 hB_pos).ne'
        congr 1; field_simp
      · simp only [multiTargetState, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, mul_one]
        exact_mod_cast (by simpa [div_eq_mul_inv] using Real.div_sqrt (x := (B : ℝ)) :
          (B : ℝ) * (1 / √(B : ℝ)) = √(B : ℝ))
  | succ k ih =>
      rcases groverStep_mark_and_sum hM ih.1 ih.2 with ⟨hm', hs'⟩
      let θ := halfAngleReal c; let α := (2 * (k : ℝ) + 1) * θ; let β := 2 * ((k + 1 : ℕ) : ℝ) * θ
      have hc1 : Real.cos (2 * (k : ℝ) * θ) - 2 * Real.sin θ * Real.sin α = Real.cos β := by
        rw [show 2 * (k : ℝ) * θ = α - θ by dsimp [α]; ring,
          show β = α + θ by dsimp [α, β]; push_cast; ring, Real.cos_sub, Real.cos_add]; ring
      have hs1 : 2 * Real.sin θ * (Real.cos (2 * (k : ℝ) * θ) - 2 * Real.sin θ * Real.sin α) +
          Real.sin α = Real.sin ((2 * ((k + 1 : ℕ) : ℝ) + 1) * θ) := by
        rw [hc1, show α = β - θ by dsimp [α, β]; push_cast; ring,
          show (2 * ((k + 1 : ℕ) : ℝ) + 1) * θ = β + θ by dsimp [β]; ring,
          Real.sin_sub, Real.sin_add]; ring
      exact ⟨fun i hi ↦ (hm' i hi).trans (congrArg (fun x : ℝ ↦ ((1 / √r * x : ℝ) : ℂ))
        hs1), hs'.trans (congrArg (fun x : ℝ ↦ ((√(B : ℝ) * x : ℝ) : ℂ)) hc1)⟩
/-- Total probability on `M` after `K` multi-target Grover steps equals
  `p_succ_real K (B / M.card)`. -/
theorem multiTarget_success_prob_eq (B : ℕ) [NeZero B] (M : Finset (Fin B)) (hM : 1 ≤ M.card) (K :
    ℕ) : (∑ i ∈ M, Complex.normSq (multiTargetState B M K i)) = p_succ_real K ((B : ℝ) / (M.card :
    ℝ)) := by
  have hinv := (multiTargetState_sum_invariants B M hM K).1
  have hr_pos : (0 : ℝ) < (M.card : ℝ) := by exact_mod_cast (by omega : 0 < M.card)
  have hcongr : ∀ i ∈ M, Complex.normSq (multiTargetState B M K i) = (1 / (M.card : ℝ)) *
    p_succ_real K ((B : ℝ) / (M.card : ℝ)) := by
    intro i hi; rw [hinv i hi, Complex.normSq_ofReal]; dsimp [p_succ_real]
    have hsq : √(M.card : ℝ) * √(M.card : ℝ) = (M.card : ℝ) := Real.mul_self_sqrt hr_pos.le
    have hsr : √(M.card : ℝ) ≠ 0 := (Real.sqrt_pos.2 hr_pos).ne'
    field_simp
    linear_combination Real.sin ((2 * (K : ℝ) + 1) * halfAngleReal ((B : ℝ) / (M.card : ℝ))) ^ 2 *
      hsq.symm
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]; field_simp
/-!
## 1. Zero-Cost Sign-Tagged Non-Oracle Unitaries (`tagUnitary`)
-/
/-- The first `Q` wires inside a `(Q + 1)`-wire system. -/
def tagSysReg (Q : ℕ) : QRegister Q (Q + 1) := QRegister.block 0 Q (by omega)
/-- The last wire `Q` (the sign-tag wire) inside a `(Q + 1)`-wire system. -/
def tagWireReg (Q : ℕ) : QRegister 1 (Q + 1) := QRegister.block Q 1 (by omega)
lemma tagSysReg_disjoint_tagWireReg (Q : ℕ) : (tagSysReg Q).DisjointWires (tagWireReg Q) :=
    QRegister.block_disjoint_of_le 0 Q Q 1 (by omega) (by omega) (by omega)
/-- Block-diagonal matrix applying `U` on `tagWireReg = 0` and `-1` on `tagWireReg = 1`. -/
noncomputable def tagMatrix {Q : ℕ} (U : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) : Matrix (Fin (2 ^ (Q
    + 1))) (Fin (2 ^ (Q + 1))) ℂ := (tagSysReg Q).embedMatrix U * (tagWireReg
    Q).basisOutcomeProjector 0 - (tagWireReg Q).basisOutcomeProjector 1
lemma tagWireReg_proj_zero_mul_one (Q : ℕ) : (tagWireReg Q).basisOutcomeProjector 0 * (tagWireReg
    Q).basisOutcomeProjector 1 = 0 := by
  rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
    ← (tagWireReg Q).embedMatrix_mul, compProj_mul_of_ne (by intro h; cases congrArg Fin.val h),
    (tagWireReg Q).embedMatrix_zero]
lemma tagWireReg_proj_one_mul_zero (Q : ℕ) : (tagWireReg Q).basisOutcomeProjector 1 * (tagWireReg
    Q).basisOutcomeProjector 0 = 0 := by
  rw [QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector,
    ← (tagWireReg Q).embedMatrix_mul, compProj_mul_of_ne (by intro h; cases congrArg Fin.val h),
    (tagWireReg Q).embedMatrix_zero]
lemma tagWireReg_proj_add_eq_one (Q : ℕ) : (tagWireReg Q).basisOutcomeProjector 0 + (tagWireReg
    Q).basisOutcomeProjector 1 = 1 := by
  simpa [Fin.sum_univ_two] using (tagWireReg Q).sum_basisOutcomeProjector
lemma embedMatrix_comm_tagWireReg_proj {Q : ℕ} (U : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) (b : Fin
    (2 ^ 1)) : (tagSysReg Q).embedMatrix U * (tagWireReg Q).basisOutcomeProjector b = (tagWireReg
    Q).basisOutcomeProjector b * (tagSysReg Q).embedMatrix U := (tagSysReg
    Q).embedMatrix_comm_of_disjoint (tagWireReg Q) (tagSysReg_disjoint_tagWireReg Q) U (compProj b)
lemma tagMatrix_conjTranspose {Q : ℕ} (U : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) : (tagMatrix U)ᴴ =
    tagMatrix Uᴴ := by
  dsimp [tagMatrix]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, (tagWireReg
    Q).basisOutcomeProjector_conjTranspose 0, (tagWireReg Q).basisOutcomeProjector_conjTranspose 1,
    ← (tagSysReg Q).embedMatrix_conjTranspose, ← embedMatrix_comm_tagWireReg_proj Uᴴ 0]
lemma tagMatrix_mul {Q : ℕ} (U V : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) : tagMatrix U *
    tagMatrix V = (tagSysReg Q).embedMatrix (U * V) * (tagWireReg Q).basisOutcomeProjector 0 +
    (tagWireReg Q).basisOutcomeProjector 1 := by
  dsimp [tagMatrix]; let P0 := (tagWireReg Q).basisOutcomeProjector 0
  let P1 := (tagWireReg Q).basisOutcomeProjector 1; let E := (tagSysReg Q).embedMatrix
  have hV : E V * P0 = P0 * E V := embedMatrix_comm_tagWireReg_proj V 0
  have hUV : E U * P0 * (E V * P0) = E (U * V) * P0 := by
    rw [hV, Matrix.mul_assoc (E U), ← Matrix.mul_assoc P0, (tagWireReg
      Q).basisOutcomeProjector_mul_self 0, ← hV, ← Matrix.mul_assoc, ← (tagSysReg
      Q).embedMatrix_mul]
  calc (E U * P0 - P1) * (E V * P0 - P1)
    = E U * P0 * (E V * P0) - E U * (P0 * P1) - P1 * P0 * E V + P1 * P1 := by rw [hV]; noncomm_ring
    _ = E (U * V) * P0 + P1 := by
        rw [hUV, tagWireReg_proj_zero_mul_one, tagWireReg_proj_one_mul_zero, (tagWireReg
          Q).basisOutcomeProjector_mul_self 1]; noncomm_ring
/-- Wrap any `Q`-qubit unitary `U` into a `(Q + 1)`-qubit unitary acting as `U` on
  `tagWireReg = 0`
  and as `-1` on `tagWireReg = 1`. -/
noncomputable def tagUnitary {Q : ℕ} (U : Unitary (2 ^ Q)) : Unitary (2 ^ (Q + 1)) :=
  ⟨tagMatrix U.1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, tagMatrix_conjTranspose]
    have h1 : U.1 * U.1ᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.2
    rw [tagMatrix_mul, h1, (tagSysReg Q).embedMatrix_one, one_mul, tagWireReg_proj_add_eq_one]⟩
@[simp]
lemma tagUnitary_val {Q : ℕ} (U : Unitary (2 ^ Q)) : (tagUnitary U).1 = tagMatrix U.1 := rfl
/-!
## 2. Single-Slot Ancilla Hadamard Phase Kickback
-/
/-- Address component `x: Fin (2 ^ n)` of a `(n + 1)`-qubit oracle slot index. -/
def slotAddr {n : ℕ} (u : Fin (2 ^ (n + 1))) : Fin (2 ^ n) := (splitBasisEquiv n 1 u).1
/-- Ancilla bit component `b: Fin (2 ^ 1)` of a `(n + 1)`-qubit oracle slot index. -/
def slotBit {n : ℕ} (u : Fin (2 ^ (n + 1))) : Fin (2 ^ 1) := (splitBasisEquiv n 1 u).2
/-- Pack `(addr, bit)` into `Fin (2 ^ (n + 1))`. -/
def mkSlotIdx {n : ℕ} (x : Fin (2 ^ n)) (b : Fin (2 ^ 1)) : Fin (2 ^ (n + 1)) := (splitBasisEquiv n
    1).symm (x, b)
@[simp]
lemma slotAddr_mkSlotIdx {n : ℕ} (x : Fin (2 ^ n)) (b : Fin (2 ^ 1)) : slotAddr (mkSlotIdx x b) =
    x := by dsimp only [slotAddr, mkSlotIdx]; rw [Equiv.apply_symm_apply]
@[simp] lemma slotBit_mkSlotIdx {n : ℕ} (x : Fin (2 ^ n)) (b : Fin (2 ^ 1)) : slotBit (mkSlotIdx x
    b) = b := by dsimp only [slotBit, mkSlotIdx]; rw [Equiv.apply_symm_apply]
@[simp] lemma mkSlotIdx_slotAddr_slotBit {n : ℕ} (u : Fin (2 ^ (n + 1))) : mkSlotIdx (slotAddr
    u) (slotBit u) = u := by
  dsimp only [slotAddr, slotBit, mkSlotIdx]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
/-- Hadamard matrix `I_{2^n} ⊗ H` acting on the ancilla bit of a `(n + 1)`-qubit oracle
  slot. -/
noncomputable def ancHMatrix (n : ℕ) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ :=
    Matrix.of fun u v ↦ if slotAddr u = slotAddr v then (1 / √2 : ℂ) * (if slotBit u = 1 ∧ slotBit v
    = 1 then -1 else 1) else 0
@[simp]
lemma ancHMatrix_conjTranspose (n : ℕ) : (ancHMatrix n)ᴴ = ancHMatrix n := by
  ext u v; simp only [ancHMatrix, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : slotAddr v = slotAddr u
  · rw [ite_eq_left h, ite_eq_left h.symm]; by_cases hb : slotBit u = 1 ∧ slotBit v = 1
    · simp [hb]
    · simp [hb, show ¬ (slotBit v = 1 ∧ slotBit u = 1) from fun h' ↦ hb ⟨h'.2, h'.1⟩]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), star_zero]
lemma fin2_eq_zero_or_one (b : Fin (2 ^ 1)) : b = 0 ∨ b = 1 :=
  match b with | ⟨0, _⟩ => Or.inl rfl | ⟨1, _⟩ => Or.inr rfl | ⟨_ + 2, h⟩ => absurd h (by omega)
@[simp] lemma ancHMatrix_apply {n : ℕ} (u v : Fin (2 ^ (n + 1))) : ancHMatrix n u v =
    if slotAddr u = slotAddr v then (1 / √2 : ℂ) * (if slotBit u = 1 ∧ slotBit v = 1 then -1 else
    1) else 0 := rfl
/-!
## Householder State Preparation `U_prep(B)` and Subspace Block Embedding
-/
/-- Real symmetric rank-1 projection entries onto `w_0 = √((√B + 1)/(2 √B))`,
  `w_i = 1 / √(2 √B (√B + 1))`. -/
noncomputable def householderProjReal (B : ℕ) (i j : Fin B) : ℝ :=
  let s := √(B : ℝ)
  if i.val = 0 then if j.val = 0 then (s + 1) / (2 * s) else 1 / (2 * s)
  else if j.val = 0 then 1 / (2 * s) else 1 / (2 * s * (s + 1))
/-- Rank-1 projection matrix `|w⟩⟨w|` on `Fin B`. -/
noncomputable def householderProjMatrix (B : ℕ) : Matrix (Fin B) (Fin B) ℂ :=
    Matrix.of fun i j ↦ (householderProjReal B i j : ℂ)
lemma householderProjMatrix_isSelfAdjoint (B : ℕ) : IsSelfAdjoint (householderProjMatrix B) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]; ext i j
  simp only [householderProjMatrix, householderProjReal, Matrix.conjTranspose_apply,
    Matrix.of_apply]
  split_ifs <;> simp
lemma householderProjMatrix_isIdempotentElem (B : ℕ) [NeZero B] :
    IsIdempotentElem (householderProjMatrix B) := by
  rw [IsIdempotentElem]; ext i j; rw [Matrix.mul_apply]; set s : ℝ := √(B : ℝ)
  have hB_pos : 0 < (B : ℝ) := (by exact_mod_cast (NeZero.pos B))
  have hs_pos : 0 < s := Real.sqrt_pos.2 hB_pos; have hs_ne : s ≠ 0 := hs_pos.ne'
  have hs1_ne : s + 1 ≠ 0 := (by linarith)
  have hs_sq : s * s = (B : ℝ) := Real.mul_self_sqrt hB_pos.le; let k0 : Fin B := ⟨0, NeZero.pos B⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k0)]
  let f (x : Fin B) : ℝ := if x.val = 0 then 1 / (2 * s) else 1 / (2 * s * (s + 1))
  have hrest_congr : ∀ k ∈ Finset.univ.erase k0,
      householderProjMatrix B i k * householderProjMatrix B k j = ((f i * f j : ℝ) : ℂ) := by
    intro k hk; have hk0 : k.val ≠ 0 := fun hv ↦ (Finset.mem_erase.mp hk).1 (Fin.ext hv)
    dsimp [householderProjMatrix, householderProjReal, f, s]
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;> simp only [hi, hj, hk0, ↓reduceIte,
      Complex.ofReal_mul]
  rw [Finset.sum_congr rfl hrest_congr, Finset.sum_const, nsmul_eq_mul]
  have hreal : householderProjReal B i k0 * householderProjReal B k0 j + ((Finset.univ.erase k0 :
      Finset (Fin B)).card : ℝ) * (f i * f j) =
      householderProjReal B i j := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k0), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (NeZero.one_le), Nat.cast_one, ← hs_sq]
    dsimp [householderProjReal, k0, f]
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;> simp only [hi, hj,
      ↓reduceIte] <;> field_simp <;> ring
  simpa only [householderProjMatrix, Matrix.of_apply, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_natCast] using congrArg Complex.ofReal hreal
lemma householderProjMatrix_isStarProjection (B : ℕ) [NeZero B] :
    IsStarProjection (householderProjMatrix B) :=
  ⟨householderProjMatrix_isIdempotentElem B, householderProjMatrix_isSelfAdjoint B⟩
/-- Householder state preparation unitary `2 |w⟩⟨w| - I` on `Fin B`. -/
noncomputable def householderPrepUnitary (B : ℕ) [NeZero B] : Unitary B :=
    ⟨2 * householderProjMatrix B - 1, (householderProjMatrix_isStarProjection
    B).two_mul_sub_one_mem_unitary⟩
/-- Column `0` of `householderPrepUnitary B` is the uniform superposition `1 / √B` on `Fin
  B`. -/
theorem householderPrepUnitary_apply_zero (B : ℕ) [NeZero B] (i : Fin B) : (householderPrepUnitary
    B).1 i ⟨0, NeZero.pos B⟩ = (1 / √(B : ℝ) : ℂ) := by
  set s := √(B : ℝ); have hs_ne : s ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos B)).ne'
  rw [show (householderPrepUnitary B).1 = householderProjMatrix B + householderProjMatrix B - 1 by
      dsimp [householderPrepUnitary]; rw [two_mul],
    Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]
  dsimp only [householderProjMatrix, householderProjReal, Matrix.of_apply]
  simp only [show (i = ⟨0, NeZero.pos B⟩) ↔ i.val = 0 from Fin.ext_iff]
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceIte]; exact_mod_cast (by field_simp; ring :
      (s + 1) / (2 * s) + (s + 1) / (2 * s) - 1 = 1 / s)
  · simp only [hi, ↓reduceIte, sub_zero]; exact_mod_cast (by field_simp; ring :
      1 / (2 * s) + 1 / (2 * s) = 1 / s)
/-- Block-diagonal embedding of a `B × B` matrix into the top-left `B × B` corner of `Fin W`
  (with `1` on the remaining `W - B` diagonal entries). -/
def embedBlockMatrix {B W : ℕ} (_hBW : B ≤ W) (A : Matrix (Fin B) (Fin B) ℂ) : Matrix (Fin W) (Fin
    W) ℂ := Matrix.of fun i j ↦ if hi : i.val < B then if hj : j.val <
    B then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else if i = j then 1 else 0
lemma sum_fin_castLE_of_ge_zero {B W : ℕ} (hBW : B ≤ W) (f : Fin W → ℂ) (hf : ∀ k : Fin W, ¬ k.val <
    B → f k = 0) : ∑ k : Fin W, f k = ∑ k : Fin B, f (Fin.castLE hBW k) := by
  refine (Finset.sum_subset (Finset.subset_univ _) fun k _ hk ↦ hf k fun hlt ↦ hk
    (Finset.mem_map.mpr ⟨⟨k.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)).symm.trans (Finset.sum_map
    _ (Fin.castLEEmb hBW) _)
@[simp] lemma embedBlockMatrix_one {B W : ℕ} (hBW : B ≤ W) : embedBlockMatrix hBW (1 : Matrix (Fin
    B) (Fin B) ℂ) = 1 := by
  ext i j; rw [Matrix.one_apply]; dsimp only [embedBlockMatrix, Matrix.of_apply]
  by_cases hi : i.val < B <;> by_cases hj : j.val < B
  · simp [hi, hj, Matrix.one_apply, Fin.ext_iff]
  · have hij : i ≠ j := fun h ↦ hj (h ▸ hi); simp [hi, hj, hij]
  · have hij : i ≠ j := fun h ↦ hi (h ▸ hj); simp [hi, hij]
  · simp [hi]
@[simp] lemma embedBlockMatrix_conjTranspose {B W : ℕ} (hBW : B ≤ W) (A : Matrix (Fin B) (Fin B) ℂ)
    : (embedBlockMatrix hBW A)ᴴ = embedBlockMatrix hBW Aᴴ := by
  ext i j; simp only [embedBlockMatrix, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hi : i.val < B <;> by_cases hj : j.val < B
  · simp [hi, hj]
  · have hji : j ≠ i := fun h ↦ hj (h ▸ hi); simp [hi, hj, hji]
  · have hij : i ≠ j := fun h ↦ hi (h ▸ hj); simp [hi, hj, hij]
  · simp [hi, hj, eq_comm]
@[simp] lemma embedBlockMatrix_mul {B W : ℕ} (hBW : B ≤ W) (A C : Matrix (Fin B) (Fin B) ℂ) :
    embedBlockMatrix hBW (A * C) = embedBlockMatrix hBW A * embedBlockMatrix hBW C := by
  ext i j; rw [Matrix.mul_apply]; by_cases hi : i.val < B
  · by_cases hj : j.val < B
    · simp only [embedBlockMatrix, Matrix.of_apply, hi, hj, ↓reduceDIte, Matrix.mul_apply]; symm
      rw [sum_fin_castLE_of_ge_zero hBW _ (fun k hk ↦ by simp [hk])]
      exact Finset.sum_congr rfl fun k _ ↦ by simp [k.isLt]
    · simp only [embedBlockMatrix, Matrix.of_apply, hi, hj, ↓reduceDIte]; symm
      exact Finset.sum_eq_zero fun k _ ↦ by by_cases hk : k.val < B <;> simp [hk]
  · simp only [embedBlockMatrix, Matrix.of_apply, hi, ↓reduceDIte]
    rw [Fintype.sum_eq_single i (fun k hk ↦ by simp [hk.symm])]; simp [hi]
/-- Embed a `B × B` unitary into `Unitary W` for `B ≤ W`. -/
noncomputable def embedBlockUnitary {B W : ℕ} (hBW : B ≤ W) (U : Unitary B) : Unitary W :=
  ⟨embedBlockMatrix hBW U.1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, embedBlockMatrix_conjTranspose, ←
      embedBlockMatrix_mul]
    have h1 : U.1 * U.1ᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact U.2.2
    rw [h1, embedBlockMatrix_one]⟩
/-- Zero-padded embedding of a vector `v: Fin B → ℂ` into `Fin W → ℂ`. -/
def embedBlockVec {B W : ℕ} (_hBW : B ≤ W) (v : Fin B → ℂ) : Fin W → ℂ := fun i ↦ if hi : i.val <
    B then v ⟨i.val, hi⟩ else 0
lemma embedBlockMatrix_mulVec {B W : ℕ} (hBW : B ≤ W) (A : Matrix (Fin B) (Fin B) ℂ) (v : Fin B → ℂ)
    : embedBlockMatrix hBW A *ᵥ embedBlockVec hBW v = embedBlockVec hBW (A *ᵥ v) := by
  funext i; rw [Matrix.mulVec, dotProduct]; by_cases hi : i.val < B
  · simp only [embedBlockVec, hi, ↓reduceDIte, Matrix.mulVec, dotProduct]
    rw [sum_fin_castLE_of_ge_zero hBW _ (fun k hk ↦ by simp [hk])]
    exact Finset.sum_congr rfl fun k _ ↦ by simp [embedBlockMatrix, hi, k.isLt]
  · simp only [embedBlockVec, hi, ↓reduceDIte]; exact Finset.sum_eq_zero fun k _ ↦ by
      rcases eq_or_ne i k with rfl | hik
      · simp [embedBlockMatrix, hi]
      · simp [embedBlockMatrix, hi, hik]
/-!
## 1. Register Layout and Wire Disjointness inside `groverFindAllQubitsInternal`
-/
def groverSysQubits (n m k : ℕ) : ℕ := k * n + m * (n + 1) + 1
def groverFindAllQubitsInternal (n m k : ℕ) : ℕ := groverSysQubits n m k + 1
def tagReg (n m k : ℕ) : QRegister 1 (groverFindAllQubitsInternal n m k) :=
    tagWireReg (groverSysQubits n m k)
def sysReg (n m k : ℕ) : QRegister (groverSysQubits n m k) (groverFindAllQubitsInternal n m k) :=
    tagSysReg (groverSysQubits n m k)
def sysOutReg (n m k : ℕ) : QRegister (k * n) (groverSysQubits n m k) :=
  QRegister.block 0 (k * n) (by dsimp [groverSysQubits]; omega)
def sysWorkReg (n m k : ℕ) : QRegister (m * (n + 1)) (groverSysQubits n m k) :=
  QRegister.block (k * n) (m * (n + 1)) (by dsimp [groverSysQubits]; omega)
def sysFlagReg (n m k : ℕ) : QRegister 1 (groverSysQubits n m k) :=
  QRegister.block (k * n + m * (n + 1)) 1 (by dsimp [groverSysQubits]; omega)
def localSlotReg (n m : ℕ) (j : Fin m) : QRegister (n + 1) (m * (n + 1)) := QRegister.block (j.val *
    (n + 1)) (n + 1) (by nlinarith [j.isLt])
def slotReg (n m k : ℕ) (j : Fin m) : QRegister (n + 1) (groverFindAllQubitsInternal n m k) :=
    QRegister.block (k * n + j.val * (n + 1)) (n + 1)
    (by dsimp [groverFindAllQubitsInternal, groverSysQubits]; nlinarith [j.isLt])
lemma sysOutReg_disjoint_sysWorkReg (n m k : ℕ) : (sysOutReg n m k).DisjointWires (sysWorkReg n m
    k) := QRegister.block_disjoint_of_le 0 (k * n) (k * n) (m * (n + 1))
    (by dsimp [groverSysQubits]; omega) (by dsimp [groverSysQubits]; omega) (by omega)
lemma sysOutReg_disjoint_sysFlagReg (n m k : ℕ) : (sysOutReg n m k).DisjointWires (sysFlagReg n m
    k) := QRegister.block_disjoint_of_le 0 (k * n) (k * n + m * (n + 1)) 1
    (by dsimp [groverSysQubits]; omega) (by dsimp [groverSysQubits]; omega) (by omega)
lemma sysWorkReg_disjoint_sysFlagReg (n m k : ℕ) : (sysWorkReg n m k).DisjointWires (sysFlagReg n m
    k) := QRegister.block_disjoint_of_le (k * n) (m * (n + 1)) (k * n + m * (n + 1)) 1
    (by dsimp [groverSysQubits]; omega) (by dsimp [groverSysQubits]; omega) (by omega)
lemma localSlotReg_disjoint (n m : ℕ) {j₁ j₂ : Fin m} (hne : j₁ ≠ j₂) : (localSlotReg n m
    j₁).DisjointWires (localSlotReg n m j₂) := by
  have hval : j₁.val ≠ j₂.val := fun h ↦ hne (Fin.ext h); rcases lt_or_gt_of_ne hval with hlt | hgt
  · exact QRegister.block_disjoint_of_le (j₁.val * (n + 1)) (n + 1) (j₂.val * (n + 1)) (n + 1)
      (by nlinarith [j₁.isLt]) (by nlinarith [j₂.isLt]) (by nlinarith)
  · exact QRegister.disjoint_comm.mp
      (QRegister.block_disjoint_of_le (j₂.val * (n + 1)) (n + 1) (j₁.val * (n + 1)) (n + 1)
        (by nlinarith [j₂.isLt]) (by nlinarith [j₁.isLt]) (by nlinarith))
/-!
## 2. Bucket Partitioning and Collision-Free Target Sets (`GoodTargetSet`)
-/
/-- Effective bucket size `max 1 (min b (2 ^ n))` (always in `[1, 2 ^ n]`). -/
def bEff (n b : ℕ) : ℕ := max 1 (min b (2 ^ n))
/-- Number of full buckets `B = 2 ^ n / bEff n b` (always `≥ 1`). -/
def bucketCount (n b : ℕ) : ℕ := 2 ^ n / bEff n b
lemma bEff_pos (n b : ℕ) : 0 < bEff n b := by dsimp [bEff]; omega
lemma bEff_le_two_pow (n b : ℕ) : bEff n b ≤ 2 ^ n := by
  dsimp [bEff]; have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega
lemma bucketCount_pos (n b : ℕ) : 0 < bucketCount n b := Nat.div_pos (bEff_le_two_pow n b) (bEff_pos
    n b)
instance instNeZeroBucketCount (n b : ℕ) : NeZero (bucketCount n b) := ⟨(bucketCount_pos n b).ne'⟩
/-!
## 3. Controlled Register Permutations and Coherent Bucket Trial Circuit
-/
/-- Pack `m` local slot indices `Fin m → Fin (2 ^ (n + 1))` into a `workReg` basis index. -/
noncomputable def packWorkSlots (n m : ℕ) (slots : Fin m → Fin (2 ^ (n + 1))) : Fin (2 ^ (m * (n +
    1))) := (List.finRange m).foldr (fun j acc ↦ (localSlotReg n m j).replaceIndex acc (slots j)) 0
/-- Guard predicate `σ res = 0` (`True` when stage `s` has not yet found a new target). -/
def stageRetryGuard {Var : Type} (res : Var) : Store Var → Prop := fun σ ↦ σ res = 0
instance instDecidablePredStageRetryGuard {Var : Type} (res : Var) : DecidablePred (stageRetryGuard
    res) := fun σ ↦ inferInstanceAs (Decidable (σ res = 0))
/-!
## 4. Stage Fiber Observables and Expected Cost Witnesses
-/
/-!
## Combinatorial Collision & Remainder Bound (`badTargetSet_card_le`, `0` sorries)
-/
lemma add_one_mul_choose_eq (N r : ℕ) : (N + 1) * Nat.choose N r = Nat.choose (N + 1) (r + 1) * (r +
    1) := by
  induction N generalizing r with
  | zero =>
      rcases r with _ | r
      · simp
      · simp [Nat.choose_eq_zero_of_lt (by omega : 1 < r + 2)]
  | succ N ih =>
      rcases r with _ | r
      · simp
      · nlinarith [ih r, ih (r + 1), Nat.choose_succ_succ N r,
          Nat.choose_succ_succ (N + 1) (r + 1)]
/-!
## 1. Losslessness of `parallelBucketTrial`
-/
/-!
## 2. Single-Trial Weakest-Precondition Fiber Lemmas
-/
/-!
### 2.1 Register Decomposition & System-Subspace Lifting
-/
@[simp] lemma block_wires_val {s r n : ℕ} (h : s + r ≤ n) (i : Fin r) : ((QRegister.block s r h).1
    i).val = s + i.val := rfl
@[simp] lemma block_apply_val {s r n : ℕ} (h : s + r ≤ n) (i : Fin r) : (QRegister.block s r h
    i).val = s + i.val := rfl
@[simp] lemma compose_wires_val {w₁ w₂ w₃ : ℕ} (r₁ : QRegister w₂ w₃) (r₂ : QRegister w₁ w₂) (i :
    Fin w₁) : ((r₁.compose r₂).1 i).val = (r₁ (r₂ i)).val := rfl
@[simp] lemma compose_apply_val {w₁ w₂ w₃ : ℕ} (r₁ : QRegister w₂ w₃) (r₂ : QRegister w₁ w₂) (i :
    Fin w₁) : (r₁.compose r₂ i).val = (r₁ (r₂ i)).val := rfl
@[simp] lemma sysReg_wires_val (n m k : ℕ) (i : Fin (groverSysQubits n m k)) : ((sysReg n m k).1
    i).val = 0 + i.val := rfl
@[simp] lemma sysReg_apply_val (n m k : ℕ) (i : Fin (groverSysQubits n m k)) : (sysReg n m k
    i).val = 0 + i.val := rfl
@[simp] lemma tagReg_wires_val (n m k : ℕ) (i : Fin 1) : ((tagReg n m k).1 i).val =
    groverSysQubits n m k + i.val := rfl
@[simp] lemma tagReg_apply_val (n m k : ℕ) (i : Fin 1) : (tagReg n m k i).val =
    groverSysQubits n m k + i.val := rfl
lemma sysState_ext {n m k : ℕ} {u v : Fin (2 ^ groverSysQubits n m k)} (ho : (sysOutReg n m
    k).extractIndex u = (sysOutReg n m k).extractIndex v) (hw : (sysWorkReg n m k).extractIndex u =
    (sysWorkReg n m k).extractIndex v) (hf : (sysFlagReg n m k).extractIndex u = (sysFlagReg n m
    k).extractIndex v) : u = v := by
  apply (basisBits (groverSysQubits n m k)).injective; funext q
  have hq0 : q.val < k * n + m * (n + 1) + 1 := q.isLt
  by_cases h1 : q.val < k * n
  · rw [show q = sysOutReg n m k ⟨q.val, h1⟩ from Fin.ext (by simp [sysOutReg]),
      ← (sysOutReg n m k).basisBits_extractIndex, ← (sysOutReg n m k).basisBits_extractIndex, ho]
  · by_cases h2 : q.val < k * n + m * (n + 1)
    · rw [show q = sysWorkReg n m k ⟨q.val - k * n, by omega⟩ from Fin.ext
        (by simp only [sysWorkReg, block_apply_val]; omega),
        ← (sysWorkReg n m k).basisBits_extractIndex,
        ← (sysWorkReg n m k).basisBits_extractIndex, hw]
    · rw [show q = sysFlagReg n m k ⟨0, by omega⟩ from Fin.ext
        (by simp only [sysFlagReg, block_apply_val]; omega),
        ← (sysFlagReg n m k).basisBits_extractIndex,
        ← (sysFlagReg n m k).basisBits_extractIndex, hf]
noncomputable def mkSysState (n m k : ℕ) (y : Fin (2 ^ (k * n))) (w : Fin (2 ^ (m * (n + 1)))) (f :
    Fin (2 ^ 1)) : Fin (2 ^ groverSysQubits n m k) := (sysFlagReg n m k).replaceIndex ((sysWorkReg n
    m k).replaceIndex ((sysOutReg n m k).replaceIndex 0 y) w) f
@[simp]
lemma extractIndex_sysOutReg_mkSysState (n m k : ℕ) (y : Fin (2 ^ (k * n))) (w : Fin (2 ^ (m * (n +
    1)))) (f : Fin (2 ^ 1)) : (sysOutReg n m k).extractIndex (mkSysState n m k y w f) = y := by
  simp [mkSysState, (sysOutReg n m k).extractIndex_replaceIndex_of_disjoint _
    (sysOutReg_disjoint_sysFlagReg n m k), (sysOutReg n m k).extractIndex_replaceIndex_of_disjoint _
    (sysOutReg_disjoint_sysWorkReg n m k)]
@[simp] lemma extractIndex_sysWorkReg_mkSysState (n m k : ℕ) (y : Fin (2 ^ (k * n))) (w : Fin (2 ^
    (m * (n + 1)))) (f : Fin (2 ^ 1)) : (sysWorkReg n m k).extractIndex (mkSysState n m k y w f) =
    w := by
  simp [mkSysState, (sysWorkReg n m k).extractIndex_replaceIndex_of_disjoint _
    (sysWorkReg_disjoint_sysFlagReg n m k)]
@[simp] lemma extractIndex_sysFlagReg_mkSysState (n m k : ℕ) (y : Fin (2 ^ (k * n))) (w : Fin (2 ^
    (m * (n + 1)))) (f : Fin (2 ^ 1)) : (sysFlagReg n m k).extractIndex (mkSysState n m k y w f) =
    f := by simp [mkSysState]
@[simp] lemma replaceIndex_sysOutReg_mkSysState (n m k : ℕ) (y y' : Fin (2 ^ (k * n))) (w : Fin (2 ^
    (m * (n + 1)))) (f : Fin (2 ^ 1)) : (sysOutReg n m k).replaceIndex (mkSysState n m k y w f) y' =
    mkSysState n m k y' w f := by
  apply sysState_ext <;> simp [(sysWorkReg n m k).extractIndex_replaceIndex_of_disjoint _
    (QRegister.disjoint_comm.mp (sysOutReg_disjoint_sysWorkReg n m k)), (sysFlagReg n m
    k).extractIndex_replaceIndex_of_disjoint _ (QRegister.disjoint_comm.mp
    (sysOutReg_disjoint_sysFlagReg n m k))]
@[simp] lemma replaceIndex_sysWorkReg_mkSysState (n m k : ℕ) (y : Fin (2 ^ (k * n))) (w w' : Fin (2
    ^ (m * (n + 1)))) (f : Fin (2 ^ 1)) : (sysWorkReg n m k).replaceIndex (mkSysState n m k y w
    f) w' = mkSysState n m k y w' f := by
  apply sysState_ext <;> simp [(sysOutReg n m k).extractIndex_replaceIndex_of_disjoint _
    (sysOutReg_disjoint_sysWorkReg n m k), (sysFlagReg n m k).extractIndex_replaceIndex_of_disjoint
    _ (QRegister.disjoint_comm.mp (sysWorkReg_disjoint_sysFlagReg n m k))]
@[simp] lemma replaceIndex_sysFlagReg_mkSysState (n m k : ℕ) (y : Fin (2 ^ (k * n))) (w : Fin (2 ^
    (m * (n + 1)))) (f f' : Fin (2 ^ 1)) : (sysFlagReg n m k).replaceIndex (mkSysState n m k y w
    f) f' = mkSysState n m k y w f' := by
  apply sysState_ext <;> simp [(sysOutReg n m k).extractIndex_replaceIndex_of_disjoint _
    (sysOutReg_disjoint_sysFlagReg n m k), (sysWorkReg n m k).extractIndex_replaceIndex_of_disjoint
    _ (sysWorkReg_disjoint_sysFlagReg n m k)]
lemma sum_fin_two_pow_one_matrix {D : ℕ} (f : Fin (2 ^ 1) → Matrix (Fin D) (Fin D) ℂ) : (∑ b : Fin
    (2 ^ 1), f b) = f 0 + f 1 := Fin.sum_univ_two f
/-!
### 2.2 Permutations, Slot Packing, and Tracing `sysTrialUnitary`
-/
lemma extractIndex_localSlotReg_foldr (n m : ℕ) (slots : Fin m → Fin (2 ^ (n + 1))) (j : Fin m) (L :
    List (Fin m)) (acc : Fin (2 ^ (m * (n + 1)))) (hj : j ∈ L) : (localSlotReg n m
    j).extractIndex (L.foldr (fun j' a ↦ (localSlotReg n m j').replaceIndex a (slots j')) acc) =
    slots j := by
  induction L with
  | nil => cases hj
  | cons j' rest ih =>
      dsimp only [List.foldr_cons]; rcases eq_or_ne j j' with rfl | hjj
      · exact (localSlotReg n m j).extractIndex_replaceIndex _ _
      · rw [(localSlotReg n m j).extractIndex_replaceIndex_of_disjoint _
          (localSlotReg_disjoint n m hjj)]; exact ih (List.mem_of_ne_of_mem hjj hj)
@[simp] lemma extractIndex_localSlotReg_packWorkSlots (n m : ℕ) (slots : Fin m → Fin (2 ^ (n + 1)))
    (j : Fin m) : (localSlotReg n m j).extractIndex (packWorkSlots n m slots) = slots j :=
    extractIndex_localSlotReg_foldr n m slots j (List.finRange m) 0 (List.mem_finRange j)
lemma sum_normSq_multiTargetState (B : ℕ) [NeZero B] (M : Finset (Fin B)) (K : ℕ) : (∑ i : Fin B,
    Complex.normSq (multiTargetState B M K i)) = 1 := by
  induction K with
  | zero =>
      have hB : 0 < (B : ℝ) := by exact_mod_cast NeZero.pos B
      simp only [multiTargetState, Complex.normSq_ofReal, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hne := (Real.sqrt_pos.2 hB).ne'; field_simp; exact (Real.sq_sqrt hB.le).symm
  | succ K ih =>
      change (∑ i : Fin B, Complex.normSq (((setDiffuserUnitary B).1 *ᵥ (setOracleUnitary B M).1 *ᵥ
        multiTargetState B M K) i)) = 1
      rw [sum_normSq_unitary_mulVec (setDiffuserUnitary B), sum_normSq_unitary_mulVec
        (setOracleUnitary B M), ih]
/-!
### 2.3 Collision-Free Bucket Characterization (`GoodTargetSet`) & Retry Expectation
-/
/-!
## Stage-to-Stage Correctness and Total Correctness (`0` sorries)
-/
@[simp] lemma s20_extractIndex_zero {w Q : ℕ} (r : QRegister w Q) : r.extractIndex 0 = 0 := by
  apply (basisBits w).injective; funext i; simp [r.basisBits_extractIndex, basisBits_eq_div_mod]
/-!
## 1. Unconditional Single-Trial `CostBound` (`parallelBucketTrial_costBound`, `0` sorries)
-/
/-!
## 2. Helper Lemmas for Guarded Bucket Trials and Geometric Sums
-/
/-!
## 1. Stroboscopic Bucket Evolution and 8-15-17 Nonunitary Damping Operator
-/
/-- Parametric bucket state vector on `Fin B` after `K` coherent Grover steps starting from
  an
  arbitrary initial state vector `v₀: Fin B → ℂ`. -/
noncomputable def stroboscopicGroverState (B : ℕ) (M : Finset (Fin B)) (v₀ : Fin B → ℂ) : ℕ → Fin B
    → ℂ
  | 0 => v₀
  | k + 1 => setDiffuserMatrix B *ᵥ setOracleMatrix B M *ᵥ stroboscopicGroverState B M v₀ k
/-- Universal 2-parameter invariant recurrence for `stroboscopicGroverState`: `K` Grover
  steps
  rotate `(c₀, s₀)` by `2 * K * θ` in `SO(2)` and preserve the `ℓ₂` norm squared. -/
theorem stroboscopicGroverState_invariants (B : ℕ) [NeZero B] (M : Finset (Fin B)) (hM : 1 ≤ M.card)
    (v₀ : Fin B → ℂ) (c₀ s₀ : ℝ) (hmark₀ : ∀ i ∈ M, v₀ i = ((1 / √(M.card : ℝ)) * s₀ : ℝ)) (hsum₀ :
    ∑ i : Fin B, v₀ i = (√(B : ℝ) * (c₀ * Real.cos (halfAngleReal ((B : ℝ) / (M.card : ℝ))) + s₀ *
    Real.sin (halfAngleReal ((B : ℝ) / (M.card : ℝ)))) : ℝ)) (K : ℕ) :
    let θ := halfAngleReal ((B : ℝ) / (M.card : ℝ))
    let sK := c₀ * Real.sin (2 * (K : ℝ) * θ) + s₀ * Real.cos (2 * (K : ℝ) * θ)
    let cK := c₀ * Real.cos (2 * (K : ℝ) * θ) - s₀ * Real.sin (2 * (K : ℝ) * θ)
    (∀ i ∈ M, stroboscopicGroverState B M v₀ K i = ((1 / √(M.card : ℝ)) * sK : ℝ)) ∧
    (∑ i : Fin B, stroboscopicGroverState B M v₀ K i = (√(B : ℝ) * (cK * Real.cos θ + sK * Real.sin
      θ) : ℝ)) ∧
    (∑ i : Fin B, Complex.normSq (stroboscopicGroverState B M v₀ K i)) = ∑ i : Fin B, Complex.normSq
      (v₀ i) := by
  induction K with
  | zero =>
      exact ⟨fun i hi ↦ by simpa [stroboscopicGroverState] using hmark₀ i hi,
        by simpa [stroboscopicGroverState] using hsum₀, rfl⟩
  | succ k ih =>
      rcases ih with ⟨hmark, hsum, hnorm⟩
      rcases groverStep_mark_and_sum hM hmark hsum with ⟨hm', hs'⟩
      let θ := halfAngleReal ((B : ℝ) / (M.card : ℝ)); let α := 2 * (k : ℝ) * θ
      let β := 2 * ((k + 1 : ℕ) : ℝ) * θ; have hsc := Real.sin_sq_add_cos_sq θ
      let sk := c₀ * Real.sin α + s₀ * Real.cos α; let ck := c₀ * Real.cos α - s₀ * Real.sin α
      let sk1 := c₀ * Real.sin β + s₀ * Real.cos β; let ck1 := c₀ * Real.cos β - s₀ * Real.sin β
      have hang : β = α + 2 * θ := by dsimp [α, β]; push_cast; ring
      have hsk1 : sk1 = sk * Real.cos (2 * θ) + ck * Real.sin (2 * θ) := by
        dsimp only [sk1, sk, ck]; rw [hang, Real.sin_add, Real.cos_add]; ring
      have hck1 : ck1 = ck * Real.cos (2 * θ) - sk * Real.sin (2 * θ) := by
        dsimp only [ck1, sk, ck]; rw [hang, Real.sin_add, Real.cos_add]; ring
      have hs_eq : ck * Real.cos θ + sk * Real.sin θ - 2 * Real.sin θ * sk =
          ck1 * Real.cos θ + sk1 * Real.sin θ := by
        rw [hck1, hsk1, Real.sin_two_mul, Real.cos_two_mul']
        linear_combination -(ck * Real.cos θ - sk * Real.sin θ) * hsc
      have hm_eq : 2 * Real.sin θ * (ck * Real.cos θ + sk * Real.sin θ - 2 * Real.sin θ * sk) +
          sk = sk1 := by
        rw [hsk1, Real.sin_two_mul, Real.cos_two_mul']; linear_combination -sk * hsc
      refine ⟨fun i hi ↦ (hm' i hi).trans (congrArg (fun x : ℝ ↦ ((1 / √(M.card : ℝ) * x : ℝ) : ℂ))
        hm_eq), hs'.trans (congrArg (fun x : ℝ ↦ ((√(B : ℝ) * x : ℝ) : ℂ)) hs_eq), ?_⟩
      change (∑ i : Fin B, Complex.normSq (((setDiffuserUnitary B).1 *ᵥ (setOracleUnitary B M).1 *ᵥ
        stroboscopicGroverState B M v₀ k) i)) = _
      rw [sum_normSq_unitary_mulVec (setDiffuserUnitary B), sum_normSq_unitary_mulVec
        (setOracleUnitary B M), hnorm]
/-!
## 2. 8-15-17 Zeno Slot Ancilla Unitary and System Pre/Post-Oracle Steps
-/
/-- Address-conditioned ancilla reflection matrix on `Fin (2 ^ (n + 1))`:
  applies `H` on `slotAddr u ∈ F`
  and the Euclid `(1, 4)` reflection `(1 / √17) [[4, 1], [1, -4]]` on `slotAddr u ∉ F`. -/
noncomputable def zenoSlotAncMatrix (n : ℕ) (F : Finset (Fin (2 ^ n))) : Matrix (Fin (2 ^ (n +
    1))) (Fin (2 ^ (n + 1))) ℂ := Matrix.of fun u v ↦ if slotAddr u =
    slotAddr v then if slotAddr u ∈ F then (1 / √2 : ℂ) * (if slotBit u = 1 ∧ slotBit v = 1 then -1
    else 1) else (1 / √5 : ℂ) * (if slotBit u = 0 ∧ slotBit v = 0 then 2 else if slotBit u = 1 ∧
    slotBit v = 1 then -2 else 1) else 0
@[simp]
lemma zenoSlotAncMatrix_apply {n : ℕ} (F : Finset (Fin (2 ^ n))) (u v : Fin (2 ^ (n + 1))) :
    zenoSlotAncMatrix n F u v = if slotAddr u = slotAddr v then if slotAddr u ∈ F then (1 / √2 :
    ℂ) * (if slotBit u = 1 ∧ slotBit v = 1 then -1 else 1) else (1 / √5 : ℂ) * (if slotBit u = 0 ∧
    slotBit v = 0 then 2 else if slotBit u = 1 ∧ slotBit v = 1 then -2 else 1) else 0 := rfl
@[simp] lemma zenoSlotAncMatrix_conjTranspose (n : ℕ) (F : Finset (Fin (2 ^ n))) :
    (zenoSlotAncMatrix n F)ᴴ = zenoSlotAncMatrix n F := by
  ext u v; simp only [zenoSlotAncMatrix_apply, Matrix.conjTranspose_apply]
  by_cases h : slotAddr v = slotAddr u
  · rw [ite_eq_left h, ite_eq_left h.symm, h]
    rcases fin2_eq_zero_or_one (slotBit u) with hu | hu <;>
      rcases fin2_eq_zero_or_one (slotBit v) with hv | hv <;>
      by_cases hF : slotAddr u ∈ F <;> simp [hu, hv, hF]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), star_zero]
/-!
## 1. Reusable Single Zeno-Grover Pulse and 22-Horizon Pentadic Stroboscopic Cascade
-/
/-!
## 2. Recursive Stroboscopic Amplitudes, Cumulative Discovery Probabilities, and Survival Sums
-/
/-- Recursive stroboscopic `(marked, unmarked)` amplitude pair `(a_r, b_r)`
  before damping at pulse `r`. -/
noncomputable def zenoAmpPair (K₁ K₂ : ℕ) (c : ℝ) : ℕ → ℝ × ℝ
  | 0 =>
      (Real.sin ((2 * (K₁ : ℝ) + 1) * halfAngleReal c), Real.cos ((2 * (K₁ : ℝ) + 1) * halfAngleReal
        c))
  | r + 1 =>
      let p := zenoAmpPair K₁ K₂ c r
      let θ := halfAngleReal c
      (p.2 * Real.sin (2 * (K₂ : ℝ) * θ) + (4 / 5 : ℝ) * p.1 * Real.cos (2 * (K₂ : ℝ) * θ), p.2 *
        Real.cos (2 * (K₂ : ℝ) * θ) - (4 / 5 : ℝ) * p.1 * Real.sin (2 * (K₂ : ℝ) * θ))
/-- Marked amplitude `a_r` at stroboscopic pulse `r`. -/
noncomputable def zenoAmpA (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : ℝ := (zenoAmpPair K₁ K₂ c r).1
/-- Unmarked amplitude `b_r` at stroboscopic pulse `r`. -/
noncomputable def zenoAmpB (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : ℝ := (zenoAmpPair K₁ K₂ c r).2
@[simp]
lemma zenoAmpA_zero (K₁ K₂ : ℕ) (c : ℝ) : zenoAmpA K₁ K₂ c 0 = Real.sin ((2 * (K₁ : ℝ) + 1) *
    halfAngleReal c) := rfl
@[simp] lemma zenoAmpB_zero (K₁ K₂ : ℕ) (c : ℝ) : zenoAmpB K₁ K₂ c 0 = Real.cos ((2 * (K₁ : ℝ) + 1)
    * halfAngleReal c) := rfl
lemma zenoAmpA_succ (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : zenoAmpA K₁ K₂ c (r + 1) = zenoAmpB K₁ K₂ c r *
    Real.sin (2 * (K₂ : ℝ) * halfAngleReal c) + (4 / 5 : ℝ) * zenoAmpA K₁ K₂ c r * Real.cos (2 * (K₂
    : ℝ) * halfAngleReal c) := rfl
lemma zenoAmpB_succ (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : zenoAmpB K₁ K₂ c (r + 1) = zenoAmpB K₁ K₂ c r *
    Real.cos (2 * (K₂ : ℝ) * halfAngleReal c) - (4 / 5 : ℝ) * zenoAmpA K₁ K₂ c r * Real.sin (2 * (K₂
    : ℝ) * halfAngleReal c) := rfl
/-- Discovery probability `(9 / 25) * a_r ^ 2` extracted at stroboscopic pulse `r`. -/
noncomputable def zenoStagePSucc (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : ℝ := (9 / 25 : ℝ) *
    zenoAmpA K₁ K₂ c r ^ 2
/-- Cumulative discovery probability after pulse `0` and `r` mid-pulses. -/
noncomputable def zenoCumProb (K₁ K₂ : ℕ) (c : ℝ) : ℕ → ℝ
  | 0 => zenoStagePSucc K₁ K₂ c 0
  | r + 1 => zenoCumProb K₁ K₂ c r + zenoStagePSucc K₁ K₂ c (r + 1)
@[simp]
lemma zenoCumProb_zero (K₁ K₂ : ℕ) (c : ℝ) : zenoCumProb K₁ K₂ c 0 = zenoStagePSucc K₁ K₂ c 0 := rfl
lemma zenoCumProb_succ (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : zenoCumProb K₁ K₂ c (r + 1) =
    zenoCumProb K₁ K₂ c r + zenoStagePSucc K₁ K₂ c (r + 1) := rfl
/-- Sum of survival probabilities `∑_{j=0}^{r-1} (1 - zenoCumProb K₁ K₂ c j)`
  across `r` mid-pulses. -/
noncomputable def zenoSurvSum (K₁ K₂ : ℕ) (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 => zenoSurvSum K₁ K₂ c r + (1 - zenoCumProb K₁ K₂ c r)
@[simp]
lemma zenoSurvSum_zero (K₁ K₂ : ℕ) (c : ℝ) : zenoSurvSum K₁ K₂ c 0 = 0 := rfl
lemma zenoSurvSum_succ (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : zenoSurvSum K₁ K₂ c (r + 1) =
    zenoSurvSum K₁ K₂ c r + (1 - zenoCumProb K₁ K₂ c r) := rfl
/-- Marked amplitude at the terminal projective verification pulse (after 20 mid-pulses). -/
noncomputable def zenoTermAmpA (K₁ K₂ K₃ : ℕ) (c : ℝ) : ℝ :=
  let θ := halfAngleReal c
  zenoAmpB K₁ K₂ c 20 * Real.sin (2 * (K₃ : ℝ) * θ) + (4 / 5 : ℝ) * zenoAmpA K₁ K₂ c 20 * Real.cos
    (2 * (K₃ : ℝ) * θ)
/-- Unmarked amplitude at the terminal projective verification pulse (after 20 mid-pulses). -/
noncomputable def zenoTermAmpB (K₁ K₂ K₃ : ℕ) (c : ℝ) : ℝ :=
  let θ := halfAngleReal c
  zenoAmpB K₁ K₂ c 20 * Real.cos (2 * (K₃ : ℝ) * θ) - (4 / 5 : ℝ) * zenoAmpA K₁ K₂ c 20 * Real.sin
    (2 * (K₃ : ℝ) * θ)
/-- Terminal projective discovery probability `zenoTermAmpA ^ 2`. -/
noncomputable def zenoTermPSucc (K₁ K₂ K₃ : ℕ) (c : ℝ) : ℝ := zenoTermAmpA K₁ K₂ K₃ c ^ 2
/-- Total single-cycle discovery probability across all 22 horizons. -/
noncomputable def p_zeno_real (K₁ K₂ K₃ : ℕ) (c : ℝ) : ℝ := zenoCumProb K₁ K₂ c 20 +
    zenoTermPSucc K₁ K₂ K₃ c
lemma s22_rot_sq_add_sq (c a α : ℝ) : (c * Real.sin α + a * Real.cos α) ^ 2 + (c * Real.cos α - a *
    Real.sin α) ^ 2 = c ^ 2 + a ^ 2 := by
  linear_combination (c ^ 2 + a ^ 2) * Real.sin_sq_add_cos_sq α
lemma one_sub_zenoCumProb_eq_sq (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : 1 - zenoCumProb K₁ K₂ c r =
    zenoAmpB K₁ K₂ c r ^ 2 + ((4 / 5 : ℝ) * zenoAmpA K₁ K₂ c r) ^ 2 := by
  induction r with
  | zero =>
      dsimp only [zenoCumProb, zenoStagePSucc, zenoAmpA, zenoAmpB, zenoAmpPair]
      linarith [Real.sin_sq_add_cos_sq ((2 * (K₁ : ℝ) + 1) * halfAngleReal c)]
  | succ r ih =>
      have hrot : zenoAmpA K₁ K₂ c (r + 1) ^ 2 + zenoAmpB K₁ K₂ c (r + 1) ^ 2 =
        zenoAmpB K₁ K₂ c r ^ 2 + ((4 / 5 : ℝ) * zenoAmpA K₁ K₂ c r) ^ 2 := s22_rot_sq_add_sq _ _ _
      rw [zenoCumProb_succ, zenoStagePSucc]; linarith [ih, hrot]
lemma one_sub_zenoCumProb_nonneg (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : 0 ≤ 1 - zenoCumProb K₁ K₂ c r := by
  rw [one_sub_zenoCumProb_eq_sq]; positivity
lemma zenoCumProb_nonneg (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : 0 ≤ zenoCumProb K₁ K₂ c r := by
  induction r with
  | zero => dsimp [zenoCumProb, zenoStagePSucc]; positivity
  | succ r ih => rw [zenoCumProb_succ, zenoStagePSucc]; positivity
lemma zenoSurvSum_nonneg (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : 0 ≤ zenoSurvSum K₁ K₂ c r := by
  induction r with
  | zero => simp
  | succ r ih => rw [zenoSurvSum_succ]; linarith [one_sub_zenoCumProb_nonneg K₁ K₂ c r]
lemma one_sub_p_zeno_real_eq_sq (K₁ K₂ K₃ : ℕ) (c : ℝ) : 1 - p_zeno_real K₁ K₂ K₃ c =
    zenoTermAmpB K₁ K₂ K₃ c ^ 2 := by
  have hterm : zenoTermAmpA K₁ K₂ K₃ c ^ 2 + zenoTermAmpB K₁ K₂ K₃ c ^ 2 = zenoAmpB K₁ K₂ c 20 ^ 2 +
    ((4 / 5 : ℝ) * zenoAmpA K₁ K₂ c 20) ^ 2 := s22_rot_sq_add_sq _ _ _
  dsimp only [p_zeno_real, zenoTermPSucc]; linarith [one_sub_zenoCumProb_eq_sq K₁ K₂ c 20, hterm]
lemma p_zeno_real_nonneg (K₁ K₂ K₃ : ℕ) (c : ℝ) : 0 ≤ p_zeno_real K₁ K₂ K₃ c := by
  dsimp [p_zeno_real, zenoTermPSucc]; have hc := zenoCumProb_nonneg K₁ K₂ c 20; positivity
lemma p_zeno_real_le_one (K₁ K₂ K₃ : ℕ) (c : ℝ) : p_zeno_real K₁ K₂ K₃ c ≤ 1 := by
  nlinarith [one_sub_p_zeno_real_eq_sq K₁ K₂ K₃ c, sq_nonneg (zenoTermAmpB K₁ K₂ K₃ c)]
lemma zenoCumProb_zero_le (K₁ K₂ : ℕ) (c : ℝ) (r : ℕ) : zenoCumProb K₁ K₂ c 0 ≤
    zenoCumProb K₁ K₂ c r := by
  induction r with
  | zero => exact le_rfl
  | succ r h => rw [zenoCumProb_succ, zenoStagePSucc]; linarith [sq_nonneg (zenoAmpA K₁ K₂ c (r+1))]
/-!
## 3. Losslessness, Cost Bounds, and `threeHorizonZenoTrial_onFiber_split`
-/
end
end Sec_ThreeHorizonZenoCascade
section Sec_QuarticOccupancyMarkov
section
open Operator QProg
open scoped Matrix
private theorem wp_measureRegister_coe {Var : Type} [DecidableEq Var] {n k : ℕ}
    (res : Var) (r : QRegister k n) (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) :
    (wp (QProg.measureRegister res r) Θ σ).1 = ∑ o : Fin (2 ^ k),
        HermitianMat.conj (r.basisOutcomeProjector o)ᴴ (Θ (Store.subst σ res ↑o.val)).1 := rfl
end
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
/-- Exact fourth-order binomial occupancy tail polynomial `T_s(w, r, p) = P(|H_w| ≥ s)`
  for `s ∈ {0, 1, 2, 3, 4}`. -/
noncomputable def quarticOccupancyTail (s w r : ℕ) (p : ℝ) : ℝ :=
  match s with
  | 4 =>
      1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) / 6) *
            (1 - ((r : ℝ) - 3) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) / 2) *
          (1 - ((r : ℝ) - 2) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 2) *
          (1 - ((r : ℝ) - 1) / (r : ℝ) * p) ^ w +
        (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 6) *
          (1 - p) ^ w
  | _ => occupancyTail s w r p
private lemma slotDiagExp_subsetCardSumInd_zero {n m k r : ℕ} (hr1 : 1 ≤ r) {S T : Finset (Fin (2 ^
  n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) : quarticSlotDiagExp n m k S T K
  (subsetCardSumInd n m k 0 (S \ T)) = (1 - (multiP_succ K r (2 ^ n) : ℂ)) ^ (activeSlots m k) := by
  have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) (Nat.zero_le r) hTS hr K
  dsimp only at h; change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 0 (S \ T)) = _ at h
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); rw [h, Nat.choose_zero_right];
    push_cast; rw [sub_zero, div_self hr_ne, one_mul, one_mul]
/-- Exact `w`-slot expectation identity `(U_allᴴ · diag(stratumExitInd s (S \ T)) ·
  U_all)_{0,0} =
  quarticOccupancyTail s w r p`
  for all `1 ≤ s ≤ 4`. -/
theorem conj_stratumExitInd_quartic_zero_zero {n m k s r : ℕ} (hs1 : 1 ≤ s) (hs4 : s ≤ 4) (hsr : s ≤
  r) {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) :
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    (U_all.1ᴴ * Matrix.diagonal (stratumExitInd n m k s (S \ T)) * U_all.1) 0 0 =
      (quarticOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n)) : ℂ) := by
  change quarticSlotDiagExp n m k S T K (stratumExitInd n m k s (S \ T)) = _; have hr1 : 1 ≤ r :=
    hs1.trans hsr; have hself : quarticSlotDiagExp n m k S T K (validAllInd n m k (S \ T)) = 1 :=
    conj_validAllInd_self_zero_zero hTS K; have h0 := slotDiagExp_subsetCardSumInd_zero (m := m) (k
    := k) hr1 hTS hr K
  have h1 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 1 (S \ T)) = (r : ℂ) * (1 - ((r :
    ℝ) - 1) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
    have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr1 hTS hr K; dsimp only at h
    change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 1 (S \ T)) = _ at h; rw [h,
      Nat.choose_one_right]; congr 2; push_cast; rfl
  rcases s with _ | _ | _ | _ | _ | s
  · omega
  · have hfun : stratumExitInd n m k 1 (S \ T) = fun o ↦ validAllInd n m k (S \ T) o -
      subsetCardSumInd n m k 0 (S \ T) o := funext (quartic_stratumExitInd_decomp_one n m k (S \ T))
    rw [hfun, quarticSlotDiagExp_sub, hself, h0]; simp only [quarticOccupancyTail, occupancyTail]
    push_cast; ring
  · have hfun : stratumExitInd n m k 2 (S \ T) = fun o ↦ (validAllInd n m k (S \ T) o -
      subsetCardSumInd n m k 1 (S \ T) o) + (((S \ T).card : ℂ) - 1) * subsetCardSumInd n m k 0 (S \
      T) o := funext (quartic_stratumExitInd_decomp_two n m k (S \ T)); rw [hfun,
      quarticSlotDiagExp_add, quarticSlotDiagExp_sub, quarticSlotDiagExp_const_mul, hself, h1, h0,
      hr]; simp only [quarticOccupancyTail, occupancyTail]; push_cast; ring
  · have hr2 : 2 ≤ r := (by omega)
    have h2 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 2 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) / 2) * (1 - ((r : ℝ) - 2) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k)
      := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr2 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 2 (S \ T)) = _ at h; rw [h,
        choose_two_cast_complex r]; congr 2
    have hfun : stratumExitInd n m k 3 (S \ T) = fun o ↦ ((validAllInd n m k (S \ T) o -
      subsetCardSumInd n m k 2 (S \ T) o) + (((S \ T).card : ℂ) - 2) * subsetCardSumInd n m k 1 (S \
      T) o) - ((((S \ T).card : ℂ) - 1) * (((S \ T).card : ℂ) - 2) / 2) * subsetCardSumInd n m k 0
      (S \ T) o := funext (quartic_stratumExitInd_decomp_three n m k (S \ T))
    rw [hfun, quarticSlotDiagExp_sub, quarticSlotDiagExp_add, quarticSlotDiagExp_sub,
      quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul, hself, h2, h1, h0, hr]
    simp only [quarticOccupancyTail, occupancyTail]; push_cast; ring
  · have hr2 : 2 ≤ r := (by omega); have hr3 : 3 ≤ r := (by omega)
    have h2 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 2 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) / 2) * (1 - ((r : ℝ) - 2) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k)
      := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr2 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 2 (S \ T)) = _ at h; rw [h,
        choose_two_cast_complex r]; congr 2
    have h3 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 3 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) * ((r : ℂ) - 2) / 6) * (1 - ((r : ℝ) - 3) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^
      (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr3 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 3 (S \ T)) = _ at h; rw [h,
        choose_three_cast_complex r]; congr 2
    have hfun : stratumExitInd n m k 4 (S \ T) = fun o ↦ (((validAllInd n m k (S \ T) o -
      subsetCardSumInd n m k 3 (S \ T) o) + (((S \ T).card : ℂ) - 3) * subsetCardSumInd n m k 2 (S \
      T) o) - ((((S \ T).card : ℂ) - 2) * (((S \ T).card : ℂ) - 3) / 2) * subsetCardSumInd n m k 1
      (S \ T) o) + ((((S \ T).card : ℂ) - 1) * (((S \ T).card : ℂ) - 2) * (((S \ T).card : ℂ) - 3) /
      6) * subsetCardSumInd n m k 0 (S \ T) o := funext (stratumExitInd_decomp_four n m k (S \ T))
    rw [hfun, quarticSlotDiagExp_add, quarticSlotDiagExp_sub, quarticSlotDiagExp_add,
      quarticSlotDiagExp_sub, quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul,
      quarticSlotDiagExp_const_mul, hself, h3, h2, h1, h0, hr]; simp only [quarticOccupancyTail];
      push_cast; ring
  · omega
/-- Exact Markov recurrence for the fourth-order occupancy tail `quarticOccupancyTail 4`. -/
theorem quarticOccupancyTail_markov_four {w r : ℕ} (hr1 : 1 ≤ r) (p : ℝ) :
    let α : ℝ := ((r : ℝ) - 3) / (r : ℝ)
    quarticOccupancyTail 4 (w + 1) r p = (1 - α * p) * quarticOccupancyTail 4 w r p + α * p *
      occupancyTail 3 w r p := by
  intro α; have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hr1))
  simp only [quarticOccupancyTail, occupancyTail, α]; rw [pow_succ, pow_succ, pow_succ, pow_succ]
  field_simp [hr_ne]; ring
private lemma second_diff_pow_nonneg_m02 {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (w : ℕ) : 0 ≤ (a + 2 *
  δ) ^ w - 2 * (a + δ) ^ w + a ^ w := by
  induction w with
  | zero => norm_num
  | succ w ih =>
    have hpow : a ^ w ≤ (a + 2 * δ) ^ w := pow_le_pow_left₀ ha (by linarith) w; have hid : (a + 2 *
      δ) ^ (w + 1) - 2 * (a + δ) ^ (w + 1) + a ^ (w + 1) = (a + δ) * ((a + 2 * δ) ^ w - 2 * (a + δ)
      ^ w + a ^ w) + δ * ((a + 2 * δ) ^ w - a ^ w) := (by ring); rw [hid]; nlinarith
/-- Non-negativity of third-order finite differences of `x ↦ x ^ w` on `[0, ∞)`. -/
theorem third_diff_pow_nonneg {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (w : ℕ) : 0 ≤ (a + 3 * δ) ^ w - 3
  * (a + 2 * δ) ^ w + 3 * (a + δ) ^ w - a ^ w := by
  induction w with
  | zero => norm_num
  | succ w ih =>
    have hsec := second_diff_pow_nonneg_m02 ha hδ w; have hid : (a + 3 * δ) ^ (w + 1) - 3 * (a + 2 *
      δ) ^ (w + 1) + 3 * (a + δ) ^ (w + 1) - a ^ (w + 1) = (a + 3 * δ) * ((a + 3 * δ) ^ w - 3 * (a +
      2 * δ) ^ w + 3 * (a + δ) ^ w - a ^ w) + 3 * δ * ((a + 2 * δ) ^ w - 2 * (a + δ) ^ w + a ^ w) :=
      (by ring); rw [hid]; nlinarith
/-- Monotonicity in stride order: `quarticOccupancyTail 4 w r p ≤ occupancyTail 3 w r p`. -/
theorem quarticOccupancyTail_four_le_three {w r : ℕ} (hr4 : 4 ≤ r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤
  1) : quarticOccupancyTail 4 w r p ≤ occupancyTail 3 w r p := by
  have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r)); have hr_ne : (r : ℝ) ≠ 0 :=
    hr_pos.ne'; simp only [quarticOccupancyTail, occupancyTail]
  let a : ℝ := 1 - p; let δ : ℝ := p / (r : ℝ)
  have ha1 : 1 - ((r : ℝ) - 1) / (r : ℝ) * p = a + δ := (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha2 : 1 - ((r : ℝ) - 2) / (r : ℝ) * p = a + 2 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha3 : 1 - ((r : ℝ) - 3) / (r : ℝ) * p = a + 3 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring); have ha0 : 1 - p = a := rfl; rw [ha1, ha2, ha3,
    ha0]; have hr4_r : (4 : ℝ) ≤ r := (by exact_mod_cast hr4)
  have hcoeff : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) / 6 := by
    have : 0 ≤ (r : ℝ) - 1 := (by linarith); have : 0 ≤ (r : ℝ) - 2 := (by linarith); positivity
  have htd := third_diff_pow_nonneg (a := a) (δ := δ) (by dsimp [a]; linarith) (div_nonneg hp0
    hr_pos.le) w; have hid : (1 - (r : ℝ) * ((r : ℝ) - 1) / 2 * (a + 2 * δ) ^ w + (r : ℝ) * ((r : ℝ)
    - 2) * (a + δ) ^ w - ((r : ℝ) - 1) * ((r : ℝ) - 2) / 2 * a ^ w) - (1 - (r : ℝ) * ((r : ℝ) - 1) *
    ((r : ℝ) - 2) / 6 * (a + 3 * δ) ^ w + (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) / 2 * (a + 2 * δ)
    ^ w - (r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 2 * (a + δ) ^ w + ((r : ℝ) - 1) * ((r : ℝ) - 2)
    * ((r : ℝ) - 3) / 6 * a ^ w) = ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) / 6) * ((a + 3 * δ) ^ w
    - 3 * (a + 2 * δ) ^ w + 3 * (a + δ) ^ w - a ^ w) := (by ring)
  have hprod : 0 ≤ ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) / 6) * ((a + 3 * δ) ^ w - 3 * (a + 2 *
    δ) ^ w + 3 * (a + δ) ^ w - a ^ w) := mul_nonneg hcoeff htd; linarith
private lemma occupancyTail_three_nonneg_and_le_one {w r : ℕ} (hr3 : 3 ≤ r) {p : ℝ} (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) : 0 ≤ occupancyTail 3 w r p ∧ occupancyTail 3 w r p ≤ 1 := by
  rcases eq_or_lt_of_le hp0 with rfl | hp_pos
  · have h0 : occupancyTail 3 w r 0 = 0 :=
      (by simp only [occupancyTail, mul_zero, sub_zero, one_pow]; ring); rw [h0]; exact ⟨le_rfl,
      zero_le_one⟩
  · rcases lt_or_ge w 3 with hwlt | hw3
    · have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (by omega : r ≠ 0)); interval_cases w
      · have h0 : occupancyTail 3 0 r p = 0 := (by simp only [occupancyTail, pow_zero]; ring)
        rw [h0]; exact ⟨le_rfl, zero_le_one⟩
      · have h1 : occupancyTail 3 1 r p = 0 :=
          (by simp only [occupancyTail, pow_one]; field_simp [hr_ne]; ring); rw [h1]; exact ⟨le_rfl,
          zero_le_one⟩
      · have h2 : occupancyTail 3 2 r p = 0 :=
          (by simp only [occupancyTail]; field_simp [hr_ne]; ring); rw [h2]; exact ⟨le_rfl,
          zero_le_one⟩
    · rcases occupancyTail_pos_and_mono (s := 3) (w := w) (r := r) (by omega) (by omega) hw3 hr3
        hp_pos le_rfl hp1 with ⟨hpos, _, hle1⟩; exact ⟨hpos.le, hle1⟩
private lemma occupancyTail_three_mono {w r : ℕ} (hr3 : 3 ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁
  ≤ p₂) (hp2 : p₂ ≤ 1) : occupancyTail 3 w r p₁ ≤ occupancyTail 3 w r p₂ := by
  rcases lt_or_ge w 3 with hwlt | hw3
  · interval_cases w
    · have h0 (p : ℝ) : occupancyTail 3 0 r p = 0 := (by simp only [occupancyTail, pow_zero]; ring)
      rw [h0, h0]
    · have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (by omega : r ≠ 0))
      have h1 (p : ℝ) : occupancyTail 3 1 r p = 0 :=
        (by simp only [occupancyTail, pow_one]; field_simp [hr_ne]; ring); rw [h1, h1]
    · have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (by omega : r ≠ 0))
      have h2 (p : ℝ) : occupancyTail 3 2 r p = 0 :=
        (by simp only [occupancyTail]; field_simp [hr_ne]; ring); rw [h2, h2]
  · exact (occupancyTail_pos_and_mono (by omega) (by omega) hw3 hr3 hp1 hp12 hp2).2.1
private lemma quarticOccupancyTail_four_nonneg {w r : ℕ} (hr4 : 4 ≤ r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 :
  p ≤ 1) : 0 ≤ quarticOccupancyTail 4 w r p := by
  have hr1 : 1 ≤ r := (by omega); have hr3 : 3 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr4_r : (4 : ℝ) ≤ r := (by exact_mod_cast hr4)
  let α : ℝ := ((r : ℝ) - 3) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
  have hαp0 : 0 ≤ α * p := mul_nonneg hα0 hp0; have hαp1 : α * p ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 : quarticOccupancyTail 4 0 r p = 0 :=
      (by simp only [quarticOccupancyTail, pow_zero]; ring); rw [h0]
  | succ w ih =>
    have hm := quarticOccupancyTail_markov_four (w := w) hr1 p; dsimp only at hm
    change quarticOccupancyTail 4 (w + 1) r p = (1 - α * p) * quarticOccupancyTail 4 w r p + α * p *
      occupancyTail 3 w r p at hm; rw [hm]; have h3_0 := (occupancyTail_three_nonneg_and_le_one (w
      := w) hr3 hp0 hp1).1; nlinarith
private lemma quarticOccupancyTail_four_nonneg_and_le_one {w r : ℕ} (hr4 : 4 ≤ r) {p : ℝ} (hp0 : 0 ≤
  p) (hp1 : p ≤ 1) : 0 ≤ quarticOccupancyTail 4 w r p ∧ quarticOccupancyTail 4 w r p ≤ 1 :=
  ⟨quarticOccupancyTail_four_nonneg hr4 hp0 hp1, (quarticOccupancyTail_four_le_three hr4 hp0
    hp1).trans (occupancyTail_three_nonneg_and_le_one (by omega) hp0 hp1).2⟩
private lemma quarticOccupancyTail_four_mono {w r : ℕ} (hr4 : 4 ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁)
  (hp12 : p₁ ≤ p₂) (hp2 : p₂ ≤ 1) : quarticOccupancyTail 4 w r p₁ ≤ quarticOccupancyTail 4 w r p₂ :=
  by
  have hr1 : 1 ≤ r := (by omega); have hr3 : 3 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr4_r : (4 : ℝ) ≤ r := (by exact_mod_cast hr4)
  let α : ℝ := ((r : ℝ) - 3) / (r : ℝ)
  have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith); have hp2_0 : 0 ≤ p₂ := hp1.le.trans hp12;
    have hαp2_0 : 0 ≤ α * p₂ := mul_nonneg hα0 hp2_0; have hαp2_1 : α * p₂ ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 (p : ℝ) : quarticOccupancyTail 4 0 r p = 0 :=
      (by simp only [quarticOccupancyTail, pow_zero]; ring); rw [h0, h0]
  | succ w ih =>
    have hm1 := quarticOccupancyTail_markov_four (w := w) hr1 p₁; have hm2 :=
      quarticOccupancyTail_markov_four (w := w) hr1 p₂; dsimp only at hm1 hm2
    change quarticOccupancyTail 4 (w + 1) r p₁ = (1 - α * p₁) * quarticOccupancyTail 4 w r p₁ + α *
      p₁ * occupancyTail 3 w r p₁ at hm1
    change quarticOccupancyTail 4 (w + 1) r p₂ = (1 - α * p₂) * quarticOccupancyTail 4 w r p₂ + α *
      p₂ * occupancyTail 3 w r p₂ at hm2; rw [hm1, hm2]; have h3_mono := occupancyTail_three_mono (w
      := w) hr3 hp1 hp12 hp2
    have h4_le_3 := quarticOccupancyTail_four_le_three (w := w) hr4 hp1.le (hp12.trans hp2)
    have hid : ((1 - α * p₂) * quarticOccupancyTail 4 w r p₂ + α * p₂ * occupancyTail 3 w r p₂) -
      ((1 - α * p₁) * quarticOccupancyTail 4 w r p₁ + α * p₁ * occupancyTail 3 w r p₁) = (1 - α *
      p₂) * (quarticOccupancyTail 4 w r p₂ - quarticOccupancyTail 4 w r p₁) + α * p₂ *
      (occupancyTail 3 w r p₂ - occupancyTail 3 w r p₁) + α * (p₂ - p₁) * (occupancyTail 3 w r p₁ -
      quarticOccupancyTail 4 w r p₁) := (by ring)
    have ht1 : 0 ≤ (1 - α * p₂) * (quarticOccupancyTail 4 w r p₂ - quarticOccupancyTail 4 w r p₁) :=
      mul_nonneg (by linarith) (by linarith); have ht2 : 0 ≤ α * p₂ * (occupancyTail 3 w r p₂ -
      occupancyTail 3 w r p₁) := mul_nonneg hαp2_0 (by linarith); have ht3 : 0 ≤ α * (p₂ - p₁) *
      (occupancyTail 3 w r p₁ - quarticOccupancyTail 4 w r p₁) := mul_nonneg (mul_nonneg hα0
      (by linarith)) (by linarith); linarith
/-- Positivity, monotonicity in `p ∈ (0, 1]`, and upper bound `≤ 1` for
  `quarticOccupancyTail s w r
  p`
  across all `1 ≤ s ≤ 4`. -/
theorem quarticOccupancyTail_pos_and_mono {s w r : ℕ} (hs1 : 1 ≤ s) (hs4 : s ≤ 4) (hsw : s ≤ w) (hsr
  : s ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤ p₂) (hp2 : p₂ ≤ 1) : 0 < quarticOccupancyTail s w
  r p₁ ∧ quarticOccupancyTail s w r p₁ ≤ quarticOccupancyTail s w r p₂ ∧ quarticOccupancyTail s w r
  p₂ ≤ 1 := by
  rcases lt_or_eq_of_le hs4 with hs3 | rfl
  · have h_eq (p : ℝ) : quarticOccupancyTail s w r p = occupancyTail s w r p := by
      rcases s with _ | _ | _ | _ | s <;> try omega
      all_goals rfl
    rw [h_eq p₁, h_eq p₂]; exact occupancyTail_pos_and_mono hs1 (by omega) hsw hsr hp1 hp12 hp2
  · refine ⟨?_, quarticOccupancyTail_four_mono hsr hp1 hp12 hp2,
      (quarticOccupancyTail_four_nonneg_and_le_one hsr (hp1.le.trans hp12) hp2).2⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0) with ⟨w', rfl⟩; have hr1 : 1 ≤ r :=
      (by omega); have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1); have hr4_r : (4 : ℝ) ≤ r :=
      (by exact_mod_cast hsr)
    let α : ℝ := ((r : ℝ) - 3) / (r : ℝ); have hα_pos : 0 < α := div_pos (by linarith) hr_pos
    have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
    have hp1_le1 : p₁ ≤ 1 := hp12.trans hp2; have hαp_pos : 0 < α * p₁ := mul_pos hα_pos hp1
    have hαp_le1 : α * p₁ ≤ 1 := (by nlinarith); have hm := quarticOccupancyTail_markov_four (w :=
      w') hr1 p₁; dsimp only at hm; change quarticOccupancyTail 4 (w' + 1) r p₁ = (1 - α * p₁) *
      quarticOccupancyTail 4 w' r p₁ + α * p₁ * occupancyTail 3 w' r p₁ at hm; rw [hm]; have h4_0 :=
      quarticOccupancyTail_four_nonneg (w := w') hsr hp1.le hp1_le1; have h3_pos :=
      (occupancyTail_pos_and_mono (s := 3) (w := w') (r := r) (by omega) (by omega) (by omega)
      (by omega) hp1 le_rfl hp1_le1).1; nlinarith
end QuantumComputation.Specs
end
end Sec_QuarticOccupancyMarkov
section Sec_QuarticAttemptHelpers
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
private lemma quartic_unitary_list_prod_val {d : ℕ} (l : List (Unitary d)) : l.prod.1 = (l.map
  Subtype.val).prod := by
  induction l with
  | nil => rfl
  | cons u us ih => exact congrArg (u.1 * ·) ih
private lemma quartic_embedUnitary_prod_val {Q w : ℕ} (U : Unitary (2 ^ w)) (regs : List (QRegister
  w Q)) : ((regs.map fun (r : QRegister w Q) ↦ r.embedUnitary U).prod).1 = embedList regs U.1 := by
  rw [embedList, quartic_unitary_list_prod_val, List.map_map]; rfl
private lemma quartic_unitary_mul_val {d : ℕ} (u v : Unitary d) : (u * v).1 = u.1 * v.1 := rfl
private lemma quartic_embedUnitary_prod_mul {Q w : ℕ} (U V : Unitary (2 ^ w)) (regs : List
  (QRegister w Q)) (hpair : regs.Pairwise QRegister.DisjointWires) : (regs.map fun r ↦
  r.embedUnitary U).prod * (regs.map fun r ↦ r.embedUnitary V).prod = (regs.map fun r ↦
  r.embedUnitary (U * V)).prod := by
  apply Subtype.ext; rw [quartic_unitary_mul_val, quartic_embedUnitary_prod_val,
    quartic_embedUnitary_prod_val, quartic_embedUnitary_prod_val]; exact (embedList_mul_and_diagonal
    U.1 V.1 (fun _ ↦ 0) regs hpair).1
lemma quartic_embedAllSlots_one (n m k : ℕ) : embedAllSlots n m k 1 = 1 := by
  unfold embedAllSlots; induction slotRegList n m k <;> simp
lemma quartic_embedAllSlots_mul (n m k : ℕ) (U V : Unitary (2 ^ (n + 1))) : embedAllSlots n m k (U *
  V) = embedAllSlots n m k U * embedAllSlots n m k V :=
  (quartic_embedUnitary_prod_mul U V (slotRegList n m k) (slotRegList_pairwise_disjoint n m k)).symm
lemma quartic_embedAllSlots_mul_self (n m k : ℕ) {U : Unitary (2 ^ (n + 1))} (hU : U * U = 1) :
  embedAllSlots n m k U * embedAllSlots n m k U = 1 := by
  rw [← quartic_embedAllSlots_mul, hU, quartic_embedAllSlots_one]
lemma quartic_batchOracleReg_embedUnitary_eq (n m k : ℕ) (S : Finset (Fin (2 ^ n))) :
    (batchOracleReg n m k).embedUnitary (groverParallelMarkingOracle (activeSlots m k) S) =
      embedAllSlots n m k (groverSetMarkingOracle S) := batchOracleReg_embedUnitary_eq n m k S
private lemma quartic_conjTranspose_diagonal_mul_apply_zero' {D : ℕ} [NeZero D] (M : Matrix (Fin D)
  (Fin D) ℂ) (d : Fin D → ℂ) : (Mᴴ * Matrix.diagonal d * M) 0 0 = ∑ idx : Fin D, star ((M *ᵥ
  Pi.single 0 1) idx) * d idx * (M *ᵥ Pi.single 0 1) idx := by
  have hcol : ∀ idx, (M *ᵥ Pi.single 0 1) idx = M idx 0 := fun idx ↦ by simp
  simp_rw [hcol]; simp [Matrix.mul_apply, Matrix.diagonal_apply]
lemma quartic_conj_diagonal_mul_valid_eq {D : ℕ} [NeZero D] (U : Unitary D) (v d : Fin D → ℂ) (hv :
  ∀ o, v o = 1 ∨ v o = 0) (h1 : (U.1ᴴ * Matrix.diagonal v * U.1) 0 0 = 1) : (U.1ᴴ * Matrix.diagonal
  d * U.1) 0 0 = (U.1ᴴ * Matrix.diagonal (fun o ↦ d o * v o) * U.1) 0 0 := by
  let ψ : Fin D → ℂ := U.1 *ᵥ Pi.single 0 1
  have hnorm : (U.1ᴴ * Matrix.diagonal (fun _ : Fin D ↦ (1 : ℂ)) * U.1) 0 0 = 1 := by
    have hunit : U.1ᴴ * U.1 = 1 := (by have h := U.2.1; rwa [← Matrix.star_eq_conjTranspose])
    simp [Matrix.diagonal_one, hunit]
  rw [quartic_conjTranspose_diagonal_mul_apply_zero'] at h1 hnorm
  have hdiff : ∑ o : Fin D, (star (ψ o) * (1 : ℂ) * ψ o - star (ψ o) * v o * ψ o) = 0 :=
    (by rw [Finset.sum_sub_distrib, hnorm, h1, sub_self])
  let t : Fin D → ℝ := fun o ↦ (1 - (v o).re) * Complex.normSq (ψ o)
  have ht_eq : ∀ o : Fin D, star (ψ o) * (1 : ℂ) * ψ o - star (ψ o) * v o * ψ o = (t o : ℂ) := by
    intro o; have hconj : star (ψ o) * ψ o = (Complex.normSq (ψ o) : ℂ) :=
      (by rw [mul_comm, Complex.star_def, Complex.mul_conj]); rcases hv o with hvo | hvo
    · simp [t, hvo]
    · rw [hvo, mul_one, mul_zero, zero_mul, sub_zero, hconj]; simp [t, hvo]
  simp_rw [ht_eq] at hdiff; rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at hdiff
  have ht_nonneg : ∀ o ∈ (Finset.univ : Finset (Fin D)), 0 ≤ t o := by
    intro o _; rcases hv o with hvo | hvo <;> simp [t, hvo, Complex.normSq_nonneg]
  have ht_zero := (Finset.sum_eq_zero_iff_of_nonneg ht_nonneg).mp hdiff
  rw [quartic_conjTranspose_diagonal_mul_apply_zero',
    quartic_conjTranspose_diagonal_mul_apply_zero']; refine Finset.sum_congr rfl fun o _ ↦ ?_
  rcases hv o with hvo | hvo
  · rw [hvo, mul_one]
  · have hto := ht_zero o (Finset.mem_univ o); simp only [t, hvo, Complex.zero_re, sub_zero,
      one_mul, Complex.normSq_eq_zero] at hto; change star (ψ o) * d o * ψ o = star (ψ o) * (d o * v
      o) * ψ o; rw [hto, mul_zero, mul_zero]
end QuantumComputation.Specs
end
end Sec_QuarticAttemptHelpers
section Sec_SexticEulerMobiusDecomp
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
/-- Unconditional complex polynomial identity for `Nat.choose m 4`. -/
theorem choose_four_cast_complex (m : ℕ) : (Nat.choose m 4 : ℂ) = (m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ)
  - 2) * ((m : ℂ) - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ m 3]; push_cast; rw [choose_three_cast_complex m, ih]; ring
/-- Unconditional complex polynomial identity for `Nat.choose m 5`. -/
theorem choose_five_cast_complex (m : ℕ) : (Nat.choose m 5 : ℂ) = (m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ)
  - 2) * ((m : ℂ) - 3) * ((m : ℂ) - 4) / 120 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.choose_succ_succ m 4]; push_cast; rw [choose_four_cast_complex m, ih]; ring
/-- Exact fifth-order Boolean-lattice Euler-Mobius character decomposition of
  `stratumExitInd n m k
  5 R`. -/
theorem stratumExitInd_decomp_five (n m k : ℕ) (R : Finset (Fin (2 ^ n))) (o : Fin (2 ^
  findAllQubits n m k)) : stratumExitInd n m k 5 R o = validAllInd n m k R o - subsetCardSumInd n m
  k 4 R o + ((R.card : ℂ) - 4) * subsetCardSumInd n m k 3 R o - (((R.card : ℂ) - 3) * ((R.card : ℂ)
  - 4) / 2) * subsetCardSumInd n m k 2 R o + (((R.card : ℂ) - 2) * ((R.card : ℂ) - 3) * ((R.card :
  ℂ) - 4) / 6) * subsetCardSumInd n m k 1 R o - (((R.card : ℂ) - 1) * ((R.card : ℂ) - 2) * ((R.card
  : ℂ) - 3) * ((R.card : ℂ) - 4) / 24) * subsetCardSumInd n m k 0 R o := by
  by_cases hHR : hitSet n m k o ⊆ R
  · rw [subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset
      hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, true_and]; have hle : (hitSet n m
      k o).card ≤ R.card := Finset.card_le_card hHR; generalize (hitSet n m k o).card = h at hle ⊢
    rcases h with _ | _ | _ | _ | _ | c
    · simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero,
        show ¬ (5 ≤ 0) by omega, Nat.choose_zero_right, Nat.cast_one,
        Nat.choose_one_right, choose_two_cast_complex, choose_three_cast_complex,
        choose_four_cast_complex]; ring
    · simp only [show 1 ≤ 4 by omega, show 1 ≤ 3 by omega, show 1 ≤ 2 by omega,
        show 1 ≤ 1 by omega, show ¬ (1 ≤ 0) by omega, show ¬ (5 ≤ 1) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 4 - 1 = 3 from rfl, show 3 - 1 = 2 from rfl, show 2 - 1 = 1 from rfl,
        choose_three_cast_complex, choose_two_cast_complex, Nat.choose_one_right, Nat.cast_sub hle,
        Nat.cast_one]; ring
    · simp only [show 2 ≤ 4 by omega, show 2 ≤ 3 by omega, show 2 ≤ 2 by omega,
        show ¬ (2 ≤ 1) by omega, show ¬ (2 ≤ 0) by omega, show ¬ (5 ≤ 2) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 4 - 2 = 2 from rfl, show 3 - 2 = 1 from rfl, choose_two_cast_complex,
        Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 3 ≤ 4 by omega, show 3 ≤ 3 by omega, show ¬ (3 ≤ 2) by omega,
        show ¬ (3 ≤ 1) by omega, show ¬ (3 ≤ 0) by omega, show ¬ (5 ≤ 3) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 4 - 3 = 1 from rfl, Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 4 ≤ 4 by omega, show ¬ (4 ≤ 3) by omega, show ¬ (4 ≤ 2) by omega,
        show ¬ (4 ≤ 1) by omega, show ¬ (4 ≤ 0) by omega, show ¬ (5 ≤ 4) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]; ring
    · have h5 : 5 ≤ c + 5 := (by omega); have hn4 : ¬ (c + 5 ≤ 4) := (by omega); have hn3 : ¬ (c + 5
        ≤ 3) := (by omega); have hn2 : ¬ (c + 5 ≤ 2) := (by omega); have hn1 : ¬ (c + 5 ≤ 1) :=
        (by omega); have hn0 : ¬ (c + 5 ≤ 0) := (by omega); simp only [h5, hn4, hn3, hn2, hn1, hn0,
        ↓reduceIte]; ring
  · rw [subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR]; simp only [stratumExitInd, validAllInd_eq_hitSet_subset,
      hHR, false_and, ↓reduceIte]; ring
/-- Exact sixth-order Boolean-lattice Euler-Mobius character decomposition of
  `stratumExitInd n m k
  6 R`. -/
theorem stratumExitInd_decomp_six (n m k : ℕ) (R : Finset (Fin (2 ^ n))) (o : Fin (2 ^ findAllQubits
  n m k)) : stratumExitInd n m k 6 R o = validAllInd n m k R o - subsetCardSumInd n m k 5 R o +
  ((R.card : ℂ) - 5) * subsetCardSumInd n m k 4 R o - (((R.card : ℂ) - 4) * ((R.card : ℂ) - 5) / 2)
  * subsetCardSumInd n m k 3 R o + (((R.card : ℂ) - 3) * ((R.card : ℂ) - 4) * ((R.card : ℂ) - 5) /
  6) * subsetCardSumInd n m k 2 R o - (((R.card : ℂ) - 2) * ((R.card : ℂ) - 3) * ((R.card : ℂ) - 4)
  * ((R.card : ℂ) - 5) / 24) * subsetCardSumInd n m k 1 R o + (((R.card : ℂ) - 1) * ((R.card : ℂ) -
  2) * ((R.card : ℂ) - 3) * ((R.card : ℂ) - 4) * ((R.card : ℂ) - 5) / 120) * subsetCardSumInd n m k
  0 R o := by
  by_cases hHR : hitSet n m k o ⊆ R
  · rw [subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset
      hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR,
      subsetCardSumInd_of_subset hHR]; simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR,
      true_and]; have hle : (hitSet n m k o).card ≤ R.card := Finset.card_le_card hHR
    generalize (hitSet n m k o).card = h at hle ⊢; rcases h with _ | _ | _ | _ | _ | _ | c
    · simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero,
        show ¬ (6 ≤ 0) by omega, Nat.choose_zero_right, Nat.cast_one,
        Nat.choose_one_right, choose_two_cast_complex, choose_three_cast_complex,
        choose_four_cast_complex, choose_five_cast_complex]; ring
    · simp only [show 1 ≤ 5 by omega, show 1 ≤ 4 by omega, show 1 ≤ 3 by omega,
        show 1 ≤ 2 by omega, show 1 ≤ 1 by omega, show ¬ (1 ≤ 0) by omega,
        show ¬ (6 ≤ 1) by omega, ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 5 - 1 = 4 from rfl, show 4 - 1 = 3 from rfl, show 3 - 1 = 2 from rfl, show 2 - 1 = 1
        from rfl, choose_four_cast_complex, choose_three_cast_complex, choose_two_cast_complex,
        Nat.choose_one_right, Nat.cast_sub hle, Nat.cast_one]; ring
    · simp only [show 2 ≤ 5 by omega, show 2 ≤ 4 by omega, show 2 ≤ 3 by omega,
        show 2 ≤ 2 by omega, show ¬ (2 ≤ 1) by omega, show ¬ (2 ≤ 0) by omega,
        show ¬ (6 ≤ 2) by omega, ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 5 - 2 = 3 from rfl, show 4 - 2 = 2 from rfl, show 3 - 2 = 1 from rfl,
        choose_three_cast_complex, choose_two_cast_complex, Nat.choose_one_right, Nat.cast_sub hle]
      push_cast; ring
    · simp only [show 3 ≤ 5 by omega, show 3 ≤ 4 by omega, show 3 ≤ 3 by omega,
        show ¬ (3 ≤ 2) by omega, show ¬ (3 ≤ 1) by omega, show ¬ (3 ≤ 0) by omega,
        show ¬ (6 ≤ 3) by omega, ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 5 - 3 = 2 from rfl, show 4 - 3 = 1 from rfl, choose_two_cast_complex,
        Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 4 ≤ 5 by omega, show 4 ≤ 4 by omega, show ¬ (4 ≤ 3) by omega,
        show ¬ (4 ≤ 2) by omega, show ¬ (4 ≤ 1) by omega, show ¬ (4 ≤ 0) by omega,
        show ¬ (6 ≤ 4) by omega, ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 5 - 4 = 1 from rfl, Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 5 ≤ 5 by omega, show ¬ (5 ≤ 4) by omega, show ¬ (5 ≤ 3) by omega,
        show ¬ (5 ≤ 2) by omega, show ¬ (5 ≤ 1) by omega, show ¬ (5 ≤ 0) by omega,
        show ¬ (6 ≤ 5) by omega, ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      ring
    · have h6 : 6 ≤ c + 6 := (by omega); have hn5 : ¬ (c + 6 ≤ 5) := (by omega); have hn4 : ¬ (c + 6
        ≤ 4) := (by omega); have hn3 : ¬ (c + 6 ≤ 3) := (by omega); have hn2 : ¬ (c + 6 ≤ 2) :=
        (by omega); have hn1 : ¬ (c + 6 ≤ 1) := (by omega); have hn0 : ¬ (c + 6 ≤ 0) := (by omega)
      simp only [h6, hn5, hn4, hn3, hn2, hn1, hn0, ↓reduceIte]; ring
  · rw [subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, false_and, ↓reduceIte]; ring
end QuantumComputation.Specs
end
end Sec_SexticEulerMobiusDecomp
section Sec_SexticOccupancyMarkov
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
/-- Exact sixth-order binomial occupancy tail polynomial `T_s(w, r, p) = P(|H_w| ≥ s)`
  for `s ∈ {0, 1, 2, 3, 4, 5, 6}`. -/
noncomputable def sexticOccupancyTail (s w r : ℕ) (p : ℝ) : ℝ :=
  match s with
  | 5 =>
      1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 24) *
            (1 - ((r : ℝ) - 4) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) / 6) *
          (1 - ((r : ℝ) - 3) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 4) *
          (1 - ((r : ℝ) - 2) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 6) *
          (1 - ((r : ℝ) - 1) / (r : ℝ) * p) ^ w -
        (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 24) *
          (1 - p) ^ w
  | 6 =>
      1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 120) *
            (1 - ((r : ℝ) - 5) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 5) / 24) *
          (1 - ((r : ℝ) - 4) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 12) *
          (1 - ((r : ℝ) - 3) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 12) *
          (1 - ((r : ℝ) - 2) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 24) *
          (1 - ((r : ℝ) - 1) / (r : ℝ) * p) ^ w +
        (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 120) *
          (1 - p) ^ w
  | _ => quarticOccupancyTail s w r p
private lemma s7_slotDiagExp_zero {n m k r : ℕ} (hr1 : 1 ≤ r) {S T : Finset (Fin (2 ^ n))} (hTS : T
  ⊆ S) (hr : (S \ T).card = r) (K : ℕ) : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 0 (S
  \ T)) = (1 - (multiP_succ K r (2 ^ n) : ℂ)) ^ (activeSlots m k) := by
  have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) (Nat.zero_le r) hTS hr K
  dsimp only at h; change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 0 (S \ T)) = _ at h
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); rw [h, Nat.choose_zero_right];
    push_cast; rw [sub_zero, div_self hr_ne, one_mul, one_mul]
/-- Exact `w`-slot expectation identity `(U_allᴴ · diag(stratumExitInd s (S \ T)) ·
  U_all)_{0,0} =
  sexticOccupancyTail s w r p`
  for all `1 ≤ s ≤ 6`. -/
theorem conj_stratumExitInd_sextic_zero_zero {n m k s r : ℕ} (hs1 : 1 ≤ s) (hs6 : s ≤ 6) (hsr : s ≤
  r) {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) :
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    (U_all.1ᴴ * Matrix.diagonal (stratumExitInd n m k s (S \ T)) * U_all.1) 0 0 =
      (sexticOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n)) : ℂ) := by
  rcases le_or_gt s 4 with hs4 | hs_gt4
  · have h_eq : sexticOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n)) =
      quarticOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n)) := by
      rcases s with _ | _ | _ | _ | _ | s <;> try omega
      all_goals rfl
    rw [h_eq]; exact conj_stratumExitInd_quartic_zero_zero hs1 hs4 hsr hTS hr K
  · change quarticSlotDiagExp n m k S T K (stratumExitInd n m k s (S \ T)) = _; have hr1 : 1 ≤ r :=
      (by omega); have hr2 : 2 ≤ r := (by omega); have hr3 : 3 ≤ r := (by omega)
    have hr4 : 4 ≤ r := (by omega); have hself : quarticSlotDiagExp n m k S T K (validAllInd n m k
      (S \ T)) = 1 := conj_validAllInd_self_zero_zero hTS K; have h0 := s7_slotDiagExp_zero (m :=
      m) (k := k) hr1 hTS hr K
    have h1 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 1 (S \ T)) = (r : ℂ) * (1 - ((r
      : ℝ) - 1) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr1 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 1 (S \ T)) = _ at h; rw [h,
        Nat.choose_one_right]; congr 2; push_cast; rfl
    have h2 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 2 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) / 2) * (1 - ((r : ℝ) - 2) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k)
      := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr2 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 2 (S \ T)) = _ at h; rw [h,
        choose_two_cast_complex r]; congr 2
    have h3 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 3 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) * ((r : ℂ) - 2) / 6) * (1 - ((r : ℝ) - 3) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^
      (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr3 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 3 (S \ T)) = _ at h; rw [h,
        choose_three_cast_complex r]; congr 2
    have h4 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 4 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) * ((r : ℂ) - 2) * ((r : ℂ) - 3) / 24) * (1 - ((r : ℝ) - 4) / (r : ℝ) * multiP_succ K r
      (2 ^ n) : ℂ) ^ (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr4 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 4 (S \ T)) = _ at h; rw [h,
        choose_four_cast_complex r]; congr 2
    interval_cases s
    · have hfun : stratumExitInd n m k 5 (S \ T) = fun o ↦ ((((validAllInd n m k (S \ T) o -
        subsetCardSumInd n m k 4 (S \ T) o) + (((S \ T).card : ℂ) - 4) * subsetCardSumInd n m k 3 (S
        \ T) o) - ((((S \ T).card : ℂ) - 3) * (((S \ T).card : ℂ) - 4) / 2) * subsetCardSumInd n m k
        2 (S \ T) o) + ((((S \ T).card : ℂ) - 2) * (((S \ T).card : ℂ) - 3) * (((S \ T).card : ℂ) -
        4) / 6) * subsetCardSumInd n m k 1 (S \ T) o) - ((((S \ T).card : ℂ) - 1) * (((S \ T).card :
        ℂ) - 2) * (((S \ T).card : ℂ) - 3) * (((S \ T).card : ℂ) - 4) / 24) * subsetCardSumInd n m k
        0 (S \ T) o := funext (stratumExitInd_decomp_five n m k (S \ T))
      rw [hfun, quarticSlotDiagExp_sub, quarticSlotDiagExp_add, quarticSlotDiagExp_sub,
        quarticSlotDiagExp_add, quarticSlotDiagExp_sub, quarticSlotDiagExp_const_mul,
        quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul,
        hself, h4, h3, h2, h1, h0, hr]; simp only [sexticOccupancyTail]; push_cast; ring
    · have hr5 : 5 ≤ r := (by omega)
      have h5 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 5 (S \ T)) = ((r : ℂ) * ((r :
        ℂ) - 1) * ((r : ℂ) - 2) * ((r : ℂ) - 3) * ((r : ℂ) - 4) / 120) * (1 - ((r : ℝ) - 5) / (r :
        ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
        have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr5 hTS hr K
        dsimp only at h; change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 5 (S \ T)) =
          _ at h; rw [h, choose_five_cast_complex r]; congr 2
      have hfun : stratumExitInd n m k 6 (S \ T) = fun o ↦ (((((validAllInd n m k (S \ T) o -
        subsetCardSumInd n m k 5 (S \ T) o) + (((S \ T).card : ℂ) - 5) * subsetCardSumInd n m k 4 (S
        \ T) o) - ((((S \ T).card : ℂ) - 4) * (((S \ T).card : ℂ) - 5) / 2) * subsetCardSumInd n m k
        3 (S \ T) o) + ((((S \ T).card : ℂ) - 3) * (((S \ T).card : ℂ) - 4) * (((S \ T).card : ℂ) -
        5) / 6) * subsetCardSumInd n m k 2 (S \ T) o) - ((((S \ T).card : ℂ) - 2) * (((S \ T).card :
        ℂ) - 3) * (((S \ T).card : ℂ) - 4) * (((S \ T).card : ℂ) - 5) / 24) * subsetCardSumInd n m k
        1 (S \ T) o) + ((((S \ T).card : ℂ) - 1) * (((S \ T).card : ℂ) - 2) * (((S \ T).card : ℂ) -
        3) * (((S \ T).card : ℂ) - 4) * (((S \ T).card : ℂ) - 5) / 120) * subsetCardSumInd n m k 0
        (S \ T) o := funext (stratumExitInd_decomp_six n m k (S \ T))
      rw [hfun, quarticSlotDiagExp_add, quarticSlotDiagExp_sub, quarticSlotDiagExp_add,
        quarticSlotDiagExp_sub, quarticSlotDiagExp_add, quarticSlotDiagExp_sub,
        quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul,
        quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul, hself, h5, h4, h3, h2, h1, h0,
        hr]; simp only [sexticOccupancyTail]; push_cast; ring
/-- Exact Markov recurrence for the fifth-order occupancy tail `sexticOccupancyTail 5`. -/
theorem sexticOccupancyTail_markov_five {w r : ℕ} (hr1 : 1 ≤ r) (p : ℝ) :
    let α : ℝ := ((r : ℝ) - 4) / (r : ℝ)
    sexticOccupancyTail 5 (w + 1) r p = (1 - α * p) * sexticOccupancyTail 5 w r p + α * p *
      quarticOccupancyTail 4 w r p := by
  intro α; have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hr1))
  simp only [sexticOccupancyTail, quarticOccupancyTail, α]; rw [pow_succ, pow_succ, pow_succ,
    pow_succ, pow_succ]; field_simp [hr_ne]; ring
/-- Exact Markov recurrence for the sixth-order occupancy tail `sexticOccupancyTail 6`. -/
theorem sexticOccupancyTail_markov_six {w r : ℕ} (hr1 : 1 ≤ r) (p : ℝ) :
    let α : ℝ := ((r : ℝ) - 5) / (r : ℝ)
    sexticOccupancyTail 6 (w + 1) r p = (1 - α * p) * sexticOccupancyTail 6 w r p + α * p *
      sexticOccupancyTail 5 w r p := by
  intro α; have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hr1))
  simp only [sexticOccupancyTail, α]; rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ,
    pow_succ]; field_simp [hr_ne]; ring
/-- Non-negativity of fourth-order finite differences of `x ↦ x ^ w` on `[0, ∞)`. -/
theorem fourth_diff_pow_nonneg {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (w : ℕ) : 0 ≤ (a + 4 * δ) ^ w - 4
  * (a + 3 * δ) ^ w + 6 * (a + 2 * δ) ^ w - 4 * (a + δ) ^ w + a ^ w := by
  induction w with
  | zero => norm_num
  | succ w ih =>
    have htd := third_diff_pow_nonneg ha hδ w
    have hid : (a + 4 * δ) ^ (w + 1) - 4 * (a + 3 * δ) ^ (w + 1) + 6 * (a + 2 * δ) ^ (w + 1) - 4 *
      (a + δ) ^ (w + 1) + a ^ (w + 1) = (a + 4 * δ) * ((a + 4 * δ) ^ w - 4 * (a + 3 * δ) ^ w + 6 *
      (a + 2 * δ) ^ w - 4 * (a + δ) ^ w + a ^ w) + 4 * δ * ((a + 3 * δ) ^ w - 3 * (a + 2 * δ) ^ w +
      3 * (a + δ) ^ w - a ^ w) := (by ring); rw [hid]; nlinarith
/-- Non-negativity of fifth-order finite differences of `x ↦ x ^ w` on `[0, ∞)`. -/
theorem fifth_diff_pow_nonneg {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (w : ℕ) : 0 ≤ (a + 5 * δ) ^ w - 5
  * (a + 4 * δ) ^ w + 10 * (a + 3 * δ) ^ w - 10 * (a + 2 * δ) ^ w + 5 * (a + δ) ^ w - a ^ w := by
  induction w with
  | zero => norm_num
  | succ w ih =>
    have hfd := fourth_diff_pow_nonneg ha hδ w
    have hid : (a + 5 * δ) ^ (w + 1) - 5 * (a + 4 * δ) ^ (w + 1) + 10 * (a + 3 * δ) ^ (w + 1) - 10 *
      (a + 2 * δ) ^ (w + 1) + 5 * (a + δ) ^ (w + 1) - a ^ (w + 1) = (a + 5 * δ) * ((a + 5 * δ) ^ w -
      5 * (a + 4 * δ) ^ w + 10 * (a + 3 * δ) ^ w - 10 * (a + 2 * δ) ^ w + 5 * (a + δ) ^ w - a ^ w) +
      5 * δ * ((a + 4 * δ) ^ w - 4 * (a + 3 * δ) ^ w + 6 * (a + 2 * δ) ^ w - 4 * (a + δ) ^ w + a ^
      w) := (by ring); rw [hid]; nlinarith
/-- Monotonicity in stride order: `sexticOccupancyTail 5 w r p ≤ quarticOccupancyTail 4 w r
  p`. -/
theorem sexticOccupancyTail_five_le_four {w r : ℕ} (hr5 : 5 ≤ r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
  : sexticOccupancyTail 5 w r p ≤ quarticOccupancyTail 4 w r p := by
  have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r)); have hr_ne : (r : ℝ) ≠ 0 :=
    hr_pos.ne'; simp only [sexticOccupancyTail, quarticOccupancyTail]
  let a : ℝ := 1 - p; let δ : ℝ := p / (r : ℝ)
  have ha1 : 1 - ((r : ℝ) - 1) / (r : ℝ) * p = a + δ := (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha2 : 1 - ((r : ℝ) - 2) / (r : ℝ) * p = a + 2 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha3 : 1 - ((r : ℝ) - 3) / (r : ℝ) * p = a + 3 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha4 : 1 - ((r : ℝ) - 4) / (r : ℝ) * p = a + 4 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring); have ha0 : 1 - p = a := rfl; rw [ha1, ha2, ha3,
    ha4, ha0]; have hr5_r : (5 : ℝ) ≤ r := (by exact_mod_cast hr5)
  have hcoeff : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 24 := by
    have : 0 ≤ (r : ℝ) - 1 := (by linarith); have : 0 ≤ (r : ℝ) - 2 := (by linarith); have : 0 ≤ (r
      : ℝ) - 3 := (by linarith); positivity
  have hfd := fourth_diff_pow_nonneg (a := a) (δ := δ) (by dsimp [a]; linarith) (div_nonneg hp0
    hr_pos.le) w; have hid : (1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) / 6) * (a + 3 * δ) ^ w +
    ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) / 2) * (a + 2 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 2) * ((r
    : ℝ) - 3) / 2) * (a + δ) ^ w + (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 6) * a ^ w) - (1
    - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 24) * (a + 4 * δ) ^ w + ((r : ℝ) *
    ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) / 6) * (a + 3 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 1)
    * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 4) * (a + 2 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) -
    3) * ((r : ℝ) - 4) / 6) * (a + δ) ^ w - (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r :
    ℝ) - 4) / 24) * a ^ w) = ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 24) * ((a +
    4 * δ) ^ w - 4 * (a + 3 * δ) ^ w + 6 * (a + 2 * δ) ^ w - 4 * (a + δ) ^ w + a ^ w) := (by ring)
  have hprod := mul_nonneg hcoeff hfd; linarith
/-- Monotonicity in stride order: `sexticOccupancyTail 6 w r p ≤ sexticOccupancyTail 5 w r
  p`. -/
theorem sexticOccupancyTail_six_le_five {w r : ℕ} (hr6 : 6 ≤ r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
  : sexticOccupancyTail 6 w r p ≤ sexticOccupancyTail 5 w r p := by
  have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r)); have hr_ne : (r : ℝ) ≠ 0 :=
    hr_pos.ne'; simp only [sexticOccupancyTail]
  let a : ℝ := 1 - p; let δ : ℝ := p / (r : ℝ)
  have ha1 : 1 - ((r : ℝ) - 1) / (r : ℝ) * p = a + δ := (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha2 : 1 - ((r : ℝ) - 2) / (r : ℝ) * p = a + 2 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha3 : 1 - ((r : ℝ) - 3) / (r : ℝ) * p = a + 3 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha4 : 1 - ((r : ℝ) - 4) / (r : ℝ) * p = a + 4 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha5 : 1 - ((r : ℝ) - 5) / (r : ℝ) * p = a + 5 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring); have ha0 : 1 - p = a := rfl; rw [ha1, ha2, ha3,
    ha4, ha5, ha0]; have hr6_r : (6 : ℝ) ≤ r := (by exact_mod_cast hr6)
  have hcoeff : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 120
    := by
    have : 0 ≤ (r : ℝ) - 1 := (by linarith); have : 0 ≤ (r : ℝ) - 2 := (by linarith); have : 0 ≤ (r
      : ℝ) - 3 := (by linarith); have : 0 ≤ (r : ℝ) - 4 := (by linarith); positivity
  have hfd := fifth_diff_pow_nonneg (a := a) (δ := δ) (by dsimp [a]; linarith) (div_nonneg hp0
    hr_pos.le) w; have hid : (1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) / 24) *
    (a + 4 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) / 6) * (a + 3 * δ) ^
    w - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 4) * (a + 2 * δ) ^ w + ((r : ℝ) *
    ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 6) * (a + δ) ^ w - (((r : ℝ) - 1) * ((r : ℝ) -
    2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 24) * a ^ w) - (1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) -
    2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 120) * (a + 5 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) * ((r :
    ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 5) / 24) * (a + 4 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 1) * ((r
    : ℝ) - 2) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 12) * (a + 3 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) *
    ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 12) * (a + 2 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 2)
    * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 24) * (a + δ) ^ w + (((r : ℝ) - 1) * ((r : ℝ)
    - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 120) * a ^ w) = ((r : ℝ) * ((r : ℝ) - 1)
    * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) / 120) * ((a + 5 * δ) ^ w - 5 * (a + 4 * δ) ^ w
    + 10 * (a + 3 * δ) ^ w - 10 * (a + 2 * δ) ^ w + 5 * (a + δ) ^ w - a ^ w) := (by ring)
  have hprod := mul_nonneg hcoeff hfd; linarith
private lemma s7_tail_four_bounds {w r : ℕ} (hr4 : 4 ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤
  p₂) (hp2 : p₂ ≤ 1) : 0 ≤ quarticOccupancyTail 4 w r p₁ ∧ quarticOccupancyTail 4 w r p₁ ≤
  quarticOccupancyTail 4 w r p₂ ∧ quarticOccupancyTail 4 w r p₂ ≤ 1 := by
  rcases lt_or_ge w 4 with hwlt | hw4
  · have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (by omega : r ≠ 0))
    have h0 (p : ℝ) : quarticOccupancyTail 4 w r p = 0 := by
      interval_cases w
      · simp only [quarticOccupancyTail, pow_zero]; ring
      · simp only [quarticOccupancyTail, pow_one]; field_simp [hr_ne]; ring
      · simp only [quarticOccupancyTail]; field_simp [hr_ne]; ring
      · simp only [quarticOccupancyTail]; field_simp [hr_ne]; ring
    rw [h0 p₁, h0 p₂]; exact ⟨le_rfl, le_rfl, zero_le_one⟩
  · rcases quarticOccupancyTail_pos_and_mono (s := 4) (w := w) (r := r) (by omega) (by omega) hw4
      hr4 hp1 hp12 hp2 with ⟨hpos, hmono, hle1⟩; exact ⟨hpos.le, hmono, hle1⟩
private lemma s7_tail_five_nonneg {w r : ℕ} (hr5 : 5 ≤ r) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : 0 ≤
  sexticOccupancyTail 5 w r p := by
  have hr1 : 1 ≤ r := (by omega); have hr4 : 4 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr5_r : (5 : ℝ) ≤ r := (by exact_mod_cast hr5)
  let α : ℝ := ((r : ℝ) - 4) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
  have hαp0 : 0 ≤ α * p := mul_nonneg hα0 hp0.le; have hαp1 : α * p ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 : sexticOccupancyTail 5 0 r p = 0 :=
      (by simp only [sexticOccupancyTail, pow_zero]; ring); rw [h0]
  | succ w ih =>
    have hm := sexticOccupancyTail_markov_five (w := w) hr1 p; dsimp only at hm
    change sexticOccupancyTail 5 (w + 1) r p = (1 - α * p) * sexticOccupancyTail 5 w r p + α * p *
      quarticOccupancyTail 4 w r p at hm; rw [hm]; have h4_0 := (s7_tail_four_bounds (w := w) hr4
      hp0 le_rfl hp1).1; nlinarith
private lemma s7_tail_five_mono {w r : ℕ} (hr5 : 5 ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤ p₂)
  (hp2 : p₂ ≤ 1) : sexticOccupancyTail 5 w r p₁ ≤ sexticOccupancyTail 5 w r p₂ := by
  have hr1 : 1 ≤ r := (by omega); have hr4 : 4 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr5_r : (5 : ℝ) ≤ r := (by exact_mod_cast hr5)
  let α : ℝ := ((r : ℝ) - 4) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith); have hp2_0 : 0 ≤ p₂ := hp1.le.trans hp12;
    have hαp2_0 : 0 ≤ α * p₂ := mul_nonneg hα0 hp2_0; have hαp2_1 : α * p₂ ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 (p : ℝ) : sexticOccupancyTail 5 0 r p = 0 :=
      (by simp only [sexticOccupancyTail, pow_zero]; ring); rw [h0, h0]
  | succ w ih =>
    have hm1 := sexticOccupancyTail_markov_five (w := w) hr1 p₁; have hm2 :=
      sexticOccupancyTail_markov_five (w := w) hr1 p₂; dsimp only at hm1 hm2
    change sexticOccupancyTail 5 (w + 1) r p₁ = (1 - α * p₁) * sexticOccupancyTail 5 w r p₁ + α * p₁
      * quarticOccupancyTail 4 w r p₁ at hm1; change sexticOccupancyTail 5 (w + 1) r p₂ = (1 - α *
      p₂) * sexticOccupancyTail 5 w r p₂ + α * p₂ * quarticOccupancyTail 4 w r p₂ at hm2; rw [hm1,
      hm2]; have h4_mono := (s7_tail_four_bounds (w := w) hr4 hp1 hp12 hp2).2.1; have h5_le_4 :=
      sexticOccupancyTail_five_le_four (w := w) hr5 hp1.le (hp12.trans hp2); have hid : ((1 - α *
      p₂) * sexticOccupancyTail 5 w r p₂ + α * p₂ * quarticOccupancyTail 4 w r p₂) - ((1 - α * p₁) *
      sexticOccupancyTail 5 w r p₁ + α * p₁ * quarticOccupancyTail 4 w r p₁) = (1 - α * p₂) *
      (sexticOccupancyTail 5 w r p₂ - sexticOccupancyTail 5 w r p₁) + α * p₂ * (quarticOccupancyTail
      4 w r p₂ - quarticOccupancyTail 4 w r p₁) + α * (p₂ - p₁) * (quarticOccupancyTail 4 w r p₁ -
      sexticOccupancyTail 5 w r p₁) := (by ring); have ht1 : 0 ≤ (1 - α * p₂) * (sexticOccupancyTail
      5 w r p₂ - sexticOccupancyTail 5 w r p₁) := mul_nonneg (by linarith) (by linarith)
    have ht2 : 0 ≤ α * p₂ * (quarticOccupancyTail 4 w r p₂ - quarticOccupancyTail 4 w r p₁) :=
      mul_nonneg hαp2_0 (by linarith); have ht3 : 0 ≤ α * (p₂ - p₁) * (quarticOccupancyTail 4 w r p₁
      - sexticOccupancyTail 5 w r p₁) := mul_nonneg (mul_nonneg hα0 (by linarith)) (by linarith)
    linarith
private lemma s7_tail_six_nonneg {w r : ℕ} (hr6 : 6 ≤ r) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : 0 ≤
  sexticOccupancyTail 6 w r p := by
  have hr1 : 1 ≤ r := (by omega); have hr5 : 5 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr6_r : (6 : ℝ) ≤ r := (by exact_mod_cast hr6)
  let α : ℝ := ((r : ℝ) - 5) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
  have hαp0 : 0 ≤ α * p := mul_nonneg hα0 hp0.le; have hαp1 : α * p ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 : sexticOccupancyTail 6 0 r p = 0 :=
      (by simp only [sexticOccupancyTail, pow_zero]; ring); rw [h0]
  | succ w ih =>
    have hm := sexticOccupancyTail_markov_six (w := w) hr1 p; dsimp only at hm
    change sexticOccupancyTail 6 (w + 1) r p = (1 - α * p) * sexticOccupancyTail 6 w r p + α * p *
      sexticOccupancyTail 5 w r p at hm
    rw [hm]; have h5_0 := s7_tail_five_nonneg (w := w) hr5 hp0 hp1; nlinarith
private lemma s7_tail_six_mono {w r : ℕ} (hr6 : 6 ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤ p₂)
  (hp2 : p₂ ≤ 1) : sexticOccupancyTail 6 w r p₁ ≤ sexticOccupancyTail 6 w r p₂ := by
  have hr1 : 1 ≤ r := (by omega); have hr5 : 5 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr6_r : (6 : ℝ) ≤ r := (by exact_mod_cast hr6)
  let α : ℝ := ((r : ℝ) - 5) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith); have hp2_0 : 0 ≤ p₂ := hp1.le.trans hp12;
    have hαp2_0 : 0 ≤ α * p₂ := mul_nonneg hα0 hp2_0; have hαp2_1 : α * p₂ ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 (p : ℝ) : sexticOccupancyTail 6 0 r p = 0 :=
      (by simp only [sexticOccupancyTail, pow_zero]; ring); rw [h0, h0]
  | succ w ih =>
    have hm1 := sexticOccupancyTail_markov_six (w := w) hr1 p₁; have hm2 :=
      sexticOccupancyTail_markov_six (w := w) hr1 p₂; dsimp only at hm1 hm2
    change sexticOccupancyTail 6 (w + 1) r p₁ = (1 - α * p₁) * sexticOccupancyTail 6 w r p₁ + α * p₁
      * sexticOccupancyTail 5 w r p₁ at hm1; change sexticOccupancyTail 6 (w + 1) r p₂ = (1 - α *
      p₂) * sexticOccupancyTail 6 w r p₂ + α * p₂ * sexticOccupancyTail 5 w r p₂ at hm2; rw [hm1,
      hm2]; have h5_mono := s7_tail_five_mono (w := w) hr5 hp1 hp12 hp2; have h6_le_5 :=
      sexticOccupancyTail_six_le_five (w := w) hr6 hp1.le (hp12.trans hp2); have hid : ((1 - α * p₂)
      * sexticOccupancyTail 6 w r p₂ + α * p₂ * sexticOccupancyTail 5 w r p₂) - ((1 - α * p₁) *
      sexticOccupancyTail 6 w r p₁ + α * p₁ * sexticOccupancyTail 5 w r p₁) = (1 - α * p₂) *
      (sexticOccupancyTail 6 w r p₂ - sexticOccupancyTail 6 w r p₁) + α * p₂ * (sexticOccupancyTail
      5 w r p₂ - sexticOccupancyTail 5 w r p₁) + α * (p₂ - p₁) * (sexticOccupancyTail 5 w r p₁ -
      sexticOccupancyTail 6 w r p₁) := (by ring); have ht1 : 0 ≤ (1 - α * p₂) * (sexticOccupancyTail
      6 w r p₂ - sexticOccupancyTail 6 w r p₁) := mul_nonneg (by linarith) (by linarith)
    have ht2 : 0 ≤ α * p₂ * (sexticOccupancyTail 5 w r p₂ - sexticOccupancyTail 5 w r p₁) :=
      mul_nonneg hαp2_0 (by linarith); have ht3 : 0 ≤ α * (p₂ - p₁) * (sexticOccupancyTail 5 w r p₁
      - sexticOccupancyTail 6 w r p₁) := mul_nonneg (mul_nonneg hα0 (by linarith)) (by linarith)
    linarith
/-- Positivity, monotonicity in `p ∈ (0, 1]`, and upper bound `≤ 1` for `sexticOccupancyTail
  s w r
  p`
  across all `1 ≤ s ≤ 6`. -/
theorem sexticOccupancyTail_pos_and_mono {s w r : ℕ} (hs1 : 1 ≤ s) (hs6 : s ≤ 6) (hsw : s ≤ w) (hsr
  : s ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤ p₂) (hp2 : p₂ ≤ 1) : 0 < sexticOccupancyTail s w
  r p₁ ∧ sexticOccupancyTail s w r p₁ ≤ sexticOccupancyTail s w r p₂ ∧ sexticOccupancyTail s w r p₂
  ≤ 1 := by
  rcases le_or_gt s 4 with hs4 | hs_gt4
  · have h_eq (p : ℝ) : sexticOccupancyTail s w r p = quarticOccupancyTail s w r p := by
      rcases s with _ | _ | _ | _ | _ | s <;> try omega
      all_goals rfl
    rw [h_eq p₁, h_eq p₂]; exact quarticOccupancyTail_pos_and_mono hs1 hs4 hsw hsr hp1 hp12 hp2
  · have hp2_pos : 0 < p₂ := hp1.trans_le hp12; have hp1_le1 : p₁ ≤ 1 := hp12.trans hp2
    have hr4 : 4 ≤ r := (by omega); have h4_le1 := (s7_tail_four_bounds (w := w) hr4 hp2_pos le_rfl
      hp2).2.2
    interval_cases s
    · refine ⟨?_, s7_tail_five_mono hsr hp1 hp12 hp2, (sexticOccupancyTail_five_le_four hsr
        hp2_pos.le hp2).trans h4_le1⟩; rcases Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0) with
        ⟨w', rfl⟩; have hr1 : 1 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
        (by exact_mod_cast hr1); have hr5_r : (5 : ℝ) ≤ r := (by exact_mod_cast hsr)
      let α : ℝ := ((r : ℝ) - 4) / (r : ℝ); have hα_pos : 0 < α := div_pos (by linarith) hr_pos
      have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
      have hαp_pos : 0 < α * p₁ := mul_pos hα_pos hp1; have hαp_le1 : α * p₁ ≤ 1 := (by nlinarith)
      have hm := sexticOccupancyTail_markov_five (w := w') hr1 p₁; dsimp only at hm
      change sexticOccupancyTail 5 (w' + 1) r p₁ = (1 - α * p₁) * sexticOccupancyTail 5 w' r p₁ + α
        * p₁ * quarticOccupancyTail 4 w' r p₁ at hm; rw [hm]; have h5_0 := s7_tail_five_nonneg (w
        := w') hsr hp1 hp1_le1; have h4_pos := (quarticOccupancyTail_pos_and_mono (s := 4) (w := w')
        (r := r) (by omega) (by omega) (by omega) (by omega) hp1 le_rfl hp1_le1).1; nlinarith
    · have hr5 : 5 ≤ r := (by omega)
      have h5_le_4 := sexticOccupancyTail_five_le_four (w := w) hr5 hp2_pos.le hp2; have h6_le_5 :=
        sexticOccupancyTail_six_le_five (w := w) hsr hp2_pos.le hp2; refine ⟨?_, s7_tail_six_mono
        hsr hp1 hp12 hp2, (h6_le_5.trans h5_le_4).trans h4_le1⟩
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0) with ⟨w', rfl⟩; have hr1 : 1 ≤ r :=
        (by omega); have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
      have hr6_r : (6 : ℝ) ≤ r := (by exact_mod_cast hsr); let α : ℝ := ((r : ℝ) - 5) / (r : ℝ)
      have hα_pos : 0 < α := div_pos (by linarith) hr_pos
      have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
      have hαp_pos : 0 < α * p₁ := mul_pos hα_pos hp1; have hαp_le1 : α * p₁ ≤ 1 := (by nlinarith)
      have hm := sexticOccupancyTail_markov_six (w := w') hr1 p₁; dsimp only at hm
      change sexticOccupancyTail 6 (w' + 1) r p₁ = (1 - α * p₁) * sexticOccupancyTail 6 w' r p₁ + α
        * p₁ * sexticOccupancyTail 5 w' r p₁ at hm; rw [hm]; have h6_0 := s7_tail_six_nonneg (w :=
        w') hsr hp1 hp1_le1
      -- Prove positivity of sexticOccupancyTail 5 w' r p₁ via its Markov recurrence
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : w' ≠ 0) with ⟨w'', rfl⟩
      let β : ℝ := ((r : ℝ) - 4) / (r : ℝ); have hβ_pos : 0 < β := div_pos (by linarith) hr_pos
      have hβ1 : β ≤ 1 := (div_le_one hr_pos).2 (by linarith)
      have hβp_pos : 0 < β * p₁ := mul_pos hβ_pos hp1; have hβp_le1 : β * p₁ ≤ 1 := (by nlinarith)
      have hm5 := sexticOccupancyTail_markov_five (w := w'') hr1 p₁; dsimp only at hm5
      change sexticOccupancyTail 5 (w'' + 1) r p₁ = (1 - β * p₁) * sexticOccupancyTail 5 w'' r p₁ +
        β * p₁ * quarticOccupancyTail 4 w'' r p₁ at hm5; have h5_0' := s7_tail_five_nonneg (w :=
        w'') hr5 hp1 hp1_le1; have h4_pos := (quarticOccupancyTail_pos_and_mono (s := 4) (w := w'')
        (r := r) (by omega) (by omega) (by omega) (by omega) hp1 le_rfl hp1_le1).1
      have h5_pos : 0 < sexticOccupancyTail 5 (w'' + 1) r p₁ := (by rw [hm5]; nlinarith); nlinarith
end QuantumComputation.Specs
end
end Sec_SexticOccupancyMarkov
section Sec_OcticEulerMobiusDecomp
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
/-- Unconditional complex polynomial identity for `Nat.choose m 6`. -/
theorem choose_six_cast_complex (m : ℕ) : (Nat.choose m 6 : ℂ) = (m : ℂ) * ((m : ℂ) - 1) * ((m : ℂ)
  - 2) * ((m : ℂ) - 3) * ((m : ℂ) - 4) * ((m : ℂ) - 5) / 720 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.choose_succ_succ m 5]; push_cast; rw [choose_five_cast_complex m, ih]; ring
/-- Unconditional complex polynomial identity for `Nat.choose m 7`. -/
theorem choose_seven_cast_complex (m : ℕ) : (Nat.choose m 7 : ℂ) = (m : ℂ) * ((m : ℂ) - 1) * ((m :
  ℂ) - 2) * ((m : ℂ) - 3) * ((m : ℂ) - 4) * ((m : ℂ) - 5) * ((m : ℂ) - 6) / 5040 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.choose_succ_succ m 6]; push_cast; rw [choose_six_cast_complex m, ih]; ring
/-- Exact seventh-order Boolean-lattice Euler-Mobius character decomposition of
  `stratumExitInd n m
  k 7 R`. -/
theorem stratumExitInd_decomp_seven (n m k : ℕ) (R : Finset (Fin (2 ^ n))) (o : Fin (2 ^
  findAllQubits n m k)) : stratumExitInd n m k 7 R o = validAllInd n m k R o - subsetCardSumInd n m
  k 6 R o + ((R.card : ℂ) - 6) * subsetCardSumInd n m k 5 R o - (((R.card : ℂ) - 5) * ((R.card : ℂ)
  - 6) / 2) * subsetCardSumInd n m k 4 R o + (((R.card : ℂ) - 4) * ((R.card : ℂ) - 5) * ((R.card :
  ℂ) - 6) / 6) * subsetCardSumInd n m k 3 R o - (((R.card : ℂ) - 3) * ((R.card : ℂ) - 4) * ((R.card
  : ℂ) - 5) * ((R.card : ℂ) - 6) / 24) * subsetCardSumInd n m k 2 R o + (((R.card : ℂ) - 2) *
  ((R.card : ℂ) - 3) * ((R.card : ℂ) - 4) * ((R.card : ℂ) - 5) * ((R.card : ℂ) - 6) / 120) *
  subsetCardSumInd n m k 1 R o - (((R.card : ℂ) - 1) * ((R.card : ℂ) - 2) * ((R.card : ℂ) - 3) *
  ((R.card : ℂ) - 4) * ((R.card : ℂ) - 5) * ((R.card : ℂ) - 6) / 720) * subsetCardSumInd n m k 0 R o
  := by
  by_cases hHR : hitSet n m k o ⊆ R
  · rw [subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset
      hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR,
      subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR]; simp only [stratumExitInd,
      validAllInd_eq_hitSet_subset, hHR, true_and]; have hle : (hitSet n m k o).card ≤ R.card :=
      Finset.card_le_card hHR; generalize (hitSet n m k o).card = h at hle ⊢
    rcases h with _ | _ | _ | _ | _ | _ | _ | c
    · simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero,
        show ¬ (7 ≤ 0) by omega, Nat.choose_zero_right, Nat.cast_one,
        Nat.choose_one_right, choose_two_cast_complex, choose_three_cast_complex,
        choose_four_cast_complex, choose_five_cast_complex, choose_six_cast_complex]; ring
    · simp only [show 1 ≤ 6 by omega, show 1 ≤ 5 by omega, show 1 ≤ 4 by omega,
        show 1 ≤ 3 by omega, show 1 ≤ 2 by omega, show 1 ≤ 1 by omega,
        show ¬ (1 ≤ 0) by omega, show ¬ (7 ≤ 1) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 6 - 1 = 5 from rfl, show 5 - 1 = 4 from rfl, show 4 - 1 = 3 from rfl, show 3 - 1 = 2
        from rfl, show 2 - 1 = 1 from rfl, choose_five_cast_complex, choose_four_cast_complex,
        choose_three_cast_complex, choose_two_cast_complex, Nat.choose_one_right, Nat.cast_sub hle,
        Nat.cast_one]; ring
    · simp only [show 2 ≤ 6 by omega, show 2 ≤ 5 by omega, show 2 ≤ 4 by omega,
        show 2 ≤ 3 by omega, show 2 ≤ 2 by omega, show ¬ (2 ≤ 1) by omega,
        show ¬ (2 ≤ 0) by omega, show ¬ (7 ≤ 2) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 6 - 2 = 4 from rfl, show 5 - 2 = 3 from rfl, show 4 - 2 = 2 from rfl, show 3 - 2 = 1
        from rfl, choose_four_cast_complex, choose_three_cast_complex, choose_two_cast_complex,
        Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 3 ≤ 6 by omega, show 3 ≤ 5 by omega, show 3 ≤ 4 by omega,
        show 3 ≤ 3 by omega, show ¬ (3 ≤ 2) by omega, show ¬ (3 ≤ 1) by omega,
        show ¬ (3 ≤ 0) by omega, show ¬ (7 ≤ 3) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 6 - 3 = 3 from rfl, show 5 - 3 = 2 from rfl, show 4 - 3 = 1 from rfl,
        choose_three_cast_complex, choose_two_cast_complex, Nat.choose_one_right, Nat.cast_sub hle]
      push_cast; ring
    · simp only [show 4 ≤ 6 by omega, show 4 ≤ 5 by omega, show 4 ≤ 4 by omega,
        show ¬ (4 ≤ 3) by omega, show ¬ (4 ≤ 2) by omega, show ¬ (4 ≤ 1) by omega,
        show ¬ (4 ≤ 0) by omega, show ¬ (7 ≤ 4) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 6 - 4 = 2 from rfl, show 5 - 4 = 1 from rfl, choose_two_cast_complex,
        Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 5 ≤ 6 by omega, show 5 ≤ 5 by omega, show ¬ (5 ≤ 4) by omega,
        show ¬ (5 ≤ 3) by omega, show ¬ (5 ≤ 2) by omega, show ¬ (5 ≤ 1) by omega,
        show ¬ (5 ≤ 0) by omega, show ¬ (7 ≤ 5) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 6 - 5 = 1 from rfl, Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 6 ≤ 6 by omega, show ¬ (6 ≤ 5) by omega, show ¬ (6 ≤ 4) by omega,
        show ¬ (6 ≤ 3) by omega, show ¬ (6 ≤ 2) by omega, show ¬ (6 ≤ 1) by omega,
        show ¬ (6 ≤ 0) by omega, show ¬ (7 ≤ 6) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]; ring
    · have h7 : 7 ≤ c + 7 := (by omega); have hn6 : ¬ (c + 7 ≤ 6) := (by omega); have hn5 : ¬ (c + 7
        ≤ 5) := (by omega); have hn4 : ¬ (c + 7 ≤ 4) := (by omega); have hn3 : ¬ (c + 7 ≤ 3) :=
        (by omega); have hn2 : ¬ (c + 7 ≤ 2) := (by omega); have hn1 : ¬ (c + 7 ≤ 1) := (by omega)
      have hn0 : ¬ (c + 7 ≤ 0) := (by omega); simp only [h7, hn6, hn5, hn4, hn3, hn2, hn1, hn0,
        ↓reduceIte]; ring
  · rw [subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR]; simp only [stratumExitInd, validAllInd_eq_hitSet_subset,
      hHR, false_and, ↓reduceIte]; ring
/-- Exact eighth-order Boolean-lattice Euler-Mobius character decomposition of
  `stratumExitInd n m k
  8 R`. -/
theorem stratumExitInd_decomp_eight (n m k : ℕ) (R : Finset (Fin (2 ^ n))) (o : Fin (2 ^
  findAllQubits n m k)) : stratumExitInd n m k 8 R o = validAllInd n m k R o - subsetCardSumInd n m
  k 7 R o + ((R.card : ℂ) - 7) * subsetCardSumInd n m k 6 R o - (((R.card : ℂ) - 6) * ((R.card : ℂ)
  - 7) / 2) * subsetCardSumInd n m k 5 R o + (((R.card : ℂ) - 5) * ((R.card : ℂ) - 6) * ((R.card :
  ℂ) - 7) / 6) * subsetCardSumInd n m k 4 R o - (((R.card : ℂ) - 4) * ((R.card : ℂ) - 5) * ((R.card
  : ℂ) - 6) * ((R.card : ℂ) - 7) / 24) * subsetCardSumInd n m k 3 R o + (((R.card : ℂ) - 3) *
  ((R.card : ℂ) - 4) * ((R.card : ℂ) - 5) * ((R.card : ℂ) - 6) * ((R.card : ℂ) - 7) / 120) *
  subsetCardSumInd n m k 2 R o - (((R.card : ℂ) - 2) * ((R.card : ℂ) - 3) * ((R.card : ℂ) - 4) *
  ((R.card : ℂ) - 5) * ((R.card : ℂ) - 6) * ((R.card : ℂ) - 7) / 720) * subsetCardSumInd n m k 1 R o
  + (((R.card : ℂ) - 1) * ((R.card : ℂ) - 2) * ((R.card : ℂ) - 3) * ((R.card : ℂ) - 4) * ((R.card :
  ℂ) - 5) * ((R.card : ℂ) - 6) * ((R.card : ℂ) - 7) / 5040) * subsetCardSumInd n m k 0 R o := by
  by_cases hHR : hitSet n m k o ⊆ R
  · rw [subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset
      hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR,
      subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset hHR, subsetCardSumInd_of_subset
      hHR]; simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, true_and]
    have hle : (hitSet n m k o).card ≤ R.card := Finset.card_le_card hHR; generalize (hitSet n m k
      o).card = h at hle ⊢; rcases h with _ | _ | _ | _ | _ | _ | _ | _ | c
    · simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero,
        show ¬ (8 ≤ 0) by omega, Nat.choose_zero_right, Nat.cast_one,
        Nat.choose_one_right, choose_two_cast_complex, choose_three_cast_complex,
        choose_four_cast_complex, choose_five_cast_complex, choose_six_cast_complex,
        choose_seven_cast_complex]; ring
    · simp only [show 1 ≤ 7 by omega, show 1 ≤ 6 by omega, show 1 ≤ 5 by omega,
        show 1 ≤ 4 by omega, show 1 ≤ 3 by omega, show 1 ≤ 2 by omega,
        show 1 ≤ 1 by omega, show ¬ (1 ≤ 0) by omega, show ¬ (8 ≤ 1) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 7 - 1 = 6 from rfl, show 6 - 1 = 5 from rfl, show 5 - 1 = 4 from rfl, show 4 - 1 = 3
        from rfl, show 3 - 1 = 2 from rfl, show 2 - 1 = 1 from rfl, choose_six_cast_complex,
        choose_five_cast_complex, choose_four_cast_complex, choose_three_cast_complex,
        choose_two_cast_complex, Nat.choose_one_right, Nat.cast_sub hle, Nat.cast_one]; ring
    · simp only [show 2 ≤ 7 by omega, show 2 ≤ 6 by omega, show 2 ≤ 5 by omega,
        show 2 ≤ 4 by omega, show 2 ≤ 3 by omega, show 2 ≤ 2 by omega,
        show ¬ (2 ≤ 1) by omega, show ¬ (2 ≤ 0) by omega, show ¬ (8 ≤ 2) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 7 - 2 = 5 from rfl, show 6 - 2 = 4 from rfl, show 5 - 2 = 3 from rfl, show 4 - 2 = 2
        from rfl, show 3 - 2 = 1 from rfl, choose_five_cast_complex, choose_four_cast_complex,
        choose_three_cast_complex, choose_two_cast_complex, Nat.choose_one_right, Nat.cast_sub hle]
      push_cast; ring
    · simp only [show 3 ≤ 7 by omega, show 3 ≤ 6 by omega, show 3 ≤ 5 by omega,
        show 3 ≤ 4 by omega, show 3 ≤ 3 by omega, show ¬ (3 ≤ 2) by omega,
        show ¬ (3 ≤ 1) by omega, show ¬ (3 ≤ 0) by omega, show ¬ (8 ≤ 3) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 7 - 3 = 4 from rfl, show 6 - 3 = 3 from rfl, show 5 - 3 = 2 from rfl, show 4 - 3 = 1
        from rfl, choose_four_cast_complex, choose_three_cast_complex, choose_two_cast_complex,
        Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 4 ≤ 7 by omega, show 4 ≤ 6 by omega, show 4 ≤ 5 by omega,
        show 4 ≤ 4 by omega, show ¬ (4 ≤ 3) by omega, show ¬ (4 ≤ 2) by omega,
        show ¬ (4 ≤ 1) by omega, show ¬ (4 ≤ 0) by omega, show ¬ (8 ≤ 4) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 7 - 4 = 3 from rfl, show 6 - 4 = 2 from rfl, show 5 - 4 = 1 from rfl,
        choose_three_cast_complex, choose_two_cast_complex, Nat.choose_one_right, Nat.cast_sub hle]
      push_cast; ring
    · simp only [show 5 ≤ 7 by omega, show 5 ≤ 6 by omega, show 5 ≤ 5 by omega,
        show ¬ (5 ≤ 4) by omega, show ¬ (5 ≤ 3) by omega, show ¬ (5 ≤ 2) by omega,
        show ¬ (5 ≤ 1) by omega, show ¬ (5 ≤ 0) by omega, show ¬ (8 ≤ 5) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 7 - 5 = 2 from rfl, show 6 - 5 = 1 from rfl, choose_two_cast_complex,
        Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 6 ≤ 7 by omega, show 6 ≤ 6 by omega, show ¬ (6 ≤ 5) by omega,
        show ¬ (6 ≤ 4) by omega, show ¬ (6 ≤ 3) by omega, show ¬ (6 ≤ 2) by omega,
        show ¬ (6 ≤ 1) by omega, show ¬ (6 ≤ 0) by omega, show ¬ (8 ≤ 6) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]
      rw [show 7 - 6 = 1 from rfl, Nat.choose_one_right, Nat.cast_sub hle]; push_cast; ring
    · simp only [show 7 ≤ 7 by omega, show ¬ (7 ≤ 6) by omega, show ¬ (7 ≤ 5) by omega,
        show ¬ (7 ≤ 4) by omega, show ¬ (7 ≤ 3) by omega, show ¬ (7 ≤ 2) by omega,
        show ¬ (7 ≤ 1) by omega, show ¬ (7 ≤ 0) by omega, show ¬ (8 ≤ 7) by omega,
        ↓reduceIte, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one]; ring
    · have h8 : 8 ≤ c + 8 := (by omega); have hn7 : ¬ (c + 8 ≤ 7) := (by omega); have hn6 : ¬ (c + 8
        ≤ 6) := (by omega); have hn5 : ¬ (c + 8 ≤ 5) := (by omega); have hn4 : ¬ (c + 8 ≤ 4) :=
        (by omega); have hn3 : ¬ (c + 8 ≤ 3) := (by omega); have hn2 : ¬ (c + 8 ≤ 2) := (by omega)
      have hn1 : ¬ (c + 8 ≤ 1) := (by omega); have hn0 : ¬ (c + 8 ≤ 0) := (by omega); simp only [h8,
        hn7, hn6, hn5, hn4, hn3, hn2, hn1, hn0, ↓reduceIte]; ring
  · rw [subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR,
      subsetCardSumInd_of_not_subset hHR, subsetCardSumInd_of_not_subset hHR]
    simp only [stratumExitInd, validAllInd_eq_hitSet_subset, hHR, false_and, ↓reduceIte]; ring
end QuantumComputation.Specs
end
end Sec_OcticEulerMobiusDecomp
section Sec_OcticOccupancyMarkov
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal
/-- Exact eighth-order binomial occupancy tail polynomial `T_s(w, r, p) = P(|H_w| ≥ s)`
  for `s ∈ {0..8}`. -/
noncomputable def octicOccupancyTail (s w r : ℕ) (p : ℝ) : ℝ :=
  match s with
  | 7 =>
      1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) /
        720) *
            (1 - ((r : ℝ) - 6) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 6) /
          120) *
          (1 - ((r : ℝ) - 5) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 5) * ((r : ℝ) - 6) /
          48) *
          (1 - ((r : ℝ) - 4) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) /
          36) *
          (1 - ((r : ℝ) - 3) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) /
          48) *
          (1 - ((r : ℝ) - 2) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) /
          120) *
          (1 - ((r : ℝ) - 1) / (r : ℝ) * p) ^ w -
        (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) -
          6) / 720) *
          (1 - p) ^ w
  | 8 =>
      1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) *
        ((r : ℝ) - 6) / 5040) *
            (1 - ((r : ℝ) - 7) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) *
          ((r : ℝ) - 7) / 720) *
          (1 - ((r : ℝ) - 6) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 6) *
          ((r : ℝ) - 7) / 240) *
          (1 - ((r : ℝ) - 5) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 5) * ((r : ℝ) - 6) *
          ((r : ℝ) - 7) / 144) *
          (1 - ((r : ℝ) - 4) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) *
          ((r : ℝ) - 7) / 144) *
          (1 - ((r : ℝ) - 3) / (r : ℝ) * p) ^ w +
        ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) *
          ((r : ℝ) - 7) / 240) *
          (1 - ((r : ℝ) - 2) / (r : ℝ) * p) ^ w -
        ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) *
          ((r : ℝ) - 7) / 720) *
          (1 - ((r : ℝ) - 1) / (r : ℝ) * p) ^ w +
        (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) -
          6) * ((r : ℝ) - 7) / 5040) *
          (1 - p) ^ w
  | _ => sexticOccupancyTail s w r p
private lemma s8_slotDiagExp_zero {n m k r : ℕ} (hr1 : 1 ≤ r) {S T : Finset (Fin (2 ^ n))} (hTS : T
  ⊆ S) (hr : (S \ T).card = r) (K : ℕ) : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 0 (S
  \ T)) = (1 - (multiP_succ K r (2 ^ n) : ℂ)) ^ (activeSlots m k) := by
  have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) (Nat.zero_le r) hTS hr K
  dsimp only at h; change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 0 (S \ T)) = _ at h
  have hr_ne : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); rw [h, Nat.choose_zero_right];
    push_cast; rw [sub_zero, div_self hr_ne, one_mul, one_mul]
/-- Exact `w`-slot expectation identity `(U_allᴴ · diag(stratumExitInd s (S \ T)) ·
  U_all)_{0,0} =
  octicOccupancyTail s w r p`
  for all `1 ≤ s ≤ 8`. -/
theorem conj_stratumExitInd_octic_zero_zero {n m k s r : ℕ} (hs1 : 1 ≤ s) (hs8 : s ≤ 8) (hsr : s ≤
  r) {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (K : ℕ) :
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    (U_all.1ᴴ * Matrix.diagonal (stratumExitInd n m k s (S \ T)) * U_all.1) 0 0 =
      (octicOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n)) : ℂ) := by
  rcases le_or_gt s 6 with hs6 | hs_gt6
  · have h_eq : octicOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n)) =
      sexticOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n)) := by
      rcases s with _ | _ | _ | _ | _ | _ | _ | s <;> try omega
      all_goals rfl
    rw [h_eq]; exact conj_stratumExitInd_sextic_zero_zero hs1 hs6 hsr hTS hr K
  · change quarticSlotDiagExp n m k S T K (stratumExitInd n m k s (S \ T)) = _; have hr1 : 1 ≤ r :=
      (by omega); have hr2 : 2 ≤ r := (by omega); have hr3 : 3 ≤ r := (by omega)
    have hr4 : 4 ≤ r := (by omega); have hr5 : 5 ≤ r := (by omega); have hr6 : 6 ≤ r := (by omega)
    have hself : quarticSlotDiagExp n m k S T K (validAllInd n m k (S \ T)) = 1 :=
      conj_validAllInd_self_zero_zero hTS K
    have h0 := s8_slotDiagExp_zero (m := m) (k := k) hr1 hTS hr K
    have h1 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 1 (S \ T)) = (r : ℂ) * (1 - ((r
      : ℝ) - 1) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr1 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 1 (S \ T)) = _ at h; rw [h,
        Nat.choose_one_right]; congr 2; push_cast; rfl
    have h2 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 2 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) / 2) * (1 - ((r : ℝ) - 2) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k)
      := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr2 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 2 (S \ T)) = _ at h; rw [h,
        choose_two_cast_complex r]; congr 2
    have h3 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 3 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) * ((r : ℂ) - 2) / 6) * (1 - ((r : ℝ) - 3) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^
      (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr3 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 3 (S \ T)) = _ at h; rw [h,
        choose_three_cast_complex r]; congr 2
    have h4 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 4 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) * ((r : ℂ) - 2) * ((r : ℂ) - 3) / 24) * (1 - ((r : ℝ) - 4) / (r : ℝ) * multiP_succ K r
      (2 ^ n) : ℂ) ^ (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr4 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 4 (S \ T)) = _ at h; rw [h,
        choose_four_cast_complex r]; congr 2
    have h5 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 5 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) * ((r : ℂ) - 2) * ((r : ℂ) - 3) * ((r : ℂ) - 4) / 120) * (1 - ((r : ℝ) - 5) / (r : ℝ)
      * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr5 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 5 (S \ T)) = _ at h; rw [h,
        choose_five_cast_complex r]; congr 2
    have h6 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 6 (S \ T)) = ((r : ℂ) * ((r :
      ℂ) - 1) * ((r : ℂ) - 2) * ((r : ℂ) - 3) * ((r : ℂ) - 4) * ((r : ℂ) - 5) / 720) * (1 - ((r : ℝ)
      - 6) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k) := by
      have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr6 hTS hr K
      dsimp only at h
      change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 6 (S \ T)) = _ at h; rw [h,
        choose_six_cast_complex r]; congr 2
    interval_cases s
    · have hfun : stratumExitInd n m k 7 (S \ T) = fun o ↦ ((((((validAllInd n m k (S \ T) o -
        subsetCardSumInd n m k 6 (S \ T) o) + (((S \ T).card : ℂ) - 6) * subsetCardSumInd n m k 5 (S
        \ T) o) - ((((S \ T).card : ℂ) - 5) * (((S \ T).card : ℂ) - 6) / 2) * subsetCardSumInd n m k
        4 (S \ T) o) + ((((S \ T).card : ℂ) - 4) * (((S \ T).card : ℂ) - 5) * (((S \ T).card : ℂ) -
        6) / 6) * subsetCardSumInd n m k 3 (S \ T) o) - ((((S \ T).card : ℂ) - 3) * (((S \ T).card :
        ℂ) - 4) * (((S \ T).card : ℂ) - 5) * (((S \ T).card : ℂ) - 6) / 24) * subsetCardSumInd n m k
        2 (S \ T) o) + ((((S \ T).card : ℂ) - 2) * (((S \ T).card : ℂ) - 3) * (((S \ T).card : ℂ) -
        4) * (((S \ T).card : ℂ) - 5) * (((S \ T).card : ℂ) - 6) / 120) * subsetCardSumInd n m k 1
        (S \ T) o) - ((((S \ T).card : ℂ) - 1) * (((S \ T).card : ℂ) - 2) * (((S \ T).card : ℂ) - 3)
        * (((S \ T).card : ℂ) - 4) * (((S \ T).card : ℂ) - 5) * (((S \ T).card : ℂ) - 6) / 720) *
        subsetCardSumInd n m k 0 (S \ T) o := funext (stratumExitInd_decomp_seven n m k (S \ T))
      rw [hfun, quarticSlotDiagExp_sub, quarticSlotDiagExp_add, quarticSlotDiagExp_sub,
        quarticSlotDiagExp_add, quarticSlotDiagExp_sub, quarticSlotDiagExp_add,
        quarticSlotDiagExp_sub, quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul,
        quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul,
        quarticSlotDiagExp_const_mul, hself, h6, h5, h4, h3, h2, h1, h0, hr]
      simp only [octicOccupancyTail]; push_cast; ring
    · have hr7 : 7 ≤ r := (by omega)
      have h7 : quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 7 (S \ T)) = ((r : ℂ) * ((r :
        ℂ) - 1) * ((r : ℂ) - 2) * ((r : ℂ) - 3) * ((r : ℂ) - 4) * ((r : ℂ) - 5) * ((r : ℂ) - 6) /
        5040) * (1 - ((r : ℝ) - 7) / (r : ℝ) * multiP_succ K r (2 ^ n) : ℂ) ^ (activeSlots m k)
        := by
        have h := slotDiagExp_subsetCardSumInd (n := n) (m := m) (k := k) hr7 hTS hr K
        dsimp only at h; change quarticSlotDiagExp n m k S T K (subsetCardSumInd n m k 7 (S \ T)) =
          _ at h; rw [h, choose_seven_cast_complex r]; congr 2
      have hfun : stratumExitInd n m k 8 (S \ T) = fun o ↦ (((((((validAllInd n m k (S \ T) o -
        subsetCardSumInd n m k 7 (S \ T) o) + (((S \ T).card : ℂ) - 7) * subsetCardSumInd n m k 6 (S
        \ T) o) - ((((S \ T).card : ℂ) - 6) * (((S \ T).card : ℂ) - 7) / 2) * subsetCardSumInd n m k
        5 (S \ T) o) + ((((S \ T).card : ℂ) - 5) * (((S \ T).card : ℂ) - 6) * (((S \ T).card : ℂ) -
        7) / 6) * subsetCardSumInd n m k 4 (S \ T) o) - ((((S \ T).card : ℂ) - 4) * (((S \ T).card :
        ℂ) - 5) * (((S \ T).card : ℂ) - 6) * (((S \ T).card : ℂ) - 7) / 24) * subsetCardSumInd n m k
        3 (S \ T) o) + ((((S \ T).card : ℂ) - 3) * (((S \ T).card : ℂ) - 4) * (((S \ T).card : ℂ) -
        5) * (((S \ T).card : ℂ) - 6) * (((S \ T).card : ℂ) - 7) / 120) * subsetCardSumInd n m k 2
        (S \ T) o) - ((((S \ T).card : ℂ) - 2) * (((S \ T).card : ℂ) - 3) * (((S \ T).card : ℂ) - 4)
        * (((S \ T).card : ℂ) - 5) * (((S \ T).card : ℂ) - 6) * (((S \ T).card : ℂ) - 7) / 720) *
        subsetCardSumInd n m k 1 (S \ T) o) + ((((S \ T).card : ℂ) - 1) * (((S \ T).card : ℂ) - 2) *
        (((S \ T).card : ℂ) - 3) * (((S \ T).card : ℂ) - 4) * (((S \ T).card : ℂ) - 5) * (((S \
        T).card : ℂ) - 6) * (((S \ T).card : ℂ) - 7) / 5040) * subsetCardSumInd n m k 0 (S \ T) o :=
        funext (stratumExitInd_decomp_eight n m k (S \ T)); rw [hfun, quarticSlotDiagExp_add,
        quarticSlotDiagExp_sub, quarticSlotDiagExp_add, quarticSlotDiagExp_sub,
        quarticSlotDiagExp_add, quarticSlotDiagExp_sub, quarticSlotDiagExp_add,
        quarticSlotDiagExp_sub, quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul,
        quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul,
        quarticSlotDiagExp_const_mul, quarticSlotDiagExp_const_mul, hself, h7, h6, h5, h4, h3, h2,
        h1, h0, hr]; simp only [octicOccupancyTail]; push_cast; ring
/-- Exact Markov recurrence for the seventh-order occupancy tail `octicOccupancyTail 7`. -/
theorem octicOccupancyTail_markov_seven {w r : ℕ} (hr1 : 1 ≤ r) (p : ℝ) :
    let α : ℝ := ((r : ℝ) - 6) / (r : ℝ)
    octicOccupancyTail 7 (w + 1) r p = (1 - α * p) * octicOccupancyTail 7 w r p + α * p *
      sexticOccupancyTail 6 w r p := by
  intro α; have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hr1))
  simp only [octicOccupancyTail, sexticOccupancyTail, α]; rw [pow_succ, pow_succ, pow_succ,
    pow_succ, pow_succ, pow_succ, pow_succ]; field_simp [hr_ne]; ring
/-- Exact Markov recurrence for the eighth-order occupancy tail `octicOccupancyTail 8`. -/
theorem octicOccupancyTail_markov_eight {w r : ℕ} (hr1 : 1 ≤ r) (p : ℝ) :
    let α : ℝ := ((r : ℝ) - 7) / (r : ℝ)
    octicOccupancyTail 8 (w + 1) r p = (1 - α * p) * octicOccupancyTail 8 w r p + α * p *
      octicOccupancyTail 7 w r p := by
  intro α; have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hr1))
  simp only [octicOccupancyTail, α]; rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_succ, pow_succ,
    pow_succ, pow_succ]; field_simp [hr_ne]; ring
/-- Non-negativity of sixth-order finite differences of `x ↦ x ^ w` on `[0, ∞)`. -/
theorem sixth_diff_pow_nonneg {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (w : ℕ) : 0 ≤ (a + 6 * δ) ^ w - 6
  * (a + 5 * δ) ^ w + 15 * (a + 4 * δ) ^ w - 20 * (a + 3 * δ) ^ w + 15 * (a + 2 * δ) ^ w - 6 * (a +
  δ) ^ w + a ^ w := by
  induction w with
  | zero => norm_num
  | succ w ih =>
    have hfd := fifth_diff_pow_nonneg ha hδ w
    have hid : (a + 6 * δ) ^ (w + 1) - 6 * (a + 5 * δ) ^ (w + 1) + 15 * (a + 4 * δ) ^ (w + 1) - 20 *
      (a + 3 * δ) ^ (w + 1) + 15 * (a + 2 * δ) ^ (w + 1) - 6 * (a + δ) ^ (w + 1) + a ^ (w + 1) = (a
      + 6 * δ) * ((a + 6 * δ) ^ w - 6 * (a + 5 * δ) ^ w + 15 * (a + 4 * δ) ^ w - 20 * (a + 3 * δ) ^
      w + 15 * (a + 2 * δ) ^ w - 6 * (a + δ) ^ w + a ^ w) + 6 * δ * ((a + 5 * δ) ^ w - 5 * (a + 4 *
      δ) ^ w + 10 * (a + 3 * δ) ^ w - 10 * (a + 2 * δ) ^ w + 5 * (a + δ) ^ w - a ^ w) := (by ring)
    rw [hid]; nlinarith
/-- Non-negativity of seventh-order finite differences of `x ↦ x ^ w` on `[0, ∞)`. -/
theorem seventh_diff_pow_nonneg {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (w : ℕ) : 0 ≤ (a + 7 * δ) ^ w -
  7 * (a + 6 * δ) ^ w + 21 * (a + 5 * δ) ^ w - 35 * (a + 4 * δ) ^ w + 35 * (a + 3 * δ) ^ w - 21 * (a
  + 2 * δ) ^ w + 7 * (a + δ) ^ w - a ^ w := by
  induction w with
  | zero => norm_num
  | succ w ih =>
    have hsd := sixth_diff_pow_nonneg ha hδ w
    have hid : (a + 7 * δ) ^ (w + 1) - 7 * (a + 6 * δ) ^ (w + 1) + 21 * (a + 5 * δ) ^ (w + 1) - 35 *
      (a + 4 * δ) ^ (w + 1) + 35 * (a + 3 * δ) ^ (w + 1) - 21 * (a + 2 * δ) ^ (w + 1) + 7 * (a + δ)
      ^ (w + 1) - a ^ (w + 1) = (a + 7 * δ) * ((a + 7 * δ) ^ w - 7 * (a + 6 * δ) ^ w + 21 * (a + 5 *
      δ) ^ w - 35 * (a + 4 * δ) ^ w + 35 * (a + 3 * δ) ^ w - 21 * (a + 2 * δ) ^ w + 7 * (a + δ) ^ w
      - a ^ w) + 7 * δ * ((a + 6 * δ) ^ w - 6 * (a + 5 * δ) ^ w + 15 * (a + 4 * δ) ^ w - 20 * (a + 3
      * δ) ^ w + 15 * (a + 2 * δ) ^ w - 6 * (a + δ) ^ w + a ^ w) := (by ring); rw [hid]; nlinarith
/-- Monotonicity in stride order: `octicOccupancyTail 7 w r p ≤ sexticOccupancyTail 6 w r
  p`. -/
theorem octicOccupancyTail_seven_le_six {w r : ℕ} (hr7 : 7 ≤ r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
  : octicOccupancyTail 7 w r p ≤ sexticOccupancyTail 6 w r p := by
  have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r)); have hr_ne : (r : ℝ) ≠ 0 :=
    hr_pos.ne'; simp only [octicOccupancyTail, sexticOccupancyTail]
  let a : ℝ := 1 - p; let δ : ℝ := p / (r : ℝ)
  have ha1 : 1 - ((r : ℝ) - 1) / (r : ℝ) * p = a + δ := (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha2 : 1 - ((r : ℝ) - 2) / (r : ℝ) * p = a + 2 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha3 : 1 - ((r : ℝ) - 3) / (r : ℝ) * p = a + 3 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha4 : 1 - ((r : ℝ) - 4) / (r : ℝ) * p = a + 4 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha5 : 1 - ((r : ℝ) - 5) / (r : ℝ) * p = a + 5 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha6 : 1 - ((r : ℝ) - 6) / (r : ℝ) * p = a + 6 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring); have ha0 : 1 - p = a := rfl; rw [ha1, ha2, ha3,
    ha4, ha5, ha6, ha0]; have hr7_r : (7 : ℝ) ≤ r := (by exact_mod_cast hr7)
  have hcoeff : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r :
    ℝ) - 5) / 720 := by
    have : 0 ≤ (r : ℝ) - 1 := (by linarith); have : 0 ≤ (r : ℝ) - 2 := (by linarith); have : 0 ≤ (r
      : ℝ) - 3 := (by linarith); have : 0 ≤ (r : ℝ) - 4 := (by linarith); have : 0 ≤ (r : ℝ) - 5 :=
      (by linarith); positivity
  have hsd := sixth_diff_pow_nonneg (a := a) (δ := δ) (by dsimp [a]; linarith) (div_nonneg hp0
    hr_pos.le) w; have hid : (1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r :
    ℝ) - 4) / 120) * (a + 5 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) *
    ((r : ℝ) - 5) / 24) * (a + 4 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4)
    * ((r : ℝ) - 5) / 12) * (a + 3 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) * ((r : ℝ) -
    4) * ((r : ℝ) - 5) / 12) * (a + 2 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ)
    - 4) * ((r : ℝ) - 5) / 24) * (a + δ) ^ w + (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r
    : ℝ) - 4) * ((r : ℝ) - 5) / 120) * a ^ w) - (1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r
    : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 720) * (a + 6 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) *
    ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 6) / 120) * (a + 5 * δ) ^ w - ((r :
    ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 5) * ((r : ℝ) - 6) / 48) * (a +
    4 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ)
    - 6) / 36) * (a + 3 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r :
    ℝ) - 5) * ((r : ℝ) - 6) / 48) * (a + 2 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r
    : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) / 120) * (a + δ) ^ w - (((r : ℝ) - 1) * ((r : ℝ) - 2)
    * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) / 720) * a ^ w) = ((r : ℝ) * ((r
    : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) / 720) * ((a + 6 * δ)
    ^ w - 6 * (a + 5 * δ) ^ w + 15 * (a + 4 * δ) ^ w - 20 * (a + 3 * δ) ^ w + 15 * (a + 2 * δ) ^ w -
    6 * (a + δ) ^ w + a ^ w) := (by ring); have hprod := mul_nonneg hcoeff hsd; linarith
/-- Monotonicity in stride order: `octicOccupancyTail 8 w r p ≤ octicOccupancyTail 7 w r p`. -/
theorem octicOccupancyTail_eight_le_seven {w r : ℕ} (hr8 : 8 ≤ r) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤
  1) : octicOccupancyTail 8 w r p ≤ octicOccupancyTail 7 w r p := by
  have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast (by omega : 0 < r)); have hr_ne : (r : ℝ) ≠ 0 :=
    hr_pos.ne'; simp only [octicOccupancyTail]
  let a : ℝ := 1 - p; let δ : ℝ := p / (r : ℝ)
  have ha1 : 1 - ((r : ℝ) - 1) / (r : ℝ) * p = a + δ := (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha2 : 1 - ((r : ℝ) - 2) / (r : ℝ) * p = a + 2 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha3 : 1 - ((r : ℝ) - 3) / (r : ℝ) * p = a + 3 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha4 : 1 - ((r : ℝ) - 4) / (r : ℝ) * p = a + 4 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha5 : 1 - ((r : ℝ) - 5) / (r : ℝ) * p = a + 5 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha6 : 1 - ((r : ℝ) - 6) / (r : ℝ) * p = a + 6 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring)
  have ha7 : 1 - ((r : ℝ) - 7) / (r : ℝ) * p = a + 7 * δ :=
    (by dsimp [a, δ]; field_simp [hr_ne]; ring); have ha0 : 1 - p = a := rfl; rw [ha1, ha2, ha3,
    ha4, ha5, ha6, ha7, ha0]; have hr8_r : (8 : ℝ) ≤ r := (by exact_mod_cast hr8)
  have hcoeff : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r :
    ℝ) - 5) * ((r : ℝ) - 6) / 5040 := by
    have : 0 ≤ (r : ℝ) - 1 := (by linarith); have : 0 ≤ (r : ℝ) - 2 := (by linarith); have : 0 ≤ (r
      : ℝ) - 3 := (by linarith); have : 0 ≤ (r : ℝ) - 4 := (by linarith); have : 0 ≤ (r : ℝ) - 5 :=
      (by linarith); have : 0 ≤ (r : ℝ) - 6 := (by linarith); positivity
  have hsd := seventh_diff_pow_nonneg (a := a) (δ := δ) (by dsimp [a]; linarith) (div_nonneg hp0
    hr_pos.le) w; have hid : (1 - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r :
    ℝ) - 4) * ((r : ℝ) - 5) / 720) * (a + 6 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) *
    ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 6) / 120) * (a + 5 * δ) ^ w - ((r : ℝ) * ((r : ℝ) -
    1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 5) * ((r : ℝ) - 6) / 48) * (a + 4 * δ) ^ w + ((r
    : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) / 36) * (a
    + 3 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r :
    ℝ) - 6) / 48) * (a + 2 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r
    : ℝ) - 5) * ((r : ℝ) - 6) / 120) * (a + δ) ^ w - (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3)
    * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) / 720) * a ^ w) - (1 - ((r : ℝ) * ((r : ℝ) - 1)
    * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) / 5040) * (a + 7
    * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) -
    5) * ((r : ℝ) - 7) / 720) * (a + 6 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r :
    ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 6) * ((r : ℝ) - 7) / 240) * (a + 5 * δ) ^ w + ((r : ℝ) *
    ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 5) * ((r : ℝ) - 6) * ((r : ℝ) - 7) /
    144) * (a + 4 * δ) ^ w - ((r : ℝ) * ((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 4) * ((r : ℝ) -
    5) * ((r : ℝ) - 6) * ((r : ℝ) - 7) / 144) * (a + 3 * δ) ^ w + ((r : ℝ) * ((r : ℝ) - 1) * ((r :
    ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) * ((r : ℝ) - 7) / 240) * (a + 2 * δ) ^ w
    - ((r : ℝ) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) * ((r
    : ℝ) - 7) / 720) * (a + δ) ^ w + (((r : ℝ) - 1) * ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4)
    * ((r : ℝ) - 5) * ((r : ℝ) - 6) * ((r : ℝ) - 7) / 5040) * a ^ w) = ((r : ℝ) * ((r : ℝ) - 1) *
    ((r : ℝ) - 2) * ((r : ℝ) - 3) * ((r : ℝ) - 4) * ((r : ℝ) - 5) * ((r : ℝ) - 6) / 5040) * ((a + 7
    * δ) ^ w - 7 * (a + 6 * δ) ^ w + 21 * (a + 5 * δ) ^ w - 35 * (a + 4 * δ) ^ w + 35 * (a + 3 * δ)
    ^ w - 21 * (a + 2 * δ) ^ w + 7 * (a + δ) ^ w - a ^ w) := (by ring)
  have hprod := mul_nonneg hcoeff hsd; linarith
private lemma s8_tail_six_bounds {w r : ℕ} (hr6 : 6 ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤
  p₂) (hp2 : p₂ ≤ 1) : 0 ≤ sexticOccupancyTail 6 w r p₁ ∧ sexticOccupancyTail 6 w r p₁ ≤
  sexticOccupancyTail 6 w r p₂ ∧ sexticOccupancyTail 6 w r p₂ ≤ 1 := by
  rcases lt_or_ge w 6 with hwlt | hw6
  · have hr_ne : (r : ℝ) ≠ 0 := (by exact_mod_cast (by omega : r ≠ 0))
    have h0 (p : ℝ) : sexticOccupancyTail 6 w r p = 0 := by
      interval_cases w
      · simp only [sexticOccupancyTail, pow_zero]; ring
      · simp only [sexticOccupancyTail, pow_one]; field_simp [hr_ne]; ring
      · simp only [sexticOccupancyTail]; field_simp [hr_ne]; ring
      · simp only [sexticOccupancyTail]; field_simp [hr_ne]; ring
      · simp only [sexticOccupancyTail]; field_simp [hr_ne]; ring
      · simp only [sexticOccupancyTail]; field_simp [hr_ne]; ring
    rw [h0 p₁, h0 p₂]; exact ⟨le_rfl, le_rfl, zero_le_one⟩
  · rcases sexticOccupancyTail_pos_and_mono (s := 6) (w := w) (r := r) (by omega) (by omega) hw6 hr6
      hp1 hp12 hp2 with ⟨hpos, hmono, hle1⟩; exact ⟨hpos.le, hmono, hle1⟩
private lemma s8_tail_seven_nonneg {w r : ℕ} (hr7 : 7 ≤ r) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : 0
  ≤ octicOccupancyTail 7 w r p := by
  have hr1 : 1 ≤ r := (by omega); have hr6 : 6 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr7_r : (7 : ℝ) ≤ r := (by exact_mod_cast hr7)
  let α : ℝ := ((r : ℝ) - 6) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
  have hαp0 : 0 ≤ α * p := mul_nonneg hα0 hp0.le; have hαp1 : α * p ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 : octicOccupancyTail 7 0 r p = 0 := (by simp only [octicOccupancyTail, pow_zero]; ring)
    rw [h0]
  | succ w ih =>
    have hm := octicOccupancyTail_markov_seven (w := w) hr1 p; dsimp only at hm
    change octicOccupancyTail 7 (w + 1) r p = (1 - α * p) * octicOccupancyTail 7 w r p + α * p *
      sexticOccupancyTail 6 w r p at hm; rw [hm]; have h6_0 := (s8_tail_six_bounds (w := w) hr6 hp0
      le_rfl hp1).1; nlinarith
private lemma s8_tail_seven_mono {w r : ℕ} (hr7 : 7 ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤
  p₂) (hp2 : p₂ ≤ 1) : octicOccupancyTail 7 w r p₁ ≤ octicOccupancyTail 7 w r p₂ := by
  have hr1 : 1 ≤ r := (by omega); have hr6 : 6 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr7_r : (7 : ℝ) ≤ r := (by exact_mod_cast hr7)
  let α : ℝ := ((r : ℝ) - 6) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith); have hp2_0 : 0 ≤ p₂ := hp1.le.trans hp12;
    have hαp2_0 : 0 ≤ α * p₂ := mul_nonneg hα0 hp2_0; have hαp2_1 : α * p₂ ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 (p : ℝ) : octicOccupancyTail 7 0 r p = 0 :=
      (by simp only [octicOccupancyTail, pow_zero]; ring); rw [h0, h0]
  | succ w ih =>
    have hm1 := octicOccupancyTail_markov_seven (w := w) hr1 p₁; have hm2 :=
      octicOccupancyTail_markov_seven (w := w) hr1 p₂; dsimp only at hm1 hm2
    change octicOccupancyTail 7 (w + 1) r p₁ = (1 - α * p₁) * octicOccupancyTail 7 w r p₁ + α * p₁ *
      sexticOccupancyTail 6 w r p₁ at hm1; change octicOccupancyTail 7 (w + 1) r p₂ = (1 - α * p₂) *
      octicOccupancyTail 7 w r p₂ + α * p₂ * sexticOccupancyTail 6 w r p₂ at hm2; rw [hm1, hm2];
      have h6_mono := (s8_tail_six_bounds (w := w) hr6 hp1 hp12 hp2).2.1; have h7_le_6 :=
      octicOccupancyTail_seven_le_six (w := w) hr7 hp1.le (hp12.trans hp2); have hid : ((1 - α * p₂)
      * octicOccupancyTail 7 w r p₂ + α * p₂ * sexticOccupancyTail 6 w r p₂) - ((1 - α * p₁) *
      octicOccupancyTail 7 w r p₁ + α * p₁ * sexticOccupancyTail 6 w r p₁) = (1 - α * p₂) *
      (octicOccupancyTail 7 w r p₂ - octicOccupancyTail 7 w r p₁) + α * p₂ * (sexticOccupancyTail 6
      w r p₂ - sexticOccupancyTail 6 w r p₁) + α * (p₂ - p₁) * (sexticOccupancyTail 6 w r p₁ -
      octicOccupancyTail 7 w r p₁) := (by ring); have ht1 : 0 ≤ (1 - α * p₂) * (octicOccupancyTail 7
      w r p₂ - octicOccupancyTail 7 w r p₁) := mul_nonneg (by linarith) (by linarith)
    have ht2 : 0 ≤ α * p₂ * (sexticOccupancyTail 6 w r p₂ - sexticOccupancyTail 6 w r p₁) :=
      mul_nonneg hαp2_0 (by linarith); have ht3 : 0 ≤ α * (p₂ - p₁) * (sexticOccupancyTail 6 w r p₁
      - octicOccupancyTail 7 w r p₁) := mul_nonneg (mul_nonneg hα0 (by linarith)) (by linarith)
    linarith
private lemma s8_tail_eight_nonneg {w r : ℕ} (hr8 : 8 ≤ r) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : 0
  ≤ octicOccupancyTail 8 w r p := by
  have hr1 : 1 ≤ r := (by omega); have hr7 : 7 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr8_r : (8 : ℝ) ≤ r := (by exact_mod_cast hr8)
  let α : ℝ := ((r : ℝ) - 7) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
  have hαp0 : 0 ≤ α * p := mul_nonneg hα0 hp0.le; have hαp1 : α * p ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 : octicOccupancyTail 8 0 r p = 0 := (by simp only [octicOccupancyTail, pow_zero]; ring)
    rw [h0]
  | succ w ih =>
    have hm := octicOccupancyTail_markov_eight (w := w) hr1 p; dsimp only at hm
    change octicOccupancyTail 8 (w + 1) r p = (1 - α * p) * octicOccupancyTail 8 w r p + α * p *
      octicOccupancyTail 7 w r p at hm
    rw [hm]; have h7_0 := s8_tail_seven_nonneg (w := w) hr7 hp0 hp1; nlinarith
private lemma s8_tail_eight_mono {w r : ℕ} (hr8 : 8 ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤
  p₂) (hp2 : p₂ ≤ 1) : octicOccupancyTail 8 w r p₁ ≤ octicOccupancyTail 8 w r p₂ := by
  have hr1 : 1 ≤ r := (by omega); have hr7 : 7 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
    (by exact_mod_cast hr1); have hr8_r : (8 : ℝ) ≤ r := (by exact_mod_cast hr8)
  let α : ℝ := ((r : ℝ) - 7) / (r : ℝ); have hα0 : 0 ≤ α := div_nonneg (by linarith) hr_pos.le
  have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith); have hp2_0 : 0 ≤ p₂ := hp1.le.trans hp12;
    have hαp2_0 : 0 ≤ α * p₂ := mul_nonneg hα0 hp2_0; have hαp2_1 : α * p₂ ≤ 1 := (by nlinarith)
  induction w with
  | zero =>
    have h0 (p : ℝ) : octicOccupancyTail 8 0 r p = 0 :=
      (by simp only [octicOccupancyTail, pow_zero]; ring); rw [h0, h0]
  | succ w ih =>
    have hm1 := octicOccupancyTail_markov_eight (w := w) hr1 p₁; have hm2 :=
      octicOccupancyTail_markov_eight (w := w) hr1 p₂; dsimp only at hm1 hm2
    change octicOccupancyTail 8 (w + 1) r p₁ = (1 - α * p₁) * octicOccupancyTail 8 w r p₁ + α * p₁ *
      octicOccupancyTail 7 w r p₁ at hm1; change octicOccupancyTail 8 (w + 1) r p₂ = (1 - α * p₂) *
      octicOccupancyTail 8 w r p₂ + α * p₂ * octicOccupancyTail 7 w r p₂ at hm2
    rw [hm1, hm2]; have h7_mono := s8_tail_seven_mono (w := w) hr7 hp1 hp12 hp2; have h8_le_7 :=
      octicOccupancyTail_eight_le_seven (w := w) hr8 hp1.le (hp12.trans hp2); have hid : ((1 - α *
      p₂) * octicOccupancyTail 8 w r p₂ + α * p₂ * octicOccupancyTail 7 w r p₂) - ((1 - α * p₁) *
      octicOccupancyTail 8 w r p₁ + α * p₁ * octicOccupancyTail 7 w r p₁) = (1 - α * p₂) *
      (octicOccupancyTail 8 w r p₂ - octicOccupancyTail 8 w r p₁) + α * p₂ * (octicOccupancyTail 7 w
      r p₂ - octicOccupancyTail 7 w r p₁) + α * (p₂ - p₁) * (octicOccupancyTail 7 w r p₁ -
      octicOccupancyTail 8 w r p₁) := (by ring); have ht1 : 0 ≤ (1 - α * p₂) * (octicOccupancyTail 8
      w r p₂ - octicOccupancyTail 8 w r p₁) := mul_nonneg (by linarith) (by linarith)
    have ht2 : 0 ≤ α * p₂ * (octicOccupancyTail 7 w r p₂ - octicOccupancyTail 7 w r p₁) :=
      mul_nonneg hαp2_0 (by linarith); have ht3 : 0 ≤ α * (p₂ - p₁) * (octicOccupancyTail 7 w r p₁ -
      octicOccupancyTail 8 w r p₁) := mul_nonneg (mul_nonneg hα0 (by linarith)) (by linarith)
    linarith
/-- Positivity, monotonicity in `p ∈ (0, 1]`, and upper bound `≤ 1` for `octicOccupancyTail
  s w r p`
  across all `1 ≤ s ≤ 8`. -/
theorem octicOccupancyTail_pos_and_mono {s w r : ℕ} (hs1 : 1 ≤ s) (hs8 : s ≤ 8) (hsw : s ≤ w) (hsr :
  s ≤ r) {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ ≤ p₂) (hp2 : p₂ ≤ 1) : 0 < octicOccupancyTail s w r
  p₁ ∧ octicOccupancyTail s w r p₁ ≤ octicOccupancyTail s w r p₂ ∧ octicOccupancyTail s w r p₂ ≤ 1
  := by
  rcases le_or_gt s 6 with hs6 | hs_gt6
  · have h_eq (p : ℝ) : octicOccupancyTail s w r p = sexticOccupancyTail s w r p := by
      rcases s with _ | _ | _ | _ | _ | _ | _ | s <;> try omega
      all_goals rfl
    rw [h_eq p₁, h_eq p₂]; exact sexticOccupancyTail_pos_and_mono hs1 hs6 hsw hsr hp1 hp12 hp2
  · have hp2_pos : 0 < p₂ := hp1.trans_le hp12; have hp1_le1 : p₁ ≤ 1 := hp12.trans hp2
    have hr6 : 6 ≤ r := (by omega); have h6_le1 := (s8_tail_six_bounds (w := w) hr6 hp2_pos le_rfl
      hp2).2.2
    interval_cases s
    · refine ⟨?_, s8_tail_seven_mono hsr hp1 hp12 hp2, (octicOccupancyTail_seven_le_six hsr
        hp2_pos.le hp2).trans h6_le1⟩; rcases Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0) with
        ⟨w', rfl⟩; have hr1 : 1 ≤ r := (by omega); have hr_pos : 0 < (r : ℝ) :=
        (by exact_mod_cast hr1); have hr7_r : (7 : ℝ) ≤ r := (by exact_mod_cast hsr)
      let α : ℝ := ((r : ℝ) - 6) / (r : ℝ); have hα_pos : 0 < α := div_pos (by linarith) hr_pos
      have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
      have hαp_pos : 0 < α * p₁ := mul_pos hα_pos hp1; have hαp_le1 : α * p₁ ≤ 1 := (by nlinarith)
      have hm := octicOccupancyTail_markov_seven (w := w') hr1 p₁; dsimp only at hm
      change octicOccupancyTail 7 (w' + 1) r p₁ = (1 - α * p₁) * octicOccupancyTail 7 w' r p₁ + α *
        p₁ * sexticOccupancyTail 6 w' r p₁ at hm; rw [hm]; have h7_0 := s8_tail_seven_nonneg (w :=
        w') hsr hp1 hp1_le1; have h6_pos := (sexticOccupancyTail_pos_and_mono (s := 6) (w := w') (r
        := r) (by omega) (by omega) (by omega) (by omega) hp1 le_rfl hp1_le1).1; nlinarith
    · have hr7 : 7 ≤ r := (by omega)
      have h7_le_6 := octicOccupancyTail_seven_le_six (w := w) hr7 hp2_pos.le hp2; have h8_le_7 :=
        octicOccupancyTail_eight_le_seven (w := w) hsr hp2_pos.le hp2; refine ⟨?_,
        s8_tail_eight_mono hsr hp1 hp12 hp2, (h8_le_7.trans h7_le_6).trans h6_le1⟩
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0) with ⟨w', rfl⟩; have hr1 : 1 ≤ r :=
        (by omega); have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
      have hr8_r : (8 : ℝ) ≤ r := (by exact_mod_cast hsr); let α : ℝ := ((r : ℝ) - 7) / (r : ℝ)
      have hα_pos : 0 < α := div_pos (by linarith) hr_pos
      have hα1 : α ≤ 1 := (div_le_one hr_pos).2 (by linarith)
      have hαp_pos : 0 < α * p₁ := mul_pos hα_pos hp1; have hαp_le1 : α * p₁ ≤ 1 := (by nlinarith)
      have hm := octicOccupancyTail_markov_eight (w := w') hr1 p₁; dsimp only at hm
      change octicOccupancyTail 8 (w' + 1) r p₁ = (1 - α * p₁) * octicOccupancyTail 8 w' r p₁ + α *
        p₁ * octicOccupancyTail 7 w' r p₁ at hm; rw [hm]; have h8_0 := s8_tail_eight_nonneg (w :=
        w') hsr hp1 hp1_le1; rcases Nat.exists_eq_succ_of_ne_zero (by omega : w' ≠ 0) with ⟨w'',
        rfl⟩
      let β : ℝ := ((r : ℝ) - 6) / (r : ℝ); have hβ_pos : 0 < β := div_pos (by linarith) hr_pos
      have hβ1 : β ≤ 1 := (div_le_one hr_pos).2 (by linarith)
      have hβp_pos : 0 < β * p₁ := mul_pos hβ_pos hp1; have hβp_le1 : β * p₁ ≤ 1 := (by nlinarith)
      have hm7 := octicOccupancyTail_markov_seven (w := w'') hr1 p₁; dsimp only at hm7
      change octicOccupancyTail 7 (w'' + 1) r p₁ = (1 - β * p₁) * octicOccupancyTail 7 w'' r p₁ + β
        * p₁ * sexticOccupancyTail 6 w'' r p₁ at hm7
      have h7_0' := s8_tail_seven_nonneg (w := w'') hr7 hp1 hp1_le1; have h6_pos :=
        (sexticOccupancyTail_pos_and_mono (s := 6) (w := w'') (r := r) (by omega) (by omega)
        (by omega) (by omega) hp1 le_rfl hp1_le1).1; have h7_pos : 0 < octicOccupancyTail 7 (w'' +
        1) r p₁ := (by rw [hm7]; nlinarith); nlinarith
end QuantumComputation.Specs
end
end Sec_OcticOccupancyMarkov
section Sec_SexticStratumSchedule
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal NNRat
/-- Predicate selecting the supported `(m, r)` stage grid (`1..10` box plus dyadic `m ∈
  {1,2,4,8,16,32}, r ≤ 32`). -/
def isSupportedMR (m r : ℕ) : Bool :=
  decide (((1 ≤ m ∧ m ≤ 10) ∧ (1 ≤ r ∧ r ≤ 10)) ∨
    ((m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 8 ∨ m = 16 ∨ m = 32) ∧ (1 ≤ r ∧ r ≤ 32)))
lemma isSupportedMR_of_le {m r k : ℕ} (h : isSupportedMR m k = true) (hr1 : 1 ≤ r) (hrk : r ≤ k) :
  isSupportedMR m r = true := by
  unfold isSupportedMR at h ⊢; simp only [decide_eq_true_eq] at h ⊢; omega
lemma bounds_of_isSupportedMR {m r : ℕ} (h : isSupportedMR m r = true) : 1 ≤ m ∧ m ≤ 32 ∧ 1 ≤ r ∧ r
  ≤ 32 := by unfold isSupportedMR at h; simp only [decide_eq_true_eq] at h; omega
/-- 10 × 10 stratum-1 threshold table `sexticStratum1Grid w r` (`s1 ∈ {1..8}`). -/
def sexticStratum1Grid (w r : ℕ) : ℕ :=
  match w, r with
  | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 1, 6 => 1 | 1, 7 => 1 | 1, 8 => 1 | 1, 9 => 1 | 1, 10 => 1
  | 2, 1 => 1 | 2, 2 => 1 | 2, 3 => 1 | 2, 4 => 1 | 2, 5 => 1
  | 2, 6 => 1 | 2, 7 => 1 | 2, 8 => 1 | 2, 9 => 1 | 2, 10 => 1
  | 3, 1 => 1 | 3, 2 => 1 | 3, 3 => 1 | 3, 4 => 1 | 3, 5 => 1
  | 3, 6 => 1 | 3, 7 => 1 | 3, 8 => 1 | 3, 9 => 1 | 3, 10 => 1
  | 4, 1 => 1 | 4, 2 => 1 | 4, 3 => 1 | 4, 4 => 1 | 4, 5 => 1
  | 4, 6 => 1 | 4, 7 => 1 | 4, 8 => 1 | 4, 9 => 1 | 4, 10 => 1
  | 5, 1 => 1 | 5, 2 => 1 | 5, 3 => 1 | 5, 4 => 1 | 5, 5 => 1
  | 5, 6 => 1 | 5, 7 => 1 | 5, 8 => 1 | 5, 9 => 1 | 5, 10 => 1
  | 6, 1 => 1 | 6, 2 => 1 | 6, 3 => 1 | 6, 4 => 1 | 6, 5 => 1
  | 6, 6 => 1 | 6, 7 => 1 | 6, 8 => 1 | 6, 9 => 1 | 6, 10 => 1
  | 7, 1 => 1 | 7, 2 => 1 | 7, 3 => 1 | 7, 4 => 1 | 7, 5 => 1
  | 7, 6 => 1 | 7, 7 => 2 | 7, 8 => 2 | 7, 9 => 2 | 7, 10 => 2
  | 8, 1 => 1 | 8, 2 => 1 | 8, 3 => 1 | 8, 4 => 1 | 8, 5 => 1
  | 8, 6 => 1 | 8, 7 => 2 | 8, 8 => 2 | 8, 9 => 2 | 8, 10 => 2
  | 9, 1 => 1 | 9, 2 => 1 | 9, 3 => 1 | 9, 4 => 1 | 9, 5 => 1
  | 9, 6 => 1 | 9, 7 => 2 | 9, 8 => 2 | 9, 9 => 3 | 9, 10 => 3
  | 10, 1 => 1 | 10, 2 => 1 | 10, 3 => 1 | 10, 4 => 1 | 10, 5 => 1
  | 10, 6 => 1 | 10, 7 => 2 | 10, 8 => 2 | 10, 9 => 3 | 10, 10 => 3
  | 2, 11 => 1 | 2, 12 => 1 | 2, 13 => 1 | 2, 14 => 1 | 2, 15 => 1
  | 2, 16 => 1 | 2, 17 => 1 | 2, 18 => 1 | 2, 19 => 1 | 2, 20 => 1
  | 2, 21 => 1 | 2, 22 => 1 | 2, 23 => 1 | 2, 24 => 1 | 2, 25 => 1
  | 2, 26 => 1 | 2, 27 => 1 | 2, 28 => 1 | 2, 29 => 1 | 2, 30 => 1
  | 2, 31 => 1 | 2, 32 => 1 | 4, 11 => 1 | 4, 12 => 1 | 4, 13 => 1
  | 4, 14 => 1 | 4, 15 => 1 | 4, 16 => 1 | 4, 17 => 1 | 4, 18 => 1
  | 4, 19 => 1 | 4, 20 => 1 | 4, 21 => 1 | 4, 22 => 1 | 4, 23 => 1
  | 4, 24 => 1 | 4, 25 => 1 | 4, 26 => 1 | 4, 27 => 1 | 4, 28 => 1
  | 4, 29 => 1 | 4, 30 => 1 | 4, 31 => 1 | 4, 32 => 1 | 8, 11 => 3
  | 8, 12 => 3 | 8, 13 => 3 | 8, 14 => 3 | 8, 15 => 3 | 8, 16 => 3
  | 8, 17 => 3 | 8, 18 => 3 | 8, 19 => 3 | 8, 20 => 3 | 8, 21 => 3
  | 8, 22 => 3 | 8, 23 => 3 | 8, 24 => 3 | 8, 25 => 3 | 8, 26 => 3
  | 8, 27 => 3 | 8, 28 => 3 | 8, 29 => 3 | 8, 30 => 3 | 8, 31 => 3
  | 8, 32 => 3 | 16, 1 => 1 | 16, 2 => 1 | 16, 3 => 1 | 16, 4 => 1
  | 16, 5 => 1 | 16, 6 => 1 | 16, 7 => 2 | 16, 8 => 3 | 16, 9 => 3
  | 16, 10 => 3 | 16, 11 => 3 | 16, 12 => 3 | 16, 13 => 3 | 16, 14 => 3
  | 16, 15 => 3 | 16, 16 => 3 | 16, 17 => 3 | 16, 18 => 3 | 16, 19 => 3
  | 16, 20 => 3 | 16, 21 => 3 | 16, 22 => 3 | 16, 23 => 3 | 16, 24 => 3
  | 16, 25 => 3 | 16, 26 => 3 | 16, 27 => 3 | 16, 28 => 3 | 16, 29 => 3
  | 16, 30 => 3 | 16, 31 => 3 | 16, 32 => 3 | 32, 1 => 1 | 32, 2 => 1
  | 32, 3 => 1 | 32, 4 => 1 | 32, 5 => 1 | 32, 6 => 1 | 32, 7 => 2
  | 32, 8 => 3 | 32, 9 => 3 | 32, 10 => 3 | 32, 11 => 3 | 32, 12 => 3
  | 32, 13 => 3 | 32, 14 => 3 | 32, 15 => 3 | 32, 16 => 3 | 32, 17 => 3
  | 32, 18 => 3 | 32, 19 => 3 | 32, 20 => 3 | 32, 21 => 3 | 32, 22 => 3
  | 32, 23 => 3 | 32, 24 => 3 | 32, 25 => 3 | 32, 26 => 3 | 32, 27 => 3
  | 32, 28 => 3 | 32, 29 => 3 | 32, 30 => 3 | 32, 31 => 3 | 32, 32 => 3
  | _, _ => 1
/-- Stratum-1 loop exit threshold `sexticStratum1 w r`. -/
def sexticStratum1 (w r : ℕ) : ℕ :=
  if isSupportedMR w r = true ∧ 2 ≤ w then sexticStratum1Grid w r else 1
/-- 10 × 10 stratum-2 threshold table `sexticStratum2Grid w r` (`s2 ∈ {1..8}`). -/
def sexticStratum2Grid (w r : ℕ) : ℕ :=
  match w, r with
  | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 1, 6 => 1 | 1, 7 => 1 | 1, 8 => 1 | 1, 9 => 1 | 1, 10 => 1
  | 2, 1 => 1 | 2, 2 => 2 | 2, 3 => 2 | 2, 4 => 2 | 2, 5 => 2
  | 2, 6 => 2 | 2, 7 => 2 | 2, 8 => 2 | 2, 9 => 2 | 2, 10 => 2
  | 3, 1 => 1 | 3, 2 => 2 | 3, 3 => 2 | 3, 4 => 2 | 3, 5 => 2
  | 3, 6 => 2 | 3, 7 => 2 | 3, 8 => 2 | 3, 9 => 2 | 3, 10 => 2
  | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 2 | 4, 4 => 2 | 4, 5 => 2
  | 4, 6 => 2 | 4, 7 => 2 | 4, 8 => 2 | 4, 9 => 2 | 4, 10 => 2
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 2 | 5, 4 => 2 | 5, 5 => 2
  | 5, 6 => 2 | 5, 7 => 2 | 5, 8 => 2 | 5, 9 => 2 | 5, 10 => 2
  | 6, 1 => 1 | 6, 2 => 2 | 6, 3 => 2 | 6, 4 => 2 | 6, 5 => 2
  | 6, 6 => 2 | 6, 7 => 2 | 6, 8 => 2 | 6, 9 => 2 | 6, 10 => 2
  | 7, 1 => 1 | 7, 2 => 2 | 7, 3 => 2 | 7, 4 => 2 | 7, 5 => 2
  | 7, 6 => 2 | 7, 7 => 3 | 7, 8 => 3 | 7, 9 => 3 | 7, 10 => 3
  | 8, 1 => 1 | 8, 2 => 2 | 8, 3 => 2 | 8, 4 => 2 | 8, 5 => 2
  | 8, 6 => 2 | 8, 7 => 3 | 8, 8 => 3 | 8, 9 => 3 | 8, 10 => 3
  | 9, 1 => 1 | 9, 2 => 2 | 9, 3 => 2 | 9, 4 => 2 | 9, 5 => 2
  | 9, 6 => 2 | 9, 7 => 3 | 9, 8 => 3 | 9, 9 => 4 | 9, 10 => 4
  | 10, 1 => 1 | 10, 2 => 2 | 10, 3 => 2 | 10, 4 => 2 | 10, 5 => 2
  | 10, 6 => 2 | 10, 7 => 3 | 10, 8 => 3 | 10, 9 => 4 | 10, 10 => 4
  | 2, 11 => 1 | 2, 12 => 1 | 2, 13 => 1 | 2, 14 => 1 | 2, 15 => 1
  | 2, 16 => 1 | 2, 17 => 1 | 2, 18 => 1 | 2, 19 => 1 | 2, 20 => 1
  | 2, 21 => 1 | 2, 22 => 1 | 2, 23 => 1 | 2, 24 => 1 | 2, 25 => 1
  | 2, 26 => 1 | 2, 27 => 1 | 2, 28 => 1 | 2, 29 => 1 | 2, 30 => 1
  | 2, 31 => 1 | 2, 32 => 1 | 4, 11 => 1 | 4, 12 => 1 | 4, 13 => 1
  | 4, 14 => 1 | 4, 15 => 1 | 4, 16 => 1 | 4, 17 => 1 | 4, 18 => 1
  | 4, 19 => 1 | 4, 20 => 1 | 4, 21 => 1 | 4, 22 => 1 | 4, 23 => 1
  | 4, 24 => 1 | 4, 25 => 1 | 4, 26 => 1 | 4, 27 => 1 | 4, 28 => 1
  | 4, 29 => 1 | 4, 30 => 1 | 4, 31 => 1 | 4, 32 => 1 | 8, 11 => 4
  | 8, 12 => 4 | 8, 13 => 4 | 8, 14 => 4 | 8, 15 => 4 | 8, 16 => 4
  | 8, 17 => 4 | 8, 18 => 4 | 8, 19 => 4 | 8, 20 => 4 | 8, 21 => 4
  | 8, 22 => 4 | 8, 23 => 4 | 8, 24 => 4 | 8, 25 => 4 | 8, 26 => 4
  | 8, 27 => 4 | 8, 28 => 4 | 8, 29 => 4 | 8, 30 => 4 | 8, 31 => 4
  | 8, 32 => 4 | 16, 1 => 1 | 16, 2 => 1 | 16, 3 => 1 | 16, 4 => 1
  | 16, 5 => 1 | 16, 6 => 2 | 16, 7 => 3 | 16, 8 => 4 | 16, 9 => 4
  | 16, 10 => 4 | 16, 11 => 4 | 16, 12 => 4 | 16, 13 => 4 | 16, 14 => 4
  | 16, 15 => 4 | 16, 16 => 4 | 16, 17 => 4 | 16, 18 => 4 | 16, 19 => 4
  | 16, 20 => 4 | 16, 21 => 4 | 16, 22 => 4 | 16, 23 => 4 | 16, 24 => 4
  | 16, 25 => 4 | 16, 26 => 4 | 16, 27 => 4 | 16, 28 => 4 | 16, 29 => 4
  | 16, 30 => 4 | 16, 31 => 4 | 16, 32 => 4 | 32, 1 => 1 | 32, 2 => 1
  | 32, 3 => 1 | 32, 4 => 1 | 32, 5 => 1 | 32, 6 => 2 | 32, 7 => 3
  | 32, 8 => 4 | 32, 9 => 4 | 32, 10 => 4 | 32, 11 => 4 | 32, 12 => 4
  | 32, 13 => 4 | 32, 14 => 4 | 32, 15 => 4 | 32, 16 => 4 | 32, 17 => 4
  | 32, 18 => 4 | 32, 19 => 4 | 32, 20 => 4 | 32, 21 => 4 | 32, 22 => 4
  | 32, 23 => 4 | 32, 24 => 4 | 32, 25 => 4 | 32, 26 => 4 | 32, 27 => 4
  | 32, 28 => 4 | 32, 29 => 4 | 32, 30 => 4 | 32, 31 => 4 | 32, 32 => 4
  | _, _ => 1
/-- Stratum-2 surplus threshold `sexticStratum2 w r`. -/
def sexticStratum2 (w r : ℕ) : ℕ :=
  if isSupportedMR w r = true ∧ 2 ≤ w then sexticStratum2Grid w r else 1
/-- 10 × 10 stratum-3 threshold table `sexticStratum3Grid w r` (`s3 ∈ {1..8}`). -/
def sexticStratum3Grid (w r : ℕ) : ℕ :=
  match w, r with
  | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 1, 6 => 1 | 1, 7 => 1 | 1, 8 => 1 | 1, 9 => 1 | 1, 10 => 1
  | 2, 1 => 1 | 2, 2 => 2 | 2, 3 => 2 | 2, 4 => 2 | 2, 5 => 2
  | 2, 6 => 2 | 2, 7 => 2 | 2, 8 => 2 | 2, 9 => 2 | 2, 10 => 2
  | 3, 1 => 1 | 3, 2 => 2 | 3, 3 => 3 | 3, 4 => 3 | 3, 5 => 3
  | 3, 6 => 3 | 3, 7 => 3 | 3, 8 => 3 | 3, 9 => 3 | 3, 10 => 3
  | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 3 | 4, 4 => 3 | 4, 5 => 3
  | 4, 6 => 3 | 4, 7 => 3 | 4, 8 => 3 | 4, 9 => 3 | 4, 10 => 3
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 3 | 5, 4 => 3 | 5, 5 => 3
  | 5, 6 => 3 | 5, 7 => 3 | 5, 8 => 3 | 5, 9 => 3 | 5, 10 => 3
  | 6, 1 => 1 | 6, 2 => 2 | 6, 3 => 3 | 6, 4 => 3 | 6, 5 => 3
  | 6, 6 => 3 | 6, 7 => 3 | 6, 8 => 3 | 6, 9 => 3 | 6, 10 => 3
  | 7, 1 => 1 | 7, 2 => 2 | 7, 3 => 3 | 7, 4 => 3 | 7, 5 => 3
  | 7, 6 => 3 | 7, 7 => 4 | 7, 8 => 4 | 7, 9 => 4 | 7, 10 => 4
  | 8, 1 => 1 | 8, 2 => 2 | 8, 3 => 3 | 8, 4 => 3 | 8, 5 => 3
  | 8, 6 => 3 | 8, 7 => 4 | 8, 8 => 4 | 8, 9 => 4 | 8, 10 => 4
  | 9, 1 => 1 | 9, 2 => 2 | 9, 3 => 3 | 9, 4 => 3 | 9, 5 => 3
  | 9, 6 => 3 | 9, 7 => 4 | 9, 8 => 4 | 9, 9 => 5 | 9, 10 => 5
  | 10, 1 => 1 | 10, 2 => 2 | 10, 3 => 3 | 10, 4 => 3 | 10, 5 => 3
  | 10, 6 => 3 | 10, 7 => 4 | 10, 8 => 4 | 10, 9 => 5 | 10, 10 => 5
  | 2, 11 => 1 | 2, 12 => 1 | 2, 13 => 1 | 2, 14 => 1 | 2, 15 => 1
  | 2, 16 => 1 | 2, 17 => 1 | 2, 18 => 1 | 2, 19 => 1 | 2, 20 => 1
  | 2, 21 => 1 | 2, 22 => 1 | 2, 23 => 1 | 2, 24 => 1 | 2, 25 => 1
  | 2, 26 => 1 | 2, 27 => 1 | 2, 28 => 1 | 2, 29 => 1 | 2, 30 => 1
  | 2, 31 => 1 | 2, 32 => 1 | 4, 11 => 1 | 4, 12 => 1 | 4, 13 => 1
  | 4, 14 => 1 | 4, 15 => 1 | 4, 16 => 1 | 4, 17 => 1 | 4, 18 => 1
  | 4, 19 => 1 | 4, 20 => 1 | 4, 21 => 1 | 4, 22 => 1 | 4, 23 => 1
  | 4, 24 => 1 | 4, 25 => 1 | 4, 26 => 1 | 4, 27 => 1 | 4, 28 => 1
  | 4, 29 => 1 | 4, 30 => 1 | 4, 31 => 1 | 4, 32 => 1 | 8, 11 => 5
  | 8, 12 => 5 | 8, 13 => 5 | 8, 14 => 5 | 8, 15 => 5 | 8, 16 => 5
  | 8, 17 => 5 | 8, 18 => 5 | 8, 19 => 5 | 8, 20 => 5 | 8, 21 => 5
  | 8, 22 => 5 | 8, 23 => 5 | 8, 24 => 5 | 8, 25 => 5 | 8, 26 => 5
  | 8, 27 => 5 | 8, 28 => 5 | 8, 29 => 5 | 8, 30 => 5 | 8, 31 => 5
  | 8, 32 => 5 | 16, 1 => 1 | 16, 2 => 1 | 16, 3 => 1 | 16, 4 => 1
  | 16, 5 => 2 | 16, 6 => 3 | 16, 7 => 4 | 16, 8 => 5 | 16, 9 => 5
  | 16, 10 => 5 | 16, 11 => 5 | 16, 12 => 5 | 16, 13 => 5 | 16, 14 => 5
  | 16, 15 => 5 | 16, 16 => 5 | 16, 17 => 5 | 16, 18 => 5 | 16, 19 => 5
  | 16, 20 => 5 | 16, 21 => 5 | 16, 22 => 5 | 16, 23 => 5 | 16, 24 => 5
  | 16, 25 => 5 | 16, 26 => 5 | 16, 27 => 5 | 16, 28 => 5 | 16, 29 => 5
  | 16, 30 => 5 | 16, 31 => 5 | 16, 32 => 5 | 32, 1 => 1 | 32, 2 => 1
  | 32, 3 => 1 | 32, 4 => 1 | 32, 5 => 2 | 32, 6 => 3 | 32, 7 => 4
  | 32, 8 => 5 | 32, 9 => 5 | 32, 10 => 5 | 32, 11 => 5 | 32, 12 => 5
  | 32, 13 => 5 | 32, 14 => 5 | 32, 15 => 5 | 32, 16 => 5 | 32, 17 => 5
  | 32, 18 => 5 | 32, 19 => 5 | 32, 20 => 5 | 32, 21 => 5 | 32, 22 => 5
  | 32, 23 => 5 | 32, 24 => 5 | 32, 25 => 5 | 32, 26 => 5 | 32, 27 => 5
  | 32, 28 => 5 | 32, 29 => 5 | 32, 30 => 5 | 32, 31 => 5 | 32, 32 => 5
  | _, _ => 1
/-- Stratum-3 surplus threshold `sexticStratum3 w r`. -/
def sexticStratum3 (w r : ℕ) : ℕ :=
  if isSupportedMR w r = true ∧ 2 ≤ w then sexticStratum3Grid w r else 1
/-- 10 × 10 stratum-4 threshold table `sexticStratum4Grid w r` (`s4 ∈ {1..8}`). -/
def sexticStratum4Grid (w r : ℕ) : ℕ :=
  match w, r with
  | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 1, 6 => 1 | 1, 7 => 1 | 1, 8 => 1 | 1, 9 => 1 | 1, 10 => 1
  | 2, 1 => 1 | 2, 2 => 2 | 2, 3 => 2 | 2, 4 => 2 | 2, 5 => 2
  | 2, 6 => 2 | 2, 7 => 2 | 2, 8 => 2 | 2, 9 => 2 | 2, 10 => 2
  | 3, 1 => 1 | 3, 2 => 2 | 3, 3 => 3 | 3, 4 => 3 | 3, 5 => 3
  | 3, 6 => 3 | 3, 7 => 3 | 3, 8 => 3 | 3, 9 => 3 | 3, 10 => 3
  | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 3 | 4, 4 => 4 | 4, 5 => 4
  | 4, 6 => 4 | 4, 7 => 4 | 4, 8 => 4 | 4, 9 => 4 | 4, 10 => 4
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 3 | 5, 4 => 4 | 5, 5 => 4
  | 5, 6 => 4 | 5, 7 => 4 | 5, 8 => 4 | 5, 9 => 4 | 5, 10 => 4
  | 6, 1 => 1 | 6, 2 => 2 | 6, 3 => 3 | 6, 4 => 4 | 6, 5 => 4
  | 6, 6 => 4 | 6, 7 => 4 | 6, 8 => 4 | 6, 9 => 4 | 6, 10 => 4
  | 7, 1 => 1 | 7, 2 => 2 | 7, 3 => 3 | 7, 4 => 4 | 7, 5 => 4
  | 7, 6 => 4 | 7, 7 => 5 | 7, 8 => 5 | 7, 9 => 5 | 7, 10 => 5
  | 8, 1 => 1 | 8, 2 => 2 | 8, 3 => 3 | 8, 4 => 4 | 8, 5 => 4
  | 8, 6 => 4 | 8, 7 => 5 | 8, 8 => 5 | 8, 9 => 5 | 8, 10 => 5
  | 9, 1 => 1 | 9, 2 => 2 | 9, 3 => 3 | 9, 4 => 4 | 9, 5 => 4
  | 9, 6 => 4 | 9, 7 => 5 | 9, 8 => 5 | 9, 9 => 6 | 9, 10 => 6
  | 10, 1 => 1 | 10, 2 => 2 | 10, 3 => 3 | 10, 4 => 4 | 10, 5 => 4
  | 10, 6 => 4 | 10, 7 => 5 | 10, 8 => 5 | 10, 9 => 6 | 10, 10 => 6
  | 2, 11 => 1 | 2, 12 => 1 | 2, 13 => 1 | 2, 14 => 1 | 2, 15 => 1
  | 2, 16 => 1 | 2, 17 => 1 | 2, 18 => 1 | 2, 19 => 1 | 2, 20 => 1
  | 2, 21 => 1 | 2, 22 => 1 | 2, 23 => 1 | 2, 24 => 1 | 2, 25 => 1
  | 2, 26 => 1 | 2, 27 => 1 | 2, 28 => 1 | 2, 29 => 1 | 2, 30 => 1
  | 2, 31 => 1 | 2, 32 => 1 | 4, 11 => 2 | 4, 12 => 2 | 4, 13 => 2
  | 4, 14 => 2 | 4, 15 => 2 | 4, 16 => 2 | 4, 17 => 2 | 4, 18 => 2
  | 4, 19 => 2 | 4, 20 => 2 | 4, 21 => 2 | 4, 22 => 2 | 4, 23 => 2
  | 4, 24 => 2 | 4, 25 => 2 | 4, 26 => 2 | 4, 27 => 2 | 4, 28 => 2
  | 4, 29 => 2 | 4, 30 => 2 | 4, 31 => 2 | 4, 32 => 2 | 8, 11 => 6
  | 8, 12 => 6 | 8, 13 => 6 | 8, 14 => 6 | 8, 15 => 6 | 8, 16 => 6
  | 8, 17 => 6 | 8, 18 => 6 | 8, 19 => 6 | 8, 20 => 6 | 8, 21 => 6
  | 8, 22 => 6 | 8, 23 => 6 | 8, 24 => 6 | 8, 25 => 6 | 8, 26 => 6
  | 8, 27 => 6 | 8, 28 => 6 | 8, 29 => 6 | 8, 30 => 6 | 8, 31 => 6
  | 8, 32 => 6 | 16, 1 => 1 | 16, 2 => 1 | 16, 3 => 1 | 16, 4 => 2
  | 16, 5 => 3 | 16, 6 => 4 | 16, 7 => 5 | 16, 8 => 6 | 16, 9 => 6
  | 16, 10 => 6 | 16, 11 => 6 | 16, 12 => 6 | 16, 13 => 6 | 16, 14 => 6
  | 16, 15 => 6 | 16, 16 => 6 | 16, 17 => 6 | 16, 18 => 6 | 16, 19 => 6
  | 16, 20 => 6 | 16, 21 => 6 | 16, 22 => 6 | 16, 23 => 6 | 16, 24 => 6
  | 16, 25 => 6 | 16, 26 => 6 | 16, 27 => 6 | 16, 28 => 6 | 16, 29 => 6
  | 16, 30 => 6 | 16, 31 => 6 | 16, 32 => 6 | 32, 1 => 1 | 32, 2 => 1
  | 32, 3 => 1 | 32, 4 => 2 | 32, 5 => 3 | 32, 6 => 4 | 32, 7 => 5
  | 32, 8 => 6 | 32, 9 => 6 | 32, 10 => 6 | 32, 11 => 6 | 32, 12 => 6
  | 32, 13 => 6 | 32, 14 => 6 | 32, 15 => 6 | 32, 16 => 6 | 32, 17 => 6
  | 32, 18 => 6 | 32, 19 => 6 | 32, 20 => 6 | 32, 21 => 6 | 32, 22 => 6
  | 32, 23 => 6 | 32, 24 => 6 | 32, 25 => 6 | 32, 26 => 6 | 32, 27 => 6
  | 32, 28 => 6 | 32, 29 => 6 | 32, 30 => 6 | 32, 31 => 6 | 32, 32 => 6
  | _, _ => 1
/-- Stratum-4 surplus threshold `sexticStratum4 w r`. -/
def sexticStratum4 (w r : ℕ) : ℕ :=
  if isSupportedMR w r = true ∧ 2 ≤ w then sexticStratum4Grid w r else 1
/-- 10 × 10 stratum-5 threshold table `sexticStratum5Grid w r` (`s5 ∈ {1..8}`). -/
def sexticStratum5Grid (w r : ℕ) : ℕ :=
  match w, r with
  | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 1, 6 => 1 | 1, 7 => 1 | 1, 8 => 1 | 1, 9 => 1 | 1, 10 => 1
  | 2, 1 => 1 | 2, 2 => 2 | 2, 3 => 2 | 2, 4 => 2 | 2, 5 => 2
  | 2, 6 => 2 | 2, 7 => 2 | 2, 8 => 2 | 2, 9 => 2 | 2, 10 => 2
  | 3, 1 => 1 | 3, 2 => 2 | 3, 3 => 3 | 3, 4 => 3 | 3, 5 => 3
  | 3, 6 => 3 | 3, 7 => 3 | 3, 8 => 3 | 3, 9 => 3 | 3, 10 => 3
  | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 3 | 4, 4 => 4 | 4, 5 => 4
  | 4, 6 => 4 | 4, 7 => 4 | 4, 8 => 4 | 4, 9 => 4 | 4, 10 => 4
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 3 | 5, 4 => 4 | 5, 5 => 5
  | 5, 6 => 5 | 5, 7 => 5 | 5, 8 => 5 | 5, 9 => 5 | 5, 10 => 5
  | 6, 1 => 1 | 6, 2 => 2 | 6, 3 => 3 | 6, 4 => 4 | 6, 5 => 5
  | 6, 6 => 5 | 6, 7 => 5 | 6, 8 => 5 | 6, 9 => 5 | 6, 10 => 5
  | 7, 1 => 1 | 7, 2 => 2 | 7, 3 => 3 | 7, 4 => 4 | 7, 5 => 5
  | 7, 6 => 5 | 7, 7 => 6 | 7, 8 => 6 | 7, 9 => 6 | 7, 10 => 6
  | 8, 1 => 1 | 8, 2 => 2 | 8, 3 => 3 | 8, 4 => 4 | 8, 5 => 5
  | 8, 6 => 5 | 8, 7 => 6 | 8, 8 => 6 | 8, 9 => 6 | 8, 10 => 6
  | 9, 1 => 1 | 9, 2 => 2 | 9, 3 => 3 | 9, 4 => 4 | 9, 5 => 5
  | 9, 6 => 5 | 9, 7 => 6 | 9, 8 => 6 | 9, 9 => 7 | 9, 10 => 7
  | 10, 1 => 1 | 10, 2 => 2 | 10, 3 => 3 | 10, 4 => 4 | 10, 5 => 5
  | 10, 6 => 5 | 10, 7 => 6 | 10, 8 => 6 | 10, 9 => 7 | 10, 10 => 7
  | 2, 11 => 1 | 2, 12 => 1 | 2, 13 => 1 | 2, 14 => 1 | 2, 15 => 1
  | 2, 16 => 1 | 2, 17 => 1 | 2, 18 => 1 | 2, 19 => 1 | 2, 20 => 1
  | 2, 21 => 1 | 2, 22 => 1 | 2, 23 => 1 | 2, 24 => 1 | 2, 25 => 1
  | 2, 26 => 1 | 2, 27 => 1 | 2, 28 => 1 | 2, 29 => 1 | 2, 30 => 1
  | 2, 31 => 1 | 2, 32 => 1 | 4, 11 => 3 | 4, 12 => 3 | 4, 13 => 3
  | 4, 14 => 3 | 4, 15 => 3 | 4, 16 => 3 | 4, 17 => 3 | 4, 18 => 3
  | 4, 19 => 3 | 4, 20 => 3 | 4, 21 => 3 | 4, 22 => 3 | 4, 23 => 3
  | 4, 24 => 3 | 4, 25 => 3 | 4, 26 => 3 | 4, 27 => 3 | 4, 28 => 3
  | 4, 29 => 3 | 4, 30 => 3 | 4, 31 => 3 | 4, 32 => 3 | 8, 11 => 7
  | 8, 12 => 7 | 8, 13 => 7 | 8, 14 => 7 | 8, 15 => 7 | 8, 16 => 7
  | 8, 17 => 7 | 8, 18 => 7 | 8, 19 => 7 | 8, 20 => 7 | 8, 21 => 7
  | 8, 22 => 7 | 8, 23 => 7 | 8, 24 => 7 | 8, 25 => 7 | 8, 26 => 7
  | 8, 27 => 7 | 8, 28 => 7 | 8, 29 => 7 | 8, 30 => 7 | 8, 31 => 7
  | 8, 32 => 7 | 16, 1 => 1 | 16, 2 => 1 | 16, 3 => 2 | 16, 4 => 3
  | 16, 5 => 4 | 16, 6 => 5 | 16, 7 => 6 | 16, 8 => 7 | 16, 9 => 7
  | 16, 10 => 7 | 16, 11 => 7 | 16, 12 => 7 | 16, 13 => 7 | 16, 14 => 7
  | 16, 15 => 7 | 16, 16 => 7 | 16, 17 => 7 | 16, 18 => 7 | 16, 19 => 7
  | 16, 20 => 7 | 16, 21 => 7 | 16, 22 => 7 | 16, 23 => 7 | 16, 24 => 7
  | 16, 25 => 7 | 16, 26 => 7 | 16, 27 => 7 | 16, 28 => 7 | 16, 29 => 7
  | 16, 30 => 7 | 16, 31 => 7 | 16, 32 => 7 | 32, 1 => 1 | 32, 2 => 1
  | 32, 3 => 2 | 32, 4 => 3 | 32, 5 => 4 | 32, 6 => 5 | 32, 7 => 6
  | 32, 8 => 7 | 32, 9 => 7 | 32, 10 => 7 | 32, 11 => 7 | 32, 12 => 7
  | 32, 13 => 7 | 32, 14 => 7 | 32, 15 => 7 | 32, 16 => 7 | 32, 17 => 7
  | 32, 18 => 7 | 32, 19 => 7 | 32, 20 => 7 | 32, 21 => 7 | 32, 22 => 7
  | 32, 23 => 7 | 32, 24 => 7 | 32, 25 => 7 | 32, 26 => 7 | 32, 27 => 7
  | 32, 28 => 7 | 32, 29 => 7 | 32, 30 => 7 | 32, 31 => 7 | 32, 32 => 7
  | _, _ => 1
/-- Stratum-5 surplus threshold `sexticStratum5 w r`. -/
def sexticStratum5 (w r : ℕ) : ℕ :=
  if isSupportedMR w r = true ∧ 2 ≤ w then sexticStratum5Grid w r else 1
/-- 10 × 10 stratum-6 threshold table `sexticStratum6Grid w r` (`s6 ∈ {1..8}`). -/
def sexticStratum6Grid (w r : ℕ) : ℕ :=
  match w, r with
  | 1, 1 => 1 | 1, 2 => 1 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 1
  | 1, 6 => 1 | 1, 7 => 1 | 1, 8 => 1 | 1, 9 => 1 | 1, 10 => 1
  | 2, 1 => 1 | 2, 2 => 2 | 2, 3 => 2 | 2, 4 => 2 | 2, 5 => 2
  | 2, 6 => 2 | 2, 7 => 2 | 2, 8 => 2 | 2, 9 => 2 | 2, 10 => 2
  | 3, 1 => 1 | 3, 2 => 2 | 3, 3 => 3 | 3, 4 => 3 | 3, 5 => 3
  | 3, 6 => 3 | 3, 7 => 3 | 3, 8 => 3 | 3, 9 => 3 | 3, 10 => 3
  | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 3 | 4, 4 => 4 | 4, 5 => 4
  | 4, 6 => 4 | 4, 7 => 4 | 4, 8 => 4 | 4, 9 => 4 | 4, 10 => 4
  | 5, 1 => 1 | 5, 2 => 2 | 5, 3 => 3 | 5, 4 => 4 | 5, 5 => 5
  | 5, 6 => 5 | 5, 7 => 5 | 5, 8 => 5 | 5, 9 => 5 | 5, 10 => 5
  | 6, 1 => 1 | 6, 2 => 2 | 6, 3 => 3 | 6, 4 => 4 | 6, 5 => 5
  | 6, 6 => 6 | 6, 7 => 6 | 6, 8 => 6 | 6, 9 => 6 | 6, 10 => 6
  | 7, 1 => 1 | 7, 2 => 2 | 7, 3 => 3 | 7, 4 => 4 | 7, 5 => 5
  | 7, 6 => 6 | 7, 7 => 7 | 7, 8 => 7 | 7, 9 => 7 | 7, 10 => 7
  | 8, 1 => 1 | 8, 2 => 2 | 8, 3 => 3 | 8, 4 => 4 | 8, 5 => 5
  | 8, 6 => 6 | 8, 7 => 7 | 8, 8 => 7 | 8, 9 => 7 | 8, 10 => 7
  | 9, 1 => 1 | 9, 2 => 2 | 9, 3 => 3 | 9, 4 => 4 | 9, 5 => 5
  | 9, 6 => 6 | 9, 7 => 7 | 9, 8 => 7 | 9, 9 => 8 | 9, 10 => 8
  | 10, 1 => 1 | 10, 2 => 2 | 10, 3 => 3 | 10, 4 => 4 | 10, 5 => 5
  | 10, 6 => 6 | 10, 7 => 7 | 10, 8 => 7 | 10, 9 => 8 | 10, 10 => 8
  | 2, 11 => 2 | 2, 12 => 2 | 2, 13 => 2 | 2, 14 => 2 | 2, 15 => 2
  | 2, 16 => 2 | 2, 17 => 2 | 2, 18 => 2 | 2, 19 => 2 | 2, 20 => 2
  | 2, 21 => 2 | 2, 22 => 2 | 2, 23 => 2 | 2, 24 => 2 | 2, 25 => 2
  | 2, 26 => 2 | 2, 27 => 2 | 2, 28 => 2 | 2, 29 => 2 | 2, 30 => 2
  | 2, 31 => 2 | 2, 32 => 2 | 4, 11 => 4 | 4, 12 => 4 | 4, 13 => 4
  | 4, 14 => 4 | 4, 15 => 4 | 4, 16 => 4 | 4, 17 => 4 | 4, 18 => 4
  | 4, 19 => 4 | 4, 20 => 4 | 4, 21 => 4 | 4, 22 => 4 | 4, 23 => 4
  | 4, 24 => 4 | 4, 25 => 4 | 4, 26 => 4 | 4, 27 => 4 | 4, 28 => 4
  | 4, 29 => 4 | 4, 30 => 4 | 4, 31 => 4 | 4, 32 => 4 | 8, 11 => 8
  | 8, 12 => 8 | 8, 13 => 8 | 8, 14 => 8 | 8, 15 => 8 | 8, 16 => 8
  | 8, 17 => 8 | 8, 18 => 8 | 8, 19 => 8 | 8, 20 => 8 | 8, 21 => 8
  | 8, 22 => 8 | 8, 23 => 8 | 8, 24 => 8 | 8, 25 => 8 | 8, 26 => 8
  | 8, 27 => 8 | 8, 28 => 8 | 8, 29 => 8 | 8, 30 => 8 | 8, 31 => 8
  | 8, 32 => 8 | 16, 1 => 1 | 16, 2 => 2 | 16, 3 => 3 | 16, 4 => 4
  | 16, 5 => 5 | 16, 6 => 6 | 16, 7 => 7 | 16, 8 => 8 | 16, 9 => 8
  | 16, 10 => 8 | 16, 11 => 8 | 16, 12 => 8 | 16, 13 => 8 | 16, 14 => 8
  | 16, 15 => 8 | 16, 16 => 8 | 16, 17 => 8 | 16, 18 => 8 | 16, 19 => 8
  | 16, 20 => 8 | 16, 21 => 8 | 16, 22 => 8 | 16, 23 => 8 | 16, 24 => 8
  | 16, 25 => 8 | 16, 26 => 8 | 16, 27 => 8 | 16, 28 => 8 | 16, 29 => 8
  | 16, 30 => 8 | 16, 31 => 8 | 16, 32 => 8 | 32, 1 => 1 | 32, 2 => 2
  | 32, 3 => 3 | 32, 4 => 4 | 32, 5 => 5 | 32, 6 => 6 | 32, 7 => 7
  | 32, 8 => 8 | 32, 9 => 8 | 32, 10 => 8 | 32, 11 => 8 | 32, 12 => 8
  | 32, 13 => 8 | 32, 14 => 8 | 32, 15 => 8 | 32, 16 => 8 | 32, 17 => 8
  | 32, 18 => 8 | 32, 19 => 8 | 32, 20 => 8 | 32, 21 => 8 | 32, 22 => 8
  | 32, 23 => 8 | 32, 24 => 8 | 32, 25 => 8 | 32, 26 => 8 | 32, 27 => 8
  | 32, 28 => 8 | 32, 29 => 8 | 32, 30 => 8 | 32, 31 => 8 | 32, 32 => 8
  | _, _ => 1
/-- Stratum-6 surplus threshold `sexticStratum6 w r`. -/
def sexticStratum6 (w r : ℕ) : ℕ :=
  if isSupportedMR w r = true ∧ 2 ≤ w then sexticStratum6Grid w r else 1
private def sexticStratumOk (w i : ℕ) : Bool :=
  let r := i + 1; let s1 := sexticStratum1Grid w r; let s2 := sexticStratum2Grid w r
  let s3 := sexticStratum3Grid w r; let s4 := sexticStratum4Grid w r
  let s5 := sexticStratum5Grid w r; let s6 := sexticStratum6Grid w r
  Nat.ble 1 s1 && Nat.ble s1 s2 && Nat.ble s2 s3 && Nat.ble s3 s4 && Nat.ble s4 s5 &&
    Nat.ble s5 s6 && Nat.ble s6 8 && Nat.ble s6 w && Nat.ble s6 r
private lemma sexticStratum_ok : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 32] : List ℕ).all
    (fun w ↦ (List.range 32).all (sexticStratumOk w)) = true := rfl
theorem sexticStratum_bounds {w r : ℕ} (hw : 1 ≤ w) (hr : 1 ≤ r) : 1 ≤ sexticStratum1 w r ∧
  sexticStratum1 w r ≤ sexticStratum2 w r ∧ sexticStratum2 w r ≤ sexticStratum3 w r ∧ sexticStratum3
  w r ≤ sexticStratum4 w r ∧ sexticStratum4 w r ≤ sexticStratum5 w r ∧ sexticStratum5 w r ≤
  sexticStratum6 w r ∧ sexticStratum6 w r ≤ 8 ∧ sexticStratum6 w r ≤ w ∧ sexticStratum6 w r ≤ r :=
  by
  by_cases h : isSupportedMR w r = true ∧ 2 ≤ w
  · rcases r with _ | r'
    · omega
    have hm : w ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 32] : List ℕ) ∧ r' < 32 := by
      unfold isSupportedMR at h; simp only [decide_eq_true_eq, List.mem_cons,
        List.not_mem_nil, or_false] at h ⊢; omega
    have h2 := List.all_eq_true.mp (List.all_eq_true.mp sexticStratum_ok w hm.1) r'
      (List.mem_range.mpr hm.2)
    simp only [sexticStratum1, sexticStratum2, sexticStratum3, sexticStratum4, sexticStratum5,
      sexticStratum6, h.1, h.2, and_self, ↓reduceIte]
    simpa only [sexticStratumOk, Bool.and_eq_true, and_assoc, Nat.ble_eq] using h2
  · simp only [sexticStratum1, sexticStratum2, sexticStratum3, sexticStratum4, sexticStratum5,
      sexticStratum6, h, ↓reduceIte]
    exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, by omega, hw, hr⟩
/-- 10 × 10 multiplicity-adaptive scaled phase numerator table `sexticPhiScaledGrid w r` (`×
  600`). -/
def sexticPhiScaledGrid (w r : ℕ) : ℕ :=
  match w, r with
  | 1, 1 => 700 | 1, 2 => 700 | 1, 3 => 700 | 1, 4 => 700 | 1, 5 => 700
  | 1, 6 => 700 | 1, 7 => 700 | 1, 8 => 700 | 1, 9 => 700 | 1, 10 => 700
  | 2, 1 => 700 | 2, 2 => 683 | 2, 3 => 664 | 2, 4 => 688 | 2, 5 => 681
  | 2, 6 => 691 | 2, 7 => 688 | 2, 8 => 692 | 2, 9 => 691 | 2, 10 => 693
  | 3, 1 => 700 | 3, 2 => 622 | 3, 3 => 670 | 3, 4 => 659 | 3, 5 => 678
  | 3, 6 => 677 | 3, 7 => 679 | 3, 8 => 684 | 3, 9 => 684 | 3, 10 => 686
  | 4, 1 => 700 | 4, 2 => 559 | 4, 3 => 668 | 4, 4 => 650 | 4, 5 => 653
  | 4, 6 => 675 | 4, 7 => 674 | 4, 8 => 671 | 4, 9 => 680 | 4, 10 => 681
  | 5, 1 => 700 | 5, 2 => 507 | 5, 3 => 646 | 5, 4 => 665 | 5, 5 => 633
  | 5, 6 => 653 | 5, 7 => 676 | 5, 8 => 670 | 5, 9 => 665 | 5, 10 => 674
  | 6, 1 => 700 | 6, 2 => 466 | 6, 3 => 615 | 6, 4 => 671 | 6, 5 => 637
  | 6, 6 => 628 | 6, 7 => 658 | 6, 8 => 678 | 6, 9 => 668 | 6, 10 => 658
  | 7, 1 => 700 | 7, 2 => 433 | 7, 3 => 582 | 7, 4 => 663 | 7, 5 => 658
  | 7, 6 => 611 | 7, 7 => 635 | 7, 8 => 666 | 7, 9 => 681 | 7, 10 => 668
  | 8, 1 => 700 | 8, 2 => 405 | 8, 3 => 552 | 8, 4 => 647 | 8, 5 => 671
  | 8, 6 => 618 | 8, 7 => 610 | 8, 8 => 640 | 8, 9 => 670 | 8, 10 => 679
  | 9, 1 => 700 | 9, 2 => 383 | 9, 3 => 524 | 9, 4 => 627 | 9, 5 => 673
  | 9, 6 => 645 | 9, 7 => 593 | 9, 8 => 610 | 9, 9 => 657 | 9, 10 => 681
  | 10, 1 => 700 | 10, 2 => 363 | 10, 3 => 500 | 10, 4 => 606 | 10, 5 => 666
  | 10, 6 => 667 | 10, 7 => 594 | 10, 8 => 581 | 10, 9 => 628 | 10, 10 => 659
  | 2, 11 => 690 | 2, 12 => 691 | 2, 13 => 691 | 2, 14 => 692 | 2, 15 => 692
  | 2, 16 => 692 | 2, 17 => 693 | 2, 18 => 693 | 2, 19 => 693 | 2, 20 => 693
  | 2, 21 => 693 | 2, 22 => 694 | 2, 23 => 694 | 2, 24 => 694 | 2, 25 => 694
  | 2, 26 => 694 | 2, 27 => 694 | 2, 28 => 694 | 2, 29 => 694 | 2, 30 => 694
  | 2, 31 => 694 | 2, 32 => 694 | 4, 11 => 679 | 4, 12 => 682 | 4, 13 => 684
  | 4, 14 => 684 | 4, 15 => 686 | 4, 16 => 686 | 4, 17 => 686 | 4, 18 => 688
  | 4, 19 => 688 | 4, 20 => 689 | 4, 21 => 689 | 4, 22 => 689 | 4, 23 => 690
  | 4, 24 => 690 | 4, 25 => 691 | 4, 26 => 691 | 4, 27 => 691 | 4, 28 => 691
  | 4, 29 => 692 | 4, 30 => 692 | 4, 31 => 693 | 4, 32 => 693 | 8, 11 => 676
  | 8, 12 => 664 | 8, 13 => 667 | 8, 14 => 679 | 8, 15 => 689 | 8, 16 => 688
  | 8, 17 => 679 | 8, 18 => 673 | 8, 19 => 677 | 8, 20 => 684 | 8, 21 => 689
  | 8, 22 => 689 | 8, 23 => 684 | 8, 24 => 681 | 8, 25 => 681 | 8, 26 => 686
  | 8, 27 => 690 | 8, 28 => 690 | 8, 29 => 688 | 8, 30 => 686 | 8, 31 => 686
  | 8, 32 => 688 | 16, 1 => 700 | 16, 2 => 288 | 16, 3 => 398 | 16, 4 => 494
  | 16, 5 => 576 | 16, 6 => 638 | 16, 7 => 673 | 16, 8 => 671 | 16, 9 => 499
  | 16, 10 => 500 | 16, 11 => 523 | 16, 12 => 543 | 16, 13 => 554 | 16, 14 => 552
  | 16, 15 => 530 | 16, 16 => 490 | 16, 17 => 476 | 16, 18 => 491 | 16, 19 => 505
  | 16, 20 => 515 | 16, 21 => 517 | 16, 22 => 505 | 16, 23 => 483 | 16, 24 => 473
  | 16, 25 => 478 | 16, 26 => 489 | 16, 27 => 497 | 16, 28 => 499 | 16, 29 => 494
  | 16, 30 => 481 | 16, 31 => 472 | 16, 32 => 473 | 32, 1 => 700 | 32, 2 => 210
  | 32, 3 => 282 | 32, 4 => 351 | 32, 5 => 413 | 32, 6 => 472 | 32, 7 => 527
  | 32, 8 => 576 | 32, 9 => 357 | 32, 10 => 305 | 32, 11 => 307 | 32, 12 => 332
  | 32, 13 => 354 | 32, 14 => 373 | 32, 15 => 390 | 32, 16 => 405 | 32, 17 => 292
  | 32, 18 => 302 | 32, 19 => 317 | 32, 20 => 332 | 32, 21 => 345 | 32, 22 => 355
  | 32, 23 => 361 | 32, 24 => 358 | 32, 25 => 300 | 32, 26 => 312 | 32, 27 => 324
  | 32, 28 => 333 | 32, 29 => 341 | 32, 30 => 345 | 32, 31 => 343 | 32, 32 => 330
  | _, _ => 700
/-- 2D stage-and-multiplicity-adaptive rotation phase numerator `sexticPhiScaledNat w r` (`×
  600`). -/
def sexticPhiScaledNat (w r : ℕ) : ℕ :=
  if isSupportedMR w r = true ∧ 2 ≤ w then sexticPhiScaledGrid w r else 700
private lemma sexticPhi_ok : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 32] : List ℕ).all (fun w ↦
    (List.range 33).all fun r ↦ Nat.ble 210 (sexticPhiScaledGrid w r) &&
      Nat.ble (sexticPhiScaledGrid w r) 840) = true := rfl
theorem sexticPhiScaledNat_bounds (w r : ℕ) : 210 ≤ sexticPhiScaledNat w r ∧ sexticPhiScaledNat w r
  ≤ 840 := by
  by_cases h : isSupportedMR w r = true ∧ 2 ≤ w
  · have hm : w ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 16, 32] : List ℕ) ∧ r < 33 := by
      unfold isSupportedMR at h; simp only [decide_eq_true_eq, List.mem_cons,
        List.not_mem_nil, or_false] at h ⊢; omega
    have h2 := List.all_eq_true.mp (List.all_eq_true.mp sexticPhi_ok w hm.1) r
      (List.mem_range.mpr hm.2)
    simp only [sexticPhiScaledNat, h.1, h.2, and_self, ↓reduceIte]
    simpa only [Bool.and_eq_true, Nat.ble_eq] using h2
  · have h1 : sexticPhiScaledNat w r = 700 := (by simp [sexticPhiScaledNat, h]); rw [h1]; omega
/-- Rational target rotation angle `sexticPhiQ w r = sexticPhiScaledNat w r / 600`. -/
def sexticPhiQ (w r : ℕ) : ℚ≥0 :=
  (sexticPhiScaledNat w r : ℚ≥0) / 600
/-- Real target rotation angle `sexticPhiReal w r`. -/
noncomputable def sexticPhiReal (w r : ℕ) : ℝ :=
  (sexticPhiQ w r : ℝ)
theorem sexticPhiScaledNat_div_eq (w r : ℕ) : (sexticPhiScaledNat w r : ℝ) / 600 = sexticPhiReal w r
  := by simp [sexticPhiReal, sexticPhiQ]
theorem sexticPhiReal_bounds (w r : ℕ) : (7 / 20 : ℝ) ≤ sexticPhiReal w r ∧ sexticPhiReal w r ≤ 7 /
  5 := by
  rcases sexticPhiScaledNat_bounds w r with ⟨hlo, hhi⟩; have hlo_r : (210 : ℝ) ≤ (sexticPhiScaledNat
    w r : ℝ) := (by exact_mod_cast hlo); have hhi_r : (sexticPhiScaledNat w r : ℝ) ≤ 840 :=
    (by exact_mod_cast hhi); rw [← sexticPhiScaledNat_div_eq]; constructor <;> linarith
/-- One full punctuated `w`-slot attempt using the 2D multiplicity-adaptive phase
  `sexticPhiReal`. -/
noncomputable def sexticAttemptBody {Var : Type} (n m k r : ℕ) (T : Finset (Fin (2 ^ n)))
    (res : Var) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k))
      Var (findAllQubits n m k) ((n + 1) * activeSlots m k) :=
  let Q := findAllQubits n m k
  let K := stageIterations (sexticPhiReal (activeSlots m k) r) n r
  .seq (qsetSim n m Q res)
    (.seq (.step (tagFreeStep (embedAllSlots n m k (prepSlotUnitary n))))
      (.seq (repeatCircuit K (groverIterBatchCircuit n m k T))
        (.seq (.step (tagFreeStep (embedAllSlots n m k (verPrepSlotUnitary n))))
          (.seq (.oracle (batchOracleReg n m k))
            (.seq (.step (tagFreeStep (embedAllSlots n m k (clearSlotFlagsUnitary T))))
              (.measure res (QRegister.whole Q)))))))
theorem multiP_succ_sexticStageIterations_pos {n w r : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ 2 ^ n) : 0 <
  multiP_succ (stageIterations (sexticPhiReal w r) n r) r (2 ^ n) ∧ multiP_succ (stageIterations
  (sexticPhiReal w r) n r) r (2 ^ n) ≤ 1 := by
  refine ⟨?_, Real.sin_sq_le_one _⟩; unfold stageIterations
  split_ifs with hge
  · unfold multiP_succ; set θ := multiHalfAngle r (2 ^ n); set φ := sexticPhiReal w r; set K :=
      (round (φ / (2 * θ))).toNat; have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1)
    have hd_pos : 0 < ((2 ^ n : ℕ) : ℝ) := (by positivity)
    have hθ_pos : 0 < θ := Real.arcsin_pos.2 (by positivity); rcases sexticPhiReal_bounds w r with
      ⟨hφ_lo, hφ_hi⟩; have hφ_pos : 0 < φ := (by linarith); obtain ⟨hK_lo, hK_hi⟩ :=
      odd_round_div_sub_mem_Icc hθ_pos hφ_pos.le; have h16384 : (16384 : ℝ) * (r : ℝ) ≤ ((2 ^ n : ℕ)
      : ℝ) := (by exact_mod_cast hge)
    let c : ℝ := ((2 ^ n : ℕ) : ℝ) / (r : ℝ)
    have hc64 : 64 ≤ c := (le_div_iff₀ hr_pos).2 (by linarith)
    have hθ_eq : θ = Real.arcsin (1 / Real.sqrt c) := by
      change Real.arcsin (Real.sqrt (r : ℝ) / Real.sqrt ((2 ^ n : ℕ) : ℝ)) = _; congr 1
      rw [Real.sqrt_div hd_pos.le, one_div_div]
    have hθ_le : θ ≤ 9 / 50 := by
      rw [hθ_eq]
      exact arcsin_one_div_sqrt_le (by linarith) (by norm_num) (by norm_num) (by nlinarith)
    have hsin_pos : 0 < Real.sin ((2 * (K : ℝ) + 1) * θ) := Real.sin_pos_of_pos_of_lt_pi
      (by linarith) (by linarith [Real.pi_gt_three]); exact sq_pos_of_pos hsin_pos
  · unfold multiP_succ; have hsin : Real.sin ((2 * ((0 : ℕ) : ℝ) + 1) * multiHalfAngle r (2 ^ n)) =
      Real.sqrt (r : ℝ) / Real.sqrt ((2 ^ n : ℕ) : ℝ) :=
      (by rw [Nat.cast_zero, mul_zero, zero_add, one_mul]; exact sin_multiHalfAngle hrd); rw [hsin]
    have hr_pos : 0 < (r : ℝ) := (by exact_mod_cast hr1); have hd_pos : 0 < ((2 ^ n : ℕ) : ℝ) :=
      (by positivity); positivity
theorem octicOccupancyTail_stage_bounds {n m k s r : ℕ} (hs1 : 1 ≤ s) (hs8 : s ≤ 8) (hsw : s ≤
  activeSlots m k) (hsr : s ≤ r) (hrd : r ≤ 2 ^ n) :
    let K := stageIterations (sexticPhiReal (activeSlots m k) r) n r
    let p := multiP_succ K r (2 ^ n)
    0 < octicOccupancyTail s (activeSlots m k) r p ∧ octicOccupancyTail s (activeSlots m k) r p ≤ 1
      := by
  intro K p; have hr1 : 1 ≤ r := hs1.trans hsr; rcases multiP_succ_sexticStageIterations_pos (w :=
    activeSlots m k) hr1 hrd with ⟨hp0, hp1⟩
  rcases octicOccupancyTail_pos_and_mono hs1 hs8 hsw hsr hp0 le_rfl hp1 with ⟨ht0, _, ht1⟩
  exact ⟨ht0, ht1⟩
private lemma s15_wp_groverIterBatchCircuit {Var : Type} [DecidableEq Var] {n m k : ℕ} (_hm : 1 ≤ m)
  (S T : Finset (Fin (2 ^ n))) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
  ((groverIterBatchCircuit n m k T).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots
  m k) S)) Θ = CQAssertion.qAssign (embedAllSlots n m k (singleSlotIterUnitary S T)) Θ := by
  simp only [groverIterBatchCircuit, OracleDynamicCircuit.compile, wp_qSeq, wp_qAssign_tagFreeStep]
  simp only [wp_qAssign, batchOracleReg_embedUnitary_eq n m k S, CQAssertion.qAssign_qAssign, ←
    quartic_embedAllSlots_mul, singleSlotIterUnitary, mul_assoc]
private lemma s15_wp_repeatCircuit_groverIterBatchCircuit {Var : Type} [DecidableEq Var] {n m k : ℕ}
  (hm : 1 ≤ m) (S T : Finset (Fin (2 ^ n))) (K : ℕ) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits
    n m k))
  : wp ((repeatCircuit K (groverIterBatchCircuit n m k T)).compile QProg.qAssign
  (groverParallelMarkingOracle (activeSlots m k) S)) Θ = CQAssertion.qAssign (embedAllSlots n m k
  ((singleSlotIterUnitary S T) ^ K)) Θ := by
  induction K generalizing Θ with
  | zero =>
    simp only [repeatCircuit, OracleDynamicCircuit.compile, wp_skip, pow_zero,
      quartic_embedAllSlots_one]; exact (CQAssertion.qAssign_one Θ).symm
  | succ K ih =>
    simp only [repeatCircuit, OracleDynamicCircuit.compile, wp_qSeq, s15_wp_groverIterBatchCircuit
      hm S T, ih, CQAssertion.qAssign_qAssign, ← quartic_embedAllSlots_mul, ← pow_succ']
private lemma s15_sum_smul_compProj_eq_diagonal {d : ℕ} (c : Fin d → ℂ) : ∑ o : Fin d, c o •
  compProj o = Matrix.diagonal c := by
  ext i j; rw [Matrix.sum_apply]; by_cases hij : i = j
  · subst hij; simp [compProj_apply]
  · rw [Matrix.diagonal_apply_ne _ hij]; refine Finset.sum_eq_zero fun x _ ↦ ?_
    rw [Matrix.smul_apply, compProj_apply, smul_eq_mul]; split_ifs with h
    · exact (hij (h.1.trans h.2.symm)).elim
    · ring
private noncomputable def sexticAttemptTail {Var : Type} (n m k r : ℕ) (T : Finset (Fin (2 ^ n)))
    (res : Var) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k)
    ((n + 1) * activeSlots m k) :=
  let Q := findAllQubits n m k
  let K := stageIterations (sexticPhiReal (activeSlots m k) r) n r
  .seq (.step (tagFreeStep (embedAllSlots n m k (prepSlotUnitary n))))
    (.seq (repeatCircuit K (groverIterBatchCircuit n m k T))
      (.seq (.step (tagFreeStep (embedAllSlots n m k (verPrepSlotUnitary n))))
        (.seq (.oracle (batchOracleReg n m k))
          (.seq (.step (tagFreeStep (embedAllSlots n m k (clearSlotFlagsUnitary T))))
            (.measure res (QRegister.whole Q))))))
private lemma sexticAttemptBody_eq_seq_sexticAttemptTail {Var : Type} (n m k r : ℕ)
    (T : Finset (Fin (2 ^ n))) (res : Var) : sexticAttemptBody n m k r T res =
      .seq (qsetSim n m (findAllQubits n m k) res) (sexticAttemptTail n m k r T res) := rfl
private lemma wp_sexticAttemptTail {Var : Type} [DecidableEq Var] {n m k r : ℕ} (hm : 1 ≤ m) (S T :
  Finset (Fin (2 ^ n))) (res : Var) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
  ((sexticAttemptTail n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots
  m k) S)) Θ = CQAssertion.qAssign (embedAllSlots n m k (singleSlotAttemptUnitary S T
  (stageIterations (sexticPhiReal (activeSlots m k) r) n r))) (wp (QProg.measureRegister res
  (QRegister.whole (findAllQubits n m k))) Θ) := by
  dsimp only [sexticAttemptTail, OracleDynamicCircuit.compile, singleSlotAttemptUnitary]
  rw [wp_qSeq, wp_qSeq, wp_qSeq, wp_qSeq, wp_qSeq]; rw [wp_qAssign_tagFreeStep,
    wp_qAssign_tagFreeStep, wp_qAssign_tagFreeStep]; rw [batchOracleReg_embedUnitary_eq n m k S,
    s15_wp_repeatCircuit_groverIterBatchCircuit hm S T]; rw [wp_qAssign, wp_qAssign, wp_qAssign,
    wp_qAssign]; rw [CQAssertion.qAssign_qAssign, CQAssertion.qAssign_qAssign,
    CQAssertion.qAssign_qAssign, CQAssertion.qAssign_qAssign]; rw [← quartic_embedAllSlots_mul, ←
    quartic_embedAllSlots_mul, ← quartic_embedAllSlots_mul, ← quartic_embedAllSlots_mul]
  simp only [mul_assoc]
theorem wp_sexticAttemptBody_apply {Var : Type} [DecidableEq Var]
    {n m k r : ℕ} (hm : 1 ≤ m) (S T : Finset (Fin (2 ^ n))) (res : Var)
    (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ : Store Var) :
    let Q := findAllQubits n m k
    let K := stageIterations (sexticPhiReal (activeSlots m k) r) n r
    let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
    let d_Θ : Fin (2 ^ Q) → ℂ := fun o ↦ (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o
    ((wp ((sexticAttemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)) Θ) σ).1.1 = ((U_all.1ᴴ * Matrix.diagonal d_Θ * U_all.1) 0 0) • (1 :
      Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) := by
  intro Q K U_all d_Θ; rw [sexticAttemptBody_eq_seq_sexticAttemptTail, OracleDynamicCircuit.compile,
    wp_qSeq, wp_sexticAttemptTail hm S T res Θ]
  let Ψ := CQAssertion.qAssign U_all (wp (QProg.measureRegister res (QRegister.whole Q)) Θ)
  have hΨ : ∀ o : Fin (2 ^ Q), Ψ (Store.subst σ res (o.val : ℤ)) = Ψ σ := by
    intro o; simp only [Ψ, QProg.measureRegister, wp_qMeasure, CQAssertion.qAssign_apply]
    rw [wp_qMeasure_subst_same_const]
  have hmeas : (wp (QProg.measureRegister res (QRegister.whole Q)) Θ σ).1.1 = Matrix.diagonal d_Θ
    := by
    simp only [wp_measureRegister_coe, HermitianMat.val_eq_coe, HermitianMat.mat_finset_sum]
    have hterm : ∀ o : Fin (2 ^ Q), (((Θ (Store.subst σ res (Int.ofNat o.val))).1.conj
      ((QRegister.whole Q).basisOutcomeProjector o)ᴴ).mat) = d_Θ o • compProj o := by
      intro o; rw [HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose,
        QRegister.basisOutcomeProjector, QRegister.whole_embedMatrix, compProj_conjTranspose,
        compProj_mul_mul]; rfl
    exact (Finset.sum_congr rfl fun o _ ↦ hterm o).trans (s15_sum_smul_compProj_eq_diagonal d_Θ)
  have hΨ_mat : (Ψ σ).1.1 = U_all.1ᴴ * Matrix.diagonal d_Θ * U_all.1 :=
    (by dsimp only [Ψ]; rw [qhlQAssign_val, hmeas]); rw [wp_qsetSim res
    (groverParallelMarkingOracle (activeSlots m k) S) Ψ σ (Ψ σ) hΨ, hΨ_mat]
private lemma s15_stageMissZ_natCast (n m k s : ℕ) (o : Fin (2 ^ findAllQubits n m k)) : stageMissZ
  n m k s (o.val : ℤ) = stageMissOutcome n m k s o := by
  unfold stageMissZ; rw [dite_eq_left (Int.natCast_nonneg o.val)]
  have hlt : (o.val : ℤ).toNat < 2 ^ findAllQubits n m k := by rw [Int.toNat_natCast]; exact o.isLt
  rw [dite_eq_left hlt]; have ho : (⟨(o.val : ℤ).toNat, hlt⟩ : Fin (2 ^ findAllQubits n m k)) = o :=
    Fin.ext (Int.toNat_natCast o.val); rw [ho]
theorem wp_sexticAttemptBody_occupancyStratum_full {Var : Type} [DecidableEq Var] {n m k s r : ℕ}
  (hm : 1 ≤ m) (hs1 : 1 ≤ s) (hs8 : s ≤ 8) (hsw : s ≤ activeSlots m k) (hsr : s ≤ r) (hrd : r ≤ 2 ^
  n) {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (res : Var) :
    let K := stageIterations (sexticPhiReal (activeSlots m k) r) n r
    let p := octicOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n))
    let body := (sexticAttemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)
    wp body (liftPureProp (fun σ ↦ ¬ stageRetryGuard n m k s res σ)) = constAssertion p ∧ ∀ (Θ :
      CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ : Store Var) (c : ℝ), 0 ≤ c → c ≤ 1 → (∀
        o : Fin
      (2 ^ findAllQubits n m k), hitSet n m k o ⊆ S \ T → if stageMissOutcome n m k s o = true then
      (Θ (Store.subst σ res (o.val : ℤ))).1 = c • 1 else (Θ (Store.subst σ res (o.val : ℤ))).1 = 1)
      → ((wp body Θ) σ).1 = (p + (1 - p) * c) • 1 := by
  intro K p body; let Q := findAllQubits n m k
  let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
  have hstratum : (U_all.1ᴴ * Matrix.diagonal (stratumExitInd n m k s (S \ T)) * U_all.1) 0 0 = (p :
    ℂ) := conj_stratumExitInd_octic_zero_zero hs1 hs8 hsr hTS hr K
  have hvalid_all : (U_all.1ᴴ * Matrix.diagonal (validAllInd n m k (S \ T)) * U_all.1) 0 0 = 1 :=
    conj_validAllInd_self_zero_zero hTS K
  have hvalid_oz : ∀ o, validAllInd n m k (S \ T) o = 1 ∨ validAllInd n m k (S \ T) o = 0 := by
    intro o; rw [validAllInd_eq_hitSet_subset]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hstep_aux : ∀ (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (c : ℝ), (∀ o : Fin (2 ^
    Q),
    hitSet n m k o ⊆ S \ T → stageMissOutcome n m k s o = true → (Θ (Store.subst σ res (o.val :
    ℤ))).1.mat o o = (c : ℂ)) → (∀ o : Fin (2 ^ Q), hitSet n m k o ⊆ S \ T → stageMissOutcome n m k
    s o = false → (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o = 1) → ((wp body Θ) σ).1 = (p + (1 -
    p) * c) • 1 := by
    intro Θ σ c hmiss_Θ hhit_Θ
    let d_Θ : Fin (2 ^ Q) → ℂ := fun o ↦ (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o
    have hconj := quartic_conj_diagonal_mul_valid_eq U_all (validAllInd n m k (S \ T)) d_Θ hvalid_oz
      hvalid_all
    have hdiag : Matrix.diagonal (fun o ↦ d_Θ o * validAllInd n m k (S \ T) o) = (c : ℂ) •
      Matrix.diagonal (validAllInd n m k (S \ T)) + (1 - (c : ℂ)) • Matrix.diagonal (stratumExitInd
      n m k s (S \ T)) := by
      ext i j; by_cases hij : i = j
      · subst hij; dsimp only [d_Θ]; simp only [Matrix.diagonal_apply_eq, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, validAllInd_eq_hitSet_subset, stratumExitInd]
        by_cases hsub : hitSet n m k i ⊆ S \ T
        · by_cases hlt : (hitSet n m k i).card < s
          · have hmiss : stageMissOutcome n m k s i = true := decide_eq_true hlt
            have hnot_ge : ¬ (hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card) := (by omega)
            rw [ite_eq_left hsub, ite_eq_right hnot_ge, hmiss_Θ i hsub hmiss]; ring
          · have hmiss : stageMissOutcome n m k s i = false := decide_eq_false hlt
            have hge : hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card := ⟨hsub, by omega⟩
            rw [ite_eq_left hsub, ite_eq_left hge, hhit_Θ i hsub hmiss]; ring
        · have hnot_ge : ¬ (hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card) := fun h ↦ hsub h.1
          rw [ite_eq_right hsub, ite_eq_right hnot_ge]; ring
      · simp [hij]
    have hentry : (U_all.1ᴴ * Matrix.diagonal d_Θ * U_all.1) 0 0 = ((p + (1 - p) * c : ℝ) : ℂ) := by
      rw [hconj, hdiag]; simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hvalid_all]; rw [hstratum]; push_cast;
        ring
    apply Subtype.ext; change ((wp body Θ) σ).1.1 = ((p + (1 - p) * c) • (1 : HermitianMat (Fin (2 ^
      Q)) ℂ)).1; rw [wp_sexticAttemptBody_apply hm S T res Θ σ, hentry, HermitianMat.val_eq_coe,
      HermitianMat.mat_smul, HermitianMat.mat_one]; ext i j; simp [Complex.real_smul]
  have hstep : ∀ (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (c : ℝ), 0 ≤ c → c ≤ 1 → (∀ o
    : Fin
    (2 ^ Q), hitSet n m k o ⊆ S \ T → if stageMissOutcome n m k s o = true then (Θ (Store.subst σ
    res (o.val : ℤ))).1 = c • 1 else (Θ (Store.subst σ res (o.val : ℤ))).1 = 1) → ((wp body Θ) σ).1
    = (p + (1 - p) * c) • 1 := by
    intro Θ σ c _ _ hΘ; refine hstep_aux Θ σ c (fun o hsub hmiss ↦ ?_) (fun o hsub hmiss ↦ ?_)
    · have ho := hΘ o hsub; rw [ite_eq_left hmiss] at ho; have hmat := congrFun (congrFun (congrArg
        HermitianMat.mat ho) o) o; simp only [HermitianMat.mat_smul, HermitianMat.mat_one,
        Matrix.smul_apply, Matrix.one_apply_eq, Complex.real_smul, mul_one] at hmat; exact hmat
    · have ho := hΘ o hsub; have hnot : ¬ stageMissOutcome n m k s o = true := (by simp [hmiss])
      rw [ite_eq_right hnot] at ho; have hmat := congrFun (congrFun (congrArg HermitianMat.mat ho)
        o) o; simp only [HermitianMat.mat_one, Matrix.one_apply_eq] at hmat; exact hmat
  refine ⟨?_, hstep⟩
  rcases octicOccupancyTail_stage_bounds (m := m) (k := k) hs1 hs8 hsw hsr hrd with ⟨hp0, hp1⟩
  funext σ; apply Subtype.ext; rw [constAssertion_apply_of_bounds p hp0.le hp1 σ]
  have hexit := hstep_aux (liftPureProp (fun τ ↦ ¬ stageRetryGuard n m k s res τ)) σ 0
    (fun o _ hmiss ↦ by
      have hg : ¬ ¬ stageRetryGuard n m k s res (Store.subst σ res (o.val : ℤ)) :=
        (by simp [stageRetryGuard, s15_stageMissZ_natCast, hmiss])
      rw [liftPureProp_apply, ite_eq_right hg]; simp)
    (fun o _ hmiss ↦ by
      have hg : ¬ stageRetryGuard n m k s res (Store.subst σ res (o.val : ℤ)) :=
        (by simp [stageRetryGuard, s15_stageMissZ_natCast, hmiss])
      rw [liftPureProp_apply, ite_eq_left hg]; simp)
  rw [hexit]; congr 1; ring
theorem wp_sexticAttemptBody_occupancyStratum_eq {Var : Type} [DecidableEq Var] {n m k s r : ℕ} (hm
  : 1 ≤ m) (hs1 : 1 ≤ s) (hs8 : s ≤ 8) (hsw : s ≤ activeSlots m k) (hsr : s ≤ r) (hrd : r ≤ 2 ^ n)
  {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (res : Var) :
    let K := stageIterations (sexticPhiReal (activeSlots m k) r) n r
    let p := octicOccupancyTail s (activeSlots m k) r (multiP_succ K r (2 ^ n))
    let body := (sexticAttemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)
    wp body (liftPureProp (fun σ ↦ ¬ stageRetryGuard n m k s res σ)) = constAssertion p :=
  (wp_sexticAttemptBody_occupancyStratum_full hm hs1 hs8 hsw hsr hrd hTS hr res).1
theorem wp_sexticAttemptBody_conditionalStratum_step {Var : Type} [DecidableEq Var] {n m k s1 s r :
  ℕ} (hm : 1 ≤ m) (hs1 : 1 ≤ s1) (hs1_s : s1 ≤ s) (hs8 : s ≤ 8) (hsw : s ≤ activeSlots m k) (hsr : s
  ≤ r) {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) (hr : (S \ T).card = r) (res : Var) (Θ :
  CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ : Store Var) (c : ℝ) :
    let K := stageIterations (sexticPhiReal (activeSlots m k) r) n r
    let p_single := multiP_succ K r (2 ^ n)
    let p1 := octicOccupancyTail s1 (activeSlots m k) r p_single
    let ps := octicOccupancyTail s (activeSlots m k) r p_single
    let body := (sexticAttemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)
    (∀ o : Fin (2 ^ findAllQubits n m k), hitSet n m k o ⊆ S \ T → if stageMissOutcome n m k s1 o =
      true then (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o = (c : ℂ) else if stageMissOutcome n m
      k s o = true then (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o = 0 else (Θ (Store.subst σ res
      (o.val : ℤ))).1.mat o o = 1) → ((wp body Θ) σ).1 = (ps + (1 - p1) * c) • 1 := by
  have _ := hsw; intro K p_single p1 ps body hΘ; let Q := findAllQubits n m k
  let U_all := embedAllSlots n m k (singleSlotAttemptUnitary S T K)
  have hs1_8 : s1 ≤ 8 := hs1_s.trans hs8; have hs1_r : s1 ≤ r := hs1_s.trans hsr
  have hs_1 : 1 ≤ s := hs1.trans hs1_s
  have hstratum1 : (U_all.1ᴴ * Matrix.diagonal (stratumExitInd n m k s1 (S \ T)) * U_all.1) 0 0 =
    (p1 : ℂ) := conj_stratumExitInd_octic_zero_zero hs1 hs1_8 hs1_r hTS hr K
  have hstratums : (U_all.1ᴴ * Matrix.diagonal (stratumExitInd n m k s (S \ T)) * U_all.1) 0 0 = (ps
    : ℂ) := conj_stratumExitInd_octic_zero_zero hs_1 hs8 hsr hTS hr K
  have hvalid_all : (U_all.1ᴴ * Matrix.diagonal (validAllInd n m k (S \ T)) * U_all.1) 0 0 = 1 :=
    conj_validAllInd_self_zero_zero hTS K
  have hvalid_oz : ∀ o, validAllInd n m k (S \ T) o = 1 ∨ validAllInd n m k (S \ T) o = 0 := by
    intro o; rw [validAllInd_eq_hitSet_subset]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
  let d_Θ : Fin (2 ^ Q) → ℂ := fun o ↦ (Θ (Store.subst σ res (o.val : ℤ))).1.mat o o
  have hconj := quartic_conj_diagonal_mul_valid_eq U_all (validAllInd n m k (S \ T)) d_Θ hvalid_oz
    hvalid_all
  have hdiag : Matrix.diagonal (fun o ↦ d_Θ o * validAllInd n m k (S \ T) o) = Matrix.diagonal
    (stratumExitInd n m k s (S \ T)) + (c : ℂ) • Matrix.diagonal (validAllInd n m k (S \ T)) - (c :
    ℂ) • Matrix.diagonal (stratumExitInd n m k s1 (S \ T)) := by
    ext i j; by_cases hij : i = j
    · subst hij; dsimp only [d_Θ]; simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, validAllInd_eq_hitSet_subset,
        stratumExitInd]; by_cases hsub : hitSet n m k i ⊆ S \ T
      · have ho := hΘ i hsub; by_cases hlt1 : (hitSet n m k i).card < s1
        · have hlt_s : (hitSet n m k i).card < s := lt_of_lt_of_le hlt1 hs1_s
          have hmiss1 : stageMissOutcome n m k s1 i = true := decide_eq_true hlt1
          have hnot_ge1 : ¬ (hitSet n m k i ⊆ S \ T ∧ s1 ≤ (hitSet n m k i).card) := (by omega)
          have hnot_ges : ¬ (hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card) := (by omega)
          rw [ite_eq_left hmiss1] at ho; rw [ite_eq_left hsub, ite_eq_right hnot_ges, ite_eq_right
            hnot_ge1, ho]; ring
        · have hmiss1 : ¬ stageMissOutcome n m k s1 i = true := (by simp [stageMissOutcome, hlt1])
          have hge1 : hitSet n m k i ⊆ S \ T ∧ s1 ≤ (hitSet n m k i).card := ⟨hsub, by omega⟩
          rw [ite_eq_right hmiss1] at ho; by_cases hlt_s : (hitSet n m k i).card < s
          · have hmisss : stageMissOutcome n m k s i = true := decide_eq_true hlt_s
            have hnot_ges : ¬ (hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card) := (by omega)
            rw [ite_eq_left hmisss] at ho; rw [ite_eq_left hsub, ite_eq_right hnot_ges, ite_eq_left
              hge1, ho]; ring
          · have hmisss : ¬ stageMissOutcome n m k s i = true := (by simp [stageMissOutcome, hlt_s])
            have hges : hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card := ⟨hsub, by omega⟩
            rw [ite_eq_right hmisss] at ho; rw [ite_eq_left hsub, ite_eq_left hges, ite_eq_left
              hge1, ho]; ring
      · have hnot_ge1 : ¬ (hitSet n m k i ⊆ S \ T ∧ s1 ≤ (hitSet n m k i).card) := fun h ↦ hsub h.1
        have hnot_ges : ¬ (hitSet n m k i ⊆ S \ T ∧ s ≤ (hitSet n m k i).card) := fun h ↦ hsub h.1
        rw [ite_eq_right hsub, ite_eq_right hnot_ges, ite_eq_right hnot_ge1]; ring
    · simp [hij]
  have hentry : (U_all.1ᴴ * Matrix.diagonal d_Θ * U_all.1) 0 0 = ((ps + (1 - p1) * c : ℝ) : ℂ) := by
    rw [hconj, hdiag]; simp only [Matrix.mul_sub, Matrix.sub_mul, mul_add, add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      hvalid_all]; rw [hstratum1, hstratums]; push_cast; ring
  apply Subtype.ext; change ((wp body Θ) σ).1.1 = ((ps + (1 - p1) * c) • (1 : HermitianMat (Fin (2 ^
    Q)) ℂ)).1; rw [wp_sexticAttemptBody_apply hm S T res Θ σ, hentry, HermitianMat.val_eq_coe,
    HermitianMat.mat_smul, HermitianMat.mat_one]; ext i j; simp [Complex.real_smul]
private lemma s15_costBound_zero_tagFreeStep {Var : Type} [DecidableEq Var] {n w Q : ℕ} (S : Finset
  (Fin (2 ^ n))) (U : Unitary (2 ^ Q)) (hU : U * U = 1) : CostBound (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle w S)) (.qAssign (tagFreeStep U) : QProg Var (2 ^ Q)) 0 := by
  intro state; rw [expectedCost_qAssign, ofEmbeddedOracle_tagFreeStep_eq_zero (w := w) S U hU]; simp
private lemma s15_costBound_one_qAssign {Var : Type} [DecidableEq Var] {n w Q : ℕ} (S : Finset (Fin
  (2 ^ n))) (U : Unitary (2 ^ Q)) : CostBound (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle w S)) (.qAssign U : QProg Var (2 ^ Q)) 1 := by
  refine (CostBound.qAssign (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle w S)) U).mono
    ?_; unfold CostModel.ofEmbeddedOracle; dsimp
  split_ifs <;> norm_num
private lemma s15_costBound_groverIterBatchCircuit {Var : Type} [DecidableEq Var] {n m k : ℕ} (S T :
  Finset (Fin (2 ^ n))) : Lossless ((groverIterBatchCircuit (Var := Var) n m k T).compile
  QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) ∧ CostBound
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
  ((groverIterBatchCircuit (Var := Var) n m k T).compile QProg.qAssign (groverParallelMarkingOracle
  (activeSlots m k) S)) 1 := by
  rcases slotUnitaries_involution (n := n) T with ⟨_, hunmark, hdiff, _, _⟩
  simp only [groverIterBatchCircuit, OracleDynamicCircuit.compile]; refine ⟨Lossless.seq
    (Lossless.qAssign _) (Lossless.seq (Lossless.qAssign _) (Lossless.qAssign _)), ?_⟩
  have h1 := s15_costBound_one_qAssign (Var := Var) (w := activeSlots m k) S ((batchOracleReg n m
    k).embedUnitary (groverParallelMarkingOracle (activeSlots m k) S))
  have h2 := s15_costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S (embedAllSlots n m
    k (unmarkSlotUnitary T)) (quartic_embedAllSlots_mul_self n m k hunmark)
  have h3 := s15_costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S (embedAllSlots n m
    k (diffuserSlotUnitary n)) (quartic_embedAllSlots_mul_self n m k hdiff); have h23 :=
    CostBound.seq h2 h3; rw [add_zero] at h23; have h123 := CostBound.seq h1 h23
  rwa [add_zero] at h123
private lemma s15_lossless_and_costBound_repeatCircuit_groverIter {Var : Type} [DecidableEq Var] {n
  m k : ℕ} (S T : Finset (Fin (2 ^ n))) (K : ℕ) : Lossless ((repeatCircuit K (groverIterBatchCircuit
  (Var := Var) n m k T)).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) ∧
  CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
  ((repeatCircuit K (groverIterBatchCircuit (Var := Var) n m k T)).compile QProg.qAssign
  (groverParallelMarkingOracle (activeSlots m k) S)) (K : ℝ≥0) := by
  rcases s15_costBound_groverIterBatchCircuit (Var := Var) (n := n) (m := m) (k := k) S T with
    ⟨hloss_iter, hcost_iter⟩
  induction K with
  | zero =>
      simp only [repeatCircuit, OracleDynamicCircuit.compile, Nat.cast_zero]; exact ⟨Lossless.skip,
        CostBound.skip_zero _⟩
  | succ K ih =>
      simp only [repeatCircuit, OracleDynamicCircuit.compile, Nat.cast_add, Nat.cast_one]
      exact ⟨Lossless.seq ih.1 hloss_iter, CostBound.seq ih.2 hcost_iter⟩
theorem lossless_and_costBound_sexticAttemptBody {Var : Type} [DecidableEq Var] {n m k r : ℕ} (hm :
  1 ≤ m) (S T : Finset (Fin (2 ^ n))) (res : Var) :
    let body := (sexticAttemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)
    let K := stageIterations (sexticPhiReal (activeSlots m k) r) n r
    Lossless body ∧ CostBound (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots
      m k) S)) body ((K + 1 : ℕ) : ℝ≥0) := by
  have _ := hm; intro body K; let Q := findAllQubits n m k
  rcases slotUnitaries_involution (n := n) T with ⟨hprep, _, _, hver, hclear⟩
  rcases lossless_And_costBound_qsetSim_setRes (n := n) (m := m) (w := activeSlots m k) (Q := Q) S
    res 0 with ⟨hloss_qset, _, hcost_qset, _⟩
  rcases s15_lossless_and_costBound_repeatCircuit_groverIter (Var := Var) (n := n) (m := m) (k := k)
    S T K with ⟨hloss_rep, hcost_rep⟩; have hbody_eq : body = .qSeq ((qsetSim n m Q res).compile
    QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) (.qSeq (.qAssign (tagFreeStep
    (embedAllSlots n m k (prepSlotUnitary n)))) (.qSeq ((repeatCircuit K (groverIterBatchCircuit n m
    k T)).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) (.qSeq (.qAssign
    (tagFreeStep (embedAllSlots n m k (verPrepSlotUnitary n)))) (.qSeq (.qAssign ((batchOracleReg n
    m k).embedUnitary (groverParallelMarkingOracle (activeSlots m k) S))) (.qSeq (.qAssign
    (tagFreeStep (embedAllSlots n m k (clearSlotFlagsUnitary T)))) (QProg.measureRegister res
    (QRegister.whole Q))))))) := rfl; rw [hbody_eq]; refine ⟨?_, ?_⟩
  · exact Lossless.seq hloss_qset (Lossless.seq (Lossless.qAssign _) (Lossless.seq hloss_rep
      (Lossless.seq (Lossless.qAssign _) (Lossless.seq (Lossless.qAssign _) (Lossless.seq
      (Lossless.qAssign _) (lossless_measureRegister res (QRegister.whole Q)))))))
  · have hc_prep := s15_costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S
      (embedAllSlots n m k (prepSlotUnitary n)) (quartic_embedAllSlots_mul_self n m k hprep)
    have hc_ver := s15_costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S
      (embedAllSlots n m k (verPrepSlotUnitary n)) (quartic_embedAllSlots_mul_self n m k hver)
    have hc_ora := s15_costBound_one_qAssign (Var := Var) (w := activeSlots m k) S ((batchOracleReg
      n m k).embedUnitary (groverParallelMarkingOracle (activeSlots m k) S)); have hc_clr :=
      s15_costBound_zero_tagFreeStep (Var := Var) (w := activeSlots m k) S (embedAllSlots n m k
      (clearSlotFlagsUnitary T)) (quartic_embedAllSlots_mul_self n m k hclear); have hc_meas :=
      costBound_zero_measureRegister (Var := Var) (w := activeSlots m k) S res (QRegister.whole Q)
    have htot := CostBound.seq hcost_qset (CostBound.seq hc_prep (CostBound.seq hcost_rep
      (CostBound.seq hc_ver (CostBound.seq hc_ora (CostBound.seq hc_clr hc_meas)))))
    convert htot using 1
    push_cast; ring
end QuantumComputation.Specs
end
end Sec_SexticStratumSchedule
section Sec_SexticStratumStageWP
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal NNRat QHLExpectation ComplexOrder MatrixOrder

/-!
## Bimodal Conjugate-Zero Reflection & Residue-Aligned Multi-Stride Interfaces (`0` sorries)
-/
/-- State-adaptive bimodal stage mode selector: `true` when the coherent conjugate-zero
  odd-parity monadic step (`s = 1`) is selected for active slot count `w` and `r` remaining
  unmarked targets. -/
def useParityMonadicStage (w r : ℕ) : Bool := decide (w ≤ 1 ∨ r ≤ 1)
/-- Exact fraction `(1 - (1 - 2r / 2^n)^w) / 2` of `w`-slot address tuples in `(Fin (2 ^
  n))^w`
  that hit an odd number of targets in an `r`-element unmarked target set. -/
noncomputable def oddParityMarkedFraction (n w r : ℕ) : ℝ := (1 - (1 - 2 * (r : ℝ) / (2 ^ n : ℝ)) ^
    w) / 2
/-- Effective Grover half-angle `θ = arcsin(√(oddParityMarkedFraction n w r))` for the
  conjugate-zero odd-parity monadic stage. -/
noncomputable def parityHalfAngle (n w r : ℕ) : ℝ := Real.arcsin (Real.sqrt (oddParityMarkedFraction
    n w r))
/-- Global computational-basis reflection matrix `2 |0⟩⟨0| - I` on `Fin (2 ^ Q)`. -/
def zeroReflMatrix (Q : ℕ) : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ := Matrix.diagonal (fun o : Fin (2
    ^ Q) ↦ if o = 0 then (1 : ℂ) else -1)
@[simp]
theorem zeroReflMatrix_conjTranspose (Q : ℕ) : (zeroReflMatrix Q)ᴴ = zeroReflMatrix Q := by
  ext i j; simp only [zeroReflMatrix, Matrix.diagonal_conjTranspose]; congr 1; funext o
  by_cases ho : o = 0 <;> simp [ho]
@[simp] theorem zeroReflMatrix_mul_self (Q : ℕ) : zeroReflMatrix Q * zeroReflMatrix Q = 1 := by
  simp only [zeroReflMatrix, Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one
  split_ifs <;> ring
/-- Global zero-state reflection unitary `2 |0⟩⟨0| - I` on `Fin (2 ^ Q)`. -/
noncomputable def zeroReflUnitary (Q : ℕ) : Unitary (2 ^ Q) :=
  ⟨zeroReflMatrix Q, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, zeroReflMatrix_conjTranspose,
      zeroReflMatrix_mul_self]⟩
@[simp]
theorem zeroReflUnitary_val (Q : ℕ) : (zeroReflUnitary Q).1 = zeroReflMatrix Q := rfl
@[simp] theorem zeroReflUnitary_mul_self (Q : ℕ) : zeroReflUnitary Q * zeroReflUnitary Q = 1 := by
  apply Subtype.ext; exact zeroReflMatrix_mul_self Q
/-- Conjugate-zero joint `w`-slot reflection unitary `P * zeroReflUnitary Q * P`, where
  `P = embedAllSlots n m k (prepSlotUnitary n)`. -/
noncomputable def jointDiffuserUnitary (n m k : ℕ) : Unitary (2 ^ findAllQubits n m k) :=
    embedAllSlots n m k (prepSlotUnitary n) * zeroReflUnitary (findAllQubits n m k) *
    embedAllSlots n m k (prepSlotUnitary n)
private lemma unitary_list_prod_val_m10 {d : ℕ} (l : List (Unitary d)) : l.prod.1 = (l.map
  Subtype.val).prod := by
  induction l with
  | nil => rfl
  | cons u us ih => exact congrArg (u.1 * ·) ih
lemma embedAllSlots_one_m10 (n m k : ℕ) : embedAllSlots n m k 1 = 1 := by
  unfold embedAllSlots; induction slotRegList n m k <;> simp
lemma embedAllSlots_mul_m10 (n m k : ℕ) (U V : Unitary (2 ^ (n + 1))) : embedAllSlots n m k (U * V)
  = embedAllSlots n m k U * embedAllSlots n m k V := by
  apply Subtype.ext; change ((slotRegList n m k).map fun r ↦ QRegister.embedUnitary r (U *
    V)).prod.1 = ((slotRegList n m k).map fun r ↦ QRegister.embedUnitary r U).prod.1 * ((slotRegList
    n m k).map fun r ↦ QRegister.embedUnitary r V).prod.1; rw [unitary_list_prod_val_m10,
    unitary_list_prod_val_m10, unitary_list_prod_val_m10, List.map_map, List.map_map, List.map_map]
  exact ((embedList_mul_and_diagonal U.1 V.1 (fun _ ↦ 0) (slotRegList n m k)
    (slotRegList_pairwise_disjoint n m k)).1).symm
lemma embedAllSlots_mul_self_m10 (n m k : ℕ) {U : Unitary (2 ^ (n + 1))} (hU : U * U = 1) :
  embedAllSlots n m k U * embedAllSlots n m k U = 1 := by
  rw [← embedAllSlots_mul_m10, hU, embedAllSlots_one_m10]
theorem jointDiffuserUnitary_mul_self (n m k : ℕ) : jointDiffuserUnitary n m k *
  jointDiffuserUnitary n m k = 1 := by
  unfold jointDiffuserUnitary; set P := embedAllSlots n m k (prepSlotUnitary n); set Z :=
    zeroReflUnitary (findAllQubits n m k)
  have hP : P * P = 1 := embedAllSlots_mul_self_m10 n m k (slotUnitaries_involution (n := n) ∅).1
  calc P * Z * P * (P * Z * P) = P * Z * (P * P) * Z * P := by simp only [mul_assoc]
    _ = 1 := by rw [hP, mul_one, mul_assoc P Z Z, zeroReflUnitary_mul_self, mul_one, hP]
/-- One coherent conjugate-zero `w`-slot Grover iteration for unmarked target set `S \ T`. -/
noncomputable def parityIterBatchCircuit {Var : Type} (n m k : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) *
    activeSlots m k) := .seq (.oracle (batchOracleReg n m k)) (.seq (.step (tagFreeStep
    (embedAllSlots n m k (unmarkSlotUnitary T)))) (.step (tagFreeStep (jointDiffuserUnitary n m
    k))))
/-- `true` iff the `activeSlots m k` slot verification flags on global outcome `o` have odd
  parity
  (i.e. `∏ j, (if b_j = 1 then -1 else 1) = -1`). -/
def hasOddSlotFlags (n m k : ℕ) (o : Fin (2 ^ findAllQubits n m k)) : Bool :=
    decide ((((List.finRange (activeSlots m k)).map fun j ↦ if (slotOutcome n m k j o).2 = 1 then
    (-1 : ℤ) else 1).prod) = -1)
/-- Odd flag parity implies that at least one active slot has flag `1`, so `1 ≤ (hitSet n m
  k
  o).card`. -/
theorem card_hitSet_pos_of_hasOddSlotFlags {n m k : ℕ} {o : Fin (2 ^ findAllQubits n m k)} (hodd :
  hasOddSlotFlags n m k o = true) : 1 ≤ (hitSet n m k o).card := by
  unfold hasOddSlotFlags at hodd; have hprod := of_decide_eq_true hodd
  by_contra hlt; have hemp : hitSet n m k o = ∅ := Finset.card_eq_zero.mp (by omega)
  have hall : ∀ j : Fin (activeSlots m k), (slotOutcome n m k j o).2 ≠ 1 := fun j hj ↦ by
    have hm : (slotOutcome n m k j o).1 ∈ hitSet n m k o := Finset.mem_image.mpr ⟨j,
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩
    rw [hemp] at hm; exact Finset.notMem_empty _ hm
  have hfun : (fun j : Fin (activeSlots m k) ↦ if (slotOutcome n m k j o).2 = 1 then (-1 : ℤ) else
    1) = fun _ ↦ (1 : ℤ) := funext fun j ↦ ite_eq_right (hall j); rw [hfun, List.map_const',
    List.length_finRange, List.prod_replicate, one_pow] at hprod; omega
/-- `true` when outcome `o` does NOT have odd slot-flag parity. -/
def parityMissOutcome (n m k : ℕ) (o : Fin (2 ^ findAllQubits n m k)) : Bool :=
    !hasOddSlotFlags n m k o
/-- Extend `parityMissOutcome` to `z: ℤ` (returning `true` outside `0.. 2^Q - 1`). -/
def parityMissZ (n m k : ℕ) (z : ℤ) : Bool := if _h0 : 0 ≤ z then if hlt : z.toNat <
    2 ^ findAllQubits n m k then parityMissOutcome n m k ⟨z.toNat, hlt⟩ else true else true
/-- Retry loop continuation guard for the odd-parity monadic stage: continues when flag
  parity
  is even, exits when flag parity is odd. -/
def parityRetryGuard {Var : Type} (n m k : ℕ) (res : Var) : Store Var → Prop :=
    fun σ ↦ parityMissZ n m k (σ res) = true
instance {Var : Type} (n m k : ℕ) (res : Var) : DecidablePred (parityRetryGuard n m k res) := fun σ
    ↦ inferInstanceAs (Decidable (parityMissZ n m k (σ res) = true))
lemma wp_compile_branchOnTupleExpr_m10 {Step Var : Type} [DecidableEq Var] {Q w n s : ℕ}
  (compileStep : Step → QProg Var (2 ^ Q)) (oracle : Unitary (2 ^ w)) (e : Expr Var) (f : (Fin s →
  Fin (2 ^ n)) → OracleDynamicCircuit Step Var Q w) (l : List (Fin s → Fin (2 ^ n))) (xs : Fin s →
  Fin (2 ^ n)) (hxs : xs ∈ l) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (he : e σ =
    (encodeTuple
  n xs : ℤ)) : wp ((branchOnTupleExpr e f l).compile compileStep oracle) Θ σ = wp ((f xs).compile
  compileStep oracle) Θ σ := wp_compile_branchOnTupleExpr_m20 compileStep oracle e f l xs hxs Θ σ he
lemma extractHitTupleZ_of_fin_m10 (n m k s : ℕ) (o : Fin (2 ^ findAllQubits n m k)) :
  extractHitTupleZ n m k s (o.val : ℤ) = extractHitTuple n m k s o :=
  extractHitTupleZ_of_fin_m20 n m k s o
lemma validStageStore_appendTuple_m10 {Var : Type} [DecidableEq Var] {n m k p s : ℕ} (hps : p + s ≤
  k) {S : Finset (Fin (2 ^ n))} {xs : Fin p → Fin (2 ^ n)} (hxs_inj : Function.Injective xs)
  (hxs_sub : Finset.univ.image xs ⊆ S) {ys : Fin s → Fin (2 ^ n)} (hys_inj : Function.Injective ys)
  (hys_mem : ∀ j : Fin s, ys j ∈ S \ Finset.univ.image xs) (res : Var) (τ : Store Var) :
  ValidStageStore n S (p + s) res (Store.subst τ res ((encodeTupleFin n m k hps (appendTuple xs
  ys)).val : ℤ)) :=
  ⟨appendTuple xs ys, appendTuple_injective hxs_inj hys_inj fun i j h ↦ (Finset.mem_sdiff.mp
    (hys_mem j)).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i,
    h⟩), image_appendTuple_subset hxs_sub fun j ↦ (Finset.mem_sdiff.mp (hys_mem j)).1,
    by simp [encodeTupleFin]⟩
def ValidHitExit_m10 {Var : Type} (n m k s : ℕ) (R : Finset (Fin (2 ^ n))) (res : Var) (τ : Store
    Var) : Prop := Function.Injective (extractHitTupleZ n m k s (τ res)) ∧ ∀ i : Fin s,
    extractHitTupleZ n m k s (τ res) i ∈ R
lemma wp_stageBranch_step3_m10 {Var : Type} [DecidableEq Var] {n m k p s : ℕ} (hps : p + s ≤ k)
    {S : Finset (Fin (2 ^ n))} {xs : Fin p → Fin (2 ^ n)} (hxs_inj : Function.Injective xs) (hxs_sub
    : Finset.univ.image xs ⊆ S) (res : Var) (τ : Store Var) (h_hit : ValidHitExit_m10 n m k s (S \
    Finset.univ.image xs) res τ) : wp ((branchOnTupleExpr (fun σ ↦ (encodeTuple n (extractHitTupleZ
    n m k s (σ res)) : ℤ)) (fun ys : Fin s → Fin (2 ^ n) ↦ setResCircuit n m (findAllQubits n m k)
    res (encodeTupleFin n m k hps (appendTuple xs ys))) (enumTuples n s)).compile QProg.qAssign
    (groverParallelMarkingOracle (activeSlots m k) S)) (liftPureProp (ValidStageStore n S (p + s)
    res)) τ = 1 := by exact wp_commitHitTuple hps hxs_inj hxs_sub res τ h_hit
lemma costBound_zero_branchOnTupleExpr_setRes_m10 {Var : Type} [DecidableEq Var] {n m w Q s : ℕ} (S
  : Finset (Fin (2 ^ n))) (e : Expr Var) (res : Var) (target : (Fin s → Fin (2 ^ n)) → Fin (2 ^ Q))
  (l : List (Fin s → Fin (2 ^ n))) : CostBound (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle w S)) ((branchOnTupleExpr e (fun ys ↦ setResCircuit n m Q res (target
  ys)) l).compile QProg.qAssign (groverParallelMarkingOracle w S)) 0 := by
  set G := groverParallelMarkingOracle w S
  set f := fun ys : Fin s → Fin (2 ^ n) ↦ setResCircuit n m Q res (target ys)
  induction l with
  | nil => exact CostBound.skip_zero _
  | cons ys rest ih =>
    rw [show (branchOnTupleExpr e f (ys :: rest)).compile QProg.qAssign G = .qIf _ ((f ys).compile
      QProg.qAssign G) ((branchOnTupleExpr e f rest).compile QProg.qAssign G) from rfl, ← max_self
      (0 : ℝ≥0)]; exact CostBound.qIf _ (lossless_And_costBound_qsetSim_setRes (w := w) S res
      _).2.2.2 ih
lemma expect_true_false_eq_cqTrace_m10 {Var : Type} {d : ℕ} (cond : Store Var → Prop) [DecidablePred
  cond] (Δ : CQState (Store Var) d) (Θ : CQAssertion (Store Var) d) (hΔ : 𝔼[Δ, Θ] = CQState.trace Δ)
    : 𝔼[Δ.cqTrueSt
  cond, Θ] = CQState.trace (Δ.cqTrueSt cond) ∧ 𝔼[Δ.cqFalseSt cond, Θ] = CQState.trace (Δ.cqFalseSt
  cond) := by
  have hp : 𝔼[Δ, Θ] = 𝔼[Δ.cqTrueSt cond, Θ] + 𝔼[Δ.cqFalseSt cond, Θ] :=
    (by simpa [ite_self] using cqExpect_ite_split cond Δ Θ Θ)
  have ht : (CQState.trace (Δ.cqTrueSt cond) : ℝ) + CQState.trace (Δ.cqFalseSt cond) =
    CQState.trace Δ := by exact_mod_cast CQState.trace_cqTrueSt_add_trace_cqFalseSt cond Δ
  have h1 := (expect_mono le_rfl (le_top : Θ ≤ ⊤)).trans_eq (expect_top (Δ.cqTrueSt cond))
  have h2 := (expect_mono le_rfl (le_top : Θ ≤ ⊤)).trans_eq (expect_top (Δ.cqFalseSt cond))
  exact ⟨by linarith, by linarith⟩
lemma stateMass_trueState_eq_zero_of_disjoint_m10 {Var : Type} {d : ℕ} (cond : Store Var → Prop)
  [DecidablePred cond] (Δ : CQState (Store Var) d) (Θ : CQAssertion (Store Var) d) (hΔ : 𝔼[Δ, Θ] =
    CQState.trace Δ)
  (hdisj : ∀ σ, cond σ → Θ σ = ⊥) : ((Δ.cqTrueSt cond).trace : ℝ≥0∞) = 0 := by
  have htf := (expect_true_false_eq_cqTrace_m10 cond Δ Θ hΔ).1
  have hfun : (fun σ ↦ if cond σ then (⊥ : CQAssertion (Store Var) d) σ else Θ σ) = Θ :=
    funext fun σ ↦ if hc : cond σ then by simp [hc, hdisj σ hc] else by simp [hc]
  have hpart := cqExpect_ite_split cond Δ ⊥ Θ; rw [hfun, expect_bot, zero_add] at hpart
  have hp2 : 𝔼[Δ, Θ] = 𝔼[Δ.cqTrueSt cond, Θ] + 𝔼[Δ.cqFalseSt cond, Θ] :=
    (by simpa [ite_self] using cqExpect_ite_split cond Δ Θ Θ)
  exact ENNReal.coe_eq_zero.mpr (NNReal.coe_eq_zero.mp
    (show (CQState.trace (Δ.cqTrueSt cond) : ℝ) = 0 by linarith))
lemma card_sdiff_image_of_valid_m10 {n k p r : ℕ} (hrk : r ≤ k) (hp : k - r = p) {S : Finset (Fin (2
  ^ n))} (hS : S ∈ groverTargetSets n k) {xs : Fin p → Fin (2 ^ n)} (hxs_inj : Function.Injective
  xs) (hxs_sub : Finset.univ.image xs ⊆ S) : (S \ Finset.univ.image xs).card = r := by
  rw [Finset.card_sdiff_of_subset hxs_sub, (Finset.mem_powersetCard.mp hS).2,
    Finset.card_image_of_injective _ hxs_inj, Finset.card_fin]; omega
/-- Composite `Q`-qubit unitary for one `K`-iteration conjugate-zero parity attempt before
  measurement. -/
noncomputable def parityAttemptUnitary (n m k : ℕ) (S T : Finset (Fin (2 ^ n))) (K : ℕ) : Unitary (2
    ^ findAllQubits n m k) := embedAllSlots n m k (clearSlotFlagsUnitary T) *
    embedAllSlots n m k (groverSetMarkingOracle S) * embedAllSlots n m k (verPrepSlotUnitary n) *
    (jointDiffuserUnitary n m k * embedAllSlots n m k (unmarkSlotUnitary T) * embedAllSlots n m k
    (groverSetMarkingOracle S)) ^ K * embedAllSlots n m k (prepSlotUnitary n)
lemma parityMissZ_natCast_m10 (n m k : ℕ) (o : Fin (2 ^ findAllQubits n m k)) : parityMissZ n m k
  (o.val : ℤ) = parityMissOutcome n m k o := by
  have hlt : (o.val : ℤ).toNat < 2 ^ findAllQubits n m k := by rw [Int.toNat_natCast]; exact o.isLt
  unfold parityMissZ; rw [dite_eq_left (Int.natCast_nonneg o.val), dite_eq_left hlt]
  exact congrArg (parityMissOutcome n m k) (Fin.ext (Int.toNat_natCast o.val))
theorem one_sub_mul_le_pow_and_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (w : ℕ) : 1 - (w : ℝ) * x ≤ (1
  - x) ^ w ∧ (1 - x) ^ w ≤ 1 - (w : ℝ) * x + (w : ℝ) ^ 2 * x ^ 2 := by
  induction w with
  | zero => simp
  | succ w ih =>
    have h1x : 0 ≤ 1 - x := (by linarith); have hwx3 : 0 ≤ (w : ℝ) ^ 2 * x ^ 3 := (by positivity)
    rw [pow_succ]; push_cast
    exact ⟨by nlinarith [mul_le_mul_of_nonneg_right ih.1 h1x],
      by nlinarith [mul_le_mul_of_nonneg_right ih.2 h1x, sq_nonneg x]⟩
theorem oddParityMarkedFraction_bounds {n w r : ℕ} (hrN : 2 * r ≤ 2 ^ n) : ((w : ℝ) * (r : ℝ) / (2 ^
  n : ℝ)) * (1 - 2 * (w : ℝ) * (r : ℝ) / (2 ^ n : ℝ)) ≤ oddParityMarkedFraction n w r ∧
  oddParityMarkedFraction n w r ≤ (w : ℝ) * (r : ℝ) / (2 ^ n : ℝ) := by
  set x : ℝ := 2 * (r : ℝ) / (2 ^ n : ℝ)
  have hx1 : x ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hrN)
  obtain ⟨hlow, hhigh⟩ := one_sub_mul_le_pow_and_le (by positivity : 0 ≤ x) hx1 w
  unfold oddParityMarkedFraction; change _ ≤ (1 - (1 - x) ^ w) / 2 ∧ (1 - (1 - x) ^ w) / 2 ≤ _
  constructor
  · refine le_trans ?_ (by linarith : (1 - (1 - (w : ℝ) * x + (w : ℝ) ^ 2 * x ^ 2)) / 2 ≤ _)
    dsimp [x]; ring_nf; exact le_rfl
  · refine le_trans (by linarith : _ ≤ ((w : ℝ) * x) / 2) ?_; dsimp [x]; ring_nf; exact le_rfl
def invSqrtLowerNum8 (r : ℕ) : ℕ :=
  match r with
  | 1 => 100000000 | 2 => 70710678 | 3 => 57735026 | 4 => 50000000 | 5 => 44721359 | 6 => 40824829 |
    7 => 37796447 | 8 => 35355339 | 9 => 33333333 | 10 => 31622776 | 11 => 30151134 | 12 => 28867513
      | 13 => 27735009 | 14 => 26726124 | 15 => 25819888 | 16 => 25000000 | 17 => 24253562 | 18 =>
        23570226 | 19 => 22941573 | 20 => 22360679 | 21 => 21821789 | 22 => 21320071 | 23 =>
          20851441 | 24 => 20412414 | 25 => 20000000 | 26 => 19611613 | 27 => 19245008 | 28 =>
            18898223 | 29 => 18569533 | 30 => 18257418 | 31 => 17960530 | 32 => 17677669
  | _ => 0
def invSqrtUpperNum8 (r : ℕ) : ℕ :=
  match r with
  | 1 => 100000000 | 2 => 70710679 | 3 => 57735027 | 4 => 50000000 | 5 => 44721360 | 6 => 40824830 |
    7 => 37796448 | 8 => 35355340 | 9 => 33333334 | 10 => 31622777 | 11 => 30151135 | 12 => 28867514
      | 13 => 27735010 | 14 => 26726125 | 15 => 25819889 | 16 => 25000000 | 17 => 24253563 | 18 =>
        23570227 | 19 => 22941574 | 20 => 22360680 | 21 => 21821790 | 22 => 21320072 | 23 =>
          20851442 | 24 => 20412415 | 25 => 20000000 | 26 => 19611614 | 27 => 19245009 | 28 =>
            18898224 | 29 => 18569534 | 30 => 18257419 | 31 => 17960531 | 32 => 17677670
  | _ => 100000000
def sqrtMUpperNum8 (m : ℕ) : ℕ :=
  match m with
  | 1 => 100000000 | 2 => 141421357 | 3 => 173205081 | 4 => 200000000 | 5 => 223606798 | 6 =>
    244948975 | 7 => 264575132 | 8 => 282842713 | 9 => 300000000 | 10 => 316227767 | 11 => 331662480
      | 12 => 346410162 | 13 => 360555128 | 14 => 374165739 | 15 => 387298335 | 16 => 400000000 | 17
        => 412310563 | 18 => 424264069 | 19 => 435889895 | 20 => 447213596 | 21 => 458257570 | 22 =>
          469041576 | 23 => 479583153 | 24 => 489897949 | 25 => 500000000 | 26 => 509901952 | 27 =>
            519615243 | 28 => 529150263 | 29 => 538516481 | 30 => 547722558 | 31 => 556776437 | 32
              => 565685425
  | _ => m * 100000000
def harmonicLowerScaled8 : ℕ → ℕ
  | 0 => 0
  | k + 1 => harmonicLowerScaled8 k + invSqrtLowerNum8 (k + 1)
/-- Six-threshold sextic stage branch: runs `.qWhile` on the stratum-1 exit guard
  `stageRetryGuard n m k s1 res`, then branches via a 5-deep `.qIf` cascade on
  `stageRetryGuard n m k s2 res`.. `stageRetryGuard n m k s6 res`
  to commit `s1`.. `s6` newly discovered targets. -/
noncomputable def sexticStratumBranchCircuit {Var : Type} (n m k : ℕ) {p s1 s2 s3 s4 s5 s6 : ℕ}
    (hps1 : p + s1 ≤ k) (hps2 : p + s2 ≤ k) (hps3 : p + s3 ≤ k) (hps4 : p + s4 ≤ k) (hps5 : p + s5 ≤
    k) (hps6 : p + s6 ≤ k) (r : ℕ) (xs : Fin p → Fin (2 ^ n)) (res : Var) (cont1 cont2 cont3 cont4
    cont5 cont6 : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k)
    ((n + 1) * activeSlots m k)) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
    (findAllQubits n m k) ((n + 1) * activeSlots m k) :=
  let Q := findAllQubits n m k
  let T := Finset.univ.image xs
  .seq (setResCircuit n m Q res 0) (.seq (.qWhile (stageRetryGuard n m k s1 res) (sexticAttemptBody
    n m k r T res)) (.qIf (stageRetryGuard n m k s2 res) (.seq (commitHitTuple n m k hps1 xs res)
    cont1) (.qIf (stageRetryGuard n m k s3 res) (.seq (commitHitTuple n m k hps2 xs res) cont2)
    (.qIf (stageRetryGuard n m k s4 res) (.seq (commitHitTuple n m k hps3 xs res) cont3) (.qIf
    (stageRetryGuard n m k s5 res) (.seq (commitHitTuple n m k hps4 xs res) cont4) (.qIf
    (stageRetryGuard n m k s6 res) (.seq (commitHitTuple n m k hps5 xs res) cont5) (.seq
    (commitHitTuple n m k hps6 xs res) cont6)))))))
/-- Stratum dispatch over all `p`-tuples `xs ∈ enumTuples n p` for a 6-stratum sextic stage. -/
noncomputable def sexticStratumCircuit {Var : Type} (n m k p r s1 s2 s3 s4 s5 s6 : ℕ) (res : Var)
    (cont1 cont2 cont3 cont4 cont5 cont6 : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k))
    Var (findAllQubits n m k) ((n + 1) * activeSlots m k)) : OracleDynamicCircuit (Unitary (2 ^
    findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) * activeSlots m k) := if hps : p + s1 ≤
    k ∧ p + s2 ≤ k ∧ p + s3 ≤ k ∧ p + s4 ≤ k ∧ p + s5 ≤ k ∧ p + s6 ≤ k then branchOnTupleExpr (fun σ
    ↦ σ res) (fun xs ↦ sexticStratumBranchCircuit n m k hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1
    hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res cont1 cont2 cont3 cont4 cont5 cont6) (enumTuples n
    p) else .skip
/-- Expected wall-clock query cost of the `.qWhile` loop in a sextic stage at remaining
  target count `r`. -/
noncomputable def sexticLoopCostNNReal (n m k r : ℕ) : ℝ≥0 :=
  let w := activeSlots m k
  let s1 := sexticStratum1 w r
  let K := stageIterations (sexticPhiReal w r) n r
  (Real.toNNReal (octicOccupancyTail s1 w r (multiP_succ K r (2 ^ n))))⁻¹ * ((K + 1 : ℕ) : ℝ≥0)
/-- Conditioned Loewner-limit surplus probability `min(1, T_s(w, r, p) / T_{s1}(w, r, p))`
  upon exiting `.qWhile (stageRetryGuard n m k s1 res)`. -/
noncomputable def sexticCondProbNNReal (n m k s1 s r : ℕ) : ℝ≥0 :=
  let w := activeSlots m k
  let K := stageIterations (sexticPhiReal w r) n r
  let p := multiP_succ K r (2 ^ n)
  Real.toNNReal (min 1 (octicOccupancyTail s w r p / octicOccupancyTail s1 w r p))
/-- Stratum-6 conditioned surplus-capture probability. -/
noncomputable def sexticProb6NNReal (n m k r : ℕ) : ℝ≥0 :=
  let w := activeSlots m k
  sexticCondProbNNReal n m k (sexticStratum1 w r) (sexticStratum6 w r) r
/-- Stratum-5 conditioned surplus-capture probability (monotone envelope `≥ q6`). -/
noncomputable def sexticProb5NNReal (n m k r : ℕ) : ℝ≥0 :=
  let w := activeSlots m k
  max (sexticCondProbNNReal n m k (sexticStratum1 w r) (sexticStratum5 w r) r) (sexticProb6NNReal n
    m k r)
/-- Stratum-4 conditioned surplus-capture probability (monotone envelope `≥ q5`). -/
noncomputable def sexticProb4NNReal (n m k r : ℕ) : ℝ≥0 :=
  let w := activeSlots m k
  max (sexticCondProbNNReal n m k (sexticStratum1 w r) (sexticStratum4 w r) r) (sexticProb5NNReal n
    m k r)
/-- Stratum-3 conditioned surplus-capture probability (monotone envelope `≥ q4`). -/
noncomputable def sexticProb3NNReal (n m k r : ℕ) : ℝ≥0 :=
  let w := activeSlots m k
  max (sexticCondProbNNReal n m k (sexticStratum1 w r) (sexticStratum3 w r) r) (sexticProb4NNReal n
    m k r)
/-- Stratum-2 conditioned surplus-capture probability (monotone envelope `≥ q3`). -/
noncomputable def sexticProb2NNReal (n m k r : ℕ) : ℝ≥0 :=
  let w := activeSlots m k
  max (sexticCondProbNNReal n m k (sexticStratum1 w r) (sexticStratum2 w r) r) (sexticProb3NNReal n
    m k r)
/-- Six-stratum exit invariant after the `.qWhile` loop on `stageRetryGuard n m k s1 res`. -/
def ValidSexticExit {Var : Type} (n m k s1 s2 s3 s4 s5 s6 : ℕ) (R : Finset (Fin (2 ^ n))) (res :
    Var) (τ : Store Var) : Prop := ValidHitExit_m20 n m k s1 R res τ ∧ (¬ stageRetryGuard n m k s2
    res τ → ValidHitExit_m20 n m k s2 R res τ) ∧ (¬ stageRetryGuard n m k s3 res τ →
    ValidHitExit_m20 n m k s3 R res τ) ∧ (¬ stageRetryGuard n m k s4 res τ → ValidHitExit_m20 n m k
    s4 R res τ) ∧ (¬ stageRetryGuard n m k s5 res τ → ValidHitExit_m20 n m k s5 R res τ) ∧ (¬
    stageRetryGuard n m k s6 res τ → ValidHitExit_m20 n m k s6 R res τ)
private noncomputable def sexticLoopApproxAssertion {Var : Type} (n m k s1 s2 s3 s4 s5 s6 : ℕ) (R :
    Finset (Fin (2 ^ n))) (res : Var) (prob : ℝ) (iter : ℕ) : CQAssertion (Store Var) (2 ^
      findAllQubits n m
    k) := fun σ ↦ if stageRetryGuard n m k s1 res σ then constAssertion (1 - (1 - prob) ^
    iter) σ else liftPureProp (ValidSexticExit n m k s1 s2 s3 s4 s5 s6 R res) σ
private lemma wp_qWhile_validSexticExit {Var : Type} [DecidableEq Var] {n m k s1 s2 s3 s4 s5 s6 : ℕ}
  {R : Finset (Fin (2 ^ n))} (res : Var) (body : QProg Var (2 ^ findAllQubits n m k)) (Θ₃ :
  CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (prob : ℝ) (hprob_pos : 0 < prob) (hprob_le1 :
    prob ≤
  1) (hΨ_le_Θ₃ : liftPureProp (ValidSexticExit n m k s1 s2 s3 s4 s5 s6 R res) ≤ Θ₃) (hstep : ∀ (Θ :
  CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (σ : Store Var) (c : ℝ), 0 ≤ c → c ≤ 1 → (∀ o :
    Fin (2
  ^ findAllQubits n m k), hitSet n m k o ⊆ R → if stageMissOutcome n m k s1 o = true then (Θ
  (Store.subst σ res (o.val : ℤ))).1 = c • 1 else (Θ (Store.subst σ res (o.val : ℤ))).1 = 1) → ((wp
  body Θ) σ).1 = (prob + (1 - prob) * c) • 1) (τ : Store Var) (hguard : stageRetryGuard n m k s1 res
  τ) : wp (.qWhile (stageRetryGuard n m k s1 res) body) Θ₃ τ = 1 := by
  have h1p0 : 0 ≤ 1 - prob := (by linarith); have h1p1 : 1 - prob < 1 := (by linarith)
  let g1 := stageRetryGuard n m k s1 res; let Ψ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)
    :=
    liftPureProp (ValidSexticExit n m k s1 s2 s3 s4 s5 s6 R res)
  have hbnd : ∀ i : ℕ, 0 ≤ 1 - (1 - prob) ^ i ∧ 1 - (1 - prob) ^ i ≤ 1 := fun i ↦
    ⟨by linarith [pow_le_one₀ h1p0 h1p1.le (n := i)], by linarith [pow_nonneg h1p0 i]⟩
  have happrox_le : ∀ iter : ℕ, sexticLoopApproxAssertion n m k s1 s2 s3 s4 s5 s6 R res prob iter ≤
    whileRecWP (wp body) g1 (iter + 1) Ψ := by
    intro iter; induction iter with
    | zero =>
        intro σ; by_cases hg : g1 σ
        · simp only [sexticLoopApproxAssertion, g1, hg, ↓reduceIte, pow_zero, sub_self]
          change (constAssertion 0 σ).1 ≤ _; rw [constAssertion_apply_of_bounds 0 le_rfl
            zero_le_one, zero_smul]; exact (whileRecWP (wp body) g1 1 Ψ σ).2.1
        · simp [sexticLoopApproxAssertion, g1, Ψ, hg, whileRecWP]
    | succ iter ih =>
        intro σ; by_cases hg : g1 σ
        · simp only [sexticLoopApproxAssertion, g1, hg, ↓reduceIte, whileRecWP]
          refine le_trans ?_ (wp_mono body ih σ)
          rcases hbnd iter with ⟨hc0, hc1⟩; rcases hbnd (iter + 1) with ⟨hc0', hc1'⟩; have hwp_eq :=
            hstep (sexticLoopApproxAssertion n m k s1 s2 s3 s4 s5 s6 R res prob iter) σ (1 - (1 -
            prob) ^ iter) hc0 hc1 ?_
          · change (constAssertion (1 - (1 - prob) ^ (iter + 1)) σ).1 ≤ _
            rw [constAssertion_apply_of_bounds _ hc0' hc1',
              ← show prob + (1 - prob) * (1 - (1 - prob) ^ iter) = 1 - (1 - prob) ^ (iter + 1) by
                rw [pow_succ']; ring,
              ← hwp_eq]
          · intro o hsub; let σ' := Store.subst σ res (o.val : ℤ); have hres_o : σ' res = (o.val :
              ℤ) := Store.subst_self σ res _; by_cases hmiss : stageMissOutcome n m k s1 o = true
            · have hg_o : g1 σ' := by simp [g1, σ', stageRetryGuard, stageMissZ_of_fin_m20, hmiss]
              rw [ite_eq_left hmiss, sexticLoopApproxAssertion, ite_eq_left hg_o,
                constAssertion_apply_of_bounds _ hc0 hc1]
            · have hg_o : ¬ g1 σ' :=
                (by simp [g1, σ', stageRetryGuard, stageMissZ_of_fin_m20, hmiss])
              have hhit_of : ∀ {s : ℕ}, ¬ stageRetryGuard n m k s res σ' → ValidHitExit_m20 n m k s
                R res σ' := fun {s} hgs ↦ by
                have hms : stageMissOutcome n m k s o = false :=
                  (by simpa [σ', stageRetryGuard, stageMissZ_of_fin_m20] using hgs)
                unfold ValidHitExit_m20; rw [hres_o, extractHitTupleZ_of_fin_m20]
                exact extractHitTuple_injective_and_mem hsub (by simpa [stageMissOutcome] using hms)
              have hhit : ValidSexticExit n m k s1 s2 s3 s4 s5 s6 R res σ' := ⟨hhit_of hg_o,
                hhit_of, hhit_of, hhit_of, hhit_of, hhit_of⟩; rw [ite_eq_right hmiss,
                sexticLoopApproxAssertion, ite_eq_right hg_o, liftPureProp_apply, ite_eq_left hhit];
                rfl
        · simp [sexticLoopApproxAssertion, g1, Ψ, hg, whileRecWP]
  have h1_le : (1 : HermitianMat (Fin (2 ^ findAllQubits n m k)) ℂ) ≤ (wp (.qWhile g1 body) Θ₃ τ).1
    := by
    refine hermitian_le_of_geometric_sub_smul_le (1 - prob) h1p0 h1p1 1 1 _ fun iter ↦ ?_
    rcases hbnd iter with ⟨hc0, hc1⟩
    have hsub : (1 : HermitianMat (Fin (2 ^ findAllQubits n m k)) ℂ) - (1 - prob) ^ iter • 1 =
      (sexticLoopApproxAssertion n m k s1 s2 s3 s4 s5 s6 R res prob iter τ).1 := by
      simp [sexticLoopApproxAssertion, hguard, constAssertion_apply_of_bounds _ hc0 hc1, sub_smul]
    rw [hsub]; exact (happrox_le iter τ).trans ((whileRecWP_arg_mono (wp_mono body) g1 (iter + 1)
      hΨ_le_Θ₃ τ).trans (whileRecWP_le_wp_qWhile g1 body (iter + 1) Θ₃ τ))
  exact Subtype.ext (le_antisymm (wp (.qWhile g1 body) Θ₃ τ).2.2 h1_le)
private lemma wp_init_qWhile_validSexticExit {Var : Type} [DecidableEq Var] {n m k p s1 s2 s3 s4 s5
  s6 r : ℕ} (hm : 1 ≤ m) (hs1_ge1 : 1 ≤ s1) (hs1_le8 : s1 ≤ 8) (hsw1 : s1 ≤ activeSlots m k) (hsr1 :
  s1 ≤ r) (hrd : r ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))} {xs : Fin p → Fin (2 ^ n)} (hxs_sub :
  Finset.univ.image xs ⊆ S) (hr_card : (S \ Finset.univ.image xs).card = r) (res : Var) (Θ₃ :
  CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (hΨ_le_Θ₃ : liftPureProp (ValidSexticExit n m k
    s1 s2
  s3 s4 s5 s6 (S \ Finset.univ.image xs) res) ≤ Θ₃) (σ : Store Var) : wp (.qSeq ((setResCircuit n m
  (findAllQubits n m k) res 0).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k)
  S)) (.qWhile (stageRetryGuard n m k s1 res) ((sexticAttemptBody n m k r (Finset.univ.image xs)
  res).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)))) Θ₃ σ = 1 := by
  rw [wp_qSeq]; refine Subtype.ext (Subtype.ext ?_); rw [wp_setResCircuit]
  rcases octicOccupancyTail_stage_bounds hs1_ge1 hs1_le8 hsw1 hsr1 hrd with ⟨hp0, hp1⟩
  have hw := wp_qWhile_validSexticExit res _ Θ₃ _ hp0 hp1 hΨ_le_Θ₃
    (wp_sexticAttemptBody_occupancyStratum_full hm hs1_ge1 hs1_le8 hsw1 hsr1 hrd hxs_sub hr_card
    res).2 (Store.subst σ res 0) (stageRetryGuard_subst_zero_m20 n m k s1 hs1_ge1 res σ)
  have hmat : (wp (.qWhile (stageRetryGuard n m k s1 res) _) Θ₃ (Store.subst σ res ((0 : Fin (2 ^
    findAllQubits n m k)).val : ℤ))).1.1 0 0 = 1 :=
    congrArg (fun A : Observable (Fin (2 ^ findAllQubits n m k)) ↦ A.1.1 0 0) hw
  rw [hmat, one_smul]; rfl
private lemma s20_wp_seq_of_wp_first_eq_one {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d] {P :
  Store Var → Prop} {c₁ c₂ : QProg Var d} {Φ : CQAssertion (Store Var) d} {τ : Store Var} (hc₁ : wp
    c₁
  (liftPureProp P) τ = 1) (hc₂ : ∀ τ', P τ' → wp c₂ Φ τ' = 1) : wp (.qSeq c₁ c₂) Φ τ = 1 := by
  rw [wp_qSeq]; refine le_antisymm (wp c₁ (wp c₂ Φ) τ).2.2 (hc₁ ▸ wp_mono c₁ (fun τ' ↦ ?_) τ)
  by_cases hP : P τ'
  · rw [liftPureProp_apply, ite_eq_left hP, hc₂ τ' hP]
  · rw [liftPureProp_apply, ite_eq_right hP]; exact zero_le
theorem wp_sexticStratumBranchCircuit {Var : Type} [DecidableEq Var] {n m k p s1 s2 s3 s4 s5 s6 r :
  ℕ} (hm : 1 ≤ m) (hps1 : p + s1 ≤ k) (hps2 : p + s2 ≤ k) (hps3 : p + s3 ≤ k) (hps4 : p + s4 ≤ k)
  (hps5 : p + s5 ≤ k) (hps6 : p + s6 ≤ k) (hs1_ge1 : 1 ≤ s1) (hs1_le8 : s1 ≤ 8) (hsw1 : s1 ≤
  activeSlots m k) (hsr1 : s1 ≤ r) (hrd : r ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))} {xs : Fin p → Fin (2
  ^ n)} (hxs_inj : Function.Injective xs) (hxs_sub : Finset.univ.image xs ⊆ S) (hr_card : (S \
  Finset.univ.image xs).card = r) (res : Var) (cont1 cont2 cont3 cont4 cont5 cont6 :
  OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) *
  activeSlots m k)) (Φ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (hcont1 : ∀ τ : Store
    Var,
  ValidStageStore n S (p + s1) res τ → wp (cont1.compile QProg.qAssign (groverParallelMarkingOracle
  (activeSlots m k) S)) Φ τ = 1) (hcont2 : ∀ τ : Store Var, ValidStageStore n S (p + s2) res τ → wp
  (cont2.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1) (hcont3 :
  ∀ τ : Store Var, ValidStageStore n S (p + s3) res τ → wp (cont3.compile QProg.qAssign
  (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1) (hcont4 : ∀ τ : Store Var,
  ValidStageStore n S (p + s4) res τ → wp (cont4.compile QProg.qAssign (groverParallelMarkingOracle
  (activeSlots m k) S)) Φ τ = 1) (hcont5 : ∀ τ : Store Var, ValidStageStore n S (p + s5) res τ → wp
  (cont5.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1) (hcont6 :
  ∀ τ : Store Var, ValidStageStore n S (p + s6) res τ → wp (cont6.compile QProg.qAssign
  (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1) (σ : Store Var) : wp
  ((sexticStratumBranchCircuit n m k hps1 hps2 hps3 hps4 hps5 hps6 r xs res cont1 cont2 cont3 cont4
  cont5 cont6).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ σ = 1 :=
  by
  let Q := findAllQubits n m k; let T := Finset.univ.image xs
  let G := groverParallelMarkingOracle (activeSlots m k) S
  let comp := fun c : OracleDynamicCircuit _ Var Q ((n + 1) * activeSlots m k) ↦
    c.compile QProg.qAssign G
  let c_init := comp (setResCircuit n m Q res 0); let body := comp (sexticAttemptBody n m k r T res)
  let c_while := QProg.qWhile (stageRetryGuard n m k s1 res) body
  let c_if := comp (.qIf (stageRetryGuard n m k s2 res)
    (.seq (commitHitTuple n m k hps1 xs res) cont1) (.qIf (stageRetryGuard n m k s3 res)
    (.seq (commitHitTuple n m k hps2 xs res) cont2) (.qIf (stageRetryGuard n m k s4 res)
    (.seq (commitHitTuple n m k hps3 xs res) cont3) (.qIf (stageRetryGuard n m k s5 res)
    (.seq (commitHitTuple n m k hps4 xs res) cont4) (.qIf (stageRetryGuard n m k s6 res)
    (.seq (commitHitTuple n m k hps5 xs res) cont5)
    (.seq (commitHitTuple n m k hps6 xs res) cont6))))))
  have hbr : ∀ {s : ℕ} (hps : p + s ≤ k) {ct} (hct : ∀ τ, ValidStageStore n S (p + s) res τ → wp
    (comp ct) Φ τ = 1) {τ}, ValidHitExit_m20 n m k s (S \ T) res τ → wp (.qSeq (comp (commitHitTuple
    n m k hps xs res)) (comp ct)) Φ τ = 1 := fun {s} hps {ct} hct {τ} hh ↦
    s20_wp_seq_of_wp_first_eq_one (wp_commitHitTuple (m := m) hps hxs_inj hxs_sub res τ hh) hct
  have hif : ∀ {g : Store Var → Prop} [DecidablePred g] {c1 c2 : QProg Var (2 ^ Q)} {τ}, (g τ → wp
    c1 Φ τ = 1) → (¬ g τ → wp c2 Φ τ = 1) → wp (.qIf g c1 c2) Φ τ = 1 := by
    intro g _ c1 c2 τ h1 h2; by_cases hg : g τ
    · simp only [wp_qIf, hg, ↓reduceIte]; exact h1 hg
    · simp only [wp_qIf, hg, ↓reduceIte]; exact h2 hg
  have hle_if : liftPureProp (ValidSexticExit n m k s1 s2 s3 s4 s5 s6 (S \ T) res) ≤ wp c_if Φ := by
    intro τ; by_cases hsex : ValidSexticExit n m k s1 s2 s3 s4 s5 s6 (S \ T) res τ
    · rw [liftPureProp_apply, ite_eq_left hsex]; refine le_of_eq (Eq.symm ?_); dsimp only [c_if,
        comp, OracleDynamicCircuit.compile]
      exact hif (fun _ ↦ hbr hps1 hcont1 hsex.1) fun h2 ↦ hif (fun _ ↦ hbr hps2 hcont2 (hsex.2.1
        h2)) fun h3 ↦ hif (fun _ ↦ hbr hps3 hcont3 (hsex.2.2.1 h3)) fun h4 ↦ hif (fun _ ↦ hbr hps4
        hcont4 (hsex.2.2.2.1 h4)) fun h5 ↦ hif (fun _ ↦ hbr hps5 hcont5 (hsex.2.2.2.2.1 h5)) fun h6
        ↦ hbr hps6 hcont6 (hsex.2.2.2.2.2 h6)
    · rw [liftPureProp_apply, ite_eq_right hsex]; exact zero_le
  change wp (.qSeq c_init (.qSeq c_while c_if)) Φ σ = 1; rw [wp_qSeq, wp_qSeq, ← wp_qSeq]
  exact wp_init_qWhile_validSexticExit hm hs1_ge1 hs1_le8 hsw1 hsr1 hrd hxs_sub hr_card res (wp c_if
    Φ) hle_if σ
private lemma s20_expect_interp_eq_cqTrace_of_wp_eq_one {Var : Type} [DecidableEq Var] {d : ℕ}
  [NeZero d] {P Q : Store Var → Prop} (c : QProg Var d) (Δ : CQState (Store Var) d) (hΔ : 𝔼[Δ,
    liftPureProp
  P] = CQState.trace Δ) (hwp : ∀ τ, P τ → wp c (liftPureProp Q) τ = 1) : 𝔼[(interp c).toStateFun Δ,
  liftPureProp Q] = CQState.trace ((interp c).toStateFun Δ) := by
  set Δ' := (interp c).toStateFun Δ
  have hle : liftPureProp P ≤ wp c (liftPureProp Q) := fun τ ↦ by
    by_cases hP : P τ
    · rw [liftPureProp_apply, ite_eq_left hP, hwp τ hP]
    · rw [liftPureProp_apply, ite_eq_right hP]; exact zero_le
  have h1 := (hΔ.symm.trans_le (expect_mono le_rfl hle)).trans_eq (wp_expectation_eq c Δ _)
  have h2 := (expect_mono le_rfl (le_top : liftPureProp Q ≤ ⊤)).trans_eq (expect_top Δ')
  linarith [NNReal.coe_le_coe.mpr ((interp c).trace_toStateFun_le Δ)]
private lemma s20_stateMass_mul_coe_eq_ofReal {Var : Type} {d : ℕ} (s : CQState (Store Var) d) (W :
    ℝ≥0) :
    stateMass s * (W : ℝ≥0∞) = ENNReal.ofReal ((s.trace : ℝ) * (W : ℝ)) := by
  rw [stateMass_eq_ofReal_trace, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul s.trace.coe_nonneg]
private lemma s20_stageRetryGuard_not_of_le {Var : Type} {n m k s_lo s_hi : ℕ} (hle : s_lo ≤ s_hi)
  (res : Var) (τ : Store Var) (hg : ¬ stageRetryGuard n m k s_hi res τ) : ¬ stageRetryGuard n m k
  s_lo res τ := by
  have hm : stageMissZ n m k s_hi (τ res) = false := by simpa [stageRetryGuard] using hg
  unfold stageRetryGuard; unfold stageMissZ at hm ⊢; split_ifs at hm ⊢ with h0 hlt
  simp only [stageMissOutcome, decide_eq_false_iff_not, Bool.not_eq_true] at hm ⊢; omega
private noncomputable def sexticSurplusApproxAssertion {Var : Type} (n m k s1 s : ℕ) (res : Var) (p1
    q : ℝ) (iter : ℕ) : CQAssertion (Store Var) (2 ^ findAllQubits n m k) :=
    fun σ ↦ if stageRetryGuard n m k s1 res σ then constAssertion (q * (1 - (1 - p1) ^
    iter)) σ else liftPureProp (fun τ ↦ ¬ stageRetryGuard n m k s res τ) σ
private lemma s20_conditional_surplus_expect_ge {Var : Type} [DecidableEq Var] {n m k p s1 s r : ℕ}
  (hm : 1 ≤ m) (hrd : r ≤ 2 ^ n) (hs1_ge1 : 1 ≤ s1) (hs1_s : s1 ≤ s) (hs_le8 : s ≤ 8) (hsw : s ≤
  activeSlots m k) (hsr : s ≤ r) {S : Finset (Fin (2 ^ n))} {xs : Fin p → Fin (2 ^ n)} (hxs_sub :
  Finset.univ.image xs ⊆ S) (hr_card : (S \ Finset.univ.image xs).card = r) (res : Var) (Δ : CQState
  (Store Var) (2 ^ findAllQubits n m k)) :
    let Q := findAllQubits n m k; let T := Finset.univ.image xs
    let c_init := (setResCircuit n m Q res 0).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)
    let body := (sexticAttemptBody n m k r T res).compile QProg.qAssign (groverParallelMarkingOracle
      (activeSlots m k) S)
    let c_pre := QProg.qSeq c_init (QProg.qWhile (stageRetryGuard n m k s1 res) body)
    let out := (interp c_pre).toStateFun Δ; let q_s := sexticCondProbNNReal n m k s1 s r
    q_s ≤ 1 ∧ CQState.trace Δ * (q_s : ℝ) ≤ 𝔼[out, liftPureProp (fun τ ↦ ¬ stageRetryGuard n m k s
      res τ)] := by
  intro Q T c_init body c_pre out q_s; let w := activeSlots m k
  let K := stageIterations (sexticPhiReal w r) n r; let p_single := multiP_succ K r (2 ^ n)
  let p1 := octicOccupancyTail s1 w r p_single; let ps := octicOccupancyTail s w r p_single
  let q : ℝ := min 1 (ps / p1); have hs_ge1 : 1 ≤ s := hs1_ge1.trans hs1_s
  have hs1_le8 : s1 ≤ 8 := hs1_s.trans hs_le8; have hsw1 : s1 ≤ w := hs1_s.trans hsw
  have hsr1 : s1 ≤ r := hs1_s.trans hsr
  rcases octicOccupancyTail_stage_bounds (m := m) (k := k) hs1_ge1 hs1_le8 hsw1 hsr1 hrd with
    ⟨hp1_pos, hp1_le1⟩
  rcases octicOccupancyTail_stage_bounds (m := m) (k := k) hs_ge1 hs_le8 hsw hsr hrd with ⟨hps_pos,
    _hps_le1⟩; have hq0 : 0 ≤ q := le_min zero_le_one (div_nonneg hps_pos.le hp1_pos.le)
  have hq1 : q ≤ 1 := min_le_left 1 (ps / p1)
  have hqp1_le_ps : q * p1 ≤ ps := by
    have hle : q ≤ ps / p1 := min_le_right 1 (ps / p1)
    have hmul := mul_le_mul_of_nonneg_right hle hp1_pos.le
    rwa [div_mul_cancel₀ ps hp1_pos.ne'] at hmul
  have hq_s_le1 : q_s ≤ 1 := Real.toNNReal_le_one.mpr hq1; have hq_s_coe : (q_s : ℝ) = q :=
    Real.coe_toNNReal q hq0
  have h1p1_nonneg : 0 ≤ 1 - p1 := (by linarith); have h1p1_lt1 : 1 - p1 < 1 := (by linarith)
  let guard1 : Store Var → Prop := stageRetryGuard n m k s1 res
  let guard_s : Store Var → Prop := stageRetryGuard n m k s res
  let Ψ_s : CQAssertion (Store Var) (2 ^ Q) := liftPureProp (fun τ ↦ ¬ guard_s τ)
  have hbounds : ∀ i : ℕ, 0 ≤ q * (1 - (1 - p1) ^ i) ∧ q * (1 - (1 - p1) ^ i) ≤ 1 := fun i ↦ by
    have hp0 := pow_nonneg h1p1_nonneg i; have hp1 := pow_le_one₀ h1p1_nonneg h1p1_lt1.le (n := i)
    exact ⟨mul_nonneg hq0 (by linarith), (mul_le_mul hq1 (by linarith) (by linarith)
      zero_le_one).trans_eq (mul_one 1)⟩
  have happrox_le : ∀ iter : ℕ, sexticSurplusApproxAssertion n m k s1 s res p1 q iter ≤ whileRecWP
    (wp body) guard1 (iter + 1) Ψ_s := by
    intro iter; induction iter with
    | zero =>
        intro σ; by_cases hg1 : guard1 σ
        · simp only [sexticSurplusApproxAssertion, guard1, hg1, ↓reduceIte, pow_zero, sub_self,
            mul_zero]; change (constAssertion 0 σ).1 ≤ _; rw [constAssertion_apply_of_bounds 0
            le_rfl zero_le_one, zero_smul]; exact (whileRecWP (wp body) guard1 1 Ψ_s σ).2.1
        · simp [sexticSurplusApproxAssertion, guard1, guard_s, Ψ_s, hg1, whileRecWP]
    | succ iter ih =>
        intro σ; by_cases hg1 : guard1 σ
        · simp only [sexticSurplusApproxAssertion, guard1, hg1, ↓reduceIte, whileRecWP]
          refine le_trans ?_ (wp_mono body ih σ)
          rcases hbounds iter with ⟨hc0, hc1⟩; rcases hbounds (iter + 1) with ⟨hc0', hc1'⟩
          set c : ℝ := q * (1 - (1 - p1) ^ iter)
          let SA := sexticSurplusApproxAssertion n m k s1 s res p1 q iter
          have hwp_eq := wp_sexticAttemptBody_conditionalStratum_step hm hs1_ge1 hs1_s hs_le8 hsw
            hsr hxs_sub hr_card res SA σ c ?_
          · change (constAssertion (q * (1 - (1 - p1) ^ (iter + 1))) σ).1 ≤ _
            rw [constAssertion_apply_of_bounds _ hc0' hc1', hwp_eq]; have hring : q * (1 - (1 - p1)
              ^ (iter + 1)) = q * p1 + (1 - p1) * c := (by dsimp [c]; rw [pow_succ']; ring)
            exact smul_le_smul_of_nonneg_right (by linarith [hqp1_le_ps]) zero_le_one
          · intro o hsub; let σ' := Store.subst σ res (o.val : ℤ)
            have hg_iff : ∀ {t}, stageRetryGuard n m k t res σ' ↔ stageMissOutcome n m k t o = true
              := (by simp [σ', stageRetryGuard, stageMissZ_of_fin_m20])
            by_cases hm1 : stageMissOutcome n m k s1 o = true
            · rw [ite_eq_left hm1]; change (sexticSurplusApproxAssertion n m k s1 s res p1 q iter
                σ').1.mat o o = (c : ℂ); rw [sexticSurplusApproxAssertion, ite_eq_left (hg_iff.mpr
                hm1), constAssertion_apply_of_bounds c hc0 hc1]; simp [Complex.real_smul]
            · rw [ite_eq_right hm1]; by_cases hms : stageMissOutcome n m k s o = true
              · rw [ite_eq_left hms]; change (sexticSurplusApproxAssertion n m k s1 s res p1 q iter
                  σ').1.mat o o = 0; rw [sexticSurplusApproxAssertion, ite_eq_right (mt hg_iff.mp
                  hm1), liftPureProp_apply, ite_eq_right (not_not.mpr (hg_iff.mpr hms))]; simp
              · rw [ite_eq_right hms]; change (sexticSurplusApproxAssertion n m k s1 s res p1 q iter
                  σ').1.mat o o = 1; rw [sexticSurplusApproxAssertion, ite_eq_right (mt hg_iff.mp
                  hm1), liftPureProp_apply, ite_eq_left (mt hg_iff.mp hms)]; simp
        · simp [sexticSurplusApproxAssertion, guard1, guard_s, Ψ_s, hg1, whileRecWP]
  let Θ_init : CQAssertion (Store Var) (2 ^ Q) := fun τ ↦ if guard1 τ then constAssertion q τ else ⊥
  have hΘ_le : Θ_init ≤ wp (.qWhile guard1 body) Ψ_s := by
    intro τ; by_cases hg1 : guard1 τ
    · simp only [Θ_init, hg1, ↓reduceIte]; change (constAssertion q τ).1 ≤ _
      rw [constAssertion_apply_of_bounds q hq0 hq1]; refine hermitian_le_of_geometric_sub_smul_le (1
        - p1) h1p1_nonneg h1p1_lt1 (q • 1) (q • 1) _ fun iter ↦ ?_; rcases hbounds iter with ⟨hc0,
        hc1⟩
      have hsub : (q • (1 : HermitianMat (Fin (2 ^ Q)) ℂ)) - (1 - p1) ^ iter • (q • 1) =
        (sexticSurplusApproxAssertion n m k s1 s res p1 q iter τ).1 := by
        simp only [sexticSurplusApproxAssertion, guard1, hg1, ↓reduceIte,
          constAssertion_apply_of_bounds _ hc0 hc1, smul_smul, ← sub_smul]; congr 1; ring
      rw [hsub]; exact (happrox_le iter τ).trans (whileRecWP_le_wp_qWhile guard1 body (iter + 1) Ψ_s
        τ)
    · simp [Θ_init, hg1]
  have hwp_init : wp c_init Θ_init = constAssertion q := by
    funext σ; refine Subtype.ext (Subtype.ext ?_); dsimp only [c_init]; rw [wp_setResCircuit]
    have hg0 : guard1 (Store.subst σ res ((0 : Fin (2 ^ Q)).val : ℤ)) :=
      stageRetryGuard_subst_zero_m20 n m k s1 hs1_ge1 res σ; rw [show Θ_init _ = constAssertion q _
      from ite_eq_left hg0, constAssertion_apply_of_bounds q hq0 hq1, constAssertion_apply_of_bounds
      q hq0 hq1]; ext i j; simp [HermitianMat.val_eq_coe, Complex.real_smul]
  have hq_le_pre : constAssertion q ≤ wp c_pre Ψ_s := hwp_init ▸ wp_mono c_init hΘ_le; have h1 :=
    (expect_mono le_rfl hq_le_pre).trans_eq (wp_expectation_eq c_pre Δ Ψ_s); have h2 :=
    expect_constAssertion q Δ ⟨hq0, hq1⟩; exact ⟨hq_s_le1, by rw [hq_s_coe]; linarith⟩
theorem expectedCost_sexticStratumBranchCircuit_le {Var : Type} [DecidableEq Var] {n m k p s1 s2 s3
  s4 s5 s6 r : ℕ} (hm : 1 ≤ m) (hrd : r ≤ 2 ^ n) (hs1_ge1 : 1 ≤ s1) (hs1_s2 : s1 ≤ s2) (hs2_s3 : s2
  ≤ s3) (hs3_s4 : s3 ≤ s4) (hs4_s5 : s4 ≤ s5) (hs5_s6 : s5 ≤ s6) (hs6_le8 : s6 ≤ 8) (hsw6 : s6 ≤
  activeSlots m k) (hsr6 : s6 ≤ r) (hs1_eq : s1 = sexticStratum1 (activeSlots m k) r) (hs2_eq : s2 =
  sexticStratum2 (activeSlots m k) r) (hs3_eq : s3 = sexticStratum3 (activeSlots m k) r) (hs4_eq :
  s4 = sexticStratum4 (activeSlots m k) r) (hs5_eq : s5 = sexticStratum5 (activeSlots m k) r)
  (hs6_eq : s6 = sexticStratum6 (activeSlots m k) r) (hps1 : p + s1 ≤ k) (hps2 : p + s2 ≤ k) (hps3 :
  p + s3 ≤ k) (hps4 : p + s4 ≤ k) (hps5 : p + s5 ≤ k) (hps6 : p + s6 ≤ k) {S : Finset (Fin (2 ^ n))}
  {xs : Fin p → Fin (2 ^ n)} (hxs_inj : Function.Injective xs) (hxs_sub : Finset.univ.image xs ⊆ S)
  (hr_card : (S \ Finset.univ.image xs).card = r) (res : Var) (cont1 cont2 cont3 cont4 cont5 cont6 :
  OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) *
  activeSlots m k)) (V1 V2 V3 V4 V5 V6 : ℝ≥0) (hcost1 : ∀ Δ1 : CQState (Store Var) (2 ^
    findAllQubits n m
  k), 𝔼[Δ1, liftPureProp (ValidStageStore n S (p + s1) res)] = CQState.trace Δ1 → expectedCost
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S)) (cont1.compile
  QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ1 ≤
  stateMass Δ1 * (V1 : ℝ≥0∞))
  (hcost2 : ∀ Δ2 : CQState (Store Var) (2 ^ findAllQubits n m k), 𝔼[Δ2, liftPureProp
    (ValidStageStore n S (p
  + s2) res)] = CQState.trace Δ2 → expectedCost (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle (activeSlots m k) S)) (cont2.compile QProg.qAssign
  (groverParallelMarkingOracle (activeSlots m k) S)) Δ2 ≤ stateMass Δ2 * (V2 : ℝ≥0∞))
  (hcost3 : ∀ Δ3 : CQState (Store Var) (2 ^ findAllQubits n m k),
  𝔼[Δ3, liftPureProp (ValidStageStore n S (p + s3) res)] =
  CQState.trace Δ3 → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle
  (activeSlots m k) S)) (cont3.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k)
  S)) Δ3 ≤ stateMass Δ3 * (V3 : ℝ≥0∞)) (hcost4 : ∀ Δ4 : CQState (Store Var) (2 ^ findAllQubits n m
    k),
  𝔼[Δ4, liftPureProp (ValidStageStore n S (p + s4) res)] = CQState.trace Δ4 → expectedCost
  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S)) (cont4.compile
  QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ4 ≤
  stateMass Δ4 * (V4 : ℝ≥0∞))
  (hcost5 : ∀ Δ5 : CQState (Store Var) (2 ^ findAllQubits n m k), 𝔼[Δ5, liftPureProp
    (ValidStageStore n S (p
  + s5) res)] = CQState.trace Δ5 → expectedCost (CostModel.ofEmbeddedOracle
  (groverParallelMarkingOracle (activeSlots m k) S)) (cont5.compile QProg.qAssign
  (groverParallelMarkingOracle (activeSlots m k) S)) Δ5 ≤ stateMass Δ5 * (V5 : ℝ≥0∞))
  (hcost6 : ∀ Δ6 : CQState (Store Var) (2 ^ findAllQubits n m k),
  𝔼[Δ6, liftPureProp (ValidStageStore n S (p + s6) res)] =
  CQState.trace Δ6 → expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle
  (activeSlots m k) S)) (cont6.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k)
  S)) Δ6 ≤ stateMass Δ6 * (V6 : ℝ≥0∞)) (Δ : CQState (Store Var) (2 ^ findAllQubits n m k)) :
    let q2 := sexticProb2NNReal n m k r; let q3 := sexticProb3NNReal n m k r
    let q4 := sexticProb4NNReal n m k r; let q5 := sexticProb5NNReal n m k r
    let q6 := sexticProb6NNReal n m k r; let W6 := V6; let W5 := max V5 W6; let W4 := max V4 W5
    let W3 := max V3 W4; let W2 := max V2 W3; let W1 := max V1 W2
    expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
      ((sexticStratumBranchCircuit n m k hps1 hps2 hps3 hps4 hps5 hps6 r xs res cont1 cont2 cont3
      cont4 cont5 cont6).compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ
      ≤ stateMass Δ * ((sexticLoopCostNNReal n m k r + ((1 - q2) * W1 + (q2 - q3) * W2 +
      (q3 - q4) * W3 + (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6) : ℝ≥0) : ℝ≥0∞) := by
  intro q2 q3 q4 q5 q6 W6 W5 W4 W3 W2 W1; let Q : ℕ := findAllQubits n m k
  let T : Finset (Fin (2 ^ n)) := Finset.univ.image xs; let R : Finset (Fin (2 ^ n)) := S \ T
  let G := groverParallelMarkingOracle (activeSlots m k) S
  let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle G
  let comp := fun c : OracleDynamicCircuit _ Var Q ((n + 1) * activeSlots m k) ↦
    c.compile QProg.qAssign G
  let guard1 := stageRetryGuard n m k s1 res; let guard2 := stageRetryGuard n m k s2 res
  let guard3 := stageRetryGuard n m k s3 res; let guard4 := stageRetryGuard n m k s4 res
  let guard5 := stageRetryGuard n m k s5 res; let guard6 := stageRetryGuard n m k s6 res
  let c_init := comp (setResCircuit n m Q res 0); let body := comp (sexticAttemptBody n m k r T res)
  let c_while : QProg Var (2 ^ Q) := .qWhile guard1 body; let c_pre := QProg.qSeq c_init c_while
  let br := fun {s : ℕ} (hps : p + s ≤ k) ct ↦
    QProg.qSeq (comp (commitHitTuple n m k hps xs res)) (comp ct)
  let c_if56 := QProg.qIf guard6 (br hps5 cont5) (br hps6 cont6); let c_if456 := QProg.qIf guard5
    (br hps4 cont4) c_if56; let c_if3456 := QProg.qIf guard4 (br hps3 cont3) c_if456
  let c_if23456 := QProg.qIf guard3 (br hps2 cont2) c_if3456; let c_if := QProg.qIf guard2
    (br hps1 cont1) c_if23456
  -- Step 1: Loop cost bound for c_pre =.qSeq c_init c_while
  let K_it := stageIterations (sexticPhiReal (activeSlots m k) r) n r
  let p1_raw := octicOccupancyTail s1 (activeSlots m k) r (multiP_succ K_it r (2 ^ n))
  rcases octicOccupancyTail_stage_bounds (m := m) (k := k) hs1_ge1 (by omega) (by omega) (by omega)
    hrd with ⟨hp1_pos, hp1_le1⟩
  have hwp_exit1 : wp body (liftPureProp (fun σ ↦ ¬ guard1 σ)) = constAssertion ((Real.toNNReal
    p1_raw : ℝ≥0) : ℝ) := by
    rw [Real.coe_toNNReal _ hp1_pos.le]
    exact wp_sexticAttemptBody_occupancyStratum_eq hm hs1_ge1 (by omega) (by omega) (by omega) hrd
      hxs_sub hr_card res
  rcases lossless_and_costBound_sexticAttemptBody (k := k) (r := r) hm S T res with ⟨hb_loss, hbc⟩
  have hw_cost := CostBound.qWhile_of_wp_eq hbc (Real.toNNReal_pos.mpr hp1_pos)
    (Real.toNNReal_le_one.mpr hp1_le1) hb_loss hwp_exit1
  rw [show (Real.toNNReal p1_raw)⁻¹ * ((K_it + 1 : ℕ) : ℝ≥0) = sexticLoopCostNNReal n m k r
    by dsimp [sexticLoopCostNNReal, p1_raw, K_it]; rw [← hs1_eq]] at hw_cost
  have hc_pre : CostBound model c_pre (sexticLoopCostNNReal n m k r) := by
    rw [← zero_add (sexticLoopCostNNReal n m k r)]
    exact CostBound.seq (lossless_And_costBound_qsetSim_setRes (m := m) (w := activeSlots m k) S res
      (0 : Fin (2 ^ Q))).2.2.2 hw_cost
  -- Step 2: Output state `out` of `c_pre` satisfies ValidSexticExit and preserves trace
  let out := (interp c_pre).toStateFun Δ; let out_b1 := out.cqTrueSt guard2
  let out_ge2 := out.cqFalseSt guard2; let out_b2 := out_ge2.cqTrueSt guard3
  let out_ge3 := out_ge2.cqFalseSt guard3; let out_b3 := out_ge3.cqTrueSt guard4
  let out_ge4 := out_ge3.cqFalseSt guard4; let out_b4 := out_ge4.cqTrueSt guard5
  let out_ge5 := out_ge4.cqFalseSt guard5; let out_b5 := out_ge5.cqTrueSt guard6
  let out_b6 := out_ge5.cqFalseSt guard6; let Ψ_sex : CQAssertion (Store Var) (2 ^ Q) :=
    liftPureProp (ValidSexticExit n m k s1 s2 s3 s4 s5 s6 R res)
  have hpre_wp : wp c_pre Ψ_sex = ⊤ := funext fun σ ↦ wp_init_qWhile_validSexticExit hm hs1_ge1
    (by omega) (by omega) (by omega) hrd hxs_sub hr_card res _ le_rfl σ; have hout_exp_Δ : 𝔼[out,
    Ψ_sex] = Δ.trace := (by rw [← wp_expectation_eq, hpre_wp, expect_top])
  have hout_exp : 𝔼[out, Ψ_sex] = CQState.trace out := by
    linarith [(expect_mono le_rfl (le_top : Ψ_sex ≤ ⊤)).trans_eq (expect_top out),
      NNReal.coe_le_coe.mpr ((interp c_pre).trace_toStateFun_le Δ)]
  have htr_part2 : (CQState.trace out_b1 : ℝ) + CQState.trace out_ge2 = CQState.trace Δ := by
    have h : (CQState.trace out_b1 : ℝ) + CQState.trace out_ge2 = CQState.trace out := by
      exact_mod_cast out.trace_cqTrueSt_add_trace_cqFalseSt guard2
    linarith
  have htr_part3 : (out_b2.trace : ℝ) + out_ge3.trace = out_ge2.trace := by
    exact_mod_cast out_ge2.trace_cqTrueSt_add_trace_cqFalseSt guard3
  have htr_part4 : (out_b3.trace : ℝ) + out_ge4.trace = out_ge3.trace := by
    exact_mod_cast out_ge3.trace_cqTrueSt_add_trace_cqFalseSt guard4
  have htr_part5 : (out_b4.trace : ℝ) + out_ge5.trace = out_ge4.trace := by
    exact_mod_cast out_ge4.trace_cqTrueSt_add_trace_cqFalseSt guard5
  have htr_part6 : (out_b5.trace : ℝ) + out_b6.trace = out_ge5.trace := by
    exact_mod_cast out_ge5.trace_cqTrueSt_add_trace_cqFalseSt guard6
  -- Step 3: Branch cost bounds on `out_b1`.. `out_b6`
  rcases expect_true_false_eq_cqTrace_m10 guard2 out Ψ_sex hout_exp with ⟨hout_b1_exp, hout_ge2_exp⟩
  have hout_ge3_exp := (expect_true_false_eq_cqTrace_m10 guard3 out_ge2 Ψ_sex hout_ge2_exp).2
  have hout_ge4_exp := (expect_true_false_eq_cqTrace_m10 guard4 out_ge3 Ψ_sex hout_ge3_exp).2
  have hout_ge5_exp := (expect_true_false_eq_cqTrace_m10 guard5 out_ge4 Ψ_sex hout_ge4_exp).2
  have hfalse_hit : ∀ {s : ℕ} (g : Store Var → Prop) [DecidablePred g] (st : CQState (Store Var) (2
    ^ Q)),
    𝔼[st, Ψ_sex] = CQState.trace st → (∀ τ, ValidSexticExit n m k s1 s2 s3 s4 s5 s6 R res τ → ¬ g τ
    → ValidHitExit_m20 n m k s R res τ) → 𝔼[st.cqFalseSt g, liftPureProp (ValidHitExit_m20 n m k s R
    res)] = CQState.trace (st.cqFalseSt g) := by
    intro s g _ st hst hproj; set Φh : CQAssertion (Store Var) (2 ^ Q) := liftPureProp
      (ValidHitExit_m20 n m
      k s R res)
    have hle : Ψ_sex ≤ fun τ ↦ if g τ then (⊤ : CQAssertion (Store Var) (2 ^ Q)) τ else Φh τ := fun
      τ ↦ by
      by_cases hg : g τ; · simp only [hg, ↓reduceIte]; exact le_top
      simp only [hg, ↓reduceIte]; by_cases hs : ValidSexticExit n m k s1 s2 s3 s4 s5 s6 R res τ
      · dsimp only [Ψ_sex, Φh]; rw [liftPureProp_apply, ite_eq_left hs, liftPureProp_apply,
          ite_eq_left (hproj τ hs hg)]
      · dsimp only [Ψ_sex]; rw [liftPureProp_apply, ite_eq_right hs]; exact zero_le
    have hp := cqExpect_ite_split g st ⊤ Φh; rw [expect_top] at hp
    have htr_g : (CQState.trace (st.cqTrueSt g) : ℝ) + CQState.trace (st.cqFalseSt g) =
      CQState.trace st := by exact_mod_cast st.trace_cqTrueSt_add_trace_cqFalseSt g
    linarith [hst.symm.trans_le ((expect_mono le_rfl hle).trans_eq hp),
      (expect_mono le_rfl (le_top : Φh ≤ ⊤)).trans_eq (expect_top (st.cqFalseSt g)), htr_g]
  have hbr_cost : ∀ {P : Store Var → Prop} {s : ℕ} (hps : p + s ≤ k) {ct} {V W : ℝ≥0} (hVW : V ≤ W)
    (st : CQState (Store Var) (2 ^ Q)), 𝔼[st, liftPureProp P] = CQState.trace st → (∀ τ, P τ →
    ValidHitExit_m20 n m k s R res τ) → (∀ Δs, 𝔼[Δs, liftPureProp (ValidStageStore n S (p + s) res)]
    = CQState.trace Δs → expectedCost model (comp ct) Δs ≤ stateMass Δs * (V : ℝ≥0∞)) → expectedCost
    model (br hps ct) st ≤ stateMass st * (W : ℝ≥0∞) := by
    intro P s hps ct V W hVW st hst hP hct; let c_cm := comp (commitHitTuple n m k hps xs res)
    have hΔs := s20_expect_interp_eq_cqTrace_of_wp_eq_one c_cm st hst (fun τ hp ↦ wp_commitHitTuple
      (m := m) hps hxs_inj hxs_sub res τ (hP τ hp)); have hc0 : expectedCost model c_cm st = 0 :=
      (by simpa using costBound_zero_commitHitTuple (m := m) hps S xs res st)
    dsimp only [br]; rw [expectedCost_qSeq, hc0, zero_add]
    exact (hct _ hΔs).trans ((mul_le_mul_of_nonneg_right (stateMass_interp_le c_cm st)
      zero_le).trans (mul_le_mul_of_nonneg_left (ENNReal.coe_le_coe.mpr hVW) zero_le))
  have hout_ge2_hit := hfalse_hit guard2 out hout_exp (fun _ h ↦ h.2.1); have hout_ge3_hit :=
    hfalse_hit guard3 out_ge2 hout_ge2_exp (fun _ h ↦ h.2.2.1)
  have hout_ge4_hit := hfalse_hit guard4 out_ge3 hout_ge3_exp (fun _ h ↦ h.2.2.2.1)
  have hout_ge5_hit := hfalse_hit guard5 out_ge4 hout_ge4_exp (fun _ h ↦ h.2.2.2.2.1)
  have hout_b6_hit := hfalse_hit guard6 out_ge5 hout_ge5_exp (fun _ h ↦ h.2.2.2.2.2)
  have hcost_b1 := hbr_cost hps1 (le_max_left V1 W2) out_b1 hout_b1_exp (fun _ h ↦ h.1) hcost1
  have hcost_b2 := hbr_cost hps2 (le_max_left V2 W3) out_b2 (expect_true_false_eq_cqTrace_m10 guard3
    out_ge2 _ hout_ge2_hit).1 (fun _ h ↦ h) hcost2
  have hcost_b3 := hbr_cost hps3 (le_max_left V3 W4) out_b3 (expect_true_false_eq_cqTrace_m10 guard4
    out_ge3 _ hout_ge3_hit).1 (fun _ h ↦ h) hcost3
  have hcost_b4 := hbr_cost hps4 (le_max_left V4 W5) out_b4 (expect_true_false_eq_cqTrace_m10 guard5
    out_ge4 _ hout_ge4_hit).1 (fun _ h ↦ h) hcost4
  have hcost_b5 := hbr_cost hps5 (le_max_left V5 W6) out_b5 (expect_true_false_eq_cqTrace_m10 guard6
    out_ge5 _ hout_ge5_hit).1 (fun _ h ↦ h) hcost5
  have hcost_b6 := hbr_cost hps6 le_rfl out_b6 hout_b6_hit (fun _ h ↦ h) hcost6
  -- Step 4: Conditioned Loewner-limit surplus-mass lower bounds on `out_ge2`.. `out_b6`
  let hcs := fun (s : ℕ) (h1 : s1 ≤ s) (h8 : s ≤ 8) (hw : s ≤ activeSlots m k) (hr : s ≤ r) ↦
    s20_conditional_surplus_expect_ge hm hrd hs1_ge1 h1 h8 hw hr hxs_sub hr_card res Δ
  rcases hcs s2 hs1_s2 (by omega) (by omega) (by omega) with ⟨hq2_raw_le1, hsurp2_exp⟩
  rcases hcs s3 (by omega) (by omega) (by omega) (by omega) with ⟨hq3_raw_le1, hsurp3_exp⟩
  rcases hcs s4 (by omega) (by omega) (by omega) (by omega) with ⟨hq4_raw_le1, hsurp4_exp⟩
  rcases hcs s5 (by omega) (by omega) (by omega) (by omega) with ⟨hq5_raw_le1, hsurp5_exp⟩
  rcases hcs s6 (by omega) hs6_le8 hsw6 hsr6 with ⟨hq6_raw_le1, hsurp6_exp⟩
  have hΨ_false : ∀ (cond : Store Var → Prop) [DecidablePred cond] (st : CQState (Store Var) (2 ^
    Q)), 𝔼[st,
    liftPureProp (fun τ ↦ ¬ cond τ)] = CQState.trace (st.cqFalseSt cond) := by
    intro cond _ st; rw [show liftPureProp (fun τ ↦ ¬ cond τ) = fun τ ↦
        if cond τ then (⊥ : CQAssertion (Store Var) (2 ^ Q)) τ else (⊤ : CQAssertion (Store Var) (2
          ^ Q)) τ by
      funext τ; by_cases h : cond τ <;> simp [h],
      cqExpect_ite_split, expect_bot, zero_add, expect_top]
  have hΨ_drop : ∀ {s_lo s_hi : ℕ} (hle : s_lo ≤ s_hi) {st : CQState (Store Var) (2 ^ Q)}, 𝔼[st,
    liftPureProp (fun τ ↦ ¬ stageRetryGuard n m k s_hi res τ)] = 𝔼[st.cqFalseSt (stageRetryGuard n m
    k s_lo res), liftPureProp (fun τ ↦ ¬ stageRetryGuard n m k s_hi res τ)] := by
    intro s_lo s_hi hle st
    let Ψ : CQAssertion (Store Var) (2 ^ Q) := liftPureProp (fun τ ↦ ¬ stageRetryGuard n m k s_hi
      res τ)
    have hpart : Ψ = fun τ ↦ if stageRetryGuard n m k s_lo res τ then (⊥ : CQAssertion (Store Var)
      (2 ^ Q))
      τ else Ψ τ := funext fun τ ↦ by
      by_cases hg_lo : stageRetryGuard n m k s_lo res τ
      · have hg_hi : stageRetryGuard n m k s_hi res τ :=
          (by by_contra h0; exact s20_stageRetryGuard_not_of_le hle res τ h0 hg_lo); simp [Ψ, hg_lo,
          hg_hi]
      · simp [hg_lo]
    change 𝔼[st, Ψ] = _; (conv_lhs => rw [hpart]); rw [cqExpect_ite_split, expect_bot, zero_add]
  have hexp2_eq := hΨ_false guard2 out; have hexp3_eq : 𝔼[out, liftPureProp (fun τ ↦ ¬ guard3 τ)] =
    out_ge3.trace := by rw [hΨ_drop (by omega), hΨ_false]
  have hexp4_eq : 𝔼[out, liftPureProp (fun τ ↦ ¬ guard4 τ)] = CQState.trace out_ge4 :=
    (by rw [hΨ_drop (s_lo := s2) (by omega), hΨ_drop (s_lo := s3) (by omega), hΨ_false])
  have hexp5_eq : 𝔼[out, liftPureProp (fun τ ↦ ¬ guard5 τ)] = CQState.trace out_ge5 := by
    rw [hΨ_drop (s_lo := s2) (by omega), hΨ_drop (s_lo := s3) (by omega), hΨ_drop (s_lo := s4)
      (by omega), hΨ_false]
  have hexp6_eq : 𝔼[out, liftPureProp (fun τ ↦ ¬ guard6 τ)] = CQState.trace out_b6 := by
    rw [hΨ_drop (s_lo := s2) (by omega), hΨ_drop (s_lo := s3) (by omega), hΨ_drop (s_lo := s4)
      (by omega), hΨ_drop (s_lo := s5) (by omega), hΨ_false]
  let c := fun s ↦ sexticCondProbNNReal n m k s1 s r
  have hq6 : q6 = c s6 := by dsimp [q6, c, sexticProb6NNReal]; rw [← hs1_eq, ← hs6_eq]
  have hq5 : q5 = max (c s5) q6 := by dsimp [q5, q6, c, sexticProb5NNReal]; rw [← hs1_eq, ← hs5_eq]
  have hq4 : q4 = max (c s4) q5 := by dsimp [q4, q5, c, sexticProb4NNReal]; rw [← hs1_eq, ← hs4_eq]
  have hq3 : q3 = max (c s3) q4 := by dsimp [q3, q4, c, sexticProb3NNReal]; rw [← hs1_eq, ← hs3_eq]
  have hq2 : q2 = max (c s2) q3 := by dsimp [q2, q3, c, sexticProb2NNReal]; rw [← hs1_eq, ← hs2_eq]
  have hq6_le_q5 := hq5 ▸ le_max_right _ _; have hq5_le_q4 := hq4 ▸ le_max_right _ _
  have hq4_le_q3 := hq3 ▸ le_max_right _ _; have hq3_le_q2 := hq2 ▸ le_max_right _ _
  have hq5_le1 : q5 ≤ 1 := by rw [hq5, hq6]; exact max_le hq5_raw_le1 hq6_raw_le1
  have hq4_le1 : q4 ≤ 1 := (by rw [hq4]; exact max_le hq4_raw_le1 hq5_le1); have hq3_le1 : q3 ≤ 1 :=
    (by rw [hq3]; exact max_le hq3_raw_le1 hq4_le1); have hq2_le1 : q2 ≤ 1 :=
    (by rw [hq2]; exact max_le hq2_raw_le1 hq3_le1)
  have hmax_surp : ∀ {s : ℕ} {q_lo q_hi : ℝ≥0} {st_lo st_hi b : CQState (Store Var) (2 ^ Q)}, q_lo =
    max
    (sexticCondProbNNReal n m k s1 s r) q_hi → CQState.trace Δ * (sexticCondProbNNReal n m k s1 s r
    : ℝ) ≤ CQState.trace st_lo → CQState.trace Δ * (q_hi : ℝ) ≤ CQState.trace st_hi →
    (CQState.trace b : ℝ) + CQState.trace st_hi = CQState.trace st_lo → CQState.trace Δ *
    (q_lo : ℝ) ≤ CQState.trace st_lo := by
    intro _ _ _ _ _ b hq h1 h2 hp; rw [hq, NNReal.coe_max, mul_max_of_nonneg _ _ Δ.trace.coe_nonneg]
    exact max_le h1 (by linarith [h2, hp, b.trace.coe_nonneg])
  have htr_6_surp : Δ.trace * (q6 : ℝ) ≤ out_b6.trace := by rw [hq6, ← hexp6_eq]; exact hsurp6_exp
  have htr_5_surp := hmax_surp hq5 (by rw [← hexp5_eq]; exact hsurp5_exp) htr_6_surp htr_part6
  have htr_4_surp := hmax_surp hq4 (by rw [← hexp4_eq]; exact hsurp4_exp) htr_5_surp htr_part5
  have htr_3_surp := hmax_surp hq3 (by rw [← hexp3_eq]; exact hsurp3_exp) htr_4_surp htr_part4
  have htr_2_surp := hmax_surp hq2 (by rw [← hexp2_eq]; exact hsurp2_exp) htr_3_surp htr_part3
  -- Step 5: 6-term Abel summation for the 6-stratum continuation cost
  have hbranch_le : stateMass out_b1 * (W1 : ℝ≥0∞) + (stateMass out_b2 * (W2 : ℝ≥0∞) + (stateMass
    out_b3 * (W3 : ℝ≥0∞) + (stateMass out_b4 * (W4 : ℝ≥0∞) + (stateMass out_b5 * (W5 : ℝ≥0∞) +
    stateMass out_b6 * (W6 : ℝ≥0∞))))) ≤ stateMass Δ * (((1 - q2) * W1 + (q2 - q3) * W2 + (q3 - q4)
    * W3 + (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6 : ℝ≥0) : ℝ≥0∞) := by
    have h0 (s : CQState (Store Var) (2 ^ Q)) (W : ℝ≥0) := mul_nonneg s.trace.coe_nonneg
      W.coe_nonneg
    have h56 := add_nonneg (h0 out_b5 W5) (h0 out_b6 W6); have h46 := add_nonneg (h0 out_b4 W4) h56
    have h36 := add_nonneg (h0 out_b3 W3) h46; have h26 := add_nonneg (h0 out_b2 W2) h36
    simp only [s20_stateMass_mul_coe_eq_ofReal]; rw [← ENNReal.ofReal_add (h0 out_b5 W5) (h0 out_b6
      W6), ← ENNReal.ofReal_add (h0 out_b4 W4) h56, ← ENNReal.ofReal_add (h0 out_b3 W3) h46, ←
      ENNReal.ofReal_add (h0 out_b2 W2) h36, ← ENNReal.ofReal_add (h0 out_b1 W1) h26]
    refine ENNReal.ofReal_le_ofReal ?_; simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one,
      NNReal.coe_sub hq2_le1, NNReal.coe_sub hq3_le_q2, NNReal.coe_sub hq4_le_q3, NNReal.coe_sub
      hq5_le_q4, NNReal.coe_sub hq6_le_q5, eq_sub_of_add_eq htr_part2, eq_sub_of_add_eq htr_part3,
      eq_sub_of_add_eq htr_part4, eq_sub_of_add_eq htr_part5, eq_sub_of_add_eq htr_part6]
    have hw : ∀ {a b x y : ℝ}, x ≤ y → b ≤ a → 0 ≤ (y - x) * (a - b) := fun h1 h2 ↦ mul_nonneg
      (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
    have h2 := hw htr_2_surp (by exact_mod_cast le_max_right V1 W2 : (W2 : ℝ) ≤ W1)
    have h3 := hw htr_3_surp (by exact_mod_cast le_max_right V2 W3 : (W3 : ℝ) ≤ W2)
    have h4 := hw htr_4_surp (by exact_mod_cast le_max_right V3 W4 : (W4 : ℝ) ≤ W3)
    have h5 := hw htr_5_surp (by exact_mod_cast le_max_right V4 W5 : (W5 : ℝ) ≤ W4)
    have h6 := hw htr_6_surp (by exact_mod_cast le_max_right V5 W6 : (W6 : ℝ) ≤ W5)
    exact sub_nonneg.mp (le_of_le_of_eq (add_nonneg h2 (add_nonneg h3 (add_nonneg h4 (add_nonneg h5
      h6)))) (by ring))
  change expectedCost model (.qSeq c_init (.qSeq c_while c_if)) Δ ≤ _
  have hc_a : expectedCost model (.qSeq c_init (.qSeq c_while c_if)) Δ = expectedCost model c_pre Δ
    + expectedCost model c_if out :=
    (by dsimp only [c_pre, out]; simp only [expectedCost_qSeq, add_assoc]; rfl)
  have hc_if : expectedCost model c_if out = expectedCost model (br hps1 cont1) out_b1 +
    (expectedCost model (br hps2 cont2) out_b2 + (expectedCost model (br hps3 cont3) out_b3 +
    (expectedCost model (br hps4 cont4) out_b4 + (expectedCost model (br hps5 cont5) out_b5 +
    expectedCost model (br hps6 cont6) out_b6)))) := by
    dsimp only [c_if, c_if23456, c_if3456, c_if456, c_if56, out_b1, out_ge2, out_b2, out_ge3,
      out_b3, out_ge4, out_b4, out_ge5, out_b5, out_b6]; rw [cqExpectedCostIf, cqExpectedCostIf,
      cqExpectedCostIf, cqExpectedCostIf, cqExpectedCostIf]
  rw [hc_a, hc_if]; refine (add_le_add (hc_pre Δ) (add_le_add hcost_b1 (add_le_add hcost_b2
    (add_le_add hcost_b3 (add_le_add hcost_b4 (add_le_add hcost_b5 hcost_b6)))))).trans ((add_le_add
    le_rfl hbranch_le).trans_eq ?_); rw [← mul_add, ← ENNReal.coe_add]
end QuantumComputation.Specs
end
end Sec_SexticStratumStageWP
section Sec_SexticCascadeCorrectness
section Sec_ChebyshevParityRecurrence
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix Kronecker NNReal ENNReal NNRat
/- ## 2D Chebyshev Reflection Recurrence & Conjugate-Zero Parity Attempt WP (`M20`) -/
/-- Single-slot diagonal phase entry flipping sign when `x ∈ S` and flag `b = 1`. -/
def slotVerPhaseDiag {n : ℕ} (S : Finset (Fin (2 ^ n))) (idx : Fin (2 ^ (n + 1))) : ℂ :=
  if (splitBasisEquiv n 1 idx).1 ∈ S ∧ (splitBasisEquiv n 1 idx).2 = 1 then -1 else 1
/-- Global diagonal phase entry across all active slots. -/
def allSlotsVerPhaseDiag (n m k : ℕ) (S : Finset (Fin (2 ^ n)))
    (o : Fin (2 ^ findAllQubits n m k)) : ℂ :=
  ((slotRegList n m k).map fun r ↦ slotVerPhaseDiag S (r.extractIndex o)).prod
end QuantumComputation.Specs
end
end Sec_ChebyshevParityRecurrence
section Sec_SexticCascadeCorrectness
@[expose] public section

open Store (Expr)
open QuantumComputation.Specs.GroverAuxDefs
namespace QuantumComputation.Specs
open Operator ResourceCounting Real
open scoped Matrix NNReal ENNReal QHLExpectation ComplexOrder MatrixOrder
private lemma s25_expectedCost_eq_zero_of_stateMass_eq_zero {Var : Type} [DecidableEq Var]
    {d : ℕ} [NeZero d] (model : CostModel d) (p : QProg Var d) :
    ∀ {Δ : CQState (Store Var) d}, stateMass Δ = 0 → expectedCost model p Δ = 0 := by induction p
      with
  | skip => intro Δ _; rfl
  | abort => intro Δ _; rfl
  | assign x e => intro Δ hΔ; have h0 : Δ.trace = 0 := ENNReal.coe_eq_zero.mp hΔ; simp [h0]
  | qMeasure x m => intro Δ hΔ; have h0 : Δ.trace = 0 := ENNReal.coe_eq_zero.mp hΔ; simp [h0]
  | qSet => intro Δ hΔ; have h0 : Δ.trace = 0 := ENNReal.coe_eq_zero.mp hΔ; simp [h0]
  | qAssign u => intro Δ hΔ; have h0 : Δ.trace = 0 := ENNReal.coe_eq_zero.mp hΔ; simp [h0]
  | qSeq p₁ p₂ ih₁ ih₂ =>
      intro Δ hΔ
      rw [expectedCost_qSeq, ih₁ hΔ, zero_add]
      exact ih₂ (nonpos_iff_eq_zero.mp ((stateMass_interp_le p₁ Δ).trans_eq hΔ))
  | qIf cond p₁ p₂ ih₁ ih₂ =>
      intro Δ hΔ
      rw [cqExpectedCostIf]; have ht : stateMass (Δ.cqTrueSt cond) = 0 :=
        nonpos_iff_eq_zero.mp ((stateMass_cqTrueSt_le cond Δ).trans_eq hΔ)
      have hf : stateMass (Δ.cqFalseSt cond) = 0 := by
        have hp := stateMass_cqTrue_cqFalse_split cond Δ; rw [ht, zero_add, hΔ] at hp; exact hp
      rw [ih₁ ht, ih₂ hf, add_zero]
  | qWhile cond body ih =>
      intro Δ hΔ
      rw [expectedCost_qWhile_eq_tsum]
      refine ENNReal.tsum_eq_zero.mpr fun i ↦ ih ?_; exact nonpos_iff_eq_zero.mp
        ((antitone_stateMass_activeIter cond body Δ (Nat.zero_le i)).trans
          ((stateMass_cqTrueSt_le cond Δ).trans_eq hΔ))
private lemma s25_expect_true_false_eq_cqTrace {Var : Type} {d : ℕ}
    (cond : Store Var → Prop) [DecidablePred cond] (Δ : CQState (Store Var) d) (Θ : CQAssertion
      (Store Var) d)
    (hΔ : 𝔼[Δ, Θ] = CQState.trace Δ) : 𝔼[Δ.cqTrueSt cond, Θ] = CQState.trace (Δ.cqTrueSt cond) ∧
    𝔼[Δ.cqFalseSt cond, Θ] = CQState.trace (Δ.cqFalseSt cond) := by
  have hpart_exp : 𝔼[Δ, Θ] = 𝔼[Δ.cqTrueSt cond, Θ] + 𝔼[Δ.cqFalseSt cond, Θ] := by
    simpa [ite_self] using cqExpect_ite_split cond Δ Θ Θ
  have hpart_tr : (CQState.trace (Δ.cqTrueSt cond) : ℝ) + CQState.trace (Δ.cqFalseSt cond) =
    CQState.trace Δ := by exact_mod_cast CQState.trace_cqTrueSt_add_trace_cqFalseSt cond Δ
  have hle_t : 𝔼[Δ.cqTrueSt cond, Θ] ≤ CQState.trace (Δ.cqTrueSt cond) :=
    (expect_mono le_rfl le_top).trans_eq (expect_top _)
  have hle_f : 𝔼[Δ.cqFalseSt cond, Θ] ≤ CQState.trace (Δ.cqFalseSt cond) :=
    (expect_mono le_rfl le_top).trans_eq (expect_top _)
  constructor <;> linarith
private lemma s25_stateMass_trueState_eq_zero_of_disjoint {Var : Type} {d : ℕ}
    (cond : Store Var → Prop) [DecidablePred cond] (Δ : CQState (Store Var) d) (Θ : CQAssertion
      (Store Var) d)
    (hΔ : 𝔼[Δ, Θ] = CQState.trace Δ) (hdisj : ∀ σ, cond σ → Θ σ = ⊥) :
    stateMass (Δ.cqTrueSt cond) = 0 := by
  have htf := s25_expect_true_false_eq_cqTrace cond Δ Θ hΔ
  have hfun : (fun σ ↦ if cond σ then (⊥ : CQAssertion (Store Var) d) σ else Θ σ) = Θ := by
    funext σ
    by_cases hc : cond σ
    · simp [hc, hdisj σ hc]
    · simp [hc]
  have hpart := cqExpect_ite_split cond Δ ⊥ Θ; rw [hfun, expect_bot, zero_add] at hpart
  have hpart2 : 𝔼[Δ, Θ] = 𝔼[Δ.cqTrueSt cond, Θ] + 𝔼[Δ.cqFalseSt cond, Θ] := by
    simpa [ite_self] using cqExpect_ite_split cond Δ Θ Θ
  have htr0 : (CQState.trace (Δ.cqTrueSt cond) : ℝ) = 0 := by linarith [htf.1]
  rw [stateMass_eq_ofReal_trace, htr0, ENNReal.ofReal_zero]
private lemma s25_card_sdiff_image_of_valid {n k p r : ℕ} (hrk : r ≤ k) (hp : k - r = p)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k)
    {xs : Fin p → Fin (2 ^ n)} (hxs_inj : Function.Injective xs)
    (hxs_sub : Finset.univ.image xs ⊆ S) : (S \ Finset.univ.image xs).card = r := by
  have hS_card : S.card = k := (Finset.mem_powersetCard.mp hS).2
  have hT_card : (Finset.univ.image xs).card = p := by
    rw [Finset.card_image_of_injective _ hxs_inj, Finset.card_fin]
  rw [Finset.card_sdiff_of_subset hxs_sub, hS_card, hT_card]; omega
theorem sexticStratum_correct_and_cost {Var : Type} [DecidableEq Var]
    {n m k p r s1 s2 s3 s4 s5 s6 : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hkN : k ≤ 2 ^ n)
    (hr1 : 1 ≤ r) (hrk : r ≤ k) (hp : k - r = p) (hs1_eq : s1 = sexticStratum1 (activeSlots m k) r)
    (hs2_eq : s2 = sexticStratum2 (activeSlots m k) r)
    (hs3_eq : s3 = sexticStratum3 (activeSlots m k) r)
    (hs4_eq : s4 = sexticStratum4 (activeSlots m k) r)
    (hs5_eq : s5 = sexticStratum5 (activeSlots m k) r)
    (hs6_eq : s6 = sexticStratum6 (activeSlots m k) r)
    (res : Var) {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k)
    (cont1 cont2 cont3 cont4 cont5 cont6 : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k))
        Var (findAllQubits n m k) ((n + 1) * activeSlots m k))
    (Φ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) (V1 V2 V3 V4 V5 V6 : ℝ≥0)
    (hwp1 : ∀ τ : Store Var, ValidStageStore n S (p + s1) res τ →
      wp (cont1.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1)
    (hwp2 : ∀ τ : Store Var, ValidStageStore n S (p + s2) res τ →
      wp (cont2.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1)
    (hwp3 : ∀ τ : Store Var, ValidStageStore n S (p + s3) res τ →
      wp (cont3.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1)
    (hwp4 : ∀ τ : Store Var, ValidStageStore n S (p + s4) res τ →
      wp (cont4.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1)
    (hwp5 : ∀ τ : Store Var, ValidStageStore n S (p + s5) res τ →
      wp (cont5.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1)
    (hwp6 : ∀ τ : Store Var, ValidStageStore n S (p + s6) res τ →
      wp (cont6.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Φ τ = 1)
    (hcost1 : ∀ Δ1 : CQState (Store Var) (2 ^ findAllQubits n m k),
      𝔼[Δ1, liftPureProp (ValidStageStore n S (p + s1) res)] = CQState.trace Δ1 →
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
        (cont1.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ1 ≤
        stateMass Δ1 * (V1 : ℝ≥0∞)) (hcost2 : ∀ Δ2 : CQState (Store Var) (2 ^ findAllQubits n m k),
      𝔼[Δ2, liftPureProp (ValidStageStore n S (p + s2) res)] = CQState.trace Δ2 →
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
        (cont2.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ2 ≤
        stateMass Δ2 * (V2 : ℝ≥0∞)) (hcost3 : ∀ Δ3 : CQState (Store Var) (2 ^ findAllQubits n m k),
      𝔼[Δ3, liftPureProp (ValidStageStore n S (p + s3) res)] = CQState.trace Δ3 →
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
        (cont3.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ3 ≤
        stateMass Δ3 * (V3 : ℝ≥0∞)) (hcost4 : ∀ Δ4 : CQState (Store Var) (2 ^ findAllQubits n m k),
      𝔼[Δ4, liftPureProp (ValidStageStore n S (p + s4) res)] = CQState.trace Δ4 →
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
        (cont4.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ4 ≤
        stateMass Δ4 * (V4 : ℝ≥0∞)) (hcost5 : ∀ Δ5 : CQState (Store Var) (2 ^ findAllQubits n m k),
      𝔼[Δ5, liftPureProp (ValidStageStore n S (p + s5) res)] = CQState.trace Δ5 →
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
        (cont5.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ5 ≤
        stateMass Δ5 * (V5 : ℝ≥0∞)) (hcost6 : ∀ Δ6 : CQState (Store Var) (2 ^ findAllQubits n m k),
      𝔼[Δ6, liftPureProp (ValidStageStore n S (p + s6) res)] = CQState.trace Δ6 →
      expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
        (cont6.compile QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ6 ≤
        stateMass Δ6 * (V6 : ℝ≥0∞)) :
    let prog := (sexticStratumCircuit n m k p r s1 s2 s3 s4 s5 s6 res
      cont1 cont2 cont3 cont4 cont5 cont6).compile
      QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)
    let q2 := sexticProb2NNReal n m k r
    let q3 := sexticProb3NNReal n m k r
    let q4 := sexticProb4NNReal n m k r
    let q5 := sexticProb5NNReal n m k r
    let q6 := sexticProb6NNReal n m k r
    let W6 := V6
    let W5 := max V5 W6
    let W4 := max V4 W5
    let W3 := max V3 W4
    let W2 := max V2 W3
    let W1 := max V1 W2
    (∀ σ : Store Var, ValidStageStore n S p res σ → wp prog Φ σ = 1) ∧
    (∀ Δ : CQState (Store Var) (2 ^ findAllQubits n m k),
      𝔼[Δ, liftPureProp (ValidStageStore n S p res)] = CQState.trace Δ →
      expectedCost
          (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S)) prog Δ ≤
        stateMass Δ * ((sexticLoopCostNNReal n m k r +
            ((1 - q2) * W1 + (q2 - q3) * W2 + (q3 - q4) * W3 +
              (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6) : ℝ≥0) : ℝ≥0∞)) := by
  have _ := hn; have hw1 : 1 ≤ activeSlots m k := activeSlots_pos m k
  rcases sexticStratum_bounds hw1 hr1 with
    ⟨hs1_ge1', hs1_s2', hs2_s3', hs3_s4', hs4_s5', hs5_s6', hs6_le8', hsw6', hsr6'⟩
  have hs1_ge1 : 1 ≤ s1 := hs1_eq ▸ hs1_ge1'; have hs1_s2 : s1 ≤ s2 := hs1_eq ▸ hs2_eq ▸ hs1_s2'
  have hs2_s3 : s2 ≤ s3 := hs2_eq ▸ hs3_eq ▸ hs2_s3'
  have hs3_s4 : s3 ≤ s4 := hs3_eq ▸ hs4_eq ▸ hs3_s4'
  have hs4_s5 : s4 ≤ s5 := hs4_eq ▸ hs5_eq ▸ hs4_s5'
  have hs5_s6 : s5 ≤ s6 := hs5_eq ▸ hs6_eq ▸ hs5_s6'; have hs6_le8 : s6 ≤ 8 := hs6_eq ▸ hs6_le8'
  have hsw6 : s6 ≤ activeSlots m k := hs6_eq ▸ hsw6'; have hsr6 : s6 ≤ r := hs6_eq ▸ hsr6'
  have hs1_s6 : s1 ≤ s6 := (((hs1_s2.trans hs2_s3).trans hs3_s4).trans hs4_s5).trans hs5_s6
  have hs1_le8 : s1 ≤ 8 := hs1_s6.trans hs6_le8
  have hsw1 : s1 ≤ activeSlots m k := hs1_s6.trans hsw6; have hsr1 : s1 ≤ r := hs1_s6.trans hsr6
  have hps : p + s1 ≤ k ∧ p + s2 ≤ k ∧ p + s3 ≤ k ∧ p + s4 ≤ k ∧ p + s5 ≤ k ∧ p + s6 ≤ k :=
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hrd : r ≤ 2 ^ n := by omega
  have hprog : (sexticStratumCircuit n m k p r s1 s2 s3 s4 s5 s6 res
        cont1 cont2 cont3 cont4 cont5 cont6).compile
        QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S) =
      (branchOnTupleExpr (fun σ ↦ σ res) (fun xs ↦ sexticStratumBranchCircuit n m k
          hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
          cont1 cont2 cont3 cont4 cont5 cont6) (enumTuples n p)).compile QProg.qAssign
          (groverParallelMarkingOracle (activeSlots m k) S) := by
    rw [sexticStratumCircuit, dite_eq_left hps]
  intro prog q2 q3 q4 q5 q6 W6 W5 W4 W3 W2 W1
  dsimp only [prog]; rw [hprog]
  constructor
  · rintro σ ⟨xs, hxs_inj, hxs_sub, hσ_res⟩
    rw [wp_compile_branchOnTupleExpr_m20 QProg.qAssign
      (groverParallelMarkingOracle (activeSlots m k) S) (fun σ ↦ σ res)
      (fun xs ↦ sexticStratumBranchCircuit n m k
        hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
        cont1 cont2 cont3 cont4 cont5 cont6)
      (enumTuples n p) xs (mem_enumTuples n xs) _ σ hσ_res]
    exact wp_sexticStratumBranchCircuit hm
      hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2
      hs1_ge1 hs1_le8 hsw1 hsr1 hrd
      hxs_inj hxs_sub (s25_card_sdiff_image_of_valid hrk hp hS hxs_inj hxs_sub)
      res cont1 cont2 cont3 cont4 cont5 cont6 Φ hwp1 hwp2 hwp3 hwp4 hwp5 hwp6 σ
  · suffices h_branch : ∀ (l : List (Fin p → Fin (2 ^ n)))
        (Δ : CQState (Store Var) (2 ^ findAllQubits n m k)),
        𝔼[Δ, liftPureProp (ValidStageStore n S p res)] = CQState.trace Δ →
        expectedCost (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
          ((branchOnTupleExpr (fun σ ↦ σ res)
            (fun xs ↦ sexticStratumBranchCircuit n m k
              hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
              cont1 cont2 cont3 cont4 cont5 cont6) l).compile
            QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) Δ ≤
          stateMass Δ * ((sexticLoopCostNNReal n m k r +
              ((1 - q2) * W1 + (q2 - q3) * W2 + (q3 - q4) * W3 +
                (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6) : ℝ≥0) : ℝ≥0∞) by
      exact h_branch (enumTuples n p)
    intro l
    induction l with
    | nil =>
        intro Δ _
        simp [branchOnTupleExpr]
    | cons xs rest ih =>
        intro Δ hΔ
        let cond : Store Var → Prop := fun σ ↦ σ res = (encodeTuple n xs : ℤ)
        rw [show (branchOnTupleExpr (fun σ ↦ σ res)
              (fun xs ↦ sexticStratumBranchCircuit n m k
                hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
                cont1 cont2 cont3 cont4 cont5 cont6)
              (xs :: rest)).compile QProg.qAssign
                (groverParallelMarkingOracle (activeSlots m k) S) =
            .qIf cond ((sexticStratumBranchCircuit n m k
                hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
                cont1 cont2 cont3 cont4 cont5 cont6).compile
                QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S))
              ((branchOnTupleExpr (fun σ ↦ σ res)
                (fun xs ↦ sexticStratumBranchCircuit n m k
                  hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
                  cont1 cont2 cont3 cont4 cont5 cont6) rest).compile
                QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) from rfl,
          cqExpectedCostIf]
        rcases s25_expect_true_false_eq_cqTrace cond Δ
            (liftPureProp (ValidStageStore n S p res)) hΔ with ⟨_, h_false⟩
        have h_rest := ih (Δ.cqFalseSt cond) h_false; have h_head : expectedCost
            (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
            ((sexticStratumBranchCircuit n m k
              hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
              cont1 cont2 cont3 cont4 cont5 cont6).compile
              QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S)) (Δ.cqTrueSt cond) ≤
            stateMass (Δ.cqTrueSt cond) * ((sexticLoopCostNNReal n m k r +
                ((1 - q2) * W1 + (q2 - q3) * W2 + (q3 - q4) * W3 +
                  (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6) : ℝ≥0) : ℝ≥0∞) := by
          by_cases hvalid : Function.Injective xs ∧ Finset.univ.image xs ⊆ S
          · exact expectedCost_sexticStratumBranchCircuit_le hm hrd
              hs1_ge1 hs1_s2 hs2_s3 hs3_s4 hs4_s5 hs5_s6 hs6_le8 hsw6 hsr6
              hs1_eq hs2_eq hs3_eq hs4_eq hs5_eq hs6_eq
              hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2
              hvalid.1 hvalid.2
              (s25_card_sdiff_image_of_valid hrk hp hS hvalid.1 hvalid.2)
              res cont1 cont2 cont3 cont4 cont5 cont6
              V1 V2 V3 V4 V5 V6 hcost1 hcost2 hcost3 hcost4 hcost5 hcost6
              (Δ.cqTrueSt cond)
          · have hmass0 : stateMass (Δ.cqTrueSt cond) = 0 := by
              refine s25_stateMass_trueState_eq_zero_of_disjoint cond Δ
                (liftPureProp (ValidStageStore n S p res)) hΔ (fun σ hres ↦ ?_)
              have hnot_valid : ¬ ValidStageStore n S p res σ := by
                rintro ⟨xs', hxs'_inj, hxs'_sub, hσ'⟩
                have heq : xs = xs' := encodeTuple_injective n (Int.ofNat.inj (hres.symm.trans hσ'))
                subst heq
                exact hvalid ⟨hxs'_inj, hxs'_sub⟩
              simp [hnot_valid]
            rw [s25_expectedCost_eq_zero_of_stateMass_eq_zero _ _ hmass0, hmass0, zero_mul]
        calc
          expectedCost
              (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
              ((sexticStratumBranchCircuit n m k
                hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
                cont1 cont2 cont3 cont4 cont5 cont6).compile
                QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S))
                (Δ.cqTrueSt cond) + expectedCost
                  (CostModel.ofEmbeddedOracle (groverParallelMarkingOracle (activeSlots m k) S))
                ((branchOnTupleExpr (fun σ ↦ σ res)
                  (fun xs ↦ sexticStratumBranchCircuit n m k
                    hps.1 hps.2.1 hps.2.2.1 hps.2.2.2.1 hps.2.2.2.2.1 hps.2.2.2.2.2 r xs res
                    cont1 cont2 cont3 cont4 cont5 cont6) rest).compile
                  QProg.qAssign (groverParallelMarkingOracle (activeSlots m k) S))
                  (Δ.cqFalseSt cond)
            ≤ stateMass (Δ.cqTrueSt cond) * ((sexticLoopCostNNReal n m k r +
                  ((1 - q2) * W1 + (q2 - q3) * W2 + (q3 - q4) * W3 +
                    (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6) : ℝ≥0) : ℝ≥0∞) +
                stateMass (Δ.cqFalseSt cond) * ((sexticLoopCostNNReal n m k r +
                  ((1 - q2) * W1 + (q2 - q3) * W2 + (q3 - q4) * W3 +
                    (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6) : ℝ≥0) : ℝ≥0∞) :=
            add_le_add h_head h_rest
          _ = (stateMass (Δ.cqTrueSt cond) + stateMass (Δ.cqFalseSt cond)) *
                ((sexticLoopCostNNReal n m k r + ((1 - q2) * W1 + (q2 - q3) * W2 + (q3 - q4) * W3 +
                    (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6) : ℝ≥0) : ℝ≥0∞) := by
            rw [← add_mul]
          _ = stateMass Δ * ((sexticLoopCostNNReal n m k r +
                  ((1 - q2) * W1 + (q2 - q3) * W2 + (q3 - q4) * W3 +
                    (q4 - q5) * W4 + (q5 - q6) * W5 + q6 * W6) : ℝ≥0) : ℝ≥0∞) := by
            rw [stateMass_cqTrue_cqFalse_split]
end QuantumComputation.Specs
end
end Sec_SexticCascadeCorrectness
end Sec_SexticCascadeCorrectness
section Sec_TensorConveyorBasis2d
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real
open scoped Matrix
open QuantumComputation.Specs.GroverFindAll.TensorConveyorCert
/-- Phase-flip unitary `-1` on `R` and `+1` outside `R` on `Fin (2 ^ n)`. -/
def setOracleUnitary {n : ℕ} (R : Finset (Fin (2 ^ n))) : Unitary (2 ^ n) :=
  ⟨setOracleMatrix R, by
    rw [setOracleMatrix, Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    split_ifs <;> simp⟩
/-- Single Grover step `D * O_R` on `Fin (2 ^ n)`. -/
noncomputable def groverStepUnitary {n : ℕ} (R : Finset (Fin (2 ^ n))) : Unitary (2 ^ n) :=
  Grover.diffuserUnitary * setOracleUnitary R
/-- Subset of register indices `q: Fin d` whose `n`-bit address lies in `R`. -/
def tcHitRegs (n d : ℕ) (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (n * d))) : Finset (Fin d) :=
  Finset.univ.filter fun q : Fin d ↦ (localMemSlotReg n d q).extractIndex z ∈ R
namespace TensorConveyorBasis2d
/- ## 1. `d`-Register Tuple Bijection, Real Matrix Lifting, & Product Hadamard -/
/-- `d`-tuple index space `Fin d → Fin (2 ^ n)` for a single `n * d`-qubit conveyor slot. -/
abbrev TupleSpace (n d : ℕ) : Type := Fin d → Fin (2 ^ n)
theorem localMemSlotReg_disjoint {n d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    (localMemSlotReg n d i).DisjointWires (localMemSlotReg n d j) := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
  · exact QRegister.block_disjoint_of_le _ _ _ _ _ _ (by nlinarith)
  · exact QRegister.disjoint_comm.2
      (QRegister.block_disjoint_of_le _ _ _ _ _ _ (by nlinarith))
/-- Bijection between `Fin (2 ^ (n * d))` and `Fin d → Fin (2 ^ n)` via `localMemSlotReg`. -/
noncomputable def regsEquiv (n d : ℕ) : Fin (2 ^ (n * d)) ≃ TupleSpace n d :=
  Equiv.ofBijective (fun z q ↦ (localMemSlotReg n d q).extractIndex z) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [pow_mul]⟩
    by_cases hn0 : n = 0
    · subst hn0
      exact fun z₁ z₂ _ ↦ Fin.ext (by have := z₁.isLt; have := z₂.isLt; simp at *; omega)
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      intro z₁ z₂ h
      apply (basisBits (n * d)).injective
      funext w
      have hi_lt : w.val / n < d := Nat.div_lt_of_lt_mul w.isLt
      let i : Fin d := ⟨w.val / n, hi_lt⟩
      let c : Fin n := ⟨w.val % n, Nat.mod_lt _ hn_pos⟩
      have hw_eq : w = localMemSlotReg n d i c := by
        ext
        simp only [localMemSlotReg, QRegister.block_apply_val, i, c]
        exact (Nat.div_add_mod' w.val n).symm
      have hi_eq : (localMemSlotReg n d i).extractIndex z₁ =
          (localMemSlotReg n d i).extractIndex z₂ := congrFun h i
      rw [hw_eq, ← (localMemSlotReg n d i).basisBits_extractIndex,
        ← (localMemSlotReg n d i).basisBits_extractIndex, hi_eq]
@[simp]
theorem regsEquiv_apply (n d : ℕ) (z : Fin (2 ^ (n * d))) (q : Fin d) :
    regsEquiv n d z q = (localMemSlotReg n d q).extractIndex z :=
  rfl
theorem regsEquiv_replaceIndex {n d : ℕ} (z : Fin (2 ^ (n * d))) (q : Fin d) (x : Fin (2 ^ n)) :
    regsEquiv n d ((localMemSlotReg n d q).replaceIndex z x) =
      Function.update (regsEquiv n d z) q x := by
  funext q'
  by_cases hqq : q' = q
  · subst hqq
    simp
  · simp only [regsEquiv_apply, Function.update_of_ne hqq]
    exact (localMemSlotReg n d q').extractIndex_replaceIndex_of_disjoint (localMemSlotReg n d q)
      (localMemSlotReg_disjoint hqq) z x
theorem tcHitRegs_eq_filter_regsEquiv (n d : ℕ) (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (n * d))) :
    tcHitRegs n d R z = Finset.univ.filter (fun q : Fin d ↦ regsEquiv n d z q ∈ R) := by
  ext q
  simp only [tcHitRegs, Finset.mem_filter, Finset.mem_univ, true_and]; rw [regsEquiv_apply]
/-- Lift a real matrix on `TupleSpace n d` to a complex matrix on `Fin (2 ^ (n * d))`. -/
noncomputable def liftTupleRealMat {n d : ℕ} (M : Matrix (TupleSpace n d) (TupleSpace n d) ℝ) :
    Matrix (Fin (2 ^ (n * d))) (Fin (2 ^ (n * d))) ℂ :=
  (M.map Complex.ofReal).submatrix (regsEquiv n d) (regsEquiv n d)
theorem isRealMatrix_liftTupleRealMat {n d : ℕ} (M : Matrix (TupleSpace n d) (TupleSpace n d) ℝ) :
    IsRealMatrix (liftTupleRealMat M) := by
  intro a b
  simp [liftTupleRealMat]
theorem liftTupleRealMat_one (n d : ℕ) :
    liftTupleRealMat (1 : Matrix (TupleSpace n d) (TupleSpace n d) ℝ) = 1 := by
  ext a b
  simp only [liftTupleRealMat, Matrix.submatrix_apply, Matrix.map_apply, Matrix.one_apply,
    (regsEquiv n d).injective.eq_iff]
  split_ifs <;> simp
theorem liftTupleRealMat_mul {n d : ℕ} (A B : Matrix (TupleSpace n d) (TupleSpace n d) ℝ) :
    liftTupleRealMat (A * B) = liftTupleRealMat A * liftTupleRealMat B := by
  ext a b
  simp only [liftTupleRealMat, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul]
  exact ((regsEquiv n d).sum_comp fun f ↦
    ((A (regsEquiv n d a) f : ℂ) * (B f (regsEquiv n d b) : ℂ))).symm
theorem liftTupleRealMat_conjTranspose {n d : ℕ} (M : Matrix (TupleSpace n d) (TupleSpace n d) ℝ) :
    (liftTupleRealMat M)ᴴ = liftTupleRealMat Mᵀ := by
  ext a b
  simp [liftTupleRealMat]
theorem liftTupleRealMat_mem_unitaryGroup {n d : ℕ} {M : Matrix (TupleSpace n d) (TupleSpace n d) ℝ}
    (h1 : Mᵀ * M = 1) (_h2 : M * Mᵀ = 1) :
    liftTupleRealMat M ∈ Matrix.unitaryGroup (Fin (2 ^ (n * d))) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, liftTupleRealMat_conjTranspose,
    ← liftTupleRealMat_mul Mᵀ M, h1, liftTupleRealMat_one]
theorem liftTupleRealMat_mulVec_comp {n d : ℕ}
    (M : Matrix (TupleSpace n d) (TupleSpace n d) ℝ) (v : TupleSpace n d → ℝ)
    (z : Fin (2 ^ (n * d))) : (liftTupleRealMat M *ᵥ fun w ↦ (v (regsEquiv n d w) : ℂ)) z =
      (((M *ᵥ v) (regsEquiv n d z) : ℝ) : ℂ) := by
  simp only [liftTupleRealMat, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul]
  exact (regsEquiv n d).sum_comp fun f ↦ ((M (regsEquiv n d z) f : ℂ) * (v f : ℂ))
/-- Real entries `(hadamardMatrix n i j).re` of the `n`-qubit Walsh-Hadamard transform. -/
noncomputable def realHadamard (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  Matrix.of fun i j ↦ (hadamardMatrix n i j).re
theorem ofReal_realHadamard (n : ℕ) (i j : Fin (2 ^ n)) :
    ((realHadamard n i j : ℝ) : ℂ) = hadamardMatrix n i j :=
  Complex.ext rfl (isRealMatrix_hadamardMatrix n i j).symm
theorem realHadamard_transpose (n : ℕ) : (realHadamard n)ᵀ = realHadamard n := by
  ext i j
  apply Complex.ofReal_injective
  rw [Matrix.transpose_apply, ofReal_realHadamard, ofReal_realHadamard]
  have h := congr($(hadamardMatrix_conjTranspose n) i j)
  rw [Matrix.conjTranspose_apply, ← ofReal_realHadamard, Complex.star_def, Complex.conj_ofReal,
    ofReal_realHadamard] at h
  exact h
theorem realHadamard_mul_self (n : ℕ) : realHadamard n * realHadamard n = 1 := by
  ext i j
  have h := congr($(hadamardMatrix_mul_self n) i j)
  simp only [Matrix.mul_apply, ← ofReal_realHadamard, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Matrix.one_apply] at h
  have hrhs : (if i = j then (1 : ℂ) else 0) = (((1 : Matrix _ _ ℝ) i j : ℝ) : ℂ) := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hrhs] at h; rw [Matrix.mul_apply]; exact Complex.ofReal_injective h
/-- Tensor-power Hadamard matrix `(realHadamard n)^{⊗ d}` on `TupleSpace n d`. -/
noncomputable def hProdMat (n d : ℕ) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  Matrix.of fun f g ↦ ∏ q : Fin d, realHadamard n (f q) (g q)
theorem hProdMat_transpose (n d : ℕ) : (hProdMat n d)ᵀ = hProdMat n d := by
  ext f g
  simp only [Matrix.transpose_apply, hProdMat, Matrix.of_apply]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  simpa using congr($(realHadamard_transpose n) (f q) (g q))
theorem hProdMat_mul_self (n d : ℕ) : hProdMat n d * hProdMat n d = 1 := by
  ext f h
  simp only [Matrix.mul_apply, hProdMat, Matrix.of_apply, ← Finset.prod_mul_distrib]
  have hprod := (Fintype.prod_sum fun (q : Fin d) (y : Fin (2 ^ n)) ↦
    realHadamard n (f q) y * realHadamard n y (h q)).symm
  rw [hprod]
  have hfactor : ∀ q : Fin d, (∑ y : Fin (2 ^ n), realHadamard n (f q) y * realHadamard n y (h q)) =
        if f q = h q then 1 else 0 := by
    intro q
    have h1 := congr($(realHadamard_mul_self n) (f q) (h q))
    simpa [Matrix.mul_apply, Matrix.one_apply] using h1
  simp_rw [hfactor]
  by_cases hfh : f = h
  · subst hfh; simp
  · have hex : ∃ q : Fin d, f q ≠ h q := Function.ne_iff.1 hfh; rcases hex with ⟨q, hq⟩
    rw [Matrix.one_apply_ne hfh]; exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])
/- ## 2. Coordinate Symmetrizers & Weight-Block Partial-Isometry Intertwiner -/
/-- Coordinate-permutation matrix `(permMat n d σ) f g = [f ∘ σ = g]` on `TupleSpace n d`. -/
def permMat (n d : ℕ) (σ : Equiv.Perm (Fin d)) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  Matrix.of fun f g ↦ if f ∘ σ = g then 1 else 0
theorem permMat_mulVec {n d : ℕ} (σ : Equiv.Perm (Fin d)) (v : TupleSpace n d → ℝ)
    (f : TupleSpace n d) : (permMat n d σ *ᵥ v) f = v (f ∘ σ) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (f ∘ σ)]
  · simp [permMat]
  · intro g _ hne
    have hne' : f ∘ σ ≠ g := hne.symm; simp [permMat, hne']
  · intro h
    exact (h (Finset.mem_univ _)).elim
theorem permMat_transpose (n d : ℕ) (σ : Equiv.Perm (Fin d)) :
    (permMat n d σ)ᵀ = permMat n d σ⁻¹ := by
  ext f g
  simp only [Matrix.transpose_apply, permMat, Matrix.of_apply]
  have hiff : (g ∘ ⇑σ = f) ↔ (f ∘ ⇑(σ⁻¹) = g) := by
    constructor <;> intro h <;> funext i <;> rw [← h] <;> simp
  by_cases h : g ∘ ⇑σ = f
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.2 h)]
theorem permMat_mul (n d : ℕ) (σ τ : Equiv.Perm (Fin d)) :
    permMat n d σ * permMat n d τ = permMat n d (σ * τ) := by
  ext f h
  rw [Matrix.mul_apply, Finset.sum_eq_single (f ∘ σ)]
  · have hcomp : (f ∘ ⇑σ) ∘ ⇑τ = f ∘ ⇑(σ * τ) := by
      funext i; rfl
    simp only [permMat, Matrix.of_apply, ↓reduceIte, one_mul, hcomp]
  · intro g _ hne
    have hne' : f ∘ σ ≠ g := hne.symm; simp [permMat, hne']
  · intro habs
    exact (habs (Finset.mem_univ _)).elim
/-- Subgroup type of permutations of `Fin d` fixing coordinate `⟨0, hd⟩`. -/
abbrev StabZero (d : ℕ) (hd : 1 ≤ d) : Type := {σ : Equiv.Perm (Fin d) // σ ⟨0, hd⟩ = ⟨0, hd⟩}
/-- Inversion equivalence on `StabZero d hd`. -/
def stabInvEquiv (d : ℕ) (hd : 1 ≤ d) : StabZero d hd ≃ StabZero d hd where
  toFun τ := ⟨τ.1⁻¹, (congrArg (⇑(τ.1⁻¹)) τ.2).symm.trans (τ.1.symm_apply_apply ⟨0, hd⟩)⟩
  invFun τ := ⟨τ.1⁻¹, (congrArg (⇑(τ.1⁻¹)) τ.2).symm.trans (τ.1.symm_apply_apply ⟨0, hd⟩)⟩
  left_inv τ := by ext1; exact inv_inv τ.1
  right_inv τ := by ext1; exact inv_inv τ.1
/-- Left-multiplication equivalence on `StabZero d hd`. -/
def stabMulLeftEquiv (d : ℕ) (hd : 1 ≤ d) (ρ : StabZero d hd) :
    StabZero d hd ≃ StabZero d hd where
  toFun τ := ⟨ρ.1 * τ.1, by simp [Equiv.Perm.mul_apply, τ.2, ρ.2]⟩
  invFun τ := ⟨ρ.1⁻¹ * τ.1, by
    rw [Equiv.Perm.mul_apply, τ.2]
    exact (congrArg (⇑(ρ.1⁻¹)) ρ.2).symm.trans (ρ.1.symm_apply_apply ⟨0, hd⟩)⟩
  left_inv τ := by ext1; simp
  right_inv τ := by ext1; simp
/-- Coset decomposition `Fin d × StabZero d hd ≃ Equiv.Perm (Fin d)` via `Equiv.swap ⟨0, hd⟩
  j`. -/
def cosetEquiv (d : ℕ) (hd : 1 ≤ d) :
    Fin d × StabZero d hd ≃ Equiv.Perm (Fin d) where
  toFun p := Equiv.swap ⟨0, hd⟩ p.1 * p.2.1
  invFun σ := (σ ⟨0, hd⟩, ⟨Equiv.swap ⟨0, hd⟩ (σ ⟨0, hd⟩) * σ, by simp⟩)
  left_inv := fun ⟨j, ⟨τ, hτ⟩⟩ ↦ by
    ext1
    · simp [Equiv.Perm.mul_apply, hτ]
    · ext i
      simp [Equiv.Perm.mul_apply, hτ]
  right_inv σ := by
    ext i
    simp
/-- Full `S_d` coordinate-symmetrizer on `TupleSpace n d`. -/
noncomputable def symAllMat (n d : ℕ) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  ((1 : ℝ) / (Fintype.card (Equiv.Perm (Fin d)) : ℝ)) • ∑ σ : Equiv.Perm (Fin d), permMat n d σ
/-- Tail `StabZero d hd` coordinate-symmetrizer on `TupleSpace n d`. -/
noncomputable def symStabMat (n d : ℕ) (hd : 1 ≤ d) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  ((1 : ℝ) / (Fintype.card (StabZero d hd) : ℝ)) • ∑ τ : StabZero d hd, permMat n d τ.1
theorem symAllMat_transpose (n d : ℕ) : (symAllMat n d)ᵀ = symAllMat n d := by
  unfold symAllMat; rw [Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  simp_rw [permMat_transpose]
  exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin d))) (fun σ ↦ permMat n d σ)
theorem symStabMat_transpose (n d : ℕ) (hd : 1 ≤ d) : (symStabMat n d hd)ᵀ = symStabMat n d hd := by
  unfold symStabMat; rw [Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  simp_rw [permMat_transpose]
  simpa [stabInvEquiv] using Equiv.sum_comp (stabInvEquiv d hd) (fun τ ↦ permMat n d τ.1)
theorem permMat_mul_symAllMat (n d : ℕ) (ρ : Equiv.Perm (Fin d)) :
    permMat n d ρ * symAllMat n d = symAllMat n d := by
  unfold symAllMat; rw [Matrix.mul_smul, Finset.mul_sum]
  congr 1
  simp_rw [permMat_mul]
  exact Equiv.sum_comp (Equiv.mulLeft ρ) (fun σ ↦ permMat n d σ)
theorem permMat_mul_symStabMat (n d : ℕ) (hd : 1 ≤ d) (ρ : StabZero d hd) :
    permMat n d ρ.1 * symStabMat n d hd = symStabMat n d hd := by
  unfold symStabMat; rw [Matrix.mul_smul, Finset.mul_sum]
  congr 1
  simp_rw [permMat_mul]
  simpa [stabMulLeftEquiv] using
    Equiv.sum_comp (stabMulLeftEquiv d hd ρ) (fun τ ↦ permMat n d τ.1)
theorem symAllMat_mul_self (n d : ℕ) : symAllMat n d * symAllMat n d = symAllMat n d := by
  nth_rw 1 [symAllMat]
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [permMat_mul_symAllMat]
  ext f g
  rw [Matrix.smul_apply, Matrix.sum_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
  have hpos : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin d)) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  rw [one_div_mul_cancel hpos.ne', one_mul]
theorem symStabMat_mul_self (n d : ℕ) (hd : 1 ≤ d) :
    symStabMat n d hd * symStabMat n d hd = symStabMat n d hd := by
  have : Nonempty (StabZero d hd) := ⟨⟨1, rfl⟩⟩
  nth_rw 1 [symStabMat]
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [permMat_mul_symStabMat]
  ext f g
  rw [Matrix.smul_apply, Matrix.sum_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
  have hpos : (0 : ℝ) < (Fintype.card (StabZero d hd) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  rw [one_div_mul_cancel hpos.ne', one_mul]
theorem card_perm_eq_mul_card_stabZero (d : ℕ) (hd : 1 ≤ d) :
    Fintype.card (Equiv.Perm (Fin d)) = d * Fintype.card (StabZero d hd) := by
  calc Fintype.card (Equiv.Perm (Fin d))
      = Fintype.card (Fin d × StabZero d hd) := Fintype.card_congr (cosetEquiv d hd).symm
    _ = d * Fintype.card (StabZero d hd) := by rw [Fintype.card_prod, Fintype.card_fin]
theorem symAllMat_eq_avgSwap_mul_symStabMat (n d : ℕ) (hd : 1 ≤ d) : symAllMat n d =
      (((1 : ℝ) / (d : ℝ)) • ∑ j : Fin d, permMat n d (Equiv.swap ⟨0, hd⟩ j)) *
        symStabMat n d hd := by
  unfold symAllMat symStabMat; rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul]
  simp_rw [Finset.mul_sum, permMat_mul]
  have hcard : ((1 : ℝ) / (Fintype.card (Equiv.Perm (Fin d)) : ℝ)) =
      ((1 : ℝ) / (d : ℝ)) * ((1 : ℝ) / (Fintype.card (StabZero d hd) : ℝ)) := by
    rw [card_perm_eq_mul_card_stabZero d hd, Nat.cast_mul, one_div_mul_one_div]
  rw [hcard]
  congr 1
  rw [← Fintype.sum_prod_type'
    (fun (j : Fin d) (τ : StabZero d hd) ↦ permMat n d (Equiv.swap ⟨0, hd⟩ j * τ.1))]
  simpa [cosetEquiv] using (Equiv.sum_comp (cosetEquiv d hd) (fun σ ↦ permMat n d σ)).symm
theorem diagonal_mul_apply {α R : Type*} [Fintype α] [DecidableEq α] [Semiring R]
    (v : α → R) (M : Matrix α α R) (i j : α) : (Matrix.diagonal v * M) i j = v i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [Matrix.diagonal]
  · intro k _ hki
    simp [Matrix.diagonal, hki.symm]
  · intro h
    exact (h (Finset.mem_univ i)).elim
theorem mul_diagonal_apply {α R : Type*} [Fintype α] [DecidableEq α] [Semiring R]
    (M : Matrix α α R) (v : α → R) (i j : α) : (M * Matrix.diagonal v) i j = M i j * v j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [Matrix.diagonal]
  · intro k _ hkj
    simp [Matrix.diagonal, hkj]
  · intro h
    exact (h (Finset.mem_univ j)).elim
/-- Number of nonzero coordinates `q: Fin d` (`f q ≠ 0`) in a tuple `f: TupleSpace n d`. -/
def wtTuple {n d : ℕ} (f : TupleSpace n d) : ℕ := (Finset.univ.filter fun q : Fin d ↦ f q ≠ 0).card
theorem wtTuple_le {n d : ℕ} (f : TupleSpace n d) : wtTuple f ≤ d := by
  calc wtTuple f
      ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
    _ = d := by simp
theorem wtTuple_comp_perm {n d : ℕ} (f : TupleSpace n d) (σ : Equiv.Perm (Fin d)) :
    wtTuple (f ∘ σ) = wtTuple f := by
  unfold wtTuple
  refine Finset.card_bij (fun q _ ↦ σ q) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hq ⊢; exact hq
  · intro q₁ _ q₂ _ h
    exact σ.injective h
  · intro q' hq'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq'
    refine ⟨σ⁻¹ q', ?_, σ.apply_symm_apply q'⟩; simp [Function.comp_apply, σ.apply_symm_apply, hq']
/-- Diagonal projector onto tuples of Hamming weight `w` (`wtTuple f = w`). -/
def wtProj (n d w : ℕ) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  Matrix.diagonal fun f ↦ if wtTuple f = w then 1 else 0
/-- Diagonal projector onto tuples of Hamming weight `w` with zero head coordinate
  `f ⟨0, hd⟩ = 0`. -/
def wtZeroProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  Matrix.diagonal fun f ↦ if wtTuple f = w ∧ f ⟨0, hd⟩ = 0 then 1 else 0
theorem wtProj_transpose (n d w : ℕ) : (wtProj n d w)ᵀ = wtProj n d w := Matrix.diagonal_transpose _
theorem wtProj_mul_self (n d w : ℕ) : wtProj n d w * wtProj n d w = wtProj n d w := by
  rw [wtProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext f
  split_ifs <;> simp
theorem wtProj_mul_of_ne (n d : ℕ) {w₁ w₂ : ℕ} (hne : w₁ ≠ w₂) :
    wtProj n d w₁ * wtProj n d w₂ = 0 := by
  ext f g
  rw [wtProj, wtProj, Matrix.diagonal_mul_diagonal]
  by_cases hfg : f = g
  · subst hfg
    rw [Matrix.diagonal_apply_eq]
    by_cases hw1 : wtTuple f = w₁
    · simp [hw1, hne]
    · simp [hw1]
  · simp [Matrix.diagonal_apply_ne _ hfg]
theorem sum_wtProj (n d : ℕ) : (∑ w ∈ Finset.range (d + 1), wtProj n d w) = 1 := by
  ext f g
  rw [Matrix.sum_apply]
  by_cases hfg : f = g
  · subst hfg
    simp only [wtProj, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [Finset.sum_eq_single (wtTuple f)]
    · simp
    · intro w _ hne
      simp [hne.symm]
    · intro hmem
      exact (hmem (Finset.mem_range.2 (Nat.lt_succ_of_le (wtTuple_le f)))).elim
  · simp [wtProj, Matrix.diagonal_apply_ne _ hfg, Matrix.one_apply_ne hfg]
theorem wtZeroProj_transpose (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    (wtZeroProj n d hd w)ᵀ = wtZeroProj n d hd w :=
  Matrix.diagonal_transpose _
theorem wtZeroProj_mul_self (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    wtZeroProj n d hd w * wtZeroProj n d hd w = wtZeroProj n d hd w := by
  rw [wtZeroProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext f
  split_ifs <;> simp
theorem wtProj_mul_wtZeroProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    wtProj n d w * wtZeroProj n d hd w = wtZeroProj n d hd w := by
  rw [wtProj, wtZeroProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext f
  by_cases hw : wtTuple f = w
  · by_cases hf0 : f ⟨0, hd⟩ = 0 <;> simp [hw, hf0]
  · simp [hw]
theorem wtZeroProj_mul_wtProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    wtZeroProj n d hd w * wtProj n d w = wtZeroProj n d hd w := by
  rw [wtProj, wtZeroProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext f
  by_cases hw : wtTuple f = w
  · by_cases hf0 : f ⟨0, hd⟩ = 0 <;> simp [hw, hf0]
  · simp [hw]
theorem permMat_mul_wtProj (n d w : ℕ) (σ : Equiv.Perm (Fin d)) :
    permMat n d σ * wtProj n d w = wtProj n d w * permMat n d σ := by
  ext f g
  rw [wtProj, mul_diagonal_apply, diagonal_mul_apply, permMat, Matrix.of_apply]
  by_cases h : f ∘ σ = g
  · subst h
    rw [wtTuple_comp_perm]; ring
  · simp [h]
theorem symAllMat_mul_wtProj (n d w : ℕ) :
    symAllMat n d * wtProj n d w = wtProj n d w * symAllMat n d := by
  unfold symAllMat; rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun σ _ ↦ permMat_mul_wtProj n d w σ
theorem permMat_mul_wtZeroProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) (τ : StabZero d hd) :
    permMat n d τ.1 * wtZeroProj n d hd w = wtZeroProj n d hd w * permMat n d τ.1 := by
  ext f g
  rw [wtZeroProj, mul_diagonal_apply, diagonal_mul_apply, permMat, Matrix.of_apply]
  by_cases h : f ∘ τ.1 = g
  · subst h
    have h0 : (f ∘ τ.1) ⟨0, hd⟩ = f ⟨0, hd⟩ := by simp [Function.comp_apply, τ.2]
    rw [wtTuple_comp_perm, h0]; ring
  · simp [h]
theorem symStabMat_mul_wtZeroProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    symStabMat n d hd * wtZeroProj n d hd w = wtZeroProj n d hd w * symStabMat n d hd := by
  unfold symStabMat; rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun τ _ ↦ permMat_mul_wtZeroProj n d hd w τ
/-- Weight-`w` `S_d`-symmetric projector `wtProj n d w * symAllMat n d`. -/
noncomputable def p1Mat (n d w : ℕ) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  wtProj n d w * symAllMat n d
/-- Weight-`w` zero-head `StabZero`-symmetric projector `wtZeroProj * symStabMat`. -/
noncomputable def p2Mat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  wtZeroProj n d hd w * symStabMat n d hd
theorem p1Mat_transpose (n d w : ℕ) : (p1Mat n d w)ᵀ = p1Mat n d w := by
  rw [p1Mat, Matrix.transpose_mul, symAllMat_transpose, wtProj_transpose, symAllMat_mul_wtProj]
theorem p1Mat_mul_self (n d w : ℕ) : p1Mat n d w * p1Mat n d w = p1Mat n d w := by
  calc p1Mat n d w * p1Mat n d w
      = wtProj n d w * (symAllMat n d * wtProj n d w) * symAllMat n d := by
          simp only [p1Mat, Matrix.mul_assoc]
    _ = (wtProj n d w * wtProj n d w) * (symAllMat n d * symAllMat n d) := by
          rw [symAllMat_mul_wtProj]; simp only [Matrix.mul_assoc]
    _ = p1Mat n d w := by rw [wtProj_mul_self, symAllMat_mul_self, p1Mat]
theorem p1Mat_mul_wtProj (n d w : ℕ) : p1Mat n d w * wtProj n d w = p1Mat n d w := by
  rw [p1Mat, Matrix.mul_assoc, symAllMat_mul_wtProj, ← Matrix.mul_assoc, wtProj_mul_self]
theorem p2Mat_transpose (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : (p2Mat n d hd w)ᵀ = p2Mat n d hd w := by
  rw [p2Mat, Matrix.transpose_mul, symStabMat_transpose, wtZeroProj_transpose,
    symStabMat_mul_wtZeroProj]
theorem p2Mat_mul_self (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    p2Mat n d hd w * p2Mat n d hd w = p2Mat n d hd w := by
  calc p2Mat n d hd w * p2Mat n d hd w
      = wtZeroProj n d hd w * (symStabMat n d hd * wtZeroProj n d hd w) * symStabMat n d hd := by
          simp only [p2Mat, Matrix.mul_assoc]
    _ = (wtZeroProj n d hd w * wtZeroProj n d hd w) *
          (symStabMat n d hd * symStabMat n d hd) := by
          rw [symStabMat_mul_wtZeroProj]; simp only [Matrix.mul_assoc]
    _ = p2Mat n d hd w := by rw [wtZeroProj_mul_self, symStabMat_mul_self, p2Mat]
theorem wtProj_mul_p2Mat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    wtProj n d w * p2Mat n d hd w = p2Mat n d hd w := by
  rw [p2Mat, ← Matrix.mul_assoc, wtProj_mul_wtZeroProj]
theorem p2Mat_mul_wtProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    p2Mat n d hd w * wtProj n d w = p2Mat n d hd w := by
  calc p2Mat n d hd w * wtProj n d w
      = (p2Mat n d hd w)ᵀ * (wtProj n d w)ᵀ := by rw [p2Mat_transpose, wtProj_transpose]
    _ = (wtProj n d w * p2Mat n d hd w)ᵀ := (Matrix.transpose_mul _ _).symm
    _ = p2Mat n d hd w := by rw [wtProj_mul_p2Mat, p2Mat_transpose]
theorem symStabMat_mul_p2Mat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    symStabMat n d hd * p2Mat n d hd w = p2Mat n d hd w := by
  rw [p2Mat, ← Matrix.mul_assoc, symStabMat_mul_wtZeroProj, Matrix.mul_assoc,
    symStabMat_mul_self]
theorem sum_wtZeroProj_swap_wtZeroProj (n d : ℕ) (hd : 1 ≤ d) {w : ℕ} (hw : w ≤ d) : (∑ j : Fin d,
      wtZeroProj n d hd w * permMat n d (Equiv.swap ⟨0, hd⟩ j) * wtZeroProj n d hd w) =
      ((d : ℝ) - (w : ℝ)) • wtZeroProj n d hd w := by
  ext f g
  rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]; dsimp only [wtZeroProj]
  set q₀ : Fin d := ⟨0, hd⟩
  simp_rw [mul_diagonal_apply, diagonal_mul_apply, permMat, Matrix.of_apply]
  by_cases hf : wtTuple f = w ∧ f q₀ = 0
  · have hf1 : (if wtTuple f = w ∧ f q₀ = 0 then (1 : ℝ) else 0) = 1 := ite_eq_left hf
    by_cases hfg : f = g
    · subst hfg
      simp only [Matrix.diagonal_apply_eq, hf1, one_mul, mul_one]
      have hiff : ∀ j : Fin d, (f ∘ Equiv.swap q₀ j = f) ↔ f j = 0 := by
        intro j
        constructor
        · intro h
          have h0 := congrFun h q₀
          simpa [Function.comp_apply, hf.2] using h0
        · intro hfj
          funext q
          by_cases hq0 : q = q₀
          · subst hq0; simp [Function.comp_apply, hfj, hf.2]
          · by_cases hqj : q = j
            · subst hqj; simp [Function.comp_apply, hfj, hf.2]
            · simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hq0 hqj]
      have hterm : ∀ j : Fin d,
          (if f ∘ Equiv.swap q₀ j = f then (1 : ℝ) else 0) = if f j = 0 then 1 else 0 := by
        intro j
        by_cases hfj : f j = 0
        · rw [ite_eq_left ((hiff j).2 hfj), ite_eq_left hfj]
        · rw [ite_eq_right (mt (hiff j).1 hfj), ite_eq_right hfj]
      simp_rw [hterm]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin d))) (fun j : Fin d ↦ f j = 0)
      have hneg : (Finset.univ.filter fun j : Fin d ↦ ¬ f j = 0).card = w := by
        simpa [wtTuple] using hf.1
      have hzero_card : (Finset.univ.filter fun j : Fin d ↦ f j = 0).card = d - w := by
        rw [Finset.card_univ, Fintype.card_fin, hneg] at hpart; omega
      rw [hzero_card, Nat.cast_sub hw]
    · simp only [Matrix.diagonal_apply_ne _ hfg, mul_zero]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      by_cases hg : wtTuple g = w ∧ g q₀ = 0
      · have hne_swap : f ∘ Equiv.swap q₀ j ≠ g := by
          intro heq
          apply hfg
          have hfj : f j = 0 := by
            have h0 := congrFun heq q₀
            simpa [Function.comp_apply, hg.2] using h0
          funext q
          rw [← heq, Function.comp_apply]
          by_cases hq0 : q = q₀
          · subst hq0; simp [hfj, hf.2]
          · by_cases hqj : q = j
            · subst hqj; simp [hfj, hf.2]
            · rw [Equiv.swap_apply_of_ne_of_ne hq0 hqj]
        rw [ite_eq_right hne_swap, mul_zero, zero_mul]
      · rw [ite_eq_right hg, mul_zero]
  · have hf0 : (if wtTuple f = w ∧ f q₀ = 0 then (1 : ℝ) else 0) = 0 := ite_eq_right hf
    by_cases hfg : f = g
    · subst hfg
      simp only [Matrix.diagonal_apply_eq, hf0, zero_mul, mul_zero, Finset.sum_const_zero]
    · simp only [Matrix.diagonal_apply_ne _ hfg, hf0, zero_mul, mul_zero, Finset.sum_const_zero]
theorem p2_mul_p1_mul_p2 (n d : ℕ) (hd : 1 ≤ d) {w : ℕ} (hw : w ≤ d) :
    p2Mat n d hd w * p1Mat n d w * p2Mat n d hd w =
      (((d : ℝ) - (w : ℝ)) / (d : ℝ)) • p2Mat n d hd w := by
  have hp2L : p2Mat n d hd w = symStabMat n d hd * wtZeroProj n d hd w := by
    rw [p2Mat, symStabMat_mul_wtZeroProj]
  calc p2Mat n d hd w * p1Mat n d w * p2Mat n d hd w
      = (p2Mat n d hd w * wtProj n d w) * (symAllMat n d * p2Mat n d hd w) := by
          simp only [p1Mat, Matrix.mul_assoc]
    _ = p2Mat n d hd w * ((((1 : ℝ) / (d : ℝ)) • ∑ j : Fin d, permMat n d (Equiv.swap ⟨0, hd⟩ j)) *
            (symStabMat n d hd * p2Mat n d hd w)) := by
          rw [p2Mat_mul_wtProj, symAllMat_eq_avgSwap_mul_symStabMat n d hd, Matrix.mul_assoc]
    _ = ((1 : ℝ) / (d : ℝ)) • (symStabMat n d hd * (∑ j : Fin d,
              wtZeroProj n d hd w * permMat n d (Equiv.swap ⟨0, hd⟩ j) * wtZeroProj n d hd w) *
            symStabMat n d hd) := by
          rw [symStabMat_mul_p2Mat, Matrix.smul_mul, Matrix.mul_smul]
          congr 1
          rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          nth_rw 1 [hp2L]
          rw [p2Mat]; simp only [Matrix.mul_assoc]
    _ = (((d : ℝ) - (w : ℝ)) / (d : ℝ)) • p2Mat n d hd w := by
          rw [sum_wtZeroProj_swap_wtZeroProj n d hd hw, Matrix.mul_smul, Matrix.smul_mul,
            smul_smul, ← hp2L, p2Mat, Matrix.mul_assoc, symStabMat_mul_self, ← p2Mat]
          congr 1
          ring
/-- Unnormalized weight-`w` partial isometry `(wtProj - p2Mat) * p1Mat * p2Mat`. -/
noncomputable def qOp (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  (wtProj n d w - p2Mat n d hd w) * p1Mat n d w * p2Mat n d hd w
theorem wtProj_sub_p2Mat_mul_self (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    (wtProj n d w - p2Mat n d hd w) * (wtProj n d w - p2Mat n d hd w) =
      wtProj n d w - p2Mat n d hd w := by
  rw [sub_mul, mul_sub, mul_sub, wtProj_mul_self, wtProj_mul_p2Mat, p2Mat_mul_wtProj,
    p2Mat_mul_self]
  abel
theorem qOp_transpose_mul_self (n d : ℕ) (hd : 1 ≤ d) {w : ℕ} (hw : w ≤ d) :
    (qOp n d hd w)ᵀ * qOp n d hd w =
      ((((d : ℝ) - (w : ℝ)) / (d : ℝ)) - (((d : ℝ) - (w : ℝ)) / (d : ℝ)) ^ 2) • p2Mat n d hd w := by
  have hqt : (qOp n d hd w)ᵀ = p2Mat n d hd w * p1Mat n d w * (wtProj n d w - p2Mat n d hd w) := by
    simp only [qOp, Matrix.transpose_mul, Matrix.transpose_sub, wtProj_transpose,
      p1Mat_transpose, p2Mat_transpose, Matrix.mul_assoc]
  calc (qOp n d hd w)ᵀ * qOp n d hd w
      = p2Mat n d hd w * p1Mat n d w *
          ((wtProj n d w - p2Mat n d hd w) * (wtProj n d w - p2Mat n d hd w)) *
          p1Mat n d w * p2Mat n d hd w := by
          rw [hqt, qOp]; simp only [Matrix.mul_assoc]
    _ = p2Mat n d hd w * ((p1Mat n d w * wtProj n d w) * p1Mat n d w) * p2Mat n d hd w -
          (p2Mat n d hd w * p1Mat n d w * p2Mat n d hd w) *
            (p1Mat n d w * p2Mat n d hd w) := by
          rw [wtProj_sub_p2Mat_mul_self, mul_sub, sub_mul, sub_mul]; simp only [Matrix.mul_assoc]
    _ = ((((d : ℝ) - (w : ℝ)) / (d : ℝ)) - (((d : ℝ) - (w : ℝ)) / (d : ℝ)) ^ 2) •
          p2Mat n d hd w := by
          rw [p1Mat_mul_wtProj, p1Mat_mul_self, p2_mul_p1_mul_p2 n d hd hw,
            Matrix.smul_mul, ← Matrix.mul_assoc, p2_mul_p1_mul_p2 n d hd hw,
            smul_smul, ← sub_smul]
          congr 1
          ring
/-- Normalized weight-`w` partial isometry mapping `p2Mat` onto its orthogonal partner
  `pAMat`. -/
noncomputable def wOp (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  ((d : ℝ) / √(((d : ℝ) - (w : ℝ)) * (w : ℝ))) • qOp n d hd w
theorem wOp_transpose_mul_self (n d : ℕ) (hd : 1 ≤ d) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) :
    (wOp n d hd w)ᵀ * wOp n d hd w = p2Mat n d hd w := by
  rw [wOp, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    qOp_transpose_mul_self n d hd hwd.le, smul_smul]
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hw_pos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (show 0 < w by omega)
  have hsub_pos : (0 : ℝ) < (d : ℝ) - (w : ℝ) := by
    have : (w : ℝ) < (d : ℝ) := by exact_mod_cast hwd
    linarith
  have hprod_pos : (0 : ℝ) < ((d : ℝ) - (w : ℝ)) * (w : ℝ) := mul_pos hsub_pos hw_pos
  have hsq : √(((d : ℝ) - (w : ℝ)) * (w : ℝ)) ^ 2 = ((d : ℝ) - (w : ℝ)) * (w : ℝ) :=
    Real.sq_sqrt hprod_pos.le
  have hscalar : ((d : ℝ) / √(((d : ℝ) - (w : ℝ)) * (w : ℝ))) *
        ((d : ℝ) / √(((d : ℝ) - (w : ℝ)) * (w : ℝ))) *
        (((d : ℝ) - (w : ℝ)) / (d : ℝ) - (((d : ℝ) - (w : ℝ)) / (d : ℝ)) ^ 2) = 1 := by
    rw [div_mul_div_comm, ← sq (d : ℝ), ← sq √(((d : ℝ) - (w : ℝ)) * (w : ℝ)), hsq]
    have hd_ne : (d : ℝ) ≠ 0 := hd_pos.ne'
    field_simp [hsub_pos.ne', hw_pos.ne', hd_ne]
    ring
  rw [hscalar, one_smul]
theorem wtProj_mul_wOp (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    wtProj n d w * wOp n d hd w = wOp n d hd w := by
  rw [wOp, Matrix.mul_smul, qOp, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_sub,
    wtProj_mul_self, wtProj_mul_p2Mat]
theorem wOp_mul_wtProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    wOp n d hd w * wtProj n d w = wOp n d hd w := by
  rw [wOp, Matrix.smul_mul, qOp, Matrix.mul_assoc, p2Mat_mul_wtProj]
theorem p2Mat_mul_wOp (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : p2Mat n d hd w * wOp n d hd w = 0 := by
  have hz : p2Mat n d hd w * (wtProj n d w - p2Mat n d hd w) = 0 := by
    rw [mul_sub, p2Mat_mul_wtProj, p2Mat_mul_self, sub_self]
  rw [wOp, Matrix.mul_smul, qOp, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hz,
    Matrix.zero_mul, Matrix.zero_mul, smul_zero]
theorem wOp_mul_p2Mat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    wOp n d hd w * p2Mat n d hd w = wOp n d hd w := by
  rw [wOp, Matrix.smul_mul, qOp, Matrix.mul_assoc, p2Mat_mul_self]
theorem wOp_transpose_mul_p2Mat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    (wOp n d hd w)ᵀ * p2Mat n d hd w = 0 := by
  calc (wOp n d hd w)ᵀ * p2Mat n d hd w
      = (p2Mat n d hd w * wOp n d hd w)ᵀ := by rw [Matrix.transpose_mul, p2Mat_transpose]
    _ = 0 := by rw [p2Mat_mul_wOp, Matrix.transpose_zero]
theorem p2Mat_mul_wOp_transpose (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    p2Mat n d hd w * (wOp n d hd w)ᵀ = (wOp n d hd w)ᵀ := by
  calc p2Mat n d hd w * (wOp n d hd w)ᵀ
      = (wOp n d hd w * p2Mat n d hd w)ᵀ := by rw [Matrix.transpose_mul, p2Mat_transpose]
    _ = (wOp n d hd w)ᵀ := by rw [wOp_mul_p2Mat]
theorem wOp_mul_self (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : wOp n d hd w * wOp n d hd w = 0 := by
  calc wOp n d hd w * wOp n d hd w
      = (wOp n d hd w * p2Mat n d hd w) * wOp n d hd w := by rw [wOp_mul_p2Mat]
    _ = wOp n d hd w * (p2Mat n d hd w * wOp n d hd w) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [p2Mat_mul_wOp, Matrix.mul_zero]
/-- Orthogonal partner projector `wOp * (wOp)ᵀ` in weight sector `w`. -/
noncomputable def pAMat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  wOp n d hd w * (wOp n d hd w)ᵀ
theorem pAMat_transpose (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : (pAMat n d hd w)ᵀ = pAMat n d hd w := by
  simp [pAMat, Matrix.transpose_mul]
theorem pAMat_mul_self (n d : ℕ) (hd : 1 ≤ d) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) :
    pAMat n d hd w * pAMat n d hd w = pAMat n d hd w := by
  calc pAMat n d hd w * pAMat n d hd w
      = wOp n d hd w * ((wOp n d hd w)ᵀ * wOp n d hd w) * (wOp n d hd w)ᵀ := by
          simp only [pAMat, Matrix.mul_assoc]
    _ = pAMat n d hd w := by rw [wOp_transpose_mul_self n d hd hw1 hwd, wOp_mul_p2Mat, pAMat]
theorem wtProj_mul_pAMat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    wtProj n d w * pAMat n d hd w = pAMat n d hd w := by
  rw [pAMat, ← Matrix.mul_assoc, wtProj_mul_wOp]
theorem pAMat_mul_wtProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    pAMat n d hd w * wtProj n d w = pAMat n d hd w := by
  calc pAMat n d hd w * wtProj n d w
      = (wtProj n d w * pAMat n d hd w)ᵀ := by
          rw [Matrix.transpose_mul, pAMat_transpose, wtProj_transpose]
    _ = pAMat n d hd w := by rw [wtProj_mul_pAMat, pAMat_transpose]
theorem pAMat_mul_p2Mat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : pAMat n d hd w * p2Mat n d hd w = 0 := by
  rw [pAMat, Matrix.mul_assoc, wOp_transpose_mul_p2Mat, Matrix.mul_zero]
theorem p2Mat_mul_pAMat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : p2Mat n d hd w * pAMat n d hd w = 0 := by
  rw [pAMat, ← Matrix.mul_assoc, p2Mat_mul_wOp, Matrix.zero_mul]
theorem pAMat_mul_wOp (n d : ℕ) (hd : 1 ≤ d) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) :
    pAMat n d hd w * wOp n d hd w = wOp n d hd w := by
  rw [pAMat, Matrix.mul_assoc, wOp_transpose_mul_self n d hd hw1 hwd, wOp_mul_p2Mat]
theorem wOp_mul_pAMat (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) : wOp n d hd w * pAMat n d hd w = 0 := by
  rw [pAMat, ← Matrix.mul_assoc, wOp_mul_self, Matrix.zero_mul]
theorem pAMat_mul_wOp_transpose (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) :
    pAMat n d hd w * (wOp n d hd w)ᵀ = 0 := by
  calc pAMat n d hd w * (wOp n d hd w)ᵀ
      = (wOp n d hd w * pAMat n d hd w)ᵀ := by rw [Matrix.transpose_mul, pAMat_transpose]
    _ = 0 := by rw [wOp_mul_pAMat, Matrix.transpose_zero]
theorem wOp_transpose_mul_pAMat (n d : ℕ) (hd : 1 ≤ d) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) :
    (wOp n d hd w)ᵀ * pAMat n d hd w = (wOp n d hd w)ᵀ := by
  calc (wOp n d hd w)ᵀ * pAMat n d hd w
      = (pAMat n d hd w * wOp n d hd w)ᵀ := by rw [Matrix.transpose_mul, pAMat_transpose]
    _ = (wOp n d hd w)ᵀ := by rw [pAMat_mul_wOp n d hd hw1 hwd]
/-- Weight-`w` `SO(2)` rotation block on `(pAMat, p2Mat)` parameterized by `p: ℤ × ℤ`. -/
noncomputable def uBlock (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) (p : ℤ × ℤ) :
    Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  let X := pAMat n d hd w + p2Mat n d hd w
  let Y := -wOp n d hd w + (wOp n d hd w)ᵀ
  let ca : ℝ := (tcRatCos ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
  let sa : ℝ := (tcRatSin ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
  (wtProj n d w - X) + ca • X + sa • Y
theorem wtProj_mul_uBlock (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) (p : ℤ × ℤ) :
    wtProj n d w * uBlock n d hd w p = uBlock n d hd w p := by
  unfold uBlock; dsimp only
  have hX : wtProj n d w * (pAMat n d hd w + p2Mat n d hd w) = pAMat n d hd w + p2Mat n d hd w := by
    rw [mul_add, wtProj_mul_pAMat, wtProj_mul_p2Mat]
  have hWt : wtProj n d w * (wOp n d hd w)ᵀ = (wOp n d hd w)ᵀ := by
    calc wtProj n d w * (wOp n d hd w)ᵀ
        = (wOp n d hd w * wtProj n d w)ᵀ := by rw [Matrix.transpose_mul, wtProj_transpose]
      _ = (wOp n d hd w)ᵀ := by rw [wOp_mul_wtProj]
  have hY : wtProj n d w * (-wOp n d hd w + (wOp n d hd w)ᵀ) = -wOp n d hd w + (wOp n d hd w)ᵀ := by
    rw [mul_add, Matrix.mul_neg, wtProj_mul_wOp, hWt]
  rw [mul_add, mul_add, mul_sub, wtProj_mul_self, hX, Matrix.mul_smul, hX, Matrix.mul_smul, hY]
theorem uBlock_mul_wtProj (n d : ℕ) (hd : 1 ≤ d) (w : ℕ) (p : ℤ × ℤ) :
    uBlock n d hd w p * wtProj n d w = uBlock n d hd w p := by
  unfold uBlock; dsimp only
  have hX : (pAMat n d hd w + p2Mat n d hd w) * wtProj n d w = pAMat n d hd w + p2Mat n d hd w := by
    rw [add_mul, pAMat_mul_wtProj, p2Mat_mul_wtProj]
  have hWt : (wOp n d hd w)ᵀ * wtProj n d w = (wOp n d hd w)ᵀ := by
    calc (wOp n d hd w)ᵀ * wtProj n d w
        = (wtProj n d w * wOp n d hd w)ᵀ := by rw [Matrix.transpose_mul, wtProj_transpose]
      _ = (wOp n d hd w)ᵀ := by rw [wtProj_mul_wOp]
  have hY : (-wOp n d hd w + (wOp n d hd w)ᵀ) * wtProj n d w = -wOp n d hd w + (wOp n d hd w)ᵀ := by
    rw [add_mul, Matrix.neg_mul, wOp_mul_wtProj, hWt]
  rw [add_mul, add_mul, sub_mul, wtProj_mul_self, hX, Matrix.smul_mul, hX, Matrix.smul_mul, hY]
theorem uBlock_orthogonal (n d : ℕ) (hd : 1 ≤ d) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) (p : ℤ × ℤ) :
    (uBlock n d hd w p)ᵀ * uBlock n d hd w p = wtProj n d w ∧
      uBlock n d hd w p * (uBlock n d hd w p)ᵀ = wtProj n d w := by
  set P := wtProj n d w
  set A := pAMat n d hd w
  set B := p2Mat n d hd w
  set W := wOp n d hd w
  set X := A + B
  set Y := -W + Wᵀ
  set ca : ℝ := (tcRatCos ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
  set sa : ℝ := (tcRatSin ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
  have hcs : ca ^ 2 + sa ^ 2 = 1 := tcRatCos_sq_add_sin_sq_real ((p.1 : ℚ) / (p.2 : ℚ))
  have hXX : X * X = X := by
    dsimp [X]
    rw [add_mul, mul_add, mul_add, pAMat_mul_self n d hd hw1 hwd, pAMat_mul_p2Mat,
      p2Mat_mul_pAMat, p2Mat_mul_self]
    abel
  have hXY : X * Y = Y := by
    dsimp [X, Y]
    rw [mul_add, add_mul, add_mul, Matrix.mul_neg, Matrix.mul_neg, pAMat_mul_wOp n d hd hw1 hwd,
      p2Mat_mul_wOp, pAMat_mul_wOp_transpose, p2Mat_mul_wOp_transpose]
    abel
  have hYX : Y * X = Y := by
    dsimp [X, Y]
    rw [add_mul, mul_add, mul_add, Matrix.neg_mul, Matrix.neg_mul, wOp_mul_pAMat, wOp_mul_p2Mat,
      wOp_transpose_mul_pAMat n d hd hw1 hwd, wOp_transpose_mul_p2Mat]
    abel
  have hWtWt : Wᵀ * Wᵀ = 0 := by
    calc Wᵀ * Wᵀ = (W * W)ᵀ := (Matrix.transpose_mul W W).symm
      _ = 0 := by rw [wOp_mul_self, Matrix.transpose_zero]
  have hYY : Y * Y = -X := by
    dsimp [X, Y]
    rw [add_mul, mul_add, mul_add, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_neg,
      neg_neg, wOp_mul_self, wOp_transpose_mul_self n d hd hw1 hwd, hWtWt]
    change (0 - pAMat n d hd w) + (-B + 0) = -(A + B); dsimp [A]
    abel
  have hPX : P * X = X := by dsimp [P, X]; rw [mul_add, wtProj_mul_pAMat, wtProj_mul_p2Mat]
  have hXP : X * P = X := by dsimp [P, X]; rw [add_mul, pAMat_mul_wtProj, p2Mat_mul_wtProj]
  have hRX : (P - X) * X = 0 := by rw [sub_mul, hPX, hXX, sub_self]
  have hXR : X * (P - X) = 0 := by rw [mul_sub, hXP, hXX, sub_self]
  have hRY : (P - X) * Y = 0 := by rw [← hXY, ← Matrix.mul_assoc, hRX, Matrix.zero_mul]
  have hYR : Y * (P - X) = 0 := by rw [← hYX, Matrix.mul_assoc, hXR, Matrix.mul_zero]
  have hRR : (P - X) * (P - X) = P - X := by
    rw [sub_mul, hXR, sub_zero, mul_sub, wtProj_mul_self, hPX]
  have hut : (uBlock n d hd w p)ᵀ = (P - X) + ca • X - sa • Y := by
    have hXt : Xᵀ = X := by dsimp [X]; rw [Matrix.transpose_add, pAMat_transpose, p2Mat_transpose]
    have hYt : Yᵀ = -Y := by
      dsimp [Y]; rw [Matrix.transpose_add, Matrix.transpose_neg, Matrix.transpose_transpose]
      abel
    change (((P - X) + ca • X + sa • Y)ᵀ) = _
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_sub, wtProj_transpose, hXt,
      Matrix.transpose_smul, hXt, Matrix.transpose_smul, hYt, smul_neg, ← sub_eq_add_neg]
  have hgen : ∀ s : ℝ, ca ^ 2 + s ^ 2 = 1 →
      ((P - X) + ca • X - s • Y) * ((P - X) + ca • X + s • Y) = P := by
    intro s hs
    have hRM : (P - X) * (ca • X + s • Y) = 0 := by
      rw [mul_add, Matrix.mul_smul, hRX, Matrix.mul_smul, hRY, smul_zero, smul_zero, add_zero]
    have hMR : (ca • X - s • Y) * (P - X) = 0 := by
      rw [sub_mul, Matrix.smul_mul, hXR, Matrix.smul_mul, hYR, smul_zero, smul_zero, sub_zero]
    have hMM : (ca • X - s • Y) * (ca • X + s • Y) = X := by
      rw [sub_mul, mul_add, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
        smul_smul, smul_smul, smul_smul, smul_smul, hXX, hXY, hYX, hYY, smul_neg]
      have hmid : (ca * ca) • X + (ca * s) • Y - ((s * ca) • Y + -((s * s) • X)) =
          (ca ^ 2 + s ^ 2) • X := by
        rw [mul_comm s ca, sub_add_eq_sub_sub, sub_neg_eq_add, add_sub_assoc, sub_self, add_zero,
          ← add_smul, ← sq, ← sq]
      rw [hmid, hs, one_smul]
    calc ((P - X) + ca • X - s • Y) * ((P - X) + ca • X + s • Y)
        = ((P - X) + (ca • X - s • Y)) * ((P - X) + (ca • X + s • Y)) := by
            rw [add_sub_assoc, add_assoc]
      _ = (P - X) * (P - X) + (P - X) * (ca • X + s • Y) +
            ((ca • X - s • Y) * (P - X) + (ca • X - s • Y) * (ca • X + s • Y)) := by
            rw [add_mul, mul_add (P - X), mul_add (ca • X - s • Y)]
      _ = P := by rw [hRR, hRM, hMR, hMM, add_zero, zero_add, sub_add_cancel]
  constructor
  · rw [hut]; exact hgen sa hcs
  · rw [hut]; change ((P - X) + ca • X + sa • Y) * ((P - X) + ca • X - sa • Y) = P
    have h1 := hgen (-sa) (by linear_combination hcs)
    rw [neg_smul, sub_neg_eq_add, ← sub_eq_add_neg] at h1; exact h1
/-- Weight-sector component of `uCoreMat`: identity on `w = 0` or `w ≥ d`, and `uBlock` on
  `1 ≤ w < d`. -/
noncomputable def uWeightBlock (n d : ℕ) (hd : 1 ≤ d) (uRow : ℕ → ℤ × ℤ) (w : ℕ) :
    Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  if w = 0 ∨ d ≤ w then wtProj n d w else uBlock n d hd w (uRow (w - 1))
theorem wtProj_mul_uWeightBlock (n d : ℕ) (hd : 1 ≤ d) (uRow : ℕ → ℤ × ℤ) (w : ℕ) :
    wtProj n d w * uWeightBlock n d hd uRow w = uWeightBlock n d hd uRow w := by
  unfold uWeightBlock
  split_ifs
  · exact wtProj_mul_self n d w
  · exact wtProj_mul_uBlock n d hd w (uRow (w - 1))
theorem uWeightBlock_mul_wtProj (n d : ℕ) (hd : 1 ≤ d) (uRow : ℕ → ℤ × ℤ) (w : ℕ) :
    uWeightBlock n d hd uRow w * wtProj n d w = uWeightBlock n d hd uRow w := by
  unfold uWeightBlock
  split_ifs
  · exact wtProj_mul_self n d w
  · exact uBlock_mul_wtProj n d hd w (uRow (w - 1))
theorem uWeightBlock_orthogonal (n d : ℕ) (hd : 1 ≤ d) (uRow : ℕ → ℤ × ℤ) (w : ℕ) :
    (uWeightBlock n d hd uRow w)ᵀ * uWeightBlock n d hd uRow w = wtProj n d w ∧
      uWeightBlock n d hd uRow w * (uWeightBlock n d hd uRow w)ᵀ = wtProj n d w := by
  unfold uWeightBlock
  by_cases h : w = 0 ∨ d ≤ w
  · simp only [h, ↓reduceIte, wtProj_transpose, wtProj_mul_self, and_self]
  · simp only [h, ↓reduceIte]
    have hw1 : 1 ≤ w := by omega
    have hwd : w < d := by omega
    exact uBlock_orthogonal n d hd hw1 hwd (uRow (w - 1))
/-- Sum of orthogonal weight-sector blocks `0.. d` on `TupleSpace n d`. -/
noncomputable def uCoreMat (n d : ℕ) (hd : 1 ≤ d) (uRow : ℕ → ℤ × ℤ) :
    Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  ∑ w ∈ Finset.range (d + 1), uWeightBlock n d hd uRow w
theorem uCoreMat_orthogonal (n d : ℕ) (hd : 1 ≤ d) (uRow : ℕ → ℤ × ℤ) :
    (uCoreMat n d hd uRow)ᵀ * uCoreMat n d hd uRow = 1 ∧
      uCoreMat n d hd uRow * (uCoreMat n d hd uRow)ᵀ = 1 := by
  unfold uCoreMat; rw [Matrix.transpose_sum, Finset.sum_mul, Finset.sum_mul]
  constructor
  · trans ∑ w₁ ∈ Finset.range (d + 1), wtProj n d w₁
    · refine Finset.sum_congr rfl fun w₁ _ ↦ ?_; rw [Finset.mul_sum, Finset.sum_eq_single w₁]
      · exact (uWeightBlock_orthogonal n d hd uRow w₁).1
      · intro w₂ _ hne
        calc (uWeightBlock n d hd uRow w₁)ᵀ * uWeightBlock n d hd uRow w₂
            = (wtProj n d w₁ * uWeightBlock n d hd uRow w₁)ᵀ *
                (wtProj n d w₂ * uWeightBlock n d hd uRow w₂) := by
                rw [wtProj_mul_uWeightBlock, wtProj_mul_uWeightBlock]
          _ = (uWeightBlock n d hd uRow w₁)ᵀ *
                (wtProj n d w₁ * wtProj n d w₂) * uWeightBlock n d hd uRow w₂ := by
                rw [Matrix.transpose_mul, wtProj_transpose]; simp only [Matrix.mul_assoc]
          _ = 0 := by rw [wtProj_mul_of_ne n d hne.symm, Matrix.mul_zero, Matrix.zero_mul]
      · intro hm; exact (hm (by assumption)).elim
    · exact sum_wtProj n d
  · trans ∑ w₁ ∈ Finset.range (d + 1), wtProj n d w₁
    · refine Finset.sum_congr rfl fun w₁ _ ↦ ?_; rw [Finset.mul_sum, Finset.sum_eq_single w₁]
      · exact (uWeightBlock_orthogonal n d hd uRow w₁).2
      · intro w₂ _ hne
        calc uWeightBlock n d hd uRow w₁ * (uWeightBlock n d hd uRow w₂)ᵀ
            = (uWeightBlock n d hd uRow w₁ * wtProj n d w₁) *
                (uWeightBlock n d hd uRow w₂ * wtProj n d w₂)ᵀ := by
                rw [uWeightBlock_mul_wtProj, uWeightBlock_mul_wtProj]
          _ = uWeightBlock n d hd uRow w₁ *
                (wtProj n d w₁ * wtProj n d w₂) * (uWeightBlock n d hd uRow w₂)ᵀ := by
                rw [Matrix.transpose_mul, wtProj_transpose]; simp only [Matrix.mul_assoc]
          _ = 0 := by rw [wtProj_mul_of_ne n d hne.symm, Matrix.mul_zero, Matrix.zero_mul]
      · intro hm; exact (hm (by assumption)).elim
    · exact sum_wtProj n d
/-- Hadamard-conjugated real orthogonal intertwiner matrix on `TupleSpace n d`. -/
noncomputable def tcIntertwinerRealMat (n d : ℕ) (uRow : ℕ → ℤ × ℤ) :
    Matrix (TupleSpace n d) (TupleSpace n d) ℝ :=
  if hd : 1 ≤ d then hProdMat n d * uCoreMat n d hd uRow * hProdMat n d else 1
theorem tcIntertwinerRealMat_orthogonal (n d : ℕ) (uRow : ℕ → ℤ × ℤ) :
    (tcIntertwinerRealMat n d uRow)ᵀ * tcIntertwinerRealMat n d uRow = 1 ∧
      tcIntertwinerRealMat n d uRow * (tcIntertwinerRealMat n d uRow)ᵀ = 1 := by
  unfold tcIntertwinerRealMat
  by_cases hd : 1 ≤ d
  · simp only [hd, ↓reduceDIte]; rcases uCoreMat_orthogonal n d hd uRow with ⟨h1, h2⟩
    have hHt : (hProdMat n d)ᵀ = hProdMat n d := hProdMat_transpose n d
    have hHH : hProdMat n d * hProdMat n d = 1 := hProdMat_mul_self n d
    constructor
    · calc (hProdMat n d * uCoreMat n d hd uRow * hProdMat n d)ᵀ *
            (hProdMat n d * uCoreMat n d hd uRow * hProdMat n d)
          = hProdMat n d * (uCoreMat n d hd uRow)ᵀ * (hProdMat n d * hProdMat n d) *
              uCoreMat n d hd uRow * hProdMat n d := by
              simp only [Matrix.transpose_mul, hHt, Matrix.mul_assoc]
        _ = hProdMat n d * ((uCoreMat n d hd uRow)ᵀ * uCoreMat n d hd uRow) *
              hProdMat n d := by
              rw [hHH, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hHH]
    · calc (hProdMat n d * uCoreMat n d hd uRow * hProdMat n d) *
            (hProdMat n d * uCoreMat n d hd uRow * hProdMat n d)ᵀ
          = hProdMat n d * uCoreMat n d hd uRow * (hProdMat n d * hProdMat n d) *
              (uCoreMat n d hd uRow)ᵀ * hProdMat n d := by
              simp only [Matrix.transpose_mul, hHt, Matrix.mul_assoc]
        _ = hProdMat n d * (uCoreMat n d hd uRow * (uCoreMat n d hd uRow)ᵀ) *
              hProdMat n d := by
              rw [hHH, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, hHH]
  · simp [hd]
end TensorConveyorBasis2d
/-- Zero-oracle target-independent real orthogonal intertwiner on `n * d` qubits (`d`
  registers
  of `n` qubits, with `localMemSlotReg n d 0` as the active Grover head register and
  `localMemSlotReg n d 1.. d - 1` as passive storage registers), parameterized by
  stereographic
  rational pairs `uRow: ℕ → ℤ × ℤ`. -/
noncomputable def tcIntertwinerUnitary (n d : ℕ) (uRow : ℕ → ℤ × ℤ) : Unitary (2 ^ (n * d)) :=
  ⟨TensorConveyorBasis2d.liftTupleRealMat (TensorConveyorBasis2d.tcIntertwinerRealMat n d uRow),
  TensorConveyorBasis2d.liftTupleRealMat_mem_unitaryGroup
  (TensorConveyorBasis2d.tcIntertwinerRealMat_orthogonal n d uRow).1
  (TensorConveyorBasis2d.tcIntertwinerRealMat_orthogonal n d uRow).2⟩
theorem isRealMatrix_tcIntertwinerUnitary (n d : ℕ) (uRow : ℕ → ℤ × ℤ) :
    IsRealMatrix (tcIntertwinerUnitary n d uRow).1 :=
  TensorConveyorBasis2d.isRealMatrix_liftTupleRealMat _
/-- Single coherent `TensorConveyor` pulse on `n * d` qubits: `K_blk` Grover iterations on
  subregister `0` followed by `tcIntertwinerUnitary n d uRow`. -/
noncomputable def tcSlotPulseUnitary (n d : ℕ) (hd : 1 ≤ d)
    (R : Finset (Fin (2 ^ n))) (K_blk : ℕ) (uRow : ℕ → ℤ × ℤ) : Unitary (2 ^ (n * d)) :=
  tcIntertwinerUnitary n d uRow *
    (localMemSlotReg n d ⟨0, hd⟩).embedUnitary (groverStepUnitary R ^ K_blk)
/-- Cumulative `t`-pulse `TensorConveyor` unitary (`t` pulses `0.. t - 1`) on `n * d`
  qubits. -/
noncomputable def tcSlotConveyorUnitary (n d : ℕ) (hd : 1 ≤ d)
    (R : Finset (Fin (2 ^ n))) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) : ℕ → Unitary (2 ^ (n * d))
  | 0 => 1
  | t + 1 => tcSlotPulseUnitary n d hd R K_blk (uFn t) * tcSlotConveyorUnitary n d hd R K_blk uFn t
/-- Single-slot `n * d`-qubit pure state after preparing `|+⟩^{⊗ (n * d)}` and applying
  `steps`
  pulses of `tcSlotPulseUnitary`. -/
noncomputable def tcSlotConveyorVec (n d : ℕ) (hd : 1 ≤ d)
    (R : Finset (Fin (2 ^ n))) (K_blk : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ) :
    Fin (2 ^ (n * d)) → ℂ :=
  (tcSlotConveyorUnitary n d hd R K_blk uFn steps).1 *ᵥ (hadamardUnitary.1 *ᵥ Pi.single 0 1)
namespace TensorConveyorBasis2d
/- ## 3. Single-Register `(uVec, mVec, sVec, pVec)` & `2d`-Subspace Evolution -/
/-- Normalized uniform vector on unmarked basis states `Rᶜ ⊆ Fin (2 ^ n)`. -/
noncomputable def uVec {n : ℕ} (R : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) : ℝ :=
  if x ∈ R then 0 else 1 / √((2 ^ n : ℝ) - (R.card : ℝ))
/-- Normalized uniform vector on marked basis states `R ⊆ Fin (2 ^ n)`. -/
noncomputable def mVec {n : ℕ} (R : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) : ℝ :=
  if x ∈ R then 1 / √(R.card : ℝ) else 0
/-- Half-step Grover angle `α = arcsin(√|R| / √(2^n))` (`θ₁ = 2α`). -/
noncomputable def alphaAngle (n : ℕ) (R : Finset (Fin (2 ^ n))) : ℝ :=
  Real.arcsin (√(R.card : ℝ) / √(2 ^ n : ℝ))
/-- Uniform superposition `(1 / √(2^n),..., 1 / √(2^n))` on `Fin (2 ^ n)`. -/
noncomputable def sVec (n : ℕ) (_ : Fin (2 ^ n)) : ℝ := 1 / √(2 ^ n : ℝ)
/-- Unit vector in `span{uVec R, mVec R}` orthogonal to `sVec n`. -/
noncomputable def pVec {n : ℕ} (R : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) : ℝ :=
  -Real.sin (alphaAngle n R) * uVec R x + Real.cos (alphaAngle n R) * mVec R x
theorem sin_cos_alphaAngle {n : ℕ} {R : Finset (Fin (2 ^ n))} (hrN : R.card < 2 ^ n) :
    Real.sin (alphaAngle n R) = √(R.card : ℝ) / √(2 ^ n : ℝ) ∧
      Real.cos (alphaAngle n R) = √((2 ^ n : ℝ) - (R.card : ℝ)) / √(2 ^ n : ℝ) := by
  have hN_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have hr_nn : (0 : ℝ) ≤ (R.card : ℝ) := by positivity
  have hNr_nn : (0 : ℝ) ≤ (2 ^ n : ℝ) - (R.card : ℝ) := by
    have : (R.card : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hrN
    linarith
  set x : ℝ := √(R.card : ℝ) / √(2 ^ n : ℝ)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := (div_le_one (Real.sqrt_pos.2 hN_pos)).2
    (Real.sqrt_le_sqrt (by exact_mod_cast hrN.le))
  have hsin : Real.sin (alphaAngle n R) = x := Real.sin_arcsin (by linarith) hx1; refine ⟨hsin, ?_⟩
  have hα0 : 0 ≤ alphaAngle n R := Real.arcsin_nonneg.2 hx0
  have hα1 : alphaAngle n R ≤ π / 2 := Real.arcsin_le_pi_div_two x
  have hcos_nn : 0 ≤ Real.cos (alphaAngle n R) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hα1⟩
  have hsq : Real.cos (alphaAngle n R) ^ 2 =
      (√((2 ^ n : ℝ) - (R.card : ℝ)) / √(2 ^ n : ℝ)) ^ 2 := by
    have hcs := Real.cos_sq_add_sin_sq (alphaAngle n R); rw [hsin] at hcs
    have hx_sq : x ^ 2 = (R.card : ℝ) / (2 ^ n : ℝ) := by
      dsimp [x]; rw [div_pow, Real.sq_sqrt hr_nn, Real.sq_sqrt hN_pos.le]
    have hrhs_sq : (√((2 ^ n : ℝ) - (R.card : ℝ)) / √(2 ^ n : ℝ)) ^ 2 =
        ((2 ^ n : ℝ) - (R.card : ℝ)) / (2 ^ n : ℝ) := by
      rw [div_pow, Real.sq_sqrt hNr_nn, Real.sq_sqrt hN_pos.le]
    rw [hrhs_sq]; have hN_ne : (2 ^ n : ℝ) ≠ 0 := hN_pos.ne'
    have hsum1 : ((2 ^ n : ℝ) - (R.card : ℝ)) / (2 ^ n : ℝ) + (R.card : ℝ) / (2 ^ n : ℝ) = 1 := by
      field_simp [hN_ne]; ring
    linarith
  calc Real.cos (alphaAngle n R)
      = √(Real.cos (alphaAngle n R) ^ 2) := (Real.sqrt_sq hcos_nn).symm
    _ = √((√((2 ^ n : ℝ) - (R.card : ℝ)) / √(2 ^ n : ℝ)) ^ 2) := by rw [hsq]
    _ = √((2 ^ n : ℝ) - (R.card : ℝ)) / √(2 ^ n : ℝ) := Real.sqrt_sq (by positivity)
theorem sVec_eq_comb {n : ℕ} {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card)
    (hrN : R.card < 2 ^ n) (x : Fin (2 ^ n)) : sVec n x = Real.cos (alphaAngle n R) * uVec R x +
      Real.sin (alphaAngle n R) * mVec R x := by
  rcases sin_cos_alphaAngle hrN with ⟨hsin, hcos⟩; rw [hsin, hcos, sVec, uVec, mVec]
  by_cases hx : x ∈ R
  · simp only [hx, ↓reduceIte, mul_zero, zero_add]
    have hr_pos : (0 : ℝ) < (R.card : ℝ) := by exact_mod_cast hr1
    have hne : √(R.card : ℝ) ≠ 0 := (Real.sqrt_pos.2 hr_pos).ne'
    field_simp [hne]
  · simp only [hx, ↓reduceIte, mul_zero, add_zero]
    have hNr_pos : (0 : ℝ) < (2 ^ n : ℝ) - (R.card : ℝ) := by
      have : (R.card : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hrN
      linarith
    have hne : √((2 ^ n : ℝ) - (R.card : ℝ)) ≠ 0 := (Real.sqrt_pos.2 hNr_pos).ne'
    field_simp [hne]
theorem uVec_mVec_orthonormal {n : ℕ} {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card)
    (hrN : R.card < 2 ^ n) : dotProduct (uVec R) (uVec R) = 1 ∧ dotProduct (mVec R) (mVec R) = 1 ∧
      dotProduct (uVec R) (mVec R) = 0 := by
  have hr_pos : (0 : ℝ) < (R.card : ℝ) := by exact_mod_cast hr1
  have hNr_pos : (0 : ℝ) < (2 ^ n : ℝ) - (R.card : ℝ) := by
    have : (R.card : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hrN
    linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [dotProduct, uVec]
    have hterm : ∀ x : Fin (2 ^ n), (if x ∈ R then (0 : ℝ) else 1 / √((2 ^ n : ℝ) - (R.card : ℝ))) *
          (if x ∈ R then 0 else 1 / √((2 ^ n : ℝ) - (R.card : ℝ))) =
        if x ∉ R then 1 / ((2 ^ n : ℝ) - (R.card : ℝ)) else 0 := by
      intro x
      by_cases hx : x ∈ R
      · simp [hx]
      · simp only [hx, ↓reduceIte, not_false_eq_true]
        rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hNr_pos.le]
    simp_rw [hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 ^ n)))) (· ∈ R)
    have hmem_R : (Finset.univ.filter (· ∈ R)).card = R.card := by
      have : Finset.univ.filter (· ∈ R) = R := by ext x; simp
      rw [this]
    have hcard_c : (Finset.univ.filter (· ∉ R)).card = 2 ^ n - R.card := by
      rw [Finset.card_univ, Fintype.card_fin, hmem_R] at hpart; omega
    rw [hcard_c, Nat.cast_sub hrN.le, Nat.cast_pow, Nat.cast_ofNat, mul_one_div_cancel hNr_pos.ne']
  · simp only [dotProduct, mVec]
    have hterm : ∀ x : Fin (2 ^ n), (if x ∈ R then (1 / √(R.card : ℝ)) else 0) *
          (if x ∈ R then (1 / √(R.card : ℝ)) else 0) = if x ∈ R then 1 / (R.card : ℝ) else 0 := by
      intro x
      by_cases hx : x ∈ R
      · simp only [hx, ↓reduceIte]; rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hr_pos.le]
      · simp [hx]
    simp_rw [hterm, ← Finset.sum_filter]
    have hfilt : Finset.univ.filter (· ∈ R) = R := by ext x; simp
    rw [hfilt, Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel hr_pos.ne']
  · simp only [dotProduct, uVec, mVec]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    by_cases hx : x ∈ R <;> simp [hx]
theorem sVec_pVec_orthonormal {n : ℕ} {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card)
    (hrN : R.card < 2 ^ n) : dotProduct (sVec n) (sVec n) = 1 ∧ dotProduct (pVec R) (pVec R) = 1 ∧
      dotProduct (sVec n) (pVec R) = 0 := by
  rcases uVec_mVec_orthonormal hr1 hrN with ⟨huu, hmm, hum⟩
  have hmu : dotProduct (mVec R) (uVec R) = 0 := by rw [dotProduct_comm, hum]
  have hs_eq : sVec n = Real.cos (alphaAngle n R) • uVec R +
      Real.sin (alphaAngle n R) • mVec R := by
    funext x; exact sVec_eq_comb hr1 hrN x
  have hp_eq : pVec R = (-Real.sin (alphaAngle n R)) • uVec R +
      Real.cos (alphaAngle n R) • mVec R := by
    funext x; rfl
  have hcs := Real.cos_sq_add_sin_sq (alphaAngle n R); refine ⟨?_, ?_, ?_⟩
  · rw [hs_eq]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      huu, hmm, hum, hmu]
    linear_combination hcs
  · rw [hp_eq]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      huu, hmm, hum, hmu]
    linear_combination hcs
  · rw [hs_eq, hp_eq]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      huu, hmm, hum, hmu]
    ring
theorem sum_sVec_and_pVec {n : ℕ} {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card)
    (hrN : R.card < 2 ^ n) : (∑ x : Fin (2 ^ n), sVec n x) = √(2 ^ n : ℝ) ∧
      (∑ x : Fin (2 ^ n), pVec R x) = 0 := by
  constructor
  · simp only [sVec, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simpa [div_eq_mul_inv] using Real.div_sqrt (x := (2 ^ n : ℝ))
  · have horth : (∑ x : Fin (2 ^ n), (1 / √(2 ^ n : ℝ)) * pVec R x) = 0 :=
      (sVec_pVec_orthonormal hr1 hrN).2.2
    rw [← Finset.mul_sum] at horth; exact (mul_eq_zero.1 horth).resolve_left (by positivity)
theorem realHadamard_mulVec_single_zero (n : ℕ) : realHadamard n *ᵥ Pi.single 0 1 = sVec n := by
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  apply Complex.ofReal_injective
  rw [ofReal_realHadamard, hadamardMatrix_apply_zero, sVec]; push_cast; rfl
theorem realHadamard_mulVec_sVec (n : ℕ) : realHadamard n *ᵥ sVec n = Pi.single 0 1 := by
  rw [← realHadamard_mulVec_single_zero, Matrix.mulVec_mulVec, realHadamard_mul_self,
    Matrix.one_mulVec]
theorem realHadamard_mulVec_pVec_zero {n : ℕ} {R : Finset (Fin (2 ^ n))}
    (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n) : (realHadamard n *ᵥ pVec R) 0 = 0 := by
  have hrow : ∀ j : Fin (2 ^ n), realHadamard n 0 j = 1 / √(2 ^ n : ℝ) := by
    intro j
    apply Complex.ofReal_injective
    rw [ofReal_realHadamard, hadamardMatrix_zero_apply]; push_cast; rfl
  simp only [Matrix.mulVec, dotProduct, hrow, ← Finset.mul_sum,
    (sum_sVec_and_pVec hr1 hrN).2, mul_zero]
theorem groverStepUnitary_mulVec_comb {n : ℕ} {R : Finset (Fin (2 ^ n))}
    (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n) (a₀ a₁ : ℝ) : let θ₁ := tcTheta1Real (2 ^ n) R.card
    (groverStepUnitary R).1 *ᵥ (fun x ↦ ((a₀ * sVec n x + a₁ * pVec R x : ℝ) : ℂ)) =
      fun x ↦ (((Real.cos θ₁ * a₀ - Real.sin θ₁ * a₁) * sVec n x +
        (Real.sin θ₁ * a₀ + Real.cos θ₁ * a₁) * pVec R x : ℝ) : ℂ) := by
  intro θ₁
  set α := alphaAngle n R
  have hθ₁ : θ₁ = 2 * α := by simp [θ₁, tcTheta1Real, α, alphaAngle]
  have hc2 : Real.cos θ₁ = Real.cos α ^ 2 - Real.sin α ^ 2 := by rw [hθ₁, Real.cos_two_mul']
  have hs2 : Real.sin θ₁ = 2 * Real.sin α * Real.cos α := by rw [hθ₁, Real.sin_two_mul]
  have hcs := Real.cos_sq_add_sin_sq α
  set b₀ : ℝ := Real.cos θ₁ * a₀ - Real.sin θ₁ * a₁
  set b₁ : ℝ := -(Real.sin θ₁ * a₀ + Real.cos θ₁ * a₁)
  have horacle : setOracleMatrix R *ᵥ (fun x ↦ ((a₀ * sVec n x + a₁ * pVec R x : ℝ) : ℂ)) =
        fun x ↦ ((b₀ * sVec n x + b₁ * pVec R x : ℝ) : ℂ) := by
    funext x
    rw [setOracleMatrix_mulVec]; have hsx := sVec_eq_comb hr1 hrN x
    by_cases hx : x ∈ R
    · simp only [hx, ↓reduceIte]
      have hu0 : uVec R x = 0 := by simp [uVec, hx]
      have hp_x : pVec R x = Real.cos α * mVec R x := by simp [pVec, α, hu0]
      have hs_x : sVec n x = Real.sin α * mVec R x := by rw [hsx]; simp [α, hu0]
      rw [hs_x, hp_x, ← Complex.ofReal_neg]
      congr 1
      dsimp [b₀, b₁]; rw [hc2, hs2]
      linear_combination (a₀ * Real.sin α + a₁ * Real.cos α) * mVec R x * hcs
    · simp only [hx, ↓reduceIte]
      have hm0 : mVec R x = 0 := by simp [mVec, hx]
      have hp_x : pVec R x = -Real.sin α * uVec R x := by simp [pVec, α, hm0]
      have hs_x : sVec n x = Real.cos α * uVec R x := by rw [hsx]; simp [α, hm0]
      rw [hs_x, hp_x]
      congr 1
      dsimp [b₀, b₁]; rw [hc2, hs2]
      linear_combination (-a₀ * Real.cos α + a₁ * Real.sin α) * uVec R x * hcs
  have hcoe : (groverStepUnitary R).1 = Grover.diffuserMatrix * setOracleMatrix R := by
    rw [groverStepUnitary, Submonoid.coe_mul, Grover.diffuserUnitary_coe, setOracleUnitary]
  rw [hcoe, ← Matrix.mulVec_mulVec, horacle]
  funext x
  rw [Grover.diffuserMatrix_mulVec]
  have hsum : (∑ i : Fin (2 ^ n), ((b₀ * sVec n i + b₁ * pVec R i : ℝ) : ℂ)) =
      ((b₀ * √(2 ^ n : ℝ) : ℝ) : ℂ) := by
    simp_rw [Complex.ofReal_add, Complex.ofReal_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    rcases sum_sVec_and_pVec hr1 hrN with ⟨hss, hsp⟩; have hssC := congrArg Complex.ofReal hss
    have hspC := congrArg Complex.ofReal hsp
    simp only [Complex.ofReal_sum, Complex.ofReal_zero] at hssC hspC
    rw [hssC, hspC, mul_zero, add_zero]
  rw [hsum]
  have h2 : ((2 : ℂ) / 2 ^ n) = ((2 / (2 ^ n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [h2, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  congr 1
  simp only [sVec, b₀, b₁]
  have hN_ne : (2 ^ n : ℝ) ≠ 0 := by positivity
  have hsqrt_ne : √(2 ^ n : ℝ) ≠ 0 := by positivity
  field_simp [hN_ne, hsqrt_ne]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 ^ n : ℝ))]; ring
theorem groverStepUnitary_pow_mulVec_comb {n : ℕ} {R : Finset (Fin (2 ^ n))}
    (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n) (K : ℕ) (a₀ a₁ : ℝ) :
    let θ₁ := tcTheta1Real (2 ^ n) R.card
    (groverStepUnitary R ^ K).1 *ᵥ (fun x ↦ ((a₀ * sVec n x + a₁ * pVec R x : ℝ) : ℂ)) =
      fun x ↦ (((Real.cos ((K : ℝ) * θ₁) * a₀ - Real.sin ((K : ℝ) * θ₁) * a₁) * sVec n x +
        (Real.sin ((K : ℝ) * θ₁) * a₀ + Real.cos ((K : ℝ) * θ₁) * a₁) * pVec R x : ℝ) : ℂ) := by
  intro θ₁
  induction K with
  | zero => simp
  | succ K ih =>
      rw [pow_succ' (groverStepUnitary R) K, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih,
        groverStepUnitary_mulVec_comb hr1 hrN]
      funext x
      congr 1
      have harg : (((K + 1 : ℕ) : ℝ) * θ₁) = θ₁ + (K : ℝ) * θ₁ := by push_cast; ring
      rw [harg, Real.cos_add, Real.sin_add]; ring
/-- Coordinatewise tensor product `∏ q: Fin d, F q (f q)` on `TupleSpace n d`. -/
noncomputable def prodVec {n d : ℕ} (F : Fin d → Fin (2 ^ n) → ℝ) (f : TupleSpace n d) : ℝ :=
  ∏ q : Fin d, F q (f q)
theorem localMemSlotEmbed_mulVec_prodVec {n d : ℕ} (q₀ : Fin d)
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (F : Fin d → Fin (2 ^ n) → ℝ) (g : Fin (2 ^ n) → ℝ)
    (hM : M *ᵥ (fun x ↦ (F q₀ x : ℂ)) = fun x ↦ (g x : ℂ)) :
    (localMemSlotReg n d q₀).embedMatrix M *ᵥ (fun z ↦ (prodVec F (regsEquiv n d z) : ℂ)) =
      fun z ↦ (prodVec (Function.update F q₀ g) (regsEquiv n d z) : ℂ) := by
  funext z
  rw [(localMemSlotReg n d q₀).embedMatrix_mulVec_apply]
  change (∑ u : Fin (2 ^ n), M ((localMemSlotReg n d q₀).extractIndex z) u *
        (prodVec F (regsEquiv n d ((localMemSlotReg n d q₀).replaceIndex z u)) : ℂ)) = _
  simp_rw [regsEquiv_replaceIndex]
  set f := regsEquiv n d z
  have hq0 : (localMemSlotReg n d q₀).extractIndex z = f q₀ := (regsEquiv_apply n d z q₀).symm
  rw [hq0]; have hsplit : ∀ u : Fin (2 ^ n), (prodVec F (Function.update f q₀ u) : ℂ) =
        (F q₀ u : ℂ) * ∏ q ∈ Finset.univ.erase q₀, (F q (f q) : ℂ) := by
    intro u
    rw [prodVec, Complex.ofReal_prod,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun q hq ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  simp_rw [hsplit, ← mul_assoc, ← Finset.sum_mul]
  have hact : (∑ u : Fin (2 ^ n), M (f q₀) u * (F q₀ u : ℂ)) = (g (f q₀) : ℂ) := congrFun hM (f q₀)
  rw [hact, prodVec, Complex.ofReal_prod,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun q hq ↦ ?_; rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
theorem hProdMat_mulVec_prodVec {n d : ℕ} (F : Fin d → Fin (2 ^ n) → ℝ) :
    hProdMat n d *ᵥ prodVec F = prodVec (fun q ↦ realHadamard n *ᵥ F q) := by
  funext f
  simp only [Matrix.mulVec, dotProduct, hProdMat, Matrix.of_apply, prodVec,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun (q : Fin d) (y : Fin (2 ^ n)) ↦ realHadamard n (f q) y * F q y).symm
/-- Binary tensor-product basis vector assigning `v₁` on `S` and `v₀` on `Sᶜ`. -/
noncomputable def prodSubVec {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ) (S : Finset (Fin d)) :
    TupleSpace n d → ℝ :=
  prodVec fun q ↦ if q ∈ S then v₁ else v₀
theorem dotProduct_prodSubVec {n d : ℕ} {v₀ v₁ : Fin (2 ^ n) → ℝ}
    (hv0 : dotProduct v₀ v₀ = 1) (hv1 : dotProduct v₁ v₁ = 1) (hv01 : dotProduct v₀ v₁ = 0)
    (S₁ S₂ : Finset (Fin d)) :
    dotProduct (prodSubVec v₀ v₁ S₁) (prodSubVec v₀ v₁ S₂) = if S₁ = S₂ then 1 else 0 := by
  have hv10 : dotProduct v₁ v₀ = 0 := by rw [dotProduct_comm, hv01]
  simp only [dotProduct, prodSubVec, prodVec, ← Finset.prod_mul_distrib]
  rw [(Fintype.prod_sum fun (q : Fin d) (x : Fin (2 ^ n)) ↦
    ((if q ∈ S₁ then v₁ else v₀) x) * ((if q ∈ S₂ then v₁ else v₀) x)).symm]
  by_cases hS : S₁ = S₂
  · subst hS
    simp only [↓reduceIte]
    refine Finset.prod_eq_one fun q _ ↦ ?_
    by_cases hq : q ∈ S₁
    · simpa [hq, dotProduct] using hv1
    · simpa [hq, dotProduct] using hv0
  · simp only [hS, ↓reduceIte]
    have hex : ∃ q : Fin d, (q ∈ S₁ ∧ q ∉ S₂) ∨ (q ∉ S₁ ∧ q ∈ S₂) := by
      by_contra hall
      apply hS
      ext q
      have hq := not_or.1 (not_exists.1 hall q)
      tauto
    rcases hex with ⟨q, hq | hq⟩
    · exact Finset.prod_eq_zero (Finset.mem_univ q) (by simpa [hq.1, hq.2, dotProduct] using hv10)
    · exact Finset.prod_eq_zero (Finset.mem_univ q) (by simpa [hq.1, hq.2, dotProduct] using hv01)
theorem permMat_mulVec_prodSubVec {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ)
    (S : Finset (Fin d)) (σ : Equiv.Perm (Fin d)) :
    permMat n d σ *ᵥ prodSubVec v₀ v₁ S = prodSubVec v₀ v₁ (S.map σ.toEmbedding) := by
  funext f
  rw [permMat_mulVec, prodSubVec, prodVec, prodSubVec, prodVec,
    ← Equiv.prod_comp σ (fun q ↦ (if q ∈ S.map σ.toEmbedding then v₁ else v₀) (f q))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_; simp [Function.comp_apply]
theorem prodSubVec_zero_support {n d : ℕ} {qVec : Fin (2 ^ n) → ℝ} (hq0 : qVec 0 = 0)
    (S : Finset (Fin d)) {f : TupleSpace n d} (hnz : prodSubVec (Pi.single 0 1) qVec S f ≠ 0) :
    Finset.univ.filter (fun i : Fin d ↦ f i ≠ 0) = S := by
  rw [prodSubVec, prodVec, Finset.prod_ne_zero_iff] at hnz
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have hi := hnz i (Finset.mem_univ i)
  by_cases his : i ∈ S
  · simp only [his, ↓reduceIte] at hi
    exact ⟨fun _ ↦ his, fun _ h0 ↦ hi (h0 ▸ hq0)⟩
  · simp only [his, ↓reduceIte, Pi.single_apply] at hi
    by_cases hfi : f i = 0
    · simp [hfi, his]
    · simp [hfi] at hi
theorem wtProj_mulVec_prodSubVec_e0 {n d : ℕ} {qVec : Fin (2 ^ n) → ℝ} (hq0 : qVec 0 = 0)
    (w : ℕ) (S : Finset (Fin d)) : wtProj n d w *ᵥ prodSubVec (Pi.single 0 1) qVec S =
      if S.card = w then prodSubVec (Pi.single 0 1) qVec S else 0 := by
  funext f
  rw [wtProj, Matrix.mulVec_diagonal]
  by_cases hnz : prodSubVec (Pi.single 0 1) qVec S f = 0
  · split_ifs <;> simp [hnz]
  · have hwt : wtTuple f = S.card := by
      unfold wtTuple; rw [prodSubVec_zero_support hq0 S hnz]
    by_cases hcard : S.card = w
    · simp [hwt, hcard]
    · simp [hwt, hcard]
theorem wtZeroProj_mulVec_prodSubVec_e0 {n d : ℕ} (hd : 1 ≤ d) {qVec : Fin (2 ^ n) → ℝ}
    (hq0 : qVec 0 = 0) (w : ℕ) (S : Finset (Fin d)) :
    wtZeroProj n d hd w *ᵥ prodSubVec (Pi.single 0 1) qVec S =
      if S.card = w ∧ ⟨0, hd⟩ ∉ S then prodSubVec (Pi.single 0 1) qVec S else 0 := by
  funext f
  rw [wtZeroProj, Matrix.mulVec_diagonal]
  by_cases hnz : prodSubVec (Pi.single 0 1) qVec S f = 0
  · split_ifs <;> simp [hnz]
  · have hsupp := prodSubVec_zero_support hq0 S hnz
    have hwt : wtTuple f = S.card := by unfold wtTuple; rw [hsupp]
    have h0_iff : f ⟨0, hd⟩ = 0 ↔ ⟨0, hd⟩ ∉ S := by
      have hmem := Finset.ext_iff.1 hsupp ⟨0, hd⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      tauto
    by_cases hc : S.card = w ∧ ⟨0, hd⟩ ∉ S
    · have hf : wtTuple f = w ∧ f ⟨0, hd⟩ = 0 := ⟨hwt.trans hc.1, h0_iff.2 hc.2⟩; simp [hc, hf]
    · have hf : ¬ (wtTuple f = w ∧ f ⟨0, hd⟩ = 0) :=
        fun h ↦ hc ⟨hwt.symm.trans h.1, h0_iff.1 h.2⟩
      simp [hc, hf]
/-- Unnormalized weight-`w` tail-symmetric vector with coordinate `0` in `v₀`. -/
noncomputable def tailZeroSubVec {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ) (hd : 1 ≤ d) (w : ℕ) :
    TupleSpace n d → ℝ :=
  ∑ T ∈ ((Finset.univ : Finset (Fin d)).erase ⟨0, hd⟩).powersetCard w, prodSubVec v₀ v₁ T
/-- Unnormalized weight-`w` tail-symmetric vector with coordinate `0` in `v₁`. -/
noncomputable def headOneSubVec {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ) (hd : 1 ≤ d) (w : ℕ) :
    TupleSpace n d → ℝ :=
  ∑ T ∈ ((Finset.univ : Finset (Fin d)).erase ⟨0, hd⟩).powersetCard (w - 1),
    prodSubVec v₀ v₁ (insert ⟨0, hd⟩ T)
/-- Orthonormal `2d`-subspace basis `F_k` (`k < 2 * d`) on `TupleSpace n d` built from
  `(v₀, v₁)`. -/
noncomputable def basis2dTuple {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ) (hd : 1 ≤ d) (k : ℕ) :
    TupleSpace n d → ℝ :=
  if k < 2 * d then
    (1 / √(Nat.choose (d - 1) (k / 2) : ℝ)) •
      if k % 2 = 0 then tailZeroSubVec v₀ v₁ hd (k / 2) else headOneSubVec v₀ v₁ hd (k / 2 + 1)
  else 0
theorem symStabMat_mulVec_tailZeroSubVec {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ) (hd : 1 ≤ d) (w : ℕ) :
    symStabMat n d hd *ᵥ tailZeroSubVec v₀ v₁ hd w = tailZeroSubVec v₀ v₁ hd w := by
  have : Nonempty (StabZero d hd) := ⟨⟨1, rfl⟩⟩
  set U := (Finset.univ : Finset (Fin d)).erase ⟨0, hd⟩
  have hperm : ∀ τ : StabZero d hd,
      permMat n d τ.1 *ᵥ tailZeroSubVec v₀ v₁ hd w = tailZeroSubVec v₀ v₁ hd w := by
    intro τ
    rw [tailZeroSubVec, Matrix.mulVec_sum]
    simp_rw [permMat_mulVec_prodSubVec]
    refine Finset.sum_bij (fun T _ ↦ T.map τ.1.toEmbedding) ?_ ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_powersetCard] at hT ⊢
      refine ⟨fun x hx ↦ ?_, by rw [Finset.card_map, hT.2]⟩
      rcases Finset.mem_map.1 hx with ⟨y, hy, rfl⟩
      have hy0 : y ≠ ⟨0, hd⟩ := Finset.ne_of_mem_erase (hT.1 hy)
      refine Finset.mem_erase.2 ⟨fun hEq ↦ hy0 (τ.1.injective (hEq.trans τ.2.symm)),
        Finset.mem_univ _⟩
    · intro T₁ _ T₂ _ hEq
      ext x
      have hm := Finset.ext_iff.1 hEq (τ.1 x)
      simpa using hm
    · intro S hS
      rw [Finset.mem_powersetCard] at hS; have hsymm0 : τ.1.symm ⟨0, hd⟩ = ⟨0, hd⟩ :=
        (congrArg (⇑τ.1.symm) τ.2).symm.trans (τ.1.symm_apply_apply ⟨0, hd⟩)
      refine ⟨S.map τ.1.symm.toEmbedding, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        refine ⟨fun x hx ↦ ?_, by rw [Finset.card_map, hS.2]⟩
        rcases Finset.mem_map.1 hx with ⟨y, hy, rfl⟩
        have hy0 : y ≠ ⟨0, hd⟩ := Finset.ne_of_mem_erase (hS.1 hy)
        exact Finset.mem_erase.2 ⟨fun hEq ↦ hy0 (τ.1.symm.injective (hEq.trans hsymm0.symm)),
          Finset.mem_univ _⟩
      · ext x
        simp
    · intro _ _; rfl
  rw [symStabMat, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp_rw [hperm]
  rw [Finset.sum_const, Finset.card_univ]
  funext f
  simp only [Pi.smul_apply]; simp only [smul_eq_mul, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (Fintype.card (StabZero d hd) : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  rw [← mul_assoc, one_div_mul_cancel hpos.ne', one_mul]
theorem sum_swap_mulVec_tailZeroSubVec {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ)
    (hd : 1 ≤ d) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) :
    (∑ j : Fin d, permMat n d (Equiv.swap ⟨0, hd⟩ j) *ᵥ tailZeroSubVec v₀ v₁ hd w) =
      ((d : ℝ) - (w : ℝ)) • (tailZeroSubVec v₀ v₁ hd w + headOneSubVec v₀ v₁ hd w) := by
  set q₀ : Fin d := ⟨0, hd⟩
  set U := (Finset.univ : Finset (Fin d)).erase q₀
  simp_rw [tailZeroSubVec, Matrix.mulVec_sum, permMat_mulVec_prodSubVec]
  rw [Finset.sum_comm]; have hsplit : ∀ T ∈ U.powersetCard w,
      (∑ j : Fin d, prodSubVec v₀ v₁ (T.map (Equiv.swap q₀ j).toEmbedding)) =
        ((d : ℝ) - (w : ℝ)) • prodSubVec v₀ v₁ T +
          ∑ j ∈ T, prodSubVec v₀ v₁ (insert q₀ (T.erase j)) := by
    intro T hT
    rcases Finset.mem_powersetCard.1 hT with ⟨hTU, hTcard⟩
    have hq0_not : q₀ ∉ T := fun h ↦ (Finset.mem_erase.1 (hTU h)).1 rfl
    have huniv : (Finset.univ : Finset (Fin d)) = (Finset.univ \ T) ∪ T := by
      ext j; by_cases hj : j ∈ T <;> simp [hj]
    have hdisj : Disjoint (Finset.univ \ T) T := Finset.sdiff_disjoint
    rw [huniv, Finset.sum_union hdisj]
    congr 1
    · have hnot : ∀ j ∈ Finset.univ \ T,
          prodSubVec v₀ v₁ (T.map (Equiv.swap q₀ j).toEmbedding) = prodSubVec v₀ v₁ T := by
        intro j hj
        have hjT : j ∉ T := (Finset.mem_sdiff.1 hj).2
        congr 1
        ext x
        simp only [Finset.mem_map, Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨y, hy, rfl⟩
          have hy0 : y ≠ q₀ := fun h ↦ hq0_not (h ▸ hy)
          have hyj : y ≠ j := fun h ↦ hjT (h ▸ hy); rwa [Equiv.swap_apply_of_ne_of_ne hy0 hyj]
        · intro hx
          refine ⟨x, hx, ?_⟩
          exact Equiv.swap_apply_of_ne_of_ne (fun h ↦ hq0_not (h ▸ hx)) (fun h ↦ hjT (h ▸ hx))
      rw [Finset.sum_congr rfl hnot, Finset.sum_const,
        Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, Fintype.card_fin,
        hTcard]
      funext f
      simp [nsmul_eq_mul, Nat.cast_sub hwd.le]
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      congr 1
      ext x
      simp only [Finset.mem_map, Equiv.coe_toEmbedding, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨y, hy, rfl⟩
        by_cases hyj : y = j
        · subst hyj; exact Or.inl (Equiv.swap_apply_right q₀ y)
        · have hy0 : y ≠ q₀ := fun h ↦ hq0_not (h ▸ hy); rw [Equiv.swap_apply_of_ne_of_ne hy0 hyj]
          exact Or.inr ⟨hyj, hy⟩
      · rintro (rfl | ⟨hxj, hxT⟩)
        · exact ⟨j, hj, Equiv.swap_apply_right q₀ j⟩
        · exact ⟨x, hxT, Equiv.swap_apply_of_ne_of_ne (fun h ↦ hq0_not (h ▸ hxT)) hxj⟩
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  congr 1
  rw [Finset.sum_sigma' (U.powersetCard w) (fun T : Finset (Fin d) ↦ T)]
  have hbij : (∑ p ∈ (U.powersetCard w).sigma (fun T ↦ T),
          prodSubVec (n := n) v₀ v₁ (insert q₀ (p.1.erase p.2))) =
        ∑ p ∈ (U.powersetCard (w - 1)).sigma (fun T' ↦ U \ T'),
          prodSubVec (n := n) v₀ v₁ (insert q₀ p.1) := by
    refine Finset.sum_bij (fun p _ ↦ ⟨p.1.erase p.2, p.2⟩) ?_ ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_sigma.1 hp with ⟨hp1, hp2⟩
      rcases Finset.mem_powersetCard.1 hp1 with ⟨hTU, hTc⟩
      refine Finset.mem_sigma.2 ⟨Finset.mem_powersetCard.2
        ⟨(Finset.erase_subset p.2 p.1).trans hTU, by rw [Finset.card_erase_of_mem hp2, hTc]⟩,
        Finset.mem_sdiff.2 ⟨hTU hp2, Finset.notMem_erase p.2 p.1⟩⟩
    · intro p₁ hp₁ p₂ hp₂ hEq
      have hj : p₁.2 = p₂.2 := congrArg Sigma.snd hEq
      have hE : p₁.1.erase p₁.2 = p₂.1.erase p₂.2 := congrArg Sigma.fst hEq
      ext1
      · rw [← Finset.insert_erase (Finset.mem_sigma.1 hp₁).2, hE, hj,
          Finset.insert_erase (Finset.mem_sigma.1 hp₂).2]
      · exact heq_of_eq hj
    · intro q hq
      rcases Finset.mem_sigma.1 hq with ⟨hq1, hq2⟩
      rcases Finset.mem_powersetCard.1 hq1 with ⟨hT'U, hT'c⟩
      rcases Finset.mem_sdiff.1 hq2 with ⟨hjU, hjnot⟩
      refine ⟨⟨insert q.2 q.1, q.2⟩, Finset.mem_sigma.2 ⟨Finset.mem_powersetCard.2
        ⟨Finset.insert_subset_iff.2 ⟨hjU, hT'U⟩, ?_⟩, Finset.mem_insert_self _ _⟩, ?_⟩
      · rw [Finset.card_insert_of_notMem hjnot, hT'c]; omega
      · ext1
        · exact Finset.erase_insert hjnot
        · rfl
    · intro _ _; rfl
  rw [hbij, Finset.sum_sigma, headOneSubVec, Finset.smul_sum]
  refine Finset.sum_congr rfl fun T' hT' ↦ ?_
  rcases Finset.mem_powersetCard.1 hT' with ⟨hT'U, hT'c⟩
  have hcardU : U.card = d - 1 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem (Finset.mem_univ q₀), Finset.card_univ, Fintype.card_fin]
  have hsdiff_c : (U \ T').card = d - w := by
    rw [Finset.card_sdiff_of_subset hT'U, hcardU, hT'c]; omega
  dsimp only; rw [Finset.sum_const, hsdiff_c]
  funext f
  simp [nsmul_eq_mul, Nat.cast_sub hwd.le, q₀]
theorem symAllMat_mulVec_tailZeroSubVec {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ)
    (hd : 1 ≤ d) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) : symAllMat n d *ᵥ tailZeroSubVec v₀ v₁ hd w =
      (((d : ℝ) - (w : ℝ)) / (d : ℝ)) • (tailZeroSubVec v₀ v₁ hd w + headOneSubVec v₀ v₁ hd w) := by
  rw [symAllMat_eq_avgSwap_mul_symStabMat n d hd, ← Matrix.mulVec_mulVec,
    symStabMat_mulVec_tailZeroSubVec, Matrix.smul_mulVec, Matrix.sum_mulVec,
    sum_swap_mulVec_tailZeroSubVec v₀ v₁ hd hw1 hwd, smul_smul]
  congr 1
  ring
theorem wtProj_mulVec_tailZeroSubVec_e0 {n d : ℕ} (hd : 1 ≤ d) {qVec : Fin (2 ^ n) → ℝ}
    (hq0 : qVec 0 = 0) (w w' : ℕ) : wtProj n d w' *ᵥ tailZeroSubVec (Pi.single 0 1) qVec hd w =
      if w = w' then tailZeroSubVec (Pi.single 0 1) qVec hd w else 0 := by
  rw [tailZeroSubVec, Matrix.mulVec_sum]
  by_cases hww : w = w'
  · subst hww
    simp only [↓reduceIte]
    refine Finset.sum_congr rfl fun T hT ↦ ?_
    rw [wtProj_mulVec_prodSubVec_e0 hq0, (Finset.mem_powersetCard.1 hT).2, ite_eq_left rfl]
  · simp only [hww, ↓reduceIte]
    refine Finset.sum_eq_zero fun T hT ↦ ?_
    rw [wtProj_mulVec_prodSubVec_e0 hq0, (Finset.mem_powersetCard.1 hT).2, ite_eq_right hww]
theorem wtProj_mulVec_headOneSubVec_e0 {n d : ℕ} (hd : 1 ≤ d) {qVec : Fin (2 ^ n) → ℝ}
    (hq0 : qVec 0 = 0) {w : ℕ} (hw1 : 1 ≤ w) (w' : ℕ) :
    wtProj n d w' *ᵥ headOneSubVec (Pi.single 0 1) qVec hd w =
      if w = w' then headOneSubVec (Pi.single 0 1) qVec hd w else 0 := by
  rw [headOneSubVec, Matrix.mulVec_sum]
  have hcard : ∀ T ∈ ((Finset.univ : Finset (Fin d)).erase ⟨0, hd⟩).powersetCard (w - 1),
      (insert ⟨0, hd⟩ T).card = w := by
    intro T hT
    rcases Finset.mem_powersetCard.1 hT with ⟨hTU, hTc⟩
    have hnot : ⟨0, hd⟩ ∉ T := fun h ↦ (Finset.mem_erase.1 (hTU h)).1 rfl
    rw [Finset.card_insert_of_notMem hnot, hTc]; omega
  by_cases hww : w = w'
  · subst hww
    simp only [↓reduceIte]
    refine Finset.sum_congr rfl fun T hT ↦ ?_
    rw [wtProj_mulVec_prodSubVec_e0 hq0, hcard T hT, ite_eq_left rfl]
  · simp only [hww, ↓reduceIte]
    refine Finset.sum_eq_zero fun T hT ↦ ?_
    rw [wtProj_mulVec_prodSubVec_e0 hq0, hcard T hT, ite_eq_right hww]
theorem p2Mat_mulVec_tailZero_and_headOne_e0 {n d : ℕ} (hd : 1 ≤ d) {qVec : Fin (2 ^ n) → ℝ}
    (hq0 : qVec 0 = 0) (w : ℕ) : p2Mat n d hd w *ᵥ tailZeroSubVec (Pi.single 0 1) qVec hd w =
      tailZeroSubVec (Pi.single 0 1) qVec hd w ∧
    p2Mat n d hd w *ᵥ headOneSubVec (Pi.single 0 1) qVec hd w = 0 := by
  constructor
  · rw [p2Mat, ← Matrix.mulVec_mulVec, symStabMat_mulVec_tailZeroSubVec, tailZeroSubVec,
      Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun T hT ↦ ?_; rcases Finset.mem_powersetCard.1 hT with ⟨hTU, hTc⟩
    have hnot : ⟨0, hd⟩ ∉ T := fun h ↦ (Finset.mem_erase.1 (hTU h)).1 rfl
    rw [wtZeroProj_mulVec_prodSubVec_e0 hd hq0, ite_eq_left ⟨hTc, hnot⟩]
  · have hp2 : p2Mat n d hd w = symStabMat n d hd * wtZeroProj n d hd w := by
      rw [p2Mat, symStabMat_mul_wtZeroProj]
    rw [hp2, ← Matrix.mulVec_mulVec]
    have hz : wtZeroProj n d hd w *ᵥ headOneSubVec (Pi.single 0 1) qVec hd w = 0 := by
      rw [headOneSubVec, Matrix.mulVec_sum]
      refine Finset.sum_eq_zero fun T _ ↦ ?_; rw [wtZeroProj_mulVec_prodSubVec_e0 hd hq0]; simp
    rw [hz, Matrix.mulVec_zero]
theorem wOp_mulVec_basis2dTuple_even {n d : ℕ} (hd : 1 ≤ d) {qVec : Fin (2 ^ n) → ℝ}
    (hq0 : qVec 0 = 0) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) :
    wOp n d hd w *ᵥ basis2dTuple (Pi.single 0 1) qVec hd (2 * w) =
      basis2dTuple (Pi.single 0 1) qVec hd (2 * w - 1) := by
  have h2w_lt : 2 * w < 2 * d := by omega
  have h2wm1_lt : 2 * w - 1 < 2 * d := by omega
  have hdiv0 : (2 * w) / 2 = w := by omega
  have hmod0 : (2 * w) % 2 = 0 := by omega
  have hdiv1 : (2 * w - 1) / 2 = w - 1 := by omega
  have hmod1 : (2 * w - 1) % 2 = 1 := by omega
  have hadd1 : w - 1 + 1 = w := by omega
  have hb : basis2dTuple (Pi.single 0 1) qVec hd (2 * w) =
      (1 / √(Nat.choose (d - 1) w : ℝ)) • tailZeroSubVec (Pi.single 0 1) qVec hd w := by
    simp [basis2dTuple, h2w_lt, hdiv0, hmod0]
  have ha : basis2dTuple (Pi.single 0 1) qVec hd (2 * w - 1) =
      (1 / √(Nat.choose (d - 1) (w - 1) : ℝ)) • headOneSubVec (Pi.single 0 1) qVec hd w := by
    simp [basis2dTuple, h2wm1_lt, hdiv1, hmod1, hadd1]
  rw [hb, ha, Matrix.mulVec_smul]
  rcases p2Mat_mulVec_tailZero_and_headOne_e0 (n := n) hd hq0 w with ⟨hp2_tail, hp2_head⟩
  have hp1 : p1Mat n d w *ᵥ tailZeroSubVec (Pi.single 0 1) qVec hd w =
      (((d : ℝ) - (w : ℝ)) / (d : ℝ)) • (tailZeroSubVec (Pi.single 0 1) qVec hd w +
          headOneSubVec (Pi.single 0 1) qVec hd w) := by
    rw [p1Mat, ← Matrix.mulVec_mulVec, symAllMat_mulVec_tailZeroSubVec _ _ hd hw1 hwd,
      Matrix.mulVec_smul, Matrix.mulVec_add, wtProj_mulVec_tailZeroSubVec_e0 hd hq0 w w,
      wtProj_mulVec_headOneSubVec_e0 hd hq0 hw1 w]
    simp
  have hqOp : qOp n d hd w *ᵥ tailZeroSubVec (Pi.single 0 1) qVec hd w =
      (((d : ℝ) - (w : ℝ)) / (d : ℝ)) • headOneSubVec (Pi.single 0 1) qVec hd w := by
    rw [qOp, ← Matrix.mulVec_mulVec, hp2_tail, ← Matrix.mulVec_mulVec, hp1,
      Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_add,
      wtProj_mulVec_tailZeroSubVec_e0 hd hq0 w w, wtProj_mulVec_headOneSubVec_e0 hd hq0 hw1 w,
      hp2_tail, hp2_head]
    simp
  rw [wOp, Matrix.smul_mulVec, hqOp, smul_smul, smul_smul]
  congr 1
  have hchoose_nat : Nat.choose (d - 1) w * w = Nat.choose (d - 1) (w - 1) * (d - w) := by
    have hc := Nat.choose_succ_right_eq (d - 1) (w - 1)
    have hsub : d - 1 - (w - 1) = d - w := by omega
    rwa [hadd1, hsub] at hc
  have hchoose_r : (Nat.choose (d - 1) w : ℝ) * (w : ℝ) =
      (Nat.choose (d - 1) (w - 1) : ℝ) * ((d : ℝ) - (w : ℝ)) := by
    have hcast : ((Nat.choose (d - 1) w * w : ℕ) : ℝ) =
        ((Nat.choose (d - 1) (w - 1) * (d - w) : ℕ) : ℝ) := by exact_mod_cast hchoose_nat
    simpa [Nat.cast_mul, Nat.cast_sub hwd.le] using hcast
  have hc_w_pos : (0 : ℝ) < (Nat.choose (d - 1) w : ℝ) :=
    Nat.cast_pos.2 (Nat.choose_pos (by omega))
  have hc_wm1_pos : (0 : ℝ) < (Nat.choose (d - 1) (w - 1) : ℝ) :=
    Nat.cast_pos.2 (Nat.choose_pos (by omega))
  have hw_pos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (show 0 < w by omega)
  have hdw_pos : (0 : ℝ) < (d : ℝ) - (w : ℝ) := by
    have : (w : ℝ) < (d : ℝ) := by exact_mod_cast hwd
    linarith
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hcw_eq : (Nat.choose (d - 1) w : ℝ) =
      (Nat.choose (d - 1) (w - 1) : ℝ) * ((d : ℝ) - (w : ℝ)) / (w : ℝ) :=
    eq_div_of_mul_eq hw_pos.ne' hchoose_r
  have hsq_eq : (((1 / √(Nat.choose (d - 1) w : ℝ)) *
          ((d : ℝ) / √(((d : ℝ) - (w : ℝ)) * (w : ℝ)))) * (((d : ℝ) - (w : ℝ)) / (d : ℝ))) ^ 2 =
        (1 / √(Nat.choose (d - 1) (w - 1) : ℝ)) ^ 2 := by
    have h1 : √(Nat.choose (d - 1) w : ℝ) ^ 2 = (Nat.choose (d - 1) w : ℝ) :=
      Real.sq_sqrt hc_w_pos.le
    have h2 : √(((d : ℝ) - (w : ℝ)) * (w : ℝ)) ^ 2 = ((d : ℝ) - (w : ℝ)) * (w : ℝ) :=
      Real.sq_sqrt (mul_pos hdw_pos hw_pos).le
    have h3 : √(Nat.choose (d - 1) (w - 1) : ℝ) ^ 2 = (Nat.choose (d - 1) (w - 1) : ℝ) :=
      Real.sq_sqrt hc_wm1_pos.le
    rw [mul_pow, mul_pow, div_pow, div_pow, div_pow, div_pow, one_pow, h1, h2, h3, hcw_eq]
    field_simp [hc_wm1_pos.ne', hdw_pos.ne', hw_pos.ne', hd_pos.ne']
  calc ((1 / √(Nat.choose (d - 1) w : ℝ)) *
        ((d : ℝ) / √(((d : ℝ) - (w : ℝ)) * (w : ℝ)))) * (((d : ℝ) - (w : ℝ)) / (d : ℝ))
      = √((((1 / √(Nat.choose (d - 1) w : ℝ)) * ((d : ℝ) / √(((d : ℝ) - (w : ℝ)) * (w : ℝ)))) *
            (((d : ℝ) - (w : ℝ)) / (d : ℝ))) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ = √((1 / √(Nat.choose (d - 1) (w - 1) : ℝ)) ^ 2) := by rw [hsq_eq]
    _ = 1 / √(Nat.choose (d - 1) (w - 1) : ℝ) := Real.sqrt_sq (by positivity)
theorem uBlock_mulVec_pair {n d : ℕ} (hd : 1 ≤ d) {qVec : Fin (2 ^ n) → ℝ}
    (hq0 : qVec 0 = 0) {w : ℕ} (hw1 : 1 ≤ w) (hwd : w < d) (p : ℤ × ℤ) :
    let ca : ℝ := (tcRatCos ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
    let sa : ℝ := (tcRatSin ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
    let aHad := basis2dTuple (Pi.single 0 1) qVec hd (2 * w - 1)
    let bHad := basis2dTuple (Pi.single 0 1) qVec hd (2 * w)
    uBlock n d hd w p *ᵥ aHad = ca • aHad + sa • bHad ∧
      uBlock n d hd w p *ᵥ bHad = ca • bHad - sa • aHad := by
  intro ca sa aHad bHad
  have hW_b : wOp n d hd w *ᵥ bHad = aHad := wOp_mulVec_basis2dTuple_even hd hq0 hw1 hwd
  have hp2_b : p2Mat n d hd w *ᵥ bHad = bHad := by
    have h2w_lt : 2 * w < 2 * d := by omega
    have hdiv0 : (2 * w) / 2 = w := by omega
    have hmod0 : (2 * w) % 2 = 0 := by omega
    have hb_eq : bHad = (1 / √(Nat.choose (d - 1) w : ℝ)) •
        tailZeroSubVec (Pi.single 0 1) qVec hd w := by
      simp [bHad, basis2dTuple, h2w_lt, hdiv0, hmod0]
    rw [hb_eq, Matrix.mulVec_smul, (p2Mat_mulVec_tailZero_and_headOne_e0 hd hq0 w).1]
  have hWt_a : (wOp n d hd w)ᵀ *ᵥ aHad = bHad := by
    rw [← hW_b, Matrix.mulVec_mulVec, wOp_transpose_mul_self n d hd hw1 hwd, hp2_b]
  have hW_a : wOp n d hd w *ᵥ aHad = 0 := by
    rw [← hW_b, Matrix.mulVec_mulVec, wOp_mul_self, Matrix.zero_mulVec]
  have hWt_b : (wOp n d hd w)ᵀ *ᵥ bHad = 0 := by
    rw [← hp2_b, Matrix.mulVec_mulVec, wOp_transpose_mul_p2Mat, Matrix.zero_mulVec]
  have hpA_a : pAMat n d hd w *ᵥ aHad = aHad := by rw [pAMat, ← Matrix.mulVec_mulVec, hWt_a, hW_b]
  have hpA_b : pAMat n d hd w *ᵥ bHad = 0 := by
    rw [pAMat, ← Matrix.mulVec_mulVec, hWt_b, Matrix.mulVec_zero]
  have hp2_a : p2Mat n d hd w *ᵥ aHad = 0 := by
    rw [← hW_b, Matrix.mulVec_mulVec, p2Mat_mul_wOp, Matrix.zero_mulVec]
  have hP_a : wtProj n d w *ᵥ aHad = aHad := by
    rw [← hW_b, Matrix.mulVec_mulVec, wtProj_mul_wOp, hW_b]
  have hP_b : wtProj n d w *ᵥ bHad = bHad := by
    rw [← hp2_b, Matrix.mulVec_mulVec, wtProj_mul_p2Mat, hp2_b]
  constructor
  · unfold uBlock; dsimp only
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
      Matrix.neg_mulVec, hP_a, hpA_a, hp2_a, hW_a, hWt_a]
    simp [ca, sa]
  · unfold uBlock; dsimp only
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
      Matrix.neg_mulVec, hP_b, hpA_b, hp2_b, hW_b, hWt_b]
    simp [ca, sa, sub_eq_add_neg, smul_neg]
theorem wtProj_mulVec_basis2dTuple_e0 {n d : ℕ} (hd : 1 ≤ d) {qVec : Fin (2 ^ n) → ℝ}
    (hq0 : qVec 0 = 0) {k : ℕ} (hk : k < 2 * d) (w' : ℕ) :
    wtProj n d w' *ᵥ basis2dTuple (Pi.single 0 1) qVec hd k =
      if k / 2 + k % 2 = w' then basis2dTuple (Pi.single 0 1) qVec hd k else 0 := by
  by_cases hmod : k % 2 = 0
  · have hwt : k / 2 + k % 2 = k / 2 := by omega
    rw [hwt]
    have hb : basis2dTuple (Pi.single 0 1) qVec hd k = (1 / √(Nat.choose (d - 1) (k / 2) : ℝ)) •
          tailZeroSubVec (Pi.single 0 1) qVec hd (k / 2) := by
      simp [basis2dTuple, hk, hmod]
    rw [hb, Matrix.mulVec_smul, wtProj_mulVec_tailZeroSubVec_e0 hd hq0]
    split_ifs <;> simp
  · have hmod1 : k % 2 = 1 := by omega
    have hwt : k / 2 + k % 2 = k / 2 + 1 := by omega
    rw [hwt]
    have hb : basis2dTuple (Pi.single 0 1) qVec hd k = (1 / √(Nat.choose (d - 1) (k / 2) : ℝ)) •
          headOneSubVec (Pi.single 0 1) qVec hd (k / 2 + 1) := by
      simp [basis2dTuple, hk, hmod]
    rw [hb, Matrix.mulVec_smul, wtProj_mulVec_headOneSubVec_e0 hd hq0 (by omega)]
    split_ifs <;> simp
theorem uCoreMat_mulVec_basis2dTuple_cases {n d : ℕ} (hd : 1 ≤ d) (hd2 : 2 ≤ d)
    {qVec : Fin (2 ^ n) → ℝ} (hq0 : qVec 0 = 0) (uRow : ℕ → ℤ × ℤ) :
    let F := basis2dTuple (Pi.single 0 1) qVec hd
    uCoreMat n d hd uRow *ᵥ F 0 = F 0 ∧ uCoreMat n d hd uRow *ᵥ F (2 * d - 1) = F (2 * d - 1) ∧
    (∀ w, 1 ≤ w → w < d →
      let p := uRow (w - 1)
      let ca : ℝ := (tcRatCos ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
      let sa : ℝ := (tcRatSin ((p.1 : ℚ) / (p.2 : ℚ)) : ℝ)
      uCoreMat n d hd uRow *ᵥ F (2 * w - 1) = ca • F (2 * w - 1) + sa • F (2 * w) ∧
      uCoreMat n d hd uRow *ᵥ F (2 * w) = ca • F (2 * w) - sa • F (2 * w - 1)) := by
  intro F
  have hsingle : ∀ k (hk : k < 2 * d),
      uCoreMat n d hd uRow *ᵥ F k = uWeightBlock n d hd uRow (k / 2 + k % 2) *ᵥ F k := by
    intro k hk
    rw [uCoreMat, Matrix.sum_mulVec, Finset.sum_eq_single (k / 2 + k % 2)]
    · intro w' _ hne
      dsimp [F]
      rw [← uWeightBlock_mul_wtProj, ← Matrix.mulVec_mulVec,
        wtProj_mulVec_basis2dTuple_e0 hd hq0 hk w', ite_eq_right hne.symm, Matrix.mulVec_zero]
    · intro hm
      exact (hm (Finset.mem_range.2 (by omega))).elim
  refine ⟨?_, ?_, ?_⟩
  · rw [hsingle 0 (by omega)]; dsimp [F]
    have huwb0 : uWeightBlock n d hd uRow (0 / 2 + 0 % 2) = wtProj n d 0 := by simp [uWeightBlock]
    rw [huwb0, wtProj_mulVec_basis2dTuple_e0 hd hq0 (k := 0) (by omega), ite_eq_left rfl]
  · have hwt : (2 * d - 1) / 2 + (2 * d - 1) % 2 = d := by omega
    rw [hsingle (2 * d - 1) (by omega), hwt]; dsimp [F]
    have huwb : uWeightBlock n d hd uRow d = wtProj n d d := by simp [uWeightBlock]
    rw [huwb, wtProj_mulVec_basis2dTuple_e0 hd hq0 (k := 2 * d - 1) (by omega), ite_eq_left hwt]
  · intro w hw1 hwd
    have hwt1 : (2 * w - 1) / 2 + (2 * w - 1) % 2 = w := by omega
    have hwt0 : (2 * w) / 2 + (2 * w) % 2 = w := by omega
    have huwb : uWeightBlock n d hd uRow w = uBlock n d hd w (uRow (w - 1)) := by
      have hnot : ¬ (w = 0 ∨ d ≤ w) := by omega
      simp [uWeightBlock, hnot]
    rw [hsingle (2 * w - 1) (by omega), hwt1, hsingle (2 * w) (by omega), hwt0, huwb]
    exact uBlock_mulVec_pair hd hq0 hw1 hwd (uRow (w - 1))
theorem hProdMat_mulVec_basis2dTuple {n d : ℕ} (v₀ v₁ : Fin (2 ^ n) → ℝ) (hd : 1 ≤ d) (k : ℕ) :
    hProdMat n d *ᵥ basis2dTuple v₀ v₁ hd k =
      basis2dTuple (realHadamard n *ᵥ v₀) (realHadamard n *ᵥ v₁) hd k := by
  have hsub : ∀ S : Finset (Fin d), hProdMat n d *ᵥ prodSubVec v₀ v₁ S =
        prodSubVec (realHadamard n *ᵥ v₀) (realHadamard n *ᵥ v₁) S := by
    intro S
    rw [prodSubVec, hProdMat_mulVec_prodVec, prodSubVec]
    congr 1
    funext q
    by_cases hq : q ∈ S <;> simp [hq]
  unfold basis2dTuple
  by_cases hk : k < 2 * d
  · simp only [hk, ↓reduceIte, Matrix.mulVec_smul]
    congr 1
    split_ifs <;> simp only [tailZeroSubVec, headOneSubVec, Matrix.mulVec_sum, hsub]
  · simp [hk]
theorem tcIntertwinerRealMat_mulVec_sum_basis2d {n d : ℕ} (hd : 1 ≤ d) (hd2 : 2 ≤ d)
    {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n)
    (uRow : ℕ → ℤ × ℤ) (b : ℕ → ℝ) : tcIntertwinerRealMat n d uRow *ᵥ
        (∑ k ∈ Finset.range (2 * d), b k • basis2dTuple (sVec n) (pVec R) hd k) =
      ∑ k ∈ Finset.range (2 * d),
        (tcIntertwinerStepReal d uRow b k) • basis2dTuple (sVec n) (pVec R) hd k := by
  set qVec := realHadamard n *ᵥ pVec R
  have hq0 : qVec 0 = 0 := realHadamard_mulVec_pVec_zero hr1 hrN
  have hs_had : realHadamard n *ᵥ sVec n = Pi.single 0 1 := realHadamard_mulVec_sVec n
  have hq_inv : realHadamard n *ᵥ qVec = pVec R := by
    dsimp [qVec]; rw [Matrix.mulVec_mulVec, realHadamard_mul_self, Matrix.one_mulVec]
  set E := basis2dTuple (Pi.single 0 1) qVec hd
  set G := basis2dTuple (sVec n) (pVec R) hd
  have hH_G : ∀ k, hProdMat n d *ᵥ G k = E k := by
    intro k
    simpa [G, E, qVec, hs_had] using hProdMat_mulVec_basis2dTuple (sVec n) (pVec R) hd k
  have hH_E : ∀ k, hProdMat n d *ᵥ E k = G k := by
    intro k
    dsimp [G, E]; rw [hProdMat_mulVec_basis2dTuple, realHadamard_mulVec_single_zero, hq_inv]
  rcases uCoreMat_mulVec_basis2dTuple_cases hd hd2 hq0 uRow with ⟨hc0, hcTop, hcMid⟩
  have hcore_sum : uCoreMat n d hd uRow *ᵥ (∑ k ∈ Finset.range (2 * d), b k • E k) =
        ∑ k ∈ Finset.range (2 * d), (tcIntertwinerStepReal d uRow b k) • E k := by
    have hpref : ∀ m ≤ d - 1, uCoreMat n d hd uRow *ᵥ (∑ k ∈ Finset.range (1 + 2 * m), b k • E k) =
          ∑ k ∈ Finset.range (1 + 2 * m), (tcIntertwinerStepReal d uRow b k) • E k := by
      intro m hm
      induction m with
      | zero =>
          simp only [mul_zero, add_zero, Finset.range_one, Finset.sum_singleton, Matrix.mulVec_smul]
          have h0 : tcIntertwinerStepReal d uRow b 0 = b 0 := by
            have : 0 < 2 * d := by omega
            simp [tcIntertwinerStepReal, this]
          dsimp [E]; rw [hc0, h0]
      | succ m ih =>
          set w := m + 1
          have hw1 : 1 ≤ w := by omega
          have hwd : w < d := by omega
          have hk1 : 1 + 2 * m = 2 * w - 1 := by omega
          have hk2 : 1 + 2 * m + 1 = 2 * w := by omega
          have hpair_vec : uCoreMat n d hd uRow *ᵥ (b (2 * w - 1) • E (2 * w - 1)) +
                uCoreMat n d hd uRow *ᵥ (b (2 * w) • E (2 * w)) =
              tcIntertwinerStepReal d uRow b (2 * w - 1) • E (2 * w - 1) +
                tcIntertwinerStepReal d uRow b (2 * w) • E (2 * w) := by
            rw [Matrix.mulVec_smul, Matrix.mulVec_smul]; dsimp [E]
            rcases hcMid w hw1 hwd with ⟨hm1, hm0⟩; rw [hm1, hm0]
            have hstep1 : tcIntertwinerStepReal d uRow b (2 * w - 1) =
                (tcRatCos (((uRow (w - 1)).1 : ℚ) / ((uRow (w - 1)).2 : ℚ)) : ℝ) * b (2 * w - 1) -
                  (tcRatSin (((uRow (w - 1)).1 : ℚ) / ((uRow (w - 1)).2 : ℚ)) : ℝ) * b (2 * w) := by
              have hlt1 : 2 * w - 1 < 2 * d := by omega
              have hne0 : 2 * w - 1 ≠ 0 := by omega
              have hlt2 : 2 * w - 1 + 1 < 2 * d := by omega
              have hdiv : (2 * w - 1 + 1) / 2 = w := by omega
              have hmod : (2 * w - 1) % 2 = 1 := by omega
              simp [tcIntertwinerStepReal, hlt1, hne0, hlt2, hdiv, hmod]
            have hstep2 : tcIntertwinerStepReal d uRow b (2 * w) =
                (tcRatSin (((uRow (w - 1)).1 : ℚ) / ((uRow (w - 1)).2 : ℚ)) : ℝ) * b (2 * w - 1) +
                  (tcRatCos (((uRow (w - 1)).1 : ℚ) / ((uRow (w - 1)).2 : ℚ)) : ℝ) * b (2 * w) := by
              have hlt1 : 2 * w < 2 * d := by omega
              have hne0 : 2 * w ≠ 0 := by omega
              have hlt2 : 2 * w + 1 < 2 * d := by omega
              have hdiv : (2 * w + 1) / 2 = w := by omega
              simp [tcIntertwinerStepReal, hlt1, hne0, hlt2, hdiv]
            rw [hstep1, hstep2]
            funext f
            simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
          have h12 : 1 + 2 * (m + 1) = (1 + 2 * m) + 1 + 1 := by omega
          rw [h12, Finset.sum_range_succ, Finset.sum_range_succ, Matrix.mulVec_add,
            Matrix.mulVec_add, ih (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
            hk2, hk1]
          funext f
          have hp := congrFun hpair_vec f; simp only [Pi.add_apply] at hp ⊢; linarith
    have h2d : 2 * d = (1 + 2 * (d - 1)) + 1 := by omega
    have hk_top : 1 + 2 * (d - 1) = 2 * d - 1 := by omega
    rw [h2d, Finset.sum_range_succ, Matrix.mulVec_add, hpref (d - 1) le_rfl,
      Finset.sum_range_succ]
    congr 1
    rw [hk_top, Matrix.mulVec_smul]; dsimp [E]; rw [hcTop]
    have htop : tcIntertwinerStepReal d uRow b (2 * d - 1) = b (2 * d - 1) := by
      have hlt : 2 * d - 1 < 2 * d := by omega
      have hne0 : 2 * d - 1 ≠ 0 := by omega
      have hnlt : ¬ (2 * d - 1 + 1 < 2 * d) := by omega
      simp [tcIntertwinerStepReal, hlt, hne0, hnlt]
    rw [htop]
  have htc : tcIntertwinerRealMat n d uRow =
      hProdMat n d * uCoreMat n d hd uRow * hProdMat n d := by
    simp [tcIntertwinerRealMat, hd]
  rw [htc, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h1 : hProdMat n d *ᵥ (∑ k ∈ Finset.range (2 * d), b k • G k) =
      ∑ k ∈ Finset.range (2 * d), b k • E k := by
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_; rw [Matrix.mulVec_smul, hH_G]
  rw [h1, hcore_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_; rw [Matrix.mulVec_smul, hH_E]
/-- Lift a real tuple vector `TupleSpace n d → ℝ` to `Fin (2 ^ (n * d)) → ℂ` via
  `regsEquiv`. -/
noncomputable def liftVec {n d : ℕ} (v : TupleSpace n d → ℝ) (z : Fin (2 ^ (n * d))) : ℂ :=
  (v (regsEquiv n d z) : ℂ)
theorem liftVec_add {n d : ℕ} (u v : TupleSpace n d → ℝ) :
    liftVec (u + v) = liftVec u + liftVec v := by
  funext z; simp [liftVec]
theorem liftVec_smul {n d : ℕ} (c : ℝ) (v : TupleSpace n d → ℝ) :
    liftVec (c • v) = (c : ℂ) • liftVec v := by
  funext z; simp [liftVec]
theorem liftVec_sum {n d : ℕ} {α : Type*} (s : Finset α) (f : α → TupleSpace n d → ℝ) :
    liftVec (∑ x ∈ s, f x) = ∑ x ∈ s, liftVec (f x) := by
  funext z
  simp [liftVec, Finset.sum_apply]
theorem prodVec_update_head_comb {n d : ℕ} (hd : 1 ≤ d) {R : Finset (Fin (2 ^ n))}
    {T : Finset (Fin d)} (hq0_not : ⟨0, hd⟩ ∉ T) (a₀ a₁ : ℝ) :
    prodVec (Function.update (fun q : Fin d ↦ if q ∈ T then pVec R else sVec n) ⟨0, hd⟩
        (fun x ↦ a₀ * sVec n x + a₁ * pVec R x)) = a₀ • prodSubVec (sVec n) (pVec R) T +
        a₁ • prodSubVec (sVec n) (pVec R) (insert ⟨0, hd⟩ T) := by
  set q₀ : Fin d := ⟨0, hd⟩
  funext f
  simp only [prodVec, prodSubVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀)]
  simp only [Function.update_self, hq0_not, ↓reduceIte, Finset.mem_insert_self]
  have h1 : (∏ q ∈ Finset.univ.erase q₀,
        Function.update (fun q : Fin d ↦ if q ∈ T then pVec R else sVec n) q₀
          (fun x ↦ a₀ * sVec n x + a₁ * pVec R x) q (f q)) =
      ∏ q ∈ Finset.univ.erase q₀, (if q ∈ T then pVec R else sVec n) (f q) := by
    refine Finset.prod_congr rfl fun q hq ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  have h2 : (∏ q ∈ Finset.univ.erase q₀, (if q ∈ insert q₀ T then pVec R else sVec n) (f q)) =
      ∏ q ∈ Finset.univ.erase q₀, (if q ∈ T then pVec R else sVec n) (f q) := by
    refine Finset.prod_congr rfl fun q hq ↦ ?_; have hne : q ≠ q₀ := Finset.ne_of_mem_erase hq
    simp [Finset.mem_insert, hne]
  rw [h1, h2]; ring
theorem groverHeadEmbed_mulVec_sum_basis2d {n d : ℕ} (hd : 1 ≤ d)
    {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n) (K_blk : ℕ) (b : ℕ → ℝ) :
    let θ₁ := tcTheta1Real (2 ^ n) R.card
    let c1 := Real.cos ((K_blk : ℝ) * θ₁)
    let s1 := Real.sin ((K_blk : ℝ) * θ₁)
    (localMemSlotReg n d ⟨0, hd⟩).embedMatrix (groverStepUnitary R ^ K_blk).1 *ᵥ
        liftVec (∑ k ∈ Finset.range (2 * d), b k • basis2dTuple (sVec n) (pVec R) hd k) =
      liftVec (∑ k ∈ Finset.range (2 * d),
        (tcGroverStepReal d c1 s1 b k) • basis2dTuple (sVec n) (pVec R) hd k) := by
  intro θ₁ c1 s1
  set q₀ : Fin d := ⟨0, hd⟩
  set M := (localMemSlotReg n d q₀).embedMatrix (groverStepUnitary R ^ K_blk).1
  set G := basis2dTuple (sVec n) (pVec R) hd
  have hpair : ∀ w < d, M *ᵥ liftVec (b (2 * w) • G (2 * w) + b (2 * w + 1) • G (2 * w + 1)) =
        liftVec ((c1 * b (2 * w) - s1 * b (2 * w + 1)) • G (2 * w) +
          (s1 * b (2 * w) + c1 * b (2 * w + 1)) • G (2 * w + 1)) := by
    intro w hwd
    have hlt0 : 2 * w < 2 * d := by omega
    have hlt1 : 2 * w + 1 < 2 * d := by omega
    have hdiv0 : (2 * w) / 2 = w := by omega
    have hmod0 : (2 * w) % 2 = 0 := by omega
    have hdiv1 : (2 * w + 1) / 2 = w := by omega
    have hmod1 : (2 * w + 1) % 2 = 1 := by omega
    have hG0 : G (2 * w) =
        (1 / √(Nat.choose (d - 1) w : ℝ)) • tailZeroSubVec (sVec n) (pVec R) hd w := by
      simp [G, basis2dTuple, hlt0, hdiv0, hmod0]
    have hG1 : G (2 * w + 1) =
        (1 / √(Nat.choose (d - 1) w : ℝ)) • headOneSubVec (sVec n) (pVec R) hd (w + 1) := by
      simp [G, basis2dTuple, hlt1, hdiv1, hmod1]
    have hsub_sum : ∀ a₀ a₁ : ℝ, a₀ • G (2 * w) + a₁ • G (2 * w + 1) =
          (1 / √(Nat.choose (d - 1) w : ℝ)) •
            ∑ T ∈ ((Finset.univ : Finset (Fin d)).erase q₀).powersetCard w,
              (a₀ • prodSubVec (sVec n) (pVec R) T +
                a₁ • prodSubVec (sVec n) (pVec R) (insert q₀ T)) := by
      intro a₀ a₁
      rw [hG0, hG1, tailZeroSubVec, headOneSubVec, Nat.add_sub_cancel, smul_comm a₀,
        smul_comm a₁, ← smul_add, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    rw [hsub_sum, hsub_sum, liftVec_smul, liftVec_smul, Matrix.mulVec_smul,
      liftVec_sum, liftVec_sum, Matrix.mulVec_sum]
    congr 1
    refine Finset.sum_congr rfl fun T hT ↦ ?_; have hq0_not : q₀ ∉ T :=
      fun h ↦ (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hT).1 h)).1 rfl
    rw [← prodVec_update_head_comb hd hq0_not, ← prodVec_update_head_comb hd hq0_not]
    have hupd0 : (Function.update (fun q : Fin d ↦ if q ∈ T then pVec R else sVec n) q₀
        (fun x ↦ b (2 * w) * sVec n x + b (2 * w + 1) * pVec R x)) q₀ =
        fun x ↦ b (2 * w) * sVec n x + b (2 * w + 1) * pVec R x := Function.update_self _ _ _
    have hact := localMemSlotEmbed_mulVec_prodVec q₀ (groverStepUnitary R ^ K_blk).1
      (Function.update (fun q : Fin d ↦ if q ∈ T then pVec R else sVec n) q₀
        (fun x ↦ b (2 * w) * sVec n x + b (2 * w + 1) * pVec R x))
      (fun x ↦ (c1 * b (2 * w) - s1 * b (2 * w + 1)) * sVec n x +
        (s1 * b (2 * w) + c1 * b (2 * w + 1)) * pVec R x)
      (by
        rw [hupd0]
        exact groverStepUnitary_pow_mulVec_comb hr1 hrN K_blk (b (2 * w)) (b (2 * w + 1)))
    rw [Function.update_idem] at hact; exact hact
  have hpref : ∀ m ≤ d, M *ᵥ liftVec (∑ k ∈ Finset.range (2 * m), b k • G k) =
        liftVec (∑ k ∈ Finset.range (2 * m), (tcGroverStepReal d c1 s1 b k) • G k) := by
    intro m hm
    induction m with
    | zero =>
        have h0 : liftVec (0 : TupleSpace n d → ℝ) = 0 := by funext z; simp [liftVec]
        simp [h0]
    | succ m ih =>
        have h2m : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
        have hg0 : tcGroverStepReal d c1 s1 b (2 * m) = c1 * b (2 * m) - s1 * b (2 * m + 1) := by
          have hlt : 2 * m < 2 * d := by omega
          have hdiv : (2 * m) / 2 = m := by omega
          have hmod : (2 * m) % 2 = 0 := by omega
          simp [tcGroverStepReal, hlt, hdiv, hmod]
        have hg1 : tcGroverStepReal d c1 s1 b (2 * m + 1) =
            s1 * b (2 * m) + c1 * b (2 * m + 1) := by
          have hlt : 2 * m + 1 < 2 * d := by omega
          have hdiv : (2 * m + 1) / 2 = m := by omega
          have hmod : (2 * m + 1) % 2 = 1 := by omega
          simp [tcGroverStepReal, hlt, hdiv, hmod]
        have hsum_L : (∑ k ∈ Finset.range (2 * (m + 1)), b k • G k) =
            (∑ k ∈ Finset.range (2 * m), b k • G k) +
              (b (2 * m) • G (2 * m) + b (2 * m + 1) • G (2 * m + 1)) := by
          rw [h2m, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
        have hsum_R : (∑ k ∈ Finset.range (2 * (m + 1)), (tcGroverStepReal d c1 s1 b k) • G k) =
            (∑ k ∈ Finset.range (2 * m), (tcGroverStepReal d c1 s1 b k) • G k) +
              ((c1 * b (2 * m) - s1 * b (2 * m + 1)) • G (2 * m) +
                (s1 * b (2 * m) + c1 * b (2 * m + 1)) • G (2 * m + 1)) := by
          rw [h2m, Finset.sum_range_succ, Finset.sum_range_succ, hg0, hg1, add_assoc]
        rw [hsum_L, hsum_R, liftVec_add, Matrix.mulVec_add, ih (by omega),
          hpair m (by omega), ← liftVec_add]
  exact hpref d le_rfl
theorem tcSlotConveyorVec_eq_sum_basis2d {n d : ℕ} (hd : 1 ≤ d) (hd2 : 2 ≤ d)
    {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n)
    (K_blk steps : ℕ) (uFn : ℕ → ℕ → ℤ × ℤ) : let θ₁ := tcTheta1Real (2 ^ n) R.card
    let c1 := Real.cos ((K_blk : ℝ) * θ₁)
    let s1 := Real.sin ((K_blk : ℝ) * θ₁)
    tcSlotConveyorVec n d hd R K_blk uFn steps = liftVec (∑ k ∈ Finset.range (2 * d),
        (tcEvolutionReal d c1 s1 uFn steps k) • basis2dTuple (sVec n) (pVec R) hd k) := by
  intro θ₁ c1 s1
  induction steps with
  | zero =>
      funext z
      rw [tcSlotConveyorVec, tcSlotConveyorUnitary, Submonoid.coe_one, Matrix.one_mulVec,
        hadamardUnitary_coe, Matrix.mulVec_single_one, Matrix.col_apply, hadamardMatrix_apply_zero,
        liftVec, Finset.sum_apply]
      have h0_mem : 0 ∈ Finset.range (2 * d) := Finset.mem_range.2 (by omega)
      rw [Finset.sum_eq_single 0]
      · have hlt0 : 0 < 2 * d := by omega
        simp only [tcEvolutionReal, tcInitReal, ↓reduceIte, basis2dTuple, hlt0, Nat.zero_div,
          Nat.zero_mod, Nat.choose_zero_right, Nat.cast_one, Real.sqrt_one, div_one, one_smul,
          tailZeroSubVec, Finset.powersetCard_zero, Finset.sum_singleton, prodSubVec, prodVec,
          Finset.notMem_empty, sVec, Pi.smul_apply, smul_eq_mul, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
        have hp : (1 / √(2 ^ n : ℝ)) ^ d = 1 / √(2 ^ (n * d) : ℝ) := by
          have hpow : (√(2 ^ n : ℝ)) ^ d = √(2 ^ (n * d) : ℝ) := by
            have hsq : ((√(2 ^ n : ℝ)) ^ d) ^ 2 = (2 ^ (n * d) : ℝ) := by
              rw [pow_right_comm, Real.sq_sqrt (by positivity), ← pow_mul]
            calc (√(2 ^ n : ℝ)) ^ d
                = √(((√(2 ^ n : ℝ)) ^ d) ^ 2) := (Real.sqrt_sq (by positivity)).symm
              _ = √(2 ^ (n * d) : ℝ) := by rw [hsq]
          rw [_root_.one_div_pow, hpow]
        rw [hp]; push_cast; ring
      · intro k _ hne
        simp [tcEvolutionReal, tcInitReal, hne]
      · intro hm; exact (hm h0_mem).elim
  | succ t ih =>
      have hstep : tcSlotConveyorVec n d hd R K_blk uFn (t + 1) =
          (tcIntertwinerUnitary n d (uFn t)).1 *ᵥ
            ((localMemSlotReg n d ⟨0, hd⟩).embedMatrix (groverStepUnitary R ^ K_blk).1 *ᵥ
              tcSlotConveyorVec n d hd R K_blk uFn t) := by
        simp only [tcSlotConveyorVec, tcSlotConveyorUnitary, tcSlotPulseUnitary,
          Submonoid.coe_mul, QRegister.embedUnitary_val, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      have hlift_mv : ∀ (M : Matrix (TupleSpace n d) (TupleSpace n d) ℝ) (v : TupleSpace n d → ℝ),
          liftTupleRealMat M *ᵥ liftVec v = liftVec (M *ᵥ v) :=
        fun M v ↦ funext (liftTupleRealMat_mulVec_comp M v)
      rw [hstep, ih, groverHeadEmbed_mulVec_sum_basis2d hd hr1 hrN K_blk]
      dsimp only [tcIntertwinerUnitary, c1, s1, θ₁]
      rw [hlift_mv, tcIntertwinerRealMat_mulVec_sum_basis2d hd hd2 hr1 hrN (uFn t),
        tcEvolutionReal, tcBlockStepReal]
/- ## 4. Orthonormality, Ideal Fiber-Uniform State `ψ_id`, & Telescoped L2 Shift Bound -/
theorem dotProduct_basis2dTuple {n d : ℕ} {v₀ v₁ : Fin (2 ^ n) → ℝ}
    (hv0 : dotProduct v₀ v₀ = 1) (hv1 : dotProduct v₁ v₁ = 1) (hv01 : dotProduct v₀ v₁ = 0)
    (hd : 1 ≤ d) {k₁ k₂ : ℕ} (hk1 : k₁ < 2 * d) (hk2 : k₂ < 2 * d) :
    dotProduct (basis2dTuple v₀ v₁ hd k₁) (basis2dTuple v₀ v₁ hd k₂) =
      if k₁ = k₂ then 1 else 0 := by
  set q₀ : Fin d := ⟨0, hd⟩
  set U := (Finset.univ : Finset (Fin d)).erase q₀
  let mkSub (k : ℕ) (T : Finset (Fin d)) : Finset (Fin d) := if k % 2 = 0 then T else insert q₀ T
  have hform : ∀ k (hk : k < 2 * d), basis2dTuple v₀ v₁ hd k =
        (1 / √(Nat.choose (d - 1) (k / 2) : ℝ)) •
          ∑ T ∈ U.powersetCard (k / 2), prodSubVec v₀ v₁ (mkSub k T) := by
    intro k hk
    by_cases hm : k % 2 = 0
    · simp [basis2dTuple, hk, hm, tailZeroSubVec, mkSub, U, q₀]
    · simp [basis2dTuple, hk, hm, headOneSubVec, mkSub, U, q₀]
  have hmk_inj : ∀ {j₁ j₂ : ℕ} {T₁ T₂ : Finset (Fin d)},
      T₁ ∈ U.powersetCard (j₁ / 2) → T₂ ∈ U.powersetCard (j₂ / 2) →
      (mkSub j₁ T₁ = mkSub j₂ T₂ ↔ j₁ = j₂ ∧ T₁ = T₂) := by
    intro j₁ j₂ T₁ T₂ hT₁ hT₂
    rcases Finset.mem_powersetCard.1 hT₁ with ⟨hT₁U, hT₁c⟩
    rcases Finset.mem_powersetCard.1 hT₂ with ⟨hT₂U, hT₂c⟩
    have hn1 : q₀ ∉ T₁ := fun h ↦ (Finset.mem_erase.1 (hT₁U h)).1 rfl
    have hn2 : q₀ ∉ T₂ := fun h ↦ (Finset.mem_erase.1 (hT₂U h)).1 rfl
    constructor
    · intro hEq
      have her1 : (mkSub j₁ T₁).erase q₀ = T₁ := by
        dsimp [mkSub]; split_ifs
        · exact Finset.erase_eq_of_notMem hn1
        · exact Finset.erase_insert hn1
      have her2 : (mkSub j₂ T₂).erase q₀ = T₂ := by
        dsimp [mkSub]; split_ifs
        · exact Finset.erase_eq_of_notMem hn2
        · exact Finset.erase_insert hn2
      have hTT : T₁ = T₂ := by rw [← her1, hEq, her2]
      have hdiv : j₁ / 2 = j₂ / 2 := by rw [← hT₁c, hTT, hT₂c]
      have hq_iff : (q₀ ∈ mkSub j₁ T₁) ↔ (q₀ ∈ mkSub j₂ T₂) := by rw [hEq]
      have hm1 : (q₀ ∈ mkSub j₁ T₁) ↔ j₁ % 2 ≠ 0 := by
        dsimp [mkSub]; split_ifs with h <;> simp [h, hn1]
      have hm2 : (q₀ ∈ mkSub j₂ T₂) ↔ j₂ % 2 ≠ 0 := by
        dsimp [mkSub]; split_ifs with h <;> simp [h, hn2]
      have hmod : j₁ % 2 = j₂ % 2 := by have hiff := hm1.symm.trans (hq_iff.trans hm2); omega
      exact ⟨by omega, hTT⟩
    · rintro ⟨rfl, rfl⟩; rfl
  rw [hform k₁ hk1, hform k₂ hk2, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    sum_dotProduct]
  simp_rw [dotProduct_sum, dotProduct_prodSubVec hv0 hv1 hv01]
  by_cases hkk : k₁ = k₂
  · subst hkk
    simp only [↓reduceIte]
    have hinner : ∀ T₁ ∈ U.powersetCard (k₁ / 2), (∑ T₂ ∈ U.powersetCard (k₁ / 2),
            if mkSub k₁ T₁ = mkSub k₁ T₂ then (1 : ℝ) else 0) = 1 := by
      intro T₁ hT₁
      rw [Finset.sum_eq_single T₁]
      · simp
      · intro T₂ hT₂ hne
        have hne_mk : mkSub k₁ T₁ ≠ mkSub k₁ T₂ :=
          fun h ↦ hne ((hmk_inj hT₁ hT₂).1 h).2.symm
        simp [hne_mk]
      · intro hm; exact (hm hT₁).elim
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard]
    have hcardU : U.card = d - 1 := by
      dsimp [U]
      rw [Finset.card_erase_of_mem (Finset.mem_univ q₀), Finset.card_univ, Fintype.card_fin]
    rw [hcardU, nsmul_eq_mul, mul_one]; have hc_pos : (0 : ℝ) < (Nat.choose (d - 1) (k₁ / 2) : ℝ) :=
      Nat.cast_pos.2 (Nat.choose_pos (by omega))
    rw [← mul_assoc, div_mul_div_comm, one_mul, Real.mul_self_sqrt hc_pos.le,
      one_div_mul_cancel hc_pos.ne']
  · simp only [hkk, ↓reduceIte]
    have hz : (∑ x ∈ U.powersetCard (k₁ / 2), ∑ x_1 ∈ U.powersetCard (k₂ / 2),
        if mkSub k₁ x = mkSub k₂ x_1 then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun T₁ hT₁ ↦ Finset.sum_eq_zero fun T₂ hT₂ ↦ ?_
      have hne_mk : mkSub k₁ T₁ ≠ mkSub k₂ T₂ :=
        fun h ↦ hkk ((hmk_inj hT₁ hT₂).1 h).1
      simp [hne_mk]
    rw [hz, mul_zero, mul_zero]
theorem dotProduct_sum_basis2dTuple {n d : ℕ} {v₀ v₁ : Fin (2 ^ n) → ℝ}
    (hv0 : dotProduct v₀ v₀ = 1) (hv1 : dotProduct v₁ v₁ = 1) (hv01 : dotProduct v₀ v₁ = 0)
    (hd : 1 ≤ d) (b₁ b₂ : ℕ → ℝ) :
    dotProduct (∑ k ∈ Finset.range (2 * d), b₁ k • basis2dTuple v₀ v₁ hd k)
        (∑ k ∈ Finset.range (2 * d), b₂ k • basis2dTuple v₀ v₁ hd k) =
      ∑ k ∈ Finset.range (2 * d), b₁ k * b₂ k := by
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun k₁ hk₁ ↦ ?_; rw [dotProduct_sum, Finset.sum_eq_single k₁]
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      dotProduct_basis2dTuple hv0 hv1 hv01 hd (Finset.mem_range.1 hk₁) (Finset.mem_range.1 hk₁),
      ite_eq_left rfl, mul_one]
  · intro k₂ hk₂ hne
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      dotProduct_basis2dTuple hv0 hv1 hv01 hd (Finset.mem_range.1 hk₁) (Finset.mem_range.1 hk₂),
      ite_eq_right hne.symm, mul_zero, mul_zero]
  · intro hm; exact (hm hk₁).elim
theorem sum_sq_tcEvolutionReal {d : ℕ} (hd2 : 2 ≤ d) (φ : ℝ) (uFn : ℕ → ℕ → ℤ × ℤ) (steps : ℕ) :
    (∑ k ∈ Finset.range (2 * d),
        (tcEvolutionReal d (Real.cos φ) (Real.sin φ) uFn steps k) ^ 2) = 1 := by
  set c1 := Real.cos φ
  set s1 := Real.sin φ
  have hcs1 : c1 ^ 2 + s1 ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
  have hgrov : ∀ b : ℕ → ℝ, (∑ k ∈ Finset.range (2 * d), (tcGroverStepReal d c1 s1 b k) ^ 2) =
        ∑ k ∈ Finset.range (2 * d), (b k) ^ 2 := by
    intro b
    have hpref : ∀ m ≤ d, (∑ k ∈ Finset.range (2 * m), (tcGroverStepReal d c1 s1 b k) ^ 2) =
          ∑ k ∈ Finset.range (2 * m), (b k) ^ 2 := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
          have h2m : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
          have hg0 : tcGroverStepReal d c1 s1 b (2 * m) = c1 * b (2 * m) - s1 * b (2 * m + 1) := by
            simp [tcGroverStepReal, show 2 * m < 2 * d by omega, show (2 * m) / 2 = m by omega,
              show (2 * m) % 2 = 0 by omega]
          have hg1 : tcGroverStepReal d c1 s1 b (2 * m + 1) =
              s1 * b (2 * m) + c1 * b (2 * m + 1) := by
            simp [tcGroverStepReal, show 2 * m + 1 < 2 * d by omega,
              show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]
          have hpair_sq : (tcGroverStepReal d c1 s1 b (2 * m)) ^ 2 +
              (tcGroverStepReal d c1 s1 b (2 * m + 1)) ^ 2 =
              (b (2 * m)) ^ 2 + (b (2 * m + 1)) ^ 2 := by
            rw [hg0, hg1]
            linear_combination ((b (2 * m)) ^ 2 + (b (2 * m + 1)) ^ 2) * hcs1
          rw [h2m, Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega),
            Finset.sum_range_succ, Finset.sum_range_succ]
          linarith [hpair_sq]
    exact hpref d le_rfl
  have hint : ∀ (uRow : ℕ → ℤ × ℤ) (b : ℕ → ℝ),
      (∑ k ∈ Finset.range (2 * d), (tcIntertwinerStepReal d uRow b k) ^ 2) =
        ∑ k ∈ Finset.range (2 * d), (b k) ^ 2 := by
    intro uRow b
    have hpref : ∀ m ≤ d - 1,
        (∑ k ∈ Finset.range (1 + 2 * m), (tcIntertwinerStepReal d uRow b k) ^ 2) =
          ∑ k ∈ Finset.range (1 + 2 * m), (b k) ^ 2 := by
      intro m hm
      induction m with
      | zero => simp [tcIntertwinerStepReal, show 0 < 2 * d by omega]
      | succ m ih =>
          set w := m + 1
          have hk1 : 1 + 2 * m = 2 * w - 1 := by omega
          have hk2 : 1 + 2 * m + 1 = 2 * w := by omega
          set q : ℚ := ((uRow (w - 1)).1 : ℚ) / ((uRow (w - 1)).2 : ℚ)
          have hcs_q := tcRatCos_sq_add_sin_sq_real q
          have hi1 : tcIntertwinerStepReal d uRow b (2 * w - 1) =
              (tcRatCos q : ℝ) * b (2 * w - 1) - (tcRatSin q : ℝ) * b (2 * w) := by
            simp [tcIntertwinerStepReal, q, show 2 * w - 1 < 2 * d by omega,
              show 2 * w - 1 ≠ 0 by omega, show 2 * w - 1 + 1 < 2 * d by omega,
              show (2 * w - 1 + 1) / 2 = w by omega, show (2 * w - 1) % 2 = 1 by omega]
          have hi2 : tcIntertwinerStepReal d uRow b (2 * w) =
              (tcRatSin q : ℝ) * b (2 * w - 1) + (tcRatCos q : ℝ) * b (2 * w) := by
            simp [tcIntertwinerStepReal, q, show 2 * w < 2 * d by omega,
              show 2 * w ≠ 0 by omega, show 2 * w + 1 < 2 * d by omega,
              show (2 * w + 1) / 2 = w by omega]
          have hpair_sq : (tcIntertwinerStepReal d uRow b (2 * w - 1)) ^ 2 +
              (tcIntertwinerStepReal d uRow b (2 * w)) ^ 2 =
              (b (2 * w - 1)) ^ 2 + (b (2 * w)) ^ 2 := by
            rw [hi1, hi2]
            linear_combination ((b (2 * w - 1)) ^ 2 + (b (2 * w)) ^ 2) * hcs_q
          have h12 : 1 + 2 * (m + 1) = (1 + 2 * m) + 1 + 1 := by omega
          rw [h12, Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega),
            Finset.sum_range_succ, Finset.sum_range_succ, hk2, hk1]
          linarith [hpair_sq]
    have h2d : 2 * d = (1 + 2 * (d - 1)) + 1 := by omega
    have htop : 1 + 2 * (d - 1) = 2 * d - 1 := by omega
    rw [h2d, Finset.sum_range_succ, hpref (d - 1) le_rfl, Finset.sum_range_succ, htop]
    congr 1
    have ht : tcIntertwinerStepReal d uRow b (2 * d - 1) = b (2 * d - 1) := by
      simp [tcIntertwinerStepReal, show 2 * d - 1 < 2 * d by omega,
        show 2 * d - 1 ≠ 0 by omega, show ¬ (2 * d - 1 + 1 < 2 * d) by omega]
    rw [ht]
  induction steps with
  | zero =>
      rw [Finset.sum_eq_single 0]
      · simp [tcEvolutionReal, tcInitReal]
      · intro k _ hne; simp [tcEvolutionReal, tcInitReal, hne]
      · intro hm; exact (hm (Finset.mem_range.2 (by omega))).elim
  | succ t ih => rw [tcEvolutionReal, tcBlockStepReal, hint, hgrov, ih]
/-- Ideal fiber-uniform tuple vector `∑_{k < 2d} a_k • basis2dTuple (uVec R) (mVec R) hd k`. -/
noncomputable def idealTupleVec {n d : ℕ} (hd : 1 ≤ d) (R : Finset (Fin (2 ^ n)))
    (a : ℕ → ℝ) : TupleSpace n d → ℝ :=
  ∑ k ∈ Finset.range (2 * d), a k • basis2dTuple (uVec R) (mVec R) hd k
theorem sum_normSq_liftVec {n d : ℕ} (v : TupleSpace n d → ℝ) :
    (∑ z : Fin (2 ^ (n * d)), Complex.normSq (liftVec v z)) = dotProduct v v := by
  simp_rw [liftVec, Complex.normSq_ofReal]
  exact (regsEquiv n d).sum_comp fun f ↦ v f * v f
theorem idealTupleVec_eq_of_hitRegs_eq {n d : ℕ} (hd : 1 ≤ d) (R : Finset (Fin (2 ^ n)))
    (a : ℕ → ℝ) {z₁ z₂ : Fin (2 ^ (n * d))} (h : tcHitRegs n d R z₁ = tcHitRegs n d R z₂) :
    idealTupleVec hd R a (regsEquiv n d z₁) = idealTupleVec hd R a (regsEquiv n d z₂) := by
  have hmem : ∀ q : Fin d, ((localMemSlotReg n d q).extractIndex z₁ ∈ R) ↔
        ((localMemSlotReg n d q).extractIndex z₂ ∈ R) := by
    intro q
    simpa [tcHitRegs] using Finset.ext_iff.1 h q
  have hsub : ∀ S : Finset (Fin d), prodSubVec (uVec R) (mVec R) S (regsEquiv n d z₁) =
        prodSubVec (uVec R) (mVec R) S (regsEquiv n d z₂) := by
    intro S
    simp only [prodSubVec, prodVec, regsEquiv_apply]
    refine Finset.prod_congr rfl fun q _ ↦ ?_
    by_cases hq : q ∈ S
    · simp only [hq, ↓reduceIte, mVec]
      by_cases hr : (localMemSlotReg n d q).extractIndex z₁ ∈ R
      · rw [ite_eq_left hr, ite_eq_left ((hmem q).1 hr)]
      · rw [ite_eq_right hr, ite_eq_right (mt (hmem q).2 hr)]
    · simp only [hq, ↓reduceIte, uVec]
      by_cases hr : (localMemSlotReg n d q).extractIndex z₁ ∈ R
      · rw [ite_eq_left hr, ite_eq_left ((hmem q).1 hr)]
      · rw [ite_eq_right hr, ite_eq_right (mt (hmem q).2 hr)]
  simp only [idealTupleVec, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  congr 1
  unfold basis2dTuple
  split_ifs
  · simp only [Pi.smul_apply, tailZeroSubVec, Finset.sum_apply, hsub]
  · simp only [Pi.smul_apply, headOneSubVec, Finset.sum_apply, hsub]
  · rfl
theorem prodSubVec_uVec_mVec_support {n d : ℕ} (R : Finset (Fin (2 ^ n)))
    (S : Finset (Fin d)) {f : TupleSpace n d} (hnz : prodSubVec (uVec R) (mVec R) S f ≠ 0) :
    Finset.univ.filter (fun q : Fin d ↦ f q ∈ R) = S := by
  rw [prodSubVec, prodVec, Finset.prod_ne_zero_iff] at hnz
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have hq := hnz q (Finset.mem_univ q)
  by_cases hqs : q ∈ S
  · simp only [hqs, ↓reduceIte, mVec] at hq
    by_cases hfr : f q ∈ R
    · simp [hfr, hqs]
    · simp [hfr] at hq
  · simp only [hqs, ↓reduceIte, uVec] at hq
    by_cases hfr : f q ∈ R
    · simp [hfr] at hq
    · simp [hfr, hqs]
theorem sum_normSq_idealTupleVec_hitWeight {n d : ℕ} (hd : 1 ≤ d) (hd2 : 2 ≤ d)
    {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n)
    (a : ℕ → ℝ) {w : ℕ} (hw : w ≤ d) :
    (∑ z : Fin (2 ^ (n * d)) with (tcHitRegs n d R z).card = w,
        Complex.normSq (liftVec (idealTupleVec hd R a) z)) =
      tcWeightProbReal d a w := by
  let filt (v : TupleSpace n d → ℝ) (f : TupleSpace n d) : ℝ :=
    if (Finset.univ.filter fun q : Fin d ↦ f q ∈ R).card = w then v f else 0
  have hsum_eq :
      (∑ z : Fin (2 ^ (n * d)) with (tcHitRegs n d R z).card = w,
          Complex.normSq (liftVec (idealTupleVec hd R a) z)) =
        dotProduct (filt (idealTupleVec hd R a)) (filt (idealTupleVec hd R a)) := by
    rw [Finset.sum_filter, dotProduct]
    simp_rw [tcHitRegs_eq_filter_regsEquiv, liftVec, Complex.normSq_ofReal]
    rw [Equiv.sum_comp (regsEquiv n d) (fun f : TupleSpace n d ↦
      if (Finset.univ.filter fun q : Fin d ↦ f q ∈ R).card = w then
        idealTupleVec hd R a f * idealTupleVec hd R a f else 0)]
    refine Finset.sum_congr rfl fun f _ ↦ ?_; dsimp [filt]
    split_ifs <;> ring
  have hfilt_prod : ∀ S : Finset (Fin d), filt (prodSubVec (uVec R) (mVec R) S) =
        if S.card = w then prodSubVec (uVec R) (mVec R) S else 0 := by
    intro S
    funext f
    dsimp [filt]
    by_cases hnz : prodSubVec (uVec R) (mVec R) S f = 0
    · split_ifs <;> simp [hnz]
    · rw [prodSubVec_uVec_mVec_support R S hnz]
      split_ifs <;> rfl
  have hfilt_basis : ∀ k (hk : k < 2 * d), filt (basis2dTuple (uVec R) (mVec R) hd k) =
        (if k / 2 + k % 2 = w then (1 : ℝ) else 0) • basis2dTuple (uVec R) (mVec R) hd k := by
    intro k hk
    have hlin_sum : ∀ {α : Type} (s : Finset α) (g : α → TupleSpace n d → ℝ),
        filt (∑ x ∈ s, g x) = ∑ x ∈ s, filt (g x) := by
      intro α s g
      funext f
      simp only [filt, Finset.sum_apply]
      by_cases hc : (Finset.univ.filter fun q : Fin d ↦ f q ∈ R).card = w <;> simp [hc]
    have hlin_smul : ∀ (c : ℝ) (v : TupleSpace n d → ℝ), filt (c • v) = c • filt v := by
      intro c v; funext f; dsimp [filt]; split_ifs <;> simp
    by_cases hm : k % 2 = 0
    · have hwt : k / 2 + k % 2 = k / 2 := by omega
      have hb : basis2dTuple (uVec R) (mVec R) hd k = (1 / √(Nat.choose (d - 1) (k / 2) : ℝ)) •
            tailZeroSubVec (uVec R) (mVec R) hd (k / 2) := by
        simp [basis2dTuple, hk, hm]
      rw [hwt, hb, hlin_smul, tailZeroSubVec, hlin_sum]
      by_cases hcw : k / 2 = w
      · simp only [hcw, ↓reduceIte, one_smul]
        congr 1
        refine Finset.sum_congr rfl fun T hT ↦ ?_
        rw [hfilt_prod, (Finset.mem_powersetCard.1 hT).2, ite_eq_left rfl]
      · simp only [hcw, ↓reduceIte, zero_smul]
        have hz : (∑ x ∈ ((Finset.univ : Finset (Fin d)).erase ⟨0, hd⟩).powersetCard (k / 2),
            filt (prodSubVec (uVec R) (mVec R) x)) = 0 := by
          refine Finset.sum_eq_zero fun T hT ↦ ?_
          rw [hfilt_prod, (Finset.mem_powersetCard.1 hT).2, ite_eq_right hcw]
        rw [hz, smul_zero]
    · have hwt : k / 2 + k % 2 = k / 2 + 1 := by omega
      have hb : basis2dTuple (uVec R) (mVec R) hd k = (1 / √(Nat.choose (d - 1) (k / 2) : ℝ)) •
            headOneSubVec (uVec R) (mVec R) hd (k / 2 + 1) := by
        simp [basis2dTuple, hk, hm]
      rw [hwt, hb, hlin_smul, headOneSubVec, Nat.add_sub_cancel, hlin_sum]
      have hcard_ins : ∀ T ∈ ((Finset.univ : Finset (Fin d)).erase ⟨0, hd⟩).powersetCard (k / 2),
          (insert ⟨0, hd⟩ T).card = k / 2 + 1 := by
        intro T hT
        rcases Finset.mem_powersetCard.1 hT with ⟨hTU, hTc⟩
        have hnot : ⟨0, hd⟩ ∉ T := fun h ↦ (Finset.mem_erase.1 (hTU h)).1 rfl
        rw [Finset.card_insert_of_notMem hnot, hTc]
      by_cases hcw : k / 2 + 1 = w
      · simp only [hcw, ↓reduceIte, one_smul]
        congr 1
        refine Finset.sum_congr rfl fun T hT ↦ ?_
        rw [hfilt_prod, hcard_ins T hT, hcw, ite_eq_left rfl]
      · simp only [hcw, ↓reduceIte, zero_smul]
        have hz : (∑ x ∈ ((Finset.univ : Finset (Fin d)).erase ⟨0, hd⟩).powersetCard (k / 2),
            filt (prodSubVec (uVec R) (mVec R) (insert ⟨0, hd⟩ x))) = 0 := by
          refine Finset.sum_eq_zero fun T hT ↦ ?_; rw [hfilt_prod, hcard_ins T hT, ite_eq_right hcw]
        rw [hz, smul_zero]
  have hfilt_ideal : filt (idealTupleVec hd R a) = ∑ k ∈ Finset.range (2 * d),
        (if k / 2 + k % 2 = w then a k else 0) • basis2dTuple (uVec R) (mVec R) hd k := by
    have h1 : filt (idealTupleVec hd R a) =
        ∑ k ∈ Finset.range (2 * d), a k • filt (basis2dTuple (uVec R) (mVec R) hd k) := by
      funext f
      simp only [filt, idealTupleVec, Finset.sum_apply, Pi.smul_apply]
      by_cases hc : (Finset.univ.filter fun q : Fin d ↦ f q ∈ R).card = w <;> simp [hc]
    rw [h1]
    refine Finset.sum_congr rfl fun k hk ↦ ?_; rw [hfilt_basis k (Finset.mem_range.1 hk), smul_smul]
    split_ifs <;> simp
  rcases uVec_mVec_orthonormal hr1 hrN with ⟨huu, hmm, hum⟩
  rw [hsum_eq, hfilt_ideal, dotProduct_sum_basis2dTuple huu hmm hum hd]; have hsq_term : ∀ k : ℕ,
      (if k / 2 + k % 2 = w then a k else 0) * (if k / 2 + k % 2 = w then a k else 0) =
        if k / 2 + k % 2 = w then (a k) ^ 2 else 0 := by
    intro k; split_ifs <;> ring
  simp_rw [hsq_term]
  by_cases hw0 : w = 0
  · subst hw0
    rw [Finset.sum_eq_single 0]
    · simp [tcWeightProbReal]
    · intro k _ hne
      have hne_wt : k / 2 + k % 2 ≠ 0 := by omega
      rw [ite_eq_right hne_wt]
    · intro hm; exact (hm (Finset.mem_range.2 (by omega))).elim
  · by_cases hwd : w < d
    · rw [← Finset.sum_filter]
      have hpair_set : (Finset.range (2 * d)).filter (fun k ↦ k / 2 + k % 2 = w) =
          {2 * w - 1, 2 * w} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [hpair_set, Finset.sum_pair (by omega)]; simp [tcWeightProbReal, hw0, hwd]
    · have hweq : w = d := by omega
      rw [hweq, Finset.sum_eq_single (2 * d - 1)]
      · have hwt : (2 * d - 1) / 2 + (2 * d - 1) % 2 = d := by omega
        have hdne0 : d ≠ 0 := by omega
        simp [tcWeightProbReal, hwt, hdne0]
      · intro k hk hne
        have hlt : k < 2 * d := Finset.mem_range.1 hk
        have hne_wt : k / 2 + k % 2 ≠ d := by omega
        rw [ite_eq_right hne_wt]
      · intro hm; exact (hm (Finset.mem_range.2 (by omega))).elim
/-- Single-register orthogonal rotation mapping `uVec R ↦ sVec n` and `mVec R ↦ pVec R`. -/
noncomputable def rotAlphaMat {n : ℕ} (R : Finset (Fin (2 ^ n))) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  Matrix.of fun i j ↦
    (if i = j then 1 else 0) +
      (Real.cos (alphaAngle n R) - 1) * (uVec R i * uVec R j + mVec R i * mVec R j) +
      Real.sin (alphaAngle n R) * (mVec R i * uVec R j - uVec R i * mVec R j)
theorem rotAlphaMat_props {n : ℕ} {R : Finset (Fin (2 ^ n))}
    (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n) : rotAlphaMat R *ᵥ uVec R = sVec n ∧
    rotAlphaMat R *ᵥ mVec R = pVec R ∧ (∀ v : Fin (2 ^ n) → ℝ,
      dotProduct (rotAlphaMat R *ᵥ v) (rotAlphaMat R *ᵥ v) = dotProduct v v) ∧
    (∀ v : Fin (2 ^ n) → ℝ, dotProduct (rotAlphaMat R *ᵥ v - v) (rotAlphaMat R *ᵥ v - v) ≤
        4 * ((R.card : ℝ) / (2 ^ n : ℝ)) * dotProduct v v) := by
  rcases uVec_mVec_orthonormal hr1 hrN with ⟨huu, hmm, hum⟩
  have hmu : dotProduct (mVec R) (uVec R) = 0 := by rw [dotProduct_comm, hum]
  set u := uVec R
  set m := mVec R
  set α := alphaAngle n R
  set cα := Real.cos α
  set sα := Real.sin α
  have hcs : cα ^ 2 + sα ^ 2 = 1 := Real.cos_sq_add_sin_sq α
  have hact : ∀ v : Fin (2 ^ n) → ℝ, rotAlphaMat R *ᵥ v =
        v + ((cα - 1) * dotProduct u v - sα * dotProduct m v) • u +
          (sα * dotProduct u v + (cα - 1) * dotProduct m v) • m := by
    intro v
    funext i
    simp only [Matrix.mulVec, dotProduct, rotAlphaMat, Matrix.of_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have hsum_id : (∑ j : Fin (2 ^ n), (if i = j then (1 : ℝ) else 0) * v j) = v i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne; simp [hne.symm]
      · intro hm'; exact (hm' (Finset.mem_univ i)).elim
    have hsplit : ∀ j : Fin (2 ^ n),
        ((if i = j then (1 : ℝ) else 0) + (cα - 1) * (u i * u j + m i * m j) +
            sα * (m i * u j - u i * m j)) * v j = (if i = j then 1 else 0) * v j +
            ((cα - 1) * u i + sα * m i) * (u j * v j) +
            ((cα - 1) * m i - sα * u i) * (m j * v j) := by
      intro j; ring
    change (∑ j : Fin (2 ^ n),
        ((if i = j then (1 : ℝ) else 0) + (cα - 1) * (u i * u j + m i * m j) +
          sα * (m i * u j - u i * m j)) * v j) = _
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsum_id]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hact u, huu, hmu]
    funext x
    rw [sVec_eq_comb hr1 hrN x]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, u, m, cα, sα, α]; ring
  · rw [hact m, hum, hmm]
    funext x
    simp only [pVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, u, m, cα, sα, α]; ring
  · intro v
    set au := dotProduct u v
    set am := dotProduct m v
    set w := v - au • u - am • m
    have huw : dotProduct u w = 0 := by
      simp only [w, dotProduct_sub, dotProduct_smul, smul_eq_mul, huu, hum]; dsimp [au]; ring
    have hmw : dotProduct m w = 0 := by
      simp only [w, dotProduct_sub, dotProduct_smul, smul_eq_mul, hmu, hmm]; dsimp [am]; ring
    have hwu : dotProduct w u = 0 := by rw [dotProduct_comm, huw]
    have hwm : dotProduct w m = 0 := by rw [dotProduct_comm, hmw]
    have hv_eq : v = w + au • u + am • m := by dsimp [w]; abel
    have hrv_eq : rotAlphaMat R *ᵥ v = w + (cα * au - sα * am) • u + (sα * au + cα * am) • m := by
      rw [hact v]
      funext i
      have hi := congrFun hv_eq i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, au, am] at hi ⊢; linarith
    have horth_norm : ∀ x y : ℝ, dotProduct (w + x • u + y • m) (w + x • u + y • m) =
          dotProduct w w + x ^ 2 + y ^ 2 := by
      intro x y
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        huu, hmm, hum, hmu, huw, hmw, hwu, hwm]
      ring
    rw [hrv_eq, horth_norm, hv_eq, horth_norm]
    linear_combination (au ^ 2 + am ^ 2) * hcs
  · intro v
    set au := dotProduct u v
    set am := dotProduct m v
    set w := v - au • u - am • m
    have huw : dotProduct u w = 0 := by
      simp only [w, dotProduct_sub, dotProduct_smul, smul_eq_mul, huu, hum]; dsimp [au]; ring
    have hmw : dotProduct m w = 0 := by
      simp only [w, dotProduct_sub, dotProduct_smul, smul_eq_mul, hmu, hmm]; dsimp [am]; ring
    have hwu : dotProduct w u = 0 := by rw [dotProduct_comm, huw]
    have hwm : dotProduct w m = 0 := by rw [dotProduct_comm, hmw]
    have hv_eq : v = w + au • u + am • m := by dsimp [w]; abel
    have hv_norm : dotProduct v v = dotProduct w w + au ^ 2 + am ^ 2 := by
      rw [hv_eq]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        huu, hmm, hum, hmu, huw, hmw, hwu, hwm]
      ring
    have hdiff : rotAlphaMat R *ᵥ v - v =
        ((cα - 1) * au - sα * am) • u + (sα * au + (cα - 1) * am) • m := by
      rw [hact v]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, au, am]; ring
    have hdiff_norm : dotProduct (rotAlphaMat R *ᵥ v - v) (rotAlphaMat R *ᵥ v - v) =
        (2 - 2 * cα) * (au ^ 2 + am ^ 2) := by
      rw [hdiff]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        huu, hmm, hum, hmu]
      linear_combination (au ^ 2 + am ^ 2) * hcs
    have hw_nn : 0 ≤ dotProduct w w :=
      Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (w i)
    have hc_lb : 1 - (R.card : ℝ) / (2 ^ n : ℝ) ≤ cα := by
      have hcos := (sin_cos_alphaAngle hrN).2
      have hN_pos : (0 : ℝ) < (2 ^ n : ℝ) := pow_pos (by norm_num) n
      set x := (R.card : ℝ) / (2 ^ n : ℝ)
      have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hN_pos.le
      have hx1 : x ≤ 1 := (div_le_one hN_pos).2 (by exact_mod_cast hrN.le)
      have hc_eq : cα = √(1 - x) := by
        dsimp [cα, α, x]
        have hNr : (0 : ℝ) ≤ (2 ^ n : ℝ) - (R.card : ℝ) := by
          have : (R.card : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hrN
          linarith
        rw [hcos, ← Real.sqrt_div hNr, sub_div, div_self hN_pos.ne']
      rw [hc_eq]
      have h1x_nn : 0 ≤ 1 - x := by linarith
      have hsq_le : (1 - x) ^ 2 ≤ 1 - x := by nlinarith
      simpa [Real.sqrt_sq h1x_nn] using Real.sqrt_le_sqrt hsq_le
    have hr_nn : 0 ≤ (R.card : ℝ) / (2 ^ n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (pow_pos (by norm_num) n).le
    have h2c_ub : 2 - 2 * cα ≤ 4 * ((R.card : ℝ) / (2 ^ n : ℝ)) := by linarith
    have h2c_nn : 0 ≤ 2 - 2 * cα := by linarith [Real.cos_le_one α]
    rw [hdiff_norm, hv_norm]
    calc (2 - 2 * cα) * (au ^ 2 + am ^ 2)
        ≤ (2 - 2 * cα) * (dotProduct w w + au ^ 2 + am ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) h2c_nn
      _ ≤ (4 * ((R.card : ℝ) / (2 ^ n : ℝ))) * (dotProduct w w + au ^ 2 + am ^ 2) :=
          mul_le_mul_of_nonneg_right h2c_ub (by nlinarith [hw_nn, sq_nonneg au, sq_nonneg am])
/-- Fiber decomposition splitting `TupleSpace n d` along coordinate `q: Fin d`. -/
def fiberZeroEquiv (n d : ℕ) (q : Fin d) :
    {f : TupleSpace n d // f q = 0} × Fin (2 ^ n) ≃ TupleSpace n d where
  toFun p := Function.update p.1.1 q p.2
  invFun h := (⟨Function.update h q 0, Function.update_self q 0 h⟩, h q)
  left_inv := fun ⟨⟨f, hf⟩, x⟩ ↦ by
    ext1
    · ext1
      dsimp only; rw [Function.update_idem, ← hf, Function.update_eq_self]
    · dsimp only; exact Function.update_self q x f
  right_inv h := by dsimp only; rw [Function.update_idem, Function.update_eq_self]
/-- Apply `rotAlphaMat R` along coordinate `q: Fin d` of `W: TupleSpace n d → ℝ`. -/
noncomputable def applyRotCoord {n d : ℕ} (R : Finset (Fin (2 ^ n))) (q : Fin d)
    (W : TupleSpace n d → ℝ) (f : TupleSpace n d) : ℝ :=
  (rotAlphaMat R *ᵥ fun y ↦ W (Function.update f q y)) (f q)
theorem applyRotCoord_norm_and_shift {n d : ℕ} {R : Finset (Fin (2 ^ n))}
    (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n) (q : Fin d) (W : TupleSpace n d → ℝ) :
    dotProduct (applyRotCoord R q W) (applyRotCoord R q W) = dotProduct W W ∧
    dotProduct (applyRotCoord R q W - W) (applyRotCoord R q W - W) ≤
      4 * ((R.card : ℝ) / (2 ^ n : ℝ)) * dotProduct W W := by
  rcases rotAlphaMat_props hr1 hrN with ⟨_, _, hnorm, hshift⟩
  have hslice : ∀ (f₀ : {f : TupleSpace n d // f q = 0}) (x : Fin (2 ^ n)),
      applyRotCoord R q W (Function.update f₀.1 q x) =
        (rotAlphaMat R *ᵥ fun y ↦ W (Function.update f₀.1 q y)) x := by
    intro f₀ x
    simp only [applyRotCoord, Function.update_self, Function.update_idem]
  have hdecomp : ∀ g : TupleSpace n d → ℝ, dotProduct g g = ∑ f₀ : {f : TupleSpace n d // f q = 0},
          ∑ x : Fin (2 ^ n), g (Function.update f₀.1 q x) * g (Function.update f₀.1 q x) := by
    intro g
    rw [dotProduct, ← Equiv.sum_comp (fiberZeroEquiv n d q) (fun h ↦ g h * g h),
      Fintype.sum_prod_type]
    rfl
  constructor
  · rw [hdecomp (applyRotCoord R q W), hdecomp W]
    refine Finset.sum_congr rfl fun f₀ _ ↦ ?_
    simp_rw [hslice f₀]
    exact hnorm (fun y ↦ W (Function.update f₀.1 q y))
  · rw [hdecomp (applyRotCoord R q W - W), hdecomp W, Finset.mul_sum]
    refine Finset.sum_le_sum fun f₀ _ ↦ ?_
    have hsub_slice : ∀ x : Fin (2 ^ n), (applyRotCoord R q W - W) (Function.update f₀.1 q x) =
          (rotAlphaMat R *ᵥ (fun y ↦ W (Function.update f₀.1 q y)) -
            (fun y ↦ W (Function.update f₀.1 q y))) x := by
      intro x
      simp only [Pi.sub_apply, hslice f₀]
    simp_rw [hsub_slice]
    exact hshift (fun y ↦ W (Function.update f₀.1 q y))
theorem applyRotCoord_prodVec {n d : ℕ} (R : Finset (Fin (2 ^ n))) (q : Fin d)
    (F : Fin d → Fin (2 ^ n) → ℝ) :
    applyRotCoord R q (prodVec F) = prodVec (Function.update F q (rotAlphaMat R *ᵥ F q)) := by
  funext f
  simp only [applyRotCoord, Matrix.mulVec, dotProduct, prodVec]
  have hsplit : ∀ y : Fin (2 ^ n), (∏ i : Fin d, F i (Function.update f q y i)) =
        F q y * ∏ i ∈ Finset.univ.erase q, F i (f i) := by
    intro y
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp_rw [hsplit, ← mul_assoc, ← Finset.sum_mul]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi ↦ ?_; rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
/-- Sequentially apply `applyRotCoord R ⟨0, _⟩.. ⟨m - 1, _⟩` on `TupleSpace n d`. -/
noncomputable def prefixRotVec {n d : ℕ} (R : Finset (Fin (2 ^ n))) :
    ℕ → (TupleSpace n d → ℝ) → (TupleSpace n d → ℝ)
  | 0, W => W
  | m + 1, W =>
      if hm : m < d then applyRotCoord R ⟨m, hm⟩ (prefixRotVec R m W) else prefixRotVec R m W
theorem prefixRotVec_linear {n d : ℕ} (R : Finset (Fin (2 ^ n))) (m : ℕ) :
    (∀ u v : TupleSpace n d → ℝ,
      prefixRotVec R m (u + v) = prefixRotVec R m u + prefixRotVec R m v) ∧
    (∀ (c : ℝ) (v : TupleSpace n d → ℝ), prefixRotVec R m (c • v) = c • prefixRotVec R m v) := by
  induction m with
  | zero => exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | succ m ih =>
      rcases ih with ⟨hadd, hsmul⟩
      by_cases hm : m < d
      · refine ⟨fun u v ↦ ?_, fun c v ↦ ?_⟩
        · funext f
          simp only [Pi.add_apply, prefixRotVec, hm, ↓reduceDIte, hadd, applyRotCoord]
          exact congrFun (Matrix.mulVec_add (rotAlphaMat R)
            (fun y ↦ prefixRotVec R m u (Function.update f ⟨m, hm⟩ y))
            (fun y ↦ prefixRotVec R m v (Function.update f ⟨m, hm⟩ y))) (f ⟨m, hm⟩)
        · funext f
          simp only [Pi.smul_apply, prefixRotVec, hm, ↓reduceDIte, hsmul, applyRotCoord]
          exact congrFun (Matrix.mulVec_smul (rotAlphaMat R) c
            (fun y ↦ prefixRotVec R m v (Function.update f ⟨m, hm⟩ y))) (f ⟨m, hm⟩)
      · simp [prefixRotVec, hm, hadd, hsmul]
theorem prefixRotVec_sum {n d : ℕ} (R : Finset (Fin (2 ^ n))) (m : ℕ)
    {α : Type*} (s : Finset α) (g : α → TupleSpace n d → ℝ) :
    prefixRotVec R m (∑ x ∈ s, g x) = ∑ x ∈ s, prefixRotVec R m (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h0 := (prefixRotVec_linear (n := n) (d := d) R m).2 0 0
      simpa using h0
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, (prefixRotVec_linear R m).1, ih, Finset.sum_insert ha]
theorem prefixRotVec_d_idealTupleVec {n d : ℕ} (hd : 1 ≤ d)
    {R : Finset (Fin (2 ^ n))} (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n) (a : ℕ → ℝ) :
    prefixRotVec R d (idealTupleVec hd R a) =
      ∑ k ∈ Finset.range (2 * d), a k • basis2dTuple (sVec n) (pVec R) hd k := by
  rcases rotAlphaMat_props hr1 hrN with ⟨hru, hrm, _, _⟩
  have hsub : ∀ (m : ℕ) (_ : m ≤ d) (S : Finset (Fin d)),
      prefixRotVec R m (prodSubVec (uVec R) (mVec R) S) = prodVec fun q : Fin d ↦
          if q.val < m then (if q ∈ S then pVec R else sVec n)
          else (if q ∈ S then mVec R else uVec R) := by
    intro m hm S
    induction m with
    | zero => simp [prefixRotVec, prodSubVec]
    | succ m ih =>
        have hlt : m < d := by omega
        have hp : prefixRotVec R (m + 1) (prodSubVec (uVec R) (mVec R) S) =
            applyRotCoord R ⟨m, hlt⟩ (prefixRotVec R m (prodSubVec (uVec R) (mVec R) S)) := by
          simp [prefixRotVec, hlt]
        rw [hp, ih (by omega), applyRotCoord_prodVec]
        congr 1
        funext q
        by_cases hqm : q = ⟨m, hlt⟩
        · subst hqm
          simp only [Function.update_self, lt_self_iff_false, ↓reduceIte, Nat.lt_succ_self]
          by_cases hqS : (⟨m, hlt⟩ : Fin d) ∈ S <;> simp [hqS, hru, hrm]
        · have hval_ne : q.val ≠ m := fun h ↦ hqm (Fin.ext h); rw [Function.update_of_ne hqm]
          have hiff : (q.val < m + 1) ↔ (q.val < m) := by omega
          by_cases hlt_q : q.val < m
          · simp [hlt_q, hiff.2 hlt_q]
          · simp [hlt_q, mt hiff.1 hlt_q]
  have hsub_d : ∀ S : Finset (Fin d),
      prefixRotVec R d (prodSubVec (uVec R) (mVec R) S) = prodSubVec (sVec n) (pVec R) S := by
    intro S
    rw [hsub d le_rfl S, prodSubVec]
    congr 1
    funext q
    simp [q.isLt]
  rw [idealTupleVec, prefixRotVec_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_; rw [(prefixRotVec_linear R d).2]
  congr 1
  have hk_lt : k < 2 * d := Finset.mem_range.1 hk
  by_cases hm : k % 2 = 0
  · simp [basis2dTuple, hk_lt, hm, tailZeroSubVec, (prefixRotVec_linear R d).2,
      prefixRotVec_sum, hsub_d]
  · simp [basis2dTuple, hk_lt, hm, headOneSubVec, (prefixRotVec_linear R d).2,
      prefixRotVec_sum, hsub_d]
theorem l2_shift_prefixRotVec_d {n d : ℕ} (hd : 1 ≤ d) {R : Finset (Fin (2 ^ n))}
    (hr1 : 1 ≤ R.card) (hrN : R.card < 2 ^ n) (W : TupleSpace n d → ℝ) (hW : dotProduct W W = 1) :
    dotProduct (prefixRotVec R d W - W) (prefixRotVec R d W - W) ≤
      4 * (d : ℝ) ^ 2 * ((R.card : ℝ) / (2 ^ n : ℝ)) := by
  have hnorm_m : ∀ m : ℕ, dotProduct (prefixRotVec R m W) (prefixRotVec R m W) = 1 := by
    intro m
    induction m with
    | zero => exact hW
    | succ m ih =>
        by_cases hm : m < d
        · have hp : prefixRotVec R (m + 1) W = applyRotCoord R ⟨m, hm⟩ (prefixRotVec R m W) := by
            simp [prefixRotVec, hm]
          rw [hp, (applyRotCoord_norm_and_shift hr1 hrN ⟨m, hm⟩ _).1, ih]
        · simp [prefixRotVec, hm, ih]
  have hstep_m : ∀ m (hm : m < d), dotProduct (prefixRotVec R (m + 1) W - prefixRotVec R m W)
        (prefixRotVec R (m + 1) W - prefixRotVec R m W) ≤ 4 * ((R.card : ℝ) / (2 ^ n : ℝ)) := by
    intro m hm
    have hp : prefixRotVec R (m + 1) W = applyRotCoord R ⟨m, hm⟩ (prefixRotVec R m W) := by
      simp [prefixRotVec, hm]
    rw [hp]; have hb := (applyRotCoord_norm_and_shift hr1 hrN ⟨m, hm⟩ (prefixRotVec R m W)).2
    rwa [hnorm_m m, mul_one] at hb
  have htele : ∀ (k : ℕ) (f : TupleSpace n d), prefixRotVec R k W f - W f =
        ∑ m ∈ Finset.range k, (prefixRotVec R (m + 1) W f - prefixRotVec R m W f) := by
    intro k f
    induction k with
    | zero => simp [prefixRotVec]
    | succ k ih => rw [Finset.sum_range_succ, ← ih]; ring
  have hpt : ∀ f : TupleSpace n d, (prefixRotVec R d W f - W f) ^ 2 ≤
        (d : ℝ) * ∑ m ∈ Finset.range d,
          (prefixRotVec R (m + 1) W f - prefixRotVec R m W f) ^ 2 := by
    intro f
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range d)
      (fun _ ↦ (1 : ℝ)) (fun m ↦ prefixRotVec R (m + 1) W f - prefixRotVec R m W f)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
    rwa [← htele d f] at hcs
  have hsq_dot : ∀ u : TupleSpace n d → ℝ, dotProduct u u = ∑ f : TupleSpace n d, (u f) ^ 2 := by
    intro u; simp [dotProduct, sq]
  rw [hsq_dot]
  calc (∑ f : TupleSpace n d, ((prefixRotVec R d W - W) f) ^ 2)
      ≤ ∑ f : TupleSpace n d, (d : ℝ) * ∑ m ∈ Finset.range d,
            (prefixRotVec R (m + 1) W f - prefixRotVec R m W f) ^ 2 :=
        Finset.sum_le_sum fun f _ ↦ hpt f
    _ = (d : ℝ) * ∑ m ∈ Finset.range d, dotProduct (prefixRotVec R (m + 1) W - prefixRotVec R m W)
            (prefixRotVec R (m + 1) W - prefixRotVec R m W) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun m _ ↦ ?_; simp [dotProduct, sq]
    _ ≤ (d : ℝ) * ∑ m ∈ Finset.range d, 4 * ((R.card : ℝ) / (2 ^ n : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum fun m hm ↦ hstep_m m (Finset.mem_range.1 hm)
    _ = 4 * (d : ℝ) ^ 2 * ((R.card : ℝ) / (2 ^ n : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
end TensorConveyorBasis2d
/-- Single-slot `2d`-basis evolution and terminal `(s_N, v_R) → (u_{Rᶜ}, u_R)` fiber-uniform
  approximation: `tcSlotConveyorVec` is within L2 distance `2 * (steps + 1) * d * √(|R| /
  2^n)` of
  a unit state `ψ_id` whose Born probabilities `Complex.normSq (ψ_id z)` depend only on the
  hit
  register subset `tcHitRegs n d R z` and sum to `tcWeightProbReal d a w` on each weight `w
  ≤ d`. -/
theorem tcSlotConveyorVec_ideal_approx {n d : ℕ} (hn : 700 ≤ n) (hd2 : 2 ≤ d) (hd12 : d ≤ 12)
    (R : Finset (Fin (2 ^ n))) (hr1 : 1 ≤ R.card) (hr1024 : R.card ≤ 1024)
    (K_blk steps : ℕ) (hsteps : steps ≤ 250) (uFn : ℕ → ℕ → ℤ × ℤ)
    (hu : ∀ t < steps, ∀ j < d - 1, (uFn t j).2 ≠ 0) : let θ₁ := tcTheta1Real (2 ^ n) R.card
    let a := tcEvolutionReal d
      (Real.cos ((K_blk : ℝ) * θ₁)) (Real.sin ((K_blk : ℝ) * θ₁)) uFn steps
    ∃ ψ_id : Fin (2 ^ (n * d)) → ℂ, (∑ z : Fin (2 ^ (n * d)), Complex.normSq (ψ_id z) = 1) ∧
      (∑ z : Fin (2 ^ (n * d)),
          Complex.normSq (tcSlotConveyorVec n d (by omega) R K_blk uFn steps z - ψ_id z) ≤
        ((2 * ((steps + 1 : ℕ) : ℝ) * (d : ℝ)) * √((R.card : ℝ) / (2 ^ n : ℝ))) ^ 2) ∧
      (∀ z₁ z₂ : Fin (2 ^ (n * d)), tcHitRegs n d R z₁ = tcHitRegs n d R z₂ →
          Complex.normSq (ψ_id z₁) = Complex.normSq (ψ_id z₂)) ∧ (∀ w ≤ d,
        (∑ z : Fin (2 ^ (n * d)) with (tcHitRegs n d R z).card = w,
            Complex.normSq (ψ_id z)) =
          tcWeightProbReal d a w) := by
  have _ : d ≤ 12 ∧ steps ≤ 250 ∧ (∀ t < steps, ∀ j < d - 1, (uFn t j).2 ≠ 0) := ⟨hd12, hsteps, hu⟩
  intro θ₁ a
  have hd1 : 1 ≤ d := by omega
  have hrN : R.card < 2 ^ n := by
    have h11 : 1024 < 2 ^ 11 := by norm_num
    have hpow : 2 ^ 11 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega); omega
  open TensorConveyorBasis2d in
  refine ⟨liftVec (idealTupleVec hd1 R a), ?_, ?_, ?_, ?_⟩
  · rcases uVec_mVec_orthonormal hr1 hrN with ⟨huu, hmm, hum⟩
    rw [sum_normSq_liftVec, idealTupleVec, dotProduct_sum_basis2dTuple huu hmm hum hd1]
    simp_rw [← sq]
    exact sum_sq_tcEvolutionReal hd2 ((K_blk : ℝ) * θ₁) uFn steps
  · rcases uVec_mVec_orthonormal hr1 hrN with ⟨huu, hmm, hum⟩
    have hideal_norm : dotProduct (idealTupleVec hd1 R a) (idealTupleVec hd1 R a) = 1 := by
      rw [idealTupleVec, dotProduct_sum_basis2dTuple huu hmm hum hd1]
      simp_rw [← sq]
      exact sum_sq_tcEvolutionReal hd2 ((K_blk : ℝ) * θ₁) uFn steps
    have hconv_eq := tcSlotConveyorVec_eq_sum_basis2d hd1 hd2 hr1 hrN K_blk steps uFn
    have hrot_eq := prefixRotVec_d_idealTupleVec hd1 hr1 hrN a
    have hdiff_vec : ∀ z : Fin (2 ^ (n * d)),
        tcSlotConveyorVec n d hd1 R K_blk uFn steps z - liftVec (idealTupleVec hd1 R a) z =
          liftVec (prefixRotVec R d (idealTupleVec hd1 R a) - idealTupleVec hd1 R a) z := by
      intro z
      rw [hconv_eq, ← hrot_eq]; simp [liftVec, a, θ₁]
    simp_rw [hdiff_vec]
    rw [sum_normSq_liftVec]
    have hl2 := l2_shift_prefixRotVec_d hd1 hr1 hrN (idealTupleVec hd1 R a) hideal_norm
    have hsq_rhs : 4 * (d : ℝ) ^ 2 * ((R.card : ℝ) / (2 ^ n : ℝ)) ≤
          ((2 * ((steps + 1 : ℕ) : ℝ) * (d : ℝ)) * √((R.card : ℝ) / (2 ^ n : ℝ))) ^ 2 := by
      have hratio_nn : (0 : ℝ) ≤ (R.card : ℝ) / (2 ^ n : ℝ) := by positivity
      have hsq_rt : √((R.card : ℝ) / (2 ^ n : ℝ)) ^ 2 = (R.card : ℝ) / (2 ^ n : ℝ) :=
        Real.sq_sqrt hratio_nn
      have h1_le : (1 : ℝ) ≤ ((steps + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos steps
      have h1_sq : (1 : ℝ) ≤ ((steps + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      calc 4 * (d : ℝ) ^ 2 * ((R.card : ℝ) / (2 ^ n : ℝ))
          = 4 * 1 * (d : ℝ) ^ 2 * ((R.card : ℝ) / (2 ^ n : ℝ)) := by ring
        _ ≤ 4 * (((steps + 1 : ℕ) : ℝ) ^ 2) * (d : ℝ) ^ 2 * ((R.card : ℝ) / (2 ^ n : ℝ)) := by
            have : (0 : ℝ) ≤ (d : ℝ) ^ 2 * ((R.card : ℝ) / (2 ^ n : ℝ)) := by positivity
            nlinarith
        _ = ((2 * ((steps + 1 : ℕ) : ℝ) * (d : ℝ)) * √((R.card : ℝ) / (2 ^ n : ℝ))) ^ 2 := by
            rw [mul_pow, hsq_rt]; ring
    exact hl2.trans hsq_rhs
  · intro z₁ z₂ h
    simp only [liftVec]; rw [idealTupleVec_eq_of_hitRegs_eq hd1 R a h]
  · intro w hw
    exact sum_normSq_idealTupleVec_hitWeight hd1 hd2 hr1 hrN a hw
end QuantumComputation.Specs.GroverFindAll
end
end Sec_TensorConveyorBasis2d
