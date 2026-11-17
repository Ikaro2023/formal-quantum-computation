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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
import Mathlib.Data.Fintype.CardEmbedding
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.WeakDickeCore
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingZoomK2Base
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingMidPZoomEval
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingMidPZoomCerts
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.MpzGHZoomTables
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.MpzGHZoomCertsBK8

/-
 High-Rank L <= 112 Middle-p Collision-Zoom 6-Cell Companion (`MpzGHZoomCertsB`).
-/

@[expose] public section

namespace QuantumComputation.Specs.GroverFindAll.MpzGHMidP

open scoped NNReal NNRat

/-- Computable cell selector for the 6 selected `L <= 112` middle-`p` Collision-Zoom cells. -/
def isMpzGHMidPCell (m k : ℕ) : Bool :=
  (m == 64 && k == 4) || (m == 128 && k == 4) || (m == 256 && k == 4) ||
    (m == 512 && k == 4) || (m == 512 && k == 8) || (m == 1024 && k == 8)

/-- Register width `m * (n + 1) + k * n` matching `masterWDZoomQubits`. -/
abbrev mpzGHMidPQubits (n m k : ℕ) : ℕ :=
  m * (n + 1) + k * n

/-- Exact coprime asymptotic relative-cost table across the 6 `L <= 112` middle-`p` cells. -/
def relCostMpzGHMidP (m k : ℕ) : ℚ≥0 :=
  if m == 64 && k == 4 then NNRat.divNat 971953019 2784457050
  else if m == 128 && k == 4 then NNRat.divNat 156832149 464076175
  else if m == 256 && k == 4 then NNRat.divNat 462221306 1392228525
  else if m == 512 && k == 4 then NNRat.divNat 183092327 556891410
  else if m == 512 && k == 8 then NNRat.divNat 484469487 2185718399
  else if m == 1024 && k == 8 then NNRat.divNat 951881197 4371436798
  else 1

/-- Every covered `MpzGHMidP` cell lies on `groverGrid × groverGrid`. -/
theorem isMpzGHMidPCell_isGridCell {m k : ℕ} (h : isMpzGHMidPCell m k = true) :
    GroverFindAll.isGridCell m k = true := by
  unfold isMpzGHMidPCell at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

end QuantumComputation.Specs.GroverFindAll.MpzGHMidP

end

section MpzMidPFastS1
namespace QuantumComputation.Specs.DickeSol.MpzS1
open QuantumComputation.Specs.DickeSol
open QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
private lemma cond_eq_ite_s1 {α : Type*} (b : Bool) (P : Prop) [Decidable P] (hb : b = true ↔ P) (x
    y : α) : cond b x y = (if P then x else y) := by
  cases b with
  | true => exact (ite_eq_left (hb.mp rfl)).symm
  | false => exact (ite_eq_right (mt hb.mpr Bool.false_ne_true)).symm
private lemma cond_eq_ite_congr_s1 {α : Type*} (b : Bool) (P : Prop) [Decidable P] (hb : b = true ↔
P) {x x' y : α} (hx : x = x') : cond b x y = (if P then x' else y) := by
  rw [hx]; exact cond_eq_ite_s1 b P hb x' y
private def fastBeqZS1 (a b : ℤ) : Bool := midPBleZ a b && midPBleZ b a
private lemma fastBeqZ_iff_s1 (a b : ℤ) : fastBeqZS1 a b = true ↔ a = b := by
  unfold fastBeqZS1; simp only [Bool.and_eq_true, midPBleZ_iff]; omega
private def fastBinomS1 (r w : ℕ) : ℕ := midPLitNat (r.descFactorial w / w.factorial) id
private lemma fastBinom_eq_s1 (r w : ℕ) : fastBinomS1 r w = ghBinom r w := by
  conv_lhs => unfold fastBinomS1; rw [midPLitNat_eq]
  (conv_rhs => unfold ghBinom; rw [ghForceNat_eq]); rfl
private def _sB : ℕ := 1000000000000000
private def _s2B : ℕ := 2000000000000000
private def _maxAngZ : ℤ := Int.ofNat (Nat.mul 1024 _sB)
private lemma _sB_eq : (Int.ofNat _sB : ℤ) = (wdScale : ℤ) := rfl
private lemma _s2B_eq : (Int.ofNat _s2B : ℤ) = 2 * (wdScale : ℤ) := rfl
private lemma _sB_midP : Int.ofNat _sB = midPScaleZ := rfl
private lemma _s2B_midP : Int.ofNat _s2B = Int.mul 2 midPScaleZ := rfl
private def _zNegNat (n : ℕ) : ℤ :=
  cond (Nat.ble 1 n) (midPLitNat (Nat.sub n 1) Int.negSucc) 0
private lemma _zNegNat_eq (n : ℕ) : _zNegNat n = -(n : ℤ) := by
  unfold _zNegNat; rw [midPLitNat_eq]; cases n <;> rfl
private def _zNeg : ℤ → ℤ
  | Int.ofNat a => _zNegNat a
  | Int.negSucc a => midPLitNat (Nat.add a 1) Int.ofNat
private lemma _zNeg_eq (x : ℤ) : _zNeg x = -x := by
  cases x with
  | ofNat a => exact _zNegNat_eq a
  | negSucc a => dsimp only [_zNeg]; rw [midPLitNat_eq]; rfl
private def _subNN (a b : ℕ) : ℤ :=
  cond (Nat.ble a b) (_zNegNat (Nat.sub b a)) (midPLitNat (Nat.sub a b) Int.ofNat)
private lemma _subNN_eq (a b : ℕ) : _subNN a b = (a : ℤ) - (b : ℤ) := by
  unfold _subNN; rw [_zNegNat_eq, midPLitNat_eq]
  cases h : Nat.ble a b <;>
    simp only [Bool.cond_true, Bool.cond_false, Bool.eq_false_iff, ne_eq,
      Nat.ble_eq, Nat.sub_eq, Int.ofNat_eq_natCast] at h ⊢ <;> omega
private def _zAdd : ℤ → ℤ → ℤ
  | Int.ofNat a, Int.ofNat b => midPLitNat (Nat.add a b) Int.ofNat
  | Int.ofNat a, Int.negSucc b => _subNN a (Nat.add b 1)
  | Int.negSucc a, Int.ofNat b => _subNN b (Nat.add a 1)
  | Int.negSucc a, Int.negSucc b => midPLitNat (Nat.add (Nat.add a b) 1) Int.negSucc
private lemma _zAdd_eq (x y : ℤ) : _zAdd x y = x + y := by
  cases x <;> cases y <;>
    simp only [_zAdd, _subNN_eq, midPLitNat_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private lemma _zAdd_int (x y : ℤ) : _zAdd x y = Int.add x y := _zAdd_eq x y
private def _zSub (x y : ℤ) : ℤ := _zAdd x (_zNeg y)
private lemma _zSub_eq (x y : ℤ) : _zSub x y = x - y := by
  unfold _zSub; rw [_zAdd_eq, _zNeg_eq]; omega
private lemma _zSub_int (x y : ℤ) : _zSub x y = Int.sub x y := _zSub_eq x y
private def _zMul : ℤ → ℤ → ℤ
  | Int.ofNat a, Int.ofNat b => Int.ofNat (Nat.mul a b)
  | Int.ofNat a, Int.negSucc b => _zNegNat (Nat.mul a (Nat.add b 1))
  | Int.negSucc a, Int.ofNat b => _zNegNat (Nat.mul (Nat.add a 1) b)
  | Int.negSucc a, Int.negSucc b => Int.ofNat (Nat.mul (Nat.add a 1) (Nat.add b 1))
private lemma _zMul_eq (x y : ℤ) : _zMul x y = x * y := by
  cases x <;> cases y <;>
    simp only [_zMul, _zNegNat_eq, Nat.mul_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> push_cast <;> ring
private lemma _zMul_int (x y : ℤ) : _zMul x y = Int.mul x y := _zMul_eq x y
private def _zDivFl (x : ℤ) (d : ℕ) : ℤ :=
  cond (Nat.ble 1 d)
    (match x with
     | Int.ofNat a => Int.ofNat (Nat.div a d)
     | Int.negSucc a => Int.negSucc (Nat.div a d)) 0
private lemma _zDivFl_eq (x : ℤ) (d : ℕ) : _zDivFl x d = wdDivFloor x (Int.ofNat d) := by
  cases d with
  | zero => simp [_zDivFl, wdDivFloor]
  | succ _ => cases x <;> rfl
private def _zDivCl (x : ℤ) (d : ℕ) : ℤ := _zNeg (_zDivFl (_zNeg x) d)
private lemma _zDivCl_eq (x : ℤ) (d : ℕ) : _zDivCl x d = wdDivCeil x (Int.ofNat d) := by
  unfold _zDivCl wdDivCeil; rw [_zNeg_eq, _zDivFl_eq, _zNeg_eq]; rfl
private lemma _ble_eq_ghBle (a b : ℤ) : midPBleZ a b = ghBleZ a b := by
  rw [ghBleZ_eq_decide]; by_cases h : a ≤ b
  · rw [decide_eq_true h]; exact (midPBleZ_iff a b).mpr h
  · rw [decide_eq_false h]; exact Bool.eq_false_iff.mpr (mt (midPBleZ_iff a b).mp h)
private lemma _ble_false {a b : ℤ} (h : midPBleZ a b = false) : b < a := by
  have h' : ¬(a ≤ b) := fun hab ↦ by rw [(midPBleZ_iff a b).mpr hab] at h; cases h
  omega
private def _minZ (a b : ℤ) : ℤ := cond (midPBleZ a b) a b
private def _maxZ (a b : ℤ) : ℤ := cond (midPBleZ a b) b a
private lemma _minZ_eq_gh (a b : ℤ) : _minZ a b = ghMinZ a b := by
  unfold _minZ ghMinZ; rw [_ble_eq_ghBle]
private lemma _maxZ_eq_gh (a b : ℤ) : _maxZ a b = ghMaxZ a b := by
  unfold _maxZ ghMaxZ; rw [_ble_eq_ghBle]
private lemma _minZ_eq (a b : ℤ) : _minZ a b = min a b := (_minZ_eq_gh a b).trans (ghMinZ_eq a b)
private lemma _maxZ_eq (a b : ℤ) : _maxZ a b = max a b := (_maxZ_eq_gh a b).trans (ghMaxZ_eq a b)
private def _seq2Z {α : Type*} (a b : ℤ) (k : ℤ → ℤ → α) : α :=
  midPSeqInt a fun a' ↦ midPSeqInt b fun b' ↦ k a' b'
private lemma _seq2Z_eq {α : Type*} (a b : ℤ) (k : ℤ → ℤ → α) : _seq2Z a b k = k a b := by
  simp only [_seq2Z, midPSeqInt_eq]
private def _seq4Z {α : Type*} (a b c d : ℤ) (k : ℤ → ℤ → ℤ → ℤ → α) : α :=
  _seq2Z a b fun a' b' ↦ _seq2Z c d fun c' d' ↦ k a' b' c' d'
private lemma _seq4Z_eq {α : Type*} (a b c d : ℤ) (k : ℤ → ℤ → ℤ → ℤ → α) :
    _seq4Z a b c d k = k a b c d := by
  simp only [_seq4Z, _seq2Z_eq]
private def _ivDivK {α : Type*} (lo hi : ℤ) (k : ℤ → ℤ → α) : α :=
  _seq2Z (_zDivFl lo _sB) (_zDivCl hi _sB) k
private lemma _ivDivK_eq {α : Type*} (lo hi : ℤ) (k : ℤ → ℤ → α) :
    _ivDivK lo hi k = k (wdDivFloor lo (wdScale : ℤ)) (wdDivCeil hi (wdScale : ℤ)) := by
  unfold _ivDivK; simp only [_seq2Z_eq, _zDivFl_eq, _zDivCl_eq, _sB_eq]
private def _ivMul4K {α : Type*} (xl xh yl yh : ℤ) (k : ℤ → ℤ → α) : α :=
  _seq4Z (_zMul xl yl) (_zMul xl yh) (_zMul xh yl) (_zMul xh yh) fun p1 p2 p3 p4 ↦
    _ivDivK (_minZ (_minZ p1 p2) (_minZ p3 p4)) (_maxZ (_maxZ p1 p2) (_maxZ p3 p4)) k
private lemma _ivMul4K_eq {α : Type*} (xl xh yl yh : ℤ) (k : ℤ → ℤ → α) :
    _ivMul4K xl xh yl yh k = k (ghMulIV (xl, xh) (yl, yh)).1 (ghMulIV (xl, xh) (yl, yh)).2 := by
  unfold _ivMul4K
  simp only [_seq4Z_eq, _ivDivK_eq, ghMulIV_eq, wdMul, _zMul_eq, _minZ_eq, _maxZ_eq]
private lemma _min4_eq {p1 p2 p3 p4 m : ℤ} (hm : m = p1 ∨ m = p2 ∨ m = p3 ∨ m = p4)
    (h1 : m ≤ p1) (h2 : m ≤ p2) (h3 : m ≤ p3) (h4 : m ≤ p4) :
    min (min p1 p2) (min p3 p4) = m := by
  apply le_antisymm
  · rcases hm with rfl | rfl | rfl | rfl
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact le_min (le_min h1 h2) (le_min h3 h4)
private lemma _max4_eq {p1 p2 p3 p4 m : ℤ} (hm : m = p1 ∨ m = p2 ∨ m = p3 ∨ m = p4)
    (h1 : p1 ≤ m) (h2 : p2 ≤ m) (h3 : p3 ≤ m) (h4 : p4 ≤ m) :
    max (max p1 p2) (max p3 p4) = m := by
  apply le_antisymm
  · exact max_le (max_le h1 h2) (max_le h3 h4)
  · rcases hm with rfl | rfl | rfl | rfl
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
private def _ivMul2K {α : Type*} (a b c d : ℤ) (k : ℤ → ℤ → α) : α :=
  _seq2Z (_zMul a b) (_zMul c d) fun lo hi ↦ _ivDivK lo hi k
private lemma _ivMul2K_eq {α : Type*} {xl xh yl yh lo hi : ℤ} (k : ℤ → ℤ → α)
    (hlo : lo = xl * yl ∨ lo = xl * yh ∨ lo = xh * yl ∨ lo = xh * yh)
    (l1 : lo ≤ xl * yl) (l2 : lo ≤ xl * yh) (l3 : lo ≤ xh * yl) (l4 : lo ≤ xh * yh)
    (hhi : hi = xl * yl ∨ hi = xl * yh ∨ hi = xh * yl ∨ hi = xh * yh)
    (u1 : xl * yl ≤ hi) (u2 : xl * yh ≤ hi) (u3 : xh * yl ≤ hi) (u4 : xh * yh ≤ hi)
    (a b c d : ℤ) (hab : a * b = lo) (hcd : c * d = hi) :
    _ivMul2K a b c d k = k (ghMulIV (xl, xh) (yl, yh)).1 (ghMulIV (xl, xh) (yl, yh)).2 := by
  unfold _ivMul2K; simp only [_seq2Z_eq, _zMul_eq, hab, hcd, _ivDivK_eq, ghMulIV_eq, wdMul]
  rw [_min4_eq hlo l1 l2 l3 l4, _max4_eq hhi u1 u2 u3 u4]
private def _ivMulK {α : Type*} (xl xh yl yh : ℤ) (k : ℤ → ℤ → α) : α :=
  cond (midPBleZ xl xh && midPBleZ yl yh)
    (cond (midPBleZ 0 xl)
      (cond (midPBleZ 0 yl) (_ivMul2K xl yl xh yh k)
        (cond (midPBleZ yh 0) (_ivMul2K xh yl xl yh k) (_ivMul2K xh yl xh yh k)))
      (cond (midPBleZ xh 0)
        (cond (midPBleZ 0 yl) (_ivMul2K xl yh xh yl k)
          (cond (midPBleZ yh 0) (_ivMul2K xh yh xl yl k) (_ivMul2K xl yh xl yl k)))
        (cond (midPBleZ 0 yl) (_ivMul2K xl yh xh yh k)
          (cond (midPBleZ yh 0) (_ivMul2K xh yl xl yl k) (_ivMul4K xl xh yl yh k)))))
    (_ivMul4K xl xh yl yh k)
private lemma _ivMulK_eq {α : Type*} (xl xh yl yh : ℤ) (k : ℤ → ℤ → α) :
    _ivMulK xl xh yl yh k = k (ghMulIV (xl, xh) (yl, yh)).1 (ghMulIV (xl, xh) (yl, yh)).2 := by
  unfold _ivMulK
  cases h1 : midPBleZ xl xh
  · exact _ivMul4K_eq xl xh yl yh k
  · cases h2 : midPBleZ yl yh
    · exact _ivMul4K_eq xl xh yl yh k
    · have hx := (midPBleZ_iff xl xh).mp h1; have hy := (midPBleZ_iff yl yh).mp h2
      cases h3 : midPBleZ 0 xl
      · have hxl := _ble_false h3
        cases h4 : midPBleZ xh 0
        · have hxh := _ble_false h4
          cases h5 : midPBleZ 0 yl
          · have hyl := _ble_false h5
            cases h6 : midPBleZ yh 0
            · exact _ivMul4K_eq xl xh yl yh k
            · have hyh := (midPBleZ_iff yh 0).mp h6
              exact _ivMul2K_eq k (Or.inr (Or.inr (Or.inl rfl)))
                (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
                (Or.inl rfl) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
                xh yl xl yl rfl rfl
          · have hyl := (midPBleZ_iff 0 yl).mp h5
            exact _ivMul2K_eq k (Or.inr (Or.inl rfl))
              (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              (Or.inr (Or.inr (Or.inr rfl)))
              (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              xl yh xh yh rfl rfl
        · have hxh := (midPBleZ_iff xh 0).mp h4
          cases h5 : midPBleZ 0 yl
          · have hyl := _ble_false h5
            cases h6 : midPBleZ yh 0
            · have hyh := _ble_false h6
              exact _ivMul2K_eq k (Or.inr (Or.inl rfl))
                (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
                (Or.inl rfl) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
                xl yh xl yl rfl rfl
            · have hyh := (midPBleZ_iff yh 0).mp h6
              exact _ivMul2K_eq k (Or.inr (Or.inr (Or.inr rfl)))
                (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
                (Or.inl rfl) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
                xh yh xl yl rfl rfl
          · have hyl := (midPBleZ_iff 0 yl).mp h5
            exact _ivMul2K_eq k (Or.inr (Or.inl rfl))
              (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              (Or.inr (Or.inr (Or.inl rfl)))
              (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              xl yh xh yl rfl rfl
      · have hxl := (midPBleZ_iff 0 xl).mp h3
        cases h5 : midPBleZ 0 yl
        · have hyl := _ble_false h5
          cases h6 : midPBleZ yh 0
          · have hyh := _ble_false h6
            exact _ivMul2K_eq k (Or.inr (Or.inr (Or.inl rfl)))
              (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              (Or.inr (Or.inr (Or.inr rfl)))
              (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              xh yl xh yh rfl rfl
          · have hyh := (midPBleZ_iff yh 0).mp h6
            exact _ivMul2K_eq k (Or.inr (Or.inr (Or.inl rfl)))
              (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              (Or.inr (Or.inl rfl)) (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              xh yl xl yh rfl rfl
        · have hyl := (midPBleZ_iff 0 yl).mp h5
          exact _ivMul2K_eq k (Or.inl rfl)
            (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
            (Or.inr (Or.inr (Or.inr rfl)))
            (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
            xl yl xh yh rfl rfl
private def _ivSqK {α : Type*} (xl xh : ℤ) (k : ℤ → ℤ → α) : α :=
  _seq2Z (_zMul xl xl) (_zMul xh xh) fun p1 p2 ↦
    _seq2Z (cond (midPBleZ xl 0 && midPBleZ 0 xh) 0 (_zDivFl (_minZ p1 p2) _sB))
      (_zDivCl (_maxZ p1 p2) _sB) k
private lemma _ivSqK_eq {α : Type*} (xl xh : ℤ) (k : ℤ → ℤ → α) :
    _ivSqK xl xh k = k (ghSqIV (xl, xh)).1 (ghSqIV (xl, xh)).2 := by
  unfold _ivSqK ghSqIV
  simp only [_seq2Z_eq, _zMul_int, _ble_eq_ghBle, _minZ_eq_gh, _maxZ_eq_gh,
    _zDivFl_eq, _zDivCl_eq, _sB_eq]
private def _sqHi (xl xh : ℤ) : ℤ :=
  _seq2Z (_zMul xl xl) (_zMul xh xh) fun p1 p2 ↦ _zDivCl (_maxZ p1 p2) _sB
private lemma _sqHi_eq (xl xh : ℤ) : _sqHi xl xh = (ghSqIV (xl, xh)).2 := by
  unfold _sqHi ghSqIV; simp only [_seq2Z_eq, _zMul_int, _maxZ_eq_gh, _zDivCl_eq, _sB_eq]
private def uCAbs2Hi (z : WDCVal) : ℤ := _zAdd (_sqHi z.1.1 z.1.2) (_sqHi z.2.1 z.2.2)
private lemma uCAbs2Hi_eq (z : WDCVal) : uCAbs2Hi z = wdCAbs2Hi z := by
  rcases z with ⟨⟨rl, rh⟩, ⟨il, ih⟩⟩
  unfold uCAbs2Hi wdCAbs2Hi; rw [_zAdd_eq, _sqHi_eq, _sqHi_eq]
private def uRatK {α : Type*} (num : ℤ) (den : ℕ) (k : WDIVal → α) : α :=
  midPSeqInt (_zMul num (Int.ofNat _sB)) fun ns ↦
    _seq2Z (_zDivFl ns den) (_zDivCl ns den) fun lo hi ↦ k (lo, hi)
private lemma uRatK_eq {α : Type*} (num : ℤ) (den : ℕ) (k : WDIVal → α) :
    uRatK num den k = k (wdRat num den) := by
  have hsB : _sB = wdScale := rfl
  unfold uRatK wdRat
  simp only [midPSeqInt_eq, _seq2Z_eq, _zMul_eq, hsB, _zDivFl_eq, _zDivCl_eq, Int.ofNat_eq_natCast]
private def uMulIVK {α : Type*} (x y : WDIVal) (k : WDIVal → α) : α :=
  _ivMulK x.1 x.2 y.1 y.2 fun lo hi ↦ k (lo, hi)
private lemma uMulIVK_eq {α : Type*} (x y : WDIVal) (k : WDIVal → α) :
    uMulIVK x y k = k (midPFastMulIV x y) := by
  rcases x with ⟨xl, xh⟩; rcases y with ⟨yl, yh⟩
  unfold uMulIVK; rw [_ivMulK_eq, midPFastMulIV_eq]
private def _trigBaseK {α : Type*} (ul uh : ℤ) (k : ℤ → ℤ → ℤ → ℤ → α) : α :=
  _seq2Z (_zMul ul ul) (_zMul uh uh) fun ql qh ↦
    _seq2Z (_zDivFl ql _sB) (_zDivCl qh _sB) fun ul2 uh2 ↦
    midPSeqInt (_zDivCl (_zMul uh2 uh2) _sB) fun uh4 ↦
    _seq2Z (_zDivCl (_zMul uh2 uh) _sB) (_zDivFl (_zMul ul2 ul) _sB) fun uh3 ul3 ↦
    midPSeqInt (_zDivCl (_zMul uh4 uh) _sB) fun uh5 ↦
    _seq4Z (_zSub (Int.ofNat _sB) (_zDivCl qh _s2B))
      (_zAdd (_zSub (Int.ofNat _sB) (_zDivFl ql _s2B)) (_zDivCl uh4 24))
      (_maxZ 0 (_zSub ul (_zDivCl uh3 6)))
      (_zAdd (_zSub uh (_zDivFl ul3 6)) (_zDivCl uh5 120)) k
private lemma _trigBaseK_eq {α : Type*} (ul uh : ℤ) (k : ℤ → ℤ → ℤ → ℤ → α) :
    _trigBaseK ul uh k = ghTrigBaseCPS (ul, uh) (fun c s ↦ k c.1 c.2 s.1 s.2) := by
  unfold _trigBaseK ghTrigBaseCPS
  simp only [_seq2Z_eq, midPSeqInt_eq, _seq4Z_eq, ghSeqIV_eq, _zMul_int, _zSub_eq,
    _zAdd_eq, _maxZ_eq_gh, _zDivFl_eq, _zDivCl_eq, _sB_eq, _s2B_eq]
  rfl
private def _dblIterK {α : Type*} : ℕ → ℤ → ℤ → ℤ → ℤ → (ℤ → ℤ → ℤ → ℤ → α) → α
  | 0, cl, ch, sl, sh, k => k cl ch sl sh
  | n + 1, cl, ch, sl, sh, k =>
      _ivSqK cl ch fun c2l c2h ↦ _ivSqK sl sh fun s2l s2h ↦
      _seq2Z (_zSub c2l s2h) (_zSub c2h s2l) fun cl' ch' ↦
      _ivMulK sl sh cl ch fun msl msh ↦
      _seq2Z (_zMul 2 msl) (_zMul 2 msh) fun sl' sh' ↦ _dblIterK n cl' ch' sl' sh' k
private lemma _dblIterK_eq {α : Type*} :
    ∀ (n : ℕ) (cl ch sl sh : ℤ) (k : ℤ → ℤ → ℤ → ℤ → α),
      _dblIterK n cl ch sl sh k =
        midPDoubleAngleIterCPS n (cl, ch) (sl, sh) (fun c s ↦ k c.1 c.2 s.1 s.2)
  | 0, _, _, _, _, _ => rfl
  | n + 1, cl, ch, sl, sh, k => by
      simp only [_dblIterK, _ivSqK_eq, _seq2Z_eq, _ivMulK_eq, midPDoubleAngleIterCPS,
        midPSeqIV_eq, wdSub, wdScaleNat, midPFastMulIV_eq, _zSub_eq, _zMul_eq]
      exact _dblIterK_eq n _ _ _ _ k
private def fastTrigCPSS1 {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) : α :=
  _seq2Z (_zDivFl x.1 1024) (_zDivCl x.2 1024) fun ul uh ↦
    _trigBaseK ul uh fun c0l c0h s0l s0h ↦
      _dblIterK 10 c0l c0h s0l s0h fun cl ch sl sh ↦ k (cl, ch) (sl, sh)
private lemma fastTrigCPS_eq_s1 {α : Type*} (x : WDIVal) (k : WDIVal → WDIVal → α) :
    fastTrigCPSS1 x k = midPTrigCPS x k := by
  rcases x with ⟨xl, xh⟩; unfold fastTrigCPSS1 midPTrigCPS
  simp only [_seq2Z_eq, midPSeqIV_eq, _zDivFl_eq, _zDivCl_eq, _trigBaseK_eq]
  have h1024 : (Int.ofNat 1024 : ℤ) = 1024 := rfl; rw [h1024]
  refine congrArg (ghTrigBaseCPS _) (funext fun c0 ↦ funext fun s0 ↦ ?_)
  exact _dblIterK_eq 10 c0.1 c0.2 s0.1 s0.2 fun cl ch sl sh ↦ k (cl, ch) (sl, sh)
private def uCRMulK {α : Type*} (rIV : WDIVal) (z : WDCVal) (k : WDCVal → α) : α :=
  _ivMulK rIV.1 rIV.2 z.1.1 z.1.2 fun rl rh ↦
    _ivMulK rIV.1 rIV.2 z.2.1 z.2.2 fun il ih ↦ k ((rl, rh), (il, ih))
private lemma uCRMulK_eq {α : Type*} (rIV : WDIVal) (z : WDCVal) (k : WDCVal → α) :
    uCRMulK rIV z k = k (midPFastCRMul rIV z) := by
  rcases rIV with ⟨rl, rh⟩; rcases z with ⟨⟨zrl, zrh⟩, ⟨zil, zih⟩⟩
  unfold uCRMulK midPFastCRMul; simp only [_ivMulK_eq, midPFastMulIV_eq]
private def uCMulK {α : Type*} (a b : WDCVal) (k : WDCVal → α) : α :=
  _ivMulK a.1.1 a.1.2 b.1.1 b.1.2 fun acl ach ↦
  _ivMulK a.2.1 a.2.2 b.2.1 b.2.2 fun bdl bdh ↦
  _ivMulK a.1.1 a.1.2 b.2.1 b.2.2 fun adl adh ↦
  _ivMulK a.2.1 a.2.2 b.1.1 b.1.2 fun bcl bch ↦
  _seq4Z (_zSub acl bdh) (_zSub ach bdl) (_zAdd adl bcl) (_zAdd adh bch)
    fun rl rh il ih ↦ k ((rl, rh), (il, ih))
private lemma uCMulK_eq {α : Type*} (a b : WDCVal) (k : WDCVal → α) :
    uCMulK a b k = k (midPFastCMul a b) := by
  rcases a with ⟨⟨al, ah⟩, ⟨bl, bh⟩⟩; rcases b with ⟨⟨cl, ch⟩, ⟨dl, dh⟩⟩
  unfold uCMulK midPFastCMul
  simp only [_ivMulK_eq, _seq4Z_eq, midPSeqIV_eq, midPFastMulIV_eq, _zSub_int, _zAdd_int]
private def uRotSubK {α : Type*} (c s : WDIVal) (a b : WDCVal) (k : WDCVal → α) : α :=
  _ivMulK c.1 c.2 a.1.1 a.1.2 fun carl carh ↦
  _ivMulK c.1 c.2 a.2.1 a.2.2 fun cail caih ↦
  _ivMulK s.1 s.2 b.1.1 b.1.2 fun sbrl sbrh ↦
  _ivMulK s.1 s.2 b.2.1 b.2.2 fun sbil sbih ↦
  _seq4Z (_zSub carl sbrh) (_zSub carh sbrl) (_zSub cail sbih) (_zSub caih sbil)
    fun rl rh il ih ↦ k ((rl, rh), (il, ih))
private lemma uRotSubK_eq {α : Type*} (c s : WDIVal) (a b : WDCVal) (k : WDCVal → α) :
    uRotSubK c s a b k = k (midPFastCSub (midPFastCRMul c a) (midPFastCRMul s b)) := by
  rcases c with ⟨cl, ch⟩; rcases s with ⟨sl, sh⟩
  rcases a with ⟨⟨arl, arh⟩, ⟨ail, aih⟩⟩; rcases b with ⟨⟨brl, brh⟩, ⟨bil, bih⟩⟩
  unfold uRotSubK midPFastCSub midPFastCRMul
  simp only [_ivMulK_eq, _seq4Z_eq, midPFastMulIV_eq, _zSub_int]
private def uRotAddK {α : Type*} (c s : WDIVal) (a b : WDCVal) (k : WDCVal → α) : α :=
  _ivMulK s.1 s.2 a.1.1 a.1.2 fun sarl sarh ↦
  _ivMulK s.1 s.2 a.2.1 a.2.2 fun sail saih ↦
  _ivMulK c.1 c.2 b.1.1 b.1.2 fun cbrl cbrh ↦
  _ivMulK c.1 c.2 b.2.1 b.2.2 fun cbil cbih ↦
  _seq4Z (_zAdd sarl cbrl) (_zAdd sarh cbrh) (_zAdd sail cbil) (_zAdd saih cbih)
    fun rl rh il ih ↦ k ((rl, rh), (il, ih))
private lemma uRotAddK_eq {α : Type*} (c s : WDIVal) (a b : WDCVal) (k : WDCVal → α) :
    uRotAddK c s a b k = k (midPFastCAdd (midPFastCRMul s a) (midPFastCRMul c b)) := by
  rcases c with ⟨cl, ch⟩; rcases s with ⟨sl, sh⟩
  rcases a with ⟨⟨arl, arh⟩, ⟨ail, aih⟩⟩; rcases b with ⟨⟨brl, brh⟩, ⟨bil, bih⟩⟩
  unfold uRotAddK midPFastCAdd midPFastCRMul
  simp only [_ivMulK_eq, _seq4Z_eq, midPFastMulIV_eq, _zAdd_int]
private def uCombineZip : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, c, s, l, r =>
      midPUnconsC l fun l0 _ ↦ midPUnconsC r fun r0 _ ↦
        uRotSubK c s l0 r0 fun y0 ↦ uRotAddK c s l0 r0 fun y1 ↦ [y0, y1]
  | t + 1, c, s, l, r =>
      midPUnconsC l fun l0 ltl ↦ midPUnconsC r fun r0 rtl ↦
        uRotSubK c s l0 r0 fun y0 ↦ y0 :: uCombineZip t c s ltl rtl
private lemma uCombineZip_eq :
    ∀ (t : ℕ) (c s : WDIVal) (l r : List WDCVal), uCombineZip t c s l r = midPCombineZip t c s l r
  | 0, c, s, l, r => by
      cases l <;> cases r <;>
        simp only [uCombineZip, midPCombineZip, midPUnconsC, uRotSubK_eq, uRotAddK_eq]
  | t + 1, c, s, l, r => by
      cases l <;> cases r <;>
        simp only [uCombineZip, midPCombineZip, midPUnconsC, uRotSubK_eq, uCombineZip_eq t]
private def uAdvanceZip : ℕ → ℕ → WDIVal → WDIVal → List (List WDCVal) → List (List WDCVal)
  | 0, _, _, _, _ => []
  | n + 1, t, c, s, rows =>
      midPUnconsRows rows fun r0 tl ↦ midPUnconsRows tl fun r1 _ ↦
        uCombineZip t c s r0 r1 :: uAdvanceZip n t c s tl
private lemma uAdvanceZip_eq :
    ∀ (n t : ℕ) (c s : WDIVal) (rows : List (List WDCVal)),
      uAdvanceZip n t c s rows = midPAdvanceZip n t c s rows
  | 0, _, _, _, _ => rfl
  | n + 1, t, c, s, rows => by
      rcases rows with _ | ⟨r0, _ | ⟨r1, tl⟩⟩ <;>
        simp only [uAdvanceZip, midPAdvanceZip, midPUnconsRows, uCombineZip_eq, uAdvanceZip_eq n]
private def uIterLayers : ℕ → ℕ → WDIVal → WDIVal → List (List WDCVal) → List (List WDCVal)
  | 0, _, _, _, rows => rows
  | rem + 1, t, c, s, rows =>
      midPSeqCIVRows (uAdvanceZip (Nat.add rem 1) t c s rows) fun rows' ↦
        uIterLayers rem (Nat.add t 1) c s rows'
private lemma uIterLayers_eq :
    ∀ (rem t : ℕ) (c s : WDIVal) (rows : List (List WDCVal)),
      uIterLayers rem t c s rows = midPFastIterLayersCIV rem t c s rows
  | 0, _, _, _, _ => rfl
  | rem + 1, t, c, s, rows => by
      simp only [uIterLayers, midPFastIterLayersCIV, uAdvanceZip_eq, midPSeqCIVRows_eq]
      exact uIterLayers_eq rem (Nat.add t 1) c s _
private def uDickeStepVec (deg : ℕ) (cIV sIV : WDIVal) (uList : List WDCVal) : List WDCVal :=
  midPSeqCIVRows (midPFastInitRowsList (Nat.add deg 1) uList) fun initRows ↦
    (uIterLayers deg 0 cIV sIV initRows).headD []
private lemma uDickeStepVec_eq (deg : ℕ) (cIV sIV : WDIVal) (uList : List WDCVal) :
    uDickeStepVec deg cIV sIV uList = midPFastDickeStepVec deg cIV sIV uList := by
  simp only [uDickeStepVec, midPFastDickeStepVec, midPSeqCIVRows_eq, uIterLayers_eq]
private def uZipRotSub : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, _, _, _, _ => []
  | n + 1, c, s, m0, m1 =>
      midPUnconsC m0 fun a0 tl0 ↦ midPUnconsC m1 fun a1 tl1 ↦
        uRotSubK c s a0 a1 fun y ↦ y :: uZipRotSub n c s tl0 tl1
private lemma uZipRotSub_eq :
    ∀ (n : ℕ) (c s : WDIVal) (m0 m1 : List WDCVal),
      uZipRotSub n c s m0 m1 = midPZipRotSub n c s m0 m1
  | 0, _, _, _, _ => rfl
  | n + 1, c, s, m0, m1 => by
      cases m0 <;> cases m1 <;>
        simp only [uZipRotSub, midPZipRotSub, midPUnconsC, uRotSubK_eq, uZipRotSub_eq n]
private def uZipRotAdd : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, _, _, _, _ => []
  | n + 1, c, s, m0, m1 =>
      midPUnconsC m0 fun a0 tl0 ↦ midPUnconsC m1 fun a1 tl1 ↦
        uRotAddK c s a0 a1 fun y ↦ y :: uZipRotAdd n c s tl0 tl1
private lemma uZipRotAdd_eq :
    ∀ (n : ℕ) (c s : WDIVal) (m0 m1 : List WDCVal),
      uZipRotAdd n c s m0 m1 = midPZipRotAdd n c s m0 m1
  | 0, _, _, _, _ => rfl
  | n + 1, c, s, m0, m1 => by
      cases m0 <;> cases m1 <;>
        simp only [uZipRotAdd, midPZipRotAdd, midPUnconsC, uRotAddK_eq, uZipRotAdd_eq n]
private def uDampShift0 : ℕ → List WDCVal → List WDCVal → List WDCVal
  | 0, _, _ => []
  | k + 1, gs, xs =>
      midPUnconsC1 gs fun g gsTl ↦ midPUnconsC xs fun x xsTl ↦
        uCMulK g x fun gx ↦ gx :: uDampShift0 k gsTl xsTl
private lemma uDampShift0_eq :
    ∀ (k : ℕ) (gs xs : List WDCVal), uDampShift0 k gs xs = midPDampShift0Aux k gs xs
  | 0, _, _ => rfl
  | k + 1, gs, xs => by
      cases gs <;> cases xs <;>
        simp only [uDampShift0, midPDampShift0Aux, midPUnconsC1, midPUnconsC,
          uCMulK_eq, uDampShift0_eq k]
private def uDamp2Row0 (deg1 : ℕ) (gIVs r0 : List WDCVal) : List WDCVal :=
  midPUnconsC r0 fun x0 r0Tl ↦ x0 :: uDampShift0 deg1 gIVs r0Tl
private lemma uDamp2Row0_eq (deg1 : ℕ) (gIVs r0 : List WDCVal) :
    uDamp2Row0 deg1 gIVs r0 = midPFastDamp2Row0 deg1 gIVs r0 := by
  cases r0 <;> simp only [uDamp2Row0, midPFastDamp2Row0, midPUnconsC, uDampShift0_eq]
private def uDamp2Row1 (deg1 : ℕ) (gs r1 : List WDCVal) : List WDCVal :=
  uDampShift0 (Nat.add deg1 1) gs r1
private lemma uDamp2Row1_eq (deg1 : ℕ) (gs r1 : List WDCVal) :
    uDamp2Row1 deg1 gs r1 = midPFastDamp2Row1 deg1 gs r1 := uDampShift0_eq _ gs r1
private def uDampUTail : ℕ → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, cTop, gs, xs =>
      midPUnconsC1 gs fun g _ ↦ midPUnconsC xs fun x _ ↦
        uCMulK g x fun gx ↦ uCRMulK cTop gx fun y ↦ [y]
  | k + 1, cTop, gs, xs =>
      midPUnconsC1 gs fun g gsTl ↦ midPUnconsC xs fun x xsTl ↦
        uCMulK g x fun gx ↦ gx :: uDampUTail k cTop gsTl xsTl
private lemma uDampUTail_eq :
    ∀ (k : ℕ) (cTop : WDIVal) (gs xs : List WDCVal),
      uDampUTail k cTop gs xs = midPFastDampUTail k cTop gs xs
  | 0, cTop, gs, xs => by
      cases gs <;> cases xs <;>
        simp only [uDampUTail, midPFastDampUTail, midPUnconsC1, midPUnconsC, uCMulK_eq, uCRMulK_eq]
  | k + 1, cTop, gs, xs => by
      cases gs <;> cases xs <;>
        simp only [uDampUTail, midPFastDampUTail, midPUnconsC1, midPUnconsC,
          uCMulK_eq, uDampUTail_eq k]
private def uDampUAux : ℕ → WDIVal → List WDCVal → List WDCVal → List WDCVal
  | 0, _, _, _ => []
  | k + 1, cTop, gs, xs => uDampUTail k cTop gs xs
private def uDampU (r : ℕ) (gIVs : List WDCVal) (cTop : WDIVal)
    (uVec : List WDCVal) : List WDCVal :=
  midPUnconsC uVec fun u0 uTl ↦ u0 :: uDampUAux r cTop gIVs uTl
private lemma uDampU_eq (r : ℕ) (gIVs : List WDCVal) (cTop : WDIVal) (uVec : List WDCVal) :
    uDampU r gIVs cTop uVec = midPFastDampU r gIVs cTop uVec := by
  cases r <;> cases uVec <;>
    simp only [uDampU, midPFastDampU, uDampUAux, midPFastDampUAux, midPUnconsC, uDampUTail_eq]
private def uStep2RowCPS {α : Type*} (deg1 : ℕ) (gIVs : List WDCVal)
    (c1 s1 cC sC : WDIVal) (r0 r1 : List WDCVal)
    (k : List WDCVal → List WDCVal → α) : α :=
  midPSeqCIVList (uDamp2Row0 deg1 gIVs r0) fun d0 ↦
  midPSeqCIVList (uDamp2Row1 deg1 gIVs r1) fun d1 ↦
  midPSeqCIVList (uDickeStepVec deg1 c1 s1 d0) fun m0 ↦
  midPSeqCIVList (uDickeStepVec deg1 c1 s1 d1) fun m1 ↦
  midPSeqCIVList (uZipRotSub (Nat.add deg1 1) cC sC m0 m1) fun n0 ↦
  midPSeqCIVList (uZipRotAdd (Nat.add deg1 1) cC sC m0 m1) fun n1 ↦ k n0 n1
private lemma uStep2RowCPS_eq {α : Type*} (deg1 : ℕ) (gIVs : List WDCVal)
    (c1 s1 cC sC : WDIVal) (r0 r1 : List WDCVal)
    (k : List WDCVal → List WDCVal → α) :
    uStep2RowCPS deg1 gIVs c1 s1 cC sC r0 r1 k =
      midPFastStep2RowCPS deg1 gIVs c1 s1 cC sC r0 r1 k := by
  simp only [uStep2RowCPS, midPFastStep2RowCPS, midPSeqCIVList_eq,
    uDamp2Row0_eq, uDamp2Row1_eq, uDickeStepVec_eq, uZipRotSub_eq, uZipRotAdd_eq]
private def uDicke2Cols : ℕ → WDIVal → WDIVal → List WDCVal → List WDCVal → List WDCVal →
    List WDCVal × List WDCVal × List WDCVal
  | 0, _, _, _, _, _ => ([], [], [])
  | n + 1, c2, s2, r0, r1, r2 =>
      midPUnconsC r0 fun a r0Tl ↦ midPUnconsC r1 fun b r1Tl ↦ midPUnconsC r2 fun d r2Tl ↦
      uRotSubK c2 s2 a b fun m00 ↦ uRotAddK c2 s2 a b fun m01 ↦
      uRotSubK c2 s2 b d fun m10 ↦ uRotAddK c2 s2 b d fun m11 ↦
      uRotSubK c2 s2 m00 m10 fun y0 ↦ uRotSubK c2 s2 m01 m11 fun y1 ↦
      uRotAddK c2 s2 m01 m11 fun y2 ↦
      match uDicke2Cols n c2 s2 r0Tl r1Tl r2Tl with
      | (t0, t1, t2) => (y0 :: t0, y1 :: t1, y2 :: t2)
private lemma uDicke2Cols_eq :
    ∀ (n : ℕ) (c2 s2 : WDIVal) (r0 r1 r2 : List WDCVal),
      uDicke2Cols n c2 s2 r0 r1 r2 = midPDicke2Cols n c2 s2 r0 r1 r2
  | 0, _, _, _, _, _ => rfl
  | n + 1, c2, s2, r0, r1, r2 => by
      dsimp only [uDicke2Cols, midPDicke2Cols]
      refine congrArg (midPUnconsC r0) (funext fun a ↦ funext fun r0Tl ↦
        congrArg (midPUnconsC r1) (funext fun b ↦ funext fun r1Tl ↦
          congrArg (midPUnconsC r2) (funext fun d ↦ funext fun r2Tl ↦ ?_)))
      simp only [uRotSubK_eq, uRotAddK_eq, midPSeqCIV_eq, uDicke2Cols_eq n c2 s2 r0Tl r1Tl r2Tl]
private def uStepTwoPairCPS {α : Type*} (deg1 : ℕ) (gIVs : List WDCVal)
    (c1 s1 c2 s2 : WDIVal) (tp0 tp1 tp2 : List WDCVal)
    (k : List WDCVal → List WDCVal → List WDCVal → α) : α :=
  midPSeqCIVList (uDamp2Row0 deg1 gIVs tp0) fun d0 ↦
  midPSeqCIVList (uDamp2Row1 deg1 gIVs tp1) fun d1 ↦
  midPSeqCIVList (uDamp2Row1 deg1 gIVs.tail tp2) fun d2 ↦
  midPSeqCIVList (uDickeStepVec deg1 c1 s1 d0) fun m0 ↦
  midPSeqCIVList (uDickeStepVec deg1 c1 s1 d1) fun m1 ↦
  midPSeqCIVList (uDickeStepVec deg1 c1 s1 d2) fun m2 ↦
  match uDicke2Cols (Nat.add deg1 1) c2 s2 m0 m1 m2 with
  | (c0, c1', c2') =>
      midPSeqCIVList c0 fun n0 ↦ midPSeqCIVList c1' fun n1 ↦ midPSeqCIVList c2' fun n2 ↦ k n0 n1 n2
private lemma uStepTwoPairCPS_eq {α : Type*} (deg1 : ℕ) (gIVs : List WDCVal)
    (c1 s1 c2 s2 : WDIVal) (tp0 tp1 tp2 : List WDCVal)
    (k : List WDCVal → List WDCVal → List WDCVal → α) :
    uStepTwoPairCPS deg1 gIVs c1 s1 c2 s2 tp0 tp1 tp2 k =
      midPFastStepTwoPairCPS deg1 gIVs c1 s1 c2 s2 tp0 tp1 tp2 k := by
  unfold uStepTwoPairCPS midPFastStepTwoPairCPS
  simp only [midPSeqCIVList_eq, uDamp2Row0_eq, uDamp2Row1_eq, uDickeStepVec_eq, uDicke2Cols_eq]
private def fastEvalPhaseIVS1 (ph : MidPPhaseSpec) : Option WDCVal :=
  cond (Nat.ble 1 ph.gd &&
      fastBeqZS1 (_zAdd (_zMul ph.ga ph.ga) (_zMul ph.gb ph.gb))
        (_zMul (Int.ofNat ph.gd) (Int.ofNat ph.gd)))
    (uRatK ph.ga ph.gd fun re ↦ uRatK ph.gb ph.gd fun im ↦ some (re, im)) none
private lemma fastEvalPhaseIV_eq_s1 (ph : MidPPhaseSpec) :
    fastEvalPhaseIVS1 ph = evalMidPPhaseIV ph := by
  unfold fastEvalPhaseIVS1 evalMidPPhaseIV; simp only [uRatK_eq, midPSeqCIV_eq]
  refine cond_eq_ite_congr_s1 _ _ ?_ rfl
  simp only [Bool.and_eq_true, Nat.ble_eq, fastBeqZ_iff_s1, _zAdd_eq, _zMul_eq,
    Int.ofNat_eq_natCast]
  have h1 : ph.ga * ph.ga + ph.gb * ph.gb = ph.ga ^ 2 + ph.gb ^ 2 := by ring
  have h2 : (ph.gd : ℤ) * (ph.gd : ℤ) = (ph.gd : ℤ) ^ 2 := by ring
  rw [h1, h2]; omega
private def fastEvalPhasesIVS1 : List MidPPhaseSpec → Option (List WDCVal)
  | [] => some []
  | ph :: rest =>
      match fastEvalPhaseIVS1 ph, fastEvalPhasesIVS1 rest with
      | some gIV, some tl => some (gIV :: tl)
      | _, _ => none
private lemma fastEvalPhasesIV_eq_s1 :
    ∀ ps : List MidPPhaseSpec, fastEvalPhasesIVS1 ps = evalMidPPhasesIV ps
  | [] => rfl
  | ph :: rest => by
      dsimp only [fastEvalPhasesIVS1, evalMidPPhasesIV]
      rw [fastEvalPhaseIV_eq_s1 ph, fastEvalPhasesIV_eq_s1 rest]
      cases evalMidPPhaseIV ph <;> cases evalMidPPhasesIV rest <;> rfl
private def _probeOk (r : ℕ) (p : MidPProbeSpec) : Bool :=
  Nat.ble p.phases.length r && Nat.ble r p.phases.length && Nat.ble 1 p.daDen &&
    Nat.ble 1 p.cDen &&
    fastBeqZS1 (_zAdd (_zMul p.cNum p.cNum) (_zMul (Int.ofNat p.sNum) (Int.ofNat p.sNum)))
      (_zMul (Int.ofNat p.cDen) (Int.ofNat p.cDen))
private lemma _probeOk_iff (r : ℕ) (p : MidPProbeSpec) :
    _probeOk r p = true ↔
      p.phases.length = r ∧ 0 < p.daDen ∧ 0 < p.cDen ∧
        p.cNum ^ 2 + (p.sNum : ℤ) ^ 2 = (p.cDen : ℤ) ^ 2 := by
  unfold _probeOk
  simp only [Bool.and_eq_true, Nat.ble_eq, fastBeqZ_iff_s1, _zAdd_eq, _zMul_eq,
    Int.ofNat_eq_natCast]
  have h1 : p.cNum * p.cNum + (p.sNum : ℤ) * (p.sNum : ℤ) = p.cNum ^ 2 + (p.sNum : ℤ) ^ 2 := by ring
  have h2 : (p.cDen : ℤ) * (p.cDen : ℤ) = (p.cDen : ℤ) ^ 2 := by ring
  rw [h1, h2]; omega
private def fastProbeStepS1 (r : ℕ) (p : MidPProbeSpec)
    (st : MidPProbeState) : Option MidPProbeState :=
  cond (_probeOk r p)
    (match fastEvalPhasesIVS1 p.phases with
     | none => none
     | some gIVs =>
         uRatK (Int.ofNat p.daNum) p.daDen fun daIV ↦
         midPSeqInt (_maxZ 0 (_zSub daIV.1 2)) fun dp1l ↦
         let dphi1 : WDIVal := (dp1l, daIV.2)
         uMulIVK dphi1 (midPSqrtRatioIv 2) fun dphi2 ↦
         uMulIVK dphi1 (midPSqrtRatioIv 3) fun dphi3 ↦
         uMulIVK dphi1 (midPSqrtRatioIv 4) fun dphi4 ↦
         if midPBleZ 0 dphi1.1 && midPBleZ dphi4.2 _maxAngZ then
           uRatK p.cNum p.cDen fun cTop ↦
           midPSeqCIVList (uDampU r gIVs cTop st.uVec) fun uD ↦
           midPSeqInt (midPSumRangeZ (Nat.add r 1) fun w ↦
             _zMul (Int.ofNat (fastBinomS1 r w)) (uCAbs2Hi (uD.getD w wdCZero))) fun sHi ↦
           midPSeqInt (_zDivCl (_zMul (_zAdd daIV.2 4) wdPi4InvHi) _s2B) fun qdaHi ↦
           midPSeqInt (_zDivCl (_zMul sHi qdaHi) _sB) fun stepQ ↦
           midPSeqInt (_zAdd st.qExtraHi stepQ) fun qExNext ↦
           midPSeqInt (_zAdd st.qCollAddHi qdaHi) fun qCollNext ↦
           fastTrigCPSS1 dphi1 fun c1 s1 ↦
           fastTrigCPSS1 dphi2 fun c2 s2 ↦
           fastTrigCPSS1 dphi3 fun c3 s3 ↦
           midPSeqCIVList (uDickeStepVec r c1 s1 uD) fun uNext ↦
           uStep2RowCPS (r - 2) gIVs c1 s1 c2 s2 st.sp0 st.sp1 fun sp0N sp1N ↦
           uStep2RowCPS (r - 3) gIVs c1 s1 c3 s3 st.st0 st.st1 fun st0N st1N ↦
           if Nat.ble 4 r then
             uStepTwoPairCPS (r - 4) gIVs c1 s1 c2 s2 st.tp0 st.tp1 st.tp2
               fun tp0N tp1N tp2N ↦
                 some ⟨qExNext, qCollNext, uNext, sp0N, sp1N, st0N, st1N,
                   tp0N, tp1N, tp2N, [], []⟩
           else some ⟨qExNext, qCollNext, uNext, sp0N, sp1N, st0N, st1N, [], [], [], [], []⟩
         else none)
    none
private lemma fastProbeStep_eq_s1 (r : ℕ) (p : MidPProbeSpec) (st : MidPProbeState) :
    fastProbeStepS1 r p st = evalMidPProbeStep r false p st := by
  unfold fastProbeStepS1 evalMidPProbeStep; rw [fastEvalPhasesIV_eq_s1]
  refine cond_eq_ite_congr_s1 _ _ (_probeOk_iff r p) ?_
  cases evalMidPPhasesIV p.phases with
  | none => rfl
  | some gIVs =>
      have hnf : ¬(false = true) := Bool.false_ne_true
      have hmax : _maxAngZ = Int.mul 1024 midPScaleZ := rfl
      have hda : Int.ofNat p.daNum = (p.daNum : ℤ) := rfl
      dsimp only
      simp only [uRatK_eq, hda, midPSeqInt_eq, _maxZ_eq_gh, _zSub_int, _zAdd_int, _zMul_int,
        uMulIVK_eq, hmax, midPSeqCIVList_eq, uDampU_eq, fastBinom_eq_s1, uCAbs2Hi_eq,
        _zDivCl_eq, _sB_midP, _s2B_midP, fastTrigCPS_eq_s1, uDickeStepVec_eq,
        uStep2RowCPS_eq, uStepTwoPairCPS_eq, ite_eq_right hnf]
private def fastEvalProbesS1 (r : ℕ) :
    List MidPProbeSpec → MidPProbeState → Option MidPProbeState
  | [], st => some st
  | p :: rest, st =>
      match fastProbeStepS1 r p st with
      | none => none
      | some st' => fastEvalProbesS1 r rest st'
private theorem fastEvalProbes_eq_s1 (r : ℕ) :
    ∀ (ps : List MidPProbeSpec) (st : MidPProbeState),
      fastEvalProbesS1 r ps st = evalMidPProbes r false ps st
  | [], _ => rfl
  | p :: rest, st => by
      dsimp only [fastEvalProbesS1, evalMidPProbes]; rw [fastProbeStep_eq_s1 r p st]
      cases evalMidPProbeStep r false p st with
      | none => rfl
      | some st' => exact fastEvalProbes_eq_s1 r rest st'
private def evalMidPRowInitProbesS1 (m r : ℕ) (spec : MidPRowSpec) (ps0 : List MidPProbeSpec) :
    Option
    MidPProbeState :=
  let p := Stage2CertInternals.gridExp m
  if 3 ≤ r ∧ r ≤ 16 ∧ r - 1 < m ∧ 2 ≤ p ∧ p ≤ 10 ∧ m = 2 ^ p ∧
      0 < spec.a0Den ∧ 0 < spec.kzDen then
    let a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den
    let phi01 : WDIVal := (ghMaxZ 0 (Int.sub a0IV.1 1), Int.add a0IV.2 1)
    let phi02 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 2)
    let phi03 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 3)
    let phi04 : WDIVal := midPFastMulIV phi01 (midPSqrtRatioIv 4)
    let maxAng : ℤ := Int.mul 1024 midPScaleZ
    if midPBleZ 0 phi01.1 && midPBleZ phi04.2 maxAng then
      midPTrigCPS phi01 fun c01 s01 ↦ midPTrigCPS phi02 fun c02 s02 ↦
      midPTrigCPS phi03 fun c03 s03 ↦
      midPSeqCIVList (midPFastDickeStepVec r c01 s01 (midPOneHot0 (Nat.add r 1))) fun u0 ↦
      midPSeqCIVList (midPFastDickeStepVec (r - 2) c01 s01 (midPOneHot0 (r - 1))) fun uRm2 ↦
      midPSeqCIVList (uRm2.map (midPFastCRMul c02)) fun sp0Init ↦
      midPSeqCIVList (uRm2.map (midPFastCRMul s02)) fun sp1Init ↦
      midPSeqCIVList (midPFastDickeStepVec (r - 3) c01 s01 (midPOneHot0 (r - 2))) fun uRm3 ↦
      midPSeqCIVList (uRm3.map (midPFastCRMul c03)) fun st0Init ↦
      midPSeqCIVList (uRm3.map (midPFastCRMul s03)) fun st1Init ↦
      let runInit (tp0I tp1I tp2I : List WDCVal) : Option MidPProbeState :=
        fastEvalProbesS1 r ps0
          ⟨0, 0, u0, sp0Init, sp1Init, st0Init, st1Init, tp0I, tp1I, tp2I, [], []⟩
      if Nat.ble 4 r then
        midPSeqCIVList (midPFastDickeStepVec (r - 4) c01 s01 (midPOneHot0 (r - 3))) fun uRm4 ↦
        midPSeqCIVList (midPFastDickeStepVec 2 c02 s02 (midPOneHot0 3)) fun uP2 ↦
        let p20 := uP2.getD 0 wdCZero; let p21 := uP2.getD 1 wdCZero; let p22 := uP2.getD 2 wdCZero
        midPSeqCIVList (uRm4.map (midPFastCMul p20)) fun tp0I ↦
        midPSeqCIVList (uRm4.map (midPFastCMul p21)) fun tp1I ↦
        midPSeqCIVList (uRm4.map (midPFastCMul p22)) fun tp2I ↦ runInit tp0I tp1I tp2I
      else runInit [] [] []
    else none
  else none
private def midPRowFinishS1 (m r : ℕ) (spec : MidPRowSpec) (fin : MidPProbeState) : Option
    MidPSummary :=
  let a0IV := wdRat (spec.a0Num : ℤ) spec.a0Den; let maxAng : ℤ := Int.mul 1024 midPScaleZ
  let q0Hi := wdDivCeil (Int.mul (Int.add a0IV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
  let qDistHi := Int.add q0Hi fin.qExtraHi; let qCollHi := Int.add q0Hi fin.qCollAddHi
  let kzIV := wdRat (spec.kzNum : ℤ) spec.kzDen
  let azIV : WDIVal := (ghMaxZ 0 (Int.sub kzIV.1 1), Int.add kzIV.2 1)
  if midPBleZ 0 azIV.1 && midPBleZ azIV.2 maxAng then
    midPTrigCPS azIV fun _ sAz ↦
    let zHitLo := (ghSqIV sAz).1
    let qzSub := wdDivCeil (Int.mul (Int.add kzIV.2 2) wdPi4InvHi) (Int.mul 2 midPScaleZ)
    let uScale := midPUnpaddedZoomScaleHi15 (r - 1) m
    let qZoomHi := wdDivCeil (Int.mul qzSub uScale) midPScaleZ
    if midPBleZ 0 zHitLo && midPBleZ zHitLo midPScaleZ &&
        midPBleZ (Int.add qCollHi qZoomHi) (Int.mul 12 midPScaleZ) then
      midPSeqInt qDistHi fun qdF ↦ midPSeqInt qCollHi fun qcF ↦ midPSeqInt qZoomHi fun qzF ↦
      midPSeqInt zHitLo fun zhF ↦ midPSeqZList (fin.uVec.map wdCAbs2Hi) fun uAbs ↦
      midPSeqZList (fin.sp0.map wdCAbs2Hi) fun z0Abs ↦
      midPSeqZList (fin.sp1.map wdCAbs2Hi) fun z1Abs ↦
      let tpWt :=if Nat.ble 4 r then midPCollapseTwoPairWt (r - 4) r fin.tp0 fin.tp1 fin.tp2
        else List.replicate (Nat.add r 1) 0
      let stWt := midPCollapse2RowWt (r - 3) r fin.st0 fin.st1
      let q1Wt :=if Nat.ble 4 r && false then midPCollapse2RowWt (r - 4) r fin.q10 fin.q11
        else List.replicate (Nat.add r 1) 0
      midPSeqZList tpWt fun tpF ↦ midPSeqZList stWt fun stF ↦ midPSeqZList q1Wt fun q1F ↦
        some ⟨qdF, qcF, qzF, zhF, uAbs, z0Abs, z1Abs, tpF, stF, q1F⟩
    else none
  else none
private def midPOptBoolS1 {α : Type*} (mx : Option α) (f : α → Bool) : Bool :=
  match mx with
  | none => false
  | some x => f x
private lemma midPOptBool_eq_true_s1 {α : Type*} {mx : Option α} {f : α → Bool} (h : midPOptBoolS1
mx f = true) : ∃ x : α, mx = some x ∧ f x = true := by
  cases mx with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩
private def checkGHMidPSummaryPassesS1 (m W r : ℕ) (vSeq : List (List ℕ)) (s : MidPSummary) :
    Bool :=
  (List.range W).all (fun i ↦
    match evalMidPStepFromSummary m r false s (vSeq.getD (i + 1) []) with
    | some hir => Nat.ble hir ((vSeq.getD i []).getD r 0)
    | none => false)
private theorem evalMidPProbes_append_s1 (r : ℕ) (includeRm3 : Bool) : ∀ (xs ys : List
    MidPProbeSpec) (st :
MidPProbeState), evalMidPProbes r includeRm3 (xs ++ ys) st = match evalMidPProbes r includeRm3 xs
    st with
        | none => none
        | some st' => evalMidPProbes r includeRm3 ys st'
  | [], _, _ => by
      rw [List.nil_append]; rfl
  | p :: xs, ys, st => by
      rw [List.cons_append]; dsimp only [evalMidPProbes]
      cases evalMidPProbeStep r includeRm3 p st with
      | none => rfl
      | some st1 => exact evalMidPProbes_append_s1 r includeRm3 xs ys st1
private lemma midPTrigCPS_congr_of_some_s1 {α β : Type*} {x : WDIVal} {k₁ : WDIVal → WDIVal →
Option α} {k₂ : WDIVal → WDIVal → β} {v : α} {rhs : β} (h0 : midPTrigCPS x k₁ = some v) (hk : ∀ c s
: WDIVal, k₁ c s = some v → k₂ c s = rhs) : midPTrigCPS x k₂ = rhs := by
  rw [midPTrigCPS_eq] at h0 ⊢; exact hk (wdTrig x).1 (wdTrig x).2 h0
private theorem evalMidPRowSummary_of_initProbes_s1 {m r : ℕ} {spec : MidPRowSpec} {ps0 psRest
    : List
MidPProbeSpec} {st0 fin : MidPProbeState} (h0 : evalMidPRowInitProbesS1 m r spec ps0 = some st0)
(hrest : evalMidPProbes r false psRest st0 = some fin) (hpr : spec.probes = ps0 ++ psRest) :
    evalMidPRowSummary m r false spec = midPRowFinishS1 m r spec fin := by
  unfold evalMidPRowInitProbesS1 at h0; unfold evalMidPRowSummary; dsimp only at h0 ⊢
  split at h0
  · next hg1 =>
      rw [ite_eq_left hg1]
      split at h0
      · next hg2 =>
          rw [ite_eq_left hg2]; refine midPTrigCPS_congr_of_some_s1 h0 fun c01 s01 h0 ↦ ?_
          refine midPTrigCPS_congr_of_some_s1 h0 fun c02 s02 h0 ↦ ?_
          refine midPTrigCPS_congr_of_some_s1 h0 fun c03 s03 h0 ↦ ?_
          conv at h0 => lhs; simp only [midPSeqCIVList_eq]
          conv_lhs => simp only [midPSeqCIVList_eq]
          by_cases hr4 : Nat.ble 4 r = true
          · rw [ite_eq_left hr4] at h0 ⊢
            have hnf : ¬(false = true) := Bool.false_ne_true
            rw [ite_eq_right hnf]; rw [fastEvalProbes_eq_s1] at h0
            rw [hpr, evalMidPProbes_append_s1, h0]; dsimp only; rw [hrest]; unfold midPRowFinishS1
            rfl
          · rw [ite_eq_right hr4] at h0 ⊢
            rw [fastEvalProbes_eq_s1] at h0; rw [hpr, evalMidPProbes_append_s1, h0]; dsimp only
            rw [hrest]; unfold midPRowFinishS1; rfl
      · cases h0
  · cases h0
private lemma checkGHMidPRowsSlice_of_summary_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec :
MidPRowSpec} {s : MidPSummary} (hsum : evalMidPRowSummary m r false spec = some s) (hp :
checkGHMidPSummaryPassesS1 m W r vSeq s = true) : checkGHMidPRowsSlice false m W vSeq r [spec] =
    true := by
  simp only [checkGHMidPRowsSlice]; rw [hsum]; dsimp only [checkGHMidPSummaryPassesS1] at hp ⊢
  rw [Bool.and_true]; simp only [List.all_eq_true] at hp ⊢; intro i hi; have hpi := hp i hi
  cases hst : evalMidPStepFromSummary m r false s (vSeq.getD (i + 1) []) with
  | none =>
      rw [hst] at hpi; cases hpi
  | some _ =>
      rw [hst] at hpi; exact hpi
private def uCheckFullRowS1 (m W r : ℕ) (vSeq : List (List ℕ)) (spec : MidPRowSpec) : Bool :=
  midPOptBoolS1 (evalMidPRowInitProbesS1 m r spec spec.probes) fun fin ↦
    midPOptBoolS1 (midPRowFinishS1 m r spec fin)
      (checkGHMidPSummaryPassesS1 m W r vSeq)
private theorem uCheckFullRow_sound_s1 {m W r : ℕ} {vSeq : List (List ℕ)} {spec : MidPRowSpec} (h :
uCheckFullRowS1 m W r vSeq spec = true) : checkGHMidPRowsSlice false m W vSeq r [spec] = true := by
  unfold uCheckFullRowS1 at h; obtain ⟨fin, h0, h1⟩ := midPOptBool_eq_true_s1 h
  obtain ⟨s, hms, hp⟩ := midPOptBool_eq_true_s1 h1
  have h0' : evalMidPRowInitProbesS1 m r spec spec.probes = some fin := h0
  have hsum : evalMidPRowSummary m r false spec = some s :=
    (evalMidPRowSummary_of_initProbes_s1 h0' rfl (List.append_nil spec.probes).symm).trans hms
  exact checkGHMidPRowsSlice_of_summary_s1 hsum hp
end QuantumComputation.Specs.DickeSol.MpzS1
end MpzMidPFastS1

section

namespace QuantumComputation.Specs.GroverFindAll.MpzGHMidP

open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal ENNReal NNRat
open QuantumComputation.Specs QuantumComputation.Specs.DickeSol
open QuantumComputation.Specs.DickeSol.MpzMidP
open QuantumComputation.Specs.DickeSol.MpzS1
open QuantumComputation.Specs.GroverFindAll.GaussianHammingZoomK2
open QuantumComputation.Specs.GroverFindAll.MpzGHZoom

private lemma bL {a b : Bool} (h : (a && b) = true) : a = true := by
  simp only [Bool.and_eq_true] at h; exact h.1
private lemma bR {a b : Bool} (h : (a && b) = true) : b = true := by
  simp only [Bool.and_eq_true] at h; exact h.2
private lemma _rowsCons {m r : ℕ} {vSeq : List (List ℕ)} {x : GHMidPRowSpec}
    {xs : List GHMidPRowSpec} (hx : checkGHMidPRowsSlice false m 16 vSeq r [x] = true)
    (hxs : checkGHMidPRowsSlice false m 16 vSeq (r + 1) xs = true) :
    checkGHMidPRowsSlice false m 16 vSeq r (x :: xs) = true :=
  checkGHMidPRowsSlice_append false m 16 vSeq r [x] xs hx hxs
private def mpzHdr64 : Bool :=
  checkGHMidPSpineHeaderAndR2 64 4 16 mpzMidPRows64.length mpzZoomRow64 mpzMidPVSeq_64 &&
    checkGHMidPCellRatio 4 mpzMidPVSeq_64 971953019 2784457050
private theorem mpzHdr64_b : mpzHdr64 = true := by
  decide +kernel
private def mpzHdr512 : Bool :=
  checkGHMidPSpineHeaderAndR2 512 8 16 mpzMidPRows512.length mpzZoomRow512
    mpzMidPVSeq_512 &&
    checkGHMidPCellRatio 4 mpzMidPVSeq_512 183092327 556891410
private theorem mpzHdr512_b : mpzHdr512 = true := by
  decide +kernel
private theorem mpzRow_m64_r3_b :
    uCheckFullRowS1 64 16 3 mpzMidPVSeq_64 mpzMidPRow_m64_r3 = true := by
  decide +kernel
private theorem mpzRow_m64_r4_b :
    uCheckFullRowS1 64 16 4 mpzMidPVSeq_64 mpzMidPRow_m64_r4 = true := by
  decide +kernel
private theorem mpzMidPRows64_ok :
    checkGHMidPRowsSlice false 64 16 mpzMidPVSeq_64 3 mpzMidPRows64 = true :=
  _rowsCons (uCheckFullRow_sound_s1 mpzRow_m64_r3_b)
    (uCheckFullRow_sound_s1 mpzRow_m64_r4_b)
private theorem mpzRow_m512_r3_b :
    uCheckFullRowS1 512 16 3 mpzMidPVSeq_512 mpzMidPRow_m512_r3 = true := by
  decide +kernel
private theorem mpzRow_m512_r4_b :
    uCheckFullRowS1 512 16 4 mpzMidPVSeq_512 mpzMidPRow_m512_r4 = true := by
  decide +kernel
private theorem mpzRow_m512_r5_b :
    uCheckFullRowS1 512 16 5 mpzMidPVSeq_512 mpzMidPRow_m512_r5 = true := by
  decide +kernel
private theorem mpzRow_m512_r6_b :
    uCheckFullRowS1 512 16 6 mpzMidPVSeq_512 mpzMidPRow_m512_r6 = true := by
  decide +kernel
private theorem mpzRow_m512_r7_b :
    uCheckFullRowS1 512 16 7 mpzMidPVSeq_512 mpzMidPRow_m512_r7 = true := by
  decide +kernel
private theorem mpzRow_m512_r8_b :
    uCheckFullRowS1 512 16 8 mpzMidPVSeq_512 mpzMidPRow_m512_r8 = true := by
  decide +kernel
private theorem mpzMidPRows512_ok :
    checkGHMidPRowsSlice false 512 16 mpzMidPVSeq_512 3 mpzMidPRows512 = true :=
  _rowsCons (uCheckFullRow_sound_s1 mpzRow_m512_r3_b)
    (_rowsCons (uCheckFullRow_sound_s1 mpzRow_m512_r4_b)
    (_rowsCons (uCheckFullRow_sound_s1 mpzRow_m512_r5_b)
    (_rowsCons (uCheckFullRow_sound_s1 mpzRow_m512_r6_b)
    (_rowsCons (uCheckFullRow_sound_s1 mpzRow_m512_r7_b)
    (uCheckFullRow_sound_s1 mpzRow_m512_r8_b)))))
private theorem mpzMidPSpine_64_ok :
    checkGHMidPSpine false 64 4 16 mpzZoomRow64 mpzMidPRows64 mpzMidPVSeq_64 = true :=
  checkGHMidPSpine_of_slices (rowsMidP := mpzMidPRows64) (bL mpzHdr64_b) mpzMidPRows64_ok
private theorem mpzMidPSpine_512_ok :
    checkGHMidPSpine false 512 8 16 mpzZoomRow512 mpzMidPRows512 mpzMidPVSeq_512 = true :=
  checkGHMidPSpine_of_slices (rowsMidP := mpzMidPRows512)
    (bL mpzHdr512_b) mpzMidPRows512_ok
private structure MpzMidPCertEntry where
  kMax : ℕ
  W : ℕ
  row2 : GHZoomRowSpec
  rowsMidP : List GHMidPRowSpec
  vSeq : List (List ℕ)
  num : ℕ
  den : ℕ
private def mpzMidPCertValid (m k : ℕ) (c : MpzMidPCertEntry) : Prop :=
  Stage1.cells m k = true ∧ 2 ≤ m ∧ 2 ≤ k ∧ k ≤ c.kMax ∧ c.W ≤ 16 ∧
    checkGHMidPSpine false m c.kMax c.W c.row2 c.rowsMidP c.vSeq = true ∧
    checkGHMidPCellRatio k c.vSeq c.num c.den = true ∧
    relCostMpzGHMidP m k = (c.num : ℚ≥0) / (c.den : ℚ≥0)
private lemma mpz_cells_pow {i j m k : ℕ} (hi : i < 11) (hj : j < 11)
    (hm : 2 ^ i = m) (hk : 2 ^ j = k) : Stage1.cells m k = true := by
  simp only [Stage1.cells, gridCells, groverGrid, Bool.and_eq_true, decide_eq_true_eq,
    Finset.mem_image, Finset.mem_range]
  exact ⟨⟨i, hi, hm⟩, ⟨j, hj, hk⟩⟩
private lemma mpzMP_mk {m k : ℕ} {c : MpzMidPCertEntry} (i j : ℕ) (hi : i < 11) (hj : j < 11)
    (hm : 2 ^ i = m) (hk : 2 ^ j = k) (hw : 2 ≤ m ∧ 2 ≤ k ∧ k ≤ c.kMax ∧ c.W ≤ 16)
    (hs : checkGHMidPSpine false m c.kMax c.W c.row2 c.rowsMidP c.vSeq = true)
    (hrat : checkGHMidPCellRatio k c.vSeq c.num c.den = true)
    (hrc : relCostMpzGHMidP m k = (c.num : ℚ≥0) / (c.den : ℚ≥0)) :
    mpzMidPCertValid m k c :=
  ⟨mpz_cells_pow hi hj hm hk, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, hs, hrat, hrc⟩
private def mpzMidPLookup (m k : ℕ) : Option MpzMidPCertEntry :=
  if k = 4 then
    if m = 64 then
      some ⟨4, 16, mpzZoomRow64, mpzMidPRows64, mpzMidPVSeq_64, 971953019, 2784457050⟩
    else if m = 128 then
      some ⟨4, 16, mpzZoomRow128, mpzMidPRows128, mpzMidPVSeq_128, 156832149, 464076175⟩
    else if m = 256 then
      some ⟨4, 16, mpzZoomRow256, mpzMidPRows256, mpzMidPVSeq_256, 462221306, 1392228525⟩
    else if m = 512 then
      some ⟨8, 16, mpzZoomRow512, mpzMidPRows512, mpzMidPVSeq_512, 183092327, 556891410⟩
    else none
  else if k = 8 then
    if m = 512 then
      some ⟨8, 16, mpzZoomRow512, mpzMidPRows512, mpzMidPVSeq_512, 484469487, 2185718399⟩
    else if m = 1024 then
      some ⟨8, 16, mpzZoomRow1024, mpzMidPRows1024, mpzMidPVSeq_1024, 951881197, 4371436798⟩
    else none
  else none
private lemma mpzMidPLookup_isSome {m k : ℕ} (h : isMpzGHMidPCell m k = true) :
    (mpzMidPLookup m k).isSome = true := by
  unfold isMpzGHMidPCell at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [mpzMidPLookup]
private lemma mpzMidPLookup_props {m k : ℕ} {c : MpzMidPCertEntry}
    (h : mpzMidPLookup m k = some c) : mpzMidPCertValid m k c := by
  unfold mpzMidPLookup at h
  by_cases hk4 : k = 4
  · rw [ite_eq_left hk4] at h; subst hk4
    by_cases hm64 : m = 64
    · rw [ite_eq_left hm64] at h; cases h; subst hm64
      exact mpzMP_mk 6 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        mpzMidPSpine_64_ok (bR mpzHdr64_b)
        (by unfold relCostMpzGHMidP; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm64] at h
    by_cases hm128 : m = 128
    · rw [ite_eq_left hm128] at h; cases h; subst hm128
      exact mpzMP_mk 7 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        mpzMidPSpine_128_ok (bL mpzCellRatios_bk8_ok)
        (by unfold relCostMpzGHMidP; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm128] at h
    by_cases hm256 : m = 256
    · rw [ite_eq_left hm256] at h; cases h; subst hm256
      exact mpzMP_mk 8 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        mpzMidPSpine_256_ok (bL (bR mpzCellRatios_bk8_ok))
        (by unfold relCostMpzGHMidP; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm256] at h
    by_cases hm512 : m = 512
    · rw [ite_eq_left hm512] at h; cases h; subst hm512
      exact mpzMP_mk 9 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        mpzMidPSpine_512_ok (bR mpzHdr512_b)
        (by unfold relCostMpzGHMidP; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm512] at h; cases h
  rw [ite_eq_right hk4] at h
  by_cases hk8 : k = 8
  · rw [ite_eq_left hk8] at h; subst hk8
    by_cases hm512 : m = 512
    · rw [ite_eq_left hm512] at h; cases h; subst hm512
      exact mpzMP_mk 9 3 (by omega) (by omega) rfl rfl (by dsimp; omega)
        mpzMidPSpine_512_ok (bL (bR (bR mpzCellRatios_bk8_ok)))
        (by unfold relCostMpzGHMidP; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm512] at h
    by_cases hm1024 : m = 1024
    · rw [ite_eq_left hm1024] at h; cases h; subst hm1024
      exact mpzMP_mk 10 3 (by omega) (by omega) rfl rfl (by dsimp; omega)
        mpzMidPSpine_1024_ok (bR (bR (bR mpzCellRatios_bk8_ok)))
        (by unfold relCostMpzGHMidP; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm1024] at h; cases h
  rw [ite_eq_right hk8] at h; cases h
private noncomputable def mpzMidPUnifiedCircuit {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) (c : MpzMidPCertEntry) (hv : mpzMidPCertValid m k c) :
    OracleDynamicCircuit (Unitary (2 ^ mpzGHMidPQubits n m k)) Var
      (mpzGHMidPQubits n m k) ((n + 1) * m) :=
  DickeSol.ghMidPCertCircuit res (DickeSol.Stage1.cells_mem_grid hv.1).1
    (DickeSol.Stage1.cells_mem_grid hv.1).2 hv.2.1 hv.2.2.1
    c.kMax c.W c.row2 c.rowsMidP hv.2.2.2.2.1 n
private lemma mpzMidP_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle
  rfl
private lemma mpzMidP_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k =
      (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl
private lemma mpzMidP_vanilla_eq (n m k : ℕ) :
    DickeSol.vanillaFindAllCost n m k =
      (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl

end QuantumComputation.Specs.GroverFindAll.MpzGHMidP

end

public section

namespace QuantumComputation.Specs.GroverFindAll.MpzGHMidP

open Operator ResourceCounting Real QProg QProg.Notation
open scoped NNReal ENNReal NNRat
open QuantumComputation.Specs

/-- Certified dynamic circuit for `MpzGHMidP`. -/
noncomputable def findAllMpzGHMidPCircuit {Var : Type} [DecidableEq Var]
    (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ mpzGHMidPQubits n m k)) Var
      (mpzGHMidPQubits n m k) ((n + 1) * m) :=
  match hlook : mpzMidPLookup m k with
  | some c => mpzMidPUnifiedCircuit res n m k c (mpzMidPLookup_props hlook)
  | none => .skip

theorem mpzGHMidP_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n)
    (hcell : isMpzGHMidPCell m k = true) (hkN : k ≤ 2 ^ n)
    (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ mpzGHMidPQubits n m k)) ⦄
    (QProg.qSet ;; (findAllMpzGHMidPCircuit res n m k).compile QProg.qAssign
      (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  cases hlook : mpzMidPLookup m k with
  | none =>
      have his := mpzMidPLookup_isSome hcell; rw [hlook] at his; cases his
  | some c =>
      have hv := mpzMidPLookup_props hlook
      have hcirc : findAllMpzGHMidPCircuit (Var := Var) res n m k =
          mpzMidPUnifiedCircuit res n m k c hv := by
        unfold findAllMpzGHMidPCircuit
        split
        · next _ h => rw [hlook] at h; cases h; rfl
        · next h => rw [hlook] at h; cases h
      have hS1 : S ∈ DickeSol.groverTargetSets n k := by rw [mpzMidP_targetSets_eq]; exact hS
      rw [hcirc, ← mpzMidP_oracle_eq]; dsimp only [mpzMidPUnifiedCircuit]
      have hcorr := DickeSol.ghMidPCert_correctness res hn hv.1 hv.2.1 hv.2.2.1 hkN
        c.kMax c.W c.row2 c.rowsMidP hv.2.2.2.2.1 hS1
      dsimp only [mpzGHMidPQubits, DickeSol.Stage1.qubits] at hcorr ⊢; exact hcorr

theorem mpzGHMidP_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hcell : isMpzGHMidPCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n →
      ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
        (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
          CostBound (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
            (QProg.qSet ;; (findAllMpzGHMidPCircuit res n m k).compile
              QProg.qAssign (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
        (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
            ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
          ((relCostMpzGHMidP m k : ℚ≥0) : ℝ) *
            ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  cases hlook : mpzMidPLookup m k with
  | none =>
      have his := mpzMidPLookup_isSome hcell; rw [hlook] at his; cases his
  | some c =>
      have hv := mpzMidPLookup_props hlook
      have hcirc : ∀ n, findAllMpzGHMidPCircuit (Var := Var) res n m k =
          mpzMidPUnifiedCircuit res n m k c hv := by
        intro n; unfold findAllMpzGHMidPCircuit
        split
        · next _ h => rw [hlook] at h; cases h; rfl
        · next h => rw [hlook] at h; cases h
      have hgrid := DickeSol.Stage1.cells_mem_grid hv.1
      obtain ⟨n₀, hn₀⟩ := DickeSol.ghMidPCert_relCost (Var := Var) res hgrid.1 hgrid.2
        hv.2.1 hv.2.2.1 c.kMax c.W hv.2.2.2.1 c.row2 c.rowsMidP
        hv.2.2.2.2.1 c.vSeq c.num c.den hv.2.2.2.2.2.1 hv.2.2.2.2.2.2.1
      refine ⟨n₀, fun n hn hkN ↦ ?_⟩
      obtain ⟨q, hq, hsum⟩ := hn₀ n hn hkN
      refine ⟨q, fun S hS ↦ ?_, ?_⟩
      · rw [hcirc n, ← mpzMidP_oracle_eq]; dsimp only [mpzMidPUnifiedCircuit]
        have hqS := hq S (by rw [mpzMidP_targetSets_eq]; exact hS)
        dsimp only [mpzGHMidPQubits, DickeSol.Stage1.qubits] at hqS ⊢; exact hqS
      · rw [← mpzMidP_targetSets_eq, ← mpzMidP_vanilla_eq, hv.2.2.2.2.2.2.2]; exact hsum

end QuantumComputation.Specs.GroverFindAll.MpzGHMidP

end
