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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.PotentialSelectSpecA
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
open scoped BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoinWrap (xagEnv)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec (mkFin3 mkFin187
    mkFin234 foldSum sum_fin_eq_foldSum sum_fin_mul)
set_option exponentiation.threshold 256

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
open PrimitiveGate PhotochemistrySolution.CoinWrap
/-- Balanced binary check of `p x = true` on `[base, base + len)` with depth `fuel`. -/
def allTree : ℕ → ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, _, _, _ => false
  | _ + 1, _, 0, _ => true
  | _ + 1, base, 1, p => p base
  | fuel + 1, base, len + 2, p =>
      let half := (len + 2) / 2
      Bool.and (allTree fuel base half p)
        (allTree fuel (base + half) (len + 2 - half) p)
theorem allTree_imp : ∀ fuel base len p, allTree fuel base len p = true →
    ∀ d < len, p (base + d) = true
  | 0, _, _, _, hT, _, _ => Bool.noConfusion hT
  | _ + 1, _, 0, _, _, _, hd => absurd hd (Nat.not_lt_zero _)
  | _ + 1, _, 1, _, hT, 0, _ => hT
  | _ + 1, _, 1, _, _, _ + 1, hd => by omega
  | fuel + 1, base, len + 2, p, hT, d, hd => by
      rcases Bool.and_eq_true_iff.mp hT with ⟨hL, hR⟩
      by_cases hdh : d < (len + 2) / 2
      · exact allTree_imp fuel base _ p hL d hdh
      · simpa only [show base + (len + 2) / 2 + (d - (len + 2) / 2) = base + d by omega] using
          allTree_imp fuel (base + (len + 2) / 2) _ p hR (d - (len + 2) / 2) (by omega)
theorem allTree_zero {fuel len : ℕ} {p : ℕ → Bool} (hT : allTree fuel 0 len p = true) {xv : ℕ}
    (hx : xv < len) : p xv = true := by simpa using allTree_imp fuel 0 len p hT xv hx
theorem oddBits_eq_false_of_lt {v : ℕ} :
    ∀ (n : ℕ), (∀ i < n, v.testBit i = false) → oddBits v n = false
  | 0, _ => rfl
  | n + 1, hLt => by
      simp [oddBits, oddBits_eq_false_of_lt n fun i hi ↦ hLt i (by omega), hLt n (by omega)]
theorem oddBits_congr_lt {u v : ℕ} :
    ∀ (n : ℕ), (∀ i < n, u.testBit i = v.testBit i) → oddBits u n = oddBits v n
  | 0, _ => rfl
  | n + 1, hEq => by
      simp [oddBits, oddBits_congr_lt n fun i hi ↦ hEq i (by omega), hEq n (by omega)]
theorem oddBits_trim_above {v m : ℕ} (hHi : ∀ i, m ≤ i → v.testBit i = false) :
    ∀ (d : ℕ), oddBits v (m + d) = oddBits v m
  | 0 => rfl
  | d + 1 => by simp [oddBits, hHi (m + d) (by omega), oddBits_trim_above hHi d]
theorem oddBits_and_xor (e a b : ℕ) :
    ∀ (n : ℕ),
      oddBits (e &&& (a ^^^ b)) n = xor (oddBits (e &&& a) n) (oddBits (e &&& b) n)
  | 0 => rfl
  | n + 1 => by
      simp only [oddBits, oddBits_and_xor e a b n, Nat.testBit_and, Nat.testBit_xor]
      cases oddBits (e &&& a) n <;> cases oddBits (e &&& b) n <;>
        cases e.testBit n <;> cases a.testBit n <;> cases b.testBit n <;> rfl
theorem oddBits_and_unit (e j : ℕ) : ∀ n, j < n → oddBits
    (e &&& (1 <<< j)) n = e.testBit j
  | 0, hj => nomatch hj
  | n + 1, hj => by
      dsimp only [oddBits]
      rcases eq_or_ne j n with rfl | hEq
      · rw [oddBits_eq_false_of_lt j fun i hi ↦ by
          simp [Nat.testBit_and, Nat.testBit_shiftLeft, show ¬(i ≥ j) by omega]]
        simp [Nat.testBit_and, Nat.testBit_shiftLeft, show (1 : ℕ).testBit 0 = true from rfl]
      · rw [oddBits_and_unit e j n (by omega), Nat.testBit_and, Nat.testBit_shiftLeft,
          show n - j = (n - j - 1) + 1 by omega, CoinWrap.testBit_one_succ]
        simp [show n ≥ j by omega]
/-- Fixed `376`-bit parity evaluation (`42 + 334 = 376`) on environment `e`. -/
def wBit (e msk : ℕ) : Bool := oddBits (e &&& msk) 376
theorem wBit_zero (e : ℕ) : wBit e 0 = false := oddBits_eq_false_of_lt 376 fun _ _ ↦ by simp
theorem wBit_unit (e j : ℕ) (hj : j < 376) : wBit e (1 <<< j) = e.testBit j :=
  oddBits_and_unit e j 376 hj

/-- Pack wire parities `ms` LSB-first into a `Nat`. -/
def wPack (e : ℕ) : List ℕ → ℕ
  | [] => 0
  | ma :: ms => cond (wBit e ma) 1 0 + 2 * wPack e ms
theorem wPack_lt_pow (e : ℕ) : ∀ (ms : List ℕ), wPack e ms < 2 ^ ms.length
  | [] => by simp [wPack]
  | ma :: ms => by
      have := wPack_lt_pow e ms
      cases h : wBit e ma <;> simp [wPack, h, Nat.pow_succ] <;> omega
theorem testBit_wPack (e : ℕ) :
    ∀ (ms : List ℕ) (idx : ℕ), (wPack e ms).testBit idx = wBit e (ms.getD idx 0)
  | [], _ => by rw [wPack, Nat.zero_testBit, List.getD_nil, wBit_zero]
  | ma :: ms, 0 => by
      cases h : wBit e ma <;> simp [wPack, h, List.getD, Nat.testBit, Nat.add_mul_mod_self_left]
  | ma :: ms, idx + 1 => by
      rw [wPack, show (ma :: ms).getD (idx + 1) 0 = ms.getD idx 0 by simp [List.getD],
          Nat.testBit_succ, show (cond (wBit e ma) 1 0 + 2 * wPack e ms) / 2 = wPack e ms by
            cases wBit e ma <;> dsimp only [cond] <;> omega, testBit_wPack e ms idx]
@[simp] theorem nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
@[simp] theorem nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
@[simp] theorem nat_land_eq (a b : ℕ) : Nat.land a b = a &&& b := rfl
@[simp] theorem nat_lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl
@[simp] theorem nat_xor_eq (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
@[simp] theorem nat_shr_eq (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem nat_shl_one (d : ℕ) : Nat.shiftLeft 1 d = 2 ^ d := by simp [Nat.shiftLeft_eq]
theorem blt_eq_false_iff (a b : ℕ) : Nat.blt a b = false ↔ b ≤ a := by
  rw [← Bool.not_eq_true, Nat.blt_eq, not_lt]
/-- Binary tree of `2^m`-bit GMP truth-table `Nat`s for bit-parallel sub-XAG evaluation. -/
inductive WTree : Type
  | empty : WTree
  | leaf : ℕ → WTree
  | node : WTree → WTree → WTree
/-- Left child of `WTree` (`.empty` on non-nodes). -/
def wLeft : WTree → WTree
  | .node l _ => l
  | _ => .empty
/-- Right child of `WTree` (`.empty` on non-nodes). -/
def wRight : WTree → WTree
  | .node _ r => r
  | _ => .empty
/-- Force `v` to a GMP literal in WHNF before storing in a constructor. -/
def forceNat {α : Type} : ℕ → (ℕ → α) → α
  | 0, fn => fn 0
  | k + 1, fn => fn (Nat.succ k)
theorem forceNat_eq {α : Type} : ∀ (v : ℕ) (fn : ℕ → α), forceNat v fn = fn v
  | 0, _ | _ + 1, _ => rfl
/-- Monomorphic `testBit` using GMP kernel primitives (`0` typeclass unfoldings). -/
def bitAt (v i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight v i) 1) 1
theorem bitAt_eq_testBit (v i : ℕ) : bitAt v i = v.testBit i := by
  rw [bitAt, Nat.testBit, nat_shr_eq, nat_land_eq, Nat.and_comm 1 (v >>> i)]
  have := Nat.and_one_is_mod (v >>> i)
  rcases (by omega : (v >>> i) &&& 1 = 0 ∨ (v >>> i) &&& 1 = 1) with h | h <;> rw [h] <;> rfl
/-- Read leaf `idx < 2^d` of a depth-`d` `WTree` (`0` on `.empty`). -/
def getWTree : ℕ → WTree → ℕ → ℕ
  | _, .empty, _ => 0
  | 0, .leaf v, _ => v
  | 0, .node _ _, _ => 0
  | _ + 1, .leaf _, _ => 0
  | d + 1, .node l r, idx =>
      let half := Nat.shiftLeft 1 d
      match Nat.blt idx half with
      | true => getWTree d l idx
      | false => getWTree d r (Nat.sub idx half)
/-- Update leaf `idx < 2^d` of a depth-`d` `WTree` to `v`. -/
def setWTree : ℕ → ℕ → ℕ → WTree → WTree
  | 0, _, v, _ => .leaf v
  | d + 1, idx, v, tr =>
      let half := Nat.shiftLeft 1 d
      match Nat.blt idx half with
      | true => .node (setWTree d idx v (wLeft tr)) (wRight tr)
      | false => .node (wLeft tr) (setWTree d (Nat.sub idx half) v (wRight tr))
theorem getWTree_empty : ∀ (d j : ℕ), getWTree d .empty j = 0
  | 0, _ | _ + 1, _ => rfl
theorem getWTree_succ (d j : ℕ) (tr : WTree) :
    getWTree (d + 1) tr j =
      match Nat.blt j (Nat.shiftLeft 1 d) with
      | true => getWTree d (wLeft tr) j
      | false => getWTree d (wRight tr) (Nat.sub j (Nat.shiftLeft 1 d)) := by
  cases tr <;> dsimp only [getWTree, wLeft, wRight] <;>
    cases Nat.blt j (Nat.shiftLeft 1 d) <;> exact (getWTree_empty d _).symm

theorem getWTree_setWTree : ∀ d idx j v tr, idx < 2 ^ d → j < 2 ^ d →
    getWTree d (setWTree d idx v tr) j = if j = idx then v else getWTree d tr j
  | 0, idx, j, _, _, _, _ => by
      simp [setWTree, getWTree, show idx = 0 by omega, show j = 0 by omega]
  | d + 1, idx, j, v, tr, hI, hJ => by
      rw [getWTree_succ d j tr]
      dsimp only [setWTree]
      rw [nat_shl_one d, nat_sub_eq, nat_sub_eq]
      cases hIL : Nat.blt idx (2 ^ d) <;> cases hJL : Nat.blt j (2 ^ d) <;>
        dsimp only [getWTree] <;> rw [nat_shl_one d, hJL]
      · have := (⟨(blt_eq_false_iff _ _).mp hIL,
          (blt_eq_false_iff _ _).mp hJL, Nat.pow_succ 2 d⟩ : _ ∧ _ ∧ _)
        rw [nat_sub_eq, getWTree_setWTree d _ _ v (wRight tr) (by omega) (by omega)]
        by_cases hEq : j = idx <;> simp [hEq, show j - 2 ^ d = idx - 2 ^ d ↔ j = idx by omega]
      · simp [show j ≠ idx from fun h ↦ by simp [h, hIL] at hJL]
      · simp [show j ≠ idx from fun h ↦ by simp [h, hIL] at hJL]
      · exact getWTree_setWTree d idx j v (wLeft tr)
          (Nat.blt_eq.mp hIL) (Nat.blt_eq.mp hJL)
/-- `2^m`-bit truth table for input wire `i`: bit `r < 2^m` equals `r.testBit i`. -/
def varTable : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, i =>
      let half := Nat.shiftLeft 1 m
      match Nat.beq i m with
      | true => Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 half) 1) half
      | false =>
          forceNat (varTable m i) fun sub ↦
            Nat.lor sub (Nat.shiftLeft sub half)
theorem varTable_spec : ∀ m i, i < m →
    varTable m i < 2 ^ (2 ^ m) ∧ ∀ r < 2 ^ m, (varTable m i).testBit r =
    r.testBit i
  | 0, _, hi => nomatch hi
  | m + 1, i, hi => by
      have h2m : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      have hShl {k x} (hx : x < 2 ^ (2 ^ k)) : x <<< (2 ^ k) < 2 ^ (2 ^ (k + 1)) := by
        rw [Nat.shiftLeft_eq, show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by ring, Nat.pow_add]
        exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
      dsimp only [varTable]
      rw [nat_shl_one m]
      cases hBeq : Nat.beq i m
      · have him : i + 1 ≤ m := Nat.lt_of_le_of_ne (by omega) fun h ↦
          Bool.noConfusion (hBeq.symm.trans (Nat.beq_eq.mpr h))
        obtain ⟨hL, hB⟩ := varTable_spec m i him
        simp only [forceNat_eq, nat_lor_eq,
          show Nat.shiftLeft _ _ = varTable m i <<< (2 ^ m) from rfl]
        refine ⟨Nat.or_lt_two_pow (hL.trans_le (Nat.pow_le_pow_right (by omega)
          (Nat.pow_le_pow_right (by omega) (by omega)))) (hShl hL), fun r hr ↦ ?_⟩
        rw [Nat.testBit_or, Nat.testBit_shiftLeft]
        if hGe : r ≥ 2 ^ m then
          obtain ⟨q, hq⟩ := Nat.pow_dvd_pow 2 him
          have hM : (r - 2 ^ m) % 2 ^ (i + 1) = r % 2 ^ (i + 1) := by
            conv_rhs =>
              rw [show r = (r - 2 ^ m) + 2 ^ (i + 1) * q by omega, Nat.add_mul_mod_self_left]
          rw [Nat.testBit_lt_two_pow (hL.trans_le (Nat.pow_le_pow_right (by omega) hGe)),
            Bool.false_or, decide_eq_true hGe, Bool.true_and, hB _ (by omega)]
          simpa [Nat.testBit_mod_two_pow, Nat.lt_succ_self i] using congrArg (·.testBit i) hM
        else simp [hGe, hB r (by omega)]
      · obtain rfl : i = m := Nat.beq_eq.mp hBeq
        simp only [nat_shl_one (2 ^ i), nat_sub_eq,
          show Nat.shiftLeft _ _ = (2 ^ (2 ^ i) - 1) <<< (2 ^ i) from rfl]
        refine ⟨hShl (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one), fun r hr ↦ ?_⟩
        rw [Nat.testBit_shiftLeft]
        if hGe : r ≥ 2 ^ i then
          have hS : r - 2 ^ i < 2 ^ i := by omega
          rw [decide_eq_true hGe, Bool.true_and, Nat.testBit_two_pow_sub_one,
            decide_eq_true hS, Nat.testBit, Nat.shiftRight_eq_div_pow,
            show r = (r - 2 ^ i) + 2 ^ i * 1 by omega,
            Nat.add_mul_div_left _ _ (Nat.two_pow_pos i), Nat.div_eq_of_lt hS]
          rfl
        else simp [hGe, Nat.testBit_lt_two_pow (show r < 2 ^ i by omega)]
/-- Direct `WTree` XOR parity over leaf truth tables or global masks selected by `mask`. -/
def xorWTree : ℕ → WTree → ℕ → ℕ
  | _, .empty, _ => 0
  | 0, .leaf v, mask =>
      match bitAt mask 0 with
      | true => v
      | false => 0
  | 0, .node _ _, _ => 0
  | _ + 1, .leaf _, _ => 0
  | d + 1, .node l r, mask =>
      let half := Nat.shiftLeft 1 d
      let mL := Nat.land mask (Nat.sub (Nat.shiftLeft 1 half) 1)
      let mR := Nat.land (Nat.shiftRight mask half) (Nat.sub (Nat.shiftLeft 1 half) 1)
      match Nat.beq mL 0, Nat.beq mR 0 with
      | true, true => 0
      | false, true => xorWTree d l mL
      | true, false => xorWTree d r mR
      | false, false => Nat.xor (xorWTree d l mL) (xorWTree d r mR)
theorem xorWTree_zero : ∀ d tr, xorWTree d tr 0 = 0
  | 0, tr => by cases tr <;> rfl
  | _ + 1, tr => by cases tr <;> simp [xorWTree]
theorem xorWTree_succ (d : ℕ) (tr : WTree) (mask : ℕ) :
    let half := Nat.shiftLeft 1 d
    let mLo := Nat.sub (Nat.shiftLeft 1 half) 1
    xorWTree (d + 1) tr mask = xorWTree d (wLeft tr) (Nat.land mask mLo) ^^^
      xorWTree d (wRight tr) (Nat.land (Nat.shiftRight mask half) mLo) := by
  intro half mLo
  cases tr with
  | empty | leaf _ => cases d <;> simp [xorWTree, wLeft, wRight]
  | node l r =>
      dsimp only [xorWTree, wLeft, wRight]
      cases hBL : Nat.beq _ 0 <;> cases hBR : Nat.beq _ 0
      · rfl
      · rw [Nat.beq_eq.mp hBR, xorWTree_zero, Nat.xor_zero]
      · rw [Nat.beq_eq.mp hBL, xorWTree_zero, Nat.zero_xor]
      · rw [Nat.beq_eq.mp hBL, Nat.beq_eq.mp hBR, xorWTree_zero, xorWTree_zero, Nat.zero_xor]
theorem testBit_xorWTree (e row : ℕ) : ∀ d vTr mTr mask,
    (∀ j < 2 ^ d, (getWTree d vTr j).testBit row = wBit e (getWTree d mTr j)) →
    (xorWTree d vTr mask).testBit row = wBit e (xorWTree d mTr mask)
  | 0, vTr, mTr, mask, hBit => by
      have hz (t) : xorWTree 0 t mask = cond (bitAt mask 0) (getWTree 0 t 0) 0 := by
        cases t <;> dsimp only [xorWTree] <;> cases bitAt mask 0 <;> rfl
      rw [hz, hz]
      cases bitAt mask 0 <;> simp [wBit_zero, hBit 0 (by omega)]
  | d + 1, vTr, mTr, mask, hBit => by
      have : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
      rw [xorWTree_succ, xorWTree_succ, Nat.testBit_xor, wBit, oddBits_and_xor, ← wBit, ← wBit]
      refine congrArg₂ xor (testBit_xorWTree e row d _ _ _ fun j hj ↦ ?_)
        (testBit_xorWTree e row d _ _ _ fun j hj ↦ ?_)
      · have h := hBit j (by omega)
        rwa [getWTree_succ, getWTree_succ, nat_shl_one d, Nat.blt_eq.mpr hj] at h
      · have h := hBit (2 ^ d + j) (by omega)
        rw [getWTree_succ, getWTree_succ, nat_shl_one d,
          (blt_eq_false_iff (2 ^ d + j) (2 ^ d)).mpr (by omega)] at h
        dsimp only [cond] at h
        rwa [nat_sub_eq, Nat.add_sub_cancel_left] at h
end QuantumComputation.Specs.PhotochemistrySolution.FermatInverse
end

noncomputable section
set_option maxRecDepth 4096
namespace QuantumComputation.Specs.PhotochemistrySolution.Cartesian254
open QuantumComputation.Specs
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.ScreenFermatCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (decodeUltraNuc192
    decodePinnedNuc192 phiU1 phiU1Inv phiU1_spec phiU1Inv_spec eqSec bitAt letB allTree)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (allTree_zero)
/-- `16`-entry quotient lookup `(h1, q5, isX)` for `B2_x_255`. -/
def b2QEntry : ℕ → ℕ × ℕ × Bool
  | 0 => (1, 0, false)
  | 1 => (2, 0, false)
  | 2 => (0, 1, false)
  | 3 => (1, 3, false)
  | 4 => (0, 0, false)
  | 5 => (1, 2, false)
  | 6 => (1, 1, false)
  | 7 => (2, 1, false)
  | 8 => (2, 2, false)
  | 9 => (2, 4, false)
  | 10 => (1, 4, false)
  | 11 => (0, 3, false)
  | 12 => (0, 4, false)
  | 13 => (0, 2, false)
  | 14 => (2, 3, false)
  | _ => (0, 6, true)
/-- Exact `B2_x_255` map `a8 ↦ (r17, h1, q5, isX)` on `a8 < 256`. -/
def b2Spec (a8 : ℕ) : ℕ × ℕ × ℕ × Bool :=
  let lo4 := a8 % 16; let hi4 := (a8 / 16) % 16; let q := cond (hi4 == 15) lo4 hi4;
  let r17 := cond (hi4 == 15) 16 lo4; let e := b2QEntry q
  (r17, e.1, e.2.1, e.2.2)
/-- `33 → 11 × 3` coset-folded remainder map `r ↦ (r11, h2)` for `B6_y_1023_coset`. -/
def b6Rem33 (r : ℕ) : ℕ × ℕ :=
  cond (r == 32) (9, 2)
    (let r4 := r / 16
     let r30 := r % 16
     cond (Nat.blt r30 11) (r30, r4)
       (cond (r30 == 11) (10 - 2 * r4, 2)
         (Nat.xor (r30 - 8) (4 * r4), 2)))
/-- Exact `B6_y_1023_coset` map `a10 ↦ (r11, h2, q31, isY)` on `a10 < 1024`. -/
def b6Spec (a10 : ℕ) : ℕ × ℕ × ℕ × Bool :=
  let lo5 := a10 % 32; let hi5 := (a10 / 32) % 32; let q31 := cond (hi5 == 31) lo5 hi5;
  let r := cond (hi5 == 31) 32 lo5; let rh := b6Rem33 r
  (rh.1, rh.2, q31, q31 == 31)
/-- `13`-AND `B11_z2_nuc13` `8`-bit `z2` bijection on `row = h2 + 4 * x` (`louts[9..16]`). -/
def b11Z2Row (row : ℕ) : ℕ :=
  letB (bitAt row 0) fun b0 ↦
  letB (bitAt row 1) fun b1 ↦
  letB (bitAt row 2) fun b2 ↦
  letB (bitAt row 3) fun b3 ↦
  letB (bitAt row 4) fun b4 ↦
  letB (bitAt row 5) fun b5 ↦
  letB (bitAt row 6) fun b6 ↦
  letB (bitAt row 7) fun b7 ↦
  letB (Bool.and b6 b7) fun g0 ↦
  letB (Bool.and b5 b4) fun g1 ↦
  letB (Bool.and g1 (xor (xor true b3) b7)) fun g2 ↦
  letB (Bool.and (xor b7 g0) (xor (xor b6 g0) g2)) fun g3 ↦
  letB (Bool.and (xor (xor true b2) g0) (xor (xor true b0) (xor b1 b2))) fun g4 ↦
  letB (Bool.and g4 (xor (xor true g3) g4)) fun g5 ↦
  letB (Bool.and (xor (xor (xor true b0) (xor b1 g3)) (xor g4 g5)) (xor (xor b0 b1) g0)) fun g6 ↦
  letB (Bool.and (xor (xor (xor true b0) (xor b1 b2)) (xor (xor b7 g0) (xor g4 g5)))
      (xor g3 g6)) fun g7 ↦
  letB (Bool.and (xor (xor g3 g4) (xor g6 g7)) b1) fun g8 ↦
  letB (Bool.and (xor (xor g2 g5) g6) (xor (xor g0 g5) (xor g6 g8))) fun g9 ↦
  letB (Bool.and (xor (xor (xor b1 b4) (xor b7 g0)) (xor g7 g9))
      (xor (xor (xor true g0) (xor g3 g5)) g6)) fun g11 ↦
  (Nat.lor (Nat.lor (Nat.lor (cond (xor (xor (xor true b1) (xor g0 g4)) g7) 1 0)
      (cond (xor b0 b2) 2 0)) (Nat.lor (cond (xor (xor true b0) (xor b1 b7)) 4 0) (cond b5 8 0)))
      (Nat.lor (Nat.lor (cond b4 16 0) (cond b3 32 0))
      (Nat.lor (cond (xor (xor (xor true b1) (xor b4 b6)) (xor g7 g11)) 64 0)
      (cond (xor (xor b7 g0) g6) 128 0))))
/-- `z2` electron index `0..186` from `(h2, x)` with `h2 < 3, x < 64`. -/
def b11Z2OfHX (h2 x : ℕ) : ℕ := b11Z2Row (h2 + 4 * (x % 64))
def cart254V23 (lo1 lo2 w11 : ℕ) : ℕ := lo1 + 64 * lo2 + 4096 * w11
/-- Unpack byte `k` (`0 ≤ k < 64`) from a `512`-bit little-endian `ℕ` lookup constant. -/
def byteAt64 (tbl k : ℕ) : ℕ := (tbl >>> (8 * k)) % 256
/-- Unpack byte `i` (`0 ≤ i < 256`) from four `512`-bit little-endian `ℕ` lookup constants. -/
def byteAt256 (t0 t1 t2 t3 i : ℕ) : ℕ :=
  cond (Nat.blt i 128)
    (cond (Nat.blt i 64) (byteAt64 t0 i) (byteAt64 t1 (i - 64)))
    (cond (Nat.blt i 192) (byteAt64 t2 (i - 128)) (byteAt64 t3 (i - 192)))
/-- Reindex `foldSum M` along a bijection `σ` with two-sided inverse `τ` on `< M`. -/
theorem foldSum_perm (M : ℕ) (σ τ : ℕ → ℕ)
    (hσ : ∀ i < M, σ i < M ∧ τ (σ i) = i) (hτ : ∀ j < M, τ j < M ∧ σ (τ j) = j)
    (f : ℕ → ℕ) : (foldSum M fun i ↦ f (σ i)) = foldSum M f := by
  rw [← sum_fin_eq_foldSum M, ← sum_fin_eq_foldSum M]
  exact Finset.sum_bij (fun i _ ↦ ⟨σ i.val, (hσ i.val i.isLt).1⟩) (fun _ _ ↦ Finset.mem_univ _)
    (fun a _ b _ hab ↦ Fin.ext <| (hσ a.val a.isLt).2.symm.trans <|
      (congrArg τ (congrArg Fin.val hab)).trans (hσ b.val b.isLt).2)
    (fun j _ ↦ ⟨⟨τ j.val, (hτ j.val j.isLt).1⟩, Finset.mem_univ _, Fin.ext (hτ j.val j.isLt).2⟩)
    (fun _ _ ↦ rfl)
/-- Inverse of `b2Spec` on `(r17, h1, q5) ∈ Fin 17 × Fin 3 × Fin 5 → Fin 255`. -/
def b2Inv255 (r17 h1 q5 : ℕ) : ℕ :=
  let q := byteAt64 0x90e0807010a030506000c0b0d0204 (h1 * 5 + q5)
  cond (r17 == 16) (240 + q) (16 * q + r17)
theorem b2Spec_255 : (b2Spec 255).2.2.2 = true := rfl
theorem b2Spec_lt255 {a8 : ℕ} (ha : a8 < 255) :
    (b2Spec a8).1 < 17 ∧ (b2Spec a8).2.1 < 3 ∧ (b2Spec a8).2.2.1 < 5 ∧
      (b2Spec a8).2.2.2 = false ∧
      b2Inv255 (b2Spec a8).1 (b2Spec a8).2.1 (b2Spec a8).2.2.1 = a8 := by
  simpa only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, and_assoc] using allTree_zero
    (rfl : allTree 9 0 255 (fun x ↦
      let p := b2Spec x
      Nat.blt p.1 17 && Nat.blt p.2.1 3 && Nat.blt p.2.2.1 5 &&
        (p.2.2.2 == false) && (b2Inv255 p.1 p.2.1 p.2.2.1 == x)) = true) ha
theorem b2Inv255_spec {r17 h1 q5 : ℕ} (hr : r17 < 17) (hh : h1 < 3) (hq : q5 < 5) :
    b2Inv255 r17 h1 q5 < 255 ∧ b2Spec (b2Inv255 r17 h1 q5) = (r17, h1, q5, false) := by
  simpa only [show (r17 * 15 + (h1 * 5 + q5)) / 15 = r17 by omega,
    show ((r17 * 15 + (h1 * 5 + q5)) % 15) / 5 = h1 by omega,
    show (r17 * 15 + (h1 * 5 + q5)) % 5 = q5 by omega,
    Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, Prod.ext_iff, and_assoc] using
    allTree_zero (rfl : allTree 9 0 255 (fun idx ↦
      let a8 := b2Inv255 (idx / 15) ((idx % 15) / 5) (idx % 5)
      let p := b2Spec a8
      Nat.blt a8 255 && (p.1 == idx / 15) && (p.2.1 == (idx % 15) / 5) &&
        (p.2.2.1 == idx % 5) && (p.2.2.2 == false)) = true)
      (show r17 * 15 + (h1 * 5 + q5) < 255 by omega)
/-- Inverse of `b6Spec` on `(r11, h2, q31) ∈ Fin 11 × Fin 3 × Fin 31 → Fin 1023`. -/
def b6Inv1023 (r11 h2 q31 : ℕ) : ℕ :=
  let r :=
      byteAt64 ((0xb <<< 256) ||| (0x1a0a2019091b18080f17070e16060d15 <<< 128) |||
      0x50c14041f13031e12021d11011c1000) (r11 * 3 + h2)
  cond (r == 32) (992 + q31) (32 * q31 + r)
theorem b6Spec_1023 : (b6Spec 1023).2.2.2 = true := rfl
theorem b6Spec_lt1023 {a10 : ℕ} (ha : a10 < 1023) :
    (b6Spec a10).1 < 11 ∧ (b6Spec a10).2.1 < 3 ∧ (b6Spec a10).2.2.1 < 31 ∧
      (b6Spec a10).2.2.2 = false ∧
      b6Inv1023 (b6Spec a10).1 (b6Spec a10).2.1 (b6Spec a10).2.2.1 = a10 := by
  simpa only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, and_assoc] using allTree_zero
    (rfl : allTree 11 0 1023 (fun x ↦
      let p := b6Spec x
      Nat.blt p.1 11 && Nat.blt p.2.1 3 && Nat.blt p.2.2.1 31 &&
        (p.2.2.2 == false) && (b6Inv1023 p.1 p.2.1 p.2.2.1 == x)) = true) ha
theorem b6Inv1023_spec {r11 h2 q31 : ℕ} (hr : r11 < 11) (hh : h2 < 3) (hq : q31 < 31) :
    b6Inv1023 r11 h2 q31 < 1023 ∧ b6Spec (b6Inv1023 r11 h2 q31) = (r11, h2, q31, false) := by
  simpa only [show (r11 * 93 + (h2 * 31 + q31)) / 93 = r11 by omega,
    show ((r11 * 93 + (h2 * 31 + q31)) % 93) / 31 = h2 by omega,
    show (r11 * 93 + (h2 * 31 + q31)) % 31 = q31 by omega,
    Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, Prod.ext_iff, and_assoc] using
    allTree_zero (rfl : allTree 11 0 1023 (fun idx ↦
      let a10 := b6Inv1023 (idx / 93) ((idx % 93) / 31) (idx % 31)
      let p := b6Spec a10
      Nat.blt a10 1023 && (p.1 == idx / 93) && (p.2.1 == (idx % 93) / 31) &&
        (p.2.2.1 == idx % 31) && (p.2.2.2 == false)) = true)
      (show r11 * 93 + (h2 * 31 + q31) < 1023 by omega)
/-- Pack `(a8, a10) ∈ Fin 255 × Fin 1023` into `((u1 * 3 + h1) * 3 + h2) * 155 + q5 * 31 + q31`. -/
def cartGridFwd (p : ℕ) : ℕ :=
  let a8 := p / 1023; let a10 := p % 1023; let px := b2Spec a8; let py := b6Spec a10;
  let u1 := phiU1 py.1 px.1
  (((u1 * 3 + px.2.1) * 3 + py.2.1) * 5 + px.2.2.1) * 31 + py.2.2.1
/-- Inverse of `cartGridFwd` on `idx < 260865`. -/
def cartGridInv (idx : ℕ) : ℕ :=
  let q31 := idx % 31; let t1 := idx / 31; let q5 := t1 % 5; let t2 := t1 / 5; let h2 := t2 % 3;
  let t3 := t2 / 3; let h1 := t3 % 3; let u1 := t3 / 3; let pu := phiU1Inv u1
  b2Inv255 pu.2 h1 q5 * 1023 + b6Inv1023 pu.1 h2 q31
theorem cartIdx_digits {u1 h1 h2 q5 q31 : ℕ}
    (hh1 : h1 < 3) (hh2 : h2 < 3) (hq5 : q5 < 5) (hq31 : q31 < 31) :
    let idx := (((u1 * 3 + h1) * 3 + h2) * 5 + q5) * 31 + q31
    idx % 31 = q31 ∧ (idx / 31) % 5 = q5 ∧ (idx / 31 / 5) % 3 = h2 ∧
      (idx / 31 / 5 / 3) % 3 = h1 ∧ idx / 31 / 5 / 3 / 3 = u1 :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩
theorem cartGridFwd_spec {p : ℕ} (hp : p < 260865) :
    cartGridFwd p < 260865 ∧ cartGridInv (cartGridFwd p) = p := by
  obtain ⟨hr17, hh1, hq5, _, hinv2⟩ := b2Spec_lt255 (show p / 1023 < 255 by omega)
  obtain ⟨hr11, hh2, hq31, _, hinv6⟩ := b6Spec_lt1023 (show p % 1023 < 1023 by omega)
  obtain ⟨hu1, hpu⟩ := phiU1_spec hr11 hr17
  obtain ⟨d1, d2, d3, d4, d5⟩ := cartIdx_digits
    (u1 := phiU1 (b6Spec (p % 1023)).1 (b2Spec (p / 1023)).1) hh1 hh2 hq5 hq31
  dsimp only [cartGridFwd, cartGridInv] at d1 d2 d3 d4 d5 ⊢
  rw [d1, d2, d3, d4, d5, hpu, hinv2, hinv6]
  exact ⟨by omega, by omega⟩
theorem cartGridInv_spec {idx : ℕ} (hidx : idx < 260865) :
    cartGridInv idx < 260865 ∧ cartGridFwd (cartGridInv idx) = idx := by
  obtain ⟨hr11, hr17, hpu⟩ := phiU1Inv_spec (show idx / 31 / 5 / 3 / 3 < 187 by omega)
  obtain ⟨ha8, hb2⟩ := b2Inv255_spec hr17 (by omega : (idx / 31 / 5 / 3) % 3 < 3)
    (by omega : (idx / 31) % 5 < 5)
  obtain ⟨ha10, hb6⟩ := b6Inv1023_spec hr11 (by omega : (idx / 31 / 5) % 3 < 3)
    (by omega : idx % 31 < 31)
  dsimp only [cartGridInv, cartGridFwd]
  set b2 := b2Inv255 (phiU1Inv (idx / 31 / 5 / 3 / 3)).2
    ((idx / 31 / 5 / 3) % 3) ((idx / 31) % 5)
  set b6 := b6Inv1023 (phiU1Inv (idx / 31 / 5 / 3 / 3)).1 ((idx / 31 / 5) % 3) (idx % 31)
  rw [show (b2 * 1023 + b6) / 1023 = b2 by omega,
    show (b2 * 1023 + b6) % 1023 = b6 by omega, hb2, hb6]
  simpa only [hpu] using (⟨by omega, by omega⟩ : _ < 260865 ∧ _ = idx)
/-- Reindex `(a8 : Fin 255) × (a10 : Fin 1023)` onto `(u1, h1, h2, q5, q31)`. -/
theorem sum_a8_a10_cart254 (K : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) :
    (∑ a8 : Fin 255, ∑ a10 : Fin 1023,
      K (phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1) (b2Spec a8.val).2.1
        (b6Spec a10.val).2.1 (b2Spec a8.val).2.2.1 (b6Spec a10.val).2.2.1) =
    ∑ u1 : Fin 187, ∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ q5 : Fin 5, ∑ q31 : Fin 31,
      K u1.val h1.val h2.val q5.val q31.val := by
  let G (idx : ℕ) := K (idx / 31 / 5 / 3 / 3) ((idx / 31 / 5 / 3) % 3)
    ((idx / 31 / 5) % 3) ((idx / 31) % 5) (idx % 31)
  trans ∑ p : Fin 260865, G (cartGridFwd p.val)
  · rw [show (260865 : ℕ) = 255 * 1023 from rfl,
      sum_fin_mul (A := 255) (B := 1023) (Nat.succ_pos _) fun p ↦ G (cartGridFwd p)]
    refine Finset.sum_congr rfl fun a8 _ ↦ Finset.sum_congr rfl fun a10 _ ↦ ?_
    obtain ⟨e1, e2, e3, e4, e5⟩ := cartIdx_digits
      (u1 := phiU1 (b6Spec a10.val).1 (b2Spec a8.val).1) (b2Spec_lt255 a8.isLt).2.1
      (b6Spec_lt1023 a10.isLt).2.1 (b2Spec_lt255 a8.isLt).2.2.1 (b6Spec_lt1023 a10.isLt).2.2.1
    dsimp only [G, cartGridFwd] at e1 e2 e3 e4 e5 ⊢
    rw [show (a8.val * 1023 + a10.val) / 1023 = a8.val by omega,
      show (a8.val * 1023 + a10.val) % 1023 = a10.val by omega, e1, e2, e3, e4, e5]
  · rw [sum_fin_eq_foldSum 260865 fun p ↦ G (cartGridFwd p),
      foldSum_perm 260865 cartGridFwd cartGridInv (fun _ ↦ cartGridFwd_spec)
        (fun _ ↦ cartGridInv_spec) G, ← sum_fin_eq_foldSum 260865 G,
      show (260865 : ℕ) = 8415 * 31 from rfl,
      sum_fin_mul (A := 8415) (B := 31) (Nat.succ_pos _) G,
      show (8415 : ℕ) = 1683 * 5 from rfl,
      sum_fin_mul (A := 1683) (B := 5) (Nat.succ_pos _)
        (fun t1 ↦ ∑ q31 : Fin 31, G (t1 * 31 + q31.val)),
      show (1683 : ℕ) = 561 * 3 from rfl,
      sum_fin_mul (A := 561) (B := 3) (Nat.succ_pos _)
        (fun t2 ↦ ∑ q5 : Fin 5, ∑ q31 : Fin 31, G ((t2 * 5 + q5.val) * 31 + q31.val)),
      show (561 : ℕ) = 187 * 3 from rfl,
      sum_fin_mul (A := 187) (B := 3) (Nat.succ_pos _)
        (fun t3 ↦ ∑ h2 : Fin 3, ∑ q5 : Fin 5, ∑ q31 : Fin 31,
          G (((t3 * 3 + h2.val) * 5 + q5.val) * 31 + q31.val))]
    refine Finset.sum_congr rfl fun u1 _ ↦ Finset.sum_congr rfl fun h1 _ ↦
      Finset.sum_congr rfl fun h2 _ ↦ Finset.sum_congr rfl fun q5 _ ↦
      Finset.sum_congr rfl fun q31 _ ↦ ?_
    obtain ⟨e1, e2, e3, e4, e5⟩ :=
      cartIdx_digits (u1 := u1.val) h1.isLt h2.isLt q5.isLt q31.isLt
    dsimp only [G] at e1 e2 e3 e4 e5 ⊢
    rw [e1, e2, e3, e4, e5]
/--
Extension of `b11Z2OfHX` to a bijection `Fin 192 → Fin 192` mapping invalid slots to `187..191` .
-/
def b11Ext192 (raw : ℕ) : ℕ :=
  cond (raw == 47) 187
    (cond (raw == 110) 188
      (cond (raw == 111) 189
        (cond (raw == 174) 190
          (cond (raw == 175) 191 (b11Z2OfHX (raw / 64) (raw % 64))))))
/-- Inverse of `b11Ext192` on `Fin 192`. -/
def b11ExtInv192 (i : ℕ) : ℕ :=
    byteAt256 ((0x1fbfbe1e5e9f5f9e17b7b61656975796 <<< 384) |||
    (0x1b7a7b1a5a9b5b9a1372731252935392 <<< 256) ||| (0x1dbdbc1c5c9d5d9c15b5b41454955594 <<<
    128) ||| 0x19787918589959981170711050915190) ((0xf7e7f0e4e8f4f8e0776770646874786 <<< 384) |||
    (0xbbbba0a4a8b4b8a03b3b20242834382 <<< 256) ||| (0xd7c7d0c4c8d4d8c0574750444854584 <<< 128) |||
    0x9b9b8084889498801b1b00040814180) ((0xafae6f6e2f3f3e2e66a767a627373626 <<< 384) |||
    (0x6aab6baa2b3b3a2a62a363a223333222 <<< 256) ||| (0x6cad6dac2d3d3c2c64a565a425353424 <<<
    128) ||| 0x68a969a82939382860a161a021313020) 0 i
theorem check_b11Ext192 :
    (allTree 9 0 192 (fun raw ↦
      let z := b11Ext192 raw; let v := (decodeUltraNuc192 raw).1
      Nat.blt z 192 && (b11ExtInv192 z == raw) && (Nat.blt z 187 == v) &&
        (Bool.not v || (z == b11Z2OfHX (raw / 64) (raw % 64)))) &&
     allTree 9 0 192 (fun z ↦
      let raw := b11ExtInv192 z
      Nat.blt raw 192 && (b11Ext192 raw == z))) = true := rfl
theorem b11Ext192_spec {raw : ℕ} (h : raw < 192) :
    b11Ext192 raw < 192 ∧ b11ExtInv192 (b11Ext192 raw) = raw ∧
      Nat.blt (b11Ext192 raw) 187 = (decodeUltraNuc192 raw).1 ∧
      ((decodeUltraNuc192 raw).1 = true →
        b11Ext192 raw = b11Z2OfHX (raw / 64) (raw % 64)) := by
  have ht := allTree_zero (Bool.and_eq_true_iff.mp check_b11Ext192).1 h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq,
    beq_iff_eq, and_assoc] at ht
  exact ⟨ht.1, ht.2.1, ht.2.2.1, fun hv ↦ ht.2.2.2.resolve_left (by simp [hv])⟩
theorem b11ExtInv192_spec {z : ℕ} (hz : z < 192) :
    b11ExtInv192 z < 192 ∧ b11Ext192 (b11ExtInv192 z) = z := by
  simpa only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] using
    allTree_zero (Bool.and_eq_true_iff.mp check_b11Ext192).2 hz
/-- Bijection `Fin 192 → Fin 192` transporting `decodeUltraNuc192` to `decodePinnedNuc192`. -/
def ultraToPinned192 (i : ℕ) : ℕ := byteAt256
  ((0x3f3e3d3c3b3a39383736353433323130 <<< 384) ||| (0xbb772d2c2b2a29282726252423222120 <<< 256) |||
      (0x1f1e1d1c1b1a19181716151413121110 <<< 128) ||| 0xf0e0d0c0b0a09080706050403020100)
  ((0xb3b17e767d757c747b737a7279717870 <<< 384) ||| (0xbdbc6d6c6b6a69686766656463626160 <<< 256) |||
      (0x5f5e5d5c5b5a59585756555453525150 <<< 128) ||| 0x4f4e4d4c4b4a49484746454443424140)
  ((0xbab5b9afb8aeb77fb66fb46eb22fb02e <<< 384) ||| (0xbfbeadacabaaa9a8a7a6a5a4a3a2a1a0 <<< 256) |||
      (0x9f9e9d9c9b9a99989796959493929190 <<< 128) ||| 0x8f8e8d8c8b8a89888786858483828180)
  0 i
/-- Inverse of `ultraToPinned192` on `Fin 192`. -/
def pinnedToUltra192 (i : ℕ) : ℕ :=
    byteAt256 ((0x3f3e3d3c3b3a39383736353433323130 <<< 384) |||
    (0xb2b02d2c2b2a29282726252423222120 <<< 256) ||| (0x1f1e1d1c1b1a19181716151413121110 <<<
    128) ||| 0xf0e0d0c0b0a09080706050403020100) ((0xb87d7b79777573712e7c7a7876747270 <<< 384) |||
    (0xb6b46d6c6b6a69686766656463626160 <<< 256) ||| (0x5f5e5d5c5b5a59585756555453525150 <<<
    128) ||| 0x4f4e4d4c4b4a49484746454443424140) ((0xafae6f6e2fbfbdbbb9b7beb57fb37eb1 <<< 384) |||
    (0xbcbaadacabaaa9a8a7a6a5a4a3a2a1a0 <<< 256) ||| (0x9f9e9d9c9b9a99989796959493929190 <<<
    128) ||| 0x8f8e8d8c8b8a89888786858483828180) 0 i
theorem check_ultraToPinned192 :
    (allTree 9 0 192 (fun raw ↦
      let z := ultraToPinned192 raw; let dP := decodePinnedNuc192 z; let dU := decodeUltraNuc192 raw
      Nat.blt z 192 && (pinnedToUltra192 z == raw) && (dP.1 == dU.1) && (dP.2 == dU.2)) &&
     allTree 9 0 192 (fun z ↦
      let raw := pinnedToUltra192 z
      Nat.blt raw 192 && (ultraToPinned192 raw == z))) = true := rfl
theorem ultraToPinned192_spec {raw : ℕ} (h : raw < 192) :
    ultraToPinned192 raw < 192 ∧ pinnedToUltra192 (ultraToPinned192 raw) = raw ∧
      decodePinnedNuc192 (ultraToPinned192 raw) = decodeUltraNuc192 raw := by
  simpa only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, Prod.ext_iff, and_assoc] using
    allTree_zero (Bool.and_eq_true_iff.mp check_ultraToPinned192).1 h
theorem pinnedToUltra192_spec {z : ℕ} (hz : z < 192) :
    pinnedToUltra192 z < 192 ∧ ultraToPinned192 (pinnedToUltra192 z) = z := by
  simpa only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] using
    allTree_zero (Bool.and_eq_true_iff.mp check_ultraToPinned192).2 hz
/-- Raw `11`-bit `W11` integer (`rOuter41Layout[{0..4, 11..14, 31..32}]`) of coin `c`. -/
def w11NatOfCoin (c : Fin (2 ^ 41)) : ℕ :=
  c.val % 32 + 32 * (((c.val / 32) % 1024) / 64) + 512 * (((c.val / 33554432) % 256) / 64)
theorem w11NatOfCoin_lt2048 (c : Fin (2 ^ 41)) : w11NatOfCoin c < 2048 := by
  unfold w11NatOfCoin
  omega
theorem nat_subword_testBit (n s w j : ℕ) (hj : j < w) :
    ((n / 2 ^ s) % 2 ^ w).testBit j = n.testBit (s + j) := by
  rw [← Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_and, Nat.testBit_div_two_pow,
      Nat.testBit_two_pow_sub_one, decide_eq_true hj, Bool.and_true, Nat.add_comm]
theorem w11NatOfCoin_testBit (c : Fin (2 ^ 41)) (j : Fin 11) :
    (w11NatOfCoin c).testBit j.val =
      c.val.testBit
        (if j.val < 5 then j.val else if j.val < 9 then 6 + j.val else 22 + j.val) := by
  have hj := j.isLt
  have hSub (sw sc k : ℕ) (heq : (w11NatOfCoin c / 2 ^ sw) % 2 ^ k = (c.val / 2 ^ sc) % 2 ^ k)
      (hk : sw ≤ j.val ∧ j.val < sw + k) :
      (w11NatOfCoin c).testBit j.val = c.val.testBit (sc + (j.val - sw)) := by
    rw [← nat_subword_testBit c.val sc k _ (by omega), ← heq,
      nat_subword_testBit _ sw k _ (by omega)]
    exact congrArg _ (by omega)
  have hP {a b d : ℕ} (_ : a < 2 ^ 5) (_ : b < 2 ^ 4) (_ : d < 2 ^ 2) :
      ((a + 32 * b + 512 * d) / 2 ^ 0) % 2 ^ 5 = a ∧
      ((a + 32 * b + 512 * d) / 2 ^ 5) % 2 ^ 4 = b ∧
      ((a + 32 * b + 512 * d) / 2 ^ 9) % 2 ^ 2 = d := by omega
  have h059 : (w11NatOfCoin c / 2 ^ 0) % 2 ^ 5 = (c.val / 2 ^ 0) % 2 ^ 5 ∧
      (w11NatOfCoin c / 2 ^ 5) % 2 ^ 4 = (c.val / 2 ^ 11) % 2 ^ 4 ∧
      (w11NatOfCoin c / 2 ^ 9) % 2 ^ 2 = (c.val / 2 ^ 31) % 2 ^ 2 := by
    dsimp only [w11NatOfCoin]
    rw [show c.val % 32 = c.val % 2 ^ 5 from rfl,
      show (1024 : ℕ) = 64 * 2 ^ 4 from rfl, show (256 : ℕ) = 64 * 2 ^ 2 from rfl,
      Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
      show 32 * 64 = 2 ^ 11 from rfl, show 33554432 * 64 = 2 ^ 31 from rfl]
    simpa only [pow_zero, Nat.div_one] using hP (Nat.mod_lt _ (by decide))
      (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  split_ifs with lt5 lt9
  · exact (hSub 0 0 5 h059.1 ⟨by omega, lt5⟩).trans (congrArg _ (by omega))
  · exact (hSub 5 11 4 h059.2.1 ⟨by omega, by omega⟩).trans (congrArg _ (by omega))
  · exact (hSub 9 31 2 h059.2.2 ⟨by omega, by omega⟩).trans (congrArg _ (by omega))
end QuantumComputation.Specs.PhotochemistrySolution.Cartesian254
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708
open QuantumComputation.Specs
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.ScreenFermatCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1ZeroNEremSpec (bSum)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (phiU1 decodeUltraNuc192
    eeCellFermat eqSec allTree allTree_zero blt_eq_false_iff)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Cartesian254 (b2Spec b6Spec b2Spec_255
    b2Spec_lt255 b6Spec_1023 b6Spec_lt1023 sum_a8_a10_cart254 w11NatOfCoin b11Z2OfHX)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Cartesian254 (cart254V23 b11Ext192
    b11ExtInv192 b11Ext192_spec b11ExtInv192_spec foldSum_perm)
set_option allowUnsafeReducibility true in
attribute [local irreducible] foldSum bSum
/-- Pack `(hi8, lo8, hi10, lo10, c5)` into `ℕ`. -/
def tier1PackCoin5 (hi8 lo8 hi10 lo10 c5 : ℕ) : ℕ :=
  (((hi8 * 256 + lo8) * 1024 + hi10) * 1024 + lo10) * 32 + c5
/-- Construct `Fin (2 ^ 41)` from `(hi8, lo8, hi10, lo10, c5)`. -/
def tier1CoinOf5 (hi8 lo8 hi10 lo10 c5 : ℕ) : Fin (2 ^ 41) :=
  ⟨tier1PackCoin5 hi8 lo8 hi10 lo10 c5 % 2 ^ 41, Nat.mod_lt _ (Nat.two_pow_pos 41)⟩
theorem tier1CoinOf5_digits {hi8 lo8 hi10 lo10 c5 : ℕ}
    (h1 : hi8 < 256) (h2 : lo8 < 256) (h3 : hi10 < 1024) (h4 : lo10 < 1024) (h5 : c5 < 32) :
    let c := tier1CoinOf5 hi8 lo8 hi10 lo10 c5
    c.val % 32 = c5 ∧ ((c.val / 32) % 1048576) % 1024 = lo10 ∧
      ((c.val / 32) % 1048576) / 1024 = hi10 ∧ (c.val / 33554432) % 256 = lo8 ∧
      (c.val / 33554432) / 256 = hi8 ∧ (c.val / 32) % 1024 = lo10 := by
  have hc : (tier1CoinOf5 hi8 lo8 hi10 lo10 c5).val = tier1PackCoin5 hi8 lo8 hi10 lo10 c5 :=
    Nat.mod_eq_of_lt (by
      dsimp [tier1PackCoin5]
      omega)
  dsimp only
  rw [hc, tier1PackCoin5]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
theorem w11NatOfCoin_tier1CoinOf5 {hi8 lo8 hi10 lo10 c5 : ℕ}
    (h1 : hi8 < 256) (h2 : lo8 < 256) (h3 : hi10 < 1024) (h4 : lo10 < 1024) (h5 : c5 < 32) :
    w11NatOfCoin (tier1CoinOf5 hi8 lo8 hi10 lo10 c5) =
      c5 + 32 * (lo10 / 64) + 512 * (lo8 / 64) := by
  obtain ⟨dc5, _, _, dlo8, _, dm10⟩ := tier1CoinOf5_digits h1 h2 h3 h4 h5
  rw [w11NatOfCoin, dc5, dm10, dlo8]
/-- Split `∑ c : Fin (2 ^ 41)` into `5` nested `Fin` sums via `tier1CoinOf5`. -/
theorem tier1_sum_coin41_split5 (H : Fin (2 ^ 41) → ℕ) :
    (∑ c : Fin (2 ^ 41), H c) =
      ∑ hi8 : Fin 256, ∑ lo8 : Fin 256, ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
        H (tier1CoinOf5 hi8.val lo8.val hi10.val lo10.val c5.val) := by
  let g (n : ℕ) := H ⟨n % 2 ^ 41, Nat.mod_lt _ (Nat.two_pow_pos 41)⟩
  trans ∑ x : Fin (68719476736 * 32), g x.val
  · exact Finset.sum_bij (fun c _ ↦ ⟨c.val, c.isLt⟩) (fun _ _ ↦ Finset.mem_univ _)
      (fun _ _ _ _ h ↦ Fin.ext (congrArg Fin.val h))
      (fun x _ ↦ ⟨⟨x.val, x.isLt⟩, Finset.mem_univ _, rfl⟩)
      (fun c _ ↦ congrArg H (Fin.ext (Nat.mod_eq_of_lt c.isLt)).symm)
  · rw [sum_fin_mul (A := 68719476736) (B := 32) (Nat.succ_pos _) g,
      show (68719476736 : ℕ) = 67108864 * 1024 from rfl,
      sum_fin_mul (A := 67108864) (B := 1024) (Nat.succ_pos _)
        (fun t1 ↦ ∑ c5 : Fin 32, g (t1 * 32 + c5.val)),
      show (67108864 : ℕ) = 65536 * 1024 from rfl,
      sum_fin_mul (A := 65536) (B := 1024) (Nat.succ_pos _)
        (fun t2 ↦ ∑ lo10 : Fin 1024, ∑ c5 : Fin 32, g ((t2 * 1024 + lo10.val) * 32 + c5.val)),
      show (65536 : ℕ) = 256 * 256 from rfl,
      sum_fin_mul (A := 256) (B := 256) (Nat.succ_pos _)
        (fun t3 ↦ ∑ hi10 : Fin 1024, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
          g (((t3 * 1024 + hi10.val) * 1024 + lo10.val) * 32 + c5.val))]
    rfl
/-- Reverse reindexing `r ↦ N - 1 - r` on `Fin N`. -/
theorem tier1_sum_rev_fin {N : ℕ} (f : ℕ → ℕ) :
    (∑ r : Fin N, f (N - 1 - r.val)) = ∑ a : Fin N, f a.val :=
  Finset.sum_bij (fun r _ ↦ ⟨N - 1 - r.val, by omega⟩) (fun _ _ ↦ Finset.mem_univ _)
    (fun r1 _ r2 _ h ↦ Fin.ext ((Nat.sub_sub_self (Nat.le_sub_one_of_lt r1.isLt)).symm.trans
      ((congrArg (N - 1 - ·) (congrArg Fin.val h)).trans
        (Nat.sub_sub_self (Nat.le_sub_one_of_lt r2.isLt)))))
    (fun a _ ↦ ⟨⟨N - 1 - a.val, by omega⟩, Finset.mem_univ _,
      Fin.ext (Nat.sub_sub_self (Nat.le_sub_one_of_lt a.isLt))⟩)
    (fun _ _ ↦ rfl)
/-- Reindex `(lo10 : Fin 1024) × (c5 : Fin 32)` onto `u15 : Fin 32768`. -/
theorem tier1_sum_lo10_c5_u15 (f : ℕ → ℕ) :
    (∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
      f ((lo10.val % 64) + 64 * c5.val + 2048 * (lo10.val / 64))) =
      ∑ u15 : Fin 32768, f u15.val := by
  rw [show (1024 : ℕ) = 16 * 64 from rfl, show (32768 : ℕ) = 512 * 64 from rfl,
      sum_fin_mul (A := 16) (B := 64) (Nat.succ_pos _)
        (fun l ↦ ∑ c5 : Fin 32, f ((l % 64) + 64 * c5.val + 2048 * (l / 64))),
      sum_fin_mul (A := 512) (B := 64) (Nat.succ_pos _) f, show (512 : ℕ) = 16 * 32 from rfl,
      sum_fin_mul (A := 16) (B := 32) (Nat.succ_pos _)
          (fun k ↦ ∑ lo2 : Fin 64, f (k * 64 + lo2.val))]
  exact Finset.sum_congr rfl fun b4 _ ↦ Finset.sum_comm.trans
    (Finset.sum_congr rfl fun c5 _ ↦ Finset.sum_congr rfl fun lo2 _ ↦ by
      have := lo2.isLt
      exact congrArg f (by omega))
/-- Reindex `(lo8 : Fin 256) × (lo10 : Fin 1024) × (c5 : Fin 32)` onto `(lo1, lo2, w11)`. -/
theorem tier1_sum_lo8_lo10_c5_w11 (f : ℕ → ℕ → ℕ → ℕ) :
    (∑ lo8 : Fin 256, ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
      f (lo8.val % 64) (lo10.val % 64) (c5.val + 32 * (lo10.val / 64) + 512 * (lo8.val / 64))) =
      ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048, f lo1.val lo2.val w11.val := by
  rw [show (256 : ℕ) = 4 * 64 from rfl,
    sum_fin_mul (A := 4) (B := 64) (Nat.succ_pos _) (fun l8 ↦ ∑ lo10 : Fin 1024, ∑ c5 : Fin 32,
      f (l8 % 64) (lo10.val % 64) (c5.val + 32 * (lo10.val / 64) + 512 * (l8 / 64)))]
  trans ∑ d2 : Fin 4, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ b4 : Fin 16, ∑ c5 : Fin 32,
    f lo1.val lo2.val ((d2.val * 16 + b4.val) * 32 + c5.val)
  · refine Finset.sum_congr rfl fun d2 _ ↦ Finset.sum_congr rfl fun lo1 _ ↦ ?_
    rw [show (1024 : ℕ) = 16 * 64 from rfl,
      sum_fin_mul (A := 16) (B := 64) (Nat.succ_pos _) (fun l10 ↦ ∑ c5 : Fin 32,
        f ((d2.val * 64 + lo1.val) % 64) (l10 % 64)
          (c5.val + 32 * (l10 / 64) + 512 * ((d2.val * 64 + lo1.val) / 64))),
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun lo2 _ ↦ Finset.sum_congr rfl fun b4 _ ↦
      Finset.sum_congr rfl fun c5 _ ↦ ?_
    have := (⟨lo1.isLt, lo2.isLt⟩ : _ ∧ _)
    rw [show (d2.val * 64 + lo1.val) % 64 = lo1.val by omega,
      show (b4.val * 64 + lo2.val) % 64 = lo2.val by omega]
    exact congrArg (f lo1.val lo2.val) (by omega)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun lo1 _ ↦
      Finset.sum_comm.trans (Finset.sum_congr rfl fun lo2 _ ↦ ?_)
    rw [← sum_fin_mul (A := 4) (B := 16) (Nat.succ_pos _)
          (fun k ↦ ∑ c5 : Fin 32, f lo1.val lo2.val (k * 32 + c5.val)),
        ← sum_fin_mul (A := 64) (B := 32) (Nat.succ_pos _) (f lo1.val lo2.val)]
theorem tier1_cond_kin_or_idle (c : Bool) {p q : ZeroNEremSector × ℕ}
    (hp : p.1 = .idle ∨ ∃ i ax, p.1 = .kin i ax)
    (hq : q.1 = .idle ∨ ∃ i ax, q.1 = .kin i ax) :
    (cond c p q).1 = .idle ∨ ∃ i ax, (cond c p q).1 = .kin i ax := by
  cases c <;> assumption

/-- Kinetic fallback `.kin (47 + u1) h1` on interior cells. -/
def tier1FbKin (u1 h1 : ℕ) : ZeroNEremSector :=
  .kin (mkFin234 (47 + u1)) (mkFin3 h1)
/-- `.ee` candidate tag on `(u1, h1, h2, lo1, lo2)`. -/
def tier1EeTag (u1 h1 h2 lo1 lo2 : ℕ) : ZeroNEremSector :=
  let d1 := decodeUltraNuc192 (64 * h1 + lo1)
  let d2 := decodeUltraNuc192 (64 * h2 + lo2)
  let z2 := b11Z2OfHX h2 lo2
  cond (d1.1 && d2.1 && Bool.not (Nat.beq u1 z2))
    (let cE := Nat.blt z2 u1
     .ee d1.2 (mkFin187 (cond cE z2 u1)) (mkFin187 (cond cE u1 z2)))
    (tier1FbKin u1 h1)
/-- `.nn` candidate tag on `(u1, h1, h2, lo1, lo2)`. -/
def tier1NnTag (u1 h1 h2 lo1 lo2 : ℕ) : ZeroNEremSector :=
  let d1 := decodeUltraNuc192 (64 * h1 + lo1)
  let d2 := decodeUltraNuc192 (64 * h2 + lo2)
  let cN := Nat.blt d2.2.val d1.2.val
  cond (d1.1 && d2.1 && Bool.not (Nat.beq d1.2.val d2.2.val))
    (.nn (cond cN d2.2 d1.2) (cond cN d1.2 d2.2) (mkFin187 u1))
    (tier1FbKin u1 h1)
/-- `.en` candidate tag on `(u1, h1, lo1)`. -/
def tier1EnTag (u1 h1 lo1 : ℕ) : ZeroNEremSector :=
  let d1 := decodeUltraNuc192 (64 * h1 + lo1)
  cond d1.1 (.en d1.2 (mkFin187 u1)) (tier1FbKin u1 h1)
theorem tier1_nat_beq_eq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr fun hb ↦ h (Nat.beq_eq.mp hb)
theorem sum_fin_blt {α : Type*} (M K : ℕ) (a b : α) (f : α → ℕ) :
    (∑ x : Fin M, f (cond (Nat.blt x.val K) a b)) =
      min M K * f a + (M - min M K) * f b := by
  induction M with
  | zero => simp
  | succ m ih =>
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, ih]
      cases hb : Nat.blt m K
      · have hge := (blt_eq_false_iff m K).mp hb
        rw [Bool.cond_false, Nat.min_eq_right hge, Nat.min_eq_right (by omega),
            show m + 1 - K = m - K + 1 by omega]
        ring
      · have := Nat.blt_eq.mp hb
        rw [Bool.cond_true, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega),
          Nat.sub_self, Nat.sub_self]
        ring
theorem tier1_sum_fin_blt_min (M K : ℕ) :
    (∑ x : Fin M, cond (Nat.blt x.val K) 1 0) = min M K := by
  simpa using sum_fin_blt M K (1 : ℕ) 0 id
theorem tier1_sum_fin_blt_val (M K : ℕ) (a b : ZeroNEremSector) (f : ZeroNEremSector → ℕ) :
    (∑ x : Fin M, f (cond (Nat.blt x.val K) a b)) = min M K * f a + (M - min M K) * f b :=
  sum_fin_blt M K a b f
theorem tier1_sum_lo1_lo2_w11_v23 (g : ℕ → ℕ) :
    (∑ lo1 : Fin 64, ∑ lo2 : Fin 64, ∑ w11 : Fin 2048, g (cart254V23 lo1.val lo2.val w11.val)) =
      ∑ v23 : Fin 8388608, g v23.val := by
  conv_rhs =>
    rw [show (8388608 : ℕ) = 131072 * 64 from rfl,
        sum_fin_mul (A := 131072) (B := 64) (Nat.succ_pos _) g, Finset.sum_comm]
  refine Finset.sum_congr rfl fun lo1 _ ↦ ?_
  rw [Finset.sum_comm, show (131072 : ℕ) = 2048 * 64 from rfl,
      sum_fin_mul (A := 2048) (B := 64) (Nat.succ_pos _) (fun v17 ↦ g (v17 * 64 + lo1.val))]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  unfold cart254V23
  exact congrArg g (by omega)
theorem tier1_sum_h1_h2_lo1_lo2 (G : ℕ → ℕ → ℕ) :
    (∑ h1 : Fin 3, ∑ h2 : Fin 3, ∑ lo1 : Fin 64, ∑ lo2 : Fin 64,
      G (64 * h1.val + lo1.val) (64 * h2.val + lo2.val)) =
      foldSum 192 fun z1 ↦ foldSum 192 fun z2 ↦ G z1 z2 := by
  have h192 (f : ℕ → ℕ) :
      (∑ h : Fin 3, ∑ lo : Fin 64, f (64 * h.val + lo.val)) = foldSum 192 f := by
    rw [← sum_fin_eq_foldSum 192 f, show (192 : ℕ) = 3 * 64 from rfl,
        sum_fin_mul (A := 3) (B := 64) (Nat.succ_pos _) f]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ congrArg f (by omega)
  rw [← h192 (fun z1 ↦ foldSum 192 fun z2 ↦ G z1 z2)]
  refine Finset.sum_congr rfl fun h1 _ ↦ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun lo1 _ ↦ h192 (fun z2 ↦ G (64 * h1.val + lo1.val) z2)
theorem tier1_mul_cond_eqSec (n : ℕ) (a s : ZeroNEremSector) :
    n * cond (eqSec a s) 1 0 = cond (eqSec a s) n 0 := by cases eqSec a s <;> simp
theorem tier1EeTag_eq_eeCell {u1 h1 h2 lo1 lo2 : ℕ} (_hh1 : h1 < 3) (hh2 : h2 < 3)
    (hlo1 : lo1 < 64) (hlo2 : lo2 < 64) (s : ZeroNEremSector) :
    let z1 := 64 * h1 + lo1
    let z2' := b11Ext192 (64 * h2 + lo2)
    167085 * cond (eqSec (tier1EeTag u1 h1 h2 lo1 lo2) s) 1 0 +
      4947 * cond (eqSec (tier1FbKin u1 h1) s) 1 0 =
    cond (eqSec (eeCellFermat u1 z1 z2').1 s) (eeCellFermat u1 z1 z2').2 0 +
      cond (eqSec (.kin (mkFin234 (47 + u1)) (mkFin3 (z1 / 64))) s)
        (172032 - (eeCellFermat u1 z1 z2').2) 0 := by
  obtain ⟨_, _, hbVal, hbEq⟩ := b11Ext192_spec (show 64 * h2 + lo2 < 192 by omega)
  dsimp only [tier1EeTag, eeCellFermat, tier1FbKin, qEEFermatCoin]
  rw [show (64 * h1 + lo1) / 64 = h1 by omega, hbVal]
  have hFb (x : ℕ) : 167085 * cond (eqSec (.kin (mkFin234 (47 + x)) (mkFin3 h1)) s) 1 0 +
      4947 * cond (eqSec (.kin (mkFin234 (47 + x)) (mkFin3 h1)) s) 1 0 =
      0 + cond (eqSec (.kin (mkFin234 (47 + x)) (mkFin3 h1)) s) (172032 - 0) 0 := by
    cases eqSec (.kin (mkFin234 (47 + x)) (mkFin3 h1)) s <;> rfl
  cases hd1 : (decodeUltraNuc192 (64 * h1 + lo1)).1
  · simpa using hFb u1
  · cases hd2 : (decodeUltraNuc192 (64 * h2 + lo2)).1
    · simpa using hFb u1
    · rw [hbEq hd2, show (64 * h2 + lo2) / 64 = h2 by omega,
        show (64 * h2 + lo2) % 64 = lo2 by omega]
      if heq : u1 = b11Z2OfHX h2 lo2 then
        simpa [heq, Nat.beq_eq.mpr rfl] using hFb (b11Z2OfHX h2 lo2)
      else
        rw [tier1_nat_beq_eq_false_of_ne heq, beq_eq_false_iff_ne.mpr (Ne.symm heq)]
        simp only [show (false == false) = true from rfl,
          Bool.true_and, Bool.not_false, Bool.cond_true]
        rcases hc : Nat.blt (b11Z2OfHX h2 lo2) u1
        · have hge := (blt_eq_false_iff _ _).mp hc
          simp only [Bool.cond_false, Nat.min_eq_left hge, Nat.max_eq_right hge,
            tier1_mul_cond_eqSec, show 172032 - 167085 = 4947 from rfl]
        · have hlt := (Nat.blt_eq.mp hc).le
          simp only [Bool.cond_true, Nat.min_eq_right hlt, Nat.max_eq_left hlt,
            tier1_mul_cond_eqSec, show 172032 - 167085 = 4947 from rfl]
theorem tier1_xor_bit {a b : ℕ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    Nat.xor a b = cond (Nat.beq a b) 0 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl
theorem tier1_cond_snd_le {c : Bool} {p q : ZeroNEremSector × ℕ}
    (hp : p.2 ≤ 32768) (hq : q.2 ≤ 32768) : (cond c p q).2 ≤ 32768 := by
  cases c <;> assumption
theorem tier1_cond_idle_zero {c : Bool} {p q : ZeroNEremSector × ℕ}
    (hp : cond (eqSec p.1 .idle) p.2 0 = 0) (hq : cond (eqSec q.1 .idle) q.2 0 = 0) :
    cond (eqSec (cond c p q).1 .idle) (cond c p q).2 0 = 0 := by
  cases c <;> assumption
def tier1IsNucOrIdle : ZeroNEremSector → Bool
  | .idle => true
  | .kin p _ => Nat.blt p.val 47
  | _ => false
theorem tier1_sum_fin_blt_eqSec (M K : ℕ) (a b s : ZeroNEremSector) :
    (∑ x : Fin M, cond (eqSec (cond (Nat.blt x.val K) a b) s) 1 0) =
      min M K * cond (eqSec a s) 1 0 + (M - min M K) * cond (eqSec b s) 1 0 :=
  tier1_sum_fin_blt_val M K a b (fun sec ↦ cond (eqSec sec s) 1 0)
theorem tier1_cond_shift {c : Bool} {px p0 qx q0 : ZeroNEremSector × ℕ}
    {ax0 ax : Fin 3} {i : Particle_frozen}
    (hp : cond (eqSec px.1 (.kin i ax)) px.2 0 =
      cond (ax0.val == ax.val) (cond (eqSec p0.1 (.kin i 0)) p0.2 0) 0)
    (hq : cond (eqSec qx.1 (.kin i ax)) qx.2 0 =
      cond (ax0.val == ax.val) (cond (eqSec q0.1 (.kin i 0)) q0.2 0) 0) :
    cond (eqSec (cond c px qx).1 (.kin i ax)) (cond c px qx).2 0 =
      cond (ax0.val == ax.val) (cond (eqSec (cond c p0 q0).1 (.kin i 0)) (cond c p0 q0).2 0) 0 := by
  cases c <;> assumption

theorem tier1FbKin_eq_ax {u0 : ℕ} {i : Particle_frozen} (ax : Fin 3)
    (hpi : mkFin234 (47 + u0) = i) {m : ℕ} (hm : m < 3) :
    cond (eqSec (tier1FbKin u0 m) (.kin i ax)) 1 0 = cond (⟨m, hm⟩ == ax) 1 0 := by
  dsimp only [tier1FbKin, eqSec]
  rw [hpi, beq_self_eq_true, Bool.true_and,
      show mkFin3 m = ⟨m, hm⟩ from Fin.ext (Nat.mod_eq_of_lt hm)]

theorem tier1_sum2_add4 (A B C D : Fin 3 → Fin 3 → ℕ) :
    (∑ h1 : Fin 3, ∑ h2 : Fin 3, (A h1 h2 + B h1 h2 + C h1 h2 + D h1 h2)) =
      (∑ h1 : Fin 3, ∑ h2 : Fin 3, A h1 h2) + (∑ h1 : Fin 3, ∑ h2 : Fin 3, B h1 h2) +
      (∑ h1 : Fin 3, ∑ h2 : Fin 3, C h1 h2) + (∑ h1 : Fin 3, ∑ h2 : Fin 3, D h1 h2) := by
  simp only [Finset.sum_add_distrib]
end QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708
end

noncomputable section
set_option maxRecDepth 4096
namespace QuantumComputation.Specs.PhotochemistrySolution.XagParityEngine
open PrimitiveGate PhotochemistrySolution.CoinWrap PhotochemistrySolution.FermatInverse
/-- Monomorphic pair equality check (`0` typeclass synthesis). -/
def beqPair (p q : ℕ × ℕ) : Bool := Bool.and (Nat.beq p.1 q.1) (Nat.beq p.2 q.2)
theorem beqPair_imp {p q : ℕ × ℕ} (h : beqPair p q = true) : p = q := by
  rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
  exact Prod.ext (Nat.beq_eq.mp h1) (Nat.beq_eq.mp h2)
/-- Topological fanin well-formedness check for an `N`-gate XAG table `gatesAt`. -/
def gatesWfCheck (N : ℕ) (gatesAt : ℕ → ℕ × ℕ) : Bool :=
  allTree 10 0 N fun k ↦
    Bool.and (Nat.blt (gatesAt k).1 (1 <<< (42 + k))) (Nat.blt (gatesAt k).2 (1 <<< (42 + k)))
theorem oddBits_eq_wBit_gen {N : ℕ} (hN : N ≤ 334) {gates : Fin N → ℕ × ℕ}
    (c : Fin (2 ^ 41)) (msk : ℕ) :
    oddBits (xagEnv c.val N gates N le_rfl &&& msk) (42 + N) =
      wBit (xagEnv c.val N gates N le_rfl) msk := by
  conv_rhs =>
    rw [wBit, show (376 : ℕ) = (42 + N) + (334 - N) by omega,
        oddBits_trim_above (m := 42 + N) (fun i hi ↦ by
          rw [Nat.testBit_and, xagEnv_testBit_above (gates := gates) c.isLt N le_rfl hi,
              Bool.false_and])]
theorem wBit_const1_gen {N : ℕ} (_hN : N ≤ 334) {gates : Fin N → ℕ × ℕ} (c : Fin (2 ^ 41)) :
    wBit (xagEnv c.val N gates N le_rfl) 1 = true := by
  rw [show (1 : ℕ) = 1 <<< 0 from rfl, wBit_unit _ 0 (by omega),
      ← xagEnv_congr_step (Nat.zero_add N) (by omega) le_rfl]
  exact (xagEnv_mono_below (gates := gates) (k := 0) (by omega) N (by omega)).trans
    (xagEnv_zero_testBit c.val c.isLt).1
theorem wBit_coin_gen {N : ℕ} (_hN : N ≤ 334) {gates : Fin N → ℕ × ℕ} (c : Fin (2 ^ 41))
    {i : ℕ} (hi : i < 41) :
    wBit (xagEnv c.val N gates N le_rfl) (1 <<< (1 + i)) = c.val.testBit i := by
  rw [wBit_unit _ (1 + i) (by omega), ← xagEnv_congr_step (Nat.zero_add N) (by omega) le_rfl]
  exact (xagEnv_mono_below (gates := gates) (k := 0) (by omega) N (by omega)).trans
    ((xagEnv_zero_testBit c.val c.isLt).2.1 i hi)
theorem wBit_xagEnvGen_gate {N : ℕ} (hN : N ≤ 334) {gatesAt : ℕ → ℕ × ℕ}
    (hWf : gatesWfCheck N gatesAt = true) (c : Fin (2 ^ 41)) {k : ℕ} (hk : k < N) :
    let e := xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl
    wBit e (1 <<< (42 + k)) = Bool.and (wBit e (gatesAt k).1) (wBit e (gatesAt k).2) := by
  intro e
  rcases Bool.and_eq_true_iff.mp (allTree_zero hWf hk) with ⟨hA0, hB0⟩
  rw [Nat.shiftLeft_eq, one_mul] at hA0 hB0
  have hM := xagEnv_mono_below (c := c.val) (N := N) (gates := fun j ↦ gatesAt j.val)
    (k := k + 1) (b := 42 + k) (by omega) (N - 1 - k) (by omega)
  rw [xagEnv_congr_step (show (k + 1) + (N - 1 - k) = N by omega) _ le_rfl] at hM
  rw [wBit_unit e (42 + k) (by omega), hM]
  dsimp only [xagEnv]
  set ek := xagEnv c.val N (fun j ↦ gatesAt j.val) k hk.le
  have hTrim {m : ℕ} (hmLt : m < 2 ^ (42 + k)) : wBit e m = oddBits (ek &&& m) (42 + k) := by
    rw [wBit, show (376 : ℕ) = (42 + k) + (334 - k) by omega, oddBits_trim_above fun i hi ↦ by
      simp [Nat.testBit_and, Nat.testBit_lt_two_pow
        (hmLt.trans_le (Nat.pow_le_pow_right (by omega) hi))]]
    refine oddBits_congr_lt (42 + k) fun i hi ↦ ?_
    have hm := xagEnv_mono_below (c := c.val) (N := N) (gates := fun j ↦ gatesAt j.val)
      (k := k) (b := i) hi (N - k) (by omega)
    rw [xagEnv_congr_step (show k + (N - k) = N by omega) _ le_rfl] at hm
    rw [Nat.testBit_and, Nat.testBit_and, hm]
  rw [hTrim (Nat.blt_eq.mp hA0), hTrim (Nat.blt_eq.mp hB0)]
  exact ite_or_unit_testBit ek (42 + k) _
    (xagEnv_testBit_above (gates := fun j ↦ gatesAt j.val) c.isLt k hk.le le_rfl)
end QuantumComputation.Specs.PhotochemistrySolution.XagParityEngine
end

noncomputable section
set_option maxRecDepth 16384
namespace QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708
open PhotochemistrySolution.CoinWrap
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (WTree getWTree
    getWTree_empty getWTree_setWTree setWTree forceNat forceNat_eq varTable varTable_spec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (xorWTree testBit_xorWTree
    wBit wBit_zero wPack wPack_lt_pow testBit_wPack bitAt bitAt_eq_testBit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FermatInverse (b2_mod_two_mul nat_add_eq
    nat_sub_eq nat_land_eq nat_shr_eq nat_shl_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XagParityEngine (gatesWfCheck
    wBit_const1_gen wBit_xagEnvGen_gate)
/-- Total AND gate count `232` of the `Tier1` `K = 3,708` forward XAG (`928 T`). -/
abbrev nGatesTier1K3708 : ℕ := 232
/-- Packed `15`-bit bit-offsets (`22` per odd-tagged word) for the `232` Tier1 gates. -/
def tier1GateOffs : List ℕ := [
  0x45c08580fd01c6036c06080af01430240040407300cf01680264041006c00b4012001d002c00340001,
  0x9c412cc24e048108bc1110211040007bc0f101d7038c06e40d641a4032f062c0bf416602ab04ec0929,
  0x106420303f507d10f781e9c3bd07490e301bfc36d06b60d2c19f831f06060bcc17082c905630a681425,
  0x1bbc35d86910cc618f4314860d0bd617142cbc5640a991454278c4bc09411224238046308ac10fc2131,
  0x26704b949511267245847c48e511a8230c45a08a7112021ec42b0833103920103e3c7870eb91cc8386d,
  0x2e345b80b5916882cb458d4b0615e32b745664abc155b2a745458a7d14de292c5108a0513ca273c4d8d,
  0x3a4872fce2d1c0237b46e48d9d1ae2352468e8cf519bb32e064b4c69188730b060b4bf917bc2f145d61,
  0x466c8bad148224943d4862d0a020fd4184823102b20243fec7ea0fb91f443dd47ad4f281e0b3b5c75e5,
  0x55ccaa4153129f05324a52147528ad50a89f9d3d327314da09a1d31f25da4b04947925b246647fc8e29,
  0x644cc7458c4312b619cc249829300a5f44bd297712ea65cc4b7fd6d02d5159e4b23d6282bf9573cacf1,
  0x1b5336486ba4d561a6f3464681cce619a933116598c9ed]
/-- Packed `336`-bit sparse-byte payload words (odd-tagged) for the `232` Tier1 gates. -/
def tier1GateStream : List ℕ := [
  0x1a00603000c0600208312a08038c0408803090402104200a2090042011002200505000a202800388a00a3,
  0x60007086c000e878018001c254a803240600070810108580180c00c07400603000c000f0010122030041,
  0x139b000a4803f2039b000a49f00900050003700282e003f2020b010141f003630082e1f03f04c04141201,
  0xc0e0e87e1469e0d05c1f1003f0403c2e17b0383a1f011000b004002e21100440420e01100035892e1b01,
  0x40020309208001100083408100500020d400203b08600c0507e006007e0bc0040c3f0403e1384000b85f,
  0x540046080c200302c02010080040080a046003280386c0201008001530081b418a03058080204004201,
  0x598000b03000090407001f0c0140b6700534008608e10009821c40046086a0b020d400700e0a25000983,
  0x1d081004236c040301fb50200440c0d00c1400ad408011021240410003c14100600078082c000252c0007,
  0x127b00200d00b00400d003630002601f0020b00401d1442ea3e02a4809b70200440b1d2c8e412920100ed,
  0x30024100004039b0002411f01a039b000240023f21403630002611f004020b00411d0090000230500219,
  0x1008847e0130b0000585800c840000d860002a007e083c121000c41b9002032a2e01b200041a03202601,
  0x8810018100080400410002040016900a004081e011808a13d00a0415024f04619e8d2014008303c0d5d,
  0xec0e1c022c2003302a0008b082c080c030008240008082800808b08208c0a0280098012004200501001,
  0x4b3021a4001600380034d00200c03383cc206000b0818000cc0006d00058400600250000620008b08043,
  0x81008b05408d0110080720ffef05404001a680100640ee0e348002c00500069a00401f00b83d02058401,
  0xbe08080720f7cf02205102b08a811a02200801f7d61dc0022c201883981c0600301600800b83503b009,
  0x6c0008b00da0088080620fedf30018001b18001300471f46100000600301600800b8350bb01d808b069,
  0x1d8098022c0b0040201883ecde40820470013d8098022c0b0040200881d9bc8104080416008021c750f71,
  0x1c4082057000140300020d0000408204020b0040100271d607e18000046003000363000260080371f6033,
  0x4880034d0020116e0c024602239b000a482810021dfe4880022c20826c0b034d00503b001020800fea1,
  0x173ab005a4802036ffb034d00503b001020820feac04881610005660403c71a239b000a481404021dfe5,
  0x409a406c003c71a239b000a481404038eff02800000c0000048c04473600149050201dfcc0488040631,
  0x4dfb6110003c71a239b000a4815038efd83a50802800342c000f1c688e6c00292050080a3bfc82a060a1,
  0x4001e3a591c8252402081f6f0c4001182000f19ec008e6c002920506ffff808800482c20167c05490141,
  0x158100004083a508028183429a400008082a060a0040609a67100208003c71a239b000a48141003beff11,
  0x3820200802020680208003c74b23904a4804119f6f014000002c180000110009058402cf80a92028dfb,
  0x400c04102100000b01008041240030000820020004000400800103a434100038200c000800c23a434101,
  0x80128221058080a040407f80700002004205c2f60707420101fe00c00008010808040609210000401,
  0x848420200070d828f880ac5f089c1c0513000e03fd04800001100000084422c2ae0b07408201fe0241,
  0x1008080609570000298422f844e0e02820201fe280801c030603041080000410009042101000386c140a1,
  0x1014181c07f809218000002a7001d000701c06180579800011c2202e17b0383a040807f80321800003825,
  0x88040001000000834100915235c0482e48003807fa0659800001064030141806080419000404420b01,
  0x880000034000001422000080500000100000200c06000008000009810000100c0030000a81000008001,
  0x18048c00020ee060000046004300008708003800010104800020a81c000101004060000a1d8900005,
  0x858e407000000900000017f202051740008063180000012e0260000803018000025a05400b0000b31001,
  0x68800800e0a29098051c00024ce0203400003f69008151d0002008e402000f40002175280818803d0003,
  0x4045840003020091c0008b0800cc06050106900001000c15003f0403400f0c040000047006000000d35,
  0xd3d801010980ed8124701611a3b0011300da0248e02c236601804000a000012380b08d18060006030001,
  0x11601b180013010800df86a022c2100181014045816008042003360e91c000d346884c07040d238001a69,
  0xc0a0212384701611bb8060012384701611a80b80603e1000000041600800400074ba008b084006040401,
  0xc0c0e12083847611bf0060012083847611a02f006040608163380022c21f00c0808163380022c2100f01,
  0x1e10060bc721611bf8060010060bc721611a08f806041e0a083820022c21e80c080a083820022c2004e81,
  0x180600120633c711611a08f80602fe0940000008044000027e0216338101f80000021633810010f800043,
  0x1a68d10102e038280ff82838ce05c008b087f01810141c6702e004584020f80c0bfe120633c711611bf,
  0x100a000103ff828608008b08790181014304004584080c80c0a07fe18384740034d1a21dc07040c1c23a1,
  0xb19c0b8401e00010fff84878cf19c5846ff00c00243c678ce2c23480f806041ffe39319400001c981,
  0xa00980010200383fff828382e054008b087f01810141c1702a004584200f80c0c7ffe16338171bc01,
  0x80c0002201402021000a800800100203fffe124711611be601800491c458468fc00109806e1ffff41841,
  0x7fffe31c20000100080000084028408205025c001e400a1020810080d70020818340d07000004cb01,
  0x70c10010003210300000806034041c000047fffe1825c60000101c408000040590103000004061541801,
  0xe0203da0000082380b08d09806000680180583000000680c6414007030400e008204000003ffff399051,
  0x5a0605070dc0480116100b40c081007fffe104701611bf300c0020101c17000458423c030201ffff8187,
  0x43c00fc100e7e03e1280180000025003000000420201c208e0102c2023f01800f500386e020008b0800f,
  0x77901503050170037fa8030000000c08000001e200078e3447360014902800c77e3b5004038411c02459,
  0x1fac0024000002024d800e03c536239b000a483403c801dfa024d400e022c2003c800c0a02f1004880039,
  0xc0a1cc1034d00503b00102004814000fee0300000000a4d400ef10003c67b00239b000a481483c831f,
  0x71a239b000a481410810037dfec0024000002044d800fc01b73ab005a483fc800df84d400e022c2002c9,
  0x800db84d400e022c2002c800c0ade4d400e02442e239b000a480811c801dfc03000000026f100488003d,
  0x2c200403e40060701400000000dc1220008b0801206000d81d80044000002484d800f432f23904a4823d,
  0x141483e41beff6001100000080911040dceac0169200e0001bf09a801c04584004c800c0a02b04d800e03,
  0x701161001320030280b010540c140080a800134c0500000000d9a4d400ef100488003c536239b000a483,
  0x2013500381182000d3400806c0d901dc1d80044000002024d800e03856673a01a482402e400edd26a01,
  0x84000002028002c08180706003d000268935003808b08008c800c0b80c1074a100501200068501400001,
  0x8c800c0a058002c0044002416100b3e02a480bd0037ed0090000000c002c0044161000b02d003181b001,
  0x16f0090000000174003800000130040000000680024d800e02422cb3e02a4821f20076e135003808b0801,
  0x84000002a3874b90706005000036a135003808b08008c800c0a2780208003c74b23904a4804118001f,
  0xc006000000039ec04d020116058020100c410001fcdefb80024d400e046080034d00201a03f203b83b1,
  0x40007fb783500241008600180106a0010c000002040ec076022c1a02f820201c810001df3c0a00000001,
  0x11028815845408d01100400c6007beb0280000000030002180000040e72893408069a0016008040111,
  0x1ccb9268102c0100100c600f86b0180010c0000024c0d407b201a02f821180067201a800430000008100d,
  0x424028c0030020d40020c000003700300073d041e20022c0b00402018831803f9bc0a00000003200c001,
  0x300073ca01300022c0b00402018838c01fcde0480000000030120800c0060000300020c0000029403001,
  0xc0b00402018838001fcde0300020c00000206480e4026201502340440038c0033d20d400c00000002901,
  0x30002050c0030000d40020c00000204800000000e400300180b0040040c00e0d40588073d041a04023,
  0x1000000c00100c01800c000d8c000980200b1800e3ec0880000000800e4040810c00600003000c0000009,
  0x2c000c000c8200361801c00806000c000000038003000300036300026003860018f906a00103,
  0x1000000e00350064100da008800a180063641a80040c00000209000d40408204020b004011860038ea023,
  0x188106a0030000003300c010208100c1800e0040804800000024100040d4003408005c600700201800103,
  0x3069f500386e024008b080080cb40c0a3a800d406018c300100100c00080c00000207001a04020380001,
  0x8b0800cb40c087d400e1b8090022c20032d0302254281170006000187d400f088090022c052402032d1,
  0x1033d03029f500386e024008b080080cb40c0a187d400e731e8090022c023403033d03069f500386e0241,
  0x187d400ed40d8090022c026403033d03069f500386e024008b0800cb40c08207d400e720d8090022d3003,
  0x100386e024008b0800cb40c08087d400e40148090022c033b033d03061f500386e024008b0800cb40c085,
  0xae1f5003c22024008b4900e065a06053ea0070dc04801161000cb40c0890a713000455001c00061f5]
/-- Read payload `w[i] >>> 1` from an odd-tagged word list. -/
def tier1WordAt : ℕ → List ℕ → ℕ
  | _, [] => 0
  | 0, w :: _ => Nat.shiftRight w 1
  | i + 1, _ :: ws => tier1WordAt i ws
/-- Read consecutive `336`-bit payload words `(w[i] >>> 1, w[i+1] >>> 1)`. -/
def tier1StreamPair : ℕ → List ℕ → ℕ × ℕ
  | _, [] => (0, 0)
  | 0, w0 :: ws =>
      (Nat.shiftRight w0 1, match ws with | [] => 0 | w1 :: _ => Nat.shiftRight w1 1)
  | i + 1, _ :: ws => tier1StreamPair i ws
/-- Unpack `nb` sparse bytes selected by `bm` from `bs` starting at bit shift `sh`. -/
def tier1UnpackBytes : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, _, bs => (0, bs)
  | n + 1, sh, bm, bs =>
      match Nat.beq (Nat.land bm 1) 1 with
      | false => tier1UnpackBytes n (Nat.add sh 8) (Nat.shiftRight bm 1) bs
      | true =>
          let b := Nat.land bs 255
          match tier1UnpackBytes n (Nat.add sh 8) (Nat.shiftRight bm 1)
            (Nat.shiftRight bs 8) with
          | (acc, bs') => (Nat.lor (Nat.shiftLeft b sh) acc, bs')
/-- Total `Nat`-indexed lookup across all `232` `Tier1` `K = 3,708` forward XAG gates. -/
def gatesTier1K3708At (k : ℕ) : ℕ × ℕ := match Nat.blt k 232 with
  | false => (0, 0)
  | true =>
      let ow := tier1WordAt (Nat.div k 22) tier1GateOffs
      let off := Nat.land (Nat.shiftRight ow (Nat.mul 15 (Nat.mod k 22))) 32767
      let rem := Nat.mod off 336
      let nb := Nat.div (Nat.add 49 k) 8
      match tier1StreamPair (Nat.div off 336) tier1GateStream with
      | (loW, hiW) =>
          let blob := Nat.lor (Nat.shiftRight loW rem) (Nat.shiftLeft hiW (Nat.sub 336 rem))
          match tier1UnpackBytes nb 0 blob (Nat.shiftRight blob nb) with
          | (u, bs1) => (u, (tier1UnpackBytes nb 0 bs1 (Nat.shiftRight bs1 nb)).1)
/-- `232`-AND forward XAG gate array. -/
def gatesTier1K3708 (k : Fin nGatesTier1K3708) : ℕ × ℕ := gatesTier1K3708At k.val
/-- All `232` forward gates depend strictly on prefix bits `< 42 + k`. -/
theorem gatesTier1K3708_wf : gatesWfCheck nGatesTier1K3708 gatesTier1K3708At = true := rfl

/-- Pack `r`-th bit of each word in `outs` LSB-first using GMP kernel primitives. -/
def packRowAtT1 (r : ℕ) : List ℕ → ℕ
  | [] => 0
  | ov :: os => Nat.add (cond (bitAt ov r) 1 0) (Nat.mul 2 (packRowAtT1 r os))
theorem packRowAtT1_cons (r ov : ℕ) (os : List ℕ) :
    packRowAtT1 r (ov :: os) = cond (bitAt ov r) 1 0 + 2 * packRowAtT1 r os := rfl
theorem packRowAtT1_append (r : ℕ) :
    ∀ (xs ys : List ℕ),
      packRowAtT1 r (xs ++ ys) = packRowAtT1 r xs + 2 ^ xs.length * packRowAtT1 r ys
  | [], _ => by simp [packRowAtT1]
  | ov :: xs, ys => by
      rw [List.cons_append, packRowAtT1_cons, packRowAtT1_cons, List.length_cons,
          packRowAtT1_append r xs ys]
      ring
/-- Populate `(mTr, vTr)` at indices `i + 1 ..` with input masks `ms` and `varTable m`. -/
def initInTreesT1 (m : ℕ) : ℕ → List ℕ → WTree → WTree → WTree × WTree
  | _, [], mTr, vTr => (mTr, vTr)
  | i, gm :: ms, mTr, vTr =>
      forceNat (varTable m i) fun vt ↦
        initInTreesT1 m (Nat.succ i) ms
          (setWTree 7 (Nat.succ i) gm mTr) (setWTree 7 (Nat.succ i) vt vTr)
theorem getWTree_initInTreesT1 (m : ℕ) : ∀ i (ms : List ℕ) mTr vTr j,
    i + 1 + ms.length ≤ 128 → j < 128 →
    getWTree 7 (initInTreesT1 m i ms mTr vTr).1 j =
      (if i < j ∧ j ≤ i + ms.length then ms.getD (j - (i + 1)) 0 else getWTree 7 mTr j) ∧
    getWTree 7 (initInTreesT1 m i ms mTr vTr).2 j =
      (if i < j ∧ j ≤ i + ms.length then varTable m (j - 1) else getWTree 7 vTr j)
  | i, [], _, _, j, _, _ => by simp [initInTreesT1, show ¬(i < j ∧ j ≤ i) by omega]
  | i, gm :: ms, mTr, vTr, j, hLen, hj => by
      simp only [List.length_cons, initInTreesT1, forceNat_eq] at hLen ⊢
      obtain ⟨s1, s2⟩ := getWTree_initInTreesT1 m (i + 1) ms _ _ j (by omega) hj
      rw [s1, s2]
      if hIn : i + 1 < j ∧ j ≤ i + 1 + ms.length then
        simp [hIn, show i < j ∧ j ≤ i + (ms.length + 1) by omega,
          show j - (i + 1) = (j - (i + 1 + 1)) + 1 by omega, List.getD]
      else
        simp only [hIn, ↓reduceIte, getWTree_setWTree 7 (i + 1) j _ _ (by omega) hj]
        by_cases hEq : j = i + 1 <;>
          simp [hEq, show (i < j ∧ j ≤ i + (ms.length + 1)) ↔ j = i + 1 by omega]
/--
Simultaneously verify global fanin masks in `mTr` and evaluate `2^m` -bit truth tables in `vTr` .
-/
def runGatesT1 (gatesAt : ℕ → ℕ × ℕ) :
    ℕ → ℕ → WTree → WTree → List (ℕ × ℕ) → Option (WTree × WTree)
  | _, _, mTr, vTr, [] => some (mTr, vTr)
  | k, idx, mTr, vTr, (ga, gb) :: gs =>
      let exp := gatesAt k
      match Bool.and (Nat.beq exp.1 (xorWTree 7 mTr ga))
                     (Nat.beq exp.2 (xorWTree 7 mTr gb)) with
      | false => none
      | true =>
          forceNat (Nat.land (xorWTree 7 vTr ga) (xorWTree 7 vTr gb)) fun gv ↦
            runGatesT1 gatesAt (Nat.succ k) (Nat.succ idx)
              (setWTree 7 idx (Nat.shiftLeft 1 (Nat.add 42 k)) mTr)
              (setWTree 7 idx gv vTr) gs
theorem runGatesT1_spec {N : ℕ} (hN : N ≤ 334) {gatesAt : ℕ → ℕ × ℕ}
    (hWf : gatesWfCheck N gatesAt = true) (c : Fin (2 ^ 41)) (row : ℕ) :
    let e := xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl
    ∀ gs k idx mTr vTr mEnd vEnd, runGatesT1 gatesAt k idx mTr vTr gs = some (mEnd, vEnd) →
      idx + gs.length ≤ 128 → k + gs.length ≤ N →
      (∀ j < 128, (getWTree 7 vTr j).testBit row = wBit e (getWTree 7 mTr j)) →
      ∀ j < 128, (getWTree 7 vEnd j).testBit row = wBit e (getWTree 7 mEnd j)
  | [], _, _, _, _, _, _, hRun, _, _, hInv => (Prod.mk.inj (Option.some.inj hRun)).1 ▸
      (Prod.mk.inj (Option.some.inj hRun)).2 ▸ hInv
  | (ga, gb) :: gs, k, idx, mTr, vTr, mEnd, vEnd, hRun, hIdx, hKN, hInv => by
      simp only [List.length_cons] at hIdx hKN
      dsimp only [runGatesT1] at hRun
      cases hChk : Bool.and (Nat.beq (gatesAt k).1 (xorWTree 7 mTr ga))
                            (Nat.beq (gatesAt k).2 (xorWTree 7 mTr gb))
      · simp [hChk] at hRun
      · rw [hChk, forceNat_eq] at hRun
        rcases Bool.and_eq_true_iff.mp hChk with ⟨hEqA, hEqB⟩
        refine runGatesT1_spec hN hWf c row gs (k + 1) (idx + 1) _ _ mEnd vEnd hRun
          (by omega) (by omega) fun j hj ↦ ?_
        rw [getWTree_setWTree 7 idx j _ vTr (by omega) hj,
          getWTree_setWTree 7 idx j _ mTr (by omega) hj]
        if hJEq : j = idx then
          simp only [hJEq, ↓reduceIte, nat_land_eq, nat_add_eq, Nat.testBit_and,
            testBit_xorWTree _ _ 7 _ _ _ hInv, ← Nat.beq_eq.mp hEqA, ← Nat.beq_eq.mp hEqB,
            show Nat.shiftLeft 1 (42 + k) = 1 <<< (42 + k) from rfl]
          exact (wBit_xagEnvGen_gate hN hWf c (by omega)).symm
        else simp [hJEq, hInv j hj]
/-- Verify output masks against `mEnd` and collect output truth tables from `vEnd`. -/
def evalOutsT1 (mEnd vEnd : WTree) : List ℕ → List ℕ → Option (List ℕ)
  | [], [] => some []
  | lo :: ls, go :: gs =>
      match Nat.beq go (xorWTree 7 mEnd lo) with
      | false => none
      | true =>
          forceNat (xorWTree 7 vEnd lo) fun ov ↦
            match evalOutsT1 mEnd vEnd ls gs with
            | none => none
            | some os => some (ov :: os)
  | _, _ => none
theorem evalOutsT1_spec (e row : ℕ) (mEnd vEnd : WTree)
    (hInv : ∀ j < 128, (getWTree 7 vEnd j).testBit row =
    wBit e (getWTree 7 mEnd j)) :
    ∀ ls gs outs, evalOutsT1 mEnd vEnd ls gs = some outs → packRowAtT1 row outs = wPack e gs
  | [], [], _, h => Option.some.inj h ▸ rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | lo :: ls, go :: gs, _, h => by
      dsimp only [evalOutsT1] at h
      cases hEq : Nat.beq go (xorWTree 7 mEnd lo)
      · simp [hEq] at h
      · rw [hEq, forceNat_eq] at h
        rcases hTl : evalOutsT1 mEnd vEnd ls gs with _ | os <;>
          simp only [hTl, reduceCtorEq, Option.some.injEq] at h
        subst h
        rw [packRowAtT1_cons, wPack, bitAt_eq_testBit,
          testBit_xorWTree e row 7 vEnd mEnd lo hInv, ← Nat.beq_eq.mp hEq,
          evalOutsT1_spec e row mEnd vEnd hInv ls gs os hTl]
/-- Shared SIMD `WTree` block runner passing `(tr0, outs)` to `finish`. -/
def checkBlockWithOutsT1 (N : ℕ) (gatesAt : ℕ → ℕ × ℕ) (k0 m : ℕ) (inMasks : List ℕ)
    (lgates : List (ℕ × ℕ)) (louts gouts : List ℕ) (finish : WTree → List ℕ → Bool) : Bool :=
  let endIdx := Nat.add (Nat.succ m) lgates.length
  match Bool.and (Nat.beq inMasks.length m)
          (Bool.and (Nat.ble (Nat.add k0 lgates.length) N)
            (Bool.and (Nat.ble N 334) (Nat.ble endIdx 128))) with
  | false => false
  | true =>
      forceNat (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 m)) 1) fun ones ↦
        match initInTreesT1 m 0 inMasks (setWTree 7 0 1 .empty) (setWTree 7 0 ones .empty) with
        | (mTr0, vTr0) =>
            match runGatesT1 gatesAt k0 (Nat.succ m) mTr0 vTr0 lgates with
            | none => false
            | some (mEnd, vEnd) =>
                match evalOutsT1 mEnd vEnd louts gouts with
                | none => false
                | some outs => finish vTr0 outs
theorem checkBlockWithOutsT1_imp
    {N k0 m : ℕ} {gatesAt : ℕ → ℕ × ℕ} {inMasks : List ℕ} {lgates : List (ℕ × ℕ)}
    {louts gouts : List ℕ} {finish : WTree → List ℕ → Bool}
    (hWf : gatesWfCheck N gatesAt = true)
    (hCert : checkBlockWithOutsT1 N gatesAt k0 m inMasks lgates louts gouts finish = true)
    (c : Fin (2 ^ 41)) :
    let e := xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl
    let row := wPack e inMasks
    ∃ (tr0 : WTree) (outs : List ℕ),
      finish tr0 outs = true ∧ row < 2 ^ m ∧ bitAt (getWTree 7 tr0 0) row = true ∧
      (∀ i < m, bitAt (getWTree 7 tr0 (Nat.succ i)) row = bitAt row i) ∧
      packRowAtT1 row outs = wPack e gouts := by
  intro e row
  dsimp only [checkBlockWithOutsT1] at hCert
  cases hBds : Bool.and (Nat.beq inMasks.length m)
      (Bool.and (Nat.ble (Nat.add k0 lgates.length) N)
        (Bool.and (Nat.ble N 334) (Nat.ble (Nat.add (Nat.succ m) lgates.length) 128)))
  · exact Bool.noConfusion (hBds ▸ hCert)
  rw [hBds, forceNat_eq, nat_shl_one m, nat_shl_one, nat_sub_eq] at hCert
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, nat_add_eq] at hBds
  rcases hBds with ⟨hM, hK, hN, hE⟩
  rcases hInit : initInTreesT1 m 0 inMasks
    (setWTree 7 0 1 .empty) (setWTree 7 0 (2 ^ 2 ^ m - 1) .empty) with ⟨m0, v0⟩
  rcases hRG : runGatesT1 gatesAt k0 (Nat.succ m) m0 v0 lgates with _ | ⟨mE, vE⟩
  · simp [hInit, hRG] at hCert
  rcases hEO : evalOutsT1 mE vE louts gouts with _ | outs
  · simp [hInit, hRG, hEO] at hCert
  simp only [hInit, hRG, hEO] at hCert
  have hr : row < 2 ^ m := hM ▸ wPack_lt_pow e inMasks
  have hG (j) (hj : j < 128) := hInit ▸ getWTree_initInTreesT1 m 0 inMasks _ _ j (by omega) hj
  have h1 : (getWTree 7 v0 0).testBit row = true := by
    simpa [(hG 0 (by omega)).2, getWTree_setWTree 7 0 0 _ .empty (by omega) (by omega),
      Nat.testBit_two_pow_sub_one] using hr
  refine ⟨v0, outs, hCert, hr, by rwa [bitAt_eq_testBit], fun i hi ↦ by
      simpa [bitAt_eq_testBit, (hG (i + 1) (by omega)).2, Nat.add_one_le_iff, hM, hi]
        using (varTable_spec m i hi).2 row hr,
    evalOutsT1_spec e row mE vE (runGatesT1_spec hN hWf c row lgates k0 (m + 1)
      m0 v0 mE vE hRG hE hK fun j hj ↦ ?_) louts gouts outs hEO⟩
  obtain ⟨gm0, gv0⟩ := hG j hj
  rcases eq_or_ne j 0 with rfl | hj0
  · simpa [h1, gm0, getWTree_setWTree 7 0 0 1 .empty (by omega) (by omega)]
      using (wBit_const1_gen hN c).symm
  · if hIn : 0 < j ∧ j ≤ inMasks.length then
      rw [gm0, gv0, ite_eq_left (by omega), ite_eq_left (by omega),
        (varTable_spec m (j - 1) (by omega)).2 row hr, Nat.zero_add, testBit_wPack]
    else
      simp [gm0, gv0, hIn, hj0, getWTree_setWTree 7 0 j _ .empty (by omega) hj,
        getWTree_empty, wBit_zero]
/-- Eagerly split every word in `outs` into low `half` bits and next `half` bits. -/
def splitMaskListT1 (half mask : ℕ) : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | ov :: os =>
      forceNat (Nat.land ov mask) fun lo ↦
        forceNat (Nat.land (Nat.shiftRight ov half) mask) fun hi ↦
          match splitMaskListT1 half mask os with
          | (ls, hs) => (lo :: ls, hi :: hs)
theorem packRowAtT1_splitMaskListT1 {half mask : ℕ} (hM : mask = 2 ^ half - 1) :
    ∀ outs {r}, r < half → packRowAtT1 r (splitMaskListT1 half mask outs).1 =
    packRowAtT1 r outs ∧
      packRowAtT1 r (splitMaskListT1 half mask outs).2 = packRowAtT1 (half + r) outs
  | [], _, _ => ⟨rfl, rfl⟩
  | ov :: os, r, hr => by
      simp only [splitMaskListT1, forceNat_eq]
      rcases hRec : splitMaskListT1 half mask os with ⟨ls, hs⟩
      obtain ⟨ihL, ihR⟩ := hRec ▸ packRowAtT1_splitMaskListT1 hM os hr
      simp [packRowAtT1, ihL, ihR, bitAt_eq_testBit, hM, hr]
/-- Sequential row check across `c` unboxed rows `[base + r, base + r + c)`. -/
def checkSmallPredT1 : ℕ → ℕ → ℕ → List ℕ → (ℕ → ℕ → Bool) → Bool
  | 0, _, _, _, _ => true
  | c + 1, base, r, outs, pred =>
      match pred (Nat.add base r) (packRowAtT1 r outs) with
      | false => false
      | true => checkSmallPredT1 c base (Nat.succ r) outs pred
theorem checkSmallPredT1_imp {base : ℕ} {outs : List ℕ} {pred : ℕ → ℕ → Bool} :
    ∀ (c r : ℕ), checkSmallPredT1 c base r outs pred = true →
      ∀ d < c, pred (base + (r + d)) (packRowAtT1 (r + d) outs) = true
  | 0, _, _, _, hd => nomatch hd
  | c + 1, r, hC, d, hd => by
      dsimp only [checkSmallPredT1] at hC
      cases hP : pred (Nat.add base r) (packRowAtT1 r outs)
      · exact Bool.noConfusion (hP ▸ hC)
      · rw [hP] at hC
        cases d with
        | zero => simpa only [nat_add_eq, Nat.add_zero] using hP
        | succ d =>
            simpa only [show r + 1 + d = r + (d + 1) by omega] using
              checkSmallPredT1_imp c (r + 1) hC d (Nat.lt_of_succ_lt_succ hd)
/-- Check `pred (base + r) (packRowAtT1 r outs)` across `r < 2^m` via `32`-bit unboxed chunks. -/
def checkCubeUnboxedT1 : ℕ → ℕ → List ℕ → (ℕ → ℕ → Bool) → Bool
  | 0, base, outs, pred => pred base (packRowAtT1 0 outs)
  | m + 1, base, outs, pred =>
      match Nat.ble (m + 1) 5 with
      | true => checkSmallPredT1 (Nat.shiftLeft 1 (m + 1)) base 0 outs pred
      | false =>
          let half := Nat.shiftLeft 1 m
          forceNat (Nat.sub (Nat.shiftLeft 1 half) 1) fun mask ↦
            match splitMaskListT1 half mask outs with
            | (outsL, outsR) =>
                match checkCubeUnboxedT1 m base outsL pred with
                | false => false
                | true => checkCubeUnboxedT1 m (Nat.add base half) outsR pred
theorem checkCubeUnboxedT1_imp :
    ∀ (m base : ℕ) (outs : List ℕ) (pred : ℕ → ℕ → Bool),
      checkCubeUnboxedT1 m base outs pred = true →
      ∀ r < 2 ^ m, pred (base + r) (packRowAtT1 r outs) = true
  | 0, base, _, _, hC, r, hr => (show r = 0 by omega) ▸ (Nat.add_zero base).symm ▸ hC
  | m + 1, base, outs, pred, hC, r, hr => by
      dsimp only [checkCubeUnboxedT1] at hC
      cases hBle : Nat.ble (m + 1) 5
      · rw [hBle, forceNat_eq, nat_shl_one m, nat_shl_one (2 ^ m), nat_sub_eq, nat_add_eq] at hC
        rcases hSp : splitMaskListT1 (2 ^ m) (2 ^ 2 ^ m - 1) outs with ⟨outsL, outsR⟩
        rw [hSp] at hC
        cases hL : checkCubeUnboxedT1 m base outsL pred
        · exact Bool.noConfusion (hL ▸ hC)
        · rw [hL] at hC
          if hrL : r < 2 ^ m then
            simpa only [hSp ▸ (packRowAtT1_splitMaskListT1 rfl outs hrL).1] using
              checkCubeUnboxedT1_imp m base outsL pred hL r hrL
          else
            have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
            simpa only [show base + 2 ^ m + (r - 2 ^ m) = base + r by omega,
              hSp ▸ (packRowAtT1_splitMaskListT1 rfl outs (by omega : r - 2 ^ m < 2 ^ m)).2,
              show 2 ^ m + (r - 2 ^ m) = r by omega] using
              checkCubeUnboxedT1_imp m (base + 2 ^ m) outsR pred hC (r - 2 ^ m) (by omega)
      · rw [hBle] at hC
        simpa only [Nat.zero_add] using
          checkSmallPredT1_imp (Nat.shiftLeft 1 (m + 1)) 0 hC r (by rwa [nat_shl_one])
/-- Fast unboxed-chunk full-output block certificate (`0` double `checkCube`). -/
def checkBlockFullFastT1 (N : ℕ) (gatesAt : ℕ → ℕ × ℕ) (k0 m : ℕ) (inMasks : List ℕ)
    (lgates : List (ℕ × ℕ)) (louts gouts : List ℕ) (care : ℕ → Bool) (spec : ℕ → ℕ) : Bool :=
  checkBlockWithOutsT1 N gatesAt k0 m inMasks lgates louts gouts fun _ outs ↦
    checkCubeUnboxedT1 m 0 outs fun row pv ↦
      match care row with
      | false => true
      | true => Nat.beq pv (spec row)
theorem wPack_of_checkBlockFullFastT1
    {N k0 m : ℕ} {gatesAt : ℕ → ℕ × ℕ} {inMasks : List ℕ} {lgates : List (ℕ × ℕ)}
    {louts gouts : List ℕ} {care : ℕ → Bool} {spec : ℕ → ℕ}
    (hWf : gatesWfCheck N gatesAt = true)
    (hCert : checkBlockFullFastT1 N gatesAt k0 m inMasks lgates louts gouts care spec = true)
    (c : Fin (2 ^ 41))
    (hCare : care (wPack (xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl) inMasks) = true) :
    let e := xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl
    wPack e gouts = spec (wPack e inMasks) := by
  intro e
  rcases checkBlockWithOutsT1_imp hWf hCert c with ⟨_, outs, hCube, hRLt, _, _, hOut⟩
  have hRow := checkCubeUnboxedT1_imp m 0 outs _ hCube (wPack e inMasks) hRLt
  change care (wPack e inMasks) = true at hCare
  rw [Nat.zero_add, hOut, hCare] at hRow
  exact Nat.beq_eq.mp hRow
/-- Fast unboxed-chunk masked-output block certificate. -/
def checkBlockMaskFastT1 (N : ℕ) (gatesAt : ℕ → ℕ × ℕ) (k0 m : ℕ) (inMasks : List ℕ)
    (lgates : List (ℕ × ℕ)) (louts gouts : List ℕ) (care : ℕ → Bool) (careMask spec : ℕ → ℕ) :
        Bool :=
  checkBlockWithOutsT1 N gatesAt k0 m inMasks lgates louts gouts fun _ outs ↦
    checkCubeUnboxedT1 m 0 outs fun row pv ↦
      match care row with
      | false => true
      | true =>
          let cm := careMask row
          Nat.beq (Nat.land pv cm) (Nat.land (spec row) cm)
theorem wPack_of_checkBlockMaskFastT1
    {N k0 m : ℕ} {gatesAt : ℕ → ℕ × ℕ} {inMasks : List ℕ} {lgates : List (ℕ × ℕ)}
    {louts gouts : List ℕ} {care : ℕ → Bool} {careMask spec : ℕ → ℕ}
    (hWf : gatesWfCheck N gatesAt = true)
    (hCert :
      checkBlockMaskFastT1 N gatesAt k0 m inMasks lgates louts gouts care careMask spec = true)
    (c : Fin (2 ^ 41))
    (hCare : care (wPack (xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl) inMasks) = true) :
    let e := xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl
    (wPack e gouts) &&& careMask (wPack e inMasks) =
      (spec (wPack e inMasks)) &&& careMask (wPack e inMasks) := by
  intro e
  rcases checkBlockWithOutsT1_imp hWf hCert c with ⟨_, outs, hCube, hRLt, _, _, hOut⟩
  have hRow := checkCubeUnboxedT1_imp m 0 outs _ hCube (wPack e inMasks) hRLt
  change care (wPack e inMasks) = true at hCare
  rw [Nat.zero_add, hOut, hCare] at hRow
  simpa only [nat_land_eq] using Nat.beq_eq.mp hRow

theorem bitAt_div_modT1 (r sh k j : ℕ) (hj : j < k) :
    bitAt r (sh + j) = bitAt ((r / 2 ^ sh) % 2 ^ k) j := by
  simp [bitAt_eq_testBit, Nat.testBit_mod_two_pow, hj, Nat.testBit_div_two_pow, Nat.add_comm]
/-- Bitwise complement of bitplane `a` within `ones`. -/
def notPlaneT1 (ones a : ℕ) : ℕ := Nat.xor ones a
/-- Bitwise AND of bitplanes `a` and `b`. -/
def andPlaneT1 (a b : ℕ) : ℕ := Nat.land a b
/-- Bitwise OR of bitplanes `a` and `b`. -/
def orPlaneT1 (a b : ℕ) : ℕ := Nat.lor a b
/-- Bitwise `2`-to-`1` MUX bitplane `(sel &&& tVal) ||| ((ones ^^^ sel) &&& fVal)`. -/
def muxPlaneT1 (ones sel tVal fVal : ℕ) : ℕ :=
  Nat.lor (Nat.land sel tVal) (Nat.land (Nat.xor ones sel) fVal)
theorem bitAt_notPlaneT1 {ones a r : ℕ} (h1 : bitAt ones r = true) :
    bitAt (notPlaneT1 ones a) r = Bool.not (bitAt a r) := by
  simp [notPlaneT1, bitAt_eq_testBit,
      show ones.testBit r = true by simpa [bitAt_eq_testBit] using h1]
theorem bitAt_andPlaneT1 (a b r : ℕ) :
    bitAt (andPlaneT1 a b) r = Bool.and (bitAt a r) (bitAt b r) := by
  rw [andPlaneT1, bitAt_eq_testBit, bitAt_eq_testBit, bitAt_eq_testBit, nat_land_eq,
      Nat.testBit_and]
theorem bitAt_orPlaneT1 (a b r : ℕ) :
    bitAt (orPlaneT1 a b) r = Bool.or (bitAt a r) (bitAt b r) := by
  simp [orPlaneT1, bitAt_eq_testBit]
theorem bitAt_muxPlaneT1 {ones sel tVal fVal r : ℕ} (h1 : bitAt ones r = true) :
    bitAt (muxPlaneT1 ones sel tVal fVal) r = cond (bitAt sel r) (bitAt tVal r) (bitAt fVal r) := by
  change bitAt (orPlaneT1 (andPlaneT1 sel tVal) (andPlaneT1 (notPlaneT1 ones sel) fVal)) r = _
  rw [bitAt_orPlaneT1, bitAt_andPlaneT1, bitAt_andPlaneT1, bitAt_notPlaneT1 h1]
  cases bitAt sel r <;> cases bitAt tVal r <;> cases bitAt fVal r <;> rfl
/-- Build `k` bitplanes `[f i, f (i + 1), ..., f (i + k - 1)]`. -/
def buildPlanesT1 (f : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, i => f i :: buildPlanesT1 f k (Nat.succ i)
theorem buildPlanesT1_len (f : ℕ → ℕ) : ∀ (k i : ℕ), (buildPlanesT1 f k i).length = k
  | 0, _ => rfl
  | k + 1, i => congrArg (· + 1) (buildPlanesT1_len f k (i + 1))
theorem packRowAtT1_buildPlanesT1 (r : ℕ) (f : ℕ → ℕ) :
    ∀ (k i v : ℕ), (∀ j < k, bitAt (f (i + j)) r = bitAt v j) →
      packRowAtT1 r (buildPlanesT1 f k i) = v % 2 ^ k
  | 0, _, _, _ => by simp [buildPlanesT1, packRowAtT1, pow_zero, Nat.mod_one]
  | k + 1, i, v, hBit => by
      dsimp only [buildPlanesT1]
      rw [packRowAtT1_cons,
        show bitAt (f i) r = bitAt v 0 by simpa using hBit 0 (Nat.zero_lt_succ k),
        packRowAtT1_buildPlanesT1 r f k (i + 1) (v / 2) fun j hj ↦ by
          simpa [show i + 1 + j = i + (j + 1) by omega, bitAt_eq_testBit,
            show v / 2 = v / 2 ^ 1 from rfl, Nat.testBit_div_two_pow] using
            hBit (j + 1) (Nat.succ_lt_succ hj)]
      rw [show cond (bitAt v 0) 1 0 = v % 2 by
            rcases (show v % 2 = 0 ∨ v % 2 = 1 by omega) with h | h <;>
              simp [bitAt_eq_testBit, Nat.testBit_zero, h],
          show 2 ^ (k + 1) = 2 * 2 ^ k by ring]
      exact b2_mod_two_mul v (2 ^ k) (Nat.two_pow_pos k)
/-- Bitplanes for `cond sw ((r / 2^shB) % 2^k) (cond en ((r / 2^shA) % 2^k) 0)`. -/
def muxAPlanesT1 (vt : ℕ → ℕ) (ones sw en shA shB k : ℕ) : List ℕ :=
  buildPlanesT1
    (fun j ↦ muxPlaneT1 ones sw (vt (Nat.add shB j)) (andPlaneT1 en (vt (Nat.add shA j)))) k 0
theorem packRowAtT1_muxAPlanesT1 {m r ones sw en : ℕ} {vt : ℕ → ℕ} (h1 : bitAt ones r = true)
    (hVt : ∀ i < m, bitAt (vt i) r = bitAt r i) (shA shB k : ℕ) (hA : shA + k ≤ m)
    (hB : shB + k ≤ m) : packRowAtT1 r (muxAPlanesT1 vt ones sw en shA shB k) =
      cond (bitAt sw r) ((r / 2 ^ shB) % 2 ^ k) (cond (bitAt en r) ((r / 2 ^ shA) % 2 ^ k) 0) := by
  set v := cond (bitAt sw r) ((r / 2 ^ shB) % 2 ^ k) (cond (bitAt en r) ((r / 2 ^ shA) % 2 ^ k) 0)
  rw [muxAPlanesT1, packRowAtT1_buildPlanesT1 r _ k 0 v fun j hj ↦ by
        rw [Nat.zero_add, bitAt_muxPlaneT1 h1, bitAt_andPlaneT1, nat_add_eq, nat_add_eq,
            hVt (shB + j) (by omega), hVt (shA + j) (by omega),
            bitAt_div_modT1 r shB k j hj, bitAt_div_modT1 r shA k j hj]
        cases hSw : bitAt sw r <;> cases hEn : bitAt en r <;>
          simp [v, hSw, hEn, bitAt_eq_testBit],
      Nat.mod_eq_of_lt (by
        cases hSw : bitAt sw r <;> cases hEn : bitAt en r <;>
          simp [v, hSw, hEn, Nat.mod_lt _ (Nat.two_pow_pos k), Nat.two_pow_pos k])]
/-- Bitplanes for `cond doX (cond sw ((r / 2^shA) % 2^k) ((r / 2^shB) % 2^k)) 0`. -/
def muxBPlanesT1 (vt : ℕ → ℕ) (ones doX sw shA shB k : ℕ) : List ℕ :=
  buildPlanesT1
    (fun j ↦ andPlaneT1 doX (muxPlaneT1 ones sw (vt (Nat.add shA j)) (vt (Nat.add shB j)))) k 0
theorem packRowAtT1_muxBPlanesT1 {m r ones doX sw : ℕ} {vt : ℕ → ℕ} (h1 : bitAt ones r = true)
    (hVt : ∀ i < m, bitAt (vt i) r = bitAt r i) (shA shB k : ℕ) (hA : shA + k ≤ m)
    (hB : shB + k ≤ m) : packRowAtT1 r (muxBPlanesT1 vt ones doX sw shA shB k) =
      cond (bitAt doX r) (cond (bitAt sw r) ((r / 2 ^ shA) % 2 ^ k) ((r / 2 ^ shB) % 2 ^ k)) 0 := by
  set v := cond (bitAt doX r) (cond (bitAt sw r) ((r / 2 ^ shA) % 2 ^ k) ((r / 2 ^ shB) % 2 ^ k)) 0
  rw [muxBPlanesT1, packRowAtT1_buildPlanesT1 r _ k 0 v fun j hj ↦ by
        rw [Nat.zero_add, bitAt_andPlaneT1, bitAt_muxPlaneT1 h1, nat_add_eq, nat_add_eq,
            hVt (shA + j) (by omega), hVt (shB + j) (by omega),
            bitAt_div_modT1 r shA k j hj, bitAt_div_modT1 r shB k j hj]
        cases hDX : bitAt doX r <;> cases hSw : bitAt sw r <;>
          simp [v, hDX, hSw, bitAt_eq_testBit],
      Nat.mod_eq_of_lt (by
        cases hDX : bitAt doX r <;> cases hSw : bitAt sw r <;>
          simp [v, hDX, hSw, Nat.mod_lt _ (Nat.two_pow_pos k), Nat.two_pow_pos k])]
/-- Check `carePlane &&& ov == carePlane &&& sv` across corresponding bitplanes. -/
def checkPlanesEqT1 (carePlane : ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | ov :: os, sv :: ss =>
      Bool.and (Nat.beq (Nat.land carePlane ov) (Nat.land carePlane sv))
        (checkPlanesEqT1 carePlane os ss)
  | _, _ => false
theorem packRowAtT1_of_checkPlanesEqT1 {carePlane r : ℕ} (hCare : bitAt carePlane r = true) :
    ∀ {os ss : List ℕ}, checkPlanesEqT1 carePlane os ss = true →
      packRowAtT1 r os = packRowAtT1 r ss
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => Bool.noConfusion h
  | ov :: os, sv :: ss, h => by
      rcases Bool.and_eq_true_iff.mp h with ⟨hHd, hTl⟩
      have hEq : bitAt (andPlaneT1 carePlane ov) r = bitAt (andPlaneT1 carePlane sv) r :=
        congrArg (fun w ↦ bitAt w r) (Nat.beq_eq.mp hHd)
      rw [bitAt_andPlaneT1, bitAt_andPlaneT1, hCare, Bool.true_and, Bool.true_and] at hEq
      rw [packRowAtT1, packRowAtT1, hEq, packRowAtT1_of_checkPlanesEqT1 hCare hTl]
/-- Word-parallel `2^m`-bit bitplane certificate (`0` per-row loop). -/
def checkBlockPlanesT1 (N : ℕ) (gatesAt : ℕ → ℕ × ℕ) (k0 m : ℕ) (inMasks : List ℕ)
    (lgates : List (ℕ × ℕ)) (louts gouts : List ℕ) (mkPlanes : ℕ → (ℕ → ℕ) → ℕ × List ℕ) : Bool :=
  checkBlockWithOutsT1 N gatesAt k0 m inMasks lgates louts gouts fun tr0 outs ↦
    match mkPlanes (getWTree 7 tr0 0) (fun i ↦ getWTree 7 tr0 (Nat.succ i)) with
    | (carePlane, specPlanes) => checkPlanesEqT1 carePlane outs specPlanes
theorem wPack_of_checkBlockPlanesT1
    {N k0 m : ℕ} {gatesAt : ℕ → ℕ × ℕ} {inMasks : List ℕ} {lgates : List (ℕ × ℕ)}
    {louts gouts : List ℕ} {mkPlanes : ℕ → (ℕ → ℕ) → ℕ × List ℕ}
    {care : ℕ → Bool} {spec : ℕ → ℕ}
    (hWf : gatesWfCheck N gatesAt = true)
    (hCert : checkBlockPlanesT1 N gatesAt k0 m inMasks lgates louts gouts mkPlanes = true)
    (hPlanes : ∀ {r ones : ℕ} {vt : ℕ → ℕ},
      r < 2 ^ m → bitAt ones r = true → (∀ i < m, bitAt (vt i) r = bitAt r i) →
      care r = true →
      bitAt (mkPlanes ones vt).1 r = true ∧ packRowAtT1 r (mkPlanes ones vt).2 = spec r)
    (c : Fin (2 ^ 41))
    (hCare : care (wPack (xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl) inMasks) = true) :
    let e := xagEnv c.val N (fun j ↦ gatesAt j.val) N le_rfl
    wPack e gouts = spec (wPack e inMasks) := by
  intro e
  rcases checkBlockWithOutsT1_imp hWf hCert c with ⟨tr0, outs, hFin, hRLt, hOnes, hVt, hOut⟩
  obtain ⟨hCP, hSP⟩ := hPlanes hRLt hOnes hVt hCare
  rcases hMk : mkPlanes (getWTree 7 tr0 0) (fun i ↦ getWTree 7 tr0 (Nat.succ i)) with ⟨cp, sp⟩
  rw [hMk] at hFin hCP hSP
  rw [← hOut, packRowAtT1_of_checkPlanesEqT1 hCP hFin, hSP]
/-- Bitplane pair `(carePlane, planes)` for `k`-bit swapped `2`-way MUX with `sw` output (`F22`). -/
def planesSwMux2T1 (k ones : ℕ) (vt : ℕ → ℕ) : ℕ × List ℕ :=
  let sw := andPlaneT1 (vt 1) (notPlaneT1 ones (vt 2))
  (orPlaneT1 (notPlaneT1 ones (vt 1)) (vt 0),
   (sw :: muxAPlanesT1 vt ones sw (vt 0) 3 (3 + k) k) ++
     muxBPlanesT1 vt ones (vt 1) sw 3 (3 + k) k)
theorem planesSwMux2T1_spec {k m r ones : ℕ} {vt : ℕ → ℕ} (hk : 3 + 2 * k ≤ m)
    (_hr : r < 2 ^ m) (h1 : bitAt ones r = true) (hVt : ∀ i < m, bitAt (vt i) r = bitAt r i)
    (hCare : Bool.or (Bool.not (bitAt r 1)) (bitAt r 0) = true) :
    bitAt (planesSwMux2T1 k ones vt).1 r = true ∧
      packRowAtT1 r (planesSwMux2T1 k ones vt).2 =
        let sw := Bool.and (bitAt r 1) (Bool.not (bitAt r 2))
        cond sw 1 0 +
          2 * cond sw ((r / 2 ^ (3 + k)) % 2 ^ k) (cond (bitAt r 0) ((r / 8) % 2 ^ k) 0) +
          2 ^ (k + 1) * cond (bitAt r 1)
            (cond sw ((r / 8) % 2 ^ k) ((r / 2 ^ (3 + k)) % 2 ^ k)) 0 := by
  dsimp only [planesSwMux2T1]
  refine ⟨?_, ?_⟩
  · rwa [bitAt_orPlaneT1, bitAt_notPlaneT1 h1, hVt 1 (by omega), hVt 0 (by omega)]
  rw [List.cons_append, packRowAtT1_cons, packRowAtT1_append,
    show (muxAPlanesT1 _ _ _ _ _ _ k).length = k from buildPlanesT1_len _ k 0,
    packRowAtT1_muxAPlanesT1 h1 hVt 3 (3 + k) k (by omega) (by omega),
    packRowAtT1_muxBPlanesT1 h1 hVt 3 (3 + k) k (by omega) (by omega),
    bitAt_andPlaneT1, bitAt_notPlaneT1 h1,
    hVt 0 (by omega), hVt 1 (by omega), hVt 2 (by omega),
    show 2 ^ (k + 1) = 2 * 2 ^ k by ring]
  ring_nf
/-- Bitplane pair for `k`-bit direct `2`-way MUX (`F23`, `F25`). -/
def planesDirectMux2T1 (k ones : ℕ) (vt : ℕ → ℕ) : ℕ × List ℕ :=
  (andPlaneT1 (orPlaneT1 (notPlaneT1 ones (vt 1)) (vt 0))
     (orPlaneT1 (notPlaneT1 ones (vt 2)) (vt 1)),
   muxAPlanesT1 vt ones (vt 2) (vt 0) 3 (3 + k) k ++
     muxBPlanesT1 vt ones (vt 1) (vt 2) 3 (3 + k) k)
theorem planesDirectMux2T1_spec {k m r ones : ℕ} {vt : ℕ → ℕ} (hk : 3 + 2 * k ≤ m)
    (_hr : r < 2 ^ m) (h1 : bitAt ones r = true) (hVt : ∀ i < m, bitAt (vt i) r = bitAt r i)
    (hCare : Bool.and (Bool.or (Bool.not (bitAt r 1)) (bitAt r 0))
                      (Bool.or (Bool.not (bitAt r 2)) (bitAt r 1)) = true) :
    bitAt (planesDirectMux2T1 k ones vt).1 r = true ∧
      packRowAtT1 r (planesDirectMux2T1 k ones vt).2 =
        let a := (r / 8) % 2 ^ k; let b := (r / 2 ^ (3 + k)) % 2 ^ k
        cond (bitAt r 2) b (cond (bitAt r 0) a 0) +
          2 ^ k * cond (bitAt r 1) (cond (bitAt r 2) a b) 0 := by
  dsimp only [planesDirectMux2T1]
  refine ⟨by rwa [bitAt_andPlaneT1, bitAt_orPlaneT1, bitAt_orPlaneT1, bitAt_notPlaneT1 h1,
    bitAt_notPlaneT1 h1, hVt 0 (by omega), hVt 1 (by omega), hVt 2 (by omega)], ?_⟩
  rw [packRowAtT1_append,
    show (muxAPlanesT1 _ _ _ _ _ _ k).length = k from buildPlanesT1_len _ k 0,
    packRowAtT1_muxAPlanesT1 h1 hVt 3 (3 + k) k (by omega) (by omega),
    packRowAtT1_muxBPlanesT1 h1 hVt 3 (3 + k) k (by omega) (by omega),
    hVt 0 (by omega), hVt 1 (by omega), hVt 2 (by omega)]
  rfl
/-- Bitplane pair for dual `k`-bit swapped MUX with `sw` output (`F24`). -/
def planesSwMux4T1 (k ones : ℕ) (vt : ℕ → ℕ) : ℕ × List ℕ :=
  let sw := andPlaneT1 (vt 1) (notPlaneT1 ones (vt 2))
  (orPlaneT1 (notPlaneT1 ones (vt 1)) (vt 0),
   (sw :: muxAPlanesT1 vt ones sw (vt 0) 3 (3 + k) k) ++
     (muxBPlanesT1 vt ones (vt 1) sw 3 (3 + k) k ++
       (muxAPlanesT1 vt ones sw (vt 0) (3 + 2 * k) (3 + 3 * k) k ++
         muxBPlanesT1 vt ones (vt 1) sw (3 + 2 * k) (3 + 3 * k) k)))
theorem planesSwMux4T1_spec {k m r ones : ℕ} {vt : ℕ → ℕ} (hk : 3 + 4 * k ≤ m)
    (_hr : r < 2 ^ m) (h1 : bitAt ones r = true) (hVt : ∀ i < m, bitAt (vt i) r = bitAt r i)
    (hCare : Bool.or (Bool.not (bitAt r 1)) (bitAt r 0) = true) :
    bitAt (planesSwMux4T1 k ones vt).1 r = true ∧
      packRowAtT1 r (planesSwMux4T1 k ones vt).2 =
        let sw := Bool.and (bitAt r 1) (Bool.not (bitAt r 2))
        let a := (r / 8) % 2 ^ k
        let b := (r / 2 ^ (3 + k)) % 2 ^ k
        let s1 := (r / 2 ^ (3 + 2 * k)) % 2 ^ k
        let s2 := (r / 2 ^ (3 + 3 * k)) % 2 ^ k
        cond sw 1 0 + 2 * cond sw b (cond (bitAt r 0) a 0) +
          2 ^ (k + 1) * cond (bitAt r 1) (cond sw a b) 0 +
          2 ^ (2 * k + 1) * cond sw s2 (cond (bitAt r 0) s1 0) +
          2 ^ (3 * k + 1) * cond (bitAt r 1) (cond sw s1 s2) 0 := by
  dsimp only [planesSwMux4T1]
  refine ⟨?_, ?_⟩
  · rwa [bitAt_orPlaneT1, bitAt_notPlaneT1 h1, hVt 1 (by omega), hVt 0 (by omega)]
  rw [List.cons_append, packRowAtT1_cons, packRowAtT1_append, packRowAtT1_append,
    packRowAtT1_append,
    show (muxAPlanesT1 _ _ _ _ _ _ k).length = k from buildPlanesT1_len _ k 0,
    show (muxBPlanesT1 _ _ _ _ _ _ k).length = k from buildPlanesT1_len _ k 0,
    show (muxAPlanesT1 _ _ _ _ (3 + 2 * k) _ k).length = k from buildPlanesT1_len _ k 0,
    packRowAtT1_muxAPlanesT1 h1 hVt 3 (3 + k) k (by omega) (by omega),
    packRowAtT1_muxBPlanesT1 h1 hVt 3 (3 + k) k (by omega) (by omega),
    packRowAtT1_muxAPlanesT1 h1 hVt (3 + 2 * k) (3 + 3 * k) k (by omega) (by omega),
    packRowAtT1_muxBPlanesT1 h1 hVt (3 + 2 * k) (3 + 3 * k) k (by omega) (by omega),
    bitAt_andPlaneT1, bitAt_notPlaneT1 h1,
    hVt 0 (by omega), hVt 1 (by omega), hVt 2 (by omega),
    show 2 * k + 1 = k + k + 1 by omega, show 3 * k + 1 = k + k + k + 1 by omega,
    Nat.pow_succ, Nat.pow_add, Nat.pow_add]
  ring_nf
/-- Bitplane pair for `cond (bitAt r 0) (r / 2) 0` on `m = 1 + k` (`F26`). -/
def planesGateTopSliceT1 (k ones : ℕ) (vt : ℕ → ℕ) : ℕ × List ℕ :=
  (ones, buildPlanesT1 (fun j ↦ andPlaneT1 (vt 0) (vt (Nat.add 1 j))) k 0)
theorem planesGateTopSliceT1_spec {k r ones : ℕ} {vt : ℕ → ℕ} (hr : r < 2 ^ (1 + k))
    (h1 : bitAt ones r = true) (hVt : ∀ i < 1 + k, bitAt (vt i) r = bitAt r i) :
    bitAt (planesGateTopSliceT1 k ones vt).1 r = true ∧
      packRowAtT1 r (planesGateTopSliceT1 k ones vt).2 = cond (bitAt r 0) (r / 2) 0 := by
  have hDivLt : r / 2 < 2 ^ k :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.pow_add, mul_comm] using hr)
  set v := cond (bitAt r 0) (r / 2) 0
  refine ⟨h1, (packRowAtT1_buildPlanesT1 r _ k 0 v fun j hj ↦ ?_).trans
    (Nat.mod_eq_of_lt (by cases h0 : bitAt r 0 <;> simp [v, h0, hDivLt, Nat.two_pow_pos k]))⟩
  rw [Nat.zero_add, bitAt_andPlaneT1, nat_add_eq, hVt 0 (by omega), hVt (1 + j) (by omega),
    bitAt_div_modT1 r 1 k j hj, pow_one, Nat.mod_eq_of_lt hDivLt]
  cases h0 : bitAt r 0 <;> simp [v, h0, bitAt_eq_testBit]
/-- Bitplane pair `(carePlane, planes)` for `F20` (`B17ab_do_pot`). -/
def planesPot20T1 (ones : ℕ) (vt : ℕ → ℕ) : ℕ × List ℕ :=
  let a1 := orPlaneT1 (vt 0) (vt 1); let b1 := andPlaneT1 (vt 0) (vt 1)
  let b2 := orPlaneT1 b1 (andPlaneT1 a1 (vt 2)); let a2 := orPlaneT1 a1 (vt 2)
  let b3 := orPlaneT1 b2 (andPlaneT1 a2 (vt 3)); let a3 := orPlaneT1 a2 (vt 3)
  let b4 := orPlaneT1 b3 (andPlaneT1 a3 (vt 4)); let a4 := orPlaneT1 a3 (vt 4)
  let b5 := orPlaneT1 b4 (andPlaneT1 a4 (vt 5)); let z12 := andPlaneT1 (vt 7) (vt 8)
  let doEe :=
      andPlaneT1 (andPlaneT1 z12 (notPlaneT1 ones (vt 9))) (orPlaneT1 (vt 0) (andPlaneT1 (vt 1)
      (vt 6)))
  let doNn :=
      andPlaneT1 (andPlaneT1 z12 (notPlaneT1 ones (vt 10))) (orPlaneT1 (vt 2) (andPlaneT1 (vt 3)
      (vt 6)))
  let doEn := andPlaneT1 (vt 7) (orPlaneT1 (vt 4) (andPlaneT1 (vt 5) (vt 6)))
  (notPlaneT1 ones b5, [doEe, doNn, doEn])
end QuantumComputation.Specs.PhotochemistrySolution.Tier1K3708
end
end
