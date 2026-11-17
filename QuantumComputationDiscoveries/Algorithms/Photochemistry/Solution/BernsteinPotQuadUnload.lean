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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.QftPostCancelPotWiring
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.KineticBellSwapMux

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (stepCB
    SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn
    portSwap1Circ portSwapVecCirc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (permUnitary_mulVec_ket ket_H)
section

open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (ComputeProgWires)
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
set_option exponentiation.threshold 8192
open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate Real QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution
  PhotochemistrySolution.ClusterPotSlice PhotochemistrySolution.KinNormSlice
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.TelescopeSlice PhotochemistrySolution.EvenOctB70
  PhotochemistrySolution.ScreenFermatCore PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.Sub5885
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen

/-- GMP `O(1)`-depth Lagrange bin-box check (`0` `Nat.ble`, `0` `Classical.propDecidable`). -/
def boxOkFast (b1 b2 c : ℕ) : Bool :=
  let a0 : ℤ := binLoUltra b1; let a1 : ℤ := binHiUltra b1; let d0 : ℤ := binLoUltra b2;
  let d1 : ℤ := binHiUltra b2; let cz : ℤ := c
  (zLeB (cz + 1) (a1 + d1) || zLeB ((cz - a1 - d1) ^ 2) (4 * a1 * d1)) &&
  (zLeB (a0 + 1) (d1 + cz) || zLeB ((a0 - d1 - cz) ^ 2) (4 * d1 * cz)) &&
  (zLeB (d0 + 1) (a1 + cz) || zLeB ((d0 - a1 - cz) ^ 2) (4 * a1 * cz))
/-- Range check over active `(k, idx7, j)` control points (`0` `Nat.ble`, `0` `propDecidable`). -/
def checkPopBernCtrlRanges (word512 : ℕ → ℕ) (yClamp0 yClamp1 yLoF yHiF yHiF48 yLoT yHiT : ℕ) :
    Bool :=
  (natLeB yLoF yClamp0 && natLeB yClamp0 yHiF48 && natLeB yHiF48 yHiF &&
   natLeB yLoF yClamp1 && natLeB yClamp1 yHiF48 &&
   natLeB yLoT yClamp0 && natLeB yClamp0 yHiT &&
   natLeB yLoT yClamp1 && natLeB yClamp1 yHiT) &&
  allRange 4 9 fun k ↦ allRange 7 128 fun i7 ↦
    cond (Nat.beq k 8 && natLeB 95 i7) true
      (allRange 2 4 fun j ↦
        let y := (word512 (4 * i7 + j)) >>> k
        (cond (Nat.beq k 0 && Nat.beq i7 0 && natLtB 0 j) true
          (natLeB yLoF y && natLeB y yHiF)) &&
        (cond (natLtB k 2 || (Nat.beq k 2 && natLtB i7 96) ||
            (Nat.beq k 2 && Nat.beq i7 96 && natLtB 0 j)) true
          (natLeB yLoF y && natLeB y yHiF48)) &&
        (cond (Nat.beq k 0 || (Nat.beq k 1 && natLtB i7 64) ||
            (Nat.beq k 1 && Nat.beq i7 64 && natLtB 0 j)) true
          (natLeB yLoT y && natLeB y yHiT)))
theorem boxOkFast_of_boxOkUltra {b1 b2 c : ℕ} (h : boxOkUltra b1 b2 c = true) :
    boxOkFast b1 b2 c = true := by
  simp only [boxOkUltra, decide_eq_true_eq] at h
  simp only [boxOkFast, Bool.and_eq_true, Bool.or_eq_true, zLeB_eq_true]
  exact ⟨⟨if h1 : (binHiUltra b1 : ℤ) + binHiUltra b2 ≤ c then .inr (h.1 h1) else .inl (by omega),
    if h2 : (binHiUltra b2 : ℤ) + c ≤ binLoUltra b1 then .inr (h.2.1 h2) else .inl (by omega)⟩,
    if h3 : (binHiUltra b1 : ℤ) + c ≤ binLoUltra b2 then .inr (h.2.2 h3) else .inl (by omega)⟩
set_option maxHeartbeats 800000 in
-- Large circuit/register elaboration requires raised heartbeat limit.
theorem ctrl_bounds_of_ranges {word512 : ℕ → ℕ} {yClamp0 yClamp1 yLoF yHiF yHiF48 yLoT yHiT : ℕ}
    (hr : checkPopBernCtrlRanges word512 yClamp0 yClamp1 yLoF yHiF yHiF48 yLoT yHiT = true) :
    (∀ {d2 : ℕ}, Is3DBoxDistSq d2 → ∀ c : Fin 3 → Fin 2048,
      yLoF ≤ y36PopBernClamped word512 yClamp0 yClamp1 false d2 c ∧
        y36PopBernClamped word512 yClamp0 yClamp1 false d2 c ≤ yHiF) ∧
    (∀ {d2 : ℕ}, Is3DBoxDistSq d2 → 48 ≤ d2 → ∀ c : Fin 3 → Fin 2048,
      yLoF ≤ y36PopBernClamped word512 yClamp0 yClamp1 false d2 c ∧
        y36PopBernClamped word512 yClamp0 yClamp1 false d2 c ≤ yHiF48) ∧
    (∀ {d2 : ℕ}, Is3DBoxDistSq d2 → ∀ c : Fin 3 → Fin 2048,
      yLoT ≤ y36PopBernClamped word512 yClamp0 yClamp1 true d2 c ∧
        y36PopBernClamped word512 yClamp0 yClamp1 true d2 c ≤ yHiT) := by
  rcases (by simpa only [checkPopBernCtrlRanges, Bool.and_eq_true, natLeB_eq_true] using hr) with
      ⟨hcl, hall⟩
  have active (isNN : Bool) {d2 : ℕ} (h3d : Is3DBoxDistSq d2) (c : Fin 3 → Fin 2048) :
      (d2 < 194560 ∧ ∃ j : Fin 4, (t11OfParts (evenOctIdxT10K isNN d2) = 0 → j.val = 0) ∧
        y36PopBernClamped word512 yClamp0 yClamp1 isNN d2 c =
          (word512 (4 * idx7OfParts (evenOctIdxT10K isNN d2) +
              j.val)) >>> (evenOctIdxT10K isNN d2).2.2) ∨
      (y36PopBernClamped word512 yClamp0 yClamp1 isNN d2 c = yClamp0 ∨
       y36PopBernClamped word512 yClamp0 yClamp1 isNN d2 c = yClamp1) := by
    by_cases hge : 194560 ≤ d2
    · rcases openDistSq_ge_194560_iff h3d hge with rfl | rfl
      · exact .inr (.inl (by simp [y36PopBernClamped,
          (by cases isNN <;> decide : isClamp95Parts (evenOctIdxT10K isNN 194566) = true),
          (by cases isNN <;> decide : (t11OfParts (evenOctIdxT10K isNN 194566)).testBit 9 =
                false)]))
      · exact .inr (.inr (by simp [y36PopBernClamped,
          (by cases isNN <;> decide : isClamp95Parts (evenOctIdxT10K isNN 195075) = true),
          (by cases isNN <;> decide : (t11OfParts (evenOctIdxT10K isNN 195075)).testBit 9 = true)]))
    · exact .inl ⟨by omega, ⟨popBernJ (t11OfParts (evenOctIdxT10K isNN d2)) c,
          popBernJ_lt_four _ c⟩,
        fun ht0 ↦ (congrArg (popBernJ · c) ht0).trans (popBernJ_zero_of_t11_zero c),
        by simp [y36PopBernClamped, Bool.eq_false_iff.mpr fun hc ↦
          hge ((isClamp95Parts_iff_ge_194560 isNN (is3DBoxDistSq_le h3d)).mp hc)]⟩
  have row (isNN : Bool) {d2 : ℕ} (hlt : d2 < 194560) (j : Fin 4) :
      let p := evenOctIdxT10K isNN d2
      let y := (word512 (4 * idx7OfParts p + j.val)) >>> p.2.2
      (cond (Nat.beq p.2.2 0 && Nat.beq (idx7OfParts p) 0 && natLtB 0 j.val) true
        (natLeB yLoF y && natLeB y yHiF) = true ∧
       cond (natLtB p.2.2 2 || (Nat.beq p.2.2 2 && natLtB (idx7OfParts p) 96) ||
         (Nat.beq p.2.2 2 && Nat.beq (idx7OfParts p) 96 && natLtB 0 j.val)) true
         (natLeB yLoF y && natLeB y yHiF48) = true) ∧
      cond (Nat.beq p.2.2 0 || (Nat.beq p.2.2 1 && natLtB (idx7OfParts p) 64) ||
        (Nat.beq p.2.2 1 && Nat.beq (idx7OfParts p) 64 && natLtB 0 j.val)) true
        (natLeB yLoT y && natLeB y yHiT) = true := by
    have hb := parts_popBern_bounds isNN (hlt.trans (by omega))
    have h1 := allRange_eq_true (by norm_num)
      (allRange_eq_true (by norm_num) hall (Nat.lt_succ_of_le hb.2.2)) hb.1
    rw [cond_false_of_not (by
      simp only [Bool.and_eq_true, Nat.beq_eq, natLeB_eq_true]
      rintro ⟨hk8, h95⟩
      dsimp only [evenOctIdxT10K, idx7OfParts] at hk8 h95
      have _ : max d2 (if isNN = true then 8 else 1) < 194560 :=
          max_lt hlt (by split_ifs <;> norm_num)
      rw [hk8, Nat.shiftLeft_eq] at h95
      split_ifs at h95 <;> omega)] at h1
    simpa only [Bool.and_eq_true] using allRange_eq_true (by norm_num) h1 j.isLt
  clear hall
  refine ⟨fun {d2} h3d c ↦ ?_, fun {d2} h3d h48 c ↦ ?_, fun {d2} h3d c ↦ ?_⟩
  · rcases active false h3d c with ⟨hlt, j, ht0, hy⟩ | (hy | hy)
    · have h3 := (row false hlt j).1.1
      rw [cond_false_of_not (by
        simp only [Bool.and_eq_true, Nat.beq_eq, natLtB_eq_true]
        rintro ⟨⟨hk0, hi0⟩, hj0⟩
        have _ : d2 < 4 := by
          dsimp only [evenOctIdxT10K, evenOctKRef] at hk0
          have _ : d2 ≤ max d2 (if false = true then 8 else 1) := le_max_left d2 _
          split_ifs at hk0 <;> omega
        interval_cases d2 <;> exact hj0.ne' (ht0 rfl))] at h3
      simpa only [hy, Bool.and_eq_true, natLeB_eq_true] using h3
    all_goals
      rw [hy]
      omega
  · rcases active false h3d c with ⟨hlt, j, ht0, hy⟩ | (hy | hy)
    · have hkGe : 2 ≤ (evenOctIdxT10K false d2).2.2 ∧ ((evenOctIdxT10K false d2).2.2 = 2 → d2 < 64)
          := by
        dsimp only [evenOctIdxT10K, evenOctKRef]
        rw [max_eq_left (le_trans (by decide) h48)]
        split_ifs <;> omega
      have h3 := (row false hlt j).1.2
      rw [cond_false_of_not (by
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, natLtB_eq_true]
        rintro ((hk2 | ⟨hk2, hi⟩) | ⟨⟨hk2, hi⟩, hj0⟩)
        · exact absurd hk2 (not_lt.mpr hkGe.1)
        all_goals
          have _ := hkGe.2 hk2
          interval_cases d2 <;>
              first | exact hj0.ne' (ht0 rfl) | exact absurd hi (by decide))] at h3
      simpa only [hy, Bool.and_eq_true, natLeB_eq_true] using h3
    all_goals
      rw [hy]
      omega
  · rcases active true h3d c with ⟨hlt, j, ht0, hy⟩ | (hy | hy)
    · have hkGe : 1 ≤ (evenOctIdxT10K true d2).2.2 ∧ ((evenOctIdxT10K true d2).2.2 = 1 → d2 < 16)
          := by
        dsimp only [evenOctIdxT10K]
        set m := max d2 (if true = true then 8 else 1)
        have _ : 8 ≤ m ∧ d2 ≤ m := ⟨le_max_right d2 _, le_max_left d2 _⟩
        unfold evenOctKRef
        split_ifs <;> omega
      have h3 := (row true hlt j).2
      rw [cond_false_of_not (by
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, natLtB_eq_true]
        rintro ((hk0 | ⟨hk1, hi⟩) | ⟨⟨hk1, hi⟩, hj0⟩)
        · exact absurd hk0 (by omega)
        all_goals
          have _ := hkGe.2 hk1
          interval_cases d2 <;>
              first | exact hj0.ne' (ht0 rfl) | exact absurd hi (by decide))] at h3
      simpa only [hy, Bool.and_eq_true, natLeB_eq_true] using h3
    all_goals
      rw [hy]
      omega
/- ## Canonical `kExt`-Coin Expectation & `PopBern` Potential Abbreviations -/

/-- Uniform `2 ^ kExt` expectation of any `kExt`-coin family of `PotExpectFn`s. -/
abbrev potExpectAvgK {kExt : ℕ} (peK : BitAssignment kExt → PotExpectFn) : PotExpectFn :=
    fun s nn sp1 sp2 nA nB eA eB ↦
    (2 ^ kExt : ℝ)⁻¹ * ∑ γ : BitAssignment kExt, peK γ s nn sp1 sp2 nA nB eA eB
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein

namespace QuantumComputation.Specs.PhotochemistrySolution.OuterW11Alt
set_option exponentiation.threshold 8192
open Real PhotochemistrySolution.EvenOctB70
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (idx7OfParts t11OfParts)
inductive ChW11 : Type
  | ee : ChW11
  | nn : ChW11
  | en9 : ChW11
  | en10 : ChW11
def chFnFast : ChW11 → Nat → Nat
  | .ee, y => y / 64
  | .nn, y => y / 32
  | .en9, y => y / 64 + y / 8
  | .en10, y => y / 32 + y / 8
inductive NatTree : Type
  | leaf : Nat → NatTree
  | node : NatTree → NatTree → NatTree
inductive Cube3 : Type
  | mk : NatTree → NatTree → Cube3
inductive SumTree : Type
  | leaf : Nat → SumTree
  | node : Nat → SumTree → SumTree → SumTree
/-- Root sum of a `SumTree`. -/
def stVal : SumTree → Nat
  | .leaf v => v
  | .node v _ _ => v
/-- Computable clamped squared distance `max d2 (if isNN then 8 else 1)`. -/
def maxDistW11 (isNN : Bool) (d2 : Nat) : Nat :=
  cond isNN (cond (Nat.ble (d2 + 1) 8) 8 d2) (cond (Nat.ble (d2 + 1) 1) 1 d2)
/-- Computable even-octave index `k ∈ 0..8` of clamped `m`. -/
def evenOctKW11 (m : Nat) : Nat :=
  cond (Nat.ble (m + 1) 4) 0 (cond (Nat.ble (m + 1) 16) 1 (cond (Nat.ble (m + 1) 64) 2
    (cond (Nat.ble (m + 1) 256) 3 (cond (Nat.ble (m + 1) 1024) 4 (cond (Nat.ble (m + 1) 4096) 5
      (cond (Nat.ble (m + 1) 16384) 6 (cond (Nat.ble (m + 1) 65536) 7 8)))))))
/-- Computable `(idx8, t10, k)` decomposition matching `evenOctIdxT10K`. -/
def evenOctPartsW11 (isNN : Bool) (d2 : Nat) : Nat × Nat × Nat :=
  let m := maxDistW11 isNN d2; let k := evenOctKW11 m; let u := m * (2 ^ (16 - 2 * k))
  (cond (Nat.ble (u + 1) 131072) ((u - 65536) / 512) (128 + (u - 131072) / 1024),
   cond (Nat.ble (u + 1) 131072) ((u % 512) * 2) (u % 1024), k)
theorem cond_ble_eq_ite_w11B {α : Type*} (a b : Nat) (x y : α) :
    cond (Nat.ble a b) x y = if a ≤ b then x else y := by
  by_cases h : a ≤ b <;> simp [Nat.ble_eq, h]
theorem cond_ble_succ_eq_ite_w11B {α : Type*} (a b : Nat) (x y : α) :
    cond (Nat.ble (a + 1) b) x y = if a < b then x else y :=
  (cond_ble_eq_ite_w11B (a + 1) b x y).trans (by split_ifs <;> first | rfl | omega)
theorem maxDistW11_eq_w11B (isNN : Bool) (d2 : Nat) :
    maxDistW11 isNN d2 = max d2 (if isNN then 8 else 1) := by
  cases isNN <;> simp only [maxDistW11, Bool.cond_true, Bool.cond_false, Bool.false_eq_true,
    ↓reduceIte, cond_ble_succ_eq_ite_w11B, Nat.max_def] <;> split_ifs <;> omega
theorem evenOctKW11_eq_w11B (m : Nat) : evenOctKW11 m = evenOctKRef m := by
  simp only [evenOctKW11, evenOctKRef, cond_ble_succ_eq_ite_w11B]
theorem evenOctPartsW11_eq_w11B (isNN : Bool) (d2 : Nat) :
    evenOctPartsW11 isNN d2 = evenOctIdxT10K isNN d2 := by
  simp only [evenOctPartsW11, evenOctIdxT10K, maxDistW11_eq_w11B, evenOctKW11_eq_w11B,
      Nat.shiftLeft_eq, cond_ble_succ_eq_ite_w11B]
theorem evenOct_m_shift_w11B (isNN : Bool) {d2 : Nat} (hd2 : d2 < 262144) :
    let p := evenOctIdxT10K isNN d2
    let i7 := idx7OfParts p
    let shP := cond (Nat.ble 64 i7) (16 - 2 * p.2.2) (17 - 2 * p.2.2)
    let w0P := cond (Nat.ble 64 i7) (2048 * i7) (131072 + 2048 * i7)
    max d2 (if isNN then 8 else 1) * 2 ^ shP = w0P + t11OfParts p := by
  dsimp only [evenOctIdxT10K, idx7OfParts, t11OfParts]
  simp only [Nat.shiftLeft_eq, cond_ble_eq_ite_w11B]
  set m := max d2 (if isNN then 8 else 1)
  have _ : 1 ≤ m ∧ m < 262144 := by
    cases isNN <;> simp only [m, ↓reduceIte, Bool.false_eq_true] <;> omega
  have _ : evenOctKRef m ≤ 8 ∧ 65536 ≤ m * 2 ^ (16 - 2 * evenOctKRef m) ∧
      m * 2 ^ (16 - 2 * evenOctKRef m) < 262144 := by
        unfold evenOctKRef
        split_ifs <;> omega
  (split_ifs <;> try rw [show m * 2 ^ (17 - 2 * evenOctKRef m) = 2 *
      (m * 2 ^ (16 - 2 * evenOctKRef m)) by
    rw [show 17 - 2 * evenOctKRef m = (16 - 2 * evenOctKRef m) + 1 by omega, pow_succ]
    ring]) <;> omega
theorem evenOct_mid_props_w11B (isNN : Bool) {d2 : Nat}
    (hlo : 256 ≤ d2) (hhi : d2 < 194560) :
    let p := evenOctIdxT10K isNN d2
    let i7 := idx7OfParts p
    let t11 := t11OfParts p
    let k := p.2.2
    let shP := cond (Nat.ble 64 i7) (16 - 2 * k) (17 - 2 * k)
    let rStep := cond (Nat.ble 7 shP) 128 (2 ^ shP)
    4 ≤ k ∧ k ≤ 8 ∧ i7 < 128 ∧ t11 < 2048 ∧ (Nat.beq k 8 && Nat.ble 95 i7) = false ∧
      (t11 % 128) % rStep = 0 := by
  have hb := evenOctIdxT10K_bounds isNN (d2 := d2) (by omega)
  have hs := evenOct_m_shift_w11B isNN (d2 := d2) (by omega)
  dsimp only [idx7OfParts, t11OfParts] at hb hs ⊢
  set p := evenOctIdxT10K isNN d2
  have kR : 4 ≤ p.2.2 ∧ p.2.2 ≤ 8 := by
    have _ : 256 ≤ max d2 (if isNN then 8 else 1) := le_trans hlo (le_max_left _ _)
    dsimp only [p, evenOctIdxT10K, evenOctKRef]
    split_ifs <;> omega
  refine ⟨kR.1, kR.2, by omega, by omega, Bool.eq_false_iff.mpr fun h ↦ by
      rcases (by simpa only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] using h) with ⟨k8, h9⟩
      have _ : max d2 (if isNN then 8 else 1) < 194560 := max_lt hhi (by split_ifs <;> omega)
      dsimp only [p, evenOctIdxT10K] at k8 h9
      rw [k8, show 16 - 2 * 8 = 0 from rfl, Nat.shiftLeft_zero] at h9
      split_ifs at h9 <;> omega, ?_⟩
  simp only [cond_ble_eq_ite_w11B] at hs ⊢
  by_cases h6 : 64 ≤ p.1 / 2 <;> simp only [h6, ↓reduceIte] at hs ⊢ <;>
    rcases (by omega : p.2.2 = 4 ∨ p.2.2 = 5 ∨ p.2.2 = 6 ∨ p.2.2 = 7 ∨ p.2.2 = 8) with
      k | k | k | k | k <;> rw [k] at hs ⊢ <;> norm_num at hs ⊢ <;> omega
/- ## Pure-`Nat` Degree-7 Bernstein & Cubic `evalPointNumST` Soundness -/

inductive PairList : Type
  | nil : PairList
  | cons : NatTree → NatTree → PairList → PairList
inductive L4 : Type
  | mk : Nat → Nat → Nat → Nat → L4
/-- Precomputed `(S2, 7 * S2, 21 * S2, 35 * S2)` threshold tuple for degree-7 Bernstein checks. -/
inductive U7 : Type
  | mk : Nat → Nat → Nat → Nat → U7
/-- Precomputed knot-step chain within a single `(k, half)` octant slice. -/
inductive HChain : Type
  | nil : HChain
  | step :
      Bool → Nat → Nat →
      Bool → Nat → Nat →
      Bool → Nat → Nat →
      Bool → Nat → Nat →
      Nat → HChain → HChain
/-- Precomputed half-octave `(rStep, u7, chain)` for fixed `(ch, s0Sq, k, half)`. -/
inductive HalfOct : Type
  | mk : Nat → U7 → HChain → HalfOct
inductive CConsts : Type
  | mk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → CConsts
end QuantumComputation.Specs.PhotochemistrySolution.OuterW11Alt

namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open Qubit PhotochemistrySolution
def dom22Bit (p : ℕ × ℕ × ℕ) (j : Fin 22) : Bool :=
    if j.val < 8 then p.1.testBit j.val else if j.val < 18 then p.2.1.testBit (j.val -
    8) else p.2.2.testBit (j.val - 18)
def rIdx7Of22 {n : ℕ} (rOut22 : QRegister 22 n) : QRegister 7 n :=
  ⟨⟨fun i ↦ rOut22 ⟨1 + i.val, by omega⟩, fun _ _ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (rOut22.wires.injective e); dsimp at hv; omega)⟩⟩
def rK4Of22 {n : ℕ} (rOut22 : QRegister 22 n) : QRegister 4 n :=
  ⟨⟨fun i ↦ rOut22 ⟨18 + i.val, by omega⟩, fun _ _ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (rOut22.wires.injective e); dsimp at hv; omega)⟩⟩
/-- Map input bit `u ∈ [0..10] ∪ {44} ∪ [45..51]` of `cpPopBernComp` to `Fin 22`. -/
def compOutIdx (u : ℕ) : Fin 22 :=
  if hu0 : u < 10 then ⟨8 + u, by omega⟩
  else if u = 10 then ⟨0, by decide⟩
  else if u = 44 then ⟨21, by decide⟩
  else if hu1 : u < 52 then ⟨u - 44, by omega⟩
  else ⟨0, by decide⟩
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
open Qubit PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
theorem computeProgWires_of_supp {n : ℕ} {S : Wire n → Prop} :
    ∀ {q : ComputeProg n}, ProgSupportedIn S q → ComputeProgWires S q
  | .id, _ => trivial
  | .x _, hu => hu
  | .cnot _ _ _, ⟨hc, ht⟩ => ⟨hc, ht⟩
  | .andGate _ _ _ _ _ _, ⟨h₁, h₂, ha⟩ => ⟨h₁, h₂, ha⟩
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨computeProgWires_of_supp h₁, computeProgWires_of_supp h₂⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
end

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.PotOracleGen
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
theorem mod5_lt (n : ℕ) : n % 5 < 5 := Nat.mod_lt n (by decide)
theorem revCore_coin_lt {M : ℕ} (i : Fin (41 + (M + 3))) : i.val % 41 < 41 :=
    Nat.mod_lt i.val (by decide)
theorem revCore_scr_lt {M : ℕ} (hM5 : M + 5 ≤ 361) (i : Fin (41 + (M + 3))) :
    i.val - 41 < 1493 := by omega
theorem revTmp_m0_lt {M : ℕ} (hM5 : M + 5 ≤ 361) : M < 1493 := by omega
theorem revTmp_m1_lt {M : ℕ} (hM5 : M + 5 ≤ 361) : M + 1 < 1493 := by omega
theorem revTmp_m3_lt {M : ℕ} (hM5 : M + 5 ≤ 361) : M + 3 < 1493 := by omega
theorem revTmp_m4_lt {M : ℕ} (hM5 : M + 5 ≤ 361) : M + 4 < 1493 := by omega
theorem midPred_m2_lt {M : ℕ} (hM5 : M + 5 ≤ 361) : M + 2 < 1493 := by omega
theorem midPred_coin_lt {M : ℕ} (u : Fin (49 + M)) : (u.val - 1) % 41 < 41 :=
    Nat.mod_lt _ (by decide)
theorem midPred_work_lt_all {M : ℕ} (hM5 : M + 5 ≤ 361) (u : Fin (49 + M)) :
    u.val - 42 < 1493 := by omega
theorem midPred_tail_lt {M : ℕ} (u : Fin (49 + M)) : (u.val - (42 + M)) % 5 < 5 := mod5_lt _
theorem midPred_tmp_lt {M : ℕ} (hM5 : M + 5 ≤ 361) (u : Fin (49 + M)) :
    M + 3 + (u.val - (47 + M)) < 1493 := by omega
theorem tailPred_blk_le (M : ℕ) : 0 + (47 + M) ≤ 49 + M := by omega
theorem lt40_15 : 15 < 40 := by decide
theorem lt40_1 : 1 < 40 := by decide
theorem rScr_ne_rOuter41 (k : Fin 1493) (j : Fin 41) :
    rScrCompact1493 k ≠ rOuter41Layout j := fun e ↦ by
  have _ := k.isLt
  have _ := j.isLt
  have hv := congrArg Fin.val e
  rw [val_rScrCompact1493, val_rOuter41Layout] at hv
  split_ifs at hv <;> omega
theorem rScr_ne_rOut40 (k : Fin 1493) (j : Fin 40) :
    rScrCompact1493 k ≠ rOut40Layout j := fun e ↦ by
  have _ := k.isLt
  have _ := j.isLt
  have hv := congrArg Fin.val e
  rw [val_rScrCompact1493, val_rOut40Layout] at hv
  split_ifs at hv <;> omega
theorem rOuter41_ne_rOut40 (i : Fin 41) (j : Fin 40) :
    rOuter41Layout i ≠ rOut40Layout j := fun e ↦ by
  have _ := i.isLt
  have _ := j.isLt
  have hv := congrArg Fin.val e
  rw [val_rOuter41Layout, val_rOut40Layout] at hv
  omega
theorem rOut40Layout_sub_scr (j : Fin 40) : ∃ m : Fin scrLLayout, rOut40Layout j = rScrLayout m :=
  ⟨⟨65 + j.val, by
    dsimp [scrLLayout]
    omega⟩,
    Fin.ext (by
      rw [val_rOut40Layout, val_rScrLayout]
      dsimp
      omega)⟩
/--
Wire map for `(41 + (M + 3))` -wire reverse core (`rOuter41Layout ++ rScrCompact1493[0..M+2]`).
-/
def revCoreWireFn (M : ℕ) (hM5 : M + 5 ≤ 361) (i : Fin (41 + (M + 3))) : Wire dLayout :=
    if Nat.ble (i.val + 1) 41 then rOuter41Layout ⟨i.val % 41,
    revCore_coin_lt i⟩ else rScrCompact1493 ⟨i.val - 41, revCore_scr_lt hM5 i⟩
theorem revCoreWireFn_injective (M : ℕ) (hM5 : M + 5 ≤ 361) :
    Function.Injective (revCoreWireFn M hM5) := fun a b e ↦ by
  dsimp only [revCoreWireFn] at e
  split_ifs at e with ha hb hb
  · have h := congrArg Fin.val (rOuter41Layout.wires.injective e)
    dsimp only at h
    rw [Nat.mod_eq_of_lt (Nat.le_of_ble_eq_true ha),
        Nat.mod_eq_of_lt (Nat.le_of_ble_eq_true hb)] at h
    exact Fin.ext h
  · exact absurd e.symm (rScr_ne_rOuter41 _ _)
  · exact absurd e (rScr_ne_rOuter41 _ _)
  · have _ : ¬a.val < 41 := fun l ↦ ha (Nat.ble_eq_true_of_le l)
    have _ : ¬b.val < 41 := fun l ↦ hb (Nat.ble_eq_true_of_le l)
    have h := congrArg Fin.val (rScrCompact1493.wires.injective e)
    clear e
    dsimp only at h
    exact Fin.ext (by omega)
def rRevCore (M : ℕ) (hM5 : M + 5 ≤ 361) : QRegister (41 + (M + 3)) dLayout :=
    ⟨⟨revCoreWireFn M hM5, revCoreWireFn_injective M hM5⟩⟩
theorem rRevCore_coin (M : ℕ) (hM5 : M + 5 ≤ 361) (k : Fin 41) :
    rRevCore M hM5 ⟨k.val, by omega⟩ = rOuter41Layout k := by
  change revCoreWireFn M hM5 ⟨k.val, _⟩ = rOuter41Layout k
  dsimp only [revCoreWireFn]
  rw [ite_eq_left (Nat.ble_eq_true_of_le k.isLt)]
  exact congrArg rOuter41Layout (Fin.ext (Nat.mod_eq_of_lt k.isLt))
theorem rRevCore_scr (M : ℕ) (hM5 : M + 5 ≤ 361) (k : Fin (M + 3)) :
    rRevCore M hM5 ⟨41 + k.val, by omega⟩ =
      rScrCompact1493 ⟨k.val, by omega⟩ := by
  change revCoreWireFn M hM5 ⟨41 + k.val, _⟩ = _
  dsimp only [revCoreWireFn]
  rw [ite_eq_right (mt Nat.ble_eq.mp (by omega))]
  exact congrArg rScrCompact1493 (Fin.ext (by
    dsimp only
    omega))
/--
Wire map for `6` -wire First-pass `TempAND` helper
`[out[15], scr[M], out[1], scr[M+1], scr[M+3], scr[M+4]]` .
-/
def revTmpWireFn (M : ℕ) (hM5 : M + 5 ≤ 361) (i : Fin 6) : Wire dLayout :=
  match i.val with
  | 0 => rOut40Layout ⟨15, lt40_15⟩
  | 1 => rScrCompact1493 ⟨M, revTmp_m0_lt hM5⟩
  | 2 => rOut40Layout ⟨1, lt40_1⟩
  | 3 => rScrCompact1493 ⟨M + 1, revTmp_m1_lt hM5⟩
  | 4 => rScrCompact1493 ⟨M + 3, revTmp_m3_lt hM5⟩
  | _ => rScrCompact1493 ⟨M + 4, revTmp_m4_lt hM5⟩
theorem revTmpWireFn_injective (M : ℕ) (hM5 : M + 5 ≤ 361) :
    Function.Injective (revTmpWireFn M hM5) := fun a b e ↦ by
  fin_cases a <;> fin_cases b <;> dsimp only [revTmpWireFn] at e <;> first
    | rfl
    | exact absurd e (rScr_ne_rOut40 _ _)
    | exact absurd e.symm (rScr_ne_rOut40 _ _)
    | exact absurd (congrArg Fin.val (rOut40Layout.wires.injective e)) (by
        dsimp only
        omega)
    | exact absurd (congrArg Fin.val (rScrCompact1493.wires.injective e)) (by
        dsimp only
        omega)
def rRevTmp (M : ℕ) (hM5 : M + 5 ≤ 361) : QRegister 6 dLayout :=
  ⟨⟨revTmpWireFn M hM5, revTmpWireFn_injective M hM5⟩⟩
/-- First-pass `32`-wire output subregister of `rOut40Layout`. -/
def outMid32WireFn (j : Fin 32) : Wire dLayout := rOut40Layout ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
theorem outMid32WireFn_injective : Function.Injective outMid32WireFn := fun _ _ e ↦
    mid32OutIdx_injective (congrArg Fin.val (rOut40Layout.wires.injective e))
def rOutMid32 : QRegister 32 dLayout := ⟨⟨outMid32WireFn, outMid32WireFn_injective⟩⟩
/-- Second-pass `5`-wire tail output subregister of `rOut40Layout` (`[15, 1, 33, 14, 0]`). -/
def outTail5WireFn (s : Fin 5) : Wire dLayout := rOut40Layout ⟨tail5OutIdx s, tail5OutIdx_lt40 s⟩
theorem outTail5WireFn_injective : Function.Injective outTail5WireFn := fun _ _ e ↦
    tail5OutIdx_injective (congrArg Fin.val (rOut40Layout.wires.injective e))
def rOutTail5 : QRegister 5 dLayout := ⟨⟨outTail5WireFn, outTail5WireFn_injective⟩⟩
/--
`(49 + M)`-wire First-pass predictor register (`0 = wOne`, `1..41 = coin`, `42..41+M = work`,
`42+M..46+M = rOutTail5`, `47+M..48+M = tmp0, tmp1`), pure `Bool` branching.
-/
def midPredWireFn (M : ℕ) (hM5 : M + 5 ≤ 361) (u : Fin (49 + M)) : Wire dLayout :=
    if u.val == 0 then rScrCompact1493 ⟨M + 2, midPred_m2_lt hM5⟩ else if Nat.ble (u.val +
    1) 42 then rOuter41Layout ⟨(u.val - 1) % 41, midPred_coin_lt u⟩ else if Nat.ble (u.val + 1)
    (42 + M) then rScrCompact1493 ⟨u.val - 42, midPred_work_lt_all hM5 u⟩ else if Nat.ble (u.val +
    1) (47 + M) then rOutTail5 ⟨(u.val - (42 + M)) % 5, midPred_tail_lt u⟩ else rScrCompact1493 ⟨M +
    3 + (u.val - (47 + M)), midPred_tmp_lt hM5 u⟩
theorem midPredWireFn_injective (M : ℕ) (hM5 : M + 5 ≤ 361) :
    Function.Injective (midPredWireFn M hM5) := fun a b e ↦ by
  have hc (u : Fin (49 + M)) :
      (∃ k : Fin 1493, midPredWireFn M hM5 u = rScrCompact1493 k ∧
        ((u.val = 0 ∧ k.val = M + 2) ∨ (42 ≤ u.val ∧ u.val < 42 + M ∧ k.val = u.val - 42) ∨
          (47 + M ≤ u.val ∧ k.val = M + 3 + (u.val - (47 + M))))) ∨
      (1 ≤ u.val ∧ u.val < 42 ∧ midPredWireFn M hM5 u = rOuter41Layout ⟨(u.val - 1) % 41,
          midPred_coin_lt u⟩) ∨
      (42 + M ≤ u.val ∧ u.val < 47 + M ∧
        midPredWireFn M hM5 u = rOutTail5 ⟨(u.val - (42 + M)) % 5, midPred_tail_lt u⟩) := by
    dsimp only [midPredWireFn]
    if h0 : (u.val == 0) = true then
      rw [ite_eq_left h0]
      exact .inl ⟨_, rfl, .inl ⟨beq_iff_eq.mp h0, rfl⟩⟩
    else
      rw [ite_eq_right h0]
      if h1 : Nat.ble (u.val + 1) 42 = true then
        rw [ite_eq_left h1]
        exact .inr (.inl ⟨Nat.pos_of_ne_zero fun z ↦ h0 (beq_iff_eq.mpr z),
          Nat.le_of_ble_eq_true h1, rfl⟩)
      else
        rw [ite_eq_right h1]
        if h2 : Nat.ble (u.val + 1) (42 + M) = true then
          rw [ite_eq_left h2]
          exact .inl ⟨_, rfl,
            .inr (.inl ⟨Nat.le_of_not_lt fun l ↦ h1 (Nat.ble_eq_true_of_le l),
              Nat.le_of_ble_eq_true h2, rfl⟩)⟩
        else
          rw [ite_eq_right h2]
          if h3 : Nat.ble (u.val + 1) (47 + M) = true then
            rw [ite_eq_left h3]
            exact .inr (.inr ⟨Nat.le_of_not_lt fun l ↦ h2 (Nat.ble_eq_true_of_le l),
              Nat.le_of_ble_eq_true h3, rfl⟩)
          else
            rw [ite_eq_right h3]
            exact .inl ⟨_, rfl,
              .inr (.inr ⟨Nat.le_of_not_lt fun l ↦ h3 (Nat.ble_eq_true_of_le l), rfl⟩)⟩
  rcases hc a with ⟨ka, ea, ha⟩ | ⟨ha1, ha2, ea⟩ | ⟨ha1, ha2, ea⟩ <;>
    rcases hc b with ⟨kb, eb, hb⟩ | ⟨hb1, hb2, eb⟩ | ⟨hb1, hb2, eb⟩
  · have h : ka.val = kb.val :=
        congrArg Fin.val (rScrCompact1493.wires.injective (ea.symm.trans (e.trans eb)))
    rcases ha with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;> rcases hb with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;>
        exact Fin.ext (by omega)
  · exact absurd (ea.symm.trans (e.trans eb)) (rScr_ne_rOuter41 _ _)
  · exact absurd (ea.symm.trans (e.trans eb)) (rScr_ne_rOut40 _ _)
  · exact absurd (eb.symm.trans (e.symm.trans ea)) (rScr_ne_rOuter41 _ _)
  · have h := congrArg Fin.val (rOuter41Layout.wires.injective (ea.symm.trans (e.trans eb)))
    have la : a.val - 1 < 41 := by omega
    have lb : b.val - 1 < 41 := by omega
    dsimp only at h
    rw [Nat.mod_eq_of_lt la, Nat.mod_eq_of_lt lb] at h
    exact Fin.ext (by omega)
  · exact absurd (ea.symm.trans (e.trans eb)) (rOuter41_ne_rOut40 _ _)
  · exact absurd (eb.symm.trans (e.symm.trans ea)) (rScr_ne_rOut40 _ _)
  · exact absurd (eb.symm.trans (e.symm.trans ea)) (rOuter41_ne_rOut40 _ _)
  · have h := congrArg Fin.val (rOutTail5.wires.injective (ea.symm.trans (e.trans eb)))
    have la : a.val - (42 + M) < 5 := by omega
    have lb : b.val - (42 + M) < 5 := by omega
    dsimp only at h
    rw [Nat.mod_eq_of_lt la, Nat.mod_eq_of_lt lb] at h
    exact Fin.ext (by omega)
def rMidPred (M : ℕ) (hM5 : M + 5 ≤ 361) : QRegister (49 + M) dLayout :=
  ⟨⟨midPredWireFn M hM5, midPredWireFn_injective M hM5⟩⟩
/-- `(47 + M)`-wire Second-pass predictor register (`0..46+M` prefix of `rMidPred`). -/
abbrev rTailPred (M : ℕ) (hM5 : M + 5 ≤ 361) : QRegister (47 + M) dLayout :=
    (rMidPred M hM5).compose (QRegister.block 0 (47 + M) (tailPred_blk_le M))
theorem disj_rRevCore_rOutMid32 (M : ℕ) (hM5 : M + 5 ≤ 361) :
    (rRevCore M hM5).DisjointWires rOutMid32 :=
  disj_of_ne fun i j ↦ by
    change revCoreWireFn M hM5 i ≠ rOut40Layout ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
    dsimp only [revCoreWireFn]
    split_ifs <;>
        first | exact rOuter41_ne_rOut40 _ _ | exact rScr_ne_rOut40 _ _
theorem disj_rRevCore_rOutTail5 (M : ℕ) (hM5 : M + 5 ≤ 361) :
    (rRevCore M hM5).DisjointWires rOutTail5 :=
  disj_of_ne fun i s ↦ by
    change revCoreWireFn M hM5 i ≠ rOut40Layout ⟨tail5OutIdx s, tail5OutIdx_lt40 s⟩
    dsimp only [revCoreWireFn]
    split_ifs <;>
        first | exact rOuter41_ne_rOut40 _ _ | exact rScr_ne_rOut40 _ _
theorem disj_rRevTmp_rOutMid32 (M : ℕ) (hM5 : M + 5 ≤ 361) :
    (rRevTmp M hM5).DisjointWires rOutMid32 :=
  disj_of_ne fun i j ↦ by
    change revTmpWireFn M hM5 i ≠ rOut40Layout ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
    fin_cases i <;> dsimp only [revTmpWireFn] <;> first
      | exact rScr_ne_rOut40 _ _
      | exact fun e ↦ mid32_ne_tail5 j 0 (congrArg Fin.val (rOut40Layout.wires.injective e)).symm
      | exact fun e ↦ mid32_ne_tail5 j 1 (congrArg Fin.val (rOut40Layout.wires.injective e)).symm
theorem disj_rMidPred_rOutMid32 (M : ℕ) (hM5 : M + 5 ≤ 361) :
    (rMidPred M hM5).DisjointWires rOutMid32 :=
  disj_of_ne fun u j ↦ by
    change midPredWireFn M hM5 u ≠ rOut40Layout ⟨mid32OutIdx j, mid32OutIdx_lt40 j⟩
    dsimp only [midPredWireFn]
    if h0 : (u.val == 0) = true then
      rw [ite_eq_left h0]
      exact rScr_ne_rOut40 _ _
    else
      rw [ite_eq_right h0]
      if h1 : Nat.ble (u.val + 1) 42 = true then
        rw [ite_eq_left h1]
        exact rOuter41_ne_rOut40 _ _
      else
        rw [ite_eq_right h1]
        if h2 : Nat.ble (u.val + 1) (42 + M) = true then
          rw [ite_eq_left h2]
          exact rScr_ne_rOut40 _ _
        else
          rw [ite_eq_right h2]
          if h3 : Nat.ble (u.val + 1) (47 + M) = true then
            rw [ite_eq_left h3]
            exact fun e ↦ mid32_ne_tail5 j ⟨(u.val - (42 + M)) % 5, mod5_lt _⟩
              (congrArg Fin.val (rOut40Layout.wires.injective e)).symm
          else
            rw [ite_eq_right h3]
            exact rScr_ne_rOut40 _ _
theorem rTailPred_ne_rOutTail5_of_lt (M : ℕ) (hM5 : M + 5 ≤ 361) (s : Fin 5)
    (u : Fin (47 + M)) (hu : u.val < 42 + M + s.val) : rTailPred M hM5 u ≠ rOutTail5 s := by
  let u' : Fin (49 + M) := ⟨u.val, by omega⟩
  have hu0 : rTailPred M hM5 u = midPredWireFn M hM5 u' :=
    congrArg (midPredWireFn M hM5) (Fin.ext (Nat.zero_add u.val))
  rw [hu0]
  dsimp only [midPredWireFn]
  if h0 : (u'.val == 0) = true then
    rw [ite_eq_left h0]
    exact rScr_ne_rOut40 _ _
  else
    rw [ite_eq_right h0]
    if h1 : Nat.ble (u'.val + 1) 42 = true then
      rw [ite_eq_left h1]
      exact rOuter41_ne_rOut40 _ _
    else
      rw [ite_eq_right h1]
      if h2 : Nat.ble (u'.val + 1) (42 + M) = true then
        rw [ite_eq_left h2]
        exact rScr_ne_rOut40 _ _
      else
        rw [ite_eq_right h2, ite_eq_left (Nat.ble_eq_true_of_le u.isLt)]
        exact fun e ↦ by
          have h := congrArg Fin.val (rOutTail5.wires.injective e)
          have _ : ¬u.val < 42 + M := fun l ↦ h2 (Nat.ble_eq_true_of_le l)
          have hlt : u.val - (42 + M) < 5 := by omega
          dsimp only [u'] at h
          rw [Nat.mod_eq_of_lt hlt] at h
          omega
open PhotochemistrySolution.CoinWrap PhotochemistrySolution.Stage1SingleWrap
  PhotochemistrySolution.Stage1Opt41Single
open PhotochemistrySolution.Stage1Opt41TwoWrap
theorem coreXag_le (M : ℕ) : 0 + (41 + (M + 2)) ≤ 41 + (M + 3) := by omega
theorem corePre_le (M : ℕ) : 0 + (41 + M) ≤ 41 + (M + 3) := by omega
theorem coreM0_lt (M : ℕ) : 41 + M < 41 + (M + 3) := by omega
theorem coreM1_lt (M : ℕ) : 42 + M < 41 + (M + 3) := by omega
theorem coreOne_lt (M : ℕ) : 43 + M < 41 + (M + 3) := by omega
theorem self_le_nat (M : ℕ) : M ≤ M := le_rfl
theorem corePre_width_le (M : ℕ) : 41 + M ≤ 41 + M := le_rfl
abbrev rCoreXag (M : ℕ) : QRegister (41 + (M + 2)) (41 + (M + 3)) :=
    QRegister.block 0 (41 + (M + 2)) (coreXag_le M)
abbrev rCorePre (M : ℕ) : QRegister (41 + M) (41 + (M + 3)) :=
    QRegister.block 0 (41 + M) (corePre_le M)
def wCoreM0 (M : ℕ) : Wire (41 + (M + 3)) := ⟨41 + M, coreM0_lt M⟩
def wCoreM1 (M : ℕ) : Wire (41 + (M + 3)) := ⟨42 + M, coreM1_lt M⟩
def wCoreOne (M : ℕ) : Wire (41 + (M + 3)) := ⟨43 + M, coreOne_lt M⟩
theorem disj_corePre_M0 (M : ℕ) (i : Fin (41 + M)) : rCorePre M i ≠ wCoreM0 M :=
  mt (congrArg Fin.val) (show 0 + i.val ≠ 41 + M by omega)
theorem disj_corePre_M1 (M : ℕ) (i : Fin (41 + M)) : rCorePre M i ≠ wCoreM1 M :=
  mt (congrArg Fin.val) (show 0 + i.val ≠ 42 + M by omega)
theorem sXag_self_empty (M : ℕ) : sXag M M = ∅ := Finset.ext fun _ ↦ by
  simp only [sXag, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, not_exists, not_and]
  omega
/--
Reverse core `ComputeProg`: runs `compileXag M coreGates`, computes `coreMask0` into `41 + M`
and `coreMask1` into `42 + M`, and toggles `43 + M` (`wOne`) to `1` (`M` `TempAND`s total).
-/
def cpRevCore (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (coreMask0 coreMask1 : ℕ) : ComputeProg (41 +
    (M + 3)) :=
  let p0 := mapCPSW (rCoreXag M) (compileXag M coreGates M (self_le_nat M));
  let p1 :=
      qXorMask1 (rCorePre M) (wCoreM0 M) (disj_corePre_M0 M) coreMask0 (41 + M)
      (corePre_width_le M); let p2 :=
                              qXorMask1 (rCorePre M) (wCoreM1 M) (disj_corePre_M1 M) coreMask1 (41 +
                              M) (corePre_width_le M)
  .seq (.seq (.seq p0 p1) p2) (.x (wCoreOne M))
theorem fwdBits_cpRevCore (M : ℕ) (coreGates : Fin M → ℕ × ℕ) (coreMask0 coreMask1 : ℕ)
    (c : Fin (2 ^ 41)) (α : BitAssignment (41 + (M + 3)))
    (hc : ∀ k : Fin 41, α ⟨k.val, by omega⟩ = if c.val.testBit k.val then 1 else 0)
    (hz : ∀ k : Fin (M + 3), α ⟨41 + k.val, by omega⟩ = 0) :
    let env := xagEnv c.val M coreGates M le_rfl;
    let β := (cpRevCore M coreGates coreMask0 coreMask1).fwdBits α
    (∀ u : Fin (41 + M), β ⟨u.val, by omega⟩ = if env.testBit (1 + u.val) then 1 else 0) ∧
    β (wCoreM0 M) = (if oddBits (env &&& coreMask0) (42 + M) then 1 else 0) ∧
    β (wCoreM1 M) = (if oddBits (env &&& coreMask1) (42 + M) then 1 else 0) ∧
    β (wCoreOne M) = 1 := by
  let env := xagEnv c.val M coreGates M le_rfl
  obtain ⟨he0, _, heB⟩ := xagEnv_invariant c M coreGates M le_rfl
  have hInitEq : (fun k : Fin (41 + (M + 2)) ↦ α (rCoreXag M k)) = coinInitBits (M + 2) c :=
      funext fun k ↦ by
    dsimp only [coinInitBits]
    if hk : k.val < 41 then
      rw [ifp_tw hk]
      exact (congrArg α (Fin.ext (Nat.zero_add k.val))).trans (hc ⟨k.val, hk⟩)
    else
      rw [ifn_tw hk]
      exact (congrArg α (Fin.ext (by
          simp only [QRegister.block_apply_val]
          omega))).trans
            (hz ⟨k.val - 41, by omega⟩)
  let p0 := mapCPSW (rCoreXag M) (compileXag M coreGates M (self_le_nat M))
  let β0 := p0.fwdBits α
  have hβ0_xag : ∀ i : Fin (41 + (M + 2)),
      β0 ⟨i.val, by omega⟩ = if i.val < 41 +
          M then (if env.testBit (1 + i.val) then 1 else 0) else 0 := fun i ↦
    (congrArg β0 (Fin.ext (Nat.zero_add i.val)).symm).trans
      ((fwdBits_mapCPSW_inside (rCoreXag M) _ α i).trans (by
        rw [hInitEq]
        exact heB i))
  have hβ0_one : β0 (wCoreOne M) = 0 :=
    (fwdBits_mapCPSW_outside (rCoreXag M) _ α fun i e ↦ by
      have hv :=
          congrArg Fin.val e
      simp only [QRegister.block_apply_val, wCoreOne] at hv
      omega).trans
      ((congrArg α (Fin.ext (by
        simp only [wCoreOne]
        omega))).trans (hz ⟨M + 2, by omega⟩))
  have hPreBits : ∀ u : Fin (41 + M), β0 (rCorePre M u) = if env.testBit (1 +
      u.val) then 1 else 0 := fun u ↦ by
    rw [show rCorePre M u = ⟨u.val, by omega⟩ from Fin.ext (Nat.zero_add u.val), hβ0_xag ⟨u.val,
        by omega⟩, ifp_tw u.isLt]
  have hp0 := maskParity_eq_oddBits coreMask0 env _ he0 hPreBits (41 + M) (corePre_width_le M)
  have hp1 := maskParity_eq_oddBits coreMask1 env _ he0 hPreBits (41 + M) (corePre_width_le M)
  rw [show 1 + (41 + M) = 42 + M by omega] at hp0 hp1
  let p1 :=
      qXorMask1 (rCorePre M) (wCoreM0 M) (disj_corePre_M0 M) coreMask0 (41 + M) (corePre_width_le M)
  let p2 :=
      qXorMask1 (rCorePre M) (wCoreM1 M) (disj_corePre_M1 M) coreMask1 (41 + M) (corePre_width_le M)
  let β1 := p1.fwdBits β0
  have h0_m0 : β0 (wCoreM0 M) = 0 :=
      (hβ0_xag ⟨41 + M, by omega⟩).trans (ifn_tw (by
        dsimp only
        omega))
  have h0_m1 : β0 (wCoreM1 M) = 0 :=
      (hβ0_xag ⟨42 + M, by omega⟩).trans (ifn_tw (by
        dsimp only
        omega))
  have s1 : β1 = Function.update β0 (wCoreM0 M) (if oddBits (env &&& coreMask0)
      (42 + M) then 1 else 0) := by
    dsimp only [β1, p1]
    rw [fwdBits_qXorMask1, hp0, h0_m0, zero_add]
  have uNe {f : BitAssignment (41 + (M + 3))} {a b v} (h : b.val ≠ a.val) :
      Function.update f a v b = f b := Function.update_of_ne (mt (congrArg Fin.val) h) v f
  let β2 := p2.fwdBits β1
  have s2 : β2 = Function.update β1 (wCoreM1 M) (if oddBits (env &&& coreMask1)
      (42 + M) then 1 else 0) := by
    dsimp only [β2, p2]
    rw [fwdBits_qXorMask1, show (fun u ↦ β1 (rCorePre M u)) = fun u ↦
        β0 (rCorePre M u) from
      funext fun u ↦ by rw [s1, Function.update_of_ne (disj_corePre_M0 M u)], hp1,
      s1, uNe (by
        dsimp only [wCoreM0, wCoreM1]
        omega), h0_m1, zero_add]
  let β := Function.update β2 (wCoreOne M) (β2 (wCoreOne M) + 1)
  change (∀ u : Fin (41 + M), β ⟨u.val, _⟩ = _) ∧ β (wCoreM0 M) = _ ∧ β (wCoreM1 M) = _ ∧
      β (wCoreOne M) = 1
  dsimp only [β]
  exact ⟨fun u ↦ by
      rw [uNe (by
        dsimp only [wCoreOne]
        omega), s2, uNe (by
        dsimp only [wCoreM1]
        omega),
        s1, uNe (by
          dsimp only [wCoreM0]
          omega)]
      exact (hβ0_xag ⟨u.val, by omega⟩).trans (ifp_tw u.isLt),
    by rw [uNe (by
      dsimp only [wCoreM0, wCoreOne]
      omega), s2,
         uNe (by
           dsimp only [wCoreM0, wCoreM1]
           omega),
        s1, Function.update_self],
    by rw [uNe (by
      dsimp only [wCoreM1, wCoreOne]
      omega), s2, Function.update_self],
    by rw [Function.update_self, s2, uNe (by
      dsimp only [wCoreOne, wCoreM1]
      omega),
        s1, uNe (by
          dsimp only [wCoreOne, wCoreM0]
          omega), hβ0_one, zero_add]⟩
theorem lt6_0 : 0 < 6 := by decide
theorem lt6_1 : 1 < 6 := by decide
theorem lt6_2 : 2 < 6 := by decide
theorem lt6_3 : 3 < 6 := by decide
theorem lt6_4 : 4 < 6 := by decide
theorem lt6_5 : 5 < 6 := by decide
abbrev w6_0 : Wire 6 := ⟨0, lt6_0⟩
abbrev w6_1 : Wire 6 := ⟨1, lt6_1⟩
abbrev w6_2 : Wire 6 := ⟨2, lt6_2⟩
abbrev w6_3 : Wire 6 := ⟨3, lt6_3⟩
abbrev w6_4 : Wire 6 := ⟨4, lt6_4⟩
abbrev w6_5 : Wire 6 := ⟨5, lt6_5⟩
theorem ne6_01 : w6_0 ≠ w6_1 := by decide
theorem ne6_04 : w6_0 ≠ w6_4 := by decide
theorem ne6_14 : w6_1 ≠ w6_4 := by decide
theorem ne6_23 : w6_2 ≠ w6_3 := by decide
theorem ne6_25 : w6_2 ≠ w6_5 := by decide
theorem ne6_35 : w6_3 ≠ w6_5 := by decide
def sRevTmp : Finset (Wire 6) := {w6_4, w6_5}
/-- `2`-`TempAND` First-pass helper computing `w0 * w1` into `w4` and `w2 * w3` into `w5`. -/
def cpRevTmp : ComputeProg 6 :=
    .seq (.andGate w6_0 w6_1 w6_4 ne6_01 ne6_04 ne6_14)
    (.andGate w6_2 w6_3 w6_5 ne6_23 ne6_25 ne6_35)
theorem cpRevTmp_spec : cpRevTmp.numAnd = 2 ∧ cpRevTmp.ValidProg ∅ sRevTmp :=
    ⟨rfl,
    by
      dsimp only [cpRevTmp, sRevTmp, ComputeProg.ValidProg, ComputeProg.finalClean]
      decide⟩
theorem fwdBits_cpRevTmp (α : BitAssignment 6) (h4 : α w6_4 = 0)
    (h5 : α w6_5 = 0) : cpRevTmp.fwdBits α w6_0 = α w6_0 ∧ cpRevTmp.fwdBits α w6_1 = α w6_1 ∧
    cpRevTmp.fwdBits α w6_2 = α w6_2 ∧ cpRevTmp.fwdBits α w6_3 = α w6_3 ∧ cpRevTmp.fwdBits α w6_4 =
    α w6_0 * α w6_1 ∧ cpRevTmp.fwdBits α w6_5 = α w6_2 * α w6_3 := by
  dsimp only [cpRevTmp, ComputeProg.fwdBits]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by decide)])) <;>
    simp only [h4, h5, zero_add]
end QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
namespace QuantumComputation.Specs.PhotochemistrySolution.CoulombFast

open Operator QProg Matrix Circuit Qubit PhotochemistrySolution
  PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.ZeroNEremCsa36Kick
  PhotochemistrySolution.BandEnc12Sync PhotochemistrySolution.FineLegendre
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep (WirePair
    czPairsCircuit xUnloadChunkCzPairsSeqDyn)
/-- Total output-wire indexer on `QRegister B n` (`0` typeclasses). -/
def outWireOfReg {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n) (j : ℕ) : Wire n :=
    rOut ⟨j % B, Nat.mod_lt j hB⟩
theorem circWires_czPairs {n : ℕ} {S : Wire n → Prop} (pairs : List (WirePair n))
    (h : ∀ p ∈ pairs, S p.1 ∧ S p.2.1) : CircWires S (czPairsCircuit pairs) :=
    Dist18QuadUnld.circWires_czPairs_quad pairs h
theorem dynWires_xUnloadChunk {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (rOut : ℕ → Wire n)
    (ofs : ℕ)
    (pairsFn : ℕ → List (WirePair n)) (hOut : ∀ i, S (rOut i))
        (hPairs : ∀ j p, p ∈ pairsFn j → S p.1 ∧ S p.2.1) (k : ℕ) :
    DynWires S (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn (.circuit .identity) k) :=
  Dist18QuadUnld.dynWires_xUnloadChunk_quad v rOut ofs pairsFn hOut hPairs k
/-- Prefix update writing `g i` onto `outWireOfReg hB rOut i` for `i < k`. -/
def updPrefix {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n)
    (β : BitAssignment n) (g : ℕ → ZMod 2) : ℕ → BitAssignment n
  | 0 => β
  | k + 1 => Function.update (updPrefix hB rOut β g k) (outWireOfReg hB rOut k) (g k)
theorem updPrefix_eq_writeReg {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n) (β : BitAssignment n)
    (g : ℕ → ZMod 2) : updPrefix hB rOut β g B = writeReg β rOut (fun j ↦ g j.val) := by
  rw [← PhotochemistrySolution.Dist18QuadUnld.updPrefixQuad_eq_writeReg]
  exact Nat.rec (motive := fun k ↦ updPrefix hB rOut β g k =
      Dist18QuadUnld.updPrefixQuad hB rOut β g k) rfl
    (fun _ ih ↦ by simp [updPrefix, outWireOfReg, Dist18QuadUnld.updPrefixQuad,
      PhotochemistrySolution.Dist18QuadUnld.outWireOfRegQuad, ih]) B
theorem projBit_zero_mkKetOpW {W n : ℕ} [NeZero (2 ^ n)] (rWork : QRegister W n) (q : Wire n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (hq0 : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → st δ q = 0) :
    projBit q 0 * mkKetOpW rWork st ph = mkKetOpW rWork st ph :=
  PhotochemistrySolution.Dist18QuadUnld.projBit_zero_mkKetOpW_quad rWork q st ph hq0
theorem getCT_loadCols_on :
    ∀ (k off : ℕ) (cs : List ℕ) (ct : CT) (u : ℕ),
      off + k ≤ 128 → u < 128 →
      (∀ j < k, getCT 7 ct (off + j) = 0) →
      getCT 7 (loadCols k off cs ct) u =
        if off ≤ u ∧ u < off + k then cs.getD (u - off) 0 else getCT 7 ct u
  | 0, _, _, _, _, _, _, _ => by
      simp only [loadCols]
      exact (ite_eq_right (by omega)).symm
  | k + 1, off, cs, ct, u, hk, hu, hz => by
      simp only [loadCols, xorStrict_eq]
      rw [getCT_xorCT 7 _ u (off + k) (cs.getD k 0) (by omega) (by omega),
        getCT_loadCols_on k off cs ct u (by omega) hu (fun j hj ↦ hz j (by omega))]
      rcases eq_or_ne (off + k) u with rfl | hku
      · simp [hz k (by omega), show off + k - off = k by omega]
      · simp [hku, show (off ≤ u ∧ u < off + (k + 1)) ↔ (off ≤ u ∧ u < off + k) by omega]
end QuantumComputation.Specs.PhotochemistrySolution.CoulombFast

namespace QuantumComputation.Specs.PhotochemistrySolution.Unshift32Bf84
open Qubit PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18 (testBit_xor_shift1)
theorem cond_shift_lo_same (c0 d t w : ℕ) (p : Bool) (hdw : d.testBit w = false) :
    ((if p then (c0 ^^^ d) ^^^ (1 <<< t) else c0 ^^^ d) ^^^ (if p then c0 ^^^ (1 <<<
        t) else c0)).testBit w = false := by
  cases p <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_xor, hdw] <;>
    cases (1 <<< t).testBit w <;> cases c0.testBit w <;> rfl
theorem cond_shift_lo_ge8 (c0 d t w : ℕ) (p1 p2 : Bool) (htw : t ≠ w) (hdw : d.testBit w = false) :
    ((if p1 then (c0 ^^^ d) ^^^ (1 <<< t) else c0 ^^^ d) ^^^ (if p2 then c0 ^^^ (1 <<<
        t) else c0)).testBit w = false := by
  rw [Nat.testBit_xor]
  cases p1 <;> cases p2 <;> simp only [↓reduceIte, Bool.false_eq_true, testBit_xor_shift1] <;>
      simp [htw, Nat.testBit_xor, hdw]
theorem xor4_cond_shift (c0 d1 d2 t : ℕ) (p12 p0 p1 p2 : Bool) (hp : p12 = xor p0 (xor p1 p2)) :
    (if p12 then (c0 ^^^ d1 ^^^ d2) ^^^ (1 <<< t) else (c0 ^^^ d1 ^^^ d2)) =
      (if p0 then c0 ^^^ (1 <<< t) else c0) ^^^ (if p1 then (c0 ^^^ d1) ^^^ (1 <<<
          t) else (c0 ^^^ d1)) ^^^
        (if p2 then (c0 ^^^ d2) ^^^ (1 <<< t) else (c0 ^^^ d2)) :=
  hp ▸ Nat.eq_of_testBit_eq fun k ↦ by
    cases p0 <;> cases p1 <;> cases p2 <;>
      simp only [↓reduceIte, Bool.false_eq_true, Bool.xor_true, Bool.xor_false,
        Bool.not_true, Bool.not_false, Nat.testBit_xor] <;>
      cases (1 <<< t).testBit k <;> cases c0.testBit k <;> cases d1.testBit k <;>
          cases d2.testBit k <;> rfl
theorem and_xor4_bool (en b0 b1 b2 : Bool) : (en && xor (xor b0 b1) b2) = xor (en && b0)
    (xor (en && xor b0 b1) (en && xor b0 b2)) := by
  cases en <;> cases b0 <;> cases b1 <;> cases b2 <;> rfl
def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allLt n p && p n
theorem allLt_spec : ∀ {n : ℕ} {p : ℕ → Bool}, allLt n p = true → ∀ i < n, p i = true
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, _, h, i, hi =>
      let ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      if hin : i = n then hin ▸ h2 else allLt_spec h1 i (by omega)
end QuantumComputation.Specs.PhotochemistrySolution.Unshift32Bf84

namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open PhotochemistrySolution
/-- Pairwise disjointness of `(wG, rIdx7, rK4, rJ2, rY36, rPool)` for `pGGatedInnerCore`. -/
abbrev GGatedCoreDisj {M n : ℕ} (wG : Wire n) (rIdx7 : QRegister 7 n) (rK4 : QRegister 4 n)
    (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n) (rPool : QRegister M n) : Prop :=
    (∀ i, wG ≠ rIdx7 i) ∧ (∀ i, wG ≠ rK4 i) ∧ (∀ i, wG ≠ rJ2 i) ∧ (∀ b, wG ≠ rY36 b) ∧
    (∀ u, wG ≠ rPool u) ∧ rIdx7.DisjointWires rK4 ∧ rIdx7.DisjointWires rJ2 ∧
    rIdx7.DisjointWires rY36 ∧ rIdx7.DisjointWires rPool ∧ rK4.DisjointWires rJ2 ∧
    rK4.DisjointWires rY36 ∧ rK4.DisjointWires rPool ∧ rJ2.DisjointWires rY36 ∧
    rJ2.DisjointWires rPool ∧ rY36.DisjointWires rPool
theorem ggCore_YP {M n : ℕ} {wG : Wire n} {rIdx7 : QRegister 7 n} {rK4 : QRegister 4 n}
    {rJ2 : QRegister 2 n} {rY36 : QRegister 36 n} {rPool : QRegister M n}
    (hd : GGatedCoreDisj wG rIdx7 rK4 rJ2 rY36 rPool) : rY36.DisjointWires rPool :=
    hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2
theorem ggCore_KY {M n : ℕ} {wG : Wire n} {rIdx7 : QRegister 7 n} {rK4 : QRegister 4 n}
    {rJ2 : QRegister 2 n} {rY36 : QRegister 36 n} {rPool : QRegister M n}
    (hd : GGatedCoreDisj wG rIdx7 rK4 rJ2 rY36 rPool) : rK4.DisjointWires rY36 :=
    hd.2.2.2.2.2.2.2.2.2.2.1
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine

open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.XMeasUnld
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.XMeasChunkQromUnld
  PhotochemistrySolution.SplitBellVecCleanStep PhotochemistrySolution.QubitizationWalkSem
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open scoped Circuit.Notation
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep (WirePair
    czPairsCircuit czPairsParity czPairsParity_indep cnotPairsCircuit count_cnotPairsCircuit
    xUnloadCzPairsSeqDyn count_xUnloadCzPairsSeqDyn subspaceStep_xUnloadCzPairsSeqDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CoulombFast (circWires_czPairs)
attribute [local semireducible] remeasureIf projBit chunkXorOp
theorem lt_of_ble_succ {a b : ℕ} (h : Nat.ble (a + 1) b = true) : a < b := Nat.le_of_ble_eq_true h
theorem lt_trans_ble {a b c : ℕ} (h1 : Nat.ble (a + 1) b = true) (h2 : Nat.ble (b + 1) c = true) :
    a < c := Nat.lt_trans (lt_of_ble_succ h1) (lt_of_ble_succ h2)
theorem fin_ne_of_ble {W a b : ℕ} (ha : a < W) (hb : b < W) (hab : Nat.ble (a + 1) b = true) :
    (⟨a, ha⟩ : Wire W) ≠ ⟨b, hb⟩ := fun e ↦ Nat.ne_of_lt (lt_of_ble_succ hab) (congrArg Fin.val e)
theorem fin_ne_of_beq_false {W a b : ℕ} (ha : a < W) (hb : b < W) (hne : (a == b) = false) :
    (⟨a, ha⟩ : Wire W) ≠ ⟨b, hb⟩ :=
  fun e ↦ Bool.noConfusion ((beq_iff_eq.mpr (congrArg Fin.val e)).symm.trans hne)
/-- Total lift of `(a < b < W)` index pairs onto `r : QRegister W n`. -/
def wirePairsOfReg {W n : ℕ} (r : QRegister W n) : List (ℕ × ℕ) → List (WirePair n)
  | [] => []
  | p :: ps =>
      match h1 : Nat.ble (p.1 + 1) p.2, h2 : Nat.ble (p.2 + 1) W with
      | true, true =>
          ⟨r ⟨p.1, lt_trans_ble h1 h2⟩,
            ⟨r ⟨p.2, lt_of_ble_succ h2⟩, r.wires.injective.ne (fin_ne_of_ble _ _ h1)⟩⟩ ::
            wirePairsOfReg r ps
      | _, _ => wirePairsOfReg r ps
/-- Total lift of `(a ≠ b, a < W, b < W)` CNOT pairs onto `r : QRegister W n`. -/
def cnotWirePairsOfReg {W n : ℕ} (r : QRegister W n) : List (ℕ × ℕ) → List (WirePair n)
  | [] => []
  | p :: ps =>
      match hne : p.1 == p.2, h1 : Nat.ble (p.1 + 1) W, h2 : Nat.ble (p.2 + 1) W with
      | false, true, true =>
          ⟨r ⟨p.1, lt_of_ble_succ h1⟩,
            ⟨r ⟨p.2, lt_of_ble_succ h2⟩, r.wires.injective.ne (fin_ne_of_beq_false _ _ hne)⟩⟩ ::
            cnotWirePairsOfReg r ps
      | _, _, _ => cnotWirePairsOfReg r ps
theorem wirePairsOfReg_mem_lt {W n : ℕ} (r : QRegister W n) {bound : ℕ} :
    ∀ (ps : List (ℕ × ℕ)), checkPairsBound bound ps = true →
      ∀ wp ∈ wirePairsOfReg r ps,
        (∃ u : Fin W, u.val < bound ∧ r u = wp.1) ∧ (∃ u : Fin W, u.val < bound ∧ r u = wp.2.1)
  | [], _, _, hmem => absurd hmem List.not_mem_nil
  | p :: ps, hchk, wp, hmem => by
      obtain ⟨⟨hp1, hp2⟩, hrest⟩ := by simpa only [checkPairsBound, Bool.and_eq_true] using hchk
      dsimp only [wirePairsOfReg] at hmem; split at hmem
      · rename_i h1 h2
        exact (List.mem_cons.mp hmem).elim
          (fun e ↦ e ▸ ⟨⟨⟨p.1, lt_trans_ble h1 h2⟩, lt_trans_ble hp1 hp2, rfl⟩,
            ⟨⟨p.2, lt_of_ble_succ h2⟩, lt_of_ble_succ hp2, rfl⟩⟩)
          (wirePairsOfReg_mem_lt r ps hrest wp)
      · exact wirePairsOfReg_mem_lt r ps hrest wp hmem
theorem z2_mul_add_ite (a b c : Bool) : ((if a then (1 : ZMod 2) else 0) * (if b then 1 else 0) +
    (if c then 1 else 0)) = if xor (a && b) c then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> decide
theorem czPairsParity_wirePairsOfReg {W n : ℕ} (r : QRegister W n) {bound : ℕ}
    (hbW : bound ≤ W) (bitOf : ℕ → Bool) (β : BitAssignment n)
    (hBit : ∀ u : Fin W, u.val < bound → β (r u) = if bitOf u.val then 1 else 0) :
    ∀ (ps : List (ℕ × ℕ)), checkPairsBound bound ps = true →
      czPairsParity (wirePairsOfReg r ps) β = if pairsParityBool bitOf ps then 1 else 0
  | [], _ => rfl
  | p :: ps, hchk => by
      obtain ⟨⟨hp1, hp2⟩, hrest⟩ := by simpa only [checkPairsBound, Bool.and_eq_true] using hchk
      have h2W := Nat.ble_eq_true_of_le (Nat.lt_of_lt_of_le (lt_of_ble_succ hp2) hbW)
      dsimp only [wirePairsOfReg]
      split
      · rename_i h1 h2
        rw [czPairsParity, pairsParityBool, hBit ⟨p.1, lt_trans_ble h1 h2⟩ (lt_trans_ble hp1 hp2),
          hBit ⟨p.2, lt_of_ble_succ h2⟩ (lt_of_ble_succ hp2),
              czPairsParity_wirePairsOfReg r hbW bitOf β hBit ps hrest]
        exact z2_mul_add_ite (bitOf p.1) (bitOf p.2) (pairsParityBool bitOf ps)
      · simp_all
/-- Exact 19-pair Stage-1 reverse `pre_cnots` list `(src, dst)` on `rOut40Layout`. -/
def preCnotRawPairs40 : List (ℕ × ℕ) :=
  [(1, 35), (15, 32), (1, 32), (0, 34), (14, 34),
   (24, 16), (25, 17), (26, 18), (27, 19), (28, 20), (29, 21), (30, 22), (31, 23),
   (8, 2), (9, 3), (10, 4), (11, 5), (12, 6), (13, 7)]
/-- `0-T` 19-CNOT pre-reduction circuit on `rOut : QRegister 40 n`. -/
def cPreCnot40 {n : ℕ} (rOut : QRegister 40 n) : Circuit n :=
    cnotPairsCircuit (cnotWirePairsOfReg rOut preCnotRawPairs40)
theorem count_cPreCnot40 {n : ℕ} (rOut : QRegister 40 n) : (cPreCnot40 rOut).count .T = 0 ∧
    (cPreCnot40 rOut).count .TOFF = 0 := count_cnotPairsCircuit _
theorem cnotWirePairsOfReg_mem {W n : ℕ} (r : QRegister W n) :
    ∀ (ps : List (ℕ × ℕ)) (wp : WirePair n), wp ∈ cnotWirePairsOfReg r ps →
      (∃ u : Fin W, r u = wp.1) ∧ (∃ u : Fin W, r u = wp.2.1)
  | [], _, hmem => absurd hmem List.not_mem_nil
  | _ :: ps, wp, hmem => by
      dsimp only [cnotWirePairsOfReg] at hmem; split at hmem
      · exact (List.mem_cons.mp hmem).elim (fun e ↦ e ▸ ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩)
            (cnotWirePairsOfReg_mem r ps wp)
      · exact cnotWirePairsOfReg_mem r ps wp hmem
theorem circWires_cnotPairs {n : ℕ} {S : Wire n → Prop} :
    ∀ (pairs : List (WirePair n)), (∀ p ∈ pairs, S p.1 ∧ S p.2.1) →
        CircWires S (cnotPairsCircuit pairs)
  | [], _ => trivial
  | p :: ps, hpAll =>
      let hp := hpAll p List.mem_cons_self
      ⟨fun i ↦ by fin_cases i <;> [exact hp.1; exact hp.2],
       circWires_cnotPairs ps (fun p' hp' ↦ hpAll p' (List.mem_cons_of_mem p hp'))⟩
theorem circWires_cPreCnot40 {n : ℕ} {S : Wire n → Prop} (rOut : QRegister 40 n)
    (hOut : ∀ u : Fin 40, S (rOut u)) : CircWires S (cPreCnot40 rOut) :=
  circWires_cnotPairs _ fun wp hmem ↦ by
    obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ :=
        cnotWirePairsOfReg_mem rOut preCnotRawPairs40 wp hmem; exact ⟨hu1 ▸ hOut u1, hu2 ▸ hOut u2⟩
def applyCnotPairs {n : ℕ} : List (WirePair n) → BitAssignment n → BitAssignment n
  | [], β => β
  | p :: ps, β => applyCnotPairs ps (Function.update β p.2.1 (β p.2.1 + β p.1))
theorem cnotPairsCircuit_mulVec_ket {n : ℕ} :
    ∀ (ps : List (WirePair n)) (β : BitAssignment n),
      (cnotPairsCircuit ps).eval.1.mulVec (ket β) = ket (applyCnotPairs ps β)
  | [], β =>
        by rw [cnotPairsCircuit, applyCnotPairs, Circuit.eval_identity, Submonoid.coe_one,
             Matrix.one_mulVec]
  | p :: ps, β =>
        by rw [cnotPairsCircuit, eval_seq_mulVec, ket_CNOT, cnotPairsCircuit_mulVec_ket ps]; rfl
def notSourceIn (t : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | q :: qs => Bool.not (q.1 == t) && notSourceIn t qs
def checkDisjCnotPairs (W : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: ps =>
      Bool.not (p.1 == p.2) && Nat.ble (p.1 + 1) W && Nat.ble (p.2 + 1) W &&
      notSourceIn p.2 ps && checkDisjCnotPairs W ps
def rawCnotXorSrcs (j : ℕ) : List (ℕ × ℕ) → (ℕ → Bool) → Bool
  | [], _ => false
  | p :: ps, f => xor (if p.2 == j then f p.1 else false) (rawCnotXorSrcs j ps f)
theorem rawCnotXorSrcs_congr_notSource (t j : ℕ) (f f' : ℕ → Bool) (heq : ∀ k, k ≠ t → f' k = f k) :
    ∀ (ps : List (ℕ × ℕ)), notSourceIn t ps = true → rawCnotXorSrcs j ps f' = rawCnotXorSrcs j ps f
  | [], _ => rfl
  | q :: qs, hns => by
      simp only [notSourceIn, Bool.and_eq_true] at hns
      dsimp only [rawCnotXorSrcs]
      rw [heq q.1 (fun e ↦ by simp [e] at hns),
        rawCnotXorSrcs_congr_notSource t j f f' heq qs hns.2]
theorem z2_add_ite_xor (a b : Bool) : ((if a then (1 : ZMod 2) else 0) + (if b then 1 else 0)) =
    if xor a b then 1 else 0 := by
  cases a <;> cases b <;> decide
theorem applyCnotPairs_cnotWirePairsOfReg {W n : ℕ} (r : QRegister W n) :
    ∀ (ps : List (ℕ × ℕ)), checkDisjCnotPairs W ps = true →
      ∀ (f : ℕ → Bool) (β : BitAssignment n),
      (∀ u : Fin W, β (r u) = if f u.val then 1 else 0) →
      (∀ w : Wire n, (∀ u : Fin W, w ≠ r u) → applyCnotPairs (cnotWirePairsOfReg r ps) β w = β w) ∧
      (∀ u : Fin W, applyCnotPairs (cnotWirePairsOfReg r ps) β (r u) =
        if xor (f u.val) (rawCnotXorSrcs u.val ps f) then 1 else 0)
  | [], _, f, β, hβ =>
        ⟨fun _ _ ↦ rfl, fun u ↦
        by simpa [cnotWirePairsOfReg, applyCnotPairs, rawCnotXorSrcs] using hβ u⟩
  | p :: ps, hchk, f, β, hβ => by
      obtain ⟨⟨⟨⟨_, hp1⟩, hp2⟩, hns⟩, hrest⟩ := by
        simpa only [checkDisjCnotPairs, Bool.and_eq_true] using hchk
      dsimp only [cnotWirePairsOfReg]
      split
      · rename_i _ h1 h2
        dsimp only [applyCnotPairs]
        let u2 : Fin W := ⟨p.2, lt_of_ble_succ h2⟩
        let f' : ℕ → Bool := fun k ↦ xor (f k) (if p.2 == k then f p.1 else false)
        obtain ⟨hout, hin⟩ := applyCnotPairs_cnotWirePairsOfReg r ps hrest f'
          (Function.update β (r u2) (β (r u2) + β (r ⟨p.1, lt_of_ble_succ h1⟩))) fun u ↦ by
          dsimp only [f']
          by_cases hu : u.val = p.2
          · rw [show u = u2 from Fin.ext hu, Function.update_self, hβ u2,
                hβ ⟨p.1, lt_of_ble_succ h1⟩, show u2.val = p.2 from rfl]
            simpa only [beq_self_eq_true, ↓reduceIte] using z2_add_ite_xor (f p.2) (f p.1)
          · simp only [Function.update_of_ne (r.wires.injective.ne (show u ≠
                u2 from Fin.ne_of_val_ne hu)),
              beq_false_of_ne (Ne.symm hu), Bool.false_eq_true, ↓reduceIte, Bool.xor_false, hβ u]
        refine ⟨fun w hw ↦ (hout w hw).trans (Function.update_of_ne (hw u2) _ _), fun u ↦ ?_⟩
        rw [hin u, rawCnotXorSrcs_congr_notSource p.2 u.val f f' (fun k hk ↦
            by simp [f', hk.symm]) ps hns]
        simp only [f', rawCnotXorSrcs, Bool.xor_assoc]
        exact if_congr Iff.rfl rfl rfl
      · simp_all
theorem checkDisjCnotPairs_preCnot40 : checkDisjCnotPairs 40 preCnotRawPairs40 = true := rfl
theorem rawCnotXorSrcs_preCnot40 (m : ℕ) (j : Fin 40) : xor (m.testBit j.val)
    (rawCnotXorSrcs j.val preCnotRawPairs40 m.testBit) = preCnotBit40 m j.val := by
  fin_cases j <;> (dsimp only [preCnotRawPairs40, rawCnotXorSrcs, preCnotBit40]; simp)
theorem cPreCnot40_mulVec_ket {n : ℕ} (rOut : QRegister 40 n) (m : ℕ) (β : BitAssignment n)
    (hβ : ∀ u : Fin 40, β (rOut u) = if m.testBit u.val then 1 else 0) :
    (cPreCnot40 rOut).eval.1.mulVec (ket β) = ket (DynCircExt.writeReg β rOut (fun u ↦
    if preCnotBit40 m u.val then 1 else 0)) := by
  rw [cPreCnot40, cnotPairsCircuit_mulVec_ket];
  obtain ⟨hout, hin⟩ :=
      applyCnotPairs_cnotWirePairsOfReg rOut preCnotRawPairs40 checkDisjCnotPairs_preCnot40
      m.testBit β hβ
  congr 1; funext w
  by_cases hw : ∃ u : Fin 40, rOut u = w
  · obtain ⟨u, rfl⟩ :=
        hw; rw [hin u, rawCnotXorSrcs_preCnot40 m u, DynCircExt.writeReg_apply_reg]
  · rw [hout w (fun u e ↦ hw ⟨u, e.symm⟩),
        DynCircExt.writeReg_apply_of_not_mem _ _ _ _ (by simpa [Set.mem_range] using hw)]
theorem subspaceStep_seq_trans {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {R₀ R₁ R₂ : Operator (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : SubspaceStep R₀ R₁ d₁) (h₂ : SubspaceStep R₁ R₂ d₂) :
    SubspaceStep R₀ R₂ (.seq d₁ d₂) := fun Obs ↦ by
  obtain ⟨M₁, hw₁, hm₁⟩ := h₂ Obs; obtain ⟨M₀, hw₀, hm₀⟩ := h₁ M₁
  exact ⟨M₀, (wp_seq_compile d₁ d₂ (fun _ ↦ Obs)).trans ((congrArg (wp d₁.compile) hw₁).trans hw₀),
      hm₁.trans hm₀⟩
/-- Optional pre-`X` toggle + `0-T` `CZ` Pauli-`X` measurement unloader on wire `q`. -/
def xUnloadCzPairsXSeqDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n) (preX : Bool)
    (pairs : List (WirePair n)) (rest : DynamicCircuit Var n) : DynamicCircuit Var n :=
  if preX then .seq (.circuit (.X q)) (xUnloadCzPairsSeqDyn v q pairs rest)
  else xUnloadCzPairsSeqDyn v q pairs rest
/-- Multi-wire `0-T` pre-`X` + `CZ` Pauli-`X` unloader across `j = k - 1, ..., 0`. -/
def xUnloadChunkCzPairsXSeqDyn {Var : Type} {n : ℕ}
    (v : Var) (rOut : ℕ → Wire n) (ofs : ℕ)
    (px : ℕ → Bool) (pf : ℕ → List (WirePair n))
    (rest : DynamicCircuit Var n) : ℕ → DynamicCircuit Var n
  | 0 => rest
  | j + 1 =>
      xUnloadCzPairsXSeqDyn v (rOut (ofs + j)) (px j) (pf j)
        (xUnloadChunkCzPairsXSeqDyn v rOut ofs px pf rest j)
theorem count_xUnloadChunkCzPairsXSeqDyn {Var : Type} {n : ℕ}
    (v : Var) (rOut : ℕ → Wire n) (ofs : ℕ)
    (px : ℕ → Bool) (pf : ℕ → List (WirePair n)) (rest : DynamicCircuit Var n) :
    ∀ k : ℕ,
      (xUnloadChunkCzPairsXSeqDyn v rOut ofs px pf rest k).count .T = rest.count .T ∧
      (xUnloadChunkCzPairsXSeqDyn v rOut ofs px pf rest k).count .TOFF = rest.count .TOFF
  | 0 => ⟨rfl, rfl⟩
  | j + 1 => by
      obtain ⟨ht_ih, hf_ih⟩ :=
          count_xUnloadChunkCzPairsXSeqDyn v rOut ofs px pf rest j; obtain ⟨ht, hf⟩ :=
          count_xUnloadCzPairsSeqDyn v (rOut (ofs + j)) (pf j)
          (xUnloadChunkCzPairsXSeqDyn v rOut ofs px pf rest j);
          dsimp only [xUnloadChunkCzPairsXSeqDyn, xUnloadCzPairsXSeqDyn]
      cases px j <;> simp [DynamicCircuit.count, Circuit.X, ht, hf, ht_ih, hf_ih]
theorem dynWires_xUnloadChunkX {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rOut : ℕ → Wire n) (ofs : ℕ)
    (px : ℕ → Bool) (pf : ℕ → List (WirePair n))
    (hOut : ∀ i, S (rOut i)) (hPairs : ∀ j p, p ∈ pf j → S p.1 ∧ S p.2.1) :
    ∀ k : ℕ, DynWires S (xUnloadChunkCzPairsXSeqDyn v rOut ofs px pf (.circuit .identity) k)
  | 0 => trivial
  | j + 1 => by
      have hd0 : DynWires S (xUnloadCzPairsSeqDyn v (rOut (ofs + j)) (pf j) _) :=
        ⟨fun _ ↦ hOut _, ⟨fun _ ↦ hOut _, ⟨fun _ ↦ hOut _, circWires_czPairs (pf j) (hPairs j)⟩,
            trivial⟩,
          dynWires_xUnloadChunkX v rOut ofs px pf hOut hPairs j⟩
      dsimp only [xUnloadChunkCzPairsXSeqDyn, xUnloadCzPairsXSeqDyn]
      cases px j
      · exact hd0
      · exact ⟨fun _ ↦ hOut _, hd0⟩
theorem x_mul_xorWireUnitary_add_one {n : ℕ} (q : Wire n) (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q a) = f β)
    (hg : ∀ β a, ((1 : ZMod 2) + f (Function.update β q a)) = (1 : ZMod 2) + f β) :
    (Circuit.X q).eval.1 * (xorWireUnitary q (fun β ↦ (1 : ZMod 2) + f β) hg).1 =
    (xorWireUnitary q f hf).1 := by
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, xorWireUnitary_mulVec_ket, ket_X, xorWireUnitary_mulVec_ket,
      Function.update_self,
      Function.update_idem]; refine congrArg ket (congrArg (Function.update β q) ?_)
  simp only [add_assoc, add_left_comm (1 : ZMod 2) (f β) 1, CharTwo.add_self_eq_zero, add_zero]
theorem subspaceStep_xUnloadChunkCzPairsXSeqDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (r : ℕ → Wire n) (o : ℕ)
    (px : ℕ → Bool) (pf : ℕ → List (WirePair n)) (bf : ℕ → BitAssignment n → ZMod 2)
    (hf : ∀ i β a, bf i (Function.update β (r (o + i)) a) = bf i β)
    (heq : ∀ i β, bf i β = (if px i then (1 : ZMod 2) else 0) + czPairsParity (pf i) β)
    (hdj : ∀ i, ∀ p ∈ pf i, p.1 ≠ r (o + i) ∧ p.2.1 ≠ r (o + i))
    (rest : DynamicCircuit Var n) (R Ro : Operator (2 ^ n)) (hr : SubspaceStep R Ro rest) :
    ∀ k : ℕ,
      (∀ a < k, ∀ b < k, a ≠ b → r (o + a) ≠ r (o + b)) →
      (∀ i < k, projBit (r (o + i)) 0 * R = R) →
      SubspaceStep (chunkXorOp r o bf hf k * R) Ro (xUnloadChunkCzPairsXSeqDyn v r o px pf rest k)
  | 0, _, _ => by simpa [chunkXorOp, xUnloadChunkCzPairsXSeqDyn] using hr
  | j + 1, hinj, hR0 => by
      have ih :=
          subspaceStep_xUnloadChunkCzPairsXSeqDyn v r o px pf bf hf heq hdj rest R Ro hr j
          (fun a ha b hb hab ↦ hinj a (Nat.lt_succ_of_lt ha) b (Nat.lt_succ_of_lt hb) hab)
          (fun i hi ↦ hR0 i (Nat.lt_succ_of_lt hi))
      let Rp := chunkXorOp r o bf hf j * R
      have hq : projBit (r (o + j)) 0 * Rp = Rp := by
        have h0 := hR0 j (Nat.lt_succ_self j); dsimp only [Rp, projBit] at h0 ⊢
        rw [← Matrix.mul_assoc, proj_zero_comm_chunkXorOp r o bf hf (r (o + j)) j (fun i hi ↦
            hinj i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_self j)
            (Nat.ne_of_lt hi)), Matrix.mul_assoc, h0]
      have hfcz := czPairsParity_indep (r (o + j)) (pf j) (hdj j)
      have s0 :=
          subspaceStep_xUnloadCzPairsSeqDyn v (r (o + j)) (pf j) _ _ hfcz (fun _ ↦ rfl) Rp Ro hq ih
      have hU_eq (g : BitAssignment n → ZMod 2) (hg : ∀ β a, g (Function.update β (r (o + j)) a) =
          g β)
          (hfg : ∀ β, bf j β = g β) : xorWireUnitary (r (o + j)) (bf j)
              (hf j) = xorWireUnitary (r (o + j)) g hg :=
        Subtype.ext (matrix_ext_ket fun β ↦
            by rw [xorWireUnitary_mulVec_ket, xorWireUnitary_mulVec_ket, hfg β])
      dsimp only [chunkXorOp, xUnloadChunkCzPairsXSeqDyn, xUnloadCzPairsXSeqDyn]
      rw [Matrix.mul_assoc]
      cases hpx : px j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rwa [hU_eq _ hfcz fun β ↦ (heq j β).trans (by simp [hpx])]
      · have hg1 (β : BitAssignment n) (a : ZMod 2) := congrArg ((1 : ZMod 2) + ·) (hfcz β a)
        rw [hU_eq (fun β ↦ 1 + czPairsParity (pf j) β) hg1 fun β ↦ (heq j β).trans (by simp [hpx])]
        refine subspaceStep_seq_trans (subspaceStep_of_circuit _ (Circuit.X (r (o + j)))) ?_
        rwa [← Matrix.mul_assoc, x_mul_xorWireUnitary_add_one (r (o + j)) _ hfcz hg1]
end QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.Stage2Xor84 PhotochemistrySolution.Stage2QromMux
  PhotochemistrySolution.Stage2PotUnld PhotochemistrySolution.SplitRouterFredkinMux
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
/--
Wire map for `rElecBorrow96` packing `privRank454 (j - 4602) ∈ [0..453]` sequentially across
`rScrLayout[30..62]` (`33` wires), `rScrLayout[105..200]` (`96` wires = `rNucLayout[14..109]`), and
`rScrLayout[297..621]` (`325` wires, first `136 + wIn` active in `ActiveLayoutFusedOf wIn`).
-/
def elecBorrow96WireFn (j : Fin (routerWidth 187 8)) : Wire dLayout :=
  if _ : j.val < 4602 then elecRouterWireFn j
  else
    let rk := privRank454 (j.val - 4602)
    if _ : rk < 33 then rScrLayout ⟨30 + rk, by dsimp [scrLLayout]; omega⟩
    else if _ : rk < 129 then rScrLayout ⟨105 + (rk - 33), by dsimp [scrLLayout]; omega⟩
    else rScrLayout ⟨297 + (rk - 129), by
      have _ : rk < 454 := privRank454_lt (by have _ : j.val < 5056 := hEW5056 ▸ j.isLt; omega)
      dsimp [scrLLayout]; omega⟩
theorem val_elecBorrow96WireFn (j : Fin (routerWidth 187 8)) :
    (elecBorrow96WireFn j).val =
      if j.val < 18 then 5729 + j.val
      else if j.val < 114 then 5851 + (j.val - 18)
      else if j.val < 4602 then 1128 + (j.val - 114)
      else if privRank454 (j.val - 4602) < 33 then 5680 + privRank454 (j.val - 4602)
      else if privRank454 (j.val - 4602) < 129 then 5755 + (privRank454 (j.val - 4602) - 33)
      else 5947 + (privRank454 (j.val - 4602) - 129) := by
  have _ : j.val < 5056 := hEW5056 ▸ j.isLt
  dsimp only [elecBorrow96WireFn]
  split_ifs <;> simp only [val_elecRouterWireFn, val_rScrLayout] <;> (try split_ifs) <;> omega
/--
Electronic `RouterReg 187 8 dLayout` borrowing `rNucLayout[14..109]` (`96` clean wires before
`Load(rNuc)` and after `Unload(rNuc)`), giving `265 + wIn` active clean wires across `wIn ≥
0`.
-/
theorem elecBorrow96WireFn_inj : Function.Injective elecBorrow96WireFn := fun a b h ↦ by
  have ha : a.val < 5056 := hEW5056 ▸ a.isLt
  have hb : b.val < 5056 := hEW5056 ▸ b.isLt
  have hra := privRank454_lt (show a.val - 4602 < 454 by omega)
  have hrb := privRank454_lt (show b.val - 4602 < 454 by omega)
  have hv :=
      (val_elecBorrow96WireFn a).symm.trans ((congrArg Fin.val h).trans (val_elecBorrow96WireFn b))
  split_ifs at hv <;> exact Fin.ext (by
    first | omega | (
            have := privRank454_inj (a := a.val - 4602) (b := b.val - 4602) (by omega)
                       (by omega) (by omega)
            omega))
def rElecBorrow96 : RouterReg 187 8 dLayout := ⟨⟨elecBorrow96WireFn, elecBorrow96WireFn_inj⟩⟩
theorem rElecBorrow96_eq_of_lt4602 {j : Fin (routerWidth 187 8)} (hj : j.val < 4602) :
    rElecBorrow96 j = rElecLayout j := dite_eq_left hj
theorem rElecBorrow96_roles_eq :
    rHas1 rElecBorrow96 = rHas1 rElecLayout ∧ rRawHas2 rElecBorrow96 = rRawHas2 rElecLayout ∧
      rIdx1 rElecBorrow96 = rIdx1 rElecLayout ∧ rIdx2 rElecBorrow96 = rIdx2 rElecLayout ∧
      rBufLo rElecBorrow96 = rBufLo rElecLayout ∧ rBufHi rElecBorrow96 = rBufHi rElecLayout ∧
      rHA rElecBorrow96 = rHA rElecLayout ∧ rHB rElecBorrow96 = rHB rElecLayout ∧
      rSys rElecBorrow96 = rSys rElecLayout := by
  have eq {j : Fin (routerWidth 187 8)} (hj : j.val < 4602 := by simp [routerWidth] <;> omega) :
      rElecBorrow96 j = rElecLayout j := rElecBorrow96_eq_of_lt4602 hj
  exact ⟨eq, eq, funext fun _ ↦ eq, funext fun _ ↦ eq, funext fun _ ↦ eq,
    funext fun _ ↦ eq, funext fun _ ↦ eq, funext fun _ ↦ eq, funext fun _ ↦ funext fun _ ↦ eq⟩
theorem rElecBorrow96_loc_scr (j : Fin 454) : ∃ m : Fin scrLLayout, rElecBorrow96 ⟨4602 + j.val,
    privIdx_lt j⟩ = rScrLayout m ∧ (m.val < 65 ∨ 105 ≤ m.val) := by
  have _ := privRank454_lt j.isLt
  let mVal := if privRank454 j.val < 33 then 30 + privRank454 j.val
    else if privRank454 j.val < 129 then 105 + (privRank454 j.val - 33) else 297 +
        (privRank454 j.val - 129)
  refine ⟨⟨mVal, by
    dsimp [mVal, scrLLayout]
    split_ifs <;> omega⟩, Fin.ext ?_,
      by
        dsimp [mVal]
        split_ifs <;> omega⟩
  change (elecBorrow96WireFn _).val = _
  rw [val_elecBorrow96WireFn, val_rScrLayout]
  simp only [Nat.add_sub_cancel_left, mVal]
  split_ifs <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst
namespace QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6Step
set_option maxRecDepth 4096
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectQft8GidneyStg3
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.Stage2Xor84 PhotochemistrySolution.Stage2PotUnld
  PhotochemistrySolution.Stage2ElecFirst PhotochemistrySolution.ProviderZeroFloor
  PhotochemistrySolution.Kinetic664 PhotochemistrySolution.KinBellMux6
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel
    Stage4Kin14Scb.abpKin14Csel Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel
    Kinetic664.abpKin15SqFree2m1Csel Qft8PostCancelT5.qft8PostCancel98CatU
    Qft8PostCancelT5.polyPostCancelT5Qft8Bracket98 Stage4KinFull.bAxisMux27 bSpeciesSwap50
    rPre165Align rClean690Layout rWorkInnerLayout rAlignLayout
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem ket_dc_eq_sb {n : ℕ} (β : BitAssignment n) :
    DynCircExt.ket β = KinB.ket β := rfl
theorem ket_dc_eq_xm {n : ℕ} (β : BitAssignment n) :
    DynCircExt.ket β = PhotochemistrySolution.XMeasUnld.ket β := rfl
theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := DynCircExt.bit_cases b
/-! ## Part A: `rBellMux71Layout` (`71` Wires) & `10`-Wire `pKinOneHot6Local` (`3` ANDs = `12 T`) -/
theorem b71_pre_ctrl {j : Fin 71} (_h1 : ¬ j.val = 0) (h2 : j.val < 7) :
    65 + (j.val - 1) < 165 := by omega
theorem b71_pre_buf {j : Fin 71} (h2 : ¬ j.val < 7) (h3 : j.val < 15) :
    71 + (j.val - 7) < 165 := by omega
theorem b71_pre_h {j : Fin 71} (h3 : ¬ j.val < 15) (h4 : j.val < 23) :
    79 + (j.val - 15) < 165 := by omega
theorem b71_nuc {j : Fin 71} (h4 : ¬ j.val < 23) (h5 : j.val < 47) :
    j.val - 23 < 24 := by omega
theorem b71_elec {j : Fin 71} (h5 : ¬ j.val < 47) :
    j.val - 47 < 24 := by omega
/--
`71`-wire `BellMuxReg 6 8 dLayout` layout (`bellMuxWidth 6 8 = 71`):
- `0` (`bmAnc`): `6001` (`rPre165[87]`)
- `1..6` (`bmCtrl 0..5`): `5979..5984` (`rPre165[65..70]`)
- `7..14` (`bmBuf 0..7`): `5985..5992` (`rPre165[71..78]`)
- `15..22` (`bmH 0..7`): `5993..6000` (`rPre165[79..86]`)
- `23..46` (`bmTgt k p`, `p ∈ 0..2`): `rBufLo rNucLayout (8*p + k)` (`5755..5778`)
- `47..70` (`bmTgt k p`, `p ∈ 3..5`): `rBufLo rElecLayout (8*(p-3) + k)` (`5851..5874`).
-/
def bellMux71WireFn (j : Fin (bellMuxWidth 6 8)) : Wire dLayout :=
  if h1 : j.val = 0 then rPre165Align ⟨87, by decide⟩
  else if h2 : j.val < 7 then rPre165Align ⟨65 + (j.val - 1), b71_pre_ctrl h1 h2⟩
  else if h3 : j.val < 15 then rPre165Align ⟨71 + (j.val - 7), b71_pre_buf h2 h3⟩
  else if h4 : j.val < 23 then rPre165Align ⟨79 + (j.val - 15), b71_pre_h h3 h4⟩
  else if h5 : j.val < 47 then rBufLo rNucLayout ⟨j.val - 23, b71_nuc h4 h5⟩
  else rBufLo rElecLayout ⟨j.val - 47, b71_elec h5⟩
theorem val_rBufLo_nuc_kbm (b : Fin 24) : (rBufLo rNucLayout b).val = 5755 + b.val :=
  (val_nucRouterWireFn ⟨14 + b.val,
      by
        rw [hNW1394]
        omega⟩).trans (by
        dsimp
        split_ifs <;> omega)
theorem val_rBufLo_elec_kbm (b : Fin 24) : (rBufLo rElecLayout b).val = 5851 + b.val :=
  (val_elecRouterWireFn ⟨18 + b.val,
      by
        rw [hEW5056]
        omega⟩).trans (by
        dsimp
        split_ifs <;> omega)
theorem val_bellMux71WireFn (j : Fin (bellMuxWidth 6 8)) : (bellMux71WireFn j).val = if j.val =
    0 then 6001 else if j.val < 7 then 5979 + (j.val - 1) else if j.val < 15 then 5985 + (j.val - 7)
    else if j.val < 23 then 5993 + (j.val - 15) else if j.val < 47 then 5755 +
        (j.val - 23) else 5851 + (j.val - 47) := by
  have hj : j.val < 71 := j.isLt
  dsimp only [bellMux71WireFn]
  split_ifs <;> simp only [val_rPre165_w0, val_rBufLo_nuc_kbm, val_rBufLo_elec_kbm] <;>
      (try dsimp) <;> split_ifs <;> omega
theorem bellMux71WireFn_inj : Function.Injective bellMux71WireFn := fun a b h ↦ by
  have ha : a.val < 71 := a.isLt
  have hb : b.val < 71 := b.isLt
  have hv := (val_bellMux71WireFn a).symm.trans ((congrArg Fin.val h).trans (val_bellMux71WireFn b))
  split_ifs at hv <;> exact Fin.ext (by omega)
def rBellMux71Layout : BellMuxReg 6 8 dLayout := ⟨⟨bellMux71WireFn, bellMux71WireFn_inj⟩⟩
theorem val_bmCtrl_layout (p : Fin 6) : (bmCtrl rBellMux71Layout p).val = 5979 + p.val :=
  (val_bellMux71WireFn ⟨1 + p.val, bm_ltCtrl p⟩).trans (by
    dsimp
    split_ifs <;> omega)
theorem val_bmBuf_layout (k : Fin 8) : (bmBuf rBellMux71Layout k).val = 5985 + k.val :=
  (val_bellMux71WireFn ⟨1 + 6 + k.val,
      bm_ltBuf (M := 6) k⟩).trans (by
        dsimp
        split_ifs <;> omega)
theorem val_bmH_layout (k : Fin 8) : (bmH rBellMux71Layout k).val = 5993 + k.val :=
  (val_bellMux71WireFn ⟨1 + 6 + 8 + k.val,
      bm_ltH (M := 6) k⟩).trans (by
        dsimp
        split_ifs <;> omega)
theorem val_bmTgt_layout (k : Fin 8) (p : Fin 6) :
    (bmTgt rBellMux71Layout k p).val =
      if p.val < 3 then 5755 + (p.val * 8 + k.val) else 5851 + ((p.val - 3) * 8 + k.val) :=
  (val_bellMux71WireFn ⟨23 + (p.val * 8 + k.val), bm_ltTgt k p⟩).trans
    (by
      dsimp
      split_ifs <;> omega)
/-- Dedicated 8-wire register for `bmBuf rBellMux71Layout` (`5985..5992`). -/
def rBmBufLayout : QRegister 8 dLayout :=
  ⟨⟨bmBuf rBellMux71Layout, fun a b h ↦ by
    have hv := congrArg Fin.val h
    rw [val_bmBuf_layout, val_bmBuf_layout] at hv; exact Fin.ext (by omega)⟩⟩
theorem rBmBuf_apply (k : Fin 8) : rBmBufLayout k = bmBuf rBellMux71Layout k := rfl
/-- Dedicated 8-wire register for port `p : Fin 6` (`bmTgt rBellMux71Layout · p`). -/
def rPort6Layout (p : Fin 6) : QRegister 8 dLayout :=
  ⟨⟨fun k ↦ bmTgt rBellMux71Layout k p, fun a b h ↦ by
    have hv := congrArg Fin.val h
    rw [val_bmTgt_layout, val_bmTgt_layout] at hv; split_ifs at hv <;> exact Fin.ext (by omega)⟩⟩
theorem rPort6Layout_zero_eq_rPKin (k : Fin 8) : rPort6Layout ⟨0, by decide⟩ k = rPKinLayout k :=
    Fin.ext (by simp [rPort6Layout, val_bmTgt_layout, val_rPKinLayout])
/-- Decoder scratch wire `wAyKin = 5978` (`rPre165[64]`, holds `sy ∧ ¬sz`). -/
def wAyKin : Wire dLayout := rPre165Align ⟨64, by decide⟩
theorem val_wAyKin : wAyKin.val = 5978 := by simp [wAyKin, val_rPre165_w0]
/--
`10`-wire register `(e, sy, sz, ay, c0, c1, c2, c3, c4, c5)` on `dLayout`
(`6058, 6056, 6057, 5978, 5979..5984`).
-/
def oneHot10WireFn (i : Fin 10) : Wire dLayout :=
  if i.val = 0 then wIsElecKin
  else if i.val = 1 then wKinAxis0
  else if i.val = 2 then wKinAxis1
  else if i.val = 3 then wAyKin
  else bmCtrl rBellMux71Layout ⟨i.val - 4, by omega⟩
theorem val_oneHot10WireFn (i : Fin 10) : (oneHot10WireFn i).val = if i.val =
    0 then 6058 else if i.val = 1 then 6056 else if i.val = 2 then 6057 else if i.val =
    3 then 5978 else 5979 + (i.val - 4) := by
  dsimp only [oneHot10WireFn]
  split_ifs <;> simp [wIsElecKin, wKinAxis0, wKinAxis1, val_rAlignLayout, val_wAyKin,
      val_bmCtrl_layout]
theorem oneHot10WireFn_inj : Function.Injective oneHot10WireFn := fun a b h ↦ by
  have hv := (val_oneHot10WireFn a).symm.trans ((congrArg Fin.val h).trans (val_oneHot10WireFn b))
  split_ifs at hv <;> exact Fin.ext (by omega)
def rOneHot10Layout : QRegister 10 dLayout := ⟨⟨oneHot10WireFn, oneHot10WireFn_inj⟩⟩
theorem rOneHot10_apply (i : Fin 10) : rOneHot10Layout i = oneHot10WireFn i := rfl
theorem rOneHot10_0 : rOneHot10Layout ⟨0, by decide⟩ = wIsElecKin := rfl
theorem rOneHot10_1 : rOneHot10Layout ⟨1, by decide⟩ = wKinAxis0 := rfl
theorem rOneHot10_2 : rOneHot10Layout ⟨2, by decide⟩ = wKinAxis1 := rfl
theorem rOneHot10_3 : rOneHot10Layout ⟨3, by decide⟩ = wAyKin := rfl
theorem rOneHot10_ctrl (p : Fin 6) : rOneHot10Layout ⟨4 + p.val, by omega⟩ =
    bmCtrl rBellMux71Layout p :=
  Fin.ext ((val_oneHot10WireFn ⟨4 + p.val, by omega⟩).trans
    (by
      rw [val_bmCtrl_layout]
      dsimp
      split_ifs <;> omega))
/--
Exact `3`-AND (`12 T`, `0-T` MBU uncompute) `1 -> 6` one-hot decoder on `Wire 10`:
`0 = e`, `1 = sy`, `2 = sz`, `3 = ay`, `4..9 = c0..c5`.
-/
def pKinOneHot6Local : ComputeProg 10 :=
  let we  : Wire 10 := ⟨0, by decide⟩
  let wsy : Wire 10 := ⟨1, by decide⟩
  let wsz : Wire 10 := ⟨2, by decide⟩
  let way : Wire 10 := ⟨3, by decide⟩
  let wc0 : Wire 10 := ⟨4, by decide⟩
  let wc1 : Wire 10 := ⟨5, by decide⟩
  let wc2 : Wire 10 := ⟨6, by decide⟩
  let wc3 : Wire 10 := ⟨7, by decide⟩
  let wc4 : Wire 10 := ⟨8, by decide⟩
  let wc5 : Wire 10 := ⟨9, by decide⟩
  .seq (.x wsz)
  (.seq (.andGate wsy wsz way (by decide) (by decide) (by decide))
  (.seq (.x wsz)
  (.seq (.andGate we wsz wc5 (by decide) (by decide) (by decide))
  (.seq (.andGate we way wc4 (by decide) (by decide) (by decide))
  (.seq (.cnot we wc3 (by decide))
  (.seq (.cnot wc4 wc3 (by decide))
  (.seq (.cnot wc5 wc3 (by decide))
  (.seq (.cnot wsz wc2 (by decide))
  (.seq (.cnot wc5 wc2 (by decide))
  (.seq (.cnot way wc1 (by decide))
  (.seq (.cnot wc4 wc1 (by decide))
  (.seq (.x wc0)
  (.seq (.cnot wc1 wc0 (by decide))
  (.seq (.cnot wc2 wc0 (by decide))
  (.seq (.cnot wc3 wc0 (by decide))
  (.seq (.cnot wc4 wc0 (by decide))
        (.cnot wc5 wc0 (by decide))))))))))))))))))
def activePort6 (e sy sz : ZMod 2) : Fin 6 :=
  if sz = 1 then
    if e = 1 then ⟨5, by decide⟩ else ⟨2, by decide⟩
  else if sy = 1 then
    if e = 1 then ⟨4, by decide⟩ else ⟨1, by decide⟩
  else
    if e = 1 then ⟨3, by decide⟩ else ⟨0, by decide⟩
def mkOneHot10In (e sy sz : ZMod 2) : BitAssignment 10
  | ⟨0, _⟩ => e
  | ⟨1, _⟩ => sy
  | ⟨2, _⟩ => sz
  | _ => 0
def vec10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ZMod 2) : BitAssignment 10 := fun i ↦
    if i.val = 0 then a0 else if i.val = 1 then a1 else if i.val = 2 then a2 else if i.val =
    3 then a3 else if i.val = 4 then a4 else if i.val = 5 then a5 else if i.val =
    6 then a6 else if i.val = 7 then a7 else if i.val = 8 then a8 else a9
theorem vec10_apply (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ZMod 2) (i : Fin 10) :
    vec10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 i =
      if i.val = 0 then a0 else if i.val = 1 then a1 else if i.val = 2 then a2
      else if i.val = 3 then a3 else if i.val = 4 then a4 else if i.val = 5 then a5
      else if i.val = 6 then a6 else if i.val = 7 then a7 else if i.val = 8 then a8 else a9 := rfl
theorem mkOneHot10In_eq_vec10 (e sy sz : ZMod 2) : mkOneHot10In e sy sz =
    vec10 e sy sz 0 0 0 0 0 0 0 := by
  ext i
  fin_cases i <;> rfl
theorem update_vec10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : ZMod 2) (k : Fin 10)
    (v : ZMod 2) : Function.update (vec10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) k v =
    vec10 (if k.val = 0 then v else a0) (if k.val = 1 then v else a1) (if k.val = 2 then v else a2)
        (if k.val = 3 then v else a3) (if k.val = 4 then v else a4)
    (if k.val = 5 then v else a5) (if k.val = 6 then v else a6) (if k.val = 7 then v else a7)
        (if k.val = 8 then v else a8) (if k.val = 9 then v else a9) := by
  ext i
  fin_cases i <;> fin_cases k <;> simp [vec10, Fin.ext_iff]
theorem pKinOneHot6Local_fwdBits_eq (e sy sz : ZMod 2) :
    pKinOneHot6Local.fwdBits (mkOneHot10In e sy sz) =
      let ay := 0 + sy * (sz + 1); let c5 := 0 + e * (sz + 1 + 1); let c4 := 0 + e * ay;
      let c3 := 0 + e + c4 + c5; let c2 := 0 + (sz + 1 + 1) + c5; let c1 := 0 + ay + c4;
      let c0 := 0 + 1 + c1 + c2 + c3 + c4 + c5
      vec10 e sy (sz + 1 + 1) ay c0 c1 c2 c3 c4 c5 := by
  simp only [pKinOneHot6Local, ComputeProg.fwdBits, mkOneHot10In_eq_vec10, update_vec10,
      vec10_apply, ↓reduceIte, Nat.reduceEqDiff]
theorem pKinOneHot6Local_fwdBits_spec (e sy sz : ZMod 2) :
    let out := pKinOneHot6Local.fwdBits (mkOneHot10In e sy sz)
    out ⟨0, by decide⟩ = e ∧ out ⟨1, by decide⟩ = sy ∧ out ⟨2, by decide⟩ = sz ∧
      out ⟨4 + (activePort6 e sy sz).val, by omega⟩ = 1 ∧ ∀ p : Fin 6, p ≠ activePort6 e sy sz →
          out ⟨4 + p.val, by omega⟩ = 0 := by
  dsimp only
  rw [pKinOneHot6Local_fwdBits_eq]
  rcases zmod2_cases e with rfl | rfl <;> rcases zmod2_cases sy with rfl | rfl <;>
      rcases zmod2_cases sz with rfl | rfl <;>
    refine ⟨by decide, by decide, by decide, by decide, fun p hp ↦
        by fin_cases p <;> first | exact absurd rfl hp | decide⟩
theorem writeReg_update_kbm {K d : ℕ} (r : QRegister K d) (δ : BitAssignment d)
    (α : BitAssignment K) (i : Fin K) (v : ZMod 2) :
    Function.update (DynCircExt.writeReg δ r α)
        (r i) v = DynCircExt.writeReg δ r (Function.update α i v) := by
  ext u
  rcases Classical.em (u ∈ Set.range r.wires) with ⟨j, rfl⟩ | hu
  · by_cases h : j = i <;> simp [h, DynCircExt.writeReg_apply_reg, r.wires.injective.eq_iff]
  · simp [Function.update_of_ne (fun h ↦ hu ⟨i, h.symm⟩ : u ≠ r i),
      DynCircExt.writeReg_apply_of_not_mem _ r _ u hu]
theorem writeReg_idem_kbm {K d : ℕ} (r : QRegister K d) (δ : BitAssignment d)
    (α β : BitAssignment K) : DynCircExt.writeReg (DynCircExt.writeReg δ r α) r β =
    DynCircExt.writeReg δ r β := by
  ext u
  rcases Classical.em (u ∈ Set.range r.wires) with ⟨_, rfl⟩ | hu
  · simp only [DynCircExt.writeReg_apply_reg]
  · simp only [DynCircExt.writeReg_apply_of_not_mem _ r _ u hu]
end QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6Step
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution
  PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectCompactAnc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.KetSupport
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr bSpeciesSwap50
    abpKin14Usel
def IsRoutedKet (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (γ : BitAssignment dLayout) :
    Prop :=
    ∃ (β : BitAssignment dLayout) (c : Fin (2 ^ 41)) (z : BitAssignment 41), CleanScr β ∧ γ =
    routedKet decodeCoin β c z
theorem val_bufHi_nuc (b : Fin 24) : (rBufHi rNucLayout b).val = 5779 + b.val := by
  change (nucRouterWireFn ⟨38 + b.val, _⟩).val = _
  rw [val_nucRouterWireFn]
  dsimp only
  split_ifs <;> omega
theorem val_sys_nuc_lt (p : Fin 47) (b : Fin 24) : (rSys rNucLayout p b).val < 1128 := by
  change (nucRouterWireFn ⟨110 + 24 * p.val + b.val, _⟩).val < _
  rw [val_nucRouterWireFn]
  dsimp only
  split_ifs <;> omega
theorem val_bufHi_elec (b : Fin 24) : (rBufHi rElecLayout b).val = 5875 + b.val := by
  change (elecRouterWireFn ⟨42 + b.val, _⟩).val = _
  rw [val_elecRouterWireFn]
  dsimp only
  split_ifs <;> omega
theorem val_sys_elec_lt (p : Fin 187) (b : Fin 24) : (rSys rElecLayout p b).val < 5616 := by
  change (elecRouterWireFn ⟨114 + 24 * p.val + b.val, _⟩).val < _
  rw [val_elecRouterWireFn]
  dsimp only
  split_ifs <;> omega
theorem routedKet_clean690 {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout} (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41)
    (m : Fin 690) : routedKet decodeCoin β c z (rClean690Layout m) = 0 := by
  have hm := val_rClean690Layout m
  exact ((validRouter_stage1 (decodeCoin :=
      decodeCoin) hScr c z).2.2.2.1 _ (by split_ifs at hm <;> omega)).trans
    (stage1_scr_zero hScr c z (by split_ifs at hm <;> omega))
theorem routedKet_wIsElecKin {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout}
    (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    routedKet decodeCoin β c z wIsElecKin = 0 :=
  (Fin.ext (by
    rw [val_rAlignLayout, val_rClean690Layout]
    dsimp only
    split_ifs <;> omega) :
    wIsElecKin = rClean690Layout ⟨144, by omega⟩) ▸ routedKet_clean690 hScr c z _
theorem stage1_rebuild_onePort {M D : ℕ} (r : RouterReg M D dLayout)
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} {β δ : BitAssignment dLayout}
    (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41) (p₀ : Fin M)
    (hSysVal : ∀ (p : Fin M) (b : Fin 24), (rSys r p b).val < 5616) : ∃ β' : BitAssignment dLayout,
    CleanScr β' ∧ (∀ b : Fin 24, routedStage1 decodeCoin β' c z (rSys r p₀ b) =
    δ (rBufLo r b)) ∧ (∀ w : Wire dLayout, 5616 ≤ w.val ∧ w.val ≤ 5649 →
    routedStage1 decodeCoin β' c z w = δ w) ∧ (∀ w : Wire dLayout, (∀ b : Fin 24, w ≠
    rSys r p₀ b) → ¬(5616 ≤ w.val ∧ w.val ≤ 5649) → routedStage1 decodeCoin β' c z w =
    routedStage1 decodeCoin β c z w) := by
  let rRow : QRegister 24 dLayout := ⟨⟨fun b ↦ rSys r p₀ b, fun a b e ↦
    Fin.ext (by
      have h := congrArg Fin.val (r.wires.injective e)
      dsimp at h
      omega)⟩⟩
  let rCat34 : QRegister 34 dLayout := QRegister.block 5616 34 (by
    have h0 :=
        (rScrLayout ⟨0, by
          unfold scrLLayout
          omega⟩).isLt
    rw [val_rScrLayout] at h0
    omega)
  let β' :=
      DynCircExt.writeReg (DynCircExt.writeReg β rRow fun b ↦ δ (rBufLo r b)) rCat34 fun k ↦
      δ (rCat34 k)
  have vCat (k : Fin 34) : (rCat34 k).val = 5616 + k.val := rfl
  have nCat {w : Wire dLayout} (hw : ¬(5616 ≤ w.val ∧ w.val ≤ 5649)) : w ∉ Set.range rCat34.wires :=
    fun ⟨k, hk⟩ ↦ hw (by
      have := (congrArg Fin.val hk).symm.trans (vCat k)
      omega)
  have hd7298 : totDimCompactGen scrWLayout = 7298 := by
    rw [totDimCompactGen, hSys5616, ancWOfScr_layout_odd]
  let wrNm := @DynCircExt.writeReg_apply_of_not_mem
  refine ⟨β', fun m ↦ ?_, fun b ↦ ?_, fun w hw ↦ ?_, fun w hne hnc ↦ ?_⟩
  · have hm : 5650 ≤ (rScrLayout m).val := by
      rw [val_rScrLayout]
      omega
    exact (wrNm _ _ _ _ (nCat (by omega))).trans ((wrNm _ _ _ _ fun ⟨b, hb⟩ ↦ by
      have hv : (rSys r p₀ b).val = _ :=
          congrArg Fin.val hb
      have hs := hSysVal p₀ b
      omega).trans (hScr m))
  · have hs := hSysVal p₀ b
    exact (stage1_outside_eq decodeCoin β' c z (by omega) (.inl (by omega))).trans
      ((wrNm _ _ _ (rRow b)
          (nCat (by
            change ¬(5616 ≤ (rSys r p₀ b).val ∧ (rSys r p₀ b).val ≤ 5649)
            omega))).trans
        (DynCircExt.writeReg_apply_reg β rRow _ b))
  · exact (stage1_outside_eq decodeCoin β' c z (by omega) (.inl (by omega))).trans
      ((Fin.ext (by
        rw [vCat]
        dsimp only
        omega) : w = rCat34 ⟨w.val - 5616, by omega⟩) ▸
        DynCircExt.writeReg_apply_reg _ rCat34 _ _)
  · have eqWr {k} (rk : QRegister k dLayout) (vk : BitAssignment k) {f g : BitAssignment dLayout}
        (hfg : f w = g w) :
        DynCircExt.writeReg f rk vk w = DynCircExt.writeReg g rk vk w :=
      (Classical.em (w ∈ Set.range rk.wires)).elim (fun ⟨j, hj⟩ ↦
          hj ▸ (DynCircExt.writeReg_apply_reg f rk vk j).trans
        (DynCircExt.writeReg_apply_reg g rk vk j).symm) fun h ↦
            (wrNm f rk vk w h).trans (hfg.trans (wrNm g rk vk w h).symm)
    exact eqWr rOut40Layout _ (eqWr rLcu82Layout _ ((wrNm _ _ _ _ (nCat hnc)).trans (wrNm _ _ _ _
        fun ⟨b, hb⟩ ↦ hne b hb.symm)))
/-- Nuclear port (`i.val < 47`) routed-ket reconstruction after kinetic core selection. -/
theorem kin_nuc_rebuild {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β ξ : BitAssignment dLayout} (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41)
    (i : Particle_frozen) (ax : Fin 3) (hs : decodeCoin c = .kin i ax) (hi : i.val < 47)
    (hξ : (∀ k : Fin 521, ξ (rWorkInnerLayout k) = 0) ∧ (∀ w : Wire dLayout, ¬(5616 ≤ w.val ∧
    w.val ≤ 5649) → ¬(5755 ≤ w.val ∧ w.val ≤ 5778) → ξ w =
    speciesSwapBits (pKinAlign0.fwdBits (routedKet decodeCoin β c z)) w)) :
    IsRoutedKet decodeCoin (pKinAlign0.fwdBits (speciesSwapBits ξ)) := by
  have _ := ax.isLt
  let γ := routedKet decodeCoin β c z
  let ηk := pKinAlign0.fwdBits γ
  let δ := pKinAlign0.fwdBits (speciesSwapBits ξ)
  have mkF (η : BitAssignment dLayout)
      (hη : ∀ j, η (rOut40Layout j) = outMaskBits40 (decodeCoin c) j) :=
    packOut40ZeroNErem_fields true false i.val 0 false false 0 0 false false true false 0 ax.val
      (by omega) (by omega) (by omega) (by omega) η
      fun j ↦ (hη j).trans (by
        dsimp [outMaskBits40]
        rw [hs]
        simp [zeroNEremOutMask, hi])
  have mkS1 (b0 : BitAssignment dLayout) :=
      mkF (routedStage1 decodeCoin b0 c z) (DynCircExt.writeReg_apply_reg _ rOut40Layout _)
  have F1 := mkS1 β
  have hEK0 : ηk wIsElecKin = 0 := by
    rw [show ηk wIsElecKin =
        _ from (fwdBits_pKinAlign0_targets (routedKet decodeCoin β c z)).2.2.2,
      routedKet_wIsElecKin hScr c z, ← rElec_header_eq_out40.1,
          (mkF _ (routedKet_out40 hScr c z)).2.2.2.2.1]
    rfl
  have hSpId (u : Wire dLayout) : speciesSwapBits ηk u = ηk u := speciesSwapBits_of_off fun h ↦
      zero_ne_one (hEK0 ▸ h)
  have hEKξ : ξ wIsElecKin = 0 :=
      (hξ.2 wIsElecKin (by
        rw [val_rAlignLayout]
        omega)
      (by
        rw [val_rAlignLayout]
        omega)).trans
    ((hSpId wIsElecKin).trans hEK0)
  obtain ⟨β', hScr', hRow', hCat', hSame'⟩ :=
      stage1_rebuild_onePort rNucLayout (decodeCoin := decodeCoin) (δ := δ)
    hScr c z ⟨i.val, hi⟩ fun p b ↦ (val_sys_nuc_lt p b).trans (by omega)
  have F1' := mkS1 β'
  have V := validRouter_stage1 (decodeCoin := decodeCoin) hScr c z
  have V' := validRouter_stage1 (decodeCoin := decodeCoin) hScr' c z
  have eIdle :=
      routerSwapBits_idle_eq rElecLayout ((V.2.1 _).trans F1.2.2.2.2.1)
      ((V.2.1 _).trans F1.2.2.2.2.2.1)
  refine ⟨β', c, z, hScr',
      Eq.symm ((routerSwapBits_idle_eq rElecLayout ((V'.2.1 _).trans F1'.2.2.2.2.1)
    ((V'.2.1 _).trans F1'.2.2.2.2.2.1)).trans <| routerSwapBits_onePort_eq rNucLayout ⟨i.val,
        hi⟩ V.1 V'.1
      F1.1 F1.2.1 F1.2.2.1 F1'.1 F1'.2.1 F1'.2.2.1 hRow' (fun w nLo nCat ↦
          (congrFun eIdle.symm w).trans
        (fwdBits_pKinAlign0_keep (Bad := fun u ↦ (5616 ≤ u.val ∧ u.val ≤ 5649) ∨ (5755 ≤ u.val ∧
            u.val ≤ 5778))
          (fun _ _ ↦ by omega)
              (fun u hu ↦ (speciesSwapBits_of_off fun h ↦ zero_ne_one (hEKξ ▸ h)).trans
            ((hξ.2 u (fun h ↦ hu (.inl h)) fun h ↦ hu (.inr h)).trans (hSpId u)))
          (fun h ↦ h.elim nCat fun h78 ↦ nLo ⟨w.val - 5755, by omega⟩
            (Fin.ext (by
              rw [val_rBufLo_nuc]
              dsimp only
              omega)))).symm)
      hSame' hCat' fun w hw ↦ ⟨fun b e ↦ by
        have := val_rBufLo_nuc b
        rw [e] at hw
        omega,
        fun b e ↦ by
          have := val_bufHi_nuc b
          rw [e] at hw
          omega,
        fun p b e ↦ by
          have := val_sys_nuc_lt p b
          rw [e] at hw
          omega⟩)⟩
theorem kin_elec_rebuild {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β ξ : BitAssignment dLayout} (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41)
    (i : Particle_frozen) (ax : Fin 3) (hs : decodeCoin c = .kin i ax) (hi : ¬ i.val < 47)
    (hξ : (∀ k : Fin 521, ξ (rWorkInnerLayout k) = 0) ∧ (∀ w : Wire dLayout, ¬(5616 ≤ w.val ∧
    w.val ≤ 5649) → ¬(5755 ≤ w.val ∧ w.val ≤ 5778) → ξ w =
    speciesSwapBits (pKinAlign0.fwdBits (routedKet decodeCoin β c z)) w)) :
    IsRoutedKet decodeCoin (pKinAlign0.fwdBits (speciesSwapBits ξ)) := by
  have hi234 := i.isLt
  have hax := ax.isLt
  let γ := routedKet decodeCoin β c z
  let ηk := pKinAlign0.fwdBits γ
  let δ := pKinAlign0.fwdBits (speciesSwapBits ξ)
  have mkF (η : BitAssignment dLayout)
      (hη : ∀ j, η (rOut40Layout j) = outMaskBits40 (decodeCoin c) j) :=
    packOut40ZeroNErem_fields false false 0 0 true false (i.val -
        47) 0 false false true false 0 ax.val
      (by omega) (by omega) (by omega) (by omega) η
      fun j ↦ (hη j).trans (by
        dsimp [outMaskBits40]
        rw [hs]
        simp [zeroNEremOutMask, hi])
  have mkS1 (b0 : BitAssignment dLayout) :=
      mkF (routedStage1 decodeCoin b0 c z) (DynCircExt.writeReg_apply_reg _ rOut40Layout _)
  have F1 := mkS1 β
  have hEK1 : ηk wIsElecKin = 1 := by
    rw [show ηk wIsElecKin =
        _ from (fwdBits_pKinAlign0_targets (routedKet decodeCoin β c z)).2.2.2,
      routedKet_wIsElecKin hScr c z, ← rElec_header_eq_out40.1,
          (mkF _ (routedKet_out40 hScr c z)).2.2.2.2.1]
    rfl
  have hEKB : 5947 ≤ wIsElecKin.val := by
    rw [val_rAlignLayout]
    omega
  have hEKξ : ξ wIsElecKin = 1 := (hξ.2 wIsElecKin (by omega) (by omega)).trans
    ((speciesSwapBits_of_other (by omega) (by omega)).trans hEK1)
  have hδKeep (w : Wire dLayout) (hw1 : ¬(5616 ≤ w.val ∧ w.val ≤ 5649))
      (hw2 : ¬(5851 ≤ w.val ∧ w.val ≤ 5874)) :
      δ w = γ w := fwdBits_pKinAlign0_keep
    (Bad := fun u ↦ (5616 ≤ u.val ∧ u.val ≤ 5649) ∨ (5851 ≤ u.val ∧ u.val ≤ 5874))
        (fun _ _ ↦ by omega)
    (fun u hu ↦ by
      by_cases hN : 5755 ≤ u.val ∧ u.val < 5779
      · let v := rBufLo rElecLayout ⟨u.val - 5755, by omega⟩
        have hv0 : v.val = 5851 + (u.val - 5755) := val_rBufLo_elec _
        rw [speciesSwapBits_of_nucBuf hEKξ hN, hξ.2 v (by omega)
            (by omega), speciesSwapBits_of_elecBuf hEK1 (by omega)]
        exact congrArg ηk (Fin.ext (by
          rw [val_rBufLo_nuc]
          dsimp only
          omega))
      · rw [speciesSwapBits_of_other hN fun hE ↦ hu (.inr ⟨hE.1, by omega⟩),
          hξ.2 u (fun h ↦ hu (.inl h)) fun h ↦ hN ⟨h.1, by omega⟩,
          speciesSwapBits_of_other hN fun hE ↦
              hu (.inr ⟨hE.1, by omega⟩)]) (fun h ↦ h.elim hw1 hw2)
  obtain ⟨β', hScr', hRow', hCat', hSame'⟩ :=
    stage1_rebuild_onePort rElecLayout (decodeCoin := decodeCoin)
        (δ := δ) hScr c z ⟨i.val - 47, by omega⟩ val_sys_elec_lt
  have F1' := mkS1 β'
  have V := validRouter_stage1 (decodeCoin := decodeCoin) hScr c z
  have V' := validRouter_stage1 (decodeCoin := decodeCoin) hScr' c z
  have nIdle := routerSwapBits_idle_eq rNucLayout F1.1 F1.2.1
  have nIdle' := routerSwapBits_idle_eq rNucLayout F1'.1 F1'.2.1
  exact ⟨β', c, z, hScr', (routerSwapBits_onePort_eq rElecLayout (δ := δ)
      ⟨i.val - 47, by omega⟩ V.2.2.1 V'.2.2.1
    ((congrFun nIdle _).trans F1.2.2.2.2.1) ((congrFun nIdle _).trans F1.2.2.2.2.2.1)
    ((congrArg (idxValD (rIdx1 rElecLayout)) nIdle).trans F1.2.2.2.2.2.2.1)
    ((congrFun nIdle' _).trans F1'.2.2.2.2.1) ((congrFun nIdle' _).trans F1'.2.2.2.2.2.1)
    ((congrArg (idxValD (rIdx1 rElecLayout)) nIdle').trans F1'.2.2.2.2.2.2.1)
    (fun b ↦ (congrFun nIdle' _).trans (hRow' b))
    (fun w nLo nCat ↦ (hδKeep w nCat fun h74 ↦ nLo ⟨w.val - 5851, by omega⟩
      (Fin.ext (by
        rw [val_rBufLo_elec]
        dsimp only
        omega))).symm)
    (fun w hne nCat ↦ (congrFun nIdle' w).trans ((hSame' w hne nCat).trans (congrFun nIdle w).symm))
    (fun w hw ↦ (congrFun nIdle' w).trans (hCat' w hw))
    fun w hw ↦ ⟨fun b e ↦ by
      have := val_rBufLo_elec b
      rw [e] at hw
      omega,
      fun b e ↦ by
        have := val_bufHi_elec b
        rw [e] at hw
        omega,
      fun p b e ↦ by
        have := val_sys_elec_lt p b
        rw [e] at hw
        omega⟩).symm⟩
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end

noncomputable section
attribute [local irreducible]
    QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc.ancWOfScr
    QuantumComputation.Specs.PhotochemistrySolution.PgBase.phaseGradientState
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs PhotochemistrySolution.KetSupport
  PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSandwich PhotochemistrySolution.SelectCompactAnc
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
attribute [local irreducible] systemQubits_frozen
theorem routedKet_eq_writeReg_z (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (β : BitAssignment dLayout) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    routedKet decodeCoin β c z =
    DynCircExt.writeReg (routedKet decodeCoin β c 0) rInner41Layout z := by
  have hs0 (w : Wire dLayout) (hw : w ∉ Set.range rInner41Layout.wires) :
      routedStage0 β c z w = routedStage0 β c 0 w := by
    rcases Classical.em (w ∈ Set.range rLcu82Layout.wires) with ⟨i, rfl⟩ | hl
    · simp only [routedStage0, DynCircExt.writeReg_apply_reg, pack82, not_le.mp fun hle ↦
        hw ⟨⟨i.val - 41, Nat.sub_lt_left_of_lt_add hle (by simpa [mLayout] using i.isLt)⟩,
          (rInner41_eq_lcu _).trans (congrArg rLcu82Layout (Fin.ext (Nat.add_sub_of_le hle)))⟩,
              ↓reduceDIte]
    · simp only [routedStage0, DynCircExt.writeReg_apply_of_not_mem _ _ _ w hl]
  dsimp only [routedKet, routedStage2]
  rw [show routedStage1 decodeCoin β c z =
        DynCircExt.writeReg (routedStage1 decodeCoin β c 0) rInner41Layout z from funext fun w
            ↦ by
      rcases Classical.em (w ∈ Set.range rInner41Layout.wires) with ⟨k, rfl⟩ | hw
      · rw [DynCircExt.writeReg_apply_reg, routedStage1,
            DynCircExt.writeReg_apply_of_not_mem _ _ _ _
          fun ⟨_, hj⟩ ↦
              absurd (congrArg Fin.val hj)
              (by
                simp only [val_rOut40Layout, val_rInner41Layout]
                omega),
          rInner41_eq_lcu k]
        simpa only [routedStage0, DynCircExt.writeReg_apply_reg, pack82, show ¬41 + k.val <
            41 by omega, ↓reduceDIte]
          using congrArg z (Fin.ext (Nat.add_sub_cancel_left 41 k.val))
      · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ w hw]
        rcases Classical.em (w ∈ Set.range rOut40Layout.wires) with ⟨_, rfl⟩ | ho
        · simp only [routedStage1, DynCircExt.writeReg_apply_reg]
        · simp only [routedStage1, DynCircExt.writeReg_apply_of_not_mem _ _ _ w ho, hs0 w hw],
    routerSwapBits_writeReg_z rNucLayout fun j ↦ (fun _ ↦ by omega) (val_rNuc_bounds j),
    routerSwapBits_writeReg_z rElecLayout fun j ↦ (fun _ ↦ by omega) (val_rElec_bounds j)]
theorem routedKet_rInner41 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (β : BitAssignment dLayout) (c : Fin (2 ^ 41)) (z : BitAssignment 41)
    (k : Fin 41) : routedKet decodeCoin β c z (rInner41Layout k) = z k := by
  rw [routedKet_eq_writeReg_z decodeCoin β c z, DynCircExt.writeReg_apply_reg]
theorem routedKet_align_zero {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout} (hScr : ∀ m, β (rScrLayout m) = 0)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    ∀ k : Fin 136, routedKet decodeCoin β c z (rAlignLayout k) = 0 := fun k ↦
  (fun _ ↦ ((validRouter_stage1 (decodeCoin := decodeCoin) hScr c z).2.2.2.1 _
    (.inr (.inr (by omega)))).trans (stage1_scr_zero hScr c z (.inr (by omega))))
        (val_rAlignLayout k)
theorem routerSwapBits_cases {M D n : ℕ} (r : RouterReg M D n) {β : BitAssignment n}
    (hV : ValidRouterInput r β) : (β (rHas1 r) = 0 → β (rRawHas2 r) = 0 →
    (∀ b, routerSwapBits r β (rBufLo r b) = 0) ∧ (∀ b, routerSwapBits r β (rBufHi r b) = 0)) ∧
    (∀ p : Fin M, β (rHas1 r) = 1 → β (rRawHas2 r) = 0 → idxValD (rIdx1 r) β = p.val →
    (∀ b, routerSwapBits r β (rBufLo r b) = β (rSys r p b)) ∧
    (∀ b, routerSwapBits r β (rBufHi r b) = 0)) ∧ (∀ p1 p2 : Fin M, p1.val < p2.val →
    β (rHas1 r) = 1 → β (rRawHas2 r) = 1 → idxValD (rIdx1 r) β = p1.val → idxValD (rIdx2 r) β =
    p2.val → (∀ b, routerSwapBits r β (rBufLo r b) = β (rSys r p1 b)) ∧
    (∀ b, routerSwapBits r β (rBufHi r b) = β (rSys r p2 b))) := by
  obtain ⟨sLo, sHi, _, _⟩ := routerSwapBits_spec r hV
  have hHi0 (h20 : β (rRawHas2 r) = 0) (b) := (sHi b).trans (dite_eq_right fun h ↦
    zero_ne_one ((show routerHas2Eff r β = 0 by simp [routerHas2Eff, h20]) ▸ h.1))
  have hLo1 (p : Fin M) (h1) (hm : routerIdxMinVal r β = p.val) (b) :=
    (sLo b).trans ((dite_eq_left ⟨h1, hm ▸ p.isLt⟩).trans (congrArg (β <| rSys r · b) (Fin.ext hm)))
  refine ⟨fun h10 h20 ↦ ⟨fun b ↦ (sLo b).trans (dite_eq_right fun h ↦ zero_ne_one (h10 ▸ h.1)),
    hHi0 h20⟩, fun p h1 h20 hi1 ↦ ⟨hLo1 p h1 (by simp [routerIdxMinVal, routerHas2Eff, h20, hi1]),
    hHi0 h20⟩, fun p1 p2 hl h1 h2 i1 i2 ↦ ?_⟩
  have he : routerHas2Eff r β = 1 := by simp [routerHas2Eff, h2, i1, i2, Nat.ne_of_lt hl]
  have hx : routerIdxMaxVal r β = p2.val := by simp [routerIdxMaxVal, he, i1, i2, not_lt_of_gt hl]
  exact ⟨hLo1 p1 h1 (by simp [routerIdxMinVal, he, i1, i2, not_lt_of_gt hl]), fun b ↦
    (sHi b).trans ((dite_eq_left ⟨he, hx ▸ p2.isLt⟩).trans (congrArg (β <| rSys r · b) (Fin.ext
        hx)))⟩
theorem routedBuf_keep_stage1 {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout} (hScr : ∀ m, β (rScrLayout m) = 0)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    (∀ p b, routedStage1 decodeCoin β c z (rSys rNucLayout p b) = β (rSys rNucLayout p b)) ∧
    (∀ p b, routedStage2 decodeCoin β c z (rSys rElecLayout p b) = β (rSys rElecLayout p b)) := by
  have hO {w : Wire dLayout} (_ : w.val < 5616) : routedStage1 decodeCoin β c z w = β w :=
    stage1_outside_eq decodeCoin β c z (by omega) (.inl (by omega))
  exact ⟨fun p b ↦ hO (by
      rw [show (rSys rNucLayout p b).val = _ from val_nucRouterWireFn ⟨110 + 24 * p.val + b.val, _⟩]
      dsimp only
      split_ifs <;> omega),
    fun p b ↦ ((validRouter_stage1 (decodeCoin := decodeCoin) hScr c z).2.1 _).trans (hO (by
      rw [show (rSys rElecLayout p b).val = _ from val_elecRouterWireFn ⟨114 + 24 * p.val + b.val,
          _⟩]
      dsimp only
      split_ifs <;> omega))⟩
theorem proj_had82_ket_routedStage0 {β : BitAssignment dLayout}
    (hr0 : ∀ i, β (rLcu82Layout i) = 0) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
    (rLcu82Layout.basisOutcomeProjector 0 *
        (uHad82Layout⁻¹).1).mulVec (ket (routedStage0 β c z)) = (sqrtHalf ^ 82) • ket β :=
  let _ : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  proj_zero_mul_hadamardRegSym_inv_mulVec (Var :=
      Unit) wHasN1 82 rLcu82Layout hDisjHad82_layout β hr0 (pack82 c z)
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring


namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.DynQromUncompA
open PhotochemistrySolution.XMeasChunkQromUnldA PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.TopSelectBridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
attribute [local irreducible] SpecDefs.systemQubits_frozen
    XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel Stage4Kin14Scb.abpKin14Csel
    bSpeciesSwap50 Stage4KinFull.bAxisMux27
theorem val_rBufLo_hi (b : Fin 24) : (rBufLo rElecLayout b).val = 5851 + b.val ∧
    (rBufHi rElecLayout b).val = 5875 + b.val :=
  ⟨val_rCoordLayout ⟨2, by decide⟩ b, val_rCoordLayout ⟨3, by decide⟩ b⟩
theorem comm_align_of_disj {k : ℕ} (r : QRegister k dLayout) (M : Operator (2 ^ k))
    (neR : ∀ {u : Wire dLayout}, u.val < 5616 ∨ (5650 ≤ u.val ∧ u.val < 7256) → ∀ i : Fin k, u ≠
        r i) :
    Commute uPreAlign109Layout.1 (r.embedMatrix M) ∧ Commute uKinAlign0Layout.1 (r.embedMatrix M) :=
  ⟨fwdCirc_comm_embedMatrix_of_disj r (cpWires_pPreAlign109
      (fun _ _ ↦ neR (by
        rw [val_rAlignLayout]
        dsimp
        omega))
      (fun _ ↦ neR (by
        rw [val_rOut40Layout]
        omega))
      (fun j ↦ neR (by
        have := val_rNuc_bounds j
        omega))
      (fun b ↦ neR (by
        rw [(val_rBufLo_hi b).1]
        omega))
      (fun b ↦ neR (by
        rw [(val_rBufLo_hi b).2]
        omega))) M,
   fwdCirc_comm_embedMatrix_of_disj r (cpWires_pKinAlign0
      (fun _ ↦ neR (by
        rw [val_rAlignLayout]
        omega))
      (fun _ ↦ neR (by
        rw [val_rOut40Layout]
        omega))) M⟩
theorem comm_pq : Commute uPreAlign109Layout.1 (projOneQCompactGen scrWLayout) ∧
    Commute uKinAlign0Layout.1 (projOneQCompactGen scrWLayout) :=
  comm_align_of_disj (QRegister.singleton wLocQLayout) (compProj 1) fun hu i e ↦ by
    fin_cases i
    have hv : _ = wLocQLayout.val := congrArg Fin.val e
    rw [val_wLocQLayout] at hv
    omega
theorem cOffPre {k : ℕ} (r : QRegister k dLayout)
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
        (scrSubLGen hpLayout) r)
    (M : Operator (2 ^ k)) : Commute uPreAlign109Layout.1 (r.embedMatrix M) ∧
        Commute uKinAlign0Layout.1 (r.embedMatrix M) :=
  comm_align_of_disj r M fun hu i e ↦ by
    have hb := hoffIndex_bounds_layout hoff i
    have hv := congrArg Fin.val e
    omega
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs PhotochemistrySolution.KetSupport
  PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.SelectDataBuilder
open PhotochemistrySolution.SelectQromKetBridge PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.Stage4KinFull
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb (abpKin14Usel)
attribute [local irreducible] systemQubits_frozen abpKin14Usel
theorem val_rBufLo_hi_nuc (b : Fin 24) : (rBufLo rNucLayout b).val = 5755 + b.val ∧
    (rBufHi rNucLayout b).val = 5779 + b.val :=
  ⟨by
    change (nucRouterWireFn ⟨14 + b.val, _⟩).val = _
    rw [val_nucRouterWireFn]
    dsimp
    split_ifs <;> omega,
   by
     change (nucRouterWireFn ⟨38 + b.val, _⟩).val = _
     rw [val_nucRouterWireFn]
     dsimp
     split_ifs <;> omega⟩
/-- Bit-level action of `uMux27Layout` on `dLayout` computational basis assignments. -/
def muxBits (δ : BitAssignment dLayout) : BitAssignment dLayout :=
    DynCircExt.writeReg δ rMux27Layout (bAxisMux27.evalS (fun j ↦ δ (rMux27Layout j)))
theorem uMux27Layout_mulVec_ket (δ : BitAssignment dLayout) : uMux27Layout.1.mulVec (ket δ) =
    ket (muxBits δ) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  rw [uMux27Layout, embedUnitary_toBracket_ket,
      StructuredCB.toCB_evalBits_eq_evalS bAxisMux27_props.2.2]
  rfl
theorem qft8_conj_phaseDiag_mulVec_ket {N : ℕ} [NeZero (2 ^ N)] (r8 : QRegister 8 N)
    (Qid Umid : Operator.Unitary (2 ^ N)) (hQ : Qid.1 = r8.embedMatrix (QFT.qftMatrix 8))
    (f : BitAssignment N → ℂ) (hf : ∀ γ : BitAssignment N, Umid.1.mulVec (ket γ) = f γ • ket γ)
    (δ : BitAssignment N) : ((Qid⁻¹ * Umid * Qid).1).mulVec (ket δ) =
    (r8.embedMatrix ((QFT.qftMatrix 8)ᴴ * Matrix.diagonal (fun k : Fin 256 ↦
    f (DynCircExt.writeReg δ r8 (basisBits 8 k))) * QFT.qftMatrix 8)).mulVec (ket δ) := by
  have : NeZero (2 ^ 8) := ⟨pow_ne_zero 8 two_ne_zero⟩
  have hQi : (Qid⁻¹).1 = r8.embedMatrix ((QFT.qftMatrix 8)ᴴ) := by
    rw [← mul_one (Qid⁻¹).1, ← show Qid.1 * r8.embedMatrix ((QFT.qftMatrix 8)ᴴ) = 1 by
      rw [hQ, ← r8.embedMatrix_mul, show QFT.qftMatrix 8 * (QFT.qftMatrix 8)ᴴ = 1 from
        congrArg Subtype.val (mul_inv_cancel qftGridUnitary), r8.embedMatrix_one],
      ← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one, one_mul]
  change ((Qid⁻¹).1 * Umid.1 * Qid.1).mulVec (ket δ) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQ, hQi,
      embedMatrix_mulVec_ket_sym r8 (QFT.qftMatrix 8) δ,
    Matrix.mulVec_sum, Matrix.mul_assoc ((QFT.qftMatrix 8)ᴴ), r8.embedMatrix_mul,
        ← Matrix.mulVec_mulVec,
    embedMatrix_mulVec_ket_sym r8 _ δ]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [Matrix.mulVec_smul, hf, smul_smul, Matrix.diagonal_mul, mul_comm]
/-- Combined bit-map of `pKinAlign0`, `uSpeciesSwap50Layout`, and `uMux27Layout` on `dLayout`. -/
def kinFwdBits (δ : BitAssignment dLayout) : BitAssignment dLayout :=
  muxBits (speciesSwapBits (pKinAlign0.fwdBits δ))
/-- Forward conjugation unitary mapping `ket (routedStage0 α c z)` to `ket (kinFwdBits _)`. -/
noncomputable def uKinFwd {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) : Operator.Unitary (2 ^ dLayout) :=
    uMux27Layout * (uSpeciesSwap50Layout * (uKinAlign0Layout * wNoHad o1.uLocal))
theorem conj4_group {G : Type*} [Group G] (a b c d q : G) :
    d⁻¹ * (c⁻¹ * (b⁻¹ * (a⁻¹ * q * a) * b) * c) * d = (a * (b * (c * d)))⁻¹ * q *
        (a * (b * (c * d))) := by group
theorem uKinFwd_mulVec_ket {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {α : BitAssignment dLayout}
    (hScr : ∀ m, α (rScrLayout m) = 0) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    (uKinFwd o1).1.mulVec (ket (routedStage0 α c z)) =
    ket (kinFwdBits (routedKet decodeCoin α c z)) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  let δ := routedKet decodeCoin α c z
  rw [uKinFwd, kinFwdBits, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, wNoHad_mulVec_ket o1 hScr c z,
    show uKinAlign0Layout.1.mulVec (ket δ) =
        ket (pKinAlign0.fwdBits δ) from fwdCirc_mulVec_ket pKinAlign0 δ,
    uSpeciesSwap50Layout_mulVec_ket _ ((fwdBits_not_target targetsIn_pKinAlign0 δ
      (by
        rw [val_rWorkInnerLayout]
        dsimp
        omega)).trans (routedKet_workInner hScr c z ⟨21,
          by omega⟩)),
    uMux27Layout_mulVec_ket]
theorem kinFwdBits_writeReg_z (α : BitAssignment dLayout) (z : BitAssignment 41) :
    kinFwdBits (DynCircExt.writeReg α rInner41Layout z) =
    DynCircExt.writeReg (kinFwdBits α) rInner41Layout z := by
  have h1 : pKinAlign0.fwdBits (writeReg α rInner41Layout z) =
      writeReg (pKinAlign0.fwdBits α) rInner41Layout z := funext fun w ↦ by
    rcases em (w ∈ Set.range rInner41Layout.wires) with ⟨k, rfl⟩ | hw
    · rw [writeReg_apply_reg,
          fwdBits_not_target targetsIn_pKinAlign0 _ (by
            rw [val_rInner41Layout]
            omega),
          writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ w hw]
      by_cases hltw : w.val < 7256
      · exact fwdBits_congr_wires (cpWires_pKinAlign0 (fun _ ↦ by
        rw [val_rAlignLayout]
        omega)
          fun _ ↦
              by
                rw [val_rOut40Layout]
                omega)
                   (fun _ hu ↦ writeReg_rInner41_lt7256 α z hu) w hltw
      · have hw7 : w.val = 7297 := Classical.byContradiction fun _ ↦
            hw ⟨⟨w.val - 7256, by
              have := wire_lt_7298 w
              omega⟩,
          Fin.ext (by
            rw [val_rInner41Layout]
            dsimp
            omega)⟩
        rw [fwdBits_not_target targetsIn_pKinAlign0 _ (by omega),
            fwdBits_not_target targetsIn_pKinAlign0 _ (by omega),
          writeReg_apply_of_not_mem _ _ _ w hw]
  let η := pKinAlign0.fwdBits α
  have h2 : speciesSwapBits (writeReg η rInner41Layout z) =
      writeReg (speciesSwapBits η) rInner41Layout z := funext fun w ↦ by
    rcases em (w ∈ Set.range rInner41Layout.wires) with ⟨k, rfl⟩ | hw
    · rw [writeReg_apply_reg, speciesSwapBits_outside _ (by
      rw [val_rInner41Layout]
      omega)
        (by
          rw [val_rInner41Layout]
          omega), writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ w hw]
      dsimp only [speciesSwapBits]
      rw [writeReg_rInner41_lt7256 η z
          (by
            dsimp [wIsElecKin]
            rw [val_rAlignLayout]
            omega)]
      split_ifs
      · exact writeReg_rInner41_lt7256 η z
            (by
              rw [(val_rBufLo_hi ⟨w.val - 5755, by omega⟩).1]
              omega)
      · exact writeReg_rInner41_lt7256 η z
            (by
              rw [(val_rBufLo_hi_nuc ⟨w.val - 5851, by omega⟩).1]
              omega)
      all_goals exact writeReg_apply_of_not_mem _ _ _ w hw
  let σ := speciesSwapBits η
  have hMuxLt (j : Fin 27) : (rMux27Layout j).val < 7256 := by
    change (mux27WireFn j).val < 7256
    rw [val_mux27WireFn j]
    split_ifs <;> omega
  rw [kinFwdBits, muxBits, h1, h2, show (fun j ↦ writeReg σ rInner41Layout z (rMux27Layout j)) =
    fun j ↦ σ (rMux27Layout j) from funext fun j ↦
        writeReg_rInner41_lt7256 σ z (hMuxLt j), kinFwdBits, muxBits]
  ext w
  rcases em (w ∈ Set.range rInner41Layout.wires) with ⟨k, rfl⟩ | hw
  · rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ rMux27Layout _ _
      fun ⟨j, hj⟩ ↦
          by
            have hv := congrArg Fin.val hj
            have :=
                                                  hMuxLt j
            rw [val_rInner41Layout] at hv
            omega,
      writeReg_apply_reg]
  · rcases em (w ∈ Set.range rMux27Layout.wires) with ⟨j, rfl⟩ | hm
    · rw [writeReg_apply_of_not_mem _ _ _ _ hw, writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ w hw, writeReg_apply_of_not_mem _ rMux27Layout _ w hm,
        writeReg_apply_of_not_mem _ rMux27Layout _ w hm, writeReg_apply_of_not_mem _ _ _ w hw]
theorem fin21_lt_521 : 21 < 521 := by omega
theorem coord24_lt (ax : Fin 3) (b : Fin 8) : 8 * ax.val + b.val < 24 := by omega
theorem mux27_wires_eq : rMux27Layout (wMux 0) = wKinAxis0 ∧ rMux27Layout (wMux 1) = wKinAxis1 ∧
    rMux27Layout (wMux 26) = rWorkInnerLayout ⟨21, fin21_lt_521⟩ ∧
    (∀ b : Fin 8, rMux27Layout (wMux (2 + b.val)) = rPKinLayout b) ∧ (∀ (ax : Fin 3)
    (b : Fin 8), rMux27Layout (wMux (2 + (8 * ax.val + b.val))) = rBufLo rNucLayout ⟨8 * ax.val +
    b.val, coord24_lt ax b⟩) :=
  ⟨rfl, rfl, rfl,
   fun b ↦ Fin.ext (by
     change (mux27WireFn _).val = _
     rw [val_mux27WireFn, val_rPKinLayout,
     show (wMux (2 + b.val)).val = 2 + b.val from Nat.mod_eq_of_lt (by omega)]
     split_ifs <;>
         omega),
   fun ax b ↦ Fin.ext (by
     change (mux27WireFn _).val = _
     rw [val_mux27WireFn,
     (val_rBufLo_hi_nuc ⟨8 * ax.val + b.val, coord24_lt ax b⟩).1,
     show (wMux (2 + (8 * ax.val + b.val))).val = 2 +
         (8 * ax.val + b.val) from Nat.mod_eq_of_lt (by omega)]
     dsimp only
     split_ifs <;> omega)⟩
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end
end

noncomputable section

open QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open PhotochemistrySolution.ZeroNEremAxisSq18
/-- Recursive ripple-borrow boolean specification matching `cmp11Prefix`. -/
def cmpBits : ℕ → (ℕ → Bool) → (ℕ → Bool) → Bool
  | 0, cB, tB => !cB 0 && tB 0
  | k + 1, cB, tB =>
      let p := cmpBits k cB tB
      (!cB (k + 1) && tB (k + 1)) || ((cB (k + 1) == tB (k + 1)) && p)
theorem cmpBits_eq_decide_lt : ∀ (m c t : ℕ),
    cmpBits m c.testBit t.testBit = decide (c % 2 ^ (m + 1) < t % 2 ^ (m + 1))
  | 0, c, t => by
      dsimp only [cmpBits]
      rw [Nat.testBit_zero, Nat.testBit_zero]
      rcases (by omega : c % 2 = 0 ∨ c % 2 = 1) with h1 | h1 <;>
          rcases (by omega : t % 2 = 0 ∨ t % 2 = 1) with h2 | h2 <;>
          simp [h1, h2, show (2 : ℕ) ^ 1 = 2 from rfl]
  | k + 1, c, t => by
      have hsplit : ∀ x : ℕ, x % 2 ^ (k + 2) = x % 2 ^ (k + 1) + 2 ^ (k + 1) *
          (if x.testBit (k + 1) then 1 else 0) := fun x ↦ by
        rw [Nat.mod_pow_succ]
        congr 2
        rw [Nat.testBit_eq_decide_div_mod_eq]
        rcases (by omega : x / 2 ^ (k + 1) % 2 = 0 ∨ x / 2 ^ (k + 1) % 2 = 1) with h | h <;>
            simp [h]
      dsimp only [cmpBits]
      rw [cmpBits_eq_decide_lt k c t]
      have hcl : c % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
      have htl : t % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
      apply Bool.eq_iff_iff.mpr
      rw [hsplit c, hsplit t]
      cases c.testBit (k + 1) <;> cases t.testBit (k + 1) <;> by_cases hlt : c % 2 ^ (k + 1) <
          t % 2 ^ (k + 1) <;> simp [hlt] <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein

namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution
  PhotochemistrySolution.SelectCsa64ProvSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.EvenOctB70 PhotochemistrySolution.PotOracleGen
open PhotochemistrySolution.KinB PhotochemistrySolution.SubregMBUCore
/--
Two-state (`stPre`, `stPost` ) mask-based `wrapDynOnReg` `SubspaceStep` for `Mid_OW` Z-reflection.
-/
theorem subspaceStep_wrapOnReg_mkKetOpW_mask2 {Var : Type} [Fintype Var] [DecidableEq Var]
    {W w n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister w n) (sMask : ℕ)
    (cp : ComputeProg w) (nAnd : ℕ) (hValid : StructuredCB.validProgMask 0 sMask cp = true)
    (hAnd : cp.numAnd = nAnd) (stPre stPost : BitAssignment n → BitAssignment n)
    (phPre phPost : BitAssignment n → ZMod 2) (pMid : DynamicCircuit Var n)
    (hClnPre : ∀ u : Wire w, sMask.testBit u.val = true → ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
    stPre δ (r u) = 0) (hClnPost : ∀ u : Wire w, sMask.testBit u.val = true → ∀ δ,
    (∀ k : Fin W, δ (rWork k) = 0) → stPost δ (r u) = 0)
    (hMid : SubspaceStep (mkKetOpW rWork (fun δ ↦ stepCB r cp.fwdBits (stPre δ)) phPre)
    (mkKetOpW rWork (fun δ ↦ stepCB r cp.fwdBits (stPost δ)) phPost) pMid) :
    SubspaceStep (mkKetOpW rWork stPre phPre) (mkKetOpW rWork stPost phPost)
    (wrapDynOnReg v r cp pMid) ∧ (wrapDynOnReg v r cp pMid).count .T = 4 * nAnd + pMid.count .T ∧
    (wrapDynOnReg v r cp pMid).count .TOFF = pMid.count .TOFF ∧ (∀ S : Wire n → Prop,
    (∀ u, S (r u)) → DynWires S pMid → DynWires S (wrapDynOnReg v r cp pMid)) :=
  subspaceStep_wrapOnReg_vprog2 v rWork r (maskFinset w sMask) cp nAnd (maskFinset_zero w ▸
      StructuredCB.validProg_of_validProgMask
      hValid) hAnd stPre stPost phPre phPost pMid
    (fun u hu ↦ hClnPre u (mem_maskFinset.mp hu))
        (fun u hu ↦ hClnPost u (mem_maskFinset.mp hu)) hMid
/-- Clamp-free `36`-bit Popcount-Bernstein sample `(word512 (4 * idx7 + j)) >>> k`. -/
def y36PopBernNoClamp (word512 : ℕ → ℕ) (isNN : Bool) (d2 : ℕ) (c : Fin 3 → Fin 2048) : ℕ :=
  let p := evenOctIdxT10K isNN d2
  (word512 (4 * idx7OfParts p + popBernJ (t11OfParts p) c)) >>> p.2.2
theorem rJ2OfPers_inj {wPers n : ℕ} (outIdx2 : Fin 2 → Fin wPers)
    (hInj : Function.Injective outIdx2) (rPersT : QRegister wPers n) : Function.Injective (fun q ↦
    rPersT (outIdx2 q)) :=
  fun _ _ e ↦ hInj (rPersT.wires.injective e)
/-- `2`-wire `[j0, j1]` subregister extracted from `rPersT` via injective `outIdx2`. -/
def rJ2OfPers {wPers n : ℕ} (outIdx2 : Fin 2 → Fin wPers) (hInj : Function.Injective outIdx2)
    (rPersT : QRegister wPers n) : QRegister 2 n :=
  ⟨⟨fun q ↦ rPersT (outIdx2 q), rJ2OfPers_inj outIdx2 hInj rPersT⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
end

noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Stage2Xor84
  PhotochemistrySolution.Stage2PotUnld PhotochemistrySolution.Stage2ElecFirst
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg)
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
theorem routedKet_oneHot_portB {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {α : BitAssignment dLayout} (hScr : CleanScr α)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) (b : Fin 24) :
    (routedKet decodeCoin α c z (wPotIsNN rPot0Layout) = 0 →
        routedKet decodeCoin α c z (rBufHi rNucLayout b) = 0) ∧
    (routedKet decodeCoin α c z (wPotIsNN rPot0Layout) = 1 →
        routedKet decodeCoin α c z (rBufHi rElecLayout b) = 0) := by
  let δ₁ := routedStage1 decodeCoin α c z
  let δ₂ := routedStage2 decodeCoin α c z
  obtain ⟨hVN, hKeepE, hVE, hOut, _, hNHi⟩ :=
      validRouter_stage1 (decodeCoin := decodeCoin) hScr c z
  rw [hOut _ (.inl (by simp [rPot0_flags_eq_out40.2.2.2.1, val_rOut40Layout])), hNHi b]
  have notCond {M D : ℕ} (r : RouterReg M D dLayout) (δ) (h0 : δ (rRawHas2 r) = 0) :
      ¬ (routerHas2Eff r δ = 1 ∧ routerIdxMaxVal r δ < M) := by
    rw [routerHas2Eff]
    split_ifs with h <;> simp [h0] at h ⊢
  have checkSec (hN1 hN2 : Bool) (n1 n2 : ℕ) (hE1 hE2 : Bool) (e1 e2 : ℕ)
      (isScreen isPot isKin isNN : Bool) (sp1 aux2 : ℕ)
      (ln1 : n1 < 64 := by
        omega) (ln2 : n2 < 64 := by omega) (le1 : e1 < 256 := by omega) (le2 : e2 < 256 := by omega)
      (impN : isNN = false → hN2 = false := by simp) (impE : isNN = true → hE2 = false := by simp)
      (heq : zeroNEremOutMask (decodeCoin c) =
          packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2) :
      (δ₁ (wPotIsNN rPot0Layout) = 0 → δ₂ (rBufHi rNucLayout b) = 0) ∧ (δ₁ (wPotIsNN rPot0Layout) =
          1 → routedKet decodeCoin α c z (rBufHi rElecLayout b) = 0) := by
    have F :=
        packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScreen isPot isKin isNN sp1 aux2
        ln1 ln2 le1 le2 δ₁
      (fun j ↦ (writeReg_apply_reg _ rOut40Layout _ j).trans (by simp [outMaskBits40, heq]))
    have hNNVal := F.2.2.2.2.2.2.2.2.2.2.2.1
    exact ⟨fun h0 ↦ ((routerSwapBits_spec rNucLayout hVN).2.1 b).trans
        (dite_eq_right (notCond rNucLayout δ₁ (F.2.1.trans
            (by simp [impN (by cases isNN <;> simp_all)])))),
      fun h1 ↦ ((routerSwapBits_spec rElecLayout hVE).2.1 b).trans
        (dite_eq_right (notCond rElecLayout δ₂ ((hKeepE _).trans (F.2.2.2.2.2.1.trans
            (by simp [impE (by cases isNN <;> simp_all)])))))⟩
  cases hc : decodeCoin c with
  | idle =>
        exact checkSec false false 0 0 false false 0 0 false false false false 0 0 (heq := hc ▸ rfl)
  | ee n1 e1 e2 =>
        exact checkSec true false n1.val 0 true true e1.val e2.val true true false false (nucSpecies
        n1).val 0 (heq := hc ▸ rfl)
  | nn n1 n2 e1 =>
        exact checkSec true true n1.val n2.val true false e1.val 0 true true false true (nucSpecies
        n1).val (nucSpecies n2).val (heq := hc ▸ rfl)
  | en n1 e1 =>
        exact checkSec true false n1.val 0 true false e1.val 0 false true false false (nucSpecies
        n1).val 0 (heq := hc ▸ rfl)
  | kin i ax =>
      by_cases hi : i.val < 47
      · exact checkSec true false i.val 0 false false 0 0 false false true false 0 ax.val (heq := by
          simp [hc, zeroNEremOutMask, hi])
      · exact checkSec false false 0 0 true false (i.val -
            47) 0 false false true false 0 ax.val (heq := by simp [hc, zeroNEremOutMask, hi])
theorem rBufHi_inj {M D n : ℕ} (r48 : RouterReg M D n) : Function.Injective (rBufHi r48) :=
  fun _ _ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (r48.wires.injective e)
    dsimp [rBufHi] at hv
    omega)
/-- Clamped bit-assignment enforcing the one-hot `PortB` invariant identically on all `δ`. -/
def clampOneHot {n : ℕ} (rTot : QRegister dLayout n) (δ : BitAssignment n) : BitAssignment n :=
    writeReg (writeReg δ (rTot.compose ⟨rBufHi rElecLayout, rBufHi_inj rElecLayout⟩)
    (fun b ↦ if δ (rTot (wPotIsNN rPot0Layout)) == 1 then 0 else δ (rTot (rBufHi rElecLayout b))))
    (rTot.compose ⟨rBufHi rNucLayout, rBufHi_inj rNucLayout⟩)
    (fun b ↦ if δ (rTot (wPotIsNN rPot0Layout)) == 1 then δ (rTot (rBufHi rNucLayout b)) else 0)
end QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB
namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectCompactRot34
open PhotochemistrySolution.OvBidir PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.QubitizationWalkSem PhotochemistrySolution.SelectDataBuilder
  PhotochemistrySolution.XMeasChunkQromUnldA
open PhotochemistrySolution.Stage4Cluster22Xnor PhotochemistrySolution.TopSelectBridge
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
/- ## Section 1: Retired Top-3 Phase-Gradient Slice `locGrad3Hi` (`{5647, 5648, 5649}`) -/
theorem hSliceGrad3Hi_refl {ancW : ℕ} (hAnc : 100 ≤ ancW) : 31 + 3 ≤ ancW := by omega
/-- Top-3 retired phase-gradient slice `ancIdx 31..33` (`rCat[5..7]`). -/
def locGrad3HiGen_refl {ancW : ℕ} (hAnc : 100 ≤ ancW) : QRegister 3 (systemQubits_frozen + ancW) :=
  (locAncGen ancW).slice 31 3 (hSliceGrad3Hi_refl hAnc)
/-- Compact-layout top-3 retired phase-gradient slice `ancIdx 31..33`. -/
def locGrad3HiCompactGen_refl (scrW : ℕ) : QRegister 3 (totDimCompactGen scrW) :=
  locGrad3HiGen_refl (hAncCompact scrW)
/-- Concrete `dLayout = 7298` top-3 retired phase-gradient register `{5647, 5648, 5649}`. -/
abbrev locGrad3HiLayout_refl : QRegister 3 dLayout := locGrad3HiCompactGen_refl scrWLayout
theorem val_locGrad3HiLayout_refl (j : Fin 3) : (locGrad3HiLayout_refl j).val = 5647 + j.val := by
  fin_cases j <;> rfl
attribute [local reducible] totDimCompactGen
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr PgBase.phaseGradientState phaseFlipUnitary
/- ## Section 2: `signedPermUnitary` Commutation with Disjoint `embedMatrix` -/
theorem signedPermUnitary_comm_embedMatrix {k n : ℕ} (f : BitAssignment n → BitAssignment n)
    (hf : ∀ δ, f (f δ) = δ) (φ : BitAssignment n → ZMod 2) (r : QRegister k n)
    (hWriteF : ∀ (δ : BitAssignment n) (η : BitAssignment k),
      f (writeReg δ r η) = writeReg (f δ) r η)
    (hWriteΦ : ∀ (δ : BitAssignment n) (η : BitAssignment k), φ (writeReg δ r η) = φ δ)
    (M : Operator (2 ^ k)) :
    Commute (signedPermUnitary (equivOfInvol f hf) φ).1 (r.embedMatrix M) := by
  have hRead (δ : BitAssignment n) : readRegIdx r (f δ) = readRegIdx r δ :=
    congrArg (basisBitsEquiv k).symm (funext fun j ↦ by
      simpa only [readRegIdx, (basisBitsEquiv n).apply_symm_apply] using
        (congrFun ((congrArg f (writeReg_self r δ).symm).trans (hWriteF δ _)) (r j)).trans
          (writeReg_apply_reg (f δ) r _ j))
  refine Commute.mul_left (matrix_ext_ket fun δ ↦ ?_)
    (RouterSelectWiringB.comm_embedMatrix_of_isPhaseDiag (phaseFlipUnitary_mulVec_ket φ) r M
        hWriteΦ)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, embedMatrix_mulVec_ket_sym,
      permUnitary_mulVec_ket,
    equivOfInvol_apply, embedMatrix_mulVec_ket_sym, Matrix.mulVec_sum, hRead δ]
  exact Finset.sum_congr rfl fun _ _ ↦ by
    rw [Matrix.mulVec_smul, permUnitary_mulVec_ket, equivOfInvol_apply, hWriteF]
/- ## Section 3: Reflected 4-Port Stage-4 Potential Unitary on `rPot0Layout` -/
/--
Active gate boolean on a 4-port potential register (`locQ && isPot` on `Csel` , `isPot` on `Usel` ).
-/
def potGateActive4 {W n : ℕ} (isCsel : Bool) (r : QRegister (146 + W) n) (δ : BitAssignment n) :
    Bool :=
  if isCsel then (δ (wPotLocQ r) == 1) && (δ (wPotIsPot r) == 1)
  else (δ (wPotIsPot r) == 1)
/-- Classical inner-coin reflection on a 4-port potential register. -/
def potReflSwap4 {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) {W n : ℕ}
    (isCsel : Bool) (r : QRegister (146 + W) n) (δ : BitAssignment n) : BitAssignment n :=
  if potGateActive4 isCsel r δ then
    writeReg δ (rPotCoin41 r) (potOracleCoinEval spec.coinSwap r δ)
  else δ
/-- Phase bit of a reflected 4-port potential unitary on `r : QRegister (146 + W) n`. -/
def potReflPh4 {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) {W n : ℕ}
    (isCsel : Bool) (r : QRegister (146 + W) n) (δ : BitAssignment n) : ZMod 2 :=
    (if isCsel then δ (wPotLocQ r) * δ (wPotIsPot r) else δ (wPotIsPot r)) *
    potOracleBitEval spec.phaseBit r δ
theorem potReflSwap4_invol_and_ph {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect)
    {W n : ℕ} (isCsel : Bool) (r : QRegister (146 + W) n) (δ : BitAssignment n) :
    potReflSwap4 spec isCsel r (potReflSwap4 spec isCsel r δ) = δ ∧
      potReflPh4 spec isCsel r (potReflSwap4 spec isCsel r δ) =
        potReflPh4 spec isCsel r δ := by
  have hNonCoin (z' : BitAssignment 41) (k : ℕ) (hk : k < 105 := by
    omega) : writeReg δ (rPotCoin41 r) z' (r ⟨k, by omega⟩) = δ (r ⟨k, by omega⟩) :=
    writeReg_apply_of_not_mem δ (rPotCoin41 r) z' _ fun ⟨m, hm⟩ ↦ by
      have hv : 105 + m.val = k := congrArg Fin.val (r.wires.injective hm)
      omega
  have hC24 (z' : BitAssignment 41) (off : ℕ) (h0 : off + 24 ≤ 146 + W) (hle : off ≤ 81 := by
    omega) :
      coordOfReg24 (r.compose (QRegister.block off 24 h0)) (writeReg δ (rPotCoin41 r) z') =
          coordOfReg24 (r.compose (QRegister.block off 24 h0)) δ :=
    funext fun ax ↦
        congrArg byteOfBits (funext fun b ↦ hNonCoin z' (off + (8 * ax.val + b.val))
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (coordOfReg24_lt ax b) off) (by omega)))
  by_cases hg : potGateActive4 isCsel r δ = true
  · let z' := potOracleCoinEval spec.coinSwap r δ
    let δ' := writeReg δ (rPotCoin41 r) z'
    obtain ⟨hSwapEq, hPhEq⟩ : potOracleCoinEval spec.coinSwap r δ' = (fun m ↦ δ (rPotCoin41 r m)) ∧
        potOracleBitEval spec.phaseBit r δ' = potOracleBitEval spec.phaseBit r δ := by
      dsimp only [potOracleCoinEval, potOracleBitEval, δ']
      rw [hNonCoin z' 1, hNonCoin z' 4, hNonCoin z' 5, hNonCoin z' 6, hNonCoin z' 7, hNonCoin z' 8,
        hC24 z' 9 potBlkNucA_le, hC24 z' 33 potBlkNucB_le, hC24 z' 57 potBlkElecA_le,
            hC24 z' 81 potBlkElecB_le,
        show (fun m : Fin 41 ↦ δ' (rPotCoin41 r m)) = z' from funext fun m ↦
            writeReg_apply_reg δ (rPotCoin41 r) z' m]
      exact ⟨spec.coinSwap_invol _ _ _ _ _ _ _ _ _, spec.phaseBit_coinSwap _ _ _ _ _ _ _ _ _⟩
    rw [show potReflSwap4 spec isCsel r δ = δ' by simp [potReflSwap4, hg, δ', z']]
    refine ⟨?_,
        by
          dsimp only [potReflPh4, wPotLocQ, wPotIsPot, δ']
          rw [hPhEq, hNonCoin z' 0,
             hNonCoin z' 2]⟩
    rw [potReflSwap4, ite_eq_left (by
      dsimp only [potGateActive4, wPotLocQ, wPotIsPot, δ']
      rwa [hNonCoin z' 0, hNonCoin z' 2]),
          hSwapEq]
    exact (KinBellMux6Step.writeReg_idem_kbm (rPotCoin41 r) δ z' _).trans (writeReg_self
        (rPotCoin41 r) δ)
  · simp [potReflSwap4, Bool.eq_false_iff.mpr hg]
theorem potReflSwap4_invol {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) {W n : ℕ}
    (isCsel : Bool) (r : QRegister (146 + W) n) (δ : BitAssignment n) :
    potReflSwap4 spec isCsel r (potReflSwap4 spec isCsel r δ) = δ :=
        (potReflSwap4_invol_and_ph spec isCsel r δ).1
/-- Reflected 4-port Stage-4 potential unitary (`isCsel : Bool`) on `rPot0Layout`. -/
def uPotReflZeroNErem {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect)
    (isCsel : Bool) : Unitary (2 ^ dLayout) :=
  signedPermUnitary
    (equivOfInvol (potReflSwap4 spec isCsel rPot0Layout)
      (potReflSwap4_invol spec isCsel rPot0Layout))
    (potReflPh4 spec isCsel rPot0Layout)
/-- Unguarded/ideal reflected Stage-4 potential unitary on `dLayout`. -/
abbrev uPotReflIdealZeroNErem {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) :
    Unitary (2 ^ dLayout) :=
  uPotReflZeroNErem spec false
/-- Cat-guarded (`wLocQLayout`) reflected Stage-4 potential unitary on `dLayout`. -/
abbrev uPotReflCatCselZeroNErem {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect) :
    Unitary (2 ^ dLayout) := uPotReflZeroNErem spec true
theorem uPotReflZeroNErem_mulVec_ket {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect)
    (isCsel : Bool) (δ : BitAssignment dLayout) :
    (uPotReflZeroNErem spec isCsel).1.mulVec (ket δ) =
        bitSign (potReflPh4 spec isCsel rPot0Layout δ) • ket (potReflSwap4 spec isCsel rPot0Layout
        δ) :=
  signedPermUnitary_mulVec_ket _ _ δ
theorem uPotReflZeroNErem_sq_one {potExpect : PotExpectFn} (spec : ReflPotSliceSpec potExpect)
    (isCsel : Bool) : (uPotReflZeroNErem spec isCsel).1 * (uPotReflZeroNErem spec isCsel).1 = 1 :=
  signedPermUnitary_sq_one _ _ (fun δ ↦ (potReflSwap4_invol_and_ph spec isCsel rPot0Layout δ).1)
      (fun δ ↦ (potReflSwap4_invol_and_ph spec isCsel rPot0Layout δ).2)
theorem uPotReflCatCselZeroNErem_eq_ctrl {potExpect : PotExpectFn}
    (spec : ReflPotSliceSpec potExpect) :
    (uPotReflCatCselZeroNErem spec).1 = (1 - projOneQCompactGen scrWLayout) +
        projOneQCompactGen scrWLayout * (uPotReflIdealZeroNErem spec).1 := by
  have hw0 : wPotLocQ rPot0Layout = wLocQLayout := Fin.ext (by
    change (potZeroNEremWireFn 0 pot0_le_690 ⟨0, potIdx0_lt⟩).val = wLocQLayout.val
    rw [val_potZeroNEremWireFn pot0_le_690 ⟨0, potIdx0_lt⟩, val_wLocQLayout]
    dsimp only
    split_ifs <;> omega)
  refine matrix_ext_ket fun δ ↦ ?_
  rw [uPotReflZeroNErem_mulVec_ket, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec]
  have hP1 (α : BitAssignment dLayout) :
      (projOneQCompactGen scrWLayout).mulVec (ket α) = if α wLocQLayout = 1 then ket α else 0 := by
    rw [show projOneQCompactGen scrWLayout = pBit1 wLocQLayout from eq_sub_of_add_eq'
      ((Fin.sum_univ_two (QRegister.singleton wLocQLayout).basisOutcomeProjector).symm.trans
        (QRegister.sum_basisOutcomeProjector (QRegister.singleton wLocQLayout)))]
    rcases DynCircExt.bit_cases (α wLocQLayout) with h0 | h1
    · rw [pBit1, Matrix.sub_mulVec, Matrix.one_mulVec, pBit0_ket h0, sub_self,
          ite_eq_right (h0 ▸ zero_ne_one)]
    · rw [pBit1_ket h1, ite_eq_left h1]
  rw [hP1 δ, uPotReflZeroNErem_mulVec_ket, Matrix.mulVec_smul, hP1 _,
    show potReflSwap4 spec false rPot0Layout δ wLocQLayout = δ wLocQLayout by
      dsimp only [potReflSwap4]
      split_ifs
      · exact writeReg_apply_of_not_mem δ (rPotCoin41 rPot0Layout) _ _ fun ⟨m, hm⟩ ↦
          absurd (congrArg Fin.val (rPot0Layout.wires.injective (hw0 ▸ hm)) : 105 + m.val = 0)
              (by omega)
      · rfl]
  rcases DynCircExt.bit_cases (δ wLocQLayout) with hq | hq <;>
    simp [potReflSwap4, potGateActive4, potReflPh4, hw0, hq, bitSign_zero]
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.Stage2Xor84 PhotochemistrySolution.Stage2PotUnld
  PhotochemistrySolution.Stage2ElecFirst PhotochemistrySolution.SortedRouterSpec
open PhotochemistrySolution.Coin70Lift PhotochemistrySolution.Sub5885
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
theorem nat_leftInv_of_all_lt {N : ℕ} {f g : ℕ → ℕ}
    (h : (List.range N).all (fun k ↦ g (f k) == k) = true) {k : ℕ} (hk : k < N) :
    g (f k) = k := by
  exact beq_iff_eq.mp (List.all_eq_true.mp h k (List.mem_range.mpr hk))
/-- `MuxD1`-ordered private rank bijection on `0 .. 155` for `(47, 6)` (`0` `Classical`). -/
def privRank156Sub (k : ℕ) : ℕ :=
    if k < 4 then 101 + k else if k < 6 then 153 + (k - 4) else if k < 65 then k - 6 else if k <
    112 then 106 + (k - 65) else if k < 113 then 155 else if k < 114 then 105 else if k <
    119 then 59 + (k - 114) else if k < 143 then 76 + (k - 119) else if k < 144 then 100 else 64 +
    (k - 144)
theorem privRank156Sub_lt {k : ℕ} (hk : k < 156) : privRank156Sub k < 156 := by
  unfold privRank156Sub
  split_ifs <;> omega
/-- Inverse of `privRank156Sub` on `0 .. 155` (`0` `Classical`). -/
def privUnrank156Sub (r : ℕ) : ℕ :=
    if r < 59 then 6 + r else if r < 64 then 114 + (r - 59) else if r < 76 then 144 +
    (r - 64) else if r < 100 then 119 + (r - 76) else if r < 101 then 143 else if r < 105 then r -
    101 else if r < 106 then 113 else if r < 153 then 65 + (r - 106) else if r < 155 then 4 +
    (r - 153) else 112
theorem privUnrank156Sub_rank {k : ℕ} (hk : k < 156) : privUnrank156Sub (privRank156Sub k) = k :=
  nat_leftInv_of_all_lt (by decide +kernel) hk
theorem privRank156Sub_inj {a b : ℕ} (ha : a < 156) (hb : b < 156)
    (h : privRank156Sub a = privRank156Sub b) : a =
    b := by rw [← privUnrank156Sub_rank ha, ← privUnrank156Sub_rank hb, h]
theorem nucPrivIdx_lt (k : Fin 156) : 1238 + k.val < routerWidth 47 6 := by
  have _ := k.isLt
  rw [hNW1394]
  omega
theorem nucSub_lo_lt {rk : ℕ} (h : rk < 33) : 30 + rk < scrLLayout := by
  dsimp [scrLLayout]
  omega
theorem nucSub_hi_lt (i : Fin (routerWidth 47 6)) : 297 + (privRank156Sub (i.val - 1238) - 33) <
    scrLLayout := by
  have _ := privRank156Sub_lt (sub1238_lt156 i)
  dsimp [scrLLayout]
  omega
/--
Nuclear `MuxD1` wire map placing `rk < 33` in `[5680..5712]` and `rk >= 33` in
`[5947..6069]`.
-/
def nucSubWireFn (i : Fin (routerWidth 47 6)) : Wire dLayout :=
  if _ : i.val < 1238 then nucRouterWireFn i
  else
    let rk := privRank156Sub (i.val - 1238)
    if hrk : rk < 33 then rScrLayout ⟨30 + rk, nucSub_lo_lt hrk⟩
    else rScrLayout ⟨297 + (rk - 33), nucSub_hi_lt i⟩
theorem val_nucSubWireFn (i : Fin (routerWidth 47 6)) : (nucSubWireFn i).val = if i.val <
    14 then 5715 + i.val else if i.val < 110 then 5755 + (i.val - 14) else if i.val <
    1238 then i.val - 110 else if privRank156Sub (i.val - 1238) < 33 then 5680 +
    privRank156Sub (i.val - 1238) else 5947 + (privRank156Sub (i.val - 1238) - 33) := by
  have _ : i.val < 1394 := hNW1394 ▸ i.isLt
  dsimp only [nucSubWireFn]
  split_ifs <;> simp only [val_nucRouterWireFn, val_rScrLayout] <;> (try split_ifs) <;> omega
theorem nucSubWireFn_inj : Function.Injective nucSubWireFn := fun a b h ↦ by
  have ha : a.val < 1394 := hNW1394 ▸ a.isLt
  have hb : b.val < 1394 := hNW1394 ▸ b.isLt
  have hra :=
      privRank156Sub_lt (sub1238_lt156 a)
  have hrb := privRank156Sub_lt (sub1238_lt156 b)
  have hv := (val_nucSubWireFn a).symm.trans ((congrArg Fin.val h).trans (val_nucSubWireFn b))
  split_ifs at hv <;> exact Fin.ext (by
    first | omega | (
            have := privRank156Sub_inj (sub1238_lt156 a) (sub1238_lt156 b)
                       (by omega)
            omega))
/--
Sub-`368` nuclear `RouterReg 47 6 dLayout` supporting `PubCtrlLo` (`258`), `Core` (`275`),
`Phase0Tight` (`299`), `Phase0` (`300`), `UsedXorTight KN` (`305 + KN`), and all wires (`355`).
-/
def rNucSub : RouterReg 47 6 dLayout := ⟨⟨nucSubWireFn, nucSubWireFn_inj⟩⟩
theorem rNucSub_eq_of_lt1238 {i : Fin (routerWidth 47 6)} (hi : i.val < 1238) : rNucSub i =
    rNucLayout i := by
  exact dite_eq_left hi
theorem rNucSub_loc_scr (k : Fin 156) : ∃ m : Fin scrLLayout, rNucSub ⟨1238 + k.val,
    nucPrivIdx_lt k⟩ = rScrLayout m ∧ (m.val < 65 ∨ 297 ≤ m.val) := by
  change ∃ m : Fin scrLLayout, nucSubWireFn _ = rScrLayout m ∧ _
  dsimp only [nucSubWireFn]
  split_ifs
  · omega
  · exact ⟨_, rfl, .inl (by
    dsimp
    omega)⟩
  · exact ⟨_, rfl, .inr (by
    dsimp
    omega)⟩
/-- `MuxD1`-ordered private rank bijection on `0 .. 453` for `(187, 8)` (`0` `Classical`). -/
def privRank454Sub (k : ℕ) : ℕ :=
    if k < 4 then 259 + k else if k < 6 then 451 + (k - 4) else if k < 209 then k - 6 else if k <
    396 then 264 + (k - 209) else if k < 397 then 453 else if k < 398 then 263 else if k <
    405 then 203 + (k - 398) else if k < 437 then 226 + (k - 405) else if k <
    438 then 258 else 210 + (k - 438)
theorem privRank454Sub_lt {k : ℕ} (hk : k < 454) : privRank454Sub k < 454 := by
  unfold privRank454Sub
  split_ifs <;> omega
/-- Inverse of `privRank454Sub` on `0 .. 453` (`0` `Classical`). -/
def privUnrank454Sub (r : ℕ) : ℕ :=
    if r < 203 then 6 + r else if r < 210 then 398 + (r - 203) else if r < 226 then 438 +
    (r - 210) else if r < 258 then 405 + (r - 226) else if r < 259 then 437 else if r < 263 then r -
    259 else if r < 264 then 397 else if r < 451 then 209 + (r - 264) else if r < 453 then 4 +
    (r - 451) else 396
theorem privUnrank454Sub_rank {k : ℕ} (hk : k < 454) : privUnrank454Sub (privRank454Sub k) = k :=
  nat_leftInv_of_all_lt (by decide +kernel) hk
theorem privRank454Sub_inj {a b : ℕ} (ha : a < 454) (hb : b < 454)
    (h : privRank454Sub a = privRank454Sub b) : a =
    b := by rw [← privUnrank454Sub_rank ha, ← privUnrank454Sub_rank hb, h]
theorem elecSub_sub_lt (j : Fin (routerWidth 187 8)) (h : ¬ j.val < 4602) : j.val - 4602 < 454 := by
  have _ : j.val < 5056 := hEW5056 ▸ j.isLt
  omega
theorem elecSub_mid_lt {rk : ℕ} (h : rk < 129) : 105 + (rk - 33) < scrLLayout := by
  dsimp [scrLLayout]
  omega
theorem elecSub_hi_lt {rk : ℕ} (h : rk < 454) : 297 + (rk - 129) < scrLLayout := by
  dsimp [scrLLayout]
  omega
/--
Shared 454-wire private scratch pool `[5680..5712] u [5755..5850] u [5947..6271]` used by both
`rElecBorrow96` and `rElecSub`.
-/
def elecPrivScrOfRank (rk : Fin 454) : Wire dLayout :=
  if h1 : rk.val < 33 then rScrLayout ⟨30 + rk.val, nucSub_lo_lt h1⟩
  else if h2 : rk.val < 129 then rScrLayout ⟨105 + (rk.val - 33), elecSub_mid_lt h2⟩
  else rScrLayout ⟨297 + (rk.val - 129), elecSub_hi_lt rk.isLt⟩
/-- Electronic `MuxD1` wire map packing `privRank454Sub (j - 4602)` across `elecPrivScrOfRank`. -/
def elecSubWireFn (j : Fin (routerWidth 187 8)) : Wire dLayout :=
    if h : j.val < 4602 then elecRouterWireFn j else elecPrivScrOfRank ⟨privRank454Sub (j.val -
    4602), privRank454Sub_lt (elecSub_sub_lt j h)⟩
theorem val_elecSubWireFn (j : Fin (routerWidth 187 8)) : (elecSubWireFn j).val = if j.val <
    18 then 5729 + j.val else if j.val < 114 then 5851 + (j.val - 18) else if j.val <
    4602 then 1128 + (j.val - 114) else if privRank454Sub (j.val - 4602) < 33 then 5680 +
    privRank454Sub (j.val - 4602) else if privRank454Sub (j.val - 4602) < 129 then 5755 +
    (privRank454Sub (j.val - 4602) - 33) else 5947 + (privRank454Sub (j.val - 4602) - 129) := by
  have _ : j.val < 5056 := hEW5056 ▸ j.isLt
  dsimp only [elecSubWireFn, elecPrivScrOfRank]
  split_ifs <;> simp only [val_elecRouterWireFn, val_rScrLayout] <;> (try split_ifs) <;> omega
theorem elecSubWireFn_inj : Function.Injective elecSubWireFn := fun a b h ↦ by
  have ha : a.val < 5056 := hEW5056 ▸ a.isLt
  have hb : b.val < 5056 := hEW5056 ▸ b.isLt
  have hra := privRank454Sub_lt (show a.val - 4602 < 454 by omega)
  have hrb := privRank454Sub_lt (show b.val - 4602 < 454 by omega)
  have hv := (val_elecSubWireFn a).symm.trans ((congrArg Fin.val h).trans (val_elecSubWireFn b))
  split_ifs at hv <;> exact Fin.ext (by
    first | omega | (
            have := privRank454Sub_inj (a := a.val - 4602) (b := b.val - 4602) (by omega)
                       (by omega) (by omega)
            omega))
/--
Sub-`368` electronic `RouterReg 187 8 dLayout` unlocking `329 <= wWork` (`UsedMuxD1Core`,
`-39 Q`), `361 <= wWork` (`UsedMuxD1Phase0Tight`, `-7 Q`), `362 <= wWork` (`UsedMuxD1Phase0`,
`-6 Q`), and `367 + KE <= wWork` (`UsedXorTight KE`, `-1 Q` at `KE = 0`).
-/
def rElecSub : RouterReg 187 8 dLayout := ⟨⟨elecSubWireFn, elecSubWireFn_inj⟩⟩
theorem rElecSub_eq_of_lt4602 {j : Fin (routerWidth 187 8)} (hj : j.val < 4602) : rElecSub j =
    rElecLayout j := by
  exact dite_eq_left hj
theorem elecPrivScrOfRank_scr (rk : Fin 454) :
    ∃ m : Fin scrLLayout, elecPrivScrOfRank rk = rScrLayout m ∧ (m.val < 65 ∨ 105 ≤ m.val) := by
  dsimp only [elecPrivScrOfRank]
  split_ifs
  · exact ⟨_, rfl, .inl (by
    dsimp
    omega)⟩
  all_goals exact ⟨_, rfl, .inr (by
    dsimp
    omega)⟩
theorem rElecSub_loc_scr (j : Fin 454) : ∃ m : Fin scrLLayout, rElecSub ⟨4602 + j.val,
    privIdx_lt j⟩ = rScrLayout m ∧ (m.val < 65 ∨ 105 ≤ m.val) := by
  change ∃ m : Fin scrLLayout, elecSubWireFn _ = rScrLayout m ∧ _
  dsimp only [elecSubWireFn]
  split_ifs
  · omega
  · exact elecPrivScrOfRank_scr _
/-- Public-role equality across two `RouterReg M D n` instances (`rHas1` through `rSys`). -/
abbrev MuxD1RolesEq {M D n : ℕ} (r₁ r₂ : RouterReg M D n) : Prop :=
    rHas1 r₁ = rHas1 r₂ ∧ rRawHas2 r₁ = rRawHas2 r₂ ∧ rIdx1 r₁ = rIdx1 r₂ ∧ rIdx2 r₁ = rIdx2 r₂ ∧
    rBufLo r₁ = rBufLo r₂ ∧ rBufHi r₁ = rBufHi r₂ ∧ rHA r₁ = rHA r₂ ∧ rHB r₁ = rHB r₂ ∧ rSys r₁ =
    rSys r₂
structure ValidMuxD1Stage2Regs (rNuc : RouterReg 47 6 dLayout)
    (rElec : RouterReg 187 8 dLayout) : Prop where
  pubNuc : ∀ i : Fin (routerWidth 47 6), i.val < 1238 → rNuc i = rNucLayout i
  privNuc : ∀ k : Fin 156, ∃ m : Fin scrLLayout,
    rNuc ⟨1238 + k.val, nucPrivIdx_lt k⟩ = rScrLayout m ∧ (m.val < 65 ∨ 297 ≤ m.val)
  pubElec : ∀ j : Fin (routerWidth 187 8), j.val < 4602 → rElec j = rElecLayout j
  privElec : ∀ j : Fin 454, ∃ m : Fin scrLLayout,
    rElec ⟨4602 + j.val, privIdx_lt j⟩ = rScrLayout m ∧ (m.val < 65 ∨ 105 ≤ m.val)
theorem validMuxD1Stage2Regs_sub : ValidMuxD1Stage2Regs rNucSub rElecSub :=
    ⟨fun _ hi ↦ rNucSub_eq_of_lt1238 hi, rNucSub_loc_scr, fun _ hj ↦ rElecSub_eq_of_lt4602 hj,
    rElecSub_loc_scr⟩
theorem muxD1RolesEq_of_pub {M D n : ℕ} {r₁ r₂ : RouterReg M D n}
    (hp : ∀ i : Fin (routerWidth M D), i.val < basePub M D → r₁ i = r₂ i) :
    MuxD1RolesEq r₁ r₂ := by
  refine ⟨hp _ ?_, hp _ ?_, funext fun _ ↦ hp _ ?_, funext fun _ ↦ hp _ ?_, funext fun _ ↦ hp _ ?_,
    funext fun _ ↦ hp _ ?_, funext fun _ ↦ hp _ ?_, funext fun _ ↦ hp _ ?_, funext fun _ ↦
        funext fun _ ↦ hp _ ?_⟩
  all_goals
    dsimp [basePub]
    omega
theorem ValidMuxD1Stage2Regs.rolesNuc {rNuc : RouterReg 47 6 dLayout}
    {rElec : RouterReg 187 8 dLayout} (h : ValidMuxD1Stage2Regs rNuc rElec) :
    MuxD1RolesEq rNuc rNucLayout := muxD1RolesEq_of_pub h.pubNuc
theorem ValidMuxD1Stage2Regs.rolesElec {rNuc : RouterReg 47 6 dLayout}
    {rElec : RouterReg 187 8 dLayout} (h : ValidMuxD1Stage2Regs rNuc rElec) :
    MuxD1RolesEq rElec rElecLayout := muxD1RolesEq_of_pub h.pubElec
theorem ValidMuxD1Stage2Regs.val_rNuc_bounds {rNuc : RouterReg 47 6 dLayout}
    {rElec : RouterReg 187 8 dLayout} (h : ValidMuxD1Stage2Regs rNuc rElec)
    (i : Fin (routerWidth 47 6)) : (rNuc i).val < 1128 ∨ (5650 ≤ (rNuc i).val ∧ (rNuc i).val <
    5729) ∨ (5755 ≤ (rNuc i).val ∧ (rNuc i).val < 5851) ∨ 5947 ≤ (rNuc i).val := by
  have _ : i.val < 1394 := hNW1394 ▸ i.isLt
  by_cases hi : i.val < 1238
  · have hv := (congrArg Fin.val (h.pubNuc i hi)).trans (val_nucRouterWireFn i)
    split_ifs at hv <;> omega
  · obtain ⟨m, hm, _⟩ := h.privNuc ⟨i.val - 1238, by omega⟩
    rw [show i = ⟨1238 + (i.val - 1238), _⟩ from Fin.ext (by
      dsimp
      omega), hm,
        val_rScrLayout] <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1
end

noncomputable section
set_option exponentiation.threshold 8192
section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
open QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local irreducible]
    QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc.ancWOfScr systemQubits_frozen
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.UnembedO3Bridge
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.TelescopeSlice
  PhotochemistrySolution.BlockApprox PhotochemistrySolution.Stage2Xor84
open PhotochemistrySolution.Stage2QromMux
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
attribute [local irreducible] uRouterSwapConj
theorem zeroProj_absorb {L n : ℕ} [NeZero (2 ^ n)] (rTot : QRegister dLayout n)
    (rSub : QRegister L dLayout) (M : Operator (2 ^ n))
    (hInM : ∀ ξ : BitAssignment n, inKetPred (fun ζ ↦ ∀ k : Fin L, ζ ((rTot.compose rSub) k) = 0)
        (M.mulVec (ket ξ))) : (rTot.compose rSub).basisOutcomeProjector 0 * M = M :=
  ((supportedOn_of_inKetPred hInM) ((rTot.compose rSub).basisOutcomeProjector 0) 1
    fun ζ hζ ↦
        by rw [SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left hζ,
             Matrix.one_mulVec]).trans (Matrix.one_mul M)
theorem w1Ket {n wIn : ℕ} [NeZero (2 ^ dLayout)]
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (rTot : QRegister dLayout n) (o1 : Stage1ZeroNEremLayout wIn decodeCoin)
    (η : BitAssignment n) (hScr : CleanScr (fun i ↦ η (rTot i))) :
    let α := fun i ↦ η (rTot i)
    let c := outerCoinOf82 (fun i ↦ α (rLcu82Layout i))
    let z := innerBitsOf82 (fun i ↦ α (rLcu82Layout i))
    (rTot.embedUnitary o1.uLocal).1.mulVec (ket η) =
        ket (DynCircExt.writeReg η rTot (routedStage1 decodeCoin α c z)) := by
  intro α c z
  refine embedMatrix_ket_eq_writeReg rTot o1.uLocal.1 η ((o1.ket_of_clean c α (fun k ↦ ?_)
    (fun j ↦ hScr ⟨65 + j.val, by
      simp [scrLLayout]
      omega⟩)
    fun k ↦
        (rScrCompact1493_sub_scr k).choose_spec ▸ hScr _).trans
        (by
          rw [routedStage1, routedStage0_self]
          rfl))
  rw [← routedStage0_self α, show rOuter41Layout k = rLcu82Layout ⟨k.val, fin41_lt_mLayout k⟩
    from Fin.ext (by rw [val_rOuter41Layout, val_rLcu82Layout])]
  exact (DynCircExt.writeReg_apply_reg α rLcu82Layout _ _).trans (pack82_apply_lt c z k)
theorem routerChain {n wIn : ℕ} [NeZero (2 ^ n)]
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (rTot : QRegister dLayout n) (rElec : RouterReg 187 8 dLayout)
    (hRoles : rHas1 rElec = rHas1 rElecLayout ∧ rRawHas2 rElec = rRawHas2 rElecLayout ∧
      rIdx1 rElec = rIdx1 rElecLayout ∧ rIdx2 rElec = rIdx2 rElecLayout ∧
      rBufLo rElec = rBufLo rElecLayout ∧ rBufHi rElec = rBufHi rElecLayout ∧
      rHA rElec = rHA rElecLayout ∧ rHB rElec = rHB rElecLayout ∧
      rSys rElec = rSys rElecLayout)
    (hPrivScr : ∀ j : Fin 454, ∃ m : Fin scrLLayout, rElec ⟨4602 + j.val, privIdx_lt j⟩ =
        rScrLayout m ∧ (m.val < 65 ∨ 153 ≤ m.val))
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {X : Operator (2 ^ n)}
        (hX : (rTot.compose rScrLayout).basisOutcomeProjector 0 * X = X) :
    SupportedOn (ValidRouterInput (rTot.compose rNucLayout)) ((rTot.embedUnitary o1.uLocal).1 * X) ∧
    SupportedOn (ValidRouterInput (rTot.compose rElec))
        ((uRouterSwapConj (rTot.compose rNucLayout)).1 * ((rTot.embedUnitary o1.uLocal).1 * X)) ∧
    (uRouterSwapConj (rTot.compose rElec)).1 * ((uRouterSwapConj (rTot.compose rNucLayout)).1 *
        ((rTot.embedUnitary o1.uLocal).1 * X)) = (rTot.embedUnitary (wNoHad o1.uLocal)).1 * X ∧
    (rTot.compose rScrCompact1493).basisOutcomeProjector 0 * ((rTot.embedUnitary o1.uLocal).1 * X) =
        (rTot.embedUnitary o1.uLocal).1 * X ∧
    (rTot.compose rClean690Layout).basisOutcomeProjector 0 *
        ((rTot.embedUnitary (wNoHad o1.uLocal)).1 * X) =
        (rTot.embedUnitary (wNoHad o1.uLocal)).1 * X := by
  let _ : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  have hCleanIn (ξ : BitAssignment n) : inKetPred (fun η ↦ CleanScr fun i ↦ η (rTot i))
      (X.mulVec (ket ξ)) :=
    fun η hnz ↦ Classical.byContradiction fun hnot ↦
        hnz <| (congrFun (congrArg (·.mulVec (ket ξ)) hX) _).symm.trans <| by
      rw [← Matrix.mulVec_mulVec, proj_zero_vec_entry (rTot.compose rScrLayout) _ η,
          ite_eq_right (by exact hnot)]
  have hWnhKet (η : BitAssignment n) (hScr : CleanScr fun i ↦ η (rTot i)) :
      (rTot.embedUnitary (wNoHad o1.uLocal)).1.mulVec (ket η) = _ :=
    embedMatrix_ket_eq_writeReg rTot _ η ((congrArg (wNoHad o1.uLocal).1.mulVec
      (congrArg ket (routedStage0_self (fun i ↦
          η (rTot i))).symm)).trans (wNoHad_mulVec_ket o1 hScr _ _))
  have stepN (η : BitAssignment n) (hScr : CleanScr fun i ↦ η (rTot i)) :
      (uRouterSwapConj (rTot.compose rNucLayout)).1.mulVec ((rTot.embedUnitary o1.uLocal).1.mulVec
          (ket η)) =
        ket (DynCircExt.writeReg η rTot (routedStage2 decodeCoin (fun i ↦ η (rTot i))
          (outerCoinOf82 fun i ↦ η (rTot (rLcu82Layout i)))
              (innerBitsOf82 fun i ↦ η (rTot (rLcu82Layout i))))) := by
    rw [w1Ket rTot o1 η hScr, uRouterSwapConj_ket_eq (rTot.compose rNucLayout)
      (validRouter_compose_writeReg rTot rNucLayout η _ (validRouter_stage1 (decodeCoin :=
          decodeCoin) hScr _ _).1),
      routerSwapBits_compose_writeReg rTot rNucLayout η _]
    rfl
  refine ⟨supportedOn_of_inKetPred fun ξ ↦ by
      rw [← Matrix.mulVec_mulVec]
      exact inKetPred_mulVec _ (fun η hScr ↦ w1Ket rTot o1 η hScr ▸ inKetPred_ket
        (validRouter_compose_writeReg rTot rNucLayout η _ (validRouter_stage1 (decodeCoin :=
            decodeCoin) hScr _ _).1)) (hCleanIn ξ),
    supportedOn_of_inKetPred fun ξ ↦ by
      rw [← Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      exact inKetPred_mulVec _ (fun η hScr ↦
          ((Matrix.mulVec_mulVec _ _ _).symm.trans (stepN η hScr)) ▸
        inKetPred_ket (validRouter_compose_writeReg rTot rElec η _ (validRouter_rElec rElec
            hRoles hPrivScr hScr _ _))) (hCleanIn ξ), ?_,
    zeroProj_absorb rTot rScrCompact1493 _ fun ξ ↦ ?_,
    zeroProj_absorb rTot rClean690Layout _ fun ξ ↦ by
      rw [← Matrix.mulVec_mulVec]
      exact inKetPred_mulVec _ (fun η hScr ↦ hWnhKet η hScr ▸ inKetPred_ket fun m ↦
        (DynCircExt.writeReg_apply_reg η rTot _ (rClean690Layout m)).trans (routedKet_clean690
            hScr _ _ m)) (hCleanIn ξ)⟩
  · simp only [← Matrix.mul_assoc]
    refine supportedOn_of_inKetPred hCleanIn _ _ fun η hScr ↦ ?_
    simp only [← Matrix.mulVec_mulVec]
    rw [stepN η hScr, uRouterSwapConj_ket_eq (rTot.compose rElec)
        (validRouter_compose_writeReg rTot rElec η _
      (validRouter_rElec rElec hRoles hPrivScr hScr _ _)),
          routerSwapBits_compose_writeReg rTot rElec η _,
      routerSwapBits_congr_roles rElec rElecLayout hRoles _, hWnhKet η hScr]
    rfl
  · rw [← Matrix.mulVec_mulVec]
    refine inKetPred_mulVec _ (fun η hScr ↦ ?_) (hCleanIn ξ)
    rw [w1Ket rTot o1 η hScr]
    refine inKetPred_ket fun k ↦
        (DynCircExt.writeReg_apply_reg η rTot _ (rScrCompact1493 k)).trans ?_
    rw [routedStage1, routedStage0_self,
        DynCircExt.writeReg_apply_of_not_mem _ rOut40Layout _ _ fun ⟨j, hj⟩ ↦ by
      have _ := j.isLt
      have hv := congrArg Fin.val hj
      rw [val_rOut40Layout, val_rScrCompact1493 k] at hv
      split_ifs at hv <;> omega]
    exact (rScrCompact1493_sub_scr k).choose_spec ▸ hScr _
theorem rElecXor179_loc_scr (j : Fin 454) : ∃ m : Fin scrLLayout, rElecXor179 ⟨4602 + j.val,
    privIdx_lt j⟩ = rScrLayout m ∧ (m.val < 65 ∨ 153 ≤ m.val) := by
  have _ := privRank454_lt j.isLt
  let mIdx :=
      if privRank454 j.val < 33 then 30 + privRank454 j.val else 297 + (privRank454 j.val - 33)
  refine ⟨⟨mIdx, by
    dsimp [mIdx, scrLLayout]
    split_ifs <;> omega⟩, Fin.ext ?_,
      by
        dsimp [mIdx]
        split_ifs <;> omega⟩
  change (elecXor179WireFn _).val = _
  rw [val_elecXor179WireFn, val_rScrLayout]
  simp only [Nat.add_sub_cancel_left, mIdx]
  split_ifs <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld

namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (ancWOfScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld (w1Ket)
/-- Multiplexed unitary applying `uSlice γ` on the `projBits_c70 rC γ` sector. -/
def muxMat_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n)
    (uSlice : BitAssignment m → Unitary (2 ^ n)) : Operator (2 ^ n) :=
    ∑ γ : BitAssignment m, (uSlice γ).1 * projBits_c70 rC γ
theorem muxMat_mem_unitary_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n)
    (uSlice : BitAssignment m → Unitary (2 ^ n))
    (hComm : ∀ γ δ, (uSlice γ).1 * projBits_c70 rC δ = projBits_c70 rC δ * (uSlice γ).1) :
        muxMat_c70 rC uSlice ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, muxMat_c70,
      Matrix.conjTranspose_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun γ _ ↦ ?_).trans (sum_projBits_c70 rC)
  simp_rw [Finset.mul_sum, Matrix.conjTranspose_mul, projBits_herm_c70,
      Matrix.mul_assoc ((uSlice γ).1),
    ← Matrix.mul_assoc (projBits_c70 rC γ), projBits_mul_c70]
  rw [Finset.sum_eq_single γ (fun δ _ hne ↦
      by rw [ite_eq_right hne.symm, Matrix.zero_mul, Matrix.mul_zero])
    fun hm ↦ absurd (Finset.mem_univ _) hm, ite_eq_left rfl, ← Matrix.mul_assoc, hComm γ γ,
    Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, (uSlice γ).2.2, Matrix.mul_one]
/-- Bundled `Unitary (2 ^ n)` for coin-multiplexed slice unitaries. -/
def muxUnitary_c70 {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n)
    (uSlice : BitAssignment m → Unitary (2 ^ n)) (hComm : ∀ γ δ, (uSlice γ).1 * projBits_c70 rC δ =
    projBits_c70 rC δ * (uSlice γ).1) : Unitary (2 ^ n) :=
    ⟨muxMat_c70 rC uSlice, muxMat_mem_unitary_c70 rC uSlice hComm⟩
theorem circ_comm_embedUnitary_of_disj_c70 {m n : ℕ} (rC : QRegister m n)
    (V : Unitary (2 ^ m)) :
    ∀ {c : Circuit n}, CircWires (fun w ↦ ∀ j : Fin m, w ≠ rC j) c →
      c.eval.1 * (rC.embedUnitary V).1 = (rC.embedUnitary V).1 * c.eval.1
  | .identity, _ => by simp [Circuit.eval_identity]
  | .seq _ _, ⟨h₁, h₂⟩ =>
        by rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc,
             circ_comm_embedUnitary_of_disj_c70 rC V h₁, ← Matrix.mul_assoc,
             circ_comm_embedUnitary_of_disj_c70 rC V h₂, Matrix.mul_assoc]
  | .gate g reg, hg =>
        reg.embedMatrix_comm_of_disjoint rC (QRegister.disjoint_iff.mpr fun i j e ↦
        hg i j e) g.eval.1 V.1
theorem commutesWithDyn_embedUnitary_of_disj_c70 {Var : Type}
    {m n : ℕ} (rC : QRegister m n) (V : Unitary (2 ^ m))
    {p : DynamicCircuit Var n} (hp : DynWires (fun w ↦ ∀ j : Fin m, w ≠ rC j) p) :
    CommutesWithDyn (rC.embedUnitary V) p := by
  induction p with
  | circuit _ => exact circ_comm_embedUnitary_of_disj_c70 rC V hp
  | measure _ r =>
    exact fun o ↦
      r.embedMatrix_comm_of_disjoint rC (QRegister.disjoint_iff.mpr fun i j e ↦ hp i j e)
        (compProj o) V.1
  | qIf _ _ _ iht ihf => exact ⟨iht hp.1, ihf hp.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
theorem hDisjOut40Lcu82_c70 : rOut40Layout.DisjointWires rLcu82Layout :=
    QRegister.disjoint_iff.mpr fun j i e ↦ by
  have hv := congrArg Fin.val e
  rw [val_rOut40Layout, val_rLcu82Layout] at hv
  omega
/-- Combined `122`-wire Stage-1 clean support register `rOut40Layout ++ rLcu82Layout`. -/
def rStage1Clean122_c70 : QRegister (40 + (mLayout + 2)) dLayout :=
    rOut40Layout.concat rLcu82Layout hDisjOut40Lcu82_c70
theorem rStage1Clean122_apply_c70 (idx : Fin (40 + (mLayout + 2))) :
    rStage1Clean122_c70 idx =
      if h40 : idx.val < 40 then rOut40Layout ⟨idx.val, h40⟩
      else rLcu82Layout ⟨idx.val - 40, by
        have := idx.isLt
        omega⟩ := by
  split_ifs with h40
  · exact (congrArg rStage1Clean122_c70 (Fin.ext rfl)).trans (QRegister.concat_apply_left _ _ _
        ⟨idx.val, h40⟩)
  · exact (congrArg rStage1Clean122_c70 (Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt
        h40)).symm)).trans
      (QRegister.concat_apply_right _ _ _ _)
theorem rStage1Clean122_disj_rCoinExt_c70 {kExt : ℕ} (hk : kExt ≤ 72) :
    rStage1Clean122_c70.DisjointWires (rCoinExt kExt hk) :=
  QRegister.disjoint_iff.mpr fun idx j e ↦ by
    have hv :=
        (congrArg Fin.val (rStage1Clean122_apply_c70 idx)).symm.trans ((congrArg Fin.val e).trans
        (val_rCoinExt hk j))
    have _ : idx.val < 122 := idx.isLt
    split_ifs at hv <;> simp only [val_rOut40Layout, val_rLcu82Layout] at hv <;> omega
def stage1Clean122Bits_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (ξ : BitAssignment (40 + (mLayout + 2))) : BitAssignment (40 + (mLayout + 2)) := fun idx ↦
    if idx.val < 40 then ξ idx +
    (if (zeroNEremOutMask (decodeCoin (outerCoinOf82 (fun i : Fin (mLayout + 2) ↦
    ξ (Fin.natAdd 40 i))))).testBit idx.val then 1 else 0) else ξ idx
theorem stage1Clean122Bits_invol_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) :
    Function.Involutive (stage1Clean122Bits_c70 decodeCoin) := fun ξ ↦ funext fun idx ↦ by
  by_cases h40 : idx.val < 40
  · rw [stage1Clean122Bits_c70, ite_eq_left h40, show (fun i : Fin (mLayout + 2) ↦
        stage1Clean122Bits_c70 decodeCoin ξ
        (Fin.natAdd 40 i)) = fun i ↦ ξ (Fin.natAdd 40 i) from funext fun i ↦
            ite_eq_right (Nat.not_lt_of_ge (Nat.le_add_right 40 i.val)),
      stage1Clean122Bits_c70, ite_eq_left h40]
    exact zmod2_add_cancel_c70 (ξ idx) _
  · simp only [stage1Clean122Bits_c70, ite_eq_right h40]
/-- Clean Stage-1 permutation unitary supported strictly on `rOut40Layout ++ rLcu82Layout`. -/
def uStage1Clean_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) : Unitary (2 ^ dLayout) :=
    rStage1Clean122_c70.embedUnitary (involUnitary_c70 (stage1Clean122Bits_c70 decodeCoin)
    (stage1Clean122Bits_invol_c70 decodeCoin))
theorem uStage1Clean_comm_rCoinExt_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) {kExt : ℕ}
    (hk : kExt ≤ 72) (M : Operator (2 ^ kExt)) :
    (uStage1Clean_c70 decodeCoin).1 * (rCoinExt kExt hk).embedMatrix M =
        (rCoinExt kExt hk).embedMatrix M * (uStage1Clean_c70 decodeCoin).1 :=
  rStage1Clean122_c70.embedMatrix_comm_of_disjoint (rCoinExt kExt hk)
      (rStage1Clean122_disj_rCoinExt_c70 hk) _ M
theorem uStage1Clean_mul_pScr_c70 {w1 : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decodeCoin) : (uStage1Clean_c70 decodeCoin).1 * pScr =
    o1.uLocal.1 * pScr := by
  refine matrix_ext_ket fun β ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  split_ifs with hScr
  · have hO1 := w1Ket (QRegister.whole dLayout) o1 β hScr
    rw [QRegister.whole_embedUnitary] at hO1
    rw [uStage1Clean_c70, hO1, QRegister.embedUnitary_val,
      embedMatrix_ket_eq_writeReg rStage1Clean122_c70 _ β (involUnitary_mulVec_ket_c70 _ _ _)]
    refine congrArg ket (funext fun w ↦
        Eq.trans ?_ (DynCircExt.writeReg_apply_reg β (QRegister.whole dLayout) _ w).symm)
    change _ = routedStage1 decodeCoin β (outerCoinOf82 fun i ↦ β (rLcu82Layout i))
      (innerBitsOf82 fun i ↦ β (rLcu82Layout i)) w
    rw [routedStage1, routedStage0_self]
    have h82Eq : (fun i : Fin (mLayout + 2) ↦ β (rStage1Clean122_c70 (Fin.natAdd 40 i))) = fun i ↦
        β (rLcu82Layout i) :=
      funext fun i ↦ congrArg β (QRegister.concat_apply_right _ _ _ i)
    rcases Classical.em (w ∈ Set.range rStage1Clean122_c70.wires) with ⟨idx, rfl⟩ | hm
    · rw [DynCircExt.writeReg_apply_reg, stage1Clean122Bits_c70, rStage1Clean122_apply_c70 idx]
      by_cases h40 : idx.val < 40
      · rw [ite_eq_left h40, dite_eq_left h40, h82Eq,
            (congrArg β (Fin.ext (by
              rw [val_rOut40Layout, val_rScrLayout]
              dsimp
              omega) :
          rOut40Layout ⟨idx.val, h40⟩ = rScrLayout ⟨65 + idx.val,
              by
                simp [scrLLayout]
                omega⟩)).trans (hScr _),
          zero_add, DynCircExt.writeReg_apply_reg, outMaskBits40]
      · rw [ite_eq_right h40, dite_eq_right h40, DynCircExt.writeReg_apply_of_not_mem _
            rOut40Layout _ _
          fun ⟨j, hj⟩ ↦ QRegister.disjoint_iff.mp hDisjOut40Lcu82_c70 j _ hj]
    · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hm,
          DynCircExt.writeReg_apply_of_not_mem _ rOut40Layout _ _
        fun ⟨j, hj⟩ ↦
            hm ⟨⟨j.val, Nat.lt_add_right _ j.isLt⟩, (QRegister.concat_apply_left _ _ _ j).trans hj⟩]
  · rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem wNoHad_uStage1Clean_mul_pScr_c70 {w1 : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decodeCoin) :
    (wNoHad (uStage1Clean_c70 decodeCoin)).1 * pScr = (wNoHad o1.uLocal).1 * pScr := by
  simp only [wNoHad, Submonoid.coe_mul, Matrix.mul_assoc, uStage1Clean_mul_pScr_c70 o1]
theorem wFull_uStage1Clean_mul_pScr_c70 {w1 : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decodeCoin) :
    (wFull (uStage1Clean_c70 decodeCoin)).1 * pScr = (wFull o1.uLocal).1 * pScr := by
  rw [wFull, wFull, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    comm_pScr_uHad82.eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        wNoHad_uStage1Clean_mul_pScr_c70 o1]
theorem preConj_uStage1Clean_mul_c70 {w1 : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decodeCoin) (u4 : Unitary (2 ^ dLayout))
    (hComm : pScr * (preConj o1.uLocal u4).1 = (preConj o1.uLocal u4).1 * pScr) :
    (preConj (uStage1Clean_c70 decodeCoin) u4).1 * pScr =
      (preConj o1.uLocal u4).1 * pScr := by
  let Fo := wFull o1.uLocal
  let Fc := wFull (uStage1Clean_c70 decodeCoin)
  have hAbs : pScr * ((preConj o1.uLocal u4).1 * pScr) = (preConj o1.uLocal u4).1 *
      pScr := by
    rw [← Matrix.mul_assoc, hComm, Matrix.mul_assoc, pScr_idem]
  have hFc : Fc.1 * ((preConj o1.uLocal u4).1 * pScr) = u4.1 * (Fc.1 * pScr) := by
    rw [← hAbs, ← Matrix.mul_assoc Fc.1, wFull_uStage1Clean_mul_pScr_c70 o1,
        Matrix.mul_assoc Fo.1, hAbs,
      ← Matrix.mul_assoc, ← Submonoid.coe_mul, show Fo * preConj o1.uLocal u4 = u4 *
          Fo by
            dsimp only [Fo, preConj]
            group,
      Submonoid.coe_mul, Matrix.mul_assoc, ← wFull_uStage1Clean_mul_pScr_c70 o1]
  have hL := congrArg ((Fc⁻¹).1 * ·) hFc
  rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
      Matrix.one_mul] at hL
  exact (hL.trans (by simp only [preConj, Fc, Submonoid.coe_mul, Matrix.mul_assoc])).symm
theorem preConj_uStage1Clean_c70 {w1 : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decodeCoin) (u4 : Unitary (2 ^ dLayout))
    (hComm : pScr * (preConj o1.uLocal u4).1 = (preConj o1.uLocal u4).1 * pScr) :
    (preConj (uStage1Clean_c70 decodeCoin) u4).1 * pScr =
      (preConj o1.uLocal u4).1 * pScr ∧
    pScr * (preConj (uStage1Clean_c70 decodeCoin) u4).1 =
      (preConj (uStage1Clean_c70 decodeCoin) u4).1 * pScr := by
  have hM := preConj_uStage1Clean_mul_c70 o1 u4 hComm
  have hInvEq (u1 : Unitary (2 ^ dLayout)) : (preConj u1 u4)⁻¹ = preConj u1 u4⁻¹ := by
    unfold preConj
    group
  have hMInv := congrArg Matrix.conjTranspose (preConj_uStage1Clean_mul_c70 o1 u4⁻¹
    (hInvEq o1.uLocal ▸ unitary_comm_inv_of_comm (preConj o1.uLocal u4) pScr hComm))
  have hAdj (u1 : Unitary (2 ^ dLayout)) : (preConj u1 u4⁻¹).1ᴴ = (preConj u1 u4).1 :=
    hInvEq u1 ▸ Matrix.conjTranspose_conjTranspose (preConj u1 u4).1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, pScr_herm, hAdj, hAdj] at hMInv
  exact ⟨hM, hMInv.trans (hComm.trans hM.symm)⟩
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
end

namespace QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
open Operator QProg PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Coin70Lift
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
theorem muxMat_mulVec_ket {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n)
    (uSlice : BitAssignment m → Unitary (2 ^ n)) (β : BitAssignment n) :
    (muxMat_c70 rC uSlice).mulVec (ket β) = (uSlice (fun j ↦ β (rC j))).1.mulVec (ket β) := by
  rw [muxMat_c70, Matrix.sum_mulVec, Finset.sum_eq_single (fun j ↦ β (rC j))
    (fun γ _ hne ↦ by rw [← Matrix.mulVec_mulVec, projBits_mulVec_ket_c70,
      ite_eq_right fun hγ ↦ hne (funext fun j ↦ (hγ j).symm), Matrix.mulVec_zero])
    fun hm ↦
        absurd (Finset.mem_univ _) hm, ← Matrix.mulVec_mulVec, projBits_mulVec_ket_c70,
        ite_eq_left fun _ ↦ rfl]
end QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
end

/- ## Shapes 2 & 3: Generic `2 ^ kExt` `OpSys` Linearity & `PopBernstein` Identities -/
noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
namespace QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
set_option maxRecDepth 4096
open PrimitiveGate Real PhotochemistrySolution.ClusterPotSlice
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.GenWeightsSelect PhotochemistrySolution.PotOraclePortB
open PhotochemistrySolution.Coin70Lift PhotochemistrySolution.Sub5885
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (potExpectAvgK)
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen
/-- Raw `W11` positions `{0..4, 11..14, 31..32}` inside `rOuter41Layout`. -/
def w11IdxVal (j : Fin 11) : ℕ :=
    if j.val < 5 then j.val else if j.val < 9 then 6 + j.val else 22 + j.val
theorem w11IdxVal_lt41 (j : Fin 11) : w11IdxVal j < 41 := by
  fin_cases j <;> decide
/-- `W11` index in `Fin 41`. -/
def w11Idx (j : Fin 11) : Fin 41 := ⟨w11IdxVal j, w11IdxVal_lt41 j⟩
def w11RawBits (c : Fin (2 ^ 41)) : BitAssignment 11 :=
  fun j ↦ if c.val.testBit (w11Idx j).val then 1 else 0
/-- Concatenate `(γ, ω)` onto `BitAssignment (kExt + 11)`. -/
def concatBitsK11 {kExt : ℕ} (γ : BitAssignment kExt) (ω : BitAssignment 11) :
    BitAssignment (kExt + 11) := Sum.elim γ ω ∘ finSumFinEquiv.symm
/-- 13-sector `W11` fiber multiplicity contract on `2 ^ 41` coins. -/
structure ValidOuterW11StratifiedCoin
    (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ)
    (wKin : Particle_frozen → ℕ) (wIdle : ℕ)
    (cntEE : Fin 4 → BitAssignment 11 → ℕ) (cntNN : Fin 4 → Fin 4 → BitAssignment 11 → ℕ)
    (cntEN : Fin 4 → BitAssignment 11 → ℕ) (decode : Fin (2 ^ 41) → ZeroNEremSector) : Prop where
  validCoin : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode
  sum_cntEE : ∀ s, (∑ ω, cntEE s ω) = wEE s
  sum_cntNN : ∀ s1 s2, (∑ ω, cntNN s1 s2 ω) = wNN s1 s2
  sum_cntEN : ∀ s, (∑ ω, cntEN s ω) = wEN s
  fib_ee : ∀ n1 e1 e2 ω,
    (Finset.univ.filter (fun c ↦ decode c = .ee n1 e1 e2 ∧ w11RawBits c = ω)).card =
      if e1 < e2 then cntEE (nucSpecies n1) ω else 0
  fib_nn : ∀ n1 n2 e1 ω,
    (Finset.univ.filter (fun c ↦ decode c = .nn n1 n2 e1 ∧ w11RawBits c = ω)).card =
      if n1 < n2 then cntNN (nucSpecies n1) (nucSpecies n2) ω else 0
  fib_en : ∀ n1 e1 ω,
    (Finset.univ.filter (fun c ↦ decode c = .en n1 e1 ∧ w11RawBits c = ω)).card =
      cntEN (nucSpecies n1) ω
/-- Stratified `PotExpectFn` weighting `pe11 ω` by 13-sector `W11` fiber counts. -/
abbrev potExpectStratW11 (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ)
    (cntEE : Fin 4 → BitAssignment 11 → ℕ) (cntNN : Fin 4 → Fin 4 → BitAssignment 11 → ℕ)
    (cntEN : Fin 4 → BitAssignment 11 → ℕ) (pe11 : BitAssignment 11 → PotExpectFn) : PotExpectFn :=
  fun s nn sp1 sp2 nA nB eA eB ↦
    if s then
      if nn then (wNN sp1 sp2 : ℝ)⁻¹ * ∑ ω, (cntNN sp1 sp2 ω : ℝ) *
          pe11 ω true true sp1 sp2 nA nB eA eB
      else (wEE sp1 : ℝ)⁻¹ * ∑ ω, (cntEE sp1 ω : ℝ) * pe11 ω true false sp1 sp2 nA nB eA eB
    else (wEN sp1 : ℝ)⁻¹ * ∑ ω, (cntEN sp1 ω : ℝ) * pe11 ω false false sp1 sp2 nA nB eA eB
/-- Joint `(kExt + 11)`-coin expectation averaging uniformly over `kExt` and stratifying `W11`. -/
abbrev potExpectAvgStratW11 {kExt : ℕ} (wEE : Fin 4 → ℕ) (wNN : Fin 4 → Fin 4 → ℕ) (wEN : Fin 4 → ℕ)
    (cntEE : Fin 4 → BitAssignment 11 → ℕ) (cntNN : Fin 4 → Fin 4 → BitAssignment 11 → ℕ)
    (cntEN : Fin 4 → BitAssignment 11 → ℕ) (peK11 : BitAssignment (kExt + 11) → PotExpectFn) :
    PotExpectFn :=
    potExpectAvgK (fun γ ↦ potExpectStratW11 wEE wNN wEN cntEE cntNN cntEN (fun ω ↦
    peK11 (concatBitsK11 γ ω)))
/-- Valid `decodeUltraNuc192` multiplicity `[1, 6, 7, 8]` per nucleus (`0=H, 1=C, 2=N, 3=O`). -/
def mSpCart254 : Fin 4 → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 7
  | 3 => 8
/-- Decode `BitAssignment 11` to `Fin 2048` via `natOfZModBits 11`. -/
def fin2048OfBits11 (ω : BitAssignment 11) : Fin 2048 :=
  ⟨natOfZModBits 11 ω, natOfZModBits_11_lt ω⟩
/-- Encode `Fin 2048` to `BitAssignment 11` via `Nat.testBit`. -/
def bits11OfFin2048 (u : Fin 2048) : BitAssignment 11 := fun j ↦
    if u.val.testBit j.val then 1 else 0
theorem fin2048OfBits11_bits11OfFin2048 (u : Fin 2048) : fin2048OfBits11 (bits11OfFin2048 u) =
    u := by
  exact Fin.ext (natOfZModBits_ite_testBit_local 11 u.val u.isLt)
theorem bits11OfFin2048_fin2048OfBits11 (ω : BitAssignment 11) : bits11OfFin2048
    (fin2048OfBits11 ω) = ω :=
  funext fun j ↦ by
    dsimp only [bits11OfFin2048, fin2048OfBits11, natOfZModBits]
    rcases DynCircExt.bit_cases (ω j) with h | h <;> simp [natOfBoolBits_testBit, h]
/-- Canonical bijection `BitAssignment 11 ≃ Fin 2048` matching `natOfZModBits 11`. -/
def equivBits11 : BitAssignment 11 ≃ Fin 2048 where
  toFun := fin2048OfBits11
  invFun := bits11OfFin2048
  left_inv := bits11OfFin2048_fin2048OfBits11
  right_inv := fin2048OfBits11_bits11OfFin2048
theorem sum_fin_lt_nat {M t : ℕ} (ht : t ≤ M) : (∑ u : Fin M, if u.val < t then 1 else 0) =
    t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_congr rfl fun u _ ↦ show _ = (if u.val < t then 1 else 0) +
          (if u = ⟨t, ht⟩ then 1 else 0) by
        simp only [Fin.ext_iff]
        split_ifs <;> omega]
      simp [Finset.sum_add_distrib, ih (by omega), Finset.sum_ite_eq']
theorem validOuterW11_of_nat {wEE : Fin 4 → ℕ} {wNN : Fin 4 → Fin 4 → ℕ} {wEN : Fin 4 → ℕ}
    {wKin : Particle_frozen → ℕ} {wIdle : ℕ} {cntEE2048 : Fin 4 → ℕ → ℕ} {cntNN2048 : Fin 4 →
      Fin 4 → ℕ → ℕ}
    {cntEN2048 : Fin 4 → ℕ → ℕ} {decode : Fin (2 ^ 41) → ZeroNEremSector} {w11Nat : Fin (2 ^ 41) →
      ℕ}
    (hwLt : ∀ c, w11Nat c < 2048) (hwBit : ∀ c (j : Fin 11), (w11Nat c).testBit j.val =
      c.val.testBit (w11IdxVal j))
    (hValid : ValidGenZeroNEremCoin wEE wNN wEN wKin wIdle decode)
    (hSumEE : ∀ s, (∑ u : Fin 2048, cntEE2048 s u.val) = wEE s)
    (hSumNN : ∀ s1 s2, (∑ u : Fin 2048, cntNN2048 s1 s2 u.val) = wNN s1 s2)
    (hSumEN : ∀ s, (∑ u : Fin 2048, cntEN2048 s u.val) = wEN s)
    (hFibEE : ∀ n1 e1 e2 {w : ℕ}, w < 2048 → (Finset.univ.filter (fun c ↦ decode c =
      .ee n1 e1 e2 ∧ w11Nat c = w)).card = if e1 < e2 then cntEE2048 (nucSpecies n1) w else 0)
    (hFibNN : ∀ n1 n2 e1 {w : ℕ}, w < 2048 → (Finset.univ.filter (fun c ↦ decode c =
      .nn n1 n2 e1 ∧ w11Nat c = w)).card = if n1 < n2 then cntNN2048 (nucSpecies n1)
        (nucSpecies n2) w else 0)
    (hFibEN : ∀ n1 e1 {w : ℕ}, w < 2048 → (Finset.univ.filter (fun c ↦ decode c = .en n1 e1 ∧
      w11Nat c = w)).card = cntEN2048 (nucSpecies n1) w) :
    ValidOuterW11StratifiedCoin wEE wNN wEN wKin wIdle (fun s ω ↦ cntEE2048 s
      (natOfZModBits 11 ω)) (fun s1 s2 ω ↦ cntNN2048 s1 s2 (natOfZModBits 11 ω))
        (fun s ω ↦ cntEN2048 s (natOfZModBits 11 ω)) decode := by
  have hCard (Q : Fin (2 ^ 41) → Prop) [DecidablePred Q] (ω : BitAssignment 11) :
      (Finset.univ.filter (fun c ↦ Q c ∧ w11RawBits c = ω)).card =
        (Finset.univ.filter (fun c ↦ Q c ∧ w11Nat c = natOfZModBits 11 ω)).card :=
    congrArg Finset.card (Finset.filter_congr fun c _ ↦ and_congr_right fun _ ↦ by
      rw [show w11RawBits c = bits11OfFin2048 ⟨w11Nat c, hwLt c⟩ from
        funext fun j ↦ congrArg (if · then (1 : ZMod 2) else 0) (hwBit c j).symm]
      exact ⟨fun h ↦ congrArg Fin.val ((fin2048OfBits11_bits11OfFin2048 _).symm.trans
        (congrArg fin2048OfBits11 h)),
        fun h ↦ (congrArg bits11OfFin2048 (Fin.ext h : (⟨w11Nat c, hwLt c⟩ : Fin 2048) =
          fin2048OfBits11 ω)).trans (bits11OfFin2048_fin2048OfBits11 ω)⟩)
  have hSum (f : ℕ → ℕ) :=
    Fintype.sum_equiv equivBits11 (fun ω ↦ f (natOfZModBits 11 ω)) (fun u ↦ f u.val) fun _ ↦ rfl
  exact ⟨hValid, fun s ↦ (hSum _).trans (hSumEE s), fun s1 s2 ↦ (hSum _).trans (hSumNN s1 s2),
    fun s ↦ (hSum _).trans (hSumEN s),
    fun n1 e1 e2 ω ↦ (hCard _ ω).trans (hFibEE n1 e1 e2 (natOfZModBits_11_lt ω)),
    fun n1 n2 e1 ω ↦ (hCard _ ω).trans (hFibNN n1 n2 e1 (natOfZModBits_11_lt ω)),
    fun n1 e1 ω ↦ (hCard _ ω).trans (hFibEN n1 e1 (natOfZModBits_11_lt ω))⟩
end QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge

namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192
open PrimitiveGate DynamicCircuit PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.SelectFastQft8Gidney
open PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.UnembedO3Bridge
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.FastQft8 PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.Qft8PostCancelT5 PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectKin526OneWrap
open PhotochemistrySolution.SelectQft8KinMid PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.Stage4KinFull
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
/-- Core 98-T cat-QFT kinetic unitary (`Usel`) for exact 2-coin square-free kinetic. -/
noncomputable def uKinCoreCat2m1_98UselLayout : Unitary (2 ^ dLayout) :=
  uMux27Layout⁻¹ *
    ((qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
        qft8Stg3ValidP_layout)⁻¹ *
      uKinMid2m1UselLayout *
      qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
        qft8Stg3ValidP_layout) *
    uMux27Layout
/-- Core 98-T cat-QFT kinetic unitary (`Csel`) for exact 2-coin square-free kinetic. -/
noncomputable def uKinCoreCat2m1_98CselLayout : Unitary (2 ^ dLayout) :=
  uMux27Layout⁻¹ *
    ((qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
        qft8Stg3ValidP_layout)⁻¹ *
      uKinMid2m1CselLayout *
      qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
        qft8Stg3ValidP_layout) *
    uMux27Layout
/-- Species-swapped 98-T cat-QFT kinetic unitary (`Usel`). -/
noncomputable def uKinCat2m1_98UselLayout : Unitary (2 ^ dLayout) :=
  uSpeciesSwap50Layout⁻¹ * uKinCoreCat2m1_98UselLayout * uSpeciesSwap50Layout
/-- Species-swapped 98-T cat-QFT kinetic unitary (`Csel`). -/
noncomputable def uKinCat2m1_98CselLayout : Unitary (2 ^ dLayout) :=
  uSpeciesSwap50Layout⁻¹ * uKinCoreCat2m1_98CselLayout * uSpeciesSwap50Layout
/-- Aligned 98-T cat-QFT kinetic unitary (`Usel`) for `580 T` exact 2-coin square-free kinetic. -/
noncomputable def uAlignedKinCat2m1_98UselLayout : Unitary (2 ^ dLayout) :=
  uKinAlign0Layout⁻¹ * uKinCat2m1_98UselLayout * uKinAlign0Layout
/-- Aligned 98-T cat-QFT kinetic unitary (`Csel`) for `580 T` exact 2-coin square-free kinetic. -/
noncomputable def uAlignedKinCat2m1_98CselLayout : Unitary (2 ^ dLayout) :=
    uKinAlign0Layout⁻¹ * uKinCat2m1_98CselLayout * uKinAlign0Layout
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel
    Stage4Kin14Scb.abpKin14Csel Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel
    Kinetic664.abpKin15SqFree2m1Csel Qft8PostCancelT5.qft8PostCancel98CatU
    Qft8PostCancelT5.polyPostCancelT5Qft8Bracket98 Stage4KinFull.bAxisMux27 bSpeciesSwap50
theorem uKin2m1_98Layout_props : uKinCat2m1_98CselLayout.1 = (1 - projOneQCompactGen scrWLayout) +
    projOneQCompactGen scrWLayout * uKinCat2m1_98UselLayout.1 ∧ uKinCat2m1_98UselLayout.1 *
    projOneQCompactGen scrWLayout = projOneQCompactGen scrWLayout * uKinCat2m1_98UselLayout.1 ∧
    uKinCat2m1_98UselLayout.1 * cat8SharedProjCompactGen scrWLayout = uKinIdeal2m1UselLayout.1 *
    cat8SharedProjCompactGen scrWLayout ∧ (∀ {k : ℕ} (r : QRegister k dLayout),
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r → ∀ M : Operator (2 ^ k),
    Commute uKinIdeal2m1UselLayout.1 (r.embedMatrix M)) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  let Pq := projOneQCompactGen scrWLayout
  let Qcat : Unitary (2 ^ dLayout) :=
    qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout qft8Stg3ValidP_layout
  let catM := Matrix.vecMulVec (PgBase.phaseGradientState 8) (star (PgBase.phaseGradientState 8))
  have hMid := csel_eq_and_comm_of_ket wLocQLayout uKinMid2m1CselLayout uKinMid2m1UselLayout
    (fun δ ↦ kin2m1OutBit (fun j ↦ δ (rKin226Layout j)))
    (fun δ ↦ embedUnitary_mulVec_ket_of_isPhaseDiag rKin226Layout
      abpKin15SqFree2m1Csel.toCircuit.eval isPhaseDiag_and_valid_abpKin2m1.2.2.1 δ)
    uKinMid2m1_isPhaseDiag_layout
  have h1 := csel_conj_unitary Pq Qcat _ _ (qft8PostCancel98CatU_comm_projOneQ () scrWLayout
    offKinLayout hoffKinLayout rPKinLayout qft8Stg3ValidP_layout) hMid.1 hMid.2
  have h2 := csel_conj_unitary Pq uMux27Layout _ _ (embedUnitary_comm_of_disjoint rMux27Layout
    _ _ (uMux27_disj_off PotSelectWiring.hoff_wLocQ) (compProj 1)) h1.1 h1.2
  have h3 := csel_conj_unitary Pq uSpeciesSwap50Layout _ _ (embedUnitary_comm_of_disjoint
    rSpeciesSwap50Layout _ _ (uSp50_disj_off PotSelectWiring.hoff_wLocQ)
    (compProj 1)) h2.1 h2.2
  have hCat := conj_eq_on_proj (uMux27Layout⁻¹).1 (Qcat⁻¹ * uKinMid2m1UselLayout * Qcat).1
    ((qft8Stg3IdealU scrWLayout rPKinLayout)⁻¹ * uKinMid2m1UselLayout *
      qft8Stg3IdealU scrWLayout rPKinLayout).1 uMux27Layout.1 (cat8SharedProjCompactGen scrWLayout)
    (embedUnitary_comm_of_disjoint rMux27Layout _ _ (uMux27_disj_off hoff_cat8_layout) catM)
    (qft8PostCancel98CatU_conj_mul_cat8SharedProj () scrWLayout offKinLayout hoffKinLayout
        rPKinLayout
      qft8Stg3ValidP_layout uKinMid2m1UselLayout (embedUnitary_comm_of_disjoint rKin226Layout _
        (locCat8SharedCompactGen scrWLayout) (rKin226_disj_off fun i ↦ by
          have := val_locCat8_layout i
          omega) catM)
      (diag_ket_comm_embed_dPost8U rPKinLayout _
        (fun δ ↦ bitSign (kin2m1OutBit (fun j ↦
            δ (rKin226Layout j)))) uKinMid2m1_isPhaseDiag_layout))
  exact ⟨h3.1, h3.2, conj_eq_on_proj (uSpeciesSwap50Layout⁻¹).1 uKinCoreCat2m1_98UselLayout.1
    uKinCoreIdeal2m1UselLayout.1 uSpeciesSwap50Layout.1 _ (embedUnitary_comm_of_disjoint
      rSpeciesSwap50Layout _ _ (uSp50_disj_off hoff_cat8_layout) catM) hCat,
    uKinIdeal2m1UselLayout_comm_off⟩
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
set_option exponentiation.threshold 8192
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.CoinWrap
open PhotochemistrySolution.Stage1SingleWrap
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
/-- Extract the 41-bit outer coin from ambient `rTot : QRegister dLayout n`. -/
def coinOfAmb {n : ℕ} (rTot : QRegister dLayout n) (η : BitAssignment n) : Fin (2 ^ 41) :=
    outerCoinOf82 (fun i ↦ η (rTot (rLcu82Layout i)))
theorem coinOfAmb_bit {n : ℕ} (rTot : QRegister dLayout n) (η : BitAssignment n)
    (k : Fin 41) : η (rTot (rOuter41Layout k)) =
    if (coinOfAmb rTot η).val.testBit k.val then 1 else 0 := by
  rw [← congrFun (routedStage0_self fun i ↦ η (rTot i)) (rOuter41Layout k),
    show rOuter41Layout k = rLcu82Layout ⟨k.val,
        fin41_lt_mLayout k⟩ from Fin.ext (by rw [val_rOuter41Layout, val_rLcu82Layout])]
  exact (writeReg_apply_reg _ rLcu82Layout _ _).trans (pack82_apply_lt _ _ k)
def stStage1 {n : ℕ} (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (rTot : QRegister dLayout n)
    (η : BitAssignment n) : BitAssignment n := writeReg η (rTot.compose rOut40Layout) fun j ↦
    if (zeroNEremOutMask (decodeCoin (coinOfAmb rTot η))).testBit j.val then 1 else 0
def stTailOnly {n : ℕ} (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (rTot : QRegister dLayout n)
    (η : BitAssignment n) : BitAssignment n := writeReg η (rTot.compose rOutTail5) fun s ↦
    if preCnotBit40 (zeroNEremOutMask (decodeCoin (coinOfAmb rTot η))) (tail5OutIdx s) then 1 else 0
def stPreCnotSplit {n : ℕ} (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (rTot : QRegister dLayout n) (η : BitAssignment n) : BitAssignment n :=
    writeReg (stTailOnly decodeCoin rTot η) (rTot.compose rOutMid32) fun i ↦
    if preCnotBit40 (zeroNEremOutMask (decodeCoin (coinOfAmb rTot η))) (mid32OutIdx i) then 1 else 0
theorem uLocal_mul_rScrLayout_eq_mkKetOpW {w1 n : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decodeCoin) (rTot : QRegister dLayout n) :
    (rTot.embedUnitary o1.uLocal).1 * (rTot.compose rScrLayout).basisOutcomeProjector 0 =
    mkKetOpW (rTot.compose rScrLayout) (stStage1 decodeCoin rTot) (fun _ ↦ 0) :=
  matrix_ext_ket fun η ↦ by
    rw [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · have hLoc := o1.ket_of_clean (coinOfAmb rTot η) (fun i ↦ η (rTot i)) (coinOfAmb_bit rTot η)
        (fun j ↦ (rOut40Layout_sub_scr j).elim fun m hm ↦ by simpa [hm] using hz m)
        fun k ↦ (rScrCompact1493_sub_scr k).elim fun m hm ↦ by simpa [hm] using hz m
      simp only [QRegister.embedUnitary_val, QubitizationWalkSem.bitSign, ↓reduceIte, one_smul]
      refine (embedMatrix_ket_eq_writeReg rTot o1.uLocal.1 η hLoc).trans (congrArg ket
          (funext fun w ↦ ?_))
      dsimp only [stStage1]
      rcases Classical.em (w ∈ Set.range rTot.wires) with ⟨i, rfl⟩ | hwTot
      · rw [writeReg_apply_reg]
        exact (Classical.em (i ∈ Set.range rOut40Layout.wires)).elim
          (by
            rintro ⟨j, rfl⟩
            refine (writeReg_apply_reg _ _ _ j).trans (Eq.symm <|
                writeReg_apply_reg _ _ _ j))
          fun hwOut ↦ by rw [writeReg_apply_of_not_mem _ _ _ i hwOut,
            writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦ hwOut ⟨j, rTot.wires.injective hj⟩]
      · rw [writeReg_apply_of_not_mem _ _ _ w hwTot,
          writeReg_apply_of_not_mem _ _ _ w fun ⟨j, hj⟩ ↦ hwTot ⟨rOut40Layout j, hj⟩]
    · simp only [Matrix.mulVec_zero]
def stCoreClean {n : ℕ} (M : ℕ) (hM5 : M + 5 ≤ 361) (coreGates : Fin M → ℕ × ℕ)
    (coreMask0 coreMask1 : ℕ) (rTot : QRegister dLayout n) (η : BitAssignment n) :
    BitAssignment n :=
    stepCB (rTot.compose (rRevCore M hM5)) (cpRevCore M coreGates coreMask0 coreMask1).fwdBits η
def stTier1Done {n : ℕ} (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (M : ℕ) (hM5 : M + 5 ≤ 361)
    (coreGates : Fin M → ℕ × ℕ) (coreMask0 coreMask1 : ℕ) (rTot : QRegister dLayout n)
    (η : BitAssignment n) : BitAssignment n :=
    writeReg (stCoreClean M hM5 coreGates coreMask0 coreMask1 rTot η)
    (rTot.compose rOutTail5) fun s ↦
    if preCnotBit40 (zeroNEremOutMask (decodeCoin (coinOfAmb rTot η))) (tail5OutIdx s) then 1 else 0
def stTmpClean {n : ℕ} (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (M : ℕ) (hM5 : M + 5 ≤ 361)
    (coreGates : Fin M → ℕ × ℕ) (coreMask0 coreMask1 : ℕ) (rTot : QRegister dLayout n)
    (η : BitAssignment n) : BitAssignment n :=
    stepCB (rTot.compose (rRevTmp M hM5)) cpRevTmp.fwdBits (stTier1Done decodeCoin M hM5 coreGates
    coreMask0 coreMask1 rTot η)
theorem stCoreClean_bits {n : ℕ} (M : ℕ) (hM5 : M + 5 ≤ 361) (coreGates : Fin M → ℕ × ℕ)
    (coreMask0 coreMask1 : ℕ) (rTot : QRegister dLayout n) (η : BitAssignment n)
    (hz : ∀ m : Fin scrLLayout, η ((rTot.compose rScrLayout) m) = 0) :
    let c := coinOfAmb rTot η
    let env := xagEnv c.val M coreGates M le_rfl
    let stC := stCoreClean M hM5 coreGates coreMask0 coreMask1 rTot η
    stC (rTot (rScrCompact1493 ⟨M + 2, midPred_m2_lt hM5⟩)) = 1 ∧
        (∀ k : Fin 41, stC (rTot (rOuter41Layout k)) = if env.testBit (1 + k.val) then 1 else 0) ∧
    (∀ k : Fin M, stC (rTot (rScrCompact1493 ⟨k.val, by omega⟩)) = if env.testBit (42 +
        k.val) then 1 else 0) ∧
    stC (rTot (rScrCompact1493 ⟨M, revTmp_m0_lt hM5⟩)) = (if oddBits (env &&& coreMask0)
        (42 + M) then 1 else 0) ∧
    stC (rTot (rScrCompact1493 ⟨M + 1, revTmp_m1_lt hM5⟩)) = (if oddBits (env &&& coreMask1)
        (42 + M) then 1 else 0) ∧
    (∀ k : Fin 1493, M + 3 ≤ k.val → stC (rTot (rScrCompact1493 k)) = 0) := by
  intro c env stC
  obtain ⟨hPre, hM0, hM1, hOne⟩ := fwdBits_cpRevCore M coreGates coreMask0 coreMask1 c
    (fun i ↦ η ((rTot.compose (rRevCore M hM5)) i))
    (fun k ↦ (congrArg (η <| rTot ·) (rRevCore_coin M hM5 k)).trans (coinOfAmb_bit rTot η k))
    fun k ↦ (congrArg (η <| rTot ·) (rRevCore_scr M hM5 ⟨k.val, by omega⟩)).trans
      ((rScrCompact1493_sub_scr ⟨k.val, by omega⟩).elim fun m hm ↦ by simpa [hm] using hz m)
  have regEq (i : Fin (41 + (M + 3))) : stC (rTot (rRevCore M hM5 i)) = _ :=
    writeReg_apply_reg η (rTot.compose (rRevCore M hM5)) _ i
  refine ⟨by simpa only [← rRevCore_scr M hM5 ⟨M + 2, by omega⟩, regEq] using
      (congrArg _ (Fin.ext (by
        simp only [wCoreOne]
        omega))).trans hOne,
    fun k ↦ by simpa only [← rRevCore_coin M hM5 k, regEq] using hPre ⟨k.val, by omega⟩,
    fun k ↦
        by simpa only [← rRevCore_scr M hM5 ⟨k.val, by omega⟩, regEq, show 42 + k.val = 1 +
             (41 + k.val) by omega]
      using hPre ⟨41 + k.val, by omega⟩,
    by simpa only [← rRevCore_scr M hM5 ⟨M, by omega⟩, regEq, wCoreM0] using hM0,
    by simpa only [← rRevCore_scr M hM5 ⟨M + 1, by omega⟩, regEq] using
      (congrArg _ (Fin.ext (by
        simp only [wCoreM1]
        omega))).trans hM1, fun k hk ↦ ?_⟩
  dsimp only [stC, stCoreClean, stepCB]
  rw [writeReg_apply_of_not_mem _ (rTot.compose (rRevCore M hM5)) _ _]
  · exact (rScrCompact1493_sub_scr k).elim fun m hm ↦ by simpa [hm] using hz m
  · rintro ⟨i, hi⟩
    have he : revCoreWireFn M hM5 i = rScrCompact1493 k := rTot.wires.injective hi
    dsimp only [revCoreWireFn] at he
    split_ifs at he
    · exact rScr_ne_rOuter41 k _ he.symm
    · exact absurd (congrArg Fin.val (rScrCompact1493.wires.injective he)) (by
      dsimp
      omega)
theorem stCoreClean_tailPred_lt42M {n : ℕ} (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (M : ℕ)
    (hM5 : M + 5 ≤ 361) (coreGates : Fin M → ℕ × ℕ) (coreMask0 coreMask1 : ℕ)
    (rTot : QRegister dLayout n) (η : BitAssignment n)
    (hz : ∀ m : Fin scrLLayout, η ((rTot.compose rScrLayout) m) = 0) (u : Fin (47 + M))
    (hu : u.val < 42 + M) :
    stCoreClean M hM5 coreGates coreMask0 coreMask1 rTot η (rTot (rTailPred M hM5 u)) =
    if tailPredBit M coreGates (coinOfAmb rTot η)
    (zeroNEremOutMask (decodeCoin (coinOfAmb rTot η))) u.val then 1 else 0 := by
  obtain ⟨hOne, hCoin, hWork, _, _, _⟩ :=
      stCoreClean_bits M hM5 coreGates coreMask0 coreMask1 rTot η hz
  rw [show rTailPred M hM5 u = midPredWireFn M hM5 ⟨u.val,
      by omega⟩ from congrArg (midPredWireFn M hM5) (Fin.ext (Nat.zero_add u.val))]
  dsimp only [midPredWireFn]
  by_cases h0 : u.val = 0
  · simpa only [h0, beq_self_eq_true, ↓reduceIte, tailPredBit_zero] using hOne
  · dsimp only [tailPredBit]
    simp only [beq_false_of_ne h0, Nat.ble_eq_true_of_le hu, Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : u.val < 42
    · simp only [Nat.ble_eq_true_of_le h1, ↓reduceIte]
      exact (hCoin ⟨(u.val - 1) % 41,
          _⟩).trans (by simp only [show 1 + (u.val - 1) % 41 = u.val by omega])
    · simp only [Bool.eq_false_iff.mpr fun l ↦ h1 (Nat.le_of_ble_eq_true l), Bool.false_eq_true,
          ↓reduceIte]
      exact (hWork ⟨u.val - 42,
          by omega⟩).trans (by simp only [show 42 + (u.val - 42) = u.val by omega])
theorem cPreCnot40_mul_stStage1_eq_stPreCnotSplit {n : ℕ}
    (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (rTot : QRegister dLayout n) :
    (cPreCnot40 (rTot.compose rOut40Layout)).eval.1 * mkKetOpW (rTot.compose rScrLayout)
    (stStage1 decodeCoin rTot) (fun _ ↦ 0) = mkKetOpW (rTot.compose rScrLayout)
    (stPreCnotSplit decodeCoin rTot) (fun _ ↦ 0) :=
  matrix_ext_ket fun η ↦ by
    rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · let s := decodeCoin (coinOfAmb rTot η)
      let m40 := zeroNEremOutMask s
      rw [Matrix.mulVec_smul,
          cPreCnot40_mulVec_ket (rTot.compose rOut40Layout) m40 (stStage1 decodeCoin rTot η) fun u ↦
          writeReg_apply_reg η (rTot.compose rOut40Layout) _ u]
      refine congrArg (QubitizationWalkSem.bitSign 0 • ·) (congrArg ket (funext fun w ↦ ?_))
      by_cases hwOut : w ∈ Set.range (rTot.compose rOut40Layout).wires
      · obtain ⟨j, rfl⟩ := hwOut
        rw [writeReg_apply_reg]
        have hpure (hp : j.val = 35 ∨ j.val = 32 ∨ j.val = 34) :
            (if preCnotBit40 m40 j.val then (1 : ZMod 2) else 0) =
                stPreCnotSplit decodeCoin rTot η ((rTot.compose rOut40Layout) j) := by
          obtain ⟨p35, p32, p34⟩ := preCnotBit40_zeroNErem_pureZero s
          rw [show preCnotBit40 m40 j.val =
              false by rcases hp with h | h | h <;> simp [h, m40, p35, p32, p34],
            stPreCnotSplit, writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, e⟩ ↦
                (by decide : ∀ (i : Fin 32) (j : Fin 40),
              (j.val = 35 ∨ j.val = 32 ∨ j.val = 34) → mid32OutIdx i ≠ j.val) i j hp
              (congrArg Fin.val (rOut40Layout.wires.injective (rTot.wires.injective e))),
            stTailOnly, writeReg_apply_of_not_mem _ _ _ _ fun ⟨t, e⟩ ↦
                (by decide : ∀ (t : Fin 5) (j : Fin 40),
              (j.val = 35 ∨ j.val = 32 ∨ j.val = 34) → tail5OutIdx t ≠ j.val) t j hp
              (congrArg Fin.val (rOut40Layout.wires.injective (rTot.wires.injective e)))]
          exact (rOut40Layout_sub_scr j).elim fun m hm ↦
              by simpa [QRegister.compose, hm] using (hz m).symm
        rcases out40_partition j with h35 | h32 | h34 | ⟨i, hi⟩ | ⟨t, ht⟩
        · exact hpure (.inl h35)
        · exact hpure (.inr (.inl h32))
        · exact hpure (.inr (.inr h34))
        · rw [show (rTot.compose rOut40Layout) j =
              (rTot.compose rOutMid32) i from congrArg rTot.wires (congrArg rOut40Layout.wires
              (Fin.ext hi.symm)), stPreCnotSplit, writeReg_apply_reg, hi]
        · have hnM : (rTot.compose rOutTail5) t ∉ Set.range (rTot.compose rOutMid32).wires :=
            fun ⟨i, e⟩ ↦
                mid32_ne_tail5 i t (congrArg Fin.val (rOut40Layout.wires.injective
                (rTot.wires.injective e)))
          rw [show (rTot.compose rOut40Layout) j =
              (rTot.compose rOutTail5) t from congrArg rTot.wires (congrArg rOut40Layout.wires
              (Fin.ext ht.symm)), stPreCnotSplit, writeReg_apply_of_not_mem _ _ _ _ hnM, stTailOnly,
              writeReg_apply_reg, ht]
      · dsimp only [stStage1, stPreCnotSplit, stTailOnly]
        rw [writeReg_apply_of_not_mem _ _ _ _ hwOut, writeReg_apply_of_not_mem _ _ _ _ hwOut,
          writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, e⟩ ↦
              hwOut ⟨⟨mid32OutIdx i, mid32OutIdx_lt40 i⟩, e⟩,
              writeReg_apply_of_not_mem _ _ _ _ fun ⟨t, e⟩ ↦
              hwOut ⟨⟨tail5OutIdx t, tail5OutIdx_lt40 t⟩, e⟩]
    · simp only [Matrix.mulVec_zero]
theorem z2_mul_ite_bool (a b : Bool) : (if a then (1 : ZMod 2) else 0) * (if b then 1 else 0) =
    if (a && b) then 1 else 0 := by cases a <;> cases b <;> rfl
theorem stTmpClean_midPred {n : ℕ} (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) (M : ℕ)
    (hM5 : M + 5 ≤ 361) (coreGates : Fin M → ℕ × ℕ) (coreMask0 coreMask1 : ℕ)
    (rTot : QRegister dLayout n) (η : BitAssignment n)
    (hz : ∀ m : Fin scrLLayout, η ((rTot.compose rScrLayout) m) = 0) (u : Fin (49 + M)) :
    stTmpClean decodeCoin M hM5 coreGates coreMask0 coreMask1 rTot η (rTot (rMidPred M hM5 u)) =
    if midPredBit M coreGates coreMask0 coreMask1 (coinOfAmb rTot η)
    (zeroNEremOutMask (decodeCoin (coinOfAmb rTot η))) u.val then 1 else 0 := by
  let c := coinOfAmb rTot η
  let m40 := zeroNEremOutMask (decodeCoin c)
  let env := xagEnv c.val M coreGates M le_rfl
  let stW := stTier1Done decodeCoin M hM5 coreGates coreMask0 coreMask1 rTot η
  obtain ⟨_, _, _, hM0, hM1, hCleanHi⟩ :=
      stCoreClean_bits M hM5 coreGates coreMask0 coreMask1 rTot η hz
  have hScrW (k : Fin 1493) : stW (rTot (rScrCompact1493 k)) = _ :=
    writeReg_apply_of_not_mem _ (rTot.compose rOutTail5) _ _ fun ⟨s, hs⟩ ↦
        rScr_ne_rOut40 k _ (rTot.wires.injective hs).symm
  have hTailW (s : Fin 5) : stW (rTot (rOutTail5 s)) = _ :=
      writeReg_apply_reg _ (rTot.compose rOutTail5) _ s
  let αT : BitAssignment 6 := fun i ↦ stW ((rTot.compose (rRevTmp M hM5)) i)
  obtain ⟨f0, f1, f2, f3, f4, f5⟩ :=
      fwdBits_cpRevTmp αT ((hScrW ⟨M + 3, revTmp_m3_lt hM5⟩).trans (hCleanHi _ le_rfl))
    ((hScrW ⟨M + 4, revTmp_m4_lt hM5⟩).trans (hCleanHi _ (Nat.le_succ _)))
  by_cases hlt47 : u.val < 47 + M
  · have hn_ge (d : ℕ) {hd} (e : rMidPred M hM5 u = rScrCompact1493 ⟨M + d, hd⟩) (_ : 3 ≤ d := by
      decide) : False := by
      change midPredWireFn M hM5 u = _ at e
      dsimp only [midPredWireFn] at e
      split_ifs at e with _ _ h2 h3
      · exact absurd (Fin.mk.inj (rScrCompact1493.wires.injective e)) (by omega)
      · exact rScr_ne_rOuter41 _ _ e.symm
      · exact absurd (Fin.mk.inj (rScrCompact1493.wires.injective e)) ((fun _ ↦ by omega)
            (Nat.le_of_ble_eq_true h2))
      · exact rScr_ne_rOut40 _ _ e.symm
      · simp [Nat.ble_eq_true_of_le hlt47] at h3
    rw [show stTmpClean decodeCoin M hM5 coreGates coreMask0 coreMask1 rTot η (rTot (rMidPred M hM5
        u)) =
        stW (rTot (rMidPred M hM5 u)) by
      rcases Classical.em (rTot (rMidPred M hM5 u) ∈ Set.range (rTot.compose (rRevTmp M hM5)).wires)
          with ⟨i, hi⟩ | hwT
      · have he := rTot.wires.injective hi
        rw [stTmpClean, stepCB, ← hi, writeReg_apply_reg]
        fin_cases i <;>
            first | exact f0 | exact f1 | exact f2 | exact f3 | exact (hn_ge 3 he.symm).elim
                  | exact (hn_ge 4 he.symm).elim
      · exact writeReg_apply_of_not_mem _ (rTot.compose (rRevTmp M hM5)) _ _ hwT]
    by_cases hlt42 : u.val < 42 + M
    · have hEqTail : rMidPred M hM5 u = rTailPred M hM5 ⟨u.val, hlt47⟩ :=
        congrArg (midPredWireFn M hM5) (Fin.ext (Nat.zero_add u.val).symm)
      dsimp only [stW, stTier1Done, midPredBit, c, m40]
      simp only [Nat.ble_eq_true_of_le hlt42, ↓reduceIte]
      rw [writeReg_apply_of_not_mem _ (rTot.compose rOutTail5) _ _ fun ⟨s, hs⟩ ↦
        rTailPred_ne_rOutTail5_of_lt M hM5 s ⟨u.val, hlt47⟩ (hlt42.trans_le (Nat.le_add_right _ _))
          (hEqTail ▸ (rTot.wires.injective hs)).symm, hEqTail]
      simpa only [tailPredBit, Nat.ble_eq_true_of_le hlt42, ↓reduceIte] using
        stCoreClean_tailPred_lt42M decodeCoin M hM5 coreGates coreMask0 coreMask1 rTot η hz ⟨u.val,
            hlt47⟩ hlt42
    · change stW (rTot (midPredWireFn M hM5 u)) = _
      simp only [midPredWireFn, midPredBit, beq_false_of_ne (by omega : u.val ≠ 0),
        Bool.eq_false_iff.mpr fun l ↦
            hlt42 (Nat.le_trans (Nat.le_of_ble_eq_true l) (Nat.le_add_right 42 M)),
        Bool.eq_false_iff.mpr fun l ↦ hlt42 (Nat.le_of_ble_eq_true l), Nat.ble_eq_true_of_le hlt47,
        Bool.false_eq_true, ↓reduceIte, hTailW]
      generalize ht : (⟨(u.val - (42 + M)) % 5, midPred_tail_lt u⟩ : Fin 5) = t
      have htv : (u.val - (42 + M)) % 5 = t.val := congrArg Fin.val ht
      have hu_eq : u.val = (42 + t.val) + M :=
          ((fun _ ↦ by omega) (Nat.mod_eq_of_lt (by omega : u.val - (42 + M) < 5)))
      clear ht
      fin_cases t <;> simp [tail5OutIdx, hu_eq]
  · have hble (k : ℕ) (hk : ¬ u.val < k) : Nat.ble (u.val + 1) k = false :=
      Bool.eq_false_iff.mpr fun l ↦ hk (Nat.le_of_ble_eq_true l)
    have hwEq {w : Fin 6} (h : u.val = 47 + M ∧ w = w6_4 ∨ u.val = 48 + M ∧ w = w6_5) :
        rTot (rMidPred M hM5 u) = (rTot.compose (rRevTmp M hM5)) w := by
      rcases h with ⟨hu, rfl⟩ | ⟨hu, rfl⟩ <;>
        simp only [rMidPred, midPredWireFn, QRegister.compose, Function.Embedding.coeFn_mk, w6_4,
            rRevTmp, w6_5, beq_false_of_ne (by omega : u.val ≠ 0), hble 42 (by omega),
            hble (42 + M)
              (by omega), hble _ hlt47, Bool.false_eq_true, ↓reduceIte] <;>
              exact congrArg rTot.wires (congrArg rScrCompact1493.wires
              (Fin.ext (by
                dsimp
                omega)))
    rcases (show u.val = 47 + M ∨ u.val = 48 + M by
      have := u.isLt
      omega) with hu | hu
    · rw [hwEq (.inl ⟨hu, rfl⟩), stTmpClean, stepCB, writeReg_apply_reg, f4, show αT w6_0 =
          _ from hTailW 0,
        show αT w6_1 = _ from (hScrW ⟨M, by omega⟩).trans hM0, z2_mul_ite_bool]
      simp [midPredBit, tail5OutIdx, hu]
    · rw [hwEq (.inr ⟨hu, rfl⟩), stTmpClean, stepCB, writeReg_apply_reg, f5, show αT w6_2 =
          _ from hTailW 1,
        show αT w6_3 = _ from (hScrW ⟨M + 1, by omega⟩).trans hM1, z2_mul_ite_bool]
      simp [midPredBit, tail5OutIdx, hu]
end QuantumComputation.Specs.PhotochemistrySolution.Stage1AsymRevEngine
end
end


noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
  QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc Operator QProg Matrix Circuit
  Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
open QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortB
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.SelectOracles
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (sqrtHalf bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
def pairPermBits_c70 {m : ℕ} (j₀ : Fin m) (γ δ ξ : BitAssignment m) : BitAssignment m := fun j ↦
    ξ j + ξ j₀ * (if j = j₀ then 0 else γ j + δ j)
theorem embedUnitary_single_c70 {m n : ℕ} (rC : QRegister m n) (g : PrimitiveGate 1)
    (j₀ : Fin m) : rC.embedUnitary (Circuit.single g j₀).eval =
    (Circuit.single g (rC j₀)).eval := by
  dsimp only [Circuit.single, Circuit.eval]
  rw [← QRegister.embedUnitary_compose]
  exact congrArg (·.embedUnitary g.eval) (congrArg QRegister.mk (Function.Embedding.ext fun _ ↦
      rfl))
/-- Drop a clean `|0⟩` hypothesis on register `rC` untouched by `p`. -/
theorem subspaceStep_drop_disj_c70 {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)] (rC : QRegister m n)
    {R₁ R₂ : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (hDyn : DynWires (fun w ↦ ∀ j : Fin m, w ≠ rC j) p)
    (hR₁ : ∀ V : Unitary (2 ^ m), R₁ * (rC.embedUnitary V).1 = (rC.embedUnitary V).1 * R₁)
    (hR₂ : ∀ V : Unitary (2 ^ m), R₂ * (rC.embedUnitary V).1 = (rC.embedUnitary V).1 * R₂)
    (h0 : SubspaceStep (R₁ * rC.basisOutcomeProjector 0)
      (R₂ * rC.basisOutcomeProjector 0) p) :
    SubspaceStep R₁ R₂ p := fun Obs ↦ by
  obtain ⟨N, hw, _⟩ := h0 Obs
  refine ⟨N, hw, ?_⟩
  let P0 := rC.basisOutcomeProjector 0
  let P0L := (QRegister.whole m).basisOutcomeProjector 0
  let D : Operator (2 ^ n) := R₂ᴴ * Obs.1.1 * R₂ - R₁ᴴ * N.1.1 * R₁
  have hP0 : P0 = rC.embedMatrix P0L :=
    (congrArg (fun r : QRegister m n ↦ r.basisOutcomeProjector 0)
        (congrArg QRegister.mk (Function.Embedding.ext fun _ ↦ rfl) : rC =
        rC.compose (QRegister.whole m))).trans
      (basisOutcomeProjector_compose_zero rC (QRegister.whole m))
  have hQuad (V : Unitary (2 ^ m)) : ((rC.embedUnitary V).1 * P0)ᴴ * D * ((rC.embedUnitary V).1 *
      P0) = 0 := by
    let U := rC.embedUnitary V
    obtain ⟨N', hw', hm'⟩ := subspaceStep_mul_left_of_commutesWithDyn U
      (commutesWithDyn_embedUnitary_of_disj_c70 rC V hDyn) h0 Obs
    rw [congrFun (hw'.symm.trans hw) (fun _ ↦ 0),
      show U.1 * (R₁ * P0) = R₁ * (U.1 * P0) by rw [← Matrix.mul_assoc, ← hR₁ V, Matrix.mul_assoc],
      show U.1 * (R₂ * P0) = R₂ * (U.1 * P0) by rw [← Matrix.mul_assoc, ← hR₂ V, Matrix.mul_assoc],
      Matrix.conjTranspose_mul R₂, Matrix.conjTranspose_mul R₁] at hm'
    dsimp only [D]
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc] at hm' ⊢
    exact sub_eq_zero.mpr hm'
  have hDiag (γ : BitAssignment m) : ((uTogGen_c70 rC γ).1 * P0)ᴴ * D * ((uTogGen_c70 rC γ).1 *
      P0) = 0 := by
    simpa only [embedUnitary_uTogLocal_c70] using hQuad (uTogLocal_c70 γ)
  have hbj (j : Fin m) : (QRegister.block 0 m (Nat.zero_add m).le : QRegister m m) j = j :=
      Fin.ext (Nat.zero_add j.val)
  have hTog0 (θ : BitAssignment m) : (uTogLocal_c70 θ).1.mulVec (ket (0 : BitAssignment m)) =
      ket θ := by
    rw [uTogLocal_c70, uTogGen_mulVec_ket_c70]
    refine congrArg ket (funext fun j ↦ ?_)
    conv_lhs => rw [← hbj j]
    rw [togBits_c70, DynCircExt.writeReg_apply_reg, Pi.zero_apply, zero_add]
  have hA (θ : BitAssignment m) : (uTogGen_c70 rC θ).1 * P0 = rC.embedMatrix ((uTogLocal_c70 θ).1 *
      P0L) := by
    rw [← embedUnitary_uTogLocal_c70 rC θ, QRegister.embedUnitary_val, hP0, ← rC.embedMatrix_mul]
  have hBlock (γ δ : BitAssignment m) : projBits_c70 rC γ * D * projBits_c70 rC δ = 0 := by
    let Aγ := (uTogGen_c70 rC γ).1 * P0
    let Aδ := (uTogGen_c70 rC δ).1 * P0
    have hCore : Aγᴴ * D * Aδ = 0 := by
      rcases eq_or_ne γ δ with rfl | hγδ
      · exact hDiag γ
      · obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hγδ
        have hInv : Function.Involutive (pairPermBits_c70 j₀ γ δ) :=
          fun ξ ↦ funext fun j ↦ by simp [pairPermBits_c70, zmod2_add_cancel_c70]
        let Vb := uTogLocal_c70 γ * involUnitary_c70 (pairPermBits_c70 j₀ γ δ) hInv
        have hS (β : BitAssignment m) : (Circuit.single .S j₀).eval.1.mulVec (ket β) =
            (if β j₀ = 1 then Complex.I else 1) • ket β := by
          rw [Circuit.eval_single, QRegister.embedUnitary_val]
          change ((QRegister.singleton j₀).embedMatrix PrimitiveGate.S.eval.1).mulVec (XMeasUnld.ket
              β) = _
          rw [PhotochemistrySolution.XMeasUnld.singleton_embedMatrix_mulVec_ket]
          have e := Function.update_eq_self j₀ β
          rcases DynCircExt.bit_cases (β j₀) with hb | hb <;> rw [hb] at e <;>
            simp [PrimitiveGate.eval, Qubit.S, hb, e, show XMeasUnld.ket β = ket β from rfl]
        have hVb0 : Vb.1.mulVec (ket (0 : BitAssignment m)) = ket γ := by
          rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, involUnitary_mulVec_ket_c70,
            show pairPermBits_c70 j₀ γ δ 0 = 0 from funext fun j ↦
                by simp [pairPermBits_c70], hTog0 γ]
        have hVb1 : Vb.1.mulVec (ket (Function.update (0 : BitAssignment m) j₀ 1)) = ket δ := by
          dsimp only [Vb]
          rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, involUnitary_mulVec_ket_c70,
            uTogLocal_c70, uTogGen_mulVec_ket_c70]
          refine congrArg ket (funext fun j ↦ ?_)
          conv_lhs => rw [← hbj j]
          rw [togBits_c70, DynCircExt.writeReg_apply_reg, hbj j,
            pairPermBits_c70, Function.update_self, one_mul]
          rcases eq_or_ne j j₀ with rfl | hjj
          · rw [Function.update_self, ite_eq_left rfl, add_zero]
            rcases DynCircExt.bit_cases (γ j) with hγ | hγ <;>
              rcases DynCircExt.bit_cases (δ j) with hδ | hδ <;>
              rw [hγ, hδ] at hj₀ ⊢ <;> first | exact absurd rfl hj₀ | rfl
          · rw [Function.update_of_ne hjj, Pi.zero_apply, ite_eq_right hjj,
              zero_add, add_comm (γ j) (δ j), zmod2_add_cancel_c70]
        have hH0 : (Circuit.H j₀).eval.1.mulVec (ket (0 : BitAssignment m)) = sqrtHalf •
            (ket 0 + ket (Function.update (0 : BitAssignment m) j₀ 1)) := by
          have hk := ket_H j₀ (0 : BitAssignment m)
          rw [Pi.zero_apply, show XMeasUnld.bitSign 0 = 1 from rfl, one_smul,
            show Function.update (0 : BitAssignment m) j₀ 0 = 0 from funext fun j ↦ by
              by_cases h : j = j₀ <;> simp [h]] at hk
          exact hk
        have hQuadLin (V : Unitary (2 ^ m)) (c : ℂ)
            (hV0 : V.1.mulVec (ket 0) = sqrtHalf • (ket γ + c • ket δ)) :
            star c • (Aδᴴ * D * Aγ) + c • (Aγᴴ * D * Aδ) = 0 := by
          have q := hQuad V
          rw [show (rC.embedUnitary V).1 * P0 = sqrtHalf • (Aγ + c • Aδ) by
              rw [QRegister.embedUnitary_val, hP0, ← rC.embedMatrix_mul,
                show V.1 * P0L = sqrtHalf • ((uTogLocal_c70 γ).1 + c • (uTogLocal_c70 δ).1) *
                    P0L from
                  matrix_ext_ket fun ξ ↦ by
                    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
                        SelectRefl.ket_basisOutcomeProjector_zero]
                    by_cases hz : ∀ j : Fin m, ξ ((QRegister.whole m) j) = 0
                    · rw [ite_eq_left hz, show ξ = 0 from funext hz, Matrix.smul_mulVec,
                          Matrix.add_mulVec,
                        Matrix.smul_mulVec, hTog0 γ, hTog0 δ, hV0]
                    · rw [ite_eq_right hz, Matrix.mulVec_zero, Matrix.mulVec_zero],
                Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul, rC.embedMatrix_smul,
                rC.embedMatrix_add, rC.embedMatrix_smul, ← hA γ, ← hA δ],
            Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
            QubitizationWalkSem.star_sqrtHalf, Matrix.smul_mul, Matrix.smul_mul,
            Matrix.mul_smul, smul_smul, QubitizationWalkSem.sqrtHalf_mul_sqrtHalf] at q
          simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
            show Aγᴴ * D * Aγ = 0 from hDiag γ, show Aδᴴ * D * Aδ = 0 from hDiag δ,
            smul_zero, add_zero,
                zero_add] using (smul_eq_zero.mp q).resolve_left (one_div_ne_zero two_ne_zero)
        exact (smul_eq_zero.mp (show (2 : ℂ) • (Aγᴴ * D * Aδ) = 0 by
          rw [two_smul, show Aγᴴ * D * Aδ + Aγᴴ * D * Aδ =
              (Aδᴴ * D * Aγ + Aγᴴ * D * Aδ) + (Aγᴴ * D * Aδ - Aδᴴ * D * Aγ) by abel,
            show Aδᴴ * D * Aγ + Aγᴴ * D * Aδ = 0 by
              simpa only [star_one, one_smul] using hQuadLin (Vb * (Circuit.H j₀).eval) 1 (by
                rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hH0, Matrix.mulVec_smul,
                    Matrix.mulVec_add, hVb0, hVb1, one_smul]),
            (smul_eq_zero.mp (by
              rw [smul_sub, sub_eq_add_neg, add_comm, ← neg_smul]
              simpa only [Complex.star_def, Complex.conj_I] using
                hQuadLin (Vb * ((Circuit.H j₀).seq (Circuit.S j₀)).eval) Complex.I (by
                  rw [Circuit.eval_seq]
                  change (Vb.1 * ((Circuit.S j₀).eval.1 * (Circuit.H j₀).eval.1)).mulVec _ = _
                  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
                    hH0, Matrix.mulVec_smul, Matrix.mulVec_add, hS, hS, Pi.zero_apply,
                        Function.update_self,
                    ite_eq_right (by decide : (0 : ZMod 2) ≠ 1), ite_eq_left rfl, one_smul,
                        Matrix.mulVec_smul,
                    Matrix.mulVec_add, Matrix.mulVec_smul, hVb0, hVb1]) :
              Complex.I • (Aγᴴ * D * Aδ - Aδᴴ * D * Aγ) = 0)).resolve_left Complex.I_ne_zero,
            add_zero])).resolve_left two_ne_zero
    rw [show projBits_c70 rC γ = (uTogGen_c70 rC γ).1 * Aγᴴ by
        dsimp only [Aγ, P0]
        rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose,
            uTogGen_herm_c70, ← Matrix.mul_assoc]
        rfl, show projBits_c70 rC δ = Aδ * (uTogGen_c70 rC δ).1 from rfl]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Aγᴴ, ← Matrix.mul_assoc (Aγᴴ * D), hCore, Matrix.zero_mul,
        Matrix.mul_zero]
  exact sub_eq_zero.mp (show D = 0 by
    rw [← Matrix.one_mul D, ← Matrix.mul_one (1 * D), ← sum_projBits_c70 rC]
    simp only [Finset.sum_mul, Matrix.mul_sum, hBlock, Finset.sum_const_zero])
theorem pScrExt_comm_rCoinExt_c70 {kExt n : ℕ} [NeZero (2 ^ n)] (hk : kExt ≤ 72)
    (rTot : QRegister dLayout n)
    (V : Unitary (2 ^ kExt)) :
    (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 *
        ((rTot.compose (rCoinExt kExt hk)).embedUnitary V).1 =
      ((rTot.compose (rCoinExt kExt hk)).embedUnitary V).1 *
          (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 :=
  (rTot.compose (rScrExt kExt hk)).embedMatrix_comm_of_disjoint (rTot.compose (rCoinExt kExt hk))
    (QRegister.disjoint_iff.mpr fun i j e ↦ by
      have hi : i.val < scrLExt kExt := i.isLt
      have hv := congrArg Fin.val (rTot.wires.injective e)
      rw [val_rScrExt, val_rCoinExt] at hv
      dsimp [scrLExt] at hi
      omega) (compProj 0) V.1
theorem hP0_rScrExt_c70 {kExt n : ℕ} [NeZero (2 ^ n)] (hk : kExt ≤ 72)
    (rTot : QRegister dLayout n) : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 *
    (rTot.compose (rCoinExt kExt hk)).basisOutcomeProjector 0 =
    (rTot.compose rScrLayout).basisOutcomeProjector 0 := by
  let rC := rTot.compose (rCoinExt kExt hk)
  have hu0 : (uTogGen_c70 rC (fun _ ↦ 0)).1 = 1 := matrix_ext_ket fun β ↦ by
    rw [uTogGen_mulVec_ket_c70, Matrix.one_mulVec]
    exact congrArg ket (by simpa only [togBits_c70, add_zero] using writeReg_self rC β)
  simpa only [projBits_c70, rC, hu0, Matrix.one_mul,
      Matrix.mul_one] using pScrExt_mul_projBits_c70 hk rTot (fun _ ↦ 0)
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift

namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.Stage2PotUnld PhotochemistrySolution.Stage2ElecFirst
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr uRouterSwapConj
theorem wStage1Clean_comm_rCoinExt_c70 (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector) {kExt n : ℕ}
    (hk : kExt ≤ 72) (rTot : QRegister dLayout n) (V : Unitary (2 ^ kExt)) :
    (rTot.embedUnitary (uStage1Clean_c70 decodeCoin)).1 *
    ((rTot.compose (rCoinExt kExt hk)).embedUnitary V).1 =
    ((rTot.compose (rCoinExt kExt hk)).embedUnitary V).1 *
    (rTot.embedUnitary (uStage1Clean_c70 decodeCoin)).1
    := by rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
            QRegister.embedUnitary_val, ← rTot.embedMatrix_mul,
            ← rTot.embedMatrix_mul]; exact congrArg rTot.embedMatrix (uStage1Clean_comm_rCoinExt_c70
            decodeCoin hk V.1)
theorem wStage1Clean_mul_rScrLayout_c70 {w1 n : ℕ} [NeZero (2 ^ n)]
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} (o1 : Stage1ZeroNEremLayout w1 decodeCoin)
    (rTot : QRegister dLayout n) : (rTot.embedUnitary (uStage1Clean_c70 decodeCoin)).1 *
    (rTot.compose rScrLayout).basisOutcomeProjector 0 = (rTot.embedUnitary o1.uLocal).1 *
    (rTot.compose rScrLayout).basisOutcomeProjector 0
    := by rw [basisOutcomeProjector_compose_zero, QRegister.embedUnitary_val,
            QRegister.embedUnitary_val, ← rTot.embedMatrix_mul,
            ← rTot.embedMatrix_mul]; exact congrArg rTot.embedMatrix (uStage1Clean_mul_pScr_c70
            o1)
theorem wNoHadClean_mul_rScrLayout_c70 {w1 n : ℕ} [NeZero (2 ^ n)]
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} (o1 : Stage1ZeroNEremLayout w1 decodeCoin)
    (rTot : QRegister dLayout n) : (rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))).1 *
    (rTot.compose rScrLayout).basisOutcomeProjector 0 = (rTot.embedUnitary (wNoHad o1.uLocal)).1 *
    (rTot.compose rScrLayout).basisOutcomeProjector 0
    := by rw [basisOutcomeProjector_compose_zero, QRegister.embedUnitary_val,
            QRegister.embedUnitary_val, ← rTot.embedMatrix_mul,
            ← rTot.embedMatrix_mul]; exact congrArg rTot.embedMatrix
            (wNoHad_uStage1Clean_mul_pScr_c70 o1)
/-- Lift forward Stage-1 `o1.fwdAmb` to `rScrExt kExt hk` for any `rCoinExt`-disjoint Stage 1. -/
theorem subspaceStep_stage1_fwd_ext_c70 {Var : Type} [Fintype Var] [DecidableEq Var] {kExt w1 n : ℕ}
    [NeZero (2 ^ n)] {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} (hk : kExt ≤ 72)
    (o1 : Stage1ZeroNEremLayout w1 decodeCoin) (v : Var) (rTot : QRegister dLayout n)
    {X : Operator (2 ^ n)}
    (hDyn : DynWires (fun u ↦ ∀ j : Fin kExt, u ≠ (rTot.compose (rCoinExt kExt hk)) j)
    (o1.fwdAmb v rTot)) (hX : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X) :
    SubspaceStep X ((rTot.embedUnitary (uStage1Clean_c70 decodeCoin)).1 * X) (o1.fwdAmb v rTot)
    := by
  simpa only [Matrix.mul_assoc, hX] using subspaceStep_mul_right X
    (subspaceStep_drop_disj_c70 (rTot.compose (rCoinExt kExt hk))
      (R₂ := (rTot.embedUnitary (uStage1Clean_c70 decodeCoin)).1 *
        (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0)
      hDyn (pScrExt_comm_rCoinExt_c70 hk rTot)
      (fun V ↦ by rw [Matrix.mul_assoc, pScrExt_comm_rCoinExt_c70 hk rTot V, ← Matrix.mul_assoc,
        wStage1Clean_comm_rCoinExt_c70 decodeCoin hk rTot V, Matrix.mul_assoc])
      (subspaceStep_congr_in (hP0_rScrExt_c70 hk rTot)
        (subspaceStep_congr_out (SubspaceStep.of_clean (o1.step_and_counts v rTot).1
          (RouterSelectWiringB.proj_absorb_gen _ _ fun q ↦
            (rScrCompact1493_sub_scr q).imp fun _ ↦ congrArg rTot.wires))
          (by rw [← wStage1Clean_mul_rScrLayout_c70 o1 rTot, ← hP0_rScrExt_c70 hk rTot,
                Matrix.mul_assoc]))))
/-- Generic operator-sum lift of `L₁ * R₀ = L₂ * R₀` to any `X` absorbed by `P_ext`. -/
theorem lift_eq_of_pScrExt_c70 {kExt n : ℕ} [NeZero (2 ^ n)] (hk : kExt ≤ 72)
    (rTot : QRegister dLayout n) {L₁ L₂ X : Operator (2 ^ n)}
    (hEq0 : L₁ * (rTot.compose rScrLayout).basisOutcomeProjector 0 = L₂ *
    (rTot.compose rScrLayout).basisOutcomeProjector 0) (hL₁ : ∀ γ : BitAssignment kExt, L₁ *
    (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 =
    (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 * L₁) (hL₂ : ∀ γ : BitAssignment kExt, L₂ *
    (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 =
    (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 * L₂)
    (hX : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X) : L₁ * X = L₂ * X := by
  rw [← hX, pScrExt_eq_sum_tog_c70 hk rTot]
  simp only [Finset.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc L₁, hL₁ γ, ← Matrix.mul_assoc L₂, hL₂ γ]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc L₁, hEq0]
  simp only [Matrix.mul_assoc]
theorem comm_uRouterSwapConj_embedUnitary_c70 {M D m n : ℕ} [NeZero (2 ^ n)] (r₁ : RouterReg M D n)
    (rC : QRegister m n) (hDisj : ∀ (i : Fin (routerWidth M D)) (j : Fin m), r₁ i ≠ rC j)
    (V : Unitary (2 ^ m)) : (uRouterSwapConj r₁).1 * (rC.embedUnitary V).1 = (rC.embedUnitary V).1 *
    (uRouterSwapConj r₁).1 :=
  PhotochemistrySolution.SplitRouter47_187.comm_uRouterSwapConj_embedMatrix r₁ rC hDisj V.1
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
end

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
  QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
attribute [local irreducible] PgBase.phaseGradientState systemQubits_frozen uRouterSwapConj
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectCsa64ProvSpec
open PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.Stage2QromMux
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local irreducible] SelectCompactAnc.ancWOfScr
theorem rNucXor0_eq_of_lt1238 {i : Fin (routerWidth 47 6)} (hi : i.val < 1238) : rNucXor0 i =
    rNucLayout i := by
  exact dite_eq_left hi
theorem rNucXor0_roles_eq : rHas1 rNucXor0 = rHas1 rNucLayout ∧ rRawHas2 rNucXor0 =
    rRawHas2 rNucLayout ∧ rIdx1 rNucXor0 = rIdx1 rNucLayout ∧ rIdx2 rNucXor0 = rIdx2 rNucLayout ∧
    rBufLo rNucXor0 = rBufLo rNucLayout ∧ rBufHi rNucXor0 = rBufHi rNucLayout ∧ rHA rNucXor0 =
    rHA rNucLayout ∧ rHB rNucXor0 = rHB rNucLayout ∧ rSys rNucXor0 = rSys rNucLayout := by
  have eqk {k : ℕ} {hk : k < routerWidth 47 6} (h : k < 1238 := by omega) :
      rNucXor0 ⟨k, hk⟩ = rNucLayout ⟨k, hk⟩ := rNucXor0_eq_of_lt1238 h
  exact ⟨rNucXor0_eq_of_lt1238 (by
    dsimp
    omega),
    rNucXor0_eq_of_lt1238 (show 1 % routerWidth 47 6 < 1238 by
      rw [hNW1394]
      decide),
    funext fun _ ↦ eqk, funext fun _ ↦ eqk, funext fun _ ↦ eqk,
    funext fun _ ↦ eqk, funext fun _ ↦ eqk, funext fun _ ↦ eqk, funext fun _ ↦ funext fun _ ↦ eqk⟩
/-- Outer-Elec ket and operator chain on `(rNucXor0, rElecBorrow96)`. -/
theorem routerChain_elecFirst {n wIn : ℕ} [NeZero (2 ^ n)]
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} (rTot : QRegister dLayout n)
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {X : Operator (2 ^ n)}
    (hX : (rTot.compose rScrLayout).basisOutcomeProjector 0 * X = X) :
    SupportedOn (ValidRouterInput (rTot.compose rElecBorrow96))
    ((rTot.embedUnitary o1.uLocal).1 * X) ∧ SupportedOn (ValidRouterInput (rTot.compose rNucXor0))
    ((uRouterSwapConj (rTot.compose rElecBorrow96)).1 * ((rTot.embedUnitary o1.uLocal).1 * X)) ∧
    (uRouterSwapConj (rTot.compose rNucXor0)).1 *
    ((uRouterSwapConj (rTot.compose rElecBorrow96)).1 * ((rTot.embedUnitary o1.uLocal).1 * X)) =
    (rTot.embedUnitary (wNoHad o1.uLocal)).1 * X ∧
    (rTot.compose rScrCompact1493).basisOutcomeProjector 0 * ((rTot.embedUnitary o1.uLocal).1 * X) =
    (rTot.embedUnitary o1.uLocal).1 * X ∧ (rTot.compose rClean690Layout).basisOutcomeProjector 0 *
    ((rTot.embedUnitary (wNoHad o1.uLocal)).1 * X) = (rTot.embedUnitary (wNoHad o1.uLocal)).1 *
    X := by
  let _ : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  obtain ⟨_, _, _, c1493, c690⟩ :=
      routerChain rTot rElecXor179 rElecXor179_roles_eq rElecXor179_loc_scr o1 hX
  have hCl (ξ : BitAssignment n) : inKetPred (fun η ↦ CleanScr (fun i ↦ η (rTot i)))
      (X.mulVec (ket ξ)) :=
    fun η hnz ↦ by
      by_contra hnot
      have h := congrFun (congrArg (·.mulVec (ket ξ)) hX) ((basisBitsEquiv n).symm η)
      rw [← Matrix.mulVec_mulVec, proj_zero_vec_entry (rTot.compose rScrLayout) _ η,
        ite_eq_right (id hnot : ¬ ∀ i : Fin scrLLayout, η ((rTot.compose rScrLayout) i) = 0)] at h
      exact hnz h.symm
  have eqI {D : ℕ} {f g : Fin D → Wire dLayout} {α β : BitAssignment dLayout}
      (h : ∀ d, α (f d) = β (g d)) :
      idxValD f α = idxValD g β :=
    Nat.eq_of_testBit_eq fun d ↦ by by_cases hd : d < D <;> simp [testBit_idxValD, hd, h]
  have hS0 {α : BitAssignment dLayout} (hS : CleanScr α) (c) (z) (m : Fin scrLLayout)
      (hbd : m.val < 65 ∨ 105 ≤ m.val) : routedStage1 decodeCoin α c z (rScrLayout m) = 0 := by
    have _ : scrLLayout = 1565 ∧ m.val < scrLLayout := ⟨rfl, m.isLt⟩
    rw [routedStage1, routedStage0, writeReg_apply_of_not_mem _ rOut40Layout _ _ fun ⟨k, hk⟩ ↦
        (fun _ _ ↦
            by omega) k.isLt ((val_rOut40Layout k).symm.trans ((congrArg Fin.val hk).trans
                 (val_rScrLayout m))),
      writeReg_apply_of_not_mem _ rLcu82Layout _ _ fun ⟨l, hl⟩ ↦
        (fun _ _ ↦
            by omega) l.isLt ((val_rLcu82Layout l).symm.trans ((congrArg Fin.val hl).trans
                 (val_rScrLayout m)))]
    exact hS m
  have hVE1 {α : BitAssignment dLayout} (hS : CleanScr α) (c) (z) :
      ValidRouterInput rElecLayout (routedStage1 decodeCoin α c z) := by
    obtain ⟨_, hE, h2, _, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hS c z
    exact ⟨by simpa only [← hE] using h2.1,
        by simpa only [← hE, eqI fun _ ↦ (hE _).symm] using h2.2.1,
      by simpa only [← hE, eqI fun _ ↦ (hE _).symm] using h2.2.2.1, fun b ↦
          by simpa only [← hE] using h2.2.2.2.1 b,
      fun _ hw ↦ by
        rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
        exact (hE j).symm ▸ h2.2.2.2.2 _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩
  have hEB {α : BitAssignment dLayout} (hS : CleanScr α) (c) (z) :
      ValidRouterInput rElecBorrow96 (routedStage1 decodeCoin α c z) := by
    obtain ⟨h1, h2, hi1, hi2, hBL, hBH, hA, hB, _⟩ := rElecBorrow96_roles_eq
    have hVE := hVE1 hS c z
    refine ⟨h1 ▸ h2 ▸ hVE.1, h1 ▸ hi1 ▸ hVE.2.1, h2 ▸ hi2 ▸ hVE.2.2.1,
      fun b ↦ hBL ▸ hBH ▸ hA ▸ hB ▸ hVE.2.2.2.1 b, fun _ hw ↦ ?_⟩
    rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
    have hge : 4602 ≤ i.val := (Finset.mem_filter.mp hi).2
    let j : Fin 454 := ⟨i.val - 4602, (fun _ : i.val < 5056 ↦ by omega) (i.isLt.trans_eq hEW5056)⟩
    obtain ⟨m, hm, hbd⟩ := rElecBorrow96_loc_scr j
    exact (congrArg _ ((congrArg rElecBorrow96
      (Fin.ext (Nat.add_sub_of_le hge).symm : i = ⟨4602 + j.val, privIdx_lt j⟩)).trans hm)).trans
      (hS0 hS c z m hbd)
  have hN0 {α : BitAssignment dLayout} (hS : CleanScr α) (c) (z) :
      ValidRouterInput rNucXor0 (routerSwapBits rElecLayout (routedStage1 decodeCoin α c z))
          := by
    let δ₁ := routedStage1 decodeCoin α c z
    obtain ⟨hVN, _, _, _, _, _⟩ := validRouter_stage1 (decodeCoin := decodeCoin) hS c z
    obtain ⟨h1, h2, hi1, hi2, hBL, hBH, hA, hB, _⟩ := rNucXor0_roles_eq
    have hDE (i : Fin (routerWidth 47 6)) (k : ℕ) (hk : k < 5056) {hk' : k < routerWidth 187 8} :
        rNucXor0 i ≠ rElecLayout ⟨k, hk'⟩ := fun e ↦ by
      have _ : i.val < 1394 := hNW1394 ▸ i.isLt
      have hb :=
          (val_nucXor0WireFn i).symm.trans ((congrArg Fin.val e).trans (val_elecRouterWireFn ⟨k,
          hEW5056 ▸ hk⟩))
      dsimp at hb
      split_ifs at hb <;> omega
    have sN0 (i : Fin (routerWidth 47 6)) : routerSwapBits rElecLayout δ₁ (rNucXor0 i) =
        δ₁ (rNucXor0 i) :=
      routerSwapBits_outside_mod rElecLayout (hVE1 hS c z) (fun b ↦ hDE i (18 + b.val) (by omega))
        (fun b ↦ hDE i (42 + b.val) (by omega)) (fun p b ↦ hDE i (114 + 24 * p.val + b.val)
            (by omega))
    have eqR (i) {w} (he : rNucXor0 i = w) := (sN0 i).trans (congrArg δ₁ he)
    refine ⟨(eqR _ h1).symm ▸ (eqR _ h2).symm ▸ hVN.1,
      (eqR _ h1).symm ▸ (eqI fun d ↦ eqR _ (congrFun hi1 d)).symm ▸ hVN.2.1,
      (eqR _ h2).symm ▸ (eqI fun d ↦ eqR _ (congrFun hi2 d)).symm ▸ hVN.2.2.1,
      fun b ↦
          ⟨(eqR _ (congrFun hBL b)).trans (hVN.2.2.2.1 b).1,
          (eqR _ (congrFun hBH b)).trans (hVN.2.2.2.1 b).2.1,
        (eqR _ (congrFun hA b)).trans (hVN.2.2.2.1 b).2.2.1,
            (eqR _ (congrFun hB b)).trans (hVN.2.2.2.1 b).2.2.2⟩,
      fun _ hw ↦ ?_⟩
    rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
    have _ : 1238 ≤ i.val ∧ i.val < 1394 ∧ scrLLayout = 1565 :=
        ⟨(Finset.mem_filter.mp hi).2, hNW1394 ▸ i.isLt, rfl⟩
    rw [sN0 i]
    change δ₁ (nucXor0WireFn i) = 0
    dsimp only [nucXor0WireFn]
    rw [dite_eq_right (by omega)]
    split_ifs
    · exact hS0 hS c z ⟨30 + (i.val - 1238), by omega⟩ (.inl (by
      dsimp
      omega))
    · exact hS0 hS c z ⟨297 + (i.val - 1238 - 20), by omega⟩ (.inr (by
      dsimp
      omega))
  have stE (η : BitAssignment n) (hS : CleanScr (fun i ↦ η (rTot i))) :
      (uRouterSwapConj (rTot.compose rElecBorrow96)).1.mulVec
          ((rTot.embedUnitary o1.uLocal).1.mulVec (ket η)) =
      ket (DynCircExt.writeReg η rTot (routerSwapBits rElecLayout (routedStage1 decodeCoin
          (fun i ↦ η (rTot i))
        (outerCoinOf82 (fun i ↦ η (rTot (rLcu82Layout i))))
        (innerBitsOf82 (fun i ↦ η (rTot (rLcu82Layout i))))))) := by
    rw [w1Ket rTot o1 η hS, uRouterSwapConj_ket_eq (rTot.compose rElecBorrow96)
        (validRouter_compose_writeReg rTot rElecBorrow96 η _ (hEB hS _ _)),
      routerSwapBits_compose_writeReg rTot rElecBorrow96 η _,
      routerSwapBits_congr_roles rElecBorrow96 rElecLayout rElecBorrow96_roles_eq _]
  refine ⟨supportedOn_of_inKetPred fun ξ ↦ by
      rw [← Matrix.mulVec_mulVec]
      exact inKetPred_mulVec _ (fun η hS ↦ w1Ket rTot o1 η hS ▸
        inKetPred_ket (validRouter_compose_writeReg rTot rElecBorrow96 η _ (hEB hS _ _)))
            (hCl ξ),
    supportedOn_of_inKetPred fun ξ ↦ by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      exact inKetPred_mulVec _ (fun η hS ↦ ((Matrix.mulVec_mulVec _ _ _).symm.trans (stE η hS)) ▸
        inKetPred_ket (validRouter_compose_writeReg rTot rNucXor0 η _ (hN0 hS _ _))) (hCl ξ),
    ?_, c1493, c690⟩
  simp only [← Matrix.mul_assoc]
  refine supportedOn_of_inKetPred hCl _ _ fun η hS ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  rw [stE η hS, uRouterSwapConj_ket_eq (rTot.compose rNucXor0)
      (validRouter_compose_writeReg rTot rNucXor0 η _ (hN0 hS _ _)),
    routerSwapBits_compose_writeReg rTot rNucXor0 η _,
    routerSwapBits_congr_roles rNucXor0 rNucLayout rNucXor0_roles_eq _,
    routerSwap_nuc_elec_comm (validRouter_stage1 (decodeCoin :=
        decodeCoin) hS _ _).1 (hVE1 hS _ _),
    QRegister.embedUnitary_val,
        embedMatrix_ket_eq_writeReg rTot _ η ((congrArg (wNoHad o1.uLocal).1.mulVec
      (congrArg ket (routedStage0_self _).symm)).trans (wNoHad_mulVec_ket o1 hS _ _))]
  rfl
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecFirst

namespace QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
set_option exponentiation.threshold 8192
open PhotochemistrySolution.KetSupport PhotochemistrySolution.GenWeightsSelect
  PhotochemistrySolution.BlockApprox PhotochemistrySolution.Stage2ElecFirst
open PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.SelectCompactAnc
attribute [local reducible] totDimCompactGen
attribute [local irreducible] PhotochemistrySolution.SelectCompactAnc.ancWOfScr reflULGen
theorem concat_compose_rScrExt_c70 {kExt n : ℕ} (hk : kExt ≤ 72)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrWLayout) n)
    (hdisj : rSys.DisjointWires rAnc) : (rSys.concat rAnc hdisj).compose (rScrExt kExt hk) =
    rAnc.compose (scrSubLGen (hpExt kExt hk)) :=
  congrArg QRegister.mk (Function.Embedding.ext
    (FusedUnembedLGen.concat_rScr_apply_fs (hpExt kExt hk) rSys rAnc hdisj))
end QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
end

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.KetSupport PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ZeroNEremSpec
attribute [local reducible] totDimCompactGen
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
  PgBase.phaseGradientState reflULGen
theorem rankOne_cat8_decomp (Mcat : Operator (2 ^ 8)) : ∃ (E : Fin (2 ^ 8) → Fin (2 ^ 8) →
    Operator (2 ^ 8)), (∑ k : Fin (2 ^ 8), E k 0 * Mcat * E 0 k) =
    (Mcat 0 0) • (1 : Operator (2 ^ 8)) := by
  let E (a b : Fin (2 ^ 8)) : Operator (2 ^ 8) := Matrix.of fun i j ↦ if i = a ∧ j = b then 1 else 0
  have s0 (f : Fin (2 ^ 8) → ℂ) (x) (hf : ∀ y ≠ x, f y = 0) :=
      Finset.sum_eq_single x (fun y _ ↦ hf y) fun h ↦ (h (Finset.mem_univ x)).elim
  have hU (k : Fin (2 ^ 8)) : E k 0 * Mcat * E 0 k = (Mcat 0 0) • E k k := Matrix.ext fun a b ↦ by
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, E]
    rw [s0 _ 0 fun x hx ↦ by simp [hx], s0 _ 0 fun y hy ↦ by simp [hy]]
    by_cases hak : a = k <;> by_cases hbk : b = k <;> simp [hak, hbk]
  refine ⟨E, Matrix.ext fun i j ↦ ?_⟩
  simp only [hU, Matrix.sum_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, E]
  rw [s0 _ i fun k hk ↦ by simp [hk.symm]]
  by_cases h : i = j <;> simp [h, eq_comm]
theorem comm_of_cat8_embed {N : ℕ} (rCat : QRegister 8 N) (Mcat : Operator (2 ^ 8))
    (hc0 : Mcat 0 0 ≠ 0) (P S U : Operator (2 ^ N))
    (cP : ∀ M : Operator (2 ^ 8), P * rCat.embedMatrix M = rCat.embedMatrix M * P)
    (cS : ∀ M : Operator (2 ^ 8), S * rCat.embedMatrix M = rCat.embedMatrix M * S)
    (hCat : U * rCat.embedMatrix Mcat = S * rCat.embedMatrix Mcat) (hCommU : P * U = U * P) : P *
    S = S * P := by
  let D : Operator (2 ^ N) := P * S - S * P
  obtain ⟨E, hSum⟩ := rankOne_cat8_decomp Mcat
  refine sub_eq_zero.mp ((smul_eq_zero.mp (?_ : (Mcat 0 0) • D = 0)).resolve_left hc0)
  rw [show (Mcat 0 0) • D = D * rCat.embedMatrix (∑ k : Fin (2 ^ 8), E k 0 * Mcat * E 0 k) by
      rw [hSum, rCat.embedMatrix_smul, rCat.embedMatrix_one, mul_smul_comm, mul_one],
          rCat.embedMatrix_sum, Matrix.mul_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [rCat.embedMatrix_mul, rCat.embedMatrix_mul, ← Matrix.mul_assoc D, ← Matrix.mul_assoc D,
    show D * rCat.embedMatrix (E k 0) = rCat.embedMatrix (E k 0) * D by
      dsimp only [D]
      rw [sub_mul, mul_sub, Matrix.mul_assoc, cS _, ← Matrix.mul_assoc P _ S, cP _,
        Matrix.mul_assoc, Matrix.mul_assoc, cP _, ← Matrix.mul_assoc S _ P, cS _, Matrix.mul_assoc],
    Matrix.mul_assoc _ D, show D * rCat.embedMatrix Mcat = 0 by
      dsimp only [D]
      rw [sub_mul, Matrix.mul_assoc P S, ← hCat, ← Matrix.mul_assoc P, hCommU, Matrix.mul_assoc U P,
        cP Mcat, ← Matrix.mul_assoc U, hCat, Matrix.mul_assoc S, ← cP Mcat, ← Matrix.mul_assoc S,
            sub_self], mul_zero, zero_mul]
theorem comm_pScr_id_of_usel {wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) (uId uUsel : Operator.Unitary (2 ^ dLayout))
    (hIdOff : ∀ {m : ℕ} (r : QRegister m dLayout) (M : Operator (2 ^ m)),
    OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r → Commute uId.1 (r.embedMatrix M))
    (hCatPre : (preConj o1.uLocal uUsel).1 * cat8SharedProjCompactGen scrWLayout =
    (preConj o1.uLocal uId).1 * cat8SharedProjCompactGen scrWLayout)
    (hCommU : pScr * (preConj o1.uLocal uUsel).1 = (preConj o1.uLocal uUsel).1 * pScr) :
    pScr * (preConj o1.uLocal uId).1 = (preConj o1.uLocal uId).1 * pScr := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  have : NeZero (2 ^ (totDimCompactGen scrWLayout)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hz : PgBase.phaseGradientState 8 0 ≠ 0 := by
    rw [phaseGradientState_apply 8 0]
    exact mul_ne_zero (one_div_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)))
          (Complex.exp_ne_zero _)
  exact comm_of_cat8_embed (locCat8SharedCompactGen scrWLayout)
      (Matrix.vecMulVec (PgBase.phaseGradientState 8) (star (PgBase.phaseGradientState 8)))
      (mul_ne_zero hz (star_ne_zero.mpr hz)) pScr (preConj o1.uLocal uId).1 (preConj o1.uLocal
      uUsel).1 (fun M ↦ (pScr_comm_off hoff_cat8_layout M).eq)
      (fun M ↦ (preConj_comm_off o1 uId hIdOff hoff_cat8_layout M).eq) hCatPre hCommU
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192
open DynamicCircuit QuantumComputation.Specs PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.Kinetic664
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.Qft8PostCancelT5 PhotochemistrySolution.Stage4KinFull
  PhotochemistrySolution.SelectQft8KinMid
open PhotochemistrySolution.SelectQromKetBridge PhotochemistrySolution.TargetBScr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState Stage4Kin14Scb.abpKin14Usel Stage4Kin14Scb.abpKin14Csel
    Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel
    Kinetic664.abpKin15SqFree2m1Csel Qft8PostCancelT5.qft8PostCancel98CatU
    Qft8PostCancelT5.polyPostCancelT5Qft8Bracket98 Stage4KinFull.bAxisMux27 bSpeciesSwap50
theorem uKinCoreCat2m1_98Usel_pw_comm {w : Wire dLayout} (hw1 : ¬(5642 ≤ w.val ∧ w.val ≤ 5649))
    (hw2 : ¬(5755 ≤ w.val ∧ w.val ≤ 5778)) (hw3 : ¬(6083 ≤ w.val ∧ w.val ≤ 6603)) :
    uKinCoreCat2m1_98UselLayout.1 * rWorkInnerLayout.basisOutcomeProjector 0 =
    rWorkInnerLayout.basisOutcomeProjector 0 * uKinCoreCat2m1_98UselLayout.1 ∧
    (uKinCoreCat2m1_98UselLayout.1 * rWorkInnerLayout.basisOutcomeProjector 0) * pBit0 w =
    pBit0 w * (uKinCoreCat2m1_98UselLayout.1 * rWorkInnerLayout.basisOutcomeProjector 0) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  have hd : dLayout = 7298 := hDLayout_w0
  let PW := rWorkInnerLayout.basisOutcomeProjector 0
  let P := pBit0 w
  let Qcat : Unitary (2 ^ dLayout) :=
      qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout
  have hpq : PW * P = P * PW :=
      rWorkInnerLayout.embedMatrix_comm_of_disjoint (QRegister.singleton w)
    (QRegister.disjoint_iff.mpr fun k i e ↦ by
      have hv := congrArg Fin.val (e.trans (QRegister.singleton_apply w i))
      rw [val_rWorkInnerLayout] at hv
      exact hw3 ⟨by omega, by omega⟩)
          (compProj 0) (compProj 0)
  have cM : (uMux27Layout.1 * PW) * P = P * (uMux27Layout.1 * PW) :=
      ketPerm_on_pw_comm_bit0 uMux27Layout.1
    (fun δ ↦ DynCircExt.writeReg δ rMux27Layout (bAxisMux27.evalS (fun j ↦ δ (rMux27Layout j))))
    (fun δ _ ↦
        by rw [uMux27Layout, embedUnitary_toBracket_ket,
             StructuredCB.toCB_evalBits_eq_evalS bAxisMux27_props.2.2]) w hpq fun δ h ↦ by
      if hm : w ∈ Set.range rMux27Layout.wires then
        obtain ⟨j, rfl⟩ := hm
        rw [DynCircExt.writeReg_apply_reg]
        obtain ⟨y0, y1, _, _⟩ := bAxisMux27_evalS (fun k ↦ δ (rMux27Layout k)) (h ⟨21, by omega⟩)
        have hvj : (mux27WireFn j).val = (rMux27Layout j).val :=
            congrArg Fin.val (rMux27_eq_fn_w0 j).symm
        rw [val_mux27WireFn] at hvj
        exact (show j.val = 0 ∨ j.val = 1 by split_ifs at hvj <;> omega).elim
          (fun hj0 ↦ (Fin.ext hj0 : j = wMux 0) ▸ y0) (fun hj1 ↦ (Fin.ext hj1 : j = wMux 1) ▸ y1)
      else exact DynCircExt.writeReg_apply_of_not_mem δ rMux27Layout _ w hm
  have ic (U : Unitary (2 ^ dLayout)) := inv_comm_proj U.1 (U⁻¹).1 PW P
    (congrArg Subtype.val (inv_mul_cancel U)) (congrArg Subtype.val (mul_inv_cancel U))
  let mp (A B : Operator (2 ^ dLayout)) := mul_proj_comm A B PW P pw_mul_self
  have cMi := ic uMux27Layout uMux27Layout_comm_rWorkInner hpq cM
  have hQpw : Qcat.1 * PW = PW * Qcat.1 := by
    simpa only [QRegister.whole_compose,
        QRegister.whole_embedUnitary] using (qft8PostCancel98Bracket_cleanStep_catU_of_subreg ()
      scrWLayout offKinLayout hoffKinLayout rPKinLayout qft8Stg3ValidP_layout rWorkInnerLayout
      (fun i ↦ ⟨⟨i.val, by omega⟩, qft8Stg3Clean13_eq_workInner i⟩)
      (QRegister.disjoint_iff.mpr fun k i e ↦
          by
            have e0 :=
               congrArg Fin.val e
            rw [val_rWorkInnerLayout, val_rPKinLayout] at e0
            omega)
      (QRegister.disjoint_iff.mpr fun k c e ↦ by
        have e0 :=
            (congrArg Fin.val e).trans (val_locCat8_layout c)
        rw [val_rWorkInnerLayout] at e0
        omega)
      (QRegister.whole dLayout)).1.1
  have cQ : (Qcat.1 * PW) * P = P * (Qcat.1 * PW) :=
      (comm_mul P Qcat.1 PW (localOnQft16_comm_basisOutcomeProjector
    (qft8PostCancel98CatU_localOnQft16 () scrWLayout offKinLayout hoffKinLayout rPKinLayout
        qft8Stg3ValidP_layout).1 (QRegister.singleton w)
    (QRegister.disjoint_iff.mpr fun i k e ↦ by
      have hv : w.val = (rPKinLayout k).val :=
          congrArg Fin.val ((QRegister.singleton_apply w i).symm.trans e)
      rw [val_rPKinLayout] at hv
      exact hw2 ⟨by omega, by omega⟩)
    (QRegister.disjoint_iff.mpr fun i c e ↦ by
      have hv :=
          (congrArg Fin.val ((QRegister.singleton_apply w i).symm.trans e)).trans
          (val_locCat8_layout c)
      exact hw1 ⟨by omega, by omega⟩) 0).symm hpq.symm).symm
  have cQi := ic Qcat hQpw hpq cQ
  have p1 := mp (Qcat⁻¹).1 uKinMid2m1UselLayout.1 cQi.1
    (IsPhaseDiag.comm_basisOutcomeProjector_zero uKinMid2m1_isPhaseDiag_layout rWorkInnerLayout)
        cQi.2 (comm_mul P uKinMid2m1UselLayout.1
      PW (IsPhaseDiag.comm_basisOutcomeProjector_zero uKinMid2m1_isPhaseDiag_layout
          (QRegister.singleton w)).symm hpq.symm).symm
  have p2 := mp _ Qcat.1 p1.1 hQpw p1.2 cQ
  have p3 := mp (uMux27Layout⁻¹).1 _ cMi.1 p2.1 cMi.2 p2.2
  exact mp _ uMux27Layout.1 p3.1 uMux27Layout_comm_rWorkInner p3.2 cM
theorem uKinCat2m1_98Usel_mul_pw_comm_bit0 {w : Wire dLayout} (hw : NotKinTarget w) :
    uKinCat2m1_98UselLayout.1 * rWorkInnerLayout.basisOutcomeProjector 0 =
    rWorkInnerLayout.basisOutcomeProjector 0 * uKinCat2m1_98UselLayout.1 ∧
    (uKinCat2m1_98UselLayout.1 * rWorkInnerLayout.basisOutcomeProjector 0) * pBit0 w =
    pBit0 w * (uKinCat2m1_98UselLayout.1 * rWorkInnerLayout.basisOutcomeProjector 0) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  have hd : dLayout = 7298 := hDLayout_w0
  let PW := rWorkInnerLayout.basisOutcomeProjector 0
  let P := pBit0 w
  let S := uSpeciesSwap50Layout
  have hpq : PW * P = P * PW :=
      rWorkInnerLayout.embedMatrix_comm_of_disjoint (QRegister.singleton w)
    (QRegister.disjoint_iff.mpr fun k i e ↦ by
      have hv := congrArg Fin.val (e.trans (QRegister.singleton_apply w i))
      rw [val_rWorkInnerLayout] at hv
      exact hw.2.2.2 ⟨by omega,
          by omega⟩) (compProj 0) (compProj 0)
  have cS := ketPerm_on_pw_comm_bit0 S.1 speciesSwapBits
    (fun δ h0 ↦ uSpeciesSwap50Layout_mulVec_ket δ (h0 ⟨21, by omega⟩)) w hpq fun δ _ ↦
        speciesSwapBits_outside δ (by omega) (by omega)
  have cSi := inv_comm_proj S.1 (S⁻¹).1 PW P (congrArg Subtype.val (inv_mul_cancel S))
    (congrArg Subtype.val (mul_inv_cancel S)) uSpeciesSwap50Layout_comm_rWorkInner hpq cS
  have p4 := uKinCoreCat2m1_98Usel_pw_comm (fun h ↦ hw.1 ⟨by omega, h.2⟩) hw.2.1 hw.2.2.2
  have p5 := mul_proj_comm (S⁻¹).1 _ PW P pw_mul_self cSi.1 p4.1 cSi.2 p4.2
  exact mul_proj_comm _ S.1 PW P pw_mul_self p5.1 uSpeciesSwap50Layout_comm_rWorkInner
      p5.2 cS
theorem uKinCat2m1_98_mul_pw_comm_reg {L : ℕ} (r : QRegister L dLayout)
    (hr : ∀ i : Fin L, NotKinTarget (r i)) : (uKinCat2m1_98UselLayout.1 *
    rWorkInnerLayout.basisOutcomeProjector 0) * r.basisOutcomeProjector 0 =
    r.basisOutcomeProjector 0 * (uKinCat2m1_98UselLayout.1 *
    rWorkInnerLayout.basisOutcomeProjector 0) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  induction L with
  | zero =>
      rw [show r.basisOutcomeProjector 0 = 1 from KinB.matrix_ext_ket fun _ ↦
        by rw [SelectRefl.ket_basisOutcomeProjector_zero, ifPosSqf (fun i ↦ Fin.elim0 i),
             Matrix.one_mulVec], mul_one, one_mul]
  | succ m ih =>
      let rH : QRegister 1 dLayout := QRegister.singleton (r 0)
      let rT : QRegister m dLayout :=
          ⟨⟨fun j ↦ r j.succ, fun _ _ h ↦ Fin.succ_inj.mp (r.wires.injective h)⟩⟩
      let kz {k} (q : QRegister k dLayout) := SelectRefl.ket_basisOutcomeProjector_zero q
      rw [show r.basisOutcomeProjector 0 = rH.basisOutcomeProjector 0 *
          rT.basisOutcomeProjector 0 from
        KinB.matrix_ext_ket fun δ ↦ by
          rw [kz, ← Matrix.mulVec_mulVec, kz]
          if ht : ∀ j : Fin m, δ (rT j) = 0 then
            rw [ifPosSqf ht, kz]
            exact (em (∀ j : Fin 1, δ (rH j) = 0)).elim (fun hh ↦
                by rw [ifPosSqf hh, ifPosSqf (fun i ↦ Fin.cases (hh 0) ht i)])
              fun hh ↦ by rw [ifNegSqf hh, ifNegSqf (fun a ↦ hh fun _ ↦ a 0)]
          else rw [ifNegSqf ht, ifNegSqf (fun a ↦ ht fun j ↦ a j.succ), Matrix.mulVec_zero]]
      exact comm_mul _ _ _ (uKinCat2m1_98Usel_mul_pw_comm_bit0 (hr 0)).2 (ih rT fun j ↦
          hr j.succ)
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
  QuantumComputation.Specs.PhotochemistrySolution.SelectQromKetBridge
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
  QuantumComputation.Specs.PhotochemistrySolution.SelectQft8GidneyStg3
  QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.Kinetic664
  QuantumComputation.Specs.PhotochemistrySolution.Qft8PostCancelT5
  QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull (wMux bAxisMux27
    bAxisMux27_props bAxisMux27_evalS mux1Bit6)
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open DynamicCircuit PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.FastQft8
  PhotochemistrySolution.ProviderCoreFused
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel
    Stage4Kin14Scb.abpKin14Csel Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel
    Kinetic664.abpKin15SqFree2m1Csel Qft8PostCancelT5.qft8PostCancel98CatU
    Qft8PostCancelT5.polyPostCancelT5Qft8Bracket98 Stage4KinFull.bAxisMux27 bSpeciesSwap50
theorem cpWires_mapCPReg {K n : ℕ} {P : Wire K → Prop} {S : Wire n → Prop} (r : QRegister K n)
    (hr : ∀ w, P w → S (r w)) {p : ComputeProg K} (h : ComputeProgWires P p) :
    ComputeProgWires S (mapCPReg r p) := by
  induction p with
  | id => trivial
  | x u => exact hr u h
  | cnot c tgt _ => exact ⟨hr c h.1, hr tgt h.2⟩
  | andGate c₁ c₂ a _ _ _ => exact ⟨hr c₁ h.1, hr c₂ h.2.1, hr a h.2.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
set_option maxHeartbeats 1600000 in
-- Commuting the aligned kinetic unitary with the 690-wire clean projector unfolds layout terms.
theorem uAlignedKin2m1_98_comm_rClean690 (isCsel : Bool) :
    (if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout).1 *
    rClean690Layout.basisOutcomeProjector 0 = rClean690Layout.basisOutcomeProjector 0 *
    (if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout).1 := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩;
  have hd : dLayout = 7298 := hDLayout_w0
  let A : Operator (2 ^ dLayout) := uKinAlign0Layout.1;
  let P4 : Operator (2 ^ dLayout) := rKin4.basisOutcomeProjector 0;
  let P165 : Operator (2 ^ dLayout) := rPre165Align.basisOutcomeProjector 0;
  let PW : Operator (2 ^ dLayout) := rWorkInnerLayout.basisOutcomeProjector 0;
  let EQ : Operator (2 ^ dLayout) :=
      eqWireProj wAxis0 wKinAxis0 * (eqWireProj wAxis1 wKinAxis1 * (eqWireProj wIsFine wIsFineCopy *
      eqWireProj wHasE1 wIsElecKin)); have hAA : A * A = 1 :=
                                        congrArg Subtype.val uKinAlign0Layout_sq_one
  have hConjP4 : A * P4 * A = EQ := by
    refine KinB.matrix_ext_ket fun δ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec];
    have hAd : A.mulVec (KinB.ket δ) = KinB.ket (pKinAlign0.fwdBits δ) :=
        fwdCirc_mulVec_ket pKinAlign0 δ
    have hAdd : A.mulVec (KinB.ket (pKinAlign0.fwdBits δ)) = KinB.ket δ := by
      rw [← hAd, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
    obtain ⟨t0, t1, t2, t3⟩ := fwdBits_pKinAlign0_targets δ
    have ziff : ∀ x y : ZMod 2, y + x = 0 ↔ x = y := by decide +kernel
    have eqv4 : (∀ j : Fin 4, (pKinAlign0.fwdBits δ) (rKin4 j) = 0) ↔
        (δ wAxis0 = δ wKinAxis0 ∧ δ wAxis1 = δ wKinAxis1 ∧
         δ wIsFine = δ wIsFineCopy ∧ δ wHasE1 = δ wIsElecKin) :=
      ⟨fun h ↦ ⟨(ziff _ _).mp (t0 ▸ h 0), (ziff _ _).mp (t1 ▸ h 1),
        (ziff _ _).mp (t2 ▸ h 2), (ziff _ _).mp (t3 ▸ h 3)⟩, fun ⟨e0, e1, e2, e3⟩ j ↦ by
        fin_cases j
        exacts [t0.trans ((ziff _ _).mpr e0), t1.trans ((ziff _ _).mpr e1),
          t2.trans ((ziff _ _).mpr e2), t3.trans ((ziff _ _).mpr e3)]⟩
    rw [hAd, SelectRefl.ket_basisOutcomeProjector_zero]
    dsimp only [EQ]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, eqWireProj_ket]
    by_cases e3 : δ wHasE1 = δ wIsElecKin
    · rw [ifPosSqf e3, eqWireProj_ket]
      by_cases e2 : δ wIsFine = δ wIsFineCopy
      · rw [ifPosSqf e2, eqWireProj_ket]
        by_cases e1 : δ wAxis1 = δ wKinAxis1
        · rw [ifPosSqf e1, eqWireProj_ket]
          by_cases e0 : δ wAxis0 = δ wKinAxis0
          · rw [ifPosSqf e0, ifPosSqf (eqv4.mpr ⟨e0, e1, e2, e3⟩), hAdd]
          · rw [ifNegSqf e0, ifNegSqf (fun ha ↦ e0 (eqv4.mp ha).1), Matrix.mulVec_zero]
        · simp only [ifNegSqf e1, ifNegSqf (fun ha ↦ e1 (eqv4.mp ha).2.1), Matrix.mulVec_zero]
      · simp only [ifNegSqf e2, ifNegSqf (fun ha ↦ e2 (eqv4.mp ha).2.2.1), Matrix.mulVec_zero]
    · simp only [ifNegSqf e3, ifNegSqf (fun ha ↦ e3 (eqv4.mp ha).2.2.2), Matrix.mulVec_zero]
  have cEq2 (u v : Wire dLayout) (hu : u.val = 5753 ∨ u.val = 5754 ∨ u.val = 5748 ∨ u.val = 5729)
      (hv : v.val = 6056 ∨ v.val = 6057 ∨ v.val = 6082 ∨ v.val = 6058) :
      Commute (uKinCat2m1_98UselLayout.1 * PW) (eqWireProj u v) :=
    comm_eqWireProj
      (uKinCat2m1_98Usel_mul_pw_comm_bit0 ⟨by omega, by omega, by omega, by omega⟩).2
      (uKinCat2m1_98Usel_mul_pw_comm_bit0 ⟨by omega, by omega, by omega, by omega⟩).2
  have cEQ : (uKinCat2m1_98UselLayout.1 * PW) * EQ = EQ * (uKinCat2m1_98UselLayout.1 * PW) :=
    ((cEq2 wAxis0 wKinAxis0 (by simp [wAxis0, val_rOut40Layout])
        (by simp [wKinAxis0, val_rAlignLayout])).mul_right
      ((cEq2 wAxis1 wKinAxis1 (by simp [wAxis1, val_rOut40Layout])
          (by simp [wKinAxis1, val_rAlignLayout])).mul_right
        ((cEq2 wIsFine wIsFineCopy (by simp [wIsFine, val_rOut40Layout])
            (by simp [wIsFineCopy, val_rAlignLayout])).mul_right
          (cEq2 wHasE1 wIsElecKin (by simp [wHasE1, val_rOut40Layout])
            (by simp [wIsElecKin, val_rAlignLayout]))))).eq
  have cP165 : (uKinCat2m1_98UselLayout.1 * PW) * P165 = P165 * (uKinCat2m1_98UselLayout.1 * PW) :=
    uKinCat2m1_98_mul_pw_comm_reg rPre165Align fun i ↦ by
      have := val_pre165_bounds i
      exact ⟨by omega, by omega, by omega, by omega⟩
  have cKPW : uKinCat2m1_98UselLayout.1 * PW = PW * uKinCat2m1_98UselLayout.1 :=
    (uKinCat2m1_98Usel_mul_pw_comm_bit0 (w := rPre165Align ⟨0, by decide⟩) (by
      have := val_pre165_bounds ⟨0, by decide⟩
      exact ⟨by omega, by omega, by omega, by omega⟩)).1
  have cAP165 : A * P165 = P165 * A :=
    (fwdCirc_comm_embedMatrix_of_disj rPre165Align (cpWires_pKinAlign0_tight
      (fun k _ i e ↦ by
        have hv := congrArg Fin.val e; rw [val_rAlignLayout] at hv
        have := val_pre165_bounds i; omega)
      (fun j i e ↦ by
        have hv := congrArg Fin.val e; rw [val_rOut40Layout] at hv
        have := val_pre165_bounds i; omega)) (compProj 0)).eq
  have cAPW : A * PW = PW * A :=
    (fwdCirc_comm_embedMatrix_of_disj rWorkInnerLayout (cpWires_pKinAlign0
      (fun k i e ↦ by
        have hv := congrArg Fin.val e; rw [val_rAlignLayout, val_rWorkInnerLayout] at hv; omega)
      (fun j i e ↦ by
        have hv := congrArg Fin.val e; rw [val_rOut40Layout, val_rWorkInnerLayout] at hv; omega))
      (compProj 0)).eq
  have cP4PW : P4 * PW = PW * P4 :=
    rKin4.embedMatrix_comm_of_disjoint rWorkInnerLayout (QRegister.disjoint_iff.mpr fun j k
      e ↦ by
      fin_cases j <;> (
        have hv := congrArg Fin.val e; dsimp only at hv; rw [rKin4_apply] at hv; dsimp at hv
        rw [val_rAlignLayout, val_rWorkInnerLayout] at hv; dsimp only at hv; omega))
      (compProj 0) (compProj 0)
  have cP165PW : P165 * PW = PW * P165 :=
    rPre165Align.embedMatrix_comm_of_disjoint rWorkInnerLayout
      (QRegister.disjoint_iff.mpr fun i k e ↦ by
        have hv := congrArg Fin.val e; rw [val_rWorkInnerLayout] at hv
        have := val_pre165_bounds i; omega) (compProj 0) (compProj 0)
  have cMPW : (EQ * P165) * PW = PW * (EQ * P165) :=
    (comm_mul PW EQ P165 (hConjP4 ▸ conj_comm_sel A P4 A PW cAPW cP4PW cAPW).symm
      cP165PW.symm).symm
  have cKM := comm_mul (uKinCat2m1_98UselLayout.1 * PW) EQ P165 cEQ cP165
  have hCommU : uAlignedKinCat2m1_98UselLayout.1 * rClean690Layout.basisOutcomeProjector 0 =
      rClean690Layout.basisOutcomeProjector 0 *
      uAlignedKinCat2m1_98UselLayout.1
      := by rw [rClean690Layout_proj_split_sqf]; unfold uAlignedKinCat2m1_98UselLayout;
              rw [uKinAlign0Layout_inv_eq, Submonoid.coe_mul,
              Submonoid.coe_mul]; exact conj_invol_comm_mul A uKinCat2m1_98UselLayout.1 P4
              P165 PW EQ hAA hConjP4 cAP165 cAPW cMPW cKM cKPW
  cases isCsel
  · exact hCommU
  · simp only [↓reduceIte]
    exact comm_csel_of_props_layout
      ((csel_conj_unitary (projOneQCompactGen scrWLayout) uKinAlign0Layout
        uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
        (fwdCirc_comm_embedMatrix_of_disj (QRegister.singleton wLocQLayout) (cpWires_pKinAlign0
          (fun k _ e ↦ by
            change rAlignLayout.wires k = wLocQLayout at e; have hv := congrArg Fin.val e
            rw [val_rAlignLayout, val_wLocQLayout] at hv; omega)
          (fun j _ e ↦ by
            change rOut40Layout.wires j = wLocQLayout at e; have hv := congrArg Fin.val e
            rw [val_rOut40Layout, val_wLocQLayout] at hv; omega)) (compProj 1)).eq
        uKin2m1_98Layout_props.1 uKin2m1_98Layout_props.2.1).1)
      ((QRegister.singleton wLocQLayout).embedMatrix_comm_of_disjoint rClean690Layout
        (QRegister.disjoint_iff.mpr fun _ i e ↦ by
          change wLocQLayout = rClean690Layout.wires i at e; have hv := congrArg Fin.val e
          rw [val_wLocQLayout, val_rClean690Layout] at hv; split_ifs at hv <;> omega)
        (compProj 1) (compProj 0)) hCommU
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6Step
open PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.Stage2Xor84 PhotochemistrySolution.Stage2PotUnld
  PhotochemistrySolution.Stage2ElecFirst
open PhotochemistrySolution.ProviderZeroFloor PhotochemistrySolution.KinBellMux6
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb (wKin)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel
    Stage4Kin14Scb.abpKin14Csel Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel
    Kinetic664.abpKin15SqFree2m1Csel Qft8PostCancelT5.qft8PostCancel98CatU
    Qft8PostCancelT5.polyPostCancelT5Qft8Bracket98 Stage4KinFull.bAxisMux27 bSpeciesSwap50
    rPre165Align rClean690Layout rWorkInnerLayout rAlignLayout
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem mapCPReg_fwdBits_eq_writeReg {K d : ℕ} (r : QRegister K d) :
    ∀ (p : ComputeProg K) (δ : BitAssignment d),
      (mapCPReg r p).fwdBits δ =
        DynCircExt.writeReg δ r (p.fwdBits (fun i ↦ δ (r i)))
  | .id, δ => by
      dsimp only [mapCPReg, ComputeProg.fwdBits]; ext u
      by_cases hu : u ∈ Set.range r.wires
      · rcases hu with ⟨j, rfl⟩
        exact (DynCircExt.writeReg_apply_reg δ r (fun i ↦ δ (r i)) j).symm
      · exact (DynCircExt.writeReg_apply_of_not_mem δ r (fun i ↦ δ (r i)) u hu).symm
  | .x i, δ => by
      dsimp only [mapCPReg, ComputeProg.fwdBits]
      have h0 : δ = DynCircExt.writeReg δ r (fun j ↦ δ (r j)) :=
          mapCPReg_fwdBits_eq_writeReg r .id δ
      conv_lhs => rw [h0]
      rw [DynCircExt.writeReg_apply_reg, writeReg_update_kbm]
  | .cnot u₁ u₂ h12, δ => by
      dsimp only [mapCPReg, ComputeProg.fwdBits]
      have h0 : δ = DynCircExt.writeReg δ r (fun j ↦ δ (r j)) :=
          mapCPReg_fwdBits_eq_writeReg r .id δ
      conv_lhs => rw [h0]
      rw [DynCircExt.writeReg_apply_reg, DynCircExt.writeReg_apply_reg, writeReg_update_kbm]
  | .andGate c₁ c₂ a h12 h1a h2a, δ => by
      dsimp only [mapCPReg, ComputeProg.fwdBits]
      have h0 : δ = DynCircExt.writeReg δ r (fun j ↦ δ (r j)) :=
          mapCPReg_fwdBits_eq_writeReg r .id δ
      conv_lhs => rw [h0]
      rw [DynCircExt.writeReg_apply_reg, DynCircExt.writeReg_apply_reg,
          DynCircExt.writeReg_apply_reg, writeReg_update_kbm]
  | .seq p₁ p₂, δ => by
      dsimp only [mapCPReg, ComputeProg.fwdBits];
      rw [mapCPReg_fwdBits_eq_writeReg r p₁ δ, mapCPReg_fwdBits_eq_writeReg r p₂, writeReg_idem_kbm]
      congr 1; congr 1; funext j; exact DynCircExt.writeReg_apply_reg δ r _ j
/-- Local `2 ^ dLayout` unitary for `pKinOneHot6Local` mapped onto `rOneHot10Layout`. -/
def uOneHot6Layout : Unitary (2 ^ dLayout) :=
    rOneHot10Layout.embedUnitary (fwdCirc pKinOneHot6Local).eval
def oneHot6Bits (δ : BitAssignment dLayout) : BitAssignment dLayout :=
    DynCircExt.writeReg δ rOneHot10Layout (pKinOneHot6Local.fwdBits (fun i ↦
    δ (rOneHot10Layout i)))
theorem uOneHot6Layout_mulVec_ket (δ : BitAssignment dLayout) :
    uOneHot6Layout.1.mulVec (DynCircExt.ket δ) = DynCircExt.ket (oneHot6Bits δ) := by
  have hev : uOneHot6Layout = (fwdCirc (mapCPReg rOneHot10Layout pKinOneHot6Local)).eval := by
    dsimp only [uOneHot6Layout];
    rw [SubspaceMbu.fwdCirc_mapCPReg_eq_onRegister, Circuit.eval_onRegister]
  rw [hev, ket_dc_eq_sb, fwdCirc_mulVec_ket, mapCPReg_fwdBits_eq_writeReg]; rfl
theorem oneHot6Bits_props {δ : BitAssignment dLayout}
    (hAy : δ wAyKin = 0) (hCtrl : ∀ p : Fin 6, δ (bmCtrl rBellMux71Layout p) = 0) :
    let p₀ := activePort6 (δ wIsElecKin) (δ wKinAxis0) (δ wKinAxis1)
    oneHot6Bits δ (bmCtrl rBellMux71Layout p₀) = 1 ∧
    (∀ p : Fin 6, p ≠ p₀ → oneHot6Bits δ (bmCtrl rBellMux71Layout p) = 0) ∧
    (∀ u : Wire dLayout, u ≠ wAyKin → (∀ p : Fin 6, u ≠ bmCtrl rBellMux71Layout p) →
      oneHot6Bits δ u = δ u) := by
  intro p₀
  have hIn : (fun i : Fin 10 ↦ δ (rOneHot10Layout i)) =
      mkOneHot10In (δ wIsElecKin) (δ wKinAxis0) (δ wKinAxis1) := funext fun i ↦ by
    rw [rOneHot10_apply]
    fin_cases i <;> dsimp only [oneHot10WireFn, mkOneHot10In] <;>
      first | rfl | exact hAy | exact hCtrl _
  obtain ⟨he, hsy, hsz, hp1, hp0⟩ :=
    pKinOneHot6Local_fwdBits_spec (δ wIsElecKin) (δ wKinAxis0) (δ wKinAxis1)
  refine ⟨?_, fun p hp ↦ ?_, fun u huA huC ↦ ?_⟩
  · rw [← rOneHot10_ctrl p₀]
    simpa only [oneHot6Bits, DynCircExt.writeReg_apply_reg, hIn] using hp1
  · rw [← rOneHot10_ctrl p]
    simpa only [oneHot6Bits, DynCircExt.writeReg_apply_reg, hIn] using hp0 p hp
  · dsimp only [oneHot6Bits]
    by_cases hm : u ∈ Set.range rOneHot10Layout.wires
    · rcases hm with ⟨i, rfl⟩
      rw [DynCircExt.writeReg_apply_reg, hIn]
      fin_cases i
      exacts [he, hsy, hsz, absurd rOneHot10_3 huA, absurd (rOneHot10_ctrl 0) (huC _),
        absurd (rOneHot10_ctrl 1) (huC _), absurd (rOneHot10_ctrl 2) (huC _),
        absurd (rOneHot10_ctrl 3) (huC _), absurd (rOneHot10_ctrl 4) (huC _),
        absurd (rOneHot10_ctrl 5) (huC _)]
    · exact DynCircExt.writeReg_apply_of_not_mem δ rOneHot10Layout _ u hm
/-! ## Part B: `rSwapBufPKin`, `rClean566Layout`, and `pKinCore336Raw` (`336 T`, `0 TOFF`) -/

def swapBufPKinVal (x : ℕ) : ℕ :=
    if 5755 ≤ x ∧ x ≤ 5762 then x + 230 else if 5985 ≤ x ∧ x ≤ 5992 then x - 230 else x
theorem swapBufPKinVal_invol (x : ℕ) : swapBufPKinVal (swapBufPKinVal x) = x := by
  unfold swapBufPKinVal; split_ifs <;> omega
theorem swapBufPKinVal_lt {x : ℕ} (hx : x < dLayout) : swapBufPKinVal x < dLayout := by
  rw [hDLayout_w0] at hx ⊢; unfold swapBufPKinVal; split_ifs <;> omega
def swapBufPKinFn (w : Wire dLayout) : Wire dLayout :=
    ⟨swapBufPKinVal w.val, swapBufPKinVal_lt w.isLt⟩
theorem swapBufPKinFn_invol (w : Wire dLayout) : swapBufPKinFn (swapBufPKinFn w) = w :=
  Fin.ext (swapBufPKinVal_invol w.val)
/--
Full-width register permutation swapping `rPKinLayout` (`5755..5762`) with `bmBuf` (`5985..5992`).
-/
def rSwapBufPKin : QRegister dLayout dLayout :=
    ⟨⟨swapBufPKinFn, Function.Involutive.injective swapBufPKinFn_invol⟩⟩
theorem val_rSwapBufPKin (w : Wire dLayout) : (rSwapBufPKin w).val = swapBufPKinVal w.val := rfl
theorem c566_pre {m : Fin 566} (hm : m.val < 45) : m.val < 165 := by omega
theorem c566_wk (m : Fin 566) : m.val - 45 < 521 := by omega
/--
`566`-wire clean pool (`{5680..5712, 5947..5958, 6083..6603}`) fixed by `rSwapBufPKin`
and 100% disjoint from `rOneHot10Layout` and `rBellMux71Layout`.
-/
def clean566Fn (m : Fin 566) : Wire dLayout :=
    if hm : m.val < 45 then rPre165Align ⟨m.val, c566_pre hm⟩ else rWorkInnerLayout ⟨m.val - 45,
    c566_wk m⟩
theorem val_clean566_bounds (m : Fin 566) : (5680 ≤ (clean566Fn m).val ∧ (clean566Fn m).val ≤
    5712) ∨ (5947 ≤ (clean566Fn m).val ∧ (clean566Fn m).val ≤ 5958) ∨ (6083 ≤ (clean566Fn m).val ∧
    (clean566Fn m).val ≤ 6603) := by
  have hm_lt := m.isLt; dsimp only [clean566Fn]
  by_cases hm : m.val < 45
  · rw [dite_eq_left hm, val_rPre165_w0]; dsimp; split_ifs <;> omega
  · rw [dite_eq_right hm, val_rWorkInnerLayout]; dsimp; omega
theorem clean566Fn_inj : Function.Injective clean566Fn := fun a b h ↦ by
  dsimp only [clean566Fn] at h
  by_cases ha : a.val < 45 <;> by_cases hb : b.val < 45
  · simp only [ha, hb, ↓reduceDIte] at h;
    have ev := congrArg Fin.val (rPre165Align.wires.injective h)
    dsimp at ev; exact Fin.ext ev
  · simp only [ha, hb, ↓reduceDIte] at h
    have hv := congrArg Fin.val h; rw [val_rPre165_w0, val_rWorkInnerLayout] at hv
    dsimp at hv; split_ifs at hv <;> omega
  · simp only [ha, hb, ↓reduceDIte] at h
    have hv := congrArg Fin.val h; rw [val_rPre165_w0, val_rWorkInnerLayout] at hv
    dsimp at hv; split_ifs at hv <;> omega
  · simp only [ha, hb, ↓reduceDIte] at h;
    have ev := congrArg Fin.val (rWorkInnerLayout.wires.injective h)
    dsimp at ev; exact Fin.ext (by omega)
def rClean566Layout : QRegister 566 dLayout := ⟨⟨clean566Fn, clean566Fn_inj⟩⟩
theorem rClean566_apply (m : Fin 566) : rClean566Layout m = clean566Fn m := rfl
theorem subreg_rClean566_rClean686 (m : Fin 566) : ∃ q : Fin 686, rClean566Layout m =
    rClean686Layout q := by
  by_cases hm : m.val < 45
  · refine ⟨⟨m.val, by omega⟩, ?_⟩
    rw [rClean566_apply, rClean686_eq_fn_w0]; dsimp only [clean566Fn, clean686Fn]
    rw [dite_eq_left hm, dite_eq_left (by omega)]
  · refine ⟨⟨165 + (m.val - 45), by omega⟩, ?_⟩
    rw [rClean566_apply, rClean686_eq_fn_w0]; dsimp only [clean566Fn, clean686Fn]
    rw [dite_eq_right hm, dite_eq_right (by omega)]
    exact congrArg rWorkInnerLayout (Fin.ext (by dsimp; omega))
theorem rSwapBufPKin_compose_rClean566 : rSwapBufPKin.compose rClean566Layout =
    rClean566Layout := by
  apply congrArg QRegister.mk; apply Function.Embedding.ext; intro m
  have hb :=
      val_clean566_bounds m; apply Fin.ext; change swapBufPKinVal (clean566Fn m).val =
      (clean566Fn m).val
  unfold swapBufPKinVal; split_ifs <;> omega
theorem fwdBits_congr_of_wires_kbm {N : ℕ} {P : Wire N → Prop} :
    ∀ {p : ComputeProg N}, ComputeProgWires P p →
      ∀ {γ₁ γ₂ : BitAssignment N}, (∀ w, P w → γ₁ w = γ₂ w) →
      ∀ w, P w → p.fwdBits γ₁ w = p.fwdBits γ₂ w
  | .id, _, _, _, hγ, w, hw => hγ w hw
  | .x u, hp, γ₁, γ₂, hγ, w, hw => by
      dsimp only [ComputeProg.fwdBits]
      by_cases hwu : w = u
      · subst hwu; simp only [Function.update_self, hγ w hp]
      · simp only [Function.update_of_ne hwu]; exact hγ w hw
  | .cnot u₁ u₂ _, ⟨hc, ht⟩, γ₁, γ₂, hγ, w, hw => by
      dsimp only [ComputeProg.fwdBits]
      by_cases hwt : w = u₂
      · subst hwt; simp only [Function.update_self, hγ w ht, hγ u₁ hc]
      · simp only [Function.update_of_ne hwt]; exact hγ w hw
  | .andGate c₁ c₂ a _ _ _, ⟨hc₁, hc₂, ha⟩, γ₁, γ₂, hγ, w, hw => by
      dsimp only [ComputeProg.fwdBits]
      by_cases hwa : w = a
      · subst hwa; simp only [Function.update_self, hγ w ha, hγ c₁ hc₁, hγ c₂ hc₂]
      · simp only [Function.update_of_ne hwa]; exact hγ w hw
  | .seq p₁ p₂, ⟨hp₁, hp₂⟩, _, _, hγ, w, hw =>
      fwdBits_congr_of_wires_kbm hp₂ (fun u hu ↦ fwdBits_congr_of_wires_kbm hp₁ hγ u hu) w hw
/-- Inner `Q98⁻¹ * Mid_2m1 * Q98` unitary on `dLayout` (`rPKinLayout`). -/
def uQft98Mid2m1Layout (isCsel : Bool) : Unitary (2 ^ dLayout) :=
  (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout)⁻¹ *
    (if isCsel then uKinMid2m1CselLayout else uKinMid2m1UselLayout) *
    (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
        qft8Stg3ValidP_layout)
theorem kin2m1RawBit_congr_lt70 {γ₁ γ₂ : BitAssignment 226} (h : ∀ w : Wire 226, w.val < 70 → γ₁ w =
    γ₂ w)
    : kin2m1RawBit γ₁ = kin2m1RawBit γ₂ :=
  fwdBits_congr_of_wires_kbm (computeProgWires_of_lt70 (by decide +kernel)) h (wKin 68)
      (by decide +kernel)
/--
Tight wire footprint of `pKinCore252AsymRaw v (rT.compose rSwapBufPKin) isCsel` in `rT` coords
(`5647..5649` 100% excluded!).
-/
def IsCore252Wire (w : Wire dLayout) : Prop :=
    (5642 ≤ w.val ∧ w.val ≤ 5646) ∨ (5680 ≤ w.val ∧ w.val ≤ 5712) ∨ w.val = 5749 ∨ (5947 ≤ w.val ∧
    w.val ≤ 5958) ∨ (5985 ≤ w.val ∧ w.val ≤ 5992) ∨ (6083 ≤ w.val ∧ w.val ≤ 6095) ∨ w.val = 6105 ∨
    (7256 ≤ w.val ∧ w.val ≤ 7269) ∨ w.val = 7297
def InEmbedRange {b d : ℕ} (r0 : QRegister b d) (A : Operator (2 ^ d)) : Prop :=
    ∃ M : Operator (2 ^ b), A = r0.embedMatrix M
theorem InEmbedRange.one {b d : ℕ} (r0 : QRegister b d) : InEmbedRange r0 1 :=
    ⟨1, r0.embedMatrix_one.symm⟩
theorem InEmbedRange.add {b d : ℕ} {r0 : QRegister b d} {A B : Operator (2 ^ d)}
    (hA : InEmbedRange r0 A) (hB : InEmbedRange r0 B) : InEmbedRange r0 (A + B) := by
  rcases hA with ⟨MA, rfl⟩; rcases hB with ⟨MB, rfl⟩
  exact ⟨MA + MB, (r0.embedMatrix_add MA MB).symm⟩
theorem InEmbedRange.sub {b d : ℕ} {r0 : QRegister b d} {A B : Operator (2 ^ d)}
    (hA : InEmbedRange r0 A) (hB : InEmbedRange r0 B) : InEmbedRange r0 (A - B) := by
  rcases hA with ⟨MA, rfl⟩; rcases hB with ⟨MB, rfl⟩
  refine ⟨MA - MB, ?_⟩;
  rw [sub_eq_add_neg, sub_eq_add_neg, r0.embedMatrix_add, ← neg_one_smul ℂ MB, r0.embedMatrix_smul,
      neg_one_smul]
theorem InEmbedRange.mul {b d : ℕ} {r0 : QRegister b d} {A B : Operator (2 ^ d)}
    (hA : InEmbedRange r0 A) (hB : InEmbedRange r0 B) : InEmbedRange r0 (A * B) := by
  rcases hA with ⟨MA, rfl⟩; rcases hB with ⟨MB, rfl⟩
  exact ⟨MA * MB, (r0.embedMatrix_mul MA MB).symm⟩
theorem InEmbedRange.unitary_inv {b d : ℕ} {r0 : QRegister b d} {U : Unitary (2 ^ d)}
    (hU : InEmbedRange r0 U.1) : InEmbedRange r0 (U⁻¹).1 := by
  rcases hU with ⟨MU, hEq⟩
  have hInv : (U⁻¹).1 = U.1ᴴ := by
    change (star U : Unitary (2 ^ d)).1 = U.1ᴴ; rw [Unitary.coe_star, Matrix.star_eq_conjTranspose]
  rw [hInv, hEq]; exact ⟨MUᴴ, (r0.embedMatrix_conjTranspose MU).symm⟩
theorem InEmbedRange.of_subreg {k b d : ℕ} {r0 : QRegister b d} (r1 : QRegister k d)
    (hSub : ∀ i : Fin k, ∃ j : Fin b, r1 i = r0 j) (M : Operator (2 ^ k)) :
    InEmbedRange r0 (r1.embedMatrix M) := by
  classical
  let f : Fin k → Fin b := fun i ↦ Classical.choose (hSub i)
  have hf : ∀ i, r1 i = r0 (f i) := fun i ↦ Classical.choose_spec (hSub i)
  let rSub : QRegister k b :=
      ⟨⟨f, fun x y hxy ↦
      r1.wires.injective ((hf x).trans ((congrArg r0.wires hxy).trans (hf y).symm))⟩⟩
  have hComp : r1 = r0.compose rSub :=
      congrArg QRegister.mk (Function.Embedding.ext hf); rw [hComp]; exact ⟨rSub.embedMatrix M,
      r0.embedMatrix_compose rSub M⟩
theorem circWires_toCircuit_kbm {n : ℕ} {P : Wire n → Prop} :
    ∀ {b : AndBracketProg n}, AndBracketWires P b → CircWires P b.toCircuit
  | .id, _ => trivial
  | .prim _, hc => hc
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨circWires_toCircuit_kbm h₁, circWires_toCircuit_kbm h₂⟩
  | .tempAnd _ _ _ _ _ _ _, ⟨hc₁, hc₂, ha, hb⟩ =>
      ⟨fun | ⟨0, _⟩ => hc₁ | ⟨1, _⟩ => hc₂ | ⟨2, _⟩ => ha,
       circWires_toCircuit_kbm hb,
       fun | ⟨0, _⟩ => hc₁ | ⟨1, _⟩ => hc₂ | ⟨2, _⟩ => ha⟩
theorem InEmbedRange.of_circuit {b d : ℕ} (r0 : QRegister b d) :
    ∀ {c : Circuit d}, CircWires (fun w ↦ ∃ j : Fin b, w = r0 j) c →
      InEmbedRange r0 c.eval.1
  | .identity, _ => by rw [Circuit.eval_identity, Submonoid.coe_one]; exact InEmbedRange.one r0
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => by
      rw [Circuit.eval_seq, Submonoid.coe_mul];
      exact (InEmbedRange.of_circuit r0 h₂).mul (InEmbedRange.of_circuit r0 h₁)
  | .gate g reg, hg => InEmbedRange.of_subreg reg hg g.eval.1
/--
`239` non-momentum wires of the mid-stage QFT circuit:
- `0..7`: `locCat8SharedCompactGen scrWLayout` (`5642..5649`)
- `8..20`: `qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout` (`6083..6095`)
- `21..238`: `rKin226Layout ⟨8 + (j - 21), _⟩` (`{7256..7269, 5749, 7297, 6105..6306}`).
-/
def rest239WireFn (j : Fin 239) : Wire dLayout :=
  if h1 : j.val < 8 then locCat8SharedCompactGen scrWLayout ⟨j.val, h1⟩
  else if h2 : j.val < 21 then
    qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout ⟨j.val - 8, by omega⟩
  else rKin226Layout ⟨8 + (j.val - 21), by omega⟩
theorem val_rest239WireFn (j : Fin 239) : (rest239WireFn j).val = if j.val < 8 then 5642 +
    j.val else if j.val < 21 then 6083 + (j.val - 8) else if j.val < 35 then 7256 +
    (j.val - 21) else if j.val = 35 then 5749 else if j.val = 36 then 7297 else 6105 + (j.val - 37)
    := by
  have hj := j.isLt; dsimp only [rest239WireFn]
  by_cases h1 : j.val < 8
  · rw [dite_eq_left h1, val_locCat8_layout]; dsimp; split_ifs
    omega
  · rw [dite_eq_right h1]
    by_cases h2 : j.val < 21
    · rw [dite_eq_left h2, qft8Stg3Clean13_eq_workInner, val_rWorkInnerLayout]
      dsimp; split_ifs
      omega
    · rw [dite_eq_right h2, rKin226_eq_fn_w0, val_kin226WireFn]; dsimp; split_ifs <;> omega
theorem rest239WireFn_inj : Function.Injective rest239WireFn := fun a b h ↦ by
  have ha := a.isLt; have hb := b.isLt
  have hv := congrArg Fin.val h; rw [val_rest239WireFn, val_rest239WireFn] at hv
  split_ifs at hv <;> exact Fin.ext (by omega)
def rRest239 : QRegister 239 dLayout := ⟨⟨rest239WireFn, rest239WireFn_inj⟩⟩
theorem rRest239_apply (j : Fin 239) : rRest239 j = rest239WireFn j := rfl
theorem val_rRest239_bounds (j : Fin 239) : (5642 ≤ (rRest239 j).val ∧ (rRest239 j).val ≤ 5649) ∨
    (rRest239 j).val = 5749 ∨ (6083 ≤ (rRest239 j).val ∧ (rRest239 j).val ≤ 6095) ∨
    (6105 ≤ (rRest239 j).val ∧ (rRest239 j).val ≤ 6306) ∨ (7256 ≤ (rRest239 j).val ∧
    (rRest239 j).val ≤ 7269) ∨ (rRest239 j).val = 7297 := by
  have hj := j.isLt; have hv : (rRest239 j).val = _ := val_rest239WireFn j
  rw [hv]; split_ifs <;> omega
/--
`247` -wire register `rPort ++ rRest239` for any `8` -wire port `rPort` disjoint from `rRest239` .
-/
def rSQ (rPort : QRegister 8 dLayout) (hDisj : rPort.DisjointWires rRest239) :
    QRegister 247 dLayout :=
  ⟨⟨fun i ↦ if hi : i.val < 8 then rPort ⟨i.val, hi⟩ else rRest239 ⟨i.val - 8, by omega⟩,
    fun a b h ↦ by
      dsimp only at h
      by_cases ha : a.val < 8 <;> by_cases hb : b.val < 8
      · simp only [ha, hb, ↓reduceDIte] at h
        have ev := congrArg Fin.val (rPort.wires.injective h); dsimp at ev; exact Fin.ext ev
      · simp only [ha, hb, ↓reduceDIte] at h; exact absurd h (hDisj.ne _ _)
      · simp only [ha, hb, ↓reduceDIte] at h; exact absurd h.symm (hDisj.ne _ _)
      · simp only [ha, hb, ↓reduceDIte] at h;
        have ev := congrArg Fin.val (rRest239.wires.injective h)
        dsimp at ev; exact Fin.ext (by omega)⟩⟩
theorem rSQ_apply (rPort : QRegister 8 dLayout) (hDisj : rPort.DisjointWires rRest239)
    (i : Fin 247) :
    rSQ rPort hDisj i =
      if hi : i.val < 8 then rPort ⟨i.val, hi⟩ else rRest239 ⟨i.val - 8, by omega⟩ := rfl
theorem rPKin_disj_rRest239 : rPKinLayout.DisjointWires rRest239 :=
  QRegister.disjoint_iff.mpr fun k j e ↦ by
    have hk := k.isLt; have hb := val_rRest239_bounds j
    have hv := congrArg Fin.val e; rw [val_rPKinLayout] at hv; omega
theorem rBmBuf_disj_rRest239 : rBmBufLayout.DisjointWires rRest239 :=
  QRegister.disjoint_iff.mpr fun k j e ↦ by
    have hk := k.isLt; have hb := val_rRest239_bounds j
    have hv : (bmBuf rBellMux71Layout k).val = (rRest239 j).val := congrArg Fin.val e
    rw [val_bmBuf_layout] at hv; omega
theorem rPort6_disj_rRest239 (p : Fin 6) : (rPort6Layout p).DisjointWires rRest239 :=
  QRegister.disjoint_iff.mpr fun k j e ↦ by
    have hk := k.isLt; have hp := p.isLt; have hb := val_rRest239_bounds j
    have hv : (bmTgt rBellMux71Layout k p).val = (rRest239 j).val := congrArg Fin.val e
    rw [val_bmTgt_layout] at hv; split_ifs at hv <;> omega
theorem rSwapBufPKin_compose_rSQ_rPKin :
    rSwapBufPKin.compose (rSQ rPKinLayout rPKin_disj_rRest239) =
    rSQ rBmBufLayout rBmBuf_disj_rRest239 := by
  apply congrArg QRegister.mk; apply Function.Embedding.ext; intro i
  change rSwapBufPKin (rSQ rPKinLayout rPKin_disj_rRest239 i) =
      rSQ rBmBufLayout rBmBuf_disj_rRest239 i; rw [rSQ_apply, rSQ_apply]
  by_cases hi : i.val < 8
  · rw [dite_eq_left hi, dite_eq_left hi, rBmBuf_apply]; apply Fin.ext
    rw [val_rSwapBufPKin, val_rPKinLayout, val_bmBuf_layout]; unfold swapBufPKinVal
    split_ifs <;> omega
  · rw [dite_eq_right hi, dite_eq_right hi]; have hb := val_rRest239_bounds ⟨i.val - 8, by omega⟩
    apply Fin.ext; change swapBufPKinVal (rRest239 ⟨i.val - 8, _⟩).val = _; unfold swapBufPKinVal
    split_ifs <;> omega
theorem inEmbedRange_uQft98Mid2m1Layout (isCsel : Bool) :
    InEmbedRange (rSQ rPKinLayout rPKin_disj_rRest239) (uQft98Mid2m1Layout isCsel).1 := by
  let r0 := rSQ rPKinLayout rPKin_disj_rRest239
  have hSubP (k : Fin 8) : ∃ i : Fin 247, rPKinLayout k = r0 i :=
    ⟨⟨k.val, by omega⟩, by simp only [r0, rSQ_apply, dite_eq_left k.isLt]⟩
  have hSubCat (c : Fin 8) : ∃ i : Fin 247, locCat8SharedCompactGen scrWLayout c = r0 i :=
    ⟨⟨8 + c.val, by omega⟩, by
      dsimp only [r0]; rw [rSQ_apply, dite_eq_right (by dsimp; omega), rRest239_apply]
      dsimp only [rest239WireFn]; rw [dite_eq_left (by omega)]
      exact congrArg (locCat8SharedCompactGen scrWLayout) (Fin.ext (by dsimp; omega))⟩
  have hSubCln (l : Fin 13) : ∃ i : Fin 247,
      qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout l = r0 i :=
    ⟨⟨16 + l.val, by omega⟩, by
      dsimp only [r0]; rw [rSQ_apply, dite_eq_right (by dsimp; omega), rRest239_apply]
      dsimp only [rest239WireFn]; rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      exact congrArg (qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout)
        (Fin.ext (by dsimp; omega))⟩
  have hSubKin (j : Fin 226) : ∃ i : Fin 247, rKin226Layout j = r0 i := by
    by_cases hj : j.val < 8
    · refine ⟨⟨j.val, by omega⟩, ?_⟩
      dsimp only [r0]; rw [rSQ_apply, dite_eq_left hj, rKin226_eq_fn_w0]; dsimp only [kin226WireFn]
      rw [dite_eq_left hj]
    · refine ⟨⟨29 + (j.val - 8), by omega⟩, ?_⟩
      dsimp only [r0]; rw [rSQ_apply, dite_eq_right (by dsimp; omega), rRest239_apply]
      dsimp only [rest239WireFn]; rw [dite_eq_right (by omega), dite_eq_right (by omega)]
      exact congrArg rKin226Layout (Fin.ext (by dsimp; omega))
  have hQcat :
      InEmbedRange r0 (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout).1 := by
    have abBr := andBracketWires_polyPostCancelT5Qft8Bracket98 (P := fun w ↦ ∃ i : Fin 247,
      w = r0 i)
      (locCat8SharedCompactGen scrWLayout) rPKinLayout
      (qft8Stg3Delta7 scrWLayout offKinLayout hoffKinLayout)
      (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout) (qft8Stg3_rP_disj_cat8
        qft8Stg3ValidP_layout)
      (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
      (qft8Stg3_delta7_disj_cat8 hoffKinLayout) (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
      (qft8Stg3_cat8_disj_carry6 hoffKinLayout) (qft8Stg3_rP_disj_carry6 hoffKinLayout
        qft8Stg3ValidP_layout)
      (fun c ↦ hSubCat ⟨c.val, by omega⟩) hSubP
      (fun i ↦ (qft8Stg3_clean13_sub_delta7 hoffKinLayout ⟨i.val, by omega⟩) ▸ hSubCln ⟨i.val,
        by omega⟩)
      (fun i ↦ (qft8Stg3_clean13_sub_carry6 hoffKinLayout ⟨i.val, by omega⟩) ▸ hSubCln ⟨7 + i.val,
        by omega⟩)
    have hBr := InEmbedRange.of_circuit r0 (circWires_toCircuit_kbm abBr);
    have hP13 :=
        InEmbedRange.of_subreg (qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout) hSubCln
        (compProj 0); have hEff :=
                        InEmbedRange.of_subreg rPKinLayout hSubP (dPost8U *
                        qftGridUnitary).1; unfold qft8PostCancel98CatU polyPostCancelCleanUnitary
                        spliceUnitary; change InEmbedRange r0 (spliceUnitaryMat _ _ _); unfold
                        spliceUnitaryMat; exact (hBr.mul hP13).add
                        (hEff.mul ((InEmbedRange.one r0).sub hP13))
  have hMid :
      InEmbedRange r0 (if isCsel then uKinMid2m1CselLayout else uKinMid2m1UselLayout).1 := by
    cases isCsel <;> exact InEmbedRange.of_subreg rKin226Layout hSubKin _
  dsimp only [uQft98Mid2m1Layout]; rw [Submonoid.coe_mul, Submonoid.coe_mul];
  exact ((InEmbedRange.unitary_inv hQcat).mul hMid).mul hQcat
/--
Generic `247`-wire permutation-conjugation lemma via `embedMatrix_mulVec_ket_sym`:
no inverse formula needed (handles order-3 `(sy, sz) = (1, 1)` axis cycle uniformly!).
-/
theorem conj_rSQ_embedMatrix_mulVec_ket (rSrc : QRegister 8 dLayout)
    (hSrc : rSrc.DisjointWires rRest239) (rPort : QRegister 8 dLayout)
    (hPort : rPort.DisjointWires rRest239) (M : Operator (2 ^ 247)) (V : Unitary (2 ^ dLayout))
    (F : BitAssignment dLayout → BitAssignment dLayout) (Inv : BitAssignment dLayout → Prop)
    (hInvWrite : ∀ η z, Inv η → Inv (DynCircExt.writeReg η (rSQ rPort hPort) z))
    (hV : ∀ η, Inv η → V.1.mulVec (DynCircExt.ket η) = DynCircExt.ket (F η))
    (hReadPort : ∀ η, Inv η → ∀ k : Fin 8, F η (rSrc k) = η (rPort k))
    (hReadRest : ∀ η, Inv η → ∀ j : Fin 239, F η (rRest239 j) = η (rRest239 j))
    (hWrite : ∀ η z, Inv η → DynCircExt.writeReg (F η)
    (rSQ rSrc hSrc) z = F (DynCircExt.writeReg η (rSQ rPort hPort) z))
    {δ : BitAssignment dLayout} (hInv : Inv δ) : (((V⁻¹).1 * (rSQ rSrc hSrc).embedMatrix M *
    V.1).mulVec (DynCircExt.ket δ)) =
    ((rSQ rPort hPort).embedMatrix M).mulVec (DynCircExt.ket δ) := by
  have hReadIdx : readRegIdx (rSQ rSrc hSrc) (F δ) = readRegIdx (rSQ rPort hPort) δ := by
    refine readRegIdx_eq_of_bits (rSQ rSrc hSrc) (F δ) (readRegIdx (rSQ rPort hPort) δ) fun i ↦ ?_
    rw [basisBits_readRegIdx, rSQ_apply, rSQ_apply]
    by_cases hi : i.val < 8
    · rw [dite_eq_left hi, dite_eq_left hi]; exact hReadPort δ hInv ⟨i.val, hi⟩
    · rw [dite_eq_right hi, dite_eq_right hi]; exact hReadRest δ hInv ⟨i.val - 8, by omega⟩
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hV δ hInv,
      embedMatrix_mulVec_ket_sym (rSQ rSrc hSrc) M (F δ), hReadIdx, Matrix.mulVec_sum,
      embedMatrix_mulVec_ket_sym (rSQ rPort hPort) M δ]
  refine Finset.sum_congr rfl fun z' _ ↦ ?_
  rw [Matrix.mulVec_smul, hWrite δ (basisBits 247 z') hInv,
      ← hV (DynCircExt.writeReg δ (rSQ rPort hPort) (basisBits 247 z'))
          (hInvWrite δ _ hInv),
      Matrix.mulVec_mulVec,
      show (V⁻¹).1 * V.1 = 1 from congrArg Subtype.val (inv_mul_cancel V),
      Matrix.one_mulVec]
/--
6-port permutation `π_6 e sy sz : Fin 6 → Fin 6` induced by `bAxisMux27 ∘ bSpeciesSwap50`:
port `q` after `bAxisMux27 ∘ bSpeciesSwap50` holds old port `lhsPortPerm6 e sy sz q`.
-/
def lhsPortPerm6 (e sy sz : ZMod 2) (q : Fin 6) : Fin 6 :=
  let sp : Fin 6 → Fin 6 := fun r ↦
    if e = 1 then
      if hr : r.val < 3 then ⟨r.val + 3, by omega⟩ else ⟨r.val - 3, by omega⟩
    else r
  if q.val = 0 then
    if sz = 1 then sp ⟨2, by decide⟩
    else if sy = 1 then sp ⟨1, by decide⟩
    else sp ⟨0, by decide⟩
  else if q.val = 1 then
    if sy = 1 then sp ⟨0, by decide⟩ else sp ⟨1, by decide⟩
  else if q.val = 2 then
    if sz = 1 then
      if sy = 1 then sp ⟨1, by decide⟩ else sp ⟨0, by decide⟩
    else sp ⟨2, by decide⟩
  else sp q
theorem lhsPortPerm6_zero (e sy sz : ZMod 2) :
    lhsPortPerm6 e sy sz ⟨0, by decide⟩ = activePort6 e sy sz := by
  fin_cases e <;> fin_cases sy <;> fin_cases sz <;> rfl
theorem mux1Bit6_11 : ∀ x y z : ZMod 2, mux1Bit6 1 1 x y z = (z, x, y) := by decide
theorem mux1Bit6_eq_lhsPortPerm6 (e sy sz : ZMod 2) (f : Fin 6 → ZMod 2) :
    mux1Bit6 sy sz (if e = 1 then f ⟨3, by decide⟩ else f ⟨0, by decide⟩)
      (if e = 1 then f ⟨4, by decide⟩ else f ⟨1, by decide⟩)
      (if e = 1 then f ⟨5, by decide⟩ else f ⟨2, by decide⟩) =
    (f (lhsPortPerm6 e sy sz ⟨0, by decide⟩), f (lhsPortPerm6 e sy sz ⟨1, by decide⟩),
     f (lhsPortPerm6 e sy sz ⟨2, by decide⟩)) := by
  rcases zmod2_cases sy with rfl | rfl <;> rcases zmod2_cases sz with rfl | rfl
  · rcases zmod2_cases e with rfl | rfl <;>
      exact PhotochemistrySolution.Stage4KinFull.mux1Bit6_axes.1 _ _ _
  · rcases zmod2_cases e with rfl | rfl <;>
      exact PhotochemistrySolution.Stage4KinFull.mux1Bit6_axes.2.2 _ _ _
  · rcases zmod2_cases e with rfl | rfl <;>
      exact PhotochemistrySolution.Stage4KinFull.mux1Bit6_axes.2.1 _ _ _
  · rcases zmod2_cases e with rfl | rfl <;> exact mux1Bit6_11 _ _ _
def lhsPermBits (η : BitAssignment dLayout) : BitAssignment dLayout :=
    DynCircExt.writeReg (speciesSwapBits η) rMux27Layout (bAxisMux27.evalS (fun j ↦
    speciesSwapBits η (rMux27Layout j)))
theorem lhsPermBits_apply {η : BitAssignment dLayout}
    (h6104 : η (rWorkInnerLayout ⟨21, by omega⟩) = 0) :
    (∀ (k : Fin 8) (q : Fin 6),
      lhsPermBits η (bmTgt rBellMux71Layout k q) =
        η (bmTgt rBellMux71Layout k (lhsPortPerm6 (η wIsElecKin) (η wKinAxis0) (η wKinAxis1) q))) ∧
    (∀ u : Wire dLayout, (∀ (k : Fin 8) (q : Fin 6), u ≠ bmTgt rBellMux71Layout k q) →
      lhsPermBits η u = η u) := by
  let σ := speciesSwapBits η
  have hσ6104 : σ (rMux27Layout (wMux 26)) = 0 := by
    have heq : rMux27Layout (wMux 26) = rWorkInnerLayout ⟨21, by omega⟩ := by
      apply Fin.ext; rw [rMux27_eq_fn_w0, val_mux27WireFn, val_rWorkInnerLayout];
      dsimp [wMux, finMod]
    rw [heq]; exact (speciesSwapBits_outside η (by rw [val_rWorkInnerLayout]; dsimp; omega)
      (by rw [val_rWorkInnerLayout]; dsimp; omega)).trans h6104
  obtain ⟨y0, y1, y26, ybits⟩ := bAxisMux27_evalS (fun j ↦ σ (rMux27Layout j)) hσ6104
  have hσ0 : σ (rMux27Layout (wMux 0)) = η wKinAxis0 := by
    rw [show rMux27Layout (wMux 0) = wKinAxis0 from Fin.ext (by
      simp [rMux27_eq_fn_w0, val_mux27WireFn, wKinAxis0, wMux, finMod, val_rAlignLayout])]
    exact speciesSwapBits_outside η (by simp [wKinAxis0, val_rAlignLayout])
      (by simp [wKinAxis0, val_rAlignLayout])
  have hσ1 : σ (rMux27Layout (wMux 1)) = η wKinAxis1 := by
    rw [show rMux27Layout (wMux 1) = wKinAxis1 from Fin.ext (by
      simp [rMux27_eq_fn_w0, val_mux27WireFn, wKinAxis1, wMux, finMod, val_rAlignLayout])]
    exact speciesSwapBits_outside η (by simp [wKinAxis1, val_rAlignLayout])
      (by simp [wKinAxis1, val_rAlignLayout])
  have hMuxTgt (a : Fin 3) (k : Fin 8) :
      rMux27Layout (wMux (2 + a.val * 8 + k.val)) = bmTgt rBellMux71Layout k ⟨a.val, by omega⟩ := by
    have ⟨_, _⟩ := (⟨a.isLt, k.isLt⟩ : _ ∧ _); apply Fin.ext
    rw [rMux27_eq_fn_w0, val_mux27WireFn, val_bmTgt_layout,
      show (wMux (2 + a.val * 8 + k.val)).val = 2 + a.val * 8 + k.val from Nat.mod_eq_of_lt (by
        omega)]
    dsimp only
    split_ifs <;> omega
  have hσTgt (k : Fin 8) (p : Fin 6) :
      σ (bmTgt rBellMux71Layout k p) =
        if η wIsElecKin = 1 then
          if hp : p.val < 3 then η (bmTgt rBellMux71Layout k ⟨p.val + 3, by omega⟩)
          else η (bmTgt rBellMux71Layout k ⟨p.val - 3, by omega⟩)
        else η (bmTgt rBellMux71Layout k p) := by
    have ⟨_, _⟩ := (⟨k.isLt, p.isLt⟩ : _ ∧ _)
    by_cases hp3 : p.val < 3
    · have hN : bmTgt rBellMux71Layout k p = rBufLo rNucLayout ⟨p.val * 8 + k.val, by omega⟩ :=
        Fin.ext (by rw [val_bmTgt_layout, val_rBufLo_nuc_kbm, ite_eq_left hp3])
      have hE : bmTgt rBellMux71Layout k ⟨p.val + 3, by omega⟩ =
          rBufLo rElecLayout ⟨p.val * 8 + k.val, by omega⟩ := Fin.ext (by
        rw [val_bmTgt_layout, val_rBufLo_elec_kbm]; dsimp only
        rw [ite_eq_right (by omega), Nat.add_sub_cancel])
      conv_lhs => rw [hN]
      dsimp only [σ]
      rw [speciesSwapBits_bufLo_nuc, ← hE, ← hN]
      simp only [hp3, ↓reduceDIte]
    · have hE : bmTgt rBellMux71Layout k p = rBufLo rElecLayout ⟨(p.val - 3) * 8 + k.val,
      by omega⟩ :=
        Fin.ext (by rw [val_bmTgt_layout, val_rBufLo_elec_kbm, ite_eq_right hp3])
      have hN : bmTgt rBellMux71Layout k ⟨p.val - 3, by omega⟩ =
          rBufLo rNucLayout ⟨(p.val - 3) * 8 + k.val, by omega⟩ :=
        Fin.ext (by simp [val_bmTgt_layout, val_rBufLo_nuc_kbm, show p.val - 3 < 3 by omega])
      conv_lhs => rw [hE]
      dsimp only [σ]
      rw [speciesSwapBits_bufLo_elec, ← hN, ← hE]
      simp only [hp3, ↓reduceDIte]
  refine ⟨fun k q ↦ ?_, fun u hu ↦ ?_⟩
  · have ⟨_, _⟩ := (⟨k.isLt, q.isLt⟩ : _ ∧ _)
    obtain ⟨m0, m1, m2⟩ := ybits k
    have hMT0 : rMux27Layout (wMux (2 + k.val)) = bmTgt rBellMux71Layout k ⟨0, by decide⟩ :=
      (congrArg rMux27Layout (Fin.ext (by dsimp [wMux, finMod]))).trans
        (hMuxTgt ⟨0, by decide⟩ k)
    have hMT1 : rMux27Layout (wMux (10 + k.val)) = bmTgt rBellMux71Layout k ⟨1, by decide⟩ :=
      (congrArg rMux27Layout (Fin.ext (by dsimp [wMux, finMod]))).trans
        (hMuxTgt ⟨1, by decide⟩ k)
    have hMT2 : rMux27Layout (wMux (18 + k.val)) = bmTgt rBellMux71Layout k ⟨2, by decide⟩ :=
      (congrArg rMux27Layout (Fin.ext (by dsimp [wMux, finMod]))).trans
        (hMuxTgt ⟨2, by decide⟩ k)
    have hT := mux1Bit6_eq_lhsPortPerm6 (η wIsElecKin) (η wKinAxis0) (η wKinAxis1)
      (fun p ↦ η (bmTgt rBellMux71Layout k p))
    have hs (p : Fin 6) (hp : p.val < 3) : σ (bmTgt rBellMux71Layout k p) =
        if η wIsElecKin = 1 then η (bmTgt rBellMux71Layout k ⟨p.val + 3, by omega⟩)
        else η (bmTgt rBellMux71Layout k p) := by
      rw [hσTgt k p]
      exact if_congr Iff.rfl (dite_eq_left hp) rfl
    dsimp only [lhsPermBits]
    by_cases hq3 : q.val < 3
    · have hq012 : q = ⟨0, by decide⟩ ∨ q = ⟨1, by decide⟩ ∨ q = ⟨2, by decide⟩ := by
        rcases q with ⟨_ | _ | _ | _, _⟩ <;> dsimp at hq3 <;>
          first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr rfl) | omega
      rcases hq012 with rfl | rfl | rfl
      · rw [← hMT0, DynCircExt.writeReg_apply_reg, m0]
        simp only [hσ0, hσ1, hMT0, hMT1, hMT2, hs ⟨0, by decide⟩ (by decide),
          hs ⟨1, by decide⟩ (by decide), hs ⟨2, by decide⟩ (by decide)]
        exact congrArg Prod.fst hT
      · rw [← hMT1, DynCircExt.writeReg_apply_reg, m1]
        simp only [hσ0, hMT0, hMT1, hs ⟨0, by decide⟩ (by decide), hs ⟨1, by decide⟩ (by decide)]
        exact congrArg (fun x ↦ x.2.1) hT
      · rw [← hMT2, DynCircExt.writeReg_apply_reg, m2]
        simp only [hσ0, hσ1, hMT0, hMT1, hMT2, hs ⟨0, by decide⟩ (by decide),
          hs ⟨1, by decide⟩ (by decide), hs ⟨2, by decide⟩ (by decide)]
        exact congrArg (fun x ↦ x.2.2) hT
    · have hNotMux : bmTgt rBellMux71Layout k q ∉ Set.range rMux27Layout.wires := fun ⟨j, hj⟩ ↦ by
        have hv : (mux27WireFn j).val = (bmTgt rBellMux71Layout k q).val :=
          congrArg Fin.val ((rMux27_eq_fn_w0 j).symm.trans hj)
        rw [val_mux27WireFn, val_bmTgt_layout] at hv; split_ifs at hv <;> omega
      rw [DynCircExt.writeReg_apply_of_not_mem _ rMux27Layout _ _ hNotMux]
      change σ (bmTgt rBellMux71Layout k q) = _
      rw [hσTgt k q]
      dsimp only [lhsPortPerm6]
      by_cases he : η wIsElecKin = 1 <;>
        simp [he, hq3, show q.val ≠ 0 by omega, show q.val ≠ 1 by omega, show q.val ≠ 2 by omega]
  · dsimp only [lhsPermBits]
    by_cases hm : u ∈ Set.range rMux27Layout.wires
    · rcases hm with ⟨j, rfl⟩
      rw [DynCircExt.writeReg_apply_reg]; have hj := j.isLt
      by_cases hj01 : j.val = 0 ∨ j.val = 1 ∨ j.val = 26
      · rcases hj01 with hj0 | hj1 | hj26
        · rw [show j = wMux 0 from Fin.ext hj0, y0, hσ0]; rfl
        · rw [show j = wMux 1 from Fin.ext hj1, y1, hσ1]; rfl
        · rw [show j = wMux 26 from Fin.ext hj26, y26]; exact h6104.symm
      · have hj2 : 2 ≤ j.val ∧ j.val < 26 := by omega
        let a : Fin 3 := ⟨(j.val - 2) / 8, by omega⟩
        let k : Fin 8 := ⟨(j.val - 2) % 8, by omega⟩
        have hjeq : j = wMux (2 + a.val * 8 + k.val) :=
          Fin.ext (by dsimp [wMux, finMod, a, k]; omega)
        exact absurd ((congrArg rMux27Layout hjeq).trans (hMuxTgt a k)) (hu k ⟨a.val, by omega⟩)
    · rw [DynCircExt.writeReg_apply_of_not_mem _ rMux27Layout _ u hm]
      refine speciesSwapBits_outside η (fun hN ↦ ?_) (fun hE ↦ ?_)
      · let p : Fin 6 := ⟨(u.val - 5755) / 8, by omega⟩
        let k : Fin 8 := ⟨(u.val - 5755) % 8, by omega⟩
        exact hu k p (Fin.ext (by rw [val_bmTgt_layout]; dsimp [p, k]; split_ifs <;> omega))
      · let p : Fin 6 := ⟨3 + (u.val - 5851) / 8, by omega⟩
        let k : Fin 8 := ⟨(u.val - 5851) % 8, by omega⟩
        exact hu k p (Fin.ext (by rw [val_bmTgt_layout]; dsimp [p, k]; split_ifs <;> omega))
/-- Local `2 ^ dLayout` unitary for `portSwapVecCirc` on `rBellMux71Layout`. -/
def uPortSwapLayout : Unitary (2 ^ dLayout) :=
    (portSwapVecCirc 6 8 (bmBuf rBellMux71Layout) (bmCtrl rBellMux71Layout) (bmTgt rBellMux71Layout)
    (hbc_bm rBellMux71Layout) (fun k ↦ hbt_all_bm rBellMux71Layout k k)
    (fun k p ↦ hc_disj_bm rBellMux71Layout k p p)).eval
def rhsPermBits (η : BitAssignment dLayout) : BitAssignment dLayout :=
    portSwapVecBits 8 (bmBuf rBellMux71Layout) (bmCtrl rBellMux71Layout) (bmTgt rBellMux71Layout)
    (oneHot6Bits η)
theorem uPortSwap_uOneHot6_mulVec_ket (η : BitAssignment dLayout) : (uPortSwapLayout *
    uOneHot6Layout).1.mulVec (DynCircExt.ket η) = DynCircExt.ket (rhsPermBits η)
    := by rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
            uOneHot6Layout_mulVec_ket η]; dsimp only [uPortSwapLayout,
            rhsPermBits]; exact portSwapVecCirc_mulVec_ket_bm 8 (bmBuf rBellMux71Layout)
            (bmCtrl rBellMux71Layout) (bmTgt rBellMux71Layout) _ _ _ (oneHot6Bits η)
theorem rhsPermBits_apply {η : BitAssignment dLayout}
    (hAy : η wAyKin = 0)
    (hCtrl : ∀ p : Fin 6, η (bmCtrl rBellMux71Layout p) = 0)
    (hBuf : ∀ k : Fin 8, η (bmBuf rBellMux71Layout k) = 0) :
    let p₀ := activePort6 (η wIsElecKin) (η wKinAxis0) (η wKinAxis1)
    (∀ k : Fin 8, rhsPermBits η (bmBuf rBellMux71Layout k) = η (bmTgt rBellMux71Layout k p₀)) ∧
    (∀ k : Fin 8, rhsPermBits η (bmTgt rBellMux71Layout k p₀) = 0) ∧
    (∀ u : Wire dLayout,
      (∀ k : Fin 8, u ≠ bmBuf rBellMux71Layout k) →
      (∀ k : Fin 8, u ≠ bmTgt rBellMux71Layout k p₀) →
      rhsPermBits η u = oneHot6Bits η u) := by
  intro p₀
  obtain ⟨h1, h0, hOut1⟩ := oneHot6Bits_props hAy hCtrl
  obtain ⟨hLt, _, hOutS⟩ := portSwapVecBits_unique_one_bm rBellMux71Layout 8 le_rfl (oneHot6Bits η)
    p₀ h1 h0
  dsimp only [rhsPermBits]
  exact ⟨fun k ↦ ((hLt k k.isLt).1).trans (hOut1 _
      (Fin.ne_of_val_ne (by
        have ⟨_, _⟩ := (⟨k.isLt, p₀.isLt⟩ : _ ∧ _)
        rw [val_bmTgt_layout, val_wAyKin]; split_ifs <;> omega))
      (fun p ↦ (hc_disj_bm rBellMux71Layout k p p₀).symm)),
    fun k ↦ ((hLt k k.isLt).2).trans ((hOut1 _
      (Fin.ne_of_val_ne (by rw [val_bmBuf_layout, val_wAyKin]; omega))
      (fun p ↦ hbc_bm rBellMux71Layout k p)).trans (hBuf k)),
    fun u huB huT ↦ hOutS u (fun i ↦ huB i) (fun i ↦ huT i)⟩
theorem not_mem_rSQ_of_ne {rPort : QRegister 8 dLayout} {hDisj : rPort.DisjointWires rRest239}
    {u : Wire dLayout} (hP : ∀ k : Fin 8, u ≠ rPort k) (hR : ∀ j : Fin 239, u ≠ rRest239 j) :
    u ∉ Set.range (rSQ rPort hDisj).wires := by
  rintro ⟨i, hi⟩; change rSQ rPort hDisj i = u at hi; rw [rSQ_apply] at hi
  by_cases h8 : i.val < 8
  · rw [dite_eq_left h8] at hi; exact hP ⟨i.val, h8⟩ hi.symm
  · rw [dite_eq_right h8] at hi; exact hR ⟨i.val - 8, by omega⟩ hi.symm
theorem rRest239_ne_bmTgt (j : Fin 239) (k : Fin 8) (q : Fin 6) : rRest239 j ≠
    bmTgt rBellMux71Layout k q := by
  have hb := val_rRest239_bounds j
  have hk := k.isLt; have hq := q.isLt
  intro e; have hv : (rRest239 j).val = (bmTgt rBellMux71Layout k q).val := congrArg Fin.val e
  rw [val_bmTgt_layout] at hv; split_ifs at hv <;> omega
theorem rRest239_ne_bmBuf (j : Fin 239) (k : Fin 8) : rRest239 j ≠ bmBuf rBellMux71Layout k :=
    (rBmBuf_disj_rRest239.ne k j).symm
theorem rRest239_ne_bmCtrl (j : Fin 239) (p : Fin 6) : rRest239 j ≠ bmCtrl rBellMux71Layout p := by
  have hb := val_rRest239_bounds j; have hp := p.isLt; intro e;
  have hv : (rRest239 j).val = (bmCtrl rBellMux71Layout p).val := congrArg Fin.val e
  rw [val_bmCtrl_layout] at hv; omega
theorem rRest239_ne_wAyKin (j : Fin 239) : rRest239 j ≠ wAyKin := by
  have hb := val_rRest239_bounds j; intro e;
  have hv : (rRest239 j).val = wAyKin.val := congrArg Fin.val e
  rw [val_wAyKin] at hv; omega
theorem rOneHot10_not_mem_rSQ_rPort (p : Fin 6)
    (i : Fin 10) : rOneHot10Layout i ∉ Set.range (rSQ (rPort6Layout p)
    (rPort6_disj_rRest239 p)).wires := by
  have hi := i.isLt; have hp := p.isLt
  refine not_mem_rSQ_of_ne (fun k e ↦ ?_) (fun j e ↦ ?_)
  · have hk := k.isLt;
    have hv : (oneHot10WireFn i).val = (bmTgt rBellMux71Layout k p).val := congrArg Fin.val e
    rw [val_oneHot10WireFn, val_bmTgt_layout] at hv; split_ifs at hv <;> omega
  · have hb := val_rRest239_bounds j;
    have hv : (oneHot10WireFn i).val = (rRest239 j).val := congrArg Fin.val e
    rw [val_oneHot10WireFn] at hv; split_ifs at hv <;> omega
theorem rRest239_eq_rSQ (r8 : QRegister 8 dLayout) (h8 : r8.DisjointWires rRest239)
    (j : Fin 239) : rRest239 j = rSQ r8 h8 ⟨8 +
    j.val, by omega⟩ := by
  rw [rSQ_apply, dite_eq_right (Nat.not_lt.mpr (Nat.le_add_right 8 j.val))]
  exact congrArg rRest239 (Fin.ext (Nat.add_sub_cancel_left 8 j.val).symm)

private theorem bmTgt_not_mem_rSQ_of_ne {p₀ q : Fin 6} {r8 : QRegister 8 dLayout}
    (h8 : r8.DisjointWires rRest239) (hr8 : ∀ k : Fin 8, r8 k = bmTgt rBellMux71Layout k p₀)
    (hq : q ≠ p₀) (k : Fin 8) :
    bmTgt rBellMux71Layout k q ∉ Set.range (rSQ r8 h8).wires :=
  not_mem_rSQ_of_ne
    (fun k' e ↦ by
      rw [hr8 k'] at e
      by_cases hkk : k = k'
      · subst hkk
        exact ht_port_inj_bm rBellMux71Layout k q p₀ hq e
      · exact ht_disj_bm rBellMux71Layout hkk q p₀ e)
    (fun j e ↦ (rRest239_ne_bmTgt j k q) e.symm)

private theorem clean686_pre165 {δ : BitAssignment dLayout}
    (h0 : ∀ m : Fin 686, δ (rClean686Layout m) = 0) (i : Fin 165) :
    δ (rPre165Align i) = 0 := by
  have hm := h0 ⟨i.val, by omega⟩
  rw [rClean686_eq_fn_w0] at hm
  dsimp only [clean686Fn] at hm
  rwa [dite_eq_left i.isLt] at hm
theorem bellMux456_eq_uKin2m1_98_on_rClean686 (isCsel : Bool) : uPortSwapLayout.1 *
    ((rSwapBufPKin.embedUnitary (uQft98Mid2m1Layout isCsel)).1 * (uPortSwapLayout.1 *
    (uOneHot6Layout.1 * rClean686Layout.basisOutcomeProjector 0))) = uOneHot6Layout.1 *
    ((if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout).1 *
    rClean686Layout.basisOutcomeProjector 0) := by
  obtain ⟨MatQft247, hM247⟩ := inEmbedRange_uQft98Mid2m1Layout isCsel
  have hSwapM : (rSwapBufPKin.embedUnitary (uQft98Mid2m1Layout isCsel)).1 =
      (rSQ rBmBufLayout rBmBuf_disj_rRest239).embedMatrix MatQft247
      := by rw [QRegister.embedUnitary_val, hM247, ← rSwapBufPKin.embedMatrix_compose,
              rSwapBufPKin_compose_rSQ_rPKin]
  have hKinLHS : (if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout).1 =
      ((uMux27Layout * uSpeciesSwap50Layout)⁻¹).1 *
      (rSQ rPKinLayout rPKin_disj_rRest239).embedMatrix MatQft247 * (uMux27Layout *
      uSpeciesSwap50Layout).1 := by
    rw [← hM247, _root_.mul_inv_rev]
    cases isCsel <;>
      simp only [↓reduceIte, Bool.false_eq_true, uKinCat2m1_98CselLayout, uKinCat2m1_98UselLayout,
          uKinCoreCat2m1_98CselLayout, uKinCoreCat2m1_98UselLayout, uQft98Mid2m1Layout,
          Submonoid.coe_mul, mul_assoc]
  refine KinB.matrix_ext_ket fun δ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases h0 : ∀ m : Fin 686, δ (rClean686Layout m) = 0
  · rw [ite_eq_left h0, hSwapM, hKinLHS]
    set B247 := (rSQ rBmBufLayout rBmBuf_disj_rRest239).embedMatrix MatQft247
    have h6104 : δ (rWorkInnerLayout ⟨21, by omega⟩) = 0 := by
      have hm := h0 ⟨186, by decide⟩; rw [rClean686_eq_fn_w0] at hm; dsimp only [clean686Fn] at hm
      rwa [dite_eq_right (by decide)] at hm
    have hAy0 : δ wAyKin = 0 := clean686_pre165 h0 ⟨64, by decide⟩
    have hCtrl0 (p : Fin 6) : δ (bmCtrl rBellMux71Layout p) = 0 := by
      have heq : bmCtrl rBellMux71Layout p = rPre165Align ⟨65 + p.val, by omega⟩ := by
        change bellMux71WireFn ⟨1 + p.val, _⟩ = _; dsimp only [bellMux71WireFn]
        rw [dite_eq_right (by omega), dite_eq_left (by omega)]
        exact congrArg rPre165Align (Fin.ext (by dsimp; omega))
      exact heq ▸ clean686_pre165 h0 _
    have hBuf0 (k : Fin 8) : δ (bmBuf rBellMux71Layout k) = 0 := by
      have heq : bmBuf rBellMux71Layout k = rPre165Align ⟨71 + k.val, by omega⟩ := by
        change bellMux71WireFn ⟨7 + k.val, _⟩ = _; dsimp only [bellMux71WireFn]
        rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
        exact congrArg rPre165Align (Fin.ext (by dsimp; omega))
      exact heq ▸ clean686_pre165 h0 _
    let e0 := δ wIsElecKin; let sy0 := δ wKinAxis0; let sz0 := δ wKinAxis1
    let p₀ := activePort6 e0 sy0 sz0; let rPort := rPort6Layout p₀
    let hPort := rPort6_disj_rRest239 p₀
    have hKeep10 {i : Fin 10} {w : Wire dLayout} (hw : rOneHot10Layout i = w) (η) (z) :
        DynCircExt.writeReg η (rSQ rPort hPort) z w = η w :=
      hw ▸ DynCircExt.writeReg_apply_of_not_mem η _ z _ (rOneHot10_not_mem_rSQ_rPort p₀ i)
    let InvL : BitAssignment dLayout → Prop := fun η ↦
      η (rWorkInnerLayout ⟨21, by omega⟩) = 0 ∧ η wIsElecKin = e0 ∧ η wKinAxis0 = sy0 ∧ η wKinAxis1
        = sz0
    have hInvL_write (η : BitAssignment dLayout) (z : BitAssignment 247) :
        InvL η → InvL (DynCircExt.writeReg η (rSQ rPort hPort) z) :=
      fun ⟨h21, he, hsy, hsz⟩ ↦
        ⟨(DynCircExt.writeReg_apply_of_not_mem η _ z _ (not_mem_rSQ_of_ne
          (fun k e ↦ by
            have := k.isLt; have := p₀.isLt
            have hv : (rWorkInnerLayout ⟨21, by omega⟩).val = (bmTgt rBellMux71Layout k p₀).val :=
              congrArg Fin.val e
            rw [val_rWorkInnerLayout, val_bmTgt_layout] at hv; dsimp at hv
            split_ifs at hv <;> omega)
          (fun j e ↦ by
            have hb := val_rRest239_bounds j
            have hv : (rWorkInnerLayout ⟨21, by omega⟩).val = (rRest239 j).val := congrArg Fin.val
              e
            rw [val_rWorkInnerLayout] at hv; dsimp at hv; omega))).trans h21,
         (hKeep10 rOneHot10_0 η z).trans he, (hKeep10 rOneHot10_1 η z).trans hsy,
         (hKeep10 rOneHot10_2 η z).trans hsz⟩
    have hPermInj : Function.Injective (lhsPortPerm6 e0 sy0 sz0) :=
      (fun (e sy sz : ZMod 2) ↦ (by
        intro q₁ q₂ h
        revert q₁ q₂ h
        fin_cases e <;> fin_cases sy <;> fin_cases sz <;> decide :
          Function.Injective (lhsPortPerm6 e sy sz))) e0 sy0 sz0
    have hLHS_conj : (((uMux27Layout * uSpeciesSwap50Layout)⁻¹).1 *
        (rSQ rPKinLayout rPKin_disj_rRest239).embedMatrix MatQft247 *
        (uMux27Layout * uSpeciesSwap50Layout).1).mulVec (DynCircExt.ket δ) =
        ((rSQ rPort hPort).embedMatrix MatQft247).mulVec (DynCircExt.ket δ) :=
      conj_rSQ_embedMatrix_mulVec_ket rPKinLayout rPKin_disj_rRest239 rPort hPort MatQft247
        (uMux27Layout * uSpeciesSwap50Layout) lhsPermBits InvL hInvL_write
        (fun η hη ↦ by
          rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_dc_eq_sb,
            uSpeciesSwap50Layout_mulVec_ket η hη.1]
          dsimp only [uMux27Layout, lhsPermBits]
          rw [embedUnitary_toBracket_ket, StructuredCB.toCB_evalBits_eq_evalS
            bAxisMux27_props.2.2, ket_dc_eq_sb])
        (fun η ⟨h21, he, hsy, hsz⟩ k ↦ by
          rw [← rPort6Layout_zero_eq_rPKin k]
          change lhsPermBits η (bmTgt rBellMux71Layout k ⟨0, by decide⟩) = _
          rw [(lhsPermBits_apply h21).1 k ⟨0, by decide⟩, he, hsy, hsz, lhsPortPerm6_zero]
          rfl)
        (fun η ⟨h21, _, _, _⟩ j ↦ (lhsPermBits_apply h21).2 _ (rRest239_ne_bmTgt j))
        (fun η z hη ↦ by
          let η' := DynCircExt.writeReg η (rSQ rPort hPort) z
          obtain ⟨h21', he', hsy', hsz'⟩ := hInvL_write η z hη; obtain ⟨h21, he, hsy, hsz⟩ := hη
          ext u
          by_cases hTgt : ∃ (k : Fin 8) (q : Fin 6), u = bmTgt rBellMux71Layout k q
          · rcases hTgt with ⟨k, q, rfl⟩
            by_cases hq0 : q = ⟨0, by decide⟩
            · subst hq0
              have hL0 : bmTgt rBellMux71Layout k ⟨0, by decide⟩ =
                  rSQ rPKinLayout rPKin_disj_rRest239 ⟨k.val, by omega⟩ := by
                rw [rSQ_apply, dite_eq_left k.isLt]; exact rPort6Layout_zero_eq_rPKin k
              have hR0 : bmTgt rBellMux71Layout k p₀ = rSQ rPort hPort ⟨k.val,
                by omega⟩ := by rw [rSQ_apply, dite_eq_left k.isLt]; rfl
              conv_lhs => rw [hL0, DynCircExt.writeReg_apply_reg]
              rw [(lhsPermBits_apply h21').1 k ⟨0, by decide⟩, he', hsy', hsz',
                lhsPortPerm6_zero, show activePort6 e0 sy0 sz0 = p₀ from rfl, hR0]
              exact (DynCircExt.writeReg_apply_reg η (rSQ rPort hPort) z ⟨k.val,
                by omega⟩).symm
            · have hNotSrc := bmTgt_not_mem_rSQ_of_ne rPKin_disj_rRest239
                (fun k' ↦ (rPort6Layout_zero_eq_rPKin k').symm) hq0 k
              have hNotPort := bmTgt_not_mem_rSQ_of_ne hPort (fun _ ↦ rfl)
                (fun hp ↦ hq0 (hPermInj (hp.trans (lhsPortPerm6_zero e0 sy0 sz0).symm))) k
              rw [DynCircExt.writeReg_apply_of_not_mem _ _ z _ hNotSrc,
                (lhsPermBits_apply h21).1 k q,
                (lhsPermBits_apply h21').1 k q, he, hsy, hsz, he', hsy', hsz']
              exact (DynCircExt.writeReg_apply_of_not_mem η (rSQ rPort hPort) z _
                hNotPort).symm
          · push Not at hTgt
            by_cases hRest : ∃ j : Fin 239, u = rRest239 j
            · rcases hRest with ⟨j, rfl⟩
              conv_lhs => rw [rRest239_eq_rSQ rPKinLayout rPKin_disj_rRest239 j,
                DynCircExt.writeReg_apply_reg]
              rw [(lhsPermBits_apply h21').2 (rRest239 j) hTgt, rRest239_eq_rSQ rPort hPort j,
                DynCircExt.writeReg_apply_reg]
            · push Not at hRest
              have hNotSrc := not_mem_rSQ_of_ne (hDisj := rPKin_disj_rRest239)
                (fun k e ↦ hTgt k ⟨0, by decide⟩
                    (e.trans (rPort6Layout_zero_eq_rPKin k).symm)) hRest
              rw [DynCircExt.writeReg_apply_of_not_mem _ _ z u hNotSrc,
                (lhsPermBits_apply h21).2 u hTgt, (lhsPermBits_apply h21').2 u hTgt]
              exact (DynCircExt.writeReg_apply_of_not_mem η (rSQ rPort hPort) z u
                (not_mem_rSQ_of_ne (fun k e ↦ hTgt k p₀ e) hRest)).symm)
        (δ := δ) ⟨h6104, rfl, rfl, rfl⟩
    let InvR : BitAssignment dLayout → Prop := fun η ↦
        η wAyKin = 0 ∧ (∀ p : Fin 6, η (bmCtrl rBellMux71Layout p) = 0) ∧
        (∀ k : Fin 8, η (bmBuf rBellMux71Layout k) = 0) ∧ η wIsElecKin = e0 ∧ η wKinAxis0 = sy0 ∧
        η wKinAxis1 = sz0
    have hInvR_write (η : BitAssignment dLayout) (z : BitAssignment 247) :
        InvR η → InvR (DynCircExt.writeReg η (rSQ rPort hPort) z) :=
      fun ⟨hAy, hC, hB, he, hsy, hsz⟩ ↦
        ⟨(hKeep10 rOneHot10_3 η z).trans hAy,
         fun p ↦ (hKeep10 (rOneHot10_ctrl p) η z).trans (hC p),
         fun k ↦ (DynCircExt.writeReg_apply_of_not_mem η _ z _ (not_mem_rSQ_of_ne
            (fun k' e ↦ hbt_all_bm rBellMux71Layout k k' p₀ e)
            (fun j e ↦ (rRest239_ne_bmBuf j k) e.symm))).trans (hB k),
         (hKeep10 rOneHot10_0 η z).trans he, (hKeep10 rOneHot10_1 η z).trans hsy,
         (hKeep10 rOneHot10_2 η z).trans hsz⟩
    have hRHS_write : ∀ η z, InvR η → DynCircExt.writeReg (rhsPermBits η) (rSQ rBmBufLayout
        rBmBuf_disj_rRest239) z = rhsPermBits (DynCircExt.writeReg η (rSQ rPort hPort) z) :=
            fun η z hη ↦ by
      let η' :=
          DynCircExt.writeReg η (rSQ rPort hPort) z; obtain ⟨hAy', hC', hB', he', hsy', hsz'⟩ :=
          hInvR_write η z hη; obtain ⟨hAy, hC, hB, he, hsy, hsz⟩ := hη; obtain ⟨hRB, hRT, hRO⟩ :=
          rhsPermBits_apply hAy hC hB; obtain ⟨hRB', hRT', hRO'⟩ := rhsPermBits_apply hAy' hC' hB'
      have hp_eq : activePort6 (η wIsElecKin) (η wKinAxis0) (η wKinAxis1) = p₀ := by
        rw [he, hsy, hsz]
      have hp_eq' : activePort6 (η' wIsElecKin) (η' wKinAxis0) (η' wKinAxis1) = p₀ := by
        dsimp only [η']; rw [he', hsy', hsz']
      rw [hp_eq] at hRB hRT hRO; rw [hp_eq'] at hRB' hRT' hRO'
      have h10_eq : (fun i : Fin 10 ↦ η' (rOneHot10Layout i)) = (fun i : Fin 10 ↦
          η (rOneHot10Layout i)) :=
        funext fun i ↦
            DynCircExt.writeReg_apply_of_not_mem η _ z _ (rOneHot10_not_mem_rSQ_rPort p₀ i)
      ext u
      by_cases huB : ∃ k : Fin 8, u = bmBuf rBellMux71Layout k
      · rcases huB with ⟨k, rfl⟩
        have hLSQ : bmBuf rBellMux71Layout k = rSQ rBmBufLayout rBmBuf_disj_rRest239 ⟨k.val,
            by omega⟩ := by
          rw [rSQ_apply, dite_eq_left k.isLt]; rfl
        have hRSQ : bmTgt rBellMux71Layout k p₀ = rSQ rPort hPort ⟨k.val, by omega⟩ := by
          rw [rSQ_apply, dite_eq_left k.isLt]; rfl
        conv_lhs => rw [hLSQ, DynCircExt.writeReg_apply_reg]
        rw [hRB' k, hRSQ, DynCircExt.writeReg_apply_reg]
      · push Not at huB
        by_cases huT : ∃ k : Fin 8, u = bmTgt rBellMux71Layout k p₀
        · rcases huT with ⟨k, rfl⟩
          have hNotBuf :
              bmTgt rBellMux71Layout k p₀ ∉ Set.range (rSQ rBmBufLayout rBmBuf_disj_rRest239).wires
              :=
              not_mem_rSQ_of_ne (fun k' e ↦ (hbt_all_bm rBellMux71Layout k' k p₀) e.symm)
              (fun j e ↦ (rRest239_ne_bmTgt j k p₀) e.symm)
          rw [DynCircExt.writeReg_apply_of_not_mem _ _ z _ hNotBuf, hRT k, hRT' k]
        · push Not at huT
          by_cases huR : ∃ j : Fin 239, u = rRest239 j
          · rcases huR with ⟨j, rfl⟩
            conv_lhs =>
                rw [rRest239_eq_rSQ rBmBufLayout rBmBuf_disj_rRest239 j,
                DynCircExt.writeReg_apply_reg]
            rw [hRO' (rRest239 j) huB huT, (oneHot6Bits_props hAy' hC').2.2 _ (rRest239_ne_wAyKin j)
                (rRest239_ne_bmCtrl j),
                rRest239_eq_rSQ rPort hPort j, DynCircExt.writeReg_apply_reg]
          · push Not at huR
            have hNotBuf : u ∉ Set.range (rSQ rBmBufLayout rBmBuf_disj_rRest239).wires :=
                not_mem_rSQ_of_ne huB huR; have hNotPort : u ∉ Set.range (rSQ rPort hPort).wires :=
                                             not_mem_rSQ_of_ne huT huR;
                                             rw [DynCircExt.writeReg_apply_of_not_mem _ _ z u
                                             hNotBuf, hRO u huB huT,
                                             hRO' u huB huT]; dsimp only [oneHot6Bits]
            by_cases hm10 : u ∈ Set.range rOneHot10Layout.wires
            · rcases hm10 with ⟨i, rfl⟩
              rw [DynCircExt.writeReg_apply_reg, DynCircExt.writeReg_apply_reg, h10_eq]
            · rw [DynCircExt.writeReg_apply_of_not_mem η rOneHot10Layout _ u hm10,
                  DynCircExt.writeReg_apply_of_not_mem η' rOneHot10Layout _ u hm10]; exact
                  (DynCircExt.writeReg_apply_of_not_mem η (rSQ rPort hPort) z u hNotPort).symm
    have hRHS_conj :=
        conj_rSQ_embedMatrix_mulVec_ket rBmBufLayout rBmBuf_disj_rRest239 rPort hPort MatQft247
      (uPortSwapLayout * uOneHot6Layout) rhsPermBits InvR hInvR_write (fun η _ ↦
          uPortSwap_uOneHot6_mulVec_ket η)
      (fun η ⟨hAy, hC, hB, he, hsy, hsz⟩ k ↦ by
        have h := (rhsPermBits_apply hAy hC hB).1 k
        rw [he, hsy, hsz] at h; exact h)
      (fun η ⟨hAy, hC, hB, _, _, _⟩ j ↦ ((rhsPermBits_apply hAy hC hB).2.2 _ (rRest239_ne_bmBuf j)
          (fun k ↦ rRest239_ne_bmTgt j k _)).trans
        ((oneHot6Bits_props hAy hC).2.2 _ (rRest239_ne_wAyKin j) (rRest239_ne_bmCtrl j)))
      hRHS_write (δ := δ) ⟨hAy0, hCtrl0, hBuf0, rfl, rfl, rfl⟩
    have hPortInvKet : ∀ ξ : BitAssignment dLayout,
        KinBellMux6.AtMostOneCtrl (bmCtrl rBellMux71Layout) ξ →
        uPortSwapLayout.1.mulVec (DynCircExt.ket ξ) =
            (uPortSwapLayout⁻¹).1.mulVec (DynCircExt.ket ξ) := fun ξ hOne ↦ by
      have hSq : (uPortSwapLayout.1 * uPortSwapLayout.1).mulVec (DynCircExt.ket ξ) =
          DynCircExt.ket ξ
          := by rw [ket_dc_eq_sb]; simpa only [uPortSwapLayout,
                  Fin.eta] using portSwapVec_involutive_ket_prefix rBellMux71Layout 8 le_rfl hOne
      conv_rhs => rw [← hSq]
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, show (uPortSwapLayout⁻¹).1 *
          uPortSwapLayout.1 = 1 from congrArg
          Subtype.val (inv_mul_cancel uPortSwapLayout), Matrix.one_mul]
    have hSwapEqInv :
        uPortSwapLayout.1.mulVec (B247.mulVec (uPortSwapLayout.1.mulVec (uOneHot6Layout.1.mulVec
        (DynCircExt.ket δ)))) =
        (uPortSwapLayout⁻¹).1.mulVec (B247.mulVec (uPortSwapLayout.1.mulVec (uOneHot6Layout.1.mulVec
        (DynCircExt.ket δ)))) := by
      have h12 : uPortSwapLayout.1.mulVec (uOneHot6Layout.1.mulVec (DynCircExt.ket δ)) =
          DynCircExt.ket (rhsPermBits δ)
          := by rw [Matrix.mulVec_mulVec,
                  ← Submonoid.coe_mul]; exact uPortSwap_uOneHot6_mulVec_ket δ
      rw [h12,
          embedMatrix_mulVec_ket_sym (rSQ rBmBufLayout rBmBuf_disj_rRest239) MatQft247 (rhsPermBits
          δ), Matrix.mulVec_sum, Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun z' _ ↦ ?_
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      refine congrArg (_ • ·) (hPortInvKet _ (Or.inr ⟨p₀, ?_, fun p hp ↦ ?_⟩))
      · have hNot :=
            not_mem_rSQ_of_ne (rPort := rBmBufLayout) (hDisj := rBmBuf_disj_rRest239)
            (fun k e ↦ (hbc_bm rBellMux71Layout k
            p₀) e.symm) (fun j e ↦ (rRest239_ne_bmCtrl j p₀) e.symm)
        rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hNot,
            (rhsPermBits_apply hAy0 hCtrl0 hBuf0).2.2 _ (fun k ↦
            (hbc_bm rBellMux71Layout k p₀).symm) (fun k ↦ hc_disj_bm rBellMux71Layout k p₀ _)]
        exact (oneHot6Bits_props hAy0 hCtrl0).1
      · have hNot :=
            not_mem_rSQ_of_ne (rPort := rBmBufLayout) (hDisj := rBmBuf_disj_rRest239)
            (fun k e ↦ (hbc_bm rBellMux71Layout k
            p) e.symm) (fun j e ↦ (rRest239_ne_bmCtrl j p) e.symm)
        rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hNot,
            (rhsPermBits_apply hAy0 hCtrl0 hBuf0).2.2 _ (fun k ↦ (hbc_bm rBellMux71Layout k p).symm)
            (fun k ↦ hc_disj_bm rBellMux71Layout k p _)]
        exact (oneHot6Bits_props hAy0 hCtrl0).2.1 p hp
    rw [hSwapEqInv]
    have hMul10 :
        (uPortSwapLayout⁻¹).1.mulVec (B247.mulVec (uPortSwapLayout.1.mulVec (uOneHot6Layout.1.mulVec
        (DynCircExt.ket δ)))) =
        uOneHot6Layout.1.mulVec ((((uPortSwapLayout * uOneHot6Layout)⁻¹).1 * B247 *
        (uPortSwapLayout * uOneHot6Layout).1).mulVec (DynCircExt.ket δ))
        := by have h1 : uOneHot6Layout.1 * (uOneHot6Layout⁻¹).1 = 1 :=
                congrArg Subtype.val (mul_inv_cancel uOneHot6Layout);
                simp only [Matrix.mulVec_mulVec, _root_.mul_inv_rev, Submonoid.coe_mul,
                Matrix.mul_assoc]; rw [← Matrix.mul_assoc uOneHot6Layout.1 (uOneHot6Layout⁻¹).1, h1,
                Matrix.one_mul]
    rw [hMul10, hRHS_conj, ← hLHS_conj]
  · rw [ite_eq_right h0]; simp only [Matrix.mulVec_zero]
theorem portSwap1Circ_onRegister {d n : ℕ} (rT : QRegister d n) :
    ∀ (K : ℕ) (qB : Wire d) (wCtrl wTgt : Fin K → Wire d)
      (hbc : ∀ p, qB ≠ wCtrl p) (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p)
      (hbc' : ∀ p, rT qB ≠ rT (wCtrl p))
      (hbt' : ∀ p, rT qB ≠ rT (wTgt p))
      (hct' : ∀ p, rT (wCtrl p) ≠ rT (wTgt p)),
      portSwap1Circ K (rT qB) (fun p ↦ rT (wCtrl p)) (fun p ↦ rT (wTgt p)) hbc' hbt' hct' =
        (portSwap1Circ K qB wCtrl wTgt hbc hbt hct).onRegister rT
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | K + 1, qB, wCtrl, wTgt, hbc, hbt, hct, hbc', hbt', hct' => by
      dsimp only [portSwap1Circ, Circuit.onRegister]
      have ih :=
          portSwap1Circ_onRegister rT K qB (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc)
          (fun p ↦ hbc p.castSucc) (fun p ↦ hbt p.castSucc) (fun p ↦ hct p.castSucc)
          (fun p ↦ hbc' p.castSucc) (fun p ↦ hbt' p.castSucc) (fun p ↦ hct' p.castSucc)
      have hCnot : Circuit.CNOT (rT qB) (rT (wTgt (Fin.last K))) (hbt' (Fin.last K)) =
          (Circuit.CNOT qB (wTgt (Fin.last K)) (hbt (Fin.last K))).onRegister rT := by
        simp only [Circuit.CNOT, Circuit.onRegister]
        congr 1; ext i; fin_cases i <;> rfl
      have hToff : Circuit.TOFF (rT (wCtrl (Fin.last K))) (rT (wTgt (Fin.last K))) (rT qB)
          (hct' (Fin.last K)) (hbc' (Fin.last K)).symm (hbt' (Fin.last K)).symm =
          (Circuit.TOFF (wCtrl (Fin.last K)) (wTgt (Fin.last K)) qB (hct (Fin.last K))
          (hbc (Fin.last K)).symm (hbt (Fin.last K)).symm).onRegister rT := by
        simp only [Circuit.TOFF, Circuit.onRegister]
        congr 1; ext i; fin_cases i <;> rfl
      rw [ih, hCnot, hToff]; rfl
theorem portSwapVecCirc_onRegister {d n : ℕ} (rT : QRegister d n) (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire d) (wCtrl : Fin M → Wire d) (wTgt : Fin m → Fin M → Wire d)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p)
      (hbc' : ∀ k p, rT (qB k) ≠ rT (wCtrl p))
      (hbt' : ∀ k p, rT (qB k) ≠ rT (wTgt k p))
      (hct' : ∀ k p, rT (wCtrl p) ≠ rT (wTgt k p)),
      portSwapVecCirc M m (fun k ↦ rT (qB k)) (fun p ↦ rT (wCtrl p)) (fun k p ↦ rT (wTgt k p))
          hbc' hbt' hct' =
        (portSwapVecCirc M m qB wCtrl wTgt hbc hbt hct).onRegister rT
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | m + 1, qB, wCtrl, wTgt, hbc, hbt, hct, hbc', hbt', hct' => by
      dsimp only [portSwapVecCirc, Circuit.onRegister]
      rw [portSwapVecCirc_onRegister rT M m (fun k ↦ qB k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc)
          (fun k ↦ hbc k.castSucc) (fun k ↦ hbt k.castSucc) (fun k ↦ hct k.castSucc)
          (fun k ↦ hbc' k.castSucc) (fun k ↦ hbt' k.castSucc) (fun k ↦ hct' k.castSucc),
          portSwap1Circ_onRegister rT M (qB (Fin.last m)) wCtrl (wTgt (Fin.last m))
          (hbc (Fin.last m)) (hbt (Fin.last m)) (hct (Fin.last m)) (hbc' (Fin.last m))
          (hbt' (Fin.last m)) (hct' (Fin.last m))]
theorem projBit_zero_compose {d n : ℕ} (rT : QRegister d n)
    (u : Wire d) : projBit (rT u) 0 = rT.embedMatrix (projBit u 0) := by
  have hsing : QRegister.singleton (rT u) = rT.compose (QRegister.singleton u) :=
    congrArg QRegister.mk (Function.Embedding.ext fun _ ↦ rfl)
  dsimp only [projBit, QRegister.basisOutcomeProjector]; rw [hsing, rT.embedMatrix_compose]
theorem projBit0BM_compose {d n : ℕ} (rT : QRegister d n) (u : Wire d) : projBit0BM (rT u) =
    rT.embedMatrix (projBit0BM u) := projBit_zero_compose rT u
theorem projOpVecBM_compose {K d n : ℕ} (rT : QRegister d n)
    (P : Fin K → Operator (2 ^ d)) (P' : Fin K → Operator (2 ^ n))
    (hP : ∀ i : Fin K, P' i = rT.embedMatrix (P i)) :
    ∀ (q : ℕ) (hq : q ≤ K),
      projOpVecBM P' q hq = rT.embedMatrix (projOpVecBM P q hq)
  | 0, _ => rT.embedMatrix_one.symm
  | q + 1, hq => by
      dsimp only [projOpVecBM]
      rw [hP ⟨q, hq⟩, projOpVecBM_compose rT P P' hP q (Nat.le_of_succ_le hq), ← rT.embedMatrix_mul]

abbrev projZeroVec8 {n : ℕ} (f : Fin 8 → Wire n) : (q : ℕ) → q ≤ 8 → Operator (2 ^ n) :=
  projOpVecBM fun k ↦ projBit0BM (f k)

theorem projZeroVec8_compose {d n : ℕ} (rT : QRegister d n) (f : Fin 8 → Wire d) :
    ∀ (q : ℕ) (hq : q ≤ 8),
      projZeroVec8 (fun k ↦ rT (f k)) q hq = rT.embedMatrix (projZeroVec8 f q hq) :=
  projOpVecBM_compose rT _ _ fun k ↦ projBit0BM_compose rT (f k)

theorem projZeroVec8_mulVec_ket {n : ℕ} (f : Fin 8 → Wire n) (η : BitAssignment n) :
    ∀ (q : ℕ) (hq : q ≤ 8),
      (projZeroVec8 f q hq).mulVec (PhotochemistrySolution.XMeasUnld.ket η) =
        if ∀ j : Fin q, η (f ⟨j.val, Nat.lt_of_lt_of_le j.isLt hq⟩) = 0
        then PhotochemistrySolution.XMeasUnld.ket η else 0 :=
  projOpVecBM_mulVec_ket _ (fun k ↦ η (f k) = 0) η fun k ↦ projBit0BM_mulVec_ket (f k) η

def projInitBM68 {n : ℕ} (r : BellMuxReg 6 8 n) : Operator (2 ^ n) :=
    (∑ p₀ : Fin 6, projCtrlEqBM r p₀ 6 le_rfl) * projZeroVec8 (bmBuf r) 8 le_rfl *
    projZeroVec8 (bmH r) 8 le_rfl * projBit0BM (bmAnc r)
theorem projInitBM68_compose {d n : ℕ} (rT : QRegister d n) (r : BellMuxReg 6 8 d) :
    projInitBM68 (rT.compose r) = rT.embedMatrix (projInitBM68 r) := by
  dsimp only [projInitBM68]
  have hSum : (∑ p₀ : Fin 6, projCtrlEqBM (rT.compose r) p₀ 6 le_rfl) =
      rT.embedMatrix (∑ p₀ : Fin 6, projCtrlEqBM r p₀ 6 le_rfl) := by
    trans (∑ p₀ : Fin 6, rT.embedMatrix (projCtrlEqBM r p₀ 6 le_rfl))
    · refine Finset.sum_congr rfl fun p₀ _ ↦ projOpVecBM_compose rT _ _ (fun p ↦ ?_) 6 le_rfl
      by_cases hp : p = p₀ <;> simp only [hp, ↓reduceIte]
      · change projBit1BM (rT (bmCtrl r p₀)) = _
        dsimp only [projBit1BM]
        rw [projBit_zero_compose rT (bmCtrl r p₀), ← rT.embedMatrix_one,
          ← (QRegExt.embedMatrix_sub rT)]
      · exact projBit0BM_compose rT (bmCtrl r p)
    · induction (Finset.univ : Finset (Fin 6)) using Finset.cons_induction with
      | empty => simp [rT.embedMatrix_zero]
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih, rT.embedMatrix_add]
  have hB : projZeroVec8 (bmBuf (rT.compose r)) 8 le_rfl =
      rT.embedMatrix (projZeroVec8 (bmBuf r) 8 le_rfl) :=
      projZeroVec8_compose rT (bmBuf r) 8 le_rfl;
      have hH : projZeroVec8 (bmH (rT.compose r)) 8 le_rfl =
      rT.embedMatrix (projZeroVec8 (bmH r) 8 le_rfl) :=
      projZeroVec8_compose rT (bmH r) 8 le_rfl;
      have hA : projBit0BM (bmAnc (rT.compose r)) = rT.embedMatrix (projBit0BM (bmAnc r)) :=
      projBit0BM_compose rT (bmAnc r); rw [hSum, hB, hH, hA, ← rT.embedMatrix_mul,
      ← rT.embedMatrix_mul, ← rT.embedMatrix_mul]
theorem projInitBM68_mulVec_ket {n : ℕ} (r : BellMuxReg 6 8 n) (γ : BitAssignment n) :
    (projInitBM68 r).mulVec (XMeasUnld.ket γ) = if (StrictOneHot (bmCtrl r) γ ∧
    (∀ k : Fin 8, γ (bmBuf r k) = 0) ∧ (∀ k : Fin 8, γ (bmH r k) = 0) ∧ γ (bmAnc r) =
    0) then XMeasUnld.ket γ else 0 := by
  dsimp only [projInitBM68]; rw [← Matrix.mulVec_mulVec, projBit0BM_mulVec_ket]
  by_cases hA : γ (bmAnc r) = 0
  · rw [ite_eq_left hA, ← Matrix.mulVec_mulVec, projZeroVec8_mulVec_ket (bmH r) γ 8 le_rfl];
    simp only [Fin.eta]
    by_cases hH : ∀ k : Fin 8, γ (bmH r k) = 0
    · rw [ite_eq_left hH, ← Matrix.mulVec_mulVec, projZeroVec8_mulVec_ket (bmBuf r) γ 8 le_rfl];
      simp only [Fin.eta]
      by_cases hB : ∀ k : Fin 8, γ (bmBuf r k) = 0
      · rw [ite_eq_left hB, Matrix.sum_mulVec]
        by_cases hOne : StrictOneHot (bmCtrl r) γ
        · rw [ite_eq_left ⟨hOne, hB, hH, hA⟩]
          rcases hOne with ⟨p₀, hp1, hp0⟩
          rw [Finset.sum_eq_single p₀]
          · rw [projCtrlEqBM_mulVec_ket r p₀ γ 6 le_rfl]; simp only [Fin.eta]
            rw [ite_eq_left (fun p ↦ by split_ifs with hp <;> [exact hp ▸ hp1; exact hp0 p hp])]
          · intro p₁ _ hne
            rw [projCtrlEqBM_mulVec_ket r p₁ γ 6 le_rfl]; simp only [Fin.eta]
            rw [ite_eq_right]; intro hall
            have h1' : γ (bmCtrl r p₁) = 1 := by simpa using hall p₁
            exact zero_ne_one ((hp0 p₁ hne).symm.trans h1')
          · intro hm; exact absurd (Finset.mem_univ p₀) hm
        · rw [ite_eq_right (fun h ↦ hOne h.1)]
          refine Finset.sum_eq_zero fun p₀ _ ↦ ?_
          rw [projCtrlEqBM_mulVec_ket r p₀ γ 6 le_rfl]; simp only [Fin.eta]
          rw [ite_eq_right]; intro hall
          exact hOne ⟨p₀, by simpa using hall p₀, fun p hp ↦ by simpa [hp] using hall p⟩
      · rw [ite_eq_right hB, Matrix.mulVec_zero, ite_eq_right (fun h ↦ hB h.2.1)]
    · rw [ite_eq_right hH, Matrix.mulVec_zero, ite_eq_right (fun h ↦ hH h.2.2.1)]
  · rw [ite_eq_right hA, Matrix.mulVec_zero, ite_eq_right (fun h ↦ hA h.2.2.2)]
end QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6Step
end

noncomputable section
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.Kinetic664Stage4
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution.KetSupport PhotochemistrySolution PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SelectCompactAnc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.Qft8PostCancelT5 PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectKin526OneWrap PhotochemistrySolution.SelectQft8KinMid
open PhotochemistrySolution.XMeasChunkQromUnldA PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.Stage4Kin14Scb PhotochemistrySolution.Kinetic664
open PhotochemistrySolution.SelectRefl
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney hiding
  unitary_inv_comm
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr PgBase.phaseGradientState phaseFlipUnitary reflULGen bSpeciesSwap50
    Stage4KinFull.bAxisMux27 qft8PostCancel98CatU abpKin14Usel abpKin14Csel abpKin15SqFree2m1Usel
    abpKin15SqFree2m1Csel
theorem uKin2m1_98_fix_pK0 : uKinCat2m1_98UselLayout.1 * (pBit0 wIsKin *
    pBit0 (rWorkInnerLayout ⟨22, fin22_lt_521⟩)) = pBit0 wIsKin *
    pBit0 (rWorkInnerLayout ⟨22, fin22_lt_521⟩) ∧ uKinIdeal2m1UselLayout.1 *
    (pBit0 wIsKin * pBit0 (rWorkInnerLayout ⟨22, fin22_lt_521⟩)) = pBit0 wIsKin *
    pBit0 (rWorkInnerLayout ⟨22, fin22_lt_521⟩) := by
  let w22 := rWorkInnerLayout ⟨22, fin22_lt_521⟩
  let P := pBit0 wIsKin * pBit0 w22
  let Qcat :=
      qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout
  have hwKv : wIsKin.val = 5749 := val_rOut40Layout _
  have hw22v : w22.val = 6105 := val_rWorkInnerLayout _
  have hBit (u : Wire dLayout) (hu : u.val = 5749 ∨ u.val = 6105) :
      (Qcat.1 * pBit0 u = pBit0 u * Qcat.1) ∧
      (uMux27Layout.1 * pBit0 u = pBit0 u * uMux27Layout.1) ∧
      (uSpeciesSwap50Layout.1 * pBit0 u = pBit0 u * uSpeciesSwap50Layout.1) :=
    ⟨localOnQft16_comm_basisOutcomeProjector
        (qft8PostCancel98CatU_localOnQft16 () scrWLayout offKinLayout hoffKinLayout rPKinLayout
            qft8Stg3ValidP_layout).1
        (QRegister.singleton u)
        (QRegister.disjoint_iff.mpr fun i k e ↦ by
          fin_cases i
          have hv : u.val = _ :=
              (congrArg Fin.val e).trans (val_rPKinLayout k)
          have hk := k.isLt
          omega)
        (QRegister.disjoint_iff.mpr fun i c e ↦ by
          fin_cases i
          have hv : u.val = _ :=
              (congrArg Fin.val e).trans (val_locCat8_layout c)
          have hc := c.isLt
          omega) 0,
      embedUnitary_comm_of_disjoint rMux27Layout _ _ (QRegister.disjoint_iff.mpr fun j i e ↦ by
        fin_cases i
        rw [rMux27_eq_fn_w0] at e
        have hv : (mux27WireFn j).val = u.val := congrArg Fin.val e
        rw [val_mux27WireFn] at hv
        split_ifs at hv <;> omega) _,
      embedUnitary_comm_of_disjoint rSpeciesSwap50Layout _ _ (QRegister.disjoint_iff.mpr fun j i e ↦
          by
        fin_cases i
        rw [rSp50_eq_fn_w0] at e
        have hv : (speciesSwap50WireFn j).val = u.val := congrArg Fin.val e
        rw [val_speciesSwap50WireFn] at hv
        split_ifs at hv <;> omega) _⟩
  have bK := hBit wIsKin (.inl hwKv)
  have b22 := hBit w22 (.inr hw22v)
  let cf (U : Operator.Unitary (2 ^ dLayout)) (M : Operator (2 ^ dLayout)) b1 b2 hM :=
    conj_fix_proj (U⁻¹).1 U.1 M P (congrArg Subtype.val (inv_mul_cancel U))
        (comm_mul U.1 _ _ b1 b2) hM
  exact ⟨cf uSpeciesSwap50Layout uKinCoreCat2m1_98UselLayout.1 bK.2.2 b22.2.2
      (cf uMux27Layout (Qcat⁻¹ * uKinMid2m1UselLayout * Qcat).1 bK.2.1 b22.2.1
        (cf Qcat uKinMid2m1UselLayout.1 bK.1 b22.1 (matrix_ext_ket fun δ ↦ by
          dsimp only [P, pBit0]
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_basisOutcomeProjector_zero]
          by_cases h22 : ∀ i : Fin 1, δ ((QRegister.singleton w22) i) = 0
          · rw [ifPosSqf h22, ket_basisOutcomeProjector_zero]
            by_cases hK : ∀ i : Fin 1, δ ((QRegister.singleton wIsKin) i) = 0
            · rw [ifPosSqf hK, uKinMid2m1_isPhaseDiag_layout δ, kin2m1OutBit_eq_fn,
                show δ (rKin226Layout wOutKin226) = 0 from
                  (Fin.ext ((val_kin226WireFn wOutKin226).trans hw22v.symm) : rKin226Layout
                      wOutKin226 = w22) ▸ h22 0,
                show δ (rKin226Layout wIsKin226) = 0 from
                  (Fin.ext ((val_kin226WireFn wIsKin226).trans hwKv.symm) : rKin226Layout wIsKin226
                      = wIsKin) ▸ hK 0,
                zero_mul, add_zero, bitSign_zero, one_smul]
            · rw [ifNegSqf hK, Matrix.mulVec_zero]
          · rw [ifNegSqf h22, Matrix.mulVec_zero, Matrix.mulVec_zero]))),
    uKinIdeal2m1Usel_fix_pK0⟩
theorem uAlignedKinCat2m1_98Usel_fix (γ : BitAssignment dLayout) (hk0 : γ wIsKin = 0)
    (hw22 : γ (rWorkInnerLayout ⟨22, fin22_lt_521⟩) = 0) :
    uAlignedKinCat2m1_98UselLayout.1.mulVec (ket γ) = ket γ := by
  let ηk := pKinAlign0.fwdBits γ
  have hFk : uKinAlign0Layout.1.mulVec (ket γ) = ket ηk := fwdCirc_mulVec_ket pKinAlign0 γ
  unfold uAlignedKinCat2m1_98UselLayout
  rw [Submonoid.coe_mul, Submonoid.coe_mul, uKinAlign0Layout_inv_eq, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hFk, show uKinCat2m1_98UselLayout.1.mulVec (ket ηk) = ket ηk by
      rw [← show (pBit0 wIsKin * pBit0 (rWorkInnerLayout ⟨22,
          fin22_lt_521⟩)).mulVec (ket ηk) = ket ηk by
          rw [← Matrix.mulVec_mulVec,
            pBit0_ket ((fwdBits_not_target targetsIn_pKinAlign0 γ
              (fun h ↦
                  by
                    have : (rWorkInnerLayout ⟨22, fin22_lt_521⟩).val = 6105 :=
                       val_rWorkInnerLayout _
                    omega)).trans hw22),
            pBit0_ket ((fwdBits_not_target targetsIn_pKinAlign0 γ
              (fun h ↦ by
                have : wIsKin.val = 5749 := val_rOut40Layout _
                omega)).trans hk0)],
        Matrix.mulVec_mulVec, uKin2m1_98_fix_pK0.1],
    ← hFk, Matrix.mulVec_mulVec, ← Submonoid.coe_mul,
    uKinAlign0Layout_sq_one, Submonoid.coe_one, Matrix.one_mulVec]
theorem uKinCoreCat2m1_98Usel_inKetPred (η : BitAssignment dLayout)
    (hW : ∀ k : Fin 521, η (rWorkInnerLayout k) = 0) : inKetPred (fun ξ ↦ (∀ k : Fin 521,
    ξ (rWorkInnerLayout k) = 0) ∧ ∀ w : Wire dLayout, ¬(5616 ≤ w.val ∧ w.val ≤ 5649) →
    ¬(5755 ≤ w.val ∧ w.val ≤ 5778) → ξ w = η w) (uKinCoreCat2m1_98UselLayout.1.mulVec (ket η)) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  intro ξ hnz
  let PW := rWorkInnerLayout.basisOutcomeProjector 0
  have hPWη : PW.mulVec (ket η) = ket η := by rw [ket_basisOutcomeProjector_zero, ifPosSqf hW]
  have hwKv : wIsKin.val = 5749 := val_rOut40Layout _
  have hξW : ∀ k : Fin 521, ξ (rWorkInnerLayout k) = 0 := by
    by_contra hnot
    have h0 := congrFun (show uKinCoreCat2m1_98UselLayout.1.mulVec (ket η) =
        PW.mulVec (uKinCoreCat2m1_98UselLayout.1.mulVec (ket η)) by
      nth_rw 1 [← hPWη]
      rw [Matrix.mulVec_mulVec, (uKinCoreCat2m1_98Usel_pw_comm (w := wIsKin)
        (fun _ ↦ by omega) (fun _ ↦ by omega) (fun _ ↦ by omega)).1, ← Matrix.mulVec_mulVec])
      ((basisBitsEquiv dLayout).symm ξ)
    rw [proj_zero_vec_entry rWorkInnerLayout _ ξ, ifNegSqf hnot] at h0
    exact hnz h0
  refine ⟨hξW, fun w hw1 hw2 ↦ ?_⟩
  by_cases hw3 : 6083 ≤ w.val ∧ w.val ≤ 6603
  · rw [show w = rWorkInnerLayout ⟨w.val - 6083, by omega⟩ from
      Fin.ext (by
        rw [val_rWorkInnerLayout]
        dsimp only
        omega), hξW, hW]
  · have hc := (uKinCoreCat2m1_98Usel_pw_comm (fun h ↦ hw1 ⟨by omega, h.2⟩) hw2 hw3).2
    have h0 := congrFun (show (pBit0 w).mulVec (uKinCoreCat2m1_98UselLayout.1.mulVec (ket η)) =
        (uKinCoreCat2m1_98UselLayout.1 * PW).mulVec ((pBit0 w).mulVec (ket η)) by
      nth_rw 1 [← hPWη]
      dsimp only [PW] at *
      simp only [Matrix.mul_assoc] at hc
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hc]) ((basisBitsEquiv dLayout).symm ξ)
    conv_lhs at h0 =>
      dsimp only [pBit0]
      rw [proj_zero_vec_entry (QRegister.singleton w) _ ξ]
    rcases DynCircExt.bit_cases (η w) with hη0 | hη1 <;>
        rcases DynCircExt.bit_cases (ξ w) with hx0 | hx1
    · exact hx0.trans hη0.symm
    · rw [ifNegSqf (show ¬ ∀ i : Fin 1, ξ ((QRegister.singleton w) i) = 0 from fun h ↦
          zero_ne_one ((h 0).symm.trans hx1)),
        pBit0_ket hη0, ← Matrix.mulVec_mulVec, hPWη] at h0
      exact absurd h0.symm hnz
    · dsimp only [pBit0] at h0
      rw [ifPosSqf (show ∀ i : Fin 1, ξ ((QRegister.singleton w) i) = 0 from fun _ ↦ hx0),
          ket_basisOutcomeProjector_zero,
        ifNegSqf (show ¬ ∀ i : Fin 1, η ((QRegister.singleton w) i) = 0 from fun h ↦
            zero_ne_one ((h 0).symm.trans hη1)),
        Matrix.mulVec_zero, Pi.zero_apply] at h0
      exact absurd h0 hnz
    · exact hx1.trans hη1.symm
theorem uAlignedKinCat2m1_98Usel_preserves_routed {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (γ : BitAssignment dLayout) (hγ : IsRoutedKet decodeCoin γ) :
    inKetPred (IsRoutedKet decodeCoin) (uAlignedKinCat2m1_98UselLayout.1.mulVec (ket γ)) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  obtain ⟨β, c, z, hScr, rfl⟩ := hγ
  let γ := routedKet decodeCoin β c z
  have hW : ∀ k : Fin 521, γ (rWorkInnerLayout k) = 0 := routedKet_workInner hScr c z
  by_cases hk0 : γ wIsKin = 0
  · rw [uAlignedKinCat2m1_98Usel_fix γ hk0 (hW ⟨22, fin22_lt_521⟩)]
    exact inKetPred_ket ⟨β, c, z, hScr, rfl⟩
  · have hNotKin (bN1 bN2 : Bool) (n1 n2 : ℕ) (bE1 bE2 : Bool) (e1 e2 : ℕ) (bScr bPot bNN : Bool)
        (sp1 aux2 : ℕ) (hB : n1 < 64 ∧ n2 < 64 ∧ e1 < 256 ∧ e2 < 256)
        (hm : zeroNEremOutMask (decodeCoin c) =
          packOut40ZeroNErem bN1 bN2 n1 n2 bE1 bE2 e1 e2 bScr bPot false bNN sp1 aux2) : False :=
      hk0 (packOut40ZeroNErem_fields bN1 bN2 n1 n2 bE1 bE2 e1 e2 bScr bPot false bNN sp1 aux2
        hB.1 hB.2.1 hB.2.2.1 hB.2.2.2 γ (fun j ↦ (routedKet_out40 hScr c z j).trans
          (congrArg (fun m : ℕ ↦
              if m.testBit j.val then (1 : ZMod 2) else 0) hm))).2.2.2.2.2.2.2.2.2.2.1
    match hs : decodeCoin c with
    | .idle =>
          exact (hNotKin false false 0 0 false false 0 0 false false false 0 0 (by omega)
          (congrArg zeroNEremOutMask hs)).elim
    | .ee n1 e1 e2 =>
        exact (hNotKin true false n1.val 0 true true e1.val e2.val true true false (nucSpecies
            n1).val 0
          (by omega) (congrArg zeroNEremOutMask hs)).elim
    | .nn n1 n2 e1 =>
        exact (hNotKin true true n1.val n2.val true false e1.val 0 true true true (nucSpecies
            n1).val
          (nucSpecies n2).val (by omega) (congrArg zeroNEremOutMask hs)).elim
    | .en n1 e1 =>
        exact (hNotKin true false n1.val 0 true false e1.val 0 false true false (nucSpecies n1).val
            0
          (by omega) (congrArg zeroNEremOutMask hs)).elim
    | .kin i ax =>
        let ηk := pKinAlign0.fwdBits γ
        have hWη : ∀ k : Fin 521, ηk (rWorkInnerLayout k) = 0 := fun k ↦
          (fwdBits_not_target targetsIn_pKinAlign0 γ (fun h ↦
              by
                have := val_rWorkInnerLayout k
                omega)).trans (hW k)
        have spW {δ : BitAssignment dLayout} {k : Fin 521} (hk : δ (rWorkInnerLayout k) = 0) :=
          (speciesSwapBits_of_other (by
            rw [val_rWorkInnerLayout]
            omega)
              (by
                rw [val_rWorkInnerLayout]
                omega)).trans hk
        have hFwdK : ∀ α, uKinAlign0Layout.1.mulVec (ket α) = ket (pKinAlign0.fwdBits α) :=
          fwdCirc_mulVec_ket pKinAlign0
        rw [show uAlignedKinCat2m1_98UselLayout.1.mulVec (ket γ) =
            (uKinAlign0Layout * uSpeciesSwap50Layout⁻¹).1.mulVec
              (uKinCoreCat2m1_98UselLayout.1.mulVec (ket (speciesSwapBits ηk))) by
          unfold uAlignedKinCat2m1_98UselLayout uKinCat2m1_98UselLayout
          simp only [Submonoid.coe_mul, uKinAlign0Layout_inv_eq, ← Matrix.mulVec_mulVec]
          rw [hFwdK γ, uSpeciesSwap50Layout_mulVec_ket ηk (hWη ⟨21, by omega⟩)]]
        refine inKetPred_mulVec (uKinAlign0Layout * uSpeciesSwap50Layout⁻¹).1 (fun ξ hξ ↦ ?_)
          (uKinCoreCat2m1_98Usel_inKetPred (speciesSwapBits ηk) fun k ↦ spW (hWη k))
        rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          inv_mulVec_of_fwd uSpeciesSwap50Layout
            ((uSpeciesSwap50Layout_mulVec_ket (speciesSwapBits ξ) (spW (hξ.1 ⟨21, by omega⟩))).trans
              (congrArg ket (speciesSwapBits_invol ξ))),
          hFwdK (speciesSwapBits ξ)]
        exact (em (i.val < 47)).elim
          (fun hi ↦ inKetPred_ket (kin_nuc_rebuild hScr c z i ax hs hi hξ))
          (fun hi ↦ inKetPred_ket (kin_elec_rebuild hScr c z i ax hs hi hξ))
end QuantumComputation.Specs.PhotochemistrySolution.Kinetic664Stage4
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket)
attribute [local irreducible]
    QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState abpKin14Usel systemQubits_frozen
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open PrimitiveGate PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.XMeasChunkQromUnldA
attribute [local irreducible] phaseFlipUnitary abpKin14Csel bSpeciesSwap50
theorem conj_seq_cat_eq {M : Type*} [Monoid M] (K A Ucat Uid Kc Kid V Pc : M)
    (cA : A * Pc = Pc * A) (hU : Ucat * Pc = Uid * Pc) (hKc : Kc = K * Ucat * A)
    (hKid : Kid = K * Uid * A) (cV : V * Pc = Pc * V) : (Kc * V) * Pc = (Kid * V) * Pc := by
  have hK : Kc * Pc = Kid * Pc := by
    calc Kc * Pc = K * Ucat * (A * Pc) := by rw [hKc]; simp only [mul_assoc]
      _ = K * (Ucat * Pc) * A := by rw [cA]; simp only [mul_assoc]
      _ = K * (Uid * Pc) * A := by rw [hU]
      _ = K * Uid * (Pc * A) := by simp only [mul_assoc]
      _ = Kid * Pc := by rw [← cA, hKid]; simp only [mul_assoc]
  calc (Kc * V) * Pc = Kc * (V * Pc) := by simp only [mul_assoc]
    _ = (Kc * Pc) * V := by rw [cV]; simp only [mul_assoc]
    _ = (Kid * Pc) * V := by rw [hK]
    _ = (Kid * V) * Pc := by simp only [mul_assoc, ← cV]
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.KetSupport PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.InPlaceModAdd PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectDataBuilder
theorem speciesOfBits2_of_fin4 (s : Fin 4) : speciesOfBits2 (if s.val.testBit 0 then 1 else 0)
    (if s.val.testBit 1 then 1 else 0) = s := by
  fin_cases s <;> rfl
theorem idxValD_elec_stage2_eq {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout} {c : Fin (2 ^ 41)} {z : BitAssignment 41}
    (hKE : ∀ j, routedStage2 decodeCoin β c z (rElecLayout j) =
    routedStage1 decodeCoin β c z (rElecLayout j)) : idxValD (rIdx1 rElecLayout)
    (routedStage2 decodeCoin β c z) = idxValD (rIdx1 rElecLayout)
    (routedStage1 decodeCoin β c z) ∧ idxValD (rIdx2 rElecLayout)
    (routedStage2 decodeCoin β c z) = idxValD (rIdx2 rElecLayout)
    (routedStage1 decodeCoin β c z) :=
  ⟨Nat.eq_of_testBit_eq fun d ↦ by
      rw [testBit_idxValD, testBit_idxValD]
      by_cases hd : d < 8
      · rw [dite_eq_left hd, dite_eq_left hd]
        simp only [hKE ⟨2 + d, by dsimp [routerWidth]; omega⟩]
      · rw [dite_eq_right hd, dite_eq_right hd],
   Nat.eq_of_testBit_eq fun d ↦ by
      rw [testBit_idxValD, testBit_idxValD]
      by_cases hd : d < 8
      · rw [dite_eq_left hd, dite_eq_left hd]
        simp only [hKE ⟨2 + 8 + d, by dsimp [routerWidth]; omega⟩]
      · rw [dite_eq_right hd, dite_eq_right hd]⟩
theorem rPot0_ports_eq : wPotSp2B0 rPot0Layout = wAxis0 ∧ wPotSp2B1 rPot0Layout = wAxis1 ∧
    (∀ b : Fin 24, rPotNucA rPot0Layout b = rBufLo rNucLayout b) ∧
    (∀ b : Fin 24, rPotNucB rPot0Layout b = rBufHi rNucLayout b) ∧
    (∀ b : Fin 24, rPotElecA rPot0Layout b = rBufLo rElecLayout b) ∧
    (∀ b : Fin 24, rPotElecB rPot0Layout b = rBufHi rElecLayout b) ∧
    (∀ k : Fin 41, rPotCoin41 rPot0Layout k = rInner41Layout k) := by
  have PF := rPot0_flags_eq_out40
  refine ⟨PF.2.2.2.2.2.2.1.trans (congrArg rOut40Layout (Fin.ext rfl)),
    PF.2.2.2.2.2.2.2.trans (congrArg rOut40Layout (Fin.ext rfl)),
    fun b ↦ Fin.ext ?_, fun b ↦ Fin.ext ?_,
    fun b ↦ Fin.ext ?_, fun b ↦ Fin.ext ?_, fun k ↦ Fin.ext ?_⟩
  · change (potZeroNEremWireFn 0 pot0_le_690 ⟨9 + b.val, _⟩).val = _;
    rw [val_potZeroNEremWireFn pot0_le_690, (val_rBufLo_hi_nuc b).1]
    dsimp only; split_ifs <;> omega
  · change (potZeroNEremWireFn 0 pot0_le_690 ⟨33 + b.val, _⟩).val = _;
    rw [val_potZeroNEremWireFn pot0_le_690, (val_rBufLo_hi_nuc b).2]
    dsimp only; split_ifs <;> omega
  · change (potZeroNEremWireFn 0 pot0_le_690 ⟨57 + b.val, _⟩).val = _;
    rw [val_potZeroNEremWireFn pot0_le_690, (val_rBufLo_hi b).1]
    dsimp only; split_ifs <;> omega
  · change (potZeroNEremWireFn 0 pot0_le_690 ⟨81 + b.val, _⟩).val = _;
    rw [val_potZeroNEremWireFn pot0_le_690, (val_rBufLo_hi b).2]
    dsimp only; split_ifs <;> omega
  · change (potZeroNEremWireFn 0 pot0_le_690 ⟨105 + k.val, _⟩).val = _;
    rw [val_potZeroNEremWireFn pot0_le_690, val_rInner41Layout]
    dsimp only; split_ifs <;> omega
theorem coordOfReg24_zero {n : ℕ} (r24 : QRegister 24 n) (δ : BitAssignment n)
    (hz : ∀ b : Fin 24, δ (r24 b) = 0) : coordOfReg24 r24 δ = 0 := by
  funext ax; apply Fin.ext
  change finBitsVal (fun k : Fin 8 ↦ δ (r24 ⟨8 * ax.val + k.val, coordOfReg24_lt ax k⟩)) = 0
  rw [finBitsVal_eq_sum_pow]; simp [hz]
theorem coordOfReg24_sysCoord (r24 : QRegister 24 dLayout) (δ β : BitAssignment dLayout)
    (i : Particle_frozen) (hPort : ∀ (ax : Fin 3)
    (k : Fin 8), δ (r24 ⟨8 * ax.val + k.val, coordOfReg24_lt ax k⟩) =
    β (rSysLayout ((coordinateRegister_frozen i ax) k))) : coordOfReg24 r24 δ =
    sysCoord (readRegIdx rSysLayout β) i := by
  funext ax
  have hbits : (fun k : Fin 8 ↦ δ (r24 ⟨8 * ax.val + k.val, coordOfReg24_lt ax k⟩)) =
      basisBits 8 (sysCoord (readRegIdx rSysLayout β) i ax)
      := by funext k; rw [hPort ax k]; unfold sysCoord readRegIdx;
              rw [QRegExt.basisBits_extractIdx,
              QRegExt.basisBits_extractIdx]; exact
              (congrFun ((basisBitsEquiv dLayout).apply_symm_apply β) _).symm
  unfold coordOfReg24; rw [hbits, byteOfBits_basisBits]
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end

end ScopedLocalHelpers
end
