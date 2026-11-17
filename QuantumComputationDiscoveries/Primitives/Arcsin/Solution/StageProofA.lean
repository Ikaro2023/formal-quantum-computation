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

public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.StageCircuitB
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

namespace QuantumComputation.Specs.ArcsinImpl

open Function Operator Step

-- ============================================================================
-- Section 1: Stage 1 (s1Ops) and Stage 7 (s7Ops)
-- ============================================================================

def s1AncW : List Nat := rangeList 50 23
def s7AncW : List Nat :=
  [50, 51, 52, 56, 58, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 80, 81, 82, 83, 84, 85, 86]

theorem s1IncOps_cert :
    checkAdderRangeSpec s1IncOps 25 24 false false [] s1AncW
      (.wire 49 false) (List.replicate 24 .zero) = true := by
  decide +kernel

theorem s7IncOps_cert :
    checkAdderRangeSpec s7IncOps 25 24 false false [] s7AncW
      (.wire 49 false) (List.replicate 24 .zero) = true := by
  decide +kernel

def s1XLo : List XWire := (rangeList 25 23).map (fun w => .wire w false) ++ [.zero, .zero]
def s1FlipBits48 : List Nat := [0, 1, 3, 4, 6, 7, 8, 9, 10, 11, 16, 19, 22]
def s1XHi : List XWire :=
  (rangeList 0 23).map (fun i => .wire (25 + i) (s1FlipBits48.elem i)) ++ [.one, .zero]

theorem s1Add_lo_cert :
    checkAdderRangeSpec s1AddOps 0 25 false false [] ([48] ++ rangeList 50 24) .zero
      s1XLo = true := by
  decide +kernel

theorem s1Add_hi_cert :
    checkAdderRangeSpec s1AddOps 0 25 false false [48] (rangeList 50 24) .zero s1XHi = true := by
  decide +kernel

def u24OfY (y : Nat) : Nat :=
  if y.testBit 24 then (33554432 - y) % 16777216 else y

theorem u24OfY_lt {y : Nat} (hy : y < 33554432) : u24OfY y < 16777216 := by
  unfold u24OfY
  split_ifs with h24
  · exact Nat.mod_lt _ (by positivity)
  · by_contra hge
    have hge' : 16777216 ≤ y := by omega
    have hdiv : y / 16777216 = 1 := by omega
    have htb : y.testBit 24 = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      change decide (y / 16777216 % 2 = 1) = true
      rw [hdiv]; decide
    exact absurd htb (by simp [h24])

theorem sumBits_replicate_zero (M : Nat) (m : Fin 100 → Bool) :
    sumBits M (evalXWires m (List.replicate M .zero)) = 0 := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [sumBits_succ]
    have h1 : sumBits M (evalXWires m (List.replicate (M + 1) .zero)) =
              sumBits M (evalXWires m (List.replicate M .zero)) := by
      refine sumBits_congr fun k hk => ?_
      simp [evalXWires, hk, (by omega : k < M + 1), evalXWire]
    have h2 : evalXWires m (List.replicate (M + 1) .zero) M = false := by
      simp [evalXWires, evalXWire]
    rw [h1, ih, h2]; rfl

theorem exec_s1BOps {m0 : Fin 100 → Bool} :
    ∃ mB : Fin 100 → Bool,
      execList102 s1BOps m0 = some mB ∧
      (∀ w : Fin 100, 25 ≤ w.val → mB w = m0 w) ∧
      outVal102 mB = if m0 ⟨49, by decide⟩ then 33554431 - outVal102 m0 else outVal102 m0 := by
  have hex := execList102_xorTargets (by decide : 49 < 100) s1BTargets m0 (by decide) (by decide)
  refine ⟨_, hex, fun w hw => ?_, ?_⟩
  · have hnel : s1BTargets.elem w.val = false := by
      cases he : s1BTargets.elem w.val
      · rfl
      · have := mem_rangeList_iff.mp (List.mem_of_elem_eq_true he); omega
    rw [hnel]; rfl
  · cases hs : m0 ⟨49, by decide⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine outVal102_congr fun j hj => ?_
      have hel : s1BTargets.elem j.val = true :=
        List.elem_eq_true_of_mem (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
      rw [hel, ite_eq_left rfl, Bool.xor_false]
    · simp only [↓reduceIte]
      unfold outVal102 sliceVal
      have hnot := sumBits_not 25 (fun k => if h : 0 + k < 100 then m0 ⟨0 + k, h⟩ else false)
      have heq : sumBits 25 (fun k => if h : 0 + k < 100 then
          (fun w : Fin 100 =>
            if s1BTargets.elem w.val then xor (m0 w) true else m0 w) ⟨0 + k, h⟩
          else false) =
          sumBits 25 (fun k => !(if h : 0 + k < 100 then m0 ⟨0 + k, h⟩ else false)) := by
        refine sumBits_congr fun k hk => ?_
        have hk102 : 0 + k < 100 := by omega
        have hel : s1BTargets.elem (0 + k) = true :=
          List.elem_eq_true_of_mem (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
        simp only [dite_eq_left hk102, hel, ↓reduceIte, Bool.xor_true]
      rw [heq]; omega

theorem exec_incYOps {incOps : List Op102} {ancW : List Nat}
    (hsub : (ancW.all (fun w => Nat.ble 50 w && Nat.blt w 100)) = true)
    (hcert : checkAdderRangeSpec incOps 25 24 false false [] ancW (.wire 49 false)
      (List.replicate 24 .zero) = true)
    {mB : Fin 100 → Bool}
    (hanc : ∀ i : Nat, (hi : i < 50) → mB ⟨50 + i, by omega⟩ = false) :
    ∃ m1 : Fin 100 → Bool,
      execList102 (s1YTargets.map (mkCX 49) ++ incOps) mB = some m1 ∧
      (∀ w : Fin 100, w.val < 25 → m1 w = mB w) ∧
      m1 ⟨49, by decide⟩ = mB ⟨49, by decide⟩ ∧
      (∀ i : Nat, (hi : i < 50) → m1 ⟨50 + i, by omega⟩ = false) ∧
      sliceVal 25 24 m1 =
        (if mB ⟨49, by decide⟩ then (16777216 - sliceVal 25 24 mB) % 16777216
         else sliceVal 25 24 mB) := by
  have hex_x := execList102_xorTargets (by decide : 49 < 100) s1YTargets mB (by decide) (by decide)
  set mX : Fin 100 → Bool :=
    fun w => if s1YTargets.elem w.val then xor (mB w) (mB ⟨49, by decide⟩) else mB w
  have hmX_anc : ∀ w : Fin 100, w.val ∈ ancW → mX w = false := by
    intro w hw
    have h1 := List.all_eq_true.mp hsub w.val hw
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h1
    have hnel : s1YTargets.elem w.val = false := by
      cases he : s1YTargets.elem w.val
      · rfl
      · have := mem_rangeList_iff.mp (List.mem_of_elem_eq_true he); omega
    dsimp only [mX]; rw [hnel, ite_eq_right Bool.false_ne_true]
    have := hanc (w.val - 50) (by omega)
    simpa [show 50 + (w.val - 50) = w.val by omega] using this
  obtain ⟨m1, hex_inc, hnon_inc, hsl_inc⟩ :=
    checkAdderRangeSpec_sound hcert (fun _ h => by cases h) hmX_anc
  rw [execList102_append, hex_x, Option.bind_some]
  refine ⟨m1, hex_inc, fun w hw => ?_, ?_, fun i hi => ?_, ?_⟩
  · rw [hnon_inc w (Or.inl hw)]
    have hnel : s1YTargets.elem w.val = false := by
      cases he : s1YTargets.elem w.val
      · rfl
      · have := mem_rangeList_iff.mp (List.mem_of_elem_eq_true he); omega
    dsimp only [mX]; rw [hnel, ite_eq_right Bool.false_ne_true]
  · rw [hnon_inc ⟨49, by decide⟩ (Or.inr (by decide))]
    simp [mX, s1YTargets, rangeList]
  · rw [hnon_inc ⟨50 + i, by omega⟩ (Or.inr (by dsimp only; omega))]
    have hnel : s1YTargets.elem (50 + i) = false := by
      cases he : s1YTargets.elem (50 + i)
      · rfl
      · have := mem_rangeList_iff.mp (List.mem_of_elem_eq_true he); omega
    dsimp only [mX]; rw [hnel, ite_eq_right Bool.false_ne_true]
    exact hanc i hi
  · simp only [Bool.false_eq_true, ↓reduceIte] at hsl_inc
    rw [hsl_inc, sumBits_replicate_zero]
    have hmX49 : mX ⟨49, by decide⟩ = mB ⟨49, by decide⟩ := by simp [mX, s1YTargets, rangeList]
    have hc0 : evalXWire mX (.wire 49 false) = mB ⟨49, by decide⟩ := by
      dsimp only [evalXWire]; rw [dite_eq_left (by decide), Bool.xor_false, hmX49]
    rw [hc0]
    cases hs : mB ⟨49, by decide⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, add_zero]
      have hmX_lo : sliceVal 25 24 mX = sliceVal 25 24 mB := by
        unfold sliceVal
        refine sumBits_congr fun k hk => ?_
        have hk102 : 25 + k < 100 := by omega
        have hel : s1YTargets.elem (25 + k) = true :=
          List.elem_eq_true_of_mem (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
        rw [dite_eq_left hk102, dite_eq_left hk102]
        dsimp only [mX]
        rw [hel, ite_eq_left rfl, hs, Bool.xor_false]
      have hlt24 : sliceVal 25 24 mB < 2 ^ 24 := sumBits_lt 24 _
      rw [hmX_lo, Nat.mod_eq_of_lt hlt24]
    · simp only [↓reduceIte, Bool.toNat_true, zero_add]
      have hmX_lo : sliceVal 25 24 mX = 16777215 - sliceVal 25 24 mB := by
        unfold sliceVal
        have hnot := sumBits_not 24 (fun k => if h : 25 + k < 100 then mB ⟨25 + k, h⟩ else false)
        have heq : sumBits 24 (fun k => if h : 25 + k < 100 then mX ⟨25 + k, h⟩ else false) =
                   sumBits 24 (fun k => !(if h : 25 + k < 100 then mB ⟨25 + k, h⟩ else false)) := by
          refine sumBits_congr fun k hk => ?_
          have hk102 : 25 + k < 100 := by omega
          have hel : s1YTargets.elem (25 + k) = true :=
            List.elem_eq_true_of_mem (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
          rw [dite_eq_left hk102, dite_eq_left hk102]
          dsimp only [mX]
          rw [hel, ite_eq_left rfl, hs, Bool.xor_true]
        rw [heq]; omega
      have hlo_lt : sliceVal 25 24 mB < 16777216 := sumBits_lt 24 _
      have hpow24 : (2 : Nat) ^ 24 = 16777216 := by decide
      rw [hmX_lo, hpow24]
      omega

def s1AddVal (u : Nat) : Nat :=
  if u.testBit 23 then
    sumBits 23 (fun k => xor (u.testBit k) (s1FlipBits48.elem k)) + 8388608
  else
    u % 8388608

theorem s1AddVal_of_lt {u : Nat} (hu : u < 8388608) : s1AddVal u = u := by
  unfold s1AddVal
  have htb : u.testBit 23 = false := Nat.testBit_eq_false_of_lt (by omega : u < 2 ^ 23)
  rw [htb, ite_eq_right Bool.false_ne_true, Nat.mod_eq_of_lt hu]

theorem s1AddVal_8388608 : s1AddVal 8388608 = 13176795 := by decide +kernel

theorem s1XLo_getElem? {k : Nat} (hk : k < 23) : s1XLo[k]? = some (.wire (25 + k) false) := by
  unfold s1XLo
  rw [List.getElem?_append_left (by simp [rangeList_length, hk]),
      List.getElem?_map, rangeList_getElem? hk]
  rfl

theorem sumBits_s1XLo (m1 : Fin 100 → Bool) :
    sumBits 25 (evalXWires m1 s1XLo) = sliceVal 25 23 m1 := by
  have h23 : evalXWires m1 s1XLo 23 = false := rfl
  have h24 : evalXWires m1 s1XLo 24 = false := rfl
  have h25 : sumBits 25 (evalXWires m1 s1XLo) = sumBits 23 (evalXWires m1 s1XLo) := by
    rw [sumBits_succ 24, sumBits_succ 23, h23, h24]
    rfl
  rw [h25]
  unfold sliceVal
  refine sumBits_congr fun k hk => ?_
  have hk102 : 25 + k < 100 := by omega
  rw [dite_eq_left hk102]
  unfold evalXWires
  rw [s1XLo_getElem? hk]
  dsimp only [evalXWire]
  rw [dite_eq_left hk102, Bool.xor_false]

theorem s1XHi_getElem? {k : Nat} (hk : k < 23) :
    s1XHi[k]? = some (.wire (25 + k) (s1FlipBits48.elem k)) := by
  unfold s1XHi
  rw [List.getElem?_append_left (by simp [rangeList_length, hk]),
      List.getElem?_map, rangeList_getElem? hk]
  simp

theorem sumBits_s1XHi (m1 : Fin 100 → Bool) :
    sumBits 25 (evalXWires m1 s1XHi) =
      sumBits 23 (fun k => xor ((sliceVal 25 24 m1).testBit k) (s1FlipBits48.elem k)) +
        8388608 := by
  have h23 : evalXWires m1 s1XHi 23 = true := rfl
  have h24 : evalXWires m1 s1XHi 24 = false := rfl
  rw [sumBits_succ 24, sumBits_succ 23, h23, h24]
  simp only [Bool.toNat_true, Bool.toNat_false, mul_one, mul_zero, add_zero]
  have hpow : (2 : Nat) ^ 23 = 8388608 := by decide
  rw [hpow]
  congr 1
  refine sumBits_congr fun k hk => ?_
  unfold evalXWires
  rw [s1XHi_getElem? hk]
  dsimp only [evalXWire]
  have hk102 : 25 + k < 100 := by omega
  rw [dite_eq_left hk102]
  have htb :=
    sumBits_testBit 24 (fun j => if h : 25 + j < 100 then m1 ⟨25 + j, h⟩ else false) k (by omega)
  change (sliceVal 25 24 m1).testBit k = _ at htb
  rw [dite_eq_left hk102] at htb
  rw [htb]

theorem exec_s1AddOps {m1 : Fin 100 → Bool}
    (hanc : ∀ i : Nat, (hi : i < 50) → m1 ⟨50 + i, by omega⟩ = false) :
    ∃ m1a : Fin 100 → Bool,
      execList102 s1AddOps m1 = some m1a ∧
      (∀ w : Fin 100, 25 ≤ w.val → m1a w = m1 w) ∧
      outVal102 m1a = (outVal102 m1 + s1AddVal (sliceVal 25 24 m1)) % 33554432 := by
  have hu_split :
      sliceVal 25 24 m1 = sliceVal 25 23 m1 + 8388608 * (m1 ⟨48, by decide⟩).toNat := by
    unfold sliceVal
    simp [sumBits]
  have hlo_lt : sliceVal 25 23 m1 < 8388608 := sumBits_lt 23 _
  have htb23 : (sliceVal 25 24 m1).testBit 23 = m1 ⟨48, by decide⟩ := by
    have h :=
      sumBits_testBit 24 (fun k => if h : 25 + k < 100 then m1 ⟨25 + k, h⟩ else false) 23
        (by decide)
    simpa [sliceVal] using h
  unfold s1AddVal
  rw [htb23]
  cases h48 : m1 ⟨48, by decide⟩
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hfalse : ∀ w : Fin 100, w.val ∈ ([48] ++ rangeList 50 24) → m1 w = false := by
      intro w hw
      rcases List.mem_cons.mp hw with hw48 | hmem
      · have hfin : w = ⟨48, by decide⟩ := Fin.ext hw48
        rwa [hfin]
      · have hr := mem_rangeList_iff.mp hmem
        have := hanc (w.val - 50) (by omega)
        simpa [show 50 + (w.val - 50) = w.val by omega] using this
    obtain ⟨m1a, hex, hge25, hout⟩ :=
      checkAdder25_raw_sound s1Add_lo_cert (fun _ h => by cases h) hfalse
    simp only [Bool.false_eq_true, ↓reduceIte, evalXWire, Bool.toNat_false, add_zero] at hout
    rw [sumBits_s1XLo m1] at hout
    rw [h48] at hu_split
    simp only [Bool.toNat_false, mul_zero, add_zero] at hu_split
    rw [hu_split, Nat.mod_eq_of_lt hlo_lt]
    exact ⟨m1a, hex, hge25, hout⟩
  · simp only [↓reduceIte]
    have htrue : ∀ w : Fin 100, w.val ∈ [48] → m1 w = true := by
      intro w hw
      rcases List.mem_singleton.mp hw with hw48
      have hfin : w = ⟨48, by decide⟩ := Fin.ext hw48
      rwa [hfin]
    have hfalse : ∀ w : Fin 100, w.val ∈ rangeList 50 24 → m1 w = false := by
      intro w hw
      have hr := mem_rangeList_iff.mp hw
      have := hanc (w.val - 50) (by omega)
      simpa [show 50 + (w.val - 50) = w.val by omega] using this
    obtain ⟨m1a, hex, hge25, hout⟩ :=
      checkAdder25_raw_sound s1Add_hi_cert htrue hfalse
    simp only [Bool.false_eq_true, ↓reduceIte, evalXWire, Bool.toNat_false, add_zero] at hout
    rw [sumBits_s1XHi m1] at hout
    exact ⟨m1a, hex, hge25, hout⟩

theorem exec_s1Ops {m0 : Fin 100 → Bool}
    (hanc : ∀ i : Nat, (hi : i < 50) → m0 ⟨50 + i, by omega⟩ = false) :
    ∃ mB m1 m1a : Fin 100 → Bool,
      execList102 s1BOps m0 = some mB ∧
      execList102 s1YOps mB = some m1 ∧
      execList102 s1AddOps m1 = some m1a ∧
      execList102 s1Ops m0 = some m1a ∧
      (∀ w : Fin 100, 25 ≤ w.val → mB w = m0 w) ∧
      (∀ w : Fin 100, 25 ≤ w.val → m1a w = m1 w) ∧
      m1 ⟨49, by decide⟩ = m0 ⟨49, by decide⟩ ∧
      (∀ i : Nat, (hi : i < 50) → m1 ⟨50 + i, by omega⟩ = false) ∧
      sliceVal 25 24 m1 = u24OfY (sliceVal 25 25 m0) ∧
      outVal102 m1a = ((if m0 ⟨49, by decide⟩ then 33554431 - outVal102 m0 else outVal102 m0) +
        s1AddVal (sliceVal 25 24 m1)) % 33554432 := by
  obtain ⟨mB, hexB, hmB_ge25, houtB⟩ := exec_s1BOps (m0 := m0)
  have hmB_anc : ∀ i : Nat, (hi : i < 50) → mB ⟨50 + i, by omega⟩ = false := by
    intro i hi; rw [hmB_ge25 ⟨50 + i, by omega⟩ (by dsimp only; omega)]; exact hanc i hi
  obtain ⟨m1, hexY, hm1_lt25, hm1_49, hm1_anc, hm1_u24⟩ :=
    exec_incYOps (by decide) s1IncOps_cert hmB_anc
  change execList102 s1YOps mB = some m1 at hexY
  have hmB_49 : mB ⟨49, by decide⟩ = m0 ⟨49, by decide⟩ := hmB_ge25 ⟨49, by decide⟩ (by decide)
  have hmB_lo : sliceVal 25 24 mB = sliceVal 25 24 m0 := by
    unfold sliceVal
    refine sumBits_congr fun k hk => ?_
    have hk102 : 25 + k < 100 := by omega
    rw [dite_eq_left hk102, dite_eq_left hk102]
    exact hmB_ge25 ⟨25 + k, hk102⟩ (by dsimp only; omega)
  have hy_split :
      sliceVal 25 25 m0 = sliceVal 25 24 m0 + 16777216 * (m0 ⟨49, by decide⟩).toNat := by
    unfold sliceVal
    simp [sumBits]
  have hy24_tb : (sliceVal 25 25 m0).testBit 24 = m0 ⟨49, by decide⟩ := by
    have hlo : sliceVal 25 24 m0 < 16777216 := sumBits_lt 24 _
    rw [Nat.testBit_eq_decide_div_mod_eq]
    change decide (sliceVal 25 25 m0 / 16777216 % 2 = 1) = m0 ⟨49, by decide⟩
    cases hb : m0 ⟨49, by decide⟩
    · rw [hb] at hy_split
      simp only [Bool.toNat_false, mul_zero, add_zero] at hy_split
      have : sliceVal 25 25 m0 / 16777216 = 0 := by omega
      rw [this]; decide
    · rw [hb] at hy_split
      simp only [Bool.toNat_true, mul_one] at hy_split
      have : sliceVal 25 25 m0 / 16777216 = 1 := by omega
      rw [this]; decide
  have hu24_eq :
      (if mB ⟨49, by decide⟩ then (16777216 - sliceVal 25 24 mB) % 16777216
       else sliceVal 25 24 mB) =
      u24OfY (sliceVal 25 25 m0) := by
    rw [hmB_49, hmB_lo]
    unfold u24OfY
    rw [hy24_tb]
    have hlo : sliceVal 25 24 m0 < 16777216 := sumBits_lt 24 _
    cases hb : m0 ⟨49, by decide⟩
    · rw [hb] at hy_split
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, mul_zero,
        add_zero] at hy_split ⊢
      rw [hy_split]
    · rw [hb] at hy_split; simp only [↓reduceIte, Bool.toNat_true, mul_one] at hy_split ⊢
      have hsub : 33554432 - (sliceVal 25 24 m0 + 16777216) =
          16777216 - sliceVal 25 24 m0 := by
        omega
      rw [hy_split, hsub]
  rw [hu24_eq] at hm1_u24
  obtain ⟨m1a, hexA, hm1a_ge25, houtA⟩ := exec_s1AddOps hm1_anc
  have hout1 : outVal102 m1 = outVal102 mB := outVal102_congr hm1_lt25
  refine ⟨mB, m1, m1a, hexB, hexY, hexA, ?_, hmB_ge25, hm1a_ge25,
    hm1_49.trans hmB_49, hm1_anc, hm1_u24, ?_⟩
  · unfold s1Ops
    rw [List.append_assoc, execList102_append, hexB, Option.bind_some,
        execList102_append, hexY, Option.bind_some, hexA]
  · rw [houtA, hout1, houtB]

theorem neg24_invol {v : Nat} (hv : v < 16777216) :
    (16777216 - (16777216 - v) % 16777216) % 16777216 = v := by
  by_cases hv0 : v = 0
  · subst hv0; decide
  · rw [Nat.mod_eq_of_lt (by omega : 16777216 - v < 16777216),
        show 16777216 - (16777216 - v) = v by omega,
        Nat.mod_eq_of_lt hv]

theorem exec_s7Ops {m0 mB m1 m6c : Fin 100 → Bool}
    (hanc0 : ∀ i : Nat, (hi : i < 50) → m0 ⟨50 + i, by omega⟩ = false)
    (hmB_ge25 : ∀ w : Fin 100, 25 ≤ w.val → mB w = m0 w)
    (hexY : execList102 s1YOps mB = some m1)
    (hm6c_ge25 : ∀ w : Fin 100, 25 ≤ w.val → m6c w = m1 w) :
    ∃ m7 : Fin 100 → Bool,
      execList102 s7Ops m6c = some m7 ∧
      (∀ w : Fin 100, 25 ≤ w.val → m7 w = m0 w) ∧
      outVal102 m7 = if m0 ⟨49, by decide⟩ then 33554431 - outVal102 m6c else outVal102 m6c := by
  have hmB_anc : ∀ i : Nat, (hi : i < 50) → mB ⟨50 + i, by omega⟩ = false := by
    intro i hi; rw [hmB_ge25 ⟨50 + i, by omega⟩ (by dsimp only; omega)]; exact hanc0 i hi
  obtain ⟨m1', hexY', _, hm1'_49, hm1'_anc, hm1'_u24⟩ :=
    exec_incYOps (by decide) s1IncOps_cert hmB_anc
  change execList102 s1YOps mB = some m1' at hexY'
  have hm1_eq : m1' = m1 := Option.some.inj (hexY'.symm.trans hexY)
  subst hm1_eq
  have hm6c_anc : ∀ i : Nat, (hi : i < 50) → m6c ⟨50 + i, by omega⟩ = false := by
    intro i hi; rw [hm6c_ge25 ⟨50 + i, by omega⟩ (by dsimp only; omega)]; exact hm1'_anc i hi
  obtain ⟨m7y, hex7Y, hm7y_lt25, hm7y_49, hm7y_anc, hm7y_u24⟩ :=
    exec_incYOps (by decide) s7IncOps_cert hm6c_anc
  change execList102 s7YOps m6c = some m7y at hex7Y
  have hm6c_lo : sliceVal 25 24 m6c = sliceVal 25 24 m1' := by
    unfold sliceVal
    refine sumBits_congr fun k hk => ?_
    have hk102 : 25 + k < 100 := by omega
    rw [dite_eq_left hk102, dite_eq_left hk102]
    exact hm6c_ge25 ⟨25 + k, hk102⟩ (by dsimp only; omega)
  have hmB_lo : sliceVal 25 24 mB = sliceVal 25 24 m0 := by
    unfold sliceVal
    refine sumBits_congr fun k hk => ?_
    have hk102 : 25 + k < 100 := by omega
    rw [dite_eq_left hk102, dite_eq_left hk102]
    exact hmB_ge25 ⟨25 + k, hk102⟩ (by dsimp only; omega)
  have hm6c_49 : m6c ⟨49, by decide⟩ = m0 ⟨49, by decide⟩ :=
    (hm6c_ge25 ⟨49, by decide⟩ (by decide)).trans
      (hm1'_49.trans (hmB_ge25 ⟨49, by decide⟩ (by decide)))
  have hmB_49 : mB ⟨49, by decide⟩ = m0 ⟨49, by decide⟩ := hmB_ge25 ⟨49, by decide⟩ (by decide)
  have hm7y_lo_eq : sliceVal 25 24 m7y = sliceVal 25 24 m0 := by
    rw [hm7y_u24, hm6c_49, hm6c_lo, hm1'_u24, hmB_49, hmB_lo]
    cases m0 ⟨49, by decide⟩
    · rfl
    · simp only [↓reduceIte]
      exact neg24_invol (sumBits_lt 24 _)
  have hm7y_ge25 : ∀ w : Fin 100, 25 ≤ w.val → m7y w = m0 w := by
    intro w hw
    by_cases hw49 : w.val < 49
    · have hi : w.val - 25 < 24 := by omega
      have htb1 := sumBits_testBit 24
        (fun k => if h : 25 + k < 100 then m7y ⟨25 + k, h⟩ else false) (w.val - 25) hi
      have htb0 := sumBits_testBit 24
        (fun k => if h : 25 + k < 100 then m0 ⟨25 + k, h⟩ else false) (w.val - 25) hi
      change (sliceVal 25 24 m7y).testBit (w.val - 25) = _ at htb1
      change (sliceVal 25 24 m0).testBit (w.val - 25) = _ at htb0
      rw [dite_eq_left (by omega)] at htb1 htb0
      have hfin : (⟨25 + (w.val - 25), by omega⟩ : Fin 100) = w := Fin.ext (by dsimp; omega)
      rw [hfin] at htb1 htb0
      rw [← htb1, hm7y_lo_eq, htb0]
    · by_cases hw_eq49 : w.val = 49
      · have hfin : w = ⟨49, by decide⟩ := Fin.ext hw_eq49
        rw [hfin, hm7y_49, hm6c_49]
      · have hi : w.val - 50 < 50 := by omega
        have hfin : (⟨50 + (w.val - 50), by omega⟩ : Fin 100) = w := Fin.ext (by dsimp; omega)
        rw [← hfin, hm7y_anc (w.val - 50) hi, hanc0 (w.val - 50) hi]
  obtain ⟨m7, hex7B, hm7_ge25, hout7⟩ := exec_s1BOps (m0 := m7y)
  have hm7y_out : outVal102 m7y = outVal102 m6c := outVal102_congr hm7y_lt25
  have hm7y_49_eq : m7y ⟨49, by decide⟩ = m0 ⟨49, by decide⟩ :=
    hm7y_ge25 ⟨49, by decide⟩ (by decide)
  refine ⟨m7, ?_, fun w hw => (hm7_ge25 w hw).trans (hm7y_ge25 w hw), ?_⟩
  · unfold s7Ops
    rw [execList102_append, hex7Y, Option.bind_some, hex7B]
  · rw [hout7, hm7y_49_eq, hm7y_out]


-- ============================================================================
-- Section 2: 8 Unboxed 56-Bit Slices & Stages 2a, 2b, 2c, 3a, 3b, 5.2Post, 5.4, 6a, 6b, 6c
-- ============================================================================

def bHi19Wires : List Nat :=
  [57, 60, 59, 61, 53, 52, 56, 55, 54, 51, 50, 62, 63, 64, 65, 66, 67, 68, 69]
def k15Wires : List Nat := rangeList 72 15
def l7Wires : List Nat := rangeList 87 7
def clean53Wires : List Nat :=
  [50, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 72,
   73, 74, 75, 76, 77, 78, 79, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99]
def s52KeepWires : List Nat :=
  [41, 42, 43, 44, 45, 46, 47, 48, 58, 70, 71, 80, 81, 82, 83, 84, 85, 86]
def s41KeepWires : List Nat :=
  (rangeList 41 59).filter (fun q => !([49, 52, 69, 70, 71, 81, 85, 86].elem q))

def tr41pOf (tr3b : WTree) : WTree :=
  wSet (wSet (wSet (wSet tr3b 86 0) 81 (wGet tr3b 81 ^^^ wGet tr3b 85)) 85 0) 52 0

def s2bPrunedKs : List Nat := [0, 1, 2, 4, 5, 6, 7, 21]

def s2bSrc (s4 k : Nat) : Nat :=
  if Nat.ble 8 s4 && s2bPrunedKs.elem k then (50 - k - s4) % 22
  else (k + 22 - s4) % 22

def s6bSrc (s4 j : Nat) : Nat :=
  ((rangeList 0 22).find? (fun k => Nat.beq (s2bSrc s4 k) j)).getD 0

theorem s2bSrc_lt {s4 k : Nat} : s2bSrc s4 k < 22 := by
  unfold s2bSrc
  split_ifs <;> exact Nat.mod_lt _ (by decide)

theorem s2bSrc_s6bSrc_cert :
    ((rangeList 0 16).all fun s4 =>
      (rangeList 0 22).all fun j =>
        Nat.blt (s6bSrc s4 j) 22 && Nat.beq (s2bSrc s4 (s6bSrc s4 j)) j) = true := by
  decide +kernel

theorem s6bSrc_spec {s4 j : Nat} (hs4 : s4 < 16) (hj : j < 22) :
    s6bSrc s4 j < 22 ∧ s2bSrc s4 (s6bSrc s4 j) = j := by
  have h1 := List.all_eq_true.mp s2bSrc_s6bSrc_cert s4 (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
  have h2 := List.all_eq_true.mp h1 j (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h2
  exact h2

def s4Wires2b : List Nat := [50, 51, 52, 53]
def s4Wires6b : List Nat := [72, 69, 70, 71]

def s4TrueW (ws : List Nat) (s4 : Nat) : List Nat :=
  (if s4.testBit 0 then [ws.getD 0 0] else []) ++
  (if s4.testBit 1 then [ws.getD 1 0] else []) ++
  (if s4.testBit 2 then [ws.getD 2 0] else []) ++
  (if s4.testBit 3 then [ws.getD 3 0] else [])

def s4FalseW (ws : List Nat) (s4 : Nat) : List Nat :=
  (if s4.testBit 0 then [] else [ws.getD 0 0]) ++
  (if s4.testBit 1 then [] else [ws.getD 1 0]) ++
  (if s4.testBit 2 then [] else [ws.getD 2 0]) ++
  (if s4.testBit 3 then [] else [ws.getD 3 0]) ++ [62]

def s4TrueW2b (s4 : Nat) : List Nat := s4TrueW s4Wires2b s4
def s4FalseW2b (s4 : Nat) : List Nat := s4FalseW s4Wires2b s4
def targets2b (s4 : Nat) : List XWire :=
  (rangeList 0 22).map (fun k => .wire (25 + s2bSrc s4 k) false)

def s4TrueW6b (s4 : Nat) : List Nat := s4TrueW s4Wires6b s4
def s4FalseW6b (s4 : Nat) : List Nat := s4FalseW s4Wires6b s4
def targets6b (s4 : Nat) : List XWire :=
  (rangeList 0 22).map (fun j => .wire (25 + s6bSrc s4 j) false)

theorem s2b_cert_0 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 0) (s4FalseW2b 0) (targets2b 0) = true := by
  decide +kernel
theorem s2b_cert_1 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 1) (s4FalseW2b 1) (targets2b 1) = true := by
  decide +kernel
theorem s2b_cert_2 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 2) (s4FalseW2b 2) (targets2b 2) = true := by
  decide +kernel
theorem s2b_cert_3 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 3) (s4FalseW2b 3) (targets2b 3) = true := by
  decide +kernel
theorem s2b_cert_4 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 4) (s4FalseW2b 4) (targets2b 4) = true := by
  decide +kernel
theorem s2b_cert_5 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 5) (s4FalseW2b 5) (targets2b 5) = true := by
  decide +kernel
theorem s2b_cert_6 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 6) (s4FalseW2b 6) (targets2b 6) = true := by
  decide +kernel
theorem s2b_cert_7 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 7) (s4FalseW2b 7) (targets2b 7) = true := by
  decide +kernel
theorem s2b_cert_8 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 8) (s4FalseW2b 8) (targets2b 8) = true := by
  decide +kernel
theorem s2b_cert_9 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 9) (s4FalseW2b 9) (targets2b 9) = true := by
  decide +kernel
theorem s2b_cert_10 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 10) (s4FalseW2b 10) (targets2b 10) = true := by
  decide +kernel
theorem s2b_cert_11 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 11) (s4FalseW2b 11) (targets2b 11) = true := by
  decide +kernel
theorem s2b_cert_12 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 12) (s4FalseW2b 12) (targets2b 12) = true := by
  decide +kernel
theorem s2b_cert_13 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 13) (s4FalseW2b 13) (targets2b 13) = true := by
  decide +kernel
theorem s2b_cert_14 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 14) (s4FalseW2b 14) (targets2b 14) = true := by
  decide +kernel
theorem s2b_cert_15 :
    checkPermSpec s2bOps 25 22 (s4TrueW2b 15) (s4FalseW2b 15) (targets2b 15) = true := by
  decide +kernel

theorem s2b_cert {s4 : Nat} (hs4 : s4 < 16) :
    checkPermSpec s2bOps 25 22 (s4TrueW2b s4) (s4FalseW2b s4) (targets2b s4) = true := by
  rcases (by omega : s4 = 0 ∨ s4 = 1 ∨ s4 = 2 ∨ s4 = 3 ∨ s4 = 4 ∨ s4 = 5 ∨ s4 = 6 ∨ s4 = 7 ∨
    s4 = 8 ∨ s4 = 9 ∨ s4 = 10 ∨ s4 = 11 ∨ s4 = 12 ∨ s4 = 13 ∨ s4 = 14 ∨ s4 = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s2b_cert_0
  · exact s2b_cert_1
  · exact s2b_cert_2
  · exact s2b_cert_3
  · exact s2b_cert_4
  · exact s2b_cert_5
  · exact s2b_cert_6
  · exact s2b_cert_7
  · exact s2b_cert_8
  · exact s2b_cert_9
  · exact s2b_cert_10
  · exact s2b_cert_11
  · exact s2b_cert_12
  · exact s2b_cert_13
  · exact s2b_cert_14
  · exact s2b_cert_15

theorem s6b_cert_0 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 0) (s4FalseW6b 0) (targets6b 0) = true := by
  decide +kernel
theorem s6b_cert_1 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 1) (s4FalseW6b 1) (targets6b 1) = true := by
  decide +kernel
theorem s6b_cert_2 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 2) (s4FalseW6b 2) (targets6b 2) = true := by
  decide +kernel
theorem s6b_cert_3 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 3) (s4FalseW6b 3) (targets6b 3) = true := by
  decide +kernel
theorem s6b_cert_4 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 4) (s4FalseW6b 4) (targets6b 4) = true := by
  decide +kernel
theorem s6b_cert_5 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 5) (s4FalseW6b 5) (targets6b 5) = true := by
  decide +kernel
theorem s6b_cert_6 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 6) (s4FalseW6b 6) (targets6b 6) = true := by
  decide +kernel
theorem s6b_cert_7 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 7) (s4FalseW6b 7) (targets6b 7) = true := by
  decide +kernel
theorem s6b_cert_8 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 8) (s4FalseW6b 8) (targets6b 8) = true := by
  decide +kernel
theorem s6b_cert_9 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 9) (s4FalseW6b 9) (targets6b 9) = true := by
  decide +kernel
theorem s6b_cert_10 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 10) (s4FalseW6b 10) (targets6b 10) = true := by
  decide +kernel
theorem s6b_cert_11 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 11) (s4FalseW6b 11) (targets6b 11) = true := by
  decide +kernel
theorem s6b_cert_12 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 12) (s4FalseW6b 12) (targets6b 12) = true := by
  decide +kernel
theorem s6b_cert_13 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 13) (s4FalseW6b 13) (targets6b 13) = true := by
  decide +kernel
theorem s6b_cert_14 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 14) (s4FalseW6b 14) (targets6b 14) = true := by
  decide +kernel
theorem s6b_cert_15 :
    checkPermSpec s6bOps 25 22 (s4TrueW6b 15) (s4FalseW6b 15) (targets6b 15) = true := by
  decide +kernel

theorem s6b_cert {s4 : Nat} (hs4 : s4 < 16) :
    checkPermSpec s6bOps 25 22 (s4TrueW6b s4) (s4FalseW6b s4) (targets6b s4) = true := by
  rcases (by omega : s4 = 0 ∨ s4 = 1 ∨ s4 = 2 ∨ s4 = 3 ∨ s4 = 4 ∨ s4 = 5 ∨ s4 = 6 ∨ s4 = 7 ∨
    s4 = 8 ∨ s4 = 9 ∨ s4 = 10 ∨ s4 = 11 ∨ s4 = 12 ∨ s4 = 13 ∨ s4 = 14 ∨ s4 = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s6b_cert_0
  · exact s6b_cert_1
  · exact s6b_cert_2
  · exact s6b_cert_3
  · exact s6b_cert_4
  · exact s6b_cert_5
  · exact s6b_cert_6
  · exact s6b_cert_7
  · exact s6b_cert_8
  · exact s6b_cert_9
  · exact s6b_cert_10
  · exact s6b_cert_11
  · exact s6b_cert_12
  · exact s6b_cert_13
  · exact s6b_cert_14
  · exact s6b_cert_15


def allMSlice (s : Nat) : Nat :=
  [allM_0, allM_1, allM_2, allM_3, allM_4, allM_5, allM_6, allM_7].getD s 0

def fMaskInitSlice (s i : Nat) : Nat :=
  ([fMaskInitList_0, fMaskInitList_1, fMaskInitList_2, fMaskInitList_3,
    fMaskInitList_4, fMaskInitList_5, fMaskInitList_6, fMaskInitList_7].getD s []).getD i 0

def fMaskRotSlice (s i : Nat) : Nat :=
  if i < 16 then allMSlice s else 0

-- Fast O(N) Cube Word Packer:
def packCubeBit {α : Type} (f : α → Bool) : List α → Nat
  | [] => 0
  | e :: rest => (cond (f e) 1 0) + 2 * packCubeBit f rest

theorem packCubeBit_testBit {α : Type} (f : α → Bool) :
    ∀ (cs : List α) (bit : Nat) (e : α),
      cs[bit]? = some e → (packCubeBit f cs).testBit bit = f e
  | [], _, _, h => by cases h
  | e0 :: rest, 0, e, h => by
    dsimp only [List.getElem?_cons_zero] at h
    injection h with he; subst he
    dsimp only [packCubeBit]
    have hmod : ((cond (f e0) 1 0) + 2 * packCubeBit f rest) % 2 = cond (f e0) 1 0 := by
      cases f e0 <;> dsimp only [cond] <;> omega
    rw [Nat.testBit_zero, hmod]
    cases f e0 <;> rfl
  | e0 :: rest, bit + 1, e, h => by
    dsimp only [List.getElem?_cons_succ] at h
    dsimp only [packCubeBit]
    have hdiv : ((cond (f e0) 1 0) + 2 * packCubeBit f rest) / 2 = packCubeBit f rest := by
      cases f e0 <;> dsimp only [cond] <;> omega
    rw [Nat.testBit_succ, hdiv]
    exact packCubeBit_testBit f rest bit e h

def checkCubeScalar (e : Nat × Nat × Nat × Nat) : Bool :=
  let (us, ue, w, s4) := e
  Nat.beq ue (us + Nat.shiftLeft 1 w) &&
  Nat.ble w 22 &&
  Nat.blt s4 16 &&
  Nat.beq (us % Nat.shiftLeft 1 w) 0 &&
  ((rangeList 0 16).all fun k =>
    let src := s2bSrc s4 k
    let rsrc := uRotSrc s4 k
    Nat.beq src rsrc ||
      (Nat.ble w src && Nat.ble w rsrc && (us.testBit src == us.testBit rsrc))) &&
  ((rangeList 16 6).all fun k => Nat.ble w (s2bSrc s4 k))

def checkPartition4 (cur end_ : Nat) : List (Nat × Nat × Nat × Nat) → Bool
  | [] => Nat.beq cur end_
  | (us, ue, _, _) :: rest =>
      cond (Nat.beq cur us && Nat.blt us ue)
        (checkPartition4 ue end_ rest) false

def checkCubeSlice (start end_ : Nat) (cs : List (Nat × Nat × Nat × Nat))
    (allM : Nat) (fmList : List Nat) (tr0 tr2a tr2b tr6a : WTree) : Bool :=
  checkWTreeWF 7 tr0 &&
  Nat.beq allM (Nat.shiftLeft 1 cs.length - 1) &&
  checkZeroList tr0 zAnc52 &&
  checkPartition4 start end_ cs &&
  cs.all checkCubeScalar &&
  ((rangeList 0 24).all fun i =>
    Nat.beq (fmList.getD i 0) (packCubeBit (fun (_, _, w, _) => Nat.blt i w) cs) &&
    Nat.beq (wGet tr0 (25 + i))
      (packCubeBit (fun (us, _, w, _) => if Nat.blt i w then false else us.testBit i) cs)) &&
  ((rangeList 0 4).all fun b =>
    let expW := packCubeBit (fun (_, _, _, s4) => s4.testBit b) cs
    Nat.beq (wGet tr2a (s4Wires2b.getD b 0)) expW &&
    Nat.beq (wGet tr6a (s4Wires6b.getD b 0)) expW) &&
  ((rangeList 16 6).all fun k =>
    Nat.beq (wGet tr2b (25 + k))
      (packCubeBit (fun (us, _, _, s4) => us.testBit (s2bSrc s4 k)) cs))

def checkTrS54In (allM : Nat) (tr3b tr52 tr54 : WTree) : Bool :=
  let h1 := wGet tr3b 45
  let h2 := wGet tr3b 46
  let h3 := wGet tr3b 48
  let h4 := wGet tr3b 58
  let h5 := wGet tr3b 47
  let t24 := h2 &&& h4
  let t34 := h3 &&& h4
  let t25 := h2 &&& h5
  let t35 := h3 &&& h5
  let t45 := h4 &&& h5
  let t245 := h2 &&& t45
  let p12 := h1 &&& (t45 ^^^ t245)
  let exp47 := h2 ^^^ h3 ^^^ h5
  let exp69 := h2 ^^^ h5 ^^^ wGet tr3b 41 ^^^ h1 ^^^ wGet tr3b 72 ^^^ wGet tr3b 75 ^^^
               wGet tr3b 77 ^^^ wGet tr3b 78 ^^^ wGet tr3b 86 ^^^ wGet tr3b 89 ^^^ wGet tr3b 93
  let exp52 := (t25 ^^^ t35 ^^^ t45) ^^^
    (h1 &&& (allM ^^^ h2 ^^^ h3 ^^^ t24 ^^^ t34 ^^^ h5 ^^^ t25 ^^^ t35 ^^^ t45))
  let exp97 := allM ^^^ h3 ^^^ h4 ^^^ t24 ^^^ t34 ^^^ t45
  let exp72 := allM ^^^ h3 ^^^ t45 ^^^ t245 ^^^ p12
  let exp56 := allM ^^^ h3 ^^^ h4 ^^^ t245 ^^^ p12
  let exp98 := allM ^^^ h3 ^^^ h4 ^^^ t34 ^^^ h5 ^^^ t45
  let exp99 := allM ^^^ h3 ^^^ h4 ^^^ t34 ^^^ h5 ^^^ t35 ^^^ t45
  let modW := [47, 69, 52, 97, 72, 56, 98, 99]
  let keepW := (rangeList 41 8 ++ rangeList 50 50).filter (fun w => !modW.elem w)
  checkWTreeWF 7 tr54 &&
  checkEqList tr54 modW [exp47, exp69, exp52, exp97, exp72, exp56, exp98, exp99] &&
  checkEqList tr54 keepW (keepW.map (wGet tr52))

theorem s3bAdd_cert :
    checkAdderRangeSpec s3bAddOps 0 25 false false []
      [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90, 94, 95, 96, 97, 98]
      .zero
      (bHi19Wires.map (fun w => .wire w false) ++ List.replicate 6 .zero) = true := by
  decide +kernel


def s2aPre : List Op102 :=
  [mkAnd 47 46 61, mkCX 45 44, mkAnd 61 44 60, mkCX 45 44, mkCX 61 60,
   mkAnd 60 44 59, mkCX 61 60, mkCX 59 60, mkAnd 59 43 58, mkAnd 58 42 57]
def s2aG2New : List Op102 :=
  [mkCX 41 40, mkAnd 57 40 55, mkCX 41 40, mkCX 57 55, mkAnd 55 40 56, mkCX 57 55, mkCX 56 55]
def s2aG2Cert : List Op102 :=
  [mkAnd 57 41 63, mkCX 57 63, mkAnd 63 40 55, mkCX 57 63, mkAnd 63 40 56,
   mkCX 63 55, mkUnand 57 41 63]
def s2aPost : List Op102 :=
  [mkAnd 56 39 64, mkAnd 64 38 53, mkAnd 53 37 65, mkAnd 65 36 54, mkAnd 54 35 66,
   mkAnd 66 34 67, mkAnd 67 33 52, mkAnd 52 32 68, mkAnd 68 31 51, mkAnd 51 30 50,
   mkCX 64 50, mkCX 65 50, mkCX 67 50, mkCX 68 50, mkCX 66 51,
   mkUnand 52 32 68, mkUnand 66 34 67, mkUnand 54 35 66, mkUnand 53 37 65, mkUnand 56 39 64,
   mkCX 61 59, mkCX 61 58, mkCX 61 57, mkCX 61 56, mkCX 61 55, mkCX 61 54,
   mkCX 61 52, mkCX 61 51, mkCX 60 58, mkCX 60 57, mkCX 60 55, mkCX 60 54,
   mkCX 60 52, mkCX 60 51, mkCX 60 50, mkCX 59 61, mkCX 59 57, mkCX 59 50,
   mkCX 58 60, mkCX 58 59, mkCX 58 57, mkCX 58 56, mkCX 58 54, mkCX 58 52,
   mkCX 58 51, mkCX 57 61, mkCX 57 60, mkCX 57 59, mkCX 57 55, mkCX 57 50,
   mkCX 55 61, mkCX 55 58, mkCX 55 56, mkCX 55 51, mkCX 55 50, mkCX 56 61,
   mkCX 56 58, mkCX 56 51, mkCX 53 57, mkCX 53 54, mkCX 53 52, mkCX 54 57,
   mkCX 54 56, mkCX 54 55, mkCX 52 56, mkCX 52 55, mkCX 52 54, mkCX 52 51,
   mkCX 51 56, mkCX 51 50, mkCX 50 55, mkCX 47 50, mkCX 47 57]
def s2aCertOps : List Op102 := s2aPre ++ s2aG2Cert ++ s2aPost

theorem s2aOps_eq_parts : s2aOps = s2aPre ++ s2aG2New ++ s2aPost := rfl

theorem exec_mkCX_step {c t : Nat} (hc : c < 100 ∧ t < 100 ∧ c ≠ t) (m : Fin 100 → Bool) :
    execOp102 m (mkCX c t) =
      some (Function.update m ⟨t, hc.2.1⟩ (xor (m ⟨t, hc.2.1⟩) (m ⟨c, hc.1⟩))) := by
  dsimp only [execOp102, mkCX]; rw [dite_eq_left hc]

theorem exec_mkAnd_step {c1 c2 t : Nat}
    (hc : c1 < 100 ∧ c2 < 100 ∧ t < 100 ∧ c1 ≠ c2 ∧ c1 ≠ t ∧ c2 ≠ t) (m : Fin 100 → Bool) :
    execOp102 m (mkAnd c1 c2 t) =
      if m ⟨t, hc.2.2.1⟩ = false then
        some (Function.update m ⟨t, hc.2.2.1⟩ (m ⟨c1, hc.1⟩ && m ⟨c2, hc.2.1⟩))
      else none := by
  dsimp only [execOp102, mkAnd]; rw [dite_eq_left hc]

theorem exec_mkUnand_step {c1 c2 t : Nat}
    (hc : c1 < 100 ∧ c2 < 100 ∧ t < 100 ∧ c1 ≠ c2 ∧ c1 ≠ t ∧ c2 ≠ t) (m : Fin 100 → Bool) :
    execOp102 m (mkUnand c1 c2 t) =
      if m ⟨t, hc.2.2.1⟩ = (m ⟨c1, hc.1⟩ && m ⟨c2, hc.2.1⟩) then
        some (Function.update m ⟨t, hc.2.2.1⟩ false)
      else none := by
  dsimp only [execOp102, mkUnand]; rw [dite_eq_left hc]

theorem g2_bool_55 (b40 b41 b57 : Bool) :
    xor (xor (xor (b57 && xor b40 b41) b57) b57)
        ((xor (b57 && xor b40 b41) b57) && xor (xor b40 b41) b41) =
      xor ((xor (b57 && b41) b57) && b40) (xor (xor (b57 && b41) b57) b57) := by
  cases b40 <;> cases b41 <;> cases b57 <;> rfl

theorem g2_bool_56 (b40 b41 b57 : Bool) :
    ((xor (b57 && xor b40 b41) b57) && xor (xor b40 b41) b41) =
      ((xor (xor (b57 && b41) b57) b57) && b40) := by
  cases b40 <;> cases b41 <;> cases b57 <;> rfl

theorem g2_bool_40 (b40 b41 : Bool) :
    xor (xor b40 b41) b41 = b40 := by
  cases b40 <;> cases b41 <;> rfl

theorem exec_s2aG2_cert_to_new {m m' : Fin 100 → Bool}
    (h : execList102 s2aG2Cert m = some m') :
    execList102 s2aG2New m = some m' := by
  set w40 : Fin 100 := ⟨40, by decide⟩
  set w41 : Fin 100 := ⟨41, by decide⟩
  set w55 : Fin 100 := ⟨55, by decide⟩
  set w56 : Fin 100 := ⟨56, by decide⟩
  set w57 : Fin 100 := ⟨57, by decide⟩
  set w63 : Fin 100 := ⟨63, by decide⟩
  set b40 := m w40
  set b41 := m w41
  set b57 := m w57
  dsimp only [s2aG2Cert, execList102] at h
  rw [exec_mkAnd_step (by decide)] at h
  have h63 : m w63 = false := by
    by_contra hne; rw [ite_eq_right hne] at h; cases h
  rw [ite_eq_left h63] at h; dsimp only at h
  set v1 := b57 && b41
  set m1 := Function.update m w63 v1
  rw [exec_mkCX_step (by decide)] at h; dsimp only at h
  have hm1_63 : m1 w63 = v1 := Function.update_self ..
  have hm1_57 : m1 w57 = b57 := Function.update_of_ne (by decide) ..
  rw [hm1_63, hm1_57] at h
  set v2 := xor v1 b57
  set m2 := Function.update m1 w63 v2
  rw [exec_mkAnd_step (by decide)] at h
  have hm2_55_eq : m2 w55 = m w55 := by
    simp only [m2, m1, Function.update_of_ne (by decide : w55 ≠ w63)]
  have h55 : m w55 = false := by
    by_contra hne; rw [hm2_55_eq, ite_eq_right hne] at h; cases h
  rw [hm2_55_eq, ite_eq_left h55] at h; dsimp only at h
  have hm2_63 : m2 w63 = v2 := Function.update_self ..
  have hm2_40 : m2 w40 = b40 := by
    dsimp only [m2]; rw [Function.update_of_ne (by decide : w40 ≠ w63)]
    dsimp only [m1]; rw [Function.update_of_ne (by decide : w40 ≠ w63)]
  rw [hm2_63, hm2_40] at h
  set v3 := v2 && b40
  set m3 := Function.update m2 w55 v3
  rw [exec_mkCX_step (by decide)] at h; dsimp only at h
  have hm3_63 : m3 w63 = v2 := by
    simp only [m3, Function.update_of_ne (by decide : w63 ≠ w55), hm2_63]
  have hm3_57 : m3 w57 = b57 := by
    dsimp only [m3]; rw [Function.update_of_ne (by decide : w57 ≠ w55)]
    dsimp only [m2]; rw [Function.update_of_ne (by decide : w57 ≠ w63)]
    exact hm1_57
  rw [hm3_63, hm3_57] at h
  set v4 := xor v2 b57
  set m4 := Function.update m3 w63 v4
  rw [exec_mkAnd_step (by decide)] at h
  have hm4_56_eq : m4 w56 = m w56 := by
    simp only [m4, m3, m2, m1,
      Function.update_of_ne (by decide : w56 ≠ w63),
      Function.update_of_ne (by decide : w56 ≠ w55)]
  have h56 : m w56 = false := by
    by_contra hne; rw [hm4_56_eq, ite_eq_right hne] at h; cases h
  rw [hm4_56_eq, ite_eq_left h56] at h; dsimp only at h
  have hm4_63 : m4 w63 = v4 := Function.update_self ..
  have hm4_40 : m4 w40 = b40 := by
    simp only [m4, m3,
      Function.update_of_ne (by decide : w40 ≠ w63),
      Function.update_of_ne (by decide : w40 ≠ w55), hm2_40]
  rw [hm4_63, hm4_40] at h
  set v5 := v4 && b40
  set m5 := Function.update m4 w56 v5
  rw [exec_mkCX_step (by decide)] at h; dsimp only at h
  have hm5_55 : m5 w55 = v3 := by
    simp only [m5, m4, m3,
      Function.update_of_ne (by decide : w55 ≠ w56),
      Function.update_of_ne (by decide : w55 ≠ w63), Function.update_self]
  have hm5_63 : m5 w63 = v4 := by
    simp only [m5, Function.update_of_ne (by decide : w63 ≠ w56), hm4_63]
  rw [hm5_55, hm5_63] at h
  set v6 := xor v3 v4
  set m6 := Function.update m5 w55 v6
  rw [exec_mkUnand_step (by decide)] at h
  have hm6_ok : m6 w63 = (m6 w57 && m6 w41) := by
    by_contra hne; rw [ite_eq_right hne] at h; cases h
  rw [ite_eq_left hm6_ok] at h; dsimp only at h
  injection h with hm'
  subst hm'
  dsimp only [s2aG2New, execList102]
  rw [exec_mkCX_step (by decide)]; dsimp only
  set u1 := xor b40 b41
  set n1 := Function.update m w40 u1
  have hn1_55 : n1 w55 = false := by
    simp only [n1, Function.update_of_ne (by decide : w55 ≠ w40), h55]
  have hn1_57 : n1 w57 = b57 := Function.update_of_ne (by decide) ..
  have hn1_40 : n1 w40 = u1 := Function.update_self ..
  rw [exec_mkAnd_step (by decide), ite_eq_left hn1_55]; dsimp only
  rw [hn1_57, hn1_40]
  set u2 := b57 && u1
  set n2 := Function.update n1 w55 u2
  rw [exec_mkCX_step (by decide)]; dsimp only
  have hn2_40 : n2 w40 = u1 := by
    simp only [n2, Function.update_of_ne (by decide : w40 ≠ w55), hn1_40]
  have hn2_41 : n2 w41 = b41 := by
    dsimp only [n2]; rw [Function.update_of_ne (by decide : w41 ≠ w55)]
    dsimp only [n1]; rw [Function.update_of_ne (by decide : w41 ≠ w40)]
  rw [hn2_40, hn2_41]
  set u3 := xor u1 b41
  set n3 := Function.update n2 w40 u3
  rw [exec_mkCX_step (by decide)]; dsimp only
  have hn3_55 : n3 w55 = u2 := by
    simp only [n3, n2, Function.update_of_ne (by decide : w55 ≠ w40), Function.update_self]
  have hn3_57 : n3 w57 = b57 := by
    simp only [n3, n2,
      Function.update_of_ne (by decide : w57 ≠ w40),
      Function.update_of_ne (by decide : w57 ≠ w55), hn1_57]
  rw [hn3_55, hn3_57]
  set u4 := xor u2 b57
  set n4 := Function.update n3 w55 u4
  have hn4_56 : n4 w56 = false := by
    simp only [n4, n3, n2, n1,
      Function.update_of_ne (by decide : w56 ≠ w55),
      Function.update_of_ne (by decide : w56 ≠ w40), h56]
  have hn4_55 : n4 w55 = u4 := Function.update_self ..
  have hn4_40 : n4 w40 = u3 := by
    simp only [n4, n3, Function.update_of_ne (by decide : w40 ≠ w55), Function.update_self]
  rw [exec_mkAnd_step (by decide), ite_eq_left hn4_56]; dsimp only
  rw [hn4_55, hn4_40]
  set u5 := u4 && u3
  set n5 := Function.update n4 w56 u5
  rw [exec_mkCX_step (by decide)]; dsimp only
  have hn5_55 : n5 w55 = u4 := by
    simp only [n5, Function.update_of_ne (by decide : w55 ≠ w56), hn4_55]
  have hn5_57 : n5 w57 = b57 := by
    simp only [n5, n4,
      Function.update_of_ne (by decide : w57 ≠ w56),
      Function.update_of_ne (by decide : w57 ≠ w55), hn3_57]
  rw [hn5_55, hn5_57]
  set u6 := xor u4 b57
  set n6 := Function.update n5 w55 u6
  rw [exec_mkCX_step (by decide)]; dsimp only
  have hn6_55 : n6 w55 = u6 := Function.update_self ..
  have hn6_56 : n6 w56 = u5 := by
    simp only [n6, n5, Function.update_of_ne (by decide : w56 ≠ w55), Function.update_self]
  rw [hn6_55, hn6_56]
  set n7 := Function.update n6 w55 (xor u6 u5)
  set m7 := Function.update m6 w63 false
  change some n7 = some m7
  congr 1; funext w
  by_cases hw55 : w = w55
  · subst hw55
    have hlhs : n7 w55 = xor u6 u5 := by
      dsimp only [n7]; rw [Function.update_self]
    have hrhs : m7 w55 = v6 := by
      dsimp only [m7]; rw [Function.update_of_ne (by decide : w55 ≠ w63)]
      dsimp only [m6]; rw [Function.update_self]
    rw [hlhs, hrhs]
    exact g2_bool_55 b40 b41 b57
  by_cases hw56 : w = w56
  · subst hw56
    have hlhs : n7 w56 = u5 := by
      dsimp only [n7]; rw [Function.update_of_ne (by decide : w56 ≠ w55)]
      exact hn6_56
    have hrhs : m7 w56 = v5 := by
      dsimp only [m7]; rw [Function.update_of_ne (by decide : w56 ≠ w63)]
      dsimp only [m6]; rw [Function.update_of_ne (by decide : w56 ≠ w55)]
      dsimp only [m5]; rw [Function.update_self]
    rw [hlhs, hrhs]
    exact g2_bool_56 b40 b41 b57
  by_cases hw40 : w = w40
  · subst hw40
    have hlhs : n7 w40 = u3 := by
      dsimp only [n7]; rw [Function.update_of_ne (by decide : w40 ≠ w55)]
      dsimp only [n6]; rw [Function.update_of_ne (by decide : w40 ≠ w55)]
      dsimp only [n5]; rw [Function.update_of_ne (by decide : w40 ≠ w56)]
      exact hn4_40
    have hrhs : m7 w40 = b40 := by
      dsimp only [m7]; rw [Function.update_of_ne (by decide : w40 ≠ w63)]
      dsimp only [m6]; rw [Function.update_of_ne (by decide : w40 ≠ w55)]
      dsimp only [m5]; rw [Function.update_of_ne (by decide : w40 ≠ w56)]
      exact hm4_40
    rw [hlhs, hrhs]
    exact g2_bool_40 b40 b41
  by_cases hw63 : w = w63
  · subst hw63
    have hlhs : n7 w63 = false := by
      dsimp only [n7]; rw [Function.update_of_ne (by decide : w63 ≠ w55)]
      dsimp only [n6]; rw [Function.update_of_ne (by decide : w63 ≠ w55)]
      dsimp only [n5]; rw [Function.update_of_ne (by decide : w63 ≠ w56)]
      dsimp only [n4]; rw [Function.update_of_ne (by decide : w63 ≠ w55)]
      dsimp only [n3]; rw [Function.update_of_ne (by decide : w63 ≠ w40)]
      dsimp only [n2]; rw [Function.update_of_ne (by decide : w63 ≠ w55)]
      dsimp only [n1]; rw [Function.update_of_ne (by decide : w63 ≠ w40)]
      exact h63
    have hrhs : m7 w63 = false := by
      dsimp only [m7]; rw [Function.update_self]
    rw [hlhs, hrhs]
  · have hlhs : n7 w = m w := by
      dsimp only [n7]; rw [Function.update_of_ne hw55]
      dsimp only [n6]; rw [Function.update_of_ne hw55]
      dsimp only [n5]; rw [Function.update_of_ne hw56]
      dsimp only [n4]; rw [Function.update_of_ne hw55]
      dsimp only [n3]; rw [Function.update_of_ne hw40]
      dsimp only [n2]; rw [Function.update_of_ne hw55]
      dsimp only [n1]; rw [Function.update_of_ne hw40]
    have hrhs : m7 w = m w := by
      dsimp only [m7]; rw [Function.update_of_ne hw63]
      dsimp only [m6]; rw [Function.update_of_ne hw55]
      dsimp only [m5]; rw [Function.update_of_ne hw56]
      dsimp only [m4]; rw [Function.update_of_ne hw63]
      dsimp only [m3]; rw [Function.update_of_ne hw55]
      dsimp only [m2]; rw [Function.update_of_ne hw63]
      dsimp only [m1]; rw [Function.update_of_ne hw63]
    rw [hlhs, hrhs]

theorem exec_s2aOps_of_cert {m m' : Fin 100 → Bool}
    (h : execList102 s2aCertOps m = some m') :
    execList102 s2aOps m = some m' := by
  unfold s2aCertOps at h
  rw [List.append_assoc, execList102_append] at h
  cases hpre : execList102 s2aPre m with
  | none => rw [hpre] at h; cases h
  | some m1 =>
    rw [hpre, Option.bind_some, execList102_append] at h
    cases hg2 : execList102 s2aG2Cert m1 with
    | none => rw [hg2] at h; cases h
    | some m2 =>
      rw [hg2, Option.bind_some] at h
      rw [s2aOps_eq_parts, List.append_assoc, execList102_append, hpre, Option.bind_some,
          execList102_append, exec_s2aG2_cert_to_new hg2, Option.bind_some, h]

theorem cubesSlice_0_cert :
    checkCubeSlice 0 3670016 cubes_0 allM_0 fMaskInitList_0
      initTree_0 trS2a_0 trS2b_0 trS6aOut_0 = true := by decide +kernel
theorem s2a_0_cert :
    runParSeq allM_0 (fMaskInitSlice 0) [s2aCertOps] initTree_0
      (fun tr => beqWTree tr trS2a_0 && checkU24Restored initTree_0 tr &&
        Nat.beq (wGet tr 62) 0) = true := by
  decide +kernel
theorem trS2b_0_cert :
    (checkWTreeWF 7 trS2b_0 &&
     checkEqList trS2b_0 [47, 48] [wGet trS2a_0 47, wGet trS2a_0 48] &&
     checkEqList trS2b_0 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS2a_0))) = true := by
  decide +kernel
theorem s2c_0_cert :
    runParSeq allM_0 (fMaskRotSlice 0) [s2cOps] trS2b_0
      (fun tr => beqWTree tr trS2c_0) = true := by
  decide +kernel
theorem s3a_0_cert :
    runParPhaseSeq allM_0 (fMaskRotSlice 0) s3aAllSeq trS2c_0
      (fun tr => beqWTree tr trS3a_0 && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true := by
  decide +kernel
theorem s3bPost_0_cert :
    runParPhaseSeq allM_0 (fMaskRotSlice 0) [s3bPostOps] trS3a_0
      (fun tr => beqWTree tr trS3b_0 && checkZeroList tr clean3bOut) = true := by decide +kernel
theorem s4_1PostInner_0_cert :
    runParSeq allM_0 (fMaskRotSlice 0) [s4_1PostInnerOps] trS3b_0
      (fun tr => beqWTree tr (tr41pOf trS3b_0) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet trS3b_0 81 ^^^ wGet trS3b_0 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet trS3b_0))) = true := by
  decide +kernel
theorem s5_2PostInner_0_cert :
    runParSeq allM_0 (fMaskRotSlice 0) s5_2PostInnerSeq (tr41pOf trS3b_0)
      (fun tr => beqWTree tr trS52Post_0 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet trS3b_0))) = true := by
  decide +kernel
theorem trS54In_0_cert :
    checkTrS54In allM_0 trS3b_0 trS52Post_0 trS54In_0 = true := by decide +kernel
theorem s5_4_0_cert :
    runParSeq allM_0 (fMaskRotSlice 0) s5_4Seq trS54In_0
      (fun tr => beqWTree tr trS54Out_0) = true := by
  decide +kernel
theorem s6a_0_cert :
    runParSeq allM_0 (fMaskRotSlice 0) [s6aOps] trS54Out_0
      (fun tr => beqWTree tr trS6aOut_0 &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet trS2b_0)) &&
                 checkEqList tr [47, 48] [wGet initTree_0 47, wGet initTree_0 48]) = true := by
  decide +kernel
theorem trS6cIn_0_cert :
    (checkWTreeWF 7 trS6cIn_0 &&
     checkEqList trS6cIn_0 (rangeList 25 24) ((rangeList 25 24).map (wGet initTree_0)) &&
     checkEqList trS6cIn_0 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS6aOut_0))) = true := by
  decide +kernel
theorem s6c_0_cert :
    runParSeq allM_0 (fMaskInitSlice 0) [s6cOps] trS6cIn_0
      (fun tr => beqWTree tr initTree_0 &&
                 checkU24Restored initTree_0 tr &&
                 checkZeroList tr zAnc52) = true := by decide +kernel

theorem cubesSlice_1_cert :
    checkCubeSlice 3670016 5767168 cubes_1 allM_1 fMaskInitList_1
      initTree_1 trS2a_1 trS2b_1 trS6aOut_1 = true := by decide +kernel
theorem s2a_1_cert :
    runParSeq allM_1 (fMaskInitSlice 1) [s2aCertOps] initTree_1
      (fun tr => beqWTree tr trS2a_1 && checkU24Restored initTree_1 tr &&
        Nat.beq (wGet tr 62) 0) = true := by
  decide +kernel
theorem trS2b_1_cert :
    (checkWTreeWF 7 trS2b_1 &&
     checkEqList trS2b_1 [47, 48] [wGet trS2a_1 47, wGet trS2a_1 48] &&
     checkEqList trS2b_1 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS2a_1))) = true := by
  decide +kernel
theorem s2c_1_cert :
    runParSeq allM_1 (fMaskRotSlice 1) [s2cOps] trS2b_1
      (fun tr => beqWTree tr trS2c_1) = true := by
  decide +kernel
theorem s3a_1_cert :
    runParPhaseSeq allM_1 (fMaskRotSlice 1) s3aAllSeq trS2c_1
      (fun tr => beqWTree tr trS3a_1 && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true := by
  decide +kernel
theorem s3bPost_1_cert :
    runParPhaseSeq allM_1 (fMaskRotSlice 1) [s3bPostOps] trS3a_1
      (fun tr => beqWTree tr trS3b_1 && checkZeroList tr clean3bOut) = true := by decide +kernel
theorem s4_1PostInner_1_cert :
    runParSeq allM_1 (fMaskRotSlice 1) [s4_1PostInnerOps] trS3b_1
      (fun tr => beqWTree tr (tr41pOf trS3b_1) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet trS3b_1 81 ^^^ wGet trS3b_1 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet trS3b_1))) = true := by
  decide +kernel
theorem s5_2PostInner_1_cert :
    runParSeq allM_1 (fMaskRotSlice 1) s5_2PostInnerSeq (tr41pOf trS3b_1)
      (fun tr => beqWTree tr trS52Post_1 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet trS3b_1))) = true := by
  decide +kernel
theorem trS54In_1_cert :
    checkTrS54In allM_1 trS3b_1 trS52Post_1 trS54In_1 = true := by decide +kernel
theorem s5_4_1_cert :
    runParSeq allM_1 (fMaskRotSlice 1) s5_4Seq trS54In_1
      (fun tr => beqWTree tr trS54Out_1) = true := by
  decide +kernel
theorem s6a_1_cert :
    runParSeq allM_1 (fMaskRotSlice 1) [s6aOps] trS54Out_1
      (fun tr => beqWTree tr trS6aOut_1 &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet trS2b_1)) &&
                 checkEqList tr [47, 48] [wGet initTree_1 47, wGet initTree_1 48]) = true := by
  decide +kernel
theorem trS6cIn_1_cert :
    (checkWTreeWF 7 trS6cIn_1 &&
     checkEqList trS6cIn_1 (rangeList 25 24) ((rangeList 25 24).map (wGet initTree_1)) &&
     checkEqList trS6cIn_1 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS6aOut_1))) = true := by
  decide +kernel
theorem s6c_1_cert :
    runParSeq allM_1 (fMaskInitSlice 1) [s6cOps] trS6cIn_1
      (fun tr => beqWTree tr initTree_1 &&
                 checkU24Restored initTree_1 tr &&
                 checkZeroList tr zAnc52) = true := by decide +kernel

theorem cubesSlice_2_cert :
    checkCubeSlice 5767168 7208960 cubes_2 allM_2 fMaskInitList_2
      initTree_2 trS2a_2 trS2b_2 trS6aOut_2 = true := by decide +kernel
theorem s2a_2_cert :
    runParSeq allM_2 (fMaskInitSlice 2) [s2aCertOps] initTree_2
      (fun tr => beqWTree tr trS2a_2 && checkU24Restored initTree_2 tr &&
        Nat.beq (wGet tr 62) 0) = true := by
  decide +kernel
theorem trS2b_2_cert :
    (checkWTreeWF 7 trS2b_2 &&
     checkEqList trS2b_2 [47, 48] [wGet trS2a_2 47, wGet trS2a_2 48] &&
     checkEqList trS2b_2 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS2a_2))) = true := by
  decide +kernel
theorem s2c_2_cert :
    runParSeq allM_2 (fMaskRotSlice 2) [s2cOps] trS2b_2
      (fun tr => beqWTree tr trS2c_2) = true := by
  decide +kernel
theorem s3a_2_cert :
    runParPhaseSeq allM_2 (fMaskRotSlice 2) s3aAllSeq trS2c_2
      (fun tr => beqWTree tr trS3a_2 && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true := by
  decide +kernel
theorem s3bPost_2_cert :
    runParPhaseSeq allM_2 (fMaskRotSlice 2) [s3bPostOps] trS3a_2
      (fun tr => beqWTree tr trS3b_2 && checkZeroList tr clean3bOut) = true := by decide +kernel
theorem s4_1PostInner_2_cert :
    runParSeq allM_2 (fMaskRotSlice 2) [s4_1PostInnerOps] trS3b_2
      (fun tr => beqWTree tr (tr41pOf trS3b_2) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet trS3b_2 81 ^^^ wGet trS3b_2 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet trS3b_2))) = true := by
  decide +kernel
theorem s5_2PostInner_2_cert :
    runParSeq allM_2 (fMaskRotSlice 2) s5_2PostInnerSeq (tr41pOf trS3b_2)
      (fun tr => beqWTree tr trS52Post_2 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet trS3b_2))) = true := by
  decide +kernel
theorem trS54In_2_cert :
    checkTrS54In allM_2 trS3b_2 trS52Post_2 trS54In_2 = true := by decide +kernel
theorem s5_4_2_cert :
    runParSeq allM_2 (fMaskRotSlice 2) s5_4Seq trS54In_2
      (fun tr => beqWTree tr trS54Out_2) = true := by
  decide +kernel
theorem s6a_2_cert :
    runParSeq allM_2 (fMaskRotSlice 2) [s6aOps] trS54Out_2
      (fun tr => beqWTree tr trS6aOut_2 &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet trS2b_2)) &&
                 checkEqList tr [47, 48] [wGet initTree_2 47, wGet initTree_2 48]) = true := by
  decide +kernel
theorem trS6cIn_2_cert :
    (checkWTreeWF 7 trS6cIn_2 &&
     checkEqList trS6cIn_2 (rangeList 25 24) ((rangeList 25 24).map (wGet initTree_2)) &&
     checkEqList trS6cIn_2 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS6aOut_2))) = true := by
  decide +kernel
theorem s6c_2_cert :
    runParSeq allM_2 (fMaskInitSlice 2) [s6cOps] trS6cIn_2
      (fun tr => beqWTree tr initTree_2 &&
                 checkU24Restored initTree_2 tr &&
                 checkZeroList tr zAnc52) = true := by decide +kernel

theorem cubesSlice_3_cert :
    checkCubeSlice 7208960 7995392 cubes_3 allM_3 fMaskInitList_3
      initTree_3 trS2a_3 trS2b_3 trS6aOut_3 = true := by decide +kernel
theorem s2a_3_cert :
    runParSeq allM_3 (fMaskInitSlice 3) [s2aCertOps] initTree_3
      (fun tr => beqWTree tr trS2a_3 && checkU24Restored initTree_3 tr &&
        Nat.beq (wGet tr 62) 0) = true := by
  decide +kernel
theorem trS2b_3_cert :
    (checkWTreeWF 7 trS2b_3 &&
     checkEqList trS2b_3 [47, 48] [wGet trS2a_3 47, wGet trS2a_3 48] &&
     checkEqList trS2b_3 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS2a_3))) = true := by
  decide +kernel
theorem s2c_3_cert :
    runParSeq allM_3 (fMaskRotSlice 3) [s2cOps] trS2b_3
      (fun tr => beqWTree tr trS2c_3) = true := by
  decide +kernel
theorem s3a_3_cert :
    runParPhaseSeq allM_3 (fMaskRotSlice 3) s3aAllSeq trS2c_3
      (fun tr => beqWTree tr trS3a_3 && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true := by
  decide +kernel
theorem s3bPost_3_cert :
    runParPhaseSeq allM_3 (fMaskRotSlice 3) [s3bPostOps] trS3a_3
      (fun tr => beqWTree tr trS3b_3 && checkZeroList tr clean3bOut) = true := by decide +kernel
theorem s4_1PostInner_3_cert :
    runParSeq allM_3 (fMaskRotSlice 3) [s4_1PostInnerOps] trS3b_3
      (fun tr => beqWTree tr (tr41pOf trS3b_3) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet trS3b_3 81 ^^^ wGet trS3b_3 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet trS3b_3))) = true := by
  decide +kernel
theorem s5_2PostInner_3_cert :
    runParSeq allM_3 (fMaskRotSlice 3) s5_2PostInnerSeq (tr41pOf trS3b_3)
      (fun tr => beqWTree tr trS52Post_3 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet trS3b_3))) = true := by
  decide +kernel
theorem trS54In_3_cert :
    checkTrS54In allM_3 trS3b_3 trS52Post_3 trS54In_3 = true := by decide +kernel
theorem s5_4_3_cert :
    runParSeq allM_3 (fMaskRotSlice 3) s5_4Seq trS54In_3
      (fun tr => beqWTree tr trS54Out_3) = true := by
  decide +kernel
theorem s6a_3_cert :
    runParSeq allM_3 (fMaskRotSlice 3) [s6aOps] trS54Out_3
      (fun tr => beqWTree tr trS6aOut_3 &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet trS2b_3)) &&
                 checkEqList tr [47, 48] [wGet initTree_3 47, wGet initTree_3 48]) = true := by
  decide +kernel
theorem trS6cIn_3_cert :
    (checkWTreeWF 7 trS6cIn_3 &&
     checkEqList trS6cIn_3 (rangeList 25 24) ((rangeList 25 24).map (wGet initTree_3)) &&
     checkEqList trS6cIn_3 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS6aOut_3))) = true := by
  decide +kernel
theorem s6c_3_cert :
    runParSeq allM_3 (fMaskInitSlice 3) [s6cOps] trS6cIn_3
      (fun tr => beqWTree tr initTree_3 &&
                 checkU24Restored initTree_3 tr &&
                 checkZeroList tr zAnc52) = true := by decide +kernel

theorem cubesSlice_4_cert :
    checkCubeSlice 7995392 8290304 cubes_4 allM_4 fMaskInitList_4
      initTree_4 trS2a_4 trS2b_4 trS6aOut_4 = true := by decide +kernel
theorem s2a_4_cert :
    runParSeq allM_4 (fMaskInitSlice 4) [s2aCertOps] initTree_4
      (fun tr => beqWTree tr trS2a_4 && checkU24Restored initTree_4 tr &&
        Nat.beq (wGet tr 62) 0) = true := by
  decide +kernel
theorem trS2b_4_cert :
    (checkWTreeWF 7 trS2b_4 &&
     checkEqList trS2b_4 [47, 48] [wGet trS2a_4 47, wGet trS2a_4 48] &&
     checkEqList trS2b_4 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS2a_4))) = true := by
  decide +kernel
theorem s2c_4_cert :
    runParSeq allM_4 (fMaskRotSlice 4) [s2cOps] trS2b_4
      (fun tr => beqWTree tr trS2c_4) = true := by
  decide +kernel
theorem s3a_4_cert :
    runParPhaseSeq allM_4 (fMaskRotSlice 4) s3aAllSeq trS2c_4
      (fun tr => beqWTree tr trS3a_4 && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true := by
  decide +kernel
theorem s3bPost_4_cert :
    runParPhaseSeq allM_4 (fMaskRotSlice 4) [s3bPostOps] trS3a_4
      (fun tr => beqWTree tr trS3b_4 && checkZeroList tr clean3bOut) = true := by decide +kernel
theorem s4_1PostInner_4_cert :
    runParSeq allM_4 (fMaskRotSlice 4) [s4_1PostInnerOps] trS3b_4
      (fun tr => beqWTree tr (tr41pOf trS3b_4) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet trS3b_4 81 ^^^ wGet trS3b_4 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet trS3b_4))) = true := by
  decide +kernel
theorem s5_2PostInner_4_cert :
    runParSeq allM_4 (fMaskRotSlice 4) s5_2PostInnerSeq (tr41pOf trS3b_4)
      (fun tr => beqWTree tr trS52Post_4 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet trS3b_4))) = true := by
  decide +kernel
theorem trS54In_4_cert :
    checkTrS54In allM_4 trS3b_4 trS52Post_4 trS54In_4 = true := by decide +kernel
theorem s5_4_4_cert :
    runParSeq allM_4 (fMaskRotSlice 4) s5_4Seq trS54In_4
      (fun tr => beqWTree tr trS54Out_4) = true := by
  decide +kernel
theorem s6a_4_cert :
    runParSeq allM_4 (fMaskRotSlice 4) [s6aOps] trS54Out_4
      (fun tr => beqWTree tr trS6aOut_4 &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet trS2b_4)) &&
                 checkEqList tr [47, 48] [wGet initTree_4 47, wGet initTree_4 48]) = true := by
  decide +kernel
theorem trS6cIn_4_cert :
    (checkWTreeWF 7 trS6cIn_4 &&
     checkEqList trS6cIn_4 (rangeList 25 24) ((rangeList 25 24).map (wGet initTree_4)) &&
     checkEqList trS6cIn_4 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS6aOut_4))) = true := by
  decide +kernel
theorem s6c_4_cert :
    runParSeq allM_4 (fMaskInitSlice 4) [s6cOps] trS6cIn_4
      (fun tr => beqWTree tr initTree_4 &&
                 checkU24Restored initTree_4 tr &&
                 checkZeroList tr zAnc52) = true := by decide +kernel

theorem cubesSlice_5_cert :
    checkCubeSlice 8290304 8376320 cubes_5 allM_5 fMaskInitList_5
      initTree_5 trS2a_5 trS2b_5 trS6aOut_5 = true := by decide +kernel
theorem s2a_5_cert :
    runParSeq allM_5 (fMaskInitSlice 5) [s2aCertOps] initTree_5
      (fun tr => beqWTree tr trS2a_5 && checkU24Restored initTree_5 tr &&
        Nat.beq (wGet tr 62) 0) = true := by
  decide +kernel
theorem trS2b_5_cert :
    (checkWTreeWF 7 trS2b_5 &&
     checkEqList trS2b_5 [47, 48] [wGet trS2a_5 47, wGet trS2a_5 48] &&
     checkEqList trS2b_5 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS2a_5))) = true := by
  decide +kernel
theorem s2c_5_cert :
    runParSeq allM_5 (fMaskRotSlice 5) [s2cOps] trS2b_5
      (fun tr => beqWTree tr trS2c_5) = true := by
  decide +kernel
theorem s3a_5_cert :
    runParPhaseSeq allM_5 (fMaskRotSlice 5) s3aAllSeq trS2c_5
      (fun tr => beqWTree tr trS3a_5 && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true := by
  decide +kernel
theorem s3bPost_5_cert :
    runParPhaseSeq allM_5 (fMaskRotSlice 5) [s3bPostOps] trS3a_5
      (fun tr => beqWTree tr trS3b_5 && checkZeroList tr clean3bOut) = true := by decide +kernel
theorem s4_1PostInner_5_cert :
    runParSeq allM_5 (fMaskRotSlice 5) [s4_1PostInnerOps] trS3b_5
      (fun tr => beqWTree tr (tr41pOf trS3b_5) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet trS3b_5 81 ^^^ wGet trS3b_5 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet trS3b_5))) = true := by
  decide +kernel
theorem s5_2PostInner_5_cert :
    runParSeq allM_5 (fMaskRotSlice 5) s5_2PostInnerSeq (tr41pOf trS3b_5)
      (fun tr => beqWTree tr trS52Post_5 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet trS3b_5))) = true := by
  decide +kernel
theorem trS54In_5_cert :
    checkTrS54In allM_5 trS3b_5 trS52Post_5 trS54In_5 = true := by decide +kernel
theorem s5_4_5_cert :
    runParSeq allM_5 (fMaskRotSlice 5) s5_4Seq trS54In_5
      (fun tr => beqWTree tr trS54Out_5) = true := by
  decide +kernel
theorem s6a_5_cert :
    runParSeq allM_5 (fMaskRotSlice 5) [s6aOps] trS54Out_5
      (fun tr => beqWTree tr trS6aOut_5 &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet trS2b_5)) &&
                 checkEqList tr [47, 48] [wGet initTree_5 47, wGet initTree_5 48]) = true := by
  decide +kernel
theorem trS6cIn_5_cert :
    (checkWTreeWF 7 trS6cIn_5 &&
     checkEqList trS6cIn_5 (rangeList 25 24) ((rangeList 25 24).map (wGet initTree_5)) &&
     checkEqList trS6cIn_5 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS6aOut_5))) = true := by
  decide +kernel
theorem s6c_5_cert :
    runParSeq allM_5 (fMaskInitSlice 5) [s6cOps] trS6cIn_5
      (fun tr => beqWTree tr initTree_5 &&
                 checkU24Restored initTree_5 tr &&
                 checkZeroList tr zAnc52) = true := by decide +kernel

theorem cubesSlice_6_cert :
    checkCubeSlice 8376320 8388096 cubes_6 allM_6 fMaskInitList_6
      initTree_6 trS2a_6 trS2b_6 trS6aOut_6 = true := by decide +kernel
theorem s2a_6_cert :
    runParSeq allM_6 (fMaskInitSlice 6) [s2aCertOps] initTree_6
      (fun tr => beqWTree tr trS2a_6 && checkU24Restored initTree_6 tr &&
        Nat.beq (wGet tr 62) 0) = true := by
  decide +kernel
theorem trS2b_6_cert :
    (checkWTreeWF 7 trS2b_6 &&
     checkEqList trS2b_6 [47, 48] [wGet trS2a_6 47, wGet trS2a_6 48] &&
     checkEqList trS2b_6 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS2a_6))) = true := by
  decide +kernel
theorem s2c_6_cert :
    runParSeq allM_6 (fMaskRotSlice 6) [s2cOps] trS2b_6
      (fun tr => beqWTree tr trS2c_6) = true := by
  decide +kernel
theorem s3a_6_cert :
    runParPhaseSeq allM_6 (fMaskRotSlice 6) s3aAllSeq trS2c_6
      (fun tr => beqWTree tr trS3a_6 && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true := by
  decide +kernel
theorem s3bPost_6_cert :
    runParPhaseSeq allM_6 (fMaskRotSlice 6) [s3bPostOps] trS3a_6
      (fun tr => beqWTree tr trS3b_6 && checkZeroList tr clean3bOut) = true := by decide +kernel
theorem s4_1PostInner_6_cert :
    runParSeq allM_6 (fMaskRotSlice 6) [s4_1PostInnerOps] trS3b_6
      (fun tr => beqWTree tr (tr41pOf trS3b_6) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet trS3b_6 81 ^^^ wGet trS3b_6 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet trS3b_6))) = true := by
  decide +kernel
theorem s5_2PostInner_6_cert :
    runParSeq allM_6 (fMaskRotSlice 6) s5_2PostInnerSeq (tr41pOf trS3b_6)
      (fun tr => beqWTree tr trS52Post_6 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet trS3b_6))) = true := by
  decide +kernel
theorem trS54In_6_cert :
    checkTrS54In allM_6 trS3b_6 trS52Post_6 trS54In_6 = true := by decide +kernel
theorem s5_4_6_cert :
    runParSeq allM_6 (fMaskRotSlice 6) s5_4Seq trS54In_6
      (fun tr => beqWTree tr trS54Out_6) = true := by
  decide +kernel
theorem s6a_6_cert :
    runParSeq allM_6 (fMaskRotSlice 6) [s6aOps] trS54Out_6
      (fun tr => beqWTree tr trS6aOut_6 &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet trS2b_6)) &&
                 checkEqList tr [47, 48] [wGet initTree_6 47, wGet initTree_6 48]) = true := by
  decide +kernel
theorem trS6cIn_6_cert :
    (checkWTreeWF 7 trS6cIn_6 &&
     checkEqList trS6cIn_6 (rangeList 25 24) ((rangeList 25 24).map (wGet initTree_6)) &&
     checkEqList trS6cIn_6 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS6aOut_6))) = true := by
  decide +kernel
theorem s6c_6_cert :
    runParSeq allM_6 (fMaskInitSlice 6) [s6cOps] trS6cIn_6
      (fun tr => beqWTree tr initTree_6 &&
                 checkU24Restored initTree_6 tr &&
                 checkZeroList tr zAnc52) = true := by decide +kernel

theorem cubesSlice_7_cert :
    checkCubeSlice 8388096 8388608 cubes_7 allM_7 fMaskInitList_7
      initTree_7 trS2a_7 trS2b_7 trS6aOut_7 = true := by decide +kernel
theorem s2a_7_cert :
    runParSeq allM_7 (fMaskInitSlice 7) [s2aCertOps] initTree_7
      (fun tr => beqWTree tr trS2a_7 && checkU24Restored initTree_7 tr &&
        Nat.beq (wGet tr 62) 0) = true := by
  decide +kernel
theorem trS2b_7_cert :
    (checkWTreeWF 7 trS2b_7 &&
     checkEqList trS2b_7 [47, 48] [wGet trS2a_7 47, wGet trS2a_7 48] &&
     checkEqList trS2b_7 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS2a_7))) = true := by
  decide +kernel
theorem s2c_7_cert :
    runParSeq allM_7 (fMaskRotSlice 7) [s2cOps] trS2b_7
      (fun tr => beqWTree tr trS2c_7) = true := by
  decide +kernel
theorem s3a_7_cert :
    runParPhaseSeq allM_7 (fMaskRotSlice 7) s3aAllSeq trS2c_7
      (fun tr => beqWTree tr trS3a_7 && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true := by
  decide +kernel
theorem s3bPost_7_cert :
    runParPhaseSeq allM_7 (fMaskRotSlice 7) [s3bPostOps] trS3a_7
      (fun tr => beqWTree tr trS3b_7 && checkZeroList tr clean3bOut) = true := by decide +kernel
theorem s4_1PostInner_7_cert :
    runParSeq allM_7 (fMaskRotSlice 7) [s4_1PostInnerOps] trS3b_7
      (fun tr => beqWTree tr (tr41pOf trS3b_7) &&
                 Nat.beq (wGet tr 86) 0 &&
                 Nat.beq (wGet tr 85) 0 &&
                 Nat.beq (wGet tr 52) 0 &&
                 Nat.beq (wGet tr 81) (wGet trS3b_7 81 ^^^ wGet trS3b_7 85) &&
                 checkEqList tr s41KeepWires (s41KeepWires.map (wGet trS3b_7))) = true := by
  decide +kernel
theorem s5_2PostInner_7_cert :
    runParSeq allM_7 (fMaskRotSlice 7) s5_2PostInnerSeq (tr41pOf trS3b_7)
      (fun tr => beqWTree tr trS52Post_7 &&
                 checkZeroList tr clean53Wires &&
                 checkEqList tr s52KeepWires (s52KeepWires.map (wGet trS3b_7))) = true := by
  decide +kernel
theorem trS54In_7_cert :
    checkTrS54In allM_7 trS3b_7 trS52Post_7 trS54In_7 = true := by decide +kernel
theorem s5_4_7_cert :
    runParSeq allM_7 (fMaskRotSlice 7) s5_4Seq trS54In_7
      (fun tr => beqWTree tr trS54Out_7) = true := by
  decide +kernel
theorem s6a_7_cert :
    runParSeq allM_7 (fMaskRotSlice 7) [s6aOps] trS54Out_7
      (fun tr => beqWTree tr trS6aOut_7 &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet trS2b_7)) &&
                 checkEqList tr [47, 48] [wGet initTree_7 47, wGet initTree_7 48]) = true := by
  decide +kernel
theorem trS6cIn_7_cert :
    (checkWTreeWF 7 trS6cIn_7 &&
     checkEqList trS6cIn_7 (rangeList 25 24) ((rangeList 25 24).map (wGet initTree_7)) &&
     checkEqList trS6cIn_7 (rangeList 50 50)
       ((rangeList 50 50).map (wGet trS6aOut_7))) = true := by
  decide +kernel
theorem s6c_7_cert :
    runParSeq allM_7 (fMaskInitSlice 7) [s6cOps] trS6cIn_7
      (fun tr => beqWTree tr initTree_7 &&
                 checkU24Restored initTree_7 tr &&
                 checkZeroList tr zAnc52) = true := by decide +kernel


-- ============================================================================
-- Section 2b: Soundness & Execution for Stages 2a, 2b, 2c, 3a, 3b, 5.2Post, 5.4, 6a, 6b, 6c
-- ============================================================================

def findCube4 (bit : Nat) :
    List (Nat × Nat × Nat × Nat) → Nat → Option (Nat × Nat × Nat × Nat × Nat)
  | [], _ => none
  | (us, ue, w, s4) :: rest, u =>
      if Nat.blt u ue then some (bit, us, ue, w, s4)
      else findCube4 (bit + 1) rest u

theorem findCube4_sound :
    ∀ (cs : List (Nat × Nat × Nat × Nat)) (off cur end_ u : Nat),
      checkPartition4 cur end_ cs = true →
      cur ≤ u → u < end_ →
      ∃ bit us ue w s4,
        findCube4 off cs u = some (bit, us, ue, w, s4) ∧
        off ≤ bit ∧
        cs[bit - off]? = some (us, ue, w, s4) ∧
        us ≤ u ∧ u < ue
  | [], _, cur, end_, u, hpart, hcur, hu => by
      dsimp only [checkPartition4] at hpart
      have := Nat.beq_eq.mp hpart; omega
  | (us, ue, w, s4) :: rest, off, cur, end_, u, hpart, hcur, hu => by
      dsimp only [checkPartition4] at hpart
      cases hp : (Nat.beq cur us && Nat.blt us ue)
      · rw [hp, Bool.cond_false] at hpart; cases hpart
      rw [hp, Bool.cond_true] at hpart
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hp
      dsimp only [findCube4]
      cases hlt : Nat.blt u ue
      · have hue_le : ue ≤ u := (blt_false_iff u ue).1 hlt
        obtain ⟨bit, us', ue', w', s4', hf, hoff, hget, hus', hue'⟩ :=
          findCube4_sound rest (off + 1) ue end_ u hpart hue_le hu
        have hidx : bit - off = (bit - (off + 1)) + 1 := by omega
        exact ⟨bit, us', ue', w', s4', hf, by omega,
          by rw [hidx, List.getElem?_cons_succ]; exact hget, hus', hue'⟩
      · have hu_lt : u < ue := Nat.blt_eq.mp hlt
        exact ⟨off, us, ue, w, s4, rfl, le_rfl, by simp, by omega, hu_lt⟩

theorem testBit_eq_of_cube {us w u i : Nat} (hw : w ≤ i)
    (hmod : us % 2 ^ w = 0) (hus : us ≤ u) (hue : u < us + 2 ^ w) :
    u.testBit i = us.testBit i := by
  have hpow_pos : 0 < 2 ^ w := by positivity
  have hdiv : u / 2 ^ w = us / 2 ^ w := by
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
    have hu1 : q * 2 ^ w ≤ u := by linarith
    have hu2 : u < (q + 1) * 2 ^ w := by linarith
    have hq1 : u / 2 ^ w = q := Nat.div_eq_of_lt_le hu1 hu2
    have hq2 : us / 2 ^ w = q := by rw [hq, Nat.mul_comm, Nat.mul_div_cancel _ hpow_pos]
    rw [hq1, hq2]
  have hi_split : i = w + (i - w) := by omega
  rw [hi_split, Nat.add_comm w (i - w), ← Nat.testBit_div_two_pow, ← Nat.testBit_div_two_pow, hdiv]

theorem checkCubeSlice_sound {start end_ : Nat} {cs : List (Nat × Nat × Nat × Nat)}
    {allM : Nat} {fmList : List Nat} {tr0 tr2a tr2b tr6a : WTree}
    (hok : checkCubeSlice start end_ cs allM fmList tr0 tr2a tr2b tr6a = true)
    {m1 : Fin 100 → Bool}
    (hm1_anc : ∀ i : Nat, (hi : i < 50) → m1 ⟨50 + i, by omega⟩ = false)
    (hstart : start ≤ sliceVal 25 24 m1) (hend : sliceVal 25 24 m1 < end_) :
    ∃ bit us ue w s4,
      findCube4 0 cs (sliceVal 25 24 m1) = some (bit, us, ue, w, s4) ∧
      cs[bit]? = some (us, ue, w, s4) ∧
      bit < cs.length ∧
      us ≤ sliceVal 25 24 m1 ∧ sliceVal 25 24 m1 < ue ∧
      s4 < 16 ∧ w ≤ 22 ∧
      (∀ i, 22 ≤ i → i < 24 → (fmList.getD i 0).testBit bit = false) ∧
      (∀ b < 4, (wGet tr2a (s4Wires2b.getD b 0)).testBit bit = s4.testBit b ∧
                 (wGet tr6a (s4Wires6b.getD b 0)).testBit bit = s4.testBit b) ∧
      (∀ k < 16, (sliceVal 25 24 m1).testBit (s2bSrc s4 k) = uRotBit (sliceVal 25 24 m1) s4 k) ∧
      (∀ k, 16 ≤ k → k < 22 →
        (wGet tr2b (25 + k)).testBit bit = (sliceVal 25 24 m1).testBit (s2bSrc s4 k)) ∧
      ParInv bit allM (fun i => fmList.getD i 0) m1 tr0 m1 := by
  unfold checkCubeSlice at hok
  simp only [Bool.and_eq_true, Nat.beq_eq, shiftLeft_eq_mul_pow, one_mul] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf_b, hall_eq⟩, hz⟩, hpart⟩, hsc_all⟩, hu24_all⟩, hs4_all⟩, hrot6_all⟩ := hok
  obtain ⟨bit, us, ue, w, s4, hf, _, hget, hus, hue⟩ :=
    findCube4_sound cs 0 start end_ (sliceVal 25 24 m1) hpart hstart hend
  rw [Nat.sub_zero] at hget
  have hbit : bit < cs.length := (List.getElem?_eq_some_iff.mp hget).1
  have hsc : checkCubeScalar (us, ue, w, s4) = true :=
    List.all_eq_true.mp hsc_all _ (List.mem_of_getElem? hget)
  unfold checkCubeScalar at hsc
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq,
    shiftLeft_eq_mul_pow, one_mul] at hsc
  obtain ⟨⟨⟨⟨⟨hue_eq, hw22⟩, hs4_lt⟩, hmod⟩, hrot16⟩, hrot6_w⟩ := hsc
  set u := sliceVal 25 24 m1
  have hu_bit : ∀ i : Nat, (hi : i < 24) → u.testBit i = m1 ⟨25 + i, by omega⟩ := by
    intro i hi
    unfold u sliceVal
    have h :=
      sumBits_testBit 24 (fun k => if hk : 25 + k < 100 then m1 ⟨25 + k, hk⟩ else false) i hi
    simpa [show 25 + i < 100 by omega] using h
  have hfm_hi : ∀ i, 22 ≤ i → i < 24 → (fmList.getD i 0).testBit bit = false := by
    intro i hi1 hi2
    have hu24_i := List.all_eq_true.mp hu24_all i (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
    simp only [Bool.and_eq_true, Nat.beq_eq] at hu24_i
    rw [hu24_i.1,
      packCubeBit_testBit (fun (_, _, w', _) => Nat.blt i w') cs bit (us, ue, w, s4) hget]
    dsimp only
    exact (blt_false_iff i w).mpr (by omega)
  have hs4_bits : ∀ b < 4, (wGet tr2a (s4Wires2b.getD b 0)).testBit bit = s4.testBit b ∧
      (wGet tr6a (s4Wires6b.getD b 0)).testBit bit = s4.testBit b := by
    intro b hb
    have h1 := List.all_eq_true.mp hs4_all b (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
    simp only [Bool.and_eq_true, Nat.beq_eq] at h1
    have hpk :=
      packCubeBit_testBit (fun (_, _, _, s4') => s4'.testBit b) cs bit (us, ue, w, s4) hget
    rw [h1.1, h1.2, hpk]; exact ⟨rfl, rfl⟩
  have hrot16_bits : ∀ k < 16, u.testBit (s2bSrc s4 k) = uRotBit u s4 k := by
    intro k hk
    have h1 := List.all_eq_true.mp hrot16 k (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, beq_iff_eq] at h1
    unfold uRotBit
    rcases h1 with heq | ⟨⟨hw1, hw2⟩, htb_eq⟩
    · rw [heq]
    · rw [testBit_eq_of_cube hw1 hmod hus (by omega),
          testBit_eq_of_cube hw2 hmod hus (by omega), htb_eq]
  have hrot6_bits :
      ∀ k, 16 ≤ k → k < 22 → (wGet tr2b (25 + k)).testBit bit = u.testBit (s2bSrc s4 k) := by
    intro k hk1 hk2
    have h1 := List.all_eq_true.mp hrot6_all k (mem_rangeList_iff.mpr ⟨hk1, by omega⟩)
    have hw_src : w ≤ s2bSrc s4 k := by
      have h2 := List.all_eq_true.mp hrot6_w k (mem_rangeList_iff.mpr ⟨hk1, by omega⟩)
      exact Nat.ble_eq.mp h2
    rw [Nat.beq_eq.mp h1,
        packCubeBit_testBit (fun (us', _, _, s4') => us'.testBit (s2bSrc s4' k)) cs bit
          (us, ue, w, s4) hget,
        testBit_eq_of_cube hw_src hmod hus (by omega)]
  have hwf0 : WTreeWF 7 tr0 := checkWTreeWF_sound 7 tr0 hwf_b
  have hall_tb : allM.testBit bit = true := by
    rw [hall_eq]; exact testBit_two_pow_sub_one_of_lt hbit
  have hI0 : ParInv bit allM (fun i => fmList.getD i 0) m1 tr0 m1 := by
    refine ⟨hwf0, hall_tb, fun _ _ => rfl, fun q hq hfm_q => ?_⟩
    obtain ⟨hq25, hq102, _, hq_cases⟩ := isParWire_bounds hq
    rcases hq_cases with hq49_lt | hq50_le
    · set i := q.val - 25
      have hi : i < 24 := by omega
      have hqi : q.val = 25 + i := by omega
      have hu24_i := List.all_eq_true.mp hu24_all i (mem_rangeList_iff.mpr ⟨by omega, by omega⟩)
      simp only [Bool.and_eq_true, Nat.beq_eq] at hu24_i
      unfold getFMask at hfm_q
      rw [ite_eq_left hq49_lt] at hfm_q
      change (fmList.getD i 0).testBit bit = false at hfm_q
      rw [hu24_i.1,
          packCubeBit_testBit (fun (_, _, w', _) => Nat.blt i w') cs bit
            (us, ue, w, s4) hget] at hfm_q
      dsimp only at hfm_q
      have hw_le_i : w ≤ i := (blt_false_iff i w).mp hfm_q
      rw [hqi, hu24_i.2,
          packCubeBit_testBit
            (fun (us', _, w', _) => if Nat.blt i w' then false else us'.testBit i) cs bit
            (us, ue, w, s4) hget]
      dsimp only
      rw [hfm_q, ite_eq_right Bool.false_ne_true,
        ← testBit_eq_of_cube hw_le_i hmod hus (by omega), hu_bit i hi]
      congr 1; exact Fin.ext hqi
    · have hq_in : q.val ∈ zAnc52 := mem_zAnc52_iff.mpr ⟨hq50_le, hq102⟩
      rw [checkZeroList_sound zAnc52 hz q.val hq_in, Nat.zero_testBit]
      have hm1_z := hm1_anc (q.val - 50) (by omega)
      simpa [show 50 + (q.val - 50) = q.val by omega] using hm1_z
  exact ⟨bit, us, ue, w, s4, hf, hget, hbit, hus, hue, hs4_lt, hw22, hfm_hi, hs4_bits,
    hrot16_bits, hrot6_bits, hI0⟩

theorem s4TrueW_sound {ws : List Nat} {s4 : Nat} {m : Fin 100 → Bool}
    (hbits : ∀ b < 4, ∀ hlt : ws.getD b 0 < 100, m ⟨ws.getD b 0, hlt⟩ = s4.testBit b) :
    ∀ w : Fin 100, w.val ∈ s4TrueW ws s4 → m w = true := by
  intro w hw
  unfold s4TrueW at hw
  simp only [List.mem_append] at hw
  rcases hw with ((h0 | h1) | h2) | h3
  · cases hb : s4.testBit 0
    · rw [hb] at h0; cases h0
    · rw [hb, ite_eq_left rfl, List.mem_singleton] at h0
      have hlt : ws.getD 0 0 < 100 := h0 ▸ w.isLt
      rw [show w = ⟨ws.getD 0 0, hlt⟩ from Fin.ext h0, hbits 0 (by decide) hlt, hb]
  · cases hb : s4.testBit 1
    · rw [hb] at h1; cases h1
    · rw [hb, ite_eq_left rfl, List.mem_singleton] at h1
      have hlt : ws.getD 1 0 < 100 := h1 ▸ w.isLt
      rw [show w = ⟨ws.getD 1 0, hlt⟩ from Fin.ext h1, hbits 1 (by decide) hlt, hb]
  · cases hb : s4.testBit 2
    · rw [hb] at h2; cases h2
    · rw [hb, ite_eq_left rfl, List.mem_singleton] at h2
      have hlt : ws.getD 2 0 < 100 := h2 ▸ w.isLt
      rw [show w = ⟨ws.getD 2 0, hlt⟩ from Fin.ext h2, hbits 2 (by decide) hlt, hb]
  · cases hb : s4.testBit 3
    · rw [hb] at h3; cases h3
    · rw [hb, ite_eq_left rfl, List.mem_singleton] at h3
      have hlt : ws.getD 3 0 < 100 := h3 ▸ w.isLt
      rw [show w = ⟨ws.getD 3 0, hlt⟩ from Fin.ext h3, hbits 3 (by decide) hlt, hb]

theorem s4FalseW_sound {ws : List Nat} {s4 : Nat} {m : Fin 100 → Bool}
    (hbits : ∀ b < 4, ∀ hlt : ws.getD b 0 < 100, m ⟨ws.getD b 0, hlt⟩ = s4.testBit b)
    (h62 : m ⟨62, by decide⟩ = false) :
    ∀ w : Fin 100, w.val ∈ s4FalseW ws s4 → m w = false := by
  intro w hw
  unfold s4FalseW at hw
  simp only [List.mem_append, List.mem_singleton] at hw
  rcases hw with (((h0 | h1) | h2) | h3) | h62_eq
  · cases hb : s4.testBit 0
    · rw [hb, ite_eq_right Bool.false_ne_true, List.mem_singleton] at h0
      have hlt : ws.getD 0 0 < 100 := h0 ▸ w.isLt
      rw [show w = ⟨ws.getD 0 0, hlt⟩ from Fin.ext h0, hbits 0 (by decide) hlt, hb]
    · rw [hb] at h0; cases h0
  · cases hb : s4.testBit 1
    · rw [hb, ite_eq_right Bool.false_ne_true, List.mem_singleton] at h1
      have hlt : ws.getD 1 0 < 100 := h1 ▸ w.isLt
      rw [show w = ⟨ws.getD 1 0, hlt⟩ from Fin.ext h1, hbits 1 (by decide) hlt, hb]
    · rw [hb] at h1; cases h1
  · cases hb : s4.testBit 2
    · rw [hb, ite_eq_right Bool.false_ne_true, List.mem_singleton] at h2
      have hlt : ws.getD 2 0 < 100 := h2 ▸ w.isLt
      rw [show w = ⟨ws.getD 2 0, hlt⟩ from Fin.ext h2, hbits 2 (by decide) hlt, hb]
    · rw [hb] at h2; cases h2
  · cases hb : s4.testBit 3
    · rw [hb, ite_eq_right Bool.false_ne_true, List.mem_singleton] at h3
      have hlt : ws.getD 3 0 < 100 := h3 ▸ w.isLt
      rw [show w = ⟨ws.getD 3 0, hlt⟩ from Fin.ext h3, hbits 3 (by decide) hlt, hb]
    · rw [hb] at h3; cases h3
  · have hfin : w = ⟨62, by decide⟩ := Fin.ext h62_eq
    rw [hfin, h62]

theorem targets2b_eval {s4 k : Nat} (hk : k < 22) (m : Fin 100 → Bool) :
    evalXWires m (targets2b s4) k =
      m ⟨25 + s2bSrc s4 k, by have := s2bSrc_lt (s4 := s4) (k := k); omega⟩ := by
  unfold evalXWires targets2b
  rw [List.getElem?_map, rangeList_getElem? hk, Nat.zero_add]
  dsimp only [Option.map, Option.getD, evalXWire]
  have hlt : 25 + s2bSrc s4 k < 100 := by have := s2bSrc_lt (s4 := s4) (k := k); omega
  rw [dite_eq_left hlt, Bool.xor_false]

theorem targets6b_eval {s4 j : Nat} (hj : j < 22) (hs4 : s4 < 16) (m : Fin 100 → Bool) :
    evalXWires m (targets6b s4) j =
      m ⟨25 + s6bSrc s4 j, by have := (s6bSrc_spec hs4 hj).1; omega⟩ := by
  unfold evalXWires targets6b
  rw [List.getElem?_map, rangeList_getElem? hj, Nat.zero_add]
  dsimp only [Option.map, Option.getD, evalXWire]
  have hlt : 25 + s6bSrc s4 j < 100 := by have := (s6bSrc_spec hs4 hj).1; omega
  rw [dite_eq_left hlt, Bool.xor_false]

theorem sumBits_bHi19Wires {bit allM : Nat} {fMask : Nat → Nat}
    {m2b m3a : Fin 100 → Bool} {tr3a : WTree}
    (hI : ParInv bit allM fMask m2b tr3a m3a) :
    sumBits 25
        (evalXWires m3a (bHi19Wires.map (fun w => .wire w false) ++ List.replicate 6 .zero)) =
      getBits bit (bHi19Wires.map (wGet tr3a)) 0 19 := by
  have hsp := sumBits_split (A := 19) (B := 6)
    (evalXWires m3a (bHi19Wires.map (fun w => .wire w false) ++ List.replicate 6 .zero))
  have hhi0 : sumBits 6 (fun k =>
      evalXWires m3a (bHi19Wires.map (fun w => .wire w false) ++ List.replicate 6 .zero)
        (19 + k)) = 0 := by
    rw [← sumBits_zero_fn 6]
    refine sumBits_congr fun k hk => ?_
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [show 19 + 6 = 25 from rfl] at hsp
  rw [hsp, hhi0, Nat.mul_zero, Nat.add_zero]
  unfold getBits
  refine sumBits_congr fun k hk => ?_
  have hlen : bHi19Wires.length = 19 := rfl
  have hk_b : k < bHi19Wires.length := by omega
  have hk_len : k < (bHi19Wires.map (fun w => XWire.wire w false)).length := by simp [hlen, hk]
  unfold evalXWires
  rw [List.getElem?_append_left hk_len, List.getElem?_map, List.getElem?_eq_getElem hk_b]
  dsimp only [Option.map, evalXWire]
  have hmem : bHi19Wires[k]'hk_b ∈ bHi19Wires := List.getElem_mem hk_b
  have hgetD : (bHi19Wires.map (wGet tr3a)).getD (0 + k) 0 = wGet tr3a (bHi19Wires[k]'hk_b) := by
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk_b]
    rfl
  rw [hgetD]
  generalize bHi19Wires[k]'hk_b = q at hmem ⊢
  have hw_anc : 50 ≤ q ∧ q < 100 := by
    have hall : ∀ x ∈ bHi19Wires, 50 ≤ x ∧ x < 100 := by decide
    exact hall q hmem
  rw [dite_eq_left hw_anc.2, Bool.xor_false]
  obtain ⟨hpw, hfm0⟩ := isParWire_of_anc (fMask := fMask) hw_anc.1 hw_anc.2
  exact hI.hTracked ⟨q, hw_anc.2⟩ hpw (by rw [hfm0, Nat.zero_testBit])

theorem exec_s2bOps {bit allM s4 : Nat} {fMask : Nat → Nat}
    {m1 m2a : Fin 100 → Bool} {tr2a tr2b : WTree}
    (hs4 : s4 < 16)
    (hI2a : ParInv bit allM fMask m1 tr2a m2a)
    (hfm_hi : ∀ i, 22 ≤ i → i < 24 → (fMask i).testBit bit = false)
    (hm2a_u24 : ∀ i : Nat, (hi : i < 24) → m2a ⟨25 + i, by omega⟩ = m1 ⟨25 + i, by omega⟩)
    (hm2a_62 : m2a ⟨62, by decide⟩ = false)
    (hs4_bits : ∀ b < 4, (wGet tr2a (s4Wires2b.getD b 0)).testBit bit = s4.testBit b)
    (hrot16 : ∀ k < 16,
      (sliceVal 25 24 m1).testBit (s2bSrc s4 k) = uRotBit (sliceVal 25 24 m1) s4 k)
    (hrot6 : ∀ k, 16 ≤ k → k < 22 →
      (wGet tr2b (25 + k)).testBit bit = (sliceVal 25 24 m1).testBit (s2bSrc s4 k))
    (htr2b : (checkWTreeWF 7 tr2b &&
              checkEqList tr2b [47, 48] [wGet tr2a 47, wGet tr2a 48] &&
              checkEqList tr2b (rangeList 50 50) ((rangeList 50 50).map (wGet tr2a))) = true) :
    ∃ m2b : Fin 100 → Bool,
      execList102 s2bOps m2a = some m2b ∧
      outVal102 m2b = outVal102 m2a ∧
      m2b ⟨49, by decide⟩ = m1 ⟨49, by decide⟩ ∧
      (∀ k : Nat, (hk : k < 22) →
        m2b ⟨25 + k, by omega⟩ =
          m1 ⟨25 + s2bSrc s4 k, by have := s2bSrc_lt (s4 := s4) (k := k); omega⟩) ∧
      (∀ k : Nat, (hk : k < 16) → m2b ⟨25 + k, by omega⟩ = uRotBit (sliceVal 25 24 m1) s4 k) ∧
      ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr2b m2b := by
  have hm2a_s4 :
      ∀ b < 4, ∀ hlt : s4Wires2b.getD b 0 < 100, m2a ⟨s4Wires2b.getD b 0, hlt⟩ = s4.testBit b := by
    intro b hb hlt
    have h50 : 50 ≤ s4Wires2b.getD b 0 := by
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> decide
    obtain ⟨hpw, hfm0⟩ := isParWire_of_anc (fMask := fMask) h50 hlt
    rw [hI2a.hTracked ⟨s4Wires2b.getD b 0, hlt⟩ hpw (by rw [hfm0, Nat.zero_testBit]), hs4_bits b hb]
  obtain ⟨m2b, hex2b, hnon2b, hbit2b, _⟩ :=
    checkPermSpec_sound (s2b_cert hs4) (s4TrueW_sound hm2a_s4) (s4FalseW_sound hm2a_s4 hm2a_62)
  have hm2b_49 : m2b ⟨49, by decide⟩ = m1 ⟨49, by decide⟩ :=
    (hnon2b ⟨49, by decide⟩ (Or.inr (by decide))).trans (hI2a.hFree ⟨49, by decide⟩ (Or.inr rfl))
  have hm2b_k : ∀ k : Nat, (hk : k < 22) →
      m2b ⟨25 + k, by omega⟩ =
        m1 ⟨25 + s2bSrc s4 k, by have := s2bSrc_lt (s4 := s4) (k := k); omega⟩ := by
    intro k hk
    rw [hbit2b k hk, targets2b_eval hk m2a,
      hm2a_u24 (s2bSrc s4 k) (by have := s2bSrc_lt (s4 := s4) (k := k); omega)]
  have hu_bit :
      ∀ i : Nat, (hi : i < 24) → (sliceVal 25 24 m1).testBit i = m1 ⟨25 + i, by omega⟩ := by
    intro i hi
    unfold sliceVal
    have h :=
      sumBits_testBit 24 (fun k => if hk : 25 + k < 100 then m1 ⟨25 + k, hk⟩ else false) i hi
    simpa [show 25 + i < 100 by omega] using h
  have hm2b_16 :
      ∀ k : Nat, (hk : k < 16) → m2b ⟨25 + k, by omega⟩ = uRotBit (sliceVal 25 24 m1) s4 k := by
    intro k hk
    rw [hm2b_k k (by omega),
      ← hu_bit (s2bSrc s4 k) (by have := s2bSrc_lt (s4 := s4) (k := k); omega), hrot16 k hk]
  simp only [Bool.and_eq_true] at htr2b
  obtain ⟨⟨hwf2b, heq47_48⟩, heq50⟩ := htr2b
  refine ⟨m2b, hex2b, outVal102_congr (fun j hj => hnon2b j (Or.inl hj)),
    hm2b_49, hm2b_k, hm2b_16, ?_⟩
  refine ⟨checkWTreeWF_sound 7 tr2b hwf2b, hI2a.hAll, fun _ _ => rfl, fun q hq hfm_q => ?_⟩
  obtain ⟨hq25, hq102, _, hq_cases⟩ := isParWire_bounds hq
  rcases hq_cases with hq49_lt | hq50_le
  · unfold getFMask at hfm_q
    rw [ite_eq_left hq49_lt] at hfm_q
    dsimp only at hfm_q
    by_cases hlt16 : q.val - 25 < 16
    · rw [ite_eq_left hlt16, hI2a.hAll] at hfm_q; cases hfm_q
    · by_cases hlt22 : q.val - 25 < 22
      · set k := q.val - 25
        have hqk : q = ⟨25 + k, by omega⟩ := Fin.ext (by dsimp [k]; omega)
        rw [hqk, hm2b_k k hlt22]
        dsimp only
        rw [hrot6 k (by omega) hlt22,
          hu_bit (s2bSrc s4 k) (by have := s2bSrc_lt (s4 := s4) (k := k); omega)]
      · have hq47_48 : q.val = 47 ∨ q.val = 48 := by omega
        rcases hq47_48 with h47 | h48
        · have hfin : q = ⟨47, by decide⟩ := Fin.ext h47
          have hw47 : wGet tr2b 47 = wGet tr2a 47 :=
            checkEqList_sound [47, 48] [wGet tr2a 47, wGet tr2a 48] heq47_48 0 47
              (wGet tr2a 47) rfl rfl
          have hfm47 : (getFMask fMask 47).testBit bit = false := by
            unfold getFMask; rw [ite_eq_left (by decide)]; exact hfm_hi 22 (by decide) (by decide)
          rw [hfin, hnon2b ⟨47, by decide⟩ (Or.inr (by decide)),
              hI2a.hTracked ⟨47, by decide⟩ (by decide) hfm47]
          dsimp only; rw [hw47]
        · have hfin : q = ⟨48, by decide⟩ := Fin.ext h48
          have hw48 : wGet tr2b 48 = wGet tr2a 48 :=
            checkEqList_sound [47, 48] [wGet tr2a 47, wGet tr2a 48] heq47_48 1 48
              (wGet tr2a 48) rfl rfl
          have hfm48 : (getFMask fMask 48).testBit bit = false := by
            unfold getFMask; rw [ite_eq_left (by decide)]; exact hfm_hi 23 (by decide) (by decide)
          rw [hfin, hnon2b ⟨48, by decide⟩ (Or.inr (by decide)),
              hI2a.hTracked ⟨48, by decide⟩ (by decide) hfm48]
          dsimp only; rw [hw48]
  · rw [hnon2b q (Or.inr (by omega))]
    obtain ⟨hpw, hfm0⟩ := isParWire_of_anc (fMask := fMask) hq50_le hq102
    rw [hI2a.hTracked q hpw (by rw [hfm0, Nat.zero_testBit])]
    have hget := checkEqList_rangeList_getD heq50 (q.val - 50) (by omega)
    have hlen_getD : ((rangeList 50 50).map (wGet tr2a)).getD (q.val - 50) 0 = wGet tr2a q.val := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, rangeList_getElem? (by omega)]
      simp [show 50 + (q.val - 50) = q.val by omega]
    rw [show 50 + (q.val - 50) = q.val by omega, hlen_getD] at hget
    rw [hget]

theorem exec_preOps102_slice {bit allM s4 : Nat} {fMask : Nat → Nat}
    {m1 m1a : Fin 100 → Bool} {tr0 tr2a tr2b tr2c tr3a tr3b : WTree}
    (hs4 : s4 < 16)
    (hI0 : ParInv bit allM fMask m1 tr0 m1)
    (hm1a_ge25 : ∀ w : Fin 100, 25 ≤ w.val → m1a w = m1 w)
    (hfm_hi : ∀ i, 22 ≤ i → i < 24 → (fMask i).testBit bit = false)
    (hs4_bits : ∀ b < 4, (wGet tr2a (s4Wires2b.getD b 0)).testBit bit = s4.testBit b)
    (hrot16 : ∀ k < 16,
      (sliceVal 25 24 m1).testBit (s2bSrc s4 k) = uRotBit (sliceVal 25 24 m1) s4 k)
    (hrot6 : ∀ k, 16 ≤ k → k < 22 →
      (wGet tr2b (25 + k)).testBit bit = (sliceVal 25 24 m1).testBit (s2bSrc s4 k))
    (h2a : runParSeq allM fMask [s2aCertOps] tr0
      (fun tr => beqWTree tr tr2a && checkU24Restored tr0 tr && Nat.beq (wGet tr 62) 0) = true)
    (htr2b : (checkWTreeWF 7 tr2b &&
              checkEqList tr2b [47, 48] [wGet tr2a 47, wGet tr2a 48] &&
              checkEqList tr2b (rangeList 50 50) ((rangeList 50 50).map (wGet tr2a))) = true)
    (h2c : runParSeq allM (fun i => if i < 16 then allM else 0) [s2cOps] tr2b
      (fun tr => beqWTree tr tr2c) = true)
    (h3a : runParPhaseSeq allM (fun i => if i < 16 then allM else 0) s3aAllSeq tr2c
      (fun tr => beqWTree tr tr3a && checkZeroList tr
        [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
         94, 95, 96, 97, 98]) = true)
    (h3bPost : runParPhaseSeq allM (fun i => if i < 16 then allM else 0) [s3bPostOps] tr3a
      (fun tr => beqWTree tr tr3b && checkZeroList tr clean3bOut) = true) :
    ∃ m2b m3b : Fin 100 → Bool,
      execList102 preOps102 m1a = some m3b ∧
      phaseList102 preOps102 m1a = false ∧
      m2b ⟨49, by decide⟩ = m1 ⟨49, by decide⟩ ∧
      (∀ k : Nat, (hk : k < 22) →
        m2b ⟨25 + k, by omega⟩ =
          m1 ⟨25 + s2bSrc s4 k, by have := s2bSrc_lt (s4 := s4) (k := k); omega⟩) ∧
      (∀ k : Nat, (hk : k < 16) → m2b ⟨25 + k, by omega⟩ = uRotBit (sliceVal 25 24 m1) s4 k) ∧
      (∀ w : Fin 100, w.val ∈ clean3bOut → m3b w = false) ∧
      ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr3b m3b ∧
      outVal102 m3b =
        (outVal102 m1a + getBits bit (bHi19Wires.map (wGet tr3a)) 0 19) % 33554432 := by
  have hI0a : ParInv bit allM fMask m1 tr0 m1a := hI0.congr_ge25 hm1a_ge25
  obtain ⟨tr2a', m2a, hex2a_cert, hlo2a, hI2a, hk2a⟩ := runParSeq_sound [s2aCertOps] hI0a h2a
  rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hex2a_cert
  have hex2a : execList102 s2aOps m1a = some m2a := exec_s2aOps_of_cert hex2a_cert
  simp only [Bool.and_eq_true, Nat.beq_eq] at hk2a
  obtain ⟨⟨hbeq2a, hu24_2a⟩, hz62_2a⟩ := hk2a
  rw [beqWTree_sound _ _ hbeq2a] at hI2a hu24_2a hz62_2a
  have hm2a_u24 : ∀ i : Nat, (hi : i < 24) → m2a ⟨25 + i, by omega⟩ = m1 ⟨25 + i, by omega⟩ :=
    checkU24Restored_sound hI0 hI2a hu24_2a
  have hm2a_62 : m2a ⟨62, by decide⟩ = false := by
    obtain ⟨hpw, hfm0⟩ := isParWire_of_anc (fMask := fMask) (t := 62) (by decide) (by decide)
    rw [hI2a.hTracked ⟨62, by decide⟩ hpw (by rw [hfm0, Nat.zero_testBit]),
      hz62_2a, Nat.zero_testBit]
  obtain ⟨m2b, hex2b, hout2b, hm2b_49, hm2b_k, hm2b_16, hI2b⟩ :=
    exec_s2bOps hs4 hI2a hfm_hi hm2a_u24 hm2a_62 hs4_bits hrot16 hrot6 htr2b
  obtain ⟨tr2c', m2c, hex2c, hlo2c, hI2c, hk2c⟩ := runParSeq_sound [s2cOps] hI2b h2c
  rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hex2c
  rw [beqWTree_sound _ _ hk2c] at hI2c
  obtain ⟨tr3a', m3a, hex3a, hph3a, hlo3a, hI3a, hk3a⟩ := runParPhaseSeq_sound s3aAllSeq hI2c h3a
  change execList102 s3aOps m2c = some m3a at hex3a
  change phaseList102 s3aOps m2c = false at hph3a
  simp only [Bool.and_eq_true] at hk3a
  rw [beqWTree_sound _ _ hk3a.1] at hI3a hk3a
  have hm3a_false : ∀ w : Fin 100,
      w.val ∈ [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
               94, 95, 96, 97, 98] →
      m3a w = false := by
    intro w hw
    have hall : ∀ x ∈ [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
        94, 95, 96, 97, 98], 50 ≤ x ∧ x < 100 := by
      decide
    have hr := hall w.val hw
    obtain ⟨hpw, hfm0⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) hr.1 w.isLt
    rw [hI3a.hTracked w hpw (by rw [hfm0, Nat.zero_testBit]),
        checkZeroList_sound
          [70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 87, 88, 89, 90,
           94, 95, 96, 97, 98]
          hk3a.2 w.val hw,
        Nat.zero_testBit]
  obtain ⟨m3b_mid, hex3b_add, hI3b_mid, _, hout3b_mid⟩ :=
    checkAdder25_sound (by decide : 0 ≤ 25) s3bAdd_cert hI3a (fun _ h => by cases h) hm3a_false
  unfold adderStepVal25 at hout3b_mid
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.pow_zero, Nat.one_mul, Nat.sub_zero,
    evalXWire, Bool.toNat_false, add_zero] at hout3b_mid
  rw [sumBits_bHi19Wires hI3a] at hout3b_mid
  obtain ⟨tr3b', m3b, hex3b_post, hph3b_post, hlo3b_post, hI3b, hk3b⟩ :=
    runParPhaseSeq_sound [s3bPostOps] hI3b_mid h3bPost
  rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hex3b_post hph3b_post
  simp only [Bool.and_eq_true] at hk3b
  rw [beqWTree_sound _ _ hk3b.1] at hI3b hk3b
  have hm3b_clean : ∀ w : Fin 100, w.val ∈ clean3bOut → m3b w = false := by
    intro w hw
    have hall : ∀ x ∈ clean3bOut, 50 ≤ x ∧ x < 100 := by decide
    have hbnd := hall w.val hw
    obtain ⟨hpw, hfm0⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) hbnd.1 hbnd.2
    rw [hI3b.hTracked w hpw (by rw [hfm0, Nat.zero_testBit]),
        checkZeroList_sound clean3bOut hk3b.2 w.val hw, Nat.zero_testBit]
  have hout_2a : outVal102 m2a = outVal102 m1a := outVal102_congr hlo2a
  have hout_2c : outVal102 m2c = outVal102 m2b := outVal102_congr hlo2c
  have hout_3a : outVal102 m3a = outVal102 m2c := outVal102_congr hlo3a
  have hout_3b : outVal102 m3b = outVal102 m3b_mid := outVal102_congr hlo3b_post
  refine ⟨m2b, m3b, ?_, ?_, hm2b_49, hm2b_k, hm2b_16, hm3b_clean, hI3b, ?_⟩
  · unfold preOps102 s3bOps
    rw [List.append_assoc, List.append_assoc, List.append_assoc,
        execList102_append, hex2a, Option.bind_some,
        execList102_append, hex2b, Option.bind_some,
        execList102_append, hex2c, Option.bind_some,
        execList102_append, hex3a, Option.bind_some,
        execList102_append, hex3b_add, Option.bind_some, hex3b_post]
  · unfold preOps102 s3bOps
    rw [List.append_assoc, List.append_assoc, List.append_assoc,
        phaseList102_append _ _ hex2a, phaseList102_of_noPhase _ _ noPhase_s2a, Bool.false_xor,
        phaseList102_append _ _ hex2b, phaseList102_of_noPhase _ _ noPhase_s2b, Bool.false_xor,
        phaseList102_append _ _ hex2c, phaseList102_of_noPhase _ _ noPhase_s2c, Bool.false_xor,
        phaseList102_append _ _ hex3a, hph3a, Bool.false_xor,
        phaseList102_append _ _ hex3b_add,
        phaseList102_of_noPhase _ _ noPhase_s3bAdd, Bool.false_xor,
        hph3b_post]
  · rw [hout_3b, hout3b_mid, hout_3a, hout_2c, hout2b, hout_2a]

theorem exec_s6bOps {bit allM s4 : Nat} {fMask : Nat → Nat}
    {m1 m2b m6a : Fin 100 → Bool} {tr0 tr2b tr6a tr6cIn : WTree}
    (hs4 : s4 < 16)
    (hI0 : ParInv bit allM fMask m1 tr0 m1)
    (hfm_hi : ∀ i, 22 ≤ i → i < 24 → (fMask i).testBit bit = false)
    (hm2b_49 : m2b ⟨49, by decide⟩ = m1 ⟨49, by decide⟩)
    (hm2b_k : ∀ k : Nat, (hk : k < 22) →
      m2b ⟨25 + k, by omega⟩ =
        m1 ⟨25 + s2bSrc s4 k, by have := s2bSrc_lt (s4 := s4) (k := k); omega⟩)
    (hI6a : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr6a m6a)
    (hm6a_62 : m6a ⟨62, by decide⟩ = false)
    (hs4_bits6a : ∀ b < 4, (wGet tr6a (s4Wires6b.getD b 0)).testBit bit = s4.testBit b)
    (heq41 : checkEqList tr6a (rangeList 41 6) ((rangeList 41 6).map (wGet tr2b)) = true)
    (heq47_48 : checkEqList tr6a [47, 48] [wGet tr0 47, wGet tr0 48] = true)
    (hrot6 : ∀ k, 16 ≤ k → k < 22 →
      (wGet tr2b (25 + k)).testBit bit = (sliceVal 25 24 m1).testBit (s2bSrc s4 k))
    (htr6cIn : (checkWTreeWF 7 tr6cIn &&
                checkEqList tr6cIn (rangeList 25 24) ((rangeList 25 24).map (wGet tr0)) &&
                checkEqList tr6cIn (rangeList 50 50) ((rangeList 50 50).map (wGet tr6a))) = true) :
    ∃ m6b : Fin 100 → Bool,
      execList102 s6bOps m6a = some m6b ∧
      outVal102 m6b = outVal102 m6a ∧
      ParInv bit allM fMask m1 tr6cIn m6b := by
  have hm6a_s4 :
      ∀ b < 4, ∀ hlt : s4Wires6b.getD b 0 < 100, m6a ⟨s4Wires6b.getD b 0, hlt⟩ = s4.testBit b := by
    intro b hb hlt
    have h50 : 50 ≤ s4Wires6b.getD b 0 := by
      rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> decide
    obtain ⟨hpw, hfm0⟩ := isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) h50 hlt
    rw [hI6a.hTracked ⟨s4Wires6b.getD b 0, hlt⟩ hpw (by rw [hfm0, Nat.zero_testBit]),
      hs4_bits6a b hb]
  obtain ⟨m6b, hex6b, hnon6b, hbit6b, _⟩ :=
    checkPermSpec_sound (s6b_cert hs4) (s4TrueW_sound hm6a_s4) (s4FalseW_sound hm6a_s4 hm6a_62)
  have hu_bit :
      ∀ i : Nat, (hi : i < 24) → (sliceVal 25 24 m1).testBit i = m1 ⟨25 + i, by omega⟩ := by
    intro i hi
    unfold sliceVal
    have h :=
      sumBits_testBit 24 (fun k => if hk : 25 + k < 100 then m1 ⟨25 + k, hk⟩ else false) i hi
    simpa [show 25 + i < 100 by omega] using h
  have hm6a_k : ∀ k : Nat, (hk : k < 22) →
      m6a ⟨25 + k, by omega⟩ =
        m1 ⟨25 + s2bSrc s4 k, by have := s2bSrc_lt (s4 := s4) (k := k); omega⟩ := by
    intro k hk
    by_cases hk16 : k < 16
    · have hcond : (25 ≤ (⟨25 + k, by omega⟩ : Fin 100).val ∧
          (⟨25 + k, by omega⟩ : Fin 100).val < 49 ∧
          ((fun i => if i < 16 then allM else 0)
            ((⟨25 + k, by omega⟩ : Fin 100).val - 25)).testBit bit = true) ∨
          (⟨25 + k, by omega⟩ : Fin 100).val = 49 := by
        left
        dsimp only
        refine ⟨by omega, by omega, ?_⟩
        rw [Nat.add_sub_cancel_left, ite_eq_left hk16]
        exact hI6a.hAll
      have hfr : m6a ⟨25 + k, by omega⟩ = m2b ⟨25 + k, by omega⟩ :=
        hI6a.hFree ⟨25 + k, by omega⟩ hcond
      rw [hfr, hm2b_k k hk]
    · have hpw : isParWire (25 + k) = true := by
        unfold isParWire
        simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
        omega
      have hfm : (getFMask (fun i => if i < 16 then allM else 0) (25 + k)).testBit bit = false := by
        unfold getFMask
        rw [ite_eq_left (by omega)]
        change (if 25 + k - 25 < 16 then allM else 0).testBit bit = false
        rw [Nat.add_sub_cancel_left, ite_eq_right hk16, Nat.zero_testBit]
      rw [hI6a.hTracked ⟨25 + k, by omega⟩ hpw hfm]
      dsimp only
      have hget := checkEqList_rangeList_getD heq41 (k - 16) (by omega)
      have hlen_getD : ((rangeList 41 6).map (wGet tr2b)).getD (k - 16) 0 = wGet tr2b (25 + k) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, rangeList_getElem? (by omega)]
        simp [show 41 + (k - 16) = 25 + k by omega]
      rw [show 41 + (k - 16) = 25 + k by omega, hlen_getD] at hget
      rw [hget, hrot6 k (by omega) hk,
        hu_bit (s2bSrc s4 k) (by have := s2bSrc_lt (s4 := s4) (k := k); omega)]
  have hm6b_u22 : ∀ j : Nat, (hj : j < 22) → m6b ⟨25 + j, by omega⟩ = m1 ⟨25 + j, by omega⟩ := by
    intro j hj
    obtain ⟨hsrc_lt, hsrc_eq⟩ := s6bSrc_spec hs4 hj
    rw [hbit6b j hj, targets6b_eval hj hs4 m6a, hm6a_k (s6bSrc s4 j) hsrc_lt]
    congr 1; exact Fin.ext (by dsimp; omega)
  have hm6b_u24 : ∀ j : Nat, (hj : j < 24) → m6b ⟨25 + j, by omega⟩ = m1 ⟨25 + j, by omega⟩ := by
    intro j hj
    by_cases hj22 : j < 22
    · exact hm6b_u22 j hj22
    · rcases (by omega : j = 22 ∨ j = 23) with rfl | rfl
      · rw [hnon6b ⟨47, by decide⟩ (Or.inr (by decide))]
        have hfm_rot : (getFMask (fun i => if i < 16 then allM else 0) 47).testBit bit = false := by
          unfold getFMask
          rw [ite_eq_left (by decide)]
          change (if 47 - 25 < 16 then allM else 0).testBit bit = false
          rw [ite_eq_right (by decide), Nat.zero_testBit]
        have hfm0 : (getFMask fMask 47).testBit bit = false := by
          unfold getFMask; rw [ite_eq_left (by decide)]; exact hfm_hi 22 (by decide) (by decide)
        have hw47 : wGet tr6a 47 = wGet tr0 47 :=
          checkEqList_sound [47, 48] [wGet tr0 47, wGet tr0 48] heq47_48 0 47 (wGet tr0 47) rfl rfl
        rw [hI6a.hTracked ⟨47, by decide⟩ (by decide) hfm_rot,
            hI0.hTracked ⟨47, by decide⟩ (by decide) hfm0]
        dsimp only; rw [hw47]
      · rw [hnon6b ⟨48, by decide⟩ (Or.inr (by decide))]
        have hfm_rot : (getFMask (fun i => if i < 16 then allM else 0) 48).testBit bit = false := by
          unfold getFMask
          rw [ite_eq_left (by decide)]
          change (if 48 - 25 < 16 then allM else 0).testBit bit = false
          rw [ite_eq_right (by decide), Nat.zero_testBit]
        have hfm0 : (getFMask fMask 48).testBit bit = false := by
          unfold getFMask; rw [ite_eq_left (by decide)]; exact hfm_hi 23 (by decide) (by decide)
        have hw48 : wGet tr6a 48 = wGet tr0 48 :=
          checkEqList_sound [47, 48] [wGet tr0 47, wGet tr0 48] heq47_48 1 48 (wGet tr0 48) rfl rfl
        rw [hI6a.hTracked ⟨48, by decide⟩ (by decide) hfm_rot,
            hI0.hTracked ⟨48, by decide⟩ (by decide) hfm0]
        dsimp only; rw [hw48]
  simp only [Bool.and_eq_true] at htr6cIn
  obtain ⟨⟨hwf6c, heq25⟩, heq50⟩ := htr6cIn
  refine ⟨m6b, hex6b, outVal102_congr (fun j hj => hnon6b j (Or.inl hj)), ?_⟩
  refine ⟨checkWTreeWF_sound 7 tr6cIn hwf6c, hI0.hAll, ?_, ?_⟩
  · intro w hw
    rcases hw with ⟨h25, h49, _⟩ | h49_eq
    · have hfin : w = ⟨25 + (w.val - 25), by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hfin, hm6b_u24 (w.val - 25) (by omega)]
    · have hfin : w = ⟨49, by decide⟩ := Fin.ext h49_eq
      rw [hfin, hnon6b ⟨49, by decide⟩ (Or.inr (by decide)),
          hI6a.hFree ⟨49, by decide⟩ (Or.inr rfl), hm2b_49]
  · intro q hq hfm_q
    obtain ⟨hq25, hq102, _, hq_cases⟩ := isParWire_bounds hq
    rcases hq_cases with hq49_lt | hq50_le
    · have hfin : q = ⟨25 + (q.val - 25), by omega⟩ := Fin.ext (by dsimp; omega)
      have hget := checkEqList_rangeList_getD heq25 (q.val - 25) (by omega)
      have hlen_getD : ((rangeList 25 24).map (wGet tr0)).getD (q.val - 25) 0 = wGet tr0 q.val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, rangeList_getElem? (by omega)]
        simp [show 25 + (q.val - 25) = q.val by omega]
      rw [show 25 + (q.val - 25) = q.val by omega, hlen_getD] at hget
      rw [hfin, hm6b_u24 (q.val - 25) (by omega), ← hfin, hI0.hTracked q hq hfm_q, hget]
    · rw [hnon6b q (Or.inr (by omega))]
      obtain ⟨hpw, hfm0⟩ :=
        isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) hq50_le hq102
      rw [hI6a.hTracked q hpw (by rw [hfm0, Nat.zero_testBit])]
      have hget := checkEqList_rangeList_getD heq50 (q.val - 50) (by omega)
      have hlen_getD :
          ((rangeList 50 50).map (wGet tr6a)).getD (q.val - 50) 0 = wGet tr6a q.val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, rangeList_getElem? (by omega)]
        simp [show 50 + (q.val - 50) = q.val by omega]
      rw [show 50 + (q.val - 50) = q.val by omega, hlen_getD] at hget
      rw [hget]

theorem exec_postOps102_slice {bit allM s4 : Nat} {fMask : Nat → Nat}
    {m1 m2b m53 : Fin 100 → Bool} {tr0 tr2b tr54In tr54Out tr6a tr6cIn : WTree}
    (hs4 : s4 < 16)
    (hI0 : ParInv bit allM fMask m1 tr0 m1)
    (hfm_hi : ∀ i, 22 ≤ i → i < 24 → (fMask i).testBit bit = false)
    (hm2b_49 : m2b ⟨49, by decide⟩ = m1 ⟨49, by decide⟩)
    (hm2b_k : ∀ k : Nat, (hk : k < 22) →
      m2b ⟨25 + k, by omega⟩ =
        m1 ⟨25 + s2bSrc s4 k, by have := s2bSrc_lt (s4 := s4) (k := k); omega⟩)
    (hs4_bits6a : ∀ b < 4, (wGet tr6a (s4Wires6b.getD b 0)).testBit bit = s4.testBit b)
    (hrot6 : ∀ k, 16 ≤ k → k < 22 →
      (wGet tr2b (25 + k)).testBit bit = (sliceVal 25 24 m1).testBit (s2bSrc s4 k))
    (hI53 : ParInv bit allM (fun i => if i < 16 then allM else 0) m2b tr54In m53)
    (h54 : runParSeq allM (fun i => if i < 16 then allM else 0) s5_4Seq tr54In
      (fun tr => beqWTree tr tr54Out) = true)
    (h6a : runParSeq allM (fun i => if i < 16 then allM else 0) [s6aOps] tr54Out
      (fun tr => beqWTree tr tr6a &&
                 Nat.beq (wGet tr 62) 0 &&
                 checkEqList tr (rangeList 41 6) ((rangeList 41 6).map (wGet tr2b)) &&
                 checkEqList tr [47, 48] [wGet tr0 47, wGet tr0 48]) = true)
    (htr6cIn : (checkWTreeWF 7 tr6cIn &&
                checkEqList tr6cIn (rangeList 25 24) ((rangeList 25 24).map (wGet tr0)) &&
                checkEqList tr6cIn (rangeList 50 50) ((rangeList 50 50).map (wGet tr6a))) = true)
    (h6c : runParSeq allM fMask [s6cOps] tr6cIn
      (fun tr => beqWTree tr tr0 &&
                 checkU24Restored tr0 tr &&
                 checkZeroList tr zAnc52) = true) :
    ∃ m6c : Fin 100 → Bool,
      execList102 postOps102 m53 = some m6c ∧
      (∀ w : Fin 100, 25 ≤ w.val → m6c w = m1 w) ∧
      outVal102 m6c = outVal102 m53 := by
  obtain ⟨tr54', m54, hex54, hlo54, hI54, hk54⟩ := runParSeq_sound s5_4Seq hI53 h54
  change execList102 s5_4Ops m53 = some m54 at hex54
  rw [beqWTree_sound _ _ hk54] at hI54
  obtain ⟨tr6a', m6a, hex6a, hlo6a, hI6a, hk6a⟩ := runParSeq_sound [s6aOps] hI54 h6a
  rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hex6a
  simp only [Bool.and_eq_true, Nat.beq_eq] at hk6a
  obtain ⟨⟨⟨hbeq6a, hz62_6a⟩, heq41⟩, heq47_48⟩ := hk6a
  rw [beqWTree_sound _ _ hbeq6a] at hI6a hz62_6a heq41 heq47_48
  have hm6a_62 : m6a ⟨62, by decide⟩ = false := by
    obtain ⟨hpw, hfm0⟩ :=
      isParWire_of_anc (fMask := fun i => if i < 16 then allM else 0) (t := 62)
        (by decide) (by decide)
    rw [hI6a.hTracked ⟨62, by decide⟩ hpw (by rw [hfm0, Nat.zero_testBit]),
      hz62_6a, Nat.zero_testBit]
  obtain ⟨m6b, hex6b, hout6b, hI6b⟩ :=
    exec_s6bOps hs4 hI0 hfm_hi hm2b_49 hm2b_k hI6a hm6a_62 hs4_bits6a heq41 heq47_48 hrot6 htr6cIn
  obtain ⟨tr6c', m6c, hex6c, hlo6c, hI6c, hk6c⟩ := runParSeq_sound [s6cOps] hI6b h6c
  rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hex6c
  simp only [Bool.and_eq_true] at hk6c
  obtain ⟨⟨hbeq6c, hu24_6c⟩, hz52_6c⟩ := hk6c
  rw [beqWTree_sound _ _ hbeq6c] at hI6c hu24_6c hz52_6c
  have hm6c_u24 : ∀ i : Nat, (hi : i < 24) → m6c ⟨25 + i, by omega⟩ = m1 ⟨25 + i, by omega⟩ :=
    checkU24Restored_sound hI0 hI6c hu24_6c
  have hm6c_ge25 : ∀ w : Fin 100, 25 ≤ w.val → m6c w = m1 w := by
    intro w hw
    by_cases hw49 : w.val < 49
    · have hfin : w = ⟨25 + (w.val - 25), by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hfin, hm6c_u24 (w.val - 25) (by omega)]
    · by_cases hw_eq49 : w.val = 49
      · have hfin : w = ⟨49, by decide⟩ := Fin.ext hw_eq49
        rw [hfin, hI6c.hFree ⟨49, by decide⟩ (Or.inr rfl)]
      · obtain ⟨hpw, hfm0⟩ := isParWire_of_anc (fMask := fMask) (by omega) w.isLt
        have hmem : w.val ∈ zAnc52 := mem_zAnc52_iff.mpr ⟨by omega, w.isLt⟩
        rw [hI6c.hTracked w hpw (by rw [hfm0, Nat.zero_testBit]),
            hI0.hTracked w hpw (by rw [hfm0, Nat.zero_testBit])]
  have hout54 : outVal102 m54 = outVal102 m53 := outVal102_congr hlo54
  have hout6a : outVal102 m6a = outVal102 m54 := outVal102_congr hlo6a
  have hout6c : outVal102 m6c = outVal102 m6b := outVal102_congr hlo6c
  refine ⟨m6c, ?_, hm6c_ge25, ?_⟩
  · unfold postOps102
    rw [List.append_assoc, List.append_assoc,
        execList102_append, hex54, Option.bind_some,
        execList102_append, hex6a, Option.bind_some,
        execList102_append, hex6b, Option.bind_some, hex6c]
  · rw [hout6c, hout6b, hout6a, hout54]


end QuantumComputation.Specs.ArcsinImpl
