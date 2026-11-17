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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SplitRouterNuc47Elec187

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

-- kinetic phase brackets
attribute [irreducible] QuantumComputation.Specs.PhotochemistrySolution.KineticFast.pKinMidPre8CP

noncomputable section
set_option autoImplicit false
namespace QuantumComputation.Specs.PhotochemistrySolution.Kinetic664

open Operator QProg DynamicCircuit Matrix Circuit Qubit QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.Stage4Kin14Scb
  PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.KineticFast
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (czCircuit bitSign)
set_option allowUnsafeReducibility true in
attribute [local semireducible] StructuredCB.validProgMask StructuredCB.finalCleanMask

theorem ifPosSqf {α : Sort*} {c : Prop} {h : Decidable c} (hc : c) {a b : α} : @ite α c h a b = a :=
    ite_eq_left hc
theorem ifNegSqf {α : Sort*} {c : Prop} {h : Decidable c} (hc : ¬c) {a b : α} : @ite α c h a b =
    b := ite_eq_right hc
theorem difPosSqf {α : Sort*} {c : Prop} {h : Decidable c} (hc : c) {a : c → α}
    {b : ¬c → α} : @dite α c h a b = a hc := dite_eq_left hc
theorem difNegSqf {α : Sort*} {c : Prop} {h : Decidable c} (hc : ¬c) {a : c → α}
    {b : ¬c → α} : @dite α c h a b = b hc := dite_eq_right hc
/-- Clean-target mask of all 16 `andGate` ancillas `[24,28,31,34,37,40,43,46,50..68,69]`. -/
def sMask16SqFree : ℕ := 927607621570808250368
/-- Complement mask (in `0..225`) of wires touched by `pCmpU2CP` (`0..7, 15..21, 47..68`). -/
def mAvoidCmpU2 : ℕ :=
  107839786668602559178668060348078522694548577689571994254793219538688
/-- Second unsigned 7-bit uniform coin read from wires `15..21` of `Wire 226`. -/
def m7U2OfBits (β : BitAssignment 226) : ℕ :=
  prefixSum (fun i ↦ β (wKin (15 + i))) 7
/-- Clean 7-carry two's-complement comparator `|k| ≤ U2` (`15..21`) into wire `68`. -/
def pCmpU2CP : ComputeProg 226 :=
  seqCP226
    [gx226 47, gc226 7 47, gc226 47 48, gc226 0 48, gc226 15 49, gc226 47 48, gc226 47 49,
     ga226 48 49 50, gc226 47 50, gc226 47 51, gc226 1 51, gc226 16 52, gc226 50 51,
     gc226 50 52, ga226 51 52 53, gc226 50 53, gc226 47 54, gc226 2 54, gc226 17 55,
     gc226 53 54, gc226 53 55, ga226 54 55 56, gc226 53 56, gc226 47 57, gc226 3 57,
     gc226 18 58, gc226 56 57, gc226 56 58, ga226 57 58 59, gc226 56 59, gc226 47 60,
     gc226 4 60, gc226 19 61, gc226 59 60, gc226 59 61, ga226 60 61 62, gc226 59 62,
     gc226 47 63, gc226 5 63, gc226 20 64, gc226 62 63, gc226 62 64, ga226 63 64 65,
     gc226 62 65, gc226 47 66, gc226 6 66, gc226 21 67, gc226 65 66, gc226 65 67,
     ga226 66 67 68, gc226 65 68]
/-- Combine `|k| ≤ U1` (`46`) and `|k| ≤ U2` (`68`) into `1 + [U1 < |k|] * [U2 < |k|]` on `69`. -/
def pCombineSqFreeCP : ComputeProg 226 :=
  .seq (.seq (.seq (gx226 46) (gx226 68)) (ga226 46 68 69)) (gx226 69)
/-- 15-AND compute program producing `1 + [U1 < |k|] * [U2 < |k|]` on wire `69`. -/
def pKinMidPre16SqFreeCP : ComputeProg 226 :=
  .seq (.seq pKinMidPre8CP pCmpU2CP) pCombineSqFreeCP
/-- Full 16-AND (`64 T`, `-104 T/step`) square-free 2-coin kinetic compute program. -/
def pKinPre16SqFreeCP : ComputeProg 226 := .seq pKinMidPre16SqFreeCP (ga226 22 69 24)
def cpTargetMask226 : ComputeProg 226 → ℕ
  | .id => 0
  | .x u => 1 <<< u.val
  | .cnot _ tw _ => 1 <<< tw.val
  | .andGate _ _ a _ _ _ => 1 <<< a.val
  | .seq p₁ p₂ => cpTargetMask226 p₁ ||| cpTargetMask226 p₂

theorem fwdBits_not_targetMask :
    ∀ {p : ComputeProg 226} (β : BitAssignment 226) (w : Wire 226),
      (cpTargetMask226 p).testBit w.val = false → p.fwdBits β w = β w
  | .id, _, _, _ => rfl
  | .x u, β, w, hh =>
        Function.update_of_ne (fun e ↦ by simp [e, cpTargetMask226, Nat.shiftLeft_eq] at hh) _ β
  | .cnot _ tw _, β, w, hh =>
        Function.update_of_ne (fun e ↦ by simp [e, cpTargetMask226, Nat.shiftLeft_eq] at hh) _ β
  | .andGate _ _ a _ _ _, β, w, hh =>
        Function.update_of_ne (fun e ↦ by simp [e, cpTargetMask226, Nat.shiftLeft_eq] at hh) _ β
  | .seq p₁ _, β, w, hh => by
      rw [cpTargetMask226, Nat.testBit_or, Bool.or_eq_false_iff] at hh
      exact (fwdBits_not_targetMask (p₁.fwdBits β) w hh.2).trans (fwdBits_not_targetMask β w hh.1)

/-- Initial `32,768`-lane tree for `pCmpU2CP` (`15..21` = `q`, `0..7` = `k`). -/
def initCmpU2 : LTreeW0 :=
  let t0 := ltreeZeroW0 8
  let t1 :=
      List.foldl (fun t i ↦ t.set 8 (15 + i) (walshMaskW0 i (14 - i))) t0 [0, 1, 2, 3, 4, 5, 6]
  List.foldl (fun t i ↦ t.set 8 i (walshMaskW0 (7 + i) (7 - i)))
    t1 [0, 1, 2, 3, 4, 5, 6, 7]

theorem pKinPre16SqFree_props : pKinPre16SqFreeCP.numAnd = 16 ∧
    StructuredCB.validProgMask 0 sMask16SqFree pKinPre16SqFreeCP = true ∧
    avoids226 (2 ^ wLocQ226.val) pKinPre16SqFreeCP = true ∧ avoids226 mKeep pKinMidPre16SqFreeCP =
        true ∧
    avoids226 mAvoidCmpU2 pCmpU2CP = true ∧
        ((evalLanesW0 ((1 <<< 32768) - 1) pCmpU2CP initCmpU2).get 8 68 == expectedCmpMaskW0) =
        true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩

theorem initCmpU2_get_eq (lane : ℕ) (hl : lane < 32768)
    (w : Wire 226) : (initCmpU2.get 8 w.val).testBit lane =
    if w.val < 8 then lane.testBit (7 + w.val) else if 15 ≤ w.val ∧ w.val <
        22 then lane.testBit (w.val - 15) else false := by
  rw [(show ∀ u : Wire 226, initCmpU2.get 8 u.val = if u.val < 8 then walshMaskW0 (7 + u.val)
      (7 - u.val)
      else if 15 ≤ u.val ∧ u.val < 22 then walshMaskW0 (u.val - 15)
          (29 - u.val) else 0 by decide +kernel) w]
  split_ifs with h8 h22
  · exact walshMaskW0_low _ _ lane (congrArg (2 ^ ·)
        (show 15 = 7 + w.val + 1 + (7 - w.val) by omega) ▸ hl)
  · exact walshMaskW0_low _ _ lane (congrArg (2 ^ ·)
        (show 15 = w.val - 15 + 1 + (29 - w.val) by omega) ▸ hl)
  · exact Nat.zero_testBit lane

theorem cmpU2_rawBit_eq_decide_le (β : BitAssignment 226) (hclean : ∀ w : Wire 226, 47 ≤ w.val →
    w.val ≤ 68 → β w = 0) :
    pCmpU2CP.fwdBits β (wKin 68) = if (twosComplement_frozen (kOfBits8 β)).natAbs ≤
        m7U2OfBits β then 1 else 0 := by
  have hq : m7U2OfBits β < 128 := prefixSum_lt _ 7
  have hk : (kOfBits8 β).val < 256 := (kOfBits8 β).isLt
  let lane := m7U2OfBits β + 128 * (kOfBits8 β).val
  have hl : lane < 32768 := by omega
  set βL : BitAssignment 226 := fun w ↦ if (initCmpU2.get 8 w.val).testBit lane then 1 else 0
  have hβL (w) : (initCmpU2.get 8 w.val).testBit lane = (βL w == 1) :=
    Bool.rec (motive := fun b ↦ b = ((if b then (1 : ZMod 2) else 0) == 1)) rfl rfl _
  have hAgree (w : Wire 226) (hw : mAvoidCmpU2.testBit w.val = false) : β w = βL w := by
    dsimp only [βL]
    rw [initCmpU2_get_eq lane hl w]
    have hqk := lane_q_k_testBit (k := (kOfBits8 β).val) hq
    by_cases h8 : w.val < 8
    · rw [ifPosSqf h8, hqk.2 w.val, kOfBits8_val, prefixSum_testBit_lt 8 _ w.val h8,
          show wKin w.val = w from Fin.ext (wKin_val_eq w.isLt)]
      rcases DynCircExt.bit_cases (β w) with hb | hb <;> simp [hb]
    · rw [ifNegSqf h8]
      by_cases h22 : 15 ≤ w.val ∧ w.val < 22
      · rw [ifPosSqf h22, hqk.1 (w.val - 15) (by omega), m7U2OfBits,
            prefixSum_testBit_lt 7 _ (w.val - 15) (by omega),
            show wKin (15 + (w.val - 15)) =
                w from Fin.ext ((wKin_val_eq (by omega)).trans (by omega))]
        rcases DynCircExt.bit_cases (β w) with hb | hb <;> simp [hb]
      · rw [ifNegSqf h22]
        exact ((by decide +kernel : ∀ u < 226, mAvoidCmpU2.testBit u = false → u < 8 ∨
            (15 ≤ u ∧ u < 22) ∨ (47 ≤ u ∧ u ≤ 68))
          w.val w.isLt hw).elim (fun h1 ↦ absurd h1 h8) fun h ↦
              h.elim (fun h2 ↦ absurd h2 h22) fun h34 ↦ hclean w h34.1 h34.2
  have hEval := evalLanesW0_testBit hl pCmpU2CP initCmpU2 βL hβL (wKin 68)
  rw [show (wKin 68).val = 68 from rfl, beq_iff_eq.mp pKinPre16SqFree_props.2.2.2.2.2,
      expectedCmpMaskW0_testBit hq hk, ← tcAbs8W0_eq (kOfBits8 β)] at hEval
  rw [(fwdBits_avoids mAvoidCmpU2 pCmpU2CP pKinPre16SqFree_props.2.2.2.2.1).1 β βL hAgree (wKin 68)
      (by decide +kernel)]
  rcases DynCircExt.bit_cases (pCmpU2CP.fwdBits βL (wKin 68)) with hb | hb <;>
    simp_all [show ((0 : ZMod 2) == 1) = false from rfl]

theorem prefixSum_congr_lt :
    ∀ (n : ℕ) (f g : ℕ → ZMod 2), (∀ i < n, f i = g i) → prefixSum f n = prefixSum g n
  | 0, _, _, _ => rfl
  | n + 1, f, g, hh => by
      rw [prefixSum, prefixSum, prefixSum_congr_lt n f g fun i hi ↦ hh i (by omega),
          hh n (Nat.lt_succ_self n)]

def cpWiresLt70 : ComputeProg 226 → Bool
  | .id => true
  | .x u => Nat.ble (u.val + 1) 70
  | .cnot c tgt _ => Nat.ble (c.val + 1) 70 && Nat.ble (tgt.val + 1) 70
  | .andGate c₁ c₂ a _ _ _ =>
      Nat.ble (c₁.val + 1) 70 && Nat.ble (c₂.val + 1) 70 && Nat.ble (a.val + 1) 70
  | .seq p₁ p₂ => cpWiresLt70 p₁ && cpWiresLt70 p₂

theorem computeProgWires_of_lt70 :
    ∀ {p : ComputeProg 226}, cpWiresLt70 p = true →
      ComputeProgWires (fun w : Wire 226 ↦ w.val < 70) p
  | .id, _ => trivial
  | .x _, hb => Nat.le_of_ble_eq_true hb
  | .cnot _ _ _, hb =>
        ⟨Nat.le_of_ble_eq_true (Bool.and_eq_true_iff.mp hb).1,
        Nat.le_of_ble_eq_true (Bool.and_eq_true_iff.mp hb).2⟩
  | .andGate _ _ _ _ _ _, hb => let ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp hb
      ⟨Nat.le_of_ble_eq_true (Bool.and_eq_true_iff.mp h12).1,
       Nat.le_of_ble_eq_true (Bool.and_eq_true_iff.mp h12).2, Nat.le_of_ble_eq_true h3⟩
  | .seq _ _, hb =>
        ⟨computeProgWires_of_lt70 (Bool.and_eq_true_iff.mp hb).1,
        computeProgWires_of_lt70 (Bool.and_eq_true_iff.mp hb).2⟩

def cnot226_2m1 (c tw : ℕ) (hc : c < 226 := by decide) (ht : tw < 226 := by decide)
    (hne : (⟨c, hc⟩ : Wire 226) ≠ ⟨tw, ht⟩ := by decide) : ComputeProg 226 :=
  .cnot ⟨c, hc⟩ ⟨tw, ht⟩ hne
def and226_2m1 (c₁ c₂ a : ℕ) (h₁ : c₁ < 226 := by decide) (h₂ : c₂ < 226 := by decide)
    (ha : a < 226 := by decide)
    (h₁₂ : (⟨c₁, h₁⟩ : Wire 226) ≠ ⟨c₂, h₂⟩ := by decide)
    (h₁a : (⟨c₁, h₁⟩ : Wire 226) ≠ ⟨a, ha⟩ := by decide)
    (h₂a : (⟨c₂, h₂⟩ : Wire 226) ≠ ⟨a, ha⟩ := by decide) : ComputeProg 226 :=
  .andGate ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ ⟨a, ha⟩ h₁₂ h₁a h₂a
def pCoin2m1AndCP : ComputeProg 226 :=
    seqCP226 [and226_2m1 8 15 25, and226_2m1 9 16 26, and226_2m1 10 17 27, and226_2m1 11 18 28,
    and226_2m1 12 19 29, and226_2m1 13 20 30, and226_2m1 14 21 31]
def pCoin2m1SufCP : ComputeProg 226 :=
    seqCP226 [cnot226_2m1 31 30, cnot226_2m1 30 29, cnot226_2m1 29 28, cnot226_2m1 28 27,
    cnot226_2m1 27 26, cnot226_2m1 26 25]
def pCoin2m1OutCP : ComputeProg 226 :=
    seqCP226 [cnot226_2m1 8 15, cnot226_2m1 25 15, cnot226_2m1 9 16, cnot226_2m1 26 16,
    cnot226_2m1 10 17, cnot226_2m1 27 17, cnot226_2m1 11 18, cnot226_2m1 28 18, cnot226_2m1 12 19,
    cnot226_2m1 29 19, cnot226_2m1 13 20, cnot226_2m1 30 20, cnot226_2m1 14 21, cnot226_2m1 31 21]
def pCoin2m1CP : ComputeProg 226 :=
  .seq (.seq pCoin2m1AndCP pCoin2m1SufCP) pCoin2m1OutCP
/-- Recursive value of the `(2m + 1)`-weighted 7-bit carry-OR coin combiner. -/
def coin2m1Val : ℕ → ZMod 2 → (ℕ → ZMod 2) → (ℕ → ZMod 2) → ℕ
  | 0, _, _, _ => 0
  | k + 1, c, u, v =>
      let s := c + u k * v k
      coin2m1Val k s u v + (if u k + v k + s = 1 then 2 ^ k else 0)

theorem coin2m1Val_congr :
    ∀ (k : ℕ) (c : ZMod 2) {u₁ u₂ v₁ v₂ : ℕ → ZMod 2},
      (∀ i < k, u₁ i = u₂ i) → (∀ i < k, v₁ i = v₂ i) →
      coin2m1Val k c u₁ v₁ = coin2m1Val k c u₂ v₂
  | 0, _, _, _, _, _, _, _ => rfl
  | k + 1, c, u₁, u₂, v₁, v₂, hu, hv => by
      dsimp only [coin2m1Val]
      rw [hu k (Nat.lt_succ_self k), hv k (Nat.lt_succ_self k),
          coin2m1Val_congr k _ (fun i hi ↦ hu i (Nat.lt_succ_of_lt hi))
              (fun i hi ↦ hv i (Nat.lt_succ_of_lt hi))]

theorem zmod2_val_mul_pow (x : ZMod 2) (k : ℕ) : x.val * 2 ^ k = if x = 1 then 2 ^ k else 0 := by
  fin_cases x <;> first | exact Nat.zero_mul _ | exact Nat.one_mul _

theorem m7U2OfBits_pCoin2m1CP (β : BitAssignment 226) (hclean : ∀ w : Wire 226, 25 ≤ w.val → w.val ≤
    31 → β w = 0) :
    m7U2OfBits (pCoin2m1CP.fwdBits β) = coin2m1Val 7 0 (fun i ↦ β (wKin (8 + i)))
        (fun i ↦ β (wKin (15 + i))) := by
  let β₁ := pCoin2m1AndCP.fwdBits β; let β₂ := pCoin2m1SufCP.fwdBits β₁;
  let β₃ := pCoin2m1OutCP.fwdBits β₂
  have hβ₁ : ∀ k : Fin 7, β₁ ⟨25 + k.val, by omega⟩ = β (wKin (8 + k.val)) * β (wKin (15 + k.val))
      := fun k ↦ by
    fin_cases k <;>
      simp only [pCoin2m1AndCP, and226_2m1, Fin.reduceFinMk, Fin.isValue, seqCP226,
        List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceDiv,
        List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
        Order.lt_two_iff, zero_le, Nat.div_self, ComputeProg.fwdBits, ne_eq, Fin.reduceEq,
        not_false_eq_true, Function.update_of_ne, add_zero, Function.update_self, wKin, finMod,
        Nat.reduceMod, add_eq_right, β₁] <;>
      exact hclean _ (by decide) (by decide)
  have hβ₂_lo (w : Wire 226) (hw : w.val < 22) : β₂ w = β w := fwdBits_not_targetMask β w
    ((by decide +kernel : ∀ u < 22, (cpTargetMask226 (.seq pCoin2m1AndCP pCoin2m1SufCP)).testBit u =
        false) w.val hw)
  let step (a : ZMod 2) (m : ℕ) : ZMod 2 := a + β (wKin (8 + m)) * β (wKin (15 + m))
  let sc : ℕ → ZMod 2 := fun
    | 0 => 0 | 1 => step 0 6 | 2 => step (step 0 6) 5 | 3 => step (step (step 0 6) 5) 4
    | 4 => step (step (step (step 0 6) 5) 4) 3 | 5 => step (step (step (step (step 0 6) 5) 4) 3) 2
    | 6 => step (step (step (step (step (step 0 6) 5) 4) 3) 2) 1
    | _ => step (step (step (step (step (step (step 0 6) 5) 4) 3) 2) 1) 0
  have hβ₂ : ∀ k : Fin 7, β₂ ⟨25 + k.val, by omega⟩ = sc (7 - k.val) := fun k ↦ by
    fin_cases k <;>
      simp only [pCoin2m1SufCP, cnot226_2m1, Fin.reduceFinMk, Fin.isValue, seqCP226,
        List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceDiv,
        List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
        Order.lt_two_iff, zero_le, Nat.div_self, ComputeProg.fwdBits, ne_eq, Fin.reduceEq,
        not_false_eq_true, Function.update_of_ne, Function.update_self, add_zero, finMod,
        Nat.reduceMod, tsub_zero, Nat.add_one_sub_one, Nat.reduceSub, β₂, sc, step] <;>
      (repeat' (first | erw [hβ₁ 0] | erw [hβ₁ 1] | erw [hβ₁ 2] | erw [hβ₁ 3] | erw [hβ₁ 4]
                      | erw [hβ₁ 5] | erw [hβ₁ 6])) <;> simp [wKin, finMod] <;> ring
  have hOut : ∀ k : Fin 7, β₃ (wKin (15 + k.val)) = β (wKin (8 + k.val)) + β (wKin (15 + k.val)) +
      sc (7 - k.val) := fun k ↦ by
    fin_cases k <;>
      simp only [pCoin2m1OutCP, cnot226_2m1, Fin.reduceFinMk, Fin.isValue, seqCP226,
        List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceDiv,
        List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
        Order.lt_two_iff, zero_le, Nat.div_self, ComputeProg.fwdBits, Function.update_self, ne_eq,
        Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Function.update_idem, wKin, finMod,
        add_zero, Nat.reduceMod, tsub_zero, Nat.add_one_sub_one, Nat.reduceSub, β₃] <;>
      rw [hβ₂_lo _ (by decide), hβ₂_lo _ (by decide)] <;>
      (first | erw [hβ₂ 0] | erw [hβ₂ 1] | erw [hβ₂ 2] | erw [hβ₂ 3] | erw [hβ₂ 4] | erw [hβ₂ 5]
             | erw [hβ₂ 6]) <;> dsimp <;> ring
  have hOutN (k : ℕ) (hk : k < 7 := by decide) :
      β₃ (wKin (15 + k)) = β (wKin (8 + k)) + β (wKin (15 + k)) + sc (7 - k) := hOut ⟨k, hk⟩
  change m7U2OfBits β₃ = _
  simp only [m7U2OfBits, prefixSum, coin2m1Val, zmod2_val_mul_pow]
  rw [hOutN 0, hOutN 1, hOutN 2, hOutN 3, hOutN 4, hOutN 5, hOutN 6]
  rfl

def pKinMid14SqFree2m1CP : ComputeProg 226 := .seq pCoin2m1CP pCmpU2CP
def pKinPre15SqFree2m1CP : ComputeProg 226 := .seq pKinMid14SqFree2m1CP (ga226 22 68 24)
def sMask14SqFree2m1 : ℕ := 337311730794963664896
def sMask15SqFree2m1 : ℕ := 337311730794980442112
def kin2m1RawBit (β : BitAssignment 226) : ZMod 2 := pKinMid14SqFree2m1CP.fwdBits β (wKin 68)
def kin2m1OutBit (β : BitAssignment 226) : ZMod 2 := pKinPre15SqFree2m1CP.fwdBits β wOutKin226

theorem pKin2m1_props : pKinMid14SqFree2m1CP.numAnd = 14 ∧ pKinPre15SqFree2m1CP.numAnd = 15 ∧
    StructuredCB.validProgMask 0 sMask14SqFree2m1 pKinMid14SqFree2m1CP = true ∧
        StructuredCB.validProgMask 0 sMask15SqFree2m1 pKinPre15SqFree2m1CP = true ∧
    avoids226 (2 ^ wLocQ226.val) pKinPre15SqFree2m1CP = true ∧
        avoids226 (2 ^ wIsKin226.val) pKinMid14SqFree2m1CP = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel⟩

theorem kin2m1RawBit_eq (β : BitAssignment 226) (hclean : ∀ w : Wire 226, 25 ≤ w.val → β w = 0) :
    kin2m1RawBit β = if (twosComplement_frozen (kOfBits8 β)).natAbs ≤ coin2m1Val 7 0 (fun i ↦
        β (wKin (8 + i))) (fun i ↦ β (wKin (15 + i))) then 1 else 0 := by
  let β₁ := pCoin2m1CP.fwdBits β
  have hcl_u2 (w : Wire 226) (hlo : 47 ≤ w.val) (hhi : w.val ≤ 68) : β₁ w = 0 :=
    (fwdBits_not_targetMask β w ((by decide +kernel : ∀ u, 47 ≤ u → u ≤ 68 →
      (cpTargetMask226 pCoin2m1CP).testBit u = false) w.val hlo hhi)).trans (hclean w (by omega))
  have hk_eq : kOfBits8 β₁ = kOfBits8 β :=
      Fin.ext <| congrArg (· % 256) <| prefixSum_congr_lt 8 _ _ fun i hi ↦
    fwdBits_not_targetMask β (wKin i) (Nat.mod_eq_of_lt (by omega : i < 226) ▸
      (by decide +kernel : ∀ u < 8, (cpTargetMask226 pCoin2m1CP).testBit u = false) i hi)
  have hu2 := cmpU2_rawBit_eq_decide_le β₁ hcl_u2
  rwa [hk_eq, m7U2OfBits_pCoin2m1CP β fun w hlo _ ↦ hclean w hlo] at hu2

theorem kin2m1OutBit_eq_fn (β : BitAssignment 226) : kin2m1OutBit β = β wOutKin226 + β wIsKin226 *
    kin2m1RawBit β := by
  exact congrArg₂ (· + · * kin2m1RawBit β) (fwdBits_not_targetMask β wOutKin226 (by decide +kernel))
    (fwdBits_not_targetMask β (wKin 22) (by decide +kernel))

theorem hwIsKin226_ne_68 : wIsKin226 ≠ wKin 68 := by decide
/--
Physical `Usel` `14` -AND (`56 T`) bracket: `CZ(wIsKin226, wKin 68)` directly on raw comparator bit!
-/
def abpKin14SqFree2m1Usel : AndBracketProg 226 :=
  pKinMid14SqFree2m1CP.wrap (.prim (czCircuit wIsKin226 (wKin 68) hwIsKin226_ne_68))
/-- Spec `Usel` `15`-AND bracket (`IsPhaseDiag ... kin2m1OutBit` on all basis states). -/
def abpKin15SqFree2m1Usel : AndBracketProg 226 :=
  pKinPre15SqFree2m1CP.wrap (.prim (zGateCirc wOutKin226))
/-- Physical & spec `Csel` `15`-AND (`60 T`) bracket (`CZ(wLocQ226, wOutKin226)`). -/
def abpKin15SqFree2m1Csel : AndBracketProg 226 :=
    pKinPre15SqFree2m1CP.wrap (.prim (czCircuit wLocQ226 wOutKin226 hq226_ne_out))
end QuantumComputation.Specs.PhotochemistrySolution.Kinetic664
end

noncomputable section
-- circuits, counts & local unitaries
set_option autoImplicit false
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

open PhotochemistrySolution.Kinetic664 PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore Operator QProg
  Matrix Circuit Qubit PrimitiveGate DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open QuantumComputation.Specs PhotochemistrySolution
  PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectFastFlags
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SelectQromKetBridge
open PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.FastQft8
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb (fwdBits_avoids
    wOutKin226 wLocQ226)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull (bAxisMux27)
open scoped Matrix BigOperators
set_option allowUnsafeReducibility true in
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState
  XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel
  Stage4Kin14Scb.abpKin14Csel Stage4KinFull.bAxisMux27 bSpeciesSwap50

def cpAvoid23_sqf : ComputeProg 226 → Bool
  | .id => true
  | .x u => decide (u.val ≠ 23)
  | .cnot c tw _ => decide (c.val ≠ 23) && decide (tw.val ≠ 23)
  | .andGate c1 c2 a _ _ _ => decide (c1.val ≠ 23) && decide (c2.val ≠ 23) && decide (a.val ≠ 23)
  | .seq p q => cpAvoid23_sqf p && cpAvoid23_sqf q

theorem fwdBits_congr_avoid23_sqf :
    ∀ {p : ComputeProg 226} (_ : cpAvoid23_sqf p = true) (β₁ β₂ : BitAssignment 226),
      (∀ j : Wire 226, j.val ≠ 23 → β₁ j = β₂ j) →
      ∀ j : Wire 226, j.val ≠ 23 → p.fwdBits β₁ j = p.fwdBits β₂ j
  | .id, _, _, _, hβ, j, hj => hβ j hj
  | .x u, hp, _, _, hβ, j, hj => by
      simp only [ComputeProg.fwdBits, Function.update_apply, hβ j hj, hβ u (of_decide_eq_true hp)]
  | .cnot c tw _, hp, _, _, hβ, j, hj => by
      have h12 := Bool.and_eq_true_iff.mp hp
      simp only [ComputeProg.fwdBits, Function.update_apply, hβ j hj,
          hβ c (of_decide_eq_true h12.1), hβ tw (of_decide_eq_true h12.2)]
  | .andGate c1 c2 a _ _ _, hp, _, _, hβ, j, hj => by
      have h13 := Bool.and_eq_true_iff.mp hp
      have h12 := Bool.and_eq_true_iff.mp h13.1
      simp only [ComputeProg.fwdBits, Function.update_apply, hβ j hj,
          hβ c1 (of_decide_eq_true h12.1),
        hβ c2 (of_decide_eq_true h12.2), hβ a (of_decide_eq_true h13.2)]
  | .seq p q, hpq, β₁, β₂, hβ, j, hj =>
      let ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp hpq
      fwdBits_congr_avoid23_sqf hq _ _ (fwdBits_congr_avoid23_sqf hp β₁ β₂ hβ) j hj

theorem cpWires_pKinAlign0_exact {P : Wire dLayout → Prop} (h1 : P wAxis0 ∧ P wKinAxis0)
    (h2 : P wAxis1 ∧ P wKinAxis1)
    (h3 : P wIsFine ∧ P wIsFineCopy) (h4 : P wHasE1 ∧ P wIsElecKin) :
        ComputeProgWires P pKinAlign0 := ⟨h1, h2, h3, h4⟩
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
end
end
