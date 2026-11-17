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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WindowedCsaStageA

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section FastSlot3PrepAndCompact2458

section
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
namespace FastSlot3PrepAndCompact2458
local instance (priority := 1000000) instNeZeroTwoPowSlot1PwuB (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (T toffoli)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open MeasureBranchHadamardSem
open MomSlot0CircuitHalf (padZeroBits phaseDiagUnitary)
open MomSlot0LocalAndMomCombine288 (TempCzProg)
open MomSlot1GeomPriority288 (b2z)
open MomSlots35Slot3ProjNuclear (predCoarseGood33 predNotZero33 h33Unitary uOaa33 uOaa33_inv_eq
  uPrep3 s3Coarse33Core)
open FullSysPosSlots24AndTopConcrete (hadamardPayloadDyn hadamardPayloadUnitary
  count_hadamardPayloadDyn_t count_hadamardPayloadDyn_toff hadamardPayloadDyn_realizes)
open FullSysMomSlots0135Concrete (momCoreWires)
open ShiftedMagS1 (phaseDiag_eq realizesEmbedded_seq disjConcatLeft testBit_mod_two_powAux
  testBit_div_two_powAux)
open PosSlots24PartnerMux288 (qreg_ext disj_symm)
open Slot3Exact216Oracle80 (uQutrit3 uPrep3_216)
open Slot3PrepWideAndSwap3 (progNotZero33Cz progNotZero33Cz_count progNotZero33Cz_spec
  realizes_phaseDiagUnitary_cleanWorkspace_cz)
open Leaf3Prep179Spec (dynCount_seq xorRightMapGen tblBits16 phaseStage234_49
  phaseStage234_49_on_stage1 cQutrit3CoreGen cQutrit3CoreGen_count_toff
  cQutrit3CoreGen_inv_count_toff cQutrit3CoreGen_count_t cQutrit3CoreGen_inv_count_t
  cQutrit3CoreGen_eval bitsVal_testBit_eq getNatAt kcTable49168List)
open Leaf3Slot3Norm1sWidth204 (Slot3PrepCompactSpec)
open MultiBankWStateRouter
open Slot3Prep2730On170And179 (dStage234_49_fast154 dStage234_49_fast154_count_toff
  dStage234_49_fast154_count_t dStage234_49_fast154_realizes)
open D0aa33Width165Slot3Prep2356
open Slot3Prep2570On170And179 (SubspaceStep.mul_right)
/-- The `16`-wire subregister inside `Wire 198` pairing `(idxHi3Loc 0..2, idxLo5Loc 0..4)` (`0..7`)
with the `8` degree-`1` upward-Möbius wires `(49, 50, 52, 56, 57, 59, 63, 71)` (`8..15`). -/
def deg1Loc (i : Fin 16) : Wire 198 :=
  if h0 : i.val < 3 then idxHi3Loc ⟨i.val, h0⟩
  else if h1 : i.val < 8 then idxLo5Loc ⟨i.val - 3, by omega⟩
  else if i.val = 8 then ⟨49, by decide⟩
  else if i.val = 9 then ⟨50, by decide⟩
  else if i.val = 10 then ⟨52, by decide⟩
  else if i.val = 11 then ⟨56, by decide⟩
  else if i.val = 12 then ⟨57, by decide⟩
  else if i.val = 13 then ⟨59, by decide⟩
  else if i.val = 14 then ⟨63, by decide⟩
  else ⟨71, by decide⟩
theorem deg1Loc_inj : Function.Injective deg1Loc := by
  intro i j
  revert i j
  decide
def rDeg1_16In198 : QRegister 16 198 := ⟨⟨deg1Loc, deg1Loc_inj⟩⟩
@[simp] theorem rDeg1_16In198_apply (i : Fin 16) : rDeg1_16In198 i = deg1Loc i := rfl
/-- Self-inverse `8`-CNOT Clifford canceling all `8` degree-`1` Möbius wires (`0..7 ↦ 8..15`). -/
def cZeroDeg1_16 : CliffProg 16 :=
  .seq (.cnot ⟨0, by decide⟩ ⟨8, by decide⟩ (by decide))
  (.seq (.cnot ⟨1, by decide⟩ ⟨9, by decide⟩ (by decide))
  (.seq (.cnot ⟨2, by decide⟩ ⟨10, by decide⟩ (by decide))
  (.seq (.cnot ⟨3, by decide⟩ ⟨11, by decide⟩ (by decide))
  (.seq (.cnot ⟨4, by decide⟩ ⟨12, by decide⟩ (by decide))
  (.seq (.cnot ⟨5, by decide⟩ ⟨13, by decide⟩ (by decide))
  (.seq (.cnot ⟨6, by decide⟩ ⟨14, by decide⟩ (by decide))
        (.cnot ⟨7, by decide⟩ ⟨15, by decide⟩ (by decide))))))))
def in16OfHi3Lo5 (r₀ : Fin 8) (q₀ : Fin 32) : BitAssignment 16 :=
  fun m ↦
    if m.val < 3 then b2z (r₀.val.testBit m.val)
    else if m.val < 8 then b2z (q₀.val.testBit (m.val - 3))
    else if m.val = 8 then mobiusTargetBits r₀ ⟨1, by decide⟩
    else if m.val = 9 then mobiusTargetBits r₀ ⟨2, by decide⟩
    else if m.val = 10 then mobiusTargetBits r₀ ⟨4, by decide⟩
    else if m.val = 11 then mobiusTargetBits q₀ ⟨1, by decide⟩
    else if m.val = 12 then mobiusTargetBits q₀ ⟨2, by decide⟩
    else if m.val = 13 then mobiusTargetBits q₀ ⟨4, by decide⟩
    else if m.val = 14 then mobiusTargetBits q₀ ⟨8, by decide⟩
    else mobiusTargetBits q₀ ⟨16, by decide⟩
def comp16OfHi3Lo5 (r₀ : Fin 8) (q₀ : Fin 32) : BitAssignment 16 := fun m ↦ if m.val < 3 then
    b2z (r₀.val.testBit m.val) else if m.val < 8 then b2z (q₀.val.testBit (m.val - 3)) else 0
theorem mobiusTargetBits8_pow2 :
    ∀ r₀ : Fin 8,
      mobiusTargetBits r₀ ⟨1, by decide⟩ = b2z (r₀.val.testBit 0) ∧
      mobiusTargetBits r₀ ⟨2, by decide⟩ = b2z (r₀.val.testBit 1) ∧
      mobiusTargetBits r₀ ⟨4, by decide⟩ = b2z (r₀.val.testBit 2) := by
  decide
theorem mobiusTargetBits32_pow2 :
    ∀ q₀ : Fin 32,
      mobiusTargetBits q₀ ⟨1, by decide⟩ = b2z (q₀.val.testBit 0) ∧
      mobiusTargetBits q₀ ⟨2, by decide⟩ = b2z (q₀.val.testBit 1) ∧
      mobiusTargetBits q₀ ⟨4, by decide⟩ = b2z (q₀.val.testBit 2) ∧
      mobiusTargetBits q₀ ⟨8, by decide⟩ = b2z (q₀.val.testBit 3) ∧
      mobiusTargetBits q₀ ⟨16, by decide⟩ = b2z (q₀.val.testBit 4) := by
  decide
theorem cZeroDeg1_16_eval_general (β : BitAssignment 16) (m : Wire 16) :
    cZeroDeg1_16.eval β m =
      if m.val < 8 then β m else β m + β ⟨m.val - 8, by omega⟩ := by
  fin_cases m <;> simp [cZeroDeg1_16, CliffProg.eval]
theorem cZeroDeg1_16_eval_in16_eq (r₀ : Fin 8) (q₀ : Fin 32) :
    cZeroDeg1_16.eval (in16OfHi3Lo5 r₀ q₀) = comp16OfHi3Lo5 r₀ q₀ := by
  obtain ⟨hr0, hr1, hr2⟩ := mobiusTargetBits8_pow2 r₀
  obtain ⟨hq0, hq1, hq2, hq3, hq4⟩ := mobiusTargetBits32_pow2 q₀
  funext m
  rw [cZeroDeg1_16_eval_general]
  fin_cases m <;>
    (dsimp only [in16OfHi3Lo5, comp16OfHi3Lo5]
     try rw [hr0]
     try rw [hr1]
     try rw [hr2]
     try rw [hq0]
     try rw [hq1]
     try rw [hq2]
     try rw [hq3]
     try rw [hq4]
     simp [CharTwo.add_self_eq_zero])
theorem cZeroDeg1_16_eval_comp16_eq (r₀ : Fin 8) (q₀ : Fin 32) :
    cZeroDeg1_16.eval (comp16OfHi3Lo5 r₀ q₀) = in16OfHi3Lo5 r₀ q₀ := by
  rw [← cZeroDeg1_16_eval_in16_eq r₀ q₀]
  funext m
  rw [cZeroDeg1_16_eval_general]
  by_cases hm : m.val < 8
  · rw [ite_eq_left hm, cZeroDeg1_16_eval_general, ite_eq_left hm]
  · rw [ite_eq_right hm, cZeroDeg1_16_eval_general, ite_eq_right hm,
      cZeroDeg1_16_eval_general, ite_eq_left (by dsimp; omega),
      add_assoc, CharTwo.add_self_eq_zero, add_zero]
theorem deg1Loc_hi8_strictMono :
    ∀ a b : Fin 8, a < b →
      (deg1Loc ⟨8 + a.val, by omega⟩).val < (deg1Loc ⟨8 + b.val, by omega⟩).val := by
  decide
theorem deg1Loc_le_71 : ∀ i : Fin 16, (deg1Loc i).val ≤ 71 := by
  decide
theorem deg1Loc_ge_49_of_ge_8 : ∀ i : Fin 16, 8 ≤ i.val → 49 ≤ (deg1Loc i).val := by
  decide
/-- The `119` clean wires inside `49..197` in `G3_comp`:
`0..7 ↦ (49, 50, 52, 56, 57, 59, 63, 71)` (`deg1Loc 8..15`), `8..118 ↦ 87..197`. -/
def clean119Loc (j : Fin 119) : Wire 198 :=
  if h : j.val < 8 then deg1Loc ⟨8 + j.val, by omega⟩
  else ⟨87 + (j.val - 8), by omega⟩
theorem clean119Loc_strictMono : StrictMono clean119Loc := by
  intro i j hij
  change (clean119Loc i).val < (clean119Loc j).val
  have hi := i.isLt
  have hj := j.isLt
  by_cases hi8 : i.val < 8
  · by_cases hj8 : j.val < 8
    · dsimp only [clean119Loc]
      rw [dite_eq_left hi8, dite_eq_left hj8]
      exact deg1Loc_hi8_strictMono ⟨i.val, hi8⟩ ⟨j.val, hj8⟩ hij
    · dsimp only [clean119Loc]
      rw [dite_eq_left hi8, dite_eq_right hj8]
      have hle71 := deg1Loc_le_71 ⟨8 + i.val, by omega⟩
      dsimp only
      omega
  · have hj8 : ¬ j.val < 8 := by omega
    dsimp only [clean119Loc]
    rw [dite_eq_right hi8, dite_eq_right hj8]
    dsimp only
    omega
theorem clean119Loc_inj : Function.Injective clean119Loc := clean119Loc_strictMono.injective
def rClean119In198 : QRegister 119 198 := ⟨⟨clean119Loc, clean119Loc_inj⟩⟩
@[simp] theorem rClean119In198_apply (j : Fin 119) : rClean119In198 j = clean119Loc j := rfl
theorem clean119Loc_ge_49 (j : Fin 119) : 49 ≤ (clean119Loc j).val := by
  have h0 : (clean119Loc ⟨0, by decide⟩).val = 49 := rfl
  by_cases hj : j.val = 0
  · have hjeq : j = ⟨0, by decide⟩ := Fin.ext hj
    rw [hjeq, h0]
  · have hlt : (⟨0, by decide⟩ : Fin 119) < j := Nat.pos_of_ne_zero hj
    have hm := clean119Loc_strictMono hlt
    change 49 < (clean119Loc j).val at hm
    omega
theorem r49In198_disj_rClean119In198 : r49In198.DisjointWires rClean119In198 := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  have hi := i.isLt
  have hj := clean119Loc_ge_49 j
  have hv := congrArg Fin.val heq
  rw [r49In198_apply] at hv
  dsimp at hv
  omega
theorem disj49_119 {n : ℕ} (rComb : QRegister 198 n) :
    (rComb.compose r49In198).DisjointWires (rComb.compose rClean119In198) := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  exact QRegister.disjoint_iff.mp r49In198_disj_rClean119In198 i j (rComb.wires.injective heq)
theorem rWork_165_35_disj {mWork n : ℕ} (hmW : 200 ≤ mWork) (rWork : QRegister mWork n) :
    (rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)).DisjointWires
      (rWork.slice 165 35 hmW) := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  rw [QRegister.slice_apply, QRegister.slice_apply] at heq
  have hv := congrArg Fin.val (rWork.wires.injective heq)
  change 0 + i.val = 165 + j.val at hv
  omega
theorem rComb_rExtra35_disj {mWork n : ℕ} (hmW : 200 ≤ mWork) (rAct33 : QRegister 33 n)
    (rWork : QRegister mWork n) (hDisj : rAct33.DisjointWires rWork) : (rAct33.concat
    (rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)) (hDisj.compose_right
    _)).DisjointWires (rWork.slice 165 35 hmW) := disjConcatLeft (hDisj.compose_right _)
    (rWork_165_35_disj hmW rWork)
theorem r49_rClean119_35_disj {mWork n : ℕ} (hmW : 200 ≤ mWork)
    (rAct33 : QRegister 33 n) (rWork : QRegister mWork n)
    (hDisj : rAct33.DisjointWires rWork) :
    let rComb := rAct33.concat (rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW))
      (hDisj.compose_right _)
    let rExtra35 := rWork.slice 165 35 hmW
    let hCombEx := rComb_rExtra35_disj hmW rAct33 rWork hDisj
    (rComb.compose r49In198).DisjointWires
      ((rComb.compose rClean119In198).concat rExtra35 (hCombEx.compose_left _)) := by
  intro rComb rExtra35 hCombEx
  exact disj_symm (disjConcatLeft (disj_symm (disj49_119 rComb))
    (disj_symm (hCombEx.compose_left _)))
theorem rSub_concat_rExtra35_eq_slice200 {mWork n : ℕ} (hmW : 200 ≤ mWork)
    (rWork : QRegister mWork n) :
    (rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)).concat (rWork.slice 165 35 hmW)
    (rWork_165_35_disj hmW rWork) = rWork.slice 0 200 hmW := by
  let rSub := rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)
  let rExtra35 := rWork.slice 165 35 hmW
  let hSE := rWork_165_35_disj hmW rWork
  apply qreg_ext; intro k
  by_cases hk : k.val < 165
  · let i : Fin 165 := ⟨k.val, hk⟩
    have hkeq : k = Fin.castAdd 35 i := Fin.ext rfl
    calc (rSub.concat rExtra35 hSE) k
        = (rSub.concat rExtra35 hSE) (Fin.castAdd 35 i) := congrArg _ hkeq
      _ = rSub i := QRegister.concat_apply_left rSub rExtra35 hSE i
      _ = rWork ⟨0 + i.val, _⟩ := QRegister.slice_apply rWork 0 165 _ i
      _ = (rWork.slice 0 200 hmW) k := (QRegister.slice_apply rWork 0 200 hmW k).symm
  · let j : Fin 35 := ⟨k.val - 165, by omega⟩
    have hkeq : k = Fin.natAdd 165 j := Fin.ext (by dsimp [j]; omega)
    calc (rSub.concat rExtra35 hSE) k
        = (rSub.concat rExtra35 hSE) (Fin.natAdd 165 j) := congrArg _ hkeq
      _ = rExtra35 j := QRegister.concat_apply_right rSub rExtra35 hSE j
      _ = rWork ⟨165 + j.val, _⟩ := QRegister.slice_apply rWork 165 35 hmW j
      _ = rWork ⟨0 + k.val, _⟩ := congrArg rWork (Fin.ext (by dsimp [j]; omega))
      _ = (rWork.slice 0 200 hmW) k := (QRegister.slice_apply rWork 0 200 hmW k).symm
/-! ## Section 2: Direct `32 × 8` `0-T` MBU Unload `dUnloadKc16_32x8` (`Gkc 16 ↦ G1`) -/
def kcPairs32x8Aux {n : ℕ} (j : Fin 16) (wOut32 : Fin 32 → Wire n) (wOut8 : Fin 8 → Wire n)
    (hDisj : ∀ q r, wOut32 q ≠ wOut8 r) : (i : ℕ) → i ≤ 256 → List (WirePair n)
  | 0, _ => []
  | i + 1, hi =>
      let prev := kcPairs32x8Aux j wOut32 wOut8 hDisj i (Nat.le_of_succ_le hi)
      if (getNatAt kcTable49168List i).testBit j.val then
        let q : Fin 32 := ⟨i % 32, Nat.mod_lt i (by decide)⟩
        let r : Fin 8 := ⟨i / 32, by omega⟩
        ⟨wOut32 q, wOut8 r, hDisj q r⟩ :: prev
      else
        prev
def kcPairs32x8 {n : ℕ} (j : Fin 16) (wOut32 : Fin 32 → Wire n) (wOut8 : Fin 8 → Wire n)
    (hDisj : ∀ q r, wOut32 q ≠ wOut8 r) : List (WirePair n) :=
  kcPairs32x8Aux j wOut32 wOut8 hDisj 256 le_rfl
theorem czPairsParity_kcPairs32x8Aux_update {n : ℕ} (j : Fin 16)
    (wOut32 : Fin 32 → Wire n) (wOut8 : Fin 8 → Wire n)
    (hDisj : ∀ q r, wOut32 q ≠ wOut8 r)
    (qWire : Wire n) (hq32 : ∀ q, wOut32 q ≠ qWire) (hq8 : ∀ r, wOut8 r ≠ qWire)
    (β : BitAssignment n) (a : ZMod 2) :
    ∀ (i : ℕ) (hi : i ≤ 256),
      czPairsParity (kcPairs32x8Aux j wOut32 wOut8 hDisj i hi) (Function.update β qWire a) =
        czPairsParity (kcPairs32x8Aux j wOut32 wOut8 hDisj i hi) β
  | 0, _ => rfl
  | i + 1, hi => by
      dsimp only [kcPairs32x8Aux]
      split_ifs with htb
      · dsimp only [czPairsParity]
        rw [Function.update_of_ne (hq32 _), Function.update_of_ne (hq8 _),
          czPairsParity_kcPairs32x8Aux_update j wOut32 wOut8 hDisj qWire hq32 hq8 β a i
            (Nat.le_of_succ_le hi)]
      · exact czPairsParity_kcPairs32x8Aux_update j wOut32 wOut8 hDisj qWire hq32 hq8 β a i
          (Nat.le_of_succ_le hi)
theorem czPairsParity_kcPairs32x8_update {n : ℕ} (j : Fin 16) (wOut32 : Fin 32 → Wire n)
    (wOut8 : Fin 8 → Wire n) (hDisj : ∀ q r, wOut32 q ≠ wOut8 r) (qWire : Wire n)
    (hq32 : ∀ q, wOut32 q ≠ qWire) (hq8 : ∀ r, wOut8 r ≠ qWire) (β : BitAssignment n)
    (a : ZMod 2) : czPairsParity (kcPairs32x8 j wOut32 wOut8 hDisj)
    (Function.update β qWire a) = czPairsParity (kcPairs32x8 j wOut32 wOut8 hDisj) β :=
    czPairsParity_kcPairs32x8Aux_update j wOut32 wOut8 hDisj qWire hq32 hq8 β a 256 le_rfl
theorem czPairsParity_kcPairs32x8Aux_oneHot {n : ℕ} (j : Fin 16)
    (wOut32 : Fin 32 → Wire n) (wOut8 : Fin 8 → Wire n)
    (hDisj : ∀ q r, wOut32 q ≠ wOut8 r)
    (β : BitAssignment n) (c8 : Fin 256)
    (h32 : ∀ q : Fin 32, β (wOut32 q) = if q.val = c8.val % 32 then 1 else 0)
    (h8 : ∀ r : Fin 8, β (wOut8 r) = if r.val = c8.val / 32 then 1 else 0) :
    ∀ (i : ℕ) (hi : i ≤ 256),
      czPairsParity (kcPairs32x8Aux j wOut32 wOut8 hDisj i hi) β =
        if c8.val < i then b2z ((getNatAt kcTable49168List c8.val).testBit j.val) else 0
  | 0, _ => by simp [kcPairs32x8Aux, czPairsParity]
  | i + 1, hi => by
      have ih := czPairsParity_kcPairs32x8Aux_oneHot j wOut32 wOut8 hDisj β c8 h32 h8 i
        (Nat.le_of_succ_le hi)
      dsimp only [kcPairs32x8Aux]
      by_cases hic : i = c8.val
      · subst hic
        have hlt_false : ¬ c8.val < c8.val := Nat.lt_irrefl _
        have hlt_true : c8.val < c8.val + 1 := Nat.lt_succ_self _
        rw [ite_eq_right hlt_false] at ih
        rw [ite_eq_left hlt_true]
        by_cases htb : (getNatAt kcTable49168List c8.val).testBit j.val = true
        · rw [ite_eq_left htb]
          dsimp only [czPairsParity]
          rw [ih, add_zero, h32, h8]
          simp [htb, b2z]
        · rw [ite_eq_right htb, ih]
          have hbf : (getNatAt kcTable49168List c8.val).testBit j.val = false :=
            Bool.eq_false_iff.mpr htb
          rw [hbf]; rfl
      · have hiff : c8.val < i + 1 ↔ c8.val < i := by omega
        have hprod0 : β (wOut32 ⟨i % 32, Nat.mod_lt i (by decide)⟩) *
            β (wOut8 ⟨i / 32, by omega⟩) = 0 := by
          rw [h32, h8]
          by_cases hmod : i % 32 = c8.val % 32
          · have hdiv : i / 32 ≠ c8.val / 32 := fun hd ↦ hic (by
              have h1 := Nat.div_add_mod i 32
              have h2 := Nat.div_add_mod c8.val 32
              omega)
            simp [hmod, hdiv]
          · simp [hmod]
        by_cases htb : (getNatAt kcTable49168List i).testBit j.val = true
        · rw [ite_eq_left htb]
          dsimp only [czPairsParity]
          rw [hprod0, zero_add, ih]
          by_cases hlt : c8.val < i
          · rw [ite_eq_left hlt, ite_eq_left (hiff.mpr hlt)]
          · rw [ite_eq_right hlt, ite_eq_right (fun h ↦ hlt (hiff.mp h))]
        · rw [ite_eq_right htb, ih]
          by_cases hlt : c8.val < i
          · rw [ite_eq_left hlt, ite_eq_left (hiff.mpr hlt)]
          · rw [ite_eq_right hlt, ite_eq_right (fun h ↦ hlt (hiff.mp h))]
theorem czPairsParity_kcPairs32x8_oneHot {n : ℕ} (j : Fin 16) (wOut32 : Fin 32 → Wire n)
    (wOut8 : Fin 8 → Wire n) (hDisj : ∀ q r, wOut32 q ≠ wOut8 r) (β : BitAssignment n)
    (c8 : Fin 256) (h32 : ∀ q : Fin 32, β (wOut32 q) = if q.val = c8.val % 32 then 1 else 0)
    (h8 : ∀ r : Fin 8, β (wOut8 r) = if r.val = c8.val / 32 then 1 else 0) : czPairsParity
    (kcPairs32x8 j wOut32 wOut8 hDisj) β = b2z
    ((getNatAt kcTable49168List c8.val).testBit j.val) := by
  unfold kcPairs32x8
  rw [czPairsParity_kcPairs32x8Aux_oneHot j wOut32 wOut8 hDisj β c8 h32 h8 256 le_rfl,
    ite_eq_left c8.isLt]
def dUnloadKc16_32x8 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 198 n) :
    (m : ℕ) → m ≤ 16 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | m + 1, hm =>
      let j : Fin 16 := ⟨m, hm⟩
      xUnloadCzPairsSeqDyn v (rComb (kc16Loc j))
        (kcPairs32x8 j (fun q ↦ rComb (out32Loc q)) (fun r ↦ rComb (out8Loc r))
          (fun q r ↦ rComb.wires.injective.ne (out32Loc_ne_out8Loc q r)))
        (dUnloadKc16_32x8 v rComb m (Nat.le_of_succ_le hm))
theorem count_dUnloadKc16_32x8 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 198 n) :
    ∀ (m : ℕ) (hm : m ≤ 16),
      (dUnloadKc16_32x8 v rComb m hm).count T = 0 ∧
      (dUnloadKc16_32x8 v rComb m hm).count toffoli = 0
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
      obtain ⟨ht, hf⟩ := count_dUnloadKc16_32x8 v rComb m (Nat.le_of_succ_le hm)
      obtain ⟨xt, xf⟩ := count_xUnloadCzPairsSeqDyn v (rComb (kc16Loc ⟨m, hm⟩))
        (kcPairs32x8 ⟨m, hm⟩ (fun q ↦ rComb (out32Loc q)) (fun r ↦ rComb (out8Loc r))
          (fun q r ↦ rComb.wires.injective.ne (out32Loc_ne_out8Loc q r)))
        (dUnloadKc16_32x8 v rComb m (Nat.le_of_succ_le hm))
      dsimp only [dUnloadKc16_32x8]
      exact ⟨xt.trans ht, xf.trans hf⟩
/-! ## Section 3: `dCoarseGood33_200_wstate` (`988 T`, `0` `toffoli`) -/
noncomputable def dCoarseGood33_200_wstate {mWork : ℕ} (hmW : 200 ≤ mWork) {Var : Type} {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rWork : QRegister mWork n)
    (hDisj : rAct33.DisjointWires rWork) : DynamicCircuit Var n :=
  let rSub : QRegister 165 n := rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)
  let rExtra35 : QRegister 35 n := rWork.slice 165 35 hmW
  let rComb : QRegister 198 n := rAct33.concat rSub (hDisj.compose_right _)
  let hCombEx := rComb_rExtra35_disj hmW rAct33 rWork hDisj
  let rClean154 : QRegister (119 + 35) n :=
    (rComb.compose rClean119In198).concat rExtra35 (hCombEx.compose_left _)
  let step1a := wStateComputeUncondPow2 2 v
    (fun d ↦ rComb (idxHi3Loc d)) (fun r ↦ rComb (out8Loc r)) (rComb qEncLoc)
  let step1b := wStateComputeUncondPow2 4 v
    (fun d ↦ rComb (idxLo5Loc d)) (fun q ↦ rComb (out32Loc q)) (rComb qEncLoc)
  let step2 : DynamicCircuit Var n := .circuit
    (((cMobius8.onRegister (rComb.compose rOh8In198)).toCircuit) ;;ᶜ
     ((cMobius32.onRegister (rComb.compose rOh32In198)).toCircuit))
  let step3 := (pStage1Copy125.onRegister (rComb.compose r125In198)).toDyn v
  let step3_zero8 : DynamicCircuit Var n := .circuit
    ((cZeroDeg1_16.onRegister (rComb.compose rDeg1_16In198)).toCircuit)
  let step4 := dStage234_49_fast154 v (rComb.compose r49In198) rClean154
    (r49_rClean119_35_disj hmW rAct33 rWork hDisj)
  let step5_unzero8 : DynamicCircuit Var n := .circuit
    ((cZeroDeg1_16.onRegister (rComb.compose rDeg1_16In198)).toCircuit)
  let step5 : DynamicCircuit Var n := .circuit
    ((((cMobius32.inv).onRegister (rComb.compose rOh32In198)).toCircuit) ;;ᶜ
     (((cMobius8.inv).onRegister (rComb.compose rOh8In198)).toCircuit))
  let step6a := dUnloadKc16_32x8 v rComb 16 le_rfl
  let step6b := wStateUncomputeUncondPow2 4 v
    (fun d ↦ rComb (idxLo5Loc d)) (fun q ↦ rComb (out32Loc q))
  let step6c := wStateUncomputeUncondPow2 2 v
    (fun d ↦ rComb (idxHi3Loc d)) (fun r ↦ rComb (out8Loc r))
  .seq step1a (.seq step1b (.seq step2 (.seq step3 (.seq step3_zero8
    (.seq step4 (.seq step5_unzero8 (.seq step5 (.seq step6a (.seq step6b step6c)))))))))
theorem dCoarseGood33_200_wstate_count_toff {mWork : ℕ} (hmW : 200 ≤ mWork) {Var : Type} {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rWork : QRegister mWork n)
    (hDisj : rAct33.DisjointWires rWork) :
    (dCoarseGood33_200_wstate hmW v rAct33 rWork hDisj).count toffoli = 0 := by
  let rSub : QRegister 165 n := rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)
  let rExtra35 : QRegister 35 n := rWork.slice 165 35 hmW
  let rComb : QRegister 198 n := rAct33.concat rSub (hDisj.compose_right _)
  let hCombEx := rComb_rExtra35_disj hmW rAct33 rWork hDisj
  let rClean154 : QRegister (119 + 35) n :=
    (rComb.compose rClean119In198).concat rExtra35 (hCombEx.compose_left _)
  have f1a : (wStateComputeUncondPow2 2 v (fun d ↦ rComb (idxHi3Loc d)) (fun r ↦ rComb
      (out8Loc r)) (rComb qEncLoc)).count toffoli = 0 := (count_wStateComputeUncondPow2 2 v
      (fun d ↦ rComb (idxHi3Loc d)) (fun r ↦ rComb (out8Loc r)) (rComb qEncLoc)).2
  have f1b : (wStateComputeUncondPow2 4 v (fun d ↦ rComb (idxLo5Loc d)) (fun q ↦ rComb
      (out32Loc q)) (rComb qEncLoc)).count toffoli = 0 := (count_wStateComputeUncondPow2 4 v
      (fun d ↦ rComb (idxLo5Loc d)) (fun q ↦ rComb (out32Loc q)) (rComb qEncLoc)).2
  have f3 : ((pStage1Copy125.onRegister (rComb.compose r125In198)).toDyn v).count toffoli = 0 :=
    TempPhaseProg.toDyn_count_toff v (pStage1Copy125.onRegister (rComb.compose r125In198))
  have f4 : (dStage234_49_fast154 v (rComb.compose r49In198) rClean154 (r49_rClean119_35_disj
      hmW rAct33 rWork hDisj)).count toffoli = 0 := dStage234_49_fast154_count_toff v
      (rComb.compose r49In198) rClean154 (r49_rClean119_35_disj hmW rAct33 rWork hDisj)
  have f6a := (count_dUnloadKc16_32x8 v rComb 16 le_rfl).2
  have f6b : (wStateUncomputeUncondPow2 4 v (fun d ↦ rComb (idxLo5Loc d)) (fun q ↦ rComb
      (out32Loc q))).count toffoli = 0 := (count_wStateUncomputeUncondPow2 4 v (fun d ↦ rComb
      (idxLo5Loc d)) (fun q ↦ rComb (out32Loc q))).2
  have f6c : (wStateUncomputeUncondPow2 2 v (fun d ↦ rComb (idxHi3Loc d)) (fun r ↦ rComb
      (out8Loc r))).count toffoli = 0 := (count_wStateUncomputeUncondPow2 2 v (fun d ↦ rComb
      (idxHi3Loc d)) (fun r ↦ rComb (out8Loc r))).2
  have fc_toff : ∀ {m : ℕ} (c : CliffProg m), c.toCircuit.count toffoli = 0 :=
    fun c ↦ CliffProg.toCircuit_count_toff c
  dsimp only [rClean154, hCombEx, rComb, rExtra35, rSub] at f1a f1b f3 f4 f6a f6b f6c
  dsimp only [dCoarseGood33_200_wstate]
  simp only [dynCount_seq, dynCount_circuit, Circuit.count_seq, fc_toff,
    f1a, f1b, f3, f4, f6a, f6b, f6c]
theorem dCoarseGood33_200_wstate_count_t {mWork : ℕ} (hmW : 200 ≤ mWork) {Var : Type} {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rWork : QRegister mWork n)
    (hDisj : rAct33.DisjointWires rWork) :
    (dCoarseGood33_200_wstate hmW v rAct33 rWork hDisj).count T = 988 := by
  let rSub : QRegister 165 n := rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)
  let rExtra35 : QRegister 35 n := rWork.slice 165 35 hmW
  let rComb : QRegister 198 n := rAct33.concat rSub (hDisj.compose_right _)
  let hCombEx := rComb_rExtra35_disj hmW rAct33 rWork hDisj
  let rClean154 : QRegister (119 + 35) n :=
    (rComb.compose rClean119In198).concat rExtra35 (hCombEx.compose_left _)
  have term1a := (count_wStateComputeUncondPow2 2 v (fun d ↦ rComb (idxHi3Loc d))
    (fun r ↦ rComb (out8Loc r)) (rComb qEncLoc)).1
  have term1b := (count_wStateComputeUncondPow2 4 v (fun d ↦ rComb (idxLo5Loc d))
    (fun q ↦ rComb (out32Loc q)) (rComb qEncLoc)).1
  have t3 : ((pStage1Copy125.onRegister (rComb.compose r125In198)).toDyn v).count T = 152 := by
    rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd,
      pStage1Copy125_countTempAnd]
  have t4 := dStage234_49_fast154_count_t v (rComb.compose r49In198) rClean154
    (r49_rClean119_35_disj hmW rAct33 rWork hDisj)
  have t6a := (count_dUnloadKc16_32x8 v rComb 16 le_rfl).1
  have t6b := (count_wStateUncomputeUncondPow2 4 v (fun d ↦ rComb (idxLo5Loc d))
    (fun q ↦ rComb (out32Loc q))).1
  have t6c := (count_wStateUncomputeUncondPow2 2 v (fun d ↦ rComb (idxHi3Loc d))
    (fun r ↦ rComb (out8Loc r))).1
  dsimp only [rClean154, hCombEx, rComb, rExtra35, rSub] at term1a term1b t3 t4 t6a t6b t6c
  dsimp only [dCoarseGood33_200_wstate]
  simp only [dynCount_seq, dynCount_circuit, Circuit.count_seq, CliffProg.toCircuit_count_t,
    term1a, term1b, t3, t4, t6a, t6b, t6c]
  decide
/-! ## Section 4: Semantic Verification of `dCoarseGood33_200_wstate` -/
def G3_comp (x : BitAssignment 33) : BitAssignment 198 :=
  writeRegProg (G3 x) rDeg1_16In198 (comp16OfHi3Lo5 (hi3Of33 x) (lo5Of33 x))
theorem x_idxLo5_eq_b2z (x : BitAssignment 33) (d : Fin 5) :
    x ⟨25 + d.val, by omega⟩ = b2z ((lo5Of33 x).val.testBit d.val) := by
  have hmod : (lo5Of33 x).val.testBit d.val = (c8Of33 x).val.testBit d.val := by
    change ((c8Of33 x).val % 2 ^ 5).testBit d.val = _
    rw [testBit_mod_two_powAux 5 (c8Of33 x).val d.val, decide_eq_true d.isLt, Bool.true_and]
  have hbit := bitsVal_testBit_eq (fun i : Fin 8 ↦ x ⟨25 + i.val, by omega⟩) ⟨d.val, by omega⟩
  change (c8Of33 x).val.testBit d.val = _ at hbit
  rw [hmod, hbit]
  rcases bit_cases (x ⟨25 + d.val, by omega⟩) with hx | hx <;> simp [hx, b2z]
theorem x_idxHi3_eq_b2z (x : BitAssignment 33) (d : Fin 3) :
    x ⟨30 + d.val, by omega⟩ = b2z ((hi3Of33 x).val.testBit d.val) := by
  have hdiv : (hi3Of33 x).val.testBit d.val = (c8Of33 x).val.testBit (5 + d.val) :=
    testBit_div_two_powAux (c8Of33 x).val 5 d.val
  have hbit := bitsVal_testBit_eq (fun i : Fin 8 ↦ x ⟨25 + i.val, by omega⟩) ⟨5 + d.val, by omega⟩
  change (c8Of33 x).val.testBit (5 + d.val) = _ at hbit
  have hidx : (⟨30 + d.val, by omega⟩ : Wire 33) = ⟨25 + (5 + d.val), by omega⟩ :=
    Fin.ext (by dsimp; omega)
  rw [hdiv, hbit, hidx]
  rcases bit_cases (x ⟨25 + (5 + d.val), by omega⟩) with hx | hx <;> simp [hx, b2z]
theorem G3_lt33 (x : BitAssignment 33) (w : Wire 198) (hw : w.val < 33) :
    G3 x w = x ⟨w.val, hw⟩ := by
  dsimp [G3, pad125To198]
  rw [dite_eq_left (by omega : w.val < 125), pStage1Copy125_evalBits_γ2 x ⟨w.val, by omega⟩,
    ite_eq_right (by dsimp; omega)]
  dsimp [γ2_125]
  rw [dite_eq_left hw]
theorem G3_out8Loc (x : BitAssignment 33) (r : Fin 8) :
    G3 x (out8Loc r) = mobiusTargetBits (hi3Of33 x) r := by
  have hr125 : (out8Loc r).val < 125 := by revert r; decide
  have hr_not_kc : ¬ (33 ≤ (out8Loc r).val ∧ (out8Loc r).val < 49) := by revert r; decide
  dsimp [G3, pad125To198]
  rw [dite_eq_left hr125, pStage1Copy125_evalBits_γ2 x ⟨(out8Loc r).val, hr125⟩,
    ite_eq_right hr_not_kc]
  exact γ2_125_out8Loc x r hr125
theorem G3_out32Loc (x : BitAssignment 33) (q : Fin 32) :
    G3 x (out32Loc q) = mobiusTargetBits (lo5Of33 x) q := by
  have hq125 : (out32Loc q).val < 125 := by revert q; decide
  have hq_not_kc : ¬ (33 ≤ (out32Loc q).val ∧ (out32Loc q).val < 49) := by revert q; decide
  dsimp [G3, pad125To198]
  rw [dite_eq_left hq125, pStage1Copy125_evalBits_γ2 x ⟨(out32Loc q).val, hq125⟩,
    ite_eq_right hq_not_kc]
  exact γ2_125_out32Loc x q hq125
theorem G3_ge89 (x : BitAssignment 33) (w : Wire 198) (hw : 89 ≤ w.val) : G3 x w = 0 := by
  dsimp [G3, pad125To198]
  by_cases hw125 : w.val < 125
  · rw [dite_eq_left hw125, pStage1Copy125_evalBits_γ2 x ⟨w.val, hw125⟩,
      ite_eq_right (by dsimp; omega)]
    dsimp [γ2_125]
    rw [dite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega),
      dite_eq_right (by omega)]
  · rw [dite_eq_right hw125]
theorem G3_on_rDeg1_16 (x : BitAssignment 33) :
    (fun i : Fin 16 ↦ G3 x (rDeg1_16In198 i)) = in16OfHi3Lo5 (hi3Of33 x) (lo5Of33 x) := by
  funext i
  rw [rDeg1_16In198_apply]
  by_cases hi3 : i.val < 3
  · dsimp [deg1Loc, in16OfHi3Lo5]
    rw [dite_eq_left hi3, ite_eq_left hi3,
      G3_lt33 x (idxHi3Loc ⟨i.val, hi3⟩) (by dsimp [idxHi3Loc]; omega)]
    exact x_idxHi3_eq_b2z x ⟨i.val, hi3⟩
  · by_cases hi8 : i.val < 8
    · dsimp [deg1Loc, in16OfHi3Lo5]
      rw [dite_eq_right hi3, dite_eq_left hi8, ite_eq_right hi3, ite_eq_left hi8,
        G3_lt33 x (idxLo5Loc ⟨i.val - 3, by omega⟩) (by dsimp [idxLo5Loc]; omega)]
      exact x_idxLo5_eq_b2z x ⟨i.val - 3, by omega⟩
    · have hi_ge8 : 8 ≤ i.val := Nat.le_of_not_lt hi8
      have h_cases : i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨
          i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 := by
        have := i.isLt; omega
      rcases h_cases with h | h | h | h | h | h | h | h
      · have hieq : i = ⟨8, by decide⟩ := Fin.ext h
        subst hieq
        change G3 x (out8Loc ⟨1, by decide⟩) = mobiusTargetBits (hi3Of33 x) ⟨1, by decide⟩
        exact G3_out8Loc x ⟨1, by decide⟩
      · have hieq : i = ⟨9, by decide⟩ := Fin.ext h
        subst hieq
        change G3 x (out8Loc ⟨2, by decide⟩) = mobiusTargetBits (hi3Of33 x) ⟨2, by decide⟩
        exact G3_out8Loc x ⟨2, by decide⟩
      · have hieq : i = ⟨10, by decide⟩ := Fin.ext h
        subst hieq
        change G3 x (out8Loc ⟨4, by decide⟩) = mobiusTargetBits (hi3Of33 x) ⟨4, by decide⟩
        exact G3_out8Loc x ⟨4, by decide⟩
      · have hieq : i = ⟨11, by decide⟩ := Fin.ext h
        subst hieq
        change G3 x (out32Loc ⟨1, by decide⟩) = mobiusTargetBits (lo5Of33 x) ⟨1, by decide⟩
        exact G3_out32Loc x ⟨1, by decide⟩
      · have hieq : i = ⟨12, by decide⟩ := Fin.ext h
        subst hieq
        change G3 x (out32Loc ⟨2, by decide⟩) = mobiusTargetBits (lo5Of33 x) ⟨2, by decide⟩
        exact G3_out32Loc x ⟨2, by decide⟩
      · have hieq : i = ⟨13, by decide⟩ := Fin.ext h
        subst hieq
        change G3 x (out32Loc ⟨4, by decide⟩) = mobiusTargetBits (lo5Of33 x) ⟨4, by decide⟩
        exact G3_out32Loc x ⟨4, by decide⟩
      · have hieq : i = ⟨14, by decide⟩ := Fin.ext h
        subst hieq
        change G3 x (out32Loc ⟨8, by decide⟩) = mobiusTargetBits (lo5Of33 x) ⟨8, by decide⟩
        exact G3_out32Loc x ⟨8, by decide⟩
      · have hieq : i = ⟨15, by decide⟩ := Fin.ext h
        subst hieq
        change G3 x (out32Loc ⟨16, by decide⟩) = mobiusTargetBits (lo5Of33 x) ⟨16, by decide⟩
        exact G3_out32Loc x ⟨16, by decide⟩
theorem step3_zero8_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G3 S)
      (combStateOp rAct33 rSub hDisj G3_comp S)
      (.circuit ((cZeroDeg1_16.onRegister (rComb.compose rDeg1_16In198)).toCircuit)) := by
  intro rComb
  refine subspaceStep_congr_out (subspaceStep_of_circuit _ _) ?_
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul,
      CliffProg.toCircuit_eval_ket, cliff_onRegister_compose_eval]
    let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
    refine congrArg (S x • ·) (congrArg ket (congrArg (writeRegProg α rComb) ?_))
    rw [cliff_onRegister_eval_eq_writeRegProg (G3 x) rDeg1_16In198 cZeroDeg1_16,
      G3_on_rDeg1_16 x, cZeroDeg1_16_eval_in16_eq]
    rfl
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem step5_unzero8_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G3_comp S)
      (combStateOp rAct33 rSub hDisj G3 S)
      (.circuit ((cZeroDeg1_16.onRegister (rComb.compose rDeg1_16In198)).toCircuit)) := by
  intro rComb
  refine subspaceStep_congr_out (subspaceStep_of_circuit _ _) ?_
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul,
      CliffProg.toCircuit_eval_ket, cliff_onRegister_compose_eval]
    let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
    refine congrArg (S x • ·) (congrArg ket (congrArg (writeRegProg α rComb) ?_))
    rw [cliff_onRegister_eval_eq_writeRegProg (G3_comp x) rDeg1_16In198 cZeroDeg1_16]
    have hcomp_in : (fun i : Fin 16 ↦ G3_comp x (rDeg1_16In198 i)) = comp16OfHi3Lo5
        (hi3Of33 x) (lo5Of33 x) := funext fun i ↦ writeRegProg_apply_reg _ _ _ i
    rw [hcomp_in, cZeroDeg1_16_eval_comp16_eq, ← G3_on_rDeg1_16 x]
    funext w
    by_cases hmem : w ∈ Set.range rDeg1_16In198.wires
    · obtain ⟨i, rfl⟩ := hmem
      rw [writeRegProg_apply_reg]
    · rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem]
      exact writeRegProg_apply_of_not_mem (G3 x) rDeg1_16In198 _ w hmem
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem G3_comp_rClean119In198_eq_zero (x : BitAssignment 33) (j : Fin 119) :
    G3_comp x (rClean119In198 j) = 0 := by
  rw [rClean119In198_apply]
  by_cases hj8 : j.val < 8
  · dsimp only [clean119Loc]
    rw [dite_eq_left hj8]
    change writeRegProg (G3 x) rDeg1_16In198 (comp16OfHi3Lo5 (hi3Of33 x) (lo5Of33 x))
      (rDeg1_16In198 ⟨8 + j.val, by omega⟩) = 0
    rw [writeRegProg_apply_reg]
    dsimp [comp16OfHi3Lo5]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · dsimp only [clean119Loc]
    rw [dite_eq_right hj8]
    have hge87 : 87 ≤ 87 + (j.val - 8) := by omega
    have hnot16 : (⟨87 + (j.val - 8), by omega⟩ : Wire 198) ∉ Set.range rDeg1_16In198.wires := by
      rintro ⟨i, hi⟩
      have hle71 := deg1Loc_le_71 i
      have hv := congrArg Fin.val hi
      rw [rDeg1_16In198_apply] at hv
      dsimp at hv
      omega
    dsimp only [G3_comp]
    rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot16]
    by_cases hj8_eq : j.val = 8
    · have hw87 : (⟨87 + (j.val - 8), by omega⟩ : Wire 198) = out8Loc ⟨0, by decide⟩ :=
        Fin.ext (by dsimp [out8Loc]; omega)
      rw [hw87, G3_out8Loc]
      rfl
    · by_cases hj9_eq : j.val = 9
      · have hw88 : (⟨87 + (j.val - 8), by omega⟩ : Wire 198) = out32Loc ⟨0, by decide⟩ :=
          Fin.ext (by dsimp [out32Loc]; omega)
        rw [hw88, G3_out32Loc]
        rfl
      · exact G3_ge89 x _ (by dsimp; omega)
theorem G3_comp_lt49_eq_G49 (x : BitAssignment 33) (w : Wire 198) (hw : w.val < 49) :
    G3_comp x w = G49 x w := by
  have hG3 : G3 x w = G49 x w := by
    by_cases hw33 : w.val < 33
    · rw [G3_lt33 x w hw33, G49_lt33 x w hw33]
    · have hkc : 33 ≤ w.val ∧ w.val < 49 := ⟨Nat.le_of_not_lt hw33, hw⟩
      dsimp [G3, pad125To198, G49]
      rw [dite_eq_left (by omega : w.val < 125), pStage1Copy125_evalBits_γ2 x ⟨w.val, by omega⟩,
        ite_eq_left hkc, ite_eq_left hkc]
  rw [← hG3]
  dsimp [G3_comp]
  by_cases hmem : w ∈ Set.range rDeg1_16In198.wires
  · obtain ⟨i, rfl⟩ := hmem
    rw [writeRegProg_apply_reg]
    have hi8 : i.val < 8 := by
      by_contra hge
      have hge49 := deg1Loc_ge_49_of_ge_8 i (Nat.le_of_not_lt hge)
      rw [rDeg1_16In198_apply] at hw
      omega
    have hin : G3 x (rDeg1_16In198 i) = in16OfHi3Lo5 (hi3Of33 x) (lo5Of33 x) i :=
      congrFun (G3_on_rDeg1_16 x) i
    rw [hin]
    dsimp [comp16OfHi3Lo5, in16OfHi3Lo5]
    by_cases hi3 : i.val < 3
    · rw [ite_eq_left hi3, ite_eq_left hi3]
    · rw [ite_eq_right hi3, ite_eq_left hi8, ite_eq_right hi3, ite_eq_left hi8]
  · exact writeRegProg_apply_of_not_mem _ _ _ _ hmem
theorem writeRegProg_G3_comp_r49_eq {n : ℕ} (α : BitAssignment n) (rComb : QRegister 198 n)
    (x : BitAssignment 33) : (fun i : Fin 49 ↦ writeRegProg α rComb (G3_comp x) (rComb.compose
    r49In198 i)) = xorRightMapGen tblBits16 (padZeroBits x) := by
  rw [← writeRegProg_G49_r49_eq α rComb x]
  funext i
  change writeRegProg α rComb (G3_comp x) (rComb (r49In198 i)) =
    writeRegProg α rComb (G49 x) (rComb (r49In198 i))
  rw [writeRegProg_apply_reg, writeRegProg_apply_reg]
  exact G3_comp_lt49_eq_G49 x (r49In198 i) (by rw [r49In198_apply]; exact i.isLt)
theorem step4_200_subspaceStep_gen
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rAct33 : QRegister 33 n) (rSub : QRegister 165 n) (rExtra35 : QRegister 35 n)
    (hDisj : rAct33.DisjointWires rSub)
    (hCombEx : (rAct33.concat rSub hDisj).DisjointWires rExtra35)
    (G_mid : BitAssignment 33 → BitAssignment 198)
    (α49Of : BitAssignment 33 → BitAssignment 49)
    (dStep4 : DynamicCircuit Var n)
    (pred49 : BitAssignment 49 → ZMod 2)
    (pred33 : BitAssignment 33 → ZMod 2)
    (hClean : ∀ (x : BitAssignment 33) (j : Fin 119), G_mid x (rClean119In198 j) = 0)
    (hAct : ∀ (α : BitAssignment n) (rComb : QRegister 198 n) (x : BitAssignment 33),
      (fun i : Fin 49 ↦ writeRegProg α rComb (G_mid x) (rComb.compose r49In198 i)) = α49Of x)
    (hPredEq : ∀ x : BitAssignment 33, pred49 (α49Of x) = pred33 x)
    (hr0 : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      ((rAct33.concat rSub hDisj).compose r49In198)
      (((rAct33.concat rSub hDisj).compose rClean119In198).concat rExtra35 (hCombEx.compose_left _))
      (phaseDiagUnitary pred49) dStep4) :
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G_mid (fun _ ↦ 1) * rExtra35.basisOutcomeProjector 0)
      (combStateOp rAct33 rSub hDisj G_mid (fun x ↦ bitSign (pred33 x)) *
        rExtra35.basisOutcomeProjector 0)
      dStep4 := by
  let rComb := rAct33.concat rSub hDisj
  let rClean154 := (rComb.compose rClean119In198).concat rExtra35 (hCombEx.compose_left _)
  let P35 := rExtra35.basisOutcomeProjector 0
  have hPR : rClean154.basisOutcomeProjector 0 *
      (combStateOp rAct33 rSub hDisj G_mid (fun _ ↦ 1) * P35) =
      combStateOp rAct33 rSub hDisj G_mid (fun _ ↦ 1) * P35 := by
    apply matrix_ext_ket; intro α
    rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_basisOutcomeProjector_zero]
    by_cases h35 : ∀ k : Fin 35, α (rExtra35 k) = 0
    · rw [ite_eq_left h35, combStateOp, mkVecOp_mulVec_ket]
      by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
      · rw [ite_eq_left h0, one_smul, ket_basisOutcomeProjector_zero]
        have hz : ∀ idx : Fin (119 + 35),
            writeRegProg α rComb (G_mid (fun i ↦ α (rAct33 i))) (rClean154 idx) = 0 := by
          intro idx
          refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) idx
          · dsimp only [rClean154]
            rw [QRegister.concat_apply_left]
            change writeRegProg α rComb (G_mid (fun i ↦ α (rAct33 i)))
              (rComb (rClean119In198 j)) = 0
            rw [writeRegProg_apply_reg]
            exact hClean _ j
          · dsimp only [rClean154]
            rw [QRegister.concat_apply_right]
            have hnot : rExtra35 k ∉ Set.range rComb.wires := by
              rintro ⟨m, hm⟩
              exact hCombEx.ne m k hm
            rw [writeRegProg_apply_of_not_mem _ _ _ _ hnot]
            exact h35 k
        rw [ite_eq_left hz]
      · rw [ite_eq_right h0, Matrix.mulVec_zero]
    · rw [ite_eq_right h35, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have s := subspaceStep_of_realizesCleanWorkspace hr0
    (combStateOp rAct33 rSub hDisj G_mid (fun _ ↦ 1) * P35) hPR
  refine subspaceStep_congr_out s ?_
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ket_basisOutcomeProjector_zero]
  by_cases h35 : ∀ k : Fin 35, α (rExtra35 k) = 0
  · rw [ite_eq_left h35, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
    by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
    · rw[ite_eq_left h0, ite_eq_left h0, one_smul, embedUnitary_phaseDiagUnitary_mulVec_ket,
        hAct α rComb (fun i ↦ α (rAct33 i)), hPredEq (fun i ↦ α (rAct33 i))]
    · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
  · rw [ite_eq_right h35, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem step4_200_subspaceStep {mWork : ℕ} (hmW : 200 ≤ mWork)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rWork : QRegister mWork n)
    (hDisj : rAct33.DisjointWires rWork) :
    let rSub : QRegister 165 n := rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)
    let rExtra35 : QRegister 35 n := rWork.slice 165 35 hmW
    let hDisjSub : rAct33.DisjointWires rSub := hDisj.compose_right _
    let rComb : QRegister 198 n := rAct33.concat rSub hDisjSub
    let hCombEx := rComb_rExtra35_disj hmW rAct33 rWork hDisj
    let rClean154 : QRegister (119 + 35) n :=
      (rComb.compose rClean119In198).concat rExtra35 (hCombEx.compose_left _)
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisjSub G3_comp (fun _ ↦ 1) * rExtra35.basisOutcomeProjector 0)
      (combStateOp rAct33 rSub hDisjSub G3_comp (fun x ↦ bitSign (predCoarseGood33 x)) *
        rExtra35.basisOutcomeProjector 0)
      (dStage234_49_fast154 v (rComb.compose r49In198) rClean154
        (r49_rClean119_35_disj hmW rAct33 rWork hDisj)) := by
  intro rSub rExtra35 hDisjSub rComb hCombEx rClean154
  exact step4_200_subspaceStep_gen rAct33 rSub rExtra35 hDisjSub hCombEx G3_comp
    (fun x ↦ xorRightMapGen tblBits16 (padZeroBits x)) (dStage234_49_fast154 v (rComb.compose
    r49In198) rClean154 (r49_rClean119_35_disj hmW rAct33 rWork hDisj)) phaseStage234_49
    predCoarseGood33 G3_comp_rClean119In198_eq_zero writeRegProg_G3_comp_r49_eq
    phaseStage234_49_on_stage1 (dStage234_49_fast154_realizes v (rComb.compose r49In198)
    rClean154 (r49_rClean119_35_disj hmW rAct33 rWork hDisj))
theorem step6a_200_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    ∀ (m : ℕ) (hm : m ≤ 16),
      SubspaceStep (Var := Var)
        (combStateOp rAct33 rSub hDisj (Gkc m) S)
        (combStateOp rAct33 rSub hDisj (Gkc 0) S)
        (dUnloadKc16_32x8 v (rAct33.concat rSub hDisj) m hm)
  | 0, _ => by
      simpa only [dUnloadKc16_32x8, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
        subspaceStep_of_circuit (Var := Var) (combStateOp rAct33 rSub hDisj (Gkc 0) S) .identity
  | m + 1, hm => by
      let rComb := rAct33.concat rSub hDisj
      let j : Fin 16 := ⟨m, hm⟩
      let wOut32 := fun q : Fin 32 ↦ rComb (out32Loc q)
      let wOut8 := fun r : Fin 8 ↦ rComb (out8Loc r)
      have hDisj32_8 : ∀ q r, wOut32 q ≠ wOut8 r :=
        fun q r ↦ rComb.wires.injective.ne (out32Loc_ne_out8Loc q r)
      let pairs := kcPairs32x8 j wOut32 wOut8 hDisj32_8
      let f : BitAssignment n → ZMod 2 := czPairsParity pairs
      have hf : ∀ β a, f (Function.update β (rComb (kc16Loc j)) a) = f β :=
        fun β a ↦ czPairsParity_kcPairs32x8_update j wOut32 wOut8 hDisj32_8 (rComb (kc16Loc j))
          (fun q ↦ rComb.wires.injective.ne (out32Loc_ne_kc16Loc q j))
          (fun r ↦ rComb.wires.injective.ne (out8Loc_ne_kc16Loc r j)) β a
      have hq0 : projBit_dqmu (rComb (kc16Loc j)) 0 * combStateOp rAct33 rSub hDisj (Gkc m) S
          = combStateOp rAct33 rSub hDisj (Gkc m) S := by
        apply matrix_ext_ket; intro α
        rw [← Matrix.mulVec_mulVec, combStateOp, mkVecOp_mulVec_ket]
        by_cases h0 : ∀ k : Fin 165, α (rSub k) = 0
        · rw [ite_eq_left h0, Matrix.mulVec_smul, projBit_dqmu, ket_projector_zero,
            writeRegProg_apply_reg]
          have hbit0 : Gkc m (fun i ↦ α (rAct33 i)) (kc16Loc j) = 0 := by
            dsimp [Gkc]
            have hnot : ¬ (33 ≤ (kc16Loc j).val ∧ (kc16Loc j).val < 33 + m ∧ m ≤ 16) := by
              dsimp [kc16Loc, j]; omega
            rw [ite_eq_right hnot]
            dsimp [G1, G1a]
            rw [Function.update_of_ne (out32Loc_ne_kc16Loc _ j).symm,
              Function.update_of_ne (out8Loc_ne_kc16Loc _ j).symm,
              G0_ge _ (kc16Loc j) (by dsimp [kc16Loc]; omega)]
          rw [hbit0, ite_eq_left rfl]
        · rw [ite_eq_right h0, Matrix.mulVec_zero]
      have ih := step6a_200_subspaceStep v rAct33 rSub hDisj S m (Nat.le_of_succ_le hm)
      have s := subspaceStep_xUnloadCzPairsSeqDyn v (rComb (kc16Loc j)) pairs
        (dUnloadKc16_32x8 v rComb m (Nat.le_of_succ_le hm)) f hf (fun _ ↦ rfl)
        (combStateOp rAct33 rSub hDisj (Gkc m) S)
        (combStateOp rAct33 rSub hDisj (Gkc 0) S) hq0 ih
      refine subspaceStep_congr_in ?_ s
      apply matrix_ext_ket; intro α
      rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
      by_cases h0 : ∀ k : Fin 165, α (rSub k) = 0
      · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul, xorWireUnitary_mulVec_ket]
        let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
        let β := writeRegProg α rComb (Gkc m x)
        have hpar : f β = b2z ((getNatAt kcTable49168List (c8Of33 x).val).testBit m) := by
          dsimp [f, pairs]
          refine czPairsParity_kcPairs32x8_oneHot j wOut32 wOut8 hDisj32_8 β (c8Of33 x)
            (fun q ↦ ?_) (fun r ↦ ?_)
          · change writeRegProg α rComb (Gkc m x) (rComb (out32Loc q)) = _
            rw [writeRegProg_apply_reg]
            dsimp [Gkc]
            have hnot : ¬ (33 ≤ (out32Loc q).val ∧ (out32Loc q).val < 33 + m ∧ m ≤ 16) := by
              have hq := out32Loc_ge_56 q
              omega
            rw [ite_eq_right hnot]
            dsimp [G1, G1a]
            by_cases hq : q = lo5Of33 x
            · subst hq
              rw [Function.update_self]
              have hlo_eq : (lo5Of33 x).val = (c8Of33 x).val % 32 := rfl
              rw [ite_eq_left hlo_eq]
            · have hq_val : q.val ≠ (c8Of33 x).val % 32 := fun hv ↦ hq (Fin.ext hv)
              rw [Function.update_of_ne (out32Loc_inj.ne hq), ite_eq_right hq_val,
                Function.update_of_ne (out32Loc_ne_out8Loc q (hi3Of33 x)),
                G0_ge x (out32Loc q) (by have := out32Loc_ge_56 q; omega)]
          · change writeRegProg α rComb (Gkc m x) (rComb (out8Loc r)) = _
            rw [writeRegProg_apply_reg]
            dsimp [Gkc]
            have hnot : ¬ (33 ≤ (out8Loc r).val ∧ (out8Loc r).val < 33 + m ∧ m ≤ 16) := by
              have hr := out8Loc_ge_49 r
              omega
            rw [ite_eq_right hnot]
            dsimp [G1, G1a]
            rw [Function.update_of_ne (out32Loc_ne_out8Loc (lo5Of33 x) r).symm]
            by_cases hr : r = hi3Of33 x
            · subst hr
              rw [Function.update_self]
              have hhi_eq : (hi3Of33 x).val = (c8Of33 x).val / 32 := rfl
              rw [ite_eq_left hhi_eq]
            · have hr_val : r.val ≠ (c8Of33 x).val / 32 := fun hv ↦ hr (Fin.ext hv)
              rw [Function.update_of_ne (out8Loc_inj.ne hr), ite_eq_right hr_val,
                G0_ge x (out8Loc r) (by have := out8Loc_ge_49 r; omega)]
        have hβj : β (rComb (kc16Loc j)) = 0 := by
          dsimp [β]
          rw [writeRegProg_apply_reg]
          dsimp [Gkc]
          have hnot : ¬ (33 ≤ (kc16Loc j).val ∧ (kc16Loc j).val < 33 + m ∧ m ≤ 16) := by
            dsimp [kc16Loc, j]; omega
          rw [ite_eq_right hnot]
          dsimp [G1, G1a]
          rw [Function.update_of_ne (out32Loc_ne_kc16Loc _ j).symm,
            Function.update_of_ne (out8Loc_ne_kc16Loc _ j).symm,
            G0_ge _ (kc16Loc j) (by dsimp [kc16Loc]; omega)]
        change S x • ket (writeRegProg α rComb (Gkc (m + 1) x)) =
          S x • ket (Function.update β (rComb (kc16Loc j)) (β (rComb (kc16Loc j)) + f β))
        rw [hpar, hβj, zero_add]
        dsimp [β]
        rw [update_writeRegProg]
        refine congrArg (S x • ·) (congrArg ket (congrArg (writeRegProg α rComb) ?_))
        funext w
        by_cases hw : w = kc16Loc j
        · subst hw
          rw [Function.update_self]
          dsimp [Gkc, kc16Loc, j]
          have hyes : 33 ≤ 33 + m ∧ 33 + m < 33 + (m + 1) ∧ m + 1 ≤ 16 := by omega
          rw [ite_eq_left hyes, show 33 + m - 33 = m by omega]
        · rw [Function.update_of_ne hw]
          dsimp [Gkc]
          have hw_ne : w.val ≠ 33 + m := fun hv ↦ hw (Fin.ext hv)
          have hiff : (33 ≤ w.val ∧ w.val < 33 + (m + 1) ∧ m + 1 ≤ 16) ↔
              (33 ≤ w.val ∧ w.val < 33 + m ∧ m ≤ 16) := by omega
          by_cases hcond : 33 ≤ w.val ∧ w.val < 33 + m ∧ m ≤ 16
          · rw [ite_eq_left (hiff.mpr hcond), ite_eq_left hcond]
          · rw [ite_eq_right (fun h ↦ hcond (hiff.mp h)), ite_eq_right hcond]
      · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem Gkc_zero_eq_G1 : Gkc 0 = G1 := by
  funext x w
  dsimp [Gkc]
  have hnot : ¬ (33 ≤ w.val ∧ w.val < 33 + 0 ∧ 0 ≤ 16) := by omega
  rw [ite_eq_right hnot]
theorem step6b_200_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G1 S)
      (combStateOp rAct33 rSub hDisj G1a S)
      (wStateUncomputeUncondPow2 4 v (fun d ↦ rComb (idxLo5Loc d))
        (fun q ↦ rComb (out32Loc q))) := by
  intro rComb
  have hd32 := wUncondDisj32_lift rComb
  have hSupp : SupportedOn (ValidWUncondClean (fun q ↦ rComb (out32Loc q)))
      (combStateOp rAct33 rSub hDisj G1a S) :=
    supportedOn_combStateOp rAct33 rSub hDisj G1a S fun α q ↦ by
      rw [writeRegProg_apply_reg]
      dsimp [G1a]
      rw [Function.update_of_ne (out32Loc_ne_out8Loc q _)]
      exact G0_ge _ (out32Loc q) (by have := out32Loc_ge_56 q; omega)
  have s := subspaceStep_wStateUncomputeUncondPow2 4 v
    (fun d ↦ rComb (idxLo5Loc d)) (fun q ↦ rComb (out32Loc q))
    ⟨hd32.1, hd32.2.2.1⟩ (combStateOp rAct33 rSub hDisj G1a S) hSupp
  refine subspaceStep_congr_in ?_ s
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul, uOneHotUncond_mulVec_ket]
    let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
    have hidx : (⟨idxValD (fun d ↦ rComb (idxLo5Loc d)) (writeRegProg α rComb (G1a x)),
        idxValD_lt_two_pow _ _⟩ : Fin 32) = lo5Of33 x := by
      apply Fin.ext
      exact idxValD_lo5_on_G rComb α (G1a x) x fun d ↦ by
        dsimp [G1a]
        rw [Function.update_of_ne (by generalize hi3Of33 x = r; revert d r; decide)]
        exact G0_lt x (idxLo5Loc d) (by revert d; decide)
    have h0_32 : G1a x (out32Loc (lo5Of33 x)) = 0 := by
      dsimp [G1a]
      rw [Function.update_of_ne (out32Loc_ne_out8Loc (lo5Of33 x) (hi3Of33 x))]
      exact G0_ge x (out32Loc (lo5Of33 x)) (by have := out32Loc_ge_56 (lo5Of33 x); omega)
    rw [hidx, writeRegProg_apply_reg, h0_32, zero_add, update_writeRegProg]
    rfl
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem step6c_200_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rSub : QRegister 165 n)
    (hDisj : rAct33.DisjointWires rSub) (S : BitAssignment 33 → ℂ) :
    let rComb := rAct33.concat rSub hDisj
    SubspaceStep (Var := Var)
      (combStateOp rAct33 rSub hDisj G1a S)
      (combStateOp rAct33 rSub hDisj G0 S)
      (wStateUncomputeUncondPow2 2 v (fun d ↦ rComb (idxHi3Loc d))
        (fun r ↦ rComb (out8Loc r))) := by
  intro rComb
  have hd8 := wUncondDisj8_lift rComb
  have hSupp : SupportedOn (ValidWUncondClean (fun r ↦ rComb (out8Loc r)))
      (combStateOp rAct33 rSub hDisj G0 S) :=
    supportedOn_combStateOp rAct33 rSub hDisj G0 S fun α r ↦ by
      rw [writeRegProg_apply_reg]
      exact G0_ge _ (out8Loc r) (by have := out8Loc_ge_49 r; omega)
  have s := subspaceStep_wStateUncomputeUncondPow2 2 v
    (fun d ↦ rComb (idxHi3Loc d)) (fun r ↦ rComb (out8Loc r))
    ⟨hd8.1, hd8.2.2.1⟩ (combStateOp rAct33 rSub hDisj G0 S) hSupp
  refine subspaceStep_congr_in ?_ s
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, combStateOp, combStateOp, mkVecOp_mulVec_ket, mkVecOp_mulVec_ket]
  by_cases h0 : ∀ j : Fin 165, α (rSub j) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, Matrix.mulVec_smul, uOneHotUncond_mulVec_ket]
    let x : BitAssignment 33 := fun i ↦ α (rAct33 i)
    have hidx : (⟨idxValD (fun d ↦ rComb (idxHi3Loc d)) (writeRegProg α rComb (G0 x)),
        idxValD_lt_two_pow _ _⟩ : Fin 8) = hi3Of33 x := by
      apply Fin.ext
      exact idxValD_hi3_on_G rComb α (G0 x) x fun d ↦
        G0_lt x (idxHi3Loc d) (by revert d; decide)
    rw [hidx, writeRegProg_apply_reg,
      G0_ge x (out8Loc (hi3Of33 x)) (by have := out8Loc_ge_49 (hi3Of33 x); omega),
      zero_add, update_writeRegProg]
    rfl
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
theorem dCoarseGood33_200_wstate_realizes {mWork : ℕ} (hmW : 200 ≤ mWork)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rWork : QRegister mWork n)
    (hDisj : rAct33.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork
      (phaseDiagUnitary predCoarseGood33) (dCoarseGood33_200_wstate hmW v rAct33 rWork hDisj) := by
  let rSub : QRegister 165 n := rWork.slice 0 165 (le_trans (by decide : 165 ≤ 200) hmW)
  let rExtra35 : QRegister 35 n := rWork.slice 165 35 hmW
  let hSE := rWork_165_35_disj hmW rWork
  let hDisjSub : rAct33.DisjointWires rSub := hDisj.compose_right _
  let P35 := rExtra35.basisOutcomeProjector 0
  let S₁ : BitAssignment 33 → ℂ := fun _ ↦ 1
  let S₂ : BitAssignment 33 → ℂ := fun x ↦ bitSign (predCoarseGood33 x)
  have s1a := SubspaceStep.mul_right (step1a_subspaceStep (Var :=
    Var) v rAct33 rSub hDisjSub S₁) P35
  have s1b := SubspaceStep.mul_right (step1b_subspaceStep (Var :=
    Var) v rAct33 rSub hDisjSub S₁) P35
  have s2 := SubspaceStep.mul_right (step2_subspaceStep (Var := Var) rAct33 rSub hDisjSub S₁) P35
  have s3 := SubspaceStep.mul_right (step3_subspaceStep (Var := Var) v rAct33 rSub hDisjSub S₁) P35
  have s3z := SubspaceStep.mul_right (step3_zero8_subspaceStep (Var :=
    Var) rAct33 rSub hDisjSub S₁) P35
  have s4 := step4_200_subspaceStep (Var := Var) hmW v rAct33 rWork hDisj
  have s5uz := SubspaceStep.mul_right (step5_unzero8_subspaceStep (Var :=
    Var) rAct33 rSub hDisjSub S₂) P35
  have s5 := SubspaceStep.mul_right (step5_subspaceStep (Var := Var) rAct33 rSub hDisjSub S₂) P35
  have s6a0 := step6a_200_subspaceStep (Var := Var) v rAct33 rSub hDisjSub S₂ 16 le_rfl
  rw [Gkc_zero_eq_G1] at s6a0
  have s6a := SubspaceStep.mul_right s6a0 P35
  have s6b := SubspaceStep.mul_right (step6b_200_subspaceStep (Var :=
    Var) v rAct33 rSub hDisjSub S₂) P35
  have s6c := SubspaceStep.mul_right (step6c_200_subspaceStep (Var :=
    Var) v rAct33 rSub hDisjSub S₂) P35
  have sAll :=
    s1a.seq (s1b.seq (s2.seq (s3.seq (s3z.seq (s4.seq (s5uz.seq (s5.seq (s6a.seq (s6b.seq
    s6c)))))))))
  have hP200 : rSub.basisOutcomeProjector 0 * P35 =
      (rWork.slice 0 200 hmW).basisOutcomeProjector 0 := by
    rw [← QRegExt.concat_basisOutcomeProjector_zero rSub rExtra35 hSE,
      rSub_concat_rExtra35_eq_slice200 hmW rWork]
  rw[combStateOp_G0_one rAct33 rSub hDisjSub, combStateOp_G0_phase rAct33 rSub hDisjSub,
      Matrix.mul_assoc, hP200] at sAll
  exact (realizesCleanWorkspace_of_subspaceStep sAll).widenWorkspace
/-! ## Section 5: `dOaa33_200_wstate` (`1,112 T`), `dPrep3_216_gen200_wstate` (`1,229 T` = `2,458 T`
RT), & `slot3PrepAdaptiveSpec` -/
abbrev tPrep216_200_wstate : ℕ := 1229
abbrev tPrep216_200_wstate_RT : ℕ := 2458
noncomputable def dOaa33_200_wstate {Var : Type} {n : ℕ} (v : Var) (rAct33 : QRegister 33 n)
    (rWork : QRegister 200 n) (hDisj : rAct33.DisjointWires rWork) : DynamicCircuit Var n :=
  let rComb66 : QRegister (33 + 33) n :=
    rAct33.concat (rWork.slice 0 33 (by decide)) (hDisj.compose_right _)
  let dCoarse := dCoarseGood33_200_wstate (le_refl 200) v rAct33 rWork hDisj
  let dNZ := (progNotZero33Cz.onRegister rComb66).toDyn v
  let dH := hadamardPayloadDyn (Var := Var) rAct33
  .seq dCoarse (.seq dH (.seq dNZ dH))
noncomputable def dOaa33Inv_200_wstate {Var : Type} {n : ℕ} (v : Var)
    (rAct33 : QRegister 33 n) (rWork : QRegister 200 n)
    (hDisj : rAct33.DisjointWires rWork) : DynamicCircuit Var n :=
  let rComb66 : QRegister (33 + 33) n :=
    rAct33.concat (rWork.slice 0 33 (by decide)) (hDisj.compose_right _)
  let dCoarse := dCoarseGood33_200_wstate (le_refl 200) v rAct33 rWork hDisj
  let dNZ := (progNotZero33Cz.onRegister rComb66).toDyn v
  let dH := hadamardPayloadDyn (Var := Var) rAct33
  .seq dH (.seq dNZ (.seq dH dCoarse))
theorem dOaa33_200_wstate_counts {Var : Type} {n : ℕ} (v : Var) (rAct33 : QRegister 33 n)
    (rWork : QRegister 200 n) (hDisj : rAct33.DisjointWires rWork) :
    (dOaa33_200_wstate v rAct33 rWork hDisj).count toffoli = 0 ∧
    (dOaa33Inv_200_wstate v rAct33 rWork hDisj).count toffoli = 0 ∧
    (dOaa33_200_wstate v rAct33 rWork hDisj).count T = 1112 ∧
    (dOaa33Inv_200_wstate v rAct33 rWork hDisj).count T = 1112 := by
  let rComb66 : QRegister (33 + 33) n :=
    rAct33.concat (rWork.slice 0 33 (by decide)) (hDisj.compose_right _)
  have fNZ : ((progNotZero33Cz.onRegister rComb66).toDyn v).count toffoli = 0 :=
    TempCzProg.toDyn_count_toff v (progNotZero33Cz.onRegister rComb66)
  have fH : (hadamardPayloadDyn (Var := Var) rAct33).count toffoli = 0 :=
    count_hadamardPayloadDyn_toff (Var := Var) rAct33
  dsimp only [rComb66] at fNZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dOaa33_200_wstate; dsimp only
    rw [dynCount_seq, dynCount_seq, dynCount_seq, dCoarseGood33_200_wstate_count_toff, fNZ, fH]
  · unfold dOaa33Inv_200_wstate; dsimp only
    rw [dynCount_seq, dynCount_seq, dynCount_seq, dCoarseGood33_200_wstate_count_toff, fNZ, fH]
  · unfold dOaa33_200_wstate; dsimp only
    rw [dynCount_seq, dynCount_seq, dynCount_seq, dCoarseGood33_200_wstate_count_t,
      TempCzProg.toDyn_count_t, TempCzProg.onRegister_countTempAnd,
      count_hadamardPayloadDyn_t, progNotZero33Cz_count]
  · unfold dOaa33Inv_200_wstate; dsimp only
    rw [dynCount_seq, dynCount_seq, dynCount_seq, dCoarseGood33_200_wstate_count_t,
      TempCzProg.toDyn_count_t, TempCzProg.onRegister_countTempAnd,
      count_hadamardPayloadDyn_t, progNotZero33Cz_count]
theorem dOaa33_of_coarse_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rWork : QRegister 200 n)
    (hDisj : rAct33.DisjointWires rWork)
    (dCoarse : DynamicCircuit Var n)
    (hrC : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork
      (phaseDiagUnitary predCoarseGood33) dCoarse) :
    let rComb66 : QRegister (33 + 33) n :=
      rAct33.concat (rWork.slice 0 33 (by decide)) (hDisj.compose_right _)
    let dNZ := (progNotZero33Cz.onRegister rComb66).toDyn v
    let dH := hadamardPayloadDyn (Var := Var) rAct33
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork uOaa33
      (.seq dCoarse (.seq dH (.seq dNZ dH))) ∧
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork uOaa33⁻¹
      (.seq dH (.seq dNZ (.seq dH dCoarse))) := by
  intro rComb66 dNZ dH
  obtain ⟨hvN, hbN, hsN⟩ := progNotZero33Cz_spec
  obtain ⟨hrN, _, _⟩ := realizes_phaseDiagUnitary_cleanWorkspace_cz
    v rAct33 rWork hDisj (by decide : 33 ≤ 200) predNotZero33 progNotZero33Cz hvN hbN hsN
  have hrH : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork h33Unitary dH :=
    by
    have hEq : hadamardPayloadUnitary 33 = h33Unitary := rfl
    rw [← hEq]
    exact hadamardPayloadDyn_realizes rAct33 rWork
  refine ⟨?_, ?_⟩
  · have h3 := realizesEmbedded_seq rAct33 rWork hDisj hrC (realizesEmbedded_seq rAct33 rWork
      hDisj hrH (realizesEmbedded_seq rAct33 rWork hDisj hrN hrH))
    have hu : ((h33Unitary * phaseDiagUnitary predNotZero33) * h33Unitary) *
        phaseDiagUnitary predCoarseGood33 = uOaa33 := by
      rw [phaseDiag_eq predNotZero33, phaseDiag_eq predCoarseGood33]; rfl
    rwa [hu] at h3
  · have h3 := realizesEmbedded_seq rAct33 rWork hDisj hrH (realizesEmbedded_seq rAct33 rWork
      hDisj hrN (realizesEmbedded_seq rAct33 rWork hDisj hrH hrC))
    have huInv : ((phaseDiagUnitary predCoarseGood33 * h33Unitary) *
        phaseDiagUnitary predNotZero33) * h33Unitary = uOaa33⁻¹ := by
      rw [phaseDiag_eq predNotZero33, phaseDiag_eq predCoarseGood33, uOaa33_inv_eq]
      simp only [mul_assoc]
    rwa [huInv] at h3
theorem dOaa33_200_wstate_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rAct33 : QRegister 33 n) (rWork : QRegister 200 n)
    (hDisj : rAct33.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork uOaa33
    (dOaa33_200_wstate v rAct33 rWork hDisj) ∧
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork uOaa33⁻¹
    (dOaa33Inv_200_wstate v rAct33 rWork hDisj) := dOaa33_of_coarse_realizes v rAct33 rWork
    hDisj (dCoarseGood33_200_wstate (le_refl 200) v rAct33 rWork hDisj)
    (dCoarseGood33_200_wstate_realizes (le_refl 200) v rAct33 rWork hDisj)
noncomputable def dPrep3_216_gen200_wstate {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {mPrep : ℕ} (hmPrep : 200 ≤ mPrep) {Var : Type} {n : ℕ}
    (v : Var) (rCore : QRegister (momCoreWires mPayload) n) (rWork : QRegister mPrep n)
    (hCW : rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  let rW200 : QRegister 200 n := rWork.compose (QRegister.block 0 200 hmPrep)
  let rAct33 : QRegister 33 n := rCore.compose (s3Coarse33Core hmPay)
  .seq
    (dOaa33_200_wstate v rAct33 rW200 ((hCW.compose_left _).compose_right _))
    (.circuit (cQutrit3CoreGen hmPay rCore))
noncomputable def dPrep3_216Inv_gen200_wstate {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {mPrep : ℕ} (hmPrep : 200 ≤ mPrep) {Var : Type} {n : ℕ}
    (v : Var) (rCore : QRegister (momCoreWires mPayload) n) (rWork : QRegister mPrep n)
    (hCW : rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  let rW200 : QRegister 200 n := rWork.compose (QRegister.block 0 200 hmPrep)
  let rAct33 : QRegister 33 n := rCore.compose (s3Coarse33Core hmPay)
  .seq
    (.circuit (cQutrit3CoreGen hmPay rCore).inverse)
    (dOaa33Inv_200_wstate v rAct33 rW200 ((hCW.compose_left _).compose_right _))
theorem dPrep3_216_gen200_wstate_count_toff {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {mPrep : ℕ} (hmPrep : 200 ≤ mPrep) {Var : Type} {n : ℕ}
    (v : Var) (rCore : QRegister (momCoreWires mPayload) n) (rWork : QRegister mPrep n)
    (hCW : rCore.DisjointWires rWork) :
    (dPrep3_216_gen200_wstate hmPay hmPrep v rCore rWork hCW).count toffoli = 0 ∧
    (dPrep3_216Inv_gen200_wstate hmPay hmPrep v rCore rWork hCW).count toffoli = 0 := by
  let rW200 : QRegister 200 n := rWork.compose (QRegister.block 0 200 hmPrep)
  let rAct33 : QRegister 33 n := rCore.compose (s3Coarse33Core hmPay)
  obtain ⟨htF, htI, _, _⟩ :=
    dOaa33_200_wstate_counts v rAct33 rW200 ((hCW.compose_left _).compose_right _)
  have hqF : (cQutrit3CoreGen hmPay rCore).count toffoli = 0 :=
    cQutrit3CoreGen_count_toff hmPay rCore
  have hqI : (cQutrit3CoreGen hmPay rCore).inverse.count toffoli = 0 :=
    cQutrit3CoreGen_inv_count_toff hmPay rCore
  refine ⟨?_, ?_⟩
  · unfold dPrep3_216_gen200_wstate; dsimp only
    rw [dynCount_seq, htF, dynCount_circuit, hqF]
  · unfold dPrep3_216Inv_gen200_wstate; dsimp only
    rw [dynCount_seq, dynCount_circuit, hqI, htI]
theorem dPrep3_216_gen200_wstate_count_t {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {mPrep : ℕ} (hmPrep : 200 ≤ mPrep) {Var : Type} {n : ℕ}
    (v : Var) (rCore : QRegister (momCoreWires mPayload) n) (rWork : QRegister mPrep n)
    (hCW : rCore.DisjointWires rWork) :
    (dPrep3_216_gen200_wstate hmPay hmPrep v rCore rWork hCW).count T = tPrep216_200_wstate ∧
    (dPrep3_216Inv_gen200_wstate hmPay hmPrep v rCore rWork hCW).count T = tPrep216_200_wstate := by
  let rW200 : QRegister 200 n := rWork.compose (QRegister.block 0 200 hmPrep)
  let rAct33 : QRegister 33 n := rCore.compose (s3Coarse33Core hmPay)
  obtain ⟨_, _, hcF, hcI⟩ :=
    dOaa33_200_wstate_counts v rAct33 rW200 ((hCW.compose_left _).compose_right _)
  refine ⟨?_, ?_⟩
  · unfold dPrep3_216_gen200_wstate tPrep216_200_wstate; dsimp only
    rw [dynCount_seq, hcF, dynCount_circuit, cQutrit3CoreGen_count_t]
  · unfold dPrep3_216Inv_gen200_wstate tPrep216_200_wstate; dsimp only
    rw [dynCount_seq, dynCount_circuit, cQutrit3CoreGen_inv_count_t, hcI]
theorem dPrep3_216_gen200_wstate_count_t_rt_le {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {mPrep : ℕ} (hmPrep : 200 ≤ mPrep) {Var : Type} {n : ℕ}
    (v : Var) (rCore : QRegister (momCoreWires mPayload) n) (rWork : QRegister mPrep n)
    (hCW : rCore.DisjointWires rWork) :
    (dPrep3_216_gen200_wstate hmPay hmPrep v rCore rWork hCW).count T +
      (dPrep3_216Inv_gen200_wstate hmPay hmPrep v rCore rWork hCW).count T ≤
        tPrep216_200_wstate_RT := by
  obtain ⟨h1, h2⟩ := dPrep3_216_gen200_wstate_count_t hmPay hmPrep v rCore rWork hCW
  rw [h1, h2]
  decide
theorem dPrep3_216_gen200_wstate_realizes {mPayload : ℕ} (hmPay : 80 ≤ mPayload) {mPrep : ℕ}
    (hmPrep : 200 ≤ mPrep) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rCore : QRegister (momCoreWires mPayload) n)
    (rWork : QRegister mPrep n) (hCW : rCore.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork (uPrep3_216 hmPay)
    (dPrep3_216_gen200_wstate hmPay hmPrep v rCore rWork hCW) ∧
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork (uPrep3_216 hmPay)⁻¹
    (dPrep3_216Inv_gen200_wstate hmPay hmPrep v rCore rWork hCW) := by
  let rW200 : QRegister 200 n := rWork.compose (QRegister.block 0 200 hmPrep)
  let rAct33 : QRegister 33 n := rCore.compose (s3Coarse33Core hmPay)
  obtain ⟨hrF33, hrI33⟩ :=
    dOaa33_200_wstate_realizes v rAct33 rW200 ((hCW.compose_left _).compose_right _)
  have hrF_wide : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork uOaa33
      (dOaa33_200_wstate v rAct33 rW200 ((hCW.compose_left _).compose_right _)) :=
    hrF33.widenWorkspace
  have hrI_wide : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct33 rWork uOaa33⁻¹
      (dOaa33Inv_200_wstate v rAct33 rW200 ((hCW.compose_left _).compose_right _)) :=
    hrI33.widenWorkspace
  have hF0 : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork
      (uPrep3 hmPay) (dOaa33_200_wstate v rAct33 rW200 ((hCW.compose_left _).compose_right _))
      := hrF_wide.widenActive
  have hI0 : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork
      (uPrep3 hmPay)⁻¹
      (dOaa33Inv_200_wstate v rAct33 rW200 ((hCW.compose_left _).compose_right _)) := by
    have hInv : (s3Coarse33Core hmPay).embedUnitary uOaa33⁻¹ = (uPrep3 hmPay)⁻¹ :=
      (s3Coarse33Core hmPay).embedUnitary_inv uOaa33
    rw [← hInv]
    exact hrI_wide.widenActive
  have hQF : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rCore rWork
      (uQutrit3 hmPay) (.circuit (cQutrit3CoreGen hmPay rCore)) :=
    DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
      rCore rWork _ _ (cQutrit3CoreGen_eval hmPay rCore)
  have hQI : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rCore rWork
      (uQutrit3 hmPay)⁻¹ (.circuit (cQutrit3CoreGen hmPay rCore).inverse) := by
    refine DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit rCore rWork _ _ ?_
    rw [Circuit.eval_inverse, cQutrit3CoreGen_eval hmPay rCore, QRegister.embedUnitary_inv]
  have hMul : uQutrit3 hmPay * uPrep3 hmPay = uPrep3_216 hmPay := rfl
  have hMulInv : (uPrep3 hmPay)⁻¹ * (uQutrit3 hmPay)⁻¹ = (uPrep3_216 hmPay)⁻¹ := by
    rw [← hMul, _root_.mul_inv_rev]
  refine ⟨?_, ?_⟩
  · exact hF0.seq hCW hQF
  · rw [← hMulInv]
    exact hQI.seq hCW hI0
/-- Polymorphic `mPrep`-wire (`200 ≤ mPrep`) catalyst-free Slot-3 `216`-shell `Slot3PrepCompactSpec`
at **`2,458 T` RT** (`1,229 T` one-way, `-32 T/SELECT` below `2,490 T` RT, `0` `toffoli`, `0 nHa`).
-/
noncomputable def slot3PrepGen200Spec_2458 {mPrep : ℕ} (hmPrep : 200 ≤ mPrep) :
    Slot3PrepCompactSpec mPrep 2458 where
  dPrep := fun {_} {_} v rCore rWork hCW ↦
    dPrep3_216_gen200_wstate (le_refl 80) hmPrep v rCore rWork hCW
  dPrepInv := fun {_} {_} v rCore rWork hCW ↦
    dPrep3_216Inv_gen200_wstate (le_refl 80) hmPrep v rCore rWork hCW
  hToff := fun {_} {_} v rCore rWork hCW ↦
    dPrep3_216_gen200_wstate_count_toff (le_refl 80) hmPrep v rCore rWork hCW
  hTRT := fun {_} {_} v rCore rWork hCW ↦
    dPrep3_216_gen200_wstate_count_t_rt_le (le_refl 80) hmPrep v rCore rWork hCW
  hReal := fun {_} _ _ {_} _ v rCore rWork hCW ↦
    dPrep3_216_gen200_wstate_realizes (le_refl 80) hmPrep v rCore rWork hCW
/-- Polymorphic re-capped `Slot3PrepCompactSpec mPrep tCap` for any `200 ≤ mPrep` and `2,458 ≤
  tCap`. -/
noncomputable def slot3PrepGen200SpecOfCap {mPrep tCap : ℕ} (hmPrep : 200 ≤ mPrep) (htCap : 2458 ≤
    tCap) :
    Slot3PrepCompactSpec mPrep tCap where
  dPrep := (slot3PrepGen200Spec_2458 hmPrep).dPrep
  dPrepInv := (slot3PrepGen200Spec_2458 hmPrep).dPrepInv
  hToff := (slot3PrepGen200Spec_2458 hmPrep).hToff
  hTRT := fun {_} {_} v rCore rWork hCW ↦
    le_trans ((slot3PrepGen200Spec_2458 hmPrep).hTRT v rCore rWork hCW) htCap
  hReal := (slot3PrepGen200Spec_2458 hmPrep).hReal
/-- Adaptive Slot-3 preparation round-trip `.T` cap (`2,458 T` for `200 ≤ mPrep`, `2,490 T` for
  `190 ≤ mPrep < 200`). -/
def tPrepAdaptiveRT (mPrep : ℕ) : ℕ := if 200 ≤ mPrep then 2458 else 2490
/-- Adaptive `Slot3PrepCompactSpec` across all `190 ≤ mPrep`, automatically activating `2,458 T` RT
(`-32 T/SELECT`) whenever `200 ≤ mPrep` (`mWork ≥ 199` on `Ctrl`, `mWork ≥ 196` on `Cat`). -/
noncomputable def slot3PrepAdaptiveSpec (mPrep : ℕ) (hm200 : 200 ≤ mPrep) :
    Slot3PrepCompactSpec mPrep (tPrepAdaptiveRT mPrep) :=
  slot3PrepGen200SpecOfCap hm200 (by dsimp [tPrepAdaptiveRT]; rw [ite_eq_left hm200])
end
end FastSlot3PrepAndCompact2458
end
end FastSlot3PrepAndCompact2458

noncomputable section Slot3MasterBk2490NoTopBridge

section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192
namespace Slot3MasterBk2490NoTopBridge
local instance (priority := 1000000) instNeZeroTwoPowK15 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36CoreWide
open Leaf3Slot3Norm1sWidth204 (Slot3LeafSpec uSlot3Swap3Cat36Norm1s)
open OraAndPrepBundle (castNatReg)
open Leaf3HadCutBridge (hCore80_eq uSlot3HadCutCat36Mom dConjInvTailHad3D_realizes_mom36)
open ModWrapCoarse8PureMomentum (nearestProtonCoord)
open PosSlots24MergedVepBound (cellLength_ne_zero)
open Slot3NuclearTruncBkPhysics (nuclearMBk truncBkNucCfg)
noncomputable abbrev fast414TruncBkCfg (bk : ℕ) (cfg : SpecsAux.SpecMirror.Configuration) :
    SpecsAux.SpecMirror.Configuration :=
  Slot3Fast414BkPullback94.truncBkNucCfg bk cfg
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem fast414_truncBkNucCfg_of_truncBkNucCfg (bk : ℕ) (cfg : SpecsAux.SpecMirror.Configuration) :
    fast414TruncBkCfg bk (truncBkNucCfg bk cfg) = truncBkNucCfg bk cfg := by
  have hN : (fun l w ↦ (nearestProtonCoord bk (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
      ((truncBkNucCfg bk cfg).nuclei l w) : ℝ) * (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ) / (2
      : ℝ) ^ bk)) = (truncBkNucCfg bk cfg).nuclei := by
    funext l w
    have hpow : ((1 : ℝ) / 3) = (1 / 3 : ℝ) := rfl
    have hL : SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ) ≠ 0 := by
      simpa [one_div] using cellLength_ne_zero
    have hp_ne : (2 : ℝ) ^ bk ≠ 0 := by positivity
    have hcoord : nearestProtonCoord bk (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
        ((truncBkNucCfg bk cfg).nuclei l w) = (nuclearMBk bk cfg l w : ℤ) := by
      unfold nearestProtonCoord truncBkNucCfg
      dsimp only
      rw [hpow]
      have hval : (2 : ℝ) ^ bk * ((nuclearMBk bk cfg l w : ℝ) * (SpecsAux.SpecMirror.cellVolume ^ (1
          / 3 : ℝ) / (2 ^ bk : ℝ)) / SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) + 1 / 2 =
          ((nuclearMBk bk cfg l w : ℤ) : ℝ) + 1 / 2 := by
        rw [show (2 ^ bk : ℝ) = (2 : ℝ) ^ bk by norm_num]
        field_simp [hL, hp_ne]
        push_cast
        ring
      rw [hval]
      exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    rw [hcoord]
    unfold truncBkNucCfg
    dsimp only
    rw [hpow, show (2 ^ bk : ℝ) = (2 : ℝ) ^ bk by norm_num]
    push_cast
    rfl
  cases hcfg : truncBkNucCfg bk cfg
  unfold fast414TruncBkCfg Slot3Fast414BkPullback94.truncBkNucCfg
  rw [← hcfg, hN, hcfg]
/-- `0-T` HadCut conjugation wrapper for any `truncCfg`-composed `Slot3LeafSpec 36 mWB tRaw`. -/
noncomputable def slot3HadCutLeafSpec36OfTrunc {mWB tRaw tCap : ℕ}
    (t : Norm1sTier)
    (truncCfg : SpecsAux.SpecMirror.Configuration → SpecsAux.SpecMirror.Configuration)
    (S : Slot3LeafSpec 36 mWB tRaw)
    (hu : S.uCat = fun c ↦ uSlot3Swap3Cat36Norm1s t (truncCfg c))
    (htCap : tRaw ≤ tCap) : Slot3LeafSpec 36 mWB tCap where
  uCat := fun c ↦ uSlot3HadCutCat36Mom t (truncCfg c)
  dLeaf := fun c {_Var} {_n} v rC rP rWB hCP hCW hPW ↦
    JunctionUncondHadTailCut.dConjInvTailHad3D (castNatReg hCore80_eq rC)
      (S.dLeaf c v rC rP rWB hCP hCW hPW)
  hToff := fun c {_Var} {_n} v rC rP rWB hCP hCW hPW ↦
    JunctionUncondHadTailCut.count_dConjInvTailHad3D_toff _ _ (S.hToff c v rC rP rWB hCP hCW hPW)
  hT := fun c {_Var} {_n} v rC rP rWB hCP hCW hPW ↦ by
    rw [JunctionUncondHadTailCut.count_dConjInvTailHad3D_t]
    exact le_trans (S.hT c v rC rP rWB hCP hCW hPW) htCap
  hReal := fun c {_Var} [_] [_] {_n} [_] v rC rP rWB hCP hCW hPW ↦ by
    have hIn := S.hReal c v rC rP rWB hCP hCW hPW
    rw [hu] at hIn
    exact dConjInvTailHad3D_realizes_mom36 rC rP rWB hCP hCW hPW
      (uSlot3Swap3Cat36Norm1s t (truncCfg c)) _ hIn
end
end Slot3MasterBk2490NoTopBridge
end
end Slot3MasterBk2490NoTopBridge

noncomputable section Leaf3MasterBkBundle

section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192
namespace Leaf3MasterBkBundle
local instance (priority := 1000000) instNeZeroTwoPowSCMasterBk (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux SpecsAux.SpecMirror
open Slot3Norm1s36CoreWide
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
noncomputable section
open _root_.QuantumComputation.Specs.StoppingPowerSolution (cleanRem mul_mulVec_prog writeRegProg
  writeRegProg_apply_reg)
open MeasureBranchHadamardSem (ket matrix_ext_ket RealizesCleanUnitary)
open FullSysMomSlots0135Concrete (momCoreWires)
open MomSlots35Slot3ProjNuclear (s3MomCore_ge_4034)
open PosSlots24PartnerMux288 (disj_symm)
open InterWalkRSum42Hoist (qreg_ext)
open PosMomSelectDynamic (unitaryConj_val)
open ShiftedMagS1 (realizesEmbedded_compose)
open Slot3Exact216Oracle80 (uPrep3_216)
open Slot3Prep273AndSwap3 (piSwap3Core dynCount_seq)
open StepBBlock0 (s3DisjConcatLeft)
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36Physics80 (uCore149Norm1s)
open Leaf3Slot3Norm1sWidth204 (coreWires80 Slot3PrepCompactSpec Slot3LeafSpec uSlot3Swap3Cat36Norm1s
  rCore0_36 sel143_80_36 uCore143Norm1s uSlot3Cat36Norm1s)
open OraAndPrepBundle (castNatUnitary castNatUnitary_symm_cancel)
open Leaf3HadCutBridge (hCoreCat36_eq uSlot3HadCutCat36Mom uSlot3HadCutCat36FullSys)
open Leaf3Slot3ZRet193 (StepBundleW baseDiagProjW baseDiagProjW_conjTranspose ket_baseDiagProjW
  zeroTopW zeroTopW_lt zeroTopW_ge liftTopW liftTopW_lt liftTopW_ge zeroTopW_liftTopW
  rAct149_disj_rDummy_36)
open Slot3NuclearTruncBkPhysics (truncBkNucCfg)
private theorem baseDiagProjW_pres_of_mulVec {topW n : ℕ} [NeZero (2 ^ n)] (h275 : 275 ≤ topW)
    (rCombBase : QRegister 437 n) {δ_in δ_out : BitAssignment 149 → BitAssignment 437}
    {sgn : BitAssignment 149 → ZMod 2} {U : Unitary (2 ^ n)}
    (hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α)) (hM : ∀ (β : BitAssignment n) (α :
    BitAssignment 149), zeroTopW topW (fun idx ↦ β (rCombBase idx)) = δ_in α → U.1.mulVec (ket
    β) = ((-1 : ℂ) ^ (sgn α).val) • ket (writeRegProg β rCombBase (liftTopW topW (δ_out α)
    (fun idx ↦ β (rCombBase idx))))) : baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_out α)
    * (U.1 * baseDiagProjW topW rCombBase (fun δ ↦ ∃ α, δ = δ_in α)) = U.1 * baseDiagProjW
    topW rCombBase (fun δ ↦ ∃ α, δ = δ_in α) := by
  apply matrix_ext_ket
  intro β
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_baseDiagProjW]
  by_cases hP : (∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β (rCombBase w) = 0) ∧
      ∃ α, zeroTopW topW (fun idx ↦ β (rCombBase idx)) = δ_in α
  · rw [ite_eq_left hP]
    obtain ⟨_, α, htop⟩ := hP
    rw [hM β α htop, Matrix.mulVec_smul, ket_baseDiagProjW]
    let β' := writeRegProg β rCombBase (liftTopW topW (δ_out α) (fun idx ↦ β (rCombBase idx)))
    have hβ'_reg : (fun idx ↦ β' (rCombBase idx)) = liftTopW topW (δ_out α)
        (fun idx ↦ β (rCombBase idx)) := funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
    have hscr' : ∀ w : Wire 437, 275 ≤ w.val → w.val < topW → β' (rCombBase w) = 0 :=
      fun w hw1 hw2 ↦ by
        change (fun idx ↦ β' (rCombBase idx)) w = 0
        rw [hβ'_reg, liftTopW_lt hw2]
        exact hcl_out α w hw1
    have htop' : ∃ α', zeroTopW topW (fun idx ↦ β' (rCombBase idx)) = δ_out α' :=
      ⟨α, by rw [hβ'_reg, zeroTopW_liftTopW h275 _ (hcl_out α)]⟩
    rw [ite_eq_left ⟨hscr', htop'⟩]
  · rw [ite_eq_right hP, Matrix.mulVec_zero, Matrix.mulVec_zero]
/-- Monotonicity of `StepBundleW` in `topW`: any stage bundle proved at `topW₁` automatically
holds at any wider `topW₂ ≥ topW₁` whenever `δ_in` is clean above wire `275`. -/
theorem StepBundleW.widen_topW {topW₁ topW₂ : ℕ} (hle : topW₁ ≤ topW₂) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] {v : Var}
    {rCombBase : QRegister 437 n} {δ_in δ_out : BitAssignment 149 → BitAssignment 437}
    {sgn : BitAssignment 149 → ZMod 2} {d : DynamicCircuit Var n}
    (hcl_in : ∀ α, cleanRem 437 (437 - 275) (δ_in α))
    (h1 : StepBundleW topW₁ v rCombBase δ_in δ_out sgn d) : StepBundleW topW₂ v rCombBase δ_in
    δ_out sgn d := by
  have h275_1 : 275 ≤ topW₁ := h1.h275
  have h275_2 : 275 ≤ topW₂ := le_trans h275_1 hle
  obtain ⟨U, hR1, hM1, _⟩ := h1.exists_u
  have htop1_of : ∀ (β : BitAssignment n) (α : BitAssignment 149),
      zeroTopW topW₂ (fun idx ↦ β (rCombBase idx)) = δ_in α →
      zeroTopW topW₁ (fun idx ↦ β (rCombBase idx)) = δ_in α := fun β α htop2 ↦ by
    funext w
    by_cases hw : w.val < topW₁
    · rw [zeroTopW_lt hw, ← htop2, zeroTopW_lt (lt_of_lt_of_le hw hle)]
    · rw [zeroTopW_ge (by omega), hcl_in α w (by omega)]
  have hlift_of : ∀ (β : BitAssignment n) (α : BitAssignment 149),
      zeroTopW topW₂ (fun idx ↦ β (rCombBase idx)) = δ_in α →
      liftTopW topW₁ (δ_out α) (fun idx ↦ β (rCombBase idx)) =
        liftTopW topW₂ (δ_out α) (fun idx ↦ β (rCombBase idx)) := fun β α htop2 ↦ by
    funext w
    by_cases hw1 : w.val < topW₁
    · rw [liftTopW_lt hw1, liftTopW_lt (lt_of_lt_of_le hw1 hle)]
    · by_cases hw2 : w.val < topW₂
      · rw [liftTopW_ge (by omega), liftTopW_lt hw2]
        have hz := congrFun htop2 w
        rw [zeroTopW_lt hw2] at hz
        exact (hz.trans (hcl_in α w (by omega))).trans (h1.hcl_out α w (by omega)).symm
      · rw [liftTopW_ge (by omega), liftTopW_ge (by omega)]
  have hSub : baseDiagProjW topW₁ rCombBase (fun δ ↦ ∃ α, δ = δ_in α) *
      baseDiagProjW topW₂ rCombBase (fun δ ↦ ∃ α, δ = δ_in α) =
      baseDiagProjW topW₂ rCombBase (fun δ ↦ ∃ α, δ = δ_in α) := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, ket_baseDiagProjW]
    by_cases hP : (∀ w : Wire 437, 275 ≤ w.val → w.val < topW₂ → β (rCombBase w) = 0) ∧
        ∃ α, zeroTopW topW₂ (fun idx ↦ β (rCombBase idx)) = δ_in α
    · rw [ite_eq_left hP, ket_baseDiagProjW]
      obtain ⟨hscr2, α, htop2⟩ := hP
      exact ite_eq_left ⟨fun w hw1 hw2 ↦ hscr2 w hw1 (lt_of_lt_of_le hw2 hle),
        ⟨α, htop1_of β α htop2⟩⟩
    · rw [ite_eq_right hP, Matrix.mulVec_zero]
  have hR2 : RealizesCleanUnitary v (baseDiagProjW topW₂ rCombBase (fun δ ↦ ∃ α, δ = δ_in α))
      d U := RealizesCleanUnitary.mono_proj (baseDiagProjW_conjTranspose topW₁ rCombBase _)
      (baseDiagProjW_conjTranspose topW₂ rCombBase _) hSub hR1
  have hM2 : ∀ (β : BitAssignment n) (α : BitAssignment 149), zeroTopW topW₂
      (fun idx ↦ β (rCombBase idx)) = δ_in α → U.1.mulVec (ket β) = ((-1 : ℂ) ^ (sgn α).val) •
      ket (writeRegProg β rCombBase (liftTopW topW₂ (δ_out α) (fun idx ↦ β (rCombBase idx))))
      :=
    fun β α htop2 ↦ by
      rw [hM1 β α (htop1_of β α htop2), hlift_of β α htop2]
  exact ⟨h275_2, h1.hcl_out, h1.store, ⟨U, hR2, hM2,
    baseDiagProjW_pres_of_mulVec h275_2 rCombBase h1.hcl_out hM2⟩⟩
attribute [local irreducible] uCore149Norm1s
theorem coreWires80_slice18 {mDummy : ℕ} (h : 18 + mDummy ≤ 3924) :
    18 + mDummy ≤ coreWires80 := by
  have hc : coreWires80 = momCoreWires 80 := rfl
  have hm := s3MomCore_ge_4034 (le_refl 80)
  omega
/-- Generic `mCat = 36` leaf assembler for a `truncBkNucCfg bk`-truncated `uCore149Norm1s` core. -/
noncomputable def mkSlot3Cat36LeafOfTruncCoreWithDummy {bk mPrep tPrepRT mWB mDummy tCore tCap : ℕ}
    (t : Norm1sTier)
    (hmDummy : 18 + mDummy ≤ 3924) (hmPrep : mPrep ≤ mWB) (htCap : tPrepRT + tCore ≤ tCap)
    (specPrep : Slot3PrepCompactSpec mPrep tPrepRT)
    (dCore : SpecsAux.SpecMirror.Configuration → ∀ {Var : Type} {n : ℕ},
      Var → (rAct149 : QRegister 149 n) → (rWork : QRegister mWB n) →
      (rDummy : QRegister mDummy n) →
      rAct149.DisjointWires rWork → rAct149.DisjointWires rDummy →
      rWork.DisjointWires rDummy → DynamicCircuit Var n)
    (hToff : ∀ cfg {Var : Type} {n : ℕ} (v : Var)
      (rAct149 : QRegister 149 n) (rW : QRegister mWB n) (rD : QRegister mDummy n)
      (hAW : rAct149.DisjointWires rW) (hAD : rAct149.DisjointWires rD)
      (hWD : rW.DisjointWires rD),
      (dCore cfg v rAct149 rW rD hAW hAD hWD).count PrimitiveGate.TOFF = 0)
    (hT : ∀ cfg {Var : Type} {n : ℕ} (v : Var)
      (rAct149 : QRegister 149 n) (rW : QRegister mWB n) (rD : QRegister mDummy n)
      (hAW : rAct149.DisjointWires rW) (hAD : rAct149.DisjointWires rD)
      (hWD : rW.DisjointWires rD),
      (dCore cfg v rAct149 rW rD hAW hAD hWD).count PrimitiveGate.T ≤ tCore)
    (hReal : ∀ cfg {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
      (v : Var) (rAct149 : QRegister 149 n) (rW : QRegister mWB n) (rD : QRegister mDummy n)
      (hAW : rAct149.DisjointWires rW) (hAD : rAct149.DisjointWires rD)
      (hWD : rW.DisjointWires rD),
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        rAct149 rW (uCore149Norm1s t (truncBkNucCfg bk cfg))
        (dCore cfg v rAct149 rW rD hAW hAD hWD)) :
    Slot3LeafSpec 36 mWB tCap where
  uCat := fun cfg ↦ uSlot3Swap3Cat36Norm1s t (truncBkNucCfg bk cfg)
  dLeaf := fun cfg {_} {_} v rC rP rWB hCP hCW hPW ↦
    let hSlice := coreWires80_slice18 hmDummy
    let hPrep0 := Leaf3Slot3Norm1sWidth204.Internal.zero_add_le_of_le hmPrep
    let sel36 := Leaf3Slot3Norm1sWidth204.Internal.sel149In36
    .seq
      (specPrep.dPrep v (rC.compose piSwap3Core) (rWB.slice 0 mPrep hPrep0)
        ((hCW.compose_left piSwap3Core).compose_right (QRegister.block 0 mPrep hPrep0)))
      (.seq
        (dCore cfg v
          (((rC.compose piSwap3Core).concat rP (hCP.compose_left piSwap3Core)).compose sel36)
          rWB ((rC.compose piSwap3Core).slice 18 mDummy hSlice)
          ((s3DisjConcatLeft (hCW.compose_left piSwap3Core) hPW).compose_left sel36)
          (rAct149_disj_rDummy_36 hmDummy (rC.compose piSwap3Core) rP
            (hCP.compose_left piSwap3Core))
          ((disj_symm (hCW.compose_left piSwap3Core)).compose_right
            (QRegister.block 18 mDummy hSlice)))
        (specPrep.dPrepInv v (rC.compose piSwap3Core) (rWB.slice 0 mPrep hPrep0)
          ((hCW.compose_left piSwap3Core).compose_right (QRegister.block 0 mPrep hPrep0))))
  hToff := fun cfg {_} {_} v rC rP rWB hCP hCW hPW ↦ by
    have hSlice := coreWires80_slice18 hmDummy
    let hPrep0 := Leaf3Slot3Norm1sWidth204.Internal.zero_add_le_of_le hmPrep
    let sel36 := Leaf3Slot3Norm1sWidth204.Internal.sel149In36
    obtain ⟨hTF, hTI⟩ := specPrep.hToff v (rC.compose piSwap3Core) (rWB.slice 0 mPrep hPrep0)
      ((hCW.compose_left piSwap3Core).compose_right (QRegister.block 0 mPrep hPrep0))
    have hTC := hToff cfg v (((rC.compose piSwap3Core).concat rP (hCP.compose_left
        piSwap3Core)).compose sel36) rWB ((rC.compose piSwap3Core).slice 18 mDummy hSlice)
        ((s3DisjConcatLeft (hCW.compose_left piSwap3Core) hPW).compose_left sel36)
        (rAct149_disj_rDummy_36 hmDummy (rC.compose piSwap3Core) rP (hCP.compose_left
        piSwap3Core)) ((disj_symm (hCW.compose_left piSwap3Core)).compose_right
        (QRegister.block 18 mDummy hSlice))
    dsimp only [sel36] at hTC ⊢; rw [dynCount_seq, dynCount_seq, hTF, hTC, hTI]
  hT := fun cfg {_} {_} v rC rP rWB hCP hCW hPW ↦ by
    have hSlice := coreWires80_slice18 hmDummy
    let hPrep0 := Leaf3Slot3Norm1sWidth204.Internal.zero_add_le_of_le hmPrep
    let sel36 := Leaf3Slot3Norm1sWidth204.Internal.sel149In36
    have hTP := specPrep.hTRT v (rC.compose piSwap3Core) (rWB.slice 0 mPrep hPrep0)
      ((hCW.compose_left piSwap3Core).compose_right (QRegister.block 0 mPrep hPrep0))
    have hTC := hT cfg v (((rC.compose piSwap3Core).concat rP (hCP.compose_left
        piSwap3Core)).compose sel36) rWB ((rC.compose piSwap3Core).slice 18 mDummy hSlice)
        ((s3DisjConcatLeft (hCW.compose_left piSwap3Core) hPW).compose_left sel36)
        (rAct149_disj_rDummy_36 hmDummy (rC.compose piSwap3Core) rP (hCP.compose_left
        piSwap3Core)) ((disj_symm (hCW.compose_left piSwap3Core)).compose_right
        (QRegister.block 18 mDummy hSlice))
    dsimp only [sel36] at hTC ⊢; rw [dynCount_seq, dynCount_seq]; omega
  hReal := fun cfg {Var} _ _ {_} _ v rC rP rWB hCP hCW hPW ↦ by
    let cBk := truncBkNucCfg bk cfg
    have hSlice := coreWires80_slice18 hmDummy
    let hPrep0 := Leaf3Slot3Norm1sWidth204.Internal.zero_add_le_of_le hmPrep
    let sel36 := Leaf3Slot3Norm1sWidth204.Internal.sel149In36
    let rC' : QRegister coreWires80 _ := rC.compose piSwap3Core
    let hCP' : rC'.DisjointWires rP := hCP.compose_left piSwap3Core
    let hCW' : rC'.DisjointWires rWB := hCW.compose_left piSwap3Core
    let rFull' : QRegister (coreWires80 + 36) _ := rC'.concat rP hCP'
    have hDisjCat : rFull'.DisjointWires rWB := s3DisjConcatLeft hCW' hPW
    have hCoreComp : rC' = rFull'.compose rCore0_36 := by
      apply qreg_ext; intro i
      have hc : rCore0_36 i = Fin.castAdd 36 i := Fin.ext (Nat.zero_add i.val)
      change rC' i = rFull' (rCore0_36 i)
      rw [hc, QRegister.concat_apply_left]
    obtain ⟨hPF0, hPI0⟩ := specPrep.hReal v rC' (rWB.slice 0 mPrep hPrep0)
      (hCW'.compose_right (QRegister.block 0 mPrep hPrep0))
    have hPF : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rFull' rWB
        (rCore0_36.embedUnitary (uPrep3_216 (le_refl 80))) (specPrep.dPrep v rC' (rWB.slice 0
        mPrep hPrep0) (hCW'.compose_right (QRegister.block 0 mPrep hPrep0))) :=
      (Leaf3Slot3Norm1sWidth204.Internal.realizesEmbedded_eq_left
        hCoreComp rWB hPF0.widenWorkspace).widenActive
    have hPI : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        rFull' rWB ((rCore0_36.embedUnitary (uPrep3_216 (le_refl 80)))⁻¹)
        (specPrep.dPrepInv v rC' (rWB.slice 0 mPrep hPrep0)
          (hCW'.compose_right (QRegister.block 0 mPrep hPrep0))) := by
      have ha := (Leaf3Slot3Norm1sWidth204.Internal.realizesEmbedded_eq_left
        hCoreComp rWB hPI0.widenWorkspace).widenActive
      rwa [Leaf3Slot3Norm1sWidth204.Internal.embedUnitary_inv_eq] at ha
    have hCoreCat0 := (hReal cfg v (rFull'.compose sel36) rWB (rC'.slice 18 mDummy hSlice)
        (hDisjCat.compose_left sel36) (rAct149_disj_rDummy_36 hmDummy rC' rP hCP') ((disj_symm
        hCW').compose_right (QRegister.block 18 mDummy hSlice))).widenActive
    rw [Leaf3Slot3Norm1sWidth204.Internal.sel149In36_embed_uCore149Norm1s] at hCoreCat0
    have hSeq := hPF.seq hDisjCat (hCoreCat0.seq hDisjCat hPI)
    let U_p := rCore0_36.embedUnitary (uPrep3_216 (le_refl 80))
    let U_c := sel143_80_36.embedUnitary (uCore143Norm1s t cBk)
    have hUnitEq : U_p⁻¹ * U_c * U_p = uSlot3Cat36Norm1s t cBk := by
      apply Subtype.ext
      have hInv : (U_p⁻¹).1 = U_p.1ᴴ := by simp [Matrix.star_eq_conjTranspose]
      unfold uSlot3Cat36Norm1s
      rw [unitaryConj_val, Submonoid.coe_mul, Submonoid.coe_mul, hInv, Matrix.mul_assoc]
    change DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rFull' rWB (U_p⁻¹ * U_c * U_p) _ at hSeq
    rw [hUnitEq] at hSeq
    have hSeq' := Leaf3Slot3Norm1sWidth204.Internal.realizesEmbedded_eq_left
      (Leaf3Slot3Norm1sWidth204.Internal.concat_piSwap3Core_eq_compose_piSwap3Cat36
        rC rP hCP) rWB hSeq
    have hComp := realizesEmbedded_compose (Var := Var) (rC.concat rP hCP)
      Leaf3Slot3Norm1sWidth204.Internal.piSwap3Cat36 rWB hSeq'
    dsimp only
    rwa [Leaf3Slot3Norm1sWidth204.Internal.piSwap3Cat36_embedUnitary] at hComp
attribute [local irreducible] uSlot3Swap3Cat36Norm1s
theorem castNatUnitary_uSlot3HadCutCat36Mom (t : Norm1sTier) (c : SpecsAux.SpecMirror.Configuration)
    :
    castNatUnitary hCoreCat36_eq (uSlot3HadCutCat36Mom t c) =
      uSlot3HadCutCat36FullSys t c := by
  unfold uSlot3HadCutCat36Mom
  exact castNatUnitary_symm_cancel _ _
attribute [local irreducible] uSlot3HadCutCat36Mom
end
end Leaf3MasterBkBundle
namespace CompactSkeleton
export Leaf3MasterBkBundle (StepBundleW.widen_topW mkSlot3Cat36LeafOfTruncCoreWithDummy)
end CompactSkeleton
end
end Leaf3MasterBkBundle

noncomputable section BoothOpt_05_Fast3BarrelLeaf123Shave

section
namespace BoothOpt_05_Fast3BarrelLeaf123Shave
section Part6_Fast64x4Leaf2
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 16384
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instNeZeroTwoPowBoothOptS6 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open PosSlots24PartnerMux288 hiding sandPhase18
open PosSlots24PartnerMuxZeroT123 hiding zmod2_sign_eq ite_pos ite_neg dite_pos dite_neg czCircuit
  czCircuit_count_toff czCircuit_count_t
open SelectStitch (Leaf2SpecOfTrunc)
open Leaf2PosMod4WidthCore (pos24TailMag30Aux)
open Leaf2Packed18Mux2DCore (mkLeaf2SpecOfTailMag)
open Leaf2WState57PebbledLoadOpt (orbitSandPacked12WState57PebbledBaseT
  orbitSandCat144WState57PebbledBaseT)
open Leaf2Packed13AndWState57Pass2 (orbitSandCat144Packed13WState57BaseT)
/-- Base `T`-count (excluding `260 * B`) of `dPass2Ctrl190_64x4`. -/
def pass2Ctrl190_64x4BaseT (B mWB : ℕ) : ℕ :=
  32925 + orbitSandPacked12WState57PebbledBaseT B ((mWB - 18) - 34)
/-- Base `T`-count (excluding `260 * B`) of `dPass2Cat196_64x4`. -/
def pass2CatCore_64x4BaseT (B mWB : ℕ) : ℕ :=
  32925 + min (orbitSandCat144WState57PebbledBaseT B ((mWB - 18) - 34))
              (orbitSandCat144Packed13WState57BaseT B ((mWB - 18) - 34))
/-- Exact per-`B` `Leaf2SpecOfTrunc` uniting `dPass2Ctrl190_64x4` and
  `dPass2Cat196_64x4`
for `6 ≤ B ≤ 27`. -/
noncomputable def stepLeaf2Spec64x4ExactOfB (truncFn : Configuration → Configuration)
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : Leaf2SpecOfTrunc truncFn
    (pass2Ctrl190_64x4BaseT B 190 + 260 * B) (pass2CatCore_64x4BaseT B 196 + 260 * B) :=
    mkLeaf2SpecOfTailMag truncFn (pass2Ctrl190_64x4BaseT B 190 + 260 * B)
    (pass2CatCore_64x4BaseT B 196 + 260 * B) (pos24TailMag30Aux B hB6 hB27)
end Part6_Fast64x4Leaf2
end BoothOpt_05_Fast3BarrelLeaf123Shave
end
end BoothOpt_05_Fast3BarrelLeaf123Shave

end QuantumComputation.Specs.StoppingPowerSolution
end
