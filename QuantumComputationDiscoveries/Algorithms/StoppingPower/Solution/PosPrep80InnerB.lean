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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80InnerA

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosPostPrep80InnerAmpS3_p2
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80InnerAmpS3_p2 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
section PosPostPrep80InnerAmpS3

section ModPosPostPrep80InnerAmpS3
public section
namespace PosPostPrep80InnerAmpS3
section ConfigInnerAmp
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2000000
set_option exponentiation.threshold 256
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket ket_H sqrtHalf bitSign sqrtHalf_mul_sqrtHalf star_sqrtHalf
  bit_cases eval_seq_mulVec)
open ZeroAncillaUSPS3 hiding ket
open PosSlots24SemanticBridge
open Pos24HeadCoordXor80 (bitsVal3_lt8 headCoordXorSub80Fn headCoordXorSub80Fn_of_clean
  headOutMask24 rHeadAct37In80 rOut24In67 rOut24In37 xorRegBits_apply_reg
  xorRegBits_apply_of_not_mem)
open PosPostPrep80MergedVepS3
theorem sqrtHalf_eq_one_div_sqrt_two :
    (1 / √(2 : ℝ) : ℂ) = MeasureBranchHadamardSem.sqrtHalf := by
  unfold MeasureBranchHadamardSem.sqrtHalf
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  push_cast
  rfl
theorem norm_sq_sqrtHalf_local : ‖(MeasureBranchHadamardSem.sqrtHalf : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
  apply Complex.ofReal_injective
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, ← Complex.star_def, mul_comm,
    star_sqrtHalf, sqrtHalf_mul_sqrtHalf]
  push_cast
  rfl
theorem norm_sq_good_amp_pow_eq (m cardG : ℕ) (hG : 0 < cardG) (a : ℂ) :
    let sSq : ℝ := ((cardG : ℝ) / (2 : ℝ) ^ m) * ‖a‖ ^ 2
    ‖(((3 - 4 * sSq : ℝ) : ℂ) * ((sqrtHalf : ℂ) ^ m) * a)‖ ^ 2 =
      (sSq * (3 - 4 * sSq) ^ 2) / (cardG : ℝ) := by
  intro sSq
  have hpow : ‖(sqrtHalf : ℂ) ^ m‖ ^ 2 = (1 : ℝ) / (2 : ℝ) ^ m := by
    rw [norm_pow, ← pow_right_comm, norm_sq_sqrtHalf_local, _root_.one_div_pow]
  have hrealSq (r : ℝ) : ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [norm_mul, norm_mul, mul_pow, mul_pow, hrealSq, hpow]
  dsimp only [sSq]
  have hcG : (cardG : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hG)
  have h2m : ((2 : ℝ) ^ m) ≠ 0 := pow_ne_zero m (by norm_num)
  field_simp [hcG, h2m]
theorem unH_tailReg_mem_range {k n : ℕ} (r : QRegister (k + 1) n) (β : BitAssignment n)
    (b₀ : ZMod 2) (qT : BitAssignment k) : writeReg β r (Fin.cons b₀ qT) = writeReg
    (Function.update β (r 0) b₀) (r.compose (QRegister.block 1 k (by omega))) qT := by
  let rTail : QRegister k n := r.compose (QRegister.block 1 k (by omega))
  have hTail (j : Fin k) : rTail j = r j.succ := congrArg r (Fin.ext (Nat.add_comm 1 j.val))
  funext w
  by_cases hw : ∃ i : Fin (k + 1), r i = w
  · obtain ⟨i, rfl⟩ := hw
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have hnot : r 0 ∉ Set.range rTail.wires := fun ⟨j, hj⟩ ↦
        Fin.succ_ne_zero j (r.wires.injective ((hTail j).symm.trans hj))
      rw [writeReg_apply_reg, Fin.cons_zero, writeReg_apply_of_not_mem _ _ _ _ hnot,
        Function.update_self]
    · rw [writeReg_apply_reg, Fin.cons_succ, ← hTail j, writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ hw ⟨i, hi⟩),
      writeReg_apply_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ hw ⟨j.succ, (hTail j).symm.trans hj⟩),
      Function.update_of_ne (fun h ↦ hw ⟨0, h.symm⟩)]
def normOfRaw (isMerged218 s0 : Bool) (p : BitAssignment 80) : BitAssignment 80 := if !s0 then
    (if isMerged218 then flipTailDpScratch80 (p80ClearB0Local p) else p80ClearB0Local p) else
    p
def rawFromNorm (isMerged218 s0 : Bool) (b0 : Fin 8) (q : BitAssignment 80) :
    BitAssignment 80 :=
  if !s0 then
    let q' := if isMerged218 then flipTailDpScratch80 q else q
    fun idx ↦
      if h : 3 ≤ idx.val ∧ idx.val < 6 then basisBits 3 b0 ⟨idx.val - 3, by omega⟩
      else q' idx
  else q
theorem flipTailDpScratch80_involutive (q : BitAssignment 80) :
    flipTailDpScratch80 (flipTailDpScratch80 q) = q := by
  by_cases h30 : (q 30 == 1) = true
  · have h1 : flipTailDpScratch80 q = q := itePosLocalSec4 h30
    rw [h1, h1]
  · have hq' : flipTailDpScratch80 q = fun r ↦
        if r.val == 75 then q 75 + q 0 else if r.val == 76 then q 76 + q 1
        else if r.val == 77 then q 77 + q 2 else q r := iteNegLocalSec4 h30
    have h30' : ¬((flipTailDpScratch80 q 30 == 1) = true) := by rwa [hq']
    rw [show flipTailDpScratch80 (flipTailDpScratch80 q) = _ from iteNegLocalSec4 h30']
    have hxor : ∀ x y : ZMod 2, x + y + y = x := by decide
    funext r
    rcases (by omega : r.val = 75 ∨ r.val = 76 ∨ r.val = 77 ∨
        (r.val ≠ 75 ∧ r.val ≠ 76 ∧ r.val ≠ 77)) with hr | hr | hr | ⟨n75, n76, n77⟩
    · rw [show r = 75 from Fin.ext hr, hq']
      exact hxor (q 75) (q 0)
    · rw [show r = 76 from Fin.ext hr, hq']
      exact hxor (q 76) (q 1)
    · rw [show r = 77 from Fin.ext hr, hq']
      exact hxor (q 77) (q 2)
    · simp only [hq', nat_beq_false n75, nat_beq_false n76, nat_beq_false n77,
        Bool.false_eq_true, ↓reduceIte]
theorem normOfRaw_rawFromNorm (isMerged218 s0 : Bool) (b0 : Fin 8) (q : BitAssignment 80)
    (hb0z : s0 = false → ∀ j : Fin 3, q (pos80SubIdx 3 3 (by decide) j) = 0) :
    normOfRaw isMerged218 s0 (rawFromNorm isMerged218 s0 b0 q) = q := by
  cases s0
  · simp only [normOfRaw, rawFromNorm, Bool.not_false, ↓reduceIte]
    have hclr : p80ClearB0Local
        (fun idx : Fin 80 ↦
          if h : 3 ≤ idx.val ∧ idx.val < 6 then basisBits 3 b0 ⟨idx.val - 3, by omega⟩
          else (if isMerged218 then flipTailDpScratch80 q else q) idx) =
        (if isMerged218 then flipTailDpScratch80 q else q) := by
      funext idx
      by_cases h : 3 ≤ idx.val ∧ idx.val < 6
      · dsimp only [p80ClearB0Local]
        rw [itePosLocalSec4 h]
        have hj : idx = pos80SubIdx 3 3 (by decide) ⟨idx.val - 3, by omega⟩ :=
          Fin.ext (by dsimp [pos80SubIdx]; omega)
        have hz0 : q idx = 0 := by rw [hj]; exact hb0z rfl _
        cases isMerged218
        · exact hz0.symm
        · simp only [↓reduceIte]
          dsimp only [flipTailDpScratch80]
          by_cases hq30 : (q 30 == 1) = true
          · rw [itePosLocalSec4 hq30, hz0]
          · rw [iteNegLocalSec4 hq30]
            simp only [nat_beq_false (show idx.val ≠ 75 by omega),
              nat_beq_false (show idx.val ≠ 76 by omega),
              nat_beq_false (show idx.val ≠ 77 by omega), Bool.false_eq_true, ↓reduceIte, hz0]
      · dsimp only [p80ClearB0Local]
        rw [iteNegLocalSec4 h, diteNegLocalSec4 h]
    rw [hclr]
    cases isMerged218
    · rfl
    · exact flipTailDpScratch80_involutive q
  · rfl
theorem b0Raw_rawFromNorm (isMerged218 s0 : Bool) (b0 : Fin 8) (q : BitAssignment 80)
    (hb0t : s0 = true → ∀ j : Fin 3, q (pos80SubIdx 3 3 (by decide) j) = basisBits 3 b0 j) :
    (⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
      rawFromNorm isMerged218 s0 b0 q (pos80SubIdx 3 3 (by decide) j)),
      bitsVal3_lt8 _⟩ : Fin 8) = b0 := by
  apply Fin.ext
  dsimp only
  have hfun : (fun j : Fin 3 ↦ rawFromNorm isMerged218 s0 b0 q (pos80SubIdx 3 3 (by decide) j)) =
      basisBits 3 b0 := by
    funext j
    cases s0
    · fin_cases j <;> rfl
    · exact hb0t rfl j
  rw [hfun]
  exact @bitsVal_basisBits 3 b0
theorem rawFromNorm_normOfRaw (isMerged218 s0 : Bool) (p : BitAssignment 80) : rawFromNorm
    isMerged218 s0 ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3
    (by decide) j)), bitsVal3_lt8 _⟩ (normOfRaw isMerged218 s0 p) = p := by
  cases s0
  · simp only [rawFromNorm, normOfRaw, Bool.not_false, ↓reduceIte]
    have hrest : (if isMerged218 then flipTailDpScratch80 (if isMerged218 then
        flipTailDpScratch80 (p80ClearB0Local p) else p80ClearB0Local p) else (if isMerged218
        then flipTailDpScratch80 (p80ClearB0Local p) else p80ClearB0Local p)) =
        p80ClearB0Local p := by
      cases isMerged218
      · rfl
      · exact flipTailDpScratch80_involutive (p80ClearB0Local p)
    rw [hrest]
    funext idx
    by_cases h : 3 ≤ idx.val ∧ idx.val < 6
    · rw [ditePosLocalSec4 h]
      have hbb := congrFun (basisBits_bitsVal
        (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j))) ⟨idx.val - 3, by omega⟩
      have hidx : pos80SubIdx 3 3 (by decide) ⟨idx.val - 3, by omega⟩ = idx :=
        Fin.ext (by dsimp [pos80SubIdx]; omega)
      rw [hidx] at hbb
      exact hbb
    · rw [diteNegLocalSec4 h]
      dsimp only [p80ClearB0Local]
      exact iteNegLocalSec4 h
  · rfl
theorem sum_ket_anc_of_bijection {α : Type} [Fintype α] (s0 : Bool)
    (V : BitAssignment 80 → Bool) (enc : α → BitAssignment 80) (dec : BitAssignment 80 → α)
    (A : α → ℂ) (hValid : ∀ t : α, V (enc t) = true) (hLeft : ∀ t : α, dec (enc t) = t)
    (hRight : ∀ p : BitAssignment 80, V p = true → enc (dec p) = p) :
    (∑ t : α, A t • ket (padZeroBits posPostHwa (ancBits86 s0 (enc t)))) = ∑ p : BitAssignment
    80, (if V p then A (dec p) else 0) • ket (padZeroBits posPostHwa (ancBits86 s0 p)) := by
  have hFilt : (∑ p : BitAssignment 80, (if V p then A (dec p) else 0) • ket (padZeroBits
      posPostHwa (ancBits86 s0 p))) = ∑ p ∈ Finset.univ.filter (fun p ↦ V p = true), A (dec p)
      • ket (padZeroBits posPostHwa (ancBits86 s0 p)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    cases V p <;> simp
  rw [hFilt]
  refine Finset.sum_nbij' enc dec
    (fun t _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hValid t⟩)
    (fun _ _ ↦ Finset.mem_univ _) (fun t _ ↦ hLeft t)
    (fun p hp ↦ hRight p (Finset.mem_filter.mp hp).2) (fun t _ ↦ ?_)
  rw [hLeft t]
theorem shell64_amp_zero (j : Fin (2 ^ 6)) (hj : 56 ≤ j.val) :
    sbmAmp 6 headShell64Words j = 0 := by
  apply headShell64_amp_zero j
  revert j hj
  decide
theorem writeReg_comm_disj {m₁ m₂ n : ℕ} (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n)
    (hdisj : ∀ (i : Fin m₁) (j : Fin m₂), r₁ i ≠ r₂ j)
    (β : BitAssignment n) (v₁ : BitAssignment m₁) (v₂ : BitAssignment m₂) :
    writeReg (writeReg β r₁ v₁) r₂ v₂ = writeReg (writeReg β r₂ v₂) r₁ v₁ := by
  funext w
  by_cases hw2 : w ∈ Set.range r₂.wires
  · obtain ⟨j, rfl⟩ := hw2
    have hnot1 : r₂ j ∉ Set.range r₁.wires := fun ⟨i, hi⟩ ↦ hdisj i j hi
    rw [writeReg_apply_reg, writeReg_apply_of_not_mem _ _ _ _ hnot1, writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw2]
    by_cases hw1 : w ∈ Set.range r₁.wires
    · obtain ⟨i, rfl⟩ := hw1
      rw [writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hw1, writeReg_apply_of_not_mem _ _ _ _ hw1,
        writeReg_apply_of_not_mem _ _ _ _ hw2]
theorem update_writeReg_ne {m n : ℕ} (r : QRegister m n) (u : Wire n)
    (hne : ∀ i : Fin m, r i ≠ u) (β : BitAssignment n) (v : BitAssignment m) (b : ZMod 2) :
    Function.update (writeReg β r v) u b = writeReg (Function.update β u b) r v := by
  funext w
  by_cases hw : w = u
  · have hnot : u ∉ Set.range r.wires := fun ⟨i, hi⟩ ↦ hne i hi
    rw [hw, Function.update_self, writeReg_apply_of_not_mem _ _ _ _ hnot, Function.update_self]
  · rw [Function.update_of_ne hw]
    by_cases hwr : w ∈ Set.range r.wires
    · obtain ⟨i, rfl⟩ := hwr
      rw [writeReg_apply_reg, writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hwr, writeReg_apply_of_not_mem _ _ _ _ hwr,
        Function.update_of_ne hw]
theorem ket_cLeafHeadCoordXor_eq_sub80 (β : BitAssignment 128)
    (hEn : β wEnHead_128 = β (rP80_128 30)) (hscr : ∀ j : Fin 30, β (scr30_128 j) = 0) :
    cLeafHeadCoordXor.eval.1.mulVec (ket β) = ket
    (writeReg β rP80_128 (headCoordXorSub80Fn (fun j ↦ β (rP80_128 j)))) := by
  let pPre : BitAssignment 80 := fun j ↦ β (rP80_128 j)
  let γ67 : BitAssignment 67 := fun i ↦ β (rHead67_128 i)
  have hm0 : β (rHead67_128 ⟨0, by decide⟩) = pPre 30 := hEn
  have hmK : (fun i : Fin 6 ↦ β (rHead67_128 ⟨1 + i.val, head67_add1_lt i⟩)) =
      (fun i : Fin 6 ↦ pPre ⟨63 + i.val, by omega⟩) := funext fun i ↦ by fin_cases i <;> rfl
  have hmP : (fun i : Fin 3 ↦ β (rHead67_128 ⟨7 + i.val, head67_add7_lt i⟩)) =
      (fun i : Fin 3 ↦ pPre ⟨69 + i.val, by omega⟩) := funext fun i ↦ by fin_cases i <;> rfl
  have hmS : (fun i : Fin 3 ↦ β (rHead67_128 ⟨10 + i.val, head67_add10_lt i⟩)) =
      (fun i : Fin 3 ↦ pPre ⟨72 + i.val, by omega⟩) := funext fun i ↦ by fin_cases i <;> rfl
  have hOutWire (o : Fin 24) :
      rHead67_128 (rOut24In67 o) = rP80_128 (rHeadAct37In80 (rOut24In37 o)) := by
    fin_cases o <;> rfl
  have hOutRange (o : Fin 24) : (rHeadAct37In80 (rOut24In37 o)).val < 3 ∨
      (32 ≤ (rHeadAct37In80 (rOut24In37 o)).val ∧
        (rHeadAct37In80 (rOut24In37 o)).val < 53) := by
    fin_cases o <;> decide
  have hActOut (q80 : BitAssignment 80) (outIdx : Fin 24) :
      headCoordXorSub80Fn q80 (rHeadAct37In80 (rOut24In37 outIdx)) =
        q80 (rHeadAct37In80 (rOut24In37 outIdx)) +
          headOutMask24 (q80 30) (fun i : Fin 6 ↦ q80 ⟨63 + i.val, by omega⟩)
            (fun i : Fin 3 ↦ q80 ⟨69 + i.val, by omega⟩)
            (fun i : Fin 3 ↦ q80 ⟨72 + i.val, by omega⟩) outIdx := by
    unfold headCoordXorSub80Fn
    generalize headOutMask24 (q80 30) (fun i : Fin 6 ↦ q80 ⟨63 + i.val, _⟩)
      (fun i : Fin 3 ↦ q80 ⟨69 + i.val, _⟩) (fun i : Fin 3 ↦ q80 ⟨72 + i.val, _⟩) = m24
    fin_cases outIdx <;> rfl
  have hAct3 (k : Fin 3) :
      rHeadAct37In80 (rOut24In37 ⟨21 + k.val, Nat.add_lt_add_left k.isLt 21⟩) =
        ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩ := by fin_cases k <;> rfl
  have hAct21 (k : Fin 21) :
      rHeadAct37In80 (rOut24In37 ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩) =
        ⟨32 + k.val, Nat.lt_trans (Nat.add_lt_add_left k.isLt 32) (by decide)⟩ := by
    fin_cases k <;> rfl
  have hNotOut (u : Wire 128)
      (hu : ∀ o, u ≠ rP80_128 (rHeadAct37In80 (rOut24In37 o))) :
      writeReg β rHead67_128 (head67CleanMap γ67) u = β u := by
    by_cases h67 : u ∈ Set.range rHead67_128.wires
    · obtain ⟨i, rfl⟩ := h67
      have hnOut : i ∉ rOut24In67.image := by
        rw [QRegister.mem_image]
        rintro ⟨o, rfl⟩
        exact hu o (hOutWire o)
      rw [writeReg_apply_reg, head67CleanMap, xorRegBits_apply_of_not_mem _ _ _ hnOut]
    · exact writeReg_apply_of_not_mem _ _ _ _ h67
  rw [ket_cLeafHeadCoordXor β hscr]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : w ∈ Set.range rP80_128.wires
  · obtain ⟨j, rfl⟩ := hw
    rw [writeReg_apply_reg]
    by_cases hj : j.val < 3 ∨ (32 ≤ j.val ∧ j.val < 53)
    · let o : Fin 24 :=
        if _h0 : j.val < 3 then ⟨21 + j.val, by omega⟩ else ⟨j.val - 32, by omega⟩
      have hjo : j = rHeadAct37In80 (rOut24In37 o) := by
        rcases hj with h0 | h1
        · have ho3 : o = ⟨21 + (⟨j.val, h0⟩ : Fin 3).val,
              Nat.add_lt_add_left (⟨j.val, h0⟩ : Fin 3).isLt 21⟩ := by
            dsimp only [o]
            exact ditePosLocalSec4 h0
          rw [ho3, hAct3 ⟨j.val, h0⟩]
        · have hn0 : ¬(j.val < 3) := by omega
          let k21 : Fin 21 := ⟨j.val - 32, by omega⟩
          have ho21 : o = ⟨k21.val, Nat.lt_trans k21.isLt (by decide)⟩ := by
            dsimp only [o]
            exact diteNegLocalSec4 hn0
          rw [ho21, hAct21 k21]
          exact Fin.ext (show j.val = 32 + (j.val - 32) by omega)
      rw [hjo, ← hOutWire o, writeReg_apply_reg, head67CleanMap, xorRegBits_apply_reg,
        hm0, hmK, hmP, hmS, hOutWire o]
      exact (hActOut pPre o).symm
    · simp only [headCoordXorSub80Fn, show ¬(j.val < 3) by omega,
        show ¬(32 ≤ j.val ∧ j.val < 53) by omega, ↓reduceDIte]
      exact hNotOut _ fun o h ↦ hj ((rP80_128.wires.injective h).symm ▸ hOutRange o)
  · rw [writeReg_apply_of_not_mem _ _ _ _ hw]
    exact hNotOut w fun o h ↦ hw ⟨_, h.symm⟩
theorem ket_close_flags_open (s0 : Bool) (pOut : BitAssignment 80) :
    cOpen_128.inverse.eval.1.mulVec (cFlags2_128.inverse.eval.1.mulVec (ket (flags2Map128
    (openMap128 (padZeroBits posPostHwa (ancBits86 s0 pOut)))))) = ket
    (padZeroBits posPostHwa (ancBits86 s0 pOut)) := by
  let α0 := padZeroBits posPostHwa (ancBits86 s0 pOut)
  have hz (w : Wire 128) (hw : 86 ≤ w.val) : α0 w = 0 := by
    simp [α0, padZeroBits, show ¬(w.val < 86) by omega]
  have hOpen := ket_cOpen_128 α0 (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide))
  have hne (w u : Wire 128) (v : ℕ) (hu : u.val = v) (hw : w.val ≠ v) : w ≠ u :=
    fun e ↦ hw ((congrArg Fin.val e).trans hu)
  have hzO (w : Wire 128) (hw : 119 ≤ w.val) : openMap128 α0 w = 0 := by
    simp [openMap128, hne w wEnPos_128 116 rfl (by omega),
      hne w wEnS0_128 117 rfl (by omega), hne w wEnC0_128 118 rfl (by omega), hz w (by omega)]
  have hFl := ket_cFlags2_128 (openMap128 α0) (hzO _ (by decide)) (hzO _ (by decide))
      (hzO _ (by decide)) (hzO _ (by decide)) (hzO _ (by decide))
  rw [inv_mulVec_ket_of_fwd cFlags2_128 (openMap128 α0) _ hFl,
    inv_mulVec_ket_of_fwd cOpen_128 α0 _ hOpen]
theorem headOutMask24_of_pid_ge6 (en : ZMod 2) (γK : BitAssignment 6) (γPid : BitAssignment 3)
    (γSm : BitAssignment 3) (hp : ¬(Pos24HeadCoordXor80.bitsVal γPid < 6)) (outIdx : Fin 24) :
    headOutMask24 en γK γPid γSm outIdx = 0 := by
  unfold headOutMask24
  by_cases hen : en = 0
  · simp [hen]
  · simp only [hen, ↓reduceIte, hp, ↓reduceDIte]
    split_ifs <;> simp_all [Pos24HeadCoordXor80.natBits]
theorem headCoordXorSub80Fn_of_pid_ge6 (β : BitAssignment 80)
    (hp : ¬(Pos24HeadCoordXor80.bitsVal (fun i : Fin 3 ↦ β ⟨69 + i.val, by omega⟩) < 6)) :
    headCoordXorSub80Fn β = β := by
  funext q
  unfold headCoordXorSub80Fn
  have hm : ∀ outIdx : Fin 24,
      headOutMask24 (β 30)
        (fun i : Fin 6 ↦ β ⟨63 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ β ⟨69 + i.val, by omega⟩)
        (fun i : Fin 3 ↦ β ⟨72 + i.val, by omega⟩) outIdx = 0 :=
    headOutMask24_of_pid_ge6 _ _ _ _ hp
  split_ifs
  · rw [hm]; exact add_zero _
  · rw [hm]; exact add_zero _
  · rfl
abbrev HeadTuple :=
  Fin (2 ^ 2) × Fin (2 ^ 3) × Fin (2 ^ 8) × Fin (2 ^ 3) × Fin (2 ^ 8) × Bool × Fin 56 × Fin (2 ^ 3)
abbrev TailTuple :=
  Fin (2 ^ 2) × Fin (2 ^ 8) × Fin (2 ^ 3) × Fin (2 ^ 8) × Fin (2 ^ 8) × Fin (2 ^ 3) × Fin (2 ^ 30)
def headNormQ (s0 : Bool) (t : HeadTuple) : BitAssignment 80 :=
  let (u2, sm, nuc, b0, anc, bAux, k, pid) := t
  headJointPayload80 (if s0 then b0.val else 0) nuc.val anc.val (if bAux then 1 else 0) k pid.val sm
    (u2.val % 2 == 1) ((u2.val / 2) % 2 == 1)
def tailNormQ (s0 : Bool) (t : TailTuple) : BitAssignment 80 :=
  let (u2, nuc, b0, anc, part, dp, fine) := t
  tailWitnessPayload80 (if s0 then b0.val else 0) nuc.val anc.val part.val dp fine.val
    (u2.val % 2 == 1) ((u2.val / 2) % 2 == 1)
def encHead80 (isMerged218 s0 : Bool) (t : HeadTuple) : BitAssignment 80 :=
  rawFromNorm isMerged218 s0 t.2.2.2.1 (headNormQ s0 t)
def encTail80 (isMerged218 s0 : Bool) (t : TailTuple) : BitAssignment 80 :=
  rawFromNorm isMerged218 s0 t.2.2.1 (tailNormQ s0 t)
abbrev TailSubTuple := TailTuple × Bool
def validHead80OfQ (q : BitAssignment 80) : Bool :=
  let b0Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j))
  let nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j))
  let anc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j))
  let part := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j))
  let kVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ q (pos80SubIdx 63 6 (by decide) j))
  let pidVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 69 3 (by decide) j))
  let smVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 72 3 (by decide) j))
  let remZero := (q 75 == 0) && (q 76 == 0) && (q 77 == 0) && (q 78 == 0)
  if hk : kVal < 56 then
    (q 62 == 0) && (q 30 == 1) && remZero && decide (part < 2) &&
      (q == headJointPayload80 b0Val nuc anc part ⟨kVal, hk⟩ pidVal
        ⟨smVal, bitsVal3_lt8 _⟩ (q 31 == 1) (q 79 == 1))
  else false
def decHead80OfQ (b0Raw : Fin 8) (q : BitAssignment 80) : HeadTuple :=
  let nuc : Fin (2 ^ 8) := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦
    q (pos80SubIdx 6 8 (by decide) j)),
    bitsVal_lt_two_pow_local _⟩
  let anc : Fin (2 ^ 8) := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦
    q (pos80SubIdx 14 8 (by decide) j)),
    bitsVal_lt_two_pow_local _⟩
  let part := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j))
  let kVal := Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ q (pos80SubIdx 63 6 (by decide) j))
  let pid : Fin 8 := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
    q (pos80SubIdx 69 3 (by decide) j)), bitsVal3_lt8 _⟩
  let sm : Fin 8 := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
    q (pos80SubIdx 72 3 (by decide) j)), bitsVal3_lt8 _⟩
  let u2 : Fin 4 := ⟨(if q 31 == 1 then 1 else 0) + 2 * (if q 79 == 1 then 1 else 0), by
    cases (q 31 == 1) <;> cases (q 79 == 1) <;> decide⟩
  let k : Fin 56 := if hk : kVal < 56 then ⟨kVal, hk⟩ else ⟨0, by decide⟩
  (u2, sm, nuc, b0Raw, anc, part == 1, k, pid)
def validTail80OfQ (q : BitAssignment 80) : Bool :=
  let b0Val := Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j))
  let nuc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j))
  let anc := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j))
  let part := Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j))
  let fine30 := Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦ q (pos80SubIdx 32 30 (by decide) j))
  let scratchZero := decide (∀ j : Fin 12, q (pos80SubIdx 63 12 (by decide) j) = 0) && (q 78 == 0)
  let dp : Fin 8 := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
    q (pos80SubIdx 75 3 (by decide) j)), bitsVal3_lt8 _⟩
  (q 62 == 0) && !(q 30 == 1) && scratchZero &&
    (q == tailWitnessPayload80 b0Val nuc anc part dp fine30 (q 31 == 1) (q 79 == 1))
def decTail80OfQ (b0Raw : Fin 8) (q : BitAssignment 80) : TailTuple :=
  let nuc : Fin (2 ^ 8) := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦
    q (pos80SubIdx 6 8 (by decide) j)),
    bitsVal_lt_two_pow_local _⟩
  let anc : Fin (2 ^ 8) := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦
    q (pos80SubIdx 14 8 (by decide) j)),
    bitsVal_lt_two_pow_local _⟩
  let part : Fin (2 ^ 8) := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦
    q (pos80SubIdx 22 8 (by decide) j)),
    bitsVal_lt_two_pow_local _⟩
  let fine : Fin (2 ^ 30) := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦
    q (pos80SubIdx 32 30 (by decide) j)),
    bitsVal_lt_two_pow_local _⟩
  let dp : Fin 8 := ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
    q (pos80SubIdx 75 3 (by decide) j)), bitsVal3_lt8 _⟩
  let u2 : Fin 4 := ⟨(if q 31 == 1 then 1 else 0) + 2 * (if q 79 == 1 then 1 else 0), by
    cases (q 31 == 1) <;> cases (q 79 == 1) <;> decide⟩
  (u2, nuc, b0Raw, anc, part, dp, fine)
def validHead80 (isMerged218 s0 : Bool) (p : BitAssignment 80) : Bool :=
  validHead80OfQ (normOfRaw isMerged218 s0 p)
def decHead80 (isMerged218 s0 : Bool) (p : BitAssignment 80) : HeadTuple :=
  decHead80OfQ ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j)),
    bitsVal3_lt8 _⟩ (normOfRaw isMerged218 s0 p)
def validTail80 (isMerged218 s0 : Bool) (p : BitAssignment 80) : Bool :=
  validTail80OfQ (normOfRaw isMerged218 s0 p)
def decTail80 (isMerged218 s0 : Bool) (p : BitAssignment 80) : TailTuple :=
  decTail80OfQ ⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j)),
    bitsVal3_lt8 _⟩ (normOfRaw isMerged218 s0 p)
theorem bitsVal_z2BitOfNat {m : ℕ} (v : ℕ) (hv : v < 2 ^ m) :
    Pos24HeadCoordXor80.bitsVal (fun i : Fin m ↦ z2BitOfNat v i.val) = v := by
  let j : Fin (2 ^ m) := ⟨v, hv⟩
  have hfun : (fun i : Fin m ↦ z2BitOfNat v i.val) = basisBits m j :=
    funext fun i ↦ (basisBits_eq_z2BitOfNat j i).symm
  rw [hfun]
  exact bitsVal_basisBits j
theorem fin_sum_restrict {n M : ℕ} {V : Type*} [AddCommMonoid V] [Module ℂ V] (hMN : M ≤ n)
    (a : Fin n → ℂ) (v : Fin n → V) (hzero : ∀ j : Fin n, M ≤ j.val → a j = 0) :
    (∑ j : Fin n, a j • v j) = ∑ k : Fin M, a ⟨k.val, Nat.lt_of_lt_of_le k.isLt hMN⟩ • v
    ⟨k.val, Nat.lt_of_lt_of_le k.isLt hMN⟩ := by
  let emb : Fin M ↪ Fin n :=
    ⟨fun k ↦ ⟨k.val, Nat.lt_of_lt_of_le k.isLt hMN⟩,
     fun a b h ↦ by cases a; cases b; injection h with h'; exact Fin.ext h'⟩
  symm
  refine (Finset.sum_map Finset.univ emb (fun j ↦ a j • v j)).symm.trans ?_
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_
  have hge : M ≤ j.val := by
    by_contra hlt
    exact hj (Finset.mem_map.mpr ⟨⟨j.val, Nat.lt_of_not_ge hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  rw [hzero j hge, zero_smul]
theorem normOfRaw_b0Val_eq (isMerged218 s0 : Bool) (p : BitAssignment 80) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
      normOfRaw isMerged218 s0 p (pos80SubIdx 3 3 (by decide) j)) =
      if s0 then Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
        p (pos80SubIdx 3 3 (by decide) j)) else 0 := by
  cases s0
  · simp only [normOfRaw, Bool.not_false, ↓reduceIte]
    have h0 : (fun j : Fin 3 ↦ (if isMerged218 then flipTailDpScratch80 (p80ClearB0Local p)
        else p80ClearB0Local p) (pos80SubIdx 3 3 (by decide) j)) = fun _ ↦ 0 := by
      funext j
      cases isMerged218
      · fin_cases j <;> rfl
      · unfold flipTailDpScratch80
        split_ifs <;> (fin_cases j <;> rfl)
    rw [h0]
    exact bitsVal_zero_local
  · rfl
theorem headJointPayload80_at30 (b0Val nuc anc part : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (thresh rej0 : Bool) :
    headJointPayload80 b0Val nuc anc part k pidVal sm thresh rej0 30 = 1 := by
  unfold headJointPayload80
  by_cases hp : pidVal < 6 <;> simp [hp, headWitnessPayload80]
theorem headJointPayload80_at62 (b0Val nuc anc part : ℕ) (k : Fin 56) (pidVal : ℕ) (sm : Fin 8)
    (thresh rej0 : Bool) :
    headJointPayload80 b0Val nuc anc part k pidVal sm thresh rej0 62 = 0 := by
  unfold headJointPayload80
  by_cases hp : pidVal < 6 <;> simp [hp, headWitnessPayload80]
private theorem z2_ite_beq_one : (b : Bool) → ((if b then (1 : ZMod 2) else 0) == 1) = b
  | false => rfl
  | true => rfl
private theorem u2_bits_recover : (b0 b1 : Bool) →
    (((if b0 then 1 else 0) + 2 * (if b1 then 1 else 0)) % 2 == 1) = b0 ∧
    ((((if b0 then 1 else 0) + 2 * (if b1 then 1 else 0)) / 2) % 2 == 1) = b1
  | false, false => ⟨rfl, rfl⟩
  | false, true => ⟨rfl, rfl⟩
  | true, false => ⟨rfl, rfl⟩
  | true, true => ⟨rfl, rfl⟩
private abbrev headNormQNonFineVal (s0 : Bool) (t : HeadTuple) (i : ℕ) : ZMod 2 :=
  let (u2, sm, nuc, b0, anc, bAux, k, pid) := t
  if i < 6 then z2BitOfNat (if s0 then b0.val else 0) (i - 3)
  else if i < 14 then z2BitOfNat nuc.val (i - 6)
  else if i < 22 then z2BitOfNat anc.val (i - 14)
  else if i < 30 then z2BitOfNat (if bAux then 1 else 0) (i - 22)
  else if i == 30 then 1
  else if i == 31 then (if u2.val % 2 == 1 then 1 else 0)
  else if i == 62 then 0
  else if i < 69 then z2BitOfNat k.val (i - 63)
  else if i < 72 then z2BitOfNat pid.val (i - 69)
  else if i < 75 then z2BitOfNat sm.val (i - 72)
  else if i < 79 then 0
  else (if (u2.val / 2) % 2 == 1 then 1 else 0)
private theorem headNormQ_nonFine (s0 : Bool) (t : HeadTuple) (q : Fin 80)
    (hq0 : ¬(q.val < 3)) (hq1 : ¬(32 ≤ q.val ∧ q.val < 62)) :
    headNormQ s0 t q = headNormQNonFineVal s0 t q.val := by
  rcases t with ⟨u2, sm, nuc, b0, anc, bAux, k, pid⟩
  dsimp only [headNormQ, headJointPayload80, headWitnessPayload80, headNormQNonFineVal]
  by_cases h22 : 22 ≤ q.val ∧ q.val < 30
  · simp only [show ¬(q.val < 6) by omega, show ¬(q.val < 14) by omega,
      show ¬(q.val < 22) by omega, h22.2, ↓reduceIte]
    by_cases hp : pid.val < 6
    · simp only [hp, ↓reduceDIte, h22, and_self, ↓reduceIte]
    · simp only [hp, ↓reduceDIte, hq0, show ¬(q.val < 6) by omega,
        show ¬(q.val < 14) by omega, show ¬(q.val < 22) by omega, h22.2, ↓reduceIte]
  · have hcommon (b22 b32 : ZMod 2) :
        (if q.val < 6 then z2BitOfNat (if s0 then b0.val else 0) (q.val - 3)
         else if q.val < 14 then z2BitOfNat nuc.val (q.val - 6)
         else if q.val < 22 then z2BitOfNat anc.val (q.val - 14)
         else if q.val < 30 then b22
         else if q.val == 30 then 1
         else if q.val == 31 then (if u2.val % 2 == 1 then 1 else 0)
         else if q.val < 62 then b32
         else if q.val == 62 then 0
         else if q.val < 69 then z2BitOfNat k.val (q.val - 63)
         else if q.val < 72 then z2BitOfNat pid.val (q.val - 69)
         else if q.val < 75 then z2BitOfNat sm.val (q.val - 72)
         else if q.val < 79 then 0
         else (if (u2.val / 2) % 2 == 1 then 1 else 0)) =
        headNormQNonFineVal s0 (u2, sm, nuc, b0, anc, bAux, k, pid) q.val := by
      dsimp only [headNormQNonFineVal]
      by_cases h6 : q.val < 6
      · simp only [h6, ↓reduceIte]
      · by_cases h14 : q.val < 14
        · simp only [h6, h14, ↓reduceIte]
        · by_cases h22lt : q.val < 22
          · simp only [h6, h14, h22lt, ↓reduceIte]
          · by_cases e30 : q.val = 30
            · simp [e30]
            · by_cases e31 : q.val = 31
              · simp [e31]
              · simp only [h6, h14, h22lt, show ¬(q.val < 30) by omega,
                  nat_beq_false e30, nat_beq_false e31, Bool.false_eq_true,
                  show ¬(q.val < 62) by omega, ↓reduceIte]
    by_cases hp : pid.val < 6
    · rw [ditePosLocalSec4 hp, iteNegLocalSec4 h22, iteNegLocalSec4 hq0]
      exact hcommon 0 _
    · rw [diteNegLocalSec4 hp, iteNegLocalSec4 hq0]
      exact hcommon _ 0
private theorem headNormQ_slice_bitsVal (s0 : Bool) (t : HeadTuple)
    (off m v : ℕ) (h : off + m ≤ 80) (hv : v < 2 ^ m) (hq0 : 3 ≤ off)
    (hq1 : off + m ≤ 32 ∨ 62 ≤ off)
    (hbr : ∀ j : Fin m, headNormQNonFineVal s0 t (off + j.val) = z2BitOfNat v j.val) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ headNormQ s0 t (pos80SubIdx off m h j)) = v := by
  have hpt (j : Fin m) : headNormQ s0 t (pos80SubIdx off m h j) = z2BitOfNat v j.val :=
    (headNormQ_nonFine s0 t (pos80SubIdx off m h j)
      (show ¬(off + j.val < 3) by omega)
      (show ¬(32 ≤ off + j.val ∧ off + j.val < 62) by omega)).trans (hbr j)
  rw [funext hpt]
  exact bitsVal_z2BitOfNat v hv
private theorem nat_ite_beq_one : (b : Bool) → ((if b then 1 else 0) == 1) = b
  | false => rfl
  | true => rfl
private theorem u2_val_recover : ∀ u : Fin 4,
    (if u.val % 2 == 1 then 1 else 0) + 2 * (if (u.val / 2) % 2 == 1 then 1 else 0) = u.val := by
  decide
theorem head_bijection_props (isMerged218 s0 : Bool) : (∀ t : HeadTuple, validHead80
    isMerged218 s0 (encHead80 isMerged218 s0 t) = true) ∧ (∀ t : HeadTuple, decHead80
    isMerged218 s0 (encHead80 isMerged218 s0 t) = t) ∧ (∀ p : BitAssignment 80, validHead80
    isMerged218 s0 p = true → encHead80 isMerged218 s0 (decHead80 isMerged218 s0 p) = p) := by
  have hNorm (t : HeadTuple) :
      normOfRaw isMerged218 s0 (encHead80 isMerged218 s0 t) = headNormQ s0 t :=
    normOfRaw_rawFromNorm isMerged218 s0 t.2.2.2.1 (headNormQ s0 t) fun hs0 j ↦ by
      rcases t with ⟨u2, sm, nuc, b0, anc, bAux, k, pid⟩
      rw [headNormQ_nonFine s0 _ _ (show ¬(3 + j.val < 3) by omega)
        (show ¬(32 ≤ 3 + j.val ∧ 3 + j.val < 62) by omega), hs0]
      fin_cases j <;> simp [headNormQNonFineVal, pos80SubIdx, z2BitOfNat]
  have hB0 (t : HeadTuple) :
      (⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
          encHead80 isMerged218 s0 t (pos80SubIdx 3 3 (by decide) j)),
        bitsVal3_lt8 _⟩ : Fin 8) = t.2.2.2.1 :=
    b0Raw_rawFromNorm isMerged218 s0 t.2.2.2.1 (headNormQ s0 t) fun hs0 j ↦ by
      rcases t with ⟨u2, sm, nuc, b0, anc, bAux, k, pid⟩
      rw [headNormQ_nonFine s0 _ _ (show ¬(3 + j.val < 3) by omega)
        (show ¬(32 ≤ 3 + j.val ∧ 3 + j.val < 62) by omega), hs0, basisBits_eq_z2BitOfNat b0 j]
      fin_cases j <;> rfl
  have hFields : ∀ t : HeadTuple,
      let (u2, sm, nuc, b0, anc, bAux, k, pid) := t
      let q := headNormQ s0 t
      (Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j)) =
        if s0 then b0.val else 0) ∧
      (Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j)) = nuc.val) ∧
      (Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j)) = anc.val) ∧
      (Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) =
        if bAux then 1 else 0) ∧
      (Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ q (pos80SubIdx 63 6 (by decide) j)) = k.val) ∧
      (Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 69 3 (by decide) j)) =
        pid.val) ∧
      (Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 72 3 (by decide) j)) = sm.val) ∧
      ((q 31 == 1) = (u2.val % 2 == 1)) ∧ ((q 79 == 1) = ((u2.val / 2) % 2 == 1)) := by
    rintro ⟨u2, sm, nuc, b0, anc, bAux, k, pid⟩
    refine ⟨headNormQ_slice_bitsVal s0 _ 3 3 _ _
        (match s0 with | false => Nat.zero_lt_succ 7 | true => b0.isLt) (by decide) (by decide)
        (fun j ↦ by fin_cases j <;> rfl),
      headNormQ_slice_bitsVal s0 _ 6 8 _ _ nuc.isLt (by decide) (by decide)
        (fun j ↦ by fin_cases j <;> rfl),
      headNormQ_slice_bitsVal s0 _ 14 8 _ _ anc.isLt (by decide) (by decide)
        (fun j ↦ by fin_cases j <;> rfl),
      headNormQ_slice_bitsVal s0 _ 22 8 _ _ (by cases bAux <;> decide) (by decide) (by decide)
        (fun j ↦ by fin_cases j <;> rfl),
      headNormQ_slice_bitsVal s0 _ 63 6 _ _ (Nat.lt_trans k.isLt (by decide)) (by decide)
        (by decide) (fun j ↦ by fin_cases j <;> rfl),
      headNormQ_slice_bitsVal s0 _ 69 3 _ _ pid.isLt (by decide) (by decide)
        (fun j ↦ by fin_cases j <;> rfl),
      headNormQ_slice_bitsVal s0 _ 72 3 _ _ sm.isLt (by decide) (by decide)
        (fun j ↦ by fin_cases j <;> rfl),
      by
        rw [headNormQ_nonFine s0 _ 31 (by decide) (by decide)]
        exact z2_ite_beq_one _,
      by
        rw [headNormQ_nonFine s0 _ 79 (by decide) (by decide)]
        exact z2_ite_beq_one _⟩
  refine ⟨fun ⟨u2, sm, nuc, b0, anc, bAux, k, pid⟩ ↦ ?_,
    fun ⟨u2, sm, nuc, b0, anc, bAux, k, pid⟩ ↦ ?_, fun p hV ↦ ?_⟩
  · obtain ⟨eb0, enuc, eanc, epart, ek, epid, esm, eu0, eu1⟩ :=
      hFields (u2, sm, nuc, b0, anc, bAux, k, pid)
    change validHead80OfQ
      (normOfRaw isMerged218 s0 (encHead80 isMerged218 s0 (u2, sm, nuc, b0, anc, bAux, k, pid))) =
      true
    rw [hNorm]
    dsimp only [validHead80OfQ]
    have hk' : Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ headNormQ s0 (u2, sm, nuc, b0,
        anc, bAux, k, pid) (pos80SubIdx 63 6 (by decide) j)) < 56 := ek.symm ▸ k.isLt
    have hAt := fun q h0 h1 ↦ headNormQ_nonFine s0 (u2, sm, nuc, b0, anc, bAux, k, pid) q h0 h1
    rw [ditePosLocalSec4 hk', (Fin.ext ek : (⟨_, hk'⟩ : Fin 56) = k),
      (Fin.ext esm : (⟨_, bitsVal3_lt8 _⟩ : Fin 8) = sm), eb0, enuc, eanc, epart, epid, eu0, eu1,
      hAt 62 (by decide) (by decide), hAt 30 (by decide) (by decide),
      hAt 75 (by decide) (by decide), hAt 76 (by decide) (by decide),
      hAt 77 (by decide) (by decide), hAt 78 (by decide) (by decide),
      show decide ((if bAux then 1 else 0) < 2) = true by cases bAux <;> rfl]
    simp [headNormQ, headNormQNonFineVal]
  · obtain ⟨_, enuc, eanc, epart, ek, epid, esm, eu0, eu1⟩ :=
      hFields (u2, sm, nuc, b0, anc, bAux, k, pid)
    change decHead80OfQ _
      (normOfRaw isMerged218 s0 (encHead80 isMerged218 s0 (u2, sm, nuc, b0, anc, bAux, k, pid))) = _
    rw [hB0, hNorm]
    dsimp only [decHead80OfQ]
    have hk' : Pos24HeadCoordXor80.bitsVal (fun j : Fin 6 ↦ headNormQ s0 (u2, sm, nuc, b0,
        anc, bAux, k, pid) (pos80SubIdx 63 6 (by decide) j)) < 56 := ek.symm ▸ k.isLt
    rw [ditePosLocalSec4 hk']
    refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext esm) (Prod.ext (Fin.ext enuc) (Prod.ext rfl
      (Prod.ext (Fin.ext eanc) (Prod.ext ?_ (Prod.ext (Fin.ext ek) (Fin.ext epid)))))))
    · dsimp only
      rw [eu0, eu1]
      exact u2_val_recover u2
    · rw [epart]
      exact nat_ite_beq_one bAux
  · let q := normOfRaw isMerged218 s0 p
    let b0Raw : Fin 8 := ⟨Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j)), bitsVal3_lt8 _⟩
    change validHead80OfQ q = true at hV
    dsimp only [validHead80OfQ] at hV
    split_ifs at hV with hk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hV
    obtain ⟨⟨_, hpartLt⟩, hqEq⟩ := hV
    have hpartEq : (if (Pos24HeadCoordXor80.bitsVal
        (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) == 1) then 1 else 0) =
        Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) := by
      rcases (by omega :
          Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) = 0 ∨
          Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) = 1)
        with hpv | hpv <;> simp [hpv]
    obtain ⟨hu0, hu1⟩ := u2_bits_recover (q 31 == 1) (q 79 == 1)
    have hqSame : headNormQ s0 (decHead80OfQ b0Raw q) = q := by
      dsimp only [headNormQ, decHead80OfQ]
      rw [ditePosLocalSec4 hk, (normOfRaw_b0Val_eq isMerged218 s0 p).symm, hpartEq, hu0, hu1]
      exact hqEq.symm
    change rawFromNorm isMerged218 s0 (decHead80OfQ b0Raw q).2.2.2.1
      (headNormQ s0 (decHead80OfQ b0Raw q)) = p
    rw [hqSame]
    exact rawFromNorm_normOfRaw isMerged218 s0 p
private theorem tailNormQ_slice_bitsVal (s0 : Bool) (t : TailTuple)
    (off m v : ℕ) (h : off + m ≤ 80) (hv : v < 2 ^ m)
    (hpt : ∀ j : Fin m, tailNormQ s0 t (pos80SubIdx off m h j) = z2BitOfNat v j.val) :
    Pos24HeadCoordXor80.bitsVal (fun j : Fin m ↦ tailNormQ s0 t (pos80SubIdx off m h j)) = v := by
  rw [funext hpt]
  exact bitsVal_z2BitOfNat v hv
theorem tail_bijection_props (isMerged218 s0 : Bool) : (∀ t : TailTuple, validTail80
    isMerged218 s0 (encTail80 isMerged218 s0 t) = true) ∧ (∀ t : TailTuple, decTail80
    isMerged218 s0 (encTail80 isMerged218 s0 t) = t) ∧ (∀ p : BitAssignment 80, validTail80
    isMerged218 s0 p = true → encTail80 isMerged218 s0 (decTail80 isMerged218 s0 p) = p) := by
  have hNorm (t : TailTuple) :
      normOfRaw isMerged218 s0 (encTail80 isMerged218 s0 t) = tailNormQ s0 t :=
    normOfRaw_rawFromNorm isMerged218 s0 t.2.2.1 (tailNormQ s0 t) fun hs0 j ↦ by
      subst hs0
      fin_cases j <;> simp [tailNormQ, tailWitnessPayload80, pos80SubIdx, z2BitOfNat]
  have hB0 (t : TailTuple) :
      (⟨Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦
          encTail80 isMerged218 s0 t (pos80SubIdx 3 3 (by decide) j)),
        bitsVal3_lt8 _⟩ : Fin 8) = t.2.2.1 :=
    b0Raw_rawFromNorm isMerged218 s0 t.2.2.1 (tailNormQ s0 t) fun hs0 j ↦ by
      subst hs0
      rcases t with ⟨u2, nuc, b0, anc, part, dp, fine⟩
      rw [basisBits_eq_z2BitOfNat]
      fin_cases j <;> simp [tailNormQ, tailWitnessPayload80, pos80SubIdx]
  have hFields : ∀ t : TailTuple,
      let (u2, nuc, b0, anc, part, dp, fine) := t
      let q := tailNormQ s0 t
      Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j)) =
        (if s0 then b0.val else 0) ∧
      Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j)) = nuc.val ∧
      Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j)) = anc.val ∧
      Pos24HeadCoordXor80.bitsVal (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) = part.val ∧
      Pos24HeadCoordXor80.bitsVal (fun j : Fin 30 ↦ q (pos80SubIdx 32 30 (by decide) j)) =
        fine.val ∧
      Pos24HeadCoordXor80.bitsVal (fun j : Fin 3 ↦ q (pos80SubIdx 75 3 (by decide) j)) = dp.val ∧
      (q 31 == 1) = (u2.val % 2 == 1) ∧ (q 79 == 1) = ((u2.val / 2) % 2 == 1) := by
    rintro ⟨u2, nuc, b0, anc, part, dp, fine⟩
    refine ⟨tailNormQ_slice_bitsVal s0 _ 3 3 _ _
        (match s0 with | false => Nat.zero_lt_succ 7 | true => b0.isLt)
        (fun j ↦ by fin_cases j <;> rfl),
      tailNormQ_slice_bitsVal s0 _ 6 8 _ _ nuc.isLt (fun j ↦ by fin_cases j <;> rfl),
      tailNormQ_slice_bitsVal s0 _ 14 8 _ _ anc.isLt (fun j ↦ by fin_cases j <;> rfl),
      tailNormQ_slice_bitsVal s0 _ 22 8 _ _ part.isLt (fun j ↦ by fin_cases j <;> rfl),
      tailNormQ_slice_bitsVal s0 _ 32 30 _ _ fine.isLt (fun j ↦ by
        dsimp only [tailNormQ, tailWitnessPayload80, pos80SubIdx]
        simp only [show ¬(32 + j.val < 3) by omega, show ¬(32 + j.val < 6) by omega,
          show ¬(32 + j.val < 14) by omega, show ¬(32 + j.val < 22) by omega,
          show ¬(32 + j.val < 30) by omega, nat_beq_false (show 32 + j.val ≠ 30 by omega),
          nat_beq_false (show 32 + j.val ≠ 31 by omega), Bool.false_eq_true,
          show 32 + j.val < 62 by omega, ↓reduceIte, Nat.add_sub_cancel_left]),
      tailNormQ_slice_bitsVal s0 _ 75 3 _ _ dp.isLt (fun j ↦ by fin_cases j <;> rfl),
      z2_ite_beq_one (u2.val % 2 == 1), z2_ite_beq_one ((u2.val / 2) % 2 == 1)⟩
  refine ⟨fun ⟨u2, nuc, b0, anc, part, dp, fine⟩ ↦ ?_,
    fun ⟨u2, nuc, b0, anc, part, dp, fine⟩ ↦ ?_, fun p hV ↦ ?_⟩
  · obtain ⟨eb0, enuc, eanc, epart, efine, edp, eu0, eu1⟩ :=
      hFields (u2, nuc, b0, anc, part, dp, fine)
    change validTail80OfQ
      (normOfRaw isMerged218 s0 (encTail80 isMerged218 s0 (u2, nuc, b0, anc, part, dp, fine))) =
      true
    rw [hNorm]
    dsimp only [validTail80OfQ]
    have hscr12 (j : Fin 12) :
        tailNormQ s0 (u2, nuc, b0, anc, part, dp, fine) (pos80SubIdx 63 12 (by decide) j) = 0 := by
      fin_cases j <;> rfl
    rw [decide_eq_true hscr12, (Fin.ext edp : (⟨_, bitsVal3_lt8 _⟩ : Fin 8) = dp),
      eb0, enuc, eanc, epart, efine, eu0, eu1]
    change ((0 : ZMod 2) == 0 && !((0 : ZMod 2) == 1) && (true && ((0 : ZMod 2) == 0)) &&
      (tailNormQ s0 (u2, nuc, b0, anc, part, dp, fine) ==
        tailNormQ s0 (u2, nuc, b0, anc, part, dp, fine))) = true
    rw [show ((0 : ZMod 2) == 0) = true by decide,
      show ((0 : ZMod 2) == 1) = false by decide, beq_self_eq_true]
    rfl
  · obtain ⟨_, enuc, eanc, epart, efine, edp, eu0, eu1⟩ :=
      hFields (u2, nuc, b0, anc, part, dp, fine)
    change decTail80OfQ _
      (normOfRaw isMerged218 s0 (encTail80 isMerged218 s0 (u2, nuc, b0, anc, part, dp, fine))) = _
    rw [hB0, hNorm]
    dsimp only [decTail80OfQ]
    refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext enuc) (Prod.ext rfl (Prod.ext (Fin.ext eanc)
      (Prod.ext (Fin.ext epart) (Prod.ext (Fin.ext edp) (Fin.ext efine))))))
    dsimp only
    rw [eu0, eu1]
    exact u2_val_recover u2
  · let q := normOfRaw isMerged218 s0 p
    let b0Raw : Fin 8 := ⟨Pos24HeadCoordXor80.bitsVal
      (fun j : Fin 3 ↦ p (pos80SubIdx 3 3 (by decide) j)), bitsVal3_lt8 _⟩
    change validTail80OfQ q = true at hV
    dsimp only [validTail80OfQ] at hV
    simp only [Bool.and_eq_true, beq_iff_eq] at hV
    obtain ⟨_, hqEq⟩ := hV
    obtain ⟨hu0, hu1⟩ := u2_bits_recover (q 31 == 1) (q 79 == 1)
    have hqSame : tailNormQ s0 (decTail80OfQ b0Raw q) = q := by
      dsimp only [tailNormQ, decTail80OfQ]
      rw [(normOfRaw_b0Val_eq isMerged218 s0 p).symm, hu0, hu1]
      exact hqEq.symm
    change rawFromNorm isMerged218 s0 (decTail80OfQ b0Raw q).2.2.1
      (tailNormQ s0 (decTail80OfQ b0Raw q)) = p
    rw [hqSame]
    exact rawFromNorm_normOfRaw isMerged218 s0 p
def encTailSub80 (isMerged218 s0 : Bool) (ts : TailSubTuple) : BitAssignment 80 :=
  Function.update (encTail80 isMerged218 s0 ts.1) 62 (if ts.2 then 1 else 0)
def validTailSub80 (isMerged218 s0 : Bool) (p : BitAssignment 80) : Bool :=
  validTail80 isMerged218 s0 (Function.update p 62 0)
def decTailSub80 (isMerged218 s0 : Bool) (p : BitAssignment 80) : TailSubTuple :=
  (decTail80 isMerged218 s0 (Function.update p 62 0), p 62 == 1)
theorem encTail80_at62 (isMerged218 s0 : Bool) (t : TailTuple) :
    encTail80 isMerged218 s0 t 62 = 0 := by
  rcases t with ⟨u2, nuc, b0, anc, part, dp, fine⟩
  have hNorm62 : tailNormQ s0 (u2, nuc, b0, anc, part, dp, fine) 62 = 0 := rfl
  have hNorm30 : tailNormQ s0 (u2, nuc, b0, anc, part, dp, fine) 30 = 0 := rfl
  cases s0
  · simp only [encTail80, rawFromNorm, Bool.not_false, ↓reduceIte]
    rw [diteNegLocalSec4 (by decide : ¬(3 ≤ (62 : Fin 80).val ∧ (62 : Fin 80).val < 6))]
    cases isMerged218
    · exact hNorm62
    · simp only [↓reduceIte, flipTailDpScratch80, hNorm30]
      rw [iteNegLocalSec4 (by decide : ¬(((0 : ZMod 2) == 1) = true))]
      exact hNorm62
  · exact hNorm62
theorem normOfRaw_update62 (isMerged218 s0 : Bool) (p : BitAssignment 80) (b : ZMod 2) :
    normOfRaw isMerged218 s0 (Function.update p 62 b) =
      Function.update (normOfRaw isMerged218 s0 p) 62 b := by
  cases s0
  · simp only [normOfRaw, Bool.not_false, ↓reduceIte]
    have hclr : p80ClearB0Local (Function.update p 62 b) =
        Function.update (p80ClearB0Local p) 62 b := funext fun idx ↦ by
      by_cases h62 : idx = 62
      · subst h62
        simp [p80ClearB0Local]
      · simp only [Function.update_of_ne h62, p80ClearB0Local]
    rw [hclr]
    cases isMerged218
    · rfl
    · simp only [↓reduceIte]
      set c := p80ClearB0Local p
      have h30eq : Function.update c 62 b 30 = c 30 := Function.update_of_ne (by decide) _ _
      by_cases h30 : (c 30 == 1) = true
      · dsimp only [flipTailDpScratch80]
        rw [h30eq, itePosLocalSec4 h30, itePosLocalSec4 h30]
      · funext idx
        dsimp only [flipTailDpScratch80]
        rw [h30eq, iteNegLocalSec4 h30, iteNegLocalSec4 h30]
        by_cases h62 : idx = 62
        · subst h62
          simp
        · simp only [Function.update_of_ne h62,
            Function.update_of_ne (by decide : (75 : Fin 80) ≠ 62),
            Function.update_of_ne (by decide : (0 : Fin 80) ≠ 62),
            Function.update_of_ne (by decide : (76 : Fin 80) ≠ 62),
            Function.update_of_ne (by decide : (1 : Fin 80) ≠ 62),
            Function.update_of_ne (by decide : (77 : Fin 80) ≠ 62),
            Function.update_of_ne (by decide : (2 : Fin 80) ≠ 62)]
  · rfl
theorem normOfRaw_at62 (isMerged218 s0 : Bool) (p : BitAssignment 80) :
    normOfRaw isMerged218 s0 p 62 = p 62 := by
  cases s0
  · simp only [normOfRaw, Bool.not_false, ↓reduceIte]
    have hc62 : p80ClearB0Local p 62 = p 62 := rfl
    cases isMerged218
    · exact hc62
    · simp only [↓reduceIte, flipTailDpScratch80]
      split_ifs <;> exact hc62
  · rfl
theorem tail_sub_bijection_props (isMerged218 s0 : Bool) :
    (∀ ts : TailSubTuple, validTailSub80 isMerged218 s0 (encTailSub80 isMerged218 s0 ts) = true) ∧
    (∀ ts : TailSubTuple, decTailSub80 isMerged218 s0 (encTailSub80 isMerged218 s0 ts) = ts) ∧
    (∀ p : BitAssignment 80, validTailSub80 isMerged218 s0 p = true →
      encTailSub80 isMerged218 s0 (decTailSub80 isMerged218 s0 p) = p) := by
  obtain ⟨hVT, hLT, hRT⟩ := tail_bijection_props isMerged218 s0
  have hClrEnc : ∀ ts : TailSubTuple,
      Function.update (encTailSub80 isMerged218 s0 ts) 62 0 = encTail80 isMerged218 s0 ts.1 :=
    fun ⟨t, bSub⟩ ↦ by
      dsimp only [encTailSub80]
      rw [Function.update_idem, upd_eq_self _ 62 (encTail80_at62 isMerged218 s0 t)]
  refine ⟨fun ts ↦ ?_, fun ⟨t, bSub⟩ ↦ ?_, fun p hV ↦ ?_⟩
  · dsimp only [validTailSub80]
    rw [hClrEnc ts]
    exact hVT ts.1
  · apply Prod.ext
    · dsimp only [decTailSub80]
      rw [hClrEnc (t, bSub)]
      exact hLT t
    · dsimp only [decTailSub80, encTailSub80]
      rw [Function.update_self]
      cases bSub <;> rfl
  · dsimp only [validTailSub80] at hV
    dsimp only [encTailSub80, decTailSub80]
    rw [hRT (Function.update p 62 0) hV, Function.update_idem]
    have hb : (if p 62 == 1 then (1 : ZMod 2) else 0) = p 62 := by
      rcases MeasureBranchHadamardSem.bit_cases (p 62) with h | h <;> simp [h]
    rw [hb, upd_eq_self p 62 rfl]
theorem writeReg_block_out (off len : ℕ) (h : off + len ≤ 128) (β : BitAssignment 128)
    (v : BitAssignment len) (w : Wire 128) (hw : w.val < off ∨ off + len ≤ w.val) : writeReg β
    (QRegister.block off len h) v w = β w :=
  writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ by
    have :=
      congrArg Fin.val hi; dsimp [PosPostPrep80InnerAmpS3Alt.qreg_block_apply,
      PosPostPrep80InnerAmpS3Alt.qreg_block_wires_apply,
      PosPostPrep80InnerAmpS3Alt.qreg_whole_wires, PosPostPrep80InnerAmpS3Alt.emb_trans_apply,
      PosPostPrep80InnerAmpS3Alt.emb_refl_apply,
      PosPostPrep80InnerAmpS3Alt.emb_mk_apply] at this; omega
theorem writeReg_twoUnif_out (β : BitAssignment 128) (v : BitAssignment 2) (w : Wire 128)
    (h37 : w.val ≠ 37) (h85 : w.val ≠ 85) : writeReg β rTwoUnif_128 v w = β w :=
  writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ by
    fin_cases i
    · exact h37 (congrArg Fin.val hi).symm
    · exact h85 (congrArg Fin.val hi).symm
theorem padZero_ancBits_hi (s0 : Bool) (q : BitAssignment 80) (w : Wire 128)
    (hw : 86 ≤ w.val) : padZeroBits posPostHwa (ancBits86 s0 q) w = 0 := by
  dsimp only [padZeroBits]
  exact diteNegLocalSec4 (by omega)
theorem padZero_ancBits_coin0 (s0 : Bool) (q : BitAssignment 80) :
    padZeroBits posPostHwa (ancBits86 s0 q) wCoin0_128 = if s0 then 1 else 0 := by
  dsimp only [padZeroBits, ancBits86, wCoin0_128]
  rw [ditePosLocalSec4 (by decide : 0 < 86)]
  rfl
theorem padZero_ancBits_lt6 (s0 : Bool) (q : BitAssignment 80) (w : Wire 128) (h0 : w.val ≠ 0)
    (h6 : w.val < 6) : padZeroBits posPostHwa (ancBits86 s0 q) w = 0 := by
  dsimp only [padZeroBits, ancBits86]
  rw [ditePosLocalSec4 (by omega : w.val < 86)]
  rw [nat_beq_false h0, iteNegLocalSec4 (by decide)]
  exact ditePosLocalSec4 h6
private theorem ne_wire_of_val {w u : Wire 128} (h : w.val ≠ u.val) : w ≠ u :=
  fun e ↦ h (congrArg Fin.val e)
private theorem openMap128_of_ne (δ : BitAssignment 128) (w : Wire 128)
    (hn : w.val ≠ 116 ∧ w.val ≠ 117 ∧ w.val ≠ 118) : openMap128 δ w = δ w := by
  dsimp only [openMap128]
  rw [Function.update_of_ne (ne_wire_of_val hn.2.2),
    Function.update_of_ne (ne_wire_of_val hn.2.1),
    Function.update_of_ne (ne_wire_of_val hn.1)]
private theorem flags2Map128_of_ne (δ : BitAssignment 128) (w : Wire 128)
    (hn : w.val ≠ 119 ∧ w.val ≠ 120 ∧ w.val ≠ 122 ∧ w.val ≠ 123) : flags2Map128 δ w = δ w := by
  dsimp only [flags2Map128]
  rw [Function.update_of_ne (ne_wire_of_val hn.2.2.1),
    Function.update_of_ne (ne_wire_of_val hn.2.2.2),
    Function.update_of_ne (ne_wire_of_val hn.2.1),
    Function.update_of_ne (ne_wire_of_val hn.1)]
theorem padZero_ancBits_p80 (s0 : Bool) (q : BitAssignment 80) (j : Fin 80) :
    padZeroBits posPostHwa (ancBits86 s0 q) (rP80_128 j) = q j := by
  have hjv : (rP80_128 j).val = 6 + j.val := rfl
  simp only [padZeroBits, ancBits86, hjv]
  rw [ditePosLocalSec4 (show 6 + j.val < 86 by omega),
    nat_beq_false (show 6 + j.val ≠ 0 by omega), iteNegLocalSec4 (by decide),
    diteNegLocalSec4 (show ¬(6 + j.val < 6) by omega)]
  exact congrArg q (Fin.ext (show 6 + j.val - 6 = j.val by omega))
theorem padZero_ancBits_out_eq (s0 : Bool) (q₁ q₂ : BitAssignment 80) (u : Wire 128)
    (hu : u.val < 6 ∨ 86 ≤ u.val) : padZeroBits posPostHwa (ancBits86 s0 q₁) u = padZeroBits
    posPostHwa (ancBits86 s0 q₂) u := by
  rcases hu with h6 | h86
  · by_cases h0 : u.val = 0
    · rw [show u = wCoin0_128 from Fin.ext h0, padZero_ancBits_coin0, padZero_ancBits_coin0]
    · rw [padZero_ancBits_lt6 s0 q₁ u h0 h6, padZero_ancBits_lt6 s0 q₂ u h0 h6]
  · rw [padZero_ancBits_hi s0 q₁ u h86, padZero_ancBits_hi s0 q₂ u h86]
noncomputable def βInit128 (s0 : Bool) : BitAssignment 128 :=
  openMap128 (padZeroBits posPostHwa (ancBits86 s0 (fun _ ↦ 0)))
private theorem upd_congr128 {f g : BitAssignment 128} (u w : Wire 128) (v : ZMod 2)
    (h : w ≠ u → f w = g w) : Function.update f u v w = Function.update g u v w := by
  by_cases hw : w = u
  · rw [hw, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hw, Function.update_of_ne hw, h hw]
theorem openMap128_congr (δ₁ δ₂ : BitAssignment 128) (w : Wire 128)
    (hc0 : δ₁ wCoin0_128 = δ₂ wCoin0_128) (hc1 : δ₁ wCoin1_128 = δ₂ wCoin1_128)
    (hc2 : δ₁ wCoin2_128 = δ₂ wCoin2_128)
    (hw : w ≠ wEnPos_128 → w ≠ wEnS0_128 → w ≠ wEnC0_128 → δ₁ w = δ₂ w) : openMap128 δ₁ w =
    openMap128 δ₂ w := by
  dsimp only [openMap128]
  rw [hc0, hc1, hc2]
  exact upd_congr128 _ _ _ fun h3 ↦ upd_congr128 _ _ _ fun h2 ↦
    upd_congr128 _ _ _ fun h1 ↦ hw h1 h2 h3
theorem openMap_ancBits_eq_writeReg (s0 : Bool) (q : BitAssignment 80) : openMap128
    (padZeroBits posPostHwa (ancBits86 s0 q)) = writeReg (βInit128 s0) rP80_128 q := by
  funext w
  by_cases hw : w ∈ Set.range rP80_128.wires
  · obtain ⟨j, rfl⟩ := hw
    rw [writeReg_apply_reg, openMap128_of_ne _ _
      (show 6 + j.val ≠ 116 ∧ 6 + j.val ≠ 117 ∧ 6 + j.val ≠ 118 by omega)]
    exact padZero_ancBits_p80 s0 q j
  · have hwOut : w.val < 6 ∨ 86 ≤ w.val := by
      by_contra hmid
      exact hw ⟨⟨w.val - 6, by omega⟩, Fin.ext (show 6 + (w.val - 6) = w.val by omega)⟩
    rw [writeReg_apply_of_not_mem _ _ _ _ hw]
    exact openMap128_congr _ _ w (padZero_ancBits_out_eq s0 q _ _ (Or.inl (by decide)))
      (padZero_ancBits_out_eq s0 q _ _ (Or.inl (by decide)))
      (padZero_ancBits_out_eq s0 q _ _ (Or.inl (by decide)))
      (fun _ _ _ ↦ padZero_ancBits_out_eq s0 q _ w hwOut)
noncomputable def βU2_128 (s0 : Bool) (u2 : Fin (2 ^ 2)) : BitAssignment 128 :=
  writeReg (βInit128 s0) rTwoUnif_128 (basisBits 2 u2)
noncomputable def βHead128 (s0 : Bool) (u2 : Fin (2 ^ 2)) : BitAssignment 128 :=
  flags2Map128 (Function.update (βU2_128 s0 u2) wIsHead_128 1)
noncomputable def βTail128 (s0 : Bool) (u2 : Fin (2 ^ 2)) : BitAssignment 128 :=
  flags2Map128 (βU2_128 s0 u2)
theorem flags2Map128_congr (δ₁ δ₂ : BitAssignment 128) (w : Wire 128)
    (hep : δ₁ wEnPos_128 = δ₂ wEnPos_128) (hih : δ₁ wIsHead_128 = δ₂ wIsHead_128)
    (hes : δ₁ wEnS0_128 = δ₂ wEnS0_128) (hec : δ₁ wEnC0_128 = δ₂ wEnC0_128) (hw : w ≠
    wEnHead_128 → w ≠ wEnTail_128 → w ≠ wEnS0Tail_128 → w ≠ wEnAnc_128 → δ₁ w = δ₂ w) :
    flags2Map128 δ₁ w = flags2Map128 δ₂ w := by
  dsimp only [flags2Map128]
  rw [hep, hih, hes, hec]
  exact upd_congr128 _ _ _ fun hA ↦ upd_congr128 _ _ _ fun hST ↦
    upd_congr128 _ _ _ fun hT ↦ upd_congr128 _ _ _ fun hH ↦ hw hH hT hST hA
theorem βInit128_coins (s0 : Bool) :
    padZeroBits posPostHwa (ancBits86 s0 (fun _ ↦ 0)) wCoin0_128 = (if s0 then 1 else 0) ∧
    padZeroBits posPostHwa (ancBits86 s0 (fun _ ↦ 0)) wCoin1_128 = 0 ∧
    padZeroBits posPostHwa (ancBits86 s0 (fun _ ↦ 0)) wCoin2_128 = 0 :=
  ⟨padZero_ancBits_coin0 s0 _, padZero_ancBits_lt6 s0 _ wCoin1_128 (by decide) (by decide),
   padZero_ancBits_lt6 s0 _ wCoin2_128 (by decide) (by decide)⟩
theorem βInit128_enPos (s0 : Bool) : βInit128 s0 wEnPos_128 = 1 := by
  obtain ⟨_, hc1, hc2⟩ := βInit128_coins s0
  dsimp only [βInit128, openMap128]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self, hc1, hc2]
  decide
theorem βInit128_enS0 (s0 : Bool) : βInit128 s0 wEnS0_128 = if s0 then 1 else 0 := by
  obtain ⟨hc0, hc1, hc2⟩ := βInit128_coins s0
  dsimp only [βInit128, openMap128]
  rw [Function.update_of_ne (by decide), Function.update_self, hc0, hc1, hc2]
  cases s0 <;> decide
theorem βInit128_enC0 (s0 : Bool) : βInit128 s0 wEnC0_128 = if s0 then 0 else 1 := by
  obtain ⟨hc0, hc1, hc2⟩ := βInit128_coins s0
  dsimp only [βInit128, openMap128]
  rw [Function.update_self, hc0, hc1, hc2]
  cases s0 <;> decide
theorem βInit128_eq_zero_of_mid (s0 : Bool) (w : Wire 128) (h1 : 6 ≤ w.val ∧ w.val < 116) :
    βInit128 s0 w = 0 := by
  rw [βInit128, openMap128_of_ne _ w (by omega)]
  by_cases h86 : w.val < 86
  · rw [show w = rP80_128 ⟨w.val - 6, by omega⟩ from
        Fin.ext (show w.val = 6 + (w.val - 6) by omega),
      padZero_ancBits_p80]
  · exact padZero_ancBits_hi s0 _ w (by omega)
theorem βInit128_hi_zero (s0 : Bool) (w : Wire 128) (hw : 119 ≤ w.val) : βInit128 s0 w = 0 := by
  rw [βInit128, openMap128_of_ne _ w (by omega)]
  exact padZero_ancBits_hi s0 _ w (by omega)
theorem βU2_inputs (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βU2_128 s0 u2 wEnPos_128 = 1 ∧
    βU2_128 s0 u2 wEnS0_128 = (if s0 then 1 else 0) ∧
    βU2_128 s0 u2 wEnC0_128 = (if s0 then 0 else 1) ∧
    βU2_128 s0 u2 wIsHead_128 = 0 :=
  ⟨(writeReg_twoUnif_out _ _ _ (by decide) (by decide)).trans (βInit128_enPos s0),
   (writeReg_twoUnif_out _ _ _ (by decide) (by decide)).trans (βInit128_enS0 s0),
   (writeReg_twoUnif_out _ _ _ (by decide) (by decide)).trans (βInit128_enC0 s0),
   (writeReg_twoUnif_out _ _ _ (by decide) (by decide)).trans
     (βInit128_eq_zero_of_mid s0 _ (by decide))⟩
theorem βHead128_enHead (s0 : Bool) (u2 : Fin (2 ^ 2)) : βHead128 s0 u2 wEnHead_128 = 1 := by
  dsimp only [βHead128, flags2Map128]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self, Function.update_of_ne (by decide),
    Function.update_self, (βU2_inputs s0 u2).1]
  decide
theorem βHead128_enTail (s0 : Bool) (u2 : Fin (2 ^ 2)) : βHead128 s0 u2 wEnTail_128 = 0 := by
  dsimp only [βHead128, flags2Map128]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self,
    Function.update_of_ne (by decide), Function.update_self, (βU2_inputs s0 u2).1]
  decide
theorem βHead128_enS0Tail (s0 : Bool) (u2 : Fin (2 ^ 2)) : βHead128 s0 u2 wEnS0Tail_128 = 0 := by
  obtain ⟨hep, hes, _, _⟩ := βU2_inputs s0 u2
  dsimp only [βHead128, flags2Map128]
  rw [Function.update_of_ne (by decide), Function.update_self, Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self, hep, hes]
  cases s0 <;> decide
theorem βHead128_enAnc (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βHead128 s0 u2 wEnAnc_128 = if s0 then 1 else 0 := by
  obtain ⟨hep, _, hec, _⟩ := βU2_inputs s0 u2
  dsimp only [βHead128, flags2Map128]
  rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self, hep, hec]
  cases s0 <;> decide
private theorem βHead128_of_ne_flags (s0 : Bool) (u2 : Fin (2 ^ 2)) (w : Wire 128)
    (hn : w.val ≠ 119 ∧ w.val ≠ 120 ∧ w.val ≠ 122 ∧ w.val ≠ 123 ∧ w.val ≠ 36) :
    βHead128 s0 u2 w = βU2_128 s0 u2 w := by
  rw [βHead128, flags2Map128_of_ne _ w ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩,
    Function.update_of_ne (ne_wire_of_val hn.2.2.2.2)]
theorem βHead128_enS0 (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βHead128 s0 u2 wEnS0_128 = if s0 then 1 else 0 :=
  (βHead128_of_ne_flags s0 u2 _ (by decide)).trans (βU2_inputs s0 u2).2.1
theorem βHead128_enC0 (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βHead128 s0 u2 wEnC0_128 = if s0 then 0 else 1 :=
  (βHead128_of_ne_flags s0 u2 _ (by decide)).trans (βU2_inputs s0 u2).2.2.1
theorem βHead128_isHead (s0 : Bool) (u2 : Fin (2 ^ 2)) : βHead128 s0 u2 wIsHead_128 = 1 := by
  rw [βHead128, flags2Map128_of_ne _ _ (by decide), Function.update_self]
theorem βHead128_u2_0 (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βHead128 s0 u2 (rP80_128 ⟨31, by decide⟩) = basisBits 2 u2 0 := by
  rw [βHead128_of_ne_flags s0 u2 _ (by decide), βU2_128,
    show rP80_128 ⟨31, by decide⟩ = rTwoUnif_128 0 from Fin.ext rfl, writeReg_apply_reg]
theorem βHead128_u2_1 (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βHead128 s0 u2 (rP80_128 ⟨79, by decide⟩) = basisBits 2 u2 1 := by
  rw [βHead128_of_ne_flags s0 u2 _ (by decide), βU2_128,
    show rP80_128 ⟨79, by decide⟩ = rTwoUnif_128 1 from Fin.ext rfl, writeReg_apply_reg]
theorem βHead128_mid_zero (s0 : Bool) (u2 : Fin (2 ^ 2)) (w : Wire 128)
    (h1 : 6 ≤ w.val ∧ w.val < 116) (h36 : w.val ≠ 36) (h37 : w.val ≠ 37) (h85 : w.val ≠ 85) :
    βHead128 s0 u2 w = 0 := by
  rw [βHead128_of_ne_flags s0 u2 w (by omega), βU2_128, writeReg_twoUnif_out _ _ w h37 h85]
  exact βInit128_eq_zero_of_mid s0 w h1
theorem βHead128_hi_zero (s0 : Bool) (u2 : Fin (2 ^ 2)) (w : Wire 128)
    (hw : 124 ≤ w.val ∨ w.val = 121) : βHead128 s0 u2 w = 0 := by
  rw [βHead128_of_ne_flags s0 u2 w (by omega), βU2_128,
    writeReg_twoUnif_out _ _ w (by omega) (by omega)]
  exact βInit128_hi_zero s0 w (by omega)
theorem βTail128_enHead (s0 : Bool) (u2 : Fin (2 ^ 2)) : βTail128 s0 u2 wEnHead_128 = 0 := by
  obtain ⟨hep, _, _, hih⟩ := βU2_inputs s0 u2
  dsimp only [βTail128, flags2Map128]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide), Function.update_self, hep, hih]
  decide
theorem βTail128_enTail (s0 : Bool) (u2 : Fin (2 ^ 2)) : βTail128 s0 u2 wEnTail_128 = 1 := by
  obtain ⟨hep, _, _, hih⟩ := βU2_inputs s0 u2
  dsimp only [βTail128, flags2Map128]
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_self, hep, hih]
  decide
theorem βTail128_enS0Tail (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βTail128 s0 u2 wEnS0Tail_128 = if s0 then 1 else 0 := by
  obtain ⟨hep, hes, _, hih⟩ := βU2_inputs s0 u2
  dsimp only [βTail128, flags2Map128]
  rw [Function.update_of_ne (by decide), Function.update_self, hep, hes, hih]
  cases s0 <;> decide
theorem βTail128_enAnc (s0 : Bool) (u2 : Fin (2 ^ 2)) : βTail128 s0 u2 wEnAnc_128 = 1 := by
  obtain ⟨hep, _, hec, hih⟩ := βU2_inputs s0 u2
  dsimp only [βTail128, flags2Map128]
  rw [Function.update_self, hep, hec, hih]
  cases s0 <;> decide
theorem βTail128_enS0 (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βTail128 s0 u2 wEnS0_128 = if s0 then 1 else 0 :=
  (flags2Map128_of_ne _ _ (by decide)).trans (βU2_inputs s0 u2).2.1
theorem βTail128_enC0 (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βTail128 s0 u2 wEnC0_128 = if s0 then 0 else 1 :=
  (flags2Map128_of_ne _ _ (by decide)).trans (βU2_inputs s0 u2).2.2.1
theorem βTail128_u2_0 (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βTail128 s0 u2 (rP80_128 ⟨31, by decide⟩) = basisBits 2 u2 0 := by
  rw [βTail128, flags2Map128_of_ne _ _ (by decide), βU2_128,
    show rP80_128 ⟨31, by decide⟩ = rTwoUnif_128 0 from Fin.ext rfl, writeReg_apply_reg]
theorem βTail128_u2_1 (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βTail128 s0 u2 (rP80_128 ⟨79, by decide⟩) = basisBits 2 u2 1 := by
  rw [βTail128, flags2Map128_of_ne _ _ (by decide), βU2_128,
    show rP80_128 ⟨79, by decide⟩ = rTwoUnif_128 1 from Fin.ext rfl, writeReg_apply_reg]
theorem βTail128_mid_zero (s0 : Bool) (u2 : Fin (2 ^ 2)) (w : Wire 128)
    (h1 : 6 ≤ w.val ∧ w.val < 116) (h37 : w.val ≠ 37) (h85 : w.val ≠ 85) :
    βTail128 s0 u2 w = 0 := by
  rw [βTail128, flags2Map128_of_ne _ w (by omega), βU2_128, writeReg_twoUnif_out _ _ w h37 h85]
  exact βInit128_eq_zero_of_mid s0 w h1
theorem βTail128_hi_zero (s0 : Bool) (u2 : Fin (2 ^ 2)) (w : Wire 128)
    (hw : 124 ≤ w.val ∨ w.val = 121) : βTail128 s0 u2 w = 0 := by
  rw [βTail128, flags2Map128_of_ne _ w (by omega), βU2_128,
    writeReg_twoUnif_out _ _ w (by omega) (by omega)]
  exact βInit128_hi_zero s0 w (by omega)
theorem finishXorMap128_of_ne (isMerged218 : Bool) (β : BitAssignment 128) (w : Wire 128)
    (h75 : w ≠ wP80_128 ⟨75, by decide⟩) (h76 : w ≠ wP80_128 ⟨76, by decide⟩)
    (h77 : w ≠ wP80_128 ⟨77, by decide⟩) (hb0 : w ≠ rB1_128 ⟨0, by decide⟩)
    (hb1 : w ≠ rB1_128 ⟨1, by decide⟩) (hb2 : w ≠ rB1_128 ⟨2, by decide⟩) :
    finishXorMap128 isMerged218 β w = β w := by
  dsimp only [finishXorMap128]
  rw [Function.update_of_ne hb2, Function.update_of_ne hb1, Function.update_of_ne hb0,
    Function.update_of_ne h77, Function.update_of_ne h76, Function.update_of_ne h75]
theorem rawFromNorm_of_not_b0 (isMerged218 s0 : Bool) (b0 : Fin 8) (q : BitAssignment 80)
    (idx : Fin 80) (h : ¬(3 ≤ idx.val ∧ idx.val < 6)) : rawFromNorm isMerged218 s0 b0 q idx =
    if !s0 then (if isMerged218 then flipTailDpScratch80 q else q) idx else q idx := by
  cases s0
  · dsimp only [rawFromNorm, Bool.not_false, ↓reduceIte]
    exact diteNegLocalSec4 h
  · rfl
theorem openMap_ancBits_eq_βInit_of_out (s0 : Bool) (q : BitAssignment 80) (u : Wire 128)
    (hu : u.val < 6 ∨ 86 ≤ u.val) :
    openMap128 (padZeroBits posPostHwa (ancBits86 s0 q)) u = βInit128 s0 u :=
  openMap128_congr _ _ u (padZero_ancBits_out_eq s0 q _ _ (Or.inl (by decide)))
    (padZero_ancBits_out_eq s0 q _ _ (Or.inl (by decide)))
    (padZero_ancBits_out_eq s0 q _ _ (Or.inl (by decide)))
    (fun _ _ _ ↦ padZero_ancBits_out_eq s0 q _ u hu)
private theorem flags2_eq_open_of_out (s0 : Bool) (δ : BitAssignment 128) (pOut : BitAssignment 80)
    (hep : δ wEnPos_128 = 1) (hes : δ wEnS0_128 = if s0 then 1 else 0)
    (hec : δ wEnC0_128 = if s0 then 0 else 1) (hih : δ wIsHead_128 = pOut ⟨30, by decide⟩)
    (w : Wire 128) (hwOut : w.val < 6 ∨ 86 ≤ w.val) (hw : δ w = βInit128 s0 w) :
    flags2Map128 δ w =
      flags2Map128 (openMap128 (padZeroBits posPostHwa (ancBits86 s0 pOut))) w :=
  flags2Map128_congr _ _ w
    (by rw [hep, openMap_ancBits_eq_βInit_of_out s0 pOut wEnPos_128 (Or.inr (by decide)),
          βInit128_enPos])
    (by rw [hih, openMap_ancBits_eq_writeReg s0 pOut,
          show wIsHead_128 = rP80_128 ⟨30, by decide⟩ from Fin.ext rfl, writeReg_apply_reg])
    (by rw [hes, openMap_ancBits_eq_βInit_of_out s0 pOut wEnS0_128 (Or.inr (by decide)),
          βInit128_enS0])
    (by rw [hec, openMap_ancBits_eq_βInit_of_out s0 pOut wEnC0_128 (Or.inr (by decide)),
          βInit128_enC0])
    (fun _ _ _ _ ↦ hw.trans (openMap_ancBits_eq_βInit_of_out s0 pOut w hwOut).symm)
theorem βHead128_eq_flags2_open_of_out (s0 : Bool) (u2 : Fin (2 ^ 2))
    (pOut : BitAssignment 80) (hp30 : pOut ⟨30, by decide⟩ = 1) (w : Wire 128)
    (hwOut : w.val < 6 ∨ 86 ≤ w.val) :
    βHead128 s0 u2 w =
      flags2Map128 (openMap128 (padZeroBits posPostHwa (ancBits86 s0 pOut))) w := by
  obtain ⟨hep, hes, hec, _⟩ := βU2_inputs s0 u2
  exact flags2_eq_open_of_out s0 _ pOut
    (by rw [Function.update_of_ne (by decide), hep])
    (by rw [Function.update_of_ne (by decide), hes])
    (by rw [Function.update_of_ne (by decide), hec])
    (by rw [Function.update_self, hp30]) w hwOut
    (by rw [Function.update_of_ne (ne_wire_of_val (show w.val ≠ 36 by omega)),
          βU2_128, writeReg_twoUnif_out _ _ w (by omega) (by omega)])
theorem βTail128_eq_flags2_open_of_out (s0 : Bool) (u2 : Fin (2 ^ 2))
    (pOut : BitAssignment 80) (hp30 : pOut ⟨30, by decide⟩ = 0) (w : Wire 128)
    (hwOut : w.val < 6 ∨ 86 ≤ w.val) :
    βTail128 s0 u2 w =
      flags2Map128 (openMap128 (padZeroBits posPostHwa (ancBits86 s0 pOut))) w := by
  obtain ⟨hep, hes, hec, hih⟩ := βU2_inputs s0 u2
  exact flags2_eq_open_of_out s0 _ pOut hep hes hec (hih.trans hp30.symm) w hwOut
    (writeReg_twoUnif_out _ _ w (by omega) (by omega))
theorem βHead128_enPos (s0 : Bool) (u2 : Fin (2 ^ 2)) : βHead128 s0 u2 wEnPos_128 = 1 :=
  (βHead128_of_ne_flags s0 u2 _ (by decide)).trans (βU2_inputs s0 u2).1
theorem βTail128_enPos (s0 : Bool) (u2 : Fin (2 ^ 2)) : βTail128 s0 u2 wEnPos_128 = 1 :=
  (flags2Map128_of_ne _ _ (by decide)).trans (βU2_inputs s0 u2).1
theorem βTail128_isHead (s0 : Bool) (u2 : Fin (2 ^ 2)) : βTail128 s0 u2 wIsHead_128 = 0 :=
  (flags2Map128_of_ne _ _ (by decide)).trans (βU2_inputs s0 u2).2.2.2
private theorem βU2_coin_eq (s0 : Bool) (u2 : Fin (2 ^ 2)) (w : Wire 128) (hw : w.val < 6) :
    βU2_128 s0 u2 w = padZeroBits posPostHwa (ancBits86 s0 (fun _ ↦ 0)) w := by
  rw [βU2_128, writeReg_twoUnif_out _ _ w (by omega) (by omega),
    βInit128, openMap128_of_ne _ w (by omega)]
theorem βHead128_coins (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βHead128 s0 u2 wCoin0_128 = (if s0 then 1 else 0) ∧
    βHead128 s0 u2 wCoin1_128 = 0 ∧ βHead128 s0 u2 wCoin2_128 = 0 := by
  obtain ⟨hc0, hc1, hc2⟩ := βInit128_coins s0
  exact ⟨(βHead128_of_ne_flags s0 u2 _ (by decide)).trans
      ((βU2_coin_eq s0 u2 _ (by decide)).trans hc0),
    (βHead128_of_ne_flags s0 u2 _ (by decide)).trans ((βU2_coin_eq s0 u2 _ (by decide)).trans hc1),
    (βHead128_of_ne_flags s0 u2 _ (by decide)).trans ((βU2_coin_eq s0 u2 _ (by decide)).trans hc2)⟩
theorem βTail128_coins (s0 : Bool) (u2 : Fin (2 ^ 2)) :
    βTail128 s0 u2 wCoin0_128 = (if s0 then 1 else 0) ∧
    βTail128 s0 u2 wCoin1_128 = 0 ∧ βTail128 s0 u2 wCoin2_128 = 0 := by
  obtain ⟨hc0, hc1, hc2⟩ := βInit128_coins s0
  exact ⟨(flags2Map128_of_ne _ _ (by decide)).trans ((βU2_coin_eq s0 u2 _ (by decide)).trans hc0),
    (flags2Map128_of_ne _ _ (by decide)).trans ((βU2_coin_eq s0 u2 _ (by decide)).trans hc1),
    (flags2Map128_of_ne _ _ (by decide)).trans ((βU2_coin_eq s0 u2 _ (by decide)).trans hc2)⟩
theorem flagsInv_βHead128 (s0 : Bool) (u2 : Fin (2 ^ 2)) : FlagsInv128 (βHead128 s0 u2) := by
  obtain ⟨hc0, hc1, hc2⟩ := βHead128_coins s0 u2
  have hh (w : Wire 128) (hw : 124 ≤ w.val ∨ w.val = 121) := βHead128_hi_zero s0 u2 w hw
  refine ⟨by simp [βHead128_enPos, hc1, hc2],
    by cases s0 <;> simp [βHead128_enS0, βHead128_enPos, hc0],
    by cases s0 <;> simp [βHead128_enC0, βHead128_enPos, βHead128_enS0],
    by simp [βHead128_enHead, βHead128_enPos, βHead128_isHead],
    by simp [βHead128_enTail, βHead128_enPos, βHead128_enHead],
    by cases s0 <;> simp [βHead128_enS0Tail, βHead128_enS0, βHead128_enTail],
    by cases s0 <;> simp [βHead128_enAnc, βHead128_enPos, βHead128_enC0, βHead128_isHead],
    fun j ↦ βHead128_mid_zero s0 u2 _ (show 6 ≤ 86 + j.val ∧ 86 + j.val < 116 by omega)
      (show 86 + j.val ≠ 36 by omega) (show 86 + j.val ≠ 37 by omega)
      (show 86 + j.val ≠ 85 by omega),
    hh _ (Or.inr rfl), hh _ (Or.inl (by decide)), hh _ (Or.inl (by decide)),
    hh _ (Or.inl (by decide)), hh _ (Or.inl (by decide))⟩
theorem flagsInv_βTail128 (s0 : Bool) (u2 : Fin (2 ^ 2)) : FlagsInv128 (βTail128 s0 u2) := by
  obtain ⟨hc0, hc1, hc2⟩ := βTail128_coins s0 u2
  have hh (w : Wire 128) (hw : 124 ≤ w.val ∨ w.val = 121) := βTail128_hi_zero s0 u2 w hw
  refine ⟨by simp [βTail128_enPos, hc1, hc2],
    by cases s0 <;> simp [βTail128_enS0, βTail128_enPos, hc0],
    by cases s0 <;> simp [βTail128_enC0, βTail128_enPos, βTail128_enS0],
    by simp [βTail128_enHead, βTail128_enPos, βTail128_isHead],
    by simp [βTail128_enTail, βTail128_enPos, βTail128_enHead],
    by cases s0 <;> simp [βTail128_enS0Tail, βTail128_enS0, βTail128_enTail],
    by cases s0 <;> simp [βTail128_enAnc, βTail128_enPos, βTail128_enC0, βTail128_isHead],
    fun j ↦ βTail128_mid_zero s0 u2 _ (show 6 ≤ 86 + j.val ∧ 86 + j.val < 116 by omega)
      (show 86 + j.val ≠ 37 by omega) (show 86 + j.val ≠ 85 by omega),
    hh _ (Or.inr rfl), hh _ (Or.inl (by decide)), hh _ (Or.inl (by decide)),
    hh _ (Or.inl (by decide)), hh _ (Or.inl (by decide))⟩
theorem flagsInv_writeReg_payload {m : ℕ} (r : QRegister m 128)
    (hr : ∀ i : Fin m, 6 ≤ (r i).val ∧ (r i).val < 86 ∧ (r i).val ≠ 36)
    (β : BitAssignment 128) (v : BitAssignment m) (hβ : FlagsInv128 β) :
    FlagsInv128 (writeReg β r v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hs, h8, h9, h10, h11, h12⟩ := hβ
  have hout (w : Wire 128) (hw : w.val < 6 ∨ 86 ≤ w.val ∨ w.val = 36) : writeReg β r v w = β w :=
    writeReg_apply_of_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ by
      have hri := hr i
      have hv := congrArg Fin.val hi
      omega
  have hi86 (w : Wire 128) (h : 86 ≤ w.val) : writeReg β r v w = β w := hout w (Or.inr (Or.inl h))
  have hlo6 (w : Wire 128) (h : w.val < 6) : writeReg β r v w = β w := hout w (Or.inl h)
  have h36 : writeReg β r v wIsHead_128 = β wIsHead_128 := hout _ (Or.inr (Or.inr rfl))
  refine ⟨by rw [hi86 _ (by decide), hlo6 _ (by decide), hlo6 _ (by decide), h1],
    by rw [hi86 _ (by decide), hi86 _ (by decide), hlo6 _ (by decide), h2],
    by rw [hi86 _ (by decide), hi86 _ (by decide), hi86 _ (by decide), h3],
    by rw [hi86 _ (by decide), hi86 _ (by decide), h36, h4],
    by rw [hi86 _ (by decide), hi86 _ (by decide), hi86 _ (by decide), h5],
    by rw [hi86 _ (by decide), hi86 _ (by decide), hi86 _ (by decide), h6],
    by rw [hi86 _ (by decide), hi86 _ (by decide), hi86 _ (by decide), h36, h7],
    fun j ↦ (hi86 (scr30_128 j) (show 86 ≤ 86 + j.val by omega)).trans (hs j),
    (hi86 _ (by decide)).trans h8, (hi86 _ (by decide)).trans h9,
    (hi86 _ (by decide)).trans h10, (hi86 _ (by decide)).trans h11,
    (hi86 _ (by decide)).trans h12⟩
private theorem block_payload_not36 (off len : ℕ) (h : off + len ≤ 128)
    (hok : 6 ≤ off ∧ off + len ≤ 86 ∧ (36 < off ∨ off + len ≤ 36)) (i : Fin len) :
    6 ≤ (QRegister.block off len h i).val ∧
      (QRegister.block off len h i).val < 86 ∧ (QRegister.block off len h i).val ≠ 36 := by
  have hv : (QRegister.block off len h i).val = off + i.val := rfl
  omega
private theorem rP80_128_out_block {off len : ℕ} {h : off + len ≤ 128}
    {β : BitAssignment 128} {v : BitAssignment len} (j : Fin 80)
    (hout : 6 + j.val < off ∨ off + len ≤ 6 + j.val) :
    writeReg β (QRegister.block off len h) v (rP80_128 j) = β (rP80_128 j) :=
  writeReg_block_out off len h β v (rP80_128 j) hout
private theorem rP80_128_in_block {off len : ℕ} {h : off + len ≤ 128}
    {β : BitAssignment 128} {v : BitAssignment len} (j : Fin 80)
    (hlo : off ≤ 6 + j.val) (hhi : 6 + j.val < off + len) :
    writeReg β (QRegister.block off len h) v (rP80_128 j) = v ⟨6 + j.val - off, by omega⟩ := by
  have heq : rP80_128 j = QRegister.block off len h ⟨6 + j.val - off, by omega⟩ :=
    Fin.ext (show 6 + j.val = off + (6 + j.val - off) by omega)
  rw [heq, writeReg_apply_reg]
private theorem flags2_open_ancBits_p80 (s0 : Bool) (pOut : BitAssignment 80) (j : Fin 80) :
    flags2Map128 (openMap128 (padZeroBits posPostHwa (ancBits86 s0 pOut))) (rP80_128 j) = pOut j :=
      by
  rw [flags2Map128_of_ne _ _ (show 6 + j.val ≠ 119 ∧ 6 + j.val ≠ 120 ∧ 6 + j.val ≠ 122 ∧ 6 +
    j.val ≠ 123 by omega),
    openMap128_of_ne _ _ (show 6 + j.val ≠ 116 ∧ 6 + j.val ≠ 117 ∧ 6 + j.val ≠ 118 by omega)]
  exact padZero_ancBits_p80 s0 pOut j
theorem evolve_head_finish_close (isMerged218 s0 : Bool) (t : HeadTuple) :
    let (u2, sm, nuc, b0, anc, bAux, k, pid) := t
    let k64 : Fin (2 ^ 6) := ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩
    let part8 : Fin (2 ^ 8) := if bAux then ⟨1, by decide⟩ else ⟨0, by decide⟩
    let γH := writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (βHead128
        s0 u2) rSm_128 (basisBits 3 sm)) rNuc_128 (basisBits 8 nuc)) rB0_128 (basisBits 3 b0))
        rAnc_128 (basisBits 8 anc)) rPart_128 (basisBits 8 part8)) rK_128 (basisBits 6 k64))
        rPid_128 (basisBits 3 pid)
    (cJointTailBhmt_128 wJointTailFast19 false ;;ᶜ cLeafHeadCoordXor ;;ᶜ
        cFinishXorToff_128 isMerged218 ;;ᶜ cFlags2_128.inverse ;;ᶜ cOpen_128.inverse).eval.1.mulVec
        (ket γH) =
      ket (padZeroBits posPostHwa (ancBits86 s0 (encHead80 isMerged218 s0 t))) := by
  rcases t with ⟨u2, sm, nuc, b0, anc, bAux, k, pid⟩
  dsimp only
  let k64 : Fin (2 ^ 6) := ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩
  let part8 : Fin (2 ^ 8) := if bAux then ⟨1, by decide⟩ else ⟨0, by decide⟩
  have hpart8Val : part8.val = if bAux then 1 else 0 := by cases bAux <;> rfl
  let γH := writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (βHead128 s0
      u2) rSm_128 (basisBits 3 sm)) rNuc_128 (basisBits 8 nuc)) rB0_128 (basisBits 3 b0))
      rAnc_128 (basisBits 8 anc)) rPart_128 (basisBits 8 part8)) rK_128 (basisBits 6 k64))
      rPid_128 (basisBits 3 pid)
  have hOutγ (w : Wire 128) (hw : w.val < 9 ∨ (36 ≤ w.val ∧ w.val < 69) ∨ 81 ≤ w.val) :
      γH w = βHead128 s0 u2 w := by
    dsimp only [γH, rPid_128, rK_128, rPart_128, rAnc_128, rB0_128, rNuc_128, rSm_128]
    iterate 7 rw [writeReg_block_out _ _ _ _ _ _ (by omega)]
  have hScrγ (j : Fin 30) : γH (scr30_128 j) = 0 :=
    (hOutγ _ (Or.inr (Or.inr (show 81 ≤ 86 + j.val by omega)))).trans
      (βHead128_mid_zero s0 u2 _ (show 6 ≤ 86 + j.val ∧ 86 + j.val < 116 by omega)
        (show 86 + j.val ≠ 36 by omega) (show 86 + j.val ≠ 37 by omega)
        (show 86 + j.val ≠ 85 by omega))
  have hTail0 : γH wEnTail_128 = 0 :=
    (hOutγ _ (Or.inr (Or.inr (by decide)))).trans (βHead128_enTail s0 u2)
  have hHead1 : γH wEnHead_128 = 1 :=
    (hOutγ _ (Or.inr (Or.inr (by decide)))).trans (βHead128_enHead s0 u2)
  have hp30 : γH (rP80_128 30) = 1 := by
    rw [show rP80_128 30 = wIsHead_128 from Fin.ext rfl, hOutγ _ (Or.inr (Or.inl (by decide)))]
    exact βHead128_isHead s0 u2
  have hFl {m} (r : QRegister m 128) (hr : ∀ i, 6 ≤ (r i).val ∧ (r i).val < 86 ∧ (r i).val ≠ 36)
      {β v} (h : FlagsInv128 β) := flagsInv_writeReg_payload r hr β v h
  have hFlagsγ : FlagsInv128 γH :=
    hFl rPid_128 (block_payload_not36 75 3 _ (by decide))
      (hFl rK_128 (block_payload_not36 69 6 _ (by decide))
        (hFl rPart_128 (block_payload_not36 28 8 _ (by decide))
          (hFl rAnc_128 (block_payload_not36 20 8 _ (by decide))
            (hFl rB0_128 (block_payload_not36 9 3 _ (by decide))
              (hFl rNuc_128 (block_payload_not36 12 8 _ (by decide))
                (hFl rSm_128 (block_payload_not36 78 3 _ (by decide))
                  (flagsInv_βHead128 s0 u2)))))))
  iterate 4 rw [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [cJointTailBhmt_mulVec_ket_enZero wJointTailFast19 false γH hFlagsγ hTail0,
    ket_cLeafHeadCoordXor_eq_sub80 γH (hHead1.trans hp30.symm) hScrγ]
  let pPre : BitAssignment 80 := fun j ↦ γH (rP80_128 j)
  let γX := writeReg γH rP80_128 (headCoordXorSub80Fn pPre)
  rw [ket_cFinishXorToff_128 isMerged218 γX]
  have hStateEq : finishXorMap128 isMerged218 γX =
      flags2Map128 (openMap128 (padZeroBits posPostHwa
        (ancBits86 s0 (encHead80 isMerged218 s0 (u2, sm, nuc, b0, anc, bAux, k, pid))))) := by
    have hkPre : (fun i : Fin 6 ↦ pPre ⟨63 + i.val, by omega⟩) = basisBits 6 k64 :=
      funext fun i ↦ by
        let j0 : Fin 80 := ⟨63 + i.val, by omega⟩
        have hj0 : j0.val = 63 + i.val := rfl
        dsimp only [pPre, γH, rPid_128, rK_128]
        rw [rP80_128_out_block j0 (by omega), rP80_128_in_block j0 (by omega) (by omega)]
        exact congrArg (basisBits 6 k64) (Fin.ext (show 6 + j0.val - 69 = i.val by omega))
    have hpPre : (fun i : Fin 3 ↦ pPre ⟨69 + i.val, by omega⟩) = basisBits 3 pid :=
      funext fun i ↦ by
        let j0 : Fin 80 := ⟨69 + i.val, by omega⟩
        have hj0 : j0.val = 69 + i.val := rfl
        dsimp only [pPre, γH, rPid_128]
        rw [rP80_128_in_block j0 (by omega) (by omega)]
        exact congrArg (basisBits 3 pid) (Fin.ext (show 6 + j0.val - 75 = i.val by omega))
    have hsPre : (fun i : Fin 3 ↦ pPre ⟨72 + i.val, by omega⟩) = basisBits 3 sm := funext fun i ↦ by
      let j0 : Fin 80 := ⟨72 + i.val, by omega⟩
      have hj0 : j0.val = 72 + i.val := rfl
      dsimp only [pPre, γH, rPid_128, rK_128, rPart_128, rAnc_128, rB0_128, rNuc_128, rSm_128]
      iterate 6 rw [rP80_128_out_block j0 (by omega)]
      rw [rP80_128_in_block j0 (by omega) (by omega)]
      exact congrArg (basisBits 3 sm) (Fin.ext (show 6 + j0.val - 78 = i.val by omega))
    have hkLt : Pos24HeadCoordXor80.bitsVal (fun i : Fin 6 ↦ pPre ⟨63 + i.val, by omega⟩) < 56 := by
      rw [hkPre, bitsVal_basisBits]
      exact k.isLt
    have hpVal : Pos24HeadCoordXor80.bitsVal (fun i : Fin 3 ↦ pPre ⟨69 + i.val, by omega⟩) =
        pid.val := by rw [hpPre, bitsVal_basisBits]
    have hkEq : (⟨Pos24HeadCoordXor80.bitsVal (fun i : Fin 6 ↦ pPre ⟨63 + i.val, by omega⟩),
        hkLt⟩ : Fin 56) = k := Fin.ext (by
      dsimp only
      rw [hkPre, bitsVal_basisBits])
    have hsEq : (⟨Pos24HeadCoordXor80.bitsVal (fun i : Fin 3 ↦ pPre ⟨72 + i.val, by omega⟩),
        bitsVal3_lt8 _⟩ : Fin 8) = sm := Fin.ext (by
      dsimp only
      rw [hsPre, bitsVal_basisBits])
    have hPreZero (q : Fin 80) (hq : q.val < 3 ∨ (32 ≤ q.val ∧ q.val < 62)) : pPre q = 0 :=
      (hOutγ _ (hq.elim (fun _ ↦ Or.inl (show 6 + q.val < 9 by omega))
          (fun _ ↦ Or.inr (Or.inl (show 36 ≤ 6 + q.val ∧ 6 + q.val < 69 by omega))))).trans
        (βHead128_mid_zero s0 u2 _ (show 6 ≤ 6 + q.val ∧ 6 + q.val < 116 by omega)
          (show 6 + q.val ≠ 36 by omega) (show 6 + q.val ≠ 37 by omega)
          (show 6 + q.val ≠ 85 by omega))
    have hb1Pre (ax : Fin 3) : pPre ⟨ax.val, by omega⟩ = 0 := hPreZero _ (Or.inl ax.isLt)
    have hfinePre (j : Fin 30) : pPre ⟨32 + j.val, by omega⟩ = 0 :=
      hPreZero _ (Or.inr ⟨show 32 ≤ 32 + j.val by omega, show 32 + j.val < 62 by omega⟩)
    have hRestFn (q : Fin 80) (hq0 : ¬(q.val < 3)) (hq1 : ¬(32 ≤ q.val ∧ q.val < 62)) :
        headCoordXorSub80Fn pPre q = pPre q := by
      by_cases hp : pid.val < 6
      · exact (headCoordXorSub80Fn_of_clean pPre hp30 hkLt (hpVal.symm ▸ hp)
          hb1Pre hfinePre).2.2 q hq0 hq1
      · rw [headCoordXorSub80Fn_of_pid_ge6 pPre (hpVal.symm ▸ hp)]
    let pOut := encHead80 isMerged218 s0 (u2, sm, nuc, b0, anc, bAux, k, pid)
    have hOutEnc (idx : Fin 80) (hidx : ¬(3 ≤ idx.val ∧ idx.val < 6)) :
        encHead80 isMerged218 s0 (u2, sm, nuc, b0, anc, bAux, k, pid) idx =
          headNormQ s0 (u2, sm, nuc, b0, anc, bAux, k, pid) idx := by
      dsimp only [encHead80]
      rw [rawFromNorm_of_not_b0 isMerged218 s0 b0 _ idx hidx]
      have h30q : headNormQ s0 (u2, sm, nuc, b0, anc, bAux, k, pid) 30 = 1 :=
        headJointPayload80_at30 _ _ _ _ _ _ _ _ _
      cases s0
      · cases isMerged218
        · rfl
        · simp [flipTailDpScratch80, h30q]
      · rfl
    funext w
    by_cases hwP : w ∈ Set.range rP80_128.wires
    · obtain ⟨j, rfl⟩ := hwP
      rw [flags2_open_ancBits_p80]
      have hEnT0 : γX wEnTail_128 = 0 := (writeReg_block_out _ _ _ _ _ _ (by decide)).trans hTail0
      have hEnST0 : γX wEnS0Tail_128 = 0 :=
        (writeReg_block_out _ _ _ _ _ _ (by decide)).trans
          ((hOutγ _ (Or.inr (Or.inr (by decide)))).trans (βHead128_enS0Tail s0 u2))
      have hEnS0 : γX wEnS0_128 = (if s0 then 1 else 0) :=
        (writeReg_block_out _ _ _ _ _ _ (by decide)).trans
          ((hOutγ _ (Or.inr (Or.inr (by decide)))).trans (βHead128_enS0 s0 u2))
      have hcDp0 : (if isMerged218 then γX wEnS0Tail_128 else γX wEnTail_128) = 0 := by
        cases isMerged218
        · exact hEnT0
        · exact hEnST0
      have hγXB0 (i : Fin 3) : γX (rB0_128 i) = basisBits 3 b0 i := by
        let j0 : Fin 80 := ⟨3 + i.val, by omega⟩
        have hj0 : j0.val = 3 + i.val := rfl
        have heqB : rB0_128 i = rP80_128 j0 := Fin.ext (show 9 + i.val = 6 + (3 + i.val) by omega)
        dsimp only [γX]
        rw [heqB, writeReg_apply_reg, hRestFn j0 (by omega) (by omega)]
        dsimp only [pPre, γH, rPid_128, rK_128, rPart_128, rAnc_128]
        iterate 4 rw [rP80_128_out_block j0 (by omega)]
        rw [← heqB, writeReg_apply_reg]
      by_cases hj3 : j.val < 3
      · let ax : Fin 3 := ⟨j.val, hj3⟩
        have hγXAx (i : Fin 3) : γX (rB1_128 i) = headCoordXorSub80Fn pPre ⟨i.val, by omega⟩ := by
          rw [show rB1_128 i = rP80_128 ⟨i.val, by omega⟩ from Fin.ext rfl]
          exact writeReg_apply_reg _ _ _ _
        have hLHS0 (ax0 : Fin 3) : finishXorMap128 isMerged218 γX (rB1_128 ax0) =
            headCoordXorSub80Fn pPre ⟨ax0.val, by omega⟩ +
              (if s0 then 1 else 0) * basisBits 3 b0 ax0 := by
          dsimp only [finishXorMap128]
          rw [hcDp0, hEnS0, hγXB0 ⟨0, by decide⟩, hγXB0 ⟨1, by decide⟩, hγXB0 ⟨2, by decide⟩,
            hγXAx ⟨0, by decide⟩, hγXAx ⟨1, by decide⟩, hγXAx ⟨2, by decide⟩]
          fin_cases ax0
          · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
              Function.update_self]
          · rw [Function.update_of_ne (by decide), Function.update_self]
          · rw [Function.update_self]
        rw [show rP80_128 j = rB1_128 ax from Fin.ext rfl, hLHS0 ax, hOutEnc j (by omega)]
        by_cases hp : pid.val < 6
        · have hpLt : Pos24HeadCoordXor80.bitsVal (fun i : Fin 3 ↦ pPre ⟨69 + i.val, by omega⟩) <
              6 := hpVal.symm ▸ hp
          obtain ⟨hAx, _, _⟩ := headCoordXorSub80Fn_of_clean pPre hp30 hkLt hpLt hb1Pre hfinePre
          have hpEq : (⟨Pos24HeadCoordXor80.bitsVal (fun i : Fin 3 ↦ pPre ⟨69 + i.val, by omega⟩),
              hpLt⟩ : Fin 6) = ⟨pid.val, hp⟩ := Fin.ext hpVal
          rw [hkEq, hpEq, hsEq] at hAx
          rw [hAx ax]
          let dH := pos24OhPoint (pos24HeadU56 k) (pos24HeadV56 k) (pos24HeadW56 k) ⟨pid.val, hp⟩ sm
          let dpH : Fin 8 := ⟨(dH 0).val % 2 + 2 * ((dH 1).val % 2) + 4 * ((dH 2).val % 2),
            by omega⟩
          change (if ((dpH.val / 2 ^ ax.val) % 2) = 1 then (1 : ZMod 2) else 0) + _ = _
          have hdpBit : (if ((dpH.val / 2 ^ ax.val) % 2) = 1 then (1 : ZMod 2) else 0) =
              basisBits 3 dpH ax := by
            rw [basisBits_eq_z2BitOfNat]
            simp [z2BitOfNat]
          rw [hdpBit]
          dsimp only [headNormQ, headJointPayload80]
          rw [ditePosLocalSec4 hp, iteNegLocalSec4 (show ¬(22 ≤ j.val ∧ j.val < 30) by omega)]
          dsimp only [headWitnessPayload80]
          rw [itePosLocalSec4 hj3]
          cases s0
          · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
            change basisBits 3 dpH ax = z2BitOfNat (Nat.xor 0 dpH.val) ax.val
            rw [show Nat.xor 0 dpH.val = dpH.val from Nat.zero_xor dpH.val,
              basisBits_eq_z2BitOfNat dpH ax]
          · simp only [↓reduceIte, one_mul]
            change basisBits 3 dpH ax + basisBits 3 b0 ax =
              z2BitOfNat (Nat.xor b0.val dpH.val) ax.val
            rw [z2BitOfNat_xor3 b0 dpH ax, add_comm]
        · rw [headCoordXorSub80Fn_of_pid_ge6 pPre (hpVal.symm ▸ hp), hb1Pre ax, zero_add]
          dsimp only [headNormQ, headJointPayload80]
          rw [diteNegLocalSec4 hp, itePosLocalSec4 hj3]
          cases s0
          · simp [z2BitOfNat]
          · simp only [↓reduceIte, one_mul]
            exact basisBits_eq_z2BitOfNat b0 ax
      · have hUpdSelf (f : BitAssignment 128) (u : Wire 128) : Function.update f u (f u) = f :=
          upd_eq_self f u rfl
        have hLHS : finishXorMap128 isMerged218 γX (rP80_128 j) = headCoordXorSub80Fn pPre j := by
          dsimp only [finishXorMap128]
          rw [hcDp0]
          simp only [zero_mul, add_zero]
          rw [Function.update_of_ne (ne_wire_of_val (show 6 + j.val ≠ 8 by omega)),
            Function.update_of_ne (ne_wire_of_val (show 6 + j.val ≠ 7 by omega)),
            Function.update_of_ne (ne_wire_of_val (show 6 + j.val ≠ 6 by omega)),
            hUpdSelf, hUpdSelf, hUpdSelf]
          exact writeReg_apply_reg γH rP80_128 (headCoordXorSub80Fn pPre) j
        rw [hLHS]
        by_cases hjFine : 32 ≤ j.val ∧ j.val < 62
        · rw [hOutEnc j (by omega)]
          let jf : Fin 30 := ⟨j.val - 32, by omega⟩
          have hjf : j = ⟨32 + jf.val, by omega⟩ :=
            Fin.ext (show j.val = 32 + (j.val - 32) by omega)
          by_cases hp : pid.val < 6
          · have hpLt : Pos24HeadCoordXor80.bitsVal (fun i : Fin 3 ↦ pPre ⟨69 + i.val, by omega⟩) <
                6 := hpVal.symm ▸ hp
            obtain ⟨_, hFine, _⟩ := headCoordXorSub80Fn_of_clean pPre hp30 hkLt hpLt hb1Pre hfinePre
            have hpEq : (⟨Pos24HeadCoordXor80.bitsVal (fun i : Fin 3 ↦ pPre ⟨69 + i.val, by omega⟩),
                hpLt⟩ : Fin 6) = ⟨pid.val, hp⟩ := Fin.ext hpVal
            rw [hkEq, hpEq, hsEq] at hFine
            rw [hjf, hFine jf]
            dsimp only [headNormQ, headJointPayload80]
            rw [ditePosLocalSec4 hp,
              iteNegLocalSec4 (show ¬(22 ≤ 32 + jf.val ∧ 32 + jf.val < 30) by omega)]
            dsimp only [headWitnessPayload80]
            simp only [show ¬(32 + jf.val < 3) by omega, show ¬(32 + jf.val < 6) by omega,
              show ¬(32 + jf.val < 14) by omega, show ¬(32 + jf.val < 22) by omega,
              show ¬(32 + jf.val < 30) by omega, nat_beq_false (show 32 + jf.val ≠ 30 by omega),
              nat_beq_false (show 32 + jf.val ≠ 31 by omega), Bool.false_eq_true,
              show 32 + jf.val < 62 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
            unfold z2BitOfNat
            simp only [beq_iff_eq]
            rfl
          · rw [headCoordXorSub80Fn_of_pid_ge6 pPre (hpVal.symm ▸ hp), hjf, hfinePre jf]
            dsimp only [headNormQ, headJointPayload80]
            rw [diteNegLocalSec4 hp]
            simp [show ¬(32 + jf.val < 3) by omega, show ¬(32 + jf.val < 6) by omega,
              show ¬(32 + jf.val < 14) by omega, show ¬(32 + jf.val < 22) by omega,
              show ¬(32 + jf.val < 30) by omega, nat_beq_false (show 32 + jf.val ≠ 30 by omega),
              nat_beq_false (show 32 + jf.val ≠ 31 by omega), show 32 + jf.val < 62 by omega]
        · rw [hRestFn j hj3 hjFine]
          by_cases hj6 : j.val < 6
          · let jb : Fin 3 := ⟨j.val - 3, by omega⟩
            dsimp only [pPre, γH, rPid_128, rK_128, rPart_128, rAnc_128, rB0_128]
            iterate 4 rw [rP80_128_out_block j (by omega)]
            rw [rP80_128_in_block j (by omega) (by omega),
              show (⟨6 + j.val - 9, _⟩ : Fin 3) = jb from
                Fin.ext (show 6 + j.val - 9 = j.val - 3 by omega)]
            cases s0
            · dsimp only [pOut, encHead80, rawFromNorm]
              simp only [Bool.not_false, ↓reduceIte]
              rw [ditePosLocalSec4 (⟨by omega, hj6⟩ : 3 ≤ j.val ∧ j.val < 6)]
            · change basisBits 3 b0 jb = headNormQ true (u2, sm, nuc, b0, anc, bAux, k, pid) j
              rw [headNormQ_nonFine true _ j hj3 hjFine]
              dsimp only [headNormQNonFineVal]
              rw [itePosLocalSec4 hj6]
              exact basisBits_eq_z2BitOfNat b0 jb
          · rw [hOutEnc j (by omega), headNormQ_nonFine s0 _ j hj3 hjFine]
            dsimp only [headNormQNonFineVal]
            rw [iteNegLocalSec4 hj6]
            by_cases hj14 : j.val < 14
            · dsimp only [pPre, γH, rPid_128, rK_128, rPart_128, rAnc_128, rB0_128, rNuc_128]
              iterate 5 rw [rP80_128_out_block j (by omega)]
              rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat,
                itePosLocalSec4 hj14]
              exact congrArg (z2BitOfNat nuc.val) (show 6 + j.val - 12 = j.val - 6 by omega)
            · rw [iteNegLocalSec4 hj14]
              by_cases hj22 : j.val < 22
              · dsimp only [pPre, γH, rPid_128, rK_128, rPart_128, rAnc_128]
                iterate 3 rw [rP80_128_out_block j (by omega)]
                rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat,
                  itePosLocalSec4 hj22]
                exact congrArg (z2BitOfNat anc.val) (show 6 + j.val - 20 = j.val - 14 by omega)
              · rw [iteNegLocalSec4 hj22]
                by_cases hj30 : j.val < 30
                · dsimp only [pPre, γH, rPid_128, rK_128, rPart_128]
                  iterate 2 rw [rP80_128_out_block j (by omega)]
                  rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat,
                    hpart8Val, itePosLocalSec4 hj30]
                  exact congrArg (z2BitOfNat _) (show 6 + j.val - 28 = j.val - 22 by omega)
                · rw [iteNegLocalSec4 hj30]
                  by_cases hj63 : j.val < 63
                  · rcases (by omega : j.val = 30 ∨ j.val = 31 ∨ j.val = 62) with hjv | hjv | hjv
                    · rw [show j = ⟨30, by decide⟩ from Fin.ext hjv]
                      exact hp30
                    · rw [show j = ⟨31, by decide⟩ from Fin.ext hjv]
                      dsimp only [pPre]
                      rw [hOutγ _ (Or.inr (Or.inl (by decide))), βHead128_u2_0,
                        basisBits_eq_div_mod]
                      fin_cases u2 <;> rfl
                    · rw [show j = ⟨62, by decide⟩ from Fin.ext hjv]
                      exact (hOutγ _ (Or.inr (Or.inl (by decide)))).trans
                        (βHead128_mid_zero s0 u2 _ (by decide) (by decide) (by decide) (by decide))
                  · simp only [nat_beq_false (show j.val ≠ 30 by omega),
                      nat_beq_false (show j.val ≠ 31 by omega),
                      nat_beq_false (show j.val ≠ 62 by omega), Bool.false_eq_true, ↓reduceIte]
                    by_cases hj69 : j.val < 69
                    · dsimp only [pPre, γH, rPid_128, rK_128]
                      rw [rP80_128_out_block j (by omega),
                        rP80_128_in_block j (by omega) (by omega),
                        basisBits_eq_z2BitOfNat, itePosLocalSec4 hj69]
                      exact congrArg (z2BitOfNat k.val) (show 6 + j.val - 69 = j.val - 63 by omega)
                    · rw [iteNegLocalSec4 hj69]
                      by_cases hj72 : j.val < 72
                      · dsimp only [pPre, γH, rPid_128]
                        rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat,
                          itePosLocalSec4 hj72]
                        exact congrArg (z2BitOfNat pid.val)
                          (show 6 + j.val - 75 = j.val - 69 by omega)
                      · rw [iteNegLocalSec4 hj72]
                        by_cases hj75 : j.val < 75
                        · dsimp only [pPre, γH, rPid_128, rK_128, rPart_128, rAnc_128, rB0_128,
                            rNuc_128, rSm_128]
                          iterate 6 rw [rP80_128_out_block j (by omega)]
                          rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat,
                            itePosLocalSec4 hj75]
                          exact congrArg (z2BitOfNat sm.val)
                            (show 6 + j.val - 78 = j.val - 72 by omega)
                        · rw [iteNegLocalSec4 hj75]
                          by_cases hj79 : j.val < 79
                          · rw [itePosLocalSec4 hj79]
                            exact (hOutγ _ (Or.inr (Or.inr (show 81 ≤ 6 + j.val by omega)))).trans
                              (βHead128_mid_zero s0 u2 _
                                (show 6 ≤ 6 + j.val ∧ 6 + j.val < 116 by omega)
                                (show 6 + j.val ≠ 36 by omega) (show 6 + j.val ≠ 37 by omega)
                                (show 6 + j.val ≠ 85 by omega))
                          · rw [iteNegLocalSec4 hj79,
                              show j = ⟨79, by decide⟩ from Fin.ext (show j.val = 79 by omega)]
                            dsimp only [pPre]
                            rw [hOutγ _ (Or.inr (Or.inr (by decide))), βHead128_u2_1,
                              basisBits_eq_div_mod]
                            fin_cases u2 <;> rfl
    · have hwOut : w.val < 6 ∨ 86 ≤ w.val := by
        by_contra hmid
        exact hwP ⟨⟨w.val - 6, by omega⟩, Fin.ext (show 6 + (w.val - 6) = w.val by omega)⟩
      have nFin (u : Wire 128) (hu : 6 ≤ u.val ∧ u.val < 86) : w ≠ u := ne_wire_of_val (by omega)
      rw [finishXorMap128_of_ne isMerged218 γX w (nFin _ (by decide)) (nFin _ (by decide))
        (nFin _ (by decide)) (nFin _ (by decide)) (nFin _ (by decide)) (nFin _ (by decide))]
      dsimp only [γX]
      rw [writeReg_apply_of_not_mem _ _ _ _ hwP, hOutγ w (by omega)]
      exact βHead128_eq_flags2_open_of_out s0 u2 pOut
        ((hOutEnc ⟨30, by decide⟩ (by decide)).trans (headJointPayload80_at30 _ _ _ _ _ _ _ _ _))
        w hwOut
  rw [hStateEq]
  exact ket_close_flags_open s0 _
theorem finishXorMap128_update68 (isMerged218 : Bool) (β : BitAssignment 128) (b : ZMod 2) :
    finishXorMap128 isMerged218 (Function.update β wSubReject_128 b) =
      Function.update (finishXorMap128 isMerged218 β) wSubReject_128 b := by
  funext w
  by_cases hw : w = wP80_128 ⟨75, by decide⟩ ∨ w = wP80_128 ⟨76, by decide⟩ ∨
      w = wP80_128 ⟨77, by decide⟩ ∨ w = rB1_128 ⟨0, by decide⟩ ∨
      w = rB1_128 ⟨1, by decide⟩ ∨ w = rB1_128 ⟨2, by decide⟩
  · rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [finishXorMap128, wSubReject_128, wP80_128, rB1_128, rB0_128, wEnS0_128, wEnTail_128,
        wEnS0Tail_128]
  · push Not at hw
    rcases hw with ⟨h1, h2, h3, h4, h5, h6⟩
    by_cases h68 : w = wSubReject_128
    · subst h68
      rw [finishXorMap128_of_ne isMerged218 _ wSubReject_128 h1 h2 h3 h4 h5 h6,
        Function.update_self, Function.update_self]
    · rw[finishXorMap128_of_ne isMerged218 _ w h1 h2 h3 h4 h5 h6, Function.update_of_ne h68,
        Function.update_of_ne h68, finishXorMap128_of_ne isMerged218 _ w h1 h2 h3 h4 h5 h6]
theorem flags2_open_padZero_update62 (s0 : Bool) (pOut : BitAssignment 80) (b : ZMod 2) :
    flags2Map128 (openMap128 (padZeroBits posPostHwa (ancBits86 s0 (Function.update pOut 62 b)))) =
      Function.update (flags2Map128 (openMap128 (padZeroBits posPostHwa (ancBits86 s0 pOut))))
        wSubReject_128 b := by
  have heq68 : wSubReject_128 = rP80_128 62 := Fin.ext rfl
  have hOpen :
      openMap128 (padZeroBits posPostHwa (ancBits86 s0 (Function.update pOut 62 b))) =
        Function.update (openMap128 (padZeroBits posPostHwa (ancBits86 s0 pOut)))
          wSubReject_128 b := by
    rw [openMap_ancBits_eq_writeReg, openMap_ancBits_eq_writeReg, heq68]
    funext w
    by_cases hw : w ∈ Set.range rP80_128.wires
    · obtain ⟨j, rfl⟩ := hw
      by_cases hj : j = 62
      · subst hj
        rw [writeReg_apply_reg, Function.update_self, Function.update_self]
      · rw [writeReg_apply_reg, Function.update_of_ne hj,
          Function.update_of_ne (fun h ↦ hj (rP80_128.wires.injective h)), writeReg_apply_reg]
    · rw [writeReg_apply_of_not_mem _ _ _ _ hw, Function.update_of_ne (fun h ↦ hw ⟨62, h.symm⟩),
        writeReg_apply_of_not_mem _ _ _ _ hw]
  rw [hOpen]
  funext w
  by_cases hw : w = wSubReject_128
  · subst hw
    dsimp only [flags2Map128]
    rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  · rw [Function.update_of_ne hw]
    exact flags2Map128_congr _ _ w (Function.update_of_ne (by decide) _ _)
      (Function.update_of_ne (by decide) _ _) (Function.update_of_ne (by decide) _ _)
      (Function.update_of_ne (by decide) _ _) (fun _ _ _ _ ↦ Function.update_of_ne hw _ _)
theorem finishXorMap_tail_eq (isMerged218 s0 : Bool) (t : TailTuple) :
    let (u2, nuc, b0, anc, part, dp, fine) := t
    let γT := writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (βTail128 s0 u2)
        rNuc_128 (basisBits 8 nuc)) rB0_128 (basisBits 3 b0)) rAnc_128 (basisBits 8 anc))
        rPart_128 (basisBits 8 part)) rB1_128 (basisBits 3 dp)) rFine30_128 (basisBits 30 fine)
    finishXorMap128 isMerged218 γT =
      flags2Map128 (openMap128 (padZeroBits posPostHwa
        (ancBits86 s0 (encTail80 isMerged218 s0 t)))) := by
  rcases t with ⟨u2, nuc, b0, anc, part, dp, fine⟩
  dsimp only
  let γT := writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (βTail128 s0 u2)
      rNuc_128 (basisBits 8 nuc)) rB0_128 (basisBits 3 b0)) rAnc_128 (basisBits 8 anc))
      rPart_128 (basisBits 8 part)) rB1_128 (basisBits 3 dp)) rFine30_128 (basisBits 30 fine)
  have hOutγ (w : Wire 128) (hw : w.val < 6 ∨ (36 ≤ w.val ∧ w.val < 38) ∨ 68 ≤ w.val) :
      γT w = βTail128 s0 u2 w := by
    dsimp only [γT, rFine30_128, rB1_128, rPart_128, rAnc_128, rB0_128, rNuc_128]
    iterate 6 rw [writeReg_block_out _ _ _ _ _ _ (by omega)]
  let pOut := encTail80 isMerged218 s0 (u2, nuc, b0, anc, part, dp, fine)
  have hOutEncT (idx : Fin 80) (h36 : ¬(3 ≤ idx.val ∧ idx.val < 6))
      (h7578 : ¬(75 ≤ idx.val ∧ idx.val < 78)) :
      encTail80 isMerged218 s0 (u2, nuc, b0, anc, part, dp, fine) idx =
        tailNormQ s0 (u2, nuc, b0, anc, part, dp, fine) idx := by
    dsimp only [encTail80]
    rw [rawFromNorm_of_not_b0 isMerged218 s0 b0 _ idx h36]
    have h30q : (tailNormQ s0 (u2, nuc, b0, anc, part, dp, fine) 30 == 1) = false := rfl
    cases s0
    · cases isMerged218
      · rfl
      · simp [flipTailDpScratch80, h30q, nat_beq_false (show idx.val ≠ 75 by omega),
          nat_beq_false (show idx.val ≠ 76 by omega), nat_beq_false (show idx.val ≠ 77 by omega)]
    · rfl
  have hγB1 (i : Fin 3) : γT (rB1_128 i) = basisBits 3 dp i := by
    dsimp only [γT, rFine30_128]
    rw [writeReg_block_out _ _ _ _ _ _ (show 6 + i.val < 38 ∨ 68 ≤ 6 + i.val by omega),
      writeReg_apply_reg]
  have hγB0 (i : Fin 3) : γT (rB0_128 i) = basisBits 3 b0 i := by
    have hv : (rB0_128 i).val = 9 + i.val := rfl
    dsimp only [γT, rFine30_128, rB1_128, rPart_128, rAnc_128]
    iterate 4 rw [writeReg_block_out _ _ _ _ _ _ (by omega)]
    exact writeReg_apply_reg _ _ _ _
  have hEnT1 : γT wEnTail_128 = 1 :=
    (hOutγ _ (Or.inr (Or.inr (by decide)))).trans (βTail128_enTail s0 u2)
  have hEnST : γT wEnS0Tail_128 = (if s0 then 1 else 0) :=
    (hOutγ _ (Or.inr (Or.inr (by decide)))).trans (βTail128_enS0Tail s0 u2)
  have hEnS0 : γT wEnS0_128 = (if s0 then 1 else 0) :=
    (hOutγ _ (Or.inr (Or.inr (by decide)))).trans (βTail128_enS0 s0 u2)
  funext w
  by_cases hwP : w ∈ Set.range rP80_128.wires
  · obtain ⟨j, rfl⟩ := hwP
    rw [flags2_open_ancBits_p80]
    by_cases hj3 : j.val < 3
    · obtain ⟨ax, hjAx⟩ : ∃ ax : Fin 3, j = ⟨ax.val, by omega⟩ := ⟨⟨j.val, hj3⟩, rfl⟩
      have hLHS : finishXorMap128 isMerged218 γT (rP80_128 ⟨ax.val, by omega⟩) =
          basisBits 3 dp ax + (if s0 then 1 else 0) * basisBits 3 b0 ax := by
        dsimp only [finishXorMap128]
        rw [hγB1 ⟨0, by decide⟩, hγB1 ⟨1, by decide⟩, hγB1 ⟨2, by decide⟩,
          hγB0 ⟨0, by decide⟩, hγB0 ⟨1, by decide⟩, hγB0 ⟨2, by decide⟩, hEnS0]
        fin_cases ax <;> simp [rP80_128, rB1_128, wP80_128]
      rw [hjAx, hLHS,
        hOutEncT _ (show ¬(3 ≤ ax.val ∧ ax.val < 6) by omega)
          (show ¬(75 ≤ ax.val ∧ ax.val < 78) by omega)]
      cases s0
      · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
        rw [basisBits_eq_z2BitOfNat]
        dsimp only [tailNormQ, tailWitnessPayload80]
        rw [iteNegLocalSec4 (by decide : ¬(false = true)),
          show Nat.xor 0 dp.val = dp.val from Nat.zero_xor dp.val]
        fin_cases ax <;> simp
      · simp only [↓reduceIte, one_mul]
        rw [add_comm, ← z2BitOfNat_xor3 b0 dp ax]
        dsimp only [tailNormQ, tailWitnessPayload80]
        rw [itePosLocalSec4 rfl]
        fin_cases ax <;> simp
    · by_cases hj75 : 75 ≤ j.val ∧ j.val < 78
      · obtain ⟨ax, hjAx⟩ : ∃ ax : Fin 3, j = ⟨75 + ax.val, by omega⟩ :=
          ⟨⟨j.val - 75, by omega⟩, Fin.ext (show j.val = 75 + (j.val - 75) by omega)⟩
        have h75_0 (idx : Fin 80) (hidx : 75 ≤ idx.val ∧ idx.val < 78) : γT (wP80_128 idx) = 0 :=
          (hOutγ _ (Or.inr (Or.inr (show 68 ≤ 6 + idx.val by omega)))).trans
            (βTail128_mid_zero s0 u2 _ (show 6 ≤ 6 + idx.val ∧ 6 + idx.val < 116 by omega)
              (show 6 + idx.val ≠ 37 by omega) (show 6 + idx.val ≠ 85 by omega))
        have hLHS : finishXorMap128 isMerged218 γT (rP80_128 ⟨75 + ax.val, by omega⟩) =
            (if isMerged218 then (if s0 then (1 : ZMod 2) else 0) else 1) *
              basisBits 3 dp ax := by
          dsimp only [finishXorMap128]
          rw [h75_0 ⟨75, by decide⟩ (by decide), h75_0 ⟨76, by decide⟩ (by decide),
            h75_0 ⟨77, by decide⟩ (by decide), hγB1 ⟨0, by decide⟩, hγB1 ⟨1, by decide⟩,
            hγB1 ⟨2, by decide⟩, hEnT1, hEnST]
          fin_cases ax <;> simp [rP80_128, rB1_128, wP80_128]
        rw [hjAx, hLHS]
        dsimp only [pOut, encTail80]
        rw [rawFromNorm_of_not_b0 isMerged218 s0 b0 _ ⟨75 + ax.val, by omega⟩
          (show ¬(3 ≤ 75 + ax.val ∧ 75 + ax.val < 6) by omega), basisBits_eq_z2BitOfNat]
        cases s0
        · cases isMerged218
          · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, one_mul,
              tailNormQ, tailWitnessPayload80]
            fin_cases ax <;> simp
          · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, zero_mul,
              flipTailDpScratch80]
            fin_cases ax <;> simp [tailNormQ, tailWitnessPayload80]
        · cases isMerged218 <;>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, one_mul,
              tailNormQ, tailWitnessPayload80] <;>
            (fin_cases ax <;> simp)
      · rw [finishXorMap128_of_ne isMerged218 γT (rP80_128 j)
          (ne_wire_of_val (show 6 + j.val ≠ 81 by omega))
          (ne_wire_of_val (show 6 + j.val ≠ 82 by omega))
          (ne_wire_of_val (show 6 + j.val ≠ 83 by omega))
          (ne_wire_of_val (show 6 + j.val ≠ 6 by omega))
          (ne_wire_of_val (show 6 + j.val ≠ 7 by omega))
          (ne_wire_of_val (show 6 + j.val ≠ 8 by omega))]
        by_cases hj6 : j.val < 6
        · let jb : Fin 3 := ⟨j.val - 3, by omega⟩
          rw [show rP80_128 j = rB0_128 jb from Fin.ext (show 6 + j.val = 9 + (j.val - 3) by omega),
            hγB0 jb]
          cases s0
          · dsimp only [pOut, encTail80, rawFromNorm]
            rw [itePosLocalSec4 (by decide : (!false) = true),
              ditePosLocalSec4 (⟨by omega, hj6⟩ : 3 ≤ j.val ∧ j.val < 6)]
          · rw [basisBits_eq_z2BitOfNat]
            dsimp only [pOut, encTail80, rawFromNorm, Bool.not_true,
              tailNormQ, tailWitnessPayload80, jb]
            rw [iteNegLocalSec4 (by decide), itePosLocalSec4 rfl,
              iteNegLocalSec4 hj3, itePosLocalSec4 hj6]
        · rw [hOutEncT j (by omega) hj75]
          by_cases hj14 : j.val < 14
          · dsimp only [γT, rFine30_128, rB1_128, rPart_128, rAnc_128, rB0_128, rNuc_128]
            iterate 5 rw [rP80_128_out_block j (by omega)]
            rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat]
            dsimp only [tailNormQ, tailWitnessPayload80]
            simp [hj3, hj6, hj14, show 6 + j.val - 12 = j.val - 6 by omega]
          · by_cases hj22 : j.val < 22
            · dsimp only [γT, rFine30_128, rB1_128, rPart_128, rAnc_128]
              iterate 3 rw [rP80_128_out_block j (by omega)]
              rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat]
              dsimp only [tailNormQ, tailWitnessPayload80]
              simp [hj3, hj6, hj14, hj22, show 6 + j.val - 20 = j.val - 14 by omega]
            · by_cases hj30 : j.val < 30
              · dsimp only [γT, rFine30_128, rB1_128, rPart_128]
                iterate 2 rw [rP80_128_out_block j (by omega)]
                rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat]
                dsimp only [tailNormQ, tailWitnessPayload80]
                simp [hj3, hj6, hj14, hj22, hj30, show 6 + j.val - 28 = j.val - 22 by omega]
              · by_cases hj32 : j.val < 32
                · rw [hOutγ _ (Or.inr (Or.inl (show 36 ≤ 6 + j.val ∧ 6 + j.val < 38 by omega)))]
                  by_cases hj30eq : j.val = 30
                  · rw [show j = ⟨30, by decide⟩ from Fin.ext hj30eq]
                    exact βTail128_mid_zero s0 u2 _ (by decide) (by decide) (by decide)
                  · rw [show j = ⟨31, by decide⟩ from Fin.ext (show j.val = 31 by omega),
                      βTail128_u2_0, basisBits_eq_div_mod]
                    fin_cases u2 <;> rfl
                · by_cases hj62 : j.val < 62
                  · dsimp only [γT, rFine30_128]
                    rw [rP80_128_in_block j (by omega) (by omega), basisBits_eq_z2BitOfNat]
                    dsimp only [tailNormQ, tailWitnessPayload80]
                    simp [hj3, hj6, hj14, hj22, hj30, hj62,
                      nat_beq_false (show j.val ≠ 30 by omega),
                      nat_beq_false (show j.val ≠ 31 by omega),
                      show 6 + j.val - 38 = j.val - 32 by omega]
                  · rw [hOutγ _ (Or.inr (Or.inr (show 68 ≤ 6 + j.val by omega)))]
                    by_cases hj78 : j.val < 78
                    · rw [βTail128_mid_zero s0 u2 (rP80_128 j)
                        (show 6 ≤ 6 + j.val ∧ 6 + j.val < 116 by omega)
                        (show 6 + j.val ≠ 37 by omega) (show 6 + j.val ≠ 85 by omega)]
                      by_cases hj62eq : j.val = 62
                      · rw [show j = ⟨62, by decide⟩ from Fin.ext hj62eq]
                        rfl
                      · dsimp only [tailNormQ, tailWitnessPayload80]
                        simp [hj3, hj6, hj14, hj22, hj30, hj62, show j.val < 75 by omega,
                          nat_beq_false (show j.val ≠ 30 by omega),
                          nat_beq_false (show j.val ≠ 31 by omega), nat_beq_false hj62eq]
                    · by_cases hj78eq : j.val = 78
                      · rw [show j = ⟨78, by decide⟩ from Fin.ext hj78eq]
                        exact βTail128_mid_zero s0 u2 _ (by decide) (by decide) (by decide)
                      · rw [show j = ⟨79, by decide⟩ from Fin.ext (show j.val = 79 by omega),
                          βTail128_u2_1, basisBits_eq_div_mod]
                        fin_cases u2 <;> rfl
  · have hwOut : w.val < 6 ∨ 86 ≤ w.val := by
      by_contra hmid
      exact hwP ⟨⟨w.val - 6, by omega⟩, Fin.ext (show 6 + (w.val - 6) = w.val by omega)⟩
    have nFin (u : Wire 128) (hu : 6 ≤ u.val ∧ u.val < 86) : w ≠ u := ne_wire_of_val (by omega)
    rw [finishXorMap128_of_ne isMerged218 γT w (nFin _ (by decide)) (nFin _ (by decide))
      (nFin _ (by decide)) (nFin _ (by decide)) (nFin _ (by decide)) (nFin _ (by decide)),
      hOutγ w (hwOut.elim Or.inl fun _ ↦ Or.inr (Or.inr (by omega)))]
    exact βTail128_eq_flags2_open_of_out s0 u2 pOut
      (hOutEncT ⟨30, by decide⟩ (by decide) (by decide)) w hwOut
abbrev Payload80Bits := BitAssignment 2 × BitAssignment 3 × BitAssignment 16 × ZMod 2 ×
    BitAssignment 3 × BitAssignment 33 × BitAssignment 21 × ZMod 2
def payload80Join (t : Payload80Bits) : BitAssignment 80 :=
  let (qU2, qB0, qJ16, bPid0, qSm, qJ, qR21, bIH) := t
  fun j ↦
    if hj1 : j.val < 3 then qJ ⟨j.val, by omega⟩
    else if hj2 : j.val < 6 then qB0 ⟨j.val - 3, by omega⟩
    else if hj3 : j.val < 22 then qJ16 ⟨j.val - 6, by omega⟩
    else if hj4 : j.val < 30 then qR21 ⟨j.val - 22, by omega⟩
    else if hj5 : j.val = 30 then bIH
    else if hj6 : j.val = 31 then qU2 ⟨0, by decide⟩
    else if hj7 : j.val < 62 then qJ ⟨j.val - 29, by omega⟩
    else if hj8 : j.val < 69 then qR21 ⟨j.val - 54, by omega⟩
    else if hj9 : j.val = 69 then bPid0
    else if hj10 : j.val < 72 then qR21 ⟨j.val - 55, by omega⟩
    else if hj11 : j.val < 75 then qSm ⟨j.val - 72, by omega⟩
    else if hj12 : j.val < 79 then qR21 ⟨j.val - 58, by omega⟩
    else qU2 ⟨1, by decide⟩
def payload80Split (q : BitAssignment 80) : Payload80Bits :=
  (fun i : Fin 2 ↦ if i.val = 0 then q ⟨31, by decide⟩ else q ⟨79, by decide⟩,
   fun i : Fin 3 ↦ q ⟨3 + i.val, by omega⟩,
   fun i : Fin 16 ↦ q ⟨6 + i.val, by omega⟩,
   q ⟨69, by decide⟩,
   fun i : Fin 3 ↦ q ⟨72 + i.val, by omega⟩,
   fun i : Fin 33 ↦ if i.val < 3 then q ⟨i.val, by omega⟩ else q ⟨29 + i.val, by omega⟩,
   fun i : Fin 21 ↦
     if i.val < 8 then q ⟨22 + i.val, by omega⟩
     else if i.val < 15 then q ⟨54 + i.val, by omega⟩
     else if i.val < 17 then q ⟨55 + i.val, by omega⟩
     else q ⟨58 + i.val, by omega⟩,
   q ⟨30, by decide⟩)
def payload80BitsEquiv : Payload80Bits ≃ BitAssignment 80 where
  toFun := payload80Join
  invFun := payload80Split
  left_inv := fun ⟨qU2, qB0, qJ16, bPid0, qSm, qJ, qR21, bIH⟩ ↦
    Prod.ext (funext fun i ↦ by fin_cases i <;> rfl)
      (Prod.ext (funext fun i ↦ by fin_cases i <;> rfl)
        (Prod.ext (funext fun i ↦ by fin_cases i <;> rfl)
          (Prod.ext rfl
            (Prod.ext (funext fun i ↦ by fin_cases i <;> rfl)
              (Prod.ext (funext fun i ↦ by fin_cases i <;> rfl)
                (Prod.ext (funext fun i ↦ by fin_cases i <;> rfl) rfl))))))
  right_inv q := funext fun j ↦ by fin_cases j <;> rfl
theorem writeReg_p80_eq_nested (s0 : Bool)
    (qU2 : BitAssignment 2) (qB0 : BitAssignment 3) (qJ16 : BitAssignment 16) (bPid0 : ZMod 2)
    (qSm : BitAssignment 3) (qJ : BitAssignment 33) (qR21 : BitAssignment 21) (bIH : ZMod 2) :
    writeReg (βInit128 s0) rP80_128
        (payload80BitsEquiv (qU2, qB0, qJ16, bPid0, qSm, qJ, qR21, bIH)) =
      Function.update (writeReg (writeReg (writeReg (Function.update (writeReg (writeReg
        (writeReg (βInit128 s0) rTwoUnif_128 qU2) rB0_128 qB0) rJoint16_128 qJ16)
        (rPid_128 ⟨0, by decide⟩) bPid0) rSm_128 qSm) rJoint33_128 qJ) rRest21_128 qR21)
        wIsHead_128 bIH := by
  let s1 := writeReg (βInit128 s0) rTwoUnif_128 qU2
  let s2 := writeReg s1 rB0_128 qB0
  let s3 := writeReg s2 rJoint16_128 qJ16
  let s4 := Function.update s3 (rPid_128 ⟨0, by decide⟩) bPid0
  let s5 := writeReg s4 rSm_128 qSm
  let s6 := writeReg s5 rJoint33_128 qJ
  let s7 := writeReg s6 rRest21_128 qR21
  let rhs := Function.update s7 wIsHead_128 bIH
  have hnot_IH (j : Fin 80) (hj : j.val ≠ 30) : rP80_128 j ≠ wIsHead_128 :=
    ne_wire_of_val (show 6 + j.val ≠ 36 by omega)
  have hnot_R21 (j : Fin 80) (hj : ¬((22 ≤ j.val ∧ j.val < 30) ∨ (62 ≤ j.val ∧ j.val < 69) ∨
      (70 ≤ j.val ∧ j.val < 72) ∨ (75 ≤ j.val ∧ j.val < 79))) :
      rP80_128 j ∉ Set.range rRest21_128.wires := fun ⟨i, hi⟩ ↦ by
    have := i.isLt
    have hv : (if i.val < 8 then 28 + i.val else if i.val < 15 then 60 + i.val
      else if i.val < 17 then 61 + i.val else 64 + i.val) = 6 + j.val := congrArg Fin.val hi
    split_ifs at hv <;> omega
  have hnot_J (j : Fin 80) (hj : ¬(j.val < 3 ∨ (32 ≤ j.val ∧ j.val < 62))) :
      rP80_128 j ∉ Set.range rJoint33_128.wires := fun ⟨i, hi⟩ ↦ by
    have := i.isLt
    have hv : (if i.val < 3 then 6 + i.val else 35 + i.val) = 6 + j.val := congrArg Fin.val hi
    split_ifs at hv <;> omega
  have hnot_Sm (j : Fin 80) (hj : ¬(72 ≤ j.val ∧ j.val < 75)) :
      rP80_128 j ∉ Set.range rSm_128.wires := fun ⟨i, hi⟩ ↦ by
    have hv : 78 + i.val = 6 + j.val := congrArg Fin.val hi
    omega
  have hnot_Pid0 (j : Fin 80) (hj : j.val ≠ 69) : rP80_128 j ≠ rPid_128 ⟨0, by decide⟩ :=
    ne_wire_of_val (show 6 + j.val ≠ 75 by omega)
  have hnot_J16 (j : Fin 80) (hj : ¬(6 ≤ j.val ∧ j.val < 22)) :
      rP80_128 j ∉ Set.range rJoint16_128.wires := fun ⟨i, hi⟩ ↦ by
    have hv : 12 + i.val = 6 + j.val := congrArg Fin.val hi
    omega
  have hnot_B0 (j : Fin 80) (hj : ¬(3 ≤ j.val ∧ j.val < 6)) :
      rP80_128 j ∉ Set.range rB0_128.wires := fun ⟨i, hi⟩ ↦ by
    have hv : 9 + i.val = 6 + j.val := congrArg Fin.val hi
    omega
  have hHitR21 (j : Fin 80) (kv : ℕ) (hkv : kv < 21) (hj : j.val ≠ 30)
      (hk : (kv < 8 ∧ 6 + j.val = 28 + kv) ∨ (8 ≤ kv ∧ kv < 15 ∧ 6 + j.val = 60 + kv) ∨
        (15 ≤ kv ∧ kv < 17 ∧ 6 + j.val = 61 + kv) ∨ (17 ≤ kv ∧ 6 + j.val = 64 + kv)) :
      qR21 ⟨kv, hkv⟩ = rhs (rP80_128 j) := by
    have heq : rP80_128 j = rRest21_128 ⟨kv, hkv⟩ := Fin.ext (by
      change 6 + j.val = if kv < 8 then 28 + kv else if kv < 15 then 60 + kv
        else if kv < 17 then 61 + kv else 64 + kv
      split_ifs <;> omega)
    dsimp only [rhs, s7]
    rw [Function.update_of_ne (hnot_IH j hj), heq, writeReg_apply_reg]
  have hHitJ33 (j : Fin 80) (kv : ℕ) (hkv : kv < 33) (hj : j.val ≠ 30)
      (hR : ¬((22 ≤ j.val ∧ j.val < 30) ∨ (62 ≤ j.val ∧ j.val < 69) ∨
        (70 ≤ j.val ∧ j.val < 72) ∨ (75 ≤ j.val ∧ j.val < 79)))
      (hk : (kv < 3 ∧ 6 + j.val = 6 + kv) ∨ (3 ≤ kv ∧ 6 + j.val = 35 + kv)) :
      qJ ⟨kv, hkv⟩ = rhs (rP80_128 j) := by
    have heq : rP80_128 j = rJoint33_128 ⟨kv, hkv⟩ := Fin.ext (by
      change 6 + j.val = if kv < 3 then 6 + kv else 35 + kv
      split_ifs <;> omega)
    dsimp only [rhs, s7, s6]
    rw [Function.update_of_ne (hnot_IH j hj), writeReg_apply_of_not_mem _ _ _ _ (hnot_R21 j hR),
      heq, writeReg_apply_reg]
  have hPass5 (j : Fin 80) (hj : j.val ≠ 30)
      (hR : ¬((22 ≤ j.val ∧ j.val < 30) ∨ (62 ≤ j.val ∧ j.val < 69) ∨
        (70 ≤ j.val ∧ j.val < 72) ∨ (75 ≤ j.val ∧ j.val < 79)))
      (hJ : ¬(j.val < 3 ∨ (32 ≤ j.val ∧ j.val < 62))) (hS : ¬(72 ≤ j.val ∧ j.val < 75))
      (hP : j.val ≠ 69) : rhs (rP80_128 j) = s3 (rP80_128 j) := by
    dsimp only [rhs, s7, s6, s5, s4]
    rw [Function.update_of_ne (hnot_IH j hj), writeReg_apply_of_not_mem _ _ _ _ (hnot_R21 j hR),
      writeReg_apply_of_not_mem _ _ _ _ (hnot_J j hJ),
      writeReg_apply_of_not_mem _ _ _ _ (hnot_Sm j hS), Function.update_of_ne (hnot_Pid0 j hP)]
  funext w
  by_cases hw : w ∈ Set.range rP80_128.wires
  · obtain ⟨j, rfl⟩ := hw
    rw [writeReg_apply_reg]
    change payload80Join (qU2, qB0, qJ16, bPid0, qSm, qJ, qR21, bIH) j = rhs (rP80_128 j)
    dsimp only [payload80Join]
    by_cases hj1 : j.val < 3
    · rw [ditePosLocalSec4 hj1]
      exact hHitJ33 j j.val (by omega) (by omega) (by omega) (by omega)
    · rw [diteNegLocalSec4 hj1]
      by_cases hj2 : j.val < 6
      · rw [ditePosLocalSec4 hj2, hPass5 j (by omega) (by omega) (by omega) (by omega) (by omega)]
        dsimp only [s3, s2]
        rw [writeReg_apply_of_not_mem _ _ _ _ (hnot_J16 j (by omega)),
          show rP80_128 j = rB0_128 ⟨j.val - 3, by omega⟩ from
            Fin.ext (show 6 + j.val = 9 + (j.val - 3) by omega), writeReg_apply_reg]
      · rw [diteNegLocalSec4 hj2]
        by_cases hj3 : j.val < 22
        · rw [ditePosLocalSec4 hj3, hPass5 j (by omega) (by omega) (by omega) (by omega) (by omega)]
          dsimp only [s3]
          rw [show rP80_128 j = rJoint16_128 ⟨j.val - 6, by omega⟩ from
              Fin.ext (show 6 + j.val = 12 + (j.val - 6) by omega), writeReg_apply_reg]
        · rw [diteNegLocalSec4 hj3]
          by_cases hj4 : j.val < 30
          · rw [ditePosLocalSec4 hj4]
            exact hHitR21 j (j.val - 22) (by omega) (by omega) (by omega)
          · rw [diteNegLocalSec4 hj4]
            by_cases hj5 : j.val = 30
            · rw [ditePosLocalSec4 hj5]
              dsimp only [rhs]
              rw [show rP80_128 j = wIsHead_128 from Fin.ext (show 6 + j.val = 36 by omega),
                Function.update_self]
            · rw [diteNegLocalSec4 hj5]
              by_cases hj6 : j.val = 31
              · rw [ditePosLocalSec4 hj6,
                  hPass5 j (by omega) (by omega) (by omega) (by omega) (by omega)]
                dsimp only [s3, s2, s1]
                rw [writeReg_apply_of_not_mem _ _ _ _ (hnot_J16 j (by omega)),
                  writeReg_apply_of_not_mem _ _ _ _ (hnot_B0 j (by omega)),
                  show j = ⟨31, by decide⟩ from Fin.ext hj6,
                  show rP80_128 ⟨31, by decide⟩ = rTwoUnif_128 ⟨0, by decide⟩ from Fin.ext rfl,
                  writeReg_apply_reg]
              · rw [diteNegLocalSec4 hj6]
                by_cases hj7 : j.val < 62
                · rw [ditePosLocalSec4 hj7]
                  exact hHitJ33 j (j.val - 29) (by omega) (by omega) (by omega) (by omega)
                · rw [diteNegLocalSec4 hj7]
                  by_cases hj8 : j.val < 69
                  · rw [ditePosLocalSec4 hj8]
                    exact hHitR21 j (j.val - 54) (by omega) (by omega) (by omega)
                  · rw [diteNegLocalSec4 hj8]
                    by_cases hj9 : j.val = 69
                    · rw [ditePosLocalSec4 hj9]
                      dsimp only [rhs, s7, s6, s5, s4]
                      rw [Function.update_of_ne (hnot_IH j (by omega)),
                        writeReg_apply_of_not_mem _ _ _ _ (hnot_R21 j (by omega)),
                        writeReg_apply_of_not_mem _ _ _ _ (hnot_J j (by omega)),
                        writeReg_apply_of_not_mem _ _ _ _ (hnot_Sm j (by omega)),
                        show rP80_128 j = rPid_128 ⟨0, by decide⟩ from
                          Fin.ext (show 6 + j.val = 75 by omega), Function.update_self]
                    · rw [diteNegLocalSec4 hj9]
                      by_cases hj10 : j.val < 72
                      · rw [ditePosLocalSec4 hj10]
                        exact hHitR21 j (j.val - 55) (by omega) (by omega) (by omega)
                      · rw [diteNegLocalSec4 hj10]
                        by_cases hj11 : j.val < 75
                        · rw [ditePosLocalSec4 hj11]
                          dsimp only [rhs, s7, s6, s5]
                          rw [Function.update_of_ne (hnot_IH j (by omega)),
                            writeReg_apply_of_not_mem _ _ _ _ (hnot_R21 j (by omega)),
                            writeReg_apply_of_not_mem _ _ _ _ (hnot_J j (by omega)),
                            show rP80_128 j = rSm_128 ⟨j.val - 72, by omega⟩ from
                              Fin.ext (show 6 + j.val = 78 + (j.val - 72) by omega),
                            writeReg_apply_reg]
                        · rw [diteNegLocalSec4 hj11]
                          by_cases hj12 : j.val < 79
                          · rw [ditePosLocalSec4 hj12]
                            exact hHitR21 j (j.val - 58) (by omega) (by omega) (by omega)
                          · rw [diteNegLocalSec4 hj12,
                              hPass5 j (by omega) (by omega) (by omega) (by omega) (by omega)]
                            dsimp only [s3, s2, s1]
                            rw [writeReg_apply_of_not_mem _ _ _ _ (hnot_J16 j (by omega)),
                              writeReg_apply_of_not_mem _ _ _ _ (hnot_B0 j (by omega)),
                              show j = ⟨79, by decide⟩ from Fin.ext (show j.val = 79 by omega),
                              show rP80_128 ⟨79, by decide⟩ = rTwoUnif_128 ⟨1, by decide⟩ from
                                Fin.ext rfl, writeReg_apply_reg]
  · have hwOut : w.val < 6 ∨ 86 ≤ w.val := by
      by_contra hmid
      exact hw ⟨⟨w.val - 6, by omega⟩, Fin.ext (show 6 + (w.val - 6) = w.val by omega)⟩
    have hnPay {m} (r : QRegister m 128)
        (hr : ∀ i, 6 ≤ (r i).val ∧ (r i).val < 86 ∧ (r i).val ≠ 36) :
        w ∉ Set.range r.wires := fun ⟨i, hi⟩ ↦ by
      have := hr i
      have := congrArg Fin.val hi
      omega
    rw [writeReg_apply_of_not_mem _ _ _ _ hw,
      Function.update_of_ne (ne_wire_of_val (show w.val ≠ 36 by omega)),
      writeReg_apply_of_not_mem _ _ _ _ (hnPay _ rRest21_payload_not36),
      writeReg_apply_of_not_mem _ _ _ _ (hnPay _ rJoint33_payload_not36),
      writeReg_apply_of_not_mem _ _ _ _ (hnPay rSm_128 (block_payload_not36 78 3 _ (by decide))),
      Function.update_of_ne (ne_wire_of_val (show w.val ≠ 75 by omega)),
      writeReg_apply_of_not_mem _ _ _ _ (hnPay _ rJoint16_payload_not36),
      writeReg_apply_of_not_mem _ _ _ _ (hnPay rB0_128 (block_payload_not36 9 3 _ (by decide))),
      writeReg_twoUnif_out _ _ w (by omega) (by omega)]
theorem chIf_mulVec_uniform_pair (ctrl t : Wire 128) (hct : ctrl ≠ t) (δ : BitAssignment 128)
    (hc : δ ctrl = 1) (ht : δ t = 0) : (chIf ctrl t).eval.1.mulVec
    (∑ b : ZMod 2, (1 / √(2 : ℝ) : ℂ) • ket (Function.update δ t b)) = ket δ := by
  have hc0 : Function.update δ t 0 ctrl = 1 := by rw [Function.update_of_ne hct, hc]
  have hc1 : Function.update δ t 1 ctrl = 1 := by rw [Function.update_of_ne hct, hc]
  have hmul : (1 / √(2 : ℝ) : ℂ) * MeasureBranchHadamardSem.sqrtHalf = 1 / 2 := by
    rw [sqrtHalf_eq_one_div_sqrt_two, MeasureBranchHadamardSem.sqrtHalf_mul_sqrtHalf]
  have hs0 : MeasureBranchHadamardSem.bitSign 0 = 1 := rfl
  have hs1 : MeasureBranchHadamardSem.bitSign 1 = -1 := by
    unfold MeasureBranchHadamardSem.bitSign
    exact iteNegLocalSec4 (by decide)
  rw [(by decide : (Finset.univ : Finset (ZMod 2)) = {0, 1}),
    Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, chIf, dite_neg' hct, chCircuit_mulVec_ket_ctrl_one ctrl t hct _ hc0,
    chCircuit_mulVec_ket_ctrl_one ctrl t hct _ hc1, MeasureBranchHadamardSem.ket_H,
    MeasureBranchHadamardSem.ket_H]
  simp only [Function.update_self, Function.update_idem, hs0, hs1, mul_one, mul_neg, smul_add,
    smul_smul, hmul, upd_eq_self δ t ht]
  let v0 := ket δ
  let v1 := ket (Function.update δ t 1)
  change ((1 / 2 : ℂ) • v0 + (1 / 2 : ℂ) • v1) + ((1 / 2 : ℂ) • v0 + (-(1 / 2 : ℂ)) • v1) = v0
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  norm_num
theorem flags2Map128_writeReg_payload {m : ℕ} (r : QRegister m 128)
    (hr : ∀ i : Fin m, 6 ≤ (r i).val ∧ (r i).val < 86 ∧ (r i).val ≠ 36)
    (δ : BitAssignment 128) (v : BitAssignment m) :
    flags2Map128 (writeReg δ r v) = writeReg (flags2Map128 δ) r v := by
  have hout (w : Wire 128) (hw : w.val < 6 ∨ 86 ≤ w.val ∨ w.val = 36) :
      w ∉ Set.range r.wires := fun ⟨i, hi⟩ ↦ by
    have := hr i
    have := congrArg Fin.val hi
    omega
  funext w
  by_cases hwr : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hwr
    have hri := hr i
    rw [writeReg_apply_reg, flags2Map128_of_ne _ _ (by omega), writeReg_apply_reg]
  · rw [writeReg_apply_of_not_mem _ _ _ _ hwr]
    exact flags2Map128_congr _ _ w
      (writeReg_apply_of_not_mem _ _ _ _ (hout _ (Or.inr (Or.inl (by decide)))))
      (writeReg_apply_of_not_mem _ _ _ _ (hout _ (Or.inr (Or.inr rfl))))
      (writeReg_apply_of_not_mem _ _ _ _ (hout _ (Or.inr (Or.inl (by decide)))))
      (writeReg_apply_of_not_mem _ _ _ _ (hout _ (Or.inr (Or.inl (by decide)))))
      (fun _ _ _ _ ↦ writeReg_apply_of_not_mem _ _ _ _ hwr)
end ConfigInnerAmp
end PosPostPrep80InnerAmpS3
end
end ModPosPostPrep80InnerAmpS3
end PosPostPrep80InnerAmpS3
end
set_option exponentiation.threshold 256
end PosPostPrep80InnerAmpS3_p2

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
