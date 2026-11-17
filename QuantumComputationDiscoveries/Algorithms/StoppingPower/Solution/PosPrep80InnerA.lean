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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80VepCore

set_option Elab.async false

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosPostPrep80InnerAmpS3_p1
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80InnerAmpS3_p1 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
section PosPostPrep80InnerAmpS3

section ModPosPostPrep80InnerAmpS3
public section
namespace PosPostPrep80InnerAmpS3Alt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end PosPostPrep80InnerAmpS3Alt
namespace PosPostPrep80InnerAmpS3
section ConfigInnerAmp
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2000000
set_option exponentiation.threshold 256
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket ket_X ket_Z ket_H ket_CNOT ket_TOFF sqrtHalf bitSign bit_cases
  eval_seq_mulVec)
local instance (priority :=
  1000000) instLoc_PosPostPrep80InnerAmpS3_1InstNeZeroTwoPowInn {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩
open ZeroAncillaUSPS3 hiding ket
open Pos24HeadCoordXor80 (bitsVal3_lt8 headCoordXorLocal67 headOutMask24
  evolve_headCoordXorLocal67_of_clean rHeadAct37In80 rOut24In67 xorRegBits xorRegBits_apply_reg
  xorRegBits_apply_of_not_mem)
open PosPostPrep80MergedVepS3
theorem posPostHwa : 86 + 42 = 128 := by decide
def ancBits86 (s0 : Bool) (p80 : BitAssignment 80) : BitAssignment 86 := fun idx ↦ if idx.val
    == 0 then (if s0 then 1 else 0) else if hlt : idx.val < 6 then 0 else p80 ⟨idx.val - 6,
    PosSlots24SemanticOracleConcrete80.ancIdx86_sub_lt idx hlt⟩
theorem bitsVal_zero_local {m : ℕ} :
    Pos24HeadCoordXor80.bitsVal (fun _ : Fin m ↦ (0 : ZMod 2)) = 0 := by
  simp [Pos24HeadCoordXor80.bitsVal]
theorem ditePosLocal {P : Prop} [inst : Decidable P] {α : Sort*} {t : P → α} {e : ¬P → α}
    (h : P) : dite P t e = t h := dite_eq_left h
theorem diteNegLocal {P : Prop} [inst : Decidable P] {α : Sort*} {t : P → α} {e : ¬P → α}
    (h : ¬P) : dite P t e = e h := dite_eq_right h
theorem pos80_clean_scr75 (p : BitAssignment 80)
    (h : p ⟨75, by decide⟩ ≠ 0 ∨ p ⟨76, by decide⟩ ≠ 0 ∨
         p ⟨77, by decide⟩ ≠ 0 ∨ p ⟨78, by decide⟩ ≠ 0) :
    muActualFactor80 true false p = 0 := by
  unfold muActualFactor80
  simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  set q : BitAssignment 80 := flipTailDpScratch80 (p80ClearB0Local p)
  have hc30 : p80ClearB0Local p 30 = p 30 := rfl
  by_cases hp30 : (p 30 == 1) = true
  · have hq_eq : q = p80ClearB0Local p := by
      change (if p80ClearB0Local p 30 == 1 then p80ClearB0Local p else _) = _
      rw [hc30, itePosLocal hp30]
    rw [itePosLocal (by rwa [hq_eq, hc30] : (q 30 == 1) = true)]
    by_cases hq62 : (q 62 != 0) = true
    · rw [itePosLocal hq62]
    · rw [iteNegLocal hq62]
      by_cases hk : Pos24HeadCoordXor80.bitsVal
          (fun j : Fin 6 ↦ q (pos80SubIdx 63 6 (by decide) j)) < 56
      · rw [ditePosLocal hk, show ((q 75 == 0) && (q 76 == 0) && (q 77 == 0) && (q 78 == 0)) =
            false from Bool.eq_false_iff.mpr fun hc ↦ by
          rw [hq_eq] at hc
          change ((p ⟨75, by decide⟩ == 0) && (p ⟨76, by decide⟩ == 0) &&
            (p ⟨77, by decide⟩ == 0) && (p ⟨78, by decide⟩ == 0)) = true at hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          tauto]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      · exact diteNegLocal hk
  · have hq_def : q = fun r ↦ if r.val == 75 then p80ClearB0Local p 75 + p80ClearB0Local p 0
      else if r.val == 76 then p80ClearB0Local p 76 + p80ClearB0Local p 1 else if r.val == 77
      then p80ClearB0Local p 77 + p80ClearB0Local p 2 else p80ClearB0Local p r := by
      change (if p80ClearB0Local p 30 == 1 then p80ClearB0Local p else _) = _
      rw [hc30, iteNegLocal hp30]
    rw [iteNegLocal (by rwa [hq_def] : ¬(q 30 == 1) = true)]
    by_cases hcond :
        (((decide (∀ j : Fin 12, q (pos80SubIdx 63 12 (by decide) j) = 0) && (q 78 == 0)) &&
          decide (Pos24HeadCoordXor80.bitsVal
            (fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j)) < 2)) &&
         (Function.update q 62 0 == tailWitnessPayload80
            (Pos24HeadCoordXor80.bitsVal fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j))
            (Pos24HeadCoordXor80.bitsVal fun j : Fin 8 ↦ q (pos80SubIdx 6 8 (by decide) j))
            (Pos24HeadCoordXor80.bitsVal fun j : Fin 8 ↦ q (pos80SubIdx 14 8 (by decide) j))
            (Pos24HeadCoordXor80.bitsVal fun j : Fin 8 ↦ q (pos80SubIdx 22 8 (by decide) j))
            ⟨Pos24HeadCoordXor80.bitsVal fun j : Fin 3 ↦ q (pos80SubIdx 75 3 (by decide) j),
              bitsVal3_lt8 _⟩
            (Pos24HeadCoordXor80.bitsVal fun j : Fin 30 ↦ q (pos80SubIdx 32 30 (by decide) j))
            (q 31 == 1) (q 79 == 1))) = true
    · exfalso
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      have hq78 : p ⟨78, by decide⟩ = 0 :=
        (show q 78 = p ⟨78, by decide⟩ by
          rw [hq_def]
          rfl).symm.trans hcond.1.1.2
      have htw := hcond.2
      rw [show (Pos24HeadCoordXor80.bitsVal fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j)) = 0
        by
          rw [show (fun j : Fin 3 ↦ q (pos80SubIdx 3 3 (by decide) j)) = fun _ ↦ 0 from
            funext fun j ↦ by
              fin_cases j
              all_goals
                rw [hq_def]
                rfl, bitsVal_zero_local]] at htw
      set dpv := (⟨Pos24HeadCoordXor80.bitsVal
        fun j : Fin 3 ↦ q (pos80SubIdx 75 3 (by decide) j), bitsVal3_lt8 _⟩ : Fin 8)
      have hp_zero : ∀ i : Fin 3, p ⟨75 + i.val, by omega⟩ = 0 := fun i ↦ by
        have ei := congrFun htw ⟨i.val, by omega⟩
        have eb := congrFun htw ⟨75 + i.val, by omega⟩
        rw [show Function.update q 62 0 ⟨i.val, by omega⟩ = p ⟨i.val, by omega⟩ by
          rw [Function.update_of_ne (fun he ↦ by
            have hv : i.val = 62 := congrArg Fin.val he
            omega), hq_def]
          fin_cases i <;> rfl] at ei
        rw [show Function.update q 62 0 ⟨75 + i.val, by omega⟩ =
            p ⟨75 + i.val, by omega⟩ + p ⟨i.val, by omega⟩ by
          rw [Function.update_of_ne (fun he ↦ by
            have hv : 75 + i.val = 62 := congrArg Fin.val he
            omega), hq_def]
          fin_cases i <;> rfl] at eb
        fin_cases i
        all_goals
          dsimp [tailWitnessPayload80] at ei eb
          rw [Nat.zero_xor dpv.val] at ei
          exact add_right_cancel ((ei.trans eb.symm).symm.trans (zero_add _).symm)
      exact h.elim (· (hp_zero 0)) fun h ↦
        h.elim (· (hp_zero 1)) fun h ↦ h.elim (· (hp_zero 2)) (· hq78)
    · rw [iteNegLocal hcond]
theorem pos80_clean_scr75_zero (p : BitAssignment 80)
    (h : muActualFactor80 true false p ≠ 0) :
    p ⟨75, by decide⟩ = 0 := by
  by_contra h75
  exact h (pos80_clean_scr75 p (Or.inl h75))
noncomputable def KetSpan {n : ℕ} (P : BitAssignment n → Prop) :
    Submodule ℂ (Fin (2 ^ n) → ℂ) :=
  Submodule.span ℂ { ψ | ∃ β : BitAssignment n, P β ∧ ψ = ket β }
def PreservesSpan {n : ℕ} (P Q : BitAssignment n → Prop) (c : Circuit n) : Prop :=
  ∀ β : BitAssignment n, P β → c.eval.1.mulVec (ket β) ∈ KetSpan Q
def WireIndep {n : ℕ} (P : BitAssignment n → Prop) (w : Wire n) : Prop :=
  ∀ (β : BitAssignment n) (b : ZMod 2), P β → P (Function.update β w b)
theorem ket_mem_ketSpan {n : ℕ} {P : BitAssignment n → Prop} {β : BitAssignment n} (h : P β) :
    ket β ∈ KetSpan P := Submodule.subset_span ⟨β, h, rfl⟩
theorem mulVec_mem_ketSpan {n : ℕ} {P Q : BitAssignment n → Prop} (M : Operator (2 ^ n))
    (h : ∀ β : BitAssignment n, P β → M.mulVec (ket β) ∈ KetSpan Q) {ψ : Fin (2 ^ n) → ℂ}
    (hψ : ψ ∈ KetSpan P) : M.mulVec ψ ∈ KetSpan Q := by
  induction hψ using Submodule.span_induction with
  | mem _ hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      exact h β hβ
  | zero => simp only [Matrix.mulVec_zero, Submodule.zero_mem]
  | add _ _ _ _ ihx ihy =>
      rw [Matrix.mulVec_add]
      exact (KetSpan Q).add_mem ihx ihy
  | smul c _ _ ihx =>
      rw [Matrix.mulVec_smul]
      exact (KetSpan Q).smul_mem c ihx
theorem preservesSpan_id {n : ℕ} {P : BitAssignment n → Prop} :
    PreservesSpan P P (Circuit.identity : Circuit n) := fun β hβ ↦ by
  simp only [Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec]
  exact ket_mem_ketSpan hβ
theorem preservesSpan_seq {n : ℕ} {P Q R : BitAssignment n → Prop} {c₁ c₂ : Circuit n}
    (h₁ : PreservesSpan P Q c₁) (h₂ : PreservesSpan Q R c₂) :
    PreservesSpan P R (c₁ ;;ᶜ c₂) := fun β hβ ↦ by
  rw [MeasureBranchHadamardSem.eval_seq_mulVec]
  exact mulVec_mem_ketSpan c₂.eval.1 h₂ (h₁ β hβ)
theorem inv_mulVec_ket_of_fwd {n : ℕ} (c : Circuit n) (β₀ β₁ : BitAssignment n)
    (hFwd : c.eval.1.mulVec (ket β₀) = ket β₁) :
    c.inverse.eval.1.mulVec (ket β₁) = ket β₀ := by
  rw [← hFwd, Circuit.eval_inverse, Matrix.mulVec_mulVec,
    show (c.eval⁻¹).1 * c.eval.1 = 1 from congrArg Subtype.val (inv_mul_cancel c.eval),
    Matrix.one_mulVec]
theorem preservesSpan_singleton_matrix {n : ℕ} {P : BitAssignment n → Prop} (q : Wire n)
    (hq : WireIndep P q) (M : Matrix (Fin 2) (Fin 2) ℂ) (β : BitAssignment n) (hβ : P β) :
    ((QRegister.singleton q).embedMatrix M).mulVec (ket β) ∈ KetSpan P := by
  rw [singleton_embedMatrix_mulVec_ket]
  split_ifs <;>
    exact (KetSpan P).add_mem ((KetSpan P).smul_mem _ (ket_mem_ketSpan (hq β 0 hβ)))
      ((KetSpan P).smul_mem _ (ket_mem_ketSpan (hq β 1 hβ)))
theorem preservesSpan_hstWord {n : ℕ} {P : BitAssignment n → Prop}
    (w : List HSTGate) (q : Wire n) (hq : WireIndep P q) :
    PreservesSpan P P (hstWordCircuit w q) := fun β hβ ↦ by
  rw [hstWordCircuit_eval_eq_embedMatrix]
  exact preservesSpan_singleton_matrix q hq (wordMatrix2 w) β hβ
theorem preservesSpan_hstWord_inv {n : ℕ} {P : BitAssignment n → Prop}
    (w : List HSTGate) (q : Wire n) (hq : WireIndep P q) :
    PreservesSpan P P (hstWordCircuit w q).inverse := fun β hβ ↦ by
  rw [Circuit.eval_inverse, show ((hstWordCircuit w q).eval⁻¹).1 =
      (QRegister.singleton q).embedMatrix ((wordMatrix2 w)ᴴ) by
    change star ((hstWordCircuit w q).eval.1) = _
    rw [Matrix.star_eq_conjTranspose, hstWordCircuit_eval_eq_embedMatrix,
      QRegister.embedMatrix_conjTranspose]]
  exact preservesSpan_singleton_matrix q hq ((wordMatrix2 w)ᴴ) β hβ
theorem preservesSpan_cnotIf {n : ℕ} {P : BitAssignment n → Prop}
    (c t : Wire n) (ht : WireIndep P t) :
    PreservesSpan P P (cnotIf c t) := fun β hβ ↦ by
  unfold cnotIf
  split_ifs with hct
  · exact preservesSpan_id β hβ
  · rw [MeasureBranchHadamardSem.ket_CNOT]
    exact ket_mem_ketSpan (ht β _ hβ)
theorem preservesSpan_ctrlProbIf {n : ℕ} {P : BitAssignment n → Prop} (w : List HSTGate)
    (c t : Wire n) (ht : WireIndep P t) : PreservesSpan P P (ctrlProbIf w c t) := by
  unfold ctrlProbIf
  split_ifs with hct
  · exact preservesSpan_id
  · unfold ctrlProbGate
    exact preservesSpan_seq (preservesSpan_hstWord_inv w t ht)
      (preservesSpan_seq (fun β hβ ↦ by
        rw [MeasureBranchHadamardSem.ket_CNOT]
        exact ket_mem_ketSpan (ht β _ hβ))
      (preservesSpan_hstWord w t ht))
theorem preservesSpan_toffIf {n : ℕ} {P : BitAssignment n → Prop}
    (c1 c2 targ : Wire n) (ht : WireIndep P targ) :
    PreservesSpan P P (toffIf c1 c2 targ) := fun β hβ ↦ by
  unfold toffIf
  split_ifs with h12 h1t h2t
  · exact preservesSpan_id β hβ
  · exact preservesSpan_id β hβ
  · exact preservesSpan_id β hβ
  · rw [ket_TOFF]
    exact ket_mem_ketSpan (ht β _ hβ)
theorem preservesSpan_chIf {n : ℕ} {P : BitAssignment n → Prop} (ctrl targ : Wire n)
    (ht : WireIndep P targ) : PreservesSpan P P (chIf ctrl targ) := by
  unfold chIf
  split_ifs with hne
  · exact preservesSpan_id
  · unfold chCircuit
    exact preservesSpan_seq (fun β hβ ↦ by
        rw [cHalfH_eval_eq_singleton, QRegister.embedUnitary_val]
        exact preservesSpan_singleton_matrix targ ht _ β hβ)
      (preservesSpan_seq (fun β hβ ↦ by
          rw [MeasureBranchHadamardSem.ket_CNOT]
          exact ket_mem_ketSpan (ht β _ hβ))
        (fun β hβ ↦ by
          rw [cHalfH_inv_eval_eq_singleton, QRegister.embedUnitary_val]
          exact preservesSpan_singleton_matrix targ ht _ β hβ))
theorem ket_andComputeIf_of_zero {n : ℕ} (c₁ c₂ anc : Wire n)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (β : BitAssignment n) (hanc : β anc = 0) :
    (andComputeIf c₁ c₂ anc).eval.1.mulVec (ket β) =
      ket (Function.update β anc (β c₁ * β c₂)) := by
  rw [andComputeIf, dite_neg' h₁a, dite_neg' h₂a]
  exact ket_andCompute_of_zero c₁ c₂ anc h₁a h₂a β hanc
theorem ket_cnotIf_ne {n : ℕ} (c t : Wire n) (hct : c ≠ t) (β : BitAssignment n) :
    (cnotIf c t).eval.1.mulVec (ket β) = ket (Function.update β t (β t + β c)) := by
  rw [cnotIf, dite_neg' hct, MeasureBranchHadamardSem.ket_CNOT]
private theorem upd_apply {n : ℕ} (γ : BitAssignment n) (a w : Wire n) (v : ZMod 2) :
    Function.update γ a v w = if w = a then v else γ w := by
  rcases eq_or_ne w a with rfl | h
  · rw [ite_eq_left rfl, Function.update_self]
  · rw [ite_eq_right h, Function.update_of_ne h]
private theorem ket_computeEnPos {n : ℕ} (c1 c2 anc : Wire n) (h12 : c1 ≠ c2) (h1a : c1 ≠ anc)
    (h2a : c2 ≠ anc) (β : BitAssignment n) (hanc : β anc = 0) :
    (computeEnPos c1 c2 anc).eval.1.mulVec (ket β) = ket
    (Function.update β anc ((1 - β c1) * (1 - β c2))) := by
  rw [computeEnPos]
  iterate 4 rw [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [MeasureBranchHadamardSem.ket_X, MeasureBranchHadamardSem.ket_X,
    ket_andComputeIf_of_zero c1 c2 anc h1a h2a _
      (by rw [Function.update_of_ne h2a.symm, Function.update_of_ne h1a.symm, hanc]),
    MeasureBranchHadamardSem.ket_X, MeasureBranchHadamardSem.ket_X]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw1 : w = c1
  · subst hw1
    simp only [Function.update_self, Function.update_of_ne h12, Function.update_of_ne h12.symm,
      Function.update_of_ne h1a, (by decide : ∀ x : ZMod 2, x + 1 + 1 = x)]
  · by_cases hw2 : w = c2
    · subst hw2
      simp only [Function.update_self, Function.update_of_ne h12.symm, Function.update_of_ne h2a,
        (by decide : ∀ x : ZMod 2, x + 1 + 1 = x)]
    · by_cases hwa : w = anc
      · subst hwa
        simp only [Function.update_self, Function.update_of_ne hw1, Function.update_of_ne hw2,
          Function.update_of_ne h12, Function.update_of_ne h12.symm,
          (by decide : ∀ x : ZMod 2, 1 - x = x + 1)]
      · simp only [Function.update_of_ne hw1, Function.update_of_ne hw2,
          Function.update_of_ne hwa]
def openMap128 (β : BitAssignment 128) : BitAssignment 128 :=
  let ep : ZMod 2 := (1 - β wCoin1_128) * (1 - β wCoin2_128)
  let es : ZMod 2 := ep * β wCoin0_128
  let ec : ZMod 2 := ep + es
  Function.update
    (Function.update (Function.update β wEnPos_128 ep) wEnS0_128 es) wEnC0_128 ec
theorem ket_cOpen_128 (β : BitAssignment 128) (hp : β wEnPos_128 = 0) (hs : β wEnS0_128 = 0)
    (hc : β wEnC0_128 = 0) : cOpen_128.eval.1.mulVec (ket β) = ket (openMap128 β) := by
  rw [cOpen_128]
  iterate 3 rw [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [ket_computeEnPos wCoin1_128 wCoin2_128 wEnPos_128
      (by decide) (by decide) (by decide) β hp,
    ket_andComputeIf_of_zero wEnPos_128 wCoin0_128 wEnS0_128 (by decide) (by decide) _
      (by rw [Function.update_of_ne (by decide : wEnS0_128 ≠ wEnPos_128), hs]),
    ket_cnotIf_ne wEnPos_128 wEnC0_128 (by decide),
    ket_cnotIf_ne wEnS0_128 wEnC0_128 (by decide)]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : w = wEnPos_128 ∨ w = wEnS0_128 ∨ w = wEnC0_128
  · rcases hw with rfl | rfl | rfl
    all_goals
      dsimp only [openMap128]
      repeat rw [upd_apply]
      repeat first
        | rw [ite_eq_left rfl]
        | rw [ite_eq_right (by decide)]
      try simp only [hc, zero_add]
  · push Not at hw
    rcases hw with ⟨h1, h2, h3⟩
    simp only [openMap128, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
def flags2Map128 (β : BitAssignment 128) : BitAssignment 128 :=
  let eh : ZMod 2 := β wEnPos_128 * β wIsHead_128
  let et : ZMod 2 := β wEnPos_128 + eh
  let est : ZMod 2 := β wEnS0_128 * et
  let ea : ZMod 2 := β wEnPos_128 + β wEnC0_128 * β wIsHead_128
  Function.update
    (Function.update
      (Function.update
        (Function.update β wEnHead_128 eh) wEnTail_128 et) wEnS0Tail_128 est) wEnAnc_128 ea
theorem ket_cFlags2_128 (β : BitAssignment 128) (h119 : β wEnHead_128 = 0)
    (h120 : β wEnTail_128 = 0) (h121 : β wEnC0Head_128 = 0) (h122 : β wEnAnc_128 = 0)
    (h123 : β wEnS0Tail_128 = 0) : cFlags2_128.eval.1.mulVec (ket β) = ket (flags2Map128 β) := by
  rw [cFlags2_128]
  iterate 7 rw [MeasureBranchHadamardSem.eval_seq_mulVec]
  rw [ket_andComputeIf_of_zero wEnPos_128 wIsHead_128 wEnHead_128 (by decide) (by decide) β h119,
    ket_cnotIf_ne wEnPos_128 wEnTail_128 (by decide),
    ket_cnotIf_ne wEnHead_128 wEnTail_128 (by decide),
    ket_andComputeIf_of_zero wEnS0_128 wEnTail_128 wEnS0Tail_128 (by decide) (by decide) _
      (by simp only [Function.update_of_ne (by decide : wEnS0Tail_128 ≠ wEnTail_128),
        Function.update_of_ne (by decide : wEnS0Tail_128 ≠ wEnHead_128), h123]),
    ket_andComputeIf_of_zero wEnC0_128 wIsHead_128 wEnC0Head_128 (by decide) (by decide) _
      (by simp only [Function.update_of_ne (by decide : wEnC0Head_128 ≠ wEnS0Tail_128),
        Function.update_of_ne (by decide : wEnC0Head_128 ≠ wEnTail_128),
        Function.update_of_ne (by decide : wEnC0Head_128 ≠ wEnHead_128), h121]),
    ket_cnotIf_ne wEnPos_128 wEnAnc_128 (by decide),
    ket_cnotIf_ne wEnC0Head_128 wEnAnc_128 (by decide)]
  refine (fun γ (hγ : γ = Function.update (flags2Map128 β) wEnC0Head_128
      (flags2Map128 β wEnC0_128 * flags2Map128 β wIsHead_128)) ↦ show
      (andComputeIf wEnC0_128 wIsHead_128 wEnC0Head_128).inverse.eval.1.mulVec (ket γ) =
        ket (flags2Map128 β) by
    rw [hγ, andComputeIf, dite_neg' (by decide : wEnC0_128 ≠ wEnC0Head_128),
      dite_neg' (by decide : wIsHead_128 ≠ wEnC0Head_128),
      ket_andCompute_inv_of_zero _ _ _ (by decide) (by decide) (flags2Map128 β)
        (by simp only [flags2Map128, h121,
          Function.update_of_ne (by decide : wEnC0Head_128 ≠ wEnAnc_128),
          Function.update_of_ne (by decide : wEnC0Head_128 ≠ wEnS0Tail_128),
          Function.update_of_ne (by decide : wEnC0Head_128 ≠ wEnTail_128),
          Function.update_of_ne (by decide : wEnC0Head_128 ≠ wEnHead_128)])]) _ (funext fun w ↦ ?_)
  by_cases hw : w = wEnHead_128 ∨ w = wEnTail_128 ∨ w = wEnC0Head_128 ∨
      w = wEnAnc_128 ∨ w = wEnS0Tail_128
  · dsimp [wEnTail_128, wEnAnc_128] at h120 h122
    rcases hw with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [flags2Map128, h120, h122, wEnHead_128, wEnTail_128, wEnC0Head_128,
        wEnAnc_128, wEnS0Tail_128, wEnPos_128, wEnS0_128, wEnC0_128, wIsHead_128]
  · push Not at hw
    rcases hw with ⟨h1, h2, h3, h4, h5⟩
    simp only [flags2Map128, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]
theorem head67_add1_lt (i : Fin 6) : 1 + i.val < 67 := by omega
theorem head67_add7_lt (i : Fin 3) : 7 + i.val < 67 := by omega
theorem head67_add10_lt (i : Fin 3) : 10 + i.val < 67 := by omega
noncomputable def head67CleanMap (γ : BitAssignment 67) : BitAssignment 67 :=
  xorRegBits rOut24In67
    (headOutMask24 (γ ⟨0, by decide⟩)
      (fun i : Fin 6 ↦ γ ⟨1 + i.val, head67_add1_lt i⟩)
      (fun i : Fin 3 ↦ γ ⟨7 + i.val, head67_add7_lt i⟩)
      (fun i : Fin 3 ↦ γ ⟨10 + i.val, head67_add10_lt i⟩))
    γ
theorem ket_cLeafHeadCoordXor (β : BitAssignment 128)
    (hscr : ∀ j : Fin 30, β (scr30_128 j) = 0) : cLeafHeadCoordXor.eval.1.mulVec (ket β) = ket
    (writeReg β rHead67_128 (head67CleanMap (fun i : Fin 67 ↦ β (rHead67_128 i)))) := by
  let idx := (basisBitsEquiv 128).symm β
  let γ67 : BitAssignment 67 := fun i ↦ β (rHead67_128 i)
  have hClean67 : ∀ j : Fin 30, γ67 ⟨37 + j.val, by omega⟩ = 0 := fun j ↦ by
    dsimp [γ67]
    rw [show rHead67_128 ⟨37 + j.val, by omega⟩ = scr30_128 j by
      ext
      rw [rHead67_128]
      dsimp
      rw [headMap67In128_val_of_ge37 (by dsimp; omega) (by dsimp; omega)]
      dsimp [scr30_128, PosPostPrep80InnerAmpS3Alt.qreg_block_apply,
        PosPostPrep80InnerAmpS3Alt.qreg_block_wires_apply,
        PosPostPrep80InnerAmpS3Alt.qreg_whole_wires,
        PosPostPrep80InnerAmpS3Alt.emb_trans_apply,
        PosPostPrep80InnerAmpS3Alt.emb_refl_apply,
        PosPostPrep80InnerAmpS3Alt.emb_mk_apply]
      omega, hscr j]
  have hEv : headCoordXorLocal67.eval.1.mulVec (Pi.single (rHead67_128.extractIndex idx) (1 : ℂ)) =
      Pi.single ((basisBitsEquiv 67).symm (head67CleanMap γ67)) (1 : ℂ) := by
    rw [show Pi.single (rHead67_128.extractIndex idx) (1 : ℂ) = ket γ67 by
      rw [ket_eq_single_local]
      refine congrArg (fun idx67 ↦ Pi.single idx67 (1 : ℂ)) ((basisBitsEquiv 67).injective ?_)
      rw [Equiv.apply_symm_apply]
      funext i
      exact (QRegister.basisBits_extractIndex rHead67_128 idx i).trans
        (congrFun ((basisBitsEquiv 128).apply_symm_apply β) (rHead67_128 i))]
    have h1 := evolve_headCoordXorLocal67_of_clean γ67 hClean67
    change headCoordXorLocal67.eval.1.mulVec (ket γ67) = ket (head67CleanMap γ67) at h1
    rw [h1, ket_eq_single_local]
  rw [cLeafHeadCoordXor, lockPosPostVal_eq, Circuit.eval_onRegister,
    QRegister.embedUnitary_val, ket_eq_single_local β,
    rHead67_128.embedMatrix_mulVec_single_factors _ idx, hEv]
  let outBits := writeReg β rHead67_128 (head67CleanMap γ67)
  rw [ket_eq_single_local outBits]
  have hrep : rHead67_128.replaceIndex idx ((basisBitsEquiv 67).symm (head67CleanMap γ67)) =
      (basisBitsEquiv 128).symm outBits := (basisBitsEquiv 128).injective <| by
    rw [Equiv.apply_symm_apply]
    funext w
    change basisBits 128
      (rHead67_128.replaceIndex idx ((basisBitsEquiv 67).symm (head67CleanMap γ67))) w = outBits w
    by_cases hw : ∃ i : Fin 67, rHead67_128 i = w
    · obtain ⟨i, rfl⟩ := hw
      rw [QRegister.basisBits_replaceIndex_apply, basisBits_symm_local]
      exact (writeReg_apply_reg β rHead67_128 (head67CleanMap γ67) i).symm
    · have hnot : w ∉ Set.range rHead67_128.wires := fun ⟨i, hi⟩ ↦ hw ⟨i, hi⟩
      rw [QRegister.basisBits_replaceIndex_of_not_mem rHead67_128 idx _ w hnot]
      change basisBits 128 idx w = outBits w
      rw [basisBits_symm_local]
      exact (writeReg_apply_of_not_mem β rHead67_128 (head67CleanMap γ67) w hnot).symm
  funext y
  set yNew := rHead67_128.replaceIndex idx ((basisBitsEquiv 67).symm (head67CleanMap γ67))
  have hext_eq : ∀ z, rHead67_128.extractIndex z = (rHead67_128.basisSplitEquiv z).1 := fun _ ↦ rfl
  have hsp : rHead67_128.basisSplitEquiv yNew =
      ((basisBitsEquiv 67).symm (head67CleanMap γ67), (rHead67_128.basisSplitEquiv idx).2) := by
    ext1
    · change rHead67_128.extractIndex yNew = _
      refine (basisBitsEquiv 67).injective (funext fun i ↦ ?_)
      change basisBits 67 (rHead67_128.extractIndex yNew) i = _
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_replaceIndex_apply]
    · exact funext fun e ↦ QRegister.basisBits_replaceIndex_of_not_mem rHead67_128 idx _ e.1 e.2
  rw [← hrep]
  by_cases hy : y = yNew
  · subst hy
    simp only [QRegister.tensorState, hext_eq, hsp, Pi.single_eq_same, mul_one]
  · simp only [QRegister.tensorState, hext_eq, Pi.single_eq_of_ne hy]
    by_cases h1 : (rHead67_128.basisSplitEquiv y).1 =
        (basisBitsEquiv 67).symm (head67CleanMap γ67)
    · have h2 : (rHead67_128.basisSplitEquiv y).2 ≠ (rHead67_128.basisSplitEquiv idx).2 :=
        fun heq2 ↦ hy <| rHead67_128.basisSplitEquiv.injective <| by
          rw [hsp]
          exact Prod.ext h1 heq2
      rw [Pi.single_eq_of_ne h2, mul_zero]
    · rw [Pi.single_eq_of_ne h1, zero_mul]
def OpenInv128 (β : BitAssignment 128) : Prop := β wEnPos_128 = (1 - β wCoin1_128) *
    (1 - β wCoin2_128) ∧ β wEnS0_128 = β wEnPos_128 * β wCoin0_128 ∧ β wEnC0_128 = β
    wEnPos_128 + β wEnS0_128 ∧ (∀ j : Fin 30, β (scr30_128 j) = 0) ∧ β wEnHead_128 = 0 ∧ β
    wEnTail_128 = 0 ∧ β wEnC0Head_128 = 0 ∧ β wEnAnc_128 = 0 ∧ β wEnS0Tail_128 = 0 ∧ β
    wPopT01_128 = 0 ∧ β wPopMaj_128 = 0 ∧ β wPopPar_128 = 0 ∧ β wBrTop_128 = 0
def FlagsInv128 (β : BitAssignment 128) : Prop := β wEnPos_128 = (1 - β wCoin1_128) *
    (1 - β wCoin2_128) ∧ β wEnS0_128 = β wEnPos_128 * β wCoin0_128 ∧ β wEnC0_128 = β
    wEnPos_128 + β wEnS0_128 ∧ β wEnHead_128 = β wEnPos_128 * β wIsHead_128 ∧ β wEnTail_128 =
    β wEnPos_128 + β wEnHead_128 ∧ β wEnS0Tail_128 = β wEnS0_128 * β wEnTail_128 ∧ β
    wEnAnc_128 = β wEnPos_128 + β wEnC0_128 * β wIsHead_128 ∧
    (∀ j : Fin 30, β (scr30_128 j) = 0) ∧ β wEnC0Head_128 = 0 ∧ β wPopT01_128 = 0 ∧ β
    wPopMaj_128 = 0 ∧ β wPopPar_128 = 0 ∧ β wBrTop_128 = 0
theorem scr30_128_val (j : Fin 30) : (scr30_128 j).val = 86 + j.val := by
  fin_cases j <;> rfl
theorem scr20_128_val (i : Fin 20) : (scr20_128 i).val = 86 + i.val := by
  fin_cases i <;> rfl
theorem rK_128_val (i : Fin 6) : (rK_128 i).val = 69 + i.val := by
  fin_cases i <;> rfl
theorem openInv_indep_payload {w : Wire 128}
    (hw : 6 ≤ w.val ∧ w.val < 86) : WireIndep OpenInv128 w := fun β b hβ ↦ by
  have hEq : ∀ u : Wire 128, (u.val < 6 ∨ 86 ≤ u.val) →
      Function.update β w b u = β u := fun u hu ↦
    Function.update_of_ne (fun h ↦ by have := congrArg Fin.val h; omega) _ _
  have hscr : ∀ j : Fin 30, Function.update β w b (scr30_128 j) = β (scr30_128 j) := fun j ↦
    hEq _ (Or.inr (by rw [scr30_128_val]; omega))
  unfold OpenInv128 at hβ ⊢
  simpa only [hEq wCoin0_128 (Or.inl (by decide)), hEq wCoin1_128 (Or.inl (by decide)),
    hEq wCoin2_128 (Or.inl (by decide)), hEq wEnPos_128 (Or.inr (by decide)),
    hEq wEnS0_128 (Or.inr (by decide)), hEq wEnC0_128 (Or.inr (by decide)),
    hEq wEnHead_128 (Or.inr (by decide)), hEq wEnTail_128 (Or.inr (by decide)),
    hEq wEnC0Head_128 (Or.inr (by decide)), hEq wEnAnc_128 (Or.inr (by decide)),
    hEq wEnS0Tail_128 (Or.inr (by decide)), hEq wPopT01_128 (Or.inr (by decide)),
    hEq wPopMaj_128 (Or.inr (by decide)), hEq wPopPar_128 (Or.inr (by decide)),
    hEq wBrTop_128 (Or.inr (by decide)), hscr] using hβ
def flagsCore_of_flagsInv (β : BitAssignment 128) : Prop := β wEnPos_128 = (1 - β wCoin1_128)
    * (1 - β wCoin2_128) ∧ β wEnS0_128 = β wEnPos_128 * β wCoin0_128 ∧ β wEnC0_128 = β
    wEnPos_128 + β wEnS0_128 ∧ β wEnHead_128 = β wEnPos_128 * β wIsHead_128 ∧ β wEnTail_128 =
    β wEnPos_128 + β wEnHead_128 ∧ β wEnS0Tail_128 = β wEnS0_128 * β wEnTail_128 ∧ β
    wEnAnc_128 = β wEnPos_128 + β wEnC0_128 * β wIsHead_128 ∧ β wEnC0Head_128 = 0 ∧ β
    wPopT01_128 = 0 ∧ β wPopMaj_128 = 0 ∧ β wPopPar_128 = 0 ∧ β wBrTop_128 = 0
theorem flagsInv_iff (β : BitAssignment 128) :
    FlagsInv128 β ↔ (flagsCore_of_flagsInv β ∧ ∀ j : Fin 30, β (scr30_128 j) = 0) := by
  unfold FlagsInv128 flagsCore_of_flagsInv
  tauto
private theorem flagsCore_congr {γ β : BitAssignment 128}
    (h : ∀ u : Wire 128, (u.val < 6 ∨ u.val = 36 ∨ 86 ≤ u.val) → γ u = β u)
    (hc : flagsCore_of_flagsInv β) : flagsCore_of_flagsInv γ := by
  unfold flagsCore_of_flagsInv at hc ⊢
  rwa [h wCoin0_128 (Or.inl (by decide)), h wCoin1_128 (Or.inl (by decide)),
    h wCoin2_128 (Or.inl (by decide)), h wIsHead_128 (Or.inr (Or.inl rfl)),
    h wEnPos_128 (Or.inr (Or.inr (by decide))), h wEnS0_128 (Or.inr (Or.inr (by decide))),
    h wEnC0_128 (Or.inr (Or.inr (by decide))), h wEnHead_128 (Or.inr (Or.inr (by decide))),
    h wEnTail_128 (Or.inr (Or.inr (by decide))), h wEnS0Tail_128 (Or.inr (Or.inr (by decide))),
    h wEnAnc_128 (Or.inr (Or.inr (by decide))), h wEnC0Head_128 (Or.inr (Or.inr (by decide))),
    h wPopT01_128 (Or.inr (Or.inr (by decide))), h wPopMaj_128 (Or.inr (Or.inr (by decide))),
    h wPopPar_128 (Or.inr (Or.inr (by decide))), h wBrTop_128 (Or.inr (Or.inr (by decide)))]
theorem flagsInv_indep_payload_not36 {w : Wire 128}
    (hw : (6 ≤ w.val ∧ w.val < 86 ∧ w.val ≠ 36)) : WireIndep FlagsInv128 w := fun β b hβ ↦ by
  obtain ⟨hc, hs⟩ := (flagsInv_iff β).mp hβ
  have hEq : ∀ u : Wire 128, (u.val < 6 ∨ u.val = 36 ∨ 86 ≤ u.val) →
      Function.update β w b u = β u := fun u hu ↦
    Function.update_of_ne (fun h ↦ by have := congrArg Fin.val h; omega) _ _
  exact (flagsInv_iff _).mpr ⟨flagsCore_congr hEq hc, fun j ↦
    (hEq _ (Or.inr (Or.inr (by rw [scr30_128_val]; omega)))).trans (hs j)⟩
theorem preservesSpan_cLeafHeadCoordXor :
    PreservesSpan FlagsInv128 FlagsInv128 cLeafHeadCoordXor := fun β hβ ↦ by
  obtain ⟨hc, hs⟩ := (flagsInv_iff β).mp hβ
  rw [ket_cLeafHeadCoordXor β hs]
  let γ67 : BitAssignment 67 := fun i ↦ β (rHead67_128 i)
  let outBits := writeReg β rHead67_128 (head67CleanMap γ67)
  have hUnchanged : ∀ w : Wire 128,
      (w.val < 6 ∨ w.val = 36 ∨ 86 ≤ w.val) → outBits w = β w := fun w hw ↦ by
    by_cases hmem : ∃ i : Fin 67, rHead67_128 i = w
    · obtain ⟨i, rfl⟩ := hmem
      dsimp [outBits]
      rw [writeReg_apply_reg, head67CleanMap]
      refine xorRegBits_apply_of_not_mem _ _ _ fun hIn ↦ ?_
      rw [QRegister.mem_image] at hIn
      obtain ⟨j, rfl⟩ := hIn
      have hbnd : (rOut24In67 j).val ≠ 0 ∧ (rOut24In67 j).val < 37 := by
        dsimp [rOut24In67, PosPostPrep80InnerAmpS3Alt.qreg_block_apply,
          PosPostPrep80InnerAmpS3Alt.qreg_block_wires_apply,
          PosPostPrep80InnerAmpS3Alt.qreg_whole_wires,
          PosPostPrep80InnerAmpS3Alt.emb_trans_apply,
          PosPostPrep80InnerAmpS3Alt.emb_refl_apply,
          PosPostPrep80InnerAmpS3Alt.emb_mk_apply]
        omega
      have hv : (rHead67_128 (rOut24In67 j)).val =
          6 + (rHeadAct37In80 ⟨(rOut24In67 j).val, hbnd.2⟩).val :=
        headMap67In128_val_of_lt37 hbnd.1 hbnd.2
      have hlt80 := (rHeadAct37In80 ⟨(rOut24In67 j).val, hbnd.2⟩).isLt
      have hne30 : (rHeadAct37In80 ⟨(rOut24In67 j).val, hbnd.2⟩).val ≠ 30 := fun h30 ↦ by
        have hfin := congrArg Fin.val (rHeadAct37In80.wires.injective
          (Fin.ext (h30.trans (rfl : (rHeadAct37In80 ⟨0, by decide⟩).val = 30).symm)))
        dsimp [rOut24In67, PosPostPrep80InnerAmpS3Alt.qreg_block_apply,
          PosPostPrep80InnerAmpS3Alt.qreg_block_wires_apply,
          PosPostPrep80InnerAmpS3Alt.qreg_whole_wires,
          PosPostPrep80InnerAmpS3Alt.emb_trans_apply,
          PosPostPrep80InnerAmpS3Alt.emb_refl_apply,
          PosPostPrep80InnerAmpS3Alt.emb_mk_apply] at hfin
        omega
      omega
    · exact writeReg_apply_of_not_mem β rHead67_128 (head67CleanMap γ67) w
        fun ⟨i, hi⟩ ↦ hmem ⟨i, hi⟩
  exact ket_mem_ketSpan ((flagsInv_iff outBits).mpr ⟨flagsCore_congr hUnchanged hc, fun j ↦
    (hUnchanged _ (Or.inr (Or.inr (by rw [scr30_128_val]; omega)))).trans (hs j)⟩)
private theorem preservesSpan_cPmSplit {n : ℕ} {P : BitAssignment n → Prop}
    (L : ℕ) (branches : List (Wire n × List (Fin 4))) (flips : List (Wire n))
    (wPar t : Wire n) (hdisj : PmSplitDisj (branches.map Prod.fst) flips wPar t)
    (ht : WireIndep P t) (hwPar : ∀ β, P β → β wPar = 0) :
    PreservesSpan P P (cPmSplit L branches flips wPar t) := fun β hβ ↦ by
  rw [cPmSplit_mulVec_ket_embed L branches flips wPar t hdisj β (hwPar β hβ)]
  exact preservesSpan_singleton_matrix t ht (pmSplitMat L branches flips β) β hβ
theorem preservesSpan_cIsHeadPm : PreservesSpan OpenInv128 OpenInv128 cIsHeadPm_128 := by
  rw [cIsHeadPm_128, lockPosPostVal_eq, cIsHeadPmRaw_128]
  refine preservesSpan_seq (preservesSpan_cPmSplit 44 isHeadPmBranches []
      (scr30_128 ⟨0, by decide⟩) wIsHead_128 ?_ (openInv_indep_payload (by decide))
      (fun _ ⟨_, _, _, hs, _⟩ ↦ hs ⟨0, by decide⟩))
    (preservesSpan_seq (preservesSpan_cnotIf wEnC0_128 wIsHead_128
      (openInv_indep_payload (by decide)))
      (preservesSpan_cnotIf wEnS0_128 wIsHead_128 (openInv_indep_payload (by decide))))
  rw [show isHeadPmBranches.map Prod.fst = [wEnC0_128, wEnS0_128] from rfl]
  decide
def forkMap {n : ℕ} (u t uRight : Wire n) (β : BitAssignment n) : BitAssignment n :=
  Function.update (Function.update β uRight (β u * β t)) u (β u + β u * β t)
theorem ket_cUnaryFork {n : ℕ} (u t uRight : Wire n) (_hut : u ≠ t) (huR : u ≠ uRight)
    (htR : t ≠ uRight) (β : BitAssignment n) (hR : β uRight = 0) :
    (cUnaryFork u t uRight).eval.1.mulVec (ket β) = ket (forkMap u t uRight β) := by
  rw[cUnaryFork, MeasureBranchHadamardSem.eval_seq_mulVec,
      ket_andComputeIf_of_zero u t uRight huR htR β hR, ket_cnotIf_ne uRight u huR.symm,
      Function.update_self, Function.update_of_ne huR]
  rfl
theorem hsSplitDisj_0 : PmSplitDisj (hsBranches_0.map Prod.fst) hsFlips_0 wPmPar_128 (rK_128 ⟨5,
    by decide⟩) := by
  have hmap : hsBranches_0.map Prod.fst = [scr20_128 ⟨0, by decide⟩] := rfl
  rw [hmap]; decide
theorem hsSplitDisj_1 : PmSplitDisj (hsBranches_1.map Prod.fst) hsFlips_1 wPmPar_128 (rK_128 ⟨4,
    by decide⟩) := by
  have hmap : hsBranches_1.map Prod.fst = [scr20_128 ⟨0, by decide⟩] := rfl
  rw [hmap]; decide
theorem hsSplitDisj_2 : PmSplitDisj (hsBranches_2.map Prod.fst) hsFlips_2 wPmPar_128 (rK_128 ⟨3,
    by decide⟩) := by
  have hmap : hsBranches_2.map Prod.fst = [scr20_128 ⟨0, by decide⟩, scr20_128 ⟨2, by decide⟩,
    scr20_128 ⟨1, by decide⟩] := rfl
  rw [hmap]; decide
theorem hsSplitDisj_3 : PmSplitDisj (hsBranches_3.map Prod.fst) hsFlips_3 wPmPar_128 (rK_128 ⟨2,
    by decide⟩) := by
  have hmap : hsBranches_3.map Prod.fst = [scr20_128 ⟨0, by decide⟩, scr20_128 ⟨3, by decide⟩,
    scr20_128 ⟨2, by decide⟩, scr20_128 ⟨4, by decide⟩, scr20_128 ⟨1, by decide⟩] := rfl
  rw [hmap]; decide
theorem hsSplitDisj_4 : PmSplitDisj (hsBranches_4.map Prod.fst) hsFlips_4 wPmPar_128 (rK_128 ⟨1,
    by decide⟩) := by
  have hmap : hsBranches_4.map Prod.fst = [scr20_128 ⟨0, by decide⟩, scr20_128 ⟨6, by decide⟩,
    scr20_128 ⟨3, by decide⟩, scr20_128 ⟨7, by decide⟩, scr20_128 ⟨2, by decide⟩, scr20_128 ⟨8,
    by decide⟩, scr20_128 ⟨4, by decide⟩, scr20_128 ⟨9, by decide⟩, scr20_128 ⟨10, by decide⟩] :=
    rfl
  rw [hmap]; decide
theorem hsSplitDisj_5 : PmSplitDisj (hsBranches_5.map Prod.fst) hsFlips_5 wPmPar_128 (rK_128 ⟨0,
    by decide⟩) := by
  have hmap : hsBranches_5.map Prod.fst = [scr20_128 ⟨0, by decide⟩, scr20_128 ⟨11, by decide⟩,
    scr20_128 ⟨6, by decide⟩, scr20_128 ⟨12, by decide⟩, scr20_128 ⟨3, by decide⟩, scr20_128 ⟨13,
    by decide⟩, scr20_128 ⟨7, by decide⟩, scr20_128 ⟨14, by decide⟩, scr20_128 ⟨2, by decide⟩,
    scr20_128 ⟨15, by decide⟩, scr20_128 ⟨8, by decide⟩, scr20_128 ⟨16, by decide⟩, scr20_128 ⟨4,
    by decide⟩, scr20_128 ⟨17, by decide⟩, scr20_128 ⟨9, by decide⟩, scr20_128 ⟨18, by decide⟩,
    scr20_128 ⟨10, by decide⟩, scr20_128 ⟨19, by decide⟩, scr20_128 ⟨5, by decide⟩] := rfl
  rw [hmap]; decide
theorem basisBits_zero_part4 (m : ℕ) (i : Fin m) : basisBits m 0 i = 0 := by
  rw [basisBits_eq_div_mod]; simp
theorem nat_beq_false {a b : ℕ} (h : a ≠ b) : (a == b) = false := beq_eq_false_iff_ne.mpr h
theorem ditePosLocalSec4 {P : Prop} [inst : Decidable P] {α : Sort*}
    {t : P → α} {e : ¬P → α} (h : P) : dite P t e = t h := dite_eq_left h
theorem diteNegLocalSec4 {P : Prop} [inst : Decidable P] {α : Sort*}
    {t : P → α} {e : ¬P → α} (h : ¬P) : dite P t e = e h := dite_eq_right h
theorem itePosLocalSec4 {P : Prop} [inst : Decidable P] {α : Sort*}
    {t e : α} (h : P) : ite P t e = t := ite_eq_left h
theorem iteNegLocalSec4 {P : Prop} [inst : Decidable P] {α : Sort*}
    {t e : α} (h : ¬P) : ite P t e = e := ite_eq_right h
theorem basisBits_eq_z2BitOfNat {m : ℕ} (j : Fin (2 ^ m)) (i : Fin m) :
    basisBits m j i = z2BitOfNat j.val i.val := by
  rw [basisBits_eq_div_mod]
  unfold z2BitOfNat
  have hlt : j.val / 2 ^ i.val % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases (by omega : j.val / 2 ^ i.val % 2 = 0 ∨ j.val / 2 ^ i.val % 2 = 1) with h0 | h1
  · simp [h0]
  · simp [h1]
theorem bitsVal_basisBits : ∀ {m : ℕ} (j : Fin (2 ^ m)),
    Pos24HeadCoordXor80.bitsVal (basisBits m j) = j.val
  | 0, j => by
      rw [show j.val = 0 from Nat.lt_one_iff.mp j.isLt]
      simp [Pos24HeadCoordXor80.bitsVal]
  | k + 1, j => by
      dsimp only [Pos24HeadCoordXor80.bitsVal]
      rw [Fin.sum_univ_succ]
      have h0 : (basisBits (k + 1) j 0).val = j.val % 2 := by
        simp [basisBits_eq_div_mod, ZMod.val_natCast]
      let jDiv : Fin (2 ^ k) :=
        ⟨j.val / 2, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq j.isLt (pow_succ' 2 k))⟩
      have hsucc (i : Fin k) : basisBits (k + 1) j i.succ = basisBits k jDiv i := by
        rw [basisBits_eq_div_mod, basisBits_eq_div_mod]
        dsimp only [Fin.val_succ, jDiv]
        rw [pow_succ' 2 i.val, ← Nat.div_div_eq_div_mul]
      have htail : (∑ i : Fin k, (basisBits (k + 1) j i.succ).val * 2 ^ i.succ.val) =
          2 * Pos24HeadCoordXor80.bitsVal (basisBits k jDiv) := by
        dsimp only [Pos24HeadCoordXor80.bitsVal]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hsucc i, Fin.val_succ, pow_succ']
        ring
      rw [Fin.val_zero, pow_zero, mul_one, h0, htail, bitsVal_basisBits jDiv]
      exact Nat.mod_add_div j.val 2
theorem basisBits_bitsVal {m : ℕ} (γ : BitAssignment m) :
    basisBits m ⟨Pos24HeadCoordXor80.bitsVal γ, bitsVal_lt_two_pow_local γ⟩ = γ := by
  let j : Fin (2 ^ m) := (basisBitsEquiv m).symm γ
  have hj : basisBits m j = γ := (basisBitsEquiv m).apply_symm_apply γ
  have heq : (⟨Pos24HeadCoordXor80.bitsVal γ, bitsVal_lt_two_pow_local γ⟩ : Fin (2 ^ m)) = j :=
    Fin.ext ((congrArg Pos24HeadCoordXor80.bitsVal hj.symm).trans (bitsVal_basisBits j))
  rw [heq, hj]
theorem z2BitOfNat_xor3 (a b : Fin 8) (i : Fin 3) :
    z2BitOfNat (Nat.xor a.val b.val) i.val = basisBits 3 a i + basisBits 3 b i := by
  fin_cases a <;> fin_cases b <;> fin_cases i <;> decide
open Classical in
noncomputable def finishXorMap128 (isMerged218 : Bool) (β : BitAssignment 128) : BitAssignment 128
    :=
  let cDp : ZMod 2 := if isMerged218 then β wEnS0Tail_128 else β wEnTail_128
  let cS0 : ZMod 2 := β wEnS0_128
  let d0 := β (rB1_128 ⟨0, by decide⟩)
  let d1 := β (rB1_128 ⟨1, by decide⟩)
  let d2 := β (rB1_128 ⟨2, by decide⟩)
  let b0 := β (rB0_128 ⟨0, by decide⟩)
  let b1 := β (rB0_128 ⟨1, by decide⟩)
  let b2 := β (rB0_128 ⟨2, by decide⟩)
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update β
              (wP80_128 ⟨75, by decide⟩) (β (wP80_128 ⟨75, by decide⟩) + cDp * d0))
            (wP80_128 ⟨76, by decide⟩) (β (wP80_128 ⟨76, by decide⟩) + cDp * d1))
          (wP80_128 ⟨77, by decide⟩) (β (wP80_128 ⟨77, by decide⟩) + cDp * d2))
        (rB1_128 ⟨0, by decide⟩) (d0 + cS0 * b0))
      (rB1_128 ⟨1, by decide⟩) (d1 + cS0 * b1))
    (rB1_128 ⟨2, by decide⟩) (d2 + cS0 * b2)
theorem unHadamardList_mulVec_ket_zero {n : ℕ} (ctrl : Wire n) :
    ∀ (qs : List (Wire n)) (β : BitAssignment n),
      (∀ q ∈ qs, ctrl ≠ q) → β ctrl = 0 →
      (unHadamardList ctrl qs).eval.1.mulVec (ket β) = ket β
  | [], _, _, _ => by simp [unHadamardList]
  | q :: qs, β, hne, hc => by
      rw [unHadamardList, MeasureBranchHadamardSem.eval_seq_mulVec,
        unHadamardList_mulVec_ket_zero ctrl qs β (fun r hr ↦ hne r (List.mem_cons_of_mem q hr)) hc,
        chIf, dite_neg' (hne q List.mem_cons_self)]
      exact chCircuit_mulVec_ket_ctrl_zero ctrl q (hne q List.mem_cons_self) β hc
theorem headOutMask24_of_zero_en_part4 (γK : BitAssignment 6) (γPid : BitAssignment 3)
    (γSm : BitAssignment 3) : ∀ j : Fin 24, headOutMask24 0 γK γPid γSm j = 0 := by
  intro j
  fin_cases j <;> simp
theorem cLeafHeadCoordXor_mulVec_ket_zero (β : BitAssignment 128)
    (hhead : β wEnHead_128 = 0) (hscr : ∀ j : Fin 30, β (scr30_128 j) = 0) :
    cLeafHeadCoordXor.eval.1.mulVec (ket β) = ket β := by
  rw [ket_cLeafHeadCoordXor β hscr]
  refine congrArg ket (writeReg_self β rHead67_128 fun i ↦ ?_)
  unfold head67CleanMap
  have h0z : β (rHead67_128 ⟨0, by decide⟩) = 0 := hhead
  by_cases hmem : i ∈ rOut24In67.image
  · rw [QRegister.mem_image] at hmem
    obtain ⟨j, rfl⟩ := hmem
    rw [xorRegBits_apply_reg]
    dsimp only
    rw [h0z, headOutMask24_of_zero_en_part4 _ _ _ j, add_zero]
  · exact xorRegBits_apply_of_not_mem _ _ _ hmem
theorem alpha0_nil_eq_zero : alpha0 [] = 0 := by
  have h := norm_sq_alpha0_add_alpha1 []
  rw [alpha1_nil_eq_one, norm_one, one_pow] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by linarith))
theorem alpha1_singleton_H_eq_zero : alpha1 [.H] = 0 := by
  have h := norm_sq_alpha0_add_alpha1 [.H]
  rw [alpha0_singleton_H, norm_one, one_pow] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by linarith))
theorem isHeadPmDisj : PmSplitDisj (isHeadPmBranches.map Prod.fst) []
    (scr30_128 ⟨0, by decide⟩) wIsHead_128 := by
  dsimp only [isHeadPmBranches, List.map]
  decide
theorem cIsHeadPm_mulVec_ket_zero (β : BitAssignment 128)
    (hEC : β wEnC0_128 = 0) (hES : β wEnS0_128 = 0)
    (hScr0 : β (scr30_128 ⟨0, by decide⟩) = 0) :
    cIsHeadPm_128.eval.1.mulVec (ket β) = ket β := by
  have hbr : isHeadPmBranches.filter (fun p => β p.1 == 1) = [] := by
    simp only [isHeadPmBranches, List.filter, hEC, hES]
    rfl
  rw [cIsHeadPm_128, lockPosPostVal_eq, cIsHeadPmRaw_128,
    MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.eval_seq_mulVec,
    cPmSplit_mulVec_ket_zero 44 isHeadPmBranches [] (scr30_128 ⟨0, by decide⟩) wIsHead_128
      isHeadPmDisj β hScr0 hbr rfl,
    ket_cnotIf_ne _ _ (by decide), hEC, add_zero, upd_eq_self β wIsHead_128 rfl,
    ket_cnotIf_ne _ _ (by decide), hES, add_zero, upd_eq_self β wIsHead_128 rfl]
theorem cIsHeadPm_mulVec_ket_active (s0 : Bool) (β : BitAssignment 128)
    (hES : β wEnS0_128 = if s0 then 1 else 0)
    (hEC : β wEnC0_128 = if s0 then 0 else 1)
    (hIH0 : β wIsHead_128 = 0)
    (hScr0 : β (scr30_128 ⟨0, by decide⟩) = 0) :
    cIsHeadPm_128.eval.1.mulVec (ket β) =
      alpha0 (if s0 then isHeadS0TrueWord else isHeadS0FalseWord) •
        ket (Function.update β wIsHead_128 1) +
      alpha1 (if s0 then isHeadS0TrueWord else isHeadS0FalseWord) • ket β := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rw [cIsHeadPm_128, lockPosPostVal_eq, cIsHeadPmRaw_128,
    MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.eval_seq_mulVec]
  cases s0
  · simp only [Bool.false_eq_true, ↓reduceIte] at hES hEC ⊢
    have hbr : isHeadPmBranches.filter (fun p => β p.1 == 1) =
        [(wEnC0_128, isHeadS0FalseOdds)] := by
      simp only [isHeadPmBranches, List.filter, hEC, hES]
      rfl
    rw [cPmSplit_mulVec_ket_onehot 44 isHeadPmBranches [] (scr30_128 ⟨0, by decide⟩)
        wIsHead_128 wEnC0_128 isHeadS0FalseOdds isHeadPmDisj length_hstPoolOdds_0
        β hScr0 hIH0 hbr rfl,
      oddsToHst_hstPoolOdds_0,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      ket_cnotIf_ne _ _ (by decide), ket_cnotIf_ne _ _ (by decide),
      hIH0, hEC, zero_add, Function.update_self, Function.update_of_ne (by decide), hEC, h11,
      Function.update_idem, upd_eq_self β wIsHead_128 hIH0,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      ket_cnotIf_ne _ _ (by decide), ket_cnotIf_ne _ _ (by decide),
      Function.update_self, Function.update_of_ne (by decide), hIH0, hES, add_zero, add_zero,
      Function.update_idem, upd_eq_self β wIsHead_128 hIH0]
  · simp only [↓reduceIte] at hES hEC ⊢
    have hbr : isHeadPmBranches.filter (fun p => β p.1 == 1) =
        [(wEnS0_128, isHeadS0TrueOdds)] := by
      simp only [isHeadPmBranches, List.filter, hEC, hES]
      rfl
    rw [cPmSplit_mulVec_ket_onehot 44 isHeadPmBranches [] (scr30_128 ⟨0, by decide⟩)
        wIsHead_128 wEnS0_128 isHeadS0TrueOdds isHeadPmDisj length_hstPoolOdds_1
        β hScr0 hIH0 hbr rfl,
      oddsToHst_hstPoolOdds_1,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      ket_cnotIf_ne _ _ (by decide), ket_cnotIf_ne _ _ (by decide),
      hIH0, hEC, add_zero, upd_eq_self β wIsHead_128 hIH0,
      Function.update_self, Function.update_of_ne (by decide), hEC, add_zero, Function.update_idem,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      ket_cnotIf_ne _ _ (by decide), ket_cnotIf_ne _ _ (by decide),
      hIH0, hES, zero_add, Function.update_self, Function.update_of_ne (by decide), hES, h11,
      Function.update_idem, upd_eq_self β wIsHead_128 hIH0]
def AllScr21Zero (β : BitAssignment 128) : Prop :=
  ∀ j : Fin 30, j.val ≤ 20 → β (scr30_128 j) = 0
def OneHotScr21 (idx : ℕ) (β : BitAssignment 128) : Prop :=
  ∀ j : Fin 30, j.val ≤ 20 → β (scr30_128 j) = if j.val = idx then 1 else 0
theorem filter_scr20_branches_zero {α : Type*} (xs : List (Fin 20 × α))
    (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    (xs.map (fun p => (scr20_128 p.1, p.2))).filter (fun q => β q.1 == 1) = [] := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    have h0 : β (scr20_128 p.1) = 0 := hZ ⟨p.1.val, by omega⟩ p.1.isLt.le
    rw [List.map, List.filter, h0]
    exact ih
theorem filter_scr20_flips_zero (xs : List (Fin 20)) (β : BitAssignment 128)
    (hZ : AllScr21Zero β) : (xs.map scr20_128).filter (fun q => β q == 1) = [] := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    have h0 : β (scr20_128 i) = 0 := hZ ⟨i.val, by omega⟩ i.isLt.le
    rw [List.map, List.filter, h0]
    exact ih
theorem scr20_beq_one_of_oneHot (idx i : Fin 20) (β : BitAssignment 128)
    (hOH : OneHotScr21 idx.val β) : (β (scr20_128 i) == 1) = (i == idx) := by
  have hval : β (scr20_128 i) = if i.val = idx.val then 1 else 0 :=
    hOH ⟨i.val, by omega⟩ i.isLt.le
  by_cases heq : i = idx
  · subst heq
    simp [hval]
  · rw [hval, ite_eq_right (fun h => heq (Fin.ext h)), beq_false_of_ne heq]
    rfl
theorem filter_scr20_branches {α : Type*} (idx : Fin 20) (xs : List (Fin 20 × α))
    (β : BitAssignment 128) (hOH : OneHotScr21 idx.val β) :
    (xs.map (fun p => (scr20_128 p.1, p.2))).filter (fun q => β q.1 == 1) =
      (xs.filter (fun p => p.1 == idx)).map (fun p => (scr20_128 p.1, p.2)) := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rw [List.map, List.filter, scr20_beq_one_of_oneHot idx p.1 β hOH, List.filter]
    cases (p.1 == idx) <;> simp [ih]
theorem filter_scr20_flips (idx : Fin 20) (xs : List (Fin 20)) (β : BitAssignment 128)
    (hOH : OneHotScr21 idx.val β) : (xs.map scr20_128).filter (fun q => β q == 1) =
    (xs.filter (fun i => i == idx)).map scr20_128 := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [List.map, List.filter, scr20_beq_one_of_oneHot idx i β hOH, List.filter]
    cases (i == idx) <;> simp [ih]
theorem cUnaryFork_ket_zero_left {n : ℕ} (u t uRight : Wire n) (hut : u ≠ t)
    (huR : u ≠ uRight) (htR : t ≠ uRight) (β : BitAssignment n) (hu : β u = 0)
    (hR : β uRight = 0) : (cUnaryFork u t uRight).eval.1.mulVec (ket β) = ket β := by
  rw [ket_cUnaryFork u t uRight hut huR htR β hR]
  dsimp only [forkMap]
  rw [hu, zero_mul, add_zero, upd_eq_self β uRight hR, upd_eq_self β u hu]
private theorem scr20_ne_of_lt86 (i : Fin 20) {w : Wire 128} (hw : w.val < 86) :
    scr20_128 i ≠ w := fun h ↦ by
  have hv := (scr20_128_val i).symm.trans (congrArg Fin.val h)
  omega
private theorem scr20_ne_scr20 {i j : Fin 20} (hij : i ≠ j) :
    scr20_128 i ≠ scr20_128 j := fun h ↦ hij (Fin.ext (by
  have hv := (scr20_128_val i).symm.trans ((congrArg Fin.val h).trans (scr20_128_val j))
  omega))
theorem withUnaryFork_ket_zero (i_u i_R : Fin 20) (t : Wire 128) (body : Circuit 128)
    (huR : i_u ≠ i_R) (ht : t.val < 86) (β : BitAssignment 128) (hZ : AllScr21Zero β)
    (hbody : body.eval.1.mulVec (ket β) = ket β) :
    (withUnaryFork (scr20_128 i_u) t (scr20_128 i_R) body).eval.1.mulVec (ket β) = ket β := by
  have hfwd := cUnaryFork_ket_zero_left _ t _ (scr20_ne_of_lt86 i_u ht)
    (scr20_ne_scr20 huR) (scr20_ne_of_lt86 i_R ht).symm β
    (hZ ⟨i_u.val, by omega⟩ i_u.isLt.le) (hZ ⟨i_R.val, by omega⟩ i_R.isLt.le)
  rw [withUnaryFork, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec, hfwd, hbody, inv_mulVec_ket_of_fwd _ β β hfwd]
theorem cHsDepth5_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsDepth5.eval.1.mulVec (ket β) = ket β := by
  rw [cHsDepth5, cHsSplit_5]
  exact cPmSplit_mulVec_ket_zero 47 hsBranches_5 hsFlips_5 wPmPar_128 (rK_128 ⟨0, by decide⟩)
    hsSplitDisj_5 β (hZ ⟨20, by decide⟩ (le_refl 20))
    (filter_scr20_branches_zero hsBranchesIdx_5 β hZ)
    (filter_scr20_flips_zero hsFlipsIdx_5 β hZ)
theorem cHsFork_4_9_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_9.eval.1.mulVec (ket β) = ket β := cHsDepth5_ket_zero β hZ
theorem cHsFork_4_8_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_8.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨10, by decide⟩ ⟨19, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_9 (by
  decide) (by decide) β hZ (cHsFork_4_9_ket_zero β hZ)
theorem cHsFork_4_7_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_7.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨9, by decide⟩ ⟨18, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_8 (by
  decide) (by decide) β hZ (cHsFork_4_8_ket_zero β hZ)
theorem cHsFork_4_6_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_6.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨4, by decide⟩ ⟨17, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_7 (by
  decide) (by decide) β hZ (cHsFork_4_7_ket_zero β hZ)
theorem cHsFork_4_5_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_5.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨8, by decide⟩ ⟨16, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_6 (by
  decide) (by decide) β hZ (cHsFork_4_6_ket_zero β hZ)
theorem cHsFork_4_4_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_4.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨2, by decide⟩ ⟨15, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_5 (by
  decide) (by decide) β hZ (cHsFork_4_5_ket_zero β hZ)
theorem cHsFork_4_3_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_3.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨7, by decide⟩ ⟨14, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_4 (by
  decide) (by decide) β hZ (cHsFork_4_4_ket_zero β hZ)
theorem cHsFork_4_2_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_2.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨3, by decide⟩ ⟨13, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_3 (by
  decide) (by decide) β hZ (cHsFork_4_3_ket_zero β hZ)
theorem cHsFork_4_1_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_1.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨6, by decide⟩ ⟨12, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_2 (by
  decide) (by decide) β hZ (cHsFork_4_2_ket_zero β hZ)
theorem cHsFork_4_0_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_4_0.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨0, by decide⟩ ⟨11, by decide⟩ (rK_128 ⟨1, by decide⟩) cHsFork_4_1 (by
  decide) (by decide) β hZ (cHsFork_4_1_ket_zero β hZ)
theorem cHsDepth4_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsDepth4.eval.1.mulVec (ket β) = ket β := by
  rw [cHsDepth4, MeasureBranchHadamardSem.eval_seq_mulVec, cHsSplit_4,
    cPmSplit_mulVec_ket_zero 47 hsBranches_4 hsFlips_4 wPmPar_128 (rK_128 ⟨1,
      by decide⟩) hsSplitDisj_4 β (hZ ⟨20,
      by
      decide⟩ (le_refl 20)) (filter_scr20_branches_zero hsBranchesIdx_4 β hZ)
      (filter_scr20_flips_zero hsFlipsIdx_4 β hZ),
    cHsFork_4_0_ket_zero β hZ]
theorem cHsFork_3_5_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_3_5.eval.1.mulVec (ket β) = ket β := cHsDepth4_ket_zero β hZ
theorem cHsFork_3_4_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_3_4.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨1, by decide⟩ ⟨10, by decide⟩ (rK_128 ⟨2, by decide⟩) cHsFork_3_5 (by
  decide) (by decide) β hZ (cHsFork_3_5_ket_zero β hZ)
theorem cHsFork_3_3_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_3_3.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨4, by decide⟩ ⟨9, by decide⟩ (rK_128 ⟨2, by decide⟩) cHsFork_3_4 (by
  decide) (by decide) β hZ (cHsFork_3_4_ket_zero β hZ)
theorem cHsFork_3_2_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_3_2.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨2, by decide⟩ ⟨8, by decide⟩ (rK_128 ⟨2, by decide⟩) cHsFork_3_3 (by
  decide) (by decide) β hZ (cHsFork_3_3_ket_zero β hZ)
theorem cHsFork_3_1_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_3_1.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨3, by decide⟩ ⟨7, by decide⟩ (rK_128 ⟨2, by decide⟩) cHsFork_3_2 (by
  decide) (by decide) β hZ (cHsFork_3_2_ket_zero β hZ)
theorem cHsFork_3_0_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_3_0.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨0, by decide⟩ ⟨6, by decide⟩ (rK_128 ⟨2, by decide⟩) cHsFork_3_1 (by
  decide) (by decide) β hZ (cHsFork_3_1_ket_zero β hZ)
theorem cHsDepth3_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsDepth3.eval.1.mulVec (ket β) = ket β := by
  rw [cHsDepth3, MeasureBranchHadamardSem.eval_seq_mulVec, cHsSplit_3,
    cPmSplit_mulVec_ket_zero 47 hsBranches_3 hsFlips_3 wPmPar_128 (rK_128 ⟨2,
      by decide⟩) hsSplitDisj_3 β (hZ ⟨20,
      by
      decide⟩ (le_refl 20)) (filter_scr20_branches_zero hsBranchesIdx_3 β hZ)
      (filter_scr20_flips_zero hsFlipsIdx_3 β hZ),
    cHsFork_3_0_ket_zero β hZ]
theorem cHsFork_2_3_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_2_3.eval.1.mulVec (ket β) = ket β := cHsDepth3_ket_zero β hZ
theorem cHsFork_2_2_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_2_2.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨1, by decide⟩ ⟨5, by decide⟩ (rK_128 ⟨3, by decide⟩) cHsFork_2_3 (by
  decide) (by decide) β hZ (cHsFork_2_3_ket_zero β hZ)
theorem cHsFork_2_1_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_2_1.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨2, by decide⟩ ⟨4, by decide⟩ (rK_128 ⟨3, by decide⟩) cHsFork_2_2 (by
  decide) (by decide) β hZ (cHsFork_2_2_ket_zero β hZ)
theorem cHsFork_2_0_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_2_0.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨0, by decide⟩ ⟨3, by decide⟩ (rK_128 ⟨3, by decide⟩) cHsFork_2_1 (by
  decide) (by decide) β hZ (cHsFork_2_1_ket_zero β hZ)
theorem cHsDepth2_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsDepth2.eval.1.mulVec (ket β) = ket β := by
  rw [cHsDepth2, MeasureBranchHadamardSem.eval_seq_mulVec, cHsSplit_2,
    cPmSplit_mulVec_ket_zero 44 hsBranches_2 hsFlips_2 wPmPar_128 (rK_128 ⟨3,
      by decide⟩) hsSplitDisj_2 β (hZ ⟨20,
      by
      decide⟩ (le_refl 20)) (filter_scr20_branches_zero hsBranchesIdx_2 β hZ)
      (filter_scr20_flips_zero hsFlipsIdx_2 β hZ),
    cHsFork_2_0_ket_zero β hZ]
theorem cHsFork_1_1_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_1_1.eval.1.mulVec (ket β) = ket β := cHsDepth2_ket_zero β hZ
theorem cHsFork_1_0_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_1_0.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨0, by decide⟩ ⟨2, by decide⟩ (rK_128 ⟨4, by decide⟩) cHsFork_1_1 (by
  decide) (by decide) β hZ (cHsFork_1_1_ket_zero β hZ)
theorem cHsDepth1_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsDepth1.eval.1.mulVec (ket β) = ket β := by
  rw [cHsDepth1, MeasureBranchHadamardSem.eval_seq_mulVec, cHsSplit_1,
    cPmSplit_mulVec_ket_zero 40 hsBranches_1 hsFlips_1 wPmPar_128 (rK_128 ⟨4,
      by decide⟩) hsSplitDisj_1 β (hZ ⟨20,
      by
      decide⟩ (le_refl 20)) (filter_scr20_branches_zero hsBranchesIdx_1 β hZ)
      (filter_scr20_flips_zero hsFlipsIdx_1 β hZ),
    cHsFork_1_0_ket_zero β hZ]
theorem cHsFork_0_1_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_0_1.eval.1.mulVec (ket β) = ket β := cHsDepth1_ket_zero β hZ
theorem cHsFork_0_0_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsFork_0_0.eval.1.mulVec (ket β) = ket β :=
  withUnaryFork_ket_zero ⟨0, by decide⟩ ⟨1, by decide⟩ (rK_128 ⟨5, by decide⟩) cHsFork_0_1 (by
  decide) (by decide) β hZ (cHsFork_0_1_ket_zero β hZ)
theorem cHsDepth0_ket_zero (β : BitAssignment 128) (hZ : AllScr21Zero β) :
    cHsDepth0.eval.1.mulVec (ket β) = ket β := by
  rw [cHsDepth0, MeasureBranchHadamardSem.eval_seq_mulVec, cHsSplit_0,
    cPmSplit_mulVec_ket_zero 38 hsBranches_0 hsFlips_0 wPmPar_128 (rK_128 ⟨5,
      by decide⟩) hsSplitDisj_0 β (hZ ⟨20,
      by
      decide⟩ (le_refl 20)) (filter_scr20_branches_zero hsBranchesIdx_0 β hZ)
      (filter_scr20_flips_zero hsFlipsIdx_0 β hZ),
    cHsFork_0_0_ket_zero β hZ]
theorem cLeafHeadShell64_mulVec_ket_zero (β : BitAssignment 128)
    (hc : β wEnHead_128 = 0) (hscr : ∀ j : Fin 30, β (scr30_128 j) = 0) :
    cLeafHeadShell64.eval.1.mulVec (ket β) = ket β := by
  have hZ : AllScr21Zero β := fun j _ ↦ hscr j
  rw [cLeafHeadShell64, lockPosPostVal_eq, cHeadShell64PmSbm_128,
    MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.eval_seq_mulVec,
    ket_cnotIf_ne _ _ (by decide), hscr ⟨0, by decide⟩, hc, add_zero,
    upd_eq_self β (scr30_128 ⟨0, by decide⟩) (hscr ⟨0, by decide⟩),
    cHsDepth0_ket_zero β hZ,
    ket_cnotIf_ne _ _ (by decide), hscr ⟨0, by decide⟩, hc, add_zero,
    upd_eq_self β (scr30_128 ⟨0, by decide⟩) (hscr ⟨0, by decide⟩)]
def rKSub6 : QRegister 6 128 := rK_128
def rKSub5 : QRegister 5 128 := qregInit rKSub6
def rKSub4 : QRegister 4 128 := qregInit rKSub5
def rKSub3 : QRegister 3 128 := qregInit rKSub4
def rKSub2 : QRegister 2 128 := qregInit rKSub3
def rKSub1 : QRegister 1 128 := qregInit rKSub2
theorem rKSub5_val (i : Fin 5) : (rKSub5 i).val = 69 + i.val := by fin_cases i <;> rfl
theorem rKSub4_val (i : Fin 4) : (rKSub4 i).val = 69 + i.val := by fin_cases i <;> rfl
theorem rKSub3_val (i : Fin 3) : (rKSub3 i).val = 69 + i.val := by fin_cases i <;> rfl
theorem rKSub2_val (i : Fin 2) : (rKSub2 i).val = 69 + i.val := by fin_cases i <;> rfl
theorem rKSub1_val (i : Fin 1) : (rKSub1 i).val = 69 + i.val := by
  fin_cases i
  rfl
theorem not_mem_range_of_val_ge {m : ℕ} (r : QRegister m 128)
    (hr : ∀ i : Fin m, (r i).val = 69 + i.val) (w : Wire 128) (hw : 69 + m ≤ w.val) :
    w ∉ Set.range r.wires := by
  rintro ⟨i, rfl⟩
  have hi := i.isLt
  have hv := hr i
  omega
theorem writeReg_update_comm {n m : ℕ} (β : BitAssignment n) (r : QRegister m n)
    (γ : BitAssignment m) (u : Wire n) (v : ZMod 2) (hu : u ∉ Set.range r.wires) :
    writeReg (Function.update β u v) r γ = Function.update (writeReg β r γ) u v := by
  funext w
  by_cases hmem : ∃ i : Fin m, r i = w
  · obtain ⟨i, rfl⟩ := hmem
    rw [writeReg_apply_reg, Function.update_of_ne (fun h => hu ⟨i, h⟩), writeReg_apply_reg]
  · have hnot : w ∉ Set.range r.wires := fun ⟨i, hi⟩ => hmem ⟨i, hi⟩
    rw [writeReg_apply_of_not_mem _ _ _ _ hnot]
    by_cases hwu : w = u
    · subst hwu
      simp only [Function.update_self]
    · rw [Function.update_of_ne hwu, Function.update_of_ne hwu,
        writeReg_apply_of_not_mem _ _ _ _ hnot]
theorem oneHotScr21_wPmPar_zero (idx : Fin 20) (β : BitAssignment 128)
    (hOH : OneHotScr21 idx.val β) : β wPmPar_128 = 0 := by
  have h := hOH ⟨20, by decide⟩ (le_refl 20)
  dsimp only [wPmPar_128]
  rwa [ite_eq_right (ne_of_gt idx.isLt)] at h
theorem oneHotScr21_update_nonScr (idx : ℕ) (w : Wire 128) (v : ZMod 2)
    (hw : w.val < 86) (β : BitAssignment 128) (hOH : OneHotScr21 idx β) :
    OneHotScr21 idx (Function.update β w v) := fun j hj ↦ by
  have hne : scr30_128 j ≠ w := fun h ↦ by
    have hv := (scr30_128_val j).symm.trans (congrArg Fin.val h)
    omega
  rw [Function.update_of_ne hne, hOH j hj]
def forkSwap (i_u i_R : Fin 20) (β : BitAssignment 128) : BitAssignment 128 :=
  Function.update (Function.update β (scr20_128 i_R) 1) (scr20_128 i_u) 0
theorem oneHotScr21_forkSwap (i_u i_R : Fin 20) (huR : i_u ≠ i_R)
    (β : BitAssignment 128) (hOH : OneHotScr21 i_u.val β) :
    OneHotScr21 i_R.val (forkSwap i_u i_R β) := fun j hj ↦ by
  dsimp only [forkSwap]
  by_cases hju : j.val = i_u.val
  · have hjeq : scr30_128 j = scr20_128 i_u := congrArg scr30_128 (Fin.ext hju)
    rw [hjeq, Function.update_self, ite_eq_right (fun h ↦ huR (Fin.ext (hju.symm.trans h)))]
  · have hj_ne_u : scr30_128 j ≠ scr20_128 i_u := fun h ↦
      hju (congrArg Fin.val (scr30_128.wires.injective h))
    rw [Function.update_of_ne hj_ne_u]
    by_cases hjR : j.val = i_R.val
    · have hjeq : scr30_128 j = scr20_128 i_R := congrArg scr30_128 (Fin.ext hjR)
      rw [hjeq, Function.update_self, ite_eq_left hjR]
    · have hj_ne_R : scr30_128 j ≠ scr20_128 i_R := fun h ↦
        hjR (congrArg Fin.val (scr30_128.wires.injective h))
      rw [Function.update_of_ne hj_ne_R, hOH j hj, ite_eq_right hju, ite_eq_right hjR]
private theorem scr20_not_mem_rLow {m : ℕ} (rLow : QRegister m 128)
    (hrVal : ∀ i : Fin m, (rLow i).val = 69 + i.val) (hm : 69 + m ≤ 86) (i : Fin 20) :
    scr20_128 i ∉ Set.range rLow.wires :=
  not_mem_range_of_val_ge rLow hrVal (scr20_128 i)
    (le_trans hm (le_trans (Nat.le_add_right 86 i.val) (scr20_128_val i).ge))
private theorem oneHotScr21_scr20_ne {cur i : Fin 20} {γ : BitAssignment 128}
    (hOH : OneHotScr21 cur.val γ) (hne : i ≠ cur) : γ (scr20_128 i) = 0 := by
  have h := hOH ⟨i.val, by omega⟩ i.isLt.le
  rwa [ite_eq_right (fun h0 ↦ hne (Fin.ext h0))] at h
theorem withUnaryFork_ket_inactive_sum {m : ℕ} (rLow : QRegister m 128)
    (hrVal : ∀ i : Fin m, (rLow i).val = 69 + i.val) (cur i_u i_R : Fin 20) (t : Wire 128)
    (C : Circuit 128) (amp : Fin (2 ^ m) → ℂ) (γ : BitAssignment 128) (huR : i_u ≠ i_R)
    (hcur_u : i_u ≠ cur) (hcur_R : i_R ≠ cur) (ht : 69 + m ≤ t.val ∧ t.val < 86)
    (hOH : OneHotScr21 cur.val γ) (hC : C.eval.1.mulVec (ket γ) = ∑ x : Fin (2 ^ m), amp x •
    ket (writeReg γ rLow (basisBits m x))) :
    (withUnaryFork (scr20_128 i_u) t (scr20_128 i_R) C).eval.1.mulVec (ket γ) = ∑ x : Fin
    (2 ^ m), amp x • ket (writeReg γ rLow (basisBits m x)) := by
  have hu0 := oneHotScr21_scr20_ne hOH hcur_u
  have hR0 := oneHotScr21_scr20_ne hOH hcur_R
  have hm : 69 + m ≤ 86 := le_trans ht.1 ht.2.le
  rw [withUnaryFork, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec,
    cUnaryFork_ket_zero_left _ t _ (scr20_ne_of_lt86 i_u ht.2) (scr20_ne_scr20 huR)
      (scr20_ne_of_lt86 i_R ht.2).symm γ hu0 hR0, hC, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Matrix.mulVec_smul, inv_mulVec_ket_of_fwd _ _ _
    (cUnaryFork_ket_zero_left _ t _ (scr20_ne_of_lt86 i_u ht.2) (scr20_ne_scr20 huR)
      (scr20_ne_of_lt86 i_R ht.2).symm (writeReg γ rLow (basisBits m x))
      ((writeReg_apply_of_not_mem _ _ _ _ (scr20_not_mem_rLow rLow hrVal hm i_u)).trans hu0)
      ((writeReg_apply_of_not_mem _ _ _ _ (scr20_not_mem_rLow rLow hrVal hm i_R)).trans hR0))]
theorem withUnaryFork_ket_active_zero_sum {m : ℕ} (rLow : QRegister m 128)
    (hrVal : ∀ i : Fin m, (rLow i).val = 69 + i.val) (i_u i_R : Fin 20) (t : Wire 128)
    (C : Circuit 128) (amp : Fin (2 ^ m) → ℂ) (γ : BitAssignment 128) (huR : i_u ≠ i_R)
    (ht : 69 + m ≤ t.val ∧ t.val < 86) (hOH : OneHotScr21 i_u.val γ) (ht0 : γ t = 0) (hC :
    C.eval.1.mulVec (ket γ) = ∑ x : Fin (2 ^ m), amp x • ket (writeReg γ rLow (basisBits m
    x))) : (withUnaryFork (scr20_128 i_u) t (scr20_128 i_R) C).eval.1.mulVec (ket γ) = ∑ x :
    Fin (2 ^ m), amp x • ket (writeReg γ rLow (basisBits m x)) := by
  have hR0 := oneHotScr21_scr20_ne hOH huR.symm
  have hm : 69 + m ≤ 86 := le_trans ht.1 ht.2.le
  have hfork_zero (δ : BitAssignment 128) (hdt : δ t = 0) (hdR : δ (scr20_128 i_R) = 0) :
      (cUnaryFork (scr20_128 i_u) t (scr20_128 i_R)).eval.1.mulVec (ket δ) = ket δ := by
    rw [ket_cUnaryFork _ t _ (scr20_ne_of_lt86 i_u ht.2) (scr20_ne_scr20 huR)
      (scr20_ne_of_lt86 i_R ht.2).symm δ hdR]
    dsimp only [forkMap]
    rw [hdt, mul_zero, add_zero, upd_eq_self δ _ hdR, upd_eq_self δ _ rfl]
  rw [withUnaryFork, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec, hfork_zero γ ht0 hR0, hC, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Matrix.mulVec_smul, inv_mulVec_ket_of_fwd _ _ _
    (hfork_zero (writeReg γ rLow (basisBits m x))
      ((writeReg_apply_of_not_mem _ _ _ _ (not_mem_range_of_val_ge rLow hrVal t ht.1)).trans ht0)
      ((writeReg_apply_of_not_mem _ _ _ _ (scr20_not_mem_rLow rLow hrVal hm i_R)).trans hR0))]
theorem withUnaryFork_ket_active_one_sum {m : ℕ} (rLow : QRegister m 128)
    (hrVal : ∀ i : Fin m, (rLow i).val = 69 + i.val) (i_u i_R : Fin 20) (t : Wire 128)
    (C : Circuit 128) (amp : Fin (2 ^ m) → ℂ) (γ : BitAssignment 128) (huR : i_u ≠ i_R)
    (ht : 69 + m ≤ t.val ∧ t.val < 86) (hOH : OneHotScr21 i_u.val γ) (ht1 : γ t = 1) (hC :
    C.eval.1.mulVec (ket (forkSwap i_u i_R γ)) = ∑ x : Fin (2 ^ m), amp x • ket (writeReg
    (forkSwap i_u i_R γ) rLow (basisBits m x))) :
    (withUnaryFork (scr20_128 i_u) t (scr20_128 i_R) C).eval.1.mulVec (ket γ) = ∑ x : Fin
    (2 ^ m), amp x • ket (writeReg γ rLow (basisBits m x)) := by
  have hu1 : γ (scr20_128 i_u) = 1 := by
    have h := hOH ⟨i_u.val, by omega⟩ i_u.isLt.le
    rwa [ite_eq_left rfl] at h
  have hR0 := oneHotScr21_scr20_ne hOH huR.symm
  have hm : 69 + m ≤ 86 := le_trans ht.1 ht.2.le
  have hu_not := scr20_not_mem_rLow rLow hrVal hm i_u
  have hR_not := scr20_not_mem_rLow rLow hrVal hm i_R
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have hfork_one (δ : BitAssignment 128) (hdu : δ (scr20_128 i_u) = 1) (hdt : δ t = 1)
      (hdR : δ (scr20_128 i_R) = 0) :
      (cUnaryFork (scr20_128 i_u) t (scr20_128 i_R)).eval.1.mulVec (ket δ) =
        ket (forkSwap i_u i_R δ) := by
    rw [ket_cUnaryFork _ t _ (scr20_ne_of_lt86 i_u ht.2) (scr20_ne_scr20 huR)
      (scr20_ne_of_lt86 i_R ht.2).symm δ hdR]
    dsimp only [forkMap, forkSwap]
    rw [hdu, hdt, one_mul, h11]
  rw [withUnaryFork, MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec, hfork_one γ hu1 ht1 hR0, hC, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hw_sw : writeReg (forkSwap i_u i_R γ) rLow (basisBits m x) =
      forkSwap i_u i_R (writeReg γ rLow (basisBits m x)) :=
    (writeReg_update_comm _ rLow _ _ 0 hu_not).trans
      (congrArg (fun δ ↦ Function.update δ (scr20_128 i_u) 0)
        (writeReg_update_comm _ rLow _ _ 1 hR_not))
  rw [Matrix.mulVec_smul, hw_sw, inv_mulVec_ket_of_fwd _ _ _
      (hfork_one (writeReg γ rLow (basisBits m x))
        ((writeReg_apply_of_not_mem _ _ _ _ hu_not).trans hu1)
        ((writeReg_apply_of_not_mem _ _ _ _ (not_mem_range_of_val_ge rLow hrVal t ht.1)).trans ht1)
        ((writeReg_apply_of_not_mem _ _ _ _ hR_not).trans hR0))]
theorem sum_sbmAmp_one (words : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate)
    (β : BitAssignment 128) (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) :
    alpha0 (words 0 0) • ket β +
        alpha1 (words 0 0) • ket (Function.update β (rK_128 ⟨0, by decide⟩) 1) =
      ∑ j : Fin (2 ^ 1), sbmAmp 1 words j • ket (writeReg β rKSub1 (basisBits 1 j)) := by
  have htwo : (∑ j : Fin (2 ^ 1), sbmAmp 1 words j • ket (writeReg β rKSub1 (basisBits 1 j))) =
      sbmAmp 1 words 0 • ket (writeReg β rKSub1 (basisBits 1 0)) +
      sbmAmp 1 words 1 • ket (writeReg β rKSub1 (basisBits 1 1)) := Fin.sum_univ_two _
  rw [htwo]
  have hw0 : writeReg β rKSub1 (basisBits 1 0) = β :=
    writeReg_self β rKSub1 fun i ↦ by
      fin_cases i
      exact (hr 0).symm
  have hw1 : writeReg β rKSub1 (basisBits 1 1) = Function.update β (rK_128 ⟨0, by decide⟩) 1 := by
    funext w
    by_cases hw : w = rK_128 ⟨0, by decide⟩
    · subst hw
      change writeReg β rKSub1 (basisBits 1 1) (rKSub1 0) = _
      rw [writeReg_apply_reg, Function.update_self]
      rfl
    · have hnot : w ∉ Set.range rKSub1.wires := by
        rintro ⟨i, rfl⟩
        fin_cases i
        exact hw rfl
      rw [writeReg_apply_of_not_mem _ _ _ _ hnot, Function.update_of_ne hw]
  have ha0 : sbmAmp 1 words 0 = alpha0 (words 0 0) := by simp [sbmAmp]
  have ha1 : sbmAmp 1 words 1 = alpha1 (words 0 0) := by simp [sbmAmp]
  rw [hw0, hw1, ha0, ha1]
theorem stitch_sbmAmp_succ (m : ℕ) (r : QRegister (m + 1) 128)
    (words : (k : Fin (m + 1)) → Fin (2 ^ k.val) → List HSTGate) (β : BitAssignment 128)
    (hrTop : β (r (Fin.last m)) = 0) : alpha0 (words 0 0) • (∑ x : Fin (2 ^ m), sbmAmp m (fun
    k q => words k.succ ⟨q.val, lt_pow_succ_of_lt q⟩) x • ket (writeReg β (qregInit r)
    (basisBits m x))) + alpha1 (words 0 0) • (∑ x : Fin (2 ^ m), sbmAmp m (fun k q => words
    k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩) x • ket (writeReg (Function.update β (r
    (Fin.last m)) 1) (qregInit r) (basisBits m x))) = ∑ j : Fin (2 ^ (m + 1)), sbmAmp (m + 1)
    words j • ket (writeReg β r (basisBits (m + 1) j)) := by
  rw [Finset.smul_sum, Finset.smul_sum, fin_sum_pow_succ]
  have hβ0 : β = Function.update β (r (Fin.last m)) 0 := (upd_eq_self β _ hrTop).symm
  congr 1
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [smul_smul, hβ0,
      writeReg_split_msb β r 0 x ⟨x.val, lt_pow_succ_of_lt x⟩ (by simp), ← hβ0]
    simp [sbmAmp, x.isLt]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [smul_smul, writeReg_split_msb β r 1 x ⟨2 ^ m + x.val, add_lt_pow_succ x⟩ (by simp)]
    simp [sbmAmp, show ¬ (2 ^ m + x.val < 2 ^ m) by omega]
def hsWords_0_0 : (k : Fin 6) → Fin (2 ^ k.val) → List HSTGate := headShell64Words
def hsWords_1_0 : (k : Fin 5) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_0_0 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_1_1 : (k : Fin 5) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_0_0 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_2_0 : (k : Fin 4) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_1_0 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_2_1 : (k : Fin 4) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_1_0 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_2_2 : (k : Fin 4) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_1_1 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_3_0 : (k : Fin 3) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_2_0 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_3_1 : (k : Fin 3) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_2_0 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_3_2 : (k : Fin 3) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_2_1 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_3_3 : (k : Fin 3) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_2_1 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_3_4 : (k : Fin 3) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_2_2 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_3_5 : (k : Fin 3) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_2_2 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_4_0 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_0 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_4_1 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_0 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_4_2 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_1 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_4_3 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_1 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_4_4 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_2 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_4_5 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_2 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_4_6 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_3 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_4_7 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_3 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_4_8 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_4 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_4_9 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_4 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_4_10 : (k : Fin 2) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_3_5 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_0 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_0 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_1 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_0 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_2 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_1 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_3 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_1 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_4 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_2 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_5 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_2 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_6 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_3 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_7 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_3 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_8 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_4 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_9 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_4 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_10 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_5 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_11 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_5 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_12 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_6 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_13 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_6 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_14 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_7 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_15 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_7 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_17 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_8 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_18 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_9 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
def hsWords_5_19 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_9 k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩
def hsWords_5_20 : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate := fun k q =>
  hsWords_4_10 k.succ ⟨q.val, lt_pow_succ_of_lt q⟩
private theorem cHsDepth5_of_onehot (idx : Fin 20) (odds : List (Fin 4))
    (words : (k : Fin 1) → Fin (2 ^ k.val) → List HSTGate) (β : BitAssignment 128)
    (hOH : OneHotScr21 idx.val β) (hr : ∀ i : Fin 1, β (rKSub1 i) = 0)
    (hbr0 : (hsBranchesIdx_5.filter (fun p => p.1 == idx)).map
      (fun p => (scr20_128 p.1, p.2)) = [(scr20_128 idx, odds)])
    (hfl0 : (hsFlipsIdx_5.filter (fun i => i == idx)).map scr20_128 = [])
    (hlen : odds.length = 47) (hw : oddsToHst odds = words 0 0) :
    cHsDepth5.eval.1.mulVec (ket β) =
      ∑ j : Fin (2 ^ 1), sbmAmp 1 words j • ket (writeReg β rKSub1 (basisBits 1 j)) := by
  rw [cHsDepth5, cHsSplit_5,
    cPmSplit_mulVec_ket_onehot 47 hsBranches_5 hsFlips_5 wPmPar_128 (rK_128 ⟨0, by decide⟩)
      (scr20_128 idx) odds hsSplitDisj_5 hlen β (oneHotScr21_wPmPar_zero idx β hOH) (hr 0)
      ((filter_scr20_branches idx hsBranchesIdx_5 β hOH).trans hbr0)
      ((filter_scr20_flips idx hsFlipsIdx_5 β hOH).trans hfl0),
    hw, sum_sbmAmp_one words β hr]
theorem cHsDepth5_node_0 (β : BitAssignment 128) (hOH : OneHotScr21 0 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_0 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨0, by decide⟩ hstPoolOdds_21 hsWords_5_0 β hOH hr rfl rfl
    length_hstPoolOdds_21 oddsToHst_hstPoolOdds_21
theorem cHsDepth5_node_1 (β : BitAssignment 128) (hOH : OneHotScr21 11 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_1 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨11, by decide⟩ hstPoolOdds_22 hsWords_5_1 β hOH hr rfl rfl
    length_hstPoolOdds_22 oddsToHst_hstPoolOdds_22
theorem cHsDepth5_node_2 (β : BitAssignment 128) (hOH : OneHotScr21 6 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_2 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨6, by decide⟩ hstPoolOdds_23 hsWords_5_2 β hOH hr rfl rfl
    length_hstPoolOdds_23 oddsToHst_hstPoolOdds_23
theorem cHsDepth5_node_3 (β : BitAssignment 128) (hOH : OneHotScr21 12 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_3 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨12, by decide⟩ hstPoolOdds_24 hsWords_5_3 β hOH hr rfl rfl
    length_hstPoolOdds_24 oddsToHst_hstPoolOdds_24
theorem cHsDepth5_node_4 (β : BitAssignment 128) (hOH : OneHotScr21 3 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_4 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨3, by decide⟩ hstPoolOdds_25 hsWords_5_4 β hOH hr rfl rfl
    length_hstPoolOdds_25 oddsToHst_hstPoolOdds_25
theorem cHsDepth5_node_5 (β : BitAssignment 128) (hOH : OneHotScr21 13 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_5 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨13, by decide⟩ hstPoolOdds_26 hsWords_5_5 β hOH hr rfl rfl
    length_hstPoolOdds_26 oddsToHst_hstPoolOdds_26
theorem cHsDepth5_node_6 (β : BitAssignment 128) (hOH : OneHotScr21 7 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_6 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨7, by decide⟩ hstPoolOdds_27 hsWords_5_6 β hOH hr rfl rfl
    length_hstPoolOdds_27 oddsToHst_hstPoolOdds_27
theorem cHsDepth5_node_7 (β : BitAssignment 128) (hOH : OneHotScr21 14 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_7 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨14, by decide⟩ hstPoolOdds_28 hsWords_5_7 β hOH hr rfl rfl
    length_hstPoolOdds_28 oddsToHst_hstPoolOdds_28
theorem cHsDepth5_node_8 (β : BitAssignment 128) (hOH : OneHotScr21 2 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_8 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨2, by decide⟩ hstPoolOdds_29 hsWords_5_8 β hOH hr rfl rfl
    length_hstPoolOdds_29 oddsToHst_hstPoolOdds_29
theorem cHsDepth5_node_9 (β : BitAssignment 128) (hOH : OneHotScr21 15 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_9 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨15, by decide⟩ hstPoolOdds_30 hsWords_5_9 β hOH hr rfl rfl
    length_hstPoolOdds_30 oddsToHst_hstPoolOdds_30
theorem cHsDepth5_node_10 (β : BitAssignment 128) (hOH : OneHotScr21 8 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_10 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨8, by decide⟩ hstPoolOdds_31 hsWords_5_10 β hOH hr rfl rfl
    length_hstPoolOdds_31 oddsToHst_hstPoolOdds_31
theorem cHsDepth5_node_11 (β : BitAssignment 128) (hOH : OneHotScr21 16 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_11 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨16, by decide⟩ hstPoolOdds_32 hsWords_5_11 β hOH hr rfl rfl
    length_hstPoolOdds_32 oddsToHst_hstPoolOdds_32
theorem cHsDepth5_node_12 (β : BitAssignment 128) (hOH : OneHotScr21 4 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_12 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨4, by decide⟩ hstPoolOdds_33 hsWords_5_12 β hOH hr rfl rfl
    length_hstPoolOdds_33 oddsToHst_hstPoolOdds_33
theorem cHsDepth5_node_13 (β : BitAssignment 128) (hOH : OneHotScr21 17 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_13 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨17, by decide⟩ hstPoolOdds_34 hsWords_5_13 β hOH hr rfl rfl
    length_hstPoolOdds_34 oddsToHst_hstPoolOdds_34
theorem cHsDepth5_node_14 (β : BitAssignment 128) (hOH : OneHotScr21 9 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_14 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨9, by decide⟩ hstPoolOdds_35 hsWords_5_14 β hOH hr rfl rfl
    length_hstPoolOdds_35 oddsToHst_hstPoolOdds_35
theorem cHsDepth5_node_15 (β : BitAssignment 128) (hOH : OneHotScr21 18 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_15 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨18, by decide⟩ hstPoolOdds_36 hsWords_5_15 β hOH hr rfl rfl
    length_hstPoolOdds_36 oddsToHst_hstPoolOdds_36
theorem cHsDepth5_node_17 (β : BitAssignment 128) (hOH : OneHotScr21 1 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_17 j • ket (writeReg β rKSub1 (basisBits 1 j)) := by
  have hw0 : hsWords_5_17 0 0 = [] := rfl
  rw [cHsDepth5, cHsSplit_5,
    cPmSplit_mulVec_ket_flip 47 hsBranches_5 hsFlips_5 wPmPar_128 (rK_128 ⟨0, by decide⟩)
      (scr20_128 ⟨1, by decide⟩) hsSplitDisj_5 β (oneHotScr21_wPmPar_zero ⟨1, by decide⟩ β hOH)
      (hr 0) ((filter_scr20_branches ⟨1, by decide⟩ hsBranchesIdx_5 β hOH).trans rfl)
      ((filter_scr20_flips ⟨1, by decide⟩ hsFlipsIdx_5 β hOH).trans rfl),
    ← sum_sbmAmp_one hsWords_5_17 β hr, hw0,
    alpha0_nil_eq_zero, alpha1_nil_eq_one, zero_smul, one_smul, zero_add]
theorem cHsDepth5_node_18 (β : BitAssignment 128) (hOH : OneHotScr21 10 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_18 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨10, by decide⟩ hstPoolOdds_37 hsWords_5_18 β hOH hr rfl rfl
    length_hstPoolOdds_37 oddsToHst_hstPoolOdds_37
theorem cHsDepth5_node_19 (β : BitAssignment 128) (hOH : OneHotScr21 19 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_19 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨19, by decide⟩ hstPoolOdds_38 hsWords_5_19 β hOH hr rfl rfl
    length_hstPoolOdds_38 oddsToHst_hstPoolOdds_38
theorem cHsDepth5_node_20 (β : BitAssignment 128) (hOH : OneHotScr21 5 β)
    (hr : ∀ i : Fin 1, β (rKSub1 i) = 0) : cHsDepth5.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 1), sbmAmp 1 hsWords_5_20 j • ket (writeReg β rKSub1 (basisBits 1 j)) :=
  cHsDepth5_of_onehot ⟨5, by decide⟩ hstPoolOdds_39 hsWords_5_20 β hOH hr rfl rfl
    length_hstPoolOdds_39 oddsToHst_hstPoolOdds_39
private def forkChain (t : Wire 128) :
    List (Fin 20 × Fin 20) → Circuit 128 → Circuit 128
  | [], endC => endC
  | p :: ps, endC =>
      withUnaryFork (scr20_128 p.1) t (scr20_128 p.2) (forkChain t ps endC)
private theorem forkChain_append (t : Wire 128) :
    ∀ (pre suf : List (Fin 20 × Fin 20)) (endC : Circuit 128),
      forkChain t (pre ++ suf) endC = forkChain t pre (forkChain t suf endC)
  | [], _, _ => rfl
  | _ :: pre, suf, endC =>
      congrArg (withUnaryFork _ t _) (forkChain_append t pre suf endC)
private theorem forkChain_inact {m : ℕ} {rLow : QRegister m 128}
    (hrVal : ∀ i : Fin m, (rLow i).val = 69 + i.val)
    {t : Wire 128} (ht : 69 + m ≤ t.val ∧ t.val < 86)
    {cur : Fin 20} {amp : Fin (2 ^ m) → ℂ} {γ : BitAssignment 128}
    {endC : Circuit 128} (hOH : OneHotScr21 cur.val γ)
    (hEnd : endC.eval.1.mulVec (ket γ) =
      ∑ x : Fin (2 ^ m), amp x • ket (writeReg γ rLow (basisBits m x))) :
    ∀ (ps : List (Fin 20 × Fin 20)),
      (∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ cur ∧ p.2 ≠ cur) →
      (forkChain t ps endC).eval.1.mulVec (ket γ) =
        ∑ x : Fin (2 ^ m), amp x • ket (writeReg γ rLow (basisBits m x))
  | [], _ => hEnd
  | p :: ps, hps =>
      let hp := hps p List.mem_cons_self
      withUnaryFork_ket_inactive_sum rLow hrVal cur p.1 p.2 t
        (forkChain t ps endC) amp γ hp.1 hp.2.1 hp.2.2 ht hOH
        (forkChain_inact hrVal ht hOH hEnd ps fun q hm ↦
          hps q (List.mem_cons_of_mem _ hm))
private theorem hsSplitStitch_onehot {m : ℕ} (L : ℕ)
    (branchesIdx : List (Fin 20 × List (Fin 4))) (flipsIdx : List (Fin 20))
    (r : QRegister (m + 1) 128)
    (hrLowVal : ∀ i : Fin m, (qregInit r i).val = 69 + i.val)
    (htBounds : 69 + m ≤ (r (Fin.last m)).val ∧ (r (Fin.last m)).val < 86)
    (hDisj : PmSplitDisj
      ((branchesIdx.map (fun p => (scr20_128 p.1, p.2))).map Prod.fst)
      (flipsIdx.map scr20_128) wPmPar_128 (r (Fin.last m)))
    (fork0 endC : Circuit 128) (pre suf : List (Fin 20 × Fin 20))
    (idx i_R : Fin 20) (huR : idx ≠ i_R) (odds : List (Fin 4))
    (words : (k : Fin (m + 1)) → Fin (2 ^ k.val) → List HSTGate)
    (β : BitAssignment 128) (hOH : OneHotScr21 idx.val β)
    (hr : ∀ i : Fin (m + 1), β (r i) = 0)
    (hbr0 : (branchesIdx.filter (fun p => p.1 == idx)).map
      (fun p => (scr20_128 p.1, p.2)) = [(scr20_128 idx, odds)])
    (hfl0 : (flipsIdx.filter (fun i => i == idx)).map scr20_128 = [])
    (hlen : odds.length = L) (hw : oddsToHst odds = words 0 0)
    (hfk : fork0 = forkChain (r (Fin.last m)) (pre ++ (idx, i_R) :: suf) endC)
    (hPre : ∀ p ∈ pre, p.1 ≠ p.2 ∧ p.1 ≠ idx ∧ p.2 ≠ idx)
    (hSufL : ∀ p ∈ suf, p.1 ≠ p.2 ∧ p.1 ≠ idx ∧ p.2 ≠ idx)
    (hSufR : ∀ p ∈ suf, p.1 ≠ p.2 ∧ p.1 ≠ i_R ∧ p.2 ≠ i_R)
    (hEndL : endC.eval.1.mulVec (ket β) =
      ∑ x : Fin (2 ^ m),
        sbmAmp m (fun k q => words k.succ ⟨q.val, lt_pow_succ_of_lt q⟩) x •
          ket (writeReg β (qregInit r) (basisBits m x)))
    (hEndR : ∀ γ : BitAssignment 128, OneHotScr21 i_R.val γ →
      (∀ l : Fin m, γ (qregInit r l) = 0) →
      endC.eval.1.mulVec (ket γ) =
        ∑ x : Fin (2 ^ m),
          sbmAmp m (fun k q => words k.succ ⟨2 ^ k.val + q.val, add_lt_pow_succ q⟩) x •
            ket (writeReg γ (qregInit r) (basisBits m x))) :
    (cPmSplit L (branchesIdx.map (fun p => (scr20_128 p.1, p.2)))
      (flipsIdx.map scr20_128) wPmPar_128 (r (Fin.last m)) ;;ᶜ fork0).eval.1.mulVec
      (ket β) =
      ∑ j : Fin (2 ^ (m + 1)), sbmAmp (m + 1) words j •
        ket (writeReg β r (basisBits (m + 1) j)) := by
  set rLow := qregInit r
  set t := r (Fin.last m)
  have hfk' : fork0 = forkChain t pre
      (withUnaryFork (scr20_128 idx) t (scr20_128 i_R) (forkChain t suf endC)) :=
    hfk.trans (forkChain_append t pre ((idx, i_R) :: suf) endC)
  rw [MeasureBranchHadamardSem.eval_seq_mulVec,
    cPmSplit_mulVec_ket_onehot L _ _ wPmPar_128 t (scr20_128 idx) odds hDisj hlen
      β (oneHotScr21_wPmPar_zero idx β hOH) (hr (Fin.last m))
      ((filter_scr20_branches idx branchesIdx β hOH).trans hbr0)
      ((filter_scr20_flips idx flipsIdx β hOH).trans hfl0),
    hw, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hfk']
  have hL := forkChain_inact hrLowVal htBounds hOH
    (withUnaryFork_ket_active_zero_sum rLow hrLowVal idx i_R t (forkChain t suf endC) _
      β huR htBounds hOH (hr (Fin.last m))
      (forkChain_inact hrLowVal htBounds hOH hEndL suf hSufL)) pre hPre
  set β1 := Function.update β t 1
  have hOH1 : OneHotScr21 idx.val β1 :=
    oneHotScr21_update_nonScr idx.val t 1 htBounds.2 β hOH
  have hrLow1 (l : Fin m) : β1 (rLow l) = 0 := by
    dsimp only [β1]
    have hne : rLow l ≠ t := fun h ↦ by
      have hv := congrArg Fin.val h
      have hl := hrLowVal l
      have ht1 := htBounds.1
      have hlt := l.isLt
      omega
    rw [Function.update_of_ne hne]
    exact hr l.castSucc
  set γSw := forkSwap idx i_R β1
  have hOHSw : OneHotScr21 i_R.val γSw := oneHotScr21_forkSwap idx i_R huR β1 hOH1
  have hrSw (l : Fin m) : γSw (rLow l) = 0 := by
    have h86 : (rLow l).val < 86 := lt_of_lt_of_le
      (by rw [hrLowVal l]; exact Nat.add_lt_add_left l.isLt 69)
      (le_trans htBounds.1 htBounds.2.le)
    dsimp only [γSw, forkSwap]
    rw [Function.update_of_ne (scr20_ne_of_lt86 idx h86).symm,
      Function.update_of_ne (scr20_ne_of_lt86 i_R h86).symm, hrLow1 l]
  have hR := forkChain_inact hrLowVal htBounds hOH1
    (withUnaryFork_ket_active_one_sum rLow hrLowVal idx i_R t (forkChain t suf endC) _
      β1 huR htBounds hOH1 (Function.update_self t 1 β)
      (forkChain_inact hrLowVal htBounds hOHSw (hEndR γSw hOHSw hrSw) suf hSufR)) pre hPre
  rw [hL, hR]
  exact stitch_sbmAmp_succ m r words β (hr (Fin.last m))
private theorem hsSplitStitch_zero {m : ℕ} (L : ℕ)
    (branchesIdx : List (Fin 20 × List (Fin 4))) (flipsIdx : List (Fin 20))
    (r : QRegister (m + 1) 128)
    (hrLowVal : ∀ i : Fin m, (qregInit r i).val = 69 + i.val)
    (htBounds : 69 + m ≤ (r (Fin.last m)).val ∧ (r (Fin.last m)).val < 86)
    (hDisj : PmSplitDisj
      ((branchesIdx.map (fun p => (scr20_128 p.1, p.2))).map Prod.fst)
      (flipsIdx.map scr20_128) wPmPar_128 (r (Fin.last m)))
    (fork0 endC : Circuit 128) (ps : List (Fin 20 × Fin 20)) (idx : Fin 20)
    (words : (k : Fin (m + 1)) → Fin (2 ^ k.val) → List HSTGate)
    (β : BitAssignment 128) (hOH : OneHotScr21 idx.val β)
    (hr : ∀ i : Fin (m + 1), β (r i) = 0)
    (hbr0 : (branchesIdx.filter (fun p => p.1 == idx)).map
      (fun p => (scr20_128 p.1, p.2)) = [])
    (hfl0 : (flipsIdx.filter (fun i => i == idx)).map scr20_128 = [])
    (hw : words 0 0 = [.H])
    (hfk : fork0 = forkChain (r (Fin.last m)) ps endC)
    (hPs : ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ≠ idx ∧ p.2 ≠ idx)
    (hEnd : endC.eval.1.mulVec (ket β) =
      ∑ x : Fin (2 ^ m),
        sbmAmp m (fun k q => words k.succ ⟨q.val, lt_pow_succ_of_lt q⟩) x •
          ket (writeReg β (qregInit r) (basisBits m x))) :
    (cPmSplit L (branchesIdx.map (fun p => (scr20_128 p.1, p.2)))
      (flipsIdx.map scr20_128) wPmPar_128 (r (Fin.last m)) ;;ᶜ fork0).eval.1.mulVec
      (ket β) =
      ∑ j : Fin (2 ^ (m + 1)), sbmAmp (m + 1) words j •
        ket (writeReg β r (basisBits (m + 1) j)) := by
  have hL := forkChain_inact hrLowVal htBounds hOH hEnd ps hPs
  rw [MeasureBranchHadamardSem.eval_seq_mulVec,
    cPmSplit_mulVec_ket_zero L _ _ wPmPar_128 (r (Fin.last m)) hDisj β
      (oneHotScr21_wPmPar_zero idx β hOH)
      ((filter_scr20_branches idx branchesIdx β hOH).trans hbr0)
      ((filter_scr20_flips idx flipsIdx β hOH).trans hfl0),
    hfk, hL, ← stitch_sbmAmp_succ m r words β (hr (Fin.last m)),
    hw, alpha0_singleton_H, alpha1_singleton_H_eq_zero, one_smul, zero_smul, add_zero]
private def forks4Idx : List (Fin 20 × Fin 20) :=
  [(0, 11), (6, 12), (3, 13), (7, 14), (2, 15), (8, 16), (4, 17), (9, 18), (10, 19)]
theorem cHsDepth4_node_0 (β : BitAssignment 128) (hOH : OneHotScr21 0 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_0 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 0) (forks4Idx.drop 1)
    ⟨0, by decide⟩ ⟨11, by decide⟩ (by decide) hstPoolOdds_12 hsWords_4_0
    β hOH hr rfl rfl length_hstPoolOdds_12 oddsToHst_hstPoolOdds_12
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_0 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_1
theorem cHsDepth4_node_1 (β : BitAssignment 128) (hOH : OneHotScr21 6 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_1 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 1) (forks4Idx.drop 2)
    ⟨6, by decide⟩ ⟨12, by decide⟩ (by decide) hstPoolOdds_13 hsWords_4_1
    β hOH hr rfl rfl length_hstPoolOdds_13 oddsToHst_hstPoolOdds_13
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_2 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_3
theorem cHsDepth4_node_2 (β : BitAssignment 128) (hOH : OneHotScr21 3 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_2 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 2) (forks4Idx.drop 3)
    ⟨3, by decide⟩ ⟨13, by decide⟩ (by decide) hstPoolOdds_14 hsWords_4_2
    β hOH hr rfl rfl length_hstPoolOdds_14 oddsToHst_hstPoolOdds_14
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_4 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_5
theorem cHsDepth4_node_3 (β : BitAssignment 128) (hOH : OneHotScr21 7 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_3 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 3) (forks4Idx.drop 4)
    ⟨7, by decide⟩ ⟨14, by decide⟩ (by decide) hstPoolOdds_15 hsWords_4_3
    β hOH hr rfl rfl length_hstPoolOdds_15 oddsToHst_hstPoolOdds_15
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_6 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_7
theorem cHsDepth4_node_4 (β : BitAssignment 128) (hOH : OneHotScr21 2 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_4 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 4) (forks4Idx.drop 5)
    ⟨2, by decide⟩ ⟨15, by decide⟩ (by decide) hstPoolOdds_16 hsWords_4_4
    β hOH hr rfl rfl length_hstPoolOdds_16 oddsToHst_hstPoolOdds_16
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_8 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_9
theorem cHsDepth4_node_5 (β : BitAssignment 128) (hOH : OneHotScr21 8 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_5 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 5) (forks4Idx.drop 6)
    ⟨8, by decide⟩ ⟨16, by decide⟩ (by decide) hstPoolOdds_17 hsWords_4_5
    β hOH hr rfl rfl length_hstPoolOdds_17 oddsToHst_hstPoolOdds_17
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_10 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_11
theorem cHsDepth4_node_6 (β : BitAssignment 128) (hOH : OneHotScr21 4 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_6 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 6) (forks4Idx.drop 7)
    ⟨4, by decide⟩ ⟨17, by decide⟩ (by decide) hstPoolOdds_18 hsWords_4_6
    β hOH hr rfl rfl length_hstPoolOdds_18 oddsToHst_hstPoolOdds_18
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_12 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_13
theorem cHsDepth4_node_7 (β : BitAssignment 128) (hOH : OneHotScr21 9 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_7 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 7) (forks4Idx.drop 8)
    ⟨9, by decide⟩ ⟨18, by decide⟩ (by decide) hstPoolOdds_19 hsWords_4_7
    β hOH hr rfl rfl length_hstPoolOdds_19 oddsToHst_hstPoolOdds_19
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_14 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_15
theorem cHsDepth4_node_8 (β : BitAssignment 128) (hOH : OneHotScr21 1 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_8 j • ket (writeReg β rKSub2 (basisBits 2 j)) := by
  rw [cHsDepth4, MeasureBranchHadamardSem.eval_seq_mulVec, cHsSplit_4,
    cPmSplit_mulVec_ket_flip 47 hsBranches_4 hsFlips_4 wPmPar_128 (rK_128 ⟨1, by decide⟩)
      (scr20_128 ⟨1, by decide⟩) hsSplitDisj_4 β
      (oneHotScr21_wPmPar_zero ⟨1, by decide⟩ β hOH) (hr (Fin.last 1))
      ((filter_scr20_branches ⟨1, by decide⟩ hsBranchesIdx_4 β hOH).trans rfl)
      ((filter_scr20_flips ⟨1, by decide⟩ hsFlipsIdx_4 β hOH).trans rfl)]
  set β1 := Function.update β (rK_128 ⟨1, by decide⟩) 1
  have hOH1 : OneHotScr21 1 β1 :=
    oneHotScr21_update_nonScr 1 (rK_128 ⟨1, by decide⟩) 1 (by decide) β hOH
  have hrLow1 (l : Fin 1) : β1 (rKSub1 l) = 0 := by
    fin_cases l
    exact (Function.update_of_ne
      (by decide : rKSub1 0 ≠ rK_128 ⟨1, Nat.lt_of_sub_eq_succ rfl⟩) 1 β).trans (hr 0)
  have hfk : cHsFork_4_0 = forkChain (rK_128 ⟨1, by decide⟩) forks4Idx cHsDepth5 := rfl
  have hword : hsWords_4_8 0 0 = [] := rfl
  rw [hfk, forkChain_inact rKSub1_val (t := rK_128 ⟨1, by decide⟩) (by decide)
      (cur := ⟨1, by decide⟩) hOH1 (cHsDepth5_node_17 β1 hOH1 hrLow1) forks4Idx (by decide),
    ← stitch_sbmAmp_succ 1 rKSub2 hsWords_4_8 β (hr (Fin.last 1)),
    hword, alpha0_nil_eq_zero, alpha1_nil_eq_one, zero_smul, one_smul, zero_add]
  rfl
theorem cHsDepth4_node_9 (β : BitAssignment 128) (hOH : OneHotScr21 10 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_9 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 (forks4Idx.take 8) []
    ⟨10, by decide⟩ ⟨19, by decide⟩ (by decide) hstPoolOdds_20 hsWords_4_9
    β hOH hr rfl rfl length_hstPoolOdds_20 oddsToHst_hstPoolOdds_20
    rfl (by decide) (by decide) (by decide)
    (cHsDepth5_node_18 β hOH fun l ↦ hr l.castSucc) cHsDepth5_node_19
theorem cHsDepth4_node_10 (β : BitAssignment 128) (hOH : OneHotScr21 5 β)
    (hr : ∀ i : Fin 2, β (rKSub2 i) = 0) : cHsDepth4.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 2), sbmAmp 2 hsWords_4_10 j • ket (writeReg β rKSub2 (basisBits 2 j)) :=
  hsSplitStitch_zero 47 hsBranchesIdx_4 hsFlipsIdx_4 rKSub2 rKSub1_val (by decide)
    hsSplitDisj_4 cHsFork_4_0 cHsDepth5 forks4Idx ⟨5, by decide⟩
    hsWords_4_10 β hOH hr rfl rfl rfl rfl (by decide)
    (cHsDepth5_node_20 β hOH fun l ↦ hr l.castSucc)
theorem cHsDepth3_node_0 (β : BitAssignment 128) (hOH : OneHotScr21 0 β)
    (hr : ∀ i : Fin 3, β (rKSub3 i) = 0) : cHsDepth3.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 3), sbmAmp 3 hsWords_3_0 j • ket (writeReg β rKSub3 (basisBits 3 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_3 hsFlipsIdx_3 rKSub3 rKSub2_val (by decide)
    hsSplitDisj_3 cHsFork_3_0 cHsDepth4 [] [(3, 7), (2, 8), (4, 9), (1, 10)]
    ⟨0, by decide⟩ ⟨6, by decide⟩ (by decide) hstPoolOdds_7 hsWords_3_0
    β hOH hr rfl rfl length_hstPoolOdds_7 oddsToHst_hstPoolOdds_7
    rfl (by decide) (by decide) (by decide)
    (cHsDepth4_node_0 β hOH fun l ↦ hr l.castSucc) cHsDepth4_node_1
theorem cHsDepth3_node_1 (β : BitAssignment 128) (hOH : OneHotScr21 3 β)
    (hr : ∀ i : Fin 3, β (rKSub3 i) = 0) : cHsDepth3.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 3), sbmAmp 3 hsWords_3_1 j • ket (writeReg β rKSub3 (basisBits 3 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_3 hsFlipsIdx_3 rKSub3 rKSub2_val (by decide)
    hsSplitDisj_3 cHsFork_3_0 cHsDepth4 [(0, 6)] [(2, 8), (4, 9), (1, 10)]
    ⟨3, by decide⟩ ⟨7, by decide⟩ (by decide) hstPoolOdds_8 hsWords_3_1
    β hOH hr rfl rfl length_hstPoolOdds_8 oddsToHst_hstPoolOdds_8
    rfl (by decide) (by decide) (by decide)
    (cHsDepth4_node_2 β hOH fun l ↦ hr l.castSucc) cHsDepth4_node_3
theorem cHsDepth3_node_2 (β : BitAssignment 128) (hOH : OneHotScr21 2 β)
    (hr : ∀ i : Fin 3, β (rKSub3 i) = 0) : cHsDepth3.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 3), sbmAmp 3 hsWords_3_2 j • ket (writeReg β rKSub3 (basisBits 3 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_3 hsFlipsIdx_3 rKSub3 rKSub2_val (by decide)
    hsSplitDisj_3 cHsFork_3_0 cHsDepth4 [(0, 6), (3, 7)] [(4, 9), (1, 10)]
    ⟨2, by decide⟩ ⟨8, by decide⟩ (by decide) hstPoolOdds_9 hsWords_3_2
    β hOH hr rfl rfl length_hstPoolOdds_9 oddsToHst_hstPoolOdds_9
    rfl (by decide) (by decide) (by decide)
    (cHsDepth4_node_4 β hOH fun l ↦ hr l.castSucc) cHsDepth4_node_5
theorem cHsDepth3_node_3 (β : BitAssignment 128) (hOH : OneHotScr21 4 β)
    (hr : ∀ i : Fin 3, β (rKSub3 i) = 0) : cHsDepth3.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 3), sbmAmp 3 hsWords_3_3 j • ket (writeReg β rKSub3 (basisBits 3 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_3 hsFlipsIdx_3 rKSub3 rKSub2_val (by decide)
    hsSplitDisj_3 cHsFork_3_0 cHsDepth4 [(0, 6), (3, 7), (2, 8)] [(1, 10)]
    ⟨4, by decide⟩ ⟨9, by decide⟩ (by decide) hstPoolOdds_10 hsWords_3_3
    β hOH hr rfl rfl length_hstPoolOdds_10 oddsToHst_hstPoolOdds_10
    rfl (by decide) (by decide) (by decide)
    (cHsDepth4_node_6 β hOH fun l ↦ hr l.castSucc) cHsDepth4_node_7
theorem cHsDepth3_node_4 (β : BitAssignment 128) (hOH : OneHotScr21 1 β)
    (hr : ∀ i : Fin 3, β (rKSub3 i) = 0) : cHsDepth3.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 3), sbmAmp 3 hsWords_3_4 j • ket (writeReg β rKSub3 (basisBits 3 j)) :=
  hsSplitStitch_onehot 47 hsBranchesIdx_3 hsFlipsIdx_3 rKSub3 rKSub2_val (by decide)
    hsSplitDisj_3 cHsFork_3_0 cHsDepth4 [(0, 6), (3, 7), (2, 8), (4, 9)] []
    ⟨1, by decide⟩ ⟨10, by decide⟩ (by decide) hstPoolOdds_11 hsWords_3_4
    β hOH hr rfl rfl length_hstPoolOdds_11 oddsToHst_hstPoolOdds_11
    rfl (by decide) (by decide) (by decide)
    (cHsDepth4_node_8 β hOH fun l ↦ hr l.castSucc) cHsDepth4_node_9
theorem cHsDepth3_node_5 (β : BitAssignment 128) (hOH : OneHotScr21 5 β)
    (hr : ∀ i : Fin 3, β (rKSub3 i) = 0) : cHsDepth3.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 3), sbmAmp 3 hsWords_3_5 j • ket (writeReg β rKSub3 (basisBits 3 j)) :=
  hsSplitStitch_zero 47 hsBranchesIdx_3 hsFlipsIdx_3 rKSub3 rKSub2_val (by decide)
    hsSplitDisj_3 cHsFork_3_0 cHsDepth4
    [(0, 6), (3, 7), (2, 8), (4, 9), (1, 10)] ⟨5, by decide⟩
    hsWords_3_5 β hOH hr rfl rfl rfl rfl (by decide)
    (cHsDepth4_node_10 β hOH fun l ↦ hr l.castSucc)
theorem cHsDepth2_node_0 (β : BitAssignment 128) (hOH : OneHotScr21 0 β)
    (hr : ∀ i : Fin 4, β (rKSub4 i) = 0) : cHsDepth2.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 4), sbmAmp 4 hsWords_2_0 j • ket (writeReg β rKSub4 (basisBits 4 j)) :=
  hsSplitStitch_onehot 44 hsBranchesIdx_2 hsFlipsIdx_2 rKSub4 rKSub3_val (by decide)
    hsSplitDisj_2 cHsFork_2_0 cHsDepth3 [] [(2, 4), (1, 5)]
    ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide) hstPoolOdds_4 hsWords_2_0
    β hOH hr rfl rfl length_hstPoolOdds_4 oddsToHst_hstPoolOdds_4
    rfl (by decide) (by decide) (by decide)
    (cHsDepth3_node_0 β hOH fun l ↦ hr l.castSucc) cHsDepth3_node_1
theorem cHsDepth2_node_1 (β : BitAssignment 128) (hOH : OneHotScr21 2 β)
    (hr : ∀ i : Fin 4, β (rKSub4 i) = 0) : cHsDepth2.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 4), sbmAmp 4 hsWords_2_1 j • ket (writeReg β rKSub4 (basisBits 4 j)) :=
  hsSplitStitch_onehot 44 hsBranchesIdx_2 hsFlipsIdx_2 rKSub4 rKSub3_val (by decide)
    hsSplitDisj_2 cHsFork_2_0 cHsDepth3 [(0, 3)] [(1, 5)]
    ⟨2, by decide⟩ ⟨4, by decide⟩ (by decide) hstPoolOdds_5 hsWords_2_1
    β hOH hr rfl rfl length_hstPoolOdds_5 oddsToHst_hstPoolOdds_5
    rfl (by decide) (by decide) (by decide)
    (cHsDepth3_node_2 β hOH fun l ↦ hr l.castSucc) cHsDepth3_node_3
theorem cHsDepth2_node_2 (β : BitAssignment 128) (hOH : OneHotScr21 1 β)
    (hr : ∀ i : Fin 4, β (rKSub4 i) = 0) : cHsDepth2.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 4), sbmAmp 4 hsWords_2_2 j • ket (writeReg β rKSub4 (basisBits 4 j)) :=
  hsSplitStitch_onehot 44 hsBranchesIdx_2 hsFlipsIdx_2 rKSub4 rKSub3_val (by decide)
    hsSplitDisj_2 cHsFork_2_0 cHsDepth3 [(0, 3), (2, 4)] []
    ⟨1, by decide⟩ ⟨5, by decide⟩ (by decide) hstPoolOdds_6 hsWords_2_2
    β hOH hr rfl rfl length_hstPoolOdds_6 oddsToHst_hstPoolOdds_6
    rfl (by decide) (by decide) (by decide)
    (cHsDepth3_node_4 β hOH fun l ↦ hr l.castSucc) cHsDepth3_node_5
theorem cHsDepth1_node_0 (β : BitAssignment 128) (hOH : OneHotScr21 0 β)
    (hr : ∀ i : Fin 5, β (rKSub5 i) = 0) : cHsDepth1.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 5), sbmAmp 5 hsWords_1_0 j • ket (writeReg β rKSub5 (basisBits 5 j)) :=
  hsSplitStitch_onehot 40 hsBranchesIdx_1 hsFlipsIdx_1 rKSub5 rKSub4_val (by decide)
    hsSplitDisj_1 cHsFork_1_0 cHsDepth2 [] []
    ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide) hstPoolOdds_3 hsWords_1_0
    β hOH hr rfl rfl length_hstPoolOdds_3 oddsToHst_hstPoolOdds_3
    rfl (by decide) (by decide) (by decide)
    (cHsDepth2_node_0 β hOH fun l ↦ hr l.castSucc) cHsDepth2_node_1
theorem cHsDepth1_node_1 (β : BitAssignment 128) (hOH : OneHotScr21 1 β)
    (hr : ∀ i : Fin 5, β (rKSub5 i) = 0) : cHsDepth1.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 5), sbmAmp 5 hsWords_1_1 j • ket (writeReg β rKSub5 (basisBits 5 j)) :=
  hsSplitStitch_zero 40 hsBranchesIdx_1 hsFlipsIdx_1 rKSub5 rKSub4_val (by decide)
    hsSplitDisj_1 cHsFork_1_0 cHsDepth2 [(0, 2)] ⟨1, by decide⟩
    hsWords_1_1 β hOH hr rfl rfl rfl rfl (by decide)
    (cHsDepth2_node_2 β hOH fun l ↦ hr l.castSucc)
theorem cHsDepth0_node_0 (β : BitAssignment 128) (hOH : OneHotScr21 0 β)
    (hr : ∀ i : Fin 6, β (rKSub6 i) = 0) : cHsDepth0.eval.1.mulVec (ket β) = ∑ j : Fin
    (2 ^ 6), sbmAmp 6 hsWords_0_0 j • ket (writeReg β rKSub6 (basisBits 6 j)) :=
  hsSplitStitch_onehot 38 hsBranchesIdx_0 hsFlipsIdx_0 rKSub6 rKSub5_val (by decide)
    hsSplitDisj_0 cHsFork_0_0 cHsDepth1 [] []
    ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) hstPoolOdds_2 hsWords_0_0
    β hOH hr rfl rfl length_hstPoolOdds_2 oddsToHst_hstPoolOdds_2
    rfl (by decide) (by decide) (by decide)
    (cHsDepth1_node_0 β hOH fun l ↦ hr l.castSucc) cHsDepth1_node_1
theorem cLeafHeadShell64_mulVec_ket_one (β : BitAssignment 128) (hc : β wEnHead_128 = 1)
    (hr : ∀ i : Fin 6, β (rK_128 i) = 0) (hscr : ∀ j : Fin 30, β (scr30_128 j) = 0) :
    cLeafHeadShell64.eval.1.mulVec (ket β) = ∑ j : Fin (2 ^ 6), sbmAmp 6 headShell64Words j •
    ket (writeReg β rK_128 (basisBits 6 j)) := by
  set s0w := scr30_128 ⟨0, by decide⟩
  set β0 := Function.update β s0w 1
  have hOH0 : OneHotScr21 0 β0 := fun j _ ↦ by
    dsimp only [β0]
    by_cases hj0 : j.val = 0
    · rw [show scr30_128 j = s0w from congrArg scr30_128 (Fin.ext hj0),
        Function.update_self, ite_eq_left hj0]
    · have hj_ne : scr30_128 j ≠ s0w :=
        fun h ↦ hj0 (congrArg Fin.val (scr30_128.wires.injective h))
      rw [Function.update_of_ne hj_ne, hscr j, ite_eq_right hj0]
  have hr0 : ∀ i : Fin 6, β0 (rKSub6 i) = 0 := fun i ↦ by
    dsimp only [β0, rKSub6]
    rw [Function.update_of_ne (by fin_cases i <;> decide : rK_128 i ≠ s0w), hr i]
  have hs0_not : s0w ∉ Set.range rK_128.wires :=
    not_mem_range_of_val_ge rK_128 rK_128_val s0w (by decide)
  have hc_not : wEnHead_128 ∉ Set.range rK_128.wires :=
    not_mem_range_of_val_ge rK_128 rK_128_val wEnHead_128 (by decide)
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rw [cLeafHeadShell64, lockPosPostVal_eq, cHeadShell64PmSbm_128,
    MeasureBranchHadamardSem.eval_seq_mulVec, MeasureBranchHadamardSem.eval_seq_mulVec,
    ket_cnotIf_ne _ _ (by decide), hscr ⟨0, by decide⟩, hc, zero_add,
    cHsDepth0_node_0 β0 hOH0 hr0, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only [rKSub6, hsWords_0_0]
  rw [Matrix.mulVec_smul, writeReg_update_comm β rK_128 (basisBits 6 j) s0w 1 hs0_not,
    ket_cnotIf_ne _ _ (by decide), Function.update_self,
    Function.update_of_ne (by decide : wEnHead_128 ≠ s0w),
    writeReg_apply_of_not_mem _ _ _ _ hc_not, hc, h11, Function.update_idem,
    upd_eq_self (writeReg β rK_128 (basisBits 6 j)) s0w
      ((writeReg_apply_of_not_mem _ _ _ _ hs0_not).trans (hscr ⟨0, by decide⟩))]
theorem ket_toffIf_ne {n : ℕ} (c1 c2 targ : Wire n) (h12 : c1 ≠ c2) (h1t : c1 ≠ targ)
    (h2t : c2 ≠ targ) (β : BitAssignment n) : (toffIf c1 c2 targ).eval.1.mulVec (ket β) = ket
    (Function.update β targ (β targ + β c1 * β c2)) := by
  simp only [toffIf, h12, h1t, h2t, ↓reduceDIte]
  exact ket_TOFF c1 c2 targ h12 h1t h2t β
theorem ket_H_involutive {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec ((Circuit.H q).eval.1.mulVec (ket β)) = ket β := by
  have hHH : (Circuit.H q ;;ᶜ Circuit.H q).eval = 1 := Subtype.ext (by
    change ((Circuit.single .h q).eval * (Circuit.single .h q).eval).1 = 1
    rw [Circuit.eval_single, ← QRegister.embedUnitary_mul, eval_h_mul_h,
      QRegister.embedUnitary_one, OneMemClass.coe_one])
  rw [← eval_seq_mulVec, hHH, OneMemClass.coe_one, Matrix.one_mulVec]
theorem ket_H_X_H {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec
      ((Circuit.X q).eval.1.mulVec ((Circuit.H q).eval.1.mulVec (ket β))) =
      bitSign (β q) • ket β := by
  have hadd11 : (1 : ZMod 2) + 1 = 0 := rfl
  have h1 := ket_H_involutive q β
  rw [ket_H] at h1 ⊢
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, ket_X,
    Function.update_self, zero_add, hadd11, Function.update_idem] at h1 ⊢
  rcases bit_cases (β q) with hb | hb <;>
    simp only [hb, bitSign, one_ne_zero, ↓reduceIte, one_smul, neg_smul] at h1 ⊢
  · rw [add_comm (Matrix.mulVec _ (ket (Function.update β q 1))), h1]
  · rw [← h1, ← smul_neg]
    congr 1
    abel
theorem ket_cczIf_ne {n : ℕ} (c1 c2 targ : Wire n) (h12 : c1 ≠ c2) (h1t : c1 ≠ targ)
    (h2t : c2 ≠ targ) (β : BitAssignment n) : (cczIf c1 c2 targ).eval.1.mulVec (ket β) =
    bitSign (β c1 * β c2 * β targ) • ket β := by
  rw [cczIf, eval_seq_mulVec, eval_seq_mulVec]
  rcases bit_cases (β c1 * β c2) with hprod | hprod
  · have h0 (b : ZMod 2) :
        (toffIf c1 c2 targ).eval.1.mulVec (ket (Function.update β targ b)) =
          ket (Function.update β targ b) := by
      rw [ket_toffIf_ne c1 c2 targ h12 h1t h2t,
        Function.update_of_ne h1t, Function.update_of_ne h2t, hprod,
        Function.update_self, add_zero, Function.update_idem]
    have hmid : (toffIf c1 c2 targ).eval.1.mulVec ((Circuit.H targ).eval.1.mulVec (ket β)) =
        (Circuit.H targ).eval.1.mulVec (ket β) := by
      rw [ket_H]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, h0 0, h0 1]
    rw [hmid, ket_H_involutive, hprod, zero_mul]
    simp [bitSign]
  · have h1 (b : ZMod 2) :
        (toffIf c1 c2 targ).eval.1.mulVec (ket (Function.update β targ b)) =
          (Circuit.X targ).eval.1.mulVec (ket (Function.update β targ b)) := by
      rw [ket_toffIf_ne c1 c2 targ h12 h1t h2t, ket_X,
        Function.update_of_ne h1t, Function.update_of_ne h2t, hprod]
    have hmid : (toffIf c1 c2 targ).eval.1.mulVec ((Circuit.H targ).eval.1.mulVec (ket β)) =
        (Circuit.X targ).eval.1.mulVec ((Circuit.H targ).eval.1.mulVec (ket β)) := by
      rw [ket_H]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, h1 0, h1 1]
    rw [hmid, ket_H_X_H, hprod, one_mul]
theorem ket_cFinishXorToff_128 (isMerged218 : Bool) (β : BitAssignment 128) :
    (cFinishXorToff_128 isMerged218).eval.1.mulVec (ket β) =
      ket (finishXorMap128 isMerged218 β) := by
  cases isMerged218 <;>
  · rw [cFinishXorToff_128]
    iterate 5 rw [eval_seq_mulVec]
    rw [ket_toffIf_ne _ _ _ (by decide) (by decide) (by decide),
      ket_toffIf_ne _ _ _ (by decide) (by decide) (by decide),
      ket_toffIf_ne _ _ _ (by decide) (by decide) (by decide),
      ket_toffIf_ne _ _ _ (by decide) (by decide) (by decide),
      ket_toffIf_ne _ _ _ (by decide) (by decide) (by decide),
      ket_toffIf_ne _ _ _ (by decide) (by decide) (by decide)]
    refine congrArg ket (funext fun w ↦ ?_)
    by_cases hw : w = wP80_128 ⟨75, by decide⟩ ∨ w = wP80_128 ⟨76, by decide⟩ ∨
        w = wP80_128 ⟨77, by decide⟩ ∨ w = rB1_128 ⟨0, by decide⟩ ∨
        w = rB1_128 ⟨1, by decide⟩ ∨ w = rB1_128 ⟨2, by decide⟩
    · rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [finishXorMap128, wP80_128, rB1_128, rB0_128, wEnS0_128, wEnTail_128,
          wEnS0Tail_128]
    · push Not at hw
      rcases hw with ⟨h1, h2, h3, h4, h5, h6⟩
      dsimp only [finishXorMap128]
      iterate 2 rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
        Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
private theorem ket_ite_upd_t01 (cond : Prop) [Decidable cond] (c : Circuit 128)
    (hc : ∀ δ : BitAssignment 128, ∃ v : ZMod 2,
      c.eval.1.mulVec (ket δ) = ket (Function.update δ wPopT01_128 v))
    (δ : BitAssignment 128) :
    ∃ v : ZMod 2, (if cond then c else Circuit.identity).eval.1.mulVec (ket δ) =
      ket (Function.update δ wPopT01_128 v) := by
  split_ifs
  · exact hc δ
  · exact ⟨δ wPopT01_128, by
      rw [Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec,
        upd_eq_self δ wPopT01_128 rfl]⟩
private theorem ket_emitSigXor_ex (δ : Anf4) (γ : BitAssignment 128) :
    ∃ v : ZMod 2, (emitSigXor_128 δ).eval.1.mulVec (ket γ) =
      ket (Function.update γ wPopT01_128 v) := by
  have hx : ∀ η : BitAssignment 128, ∃ v : ZMod 2,
      (Circuit.X wPopT01_128).eval.1.mulVec (ket η) = ket (Function.update η wPopT01_128 v) :=
    fun η ↦ ⟨_, ket_X wPopT01_128 η⟩
  have hcn : ∀ (q : Wire 128) (hq : q ≠ wPopT01_128) (η : BitAssignment 128), ∃ v : ZMod 2,
      (cnotIf q wPopT01_128).eval.1.mulVec (ket η) = ket (Function.update η wPopT01_128 v) :=
    fun q hq η ↦ ⟨_, ket_cnotIf_ne q wPopT01_128 hq η⟩
  rw [emitSigXor_128, eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec]
  obtain ⟨v1, hv1⟩ := ket_ite_upd_t01 (δ.c0 = 1) _ hx γ
  obtain ⟨v2, hv2⟩ := ket_ite_upd_t01 (δ.cd = 1) _ (hcn wPopPar_128 (by decide))
    (Function.update γ wPopT01_128 v1)
  obtain ⟨v3, hv3⟩ := ket_ite_upd_t01 (δ.cm = 1) _ (hcn wPopMaj_128 (by decide))
    (Function.update (Function.update γ wPopT01_128 v1) wPopT01_128 v2)
  obtain ⟨v4, hv4⟩ := ket_ite_upd_t01 (δ.cmp = 1) _ (hcn wBrTop_128 (by decide))
    (Function.update (Function.update (Function.update γ wPopT01_128 v1) wPopT01_128 v2)
      wPopT01_128 v3)
  refine ⟨v4, ?_⟩
  rw [hv1, hv2, hv3, hv4]
  simp only [Function.update_idem]
private theorem ket_carryPrefix_keep (γ₀ : BitAssignment 128)
    (hscr : ∀ j : Fin 30, γ₀ (scr30_128 j) = 0) :
    ∀ (k : ℕ) (hk : k ≤ 30), ∃ γ : BitAssignment 128,
      (carryPrefix k hk).1.eval.1.mulVec (ket γ₀) = ket γ ∧
      ∀ w : Wire 128, 86 + k ≤ w.val → w.val ≤ 123 → γ w = γ₀ w
  | 0, _ =>
      ⟨γ₀, by simp [carryPrefix, Circuit.eval_identity], fun _ _ _ ↦ rfl⟩
  | i + 1, hi => by
      obtain ⟨γ, ih, hγ⟩ := ket_carryPrefix_keep γ₀ hscr i (Nat.le_of_succ_le hi)
      dsimp only [carryPrefix]
      set prev := carryPrefix i (Nat.le_of_succ_le hi)
      set fi := rFine30_128 ⟨i, hi⟩
      set ciOut := scr30_128 ⟨i, hi⟩
      set a := anfOfStage i
      have hfi_val : (fi.val : ℕ) = 38 + i := rfl
      have hco_val : (ciOut.val : ℕ) = 86 + i := rfl
      have h124 : wPopT01_128.val = 124 := rfl
      have hco0 : γ ciOut = 0 := (hγ ciOut (by omega) (by omega)).trans (hscr ⟨i, hi⟩)
      have hne_fi_co : fi ≠ ciOut := ne_of_apply_ne Fin.val (by omega)
      have hne_sig_co : wPopT01_128 ≠ ciOut := ne_of_apply_ne Fin.val (by omega)
      have hkeep_upd (η : BitAssignment 128) (u : Wire 128) (v : ZMod 2)
          (hu : u = fi ∨ u = ciOut ∨ u = wPopT01_128)
          (hη : ∀ w : Wire 128, 86 + (i + 1) ≤ w.val → w.val ≤ 123 → η w = γ₀ w)
          (w : Wire 128) (hw1 : 86 + (i + 1) ≤ w.val) (hw2 : w.val ≤ 123) :
          Function.update η u v w = γ₀ w := by
        rcases hu with rfl | rfl | rfl <;>
          rw [Function.update_of_ne (ne_of_apply_ne Fin.val (by omega))] <;>
          exact hη w hw1 hw2
      have hγ_next : ∀ w : Wire 128, 86 + (i + 1) ≤ w.val → w.val ≤ 123 → γ w = γ₀ w :=
        fun w hw1 hw2 ↦ hγ w (by omega) hw2
      by_cases h0 : i = 0
      · subst h0
        simp only [↓reduceDIte]
        obtain ⟨v, hv⟩ := ket_emitSigXor_ex (anfXor prev.2 a) γ
        rw [eval_seq_mulVec, eval_seq_mulVec, ih, hv,
          ket_andComputeIf_of_zero fi wPopT01_128 ciOut hne_fi_co hne_sig_co _
            ((Function.update_of_ne hne_sig_co.symm v γ).trans hco0)]
        exact ⟨_, rfl, hkeep_upd _ _ _ (Or.inr (Or.inl rfl))
          (hkeep_upd _ _ _ (Or.inr (Or.inr rfl)) hγ_next)⟩
      · simp only [h0, ↓reduceDIte]
        set ciIn := scr30_128 ⟨i - 1, by omega⟩
        have hci_val : (ciIn.val : ℕ) = 86 + (i - 1) := rfl
        have hne_fi_ci : fi ≠ ciIn := ne_of_apply_ne Fin.val (by omega)
        have hne_ci_co : ciIn ≠ ciOut := ne_of_apply_ne Fin.val (by omega)
        have hne_ci_sig : ciIn ≠ wPopT01_128 := ne_of_apply_ne Fin.val (by omega)
        by_cases ha0 : a = anfZero
        · rw [ite_eq_left ha0, eval_seq_mulVec, ih,
            ket_andComputeIf_of_zero fi ciIn ciOut hne_fi_co hne_ci_co γ hco0]
          exact ⟨_, rfl, hkeep_upd _ _ _ (Or.inr (Or.inl rfl)) hγ_next⟩
        · by_cases ha1 : a = anfOne
          · rw [ite_eq_right ha0, ite_eq_left ha1]
            iterate 4 rw [eval_seq_mulVec]
            rw [ih, ket_X, ket_andComputeIf_of_zero fi ciIn ciOut hne_fi_co hne_ci_co _
              ((Function.update_of_ne hne_fi_co.symm _ γ).trans hco0),
              ket_X, ket_cnotIf_ne fi ciOut hne_fi_co]
            exact ⟨_, rfl, hkeep_upd _ _ _ (Or.inr (Or.inl rfl))
              (hkeep_upd _ _ _ (Or.inl rfl)
                (hkeep_upd _ _ _ (Or.inr (Or.inl rfl))
                  (hkeep_upd _ _ _ (Or.inl rfl) hγ_next)))⟩
          · rw [ite_eq_right ha0, ite_eq_right ha1]
            obtain ⟨v, hv⟩ := ket_emitSigXor_ex (anfXor prev.2 a) γ
            iterate 7 rw [eval_seq_mulVec]
            rw [ih, hv,
              ket_cnotIf_ne ciIn fi hne_fi_ci.symm,
              ket_cnotIf_ne ciIn wPopT01_128 hne_ci_sig,
              ket_andComputeIf_of_zero fi wPopT01_128 ciOut hne_fi_co hne_sig_co _
                (by simp only [Function.update_of_ne hne_sig_co.symm,
                  Function.update_of_ne hne_fi_co.symm, hco0]),
              ket_cnotIf_ne ciIn fi hne_fi_ci.symm,
              ket_cnotIf_ne ciIn wPopT01_128 hne_ci_sig,
              ket_cnotIf_ne ciIn ciOut hne_ci_co]
            exact ⟨_, rfl, hkeep_upd _ _ _ (Or.inr (Or.inl rfl))
              (hkeep_upd _ _ _ (Or.inr (Or.inr rfl))
                (hkeep_upd _ _ _ (Or.inl rfl)
                  (hkeep_upd _ _ _ (Or.inr (Or.inl rfl))
                    (hkeep_upd _ _ _ (Or.inr (Or.inr rfl))
                      (hkeep_upd _ _ _ (Or.inl rfl)
                        (hkeep_upd _ _ _ (Or.inr (Or.inr rfl)) hγ_next))))))⟩
private theorem ket_cPopBasis_keep (β : BitAssignment 128)
    (hmaj : β wPopMaj_128 = 0) (htop : β wBrTop_128 = 0) :
    ∃ γ₀ : BitAssignment 128, cPopBasis_128.eval.1.mulVec (ket β) = ket γ₀ ∧
      ∀ w : Wire 128, 86 ≤ w.val → w.val ≤ 123 → γ₀ w = β w := by
  rw [cPopBasis_128]
  iterate 9 rw [eval_seq_mulVec]
  rw [ket_cnotIf_ne _ _ (by decide), ket_cnotIf_ne _ _ (by decide),
    ket_cnotIf_ne _ _ (by decide), ket_cnotIf_ne _ _ (by decide),
    ket_cnotIf_ne _ _ (by decide),
    ket_andComputeIf_of_zero _ _ _ (by decide) (by decide) _
      (by simp only [Function.update_of_ne
            (by decide : wPopMaj_128 ≠ rB1_128 ⟨2, Nat.lt_succ_self 2⟩),
        Function.update_of_ne
          (by decide : wPopMaj_128 ≠ rB1_128 ⟨1, Nat.lt_of_sub_eq_succ rfl⟩),
        Function.update_of_ne (by decide : wPopMaj_128 ≠ wPopPar_128), hmaj]),
    ket_cnotIf_ne _ _ (by decide), ket_cnotIf_ne _ _ (by decide),
    ket_cnotIf_ne _ _ (by decide),
    ket_andComputeIf_of_zero _ _ _ (by decide) (by decide) _
      (by simp only [Function.update_of_ne (by decide : wBrTop_128 ≠ wPopMaj_128),
        Function.update_of_ne (by decide : wBrTop_128 ≠ rB1_128 ⟨2, Nat.lt_succ_self 2⟩),
        Function.update_of_ne
          (by decide : wBrTop_128 ≠ rB1_128 ⟨1, Nat.lt_of_sub_eq_succ rfl⟩),
        Function.update_of_ne (by decide : wBrTop_128 ≠ wPopPar_128), htop])]
  refine ⟨_, rfl, fun w hw1 hw2 ↦ ?_⟩
  have hb1 : (rB1_128 ⟨1, by decide⟩).val < 86 := by decide
  have hb2 : (rB1_128 ⟨2, by decide⟩).val < 86 := by decide
  have hpar_v : 124 ≤ wPopPar_128.val := by decide
  have hmaj_v : 124 ≤ wPopMaj_128.val := by decide
  have htop_v : 124 ≤ wBrTop_128.val := by decide
  simp only [Function.update_of_ne (ne_of_apply_ne Fin.val (by omega) : w ≠ rB1_128 ⟨1, by decide⟩),
    Function.update_of_ne (ne_of_apply_ne Fin.val (by omega) : w ≠ rB1_128 ⟨2, by decide⟩),
    Function.update_of_ne (ne_of_apply_ne Fin.val (by omega) : w ≠ wPopPar_128),
    Function.update_of_ne (ne_of_apply_ne Fin.val (by omega) : w ≠ wPopMaj_128),
    Function.update_of_ne (ne_of_apply_ne Fin.val (by omega) : w ≠ wBrTop_128)]
private theorem ket_cCarry32_keep_enTail (β : BitAssignment 128)
    (hscr : ∀ j : Fin 30, β (scr30_128 j) = 0)
    (hmaj : β wPopMaj_128 = 0) (htop : β wBrTop_128 = 0) :
    ∃ γ₁ : BitAssignment 128, cCarry32_128.eval.1.mulVec (ket β) = ket γ₁ ∧
      γ₁ wEnTail_128 = β wEnTail_128 := by
  obtain ⟨γ₀, hpop, hγ₀⟩ := ket_cPopBasis_keep β hmaj htop
  have hscr0 : ∀ j : Fin 30, γ₀ (scr30_128 j) = 0 := fun j ↦ by
    have hv := scr30_128_val j
    have hj := j.isLt
    exact (hγ₀ _ (by omega) (by omega)).trans (hscr j)
  obtain ⟨γ, hcp, hγ⟩ := ket_carryPrefix_keep γ₀ hscr0 30 le_rfl
  obtain ⟨v, hemit⟩ := ket_emitSigXor_ex (carryPrefix 30 le_rfl).2 γ
  refine ⟨Function.update γ wPopT01_128 v,
    by rw [cCarry32_128, eval_seq_mulVec, eval_seq_mulVec, hpop, hcp, hemit], ?_⟩
  rw [Function.update_of_ne (by decide : wEnTail_128 ≠ wPopT01_128)]
  exact (hγ wEnTail_128 (by decide) (by decide)).trans (hγ₀ wEnTail_128 (by decide) (by decide))
theorem preservesSpan_inv_seq {n : ℕ} {P Q R : BitAssignment n → Prop}
    {c₁ c₂ : Circuit n}
    (h₂ : PreservesSpan P Q c₂.inverse) (h₁ : PreservesSpan Q R c₁.inverse) :
    PreservesSpan P R (c₁ ;;ᶜ c₂).inverse := fun β hβ ↦ by
  have hev : ((c₁ ;;ᶜ c₂).inverse).eval.1 = c₁.inverse.eval.1 * c₂.inverse.eval.1 := by
    rw [Circuit.eval_inverse, Circuit.eval_seq, _root_.mul_inv_rev,
      ← Circuit.eval_inverse, ← Circuit.eval_inverse]
    rfl
  rw [hev, ← Matrix.mulVec_mulVec]
  exact mulVec_mem_ketSpan c₁.inverse.eval.1 h₁ (h₂ β hβ)
theorem H_inv_eval {n : ℕ} (q : Wire n) :
    (Circuit.H q).inverse.eval = (Circuit.H q).eval := by
  rw [Circuit.eval_inverse]
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  change ((Circuit.single .h q).eval * (Circuit.single .h q).eval).1 = 1
  rw [Circuit.eval_single, ← QRegister.embedUnitary_mul, eval_h_mul_h,
    QRegister.embedUnitary_one, OneMemClass.coe_one]
theorem ctrlProbIf_inv_eval {n : ℕ} (w : List HSTGate) (c t : Wire n) :
    (ctrlProbIf w c t).inverse.eval = (ctrlProbIf w c t).eval := by
  rw [Circuit.eval_inverse]
  refine inv_eq_of_mul_eq_one_right ?_
  unfold ctrlProbIf
  split_ifs with hct
  · simp [Circuit.eval_identity]
  · have hXsq : (Circuit.CNOT c t hct).eval * (Circuit.CNOT c t hct).eval = 1 :=
      Subtype.ext <| MeasureBranchHadamardSem.matrix_ext_ket fun β ↦ by
        change ((Circuit.CNOT c t hct).eval.1 * (Circuit.CNOT c t hct).eval.1).mulVec (ket β) =
          (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ).mulVec (ket β)
        rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, ket_CNOT, ket_CNOT,
          Function.update_of_ne hct, Function.update_self, add_assoc, zmod2_add_self, add_zero,
          Function.update_idem, upd_eq_self β t rfl]
    set u := (hstWordCircuit w t).eval
    set x := (Circuit.CNOT c t hct).eval
    have hev : (ctrlProbGate w c t hct).eval = u * (x * u⁻¹) := by
      simp only [ctrlProbGate, Circuit.eval_seq, Circuit.eval_inverse, mul_assoc, u, x]
    rw [hev]
    calc (u * (x * u⁻¹)) * (u * (x * u⁻¹))
        = u * (x * (u⁻¹ * u) * x * u⁻¹) := by simp only [mul_assoc]
      _ = u * ((x * x) * u⁻¹) := by rw [inv_mul_cancel, mul_one, mul_assoc]
      _ = 1 := by rw [hXsq, one_mul, mul_inv_cancel]
theorem preservesSpan_H {n : ℕ} {P : BitAssignment n → Prop}
    (q : Wire n) (hq : WireIndep P q) :
    PreservesSpan P P (Circuit.H q) := fun β hβ ↦ by
  rw [ket_H]
  exact (KetSpan P).smul_mem _ ((KetSpan P).add_mem (ket_mem_ketSpan (hq β 0 hβ)) ((KetSpan
    P).smul_mem _ (ket_mem_ketSpan (hq β 1 hβ))))
theorem preservesSpan_H_inv {n : ℕ} {P : BitAssignment n → Prop}
    (q : Wire n) (hq : WireIndep P q) :
    PreservesSpan P P (Circuit.H q).inverse := fun β hβ ↦ by
  rw [congrArg Subtype.val (H_inv_eval q)]
  exact preservesSpan_H q hq β hβ
theorem preservesSpan_hadamardReg_inv {n : ℕ} {P : BitAssignment n → Prop} :
    ∀ (m : ℕ) (r : QRegister m n), (∀ i : Fin m, WireIndep P (r i)) →
      PreservesSpan P P (hadamardReg m r).inverse
  | 0, _, _ => fun β hβ ↦ by
      rw [hadamardReg, Circuit.eval_inverse, Circuit.eval_identity, inv_one,
        OneMemClass.coe_one, Matrix.one_mulVec]
      exact ket_mem_ketSpan hβ
  | m + 1, r, hr =>
      preservesSpan_inv_seq
        (preservesSpan_hadamardReg_inv m (qregInit r) (fun i ↦ hr i.castSucc))
        (preservesSpan_H_inv (r (Fin.last m)) (hr (Fin.last m)))
theorem preservesSpan_ctrlProbIf_inv {n : ℕ} {P : BitAssignment n → Prop}
    (w : List HSTGate) (c t : Wire n) (ht : WireIndep P t) :
    PreservesSpan P P (ctrlProbIf w c t).inverse := fun β hβ ↦ by
  rw [congrArg Subtype.val (ctrlProbIf_inv_eval w c t)]
  exact preservesSpan_ctrlProbIf w c t ht β hβ
private theorem cSGood34_mulVec_ket_enZero (auxGood : Bool) (β : BitAssignment 128)
    (hβ : FlagsInv128 β) (hen : β wEnTail_128 = 0) :
    (cSGood34_128 auxGood).eval.1.mulVec (ket β) = ket β := by
  obtain ⟨⟨_, _, _, _, _, _, _, _, _, hmaj, _, htop⟩, hscr⟩ := (flagsInv_iff β).mp hβ
  obtain ⟨γ₁, hFwd, hγ_en⟩ := ket_cCarry32_keep_enTail β hscr hmaj htop
  have hInv : cCarry32_128.inverse.eval.1.mulVec (ket γ₁) = ket β :=
    inv_mulVec_ket_of_fwd cCarry32_128 β γ₁ hFwd
  have hγ_en0 : γ₁ wEnTail_128 = 0 := hγ_en.trans hen
  have hadd11 : ∀ x : ZMod 2, x + 1 + 1 = x := by decide
  unfold cSGood34_128
  set c29 := scr30_128 ⟨29, by decide⟩
  have hne12 : wEnTail_128 ≠ wSubReject_128 := by decide
  have hne13 : wEnTail_128 ≠ c29 := by decide
  have hne23 : wSubReject_128 ≠ c29 := by decide
  cases auxGood
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iterate 6 rw [eval_seq_mulVec]
    rw [hFwd, ket_X, ket_X, ket_cczIf_ne wEnTail_128 wSubReject_128 c29 hne12 hne13 hne23,
      Matrix.mulVec_smul, ket_X, Matrix.mulVec_smul, ket_X, Matrix.mulVec_smul]
    simp only [Function.update_self, Function.update_of_ne hne13, Function.update_of_ne hne12,
      Function.update_of_ne hne23, Function.update_of_ne hne23.symm, Function.update_idem,
      hadd11, hγ_en0, zero_mul, bitSign, ↓reduceIte, one_smul]
    have hrest : Function.update (Function.update (Function.update γ₁ wSubReject_128
        (γ₁ wSubReject_128 + 1)) c29 (γ₁ c29)) wSubReject_128 (γ₁ wSubReject_128) = γ₁ := by
      funext w
      by_cases hw1 : w = wSubReject_128 <;> by_cases hw2 : w = c29 <;>
        simp [hw1, hw2, hne23.symm]
    rw [hrest, hInv]
  · simp only [↓reduceIte]
    iterate 6 rw [eval_seq_mulVec]
    simp only [Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec]
    rw [hFwd, ket_X, ket_cczIf_ne wEnTail_128 wSubReject_128 c29 hne12 hne13 hne23,
      Matrix.mulVec_smul, ket_X, Matrix.mulVec_smul]
    simp only [Function.update_self, Function.update_of_ne hne13, Function.update_of_ne hne23,
      Function.update_idem, hadd11, upd_eq_self γ₁ c29 rfl, hγ_en0, zero_mul, bitSign,
      ↓reduceIte, one_smul, hInv]
private theorem ket_xPrefix34_ex (β : BitAssignment 128) :
    ∀ (k : ℕ) (hk : k ≤ 34), ∃ γ : BitAssignment 128,
      (xPrefix34 k hk).eval.1.mulVec (ket β) = ket γ ∧
      ∀ w : Wire 128, 86 ≤ w.val → γ w = β w
  | 0, _ =>
      ⟨β, by simp [xPrefix34, Circuit.eval_identity], fun _ _ ↦ rfl⟩
  | k + 1, hk => by
      obtain ⟨γ, hev, hγ⟩ := ket_xPrefix34_ex β k (Nat.le_of_succ_le hk)
      refine ⟨_, by rw [xPrefix34, eval_seq_mulVec, hev, ket_X], fun w hw ↦ ?_⟩
      have hle := zeroRefl34Wire_val_le68 ⟨k, hk⟩
      rw [Function.update_of_ne (ne_of_apply_ne Fin.val (by omega)), hγ w hw]
private theorem ket_zAndPrefix_enZero (γ : BitAssignment 128)
    (hz : ∀ (s : ℕ) (hs : s ≤ 32), γ (zAccWire s hs) = 0) :
    ∀ (m : ℕ) (hm : m ≤ 32), (zAndPrefix m hm).eval.1.mulVec (ket γ) = ket γ
  | 0, _ => by simp [zAndPrefix, Circuit.eval_identity]
  | m + 1, hm => by
      rw [zAndPrefix, eval_seq_mulVec, ket_zAndPrefix_enZero γ hz m (Nat.le_of_succ_le hm)]
      have hle := zeroRefl34Wire_val_le68 ⟨m, by omega⟩
      have hge := zAccWire_val_ge86 (m + 1) hm
      have hne1 : zAccWire m (Nat.le_of_succ_le hm) ≠ zAccWire (m + 1) hm :=
        fun h ↦ absurd ((zAccWire_eq_iff _ _).mp h) (by omega)
      rw [ket_andComputeIf_of_zero _ _ _ hne1 (ne_of_apply_ne Fin.val (by omega)) γ
          (hz (m + 1) hm),
        hz m (Nat.le_of_succ_le hm), zero_mul, upd_eq_self γ _ (hz (m + 1) hm)]
private theorem cZeroRefl34_mulVec_ket_enZero (β : BitAssignment 128) (hβ : FlagsInv128 β)
    (hen : β wEnTail_128 = 0) : cZeroRefl34_128.eval.1.mulVec (ket β) = ket β := by
  obtain ⟨γ, hx, hγ⟩ := ket_xPrefix34_ex β 34 le_rfl
  obtain ⟨⟨_, _, _, _, _, _, _, _, ht01, hmaj, _, _⟩, hscr⟩ := (flagsInv_iff β).mp hβ
  have hz (s : ℕ) (hs : s ≤ 32) : γ (zAccWire s hs) = 0 := by
    rw [hγ _ (zAccWire_val_ge86 s hs)]
    unfold zAccWire
    split_ifs
    · exact hen
    · exact hscr _
    · exact ht01
    · exact hmaj
  have hSetup : cZeroReflSetup_128.eval.1.mulVec (ket β) = ket γ := by
    rw [cZeroReflSetup_128, eval_seq_mulVec, hx, ket_zAndPrefix_enZero γ hz 32 le_rfl]
  rw [cZeroRefl34_128]
  iterate 3 rw [eval_seq_mulVec]
  rw [hSetup, ket_cczIf_ne wPopMaj_128 (rJoint33_128 ⟨32, by decide⟩) wSubReject_128
      (by decide) (by decide) (by decide),
    show γ wPopMaj_128 = 0 from hz 32 le_rfl, zero_mul, zero_mul, Matrix.mulVec_smul,
    inv_mulVec_ket_of_fwd cZeroReflSetup_128 β γ hSetup, Matrix.mulVec_smul, ket_Z, hen]
  simp [bitSign]
theorem preservesSpan_cPrepA_inv {P : BitAssignment 128 → Prop} (w : List HSTGate)
    (hj : ∀ i : Fin 33, WireIndep P (rJoint33_128 i)) (hs : WireIndep P wSubReject_128) :
    PreservesSpan P P (cPrepA_128 w).inverse := preservesSpan_inv_seq
    (preservesSpan_ctrlProbIf_inv w wEnTail_128 wSubReject_128 hs)
    (preservesSpan_hadamardReg_inv 33 rJoint33_128 hj)
theorem unitary_mul_inv_val {n : ℕ} (u : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : u.1 * (u⁻¹).1
    = 1 := congrArg Subtype.val (mul_inv_cancel u)
theorem unitary_inv_mul_val {n : ℕ} (u : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : (u⁻¹).1 * u.1
    = 1 := congrArg Subtype.val (inv_mul_cancel u)
theorem mulVec_id_on_ketSpan {n : ℕ} {P : BitAssignment n → Prop} (M : Operator (2 ^ n))
    (h : ∀ β : BitAssignment n, P β → M.mulVec (ket β) = ket β) {ψ : Fin (2 ^ n) → ℂ}
    (hψ : ψ ∈ KetSpan P) : M.mulVec ψ = ψ := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      exact h β hβ
  | zero => exact Matrix.mulVec_zero M
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, ihx, ihy]
  | smul c x _ ihx => rw [Matrix.mulVec_smul, ihx]
theorem cJointTailBhmt_mulVec_ket_enZero (w : List HSTGate) (auxGood : Bool)
    (β : BitAssignment 128) (hβ : FlagsInv128 β) (hen : β wEnTail_128 = 0) :
    (cJointTailBhmt_128 w auxGood).eval.1.mulVec (ket β) = ket β := by
  let P0 : BitAssignment 128 → Prop := fun γ ↦ FlagsInv128 γ ∧ γ wEnTail_128 = 0
  have hj0 : ∀ i : Fin 33, WireIndep P0 (rJoint33_128 i) := fun i γ b ⟨hf, he⟩ ↦ by
    have hr := rJoint33_payload_not36 i
    have h120 : wEnTail_128.val = 120 := rfl
    exact ⟨flagsInv_indep_payload_not36 hr γ b hf,
      (Function.update_of_ne (ne_of_apply_ne Fin.val (by omega)) b γ).trans he⟩
  have hs0 : WireIndep P0 wSubReject_128 := fun γ b ⟨hf, he⟩ ↦
    ⟨flagsInv_indep_payload_not36 (by decide) γ b hf,
     (Function.update_of_ne (by decide : wEnTail_128 ≠ wSubReject_128) b γ).trans he⟩
  have hP1 : (ctrlProbIf w wEnTail_128 wSubReject_128).eval.1.mulVec (ket β) = ket β := by
    rw [ctrlProbIf, dite_neg' (by decide : wEnTail_128 ≠ wSubReject_128)]
    exact ctrlProbGate_mulVec_ket_zero w wEnTail_128 wSubReject_128 (by decide) β hen
  have hEnd : (if auxGood then cnotIf wEnTail_128 wSubReject_128 else
    Circuit.identity).eval.1.mulVec
      (ket β) = ket β := by
    cases auxGood
    · simp [Circuit.eval_identity]
    · simp only [↓reduceIte]
      rw [ket_cnotIf_ne wEnTail_128 wSubReject_128 (by decide), hen, add_zero,
        upd_eq_self β wSubReject_128 rfl]
  have hCancel : (cPrepA_128 w).eval.1.mulVec ((cPrepA_128 w).inverse.eval.1.mulVec (ket β)) =
      ket β := by
    rw [Circuit.eval_inverse, Matrix.mulVec_mulVec,
      unitary_mul_inv_val (cPrepA_128 w).eval, Matrix.one_mulVec]
  rw [cJointTailBhmt_128]
  iterate 5 rw [eval_seq_mulVec]
  rw [hP1, cSGood34_mulVec_ket_enZero auxGood β hβ hen,
    mulVec_id_on_ketSpan cZeroRefl34_128.eval.1
      (fun γ ⟨hf, he⟩ ↦ cZeroRefl34_mulVec_ket_enZero γ hf he)
      (preservesSpan_cPrepA_inv w hj0 hs0 β ⟨hβ, hen⟩), hCancel, hEnd]
theorem dotProduct_star_mulVec {N : Type*} [Fintype N] (A : Matrix N N ℂ) (u v : N → ℂ) :
    dotProduct (star (A.mulVec u)) v = dotProduct (star u) (Aᴴ.mulVec v) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul',
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring
theorem dotProduct_star_ket {n : ℕ} (α β : BitAssignment n) :
    dotProduct (star (ket α)) (ket β) = if α = β then 1 else 0 := by
  change dotProduct (star (Pi.single ((basisBitsEquiv n).symm α) (1 : ℂ)))
    (Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ)) = _
  simp only [dotProduct, Pi.star_apply, Pi.single_apply, apply_ite star, star_one, star_zero]
  rw [Finset.sum_eq_single ((basisBitsEquiv n).symm α)]
  · simp [(basisBitsEquiv n).symm.injective.eq_iff]
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem dotProduct_star_smul_left {N : Type*} [Fintype N] (c : ℂ) (u v : N → ℂ) : dotProduct
    (star (c • u)) v = star c * dotProduct (star u) v := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul',
    Finset.mul_sum, mul_assoc]
theorem dotProduct_star_smul_right {N : Type*} [Fintype N] (c : ℂ) (u v : N → ℂ) : dotProduct
    (star u) (c • v) = c * dotProduct (star u) v := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ ↦ by ring
theorem dotProduct_star_add_left {N : Type*} [Fintype N] (u₁ u₂ v : N → ℂ) : dotProduct
    (star (u₁ + u₂)) v = dotProduct (star u₁) v + dotProduct (star u₂) v := by
  simp only [dotProduct, Pi.star_apply, Pi.add_apply, star_add, add_mul,
    Finset.sum_add_distrib]
theorem dotProduct_star_sum_left {N ι : Type*} [Fintype N]
    (s : Finset ι) (f : ι → N → ℂ) (v : N → ℂ) :
    dotProduct (star (∑ i ∈ s, f i)) v = ∑ i ∈ s, dotProduct (star (f i)) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dotProduct]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, dotProduct_star_add_left, ih]
theorem dotProduct_star_sum_right {N ι : Type*} [Fintype N]
    (u : N → ℂ) (s : Finset ι) (g : ι → N → ℂ) :
    dotProduct (star u) (∑ j ∈ s, g j) = ∑ j ∈ s, dotProduct (star u) (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dotProduct]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, dotProduct_add, ih]
theorem bhmt_one_round_mulVec {N : Type*} [Fintype N] [DecidableEq N] (A S R₀ : Matrix N N ℂ)
    (e₀ ψ_good ψ_bad : N → ℂ) (p_good : ℂ) (hAAh : A * Aᴴ = 1) (hAhA : Aᴴ * A = 1)
    (he₀ : dotProduct (star e₀) e₀ = 1) (hsplit : A.mulVec e₀ = ψ_good + ψ_bad)
    (hSg : S.mulVec ψ_good = -ψ_good) (hSb : S.mulVec ψ_bad = ψ_bad) (hR₀ : R₀.mulVec
    (Aᴴ.mulVec (S.mulVec (A.mulVec e₀))) = (2 * dotProduct (star e₀) (Aᴴ.mulVec (S.mulVec
    (A.mulVec e₀)))) • e₀ - Aᴴ.mulVec (S.mulVec (A.mulVec e₀)))
    (hpg : dotProduct (star (A.mulVec e₀)) ψ_good = p_good) : A.mulVec
    (R₀.mulVec (Aᴴ.mulVec (S.mulVec (A.mulVec e₀)))) = (3 - 4 * p_good) • ψ_good +
    (1 - 4 * p_good) • ψ_bad := by
  set ψ₀ := A.mulVec e₀
  have hψ_norm : dotProduct (star ψ₀) ψ₀ = 1 := by
    rw [dotProduct_star_mulVec, Matrix.mulVec_mulVec, hAhA, Matrix.one_mulVec, he₀]
  have hSψ : S.mulVec ψ₀ = ψ₀ - (2 : ℂ) • ψ_good := by
    rw [show ψ₀ = ψ_good + ψ_bad from hsplit, Matrix.mulVec_add, hSg, hSb]
    ext i
    simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hinner : dotProduct (star e₀) (Aᴴ.mulVec (S.mulVec ψ₀)) = 1 - 2 * p_good := by
    rw [← dotProduct_star_mulVec, hSψ, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hψ_norm, hpg]
  have hAAh_vec : A.mulVec (Aᴴ.mulVec (S.mulVec ψ₀)) = S.mulVec ψ₀ := by
    rw [Matrix.mulVec_mulVec, hAAh, Matrix.one_mulVec]
  rw [hR₀, hinner, Matrix.mulVec_sub, Matrix.mulVec_smul, hAAh_vec, hSψ]
  change (2 * (1 - 2 * p_good)) • ψ₀ - (ψ₀ - (2 : ℂ) • ψ_good) = _
  rw [hsplit]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end ConfigInnerAmp
end PosPostPrep80InnerAmpS3
end
end ModPosPostPrep80InnerAmpS3
end PosPostPrep80InnerAmpS3
end
set_option exponentiation.threshold 256
end PosPostPrep80InnerAmpS3_p1

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
