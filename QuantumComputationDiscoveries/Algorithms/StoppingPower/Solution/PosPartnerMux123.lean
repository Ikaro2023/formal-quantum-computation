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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosOrbitToggle288
set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModPosSlots24PartnerMuxZeroT123
@[expose] public section
namespace PosSlots24PartnerMuxZeroT123Alt
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) : (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) : (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end PosSlots24PartnerMuxZeroT123Alt
namespace PosSlots24PartnerMuxZeroT123
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open OctahedralOrbit hiding ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF matrix_ext_ket
  ket_projector_zero
open Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open MeasureBranchHadamardSem (ket bitSign sqrtHalf bit_cases matrix_ext_ket eval_seq_mulVec ket_X
  ket_CNOT ket_TOFF ket_projector_zero projZeroAll ket_projZeroAll projZeroAll_conjTranspose
  RealizesCleanUnitary)
open StreamingBchComparator BchCubeDecoder
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288
instance (priority := 100000) instNeZeroTwoPowZeroT123 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
theorem ite_pos {α : Sort*} {c : Prop} {h : Decidable c} (hc : c) {a b : α} :
    @ite α c h a b = a := by cases h with | isTrue _ => rfl | isFalse hnc => exact absurd hc hnc
theorem ite_neg {α : Sort*} {c : Prop} {h : Decidable c} (hc : ¬ c) {a b : α} :
    @ite α c h a b = b := by cases h with | isTrue hc' => exact absurd hc' hc | isFalse _ => rfl
theorem dite_pos {α : Sort*} {c : Prop} {h : Decidable c} (hc : c) {a : c → α} {b : ¬ c → α} :
    @dite α c h a b = a hc := by cases h with | isTrue _ => rfl | isFalse hnc => exact absurd hc hnc
theorem dite_neg {α : Sort*} {c : Prop} {h : Decidable c} (hc : ¬ c) {a : c → α} {b : ¬ c → α} :
    @dite α c h a b = b hc := by cases h with | isTrue hc' => exact absurd hc' hc | isFalse _ => rfl
def czCircuit {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n :=
  Circuit.H b ;;ᶜ Circuit.CNOT a b h ;;ᶜ Circuit.H b
@[simp] theorem czCircuit_count_toff {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (czCircuit a b h).count PrimitiveGate.TOFF = 0 := by
  simp [czCircuit, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]
@[simp] theorem czCircuit_count_t {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (czCircuit a b h).count PrimitiveGate.T = 0 := by
  simp [czCircuit, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]
theorem sqrtHalf_mul_self_two : (sqrtHalf * sqrtHalf : ℂ) * 2 = 1 := by
  have hsq : √(1 / 2 : ℝ) * √(1 / 2 : ℝ) = 1 / 2 := Real.mul_self_sqrt (by norm_num)
  rw [show (sqrtHalf : ℂ) = ((√(1 / 2 : ℝ) : ℝ) : ℂ) by simp [sqrtHalf], ← Complex.ofReal_mul, hsq]
  norm_num
theorem ket_czCircuit {n : ℕ} (a b : Wire n) (h : a ≠ b) (β : BitAssignment n) :
    (czCircuit a b h).eval.1.mulVec (ket β) = ((-1 : ℂ) ^ (β a * β b).val) • ket β := by
  let g0 := Function.update β b 0
  let g1 := Function.update β b 1
  have hg0b : g0 b = 0 := Function.update_self _ _ _
  have hg1b : g1 b = 1 := Function.update_self _ _ _
  have hg00 : Function.update g0 b 0 = g0 := Function.update_idem _ _ _
  have hg01 : Function.update g0 b 1 = g1 := Function.update_idem _ _ _
  have hg10 : Function.update g1 b 0 = g0 := Function.update_idem _ _ _
  have hg11 : Function.update g1 b 1 = g1 := Function.update_idem _ _ _
  have hg0_eq (hb : β b = 0) : g0 = β :=
    (congrArg (Function.update β b) hb.symm).trans (Function.update_eq_self b β)
  have hg1_eq (hb : β b = 1) : g1 = β :=
    (congrArg (Function.update β b) hb.symm).trans (Function.update_eq_self b β)
  have hH0 : (Circuit.H b).eval.1.mulVec (sqrtHalf • (ket g0 + ket g1)) = ket g0 := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_add,
      MeasureBranchHadamardSem.ket_H b g0,
      MeasureBranchHadamardSem.ket_H b g1,
      hg0b, hg1b, hg00, hg01, hg10, hg11]
    ext idx
    simp [g0, g1, bitSign]
    linear_combination (ket (Function.update β b 0) idx) * sqrtHalf_mul_self_two
  have hH1 : (Circuit.H b).eval.1.mulVec (sqrtHalf • (ket g0 + (-1 : ℂ) • ket g1)) = ket g1 := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      MeasureBranchHadamardSem.ket_H b g0,
      MeasureBranchHadamardSem.ket_H b g1,
      hg0b, hg1b, hg00, hg01, hg10, hg11]
    ext idx
    simp [g0, g1, bitSign]
    linear_combination (ket (Function.update β b 1) idx) * sqrtHalf_mul_self_two
  dsimp only [czCircuit]
  rw [eval_seq_mulVec, eval_seq_mulVec, MeasureBranchHadamardSem.ket_H]
  change (Circuit.H b).eval.1.mulVec
    ((Circuit.CNOT a b h).eval.1.mulVec (sqrtHalf • (ket g0 + bitSign (β b) • ket g1))) = _
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT,
    Matrix.mulVec_smul _ (bitSign (β b)) (ket g1), ket_CNOT,
    show g0 a = β a from Function.update_of_ne h 0 β,
    show g1 a = β a from Function.update_of_ne h 1 β, hg0b, hg1b]
  rcases bit_cases (β a) with ha | ha <;> rcases bit_cases (β b) with hb | hb
  · rw [ha, hb, zero_add, add_zero, hg00, hg11, show bitSign 0 = (1 : ℂ) from rfl,
      one_smul, hH0, hg0_eq hb]
    simp
  · rw [ha, hb, zero_add, add_zero, hg00, hg11, show bitSign 1 = (-1 : ℂ) from rfl, hH1, hg1_eq hb]
    simp
  · rw [ha, hb, zero_add, show (1 : ZMod 2) + 1 = 0 from rfl, hg01, hg10,
      show bitSign 0 = (1 : ℂ) from rfl, one_smul, add_comm (ket g1) (ket g0), hH0, hg0_eq hb]
    simp
  · have hneg : ket g1 + (-1 : ℂ) • ket g0 = (-1 : ℂ) • (ket g0 + (-1 : ℂ) • ket g1) :=
      funext fun _ ↦ by simp
    rw [ha, hb, zero_add, show (1 : ZMod 2) + 1 = 0 from rfl, hg01, hg10,
      show bitSign 1 = (-1 : ℂ) from rfl, hneg, smul_comm sqrtHalf (-1 : ℂ),
      Matrix.mulVec_smul, hH1, hg1_eq hb]
    simp
def parityPrefixXorCircuit {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rSlot : QRegister 18 n) : (k : ℕ) → (hk : k ≤ 18) → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let prev := parityPrefixXorCircuit f j₀ rSlot k (by omega)
      let j : Fin 18 := ⟨k, by omega⟩
      if hne : j ≠ j₀ then
        if f j then
          prev ;;ᶜ Circuit.CNOT (rSlot j) (rSlot j₀) (rSlot.wires.injective.ne hne)
        else prev
      else prev
@[simp] theorem parityPrefixXorCircuit_count_toff {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rSlot : QRegister 18 n) :
    ∀ (k : ℕ) (hk : k ≤ 18),(parityPrefixXorCircuit f j₀ rSlot k hk).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [parityPrefixXorCircuit]
      split_ifs <;> simp [parityPrefixXorCircuit_count_toff f j₀ rSlot k]
@[simp] theorem parityPrefixXorCircuit_count_t {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rSlot : QRegister 18 n) :
    ∀ (k : ℕ) (hk : k ≤ 18),(parityPrefixXorCircuit f j₀ rSlot k hk).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [parityPrefixXorCircuit]
      split_ifs <;> simp [parityPrefixXorCircuit_count_t f j₀ rSlot k]
def otherBitsSum {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18) (rSlot : QRegister 18 n)
    (β : BitAssignment n) : (k : ℕ) → (hk : k ≤ 18) → ZMod 2
  | 0, _ => 0
  | k + 1, hk =>
      let j : Fin 18 := ⟨k, by omega⟩
      otherBitsSum f j₀ rSlot β k (by omega) +
        if j ≠ j₀ ∧ f j = true then β (rSlot j) else 0
theorem parityPrefixXorCircuit_eval_ket {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rSlot : QRegister 18 n) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ 18), (parityPrefixXorCircuit f j₀ rSlot k hk).eval.1.mulVec (ket β) =
      ket (Function.update β (rSlot j₀) (β (rSlot j₀) + otherBitsSum f j₀ rSlot β k hk))
  | 0, _ => by simp [parityPrefixXorCircuit, otherBitsSum, Function.update_eq_self]
  | k + 1, hk => by
      have ih := parityPrefixXorCircuit_eval_ket f j₀ rSlot β k (by omega)
      dsimp only [parityPrefixXorCircuit, otherBitsSum]
      by_cases hne : (⟨k, by omega⟩ : Fin 18) ≠ j₀
      · by_cases hfk : f ⟨k, by omega⟩ = true
        · rw [dite_pos hne, ite_pos hfk, ite_pos ⟨hne, hfk⟩, eval_seq_mulVec, ih, ket_CNOT,
            Function.update_self, Function.update_of_ne (rSlot.wires.injective.ne hne),
            Function.update_idem, add_assoc]
        · rw [dite_pos hne, ite_neg hfk, ih, ite_neg (fun h ↦ hfk h.2), add_zero]
      · rw [dite_neg hne, ih, ite_neg (fun h ↦ hne h.1), add_zero]
theorem otherBitsSum_update_j0 {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rSlot : QRegister 18 n) (β : BitAssignment n) (v : ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ 18),
      otherBitsSum f j₀ rSlot (Function.update β (rSlot j₀) v) k hk =
        otherBitsSum f j₀ rSlot β k hk
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [otherBitsSum]
      rw [otherBitsSum_update_j0 f j₀ rSlot β v k (by omega)]
      by_cases h : (⟨k, by omega⟩ : Fin 18) ≠ j₀ ∧ f ⟨k, by omega⟩ = true
      · rw [ite_pos h, ite_pos h, Function.update_of_ne (rSlot.wires.injective.ne h.1)]
      · rw [ite_neg h, ite_neg h]
theorem j0_add_otherBitsSum_eq_sum {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18) (hf0 : f j₀ = true)
    (rSlot : QRegister 18 n) (β : BitAssignment n) :
    β (rSlot j₀) + otherBitsSum f j₀ rSlot β 18 (le_refl 18) =
      ∑ j : Fin 18, if f j = true then β (rSlot j) else 0 := by
  suffices hsum : ∀ (k : ℕ) (hk : k ≤ 18),
      (if j₀.val < k then β (rSlot j₀) else 0) + otherBitsSum f j₀ rSlot β k hk =
        ∑ j : Fin k, if f ⟨j.val, by omega⟩ = true then β (rSlot ⟨j.val, by omega⟩) else 0 from by
    simpa [j₀.isLt] using hsum 18 (le_refl 18)
  intro k
  induction k with
  | zero =>
      intro _
      simp [otherBitsSum]
  | succ k ih =>
      intro hk
      rw [Fin.sum_univ_castSucc]
      dsimp only [otherBitsSum]
      specialize ih (by omega)
      simp only [Fin.val_castSucc, Fin.val_last]
      by_cases hjk : j₀.val = k
      · rw [ite_pos (by omega : j₀.val < k + 1),
          show (⟨k, by omega⟩ : Fin 18) = j₀ from Fin.ext hjk.symm]
        rw [ite_neg (by omega : ¬ j₀.val < k), zero_add] at ih
        simp [hf0, ih, add_comm]
      · have hne : (⟨k, by omega⟩ : Fin 18) ≠ j₀ := fun h ↦ hjk (congrArg Fin.val h).symm
        rw [if_congr (by omega : (j₀.val < k + 1) ↔ (j₀.val < k)) rfl rfl, ← add_assoc, ih,
          if_congr (and_iff_right hne) rfl rfl]
def slotOneCzCircuit {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (uWire : Wire n) (rSlot : QRegister 18 n) (huS : ∀ j, uWire ≠ rSlot j) : Circuit n :=
  parityPrefixXorCircuit f j₀ rSlot 18 (le_refl 18) ;;ᶜ
  czCircuit uWire (rSlot j₀) (huS j₀) ;;ᶜ
  parityPrefixXorCircuit f j₀ rSlot 18 (le_refl 18)
theorem slotOneCzCircuit_eval_ket {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (hf0 : f j₀ = true) (uWire : Wire n) (rSlot : QRegister 18 n) (huS : ∀ j, uWire ≠ rSlot j)
    (β : BitAssignment n) : (slotOneCzCircuit f j₀ uWire rSlot huS).eval.1.mulVec (ket β) =
    ((-1 : ℂ) ^ (β uWire * ∑ j : Fin 18, if f j = true then β (rSlot j) else 0).val) • ket β := by
  let β₁ := Function.update β (rSlot j₀) (β (rSlot j₀) + otherBitsSum f j₀ rSlot β 18 (le_refl 18))
  have hback : Function.update β₁ (rSlot j₀)
      (β₁ (rSlot j₀) + otherBitsSum f j₀ rSlot β₁ 18 (le_refl 18)) = β := by
    rw [otherBitsSum_update_j0 f j₀ rSlot β _ 18 (le_refl 18)]
    dsimp only [β₁]
    rw [Function.update_self, CharTwo.add_cancel_right, Function.update_idem,
      Function.update_eq_self]
  dsimp only [slotOneCzCircuit]
  rw [eval_seq_mulVec, eval_seq_mulVec, parityPrefixXorCircuit_eval_ket,
    ket_czCircuit, Matrix.mulVec_smul, parityPrefixXorCircuit_eval_ket]
  change ((-1 : ℂ) ^ (β₁ uWire * β₁ (rSlot j₀)).val) •
    ket (Function.update β₁ (rSlot j₀) (β₁ (rSlot j₀) +
      otherBitsSum f j₀ rSlot β₁ 18 (le_refl 18))) = _
  rw [hback]
  dsimp only [β₁]
  rw [Function.update_of_ne (huS j₀), Function.update_self,
    j0_add_otherBitsSum_eq_sum f j₀ hf0 rSlot β]
def toDynWithDyn {Var : Type} {M n : ℕ}
    (v : Var) (r : QRegister M n) (inner : DynamicCircuit Var n) : TempCtx M → DynamicCircuit Var n
  | .hole => inner
  | .seqPre c K => .seq (.circuit (c.onRegister r).toCircuit) (toDynWithDyn v r inner K)
  | .seqPost K c => .seq (toDynWithDyn v r inner K) (.circuit (c.onRegister r).toCircuit)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K =>
      .seq (DynamicCircuit.andCompute (r c₁) (r c₂) (r anc)
          (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a))
        (.seq (toDynWithDyn v r inner K)
          (DynamicCircuit.andUncompute v (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)))
theorem toDynWithDyn_count_toff {Var : Type} {M n : ℕ}
    (v : Var) (r : QRegister M n) (inner : DynamicCircuit Var n)
    (hInner : inner.count PrimitiveGate.TOFF = 0) :
    ∀ K : TempCtx M, (toDynWithDyn v r inner K).count PrimitiveGate.TOFF = 0
  | .hole => hInner
  | .seqPre c K => by
      simp [toDynWithDyn, CliffProg.toCircuit_count_toff,
        toDynWithDyn_count_toff v r inner hInner K]
  | .seqPost K c => by
      simp [toDynWithDyn, CliffProg.toCircuit_count_toff,
        toDynWithDyn_count_toff v r inner hInner K]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K => by
      simp [toDynWithDyn, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, toDynWithDyn_count_toff v r inner hInner K]
theorem toDynWithDyn_count_t {Var : Type} {M n : ℕ}
    (v : Var) (r : QRegister M n) (inner : DynamicCircuit Var n) :
    ∀ K : TempCtx M, (toDynWithDyn v r inner K).count PrimitiveGate.T = 4 * K.countTempAnd +
      inner.count PrimitiveGate.T
  | .hole => by simp [toDynWithDyn, TempCtx.countTempAnd]
  | .seqPre c K => by
      simp [toDynWithDyn, TempCtx.countTempAnd, CliffProg.toCircuit_count_t,
        toDynWithDyn_count_t v r inner K]
  | .seqPost K c => by
      simp [toDynWithDyn, TempCtx.countTempAnd, CliffProg.toCircuit_count_t,
        toDynWithDyn_count_t v r inner K]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K => by
      simp [toDynWithDyn, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, TempCtx.countTempAnd,
        toDynWithDyn_count_t v r inner K]
      ring
theorem toDynWithDyn_preservesStoreConst
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} (v : Var) (r : QRegister M n) (inner : DynamicCircuit Var n)
    (hInner : PreservesStoreConst inner) :
    ∀ K : TempCtx M, PreservesStoreConst (toDynWithDyn v r inner K)
  | .hole => hInner
  | .seqPre _ K => PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (toDynWithDyn_preservesStoreConst v r inner hInner K)
  | .seqPost K _ => PreservesStoreConst.seq
      (toDynWithDyn_preservesStoreConst v r inner hInner K) (PreservesStoreConst.circuit _)
  | .tempAnd c₁ c₂ anc h₁₂ _ _ K =>
      PreservesStoreConst.seq (PreservesStoreConst.circuit _)
        (PreservesStoreConst.seq (toDynWithDyn_preservesStoreConst v r inner hInner K)
          (PreservesStoreConst.andUncompute v (r c₁) (r c₂) (r anc) (r.wires.injective.ne h₁₂)))
theorem realizes_toDynWithDyn_diagComplex {Var : Type} [Fintype Var] [DecidableEq Var]
    {M kExt n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n)
    (rExt : QRegister kExt n) (hDisjExt : rComb.DisjointWires rExt) (remHole : ℕ)
    (hremHole : remHole ≤ M) (probe : TempPhaseProg M)
    (hProbeRem : ∀ rem, ValidCleanRem M rem probe → remHole ≤ rem)
    (hProbeBits : ∀ γ : BitAssignment M, probe.evalBits γ = γ) (inner : DynamicCircuit Var n)
    (U₀ : Unitary (2 ^ n)) (hInner : RealizesCleanUnitary v (projZeroAll remHole (tailScr
    rComb remHole hremHole)) inner U₀) (Φ : BitAssignment M → BitAssignment kExt → ℂ)
    (hInnerKet : ∀ β : BitAssignment n, U₀.1.mulVec (ket β) = Φ (fun idx ↦ β (rComb idx)) (fun
    j ↦ β (rExt j)) • ket β) : ∀ (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M), ValidCleanRem M
    rem (K.plug probe) → ∃ U : Unitary (2 ^ n), RealizesCleanUnitary v
    (projZeroAll rem (tailScr rComb rem hrem)) (toDynWithDyn v rComb inner K) U ∧ ∀ β :
    BitAssignment n, U.1.mulVec (ket β) = Φ (K.fwdBits (fun idx ↦ β (rComb idx)))
    (fun j ↦ β (rExt j)) • ket (writeRegProg β rComb ((K.plug probe).evalBits (fun idx ↦ β
    (rComb idx)))) := by
  have hExtWrite : ∀ (β : BitAssignment n) (f : BitAssignment M),
      (fun j ↦ writeRegProg β rComb f (rExt j)) = fun j ↦ β (rExt j) := fun β f ↦
    funext fun j ↦ writeRegProg_apply_of_not_mem _ _ _ _ fun ⟨idx, hidx⟩ ↦ hDisjExt.ne idx j hidx
  have hread : ∀ (β : BitAssignment n) (f : BitAssignment M),
      (fun idx ↦ writeRegProg β rComb f (rComb idx)) = f :=
    fun _ _ ↦ funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
  have hwidem : ∀ (β : BitAssignment n) (f g : BitAssignment M),
      writeRegProg (writeRegProg β rComb f) rComb g = writeRegProg β rComb g := fun β f g ↦
    funext fun w ↦ by
      by_cases hm : w ∈ Set.range rComb.wires
      · obtain ⟨idx, rfl⟩ := hm
        simp [writeRegProg_apply_reg]
      · simp [writeRegProg_apply_of_not_mem _ _ _ _ hm]
  have hcKet : ∀ (c : CliffProg M) (β : BitAssignment n),
      (c.onRegister rComb).toCircuit.eval.1.mulVec (ket β) =
        ket (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) := fun c β ↦
    (eval_onRegister_prog_ket rComb (.cliff c) β).trans
      (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
  intro K
  induction K with
  | hole =>
      intro rem hrem hv
      refine ⟨U₀, RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose remHole _)
        (projZeroAll_conjTranspose rem _) (projZeroAll_tailScr_sub rComb hremHole hrem
        (hProbeRem rem hv)) hInner, fun β ↦ ?_⟩
      dsimp only [TempCtx.fwdBits, TempCtx.plug]
      rw [hProbeBits]
      have hw : writeRegProg β rComb (fun idx ↦ β (rComb idx)) = β :=
        funext fun w ↦ by
          by_cases hm : w ∈ Set.range rComb.wires
          · obtain ⟨idx, rfl⟩ := hm
            exact writeRegProg_apply_reg _ _ _ _
          · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
      rw [hw]
      exact hInnerKet β
  | seqPre c K₁ ih =>
      intro rem hrem ⟨remMid, hmid, _, hv₁, hpres₁⟩
      obtain ⟨U₁, hReal₁, hKet₁⟩ := ih remMid hmid hv₁
      let cPre := (c.onRegister rComb).toCircuit
      let P₁ := projZeroAll rem (tailScr rComb rem hrem)
      let P₂ := projZeroAll remMid (tailScr rComb remMid hmid)
      have hclean : P₂ * (cPre.eval.1 * P₁) = cPre.eval.1 * P₁ := by
        apply matrix_ext_ket
        intro β
        simp only [P₁, P₂, mul_mulVec_prog, ket_projZeroAll]
        by_cases hz : ∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0
        · simp only [hz, imp_true_iff, ↓reduceIte, cPre, hcKet, ket_projZeroAll]
          have hγ : cleanRem M rem (fun idx ↦ β (rComb idx)) := fun w hw ↦ by
            rw [show w = ⟨(M - rem) + (w.val - (M - rem)), by omega⟩ from
              Fin.ext (Nat.add_sub_of_le hw).symm]
            exact hz ⟨w.val - (M - rem), by omega⟩
          have hout : ∀ j : Fin remMid, writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))
              (tailScr rComb remMid hmid j) = 0 := fun j ↦ by
            dsimp [tailScr]
            rw [writeRegProg_apply_reg]
            exact hpres₁ _ hγ ⟨(M - remMid) + j.val, by omega⟩ (Nat.le_add_right _ _)
          simp only [hout, imp_true_iff, ↓reduceIte]
        · simp only [hz, ↓reduceIte, Matrix.mulVec_zero]
      refine ⟨U₁ * cPre.eval, RealizesCleanUnitary_seq_asym (projZeroAll_conjTranspose rem _)
        (projZeroAll_conjTranspose remMid _) (RealizesCleanUnitary.circuit v P₁ cPre) hReal₁
        hclean, fun β ↦ ?_⟩
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, cPre, hcKet, hKet₁,
        hread, hExtWrite, hwidem]
      rfl
  | seqPost K₁ c ih =>
      intro rem hrem ⟨_, _, hv₁, _, _⟩
      obtain ⟨U₁, hReal₁, hKet₁⟩ := ih rem hrem hv₁
      let P₁ := projZeroAll rem (tailScr rComb rem hrem)
      let P₂ := projZeroAll 0 (tailScr rComb 0 (Nat.zero_le M))
      have hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁ := by
        rw [show P₂ = 1 from matrix_ext_ket fun α ↦ by simp [P₂, ket_projZeroAll], Matrix.one_mul]
      refine ⟨(c.onRegister rComb).toCircuit.eval * U₁,
        RealizesCleanUnitary_seq_asym (projZeroAll_conjTranspose rem _)
          (projZeroAll_conjTranspose 0 _) hReal₁ (RealizesCleanUnitary.circuit v P₂ _) hclean,
        fun β ↦ ?_⟩
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hKet₁, Matrix.mulVec_smul,
        hcKet, hread, hwidem]
      rfl
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      intro rem hrem ⟨hanc_lo, hvBody, hpresBody⟩
      have hanc_lt : anc.val < M := anc.isLt
      let rem' := M - (anc.val + 1)
      have hrem' : rem' ≤ M := by omega
      have hrem1 : rem' + 1 ≤ M := by omega
      obtain ⟨U_body, ihBody, hKetBody⟩ := ih rem' hrem' hvBody
      have hanc_eq : anc = ⟨M - (rem' + 1), by omega⟩ := by
        ext
        dsimp [rem']
        omega
      have hdisj : ∀ j : Fin rem', rComb anc ≠ tailScr rComb rem' hrem' j := fun j h ↦ by
        have hinj := congrArg Fin.val (rComb.wires.injective h)
        dsimp [tailScr, rem'] at hinj
        omega
      let cToff := Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
      let U_clean := cToff.eval * U_body * cToff.eval
      have hReadToff : ∀ β : BitAssignment n, (fun idx ↦ Function.update β (rComb anc)
          (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) (rComb idx)) =
          Function.update (fun idx ↦ β (rComb idx)) anc
            (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) := fun β ↦ funext fun idx ↦ by
        by_cases hia : idx = anc
        · subst hia
          simp [Function.update_self]
        · simp [Function.update_of_ne hia, Function.update_of_ne (rComb.wires.injective.ne hia)]
      have hExtToff : ∀ β : BitAssignment n, (fun j ↦ Function.update β (rComb anc)
          (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) (rExt j)) = fun j ↦ β (rExt j) :=
        fun β ↦ funext fun j ↦ Function.update_of_ne (hDisjExt.ne anc j).symm _ _
      have hCleanKet' : ∀ β : BitAssignment n, U_clean.1.mulVec (ket β) =
          Φ ((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).fwdBits (fun idx ↦ β (rComb idx)))
            (fun j ↦ β (rExt j)) • ket (writeRegProg β rComb
              (((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).plug probe).evalBits
                (fun idx ↦ β (rComb idx)))) := fun β ↦ by
        let γ : BitAssignment M := fun idx ↦ β (rComb idx)
        let β' := Function.update β (rComb anc) (β (rComb anc) + β (rComb c₁) * β (rComb c₂))
        let γ₁ := Function.update γ anc (γ anc + γ c₁ * γ c₂)
        simp only [U_clean, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        change cToff.eval.1.mulVec (U_body.1.mulVec (cToff.eval.1.mulVec (ket β))) = _
        rw [ket_TOFF, show Function.update β (rComb anc) _ = β' from rfl,
          hKetBody β', hReadToff β, hExtToff β, Matrix.mulVec_smul, ket_TOFF]
        let γ₂ := (K₁.plug probe).evalBits γ₁
        refine congrArg (fun b ↦ Φ ((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).fwdBits γ)
          (fun j ↦ β (rExt j)) • ket b) ?_
        change Function.update (writeRegProg β' rComb γ₂) (rComb anc)
            (writeRegProg β' rComb γ₂ (rComb anc) +
              writeRegProg β' rComb γ₂ (rComb c₁) * writeRegProg β' rComb γ₂ (rComb c₂)) =
          writeRegProg β rComb (Function.update γ₂ anc (γ₂ anc + γ₂ c₁ * γ₂ c₂))
        rw [writeRegProg_apply_reg, writeRegProg_apply_reg, writeRegProg_apply_reg]
        funext w
        by_cases hw : w = rComb anc
        · subst hw
          rw [Function.update_self, writeRegProg_apply_reg, Function.update_self]
        · rw [Function.update_of_ne hw]
          by_cases hm : w ∈ Set.range rComb.wires
          · obtain ⟨idx, rfl⟩ := hm
            rw [writeRegProg_apply_reg, writeRegProg_apply_reg,
              Function.update_of_ne (fun h : idx = anc ↦ hw (congrArg rComb h))]
          · rw [writeRegProg_apply_of_not_mem _ _ _ _ hm,
              writeRegProg_apply_of_not_mem _ _ _ _ hm]
            exact Function.update_of_ne hw _ _
      have hstep := RealizesCleanUnitary.withTempAnd_projZeroAll
        v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
        rem' (tailScr rComb rem' hrem') hdisj
        (toDynWithDyn v rComb inner K₁) U_body U_clean ihBody
        (fun β hanc0 _ ↦ by
          simp only [U_clean, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
          symm
          change cToff.eval.1.mulVec (U_body.1.mulVec (cToff.eval.1.mulVec (ket β))) = _
          rw [ket_TOFF, hanc0, zero_add])
        (fun β hanc0 hscr0 ↦ by
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          let β₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
          have hγ₁_clean : cleanRem M rem' β₁ := fun w hw ↦ by
            have hlt : anc.val < w.val := by
              dsimp [rem'] at hw
              omega
            dsimp only [β₁]
            rw [Function.update_of_ne (wire_ne_of_gt hlt),
              show w = ⟨(M - rem') + (w.val - (M - rem')), by omega⟩ from
                Fin.ext (Nat.add_sub_of_le hw).symm]
            exact hscr0 ⟨w.val - (M - rem'), by omega⟩
          obtain ⟨hc₁, hc₂, ha⟩ := hpresBody β₁ hγ₁_clean
          have hfinal_anc :
              (((TempCtx.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).plug probe).evalBits γ) anc = 0 := by
            dsimp only [TempCtx.plug, TempPhaseProg.evalBits]
            change Function.update ((K₁.plug probe).evalBits β₁) anc _ anc = 0
            rw [Function.update_self, ha, hc₁, hc₂]
            simp [β₁, show γ anc = 0 from hanc0, Function.update_self, Function.update_of_ne h₁a,
              Function.update_of_ne h₂a, CharTwo.add_self_eq_zero]
          rw [hCleanKet' β, Matrix.mulVec_smul, ket_projector_zero,
            writeRegProg_apply_reg, hfinal_anc]
          simp)
      exact ⟨U_clean, RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose (rem' + 1) _)
        (projZeroAll_conjTranspose rem _) (projZeroAll_tailScr_sub rComb hrem1 hrem (by omega))
        (by simpa [toDynWithDyn, hanc_eq, ← tailScr_succ rComb rem' hrem1] using hstep), hCleanKet'⟩
theorem realizes_toDynWithDyn_of_valid {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (remHole : ℕ) (hremHole : remHole ≤ M)
    (probe : TempPhaseProg M) (hProbeRem : ∀ rem, ValidCleanRem M rem probe → remHole ≤ rem)
    (hProbeBits : ∀ γ : BitAssignment M, probe.evalBits γ = γ) (inner : DynamicCircuit Var n)
    (U₀ : Unitary (2 ^ n)) (hInner : RealizesCleanUnitary v (projZeroAll remHole (tailScr
    rComb remHole hremHole)) inner U₀) (ph : BitAssignment M → ZMod 2) (hInnerKet : ∀ β :
    BitAssignment n, U₀.1.mulVec (ket β) = ((-1 : ℂ) ^ (ph (fun idx ↦ β (rComb idx))).val) •
    ket β) : ∀ (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M), ValidCleanRem M rem (K.plug probe)
    → ∃ U : Unitary (2 ^ n), RealizesCleanUnitary v (projZeroAll rem (tailScr rComb rem hrem))
    (toDynWithDyn v rComb inner K) U ∧ ∀ β : BitAssignment n, U.1.mulVec (ket β) =
    ((-1 : ℂ) ^ (ph (K.fwdBits (fun idx ↦ β (rComb idx)))).val) • ket (writeRegProg β rComb
    ((K.plug probe).evalBits (fun idx ↦ β (rComb idx)))) :=
  realizes_toDynWithDyn_diagComplex v rComb
    ({ wires := ⟨Fin.elim0, fun i ↦ i.elim0⟩ } : QRegister 0 n)
    (QRegister.disjoint_iff.mpr fun _ j ↦ j.elim0)
    remHole hremHole probe hProbeRem hProbeBits inner U₀ hInner
    (fun γ _ ↦ (-1 : ℂ) ^ (ph γ).val) hInnerKet
abbrev toDynWithCircuit {Var : Type} {M n : ℕ}
    (v : Var) (r : QRegister M n) (leaf : Circuit n) (K : TempCtx M) : DynamicCircuit Var n :=
  toDynWithDyn v r (.circuit leaf) K
instance (priority := 100000) instNeZeroTwoPowPartnerMuxZeroT (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
theorem TempCtx.append_countTempAnd {M : ℕ} :
    ∀ (K₁ K₂ : TempCtx M),(K₁.append K₂).countTempAnd = K₁.countTempAnd + K₂.countTempAnd
  | .hole, _ => by simp [TempCtx.append, TempCtx.countTempAnd]
  | .seqPre _ K₁, K₂ => TempCtx.append_countTempAnd K₁ K₂
  | .seqPost K₁ _, K₂ => TempCtx.append_countTempAnd K₁ K₂
  | .tempAnd _ _ _ _ _ _ K₁, K₂ => by
      simp only [TempCtx.append, TempCtx.countTempAnd, TempCtx.append_countTempAnd K₁ K₂]
      omega
def ctxUnarySplit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (loWire sel : Wire M)
    (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur) (hsel : sel.val < cur) : TempCtx M :=
  let hiWire : Wire M := ⟨cur, by omega⟩
  (ctxTempBit loWire sel hiWire hlo_sel
    (wire_ne_of_lt (by dsimp [hiWire]; omega))
    (wire_ne_of_lt (by dsimp [hiWire]; omega))).append
    (ctxCliffAlloc (.cnot hiWire loWire (wire_ne_of_gt (by dsimp [hiWire]; omega))))
@[simp] theorem ctxUnarySplit_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (loWire sel : Wire M) (hlo_sel : loWire ≠ sel)
    (hlo : loWire.val < cur) (hsel : sel.val < cur) (body : TempPhaseProg M) :
    (ctxUnarySplit cur hcur loWire sel hlo_sel hlo hsel).plug body =
      withUnarySplit cur hcur loWire sel hlo_sel hlo hsel body := rfl
theorem ctxUnarySplit_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (loWire sel : Wire M) (hlo_sel : loWire ≠ sel)
    (hlo : loWire.val < cur) (hsel : sel.val < cur) :
    (ctxUnarySplit cur hcur loWire sel hlo_sel hlo hsel).countTempAnd = 1 := rfl
def ctxUnarySplitRange {M : ℕ} (base L : ℕ) (sel : Wire M) (hsel : sel.val < base)
    (hcur : base + 2 * L ≤ M) :
    (K : ℕ) → (hK : K ≤ L) → TempCtx M
  | 0, _ => .hole
  | K + 1, hK =>
      let idx := L - (K + 1)
      let pos := base + L + idx
      (ctxUnarySplit pos (by dsimp [pos, idx]; omega)
        ⟨base + idx, by dsimp [idx]; omega⟩ sel
        (wire_ne_of_gt (by dsimp; omega))
        (by dsimp [pos]; omega) (by dsimp [pos]; omega)).append
        (ctxUnarySplitRange base L sel hsel hcur K (by omega))
@[simp] theorem ctxUnarySplitRange_plug {M : ℕ} (base L : ℕ) (sel : Wire M)
    (hsel : sel.val < base) (hcur : base + 2 * L ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ L) (body : TempPhaseProg M),
      (ctxUnarySplitRange base L sel hsel hcur K hK).plug body =
        withUnarySplitRange base L sel hsel hcur K hK body
  | 0, _, _ => rfl
  | K + 1, _, body => by
      simp only [ctxUnarySplitRange, withUnarySplitRange, TempCtx.append_plug,
        ctxUnarySplit_plug, ctxUnarySplitRange_plug base L sel hsel hcur K _ body]
theorem ctxUnarySplitRange_countTempAnd {M : ℕ} (base L : ℕ) (sel : Wire M)
    (hsel : sel.val < base) (hcur : base + 2 * L ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ L),
      (ctxUnarySplitRange base L sel hsel hcur K hK).countTempAnd = K
  | 0, _ => rfl
  | K + 1, _ => by
      dsimp only [ctxUnarySplitRange]
      rw [TempCtx.append_countTempAnd, ctxUnarySplit_countTempAnd,
        ctxUnarySplitRange_countTempAnd base L sel hsel hcur K]
      omega
theorem tree_cur_step {d cur M : ℕ} (hcur : cur + 2 ^ (d + 1) ≤ M) : cur + 2 ^ d ≤ M := by
  simp [pow_succ] at hcur; omega
theorem tree_split_step {d cur M : ℕ} (hcur : cur + 2 ^ (d + 1) ≤ M) : cur + 2 * 2 ^ d ≤ M := by
  simp [pow_succ] at hcur; omega
noncomputable abbrev uPosTailAndSlack (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : Unitary (2 ^ posCoreWires) :=
  diagonalSignUnitaryN (tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30)
theorem cleanRem_cast {M r₁ r₂ : ℕ} (h : r₁ = r₂) {γ : BitAssignment M} (hγ : cleanRem M r₁ γ) :
    cleanRem M r₂ γ := h ▸ hγ
theorem cliffDisjoint_of_false {M : ℕ} :
    ∀ c : CliffProg M, CliffDisjoint (fun _ ↦ False) c
  | .nil => trivial
  | .x _ => not_false
  | .cnot _ _ _ => ⟨not_false, not_false⟩
  | .seq c₁ c₂ => ⟨cliffDisjoint_of_false c₁, cliffDisjoint_of_false c₂⟩
theorem cliffProg_supportsBelow_self {M : ℕ} :
    ∀ c : CliffProg M, c.SupportsBelow M
  | .nil => trivial
  | .x w => w.isLt
  | .cnot c t _ => ⟨c.isLt, t.isLt⟩
  | .seq c₁ c₂ => ⟨cliffProg_supportsBelow_self c₁, cliffProg_supportsBelow_self c₂⟩
theorem tempCtx_disjointFrom_false {M : ℕ} :
    ∀ K : TempCtx M, K.DisjointFrom (fun _ ↦ False)
  | .hole => trivial
  | .seqPre c K₁ => ⟨cliffDisjoint_of_false c, tempCtx_disjointFrom_false K₁⟩
  | .seqPost K₁ c => ⟨tempCtx_disjointFrom_false K₁, cliffDisjoint_of_false c⟩
  | .tempAnd _ _ _ _ _ _ K₁ => ⟨not_false, not_false, not_false, tempCtx_disjointFrom_false K₁⟩
theorem tempCtx_supportsBelowCtx_self {M : ℕ} :
    ∀ K : TempCtx M, K.SupportsBelowCtx M
  | .hole => trivial
  | .seqPre c K₁ => ⟨cliffProg_supportsBelow_self c, tempCtx_supportsBelowCtx_self K₁⟩
  | .seqPost K₁ c => ⟨tempCtx_supportsBelowCtx_self K₁, cliffProg_supportsBelow_self c⟩
  | .tempAnd _ _ anc _ _ _ K₁ => ⟨anc.isLt, tempCtx_supportsBelowCtx_self K₁⟩
theorem scopedBlock_fwdBits {M rem : ℕ} (K : TempCtx M)
    (q₀ : Wire M) {s₀ : BitAssignment M → BitAssignment M}
    (h₀ : ScopedBlock M rem s₀ (.z q₀) (K.plug (.z q₀)))
    (q : Wire M) :
    ScopedBlock M rem K.fwdBits (.z q) (K.plug (.z q)) where
  valid := K.plug_validCleanRem (tempCtx_disjointFrom_false K) (tempCtx_supportsBelowCtx_self K)
    (body := .z q) trivial (fun _ _ _ ↦ rfl) q₀ (by simp) h₀.valid
  bits β hβ := funext fun w ↦
    ((K.plug_evalBits_split (tempCtx_disjointFrom_false K) (body := .z q) (fun _ _ _ ↦ rfl) q₀ β).2
      w not_false).trans (congrFun (h₀.bits β hβ) w)
  sign β _ := K.plug_evalSign (.z q) β
theorem neg_one_pow_sum_zmod2 {k : ℕ} (g : Fin k → ZMod 2) :
    (-1 : ℂ) ^ (∑ j : Fin k, g j).val = ∏ j : Fin k, (-1 : ℂ) ^ (g j).val := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, ← TempPhaseProg.neg_one_pow_zmod2_mul, ih, Fin.prod_univ_castSucc]
def RestoresAll {M : ℕ} (K : TempCtx M) : Prop :=
  ∀ (body : TempPhaseProg M),(∀ γ, body.evalBits γ = γ) → ∀ γ, (K.plug body).evalBits γ = γ
theorem RestoresAll.hole {M : ℕ} : RestoresAll (TempCtx.hole : TempCtx M) := fun _ hB γ ↦ hB γ
theorem RestoresAll.append {M : ℕ} {K₁ K₂ : TempCtx M}
    (h₁ : RestoresAll K₁) (h₂ : RestoresAll K₂) : RestoresAll (K₁.append K₂) := fun body hB γ ↦ by
  rw [TempCtx.append_plug]
  exact h₁ (K₂.plug body) (h₂ body hB) γ
theorem RestoresAll.tempBit {M : ℕ} {c₁ c₂ anc : Wire M} (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ anc)
    (h2a : c₂ ≠ anc) : RestoresAll (ctxTempBit c₁ c₂ anc h12 h1a h2a) := fun body hB γ ↦ by
  dsimp only [ctxTempBit, TempCtx.plug, TempPhaseProg.evalBits]
  let γ₁ := Function.update γ anc (γ anc + γ c₁ * γ c₂)
  change Function.update (body.evalBits γ₁) anc _ = γ
  rw [hB γ₁]
  funext w
  by_cases hw : w = anc
  · subst hw
    simp [γ₁, Function.update_self, Function.update_of_ne h1a, Function.update_of_ne h2a,
      add_assoc, CharTwo.add_self_eq_zero]
  · simp [γ₁, Function.update_of_ne hw]
theorem cliffProg_inv_eval {M : ℕ} :
    ∀ (c : CliffProg M) (γ : BitAssignment M), c.inv.eval (c.eval γ) = γ
  | .nil, _ => rfl
  | .x w, γ => by
      dsimp only [CliffProg.inv, CliffProg.eval]
      funext u
      by_cases hu : u = w
      · subst hu
        simp [Function.update_self, add_assoc, CharTwo.add_self_eq_zero]
      · simp [Function.update_of_ne hu]
  | .cnot c t hne, γ => by
      dsimp only [CliffProg.inv, CliffProg.eval]
      funext u
      by_cases hu : u = t
      · subst hu
        simp [Function.update_self, Function.update_of_ne hne,
          add_assoc, CharTwo.add_self_eq_zero]
      · simp [Function.update_of_ne hu]
  | .seq c₁ c₂, γ => by
      dsimp only [CliffProg.inv, CliffProg.eval]
      rw [cliffProg_inv_eval c₂, cliffProg_inv_eval c₁]
theorem RestoresAll.cliffAlloc {M : ℕ} (c : CliffProg M) : RestoresAll (ctxCliffAlloc c) :=
  fun body hB γ ↦ by
    dsimp only [ctxCliffAlloc, TempCtx.plug, TempPhaseProg.evalBits]
    rw [hB (c.eval γ), cliffProg_inv_eval c γ]
theorem RestoresAll.unarySplit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (loWire sel : Wire M)
    (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur) (hsel : sel.val < cur) : RestoresAll
    (ctxUnarySplit cur hcur loWire sel hlo_sel hlo hsel) := RestoresAll.append
    (RestoresAll.tempBit _ _ _) (RestoresAll.cliffAlloc _)
theorem RestoresAll.unarySplitRange {M : ℕ} (base L : ℕ) (sel : Wire M)
    (hsel : sel.val < base) (hcur : base + 2 * L ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ L), RestoresAll (ctxUnarySplitRange base L sel hsel hcur K hK)
  | 0, _ => RestoresAll.hole
  | K + 1, _ => RestoresAll.append (RestoresAll.unarySplit _ _ _ _ _ _ _)
      (RestoresAll.unarySplitRange base L sel hsel hcur K _)
theorem rElecSlot_apply_ofFin {n : ℕ} (rCore : QRegister posCoreWires n) (e : Fin 218) (j : Fin
    18) :
    rElecSlot rCore e j = rCore (rElecSlot (QRegExt.ofFin posCoreWires) e j) := rfl
section ConfigMasterWrapperZeroT
set_option maxRecDepth 16000000
def findTrueBitAux (f : Fin 18 → Bool) : (k : ℕ) → (hk : k ≤ 18) → Option (Fin 18)
  | 0, _ => none
  | k + 1, hk =>
      if f ⟨k, by omega⟩ then some ⟨k, by omega⟩
      else findTrueBitAux f k (by omega)
theorem findTrueBitAux_spec (f : Fin 18 → Bool) :
    ∀ (k : ℕ) (hk : k ≤ 18),
      (∀ j₀, findTrueBitAux f k hk = some j₀ → f j₀ = true) ∧
      (findTrueBitAux f k hk = none → ∀ (i : ℕ) (hi : i < k), f ⟨i, by omega⟩ = false)
  | 0, _ => ⟨fun _ h ↦ by simp [findTrueBitAux] at h, fun _ _ hi ↦ absurd hi (by omega)⟩
  | k + 1, hk => by
      obtain ⟨hs, hn⟩ := findTrueBitAux_spec f k (by omega)
      dsimp only [findTrueBitAux]
      cases hfk : f ⟨k, by omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨hs, fun hnone i hi ↦ ?_⟩
        by_cases hik : i = k
        · subst hik; exact hfk
        · exact hn hnone i (by omega)
      · simp only [↓reduceIte]
        exact ⟨fun j₀ hj ↦ by injection hj with hj'; subst hj'; exact hfk,
          fun h ↦ by simp at h⟩
theorem sign_zmod2_bool_if (b : Bool) (bv : ZMod 2) :
    ((-1 : ℂ) ^ (if b = true then bv else 0).val) =
      if (b && decide (bv ≠ 0)) = true then (-1 : ℂ) else 1 := by
  cases b <;> rcases bit_cases bv with rfl | rfl <;> norm_num
attribute [local irreducible]
  tailOrbitCoord128 rawOrbitCoord128 orbitRankFin16 canonTriple128 tetRank65
  tailAndSlackPhaseBitSpec
noncomputable def sandPhase18 (slot2SwappedTo0 : Bool)
    (midPhase : Fin (2 ^ (posCoreWires + 16)) → Bool)
    (w : Fin (2 ^ (posCoreWires + 18))) : Bool :=
  let bits := basisBits (posCoreWires + 18) w
  let βC : BitAssignment posCoreWires := fun i ↦ bits (Fin.castAdd 18 i)
  let βP : BitAssignment 18 := fun j ↦ bits (Fin.natAdd posCoreWires j)
  let rk := orbitRankFin16 slot2SwappedTo0 βC βP
  midPhase ((basisBitsEquiv (posCoreWires + 16)).symm fun m ↦
    if hm : m.val < posCoreWires then βC ⟨m.val, hm⟩
    else basisBits 16 rk ⟨m.val - posCoreWires, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp hm)
      m.isLt⟩)
attribute [local irreducible] DynCircuitExt.measureXResetAndBranch
end ConfigMasterWrapperZeroT
section ConfigPartner216
set_option maxRecDepth 16000000
def aliasPartner217 (v : ℕ) : ℕ := if v < 217 then v else v - 128
theorem aliasPartner217_lt {v : ℕ} (hv : v < 256) : aliasPartner217 v < 217 := by
  dsimp only [aliasPartner217]
  split_ifs <;> omega
theorem aliasPartner217_of_lt {v : ℕ} (hv : v < 217) : aliasPartner217 v = v := ite_pos hv
noncomputable def partnerTblVal216 (x : Fin (2 ^ posCoreWires)) : Fin (2 ^ 18) :=
  let βL := basisBits posCoreWires x
  let rCoreL := QRegExt.ofFin posCoreWires
  let u := aliasPartner217 (regVal (rPartnerIdx rCoreL) βL)
  have hu : u + 1 < 218 :=
    Nat.succ_lt_succ (aliasPartner217_lt (regVal_lt_two_pow (rPartnerIdx rCoreL) βL))
  (basisBitsEquiv 18).symm fun j ↦ βL (rElecSlot rCoreL ⟨u + 1, hu⟩ j)
theorem basisBits_partnerTblVal216 (x : Fin (2 ^ posCoreWires)) (j : Fin 18) :
    basisBits 18 (partnerTblVal216 x) j =
      basisBits posCoreWires x (rElecSlot (QRegExt.ofFin posCoreWires)
        ⟨aliasPartner217 (regVal (rPartnerIdx (QRegExt.ofFin posCoreWires))
          (basisBits posCoreWires x)) + 1,
          Nat.succ_lt_succ (aliasPartner217_lt (regVal_lt_two_pow _ _))⟩ j) :=
  basisBits_symm_apply_at _ j
theorem rawOrbitCoord128_eq_tailOrbitCoord128_216 (slot2SwappedTo0 : Bool)
    (hSwapped : slot2SwappedTo0 = true) (x : Fin (2 ^ posCoreWires)) (hPart : basisBits
    posCoreWires x (wSlot0Core (QRegExt.ofFin posCoreWires)) = 1 → regVal (rPartnerIdx
    (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x) < 217) : rawOrbitCoord128
    slot2SwappedTo0 (basisBits posCoreWires x) (basisBits 18 (partnerTblVal216 x)) =
    tailOrbitCoord128 slot2SwappedTo0 (basisBits posCoreWires x) := by
  subst hSwapped
  funext w
  ext
  dsimp only [rawOrbitCoord128, tailOrbitCoord128, slotSubGridCoord64, parity3OfReg]
  rcases bit_cases (basisBits posCoreWires x (wSlot0Core (QRegExt.ofFin posCoreWires))) with
    hbs0 | hbs0
  · have hbs0_beq : (basisBits posCoreWires x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) =
        false := by simp [hbs0]
    simp [hbs0_beq, Bool.not]
    rfl
  · have hmLt := hPart hbs0
    have hbs0_beq : (basisBits posCoreWires x (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) =
        true := by simp [hbs0]
    simp only [hbs0_beq, Bool.not, Bool.false_eq_true, ↓reduceIte]
    have hRegEq : regVal (axisBitRev6 (QRegExt.ofFin 18) w) (basisBits 18 (partnerTblVal216 x)) =
        regVal (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires)
          ⟨regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x) % 217 + 1,
            Nat.succ_lt_succ (Nat.mod_lt _ (by decide : 0 < 217))⟩) w)
          (basisBits posCoreWires x) :=
      regVal_congr_cross _ _ _ _ fun j ↦ by
        rw [basisBits_partnerTblVal216]
        refine congrArg (basisBits posCoreWires x) (Fin.ext ?_)
        change 18 * (aliasPartner217 _ + 1) + (6 * w.val + (5 - j.val)) =
          18 * (_ % 217 + 1) + (6 * w.val + (5 - j.val))
        rw [aliasPartner217_of_lt hmLt, Nat.mod_eq_of_lt hmLt]
    rw [hRegEq]
    rfl
theorem succ_le_two_pow : ∀ d : ℕ, d + 1 ≤ 2 ^ d
  | 0 => by decide
  | d + 1 => by
      have := succ_le_two_pow d
      have : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega
def xorUpperToMid {M : ℕ} (cur L : ℕ) (hcur : cur + 2 * L ≤ M) :
    (m : ℕ) → (hm : m + 1 ≤ L) → CliffProg M
  | 0, _ => .nil
  | m + 1, hm =>
      .seq (xorUpperToMid cur L hcur m (by omega))
        (.cnot ⟨cur + L + 1 + m, by omega⟩ ⟨cur + L, by omega⟩
          (wire_ne_of_gt (by dsimp; omega)))
theorem xorUpperToMid_supports {M : ℕ} (cur L : ℕ) (hcur : cur + 2 * L ≤ M) :
    ∀ (m : ℕ) (hm : m + 1 ≤ L),(xorUpperToMid cur L hcur m hm).SupportsBelow (cur + 2 * L)
  | 0, _ => trivial
  | m + 1, hm =>
      ⟨xorUpperToMid_supports cur L hcur m (by omega), by dsimp; omega, by dsimp; omega⟩
theorem xorUpperToMid_eval {M : ℕ} (cur L : ℕ) (hcur : cur + 2 * L ≤ M) (γ : BitAssignment M) :
    ∀ (m : ℕ) (hm : m + 1 ≤ L),
      (∀ w : Wire M, w ≠ ⟨cur + L, by omega⟩ → (xorUpperToMid cur L hcur m hm).eval γ w = γ w) ∧
      (xorUpperToMid cur L hcur m hm).eval γ ⟨cur + L, by omega⟩ =
        γ ⟨cur + L, by omega⟩ + ∑ r : Fin m, γ ⟨cur + L + 1 + r.val, by omega⟩
  | 0, _ => ⟨fun _ _ ↦ rfl, by simp [xorUpperToMid, CliffProg.eval]⟩
  | m + 1, hm => by
      obtain ⟨hOther, hMid⟩ := xorUpperToMid_eval cur L hcur γ m (by omega)
      refine ⟨fun w hw ↦ ?_, ?_⟩
      · dsimp only [xorUpperToMid, CliffProg.eval]
        rw [Function.update_of_ne hw]
        exact hOther w hw
      · dsimp only [xorUpperToMid, CliffProg.eval]
        have hne_src : (⟨cur + L + 1 + m, by omega⟩ : Wire M) ≠ ⟨cur + L, by omega⟩ :=
          wire_ne_of_gt (by dsimp; omega)
        rw [Function.update_self, hMid, hOther _ hne_src, Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, add_assoc]
def mobiusFixZeroCliff {M : ℕ} (cur L : ℕ) (hL : 1 ≤ L) (hcur : cur + 2 * L ≤ M) : CliffProg M :=
  .seq (xorUpperToMid cur L hcur (L - 1) (by omega))
    (.cnot ⟨cur + L, by omega⟩ ⟨cur, by omega⟩ (wire_ne_of_gt (by dsimp; omega)))
theorem mobiusFixZeroCliff_supports {M : ℕ} (cur L : ℕ) (hL : 1 ≤ L) (hcur : cur + 2 * L ≤ M) :
    (mobiusFixZeroCliff cur L hL hcur).SupportsBelow (cur + 2 * L) :=
  ⟨xorUpperToMid_supports cur L hcur (L - 1) (by omega), by dsimp; omega, by dsimp; omega⟩
def ctxMobiusUnaryTree {M : ℕ} :
    (d : ℕ) → (cur : ℕ) → (hcur : cur + 2 ^ d ≤ M) →
    (addr : Fin d → Wire M) → (haddr : ∀ j, (addr j).val < cur) →
    TempCtx M
  | 0, cur, hcur, _, _ =>
      ctxCliffAlloc (.x ⟨cur, by omega⟩)
  | d + 1, cur, hcur, addr, haddr =>
      let L := 2 ^ d
      have hL : 1 ≤ L := Nat.one_le_pow d 2 (by omega)
      have hsp : cur + 2 * L ≤ M := tree_split_step hcur
      let msb := addr (Fin.last d)
      let cSeed : CliffProg M :=
        .cnot msb ⟨cur + L, by omega⟩
          (wire_ne_of_lt (lt_of_lt_of_le (haddr (Fin.last d)) (by dsimp; omega)))
      (ctxMobiusUnaryTree d cur (tree_cur_step hcur)
        (fun j ↦ addr j.castSucc) (fun j ↦ haddr j.castSucc)).append
        ((ctxCliffAlloc cSeed).append
          ((ctxUnarySplitRange cur L msb (haddr (Fin.last d)) hsp (L - 1) (by omega)).append
            (ctxCliffAlloc (mobiusFixZeroCliff cur L hL hsp))))
theorem ctxMobiusUnaryTree_countTempAnd {M : ℕ} :
    ∀ (d cur : ℕ) (hcur : cur + 2 ^ d ≤ M)
      (addr : Fin d → Wire M) (haddr : ∀ j, (addr j).val < cur),
      (ctxMobiusUnaryTree d cur hcur addr haddr).countTempAnd = 2 ^ d - 1 - d
  | 0, _, _, _, _ => rfl
  | d + 1, cur, hcur, addr, haddr => by
      have hpos : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
      dsimp only [ctxMobiusUnaryTree]
      rw [TempCtx.append_countTempAnd, TempCtx.append_countTempAnd, TempCtx.append_countTempAnd,
        ctxMobiusUnaryTree_countTempAnd d cur, ctxUnarySplitRange_countTempAnd]
      change 2 ^ d - 1 - d + (0 + (2 ^ d - 1 + 0)) = 2 ^ (d + 1) - 1 - (d + 1)
      have := succ_le_two_pow d
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega
theorem RestoresAll.mobiusTree {M : ℕ} :
    ∀ (d cur : ℕ) (hcur : cur + 2 ^ d ≤ M)
      (addr : Fin d → Wire M) (haddr : ∀ j, (addr j).val < cur),
      RestoresAll (ctxMobiusUnaryTree d cur hcur addr haddr)
  | 0, _, _, _, _ => RestoresAll.cliffAlloc _
  | d + 1, cur, _, _, _ =>
      RestoresAll.append (RestoresAll.mobiusTree d cur _ _ _)
        (RestoresAll.append (RestoresAll.cliffAlloc _)
          (RestoresAll.append (RestoresAll.unarySplitRange _ _ _ _ _ _ _)
            (RestoresAll.cliffAlloc _)))
theorem ScopedBlock.ctxMobiusUnaryTree_block {M : ℕ} :
    ∀ (d cur : ℕ) (hcur : cur + 2 ^ d ≤ M)
      (addr : Fin d → Wire M) (haddr : ∀ j, (addr j).val < cur)
      (leaf body : TempPhaseProg M) (sBody : BitAssignment M → BitAssignment M),
      ScopedBlock M (M - (cur + 2 ^ d)) sBody leaf body →
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - cur) (fun β ↦ sBody (setup β)) leaf
          ((ctxMobiusUnaryTree d cur hcur addr haddr).plug body) ∧
        ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - (cur + 2 ^ d)) (setup β) ∧
          (∀ w : Wire M, w.val < cur → setup β w = β w) ∧
          (∀ (k : ℕ) (hk : k < 2 ^ d),
            setup β ⟨cur + k, by omega⟩ =
              if k = bitsVal (fun j ↦ β (addr j)) then 1 else 0) := by
  intro d
  induction d with
  | zero =>
      intro cur hcur _ _ _ body sBody hBody
      let cX : CliffProg M := .x ⟨cur, by omega⟩
      refine ⟨cX.eval, ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur)
        (remIn := M - (cur + 1)) (by omega) (by omega) cX (show cur < M - (M - (cur + 1)) by omega)
        (hBody.cast_rem (by norm_num)),
        fun β hβ ↦ ⟨fun w hw ↦ ?_, fun w hw ↦ Function.update_of_ne
          (wire_ne_of_lt hw) _ _, fun k hk ↦ ?_⟩⟩
      · rw [show 2 ^ 0 = 1 from rfl] at hw
        rw [cX.eval_outside (bound := cur + 1) (Nat.lt_succ_self cur) β w (by omega)]
        exact hβ w (by omega)
      · obtain rfl : k = 0 := by omega
        dsimp only [cX]
        simp [CliffProg.eval, hβ ⟨cur, by omega⟩ (show M - (M - cur) ≤ cur by omega), bitsVal]
  | succ d ih =>
      intro cur hcur addr haddr leaf body sBody hBody
      let L := 2 ^ d
      have hL : 1 ≤ L := Nat.one_le_pow d 2 (by omega)
      have hL2 : 2 ^ (d + 1) = 2 * L := by ring
      have hsp : cur + 2 * L ≤ M := tree_split_step hcur
      let msb := addr (Fin.last d)
      have hmsb_lt : msb.val < cur := haddr (Fin.last d)
      let cFix : CliffProg M := mobiusFixZeroCliff cur L hL hsp
      have hFixBlk := ScopedBlock.withCliffAlloc_block (M := M)
        (rem := M - (cur + 2 * L)) (remIn := M - (cur + 2 * L)) (by omega) le_rfl cFix
        (CliffProg.supportsBelow_mono (by omega) (mobiusFixZeroCliff_supports cur L hL hsp))
        (hBody.cast_rem (by omega))
      obtain ⟨sSplit, hSplitBlk, hSpecSplit⟩ :=
        ScopedBlock.withUnarySplitRange_block cur L msb hmsb_lt hsp (L - 1) (by omega)
          leaf (withCliffAlloc cFix body) (sBody ∘ cFix.eval) hFixBlk
      let cSeed : CliffProg M := .cnot msb ⟨cur + L, by omega⟩
        (wire_ne_of_lt (lt_of_lt_of_le hmsb_lt (Nat.le_add_right _ _)))
      have hSeedBlk := ScopedBlock.withCliffAlloc_block (M := M)
        (rem := M - (cur + L)) (remIn := M - (cur + L + 1)) (by omega) (by omega) cSeed
        ⟨lt_of_lt_of_le hmsb_lt (by omega), show cur + L < M - (M - (cur + L + 1)) by omega⟩
        (hSplitBlk.cast_rem (by omega))
      obtain ⟨sTree, hTreeBlk, hSpecTree⟩ := ih cur (tree_cur_step hcur)
        (fun j ↦ addr j.castSucc) (fun j ↦ haddr j.castSucc) leaf _
        (fun β ↦ (sBody ∘ cFix.eval) (sSplit (cSeed.eval β))) hSeedBlk
      have hPlugEq : ((ctxMobiusUnaryTree (d + 1) cur hcur addr haddr).plug body) =
          ((ctxMobiusUnaryTree d cur (tree_cur_step hcur) (fun j ↦ addr j.castSucc) (fun j ↦
          haddr j.castSucc)).plug (withCliffAlloc cSeed (withUnarySplitRange cur L msb hmsb_lt
          hsp (L - 1) (by omega) (withCliffAlloc cFix body)))) := by
        dsimp only [ctxMobiusUnaryTree, L, msb, cSeed, cFix]
        simp only [TempCtx.append_plug, ctxCliffAlloc_plug, ctxUnarySplitRange_plug]
      refine ⟨fun β ↦ cFix.eval (sSplit (cSeed.eval (sTree β))), hPlugEq ▸ hTreeBlk, fun β hβ ↦ ?_⟩
      obtain ⟨hcl1, hbelow1, hunary1⟩ := hSpecTree β hβ
      let β₁ := sTree β
      let β₂ := cSeed.eval β₁
      have hmsb1 : β₁ msb = β msb := hbelow1 msb hmsb_lt
      have hLd : 2 ^ d = L := rfl
      have hmid1_zero : β₁ ⟨cur + L, by omega⟩ = 0 :=
        hcl1 ⟨cur + L, by omega⟩ (show M - (M - (cur + 2 ^ d)) ≤ cur + L by omega)
      have hcl2 : cleanRem M (M - (cur + 2 * L - (L - 1))) β₂ := fun w hw ↦ by
        dsimp only [β₂, cSeed, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_gt (show cur + L < w.val by omega))]
        exact hcl1 w (by omega)
      obtain ⟨hcl3, hbelow3, hsplit3⟩ := hSpecSplit β₂ hcl2
      let β₃ := sSplit β₂
      let β₄ := cFix.eval β₃
      have hcl4 : cleanRem M (M - (cur + 2 ^ (d + 1))) β₄ := fun w hw ↦ by
        dsimp only [β₄]
        rw [cFix.eval_outside (bound := cur + 2 * L)
          (mobiusFixZeroCliff_supports cur L hL hsp) β₃ w (by omega)]
        exact hcl3 w (by omega)
      have hβ₂_below : ∀ w : Wire M, w.val < cur + L → β₂ w = β₁ w := fun w hw ↦ by
        dsimp only [β₂, cSeed, CliffProg.eval]
        exact Function.update_of_ne (wire_ne_of_lt hw) _ _
      have hβ₂_mid : β₂ ⟨cur + L, by omega⟩ = β msb := by
        dsimp only [β₂, cSeed, CliffProg.eval]
        rw [Function.update_self, hmid1_zero, zero_add, hmsb1]
      have hβ₂_msb : β₂ msb = β msb := (hβ₂_below msb (by omega)).trans hmsb1
      let loVal := bitsVal (fun j ↦ β (addr j.castSucc))
      have hlo_lt : loVal < L := bitsVal_lt_two_pow _
      have splitTop : bitsVal (fun j ↦ β (addr j)) = loVal + L * (β msb).val := by
        rw [bitsVal, Fin.sum_univ_castSucc]
        dsimp only [L, loVal, msb]
        simp [bitsVal, mul_comm]
      have hβ₃_cur0 : β₃ ⟨cur, by omega⟩ = if 0 = loVal then 1 else 0 :=
        (hbelow3 ⟨cur, by omega⟩ (Or.inl (show cur < cur + (L - (L - 1)) by omega))).trans
          ((hβ₂_below ⟨cur, by omega⟩ (show cur < cur + L by omega)).trans
            (by simpa [loVal] using hunary1 0 hL))
      have hβ₃_mid : β₃ ⟨cur + L, by omega⟩ = β msb :=
        (hbelow3 ⟨cur + L, by omega⟩
          (Or.inr ⟨le_rfl, show cur + L < cur + L + (L - (L - 1)) by omega⟩)).trans hβ₂_mid
      have hβ₃_split : ∀ (i : ℕ) (_ : 1 ≤ i) (hi : i < L),
          β₃ ⟨cur + i, by omega⟩ =
            (if i = loVal then 1 else 0) + (if i = loVal then 1 else 0) * β msb ∧
          β₃ ⟨cur + L + i, by omega⟩ = (if i = loVal then 1 else 0) * β msb := fun i _ hiL ↦ by
        obtain ⟨hs1, hs2⟩ := hsplit3 i (by omega) hiL
        dsimp only [β₃]
        rw [hs1, hs2, hβ₂_below ⟨cur + i, by omega⟩ (Nat.add_lt_add_left hiL cur)]
        dsimp only [β₁]
        rw [hunary1 i hiL, hβ₂_msb]
        exact ⟨rfl, rfl⟩
      obtain ⟨hXorOther, hXorMid⟩ := xorUpperToMid_eval cur L hsp β₃ (L - 1) (by omega)
      have hMidRecovered :
          (xorUpperToMid cur L hsp (L - 1) (by omega)).eval β₃ ⟨cur + L, by omega⟩ =
            (if 0 = loVal then 1 else 0) * β msb := by
        rw [hXorMid, hβ₃_mid]
        have hSumTerm : ∀ r : Fin (L - 1), β₃ ⟨cur + L + 1 + r.val, by omega⟩ =
            (if 1 + r.val = loVal then 1 else 0) * β msb := fun r ↦ by
          rw [show (⟨cur + L + 1 + r.val, by omega⟩ : Wire M) = ⟨cur + L + (1 + r.val), by omega⟩
            from Fin.ext (Nat.add_assoc (cur + L) 1 r.val)]
          exact (hβ₃_split (1 + r.val) (by omega) (by omega)).2
        simp_rw [hSumTerm]
        by_cases hlo0 : loVal = 0
        · rw [hlo0, Finset.sum_eq_zero fun r _ ↦ by
            rw [ite_neg (by omega : 1 + r.val ≠ 0), zero_mul]]
          simp
        · rw [Finset.sum_eq_single ⟨loVal - 1, by omega⟩
            (fun r _ hr ↦ by
              rw [ite_neg (fun h ↦ hr (Fin.ext (show r.val = loVal - 1 by omega))), zero_mul])
            (fun habs ↦ absurd (Finset.mem_univ _) habs)]
          simp [show 1 + (loVal - 1) = loVal by omega, CharTwo.add_self_eq_zero, Ne.symm hlo0]
      refine ⟨hcl4, fun w hw ↦ ?_, fun k hk ↦ ?_⟩
      · dsimp only [β₄, cFix, mobiusFixZeroCliff, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_lt hw),
          hXorOther w (wire_ne_of_lt (lt_of_lt_of_le hw (Nat.le_add_right _ _)))]
        exact (hbelow3 w (Or.inl (by omega))).trans ((hβ₂_below w (by omega)).trans (hbelow1 w hw))
      · dsimp only [β₄, cFix, mobiusFixZeroCliff, CliffProg.eval]
        rw [splitTop]
        have hLoFormula : ∀ i < L,
            (if i = loVal then (1 : ZMod 2) else 0) + (if i = loVal then 1 else 0) * β msb =
              if i = loVal + L * (β msb).val then 1 else 0 := fun i hiL ↦ by
          rcases bit_cases (β msb) with hb | hb
          · simp [hb, ZMod.val_zero]
          · by_cases hieq : i = loVal
            · rw [hb, hieq, ZMod.val_one, mul_one, ite_pos rfl, mul_one,
                CharTwo.add_self_eq_zero, ite_neg (by omega : ¬ loVal = loVal + L)]
            · simp [hb, hieq, show i ≠ loVal + L by omega]
        have hHiFormula : ∀ i < L, (if i = loVal then (1 : ZMod 2) else 0) * β msb =
            if L + i = loVal + L * (β msb).val then 1 else 0 := fun i hiL ↦ by
          rcases bit_cases (β msb) with hb | hb
          · simp [hb, ZMod.val_zero, show L + i ≠ loVal by omega]
          · by_cases hieq : i = loVal
            · simp [hb, hieq, add_comm]
            · simp [hb, hieq, show L + i ≠ loVal + L by omega]
        by_cases hk0 : k = 0
        · subst hk0
          rw [show (⟨cur + 0, by omega⟩ : Wire M) = ⟨cur, by omega⟩ from Fin.ext (Nat.add_zero cur),
            Function.update_self, hXorOther _ (wire_ne_of_lt (show cur < cur + L by omega)),
            hMidRecovered, hβ₃_cur0]
          exact hLoFormula 0 hL
        · by_cases hkL : k < L
          · rw [Function.update_of_ne (wire_ne_of_gt (show cur < cur + k by omega)),
              hXorOther _ (wire_ne_of_lt (Nat.add_lt_add_left hkL cur)),
              (hβ₃_split k (by omega) hkL).1]
            exact hLoFormula k hkL
          · by_cases hkEqL : k = L
            · subst hkEqL
              rw [Function.update_of_ne (wire_ne_of_gt (show cur < cur + L by omega)),
                hMidRecovered]
              simpa using hHiFormula 0 hL
            · let i := k - L
              rw [Function.update_of_ne (wire_ne_of_gt (show cur < cur + k by omega)),
                hXorOther _ (wire_ne_of_gt (show cur + L < cur + k by omega)),
                show (⟨cur + k, by omega⟩ : Wire M) = ⟨cur + L + i, by omega⟩ from
                  Fin.ext (show cur + k = cur + L + i by omega),
                (hβ₃_split i (by omega) (by omega)).2, show k = L + i by omega]
              exact hHiFormula i (by omega)
def withUnarySplitPrefix {M : ℕ} (base L K_max : ℕ) (hKL : K_max ≤ L)
    (sel : Wire M) (hsel : sel.val < base)
    (hcur : base + L + K_max ≤ M) :
    (K : ℕ) → (hK : K ≤ K_max) →
    TempPhaseProg M → TempPhaseProg M
  | 0, _, body => body
  | K + 1, hK, body =>
      let idx := K_max - (K + 1)
      let pos := base + L + idx
      withUnarySplit pos (by dsimp [pos, idx]; omega)
        ⟨base + idx, by dsimp [idx]; omega⟩ sel
        (wire_ne_of_gt (by dsimp; omega))
        (by dsimp [pos]; omega) (by dsimp [pos]; omega)
        (withUnarySplitPrefix base L K_max hKL sel hsel hcur K (by omega) body)
theorem ScopedBlock.withUnarySplitPrefix_block {M : ℕ} (base L K_max : ℕ) (hKL : K_max ≤ L)
    (sel : Wire M) (hsel : sel.val < base) (hcur : base + L + K_max ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ K_max)
      (leaf body : TempPhaseProg M) (sBody : BitAssignment M → BitAssignment M),
      ScopedBlock M (M - (base + L + K_max)) sBody leaf body →
      ∃ setup : BitAssignment M → BitAssignment M,
        ScopedBlock M (M - (base + L + K_max - K)) (fun β ↦ sBody (setup β)) leaf
          (withUnarySplitPrefix base L K_max hKL sel hsel hcur K hK body) ∧
        ∀ β : BitAssignment M, cleanRem M (M - (base + L + K_max - K)) β →
          cleanRem M (M - (base + L + K_max)) (setup β) ∧
          (∀ w : Wire M,
            (w.val < base + (K_max - K) ∨ (base + K_max ≤ w.val ∧ w.val < base + L + (K_max - K))) →
            setup β w = β w) ∧
          (∀ (i : ℕ) (_ : K_max - K ≤ i) (hhi : i < K_max),
            setup β ⟨base + i, by omega⟩ =
              β ⟨base + i, by omega⟩ + β ⟨base + i, by omega⟩ * β sel ∧
            setup β ⟨base + L + i, by omega⟩ = β ⟨base + i, by omega⟩ * β sel) := by
  intro K
  induction K with
  | zero =>
      intro _ _ _ _ hBody
      exact ⟨id, hBody, fun _ hβ ↦
        ⟨hβ, fun _ _ ↦ rfl, fun _ hlo hhi ↦ absurd (lt_of_le_of_lt hlo hhi) (by omega)⟩⟩
  | succ K ih =>
      intro hK leaf body sBody hBody
      let idx := K_max - (K + 1)
      let pos := base + L + idx
      obtain ⟨setupInner, hInner, hSpecInner⟩ := ih (by omega) leaf body sBody hBody
      have hStep := ScopedBlock.withUnarySplit_block (M := M) pos (by omega)
        ⟨base + idx, by omega⟩ sel (wire_ne_of_gt (lt_of_lt_of_le hsel (Nat.le_add_right _ _)))
        (show base + idx < pos by omega) (show sel.val < pos by omega)
        (hInner.cast_rem (by omega))
      refine ⟨fun β ↦ setupInner (unarySplitSetup pos (by omega) ⟨base + idx, by omega⟩ sel β),
        hStep.cast_rem (by omega), fun β hβ ↦ ?_⟩
      let β₁ := unarySplitSetup pos (by omega) ⟨base + idx, by omega⟩ sel β
      have hβ₁_other : ∀ w : Wire M, w.val ≠ base + idx → w.val ≠ pos → β₁ w = β w :=
        fun w h1 h2 ↦ by
          dsimp [β₁, unarySplitSetup]
          rw [Function.update_of_ne (fun h ↦ h1 (congrArg Fin.val h)),
            Function.update_of_ne (fun h ↦ h2 (congrArg Fin.val h))]
      obtain ⟨hcl, hbelow, hsplit⟩ := hSpecInner β₁ fun w hw ↦
        (hβ₁_other w (by omega) (by omega)).trans (hβ w (by omega))
      refine ⟨hcl, fun w hw ↦ (hbelow w (by omega)).trans
        (hβ₁_other w (by omega) (by omega)), fun i hlo hhi ↦ ?_⟩
      dsimp only
      by_cases hi : i = idx
      · subst hi
        rw [hbelow _ (Or.inl (show base + idx < base + (K_max - K) by omega)),
          hbelow _ (Or.inr ⟨show base + K_max ≤ base + L + idx by omega,
            show base + L + idx < base + L + (K_max - K) by omega⟩)]
        dsimp [β₁, unarySplitSetup, pos]
        refine ⟨Function.update_self _ _ _, ?_⟩
        rw [Function.update_of_ne (wire_ne_of_gt (show base + idx < base + L + idx by omega)),
          Function.update_self]
      · obtain ⟨h1, h2⟩ := hsplit i (by omega) hhi
        rw [h1, h2, hβ₁_other _ (show base + i ≠ base + idx by omega)
          (show base + i ≠ pos by omega),
          hβ₁_other sel (by omega) (by omega)]
        exact ⟨rfl, rfl⟩
def ctxUnarySplitPrefix {M : ℕ} (base L K_max : ℕ) (hKL : K_max ≤ L)
    (sel : Wire M) (hsel : sel.val < base)
    (hcur : base + L + K_max ≤ M) :
    (K : ℕ) → (hK : K ≤ K_max) → TempCtx M
  | 0, _ => .hole
  | K + 1, hK =>
      let idx := K_max - (K + 1)
      let pos := base + L + idx
      (ctxUnarySplit pos (by dsimp [pos, idx]; omega)
        ⟨base + idx, by dsimp [idx]; omega⟩ sel
        (wire_ne_of_gt (by dsimp; omega))
        (by dsimp [pos]; omega) (by dsimp [pos]; omega)).append
        (ctxUnarySplitPrefix base L K_max hKL sel hsel hcur K (by omega))
@[simp] theorem ctxUnarySplitPrefix_plug {M : ℕ} (base L K_max : ℕ) (hKL : K_max ≤ L)
    (sel : Wire M) (hsel : sel.val < base) (hcur : base + L + K_max ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ K_max) (body : TempPhaseProg M),
      (ctxUnarySplitPrefix base L K_max hKL sel hsel hcur K hK).plug body =
        withUnarySplitPrefix base L K_max hKL sel hsel hcur K hK body
  | 0, _, _ => rfl
  | K + 1, _, body => by
      simp only [ctxUnarySplitPrefix, withUnarySplitPrefix, TempCtx.append_plug,
        ctxUnarySplit_plug, ctxUnarySplitPrefix_plug base L K_max hKL sel hsel hcur K _ body]
theorem ctxUnarySplitPrefix_countTempAnd {M : ℕ} (base L K_max : ℕ) (hKL : K_max ≤ L)
    (sel : Wire M) (hsel : sel.val < base) (hcur : base + L + K_max ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ K_max),
      (ctxUnarySplitPrefix base L K_max hKL sel hsel hcur K hK).countTempAnd = K
  | 0, _ => rfl
  | K + 1, _ => by
      dsimp only [ctxUnarySplitPrefix]
      rw [TempCtx.append_countTempAnd, ctxUnarySplit_countTempAnd,
        ctxUnarySplitPrefix_countTempAnd base L K_max hKL sel hsel hcur K]
      omega
theorem RestoresAll.unarySplitPrefix {M : ℕ}
    (base L K_max : ℕ) (hKL : K_max ≤ L)
    (sel : Wire M) (hsel : sel.val < base) (hcur : base + L + K_max ≤ M) :
    ∀ (K : ℕ) (hK : K ≤ K_max),
      RestoresAll (ctxUnarySplitPrefix base L K_max hKL sel hsel hcur K hK)
  | 0, _ => RestoresAll.hole
  | K + 1, _ =>
      RestoresAll.append (RestoresAll.unarySplit _ _ _ _ _ _ _)
        (RestoresAll.unarySplitPrefix base L K_max hKL sel hsel hcur K _)
theorem TempCtx.append_fwdBits {M : ℕ} (F G : TempCtx M) (γ : BitAssignment M) :
    (F.append G).fwdBits γ = G.fwdBits (F.fwdBits γ) := by
  induction F generalizing γ with
  | hole => rfl
  | seqPre c _ ih => dsimp only [TempCtx.append, TempCtx.fwdBits]; exact ih (c.eval γ)
  | seqPost _ _ ih => dsimp only [TempCtx.append, TempCtx.fwdBits]; exact ih γ
  | tempAnd c₁ c₂ anc _ _ _ _ ih =>
      dsimp only [TempCtx.append, TempCtx.fwdBits]
      exact ih (Function.update γ anc (γ anc + γ c₁ * γ c₂))
set_option allowUnsafeReducibility true in
noncomputable def omega8P : ℂ := (1 + Complex.I) / (√2 : ℂ)
theorem sqrt2_mul_self_p : (√2 : ℂ) * (√2 : ℂ) = 2 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
theorem omega8P_sq : omega8P ^ 2 = Complex.I := by
  rw [omega8P, div_pow, sq (√2 : ℂ), sqrt2_mul_self_p]
  ring_nf
  rw [Complex.I_sq]
  ring
theorem omega8P_pow_four : omega8P ^ 4 = -1 := by
  rw [show omega8P ^ 4 = (omega8P ^ 2) ^ 2 by ring, omega8P_sq, Complex.I_sq]
theorem star_omega8P : star omega8P = -omega8P ^ 3 := by
  have h1 : star omega8P = (1 - Complex.I) / (√2 : ℂ) := by
    simp [omega8P, Complex.conj_ofReal]
    ring
  rw [h1, show omega8P ^ 3 = omega8P ^ 2 * omega8P by ring, omega8P_sq, omega8P]
  ring_nf
  rw [Complex.I_sq]
  ring
theorem omega8P_mem_unitary : omega8P ∈ unitary ℂ := by
  have h4 : -omega8P ^ 3 * omega8P = 1 := by
    rw [show -omega8P ^ 3 * omega8P = -omega8P ^ 4 by ring, omega8P_pow_four, neg_neg]
  exact Unitary.mem_iff.mpr ⟨star_omega8P ▸ h4, star_omega8P ▸ (mul_comm _ _).trans h4⟩
theorem complexI_mem_unitary : Complex.I ∈ unitary ℂ := by simp [Unitary.mem_iff]
theorem neg_complexI_mem_unitary : -Complex.I ∈ unitary ℂ := by simp [Unitary.mem_iff]
noncomputable def fTP (b : ZMod 2) : ℂ := if b = 0 then 1 else omega8P
noncomputable def fTiP (b : ZMod 2) : ℂ := if b = 0 then 1 else -omega8P ^ 3
theorem fTP_mul_fTiP (b : ZMod 2) : fTP b * fTiP b = 1 := by
  rcases bit_cases b with rfl | rfl <;> dsimp [fTP, fTiP]
  · ring
  · rw [show omega8P * -omega8P ^ 3 = -omega8P ^ 4 by ring, omega8P_pow_four, neg_neg]
theorem fTiP_mul_fTP (b : ZMod 2) : fTiP b * fTP b = 1 := (mul_comm _ _).trans (fTP_mul_fTiP b)
noncomputable def oneHotBitPhase (z u x : ZMod 2) : ℂ := fTiP (z + x) * fTP (z + x + u)
theorem oneHotBitPhase_zero_u (z x : ZMod 2) : oneHotBitPhase z 0 x = 1 := by
  rw [oneHotBitPhase, add_zero]
  exact fTiP_mul_fTP _
noncomputable def oneHotBoundaryPhase (z uLast : ZMod 2) : ℂ := fTP z * fTiP (z + 1 + uLast)
theorem oneHotBoundaryPhase_one (z : ZMod 2) : oneHotBoundaryPhase z 1 = 1 := by
  rw [oneHotBoundaryPhase, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  exact fTP_mul_fTiP z
noncomputable def targetDiagScalar (z y : ZMod 2) : ℂ :=
  if y = 0 then 1 else if z = 0 then -Complex.I else Complex.I
theorem targetDiagScalar_mem_unitary (z y : ZMod 2) : targetDiagScalar z y ∈ unitary ℂ := by
  rcases bit_cases y with rfl | rfl
  · exact Submonoid.one_mem _
  · rcases bit_cases z with rfl | rfl
    · exact neg_complexI_mem_unitary
    · exact complexI_mem_unitary
theorem oneHotBitPhase_one_mul_boundary_zero (z y : ZMod 2) :
    oneHotBitPhase z 1 y * oneHotBoundaryPhase z 0 = targetDiagScalar z y := by
  rcases bit_cases z with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    dsimp [oneHotBitPhase, oneHotBoundaryPhase, targetDiagScalar, fTP, fTiP]
  · rw [show 1 * omega8P * (1 * -omega8P ^ 3) = -omega8P ^ 4 by ring, omega8P_pow_four, neg_neg]
  · rw [show -omega8P ^ 3 * 1 * (1 * -omega8P ^ 3) = omega8P ^ 4 * omega8P ^ 2 by ring,
      omega8P_pow_four, omega8P_sq, neg_one_mul]
  · rw [show -omega8P ^ 3 * 1 * (omega8P * 1) = -omega8P ^ 4 by ring, omega8P_pow_four, neg_neg]
  · rw [show 1 * omega8P * (omega8P * 1) = omega8P ^ 2 by ring, omega8P_sq]
noncomputable def diagComplexUnitary {d : ℕ} (Φ : Fin (2 ^ d) → ℂ)
    (hΦ : ∀ g, Φ g ∈ unitary ℂ) : Unitary (2 ^ d) :=
  ⟨Matrix.diagonal Φ, by
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    exact hΦ⟩
noncomputable def diagComplexUnitaryN {n : ℕ} (Φ : BitAssignment n → ℂ)
    (hΦ : ∀ β, Φ β ∈ unitary ℂ) : Unitary (2 ^ n) :=
  diagComplexUnitary (fun g ↦ Φ (basisBits n g)) (fun _ ↦ hΦ _)
theorem ket_diagComplexUnitaryN {n : ℕ} (Φ : BitAssignment n → ℂ) (hΦ : ∀ β, Φ β ∈ unitary ℂ)
    (β : BitAssignment n) : (diagComplexUnitaryN Φ hΦ).1.mulVec (ket β) = Φ β • ket β := by
  rw [show ket β = (Pi.single ((basisBitsEquiv n).symm β) 1 : Fin (2 ^ n) → ℂ) from
      funext fun i ↦ by simp [ket, basisState], diagComplexUnitaryN, diagComplexUnitary]
  change (Matrix.diagonal _).mulVec (Pi.single _ 1) = _
  rw [Matrix.diagonal_mulVec_single, mul_one, (basisBitsEquiv n).apply_symm_apply β]
  funext i
  by_cases h : i = (basisBitsEquiv n).symm β
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]
theorem embedUnitary_diagComplexUnitary_mulVec_single {n k : ℕ} (r : QRegister k n)
    (Φ : Fin (2 ^ k) → ℂ) (hΦ : ∀ z, Φ z ∈ unitary ℂ) (g : Fin (2 ^ n)) :
    (r.embedUnitary (diagComplexUnitary Φ hΦ)).1.mulVec (Pi.single g 1) = Φ (r.extractIndex g)
    • Pi.single g 1 := funext fun i ↦ by
  rw [Matrix.mulVec_single_one]
  change (r.embedMatrix (Matrix.diagonal Φ)) i g =
    (Φ (r.extractIndex g) • (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ)) i
  rw [QRegister.embedMatrix_apply]
  by_cases hig : i = g
  · subst hig
    simp [Matrix.diagonal]
  · simp only [Pi.smul_apply, Pi.single_eq_of_ne hig, smul_zero]
    by_cases henv : (r.basisSplitEquiv i).2 = (r.basisSplitEquiv g).2
    · simp [henv, Matrix.diagonal, show r.extractIndex i ≠ r.extractIndex g from fun heq ↦ hig <|
        r.basisSplitEquiv.injective <| Prod.ext
          (by simpa [QRegister.basisSplitEquiv_apply_fst] using heq) henv]
    · simp [henv]
theorem singleton_diag_mulVec_ket {n : ℕ} (q : Wire n) (c1 : ℂ) (hc1 : c1 ∈ unitary ℂ)
    (γ : BitAssignment n) : ((QRegister.singleton q).embedMatrix (Matrix.diagonal fun i : Fin
    2 ↦ if i = 1 then c1 else 1)).mulVec (ket γ) = (if γ q = 0 then (1 : ℂ) else c1) • ket γ := by
  let Φ : Fin (2 ^ 1) → ℂ := fun i ↦ if i = 1 then c1 else 1
  have hΦ : ∀ i, Φ i ∈ unitary ℂ := fun i ↦ by
    by_cases h : i = 1
    · exact h ▸ hc1
    · simp only [Φ, h, ↓reduceIte]
      exact Submonoid.one_mem _
  let g := (basisBitsEquiv n).symm γ
  rw [show ket γ = (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ) from
    funext fun u ↦ by simp [g, ket, basisState]]
  have hemb := embedUnitary_diagComplexUnitary_mulVec_single (QRegister.singleton q) Φ hΦ g
  change ((QRegister.singleton q).embedMatrix (Matrix.diagonal Φ)).mulVec (Pi.single g 1) = _
    at hemb ⊢
  rw [hemb]
  refine congrArg (· • (Pi.single g (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  let idx := (QRegister.singleton q).extractIndex g
  have hbit : basisBits 1 idx 0 = γ q := by
    dsimp only [idx]
    rw [QRegister.basisBits_extractIndex]
    exact congrFun ((basisBitsEquiv n).apply_symm_apply γ) q
  change Φ idx = _
  rcases bit_cases (γ q) with hq0 | hq1
  · have hidx : idx = 0 := eq_of_basisBits_eq fun k ↦ by
      rw [Subsingleton.elim k 0, hbit, hq0]
      decide
    rw [hidx, hq0]
    rfl
  · have hidx : idx = 1 := eq_of_basisBits_eq fun k ↦ by
      rw [Subsingleton.elim k 0, hbit, hq1]
      decide
    rw [hidx, hq1]
    simp [Φ, one_ne_zero]
theorem ket_S_p {n : ℕ} (q : Wire n) (γ : BitAssignment n) : (Circuit.S q).eval.1.mulVec
    (ket γ) = (if γ q = 0 then (1 : ℂ) else Complex.I) • ket γ := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_s_val]
  exact singleton_diag_mulVec_ket q Complex.I complexI_mem_unitary γ
theorem ket_T_p {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.T q).eval.1.mulVec (ket γ) = fTP (γ q) • ket γ := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval_t_val]
  exact singleton_diag_mulVec_ket q omega8P omega8P_mem_unitary γ
theorem ket_Z_p {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ket γ) = bitSign (γ q) • ket γ := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec (ket γ) = _
  rw [show (!![(1 : ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.diagonal (fun i : Fin 2 ↦ if i = 1 then (-1 : ℂ) else 1) by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]]
  exact singleton_diag_mulVec_ket q (-1) (by simp [Unitary.mem_iff]) γ
theorem ket_Tinv_p {n : ℕ} (q : Wire n) (γ : BitAssignment n) :
    (Circuit.T q).inverse.eval.1.mulVec (ket γ) = fTiP (γ q) • ket γ := by
  change (Circuit.T q ;;ᶜ (Circuit.S q ;;ᶜ (Circuit.Z q ;;ᶜ .identity))).eval.1.mulVec (ket γ) = _
  simp only [eval_seq_mulVec, Circuit.eval_identity, Submonoid.coe_one,
    Matrix.one_mulVec, ket_T_p, ket_S_p, ket_Z_p, Matrix.mulVec_smul, smul_smul]
  refine congrArg (· • ket γ) ?_
  rcases bit_cases (γ q) with hb | hb
  · simp [hb, fTP, fTiP, bitSign]
  · simp only [hb, fTP, fTiP, bitSign, one_ne_zero, ↓reduceIte]
    rw [← omega8P_sq]
    ring
def oneHotBitStep {n : ℕ} (z u x : Wire n) (hxz : x ≠ z) (huz : u ≠ z) : Circuit n :=
  Circuit.CNOT x z hxz ;;ᶜ (Circuit.T z).inverse ;;ᶜ Circuit.CNOT u z huz ;;ᶜ
  Circuit.T z ;;ᶜ Circuit.CNOT u z huz ;;ᶜ Circuit.CNOT x z hxz
@[simp] theorem oneHotBitStep_count_toff {n : ℕ} (z u x : Wire n) (hxz : x ≠ z) (huz : u ≠ z) :
    (oneHotBitStep z u x hxz huz).count PrimitiveGate.TOFF = 0 := by
  simp [oneHotBitStep, Circuit.CNOT, Circuit.T, Circuit.single,
    Circuit.inverse, Circuit.inverseGate, Circuit.sequence, Circuit.count]
@[simp] theorem oneHotBitStep_count_t {n : ℕ} (z u x : Wire n) (hxz : x ≠ z) (huz : u ≠ z) :
    (oneHotBitStep z u x hxz huz).count PrimitiveGate.T = 2 := by
  simp only [oneHotBitStep, Circuit.count_seq]; rfl
theorem ket_oneHotBitStep {n : ℕ} (z u x : Wire n) (hxz : x ≠ z) (huz : u ≠ z)
    (β : BitAssignment n) : (oneHotBitStep z u x hxz huz).eval.1.mulVec (ket β) =
    oneHotBitPhase (β z) (β u) (β x) • ket β := by
  have hadd1 (a b : ZMod 2) : a + b + b = a := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  dsimp only [oneHotBitStep, oneHotBitPhase]
  simp only [eval_seq_mulVec, ket_CNOT, ket_T_p, ket_Tinv_p, Matrix.mulVec_smul,
    Function.update_self, Function.update_of_ne hxz, Function.update_of_ne huz,
    Function.update_idem, hadd1, Function.update_eq_self, smul_smul]
def oneHotBoundaryFix {n : ℕ} (z uLast : Wire n) (huz : uLast ≠ z) : Circuit n :=
  Circuit.T z ;;ᶜ Circuit.X z ;;ᶜ Circuit.CNOT uLast z huz ;;ᶜ
  (Circuit.T z).inverse ;;ᶜ Circuit.CNOT uLast z huz ;;ᶜ Circuit.X z
@[simp] theorem oneHotBoundaryFix_count_toff {n : ℕ} (z uLast : Wire n) (huz : uLast ≠ z) :
    (oneHotBoundaryFix z uLast huz).count PrimitiveGate.TOFF = 0 := by
  simp [oneHotBoundaryFix, Circuit.CNOT, Circuit.T, Circuit.X,
    Circuit.single, Circuit.inverse, Circuit.inverseGate, Circuit.sequence, Circuit.count]
@[simp] theorem oneHotBoundaryFix_count_t {n : ℕ} (z uLast : Wire n) (huz : uLast ≠ z) :
    (oneHotBoundaryFix z uLast huz).count PrimitiveGate.T = 2 := by
  simp only [oneHotBoundaryFix, Circuit.count_seq]; rfl
theorem ket_oneHotBoundaryFix {n : ℕ} (z uLast : Wire n) (huz : uLast ≠ z)
    (β : BitAssignment n) : (oneHotBoundaryFix z uLast huz).eval.1.mulVec (ket β) =
    oneHotBoundaryPhase (β z) (β uLast) • ket β := by
  have hadd1 (a b : ZMod 2) : a + b + b = a := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  dsimp only [oneHotBoundaryFix, oneHotBoundaryPhase]
  simp only [eval_seq_mulVec, ket_T_p, ket_X, ket_CNOT, ket_Tinv_p, Matrix.mulVec_smul,
    Function.update_self, Function.update_of_ne huz, Function.update_idem,
    hadd1, Function.update_eq_self, smul_smul]
def slotOneHotAux {n : ℕ} (rPartner18 : QRegister 18 n) (uWire : Wire n)
    (rSlot : QRegister 18 n) (huP : ∀ j, uWire ≠ rPartner18 j)
    (hSP : ∀ j, rSlot j ≠ rPartner18 j) : (b : ℕ) → (hb : b ≤ 18) → Circuit n
  | 0, _ => .identity
  | b + 1, hb =>
      slotOneHotAux rPartner18 uWire rSlot huP hSP b (Nat.le_of_succ_le hb) ;;ᶜ
      oneHotBitStep (rPartner18 ⟨b, by omega⟩) uWire (rSlot ⟨b, by omega⟩) (hSP _) (huP _)
theorem slotOneHotAux_count_toff {n : ℕ} (rPartner18 : QRegister 18 n) (uWire : Wire n)
    (rSlot : QRegister 18 n) (huP : ∀ j, uWire ≠ rPartner18 j)
    (hSP : ∀ j, rSlot j ≠ rPartner18 j) : ∀ (b : ℕ) (hb : b ≤ 18),
    (slotOneHotAux rPartner18 uWire rSlot huP hSP b hb).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | b + 1, _ => by
      dsimp only [slotOneHotAux]
      rw [Circuit.count_seq, slotOneHotAux_count_toff rPartner18 uWire rSlot huP hSP b,
        oneHotBitStep_count_toff, add_zero]
theorem slotOneHotAux_count_t {n : ℕ} (rPartner18 : QRegister 18 n) (uWire : Wire n)
    (rSlot : QRegister 18 n) (huP : ∀ j, uWire ≠ rPartner18 j)
    (hSP : ∀ j, rSlot j ≠ rPartner18 j) : ∀ (b : ℕ) (hb : b ≤ 18),
    (slotOneHotAux rPartner18 uWire rSlot huP hSP b hb).count PrimitiveGate.T = 2 * b
  | 0, _ => rfl
  | b + 1, _ => by
      dsimp only [slotOneHotAux]
      rw [Circuit.count_seq, slotOneHotAux_count_t rPartner18 uWire rSlot huP hSP b,
        oneHotBitStep_count_t]; ring
theorem slotOneHotAux_eval_ket {n : ℕ} (rPartner18 : QRegister 18 n) (uWire : Wire n)
    (rSlot : QRegister 18 n) (huP : ∀ j, uWire ≠ rPartner18 j)
    (hSP : ∀ j, rSlot j ≠ rPartner18 j) (β : BitAssignment n) : ∀ (b : ℕ) (hb : b ≤ 18),
    (slotOneHotAux rPartner18 uWire rSlot huP hSP b hb).eval.1.mulVec (ket β) =
      (∏ j : Fin b, oneHotBitPhase (β (rPartner18 ⟨j.val, by omega⟩)) (β uWire)
        (β (rSlot ⟨j.val, by omega⟩))) • ket β
  | 0, _ => by simp [slotOneHotAux]
  | b + 1, hb => by
      dsimp only [slotOneHotAux]
      rw [eval_seq_mulVec,
        slotOneHotAux_eval_ket rPartner18 uWire rSlot huP hSP β b (Nat.le_of_succ_le hb),
        Matrix.mulVec_smul, ket_oneHotBitStep, smul_smul, Fin.prod_univ_castSucc]; rfl
def oobFixAux {n : ℕ} (rPartner18 : QRegister 18 n) (uLast : Wire n)
    (huP : ∀ j, uLast ≠ rPartner18 j) : (b : ℕ) → (hb : b ≤ 18) → Circuit n
  | 0, _ => .identity
  | b + 1, hb =>
      oobFixAux rPartner18 uLast huP b (Nat.le_of_succ_le hb) ;;ᶜ
      oneHotBoundaryFix (rPartner18 ⟨b, by omega⟩) uLast (huP _)
theorem oobFixAux_count_toff {n : ℕ} (rPartner18 : QRegister 18 n) (uLast : Wire n)
    (huP : ∀ j, uLast ≠ rPartner18 j) : ∀ (b : ℕ) (hb : b ≤ 18),
    (oobFixAux rPartner18 uLast huP b hb).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | b + 1, _ => by
      dsimp only [oobFixAux]
      rw [Circuit.count_seq, oobFixAux_count_toff rPartner18 uLast huP b,
        oneHotBoundaryFix_count_toff, add_zero]
theorem oobFixAux_count_t {n : ℕ} (rPartner18 : QRegister 18 n) (uLast : Wire n)
    (huP : ∀ j, uLast ≠ rPartner18 j) : ∀ (b : ℕ) (hb : b ≤ 18),
    (oobFixAux rPartner18 uLast huP b hb).count PrimitiveGate.T = 2 * b
  | 0, _ => rfl
  | b + 1, _ => by
      dsimp only [oobFixAux]
      rw [Circuit.count_seq, oobFixAux_count_t rPartner18 uLast huP b,
        oneHotBoundaryFix_count_t]; ring
theorem oobFixAux_eval_ket {n : ℕ} (rPartner18 : QRegister 18 n) (uLast : Wire n)
    (huP : ∀ j, uLast ≠ rPartner18 j) (β : BitAssignment n) : ∀ (b : ℕ) (hb : b ≤ 18),
    (oobFixAux rPartner18 uLast huP b hb).eval.1.mulVec (ket β) =
      (∏ j : Fin b, oneHotBoundaryPhase (β (rPartner18 ⟨j.val, by omega⟩)) (β uLast)) • ket β
  | 0, _ => by simp [oobFixAux]
  | b + 1, hb => by
      dsimp only [oobFixAux]
      rw [eval_seq_mulVec, oobFixAux_eval_ket rPartner18 uLast huP β b (Nat.le_of_succ_le hb),
        Matrix.mulVec_smul, ket_oneHotBoundaryFix, smul_smul, Fin.prod_univ_castSucc]; rfl
theorem prod_mem_unitary {ι : Type*} (s : Finset ι) (g : ι → ℂ)
    (hg : ∀ i ∈ s, g i ∈ unitary ℂ) : (∏ i ∈ s, g i) ∈ unitary ℂ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact Submonoid.mul_mem _ (hg a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
theorem disj_concat_left {k₁ k₂ k₃ n : ℕ} {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n}
    {r₃ : QRegister k₃ n} (h₁₂ : r₁.DisjointWires r₂) (h₁₃ : r₁.DisjointWires r₃)
    (h₂₃ : r₂.DisjointWires r₃) : (r₁.concat r₂ h₁₂).DisjointWires r₃ :=
  QRegister.disjoint_iff.mpr fun idx j heq ↦ by
    by_cases hlt : idx.val < k₁
    · have he : idx = Fin.castAdd k₂ ⟨idx.val, hlt⟩ := by ext; rfl
      rw [he, QRegister.concat_apply_left] at heq; exact h₁₃.ne _ j heq
    · have he : idx = Fin.natAdd k₁ ⟨idx.val - k₁, by omega⟩ := by ext; dsimp; omega
      rw [he, QRegister.concat_apply_right] at heq; exact h₂₃.ne _ j heq
set_option allowUnsafeReducibility true in
noncomputable def ΦDiagM (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18))
    (m : ℕ) (hm : m ≤ 18) (γ : BitAssignment (posCoreWires + 18)) : ℂ :=
  let x := (basisBitsEquiv posCoreWires).symm (fun i ↦ γ (Fin.castAdd 18 i))
  ∏ j : Fin m,
    targetDiagScalar (γ (Fin.natAdd posCoreWires ⟨j.val, by omega⟩))
      (basisBits 18 (tbl x) ⟨j.val, by omega⟩)
theorem ΦDiagM_mem_unitary (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18))
    (m : ℕ) (hm : m ≤ 18) (γ : BitAssignment (posCoreWires + 18)) :
    ΦDiagM tbl m hm γ ∈ unitary ℂ :=
  prod_mem_unitary _ _ fun _ _ ↦ targetDiagScalar_mem_unitary _ _
noncomputable def uDiag18 (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18)) :
    Unitary (2 ^ (posCoreWires + 18)) :=
  diagComplexUnitaryN (ΦDiagM tbl 18 (le_refl 18)) (ΦDiagM_mem_unitary tbl 18 (le_refl 18))
def embedCircuit123 {k n : ℕ} (r : QRegister k n) : Circuit k → Circuit n
  | .identity => .identity
  | .gate g sub => .gate g (r.compose sub)
  | .seq c₁ c₂ => .seq (embedCircuit123 r c₁) (embedCircuit123 r c₂)
theorem embedCircuit123_eval {k n : ℕ} (r : QRegister k n) (c : Circuit k) :
    (embedCircuit123 r c).eval = r.embedUnitary c.eval := by
  induction c with
  | identity => simp [embedCircuit123, QRegister.embedUnitary_one]
  | gate g sub => simp [embedCircuit123, QRegister.embedUnitary_compose]
  | seq c₁ c₂ ih₁ ih₂ => simp [embedCircuit123, Circuit.eval_seq, ih₁, ih₂]
theorem embedCircuit123_count {k n a : ℕ} (r : QRegister k n) (c : Circuit k)
    (g : PrimitiveGate a) : (embedCircuit123 r c).count g = c.count g := by
  induction c with
  | identity => rfl
  | gate _ _ => rfl
  | seq c₁ c₂ ih₁ ih₂ => simp only [embedCircuit123, Circuit.count_seq, ih₁, ih₂]
def localHPrefix : (m : ℕ) → (hm : m ≤ 18) → Circuit (posCoreWires + 18)
  | 0, _ => .identity
  | m + 1, hm =>
      Circuit.H (Fin.natAdd posCoreWires ⟨m, by omega⟩) ;;ᶜ localHPrefix m (Nat.le_of_succ_le hm)
def localHSPrefix : (m : ℕ) → (hm : m ≤ 18) → Circuit (posCoreWires + 18)
  | 0, _ => .identity
  | m + 1, hm =>
      localHSPrefix m (Nat.le_of_succ_le hm) ;;ᶜ
      (Circuit.H (Fin.natAdd posCoreWires ⟨m, by omega⟩) ;;ᶜ
       Circuit.S (Fin.natAdd posCoreWires ⟨m, by omega⟩))
theorem localHPrefix_count_toff :
    ∀ (m : ℕ) (hm : m ≤ 18), (localHPrefix m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, _ => by
      simp [localHPrefix, Circuit.H, Circuit.single, Circuit.count, localHPrefix_count_toff m]
theorem localHPrefix_count_t :
    ∀ (m : ℕ) (hm : m ≤ 18), (localHPrefix m hm).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, _ => by
      simp [localHPrefix, Circuit.H, Circuit.single, Circuit.count, localHPrefix_count_t m]
theorem localHSPrefix_count_toff :
    ∀ (m : ℕ) (hm : m ≤ 18), (localHSPrefix m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, _ => by
      simp [localHSPrefix, Circuit.H, Circuit.S, Circuit.single, Circuit.count,
        localHSPrefix_count_toff m]
theorem localHSPrefix_count_t :
    ∀ (m : ℕ) (hm : m ≤ 18), (localHSPrefix m hm).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, _ => by
      simp [localHSPrefix, Circuit.H, Circuit.S, Circuit.single, Circuit.count,
        localHSPrefix_count_t m]
def writePref18 (y : BitAssignment 18) : (m : ℕ) → (hm : m ≤ 18) →
    BitAssignment (posCoreWires + 18) → BitAssignment (posCoreWires + 18)
  | 0, _, α => α
  | m + 1, hm, α =>
      Function.update (writePref18 y m (Nat.le_of_succ_le hm) α)
        (Fin.natAdd posCoreWires ⟨m, by omega⟩) (y ⟨m, by omega⟩)
theorem writePref18_core (y : BitAssignment 18) :
    ∀ (m : ℕ) (hm : m ≤ 18) (α : BitAssignment (posCoreWires + 18)) (i : Fin posCoreWires),
      writePref18 y m hm α (Fin.castAdd 18 i) = α (Fin.castAdd 18 i)
  | 0, _, _, _ => rfl
  | m + 1, hm, α, i => by
      dsimp only [writePref18]
      rw [Function.update_of_ne (Fin.ne_of_val_ne
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))) : Fin.castAdd 18 i ≠ _),
        writePref18_core y m (Nat.le_of_succ_le hm) α i]
theorem writePref18_lt (y : BitAssignment 18) :
    ∀ (m : ℕ) (hm : m ≤ 18) (α : BitAssignment (posCoreWires + 18)) (j : ℕ) (hj : j < m),
      writePref18 y m hm α (Fin.natAdd posCoreWires ⟨j, by omega⟩) = y ⟨j, by omega⟩
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, hm, α, j, hj => by
      dsimp only [writePref18]
      by_cases hjm : j = m
      · subst hjm
        simp [Function.update_self]
      · rw [Function.update_of_ne
            (Fin.ne_of_val_ne (show posCoreWires + j ≠ posCoreWires + m by omega)),
          writePref18_lt y m (Nat.le_of_succ_le hm) α j (by omega)]
theorem writePref18_update_ge (y : BitAssignment 18) :
    ∀ (m : ℕ) (hm : m ≤ 18) (α : BitAssignment (posCoreWires + 18))
      (k : ℕ) (_hk : m ≤ k) (hk18 : k < 18) (b : ZMod 2),
      writePref18 y m hm (Function.update α (Fin.natAdd posCoreWires ⟨k, hk18⟩) b) =
        Function.update (writePref18 y m hm α) (Fin.natAdd posCoreWires ⟨k, hk18⟩) b
  | 0, _, _, _, _, _, _ => rfl
  | m + 1, hm, α, k, hk, hk18, b => by
      dsimp only [writePref18]
      rw [writePref18_update_ge y m (Nat.le_of_succ_le hm) α k (by omega) hk18 b,
        Function.update_comm
          (Fin.ne_of_val_ne (Nat.ne_of_gt (Nat.add_lt_add_left hk posCoreWires)))]
theorem localHPrefix_comm_diagAbove (ψ : BitAssignment (posCoreWires + 18) → ℂ)
    (hψ : ∀ γ, ψ γ ∈ unitary ℂ) : ∀ (k : ℕ) (hk : k ≤ 18)
      (_hinv : ∀ (γ : BitAssignment (posCoreWires + 18)) (r : ℕ) (hr : r < k) (b : ZMod 2),
        ψ (Function.update γ (Fin.natAdd posCoreWires ⟨r, by omega⟩) b) = ψ γ)
      (γ : BitAssignment (posCoreWires + 18)),
      (diagComplexUnitaryN ψ hψ).1.mulVec ((localHPrefix k hk).eval.1.mulVec (ket γ)) =
        ψ γ • (localHPrefix k hk).eval.1.mulVec (ket γ)
  | 0, _, _, γ => by simp [localHPrefix, ket_diagComplexUnitaryN]
  | k + 1, hk, hinv, γ => by
      let qk : Wire (posCoreWires + 18) := Fin.natAdd posCoreWires ⟨k, by omega⟩
      have hinv' : ∀ (δ : BitAssignment (posCoreWires + 18)) (r : ℕ) (hr : r < k) (b : ZMod 2),
          ψ (Function.update δ (Fin.natAdd posCoreWires ⟨r, by omega⟩) b) = ψ δ :=
        fun δ r hr b ↦ hinv δ r (Nat.lt_succ_of_lt hr) b
      dsimp only [localHPrefix]
      rw [eval_seq_mulVec, MeasureBranchHadamardSem.ket_H,
        Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_add, Matrix.mulVec_smul,
        localHPrefix_comm_diagAbove ψ hψ k (Nat.le_of_succ_le hk) hinv' (Function.update γ qk 0),
        localHPrefix_comm_diagAbove ψ hψ k (Nat.le_of_succ_le hk) hinv' (Function.update γ qk 1),
        hinv γ k (Nat.lt_succ_self k) 0, hinv γ k (Nat.lt_succ_self k) 1]
      ext idx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
theorem diagComplexUnitaryN_mul_mulVec {d : ℕ} (Φ₁ Φ₂ : BitAssignment d → ℂ)
    (hΦ₁ : ∀ γ, Φ₁ γ ∈ unitary ℂ) (hΦ₂ : ∀ γ, Φ₂ γ ∈ unitary ℂ) (v : Fin (2 ^ d) → ℂ) :
    (diagComplexUnitaryN (fun γ ↦ Φ₁ γ * Φ₂ γ) (fun γ ↦ Submonoid.mul_mem _ (hΦ₁ γ) (hΦ₂
    γ))).1.mulVec v = (diagComplexUnitaryN Φ₁ hΦ₁).1.mulVec
    ((diagComplexUnitaryN Φ₂ hΦ₂).1.mulVec v) := by
  have hmat : (diagComplexUnitaryN (fun γ ↦ Φ₁ γ * Φ₂ γ) (fun γ ↦ Submonoid.mul_mem _ (hΦ₁ γ)
      (hΦ₂ γ))).1 = (diagComplexUnitaryN Φ₁ hΦ₁).1 * (diagComplexUnitaryN Φ₂ hΦ₂).1 := by
    apply matrix_ext_ket
    intro γ
    rw [← Matrix.mulVec_mulVec, ket_diagComplexUnitaryN, ket_diagComplexUnitaryN,
      Matrix.mulVec_smul, ket_diagComplexUnitaryN, smul_smul, mul_comm]
  rw [hmat, Matrix.mulVec_mulVec]
theorem hs_collapse_targetDiagScalar {d : ℕ} (q : Wire d) (y : ZMod 2) (β : BitAssignment d) :
    (Circuit.H q ;;ᶜ Circuit.S q).eval.1.mulVec
      (sqrtHalf • (targetDiagScalar 0 y • ket (Function.update β q 0) +
        targetDiagScalar 1 y • ket (Function.update β q 1))) = ket (Function.update β q y) := by
  let g0 := Function.update β q 0
  let g1 := Function.update β q 1
  have hII : Complex.I * -Complex.I = 1 := by
    rw [show Complex.I * -Complex.I = -(Complex.I ^ 2) by ring, Complex.I_sq, neg_neg]
  rw [eval_seq_mulVec]
  change (Circuit.S q).eval.1.mulVec ((Circuit.H q).eval.1.mulVec
    (sqrtHalf • (targetDiagScalar 0 y • ket g0 + targetDiagScalar 1 y • ket g1))) = _
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add,
    MeasureBranchHadamardSem.ket_H, ket_S_p, g0, g1,
    Function.update_self, Function.update_idem, one_ne_zero, ↓reduceIte]
  rcases bit_cases y with rfl | rfl <;> ext idx <;>
    simp only [targetDiagScalar, bitSign, one_ne_zero, ↓reduceIte,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · linear_combination (ket (Function.update β q 0) idx) * sqrtHalf_mul_self_two
  · linear_combination (ket (Function.update β q 1) idx) *
      (sqrtHalf_mul_self_two + ((sqrtHalf * sqrtHalf : ℂ) * 2) * hII)
theorem localConj_eval_ket (tbl : Fin (2 ^ posCoreWires) → Fin (2 ^ 18)) :
    ∀ (m : ℕ) (hm : m ≤ 18) (α : BitAssignment (posCoreWires + 18)),
      (∀ (k : ℕ) (hk : k < m), α (Fin.natAdd posCoreWires ⟨k, by omega⟩) = 0) →
      let x := (basisBitsEquiv posCoreWires).symm (fun i ↦ α (Fin.castAdd 18 i))
      (localHSPrefix m hm).eval.1.mulVec
        ((diagComplexUnitaryN (ΦDiagM tbl m hm) (ΦDiagM_mem_unitary tbl m hm)).1.mulVec
          ((localHPrefix m hm).eval.1.mulVec (ket α))) =
        ket (writePref18 (basisBits 18 (tbl x)) m hm α)
  | 0, _, α, _ => by
      dsimp only [localHPrefix, localHSPrefix, writePref18]
      simp [Circuit.eval_identity, ket_diagComplexUnitaryN, ΦDiagM]
  | m + 1, hm, α, hzero => by
      let hm' : m ≤ 18 := Nat.le_of_succ_le hm
      let qm : Wire (posCoreWires + 18) := Fin.natAdd posCoreWires ⟨m, by omega⟩
      let x := (basisBitsEquiv posCoreWires).symm (fun i ↦ α (Fin.castAdd 18 i))
      let y := basisBits 18 (tbl x)
      have hbs0 : bitSign (α qm) = 1 := congrArg bitSign (hzero m (Nat.lt_succ_self m))
      let α₀ := Function.update α qm 0
      let α₁ := Function.update α qm 1
      let ψm : BitAssignment (posCoreWires + 18) → ℂ := fun γ ↦ targetDiagScalar (γ qm)
        (basisBits 18 (tbl ((basisBitsEquiv posCoreWires).symm (fun i ↦ γ (Fin.castAdd 18 i))))
          ⟨m, by omega⟩)
      have hψm_unit : ∀ γ, ψm γ ∈ unitary ℂ := fun _ ↦ targetDiagScalar_mem_unitary _ _
      have hΦSplit : diagComplexUnitaryN (ΦDiagM tbl (m + 1) hm)
          (ΦDiagM_mem_unitary tbl (m + 1) hm) =
          diagComplexUnitaryN (fun γ ↦ ΦDiagM tbl m hm' γ * ψm γ)
            (fun γ ↦ Submonoid.mul_mem _ (ΦDiagM_mem_unitary tbl m hm' γ) (hψm_unit γ)) := by
        apply Subtype.ext
        apply matrix_ext_ket
        intro γ
        rw [ket_diagComplexUnitaryN, ket_diagComplexUnitaryN]
        refine congrArg (· • ket γ) ?_
        dsimp only [ΦDiagM, ψm]
        rw [Fin.prod_univ_castSucc]
        rfl
      have hψm_inv : ∀ (γ : BitAssignment (posCoreWires + 18)) (r : ℕ) (hr : r < m) (b : ZMod 2),
          ψm (Function.update γ (Fin.natAdd posCoreWires ⟨r, by omega⟩) b) = ψm γ :=
        fun γ r hr b ↦ by
          dsimp only [ψm]
          have hcore : (fun i : Fin posCoreWires ↦
              Function.update γ (Fin.natAdd posCoreWires (⟨r, by omega⟩ : Fin 18)) b
                (Fin.castAdd 18 i)) = fun i ↦ γ (Fin.castAdd 18 i) :=
            funext fun i ↦ Function.update_of_ne
              (Fin.ne_of_val_ne (Nat.ne_of_lt
                (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))) : Fin.castAdd 18 i ≠ _) _ _
          rw [Function.update_of_ne
              (Fin.ne_of_val_ne (Nat.ne_of_gt (Nat.add_lt_add_left hr posCoreWires))), hcore]
      have hx_upd : ∀ b : ZMod 2, (basisBitsEquiv posCoreWires).symm
          (fun i ↦ Function.update α qm b (Fin.castAdd 18 i)) = x :=
        fun b ↦ congrArg (basisBitsEquiv posCoreWires).symm <| funext fun i ↦
          Function.update_of_ne (Fin.ne_of_val_ne
            (Nat.ne_of_lt (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))) :
            Fin.castAdd 18 i ≠ _) _ _
      have hz_upd : ∀ (b : ZMod 2) (k : ℕ) (hk : k < m),
          Function.update α qm b (Fin.natAdd posCoreWires ⟨k, by omega⟩) = 0 := fun b k hk ↦ by
        rw [Function.update_of_ne
            (Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.add_lt_add_left hk posCoreWires)))]
        exact hzero k (Nat.lt_succ_of_lt hk)
      have ih₀ := localConj_eval_ket tbl m hm' α₀ (hz_upd 0)
      have ih₁ := localConj_eval_ket tbl m hm' α₁ (hz_upd 1)
      dsimp only at ih₀ ih₁
      rw [hx_upd 0] at ih₀
      rw [hx_upd 1] at ih₁
      have hψ₀ : ψm α₀ = targetDiagScalar 0 (y ⟨m, by omega⟩) := by
        dsimp only [ψm, α₀, y]
        rw [Function.update_self, hx_upd 0]
      have hψ₁ : ψm α₁ = targetDiagScalar 1 (y ⟨m, by omega⟩) := by
        dsimp only [ψm, α₁, y]
        rw [Function.update_self, hx_upd 1]
      have hHStep : (localHPrefix (m + 1) hm).eval.1.mulVec (ket α) =
          (localHPrefix m hm').eval.1.mulVec (sqrtHalf • (ket α₀ + ket α₁)) := by
        dsimp only [localHPrefix]
        rw [eval_seq_mulVec, MeasureBranchHadamardSem.ket_H,
          hbs0, one_smul]
      have hInner : (localHSPrefix m hm').eval.1.mulVec
          ((diagComplexUnitaryN (ΦDiagM tbl (m + 1) hm)
            (ΦDiagM_mem_unitary tbl (m + 1) hm)).1.mulVec
            ((localHPrefix m hm').eval.1.mulVec (sqrtHalf • (ket α₀ + ket α₁)))) =
          sqrtHalf • (targetDiagScalar 0 (y ⟨m, by omega⟩) •
              ket (Function.update (writePref18 y m hm' α) qm 0) +
            targetDiagScalar 1 (y ⟨m, by omega⟩) •
              ket (Function.update (writePref18 y m hm' α) qm 1)) := by
        rw [hΦSplit, diagComplexUnitaryN_mul_mulVec (ΦDiagM tbl m hm') ψm
          (ΦDiagM_mem_unitary tbl m hm') hψm_unit]
        simp only [Matrix.mulVec_smul, Matrix.mulVec_add,
          localHPrefix_comm_diagAbove ψm hψm_unit m hm' hψm_inv α₀,
          localHPrefix_comm_diagAbove ψm hψm_unit m hm' hψm_inv α₁, hψ₀, hψ₁]
        rw [ih₀, ih₁, writePref18_update_ge y m hm' α m (le_refl m) (by omega) 0,
          writePref18_update_ge y m hm' α m (le_refl m) (by omega) 1]
      rw [hHStep]
      dsimp only [localHSPrefix]
      rw [eval_seq_mulVec]
      change (Circuit.H qm ;;ᶜ Circuit.S qm).eval.1.mulVec
        ((localHSPrefix m hm').eval.1.mulVec
          ((diagComplexUnitaryN (ΦDiagM tbl (m + 1) hm)
            (ΦDiagM_mem_unitary tbl (m + 1) hm)).1.mulVec
            ((localHPrefix m hm').eval.1.mulVec (sqrtHalf • (ket α₀ + ket α₁))))) = _
      rw [hInner, hs_collapse_targetDiagScalar]
      rfl
attribute [local irreducible] uDiag18
attribute [local irreducible]
  partnerTblVal216 tailOrbitCoord128 rawOrbitCoord128 orbitRankFin16 canonTriple128 tetRank65
  tailAndSlackPhaseBitSpec
attribute [local irreducible] DynCircuitExt.measureXResetAndBranch
end ConfigPartner216
set_option exponentiation.threshold 256
set_option maxRecDepth 2000
end PosSlots24PartnerMuxZeroT123
end
end ModPosSlots24PartnerMuxZeroT123

end QuantumComputation.Specs.StoppingPowerSolution
