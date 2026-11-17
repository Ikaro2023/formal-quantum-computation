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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3MicroEngine

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
section ModFastMidKick275
@[expose] public section
namespace FastMidKick275Aux
section ConfigFastMidKick275
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
local instance (priority := 1000000) instNeZeroTwoPowFmk (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Real SpecsAux
open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_lt wire_ne_of_gt CliffProg
  TempPhaseProg cleanRem
  cleanRem_anti ValidCleanRem validCleanRem_mono ScopedBlock withCliffAlloc
  withCliffAlloc_countTempAnd fullAdd_val_eq withUnarySplit unarySplitSetup CliffDisjoint
  TempCtx ctxCliffAlloc ctxCliffAlloc_plug ctxCliffAlloc_disjoint ctxCliffAlloc_supports
  ctxTempBit ctxTempBit_plug)
open TwosCompAndWire0Cancel (twosComp8Int)
open ModWrapCoarse8PureMomentum (nearestProtonCoord)
open scoped BigOperators
theorem fmkItePos {α : Type*} {p : Prop} [inst : Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := ite_eq_left h
theorem fmkIteNeg {α : Type*} {p : Prop} [inst : Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := ite_eq_right h
theorem fmkDItePos {α : Type*} {p : Prop} [inst : Decidable p] (h : p) (a : p → α)
    (b : ¬ p → α) : (if hp : p then a hp else b hp) = a h := dite_eq_left h
theorem fmkEqTransItePos {α : Type*} {x a b : α} {p : Prop} {inst : Decidable p}
    (h1 : x = @ite α p inst a b) (hp : p) : x = a := h1.trans (@fmkItePos α p inst hp a b)
theorem fmkEqTransIteNeg {α : Type*} {x a b : α} {p : Prop} {inst : Decidable p}
    (h1 : x = @ite α p inst a b) (hnp : ¬ p) : x = b := h1.trans (@fmkIteNeg α p inst hnp a b)
theorem fmkEqTransDItePos {α : Type*} {x : α} {p : Prop} {inst : Decidable p}
    {a : p → α} {b : ¬ p → α} (h1 : x = @dite α p inst a b) (hp : p) : x = a hp :=
  h1.trans (@fmkDItePos α p inst hp a b)
theorem fmkEqTransDIteNeg {α : Type*} {x : α} {p : Prop} {inst : Decidable p}
    {a : p → α} {b : ¬ p → α} (h1 : x = @dite α p inst a b) (hnp : ¬ p) : x = b hnp :=
  letI := inst
  h1.trans (dite_eq_right hnp)
theorem fmkBit_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b <;> simp
theorem fmkZmod2_add_self_cancel (a b : ZMod 2) : a + b + b = a := by
  rcases fmkBit_cases a with rfl | rfl <;> rcases fmkBit_cases b with rfl | rfl <;> decide
theorem fmkLtTrans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h1 h2
theorem fmkLtLe {a b c : ℕ} (h1 : a < b) (h2 : b ≤ c) : a < c := Nat.lt_of_lt_of_le h1 h2
theorem fmkInt_add_emod (a b n : ℤ) : (a + b).emod n = (a.emod n + b.emod n).emod n :=
  Int.add_emod a b n
theorem fmkInt_emod_eq_mod (a b : ℤ) : a.emod b = a % b := rfl
theorem fmkEmod_eq_of_add_mul {a b m : ℤ} (q : ℤ) (h : a = b + q * m) : a.emod m = b.emod m := by
  rw [h, fmkInt_emod_eq_mod, fmkInt_emod_eq_mod, Int.add_mul_emod_self_right]
theorem fmkAddCongr {α : Type*} [Add α] {a₁ a₂ b₁ b₂ : α} (ha : a₁ = a₂) (hb : b₁ = b₂) :
    a₁ + b₁ = a₂ + b₂ := by
  rw [ha, hb]
theorem fmkBitsVal_zero (W : ℕ) : bitsVal (fun _ : Fin W ↦ (0 : ZMod 2)) = 0 := by
  simp [bitsVal]
theorem fmkAdd_two_mul_mod (W s0 S : ℕ) (hs0 : s0 < 2) :
    (s0 + 2 * S) % 2 ^ (W + 1) = s0 + 2 * (S % 2 ^ W) := by
  have hlt : s0 + 2 * (S % 2 ^ W) < 2 ^ (W + 1) := by
    have := Nat.mod_lt S (by positivity : 0 < 2 ^ W)
    rw [pow_succ]
    omega
  have hsp : s0 + 2 * S = (s0 + 2 * (S % 2 ^ W)) + (S / 2 ^ W) * 2 ^ (W + 1) := by
    conv_lhs => rw [← Nat.div_add_mod S (2 ^ W)]
    rw [pow_succ]
    ring
  rw [hsp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
theorem fmkBitsVal_succ_split {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
    bitsVal f = (f 0).val + 2 * bitsVal (fun j ↦ f j.succ) :=
      Slot3MicroEngineAux.bitsVal_succ_split f
theorem fmkBitsVal_castSucc_split {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
    bitsVal f = bitsVal (fun j : Fin W ↦ f j.castSucc) + 2 ^ W * (f (Fin.last W)).val := by
  rw [bitsVal, Fin.sum_univ_castSucc]
  simp [bitsVal, mul_comm]
theorem fmkBitsVal_slice_linear {N W k : ℕ} (hkW : k + W = N)
    (f g : Fin N → ZMod 2) (hlow : ∀ m : Fin N, m.val < k → g m = f m) :
    bitsVal g + 2 ^ k * bitsVal (fun j : Fin W ↦ f ⟨k + j.val, by omega⟩) =
      bitsVal f + 2 ^ k * bitsVal (fun j : Fin W ↦ g ⟨k + j.val, by omega⟩) := by
  subst hkW
  simp only [bitsVal, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd, Finset.mul_sum]
  have hlo : ∑ i : Fin k, (g (Fin.castAdd W i)).val * 2 ^ i.val =
      ∑ i : Fin k, (f (Fin.castAdd W i)).val * 2 ^ i.val :=
    Finset.sum_congr rfl fun i _ ↦ by rw [hlow _ (by simp)]
  have hhi : ∀ h : Fin (k + W) → ZMod 2,
      ∑ j : Fin W, 2 ^ k * ((h ⟨k + j.val, by omega⟩).val * 2 ^ j.val) =
      ∑ j : Fin W, (h (Fin.natAdd k j)).val * 2 ^ (k + j.val) :=
    fun h ↦ Finset.sum_congr rfl fun j _ ↦ by
      have hj : (⟨k + j.val, by omega⟩ : Fin (k + W)) = Fin.natAdd k j := Fin.ext (by simp)
      rw [hj, pow_add]
      ring
  rw [hlo, hhi f, hhi g]
  ring
theorem fmkBitsVal_take_mod : ∀ {N : ℕ} (W : ℕ) (hW : W ≤ N) (f : Fin N → ZMod 2),
      bitsVal (fun j : Fin W ↦ f ⟨j.val, by omega⟩) = bitsVal f % 2 ^ W
  | _, 0, _, _ => by simp [bitsVal, Nat.mod_one]
  | 0, W + 1, hW, _ => absurd hW (by omega)
  | N + 1, W + 1, hW, f => by
      rw [fmkBitsVal_succ_split (fun j : Fin (W + 1) ↦ f ⟨j.val, by omega⟩),
        fmkBitsVal_succ_split f]
      have htail : (fun j : Fin W ↦ f ⟨j.succ.val, by omega⟩) =
          fun j : Fin W ↦ (fun i : Fin N ↦ f i.succ) ⟨j.val, by omega⟩ :=
        funext fun _ ↦ congrArg f (Fin.ext rfl)
      rw [htail, fmkBitsVal_take_mod W (by omega) (fun i : Fin N ↦ f i.succ)]
      exact (fmkAdd_two_mul_mod W _ _ (ZMod.val_lt (f 0))).symm
theorem fmkBitsVal_eq_of_testBit {W : ℕ} (f : Fin W → ZMod 2) (v : ℕ) (hv : v < 2 ^ W)
    (h : ∀ j : Fin W, f j = if v.testBit j.val then 1 else 0) : bitsVal f = v :=
  Slot3MicroEngineAux.bitsVal_eq_of_testBit f v hv h
theorem fmkBitsVal_flip_all : ∀ (W : ℕ) (f : Fin W → ZMod 2),
      bitsVal (fun j ↦ f j + 1) + bitsVal f = 2 ^ W - 1
  | 0, _ => rfl
  | W + 1, f => by
      rw [fmkBitsVal_succ_split (fun j ↦ f j + 1), fmkBitsVal_succ_split f]
      have hih := fmkBitsVal_flip_all W (fun j ↦ f j.succ)
      have hp : 1 ≤ 2 ^ W := Nat.one_le_two_pow
      have hp2 : 2 ^ (W + 1) = 2 * 2 ^ W := by ring
      rcases fmkBit_cases (f 0) with h0 | h1
      · rw [h0]
        change 1 + 2 * bitsVal _ + (0 + 2 * bitsVal _) = _
        omega
      · rw [h1]
        change 0 + 2 * bitsVal _ + (1 + 2 * bitsVal _) = _
        omega
def fmkXVec {M : ℕ} : (W : ℕ) → (Fin W → Wire M) → CliffProg M
  | 0, _ => .nil
  | W + 1, dst => .seq (.x (dst 0)) (fmkXVec W (fun j ↦ dst j.succ))
theorem fmkXVec_supportsBelow {M bound : ℕ} : ∀ (W : ℕ) (dst : Fin W → Wire M),
      (∀ j, (dst j).val < bound) → (fmkXVec W dst).SupportsBelow bound
  | 0, _, _ => trivial
  | W + 1, _dst, h => ⟨h 0, fmkXVec_supportsBelow W _ (fun j ↦ h j.succ)⟩
theorem fmkXVec_disjoint {M : ℕ} {mutW : Wire M → Prop} : ∀ (W : ℕ) (dst : Fin W → Wire M),
      (∀ j, ¬ mutW (dst j)) → CliffDisjoint mutW (fmkXVec W dst)
  | 0, _, _ => trivial
  | W + 1, _dst, h => ⟨h 0, fmkXVec_disjoint W _ (fun j ↦ h j.succ)⟩
theorem fmkXVec_eval {M : ℕ} : ∀ (W : ℕ) (dst : Fin W → Wire M) (_ : Function.Injective dst)
      (β : BitAssignment M) (w : Wire M),
      (fmkXVec W dst).eval β w = if ∃ j, w = dst j then β w + 1 else β w
  | 0, _, _, _, _ => by simp [fmkXVec, CliffProg.eval]
  | W + 1, dst, hinj, β, w => by
      dsimp only [fmkXVec, CliffProg.eval]
      rw [fmkXVec_eval W (fun j ↦ dst j.succ) (fun _ _ h ↦ Fin.succ_injective W (hinj h))]
      simp only [Fin.exists_fin_succ]
      by_cases h0 : w = dst 0
      · subst h0
        have hnone : ¬ ∃ j : Fin W, dst 0 = dst j.succ :=
          fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (hinj hj.symm)
        simp [hnone]
      · simp [h0]
def fmkFanoutCnot {M : ℕ} : (W : ℕ) → (ctrl : Wire M) → (dst : Fin W → Wire M) →
    (∀ j, ctrl ≠ dst j) → CliffProg M
  | 0, _, _, _ => .nil
  | W + 1, ctrl, dst, hne =>
      .seq (.cnot ctrl (dst 0) (hne 0))
        (fmkFanoutCnot W ctrl (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem fmkFanoutCnot_supportsBelow {M bound : ℕ} :
    ∀ (W : ℕ) (ctrl : Wire M) (dst : Fin W → Wire M) (hne : ∀ j, ctrl ≠ dst j),
      ctrl.val < bound → (∀ j, (dst j).val < bound) →
      (fmkFanoutCnot W ctrl dst hne).SupportsBelow bound
  | 0, _, _, _, _, _ => trivial
  | W + 1, ctrl, _dst, _hne, hc, hd =>
      ⟨⟨hc, hd 0⟩, fmkFanoutCnot_supportsBelow W ctrl _ _ hc (fun j ↦ hd j.succ)⟩
theorem fmkFanoutCnot_disjoint {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (W : ℕ) (ctrl : Wire M) (dst : Fin W → Wire M) (hne : ∀ j, ctrl ≠ dst j),
      ¬ mutW ctrl → (∀ j, ¬ mutW (dst j)) → CliffDisjoint mutW (fmkFanoutCnot W ctrl dst hne)
  | 0, _, _, _, _, _ => trivial
  | W + 1, ctrl, _, _, hc, hd =>
      ⟨⟨hc, hd 0⟩, fmkFanoutCnot_disjoint W ctrl _ _ hc (fun j ↦ hd j.succ)⟩
theorem fmkFanoutCnot_eval {M : ℕ} :
    ∀ (W : ℕ) (ctrl : Wire M) (dst : Fin W → Wire M) (hne : ∀ j, ctrl ≠ dst j)
      (_ : Function.Injective dst) (β : BitAssignment M) (w : Wire M),
      (fmkFanoutCnot W ctrl dst hne).eval β w = if ∃ j, w = dst j then β w + β ctrl else β w
  | 0, _, _, _, _, _, _ => by simp [fmkFanoutCnot, CliffProg.eval]
  | W + 1, ctrl, dst, hne, hinj, β, w => by
      dsimp only [fmkFanoutCnot, CliffProg.eval]
      rw [fmkFanoutCnot_eval W ctrl (fun j ↦ dst j.succ) _
          (fun _ _ h ↦ Fin.succ_injective W (hinj h)), Function.update_of_ne (hne 0)]
      simp only [Fin.exists_fin_succ]
      by_cases h0 : w = dst 0
      · subst h0
        have hnone : ¬ ∃ j : Fin W, dst 0 = dst j.succ :=
          fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (hinj hj.symm)
        simp [hnone]
      · simp [h0]
def fmkCnotVec {M : ℕ} : (W : ℕ) → (src dst : Fin W → Wire M) → (∀ j, src j ≠ dst j) → CliffProg M
  | 0, _, _, _ => .nil
  | W + 1, src, dst, hne =>
      .seq (.cnot (src 0) (dst 0) (hne 0))
        (fmkCnotVec W (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem fmkCnotVec_eq {M : ℕ} : ∀ (W : ℕ) (src dst : Fin W → Wire M) (hne : ∀ j, src j ≠ dst j),
      fmkCnotVec W src dst hne = Slot3MicroEngineAux.cnotVec W src dst hne
  | 0, _, _, _ => rfl
  | W + 1, _, _, _ => congrArg _ (fmkCnotVec_eq W _ _ _)
theorem fmkSupportsBelowCtx_cleanRem {M curHole : ℕ} {K : TempCtx M}
    (hSupp : K.SupportsBelowCtx curHole) : ∀ (β : BitAssignment M), cleanRem M (M - curHole) β
    → cleanRem M (M - curHole) (K.fwdBits β) :=
  fun _ hβ ↦ Slot3MicroEngineAux.TempCtx.cleanRem_of_supports curHole curHole le_rfl hSupp hβ
theorem fmkAppend_fwdBits {M : ℕ} (F G : TempCtx M) (β : BitAssignment M) :
    (F.append G).fwdBits β = G.fwdBits (F.fwdBits β) :=
  Slot3MicroEngineAux.TempCtx.append_fwdBits F G β
theorem fmkAppend_countTempAnd {M : ℕ} (F G : TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd :=
  Slot3MicroEngineAux.TempCtx.append_countTempAnd F G
theorem fmkXorBlock_of_ctx {M curStart curEnd W : ℕ} [NeZero M]
    (hEnd : curEnd ≤ M) (hStart : curStart ≤ curEnd)
    (out : Fin W → Wire M) (hout_lt : ∀ j, (out j).val < curStart)
    (hout_inj : Function.Injective out)
    (src : Fin W → Wire M) (hsrc_ge : ∀ j, curStart ≤ (src j).val) (K : TempCtx M)
    (hDisj : K.DisjointFrom (fun w ↦ ∃ j, w = out j)) (hSupp : K.SupportsBelowCtx curEnd)
    (setup : BitAssignment M → BitAssignment M)
    (hProbe : ∀ q : Wire M, ScopedBlock M (M - curStart) setup (.z q) (K.plug (.z q))) :
    let hne : ∀ j, src j ≠ out j := fun j ↦ wire_ne_of_gt (fmkLtLe (hout_lt j) (hsrc_ge j))
    let p := K.plug (.cliff (fmkCnotVec W src out hne))
    ValidCleanRem M (M - curStart) p ∧ p.countTempAnd = K.countTempAnd ∧
      (∀ β : BitAssignment M, cleanRem M (M - curStart) β → p.evalSign β = 0) ∧
      (∀ β : BitAssignment M, cleanRem M (M - curStart) β → ∀ w : Wire M,
        p.evalBits β w = if h : ∃ j, w = out j then β w + setup β (src h.choose) else β w) := by
  dsimp only
  rw [fmkCnotVec_eq]
  exact Slot3MicroEngineAux.xorBlock_of_ctx hEnd hStart out hout_lt hout_inj src hsrc_ge
    K hDisj hSupp setup hProbe
theorem fmkPlug_evalBits_split_clean {M : ℕ} {mutW : Wire M → Prop} {curHole : ℕ}
    {K : TempCtx M} (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx curHole)
    {body : TempPhaseProg M} (hBodyNonMut : ∀ γ, cleanRem M (M - curHole) γ → ∀ w, ¬ mutW w →
    body.evalBits γ w = γ w) (q₀ : Wire M) : ∀ (β : BitAssignment M), cleanRem M (M - curHole)
    β → (∀ w, mutW w → (K.plug body).evalBits β w = body.evalBits (K.fwdBits β) w) ∧ (∀ w, ¬
    mutW w → (K.plug body).evalBits β w = (K.plug (.z q₀)).evalBits β w) := by
  induction K with
  | hole => exact fun β hβ ↦ ⟨fun _ _ ↦ rfl, fun w hw ↦ hBodyNonMut β hβ w hw⟩
  | seqPre c _ ih =>
      intro β hβ
      refine ih hDisj.2 hSupp.2 (c.eval β) fun w hw ↦ ?_
      rw [c.eval_outside hSupp.1 β w (by omega)]
      exact hβ w hw
  | seqPost _ _ ih =>
      intro β hβ
      obtain ⟨hM, hN⟩ := ih hDisj.1 hSupp.1 β hβ
      exact ⟨fun w hw ↦ (hDisj.2.eval_mut _ hw).trans (hM w hw),
        fun w hw ↦ hDisj.2.eval_congr_nonMut hN w hw⟩
  | tempAnd c₁ c₂ anc _ _ _ K₁ ih =>
      intro β hβ
      set β₁ := Function.update β anc (β anc + β c₁ * β c₂)
      have hβ₁ : cleanRem M (M - curHole) β₁ := fun w hw ↦ by
        dsimp only [β₁]
        rw [Function.update_of_ne (wire_ne_of_gt (fmkLtLe hSupp.1 (by omega)))]
        exact hβ w hw
      obtain ⟨hM, hN⟩ := ih hDisj.2.2.2 hSupp.2 β₁ hβ₁
      refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · dsimp only [TempCtx.plug, TempPhaseProg.evalBits, TempCtx.fwdBits]
        rw [Function.update_of_ne (by rintro rfl; exact hDisj.2.2.1 hw)]
        exact hM w hw
      · dsimp only [TempCtx.plug, TempPhaseProg.evalBits]
        by_cases hwa : w = anc
        · rw [hwa, Function.update_self, Function.update_self,
            hN c₁ hDisj.1, hN c₂ hDisj.2.1, hN anc hDisj.2.2.1]
        · rw [Function.update_of_ne hwa, Function.update_of_ne hwa, hN w hw]
theorem fmkPlug_validCleanRem_clean {M : ℕ} {mutW : Wire M → Prop} {curHole : ℕ}
    {K : TempCtx M} (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx curHole)
    {body : TempPhaseProg M} (hBodyValid : ValidCleanRem M (M - curHole) body) (hBodyNonMut :
    ∀ γ, cleanRem M (M - curHole) γ → ∀ w, ¬ mutW w → body.evalBits γ w = γ w) (q₀ : Wire M) :
    ∀ {rem : ℕ}, M - curHole ≤ rem → ValidCleanRem M rem (K.plug (.z q₀)) → ValidCleanRem M
    rem (K.plug body) := by
  induction K with
  | hole => exact fun hle _ ↦ validCleanRem_mono hle hBodyValid
  | seqPre c _ ih =>
      intro rem _ ⟨remMid, _, _, hv₁, hpres₁⟩
      refine ⟨max remMid (M - curHole), by omega, trivial,
        ih hDisj.2 hSupp.2 (Nat.le_max_right _ _) (validCleanRem_mono (Nat.le_max_left _ _) hv₁),
        fun β hβ w hw ↦ ?_⟩
      by_cases hw1 : M - remMid ≤ w.val
      · exact hpres₁ β hβ w hw1
      · rw [TempPhaseProg.evalBits, c.eval_outside hSupp.1 β w (by omega)]
        exact hβ w (by omega)
  | seqPost _ _ ih =>
      intro rem hle ⟨_, _, hv₁, _, _⟩
      exact ⟨0, Nat.zero_le M, ih hDisj.1 hSupp.1 hle hv₁, trivial,
        fun _ _ _ hw ↦ absurd hw (by omega)⟩
  | tempAnd c₁ c₂ anc _ _ _ _ ih =>
      intro rem _ ⟨hanc_lo, hv₁, hpres₁⟩
      have hrem' : M - curHole ≤ M - (anc.val + 1) := by have := hSupp.1; omega
      refine ⟨hanc_lo, ih hDisj.2.2.2 hSupp.2 hrem' hv₁, fun β₁ hβ₁ ↦ ?_⟩
      obtain ⟨_, hN⟩ := fmkPlug_evalBits_split_clean hDisj.2.2.2 hSupp.2 hBodyNonMut q₀ β₁
        (cleanRem_anti hrem' hβ₁)
      rw [hN c₁ hDisj.1, hN c₂ hDisj.2.1, hN anc hDisj.2.2.1]
      exact hpres₁ β₁ hβ₁
theorem fmkGraft_mutating_clean {M rem curHole : ℕ} [NeZero M] (mutW : Wire M → Prop)
    [DecidablePred mutW] (K : TempCtx M) (hDisj : K.DisjointFrom mutW)
    (hSupp : K.SupportsBelowCtx curHole) (hle : M - curHole ≤ rem)
    (setup : BitAssignment M → BitAssignment M) (hProbe : ∀ q : Wire M, ScopedBlock M rem
    setup (.z q) (K.plug (.z q))) (body : TempPhaseProg M)
    (hBodyValid : ValidCleanRem M (M - curHole) body) (hBodyNonMut : ∀ γ, cleanRem M (M -
    curHole) γ → ∀ w, ¬ mutW w → body.evalBits γ w = γ w) : ValidCleanRem M rem (K.plug body)
    ∧ (K.plug body).countTempAnd = K.countTempAnd + body.countTempAnd ∧ (∀ β : BitAssignment
    M, cleanRem M rem β → (K.plug body).evalSign β = body.evalSign (setup β)) ∧ (∀ β :
    BitAssignment M, cleanRem M rem β → ∀ w : Wire M, (K.plug body).evalBits β w = if mutW w
    then body.evalBits (setup β) w else β w) := by
  let q₀ : Wire M := ⟨0, NeZero.pos M⟩
  have hFwd : ∀ β : BitAssignment M, cleanRem M rem β → K.fwdBits β = setup β :=
    fun β hβ ↦ funext fun q ↦ Slot3MicroEngineAux.TempCtx.fwdBits_eq_of_block K q (hProbe q) β hβ
  refine ⟨fmkPlug_validCleanRem_clean hDisj hSupp hBodyValid hBodyNonMut q₀ hle (hProbe q₀).valid,
    K.plug_countTempAnd body, fun β hβ ↦ by rw [K.plug_evalSign, hFwd β hβ], fun β hβ w ↦ ?_⟩
  obtain ⟨hM, hN⟩ := fmkPlug_evalBits_split_clean hDisj hSupp hBodyNonMut q₀ β
    (cleanRem_anti hle hβ)
  by_cases hw : mutW w
  · simp only [hw, ↓reduceIte, hM w hw, hFwd β hβ]
  · simp only [hw, ↓reduceIte, hN w hw, (hProbe q₀).bits β hβ]
def fmkTempCtxLiftEx {M : ℕ} (cur next : ℕ) (K : TempCtx M) : Prop :=
  ∀ {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M},
    ScopedBlock M (M - next) sBody leaf body →
    ∃ sOut, ScopedBlock M (M - cur) sOut leaf (K.plug body)
theorem fmkTempCtxLiftEx_probe {M cur next : ℕ} {K : TempCtx M}
    (hK : fmkTempCtxLiftEx cur next K) (q : Wire M) :
    ScopedBlock M (M - cur) K.fwdBits (.z q) (K.plug (.z q)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.probe hK q
theorem fmkTempCtxLiftEx_mono {M cur₀ cur₁ next₀ next₁ : ℕ} {K : TempCtx M}
    (hc : cur₀ ≤ cur₁) (hn : next₀ ≤ next₁) (hM : next₁ ≤ M) (hK : fmkTempCtxLiftEx cur₁ next₀ K) :
    fmkTempCtxLiftEx cur₀ next₁ K := Slot3MicroEngineAux.TempCtxLiftEx.mono hK hc hn hM
theorem fmkTempCtxLiftEx_append {M cur mid next : ℕ} {F G : TempCtx M}
    (hF : fmkTempCtxLiftEx cur mid F) (hG : fmkTempCtxLiftEx mid next G) :
    fmkTempCtxLiftEx cur next (F.append G) := Slot3MicroEngineAux.TempCtxLiftEx.append hF hG
theorem fmkTempCtxLiftEx_cliff {M cur : ℕ} (hcur : cur ≤ M) (c : CliffProg M)
    (hc : c.SupportsBelow cur) : fmkTempCtxLiftEx cur cur (ctxCliffAlloc c) :=
  Slot3MicroEngineAux.TempCtxLiftEx.cliff cur hcur c hc
theorem fmkTempCtxLiftEx_tempBit {M cur : ℕ} (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) : fmkTempCtxLiftEx cur (cur + 1)
    (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.tempBit cur hcur c₁ c₂ h12 hc1 hc2
def fmkCtxUnarySplit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (loWire sel : Wire M)
    (hlo_sel : loWire ≠ sel) (hlo : loWire.val < cur) (hsel : sel.val < cur) : TempCtx M :=
  let hiWire : Wire M := ⟨cur, by omega⟩
  (ctxTempBit loWire sel hiWire hlo_sel
    (wire_ne_of_lt (by dsimp [hiWire]; omega))
    (wire_ne_of_lt (by dsimp [hiWire]; omega))).append
    (ctxCliffAlloc (.cnot hiWire loWire (wire_ne_of_gt (by dsimp [hiWire]; omega))))
def fmkCtxSplitPrefix {M : ℕ} (srcBase dstBase N : ℕ) (sel : Wire M)
    (hsel : sel.val < srcBase) (hgap : srcBase + N ≤ dstBase) (hdst : dstBase + N ≤ M) :
    (remK : ℕ) → (hK : remK ≤ N) → TempCtx M
  | 0, _ => .hole
  | remK + 1, _ =>
      let idx := N - (remK + 1)
      let pos := dstBase + idx
      (fmkCtxUnarySplit pos (by dsimp [pos, idx]; omega)
        ⟨srcBase + idx, by dsimp [idx]; omega⟩ sel
        (wire_ne_of_gt (by dsimp; omega))
        (by dsimp [pos, idx]; omega) (by dsimp [pos]; omega)).append
        (fmkCtxSplitPrefix srcBase dstBase N sel hsel hgap hdst remK (by omega))
theorem fmkCtxSplitPrefix_countTempAnd {M : ℕ} (srcBase dstBase N : ℕ) (sel : Wire M)
    (hsel : sel.val < srcBase) (hgap : srcBase + N ≤ dstBase) (hdst : dstBase + N ≤ M) :
    ∀ (remK : ℕ) (hK : remK ≤ N),
      (fmkCtxSplitPrefix srcBase dstBase N sel hsel hgap hdst remK hK).countTempAnd = remK
  | 0, _ => rfl
  | remK + 1, _ => by
      dsimp only [fmkCtxSplitPrefix]
      rw [fmkAppend_countTempAnd,
        fmkCtxSplitPrefix_countTempAnd srcBase dstBase N sel hsel hgap hdst remK (by omega)]
      change 1 + remK = remK + 1
      omega
theorem fmkCtxSplitPrefix_props {M : ℕ} {mutW : Wire M → Prop}
    (srcBase dstBase N : ℕ) (sel : Wire M)
    (hsel : sel.val < srcBase) (hgap : srcBase + N ≤ dstBase) (hdst : dstBase + N ≤ M)
    (hnsel : ¬ mutW sel) (hnsrc : ∀ w : Wire M, srcBase ≤ w.val → w.val < srcBase + N → ¬ mutW w)
    (hndst : ∀ w : Wire M, dstBase ≤ w.val → w.val < dstBase + N → ¬ mutW w) :
    ∀ (remK : ℕ) (hK : remK ≤ N),
      (fmkCtxSplitPrefix srcBase dstBase N sel hsel hgap hdst remK hK).DisjointFrom mutW ∧
      (fmkCtxSplitPrefix srcBase dstBase N sel hsel hgap hdst remK hK).SupportsBelowCtx
        (dstBase + N)
  | 0, _ => ⟨trivial, trivial⟩
  | remK + 1, hK => by
      obtain ⟨hdR, hsR⟩ := fmkCtxSplitPrefix_props srcBase dstBase N sel hsel hgap hdst
        hnsel hnsrc hndst remK (by omega)
      let idx := N - (remK + 1)
      let pos := dstBase + idx
      have hnlo := hnsrc ⟨srcBase + idx, by dsimp [idx]; omega⟩
        (by dsimp [idx]; omega) (by dsimp [idx]; omega)
      have hnhi := hndst ⟨pos, by dsimp [pos, idx]; omega⟩
        (by dsimp [pos, idx]; omega) (by dsimp [pos, idx]; omega)
      exact ⟨TempCtx.disjointFrom_append
          (TempCtx.disjointFrom_append ⟨hnlo, hnsel, hnhi, trivial⟩
            (ctxCliffAlloc_disjoint ⟨hnhi, hnlo⟩)) hdR,
        TempCtx.supportsBelowCtx_append (by dsimp [pos, idx]; omega)
          (TempCtx.supportsBelowCtx_append le_rfl ⟨Nat.lt_succ_self pos, trivial⟩
            (ctxCliffAlloc_supports ⟨Nat.lt_succ_self pos, by dsimp [pos, idx]; omega⟩)) hsR⟩
theorem fmkCtxSplitPrefix_scoped {M : ℕ} (srcBase dstBase N : ℕ) (sel : Wire M)
    (hsel : sel.val < srcBase) (hgap : srcBase + N ≤ dstBase) (hdst : dstBase + N ≤ M) :
    ∀ (remK : ℕ) (hK : remK ≤ N),
      let K := fmkCtxSplitPrefix srcBase dstBase N sel hsel hgap hdst remK hK
      fmkTempCtxLiftEx (dstBase + (N - remK)) (dstBase + N) K ∧
      (∀ β : BitAssignment M, cleanRem M (M - (dstBase + (N - remK))) β →
        cleanRem M (M - (dstBase + N)) (K.fwdBits β) ∧ (∀ i : ℕ, N - remK ≤ i → (hi : i < N) →
          K.fwdBits β ⟨srcBase + i, by omega⟩ =
            β ⟨srcBase + i, by omega⟩ + β ⟨srcBase + i, by omega⟩ * β sel) ∧
        (∀ i : ℕ, N - remK ≤ i → (hi : i < N) → K.fwdBits β ⟨dstBase + i, by omega⟩ =
            β ⟨srcBase + i, by omega⟩ * β sel) ∧ (∀ w : Wire M,
          ¬(srcBase + (N - remK) ≤ w.val ∧ w.val < srcBase + N) →
          ¬(dstBase + (N - remK) ≤ w.val ∧ w.val < dstBase + N) → K.fwdBits β w = β w))
  | 0, _ => by
      dsimp only [fmkCtxSplitPrefix, fmkTempCtxLiftEx, TempCtx.plug, TempCtx.fwdBits]
      rw [show dstBase + (N - 0) = dstBase + N by omega]
      exact ⟨fun h ↦ ⟨_, h⟩, fun _ hβ ↦ ⟨hβ, fun _ _ hhi ↦ absurd hhi (by omega),
        fun _ _ hhi ↦ absurd hhi (by omega), fun _ _ _ ↦ rfl⟩⟩
  | remK + 1, hK => by
      dsimp only [fmkCtxSplitPrefix]
      let idx := N - (remK + 1)
      let pos := dstBase + idx
      have hpos : pos + 1 ≤ M := by omega
      let loW : Wire M := ⟨srcBase + idx, by omega⟩
      let hiW : Wire M := ⟨pos, hpos⟩
      have hlo : loW.val < pos := show srcBase + idx < dstBase + idx by omega
      have hsp : sel.val < pos := by omega
      have hls : loW ≠ sel := wire_ne_of_gt (show sel.val < srcBase + idx by omega)
      let K0 := fmkCtxUnarySplit pos hpos loW sel hls hlo hsp
      have hplug0 (body) : K0.plug body = withUnarySplit pos hpos loW sel hls hlo hsp body := by
        simp only [K0, fmkCtxUnarySplit, withUnarySplit, TempCtx.append_plug,
          ctxCliffAlloc_plug, ctxTempBit_plug]
      have hBlk0 {leaf body sB} (hB : ScopedBlock M (M - (pos + 1)) sB leaf body) :=
        (hplug0 body).symm ▸ ScopedBlock.withUnarySplit_block pos hpos loW sel hls hlo hsp hB
      obtain ⟨hLiftR, hSpecR⟩ :=
        fmkCtxSplitPrefix_scoped srcBase dstBase N sel hsel hgap hdst remK (by omega)
      refine ⟨fmkTempCtxLiftEx_append ((show pos + 1 = dstBase + (N - remK) by omega) ▸
          fun hB ↦ ⟨_, hBlk0 hB⟩) hLiftR, fun β hβ ↦ ?_⟩
      let β₁ := unarySplitSetup pos hpos loW sel β
      rw [fmkAppend_fwdBits, show K0.fwdBits β = β₁ from funext fun u ↦
        Slot3MicroEngineAux.TempCtx.fwdBits_eq_of_block K0 u (hBlk0 (ScopedBlock.z_kick u)) β hβ]
      have hβ₁_ne (w : Wire M) (h1 : w ≠ loW) (h2 : w ≠ hiW) : β₁ w = β w := by
        dsimp only [β₁, unarySplitSetup]
        rw [Function.update_of_ne h1, Function.update_of_ne h2]
      have hβ₁_sel : β₁ sel = β sel := hβ₁_ne sel hls.symm (wire_ne_of_lt hsp)
      have hβ₁_src {i : ℕ} (hi : i ≠ idx) (hhi : i < N) :
          β₁ ⟨srcBase + i, by omega⟩ = β ⟨srcBase + i, by omega⟩ :=
        hβ₁_ne _ (Fin.ne_of_val_ne (by dsimp [loW, idx]; omega))
          (wire_ne_of_lt (by dsimp [hiW, pos, idx]; omega))
      obtain ⟨hclOut, hSrcR, hDstR, hOutR⟩ := hSpecR β₁ fun w hw ↦
        (hβ₁_ne w (wire_ne_of_gt (by dsimp [loW, idx]; omega))
          (wire_ne_of_gt (by dsimp [hiW, pos, idx]; omega))).trans (hβ w (by omega))
      refine ⟨hclOut, fun i hlo' hhi ↦ ?_, fun i hlo' hhi ↦ ?_, fun w hns hnd ↦ ?_⟩
      · by_cases hi_eq : i = idx
        · subst hi_eq
          exact (hOutR loW (by dsimp [loW, idx]; omega) (by dsimp [loW, idx]; omega)).trans
            (Function.update_self _ _ _)
        · rw [hSrcR i (by dsimp [idx] at hi_eq; omega) hhi, hβ₁_sel, hβ₁_src hi_eq hhi]
      · by_cases hi_eq : i = idx
        · subst hi_eq
          rw [hOutR hiW (by dsimp [hiW, pos, idx]; omega) (by dsimp [hiW, pos, idx]; omega)]
          dsimp only [β₁, unarySplitSetup, hiW]
          rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [loW, pos, idx]; omega)),
            Function.update_self]
        · rw [hDstR i (by dsimp [idx] at hi_eq; omega) hhi, hβ₁_sel, hβ₁_src hi_eq hhi]
      · rw [hOutR w (by omega) (by omega), hβ₁_ne w (Fin.ne_of_val_ne (by dsimp [loW, idx]; omega))
            (Fin.ne_of_val_ne (by dsimp [hiW, pos, idx]; omega))]
theorem fmkSplitPrefix_unary_contiguous {M : ℕ} (srcBase M_prev N : ℕ) (sel : Wire M)
    (hsel : sel.val < srcBase) (hNM : N ≤ M_prev) (hdst : (srcBase + M_prev) + N ≤ M)
    (β : BitAssignment M) (hβ : cleanRem M (M - (srcBase + M_prev)) β)
    (g : ZMod 2) (v_lo : ℕ) (hv_lt : v_lo < M_prev) (hv_pruned : (β sel).val = 1 → v_lo < N)
    (h_in : ∀ k : ℕ, (hk : k < M_prev) →
      β ⟨srcBase + k, by omega⟩ = g * (if k = v_lo then 1 else 0)) :
    let K := fmkCtxSplitPrefix srcBase (srcBase + M_prev) N sel hsel (by omega) hdst N le_rfl
    cleanRem M (M - (srcBase + M_prev + N)) (K.fwdBits β) ∧
      (∀ w : Wire M, w.val < srcBase → K.fwdBits β w = β w) ∧ (∀ k : ℕ, (hk : k < M_prev + N) →
        K.fwdBits β ⟨srcBase + k, by omega⟩ =
          g * (if k = v_lo + M_prev * (β sel).val then 1 else 0)) := by
  intro K
  obtain ⟨_, hSpec⟩ := fmkCtxSplitPrefix_scoped srcBase (srcBase + M_prev) N sel
    hsel (by omega) hdst N le_rfl
  obtain ⟨hcl, hSrc, hDst, hOut⟩ := hSpec β (by simpa [Nat.sub_self] using hβ)
  refine ⟨by simpa [Nat.add_assoc] using hcl, fun w hw ↦ hOut w (by omega) (by omega),
    fun k hk ↦ ?_⟩
  by_cases hkN : k < N
  · rw [hSrc k (by omega) hkN, h_in k (by omega)]
    rcases fmkBit_cases (β sel) with hs0 | hs1
    · simp [hs0, ZMod.val_zero]
    · simp only [hs1, ZMod.val_one, mul_one, CharTwo.add_self_eq_zero,
        ite_eq_right (by omega : ¬(k = v_lo + M_prev)), mul_zero]
  · by_cases hkM : k < M_prev
    · rw [hOut ⟨srcBase + k, by omega⟩ (by dsimp; omega) (by dsimp; omega), h_in k hkM]
      rcases fmkBit_cases (β sel) with hs0 | hs1
      · simp [hs0, ZMod.val_zero]
      · have hvN := hv_pruned (by rw [hs1]; rfl)
        simp only [hs1, ZMod.val_one, mul_one,
          ite_eq_right (by omega : ¬(k = v_lo)), ite_eq_right (by omega : ¬(k = v_lo + M_prev))]
    · let i := k - M_prev
      have hk_eq : (⟨srcBase + k, by omega⟩ : Wire M) = ⟨(srcBase + M_prev) + i, by omega⟩ :=
        Fin.ext (by dsimp [i]; omega)
      rw [hk_eq, hDst i (by omega) (by omega), h_in i (by omega)]
      rcases fmkBit_cases (β sel) with hs0 | hs1
      · simp only [hs0, ZMod.val_zero, mul_zero, add_zero,
          ite_eq_right (by omega : ¬(k = v_lo)), mul_zero]
      · simp only [hs1, ZMod.val_one, mul_one]
        by_cases hiv : i = v_lo
        · simp [hiv, show k = v_lo + M_prev by omega]
        · simp [hiv, show ¬(k = v_lo + M_prev) by omega]
def fmkIsMutBlock (M rem : ℕ) (mutW : Wire M → Prop) (p : TempPhaseProg M) : Prop :=
    ValidCleanRem M rem p ∧ (∀ β, cleanRem M rem β → p.evalSign β = 0) ∧
    (∀ β, cleanRem M rem β → cleanRem M rem (p.evalBits β)) ∧
    (∀ β, cleanRem M rem β → ∀ w, ¬ mutW w → p.evalBits β w = β w)
theorem fmkIsMutBlock_seq {M rem : ℕ} {mutW : Wire M → Prop} {p₁ p₂ : TempPhaseProg M}
    (hrem : rem ≤ M) (h₁ : fmkIsMutBlock M rem mutW p₁) (h₂ : fmkIsMutBlock M rem mutW p₂) :
    fmkIsMutBlock M rem mutW (.seq p₁ p₂) := ⟨⟨rem, hrem, h₁.1, h₂.1, h₁.2.2.1⟩, fun β hβ ↦ by
      dsimp only [TempPhaseProg.evalSign]
      rw [h₁.2.1 β hβ, h₂.2.1 _ (h₁.2.2.1 β hβ), zero_add], fun β hβ ↦ h₂.2.2.1 _ (h₁.2.2.1 β hβ),
    fun β hβ w hw ↦ (h₂.2.2.2 _ (h₁.2.2.1 β hβ) w hw).trans (h₁.2.2.2 β hβ w hw)⟩
theorem fmkIsMutBlock_mono_mut {M rem : ℕ} {m₁ m₂ : Wire M → Prop} {p : TempPhaseProg M}
    (h : ∀ w, m₁ w → m₂ w) (hp : fmkIsMutBlock M rem m₁ p) : fmkIsMutBlock M rem m₂ p :=
  ⟨hp.1, hp.2.1, hp.2.2.1, fun β hβ w hw ↦ hp.2.2.2 β hβ w (fun h1 ↦ hw (h w h1))⟩
theorem fmkNotRange {α β : Type*} {y : β} {f : α → β} (h : ∀ x, y ≠ f x) : ¬ ∃ x, y = f x :=
  fun ⟨x, hx⟩ ↦ h x hx
theorem fmkCtxPlug_isMutBlock {M cur next : ℕ} [NeZero M] (hle : cur ≤ next) (hnext : next ≤ M)
    (mutW : Wire M → Prop) (hmut_lt : ∀ w, mutW w → w.val < cur)
    (K : TempCtx M) (hdK : K.DisjointFrom mutW)
    (hsK : K.SupportsBelowCtx next) (hlK : fmkTempCtxLiftEx cur next K)
    (body : TempPhaseProg M) (hBody : fmkIsMutBlock M (M - next) mutW body) :
    fmkIsMutBlock M (M - cur) mutW (K.plug body) ∧
      (∀ β, cleanRem M (M - cur) β → cleanRem M (M - next) (K.fwdBits β) ∧
        ∀ w, mutW w → (K.plug body).evalBits β w = body.evalBits (K.fwdBits β) w) := by
  let _ := Classical.decPred mutW
  obtain ⟨hv, _, hs, hb⟩ := fmkGraft_mutating_clean mutW K hdK hsK (by omega)
    K.fwdBits (fmkTempCtxLiftEx_probe hlK) body hBody.1 hBody.2.2.2
  have hclK : ∀ β, cleanRem M (M - cur) β → cleanRem M (M - next) (K.fwdBits β) :=
    fun _ hβ ↦ Slot3MicroEngineAux.TempCtx.cleanRem_of_supports cur next hle hsK hβ
  have hNon : ∀ β, cleanRem M (M - cur) β → ∀ w, ¬ mutW w → (K.plug body).evalBits β w = β w :=
    fun β hβ w hw ↦ (hb β hβ w).trans (ite_eq_right hw)
  refine ⟨⟨hv, fun β hβ ↦ (hs β hβ).trans (hBody.2.1 _ (hclK β hβ)), fun β hβ w hw ↦ ?_, hNon⟩,
    fun β hβ ↦ ⟨hclK β hβ, fun w hw ↦ (hb β hβ w).trans (ite_eq_left hw)⟩⟩
  rw [hNon β hβ w (fun hm ↦ absurd (hmut_lt w hm) (by omega))]
  exact hβ w hw
theorem fmkCliffPlug_isMutBlock {M cur : ℕ} [NeZero M] (hcur : cur ≤ M)
    (mutW : Wire M → Prop) (hmut_lt : ∀ w, mutW w → w.val < cur)
    (c : CliffProg M) (hdc : CliffDisjoint mutW c) (hsc : c.SupportsBelow cur)
    (body : TempPhaseProg M) (hBody : fmkIsMutBlock M (M - cur) mutW body) :
    fmkIsMutBlock M (M - cur) mutW ((ctxCliffAlloc c).plug body) ∧
      (∀ β, cleanRem M (M - cur) β → cleanRem M (M - cur) (c.eval β) ∧
        ∀ w, mutW w → ((ctxCliffAlloc c).plug body).evalBits β w = body.evalBits (c.eval β) w) :=
  fmkCtxPlug_isMutBlock le_rfl hcur mutW hmut_lt (ctxCliffAlloc c)
    (ctxCliffAlloc_disjoint hdc) (ctxCliffAlloc_supports hsc)
    (fmkTempCtxLiftEx_cliff hcur c hsc) body hBody
theorem fmkTempBitPlug_isMutBlock {M cur : ℕ} [NeZero M] (hcur : cur + 1 ≤ M)
    (mutW : Wire M → Prop) (hmut_lt : ∀ w, mutW w → w.val < cur)
    (c₁ c₂ : Wire M) (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ ⟨cur, hcur⟩) (h2a : c₂ ≠ ⟨cur, hcur⟩)
    (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) (hnc1 : ¬ mutW c₁) (hnc2 : ¬ mutW c₂)
    (body : TempPhaseProg M) (hBody : fmkIsMutBlock M (M - (cur + 1)) mutW body) :
    let K := ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 h1a h2a
    fmkIsMutBlock M (M - cur) mutW (K.plug body) ∧ (∀ β, cleanRem M (M - cur) β →
        let δ := Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂)
        cleanRem M (M - (cur + 1)) δ ∧
        ∀ w, mutW w → (K.plug body).evalBits β w = body.evalBits δ w) := by
  dsimp only
  let K := ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 h1a h2a
  have hK_eq : K = ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2) := rfl
  have hnout : ¬ mutW ⟨cur, hcur⟩ := fun hm ↦ absurd (hmut_lt _ hm) (by dsimp; omega)
  obtain ⟨hMut, hEv⟩ := fmkCtxPlug_isMutBlock (Nat.le_succ cur) hcur mutW hmut_lt
    K ⟨hnc1, hnc2, hnout, trivial⟩ ⟨Nat.lt_succ_self cur, trivial⟩
    (hK_eq ▸ fmkTempCtxLiftEx_tempBit hcur c₁ c₂ h12 hc1 hc2) body hBody
  refine ⟨hMut, fun β hβ ↦ ?_⟩
  have hfwd : K.fwdBits β = Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂) := by
    dsimp only [K, ctxTempBit, TempCtx.fwdBits]
    rw [hβ ⟨cur, hcur⟩ (by dsimp; omega), zero_add]
  obtain ⟨hcl, hev⟩ := hEv β hβ
  exact ⟨hfwd ▸ hcl, fun w hw ↦ hfwd ▸ hev w hw⟩
def fmkInPlaceAddModCarry {M : ℕ} : (W cur : ℕ) → (hcur : cur + W ≤ M) →
    (b acc : Fin (W + 1) → Wire M) → (cin : Wire M) →
    (hab : ∀ j, acc j ≠ b j) → (hac : ∀ j, acc j ≠ cin) → (hbc : ∀ j, b j ≠ cin) →
    (hb : ∀ j, (b j).val < cur) → (ha : ∀ j, (acc j).val < cur) → (hc : cin.val < cur) →
    TempPhaseProg M
  | 0, _, _, b, acc, cin, hab, hac, _, _, _, _ =>
      .cliff (.seq (.cnot (b 0) (acc 0) (hab 0).symm) (.cnot cin (acc 0) (hac 0).symm))
  | W + 1, cur, hcur, b, acc, cin, hab, hac, hbc, hb, ha, hc =>
      let cout : Wire M := ⟨cur, by omega⟩
      let cPre : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cPost : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot (b 0) (acc 0) (hab 0).symm)
      let innerRec := fmkInPlaceAddModCarry W (cur + 1) (by omega) (fun j ↦ b j.succ)
        (fun j ↦ acc j.succ) cout (fun j ↦ hab j.succ)
        (fun j ↦ wire_ne_of_lt (ha j.succ)) (fun j ↦ wire_ne_of_lt (hb j.succ))
        (fun j ↦ Nat.lt_succ_of_lt (hb j.succ)) (fun j ↦ Nat.lt_succ_of_lt (ha j.succ))
        (Nat.lt_succ_self cur)
      let inner := withCliffAlloc (.cnot cin cout (wire_ne_of_lt hc)) innerRec
      .seq (.cliff cPre) (.seq (.tempAnd (b 0) (acc 0) cout (hab 0).symm
        (wire_ne_of_lt (hb 0)) (wire_ne_of_lt (ha 0)) inner) (.cliff cPost))
theorem fmkInPlaceAddModCarry_countTempAnd {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (b acc : Fin (W + 1) → Wire M) (cin : Wire M)
      (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hc : cin.val < cur),
      (fmkInPlaceAddModCarry W cur hcur b acc cin hab hac hbc hb ha hc).countTempAnd = W
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, b, acc, cin, hab, hac, hbc, hb, ha, hc => by
      dsimp only [fmkInPlaceAddModCarry]
      simp only [TempPhaseProg.countTempAnd, withCliffAlloc_countTempAnd,
        fmkInPlaceAddModCarry_countTempAnd W (cur + 1)]
      omega
theorem fmkInPlaceAddModCarry_spec {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (b acc : Fin (W + 1) → Wire M) (cin : Wire M) (hab_disj : ∀ i j, acc i ≠ b j)
      (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (_ : Function.Injective b) (_ : Function.Injective acc)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hc : cin.val < cur),
      let p := fmkInPlaceAddModCarry W cur hcur b acc cin (fun j ↦ hab_disj j j) hac hbc hb ha hc
      ValidCleanRem M (M - cur) p ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β → p.evalSign β = 0) ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β → cleanRem M (M - cur) (p.evalBits β) ∧
          (∀ w : Wire M, (∀ j, w ≠ acc j) → p.evalBits β w = β w) ∧
          bitsVal (fun j ↦ p.evalBits β (acc j)) =
            (bitsVal (fun j ↦ β (acc j)) + bitsVal (fun j ↦ β (b j)) + (β cin).val) % 2 ^ (W + 1))
  | 0, cur, _, b, acc, cin, hab_disj, hac, _, _, _, _, ha, _ => by
      dsimp only [fmkInPlaceAddModCarry]
      have hNon (β : BitAssignment M) (w : Wire M) (hw : ∀ j : Fin 1, w ≠ acc j) :
          (TempPhaseProg.cliff (.seq (.cnot (b 0) (acc 0) (hab_disj 0 0).symm)
            (.cnot cin (acc 0) (hac 0).symm))).evalBits β w = β w := by
        simp [TempPhaseProg.evalBits, CliffProg.eval, Function.update_of_ne (hw 0)]
      refine ⟨trivial, fun _ _ ↦ rfl, fun β hβ ↦
        ⟨fun w hw ↦ (hNon β w fun j ↦ wire_ne_of_gt (by have := ha j; omega)).trans (hβ w hw),
          hNon β, ?_⟩⟩
      rw [fmkBitsVal_succ_split, fmkBitsVal_succ_split (fun j ↦ β (acc j)),
        fmkBitsVal_succ_split (fun j ↦ β (b j))]
      simp only [bitsVal, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero,
        TempPhaseProg.evalBits, CliffProg.eval, Function.update_self,
        Function.update_of_ne (hac 0).symm]
      rcases fmkBit_cases (β (acc 0)) with h1 | h1 <;>
        rcases fmkBit_cases (β (b 0)) with h2 | h2 <;>
        rcases fmkBit_cases (β cin) with h3 | h3 <;>
        rw [h1, h2, h3] <;> decide
  | W + 1, cur, hcur, b, acc, cin, hab_disj, hac, hbc, hb_inj, ha_inj, hb, ha, hc => by
      have : NeZero M := ⟨cin.pos.ne'⟩
      dsimp only [fmkInPlaceAddModCarry]
      let cout : Wire M := ⟨cur, by omega⟩
      have hac' (j : Fin (W + 1)) : acc j.succ ≠ cout := wire_ne_of_lt (ha j.succ)
      have hbc' (j : Fin (W + 1)) : b j.succ ≠ cout := wire_ne_of_lt (hb j.succ)
      have hb' (j : Fin (W + 1)) : (b j.succ).val < cur + 1 := Nat.lt_succ_of_lt (hb j.succ)
      have ha' (j : Fin (W + 1)) : (acc j.succ).val < cur + 1 := Nat.lt_succ_of_lt (ha j.succ)
      let cPre : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cPost : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot (b 0) (acc 0) (hab_disj 0 0).symm)
      let cCarry : CliffProg M := .cnot cin cout (wire_ne_of_lt hc)
      let mutSucc : Wire M → Prop := fun w ↦ ∃ j : Fin (W + 1), w = acc j.succ
      let innerRec := fmkInPlaceAddModCarry W (cur + 1) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) cout (fun j ↦ hab_disj j.succ j.succ)
        hac' hbc' hb' ha' (Nat.lt_succ_self cur)
      obtain ⟨hvRec, hsRec, hRec⟩ := fmkInPlaceAddModCarry_spec W (cur + 1) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) cout (fun i j ↦ hab_disj i.succ j.succ)
        hac' hbc' (hb_inj.comp (Fin.succ_injective _)) (ha_inj.comp (Fin.succ_injective _))
        hb' ha' (Nat.lt_succ_self cur)
      obtain ⟨hMutIn, hEvIn⟩ := fmkCliffPlug_isMutBlock (cur := cur + 1) (by omega)
        mutSucc (by rintro _ ⟨j, rfl⟩; exact ha' j) cCarry
        ⟨fun ⟨j, hj⟩ ↦ hac j.succ hj.symm, fun ⟨j, hj⟩ ↦ hac' j hj.symm⟩
        ⟨Nat.lt_succ_of_lt hc, Nat.lt_succ_self cur⟩ innerRec
        ⟨hvRec, hsRec, fun γ hγ ↦ (hRec γ hγ).1,
          fun γ hγ w hw ↦ (hRec γ hγ).2.1 w fun j hj ↦ hw ⟨j, hj⟩⟩
      let mid := (ctxTempBit (b 0) (acc 0) cout (hab_disj 0 0).symm
        (wire_ne_of_lt (hb 0)) (wire_ne_of_lt (ha 0))).plug
          ((ctxCliffAlloc cCarry).plug innerRec)
      obtain ⟨hMutMid, hEvMid⟩ := fmkTempBitPlug_isMutBlock (cur := cur) (by omega)
        mutSucc (by rintro _ ⟨j, rfl⟩; exact ha j.succ) (b 0) (acc 0) (hab_disj 0 0).symm
        (wire_ne_of_lt (hb 0)) (wire_ne_of_lt (ha 0)) (hb 0) (ha 0)
        (fun ⟨j, hj⟩ ↦ hab_disj j.succ 0 hj.symm)
        (fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (ha_inj hj.symm))
        ((ctxCliffAlloc cCarry).plug innerRec) hMutIn
      have hcPre_cl (β : BitAssignment M) (hβ : cleanRem M (M - cur) β) :
          cleanRem M (M - cur) (cPre.eval β) := fun w hw ↦
        (cPre.eval_outside ⟨⟨hc, hb 0⟩, ⟨hc, ha 0⟩⟩ β w (by omega)).trans (hβ w hw)
      refine ⟨⟨M - cur, by omega, trivial,
          ⟨M - cur, by omega, hMutMid.1, trivial, hMutMid.2.2.1⟩, hcPre_cl⟩, fun β hβ ↦ by
          change 0 + (mid.evalSign (cPre.eval β) + 0) = 0
          rw [hMutMid.2.1 _ (hcPre_cl β hβ)]
          rfl, fun β hβ ↦ ?_⟩
      let β₁ := cPre.eval β
      let β₄ := mid.evalBits β₁
      let β_out := cPost.eval β₄
      have hβ₁_b0 : β₁ (b 0) = β (b 0) + β cin := by
        simp [β₁, cPre, CliffProg.eval, Function.update_of_ne (hab_disj 0 0).symm]
      have hβ₁_a0 : β₁ (acc 0) = β (acc 0) + β cin := by
        simp [β₁, cPre, CliffProg.eval, Function.update_of_ne (hab_disj 0 0),
          Function.update_of_ne (hbc 0).symm]
      have hβ₁_ne (w : Wire M) (h1 : w ≠ b 0) (h2 : w ≠ acc 0) : β₁ w = β w := by
        simp [β₁, cPre, CliffProg.eval, Function.update_of_ne h1, Function.update_of_ne h2]
      have hβ₄_non (w : Wire M) (hw : ¬ mutSucc w) : β₄ w = β₁ w :=
        hMutMid.2.2.2 β₁ (hcPre_cl β hβ) w hw
      have hβ₄_cin : β₄ cin = β cin := (hβ₄_non cin fun ⟨j, hj⟩ ↦ hac j.succ hj.symm).trans
          (hβ₁_ne cin (hbc 0).symm (hac 0).symm)
      have hβ₄_b0 : β₄ (b 0) = β (b 0) + β cin :=
        (hβ₄_non (b 0) fun ⟨j, hj⟩ ↦ hab_disj j.succ 0 hj.symm).trans hβ₁_b0
      have hβ₄_a0 : β₄ (acc 0) = β (acc 0) + β cin :=
        (hβ₄_non (acc 0) fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (ha_inj hj.symm)).trans hβ₁_a0
      have hNonOut (w : Wire M) (hw : ∀ j : Fin (W + 2), w ≠ acc j) : β_out w = β w := by
        dsimp only [β_out, cPost, CliffProg.eval]
        rw [Function.update_of_ne (hw 0)]
        by_cases hwb0 : w = b 0
        · rw [hwb0, Function.update_self, hβ₄_b0, hβ₄_cin, fmkZmod2_add_self_cancel]
        · rw [Function.update_of_ne hwb0, hβ₄_non w fun ⟨j, hj⟩ ↦ hw j.succ hj,
            hβ₁_ne w hwb0 (hw 0)]
      refine ⟨fun w hw ↦ (hNonOut w fun j ↦ wire_ne_of_gt
          (show (acc j).val < w.val by have := ha j; omega)).trans (hβ w hw), hNonOut, ?_⟩
      obtain ⟨hcl₂, hevMid⟩ := hEvMid β₁ (hcPre_cl β hβ)
      obtain ⟨hcl₃, hevIn⟩ := hEvIn _ hcl₂
      let β₃ := cCarry.eval (Function.update β₁ cout (β₁ (b 0) * β₁ (acc 0)))
      have hβ₃_lt (w : Wire M) (hlt : w.val < cur) (h1 : w ≠ b 0) (h2 : w ≠ acc 0) :
          β₃ w = β w := by
        simp [β₃, cCarry, CliffProg.eval,
          Function.update_of_ne (wire_ne_of_lt hlt : w ≠ cout), hβ₁_ne w h1 h2]
      change bitsVal (fun j ↦ β_out (acc j)) = _
      rw [fmkBitsVal_succ_split (fun j ↦ β_out (acc j)),
        show β_out (acc 0) = β (acc 0) + β (b 0) + β cin by
          simp only [β_out, cPost, CliffProg.eval, Function.update_self,
            Function.update_of_ne (hab_disj 0 0), hβ₄_a0, hβ₄_b0, hβ₄_cin,
            fmkZmod2_add_self_cancel]
          ring, show (fun j : Fin (W + 1) ↦ β_out (acc j.succ)) =
            fun j ↦ innerRec.evalBits β₃ (acc j.succ) from funext fun j ↦ by
          simp only [β_out, cPost, CliffProg.eval,
            Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (ha_inj h)),
            Function.update_of_ne (hab_disj j.succ 0)]
          exact (hevMid (acc j.succ) ⟨j, rfl⟩).trans (hevIn (acc j.succ) ⟨j, rfl⟩),
        (hRec β₃ hcl₃).2.2,
        show (fun j : Fin (W + 1) ↦ β₃ (acc j.succ)) = fun j ↦ β (acc j.succ) from funext
          fun j ↦ hβ₃_lt _ (ha j.succ) (hab_disj j.succ 0)
            (fun h ↦ Fin.succ_ne_zero j (ha_inj h)),
        show (fun j : Fin (W + 1) ↦ β₃ (b j.succ)) = fun j ↦ β (b j.succ) from funext fun j ↦
          hβ₃_lt _ (hb j.succ) (fun h ↦ Fin.succ_ne_zero j (hb_inj h))
            (hab_disj 0 j.succ).symm,
        show β₃ cout = β cin + (β (acc 0) + β cin) * (β (b 0) + β cin) by
          simp only [β₃, cCarry, CliffProg.eval, Function.update_self,
            Function.update_of_ne (wire_ne_of_lt hc : cin ≠ cout),
            hβ₁_ne cin (hbc 0).symm (hac 0).symm, hβ₁_b0, hβ₁_a0]
          ring, fmkBitsVal_succ_split (fun j ↦ β (acc j)), fmkBitsVal_succ_split (fun j ↦ β (b j)),
        ← fmkAdd_two_mul_mod (W + 1) _ _ (ZMod.val_lt _)]
      refine congrArg (· % 2 ^ (W + 2)) ?_
      have hfa := fullAdd_val_eq (β (acc 0)) (β (b 0)) (β cin)
      omega
def fmkU16W (i : Fin 16) : Wire 437 := ⟨91 + i.val, by omega⟩
def fmkWalk10W : Wire 437 := ⟨352, by decide⟩
def fmkBank42W (j : Fin 42) : Wire 437 := ⟨353 + j.val, by omega⟩
def fmkCat42W (j : Fin 42) : Wire 437 := ⟨107 + j.val, by omega⟩
def fmkBParW : Wire 437 := ⟨90, by decide⟩
def fmkAccW : Wire 437 := ⟨149, by decide⟩
theorem fmkBank42W_inj : Function.Injective fmkBank42W := fun a b h ↦ by
  have hv := congrArg Fin.val h
  dsimp [fmkBank42W] at hv
  exact Fin.ext (by omega)
theorem fmkCat42W_inj : Function.Injective fmkCat42W := fun a b h ↦ by
  have hv := congrArg Fin.val h
  dsimp [fmkCat42W] at hv
  exact Fin.ext (by omega)
def fmkBitZ (b : Bool) : ZMod 2 := if b then 1 else 0
theorem fmkBitZ_xor (a b : Bool) : fmkBitZ (xor a b) = fmkBitZ a + fmkBitZ b := by
  cases a <;> cases b <;> decide
theorem fmkIte_mul_bitZ (b : Bool) (x : ZMod 2) : (if b then x else 0) = x * fmkBitZ b := by
  cases b <;> simp [fmkBitZ]
namespace Micro21
section ConfigMicro21
set_option backward.isDefEq.respectTransparency true
theorem TempCtx.supportsBelowCtx_mono {M b₁ b₂ : ℕ} (hle : b₁ ≤ b₂) {K : TempCtx M} :
    K.SupportsBelowCtx b₁ → K.SupportsBelowCtx b₂ :=
  Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono hle
theorem TempCtx.append_countTempAnd {M : ℕ} (F G : TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd :=
  Slot3MicroEngineAux.TempCtx.append_countTempAnd F G
theorem TempCtx.append_fwdBits {M : ℕ} (F G : TempCtx M) (β : BitAssignment M) :
    (F.append G).fwdBits β = G.fwdBits (F.fwdBits β) :=
  Slot3MicroEngineAux.TempCtx.append_fwdBits F G β
theorem TempCtx.scopedBlock_fwdBits {M rem : ℕ} (K : TempCtx M)
    (hEx : ∀ q : Wire M, ∃ sQ, ScopedBlock M rem sQ (.z q) (K.plug (.z q))) (q : Wire M) :
    ScopedBlock M rem K.fwdBits (.z q) (K.plug (.z q)) :=
  Slot3MicroEngineAux.TempCtx.scopedBlock_fwdBits K hEx q
theorem TempCtx.fwdBits_eq_of_block {M rem : ℕ} (K : TempCtx M) (u : Wire M)
    {sU : BitAssignment M → BitAssignment M}
    (hBlk : ScopedBlock M rem sU (.z u) (K.plug (.z u))) (β : BitAssignment M)
    (hβ : cleanRem M rem β) : K.fwdBits β u = sU β u :=
  Slot3MicroEngineAux.TempCtx.fwdBits_eq_of_block K u hBlk β hβ
def TempCtxLiftEx {M : ℕ} (cur next : ℕ) (K : TempCtx M) : Prop :=
  ∀ {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M},
    ScopedBlock M (M - next) sBody leaf body →
    ∃ sOut, ScopedBlock M (M - cur) sOut leaf (K.plug body)
theorem TempCtxLiftEx.probe {M cur next : ℕ} {K : TempCtx M}
    (hK : TempCtxLiftEx cur next K) (q : Wire M) :
    ScopedBlock M (M - cur) K.fwdBits (.z q) (K.plug (.z q)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.probe hK q
theorem TempCtxLiftEx.mono {M cur₀ cur₁ next₀ next₁ : ℕ} {K : TempCtx M}
    (hK : TempCtxLiftEx cur₁ next₀ K) (hc : cur₀ ≤ cur₁) (hn : next₀ ≤ next₁) (hM : next₁ ≤ M) :
    TempCtxLiftEx cur₀ next₁ K := Slot3MicroEngineAux.TempCtxLiftEx.mono hK hc hn hM
theorem TempCtxLiftEx.append {M cur mid next : ℕ} {F G : TempCtx M}
    (hF : TempCtxLiftEx cur mid F) (hG : TempCtxLiftEx mid next G) :
    TempCtxLiftEx cur next (F.append G) := Slot3MicroEngineAux.TempCtxLiftEx.append hF hG
theorem TempCtxLiftEx.cliff {M : ℕ} (cur : ℕ) (hcur : cur ≤ M) (c : CliffProg M)
    (hc : c.SupportsBelow cur) : TempCtxLiftEx cur cur (ctxCliffAlloc c) :=
  Slot3MicroEngineAux.TempCtxLiftEx.cliff cur hcur c hc
theorem TempCtxLiftEx.tempBit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) : TempCtxLiftEx cur (cur + 1)
    (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.tempBit cur hcur c₁ c₂ h12 hc1 hc2
end ConfigMicro21
end Micro21
noncomputable section
def fmkIdx0 (b1 p b0 : ℕ) : Fin 256 :=
  ⟨b0 % 2 + 2 * (b1 % 2) + 4 * (p % 27) + 128 * ((p / 27) % 2), by omega⟩
theorem fmkOfEq {α : Sort*} {P : α → Prop} {a b : α} (h : a = b) (hb : P b) : P a :=
  Eq.mpr (congrArg P h) hb
theorem fmkTwoCliffTemp_countTempAnd {M : ℕ} (cD cB0 : CliffProg M) (lsb scrD outW : Wire M)
    (h12 : lsb ≠ scrD) (h1a : lsb ≠ outW) (h2a : scrD ≠ outW) : (((ctxCliffAlloc cD).append
    ((ctxTempBit lsb scrD outW h12 h1a h2a).append (ctxCliffAlloc (cB0.seq
    cD.inv))))).countTempAnd = 1 := by
  rw [fmkAppend_countTempAnd, fmkAppend_countTempAnd]
  rfl
theorem fmkTwoCliffTemp_fwdBits_step {M : ℕ} (cD cB0 : CliffProg M) (lsb scrD outW : Wire M)
    (h12 : lsb ≠ scrD) (h1a : lsb ≠ outW) (h2a : scrD ≠ outW) (γ : BitAssignment M)
    {P : BitAssignment M → Prop} (h : ∀ γ1 γ2 γ3 γ4 : BitAssignment M, cD.eval γ = γ1 →
    Function.update γ1 outW (γ1 outW + γ1 lsb * γ1 scrD) = γ2 → cB0.eval γ2 = γ3 → cD.inv.eval
    γ3 = γ4 → P γ4) : P (((ctxCliffAlloc cD).append ((ctxTempBit lsb scrD outW h12 h1a
    h2a).append (ctxCliffAlloc (cB0.seq cD.inv)))).fwdBits γ) := by
  rw [fmkAppend_fwdBits, fmkAppend_fwdBits]
  exact h _ _ _ _ rfl rfl rfl rfl
def fmkFanoutUnary {M : ℕ} (uBase : ℕ) (target : Wire M) (pred : ℕ → Bool) :
    (K : ℕ) → (hK : uBase + K ≤ target.val) → CliffProg M
  | 0, _ => .nil
  | K + 1, hK =>
      .seq (fmkFanoutUnary uBase target pred K (Nat.le_of_succ_le hK))
        (if pred K then
          .cnot ⟨uBase + K, lt_of_lt_of_le (Nat.lt_of_succ_le hK) (le_of_lt target.isLt)⟩
            target (wire_ne_of_lt (Nat.lt_of_succ_le hK))
        else .nil)
theorem fmkFanoutUnary_supportsBelow {M : ℕ} (uBase : ℕ) (target : Wire M)
    (pred : ℕ → Bool) (bound : ℕ) (hb : target.val < bound) :
    ∀ (K : ℕ) (hK : uBase + K ≤ target.val),
      (fmkFanoutUnary uBase target pred K hK).SupportsBelow bound
  | 0, _ => trivial
  | K + 1, hK => by
      dsimp only [fmkFanoutUnary]
      refine ⟨fmkFanoutUnary_supportsBelow uBase target pred bound hb K
        (Nat.le_of_succ_le hK), ?_⟩
      split_ifs
      · exact ⟨by dsimp; omega, hb⟩
      · trivial
theorem fmkFanoutUnary_eval {M : ℕ} (uBase : ℕ) (target : Wire M) (pred : ℕ → Bool) :
    ∀ (K : ℕ) (hK : uBase + K ≤ target.val) (β : BitAssignment M),
      (fmkFanoutUnary uBase target pred K hK).eval β = Function.update β target
          (β target + ∑ k : Fin K, if pred k.val then β ⟨uBase + k.val, by
            have := target.isLt; omega⟩ else 0)
  | 0, _, β => by simp [fmkFanoutUnary, CliffProg.eval]
  | K + 1, hK, β => by
      have ihβ := fmkFanoutUnary_eval uBase target pred K (Nat.le_of_succ_le hK) β
      dsimp only [fmkFanoutUnary, CliffProg.eval]
      split_ifs with hp
      · simp only [CliffProg.eval, ihβ,
          Function.update_of_ne (wire_ne_of_lt (show (⟨uBase + K, _⟩ : Wire M).val <
            target.val by dsimp; omega)), Function.update_idem, Function.update_self,
          Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, hp, ↓reduceIte, add_assoc]
      · simp only [CliffProg.eval, ihβ, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
          Bool.eq_false_iff.mpr hp, Bool.false_eq_true, ↓reduceIte, add_zero]
def fmkXorPredD (tTab : Fin 256 → ℕ) (j : Fin 42) (b1 : ℕ) (p : ℕ) : Bool :=
  xor ((tTab (fmkIdx0 b1 p 0)).testBit j.val) ((tTab (fmkIdx0 b1 p 1)).testBit j.val)
def fmkXorPredB (tTab : Fin 256 → ℕ) (j : Fin 42) (b1 : ℕ) (p : ℕ) : Bool :=
  (tTab (fmkIdx0 b1 p 0)).testBit j.val
theorem fmkDeltaBitsAlgebra (pNewB pOldB : Fin 8 → ZMod 2) (u9 : Fin 9 → ZMod 2)
    (hsum : bitsVal u9 = bitsVal (fun b : Fin 8 ↦ if b.val = 7 then pNewB b + 1 else pNewB b) +
      bitsVal (fun b : Fin 8 ↦ if b.val < 7 then pOldB b + 1 else pOldB b)) :
    let pNew0 : Fin 256 := ⟨bitsVal pNewB, bitsVal_lt_two_pow _⟩
    let pOld0 : Fin 256 := ⟨bitsVal pOldB, bitsVal_lt_two_pow _⟩
    twosComp8Int pNew0 - twosComp8Int pOld0 =
      ((u9 0).val : ℤ) + ∑ s : Fin 8, (2 ^ s.val : ℤ) * (2 * ((u9 s.succ).val : ℤ) - 1) := by
  intro pNew0 pOld0
  have hsum_rhs : ((u9 0).val : ℤ) +
      ∑ s : Fin 8, (2 ^ s.val : ℤ) * (2 * ((u9 s.succ).val : ℤ) - 1) = (bitsVal u9 : ℤ) - 255 := by
    rw [fmkBitsVal_succ_split u9]
    push_cast [bitsVal]
    rw [show (∑ s : Fin 8, (2 ^ s.val : ℤ) * (2 * ((u9 s.succ).val : ℤ) - 1)) =
        2 * (∑ s : Fin 8, ((u9 s.succ).val : ℤ) * (2 ^ s.val : ℤ)) -
          ∑ s : Fin 8, (2 ^ s.val : ℤ) by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring,
      show (∑ s : Fin 8, (2 ^ s.val : ℤ)) = 255 by decide]
    ring
  have hn2 := fmkBitsVal_castSucc_split
    (fun b : Fin 8 ↦ if b.val = 7 then pNewB b + 1 else pNewB b)
  simp only [Fin.val_castSucc, show ∀ j : Fin 7, j.val ≠ 7 from fun j ↦ j.isLt.ne,
    ↓reduceIte, Fin.val_last] at hn2
  have ho2 := fmkBitsVal_castSucc_split
    (fun b : Fin 8 ↦ if b.val < 7 then pOldB b + 1 else pOldB b)
  simp only [Fin.val_castSucc, Fin.is_lt, ↓reduceIte, Fin.val_last, lt_self_iff_false] at ho2
  have ho_flip := fmkBitsVal_flip_all 7 (fun j : Fin 7 ↦ pOldB j.castSucc)
  have hnl_lt := bitsVal_lt_two_pow (fun j : Fin 7 ↦ pNewB j.castSucc)
  have hol_lt := bitsVal_lt_two_pow (fun j : Fin 7 ↦ pOldB j.castSucc)
  have hn_msb : (pNewB (Fin.last 7) + 1).val + (pNewB (Fin.last 7)).val = 1 := by
    rcases fmkBit_cases (pNewB (Fin.last 7)) with h | h <;> rw [h] <;> decide
  have hnm_lt := ZMod.val_lt (pNewB (Fin.last 7))
  have hnmF_lt := ZMod.val_lt (pNewB (Fin.last 7) + 1)
  have ho_msb := ZMod.val_lt (pOldB (Fin.last 7))
  rw [hsum_rhs, hsum, hn2, ho2]
  dsimp only [twosComp8Int, pNew0, pOld0]
  rw [fmkBitsVal_castSucc_split pNewB, fmkBitsVal_castSucc_split pOldB]
  omega
noncomputable def fmkNegCoordTable (cfg : SpecsAux.SpecMirror.Configuration) (w : Fin 3)
    (idx : Fin 256) : ℕ :=
  let l := 2 * (idx.val % 128) + idx.val / 128
  if hl : l < 216 then
    ((-nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) (cfg.nuclei ⟨l,
      hl⟩ w)).emod
      (2 ^ 42 : ℤ)).toNat
  else 0
theorem fmkNegCoordTable_lt (cfg : SpecsAux.SpecMirror.Configuration) (w : Fin 3) (idx : Fin 256) :
    fmkNegCoordTable cfg w idx < 2 ^ 42 := by
  dsimp only [fmkNegCoordTable]
  split_ifs with hl
  · set z := (-nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
      (cfg.nuclei ⟨_, hl⟩ w)).emod (2 ^ 42 : ℤ)
    have hz0 : 0 ≤ z := Int.emod_nonneg _ (by positivity)
    have hz1 : z < (2 ^ 42 : ℤ) := Int.emod_lt_of_pos _ (by positivity)
    omega
  · positivity
def fmkAdd42Bank : TempPhaseProg 437 :=
  let c1W : Wire 437 := ⟨395, by decide⟩
  let bTail : Fin 41 → Wire 437 := fun j ↦ fmkBank42W j.succ
  let aTail : Fin 41 → Wire 437 := fun j ↦ fmkCat42W j.succ
  let K0 : TempCtx 437 := ctxTempBit (fmkBank42W 0) (fmkCat42W 0) c1W
      (wire_ne_of_gt (by dsimp [fmkBank42W, fmkCat42W]; omega))
      (wire_ne_of_lt (by dsimp [fmkBank42W, c1W]; omega))
      (wire_ne_of_lt (by dsimp [fmkCat42W, c1W]; omega))
  let addTail : TempPhaseProg 437 := fmkInPlaceAddModCarry 40 396 (by decide) bTail aTail c1W
      (fun j ↦ wire_ne_of_lt
        (by simp only [bTail, aTail, fmkBank42W, fmkCat42W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by simp only [aTail, fmkCat42W, c1W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by simp only [bTail, fmkBank42W, c1W, Fin.val_succ]; omega))
      (fun j ↦ by simp only [bTail, fmkBank42W, Fin.val_succ]; omega)
      (fun j ↦ by simp only [aTail, fmkCat42W, Fin.val_succ]; omega)
      (by decide)
  .seq (K0.plug addTail)
    (.cliff (.cnot (fmkBank42W 0) (fmkCat42W 0)
      (wire_ne_of_gt (by dsimp [fmkBank42W, fmkCat42W]; omega))))
theorem fmkHalfAdd_val_eq (x y : ZMod 2) : (x + y).val + 2 * (x * y).val = x.val + y.val := by
  rcases fmkBit_cases x with rfl | rfl <;> rcases fmkBit_cases y with rfl | rfl <;> decide
theorem fmkAdd42Bank_spec :
    fmkIsMutBlock 437 (437 - 395) (fun w ↦ 107 ≤ w.val ∧ w.val < 149) fmkAdd42Bank ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - 395) γ →
        ((bitsVal (fun m ↦ fmkAdd42Bank.evalBits γ (fmkCat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (fmkCat42W m)) : ℤ) +
            (bitsVal (fun m ↦ γ (fmkBank42W m)) : ℤ)).emod (2 ^ 42 : ℤ)) := by
  let mutTail : Wire 437 → Prop := fun w ↦ 108 ≤ w.val ∧ w.val < 149
  let c1W : Wire 437 := ⟨395, by decide⟩
  let bTail : Fin 41 → Wire 437 := fun j ↦ fmkBank42W j.succ
  let aTail : Fin 41 → Wire 437 := fun j ↦ fmkCat42W j.succ
  have hb_lt (j : Fin 41) : (bTail j).val < 395 := show 353 + (j.val + 1) < 395 by omega
  have ha_lt (j : Fin 41) : (aTail j).val < 395 := show 107 + (j.val + 1) < 395 by omega
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec 40 396 (by decide) bTail aTail c1W
    (fun i j ↦ wire_ne_of_lt (by
      simp only [aTail, bTail, fmkCat42W, fmkBank42W, Fin.val_succ]
      omega))
    (fun j ↦ wire_ne_of_lt (ha_lt j)) (fun j ↦ wire_ne_of_lt (hb_lt j))
    (fmkBank42W_inj.comp (Fin.succ_injective 41)) (fmkCat42W_inj.comp (Fin.succ_injective 41))
    (fun j ↦ Nat.lt_succ_of_lt (hb_lt j)) (fun j ↦ Nat.lt_succ_of_lt (ha_lt j)) (by decide)
  obtain ⟨hMutP, hEvP⟩ := fmkTempBitPlug_isMutBlock (cur := 395) (by decide) mutTail
    (fun _ hw ↦ by dsimp [mutTail] at hw; omega) (fmkBank42W 0) (fmkCat42W 0)
    (wire_ne_of_gt (by decide)) (wire_ne_of_lt (by decide)) (wire_ne_of_lt (by decide))
    (by decide) (by decide) (by decide) (by decide) _
    ⟨hvAdd, hsAdd, fun δ hδ ↦ (hAdd δ hδ).1, fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦
      hw (by rw [hj]; simp only [mutTail, aTail, fmkCat42W, Fin.val_succ]; omega)⟩
  refine ⟨fmkIsMutBlock_seq (by decide)
      (fmkIsMutBlock_mono_mut (fun _ h ↦ ⟨by omega, h.2⟩) hMutP)
      ⟨trivial, fun _ _ ↦ rfl, fun γ hγ w hw ↦ (Function.update_of_ne
        (wire_ne_of_gt (by dsimp [fmkCat42W]; omega)) _ _).trans (hγ w hw),
        fun _ _ _ hw ↦ Function.update_of_ne (fun h ↦ hw (by rw [h]; decide)) _ _⟩, fun γ hγ ↦ ?_⟩
  obtain ⟨hδ_cl, hevP⟩ := hEvP γ hγ
  let δ := Function.update γ c1W (γ (fmkBank42W 0) * γ (fmkCat42W 0))
  have hTailVal := (hAdd δ hδ_cl).2.2
  rw [show (fun j : Fin 41 ↦ δ (aTail j)) = fun j ↦ γ (fmkCat42W j.succ) from funext fun j ↦
      Function.update_of_ne (wire_ne_of_lt (ha_lt j)) _ _,
    show (fun j : Fin 41 ↦ δ (bTail j)) = fun j ↦ γ (fmkBank42W j.succ) from funext fun j ↦
      Function.update_of_ne (wire_ne_of_lt (hb_lt j)) _ _,
    show δ c1W = γ (fmkBank42W 0) * γ (fmkCat42W 0) from Function.update_self _ _ _] at hTailVal
  rw [fmkBitsVal_succ_split (fun m ↦ fmkAdd42Bank.evalBits γ (fmkCat42W m)),
    show fmkAdd42Bank.evalBits γ (fmkCat42W 0) = γ (fmkCat42W 0) + γ (fmkBank42W 0) by
      dsimp only [fmkAdd42Bank, TempPhaseProg.evalBits, CliffProg.eval]
      rw [Function.update_self]
      exact congrArg₂ (· + ·)
        (hMutP.2.2.2 γ hγ (fmkCat42W 0) (by dsimp [mutTail, fmkCat42W]; omega))
        (hMutP.2.2.2 γ hγ (fmkBank42W 0) (by dsimp [mutTail, fmkBank42W]; omega)),
    show (fun j : Fin 41 ↦ fmkAdd42Bank.evalBits γ (fmkCat42W j.succ)) =
        fun j ↦ (fmkInPlaceAddModCarry 40 396 _ _ _ _ _ _ _ _ _ _).evalBits δ (aTail j) from
      funext fun j ↦ by
        dsimp only [fmkAdd42Bank, TempPhaseProg.evalBits, CliffProg.eval]
        rw [Function.update_of_ne
          (wire_ne_of_gt (by simp only [fmkCat42W, Fin.val_succ]; omega))]
        exact hevP (aTail j) (by simp only [mutTail, aTail, fmkCat42W, Fin.val_succ]; omega),
    hTailVal, fmkBitsVal_succ_split (fun m ↦ γ (fmkCat42W m)),
    fmkBitsVal_succ_split (fun m ↦ γ (fmkBank42W m)),
    mul_comm (γ (fmkBank42W 0)) (γ (fmkCat42W 0))]
  have hha := fmkHalfAdd_val_eq (γ (fmkCat42W 0)) (γ (fmkBank42W 0))
  have hs0 := ZMod.val_lt (γ (fmkCat42W 0) + γ (fmkBank42W 0))
  rw [fmkInt_emod_eq_mod, fmkInt_emod_eq_mod]
  omega
attribute [irreducible] fmkAdd42Bank
def fmkH42NoDummy (u0 : Wire 437) : Fin 42 → Wire 437 :=
  Fin.snoc (fun j : Fin 41 ↦ fmkBank42W j.succ) u0
theorem fmkH42NoDummy_inj (u0 : Wire 437) (hu0 : u0.val < 353) :
    Function.Injective (fmkH42NoDummy u0) := by
  have hne (j : Fin 41) (h : fmkH42NoDummy u0 (Fin.last 41) = fmkH42NoDummy u0 j.castSucc) :
      False := by
    have hv := congrArg Fin.val h
    simp only [fmkH42NoDummy, Fin.snoc_last, Fin.snoc_castSucc, fmkBank42W, Fin.val_succ] at hv
    omega
  refine Fin.lastCases (Fin.lastCases (fun _ ↦ rfl) fun j h ↦ (hne j h).elim)
    (fun i ↦ Fin.lastCases (fun h ↦ (hne i h.symm).elim) fun _ h ↦ ?_)
  simp only [fmkH42NoDummy, Fin.snoc_castSucc] at h
  exact congrArg Fin.castSucc (Fin.succ_injective _ (fmkBank42W_inj h))
theorem fmkH42NoDummy_lt395 (u0 : Wire 437) (hu0 : u0.val < 353) (j : Fin 42) :
    (fmkH42NoDummy u0 j).val < 395 := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [fmkH42NoDummy, Fin.snoc_last]
    omega
  · simp only [fmkH42NoDummy, Fin.snoc_castSucc, fmkBank42W, Fin.val_succ]
    omega
theorem fmkH42NoDummy_not_cat (u0 : Wire 437) (hu_nc : ¬(107 ≤ u0.val ∧ u0.val < 149))
    (j : Fin 42) : ¬(107 ≤ (fmkH42NoDummy u0 j).val ∧ (fmkH42NoDummy u0 j).val < 149) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [fmkH42NoDummy, Fin.snoc_last] using hu_nc
  · simp only [fmkH42NoDummy, Fin.snoc_castSucc, fmkBank42W, Fin.val_succ]
    omega
def fmkStep2b_nodummy (u0 : Wire 437)
    (hu0 : ¬(107 ≤ u0.val ∧ u0.val < 149) ∧ u0.val < 353) : TempPhaseProg 437 :=
  let cin0W : Wire 437 := ⟨395, by decide⟩
  let bankTail : Fin 41 → Wire 437 := fun j ↦ fmkBank42W j.succ
  let cInner : CliffProg 437 :=
    .seq (.cnot u0 cin0W (wire_ne_of_lt (by have := hu0.2; dsimp [cin0W]; omega)))
      (.seq (.x cin0W)
        (.seq (.x u0)
          (fmkFanoutCnot 41 u0 bankTail
            (fun j ↦ wire_ne_of_lt (by have := hu0.2; dsimp [bankTail, fmkBank42W]; omega)))))
  let K2b : TempCtx 437 := (ctxTempBit u0 (fmkBank42W 0) cin0W
      (wire_ne_of_lt (by have := hu0.2; dsimp [fmkBank42W]; omega))
      (wire_ne_of_lt (by have := hu0.2; dsimp [cin0W]; omega))
      (wire_ne_of_lt (by dsimp [fmkBank42W, cin0W]; omega))).append
      (ctxCliffAlloc cInner)
  K2b.plug
    (fmkInPlaceAddModCarry 41 396 (by decide) (fmkH42NoDummy u0) fmkCat42W cin0W
      (fun j h ↦ fmkH42NoDummy_not_cat u0 hu0.1 j (by rw [← h]; dsimp [fmkCat42W]; omega))
      (fun j ↦ wire_ne_of_lt (by dsimp [fmkCat42W, cin0W]; omega))
      (fun j ↦ wire_ne_of_lt (fmkH42NoDummy_lt395 u0 hu0.2 j))
      (fun j ↦ fmkLtTrans (fmkH42NoDummy_lt395 u0 hu0.2 j) (by decide))
      (fun j ↦ by dsimp [fmkCat42W]; omega)
      (by decide))
theorem fmkStep2b_nodummy_spec (u0 : Wire 437)
    (hu0 : ¬(107 ≤ u0.val ∧ u0.val < 149) ∧ u0.val < 353) :
    fmkIsMutBlock 437 (437 - 395) (fun w ↦ 107 ≤ w.val ∧ w.val < 149) (fmkStep2b_nodummy u0 hu0) ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - 395) γ →
        let K_val := bitsVal (fun m ↦ γ (fmkBank42W m))
        ((bitsVal (fun m ↦ (fmkStep2b_nodummy u0 hu0).evalBits γ (fmkCat42W m)) : ℤ)).emod
          (2 ^ 42 : ℤ) = ((bitsVal (fun m ↦ γ (fmkCat42W m)) : ℤ) +
            ((γ u0).val : ℤ) * (K_val : ℤ) - ((K_val / 2 : ℕ) : ℤ)).emod (2 ^ 42 : ℤ)) := by
  obtain ⟨hu_nc, hu_lt⟩ := hu0
  let mutCat : Wire 437 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
  let cin0W : Wire 437 := ⟨395, by decide⟩
  let bankTail : Fin 41 → Wire 437 := fun j ↦ fmkBank42W j.succ
  have hbt_inj : Function.Injective bankTail := fmkBank42W_inj.comp (Fin.succ_injective 41)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec 41 396 (by decide)
    (fmkH42NoDummy u0) fmkCat42W cin0W
    (fun _ j h ↦ fmkH42NoDummy_not_cat u0 hu_nc j (by rw [← h]; dsimp [fmkCat42W]; omega))
    (fun _ ↦ wire_ne_of_lt (by dsimp [fmkCat42W, cin0W]; omega))
    (fun j ↦ wire_ne_of_lt (fmkH42NoDummy_lt395 u0 hu_lt j))
    (fmkH42NoDummy_inj u0 hu_lt) fmkCat42W_inj
    (fun j ↦ fmkLtTrans (fmkH42NoDummy_lt395 u0 hu_lt j) (by decide))
    (fun _ ↦ by dsimp [fmkCat42W]; omega) (by decide)
  let cInner : CliffProg 437 := .seq (.cnot u0 cin0W (wire_ne_of_lt (by dsimp [cin0W]; omega)))
      (.seq (.x cin0W) (.seq (.x u0)
        (fmkFanoutCnot 41 u0 bankTail
          (fun _ ↦ wire_ne_of_lt (by dsimp [bankTail, fmkBank42W]; omega)))))
  let K2b : TempCtx 437 := (ctxTempBit u0 (fmkBank42W 0) cin0W
      (wire_ne_of_lt (by dsimp [fmkBank42W]; omega))
      (wire_ne_of_lt (by dsimp [cin0W]; omega))
      (wire_ne_of_lt (by dsimp [fmkBank42W, cin0W]; omega))).append
      (ctxCliffAlloc cInner)
  have hsInner : cInner.SupportsBelow 396 := ⟨⟨by omega, show cin0W.val < 396 by decide⟩,
      show cin0W.val < 396 by decide, show u0.val < 396 by omega,
      fmkFanoutCnot_supportsBelow 41 u0 bankTail _ (by omega)
        (fun _ ↦ by dsimp [bankTail, fmkBank42W]; omega)⟩
  obtain ⟨hMut2b, hEv2b⟩ := fmkCtxPlug_isMutBlock (cur := 395) (next := 396)
    (by decide) (by decide) mutCat (fun _ hw ↦ by dsimp [mutCat] at hw; omega) K2b
    (TempCtx.disjointFrom_append
      ⟨hu_nc, by dsimp [mutCat, fmkBank42W]; omega, by dsimp [mutCat, cin0W]; omega, trivial⟩
      (ctxCliffAlloc_disjoint ⟨⟨hu_nc, by dsimp [mutCat, cin0W]; omega⟩,
        by dsimp [CliffDisjoint, mutCat, cin0W]; omega, hu_nc,
        fmkFanoutCnot_disjoint 41 u0 bankTail _ hu_nc
          (fun _ ↦ by dsimp [mutCat, bankTail, fmkBank42W]; omega)⟩))
    (TempCtx.supportsBelowCtx_append le_rfl ⟨by decide, trivial⟩
      (ctxCliffAlloc_supports hsInner))
    (fmkTempCtxLiftEx_append
      (fmkTempCtxLiftEx_tempBit (cur := 395) (by decide) u0 (fmkBank42W 0) _ (by omega)
        (by dsimp [fmkBank42W]; omega))
      (fmkTempCtxLiftEx_cliff (cur := 396) (by decide) cInner hsInner))
    _ ⟨hvAdd, hsAdd, fun δ hδ ↦ (hAdd δ hδ).1, fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦
      hw (by rw [hj]; dsimp [mutCat, fmkCat42W]; omega)⟩
  refine ⟨hMut2b, fun γ hγ ↦ ?_⟩
  dsimp only
  obtain ⟨hδ_cl, hev2b⟩ := hEv2b γ hγ
  let δ := K2b.fwdBits γ
  simp_rw [show ∀ m : Fin 42, (fmkStep2b_nodummy u0 ⟨hu_nc, hu_lt⟩).evalBits γ (fmkCat42W m) =
        (fmkInPlaceAddModCarry 41 396 _ _ _ _ _ _ _ _ _ _).evalBits δ (fmkCat42W m) from
    fun m ↦ hev2b (fmkCat42W m) (by dsimp [mutCat, fmkCat42W]; omega)]
  let γt := Function.update γ cin0W (γ cin0W + γ u0 * γ (fmkBank42W 0))
  have hδ_eq : δ = cInner.eval γt := fmkAppend_fwdBits _ _ γ
  have hγt_ne (w : Wire 437) (hw : w ≠ cin0W) : γt w = γ w := Function.update_of_ne hw _ _
  have hδ_cat : (fun m ↦ δ (fmkCat42W m)) = fun m ↦ γ (fmkCat42W m) := funext fun m ↦ by
    have hc : fmkCat42W m ≠ cin0W := wire_ne_of_lt (by dsimp [fmkCat42W, cin0W]; omega)
    rw [hδ_eq]
    dsimp only [cInner, CliffProg.eval]
    rw [fmkFanoutCnot_eval 41 u0 bankTail _ hbt_inj, ite_eq_right (fmkNotRange fun _ ↦
        wire_ne_of_lt (by dsimp [fmkCat42W, bankTail, fmkBank42W]; omega)),
      Function.update_of_ne (fun h ↦ hu_nc (by rw [← h]; dsimp [fmkCat42W]; omega)),
      Function.update_of_ne hc, Function.update_of_ne hc, hγt_ne _ hc]
  have hu_c : u0 ≠ cin0W := wire_ne_of_lt (by dsimp [cin0W]; omega)
  have hδ_cin : δ cin0W = γ u0 * γ (fmkBank42W 0) + γ u0 + 1 := by
    rw [hδ_eq]
    dsimp only [cInner, CliffProg.eval]
    rw [fmkFanoutCnot_eval 41 u0 bankTail _ hbt_inj, ite_eq_right (fmkNotRange fun _ ↦
        wire_ne_of_gt (by dsimp [cin0W, bankTail, fmkBank42W]; omega)),
      Function.update_of_ne hu_c.symm, Function.update_self, Function.update_self, hγt_ne u0 hu_c]
    dsimp only [γt]
    rw [Function.update_self, hγ cin0W (by decide), zero_add]
  let hZero : Fin 42 → ZMod 2 := Fin.snoc (fun j : Fin 41 ↦ γ (fmkBank42W j.succ)) 0
  have hδ_h42 (j : Fin 42) : δ (fmkH42NoDummy u0 j) = hZero j + (γ u0 + 1) := by
    rw [hδ_eq]
    dsimp only [cInner, CliffProg.eval]
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [fmkH42NoDummy, hZero, Fin.snoc_last, zero_add]
      rw [fmkFanoutCnot_eval 41 u0 bankTail _ hbt_inj,
        ite_eq_right (fmkNotRange fun _ ↦ wire_ne_of_lt (by dsimp [bankTail, fmkBank42W]; omega)),
        Function.update_self, Function.update_of_ne hu_c, Function.update_of_ne hu_c,
        hγt_ne u0 hu_c]
    · have hb_c : bankTail i ≠ cin0W :=
        wire_ne_of_lt (by dsimp [bankTail, fmkBank42W, cin0W]; omega)
      have hb_u : bankTail i ≠ u0 := wire_ne_of_gt (by dsimp [bankTail, fmkBank42W]; omega)
      simp only [fmkH42NoDummy, hZero, Fin.snoc_castSucc]
      rw [fmkFanoutCnot_eval 41 u0 bankTail _ hbt_inj, ite_eq_left ⟨i, rfl⟩,
        Function.update_of_ne hb_u, Function.update_of_ne hb_c, Function.update_of_ne hb_c,
        Function.update_self, Function.update_of_ne hu_c, Function.update_of_ne hu_c,
        hγt_ne _ hb_c, hγt_ne u0 hu_c]
  have hhZero_val : bitsVal hZero = bitsVal (fun j : Fin 41 ↦ γ (fmkBank42W j.succ)) := by
    rw [fmkBitsVal_castSucc_split]
    simp only [hZero, Fin.snoc_castSucc, Fin.snoc_last, ZMod.val_zero, mul_zero, add_zero]
  have h2b_val := (hAdd δ hδ_cl).2.2
  set C_in := bitsVal (fun m ↦ γ (fmkCat42W m))
  set H_val := bitsVal (fun j : Fin 41 ↦ γ (fmkBank42W j.succ))
  set K_val := bitsVal (fun m ↦ γ (fmkBank42W m))
  have hK_sp : K_val = (γ (fmkBank42W 0)).val + 2 * H_val := fmkBitsVal_succ_split _
  have hb0_lt : (γ (fmkBank42W 0)).val < 2 := ZMod.val_lt _
  rw [hδ_cat, Nat.add_assoc] at h2b_val
  rw [h2b_val, show K_val / 2 = H_val by omega]
  set B2 := bitsVal (fun j ↦ δ (fmkH42NoDummy u0 j)) + (δ cin0W).val
  have hH_lt : H_val < 2 ^ 42 := by
    rw [← hhZero_val]
    exact bitsVal_lt_two_pow _
  rcases fmkBit_cases (γ u0) with hu_z | hu_o
  · have hB2 : B2 = 2 ^ 42 - H_val := by
      have hfl := fmkBitsVal_flip_all 42 hZero
      rw [hhZero_val] at hfl
      dsimp only [B2]
      rw [show (fun j ↦ δ (fmkH42NoDummy u0 j)) = fun j ↦ hZero j + 1 from
          funext fun j ↦ by rw [hδ_h42 j, hu_z, zero_add],
        hδ_cin, hu_z, zero_mul, add_zero, zero_add, ZMod.val_one]
      omega
    rw [hu_z, ZMod.val_zero]
    change (((C_in + B2) % 2 ^ 42 : ℕ) : ℤ) % (2 ^ 42 : ℤ) =
      ((C_in : ℤ) + (0 : ℤ) * (K_val : ℤ) - (H_val : ℤ)) % (2 ^ 42 : ℤ)
    clear_value C_in H_val K_val B2
    omega
  · have hB2 : B2 = H_val + (γ (fmkBank42W 0)).val := by
      dsimp only [B2]
      rw [show (fun j ↦ δ (fmkH42NoDummy u0 j)) = hZero from
          funext fun j ↦ by rw [hδ_h42 j, hu_o, CharTwo.add_self_eq_zero, add_zero],
        hhZero_val, hδ_cin, hu_o, one_mul, fmkZmod2_add_self_cancel]
    rw [hu_o, ZMod.val_one]
    change (((C_in + B2) % 2 ^ 42 : ℕ) : ℤ) % (2 ^ 42 : ℤ) =
      ((C_in : ℤ) + (1 : ℤ) * (K_val : ℤ) - (H_val : ℤ)) % (2 ^ 42 : ℤ)
    clear_value C_in H_val K_val B2
    omega
attribute [irreducible] fmkStep2b_nodummy
def fmkShiftStep_at (uBit : Wire 437) (curCarry : ℕ) (s : Fin 8) (hu : ¬(107 ≤ uBit.val ∧
    uBit.val < 149) ∧ ¬(353 ≤ uBit.val ∧ uBit.val < 395) ∧ uBit.val < curCarry)
    (hcur : 395 ≤ curCarry ∧ curCarry + (41 - s.val) ≤ 437) : TempPhaseProg 437 :=
  let W := 41 - s.val
  let bankSlice : Fin (W + 1) → Wire 437 := fun j ↦ fmkBank42W ⟨j.val, by dsimp [W] at *; omega⟩
  let catSlice : Fin (W + 1) → Wire 437 :=
    fun j ↦ fmkCat42W ⟨s.val + j.val, by dsimp [W] at *; omega⟩
  let cPrep : CliffProg 437 := .seq (.x uBit) (fmkFanoutCnot (W + 1) uBit bankSlice
      (fun j h ↦ hu.2.1 (by rw [h]; dsimp [bankSlice, fmkBank42W]; omega)))
  (ctxCliffAlloc cPrep).plug
    (fmkInPlaceAddModCarry W curCarry (by dsimp [W]; exact hcur.2) bankSlice catSlice uBit
      (fun j ↦ wire_ne_of_lt (by dsimp [catSlice, bankSlice, fmkCat42W, fmkBank42W]; omega))
      (fun j h ↦ hu.1 (by rw [← h]; dsimp [catSlice, fmkCat42W]; omega))
      (fun j h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, fmkBank42W]; omega))
      (fun j ↦ by dsimp [bankSlice, fmkBank42W]; omega)
      (fun j ↦ by dsimp [catSlice, fmkCat42W]; omega)
      hu.2.2)
theorem fmkShiftStep_at_spec (uBit : Wire 437) (curCarry : ℕ) (s : Fin 8)
    (hu : ¬(107 ≤ uBit.val ∧ uBit.val < 149) ∧
      ¬(353 ≤ uBit.val ∧ uBit.val < 395) ∧ uBit.val < curCarry)
    (hcur : 395 ≤ curCarry ∧ curCarry + (41 - s.val) ≤ 437) :
    fmkIsMutBlock 437 (437 - curCarry) (fun w ↦ 107 ≤ w.val ∧ w.val < 149)
        (fmkShiftStep_at uBit curCarry s hu hcur) ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - curCarry) γ → ((bitsVal (fun m ↦
          (fmkShiftStep_at uBit curCarry s hu hcur).evalBits γ (fmkCat42W m)) : ℤ)).emod
            (2 ^ 42 : ℤ) = ((bitsVal (fun m ↦ γ (fmkCat42W m)) : ℤ) +
            (2 ^ s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) *
              (bitsVal (fun m ↦ γ (fmkBank42W m)) : ℤ)).emod (2 ^ 42 : ℤ)) := by
  let mutCat : Wire 437 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
  let W := 41 - s.val
  let bankSlice : Fin (W + 1) → Wire 437 := fun j ↦ fmkBank42W ⟨j.val, by dsimp [W] at *; omega⟩
  let catSlice : Fin (W + 1) → Wire 437 :=
    fun j ↦ fmkCat42W ⟨s.val + j.val, by dsimp [W] at *; omega⟩
  let cPrep : CliffProg 437 := .seq (.x uBit) (fmkFanoutCnot (W + 1) uBit bankSlice
      (fun j h ↦ hu.2.1 (by rw [h]; dsimp [bankSlice, fmkBank42W]; omega)))
  have hbank_inj : Function.Injective bankSlice := fun _ _ h ↦ by
    have hv := congrArg Fin.val (fmkBank42W_inj h)
    exact Fin.ext hv
  have hcat_inj : Function.Injective catSlice := fun _ _ h ↦ by
    have hv := congrArg Fin.val (fmkCat42W_inj h)
    exact Fin.ext (by dsimp at hv; omega)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec W curCarry
    (by dsimp [W]; exact hcur.2) bankSlice catSlice uBit
    (fun _ _ ↦ wire_ne_of_lt (by dsimp [catSlice, bankSlice, fmkCat42W, fmkBank42W]; omega))
    (fun _ h ↦ hu.1 (by rw [← h]; dsimp [catSlice, fmkCat42W]; omega))
    (fun _ h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, fmkBank42W]; omega))
    hbank_inj hcat_inj
    (fun _ ↦ by dsimp [bankSlice, fmkBank42W]; omega)
    (fun _ ↦ by dsimp [catSlice, fmkCat42W]; omega) hu.2.2
  obtain ⟨hMutOut, hEv⟩ := fmkCliffPlug_isMutBlock (cur := curCarry) (by omega)
    mutCat (fun _ hw ↦ by dsimp [mutCat] at hw; omega) cPrep
    ⟨hu.1, fmkFanoutCnot_disjoint (W + 1) uBit bankSlice _ hu.1
      (fun _ ↦ by dsimp [mutCat, bankSlice, fmkBank42W]; omega)⟩
    ⟨hu.2.2, fmkFanoutCnot_supportsBelow (W + 1) uBit bankSlice _ hu.2.2
      (fun _ ↦ by dsimp [bankSlice, fmkBank42W]; omega)⟩
    _ ⟨hvAdd, hsAdd, fun δ hδ ↦ (hAdd δ hδ).1, fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦
      hw (by rw [hj]; dsimp [mutCat, catSlice, fmkCat42W]; omega)⟩
  refine ⟨hMutOut, fun γ hγ ↦ ?_⟩
  obtain ⟨hγ1_cl, hev⟩ := hEv γ hγ
  let γ1 := cPrep.eval γ
  have hγ1_cat (m : Fin 42) : γ1 (fmkCat42W m) = γ (fmkCat42W m) := by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj, ite_eq_right (fmkNotRange fun _ ↦
        wire_ne_of_lt (by dsimp [fmkCat42W, bankSlice, fmkBank42W]; omega)),
      Function.update_of_ne (fun h ↦ hu.1 (by rw [← h]; dsimp [fmkCat42W]; omega))]
  simp_rw [show ∀ m : Fin 42, (fmkShiftStep_at uBit curCarry s hu hcur).evalBits γ (fmkCat42W m) =
        (fmkInPlaceAddModCarry W curCarry _ _ _ _ _ _ _ _ _ _).evalBits γ1 (fmkCat42W m) from
    fun m ↦ hev (fmkCat42W m) (by dsimp [mutCat, fmkCat42W]; omega)]
  have hsW : s.val + (W + 1) = 42 := by dsimp [W]; omega
  have hslin := fmkBitsVal_slice_linear hsW (fun m : Fin 42 ↦ γ (fmkCat42W m))
    (fun m : Fin 42 ↦
      (fmkInPlaceAddModCarry W curCarry _ _ _ _ _ _ _ _ _ _).evalBits γ1 (fmkCat42W m))
    fun m hm ↦ ((hAdd γ1 hγ1_cl).2.1 (fmkCat42W m) fun j hj ↦ by
      have hv := congrArg Fin.val hj
      dsimp [catSlice, fmkCat42W] at hv; omega).trans (hγ1_cat m)
  rw [show (fun j : Fin (W + 1) ↦ γ (fmkCat42W ⟨s.val + j.val, by omega⟩)) =
      fun j ↦ γ1 (catSlice j) from funext fun _ ↦ (hγ1_cat _).symm,
    (hAdd γ1 hγ1_cl).2.2, Nat.add_assoc] at hslin
  have hγ1_u : γ1 uBit = γ uBit + 1 := by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj, ite_eq_right (fmkNotRange fun _ h ↦
        hu.2.1 (by rw [h]; dsimp [bankSlice, fmkBank42W]; omega)), Function.update_self]
  have hγ1_bs (j : Fin (W + 1)) : γ1 (bankSlice j) = γ (bankSlice j) + (γ uBit + 1) := by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj, ite_eq_left ⟨j, rfl⟩,
      Function.update_self, Function.update_of_ne
        (fun h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, fmkBank42W]; omega))]
  set C_in := bitsVal (fun m ↦ γ (fmkCat42W m))
  set C_out := bitsVal
    (fun m ↦ (fmkInPlaceAddModCarry W curCarry _ _ _ _ _ _ _ _ _ _).evalBits γ1 (fmkCat42W m))
  set C_sl := bitsVal (fun j ↦ γ1 (catSlice j))
  set K_val := bitsVal (fun m ↦ γ (fmkBank42W m))
  set K_lo := bitsVal (fun j : Fin (W + 1) ↦ γ (bankSlice j))
  set B_add := bitsVal (fun j ↦ γ1 (bankSlice j)) + (γ1 uBit).val
  have hp42 : 2 ^ s.val * 2 ^ (W + 1) = 2 ^ 42 := by rw [← pow_add, hsW]
  have hMul42 (X : ℕ) :
      2 ^ 42 * (X / 2 ^ (W + 1)) + 2 ^ s.val * (X % 2 ^ (W + 1)) = 2 ^ s.val * X := by
    rw [← hp42, show 2 ^ s.val * 2 ^ (W + 1) * (X / 2 ^ (W + 1)) + 2 ^ s.val * (X % 2 ^ (W + 1)) =
      2 ^ s.val * (2 ^ (W + 1) * (X / 2 ^ (W + 1)) + X % 2 ^ (W + 1)) by ring, Nat.div_add_mod]
  have hK42 := hMul42 K_val
  rw [← show K_lo = K_val % 2 ^ (W + 1) from
    fmkBitsVal_take_mod (W + 1) (by dsimp [W]; omega) (fun m ↦ γ (fmkBank42W m))] at hK42
  have hS42 := hMul42 (C_sl + B_add)
  rcases fmkBit_cases (γ uBit) with hu0 | hu1
  · have hB_eq : B_add + K_lo = 2 ^ (W + 1) := by
      have hfl := fmkBitsVal_flip_all (W + 1) (fun j ↦ γ (bankSlice j))
      have hk_lt := bitsVal_lt_two_pow (fun j ↦ γ (bankSlice j))
      dsimp only [B_add, K_lo]
      rw [show (fun j ↦ γ1 (bankSlice j)) = fun j ↦ γ (bankSlice j) + 1 from
          funext fun j ↦ by rw [hγ1_bs j, hu0, zero_add], hγ1_u, hu0, zero_add, ZMod.val_one]
      omega
    have hB42 : 2 ^ s.val * B_add + 2 ^ s.val * K_lo = 2 ^ 42 := by
      rw [← mul_add, hB_eq, hp42]
    rw [hu0, ZMod.val_zero]
    refine fmkEmod_eq_of_add_mul (1 + (K_val / 2 ^ (W + 1) : ℤ) -
      ((C_sl + B_add) / 2 ^ (W + 1) : ℤ)) ?_
    zify at hslin hK42 hS42 hB42 ⊢
    linarith
  · have hB42 : 2 ^ s.val * B_add = 2 ^ s.val * K_lo := congrArg (2 ^ s.val * ·) <| by
      dsimp only [B_add, K_lo]
      rw [show (fun j ↦ γ1 (bankSlice j)) = fun j ↦ γ (bankSlice j) from
          funext fun j ↦ by rw [hγ1_bs j, hu1, CharTwo.add_self_eq_zero, add_zero],
        hγ1_u, hu1, CharTwo.add_self_eq_zero, ZMod.val_zero, add_zero]
    rw [hu1, ZMod.val_one]
    refine fmkEmod_eq_of_add_mul
      (-((K_val / 2 ^ (W + 1) : ℤ) + ((C_sl + B_add) / 2 ^ (W + 1) : ℤ))) ?_
    zify at hslin hK42 hS42 hB42 ⊢
    linarith
attribute [irreducible] fmkShiftStep_at
def fmkCtxCarryStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin)
    (ha : a.val < cur) (hb : b.val < cur) (hc : cin.val < cur) : TempCtx M :=
  let out : Wire M := ⟨cur, hcur⟩
  let cPre : CliffProg M := .seq (.cnot cin a hac.symm) (.cnot cin b hbc.symm)
  let cPost : CliffProg M := .seq (.cnot cin b hbc.symm)
    (.seq (.cnot cin a hac.symm) (.cnot cin out (wire_ne_of_lt hc)))
  (ctxCliffAlloc cPre).append ((ctxTempBit a b out hab (wire_ne_of_lt ha)
    (wire_ne_of_lt hb)).append (ctxCliffAlloc cPost))
theorem fmkCtxCarryStep_spec {M : ℕ} {mutW : Wire M → Prop} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin)
    (ha : a.val < cur) (hb : b.val < cur) (hc : cin.val < cur)
    (hna : ¬ mutW a) (hnb : ¬ mutW b) (hnc : ¬ mutW cin) (hnout : ¬ mutW ⟨cur, hcur⟩) :
    let K := fmkCtxCarryStep cur hcur a b cin hab hac hbc ha hb hc
    K.countTempAnd = 1 ∧ K.DisjointFrom mutW ∧ K.SupportsBelowCtx (cur + 1) ∧
      fmkTempCtxLiftEx cur (cur + 1) K ∧ (∀ γ : BitAssignment M, cleanRem M (M - cur) γ →
        K.fwdBits γ = Function.update γ ⟨cur, hcur⟩ (γ cin + (γ a + γ cin) * (γ b + γ cin))) := by
  intro K
  dsimp only [K, fmkCtxCarryStep]
  have hsPre : (CliffProg.seq (.cnot cin a hac.symm)
    (.cnot cin b hbc.symm)).SupportsBelow cur := ⟨⟨hc, ha⟩, hc, hb⟩
  have hsPost : (CliffProg.seq (.cnot cin b hbc.symm)
    (.seq (.cnot cin a hac.symm) (.cnot cin ⟨cur, hcur⟩
      (wire_ne_of_lt hc)))).SupportsBelow (cur + 1) :=
    ⟨⟨Nat.lt_succ_of_lt hc, Nat.lt_succ_of_lt hb⟩, ⟨Nat.lt_succ_of_lt hc, Nat.lt_succ_of_lt ha⟩,
      Nat.lt_succ_of_lt hc, Nat.lt_succ_self cur⟩
  refine ⟨rfl, TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint ⟨⟨hnc, hna⟩, hnc, hnb⟩)
      (TempCtx.disjointFrom_append ⟨hna, hnb, hnout, trivial⟩
        (ctxCliffAlloc_disjoint ⟨⟨hnc, hnb⟩, ⟨hnc, hna⟩, hnc, hnout⟩)),
    TempCtx.supportsBelowCtx_append (Nat.le_succ cur) (ctxCliffAlloc_supports hsPre)
      (TempCtx.supportsBelowCtx_append le_rfl ⟨Nat.lt_succ_self cur, trivial⟩
        (ctxCliffAlloc_supports hsPost)),
    fmkTempCtxLiftEx_append (fmkTempCtxLiftEx_cliff (by omega) _ hsPre)
      (fmkTempCtxLiftEx_append (fmkTempCtxLiftEx_tempBit hcur a b hab ha hb)
        (fmkTempCtxLiftEx_cliff hcur _ hsPost)), fun γ hγ ↦ ?_⟩
  rw [fmkAppend_fwdBits, fmkAppend_fwdBits]
  dsimp only [ctxCliffAlloc, ctxTempBit, TempCtx.fwdBits, CliffProg.eval]
  have hao : a ≠ ⟨cur, hcur⟩ := wire_ne_of_lt ha
  have hbo : b ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hb
  have hco : cin ≠ ⟨cur, hcur⟩ := wire_ne_of_lt hc
  funext u
  by_cases huo : u = ⟨cur, hcur⟩
  · subst huo
    simp only [Function.update_self, Function.update_of_ne hao, Function.update_of_ne hao.symm,
      Function.update_of_ne hbo, Function.update_of_ne hbo.symm, Function.update_of_ne hco,
      Function.update_of_ne hab, Function.update_of_ne hab.symm, Function.update_of_ne hac.symm,
      Function.update_of_ne hbc.symm, hγ ⟨cur, hcur⟩ (by dsimp; omega), zero_add]
    ring
  · by_cases hua : u = a
    · subst hua
      simp [Function.update_of_ne hao, Function.update_of_ne hab,
        Function.update_of_ne hac.symm, Function.update_of_ne hbc.symm, Function.update_of_ne hco]
    · by_cases hub : u = b
      · subst hub
        simp [Function.update_of_ne hbo, Function.update_of_ne hab.symm,
          Function.update_of_ne hac.symm, Function.update_of_ne hbc.symm, Function.update_of_ne hco]
      · simp [Function.update_of_ne huo, Function.update_of_ne hua, Function.update_of_ne hub]
attribute [irreducible] fmkCtxCarryStep
theorem fmkPNew_lt353 (w : Fin 3) (b : Fin 8) : 150 + 8 * w.val + b.val < 353 := by omega
def fmkPOldW (w : Fin 3) (b : Fin 8) : Wire 437 := ⟨8 * w.val + b.val, by omega⟩
def fmkPNewW (w : Fin 3) (b : Fin 8) : Wire 437 :=
  ⟨150 + 8 * w.val + b.val, fmkLtTrans (fmkPNew_lt353 w b) (by decide)⟩
theorem fmkPNew_ne_pOld (w : Fin 3) (b : Fin 8) : fmkPNewW w b ≠ fmkPOldW w b :=
  wire_ne_of_gt (by dsimp [fmkPNewW, fmkPOldW]; omega)
def fmkFlipP (w : Fin 3) : CliffProg 437 :=
  .seq (.x (fmkPNewW w ⟨7, by decide⟩)) (fmkXVec 7 (fun j : Fin 7 ↦ fmkPOldW w j.castSucc))
theorem fmkFlipP_supportsBelow (w : Fin 3) : (fmkFlipP w).SupportsBelow 395 :=
  ⟨by dsimp [CliffProg.SupportsBelow, fmkPNewW]; omega,
    fmkXVec_supportsBelow 7 _ (fun j ↦ by have := j.isLt; dsimp [fmkPOldW]; omega)⟩
def fmkCarryChain (a b : Fin 8 → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | k + 1 =>
      if hk : k < 8 then
        let c := fmkCarryChain a b k
        c + (a ⟨k, hk⟩ + c) * (b ⟨k, hk⟩ + c)
      else 0
def fmkSum9 (a b : Fin 8 → ZMod 2) (i : Fin 9) : ZMod 2 := if hi : i.val < 8 then a
    ⟨i.val, hi⟩ + b ⟨i.val, hi⟩ + fmkCarryChain a b i.val else fmkCarryChain a b 8
theorem fmkBitsVal_sum9 (a b : Fin 8 → ZMod 2) :
    bitsVal (fmkSum9 a b) = bitsVal a + bitsVal b := by
  have hInd : ∀ (m : ℕ) (hm : m ≤ 8),
      (∑ i : Fin m, (fmkSum9 a b ⟨i.val, by omega⟩).val * 2 ^ i.val) +
        (fmkCarryChain a b m).val * 2 ^ m = (∑ i : Fin m, (a ⟨i.val, by omega⟩).val * 2 ^ i.val) +
        (∑ i : Fin m, (b ⟨i.val, by omega⟩).val * 2 ^ i.val) := by
    intro m
    induction m with
    | zero => intro _; simp [fmkCarryChain]
    | succ m ih =>
        intro hm
        have hm_lt : m < 8 := by omega
        have hprev := ih (by omega)
        simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
        have hs_m : fmkSum9 a b ⟨m, by omega⟩ =
            a ⟨m, hm_lt⟩ + b ⟨m, hm_lt⟩ + fmkCarryChain a b m := dite_eq_left hm_lt
        have hc_m : fmkCarryChain a b (m + 1) = fmkCarryChain a b m +
            (a ⟨m, hm_lt⟩ + fmkCarryChain a b m) *
              (b ⟨m, hm_lt⟩ + fmkCarryChain a b m) := dite_eq_left hm_lt
        have hmul := congrArg (· * 2 ^ m)
          (fullAdd_val_eq (a ⟨m, hm_lt⟩) (b ⟨m, hm_lt⟩) (fmkCarryChain a b m))
        rw [hs_m, hc_m, show 2 ^ (m + 1) = 2 * 2 ^ m by ring]
        linarith
  have hcs : ∀ x : Fin 8, fmkSum9 a b x.castSucc = fmkSum9 a b ⟨x.val, by omega⟩ := fun _ ↦ rfl
  rw [bitsVal, Fin.sum_univ_castSucc]
  simpa only [bitsVal, Fin.val_castSucc, Fin.val_last, hcs,
    show fmkSum9 a b (Fin.last 8) = fmkCarryChain a b 8 from rfl] using hInd 8 le_rfl
def fmkInterleavedU9Shift (w : Fin 3) : (rem : ℕ) → (hrem : rem ≤ 7) → TempPhaseProg 437
  | 0, _ =>
      fmkShiftStep_at ⟨402, by decide⟩ 403 ⟨7, by decide⟩
        ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide⟩
  | rem + 1, hrem =>
      let k := 8 - (rem + 1)
      let ckW : Wire 437 := ⟨395 + k - 1, by dsimp [k]; omega⟩
      let pNewK : Wire 437 := fmkPNewW w ⟨k, by dsimp [k]; omega⟩
      let pOldK : Wire 437 := fmkPOldW w ⟨k, by dsimp [k]; omega⟩
      let cXorSum : CliffProg 437 := .seq (.cnot pOldK pNewK (fmkPNew_ne_pOld w _).symm)
          (.cnot ckW pNewK (wire_ne_of_gt (by dsimp [ckW, pNewK, fmkPNewW]; omega)))
      .seq
        ((ctxCliffAlloc cXorSum).plug
          (fmkShiftStep_at pNewK (395 + k) ⟨k - 1, by dsimp [k]; omega⟩
            ⟨by dsimp [pNewK, fmkPNewW]; omega, by dsimp [pNewK, fmkPNewW]; omega,
             by dsimp [pNewK, fmkPNewW, k]; omega⟩
            ⟨by omega, by dsimp [k]; omega⟩))
        ((fmkCtxCarryStep (395 + k) (by dsimp [k]; omega) pNewK pOldK ckW
          (fmkPNew_ne_pOld w _)
          (wire_ne_of_lt (by dsimp [pNewK, fmkPNewW, ckW, k]; omega))
          (wire_ne_of_lt (by dsimp [pOldK, fmkPOldW, ckW, k]; omega))
          (by dsimp [pNewK, fmkPNewW, k]; omega)
          (by dsimp [pOldK, fmkPOldW, k]; omega)
          (by dsimp [ckW, k]; omega)).plug
          (fmkInterleavedU9Shift w rem (by omega)))
theorem fmkInterleavedU9Shift_spec (w : Fin 3) : ∀ (rem : ℕ) (hrem : rem ≤ 7), let k := 8 - rem
      let pR := fmkInterleavedU9Shift w rem hrem
      fmkIsMutBlock 437 (437 - (395 + k)) (fun q ↦ 107 ≤ q.val ∧ q.val < 149) pR ∧
        (∀ γ : BitAssignment 437, cleanRem 437 (437 - (395 + k)) γ →
          let a : Fin 8 → ZMod 2 := fun b ↦ γ (fmkPNewW w b)
          let b : Fin 8 → ZMod 2 := fun b ↦ γ (fmkPOldW w b)
          γ ⟨395 + k - 1, by dsimp [k]; omega⟩ = fmkCarryChain a b k →
          ((bitsVal (fun m ↦ pR.evalBits γ (fmkCat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
            ((bitsVal (fun m ↦ γ (fmkCat42W m)) : ℤ) + (∑ i : Fin (rem + 1),
                (2 ^ (k - 1 + i.val) : ℤ) *
                  (2 * ((fmkSum9 a b ⟨k + i.val, by dsimp [k]; omega⟩).val : ℤ) - 1)) *
                (bitsVal (fun m ↦ γ (fmkBank42W m)) : ℤ)).emod (2 ^ 42 : ℤ)) := by
  let mutCat : Wire 437 → Prop := fun q ↦ 107 ≤ q.val ∧ q.val < 149
  intro rem
  induction rem with
  | zero =>
      intro _
      dsimp only [fmkInterleavedU9Shift]
      obtain ⟨hMut, hEv⟩ := fmkShiftStep_at_spec ⟨402, by decide⟩ 403 ⟨7, by decide⟩
        ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide⟩
      refine ⟨hMut, fun γ hγ hc8 ↦ ?_⟩
      rw [hEv γ hγ, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact congrArg (fun u : ZMod 2 ↦ ((bitsVal (fun m ↦ γ (fmkCat42W m)) : ℤ) +
        (2 ^ 7 : ℤ) * (2 * (u.val : ℤ) - 1) *
          (bitsVal (fun m ↦ γ (fmkBank42W m)) : ℤ)).emod (2 ^ 42 : ℤ)) hc8
  | succ rem ih =>
      intro hrem
      set k := 8 - (rem + 1)
      have hk_lt8 : k < 8 := by omega
      let ckW : Wire 437 := ⟨395 + k - 1, by omega⟩
      let pNewK : Wire 437 := fmkPNewW w ⟨k, hk_lt8⟩
      let pOldK : Wire 437 := fmkPOldW w ⟨k, hk_lt8⟩
      have hpN_lt : pNewK.val < 395 + k := by
        dsimp [pNewK, fmkPNewW]
        omega
      have hpO_lt : pOldK.val < 395 + k := by
        dsimp [pOldK, fmkPOldW]
        omega
      have hck_lt : ckW.val < 395 + k := by
        change 395 + k - 1 < 395 + k
        omega
      have hpN_nc : ¬ mutCat pNewK := by
        dsimp [mutCat, pNewK, fmkPNewW]
        omega
      have hpO_nc : ¬ mutCat pOldK := by
        dsimp [mutCat, pOldK, fmkPOldW]
        omega
      have hck_nc : ¬ mutCat ckW := by
        dsimp [mutCat, ckW]
        omega
      have hN_ck : pNewK ≠ ckW := wire_ne_of_lt (by dsimp [pNewK, fmkPNewW, ckW]; omega)
      have hO_ck : pOldK ≠ ckW := wire_ne_of_lt (by dsimp [pOldK, fmkPOldW, ckW]; omega)
      have hhu : ¬(107 ≤ pNewK.val ∧ pNewK.val < 149) ∧
          ¬(353 ≤ pNewK.val ∧ pNewK.val < 395) ∧ pNewK.val < 395 + k :=
        ⟨hpN_nc, by dsimp [pNewK, fmkPNewW]; omega, hpN_lt⟩
      have hmut_lt : ∀ q, mutCat q → q.val < 395 + k := fun _ hq ↦ by
        dsimp [mutCat] at hq
        omega
      let cXorSum : CliffProg 437 :=
        .seq (.cnot pOldK pNewK (fmkPNew_ne_pOld w _).symm) (.cnot ckW pNewK hN_ck.symm)
      let shK := fmkShiftStep_at pNewK (395 + k) ⟨k - 1, by omega⟩ hhu ⟨by omega, by dsimp; omega⟩
      obtain ⟨hMutSh, hEvSh⟩ := fmkShiftStep_at_spec pNewK (395 + k) ⟨k - 1, by omega⟩ hhu
          ⟨by omega, by dsimp; omega⟩
      obtain ⟨hMut1, hEv1⟩ := fmkCliffPlug_isMutBlock (cur := 395 + k) (by omega)
        mutCat hmut_lt cXorSum
        ⟨⟨hpO_nc, hpN_nc⟩, hck_nc, hpN_nc⟩ ⟨⟨hpO_lt, hpN_lt⟩, hck_lt, hpN_lt⟩ shK hMutSh
      obtain ⟨hMutRec, hEvRec⟩ := ih (by omega)
      have hk_rec : 8 - rem = k + 1 := by omega
      have h395 : 395 + (8 - rem) = 395 + k + 1 := by omega
      let KCarry := fmkCtxCarryStep (395 + k) (by omega) pNewK pOldK ckW
        (fmkPNew_ne_pOld w _) hN_ck hO_ck hpN_lt hpO_lt hck_lt
      obtain ⟨_, hdC, hsC, hlC, hFwdC⟩ := fmkCtxCarryStep_spec (mutW := mutCat)
        (395 + k) (by omega) pNewK pOldK ckW (fmkPNew_ne_pOld w _) hN_ck hO_ck
        hpN_lt hpO_lt hck_lt hpN_nc hpO_nc hck_nc (by dsimp [mutCat]; omega)
      obtain ⟨hMut2, hEv2⟩ := fmkCtxPlug_isMutBlock (cur := 395 + k) (next := 395 + k + 1)
        (by omega) (by omega) mutCat hmut_lt KCarry hdC hsC hlC _ (h395 ▸ hMutRec)
      refine ⟨fmkIsMutBlock_seq (Nat.sub_le _ _) hMut1 hMut2, fun γ hγ hck ↦ ?_⟩
      let a : Fin 8 → ZMod 2 := fun b ↦ γ (fmkPNewW w b)
      let b : Fin 8 → ZMod 2 := fun b ↦ γ (fmkPOldW w b)
      obtain ⟨hγx_cl, hev1⟩ := hEv1 γ hγ
      let γx := cXorSum.eval γ
      have hγx_ne (q : Wire 437) (hq : q ≠ pNewK) : γx q = γ q := by
        simp [γx, cXorSum, CliffProg.eval, Function.update_of_ne hq]
      let γ1 := ((ctxCliffAlloc cXorSum).plug shK).evalBits γ
      have hγ1_cl : cleanRem 437 (437 - (395 + k)) γ1 := hMut1.2.2.1 γ hγ
      have hγ1_non (q : Wire 437) (hq : ¬ mutCat q) : γ1 q = γ q := hMut1.2.2.2 γ hγ q hq
      have hStep1Ev : ((bitsVal (fun m ↦ γ1 (fmkCat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (fmkCat42W m)) : ℤ) +
            (2 ^ (k - 1) : ℤ) * (2 * ((fmkSum9 a b ⟨k, by omega⟩).val : ℤ) - 1) *
              (bitsVal (fun m ↦ γ (fmkBank42W m)) : ℤ)).emod (2 ^ 42 : ℤ) := by
        rw [show (fun m ↦ γ1 (fmkCat42W m)) = fun m ↦ shK.evalBits γx (fmkCat42W m) from
            funext fun m ↦ hev1 (fmkCat42W m) (by dsimp [mutCat, fmkCat42W]; omega),
          hEvSh γx hγx_cl,
          show (fun m ↦ γx (fmkCat42W m)) = fun m ↦ γ (fmkCat42W m) from funext fun _ ↦
            hγx_ne _ (wire_ne_of_lt (by dsimp [fmkCat42W, pNewK, fmkPNewW]; omega)),
          show (fun m ↦ γx (fmkBank42W m)) = fun m ↦ γ (fmkBank42W m) from funext fun _ ↦
            hγx_ne _ (wire_ne_of_gt (by dsimp [fmkBank42W, pNewK, fmkPNewW]; omega)),
          show γx pNewK = fmkSum9 a b ⟨k, by omega⟩ by
            simp only [γx, cXorSum, CliffProg.eval, fmkSum9, dite_eq_left hk_lt8,
              Function.update_self, Function.update_of_ne hN_ck.symm]
            dsimp only [pNewK, pOldK, ckW, a, b, k] at hck ⊢
            rw [hck]]
      obtain ⟨hγ2_cl, hev2⟩ := hEv2 γ1 hγ1_cl
      have hγ2_eq := hFwdC γ1 hγ1_cl
      let γ2 := KCarry.fwdBits γ1
      have hγ2_lt (q : Wire 437) (hlt : q.val < 395 + k) (hnq : ¬ mutCat q) : γ2 q = γ q :=
        (congrFun hγ2_eq q).trans
          ((Function.update_of_ne (wire_ne_of_lt hlt) _ _).trans (hγ1_non q hnq))
      have hck_rec : γ2 ⟨395 + (8 - rem) - 1, by omega⟩ = fmkCarryChain a b (8 - rem) := by
        dsimp only [γ2, KCarry]
        rw [show (⟨395 + (8 - rem) - 1, by omega⟩ : Wire 437) = ⟨395 + k, by omega⟩
            from Fin.ext (by dsimp; omega),
          hγ2_eq, Function.update_self, hk_rec, hγ1_non ckW hck_nc, hγ1_non pNewK hpN_nc,
          hγ1_non pOldK hpO_nc]
        simp only [fmkCarryChain, dite_eq_left hk_lt8]
        dsimp only [ckW, pNewK, pOldK, a, b, k] at hck ⊢
        rw [hck]
      have hRecEv := hEvRec γ2 (h395.symm ▸ hγ2_cl)
      dsimp only at hRecEv
      rw [show (fun i : Fin 8 ↦ γ2 (fmkPNewW w i)) = a from funext fun _ ↦
          hγ2_lt _ (by dsimp [fmkPNewW]; omega) (by dsimp [mutCat, fmkPNewW]; omega),
        show (fun i : Fin 8 ↦ γ2 (fmkPOldW w i)) = b from funext fun _ ↦
          hγ2_lt _ (by dsimp [fmkPOldW]; omega)
            (by dsimp [mutCat, fmkPOldW]; omega)] at hRecEv
      rw [show (fun m ↦ (fmkInterleavedU9Shift w (rem + 1) hrem).evalBits γ (fmkCat42W m)) =
          fun m ↦ (fmkInterleavedU9Shift w rem (by omega)).evalBits γ2 (fmkCat42W m) from
            funext fun m ↦ hev2 (fmkCat42W m) (by dsimp [mutCat, fmkCat42W]; omega),
        hRecEv hck_rec,
        show (fun m ↦ γ2 (fmkCat42W m)) = fun m ↦ γ1 (fmkCat42W m) from funext fun _ ↦
          (congrFun hγ2_eq _).trans
            (Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkCat42W]; omega)) _ _),
        show (fun m ↦ γ2 (fmkBank42W m)) = fun m ↦ γ (fmkBank42W m) from funext fun _ ↦
          hγ2_lt _ (by dsimp [fmkBank42W, k]; omega) (by dsimp [mutCat, fmkBank42W]; omega),
        fmkInt_add_emod, hStep1Ev, ← fmkInt_add_emod]
      have hrhs_sum :
          (∑ i : Fin (rem + 1 + 1), (2 ^ (8 - (rem + 1) - 1 + i.val) : ℤ) *
            (2 * ((fmkSum9 a b ⟨8 - (rem + 1) + i.val, by omega⟩).val : ℤ) - 1)) =
          (2 ^ (k - 1) : ℤ) * (2 * ((fmkSum9 a b ⟨k, by omega⟩).val : ℤ) - 1) +
            ∑ x : Fin (rem + 1), (2 ^ (8 - rem - 1 + x.val) : ℤ) *
              (2 * ((fmkSum9 a b ⟨8 - rem + x.val, by omega⟩).val : ℤ) - 1) := by
        rw [Fin.sum_univ_succ]
        refine congrArg _ (Finset.sum_congr rfl fun x _ ↦ ?_)
        rw [show 8 - (rem + 1) - 1 + x.succ.val = 8 - rem - 1 + x.val by
            simp only [Fin.val_succ]; omega,
          show (⟨8 - (rem + 1) + x.succ.val, by omega⟩ : Fin 9) =
            ⟨8 - rem + x.val, by omega⟩ from Fin.ext (by simp only [Fin.val_succ]; omega)]
      apply congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ))
      rw [hrhs_sum]
      ring
attribute [irreducible] fmkInterleavedU9Shift
def fmkMulAxis_no2a (w : Fin 3) : TempPhaseProg 437 :=
  let pNew0 := fmkPNewW w 0
  let pOld0 := fmkPOldW w 0
  let c1W : Wire 437 := ⟨395, by decide⟩
  let part0 : TempPhaseProg 437 :=
    (ctxCliffAlloc (.cnot pOld0 pNew0 (fmkPNew_ne_pOld w 0).symm)).plug
      (fmkStep2b_nodummy pNew0 ⟨by dsimp [pNew0, fmkPNewW]; omega, fmkPNew_lt353 w 0⟩)
  let part1 : TempPhaseProg 437 := (ctxTempBit pNew0 pOld0 c1W (fmkPNew_ne_pOld w 0)
      (wire_ne_of_lt (by dsimp [pNew0, fmkPNewW, c1W]; omega))
      (wire_ne_of_lt (by dsimp [pOld0, fmkPOldW, c1W]; omega))).plug
      (fmkInterleavedU9Shift w 7 le_rfl)
  (ctxCliffAlloc (fmkFlipP w)).plug (.seq part0 part1)
theorem fmkMulAxis_no2a_spec (w : Fin 3) :
    fmkIsMutBlock 437 (437 - 395) (fun q ↦ 107 ≤ q.val ∧ q.val < 149) (fmkMulAxis_no2a w) ∧
      (∀ β : BitAssignment 437, cleanRem 437 (437 - 395) β → let pNew0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let pOld0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let K_val := bitsVal (fun m ↦ β (fmkBank42W m))
        ((bitsVal (fun m ↦ (fmkMulAxis_no2a w).evalBits β (fmkCat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ β (fmkCat42W m)) : ℤ) +
            (twosComp8Int pNew0 - twosComp8Int pOld0) * (K_val : ℤ) -
            ((K_val / 2 : ℕ) : ℤ)).emod (2 ^ 42 : ℤ)) := by
  let mutCat : Wire 437 → Prop := fun q ↦ 107 ≤ q.val ∧ q.val < 149
  have hmut_lt : ∀ q, mutCat q → q.val < 395 := fun _ hq ↦ lt_trans hq.2 (by decide)
  let pNew0W := fmkPNewW w 0
  let pOld0W := fmkPOldW w 0
  let c1W : Wire 437 := ⟨395, by decide⟩
  have hpN_nc : ¬ mutCat pNew0W := show ¬(107 ≤ 150 + 8 * w.val + 0 ∧
    150 + 8 * w.val + 0 < 149) by omega
  have hpO_nc : ¬ mutCat pOld0W := show ¬(107 ≤ 8 * w.val + 0 ∧ 8 * w.val + 0 < 149) by omega
  have hpN_lt : pNew0W.val < 395 := lt_trans (fmkPNew_lt353 w 0) (by decide)
  have hpO_lt : pOld0W.val < 395 := show 8 * w.val + 0 < 395 by omega
  let step2b := fmkStep2b_nodummy pNew0W ⟨hpN_nc, fmkPNew_lt353 w 0⟩
  obtain ⟨hMut2b, hEv2b⟩ := fmkStep2b_nodummy_spec pNew0W ⟨hpN_nc, fmkPNew_lt353 w 0⟩
  let cXor0 : CliffProg 437 := .cnot pOld0W pNew0W (fmkPNew_ne_pOld w 0).symm
  obtain ⟨hMutP0, hEvP0⟩ := fmkCliffPlug_isMutBlock (cur := 395) (by decide) mutCat hmut_lt
    cXor0 ⟨hpO_nc, hpN_nc⟩ ⟨hpO_lt, hpN_lt⟩ step2b hMut2b
  obtain ⟨hMutSh, hEvSh⟩ := fmkInterleavedU9Shift_spec w 7 le_rfl
  obtain ⟨hMutP1, hEvP1⟩ := fmkTempBitPlug_isMutBlock (cur := 395) (by decide) mutCat hmut_lt
    pNew0W pOld0W (fmkPNew_ne_pOld w 0) (wire_ne_of_lt hpN_lt) (wire_ne_of_lt hpO_lt)
    hpN_lt hpO_lt hpN_nc hpO_nc _ hMutSh
  obtain ⟨hMutOut, hEvOut⟩ := fmkCliffPlug_isMutBlock (cur := 395) (by decide) mutCat
    hmut_lt (fmkFlipP w)
    ⟨by dsimp [CliffDisjoint, mutCat, fmkPNewW]; omega,
      fmkXVec_disjoint 7 _ (fun j ↦ by have := j.isLt; dsimp [mutCat, fmkPOldW]; omega)⟩
    (fmkFlipP_supportsBelow w) _ (fmkIsMutBlock_seq (by decide) hMutP0 hMutP1)
  refine ⟨hMutOut, fun β hβ ↦ ?_⟩
  dsimp only
  obtain ⟨hγ0_cl, hevOut⟩ := hEvOut β hβ
  let γ0 := (fmkFlipP w).eval β
  have hPOld_inj : Function.Injective (fun j : Fin 7 ↦ fmkPOldW w j.castSucc) := fun x y h ↦ by
    have hv := congrArg Fin.val h
    dsimp [fmkPOldW] at hv
    exact Fin.ext (by omega)
  have hγ0_ge24 (q : Wire 437) (hge : 24 ≤ q.val) (hne : q ≠ fmkPNewW w ⟨7, by decide⟩) :
      γ0 q = β q := by
    dsimp only [γ0, fmkFlipP, CliffProg.eval]
    rw [fmkXVec_eval 7 _ hPOld_inj,
      ite_eq_right (fmkNotRange fun _ ↦ wire_ne_of_gt (by dsimp [fmkPOldW]; omega)),
      Function.update_of_ne hne]
  have hγ0_cat (m : Fin 42) : γ0 (fmkCat42W m) = β (fmkCat42W m) :=
    hγ0_ge24 _ (by dsimp [fmkCat42W]; omega)
      (wire_ne_of_lt (by dsimp [fmkCat42W, fmkPNewW]; omega))
  have hγ0_bank (m : Fin 42) : γ0 (fmkBank42W m) = β (fmkBank42W m) :=
    hγ0_ge24 _ (by dsimp [fmkBank42W]; omega)
      (wire_ne_of_gt (by dsimp [fmkBank42W, fmkPNewW]; omega))
  let a : Fin 8 → ZMod 2 := fun b ↦ γ0 (fmkPNewW w b)
  let b : Fin 8 → ZMod 2 := fun b ↦ γ0 (fmkPOldW w b)
  obtain ⟨hγ0x_cl, hevP0⟩ := hEvP0 γ0 hγ0_cl
  let γ0x := cXor0.eval γ0
  let γ1 := ((ctxCliffAlloc cXor0).plug step2b).evalBits γ0
  have hγ1_cl : cleanRem 437 (437 - 395) γ1 := hMutP0.2.2.1 γ0 hγ0_cl
  have hγ1_non : ∀ q : Wire 437, ¬ mutCat q → γ1 q = γ0 q := hMutP0.2.2.2 γ0 hγ0_cl
  have hP0Ev : ((bitsVal (fun m ↦ γ1 (fmkCat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ β (fmkCat42W m)) : ℤ) +
        ((fmkSum9 a b 0).val : ℤ) * (bitsVal (fun m ↦ β (fmkBank42W m)) : ℤ) -
        ((bitsVal (fun m ↦ β (fmkBank42W m)) / 2 : ℕ) : ℤ)).emod (2 ^ 42 : ℤ) := by
    rw [show (fun m ↦ γ1 (fmkCat42W m)) = fun m ↦ step2b.evalBits γ0x (fmkCat42W m) from
        funext fun m ↦ hevP0 (fmkCat42W m) (by dsimp [mutCat, fmkCat42W]; omega),
      hEv2b γ0x hγ0x_cl,
      show (fun m ↦ γ0x (fmkCat42W m)) = fun m ↦ β (fmkCat42W m) from funext fun m ↦
        (Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkCat42W, pNew0W, fmkPNewW]; omega))
          _ _).trans (hγ0_cat m),
      show (fun m ↦ γ0x (fmkBank42W m)) = fun m ↦ β (fmkBank42W m) from funext fun m ↦
        (Function.update_of_ne
          (wire_ne_of_gt (by dsimp [fmkBank42W, pNew0W, fmkPNewW]; omega))
          _ _).trans (hγ0_bank m), show γ0x pNew0W = fmkSum9 a b 0 by
        dsimp [γ0x, cXor0, CliffProg.eval, fmkSum9, fmkCarryChain, a, b, pNew0W, pOld0W]
        rw [Function.update_self]
        ring]
  obtain ⟨hγ2_cl, hevP1⟩ := hEvP1 γ1 hγ1_cl
  let γ2 := Function.update γ1 c1W (γ1 pNew0W * γ1 pOld0W)
  have hγ2_lt (q : Wire 437) (hlt : q.val < 395) (hnq : ¬ mutCat q) : γ2 q = γ0 q :=
    (Function.update_of_ne (wire_ne_of_lt hlt) _ _).trans (hγ1_non q hnq)
  have hc1_eq : γ2 ⟨395 + (8 - 7) - 1, by decide⟩ = fmkCarryChain a b (8 - 7) := by
    dsimp only [γ2, c1W]
    rw [Function.update_self, hγ1_non pNew0W (by dsimp [mutCat, pNew0W, fmkPNewW]; omega),
      hγ1_non pOld0W (by dsimp [mutCat, pOld0W, fmkPOldW]; omega)]
    simp [fmkCarryChain, a, b, pNew0W, pOld0W]
  have hShEv := hEvSh γ2 hγ2_cl
  dsimp only at hShEv
  rw [show (fun i : Fin 8 ↦ γ2 (fmkPNewW w i)) = a from funext fun _ ↦
      hγ2_lt _ (by dsimp [fmkPNewW]; omega) (by dsimp [mutCat, fmkPNewW]; omega),
    show (fun i : Fin 8 ↦ γ2 (fmkPOldW w i)) = b from funext fun _ ↦
      hγ2_lt _ (by dsimp [fmkPOldW]; omega) (by dsimp [mutCat, fmkPOldW]; omega)] at hShEv
  rw [show (fun m ↦ (fmkMulAxis_no2a w).evalBits β (fmkCat42W m)) =
      fun m ↦ (fmkInterleavedU9Shift w 7 le_rfl).evalBits γ2 (fmkCat42W m) from funext fun m ↦
        (hevOut (fmkCat42W m) (by dsimp [mutCat, fmkCat42W]; omega)).trans
          (hevP1 (fmkCat42W m) (by dsimp [mutCat, fmkCat42W]; omega)), hShEv hc1_eq,
    show (fun m ↦ γ2 (fmkCat42W m)) = fun m ↦ γ1 (fmkCat42W m) from funext fun _ ↦
      Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkCat42W, c1W]; omega)) _ _,
    show (fun m ↦ γ2 (fmkBank42W m)) = fun m ↦ β (fmkBank42W m) from funext fun m ↦
      (hγ2_lt _ (by dsimp [fmkBank42W]; omega) (by dsimp [mutCat, fmkBank42W]; omega)).trans
        (hγ0_bank m)]
  let pNewB : Fin 8 → ZMod 2 := fun i ↦ β ⟨150 + 8 * w.val + i.val, by omega⟩
  let pOldB : Fin 8 → ZMod 2 := fun i ↦ β ⟨8 * w.val + i.val, by omega⟩
  have ha_flip : a = fun i : Fin 8 ↦ if i.val = 7 then pNewB i + 1 else pNewB i :=
    funext fun i ↦ by
      by_cases hi7 : i.val = 7
      · dsimp only [a, γ0, fmkFlipP, CliffProg.eval, pNewB]
        rw [ite_eq_left hi7, show fmkPNewW w i = fmkPNewW w ⟨7, by decide⟩ from
            Fin.ext (by dsimp [fmkPNewW]; omega), fmkXVec_eval 7 _ hPOld_inj,
          ite_eq_right (fmkNotRange fun _ ↦ wire_ne_of_gt (by dsimp [fmkPNewW, fmkPOldW]; omega)),
          Function.update_self]
        exact congrArg (· + 1) (congrArg β (Fin.ext (by dsimp [fmkPNewW]; omega)))
      · rw [ite_eq_right hi7]
        exact hγ0_ge24 _ (by dsimp [fmkPNewW]; omega)
          (fun h ↦ hi7 (by have hv := congrArg Fin.val h; dsimp [fmkPNewW] at hv; omega))
  have hb_flip : b = fun i : Fin 8 ↦ if i.val < 7 then pOldB i + 1 else pOldB i :=
    funext fun i ↦ by
      dsimp only [b, γ0, fmkFlipP, CliffProg.eval, pOldB]
      rw [fmkXVec_eval 7 _ hPOld_inj]
      by_cases hi7 : i.val < 7
      · rw [ite_eq_left hi7, ite_eq_left ⟨⟨i.val, hi7⟩, Fin.ext rfl⟩,
          Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkPOldW, fmkPNewW]; omega))]
        rfl
      · rw [ite_eq_right hi7, ite_eq_right (fmkNotRange fun j ↦
            wire_ne_of_gt (by have := j.isLt; dsimp [fmkPOldW]; omega)),
          Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkPOldW, fmkPNewW]; omega))]
        rfl
  have hDelta := fmkDeltaBitsAlgebra pNewB pOldB (fmkSum9 a b)
    (by rw [fmkBitsVal_sum9, ha_flip, hb_flip])
  dsimp only at hDelta
  rw [show (∑ i : Fin 8, (2 ^ (8 - 7 - 1 + i.val) : ℤ) *
        (2 * ((fmkSum9 a b ⟨8 - 7 + i.val, by omega⟩).val : ℤ) - 1)) =
      ∑ s : Fin 8, (2 ^ s.val : ℤ) * (2 * ((fmkSum9 a b s.succ).val : ℤ) - 1) from
      Finset.sum_congr rfl fun s _ ↦ by
        rw [show 8 - 7 - 1 + s.val = s.val by omega,
          show (⟨8 - 7 + s.val, by omega⟩ : Fin 9) = s.succ from Fin.ext (by dsimp; omega)],
    fmkInt_add_emod, hP0Ev, ← fmkInt_add_emod]
  apply congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ))
  rw [hDelta]
  ring
attribute [irreducible] fmkMulAxis_no2a
end
end ConfigFastMidKick275
section ConfigFastMidKick275_C
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
local instance (priority := 10) instNeZeroTwoPowFmkC (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Real SpecsAux
open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_lt wire_ne_of_gt CliffProg
  TempPhaseProg cleanRem
  cleanRem_anti ValidCleanRem validCleanRem_mono CliffDisjoint TempCtx ctxCliffAlloc
  ctxCliffAlloc_disjoint ctxCliffAlloc_supports ctxTempBit)
open TwosCompAndWire0Cancel (twosComp8Int)
open scoped BigOperators
noncomputable section
theorem fmkFanoutUnary_disjoint_len {M : ℕ} {mutW : Wire M → Prop}
    (uBase : ℕ) (target : Wire M) (pred : ℕ → Bool) (hnt : ¬ mutW target) :
    ∀ (K : ℕ) (hK : uBase + K ≤ target.val),
      (∀ w : Wire M, uBase ≤ w.val → w.val < uBase + K → ¬ mutW w) →
      CliffDisjoint mutW (fmkFanoutUnary uBase target pred K hK)
  | 0, _, _ => trivial
  | K + 1, hK, hnu => by
      dsimp only [fmkFanoutUnary]
      refine ⟨fmkFanoutUnary_disjoint_len uBase target pred hnt K (Nat.le_of_succ_le hK)
        (fun w h1 h2 ↦ hnu w h1 (by omega)), ?_⟩
      split_ifs
      · exact ⟨hnu ⟨uBase + K, lt_of_lt_of_le (Nat.lt_of_succ_le hK) (le_of_lt target.isLt)⟩
          (by dsimp; omega) (by dsimp; omega), hnt⟩
      · trivial
def fmkXorDeltaBit18 (tTab : Fin 256 → ℕ) (j : Fin 42) (γ : BitAssignment 437) : ZMod 2 :=
  let b0 := γ ⟨91, by decide⟩
  let b1 := γ ⟨92, by decide⟩
  ∑ p : Fin 54, let v00 := fmkBitZ ((tTab (fmkIdx0 0 p.val 0)).testBit j.val)
    let v01 := fmkBitZ ((tTab (fmkIdx0 0 p.val 1)).testBit j.val)
    let v10 := fmkBitZ ((tTab (fmkIdx0 1 p.val 0)).testBit j.val)
    let v11 := fmkBitZ ((tTab (fmkIdx0 1 p.val 1)).testBit j.val)
    if p.val < 18 then
      γ ⟨280 + p.val, by omega⟩ * (v00 + b0 * (v00 + v01)) +
        γ ⟨334 + p.val, by omega⟩ * (v10 + b0 * (v10 + v11))
    else
      γ ⟨280 + p.val, by omega⟩ *
        ((1 + b1) * (v00 + b0 * (v00 + v01)) + b1 * (v10 + b0 * (v10 + v11)))
theorem fmkXorDeltaBit18_congr (tTab : Fin 256 → ℕ) (j : Fin 42) {γ₁ γ₂ : BitAssignment 437}
    (h91 : γ₁ ⟨91, by decide⟩ = γ₂ ⟨91, by decide⟩) (h92 : γ₁ ⟨92, by decide⟩ = γ₂ ⟨92, by decide⟩)
    (hu : ∀ w : Wire 437, 280 ≤ w.val → w.val < 352 → γ₁ w = γ₂ w) :
    fmkXorDeltaBit18 tTab j γ₁ = fmkXorDeltaBit18 tTab j γ₂ := by
  dsimp only [fmkXorDeltaBit18]
  rw [h91, h92]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : p.val < 18
  · rw [ite_eq_left hp,
    ite_eq_left hp, hu ⟨280 + p.val, by omega⟩ (by dsimp; omega) (by dsimp; omega),
      hu ⟨334 + p.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)]
  · rw [ite_eq_right hp,
    ite_eq_right hp, hu ⟨280 + p.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)]
theorem fmkBitZ_mux4 (b0 b1 : ZMod 2) (f : ℕ → ℕ → Bool) :
    (1 + b1) * (fmkBitZ (f 0 0) + b0 * (fmkBitZ (f 0 0) + fmkBitZ (f 0 1))) +
      b1 * (fmkBitZ (f 1 0) + b0 * (fmkBitZ (f 1 0) + fmkBitZ (f 1 1))) =
      fmkBitZ (f b1.val b0.val) := by
  rcases fmkBit_cases b0 with rfl | rfl
  · rcases fmkBit_cases b1 with rfl | rfl
    · simp only [ZMod.val_zero, add_zero, one_mul, zero_mul]
    · simp only [ZMod.val_zero, ZMod.val_one, CharTwo.add_self_eq_zero,
        zero_mul, zero_add, one_mul, add_zero]
  · rcases fmkBit_cases b1 with rfl | rfl
    · simp only [ZMod.val_zero, ZMod.val_one, add_zero, one_mul, zero_mul]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · simp only [ZMod.val_one, CharTwo.add_self_eq_zero, zero_mul, zero_add, one_mul]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
theorem fmkXorDeltaBit18_of_unary72 (tTab : Fin 256 → ℕ) (j : Fin 42) (γ : BitAssignment 437)
    (g : ZMod 2) (p0 : ℕ) (hp0 : p0 < 54) (hpre : ∀ (p : ℕ) (hp : p < 18),
      γ ⟨280 + p, by omega⟩ = (1 + γ ⟨92, by decide⟩) * (g * (if p = p0 then 1 else 0)) ∧
      γ ⟨334 + p, by omega⟩ = γ ⟨92, by decide⟩ * (g * (if p = p0 then 1 else 0)))
    (hsuf : ∀ (p : ℕ), 18 ≤ p → (hp : p < 54) →
      γ ⟨280 + p, by omega⟩ = g * (if p = p0 then 1 else 0)) : fmkXorDeltaBit18 tTab j γ =
      g * fmkBitZ ((tTab (fmkIdx0 (γ ⟨92, by decide⟩).val p0
        (γ ⟨91, by decide⟩).val)).testBit j.val) := by
  dsimp only [fmkXorDeltaBit18]
  rw [Finset.sum_eq_single ⟨p0, hp0⟩]
  · dsimp only
    split_ifs with hp
    · rw [(hpre p0 hp).1, (hpre p0 hp).2, ite_eq_left rfl, mul_one,
        ← fmkBitZ_mux4 (γ ⟨91, by decide⟩) (γ ⟨92, by decide⟩)
          (fun b1 b0 ↦ (tTab (fmkIdx0 b1 p0 b0)).testBit j.val)]
      ring
    · rw [hsuf p0 (by omega) hp0, ite_eq_left rfl, mul_one,
        fmkBitZ_mux4 (γ ⟨91, by decide⟩) (γ ⟨92, by decide⟩)
          (fun b1 b0 ↦ (tTab (fmkIdx0 b1 p0 b0)).testBit j.val)]
  · intro p _ hne
    have hp_ne : p.val ≠ p0 := fun h ↦ hne (Fin.ext h)
    split_ifs with hp
    · rw [(hpre p.val hp).1, (hpre p.val hp).2, ite_eq_right hp_ne]
      ring
    · rw [hsuf p.val (by omega) p.isLt, ite_eq_right hp_ne, mul_zero, zero_mul]
  · exact fun h ↦ absurd (Finset.mem_univ _) h
theorem fmkThreeFan_eval_aux {M : ℕ} (c1 c2 c3 : CliffProg M) (dst : Wire M)
    (S1 S2 S3 : BitAssignment M → ZMod 2)
    (he1 : ∀ δ, c1.eval δ = Function.update δ dst (δ dst + S1 δ))
    (he2 : ∀ δ, c2.eval δ = Function.update δ dst (δ dst + S2 δ))
    (he3 : ∀ δ, c3.eval δ = Function.update δ dst (δ dst + S3 δ))
    (hS2 : ∀ δ v, S2 (Function.update δ dst v) = S2 δ)
    (hS3 : ∀ δ v, S3 (Function.update δ dst v) = S3 δ) (γ : BitAssignment M) :
    (CliffProg.seq c1 (.seq c2 c3)).eval γ = Function.update γ dst
    (γ dst + (S1 γ + S2 γ + S3 γ)) := by
  dsimp only [CliffProg.eval]
  rw [he1 γ, he2, hS2, Function.update_idem, Function.update_self,
    he3, hS3, Function.update_idem, Function.update_self]
  congr 1
  ring
def fmkFan3Pred (pred : ℕ → ℕ → Bool) (dst : Wire 437) (hdst : 431 ≤ dst.val) : CliffProg 437 :=
  .seq (fmkFanoutUnary 280 dst (pred 0) 54 (by omega))
    (.seq (fmkFanoutUnary 334 dst (pred 1) 18 (by omega))
      (fmkFanoutUnary 395 dst (fun i ↦ pred 1 (18 + i)) 36 (by omega)))
def fmkFan3Sum (pred : ℕ → ℕ → Bool) (γ : BitAssignment 437) : ZMod 2 :=
  (∑ p : Fin 54, if pred 0 p.val then γ ⟨280 + p.val, by omega⟩ else 0) +
  (∑ p : Fin 18, if pred 1 p.val then γ ⟨334 + p.val, by omega⟩ else 0) +
  (∑ i : Fin 36, if pred 1 (18 + i.val) then γ ⟨395 + i.val, by omega⟩ else 0)
theorem fmkFan3Sum_congr (pred : ℕ → ℕ → Bool) {γ₁ γ₂ : BitAssignment 437}
    (h : ∀ w : Wire 437, w.val < 431 → ¬(353 ≤ w.val ∧ w.val < 395) → γ₁ w = γ₂ w) :
    fmkFan3Sum pred γ₁ = fmkFan3Sum pred γ₂ := by
  dsimp only [fmkFan3Sum]
  exact fmkAddCongr
    (fmkAddCongr
      (Finset.sum_congr rfl fun p _ ↦ by rw [h _ (by dsimp; omega) (by dsimp; omega)])
      (Finset.sum_congr rfl fun p _ ↦ by rw [h _ (by dsimp; omega) (by dsimp; omega)]))
    (Finset.sum_congr rfl fun i _ ↦ by rw [h _ (by dsimp; omega) (by dsimp; omega)])
theorem fmkFan3Pred_eval (pred : ℕ → ℕ → Bool) (dst : Wire 437) (hdst : 431 ≤ dst.val)
    (γ : BitAssignment 437) : (fmkFan3Pred pred dst hdst).eval γ =
      Function.update γ dst (γ dst + fmkFan3Sum pred γ) := fmkThreeFan_eval_aux _ _ _ dst
    (fun δ ↦ ∑ p : Fin 54, if pred 0 p.val then δ ⟨280 + p.val, by omega⟩ else 0)
    (fun δ ↦ ∑ p : Fin 18, if pred 1 p.val then δ ⟨334 + p.val, by omega⟩ else 0)
    (fun δ ↦ ∑ i : Fin 36, if pred 1 (18 + i.val) then δ ⟨395 + i.val, by omega⟩ else 0)
    (fmkFanoutUnary_eval 280 dst (pred 0) 54 _)
    (fmkFanoutUnary_eval 334 dst (pred 1) 18 _)
    (fmkFanoutUnary_eval 395 dst (fun i ↦ pred 1 (18 + i)) 36 _)
    (fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))])
    (fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))])
    γ
theorem fmkFan3Pred_disjoint {mutW : Wire 437 → Prop} (pred : ℕ → ℕ → Bool)
    (dst : Wire 437) (hdst : 431 ≤ dst.val) (hndst : ¬ mutW dst)
    (hnb : ∀ w : Wire 437, ¬(353 ≤ w.val ∧ w.val < 395) → ¬ mutW w) :
    CliffDisjoint mutW (fmkFan3Pred pred dst hdst) :=
  ⟨fmkFanoutUnary_disjoint_len 280 dst _ hndst 54 (by omega) (fun w _ hw2 ↦ hnb w (by omega)),
   fmkFanoutUnary_disjoint_len 334 dst _ hndst 18 (by omega) (fun w _ hw2 ↦ hnb w (by omega)),
   fmkFanoutUnary_disjoint_len 395 dst _ hndst 36 (by omega) (fun w hw1 _ ↦ hnb w (by omega))⟩
theorem fmkFan3Pred_supportsBelow (pred : ℕ → ℕ → Bool) (dst : Wire 437)
    (hdst : 431 ≤ dst.val) (bnd : ℕ) (hbnd : dst.val < bnd) :
    (fmkFan3Pred pred dst hdst).SupportsBelow bnd :=
  ⟨fmkFanoutUnary_supportsBelow 280 dst _ bnd hbnd 54 (by omega),
   fmkFanoutUnary_supportsBelow 334 dst _ bnd hbnd 18 (by omega),
   fmkFanoutUnary_supportsBelow 395 dst _ bnd hbnd 36 (by omega)⟩
def fmkRawBit18 (tTab : Fin 256 → ℕ) (j : Fin 42) (γ : BitAssignment 437) : ZMod 2 :=
  γ ⟨91, by decide⟩ * fmkFan3Sum (fmkXorPredD tTab j) γ + fmkFan3Sum (fmkXorPredB tTab j) γ
def fmkXorBitCtx18 (tTab : Fin 256 → ℕ) (j : Fin 42) : TempCtx 437 :=
  let scrD : Wire 437 := ⟨431, by decide⟩
  let outW : Wire 437 := ⟨432, by decide⟩
  let fanD := fmkFan3Pred (fmkXorPredD tTab j) scrD le_rfl
  (ctxCliffAlloc fanD).append
    ((ctxTempBit ⟨91, by decide⟩ scrD outW (by decide) (by decide) (by decide)).append
      (ctxCliffAlloc (.seq (fmkFan3Pred (fmkXorPredB tTab j) outW (by decide)) fanD.inv)))
theorem fmkXorBitCtx18_spec (tTab : Fin 256 → ℕ) (j : Fin 42) :
    let mutJ : Wire 437 → Prop := fun w ↦ ∃ _ : Fin 1, w = fmkBank42W j
    (fmkXorBitCtx18 tTab j).DisjointFrom mutJ ∧ (fmkXorBitCtx18 tTab j).SupportsBelowCtx 433 ∧
      fmkTempCtxLiftEx 431 433 (fmkXorBitCtx18 tTab j) ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - 431) γ →
        (fmkXorBitCtx18 tTab j).fwdBits γ ⟨432, by decide⟩ = fmkRawBit18 tTab j γ) := by
  intro mutJ
  let scrD : Wire 437 := ⟨431, by decide⟩
  let outW : Wire 437 := ⟨432, by decide⟩
  have hnbank : ∀ w : Wire 437, ¬(353 ≤ w.val ∧ w.val < 395) → ¬ mutJ w :=
    fun _ hw ⟨_, hj⟩ ↦ hw (hj ▸ ⟨Nat.le_add_right 353 j.val, by dsimp [fmkBank42W]; omega⟩)
  have hdD := fmkFan3Pred_disjoint (fmkXorPredD tTab j) scrD le_rfl
    (hnbank scrD (by decide)) hnbank
  have hdB := fmkFan3Pred_disjoint (fmkXorPredB tTab j) outW (by decide)
    (hnbank outW (by decide)) hnbank
  have hsD := fmkFan3Pred_supportsBelow (fmkXorPredD tTab j) scrD le_rfl 432 (by decide)
  have hsBD : (CliffProg.seq (fmkFan3Pred (fmkXorPredB tTab j) outW (by decide))
      (fmkFan3Pred (fmkXorPredD tTab j) scrD le_rfl).inv).SupportsBelow 433 :=
    ⟨fmkFan3Pred_supportsBelow (fmkXorPredB tTab j) outW (by decide) 433 (by decide),
      CliffProg.inv_supportsBelow _ (CliffProg.supportsBelow_mono (by decide) hsD)⟩
  refine ⟨TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint hdD)
      (TempCtx.disjointFrom_append
        ⟨hnbank ⟨91, by decide⟩ (by decide), hnbank scrD (by decide),
          hnbank outW (by decide), trivial⟩
        (ctxCliffAlloc_disjoint ⟨hdB, CliffDisjoint.inv hdD⟩)),
    TempCtx.supportsBelowCtx_append (c₁ := 432) (by decide) (ctxCliffAlloc_supports hsD)
      (TempCtx.supportsBelowCtx_append le_rfl ⟨by decide, trivial⟩
        (ctxCliffAlloc_supports hsBD)), fmkTempCtxLiftEx_append
      (fmkTempCtxLiftEx_mono (by decide) le_rfl (by decide)
        (fmkTempCtxLiftEx_cliff (by decide) _ hsD))
      (fmkTempCtxLiftEx_append
        (fmkTempCtxLiftEx_tempBit (cur := 432) (by decide) ⟨91, by decide⟩ scrD
          (by decide) (by decide) (by decide))
        (fmkTempCtxLiftEx_cliff (cur := 433) (by decide) _ hsBD)), fun γ hγ ↦ ?_⟩
  dsimp only [fmkXorBitCtx18]
  refine fmkTwoCliffTemp_fwdBits_step (fmkFan3Pred (fmkXorPredD tTab j) scrD le_rfl)
    (fmkFan3Pred (fmkXorPredB tTab j) outW (by decide)) ⟨91, by decide⟩ scrD outW
    (by decide) (by decide) (by decide) γ (P := fun γ4 ↦ γ4 outW = fmkRawBit18 tTab j γ) ?_
  intro γ1 γ2 γ3 γ4 hγ1_def hγ2_def hγ3_def hγ4_def
  have hγ1_eq : γ1 = Function.update γ scrD (γ scrD + fmkFan3Sum (fmkXorPredD tTab j) γ) :=
    hγ1_def.symm.trans (fmkFan3Pred_eval _ scrD le_rfl γ)
  rw [(congrFun hγ4_def.symm outW).trans
      (CliffProg.eval_outside _ (CliffProg.inv_supportsBelow _ hsD) γ3 outW (by decide)),
    ← hγ3_def, fmkFan3Pred_eval _ outW (by decide) γ2, Function.update_self,
    show γ2 outW = γ ⟨91, by decide⟩ * fmkFan3Sum (fmkXorPredD tTab j) γ by
      rw [← hγ2_def, Function.update_self, hγ1_eq,
        Function.update_of_ne (by decide : outW ≠ scrD), hγ outW (by decide), zero_add,
        Function.update_of_ne (wire_ne_of_lt (by decide)),
        Function.update_self, hγ scrD (by decide), zero_add],
    fmkFan3Sum_congr (fmkXorPredB tTab j) (γ₁ := γ2) (γ₂ := γ) fun w hw _ ↦ by
      rw [← hγ2_def, Function.update_of_ne (wire_ne_of_lt (by dsimp [outW]; omega)),
        hγ1_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [scrD]; omega))]]
  rfl
attribute [irreducible] fmkFan3Pred fmkXorBitCtx18
def fmkXorBitProg18 (tTab : Fin 256 → ℕ) (j : Fin 42) : TempPhaseProg 437 :=
  (fmkXorBitCtx18 tTab j).plug (.cliff (fmkCnotVec 1 (fun _ ↦ ⟨432, by decide⟩)
    (fun _ ↦ fmkBank42W j) (fun _ ↦ wire_ne_of_gt (by dsimp [fmkBank42W]; omega))))
theorem fmkXorBitProg18_spec (tTab : Fin 256 → ℕ) (j : Fin 42) :
    fmkIsMutBlock 437 (437 - 431) (fun w ↦ ∃ i : Fin 42, w = fmkBank42W i)
      (fmkXorBitProg18 tTab j) ∧ (∀ γ : BitAssignment 437, cleanRem 437 (437 - 431) γ →
        (∀ w : Wire 437, w ≠ fmkBank42W j → (fmkXorBitProg18 tTab j).evalBits γ w = γ w) ∧
        (fmkXorBitProg18 tTab j).evalBits γ (fmkBank42W j) =
          γ (fmkBank42W j) + fmkRawBit18 tTab j γ) := by
  obtain ⟨hDisj, hSupp, hLift, hFwd⟩ := fmkXorBitCtx18_spec tTab j
  obtain ⟨hVal, _, hSgn, hBits⟩ := fmkXorBlock_of_ctx (M := 437) (curStart := 431)
    (curEnd := 433) (W := 1) (by omega) (by omega) (fun _ ↦ fmkBank42W j)
    (fun _ ↦ by dsimp [fmkBank42W]; omega) (fun a b _ ↦ Subsingleton.elim a b)
    (fun _ ↦ ⟨432, by decide⟩) (fun _ ↦ by decide) (fmkXorBitCtx18 tTab j) hDisj hSupp
    (fmkXorBitCtx18 tTab j).fwdBits (fmkTempCtxLiftEx_probe hLift)
  have hNonJ : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 431) γ →
      ∀ w : Wire 437, w ≠ fmkBank42W j → (fmkXorBitProg18 tTab j).evalBits γ w = γ w :=
    fun γ hγ w hne ↦ (hBits γ hγ w).trans (dite_eq_right fun ⟨_, hw⟩ ↦ hne hw)
  refine ⟨⟨hVal, hSgn, fun γ hγ w hw ↦ by
        rw [hNonJ γ hγ w (wire_ne_of_gt (by dsimp [fmkBank42W]; omega))]
        exact hγ w hw, fun γ hγ w hnw ↦ hNonJ γ hγ w fun h ↦ hnw ⟨j, h⟩⟩,
    fun γ hγ ↦ ⟨hNonJ γ hγ, ?_⟩⟩
  have hHit : (fmkXorBitProg18 tTab j).evalBits γ (fmkBank42W j) =
      γ (fmkBank42W j) + (fmkXorBitCtx18 tTab j).fwdBits γ ⟨432, by decide⟩ :=
    (hBits γ hγ (fmkBank42W j)).trans (dite_eq_left ⟨0, rfl⟩)
  rw [hHit, hFwd γ hγ]
attribute [irreducible] fmkXorBitProg18
def fmkXorBitLoop18 (tTab : Fin 256 → ℕ) : (remJ : ℕ) → remJ ≤ 42 → TempPhaseProg 437
  | 0, _ => .nil
  | remJ + 1, hJ =>
      .seq (fmkXorBitProg18 tTab ⟨42 - (remJ + 1), by omega⟩)
        (fmkXorBitLoop18 tTab remJ (by omega))
theorem fmkXorBitLoop18_spec (tTab : Fin 256 → ℕ) : ∀ (remJ : ℕ) (hJ : remJ ≤ 42),
    fmkIsMutBlock 437 (437 - 431) (fun w ↦ ∃ j : Fin 42, w = fmkBank42W j)
      (fmkXorBitLoop18 tTab remJ hJ) ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - 431) γ → ∀ j : Fin 42,
        (fmkXorBitLoop18 tTab remJ hJ).evalBits γ (fmkBank42W j) =
          if 42 - remJ ≤ j.val then γ (fmkBank42W j) + fmkRawBit18 tTab j γ else γ (fmkBank42W j))
  | 0, _ =>
      ⟨⟨trivial, fun _ _ ↦ rfl, fun _ hγ ↦ hγ, fun _ _ _ _ ↦ rfl⟩,
        fun γ _ j ↦ (ite_eq_right (by omega : ¬(42 ≤ j.val))).symm⟩
  | remJ + 1, hJ => by
      let j0 : Fin 42 := ⟨42 - (remJ + 1), by omega⟩
      obtain ⟨hMut0, hEv0⟩ := fmkXorBitProg18_spec tTab j0
      obtain ⟨hMutR, hEvR⟩ := fmkXorBitLoop18_spec tTab remJ (by omega)
      refine ⟨fmkIsMutBlock_seq (by decide) hMut0 hMutR, fun γ hγ j ↦ ?_⟩
      dsimp only [fmkXorBitLoop18, TempPhaseProg.evalBits]
      let γ1 := (fmkXorBitProg18 tTab j0).evalBits γ
      rw [hEvR γ1 (hMut0.2.2.1 γ hγ) j]
      have hnb (w : Wire 437) (hw : ¬(353 ≤ w.val ∧ w.val < 395)) : γ1 w = γ w :=
        hMut0.2.2.2 γ hγ w (fun ⟨_, h⟩ ↦ hw (by rw [h]; dsimp [fmkBank42W]; omega))
      have hraw_eq : fmkRawBit18 tTab j γ1 = fmkRawBit18 tTab j γ := by
        dsimp only [fmkRawBit18]
        rw [hnb _ (by decide), fmkFan3Sum_congr _ (fun w _ ↦ hnb w),
          fmkFan3Sum_congr _ (fun w _ ↦ hnb w)]
      by_cases hj_eq : j = j0
      · subst hj_eq
        rw [ite_eq_right (by dsimp [j0]; omega), ite_eq_left (by dsimp [j0]; omega)]
        exact (hEv0 γ hγ).2
      · have hj_ne : j.val ≠ j0.val := fun h ↦ hj_eq (Fin.ext h)
        have hγ1_j : γ1 (fmkBank42W j) = γ (fmkBank42W j) :=
          (hEv0 γ hγ).1 _ fun h ↦ hj_eq (fmkBank42W_inj h)
        by_cases hj_gt : 42 - remJ ≤ j.val
        · rw [ite_eq_left hj_gt, ite_eq_left (by omega), hγ1_j, hraw_eq]
        · rw [ite_eq_right hj_gt, ite_eq_right (by dsimp [j0] at hj_ne; omega), hγ1_j]
attribute [irreducible] fmkXorBitLoop18
def fmkXorBank42Ctx36 : TempCtx 437 :=
  fmkCtxSplitPrefix 298 395 36 ⟨92, by decide⟩ (by decide) (by decide) (by decide) 36 le_rfl
def fmkXorBank42_at353 (tTab : Fin 256 → ℕ) : TempPhaseProg 437 :=
  fmkXorBank42Ctx36.plug (fmkXorBitLoop18 tTab 42 le_rfl)
theorem fmkXorTerm_pre (b0 u0 u1 v00 v01 v10 v11 : ZMod 2) :
    (b0 * (u0 * (v00 + v01)) + b0 * (u1 * (v10 + v11))) + (u0 * v00 + u1 * v10) =
      u0 * (v00 + b0 * (v00 + v01)) + u1 * (v10 + b0 * (v10 + v11)) := by ring
theorem fmkXorTerm_suf (b0 b1 u v00 v01 v10 v11 : ZMod 2) :
    (b0 * ((u + u * b1) * (v00 + v01)) + b0 * ((u * b1) * (v10 + v11))) +
      ((u + u * b1) * v00 + (u * b1) * v10) =
    u * ((1 + b1) * (v00 + b0 * (v00 + v01)) + b1 * (v10 + b0 * (v10 + v11))) := by ring
theorem fmkRawBit18_eq_xorDeltaBit18 (tTab : Fin 256 → ℕ) (j : Fin 42) (γ δ : BitAssignment 437)
    (hδ91 : δ ⟨91, by decide⟩ = γ ⟨91, by decide⟩) (hδ_pre : ∀ (p : ℕ) (hp : p < 18),
      δ ⟨280 + p, by omega⟩ = γ ⟨280 + p, by omega⟩ ∧
      δ ⟨334 + p, by omega⟩ = γ ⟨334 + p, by omega⟩) (hδ_suf : ∀ (i : ℕ) (hi : i < 36),
      δ ⟨298 + i, by omega⟩ = γ ⟨298 + i, by omega⟩ + γ ⟨298 + i, by omega⟩ * γ ⟨92, by decide⟩ ∧
      δ ⟨395 + i, by omega⟩ = γ ⟨298 + i, by omega⟩ * γ ⟨92, by decide⟩) :
    fmkRawBit18 tTab j δ = fmkXorDeltaBit18 tTab j γ := by
  dsimp only [fmkRawBit18, fmkFan3Sum, fmkXorDeltaBit18]
  rw [hδ91]
  have split54 (f : Fin 54 → ZMod 2) : (∑ p : Fin 54, f p) =
      (∑ p : Fin 18, f ⟨p.val, by omega⟩) + (∑ i : Fin 36, f ⟨18 + i.val, by omega⟩) := by
    rw [Fin.sum_univ_add (a := 18) (b := 36)]
    rfl
  rw [split54 (fun p ↦ if fmkXorPredD tTab j 0 p.val then δ ⟨280 + p.val, by omega⟩ else 0),
    split54 (fun p ↦ if fmkXorPredB tTab j 0 p.val then δ ⟨280 + p.val, by omega⟩ else 0), split54,
    show ∀ (b0 a1 a2 a3 a4 b1 b2 b3 b4 : ZMod 2),
      b0 * ((a1 + a2) + a3 + a4) + ((b1 + b2) + b3 + b4) =
        (b0 * (a1 + a3) + (b1 + b3)) + (b0 * (a2 + a4) + (b2 + b4)) from
      fun _ _ _ _ _ _ _ _ _ ↦ by ring]
  refine fmkAddCongr ?_ ?_
  · rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp only [ite_eq_left p.isLt, (hδ_pre p.val p.isLt).1, (hδ_pre p.val p.isLt).2,
      fmkXorPredD, fmkXorPredB, fmkIte_mul_bitZ, fmkBitZ_xor]
    ring
  · rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ite_eq_right (by omega : ¬(18 + i.val < 18)),
      show (⟨280 + (18 + i.val), by omega⟩ : Wire 437) = ⟨298 + i.val, by omega⟩ from
        Fin.ext (by dsimp; omega), (hδ_suf i.val i.isLt).1, (hδ_suf i.val i.isLt).2]
    simp only [fmkXorPredD, fmkXorPredB, fmkIte_mul_bitZ, fmkBitZ_xor]
    ring
theorem fmkXorBank42_at353_spec (tTab : Fin 256 → ℕ) :
    fmkIsMutBlock 437 (437 - 395) (fun w ↦ ∃ j : Fin 42, w = fmkBank42W j)
      (fmkXorBank42_at353 tTab) ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - 395) γ → ∀ j : Fin 42,
        (fmkXorBank42_at353 tTab).evalBits γ (fmkBank42W j) =
          γ (fmkBank42W j) + fmkXorDeltaBit18 tTab j γ) := by
  let mutBank : Wire 437 → Prop := fun w ↦ ∃ j : Fin 42, w = fmkBank42W j
  obtain ⟨hLMut, hLEv⟩ := fmkXorBitLoop18_spec tTab 42 le_rfl
  have hnbank : ∀ w : Wire 437, ¬(353 ≤ w.val ∧ w.val < 395) → ¬ mutBank w :=
    fun _ hw ⟨j, hj⟩ ↦ hw (hj ▸ ⟨Nat.le_add_right 353 j.val, by dsimp [fmkBank42W]; omega⟩)
  obtain ⟨hd36, hs36⟩ := fmkCtxSplitPrefix_props (mutW := mutBank) 298 395 36 ⟨92, by decide⟩
    (by decide) (by decide) (by decide) (hnbank ⟨92, by decide⟩ (by decide))
    (fun w _ hw2 ↦ hnbank w (by omega)) (fun w hw1 _ ↦ hnbank w (by omega)) 36 le_rfl
  obtain ⟨hl36, hSpec36⟩ := fmkCtxSplitPrefix_scoped (M := 437) 298 395 36 ⟨92, by decide⟩
    (by decide) (by decide) (by decide) 36 le_rfl
  obtain ⟨hMutOut, hEvOut⟩ := fmkCtxPlug_isMutBlock (cur := 395) (next := 431)
    (by decide) (by decide) mutBank
    (by rintro _ ⟨j, rfl⟩; dsimp [fmkBank42W]; omega)
    fmkXorBank42Ctx36 hd36 hs36 hl36 (fmkXorBitLoop18 tTab 42 le_rfl) hLMut
  refine ⟨hMutOut, fun γ hγ j ↦ ?_⟩
  obtain ⟨hcl36, hev⟩ := hEvOut γ hγ
  obtain ⟨_, hsrc36, hdst36, hout36⟩ := hSpec36 γ hγ
  let δ := fmkXorBank42Ctx36.fwdBits γ
  have hbj : δ (fmkBank42W j) = γ (fmkBank42W j) :=
    hout36 (fmkBank42W j) (by dsimp [fmkBank42W]; omega) (by dsimp [fmkBank42W]; omega)
  dsimp only [fmkXorBank42_at353]
  rw [hev (fmkBank42W j) ⟨j, rfl⟩, hLEv δ hcl36 j, ite_eq_left (Nat.zero_le j.val), hbj]
  exact congrArg (γ (fmkBank42W j) + ·) (fmkRawBit18_eq_xorDeltaBit18 tTab j γ δ
    (hout36 ⟨91, by decide⟩ (by decide) (by decide))
    (fun p hp ↦ ⟨hout36 ⟨280 + p, by omega⟩ (by dsimp; omega) (by dsimp; omega),
      hout36 ⟨334 + p, by omega⟩ (by dsimp; omega) (by dsimp; omega)⟩)
    (fun i hi ↦ ⟨hsrc36 i (Nat.zero_le _) hi, hdst36 i (Nat.zero_le _) hi⟩))
attribute [irreducible] fmkXorBank42Ctx36 fmkXorBank42_at353
def fmkRefPass (tTab : Fin 256 → ℕ) (passProg : TempPhaseProg 437) : TempPhaseProg 437 :=
  .seq (fmkXorBank42_at353 tTab) (.seq passProg (fmkXorBank42_at353 tTab))
theorem fmkRefPass_spec (tTab : Fin 256 → ℕ) (passProg : TempPhaseProg 437)
    (hPass : fmkIsMutBlock 437 (437 - 395) (fun w ↦ 107 ≤ w.val ∧ w.val < 149) passProg) :
    fmkIsMutBlock 437 (437 - 353) (fun w ↦ 107 ≤ w.val ∧ w.val < 149) (fmkRefPass tTab passProg) ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - 353) γ →
        let γLoaded := (fmkXorBank42_at353 tTab).evalBits γ
        (∀ j : Fin 42, γLoaded (fmkBank42W j) = fmkXorDeltaBit18 tTab j γ) ∧
        (∀ w : Wire 437, ¬(353 ≤ w.val ∧ w.val < 395) → γLoaded w = γ w) ∧
        cleanRem 437 (437 - 395) γLoaded ∧
        (∀ m : Fin 42, (fmkRefPass tTab passProg).evalBits γ (fmkCat42W m) =
          passProg.evalBits γLoaded (fmkCat42W m))) := by
  let mutCat : Wire 437 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
  let mutBank : Wire 437 → Prop := fun w ↦ ∃ j : Fin 42, w = fmkBank42W j
  let mutBoth : Wire 437 → Prop := fun w ↦ mutCat w ∨ mutBank w
  obtain ⟨hMX, hEX⟩ := fmkXorBank42_at353_spec tTab
  have hnbank : ∀ w : Wire 437, ¬(353 ≤ w.val ∧ w.val < 395) → ¬ mutBank w :=
    fun _ hw ⟨j, hj⟩ ↦ hw (hj ▸ ⟨Nat.le_add_right 353 j.val, by dsimp [fmkBank42W]; omega⟩)
  have liftBank := fmkIsMutBlock_mono_mut (m₂ := mutBoth) (fun _ ↦ Or.inr) hMX
  have liftCat := fmkIsMutBlock_mono_mut (m₂ := mutBoth) (fun _ ↦ Or.inl) hPass
  have hMut395 := fmkIsMutBlock_seq (by decide) liftBank
    (fmkIsMutBlock_seq (by decide) liftCat liftBank)
  have hNon353 : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 353) γ →
      ∀ q : Wire 437, ¬ mutCat q → (fmkRefPass tTab passProg).evalBits γ q = γ q := by
    intro γ hγ q hnq
    have hγ395 : cleanRem 437 (437 - 395) γ := cleanRem_anti (by decide) hγ
    by_cases hb : mutBank q
    · obtain ⟨j, rfl⟩ := hb
      dsimp only [fmkRefPass, TempPhaseProg.evalBits]
      let γ1 := (fmkXorBank42_at353 tTab).evalBits γ
      have hγ1_cl : cleanRem 437 (437 - 395) γ1 := hMX.2.2.1 γ hγ395
      let γ2 := passProg.evalBits γ1
      have hγ2_cl : cleanRem 437 (437 - 395) γ2 := hPass.2.2.1 γ1 hγ1_cl
      have hγ2_low : ∀ w : Wire 437, ¬ mutCat w → ¬(353 ≤ w.val ∧ w.val < 395) → γ2 w = γ w :=
        fun w hnc hw ↦ (hPass.2.2.2 γ1 hγ1_cl w hnc).trans (hMX.2.2.2 γ hγ395 w (hnbank w hw))
      rw [hEX γ2 hγ2_cl j,
        show γ2 (fmkBank42W j) = (fmkXorBank42_at353 tTab).evalBits γ (fmkBank42W j) from
          hPass.2.2.2 γ1 hγ1_cl _ (by dsimp [mutCat, fmkBank42W]; omega), hEX γ hγ395 j,
        fmkXorDeltaBit18_congr tTab j (hγ2_low _ (by decide) (by decide))
          (hγ2_low _ (by decide) (by decide))
          (fun w h1 h2 ↦ hγ2_low w (by dsimp [mutCat]; omega) (by omega)),
        fmkZmod2_add_self_cancel]
    · exact hMut395.2.2.2 γ hγ395 q fun h ↦ h.elim hnq hb
  refine ⟨⟨validCleanRem_mono (by decide) hMut395.1,
      fun γ hγ ↦ hMut395.2.1 γ (cleanRem_anti (by decide) hγ),
      fun γ hγ q hq ↦ by rw [hNon353 γ hγ q (by dsimp [mutCat]; omega)]; exact hγ q hq, hNon353⟩,
    fun γ hγ ↦ ?_⟩
  have hγ395 : cleanRem 437 (437 - 395) γ := cleanRem_anti (by decide) hγ
  let γ1 := (fmkXorBank42_at353 tTab).evalBits γ
  have hγ1_cl : cleanRem 437 (437 - 395) γ1 := hMX.2.2.1 γ hγ395
  refine ⟨fun j ↦ by
      rw [hEX γ hγ395 j, hγ (fmkBank42W j) (by dsimp [fmkBank42W]; omega), zero_add],
    fun w hw ↦ hMX.2.2.2 γ hγ395 w (hnbank w hw), hγ1_cl, fun m ↦ ?_⟩
  dsimp only [fmkRefPass, TempPhaseProg.evalBits]
  exact hMX.2.2.2 (passProg.evalBits γ1) (hPass.2.2.1 γ1 hγ1_cl) (fmkCat42W m)
    (hnbank (fmkCat42W m) (by dsimp [fmkCat42W]; omega))
def fmkHalfSumTable (t0 t1 t2 : Fin 256 → ℕ) (idx : Fin 256) : ℕ :=
  ((t0 idx / 2) + (t1 idx / 2) + (t2 idx / 2)) % 2 ^ 42
def fmkMidKickInner353 (t0 t1 t2 : Fin 256 → ℕ) : TempPhaseProg 437 := .seq
    (fmkRefPass (fmkHalfSumTable t0 t1 t2) fmkAdd42Bank) (.seq (fmkRefPass t0 (fmkMulAxis_no2a
    0)) (.seq (fmkRefPass t1 (fmkMulAxis_no2a 1)) (fmkRefPass t2 (fmkMulAxis_no2a 2))))
theorem fmkChain4_emod {M c k0 d1 d2 d3 s1 s2 s3 s4 : ℤ} (h1 : s1.emod M = (c + k0).emod M)
    (h2 : s2.emod M = (s1 + d1).emod M) (h3 : s3.emod M = (s2 + d2).emod M)
    (h4 : s4.emod M = (s3 + d3).emod M) : s4.emod M = (c + k0 + d1 + d2 + d3).emod M := by
  rw [h4, fmkInt_add_emod s3 d3 M, h3, ← fmkInt_add_emod (n := M),
    add_assoc s2 d2 d3, fmkInt_add_emod s2 (d2 + d3) M, h2, ← fmkInt_add_emod (n := M),
    add_assoc s1 d1 (d2 + d3), fmkInt_add_emod s1 (d1 + (d2 + d3)) M, h1,
    ← fmkInt_add_emod (n := M)]
  exact congrArg (fun z : ℤ ↦ z.emod M) (by ring)
theorem fmkMidKickInner353_mutC (t0 t1 t2 : Fin 256 → ℕ) : fmkIsMutBlock 437 (437 - 353)
    (fun q : Wire 437 ↦ 107 ≤ q.val ∧ q.val < 149) (fmkMidKickInner353 t0 t1 t2) :=
  fmkIsMutBlock_seq (by decide)
    (fmkRefPass_spec (fmkHalfSumTable t0 t1 t2) fmkAdd42Bank fmkAdd42Bank_spec.1).1
    (fmkIsMutBlock_seq (by decide)
      (fmkRefPass_spec t0 (fmkMulAxis_no2a 0) (fmkMulAxis_no2a_spec 0).1).1
      (fmkIsMutBlock_seq (by decide)
        (fmkRefPass_spec t1 (fmkMulAxis_no2a 1) (fmkMulAxis_no2a_spec 1).1).1
        (fmkRefPass_spec t2 (fmkMulAxis_no2a 2) (fmkMulAxis_no2a_spec 2).1).1))
theorem fmkGraft280_frameC (K : TempCtx 437) (hdK : K.DisjointFrom (fun q : Wire 437 ↦ 107 ≤
    q.val ∧ q.val < 149)) (hsK : K.SupportsBelowCtx 353) (hlK : fmkTempCtxLiftEx 280 353 K)
    (body : TempPhaseProg 437) (hMut : fmkIsMutBlock 437 (437 - 353) (fun q : Wire 437 ↦ 107 ≤
    q.val ∧ q.val < 149) body) : ValidCleanRem 437 (437 - 280) (K.plug body) ∧
    (∀ β1, cleanRem 437 (437 - 280) β1 → (K.plug body).evalSign β1 = 0) ∧ (∀ β1, cleanRem 437
    (437 - 280) β1 → cleanRem 437 (437 - 280) ((K.plug body).evalBits β1)) ∧ (∀ β1, cleanRem
    437 (437 - 280) β1 → ∀ q : Wire 437, ¬(107 ≤ q.val ∧ q.val < 149) → (K.plug body).evalBits
    β1 q = β1 q) ∧ (∀ β1, cleanRem 437 (437 - 280) β1 → ∀ m : Fin 42, (K.plug body).evalBits
    β1 (fmkCat42W m) = body.evalBits (K.fwdBits β1) (fmkCat42W m)) := by
  obtain ⟨hMut280, hEv280⟩ := fmkCtxPlug_isMutBlock (cur := 280) (next := 353)
    (by decide) (by decide) (fun q : Wire 437 ↦ 107 ≤ q.val ∧ q.val < 149)
    (fun _ hq ↦ by omega) K hdK hsK hlK body hMut
  exact ⟨hMut280.1, hMut280.2.1, hMut280.2.2.1, hMut280.2.2.2,
    fun β1 h1 m ↦ (hEv280 β1 h1).2 (fmkCat42W m) (by dsimp [fmkCat42W]; omega)⟩
theorem fmkDeltaVal_catC (β γ : BitAssignment 437)
    (hγ_lt275 : ∀ q : Wire 437, q.val < 275 → γ q = β q)
    (idx0 : Fin 256) (p0_idx : ℕ) (hp0_lt : p0_idx < 54)
    (hidx_eq : fmkIdx0 (β ⟨92, by decide⟩).val p0_idx (β ⟨91, by decide⟩).val = idx0)
    (hpre' : ∀ (p : ℕ) (hp : p < 18), γ ⟨280 + p, by omega⟩ =
        (1 + γ ⟨92, by decide⟩) * (β fmkAccW * (if p = p0_idx then 1 else 0)) ∧
      γ ⟨334 + p, by omega⟩ = γ ⟨92, by decide⟩ * (β fmkAccW * (if p = p0_idx then 1 else 0)))
    (hsuf' : ∀ (p : ℕ), 18 ≤ p → (hp : p < 54) →
      γ ⟨280 + p, by omega⟩ = β fmkAccW * (if p = p0_idx then 1 else 0)) (δ : BitAssignment 437)
    (hδ_non : ∀ q : Wire 437, ¬(107 ≤ q.val ∧ q.val < 149) → δ q = γ q)
    (t : Fin 256 → ℕ) (ht : ∀ i, t i < 2 ^ 42) (δL : BitAssignment 437)
    (hδL : ∀ j : Fin 42, δL (fmkBank42W j) = fmkXorDeltaBit18 t j δ) :
    bitsVal (fun j : Fin 42 ↦ δL (fmkBank42W j)) = (β fmkAccW).val * t idx0 := by
  have hfn : (fun j : Fin 42 ↦ δL (fmkBank42W j)) =
      fun j : Fin 42 ↦ β fmkAccW * fmkBitZ ((t idx0).testBit j.val) := funext fun j ↦ by
    rw [hδL j, fmkXorDeltaBit18_congr t j (hδ_non _ (by decide)) (hδ_non _ (by decide))
        (fun w h1 h2 ↦ hδ_non w (by omega)),
      fmkXorDeltaBit18_of_unary72 t j γ (β fmkAccW) p0_idx hp0_lt hpre' hsuf',
      hγ_lt275 ⟨92, by decide⟩ (by decide), hγ_lt275 ⟨91, by decide⟩ (by decide), hidx_eq]
  rw [hfn]
  rcases fmkBit_cases (β fmkAccW) with ha0 | ha1
  · simp only [ha0, zero_mul, ZMod.val_zero]
    exact fmkBitsVal_zero 42
  · simp only [ha1, ZMod.val_one, one_mul]
    exact fmkBitsVal_eq_of_testBit _ _ (ht idx0) fun _ ↦ rfl
theorem fmkLoadedAxis_catC (w : Fin 3) (t : Fin 256 → ℕ) (β γ sIn : BitAssignment 437)
    (hγ_lt275 : ∀ q : Wire 437, q.val < 275 → γ q = β q)
    (hnIn : ∀ q : Wire 437, ¬(107 ≤ q.val ∧ q.val < 149) → sIn q = γ q)
    (hclIn : cleanRem 437 (437 - 353) sIn) (pNew0 pOld0 : Fin 3 → Fin 256) (hpNew0 : pNew0 w =
      ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩)
    (hpOld0 : pOld0 w =
      ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩) (kVal : ℕ)
    (hKW : ∀ δL : BitAssignment 437, (∀ j : Fin 42, δL (fmkBank42W j) = fmkXorDeltaBit18 t j sIn) →
      bitsVal (fun m ↦ δL (fmkBank42W m)) = kVal) :
    ((bitsVal (fun m ↦ (fmkRefPass t (fmkMulAxis_no2a w)).evalBits sIn (fmkCat42W m)) :
        ℤ)).emod (2 ^ 42 : ℤ) = ((bitsVal (fun m ↦ sIn (fmkCat42W m)) : ℤ) +
        ((twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) * (kVal : ℤ) -
          ((kVal / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ) := by
  obtain ⟨hMM, hEM⟩ := fmkMulAxis_no2a_spec w
  obtain ⟨_, hEP⟩ := fmkRefPass_spec t (fmkMulAxis_no2a w) hMM
  obtain ⟨hbL, hnonL, hclL, hcatP⟩ := hEP sIn hclIn
  let δL := (fmkXorBank42_at353 t).evalBits sIn
  have hδ_lt (q : Wire 437) (hq : q.val < 174) (hnc : ¬(107 ≤ q.val ∧ q.val < 149)) :
      δL q = β q := (hnonL q (by omega)).trans ((hnIn q hnc).trans (hγ_lt275 q (by omega)))
  have hpNLW : (⟨bitsVal (fun b : Fin 8 ↦ δL ⟨150 + 8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 w := (Fin.ext (congrArg bitsVal (funext fun _ ↦
      hδ_lt _ (by dsimp; omega) (by dsimp; omega)))).trans hpNew0.symm
  have hpOLW : (⟨bitsVal (fun b : Fin 8 ↦ δL ⟨8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 w := (Fin.ext (congrArg bitsVal (funext fun _ ↦
      hδ_lt _ (by dsimp; omega) (by dsimp; omega)))).trans hpOld0.symm
  have hEv := hEM δL hclL
  dsimp only at hEv
  rw [show (fun m ↦ (fmkRefPass t (fmkMulAxis_no2a w)).evalBits sIn (fmkCat42W m)) =
      fun m ↦ (fmkMulAxis_no2a w).evalBits δL (fmkCat42W m) from funext hcatP,
    hEv, show (fun m ↦ δL (fmkCat42W m)) = fun m ↦ sIn (fmkCat42W m) from
      funext fun _ ↦ hnonL _ (by dsimp [fmkCat42W]; omega), hKW δL hbL, hpNLW, hpOLW]
  exact congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ)) (by ring)
theorem fmkSeq4_evalBits_apply {n : ℕ} (P0 P1 P2 P3 : TempPhaseProg n) (γ : BitAssignment n)
    (w : Wire n) : (TempPhaseProg.seq P0 (.seq P1 (.seq P2 P3))).evalBits γ w = P3.evalBits
    (P2.evalBits (P1.evalBits (P0.evalBits γ))) w := rfl
theorem fmkMidKickInner353_eval_catC (t0 t1 t2 : Fin 256 → ℕ)
    (ht0 : ∀ i, t0 i < 2 ^ 42) (ht1 : ∀ i, t1 i < 2 ^ 42) (ht2 : ∀ i, t2 i < 2 ^ 42)
    (β γ : BitAssignment 437) (hcl72 : cleanRem 437 (437 - 353) γ)
    (hγ_lt275 : ∀ q : Wire 437, q.val < 275 → γ q = β q) (idx0 : Fin 256)
    (pNew0 pOld0 : Fin 3 → Fin 256) (hpNew0 : ∀ w : Fin 3, pNew0 w =
      ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩)
    (hpOld0 : ∀ w : Fin 3, pOld0 w =
      ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩)
    (p0_idx : ℕ) (hp0_lt : p0_idx < 54)
    (hidx_eq : fmkIdx0 (β ⟨92, by decide⟩).val p0_idx (β ⟨91, by decide⟩).val = idx0)
    (hpre' : ∀ (p : ℕ) (hp : p < 18), γ ⟨280 + p, by omega⟩ =
        (1 + γ ⟨92, by decide⟩) * (β fmkAccW * (if p = p0_idx then 1 else 0)) ∧
      γ ⟨334 + p, by omega⟩ = γ ⟨92, by decide⟩ * (β fmkAccW * (if p = p0_idx then 1 else 0)))
    (hsuf' : ∀ (p : ℕ), 18 ≤ p → (hp : p < 54) →
      γ ⟨280 + p, by omega⟩ = β fmkAccW * (if p = p0_idx then 1 else 0)) :
    ((bitsVal (fun m ↦ (fmkMidKickInner353 t0 t1 t2).evalBits γ (fmkCat42W m)) : ℤ)).emod
        (2 ^ 42 : ℤ) = ((bitsVal (fun m ↦ β (fmkCat42W m)) : ℤ) + ((β fmkAccW).val : ℤ) *
        ∑ w : Fin 3, (twosComp8Int (pNew0 w) - twosComp8Int (pOld0 w)) *
          (match w.val with | 0 => t0 idx0 | 1 => t1 idx0 | _ => t2 idx0 : ℤ)).emod
        (2 ^ 42 : ℤ) := by
  obtain ⟨hMA, hEA⟩ := fmkAdd42Bank_spec
  obtain ⟨hMP0, hEP0⟩ := fmkRefPass_spec (fmkHalfSumTable t0 t1 t2) fmkAdd42Bank hMA
  have hMP1 := (fmkRefPass_spec t0 (fmkMulAxis_no2a 0) (fmkMulAxis_no2a_spec 0).1).1
  have hMP2 := (fmkRefPass_spec t1 (fmkMulAxis_no2a 1) (fmkMulAxis_no2a_spec 1).1).1
  let s1 := (fmkRefPass (fmkHalfSumTable t0 t1 t2) fmkAdd42Bank).evalBits γ
  let s2 := (fmkRefPass t0 (fmkMulAxis_no2a 0)).evalBits s1
  let s3 := (fmkRefPass t1 (fmkMulAxis_no2a 1)).evalBits s2
  let s4 := (fmkRefPass t2 (fmkMulAxis_no2a 2)).evalBits s3
  have hc1 := hMP0.2.2.1 γ hcl72
  have hc2 := hMP1.2.2.1 s1 hc1
  have hc3 := hMP2.2.2.1 s2 hc2
  have hn1 := hMP0.2.2.2 γ hcl72
  have hn2 := fun q hq ↦ (hMP1.2.2.2 s1 hc1 q hq).trans (hn1 q hq)
  have hn3 := fun q hq ↦ (hMP2.2.2.2 s2 hc2 q hq).trans (hn2 q hq)
  obtain ⟨hbL0, hnonL0, hclL0, hcatP0⟩ := hEP0 γ hcl72
  have hs1_ev : ((bitsVal (fun m ↦ s1 (fmkCat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ β (fmkCat42W m)) : ℤ) +
        (((β fmkAccW).val * fmkHalfSumTable t0 t1 t2 idx0 : ℕ) : ℤ)).emod (2 ^ 42 : ℤ) := by
    rw [show (fun m ↦ s1 (fmkCat42W m)) =
        fun m ↦ fmkAdd42Bank.evalBits ((fmkXorBank42_at353 _).evalBits γ) (fmkCat42W m) from
        funext hcatP0, hEA _ hclL0,
      show (fun m ↦ (fmkXorBank42_at353 _).evalBits γ (fmkCat42W m)) =
        fun m ↦ β (fmkCat42W m) from funext fun _ ↦ (hnonL0 _ (by dsimp [fmkCat42W]; omega)).trans
          (hγ_lt275 _ (by dsimp [fmkCat42W]; omega)),
      fmkDeltaVal_catC β γ hγ_lt275 idx0 p0_idx hp0_lt hidx_eq hpre' hsuf' γ (fun _ _ ↦ rfl)
        (fmkHalfSumTable t0 t1 t2) (fun _ ↦ Nat.mod_lt _ (by positivity)) _ hbL0]
  have hAxis (w : Fin 3) (t : Fin 256 → ℕ) (ht : ∀ i, t i < 2 ^ 42) {s : BitAssignment 437}
      (hn : ∀ q : Wire 437, ¬(107 ≤ q.val ∧ q.val < 149) → s q = γ q)
      (hc : cleanRem 437 (437 - 353) s) :=
    fmkLoadedAxis_catC w t β γ s hγ_lt275 hn hc pNew0 pOld0 (hpNew0 w) (hpOld0 w) _
      (fmkDeltaVal_catC β γ hγ_lt275 idx0 p0_idx hp0_lt hidx_eq hpre' hsuf' s hn t ht)
  rw [show (fun m ↦ (fmkMidKickInner353 t0 t1 t2).evalBits γ (fmkCat42W m)) =
      fun m ↦ s4 (fmkCat42W m) from
        funext fun m ↦ fmkSeq4_evalBits_apply _ _ _ _ γ (fmkCat42W m),
    fmkChain4_emod hs1_ev (hAxis 0 t0 ht0 hn1 hc1) (hAxis 1 t1 ht1 hn2 hc2)
      (hAxis 2 t2 ht2 hn3 hc3), Fin.sum_univ_three]
  dsimp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  rcases fmkBit_cases (β fmkAccW) with hacc0 | hacc1
  · simp only [hacc0, ZMod.val_zero, zero_mul, Nat.zero_div, Nat.cast_zero, mul_zero,
      sub_zero, add_zero]
  · simp only [hacc1, ZMod.val_one, Nat.cast_one, one_mul, fmkHalfSumTable]
    set hsum := (t0 idx0 / 2) + (t1 idx0 / 2) + (t2 idx0 / 2)
    have hz : (2 ^ 42 : ℤ) * ((hsum / 2 ^ 42 : ℕ) : ℤ) + ((hsum % 2 ^ 42 : ℕ) : ℤ) =
        ((t0 idx0 / 2 : ℕ) : ℤ) + ((t1 idx0 / 2 : ℕ) : ℤ) + ((t2 idx0 / 2 : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_add_mod hsum (2 ^ 42)
    exact fmkEmod_eq_of_add_mul (-((hsum / 2 ^ 42 : ℕ) : ℤ)) (by linarith)
end
end ConfigFastMidKick275_C
section Dyn_FastMidKick275
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
local instance (priority := 10) instNeZeroTwoPowFmkDyn (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat Real SpecsAux
open _root_.QuantumComputation.Specs.StoppingPowerSolution (mul_mulVec_prog writeRegProg
  writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem)
open MeasureBranchHadamardSem (ket bitSign sqrtHalf
  sqrtHalf_mul_sqrtHalf bit_cases matrix_ext_ket eval_seq_mulVec ket_X ket_Z ket_H ket_CNOT
  ket_projector projZeroAll ket_projZeroAll hadamardAll xReset writeSynd syndSign
  writeSynd_apply_of_not_mem)
open scoped BigOperators Matrix ComplexOrder MatrixOrder Circuit.Notation
attribute [local instance 10] Classical.propDecidable
noncomputable section
attribute [local irreducible] fmkRefPass
theorem fmkBitSign_smul_congr {V : Type*} [AddCommGroup V] [Module ℂ V] {a b : ZMod 2}
    (h : a = b) (v : V) : bitSign a • v = bitSign b • v := by
  rw [h]
def fmkCZ {n : ℕ} (a b : Wire n) (h : a ≠ b) : Circuit n :=
  Circuit.H b ;;ᶜ Circuit.CNOT a b h ;;ᶜ Circuit.H b
@[simp] theorem fmkCZ_count_t {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (fmkCZ a b h).count PrimitiveGate.T = 0 := by
  simp [fmkCZ]
@[simp] theorem fmkCZ_count_toff {n : ℕ} (a b : Wire n) (h : a ≠ b) :
    (fmkCZ a b h).count PrimitiveGate.TOFF = 0 := by
  simp [fmkCZ]
theorem fmkBitSign_one_add (x : ZMod 2) : bitSign (1 + x) = -bitSign x := by
  rcases bit_cases x with rfl | rfl <;> simp [bitSign, show (1 + 1 : ZMod 2) = 0 from rfl]
theorem fmkBitSign_add (x y : ZMod 2) : bitSign (x + y) = bitSign x * bitSign y := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;>
    simp [bitSign, show (1 + 1 : ZMod 2) = 0 from rfl]
theorem fmkBitSign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    bitSign (∑ i ∈ s, f i) = ∏ i ∈ s, bitSign (f i) := by
  classical
  refine Finset.induction_on s (by simp [bitSign]) fun a s ha ih ↦ ?_
  rw [Finset.sum_insert ha, fmkBitSign_add, ih, Finset.prod_insert ha]
theorem fmkHadamardPair_alg {V : Type*} [AddCommGroup V] [Module ℂ V] (k0 k1 : V) (s1 s2 : ℂ)
    : (sqrtHalf : ℂ) • ((sqrtHalf : ℂ) • (k0 + s1 • k1) + s2 • ((sqrtHalf : ℂ) • (k0 + (-s1) •
    k1))) = ((1 / 2 : ℂ) * (1 + s2)) • k0 + ((1 / 2 : ℂ) * s1 * (1 - s2)) • k1 := by
  have hsq := sqrtHalf_mul_sqrtHalf
  simp only [smul_add, smul_smul,
    show (sqrtHalf : ℂ) * (sqrtHalf * s1) = (sqrtHalf * sqrtHalf) * s1 by ring,
    show (sqrtHalf : ℂ) * (s2 * sqrtHalf) = (sqrtHalf * sqrtHalf) * s2 by ring,
    show (sqrtHalf : ℂ) * (s2 * (sqrtHalf * -s1)) = -((sqrtHalf * sqrtHalf) * s1 * s2) by ring,
    hsq]
  module
theorem ket_fmkCZ {n : ℕ} (a b : Wire n) (h : a ≠ b) (β : BitAssignment n) :
    (fmkCZ a b h).eval.1.mulVec (ket β) = bitSign (β a * β b) • ket β := by
  dsimp only [fmkCZ]
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_H, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_add, Matrix.mulVec_smul, ket_CNOT, ket_CNOT]
  simp only [Function.update_of_ne h, Function.update_self, Function.update_idem, zero_add,
    Matrix.mulVec_add, Matrix.mulVec_smul, ket_H, fmkBitSign_one_add, fmkHadamardPair_alg]
  rcases bit_cases (β b) with hb | hb
  · rw [hb, show Function.update β b 0 = β by rw [← hb, Function.update_eq_self]]
    simp only [bitSign, mul_zero, ↓reduceIte]
    module
  · rw [hb, show Function.update β b 1 = β by rw [← hb, Function.update_eq_self]]
    simp only [bitSign, mul_one, one_ne_zero, ↓reduceIte]
    module
def fmkOptZ {n : ℕ} (coeff : ZMod 2) (q : Wire n) : Circuit n :=
  if coeff = 1 then Circuit.Z q else .identity
def fmkOptCZ {n : ℕ} (coeff : ZMod 2) (a b : Wire n) (h : a ≠ b) : Circuit n :=
  if coeff = 1 then fmkCZ a b h else .identity
theorem ket_fmkOptZ {n : ℕ} (coeff : ZMod 2) (q : Wire n) (β : BitAssignment n) :
    (fmkOptZ coeff q).eval.1.mulVec (ket β) = bitSign (coeff * β q) • ket β := by
  dsimp only [fmkOptZ]
  rcases bit_cases coeff with rfl | rfl
  · simp [bitSign]
  · rw [ite_eq_left rfl, one_mul, ket_Z]
theorem ket_fmkOptCZ {n : ℕ} (coeff : ZMod 2) (a b : Wire n) (h : a ≠ b) (β : BitAssignment n) :
    (fmkOptCZ coeff a b h).eval.1.mulVec (ket β) = bitSign (coeff * (β a * β b)) • ket β := by
  dsimp only [fmkOptCZ]
  rcases bit_cases coeff with rfl | rfl
  · simp [bitSign]
  · rw [ite_eq_left rfl, one_mul, ket_fmkCZ]
def fmkSeqFin {n : ℕ} : (k : ℕ) → (Fin k → Circuit n) → Circuit n
  | 0, _ => .identity
  | k + 1, cs => cs 0 ;;ᶜ fmkSeqFin k (fun i ↦ cs i.succ)
theorem fmkSeqFin_count_eq_zero {n a : ℕ} (g : PrimitiveGate a) :
    ∀ (k : ℕ) (cs : Fin k → Circuit n), (∀ i, (cs i).count g = 0) → (fmkSeqFin k cs).count g = 0
  | 0, _, _ => rfl
  | k + 1, cs, hc => by
      simp [fmkSeqFin, hc 0, fmkSeqFin_count_eq_zero g k (fun i ↦ cs i.succ) (fun i ↦ hc i.succ)]
theorem ket_fmkSeqFin {n : ℕ} (β : BitAssignment n) :
    ∀ (k : ℕ) (cs : Fin k → Circuit n) (φ : Fin k → ZMod 2),
      (∀ i, (cs i).eval.1.mulVec (ket β) = bitSign (φ i) • ket β) →
      (fmkSeqFin k cs).eval.1.mulVec (ket β) = bitSign (∑ i : Fin k, φ i) • ket β
  | 0, _, _, _ => by simp [fmkSeqFin, bitSign]
  | k + 1, cs, φ, hcs => by
      rw [fmkSeqFin, eval_seq_mulVec, hcs 0, Matrix.mulVec_smul,
        ket_fmkSeqFin β k (fun i ↦ cs i.succ) (fun i ↦ φ i.succ) (fun i ↦ hcs i.succ),
        smul_smul, ← fmkBitSign_add, Fin.sum_univ_succ]
attribute [local irreducible] fmkSeqFin
theorem ket_fmkDiag4 {n : ℕ} (c₁ c₂ c₃ c₄ : Circuit n) (β : BitAssignment n) {φ₁ φ₂ φ₃ φ₄ : ZMod 2}
    (h₁ : c₁.eval.1.mulVec (ket β) = bitSign φ₁ • ket β)
    (h₂ : c₂.eval.1.mulVec (ket β) = bitSign φ₂ • ket β)
    (h₃ : c₃.eval.1.mulVec (ket β) = bitSign φ₃ • ket β)
    (h₄ : c₄.eval.1.mulVec (ket β) = bitSign φ₄ • ket β) :
    ((c₁ ;;ᶜ c₂) ;;ᶜ (c₃ ;;ᶜ c₄)).eval.1.mulVec (ket β) = bitSign (φ₁ + φ₂ + φ₃ + φ₄) • ket β := by
  rw [eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec, h₁, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_smul, h₂, Matrix.mulVec_smul, Matrix.mulVec_smul, h₃,
    Matrix.mulVec_smul, h₄, smul_smul, smul_smul, smul_smul, ← fmkBitSign_add,
    ← fmkBitSign_add, ← fmkBitSign_add]
set_option allowUnsafeReducibility true in
theorem fmkWriteSynd_apply_mem {n : ℕ} : ∀ (m : ℕ) (qs : Fin m → Wire n), Function.Injective qs →
      ∀ (y : Fin m → Bool) (β : BitAssignment n) (r : Fin m),
        writeSynd m qs y β (qs r) = if y r then 1 else 0
  | 0, _, _, _, _, r => Fin.elim0 r
  | m + 1, qs, hqs, y, β, r => by
      cases r using Fin.cases with
      | zero =>
          rw [writeSynd, writeSynd_apply_of_not_mem m (fun i ↦ qs i.succ) _ _ (qs 0)
            (fun i h ↦ Fin.succ_ne_zero i (hqs h.symm)), Function.update_self]
      | succ j =>
          exact fmkWriteSynd_apply_mem m (fun i ↦ qs i.succ)
            (hqs.comp (Fin.succ_injective _)) (fun i ↦ y i.succ) _ j
theorem fmkSyndSign_eq_prod {n : ℕ} :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (g : Fin m → Bool) (β : BitAssignment n),
      syndSign m qs g β = ∏ r : Fin m, (if g r then bitSign (β (qs r)) else 1)
  | 0, _, _, _ => by simp [syndSign]
  | m + 1, qs, g, β => by
      rw [syndSign, fmkSyndSign_eq_prod m (fun i ↦ qs i.succ) (fun i ↦ g i.succ) β,
        Fin.prod_univ_succ]
theorem fmkSyndSign_writeSynd_eq_bitSign_sum {n : ℕ} (m : ℕ) (qs : Fin m → Wire n)
    (hqs : Function.Injective qs) (g : Fin m → Bool) (d : Fin m → ZMod 2)
    (β : BitAssignment n) : syndSign m qs g (writeSynd m qs (fun r ↦ decide (d r = 1)) β) =
    bitSign (∑ r : Fin m, if g r then d r else 0) := by
  rw [fmkSyndSign_eq_prod, fmkBitSign_sum]
  refine Finset.prod_congr rfl fun r _ ↦ ?_
  rw [fmkWriteSynd_apply_mem m qs hqs, show (if decide (d r = 1) then (1 : ZMod 2) else 0) = d r by
      rcases bit_cases (d r) with h | h <;> simp [h]]
  cases g r <;> simp [bitSign]
theorem fmkProj_comm_diag {n : ℕ} {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {clean : BitAssignment n → Prop}
    (hP_ket : ∀ β, P.mulVec (ket β) = if clean β then ket β else 0) (w : Wire n)
    (o : Fin (2 ^ 1)) : (QRegister.singleton w).basisOutcomeProjector o * P = P *
    (QRegister.singleton w).basisOutcomeProjector o := by
  apply matrix_ext_ket
  intro β
  simp only [mul_mulVec_prog, hP_ket, ket_projector]
  by_cases hc : clean β <;> by_cases hw : β w = (o.val : ZMod 2) <;>
    simp [hc, hw, hP_ket, ket_projector]
theorem fmkProjZeroAll_comm_diag {n : ℕ} {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {clean : BitAssignment n → Prop}
    (hP_ket : ∀ β, P.mulVec (ket β) = if clean β then ket β else 0) (m : ℕ)
    (qs : Fin m → Wire n) : projZeroAll m qs * P = P * projZeroAll m qs := by
  apply matrix_ext_ket
  intro β
  simp only [mul_mulVec_prog, hP_ket, ket_projZeroAll]
  by_cases hc : clean β <;> by_cases hq : (∀ r, β (qs r) = 0) <;>
    simp [hc, hq, hP_ket, ket_projZeroAll]
theorem fmkXReset_comm_diag {n : ℕ}
    {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {clean : BitAssignment n → Prop}
    (hP_ket : ∀ β, P.mulVec (ket β) = if clean β then ket β else 0) :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (g : Fin m → Bool),
      (∀ (r : Fin m) (b : ZMod 2) (β : BitAssignment n),
        clean (Function.update β (qs r) b) ↔ clean β) →
      (xReset m qs g).eval.1 * P = P * (xReset m qs g).eval.1
  | 0, _, _, _ => by simp [xReset]
  | m + 1, qs, g, hupd => by
      have h0 : (if g 0 then Circuit.X (qs 0) else .identity).eval.1 * P =
          P * (if g 0 then Circuit.X (qs 0) else .identity).eval.1 := by
        cases g 0
        · simp
        · rw [ite_eq_left rfl]
          apply matrix_ext_ket
          intro β
          rw [mul_mulVec_prog, mul_mulVec_prog, hP_ket, ket_X, hP_ket]
          by_cases hc : clean β
          · rw [ite_eq_left hc, ite_eq_left ((hupd 0 _ β).mpr hc), ket_X]
          · rw [ite_eq_right hc, ite_eq_right (mt (hupd 0 _ β).mp hc), Matrix.mulVec_zero]
      simp only [xReset, Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, h0, ← Matrix.mul_assoc,
        fmkXReset_comm_diag hP_ket m _ _ (fun r b β ↦ hupd r.succ b β), Matrix.mul_assoc]
theorem fmkHadamardAll_comm_diag {n : ℕ}
    {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {clean : BitAssignment n → Prop}
    (hP_ket : ∀ β, P.mulVec (ket β) = if clean β then ket β else 0) :
    ∀ (m : ℕ) (qs : Fin m → Wire n), (∀ (r : Fin m) (b : ZMod 2) (β : BitAssignment n),
        clean (Function.update β (qs r) b) ↔ clean β) →
      (hadamardAll m qs).eval.1 * P = P * (hadamardAll m qs).eval.1
  | 0, _, _ => by simp [hadamardAll]
  | m + 1, qs, hupd => by
      have h0 : (Circuit.H (qs 0)).eval.1 * P = P * (Circuit.H (qs 0)).eval.1 := by
        apply matrix_ext_ket
        intro β
        rw [mul_mulVec_prog, mul_mulVec_prog, hP_ket, ket_H,
          Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hP_ket, hP_ket]
        by_cases hc : clean β
        · rw [ite_eq_left hc, ite_eq_left ((hupd 0 0 β).mpr hc),
          ite_eq_left ((hupd 0 1 β).mpr hc), ket_H]
        · rw [ite_eq_right hc, ite_eq_right (mt (hupd 0 0 β).mp hc),
          ite_eq_right (mt (hupd 0 1 β).mp hc), Matrix.mulVec_zero, smul_zero, add_zero, smul_zero]
      simp only [hadamardAll, Circuit.eval_seq, Submonoid.coe_mul]
      rw [Matrix.mul_assoc, h0, ← Matrix.mul_assoc,
        fmkHadamardAll_comm_diag hP_ket m _ (fun r b β ↦ hupd r.succ b β), Matrix.mul_assoc]
theorem fmkWriteSynd_pres_clean {n : ℕ} {clean : BitAssignment n → Prop} :
    ∀ (m : ℕ) (qs : Fin m → Wire n) (y : Fin m → Bool) (β : BitAssignment n),
      (∀ (r : Fin m) (b : ZMod 2) (γ : BitAssignment n),
        clean (Function.update γ (qs r) b) ↔ clean γ) → clean β → clean (writeSynd m qs y β)
  | 0, _, _, _, _, hβ => hβ
  | m + 1, qs, y, β, hupd, hβ =>
      fmkWriteSynd_pres_clean m (fun i ↦ qs i.succ) (fun i ↦ y i.succ)
        (Function.update β (qs 0) (if y 0 then 1 else 0))
        (fun r b γ ↦ hupd r.succ b γ) ((hupd 0 _ β).mpr hβ)
theorem fmkWriteRegProg_idem {k n : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ₁ γ₂ : BitAssignment k) : writeRegProg (writeRegProg β r γ₁) r γ₂ = writeRegProg β r γ₂ := by
  funext w
  by_cases hmem : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hmem
    simp [writeRegProg_apply_reg]
  · simp [writeRegProg_apply_of_not_mem _ _ _ _ hmem]
end
end Dyn_FastMidKick275
end FastMidKick275Aux
end
end ModFastMidKick275

end QuantumComputation.Specs.StoppingPowerSolution
