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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.TempPhaseProgCore
set_option Elab.async false

@[expose] public section
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModSlot3MicroEngine
@[expose] public section
namespace Slot3MicroEngineAux
section ConfigSlot3MicroEngine
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 512
local instance (priority := 1000000) instNeZeroTwoPowS3M (k : Nat) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real LocalClassicalPerm
open MeasureBranchHadamardSem (bit_cases)
open scoped Matrix BigOperators
theorem s3mItePos {c : Prop} [h : Decidable c] {α : Sort _} (hc : c) {t e : α} : ite c t e = t :=
  match h with | isTrue _ => rfl | isFalse hn => absurd hc hn
theorem s3mIteNeg {c : Prop} [h : Decidable c] {α : Sort _} (hnc : ¬ c) {t e : α} : ite c t e = e :=
  match h with | isFalse _ => rfl | isTrue hc => absurd hc hnc
theorem s3mDitePos {c : Prop} [h : Decidable c] {α : Sort _} (hc : c) {t : c → α} {e : ¬ c → α} :
    dite c t e = t hc := match h with | isTrue _ => rfl | isFalse hn => absurd hc hn
theorem s3mDiteNeg {c : Prop} [h : Decidable c] {α : Sort _} (hnc : ¬ c) {t : c → α} {e : ¬ c → α} :
    dite c t e = e hnc := match h with | isFalse _ => rfl | isTrue hc => absurd hc hnc
theorem s3mLtTrans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h1 h2
theorem s3mLtLe {a b c : ℕ} (h1 : a < b) (h2 : b ≤ c) : a < c := Nat.lt_of_lt_of_le h1 h2
def s3mTop7Mu (t : ℕ) : ℕ := if t < 2 then 0 else if t < 4 then 1 else if t < 8 then 2 else if
    t < 16 then 3 else if t < 32 then 4 else if t < 64 then 5 else 6
theorem bitsVal_succ_split {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
    bitsVal f = (f 0).val + 2 * bitsVal (fun j ↦ f j.succ) := by
  rw [bitsVal, Fin.sum_univ_succ]
  simp only [Fin.val_zero, _root_.pow_zero, mul_one, bitsVal, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ by rw [Fin.val_succ, pow_succ]; ring)
theorem bitsVal_injective : ∀ {W : ℕ}, Function.Injective (bitsVal (q := W))
  | 0, _, _, _ => funext fun i ↦ Fin.elim0 i
  | W + 1, f, g, h => by
      rw [bitsVal_succ_split f, bitsVal_succ_split g] at h
      have hf0 := ZMod.val_lt (f 0)
      have hg0 := ZMod.val_lt (g 0)
      have htail : (fun j : Fin W ↦ f j.succ) = fun j ↦ g j.succ :=
        bitsVal_injective (by omega)
      exact funext (Fin.cases (ZMod.val_injective 2 (by omega)) (congrFun htail))
theorem bitsVal_eq_of_testBit {W : ℕ} (f : Fin W → ZMod 2) (v : ℕ) (hv : v < 2 ^ W)
    (h : ∀ j : Fin W, f j = if v.testBit j.val then 1 else 0) : bitsVal f = v := by
  induction W generalizing v with
  | zero => simp [bitsVal, show v = 0 by omega]
  | succ W ih =>
      have h0 := h 0
      simp only [Fin.val_zero, Nat.testBit_zero] at h0
      rw [bitsVal_succ_split, ih (fun j ↦ f j.succ) (v / 2) (by rw [pow_succ'] at hv; omega)
        (fun j ↦ by rw [h j.succ, Fin.val_succ, Nat.testBit_succ]), h0]
      by_cases hb : v % 2 = 1
      · simp only [hb, decide_true, ↓reduceIte, ZMod.val_one]; omega
      · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte, ZMod.val_zero]; omega
def cnotVec {M : ℕ} : (W : ℕ) → (src dst : Fin W → Wire M) → (∀ j, src j ≠ dst j) → CliffProg M
  | 0, _, _, _ => .nil
  | W + 1, src, dst, hne => .seq (.cnot (src 0) (dst 0) (hne 0))
      (cnotVec W (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem cnotVec_eval {M : ℕ} :
    ∀ (W : ℕ) (src dst : Fin W → Wire M) (hne : ∀ j, src j ≠ dst j)
      (_ : Function.Injective dst) (_ : ∀ i j, src i ≠ dst j)
      (β : BitAssignment M) (w : Wire M),
      (cnotVec W src dst hne).eval β w =
        if h : ∃ j, w = dst j then β w + β (src h.choose) else β w
  | 0, _, _, _, _, _, _, _ => by simp [cnotVec, CliffProg.eval]
  | W + 1, src, dst, hne, hinj, hdisj, β, w => by
      dsimp only [cnotVec, CliffProg.eval]
      let β₁ := Function.update β (dst 0) (β (dst 0) + β (src 0))
      have hsrc₁ : ∀ j : Fin W, β₁ (src j.succ) = β (src j.succ) := fun j ↦
        Function.update_of_ne (hdisj j.succ 0) _ _
      rw [cnotVec_eval W (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ)
        (hinj.comp (Fin.succ_injective W)) (fun i j ↦ hdisj i.succ j.succ) β₁ w]
      by_cases hs : ∃ j : Fin W, w = dst j.succ
      · have hall : ∃ i : Fin (W + 1), w = dst i := ⟨hs.choose.succ, hs.choose_spec⟩
        have hw₁ : β₁ w = β w := hs.choose_spec ▸
          Function.update_of_ne (fun h ↦ Fin.succ_ne_zero _ (hinj h)) _ _
        simp only [hs, hall, ↓reduceDIte, hw₁, hsrc₁,
          hinj (hall.choose_spec.symm.trans hs.choose_spec)]
      · by_cases h0 : w = dst 0
        · subst h0
          have hall : ∃ i : Fin (W + 1), dst 0 = dst i := ⟨0, rfl⟩
          simp only [hs, hall, ↓reduceDIte, β₁, Function.update_self, hinj hall.choose_spec.symm]
        · have hall : ¬ ∃ i : Fin (W + 1), w = dst i :=
            fun ⟨i, hi⟩ ↦ Fin.cases (motive := fun i ↦ w = dst i → False) h0
              (fun j hj ↦ hs ⟨j, hj⟩) i hi
          simp only [hs, hall, ↓reduceDIte, β₁, Function.update_of_ne h0]
theorem TempCtx.fwdBits_mut {M : ℕ} {mutW : Wire M → Prop}
    {K : TempCtx M} (hDisj : K.DisjointFrom mutW) :
    ∀ (β : BitAssignment M) {w : Wire M}, mutW w → K.fwdBits β w = β w := by
  intro β w hw
  induction K generalizing β with
  | hole => rfl
  | seqPre c _ ih => exact (ih hDisj.2 (c.eval β)).trans (hDisj.1.eval_mut β hw)
  | seqPost _ _ ih => exact ih hDisj.1 β
  | tempAnd _ _ anc _ _ _ _ ih =>
      exact (ih hDisj.2.2.2 _).trans
        (Function.update_of_ne (fun (h : w = anc) ↦ hDisj.2.2.1 (h ▸ hw)) _ _)
theorem TempCtx.supportsBelowCtx_mono {M b₁ b₂ : ℕ} (hle : b₁ ≤ b₂) {K : TempCtx M} :
    K.SupportsBelowCtx b₁ → K.SupportsBelowCtx b₂ := by
  induction K with
  | hole => exact id
  | seqPre _ _ ih => exact fun h ↦ ⟨CliffProg.supportsBelow_mono hle h.1, ih h.2⟩
  | seqPost _ _ ih => exact fun h ↦ ⟨ih h.1, CliffProg.supportsBelow_mono hle h.2⟩
  | tempAnd _ _ _ _ _ _ _ ih => exact fun h ↦ ⟨Nat.lt_of_lt_of_le h.1 hle, ih h.2⟩
theorem TempCtx.append_countTempAnd {M : ℕ} (F G : TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd := by
  induction F with
  | hole => simp [TempCtx.append, TempCtx.countTempAnd]
  | seqPre _ _ ih | seqPost _ _ ih => exact ih
  | tempAnd _ _ _ _ _ _ _ ih => dsimp [TempCtx.append, TempCtx.countTempAnd]; omega
theorem TempCtx.append_fwdBits {M : ℕ} (F G : TempCtx M) (β : BitAssignment M) :
    (F.append G).fwdBits β = G.fwdBits (F.fwdBits β) := by
  induction F generalizing β with
  | hole => rfl
  | seqPre c _ ih => exact ih (c.eval β)
  | seqPost _ _ ih | tempAnd _ _ _ _ _ _ _ ih => exact ih _
theorem TempCtx.scopedBlock_fwdBits {M rem : ℕ} (K : TempCtx M)
    (hEx : ∀ q : Wire M, ∃ sQ, ScopedBlock M rem sQ (.z q) (K.plug (.z q))) (q : Wire M) :
    ScopedBlock M rem K.fwdBits (.z q) (K.plug (.z q)) :=
  ⟨(hEx q).choose_spec.valid, (hEx q).choose_spec.bits, fun β _ ↦ K.plug_evalSign (.z q) β⟩
theorem TempCtx.fwdBits_eq_of_block {M rem : ℕ} (K : TempCtx M) (u : Wire M)
    {sU : BitAssignment M → BitAssignment M}
    (hBlk : ScopedBlock M rem sU (.z u) (K.plug (.z u))) (β : BitAssignment M)
    (hβ : cleanRem M rem β) : K.fwdBits β u = sU β u :=
  (K.plug_evalSign (.z u) β).symm.trans (hBlk.sign β hβ)
def TempCtxLiftEx {M : ℕ} (cur next : ℕ) (K : TempCtx M) : Prop :=
  ∀ {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M},
    ScopedBlock M (M - next) sBody leaf body →
    ∃ sOut, ScopedBlock M (M - cur) sOut leaf (K.plug body)
theorem TempCtxLiftEx.probe {M cur next : ℕ} {K : TempCtx M}
    (hK : TempCtxLiftEx cur next K) (q : Wire M) :
    ScopedBlock M (M - cur) K.fwdBits (.z q) (K.plug (.z q)) :=
  TempCtx.scopedBlock_fwdBits K (fun q ↦ hK (ScopedBlock.z_kick q)) q
private theorem ScopedBlock.mono_rem {M r₀ r₁ : ℕ} (hle : r₀ ≤ r₁)
    {s : BitAssignment M → BitAssignment M} {leaf prog : TempPhaseProg M}
    (h : ScopedBlock M r₀ s leaf prog) : ScopedBlock M r₁ s leaf prog :=
  ⟨validCleanRem_mono hle h.valid, fun β hβ ↦ h.bits β (cleanRem_anti hle hβ),
    fun β hβ ↦ h.sign β (cleanRem_anti hle hβ)⟩
theorem TempCtxLiftEx.mono {M cur₀ cur₁ next₀ next₁ : ℕ} {K : TempCtx M}
    (hK : TempCtxLiftEx cur₁ next₀ K)
    (hc : cur₀ ≤ cur₁) (hn : next₀ ≤ next₁) (hM : next₁ ≤ M) :
    TempCtxLiftEx cur₀ next₁ K := fun hBody ↦
  let ⟨sOut, hOut⟩ := hK (ScopedBlock.mono_rem (by omega) hBody)
  ⟨sOut, ScopedBlock.mono_rem (by omega) hOut⟩
theorem TempCtxLiftEx.append {M cur mid next : ℕ} {F G : TempCtx M}
    (hF : TempCtxLiftEx cur mid F) (hG : TempCtxLiftEx mid next G) :
    TempCtxLiftEx cur next (F.append G) := fun hBody ↦ by
  obtain ⟨_, h1⟩ := hG hBody
  obtain ⟨sOut, h2⟩ := hF h1
  exact ⟨sOut, by rwa [TempCtx.append_plug]⟩
theorem TempCtxLiftEx.cliff {M : ℕ} (cur : ℕ) (hcur : cur ≤ M) (c : CliffProg M)
    (hc : c.SupportsBelow cur) : TempCtxLiftEx cur cur (ctxCliffAlloc c) :=
  fun {leaf body sBody} hBody ↦ ⟨sBody ∘ c.eval, by
    rw [ctxCliffAlloc_plug]
    exact ScopedBlock.withCliffAlloc_block (by omega) le_rfl c
      (CliffProg.supportsBelow_mono (by omega) hc) hBody⟩
theorem TempCtxLiftEx.tempBit {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) : TempCtxLiftEx cur (cur + 1)
    (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2)) :=
  fun {leaf body sBody} hBody ↦ ⟨fun β ↦ sBody (Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂)), by
    rw [ctxTempBit_plug]
    exact ScopedBlock.withTempBit_block cur hcur c₁ c₂ h12 hc1 hc2 hBody⟩
theorem ctxCliffAlloc_fwdBits {M : ℕ} (cur : ℕ) (hcur : cur ≤ M) (c : CliffProg M)
    (hc : c.SupportsBelow cur) (β : BitAssignment M) (hβ : cleanRem M (M - cur) β) :
    (ctxCliffAlloc c).fwdBits β = c.eval β :=
  funext fun u ↦ TempCtx.fwdBits_eq_of_block (ctxCliffAlloc c) u
    (by rw [ctxCliffAlloc_plug]
        exact ScopedBlock.withCliffAlloc_block (by omega) le_rfl c
          (CliffProg.supportsBelow_mono (by omega) hc) (ScopedBlock.z_kick u)) β hβ
theorem ctxTempBit_fwdBits_clean {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) (β : BitAssignment M)
    (hβ : cleanRem M (M - cur) β) : (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1)
    (wire_ne_of_lt hc2)).fwdBits β = Function.update β ⟨cur, hcur⟩ (β c₁ * β c₂) :=
  funext fun u ↦ TempCtx.fwdBits_eq_of_block _ u
    (by rw [ctxTempBit_plug]
        exact ScopedBlock.withTempBit_block cur hcur c₁ c₂ h12 hc1 hc2 (ScopedBlock.z_kick u)) β hβ
theorem xorBlock_of_ctx {M curStart curEnd W : ℕ} [NeZero M]
    (hEnd : curEnd ≤ M) (hStart : curStart ≤ curEnd)
    (out : Fin W → Wire M) (hout_lt : ∀ j, (out j).val < curStart)
    (hout_inj : Function.Injective out)
    (src : Fin W → Wire M) (hsrc_ge : ∀ j, curStart ≤ (src j).val)
    (K : TempCtx M) (hDisj : K.DisjointFrom (fun w ↦ ∃ j, w = out j))
    (hSupp : K.SupportsBelowCtx curEnd) (setup : BitAssignment M → BitAssignment M)
    (hProbe : ∀ q : Wire M, ScopedBlock M (M - curStart) setup (.z q) (K.plug (.z q))) :
    let hne : ∀ j, src j ≠ out j := fun j ↦ wire_ne_of_gt (s3mLtLe (hout_lt j) (hsrc_ge j))
    let p := K.plug (.cliff (cnotVec W src out hne))
    ValidCleanRem M (M - curStart) p ∧ p.countTempAnd = K.countTempAnd ∧
      (∀ β : BitAssignment M, cleanRem M (M - curStart) β → p.evalSign β = 0) ∧
      (∀ β : BitAssignment M, cleanRem M (M - curStart) β → ∀ w : Wire M,
        p.evalBits β w = if h : ∃ j, w = out j then β w + setup β (src h.choose) else β w) := by
  have hdisj_so : ∀ i j, src i ≠ out j := fun i j ↦ wire_ne_of_gt (s3mLtLe (hout_lt j) (hsrc_ge i))
  obtain ⟨hVal, hCnt, hSgn, hBits⟩ := ScopedBlock.graft_mutating_body (M := M) (rem := M - curStart)
    (curHole := curEnd) (fun w ↦ ∃ j, w = out j) K hDisj hSupp (by omega) setup hProbe
    (.cliff (cnotVec W src out fun j ↦ hdisj_so j j)) trivial fun γ w hnw ↦ by
      simp [TempPhaseProg.evalBits, cnotVec_eval W src out _ hout_inj hdisj_so γ w, hnw]
  refine ⟨hVal, by dsimp only [TempPhaseProg.countTempAnd] at hCnt; omega,
    fun β hβ ↦ by simpa [TempPhaseProg.evalSign] using hSgn β hβ, fun β hβ w ↦ ?_⟩
  rw [hBits β hβ w]
  by_cases hw : ∃ j, w = out j
  · simp only [hw, ↓reduceIte, TempPhaseProg.evalBits,
      cnotVec_eval W src out _ hout_inj hdisj_so (setup β) w, ↓reduceDIte,
      ← TempCtx.fwdBits_eq_of_block K w (hProbe w) β hβ, TempCtx.fwdBits_mut hDisj β hw]
  · simp [hw]
def ctxLtStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev) : TempCtx M :=
  let out : Wire M := ⟨cur, by omega⟩
  (ctxCliffAlloc (.seq (.cnot b a hab.symm) (.cnot prev b hbp.symm))).append
    ((ctxTempBit a b out hab (wire_ne_of_lt (by dsimp [out]; omega))
        (wire_ne_of_lt (by dsimp [out]; omega))).append
      (ctxCliffAlloc (.seq (.cnot prev b hbp.symm)
        (.seq (.cnot b a hab.symm) (.cnot prev out (wire_ne_of_lt (by dsimp [out]; omega)))))))
theorem ctxLtStep_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M)
    (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev)
    (body : TempPhaseProg M) : (ctxLtStep cur hcur a b prev hab ha hb hp hbp).plug body =
    withLtStep cur hcur a b prev hab ha hb hp hbp body := by
  simp only [ctxLtStep, withLtStep, TempCtx.append_plug, ctxCliffAlloc_plug, ctxTempBit_plug]
def ctxLtCompLoop {M : ℕ} : (W cur : ℕ) → (hcur : cur + W + 1 ≤ M) → (a b : Fin W → Wire M) →
    (hab : ∀ j, a j ≠ b j) → (ha : ∀ j, (a j).val < cur) → (hb : ∀ j, (b j).val < cur) → TempCtx M
  | 0, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, hcur, a, b, hab, ha, hb =>
      let prev : Wire M := ⟨cur, by omega⟩
      (ctxLtStep (cur + 1) (by omega) (a 0) (b 0) prev (hab 0)
        (s3mLtTrans (ha 0) (by omega)) (s3mLtTrans (hb 0) (by omega)) (by dsimp [prev]; omega)
        (wire_ne_of_lt (by have := hb 0; dsimp [prev]; omega))).append
        (ctxLtCompLoop W (cur + 1) (by omega) (fun j ↦ a j.succ) (fun j ↦ b j.succ)
          (fun j ↦ hab j.succ) (fun j ↦ s3mLtTrans (ha j.succ) (by omega))
          (fun j ↦ s3mLtTrans (hb j.succ) (by omega)))
theorem ctxLtCompLoop_plug {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (body : TempPhaseProg M),
      (ctxLtCompLoop W cur hcur a b hab ha hb).plug body =
        withLtCompLoop W cur hcur a b hab ha hb body
  | 0, _, _, _, _, _, _, _, _ => rfl
  | W + 1, _, _, _, _, _, _, _, _ => by
      dsimp only [ctxLtCompLoop, withLtCompLoop]
      rw [TempCtx.append_plug, ctxLtStep_plug, ctxLtCompLoop_plug]
theorem ctxLtCompLoop_countTempAnd {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j) (ha : ∀ j, (a j).val < cur)
    (hb : ∀ j, (b j).val < cur) : (ctxLtCompLoop W cur hcur a b hab ha hb).countTempAnd = W := by
  have h1 := TempCtx.plug_countTempAnd (ctxLtCompLoop W cur hcur a b hab ha hb) .nil
  rw [ctxLtCompLoop_plug, withLtCompLoop_countTempAnd] at h1
  dsimp [TempPhaseProg.countTempAnd] at h1
  omega
theorem TempCtx.fwdBits_outside {M B : ℕ} {K : TempCtx M} (hSupp : K.SupportsBelowCtx B) :
    ∀ (β : BitAssignment M) (w : Wire M), B ≤ w.val → K.fwdBits β w = β w := by
  induction K with
  | hole => exact fun _ _ _ ↦ rfl
  | seqPre c _ ih =>
      exact fun β w hw ↦ (ih hSupp.2 (c.eval β) w hw).trans (c.eval_outside hSupp.1 β w hw)
  | seqPost _ _ ih => exact fun β w hw ↦ ih hSupp.1 β w hw
  | tempAnd _ _ _ _ _ _ _ ih =>
      exact fun β w hw ↦ (ih hSupp.2 _ w hw).trans
        (Function.update_of_ne (wire_ne_of_gt (s3mLtLe hSupp.1 hw)) _ _)
theorem TempCtx.cleanRem_of_supports {M : ℕ} (cur next : ℕ) {K : TempCtx M}
    (hle : cur ≤ next) (hSupp : K.SupportsBelowCtx next)
    {β : BitAssignment M} (hβ : cleanRem M (M - cur) β) :
    cleanRem M (M - next) (K.fwdBits β) := fun w hw ↦ by
  rw [TempCtx.fwdBits_outside hSupp β w (by omega)]
  exact hβ w (by omega)
theorem ctxLtStep_props {M : ℕ} {mutW : Wire M → Prop}
    (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev)
    (hna : ¬ mutW a) (hnb : ¬ mutW b) (hnp : ¬ mutW prev) (hno : ¬ mutW ⟨cur, by omega⟩) :
    (ctxLtStep cur hcur a b prev hab ha hb hp hbp).DisjointFrom mutW ∧
    (ctxLtStep cur hcur a b prev hab ha hb hp hbp).SupportsBelowCtx (cur + 1) := by
  dsimp only [ctxLtStep]
  exact ⟨TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint ⟨⟨hnb, hna⟩, ⟨hnp, hnb⟩⟩)
    (TempCtx.disjointFrom_append ⟨hna, hnb, hno, trivial⟩
      (ctxCliffAlloc_disjoint ⟨⟨hnp, hnb⟩, ⟨hnb, hna⟩, ⟨hnp, hno⟩⟩)),
    TempCtx.supportsBelowCtx_append le_rfl
      (ctxCliffAlloc_supports ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩)
      (TempCtx.supportsBelowCtx_append le_rfl ⟨by dsimp; omega, trivial⟩
        (ctxCliffAlloc_supports
          ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by dsimp; omega⟩⟩))⟩
theorem ctxLtCompLoop_props {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur),
      (∀ j, ¬ mutW (a j)) → (∀ j, ¬ mutW (b j)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      (ctxLtCompLoop W cur hcur a b hab ha hb).DisjointFrom mutW ∧
      (ctxLtCompLoop W cur hcur a b hab ha hb).SupportsBelowCtx (cur + W + 1)
  | 0, _, _, _, _, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | W + 1, cur, hcur, a, b, hab, ha, hb, hna, hnb, hncur => by
      obtain ⟨hd0, hs0⟩ := ctxLtStep_props (mutW := mutW) (cur + 1) (by omega)
        (a 0) (b 0) ⟨cur, by omega⟩ (hab 0) (s3mLtTrans (ha 0) (by omega))
        (s3mLtTrans (hb 0) (by omega)) (by dsimp; omega)
        (wire_ne_of_lt (by have := hb 0; dsimp; omega)) (hna 0) (hnb 0)
        (hncur _ (by dsimp; omega)) (hncur _ (by dsimp; omega))
      obtain ⟨hdR, hsR⟩ := ctxLtCompLoop_props (mutW := mutW) W (cur + 1) (by omega)
        (fun j ↦ a j.succ) (fun j ↦ b j.succ) (fun j ↦ hab j.succ)
        (fun j ↦ s3mLtTrans (ha j.succ) (by omega)) (fun j ↦ s3mLtTrans (hb j.succ) (by omega))
        (fun j ↦ hna j.succ) (fun j ↦ hnb j.succ) (fun w hw ↦ hncur w (by omega))
      exact ⟨TempCtx.disjointFrom_append hd0 hdR,
        TempCtx.supportsBelowCtx_append (by omega) hs0 (TempCtx.supportsBelowCtx_mono (by omega)
          hsR)⟩
theorem TempCtxLiftEx.ltCompLoop {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) :
    TempCtxLiftEx cur (cur + W + 1) (ctxLtCompLoop W cur hcur a b hab ha hb) :=
  fun {leaf body sBody} hBody ↦ by
    obtain ⟨s, h, _⟩ :=
      ScopedBlock.withLtCompLoop_block W cur hcur a b hab ha hb leaf body sBody hBody
    rw [← ctxLtCompLoop_plug] at h
    exact ⟨fun β ↦ sBody (s β), ScopedBlock.mono_rem (by omega) h⟩
theorem ctxLtCompLoop_scoped {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) :
    let K := ctxLtCompLoop W cur hcur a b hab ha hb
    TempCtxLiftEx cur (cur + W + 1) K ∧
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      cleanRem M (M - (cur + W + 1)) (K.fwdBits β) ∧
      ((K.fwdBits β ⟨cur + W, by omega⟩ = 1) ↔
        bitsVal (fun j ↦ β (a j)) < bitsVal (fun j ↦ β (b j)))) := by
  intro K
  refine ⟨TempCtxLiftEx.ltCompLoop W cur hcur a b hab ha hb, fun β hβ ↦
    ⟨TempCtx.cleanRem_of_supports cur (cur + W + 1) (by omega)
      (ctxLtCompLoop_props (mutW := fun _ ↦ False) W cur hcur a b hab ha hb
        (fun _ ↦ id) (fun _ ↦ id) (fun _ _ ↦ id)).2 hβ, ?_⟩⟩
  obtain ⟨_, hBlkU, hSpecU⟩ := ScopedBlock.withLtCompLoop_block W cur hcur a b hab ha hb
    (.z ⟨cur + W, by omega⟩) (.z ⟨cur + W, by omega⟩) id (ScopedBlock.z_kick ⟨cur + W, by omega⟩)
  rw [← ctxLtCompLoop_plug] at hBlkU
  have hβ1 : cleanRem M (M - (cur + 1)) β := cleanRem_anti (by omega) hβ
  rw [TempCtx.fwdBits_eq_of_block K ⟨cur + W, by omega⟩ hBlkU β hβ1]
  simpa [hβ ⟨cur, by omega⟩ (by dsimp; omega)] using (hSpecU β hβ1).2.2
def ctxAndPairs {M : ℕ} : (len cur : ℕ) → (hcur : cur + len ≤ M) → (lhs rhs : Fin len → Wire M) →
    (hne : ∀ i, lhs i ≠ rhs i) → (hl : ∀ i, (lhs i).val < cur) → (hr : ∀ i, (rhs i).val < cur) →
    TempCtx M
  | 0, _, _, _, _, _, _, _ => .hole
  | len + 1, cur, hcur, lhs, rhs, hne, hl, hr =>
      .tempAnd (lhs 0) (rhs 0) ⟨cur, by omega⟩ (hne 0) (wire_ne_of_lt (hl 0)) (wire_ne_of_lt (hr 0))
        (ctxAndPairs len (cur + 1) (by omega) (fun i ↦ lhs i.succ) (fun i ↦ rhs i.succ)
          (fun i ↦ hne i.succ) (fun i ↦ s3mLtTrans (hl i.succ) (by omega))
          (fun i ↦ s3mLtTrans (hr i.succ) (by omega)))
theorem ctxAndPairs_countTempAnd {M : ℕ} :
    ∀ (len cur : ℕ) (hcur : cur + len ≤ M) (lhs rhs : Fin len → Wire M)
      (hne : ∀ i, lhs i ≠ rhs i) (hl : ∀ i, (lhs i).val < cur) (hr : ∀ i, (rhs i).val < cur),
      (ctxAndPairs len cur hcur lhs rhs hne hl hr).countTempAnd = len
  | 0, _, _, _, _, _, _, _ => rfl
  | len + 1, cur, _, lhs, rhs, hne, hl, hr => by
      simp only [ctxAndPairs, TempCtx.countTempAnd, ctxAndPairs_countTempAnd len (cur + 1)]
      omega
theorem ctxAndPairs_props {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (len cur : ℕ) (hcur : cur + len ≤ M) (lhs rhs : Fin len → Wire M)
      (hne : ∀ i, lhs i ≠ rhs i) (hl : ∀ i, (lhs i).val < cur) (hr : ∀ i, (rhs i).val < cur),
      (∀ i, ¬ mutW (lhs i)) → (∀ i, ¬ mutW (rhs i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      (ctxAndPairs len cur hcur lhs rhs hne hl hr).DisjointFrom mutW ∧
      (ctxAndPairs len cur hcur lhs rhs hne hl hr).SupportsBelowCtx (cur + len)
  | 0, _, _, _, _, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | len + 1, cur, _, lhs, rhs, hne, hl, hr, hnl, hnr, hncur => by
      obtain ⟨hd, hs⟩ := ctxAndPairs_props len (cur + 1) (by omega) (fun i ↦ lhs i.succ)
        (fun i ↦ rhs i.succ) (fun i ↦ hne i.succ) (fun i ↦ s3mLtTrans (hl i.succ) (by omega))
        (fun i ↦ s3mLtTrans (hr i.succ) (by omega)) (fun i ↦ hnl i.succ) (fun i ↦ hnr i.succ)
        (fun w hw ↦ hncur w (by omega))
      dsimp only [ctxAndPairs, TempCtx.DisjointFrom, TempCtx.SupportsBelowCtx]
      exact ⟨⟨hnl 0, hnr 0, hncur ⟨cur, by omega⟩ le_rfl, hd⟩,
        Nat.lt_add_of_pos_right (Nat.succ_pos len), TempCtx.supportsBelowCtx_mono (by omega) hs⟩
theorem ctxAndPairs_scoped {M : ℕ} :
    ∀ (len cur : ℕ) (hcur : cur + len ≤ M)
      (lhs rhs : Fin len → Wire M) (hne : ∀ i, lhs i ≠ rhs i)
      (hl : ∀ i, (lhs i).val < cur) (hr : ∀ i, (rhs i).val < cur),
      let K := ctxAndPairs len cur hcur lhs rhs hne hl hr
      TempCtxLiftEx cur (cur + len) K ∧
      (∀ β : BitAssignment M, cleanRem M (M - cur) β →
        cleanRem M (M - (cur + len)) (K.fwdBits β) ∧
        (∀ w : Wire M, w.val < cur → K.fwdBits β w = β w) ∧
        (∀ i : Fin len, K.fwdBits β ⟨cur + i.val, by omega⟩ = β (lhs i) * β (rhs i)))
  | 0, _, _, _, _, _, _, _ =>
      ⟨fun h ↦ ⟨_, h⟩, fun _ hβ ↦ ⟨hβ, fun _ _ ↦ rfl, fun i ↦ Fin.elim0 i⟩⟩
  | len + 1, cur, hcur, lhs, rhs, hne, hl, hr => by
      dsimp only
      obtain ⟨hLiftR, hSpecR⟩ := ctxAndPairs_scoped len (cur + 1) (by omega)
        (fun i ↦ lhs i.succ) (fun i ↦ rhs i.succ) (fun i ↦ hne i.succ)
        (fun i ↦ s3mLtTrans (hl i.succ) (by omega))
        (fun i ↦ s3mLtTrans (hr i.succ) (by omega))
      refine ⟨fun hBody ↦ let ⟨_, hI⟩ := TempCtxLiftEx.mono hLiftR le_rfl (by omega) hcur hBody
        TempCtxLiftEx.tempBit (M := M) cur (by omega) (lhs 0) (rhs 0) (hne 0) (hl 0) (hr 0) hI,
        fun β hβ ↦ ?_⟩
      have hcur0 : β ⟨cur, by omega⟩ = 0 := hβ ⟨cur, by omega⟩ (by dsimp; omega)
      set β₁ := Function.update β ⟨cur, by omega⟩ (β ⟨cur, by omega⟩ + β (lhs 0) * β (rhs 0))
      obtain ⟨hclOut, hbelow, hpair⟩ := hSpecR β₁ fun w hw ↦
        (Function.update_of_ne (wire_ne_of_gt (by dsimp; omega)) _ _).trans (hβ w (by omega))
      dsimp only [ctxAndPairs, TempCtx.fwdBits]
      refine ⟨cleanRem_anti (by omega) hclOut,
        fun w hw ↦ (hbelow w (by omega)).trans (Function.update_of_ne (wire_ne_of_lt hw) _ _),
        fun i ↦ ?_⟩
      cases i using Fin.cases with
      | zero =>
          change (ctxAndPairs len (cur + 1) _ _ _ _ _ _).fwdBits β₁ ⟨cur, by omega⟩ = _
          rw [hbelow ⟨cur, by omega⟩ (by dsimp; omega)]
          exact (Function.update_self _ _ _).trans (by rw [hcur0, zero_add])
      | succ j =>
          rw [show (⟨cur + j.succ.val, by omega⟩ : Wire M) = ⟨cur + 1 + j.val, by omega⟩ from
            Fin.ext (by dsimp; omega), hpair j]
          simp [β₁, Function.update_of_ne (wire_ne_of_lt (hl j.succ) : lhs j.succ ≠ ⟨cur, by
            omega⟩),
            Function.update_of_ne (wire_ne_of_lt (hr j.succ) : rhs j.succ ≠ ⟨cur, by omega⟩)]
def cnotFoldIntoBase {M : ℕ} (base : ℕ) : (K : ℕ) → base + K + 1 ≤ M → CliffProg M
  | 0, _ => .nil
  | K + 1, hM =>
      .seq (cnotFoldIntoBase base K (by omega))
        (.cnot ⟨base + (K + 1), by omega⟩ ⟨base, by omega⟩ (wire_ne_of_gt (by dsimp; omega)))
theorem cnotFoldIntoBase_supportsBelow {M bound : ℕ} (base : ℕ) :
    ∀ (K : ℕ) (hM : base + K + 1 ≤ M), base + K + 1 ≤ bound →
      (cnotFoldIntoBase base K hM).SupportsBelow bound
  | 0, _, _ => trivial
  | K + 1, _, hb =>
      ⟨cnotFoldIntoBase_supportsBelow base K (by omega) (by omega),
        by dsimp; omega, by dsimp; omega⟩
theorem cnotFoldIntoBase_disjoint {M : ℕ} {mutW : Wire M → Prop} (base : ℕ)
    (hnb : ∀ w : Wire M, base ≤ w.val → ¬ mutW w) :
    ∀ (K : ℕ) (hM : base + K + 1 ≤ M), CliffDisjoint mutW (cnotFoldIntoBase base K hM)
  | 0, _ => trivial
  | K + 1, _ =>
      ⟨cnotFoldIntoBase_disjoint base hnb K (by omega),
        hnb _ (by dsimp; omega), hnb _ (by dsimp; omega)⟩
theorem cnotFoldIntoBase_eval {M : ℕ} (base : ℕ) :
    ∀ (K : ℕ) (hM : base + K + 1 ≤ M) (γ : BitAssignment M),
      (∀ w : Wire M, w ≠ ⟨base, by omega⟩ → (cnotFoldIntoBase base K hM).eval γ w = γ w) ∧
      (cnotFoldIntoBase base K hM).eval γ ⟨base, by omega⟩ =
        ∑ i : Fin (K + 1), γ ⟨base + i.val, by omega⟩
  | 0, _, γ => ⟨fun _ _ ↦ rfl, by simp [cnotFoldIntoBase, CliffProg.eval]⟩
  | K + 1, _, γ => by
      obtain ⟨hOther, hBase⟩ := cnotFoldIntoBase_eval base K (by omega) γ
      dsimp only [cnotFoldIntoBase, CliffProg.eval]
      refine ⟨fun w hw ↦ (Function.update_of_ne hw _ _).trans (hOther w hw), ?_⟩
      rw [Function.update_self, hBase,
        hOther ⟨base + (K + 1), by omega⟩ (wire_ne_of_gt (by dsimp; omega))]
      symm
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
def ctxDotProduct {M : ℕ} (K cur : ℕ) (hcur : cur + K + 1 ≤ M)
    (lhs rhs : Fin (K + 1) → Wire M) (hne : ∀ i, lhs i ≠ rhs i)
    (hl : ∀ i, (lhs i).val < cur) (hr : ∀ i, (rhs i).val < cur) : TempCtx M :=
  (ctxAndPairs (K + 1) cur hcur lhs rhs hne hl hr).append
    (ctxCliffAlloc (cnotFoldIntoBase cur K hcur))
theorem ctxDotProduct_countTempAnd {M : ℕ} (K cur : ℕ) (hcur : cur + K + 1 ≤ M)
    (lhs rhs : Fin (K + 1) → Wire M) (hne : ∀ i, lhs i ≠ rhs i)
    (hl : ∀ i, (lhs i).val < cur) (hr : ∀ i, (rhs i).val < cur) :
    (ctxDotProduct K cur hcur lhs rhs hne hl hr).countTempAnd = K + 1 := by
  dsimp only [ctxDotProduct]
  rw [TempCtx.append_countTempAnd, ctxAndPairs_countTempAnd]
  rfl
theorem ctxDotProduct_props {M : ℕ} {mutW : Wire M → Prop} (K cur : ℕ)
    (hcur : cur + K + 1 ≤ M) (lhs rhs : Fin (K + 1) → Wire M) (hne : ∀ i, lhs i ≠ rhs i)
    (hl : ∀ i, (lhs i).val < cur) (hr : ∀ i, (rhs i).val < cur) (hnl : ∀ i, ¬ mutW (lhs i))
    (hnr : ∀ i, ¬ mutW (rhs i)) (hncur : ∀ w : Wire M, cur ≤ w.val → ¬ mutW w) :
    (ctxDotProduct K cur hcur lhs rhs hne hl hr).DisjointFrom mutW ∧
    (ctxDotProduct K cur hcur lhs rhs hne hl hr).SupportsBelowCtx (cur + K + 1) := by
  obtain ⟨hd1, hs1⟩ := ctxAndPairs_props (K + 1) cur hcur lhs rhs hne hl hr hnl hnr hncur
  exact ⟨TempCtx.disjointFrom_append hd1
      (ctxCliffAlloc_disjoint (cnotFoldIntoBase_disjoint cur hncur K hcur)),
    TempCtx.supportsBelowCtx_append le_rfl (TempCtx.supportsBelowCtx_mono (by omega) hs1)
      (ctxCliffAlloc_supports (cnotFoldIntoBase_supportsBelow cur K hcur le_rfl))⟩
theorem ctxDotProduct_scoped {M : ℕ} (K cur : ℕ) (hcur : cur + K + 1 ≤ M)
    (lhs rhs : Fin (K + 1) → Wire M) (hne : ∀ i, lhs i ≠ rhs i)
    (hl : ∀ i, (lhs i).val < cur) (hr : ∀ i, (rhs i).val < cur) :
    let C := ctxDotProduct K cur hcur lhs rhs hne hl hr
    TempCtxLiftEx cur (cur + K + 1) C ∧
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      cleanRem M (M - (cur + K + 1)) (C.fwdBits β) ∧
      (∀ w : Wire M, w.val < cur → C.fwdBits β w = β w) ∧
      C.fwdBits β ⟨cur, by omega⟩ = ∑ i : Fin (K + 1), β (lhs i) * β (rhs i)) := by
  intro C
  obtain ⟨hLift1, hSpec1⟩ := ctxAndPairs_scoped (K + 1) cur hcur lhs rhs hne hl hr
  have hcSupp := cnotFoldIntoBase_supportsBelow cur K hcur le_rfl
  refine ⟨TempCtxLiftEx.append (TempCtxLiftEx.mono hLift1 le_rfl (by omega) hcur)
    (TempCtxLiftEx.cliff (cur + K + 1) hcur _ hcSupp), fun β hβ ↦ ?_⟩
  obtain ⟨hcl1, hbelow1, hpair1⟩ := hSpec1 β hβ
  have hcl1' : cleanRem M (M - (cur + K + 1)) _ := cleanRem_anti (by omega) hcl1
  dsimp only [C, ctxDotProduct]
  rw [TempCtx.append_fwdBits, ctxCliffAlloc_fwdBits (cur + K + 1) hcur _ hcSupp _ hcl1']
  obtain ⟨hOther, hBase⟩ := cnotFoldIntoBase_eval cur K hcur _
  exact ⟨fun w hw ↦ (hOther w (wire_ne_of_gt (by dsimp; omega))).trans (hcl1' w hw),
    fun w hw ↦ (hOther w (wire_ne_of_lt hw)).trans (hbelow1 w hw),
    hBase.trans (Finset.sum_congr rfl fun i _ ↦ hpair1 i)⟩
inductive MicroOp where
  | notW (a : ℕ)
  | cnotW (a b : ℕ)
  | andAlloc (a b : ℕ)
  | zeroAlloc
def microAllocs : List MicroOp → ℕ
  | [] => 0
  | .notW _ :: rest => microAllocs rest
  | .cnotW _ _ :: rest => microAllocs rest
  | .andAlloc _ _ :: rest => 1 + microAllocs rest
  | .zeroAlloc :: rest => 1 + microAllocs rest
def microAnds : List MicroOp → ℕ
  | [] => 0
  | .notW _ :: rest => microAnds rest
  | .cnotW _ _ :: rest => microAnds rest
  | .andAlloc _ _ :: rest => 1 + microAnds rest
  | .zeroAlloc :: rest => microAnds rest
def microValid : ℕ → List MicroOp → Bool
  | _, [] => true
  | top, .notW a :: rest => decide (a < top) && microValid top rest
  | top, .cnotW a b :: rest =>
      decide (a < top) && decide (b < top) && decide (a ≠ b) && microValid top rest
  | top, .andAlloc a b :: rest =>
      decide (a < top) && decide (b < top) && decide (a ≠ b) && microValid (top + 1) rest
  | top, .zeroAlloc :: rest => microValid (top + 1) rest
theorem microValid_notW {top a : ℕ} {rest : List MicroOp}
    (hv : microValid top (.notW a :: rest) = true) :
    a < top ∧ microValid top rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq] using hv
theorem microValid_cnotW {top a b : ℕ} {rest : List MicroOp}
    (hv : microValid top (.cnotW a b :: rest) = true) :
    a < top ∧ b < top ∧ a ≠ b ∧ microValid top rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
theorem microValid_andAlloc {top a b : ℕ} {rest : List MicroOp}
    (hv : microValid top (.andAlloc a b :: rest) = true) :
    a < top ∧ b < top ∧ a ≠ b ∧ microValid (top + 1) rest = true := by
  simpa [microValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hv
def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0
theorem boolToZMod2_not (x : Bool) : boolToZMod2 (!x) = boolToZMod2 x + 1 := by
  cases x <;> decide
theorem boolToZMod2_xor (x y : Bool) :
    boolToZMod2 (xor x y) = boolToZMod2 x + boolToZMod2 y := by
  cases x <;> cases y <;> decide
theorem boolToZMod2_and (x y : Bool) :
    boolToZMod2 (x && y) = boolToZMod2 x * boolToZMod2 y := by
  cases x <;> cases y <;> decide
theorem zmod2_eq_boolToZMod2 (z : ZMod 2) : z = boolToZMod2 (decide (z = 1)) := by
  rcases bit_cases z with rfl | rfl <;> decide
def getBoolAt : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, k + 1 => getBoolAt bs k
def setBoolAt : List Bool → ℕ → Bool → List Bool
  | [], _, _ => []
  | _ :: bs, 0, v => v :: bs
  | b :: bs, k + 1, v => b :: setBoolAt bs k v
theorem length_setBoolAt : ∀ (st : List Bool) (k : ℕ) (v : Bool),
    (setBoolAt st k v).length = st.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: bs, k + 1, v => by simp [setBoolAt, length_setBoolAt bs k v]
theorem getBoolAt_setBoolAt : ∀ (st : List Bool) (k i : ℕ),
    k < st.length → ∀ (v : Bool),
    getBoolAt (setBoolAt st k v) i = if i = k then v else getBoolAt st i
  | [], _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, 0, _, _ | _ :: _, 0, _ + 1, _, _ | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: bs, k + 1, i + 1, hk, v => by
      dsimp only [setBoolAt, getBoolAt]
      rw [getBoolAt_setBoolAt bs k i (Nat.lt_of_succ_lt_succ hk) v]
      simp only [Nat.add_right_cancel_iff]
def evalMicroList : ℕ → List MicroOp → List Bool → List Bool
  | _, [], st => st
  | top, .notW a :: rest, st => evalMicroList top rest (setBoolAt st a (!getBoolAt st a))
  | top, .cnotW a b :: rest, st =>
      evalMicroList top rest (setBoolAt st b (xor (getBoolAt st b) (getBoolAt st a)))
  | top, .andAlloc a b :: rest, st =>
      evalMicroList (top + 1) rest (setBoolAt st top (getBoolAt st a && getBoolAt st b))
  | top, .zeroAlloc :: rest, st => evalMicroList (top + 1) rest (setBoolAt st top false)
def setBoolAtStrict : List Bool → ℕ → Bool → List Bool
  | [], _, _ => []
  | _ :: bs, 0, true => true :: bs
  | _ :: bs, 0, false => false :: bs
  | b :: bs, k + 1, v => match setBoolAtStrict bs k v with | [] => [b] | h :: t => b :: h :: t
theorem setBoolAtStrict_eq : ∀ (st : List Bool) (k : ℕ) (v : Bool),
    setBoolAtStrict st k v = setBoolAt st k v
  | [], _, _ | _ :: _, 0, true | _ :: _, 0, false => rfl
  | _ :: bs, k + 1, v => by
      dsimp only [setBoolAtStrict, setBoolAt]
      rw [setBoolAtStrict_eq bs k v]
      cases setBoolAt bs k v <;> rfl
theorem evalMicroList_nil : ∀ (top : ℕ) (ops : List MicroOp), evalMicroList top ops [] = []
  | _, [] => rfl
  | top, .notW _ :: rest | top, .cnotW _ _ :: rest => evalMicroList_nil top rest
  | top, .andAlloc _ _ :: rest | top, .zeroAlloc :: rest => evalMicroList_nil (top + 1) rest
def evalMicroListStrict : ℕ → List MicroOp → List Bool → List Bool
  | _, [], st => st
  | top, .notW a :: rest, st =>
      match setBoolAtStrict st a (!getBoolAt st a) with
      | [] => [] | h :: t => evalMicroListStrict top rest (h :: t)
  | top, .cnotW a b :: rest, st =>
      match setBoolAtStrict st b (xor (getBoolAt st b) (getBoolAt st a)) with
      | [] => [] | h :: t => evalMicroListStrict top rest (h :: t)
  | top, .andAlloc a b :: rest, st =>
      match setBoolAtStrict st top (getBoolAt st a && getBoolAt st b) with
      | [] => [] | h :: t => evalMicroListStrict (top + 1) rest (h :: t)
  | top, .zeroAlloc :: rest, st =>
      match setBoolAtStrict st top false with
      | [] => [] | h :: t => evalMicroListStrict (top + 1) rest (h :: t)
private theorem match_setBoolAtStrict_eq (top' : ℕ) (rest : List MicroOp)
    (st : List Bool) (k : ℕ) (v : Bool)
    (ih : ∀ s, evalMicroListStrict top' rest s = evalMicroList top' rest s) :
    (match setBoolAtStrict st k v with
     | [] => [] | h :: t => evalMicroListStrict top' rest (h :: t)) =
    evalMicroList top' rest (setBoolAt st k v) := by
  rw [setBoolAtStrict_eq]
  cases setBoolAt st k v with
  | nil => exact (evalMicroList_nil top' rest).symm
  | cons h t => exact ih (h :: t)
theorem evalMicroListStrict_eq : ∀ (ops : List MicroOp) (top : ℕ) (st : List Bool),
    evalMicroListStrict top ops st = evalMicroList top ops st
  | [], _, _ => rfl
  | .notW a :: rest, top, st =>
      match_setBoolAtStrict_eq top rest st a _ (evalMicroListStrict_eq rest top)
  | .cnotW _ b :: rest, top, st =>
      match_setBoolAtStrict_eq top rest st b _ (evalMicroListStrict_eq rest top)
  | .andAlloc _ _ :: rest, top, st | .zeroAlloc :: rest, top, st =>
      match_setBoolAtStrict_eq (top + 1) rest st top _ (evalMicroListStrict_eq rest (top + 1))
def mkBoolList (nIn mask off : ℕ) : ℕ → List Bool
  | 0 => []
  | rem + 1 => (decide (off < nIn) && mask.testBit off) :: mkBoolList nIn mask (off + 1) rem
theorem length_mkBoolList (nIn mask off : ℕ) : ∀ rem : ℕ,
    (mkBoolList nIn mask off rem).length = rem
  | 0 => rfl
  | rem + 1 => by simp [mkBoolList, length_mkBoolList nIn mask (off + 1) rem]
theorem getBoolAt_mkBoolList (nIn mask : ℕ) :
    ∀ (off rem k : ℕ), k < rem →
      getBoolAt (mkBoolList nIn mask off rem) k = (decide (off + k < nIn) && mask.testBit (off + k))
  | _, 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | _, _ + 1, 0, _ => by simp [mkBoolList, getBoolAt]
  | off, rem + 1, k + 1, hk => by
      dsimp only [mkBoolList, getBoolAt]
      rw [getBoolAt_mkBoolList nIn mask (off + 1) rem k (by omega),
        show off + 1 + k = off + (k + 1) by omega]
def initBoolList (nIn len mask : ℕ) : List Bool := mkBoolList nIn mask 0 len
def getNatAt : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => getNatAt xs k
def packSlots (st : List Bool) : List ℕ → ℕ
  | [] => 0
  | s :: rest => (if getBoolAt st s then 1 else 0) + 2 * packSlots st rest
def allBelowFrom (pred : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | off, rem + 1 => pred off && allBelowFrom pred (off + 1) rem
theorem allBelowFrom_iff (pred : ℕ → Bool) :
    ∀ (off rem : ℕ), allBelowFrom pred off rem = true ↔ ∀ k < rem, pred (off + k) = true
  | _, 0 => by simp [allBelowFrom]
  | off, rem + 1 => by
      simp only [allBelowFrom, Bool.and_eq_true, allBelowFrom_iff pred (off + 1) rem]
      refine ⟨fun ⟨h0, hr⟩ k hk ↦ ?_, fun h ↦ ⟨by simpa using h 0 (by omega), fun k hk ↦ ?_⟩⟩
      · rcases k with _ | k'
        · simpa using h0
        · simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hr k' (by omega)
      · simpa [Nat.add_assoc, Nat.add_comm 1 k] using h (k + 1) (by omega)
theorem allBelowFrom_add (pred : ℕ → Bool) : ∀ (off a b : ℕ),
    allBelowFrom pred off (a + b) = (allBelowFrom pred off a && allBelowFrom pred (off + a) b)
  | _, 0, _ => by simp [allBelowFrom]
  | off, a + 1, b => by
      rw [Nat.succ_add]
      simp only [allBelowFrom, allBelowFrom_add pred (off + 1) a b, Bool.and_assoc,
        show off + 1 + a = off + (a + 1) by omega]
theorem allBelowFrom_chunks4 (off sz : ℕ) (pred : ℕ → Bool)
    (h0 : allBelowFrom pred off sz = true) (h1 : allBelowFrom pred (off + sz) sz = true)
    (h2 : allBelowFrom pred (off + 2 * sz) sz = true)
    (h3 : allBelowFrom pred (off + 3 * sz) sz = true) :
    allBelowFrom pred off (4 * sz) = true := by
  rw [show 4 * sz = (sz + sz) + (sz + sz) by omega, allBelowFrom_add, allBelowFrom_add,
    show off + (sz + sz) = off + 2 * sz by omega, allBelowFrom_add,
    show off + 2 * sz + sz = off + 3 * sz by omega, h0, h1, h2, h3]
  rfl
def allBelow (bound : ℕ) (pred : ℕ → Bool) : Bool := allBelowFrom pred 0 bound
theorem allBelow_iff (bound : ℕ) (pred : ℕ → Bool) :
    allBelow bound pred = true ↔ ∀ m < bound, pred m = true := by
  simpa [allBelow] using allBelowFrom_iff pred 0 bound
def microWire {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ)
    (hs : nIn ≤ s → cur + (s - nIn) < M) : Wire M :=
  if h : s < nIn then inW ⟨s, h⟩ else ⟨cur + (s - nIn), hs (Nat.le_of_not_lt h)⟩
theorem microWire_lt_in {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ) (hs : s < nIn)
    (hb : nIn ≤ s → cur + (s - nIn) < M) : microWire inW cur s hb = inW ⟨s, hs⟩ := by
  dsimp [microWire]; exact s3mDitePos hs
theorem microWire_ge_in {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ) (hs : nIn ≤ s)
    (hb : nIn ≤ s → cur + (s - nIn) < M) :
    microWire inW cur s hb = ⟨cur + (s - nIn), hb hs⟩ := by
  dsimp [microWire]; exact s3mDiteNeg (by omega)
theorem microWire_val_lt {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur : ℕ)
    (hin_lt : ∀ i, (inW i).val < cur) {s top : ℕ} (hn : nIn ≤ top) (hs : s < top)
    (hM : cur + (top - nIn) ≤ M) :
    (microWire inW cur s (fun hge ↦ by omega)).val < cur + (top - nIn) := by
  by_cases hlt : s < nIn
  · rw [microWire_lt_in inW cur s hlt]
    exact s3mLtLe (hin_lt ⟨s, hlt⟩) (by omega)
  · rw [microWire_ge_in inW cur s (by omega)]
    dsimp; omega
theorem microWire_ne {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) {s₁ s₂ : ℕ} (hne : s₁ ≠ s₂)
    (hb₁ : nIn ≤ s₁ → cur + (s₁ - nIn) < M) (hb₂ : nIn ≤ s₂ → cur + (s₂ - nIn) < M) :
    microWire inW cur s₁ hb₁ ≠ microWire inW cur s₂ hb₂ := by
  by_cases h1 : s₁ < nIn <;> by_cases h2 : s₂ < nIn
  · rw [microWire_lt_in inW cur s₁ h1, microWire_lt_in inW cur s₂ h2]
    exact fun heq ↦ hne (congrArg Fin.val (hin_inj heq))
  · rw [microWire_lt_in inW cur s₁ h1, microWire_ge_in inW cur s₂ (by omega)]
    exact wire_ne_of_lt (by have := hin_lt ⟨s₁, h1⟩; dsimp; omega)
  · rw [microWire_ge_in inW cur s₁ (by omega), microWire_lt_in inW cur s₂ h2]
    exact wire_ne_of_gt (by have := hin_lt ⟨s₂, h2⟩; dsimp; omega)
  · rw [microWire_ge_in inW cur s₁ (by omega), microWire_ge_in inW cur s₂ (by omega)]
    exact fun heq ↦ by have hv := congrArg Fin.val heq; dsimp at hv; omega
def ctxMicroRun {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) :
    (top : ℕ) → (hn : nIn ≤ top) → (ops : List MicroOp) →
    (hv : microValid top ops = true) →
    (hcur : cur + (top - nIn) + microAllocs ops ≤ M) → TempCtx M
  | _, _, [], _, _ => .hole
  | top, hn, .notW a :: rest, hv, hcur =>
      let ha := (microValid_notW hv).1
      let wA := microWire inW cur a (fun hge ↦ by dsimp [microAllocs] at hcur; omega)
      (ctxCliffAlloc (.x wA)).append
        (ctxMicroRun inW hin_inj cur hin_lt top hn rest (microValid_notW hv).2 hcur)
  | top, hn, .cnotW a b :: rest, hv, hcur =>
      let h := microValid_cnotW hv
      let wA := microWire inW cur a (fun hge ↦ by have := h.1; dsimp [microAllocs] at hcur; omega)
      let wB := microWire inW cur b (fun hge ↦ by have := h.2.1; dsimp [microAllocs] at hcur; omega)
      (ctxCliffAlloc (.cnot wA wB (microWire_ne inW hin_inj cur hin_lt h.2.2.1 _ _))).append
        (ctxMicroRun inW hin_inj cur hin_lt top hn rest h.2.2.2 hcur)
  | top, hn, .andAlloc a b :: rest, hv, hcur =>
      let h := microValid_andAlloc hv
      let curTop := cur + (top - nIn)
      let wA := microWire inW cur a (fun hge ↦ by have := h.1; dsimp [microAllocs] at hcur; omega)
      let wB := microWire inW cur b (fun hge ↦ by have := h.2.1; dsimp [microAllocs] at hcur; omega)
      have hwA_lt : wA.val < curTop :=
        microWire_val_lt inW cur hin_lt hn h.1 (by dsimp [microAllocs] at hcur; omega)
      have hwB_lt : wB.val < curTop :=
        microWire_val_lt inW cur hin_lt hn h.2.1 (by dsimp [microAllocs] at hcur; omega)
      (ctxTempBit wA wB ⟨curTop, by dsimp [curTop]; dsimp [microAllocs] at hcur; omega⟩
        (microWire_ne inW hin_inj cur hin_lt h.2.2.1 _ _)
        (wire_ne_of_lt hwA_lt) (wire_ne_of_lt hwB_lt)).append
        (ctxMicroRun inW hin_inj cur hin_lt (top + 1) (by omega) rest h.2.2.2
          (by dsimp [microAllocs] at hcur; omega))
  | top, hn, .zeroAlloc :: rest, hv, hcur =>
      ctxMicroRun inW hin_inj cur hin_lt (top + 1) (by omega) rest
        (by simpa [microValid] using hv)
        (by dsimp [microAllocs] at hcur; omega)
private theorem microWire_not_mut {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ)
    (hb : nIn ≤ s → cur + (s - nIn) < M) {mutW : Wire M → Prop}
    (hni : ∀ i, ¬ mutW (inW i)) (hnc : ∀ w : Wire M, cur ≤ w.val → ¬ mutW w) :
    ¬ mutW (microWire inW cur s hb) := by
  by_cases hlt : s < nIn
  · rw [microWire_lt_in inW cur s hlt]; exact hni _
  · rw [microWire_ge_in inW cur s (by omega)]; exact hnc _ (by dsimp; omega)
private theorem ne_microWire_of_lt_not_in {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur s : ℕ)
    (hb : nIn ≤ s → cur + (s - nIn) < M) {w : Wire M} (hw : w.val < cur)
    (hwni : ∀ i, w ≠ inW i) : w ≠ microWire inW cur s hb := by
  by_cases hlt : s < nIn
  · rw [microWire_lt_in inW cur s hlt]; exact hwni _
  · rw [microWire_ge_in inW cur s (by omega)]; exact wire_ne_of_lt (by dsimp; omega)
private def MicroLoopSpec {M nIn : ℕ} (inW : Fin nIn → Wire M) (cur top nAlloc nAnd : ℕ)
    (hcur : cur + (top - nIn) + nAlloc ≤ M) (evalFn : List Bool → List Bool) (K : TempCtx M) :
    Prop :=
  K.countTempAnd = nAnd ∧
  (∀ {mutW : Wire M → Prop}, (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
    K.DisjointFrom mutW ∧ K.SupportsBelowCtx (cur + (top - nIn) + nAlloc)) ∧
  TempCtxLiftEx (cur + (top - nIn)) (cur + (top - nIn) + nAlloc) K ∧
  (∀ (β : BitAssignment M) (st : List Bool), cleanRem M (M - (cur + (top - nIn))) β →
    st.length = top + nAlloc →
    (∀ s (_ : s < top), β (microWire inW cur s (fun _ ↦ by omega)) =
      boolToZMod2 (getBoolAt st s)) →
    cleanRem M (M - (cur + (top - nIn) + nAlloc)) (K.fwdBits β) ∧
    (∀ w : Wire M, w.val < cur → (∀ i, w ≠ inW i) → K.fwdBits β w = β w) ∧
    (∀ s (_ : s < top + nAlloc), K.fwdBits β (microWire inW cur s (fun _ ↦ by omega)) =
      boolToZMod2 (getBoolAt (evalFn st) s)))
private theorem microLoopSpec_cliff {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur top nAlloc nAnd : ℕ)
    (hin_lt : ∀ i, (inW i).val < cur) (hn : nIn ≤ top) (hcur : cur + (top - nIn) + nAlloc ≤ M)
    {evalFn : List Bool → List Bool} {K : TempCtx M}
    (hK : MicroLoopSpec inW cur top nAlloc nAnd hcur evalFn K)
    (dst : ℕ) (hdst : dst < top) (c : CliffProg M) (hcSupp : c.SupportsBelow (cur + (top - nIn)))
    (hcDisj : ∀ {mutW : Wire M → Prop},
      (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) → CliffDisjoint mutW c)
    (valZ : BitAssignment M → ZMod 2) (valB : List Bool → Bool)
    (hcEval : ∀ β, c.eval β = Function.update β (microWire inW cur dst (fun _ ↦ by omega)) (valZ β))
    (hVal : ∀ (β : BitAssignment M) (st : List Bool),
      (∀ s (_ : s < top), β (microWire inW cur s (fun _ ↦ by omega)) =
        boolToZMod2 (getBoolAt st s)) → valZ β = boolToZMod2 (valB st)) :
    MicroLoopSpec inW cur top nAlloc nAnd hcur
      (fun st ↦ evalFn (setBoolAt st dst (valB st))) ((ctxCliffAlloc c).append K) := by
  obtain ⟨hCnt, hProps, hLiftR, hEvalR⟩ := hK
  refine ⟨by rw [TempCtx.append_countTempAnd, hCnt]; dsimp [ctxCliffAlloc,
    TempCtx.countTempAnd]; omega,
    fun hni hnc ↦ ⟨TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint (hcDisj hni hnc))
      (hProps hni hnc).1, TempCtx.supportsBelowCtx_append (c₁ := cur + (top - nIn)) (by omega)
        (ctxCliffAlloc_supports hcSupp) (hProps hni hnc).2⟩,
    TempCtxLiftEx.append (TempCtxLiftEx.cliff (cur + (top - nIn)) (by omega) c hcSupp) hLiftR,
    fun β st hβ hlen hst ↦ ?_⟩
  rw [TempCtx.append_fwdBits, ctxCliffAlloc_fwdBits (cur + (top - nIn)) (by omega) c hcSupp β hβ]
  obtain ⟨hclOut, hpresOut, hsOut⟩ := hEvalR (c.eval β) (setBoolAt st dst (valB st))
    (fun w hw ↦ (congrFun (hcEval β) w).trans
      ((Function.update_of_ne (wire_ne_of_gt
        (s3mLtLe (microWire_val_lt inW cur hin_lt hn hdst (by omega)) (by omega))) _ _).trans
        (hβ w hw)))
    (by rw [length_setBoolAt]; exact hlen) fun s hs ↦ by
      rw [hcEval, getBoolAt_setBoolAt st dst s (by omega)]
      by_cases hsd : s = dst
      · subst hsd; rw [Function.update_self, s3mItePos rfl, hVal β st hst]
      · rw [Function.update_of_ne (microWire_ne inW hin_inj cur hin_lt hsd _ _),
          s3mIteNeg hsd, hst s hs]
  exact ⟨hclOut, fun w hw hwni ↦ (hpresOut w hw hwni).trans ((congrFun (hcEval β) w).trans
    (Function.update_of_ne (ne_microWire_of_lt_not_in inW cur dst _ hw hwni) _ _)), hsOut⟩
theorem ctxMicroRun_loop {M nIn : ℕ} (inW : Fin nIn → Wire M)
    (hin_inj : Function.Injective inW) (cur : ℕ) (hin_lt : ∀ i, (inW i).val < cur) :
    ∀ (ops : List MicroOp) (top : ℕ) (hn : nIn ≤ top) (hv : microValid top ops = true)
      (hcur : cur + (top - nIn) + microAllocs ops ≤ M),
      let K := ctxMicroRun inW hin_inj cur hin_lt top hn ops hv hcur
      K.countTempAnd = microAnds ops ∧
      (∀ {mutW : Wire M → Prop},
        (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
        K.DisjointFrom mutW ∧ K.SupportsBelowCtx (cur + (top - nIn) + microAllocs ops)) ∧
      TempCtxLiftEx (cur + (top - nIn)) (cur + (top - nIn) + microAllocs ops) K ∧
      (∀ (β : BitAssignment M) (st : List Bool),
        cleanRem M (M - (cur + (top - nIn))) β → st.length = top + microAllocs ops →
        (∀ (s : ℕ) (hs : s < top), β (microWire inW cur s (fun hge ↦ by omega)) =
          boolToZMod2 (getBoolAt st s)) →
        cleanRem M (M - (cur + (top - nIn) + microAllocs ops)) (K.fwdBits β) ∧
        (∀ w : Wire M, w.val < cur → (∀ i, w ≠ inW i) → K.fwdBits β w = β w) ∧
        (∀ (s : ℕ) (hs : s < top + microAllocs ops),
          K.fwdBits β (microWire inW cur s (fun hge ↦ by omega)) =
            boolToZMod2 (getBoolAt (evalMicroList top ops st) s))) := by
  intro ops
  induction ops with
  | nil =>
      intro top hn hv hcur
      dsimp only [ctxMicroRun, microAllocs, microAnds, evalMicroList, Nat.add_zero]
      exact ⟨rfl, fun _ _ ↦ ⟨trivial, trivial⟩, fun h ↦ ⟨_, h⟩,
        fun β st hβ _ hst ↦ ⟨hβ, fun _ _ _ ↦ rfl, hst⟩⟩
  | cons op rest ih =>
      intro top hn hv hcur
      cases op with
      | notW a =>
          obtain ⟨ha, hvR⟩ := microValid_notW hv
          dsimp only [ctxMicroRun, microAllocs, microAnds] at hcur ⊢
          exact microLoopSpec_cliff inW hin_inj cur top (microAllocs rest) (microAnds rest)
            hin_lt hn hcur (ih top hn hvR hcur) a ha (.x (microWire inW cur a fun _ ↦ by omega))
            (microWire_val_lt inW cur hin_lt hn ha (by omega))
            (fun hni hnc ↦ microWire_not_mut inW cur a _ hni hnc)
            (fun β ↦ β (microWire inW cur a fun _ ↦ by omega) + 1) (fun st ↦ !getBoolAt st a)
            (fun _ ↦ rfl) (fun β st hst ↦ by rw [hst a ha, boolToZMod2_not])
      | cnotW a b =>
          obtain ⟨ha, hb, hab, hvR⟩ := microValid_cnotW hv
          dsimp only [ctxMicroRun, microAllocs, microAnds] at hcur ⊢
          let wA := microWire inW cur a (fun _ ↦ by omega)
          let wB := microWire inW cur b (fun _ ↦ by omega)
          exact microLoopSpec_cliff inW hin_inj cur top (microAllocs rest) (microAnds rest)
            hin_lt hn hcur (ih top hn hvR hcur) b hb
            (.cnot wA wB (microWire_ne inW hin_inj cur hin_lt hab _ _))
            ⟨microWire_val_lt inW cur hin_lt hn ha (by omega),
             microWire_val_lt inW cur hin_lt hn hb (by omega)⟩
            (fun hni hnc ↦ ⟨microWire_not_mut inW cur a _ hni hnc,
              microWire_not_mut inW cur b _ hni hnc⟩)
            (fun β ↦ β wB + β wA) (fun st ↦ xor (getBoolAt st b) (getBoolAt st a)) (fun _ ↦ rfl)
            (fun β st hst ↦ by rw [hst b hb, hst a ha, boolToZMod2_xor])
      | andAlloc a b =>
          obtain ⟨ha, hb, hab, hvR⟩ := microValid_andAlloc hv
          dsimp only [microAllocs] at hcur
          obtain ⟨hCnt, hProps, hLiftR, hEvalR⟩ := ih (top + 1) (by omega) hvR (by omega)
          set curTop := cur + (top - nIn)
          let wA := microWire inW cur a (fun _ ↦ by omega)
          let wB := microWire inW cur b (fun _ ↦ by omega)
          let anc : Wire M := ⟨curTop, by omega⟩
          have hwA_lt := microWire_val_lt inW cur hin_lt hn ha (by omega)
          have hwB_lt := microWire_val_lt inW cur hin_lt hn hb (by omega)
          have hneAB : wA ≠ wB := microWire_ne inW hin_inj cur hin_lt hab _ _
          have hLiftR' : TempCtxLiftEx (curTop + 1) (curTop + (1 + microAllocs rest)) _ :=
            TempCtxLiftEx.mono hLiftR (by dsimp [curTop]; omega) (by dsimp [curTop]; omega)
              (by dsimp [curTop]; omega)
          dsimp only [ctxMicroRun, microAllocs, microAnds]
          refine ⟨by rw [TempCtx.append_countTempAnd, hCnt]; rfl,
            fun hni hnc ↦ ⟨TempCtx.disjointFrom_append
              ⟨microWire_not_mut inW cur a _ hni hnc, microWire_not_mut inW cur b _ hni hnc,
                hnc anc (by dsimp [anc, curTop]; omega), trivial⟩ (hProps hni hnc).1,
              TempCtx.supportsBelowCtx_append (c₁ := curTop + 1) (by dsimp [curTop]; omega)
                ⟨by dsimp [anc, curTop]; omega, trivial⟩
                (TempCtx.supportsBelowCtx_mono (by dsimp [curTop]; omega) (hProps hni hnc).2)⟩,
            TempCtxLiftEx.append
              (TempCtxLiftEx.tempBit curTop (by omega) wA wB hneAB hwA_lt hwB_lt) hLiftR',
            fun β st hβ hlen hst ↦ ?_⟩
          rw [TempCtx.append_fwdBits,
            ctxTempBit_fwdBits_clean curTop (by omega) wA wB hneAB hwA_lt hwB_lt β hβ]
          let β₁ := Function.update β anc (β wA * β wB)
          have hcl₁ : cleanRem M (M - (cur + (top + 1 - nIn))) β₁ := fun w hw ↦ by
            dsimp only [β₁]
            rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [anc, curTop]; omega))]
            exact hβ w (by dsimp [curTop]; omega)
          have hst₁ : ∀ s (_ : s < top + 1), β₁ (microWire inW cur s (fun _ ↦ by omega)) =
              boolToZMod2 (getBoolAt (setBoolAt st top (getBoolAt st a && getBoolAt st b)) s) := by
            intro s hs
            dsimp only [β₁]
            rw [getBoolAt_setBoolAt st top s (by omega)]
            by_cases hst_top : s = top
            · subst hst_top
              rw [show microWire inW cur s (fun _ ↦ by omega) = anc from
                microWire_ge_in inW cur s hn _, Function.update_self, s3mItePos rfl,
                hst a ha, hst b hb, boolToZMod2_and]
            · rw [Function.update_of_ne (wire_ne_of_lt
                (microWire_val_lt inW cur hin_lt hn (show s < top by omega) (by omega))),
                s3mIteNeg hst_top, hst s (by omega)]
          obtain ⟨hclOut, hpresOut, hsOut⟩ := hEvalR β₁ _ hcl₁
            (by rw [length_setBoolAt]; omega) hst₁
          exact ⟨cleanRem_anti (by omega) hclOut, fun w hw hwni ↦ (hpresOut w hw hwni).trans
            (Function.update_of_ne (wire_ne_of_lt (by dsimp [anc, curTop]; omega)) _ _),
            fun s hs ↦ hsOut s (by omega)⟩
      | zeroAlloc =>
          dsimp only [ctxMicroRun, microAllocs, microAnds] at hcur ⊢
          obtain ⟨hCnt, hProps, hLiftR, hEvalR⟩ := ih (top + 1) (by omega)
            (by simpa [microValid] using hv) (by omega)
          refine ⟨hCnt, fun hni hnc ↦ ⟨(hProps hni hnc).1,
              TempCtx.supportsBelowCtx_mono (by omega) (hProps hni hnc).2⟩,
            TempCtxLiftEx.mono hLiftR (by omega) (by omega) (by omega),
            fun β st hβ hlen hst ↦ ?_⟩
          obtain ⟨hclOut, hpresOut, hsOut⟩ := hEvalR β (setBoolAt st top false)
            (cleanRem_anti (by omega) hβ) (by rw [length_setBoolAt]; omega) fun s hs ↦ by
              rw [getBoolAt_setBoolAt st top s (by omega)]
              by_cases hst_top : s = top
              · subst hst_top
                rw [microWire_ge_in inW cur s hn _, s3mItePos rfl]
                exact hβ _ (by dsimp; omega)
              · rw [s3mIteNeg hst_top]
                exact hst s (by omega)
          exact ⟨cleanRem_anti (by omega) hclOut, hpresOut, fun s hs ↦ hsOut s (by omega)⟩
def ctxMicro {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur nAlloc nAnd : ℕ) (hin_lt : ∀ i, (inW i).val < cur) (ops : List MicroOp) (hMeta :
    microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ microAnds ops = nAnd)
    (hcur : cur + nAlloc ≤ M) : TempCtx M :=
  ctxMicroRun inW hin_inj cur hin_lt nIn le_rfl ops hMeta.1 (by have := hMeta.2.1; omega)
theorem bitsVal_testBit_eq {W : ℕ} (g : Fin W → ZMod 2) (i : Fin W) :
    (bitsVal g).testBit i.val = decide (g i = 1) := by
  rw [congrFun (bitsVal_injective (bitsVal_eq_of_testBit
    (fun j ↦ if (bitsVal g).testBit j.val then 1 else 0) (bitsVal g)
    (bitsVal_lt_two_pow g) fun _ ↦ rfl).symm) i]
  cases (bitsVal g).testBit i.val <;> decide
theorem ctxMicro_scoped {M nIn : ℕ} (inW : Fin nIn → Wire M) (hin_inj : Function.Injective inW)
    (cur nAlloc nAnd : ℕ) (hin_lt : ∀ i, (inW i).val < cur)
    (ops : List MicroOp)
    (hMeta : microValid nIn ops = true ∧ microAllocs ops = nAlloc ∧ microAnds ops = nAnd)
    (hcur : cur + nAlloc ≤ M) :
    let K := ctxMicro inW hin_inj cur nAlloc nAnd hin_lt ops hMeta hcur
    K.countTempAnd = nAnd ∧
    (∀ {mutW : Wire M → Prop},
      (∀ i, ¬ mutW (inW i)) → (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      K.DisjointFrom mutW ∧ K.SupportsBelowCtx (cur + nAlloc)) ∧
    TempCtxLiftEx cur (cur + nAlloc) K ∧
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      let m := bitsVal (fun i ↦ β (inW i))
      let stOut := evalMicroList nIn ops (initBoolList nIn (nIn + nAlloc) m)
      cleanRem M (M - (cur + nAlloc)) (K.fwdBits β) ∧
      (allBelow nIn (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire M, w.val < cur → K.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : nIn ≤ s) (hhi : s < nIn + nAlloc),
        K.fwdBits β ⟨cur + (s - nIn), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) := by
  intro K
  obtain ⟨hCnt, hProps, hLift, hEval⟩ :=
    ctxMicroRun_loop inW hin_inj cur hin_lt ops nIn le_rfl hMeta.1 (by have := hMeta.2.1; omega)
  have hAlloc := hMeta.2.1
  refine ⟨hCnt.trans hMeta.2.2, fun hni hnc ↦ ⟨(hProps hni hnc).1, TempCtx.supportsBelowCtx_mono
    (by omega) (hProps hni hnc).2⟩, TempCtxLiftEx.mono hLift (by omega) (by omega) hcur,
    fun β hβ ↦ ?_⟩
  let m := bitsVal (fun i ↦ β (inW i))
  let st₀ := initBoolList nIn (nIn + nAlloc) m
  have hst₀ : ∀ s (hs : s < nIn),
      β (microWire inW cur s (fun _ ↦ by omega)) = boolToZMod2 (getBoolAt st₀ s) := fun s hs ↦ by
    rw [microWire_lt_in inW cur s hs]
    dsimp [st₀, initBoolList]
    rw [getBoolAt_mkBoolList nIn m 0 (nIn + nAlloc) s (by omega)]
    simp only [Nat.zero_add, hs, decide_true, Bool.true_and]
    rw [show m.testBit s = decide (β (inW ⟨s, hs⟩) = 1) from
      bitsVal_testBit_eq (fun i ↦ β (inW i)) ⟨s, hs⟩, ← zmod2_eq_boolToZMod2]
  obtain ⟨hclOut, hpresOut, hsOut⟩ := hEval β st₀ (by simpa using hβ)
    (by dsimp [st₀, initBoolList]; rw [length_mkBoolList]; omega) hst₀
  refine ⟨cleanRem_anti (by omega) hclOut, fun hall w hw ↦ ?_, fun s hge hlt ↦ ?_⟩
  · by_cases hmem : ∃ i, w = inW i
    · obtain ⟨i, rfl⟩ := hmem
      have hi_eq := (allBelow_iff nIn _).mp hall i.val i.isLt
      simp only [beq_iff_eq] at hi_eq
      dsimp only [K, ctxMicro]
      rw [← microWire_lt_in inW cur i.val i.isLt (fun _ ↦ by omega), hsOut i.val (by omega),
        hi_eq, bitsVal_testBit_eq (fun j ↦ β (inW j)) i, ← zmod2_eq_boolToZMod2,
        microWire_lt_in inW cur i.val i.isLt]
    · exact hpresOut w hw (fun i h ↦ hmem ⟨i, h⟩)
  · dsimp only [K, ctxMicro]
    rw [← microWire_ge_in inW cur s hge (fun _ ↦ by omega)]
    exact hsOut s (by omega)
theorem boolToZMod2_decide_eq_one (b : Bool) : decide (boolToZMod2 b = 1) = b := by
  cases b <;> decide
theorem allBelowFrom_chunks2 (off sz : ℕ) (pred : ℕ → Bool)
    (h0 : allBelowFrom pred off sz = true) (h1 : allBelowFrom pred (off + sz) sz = true) :
    allBelowFrom pred off (2 * sz) = true := by
  have s1 : 2 * sz = sz + sz := by omega
  rw [s1, allBelowFrom_add, h0, h1]
  rfl
def top7MuOps : List MicroOp := [
    .notW 1, .notW 2, .notW 3, .notW 4, .notW 5, .notW 6, .andAlloc 6 5, .andAlloc 7 4,
      .andAlloc 8 3, .andAlloc 9 2, .andAlloc 10 1, .zeroAlloc, .cnotW 6 12, .cnotW 7 12,
      .cnotW 8 12, .cnotW 9 12, .cnotW 10 12, .cnotW 11 12, .zeroAlloc, .notW 13, .cnotW 6 13,
      .cnotW 8 13, .cnotW 10 13, .zeroAlloc, .notW 14, .cnotW 8 14, .notW 1, .notW 2, .notW 3,
      .notW 4, .notW 5, .notW 6
  ]
def mu3OneHot7GeOps : List MicroOp := [
    .zeroAlloc, .notW 3, .cnotW 2 3, .zeroAlloc, .cnotW 2 4, .andAlloc 3 1, .cnotW 5 3,
      .andAlloc 4 1, .cnotW 6 4, .andAlloc 3 0, .cnotW 7 3, .andAlloc 5 0, .cnotW 8 5,
      .andAlloc 4 0, .cnotW 9 4, .notW 0, .andAlloc 6 0, .notW 0, .zeroAlloc, .cnotW 10 11,
      .cnotW 9 11, .zeroAlloc, .cnotW 11 12, .cnotW 4 12, .zeroAlloc, .cnotW 12 13, .cnotW 8 13,
      .zeroAlloc, .cnotW 13 14, .cnotW 5 14, .zeroAlloc, .cnotW 14 15, .cnotW 7 15, .zeroAlloc,
      .cnotW 15 16, .cnotW 3 16
  ]
def mu3OneHot7Ops : List MicroOp := [
    .zeroAlloc, .notW 3, .cnotW 2 3, .zeroAlloc, .cnotW 2 4, .andAlloc 3 1, .cnotW 5 3,
      .andAlloc 4 1, .cnotW 6 4, .andAlloc 3 0, .cnotW 7 3, .andAlloc 5 0, .cnotW 8 5,
      .andAlloc 4 0, .cnotW 9 4, .notW 0, .andAlloc 6 0, .notW 0
  ]
def ne128_8Ops : List MicroOp := [
    .notW 0, .notW 1, .notW 2, .notW 3, .notW 4, .notW 5, .notW 6, .andAlloc 7 0, .andAlloc 8 1,
      .andAlloc 9 2, .andAlloc 10 3, .andAlloc 11 4, .andAlloc 12 5, .andAlloc 13 6, .notW 0,
      .notW 1, .notW 2, .notW 3, .notW 4, .notW 5, .notW 6, .notW 14
  ]
def and5Ops : List MicroOp := [ .andAlloc 0 1, .andAlloc 5 2, .andAlloc 6 3, .andAlloc 7 4 ]
def s3Flip8Ops : List MicroOp := [
    .notW 1, .notW 2, .notW 3, .notW 4, .notW 5, .notW 6, .notW 7, .andAlloc 1 2, .andAlloc 8 3,
      .andAlloc 9 4, .andAlloc 10 5, .andAlloc 11 6, .andAlloc 12 7, .notW 1, .notW 2, .notW 3,
      .notW 4, .notW 5, .notW 6, .notW 7, .notW 13, .andAlloc 0 13
  ]
def top7MuSlots : List ℕ := [12,13,14]
private def microCheckStrict (nIn len : ℕ) (ops : List MicroOp)
    (post : ℕ → List Bool → Bool) (m : ℕ) : Bool :=
  post m (evalMicroListStrict nIn ops (initBoolList nIn len m))
private theorem allBelow_congr_eq (bound : ℕ) (p q : ℕ → Bool) (h : ∀ m, p m = q m)
    (hp : allBelow bound p = true) : allBelow bound q = true := by
  rw [allBelow_iff] at hp ⊢
  exact fun m hm ↦ (h m).symm.trans (hp m hm)
private theorem allBelow_of_microCheckStrict (bound nIn len : ℕ) (ops : List MicroOp)
    (post : ℕ → List Bool → Bool) (chk : ℕ → Bool)
    (hchk : ∀ m, chk m = post m (evalMicroList nIn ops (initBoolList nIn len m)))
    (hok : allBelow bound (microCheckStrict nIn len ops post) = true) :
    allBelow bound chk = true := by
  rw [allBelow_iff] at hok ⊢
  exact fun m hm ↦ by rw [hchk m, ← evalMicroListStrict_eq]; exact hok m hm
private theorem slots_bounds_of_allBelow (n lo hi : ℕ) (slots : List ℕ)
    (hok : allBelow n (fun j ↦ decide (lo ≤ getNatAt slots j) &&
      decide (getNatAt slots j < hi)) = true) (k : Fin n) :
    lo ≤ getNatAt slots k.val ∧ getNatAt slots k.val < hi := by
  simpa [Bool.and_eq_true, decide_eq_true_eq] using (allBelow_iff n _).mp hok k.val k.isLt
private theorem allBelowFrom_256 (p : ℕ → Bool)
    (h0 : allBelowFrom p 0 32 = true) (h1 : allBelowFrom p 32 32 = true)
    (h2 : allBelowFrom p 64 32 = true) (h3 : allBelowFrom p 96 32 = true)
    (h4 : allBelowFrom p 128 32 = true) (h5 : allBelowFrom p 160 32 = true)
    (h6 : allBelowFrom p 192 32 = true) (h7 : allBelowFrom p 224 32 = true) :
    allBelow 256 p = true :=
  allBelowFrom_chunks2 0 128 p (allBelowFrom_chunks4 0 32 p h0 h1 h2 h3)
    (allBelowFrom_chunks4 128 32 p h4 h5 h6 h7)
theorem top7Mu_meta3 : microValid 7 top7MuOps = true ∧ microAllocs top7MuOps = 8 ∧
    microAnds top7MuOps = 5 := by decide
theorem top7MuSlots_bounds (k : Fin 3) :
    7 ≤ getNatAt top7MuSlots k.val ∧ getNatAt top7MuSlots k.val < 15 :=
  slots_bounds_of_allBelow 3 7 15 top7MuSlots (by decide) k
def top7MuCheck (m : ℕ) : Bool :=
  let st := evalMicroList 7 top7MuOps (initBoolList 7 15 m)
  allBelow 7 (fun i ↦ getBoolAt st i == m.testBit i) &&
    (packSlots st top7MuSlots == s3mTop7Mu m) &&
    allBelow 3 (fun j ↦ getBoolAt st (getNatAt top7MuSlots j) == (s3mTop7Mu m).testBit j)
private def top7MuCheckS (m : ℕ) : Bool := microCheckStrict 7 15 top7MuOps (fun m st ↦
  allBelow 7 (fun i ↦ getBoolAt st i == m.testBit i) &&
    (packSlots st top7MuSlots == s3mTop7Mu m) &&
    allBelow 3 (fun j ↦ getBoolAt st (getNatAt top7MuSlots j) == (s3mTop7Mu m).testBit j)) m
private theorem top7MuStrict_L0_0 : allBelowFrom top7MuCheckS 0 32 = true :=
  allBelowFrom_chunks4 0 8 top7MuCheckS (by decide) (by decide) (by decide) (by decide)
private theorem top7MuStrict_L0_1 : allBelowFrom top7MuCheckS 32 32 = true :=
  allBelowFrom_chunks4 32 8 top7MuCheckS (by decide) (by decide) (by decide) (by decide)
private theorem top7MuStrict_L0_2 : allBelowFrom top7MuCheckS 64 32 = true :=
  allBelowFrom_chunks4 64 8 top7MuCheckS (by decide) (by decide) (by decide) (by decide)
private theorem top7MuStrict_L0_3 : allBelowFrom top7MuCheckS 96 32 = true :=
  allBelowFrom_chunks4 96 8 top7MuCheckS (by decide) (by decide) (by decide) (by decide)
theorem top7Mu_eval_ok : allBelow 128 top7MuCheck = true :=
  allBelow_congr_eq 128 top7MuCheckS top7MuCheck
    (fun m ↦ by simp only [top7MuCheckS, top7MuCheck, microCheckStrict, evalMicroListStrict_eq])
    (allBelowFrom_chunks4 0 32 top7MuCheckS
      top7MuStrict_L0_0 top7MuStrict_L0_1 top7MuStrict_L0_2 top7MuStrict_L0_3)
def mu3Sel7Slots : List ℕ := [3,7,5,8,4,9,10]
theorem mu3OneHot7Ge_meta3 : microValid 3 mu3OneHot7GeOps = true ∧
    microAllocs mu3OneHot7GeOps = 14 ∧ microAnds mu3OneHot7GeOps = 6 := by decide
theorem mu3Sel7Slots_bounds (k : Fin 7) :
    3 ≤ getNatAt mu3Sel7Slots k.val ∧ getNatAt mu3Sel7Slots k.val < 17 :=
  slots_bounds_of_allBelow 7 3 17 mu3Sel7Slots (by decide) k
def mu3GeSlots : List ℕ := [16,15,14,13,12,11,10]
theorem mu3GeSlots_bounds (k : Fin 7) :
    3 ≤ getNatAt mu3GeSlots k.val ∧ getNatAt mu3GeSlots k.val < 17 :=
  slots_bounds_of_allBelow 7 3 17 mu3GeSlots (by decide) k
def mu3OneHot7GeCheck (m : ℕ) : Bool :=
  let st := evalMicroList 3 mu3OneHot7GeOps (initBoolList 3 17 m)
  allBelow 3 (fun i ↦ getBoolAt st i == m.testBit i) &&
    allBelow 7 (fun a ↦ getBoolAt st (getNatAt mu3Sel7Slots a) == decide (m = a)) &&
    allBelow 7 (fun a ↦ getBoolAt st (getNatAt mu3GeSlots a) == (decide (a ≤ m) && decide (m < 7)))
theorem mu3OneHot7Ge_eval_ok : allBelow 8 mu3OneHot7GeCheck = true :=
  allBelow_of_microCheckStrict 8 3 17 mu3OneHot7GeOps
    (fun m st ↦ allBelow 3 (fun i ↦ getBoolAt st i == m.testBit i) &&
      allBelow 7 (fun a ↦ getBoolAt st (getNatAt mu3Sel7Slots a) == decide (m = a)) &&
      allBelow 7 (fun a ↦
        getBoolAt st (getNatAt mu3GeSlots a) == (decide (a ≤ m) && decide (m < 7))))
    mu3OneHot7GeCheck (fun _ ↦ rfl) (by decide)
theorem mu3OneHot7_meta3 : microValid 3 mu3OneHot7Ops = true ∧ microAllocs mu3OneHot7Ops = 8 ∧
    microAnds mu3OneHot7Ops = 6 := by decide
theorem mu3Sel7Slots_bounds11 (k : Fin 7) :
    3 ≤ getNatAt mu3Sel7Slots k.val ∧ getNatAt mu3Sel7Slots k.val < 11 :=
  slots_bounds_of_allBelow 7 3 11 mu3Sel7Slots (by decide) k
def mu3OneHot7Check (m : ℕ) : Bool :=
  let st := evalMicroList 3 mu3OneHot7Ops (initBoolList 3 11 m)
  allBelow 3 (fun i ↦ getBoolAt st i == m.testBit i) &&
    allBelow 7 (fun a ↦ getBoolAt st (getNatAt mu3Sel7Slots a) == decide (m = a))
theorem mu3OneHot7_eval_ok : allBelow 8 mu3OneHot7Check = true :=
  allBelow_of_microCheckStrict 8 3 11 mu3OneHot7Ops
    (fun m st ↦ allBelow 3 (fun i ↦ getBoolAt st i == m.testBit i) &&
      allBelow 7 (fun a ↦ getBoolAt st (getNatAt mu3Sel7Slots a) == decide (m = a)))
    mu3OneHot7Check (fun _ ↦ rfl) (by decide)
theorem ne128_8_meta : microValid 8 ne128_8Ops = true ∧ microAllocs ne128_8Ops = 7 ∧
    microAnds ne128_8Ops = 7 := by decide
def ne128_8Check (m : ℕ) : Bool :=
  let st := evalMicroList 8 ne128_8Ops (initBoolList 8 15 m)
  allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) && (getBoolAt st 14 == decide (m ≠ 128))
private def ne128_8CheckS (m : ℕ) : Bool := microCheckStrict 8 15 ne128_8Ops (fun m st ↦
  allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) && (getBoolAt st 14 == decide (m ≠ 128))) m
private theorem ne128_8Strict_L0_0 : allBelowFrom ne128_8CheckS 0 32 = true :=
  allBelowFrom_chunks4 0 8 ne128_8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem ne128_8Strict_L0_1 : allBelowFrom ne128_8CheckS 32 32 = true :=
  allBelowFrom_chunks4 32 8 ne128_8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem ne128_8Strict_L0_2 : allBelowFrom ne128_8CheckS 64 32 = true :=
  allBelowFrom_chunks4 64 8 ne128_8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem ne128_8Strict_L0_3 : allBelowFrom ne128_8CheckS 96 32 = true :=
  allBelowFrom_chunks4 96 8 ne128_8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem ne128_8Strict_L0_4 : allBelowFrom ne128_8CheckS 128 32 = true :=
  allBelowFrom_chunks4 128 8 ne128_8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem ne128_8Strict_L0_5 : allBelowFrom ne128_8CheckS 160 32 = true :=
  allBelowFrom_chunks4 160 8 ne128_8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem ne128_8Strict_L0_6 : allBelowFrom ne128_8CheckS 192 32 = true :=
  allBelowFrom_chunks4 192 8 ne128_8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem ne128_8Strict_L0_7 : allBelowFrom ne128_8CheckS 224 32 = true :=
  allBelowFrom_chunks4 224 8 ne128_8CheckS (by decide) (by decide) (by decide) (by decide)
theorem ne128_8_eval_ok : allBelow 256 ne128_8Check = true :=
  allBelow_congr_eq 256 ne128_8CheckS ne128_8Check
    (fun m ↦ by simp only [ne128_8CheckS, ne128_8Check, microCheckStrict, evalMicroListStrict_eq])
    (allBelowFrom_256 ne128_8CheckS ne128_8Strict_L0_0 ne128_8Strict_L0_1 ne128_8Strict_L0_2
      ne128_8Strict_L0_3 ne128_8Strict_L0_4 ne128_8Strict_L0_5 ne128_8Strict_L0_6
        ne128_8Strict_L0_7)
theorem and5_meta : microValid 5 and5Ops = true ∧ microAllocs and5Ops = 4 ∧
    microAnds and5Ops = 4 := by decide
def and5Check (m : ℕ) : Bool :=
  let st := evalMicroList 5 and5Ops (initBoolList 5 9 m)
  allBelow 5 (fun i ↦ getBoolAt st i == m.testBit i) &&
    (getBoolAt st 8 == (m.testBit 0 && m.testBit 1 && m.testBit 2 && m.testBit 3 && m.testBit 4))
private def and5CheckS (m : ℕ) : Bool := microCheckStrict 5 9 and5Ops (fun m st ↦
  allBelow 5 (fun i ↦ getBoolAt st i == m.testBit i) &&
    (getBoolAt st 8 == (m.testBit 0 && m.testBit 1 && m.testBit 2 && m.testBit 3 && m.testBit 4))) m
theorem and5_eval_ok : allBelow 32 and5Check = true :=
  allBelow_congr_eq 32 and5CheckS and5Check
    (fun m ↦ by simp only [and5CheckS, and5Check, microCheckStrict, evalMicroListStrict_eq])
    (allBelowFrom_chunks4 0 8 and5CheckS (by decide) (by decide) (by decide) (by decide))
theorem s3Flip8_meta : microValid 8 s3Flip8Ops = true ∧ microAllocs s3Flip8Ops = 7 ∧
    microAnds s3Flip8Ops = 7 := by decide
def s3Flip8Check (m : ℕ) : Bool :=
  let st := evalMicroList 8 s3Flip8Ops (initBoolList 8 15 m)
  allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) &&
    (getBoolAt st 14 == (m.testBit 0 && decide (m / 2 ≠ 0)))
private def s3Flip8CheckS (m : ℕ) : Bool := microCheckStrict 8 15 s3Flip8Ops (fun m st ↦
  allBelow 8 (fun i ↦ getBoolAt st i == m.testBit i) &&
    (getBoolAt st 14 == (m.testBit 0 && decide (m / 2 ≠ 0)))) m
private theorem s3Flip8Strict_L0_0 : allBelowFrom s3Flip8CheckS 0 32 = true :=
  allBelowFrom_chunks4 0 8 s3Flip8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem s3Flip8Strict_L0_1 : allBelowFrom s3Flip8CheckS 32 32 = true :=
  allBelowFrom_chunks4 32 8 s3Flip8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem s3Flip8Strict_L0_2 : allBelowFrom s3Flip8CheckS 64 32 = true :=
  allBelowFrom_chunks4 64 8 s3Flip8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem s3Flip8Strict_L0_3 : allBelowFrom s3Flip8CheckS 96 32 = true :=
  allBelowFrom_chunks4 96 8 s3Flip8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem s3Flip8Strict_L0_4 : allBelowFrom s3Flip8CheckS 128 32 = true :=
  allBelowFrom_chunks4 128 8 s3Flip8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem s3Flip8Strict_L0_5 : allBelowFrom s3Flip8CheckS 160 32 = true :=
  allBelowFrom_chunks4 160 8 s3Flip8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem s3Flip8Strict_L0_6 : allBelowFrom s3Flip8CheckS 192 32 = true :=
  allBelowFrom_chunks4 192 8 s3Flip8CheckS (by decide) (by decide) (by decide) (by decide)
private theorem s3Flip8Strict_L0_7 : allBelowFrom s3Flip8CheckS 224 32 = true :=
  allBelowFrom_chunks4 224 8 s3Flip8CheckS (by decide) (by decide) (by decide) (by decide)
theorem s3Flip8_eval_ok : allBelow 256 s3Flip8Check = true :=
  allBelow_congr_eq 256 s3Flip8CheckS s3Flip8Check
    (fun m ↦ by simp only [s3Flip8CheckS, s3Flip8Check, microCheckStrict, evalMicroListStrict_eq])
    (allBelowFrom_256 s3Flip8CheckS s3Flip8Strict_L0_0 s3Flip8Strict_L0_1 s3Flip8Strict_L0_2
      s3Flip8Strict_L0_3 s3Flip8Strict_L0_4 s3Flip8Strict_L0_5 s3Flip8Strict_L0_6
        s3Flip8Strict_L0_7)
end ConfigSlot3MicroEngine
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 512
end Slot3MicroEngineAux
end
end ModSlot3MicroEngine

end QuantumComputation.Specs.StoppingPowerSolution
