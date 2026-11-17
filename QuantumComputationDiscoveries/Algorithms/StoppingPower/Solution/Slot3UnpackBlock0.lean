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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.ShiftedMag3Shell

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModStepBBlock0
@[expose] public section
namespace StepBBlock0Alt
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
end StepBBlock0Alt
namespace StepBBlock0
section ConfigStepBBlock0
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
local instance (priority := 1000000) instNeZeroTwoPowStepB0 (k : Nat) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open SpecsAux.DyadicSubgridToeplitz512AndShift
open TwosCompAndWire0Cancel (proj3Axes projAxisField)
open DyadicQft64 Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open MeasureBranchHadamardSem (bit_cases)
open FullSysMomSlots0135Concrete (momCoinReg momCoreWires momSysReg)
open Slot5MatrixAndScaleCert (signBit3)
open MomSlots35Slot3ProjNuclear
  (s3BParCore s3C8Core s3DiteNeg s3DitePos s3Fine30Core s3IteNeg s3ItePos
   s3MomCoreWires_eq s3MomCore_ge_4034 s3S3Core s3U16Core s3U22Core shellMu3)
open MomSlot0CircuitHalf (padZeroBits)
open TempPhaseProg (cnot tempAnd x)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem s3ItePos {c : Prop} [h : Decidable c] {α : Sort _} (hc : c) {t e : α} :
    ite c t e = t := by cases h with | isFalse hn => exact absurd hc hn | isTrue _ => rfl
theorem s3IteNeg {c : Prop} [h : Decidable c] {α : Sort _} (hnc : ¬ c) {t e : α} :
    ite c t e = e := by cases h with | isFalse _ => rfl | isTrue hc => exact absurd hc hnc
theorem s3DitePos {c : Prop} [h : Decidable c] {α : Sort _} (hc : c)
    {t : c → α} {e : ¬ c → α} : dite c t e = t hc :=
  match h with | isTrue _ => rfl | isFalse hn => absurd hc hn
theorem s3DiteNeg {c : Prop} [h : Decidable c] {α : Sort _} (hnc : ¬ c)
    {t : c → α} {e : ¬ c → α} : dite c t e = e hnc :=
  match h with | isFalse _ => rfl | isTrue hc => absurd hc hnc
theorem s3DisjConcatLeft {k m p n : ℕ} {r : QRegister k n} {s : QRegister m n}
    {w : QRegister p n} {hrs : r.DisjointWires s} (hrw : r.DisjointWires w)
    (hsw : s.DisjointWires w) : (r.concat s hrs).DisjointWires w := by
  rw [QRegister.disjoint_iff]
  intro i j
  cases h : finSumFinEquiv.symm i with
  | inl i₁ => simpa [QRegister.concat, h] using hrw.ne i₁ j
  | inr i₂ => simpa [QRegister.concat, h] using hsw.ne i₂ j
theorem zmod2_eq_zero_or_one (b : ZMod 2) : b = 0 ∨ b = 1 := bit_cases b
theorem s3LtTrans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := Nat.lt_trans h1 h2
theorem s3LtLe {a b c : ℕ} (h1 : a < b) (h2 : b ≤ c) : a < c := Nat.lt_of_lt_of_le h1 h2
section Slot3ArithCombinators
theorem bitsVal_succ_split {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
    bitsVal f = (f 0).val + 2 * bitsVal (fun j ↦ f j.succ) :=
  Slot3MicroEngineAux.bitsVal_succ_split f
theorem bitsVal_castSucc_split {W : ℕ} (f : Fin (W + 1) → ZMod 2) :
    bitsVal f = bitsVal (fun j : Fin W ↦ f j.castSucc) + 2 ^ W * (f (Fin.last W)).val := by
  rw [bitsVal, Fin.sum_univ_castSucc]
  simp [bitsVal, mul_comm]
theorem bitsVal_injective : ∀ {W : ℕ}, Function.Injective (bitsVal (q := W)) :=
  @Slot3MicroEngineAux.bitsVal_injective
theorem bitsVal_eq_of_testBit {W : ℕ} (f : Fin W → ZMod 2) (v : ℕ) (hv : v < 2 ^ W)
    (h : ∀ j : Fin W, f j = if v.testBit j.val then 1 else 0) : bitsVal f = v :=
  Slot3MicroEngineAux.bitsVal_eq_of_testBit f v hv h
def xVec {M : ℕ} : (W : ℕ) → (Fin W → Wire M) → CliffProg M
  | 0, _ => .nil
  | W + 1, dst => .seq (.x (dst 0)) (xVec W (fun j ↦ dst j.succ))
theorem xVec_supportsBelow {M bound : ℕ} :
    ∀ (W : ℕ) (dst : Fin W → Wire M),
      (∀ j, (dst j).val < bound) → (xVec W dst).SupportsBelow bound
  | 0, _, _ => trivial
  | W + 1, _dst, h => ⟨h 0, xVec_supportsBelow W _ (fun j ↦ h j.succ)⟩
theorem xVec_disjoint {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (W : ℕ) (dst : Fin W → Wire M),
      (∀ j, ¬ mutW (dst j)) → CliffDisjoint mutW (xVec W dst)
  | 0, _, _ => trivial
  | W + 1, _dst, h => ⟨h 0, xVec_disjoint W _ (fun j ↦ h j.succ)⟩
def cnotVec {M : ℕ} :
    (W : ℕ) → (src dst : Fin W → Wire M) → (∀ j, src j ≠ dst j) → CliffProg M
  | 0, _, _, _ => .nil
  | W + 1, src, dst, hne =>
      .seq (.cnot (src 0) (dst 0) (hne 0))
        (cnotVec W (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
private theorem stepB0_cnotVec_eq_s3m {M : ℕ} :
    ∀ (W : ℕ) (src dst : Fin W → Wire M) (hne : ∀ j, src j ≠ dst j),
      cnotVec W src dst hne = Slot3MicroEngineAux.cnotVec W src dst hne
  | 0, _, _, _ => rfl
  | W + 1, _, _, _ => congrArg _ (stepB0_cnotVec_eq_s3m W _ _ _)
theorem cnotVec_eval {M : ℕ} :
    ∀ (W : ℕ) (src dst : Fin W → Wire M) (hne : ∀ j, src j ≠ dst j)
      (_ : Function.Injective dst) (_ : ∀ i j, src i ≠ dst j)
      (β : BitAssignment M) (w : Wire M),
      (cnotVec W src dst hne).eval β w =
        if h : ∃ j, w = dst j then β w + β (src h.choose) else β w := by
  intro W src dst hne hinj hdisj β w
  rw [stepB0_cnotVec_eq_s3m]
  exact Slot3MicroEngineAux.cnotVec_eval W src dst hne hinj hdisj β w
theorem TempCtx.fwdBits_mut {M : ℕ} {mutW : Wire M → Prop}
    {K : TempCtx M} (hDisj : K.DisjointFrom mutW) :
    ∀ (β : BitAssignment M) {w : Wire M}, mutW w → K.fwdBits β w = β w :=
  Slot3MicroEngineAux.TempCtx.fwdBits_mut hDisj
theorem xorBlock_of_ctx {M curStart curEnd W : ℕ} [NeZero M]
    (hEnd : curEnd ≤ M) (hStart : curStart ≤ curEnd)
    (out : Fin W → Wire M) (hout_lt : ∀ j, (out j).val < curStart)
    (hout_inj : Function.Injective out)
    (src : Fin W → Wire M) (hsrc_ge : ∀ j, curStart ≤ (src j).val)
    (K : TempCtx M)
    (hDisj : K.DisjointFrom (fun w ↦ ∃ j, w = out j))
    (hSupp : K.SupportsBelowCtx curEnd)
    (setup : BitAssignment M → BitAssignment M)
    (hProbe : ∀ q : Wire M, ScopedBlock M (M - curStart) setup (.z q) (K.plug (.z q))) :
    let hne : ∀ j, src j ≠ out j := fun j ↦ wire_ne_of_gt (s3LtLe (hout_lt j) (hsrc_ge j))
    let p := K.plug (.cliff (cnotVec W src out hne))
    ValidCleanRem M (M - curStart) p ∧
      p.countTempAnd = K.countTempAnd ∧
      (∀ β : BitAssignment M, cleanRem M (M - curStart) β → p.evalSign β = 0) ∧
      (∀ β : BitAssignment M, cleanRem M (M - curStart) β → ∀ w : Wire M,
        p.evalBits β w = if h : ∃ j, w = out j then β w + setup β (src h.choose) else β w) := by
  dsimp only
  rw [stepB0_cnotVec_eq_s3m]
  exact Slot3MicroEngineAux.xorBlock_of_ctx hEnd hStart out hout_lt hout_inj src hsrc_ge K hDisj
    hSupp setup hProbe
def ctxFullAdd {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin)
    (ha : a.val < cur) (hb : b.val < cur) (hc : cin.val < cur) : TempCtx M :=
  let sumWire : Wire M := ⟨cur, by omega⟩
  let coutWire : Wire M := ⟨cur + 1, by omega⟩
  let cPre : CliffProg M := .seq (.cnot cin a hac.symm) (.cnot cin b hbc.symm)
  let cInner : CliffProg M :=
    .seq (.cnot cin b hbc.symm)
      (.seq (.cnot cin a hac.symm)
        (.seq (.cnot cin coutWire (wire_ne_of_lt (by dsimp [coutWire]; omega)))
          (.seq (.cnot a sumWire (wire_ne_of_lt (by dsimp [sumWire]; omega)))
            (.seq (.cnot b sumWire (wire_ne_of_lt (by dsimp [sumWire]; omega)))
              (.cnot cin sumWire (wire_ne_of_lt (by dsimp [sumWire]; omega)))))))
  (ctxCliffAlloc cPre).append
    ((ctxTempBit a b coutWire hab
        (wire_ne_of_lt (by dsimp [coutWire]; omega))
        (wire_ne_of_lt (by dsimp [coutWire]; omega))).append
      (ctxCliffAlloc cInner))
theorem ctxFullAdd_plug {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b cin : Wire M)
    (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur) (hb : b.val < cur)
    (hc : cin.val < cur) (body : TempPhaseProg M) :
    (ctxFullAdd cur hcur a b cin hab hac hbc ha hb hc).plug body = withFullAdd cur hcur a b
    cin hab hac hbc ha hb hc body := by
  simp only [ctxFullAdd, withFullAdd, TempCtx.append_plug, ctxCliffAlloc_plug, ctxTempBit_plug]
theorem ctxFullAdd_props {M : ℕ} {mutW : Wire M → Prop}
    (cur : ℕ) (hcur : cur + 2 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin)
    (ha : a.val < cur) (hb : b.val < cur) (hc : cin.val < cur)
    (hna : ¬ mutW a) (hnb : ¬ mutW b) (hnc : ¬ mutW cin)
    (hn0 : ¬ mutW ⟨cur, by omega⟩) (hn1 : ¬ mutW ⟨cur + 1, by omega⟩) :
    (ctxFullAdd cur hcur a b cin hab hac hbc ha hb hc).DisjointFrom mutW ∧
    (ctxFullAdd cur hcur a b cin hab hac hbc ha hb hc).SupportsBelowCtx (cur + 2) := by
  dsimp only [ctxFullAdd]
  exact ⟨TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint ⟨⟨hnc, hna⟩, ⟨hnc, hnb⟩⟩)
      (TempCtx.disjointFrom_append ⟨hna, hnb, hn1, trivial⟩
        (ctxCliffAlloc_disjoint
          ⟨⟨hnc, hnb⟩, ⟨hnc, hna⟩, ⟨hnc, hn1⟩, ⟨hna, hn0⟩, ⟨hnb, hn0⟩, ⟨hnc, hn0⟩⟩)),
    TempCtx.supportsBelowCtx_append le_rfl
      (ctxCliffAlloc_supports ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩)
      (TempCtx.supportsBelowCtx_append le_rfl ⟨by dsimp; omega, trivial⟩
        (ctxCliffAlloc_supports
          ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by dsimp; omega⟩,
            ⟨by omega, by dsimp; omega⟩, ⟨by omega, by dsimp; omega⟩,
            ⟨by omega, by dsimp; omega⟩⟩))⟩
def ctxRippleAddCarry {M : ℕ} :
    (W cur : ℕ) → (hcur : cur + 2 * W ≤ M) →
    (a b : Fin W → Wire M) → (cin : Wire M) →
    (∀ j, a j ≠ b j) → (∀ j, a j ≠ cin) → (∀ j, b j ≠ cin) →
    (∀ j, (a j).val < cur) → (∀ j, (b j).val < cur) → (cin.val < cur) →
    TempCtx M
  | 0, _, _, _, _, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, hcur, a, b, cin, hab, hac, hbc, ha, hb, hc =>
      let cinNext : Wire M := ⟨cur + 1, by omega⟩
      (ctxFullAdd cur (by omega) (a 0) (b 0) cin (hab 0) (hac 0) (hbc 0) (ha 0) (hb 0) hc).append
        (ctxRippleAddCarry W (cur + 2) (by omega)
          (fun j ↦ a j.succ) (fun j ↦ b j.succ) cinNext
          (fun j ↦ hab j.succ)
          (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp [cinNext]; omega))
          (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp [cinNext]; omega))
          (fun j ↦ s3LtTrans (ha j.succ) (by omega))
          (fun j ↦ s3LtTrans (hb j.succ) (by omega))
          (by dsimp [cinNext]; omega))
theorem ctxRippleAddCarry_plug {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + 2 * W ≤ M)
      (a b : Fin W → Wire M) (cin : Wire M)
      (hab : ∀ j, a j ≠ b j) (hac : ∀ j, a j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (hc : cin.val < cur)
      (body : TempPhaseProg M),
      (ctxRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc).plug body =
        withRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc body
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, a, b, cin, hab, hac, hbc, ha, hb, hc, body => by
      dsimp only [ctxRippleAddCarry, withRippleAddCarry]
      rw [TempCtx.append_plug, ctxFullAdd_plug, ctxRippleAddCarry_plug]
theorem ctxRippleAddCarry_countTempAnd {M : ℕ} (W cur : ℕ) (hcur : cur + 2 * W ≤ M)
    (a b : Fin W → Wire M) (cin : Wire M) (hab : ∀ j, a j ≠ b j) (hac : ∀ j, a j ≠ cin)
    (hbc : ∀ j, b j ≠ cin) (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur)
    (hc : cin.val < cur) : (ctxRippleAddCarry W cur hcur a b cin hab hac hbc ha hb
    hc).countTempAnd = W := by
  have h1 := TempCtx.plug_countTempAnd
    (ctxRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc) .nil
  rw [ctxRippleAddCarry_plug, withRippleAddCarry_countTempAnd] at h1
  dsimp [TempPhaseProg.countTempAnd] at h1
  omega
theorem TempCtx.supportsBelowCtx_mono {M b₁ b₂ : ℕ} (hle : b₁ ≤ b₂) {K : TempCtx M} :
    K.SupportsBelowCtx b₁ → K.SupportsBelowCtx b₂ :=
  Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono hle
theorem ctxRippleAddCarry_props {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (W cur : ℕ) (hcur : cur + 2 * W ≤ M)
      (a b : Fin W → Wire M) (cin : Wire M)
      (hab : ∀ j, a j ≠ b j) (hac : ∀ j, a j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (hc : cin.val < cur),
      (∀ j, ¬ mutW (a j)) → (∀ j, ¬ mutW (b j)) → ¬ mutW cin →
      (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      (ctxRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc).DisjointFrom mutW ∧
      (ctxRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc).SupportsBelowCtx (cur + 2 * W)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => ⟨trivial, trivial⟩
  | W + 1, cur, hcur, a, b, cin, hab, hac, hbc, ha, hb, hc, hna, hnb, hnc, hncur => by
      obtain ⟨hd0, hs0⟩ := ctxFullAdd_props (mutW := mutW) cur (by omega)
        (a 0) (b 0) cin (hab 0) (hac 0) (hbc 0) (ha 0) (hb 0) hc
        (hna 0) (hnb 0) hnc
        (hncur _ (by dsimp; omega)) (hncur _ (by dsimp; omega))
      obtain ⟨hdRest, hsRest⟩ := ctxRippleAddCarry_props (mutW := mutW) W (cur + 2) (by omega)
        (fun j ↦ a j.succ) (fun j ↦ b j.succ) ⟨cur + 1, by omega⟩
        (fun j ↦ hab j.succ)
        (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp; omega))
        (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp; omega))
        (fun j ↦ s3LtTrans (ha j.succ) (by omega))
        (fun j ↦ s3LtTrans (hb j.succ) (by omega))
        (by dsimp; omega)
        (fun j ↦ hna j.succ) (fun j ↦ hnb j.succ)
        (hncur _ (by dsimp; omega)) (fun w hw ↦ hncur w (by omega))
      exact ⟨TempCtx.disjointFrom_append hd0 hdRest, TempCtx.supportsBelowCtx_append
        (by omega) hs0 (TempCtx.supportsBelowCtx_mono (by omega) hsRest)⟩
def ctxLtStep {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev) : TempCtx M
    :=
  let out : Wire M := ⟨cur, by omega⟩
  let cPre : CliffProg M := .seq (.cnot b a hab.symm) (.cnot prev b hbp.symm)
  let cPost : CliffProg M :=
    .seq (.cnot prev b hbp.symm)
      (.seq (.cnot b a hab.symm)
        (.cnot prev out (wire_ne_of_lt (by dsimp [out]; omega))))
  (ctxCliffAlloc cPre).append
    ((ctxTempBit a b out hab
        (wire_ne_of_lt (by dsimp [out]; omega))
        (wire_ne_of_lt (by dsimp [out]; omega))).append
      (ctxCliffAlloc cPost))
theorem ctxLtStep_plug {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b prev : Wire M)
    (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev)
    (body : TempPhaseProg M) : (ctxLtStep cur hcur a b prev hab ha hb hp hbp).plug body =
    withLtStep cur hcur a b prev hab ha hb hp hbp body := by
  simp only [ctxLtStep, withLtStep, TempCtx.append_plug, ctxCliffAlloc_plug, ctxTempBit_plug]
theorem ctxLtStep_props {M : ℕ} {mutW : Wire M → Prop}
    (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b prev : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (hp : prev.val < cur) (hbp : b ≠ prev)
    (hna : ¬ mutW a) (hnb : ¬ mutW b) (hnp : ¬ mutW prev) (hno : ¬ mutW ⟨cur, by omega⟩) :
    (ctxLtStep cur hcur a b prev hab ha hb hp hbp).DisjointFrom mutW ∧
    (ctxLtStep cur hcur a b prev hab ha hb hp hbp).SupportsBelowCtx (cur + 1) :=
  Slot3MicroEngineAux.ctxLtStep_props cur hcur a b prev hab ha hb hp hbp hna hnb hnp hno
def ctxLtCompLoop {M : ℕ} :
    (W cur : ℕ) → (hcur : cur + W + 1 ≤ M) →
    (a b : Fin W → Wire M) → (hab : ∀ j, a j ≠ b j) →
    (ha : ∀ j, (a j).val < cur) → (hb : ∀ j, (b j).val < cur) →
    TempCtx M
  | 0, _, _, _, _, _, _, _ => .hole
  | W + 1, cur, hcur, a, b, hab, ha, hb =>
      let prev : Wire M := ⟨cur, by omega⟩
      (ctxLtStep (cur + 1) (by omega) (a 0) (b 0) prev (hab 0)
        (s3LtTrans (ha 0) (by omega)) (s3LtTrans (hb 0) (by omega))
        (by dsimp [prev]; omega)
        (wire_ne_of_lt (by have := hb 0; dsimp [prev]; omega))).append
        (ctxLtCompLoop W (cur + 1) (by omega)
          (fun j ↦ a j.succ) (fun j ↦ b j.succ) (fun j ↦ hab j.succ)
          (fun j ↦ s3LtTrans (ha j.succ) (by omega))
          (fun j ↦ s3LtTrans (hb j.succ) (by omega)))
theorem ctxLtCompLoop_plug {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
      (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (body : TempPhaseProg M),
      (ctxLtCompLoop W cur hcur a b hab ha hb).plug body =
        withLtCompLoop W cur hcur a b hab ha hb body
  | 0, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, a, b, hab, ha, hb, body => by
      dsimp only [ctxLtCompLoop, withLtCompLoop]
      rw [TempCtx.append_plug, ctxLtStep_plug, ctxLtCompLoop_plug]
private theorem stepB0_ctxLtCompLoop_eq_s3m {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur),
      ctxLtCompLoop W cur hcur a b hab ha hb =
        Slot3MicroEngineAux.ctxLtCompLoop W cur hcur a b hab ha hb
  | 0, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, _, _, _, _, _, _ => by
      dsimp only [ctxLtCompLoop, Slot3MicroEngineAux.ctxLtCompLoop]
      exact congrArg _ (stepB0_ctxLtCompLoop_eq_s3m W (cur + 1) _ _ _ _ _ _)
theorem ctxLtCompLoop_countTempAnd {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j) (ha : ∀ j, (a j).val < cur)
    (hb : ∀ j, (b j).val < cur) : (ctxLtCompLoop W cur hcur a b hab ha hb).countTempAnd = W
    := by
  rw [stepB0_ctxLtCompLoop_eq_s3m]
  exact Slot3MicroEngineAux.ctxLtCompLoop_countTempAnd W cur hcur a b hab ha hb
theorem ctxLtCompLoop_props {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
      (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur),
      (∀ j, ¬ mutW (a j)) → (∀ j, ¬ mutW (b j)) →
      (∀ w : Wire M, cur ≤ w.val → ¬ mutW w) →
      (ctxLtCompLoop W cur hcur a b hab ha hb).DisjointFrom mutW ∧
      (ctxLtCompLoop W cur hcur a b hab ha hb).SupportsBelowCtx (cur + W + 1) := by
  intro W cur hcur a b hab ha hb hna hnb hncur
  rw [stepB0_ctxLtCompLoop_eq_s3m]
  exact Slot3MicroEngineAux.ctxLtCompLoop_props W cur hcur a b hab ha hb hna hnb hncur
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
theorem ctxFullAdd_fwdBits {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (a b cin : Wire M)
    (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin) (ha : a.val < cur) (hb : b.val < cur)
    (hc : cin.val < cur) (β : BitAssignment M) (hβ : cleanRem M (M - cur) β) :
    (ctxFullAdd cur hcur a b cin hab hac hbc ha hb hc).fwdBits β = fullAddSetup cur hcur a b
    cin β := by
  funext u
  have hBlk := ScopedBlock.withFullAdd_block cur hcur a b cin hab hac hbc ha hb hc
    (ScopedBlock.z_kick u)
  rw [← ctxFullAdd_plug] at hBlk
  exact TempCtx.fwdBits_eq_of_block _ u hBlk β hβ
theorem ctxRippleAddCarry_scoped {M : ℕ} (W cur : ℕ) (hcur : cur + 2 * W ≤ M)
    (a b : Fin W → Wire M) (cin : Wire M)
    (hab : ∀ j, a j ≠ b j) (hac : ∀ j, a j ≠ cin) (hbc : ∀ j, b j ≠ cin)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (hc : cin.val < cur) :
    let K := ctxRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc
    (∀ q : Wire M, ScopedBlock M (M - cur) K.fwdBits (.z q) (K.plug (.z q))) ∧
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      cleanRem M (M - (cur + 2 * W)) (K.fwdBits β) ∧
      (∀ w : Wire M, w.val < cur → K.fwdBits β w = β w) ∧
      bitsVal (fun k ↦ K.fwdBits β (rippleAddCarryWires W cur hcur cin k)) =
        bitsVal (fun j ↦ β (a j)) + bitsVal (fun j ↦ β (b j)) + (β cin).val) := by
  intro K
  refine ⟨TempCtx.scopedBlock_fwdBits K fun q ↦ ?_, ?_⟩
  · obtain ⟨sQ, hBlkQ, _⟩ := ScopedBlock.withRippleAddCarry_block W cur hcur a b cin
      hab hac hbc ha hb hc (.z q) (.z q) id (ScopedBlock.z_kick q)
    rw [← ctxRippleAddCarry_plug] at hBlkQ
    exact ⟨sQ, hBlkQ⟩
  · induction W generalizing cur cin with
    | zero =>
        intro β hβ
        exact ⟨by dsimp [K, ctxRippleAddCarry, TempCtx.fwdBits]; exact hβ, fun _ _ ↦ rfl,
          by simp [K, ctxRippleAddCarry, TempCtx.fwdBits, rippleAddCarryWires, bitsVal]⟩
    | succ W ih =>
        intro β hβ
        dsimp only [K, ctxRippleAddCarry]
        rw [TempCtx.append_fwdBits, ctxFullAdd_fwdBits cur (by omega) (a 0) (b 0) cin
          (hab 0) (hac 0) (hbc 0) (ha 0) (hb 0) hc β hβ]
        let cinNext : Wire M := ⟨cur + 1, by omega⟩
        let β₁ := fullAddSetup cur (by omega) (a 0) (b 0) cin β
        have hβ₁_lt (u : Wire M) (hu : u.val < cur) : β₁ u = β u := by
          dsimp only [β₁, fullAddSetup]
          rw [Function.update_of_ne (wire_ne_of_lt (show u.val < cur + 1 by omega)),
            Function.update_of_ne (wire_ne_of_lt hu)]
        have hβ₁_clean : cleanRem M (M - (cur + 2)) β₁ := fun w hw ↦ by
          dsimp only [β₁, fullAddSetup]
          rw [Function.update_of_ne (wire_ne_of_gt (show cur + 1 < w.val by omega)),
            Function.update_of_ne (wire_ne_of_gt (show cur < w.val by omega))]
          exact hβ w (by omega)
        have ha' (j : Fin W) : (a j.succ).val < cur + 2 := lt_trans (ha j.succ) (by omega)
        have hb' (j : Fin W) : (b j.succ).val < cur + 2 := lt_trans (hb j.succ) (by omega)
        have hac' (j : Fin W) : a j.succ ≠ cinNext :=
          wire_ne_of_lt (lt_trans (ha j.succ) (by dsimp [cinNext]; omega))
        have hbc' (j : Fin W) : b j.succ ≠ cinNext :=
          wire_ne_of_lt (lt_trans (hb j.succ) (by dsimp [cinNext]; omega))
        obtain ⟨hcl, hbelow, hsum_ih⟩ := ih (cur + 2) (by omega) (fun j ↦ a j.succ)
          (fun j ↦ b j.succ) cinNext (fun j ↦ hab j.succ) hac' hbc' ha' hb'
          (by dsimp [cinNext]; omega) β₁ hβ₁_clean
        set KInner := ctxRippleAddCarry W (cur + 2) (by omega) (fun j ↦ a j.succ)
          (fun j ↦ b j.succ) cinNext (fun j ↦ hab j.succ) hac' hbc' ha' hb'
          (by dsimp [cinNext]; omega)
        have hsum0 : KInner.fwdBits β₁ ⟨cur, by omega⟩ = β (a 0) + β (b 0) + β cin := by
          rw [hbelow ⟨cur, by omega⟩ (show cur < cur + 2 by omega)]
          dsimp only [β₁, fullAddSetup]
          rw [Function.update_of_ne (wire_ne_of_lt (show cur < cur + 1 by omega)),
            Function.update_self]
        refine ⟨show cleanRem M (M - (cur + 2 * (W + 1))) (KInner.fwdBits β₁) from
            (show cur + 2 + 2 * W = cur + 2 * (W + 1) by omega) ▸ hcl,
          fun w hw ↦ (hbelow w (by omega)).trans (hβ₁_lt w hw), ?_⟩
        dsimp only [rippleAddCarryWires]
        rw [bitsVal_succ_split]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hcin1 : β₁ cinNext = β cin + (β (a 0) + β cin) * (β (b 0) + β cin) :=
          Function.update_self _ _ _
        rw [hsum0, hsum_ih, funext fun j : Fin W ↦ hβ₁_lt (a j.succ) (ha j.succ),
          funext fun j : Fin W ↦ hβ₁_lt (b j.succ) (hb j.succ),
          hcin1,
          bitsVal_succ_split (fun j ↦ β (a j)), bitsVal_succ_split (fun j ↦ β (b j))]
        have hfa := fullAdd_val_eq (β (a 0)) (β (b 0)) (β cin)
        omega
theorem ctxLtCompLoop_scoped {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) :
    let K := ctxLtCompLoop W cur hcur a b hab ha hb
    (∀ q : Wire M, ScopedBlock M (M - (cur + 1)) K.fwdBits (.z q) (K.plug (.z q))) ∧
    (∀ β : BitAssignment M, cleanRem M (M - cur) β →
      ((K.fwdBits β ⟨cur + W, by omega⟩ = 1) ↔
        bitsVal (fun j ↦ β (a j)) < bitsVal (fun j ↦ β (b j)))) := by
  intro K
  refine ⟨TempCtx.scopedBlock_fwdBits K fun q ↦ ?_, fun β hβ ↦ ?_⟩
  · obtain ⟨sQ, hBlkQ, _⟩ := ScopedBlock.withLtCompLoop_block W cur hcur a b hab ha hb
      (.z q) (.z q) id (ScopedBlock.z_kick q)
    rw [← ctxLtCompLoop_plug] at hBlkQ
    exact ⟨sQ, hBlkQ⟩
  · dsimp only [K]
    rw [stepB0_ctxLtCompLoop_eq_s3m]
    exact ((Slot3MicroEngineAux.ctxLtCompLoop_scoped W cur hcur a b hab ha hb).2 β hβ).2
theorem withCliffAlloc_valid_and_eval {M rem remIn : ℕ} (hremIn : remIn ≤ M)
    (hle : remIn ≤ rem) (c : CliffProg M) (hc : c.SupportsBelow (M - remIn))
    (body : TempPhaseProg M) (hvBody : ValidCleanRem M remIn body) : ValidCleanRem M rem
    (withCliffAlloc c body) ∧ (∀ β : BitAssignment M, cleanRem M rem β → cleanRem M remIn
    (c.eval β) ∧ (withCliffAlloc c body).evalSign β = body.evalSign (c.eval β) ∧
    (withCliffAlloc c body).evalBits β = c.inv.eval (body.evalBits (c.eval β))) := by
  have hc_clean : ∀ β : BitAssignment M, cleanRem M rem β → cleanRem M remIn (c.eval β) :=
    fun β hβ w hw ↦ by
      rw [c.eval_outside hc β w hw]
      exact hβ w (by omega)
  refine ⟨⟨remIn, hremIn, trivial, ⟨0, Nat.zero_le M, hvBody, trivial, fun _ _ _ hw ↦ absurd
    hw (by omega)⟩, fun β hβ w hw ↦ hc_clean β hβ w hw⟩, fun β hβ ↦ ⟨hc_clean β hβ, ?_, rfl⟩⟩
  simp [withCliffAlloc, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
theorem zmod2_add_self_cancel (a b : ZMod 2) : a + b + b = a := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> decide
def TempCtxLiftEx {M : ℕ} (cur next : ℕ) (K : TempCtx M) : Prop :=
  ∀ {leaf body : TempPhaseProg M} {sBody : BitAssignment M → BitAssignment M},
    ScopedBlock M (M - next) sBody leaf body →
    ∃ sOut, ScopedBlock M (M - cur) sOut leaf (K.plug body)
theorem TempCtxLiftEx.probe {M cur next : ℕ} {K : TempCtx M}
    (hK : TempCtxLiftEx cur next K) (q : Wire M) :
    ScopedBlock M (M - cur) K.fwdBits (.z q) (K.plug (.z q)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.probe hK q
theorem TempCtxLiftEx.mono {M cur₀ cur₁ next₀ next₁ : ℕ} {K : TempCtx M}
    (hc : cur₀ ≤ cur₁) (hn : next₀ ≤ next₁) (hM : next₁ ≤ M)
    (hK : TempCtxLiftEx cur₁ next₀ K) :
    TempCtxLiftEx cur₀ next₁ K :=
  Slot3MicroEngineAux.TempCtxLiftEx.mono hK hc hn hM
theorem TempCtxLiftEx.append {M cur mid next : ℕ} {F G : TempCtx M}
    (hF : TempCtxLiftEx cur mid F) (hG : TempCtxLiftEx mid next G) :
    TempCtxLiftEx cur next (F.append G) :=
  Slot3MicroEngineAux.TempCtxLiftEx.append hF hG
theorem TempCtxLiftEx.cliff {M cur : ℕ} (hcur : cur ≤ M) (c : CliffProg M)
    (hc : c.SupportsBelow cur) :
    TempCtxLiftEx cur cur (ctxCliffAlloc c) :=
  Slot3MicroEngineAux.TempCtxLiftEx.cliff cur hcur c hc
theorem TempCtxLiftEx.tempBit {M cur : ℕ} (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) : TempCtxLiftEx cur (cur + 1)
    (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.tempBit cur hcur c₁ c₂ h12 hc1 hc2
theorem TempCtxLiftEx.rippleAddCarry {M : ℕ} (W cur : ℕ) (hcur : cur + 2 * W ≤ M)
    (a b : Fin W → Wire M) (cin : Wire M)
    (hab : ∀ j, a j ≠ b j) (hac : ∀ j, a j ≠ cin) (hbc : ∀ j, b j ≠ cin)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (hc : cin.val < cur) :
    TempCtxLiftEx cur (cur + 2 * W) (ctxRippleAddCarry W cur hcur a b cin hab hac hbc ha hb hc) :=
  fun {leaf body sBody} hBody ↦ by
    obtain ⟨s, h, _⟩ := ScopedBlock.withRippleAddCarry_block W cur hcur a b cin
      hab hac hbc ha hb hc leaf body sBody hBody
    rw [← ctxRippleAddCarry_plug] at h
    exact ⟨fun β ↦ sBody (s β), h⟩
theorem TempCtxLiftEx.ltCompLoop {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
    (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) :
    TempCtxLiftEx cur (cur + W + 1) (ctxLtCompLoop W cur hcur a b hab ha hb) := by
  rw [stepB0_ctxLtCompLoop_eq_s3m]
  exact Slot3MicroEngineAux.TempCtxLiftEx.ltCompLoop W cur hcur a b hab ha hb
theorem bitsVal_slice_linear {N W k : ℕ} (hk : k + W ≤ N)
    (g g' : Fin N → ZMod 2)
    (hout : ∀ m : Fin N, (m.val < k ∨ k + W ≤ m.val) → g' m = g m) :
    bitsVal g' + 2 ^ k * bitsVal (fun j : Fin W ↦ g ⟨k + j.val, by omega⟩) =
      bitsVal g + 2 ^ k * bitsVal (fun j : Fin W ↦ g' ⟨k + j.val, by omega⟩) ∧
    2 ^ k * bitsVal (fun j : Fin W ↦ g ⟨k + j.val, by omega⟩) ≤ bitsVal g := by
  let emb : Fin W ↪ Fin N := ⟨fun j ↦ ⟨k + j.val, by omega⟩, fun i j h ↦ by
    have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega)⟩
  let S : Finset (Fin N) := Finset.univ.map emb
  have hmem_S : ∀ m : Fin N, m ∈ S ↔ k ≤ m.val ∧ m.val < k + W := by
    intro m; simp only [S, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩; dsimp [emb]; omega
    · rintro ⟨h1, h2⟩; exact ⟨⟨m.val - k, by omega⟩, Fin.ext (by dsimp [emb]; omega)⟩
  have split_any : ∀ f : Fin N → ZMod 2, bitsVal f = 2 ^ k * bitsVal
      (fun j : Fin W ↦ f (emb j)) + ∑ m ∈ Finset.univ \ S, (f m).val * 2 ^ m.val := by
    intro f
    have hpart : (∑ m ∈ S, (f m).val * 2 ^ m.val) +
        (∑ m ∈ Finset.univ \ S, (f m).val * 2 ^ m.val) = bitsVal f := by
      simpa [bitsVal] using Finset.sum_sdiff (s₁ := S) (s₂ := Finset.univ) (Finset.subset_univ S)
        (f := fun m ↦ (f m).val * 2 ^ m.val) |> Eq.symm |> fun h ↦ by omega
    have hmap : ∑ m ∈ S, (f m).val * 2 ^ m.val =
        2 ^ k * bitsVal (fun j : Fin W ↦ f (emb j)) := by
      rw [Finset.sum_map, bitsVal, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      dsimp [emb]; rw [pow_add]; ring
    omega
  have hrest_eq : (∑ m ∈ Finset.univ \ S, (g' m).val * 2 ^ m.val) =
      ∑ m ∈ Finset.univ \ S, (g m).val * 2 ^ m.val := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hmem_S] at hm
    rw [hout m (by omega)]
  have hg := split_any g
  have hg' := split_any g'
  dsimp [emb] at hg hg'
  omega
end Slot3ArithCombinators
theorem TempCtx.append_countTempAnd {M : ℕ} (F G : TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd :=
  Slot3MicroEngineAux.TempCtx.append_countTempAnd F G
theorem seqClean_spec {M cur : ℕ} (hcur : cur ≤ M) {p₁ p₂ : TempPhaseProg M}
    (hv₁ : ValidCleanRem M (M - cur) p₁) (hv₂ : ValidCleanRem M (M - cur) p₂)
    (hs₁ : ∀ β, cleanRem M (M - cur) β → p₁.evalSign β = 0)
    (hs₂ : ∀ β, cleanRem M (M - cur) β → p₂.evalSign β = 0) (hcl₁ : ∀ β, cleanRem M (M - cur)
    β → cleanRem M (M - cur) (p₁.evalBits β)) (hcl₂ : ∀ β, cleanRem M (M - cur) β → cleanRem M
    (M - cur) (p₂.evalBits β)) : ValidCleanRem M (M - cur) (.seq p₁ p₂) ∧
    (TempPhaseProg.seq p₁ p₂).countTempAnd = p₁.countTempAnd + p₂.countTempAnd ∧ (∀ β,
    cleanRem M (M - cur) β → (TempPhaseProg.seq p₁ p₂).evalSign β = 0) ∧ (∀ β, cleanRem M (M -
    cur) β → cleanRem M (M - cur) ((TempPhaseProg.seq p₁ p₂).evalBits β)) ∧ (∀ β,
    (TempPhaseProg.seq p₁ p₂).evalBits β = p₂.evalBits (p₁.evalBits β)) := by
  refine ⟨⟨M - cur, by omega, hv₁, hv₂, hcl₁⟩, rfl, fun β hβ ↦ ?_, fun β hβ ↦ ?_, fun _ ↦ rfl⟩
  · change p₁.evalSign β + p₂.evalSign (p₁.evalBits β) = 0
    rw [hs₁ β hβ, hs₂ _ (hcl₁ β hβ)]
    rfl
  · exact hcl₂ _ (hcl₁ β hβ)
def shellTop7Mu (t : Fin 128) : ℕ := if t.val < 2 then 0 else if t.val < 4 then 1 else if
    t.val < 8 then 2 else if t.val < 16 then 3 else if t.val < 32 then 4 else if t.val < 64
    then 5 else 6
theorem bitsVal_split_add :
    ∀ (A B : ℕ) (h : Fin (A + B) → ZMod 2),
      bitsVal h = bitsVal (fun i : Fin A ↦ h ⟨i.val, by omega⟩) +
        2 ^ A * bitsVal (fun j : Fin B ↦ h ⟨A + j.val, by omega⟩) := fun A B h ↦ by
  unfold bitsVal
  rw [Fin.sum_univ_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp [Fin.natAdd]
  rw [pow_add]
  ring
theorem bitsVal_top7_of_22 (f : Fin 22 → ZMod 2) :
    bitsVal (fun i : Fin 7 ↦ f ⟨15 + i.val, by omega⟩) = bitsVal f / 32768 := by
  have hsp := bitsVal_split_add 15 7 f
  have hlt : bitsVal (fun i : Fin 15 ↦ f ⟨i.val, by omega⟩) < 2 ^ 15 := bitsVal_lt_two_pow _
  rw [show (2 : ℕ) ^ 15 = 32768 by decide] at hsp hlt
  omega
theorem shellTop7Mu_eq_shellMu3 (u22 : Fin 4194304) :
    shellTop7Mu ⟨u22.val / 32768, by have := u22.isLt; omega⟩ = shellMu3 u22 := by
  unfold shellTop7Mu shellMu3
  dsimp only
  split_ifs <;> { dsimp -failIfUnchanged only [Fin.val_mk] at *; all_goals omega }
theorem u22_testBit_eq_wire {M : ℕ} (u22W : Fin 22 → Wire M) (β : BitAssignment M)
    (u22 : Fin 4194304) (hu : bitsVal (fun i ↦ β (u22W i)) = u22.val) (idx : Fin 22) :
    β (u22W idx) = if u22.val.testBit idx.val then 1 else 0 := by
  let g : Fin 22 → ZMod 2 := fun j ↦ if u22.val.testBit j.val then 1 else 0
  have hg : bitsVal g = u22.val := bitsVal_eq_of_testBit g u22.val u22.isLt (fun _ ↦ rfl)
  exact congrFun (bitsVal_injective (hu.trans hg.symm)) idx
noncomputable def dummyCfgS3 : SpecsAux.SpecMirror.Configuration where
  nuclei := fun _ _ ↦ 0
  projectileMomentum := fun _ ↦ 0
  momentum_le := by
    have h0 : SpecsAux.SpecMirror.waveNumberSq (fun _ ↦ 0) = 0 := by
      unfold SpecsAux.SpecMirror.waveNumberSq SpecsAux.SpecMirror.waveVector dotProduct
      simp
    rw [h0]
    positivity
theorem basisBits_symm {n : ℕ} (δ : BitAssignment n) : basisBits n ((basisBitsEquiv n).symm δ)
    = δ := (basisBitsEquiv n).apply_symm_apply δ
theorem symm_basisBits {n : ℕ} (z : Fin (2 ^ n)) : (basisBitsEquiv n).symm (basisBits n z) = z
    := (basisBitsEquiv n).symm_apply_apply z
open scoped Classical in
theorem sel149_wire_lt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (k : Fin 149) : (if k.val < 24
    then 3924 + k.val else if k.val < 27 then 3948 + (k.val - 24) else if k.val < 107 then
    3954 + (k.val - 27) else momCoreWires mPayload + 6 + (k.val - 107)) < momCoreWires
    mPayload + 48 := by
  have hge := s3MomCore_ge_4034 hmPay
  have hk := k.isLt
  split_ifs <;> omega
def sel149 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    QRegister 149 (momCoreWires mPayload + 48) where
  wires :=
    ⟨fun k ↦ ⟨if k.val < 24 then 3924 + k.val
              else if k.val < 27 then 3948 + (k.val - 24)
              else if k.val < 107 then 3954 + (k.val - 27)
              else momCoreWires mPayload + 6 + (k.val - 107),
              sel149_wire_lt hmPay k⟩,
     by
       intro i j hij
       have hv := congrArg Fin.val hij
       dsimp only at hv
       have hge := s3MomCore_ge_4034 hmPay
       have hi := i.isLt
       have hj := j.isLt
       split_ifs at hv <;> exact Fin.ext (by omega)⟩
open scoped Classical in
theorem hmPay80 : 80 ≤ 80 := le_rfl
def embedAlphaCore80 (α : BitAssignment 149) : BitAssignment (momCoreWires 80) :=
  fun q ↦
    if h1 : 3924 ≤ q.val ∧ q.val < 3948 then α ⟨q.val - 3924, by omega⟩
    else if h2 : 3948 ≤ q.val ∧ q.val < 3951 then α ⟨24 + (q.val - 3948), by omega⟩
    else if h3 : 3954 ≤ q.val ∧ q.val < 4034 then α ⟨27 + (q.val - 3954), by omega⟩
    else 0
def sel107_80 : QRegister 107 (momCoreWires 80) where
  wires :=
    ⟨fun k ↦
      let v := (sel149 hmPay80 ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩).val
      ⟨v, by
        have hk := k.isLt
        dsimp [sel149, v]
        split_ifs <;> (rw [s3MomCoreWires_eq]; omega)⟩,
     by
       intro i j hij
       have hv := congrArg Fin.val hij
       dsimp [sel149] at hv
       have hi := i.isLt; have hj := j.isLt
       split_ifs at hv <;>
         exact Fin.ext (by { dsimp -failIfUnchanged only [Fin.val_mk] at *; all_goals omega })⟩
theorem sel107_80_val (k : Fin 107) : (sel107_80 k).val = if k.val < 24 then 3924 + k.val else
    if k.val < 27 then 3948 + (k.val - 24) else 3954 + (k.val - 27) := by
  have hk := k.isLt
  dsimp [sel107_80, sel149]
  split_ifs <;> omega
def sel107 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : QRegister 107 (momCoreWires mPayload + 48)
    := (sel149 hmPay).slice 0 107 (by decide)
def embedAlpha107 (α : BitAssignment 107) : BitAssignment (momCoreWires 80) :=
  embedAlphaCore80 fun k ↦ if hk : k.val < 107 then α ⟨k.val, hk⟩ else 0
open scoped Classical in
theorem embedAlpha107_sel107_80 (α : BitAssignment 107) (k : Fin 107) :
    embedAlpha107 α (sel107_80 k) = α k := by
  have hk := k.isLt
  have hv := sel107_80_val k
  unfold embedAlpha107 embedAlphaCore80
  split_ifs at hv ⊢ <;> try omega
  all_goals
    dsimp only
    rw [s3DitePos (by omega)]
    exact congrArg α (Fin.ext (by dsimp; omega))
open scoped Classical in
theorem cnotVec_cliffDisjoint {M : ℕ} {mutW : Wire M → Prop} :
    ∀ (W : ℕ) (src dst : Fin W → Wire M) (hne : ∀ j, src j ≠ dst j),
      (∀ j, ¬ mutW (src j)) → (∀ j, ¬ mutW (dst j)) →
      CliffDisjoint mutW (cnotVec W src dst hne)
  | 0, _, _, _, _, _ => trivial
  | W + 1, src, dst, hne, hs, hd =>
      ⟨⟨hs 0, hd 0⟩, cnotVec_cliffDisjoint W (fun j ↦ src j.succ) (fun j ↦ dst j.succ)
        (fun j ↦ hne j.succ) (fun j ↦ hs j.succ) (fun j ↦ hd j.succ)⟩
theorem bitsVal_extract_of_agree {N W : ℕ} (r : QRegister W N) (z : Fin (2 ^ N))
    (f : Fin W → ZMod 2) (hf : ∀ i : Fin W, basisBits N z (r i) = f i) :
    bitsVal f = (r.extractIndex z).val := by
  refine bitsVal_eq_of_testBit f (r.extractIndex z).val (r.extractIndex z).isLt fun i ↦ ?_
  have hb := QRegister.basisBits_extractIndex r z i
  rw [hf i] at hb
  rw [← hb]
  exact basisBits_eq_testBit W (r.extractIndex z) i
open scoped Classical in
theorem embedAlpha107_fields (α107 : BitAssignment 107) :
    let z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
    (∀ w : Fin 3, (projAxisField ((momSysReg 80).extractIndex z80) w).val =
      bitsVal (fun b : Fin 8 ↦ α107 ⟨8 * w.val + b.val, by omega⟩)) ∧
    ((momCoinReg 80).extractIndex z80).val =
      bitsVal (fun b : Fin 3 ↦ α107 ⟨24 + b.val, by omega⟩) ∧
    ((s3U22Core hmPay80).extractIndex z80).val =
      bitsVal (fun b : Fin 22 ↦ α107 ⟨27 + b.val, by omega⟩) ∧
    (∀ w : Fin 3, signBit3 ((s3S3Core hmPay80).extractIndex z80) w =
      (α107 ⟨49 + w.val, by omega⟩).val) ∧
    ((s3C8Core hmPay80).extractIndex z80).val =
      bitsVal (fun b : Fin 8 ↦ α107 ⟨52 + b.val, by omega⟩) ∧
    ((s3Fine30Core hmPay80).extractIndex z80).val =
      bitsVal (fun b : Fin 30 ↦ α107 ⟨60 + b.val, by omega⟩) ∧
    basisBits (momCoreWires 80) z80 (s3BParCore hmPay80) = α107 ⟨90, by decide⟩ ∧
    ((s3U16Core hmPay80).extractIndex z80).val =
      bitsVal (fun b : Fin 16 ↦ α107 ⟨91 + b.val, by omega⟩) := by
  intro z80
  have hbb (k : Fin 107) : basisBits (momCoreWires 80) z80 (sel107_80 k) = α107 k := by
    rw [basisBits_symm, embedAlpha107_sel107_80]
  have hAt (k : Fin 107) {u : Wire (momCoreWires 80)} (hu : u.val = (sel107_80 k).val) :
      basisBits (momCoreWires 80) z80 u = α107 k :=
    (congrArg (basisBits (momCoreWires 80) z80) (Fin.ext hu)).trans (hbb k)
  have hPay {q off : ℕ} (hoff : off + q ≤ 80) (hB80 : (3954 + off) + q ≤ momCoreWires 80) :
      ((QRegister.block (3954 + off) q hB80).extractIndex z80).val =
        bitsVal (fun b : Fin q ↦ α107 ⟨27 + (off + b.val), by omega⟩) :=
    (bitsVal_extract_of_agree _ z80 _ fun b ↦ hAt _ (by
      have hv := sel107_80_val ⟨27 + (off + b.val), by omega⟩
      dsimp [StepBBlock0Alt.qreg_block_apply] at hv ⊢; split_ifs at hv <;> omega)).symm
  refine ⟨fun w ↦ ?_, ?_, ?_, fun w ↦ ?_, ?_, ?_, ?_, ?_⟩
  · refine (bitsVal_extract_of_agree (proj3Axes w) ((momSysReg 80).extractIndex z80) _
      fun b ↦ ?_).symm
    rw [QRegister.basisBits_extractIndex]
    exact hAt ⟨8 * w.val + b.val, by omega⟩ (by
      have hv := sel107_80_val ⟨8 * w.val + b.val, by omega⟩
      dsimp [momSysReg, proj3Axes, StepBBlock0Alt.qreg_block_apply,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits] at hv ⊢
      split_ifs at hv <;> omega)
  · exact (bitsVal_extract_of_agree (momCoinReg 80) z80 _ fun b ↦ hAt _ (by
      have hv := sel107_80_val ⟨24 + b.val, by omega⟩
      dsimp [momCoinReg, StepBBlock0Alt.qreg_block_apply, SpecsAux.SpecMirror.systemQubits,
        SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
          SpecsAux.SpecMirror.projectileBits]
        at hv ⊢
      split_ifs at hv <;> omega)).symm
  · simpa only [Nat.zero_add] using hPay (off := 0) (by decide) _
  · have hb := QRegister.basisBits_extractIndex (s3S3Core hmPay80) z80 w
    rw [hAt ⟨49 + w.val, by omega⟩ (by
      have hv := sel107_80_val ⟨49 + w.val, by omega⟩
      dsimp [s3S3Core, StepBBlock0Alt.qreg_block_apply] at hv ⊢
      split_ifs at hv <;> omega),
      basisBits_eq_testBit 3 ((s3S3Core hmPay80).extractIndex z80) w] at hb
    rw [← hb]
    rcases (s3S3Core hmPay80).extractIndex z80 with ⟨s3v, hs3lt⟩
    have hs3_8 : s3v < 8 := hs3lt
    fin_cases w <;> interval_cases s3v <;> decide +revert
  · exact (hPay (off := 25) (by decide) _).trans
      (congrArg bitsVal (funext fun b ↦ congrArg α107 (Fin.ext (by dsimp; omega))))
  · exact (hPay (off := 33) (by decide) _).trans
      (congrArg bitsVal (funext fun b ↦ congrArg α107 (Fin.ext (by dsimp; omega))))
  · have h := hbb ⟨90, by decide⟩
    convert h using 2
    exact Fin.ext rfl
  · exact (hPay (off := 64) (by decide) _).trans
      (congrArg bitsVal (funext fun b ↦ congrArg α107 (Fin.ext (by dsimp; omega))))
section BlockB_Ctx
theorem cnotVec_eval_eq {M n : ℕ} (src dst : Fin n → Wire M) (hne : ∀ j, src j ≠ dst j)
    (hdst_inj : Function.Injective dst) (hdisj : ∀ i j, src i ≠ dst j) (β : BitAssignment M) :
    (∀ q, (∀ j, q ≠ dst j) → (cnotVec n src dst hne).eval β q = β q) ∧ (∀ j, (cnotVec n src
    dst hne).eval β (dst j) = β (dst j) + β (src j)) := by
  classical
  refine ⟨fun q hq ↦ ?_, fun j ↦ ?_⟩
  · rw [cnotVec_eval n src dst hne hdst_inj hdisj β q, s3DiteNeg (fun ⟨j, hj⟩ ↦ hq j hj)]
  · have hex : ∃ i, dst j = dst i := ⟨j, rfl⟩
    have hch : hex.choose = j := hdst_inj hex.choose_spec.symm
    rw [cnotVec_eval n src dst hne hdst_inj hdisj β (dst j), s3DitePos hex, hch]
theorem xVec_eval_eq {M n : ℕ} (dst : Fin n → Wire M) (hdst_inj : Function.Injective dst)
    (β : BitAssignment M) : (∀ q, (∀ j, q ≠ dst j) → (xVec n dst).eval β q = β q) ∧
    (∀ j, (xVec n dst).eval β (dst j) = β (dst j) + 1) := by
  induction n generalizing β with
  | zero => exact ⟨fun _ _ ↦ rfl, fun j ↦ Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨hnon, hdst⟩ := ih (fun j ↦ dst j.succ)
        (fun i j h ↦ Fin.succ_injective _ (hdst_inj h)) ((CliffProg.x (dst 0)).eval β)
    refine ⟨fun q hq ↦ ?_, fun j ↦ ?_⟩
    · dsimp [xVec, CliffProg.eval] at *
      rw [hnon q (fun j ↦ hq j.succ), Function.update_of_ne (hq 0)]
    · cases j using Fin.cases with
      | zero =>
          dsimp [xVec, CliffProg.eval] at *
          rw [hnon (dst 0) (fun j h ↦ Fin.succ_ne_zero j (hdst_inj h.symm)), Function.update_self]
      | succ j' =>
          dsimp [xVec, CliffProg.eval] at *
          rw [hdst j', Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j' (hdst_inj h))]
set_option backward.isDefEq.respectTransparency true
end BlockB_Ctx
def IsMutBlock (M rem : ℕ) (mutW : Wire M → Prop) (p : TempPhaseProg M) : Prop :=
    ValidCleanRem M rem p ∧ (∀ β, cleanRem M rem β → p.evalSign β = 0) ∧
    (∀ β, cleanRem M rem β → cleanRem M rem (p.evalBits β)) ∧
    (∀ β, cleanRem M rem β → ∀ q, ¬ mutW q → p.evalBits β q = β q)
open scoped Classical in
theorem withCliffX_selfInv {M cur : ℕ} [NeZero M] (hcur : cur ≤ M)
    (q : Wire M) (hq : q.val < cur) {p : TempPhaseProg M}
    (hv : ValidCleanRem M (M - cur) p)
    (hs : ∀ β, cleanRem M (M - cur) β → p.evalSign β = 0)
    (hcl : ∀ β, cleanRem M (M - cur) β → cleanRem M (M - cur) (p.evalBits β))
    (hinv : ∀ β, cleanRem M (M - cur) β → p.evalBits (p.evalBits β) = β)
    (hnonQ : ∀ β, cleanRem M (M - cur) β → p.evalBits β q = β q) :
    let w := withCliffAlloc (.x q) p
    ValidCleanRem M (M - cur) w ∧
      (∀ β, cleanRem M (M - cur) β → w.evalSign β = 0) ∧
      (∀ β, cleanRem M (M - cur) β → cleanRem M (M - cur) (w.evalBits β)) ∧
      (∀ β, cleanRem M (M - cur) β → w.evalBits (w.evalBits β) = β) ∧
      (∀ β, cleanRem M (M - cur) β →
        w.evalBits β = Function.update (p.evalBits (Function.update β q (β q + 1))) q
          (p.evalBits (Function.update β q (β q + 1)) q + 1)) := by
  intro w
  obtain ⟨hvw, hevw⟩ := withCliffAlloc_valid_and_eval (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl (.x q) (by dsimp [CliffProg.SupportsBelow]; omega) p hv
  have hclW : ∀ β, cleanRem M (M - cur) β → cleanRem M (M - cur) (w.evalBits β) :=
    fun β hβ u hu ↦ by
      obtain ⟨hc1, _, hb1⟩ := hevw β hβ
      rw [hb1]; dsimp [CliffProg.inv, CliffProg.eval]
      rw [Function.update_of_ne (wire_ne_of_gt (by omega))]
      exact hcl _ hc1 u hu
  refine ⟨hvw,
    fun β hβ ↦ by obtain ⟨hc1, hs1, _⟩ := hevw β hβ; exact hs1.trans (hs _ hc1),
    hclW,
    fun β hβ ↦ ?_,
    fun β hβ ↦ (hevw β hβ).2.2⟩
  obtain ⟨hc1, _, hb1⟩ := hevw β hβ
  obtain ⟨_, _, hb2⟩ := hevw (w.evalBits β) (hclW β hβ)
  rw [hb2, hb1]
  dsimp [CliffProg.inv, CliffProg.eval]
  have cancelX : ∀ δ : BitAssignment M,
      Function.update (Function.update δ q (δ q + 1)) q
        (Function.update δ q (δ q + 1) q + 1) = δ := fun δ ↦ by
    funext u; by_cases hu : u = q
    · subst hu; simp [Function.update_self, add_assoc, CharTwo.add_self_eq_zero]
    · simp [Function.update_of_ne hu]
  dsimp only [CliffProg.eval] at hc1
  rw [cancelX, hinv _ hc1, cancelX]
theorem IsMutBlock.mono {M rem₁ rem₂ : ℕ} {mutW : Wire M → Prop} {p : TempPhaseProg M}
    (hle : rem₁ ≤ rem₂) (hmut : ∀ q : Wire M, mutW q → q.val < M - rem₂)
    (h : IsMutBlock M rem₁ mutW p) : IsMutBlock M rem₂ mutW p := ⟨validCleanRem_mono hle h.1,
    fun β hβ ↦ h.2.1 β (cleanRem_anti hle hβ), fun β hβ q hq ↦ (h.2.2.2 β (cleanRem_anti hle
    hβ) q (fun hm ↦ absurd (lt_of_lt_of_le (hmut q hm) hq) (Nat.lt_irrefl _))).trans (hβ q
    hq), fun β hβ q hq ↦ h.2.2.2 β (cleanRem_anti hle hβ) q hq⟩
open scoped Classical in
theorem IsMutBlock.seq {M rem : ℕ} {mutW : Wire M → Prop} {p₁ p₂ : TempPhaseProg M}
    (hrem : rem ≤ M) (h₁ : IsMutBlock M rem mutW p₁) (h₂ : IsMutBlock M rem mutW p₂) :
    IsMutBlock M rem mutW (.seq p₁ p₂) := by
  obtain ⟨hv₁, hs₁, hcl₁, hnon₁⟩ := h₁
  obtain ⟨hv₂, hs₂, hcl₂, hnon₂⟩ := h₂
  refine ⟨⟨rem, hrem, hv₁, hv₂, hcl₁⟩,
    fun β hβ ↦ by dsimp [TempPhaseProg.evalSign]; rw [hs₁ β hβ, hs₂ _ (hcl₁ β hβ), add_zero],
    fun β hβ ↦ hcl₂ _ (hcl₁ β hβ),
    fun β hβ q hq ↦ (hnon₂ _ (hcl₁ β hβ) q hq).trans (hnon₁ β hβ q hq)⟩
open scoped Classical in
theorem padZeroBits149_clean (α : BitAssignment 149) :
    cleanRem 437 288
      (MomSlot0CircuitHalf.padZeroBits (mClean := 288) α) := by
  intro q hq
  let j : Fin 288 := ⟨q.val - 149, by omega⟩
  have hqEq : q = Fin.natAdd 149 j := Fin.ext (by dsimp [j, Fin.natAdd]; omega)
  rw [hqEq]
  unfold MomSlot0CircuitHalf.padZeroBits
  exact Fin.addCases_right j
open scoped Classical in
theorem padZeroBits149_lt (α : BitAssignment 149) (k : Fin 149) :
    MomSlot0CircuitHalf.padZeroBits (mClean := 288) α
      ⟨k.val, by omega⟩ = α k := by
  have hkEq : (⟨k.val, by omega⟩ : Wire 437) = Fin.castAdd 288 k := Fin.ext rfl
  rw [hkEq]
  unfold MomSlot0CircuitHalf.padZeroBits
  exact Fin.addCases_left k
set_option backward.isDefEq.respectTransparency true
end ConfigStepBBlock0
end StepBBlock0
end
end ModStepBBlock0

section ModStepBOuter
@[expose] public section
namespace StepBOuter
section ConfigStepBOuter
local instance (priority := 10) instNeZeroTwoPowK23 (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real SpecsAux
open HermitianMat
open _root_.QuantumComputation.Specs.StoppingPowerSolution (cleanRem ValidCleanRem)
open MomSlots35Slot3ProjNuclear
  (shellMu3 shellMu3_lt_seven shellMagCoord3 s3ProjStepHw)
open StepBBlock0
  (s3ItePos s3IteNeg s3DitePos s3DiteNeg zmod2_eq_zero_or_one zmod2_add_self_cancel xVec
   xVec_supportsBelow xVec_disjoint xVec_eval_eq cnotVec cnotVec_eval_eq cnotVec_cliffDisjoint
   xorBlock_of_ctx TempCtxLiftEx shellTop7Mu u22_testBit_eq_wire IsMutBlock withCliffX_selfInv)
open Prod57BoothHoist
  (p57ProjW p57S3W p57MW p57PBufW sTrueRawValPBuf sTrueRawValPBuf_eq_sTrueRawVal
   p57ProjW_injective sTrueRawVal bitsVal_invLow7 bitsVal_xorSnoc7
   sTrue18FwdPBuf275 sTrue18RevPBuf275)
open scoped Matrix BigOperators
def coinW (b : Fin 3) : Wire 437 := ⟨24 + b.val, by omega⟩
def u22WAux (i : Fin 22) : Wire 437 := ⟨27 + i.val, by omega⟩
def top7W (i : Fin 7) : Wire 437 := ⟨42 + i.val, by omega⟩
def bParWAux : Wire 437 := ⟨90, by decide⟩
def u16WAux (b : Fin 16) : Wire 437 := ⟨91 + b.val, by omega⟩
def cat42W (j : Fin 42) : Wire 437 := ⟨107 + j.val, by omega⟩
def accWAux : Wire 437 := ⟨149, by decide⟩
def pBufW (w : Fin 3) (b : Fin 8) : Wire 437 := ⟨150 + 8 * w.val + b.val, by omega⟩
def muW (j : Fin 3) : Wire 437 := ⟨174 + j.val, by omega⟩
def coinOkW : Wire 437 := ⟨198, by decide⟩
def validStaticW : Wire 437 := ⟨258, by decide⟩
def projFlat24 (k : Fin 24) : Wire 437 := ⟨k.val, by omega⟩
def pBufFlat24 (k : Fin 24) : Wire 437 := ⟨150 + k.val, by omega⟩
section Body
set_option backward.isDefEq.respectTransparency false
theorem cnotVec_supportsBelowAux {M bound : ℕ} :
    ∀ (W : ℕ) (src dst : Fin W → Wire M) (hne : ∀ j, src j ≠ dst j),
      (∀ j, (src j).val < bound) → (∀ j, (dst j).val < bound) →
      (cnotVec W src dst hne).SupportsBelow bound
  | 0, _, _, _, _, _ => trivial
  | W + 1, src, dst, hne, hs, hd =>
      ⟨⟨hs 0, hd 0⟩, cnotVec_supportsBelowAux W (fun j ↦ src j.succ) (fun j ↦ dst j.succ)
        (fun j ↦ hne j.succ) (fun j ↦ hs j.succ) (fun j ↦ hd j.succ)⟩
def and3XorProg {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M) (c₁ c₂ c₃ dst : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) (hc3 : c₃.val < cur)
    (hd : dst.val < cur) : TempPhaseProg M :=
  let anc0 : Wire M := ⟨cur, by omega⟩
  let anc1 : Wire M := ⟨cur + 1, by omega⟩
  withTempBit c₁ c₂ anc0 h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2)
    (andXor anc0 c₃ dst anc1
      (wire_ne_of_gt hc3)
      (wire_ne_of_lt (by dsimp [anc0, anc1]; omega))
      (wire_ne_of_lt (lt_trans hc3 (by dsimp [anc1]; omega)))
      (wire_ne_of_gt (lt_trans hd (by dsimp [anc1]; omega))))
theorem and3XorProg_spec {M : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M)
    (c₁ c₂ c₃ dst : Wire M) (h12 : c₁ ≠ c₂)
    (h1d : c₁ ≠ dst) (h2d : c₂ ≠ dst) (h3d : c₃ ≠ dst)
    (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) (hc3 : c₃.val < cur) (hd : dst.val < cur) :
    let p := and3XorProg cur hcur c₁ c₂ c₃ dst h12 hc1 hc2 hc3 hd
    ValidCleanRem M (M - cur) p ∧
      (∀ β, cleanRem M (M - cur) β → p.evalSign β = 0) ∧
      (∀ β, cleanRem M (M - cur) β → cleanRem M (M - cur) (p.evalBits β)) ∧
      (∀ β, cleanRem M (M - cur) β → p.evalBits (p.evalBits β) = β) ∧
      (∀ β, cleanRem M (M - cur) β →
        p.evalBits β = Function.update β dst (β dst + β c₁ * β c₂ * β c₃)) := by
  intro p
  let anc0 : Wire M := ⟨cur, by omega⟩
  let anc1 : Wire M := ⟨cur + 1, by omega⟩
  obtain ⟨hvIn, hevIn⟩ := andXor_valid_and_eval (M := M) (rem := M - (cur + 1))
    anc0 c₃ dst anc1
    (wire_ne_of_gt hc3) (wire_ne_of_gt hd) h3d
    (by dsimp [anc0, anc1]; omega) (by dsimp [anc1]; omega) (by dsimp [anc1]; omega)
    (by dsimp [anc1]; omega)
  have hclSetup : ∀ β : BitAssignment M, cleanRem M (M - cur) β →
      cleanRem M (M - (cur + 1)) (Function.update β anc0 (β anc0 + β c₁ * β c₂)) := by
    intro β hβ w hw
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [anc0]; omega))]
    exact hβ w (by omega)
  have hvAll : ValidCleanRem M (M - cur) p :=
    ⟨by dsimp [anc0]; omega, hvIn, fun β₁ hβ₁ ↦ by
      rw [hevIn β₁ hβ₁]
      exact ⟨Function.update_of_ne h1d _ _, Function.update_of_ne h2d _ _,
        Function.update_of_ne (wire_ne_of_gt hd) _ _⟩⟩
  have hevAll : ∀ β, cleanRem M (M - cur) β →
      p.evalBits β = Function.update β dst (β dst + β c₁ * β c₂ * β c₃) := fun β hβ ↦ by
    have ha0 : β anc0 = 0 := hβ anc0 (by dsimp [anc0]; omega)
    let γ := Function.update β anc0 (β anc0 + β c₁ * β c₂)
    have hγ : γ = Function.update β anc0 (β c₁ * β c₂) := by dsimp only [γ]; rw [ha0, zero_add]
    dsimp only [p, and3XorProg, withTempBit, TempPhaseProg.evalBits]
    change Function.update ((andXor anc0 c₃ dst anc1 _ _ _ _).evalBits γ) anc0 _ = _
    rw [hevIn γ (hclSetup β hβ)]
    have hc1a : c₁ ≠ anc0 := wire_ne_of_lt hc1
    have hc2a : c₂ ≠ anc0 := wire_ne_of_lt hc2
    have hc3a : c₃ ≠ anc0 := wire_ne_of_lt hc3
    have hda : dst ≠ anc0 := wire_ne_of_lt hd
    have hpost_c1 : Function.update γ dst (γ dst + γ anc0 * γ c₃) c₁ = β c₁ := by
      rw [Function.update_of_ne h1d, hγ, Function.update_of_ne hc1a]
    have hpost_c2 : Function.update γ dst (γ dst + γ anc0 * γ c₃) c₂ = β c₂ := by
      rw [Function.update_of_ne h2d, hγ, Function.update_of_ne hc2a]
    have hpost_a0 : Function.update γ dst (γ dst + γ anc0 * γ c₃) anc0 = β c₁ * β c₂ := by
      rw [Function.update_of_ne hda.symm, hγ, Function.update_self]
    rw [hpost_c1, hpost_c2, hpost_a0, CharTwo.add_self_eq_zero]
    funext w
    by_cases hwa : w = anc0
    · subst hwa
      rw [Function.update_self, Function.update_of_ne hda.symm, ha0]
    · rw [Function.update_of_ne hwa]
      by_cases hwd : w = dst
      · subst hwd
        rw [Function.update_self, Function.update_self, hγ, Function.update_of_ne hda,
          Function.update_self, Function.update_of_ne hc3a, mul_assoc]
      · simp [Function.update_of_ne hwd, hγ, Function.update_of_ne hwa]
  have hclAll : ∀ β, cleanRem M (M - cur) β → cleanRem M (M - cur) (p.evalBits β) :=
    fun β hβ w hw ↦ by
      rw [hevAll β hβ, Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le hd (by omega)))]
      exact hβ w hw
  refine ⟨hvAll, fun β _ ↦ by
      dsimp [p, and3XorProg, withTempBit, andXor, TempPhaseProg.cnot, TempPhaseProg.evalSign],
    hclAll, fun β hβ ↦ ?_, hevAll⟩
  rw [hevAll (p.evalBits β) (hclAll β hβ), hevAll β hβ]
  funext w
  by_cases hwd : w = dst
  · subst hwd
    simp only [Function.update_self, Function.update_of_ne h1d, Function.update_of_ne h2d,
      Function.update_of_ne h3d]
    exact zmod2_add_self_cancel _ _
  · simp [Function.update_of_ne hwd]
def coinOkXor275 : TempPhaseProg 437 := withCliffAlloc (.x (coinW 0)) (and3XorProg 275
    (by decide) (coinW 0) (coinW 1) (coinW 2) coinOkW (by decide) (by decide)
    (by decide) (by decide) (by decide))
theorem coinOkXor275_spec : IsMutBlock 437 (437 - 275) (fun q ↦ q = coinOkW) coinOkXor275
    ∧ (∀ β, cleanRem 437 (437 - 275) β → coinOkXor275.evalBits β coinOkW = β coinOkW +
    if bitsVal (fun b ↦ β (coinW b)) = 6 then 1 else 0) := by
  obtain ⟨hvA, hsA, hclA, hinvA, hevA⟩ := and3XorProg_spec 275 (by decide) (coinW 0)
      (coinW 1) (coinW 2) coinOkW (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hvW, hsW, hclW, _, hevW⟩ := withCliffX_selfInv (M := 437) (cur := 275) (by decide)
    (coinW 0) (by decide) hvA hsA hclA hinvA
    (fun β hβ ↦ by rw [hevA β hβ, Function.update_of_ne (by decide)])
  have hclX (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β) :
      cleanRem 437 (437 - 275) (Function.update β (coinW 0) (β (coinW 0) + 1)) :=
    fun u hu ↦ by
      rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [coinW]; omega))]; exact hβ u hu
  refine ⟨⟨hvW, hsW, hclW, fun β hβ q hq ↦ ?_⟩, fun β hβ ↦ ?_⟩
  · change (withCliffAlloc (.x (coinW 0)) _).evalBits β q = β q
    rw [hevW β hβ, hevA _ (hclX β hβ)]
    by_cases hq0 : q = coinW 0
    · subst hq0; simp [Function.update_self, Function.update_of_ne hq, add_assoc,
        CharTwo.add_self_eq_zero]
    · simp [Function.update_of_ne hq0, Function.update_of_ne hq]
  · change (withCliffAlloc (.x (coinW 0)) _).evalBits β coinOkW = _
    rw [hevW β hβ, hevA _ (hclX β hβ), Function.update_of_ne (by decide), Function.update_self]
    simp only [Function.update_self, Function.update_of_ne (by decide : coinOkW ≠ coinW 0),
      Function.update_of_ne (by decide : coinW 1 ≠ coinW 0),
      Function.update_of_ne (by decide : coinW 2 ≠ coinW 0)]
    congr 1
    rw [show bitsVal (fun b ↦ β (coinW b)) =
        (β (coinW 0)).val + 2 * (β (coinW 1)).val + 4 * (β (coinW 2)).val by
      simp [bitsVal, Fin.sum_univ_three]; ring]
    rcases zmod2_eq_zero_or_one (β (coinW 0)) with h0 | h0 <;>
      rcases zmod2_eq_zero_or_one (β (coinW 1)) with h1 | h1 <;>
      rcases zmod2_eq_zero_or_one (β (coinW 2)) with h2 | h2 <;>
      (rw [h0, h1, h2]; decide)
def xorBlockProg (W : ℕ) (out src : Fin W → Wire 437) (hout_lt : ∀ j, (out j).val < 275)
    (hsrc_ge : ∀ j, 275 ≤ (src j).val) (K : TempCtx 437) : TempPhaseProg 437 := K.plug (.cliff
    (Slot3MicroEngineAux.cnotVec W src out (fun j ↦ wire_ne_of_gt (lt_of_lt_of_le (hout_lt j)
    (hsrc_ge j)))))
theorem xorBlock275_spec {W curEnd : ℕ} (hEnd : curEnd ≤ 437) (hStart : 275 ≤ curEnd)
    (out src : Fin W → Wire 437)
    (hout_lt : ∀ j, (out j).val < 275) (hout_inj : Function.Injective out)
    (hsrc_ge : ∀ j, 275 ≤ (src j).val)
    (K : TempCtx 437)
    (hDisj : K.DisjointFrom (fun w ↦ ∃ j, w = out j))
    (hSupp : K.SupportsBelowCtx curEnd)
    (hLift : Slot3MicroEngineAux.TempCtxLiftEx 275 curEnd K) :
    let p := xorBlockProg W out src hout_lt hsrc_ge K
    IsMutBlock 437 (437 - 275) (fun q ↦ ∃ j, q = out j) p ∧
      p.countTempAnd = K.countTempAnd ∧
      (∀ β, cleanRem 437 (437 - 275) β → ∀ j : Fin W,
        p.evalBits β (out j) = β (out j) + K.fwdBits β (src j)) := by
  classical
  obtain ⟨hVal, hCnt, hSgn, hBits⟩ :=
    Slot3MicroEngineAux.xorBlock_of_ctx (M := 437) (curStart := 275) (curEnd := curEnd) (W := W)
      hEnd hStart out hout_lt hout_inj src hsrc_ge K hDisj hSupp K.fwdBits
      (Slot3MicroEngineAux.TempCtxLiftEx.probe hLift)
  dsimp only
  have hNon : ∀ β, cleanRem 437 (437 - 275) β → ∀ q : Wire 437,
      ¬(∃ j, q = out j) → (xorBlockProg W out src hout_lt hsrc_ge K).evalBits β q = β q :=
    fun β hβ q hq ↦ by
      dsimp only [xorBlockProg]
      rw [hBits β hβ q, s3DiteNeg hq]
  have hCl : ∀ β, cleanRem 437 (437 - 275) β →
      cleanRem 437 (437 - 275) ((xorBlockProg W out src hout_lt hsrc_ge K).evalBits β) :=
    fun β hβ u hu ↦ by
      rw [hNon β hβ u (fun ⟨j, hj⟩ ↦ by subst hj; have := hout_lt j; omega)]
      exact hβ u hu
  refine ⟨⟨hVal, hSgn, hCl, hNon⟩, hCnt, fun β hβ j ↦ ?_⟩
  have hex : ∃ i, out j = out i := ⟨j, rfl⟩
  have hch : hex.choose = j := hout_inj hex.choose_spec.symm
  dsimp only [xorBlockProg]
  rw [hBits β hβ (out j), s3DitePos hex, hch]
def xorBlock1Prog (out0 src0 : Wire 437) (hout0 : out0.val < 275) (hsrc0 : 275 ≤ src0.val)
    (K : TempCtx 437) : TempPhaseProg 437 := xorBlockProg 1 (fun _ ↦ out0) (fun _ ↦ src0)
    (fun _ ↦ hout0) (fun _ ↦ hsrc0) K
theorem xorBlock1_275_spec {curEnd : ℕ} (hEnd : curEnd ≤ 437) (hStart : 275 ≤ curEnd)
    (out0 src0 : Wire 437) (hout0 : out0.val < 275) (hsrc0 : 275 ≤ src0.val)
    (K : TempCtx 437)
    (hDisj : K.DisjointFrom (fun w ↦ ∃ _ : Fin 1, w = out0))
    (hSupp : K.SupportsBelowCtx curEnd)
    (hLift : Slot3MicroEngineAux.TempCtxLiftEx 275 curEnd K) :
    let p := xorBlock1Prog out0 src0 hout0 hsrc0 K
    IsMutBlock 437 (437 - 275) (fun q ↦ q = out0) p ∧
      p.countTempAnd = K.countTempAnd ∧
      (∀ β, cleanRem 437 (437 - 275) β →
        p.evalBits β out0 = β out0 + K.fwdBits β src0) := by
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock275_spec hEnd hStart (fun _ : Fin 1 ↦ out0)
      (fun _ : Fin 1 ↦ src0) (fun _ ↦ hout0) (fun i j _ ↦ Subsingleton.elim i j)
      (fun _ ↦ hsrc0) K hDisj hSupp hLift
  exact ⟨⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q (fun ⟨_, h⟩ ↦ hq h)⟩,
    hCnt, fun β hβ ↦ hEv β hβ 0⟩
theorem top7W_inj : Function.Injective top7W := fun i j h ↦ by
  have hv := congrArg Fin.val h; dsimp [top7W] at hv; exact Fin.ext (by omega)
theorem muW_inj : Function.Injective muW := fun i j h ↦ by
  have hv := congrArg Fin.val h; dsimp [muW] at hv; exact Fin.ext (by omega)
def muXor275OutW (j : Fin 3) : Wire 437 :=
  ⟨275 + (Slot3MicroEngineAux.getNatAt Slot3MicroEngineAux.top7MuSlots j.val - 7), by
    have hb := Slot3MicroEngineAux.top7MuSlots_bounds j; omega⟩
def muXor275Ctx : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro top7W top7W_inj 275 8 5
    (fun i ↦ by dsimp [top7W]; omega)
    Slot3MicroEngineAux.top7MuOps Slot3MicroEngineAux.top7Mu_meta3 (by decide)
def muXor275 : TempPhaseProg 437 :=
  xorBlockProg 3 muW muXor275OutW
    (fun j ↦ by dsimp [muW]; omega)
    (fun j ↦ by dsimp [muXor275OutW]; omega)
    muXor275Ctx
theorem muXor275_spec_full : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ j, q = muW j) muXor275
    ∧ muXor275.countTempAnd = 5 ∧ (∀ β, cleanRem 437 (437 - 275) β → ∀ j : Fin 3,
    muXor275.evalBits β (muW j) = β (muW j) + if (shellTop7Mu ⟨bitsVal (fun i ↦ β
    (top7W i)), bitsVal_lt_two_pow _⟩).testBit j.val then 1 else 0) := by
  obtain ⟨hCntM, hPropsM, hLiftM, hEvalM⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped top7W top7W_inj 275 8 5
      (fun i ↦ by dsimp [top7W]; omega)
      Slot3MicroEngineAux.top7MuOps Slot3MicroEngineAux.top7Mu_meta3 (by decide)
  obtain ⟨hDisj, hSupp⟩ := hPropsM (mutW := fun q ↦ ∃ j, q = muW j)
    (fun i ⟨j, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [top7W, muW] at hv; omega)
    (fun w hw ⟨j, h⟩ ↦ by subst h; dsimp [muW] at hw; omega)
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock275_spec (curEnd := 283) (by decide) (by decide)
    muW muXor275OutW (fun j ↦ by dsimp [muW]; omega) muW_inj
    (fun j ↦ by dsimp [muXor275OutW]; omega) muXor275Ctx hDisj hSupp hLiftM
  refine ⟨hB, hCnt.trans hCntM, fun β hβ j ↦ ?_⟩
  dsimp only [muXor275]
  rw [hEv β hβ j]
  obtain ⟨_, _, hsOut⟩ := hEvalM β hβ
  have hb := Slot3MicroEngineAux.top7MuSlots_bounds j
  have hout := hsOut (Slot3MicroEngineAux.getNatAt Slot3MicroEngineAux.top7MuSlots j.val) hb.1 hb.2
  have hm_lt : bitsVal (fun i ↦ β (top7W i)) < 128 := bitsVal_lt_two_pow _
  have hchk := (Slot3MicroEngineAux.allBelow_iff 128 Slot3MicroEngineAux.top7MuCheck).mp
    Slot3MicroEngineAux.top7Mu_eval_ok _ hm_lt
  dsimp only [Slot3MicroEngineAux.top7MuCheck] at hchk
  simp only [Bool.and_eq_true] at hchk
  have hj_eq := (Slot3MicroEngineAux.allBelow_iff 3 _).mp hchk.2 j.val j.isLt
  simp only [beq_iff_eq] at hj_eq
  dsimp only [muXor275Ctx, muXor275OutW]
  rw [hout, hj_eq]
  rfl
theorem muXor275_spec : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ j, q = muW j) muXor275 ∧ (∀
    β, cleanRem 437 (437 - 275) β → ∀ j : Fin 3, muXor275.evalBits β (muW j) = β (muW
    j) + if (shellTop7Mu ⟨bitsVal (fun i ↦ β (top7W i)), bitsVal_lt_two_pow _⟩).testBit
    j.val then 1 else 0) := ⟨muXor275_spec_full.1, muXor275_spec_full.2.2⟩
def coinMuXor275 : TempPhaseProg 437 := .seq coinOkXor275 muXor275
theorem coinMuXor275_spec : IsMutBlock 437 (437 - 275)
    (fun q ↦ q = coinOkW ∨ ∃ j, q = muW j) coinMuXor275 ∧ (∀ β, cleanRem 437 (437 -
    275) β → coinMuXor275.evalBits β coinOkW = β coinOkW + (if bitsVal (fun b ↦ β
    (coinW b)) = 6 then 1 else 0) ∧ ∀ j : Fin 3, coinMuXor275.evalBits β (muW j) = β
    (muW j) + if (shellTop7Mu ⟨bitsVal (fun i ↦ β (top7W i)), bitsVal_lt_two_pow
    _⟩).testBit j.val then 1 else 0) := by
  obtain ⟨hB1, hE1⟩ := coinOkXor275_spec
  obtain ⟨hB2, hE2⟩ := muXor275_spec
  have hB1' :
      IsMutBlock 437 (437 - 275) (fun q ↦ q = coinOkW ∨ ∃ j, q = muW j) coinOkXor275 :=
    ⟨hB1.1, hB1.2.1, hB1.2.2.1, fun β hβ q hq ↦ hB1.2.2.2 β hβ q (fun h ↦ hq (Or.inl h))⟩
  have hB2' : IsMutBlock 437 (437 - 275) (fun q ↦ q = coinOkW ∨ ∃ j, q = muW j) muXor275 :=
    ⟨hB2.1, hB2.2.1, hB2.2.2.1, fun β hβ q hq ↦ hB2.2.2.2 β hβ q (fun h ↦ hq (Or.inr h))⟩
  refine ⟨StepBBlock0.IsMutBlock.seq (by decide) hB1' hB2', fun β hβ ↦ ?_⟩
  let β₁ := coinOkXor275.evalBits β
  have hcl₁ := hB1.2.2.1 β hβ
  have htop_pres : (fun i ↦ β₁ (top7W i)) = fun i ↦ β (top7W i) :=
    funext fun i ↦ hB1.2.2.2 β hβ (top7W i) (by
      intro h; have hv := congrArg Fin.val h; dsimp [top7W, coinOkW] at hv; omega)
  have hmu_pres : ∀ j : Fin 3, β₁ (muW j) = β (muW j) :=
    fun j ↦ hB1.2.2.2 β hβ (muW j) (by
      intro h; have hv := congrArg Fin.val h; dsimp [muW, coinOkW] at hv; omega)
  have hcok_pres : muXor275.evalBits β₁ coinOkW = β₁ coinOkW :=
    hB2.2.2.2 β₁ hcl₁ coinOkW (by
      rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; dsimp [muW, coinOkW] at hv; omega)
  refine ⟨hcok_pres.trans (hE1 β hβ), fun j ↦ ?_⟩
  change muXor275.evalBits β₁ (muW j) = _
  rw [hE2 β₁ hcl₁ j, hmu_pres j, htop_pres]
def magDest21 (idx : Fin 21) : Wire 437 :=
  p57MW ⟨idx.val / 7, by omega⟩ ⟨idx.val % 7, by omega⟩
theorem magDest21_inj : Function.Injective magDest21 := fun i j h ↦ by
  have hv := congrArg Fin.val h; dsimp [magDest21, p57MW] at hv; exact Fin.ext (by omega)
def magSel7W (a : Fin 7) : Wire 437 :=
  ⟨275 + (Slot3MicroEngineAux.getNatAt Slot3MicroEngineAux.mu3Sel7Slots a.val - 3), by
    have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds a; omega⟩
def magGeW (a : Fin 7) : Wire 437 :=
  ⟨275 + (Slot3MicroEngineAux.getNatAt Slot3MicroEngineAux.mu3GeSlots a.val - 3), by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds a; omega⟩
def magDotOff : Fin 8 → ℕ := ![0,7,13,18,22,25,27,28]
theorem magDotOff_step (b : Fin 7) :
    magDotOff b.castSucc + (6 - b.val + 1) = magDotOff b.succ := by
  fin_cases b <;> decide
theorem magDotOff_le (k : Fin 8) : magDotOff k ≤ 28 := by
  fin_cases k <;> decide
theorem magDotOff_castSucc_le (b : Fin 7) : magDotOff b.castSucc ≤ 27 := by
  fin_cases b <;> decide
theorem magDotOff_strictMono {i j : Fin 8} (h : i.val < j.val) :
    magDotOff i < magDotOff j := by
  fin_cases i <;> fin_cases j <;> simp_all [magDotOff]
theorem magBitIdx_lt' (w : Fin 3) (b : ℕ) (hb : b < 7) (k : Fin (6 - b + 1)) :
    w.val * (b + k.val + 1) + b < 22 := by
  have := k.isLt
  fin_cases w <;> (dsimp; omega)
def ctxMagAxisLoop (w : Fin 3) (base : ℕ) (hbase : base + 28 ≤ 437) (h289 : 289 ≤ base) :
    (n : ℕ) → n ≤ 7 → TempCtx 437
  | 0, _ => .hole
  | n + 1, hn =>
      let curN := base + magDotOff ⟨n, by omega⟩
      (ctxMagAxisLoop w base hbase h289 n (by omega)).append
        (Slot3MicroEngineAux.ctxDotProduct (6 - n) curN
          (by
            have hs := magDotOff_step ⟨n, by omega⟩
            have hl := magDotOff_le ⟨n + 1, by omega⟩
            dsimp [Fin.castSucc, Fin.succ] at hs
            dsimp [curN]; omega)
          (fun k ↦ magSel7W ⟨n + k.val, by omega⟩)
          (fun k ↦ u22WAux ⟨w.val * (n + k.val + 1) + n, magBitIdx_lt' w n (by omega) k⟩)
          (fun k ↦ wire_ne_of_gt (by
            have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨n + k.val, by omega⟩
            have hb2 := magBitIdx_lt' w n (by omega) k
            dsimp at hb1; dsimp [magSel7W, u22WAux]; omega))
          (fun k ↦ by
            have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨n + k.val, by omega⟩
            dsimp at hb1; dsimp [magSel7W, curN]; omega)
          (fun k ↦ by
            have hb2 := magBitIdx_lt' w n (by omega) k
            dsimp [u22WAux, curN]; omega))
theorem ctxMagAxisLoop_scoped (w : Fin 3) (base : ℕ) (hbase : base + 28 ≤ 437) (h289 : 289 ≤ base) :
    ∀ (n : ℕ) (hn : n ≤ 7),
      let K := ctxMagAxisLoop w base hbase h289 n hn
      let endN := base + magDotOff ⟨n, by omega⟩
      K.countTempAnd = magDotOff ⟨n, by omega⟩ ∧
        (∀ {mutW : Wire 437 → Prop},
          (∀ a, ¬ mutW (magSel7W a)) → (∀ i, ¬ mutW (u22WAux i)) →
          (∀ q : Wire 437, base ≤ q.val → ¬ mutW q) →
          K.DisjointFrom mutW ∧ K.SupportsBelowCtx endN) ∧
        Slot3MicroEngineAux.TempCtxLiftEx base endN K ∧
        (∀ γ : BitAssignment 437, cleanRem 437 (437 - base) γ →
          cleanRem 437 (437 - endN) (K.fwdBits γ) ∧
          (∀ q : Wire 437, q.val < base → K.fwdBits γ q = γ q) ∧
          (∀ (b : Fin 7), b.val < n →
            K.fwdBits γ ⟨base + magDotOff b.castSucc, by
              have := magDotOff_castSucc_le b; omega⟩ =
              ∑ k : Fin (6 - b.val + 1),
                γ (magSel7W ⟨b.val + k.val, by omega⟩) *
                  γ (u22WAux ⟨w.val * (b.val + k.val + 1) + b.val,
                    magBitIdx_lt' w b.val b.isLt k⟩)))
  | 0, _ => by
      dsimp only [ctxMagAxisLoop]
      have h0 : magDotOff ⟨0, by omega⟩ = 0 := rfl
      refine ⟨rfl, fun _ _ _ ↦ ⟨trivial, trivial⟩, ?_,
        fun γ hγ ↦ ⟨?_, fun _ _ ↦ rfl, fun b hb ↦ absurd hb (Nat.not_lt_zero _)⟩⟩
      · rw [h0, Nat.add_zero]; exact fun h ↦ ⟨_, h⟩
      · rw [h0, Nat.add_zero]; exact hγ
  | n + 1, hn => by
      obtain ⟨hCntP, hPropsP, hLiftP, hEvalP⟩ :=
        ctxMagAxisLoop_scoped w base hbase h289 n (by omega)
      set curN := base + magDotOff ⟨n, by omega⟩
      set endNext := base + magDotOff ⟨n + 1, by omega⟩
      have hstep : curN + (6 - n) + 1 = endNext := by
        have hs := magDotOff_step ⟨n, by omega⟩
        dsimp [Fin.castSucc, Fin.succ] at hs; dsimp [curN, endNext]; omega
      have hEndM : endNext ≤ 437 := by
        have := magDotOff_le ⟨n + 1, by omega⟩; dsimp [endNext]; omega
      let lD : Fin (6 - n + 1) → Wire 437 := fun k ↦ magSel7W ⟨n + k.val, by omega⟩
      let rD : Fin (6 - n + 1) → Wire 437 :=
        fun k ↦ u22WAux ⟨w.val * (n + k.val + 1) + n, magBitIdx_lt' w n (by omega) k⟩
      have hlBase : ∀ k : Fin (6 - n + 1), (lD k).val < base := fun k ↦ by
        have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨n + k.val, by omega⟩
        dsimp at hb1; dsimp [lD, magSel7W]; omega
      have hr275 : ∀ k : Fin (6 - n + 1), (rD k).val < 275 := fun k ↦ by
        have := magBitIdx_lt' w n (by omega) k; dsimp [rD, u22WAux]; omega
      have hneD : ∀ k, lD k ≠ rD k := fun k ↦ wire_ne_of_gt (by
        have := hr275 k; dsimp [lD, magSel7W]; omega)
      have hlD : ∀ k, (lD k).val < curN := fun k ↦
        lt_of_lt_of_le (hlBase k) (by dsimp [curN]; omega)
      have hrD : ∀ k, (rD k).val < curN := fun k ↦
        lt_of_lt_of_le (hr275 k) (by dsimp [curN]; omega)
      have hCntD := Slot3MicroEngineAux.ctxDotProduct_countTempAnd (M := 437) (6 - n) curN
        (by omega) lD rD hneD hlD hrD
      obtain ⟨hLiftD, hSpecD⟩ := Slot3MicroEngineAux.ctxDotProduct_scoped (M := 437) (6 - n) curN
        (by omega) lD rD hneD hlD hrD
      have hLiftD' : Slot3MicroEngineAux.TempCtxLiftEx curN endNext _ :=
        Slot3MicroEngineAux.TempCtxLiftEx.mono hLiftD le_rfl (by omega) hEndM
      dsimp only [ctxMagAxisLoop]
      refine ⟨by
          rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd, hCntP, hCntD]
          dsimp [curN, endNext] at hstep; omega,
        fun hns hnu hnb ↦ ?_,
        Slot3MicroEngineAux.TempCtxLiftEx.append hLiftP hLiftD',
        fun γ hγ ↦ ?_⟩
      · obtain ⟨hdP, hsP⟩ := hPropsP hns hnu hnb
        obtain ⟨hdD, hsD⟩ := Slot3MicroEngineAux.ctxDotProduct_props (6 - n) curN (by omega)
          lD rD hneD hlD hrD (fun k ↦ hns _) (fun k ↦ hnu _)
          (fun q hq ↦ hnb q (by dsimp [curN] at hq; omega))
        exact ⟨TempCtx.disjointFrom_append hdP hdD, TempCtx.supportsBelowCtx_append le_rfl
          (Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono (by omega) hsP)
          (Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono (by omega) hsD)⟩
      · obtain ⟨hcl₁, hpres₁, hout₁⟩ := hEvalP γ hγ
        set γ₁ := (ctxMagAxisLoop w base hbase h289 n (by omega)).fwdBits γ
        obtain ⟨hcl₂, hpres₂, hout₂⟩ := hSpecD γ₁ hcl₁
        rw [Slot3MicroEngineAux.TempCtx.append_fwdBits]
        refine ⟨cleanRem_anti (by omega) hcl₂, fun q hq ↦ ?_, fun b hb ↦ ?_⟩
        · rw [hpres₂ q (by dsimp [curN]; omega), hpres₁ q hq]
        · by_cases hbn : b.val < n
          · have hlt_off : magDotOff b.castSucc < magDotOff ⟨n, by omega⟩ :=
              magDotOff_strictMono (by dsimp; exact hbn)
            rw [hpres₂ _ (by dsimp [curN]; omega)]
            exact hout₁ b hbn
          · have hn7 : n < 7 := by omega
            have hbf : b = ⟨n, hn7⟩ := Fin.ext (by dsimp; omega)
            subst hbf
            have hwire : (⟨base + magDotOff (⟨n, hn7⟩ : Fin 7).castSucc, by
                have := magDotOff_castSucc_le ⟨n, hn7⟩; omega⟩ : Wire 437) =
                ⟨curN, by omega⟩ := Fin.ext rfl
            rw [hwire, hout₂]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            have hs_lt : (magSel7W ⟨n + k.val, by omega⟩).val < base := by
              have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨n + k.val, by omega⟩
              dsimp at hb1; dsimp [magSel7W]; omega
            have hu_lt : (u22WAux ⟨w.val * (n + k.val + 1) + n,
                magBitIdx_lt' w n hn7 k⟩).val < base := by
              have := magBitIdx_lt' w n hn7 k
              dsimp [u22WAux]; omega
            rw [hpres₁ _ hs_lt, hpres₁ _ hu_lt]
def magSrc21 (idx : Fin 21) : Wire 437 :=
  if h0 : idx.val < 7 then ⟨289 + idx.val, by omega⟩
  else if h1 : idx.val < 14 then
    ⟨296 + magDotOff ⟨idx.val - 7, by omega⟩, by
      have := magDotOff_le ⟨idx.val - 7, by omega⟩; omega⟩
  else
    ⟨324 + magDotOff ⟨idx.val - 14, by omega⟩, by
      have := magDotOff_le ⟨idx.val - 14, by omega⟩; omega⟩
def magUnpack275Ctx : TempCtx 437 :=
  let k1 := Slot3MicroEngineAux.ctxMicro muW muW_inj 275 14 6
    (fun i ↦ by dsimp [muW]; omega)
    Slot3MicroEngineAux.mu3OneHot7GeOps Slot3MicroEngineAux.mu3OneHot7Ge_meta3 (by decide)
  let k2 := ctxCliffAlloc (.cnot (u22WAux 0) ⟨289, by decide⟩ (by decide))
  let k3 := Slot3MicroEngineAux.ctxAndPairs 6 290 (by decide)
    (fun i : Fin 6 ↦ magGeW ⟨i.val + 1, by omega⟩)
    (fun i : Fin 6 ↦ u22WAux ⟨i.val + 1, by omega⟩)
    (fun i ↦ wire_ne_of_gt (by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
      dsimp at hb; dsimp [magGeW, u22WAux]; omega))
    (fun i ↦ by
      have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
      dsimp at hb; dsimp [magGeW]; omega)
    (fun i ↦ by dsimp [u22WAux]; omega)
  let k4 := ctxMagAxisLoop 1 296 (by decide) (by decide) 7 le_rfl
  let k5 := ctxMagAxisLoop 2 324 (by decide) (by decide) 7 le_rfl
  k1.append (k2.append (k3.append (k4.append k5)))
def magUnpack275 : TempPhaseProg 437 :=
  xorBlockProg 21 magDest21 magSrc21
    (fun idx ↦ by dsimp [magDest21, p57MW]; omega)
    (fun idx ↦ by
      dsimp only [magSrc21]
      split_ifs <;> (dsimp; omega))
    magUnpack275Ctx
theorem shellMagCoord3_testBit_eq (u22 : Fin 4194304) (w : Fin 3) (b : Fin 7) :
    (shellMagCoord3 u22 w).testBit b.val = (decide (b.val ≤ shellMu3 u22) && u22.val.testBit
    (w.val * (shellMu3 u22 + 1) + b.val)) := by
  unfold shellMagCoord3
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hle : b.val ≤ shellMu3 u22
  · have hlt : b.val < shellMu3 u22 + 1 := by omega
    have hcomm : w.val * (shellMu3 u22 + 1) + b.val = b.val + w.val * (shellMu3 u22 + 1) :=
      Nat.add_comm _ _
    simp [hle, hlt, hcomm]
  · have hge : ¬(b.val < shellMu3 u22 + 1) := by omega
    simp [hle, hge]
theorem magDotSum_eq (u22 : Fin 4194304) (w : Fin 3) (b : Fin 7)
    (selF : Fin 7 → ZMod 2) (u22F : Fin 22 → ZMod 2)
    (hsel : ∀ a : Fin 7, selF a = if shellMu3 u22 = a.val then 1 else 0)
    (hu22 : ∀ i : Fin 22, u22F i = if u22.val.testBit i.val then 1 else 0) :
    (∑ k : Fin (6 - b.val + 1),
      selF ⟨b.val + k.val, by omega⟩ *
        u22F ⟨w.val * (b.val + k.val + 1) + b.val, magBitIdx_lt' w b.val b.isLt k⟩) =
      if (shellMagCoord3 u22 w).testBit b.val then 1 else 0 := by
  rw [shellMagCoord3_testBit_eq]
  have hmu7 : shellMu3 u22 < 7 := shellMu3_lt_seven u22
  by_cases hle : b.val ≤ shellMu3 u22
  · let k₀ : Fin (6 - b.val + 1) := ⟨shellMu3 u22 - b.val, by omega⟩
    rw [Finset.sum_eq_single k₀]
    · have hk0_add : b.val + k₀.val = shellMu3 u22 := by dsimp [k₀]; omega
      rw [hsel, s3ItePos (by dsimp; omega), one_mul, hu22]
      by_cases hb0 : u22.val.testBit (w.val * (shellMu3 u22 + 1) + b.val) = true <;>
        simp [hle, hk0_add, hb0]
    · intro k _ hk_ne
      have hne_val : shellMu3 u22 ≠ b.val + k.val := fun he ↦
        hk_ne (Fin.ext (by dsimp [k₀]; omega))
      rw [hsel, s3IteNeg hne_val, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ k₀) habs
  · simp only [hle, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have hne_val : shellMu3 u22 ≠ b.val + k.val := by omega
    rw [hsel, s3IteNeg hne_val, zero_mul]
set_option maxHeartbeats 400000 in
-- 68-TempAnd 3-axis unpacking spec elaboration requires >200k heartbeats.
theorem magUnpack275_spec_full :
    IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w b, q = p57MW w b) magUnpack275 ∧
      magUnpack275.countTempAnd = 68 ∧
      (∀ β, cleanRem 437 (437 - 275) β →
        let u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
        bitsVal (fun j ↦ β (muW j)) = shellMu3 u22 →
        ∀ (w : Fin 3) (b : Fin 7),
          magUnpack275.evalBits β (p57MW w b) = β (p57MW w b) +
            if (shellMagCoord3 u22 w).testBit b.val then 1 else 0) := by
  let mut21 : Wire 437 → Prop := fun q ↦ ∃ idx, q = magDest21 idx
  have hnot_ge275 : ∀ q : Wire 437,275 ≤ q.val → ¬ mut21 q := by
    rintro q hq ⟨idx, rfl⟩; dsimp [magDest21, p57MW] at hq; omega
  have hnot_u22 : ∀ i : Fin 22, ¬ mut21 (u22WAux i) := by
    rintro i ⟨idx, h⟩
    have hv := congrArg Fin.val h; dsimp [u22WAux, magDest21, p57MW] at hv; omega
  let hin1 : ∀ i, (muW i).val < 275 := fun i ↦ by dsimp [muW]; omega
  obtain ⟨hCnt1, hProps1, hLift1, hEval1⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped muW muW_inj 275 14 6 hin1
      Slot3MicroEngineAux.mu3OneHot7GeOps Slot3MicroEngineAux.mu3OneHot7Ge_meta3 (by decide)
  obtain ⟨hd1, hs1⟩ := hProps1 (mutW := mut21)
    (fun i ⟨idx, h⟩ ↦ by
      have hv := congrArg Fin.val h; dsimp [muW, magDest21, p57MW] at hv; omega)
    hnot_ge275
  let c2 : CliffProg 437 := .cnot (u22WAux 0) ⟨289, by decide⟩ (by decide)
  have hc2_supp : c2.SupportsBelow 290 := ⟨by dsimp [u22WAux]; omega, by dsimp; omega⟩
  have hd2 : (ctxCliffAlloc c2).DisjointFrom mut21 :=
    ctxCliffAlloc_disjoint ⟨hnot_u22 0, hnot_ge275 _ (by dsimp; omega)⟩
  have hs2 : (ctxCliffAlloc c2).SupportsBelowCtx 290 := ctxCliffAlloc_supports hc2_supp
  have hLift2 : Slot3MicroEngineAux.TempCtxLiftEx 289 290 (ctxCliffAlloc c2) :=
    Slot3MicroEngineAux.TempCtxLiftEx.mono
      (Slot3MicroEngineAux.TempCtxLiftEx.cliff 290 (by decide) c2 hc2_supp)
      (by decide) le_rfl (by decide)
  let l3 : Fin 6 → Wire 437 := fun i ↦ magGeW ⟨i.val + 1, by omega⟩
  let r3 : Fin 6 → Wire 437 := fun i ↦ u22WAux ⟨i.val + 1, by omega⟩
  have hne3 : ∀ i, l3 i ≠ r3 i := fun i ↦ wire_ne_of_gt (by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
    dsimp at hb; dsimp [l3, r3, magGeW, u22WAux]; omega)
  have hl3 : ∀ i, (l3 i).val < 290 := fun i ↦ by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
    dsimp at hb; dsimp [l3, magGeW]; omega
  have hr3 : ∀ i, (r3 i).val < 290 := fun i ↦ by dsimp [r3, u22WAux]; omega
  have hCnt3 := Slot3MicroEngineAux.ctxAndPairs_countTempAnd (M := 437) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
  obtain ⟨hd3, hs3⟩ := Slot3MicroEngineAux.ctxAndPairs_props (mutW := mut21) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
    (fun i ↦ hnot_ge275 _ (by dsimp [l3, magGeW]; omega))
    (fun i ↦ hnot_u22 _)
    (fun q hq ↦ hnot_ge275 q (by omega))
  obtain ⟨hLift3, hEval3⟩ := Slot3MicroEngineAux.ctxAndPairs_scoped (M := 437) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
  obtain ⟨hCnt4, hProps4, hLift4, hEval4⟩ :=
    ctxMagAxisLoop_scoped 1 296 (by decide) (by decide) 7 le_rfl
  obtain ⟨hCnt5, hProps5, hLift5, hEval5⟩ :=
    ctxMagAxisLoop_scoped 2 324 (by decide) (by decide) 7 le_rfl
  obtain ⟨hd4, hs4⟩ := hProps4 (mutW := mut21)
    (fun a ↦ hnot_ge275 _ (by dsimp [magSel7W]; omega)) hnot_u22
    (fun q hq ↦ hnot_ge275 q (by omega))
  obtain ⟨hd5, hs5⟩ := hProps5 (mutW := mut21)
    (fun a ↦ hnot_ge275 _ (by dsimp [magSel7W]; omega)) hnot_u22
    (fun q hq ↦ hnot_ge275 q (by omega))
  have hDisjAll : magUnpack275Ctx.DisjointFrom mut21 := TempCtx.disjointFrom_append hd1
      (TempCtx.disjointFrom_append hd2 (TempCtx.disjointFrom_append hd3
      (TempCtx.disjointFrom_append hd4 hd5)))
  have hSuppAll : magUnpack275Ctx.SupportsBelowCtx 352 := TempCtx.supportsBelowCtx_append
      (by decide) hs1 (TempCtx.supportsBelowCtx_append (by decide) hs2
      (TempCtx.supportsBelowCtx_append (by decide) hs3 (TempCtx.supportsBelowCtx_append
      (by decide) hs4 hs5)))
  have hLiftAll : Slot3MicroEngineAux.TempCtxLiftEx 275 352 magUnpack275Ctx :=
      Slot3MicroEngineAux.TempCtxLiftEx.append hLift1 (Slot3MicroEngineAux.TempCtxLiftEx.append
      hLift2 (Slot3MicroEngineAux.TempCtxLiftEx.append hLift3
      (Slot3MicroEngineAux.TempCtxLiftEx.append hLift4 hLift5)))
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock275_spec (curEnd := 352) (by decide) (by decide)
    magDest21 magSrc21
    (fun idx ↦ by dsimp [magDest21, p57MW]; omega) magDest21_inj
    (fun idx ↦ by dsimp only [magSrc21]; split_ifs <;> (dsimp; omega))
    magUnpack275Ctx hDisjAll hSuppAll hLiftAll
  have hCntTot : magUnpack275Ctx.countTempAnd = 68 := by
    dsimp only [magUnpack275Ctx]
    repeat rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd]
    rw [hCnt1, hCnt3, hCnt4, hCnt5]
    rfl
  have hB' : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w b, q = p57MW w b) magUnpack275 :=
    ⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q
      (fun ⟨idx, h⟩ ↦ hq ⟨⟨idx.val / 7, by omega⟩,⟨idx.val % 7, by omega⟩, h⟩)⟩
  refine ⟨hB', hCnt.trans hCntTot, fun β hβ hmu w b ↦ ?_⟩
  set u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
  have huBitAll : ∀ i : Fin 22, β (u22WAux i) = if u22.val.testBit i.val then 1 else 0 :=
    u22_testBit_eq_wire u22WAux β u22 rfl
  clear_value u22
  let idx : Fin 21 := ⟨7 * w.val + b.val, by have := w.isLt; have := b.isLt; omega⟩
  have hdest : magDest21 idx = p57MW w b :=
    Fin.ext (by have := b.isLt; dsimp [magDest21, p57MW, idx]; omega)
  rw [← hdest]
  dsimp only [magUnpack275]
  rw [hEv β hβ idx, hdest]
  refine congrArg (β (p57MW w b) + ·) ?_
  obtain ⟨hcl1, hpres1, hsOut1⟩ := hEval1 β hβ
  have hm_lt : bitsVal (fun i ↦ β (muW i)) < 8 := bitsVal_lt_two_pow _
  have hchk1 := (Slot3MicroEngineAux.allBelow_iff 8 Slot3MicroEngineAux.mu3OneHot7GeCheck).mp
    Slot3MicroEngineAux.mu3OneHot7Ge_eval_ok _ hm_lt
  dsimp only [Slot3MicroEngineAux.mu3OneHot7GeCheck] at hchk1
  simp only [Bool.and_eq_true] at hchk1
  let k1 := Slot3MicroEngineAux.ctxMicro muW muW_inj 275 14 6 hin1
    Slot3MicroEngineAux.mu3OneHot7GeOps Slot3MicroEngineAux.mu3OneHot7Ge_meta3 (by decide)
  set β₁ := k1.fwdBits β
  have hu_β₁ : ∀ i : Fin 22, β₁ (u22WAux i) = β (u22WAux i) :=
    fun i ↦ hpres1 hchk1.1.1 (u22WAux i) (by dsimp [u22WAux]; omega)
  have hsel_β₁ : ∀ a : Fin 7, β₁ (magSel7W a) = if shellMu3 u22 = a.val then 1 else 0 := fun a ↦ by
    have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
    have ha := (Slot3MicroEngineAux.allBelow_iff 7 _).mp hchk1.1.2 a.val a.isLt
    simp only [beq_iff_eq] at ha
    dsimp only [magSel7W]
    rw [hsOut1 _ hb.1 hb.2, ha, hmu]
    by_cases he : shellMu3 u22 = a.val <;> simp [Slot3MicroEngineAux.boolToZMod2, he]
  have hge_β₁ : ∀ a : Fin 7, β₁ (magGeW a) = if a.val ≤ shellMu3 u22 then 1 else 0 := fun a ↦ by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds a
    have ha := (Slot3MicroEngineAux.allBelow_iff 7 _).mp hchk1.2 a.val a.isLt
    simp only [beq_iff_eq] at ha
    dsimp only [magGeW]
    rw [hsOut1 _ hb.1 hb.2, ha, hmu]
    have hmu7 : shellMu3 u22 < 7 := shellMu3_lt_seven u22
    by_cases hle : a.val ≤ shellMu3 u22 <;> simp [Slot3MicroEngineAux.boolToZMod2, hle, hmu7]
  have hcl1_cut : cleanRem 437 (437 - 290) β₁ := cleanRem_anti (by decide) hcl1
  have hfwd2 := Slot3MicroEngineAux.ctxCliffAlloc_fwdBits 290 (by decide) c2 hc2_supp β₁ hcl1_cut
  set β₂ := c2.eval β₁
  have hz289 : β₁ ⟨289, by decide⟩ = 0 := hcl1 ⟨289, by decide⟩ (by dsimp; omega)
  have hcl2 : cleanRem 437 (437 - 290) β₂ := fun q hq ↦ by
    dsimp only [β₂, c2, CliffProg.eval]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
    exact hcl1_cut q hq
  have hlt289_β₂ : ∀ q : Wire 437, q.val < 289 → β₂ q = β₁ q := fun q hq ↦ by
    dsimp only [β₂, c2, CliffProg.eval]
    exact Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)) _ _
  have hw289_β₂ : β₂ ⟨289, by decide⟩ = β (u22WAux 0) := by
    dsimp only [β₂, c2, CliffProg.eval]
    rw [Function.update_self, hz289, zero_add, hu_β₁ 0]
  let k3 := Slot3MicroEngineAux.ctxAndPairs 6 290 (by decide) l3 r3 hne3 hl3 hr3
  obtain ⟨hcl3, hpres3, hpair3⟩ := hEval3 β₂ hcl2
  set β₃ := k3.fwdBits β₂
  obtain ⟨hcl4, hpres4, hout4⟩ := hEval4 β₃ hcl3
  set β₄ := (ctxMagAxisLoop 1 296 (by decide) (by decide) 7 le_rfl).fwdBits β₃
  obtain ⟨_, hpres5, hout5⟩ := hEval5 β₄ hcl4
  set β₅ := (ctxMagAxisLoop 2 324 (by decide) (by decide) 7 le_rfl).fwdBits β₄
  have hAllFwd : magUnpack275Ctx.fwdBits β = β₅ := by
    dsimp only [magUnpack275Ctx]
    rw [Slot3MicroEngineAux.TempCtx.append_fwdBits, Slot3MicroEngineAux.TempCtx.append_fwdBits,
      Slot3MicroEngineAux.TempCtx.append_fwdBits, Slot3MicroEngineAux.TempCtx.append_fwdBits]
    exact congrArg (fun x ↦ (ctxMagAxisLoop 2 324 (by decide) (by decide) 7 le_rfl).fwdBits
      ((ctxMagAxisLoop 1 296 (by decide) (by decide) 7 le_rfl).fwdBits (k3.fwdBits x))) hfwd2
  rw [hAllFwd]
  have hsel_β₃ : ∀ a : Fin 7, β₃ (magSel7W a) = if shellMu3 u22 = a.val then 1 else 0 := fun a ↦ by
    have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
    rw [hpres3 _ (by dsimp [magSel7W]; omega), hlt289_β₂ _ (by dsimp [magSel7W]; omega), hsel_β₁ a]
  have hu_β₃ : ∀ i : Fin 22, β₃ (u22WAux i) = if u22.val.testBit i.val then 1 else 0 :=
    fun i ↦ by
      rw [hpres3 _ (by dsimp [u22WAux]; omega), hlt289_β₂ _ (by dsimp [u22WAux]; omega),
        hu_β₁ i, huBitAll i]
  have hw_cases : w = 0 ∨ w = 1 ∨ w = 2 :=
    match w with
    | ⟨0, _⟩ => .inl rfl
    | ⟨1, _⟩ => .inr (.inl rfl)
    | ⟨2, _⟩ => .inr (.inr rfl)
    | ⟨_ + 3, h⟩ => absurd h (by omega)
  rcases hw_cases with rfl | rfl | rfl
  · have hidx0 : idx.val < 7 := by have := b.isLt; dsimp [idx]; omega
    have hsrc0 : magSrc21 idx = ⟨289 + b.val, by have := b.isLt; omega⟩ := by
      dsimp [magSrc21]; rw [s3DitePos hidx0]; exact Fin.ext (by dsimp [idx]; omega)
    rw [hsrc0, hpres5 _ (by have := b.isLt; dsimp; omega),
      hpres4 _ (by have := b.isLt; dsimp; omega)]
    by_cases hb0 : b.val = 0
    · have hb_eq : b = 0 := Fin.ext hb0
      subst hb_eq
      have hw_eq : (⟨289 + (0 : Fin 7).val, by omega⟩ : Wire 437) = ⟨289, by decide⟩ := rfl
      rw [hw_eq, hpres3 _ (by dsimp; omega), hw289_β₂, huBitAll 0, shellMagCoord3_testBit_eq]
      simp
    · let i : Fin 6 := ⟨b.val - 1, by have := b.isLt; omega⟩
      have hw_eq : (⟨289 + b.val, by have := b.isLt; omega⟩ : Wire 437) =
          ⟨290 + i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
      have hi1 : (⟨i.val + 1, by omega⟩ : Fin 7) = b := Fin.ext (by dsimp [i]; omega)
      have hi22 : (⟨i.val + 1, by omega⟩ : Fin 22) = ⟨b.val, by have := b.isLt; omega⟩ :=
        Fin.ext (by dsimp [i]; omega)
      rw [hw_eq, hpair3 i]
      dsimp only [l3, r3]
      have h1_lt : (magGeW ⟨i.val + 1, by omega⟩).val < 289 := by
        have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
        dsimp at hb; dsimp [magGeW]; omega
      rw [hlt289_β₂ _ h1_lt, hlt289_β₂ _ (by dsimp [u22WAux]; omega),
        hge_β₁, hu_β₁, huBitAll, hi1, hi22, shellMagCoord3_testBit_eq]
      change (if b.val ≤ shellMu3 u22 then 1 else 0) * (if u22.val.testBit b.val then 1 else 0) =
        if decide (b.val ≤ shellMu3 u22) && u22.val.testBit (0 * (shellMu3 u22 + 1) + b.val)
          then 1 else 0
      rw [Nat.zero_mul, Nat.zero_add]
      by_cases hle : b.val ≤ shellMu3 u22 <;>
        by_cases htb : u22.val.testBit b.val = true <;> simp [hle, htb]
  · have hsrc1 : magSrc21 idx =
        ⟨296 + magDotOff b.castSucc, by have := magDotOff_castSucc_le b; omega⟩ := by
      dsimp [magSrc21]
      rw [s3DiteNeg (by dsimp [idx]; omega), s3DitePos (by have := b.isLt; dsimp [idx]; omega)]
      exact Fin.ext (by
        have hfin : (⟨idx.val - 7, by have := b.isLt; dsimp [idx]; omega⟩ : Fin 8) = b.castSucc :=
          Fin.ext (by dsimp [idx]; omega)
        simp [hfin])
    rw [hsrc1, hpres5 _ (by have := magDotOff_castSucc_le b; dsimp; omega), hout4 b b.isLt]
    exact magDotSum_eq u22 1 b (fun a ↦ β₃ (magSel7W a)) (fun i ↦ β₃ (u22WAux i)) hsel_β₃ hu_β₃
  · have hsrc2 : magSrc21 idx =
        ⟨324 + magDotOff b.castSucc, by have := magDotOff_castSucc_le b; omega⟩ := by
      dsimp [magSrc21]
      rw [s3DiteNeg (by dsimp [idx]; omega), s3DiteNeg (by dsimp [idx]; omega)]
      exact Fin.ext (by
        have hfin : (⟨idx.val - 14, by have := b.isLt; dsimp [idx]; omega⟩ : Fin 8) = b.castSucc :=
          Fin.ext (by dsimp [idx]; omega)
        simp [hfin])
    rw [hsrc2, hout5 b b.isLt]
    exact magDotSum_eq u22 2 b (fun a ↦ β₄ (magSel7W a)) (fun i ↦ β₄ (u22WAux i))
      (fun a ↦ by
        have := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
        rw [hpres4 _ (by dsimp [magSel7W]; omega), hsel_β₃ a])
      (fun i ↦ by rw [hpres4 _ (by dsimp [u22WAux]; omega), hu_β₃ i])
theorem magUnpack275_spec :
    IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w b, q = p57MW w b) magUnpack275 ∧
      (∀ β, cleanRem 437 (437 - 275) β →
        let u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
        bitsVal (fun j ↦ β (muW j)) = shellMu3 u22 →
        ∀ (w : Fin 3) (b : Fin 7),
          magUnpack275.evalBits β (p57MW w b) = β (p57MW w b) +
            if (shellMagCoord3 u22 w).testBit b.val then 1 else 0) :=
  ⟨magUnpack275_spec_full.1, magUnpack275_spec_full.2.2⟩
theorem cliff_cleanRem {M cur : ℕ} (hcur : cur ≤ M) :
    ∀ {c : CliffProg M}, c.SupportsBelow cur →
      ∀ {β : BitAssignment M}, cleanRem M (M - cur) β → cleanRem M (M - cur) (c.eval β) := by
  intro c hc β hβ w hw
  exact (CliffProg.eval_outside c hc β w (by omega)).trans (hβ w hw)
def vsMutW (q : Wire 437) : Prop := q = validStaticW
def axisFastVal (p : Fin 256) (m s : ℕ) : ℕ :=
  let pFlip := if p.val < 128 then p.val + 128 else p.val - 128
  let b8 := if s = 1 then 255 - m else m
  let lt := if 255 - pFlip < b8 then 1 else 0
  (p.val + b8 + lt) % 256
theorem axisFastVal_lt (p : Fin 256) (m s : ℕ) : axisFastVal p m s < 256 :=
  Nat.mod_lt _ (by decide)
theorem axisFastStep_eq_s3ProjStepHw (p : Fin 256) (m s : ℕ) (hp : p.val ≠ 128)
    (hm : m < 128) (hs : s ≤ 1) : axisFastVal p m s = (s3ProjStepHw p m s).1.val := by
  have hp_lt := p.isLt
  unfold axisFastVal s3ProjStepHw
  dsimp only
  split_ifs <;> omega
theorem ctx_fwdBits_pres {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {K : TempCtx M}, K.DisjointFrom mutW →
      ∀ (β : BitAssignment M) {w : Wire M}, mutW w → K.fwdBits β w = β w := by
  intro K hDisj β w hw
  exact Slot3MicroEngineAux.TempCtx.fwdBits_mut hDisj β hw
theorem ctx_fwdBits_clean {M next : ℕ} (hnext : next ≤ M) :
    ∀ {K : TempCtx M}, K.SupportsBelowCtx next →
      ∀ {β : BitAssignment M}, cleanRem M (M - next) β → cleanRem M (M - next) (K.fwdBits β) := by
  intro K hSupp β hβ u hu
  exact (Slot3MicroEngineAux.TempCtx.fwdBits_outside hSupp β u (by omega)).trans (hβ u hu)
def axAW (b : Fin 8) : Wire 437 := ⟨275 + b.val, by omega⟩
def axBW (b : Fin 8) : Wire 437 := ⟨283 + b.val, by omega⟩
def axBAddW (b : Fin 8) : Wire 437 := ⟨291 + b.val, by omega⟩
def axLtW : Wire 437 := ⟨307, by decide⟩
def axPrepCliff (w : Fin 3) : CliffProg 437 :=
  let c1 := cnotVec 8 (p57ProjW w) axAW
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axAW]; omega))
  let c2 := xVec 7 (fun b : Fin 7 ↦ axAW b.castSucc)
  let c3 := cnotVec 7 (p57MW w) (fun b : Fin 7 ↦ axBW b.castSucc)
    (fun b ↦ wire_ne_of_lt (by dsimp [p57MW, axBW]; omega))
  let c4 := cnotVec 8 (fun _ ↦ p57S3W w) axBW
    (fun b ↦ wire_ne_of_lt (by dsimp [p57S3W, axBW]; omega))
  let c5 := cnotVec 8 axBW axBAddW
    (fun b ↦ wire_ne_of_lt (by dsimp [axBW, axBAddW]; omega))
  .seq c1 (.seq c2 (.seq c3 (.seq c4 c5)))
theorem axPrepCliff_props (w : Fin 3) : (axPrepCliff w).SupportsBelow 299 ∧ CliffDisjoint
    (fun q ↦ ∃ b, q = pBufW w b) (axPrepCliff w) ∧
    (∀ β (q : Wire 437), q.val < 275 → (axPrepCliff w).eval β q = β q) ∧ (∀ β, cleanRem 437
    (437 - 275) β → bitsVal (fun b ↦ (axPrepCliff w).eval β (axAW b)) = 255 - (if bitsVal (fun
    b ↦ β (p57ProjW w b)) < 128 then bitsVal (fun b ↦ β (p57ProjW w b)) + 128 else bitsVal
    (fun b ↦ β (p57ProjW w b)) - 128) ∧ bitsVal (fun b ↦ (axPrepCliff w).eval β (axBW b)) =
    (if (β (p57S3W w)).val = 1 then 255 - bitsVal (fun b ↦ β (p57MW w b)) else bitsVal (fun b
    ↦ β (p57MW w b))) ∧ bitsVal (fun b ↦ (axPrepCliff w).eval β (axBAddW b)) = (if (β (p57S3W
    w)).val = 1 then 255 - bitsVal (fun b ↦ β (p57MW w b)) else bitsVal (fun b ↦ β (p57MW w
    b)))) := by
  have hinjA : Function.Injective axAW := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [axAW] at hv; omega)
  have hinjA7 : Function.Injective (fun b : Fin 7 ↦ axAW b.castSucc) := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [axAW] at hv; omega)
  have hinjB : Function.Injective axBW := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [axBW] at hv; omega)
  have hinjB7 : Function.Injective (fun b : Fin 7 ↦ axBW b.castSucc) := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [axBW] at hv; omega)
  have hinjBA : Function.Injective axBAddW := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [axBAddW] at hv; omega)
  let hne1 : ∀ b : Fin 8, p57ProjW w b ≠ axAW b :=
    fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axAW]; omega)
  let hne3 : ∀ b : Fin 7, p57MW w b ≠ axBW b.castSucc :=
    fun b ↦ wire_ne_of_lt (by dsimp [p57MW, axBW]; omega)
  let hne4 : ∀ b : Fin 8, p57S3W w ≠ axBW b :=
    fun b ↦ wire_ne_of_lt (by dsimp [p57S3W, axBW]; omega)
  let hne5 : ∀ b : Fin 8, axBW b ≠ axBAddW b :=
    fun b ↦ wire_ne_of_lt (by dsimp [axBW, axBAddW]; omega)
  have hDisjBelow (u : Wire 437) (hu : u.val < 150 ∨ 174 ≤ u.val) : ¬ ∃ b, u = pBufW w b :=
    fun ⟨b, h⟩ ↦ by
      have hv := congrArg Fin.val h
      dsimp [pBufW] at hv
      omega
  have hc1 := fun δ ↦ cnotVec_eval_eq (p57ProjW w) axAW hne1 hinjA
    (fun i j ↦ wire_ne_of_lt (by dsimp [p57ProjW, axAW]; omega)) δ
  have hc2 := fun δ ↦ xVec_eval_eq (fun b : Fin 7 ↦ axAW b.castSucc) hinjA7 δ
  have hc3 := fun δ ↦ cnotVec_eval_eq (p57MW w) (fun b : Fin 7 ↦ axBW b.castSucc) hne3 hinjB7
    (fun i j ↦ wire_ne_of_lt (by dsimp [p57MW, axBW]; omega)) δ
  have hc4 := fun δ ↦ cnotVec_eval_eq (fun _ ↦ p57S3W w) axBW hne4 hinjB
    (fun _ j ↦ wire_ne_of_lt (by dsimp [p57S3W, axBW]; omega)) δ
  have hc5 := fun δ ↦ cnotVec_eval_eq axBW axBAddW hne5 hinjBA
    (fun i j ↦ wire_ne_of_lt (by dsimp [axBW, axBAddW]; omega)) δ
  refine ⟨⟨cnotVec_supportsBelowAux 8 _ _ hne1
        (fun b ↦ by dsimp [p57ProjW]; omega) (fun b ↦ by dsimp [axAW]; omega),
      xVec_supportsBelow 7 _ (fun b ↦ by dsimp [axAW]; omega),
      cnotVec_supportsBelowAux 7 _ _ hne3
        (fun b ↦ by dsimp [p57MW]; omega) (fun b ↦ by dsimp [axBW]; omega),
      cnotVec_supportsBelowAux 8 _ _ hne4
        (fun _ ↦ by dsimp [p57S3W]; omega) (fun b ↦ by dsimp [axBW]; omega),
      cnotVec_supportsBelowAux 8 _ _ hne5
        (fun b ↦ by dsimp [axBW]; omega) (fun b ↦ by dsimp [axBAddW]; omega)⟩,
    ⟨cnotVec_cliffDisjoint 8 _ _ hne1
        (fun j ↦ hDisjBelow _ (Or.inl (by dsimp [p57ProjW]; omega)))
        (fun j ↦ hDisjBelow _ (Or.inr (by dsimp [axAW]; omega))),
      xVec_disjoint 7 _ (fun j ↦ hDisjBelow _ (Or.inr (by dsimp [axAW]; omega))),
      cnotVec_cliffDisjoint 7 _ _ hne3
        (fun j ↦ hDisjBelow _ (Or.inr (by dsimp [p57MW]; omega)))
        (fun j ↦ hDisjBelow _ (Or.inr (by dsimp [axBW]; omega))),
      cnotVec_cliffDisjoint 8 _ _ hne4
        (fun _ ↦ hDisjBelow _ (Or.inl (by dsimp [p57S3W]; omega)))
        (fun j ↦ hDisjBelow _ (Or.inr (by dsimp [axBW]; omega))),
      cnotVec_cliffDisjoint 8 _ _ hne5
        (fun j ↦ hDisjBelow _ (Or.inr (by dsimp [axBW]; omega)))
        (fun j ↦ hDisjBelow _ (Or.inr (by dsimp [axBAddW]; omega)))⟩,
    fun β q hq ↦ by
      dsimp only [axPrepCliff, CliffProg.eval]
      rw [(hc5 _).1 q (fun j ↦ wire_ne_of_lt (by dsimp [axBAddW]; omega)),
        (hc4 _).1 q (fun j ↦ wire_ne_of_lt (by dsimp [axBW]; omega)),
        (hc3 _).1 q (fun j ↦ wire_ne_of_lt (by dsimp [axBW]; omega)),
        (hc2 _).1 q (fun j ↦ wire_ne_of_lt (by dsimp [axAW]; omega)),
        (hc1 _).1 q (fun j ↦ wire_ne_of_lt (by dsimp [axAW]; omega))],
    fun β hβ ↦ ?_⟩
  let β₁ := (cnotVec 8 (p57ProjW w) axAW hne1).eval β
  let β₂ := (xVec 7 (fun b : Fin 7 ↦ axAW b.castSucc)).eval β₁
  let β₃ := (cnotVec 7 (p57MW w) (fun b : Fin 7 ↦ axBW b.castSucc) hne3).eval β₂
  let β₄ := (cnotVec 8 (fun _ ↦ p57S3W w) axBW hne4).eval β₃
  let β₅ := (cnotVec 8 axBW axBAddW hne5).eval β₄
  have hβ₂_ge283 (q : Wire 437) (hq : 283 ≤ q.val) : β₂ q = 0 := by
    dsimp only [β₂, β₁]
    rw [(hc2 _).1 _ (fun j ↦ wire_ne_of_gt (by dsimp [axAW]; omega)),
      (hc1 β).1 _ (fun j ↦ wire_ne_of_gt (by dsimp [axAW]; omega))]
    exact hβ q (by omega)
  have hβ₂_lt275 (q : Wire 437) (hq : q.val < 275) : β₂ q = β q := by
    dsimp only [β₂, β₁]
    rw [(hc2 _).1 _ (fun j ↦ wire_ne_of_lt (by dsimp [axAW]; omega)),
      (hc1 β).1 _ (fun j ↦ wire_ne_of_lt (by dsimp [axAW]; omega))]
  have hA : (fun b : Fin 8 ↦ β₅ (axAW b)) =
      fun b : Fin 8 ↦ if b.val < 7 then β (p57ProjW w b) + 1 else β (p57ProjW w b) := by
    funext b; dsimp only [β₅, β₄, β₃, β₂, β₁]
    rw [(hc5 _).1 _ (fun j ↦ wire_ne_of_lt (by dsimp [axAW, axBAddW]; omega)),
      (hc4 _).1 _ (fun j ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega)),
      (hc3 _).1 _ (fun j ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega))]
    cases b using Fin.lastCases with
    | last =>
        rw [(hc2 _).1 _ (fun j ↦ wire_ne_of_gt (by dsimp [axAW, Fin.last]; have := j.isLt; omega)),
          (hc1 β).2 (Fin.last 7), hβ _ (by dsimp [axAW]; omega), zero_add]; simp
    | cast b7 =>
        rw [(hc2 _).2 b7, (hc1 β).2 b7.castSucc, hβ _ (by dsimp [axAW]; omega), zero_add]
        simp [b7.isLt]
  have hB4 : (fun b : Fin 8 ↦ β₄ (axBW b)) = Fin.snoc (α := fun _ ↦ ZMod 2)
      (fun b : Fin 7 ↦ β (p57MW w b) + β (p57S3W w)) (β (p57S3W w)) := by
    funext b
    have hs_eq : β₃ (p57S3W w) = β (p57S3W w) :=
      ((hc3 β₂).1 _ (fun j ↦ wire_ne_of_lt (by dsimp [p57S3W, axBW]; omega))).trans
        (hβ₂_lt275 _ (by dsimp [p57S3W]; omega))
    dsimp only [β₄]; rw [(hc4 β₃).2 b, hs_eq]; dsimp only [β₃]
    cases b using Fin.lastCases with
    | last =>
        rw [Fin.snoc_last,
          (hc3 β₂).1 _ (fun j ↦ wire_ne_of_gt (by dsimp [axBW, Fin.last]; have := j.isLt; omega)),
          hβ₂_ge283 _ (by dsimp [axBW]; omega), zero_add]
    | cast b7 =>
        rw [Fin.snoc_castSucc, (hc3 β₂).2 b7, hβ₂_ge283 _ (by dsimp [axBW]; omega), zero_add,
          hβ₂_lt275 _ (by dsimp [p57MW]; omega)]
  have hB5 : (fun b : Fin 8 ↦ β₅ (axBW b)) = fun b : Fin 8 ↦ β₄ (axBW b) :=
    funext fun b ↦ (hc5 β₄).1 _ (fun j ↦ wire_ne_of_lt (by dsimp [axBW, axBAddW]; omega))
  have hBA5 : (fun b : Fin 8 ↦ β₅ (axBAddW b)) = fun b : Fin 8 ↦ β₄ (axBW b) :=
    funext fun b ↦ by
      conv_lhs => dsimp only [β₅]
      have hz_ba : β₄ (axBAddW b) = 0 := by
        dsimp only [β₄, β₃]
        rw [(hc4 _).1 _ (fun j ↦ wire_ne_of_gt (by dsimp [axBW, axBAddW]; omega)),
          (hc3 β₂).1 _ (fun j ↦ wire_ne_of_gt (by dsimp [axBW, axBAddW]; omega))]
        exact hβ₂_ge283 _ (by dsimp [axBAddW]; omega)
      rw [(hc5 β₄).2 b, hz_ba, zero_add]
  change bitsVal (fun b ↦ β₅ (axAW b)) = _ ∧ bitsVal (fun b ↦ β₅ (axBW b)) = _ ∧
    bitsVal (fun b ↦ β₅ (axBAddW b)) = _
  rw [hA, hB5, hBA5, hB4, bitsVal_invLow7, bitsVal_xorSnoc7]
  exact ⟨rfl, rfl, rfl⟩
def accMutW (q : Wire 437) : Prop := q = accWAux
def accSel7W (a : Fin 7) : Wire 437 :=
  ⟨275 + (Slot3MicroEngineAux.getNatAt Slot3MicroEngineAux.mu3Sel7Slots a.val - 3), by
    have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds11 a; omega⟩
def accMaskCliff1 (dst : Wire 437) (hdst : 283 ≤ dst.val) (pred : Fin 7 → Bool) :
    (k : ℕ) → k ≤ 7 → CliffProg 437
  | 0, _ => .nil
  | k + 1, hk =>
      let prev := accMaskCliff1 dst hdst pred k (by omega)
      if pred ⟨k, by omega⟩ then
        .seq prev (.cnot (accSel7W ⟨k, by omega⟩) dst
          (wire_ne_of_lt (by
            have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds11 ⟨k, by omega⟩
            dsimp at hb
            dsimp [accSel7W]; omega)))
      else prev
theorem accMaskCliff1_props (dst : Wire 437) (hdst : 283 ≤ dst.val) (pred : Fin 7 → Bool)
    {mutW : Wire 437 → Prop} (hns : ∀ a, ¬ mutW (accSel7W a)) (hnd : ¬ mutW dst) :
    ∀ (k : ℕ) (hk : k ≤ 7),
      CliffDisjoint mutW (accMaskCliff1 dst hdst pred k hk) ∧
        (accMaskCliff1 dst hdst pred k hk).SupportsBelow (dst.val + 1) ∧
        (∀ (γ : BitAssignment 437) (q : Wire 437), q ≠ dst →
          (accMaskCliff1 dst hdst pred k hk).eval γ q = γ q) ∧
        (∀ γ : BitAssignment 437,
          (accMaskCliff1 dst hdst pred k hk).eval γ dst =
            γ dst + ∑ i : Fin k,
              if pred ⟨i.val, by omega⟩ then γ (accSel7W ⟨i.val, by omega⟩) else 0)
  | 0, _ => ⟨trivial, trivial, fun _ _ _ ↦ rfl, fun _ ↦ by simp [accMaskCliff1, CliffProg.eval]⟩
  | k + 1, hk => by
      obtain ⟨hdP, hsP, hnonP, hevP⟩ := accMaskCliff1_props dst hdst pred hns hnd k (by omega)
      dsimp only [accMaskCliff1]
      by_cases hp : pred ⟨k, by omega⟩ = true
      · rw [s3ItePos hp]
        have hs_lt : (accSel7W ⟨k, by omega⟩).val < dst.val := by
          have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds11 ⟨k, by omega⟩
          dsimp at hb
          dsimp [accSel7W]; omega
        refine ⟨⟨hdP, hns _, hnd⟩,⟨hsP, by omega, by omega⟩, fun γ q hq ↦ ?_, fun γ ↦ ?_⟩
        · dsimp only [CliffProg.eval]
          rw [Function.update_of_ne hq]
          exact hnonP γ q hq
        · dsimp only [CliffProg.eval]
          have hsel_ne : accSel7W ⟨k, by omega⟩ ≠ dst := wire_ne_of_lt hs_lt
          rw [Function.update_self, hevP γ, hnonP γ _ hsel_ne, Fin.sum_univ_castSucc]
          simp [hp, add_assoc]
      · rw [s3IteNeg hp]
        refine ⟨hdP, hsP, hnonP, fun γ ↦ ?_⟩
        rw [hevP γ, Fin.sum_univ_castSucc]
        simp [hp]
def accNe128OutW (w : Fin 3) : Wire 437 := ⟨404 + 7 * w.val, by omega⟩
def ctxAccNe128Loop : (n : ℕ) → n ≤ 3 → TempCtx 437
  | 0, _ => .hole
  | n + 1, hn =>
      let w : Fin 3 := ⟨n, by omega⟩
      (ctxAccNe128Loop n (by omega)).append
        (Slot3MicroEngineAux.ctxMicro (p57ProjW w) (p57ProjW_injective w) (398 + 7 * n) 7 7
          (fun b ↦ by dsimp [p57ProjW]; omega)
          Slot3MicroEngineAux.ne128_8Ops Slot3MicroEngineAux.ne128_8_meta (by omega))
theorem ctxAccNe128Loop_scoped :
    ∀ (n : ℕ) (hn : n ≤ 3),
      let K := ctxAccNe128Loop n hn
      K.countTempAnd = 7 * n ∧
        (∀ {mutW : Wire 437 → Prop},
          (∀ w b, ¬ mutW (p57ProjW w b)) → (∀ q : Wire 437,398 ≤ q.val → ¬ mutW q) →
          K.DisjointFrom mutW ∧ K.SupportsBelowCtx (398 + 7 * n)) ∧
        Slot3MicroEngineAux.TempCtxLiftEx 398 (398 + 7 * n) K ∧
        (∀ γ : BitAssignment 437, cleanRem 437 (437 - 398) γ →
          cleanRem 437 (437 - (398 + 7 * n)) (K.fwdBits γ) ∧
          (∀ q : Wire 437, q.val < 398 → K.fwdBits γ q = γ q) ∧
          (∀ (w : Fin 3), w.val < n →
            K.fwdBits γ (accNe128OutW w) =
              Slot3MicroEngineAux.boolToZMod2
                (decide (bitsVal (fun b ↦ γ (p57ProjW w b)) ≠ 128))))
  | 0, _ =>
      ⟨rfl, fun _ _ ↦ ⟨trivial, trivial⟩, fun h ↦ ⟨_, h⟩,
        fun _ hγ ↦ ⟨hγ, fun _ _ ↦ rfl, fun _ hw ↦ absurd hw (Nat.not_lt_zero _)⟩⟩
  | n + 1, hn => by
      obtain ⟨hCntP, hPropsP, hLiftP, hEvalP⟩ := ctxAccNe128Loop_scoped n (by omega)
      let w₀ : Fin 3 := ⟨n, by omega⟩
      obtain ⟨hCntM, hPropsM, hLiftM, hEvalM⟩ :=
        Slot3MicroEngineAux.ctxMicro_scoped (p57ProjW w₀) (p57ProjW_injective w₀) (398 + 7 * n) 7 7
          (fun b ↦ by dsimp [p57ProjW]; omega)
          Slot3MicroEngineAux.ne128_8Ops Slot3MicroEngineAux.ne128_8_meta (by omega)
      have hLiftM' : Slot3MicroEngineAux.TempCtxLiftEx (398 + 7 * n) (398 + 7 * (n + 1)) _ :=
        Slot3MicroEngineAux.TempCtxLiftEx.mono hLiftM le_rfl (by omega) (by omega)
      dsimp only [ctxAccNe128Loop]
      refine ⟨by rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd, hCntP, hCntM]; omega,
        fun hnp hnq ↦ ?_,
        Slot3MicroEngineAux.TempCtxLiftEx.append hLiftP hLiftM',
        fun γ hγ ↦ ?_⟩
      · obtain ⟨hdP, hsP⟩ := hPropsP hnp hnq
        obtain ⟨hdM, hsM⟩ := hPropsM (fun b ↦ hnp w₀ b) (fun q hq ↦ hnq q (by omega))
        exact ⟨TempCtx.disjointFrom_append hdP hdM, TempCtx.supportsBelowCtx_append le_rfl
          (Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono (by omega) hsP)
          (Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono (by omega) hsM)⟩
      · obtain ⟨hcl₁, hpres₁, hout₁⟩ := hEvalP γ hγ
        set γ₁ := (ctxAccNe128Loop n (by omega)).fwdBits γ
        obtain ⟨hcl₂, hpres₂, hsOut₂⟩ := hEvalM γ₁ hcl₁
        have hm_lt : bitsVal (fun b ↦ γ₁ (p57ProjW w₀ b)) < 256 := bitsVal_lt_two_pow _
        have hchk := (Slot3MicroEngineAux.allBelow_iff 256 Slot3MicroEngineAux.ne128_8Check).mp
          Slot3MicroEngineAux.ne128_8_eval_ok _ hm_lt
        dsimp only [Slot3MicroEngineAux.ne128_8Check] at hchk
        simp only [Bool.and_eq_true, beq_iff_eq] at hchk
        rw [Slot3MicroEngineAux.TempCtx.append_fwdBits]
        refine ⟨cleanRem_anti (by omega) hcl₂, fun q hq ↦ ?_, fun w hw ↦ ?_⟩
        · rw [hpres₂ hchk.1 q (by omega), hpres₁ q hq]
        · by_cases hwn : w.val < n
          · rw [hpres₂ hchk.1 (accNe128OutW w) (by dsimp [accNe128OutW]; omega)]
            exact hout₁ w hwn
          · have hweq : w = w₀ := Fin.ext (by dsimp [w₀]; omega)
            subst hweq
            have hwire : accNe128OutW w₀ = ⟨398 + 7 * n + (14 - 8), by omega⟩ :=
              Fin.ext (by dsimp [accNe128OutW, w₀]; omega)
            rw [hwire, hsOut₂ 14 (by decide) (by decide), hchk.2]
            have hfn_eq : (fun b ↦ γ₁ (p57ProjW w₀ b)) = fun b ↦ γ (p57ProjW w₀ b) :=
              funext fun b ↦ hpres₁ _ (by dsimp [p57ProjW]; omega)
            rw [hfn_eq]
theorem accBool5_eq (v : ZMod 2) (R G0 G1 G2 : Prop) [Decidable R] [Decidable G0]
    [Decidable G1] [Decidable G2] : Slot3MicroEngineAux.boolToZMod2
    (decide (v = 1) && decide R && decide G0 && decide G1 && decide G2) = v *
    (if R then 1 else 0) * (if G0 ∧ G1 ∧ G2 then 1 else 0) := by
  rcases zmod2_eq_zero_or_one v with rfl | rfl <;>
  by_cases hr : R <;> by_cases g0 : G0 <;> by_cases g1 : G1 <;> by_cases g2 : G2 <;>
  simp [Slot3MicroEngineAux.boolToZMod2, hr, g0, g1, g2]
def rejW275 : Wire 437 := ⟨275, by decide⟩
def rejW276 : Wire 437 := ⟨276, by decide⟩
def rejKickCtx : TempCtx 437 := (ctxCliffAlloc (.x accWAux)).append ((ctxTempBit coinOkW
    accWAux rejW275 (by decide) (by decide) (by decide)).append (ctxTempBit rejW275 bParWAux
    rejW276 (by decide) (by decide) (by decide)))
def rejKick275 : TempPhaseProg 437 := rejKickCtx.plug (.z rejW276)
theorem rejKick275_spec : ValidCleanRem 437 (437 - 275) rejKick275 ∧ rejKick275.countTempAnd =
    2 ∧ (∀ β, cleanRem 437 (437 - 275) β → rejKick275.evalBits β = β) ∧ (∀ β, cleanRem 437
    (437 - 275) β → rejKick275.evalSign β = β coinOkW * (β accWAux + 1) * β bParWAux)
    := by
  have h1 : TempCtxLiftEx 275 275 (ctxCliffAlloc (.x accWAux)) :=
    TempCtxLiftEx.cliff (by decide) (.x accWAux)
      (by dsimp [CliffProg.SupportsBelow, accWAux]; omega)
  have h2 : TempCtxLiftEx 275 276
      (ctxTempBit coinOkW accWAux rejW275 (by decide) (by decide) (by decide)) :=
    TempCtxLiftEx.tempBit (by decide) coinOkW accWAux (by decide) (by decide) (by decide)
  have h3 : TempCtxLiftEx 276 277
      (ctxTempBit rejW275 bParWAux rejW276 (by decide) (by decide) (by decide)) :=
    TempCtxLiftEx.tempBit (by decide) rejW275 bParWAux (by decide) (by decide) (by decide)
  have hBlk := TempCtxLiftEx.probe (TempCtxLiftEx.append h1 (TempCtxLiftEx.append h2 h3)) rejW276
  have hCnt : rejKick275.countTempAnd = 2 := rfl
  refine ⟨hBlk.valid, hCnt, fun β hβ ↦ hBlk.bits β hβ, fun β hβ ↦ ?_⟩
  dsimp only [rejKick275, rejKickCtx]
  rw [hBlk.sign β hβ]
  change rejKickCtx.fwdBits β rejW276 = _
  dsimp only [rejKickCtx]
  rw [StepBBlock0.TempCtx.append_fwdBits,
    StepBBlock0.TempCtx.append_fwdBits]
  dsimp only [ctxCliffAlloc, ctxTempBit, TempCtx.fwdBits, CliffProg.eval]
  have hz275 : β rejW275 = 0 := hβ rejW275 (by dsimp [rejW275]; omega)
  have hz276 : β rejW276 = 0 := hβ rejW276 (by dsimp [rejW276]; omega)
  simp only[Function.update_self, Function.update_of_ne (by decide : rejW276 ≠ rejW275),
      Function.update_of_ne (by decide : rejW276 ≠ accWAux),
      Function.update_of_ne (by decide : rejW275 ≠ accWAux),
      Function.update_of_ne (by decide : coinOkW ≠ accWAux),
      Function.update_of_ne (by decide : bParWAux ≠ rejW275),
      Function.update_of_ne (by decide : bParWAux ≠ accWAux), hz275, hz276, zero_add]
def cSwap24_275 : TempPhaseProg 437 :=
  cswapRegProg 24 accWAux projFlat24 pBufFlat24 ⟨275, by decide⟩
    (fun k ↦ wire_ne_of_lt (by dsimp [projFlat24, pBufFlat24]; omega))
    (fun k ↦ wire_ne_of_gt (by dsimp [accWAux, projFlat24]; omega))
    (by decide)
    (fun _ ↦ by dsimp [projFlat24]; omega)
    (fun _ ↦ by dsimp [pBufFlat24]; omega)
theorem cSwap24_275_spec : ValidCleanRem 437 (437 - 275) cSwap24_275 ∧
    cSwap24_275.countTempAnd = 24 ∧
    (∀ β, cleanRem 437 (437 - 275) β → cSwap24_275.evalSign β = 0) ∧ (∀ β, cleanRem 437 (437 -
    275) β → cleanRem 437 (437 - 275) (cSwap24_275.evalBits β)) ∧ (∀ β, cleanRem 437 (437 -
    275) β → (∀ w b, cSwap24_275.evalBits β (p57ProjW w b) = if β accWAux = 1 then β
    (pBufW w b) else β (p57ProjW w b)) ∧ (∀ w b, cSwap24_275.evalBits β (pBufW w b) =
    if β accWAux = 1 then β (p57ProjW w b) else β (pBufW w b)) ∧ (∀ q : Wire 437, ¬(q.val
    < 24) → ¬(150 ≤ q.val ∧ q.val < 174) → cSwap24_275.evalBits β q = β q)) := by
  classical
  have hinjA : Function.Injective projFlat24 := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [projFlat24] at hv; omega)
  have hinjB : Function.Injective pBufFlat24 := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [pBufFlat24] at hv; omega)
  have hdisjAB : ∀ i j, projFlat24 i ≠ pBufFlat24 j := fun i j ↦
    wire_ne_of_lt (by dsimp [projFlat24, pBufFlat24]; omega)
  obtain ⟨hv, hev⟩ := cswapRegProg_valid_and_eval (M := 437) (rem := 437 - 275) (by decide)
    24 accWAux projFlat24 pBufFlat24 ⟨275, by decide⟩ _ _
    (fun k ↦ wire_ne_of_lt (by dsimp [accWAux, pBufFlat24]; omega))
    hinjA hinjB hdisjAB
    (by dsimp [accWAux]; omega)
    (fun i ↦ by dsimp [projFlat24]; omega)
    (fun i ↦ by dsimp [pBufFlat24]; omega)
    (by decide)
  have hCnt : cSwap24_275.countTempAnd = 24 := cswapRegProg_countTempAnd 24 _ _ _ _ _ _ _ _ _
  have hSgn : ∀ β, cleanRem 437 (437 - 275) β → cSwap24_275.evalSign β = 0 :=
    fun β _ ↦ cswapRegProg_evalSign 24 _ _ _ _ _ _ _ _ _ β
  have hOut : ∀ β, cleanRem 437 (437 - 275) β → ∀ q : Wire 437,
      ¬(q.val < 24) → ¬(150 ≤ q.val ∧ q.val < 174) → cSwap24_275.evalBits β q = β q :=
    fun β hβ q hnA hnB ↦ by
      dsimp only [cSwap24_275]
      rw [hev β hβ q,
        s3DiteNeg (fun ⟨i, hi⟩ ↦ hnA (by subst hi; dsimp [projFlat24]; omega)),
        s3DiteNeg (fun ⟨i, hi⟩ ↦ hnB (by subst hi; dsimp [pBufFlat24]; omega))]
  have hCl : ∀ β, cleanRem 437 (437 - 275) β → cleanRem 437 (437 - 275) (cSwap24_275.evalBits β) :=
    fun β hβ u hu ↦ (hOut β hβ u (by omega) (by omega)).trans (hβ u hu)
  refine ⟨hv, hCnt, hSgn, hCl, fun β hβ ↦ ⟨fun w b ↦ ?_, fun w b ↦ ?_, hOut β hβ⟩⟩
  · let k : Fin 24 := ⟨8 * w.val + b.val, by have := w.isLt; have := b.isLt; omega⟩
    have hk_eq : p57ProjW w b = projFlat24 k := rfl
    have hex : ∃ i : Fin 24, p57ProjW w b = projFlat24 i := ⟨k, hk_eq⟩
    have hk_ch : hex.choose = k := hinjA (hex.choose_spec.symm.trans hk_eq)
    dsimp only [cSwap24_275]
    rw [hev β hβ (p57ProjW w b), s3DitePos hex, hk_ch,
      show pBufFlat24 k = pBufW w b from
        Fin.ext (by dsimp [pBufFlat24, pBufW, k]; omega)]
  · let k : Fin 24 := ⟨8 * w.val + b.val, by have := w.isLt; have := b.isLt; omega⟩
    have hk_eq : pBufW w b = pBufFlat24 k :=
      Fin.ext (by dsimp [pBufW, pBufFlat24, k]; omega)
    have hex : ∃ i : Fin 24, pBufW w b = pBufFlat24 i := ⟨k, hk_eq⟩
    dsimp only [cSwap24_275]
    rw [hev β hβ (pBufW w b), s3DiteNeg (fun ⟨i, hi⟩ ↦ by
      have hv2 := congrArg Fin.val hi; dsimp [pBufW, projFlat24] at hv2; omega),
      s3DitePos hex, hinjB (hex.choose_spec.symm.trans hk_eq)]
    rfl
def s3FlipInW (w : Fin 3) (k : Fin 8) : Wire 437 :=
  if hk : k.val = 0 then accWAux else p57MW w ⟨k.val - 1, by omega⟩
theorem s3FlipInW_inj (w : Fin 3) : Function.Injective (s3FlipInW w) := fun i j h ↦ by
  dsimp only [s3FlipInW] at h
  split_ifs at h with hi hj
  · exact Fin.ext (by omega)
  · have hv := congrArg Fin.val h; dsimp [accWAux, p57MW] at hv; omega
  · have hv := congrArg Fin.val h; dsimp [accWAux, p57MW] at hv; omega
  · have hv := congrArg Fin.val h; dsimp [p57MW] at hv; exact Fin.ext (by omega)
def s3Flip1Ctx (w : Fin 3) : TempCtx 437 :=
  Slot3MicroEngineAux.ctxMicro (s3FlipInW w) (s3FlipInW_inj w) 275 7 7
    (fun k ↦ by dsimp only [s3FlipInW]; split_ifs <;> (dsimp [accWAux, p57MW]; omega))
    Slot3MicroEngineAux.s3Flip8Ops Slot3MicroEngineAux.s3Flip8_meta (by decide)
def s3Flip1_275 (w : Fin 3) : TempPhaseProg 437 :=
  xorBlock1Prog (p57S3W w) ⟨281, by decide⟩
    (by dsimp [p57S3W]; omega) (by decide) (s3Flip1Ctx w)
theorem s3Flip1_275_spec (w : Fin 3) : IsMutBlock 437 (437 - 275) (fun q ↦ q = p57S3W w)
    (s3Flip1_275 w) ∧ (s3Flip1_275 w).countTempAnd = 7 ∧ (∀ β, cleanRem 437 (437 - 275) β →
    (s3Flip1_275 w).evalBits β (p57S3W w) = β (p57S3W w) + β accWAux * (if bitsVal (fun j ↦ β
    (p57MW w j)) = 0 then 0 else 1)) := by
  let mut1 : Wire 437 → Prop := fun q ↦ ∃ _ : Fin 1, q = p57S3W w
  obtain ⟨hCntM, hPropsM, hLiftM, hEvalM⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped (s3FlipInW w) (s3FlipInW_inj w) 275 7 7
      (fun k ↦ by dsimp only [s3FlipInW]; split_ifs <;> (dsimp [accWAux, p57MW]; omega))
      Slot3MicroEngineAux.s3Flip8Ops Slot3MicroEngineAux.s3Flip8_meta (by decide)
  obtain ⟨hDisj, hSupp⟩ := hPropsM (mutW := mut1)
    (fun k ⟨_, h⟩ ↦ by
      have hv := congrArg Fin.val h
      dsimp only [s3FlipInW] at hv
      split_ifs at hv <;> (dsimp [accWAux, p57MW, p57S3W] at hv; omega))
    (fun q hq ⟨_, h⟩ ↦ by subst h; dsimp [p57S3W] at hq; omega)
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock1_275_spec (curEnd := 282) (by decide) (by decide)
    (p57S3W w) ⟨281, by decide⟩ (by dsimp [p57S3W]; omega) (by decide)
    (s3Flip1Ctx w) hDisj hSupp hLiftM
  refine ⟨hB, hCnt.trans hCntM, fun β hβ ↦ ?_⟩
  dsimp only [s3Flip1_275]
  rw [hEv β hβ]
  refine congrArg (β (p57S3W w) + ·) ?_
  obtain ⟨_, _, hsOut⟩ := hEvalM β hβ
  have hm_lt : bitsVal (fun k ↦ β (s3FlipInW w k)) < 256 := bitsVal_lt_two_pow _
  have hchk := (Slot3MicroEngineAux.allBelow_iff 256 Slot3MicroEngineAux.s3Flip8Check).mp
    Slot3MicroEngineAux.s3Flip8_eval_ok _ hm_lt
  dsimp only [Slot3MicroEngineAux.s3Flip8Check] at hchk
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have hwire281 : (⟨281, by decide⟩ : Wire 437) = ⟨275 + (14 - 8), by decide⟩ := rfl
  dsimp only [s3Flip1Ctx]
  rw [hwire281, hsOut 14 (by decide) (by decide), hchk.2]
  have hsplit := Slot3MicroEngineAux.bitsVal_succ_split (fun k : Fin 8 ↦ β (s3FlipInW w k))
  have htail : (fun j : Fin 7 ↦ β (s3FlipInW w j.succ)) = fun b : Fin 7 ↦ β (p57MW w b) :=
    funext fun j ↦ by
      have hne : j.succ.val ≠ 0 := by dsimp; omega
      dsimp only [s3FlipInW]
      rw [s3DiteNeg hne]
      exact congrArg (β ∘ p57MW w) (Fin.ext (by dsimp))
  have hhead : β (s3FlipInW w 0) = β accWAux := rfl
  rw [hhead, htail] at hsplit
  have ha_lt2 : (β accWAux).val < 2 := ZMod.val_lt _
  have hdiv : bitsVal (fun k ↦ β (s3FlipInW w k)) / 2 = bitsVal (fun b ↦ β (p57MW w b)) := by omega
  have htb0 := Slot3MicroEngineAux.bitsVal_testBit_eq (fun k ↦ β (s3FlipInW w k)) 0
  dsimp only [Fin.val_zero] at htb0
  rw [hhead] at htb0
  rw [htb0, hdiv]
  rcases zmod2_eq_zero_or_one (β accWAux) with h | h <;>
    simp [Slot3MicroEngineAux.boolToZMod2, h]
def s3Flip275 : TempPhaseProg 437 :=
  .seq (s3Flip1_275 0) (.seq (s3Flip1_275 1) (s3Flip1_275 2))
theorem s3Flip275_spec : IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w, q = p57S3W w) s3Flip275 ∧
    s3Flip275.countTempAnd = 21 ∧ (∀ β, cleanRem 437 (437 - 275) β → ∀ w : Fin 3,
    s3Flip275.evalBits β (p57S3W w) = β (p57S3W w) + β accWAux * (if bitsVal (fun j ↦ β
    (p57MW w j)) = 0 then 0 else 1)) := by
  let mutAll : Wire 437 → Prop := fun q ↦ ∃ w, q = p57S3W w
  have hBLift (u : Fin 3) : IsMutBlock 437 (437 - 275) mutAll (s3Flip1_275 u) := by
    obtain ⟨hB, _, _⟩ := s3Flip1_275_spec u
    exact ⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q (fun h ↦ hq ⟨u, h⟩)⟩
  obtain ⟨hB0, hc0, hE0⟩ := s3Flip1_275_spec 0
  obtain ⟨hB1, hc1, hE1⟩ := s3Flip1_275_spec 1
  obtain ⟨hB2, hc2, hE2⟩ := s3Flip1_275_spec 2
  refine ⟨StepBBlock0.IsMutBlock.seq (by decide) (hBLift 0)
      (StepBBlock0.IsMutBlock.seq (by decide) (hBLift 1) (hBLift 2)),
    by
      change (s3Flip1_275 0).countTempAnd +
        ((s3Flip1_275 1).countTempAnd + (s3Flip1_275 2).countTempAnd) = 21
      rw [hc0, hc1, hc2],
    fun β hβ w ↦ ?_⟩
  let β₁ := (s3Flip1_275 0).evalBits β
  let β₂ := (s3Flip1_275 1).evalBits β₁
  have hcl₁ := hB0.2.2.1 β hβ
  have hcl₂ := hB1.2.2.1 β₁ hcl₁
  have hm_ne (v u : Fin 3) (j : Fin 7) : p57MW u j ≠ p57S3W v := fun h ↦ by
    have hv := congrArg Fin.val h
    dsimp [p57MW, p57S3W] at hv
    omega
  have hm1 (u : Fin 3) (j : Fin 7) : β₁ (p57MW u j) = β (p57MW u j) :=
    hB0.2.2.2 β hβ _ (hm_ne 0 u j)
  have hm2 (u : Fin 3) (j : Fin 7) : β₂ (p57MW u j) = β (p57MW u j) :=
    (hB1.2.2.2 β₁ hcl₁ _ (hm_ne 1 u j)).trans (hm1 u j)
  change (s3Flip1_275 2).evalBits β₂ (p57S3W w) = _
  have hw3 : w = 0 ∨ w = 1 ∨ w = 2 :=
    match w with
    | ⟨0, _⟩ => .inl rfl
    | ⟨1, _⟩ => .inr (.inl rfl)
    | ⟨2, _⟩ => .inr (.inr rfl)
    | ⟨_ + 3, h⟩ => absurd h (by omega)
  rcases hw3 with rfl | rfl | rfl
  · rw [hB2.2.2.2 β₂ hcl₂ _ (by decide)]
    dsimp only [β₂]; rw [hB1.2.2.2 β₁ hcl₁ _ (by decide)]
    exact hE0 β hβ
  · rw [hB2.2.2.2 β₂ hcl₂ _ (by decide)]
    dsimp only [β₂]; rw [hE1 β₁ hcl₁]
    simp only [hm1]
    dsimp only [β₁]
    rw [hB0.2.2.2 β hβ (p57S3W 1) (by decide), hB0.2.2.2 β hβ accWAux (by decide)]
  · rw [hE2 β₂ hcl₂]
    simp only [hm2]
    dsimp only [β₂]
    rw [hB1.2.2.2 β₁ hcl₁ (p57S3W 2) (by decide), hB1.2.2.2 β₁ hcl₁ accWAux (by decide)]
    dsimp only [β₁]
    rw [hB0.2.2.2 β hβ (p57S3W 2) (by decide), hB0.2.2.2 β hβ accWAux (by decide)]
attribute [local irreducible]
  coinMuXor275 magUnpack275 sTrue18FwdPBuf275 sTrue18RevPBuf275 rejKick275 cSwap24_275
  s3Flip275
theorem twoPow22_eq : 2 ^ 22 = 4194304 := by decide
def getU22 (γ : BitAssignment 437) : Fin 4194304 :=
  ⟨bitsVal (fun i ↦ γ (u22WAux i)), lt_of_lt_of_eq (bitsVal_lt_two_pow _) twoPow22_eq⟩
def getProj (γ : BitAssignment 437) (w : Fin 3) : Fin 256 :=
  ⟨bitsVal (fun b ↦ γ (p57ProjW w b)), bitsVal_lt_two_pow _⟩
theorem bitsVal_congrAux {k : ℕ} {f g : Fin k → ZMod 2} (h : ∀ i, f i = g i) :
    bitsVal f = bitsVal g := by
  have hfn : f = g := funext h
  rw [hfn]
theorem bitsVal_congr_fn {k : ℕ} {f g : Fin k → ZMod 2} (h : f = g) :
    bitsVal f = bitsVal g := by
  rw [h]
theorem fin_mk_bitsVal_eq {k n : ℕ} (f g : Fin k → ZMod 2) (hf : bitsVal f < n)
    (hg : bitsVal g < n) (h : ∀ i, f i = g i) : (⟨bitsVal f, hf⟩ : Fin n) = ⟨bitsVal g, hg⟩ :=
    Fin.ext (congrArg bitsVal (funext h))
theorem getU22_congr {γ₁ γ₂ : BitAssignment 437}
    (h : ∀ i : Fin 22, γ₁ (u22WAux i) = γ₂ (u22WAux i)) : getU22 γ₁ = getU22 γ₂ :=
    fin_mk_bitsVal_eq _ _ _ _ h
theorem getProj_congr {γ₁ γ₂ : BitAssignment 437} {w : Fin 3}
    (h : ∀ b : Fin 8, γ₁ (p57ProjW w b) = γ₂ (p57ProjW w b)) : getProj γ₁ w = getProj
    γ₂ w := fin_mk_bitsVal_eq _ _ _ _ h
theorem elecsTrueRawValPBuf_eq (β : BitAssignment 437)
    (hm_val : ∀ w : Fin 3, bitsVal (fun b ↦ β (p57MW w b)) = shellMagCoord3 (getU22 β) w)
    (hpbuf7 : ∀ w : Fin 3, β (pBufW w ⟨7, by decide⟩) =
      if (axisFastVal (getProj β w) (shellMagCoord3 (getU22 β) w)
        (β (p57S3W w)).val).testBit 7 then 1 else 0) :
    sTrueRawValPBuf β = sTrueRawVal β := by
  refine sTrueRawValPBuf_eq_sTrueRawVal β fun w ↦ ?_
  rw [hm_val w]
  exact hpbuf7 w
theorem sTrueRawValPBuf_congr {γ₁ γ₂ : BitAssignment 437}
    (hp7 : ∀ w : Fin 3, γ₁ (p57ProjW w ⟨7, by decide⟩) = γ₂ (p57ProjW w ⟨7, by decide⟩))
    (hpb7 : ∀ w : Fin 3, γ₁ (p57PBufW w ⟨7, by decide⟩) = γ₂ (p57PBufW w ⟨7, by decide⟩))
    (hs : ∀ w : Fin 3, γ₁ (p57S3W w) = γ₂ (p57S3W w))
    (hm : ∀ (w : Fin 3) (b : Fin 7), γ₁ (p57MW w b) = γ₂ (p57MW w b)) :
    sTrueRawValPBuf γ₁ = sTrueRawValPBuf γ₂ := by
  unfold sTrueRawValPBuf
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hm_w : (fun b ↦ γ₁ (p57MW w b)) = fun b ↦ γ₂ (p57MW w b) := funext (hm w)
  simp only [hp7 w, hpb7 w, hs w, hm_w]
theorem seq_onReg_eval {M n : ℕ} (rComb : QRegister M n) (p₁ p₂ : TempPhaseProg M) :
    (((TempPhaseProg.seq p₁ p₂).onRegister rComb).toToffCircuit).eval =
      ((p₂.onRegister rComb).toToffCircuit).eval * ((p₁.onRegister rComb).toToffCircuit).eval := by
  simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
set_option backward.isDefEq.respectTransparency true
end Body
end
end ConfigStepBOuter
end StepBOuter
end
end ModStepBOuter

end QuantumComputation.Specs.StoppingPowerSolution
