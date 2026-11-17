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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosSpectatorPhase

@[expose] public section
set_option exponentiation.threshold 256
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

section ModProd57BoothHoist
@[expose] public section
namespace Prod57BoothHoist
section ConfigProd57BoothHoist
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency false
local instance (priority := 1000000) instNeZeroTwoPowProd57Booth (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open MeasureBranchHadamardSem (bit_cases)
open MomSlots35Slot3ProjNuclear (s3ProjStepHw)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
theorem zmod2_val_cases (b : ZMod 2) : b.val = 0 ∨ b.val = 1 := by
  revert b
  decide
theorem zmod2_val_le_one (b : ZMod 2) : b.val ≤ 1 := Nat.lt_succ_iff.mp (ZMod.val_lt b)
theorem s3LtLe {a b c : ℕ} (h1 : a < b) (h2 : b ≤ c) : a < c := Nat.lt_of_lt_of_le h1 h2
section Slot3ArithCombinators
theorem bitsVal_zero (W : ℕ) : bitsVal (fun _ : Fin W ↦ (0 : ZMod 2)) = 0 := by simp [bitsVal]
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
theorem bitsVal_flip_all : ∀ (W : ℕ) (f : Fin W → ZMod 2),
    bitsVal (fun j ↦ f j + 1) + bitsVal f = 2 ^ W - 1
  | 0, _ => rfl
  | W + 1, f => by
      rw [bitsVal_succ_split (fun j ↦ f j + 1), bitsVal_succ_split f]
      have hih := bitsVal_flip_all W (fun j ↦ f j.succ)
      have hp : 2 ^ (W + 1) = 2 * 2 ^ W ∧ 1 ≤ 2 ^ W := ⟨by ring, Nat.one_le_two_pow⟩
      rcases bit_cases (f 0) with h0 | h1
      · rw [h0]
        change (1 : ℕ) + 2 * bitsVal _ + (0 + 2 * bitsVal _) = _
        omega
      · rw [h1]
        change (0 : ℕ) + 2 * bitsVal _ + (1 + 2 * bitsVal _) = _
        omega
def fanoutCnot {M : ℕ} : (W : ℕ) → (ctrl : Wire M) → (dst : Fin W → Wire M) →
    (∀ j, ctrl ≠ dst j) → CliffProg M
  | 0, _, _, _ => .nil
  | W + 1, ctrl, dst, hne => .seq (.cnot ctrl (dst 0) (hne 0))
      (fanoutCnot W ctrl (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem fanoutCnot_supportsBelow {M bound : ℕ} : ∀ (W : ℕ) (ctrl : Wire M) (dst : Fin W → Wire M)
    (hne : ∀ j, ctrl ≠ dst j), ctrl.val < bound → (∀ j, (dst j).val < bound) →
    (fanoutCnot W ctrl dst hne).SupportsBelow bound
  | 0, _, _, _, _, _ => trivial
  | W + 1, ctrl, _, _, hc, hd =>
      ⟨⟨hc, hd 0⟩, fanoutCnot_supportsBelow W ctrl _ _ hc (fun j ↦ hd j.succ)⟩
theorem p57Slim_fanoutCnot_eq {M : ℕ} : ∀ (W : ℕ) (ctrl : Wire M) (dst : Fin W → Wire M)
    (hne : ∀ j, ctrl ≠ dst j),
    fanoutCnot W ctrl dst hne =
      Slot3MicroEngineAux.cnotVec W (fun _ ↦ ctrl) dst hne
  | 0, _, _, _ => rfl
  | W + 1, ctrl, dst, hne =>
      congrArg _ (p57Slim_fanoutCnot_eq W ctrl (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem fanoutCnot_eval {M : ℕ} (W : ℕ) (ctrl : Wire M) (dst : Fin W → Wire M)
    (hne : ∀ j, ctrl ≠ dst j) (hinj : Function.Injective dst) (β : BitAssignment M) (w : Wire M) :
    (fanoutCnot W ctrl dst hne).eval β w = if ∃ j, w = dst j then β w + β ctrl else β w := by
  rw [p57Slim_fanoutCnot_eq, Slot3MicroEngineAux.cnotVec_eval
    W (fun _ ↦ ctrl) dst hne hinj (fun _ j ↦ hne j) β w]
  by_cases h : ∃ j, w = dst j
  · simp [h]
  · simp [h]
def cnotVec {M : ℕ} : (W : ℕ) → (src dst : Fin W → Wire M) → (∀ j, src j ≠ dst j) → CliffProg M
  | 0, _, _, _ => .nil
  | W + 1, src, dst, hne => .seq (.cnot (src 0) (dst 0) (hne 0))
      (cnotVec W (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem p57Slim_cnotVec_eq {M : ℕ} : ∀ (W : ℕ) (src dst : Fin W → Wire M)
    (hne : ∀ j, src j ≠ dst j),
    cnotVec W src dst hne = Slot3MicroEngineAux.cnotVec W src dst hne
  | 0, _, _, _ => rfl
  | W + 1, src, dst, hne => congrArg _
      (p57Slim_cnotVec_eq W (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ))
theorem cnotVec_eval {M : ℕ} (W : ℕ) (src dst : Fin W → Wire M) (hne : ∀ j, src j ≠ dst j)
    (hinj : Function.Injective dst) (hdisj : ∀ i j, src i ≠ dst j)
    (β : BitAssignment M) (w : Wire M) : (cnotVec W src dst hne).eval β w =
      if h : ∃ j, w = dst j then β w + β (src h.choose) else β w := by
  rw [p57Slim_cnotVec_eq]
  exact Slot3MicroEngineAux.cnotVec_eval W src dst hne hinj hdisj β w
theorem TempCtx.fwdBits_mut {M : ℕ} {mutW : Wire M → Prop} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) : ∀ (β : BitAssignment M) {w : Wire M}, mutW w →
      K.fwdBits β w = β w := Slot3MicroEngineAux.TempCtx.fwdBits_mut hDisj
theorem TempCtx.supportsBelowCtx_mono {M b₁ b₂ : ℕ} (hle : b₁ ≤ b₂) {K : TempCtx M} :
    K.SupportsBelowCtx b₁ → K.SupportsBelowCtx b₂ :=
  Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono hle
theorem TempCtx.append_fwdBits {M : ℕ} (F G : TempCtx M) (β : BitAssignment M) :
    (F.append G).fwdBits β = G.fwdBits (F.fwdBits β) :=
  Slot3MicroEngineAux.TempCtx.append_fwdBits F G β
theorem TempCtx.scopedBlock_fwdBits {M rem : ℕ} (K : TempCtx M)
    (hEx : ∀ q : Wire M, ∃ sQ, ScopedBlock M rem sQ (.z q) (K.plug (.z q))) (q : Wire M) :
    ScopedBlock M rem K.fwdBits (.z q) (K.plug (.z q)) :=
  Slot3MicroEngineAux.TempCtx.scopedBlock_fwdBits K hEx q
theorem TempCtx.fwdBits_eq_of_block {M rem : ℕ} (K : TempCtx M) (u : Wire M)
    {sU : BitAssignment M → BitAssignment M} (hBlk : ScopedBlock M rem sU (.z u) (K.plug (.z u)))
    (β : BitAssignment M) (hβ : cleanRem M rem β) : K.fwdBits β u = sU β u :=
  Slot3MicroEngineAux.TempCtx.fwdBits_eq_of_block K u hBlk β hβ
theorem withCliffAlloc_valid_and_eval {M rem remIn : ℕ} (hremIn : remIn ≤ M) (hle : remIn ≤ rem)
    (c : CliffProg M) (hc : c.SupportsBelow (M - remIn)) (body : TempPhaseProg M)
    (hvBody : ValidCleanRem M remIn body) : ValidCleanRem M rem (withCliffAlloc c body) ∧
      (∀ β : BitAssignment M, cleanRem M rem β → cleanRem M remIn (c.eval β) ∧
        (withCliffAlloc c body).evalSign β = body.evalSign (c.eval β) ∧
        (withCliffAlloc c body).evalBits β = c.inv.eval (body.evalBits (c.eval β))) := by
  have hc_cl : ∀ β : BitAssignment M, cleanRem M rem β → cleanRem M remIn (c.eval β) :=
    fun β hβ w hw ↦ (c.eval_outside hc β w hw).trans (hβ w (by omega))
  exact ⟨⟨remIn, hremIn, trivial, ⟨0, Nat.zero_le M, hvBody, trivial,
    fun _ _ _ hw ↦ absurd hw (by omega)⟩, hc_cl⟩, fun β hβ ↦
    ⟨hc_cl β hβ, by simp [withCliffAlloc, TempPhaseProg.evalSign, TempPhaseProg.evalBits], rfl⟩⟩
theorem zmod2_add_self_cancel (a b : ZMod 2) : a + b + b = a := by
  revert a b
  decide
theorem cliffDisjoint_eval_congr_outside {M : ℕ} {mutW : Wire M → Prop} :
    ∀ {c : CliffProg M}, CliffDisjoint mutW c → ∀ {γ₁ γ₂ : BitAssignment M},
      (∀ u, ¬ mutW u → γ₁ u = γ₂ u) → ∀ w, ¬ mutW w → c.eval γ₁ w = c.eval γ₂ w
  | .nil, _, _, _, hEq, w, hw => hEq w hw
  | .x q, hq, _, _, hEq, w, hw => by
      dsimp [CliffProg.eval]
      by_cases hwq : w = q
      · simp [hwq, hEq q hq]
      · simp [Function.update_of_ne hwq, hEq w hw]
  | .cnot c₁ t₁ _, ⟨hc₁, ht₁⟩, _, _, hEq, w, hw => by
      dsimp [CliffProg.eval]
      by_cases hwt : w = t₁
      · simp [hwt, hEq t₁ ht₁, hEq c₁ hc₁]
      · simp [Function.update_of_ne hwt, hEq w hw]
  | .seq _ _, ⟨hd₁, hd₂⟩, _, _, hEq, w, hw =>
      cliffDisjoint_eval_congr_outside hd₂ (cliffDisjoint_eval_congr_outside hd₁ hEq) w hw
theorem plug_evalBits_split_clean {M : ℕ} {mutW : Wire M → Prop} {curHole : ℕ} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx curHole)
    {body : TempPhaseProg M} (hBodyNonMut : ∀ γ, cleanRem M (M - curHole) γ → ∀ w, ¬ mutW w →
    body.evalBits γ w = γ w) (q₀ : Wire M) : ∀ (β : BitAssignment M), cleanRem M (M - curHole)
    β → (∀ w, mutW w → (K.plug body).evalBits β w = body.evalBits (K.fwdBits β) w) ∧ (∀ w, ¬
    mutW w → (K.plug body).evalBits β w = (K.plug (.z q₀)).evalBits β w) := by
  induction K with
  | hole => exact fun β hβ ↦ ⟨fun _ _ ↦ rfl, hBodyNonMut β hβ⟩
  | seqPre c K₁ ih =>
      exact fun β hβ ↦ ih hDisj.2 hSupp.2 (c.eval β) fun w hw ↦
        (c.eval_outside hSupp.1 β w (by omega)).trans (hβ w hw)
  | seqPost K₁ c ih =>
      intro β hβ
      obtain ⟨hM, hN⟩ := ih hDisj.1 hSupp.1 β hβ
      exact ⟨fun w hw ↦ (hDisj.2.eval_mut _ hw).trans (hM w hw),
        cliffDisjoint_eval_congr_outside hDisj.2 hN⟩
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      intro β hβ
      let β₁ := Function.update β anc (β anc + β c₁ * β c₂)
      obtain ⟨hM, hN⟩ := ih hDisj.2.2.2 hSupp.2 β₁ fun w hw ↦
        (Function.update_of_ne (wire_ne_of_gt (s3LtLe hSupp.1 (by omega))) _ _).trans (hβ w hw)
      refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
      · have hw_ne : w ≠ anc := fun heq ↦ hDisj.2.2.1 (heq ▸ hw)
        change Function.update ((K₁.plug body).evalBits β₁) anc _ w = body.evalBits (K₁.fwdBits β₁)
          w
        exact (Function.update_of_ne hw_ne _ _).trans (hM w hw)
      · change Function.update ((K₁.plug body).evalBits β₁) anc ((K₁.plug body).evalBits β₁ anc +
            (K₁.plug body).evalBits β₁ c₁ * (K₁.plug body).evalBits β₁ c₂) w =
          Function.update ((K₁.plug (.z q₀)).evalBits β₁) anc ((K₁.plug (.z q₀)).evalBits β₁ anc +
            (K₁.plug (.z q₀)).evalBits β₁ c₁ * (K₁.plug (.z q₀)).evalBits β₁ c₂) w
        rw [hN c₁ hDisj.1, hN c₂ hDisj.2.1, hN anc hDisj.2.2.1]
        by_cases hwa : w = anc
        · simp [hwa]
        · simp [hwa, hN w hw]
theorem plug_validCleanRem_clean {M : ℕ} {mutW : Wire M → Prop} {curHole : ℕ} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx curHole)
    {body : TempPhaseProg M} (hBodyValid : ValidCleanRem M (M - curHole) body) (hBodyNonMut :
    ∀ γ, cleanRem M (M - curHole) γ → ∀ w, ¬ mutW w → body.evalBits γ w = γ w) (q₀ : Wire M) :
    ∀ {rem : ℕ}, M - curHole ≤ rem → ValidCleanRem M rem (K.plug (.z q₀)) → ValidCleanRem M
    rem (K.plug body) := by
  induction K with
  | hole => exact fun hle _ ↦ validCleanRem_mono hle hBodyValid
  | seqPre c K₁ ih =>
      intro rem hle ⟨remMid, hmid, _, hv₁, hpres₁⟩
      refine ⟨max remMid (M - curHole), by omega, trivial,
        ih hDisj.2 hSupp.2 (Nat.le_max_right _ _) (validCleanRem_mono (Nat.le_max_left _ _) hv₁),
        fun β hβ w hw ↦ ?_⟩
      by_cases hw1 : M - remMid ≤ w.val
      · exact hpres₁ β hβ w hw1
      · exact (c.eval_outside hSupp.1 β w (by omega)).trans (hβ w (by omega))
  | seqPost K₁ c ih =>
      exact fun hle ⟨_, _, hv₁, _, _⟩ ↦ ⟨0, Nat.zero_le M, ih hDisj.1 hSupp.1 hle hv₁,
        trivial, fun _ _ _ hw ↦ absurd hw (by omega)⟩
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      intro rem _ ⟨hanc_lo, hv₁, hpres₁⟩
      have hrem' : M - curHole ≤ M - (anc.val + 1) := by
        have := hSupp.1
        omega
      refine ⟨hanc_lo, ih hDisj.2.2.2 hSupp.2 hrem' hv₁, fun β₁ hβ₁ ↦ ?_⟩
      obtain ⟨_, hN⟩ := plug_evalBits_split_clean hDisj.2.2.2 hSupp.2 hBodyNonMut q₀ β₁
        (cleanRem_anti hrem' hβ₁)
      rw [hN c₁ hDisj.1, hN c₂ hDisj.2.1, hN anc hDisj.2.2.1]
      exact hpres₁ β₁ hβ₁
theorem ScopedBlock.graft_mutating_clean {M rem curHole : ℕ} [NeZero M] (mutW : Wire M → Prop)
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
  have hFwd : ∀ β : BitAssignment M, cleanRem M rem β → K.fwdBits β = setup β := by
    intro β hβ
    funext q
    have h₁ := K.plug_evalSign (.z q) β
    have h₂ := (hProbe q).sign β hβ
    dsimp [TempPhaseProg.evalSign] at h₁ h₂
    exact h₁.symm.trans h₂
  refine ⟨plug_validCleanRem_clean hDisj hSupp hBodyValid hBodyNonMut q₀ hle (hProbe q₀).valid,
    K.plug_countTempAnd body,
    fun β hβ ↦ by rw [K.plug_evalSign, hFwd β hβ],
    fun β hβ w ↦ ?_⟩
  obtain ⟨hM, hN⟩ := plug_evalBits_split_clean hDisj hSupp hBodyNonMut q₀ β (cleanRem_anti hle hβ)
  by_cases hw : mutW w
  · simp only [hw, ↓reduceIte, hM w hw, hFwd β hβ]
  · simp only [hw, ↓reduceIte, hN w hw, (hProbe q₀).bits β hβ]
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
    (hK : TempCtxLiftEx cur₁ next₀ K) : TempCtxLiftEx cur₀ next₁ K :=
  Slot3MicroEngineAux.TempCtxLiftEx.mono hK hc hn hM
theorem TempCtxLiftEx.append {M cur mid next : ℕ} {F G : TempCtx M}
    (hF : TempCtxLiftEx cur mid F) (hG : TempCtxLiftEx mid next G) :
    TempCtxLiftEx cur next (F.append G) :=
  Slot3MicroEngineAux.TempCtxLiftEx.append hF hG
theorem TempCtxLiftEx.cliff {M cur : ℕ} (hcur : cur ≤ M) (c : CliffProg M)
    (hc : c.SupportsBelow cur) : TempCtxLiftEx cur cur (ctxCliffAlloc c) :=
  Slot3MicroEngineAux.TempCtxLiftEx.cliff cur hcur c hc
theorem TempCtxLiftEx.tempBit {M cur : ℕ} (hcur : cur + 1 ≤ M) (c₁ c₂ : Wire M)
    (h12 : c₁ ≠ c₂) (hc1 : c₁.val < cur) (hc2 : c₂.val < cur) : TempCtxLiftEx cur (cur + 1)
    (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h12 (wire_ne_of_lt hc1) (wire_ne_of_lt hc2)) :=
  Slot3MicroEngineAux.TempCtxLiftEx.tempBit cur hcur c₁ c₂ h12 hc1 hc2
theorem p57Slim_bitsVal_split (W₁ : ℕ) :
    ∀ (W₂ : ℕ) (f : Fin (W₁ + W₂) → ZMod 2), bitsVal f =
      bitsVal (fun i : Fin W₁ ↦ f ⟨i.val, by omega⟩) +
        2 ^ W₁ * bitsVal (fun j : Fin W₂ ↦ f ⟨W₁ + j.val, by omega⟩)
  | 0, f => by
      have hz : bitsVal (fun j : Fin 0 ↦ f ⟨W₁ + j.val, by omega⟩) = 0 := by simp [bitsVal]
      have hf : bitsVal f = bitsVal (fun i : Fin W₁ ↦ f ⟨i.val, by omega⟩) := rfl
      rw [hz, hf]
      omega
  | W₂ + 1, f => by
      let f' : Fin ((W₁ + W₂) + 1) → ZMod 2 := f
      change bitsVal f' = _
      rw [bitsVal_castSucc_split f',
        p57Slim_bitsVal_split W₁ W₂ (fun k : Fin (W₁ + W₂) ↦ f' k.castSucc),
        bitsVal_castSucc_split (fun j : Fin (W₂ + 1) ↦ f ⟨W₁ + j.val, by omega⟩)]
      have hlo : (fun i : Fin W₁ ↦ f' (Fin.castSucc ⟨i.val, by omega⟩)) =
          (fun i : Fin W₁ ↦ f ⟨i.val, by omega⟩) := rfl
      have hmid : (fun j : Fin W₂ ↦ f' (Fin.castSucc ⟨W₁ + j.val, by omega⟩)) =
          (fun j : Fin W₂ ↦ f ⟨W₁ + j.val, by omega⟩) := rfl
      have hlast : f' (Fin.last (W₁ + W₂)) = f ⟨W₁ + (Fin.last W₂).val, by omega⟩ := rfl
      have hrhs : (fun j : Fin W₂ ↦
          (fun k : Fin (W₂ + 1) ↦ f ⟨W₁ + k.val, by omega⟩) j.castSucc) =
          (fun j : Fin W₂ ↦ f ⟨W₁ + j.val, by omega⟩) := funext fun _ ↦ congrArg f (Fin.ext rfl)
      rw [hlo, hmid, hlast, hrhs, pow_add]
      ring
theorem bitsVal_slice_linear {N W k : ℕ} (hk : k + W ≤ N) (g g' : Fin N → ZMod 2)
    (hout : ∀ m : Fin N, (m.val < k ∨ k + W ≤ m.val) → g' m = g m) :
    bitsVal g' + 2 ^ k * bitsVal (fun j : Fin W ↦ g ⟨k + j.val, by omega⟩) =
      bitsVal g + 2 ^ k * bitsVal (fun j : Fin W ↦ g' ⟨k + j.val, by omega⟩) ∧
    2 ^ k * bitsVal (fun j : Fin W ↦ g ⟨k + j.val, by omega⟩) ≤ bitsVal g := by
  have split3 : ∀ f : Fin N → ZMod 2, bitsVal f =
      bitsVal (fun i : Fin k ↦ f ⟨i.val, by omega⟩) +
        2 ^ k * (bitsVal (fun j : Fin W ↦ f ⟨k + j.val, by omega⟩) +
          2 ^ W * bitsVal (fun r : Fin (N - (k + W)) ↦ f ⟨k + W + r.val, by omega⟩)) := fun f ↦ by
    have h1 : bitsVal f = bitsVal (fun i : Fin (k + (N - k)) ↦ f ⟨i.val, by omega⟩) :=
      (Equiv.sum_comp (finCongr (by omega : k + (N - k) = N))
        (fun m : Fin N ↦ (f m).val * 2 ^ m.val)).symm
    rw [h1, p57Slim_bitsVal_split k (N - k)]
    congr 2
    have h2 : bitsVal (fun j : Fin (N - k) ↦ f ⟨k + j.val, by omega⟩) =
        bitsVal (fun j : Fin (W + (N - (k + W))) ↦ f ⟨k + j.val, by omega⟩) :=
      (Equiv.sum_comp (finCongr (by omega : W + (N - (k + W)) = N - k))
        (fun m : Fin (N - k) ↦ (f ⟨k + m.val, by omega⟩).val * 2 ^ m.val)).symm
    rw [h2, p57Slim_bitsVal_split W (N - (k + W))]
    congr 2
    exact congrArg bitsVal (funext fun r ↦ congrArg f (Fin.ext (by
      dsimp
      omega)))
  have hlo : (fun i : Fin k ↦ g' ⟨i.val, by omega⟩) = (fun i : Fin k ↦ g ⟨i.val, by omega⟩) :=
    funext fun i ↦ hout _ (Or.inl i.isLt)
  have hhi : (fun r : Fin (N - (k + W)) ↦ g' ⟨k + W + r.val, by omega⟩) =
      (fun r : Fin (N - (k + W)) ↦ g ⟨k + W + r.val, by omega⟩) :=
    funext fun r ↦ hout _ (Or.inr (by
      dsimp
      omega))
  have hg := split3 g
  have hg' := split3 g'
  rw [hlo, hhi, mul_add] at hg'
  rw [mul_add] at hg
  omega
end Slot3ArithCombinators
theorem wire_ne_val {M : ℕ} {a b : Wire M} (h : a.val ≠ b.val) : a ≠ b :=
  fun heq ↦ h (congrArg Fin.val heq)
theorem bitsVal_split_at (W₁ W₂ : ℕ) (f : Fin (W₁ + W₂) → ZMod 2) : bitsVal f =
    bitsVal (fun i : Fin W₁ ↦ f ⟨i.val, by omega⟩) +
      2 ^ W₁ * bitsVal (fun j : Fin W₂ ↦ f ⟨W₁ + j.val, by omega⟩) :=
  p57Slim_bitsVal_split W₁ W₂ f
theorem bitsVal_slice_eq_div_mod {N W k : ℕ} (hk : k + W ≤ N) (f : Fin N → ZMod 2) :
    bitsVal (fun j : Fin W ↦ f ⟨k + j.val, by omega⟩) = (bitsVal f / 2 ^ k) % 2 ^ W := by
  have h1 : bitsVal f = bitsVal (fun i : Fin (k + (N - k)) ↦ f ⟨i.val, by omega⟩) :=
    (Equiv.sum_comp (finCongr (by omega : k + (N - k) = N))
      (fun m : Fin N ↦ (f m).val * 2 ^ m.val)).symm
  rw [h1, bitsVal_split_at k (N - k), mul_comm (2 ^ k),
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt (bitsVal_lt_two_pow _),
    zero_add]
  have h2 : bitsVal (fun j : Fin (N - k) ↦ f ⟨k + j.val, by omega⟩) =
      bitsVal (fun j : Fin (W + (N - k - W)) ↦ f ⟨k + j.val, by omega⟩) :=
    (Equiv.sum_comp (finCongr (by omega : W + (N - k - W) = N - k))
      (fun m : Fin (N - k) ↦ (f ⟨k + m.val, by omega⟩).val * 2 ^ m.val)).symm
  rw [h2, bitsVal_split_at W (N - k - W), mul_comm (2 ^ W), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (bitsVal_lt_two_pow _)]
theorem fanoutCnot_disjoint {M : ℕ} {mutW : Wire M → Prop} : ∀ (n : ℕ) (c : Wire M)
    (dst : Fin n → Wire M) (hne : ∀ j, c ≠ dst j), ¬ mutW c → (∀ j, ¬ mutW (dst j)) →
    CliffDisjoint mutW (fanoutCnot n c dst hne)
  | 0, _, _, _, _, _ => trivial
  | n + 1, c, dst, hne, hc, hd => ⟨⟨hc, hd 0⟩,
      fanoutCnot_disjoint n c (fun j ↦ dst j.succ) (fun j ↦ hne j.succ) hc (fun j ↦ hd j.succ)⟩
theorem cnotVec_supportsBelow {M bound : ℕ} : ∀ (W : ℕ) (src dst : Fin W → Wire M)
    (hne : ∀ j, src j ≠ dst j), (∀ j, (src j).val < bound) → (∀ j, (dst j).val < bound) →
    (cnotVec W src dst hne).SupportsBelow bound
  | 0, _, _, _, _, _ => trivial
  | W + 1, src, dst, hne, hs, hd => ⟨⟨hs 0, hd 0⟩, cnotVec_supportsBelow W
      (fun j ↦ src j.succ) (fun j ↦ dst j.succ) (fun j ↦ hne j.succ)
      (fun j ↦ hs j.succ) (fun j ↦ hd j.succ)⟩
def boothConst57 : ℕ := 2 ^ 18 * (2 ^ 37 - 1)
def p57ProjW (w : Fin 3) (b : Fin 8) : Wire 437 := ⟨8 * w.val + b.val, by omega⟩
def p57S3W (w : Fin 3) : Wire 437 := ⟨49 + w.val, by omega⟩
def p57U38W (k : Fin 38) : Wire 437 :=
  if hk : k.val < 30 then ⟨60 + k.val, by omega⟩ else ⟨52 + (k.val - 30), by omega⟩
def p57MW (w : Fin 3) (b : Fin 7) : Wire 437 := ⟨177 + 7 * w.val + b.val, by omega⟩
def p57OutW (m : Fin 57) : Wire 437 := ⟨201 + m.val, by omega⟩
def sTrue18WDefault (j : Fin 18) : Wire 437 :=
  if hj : j.val < 16 then ⟨259 + j.val, by omega⟩ else ⟨199 + (j.val - 16), by omega⟩
theorem p57ProjW_injective (w : Fin 3) : Function.Injective (p57ProjW w) :=
  fun _ _ h ↦ Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
theorem p57OutW_injective : Function.Injective p57OutW :=
  fun _ _ h ↦ Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
theorem sTrue18WDefault_injective : Function.Injective sTrue18WDefault := by decide
def axisCmpDMag (p m s : ℕ) : ℕ :=
  let pFlip := if p < 128 then p + 128 else p - 128
  let b8 := if s = 1 then 255 - m else m
  let wWrap := if 255 - pFlip < b8 then 1 - s else s
  if wWrap = 1 then 255 - m else m
def sTrueRawVal (β : BitAssignment 437) : ℕ :=
  ∑ w : Fin 3,
    let d := axisCmpDMag (bitsVal (fun b ↦ β (p57ProjW w b)))
        (bitsVal (fun b ↦ β (p57MW w b))) (β (p57S3W w)).val
    d * d
theorem axisCmpDMag_eq_s3ProjStepHw (p : Fin 256) (hp : p.val ≠ 128) {m s : ℕ} (hm : m < 128)
    (hs : s ≤ 1) : axisCmpDMag p.val m s = (s3ProjStepHw p m s).2.1 := by
  unfold axisCmpDMag s3ProjStepHw
  dsimp only
  have hp_lt : p.val < 256 := p.isLt
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;>
    by_cases hp128 : p.val < 128 <;>
    simp only [hp128, ↓reduceIte] <;>
    repeat' (split_ifs at * <;> try omega)
theorem sTrueRawVal_eq_of_ne_128 (β : BitAssignment 437) (pVal : Fin 3 → Fin 256)
    (hpEq : ∀ w : Fin 3, bitsVal (fun b ↦ β (p57ProjW w b)) = (pVal w).val)
    (hpNe : ∀ w : Fin 3, (pVal w).val ≠ 128) :
    sTrueRawVal β = ∑ w : Fin 3,
      let st := s3ProjStepHw (pVal w) (bitsVal (fun b ↦ β (p57MW w b))) (β (p57S3W w)).val
      st.2.1 * st.2.1 := by
  unfold sTrueRawVal
  exact Finset.sum_congr rfl fun w _ ↦ by
    dsimp only
    rw [hpEq w, axisCmpDMag_eq_s3ProjStepHw (pVal w) (hpNe w)
      (bitsVal_lt_two_pow _) (zmod2_val_le_one _)]
theorem bitsVal_invLow7 (f : Fin 8 → ZMod 2) :
    let p := bitsVal f
    let pFlip := if p < 128 then p + 128 else p - 128
    bitsVal (fun b : Fin 8 ↦ if b.val < 7 then f b + 1 else f b) = 255 - pFlip := by
  dsimp only
  have h1 := bitsVal_castSucc_split f
  rw [bitsVal_castSucc_split,
    show (fun j : Fin 7 ↦ if (j.castSucc).val < 7 then f j.castSucc + 1 else f j.castSucc) =
      fun j : Fin 7 ↦ f j.castSucc + 1 from funext fun j ↦ ite_eq_left j.isLt,
    ite_eq_right (by decide : ¬ (Fin.last 7).val < 7)]
  have hfl := bitsVal_flip_all 7 (fun j : Fin 7 ↦ f j.castSucc)
  have hlt7 : bitsVal (fun j : Fin 7 ↦ f j.castSucc) < 128 := bitsVal_lt_two_pow _
  rcases zmod2_val_cases (f (Fin.last 7)) with hf7 | hf7
  · rw [h1, hf7, ite_eq_left (by omega)]
    omega
  · rw [h1, hf7, ite_eq_right (by omega)]
    omega
theorem bitsVal_xorSnoc7 (g : Fin 7 → ZMod 2) (z : ZMod 2) :
    bitsVal (Fin.snoc (α := fun _ ↦ ZMod 2) (fun b : Fin 7 ↦ g b + z) z) =
      if z.val = 1 then 255 - bitsVal g else bitsVal g := by
  rw [bitsVal_castSucc_split,
    show (fun j : Fin 7 ↦ (Fin.snoc (α := fun _ ↦ ZMod 2) (fun b : Fin 7 ↦ g b + z) z) j.castSucc) =
      fun j : Fin 7 ↦ g j + z from funext fun j ↦ Fin.snoc_castSucc _ _ _,
    Fin.snoc_last]
  have hfl := bitsVal_flip_all 7 g
  have hlt7 : bitsVal g < 128 := bitsVal_lt_two_pow _
  rcases bit_cases z with rfl | rfl
  · simp
  · simp only [ZMod.val_one, ↓reduceIte, mul_one]
    omega
def ValidSTrueMap (cur : ℕ) (sTrue18W : Fin 18 → Wire 437) : Prop := Function.Injective
    sTrue18W ∧ (∀ j, (sTrue18W j).val < cur) ∧ (∀ j w b, sTrue18W j ≠ p57ProjW w b) ∧
    (∀ j w, sTrue18W j ≠ p57S3W w) ∧ (∀ j w b, sTrue18W j ≠ p57MW w b) ∧
    (∀ j k, sTrue18W j ≠ p57U38W k) ∧ (∀ j m, sTrue18W j ≠ p57OutW m) ∧
    (∀ j, (sTrue18W j).val ≠ 258)
theorem validSTrueMap_default : ValidSTrueMap 275 sTrue18WDefault :=
  ⟨sTrue18WDefault_injective, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
def p57PBufW (w : Fin 3) (b : Fin 8) : Wire 437 := ⟨150 + 8 * w.val + b.val, by omega⟩
def p57AxisFastVal (p m s : ℕ) : ℕ :=
  let pFlip := if p < 128 then p + 128 else p - 128
  let b8 := if s = 1 then 255 - m else m
  (p + b8 + if 255 - pFlip < b8 then 1 else 0) % 256
def wWrapFromPBufZMod (p7 pb7 sw : ZMod 2) : ZMod 2 := (1 + sw + p7) * (sw + pb7)
def axisCmpDMagPBuf (p7 pb7 sw : ZMod 2) (m : ℕ) : ℕ :=
  if (wWrapFromPBufZMod p7 pb7 sw).val = 1 then 255 - m else m
def sTrueRawValPBuf (β : BitAssignment 437) : ℕ :=
  ∑ w : Fin 3,
    let d := axisCmpDMagPBuf (β (p57ProjW w ⟨7, by decide⟩)) (β (p57PBufW w ⟨7, by decide⟩))
      (β (p57S3W w)) (bitsVal (fun b ↦ β (p57MW w b)))
    d * d
theorem nat_testBit_seven_of_lt_256 {x : ℕ} (hx : x < 256) :
    x.testBit 7 = decide (128 ≤ x) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change decide ((x / 128) % 2 = 1) = decide (128 ≤ x)
  exact decide_eq_decide.mpr ⟨fun _ ↦ by omega, fun _ ↦ by omega⟩
theorem bitsVal_last_seven_eq_ite (f : Fin 8 → ZMod 2) :
    f ⟨7, by decide⟩ = if 128 ≤ bitsVal f then 1 else 0 := by
  have hsp := bitsVal_castSucc_split f
  have hlo : bitsVal (fun j : Fin 7 ↦ f j.castSucc) < 128 := bitsVal_lt_two_pow _
  change _ = _ + 128 * (f ⟨7, by decide⟩).val at hsp
  rcases bit_cases (f ⟨7, by decide⟩) with h0 | h1
  · rw [h0, ite_eq_right (by
      rw [h0, ZMod.val_zero] at hsp
      omega)]
  · rw [h1, ite_eq_left (by
      rw [h1, ZMod.val_one] at hsp
      omega)]
theorem axisCmpDMagPBuf_eq_axisCmpDMag
    (fP : Fin 8 → ZMod 2) (pb7 : ZMod 2) (sw : ZMod 2) (m : ℕ) (hm : m < 128)
    (hpb7 : pb7 = if (p57AxisFastVal (bitsVal fP) m sw.val).testBit 7 then 1 else 0) :
    axisCmpDMagPBuf (fP ⟨7, by decide⟩) pb7 sw m = axisCmpDMag (bitsVal fP) m sw.val := by
  have hp_lt : bitsVal fP < 256 := bitsVal_lt_two_pow fP
  have hfast_lt : p57AxisFastVal (bitsVal fP) m sw.val < 256 := Nat.mod_lt _ (by decide)
  simp only [nat_testBit_seven_of_lt_256 hfast_lt, decide_eq_true_eq] at hpb7
  unfold axisCmpDMagPBuf axisCmpDMag
  dsimp only
  congr 1
  rw [bitsVal_last_seven_eq_ite fP, hpb7]
  generalize bitsVal fP = p at hp_lt ⊢
  dsimp only [p57AxisFastVal]
  rcases bit_cases sw with rfl | rfl
  · simp only [ZMod.val_zero, show ¬ ((0 : ℕ) = 1) by decide, ↓reduceIte]
    by_cases hp128 : p < 128
    · have hnp : ¬ 128 ≤ p := by omega
      by_cases hlt : 255 - (p + 128) < m
      · have hge : 128 ≤ (p + m + 1) % 256 := by omega
        simp only [hp128, hnp, hlt, ↓reduceIte, hge]
        decide
      · have hng : ¬ 128 ≤ (p + m + 0) % 256 := by omega
        simp only [hp128, hnp, hlt, ↓reduceIte, hng]
        decide
    · have hgep : 128 ≤ p := by omega
      have hnlt : ¬ 255 - (p - 128) < m := by omega
      by_cases hge : 128 ≤ (p + m + 0) % 256
      · simp only [hp128, hgep, hnlt, ↓reduceIte, hge]
        decide
      · simp only [hp128, hgep, hnlt, ↓reduceIte, hge]
        decide
  · simp only [ZMod.val_one, ↓reduceIte]
    by_cases hp128 : p < 128
    · have hnp : ¬ 128 ≤ p := by omega
      have hlt : 255 - (p + 128) < 255 - m := by omega
      by_cases hge : 128 ≤ (p + (255 - m) + 1) % 256
      · simp only [hp128, hnp, hlt, ↓reduceIte, hge]
        decide
      · simp only [hp128, hnp, hlt, ↓reduceIte, hge]
        decide
    · have hgep : 128 ≤ p := by omega
      by_cases hlt : 255 - (p - 128) < 255 - m
      · have hge : 128 ≤ (p + (255 - m) + 1) % 256 := by omega
        simp only [hp128, hgep, hlt, ↓reduceIte, hge]
        decide
      · have hng : ¬ 128 ≤ (p + (255 - m) + 0) % 256 := by omega
        simp only [hp128, hgep, hlt, ↓reduceIte, hng]
        decide
theorem sTrueRawValPBuf_eq_sTrueRawVal (β : BitAssignment 437)
    (hPBuf7 : ∀ w : Fin 3, β (p57PBufW w ⟨7, by decide⟩) =
      if (p57AxisFastVal (bitsVal (fun b ↦ β (p57ProjW w b)))
          (bitsVal (fun b ↦ β (p57MW w b))) (β (p57S3W w)).val).testBit 7 then 1 else 0) :
    sTrueRawValPBuf β = sTrueRawVal β :=
  Finset.sum_congr rfl fun w _ ↦ by
    dsimp only
    rw [axisCmpDMagPBuf_eq_axisCmpDMag (fun b ↦ β (p57ProjW w b)) (β (p57PBufW w ⟨7, by decide⟩))
      (β (p57S3W w)) (bitsVal (fun b ↦ β (p57MW w b))) (bitsVal_lt_two_pow _) (hPBuf7 w)]
section P57DynBridge
open HermitianMat MeasureBranchHadamardSem
open BchCubeDecoder StreamingBchComparator
open Classical in
noncomputable def p57DiagProj {M n : ℕ} (rComb : QRegister M n) (Inv : BitAssignment M → Prop)
    : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := Matrix.diagonal fun g ↦ if Inv
    (fun idx ↦ basisBits n g (rComb idx)) then 1 else 0
noncomputable def p57CleanDiagProj {M n : ℕ} (rComb : QRegister M n) (rem : ℕ)
    (hrem : rem ≤ M) (Inv : BitAssignment M → Prop) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
    projZeroAll rem (tailScr rComb rem hrem) * p57DiagProj rComb Inv
open Classical in
theorem ket_p57DiagProj {M n : ℕ} (rComb : QRegister M n) (Inv : BitAssignment M → Prop)
    (β : BitAssignment n) : (p57DiagProj rComb Inv).mulVec (ket β) = if Inv
    (fun idx ↦ β (rComb idx)) then ket β else 0 := by
  funext i
  rw [ket, basisState]
  simp only [p57DiagProj, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply,
    mul_boole, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases h : Inv (fun idx ↦ β (rComb idx)) <;>
    by_cases hi : i = (basisBitsEquiv n).symm β <;>
    simp [h, hi]
theorem p57DiagProj_conjTranspose {M n : ℕ} (rComb : QRegister M n)
    (Inv : BitAssignment M → Prop) : (p57DiagProj rComb Inv)ᴴ = p57DiagProj rComb Inv := by
  ext i j
  simp only [p57DiagProj, Matrix.conjTranspose_apply, Matrix.diagonal_apply, eq_comm]
  by_cases hij : i = j
  · subst hij
    by_cases hc : Inv (fun idx ↦ basisBits n i (rComb idx)) <;> simp [hc]
  · simp [hij]
open Classical in
theorem p57ProjZeroAll_comm_diag {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    (Inv : BitAssignment M → Prop) (k : ℕ) (scr : Fin k → Wire n) : projZeroAll k scr *
    p57DiagProj rComb Inv = p57DiagProj rComb Inv * projZeroAll k scr := by
  apply matrix_ext_ket; intro β
  simp only [mul_mulVec_prog, ket_p57DiagProj, ket_projZeroAll]
  by_cases h1 : Inv (fun idx ↦ β (rComb idx)) <;>
    by_cases h2 : ∀ j : Fin k, β (scr j) = 0 <;>
    simp [h1, h2, ket_p57DiagProj, ket_projZeroAll]
open Classical in
theorem p57BasisProj_comm_diag {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    (Inv : BitAssignment M → Prop) (w : Wire n) :
    (QRegister.singleton w).basisOutcomeProjector 0 * p57DiagProj rComb Inv = p57DiagProj
    rComb Inv * (QRegister.singleton w).basisOutcomeProjector 0 := by
  apply matrix_ext_ket; intro β
  simp only [mul_mulVec_prog, ket_p57DiagProj, ket_projector_zero]
  by_cases h1 : Inv (fun idx ↦ β (rComb idx)) <;>
    by_cases h2 : β w = 0 <;>
    simp [h1, h2, ket_p57DiagProj, ket_projector_zero]
theorem p57CleanDiagProj_conjTranspose {M n : ℕ} [NeZero (2 ^ n)]
    (rComb : QRegister M n) (rem : ℕ) (hrem : rem ≤ M) (Inv : BitAssignment M → Prop) :
    (p57CleanDiagProj rComb rem hrem Inv)ᴴ = p57CleanDiagProj rComb rem hrem Inv := by
  dsimp [p57CleanDiagProj]
  rw [conjTranspose_mul, projZeroAll_conjTranspose, p57DiagProj_conjTranspose,
    p57ProjZeroAll_comm_diag]
theorem tailScr_zero_iff_cleanRem {M n : ℕ} (rComb : QRegister M n) (rem : ℕ) (hrem : rem ≤ M)
    (β : BitAssignment n) : (∀ j : Fin rem, β (tailScr rComb rem hrem j) = 0) ↔ cleanRem M rem
    (fun idx ↦ β (rComb idx)) :=
  ⟨fun h w hw ↦ (show w = ⟨(M - rem) + (w.val - (M - rem)), by omega⟩ from
      Fin.ext (Nat.add_sub_of_le hw).symm) ▸ h ⟨w.val - (M - rem), by omega⟩,
   fun h j ↦ h ⟨(M - rem) + j.val, by omega⟩ (by
     dsimp
     omega)⟩
open Classical in
theorem ket_p57CleanDiagProj {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n) (rem : ℕ)
    (hrem : rem ≤ M) (Inv : BitAssignment M → Prop) (β : BitAssignment n) :
    (p57CleanDiagProj rComb rem hrem Inv).mulVec (ket β) = if cleanRem M rem
    (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx)) then ket β else 0 := by
  dsimp only [p57CleanDiagProj]
  rw [mul_mulVec_prog, ket_p57DiagProj]
  by_cases hInv : Inv (fun idx ↦ β (rComb idx))
  · simp [hInv, ket_projZeroAll, tailScr_zero_iff_cleanRem]
  · simp [hInv]
open Classical in
theorem p57CleanDiagProj_mono {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    {rem₁ rem₂ : ℕ} (h₁ : rem₁ ≤ M) (h₂ : rem₂ ≤ M) (hle : rem₁ ≤ rem₂)
    {Inv₁ Inv₂ : BitAssignment M → Prop}
    (hImp : ∀ γ : BitAssignment M, cleanRem M rem₂ γ → Inv₂ γ → Inv₁ γ) : p57CleanDiagProj
    rComb rem₁ h₁ Inv₁ * p57CleanDiagProj rComb rem₂ h₂ Inv₂ = p57CleanDiagProj rComb rem₂ h₂
    Inv₂ := matrix_ext_ket fun β ↦ by
  rw [mul_mulVec_prog, ket_p57CleanDiagProj]
  by_cases h : cleanRem M rem₂ (fun idx ↦ β (rComb idx)) ∧ Inv₂ (fun idx ↦ β (rComb idx))
  · simp [h, cleanRem_anti hle h.1, hImp _ h.1 h.2, ket_p57CleanDiagProj]
  · simp [h]
open Classical in
theorem p57SeqClean_prog_inv {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    (p₁ : TempPhaseProg M) {rem₁ rem₂ : ℕ} (h₁ : rem₁ ≤ M) (h₂ : rem₂ ≤ M)
    {Inv₁ Inv₂ : BitAssignment M → Prop} (hpres : ∀ γ : BitAssignment M, cleanRem M rem₁ γ →
    Inv₁ γ → cleanRem M rem₂ (p₁.evalBits γ) ∧ Inv₂ (p₁.evalBits γ)) : p57CleanDiagProj rComb
    rem₂ h₂ Inv₂ * (((p₁.onRegister rComb).toToffCircuit).eval.1 * p57CleanDiagProj rComb rem₁
    h₁ Inv₁) = ((p₁.onRegister rComb).toToffCircuit).eval.1 * p57CleanDiagProj rComb rem₁ h₁
    Inv₁ := matrix_ext_ket fun β ↦ by
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
  by_cases h : cleanRem M rem₁ (fun idx ↦ β (rComb idx)) ∧ Inv₁ (fun idx ↦ β (rComb idx))
  · simp [h, eval_onRegister_prog_ket, Matrix.mulVec_smul, ket_p57CleanDiagProj,
      hpres _ h.1 h.2]
  · simp [h]
theorem realizesClean_andUncompute {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hP : Pᴴ = P) (hClean :
    (QRegister.singleton anc).basisOutcomeProjector 0 * ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a
    h₂a).eval.1 * P) = (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * P) : RealizesCleanUnitary
    v P (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂)
    ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval) := by
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  have hadj : (P * T_anc.1ᴴ) * P₀ = P * T_anc.1ᴴ := by
    simpa [P₀, T_anc, conjTranspose_mul, hP, QRegister.basisOutcomeProjector_conjTranspose _ 0,
      ← Matrix.mul_assoc] using congrArg conjTranspose hClean
  have hprod : (P * T_anc.1ᴴ) * (P₀ * T_anc.1ᴴ) = P := by
    have hsq : T_anc.1ᴴ * T_anc.1ᴴ = 1 := by
      simpa [T_anc, Submonoid.coe_mul, conjTranspose_mul] using
        congrArg (fun u : Unitary (2 ^ n) ↦ u.1ᴴ) (toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a)
    rw [← Matrix.mul_assoc, hadj, Matrix.mul_assoc, hsq, Matrix.mul_one]
  refine ⟨fun Ψ _ σ val ↦ wp_andUncompute_update_self v c₁ c₂ anc h₁₂ Ψ σ val, fun Θ hΘ σ ↦ ?_⟩
  let Ψ := wp (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂).compile Θ
  have hconj := congrArg (fun H : HermitianMat (Fin (2 ^ n)) ℂ ↦ H.conj (P * T_anc.1ᴴ))
    (show (Ψ σ).1.conj (P₀ * T_anc.1ᴴ) = (Θ σ).1.conj P₀ by
      simpa [Ψ, T_anc, P₀, CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj] using
        congrArg Subtype.val (congrFun
          (restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
            v c₁ c₂ anc h₁₂ h₁a h₂a Θ hΘ) σ))
  rw [conj_conj, conj_conj, hprod, hadj] at hconj
  change (Ψ σ).1.conj P = ((wpQAssignCompat T_anc Θ σ).1).conj P
  simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, conj_conj]
  exact hconj
open Classical in
theorem realizesClean_andUncompute_diag {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (rem : ℕ) (hrem : rem ≤ M)
    (Inv : BitAssignment M → Prop) (hInvEq : ∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ →
    γ anc = γ c₁ * γ c₂) : RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem Inv)
    (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc) (rComb.wires.injective.ne
    h₁₂)) ((Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc) (rComb.wires.injective.ne h₁₂)
    (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)).eval) := by
  refine realizesClean_andUncompute v _ _ _ _ _ _ _
    (p57CleanDiagProj_conjTranspose rComb rem hrem Inv) (matrix_ext_ket fun β ↦ ?_)
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
  by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
  · simp only [h, and_self, ↓reduceIte, ket_TOFF, ket_projector_zero, Function.update_self]
    have hanc : β (rComb anc) + β (rComb c₁) * β (rComb c₂) = 0 := by
      rw [hInvEq _ h.1 h.2, CharTwo.add_self_eq_zero]
    simp [hanc]
  · simp [h]
def p57ToDynWith {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (dInner : DynamicCircuit Var n) : TempCtx M → DynamicCircuit Var n
  | .hole => dInner
  | .seqPre c K => .seq (.circuit ((c.onRegister rComb).toCircuit)) (p57ToDynWith v rComb dInner K)
  | .seqPost K c => .seq (p57ToDynWith v rComb dInner K) (.circuit ((c.onRegister rComb).toCircuit))
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K =>
      .seq (DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a))
        (.seq (p57ToDynWith v rComb dInner K) (DynamicCircuit.andUncompute v (rComb c₁)
          (rComb c₂) (rComb anc) (rComb.wires.injective.ne h₁₂)))
theorem p57ToDynWith_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (dInner : DynamicCircuit Var n) (h0 : dInner.count PrimitiveGate.TOFF = 0) :
    ∀ K : TempCtx M, (p57ToDynWith v rComb dInner K).count PrimitiveGate.TOFF = 0
  | .hole => h0
  | .seqPre _ K => by simp [p57ToDynWith, p57ToDynWith_count_toff v rComb dInner h0 K]
  | .seqPost K _ => by simp [p57ToDynWith, p57ToDynWith_count_toff v rComb dInner h0 K]
  | .tempAnd _ _ _ _ _ _ K => by
      simp [p57ToDynWith, DynamicCircuit.count_andCompute_toff,
        DynamicCircuit.count_andUncompute_toff, p57ToDynWith_count_toff v rComb dInner h0 K]
theorem p57ToDynWith_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (dInner : DynamicCircuit Var n) : ∀ K : TempCtx M,
      (p57ToDynWith v rComb dInner K).count PrimitiveGate.T =
        4 * K.countTempAnd + dInner.count PrimitiveGate.T
  | .hole => by simp [p57ToDynWith, TempCtx.countTempAnd]
  | .seqPre _ K => by simp [p57ToDynWith, TempCtx.countTempAnd,
      p57ToDynWith_count_t v rComb dInner K]
  | .seqPost K _ => by simp [p57ToDynWith, TempCtx.countTempAnd,
      p57ToDynWith_count_t v rComb dInner K]
  | .tempAnd _ _ _ _ _ _ K => by
      simp [p57ToDynWith, TempCtx.countTempAnd, DynamicCircuit.count_andCompute_t,
        DynamicCircuit.count_andUncompute_t, p57ToDynWith_count_t v rComb dInner K]
      ring
theorem p57ToDynWith_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (dInner : DynamicCircuit Var n)
    (hInner : PreservesStoreConst dInner) :
    ∀ K : TempCtx M, PreservesStoreConst (p57ToDynWith v rComb dInner K)
  | .hole => hInner
  | .seqPre _ K => PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (p57ToDynWith_preservesStore v rComb dInner hInner K)
  | .seqPost K _ => PreservesStoreConst.seq (p57ToDynWith_preservesStore v rComb dInner hInner K)
      (PreservesStoreConst.circuit _)
  | .tempAnd _ _ _ _ _ _ K => PreservesStoreConst.seq (PreservesStoreConst.circuit _)
      (PreservesStoreConst.seq (p57ToDynWith_preservesStore v rComb dInner hInner K)
        (PreservesStoreConst.andUncompute v _ _ _ _))
open Classical in
theorem p57WithTempAnd_cleanDiagProj {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (rem : ℕ) (hrem : rem ≤ M) (hanc_lo : M - rem ≤ anc.val)
    (Inv : BitAssignment M → Prop) (body : TempPhaseProg M) (dBody : DynamicCircuit Var n)
    (hpresBody : ∀ β₁ : BitAssignment M, cleanRem M (M - (anc.val + 1)) β₁ → body.evalBits β₁
    c₁ = β₁ c₁ ∧ body.evalBits β₁ c₂ = β₁ c₂ ∧ body.evalBits β₁ anc = β₁ anc) (hBody :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (M - (anc.val + 1)) (by omega) (fun δ ↦
    (cleanRem M rem (Function.update δ anc 0) ∧ Inv (Function.update δ anc 0)) ∧ δ anc = δ c₁
    * δ c₂)) dBody (((body.onRegister rComb).toToffCircuit).eval)) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb rem hrem Inv) (.seq (DynamicCircuit.andCompute (rComb c₁) (rComb
    c₂) (rComb anc) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)) (.seq dBody
    (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc) (rComb.wires.injective.ne
    h₁₂)))) ((((TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister
    rComb).toToffCircuit).eval) := by
  have hanc_lt : anc.val < M := anc.isLt
  let rem' := M - (anc.val + 1)
  have hrem' : rem' ≤ M := by omega
  let InvRest : BitAssignment M → Prop :=
    fun δ ↦ cleanRem M rem (Function.update δ anc 0) ∧ Inv (Function.update δ anc 0)
  let InvBody : BitAssignment M → Prop := fun δ ↦ InvRest δ ∧ δ anc = δ c₁ * δ c₂
  let P₀ := (QRegister.singleton (rComb anc)).basisOutcomeProjector 0
  let P_rest := p57CleanDiagProj rComb rem' hrem' InvRest
  let P_body := p57CleanDiagProj rComb rem' hrem' InvBody
  let P_all := p57CleanDiagProj rComb rem hrem Inv
  let qc₁ := rComb c₁
  let qc₂ := rComb c₂
  let qanc := rComb anc
  have hq₁₂ : qc₁ ≠ qc₂ := rComb.wires.injective.ne h₁₂
  have hq₁a : qc₁ ≠ qanc := rComb.wires.injective.ne h₁a
  have hq₂a : qc₂ ≠ qanc := rComb.wires.injective.ne h₂a
  let T_anc := (Circuit.TOFF qc₁ qc₂ qanc hq₁₂ hq₁a hq₂a).eval
  let U_body := ((body.onRegister rComb).toToffCircuit).eval
  let U_clean :=
    (((TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).onRegister rComb).toToffCircuit).eval
  let V := T_anc * U_body * T_anc
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hPr_herm : P_restᴴ = P_rest := p57CleanDiagProj_conjTranspose rComb rem' hrem' InvRest
  have hPb_herm : P_bodyᴴ = P_body := p57CleanDiagProj_conjTranspose rComb rem' hrem' InvBody
  have hPall_herm : P_allᴴ = P_all := p57CleanDiagProj_conjTranspose rComb rem hrem Inv
  have hcomm_P : P₀ * P_rest = P_rest * P₀ := by
    dsimp [P₀, P_rest, p57CleanDiagProj]
    rw [← Matrix.mul_assoc, basisOutcomeProjector_comm_projZeroAll qanc 0 rem' _,
      Matrix.mul_assoc, p57BasisProj_comm_diag rComb InvRest qanc, ← Matrix.mul_assoc]
  have hPall_eq : P_all = P_rest * P₀ := matrix_ext_ket fun β ↦ by
    dsimp only [P_all, P_rest, P₀]
    rw [mul_mulVec_prog, ket_projector_zero, ket_p57CleanDiagProj]
    by_cases hanc0 : β qanc = 0
    · simp only [qanc] at hanc0
      simp only [hanc0, ↓reduceIte, ket_p57CleanDiagProj]
      let γ : BitAssignment M := fun idx ↦ β (rComb idx)
      have hupd : Function.update γ anc 0 = γ := Function.update_eq_self_iff.mpr hanc0.symm
      have hiff : (cleanRem M rem γ ∧ Inv γ) ↔ (cleanRem M rem' γ ∧ InvRest γ) := by
        dsimp only [InvRest]
        rw [hupd]
        exact ⟨fun ⟨hcr, hi⟩ ↦ ⟨cleanRem_anti (by omega) hcr, hcr, hi⟩,
          fun ⟨_, hcr, hi⟩ ↦ ⟨hcr, hi⟩⟩
      simp [γ, hiff]
    · simp only [qanc] at hanc0
      simp [hanc0, show ¬ (cleanRem M rem (fun idx ↦ β (rComb idx)) ∧
        Inv (fun idx ↦ β (rComb idx))) from fun ⟨hcr, _⟩ ↦ hanc0 (hcr anc hanc_lo)]
  have hcomm_T : T_anc.1 * P_rest = P_rest * T_anc.1 := matrix_ext_ket fun β ↦ by
    dsimp only [T_anc, P_rest]
    rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj, ket_TOFF, ket_p57CleanDiagProj]
    let γ : BitAssignment M := fun idx ↦ β (rComb idx)
    let β' := Function.update β qanc (β qanc + β qc₁ * β qc₂)
    let γ' : BitAssignment M := fun idx ↦ β' (rComb idx)
    have hγ'_eq : γ' = Function.update γ anc (γ anc + γ c₁ * γ c₂) := funext fun w ↦ by
      by_cases hw : w = anc
      · subst hw
        simp [γ', β', γ, qanc, qc₁, qc₂]
      · simp [γ', β', γ, qanc, Function.update_of_ne (rComb.wires.injective.ne hw),
          Function.update_of_ne hw]
    have hcr : cleanRem M rem' γ' ↔ cleanRem M rem' γ := by
      rw [hγ'_eq]
      refine ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩
      · have hne : w ≠ anc := wire_ne_of_gt (by
          dsimp [rem'] at hw
          omega)
        simpa [Function.update_of_ne hne] using h w hw
      · have hne : w ≠ anc := wire_ne_of_gt (by
          dsimp [rem'] at hw
          omega)
        simpa [Function.update_of_ne hne] using h w hw
    have hiff : (cleanRem M rem' γ' ∧ InvRest γ') ↔ (cleanRem M rem' γ ∧ InvRest γ) := by
      dsimp only [InvRest]
      rw [hcr, hγ'_eq, Function.update_idem]
    by_cases h : cleanRem M rem' γ ∧ InvRest γ
    · have h' := hiff.mpr h
      dsimp only [γ, γ', β'] at h h'
      simp only [h, h', and_self, ↓reduceIte, ket_TOFF]
    · have hn : ¬ (cleanRem M rem' γ' ∧ InvRest γ') := fun h' ↦ h (hiff.mp h')
      simp [γ, γ', β', h, hn]
  have hcomm_T_adj : P_rest * T_anc.1ᴴ = T_anc.1ᴴ * P_rest := by
    simpa [conjTranspose_mul, hPr_herm] using congrArg conjTranspose hcomm_T
  have habsorb : P_body * (T_anc.1 * P₀) = P_rest * (T_anc.1 * P₀) := matrix_ext_ket fun β ↦ by
    dsimp only [P_body, P_rest, P₀, T_anc]
    rw [mul_mulVec_prog, mul_mulVec_prog, mul_mulVec_prog, mul_mulVec_prog, ket_projector_zero]
    by_cases hanc0 : β (rComb anc) = 0
    · simp only [qanc, hanc0, ↓reduceIte, ket_TOFF, ket_p57CleanDiagProj, zero_add]
      let β' := Function.update β (rComb anc) (β qc₁ * β qc₂)
      have heq_bit : β' (rComb anc) = β' qc₁ * β' qc₂ := by
        simp [β', qc₁, qc₂, Function.update_self,
          Function.update_of_ne (rComb.wires.injective.ne h₁a),
          Function.update_of_ne (rComb.wires.injective.ne h₂a)]
      have hiff : (cleanRem M rem' (fun idx ↦ β' (rComb idx)) ∧
          InvBody (fun idx ↦ β' (rComb idx))) ↔ (cleanRem M rem' (fun idx ↦ β' (rComb idx)) ∧
          InvRest (fun idx ↦ β' (rComb idx))) :=
        ⟨fun ⟨h1, h2, _⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2, heq_bit⟩⟩
      by_cases hR : cleanRem M rem' (fun idx ↦ β' (rComb idx)) ∧ InvRest (fun idx ↦ β' (rComb idx))
      · rw [ite_eq_left (hiff.mpr hR), ite_eq_left hR]
      · rw [ite_eq_right (fun hl ↦ hR (hiff.mp hl)), ite_eq_right hR]
    · simp [hanc0]
  have habsorb_adj : (P₀ * T_anc.1ᴴ) * P_body = (P₀ * T_anc.1ᴴ) * P_rest := by
    simpa [conjTranspose_mul, hPb_herm, hPr_herm, hP₀_herm, ← Matrix.mul_assoc] using
      congrArg conjTranspose habsorb
  have hV_eq_clean : V.1 * P_all = U_clean.1 * P_all := matrix_ext_ket fun β ↦ by
    rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
    by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
    · simp only [h, and_self, ↓reduceIte]
      dsimp only [V, U_clean, U_body, T_anc, qc₁, qc₂, qanc,
        TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit]
      rw [Submonoid.coe_mul, Submonoid.coe_mul, mul_mulVec_prog, mul_mulVec_prog,
        eval_seq_mulVec, eval_seq_mulVec]
    · simp [h]
  have hU_clean_P₀ : P₀ * (U_clean.1 * P_all) = U_clean.1 * P_all := matrix_ext_ket fun β ↦ by
    rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
    by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
    · simp only [h, and_self, ↓reduceIte]
      let γ : BitAssignment M := fun idx ↦ β (rComb idx)
      have hanc0 : γ anc = 0 := h.1 anc hanc_lo
      let β₁ : BitAssignment M := Function.update γ anc (γ anc + γ c₁ * γ c₂)
      obtain ⟨hc1_pres, hc2_pres, hanc_pres⟩ := hpresBody β₁ fun w hw ↦ by
        dsimp only [β₁]
        rw [Function.update_of_ne (wire_ne_of_gt (by omega))]
        exact h.1 w (by omega)
      have hfinal_anc :
          (TempPhaseProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body).evalBits γ anc = 0 := by
        change Function.update (body.evalBits β₁) anc _ anc = 0
        rw [Function.update_self, hanc_pres, hc1_pres, hc2_pres]
        dsimp only [β₁]
        rw [Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
          hanc0, zero_add, CharTwo.add_self_eq_zero]
      dsimp only [U_clean, P₀]
      rw [eval_onRegister_prog_ket rComb _ β, Matrix.mulVec_smul,
        ket_projector_zero, writeRegProg_apply_reg, hfinal_anc]
      simp
    · simp [h]
  have hclean_adj : P_all * U_clean.1ᴴ * P₀ = P_all * U_clean.1ᴴ := by
    simpa [conjTranspose_mul, hP₀_herm, hPall_herm, ← Matrix.mul_assoc] using
      congrArg conjTranspose hU_clean_P₀
  have hU_eq : U_body * T_anc = T_anc * V := by
    dsimp [V]
    rw [← mul_assoc, ← mul_assoc, toffoli_eval_sq qc₁ qc₂ qanc hq₁₂ hq₁a hq₂a, one_mul]
  refine ⟨fun Ψ _ σ val ↦ ?_, fun Θ hΘ σ ↦ ?_⟩
  · simp only [DynamicCircuit.andCompute, DynamicCircuit.compile_seq,
      DynamicCircuit.compile_circuit, wp_qSeq,
      wp_circuit_compile_compat, wpQAssignCompat]
    exact congrArg _ (congrArg (fun x ↦ (x : Observable (Fin (2 ^ n))))
      (hBody.1 (wp (DynamicCircuit.andUncompute v qc₁ qc₂ qanc hq₁₂).compile Ψ)
        (fun σ' v' ↦ wp_andUncompute_update_self v qc₁ qc₂ qanc hq₁₂ Ψ σ' v') σ val))
  · let Ψ := wp (DynamicCircuit.andUncompute v qc₁ qc₂ qanc hq₁₂).compile Θ
    have hΨ_inv : ∀ σ' v', Ψ (Function.update σ' v v') = Ψ σ' :=
      fun σ' v' ↦ wp_andUncompute_update_self v qc₁ qc₂ qanc hq₁₂ Θ σ' v'
    have hstep1 : ((wp (.qSeq (DynamicCircuit.andCompute (Var := Var) qc₁ qc₂ qanc hq₁a
        hq₂a).compile (.qSeq dBody.compile (DynamicCircuit.andUncompute v qc₁ qc₂ qanc
        hq₁₂).compile)) Θ σ).1).conj P₀ = ((wpQAssignCompat T_anc (wp dBody.compile Ψ) σ).1).conj
        P₀ := congrArg Subtype.val (congrFun
      (restrictToZeroAncilla_wp_andCompute_seq_compat qc₁ qc₂ qanc hq₁₂ hq₁a hq₂a
        (.qSeq dBody.compile (DynamicCircuit.andUncompute v qc₁ qc₂ qanc hq₁₂).compile) Θ) σ)
    have hstep_uncomp : ((wpQAssignCompat T_anc Ψ σ).1).conj P₀ = (Θ σ).1.conj P₀ :=
      congrArg Subtype.val (congrFun
        (restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
          v qc₁ qc₂ qanc hq₁₂ hq₁a hq₂a Θ hΘ) σ)
    have hswap1 : P_rest * (P₀ * T_anc.1ᴴ) = (P₀ * T_anc.1ᴴ) * P_rest := by
      rw [← Matrix.mul_assoc, ← hcomm_P, Matrix.mul_assoc, hcomm_T_adj, ← Matrix.mul_assoc]
    have hprod_adj :
        (P₀ * T_anc.1ᴴ) * (P_rest * U_body.1ᴴ) = (P_all * U_clean.1ᴴ * P₀) * T_anc.1ᴴ := by
      have h1 : (P₀ * T_anc.1ᴴ) * (P_rest * U_body.1ᴴ) = P_all * (U_body * T_anc).1ᴴ := by
        rw [← Matrix.mul_assoc, ← hswap1, hPall_eq, Submonoid.coe_mul, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      have h2 : P_all * V.1ᴴ = P_all * U_clean.1ᴴ := by
        simpa [conjTranspose_mul, hPall_herm] using congrArg conjTranspose hV_eq_clean
      rw [h1, hU_eq, Submonoid.coe_mul, conjTranspose_mul, ← Matrix.mul_assoc, h2, hclean_adj]
    change ((wp (.qSeq (DynamicCircuit.andCompute (Var := Var) qc₁ qc₂ qanc hq₁a hq₂a).compile
        (.qSeq dBody.compile (DynamicCircuit.andUncompute v qc₁ qc₂ qanc hq₁₂).compile))
        Θ σ).1).conj P_all = ((wpQAssignCompat U_clean Θ σ).1).conj P_all
    rw [hPall_eq, ← conj_conj, hstep1]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    rw [hswap1, ← habsorb_adj, ← conj_conj, hBody.2 Ψ hΨ_inv σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    rw [← Matrix.mul_assoc (P₀ * T_anc.1ᴴ) P_body U_body.1ᴴ, habsorb_adj, Matrix.mul_assoc,
      hprod_adj, Matrix.mul_assoc (P_all * U_clean.1ᴴ) P₀ T_anc.1ᴴ, ← conj_conj]
    have hmid : (Ψ σ).1.conj (P₀ * T_anc.1ᴴ) = (Θ σ).1.conj P₀ := by
      simpa [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, conj_conj] using hstep_uncomp
    rw [hmid, conj_conj, hclean_adj, hPall_eq]
theorem p57ToDynWith_realizes_inv
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n)
    (innerProg : TempPhaseProg M) (dInner : DynamicCircuit Var n)
    (InvHole : BitAssignment M → Prop) (remHole : ℕ) (hremHole : remHole ≤ M)
    (hInner : RealizesCleanUnitary v (p57CleanDiagProj rComb remHole hremHole InvHole)
      dInner (((innerProg.onRegister rComb).toToffCircuit).eval))
    (hInnerRem : ∀ r, ValidCleanRem M r innerProg → remHole ≤ r) :
    ∀ (K : TempCtx M) (rem : ℕ) (hrem : rem ≤ M) (Inv : BitAssignment M → Prop),
      ValidCleanRem M rem (K.plug innerProg) →
      (∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ → InvHole (K.fwdBits γ)) →
      RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem Inv)
        (p57ToDynWith v rComb dInner K)
        ((((K.plug innerProg).onRegister rComb).toToffCircuit).eval)
  | .hole, rem, hrem, Inv, hv, hFwd =>
      RealizesCleanUnitary.mono_proj
        (p57CleanDiagProj_conjTranspose rComb remHole hremHole InvHole)
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_mono rComb hremHole hrem (hInnerRem rem hv) hFwd) hInner
  | .seqPre c K, rem, hrem, Inv, ⟨remMid, hmid, _, hv₂, hpres⟩, hFwd => by
      let InvMid : BitAssignment M → Prop := fun δ ↦ ∃ γ, cleanRem M rem γ ∧ Inv γ ∧ δ = c.eval γ
      have hseq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_conjTranspose rComb remMid hmid InvMid)
        (RealizesCleanUnitary.circuit v _ ((c.onRegister rComb).toCircuit))
        (p57ToDynWith_realizes_inv v rComb innerProg dInner InvHole remHole hremHole hInner
          hInnerRem K remMid hmid InvMid hv₂ (fun _ _ ⟨γ, hcr, hi, heq⟩ ↦ heq ▸ hFwd γ hcr hi))
        (p57SeqClean_prog_inv rComb (.cliff c) hrem hmid
          (fun γ hcr hi ↦ ⟨hpres γ hcr, ⟨γ, hcr, hi, rfl⟩⟩))
      dsimp only [p57ToDynWith]
      rwa [show ((K.plug innerProg).onRegister rComb).toToffCircuit.eval *
          ((c.onRegister rComb).toCircuit).eval =
          ((((TempCtx.seqPre c K).plug innerProg).onRegister rComb).toToffCircuit).eval by
        simp [TempCtx.plug, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
          Circuit.eval_seq]] at hseq
  | .seqPost K c, rem, hrem, Inv, ⟨remMid, hmid, hv₁, _, hpres⟩, hFwd => by
      have hseq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
        (p57CleanDiagProj_conjTranspose rComb remMid hmid (fun _ ↦ True))
        (p57ToDynWith_realizes_inv v rComb innerProg dInner InvHole remHole hremHole hInner
          hInnerRem K rem hrem Inv hv₁ hFwd)
        (RealizesCleanUnitary.circuit v _ ((c.onRegister rComb).toCircuit))
        (p57SeqClean_prog_inv rComb (K.plug innerProg) hrem hmid
          (fun γ hcr _ ↦ ⟨hpres γ hcr, trivial⟩))
      dsimp only [p57ToDynWith]
      rwa [show ((c.onRegister rComb).toCircuit).eval *
          ((K.plug innerProg).onRegister rComb).toToffCircuit.eval =
          ((((TempCtx.seqPost K c).plug innerProg).onRegister rComb).toToffCircuit).eval by
        simp [TempCtx.plug, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
          Circuit.eval_seq]] at hseq
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, rem, hrem, Inv, ⟨hanc_lo, hvBody, hpresBody⟩, hFwd => by
      have hanc_lt : anc.val < M := anc.isLt
      exact p57WithTempAnd_cleanDiagProj v rComb c₁ c₂ anc h₁₂ h₁a h₂a rem hrem hanc_lo Inv
        (K.plug innerProg) (p57ToDynWith v rComb dInner K) hpresBody
        (p57ToDynWith_realizes_inv v rComb innerProg dInner InvHole remHole hremHole hInner
          hInnerRem K (M - (anc.val + 1)) (by omega) _ hvBody fun δ _ ⟨⟨hcr, hi⟩, hbit⟩ ↦ by
            have hstep := hFwd (Function.update δ anc 0) hcr hi
            dsimp only [TempCtx.fwdBits] at hstep
            convert hstep using 2
            funext w
            by_cases hw : w = anc
            · subst hw
              simp [Function.update_self, Function.update_of_ne h₁a,
                Function.update_of_ne h₂a, hbit]
            · simp [Function.update_of_ne hw])
end P57DynBridge
section P57CleanMsbBooth
open HermitianMat MeasureBranchHadamardSem
open BchCubeDecoder StreamingBchComparator
theorem bitsVal_fin_zero (f : Fin 0 → ZMod 2) : bitsVal f = 0 := by
  simp [bitsVal]
def inPlaceAddMod1 {M : ℕ} :
    (W cur : ℕ) → (hcur : cur + W ≤ M) →
    (b acc : Fin (W + 1) → Wire M) → (cin : Wire M) →
    (hab : ∀ j, acc j ≠ b j) → (hac : ∀ j, acc j ≠ cin) → (hbc : ∀ j, b j ≠ cin) →
    (hb : ∀ j, (b j).val < cur) → (ha : ∀ j, (acc j).val < cur) → (hc : cin.val < cur) →
    TempPhaseProg M
  | 0, _, _, b, acc, cin, hab, hac, _, _, _, _ =>
      .cliff (.seq (.cnot cin (acc 0) (hac 0).symm) (.cnot (b 0) (acc 0) (hab 0).symm))
  | W + 1, cur, hcur, b, acc, cin, hab, hac, hbc, hb, ha, hc =>
      let cout : Wire M := ⟨cur, by omega⟩
      let cPre : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cPost : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot (b 0) (acc 0) (hab 0).symm)
      let innerRec := inPlaceAddMod1 W (cur + 1) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) cout
        (fun j ↦ hab j.succ)
        (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp [cout]; omega))
        (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp [cout]; omega))
        (fun j ↦ lt_trans (hb j.succ) (by omega))
        (fun j ↦ lt_trans (ha j.succ) (by omega))
        (by dsimp [cout]; omega)
      let inner := withCliffAlloc (.cnot cin cout (wire_ne_of_lt (by dsimp [cout]; omega))) innerRec
      .seq (.cliff cPre)
        (.seq (.tempAnd (b 0) (acc 0) cout (hab 0).symm
            (wire_ne_of_lt (hb 0)) (wire_ne_of_lt (ha 0)) inner)
          (.cliff cPost))
theorem inPlaceAddMod1_countTempAnd {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (b acc : Fin (W + 1) → Wire M) (cin : Wire M)
      (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hc : cin.val < cur),
      (inPlaceAddMod1 W cur hcur b acc cin hab hac hbc hb ha hc).countTempAnd = W
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, b, acc, cin, hab, hac, hbc, hb, ha, hc => by
      dsimp only [inPlaceAddMod1]
      simp only [TempPhaseProg.countTempAnd, withCliffAlloc_countTempAnd,
        inPlaceAddMod1_countTempAnd W (cur + 1)]
      omega
theorem zmod2_add3_val_mod2 (a b c : ZMod 2) :
    (a + b + c).val = (a.val + b.val + c.val) % 2 := by
  rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;> decide
theorem p57Slim_carryStep_spec {M : ℕ} (cur : ℕ) (hcur1 : cur + 1 ≤ M)
    (x0 y0 cin : Wire M) (hxy : x0 ≠ y0)
    (hx0 : x0.val < cur) (hy0 : y0.val < cur) (hc : cin.val < cur)
    (cPre cPost : CliffProg M) (hcPre : cPre.SupportsBelow cur)
    (pRec : TempPhaseProg M) (mutRec : Wire M → Prop)
    (hvRec : ValidCleanRem M (M - (cur + 1)) pRec)
    (hsRec : ∀ γ : BitAssignment M, cleanRem M (M - (cur + 1)) γ → pRec.evalSign γ = 0)
    (hNonRec : ∀ γ : BitAssignment M, cleanRem M (M - (cur + 1)) γ →
      ∀ w : Wire M, ¬ mutRec w → pRec.evalBits γ w = γ w)
    (hnm_x0 : ¬ mutRec x0) (hnm_y0 : ¬ mutRec y0) (hnm_cin : ¬ mutRec cin)
    (hnm_hi : ∀ u : Wire M, cur ≤ u.val → ¬ mutRec u) :
    let cout : Wire M := ⟨cur, hcur1⟩
    let pStep : TempPhaseProg M := .seq (.cliff cPre)
      (.seq (.tempAnd x0 y0 cout hxy (wire_ne_of_lt hx0) (wire_ne_of_lt hy0)
          (withCliffAlloc (.cnot cin cout (wire_ne_of_lt hc)) pRec))
        (.cliff cPost))
    ValidCleanRem M (M - cur) pStep ∧
      ∀ β : BitAssignment M, cleanRem M (M - cur) β →
        let β₁ := cPre.eval β
        let β₃ := Function.update β₁ cout (β₁ x0 * β₁ y0 + β₁ cin)
        let δ := Function.update (pRec.evalBits β₃) cout 0
        (CliffProg.cnot cin cout (wire_ne_of_lt hc)).eval
            (Function.update β₁ cout (β₁ cout + β₁ x0 * β₁ y0)) = β₃ ∧
          cleanRem M (M - (cur + 1)) β₃ ∧
          pStep.evalSign β = 0 ∧
          pStep.evalBits β = cPost.eval δ ∧
          (∀ w : Wire M, ¬ mutRec w → δ w = β₁ w) := by
  intro cout pStep
  have hcout : cout.val = cur := rfl
  let cCarry : CliffProg M := .cnot cin cout (wire_ne_of_lt hc)
  let inner := withCliffAlloc cCarry pRec
  have hnm_cout : ¬ mutRec cout := hnm_hi cout le_rfl
  obtain ⟨hvInner, hevInner⟩ := withCliffAlloc_valid_and_eval
    (M := M) (rem := M - (cur + 1)) (remIn := M - (cur + 1)) (by omega) le_rfl cCarry
    ⟨by omega, by omega⟩ pRec hvRec
  have hcPre_cl : ∀ β : BitAssignment M, cleanRem M (M - cur) β →
      cleanRem M (M - cur) (cPre.eval β) := fun β hβ w hw ↦
    (cPre.eval_outside hcPre β w (by omega)).trans (hβ w hw)
  have hInnerNon : ∀ γ : BitAssignment M, cleanRem M (M - (cur + 1)) γ →
      ∀ w : Wire M, ¬ mutRec w → inner.evalBits γ w = γ w := fun γ hγ w hnw ↦ by
    obtain ⟨hcγ, _, hev⟩ := hevInner γ hγ
    dsimp only [inner]
    rw [hev]
    change Function.update (pRec.evalBits (cCarry.eval γ)) cout
        (pRec.evalBits (cCarry.eval γ) cout + pRec.evalBits (cCarry.eval γ) cin) w = γ w
    by_cases hwc : w = cout
    · subst hwc
      rw [Function.update_self, hNonRec _ hcγ cout hnm_cout, hNonRec _ hcγ cin hnm_cin]
      dsimp only [cCarry, CliffProg.eval]
      rw [Function.update_self, Function.update_of_ne (wire_ne_of_lt hc : cin ≠ cout),
        zmod2_add_self_cancel]
    · rw [Function.update_of_ne hwc, hNonRec _ hcγ w hnw]
      dsimp only [cCarry, CliffProg.eval]
      rw [Function.update_of_ne hwc]
  refine ⟨⟨M - cur, by omega, trivial, ⟨0, Nat.zero_le M,
    ⟨by omega, hvInner, fun β₁ hβ₁ ↦
      ⟨hInnerNon β₁ hβ₁ x0 hnm_x0, hInnerNon β₁ hβ₁ y0 hnm_y0, hInnerNon β₁ hβ₁ cout hnm_cout⟩⟩,
    trivial, fun _ _ _ hw ↦ absurd hw (by omega)⟩, hcPre_cl⟩, fun β hβ ↦ ?_⟩
  let β₁ := cPre.eval β
  have hcl₁ : cleanRem M (M - cur) β₁ := hcPre_cl β hβ
  let β₂ := Function.update β₁ cout (β₁ cout + β₁ x0 * β₁ y0)
  let β₃ := Function.update β₁ cout (β₁ x0 * β₁ y0 + β₁ cin)
  let δ := Function.update (pRec.evalBits β₃) cout 0
  have hcl₂ : cleanRem M (M - (cur + 1)) β₂ := fun u hu ↦
    (Function.update_of_ne (wire_ne_of_gt (by omega)) _ _).trans (hcl₁ u (by omega))
  have hβ₃_eq : cCarry.eval β₂ = β₃ := funext fun u ↦ by
    dsimp only [cCarry, CliffProg.eval]
    by_cases huc : u = cout
    · subst huc
      rw [Function.update_self]
      dsimp only [β₂, β₃]
      rw [Function.update_self, Function.update_of_ne (wire_ne_of_lt hc : cin ≠ cout),
        Function.update_self, hcl₁ cout (by omega), zero_add]
    · rw [Function.update_of_ne huc]
      dsimp only [β₂, β₃]
      rw [Function.update_of_ne huc, Function.update_of_ne huc]
  obtain ⟨hc₃, hsIn, hevIn⟩ := hevInner β₂ hcl₂
  rw [hβ₃_eq] at hc₃ hsIn hevIn
  refine ⟨hβ₃_eq, hc₃, ?_, ?_, fun w hnw ↦ ?_⟩
  · change 0 + (inner.evalSign β₂ + 0) = 0
    rw [hsIn, hsRec β₃ hc₃]
    rfl
  · refine congrArg cPost.eval (funext fun u ↦ ?_)
    change Function.update (inner.evalBits β₂) cout
        (inner.evalBits β₂ cout + inner.evalBits β₂ x0 * inner.evalBits β₂ y0) u = δ u
    by_cases huc : u = cout
    · subst huc
      rw [Function.update_self, hInnerNon β₂ hcl₂ cout hnm_cout,
        hInnerNon β₂ hcl₂ x0 hnm_x0, hInnerNon β₂ hcl₂ y0 hnm_y0]
      dsimp only [β₂, δ]
      rw [Function.update_self, Function.update_of_ne (wire_ne_of_lt hx0 : x0 ≠ cout),
        Function.update_of_ne (wire_ne_of_lt hy0 : y0 ≠ cout), Function.update_self,
        hcl₁ cout (by omega), zero_add, CharTwo.add_self_eq_zero]
    · rw [Function.update_of_ne huc, hevIn]
      dsimp only [cCarry, CliffProg.inv, CliffProg.eval, δ]
      rw [Function.update_of_ne huc, Function.update_of_ne huc]
  · by_cases hwc : w = cout
    · subst hwc
      exact (Function.update_self cout 0 _).trans (hcl₁ cout (by omega)).symm
    · exact (Function.update_of_ne hwc _ _).trans
        ((hNonRec β₃ hc₃ w hnw).trans (Function.update_of_ne hwc _ _))
theorem inPlaceAddMod1_spec {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (b acc : Fin (W + 1) → Wire M) (cin : Wire M)
      (hab_disj : ∀ i j, acc i ≠ b j)
      (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (_hb_inj : Function.Injective b) (_ha_inj : Function.Injective acc)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hc : cin.val < cur),
      let p := inPlaceAddMod1 W cur hcur b acc cin (fun j ↦ hab_disj j j) hac hbc hb ha hc
      ValidCleanRem M (M - cur) p ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β → p.evalSign β = 0) ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - cur) (p.evalBits β) ∧
          (∀ w : Wire M, (∀ j, w ≠ acc j) → p.evalBits β w = β w) ∧
          bitsVal (fun j ↦ p.evalBits β (acc j)) =
            (bitsVal (fun j ↦ β (acc j)) + bitsVal (fun j ↦ β (b j)) + (β cin).val) % 2 ^ (W + 1))
  | 0, cur, hcur, b, acc, cin, hab_disj, hac, hbc, _, _, hb, ha, hc => by
      refine ⟨trivial, fun _ _ ↦ rfl, fun β hβ ↦ ?_⟩
      have hnon : ∀ w : Wire M, (∀ j : Fin 1, w ≠ acc j) →
          (inPlaceAddMod1 0 cur hcur b acc cin (fun j ↦ hab_disj j j) hac hbc hb ha hc).evalBits β w
            = β w := by
        intro w hw
        have hw0 : w ≠ acc 0 := hw 0
        dsimp [inPlaceAddMod1, TempPhaseProg.evalBits, CliffProg.eval]
        rw [Function.update_of_ne hw0, Function.update_of_ne hw0]
      refine ⟨fun w hw ↦ ?_, hnon, ?_⟩
      · rw [hnon w (fun j ↦ wire_ne_of_gt (by have := ha j; omega))]
        exact hβ w hw
      · dsimp [inPlaceAddMod1, TempPhaseProg.evalBits, CliffProg.eval]
        rw [bitsVal_succ_split, bitsVal_succ_split, bitsVal_succ_split]
        simp only [bitsVal_fin_zero, mul_zero, add_zero]
        rw [Function.update_self, Function.update_self, Function.update_of_ne (hab_disj 0 0).symm]
        have heq : β (acc 0) + β cin + β (b 0) = β (acc 0) + β (b 0) + β cin := by ring
        rw [heq, zmod2_add3_val_mod2]
  | W + 1, cur, hcur, b, acc, cin, hab_disj, hac, hbc, hb_inj, ha_inj, hb, ha, hc => by
      dsimp only [inPlaceAddMod1]
      let cout : Wire M := ⟨cur, by omega⟩
      let cPre : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cPost : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot (b 0) (acc 0) (hab_disj 0 0).symm)
      let innerRec := inPlaceAddMod1 W (cur + 1) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) cout
        (fun j ↦ hab_disj j.succ j.succ)
        (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp [cout]; omega))
        (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp [cout]; omega))
        (fun j ↦ lt_trans (hb j.succ) (by omega))
        (fun j ↦ lt_trans (ha j.succ) (by omega))
        (by dsimp [cout]; omega)
      let cCarry : CliffProg M := .cnot cin cout (wire_ne_of_lt (by dsimp [cout]; omega))
      let inner := withCliffAlloc cCarry innerRec
      obtain ⟨hvRec, hsRec, hRec⟩ := inPlaceAddMod1_spec W (cur + 1) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) cout
        (fun i j ↦ hab_disj i.succ j.succ)
        (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp [cout]; omega))
        (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp [cout]; omega))
        (hb_inj.comp (Fin.succ_injective (W + 1)))
        (ha_inj.comp (Fin.succ_injective (W + 1)))
        (fun j ↦ lt_trans (hb j.succ) (by omega))
        (fun j ↦ lt_trans (ha j.succ) (by omega))
        (by dsimp [cout]; omega)
      obtain ⟨hvInner, hevInner⟩ := withCliffAlloc_valid_and_eval
        (M := M) (rem := M - (cur + 1)) (remIn := M - (cur + 1))
        (by omega) le_rfl cCarry
        ⟨by have := hc; omega, by dsimp [cout]; omega⟩
        innerRec hvRec
      have hcPre_cl : ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - cur) (cPre.eval β) := fun β hβ w hw ↦ by
        rw [cPre.eval_outside ⟨⟨hc, hb 0⟩,⟨hc, ha 0⟩⟩ β w (by omega)]
        exact hβ w hw
      have hInnerNon : ∀ γ : BitAssignment M, cleanRem M (M - (cur + 1)) γ →
          ∀ w : Wire M, (∀ j : Fin (W + 1), w ≠ acc j.succ) → inner.evalBits γ w = γ w := by
        intro γ hγ w hw
        obtain ⟨hcγ, _, hev⟩ := hevInner γ hγ
        have hcin_eq : innerRec.evalBits (cCarry.eval γ) cin = γ cin := by
          have h1 : innerRec.evalBits (cCarry.eval γ) cin = (cCarry.eval γ) cin :=
            (hRec (cCarry.eval γ) hcγ).2.1 cin (fun j ↦ (hac j.succ).symm)
          rw [h1]
          dsimp only [cCarry, CliffProg.eval]
          exact Function.update_of_ne (wire_ne_of_lt (by dsimp [cout]; omega)) _ _
        have hcout_eq : innerRec.evalBits (cCarry.eval γ) cout = (cCarry.eval γ) cout :=
          (hRec (cCarry.eval γ) hcγ).2.1 cout
            (fun j ↦ wire_ne_of_gt (by have := ha j.succ; dsimp [cout]; omega))
        have hw_eq : innerRec.evalBits (cCarry.eval γ) w = (cCarry.eval γ) w :=
          (hRec (cCarry.eval γ) hcγ).2.1 w hw
        dsimp only [inner]
        rw [hev]
        by_cases hwc : w = cout
        · subst hwc
          have hinv1 : (cCarry.inv.eval (innerRec.evalBits (cCarry.eval γ))) cout =
              innerRec.evalBits (cCarry.eval γ) cout + innerRec.evalBits (cCarry.eval γ) cin := by
            dsimp only [cCarry, CliffProg.inv, CliffProg.eval]
            exact Function.update_self _ _ _
          rw [hinv1, hcout_eq, hcin_eq]
          dsimp only [cCarry, CliffProg.eval]
          rw [Function.update_self]
          exact zmod2_add_self_cancel _ _
        · have hinv2 : (cCarry.inv.eval (innerRec.evalBits (cCarry.eval γ))) w =
              innerRec.evalBits (cCarry.eval γ) w := by
            dsimp only [cCarry, CliffProg.inv, CliffProg.eval]
            exact Function.update_of_ne hwc _ _
          rw [hinv2, hw_eq]
          dsimp only [cCarry, CliffProg.eval]
          exact Function.update_of_ne hwc _ _
      have hvTemp : ValidCleanRem M (M - cur) (.tempAnd (b 0) (acc 0) cout (hab_disj 0 0).symm
          (wire_ne_of_lt (hb 0)) (wire_ne_of_lt (ha 0)) inner) := by
        refine ⟨by dsimp [cout]; omega, hvInner, fun β₁ hβ₁ ↦ ?_⟩
        have hcl₁' : cleanRem M (M - (cur + 1)) β₁ := by dsimp [cout] at hβ₁; exact hβ₁
        exact ⟨hInnerNon β₁ hcl₁' (b 0) (fun j ↦ (hab_disj j.succ 0).symm),
          hInnerNon β₁ hcl₁' (acc 0) (fun j h ↦ Fin.succ_ne_zero j (ha_inj h.symm)),
          hInnerNon β₁ hcl₁' cout (fun j ↦ wire_ne_of_gt (by
            have := ha j.succ; dsimp [cout]; omega))⟩
      have hTempCl : ∀ β₁ : BitAssignment M, cleanRem M (M - cur) β₁ → cleanRem M (M - cur)
          ((TempPhaseProg.tempAnd (b 0) (acc 0) cout (hab_disj 0 0).symm (wire_ne_of_lt (hb
          0)) (wire_ne_of_lt (ha 0)) inner).evalBits β₁) := by
        intro β₁ hβ₁ w hw
        dsimp only [TempPhaseProg.evalBits]
        let β₂ := Function.update β₁ cout (β₁ cout + β₁ (b 0) * β₁ (acc 0))
        have hcl₂ : cleanRem M (M - (cur + 1)) β₂ := fun u hu ↦ by
          dsimp only [β₂]
          rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [cout]; omega))]
          exact hβ₁ u (by omega)
        by_cases hwc : w = cout
        · subst hwc
          rw [Function.update_self,
            hInnerNon β₂ hcl₂ cout (fun j ↦ wire_ne_of_gt (by
              have := ha j.succ; dsimp [cout]; omega)),
            hInnerNon β₂ hcl₂ (b 0) (fun j ↦ (hab_disj j.succ 0).symm),
            hInnerNon β₂ hcl₂ (acc 0) (fun j h ↦ Fin.succ_ne_zero j (ha_inj h.symm))]
          simp [β₂, Function.update_self,
            Function.update_of_ne (wire_ne_of_lt (hb 0) : b 0 ≠ cout),
            Function.update_of_ne (wire_ne_of_lt (ha 0) : acc 0 ≠ cout),
            hβ₁ cout hw, CharTwo.add_self_eq_zero]
        · rw [Function.update_of_ne hwc,
            hInnerNon β₂ hcl₂ w (fun j ↦ wire_ne_of_gt (by have := ha j.succ; omega))]
          dsimp only [β₂]
          rw [Function.update_of_ne hwc]
          exact hβ₁ w hw
      have hvAll : ValidCleanRem M (M - cur) (.seq (.cliff cPre) (.seq (.tempAnd (b 0) (acc 0)
          cout (hab_disj 0 0).symm (wire_ne_of_lt (hb 0)) (wire_ne_of_lt (ha 0)) inner)
          (.cliff cPost))) :=
        ⟨M - cur, by omega, trivial, ⟨M - cur, by omega, hvTemp, trivial, hTempCl⟩, hcPre_cl⟩
      refine ⟨hvAll, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
      · have hcl₁ := hcPre_cl β hβ
        let β₂ := Function.update (cPre.eval β) cout
          ((cPre.eval β) cout + (cPre.eval β) (b 0) * (cPre.eval β) (acc 0))
        have hcl₂ : cleanRem M (M - (cur + 1)) β₂ := fun u hu ↦ by
          dsimp only [β₂]
          rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [cout]; omega))]
          exact hcl₁ u (by omega)
        obtain ⟨hc₃, hsIn, _⟩ := hevInner β₂ hcl₂
        change 0 + ((withCliffAlloc cCarry innerRec).evalSign β₂ + 0) = 0
        rw [hsIn, hsRec _ hc₃]; rfl
      · dsimp only [TempPhaseProg.evalBits]
        let β₁ := cPre.eval β
        have hcl₁ := hcPre_cl β hβ
        let β₂ := Function.update β₁ cout (β₁ cout + β₁ (b 0) * β₁ (acc 0))
        have hcl₂ : cleanRem M (M - (cur + 1)) β₂ := fun u hu ↦ by
          dsimp only [β₂]
          rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [cout]; omega))]
          exact hcl₁ u (by omega)
        obtain ⟨hc₃, _, hevIn⟩ := hevInner β₂ hcl₂
        let β₃ := cCarry.eval β₂
        let β₄ := inner.evalBits β₂
        let β₅ := Function.update β₄ cout (β₄ cout + β₄ (b 0) * β₄ (acc 0))
        let β_out := cPost.eval β₅
        have hβ₅_cout : β₅ cout = 0 := by
          dsimp [β₅, β₄]
          rw [Function.update_self,
            hInnerNon β₂ hcl₂ cout (fun j ↦ wire_ne_of_gt (by
              have := ha j.succ; dsimp [cout]; omega)),
            hInnerNon β₂ hcl₂ (b 0) (fun j ↦ (hab_disj j.succ 0).symm),
            hInnerNon β₂ hcl₂ (acc 0) (fun j h ↦ Fin.succ_ne_zero j (ha_inj h.symm))]
          simp [β₂, Function.update_self,
            Function.update_of_ne (wire_ne_of_lt (hb 0) : b 0 ≠ cout),
            Function.update_of_ne (wire_ne_of_lt (ha 0) : acc 0 ≠ cout),
            show β₁ cout = 0 from hcl₁ cout (by dsimp [cout]; omega),
            CharTwo.add_self_eq_zero]
        have hβ₁_b0 : β₁ (b 0) = β (b 0) + β cin := by
          dsimp [β₁, cPre, CliffProg.eval]
          rw [Function.update_of_ne (hab_disj 0 0).symm, Function.update_self]
        have hβ₁_a0 : β₁ (acc 0) = β (acc 0) + β cin := by
          dsimp [β₁, cPre, CliffProg.eval]
          rw [Function.update_self, Function.update_of_ne (hab_disj 0 0),
            Function.update_of_ne (hbc 0).symm]
        have hβ₁_other : ∀ w : Wire M, w ≠ b 0 → w ≠ acc 0 → β₁ w = β w := fun w h1 h2 ↦ by
          dsimp [β₁, cPre, CliffProg.eval]
          rw [Function.update_of_ne h2, Function.update_of_ne h1]
        have hβ₄_b0 : β₄ (b 0) = β (b 0) + β cin := by
          dsimp only [β₄]
          rw [hInnerNon β₂ hcl₂ (b 0) (fun j ↦ (hab_disj j.succ 0).symm)]
          simpa [β₂, Function.update_of_ne (wire_ne_of_lt (hb 0) : b 0 ≠ cout)] using hβ₁_b0
        have hβ₄_a0 : β₄ (acc 0) = β (acc 0) + β cin := by
          dsimp only [β₄]
          rw [hInnerNon β₂ hcl₂ (acc 0) (fun j h ↦ Fin.succ_ne_zero j (ha_inj h.symm))]
          simpa [β₂, Function.update_of_ne (wire_ne_of_lt (ha 0) : acc 0 ≠ cout)] using hβ₁_a0
        have hβ₅_cin : β₅ cin = β cin := by
          dsimp [β₅, β₄]
          rw [Function.update_of_ne (wire_ne_of_lt hc : cin ≠ cout),
            hInnerNon β₂ hcl₂ cin (fun j ↦ (hac j.succ).symm)]
          dsimp only [β₂]
          rw [Function.update_of_ne (wire_ne_of_lt hc : cin ≠ cout),
            hβ₁_other cin (hbc 0).symm (hac 0).symm]
        have hNonOut : ∀ w : Wire M, (∀ j : Fin (W + 2), w ≠ acc j) → β_out w = β w := by
          intro w hw
          have hwa0 : w ≠ acc 0 := hw 0
          dsimp [β_out, cPost, CliffProg.eval]
          rw [Function.update_of_ne hwa0]
          by_cases hwb0 : w = b 0
          · subst hwb0
            rw [Function.update_self, hβ₅_cin]
            dsimp [β₅]
            rw [Function.update_of_ne (wire_ne_of_lt (hb 0) : b 0 ≠ cout), hβ₄_b0]
            exact zmod2_add_self_cancel _ _
          · rw [Function.update_of_ne hwb0]
            by_cases hwc : w = cout
            · subst hwc
              rw [hβ₅_cout]
              exact (hβ cout (by dsimp [cout]; omega)).symm
            · dsimp [β₅, β₄]
              rw[Function.update_of_ne hwc, hInnerNon β₂ hcl₂ w (fun j ↦ hw j.succ)]
              dsimp only [β₂]
              rw[Function.update_of_ne hwc, hβ₁_other w hwb0 hwa0]
        have hClOut : cleanRem M (M - cur) β_out := fun w hw ↦ by
          rw [hNonOut w (fun j ↦ wire_ne_of_gt (by have := ha j; omega))]
          exact hβ w hw
        refine ⟨hClOut, hNonOut, ?_⟩
        have hout0 : β_out (acc 0) = β (acc 0) + β (b 0) + β cin := by
          dsimp [β_out, cPost, CliffProg.eval]
          rw [Function.update_self, Function.update_of_ne (hab_disj 0 0), Function.update_self,
            hβ₅_cin]
          dsimp [β₅]
          rw [Function.update_of_ne (wire_ne_of_lt (ha 0) : acc 0 ≠ cout),
            Function.update_of_ne (wire_ne_of_lt (hb 0) : b 0 ≠ cout),
            hβ₄_a0, hβ₄_b0, zmod2_add_self_cancel]
          ring
        have houtSucc : ∀ j : Fin (W + 1),
          β_out (acc j.succ) = innerRec.evalBits β₃ (acc j.succ) := by
          intro j
          have h1 : acc j.succ ≠ b 0 := hab_disj j.succ 0
          have h2 : acc j.succ ≠ acc 0 := fun h ↦ Fin.succ_ne_zero j (ha_inj h)
          have h3 : acc j.succ ≠ cout := wire_ne_of_lt (by have := ha j.succ; dsimp [cout]; omega)
          dsimp [β_out, cPost, CliffProg.eval, β₅, β₄]
          rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h3, hevIn]
          dsimp [cCarry, CliffProg.inv, CliffProg.eval]
          exact Function.update_of_ne h3 _ _
        have hβ₃_cout : β₃ cout = β cin + (β (acc 0) + β cin) * (β (b 0) + β cin) := by
          dsimp [β₃, cCarry, CliffProg.eval, β₂]
          rw [Function.update_self, Function.update_of_ne (wire_ne_of_lt hc : cin ≠ cout),
            hβ₁_other cin (hbc 0).symm (hac 0).symm,
            Function.update_self, hβ₁_b0, hβ₁_a0,
            hβ₁_other cout (wire_ne_of_lt (hb 0)).symm (wire_ne_of_lt (ha 0)).symm,
            hβ cout (by dsimp [cout]; omega), zero_add, mul_comm, add_comm]
        have hβ₃_acc : (fun j : Fin (W + 1) ↦ β₃ (acc j.succ)) = fun j ↦ β (acc j.succ) :=
          funext fun j ↦ by
            dsimp [β₃, cCarry, CliffProg.eval, β₂]
            rw [Function.update_of_ne (wire_ne_of_lt (by have := ha j.succ; dsimp [cout]; omega)),
              Function.update_of_ne (wire_ne_of_lt (by have := ha j.succ; dsimp [cout]; omega)),
              hβ₁_other _ (hab_disj j.succ 0) (fun h ↦ Fin.succ_ne_zero j (ha_inj h))]
        have hβ₃_b : (fun j : Fin (W + 1) ↦ β₃ (b j.succ)) = fun j ↦ β (b j.succ) :=
          funext fun j ↦ by
            dsimp [β₃, cCarry, CliffProg.eval, β₂]
            rw [Function.update_of_ne (wire_ne_of_lt (by have := hb j.succ; dsimp [cout]; omega)),
              Function.update_of_ne (wire_ne_of_lt (by have := hb j.succ; dsimp [cout]; omega)),
              hβ₁_other _ (fun h ↦ Fin.succ_ne_zero j (hb_inj h)) (hab_disj 0 j.succ).symm]
        change bitsVal (fun j ↦ β_out (acc j)) = _
        rw [bitsVal_succ_split (fun j ↦ β_out (acc j)), hout0]
        simp_rw [houtSucc]
        have hRecVal : bitsVal (fun j ↦ innerRec.evalBits β₃ (acc j.succ)) = (bitsVal (fun j ↦
            β₃ (acc j.succ)) + bitsVal (fun j ↦ β₃ (b j.succ)) + (β₃ cout).val) % 2 ^ (W + 1)
            := (hRec β₃ hc₃).2.2
        rw [hRecVal, hβ₃_acc, hβ₃_b, hβ₃_cout,
          bitsVal_succ_split (fun j ↦ β (acc j)), bitsVal_succ_split (fun j ↦ β (b j))]
        have hfa := fullAdd_val_eq (β (acc 0)) (β (b 0)) (β cin)
        set s0 := (β (acc 0) + β (b 0) + β cin).val
        set c1 := (β cin + (β (acc 0) + β cin) * (β (b 0) + β cin)).val
        set S := bitsVal (fun j ↦ β (acc j.succ)) + bitsVal (fun j ↦ β (b j.succ)) + c1
        have hs0_lt : s0 < 2 := ZMod.val_lt _
        have htot : (β (acc 0)).val + 2 * bitsVal (fun j ↦ β (acc j.succ)) +
            ((β (b 0)).val + 2 * bitsVal (fun j ↦ β (b j.succ))) + (β cin).val = s0 + 2 * S := by
          omega
        rw [htot]
        have hpw : 0 < 2 ^ (W + 1) := by positivity
        have hdiv := Nat.div_add_mod S (2 ^ (W + 1))
        have hrem_lt : S % 2 ^ (W + 1) < 2 ^ (W + 1) := Nat.mod_lt S hpw
        have hp2 : 2 ^ (W + 2) = 2 * 2 ^ (W + 1) := by ring
        have hsplit : s0 + 2 * S = (s0 + 2 * (S % 2 ^ (W + 1))) + (S / 2 ^ (W + 1)) * 2 ^ (W + 2) :=
          by
          nlinarith
        conv_rhs =>
          rw [hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
attribute [local irreducible] inPlaceAddMod1
theorem zmod2_eq_of_val_eq {x y : ZMod 2} (h : x.val = y.val) : x = y := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl
  · rfl
  · exfalso; revert h; decide
  · exfalso; revert h; decide
  · rfl
theorem zmod2_cancel_mid (a b c : ZMod 2) : (a + b + c) + b = a + c := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;> decide
theorem zmod2_cancel_left_right (c x : ZMod 2) : (c + x) + c = x := by
  rcases bit_cases c with rfl | rfl <;> rcases bit_cases x with rfl | rfl <;> decide
theorem RealizesCleanUnitary_congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] {v : Var} {P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hP : Pᴴ = P) {d : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)}
    (hReal : RealizesCleanUnitary v P d U₁) (hEq : U₁.1 * P = U₂.1 * P) : RealizesCleanUnitary
    v P d U₂ := RealizesCleanUnitary.congr_unitary hP hReal hEq
def msbClearStatic {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ c₂ msb : Wire M) (h₁₂ : c₁ ≠ c₂)
    (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (hmsb : msb.val < cur) : TempPhaseProg M :=
  let anc : Wire M := ⟨cur, hcur⟩
  .tempAnd c₁ c₂ anc h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂)
    (.cliff (.cnot anc msb (wire_ne_of_gt hmsb)))
theorem msbClearStatic_congr {M : ℕ} {cur₁ cur₂ : ℕ} (hcur : cur₁ = cur₂) (h₁ : cur₁ + 1 ≤ M)
    (h₂ : cur₂ + 1 ≤ M) {c₁ c₁' c₂ c₂' msb : Wire M} (hc₁ : c₁ = c₁') (hc₂ : c₂ = c₂')
    (hne₁ : c₁ ≠ c₂) (hne₂ : c₁' ≠ c₂') (hlt1 : c₁.val < cur₁) (hlt1' : c₁'.val < cur₂)
    (hlt2 : c₂.val < cur₁) (hlt2' : c₂'.val < cur₂) (hltm : msb.val < cur₁)
    (hltm' : msb.val < cur₂) : msbClearStatic cur₁ h₁ c₁ c₂ msb hne₁ hlt1 hlt2 hltm =
    msbClearStatic cur₂ h₂ c₁' c₂' msb hne₂ hlt1' hlt2' hltm' := by
  subst hcur hc₁ hc₂; rfl
theorem msbClearStatic_valid_le {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (c₁ c₂ msb : Wire M)
    (h₁₂ : c₁ ≠ c₂) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (hmsb : msb.val < cur) (r : ℕ)
    (hr : ValidCleanRem M r (msbClearStatic cur hcur c₁ c₂ msb h₁₂ hc₁ hc₂ hmsb)) : M - cur ≤
    r := by
  have hlo : M - r ≤ cur := hr.1
  omega
theorem msbClearStatic_spec {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (c₁ c₂ msb : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁m : c₁ ≠ msb) (h₂m : c₂ ≠ msb)
    (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (hmsb : msb.val < cur) :
    let p := msbClearStatic cur hcur c₁ c₂ msb h₁₂ hc₁ hc₂ hmsb
    ValidCleanRem M (M - cur) p ∧
      p.countTempAnd = 1 ∧
      (∀ β : BitAssignment M, cleanRem M (M - cur) β → p.evalSign β = 0) ∧
      (∀ β : BitAssignment M, cleanRem M (M - cur) β →
        p.evalBits β = Function.update β msb (β msb + β c₁ * β c₂)) := by
  dsimp only [msbClearStatic]
  let anc : Wire M := ⟨cur, hcur⟩
  have hma : msb ≠ anc := wire_ne_of_lt hmsb
  refine ⟨⟨(by
      dsimp [anc]
      omega), trivial, fun _ _ ↦ ?_⟩, rfl, fun _ _ ↦ rfl, fun β hβ ↦ ?_⟩
  · dsimp [TempPhaseProg.evalBits, CliffProg.eval]
    exact ⟨Function.update_of_ne h₁m _ _, Function.update_of_ne h₂m _ _,
      Function.update_of_ne hma.symm _ _⟩
  · funext w
    dsimp [TempPhaseProg.evalBits, CliffProg.eval]
    have hanc0 : β anc = 0 := hβ anc (by
      dsimp [anc]
      omega)
    by_cases hwa : w = anc
    · subst hwa
      rw [Function.update_self, Function.update_of_ne hma.symm, Function.update_of_ne h₁m,
        Function.update_of_ne h₂m, Function.update_self, Function.update_of_ne (wire_ne_of_lt hc₁),
        Function.update_of_ne (wire_ne_of_lt hc₂), hanc0, zero_add, CharTwo.add_self_eq_zero,
        Function.update_of_ne hma.symm, hanc0]
    · rw [Function.update_of_ne hwa]
      by_cases hwm : w = msb
      · subst hwm
        rw [Function.update_self, Function.update_self, Function.update_of_ne hma,
          Function.update_self, hanc0, zero_add]
      · rw [Function.update_of_ne hwm, Function.update_of_ne hwa, Function.update_of_ne hwm]
open Classical in
theorem dMsbClear_realizes_static {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (cur : ℕ) (hcur : cur + 1 ≤ M)
    (c₁ c₂ msb : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁m : c₁ ≠ msb) (h₂m : c₂ ≠ msb)
    (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (hmsb : msb.val < cur) (rem : ℕ)
    (hrem : rem ≤ M) (hle : M - cur ≤ rem) (Inv : BitAssignment M → Prop) (hInvEq : ∀ γ :
    BitAssignment M, cleanRem M rem γ → Inv γ → γ msb = γ c₁ * γ c₂) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb rem hrem Inv) (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂)
    (rComb msb) (rComb.wires.injective.ne h₁₂)) ((((msbClearStatic cur hcur c₁ c₂ msb h₁₂ hc₁
    hc₂ hmsb).onRegister rComb).toToffCircuit).eval) := by
  refine RealizesCleanUnitary_congr_unitary
    (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
    (realizesClean_andUncompute_diag v rComb c₁ c₂ msb h₁₂ h₁m h₂m rem hrem Inv hInvEq) ?_
  obtain ⟨_, _, hSgn, hBits⟩ := msbClearStatic_spec cur hcur c₁ c₂ msb h₁₂ h₁m h₂m hc₁ hc₂ hmsb
  apply matrix_ext_ket
  intro β
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
  by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
  · simp only [h, and_self, ↓reduceIte, ket_TOFF, eval_onRegister_prog_ket,
      hSgn _ (cleanRem_anti hle h.1), hBits _ (cleanRem_anti hle h.1), ZMod.val_zero,
      _root_.pow_zero, one_smul]
    refine congrArg ket (funext fun q ↦ ?_)
    by_cases hqm : q = rComb msb
    · subst hqm
      rw [Function.update_self, writeRegProg_apply_reg, Function.update_self]
    · rw [Function.update_of_ne hqm]
      by_cases hreg : q ∈ Set.range rComb.wires
      · obtain ⟨idx, rfl⟩ := hreg
        rw [writeRegProg_apply_reg,
          Function.update_of_ne (fun heq ↦ hqm (congrArg rComb.wires heq))]
      · exact (writeRegProg_apply_of_not_mem β rComb _ q hreg).symm
  · simp [h]
def xorAndVecStatic {M : ℕ} : (W cur : ℕ) → (hcur : cur + 1 ≤ M) → (u0 : Wire M) →
    (sW acc : Fin W → Wire M) → (hu_s : ∀ j, u0 ≠ sW j) → (hu_lt : u0.val < cur) →
    (hs_lt : ∀ j, (sW j).val < cur) → (ha_lt : ∀ j, (acc j).val < cur) → TempPhaseProg M
  | 0, _, _, _, _, _, _, _, _, _ => .nil
  | W + 1, cur, hcur, u0, sW, acc, hu_s, hu_lt, hs_lt, ha_lt =>
      .seq (msbClearStatic cur hcur u0 (sW 0) (acc 0) (hu_s 0) hu_lt (hs_lt 0) (ha_lt 0))
        (xorAndVecStatic W cur hcur u0 (fun j ↦ sW j.succ) (fun j ↦ acc j.succ)
          (fun j ↦ hu_s j.succ) hu_lt (fun j ↦ hs_lt j.succ) (fun j ↦ ha_lt j.succ))
theorem xorAndVecStatic_countTempAnd {M : ℕ} : ∀ (W cur : ℕ) (hcur : cur + 1 ≤ M) (u0 : Wire M)
    (sW acc : Fin W → Wire M) (hu_s : ∀ j, u0 ≠ sW j) (hu_lt : u0.val < cur)
    (hs_lt : ∀ j, (sW j).val < cur) (ha_lt : ∀ j, (acc j).val < cur),
    (xorAndVecStatic W cur hcur u0 sW acc hu_s hu_lt hs_lt ha_lt).countTempAnd = W
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, _, _, _, _, _, _, _ => by
      dsimp only [xorAndVecStatic, TempPhaseProg.countTempAnd]
      rw [show (msbClearStatic cur hcur _ _ _ _ _ _ _).countTempAnd = 1 from rfl,
        xorAndVecStatic_countTempAnd W cur hcur]
      omega
theorem xorAndVecStatic_spec {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + 1 ≤ M) (u0 : Wire M) (sW acc : Fin W → Wire M)
      (hu_s : ∀ j, u0 ≠ sW j) (_hu_a : ∀ j, u0 ≠ acc j) (_hsa : ∀ i j, sW i ≠ acc j)
      (_ha_inj : Function.Injective acc)
      (hu_lt : u0.val < cur) (hs_lt : ∀ j, (sW j).val < cur) (ha_lt : ∀ j, (acc j).val < cur),
      let p := xorAndVecStatic W cur hcur u0 sW acc hu_s hu_lt hs_lt ha_lt
      ValidCleanRem M (M - cur) p ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β → p.evalSign β = 0) ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - cur) (p.evalBits β) ∧
          (∀ w : Wire M, (∀ j, w ≠ acc j) → p.evalBits β w = β w) ∧
          (∀ j : Fin W, p.evalBits β (acc j) = β (acc j) + β u0 * β (sW j)))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨trivial, fun _ _ ↦ rfl, fun β hβ ↦ ⟨hβ, fun _ _ ↦ rfl, fun j ↦ Fin.elim0 j⟩⟩
  | W + 1, cur, hcur, u0, sW, acc, hu_s, hu_a, hsa, ha_inj, hu_lt, hs_lt, ha_lt => by
      dsimp only [xorAndVecStatic]
      obtain ⟨hv0, _, hs0, hb0⟩ := msbClearStatic_spec cur hcur u0 (sW 0) (acc 0)
        (hu_s 0) (hu_a 0) (hsa 0 0) hu_lt (hs_lt 0) (ha_lt 0)
      obtain ⟨hvR, hsR, hR⟩ := xorAndVecStatic_spec W cur hcur u0 (fun j ↦ sW j.succ)
        (fun j ↦ acc j.succ) (fun j ↦ hu_s j.succ) (fun j ↦ hu_a j.succ)
        (fun i j ↦ hsa i.succ j.succ) (ha_inj.comp (Fin.succ_injective W)) hu_lt
        (fun j ↦ hs_lt j.succ) (fun j ↦ ha_lt j.succ)
      have hcl0 : ∀ β : BitAssignment M, cleanRem M (M - cur) β → cleanRem M (M - cur)
          ((msbClearStatic cur hcur u0 (sW 0) (acc 0) (hu_s 0) hu_lt (hs_lt 0) (ha_lt 0)).evalBits
            β) :=
        fun β hβ w hw ↦ by
          rw [hb0 β hβ, Function.update_of_ne (wire_ne_of_gt (by
            have := ha_lt 0
            omega))]
          exact hβ w hw
      refine ⟨⟨M - cur, by omega, hv0, hvR, hcl0⟩, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
      · dsimp only [TempPhaseProg.evalSign]
        rw [hs0 β hβ, hsR _ (hcl0 β hβ), zero_add]
      · dsimp only [TempPhaseProg.evalBits]
        obtain ⟨hclOut, hnonR, haccR⟩ := hR _ (hcl0 β hβ)
        refine ⟨hclOut, fun w hw ↦ ?_, fun j ↦ ?_⟩
        · rw [hnonR w (fun j ↦ hw j.succ), hb0 β hβ, Function.update_of_ne (hw 0)]
        · cases j using Fin.cases with
          | zero =>
              rw [hnonR (acc 0) (fun j h ↦ Fin.succ_ne_zero j (ha_inj h.symm)),
                hb0 β hβ, Function.update_self]
          | succ j =>
              rw [haccR j, hb0 β hβ, Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (ha_inj h)),
                Function.update_of_ne (hu_a 0), Function.update_of_ne (hsa j.succ 0)]
def ctxCleanMsbSub {M : ℕ} :
    (W cur : ℕ) → (hcur : cur + W ≤ M) →
    (b acc : Fin (W + 1) → Wire M) → (msb cin : Wire M) →
    (hab : ∀ j, acc j ≠ b j) → (hac : ∀ j, acc j ≠ cin) → (hbc : ∀ j, b j ≠ cin) →
    (hmc : msb ≠ cin) →
    (hb : ∀ j, (b j).val < cur) → (ha : ∀ j, (acc j).val < cur) →
    (hmsb : msb.val < cur) → (hc : cin.val < cur) →
    TempCtx M
  | 0, _, _, b, acc, msb, cin, hab, hac, hbc, hmc, _, _, _, _ =>
      let cPre0 : CliffProg M := .seq (.cnot (b 0) (acc 0) (hab 0).symm)
          (.seq (.cnot cin msb hmc.symm) (.cnot cin (b 0) (hbc 0).symm))
      let cPost0 : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      .seqPre cPre0 (.seqPost .hole cPost0)
  | W + 1, cur, hcur, b, acc, msb, cin, hab, hac, hbc, hmc, hb, ha, hmsb, hc =>
      let cout : Wire M := ⟨cur, by omega⟩
      let cPre : CliffProg M :=
        .seq (.cnot (b 0) (acc 0) (hab 0).symm) (.cnot cin (b 0) (hbc 0).symm)
      let cPost : CliffProg M :=
        .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot cin (acc 0) (hac 0).symm)
      let cCarry : CliffProg M := .cnot cin cout (wire_ne_of_lt hc)
      let KRec := ctxCleanMsbSub W (cur + 1) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) msb cout
        (fun j ↦ hab j.succ)
        (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp [cout]; omega))
        (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp [cout]; omega))
        (wire_ne_of_lt (by dsimp [cout]; omega))
        (fun j ↦ lt_trans (hb j.succ) (by omega))
        (fun j ↦ lt_trans (ha j.succ) (by omega))
        (lt_trans hmsb (by omega))
        (by dsimp [cout]; omega)
      .seqPre cPre
        (.seqPost
          (.tempAnd (acc 0) (b 0) cout (hab 0)
            (wire_ne_of_lt (ha 0)) (wire_ne_of_lt (hb 0))
            (.seqPre cCarry (.seqPost KRec cCarry)))
          cPost)
theorem ctxCleanMsbSub_countTempAnd {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M)
      (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M)
      (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (hmc : msb ≠ cin)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur)
      (hmsb : msb.val < cur) (hc : cin.val < cur),
      (ctxCleanMsbSub W cur hcur b acc msb cin hab hac hbc hmc hb ha hmsb hc).countTempAnd = W
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, b, acc, msb, cin, hab, hac, hbc, hmc, hb, ha, hmsb, hc => by
      dsimp only [ctxCleanMsbSub, TempCtx.countTempAnd]
      rw [ctxCleanMsbSub_countTempAnd W (cur + 1)]
      omega
def cleanMsbSubStatic {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M) (hab : ∀ j, acc j ≠ b j)
    (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin) (hmc : msb ≠ cin)
    (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hmsb : msb.val < cur)
    (hc : cin.val < cur) : TempPhaseProg M := (ctxCleanMsbSub W cur (by omega) b acc msb cin
    hab hac hbc hmc hb ha hmsb hc).plug (msbClearStatic (cur + W) hcur (acc (Fin.last W)) (b
    (Fin.last W)) msb (hab (Fin.last W)) (lt_of_lt_of_le (ha (Fin.last W)) (by omega))
    (lt_of_lt_of_le (hb (Fin.last W)) (by omega)) (lt_of_lt_of_le hmsb (by omega)))
theorem cleanMsbSubStatic_countTempAnd {M : ℕ} (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M) (hab : ∀ j, acc j ≠ b j)
    (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin) (hmc : msb ≠ cin)
    (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hmsb : msb.val < cur)
    (hc : cin.val < cur) : (cleanMsbSubStatic W cur hcur b acc msb cin hab hac hbc hmc hb ha
    hmsb hc).countTempAnd = W + 1 := by
  dsimp only [cleanMsbSubStatic]
  rw [TempCtx.plug_countTempAnd, ctxCleanMsbSub_countTempAnd]
  rfl
def dCleanMsbSub {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) (W cur : ℕ)
    (hcur : cur + W ≤ M) (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M)
    (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin) (hmc : msb ≠ cin)
    (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hmsb : msb.val < cur)
    (hc : cin.val < cur) : DynamicCircuit Var n := p57ToDynWith v rComb
    (DynamicCircuit.andUncompute v (rComb (acc (Fin.last W))) (rComb (b (Fin.last W))) (rComb
    msb) (rComb.wires.injective.ne (hab (Fin.last W)))) (ctxCleanMsbSub W cur hcur b acc msb
    cin hab hac hbc hmc hb ha hmsb hc)
theorem dCleanMsbSub_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (W cur : ℕ) (hcur : cur + W ≤ M) (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M)
    (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin) (hmc : msb ≠ cin)
    (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hmsb : msb.val < cur)
    (hc : cin.val < cur) : (dCleanMsbSub v rComb W cur hcur b acc msb cin hab hac hbc hmc hb
    ha hmsb hc).count PrimitiveGate.T = 4 * W := by
  dsimp only [dCleanMsbSub]
  rw [p57ToDynWith_count_t, ctxCleanMsbSub_countTempAnd, DynamicCircuit.count_andUncompute_t,
    add_zero]
theorem dCleanMsbSub_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (W cur : ℕ) (hcur : cur + W ≤ M) (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M)
    (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin) (hmc : msb ≠ cin)
    (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hmsb : msb.val < cur)
    (hc : cin.val < cur) : (dCleanMsbSub v rComb W cur hcur b acc msb cin hab hac hbc hmc hb
    ha hmsb hc).count PrimitiveGate.TOFF = 0 := p57ToDynWith_count_toff v rComb _
    (DynamicCircuit.count_andUncompute_toff v _ _ _ _) _
theorem dCleanMsbSub_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (W cur : ℕ) (hcur : cur + W ≤ M)
    (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M) (hab : ∀ j, acc j ≠ b j)
    (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin) (hmc : msb ≠ cin)
    (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hmsb : msb.val < cur)
    (hc : cin.val < cur) : PreservesStoreConst (dCleanMsbSub v rComb W cur hcur b acc msb cin
    hab hac hbc hmc hb ha hmsb hc) := p57ToDynWith_preservesStore v rComb _
    (PreservesStoreConst.andUncompute v _ _ _ _) _
theorem ctxCleanMsbSub_spec {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M)
      (hab_disj : ∀ i j, acc i ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (_ham : ∀ j, acc j ≠ msb) (_hbm : ∀ j, b j ≠ msb) (hmc : msb ≠ cin)
      (_hb_inj : Function.Injective b) (_ha_inj : Function.Injective acc)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur)
      (hmsb : msb.val < cur) (hc : cin.val < cur),
      let K := ctxCleanMsbSub W cur (by omega) b acc msb cin (fun j ↦ hab_disj j j)
        hac hbc hmc hb ha hmsb hc
      let p := cleanMsbSubStatic W cur hcur b acc msb cin (fun j ↦ hab_disj j j)
        hac hbc hmc hb ha hmsb hc
      ValidCleanRem M (M - cur) p ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β → p.evalSign β = 0 ∧
          cleanRem M (M - cur) (p.evalBits β) ∧
          (∀ w : Wire M, (∀ j, w ≠ acc j) → w ≠ msb → p.evalBits β w = β w)) ∧
        (∀ (β : BitAssignment M) (aOrig : Fin (W + 1) → ZMod 2), cleanRem M (M - cur) β →
          bitsVal (fun j ↦ β (acc j)) + 2 ^ (W + 1) * (β msb).val =
            bitsVal aOrig + bitsVal (fun j ↦ β (b j)) + (β cin).val →
          K.fwdBits β msb = K.fwdBits β (acc (Fin.last W)) * K.fwdBits β (b (Fin.last W)) ∧
            (∀ j : Fin (W + 1), p.evalBits β (acc j) = aOrig j) ∧ p.evalBits β msb = 0)
  | 0, cur, hcur, b, acc, msb, cin, hab_disj, hac, hbc, ham, hbm, hmc, _, _, hb, ha, hmsb, hc => by
      dsimp only [cleanMsbSubStatic, ctxCleanMsbSub, TempCtx.plug]
      let cPre0 : CliffProg M := .seq (.cnot (b 0) (acc 0) (hab_disj 0 0).symm)
        (.seq (.cnot cin msb hmc.symm) (.cnot cin (b 0) (hbc 0).symm))
      let cPost0 : CliffProg M := .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot cin (acc 0) (hac
        0).symm)
      have hLast0 : (Fin.last 0 : Fin 1) = 0 := rfl
      let pClr0 := msbClearStatic (cur + 0) hcur (acc (Fin.last 0)) (b (Fin.last 0)) msb
        (hab_disj (Fin.last 0) (Fin.last 0)) (lt_of_lt_of_le (ha (Fin.last 0)) (by omega))
        (lt_of_lt_of_le (hb (Fin.last 0)) (by omega)) (lt_of_lt_of_le hmsb (by omega))
      obtain ⟨hvClr, _, hsClr, hbClr⟩ := msbClearStatic_spec (cur + 0) hcur (acc (Fin.last 0))
        (b (Fin.last 0)) msb (hab_disj _ _) (ham _) (hbm _)
        (lt_of_lt_of_le (ha _) (by omega)) (lt_of_lt_of_le (hb _) (by omega))
        (lt_of_lt_of_le hmsb (by omega))
      have hPre_cl : ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - (cur + 0)) (cPre0.eval β) := fun β hβ w hw ↦
        (cPre0.eval_outside ⟨⟨hb 0, ha 0⟩, ⟨hc, hmsb⟩, ⟨hc, hb 0⟩⟩ β w (by omega)).trans
          (hβ w (by omega))
      have hPreEq : ∀ β : BitAssignment M, cPre0.eval β =
          Function.update (Function.update (Function.update β (acc 0) (β (acc 0) + β (b 0)))
            msb (β msb + β cin)) (b 0) (β (b 0) + β cin) := fun β ↦ by
        dsimp only [cPre0, CliffProg.eval]
        rw [Function.update_of_ne (ham 0).symm, Function.update_of_ne (hac 0).symm,
          Function.update_of_ne (hbm 0), Function.update_of_ne (hab_disj 0 0).symm,
          Function.update_of_ne hmc.symm, Function.update_of_ne (hac 0).symm]
      refine ⟨⟨M - (cur + 0), by omega, trivial, ⟨0, Nat.zero_le M, hvClr, trivial,
        fun _ _ _ hw ↦ absurd hw (by omega)⟩, hPre_cl⟩,
        fun β hβ ↦ ?_, fun β aOrig hβ hSum ↦ ?_⟩
      · have hNon : ∀ w : Wire M, (∀ j : Fin 1, w ≠ acc j) → w ≠ msb →
            (TempPhaseProg.seq (.cliff cPre0) (.seq pClr0 (.cliff cPost0))).evalBits β w = β w :=
          fun w hw hwm ↦ by
            dsimp only [TempPhaseProg.evalBits, cPost0, CliffProg.eval]
            rw [hbClr (cPre0.eval β) (hPre_cl β hβ), Function.update_of_ne (hw 0)]
            by_cases hwb0 : w = b 0
            · subst hwb0
              simp [hPreEq β, Function.update_of_ne (hbm 0), Function.update_of_ne hmc.symm,
                Function.update_of_ne (hbc 0).symm, Function.update_of_ne (hac 0).symm]
            · simp [hPreEq β, Function.update_of_ne hwb0, Function.update_of_ne hwm,
                Function.update_of_ne (hw 0)]
        refine ⟨?_, fun w hw ↦ (hNon w (fun j ↦
          wire_ne_of_gt (lt_of_lt_of_le (ha j) (by omega)))
          (wire_ne_of_gt (by omega))).trans (hβ w hw), hNon⟩
        dsimp only [TempPhaseProg.evalSign, TempPhaseProg.evalBits]
        rw [hsClr _ (hPre_cl β hβ)]
        rfl
      · rw [bitsVal_succ_split (fun j ↦ β (acc j)), bitsVal_succ_split aOrig,
          bitsVal_succ_split (fun j ↦ β (b j))] at hSum
        simp only [bitsVal_fin_zero, mul_zero, add_zero] at hSum
        have hfa := fullAdd_val_eq (aOrig 0) (β (b 0)) (β cin)
        have hv1 : (β (acc 0)).val < 2 := ZMod.val_lt _
        have hv2 : (aOrig 0 + β (b 0) + β cin).val < 2 := ZMod.val_lt _
        have hha : cPre0.eval β (acc 0) = aOrig 0 + β cin := by
          rw [hPreEq β, Function.update_of_ne (hab_disj 0 0), Function.update_of_ne (ham 0),
            Function.update_self,
            zmod2_eq_of_val_eq (by omega : (β (acc 0)).val = (aOrig 0 + β (b 0) + β cin).val)]
          exact zmod2_cancel_mid (aOrig 0) (β (b 0)) (β cin)
        have hHole : cPre0.eval β msb =
            cPre0.eval β (acc (Fin.last 0)) * cPre0.eval β (b (Fin.last 0)) := by
          rw [hLast0, hha, hPreEq β, Function.update_of_ne (hbm 0).symm, Function.update_self,
            Function.update_self, zmod2_eq_of_val_eq (by
              omega : (β msb).val = (β cin + (aOrig 0 + β cin) * (β (b 0) + β cin)).val)]
          exact zmod2_cancel_left_right (β cin) _
        refine ⟨hHole, fun j ↦ ?_, ?_⟩
        · obtain rfl : j = 0 := Fin.ext (by omega)
          change cPost0.eval (pClr0.evalBits (cPre0.eval β)) (acc 0) = aOrig 0
          rw [hbClr (cPre0.eval β) (hPre_cl β hβ)]
          dsimp only [cPost0, CliffProg.eval]
          rw [Function.update_self, Function.update_of_ne (hab_disj 0 0),
            Function.update_of_ne (ham 0), Function.update_of_ne (hbc 0).symm,
            Function.update_of_ne hmc.symm, hha, hPreEq β,
            Function.update_of_ne (hbc 0).symm, Function.update_of_ne hmc.symm,
            Function.update_of_ne (hac 0).symm, zmod2_add_self_cancel]
        · change cPost0.eval (pClr0.evalBits (cPre0.eval β)) msb = 0
          rw [hbClr (cPre0.eval β) (hPre_cl β hβ)]
          dsimp only [cPost0, CliffProg.eval]
          rw [Function.update_of_ne (ham 0).symm, Function.update_of_ne (hbm 0).symm,
            Function.update_self, hHole, CharTwo.add_self_eq_zero]
  | W + 1, cur, hcur, b, acc, msb, cin, hab_disj, hac, hbc, ham, hbm, hmc,
      hb_inj, ha_inj, hb, ha, hmsb, hc => by
      let cout : Wire M := ⟨cur, by omega⟩
      have hcout : cout.val = cur := rfl
      let cPre : CliffProg M := .seq (.cnot (b 0) (acc 0) (hab_disj 0 0).symm) (.cnot cin (b 0) (hbc
        0).symm)
      let cPost : CliffProg M := .seq (.cnot cin (b 0) (hbc 0).symm) (.cnot cin (acc 0) (hac
        0).symm)
      have hcurRec : (cur + 1) + W + 1 ≤ M := by omega
      have hl_fin : (Fin.last (W + 1) : Fin (W + 2)) = (Fin.last W).succ := Fin.ext (by simp
        [Fin.last])
      let KRec := ctxCleanMsbSub W (cur + 1) (by omega) (fun j ↦ b j.succ) (fun j ↦ acc j.succ)
        msb cout (fun j ↦ hab_disj j.succ j.succ) (fun j ↦ wire_ne_of_lt (ha j.succ))
        (fun j ↦ wire_ne_of_lt (hb j.succ)) (wire_ne_of_lt hmsb)
        (fun j ↦ lt_trans (hb j.succ) (by omega)) (fun j ↦ lt_trans (ha j.succ) (by omega))
        (lt_trans hmsb (by omega)) (by omega)
      let pRec := cleanMsbSubStatic W (cur + 1) hcurRec (fun j ↦ b j.succ) (fun j ↦ acc j.succ)
        msb cout (fun j ↦ hab_disj j.succ j.succ) (fun j ↦ wire_ne_of_lt (ha j.succ))
        (fun j ↦ wire_ne_of_lt (hb j.succ)) (wire_ne_of_lt hmsb)
        (fun j ↦ lt_trans (hb j.succ) (by omega)) (fun j ↦ lt_trans (ha j.succ) (by omega))
        (lt_trans hmsb (by omega)) (by omega)
      have hPlugEq : cleanMsbSubStatic (W + 1) cur hcur b acc msb cin (fun j ↦ hab_disj j j)
          hac hbc hmc hb ha hmsb hc = .seq (.cliff cPre) (.seq (.tempAnd (acc 0) (b 0) cout
          (hab_disj 0 0) (wire_ne_of_lt (ha 0)) (wire_ne_of_lt (hb 0))
          (withCliffAlloc (.cnot cin cout (wire_ne_of_lt hc)) pRec)) (.cliff cPost)) := by
        dsimp only [cleanMsbSubStatic, ctxCleanMsbSub, TempCtx.plug, withCliffAlloc,
          pRec, CliffProg.inv]
        rw [msbClearStatic_congr (by omega : cur + (W + 1) = (cur + 1) + W) hcur hcurRec
          (congrArg acc hl_fin) (congrArg b hl_fin) _ (hab_disj (Fin.last W).succ (Fin.last W).succ)
          _ (lt_of_lt_of_le (ha (Fin.last W).succ) (by omega))
          _ (lt_of_lt_of_le (hb (Fin.last W).succ) (by omega)) _ (by omega)]
      obtain ⟨hvRec, hUncondRec, hSumRec⟩ := ctxCleanMsbSub_spec W (cur + 1) hcurRec
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) msb cout (fun i j ↦ hab_disj i.succ j.succ)
        (fun j ↦ wire_ne_of_lt (ha j.succ)) (fun j ↦ wire_ne_of_lt (hb j.succ))
        (fun j ↦ ham j.succ) (fun j ↦ hbm j.succ) (wire_ne_of_lt hmsb)
        (hb_inj.comp (Fin.succ_injective (W + 1))) (ha_inj.comp (Fin.succ_injective (W + 1)))
        (fun j ↦ lt_trans (hb j.succ) (by omega)) (fun j ↦ lt_trans (ha j.succ) (by omega))
        (lt_trans hmsb (by omega)) (by omega)
      obtain ⟨hvStep, hStep⟩ := p57Slim_carryStep_spec cur (by omega) (acc 0) (b 0) cin
        (hab_disj 0 0) (ha 0) (hb 0) hc cPre cPost ⟨⟨hb 0, ha 0⟩, ⟨hc, hb 0⟩⟩ pRec
        (fun w ↦ (∃ j : Fin (W + 1), w = acc j.succ) ∨ w = msb) hvRec
        (fun γ hγ ↦ (hUncondRec γ hγ).1)
        (fun γ hγ w hnw ↦ (hUncondRec γ hγ).2.2 w
          (fun j hj ↦ hnw (.inl ⟨j, hj⟩)) fun hm ↦ hnw (.inr hm))
        (fun h ↦ h.elim (fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (ha_inj hj.symm)) (ham 0))
        (fun h ↦ h.elim (fun ⟨j, hj⟩ ↦ hab_disj j.succ 0 hj.symm) (hbm 0))
        (fun h ↦ h.elim (fun ⟨j, hj⟩ ↦ hac j.succ hj.symm) hmc.symm)
        (fun u hu h ↦ h.elim (fun ⟨j, hj⟩ ↦ wire_ne_of_gt (lt_of_lt_of_le (ha j.succ) hu) hj)
          (wire_ne_of_gt (by omega)))
      have hPreEq : ∀ β : BitAssignment M, cPre.eval β = Function.update
          (Function.update β (acc 0) (β (acc 0) + β (b 0))) (b 0) (β (b 0) + β cin) := fun β ↦ by
        dsimp only [cPre, CliffProg.eval]
        rw [Function.update_of_ne (hab_disj 0 0).symm, Function.update_of_ne (hac 0).symm]
      have hPreOth : ∀ (β : BitAssignment M) (w : Wire M),
          w ≠ acc 0 → w ≠ b 0 → cPre.eval β w = β w := fun β w h1 h2 ↦ by
        rw [hPreEq β, Function.update_of_ne h2, Function.update_of_ne h1]
      refine ⟨hPlugEq ▸ hvStep, fun β hβ ↦ ?_, fun β aOrig hβ hSum ↦ ?_⟩
      · rw [hPlugEq]
        obtain ⟨_, _, hsStep, hEv, hδ⟩ := hStep β hβ
        let δ := Function.update
          (pRec.evalBits (Function.update (cPre.eval β) cout
            ((cPre.eval β) (acc 0) * (cPre.eval β) (b 0) + (cPre.eval β) cin))) cout 0
        have hδ_nm : ∀ w : Wire M, (∀ j : Fin (W + 1), w ≠ acc j.succ) → w ≠ msb →
            δ w = cPre.eval β w := fun w hw hm ↦
          hδ w fun h ↦ h.elim (fun ⟨j, hj⟩ ↦ hw j hj) hm
        have hNon : ∀ w : Wire M, (∀ j : Fin (W + 2), w ≠ acc j) → w ≠ msb →
            cPost.eval δ w = β w := fun w hw hwm ↦ by
          dsimp [cPost, CliffProg.eval]
          rw [Function.update_of_ne (hw 0)]
          by_cases hwb0 : w = b 0
          · subst hwb0
            rw [Function.update_self, hδ_nm (b 0) (fun j ↦ (hab_disj j.succ 0).symm) (hbm 0),
              hPreEq β, Function.update_self, hδ_nm cin (fun j ↦ (hac j.succ).symm) hmc.symm,
              hPreOth β cin (hac 0).symm (hbc 0).symm, zmod2_add_self_cancel]
          · rw [Function.update_of_ne hwb0, hδ_nm w (fun j ↦ hw j.succ) hwm,
              hPreOth β w (hw 0) hwb0]
        rw [hEv]
        exact ⟨hsStep, fun w hw ↦
          (hNon w (fun j ↦ wire_ne_of_gt (lt_of_lt_of_le (ha j) (by omega)))
            (wire_ne_of_gt (by omega))).trans (hβ w hw), hNon⟩
      · rw [hPlugEq]
        rw [bitsVal_succ_split (fun j ↦ β (acc j)), bitsVal_succ_split aOrig,
          bitsVal_succ_split (fun j ↦ β (b j)),
          show 2 ^ (W + 1 + 1) * (β msb).val = 2 * (2 ^ (W + 1) * (β msb).val) by ring] at hSum
        have hfa := fullAdd_val_eq (aOrig 0) (β (b 0)) (β cin)
        have hv1 : (β (acc 0)).val < 2 := ZMod.val_lt _
        have hv2 : (aOrig 0 + β (b 0) + β cin).val < 2 := ZMod.val_lt _
        obtain ⟨hEq₃, hc₃, _, hEv, hδ⟩ := hStep β hβ
        let β₃ := Function.update (cPre.eval β) cout
          ((cPre.eval β) (acc 0) * (cPre.eval β) (b 0) + (cPre.eval β) cin)
        let δ := Function.update (pRec.evalBits β₃) cout 0
        have hPre_a0 : cPre.eval β (acc 0) = aOrig 0 + β cin := by
          rw [hPreEq β, Function.update_of_ne (hab_disj 0 0), Function.update_self,
            zmod2_eq_of_val_eq (by omega : (β (acc 0)).val = (aOrig 0 + β (b 0) + β cin).val)]
          exact zmod2_cancel_mid (aOrig 0) (β (b 0)) (β cin)
        obtain ⟨hHoleRec, hAccRec, hMsbRec⟩ := hSumRec β₃ (fun j ↦ aOrig j.succ) hc₃ (by
          rw [show (fun j : Fin (W + 1) ↦ β₃ (acc j.succ)) = fun j ↦ β (acc j.succ) from
              funext fun j ↦ (Function.update_of_ne (wire_ne_of_lt (ha j.succ)) _ _).trans
                (hPreOth β _ (fun h ↦ Fin.succ_ne_zero j (ha_inj h)) (hab_disj j.succ 0)),
            show (fun j : Fin (W + 1) ↦ β₃ (b j.succ)) = fun j ↦ β (b j.succ) from
              funext fun j ↦ (Function.update_of_ne (wire_ne_of_lt (hb j.succ)) _ _).trans
                (hPreOth β _ (hab_disj 0 j.succ).symm fun h ↦ Fin.succ_ne_zero j (hb_inj h)),
            show β₃ msb = β msb from (Function.update_of_ne (wire_ne_of_lt hmsb) _ _).trans
              (hPreOth β msb (ham 0).symm (hbm 0).symm),
            show β₃ cout = β cin + (aOrig 0 + β cin) * (β (b 0) + β cin) by
              dsimp only [β₃]
              rw [Function.update_self, hPre_a0, hPreOth β cin (hac 0).symm (hbc 0).symm,
                hPreEq β, Function.update_self, add_comm]]
          omega)
        have hFwdEq : (ctxCleanMsbSub (W + 1) cur (by omega) b acc msb cin
            (fun j ↦ hab_disj j j) hac hbc hmc hb ha hmsb hc).fwdBits β = KRec.fwdBits β₃ :=
          congrArg KRec.fwdBits hEq₃
        rw [hEv]
        refine ⟨?_, fun j ↦ ?_, ?_⟩
        · rw [hFwdEq, hl_fin]
          exact hHoleRec
        · cases j using Fin.cases with
          | zero =>
              dsimp [cPost, CliffProg.eval]
              rw [Function.update_self, Function.update_of_ne (hab_disj 0 0),
                Function.update_of_ne (hbc 0).symm,
                hδ (acc 0) (fun h ↦ h.elim (fun ⟨j, hj⟩ ↦ Fin.succ_ne_zero j (ha_inj hj.symm))
                  (ham 0)),
                hδ cin (fun h ↦ h.elim (fun ⟨j, hj⟩ ↦ (hac j.succ).symm hj) hmc.symm),
                hPre_a0, hPreOth β cin (hac 0).symm (hbc 0).symm, zmod2_add_self_cancel]
          | succ j =>
              dsimp [cPost, CliffProg.eval, δ]
              rw [Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (ha_inj h)),
                Function.update_of_ne (hab_disj j.succ 0),
                Function.update_of_ne (wire_ne_of_lt (ha j.succ))]
              exact hAccRec j
        · dsimp [cPost, CliffProg.eval, δ]
          rw [Function.update_of_ne (ham 0).symm, Function.update_of_ne (hbm 0).symm,
            Function.update_of_ne (wire_ne_of_lt hmsb)]
          exact hMsbRec
theorem dCleanMsbSub_realizes_static {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (W cur : ℕ) (hcur : cur + W + 1 ≤ M)
    (b acc : Fin (W + 1) → Wire M) (msb cin : Wire M) (hab_disj : ∀ i j, acc i ≠ b j)
    (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin) (ham : ∀ j, acc j ≠ msb)
    (hbm : ∀ j, b j ≠ msb) (hmc : msb ≠ cin) (hb_inj : Function.Injective b)
    (ha_inj : Function.Injective acc) (hb : ∀ j, (b j).val < cur)
    (ha : ∀ j, (acc j).val < cur) (hmsb : msb.val < cur) (hc : cin.val < cur) (rem : ℕ)
    (hrem : rem ≤ M) (hle : M - cur ≤ rem) (Inv : BitAssignment M → Prop) (hInv : ∀ γ :
    BitAssignment M, cleanRem M rem γ → Inv γ → ∃ A₀ : ℕ, A₀ < 2 ^ (W + 1) ∧ bitsVal (fun j ↦
    γ (acc j)) + 2 ^ (W + 1) * (γ msb).val = A₀ + bitsVal (fun j ↦ γ (b j)) + (γ cin).val) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem Inv) (dCleanMsbSub v rComb W cur
    (by omega) b acc msb cin (fun j ↦ hab_disj j j) hac hbc hmc hb ha hmsb hc)
    ((((cleanMsbSubStatic W cur hcur b acc msb cin (fun j ↦ hab_disj j j) hac hbc hmc hb ha
    hmsb hc).onRegister rComb).toToffCircuit).eval) := by
  obtain ⟨hvStatic, _, hSumSpec⟩ := ctxCleanMsbSub_spec W cur hcur b acc msb cin
    hab_disj hac hbc ham hbm hmc hb_inj ha_inj hb ha hmsb hc
  exact p57ToDynWith_realizes_inv v rComb
    (msbClearStatic (cur + W) hcur (acc (Fin.last W)) (b (Fin.last W)) msb
      (hab_disj _ _) (lt_of_lt_of_le (ha _) (by omega))
      (lt_of_lt_of_le (hb _) (by omega)) (lt_of_lt_of_le hmsb (by omega)))
    _ (fun δ ↦ δ msb = δ (acc (Fin.last W)) * δ (b (Fin.last W))) (M - (cur + W)) (by omega)
    (dMsbClear_realizes_static v rComb (cur + W) hcur (acc (Fin.last W)) (b (Fin.last W)) msb
      (hab_disj (Fin.last W) (Fin.last W)) (ham (Fin.last W)) (hbm (Fin.last W))
      (lt_of_lt_of_le (ha (Fin.last W)) (by omega)) (lt_of_lt_of_le (hb (Fin.last W)) (by omega))
      (lt_of_lt_of_le hmsb (by omega)) (M - (cur + W)) (by omega) le_rfl _ fun _ _ hi ↦ hi)
    (fun r hr ↦ by
      have hlo : M - r ≤ cur + W := hr.1
      omega)
    _ rem hrem Inv (validCleanRem_mono hle hvStatic) fun γ hcr hi ↦ by
      obtain ⟨A₀, hA₀_lt, hEq⟩ := hInv γ hcr hi
      let aOrig : Fin (W + 1) → ZMod 2 := fun j ↦ if A₀.testBit j.val then 1 else 0
      rw [← bitsVal_eq_of_testBit aOrig A₀ hA₀_lt fun _ ↦ rfl] at hEq
      exact (hSumSpec γ aOrig (cleanRem_anti hle hcr) hEq).1
attribute [local irreducible]
  msbClearStatic xorAndVecStatic ctxCleanMsbSub cleanMsbSubStatic
  dCleanMsbSub
theorem cliffInv_comp_eval {M : ℕ} :
    ∀ (c : CliffProg M) (η : BitAssignment M), c.inv.eval (c.eval η) = η
  | .nil, _ => rfl
  | .x q, η => funext fun u ↦ by
      by_cases hu : u = q
      · simp [hu, CliffProg.inv, CliffProg.eval, add_assoc, CharTwo.add_self_eq_zero]
      · simp [CliffProg.inv, CliffProg.eval, Function.update_of_ne hu]
  | .cnot c₁ t₁ hct, η => funext fun u ↦ by
      by_cases hu : u = t₁
      · simp [hu, CliffProg.inv, CliffProg.eval, Function.update_of_ne hct,
          add_assoc, CharTwo.add_self_eq_zero]
      · simp [CliffProg.inv, CliffProg.eval, Function.update_of_ne hu]
  | .seq c₁ c₂, _ => by
      dsimp [CliffProg.inv, CliffProg.eval]
      rw [cliffInv_comp_eval, cliffInv_comp_eval]
def boothRad2RowVal (S : ℕ) (u : ZMod 2) : ℕ := if u.val = 1 then 2 ^ 18 + S else 2 ^ 18 - S
theorem boothRad2RowVal_add_self (S : ℕ) (hS : S < 2 ^ 18) (u : ZMod 2) :
    boothRad2RowVal S u + S = 2 ^ 18 + 2 * u.val * S := by
  unfold boothRad2RowVal
  rcases zmod2_val_cases u with hu | hu
  · simp only [hu, show ¬ ((0 : ℕ) = 1) by decide, ↓reduceIte, mul_zero, zero_mul, add_zero]
    omega
  · simp only [hu, ↓reduceIte, mul_one]
    omega
theorem boothRad2RowVal_lt (S : ℕ) (hS : S < 2 ^ 18) (u : ZMod 2) :
    boothRad2RowVal S u < 2 ^ 19 := by
  by_cases h : u.val = 1
  · simp only [boothRad2RowVal, h, ↓reduceIte]
    omega
  · simp only [boothRad2RowVal, h, ↓reduceIte]
    omega
def boothRad2PrefixVal (S : ℕ) (uBit : Fin 38 → ZMod 2) : (m : ℕ) → (hm : m ≤ 37) → ℕ
  | 0, _ => (uBit 0).val * S
  | m + 1, _ => boothRad2PrefixVal S uBit m (by omega) +
      2 ^ m * boothRad2RowVal S (uBit ⟨m + 1, by omega⟩)
theorem boothRad2PrefixVal_closed_form (S : ℕ) (hS : S < 2 ^ 18) (uBit : Fin 38 → ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ 37),
      boothRad2PrefixVal S uBit m hm + 2 ^ m * S =
        S * (1 + bitsVal (fun k : Fin (m + 1) ↦ uBit ⟨k.val, by omega⟩)) + 2 ^ 18 * (2 ^ m - 1)
  | 0, _ => by
      dsimp only [boothRad2PrefixVal]
      rw [bitsVal_succ_split, bitsVal_fin_zero, show (⟨(0 : Fin 1).val,
        by omega⟩ : Fin 38) = 0 from rfl]
      ring
  | m + 1, hm => by
      dsimp only [boothRad2PrefixVal]
      have ih := boothRad2PrefixVal_closed_form S hS uBit m (by omega)
      have hrow := boothRad2RowVal_add_self S hS (uBit ⟨m + 1, by omega⟩)
      have hsp := bitsVal_castSucc_split (fun k : Fin (m + 2) ↦ uBit ⟨k.val, by omega⟩)
      rw [show (fun j : Fin (m + 1) ↦ (fun k : Fin (m + 2) ↦ uBit ⟨k.val, by omega⟩) j.castSucc) =
          (fun j : Fin (m + 1) ↦ uBit ⟨j.val, by omega⟩) from rfl,
        show (⟨(Fin.last (m + 1)).val, by omega⟩ : Fin 38) = ⟨m + 1, by omega⟩ from rfl] at hsp
      have hp1 : 2 ^ (m + 1) = 2 * 2 ^ m := pow_succ' 2 m
      have hcalc : (boothRad2PrefixVal S uBit m (by omega) +
            2 ^ m * boothRad2RowVal S (uBit ⟨m + 1, by omega⟩)) + 2 ^ (m + 1) * S =
          (boothRad2PrefixVal S uBit m (by omega) + 2 ^ m * S) +
            2 ^ m * (boothRad2RowVal S (uBit ⟨m + 1, by omega⟩) + S) := by
        rw [hp1]
        ring
      have hsub1 : 2 ^ 18 * (2 ^ m - 1) + 2 ^ m * 2 ^ 18 = 2 ^ 18 * (2 * 2 ^ m - 1) := by
        have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        rw [show 2 * 2 ^ m - 1 = (2 ^ m - 1) + 2 ^ m by omega]
        ring
      rw [hsp, hcalc, ih, hrow, hp1]
      calc S * (1 + bitsVal (fun j : Fin (m + 1) ↦ uBit ⟨j.val, by omega⟩)) +
              2 ^ 18 * (2 ^ m - 1) + 2 ^ m * (2 ^ 18 + 2 * (uBit ⟨m + 1, by omega⟩).val * S)
          = S * (1 + (bitsVal (fun j : Fin (m + 1) ↦ uBit ⟨j.val, by omega⟩) +
                2 * 2 ^ m * (uBit ⟨m + 1, by omega⟩).val)) +
              (2 ^ 18 * (2 ^ m - 1) + 2 ^ m * 2 ^ 18) := by ring
        _ = _ := by rw [hsub1]
theorem boothRad2PrefixVal_lt (S : ℕ) (hS : S < 2 ^ 18) (uBit : Fin 38 → ZMod 2) (m : ℕ)
    (hm : m ≤ 37) : boothRad2PrefixVal S uBit m hm < 2 ^ (m + 19) := by
  have hcf := boothRad2PrefixVal_closed_form S hS uBit m hm
  have hu_lt : bitsVal (fun k : Fin (m + 1) ↦ uBit ⟨k.val, by omega⟩) < 2 ^ (m + 1) :=
    bitsVal_lt_two_pow _
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hp1 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have hp19 : 2 ^ (m + 19) = 2 ^ 18 * 2 ^ m + 2 ^ 18 * 2 ^ m := by rw [pow_add]; ring
  rw [hp1] at hu_lt
  have hle : 1 + bitsVal (fun k : Fin (m + 1) ↦ uBit ⟨k.val, by omega⟩) ≤ 2 * 2 ^ m := by
    omega
  have hmul : S * (1 + bitsVal (fun k : Fin (m + 1) ↦ uBit ⟨k.val, by omega⟩)) ≤
      S * (2 * 2 ^ m) := Nat.mul_le_mul_left S hle
  have hsub : 2 ^ 18 * (2 ^ m - 1) + 2 ^ 18 = 2 ^ 18 * 2 ^ m := by
    have h1 : (2 ^ m - 1) + 1 = 2 ^ m := Nat.sub_add_cancel hm1
    calc 2 ^ 18 * (2 ^ m - 1) + 2 ^ 18
        = 2 ^ 18 * ((2 ^ m - 1) + 1) := by ring
      _ = 2 ^ 18 * 2 ^ m := by rw [h1]
  have hpos18 : 0 < 2 ^ 18 := by decide
  have hlt_sum : boothRad2PrefixVal S uBit m hm + 2 ^ m * S < 2 ^ (m + 19) + 2 ^ m * S :=
    calc boothRad2PrefixVal S uBit m hm + 2 ^ m * S
        = S * (1 + bitsVal (fun k : Fin (m + 1) ↦ uBit ⟨k.val, by omega⟩)) +
            2 ^ 18 * (2 ^ m - 1) := hcf
      _ ≤ S * (2 * 2 ^ m) + 2 ^ 18 * (2 ^ m - 1) := Nat.add_le_add_right hmul _
      _ < S * (2 * 2 ^ m) + (2 ^ 18 * (2 ^ m - 1) + 2 ^ 18) :=
          Nat.add_lt_add_left (Nat.lt_add_of_pos_right hpos18) _
      _ = S * (2 * 2 ^ m) + 2 ^ 18 * 2 ^ m := by rw [hsub]
      _ = (S * 2 ^ m + 2 ^ 18 * 2 ^ m) + 2 ^ m * S := by ring
      _ ≤ (2 ^ 18 * 2 ^ m + 2 ^ 18 * 2 ^ m) + 2 ^ m * S :=
          Nat.add_le_add_right
            (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hS)) _) _
      _ = 2 ^ (m + 19) + 2 ^ m * S := by rw [hp19]
  exact Nat.lt_of_add_lt_add_right hlt_sum
def p57CinW : Wire 437 := ⟨275, by decide⟩
def p57B18W : Wire 437 := ⟨276, by decide⟩
def p57Z19W : Wire 437 := ⟨277, by decide⟩
def p57B19Row : Fin 19 → Wire 437 := Fin.snoc sTrue18WDefault p57B18W
def p57B20Row : Fin 20 → Wire 437 := Fin.snoc p57B19Row p57Z19W
theorem p57Slim_snoc_forall {n : ℕ} (P : Wire 437 → Prop) {f : Fin n → Wire 437}
    {x : Wire 437} (hf : ∀ i, P (f i)) (hx : P x) (j : Fin (n + 1)) :
    P (Fin.snoc (α := fun _ ↦ Wire 437) f x j) :=
  Fin.lastCases (by simpa only [Fin.snoc_last] using hx)
    (fun i ↦ by simpa only [Fin.snoc_castSucc] using hf i) j
theorem p57B19Row_lt_278 (j : Fin 19) : (p57B19Row j).val < 278 :=
  p57Slim_snoc_forall (fun w ↦ w.val < 278)
    (fun i ↦ lt_trans (validSTrueMap_default.2.1 i) (by decide)) (by decide) j
theorem p57B20Row_lt_278 (j : Fin 20) : (p57B20Row j).val < 278 :=
  p57Slim_snoc_forall (fun w ↦ w.val < 278) p57B19Row_lt_278 (by decide) j
theorem p57Slim_snoc_injective {n : ℕ} {f : Fin n → Wire 437} {x : Wire 437}
    (hf : Function.Injective f) (hne : ∀ i, f i ≠ x) : Function.Injective (Fin.snoc f x) := by
  intro i j h
  cases i using Fin.lastCases with
  | cast i' =>
      cases j using Fin.lastCases with
      | cast j' =>
          simp only [Fin.snoc_castSucc] at h
          exact congrArg Fin.castSucc (hf h)
      | last =>
          simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
          exact absurd h (hne i')
  | last =>
      cases j using Fin.lastCases with
      | cast j' =>
          simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
          exact absurd h.symm (hne j')
      | last => rfl
theorem p57B19Row_injective : Function.Injective p57B19Row :=
  p57Slim_snoc_injective validSTrueMap_default.1 fun i ↦
    wire_ne_of_lt (lt_trans (validSTrueMap_default.2.1 i) (by decide))
theorem p57B20Row_injective : Function.Injective p57B20Row :=
  p57Slim_snoc_injective p57B19Row_injective
    (p57Slim_snoc_forall (fun w ↦ w ≠ p57Z19W)
      (fun k ↦ wire_ne_of_lt (lt_trans (validSTrueMap_default.2.1 k) (by decide))) (by decide))
theorem p57OutW_lt_275 (k : Fin 57) : (p57OutW k).val < 275 := by
  dsimp [p57OutW]
  omega
theorem p57OutW_ne_b19Row (k : Fin 57) (j : Fin 19) : p57OutW k ≠ p57B19Row j :=
  p57Slim_snoc_forall (fun w ↦ p57OutW k ≠ w)
    (fun j' ↦ (validSTrueMap_default.2.2.2.2.2.2.1 j' k).symm)
    (wire_ne_of_lt (lt_trans (p57OutW_lt_275 k) (by decide))) j
theorem p57OutW_ne_b20Row (k : Fin 57) (j : Fin 20) : p57OutW k ≠ p57B20Row j :=
  p57Slim_snoc_forall (fun w ↦ p57OutW k ≠ w) (p57OutW_ne_b19Row k)
    (wire_ne_of_lt (lt_trans (p57OutW_lt_275 k) (by decide))) j
theorem p57B19Row_ne_cin (j : Fin 19) : p57B19Row j ≠ p57CinW :=
  p57Slim_snoc_forall (fun w ↦ w ≠ p57CinW)
    (fun j' ↦ wire_ne_of_lt (validSTrueMap_default.2.1 j')) (by decide) j
theorem p57B20Row_ne_cin (j : Fin 20) : p57B20Row j ≠ p57CinW :=
  p57Slim_snoc_forall (fun w ↦ w ≠ p57CinW) p57B19Row_ne_cin (by decide) j
def cBoothRowSetup (m : ℕ) (hm : m < 37) : CliffProg 437 :=
  let um1 := p57U38W ⟨m + 1, by omega⟩
  .seq (.cnot um1 p57B18W (wire_ne_val (by
    dsimp [um1, p57U38W, p57B18W]; split_ifs <;> (dsimp; omega))))
    (.seq (.x p57CinW)
      (.seq (.cnot um1 p57CinW (wire_ne_val (by
        dsimp [um1, p57U38W, p57CinW]; split_ifs <;> (dsimp; omega))))
        (fanoutCnot 18 p57CinW sTrue18WDefault
          (fun j ↦ wire_ne_of_gt (validSTrueMap_default.2.1 j)))))
theorem cBoothRowSetup_supportsBelow (m : ℕ) (hm : m < 37) :
    (cBoothRowSetup m hm).SupportsBelow (437 - (437 - 278)) := by
  change (cBoothRowSetup m hm).SupportsBelow 278
  have hum1 : (p57U38W ⟨m + 1, by omega⟩).val < 278 := by
    dsimp [p57U38W]; split_ifs <;> (dsimp; omega)
  have hcin : p57CinW.val < 278 := by dsimp [p57CinW]; omega
  have hb18 : p57B18W.val < 278 := by dsimp [p57B18W]; omega
  exact ⟨⟨hum1, hb18⟩, hcin, ⟨hum1, hcin⟩, fanoutCnot_supportsBelow 18 p57CinW sTrue18WDefault
    _ hcin (fun j ↦ lt_trans (validSTrueMap_default.2.1 j) (by decide))⟩
theorem cBoothRowSetup_disjoint_out (m : ℕ) (hm : m < 37) :
    CliffDisjoint (fun w ↦ ∃ k : Fin 57, w = p57OutW k) (cBoothRowSetup m hm) := by
  have hnu : ¬ ∃ k : Fin 57, p57U38W ⟨m + 1, by omega⟩ = p57OutW k := by
    rintro ⟨k, hk⟩
    have hv := congrArg Fin.val hk
    dsimp [p57U38W, p57OutW] at hv
    split_ifs at hv <;> (dsimp at hv; omega)
  have hncin : ¬ ∃ k : Fin 57, p57CinW = p57OutW k := by
    rintro ⟨k, hk⟩; have := p57OutW_lt_275 k; rw [← hk] at this; revert this; decide
  have hnb18 : ¬ ∃ k : Fin 57, p57B18W = p57OutW k := by
    rintro ⟨k, hk⟩; have := p57OutW_lt_275 k; rw [← hk] at this; revert this; decide
  have hns : ∀ j : Fin 18, ¬ ∃ k : Fin 57, sTrue18WDefault j = p57OutW k := by
    rintro j ⟨k, hk⟩; exact validSTrueMap_default.2.2.2.2.2.2.1 j k hk
  exact ⟨⟨hnu, hnb18⟩, hncin, ⟨hnu, hncin⟩,
    fanoutCnot_disjoint 18 p57CinW sTrue18WDefault _ hncin hns⟩
theorem cBoothRowSetup_val (m : ℕ) (hm : m < 37) (β : BitAssignment 437)
    (hβ : cleanRem 437 (437 - 275) β) :
    let γ := (cBoothRowSetup m hm).eval β
    γ p57Z19W = 0 ∧
      bitsVal (fun j ↦ γ (p57B19Row j)) + (γ p57CinW).val =
        boothRad2RowVal (bitsVal (fun j ↦ β (sTrue18WDefault j)))
          (β (p57U38W ⟨m + 1, by omega⟩)) ∧
      bitsVal (fun j ↦ γ (p57B20Row j)) + (γ p57CinW).val =
        boothRad2RowVal (bitsVal (fun j ↦ β (sTrue18WDefault j)))
          (β (p57U38W ⟨m + 1, by omega⟩)) := by
  intro γ
  let um1 := p57U38W ⟨m + 1, by omega⟩
  have hum_lt : (p57U38W ⟨m + 1, by omega⟩).val < 200 := by
    dsimp [p57U38W]
    split_ifs
    · dsimp
      omega
    · dsimp
      omega
  have hne_uc : p57U38W ⟨m + 1, by omega⟩ ≠ p57CinW := wire_ne_of_lt (lt_trans hum_lt (by decide))
  have hne_ub : p57U38W ⟨m + 1, by omega⟩ ≠ p57B18W := wire_ne_of_lt (lt_trans hum_lt (by decide))
  have hns_ge : ∀ w : Wire 437, 275 ≤ w.val → ¬ ∃ j : Fin 18, w = sTrue18WDefault j :=
    fun w hw ⟨j, hj⟩ ↦ absurd (hj ▸ validSTrueMap_default.2.1 j) (by omega)
  have hγ_eq : ∀ w : Wire 437, γ w =
      let δ := Function.update
        (Function.update (Function.update β p57B18W (β p57B18W + β um1)) p57CinW
          (β p57CinW + 1)) p57CinW ((β p57CinW + 1) + β um1)
      if ∃ j : Fin 18, w = sTrue18WDefault j then δ w + δ p57CinW else δ w := fun w ↦ by
    dsimp [γ, cBoothRowSetup, CliffProg.eval, um1]
    rw [fanoutCnot_eval 18 p57CinW sTrue18WDefault _ validSTrueMap_default.1]
    simp [Function.update_of_ne (by decide : p57CinW ≠ p57B18W), Function.update_of_ne hne_uc,
      Function.update_of_ne hne_ub]
  have hz_γ : γ p57Z19W = 0 := by
    simp [hγ_eq, hns_ge p57Z19W (by decide), Function.update_of_ne (by decide : p57Z19W ≠ p57CinW),
      Function.update_of_ne (by decide : p57Z19W ≠ p57B18W), hβ p57Z19W (by decide)]
  have hcin_γ : γ p57CinW = 1 + β um1 := by
    simp [hγ_eq, hns_ge p57CinW (by decide), hβ p57CinW (by decide)]
  have hb18_γ : γ p57B18W = β um1 := by
    simp [hγ_eq, hns_ge p57B18W (by decide), Function.update_of_ne (by decide : p57B18W ≠ p57CinW),
      hβ p57B18W (by decide)]
  have hs_γ : ∀ j : Fin 18, γ (sTrue18WDefault j) = β (sTrue18WDefault j) + (1 + β um1) :=
    fun j ↦ by
      have hne1 : sTrue18WDefault j ≠ p57CinW := wire_ne_of_lt (validSTrueMap_default.2.1 j)
      have hne2 : sTrue18WDefault j ≠ p57B18W :=
        wire_ne_of_lt (lt_trans (validSTrueMap_default.2.1 j) (by decide))
      simp [hγ_eq, show ∃ i : Fin 18, sTrue18WDefault j = sTrue18WDefault i from ⟨j, rfl⟩,
        Function.update_of_ne hne1, Function.update_of_ne hne2, hβ p57CinW (by decide)]
  have hB19 : bitsVal (fun j ↦ γ (p57B19Row j)) + (γ p57CinW).val =
      boothRad2RowVal (bitsVal (fun j ↦ β (sTrue18WDefault j))) (β um1) := by
    rw [bitsVal_castSucc_split (fun j ↦ γ (p57B19Row j)),
      show (fun j : Fin 18 ↦ γ (p57B19Row j.castSucc)) =
        (fun j : Fin 18 ↦ β (sTrue18WDefault j) + (1 + β um1)) from
        funext fun j ↦ (congrArg γ (Fin.snoc_castSucc _ _ _)).trans (hs_γ j),
      show γ (p57B19Row (Fin.last 18)) = β um1 from
        (congrArg γ (Fin.snoc_last _ _)).trans hb18_γ, hcin_γ]
    unfold boothRad2RowVal
    have hflip := bitsVal_flip_all 18 (fun j ↦ β (sTrue18WDefault j))
    have hS_lt : bitsVal (fun j ↦ β (sTrue18WDefault j)) < 2 ^ 18 := bitsVal_lt_two_pow _
    rcases bit_cases (β um1) with hu | hu
    · simp only [hu, show (1 : ZMod 2) + 0 = 1 from rfl, show ¬ ((0 : ℕ) = 1) by decide,
        ZMod.val_zero, ZMod.val_one, mul_zero, add_zero, ↓reduceIte]
      omega
    · simp only [hu, show (1 : ZMod 2) + 1 = 0 by decide, add_zero,
        ZMod.val_zero, ZMod.val_one, mul_one, ↓reduceIte]
      omega
  refine ⟨hz_γ, hB19, ?_⟩
  rw [bitsVal_castSucc_split (fun j ↦ γ (p57B20Row j)),
    show (fun j : Fin 19 ↦ γ (p57B20Row j.castSucc)) = (fun j ↦ γ (p57B19Row j)) from
      funext fun j ↦ congrArg γ (Fin.snoc_castSucc _ _ _),
    show γ (p57B20Row (Fin.last 19)) = 0 from (congrArg γ (Fin.snoc_last _ _)).trans hz_γ]
  simpa using hB19
attribute [local irreducible] cBoothRowSetup
end P57CleanMsbBooth
section P57JointSTrue18
set_option maxRecDepth 2000
open HermitianMat MeasureBranchHadamardSem
open BchCubeDecoder StreamingBchComparator
def isSTrueNat (q : ℕ) : Bool :=
  ((199 ≤ q) && (q < 201)) || ((259 ≤ q) && (q < 275))
def mutSTrue (w : Wire 437) : Prop := ∃ j : Fin 18, w = sTrue18WDefault j
theorem not_mutSTrue_of_false {w : Wire 437} (h : isSTrueNat w.val = false) : ¬ mutSTrue w := by
  rintro ⟨j, rfl⟩
  revert h; revert j; decide
inductive P57Step : Type
  | x (q : ℕ)
  | cnot (c t : ℕ)
  | tempAnd (a b dst : ℕ)
def stepToSingleCtx : P57Step → TempCtx 437
  | .x q => if hq : q < 437 then ctxCliffAlloc (.x ⟨q, hq⟩) else .hole
  | .cnot c t => if h : c < 437 ∧ t < 437 ∧ c ≠ t then
      ctxCliffAlloc (.cnot ⟨c, h.1⟩ ⟨t, h.2.1⟩ (wire_ne_val h.2.2)) else .hole
  | .tempAnd a b dst =>
      if h : a < 437 ∧ b < 437 ∧ dst < 437 ∧ a ≠ b ∧ a ≠ dst ∧ b ≠ dst then
        ctxTempBit ⟨a, h.1⟩ ⟨b, h.2.1⟩ ⟨dst, h.2.2.1⟩
          (wire_ne_val h.2.2.2.1) (wire_ne_val h.2.2.2.2.1) (wire_ne_val h.2.2.2.2.2)
      else .hole
def buildP57Ctx : List P57Step → TempCtx 437
  | [] => .hole
  | s :: ss => (stepToSingleCtx s).append (buildP57Ctx ss)
def evalP57Step : P57Step → BitAssignment 437 → BitAssignment 437
  | .x q, β => if hq : q < 437 then Function.update β ⟨q, hq⟩ (β ⟨q, hq⟩ + 1) else β
  | .cnot c t, β => if h : c < 437 ∧ t < 437 ∧ c ≠ t then
      Function.update β ⟨t, h.2.1⟩ (β ⟨t, h.2.1⟩ + β ⟨c, h.1⟩) else β
  | .tempAnd a b dst, β =>
      if h : a < 437 ∧ b < 437 ∧ dst < 437 ∧ a ≠ b ∧ a ≠ dst ∧ b ≠ dst then
        Function.update β ⟨dst, h.2.2.1⟩ (β ⟨dst, h.2.2.1⟩ + β ⟨a, h.1⟩ * β ⟨b, h.2.1⟩)
      else β
def evalP57Steps : List P57Step → BitAssignment 437 → BitAssignment 437
  | [], β => β
  | s :: ss, β => evalP57Steps ss (evalP57Step s β)
theorem stepToSingleCtx_fwdBits (s : P57Step) (β : BitAssignment 437) :
    (stepToSingleCtx s).fwdBits β = evalP57Step s β := by
  cases s <;> dsimp [stepToSingleCtx, evalP57Step] <;> split_ifs <;> rfl
theorem buildP57Ctx_fwdBits : ∀ (ss : List P57Step) (β : BitAssignment 437),
    (buildP57Ctx ss).fwdBits β = evalP57Steps ss β
  | [], _ => rfl
  | s :: ss, β => by
      dsimp only [buildP57Ctx, evalP57Steps]
      rw [TempCtx.append_fwdBits, stepToSingleCtx_fwdBits, buildP57Ctx_fwdBits ss]
theorem TempCtx.countTempAnd_append {M : ℕ} (F G : TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd :=
  Slot3MicroEngineAux.TempCtx.append_countTempAnd F G
structure P57CtxPkg (cur curEnd cnt : ℕ) (K : TempCtx 437) : Prop where
  le_end : cur ≤ curEnd
  end_le : curEnd ≤ 437
  cnt_eq : K.countTempAnd = cnt
  disj : K.DisjointFrom mutSTrue
  supp : K.SupportsBelowCtx curEnd
  lift : TempCtxLiftEx cur curEnd K
  clean : ∀ β : BitAssignment 437,
    cleanRem 437 (437 - cur) β → cleanRem 437 (437 - curEnd) (K.fwdBits β)
theorem P57CtxPkg.append {c₀ c₁ c₂ n₁ n₂ : ℕ} {F G : TempCtx 437}
    (hF : P57CtxPkg c₀ c₁ n₁ F) (hG : P57CtxPkg c₁ c₂ n₂ G) :
    P57CtxPkg c₀ c₂ (n₁ + n₂) (F.append G) :=
  ⟨le_trans hF.le_end hG.le_end, hG.end_le,
    by rw [TempCtx.countTempAnd_append, hF.cnt_eq, hG.cnt_eq],
    TempCtx.disjointFrom_append hF.disj hG.disj,
    TempCtx.supportsBelowCtx_append hG.le_end hF.supp hG.supp,
    TempCtxLiftEx.append hF.lift hG.lift,
    fun β hβ ↦ TempCtx.append_fwdBits F G β ▸ hG.clean _ (hF.clean β hβ)⟩
def wfP57Step (cur : ℕ) : P57Step → Option (ℕ × ℕ)
  | .x q => if (q < cur) && (cur ≤ 437) && !isSTrueNat q then some (cur, 0) else none
  | .cnot c t => if (c < cur) && (t < cur) && (cur ≤ 437) && (c != t) &&
      !isSTrueNat c && !isSTrueNat t then some (cur, 0) else none
  | .tempAnd a b dst => if (a < cur) && (b < cur) && (dst == cur) && (cur + 1 ≤ 437) &&
      (a != b) && !isSTrueNat a && !isSTrueNat b && !isSTrueNat dst then
      some (cur + 1, 1) else none
def wfP57Steps : ℕ → List P57Step → Option (ℕ × ℕ)
  | cur, [] => if cur ≤ 437 then some (cur, 0) else none
  | cur, s :: ss => match wfP57Step cur s with
    | none => none
    | some (cur1, c1) => match wfP57Steps cur1 ss with
      | none => none
      | some (cur2, c2) => some (cur2, c1 + c2)
theorem stepToSingleCtx_pkg {cur cur1 c1 : ℕ} {s : P57Step}
    (h : wfP57Step cur s = some (cur1, c1)) : P57CtxPkg cur cur1 c1 (stepToSingleCtx s) := by
  cases s with
  | x q =>
      dsimp [wfP57Step] at h
      split_ifs at h with hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      obtain ⟨⟨hq_cur, hcur_le⟩, hnq⟩ := hc
      have hq437 : q < 437 := lt_of_lt_of_le hq_cur hcur_le
      dsimp only [stepToSingleCtx]
      rw [dite_eq_left hq437]
      exact ⟨le_rfl, hcur_le, rfl, ctxCliffAlloc_disjoint (not_mutSTrue_of_false hnq),
        ctxCliffAlloc_supports hq_cur, TempCtxLiftEx.cliff hcur_le (.x ⟨q, hq437⟩) hq_cur,
        fun β hβ w hw ↦
          (Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le hq_cur (by omega))) _ _).trans
            (hβ w hw)⟩
  | cnot c t =>
      dsimp [wfP57Step] at h
      split_ifs at h with hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨hc_cur, ht_cur⟩, hcur_le⟩, hne⟩, hnc⟩, hnt⟩ := hc
      have hcond : c < 437 ∧ t < 437 ∧ c ≠ t :=
        ⟨lt_of_lt_of_le hc_cur hcur_le, lt_of_lt_of_le ht_cur hcur_le, hne⟩
      dsimp only [stepToSingleCtx]
      rw [dite_eq_left hcond]
      exact ⟨le_rfl, hcur_le, rfl,
        ctxCliffAlloc_disjoint ⟨not_mutSTrue_of_false hnc, not_mutSTrue_of_false hnt⟩,
        ctxCliffAlloc_supports ⟨hc_cur, ht_cur⟩,
        TempCtxLiftEx.cliff hcur_le (.cnot ⟨c, hcond.1⟩ ⟨t, hcond.2.1⟩ (wire_ne_val hne))
          ⟨hc_cur, ht_cur⟩,
        fun β hβ w hw ↦
          (Function.update_of_ne (wire_ne_of_gt (lt_of_lt_of_le ht_cur (by omega))) _ _).trans
            (hβ w hw)⟩
  | tempAnd a b dst =>
      dsimp [wfP57Step] at h
      split_ifs at h with hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, beq_iff_eq,
        decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨ha_cur, hb_cur⟩, rfl⟩, hcur_le⟩, hab⟩, hna⟩, hnb⟩, hnd⟩ := hc
      have hcond : a < 437 ∧ b < 437 ∧ dst < 437 ∧ a ≠ b ∧ a ≠ dst ∧ b ≠ dst :=
        ⟨by omega, by omega, by omega, hab, by omega, by omega⟩
      dsimp only [stepToSingleCtx]
      rw [dite_eq_left hcond]
      exact ⟨by omega, hcur_le, rfl,
        ⟨not_mutSTrue_of_false hna, not_mutSTrue_of_false hnb, not_mutSTrue_of_false hnd, trivial⟩,
        ⟨Nat.lt_succ_self dst, trivial⟩,
        TempCtxLiftEx.tempBit hcur_le ⟨a, hcond.1⟩ ⟨b, hcond.2.1⟩ (wire_ne_val hab) ha_cur hb_cur,
        fun β hβ w hw ↦
          (Function.update_of_ne (wire_ne_of_gt (show dst < w.val by omega)) _ _).trans
            (hβ w (by omega))⟩
theorem buildP57Ctx_pkg :
    ∀ {ss : List P57Step} {cur curEnd cnt : ℕ},
      wfP57Steps cur ss = some (curEnd, cnt) →
      P57CtxPkg cur curEnd cnt (buildP57Ctx ss)
  | [], cur, curEnd, cnt, h => by
      dsimp [wfP57Steps] at h
      split_ifs at h with hle
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
      exact ⟨le_rfl, hle, rfl, trivial, trivial, fun hb ↦ ⟨_, hb⟩, fun _ hβ ↦ hβ⟩
  | s :: ss, cur, curEnd, cnt, h => by
      dsimp [wfP57Steps] at h
      rcases hs : wfP57Step cur s with _ | ⟨cur1, c1⟩
      · simp [hs] at h
      · rw [hs] at h
        dsimp only at h
        rcases hss : wfP57Steps cur1 ss with _ | ⟨cur2, c2⟩
        · simp [hss] at h
        · rw [hss] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h).symm
          exact (stepToSingleCtx_pkg hs).append (buildP57Ctx_pkg hss)
def wrap7HeadW (p7 pb7 sw ww : Wire 437) : List P57Step :=
  [.x p7.val, .cnot sw.val p7.val, .cnot sw.val pb7.val, .tempAnd p7.val pb7.val ww.val,
   .cnot sw.val pb7.val, .cnot sw.val p7.val, .x p7.val]
def wrap7TailW (ww : Wire 437) (mw : Fin 7 → Wire 437) : List P57Step := [.cnot ww.val (mw
    0).val, .cnot ww.val (mw 1).val, .cnot ww.val (mw 2).val, .cnot ww.val (mw 3).val, .cnot
    ww.val (mw 4).val, .cnot ww.val (mw 5).val, .cnot ww.val (mw 6).val]
def axisWrapSteps (w : Fin 3) : List P57Step :=
  wrap7HeadW (p57ProjW w ⟨7, by decide⟩) (p57PBufW w ⟨7, by decide⟩)
      (p57S3W w) ⟨275 + w.val, by omega⟩ ++
    wrap7TailW ⟨275 + w.val, by omega⟩ (p57MW w)
def d8Wire (w : Fin 3) : Fin 8 → Wire 437 :=
  Fin.snoc (p57MW w) ⟨275 + w.val, by omega⟩
theorem evalP57Step_x (q : Wire 437) (δ : BitAssignment 437) :
    evalP57Step (.x q.val) δ = Function.update δ q (δ q + 1) := by
  simp [evalP57Step, q.isLt]
theorem evalP57Step_cnot {c t : Wire 437} (h : c ≠ t) (δ : BitAssignment 437) :
    evalP57Step (.cnot c.val t.val) δ = Function.update δ t (δ t + δ c) := by
  simp [evalP57Step, c.isLt, t.isLt, Fin.val_ne_of_ne h]
theorem evalP57Step_tempAnd {a b dst : Wire 437} (hab : a ≠ b) (had : a ≠ dst) (hbd : b ≠ dst)
    (δ : BitAssignment 437) :
    evalP57Step (.tempAnd a.val b.val dst.val) δ =
      Function.update δ dst (δ dst + δ a * δ b) := by
  simp [evalP57Step, a.isLt, b.isLt, dst.isLt,
    Fin.val_ne_of_ne hab, Fin.val_ne_of_ne had, Fin.val_ne_of_ne hbd]
theorem evalP57Steps_append : ∀ (xs ys : List P57Step) (δ : BitAssignment 437),
    evalP57Steps (xs ++ ys) δ = evalP57Steps ys (evalP57Steps xs δ)
  | [], _, _ => rfl
  | _ :: xs, ys, _ => evalP57Steps_append xs ys _
theorem zmod2_wrap_head_id (p pb s : ZMod 2) : (((p + 1 + s) + s) + 1 = p) ∧
    ((pb + s) + s = pb) ∧ ((0 : ZMod 2) + (p + 1 + s) * (pb + s) = wWrapFromPBufZMod p pb s) := by
  revert p pb s
  decide
theorem wrap7HeadW_eval (w : Fin 3) (γ : BitAssignment 437)
    (hww0 : γ ⟨275 + w.val, by omega⟩ = 0) :
    let p7 := p57ProjW w ⟨7, by decide⟩
    let pb7 := p57PBufW w ⟨7, by decide⟩
    let sw := p57S3W w
    let ww : Wire 437 := ⟨275 + w.val, by omega⟩
    evalP57Steps (wrap7HeadW p7 pb7 sw ww) γ =
      Function.update γ ww (wWrapFromPBufZMod (γ p7) (γ pb7) (γ sw)) := by
  intro p7 pb7 sw ww
  obtain ⟨h_sp, h_spb, h_ppb, h_pw, h_pbw, h_sw⟩ :
      sw ≠ p7 ∧ sw ≠ pb7 ∧ p7 ≠ pb7 ∧ p7 ≠ ww ∧ pb7 ≠ ww ∧ sw ≠ ww := by
    dsimp only [sw, p7, pb7, ww]
    clear γ hww0
    revert w
    decide
  dsimp only [wrap7HeadW, evalP57Steps]
  rw [evalP57Step_x, evalP57Step_cnot h_sp, evalP57Step_cnot h_spb,
    evalP57Step_tempAnd h_ppb h_pw h_pbw,
    evalP57Step_cnot h_spb, evalP57Step_cnot h_sp, evalP57Step_x]
  obtain ⟨hid1, hid2, hid3⟩ := zmod2_wrap_head_id (γ p7) (γ pb7) (γ sw)
  funext u
  by_cases hu1 : u = p7
  · subst hu1
    simp [h_sp, h_spb, h_ppb, h_ppb.symm,
      h_pw, h_pw.symm, h_pbw, h_pbw.symm, h_sw]
  · by_cases hu2 : u = pb7
    · subst hu2
      simp [h_sp, h_spb, h_ppb, h_ppb.symm,
        h_pw, h_pw.symm, h_pbw, h_pbw.symm, h_sw, hid2]
    · by_cases hu3 : u = ww
      · subst hu3
        simp [h_sp, h_spb, h_ppb, h_ppb.symm,
          h_pw, h_pw.symm, h_pbw, h_pbw.symm, h_sw, show γ ww = 0 from hww0, hid3]
      · simp [hu1, hu2, hu3]
theorem wrap7TailW_eval (w : Fin 3) (δ : BitAssignment 437) :
    let ww : Wire 437 := ⟨275 + w.val, by omega⟩
    let mw := p57MW w
    ∀ u : Wire 437,
      evalP57Steps (wrap7TailW ww mw) δ u =
        if ∃ b : Fin 7, u = mw b then δ u + δ ww else δ u := by
  intro ww mw u
  have hwm : ∀ b : Fin 7, ww ≠ mw b := fun b ↦
    wire_ne_val (by dsimp [ww, mw, p57MW]; omega)
  dsimp only [wrap7TailW, evalP57Steps]
  rw [evalP57Step_cnot (hwm 0), evalP57Step_cnot (hwm 1), evalP57Step_cnot (hwm 2),
    evalP57Step_cnot (hwm 3), evalP57Step_cnot (hwm 4), evalP57Step_cnot (hwm 5),
    evalP57Step_cnot (hwm 6)]
  by_cases hex : ∃ b : Fin 7, u = mw b
  · simp only [hex, ↓reduceIte]
    obtain ⟨b, rfl⟩ := hex
    fin_cases w <;> fin_cases b <;>
      simp [mw, ww, p57MW, Fin.ext_iff]
  · simp only [hex, ↓reduceIte]
    have hnu : ∀ b : Fin 7, u ≠ mw b := fun b hb ↦ hex ⟨b, hb⟩
    simp [Function.update_of_ne (hnu 0), Function.update_of_ne (hnu 1),
      Function.update_of_ne (hnu 2), Function.update_of_ne (hnu 3),
      Function.update_of_ne (hnu 4), Function.update_of_ne (hnu 5),
      Function.update_of_ne (hnu 6)]
def K_wrap0 : TempCtx 437 := buildP57Ctx (axisWrapSteps 0)
def K_wrap1 : TempCtx 437 := buildP57Ctx (axisWrapSteps 1)
def K_wrap2 : TempCtx 437 := buildP57Ctx (axisWrapSteps 2)
def K_wrap : TempCtx 437 := K_wrap0.append (K_wrap1.append K_wrap2)
theorem K_wrap_pkg : P57CtxPkg 275 278 3 K_wrap :=
  (buildP57Ctx_pkg (by decide : wfP57Steps 275 (axisWrapSteps 0) = some (276,1))).append
    ((buildP57Ctx_pkg (by decide : wfP57Steps 276 (axisWrapSteps 1) = some (277,1))).append
      (buildP57Ctx_pkg (by decide : wfP57Steps 277 (axisWrapSteps 2) = some (278,1))))
theorem axisWrap_fwdBits (w : Fin 3) (γ : BitAssignment 437)
    (hww0 : γ ⟨275 + w.val, by omega⟩ = 0) (u : Wire 437) :
    let z := wWrapFromPBufZMod
      (γ (p57ProjW w ⟨7, by decide⟩)) (γ (p57PBufW w ⟨7, by decide⟩)) (γ (p57S3W w))
    (buildP57Ctx (axisWrapSteps w)).fwdBits γ u =
      if u = ⟨275 + w.val, by omega⟩ then z
      else if ∃ b : Fin 7, u = p57MW w b then γ u + z
      else γ u := by
  intro z
  rw [buildP57Ctx_fwdBits, axisWrapSteps, evalP57Steps_append, wrap7HeadW_eval w γ hww0,
    wrap7TailW_eval w]
  by_cases huw : u = ⟨275 + w.val, by omega⟩
  · subst huw
    have hnm : ¬ ∃ b : Fin 7, (⟨275 + w.val, by omega⟩ : Wire 437) = p57MW w b := by
      rintro ⟨b, hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega
    rw [ite_eq_left rfl, ite_eq_right hnm, Function.update_self]
  · rw [ite_eq_right huw]
    by_cases hex : ∃ b : Fin 7, u = p57MW w b
    · rw [ite_eq_left hex, ite_eq_left hex, Function.update_of_ne huw, Function.update_self]
    · rw [ite_eq_right hex, ite_eq_right hex, Function.update_of_ne huw]
theorem K_wrap_spec (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β) :
    cleanRem 437 (437 - 278) (K_wrap.fwdBits β) ∧
      ∀ w : Fin 3,
        bitsVal (fun k : Fin 8 ↦ K_wrap.fwdBits β (d8Wire w k)) =
          axisCmpDMagPBuf
            (β (p57ProjW w ⟨7, by decide⟩))
            (β (p57PBufW w ⟨7, by decide⟩))
            (β (p57S3W w))
            (bitsVal (fun b : Fin 7 ↦ β (p57MW w b))) := by
  refine ⟨K_wrap_pkg.clean β hβ, fun w ↦ ?_⟩
  let βa := K_wrap0.fwdBits β
  let βb := K_wrap1.fwdBits βa
  let βc := K_wrap2.fwdBits βb
  have hKw : K_wrap.fwdBits β = βc := by
    dsimp [K_wrap, βc, βb, βa]
    rw [TempCtx.append_fwdBits, TempCtx.append_fwdBits]
  rw [hKw]
  have ha0 : β ⟨275, by decide⟩ = 0 := hβ ⟨275, by decide⟩ (by decide)
  have hb0 : βa ⟨276, by decide⟩ = 0 := by
    dsimp [βa, K_wrap0]
    rw [axisWrap_fwdBits 0 β ha0]
    have h2 : ¬ ∃ b : Fin 7, (276 : Wire 437) = p57MW 0 b := by
      rintro ⟨b, hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega
    rw [ite_eq_right (by decide), ite_eq_right h2]
    exact hβ ⟨276, by decide⟩ (by decide)
  have hc0 : βb ⟨277, by decide⟩ = 0 := by
    dsimp [βb, K_wrap1]
    rw [axisWrap_fwdBits 1 βa hb0]
    have h2 : ¬ ∃ b : Fin 7, (277 : Wire 437) = p57MW 1 b := by
      rintro ⟨b, hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega
    rw [ite_eq_right (by decide), ite_eq_right h2]
    dsimp [βa, K_wrap0]
    rw [axisWrap_fwdBits 0 β ha0]
    have h4 : ¬ ∃ b : Fin 7, (277 : Wire 437) = p57MW 0 b := by
      rintro ⟨b, hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega
    rw [ite_eq_right (by decide), ite_eq_right h4]
    exact hβ ⟨277, by decide⟩ (by decide)
  have hpres_read : ∀ (w' : Fin 3) (u : Wire 437),
      (u.val < 177) →
      (buildP57Ctx (axisWrapSteps w')).fwdBits (if w'.val = 0 then β else if w'.val = 1 then βa else
        βb) u =
        (if w'.val = 0 then β else if w'.val = 1 then βa else βb) u := by
    intro w' u hu
    fin_cases w'
    · change (buildP57Ctx (axisWrapSteps 0)).fwdBits β u = β u
      rw [axisWrap_fwdBits 0 β ha0,
        ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
        ite_eq_right (by rintro ⟨b, rfl⟩; dsimp [p57MW] at hu; omega)]
    · change (buildP57Ctx (axisWrapSteps 1)).fwdBits βa u = βa u
      rw [axisWrap_fwdBits 1 βa hb0,
        ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
        ite_eq_right (by rintro ⟨b, rfl⟩; dsimp [p57MW] at hu; omega)]
    · change (buildP57Ctx (axisWrapSteps 2)).fwdBits βb u = βb u
      rw [axisWrap_fwdBits 2 βb hc0,
        ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
        ite_eq_right (by rintro ⟨b, rfl⟩; dsimp [p57MW] at hu; omega)]
  have hread_a : ∀ u : Wire 437, u.val < 177 → βa u = β u := fun u hu ↦ hpres_read 0 u hu
  have hread_b : ∀ u : Wire 437, u.val < 177 → βb u = β u := fun u hu ↦
    (hpres_read 1 u hu).trans (hread_a u hu)
  let z (w' : Fin 3) : ZMod 2 :=
    wWrapFromPBufZMod (β (p57ProjW w' ⟨7, by decide⟩))
      (β (p57PBufW w' ⟨7, by decide⟩)) (β (p57S3W w'))
  have hz1 : wWrapFromPBufZMod (βa (p57ProjW 1 ⟨7, by decide⟩))
      (βa (p57PBufW 1 ⟨7, by decide⟩)) (βa (p57S3W 1)) = z 1 := by
    dsimp only [z]
    rw [hread_a (p57ProjW 1 ⟨7, by decide⟩) (by decide),
      hread_a (p57PBufW 1 ⟨7, by decide⟩) (by decide),
      hread_a (p57S3W 1) (by decide)]
  have hz2 : wWrapFromPBufZMod (βb (p57ProjW 2 ⟨7, by decide⟩))
      (βb (p57PBufW 2 ⟨7, by decide⟩)) (βb (p57S3W 2)) = z 2 := by
    dsimp only [z]
    rw [hread_b (p57ProjW 2 ⟨7, by decide⟩) (by decide),
      hread_b (p57PBufW 2 ⟨7, by decide⟩) (by decide),
      hread_b (p57S3W 2) (by decide)]
  have hfn : (fun k : Fin 8 ↦ βc (d8Wire w k)) =
      Fin.snoc (α := fun _ ↦ ZMod 2) (fun b : Fin 7 ↦ β (p57MW w b) + z w) (z w) := by
    funext k
    fin_cases w
    · cases k using Fin.lastCases with
      | last =>
          simp only [d8Wire, Fin.snoc_last]
          dsimp [βc, K_wrap2]; rw [axisWrap_fwdBits 2 βb hc0]
          rw [ite_eq_right (by decide), ite_eq_right (by
            rintro ⟨b, hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
          dsimp [βb, K_wrap1]; rw [axisWrap_fwdBits 1 βa hb0]
          rw [ite_eq_right (by decide), ite_eq_right (by
            rintro ⟨b, hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
          dsimp [βa, K_wrap0]; rw [axisWrap_fwdBits 0 β ha0, ite_eq_left (by decide)]
      | cast b =>
          simp only [d8Wire, Fin.snoc_castSucc]
          dsimp [βc, K_wrap2]; rw [axisWrap_fwdBits 2 βb hc0]
          rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)),
            ite_eq_right (by
              rintro ⟨b', hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
          dsimp [βb, K_wrap1]; rw [axisWrap_fwdBits 1 βa hb0]
          rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)),
            ite_eq_right (by
              rintro ⟨b', hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
          dsimp [βa, K_wrap0]; rw [axisWrap_fwdBits 0 β ha0]
          rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)), ite_eq_left ⟨b, rfl⟩]
    · cases k using Fin.lastCases with
      | last =>
          simp only [d8Wire, Fin.snoc_last]
          dsimp [βc, K_wrap2]; rw [axisWrap_fwdBits 2 βb hc0]
          rw [ite_eq_right (by decide), ite_eq_right (by
            rintro ⟨b, hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
          dsimp [βb, K_wrap1]; rw [axisWrap_fwdBits 1 βa hb0, ite_eq_left (by decide)]
          exact hz1
      | cast b =>
          simp only [d8Wire, Fin.snoc_castSucc]
          dsimp [βc, K_wrap2]; rw [axisWrap_fwdBits 2 βb hc0]
          rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)),
            ite_eq_right (by
              rintro ⟨b', hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
          dsimp [βb, K_wrap1]; rw [axisWrap_fwdBits 1 βa hb0]
          rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)), ite_eq_left ⟨b, rfl⟩]
          have hm1 : βa (p57MW 1 b) = β (p57MW 1 b) := by
            dsimp [βa, K_wrap0]; rw [axisWrap_fwdBits 0 β ha0]
            rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)),
              ite_eq_right (by
                rintro ⟨b', hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
          rw [hm1, hz1]
    · cases k using Fin.lastCases with
      | last =>
          simp only [d8Wire, Fin.snoc_last]
          dsimp [βc, K_wrap2]; rw [axisWrap_fwdBits 2 βb hc0, ite_eq_left (by decide)]
          exact hz2
      | cast b =>
          simp only [d8Wire, Fin.snoc_castSucc]
          dsimp [βc, K_wrap2]; rw [axisWrap_fwdBits 2 βb hc0]
          rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)), ite_eq_left ⟨b, rfl⟩]
          have hm2 : βb (p57MW 2 b) = β (p57MW 2 b) := by
            dsimp [βb, K_wrap1]; rw [axisWrap_fwdBits 1 βa hb0]
            rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)),
              ite_eq_right (by
                rintro ⟨b', hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
            dsimp [βa, K_wrap0]; rw [axisWrap_fwdBits 0 β ha0]
            rw [ite_eq_right (wire_ne_val (by dsimp [p57MW]; omega)),
              ite_eq_right (by
                rintro ⟨b', hb⟩; have hv := congrArg Fin.val hb; dsimp [p57MW] at hv; omega)]
          rw [hm2, hz2]
  rw [hfn, bitsVal_xorSnoc7]
  rfl
inductive BAddr : ℕ → Type
  | nil : BAddr 0
  | cons {k : ℕ} (bit : Bool) (rest : BAddr k) : BAddr (k + 1)
  deriving DecidableEq
def baddrVal : {k : ℕ} → BAddr k → ℕ
  | 0, .nil => 0
  | k + 1, .cons bit rest => cond bit (2 ^ k) 0 + baddrVal rest
theorem baddrVal_lt : ∀ {k : ℕ} (a : BAddr k), baddrVal a < 2 ^ k
  | 0, .nil => by decide
  | k + 1, .cons bit rest => by
      have h := baddrVal_lt rest
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      cases bit <;> (simp only [baddrVal, Bool.cond_false, Bool.cond_true]; omega)
def allBAddr : {k : ℕ} → (BAddr k → Bool) → Bool
  | 0, p => p .nil
  | _ + 1, p => allBAddr (fun r ↦ p (.cons false r)) && allBAddr (fun r ↦ p (.cons true r))
theorem of_allBAddr : ∀ {k : ℕ} {p : BAddr k → Bool},
    allBAddr p = true → ∀ a : BAddr k, p a = true
  | 0, _, h, .nil => h
  | _ + 1, _, h, .cons false r => of_allBAddr ((Bool.and_eq_true _ _).mp h).1 r
  | _ + 1, _, h, .cons true r => of_allBAddr ((Bool.and_eq_true _ _).mp h).2 r
inductive BTree : ℕ → Type
  | leaf (val : Bool) : BTree 0
  | node {k : ℕ} (l r : BTree k) : BTree (k + 1)
def BTree.zero : (k : ℕ) → BTree k
  | 0 => .leaf false
  | k + 1 => .node (BTree.zero k) (BTree.zero k)
def BTree.get : {k : ℕ} → BTree k → BAddr k → Bool
  | 0, .leaf v, .nil => v
  | _ + 1, .node l _, .cons false rest => l.get rest
  | _ + 1, .node _ r, .cons true rest => r.get rest
def BTree.set : {k : ℕ} → BTree k → BAddr k → Bool → BTree k
  | 0, .leaf _, .nil, v => .leaf v
  | _ + 1, .node l r, .cons false rest, v => .node (l.set rest v) r
  | _ + 1, .node l r, .cons true rest, v => .node l (r.set rest v)
theorem BTree.zero_get : ∀ {k : ℕ} (a : BAddr k),(BTree.zero k).get a = false
  | 0, .nil => rfl
  | _ + 1, .cons false rest => BTree.zero_get rest
  | _ + 1, .cons true rest => BTree.zero_get rest
theorem BTree.get_set_self : ∀ {k : ℕ} (tr : BTree k) (a : BAddr k) (v : Bool),
    (tr.set a v).get a = v
  | 0, .leaf _, .nil, _ => rfl
  | _ + 1, .node l _, .cons false rest, v => BTree.get_set_self l rest v
  | _ + 1, .node _ r, .cons true rest, v => BTree.get_set_self r rest v
theorem BTree.get_set_ne : ∀ {k : ℕ} (tr : BTree k) {a b : BAddr k} (v : Bool),
    a ≠ b → (tr.set b v).get a = tr.get a
  | 0, .leaf _, .nil, .nil, _, h => absurd rfl h
  | _ + 1, .node _ _, .cons false _, .cons true _, _, _ => rfl
  | _ + 1, .node _ _, .cons true _, .cons false _, _, _ => rfl
  | _ + 1, .node l _, .cons false _, .cons false _, v, h =>
      BTree.get_set_ne l v (fun he ↦ h (congrArg _ he))
  | _ + 1, .node _ r, .cons true _, .cons true _, v, h =>
      BTree.get_set_ne r v (fun he ↦ h (congrArg _ he))
def bxor : Bool → Bool → Bool
  | false, y => y | true, y => !y
def b2z : Bool → ZMod 2
  | false => 0 | true => 1
def z2b (z : ZMod 2) : Bool := z.val == 1
theorem b2z_z2b (z : ZMod 2) : b2z (z2b z) = z := by
  rcases bit_cases z with rfl | rfl <;> rfl
theorem b2z_not (x : Bool) : b2z (!x) = b2z x + 1 := Bool.casesOn x rfl rfl
theorem b2z_bxor : ∀ x y : Bool, b2z (bxor x y) = b2z x + b2z y := by decide
theorem b2z_and_bxor : ∀ d a b : Bool, b2z (bxor d (a && b)) = b2z d + b2z a * b2z b := by decide
theorem cond_z2b_mul (z : ZMod 2) (m : ℕ) : cond (z2b z) m 0 = z.val * m := by
  rcases bit_cases z with rfl | rfl <;> simp [z2b, ZMod.val_zero]
def initSqTree (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : BTree 6 :=
  let t3 : BTree 3 := .node (.node (.node (.leaf b0) (.leaf b1)) (.node (.leaf b2) (.leaf b3)))
    (.node (.node (.leaf b4) (.leaf b5)) (.node (.leaf b6) (.leaf b7)))
  .node (.node (.node t3 (BTree.zero 3)) (BTree.zero 4)) (BTree.zero 5)
theorem initSqTree_get_ge8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    ∀ (a : BAddr 6), 8 ≤ baddrVal a → (initSqTree b0 b1 b2 b3 b4 b5 b6 b7).get a = false
  | .cons true r, _ | .cons false (.cons true r), _ | .cons false (.cons false (.cons true r)), _ =>
      BTree.zero_get r
  | .cons false (.cons false (.cons false rest)), h => by
      have hlt : baddrVal rest < 8 := baddrVal_lt rest
      simp only [baddrVal, Bool.cond_false] at h
      omega
inductive LocalStep : Type
  | x (q : BAddr 6)
  | cnot (c t : BAddr 6)
  | tempAnd (a b dst : BAddr 6)
def evalLocalStep (tr : BTree 6) : LocalStep → BTree 6
  | .x q => tr.set q (!tr.get q)
  | .cnot c t => tr.set t (bxor (tr.get t) (tr.get c))
  | .tempAnd a b dst => tr.set dst (bxor (tr.get dst) (tr.get a && tr.get b))
def evalLocalSteps : BTree 6 → List LocalStep → BTree 6
  | tr, [] => tr
  | tr, s :: ss => evalLocalSteps (evalLocalStep tr s) ss
theorem evalLocalSteps_append :
    ∀ (xs ys : List LocalStep) (tr : BTree 6),
      evalLocalSteps tr (xs ++ ys) = evalLocalSteps (evalLocalSteps tr xs) ys
  | [], _, _ => rfl
  | _ :: xs, ys, _ => evalLocalSteps_append xs ys _
def pow2Col : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 8 | 4 => 16 | 5 => 32 | 6 => 64 | 7 => 128
  | 8 => 256 | 9 => 512 | 10 => 1024 | 11 => 2048 | 12 => 4096 | 13 => 8192
  | 14 => 16384 | 15 => 32768 | 16 => 65536 | 17 => 131072
  | n => 2 ^ n
theorem pow2Col_eq : ∀ c : ℕ, pow2Col c = 2 ^ c
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | 4 => rfl | 5 => rfl
  | 6 => rfl | 7 => rfl | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl
  | 12 => rfl | 13 => rfl | 14 => rfl | 15 => rfl | 16 => rfl | 17 => rfl
  | _ + 18 => rfl
def localColSum : List (ℕ × BAddr 6) → BTree 6 → ℕ
  | [], _ => 0
  | (c, a) :: rest, tr => Nat.add (cond (tr.get a) (pow2Col c) 0) (localColSum rest tr)
def bool8Val (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : ℕ := Nat.add (cond b0 1 0) (Nat.add (cond b1 2
    0) (Nat.add (cond b2 4 0) (Nat.add (cond b3 8 0) (Nat.add (cond b4 16 0) (Nat.add (cond b5
    32 0) (Nat.add (cond b6 64 0) (cond b7 128 0)))))))
theorem bool8Val_eq_bitsVal (f : Fin 8 → ZMod 2) : bool8Val (z2b (f 0)) (z2b (f 1))
    (z2b (f 2)) (z2b (f 3)) (z2b (f 4)) (z2b (f 5)) (z2b (f 6)) (z2b (f 7)) = bitsVal f := by
  simp only [bool8Val, Nat.add_eq, cond_z2b_mul, bitsVal, Fin.sum_univ_eight]
  change (f 0).val * 1 + ((f 1).val * 2 + ((f 2).val * 4 + ((f 3).val * 8 +
      ((f 4).val * 16 + ((f 5).val * 32 + ((f 6).val * 64 + (f 7).val * 128)))))) =
    (f 0).val * 1 + (f 1).val * 2 + (f 2).val * 4 + (f 3).val * 8 +
      (f 4).val * 16 + (f 5).val * 32 + (f 6).val * 64 + (f 7).val * 128
  ring
inductive OctIdx : Type
  | i0 | i1 | i2 | i3 | i4 | i5 | i6 | i7
inductive Oct1 : Type
  | mk (x0 x1 x2 x3 x4 x5 x6 x7 : Bool)
inductive Oct2 : Type
  | mk (o0 o1 o2 o3 o4 o5 o6 o7 : Oct1)
def oct1ToB3 : Oct1 → BTree 3
  | .mk x0 x1 x2 x3 x4 x5 x6 x7 =>
      .node (.node (.node (.leaf x0) (.leaf x1)) (.node (.leaf x2) (.leaf x3)))
            (.node (.node (.leaf x4) (.leaf x5)) (.node (.leaf x6) (.leaf x7)))
def oct2ToB6 : Oct2 → BTree 6
  | .mk o0 o1 o2 o3 o4 o5 o6 o7 =>
      .node (.node (.node (oct1ToB3 o0) (oct1ToB3 o1)) (.node (oct1ToB3 o2) (oct1ToB3 o3)))
            (.node (.node (oct1ToB3 o4) (oct1ToB3 o5)) (.node (oct1ToB3 o6) (oct1ToB3 o7)))
def octIdxToB3 : OctIdx → BAddr 3
  | .i0 => .cons false (.cons false (.cons false .nil))
  | .i1 => .cons false (.cons false (.cons true .nil))
  | .i2 => .cons false (.cons true (.cons false .nil))
  | .i3 => .cons false (.cons true (.cons true .nil))
  | .i4 => .cons true (.cons false (.cons false .nil))
  | .i5 => .cons true (.cons false (.cons true .nil))
  | .i6 => .cons true (.cons true (.cons false .nil))
  | .i7 => .cons true (.cons true (.cons true .nil))
def octAddrToB6 (hi lo : OctIdx) : BAddr 6 :=
  let r := octIdxToB3 lo
  match hi with
  | .i0 => .cons false (.cons false (.cons false r))
  | .i1 => .cons false (.cons false (.cons true r))
  | .i2 => .cons false (.cons true (.cons false r))
  | .i3 => .cons false (.cons true (.cons true r))
  | .i4 => .cons true (.cons false (.cons false r))
  | .i5 => .cons true (.cons false (.cons true r))
  | .i6 => .cons true (.cons true (.cons false r))
  | .i7 => .cons true (.cons true (.cons true r))
def getOct1 : Oct1 → OctIdx → Bool
  | .mk x0 x1 x2 x3 x4 x5 x6 x7, lo => match lo with
      | .i0 => x0 | .i1 => x1 | .i2 => x2 | .i3 => x3
      | .i4 => x4 | .i5 => x5 | .i6 => x6 | .i7 => x7
def getOct2 : Oct2 → OctIdx → OctIdx → Bool
  | .mk o0 o1 o2 o3 o4 o5 o6 o7, hi, lo => match hi with
      | .i0 => getOct1 o0 lo | .i1 => getOct1 o1 lo | .i2 => getOct1 o2 lo | .i3 => getOct1 o3 lo
      | .i4 => getOct1 o4 lo | .i5 => getOct1 o5 lo | .i6 => getOct1 o6 lo | .i7 => getOct1 o7 lo
theorem getOct1_eq : ∀ (o : Oct1) (lo : OctIdx),
    getOct1 o lo = (oct1ToB3 o).get (octIdxToB3 lo)
  | .mk _ _ _ _ _ _ _ _, lo => OctIdx.casesOn lo rfl rfl rfl rfl rfl rfl rfl rfl
theorem getOct2_eq : ∀ (t : Oct2) (hi lo : OctIdx),
    getOct2 t hi lo = (oct2ToB6 t).get (octAddrToB6 hi lo)
  | .mk _ _ _ _ _ _ _ _, hi, lo =>
      OctIdx.casesOn hi (getOct1_eq _ lo) (getOct1_eq _ lo) (getOct1_eq _ lo) (getOct1_eq _ lo)
        (getOct1_eq _ lo) (getOct1_eq _ lo) (getOct1_eq _ lo) (getOct1_eq _ lo)
def ssetOct1 {α : Type} : Oct1 → OctIdx → Bool → (Oct1 → α) → α
  | .mk x0 x1 x2 x3 x4 x5 x6 x7, lo, v, k =>
      match lo with
      | .i0 => Bool.rec (k (.mk false x1 x2 x3 x4 x5 x6 x7)) (k (.mk true x1 x2 x3 x4 x5 x6 x7)) v
      | .i1 => Bool.rec (k (.mk x0 false x2 x3 x4 x5 x6 x7)) (k (.mk x0 true x2 x3 x4 x5 x6 x7)) v
      | .i2 => Bool.rec (k (.mk x0 x1 false x3 x4 x5 x6 x7)) (k (.mk x0 x1 true x3 x4 x5 x6 x7)) v
      | .i3 => Bool.rec (k (.mk x0 x1 x2 false x4 x5 x6 x7)) (k (.mk x0 x1 x2 true x4 x5 x6 x7)) v
      | .i4 => Bool.rec (k (.mk x0 x1 x2 x3 false x5 x6 x7)) (k (.mk x0 x1 x2 x3 true x5 x6 x7)) v
      | .i5 => Bool.rec (k (.mk x0 x1 x2 x3 x4 false x6 x7)) (k (.mk x0 x1 x2 x3 x4 true x6 x7)) v
      | .i6 => Bool.rec (k (.mk x0 x1 x2 x3 x4 x5 false x7)) (k (.mk x0 x1 x2 x3 x4 x5 true x7)) v
      | .i7 => Bool.rec (k (.mk x0 x1 x2 x3 x4 x5 x6 false)) (k (.mk x0 x1 x2 x3 x4 x5 x6 true)) v
def ssetOct2 {α : Type} : Oct2 → OctIdx → OctIdx → Bool → (Oct2 → α) → α
  | .mk o0 o1 o2 o3 o4 o5 o6 o7, hi, lo, v, k =>
      match hi with
      | .i0 => ssetOct1 o0 lo v (fun u ↦ k (.mk u o1 o2 o3 o4 o5 o6 o7))
      | .i1 => ssetOct1 o1 lo v (fun u ↦ k (.mk o0 u o2 o3 o4 o5 o6 o7))
      | .i2 => ssetOct1 o2 lo v (fun u ↦ k (.mk o0 o1 u o3 o4 o5 o6 o7))
      | .i3 => ssetOct1 o3 lo v (fun u ↦ k (.mk o0 o1 o2 u o4 o5 o6 o7))
      | .i4 => ssetOct1 o4 lo v (fun u ↦ k (.mk o0 o1 o2 o3 u o5 o6 o7))
      | .i5 => ssetOct1 o5 lo v (fun u ↦ k (.mk o0 o1 o2 o3 o4 u o6 o7))
      | .i6 => ssetOct1 o6 lo v (fun u ↦ k (.mk o0 o1 o2 o3 o4 o5 u o7))
      | .i7 => ssetOct1 o7 lo v (fun u ↦ k (.mk o0 o1 o2 o3 o4 o5 o6 u))
theorem p57Slim_ssetOct1_k {α : Type} : ∀ (o : Oct1) (lo : OctIdx) (v : Bool) (k : Oct1 → α),
    ssetOct1 o lo v k = k (ssetOct1 o lo v id)
  | .mk _ _ _ _ _ _ _ _, lo, false, _ => OctIdx.casesOn lo rfl rfl rfl rfl rfl rfl rfl rfl
  | .mk _ _ _ _ _ _ _ _, lo, true, _ => OctIdx.casesOn lo rfl rfl rfl rfl rfl rfl rfl rfl
theorem p57Slim_oct1ToB3_sset : ∀ (o : Oct1) (lo : OctIdx) (v : Bool),
    oct1ToB3 (ssetOct1 o lo v id) = (oct1ToB3 o).set (octIdxToB3 lo) v
  | .mk _ _ _ _ _ _ _ _, lo, false => OctIdx.casesOn lo rfl rfl rfl rfl rfl rfl rfl rfl
  | .mk _ _ _ _ _ _ _ _, lo, true => OctIdx.casesOn lo rfl rfl rfl rfl rfl rfl rfl rfl
theorem ssetOct2_eq {α : Type} : ∀ (t : Oct2) (hi lo : OctIdx) (v : Bool) (k : Oct2 → α)
    (f : BTree 6 → α), (∀ t', k t' = f (oct2ToB6 t')) →
    ssetOct2 t hi lo v k = f ((oct2ToB6 t).set (octAddrToB6 hi lo) v)
  | .mk _ _ _ _ _ _ _ _, .i0, _, _, _, _, hf | .mk _ _ _ _ _ _ _ _, .i1, _, _, _, _, hf
  | .mk _ _ _ _ _ _ _ _, .i2, _, _, _, _, hf | .mk _ _ _ _ _ _ _ _, .i3, _, _, _, _, hf
  | .mk _ _ _ _ _ _ _ _, .i4, _, _, _, _, hf | .mk _ _ _ _ _ _ _ _, .i5, _, _, _, _, hf
  | .mk _ _ _ _ _ _ _ _, .i6, _, _, _, _, hf | .mk _ _ _ _ _ _ _ _, .i7, _, _, _, _, hf => by
      dsimp only [ssetOct2]
      rw [p57Slim_ssetOct1_k, hf]
      simp only [oct2ToB6, octAddrToB6, BTree.set]
      rw [p57Slim_oct1ToB3_sset]
def zOct1 : Oct1 := .mk false false false false false false false false
def initOct2 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Oct2 :=
  .mk (.mk b0 b1 b2 b3 b4 b5 b6 b7) zOct1 zOct1 zOct1 zOct1 zOct1 zOct1 zOct1
theorem oct2ToB6_initOct2 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    oct2ToB6 (initOct2 b0 b1 b2 b3 b4 b5 b6 b7) = initSqTree b0 b1 b2 b3 b4 b5 b6 b7 := rfl
inductive StepOct : Type
  | x (hi lo : OctIdx)
  | cnot (chi clo thi tlo : OctIdx)
  | tempAnd (ahi alo bhi blo dhi dlo : OctIdx)
def stepOctToLocal : StepOct → LocalStep
  | .x hi lo => .x (octAddrToB6 hi lo)
  | .cnot chi clo thi tlo => .cnot (octAddrToB6 chi clo) (octAddrToB6 thi tlo)
  | .tempAnd ahi alo bhi blo dhi dlo =>
      .tempAnd (octAddrToB6 ahi alo) (octAddrToB6 bhi blo) (octAddrToB6 dhi dlo)
def optStepOctList : Option StepOct → List LocalStep
  | none => [] | some s => [stepOctToLocal s]
def evalStepOct {α : Type} (tr : Oct2) (op : Option StepOct) (k : Oct2 → α) : α :=
  match op with
  | none => k tr
  | some (.x hi lo) => ssetOct2 tr hi lo (Bool.rec true false (getOct2 tr hi lo)) k
  | some (.cnot chi clo thi tlo) =>
      let vt := getOct2 tr thi tlo
      ssetOct2 tr thi tlo (Bool.rec vt (Bool.rec true false vt) (getOct2 tr chi clo)) k
  | some (.tempAnd ahi alo bhi blo dhi dlo) =>
      let vd := getOct2 tr dhi dlo
      let ab := Bool.rec false (getOct2 tr bhi blo) (getOct2 tr ahi alo)
      ssetOct2 tr dhi dlo (Bool.rec vd (Bool.rec true false vd) ab) k
theorem evalStepOct_eq {α : Type} (tr : Oct2) (op : Option StepOct)
    (k : Oct2 → α) (f : BTree 6 → α) (hf : ∀ t', k t' = f (oct2ToB6 t')) :
    evalStepOct tr op k = f (evalLocalSteps (oct2ToB6 tr) (optStepOctList op)) := by
  rcases op with _ | ⟨hi, lo⟩ | ⟨chi, clo, thi, tlo⟩ | ⟨ahi, alo, bhi, blo, dhi, dlo⟩
  · exact hf tr
  · simp only [evalStepOct, optStepOctList, stepOctToLocal, evalLocalSteps, evalLocalStep,
      ssetOct2_eq tr hi lo _ k f hf, getOct2_eq tr hi lo]
    exact congrArg (fun b ↦ f ((oct2ToB6 tr).set _ b))
      (Bool.casesOn ((oct2ToB6 tr).get (octAddrToB6 hi lo)) rfl rfl)
  · simp only [evalStepOct, optStepOctList, stepOctToLocal, evalLocalSteps, evalLocalStep,
      ssetOct2_eq tr thi tlo _ k f hf, getOct2_eq tr thi tlo, getOct2_eq tr chi clo]
    exact congrArg (fun b ↦ f ((oct2ToB6 tr).set _ b))
      (Bool.casesOn ((oct2ToB6 tr).get (octAddrToB6 chi clo))
        (Bool.casesOn ((oct2ToB6 tr).get (octAddrToB6 thi tlo)) rfl rfl)
        (Bool.casesOn ((oct2ToB6 tr).get (octAddrToB6 thi tlo)) rfl rfl))
  · simp only [evalStepOct, optStepOctList, stepOctToLocal, evalLocalSteps, evalLocalStep,
      ssetOct2_eq tr dhi dlo _ k f hf, getOct2_eq tr dhi dlo, getOct2_eq tr ahi alo,
      getOct2_eq tr bhi blo]
    exact congrArg (fun b ↦ f ((oct2ToB6 tr).set _ b)) (by
      generalize (oct2ToB6 tr).get (octAddrToB6 dhi dlo) = vd
      generalize (oct2ToB6 tr).get (octAddrToB6 ahi alo) = va
      generalize (oct2ToB6 tr).get (octAddrToB6 bhi blo) = vb
      revert vd va vb
      decide)
/-- Binary tree of `2 ^ n` optional octal steps. -/
def p57SlimProg : ℕ → Type
  | 0 => Option StepOct
  | n + 1 => p57SlimProg n × p57SlimProg n
abbrev Prog8 := p57SlimProg 8
/-- CPS evaluator for `p57SlimProg n`. -/
def p57SlimEv : (n : ℕ) → {α : Type} → Oct2 → p57SlimProg n → (Oct2 → α) → α
  | 0, _, tr, p, k => evalStepOct tr p k
  | n + 1, _, tr, p, k => p57SlimEv n tr p.1 (fun t1 ↦ p57SlimEv n t1 p.2 k)
abbrev ev8 {α : Type} (tr : Oct2) (p : Prog8) (k : Oct2 → α) : α := p57SlimEv 8 tr p k
/-- Flatten `p57SlimProg n` into `List LocalStep`. -/
def p57SlimLs : (n : ℕ) → p57SlimProg n → List LocalStep
  | 0, p => optStepOctList p
  | n + 1, p => p57SlimLs n p.1 ++ p57SlimLs n p.2
abbrev ls8 (p : Prog8) : List LocalStep := p57SlimLs 8 p
theorem p57Slim_ev_eq : ∀ (n : ℕ) {α : Type} (tr : Oct2) (p : p57SlimProg n)
    (k : Oct2 → α) (f : BTree 6 → α), (∀ t', k t' = f (oct2ToB6 t')) →
    p57SlimEv n tr p k = f (evalLocalSteps (oct2ToB6 tr) (p57SlimLs n p))
  | 0, _, tr, p, k, f, hf => evalStepOct_eq tr p k f hf
  | n + 1, _, tr, p, k, f, hf => by
      dsimp only [p57SlimEv, p57SlimLs]
      rw [evalLocalSteps_append]
      exact p57Slim_ev_eq n tr p.1 _ (fun b1 ↦ f (evalLocalSteps b1 (p57SlimLs n p.2)))
        (fun t1 ↦ p57Slim_ev_eq n t1 p.2 k f hf)
def prog8_34 : Prog8 := (((((((((some (.x .i0 .i3)),(some (.x .i0 .i2))),
  ((some (.tempAnd .i0 .i3 .i0 .i2 .i1 .i0)),(some (.x .i0 .i2)))),(((some (.x .i0 .i3)),
  (some (.x .i0 .i1))),((some (.x .i0 .i0)),(some (.tempAnd .i0 .i1 .i0 .i0 .i1 .i1))))),
  ((((some (.x .i0 .i0)),(some (.x .i0 .i1))),((some (.x .i0 .i3)),(some (.cnot .i1 .i1 .i0 .i3)))),
  (((some (.cnot .i0 .i2 .i0 .i0)),(some (.cnot .i1 .i1 .i0 .i0))),
  ((some (.tempAnd .i0 .i3 .i0 .i0 .i1 .i2)),(some (.cnot .i1 .i1 .i0 .i0)))))),
  (((((some (.cnot .i0 .i2 .i0 .i0)),(some (.cnot .i1 .i1 .i0 .i3))),((some (.x .i0 .i3)),
  (some (.cnot .i0 .i3 .i0 .i2)))),(((some (.cnot .i1 .i1 .i0 .i2)),(some (.cnot .i0 .i1 .i0 .i0))),
  ((some (.cnot .i1 .i2 .i0 .i0)),(some (.tempAnd .i0 .i2 .i0 .i0 .i1 .i3))))),
  ((((some (.cnot .i1 .i2 .i0 .i0)),(some (.cnot .i0 .i1 .i0 .i0))),((some (.cnot .i1 .i1 .i0 .i2)),
  (some (.cnot .i0 .i3 .i0 .i2)))),(((some (.x .i1 .i3)),(some (.cnot .i0 .i3 .i1 .i3))),
  ((some (.cnot .i0 .i1 .i1 .i0)),(some (.cnot .i0 .i3 .i1 .i0))))))),
  ((((((some (.tempAnd .i1 .i3 .i1 .i0 .i1 .i4)),(some (.cnot .i0 .i3 .i1 .i0))),
  ((some (.cnot .i0 .i1 .i1 .i0)),(some (.cnot .i0 .i3 .i1 .i3)))),(((some (.x .i1 .i3)),
  (some (.x .i0 .i7))),((some (.x .i0 .i6)),(some (.tempAnd .i0 .i7 .i0 .i6 .i1 .i5))))),
  ((((some (.x .i0 .i6)),(some (.x .i0 .i7))),((some (.x .i0 .i5)),(some (.x .i0 .i4)))),
  (((some (.tempAnd .i0 .i5 .i0 .i4 .i1 .i6)),(some (.x .i0 .i4))),((some (.x .i0 .i5)),
  (some (.x .i0 .i7)))))),(((((some (.cnot .i1 .i6 .i0 .i7)),(some (.cnot .i0 .i6 .i0 .i4))),
  ((some (.cnot .i1 .i6 .i0 .i4)),(some (.tempAnd .i0 .i7 .i0 .i4 .i1 .i7)))),
  (((some (.cnot .i1 .i6 .i0 .i4)),(some (.cnot .i0 .i6 .i0 .i4))),((some (.cnot .i1 .i6 .i0 .i7)),
  (some (.x .i0 .i7))))),((((some (.cnot .i0 .i7 .i0 .i6)),(some (.cnot .i1 .i6 .i0 .i6))),
  ((some (.cnot .i0 .i5 .i0 .i4)),(some (.cnot .i1 .i7 .i0 .i4)))),
  (((some (.tempAnd .i0 .i6 .i0 .i4 .i2 .i0)),(some (.cnot .i1 .i7 .i0 .i4))),
  ((some (.cnot .i0 .i5 .i0 .i4)),(some (.cnot .i1 .i6 .i0 .i6)))))))),
  (((((((some (.cnot .i0 .i7 .i0 .i6)),(some (.x .i2 .i0))),((some (.cnot .i0 .i7 .i2 .i0)),
  (some (.cnot .i0 .i5 .i1 .i5)))),(((some (.cnot .i0 .i7 .i1 .i5)),
  (some (.tempAnd .i2 .i0 .i1 .i5 .i2 .i1))),((some (.cnot .i0 .i7 .i1 .i5)),
  (some (.cnot .i0 .i5 .i1 .i5))))),((((some (.cnot .i0 .i7 .i2 .i0)),(some (.x .i2 .i0))),
  ((some (.tempAnd .i0 .i0 .i0 .i6 .i2 .i2)),(some (.tempAnd .i0 .i0 .i0 .i7 .i2 .i3)))),
  (((some (.tempAnd .i0 .i1 .i0 .i6 .i2 .i4)),(some (.tempAnd .i0 .i1 .i0 .i7 .i2 .i5))),
  ((some (.tempAnd .i0 .i2 .i0 .i4 .i2 .i6)),(some (.tempAnd .i0 .i2 .i0 .i5 .i2 .i7)))))),
  (((((some (.tempAnd .i0 .i3 .i0 .i5 .i3 .i0)),(some (.tempAnd .i0 .i3 .i0 .i4 .i3 .i1))),
  ((some (.tempAnd .i0 .i0 .i0 .i4 .i3 .i2)),(some (.tempAnd .i0 .i1 .i0 .i5 .i3 .i3)))),
  (((some (.cnot .i0 .i1 .i0 .i0)),(some (.cnot .i0 .i5 .i0 .i4))),
  ((some (.tempAnd .i0 .i0 .i0 .i4 .i3 .i4)),(some (.cnot .i0 .i5 .i0 .i4))))),
  ((((some (.cnot .i0 .i1 .i0 .i0)),(some (.cnot .i3 .i2 .i3 .i4))),((some (.cnot .i3 .i3 .i3 .i4)),
  (some (.x .i1 .i1)))),(((some (.cnot .i0 .i0 .i1 .i1)),(some (.cnot .i0 .i1 .i1 .i1))),
  ((some (.x .i1 .i6)),(some (.cnot .i0 .i4 .i1 .i6))))))),((((((some (.cnot .i0 .i5 .i1 .i6)),
  (some (.tempAnd .i1 .i1 .i1 .i6 .i3 .i5))),((some (.cnot .i0 .i5 .i1 .i6)),
  (some (.cnot .i0 .i4 .i1 .i6)))),(((some (.x .i1 .i6)),(some (.cnot .i0 .i1 .i1 .i1))),
  ((some (.cnot .i0 .i0 .i1 .i1)),(some (.x .i1 .i1))))),
  ((((some (.tempAnd .i0 .i2 .i0 .i6 .i3 .i6)),(some (.tempAnd .i0 .i3 .i0 .i7 .i3 .i7))),
  ((some (.cnot .i0 .i3 .i0 .i2)),(some (.cnot .i0 .i7 .i0 .i6)))),
  (((some (.tempAnd .i0 .i2 .i0 .i6 .i4 .i0)),(some (.cnot .i0 .i7 .i0 .i6))),
  ((some (.cnot .i0 .i3 .i0 .i2)),(some (.cnot .i3 .i6 .i4 .i0)))))),
  (((((some (.cnot .i3 .i7 .i4 .i0)),(some (.x .i1 .i0))),((some (.cnot .i0 .i2 .i1 .i0)),
  (some (.cnot .i0 .i3 .i1 .i0)))),(((some (.x .i1 .i5)),(some (.cnot .i0 .i6 .i1 .i5))),
  ((some (.cnot .i0 .i7 .i1 .i5)),(some (.tempAnd .i1 .i0 .i1 .i5 .i4 .i1))))),
  ((((some (.cnot .i0 .i7 .i1 .i5)),(some (.cnot .i0 .i6 .i1 .i5))),((some (.x .i1 .i5)),
  (some (.cnot .i0 .i3 .i1 .i0)))),(((some (.cnot .i0 .i2 .i1 .i0)),(some (.x .i1 .i0))),
  ((some (.cnot .i4 .i1 .i3 .i7)),(some (.cnot .i1 .i4 .i1 .i3))))))))),
  ((((((((some (.cnot .i1 .i4 .i1 .i2)),(some (.cnot .i1 .i4 .i1 .i0))),
  ((some (.cnot .i1 .i4 .i0 .i3)),(some (.cnot .i1 .i3 .i1 .i4)))),(((some (.cnot .i1 .i3 .i1 .i2)),
  (some (.cnot .i1 .i3 .i1 .i1))),((some (.cnot .i1 .i3 .i1 .i0)),(some (.cnot .i1 .i3 .i0 .i3))))),
  ((((some (.cnot .i1 .i3 .i0 .i1)),(some (.cnot .i1 .i2 .i1 .i3))),((some (.cnot .i1 .i2 .i1 .i1)),
  (some (.cnot .i1 .i1 .i1 .i4)))),(((some (.cnot .i1 .i1 .i1 .i3)),(some (.cnot .i1 .i1 .i0 .i3))),
  ((some (.cnot .i1 .i1 .i0 .i2)),(some (.cnot .i1 .i2 .i1 .i1)))))),
  (((((some (.cnot .i1 .i1 .i1 .i2)),(some (.cnot .i1 .i2 .i1 .i1))),
  ((some (.cnot .i1 .i0 .i0 .i2)),(some (.cnot .i1 .i2 .i1 .i0)))),(((some (.cnot .i1 .i0 .i1 .i2)),
  (some (.cnot .i1 .i2 .i1 .i0))),((some (.cnot .i0 .i3 .i1 .i4)),(some (.cnot .i1 .i3 .i0 .i3))))),
  ((((some (.cnot .i0 .i3 .i1 .i3)),(some (.cnot .i1 .i3 .i0 .i3))),((some (.cnot .i0 .i2 .i1 .i3)),
  (some (.cnot .i0 .i2 .i1 .i0)))),(((some (.cnot .i0 .i3 .i0 .i2)),(some (.cnot .i0 .i2 .i0 .i3))),
  ((some (.cnot .i0 .i3 .i0 .i2)),(some (.cnot .i0 .i1 .i1 .i2))))))),
  ((((((some (.cnot .i0 .i1 .i0 .i2)),(some (.cnot .i0 .i0 .i1 .i1))),
  ((some (.cnot .i0 .i0 .i0 .i2)),(some (.x .i0 .i1)))),(((some (.x .i0 .i3)),(some (.x .i1 .i0))),
  ((some (.x .i1 .i3)),(some (.cnot .i2 .i1 .i2 .i0))))),((((some (.cnot .i2 .i1 .i1 .i7)),
  (some (.cnot .i2 .i1 .i1 .i5))),((some (.cnot .i2 .i1 .i0 .i7)),(some (.cnot .i2 .i0 .i2 .i1)))),
  (((some (.cnot .i2 .i0 .i1 .i7)),(some (.cnot .i2 .i0 .i1 .i6))),((some (.cnot .i2 .i0 .i1 .i5)),
  (some (.cnot .i2 .i0 .i0 .i7)))))),(((((some (.cnot .i2 .i0 .i0 .i5)),
  (some (.cnot .i1 .i7 .i2 .i0))),((some (.cnot .i1 .i7 .i1 .i6)),(some (.cnot .i1 .i6 .i2 .i1)))),
  (((some (.cnot .i1 .i6 .i2 .i0)),(some (.cnot .i1 .i6 .i0 .i7))),((some (.cnot .i1 .i6 .i0 .i6)),
  (some (.cnot .i1 .i7 .i1 .i6))))),((((some (.cnot .i1 .i6 .i1 .i7)),
  (some (.cnot .i1 .i7 .i1 .i6))),((some (.cnot .i1 .i5 .i0 .i6)),(some (.cnot .i1 .i7 .i1 .i5)))),
  (((some (.cnot .i1 .i5 .i1 .i7)),(some (.cnot .i1 .i7 .i1 .i5))),((some (.cnot .i0 .i7 .i2 .i1)),
  (some (.cnot .i2 .i0 .i0 .i7)))))))),(((((((some (.cnot .i0 .i7 .i2 .i0)),
  (some (.cnot .i2 .i0 .i0 .i7))),((some (.cnot .i0 .i6 .i2 .i0)),(some (.cnot .i0 .i6 .i1 .i5)))),
  (((some (.cnot .i0 .i7 .i0 .i6)),(some (.cnot .i0 .i6 .i0 .i7))),((some (.cnot .i0 .i7 .i0 .i6)),
  (some (.cnot .i0 .i5 .i1 .i7))))),((((some (.cnot .i0 .i5 .i0 .i6)),
  (some (.cnot .i0 .i4 .i1 .i6))),((some (.cnot .i0 .i4 .i0 .i6)),(some (.x .i0 .i5)))),
  (((some (.x .i0 .i7)),(some (.x .i1 .i5))),((some (.x .i2 .i0)), none)))),((((none, none),(none,
  none)),((none, none),(none, none))),(((none, none),(none, none)),((none, none),(none, none))))),
  (((((none, none),(none, none)),((none, none),(none, none))),(((none, none),(none, none)),((none,
  none),(none, none)))),((((none, none),(none, none)),((none, none),(none, none))),(((none, none),
  (none, none)),((none, none),(none, none))))))))
def prog8_35 : Prog8 := (((((((((some (.x .i0 .i3)),(some (.x .i0 .i2))),
  ((some (.tempAnd .i0 .i3 .i0 .i2 .i1 .i0)),(some (.x .i0 .i2)))),(((some (.x .i0 .i3)),
  (some (.x .i0 .i2))),((some (.x .i0 .i0)),(some (.tempAnd .i0 .i2 .i0 .i0 .i1 .i1))))),
  ((((some (.x .i0 .i0)),(some (.x .i0 .i2))),((some (.cnot .i1 .i0 .i1 .i1)),(some (.x .i0 .i1)))),
  (((some (.cnot .i1 .i0 .i0 .i1)),(some (.tempAnd .i1 .i1 .i0 .i1 .i1 .i2))),
  ((some (.cnot .i1 .i0 .i0 .i1)),(some (.x .i0 .i1)))))),(((((some (.cnot .i1 .i0 .i1 .i1)),
  (some (.cnot .i0 .i3 .i0 .i2))),((some (.cnot .i1 .i1 .i0 .i2)),(some (.x .i0 .i1)))),
  (((some (.cnot .i1 .i0 .i0 .i1)),(some (.cnot .i1 .i2 .i0 .i1))),
  ((some (.tempAnd .i0 .i2 .i0 .i1 .i1 .i3)),(some (.cnot .i1 .i2 .i0 .i1))))),
  ((((some (.cnot .i1 .i0 .i0 .i1)),(some (.x .i0 .i1))),((some (.cnot .i1 .i1 .i0 .i2)),
  (some (.cnot .i0 .i3 .i0 .i2)))),(((some (.cnot .i0 .i3 .i0 .i2)),(some (.cnot .i1 .i0 .i0 .i2))),
  ((some (.cnot .i1 .i1 .i0 .i2)),(some (.x .i1 .i3))))))),((((((some (.cnot .i0 .i0 .i1 .i3)),
  (some (.cnot .i1 .i1 .i1 .i3))),((some (.cnot .i1 .i2 .i1 .i3)),
  (some (.tempAnd .i0 .i2 .i1 .i3 .i1 .i4)))),(((some (.cnot .i1 .i2 .i1 .i3)),
  (some (.cnot .i1 .i1 .i1 .i3))),((some (.cnot .i0 .i0 .i1 .i3)),(some (.x .i1 .i3))))),
  ((((some (.cnot .i1 .i1 .i0 .i2)),(some (.cnot .i1 .i0 .i0 .i2))),((some (.cnot .i0 .i3 .i0 .i2)),
  (some (.x .i1 .i4)))),(((some (.cnot .i0 .i1 .i1 .i4)),(some (.cnot .i0 .i0 .i1 .i3))),
  ((some (.cnot .i0 .i3 .i1 .i3)),(some (.cnot .i1 .i0 .i1 .i3)))))),
  (((((some (.cnot .i1 .i2 .i1 .i3)),(some (.tempAnd .i1 .i4 .i1 .i3 .i1 .i5))),
  ((some (.cnot .i1 .i2 .i1 .i3)),(some (.cnot .i1 .i0 .i1 .i3)))),(((some (.cnot .i0 .i3 .i1 .i3)),
  (some (.cnot .i0 .i0 .i1 .i3))),((some (.cnot .i0 .i1 .i1 .i4)),(some (.x .i1 .i4))))),
  ((((some (.x .i0 .i7)),(some (.x .i0 .i6))),((some (.tempAnd .i0 .i7 .i0 .i6 .i1 .i6)),
  (some (.x .i0 .i6)))),(((some (.x .i0 .i7)),(some (.x .i0 .i5))),((some (.x .i0 .i4)),
  (some (.tempAnd .i0 .i5 .i0 .i4 .i1 .i7)))))))),(((((((some (.x .i0 .i4)),(some (.x .i0 .i5))),
  ((some (.x .i0 .i7)),(some (.cnot .i1 .i7 .i0 .i7)))),(((some (.cnot .i0 .i6 .i0 .i4)),
  (some (.cnot .i1 .i7 .i0 .i4))),((some (.tempAnd .i0 .i7 .i0 .i4 .i2 .i0)),
  (some (.cnot .i1 .i7 .i0 .i4))))),((((some (.cnot .i0 .i6 .i0 .i4)),
  (some (.cnot .i1 .i7 .i0 .i7))),((some (.x .i0 .i7)),(some (.cnot .i0 .i7 .i0 .i6)))),
  (((some (.cnot .i1 .i7 .i0 .i6)),(some (.cnot .i0 .i5 .i0 .i4))),((some (.cnot .i2 .i0 .i0 .i4)),
  (some (.tempAnd .i0 .i6 .i0 .i4 .i2 .i1)))))),(((((some (.cnot .i2 .i0 .i0 .i4)),
  (some (.cnot .i0 .i5 .i0 .i4))),((some (.cnot .i1 .i7 .i0 .i6)),(some (.cnot .i0 .i7 .i0 .i6)))),
  (((some (.x .i2 .i1)),(some (.cnot .i0 .i7 .i2 .i1))),((some (.cnot .i0 .i5 .i1 .i6)),
  (some (.cnot .i0 .i7 .i1 .i6))))),((((some (.tempAnd .i2 .i1 .i1 .i6 .i2 .i2)),
  (some (.cnot .i0 .i7 .i1 .i6))),((some (.cnot .i0 .i5 .i1 .i6)),(some (.cnot .i0 .i7 .i2 .i1)))),
  (((some (.x .i2 .i1)),(some (.tempAnd .i0 .i0 .i0 .i6 .i2 .i3))),
  ((some (.tempAnd .i0 .i0 .i0 .i7 .i2 .i4)),(some (.tempAnd .i0 .i1 .i0 .i6 .i2 .i5))))))),
  ((((((some (.tempAnd .i0 .i1 .i0 .i7 .i2 .i6)),(some (.tempAnd .i0 .i2 .i0 .i4 .i2 .i7))),
  ((some (.tempAnd .i0 .i2 .i0 .i5 .i3 .i0)),(some (.tempAnd .i0 .i3 .i0 .i5 .i3 .i1)))),
  (((some (.tempAnd .i0 .i3 .i0 .i4 .i3 .i2)),(some (.tempAnd .i0 .i0 .i0 .i4 .i3 .i3))),
  ((some (.tempAnd .i0 .i0 .i0 .i5 .i3 .i4)),(some (.tempAnd .i0 .i1 .i0 .i4 .i3 .i5))))),
  ((((some (.tempAnd .i0 .i1 .i0 .i5 .i3 .i6)),(some (.tempAnd .i0 .i2 .i0 .i6 .i3 .i7))),
  ((some (.tempAnd .i0 .i3 .i0 .i7 .i4 .i0)),(some (.cnot .i0 .i3 .i0 .i2)))),
  (((some (.cnot .i0 .i7 .i0 .i6)),(some (.tempAnd .i0 .i2 .i0 .i6 .i4 .i1))),
  ((some (.cnot .i0 .i7 .i0 .i6)),(some (.cnot .i0 .i3 .i0 .i2)))))),
  (((((some (.cnot .i3 .i7 .i4 .i1)),(some (.cnot .i4 .i0 .i4 .i1))),((some (.x .i1 .i0)),
  (some (.cnot .i0 .i2 .i1 .i0)))),(((some (.cnot .i0 .i3 .i1 .i0)),(some (.x .i1 .i6))),
  ((some (.cnot .i0 .i6 .i1 .i6)),(some (.cnot .i0 .i7 .i1 .i6))))),
  ((((some (.tempAnd .i1 .i0 .i1 .i6 .i4 .i2)),(some (.cnot .i0 .i7 .i1 .i6))),
  ((some (.cnot .i0 .i6 .i1 .i6)),(some (.x .i1 .i6)))),(((some (.cnot .i0 .i3 .i1 .i0)),
  (some (.cnot .i0 .i2 .i1 .i0))),((some (.x .i1 .i0)),(some (.cnot .i4 .i2 .i4 .i0))))))))),
  ((((((((some (.cnot .i1 .i5 .i1 .i4)),(some (.cnot .i1 .i5 .i1 .i2))),
  ((some (.cnot .i1 .i5 .i1 .i1)),(some (.cnot .i1 .i5 .i1 .i0)))),(((some (.cnot .i1 .i5 .i0 .i2)),
  (some (.cnot .i1 .i4 .i1 .i0))),((some (.cnot .i1 .i4 .i0 .i3)),(some (.cnot .i1 .i5 .i1 .i4))))),
  ((((some (.cnot .i1 .i4 .i1 .i5)),(some (.cnot .i1 .i5 .i1 .i4))),((some (.cnot .i1 .i3 .i1 .i2)),
  (some (.cnot .i1 .i3 .i1 .i1)))),(((some (.cnot .i1 .i2 .i1 .i5)),(some (.cnot .i1 .i2 .i1 .i3))),
  ((some (.cnot .i1 .i2 .i1 .i1)),(some (.cnot .i1 .i2 .i0 .i3)))))),
  (((((some (.cnot .i1 .i1 .i1 .i4)),(some (.cnot .i1 .i1 .i1 .i0))),
  ((some (.cnot .i1 .i1 .i0 .i2)),(some (.cnot .i1 .i0 .i1 .i2)))),(((some (.cnot .i1 .i0 .i1 .i1)),
  (some (.cnot .i0 .i3 .i1 .i5))),((some (.cnot .i0 .i3 .i1 .i4)),(some (.cnot .i0 .i3 .i0 .i2))))),
  ((((some (.cnot .i0 .i3 .i0 .i1)),(some (.cnot .i1 .i3 .i0 .i3))),((some (.cnot .i0 .i3 .i1 .i3)),
  (some (.cnot .i1 .i3 .i0 .i3)))),(((some (.cnot .i0 .i2 .i1 .i4)),(some (.cnot .i0 .i2 .i1 .i3))),
  ((some (.cnot .i0 .i2 .i1 .i2)),(some (.cnot .i0 .i2 .i1 .i1))))))),
  ((((((some (.cnot .i0 .i2 .i0 .i1)),(some (.cnot .i0 .i3 .i0 .i2))),
  ((some (.cnot .i0 .i2 .i0 .i3)),(some (.cnot .i0 .i3 .i0 .i2)))),(((some (.cnot .i0 .i1 .i1 .i3)),
  (some (.cnot .i0 .i1 .i1 .i1))),((some (.cnot .i0 .i2 .i0 .i1)),(some (.cnot .i0 .i1 .i0 .i2))))),
  ((((some (.cnot .i0 .i2 .i0 .i1)),(some (.cnot .i0 .i0 .i1 .i0))),((some (.cnot .i0 .i0 .i0 .i1)),
  (some (.x .i0 .i1)))),(((some (.x .i1 .i1)),(some (.x .i1 .i2))),((some (.cnot .i2 .i2 .i2 .i1)),
  (some (.cnot .i2 .i2 .i2 .i0)))))),(((((some (.cnot .i2 .i2 .i1 .i6)),
  (some (.cnot .i2 .i2 .i0 .i7))),((some (.cnot .i2 .i1 .i2 .i2)),(some (.cnot .i2 .i1 .i2 .i0)))),
  (((some (.cnot .i2 .i1 .i1 .i7)),(some (.cnot .i2 .i1 .i1 .i6))),((some (.cnot .i2 .i1 .i0 .i7)),
  (some (.cnot .i2 .i1 .i0 .i5))))),((((some (.cnot .i2 .i0 .i2 .i1)),
  (some (.cnot .i2 .i0 .i1 .i7))),((some (.cnot .i1 .i7 .i2 .i2)),(some (.cnot .i1 .i7 .i2 .i1)))),
  (((some (.cnot .i1 .i7 .i0 .i7)),(some (.cnot .i1 .i7 .i0 .i6))),((some (.cnot .i2 .i0 .i1 .i7)),
  (some (.cnot .i1 .i7 .i2 .i0)))))))),(((((((some (.cnot .i2 .i0 .i1 .i7)),
  (some (.cnot .i1 .i6 .i0 .i6))),((some (.cnot .i2 .i0 .i1 .i6)),(some (.cnot .i1 .i6 .i2 .i0)))),
  (((some (.cnot .i2 .i0 .i1 .i6)),(some (.cnot .i0 .i7 .i2 .i2))),((some (.cnot .i2 .i1 .i0 .i7)),
  (some (.cnot .i0 .i7 .i2 .i1))))),((((some (.cnot .i2 .i1 .i0 .i7)),
  (some (.cnot .i0 .i6 .i2 .i1))),((some (.cnot .i0 .i6 .i1 .i6)),(some (.cnot .i0 .i7 .i0 .i6)))),
  (((some (.cnot .i0 .i6 .i0 .i7)),(some (.cnot .i0 .i7 .i0 .i6))),((some (.cnot .i0 .i5 .i2 .i0)),
  (some (.cnot .i0 .i5 .i0 .i6)))))),(((((some (.cnot .i0 .i4 .i1 .i7)),
  (some (.cnot .i0 .i4 .i0 .i6))),((some (.x .i0 .i5)),(some (.x .i0 .i7)))),(((some (.x .i1 .i6)),
  (some (.x .i2 .i1))),((some (.cnot .i3 .i2 .i0 .i4)), none))),(((none, none),(none, none)),((none,
  none),(none, none))))),(((((none, none),(none, none)),((none, none),(none, none))),(((none, none),
  (none, none)),((none, none),(none, none)))),((((none, none),(none, none)),((none, none),(none,
  none))),(((none, none),(none, none)),((none, none),(none, none))))))))
def localSq34A : List LocalStep := (ls8 prog8_34).take 103
def localSq34B : List LocalStep := (ls8 prog8_34).drop 103
def localSq35A : List LocalStep := (ls8 prog8_35).take 107
def localSq35B : List LocalStep := (ls8 prog8_35).drop 107
/-- Pair a column weight with a 6-bit octal address. -/
def p57Slim_col (c : ℕ) (hi lo : OctIdx) : ℕ × BAddr 6 := (c, octAddrToB6 hi lo)
def localCols34 : List (ℕ × BAddr 6) := [
  p57Slim_col 0 .i0 .i0, p57Slim_col 2 .i0 .i1, p57Slim_col 2 .i0 .i2, p57Slim_col 3 .i0 .i3,
  p57Slim_col 4 .i1 .i0, p57Slim_col 5 .i3 .i2, p57Slim_col 5 .i1 .i1, p57Slim_col 6 .i3 .i4,
  p57Slim_col 6 .i1 .i2, p57Slim_col 7 .i2 .i2, p57Slim_col 7 .i2 .i6, p57Slim_col 7 .i3 .i3,
  p57Slim_col 7 .i3 .i5, p57Slim_col 7 .i1 .i3, p57Slim_col 8 .i2 .i3, p57Slim_col 8 .i2 .i4,
  p57Slim_col 8 .i2 .i7, p57Slim_col 8 .i3 .i1, p57Slim_col 8 .i0 .i4, p57Slim_col 9 .i2 .i5,
  p57Slim_col 9 .i3 .i0, p57Slim_col 9 .i3 .i6, p57Slim_col 10 .i4 .i0, p57Slim_col 10 .i0 .i5,
  p57Slim_col 10 .i0 .i6, p57Slim_col 11 .i3 .i7, p57Slim_col 11 .i0 .i7,
  p57Slim_col 12 .i4 .i1, p57Slim_col 12 .i1 .i5, p57Slim_col 13 .i1 .i6,
  p57Slim_col 14 .i1 .i7, p57Slim_col 15 .i2 .i0]
def localCols35 : List (ℕ × BAddr 6) := [
  p57Slim_col 0 .i0 .i0, p57Slim_col 2 .i0 .i1, p57Slim_col 3 .i0 .i2, p57Slim_col 4 .i0 .i3,
  p57Slim_col 5 .i3 .i3, p57Slim_col 5 .i1 .i0, p57Slim_col 6 .i3 .i4, p57Slim_col 6 .i3 .i5,
  p57Slim_col 6 .i1 .i1, p57Slim_col 7 .i2 .i3, p57Slim_col 7 .i2 .i7, p57Slim_col 7 .i3 .i6,
  p57Slim_col 7 .i1 .i2, p57Slim_col 8 .i2 .i4, p57Slim_col 8 .i2 .i5, p57Slim_col 8 .i3 .i0,
  p57Slim_col 8 .i0 .i4, p57Slim_col 9 .i2 .i6, p57Slim_col 9 .i3 .i1, p57Slim_col 9 .i3 .i2,
  p57Slim_col 9 .i3 .i7, p57Slim_col 10 .i4 .i1, p57Slim_col 10 .i0 .i5, p57Slim_col 10 .i0 .i6,
  p57Slim_col 11 .i4 .i0, p57Slim_col 11 .i0 .i7, p57Slim_col 12 .i4 .i2,
  p57Slim_col 12 .i1 .i6, p57Slim_col 13 .i1 .i7, p57Slim_col 14 .i2 .i0,
  p57Slim_col 15 .i2 .i1]
def colSumOct34 (tr : Oct2) : ℕ :=
  Nat.add (Bool.rec 0 1 (getOct2 tr .i0 .i0))
    (Nat.add (Bool.rec 0 4 (getOct2 tr .i0 .i1))
    (Nat.add (Bool.rec 0 4 (getOct2 tr .i0 .i2))
    (Nat.add (Bool.rec 0 8 (getOct2 tr .i0 .i3))
    (Nat.add (Bool.rec 0 16 (getOct2 tr .i1 .i0))
    (Nat.add (Bool.rec 0 32 (getOct2 tr .i3 .i2))
    (Nat.add (Bool.rec 0 32 (getOct2 tr .i1 .i1))
    (Nat.add (Bool.rec 0 64 (getOct2 tr .i3 .i4))
    (Nat.add (Bool.rec 0 64 (getOct2 tr .i1 .i2))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i2 .i2))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i2 .i6))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i3 .i3))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i3 .i5))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i1 .i3))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i2 .i3))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i2 .i4))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i2 .i7))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i3 .i1))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i0 .i4))
    (Nat.add (Bool.rec 0 512 (getOct2 tr .i2 .i5))
    (Nat.add (Bool.rec 0 512 (getOct2 tr .i3 .i0))
    (Nat.add (Bool.rec 0 512 (getOct2 tr .i3 .i6))
    (Nat.add (Bool.rec 0 1024 (getOct2 tr .i4 .i0))
    (Nat.add (Bool.rec 0 1024 (getOct2 tr .i0 .i5))
    (Nat.add (Bool.rec 0 1024 (getOct2 tr .i0 .i6))
    (Nat.add (Bool.rec 0 2048 (getOct2 tr .i3 .i7))
    (Nat.add (Bool.rec 0 2048 (getOct2 tr .i0 .i7))
    (Nat.add (Bool.rec 0 4096 (getOct2 tr .i4 .i1))
    (Nat.add (Bool.rec 0 4096 (getOct2 tr .i1 .i5))
    (Nat.add (Bool.rec 0 8192 (getOct2 tr .i1 .i6))
    (Nat.add (Bool.rec 0 16384 (getOct2 tr .i1 .i7))
    (Nat.add (Bool.rec 0 32768 (getOct2 tr .i2 .i0)) (0))))))))))))))))))))))))))))))))
def colSumOct35 (tr : Oct2) : ℕ :=
  Nat.add (Bool.rec 0 1 (getOct2 tr .i0 .i0))
    (Nat.add (Bool.rec 0 4 (getOct2 tr .i0 .i1))
    (Nat.add (Bool.rec 0 8 (getOct2 tr .i0 .i2))
    (Nat.add (Bool.rec 0 16 (getOct2 tr .i0 .i3))
    (Nat.add (Bool.rec 0 32 (getOct2 tr .i3 .i3))
    (Nat.add (Bool.rec 0 32 (getOct2 tr .i1 .i0))
    (Nat.add (Bool.rec 0 64 (getOct2 tr .i3 .i4))
    (Nat.add (Bool.rec 0 64 (getOct2 tr .i3 .i5))
    (Nat.add (Bool.rec 0 64 (getOct2 tr .i1 .i1))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i2 .i3))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i2 .i7))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i3 .i6))
    (Nat.add (Bool.rec 0 128 (getOct2 tr .i1 .i2))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i2 .i4))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i2 .i5))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i3 .i0))
    (Nat.add (Bool.rec 0 256 (getOct2 tr .i0 .i4))
    (Nat.add (Bool.rec 0 512 (getOct2 tr .i2 .i6))
    (Nat.add (Bool.rec 0 512 (getOct2 tr .i3 .i1))
    (Nat.add (Bool.rec 0 512 (getOct2 tr .i3 .i2))
    (Nat.add (Bool.rec 0 512 (getOct2 tr .i3 .i7))
    (Nat.add (Bool.rec 0 1024 (getOct2 tr .i4 .i1))
    (Nat.add (Bool.rec 0 1024 (getOct2 tr .i0 .i5))
    (Nat.add (Bool.rec 0 1024 (getOct2 tr .i0 .i6))
    (Nat.add (Bool.rec 0 2048 (getOct2 tr .i4 .i0))
    (Nat.add (Bool.rec 0 2048 (getOct2 tr .i0 .i7))
    (Nat.add (Bool.rec 0 4096 (getOct2 tr .i4 .i2))
    (Nat.add (Bool.rec 0 4096 (getOct2 tr .i1 .i6))
    (Nat.add (Bool.rec 0 8192 (getOct2 tr .i1 .i7))
    (Nat.add (Bool.rec 0 16384 (getOct2 tr .i2 .i0))
    (Nat.add (Bool.rec 0 32768 (getOct2 tr .i2 .i1)) (0)))))))))))))))))))))))))))))))
theorem bool_rec_eq_cond (b : Bool) (n : ℕ) :
    Bool.rec 0 n b = cond b n 0 := Bool.casesOn b rfl rfl
theorem colSumOct34_eq (tr : Oct2) :
    colSumOct34 tr = localColSum localCols34 (oct2ToB6 tr) := by
  dsimp only [colSumOct34, localCols34, p57Slim_col, localColSum, pow2Col]
  simp only [getOct2_eq tr, octAddrToB6, octIdxToB3, bool_rec_eq_cond]
theorem colSumOct35_eq (tr : Oct2) :
    colSumOct35 tr = localColSum localCols35 (oct2ToB6 tr) := by
  dsimp only [colSumOct35, localCols35, p57Slim_col, localColSum, pow2Col]
  simp only [getOct2_eq tr, octAddrToB6, octIdxToB3, bool_rec_eq_cond]
def fastB8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : ℕ := Nat.add (Bool.rec 0 1 b0) (Nat.add
    (Bool.rec 0 2 b1) (Nat.add (Bool.rec 0 4 b2) (Nat.add (Bool.rec 0 8 b3) (Nat.add (Bool.rec
    0 16 b4) (Nat.add (Bool.rec 0 32 b5) (Nat.add (Bool.rec 0 64 b6) (Bool.rec 0 128 b7)))))))
theorem fastB8_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    fastB8 b0 b1 b2 b3 b4 b5 b6 b7 = bool8Val b0 b1 b2 b3 b4 b5 b6 b7 := by
  dsimp only [fastB8, bool8Val]
  simp only [bool_rec_eq_cond]
theorem ev8_34_ff (b2 b3 b4 b5 b6 b7 : Bool) :
    ev8 (initOct2 false false b2 b3 b4 b5 b6 b7) prog8_34 colSumOct34 =
      Nat.mul (fastB8 false false b2 b3 b4 b5 b6 b7) (fastB8 false false b2 b3 b4 b5 b6 b7) := by
  cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
theorem ev8_34_ft (b2 b3 b4 b5 b6 b7 : Bool) :
    ev8 (initOct2 false true b2 b3 b4 b5 b6 b7) prog8_34 colSumOct34 =
      Nat.mul (fastB8 false true b2 b3 b4 b5 b6 b7) (fastB8 false true b2 b3 b4 b5 b6 b7) := by
  cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
theorem ev8_34_tf (b2 b3 b4 b5 b6 b7 : Bool) :
    ev8 (initOct2 true false b2 b3 b4 b5 b6 b7) prog8_34 colSumOct34 =
      Nat.mul (fastB8 true false b2 b3 b4 b5 b6 b7) (fastB8 true false b2 b3 b4 b5 b6 b7) := by
  cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
theorem ev8_34_tt (b2 b3 b4 b5 b6 b7 : Bool) :
    ev8 (initOct2 true true b2 b3 b4 b5 b6 b7) prog8_34 colSumOct34 =
      Nat.mul (fastB8 true true b2 b3 b4 b5 b6 b7) (fastB8 true true b2 b3 b4 b5 b6 b7) := by
  cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
theorem ev8_35_ff (b2 b3 b4 b5 b6 b7 : Bool) :
    ev8 (initOct2 false false b2 b3 b4 b5 b6 b7) prog8_35 colSumOct35 =
      Nat.mul (fastB8 false false b2 b3 b4 b5 b6 b7) (fastB8 false false b2 b3 b4 b5 b6 b7) := by
  cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
theorem ev8_35_ft (b2 b3 b4 b5 b6 b7 : Bool) :
    ev8 (initOct2 false true b2 b3 b4 b5 b6 b7) prog8_35 colSumOct35 =
      Nat.mul (fastB8 false true b2 b3 b4 b5 b6 b7) (fastB8 false true b2 b3 b4 b5 b6 b7) := by
  cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
theorem ev8_35_tf (b2 b3 b4 b5 b6 b7 : Bool) :
    ev8 (initOct2 true false b2 b3 b4 b5 b6 b7) prog8_35 colSumOct35 =
      Nat.mul (fastB8 true false b2 b3 b4 b5 b6 b7) (fastB8 true false b2 b3 b4 b5 b6 b7) := by
  cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
theorem ev8_35_tt (b2 b3 b4 b5 b6 b7 : Bool) :
    ev8 (initOct2 true true b2 b3 b4 b5 b6 b7) prog8_35 colSumOct35 =
      Nat.mul (fastB8 true true b2 b3 b4 b5 b6 b7) (fastB8 true true b2 b3 b4 b5 b6 b7) := by
  cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
theorem localSq34_spec (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    localColSum localCols34 (evalLocalSteps
      (evalLocalSteps (initSqTree b0 b1 b2 b3 b4 b5 b6 b7) localSq34A) localSq34B) =
      bool8Val b0 b1 b2 b3 b4 b5 b6 b7 * bool8Val b0 b1 b2 b3 b4 b5 b6 b7 := by
  rw [← evalLocalSteps_append, show localSq34A ++ localSq34B = ls8 prog8_34 from rfl,
    ← oct2ToB6_initOct2, ← p57Slim_ev_eq 8 _ prog8_34 colSumOct34 _ colSumOct34_eq, ← fastB8_eq]
  exact Bool.casesOn b0
    (Bool.casesOn b1 (ev8_34_ff b2 b3 b4 b5 b6 b7) (ev8_34_ft b2 b3 b4 b5 b6 b7))
    (Bool.casesOn b1 (ev8_34_tf b2 b3 b4 b5 b6 b7) (ev8_34_tt b2 b3 b4 b5 b6 b7))
theorem localSq35_spec (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    localColSum localCols35 (evalLocalSteps
      (evalLocalSteps (initSqTree b0 b1 b2 b3 b4 b5 b6 b7) localSq35A) localSq35B) =
      bool8Val b0 b1 b2 b3 b4 b5 b6 b7 * bool8Val b0 b1 b2 b3 b4 b5 b6 b7 := by
  rw [← evalLocalSteps_append, show localSq35A ++ localSq35B = ls8 prog8_35 from rfl,
    ← oct2ToB6_initOct2, ← p57Slim_ev_eq 8 _ prog8_35 colSumOct35 _ colSumOct35_eq, ← fastB8_eq]
  exact Bool.casesOn b0
    (Bool.casesOn b1 (ev8_35_ff b2 b3 b4 b5 b6 b7) (ev8_35_ft b2 b3 b4 b5 b6 b7))
    (Bool.casesOn b1 (ev8_35_tf b2 b3 b4 b5 b6 b7) (ev8_35_tt b2 b3 b4 b5 b6 b7))
def readBit437 (γ : BitAssignment 437) (q : ℕ) : ZMod 2 := if h : q < 437 then γ ⟨q, h⟩ else 0
@[simp] theorem readBit437_lt (γ : BitAssignment 437) {q : ℕ} (hq : q < 437) :
    readBit437 γ q = γ ⟨q, hq⟩ := dite_eq_left hq
def colListSum : List (ℕ × ℕ) → BitAssignment 437 → ℕ
  | [], _ => 0
  | (c, q) :: rest, γ => (readBit437 γ q).val * (2 ^ c) + colListSum rest γ
theorem colListSum_append :
    ∀ (xs ys : List (ℕ × ℕ)) (γ : BitAssignment 437),
      colListSum (xs ++ ys) γ = colListSum xs γ + colListSum ys γ
  | [], _, _ => by simp [colListSum]
  | (c, q) :: xs, ys, γ => by
      dsimp only [List.cons_append, colListSum]
      rw [colListSum_append xs ys γ]
      omega
theorem colListSum_congr {items : List (ℕ × ℕ)} {γ₁ γ₂ : BitAssignment 437}
    (h : ∀ p ∈ items, readBit437 γ₁ p.2 = readBit437 γ₂ p.2) :
    colListSum items γ₁ = colListSum items γ₂ := by
  induction items with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨c, q⟩
      dsimp only [colListSum]
      rw [h (c, q) (.head _), ih (fun p' hp' ↦ h p' (.tail _ hp'))]
def mapLocalStep (emb : BAddr 6 → ℕ) : LocalStep → P57Step
  | .x q => .x (emb q)
  | .cnot c t => .cnot (emb c) (emb t)
  | .tempAnd a b dst => .tempAnd (emb a) (emb b) (emb dst)
def mapLocalCols (emb : BAddr 6 → ℕ) : List (ℕ × BAddr 6) → List (ℕ × ℕ) :=
  List.map (fun p ↦ (p.1, emb p.2))
def wfLocalStep (L : ℕ) : LocalStep → Bool
  | .x q => baddrVal q < L
  | .cnot c t => (baddrVal c < L) && (baddrVal t < L) && (c != t)
  | .tempAnd a b dst =>
      (baddrVal a < L) && (baddrVal b < L) && (baddrVal dst < L) &&
      (a != b) && (a != dst) && (b != dst)
def wfLocalSteps (L : ℕ) : List LocalStep → Bool
  | [] => true
  | s :: ss => wfLocalStep L s && wfLocalSteps L ss
def wfLocalCols (L : ℕ) : List (ℕ × BAddr 6) → Bool
  | [] => true
  | (_, a) :: rest => (baddrVal a < L) && wfLocalCols L rest
def SimTree (L : ℕ) (emb : BAddr 6 → ℕ) (tr : BTree 6) (γ : BitAssignment 437) : Prop :=
  ∀ a : BAddr 6, baddrVal a < L → readBit437 γ (emb a) = b2z (tr.get a)
theorem p57Slim_simTree_update {L : ℕ} {emb : BAddr 6 → ℕ}
    (hemb_lt : ∀ a : BAddr 6, baddrVal a < L → emb a < 437)
    (hemb_inj : ∀ a₁ a₂ : BAddr 6,
      baddrVal a₁ < L → baddrVal a₂ < L → emb a₁ = emb a₂ → a₁ = a₂)
    {tr : BTree 6} {γ : BitAssignment 437} (hSim : SimTree L emb tr γ)
    {t : BAddr 6} (htL : baddrVal t < L) (vb : Bool) (vz : ZMod 2) (hv : vz = b2z vb) :
    SimTree L emb (tr.set t vb) (Function.update γ ⟨emb t, hemb_lt t htL⟩ vz) ∧
      (∀ u : Wire 437, (∀ a : BAddr 6, baddrVal a < L → u.val ≠ emb a) →
        Function.update γ ⟨emb t, hemb_lt t htL⟩ vz u = γ u) := by
  refine ⟨fun a haL ↦ ?_, fun u hu ↦ Function.update_of_ne (wire_ne_val (hu t htL)) _ _⟩
  rw [readBit437_lt _ (hemb_lt a haL)]
  by_cases hat : a = t
  · subst hat
    rw [Function.update_self, BTree.get_set_self, hv]
  · rw [Function.update_of_ne (wire_ne_val (fun he ↦ hat (hemb_inj a t haL htL he))),
      ← readBit437_lt γ (hemb_lt a haL), hSim a haL, BTree.get_set_ne tr _ hat]
theorem mapLocalStep_sim {L : ℕ} {emb : BAddr 6 → ℕ}
    (hemb_lt : ∀ a : BAddr 6, baddrVal a < L → emb a < 437) (hemb_inj : ∀ a₁ a₂ : BAddr 6,
    baddrVal a₁ < L → baddrVal a₂ < L → emb a₁ = emb a₂ → a₁ = a₂) {s : LocalStep}
    (hwf : wfLocalStep L s = true) {tr : BTree 6} {γ : BitAssignment 437}
    (hSim : SimTree L emb tr γ) : SimTree L emb (evalLocalStep tr s)
    (evalP57Step (mapLocalStep emb s) γ) ∧ (∀ u : Wire 437, (∀ a : BAddr 6, baddrVal a < L →
    u.val ≠ emb a) → evalP57Step (mapLocalStep emb s) γ u = γ u) := by
  cases s with
  | x q =>
      dsimp [wfLocalStep] at hwf
      simp only [decide_eq_true_eq] at hwf
      dsimp only [mapLocalStep, evalP57Step, evalLocalStep]
      rw [dite_eq_left (hemb_lt q hwf)]
      exact p57Slim_simTree_update hemb_lt hemb_inj hSim hwf _ _
        (by rw [← readBit437_lt γ (hemb_lt q hwf), hSim q hwf, b2z_not])
  | cnot c t =>
      dsimp [wfLocalStep] at hwf
      simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hwf
      obtain ⟨⟨hcL, htL⟩, hct⟩ := hwf
      dsimp only [mapLocalStep, evalP57Step, evalLocalStep]
      rw [dite_eq_left ⟨hemb_lt c hcL, hemb_lt t htL, fun he ↦ hct (hemb_inj c t hcL htL he)⟩]
      exact p57Slim_simTree_update hemb_lt hemb_inj hSim htL _ _
        (by rw [← readBit437_lt γ (hemb_lt t htL), ← readBit437_lt γ (hemb_lt c hcL),
              hSim t htL, hSim c hcL, b2z_bxor])
  | tempAnd a b dst =>
      dsimp [wfLocalStep] at hwf
      simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hwf
      obtain ⟨⟨⟨⟨⟨haL, hbL⟩, hdL⟩, hab⟩, had⟩, hbd⟩ := hwf
      dsimp only [mapLocalStep, evalP57Step, evalLocalStep]
      rw [dite_eq_left ⟨hemb_lt a haL, hemb_lt b hbL, hemb_lt dst hdL,
        fun he ↦ hab (hemb_inj a b haL hbL he), fun he ↦ had (hemb_inj a dst haL hdL he),
        fun he ↦ hbd (hemb_inj b dst hbL hdL he)⟩]
      exact p57Slim_simTree_update hemb_lt hemb_inj hSim hdL _ _
        (by rw [← readBit437_lt γ (hemb_lt dst hdL), ← readBit437_lt γ (hemb_lt a haL),
              ← readBit437_lt γ (hemb_lt b hbL), hSim dst hdL, hSim a haL, hSim b hbL,
              b2z_and_bxor])
theorem mapLocalSteps_sim {L : ℕ} {emb : BAddr 6 → ℕ}
    (hemb_lt : ∀ a : BAddr 6, baddrVal a < L → emb a < 437)
    (hemb_inj : ∀ a₁ a₂ : BAddr 6, baddrVal a₁ < L → baddrVal a₂ < L → emb a₁ = emb a₂ → a₁ = a₂) :
    ∀ {ss : List LocalStep} (_hwf : wfLocalSteps L ss = true)
      {tr : BTree 6} {γ : BitAssignment 437} (_hSim : SimTree L emb tr γ),
      SimTree L emb (evalLocalSteps tr ss) ((buildP57Ctx (ss.map (mapLocalStep emb))).fwdBits γ) ∧
        (∀ u : Wire 437, (∀ a : BAddr 6, baddrVal a < L → u.val ≠ emb a) →
          (buildP57Ctx (ss.map (mapLocalStep emb))).fwdBits γ u = γ u)
  | [], _, _, _, hSim => ⟨hSim, fun _ _ ↦ rfl⟩
  | s :: ss, hwf, tr, γ, hSim => by
      dsimp [wfLocalSteps] at hwf
      simp only [Bool.and_eq_true] at hwf
      obtain ⟨hs1, hnon1⟩ := mapLocalStep_sim hemb_lt hemb_inj hwf.1 hSim
      obtain ⟨hs2, hnon2⟩ := mapLocalSteps_sim hemb_lt hemb_inj hwf.2 hs1
      rw [List.map_cons, buildP57Ctx_fwdBits, evalP57Steps, ← buildP57Ctx_fwdBits]
      exact ⟨hs2, fun u hu ↦ (hnon2 u hu).trans (hnon1 u hu)⟩
theorem colListSum_mapLocalCols {L : ℕ} {emb : BAddr 6 → ℕ} {tr : BTree 6} {γ : BitAssignment 437}
    (hSim : SimTree L emb tr γ) :
    ∀ {cols : List (ℕ × BAddr 6)}, wfLocalCols L cols = true →
      colListSum (mapLocalCols emb cols) γ = localColSum cols tr
  | [], _ => rfl
  | (c, a) :: rest, hwf => by
      dsimp [wfLocalCols] at hwf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
      change (readBit437 γ (emb a)).val * (2 ^ c) + colListSum (mapLocalCols emb rest) γ =
        Nat.add (cond (tr.get a) (pow2Col c) 0) (localColSum rest tr)
      rw [Nat.add_eq, hSim a hwf.1, colListSum_mapLocalCols hSim hwf.2, ← pow2Col_eq c]
      cases tr.get a <;> simp [b2z, cond]
def mkAxisEmb (w : Fin 3) (curStart : ℕ) (a : BAddr 6) : ℕ :=
  let idx := baddrVal a
  if idx < 7 then 177 + 7 * w.val + idx
  else if idx == 7 then 275 + w.val
  else curStart + (idx - 8)
def embAx0 : BAddr 6 → ℕ := mkAxisEmb 0 278
def embAx1 : BAddr 6 → ℕ := mkAxisEmb 1 304
def embAx2 : BAddr 6 → ℕ := mkAxisEmb 2 330
theorem mkAxisEmb_init_sim (w : Fin 3) (curStart L : ℕ) (hcur : 278 ≤ curStart)
    (hend : curStart + (L - 8) ≤ 437) (γ : BitAssignment 437)
    (hcl : cleanRem 437 (437 - curStart) γ) : SimTree L (mkAxisEmb w curStart) (initSqTree
    (z2b (γ (d8Wire w 0))) (z2b (γ (d8Wire w 1))) (z2b (γ (d8Wire w 2))) (z2b (γ (d8Wire w
    3))) (z2b (γ (d8Wire w 4))) (z2b (γ (d8Wire w 5))) (z2b (γ (d8Wire w 6))) (z2b (γ (d8Wire
    w 7)))) γ := by
  intro a haL
  by_cases hge8 : 8 ≤ baddrVal a
  · rw [initSqTree_get_ge8 _ _ _ _ _ _ _ _ a hge8]
    have h1 : ¬ baddrVal a < 7 := by omega
    have h2 : (baddrVal a == 7) = false := beq_false_of_ne (by omega)
    dsimp only [mkAxisEmb]
    rw [ite_eq_right h1, h2]
    change readBit437 γ (curStart + (baddrVal a - 8)) = 0
    have hlt437 : curStart + (baddrVal a - 8) < 437 := by omega
    rw [readBit437_lt _ hlt437]
    exact hcl ⟨curStart + (baddrVal a - 8), hlt437⟩ (by dsimp; omega)
  · rcases a with _ | ⟨bit5, _ | ⟨bit4, _ | ⟨bit3, _ | ⟨bit2, _ | ⟨bit1, _ | ⟨bit0, _ | _⟩⟩⟩⟩⟩⟩
    cases bit5
    · cases bit4
      · cases bit3
        · cases bit2 <;> cases bit1 <;> cases bit0
          · change readBit437 γ (177 + 7 * w.val + 0) = b2z (z2b (γ (d8Wire w 0)))
            rw [b2z_z2b, readBit437_lt _ (by omega)]; fin_cases w <;> rfl
          · change readBit437 γ (177 + 7 * w.val + 1) = b2z (z2b (γ (d8Wire w 1)))
            rw [b2z_z2b, readBit437_lt _ (by omega)]; fin_cases w <;> rfl
          · change readBit437 γ (177 + 7 * w.val + 2) = b2z (z2b (γ (d8Wire w 2)))
            rw [b2z_z2b, readBit437_lt _ (by omega)]; fin_cases w <;> rfl
          · change readBit437 γ (177 + 7 * w.val + 3) = b2z (z2b (γ (d8Wire w 3)))
            rw [b2z_z2b, readBit437_lt _ (by omega)]; fin_cases w <;> rfl
          · change readBit437 γ (177 + 7 * w.val + 4) = b2z (z2b (γ (d8Wire w 4)))
            rw [b2z_z2b, readBit437_lt _ (by omega)]; fin_cases w <;> rfl
          · change readBit437 γ (177 + 7 * w.val + 5) = b2z (z2b (γ (d8Wire w 5)))
            rw [b2z_z2b, readBit437_lt _ (by omega)]; fin_cases w <;> rfl
          · change readBit437 γ (177 + 7 * w.val + 6) = b2z (z2b (γ (d8Wire w 6)))
            rw [b2z_z2b, readBit437_lt _ (by omega)]; fin_cases w <;> rfl
          · change readBit437 γ (275 + w.val) = b2z (z2b (γ (d8Wire w (Fin.last 7))))
            rw [b2z_z2b, readBit437_lt _ (by omega)]; fin_cases w <;> rfl
        · exfalso; simp only [baddrVal, Bool.cond_false, Bool.cond_true] at hge8; omega
      · exfalso; simp only [baddrVal, Bool.cond_false, Bool.cond_true] at hge8; omega
    · exfalso; simp only [baddrVal, Bool.cond_true] at hge8; omega
def checkEmbProps (L : ℕ) (emb : BAddr 6 → ℕ) : Bool :=
  allBAddr (fun a₁ ↦
    if baddrVal a₁ < L then
      (emb a₁ < 437) &&
      allBAddr (fun a₂ ↦
        if baddrVal a₂ < L then (emb a₁ != emb a₂) || (a₁ == a₂) else true)
    else true)
theorem of_checkEmbProps {L : ℕ} {emb : BAddr 6 → ℕ} (h : checkEmbProps L emb = true) :
    (∀ a : BAddr 6, baddrVal a < L → emb a < 437) ∧
      (∀ a₁ a₂ : BAddr 6, baddrVal a₁ < L → baddrVal a₂ < L → emb a₁ = emb a₂ → a₁ = a₂) := by
  refine ⟨fun a ha ↦ ?_, fun a₁ a₂ h1 h2 heq ↦ ?_⟩
  · have hA := of_allBAddr h a
    simp only [ha, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hA
    exact hA.1
  · have hA1 := of_allBAddr h a₁
    simp only [h1, ↓reduceIte, Bool.and_eq_true] at hA1
    have hA2 := of_allBAddr hA1.2 a₂
    simp only [h2, ↓reduceIte, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hA2
    exact hA2.elim (absurd heq) id
def K_ax0A : TempCtx 437 := buildP57Ctx (localSq34A.map (mapLocalStep embAx0))
def K_ax0B : TempCtx 437 := buildP57Ctx (localSq34B.map (mapLocalStep embAx0))
def K_ax0 : TempCtx 437 := K_ax0A.append K_ax0B
def K_ax1A : TempCtx 437 := buildP57Ctx (localSq34A.map (mapLocalStep embAx1))
def K_ax1B : TempCtx 437 := buildP57Ctx (localSq34B.map (mapLocalStep embAx1))
def K_ax1 : TempCtx 437 := K_ax1A.append K_ax1B
def K_ax2A : TempCtx 437 := buildP57Ctx (localSq35A.map (mapLocalStep embAx2))
def K_ax2B : TempCtx 437 := buildP57Ctx (localSq35B.map (mapLocalStep embAx2))
def K_ax2 : TempCtx 437 := K_ax2A.append K_ax2B
theorem K_ax0_pkg : P57CtxPkg 278 304 26 K_ax0 :=
  (buildP57Ctx_pkg
      (by decide : wfP57Steps 278 (localSq34A.map (mapLocalStep embAx0)) = some (300, 22))).append
    (buildP57Ctx_pkg
      (by decide : wfP57Steps 300 (localSq34B.map (mapLocalStep embAx0)) = some (304, 4)))
theorem K_ax1_pkg : P57CtxPkg 304 330 26 K_ax1 :=
  (buildP57Ctx_pkg
      (by decide : wfP57Steps 304 (localSq34A.map (mapLocalStep embAx1)) = some (326, 22))).append
    (buildP57Ctx_pkg
      (by decide : wfP57Steps 326 (localSq34B.map (mapLocalStep embAx1)) = some (330, 4)))
theorem K_ax2_pkg : P57CtxPkg 330 357 27 K_ax2 :=
  (buildP57Ctx_pkg
      (by decide : wfP57Steps 330 (localSq35A.map (mapLocalStep embAx2)) = some (355, 25))).append
    (buildP57Ctx_pkg
      (by decide : wfP57Steps 355 (localSq35B.map (mapLocalStep embAx2)) = some (357, 2)))
theorem p57Slim_ax_spec (w : Fin 3) (cur L : ℕ) (hcur : 278 ≤ cur)
    (hend : cur + (L - 8) ≤ 437) (sqA sqB : List LocalStep) (cols : List (ℕ × BAddr 6))
    (hEmb : checkEmbProps L (mkAxisEmb w cur) = true)
    (hwfA : wfLocalSteps L sqA = true) (hwfB : wfLocalSteps L sqB = true)
    (hwfC : wfLocalCols L cols = true)
    (hSq : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      localColSum cols (evalLocalSteps (evalLocalSteps
        (initSqTree b0 b1 b2 b3 b4 b5 b6 b7) sqA) sqB) =
        bool8Val b0 b1 b2 b3 b4 b5 b6 b7 * bool8Val b0 b1 b2 b3 b4 b5 b6 b7)
    (γ : BitAssignment 437) (hcl : cleanRem 437 (437 - cur) γ) :
    let K := (buildP57Ctx (sqA.map (mapLocalStep (mkAxisEmb w cur)))).append
      (buildP57Ctx (sqB.map (mapLocalStep (mkAxisEmb w cur))))
    let d := bitsVal (fun k : Fin 8 ↦ γ (d8Wire w k))
    colListSum (mapLocalCols (mkAxisEmb w cur) cols) (K.fwdBits γ) = d * d ∧
      ∀ u : Wire 437, (∀ a : BAddr 6, baddrVal a < L → u.val ≠ mkAxisEmb w cur a) →
        K.fwdBits γ u = γ u := by
  obtain ⟨hLt, hInj⟩ := of_checkEmbProps hEmb
  obtain ⟨hSim1, hNon1⟩ := mapLocalSteps_sim hLt hInj hwfA
    (mkAxisEmb_init_sim w cur L hcur hend γ hcl)
  obtain ⟨hSim2, hNon2⟩ := mapLocalSteps_sim hLt hInj hwfB hSim1
  intro K d
  dsimp only [K]
  rw [TempCtx.append_fwdBits, colListSum_mapLocalCols hSim2 hwfC, hSq,
    bool8Val_eq_bitsVal (fun k : Fin 8 ↦ γ (d8Wire w k))]
  exact ⟨rfl, fun u hu ↦ (hNon2 u hu).trans (hNon1 u hu)⟩
theorem K_ax0_spec (γ : BitAssignment 437) (hcl : cleanRem 437 (437 - 278) γ) :
    let d := bitsVal (fun k : Fin 8 ↦ γ (d8Wire 0 k))
    colListSum (mapLocalCols embAx0 localCols34) (K_ax0.fwdBits γ) = d * d ∧
      ∀ u : Wire 437, (∀ a : BAddr 6, baddrVal a < 34 → u.val ≠ embAx0 a) →
        K_ax0.fwdBits γ u = γ u :=
  p57Slim_ax_spec 0 278 34 (by decide) (by decide) localSq34A localSq34B localCols34
    (by decide) (by decide) (by decide) (by decide) localSq34_spec γ hcl
theorem K_ax1_spec (γ : BitAssignment 437) (hcl : cleanRem 437 (437 - 304) γ) :
    let d := bitsVal (fun k : Fin 8 ↦ γ (d8Wire 1 k))
    colListSum (mapLocalCols embAx1 localCols34) (K_ax1.fwdBits γ) = d * d ∧
      ∀ u : Wire 437, (∀ a : BAddr 6, baddrVal a < 34 → u.val ≠ embAx1 a) →
        K_ax1.fwdBits γ u = γ u :=
  p57Slim_ax_spec 1 304 34 (by decide) (by decide) localSq34A localSq34B localCols34
    (by decide) (by decide) (by decide) (by decide) localSq34_spec γ hcl
theorem K_ax2_spec (γ : BitAssignment 437) (hcl : cleanRem 437 (437 - 330) γ) :
    let d := bitsVal (fun k : Fin 8 ↦ γ (d8Wire 2 k))
    colListSum (mapLocalCols embAx2 localCols35) (K_ax2.fwdBits γ) = d * d ∧
      ∀ u : Wire 437, (∀ a : BAddr 6, baddrVal a < 35 → u.val ≠ embAx2 a) →
        K_ax2.fwdBits γ u = γ u :=
  p57Slim_ax_spec 2 330 35 (by decide) (by decide) localSq35A localSq35B localCols35
    (by decide) (by decide) (by decide) (by decide) localSq35_spec γ hcl
def preRedItems95 : List (ℕ × ℕ) := [(0,177),(2,178),(2,179),(3,180),(4,278),(5,296),(5,279),(6,
  298),(6,280),(7,288),(7,292),(7,297),(7,299),(7,281),(8,289),(8,290),(8,293),(8,295),(8,181),(9,
  291),(9,294),(9,300),(10,302),(10,182),(10,183),(11,301),(11,275),(12,303),(12,283),(13,284),(14,
  285),(15,286),(0,184),(2,185),(2,186),(3,187),(4,304),(5,322),(5,305),(6,324),(6,306),(7,314),(7,
  318),(7,323),(7,325),(7,307),(8,315),(8,316),(8,319),(8,321),(8,188),(9,317),(9,320),(9,326),(10,
  328),(10,189),(10,190),(11,327),(11,276),(12,329),(12,309),(13,310),(14,311),(15,312),(0,191),(2,
  192),(3,193),(4,194),(5,349),(5,330),(6,350),(6,351),(6,331),(7,341),(7,345),(7,352),(7,332),(8,
  342),(8,343),(8,346),(8,195),(9,344),(9,347),(9,348),(9,353),(10,355),(10,196),(10,197),(11,354),
  (11,277),(12,356),(12,336),(13,337),(14,338),(15,339)]
theorem preRedItems95_eq : preRedItems95 = mapLocalCols embAx0 localCols34 ++
    mapLocalCols embAx1 localCols34 ++ mapLocalCols embAx2 localCols35 := by decide
def K_preRed82 : TempCtx 437 := K_wrap.append (K_ax0.append (K_ax1.append K_ax2))
theorem K_preRed82_pkg : P57CtxPkg 275 357 82 K_preRed82 :=
  K_wrap_pkg.append (K_ax0_pkg.append (K_ax1_pkg.append K_ax2_pkg))
def checkDisjFromEmb (L : ℕ) (emb : BAddr 6 → ℕ) (qs : List ℕ) : Bool :=
  qs.all (fun q ↦ (q < 437) && allBAddr (fun a ↦ if baddrVal a < L then q != emb a else true))
theorem of_checkDisjFromEmb {L : ℕ} {emb : BAddr 6 → ℕ} {qs : List ℕ}
    (h : checkDisjFromEmb L emb qs = true) {q : ℕ} (hq : q ∈ qs) :
    q < 437 ∧ ∀ a : BAddr 6, baddrVal a < L → q ≠ emb a := by
  have h1 := List.all_eq_true.mp h q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨h1.1, fun a ha ↦ ?_⟩
  have h2 := of_allBAddr h1.2 a
  simpa [ha] using h2
theorem K_preRed82_spec (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β) :
    cleanRem 437 (437 - 357) (K_preRed82.fwdBits β) ∧
      colListSum preRedItems95 (K_preRed82.fwdBits β) = sTrueRawValPBuf β := by
  refine ⟨K_preRed82_pkg.clean β hβ, ?_⟩
  obtain ⟨hcl1, hd_wrap⟩ := K_wrap_spec β hβ
  let β1 := K_wrap.fwdBits β
  let β2 := K_ax0.fwdBits β1
  let β3 := K_ax1.fwdBits β2
  let β4 := K_ax2.fwdBits β3
  obtain ⟨hSq0, hNon0⟩ := K_ax0_spec β1 hcl1
  obtain ⟨hSq1, hNon1⟩ := K_ax1_spec β2 (K_ax0_pkg.clean β1 hcl1)
  obtain ⟨hSq2, hNon2⟩ := K_ax2_spec β3 (K_ax1_pkg.clean β2 (K_ax0_pkg.clean β1 hcl1))
  change colListSum preRedItems95 ((K_wrap.append (K_ax0.append (K_ax1.append K_ax2))).fwdBits β) =
    _
  rw [TempCtx.append_fwdBits, TempCtx.append_fwdBits, TempCtx.append_fwdBits,
    preRedItems95_eq, colListSum_append, colListSum_append]
  have hd1_eq : (fun k : Fin 8 ↦ β2 (d8Wire 1 k)) = (fun k : Fin 8 ↦ β1 (d8Wire 1 k)) :=
    funext fun k ↦ hNon0 (d8Wire 1 k) (of_checkDisjFromEmb (by decide)
      (show (d8Wire 1 k).val ∈ [184, 185, 186, 187, 188, 189, 190, 276] by
        revert k
        decide)).2
  have hd2_eq : (fun k : Fin 8 ↦ β3 (d8Wire 2 k)) = (fun k : Fin 8 ↦ β1 (d8Wire 2 k)) :=
    funext fun k ↦ by
      have hm : (d8Wire 2 k).val ∈ [191, 192, 193, 194, 195, 196, 197, 277] := by
        revert k
        decide
      exact (hNon1 (d8Wire 2 k) (of_checkDisjFromEmb (by decide) hm).2).trans
        (hNon0 (d8Wire 2 k) (of_checkDisjFromEmb (by decide) hm).2)
  have hCols0_eq : colListSum (mapLocalCols embAx0 localCols34) β4 =
      colListSum (mapLocalCols embAx0 localCols34) β2 := colListSum_congr fun p hp ↦ by
    have hm := List.mem_map_of_mem (f := Prod.snd) hp
    obtain ⟨hq437, hA2⟩ := of_checkDisjFromEmb (L := 35) (emb := embAx2) (by decide) hm
    obtain ⟨_, hA1⟩ := of_checkDisjFromEmb (L := 34) (emb := embAx1) (by decide) hm
    rw [readBit437_lt _ hq437, readBit437_lt _ hq437]
    exact (hNon2 ⟨p.2, hq437⟩ hA2).trans (hNon1 ⟨p.2, hq437⟩ hA1)
  have hCols1_eq : colListSum (mapLocalCols embAx1 localCols34) β4 =
      colListSum (mapLocalCols embAx1 localCols34) β3 := colListSum_congr fun p hp ↦ by
    have hm := List.mem_map_of_mem (f := Prod.snd) hp
    obtain ⟨hq437, hA2⟩ := of_checkDisjFromEmb (L := 35) (emb := embAx2) (by decide) hm
    rw [readBit437_lt _ hq437, readBit437_lt _ hq437]
    exact hNon2 ⟨p.2, hq437⟩ hA2
  rw [hCols0_eq, hCols1_eq, hSq0, hSq1, hSq2, hd1_eq, hd2_eq, hd_wrap 0, hd_wrap 1, hd_wrap 2]
  unfold sTrueRawValPBuf
  rw [Fin.sum_univ_three]
inductive ColRedOp : Type
  | fa (col a b cin cout : ℕ)
  | ha (col a b cout : ℕ)
def colRedOpSteps : ColRedOp → List P57Step
  | .fa _ a b cin cout =>
      [.cnot cin a, .cnot cin b, .tempAnd a b cout, .cnot cin b, .cnot b a, .cnot cin cout]
  | .ha _ a b cout =>
      [.tempAnd a b cout, .cnot b a]
def buildColRedCtx : List ColRedOp → TempCtx 437
  | [] => .hole
  | op :: ops => (buildP57Ctx (colRedOpSteps op)).append (buildColRedCtx ops)
def notMemSnd (w : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | (_, u) :: rest => (w != u) && notMemSnd w rest
def wfItems (cur : ℕ) : List (ℕ × ℕ) → Bool
  | [] => cur ≤ 437
  | (_, w) :: rest => (w < cur) && notMemSnd w rest && wfItems cur rest
theorem wfItems_cur_le : ∀ {cur : ℕ} {items : List (ℕ × ℕ)},
    wfItems cur items = true → cur ≤ 437
  | _, [], h => by simpa [wfItems] using h
  | cur, _ :: rest, h => by
      dsimp [wfItems] at h; simp only [Bool.and_eq_true] at h
      exact wfItems_cur_le h.2
theorem wfItems_lt : ∀ {cur : ℕ} {items : List (ℕ × ℕ)},
    wfItems cur items = true → ∀ p ∈ items, p.2 < cur
  | _, [], _, _, hp => nomatch hp
  | cur, (c, w) :: rest, h, p, hp => by
      dsimp [wfItems] at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.mp hp with rfl | hrest
      · exact h.1.1
      · exact wfItems_lt h.2 p hrest
theorem notMemSnd_true : ∀ {w : ℕ} {items : List (ℕ × ℕ)},
    notMemSnd w items = true → ∀ p ∈ items, w ≠ p.2
  | _, [], _, _, hp => nomatch hp
  | w, (c, u) :: rest, h, p, hp => by
      dsimp [notMemSnd] at h; simp only [Bool.and_eq_true, bne_iff_ne] at h
      rcases List.mem_cons.mp hp with rfl | hrest
      · exact h.1
      · exact notMemSnd_true h.2 p hrest
theorem notMemSnd_of_ge {cur z : ℕ} {items : List (ℕ × ℕ)} (hwf : wfItems cur items = true)
    (hge : cur ≤ z) : notMemSnd z items = true := by
  induction items with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨c, w⟩
      dsimp [wfItems] at hwf; simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
      dsimp [notMemSnd]
      simp only [Bool.and_eq_true, bne_iff_ne]
      exact ⟨by omega, ih hwf.2⟩
theorem wfItems_mono {c₁ c₂ : ℕ} (hle : c₁ ≤ c₂) (h437 : c₂ ≤ 437) :
    ∀ {items : List (ℕ × ℕ)}, wfItems c₁ items = true → wfItems c₂ items = true
  | [], _ => decide_eq_true h437
  | (c, w) :: rest, h => by
      dsimp [wfItems] at h ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      exact ⟨⟨lt_of_lt_of_le h.1.1 hle, h.1.2⟩, wfItems_mono hle h437 h.2⟩
def removeOne (col w : ℕ) : List (ℕ × ℕ) → Option (List (ℕ × ℕ))
  | [] => none
  | (c, u) :: rest =>
      if (c == col) && (u == w) then
        some rest
      else
        match removeOne col w rest with
        | none => none
        | some rest' => some ((c, u) :: rest')
theorem removeOne_none_of_notMemSnd :
    ∀ {col w : ℕ} {items : List (ℕ × ℕ)},
      notMemSnd w items = true → removeOne col w items = none
  | _, _, [], _ => rfl
  | col, w, (c, u) :: tail, h => by
      dsimp [notMemSnd] at h
      simp only [Bool.and_eq_true, bne_iff_ne] at h
      have hne : ((c == col) && (u == w)) = false := by
        cases (c == col) <;> simp [beq_false_of_ne h.1.symm]
      dsimp [removeOne]
      rw [hne]
      simp [removeOne_none_of_notMemSnd h.2]
theorem removeOne_spec :
    ∀ {cur col w : ℕ} {items rest : List (ℕ × ℕ)},
      wfItems cur items = true →
      removeOne col w items = some rest →
      w < cur ∧
        notMemSnd w rest = true ∧
        (∀ z : ℕ, notMemSnd z items = true → notMemSnd z rest = true) ∧
        wfItems cur rest = true ∧
        (∀ γ : BitAssignment 437,
          colListSum items γ = (readBit437 γ w).val * (2 ^ col) + colListSum rest γ)
  | _, _, _, [], _, _, hr => nomatch hr
  | cur, col, w, (c, u) :: tail, rest, hwf, hr => by
      dsimp [wfItems] at hwf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
      obtain ⟨⟨hu_lt, hnu⟩, hwf_tail⟩ := hwf
      dsimp [removeOne] at hr
      split_ifs at hr with heq
      · cases hr
        simp only [Bool.and_eq_true, beq_iff_eq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨hu_lt, hnu, fun z hz ↦ (Bool.and_eq_true _ _).mp hz |>.2, hwf_tail, fun _ ↦ rfl⟩
      · rcases hrec : removeOne col w tail with _ | rest'
        · simp [hrec] at hr
        · rw [hrec] at hr
          cases hr
          obtain ⟨hw_lt, hnw_r, hpres, hwf_r, hsum_r⟩ := removeOne_spec hwf_tail hrec
          have hwu : w ≠ u := fun h ↦ by
            rw [h, removeOne_none_of_notMemSnd hnu] at hrec
            cases hrec
          refine ⟨hw_lt, Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr hwu, hnw_r⟩,
            fun z hz ↦ Bool.and_eq_true_iff.mpr
              ⟨((Bool.and_eq_true _ _).mp hz).1, hpres z ((Bool.and_eq_true _ _).mp hz).2⟩,
            Bool.and_eq_true_iff.mpr
              ⟨Bool.and_eq_true_iff.mpr ⟨decide_eq_true hu_lt, hpres u hnu⟩, hwf_r⟩,
            fun γ ↦ by
              dsimp [colListSum]
              rw [hsum_r γ]
              omega⟩
def applyColRedOp (cur : ℕ) (op : ColRedOp) (items : List (ℕ × ℕ)) :
    Option (ℕ × List (ℕ × ℕ)) :=
  match op with
  | .fa col a b cin cout =>
      if (cout == cur) && (cur + 1 ≤ 437) && (a != b) && (a != cin) && (b != cin) &&
          !isSTrueNat a && !isSTrueNat b && !isSTrueNat cin && !isSTrueNat cur then
        match removeOne col a items with
        | none => none
        | some items1 => match removeOne col b items1 with
          | none => none
          | some items2 => match removeOne col cin items2 with
            | none => none
            | some items3 => some (cur + 1, (col, a) :: (col + 1, cur) :: items3)
      else none
  | .ha col a b cout =>
      if (cout == cur) && (cur + 1 ≤ 437) && (a != b) &&
          !isSTrueNat a && !isSTrueNat b && !isSTrueNat cur then
        match removeOne col a items with
        | none => none
        | some items1 => match removeOne col b items1 with
          | none => none
          | some items2 => some (cur + 1, (col, a) :: (col + 1, cur) :: items2)
      else none
def applyColRedOps : ℕ → List ColRedOp → List (ℕ × ℕ) → Option (ℕ × List (ℕ × ℕ))
  | cur, [], items => some (cur, items)
  | cur, op :: ops, items => match applyColRedOp cur op items with
    | none => none
    | some (cur1, items1) => applyColRedOps cur1 ops items1
theorem fa_zmod2_id (xa xb xc : ZMod 2) : (((xb + xc) + xc) = xb) ∧ ((((xa + xc) + xb).val + 2
    * (((0 : ZMod 2) + (xa + xc) * (xb + xc)) + xc).val) = xa.val + xb.val + xc.val) := by
  revert xa xb xc
  decide
theorem ha_zmod2_id (xa xb : ZMod 2) :
    ((xa + xb).val + 2 * ((0 : ZMod 2) + xa * xb).val) = xa.val + xb.val := by
  revert xa xb
  decide
theorem wfP57Steps_fa {cur col a b cin : ℕ} (ha : a < cur) (hb : b < cur) (hc : cin < cur)
    (hle : cur + 1 ≤ 437) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin)
    (hna : isSTrueNat a = false) (hnb : isSTrueNat b = false) (hnc : isSTrueNat cin = false)
    (hnd : isSTrueNat cur = false) : wfP57Steps cur (colRedOpSteps (.fa col a b cin cur)) =
    some (cur + 1, 1) := by
  simp [colRedOpSteps, wfP57Steps, wfP57Step, ha, hb, hc, hle,
    show cur ≤ 437 by omega, show a < cur + 1 by omega, show b < cur + 1 by omega,
    show cin < cur + 1 by omega, show cur < cur + 1 by omega,
    hab, hac.symm, hbc.symm, hab.symm, show cin ≠ cur by omega, hna, hnb, hnc, hnd]
theorem wfP57Steps_ha {cur col a b : ℕ} (ha : a < cur) (hb : b < cur) (hle : cur + 1 ≤ 437)
    (hab : a ≠ b) (hna : isSTrueNat a = false) (hnb : isSTrueNat b = false)
    (hnd : isSTrueNat cur = false) : wfP57Steps cur (colRedOpSteps (.ha col a b cur)) = some
    (cur + 1, 1) := by
  simp [colRedOpSteps, wfP57Steps, wfP57Step, ha, hb, hle,
    show a < cur + 1 by omega, show b < cur + 1 by omega, hab, hab.symm, hna, hnb, hnd]
theorem applyColRedOp_sound {cur cur1 : ℕ} {op : ColRedOp} {items items1 : List (ℕ × ℕ)}
    (hwf : wfItems cur items = true) (hap : applyColRedOp cur op items = some (cur1, items1))
    : P57CtxPkg cur cur1 1 (buildP57Ctx (colRedOpSteps op)) ∧ wfItems cur1 items1 = true ∧ (∀
    γ : BitAssignment 437, cleanRem 437 (437 - cur) γ → colListSum items1 ((buildP57Ctx
    (colRedOpSteps op)).fwdBits γ) = colListSum items γ) := by
  cases op with
  | fa col a b cin cout =>
      dsimp [applyColRedOp] at hap
      split_ifs at hap with hc
      cases h1 : removeOne col a items with
      | none => rw [h1] at hap; cases hap
      | some it1 =>
          rw [h1] at hap
          dsimp only at hap
          cases h2 : removeOne col b it1 with
          | none => rw [h2] at hap; cases hap
          | some it2 =>
              rw [h2] at hap
              dsimp only at hap
              cases h3 : removeOne col cin it2 with
              | none => rw [h3] at hap; cases hap
              | some it3 =>
                  rw [h3] at hap
                  dsimp only at hap
                  injection hap with hp; injection hp with hc_eq hit_eq
                  subst hc_eq hit_eq
                  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne,
                    decide_eq_true_eq] at hc
                  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hcout, hle⟩, hab⟩, hac⟩, hbc⟩, hna⟩, hnb⟩, hnc⟩, hnd⟩ := hc
                  subst hcout
                  obtain ⟨ha_lt, hna_1, _, hwf_1, hsum_1⟩ := removeOne_spec hwf h1
                  obtain ⟨hb_lt, _, hp_2, hwf_2, hsum_2⟩ := removeOne_spec hwf_1 h2
                  obtain ⟨hc_lt, _, hp_3, hwf_3, hsum_3⟩ := removeOne_spec hwf_2 h3
                  have hna_3 : notMemSnd a it3 = true := hp_3 a (hp_2 a hna_1)
                  have hcur_nm : notMemSnd cout it3 = true := notMemSnd_of_ge hwf_3 le_rfl
                  have hpkg := buildP57Ctx_pkg
                    (wfP57Steps_fa (col := col) ha_lt hb_lt hc_lt hle hab hac hbc hna hnb hnc hnd)
                  have hwf_out : wfItems (cout + 1) ((col, a) :: (col + 1,
                    cout) :: it3) = true := by
                    dsimp [wfItems, notMemSnd]
                    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
                    exact ⟨⟨by omega, by omega, hna_3⟩,⟨by omega, hcur_nm⟩,
                      wfItems_mono (by omega) hle hwf_3⟩
                  refine ⟨hpkg, hwf_out, fun γ hcl ↦ ?_⟩
                  let wa : Wire 437 := ⟨a, by omega⟩
                  let wb : Wire 437 := ⟨b, by omega⟩
                  let wc : Wire 437 := ⟨cin, by omega⟩
                  let wd : Wire 437 := ⟨cout, by omega⟩
                  have hwa_b : wa ≠ wb := wire_ne_val hab
                  have hwa_c : wa ≠ wc := wire_ne_val hac
                  have hwb_c : wb ≠ wc := wire_ne_val hbc
                  have hwa_d : wa ≠ wd := wire_ne_val (by dsimp [wa, wd]; omega)
                  have hwb_d : wb ≠ wd := wire_ne_val (by dsimp [wb, wd]; omega)
                  have hwc_d : wc ≠ wd := wire_ne_val (by dsimp [wc, wd]; omega)
                  have hwd0 : γ wd = 0 := hcl wd (by dsimp [wd]; omega)
                  have hev : (buildP57Ctx (colRedOpSteps (.fa col a b cin cout))).fwdBits γ =
                      Function.update (Function.update γ wa ((γ wa + γ wc) + γ wb)) wd
                      (((0 : ZMod 2) + (γ wa + γ wc) * (γ wb + γ wc)) + γ wc) := by
                    rw [buildP57Ctx_fwdBits]
                    change evalP57Steps [P57Step.cnot wc.val wa.val, P57Step.cnot wc.val wb.val,
                      P57Step.tempAnd wa.val wb.val wd.val, P57Step.cnot wc.val wb.val,
                      P57Step.cnot wb.val wa.val, P57Step.cnot wc.val wd.val] γ = _
                    dsimp only [evalP57Steps]
                    rw [evalP57Step_cnot hwa_c.symm, evalP57Step_cnot hwb_c.symm,
                      evalP57Step_tempAnd hwa_b hwa_d hwb_d, evalP57Step_cnot hwb_c.symm,
                      evalP57Step_cnot hwa_b.symm, evalP57Step_cnot hwc_d]
                    obtain ⟨hbid, _⟩ := fa_zmod2_id (γ wa) (γ wb) (γ wc)
                    funext u
                    by_cases hud : u = wd
                    · subst hud
                      simp only [Function.update_self, Function.update_of_ne hwa_b,
                          Function.update_of_ne hwa_b.symm,
                          Function.update_of_ne hwa_c.symm,
                          Function.update_of_ne hwb_c.symm, Function.update_of_ne hwa_d,
                          Function.update_of_ne hwa_d.symm, Function.update_of_ne hwb_d,
                          Function.update_of_ne hwb_d.symm, Function.update_of_ne hwc_d,
                          hwd0, hbid]
                    · rw [Function.update_of_ne hud, Function.update_of_ne hud]
                      by_cases hua : u = wa
                      · subst hua
                        simp only [Function.update_self, Function.update_of_ne hwa_b,
                            Function.update_of_ne hwa_b.symm,
                            Function.update_of_ne hwa_c.symm,
                            Function.update_of_ne hwb_c.symm, Function.update_of_ne hwa_d,
                            Function.update_of_ne hwa_d.symm, Function.update_of_ne hwb_d,
                            Function.update_of_ne hwb_d.symm, Function.update_of_ne hwc_d,
                            hwd0, hbid]
                      · rw [Function.update_of_ne hua, Function.update_of_ne hua]
                        by_cases hub : u = wb
                        · subst hub
                          simp only [Function.update_self, Function.update_of_ne hwa_b,
                              Function.update_of_ne hwa_b.symm,
                              Function.update_of_ne hwa_c.symm,
                              Function.update_of_ne hwb_c.symm,
                              Function.update_of_ne hwa_d.symm, Function.update_of_ne hwb_d,
                              Function.update_of_ne hwb_d.symm, Function.update_of_ne hwc_d,
                              hwd0, hbid]
                        · simp only [Function.update_of_ne hub, Function.update_of_ne hud,
                            Function.update_of_ne hua]
                  rw [hev]
                  let γ_out := Function.update (Function.update γ wa ((γ wa + γ wc) + γ wb))
                      wd (((0 : ZMod 2) + (γ wa + γ wc) * (γ wb + γ wc)) + γ wc)
                  have hit3_eq : colListSum it3 γ_out = colListSum it3 γ := by
                    refine colListSum_congr fun p hp ↦ ?_
                    have hp_lt : p.2 < cout := wfItems_lt hwf_3 p hp
                    have hp437 : p.2 < 437 := by omega
                    have hp_ne_a : p.2 ≠ a := (notMemSnd_true hna_3 p hp).symm
                    rw [readBit437_lt _ hp437, readBit437_lt _ hp437]
                    dsimp [γ_out]
                    rw [Function.update_of_ne (wire_ne_val (by dsimp [wd]; omega)),
                      Function.update_of_ne (wire_ne_val hp_ne_a)]
                  dsimp only [colListSum]
                  rw [hit3_eq, hsum_1 γ, hsum_2 γ, hsum_3 γ]
                  have ha437 : a < 437 := by omega
                  have hb437 : b < 437 := by omega
                  have hc437 : cin < 437 := by omega
                  have hd437 : cout < 437 := by omega
                  rw [readBit437_lt γ_out ha437, readBit437_lt γ_out hd437,
                    readBit437_lt γ ha437, readBit437_lt γ hb437, readBit437_lt γ hc437]
                  have h_out_a : γ_out ⟨a, ha437⟩ = (γ wa + γ wc) + γ wb := by
                    dsimp [γ_out]; rw [Function.update_of_ne hwa_d, Function.update_self]
                  have h_out_d : γ_out ⟨cout, hd437⟩ =
                      ((0 : ZMod 2) + (γ wa + γ wc) * (γ wb + γ wc)) + γ wc := by
                    dsimp [γ_out]; exact Function.update_self _ _ _
                  rw [h_out_a, h_out_d, pow_succ]
                  have hid := (fa_zmod2_id (γ wa) (γ wb) (γ wc)).2
                  have hmul := congrArg (fun k : ℕ ↦ k * (2 ^ col)) hid
                  dsimp only [wa, wb, wc] at hmul ⊢
                  linarith
  | ha col a b cout =>
      dsimp [applyColRedOp] at hap
      split_ifs at hap with hc
      cases h1 : removeOne col a items with
      | none => rw [h1] at hap; cases hap
      | some it1 =>
          rw [h1] at hap
          dsimp only at hap
          cases h2 : removeOne col b it1 with
          | none => rw [h2] at hap; cases hap
          | some it2 =>
              rw [h2] at hap
              dsimp only at hap
              injection hap with hp; injection hp with hc_eq hit_eq
              subst hc_eq hit_eq
              simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne,
                decide_eq_true_eq] at hc
              obtain ⟨⟨⟨⟨⟨hcout, hle⟩, hab⟩, hna⟩, hnb⟩, hnd⟩ := hc
              subst hcout
              obtain ⟨ha_lt, hna_1, _, hwf_1, hsum_1⟩ := removeOne_spec hwf h1
              obtain ⟨hb_lt, _, hp_2, hwf_2, hsum_2⟩ := removeOne_spec hwf_1 h2
              have hna_2 : notMemSnd a it2 = true := hp_2 a hna_1
              have hcur_nm : notMemSnd cout it2 = true := notMemSnd_of_ge hwf_2 le_rfl
              have hpkg := buildP57Ctx_pkg (wfP57Steps_ha (col := col) ha_lt hb_lt hle hab hna hnb
                hnd)
              have hwf_out : wfItems (cout + 1) ((col, a) :: (col + 1, cout) :: it2) = true := by
                dsimp [wfItems, notMemSnd]
                simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
                exact ⟨⟨by omega, by omega, hna_2⟩,⟨by omega, hcur_nm⟩,
                  wfItems_mono (by omega) hle hwf_2⟩
              refine ⟨hpkg, hwf_out, fun γ hcl ↦ ?_⟩
              let wa : Wire 437 := ⟨a, by omega⟩
              let wb : Wire 437 := ⟨b, by omega⟩
              let wd : Wire 437 := ⟨cout, by omega⟩
              have hwa_b : wa ≠ wb := wire_ne_val hab
              have hwa_d : wa ≠ wd := wire_ne_val (by dsimp [wa, wd]; omega)
              have hwb_d : wb ≠ wd := wire_ne_val (by dsimp [wb, wd]; omega)
              have hwd0 : γ wd = 0 := hcl wd (by dsimp [wd]; omega)
              have hev : (buildP57Ctx (colRedOpSteps (.ha col a b cout))).fwdBits γ =
                  Function.update (Function.update γ wd ((0 : ZMod 2) + γ wa * γ wb))
                    wa (γ wa + γ wb) := by
                rw [buildP57Ctx_fwdBits]
                change evalP57Steps [P57Step.tempAnd wa.val wb.val wd.val,
                  P57Step.cnot wb.val wa.val] γ = _
                dsimp only [evalP57Steps]
                rw [evalP57Step_tempAnd hwa_b hwa_d hwb_d, evalP57Step_cnot hwa_b.symm]
                simp [Function.update_of_ne hwa_d, Function.update_of_ne hwb_d, hwd0]
              rw [hev]
              let γ_out := Function.update (Function.update γ wd ((0 : ZMod 2) + γ wa * γ wb))
                wa (γ wa + γ wb)
              have hit2_eq : colListSum it2 γ_out = colListSum it2 γ := by
                refine colListSum_congr fun p hp ↦ ?_
                have hp_lt : p.2 < cout := wfItems_lt hwf_2 p hp
                have hp437 : p.2 < 437 := by omega
                have hp_ne_a : p.2 ≠ a := (notMemSnd_true hna_2 p hp).symm
                rw [readBit437_lt _ hp437, readBit437_lt _ hp437]
                dsimp [γ_out]
                rw [Function.update_of_ne (wire_ne_val hp_ne_a),
                  Function.update_of_ne (wire_ne_val (by dsimp [wd]; omega))]
              dsimp only [colListSum]
              rw [hit2_eq, hsum_1 γ, hsum_2 γ]
              have ha437 : a < 437 := by omega
              have hb437 : b < 437 := by omega
              have hd437 : cout < 437 := by omega
              rw [readBit437_lt γ_out ha437, readBit437_lt γ_out hd437,
                readBit437_lt γ ha437, readBit437_lt γ hb437]
              have h_out_a : γ_out ⟨a, ha437⟩ = γ wa + γ wb := Function.update_self _ _ _
              have h_out_d : γ_out ⟨cout, hd437⟩ = (0 : ZMod 2) + γ wa * γ wb := by
                dsimp [γ_out]; rw [Function.update_of_ne hwa_d.symm, Function.update_self]
              rw [h_out_a, h_out_d, pow_succ]
              have hid := ha_zmod2_id (γ wa) (γ wb)
              have hmul := congrArg (fun k : ℕ ↦ k * (2 ^ col)) hid
              dsimp only [wa, wb] at hmul ⊢
              linarith
theorem applyColRedOps_sound :
    ∀ {ops : List ColRedOp} {cur curEnd : ℕ} {items itemsEnd : List (ℕ × ℕ)},
      wfItems cur items = true →
      applyColRedOps cur ops items = some (curEnd, itemsEnd) →
      P57CtxPkg cur curEnd ops.length (buildColRedCtx ops) ∧
        wfItems curEnd itemsEnd = true ∧
        (∀ γ : BitAssignment 437, cleanRem 437 (437 - cur) γ →
          colListSum itemsEnd ((buildColRedCtx ops).fwdBits γ) = colListSum items γ)
  | [], _, _, _, _, hwf, hap => by
      dsimp [applyColRedOps] at hap
      cases hap
      exact ⟨⟨le_rfl, wfItems_cur_le hwf, rfl, trivial, trivial, fun hb ↦ ⟨_, hb⟩, fun _ h ↦ h⟩,
        hwf, fun _ _ ↦ rfl⟩
  | op :: ops, cur, curEnd, items, itemsEnd, hwf, hap => by
      dsimp [applyColRedOps] at hap
      rcases h1 : applyColRedOp cur op items with _ | ⟨cur1, items1⟩
      · simp [h1] at hap
      rw [h1] at hap
      dsimp only at hap
      obtain ⟨hpkg1, hwf1, hsum1⟩ := applyColRedOp_sound hwf h1
      obtain ⟨hpkg2, hwf2, hsum2⟩ := applyColRedOps_sound hwf1 hap
      refine ⟨(show 1 + ops.length = (op :: ops).length from Nat.add_comm 1 ops.length) ▸
        hpkg1.append hpkg2, hwf2, fun γ hcl ↦ ?_⟩
      dsimp only [buildColRedCtx]
      rw [TempCtx.append_fwdBits, hsum2 _ (hpkg1.clean γ hcl), hsum1 γ hcl]
def colRedOps77 : List ColRedOp := [
  .fa 2 178 179 185 357, .fa 2 186 192 178 358, .fa 3 180 187 193 359, .fa 3 357 358 180 360,
  .fa 4 278 304 194 361, .fa 4 359 360 278 362, .fa 5 296 279 322 363, .fa 5 305 349 330 364,
  .fa 5 361 362 296 365, .ha 5 305 361 366, .fa 6 298 280 324 367, .fa 6 306 350 351 368,
  .fa 6 331 363 364 369, .fa 6 365 366 298 370, .fa 6 306 331 365 371, .fa 7 288 292 297 372,
  .fa 7 299 281 314 373, .fa 7 318 323 325 374, .fa 7 307 341 345 375, .fa 7 352 332 367 376,
  .fa 7 368 369 370 377, .fa 7 371 288 299 378, .fa 7 318 307 352 379, .fa 7 368 371 318 380,
  .fa 8 289 290 293 381, .fa 8 295 181 315 382, .fa 8 316 319 321 383, .fa 8 188 342 343 384,
  .fa 8 346 195 372 385, .fa 8 373 374 375 386, .fa 8 376 377 378 387, .fa 8 379 380 289 388,
  .fa 8 295 316 188 389, .fa 8 346 373 376 390, .fa 8 379 295 346 391, .fa 9 291 294 300 392,
  .fa 9 317 320 326 393, .fa 9 344 347 348 394, .fa 9 353 381 382 395, .fa 9 383 384 385 396,
  .fa 9 386 387 388 397, .fa 9 389 390 391 398, .fa 9 291 317 344 399, .fa 9 353 383 386 400,
  .fa 9 389 291 353 401, .fa 10 302 182 183 402, .fa 10 328 189 190 403, .fa 10 355 196 197 404,
  .fa 10 392 393 394 405, .fa 10 395 396 397 406, .fa 10 398 399 400 407,
  .fa 10 401 302 328 408, .fa 10 355 392 395 409, .fa 10 398 401 355 410,
  .fa 11 301 275 327 411, .fa 11 276 354 277 412, .fa 11 402 403 404 413,
  .fa 11 405 406 407 414, .fa 11 408 409 410 415, .fa 11 301 276 402 416,
  .fa 11 405 408 301 417, .fa 12 303 283 329 418, .fa 12 309 356 336 419,
  .fa 12 411 412 413 420, .fa 12 414 415 416 421, .fa 12 417 303 309 422,
  .fa 12 411 414 417 423, .fa 13 284 310 337 424, .fa 13 418 419 420 425,
  .fa 13 421 422 423 426, .fa 13 284 418 421 427, .fa 14 285 311 338 428,
  .fa 14 424 425 426 429, .fa 14 427 285 424 430, .fa 15 286 312 339 431,
  .fa 15 428 429 430 432, .ha 15 286 428 433]
def finalItems20 : List (ℕ × ℕ) := [(15,286),(16,433),(16,432),(16,431),(14,427),(13,284),(12,411),
  (11,405),(10,398),(9,389),(8,379),(7,368),(6,306),(5,305),(4,359),(3,357),(2,186),(0,177),(0,184),
  (0,191)]
def K_red77 : TempCtx 437 := buildColRedCtx colRedOps77
theorem K_red77_sound : P57CtxPkg 357 434 77 K_red77 ∧ (∀ γ : BitAssignment 437, cleanRem 437
    (437 - 357) γ → colListSum finalItems20 (K_red77.fwdBits γ) = colListSum preRedItems95 γ) := by
  obtain ⟨hpkg, _, hsum⟩ := applyColRedOps_sound (by decide : wfItems 357 preRedItems95 = true)
    (by decide : applyColRedOps 357 colRedOps77 preRedItems95 = some (434, finalItems20))
  exact ⟨(by decide : colRedOps77.length = 77) ▸ hpkg, hsum⟩
def ctxJointPBuf159 : TempCtx 437 := K_preRed82.append K_red77
theorem ctxJointPBuf159_pkg : P57CtxPkg 275 434 159 ctxJointPBuf159 :=
  K_preRed82_pkg.append K_red77_sound.1
theorem ctxJointPBuf159_spec (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β) :
    cleanRem 437 (437 - 434) (ctxJointPBuf159.fwdBits β) ∧
      colListSum finalItems20 (ctxJointPBuf159.fwdBits β) = sTrueRawValPBuf β := by
  refine ⟨ctxJointPBuf159_pkg.clean β hβ, ?_⟩
  obtain ⟨hcl1, hpre⟩ := K_preRed82_spec β hβ
  dsimp only [ctxJointPBuf159]
  rw [TempCtx.append_fwdBits, K_red77_sound.2 _ hcl1, hpre]
def targetBit (δ : BitAssignment 437) : Fin 18 → ZMod 2
  | ⟨0, _⟩ => δ ⟨177, by decide⟩ + δ ⟨184, by decide⟩ + δ ⟨191, by decide⟩
  | ⟨1, _⟩ => δ ⟨177, by decide⟩ + (δ ⟨184, by decide⟩ + δ ⟨177, by decide⟩) * (δ ⟨191,
      by decide⟩ + δ ⟨177, by decide⟩)
  | ⟨2, _⟩ => δ ⟨186, by decide⟩
  | ⟨3, _⟩ => δ ⟨357, by decide⟩
  | ⟨4, _⟩ => δ ⟨359, by decide⟩
  | ⟨5, _⟩ => δ ⟨305, by decide⟩
  | ⟨6, _⟩ => δ ⟨306, by decide⟩
  | ⟨7, _⟩ => δ ⟨368, by decide⟩
  | ⟨8, _⟩ => δ ⟨379, by decide⟩
  | ⟨9, _⟩ => δ ⟨389, by decide⟩
  | ⟨10, _⟩ => δ ⟨398, by decide⟩
  | ⟨11, _⟩ => δ ⟨405, by decide⟩
  | ⟨12, _⟩ => δ ⟨411, by decide⟩
  | ⟨13, _⟩ => δ ⟨284, by decide⟩
  | ⟨14, _⟩ => δ ⟨427, by decide⟩
  | ⟨15, _⟩ => δ ⟨286, by decide⟩
  | ⟨16, _⟩ => δ ⟨431, by decide⟩ + δ ⟨432, by decide⟩ + δ ⟨433, by decide⟩
  | ⟨17, _⟩ => δ ⟨431, by decide⟩ + (δ ⟨432, by decide⟩ + δ ⟨431, by decide⟩) * (δ ⟨433,
      by decide⟩ + δ ⟨431, by decide⟩)
  | ⟨_ + 18, h⟩ => absurd h (by omega)
theorem maj3_xor_val (x y z : ZMod 2) :
    (x + y + z).val + 2 * (x + (y + x) * (z + x)).val = x.val + y.val + z.val := by
  rcases bit_cases x with rfl | rfl <;>
    rcases bit_cases y with rfl | rfl <;>
    rcases bit_cases z with rfl | rfl <;> decide
theorem bitsVal_targetBit_eq_colListSum (δ : BitAssignment 437) :
    bitsVal (targetBit δ) = colListSum finalItems20 δ := by
  have hL : bitsVal (targetBit δ) =
      (targetBit δ ⟨0, by decide⟩).val * 1 + (targetBit δ ⟨1, by decide⟩).val * 2 +
      (targetBit δ ⟨2, by decide⟩).val * 4 + (targetBit δ ⟨3, by decide⟩).val * 8 +
      (targetBit δ ⟨4, by decide⟩).val * 16 + (targetBit δ ⟨5, by decide⟩).val * 32 +
      (targetBit δ ⟨6, by decide⟩).val * 64 + (targetBit δ ⟨7, by decide⟩).val * 128 +
      (targetBit δ ⟨8, by decide⟩).val * 256 + (targetBit δ ⟨9, by decide⟩).val * 512 +
      (targetBit δ ⟨10, by decide⟩).val * 1024 + (targetBit δ ⟨11, by decide⟩).val * 2048 +
      (targetBit δ ⟨12, by decide⟩).val * 4096 + (targetBit δ ⟨13, by decide⟩).val * 8192 +
      (targetBit δ ⟨14, by decide⟩).val * 16384 + (targetBit δ ⟨15, by decide⟩).val * 32768 +
      (targetBit δ ⟨16, by decide⟩).val * 65536 + (targetBit δ ⟨17, by decide⟩).val * 131072 := by
    repeat rw [bitsVal_succ_split]
    simp only [bitsVal_fin_zero]
    change ((targetBit δ ⟨0, by decide⟩).val
      + 2 * ((targetBit δ ⟨1, by decide⟩).val
      + 2 * ((targetBit δ ⟨2, by decide⟩).val
      + 2 * ((targetBit δ ⟨3, by decide⟩).val
      + 2 * ((targetBit δ ⟨4, by decide⟩).val
      + 2 * ((targetBit δ ⟨5, by decide⟩).val
      + 2 * ((targetBit δ ⟨6, by decide⟩).val
      + 2 * ((targetBit δ ⟨7, by decide⟩).val
      + 2 * ((targetBit δ ⟨8, by decide⟩).val
      + 2 * ((targetBit δ ⟨9, by decide⟩).val
      + 2 * ((targetBit δ ⟨10, by decide⟩).val
      + 2 * ((targetBit δ ⟨11, by decide⟩).val
      + 2 * ((targetBit δ ⟨12, by decide⟩).val
      + 2 * ((targetBit δ ⟨13, by decide⟩).val
      + 2 * ((targetBit δ ⟨14, by decide⟩).val
      + 2 * ((targetBit δ ⟨15, by decide⟩).val
      + 2 * ((targetBit δ ⟨16, by decide⟩).val
      + 2 * ((targetBit δ ⟨17, by decide⟩).val + 2 * 0)))))))))))))))))) = _
    ring
  rw [hL]
  have h0 := maj3_xor_val (δ ⟨177, by decide⟩) (δ ⟨184, by decide⟩) (δ ⟨191, by decide⟩)
  have h16 := maj3_xor_val (δ ⟨431, by decide⟩) (δ ⟨432, by decide⟩) (δ ⟨433, by decide⟩)
  dsimp only [targetBit, finalItems20, colListSum]
  repeat rw [readBit437_lt _ (by decide)]
  simp only [← pow2Col_eq, pow2Col]
  omega
def srcMid14 : Fin 14 → Wire 437
  | ⟨0, _⟩ => ⟨186, by decide⟩
  | ⟨1, _⟩ => ⟨357, by decide⟩
  | ⟨2, _⟩ => ⟨359, by decide⟩
  | ⟨3, _⟩ => ⟨305, by decide⟩
  | ⟨4, _⟩ => ⟨306, by decide⟩
  | ⟨5, _⟩ => ⟨368, by decide⟩
  | ⟨6, _⟩ => ⟨379, by decide⟩
  | ⟨7, _⟩ => ⟨389, by decide⟩
  | ⟨8, _⟩ => ⟨398, by decide⟩
  | ⟨9, _⟩ => ⟨405, by decide⟩
  | ⟨10, _⟩ => ⟨411, by decide⟩
  | ⟨11, _⟩ => ⟨284, by decide⟩
  | ⟨12, _⟩ => ⟨427, by decide⟩
  | ⟨13, _⟩ => ⟨286, by decide⟩
def dstMid14 (i : Fin 14) : Wire 437 :=
  sTrue18WDefault ⟨2 + i.val, by omega⟩
theorem dstMid14_injective : Function.Injective dstMid14 := fun i j h ↦ by
  have hv := sTrue18WDefault_injective h
  have hv2 := congrArg Fin.val hv; dsimp at hv2; exact Fin.ext (by omega)
theorem srcMid14_ne_dstMid14 (i j : Fin 14) : srcMid14 i ≠ dstMid14 j := by
  revert i j; decide
def cXor3 (a b c dst : Wire 437) (ha : a ≠ dst) (hb : b ≠ dst) (hc : c ≠ dst) : CliffProg 437 :=
  .seq (.cnot a dst ha) (.seq (.cnot b dst hb) (.cnot c dst hc))
theorem cXor3_eval (a b c dst : Wire 437) (ha : a ≠ dst) (hb : b ≠ dst) (hc : c ≠ dst)
    (δ : BitAssignment 437) : (cXor3 a b c dst ha hb hc).eval δ = Function.update δ dst
    (δ dst + (δ a + δ b + δ c)) := by
  funext u
  dsimp [cXor3, CliffProg.eval]
  by_cases hud : u = dst
  · subst hud
    simp [Function.update_self, Function.update_of_ne hb,
      Function.update_of_ne hc, add_assoc]
  · simp [Function.update_of_ne hud]
def cMid16 : CliffProg 437 :=
  .seq (cnotVec 14 srcMid14 dstMid14 (fun i ↦ srcMid14_ne_dstMid14 i i))
    (.seq
      (cXor3 ⟨431, by decide⟩ ⟨432, by decide⟩ ⟨433, by decide⟩
        (sTrue18WDefault ⟨16, by decide⟩) (by decide) (by decide) (by decide))
      (cXor3 ⟨177, by decide⟩ ⟨184, by decide⟩ ⟨191, by decide⟩
        (sTrue18WDefault ⟨0, by decide⟩) (by decide) (by decide) (by decide)))
theorem cMid16_supportsBelow : cMid16.SupportsBelow 434 := by
  refine ⟨cnotVec_supportsBelow 14 srcMid14 dstMid14 _
    (fun i ↦ by revert i; decide) (fun i ↦ by revert i; decide), ?_⟩
  dsimp [cXor3, sTrue18WDefault, CliffProg.SupportsBelow]
  decide
theorem cMid16_eval (δ : BitAssignment 437) :
    (∀ u : Wire 437, ¬ mutSTrue u → cMid16.eval δ u = δ u) ∧
      cMid16.eval δ (sTrue18WDefault ⟨17, by decide⟩) = δ (sTrue18WDefault ⟨17, by decide⟩) ∧
      cMid16.eval δ (sTrue18WDefault ⟨1, by decide⟩) = δ (sTrue18WDefault ⟨1, by decide⟩) ∧
      cMid16.eval δ (sTrue18WDefault ⟨16, by decide⟩) =
        δ (sTrue18WDefault ⟨16, by decide⟩) + targetBit δ ⟨16, by decide⟩ ∧
      cMid16.eval δ (sTrue18WDefault ⟨0, by decide⟩) =
        δ (sTrue18WDefault ⟨0, by decide⟩) + targetBit δ ⟨0, by decide⟩ ∧
      (∀ i : Fin 14,
        cMid16.eval δ (sTrue18WDefault ⟨2 + i.val, by omega⟩) =
          δ (sTrue18WDefault ⟨2 + i.val, by omega⟩) + targetBit δ ⟨2 + i.val, by omega⟩) := by
  let δ1 := (cnotVec 14 srcMid14 dstMid14 (fun i ↦ srcMid14_ne_dstMid14 i i)).eval δ
  have hδ1_non : ∀ u : Wire 437, (∀ i : Fin 14, u ≠ dstMid14 i) → δ1 u = δ u := fun u hu ↦ by
    dsimp [δ1]
    rw [cnotVec_eval 14 srcMid14 dstMid14 _ dstMid14_injective srcMid14_ne_dstMid14 δ u]
    have hnex : ¬ ∃ i : Fin 14, u = dstMid14 i := fun ⟨i, hi⟩ ↦ hu i hi
    simp [hnex]
  have hnon_mid14 : ∀ u : Wire 437, ¬ mutSTrue u → ∀ i : Fin 14, u ≠ dstMid14 i :=
    fun u hnu i h ↦ hnu ⟨⟨2 + i.val, by omega⟩, h⟩
  have hS16_ne_mid : ∀ i : Fin 14, sTrue18WDefault ⟨16, by decide⟩ ≠ dstMid14 i := fun i h ↦ by
    have hv := congrArg Fin.val (sTrue18WDefault_injective h); dsimp at hv; omega
  have hS0_ne_mid : ∀ i : Fin 14, sTrue18WDefault ⟨0, by decide⟩ ≠ dstMid14 i := fun i h ↦ by
    have hv := congrArg Fin.val (sTrue18WDefault_injective h); dsimp at hv; omega
  have hS17_ne_mid : ∀ i : Fin 14, sTrue18WDefault ⟨17, by decide⟩ ≠ dstMid14 i := fun i h ↦ by
    have hv := congrArg Fin.val (sTrue18WDefault_injective h); dsimp at hv; omega
  have hS1_ne_mid : ∀ i : Fin 14, sTrue18WDefault ⟨1, by decide⟩ ≠ dstMid14 i := fun i h ↦ by
    have hv := congrArg Fin.val (sTrue18WDefault_injective h); dsimp at hv; omega
  have hev_all : cMid16.eval δ =
      Function.update
        (Function.update δ1 (sTrue18WDefault ⟨16, by decide⟩)
          (δ (sTrue18WDefault ⟨16, by decide⟩) + targetBit δ ⟨16, by decide⟩))
        (sTrue18WDefault ⟨0, by decide⟩)
        (δ (sTrue18WDefault ⟨0, by decide⟩) + targetBit δ ⟨0, by decide⟩) := by
    dsimp only [cMid16, CliffProg.eval]
    change (cXor3 _ _ _ (sTrue18WDefault ⟨0, by decide⟩) _ _ _).eval
      ((cXor3 _ _ _ (sTrue18WDefault ⟨16, by decide⟩) _ _ _).eval δ1) = _
    rw [cXor3_eval, cXor3_eval]
    have h431 : δ1 ⟨431, by decide⟩ = δ ⟨431, by decide⟩ :=
      hδ1_non _ (hnon_mid14 _ (not_mutSTrue_of_false (by decide)))
    have h432 : δ1 ⟨432, by decide⟩ = δ ⟨432, by decide⟩ :=
      hδ1_non _ (hnon_mid14 _ (not_mutSTrue_of_false (by decide)))
    have h433 : δ1 ⟨433, by decide⟩ = δ ⟨433, by decide⟩ :=
      hδ1_non _ (hnon_mid14 _ (not_mutSTrue_of_false (by decide)))
    have hS16 : δ1 (sTrue18WDefault ⟨16, by decide⟩) = δ (sTrue18WDefault ⟨16, by decide⟩) :=
      hδ1_non _ hS16_ne_mid
    rw [hS16, h431, h432, h433]
    let δ2 := Function.update δ1 (sTrue18WDefault ⟨16, by decide⟩)
      (δ (sTrue18WDefault ⟨16, by decide⟩) +
        (δ ⟨431, by decide⟩ + δ ⟨432, by decide⟩ + δ ⟨433, by decide⟩))
    have h177 : δ2 ⟨177, by decide⟩ = δ ⟨177, by decide⟩ := by
      dsimp [δ2]; rw [Function.update_of_ne (by decide)]
      exact hδ1_non _ (hnon_mid14 _ (not_mutSTrue_of_false (by decide)))
    have h184 : δ2 ⟨184, by decide⟩ = δ ⟨184, by decide⟩ := by
      dsimp [δ2]; rw [Function.update_of_ne (by decide)]
      exact hδ1_non _ (hnon_mid14 _ (not_mutSTrue_of_false (by decide)))
    have h191 : δ2 ⟨191, by decide⟩ = δ ⟨191, by decide⟩ := by
      dsimp [δ2]; rw [Function.update_of_ne (by decide)]
      exact hδ1_non _ (hnon_mid14 _ (not_mutSTrue_of_false (by decide)))
    have hS0 : δ2 (sTrue18WDefault ⟨0, by decide⟩) = δ (sTrue18WDefault ⟨0, by decide⟩) := by
      dsimp [δ2]; rw [Function.update_of_ne (by decide)]; exact hδ1_non _ hS0_ne_mid
    change Function.update δ2 (sTrue18WDefault ⟨0, by decide⟩)
      (δ2 (sTrue18WDefault ⟨0, by decide⟩) +
        (δ2 ⟨177, by decide⟩ + δ2 ⟨184, by decide⟩ + δ2 ⟨191, by decide⟩)) = _
    rw [hS0, h177, h184, h191]
    rfl
  rw [hev_all]
  refine ⟨fun u hnu ↦ ?_, ?_, ?_, ?_, ?_, fun i ↦ ?_⟩
  · rw [Function.update_of_ne (fun h ↦ hnu ⟨⟨0, by decide⟩, h⟩),
      Function.update_of_ne (fun h ↦ hnu ⟨⟨16, by decide⟩, h⟩)]
    exact hδ1_non u (hnon_mid14 u hnu)
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hδ1_non _ hS17_ne_mid
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact hδ1_non _ hS1_ne_mid
  · rw [Function.update_of_ne (by decide), Function.update_self]
  · exact Function.update_self _ _ _
  · have hne0 : dstMid14 i ≠ sTrue18WDefault ⟨0, by decide⟩ := fun h ↦
      (hS0_ne_mid i h.symm)
    have hne16 : dstMid14 i ≠ sTrue18WDefault ⟨16, by decide⟩ := fun h ↦
      (hS16_ne_mid i h.symm)
    change Function.update _ _ _ (dstMid14 i) = _
    rw [Function.update_of_ne hne0, Function.update_of_ne hne16]
    dsimp [δ1]
    rw [cnotVec_eval 14 srcMid14 dstMid14 _ dstMid14_injective srcMid14_ne_dstMid14 δ (dstMid14 i)]
    have hex : ∃ j : Fin 14, dstMid14 i = dstMid14 j := ⟨i, rfl⟩
    have hch : hex.choose = i := dstMid14_injective hex.choose_spec.symm
    simp only [hex, ↓reduceDIte, hch]
    fin_cases i <;> rfl
def cApexPre (x y z sHi : Wire 437) (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z) : CliffProg
    437 := .seq (.cnot x sHi hxs) (.seq (.cnot x y hxy) (.cnot x z hxz))
def cApexPost (x y z : Wire 437) (hxy : x ≠ y) (hxz : x ≠ z) : CliffProg 437 :=
  .seq (.cnot x z hxz) (.cnot x y hxy)
def apexMajStatic (x y z sHi : Wire 437) (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (_hx : x.val < 434) (hy : y.val < 434) (hz : z.val < 434)
    (hs : sHi.val < 434) : TempPhaseProg 437 := .seq (.cliff (cApexPre x y z sHi hxs hxy hxz))
    (.seq (msbClearStatic 434 (by decide) y z sHi hyz hy hz hs) (.cliff (cApexPost x y z hxy
    hxz)))
theorem validCleanRem_cliff_seq_le {M r c0 : ℕ} (hc0 : c0 < M) (c : CliffProg M)
    (hc : c.SupportsBelow c0) {p : TempPhaseProg M}
    (hp : ∀ r', ValidCleanRem M r' p → M - c0 ≤ r')
    (hv : ValidCleanRem M r (.seq (.cliff c) p)) : M - c0 ≤ r := by
  obtain ⟨rMid, _, _, hvP, hpres⟩ := hv
  have hrMid : M - c0 ≤ rMid := hp rMid hvP
  by_contra hlt
  let β : BitAssignment M := fun w ↦ if w.val = c0 then 1 else 0
  have hβ : cleanRem M r β := fun w hw ↦ by
    dsimp [β]; rw [ite_eq_right (by omega)]
  have h1 : (c.eval β) ⟨c0, hc0⟩ = 0 := hpres β hβ ⟨c0, hc0⟩ (by dsimp; omega)
  rw [c.eval_outside hc β ⟨c0, hc0⟩ le_rfl] at h1
  simp [β] at h1
theorem apexMajStatic_spec (x y z sHi : Wire 437)
    (hxs : x ≠ sHi) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hys : y ≠ sHi) (hzs : z ≠ sHi)
    (hx : x.val < 434) (hy : y.val < 434) (hz : z.val < 434) (hs : sHi.val < 434) :
    let p := apexMajStatic x y z sHi hxs hxy hxz hyz hx hy hz hs
    ValidCleanRem 437 (437 - 434) p ∧
      p.countTempAnd = 1 ∧
      (∀ r, ValidCleanRem 437 r p → 437 - 434 ≤ r) ∧
      (∀ δ : BitAssignment 437, cleanRem 437 (437 - 434) δ → p.evalSign δ = 0) ∧
      (∀ δ : BitAssignment 437, cleanRem 437 (437 - 434) δ →
        cleanRem 437 (437 - 434) (p.evalBits δ) ∧
        p.evalBits δ = Function.update δ sHi (δ sHi + (δ x + (δ y + δ x) * (δ z + δ x)))) := by
  intro p
  obtain ⟨hvM, _, hsM, hbM⟩ := msbClearStatic_spec 434 (by decide) y z sHi hyz hys hzs hy hz hs
  have hcPre : (cApexPre x y z sHi hxs hxy hxz).SupportsBelow 434 := ⟨⟨hx, hs⟩, ⟨hx, hy⟩, ⟨hx, hz⟩⟩
  have hclPre : ∀ δ : BitAssignment 437, cleanRem 437 (437 - 434) δ →
      cleanRem 437 (437 - 434) ((cApexPre x y z sHi hxs hxy hxz).eval δ) := fun δ hδ w hw ↦
    ((cApexPre x y z sHi hxs hxy hxz).eval_outside hcPre δ w (by omega)).trans (hδ w hw)
  refine ⟨⟨437 - 434, by decide, trivial,
      ⟨0, Nat.zero_le 437, hvM, trivial, fun _ _ _ hw ↦ absurd hw (by omega)⟩, hclPre⟩,
    rfl, fun r hr ↦ validCleanRem_cliff_seq_le (by decide : 434 < 437) _ hcPre
      (fun r' hr' ↦ by
        obtain ⟨_, _, hv1, _, _⟩ := hr'
        exact msbClearStatic_valid_le 434 (by decide) y z sHi hyz hy hz hs r' hv1) hr,
    fun δ hδ ↦ by
      dsimp [p, apexMajStatic, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
      rw [hsM _ (hclPre δ hδ)]
      rfl,
    fun δ hδ ↦ ?_⟩
  have hev : p.evalBits δ =
      Function.update δ sHi (δ sHi + (δ x + (δ y + δ x) * (δ z + δ x))) := by
    dsimp only [p, apexMajStatic, TempPhaseProg.evalBits]
    rw [hbM _ (hclPre δ hδ)]
    funext u
    by_cases hu1 : u = sHi
    · subst hu1
      simp [cApexPre, cApexPost, CliffProg.eval, hys, hys.symm,
        hzs, hzs.symm, hyz, hyz.symm, hxs, hxy, hxz, add_assoc]
    · by_cases hu2 : u = y
      · subst hu2
        simp [cApexPre, cApexPost, CliffProg.eval, hyz, hyz.symm, hys,
          hys.symm, hzs, hzs.symm, hxy, hxz, hxs]
      · by_cases hu3 : u = z
        · subst hu3
          simp [cApexPre, cApexPost, CliffProg.eval, hzs, hzs.symm, hys,
            hys.symm, hyz, hyz.symm, hxz, hxy, hxs]
        · simp [cApexPre, cApexPost, CliffProg.eval, Function.update_apply, hu1, hu2, hu3]
  rw [hev]
  exact ⟨fun w hw ↦ (Function.update_of_ne (wire_ne_of_gt (by omega)) _ _).trans (hδ w hw), rfl⟩
def innerApex2 : TempPhaseProg 437 :=
  .seq (.cliff cMid16) (.seq
    (apexMajStatic ⟨431, by decide⟩ ⟨432, by decide⟩ ⟨433, by decide⟩
      (sTrue18WDefault ⟨17, by decide⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (apexMajStatic ⟨177, by decide⟩ ⟨184, by decide⟩ ⟨191, by decide⟩
      (sTrue18WDefault ⟨1, by decide⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)))
theorem innerApex2_spec : ValidCleanRem 437 (437 - 434) innerApex2 ∧ innerApex2.countTempAnd =
    2 ∧ (∀ r, ValidCleanRem 437 r innerApex2 → 437 - 434 ≤ r) ∧ (∀ δ : BitAssignment 437,
    cleanRem 437 (437 - 434) δ → innerApex2.evalSign δ = 0) ∧ (∀ δ : BitAssignment 437,
    cleanRem 437 (437 - 434) δ → (∀ u : Wire 437, ¬ mutSTrue u → innerApex2.evalBits δ u = δ
    u) ∧ (∀ j : Fin 18, innerApex2.evalBits δ (sTrue18WDefault j) = δ (sTrue18WDefault j) +
    targetBit δ j)) := by
  obtain ⟨hv17, _, hle17, hs17, hb17⟩ := apexMajStatic_spec
    ⟨431, by decide⟩ ⟨432, by decide⟩ ⟨433, by decide⟩ (sTrue18WDefault ⟨17, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hv1, _, _, hs1, hb1⟩ := apexMajStatic_spec
    ⟨177, by decide⟩ ⟨184, by decide⟩ ⟨191, by decide⟩ (sTrue18WDefault ⟨1, by decide⟩)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hclMid : ∀ δ : BitAssignment 437, cleanRem 437 (437 - 434) δ →
      cleanRem 437 (437 - 434) (cMid16.eval δ) := fun δ hδ w hw ↦
    (cMid16.eval_outside cMid16_supportsBelow δ w (by omega)).trans (hδ w hw)
  refine ⟨⟨437 - 434, by decide, trivial,
      ⟨437 - 434, by decide, hv17, hv1, fun δ₁ hδ₁ ↦ (hb17 δ₁ hδ₁).1⟩, hclMid⟩,
    rfl, fun r hr ↦ validCleanRem_cliff_seq_le (by decide : 434 < 437) cMid16
      cMid16_supportsBelow (fun r' hr' ↦ by
        obtain ⟨_, _, hv17', _, _⟩ := hr'
        exact hle17 r' hv17') hr,
    fun δ hδ ↦ by
      dsimp only [innerApex2, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
      rw [hs17 _ (hclMid δ hδ), hs1 _ (hb17 _ (hclMid δ hδ)).1]
      rfl,
    fun δ hδ ↦ ?_⟩
  obtain ⟨hcl2, heq17⟩ := hb17 (cMid16.eval δ) (hclMid δ hδ)
  obtain ⟨_, heq1⟩ := hb1 _ hcl2
  obtain ⟨hM_non, hM_17, hM_1, hM_16, hM_0, hM_mid⟩ := cMid16_eval δ
  have hM_src : ∀ q : Wire 437, isSTrueNat q.val = false → cMid16.eval δ q = δ q :=
    fun q hq ↦ hM_non q (not_mutSTrue_of_false hq)
  have h_ev : innerApex2.evalBits δ = Function.update
      (Function.update (cMid16.eval δ) (sTrue18WDefault ⟨17, by decide⟩)
        (δ (sTrue18WDefault ⟨17, by decide⟩) + targetBit δ ⟨17, by decide⟩))
      (sTrue18WDefault ⟨1, by decide⟩)
      (δ (sTrue18WDefault ⟨1, by decide⟩) + targetBit δ ⟨1, by decide⟩) := by
    dsimp only [innerApex2, TempPhaseProg.evalBits]
    rw [heq1, heq17, hM_17, hM_src _ (by decide), hM_src _ (by decide), hM_src _ (by decide)]
    congr 2
  rw [h_ev]
  refine ⟨fun u hnu ↦ (Function.update_of_ne (fun h ↦ hnu ⟨⟨1, by decide⟩, h⟩) _ _).trans
      ((Function.update_of_ne (fun h ↦ hnu ⟨⟨17, by decide⟩, h⟩) _ _).trans (hM_non u hnu)),
    fun j ↦ ?_⟩
  rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 16 ∨ j.val = 17 ∨
      (2 ≤ j.val ∧ j.val < 16)) with h0 | h1 | h16 | h17 | hmid
  · rw [show j = ⟨0, by decide⟩ from Fin.ext h0, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hM_0]
  · rw [show j = ⟨1, by decide⟩ from Fin.ext h1, Function.update_self]
  · rw [show j = ⟨16, by decide⟩ from Fin.ext h16, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hM_16]
  · rw [show j = ⟨17, by decide⟩ from Fin.ext h17, Function.update_of_ne (by decide),
      Function.update_self]
  · have hne : ∀ k : Fin 18, (k.val = 1 ∨ k.val = 17) → sTrue18WDefault j ≠ sTrue18WDefault k :=
      fun k hk h ↦ by
        rw [sTrue18WDefault_injective h] at hmid
        omega
    rw [Function.update_of_ne (hne ⟨1, by decide⟩ (Or.inl rfl)),
      Function.update_of_ne (hne ⟨17, by decide⟩ (Or.inr rfl)),
      show j = ⟨2 + (j.val - 2), by omega⟩ from Fin.ext (Nat.add_sub_of_le hmid.1).symm]
    exact hM_mid ⟨j.val - 2, by omega⟩
def sTrue18FwdPBuf275 : TempPhaseProg 437 := ctxJointPBuf159.plug innerApex2
def sTrue18RevPBuf275 : TempPhaseProg 437 := sTrue18FwdPBuf275
open Classical in
theorem sTrue18FwdPBuf275_graft : ValidCleanRem 437 (437 - 275) sTrue18FwdPBuf275 ∧
    sTrue18FwdPBuf275.countTempAnd = 161 ∧ (∀ β : BitAssignment 437, cleanRem 437 (437 - 275)
    β → sTrue18FwdPBuf275.evalSign β = 0) ∧ (∀ β : BitAssignment 437, cleanRem 437 (437 - 275)
    β → (∀ q : Wire 437, ¬ mutSTrue q → sTrue18FwdPBuf275.evalBits β q = β q) ∧ (∀ j : Fin 18,
    sTrue18FwdPBuf275.evalBits β (sTrue18WDefault j) = β (sTrue18WDefault j) + targetBit
    (ctxJointPBuf159.fwdBits β) j)) := by
  obtain ⟨hvIn, hcIn, _, hsIn, hbIn⟩ := innerApex2_spec
  have hpkg := ctxJointPBuf159_pkg
  obtain ⟨hv, hcnt, hsgn, hbits⟩ := ScopedBlock.graft_mutating_clean (M := 437)
    (rem := 437 - 275) (curHole := 434) mutSTrue ctxJointPBuf159 hpkg.disj hpkg.supp (by decide)
    ctxJointPBuf159.fwdBits (TempCtxLiftEx.probe hpkg.lift) innerApex2 hvIn
    fun γ hγ w hnw ↦ (hbIn γ hγ).1 w hnw
  dsimp only [sTrue18FwdPBuf275]
  refine ⟨hv, by rw [hcnt, hpkg.cnt_eq, hcIn],
    fun β hβ ↦ (hsgn β hβ).trans (hsIn _ (hpkg.clean β hβ)),
    fun β hβ ↦ ⟨fun q hnq ↦ (hbits β hβ q).trans (ite_eq_right hnq), fun j ↦ ?_⟩⟩
  rw [hbits β hβ _, ite_eq_left ⟨j, rfl⟩, (hbIn _ (hpkg.clean β hβ)).2 j,
    TempCtx.fwdBits_mut hpkg.disj β ⟨j, rfl⟩]
theorem sTrue18FwdPBuf275_spec : ValidCleanRem 437 (437 - 275) sTrue18FwdPBuf275 ∧
    sTrue18FwdPBuf275.countTempAnd = 161 ∧ (∀ β : BitAssignment 437, cleanRem 437 (437 - 275)
    β → sTrue18FwdPBuf275.evalSign β = 0) ∧ (∀ β : BitAssignment 437, cleanRem 437 (437 - 275)
    β → cleanRem 437 (437 - 275) (sTrue18FwdPBuf275.evalBits β) ∧ (∀ q : Wire 437, (∀ j, q ≠
    sTrue18WDefault j) → sTrue18FwdPBuf275.evalBits β q = β q) ∧ ((∀ j : Fin 18, β
    (sTrue18WDefault j) = 0) → bitsVal (fun j ↦ sTrue18FwdPBuf275.evalBits β (sTrue18WDefault
    j)) = sTrueRawValPBuf β)) := by
  obtain ⟨hv, hcnt, hsgn, hbits⟩ := sTrue18FwdPBuf275_graft
  refine ⟨hv, hcnt, hsgn, fun β hβ ↦ ?_⟩
  obtain ⟨hnon, hS⟩ := hbits β hβ
  refine ⟨fun w hw ↦ (hnon w fun ⟨j, hj⟩ ↦
      absurd (hj ▸ validSTrueMap_default.2.1 j) (by omega)).trans (hβ w hw),
    fun q hq ↦ hnon q fun ⟨j, hj⟩ ↦ hq j hj, fun hZero ↦ ?_⟩
  rw [show (fun j ↦ sTrue18FwdPBuf275.evalBits β (sTrue18WDefault j)) =
      targetBit (ctxJointPBuf159.fwdBits β) from
      funext fun j ↦ by rw [hS j, hZero j, zero_add],
    bitsVal_targetBit_eq_colListSum, (ctxJointPBuf159_spec β hβ).2]
theorem sTrue18RevPBuf275_spec : ValidCleanRem 437 (437 - 275) sTrue18RevPBuf275 ∧
    sTrue18RevPBuf275.countTempAnd = 161 ∧ (∀ γ : BitAssignment 437, cleanRem 437 (437 - 275)
    γ → sTrue18RevPBuf275.evalSign γ = 0) ∧ (∀ γ : BitAssignment 437, cleanRem 437 (437 - 275)
    γ → cleanRem 437 (437 - 275) (sTrue18RevPBuf275.evalBits γ) ∧ (∀ q : Wire 437, (∀ j, q ≠
    sTrue18WDefault j) → sTrue18RevPBuf275.evalBits γ q = γ q) ∧ (bitsVal (fun j ↦ γ
    (sTrue18WDefault j)) = sTrueRawValPBuf γ → ∀ j : Fin 18, sTrue18RevPBuf275.evalBits γ
    (sTrue18WDefault j) = 0)) := by
  dsimp only [sTrue18RevPBuf275]
  obtain ⟨hv, hcnt, hsgn, hbits⟩ := sTrue18FwdPBuf275_graft
  obtain ⟨_, _, _, hspec⟩ := sTrue18FwdPBuf275_spec
  refine ⟨hv, hcnt, hsgn, fun γ hγ ↦ ⟨(hspec γ hγ).1, (hspec γ hγ).2.1, fun hVal j ↦ ?_⟩⟩
  rw [(hbits γ hγ).2 j, congrFun (bitsVal_injective
    (hVal.trans ((ctxJointPBuf159_spec γ hγ).2.symm.trans
      (bitsVal_targetBit_eq_colListSum _).symm))) j, CharTwo.add_self_eq_zero]
attribute [local irreducible] ctxJointPBuf159 innerApex2 sTrue18FwdPBuf275 sTrue18RevPBuf275
set_option maxRecDepth 512
end P57JointSTrue18
end
end ConfigProd57BoothHoist
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 512

end Prod57BoothHoist
end
end ModProd57BoothHoist

end QuantumComputation.Specs.StoppingPowerSolution
