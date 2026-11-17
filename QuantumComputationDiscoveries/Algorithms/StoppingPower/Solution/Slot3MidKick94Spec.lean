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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPass2UnbarHarm
set_option Elab.async false
set_option compiler.extract_closed false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Leaf3PrepAndMidKickSpecs
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3PrepAndMidKickSpecs (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
# Compact `<= 94`-Clean-Wire Slot-3 `MidKick36` Specification & Realizer

Self-contained clean-scratch `Slot3MidKick36CompactSpec` contract, `.ofProg` and `.widen`
combinators, and `mClean <= 94`, `0 .TOFF` dynamic circuit realizer matching
`Slot3MidKick36_161w.progMidKick216_36_411` on active wires `[0..174)`.
-/

namespace Leaf3PrepAndMidKickSpecs

section ConfigLeaf3PrepAndMidKickSpecs

set_option maxRecDepth 2048
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency false

local instance (priority :=
  10) instLoc_Leaf3PrepAndMidKickSpecs_1InstNeZeroTwoPowW7 (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

open SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_lt wire_ne_of_gt CliffProg
  TempPhaseProg cleanRem)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (cleanRem_anti ValidCleanRem
  validCleanRem_mono TempCtx)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (ctxTempBit mul_mulVec_prog writeRegProg)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem tailScr)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (eval_onRegister_prog_ket
  realizes_of_validCleanRem)
open TwosCompAndWire0Cancel (twosComp8Int)
open MeasureBranchHadamardSem
  (ket bitSign matrix_ext_ket ket_TOFF ket_projector_zero
   projZeroAll ket_projZeroAll projZeroAll_conjTranspose
   RealizesCleanUnitary measureAndBranchSeq
   hadamardAll
   xReset writeSynd syndSign writeSynd_apply_of_not_mem)
open StreamingBchComparator (PreservesStoreConst)
open FastMidKick275Aux
open Prod57BoothHoist
  (p57DiagProj p57CleanDiagProj ket_p57DiagProj p57DiagProj_conjTranspose
   ket_p57CleanDiagProj realizesClean_andUncompute_diag)
open Slot3Exact216Oracle80
open Slot3MidKick36_161w

theorem mk94ToggleAnd_involutive {m : ℕ} (c₁ c₂ anc : Wire m)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (δ : BitAssignment m) :
    let δ₁ := Function.update δ anc (δ anc + δ c₁ * δ c₂)
    Function.update δ₁ anc (δ₁ anc + δ₁ c₁ * δ₁ c₂) = δ := by
  intro δ₁
  funext w
  by_cases hw : w = anc
  · subst hw
    simp [δ₁, Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
      add_assoc, CharTwo.add_self_eq_zero]
  · simp [δ₁, Function.update_of_ne hw]

theorem mk94EvalBits_injective {m : ℕ} :
    ∀ p : TempPhaseProg m, Function.Injective p.evalBits
  | .nil => Function.injective_id
  | .cliff c => fun _ _ h ↦ by
      have := congrArg c.inv.eval h
      simpa only [TempPhaseProg.evalBits, c.inv_eval] using this
  | .z _ => Function.injective_id
  | .seq p₁ p₂ => (mk94EvalBits_injective p₂).comp (mk94EvalBits_injective p₁)
  | .tempAnd c₁ c₂ anc _ h₁a h₂a body => by
      let tog := fun δ : BitAssignment m ↦ Function.update δ anc (δ anc + δ c₁ * δ c₂)
      have htog : Function.Involutive tog := mk94ToggleAnd_involutive c₁ c₂ anc h₁a h₂a
      exact htog.injective.comp ((mk94EvalBits_injective body).comp htog.injective)

open Classical in
theorem mk94ValidCleanRem_remMid_le {M rem remMid : ℕ} (hrem : rem ≤ M) (hmid : remMid ≤ M)
    (p : TempPhaseProg M) (hClean : ∀ β : BitAssignment M, cleanRem M rem β → cleanRem M
    remMid (p.evalBits β)) : remMid ≤ rem := by
  let pad : (Fin (M - rem) → ZMod 2) → BitAssignment M :=
    fun f w ↦ if hw : w.val < M - rem then f ⟨w.val, hw⟩ else 0
  let proj : BitAssignment M → (Fin (M - remMid) → ZMod 2) :=
    fun δ i ↦ δ ⟨i.val, by omega⟩
  have hpad_cl : ∀ f, cleanRem M rem (pad f) := fun f w hw ↦ by
    dsimp [pad]; rw [dite_eq_right (by omega)]
  have hinj : Function.Injective (fun f ↦ proj (p.evalBits (pad f))) := by
    intro f₁ f₂ heq
    have h₁ := hClean (pad f₁) (hpad_cl f₁)
    have h₂ := hClean (pad f₂) (hpad_cl f₂)
    have hp_eq : p.evalBits (pad f₁) = p.evalBits (pad f₂) := by
      funext w
      by_cases hw : w.val < M - remMid
      · exact congrFun heq ⟨w.val, hw⟩
      · exact (h₁ w (by omega)).trans (h₂ w (by omega)).symm
    have hpad_eq := mk94EvalBits_injective p hp_eq
    funext i
    have hi := congrFun hpad_eq ⟨i.val, by omega⟩
    simpa [pad, i.isLt] using hi
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
  have hle : M - rem ≤ M - remMid := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  omega

def mk94ExtZero {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁)
    (γ : BitAssignment M₁) : BitAssignment M₂ := fun w ↦ if e (g w) = w then γ (g w) else 0

theorem mk94ExtZero_emb {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁)
    (hge : ∀ i, g (e i) = i) (γ : BitAssignment M₁) (i : Wire M₁) :
    mk94ExtZero e g γ (e i) = γ i := by
  simp [mk94ExtZero, hge i]

theorem mk94ExtZero_update {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁)
    (_hge : ∀ i, g (e i) = i) (γ : BitAssignment M₁) {q : Wire M₂} (hq : e (g q) = q) (b : ZMod 2) :
    Function.update (mk94ExtZero e g γ) q b = mk94ExtZero e g (Function.update γ (g q) b) := by
  funext w
  by_cases hwq : w = q
  · subst hwq; simp [mk94ExtZero, hq]
  · simp only [Function.update_of_ne hwq, mk94ExtZero]
    by_cases hw : e (g w) = w
    · have hgne : g w ≠ g q := fun h ↦ hwq (by rw [← hw, ← hq, h])
      simp [hw, Function.update_of_ne hgne]
    · simp [hw]

def mk94CliffUses {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁) :
    CliffProg M₂ → Prop
  | .nil => True
  | .x q => e (g q) = q
  | .cnot c t _ => e (g c) = c ∧ e (g t) = t
  | .seq c₁ c₂ => mk94CliffUses e g c₁ ∧ mk94CliffUses e g c₂

def mk94CliffPullback {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁) :
    (c : CliffProg M₂) → mk94CliffUses e g c → CliffProg M₁
  | .nil, _ => .nil
  | .x q, _ => .x (g q)
  | .cnot c t hne, ⟨hc, ht⟩ =>
      .cnot (g c) (g t) (fun h ↦ hne (by rw [← hc, ← ht, h]))
  | .seq c₁ c₂, ⟨h₁, h₂⟩ =>
      .seq (mk94CliffPullback e g c₁ h₁) (mk94CliffPullback e g c₂ h₂)

theorem mk94CliffPullback_eval {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁)
    (hge : ∀ i, g (e i) = i) :
    ∀ (c : CliffProg M₂) (hc : mk94CliffUses e g c) (γ : BitAssignment M₁),
      c.eval (mk94ExtZero e g γ) = mk94ExtZero e g ((mk94CliffPullback e g c hc).eval γ)
  | .nil, _, _ => rfl
  | .x q, hq, γ => by
      change e (g q) = q at hq
      simp [CliffProg.eval, mk94CliffPullback, mk94ExtZero_update e g hge γ hq,
        mk94ExtZero, hq]
  | .cnot c t _, ⟨hc, ht⟩, γ => by
      simp [CliffProg.eval, mk94CliffPullback, mk94ExtZero_update e g hge γ ht,
        mk94ExtZero, hc, ht]
  | .seq c₁ c₂, ⟨h₁, h₂⟩, γ => by
      simp [CliffProg.eval, mk94CliffPullback, mk94CliffPullback_eval e g hge c₁ h₁,
        mk94CliffPullback_eval e g hge c₂ h₂]

def mk94ProgUses {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁) :
    TempPhaseProg M₂ → Prop
  | .nil => True
  | .cliff c => mk94CliffUses e g c
  | .z q => e (g q) = q
  | .seq p₁ p₂ => mk94ProgUses e g p₁ ∧ mk94ProgUses e g p₂
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      e (g c₁) = c₁ ∧ e (g c₂) = c₂ ∧ e (g anc) = anc ∧ mk94ProgUses e g body

def mk94ProgPullback {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁) :
    (p : TempPhaseProg M₂) → mk94ProgUses e g p → TempPhaseProg M₁
  | .nil, _ => .nil
  | .cliff c, hc => .cliff (mk94CliffPullback e g c hc)
  | .z q, _ => .z (g q)
  | .seq p₁ p₂, ⟨h₁, h₂⟩ =>
      .seq (mk94ProgPullback e g p₁ h₁) (mk94ProgPullback e g p₂ h₂)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, ⟨hc₁, hc₂, ha, hb⟩ =>
      .tempAnd (g c₁) (g c₂) (g anc)
        (fun h ↦ h₁₂ (by rw [← hc₁, ← hc₂, h]))
        (fun h ↦ h₁a (by rw [← hc₁, ← ha, h]))
        (fun h ↦ h₂a (by rw [← hc₂, ← ha, h]))
        (mk94ProgPullback e g body hb)

theorem mk94ProgPullback_countTempAnd {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁) :
    ∀ (p : TempPhaseProg M₂) (hp : mk94ProgUses e g p),
      (mk94ProgPullback e g p hp).countTempAnd = p.countTempAnd
  | .nil, _ => rfl
  | .cliff _, _ => rfl
  | .z _, _ => rfl
  | .seq p₁ p₂, ⟨h₁, h₂⟩ => by
      simp [mk94ProgPullback, TempPhaseProg.countTempAnd,
        mk94ProgPullback_countTempAnd e g p₁ h₁, mk94ProgPullback_countTempAnd e g p₂ h₂]
  | .tempAnd _ _ _ _ _ _ body, ⟨_, _, _, hb⟩ => by
      simp [mk94ProgPullback, TempPhaseProg.countTempAnd, mk94ProgPullback_countTempAnd e g body hb]

theorem mk94ProgPullback_eval {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁)
    (hge : ∀ i, g (e i) = i) :
    ∀ (p : TempPhaseProg M₂) (hp : mk94ProgUses e g p) (γ : BitAssignment M₁),
      p.evalBits (mk94ExtZero e g γ) = mk94ExtZero e g ((mk94ProgPullback e g p hp).evalBits γ) ∧
        (mk94ProgPullback e g p hp).evalSign γ = p.evalSign (mk94ExtZero e g γ)
  | .nil, _, _ => ⟨rfl, rfl⟩
  | .cliff c, hc, γ => ⟨mk94CliffPullback_eval e g hge c hc γ, rfl⟩
  | .z q, hq, γ => ⟨rfl, by
      change e (g q) = q at hq
      simp [mk94ProgPullback, TempPhaseProg.evalSign, mk94ExtZero, hq]⟩
  | .seq p₁ p₂, ⟨h₁, h₂⟩, γ => by
      obtain ⟨hb₁, hs₁⟩ := mk94ProgPullback_eval e g hge p₁ h₁ γ
      obtain ⟨hb₂, hs₂⟩ :=
        mk94ProgPullback_eval e g hge p₂ h₂ ((mk94ProgPullback e g p₁ h₁).evalBits γ)
      refine ⟨?_, ?_⟩
      · simp [mk94ProgPullback, TempPhaseProg.evalBits, hb₁, hb₂]
      · simp [mk94ProgPullback, TempPhaseProg.evalSign, hs₁, hb₁, hs₂]
  | .tempAnd c₁ c₂ anc _ _ _ body, ⟨hc₁, hc₂, ha, hb⟩, γ => by
      let γ₁ := Function.update γ (g anc) (γ (g anc) + γ (g c₁) * γ (g c₂))
      have hupd₁ : Function.update (mk94ExtZero e g γ) anc (mk94ExtZero e g γ anc +
          mk94ExtZero e g γ c₁ * mk94ExtZero e g γ c₂) = mk94ExtZero e g γ₁ := by
        have hv : mk94ExtZero e g γ anc + mk94ExtZero e g γ c₁ * mk94ExtZero e g γ c₂ =
            γ (g anc) + γ (g c₁) * γ (g c₂) := by
          simp [mk94ExtZero, hc₁, hc₂, ha]
        rw [hv, mk94ExtZero_update e g hge γ ha]
      obtain ⟨hbb, hsb⟩ := mk94ProgPullback_eval e g hge body hb γ₁
      let γ₂ := (mk94ProgPullback e g body hb).evalBits γ₁
      have hv₂ : mk94ExtZero e g γ₂ anc + mk94ExtZero e g γ₂ c₁ * mk94ExtZero e g γ₂ c₂ =
          γ₂ (g anc) + γ₂ (g c₁) * γ₂ (g c₂) := by
        simp [mk94ExtZero, hc₁, hc₂, ha]
      refine ⟨?_, ?_⟩
      · dsimp only [mk94ProgPullback, TempPhaseProg.evalBits]
        rw [hupd₁, hbb]
        change Function.update (mk94ExtZero e g γ₂) anc
            (mk94ExtZero e g γ₂ anc + mk94ExtZero e g γ₂ c₁ * mk94ExtZero e g γ₂ c₂) =
          mk94ExtZero e g (Function.update γ₂ (g anc) (γ₂ (g anc) + γ₂ (g c₁) * γ₂ (g c₂)))
        rw [hv₂, mk94ExtZero_update e g hge γ₂ ha]
      · dsimp only [mk94ProgPullback, TempPhaseProg.evalSign]
        rw [hupd₁]
        exact hsb

def mk94Emb411 (i : Wire 268) : Wire 411 :=
  if i.val < 196 then ⟨i.val, by omega⟩ else ⟨i.val + 143, by omega⟩

def mk94Retr411 (w : Wire 411) : Wire 268 :=
  if hw1 : w.val < 196 then ⟨w.val, by omega⟩
  else if hw2 : 339 ≤ w.val then ⟨w.val - 143, by omega⟩
  else ⟨0, by decide⟩

theorem mk94Retr411_emb (i : Wire 268) : mk94Retr411 (mk94Emb411 i) = i := by
  by_cases hi : i.val < 196
  · simp [mk94Emb411, mk94Retr411, hi]
  · have hnot : ¬ (i.val + 143 < 196) := by omega
    have hge : 339 ≤ i.val + 143 := by omega
    simp only [mk94Emb411, hi, ↓reduceIte, mk94Retr411, hnot, ↓reduceDIte, hge]
    ext; dsimp; omega

theorem mk94Emb_retr411_iff (w : Wire 411) :
    mk94Emb411 (mk94Retr411 w) = w ↔ w.val < 196 ∨ 339 ≤ w.val := by
  constructor
  · intro h
    by_cases h1 : w.val < 196
    · exact Or.inl h1
    · by_cases h2 : 339 ≤ w.val
      · exact Or.inr h2
      · exfalso
        have hv := congrArg Fin.val h
        simp [mk94Retr411, mk94Emb411, h1, h2] at hv
        omega
  · rintro (h1 | h2)
    · simp [mk94Retr411, mk94Emb411, h1]
    · have hn1 : ¬ w.val < 196 := by omega
      have hn2 : ¬ w.val - 143 < 196 := by omega
      simp only [mk94Retr411, hn1, ↓reduceDIte, h2, mk94Emb411, hn2, ↓reduceIte]
      ext; dsimp; omega

theorem mk94CleanRem_ext411 {rem : ℕ} (hrem : rem ≤ 72) {γ : BitAssignment 268} :
    cleanRem 411 rem (mk94ExtZero mk94Emb411 mk94Retr411 γ) ↔ cleanRem 268 rem γ := by
  constructor
  · intro h i hi
    have hemb : 411 - rem ≤ (mk94Emb411 i).val := by
      have hn : ¬ i.val < 196 := by omega
      simp only [mk94Emb411, hn, ↓reduceIte]; omega
    simpa only [mk94ExtZero_emb mk94Emb411 mk94Retr411 mk94Retr411_emb] using h (mk94Emb411 i) hemb
  · intro h w hw
    have hge339 : 339 ≤ w.val := by omega
    have heq := (mk94Emb_retr411_iff w).mpr (Or.inr hge339)
    have hhn : ¬ w.val < 196 := by omega
    simp only [mk94ExtZero, heq, ↓reduceIte]
    refine h _ ?_
    simp only [mk94Retr411, hhn, ↓reduceDIte, hge339]; omega

theorem mk94ValidCleanRem_pullback411 :
    ∀ (p : TempPhaseProg 411) (hp : mk94ProgUses mk94Emb411 mk94Retr411 p)
      {rem : ℕ} (_ : rem ≤ 72),
      ValidCleanRem 411 rem p →
      ValidCleanRem 268 rem (mk94ProgPullback mk94Emb411 mk94Retr411 p hp)
  | .nil, _, _, _, _ => trivial
  | .cliff _, _, _, _, _ => trivial
  | .z _, _, _, _, _ => trivial
  | .seq p₁ p₂, ⟨h₁, h₂⟩, rem, hrem, ⟨remMid, hmid411, hv1, hv2, hcl⟩ => by
      have hmid_le : remMid ≤ rem := mk94ValidCleanRem_remMid_le (by omega) hmid411 p₁ hcl
      have hmid72 : remMid ≤ 72 := le_trans hmid_le hrem
      refine ⟨remMid, by omega,
        mk94ValidCleanRem_pullback411 p₁ h₁ hrem hv1,
        mk94ValidCleanRem_pullback411 p₂ h₂ hmid72 hv2,
        fun γ hγ ↦ ?_⟩
      have h411 := hcl _ ((mk94CleanRem_ext411 hrem).mpr hγ)
      rw [(mk94ProgPullback_eval mk94Emb411 mk94Retr411 mk94Retr411_emb p₁ h₁ γ).1] at h411
      exact (mk94CleanRem_ext411 hmid72).mp h411
  | .tempAnd c₁ c₂ anc _ _ _ body, ⟨hc₁, hc₂, ha, hb⟩, rem, hrem, ⟨hanc, hvB, hrest⟩ => by
      have hge339 : 339 ≤ anc.val := by omega
      have hhn : ¬ anc.val < 196 := by omega
      have hanc_retr : (mk94Retr411 anc).val = anc.val - 143 := by
        simp [mk94Retr411, hhn, hge339]
      have hrem_eq : 268 - ((mk94Retr411 anc).val + 1) = 411 - (anc.val + 1) := by
        rw [hanc_retr]; omega
      have hrem'_le : 268 - ((mk94Retr411 anc).val + 1) ≤ 72 := by omega
      refine ⟨by rw [hanc_retr]; omega, ?_, fun γ₁ hγ₁ ↦ ?_⟩
      · rw [hrem_eq]
        exact mk94ValidCleanRem_pullback411 body hb (by omega) hvB
      · have hγ₁' : cleanRem 411 (411 - (anc.val + 1)) (mk94ExtZero mk94Emb411 mk94Retr411 γ₁) := by
          rw [← hrem_eq]; exact (mk94CleanRem_ext411 hrem'_le).mpr hγ₁
        obtain ⟨hr₁, hr₂, hra⟩ := hrest _ hγ₁'
        have hev := (mk94ProgPullback_eval mk94Emb411 mk94Retr411 mk94Retr411_emb body hb γ₁).1
        rw [hev] at hr₁ hr₂ hra
        simp only [mk94ExtZero, hc₁, hc₂, ha, ↓reduceIte] at hr₁ hr₂ hra
        exact ⟨hr₁, hr₂, hra⟩

/- ## Section 2: `Wire 268` Register Map & `331`-`TempAnd` Axis Arithmetic -/

def mk94Bank36W (r : Fin 36) : Wire 268 := ⟨196 + r.val, by omega⟩
def mk94Cat42W (m : Fin 42) : Wire 268 := ⟨107 + m.val, by omega⟩
def mk94Cat36W (m : Fin 36) : Wire 268 := ⟨113 + m.val, by omega⟩

theorem mk94Bank36W_inj : Function.Injective mk94Bank36W := fun a b h ↦ by
  have hv := congrArg Fin.val h; dsimp [mk94Bank36W] at hv; exact Fin.ext (by omega)

theorem mk94Cat36W_eq_cat42 (m : Fin 36) :
    mk94Cat36W m = mk94Cat42W ⟨6 + m.val, by omega⟩ :=
  Fin.ext (by dsimp [mk94Cat36W, mk94Cat42W]; omega)

theorem mk94Uses411_ltCore {w : Wire 411} (h : w.val < 196) : mk94Emb411 (mk94Retr411 w) = w :=
    (mk94Emb_retr411_iff w).mpr (Or.inl h)

theorem mk94Uses411_ge339 {w : Wire 411} (h : 339 ≤ w.val) : mk94Emb411 (mk94Retr411 w) = w :=
    (mk94Emb_retr411_iff w).mpr (Or.inr h)

theorem mk94CliffUses_inv {M₁ M₂ : ℕ} {e : Wire M₁ → Wire M₂} {g : Wire M₂ → Wire M₁} :
    ∀ {c : CliffProg M₂}, mk94CliffUses e g c → mk94CliffUses e g c.inv
  | .nil, _ => trivial
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨mk94CliffUses_inv h₂, mk94CliffUses_inv h₁⟩

def mk94CtxUses {M₁ M₂ : ℕ} (e : Wire M₁ → Wire M₂) (g : Wire M₂ → Wire M₁) :
    TempCtx M₂ → Prop
  | .hole => True
  | .seqPre c K => mk94CliffUses e g c ∧ mk94CtxUses e g K
  | .seqPost K c => mk94CtxUses e g K ∧ mk94CliffUses e g c
  | .tempAnd c₁ c₂ anc _ _ _ K =>
      e (g c₁) = c₁ ∧ e (g c₂) = c₂ ∧ e (g anc) = anc ∧ mk94CtxUses e g K

theorem mk94CtxUses_plug {M₁ M₂ : ℕ} {e : Wire M₁ → Wire M₂} {g : Wire M₂ → Wire M₁} :
    ∀ {K : TempCtx M₂} {body : TempPhaseProg M₂},
      mk94CtxUses e g K → mk94ProgUses e g body → mk94ProgUses e g (K.plug body)
  | .hole, _, _, hb => hb
  | .seqPre _ _, _, ⟨hc, hK⟩, hb => ⟨hc, mk94CtxUses_plug hK hb⟩
  | .seqPost _ _, _, ⟨hK, hc⟩, hb => ⟨mk94CtxUses_plug hK hb, hc⟩
  | .tempAnd _ _ _ _ _ _ _, _, ⟨h₁, h₂, ha, hK⟩, hb => ⟨h₁, h₂, ha, mk94CtxUses_plug hK hb⟩

theorem mk94CtxUses_append {M₁ M₂ : ℕ} {e : Wire M₁ → Wire M₂} {g : Wire M₂ → Wire M₁} :
    ∀ {F G : TempCtx M₂},
      mk94CtxUses e g F → mk94CtxUses e g G → mk94CtxUses e g (F.append G)
  | .hole, _, _, hG => hG
  | .seqPre _ _, _, ⟨hc, hF⟩, hG => ⟨hc, mk94CtxUses_append hF hG⟩
  | .seqPost _ _, _, ⟨hF, hc⟩, hG => ⟨mk94CtxUses_append hF hG, hc⟩
  | .tempAnd _ _ _ _ _ _ _, _, ⟨h₁, h₂, ha, hF⟩, hG => ⟨h₁, h₂, ha, mk94CtxUses_append hF hG⟩

theorem mk94Uses_xVec {W : ℕ} : ∀ (dst : Fin W → Wire 411),
    (∀ j, mk94Emb411 (mk94Retr411 (dst j)) = dst j) → mk94CliffUses mk94Emb411 mk94Retr411
    (fmkXVec W dst) := by
  induction W with
  | zero => intro _ _; trivial
  | succ W ih => intro dst hd; exact ⟨hd 0, ih _ (fun j ↦ hd j.succ)⟩

theorem mk94Uses_fanoutCnot :
    ∀ (W : ℕ) (ctrl : Wire 411) (dst : Fin W → Wire 411) (hne : ∀ j, ctrl ≠ dst j),
      mk94Emb411 (mk94Retr411 ctrl) = ctrl →
      (∀ j, mk94Emb411 (mk94Retr411 (dst j)) = dst j) →
      mk94CliffUses mk94Emb411 mk94Retr411 (fmkFanoutCnot W ctrl dst hne)
  | 0, _, _, _, _, _ => trivial
  | W + 1, ctrl, _dst, _hne, hc, hd =>
      ⟨⟨hc, hd 0⟩, mk94Uses_fanoutCnot W ctrl _ _ hc (fun j ↦ hd j.succ)⟩

theorem mk94Uses_inPlaceAddModCarry :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ 411)
      (b acc : Fin (W + 1) → Wire 411) (cin : Wire 411)
      (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hc : cin.val < cur),
      339 ≤ cur →
      (∀ j, mk94Emb411 (mk94Retr411 (b j)) = b j) →
      (∀ j, mk94Emb411 (mk94Retr411 (acc j)) = acc j) →
      mk94Emb411 (mk94Retr411 cin) = cin →
      mk94ProgUses mk94Emb411 mk94Retr411
        (fmkInPlaceAddModCarry W cur hcur b acc cin hab hac hbc hb ha hc)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hub, hua, huc =>
      ⟨⟨hub 0, hua 0⟩, ⟨huc, hua 0⟩⟩
  | W + 1, cur, hcur, b, acc, cin, hab, hac, hbc, hb, ha, hc, h339, hub, hua, huc => by
      dsimp only [fmkInPlaceAddModCarry]
      have hcout : mk94Emb411 (mk94Retr411 ⟨cur, by omega⟩) = ⟨cur, by omega⟩ :=
        mk94Uses411_ge339 (by dsimp; omega)
      have hrec := mk94Uses_inPlaceAddModCarry W (cur + 1) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) ⟨cur, by omega⟩
        (fun j ↦ hab j.succ)
        (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp; omega))
        (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp; omega))
        (fun j ↦ lt_trans (hb j.succ) (by omega))
        (fun j ↦ lt_trans (ha j.succ) (by omega))
        (by dsimp; omega)
        (by omega) (fun j ↦ hub j.succ) (fun j ↦ hua j.succ) hcout
      exact ⟨⟨⟨huc, hub 0⟩, ⟨huc, hua 0⟩⟩, ⟨⟨hub 0, hua 0, hcout, ⟨⟨huc, hcout⟩, hrec, ⟨huc,
        hcout⟩⟩⟩, ⟨⟨huc, hub 0⟩, ⟨hub 0, hua 0⟩⟩⟩⟩

theorem mk94Uses_step2b36 (u0 : Wire 411)
    (hu0 : ¬(113 ≤ u0.val ∧ u0.val < 149) ∧ u0.val < 339) (huBound : u0.val < 196) :
    mk94ProgUses mk94Emb411 mk94Retr411 (mk36Step2b36_nodummy u0 hu0) := by
  dsimp only [mk36Step2b36_nodummy]
  have hu : mk94Emb411 (mk94Retr411 u0) = u0 := mk94Uses411_ltCore huBound
  have hc0 : mk94Emb411 (mk94Retr411 ⟨375, by decide⟩) = ⟨375, by decide⟩ :=
    mk94Uses411_ge339 (by decide)
  have hb0 : mk94Emb411 (mk94Retr411 (mk36Bank36W 0)) = mk36Bank36W 0 :=
    mk94Uses411_ge339 (by dsimp [mk36Bank36W]; omega)
  have hbt : ∀ j : Fin 35, mk94Emb411 (mk94Retr411 (mk36Bank36W j.succ)) = mk36Bank36W j.succ :=
    fun j ↦ mk94Uses411_ge339 (by simp only [mk36Bank36W, Fin.val_succ]; omega)
  have hh36 : ∀ j : Fin 36, mk94Emb411 (mk94Retr411 (mk36H36NoDummy u0 j)) = mk36H36NoDummy u0 j :=
    by
    intro j; refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [mk36H36NoDummy, Fin.snoc_last]; exact hu
    · simp only [mk36H36NoDummy, Fin.snoc_castSucc]; exact hbt i
  have hcat : ∀ j : Fin 36, mk94Emb411 (mk94Retr411 (mk36Cat36W j)) = mk36Cat36W j :=
    fun j ↦ mk94Uses411_ltCore (by dsimp [mk36Cat36W]; omega)
  refine mk94CtxUses_plug (mk94CtxUses_append ⟨hu, hb0, hc0, trivial⟩ ?_)
    (mk94Uses_inPlaceAddModCarry 35 376 _ _ _ _ _ _ _ _ _ _ (by decide) hh36 hcat hc0)
  refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;>
    exact ⟨⟨hu, hc0⟩, hc0, hu, mk94Uses_fanoutCnot 35 u0 _ _ hu hbt⟩

theorem mk94Uses_shiftStep36 (uBit : Wire 411) (curCarry : ℕ) (s : Fin 8) (hu : ¬(113 ≤
    uBit.val ∧ uBit.val < 149) ∧ ¬(339 ≤ uBit.val ∧ uBit.val < 375) ∧ uBit.val < curCarry)
    (hcur : 375 ≤ curCarry ∧ curCarry + (35 - s.val) ≤ 411)
    (huU : mk94Emb411 (mk94Retr411 uBit) = uBit) : mk94ProgUses mk94Emb411 mk94Retr411
    (mk36ShiftStep36_at uBit curCarry s hu hcur) := by
  dsimp only [mk36ShiftStep36_at]
  have hbs : ∀ j : Fin (35 - s.val + 1),
      mk94Emb411 (mk94Retr411 (mk36Bank36W ⟨j.val, by omega⟩)) = mk36Bank36W ⟨j.val, by omega⟩ :=
    fun _ ↦ mk94Uses411_ge339 (by dsimp [mk36Bank36W]; omega)
  have hcs : ∀ j : Fin (35 - s.val + 1),
      mk94Emb411 (mk94Retr411 (mk36Cat36W ⟨s.val + j.val, by omega⟩)) =
        mk36Cat36W ⟨s.val + j.val, by omega⟩ :=
    fun _ ↦ mk94Uses411_ltCore (by dsimp [mk36Cat36W]; omega)
  refine mk94CtxUses_plug ?_ (mk94Uses_inPlaceAddModCarry (35 - s.val) curCarry _ _ _ _ _ _ _
    _ _ _ (by omega) hbs hcs huU)
  refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;>
    exact ⟨huU, mk94Uses_fanoutCnot _ uBit _ _ huU hbs⟩

theorem mk94Uses_interleavedU9 (w : Fin 3) :
    ∀ (rem : ℕ) (hrem : rem ≤ 7),
      mk94ProgUses mk94Emb411 mk94Retr411 (mk36InterleavedU9Shift36 w rem hrem)
  | 0, _ => mk94Uses_shiftStep36 _ 383 ⟨7, by decide⟩ _ _ (mk94Uses411_ge339 (by decide))
  | rem + 1, hrem => by
      dsimp only [mk36InterleavedU9Shift36]
      have hpN : mk94Emb411 (mk94Retr411 (mk36PNewW w ⟨8 - (rem + 1), by omega⟩)) = _ :=
        mk94Uses411_ltCore (by dsimp [mk36PNewW]; omega)
      have hpO : mk94Emb411 (mk94Retr411 (mk36POldW w ⟨8 - (rem + 1), by omega⟩)) = _ :=
        mk94Uses411_ltCore (by dsimp [mk36POldW]; omega)
      have hck : mk94Emb411 (mk94Retr411 ⟨375 + (8 - (rem + 1)) - 1, by omega⟩) = _ :=
        mk94Uses411_ge339 (by dsimp; omega)
      have hout : mk94Emb411 (mk94Retr411 ⟨375 + (8 - (rem + 1)), by omega⟩) = _ :=
        mk94Uses411_ge339 (by dsimp; omega)
      refine ⟨mk94CtxUses_plug ?_ (mk94Uses_shiftStep36 _ _ _ _ _ hpN),
        mk94CtxUses_plug ?_ (mk94Uses_interleavedU9 w rem (by omega))⟩
      · refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;> exact ⟨⟨hpO, hpN⟩, ⟨hck, hpN⟩⟩
      · unfold fmkCtxCarryStep
        refine mk94CtxUses_append ?_ (mk94CtxUses_append ⟨hpN, hpO, hout, trivial⟩ ?_)
        · refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;> exact ⟨⟨hck, hpN⟩, ⟨hck, hpO⟩⟩
        · refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;> exact ⟨⟨hck, hpO⟩, ⟨hck, hpN⟩, ⟨hck, hout⟩⟩

theorem mk94Uses_mulAxis (w : Fin 3) :
    mk94ProgUses mk94Emb411 mk94Retr411 (mk36MulAxis36_no2a w) := by
  dsimp only [mk36MulAxis36_no2a]
  have hpN0 : mk94Emb411 (mk94Retr411 (mk36PNewW w 0)) = _ :=
    mk94Uses411_ltCore (by dsimp [mk36PNewW]; omega)
  have hpO0 : mk94Emb411 (mk94Retr411 (mk36POldW w 0)) = _ :=
    mk94Uses411_ltCore (by dsimp [mk36POldW]; omega)
  have hc1 : mk94Emb411 (mk94Retr411 ⟨375, by decide⟩) = _ := mk94Uses411_ge339 (by decide)
  have hcFlip : mk94CliffUses mk94Emb411 mk94Retr411 (mk36FlipP w) :=
    ⟨mk94Uses411_ltCore (by dsimp [mk36FlipP, mk36PNewW]; omega),
      mk94Uses_xVec (fun j : Fin 7 ↦ mk36POldW w ⟨j.val, by omega⟩)
        (fun j ↦ mk94Uses411_ltCore (by dsimp [mk36POldW]; omega))⟩
  exact mk94CtxUses_plug ⟨hcFlip, trivial, mk94CliffUses_inv hcFlip⟩
    ⟨mk94CtxUses_plug ⟨⟨hpO0, hpN0⟩, trivial, ⟨hpO0, hpN0⟩⟩
        (mk94Uses_step2b36 _ _ (by dsimp [mk36PNewW]; omega)),
      mk94CtxUses_plug ⟨hpN0, hpO0, hc1, trivial⟩ (mk94Uses_interleavedU9 w 7 le_rfl)⟩

def mk94MulAxis36_no2a (w : Fin 3) : TempPhaseProg 268 :=
  mk94ProgPullback mk94Emb411 mk94Retr411 (mk36MulAxis36_no2a w) (mk94Uses_mulAxis w)

theorem mk94MulAxis36_no2a_spec (w : Fin 3) :
    (mk94MulAxis36_no2a w).countTempAnd = 296 ∧
      fmkIsMutBlock 268 36 (fun q ↦ 107 ≤ q.val ∧ q.val < 149) (mk94MulAxis36_no2a w) ∧
      (∀ γ : BitAssignment 268, cleanRem 268 36 γ →
        let pNew0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let pOld0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let K_val := bitsVal (fun m : Fin 36 ↦ γ (mk94Bank36W m))
        ((bitsVal (fun m ↦
          (mk94MulAxis36_no2a w).evalBits γ (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
            64 * ((twosComp8Int pNew0 - twosComp8Int pOld0) * (K_val : ℤ) -
              ((K_val / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ)) := by
  obtain ⟨hCnt, hMut, hEv⟩ := mk36MulAxis36_no2a_spec w
  have hCnt268 : (mk94MulAxis36_no2a w).countTempAnd = 296 :=
    (mk94ProgPullback_countTempAnd mk94Emb411 mk94Retr411 _ _).trans hCnt
  have hVal268 : ValidCleanRem 268 36 (mk94MulAxis36_no2a w) :=
    mk94ValidCleanRem_pullback411 _ _ (by decide) hMut.1
  refine ⟨hCnt268, ⟨hVal268, fun γ hγ ↦ ?_, fun γ hγ q hq ↦ ?_, fun γ hγ q hq ↦ ?_⟩, fun γ hγ
    ↦ ?_⟩
  · have h411 := (mk94CleanRem_ext411 (by decide : 36 ≤ 72)).mpr hγ
    exact (mk94ProgPullback_eval mk94Emb411 mk94Retr411 mk94Retr411_emb _ _ γ).2.trans (hMut.2.1 _
      h411)
  · have h411 := (mk94CleanRem_ext411 (by decide : 36 ≤ 72)).mpr hγ
    have hout := hMut.2.2.1 _ h411
    rw [(mk94ProgPullback_eval mk94Emb411 mk94Retr411 mk94Retr411_emb _ _ γ).1] at hout
    exact (mk94CleanRem_ext411 (by decide : 36 ≤ 72)).mp hout q hq
  · have h411 := (mk94CleanRem_ext411 (by decide : 36 ≤ 72)).mpr hγ
    have hnot : ¬(107 ≤ (mk94Emb411 q).val ∧ (mk94Emb411 q).val < 149) := by
      by_cases hlt : q.val < 196
      · simpa [mk94Emb411, hlt] using hq
      · simp only [mk94Emb411, hlt, ↓reduceIte]; omega
    have hnon := hMut.2.2.2 _ h411 (mk94Emb411 q) hnot
    rw [(mk94ProgPullback_eval mk94Emb411 mk94Retr411 mk94Retr411_emb _ _ γ).1,
      mk94ExtZero_emb mk94Emb411 mk94Retr411 mk94Retr411_emb,
      mk94ExtZero_emb mk94Emb411 mk94Retr411 mk94Retr411_emb] at hnon
    exact hnon
  · have h411 := (mk94CleanRem_ext411 (by decide : 36 ≤ 72)).mpr hγ
    have hev411 := hEv _ h411
    dsimp only at hev411 ⊢
    have hpN_eq :
        (fun b : Fin 8 ↦ mk94ExtZero mk94Emb411 mk94Retr411 γ ⟨150 + 8 * w.val + b.val, by omega⟩) =
        (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩) := funext fun b ↦ by
      have hemb : (⟨150 + 8 * w.val + b.val, by omega⟩ : Wire 411) =
          mk94Emb411 ⟨150 + 8 * w.val + b.val, by omega⟩ := by
        simp [mk94Emb411, show 150 + 8 * w.val + b.val < 196 by omega]
      rw [hemb, mk94ExtZero_emb mk94Emb411 mk94Retr411 mk94Retr411_emb]
    have hpO_eq :
        (fun b : Fin 8 ↦ mk94ExtZero mk94Emb411 mk94Retr411 γ ⟨8 * w.val + b.val, by omega⟩) =
        (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩) := funext fun b ↦ by
      have hemb : (⟨8 * w.val + b.val, by omega⟩ : Wire 411) =
          mk94Emb411 ⟨8 * w.val + b.val, by omega⟩ := by
        simp [mk94Emb411, show 8 * w.val + b.val < 196 by omega]
      rw [hemb, mk94ExtZero_emb mk94Emb411 mk94Retr411 mk94Retr411_emb]
    have hbank_eq :
        (fun m : Fin 36 ↦ mk94ExtZero mk94Emb411 mk94Retr411 γ (mk36Bank36W m)) =
        (fun m : Fin 36 ↦ γ (mk94Bank36W m)) := funext fun m ↦ by
      have hemb : mk36Bank36W m = mk94Emb411 (mk94Bank36W m) := by
        have hn : ¬ (196 + m.val < 196) := by omega
        simp only [mk94Emb411, mk94Bank36W, hn, ↓reduceIte, mk36Bank36W]
        ext; dsimp; omega
      rw [hemb, mk94ExtZero_emb mk94Emb411 mk94Retr411 mk94Retr411_emb]
    have hcat_in :
        (fun m : Fin 42 ↦ mk94ExtZero mk94Emb411 mk94Retr411 γ (mk36Cat42W m)) =
        (fun m : Fin 42 ↦ γ (mk94Cat42W m)) := funext fun m ↦ by
      have hemb : mk36Cat42W m = mk94Emb411 (mk94Cat42W m) := by
        simp [mk94Emb411, mk94Cat42W, mk36Cat42W, show 107 + m.val < 196 by omega]
      rw [hemb, mk94ExtZero_emb mk94Emb411 mk94Retr411 mk94Retr411_emb]
    have hcat_out :
        (fun m : Fin 42 ↦ (mk36MulAxis36_no2a w).evalBits
          (mk94ExtZero mk94Emb411 mk94Retr411 γ) (mk36Cat42W m)) =
        (fun m : Fin 42 ↦ (mk94MulAxis36_no2a w).evalBits γ (mk94Cat42W m)) := funext fun m ↦ by
      have hemb : mk36Cat42W m = mk94Emb411 (mk94Cat42W m) := by
        simp [mk94Emb411, mk94Cat42W, mk36Cat42W, show 107 + m.val < 196 by omega]
      rw [(mk94ProgPullback_eval mk94Emb411 mk94Retr411 mk94Retr411_emb _ _ γ).1,
        hemb, mk94ExtZero_emb mk94Emb411 mk94Retr411 mk94Retr411_emb]
      rfl
    simpa only [hpN_eq, hpO_eq, hbank_eq, hcat_in, hcat_out] using hev411

attribute [local irreducible] mk94MulAxis36_no2a

def mk94HalfBank36W : Fin 36 → Wire 268 :=
  Fin.snoc (fun j : Fin 35 ↦ mk94Bank36W j.succ) ⟨232, by decide⟩

theorem mk94HalfBank36W_val_bounds (j : Fin 36) :
    197 ≤ (mk94HalfBank36W j).val ∧ (mk94HalfBank36W j).val < 233 := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [mk94HalfBank36W, Fin.snoc_last]; decide
  · simp only [mk94HalfBank36W, Fin.snoc_castSucc, mk94Bank36W, Fin.val_succ]; omega

theorem mk94HalfBank36W_inj : Function.Injective mk94HalfBank36W := by
  intro a b
  refine Fin.lastCases ?_ (fun i ↦ ?_) a <;> refine Fin.lastCases ?_ (fun j ↦ ?_) b <;> intro h
  · rfl
  · simp only [mk94HalfBank36W, Fin.snoc_last, Fin.snoc_castSucc] at h
    have hv := congrArg Fin.val h; dsimp only [mk94Bank36W, Fin.val_succ] at hv; omega
  · simp only [mk94HalfBank36W, Fin.snoc_last, Fin.snoc_castSucc] at h
    have hv := congrArg Fin.val h; dsimp only [mk94Bank36W, Fin.val_succ] at hv; omega
  · simp only [mk94HalfBank36W, Fin.snoc_castSucc] at h
    have hv := congrArg Fin.val h; dsimp only [mk94Bank36W, Fin.val_succ] at hv
    exact congrArg Fin.castSucc (Fin.ext (by omega))

/-- `35`-`TempAnd` in-place `36`-bit modular addition `cat36 += halfBank36 (mod 2^36)` cancelling
the `- (K_val / 2)` Booth bias when wire `232` is `0` (`cleanRem 268 36`). -/
def mk94AddHalfBank36 : TempPhaseProg 268 :=
  let c1W : Wire 268 := ⟨233, by decide⟩
  let bTail : Fin 35 → Wire 268 := fun j ↦ mk94HalfBank36W j.succ
  let aTail : Fin 35 → Wire 268 := fun j ↦ mk94Cat36W j.succ
  let K0 : TempCtx 268 :=
    ctxTempBit (mk94HalfBank36W 0) (mk94Cat36W 0) c1W
      (wire_ne_of_gt (by have := (mk94HalfBank36W_val_bounds 0).1; dsimp [mk94Cat36W]; omega))
      (wire_ne_of_lt (by exact (mk94HalfBank36W_val_bounds 0).2))
      (wire_ne_of_lt (by dsimp [mk94Cat36W, c1W]; omega))
  let addTail : TempPhaseProg 268 :=
    fmkInPlaceAddModCarry 34 234 (by decide) bTail aTail c1W
      (fun j ↦ wire_ne_of_lt (by
        have := (mk94HalfBank36W_val_bounds j.succ).1
        simp only [bTail, aTail, mk94Cat36W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by simp only [aTail, mk94Cat36W, c1W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by exact (mk94HalfBank36W_val_bounds j.succ).2))
      (fun j ↦ by have := (mk94HalfBank36W_val_bounds j.succ).2; dsimp [bTail]; omega)
      (fun j ↦ by simp only [aTail, mk94Cat36W, Fin.val_succ]; omega)
      (by decide)
  .seq (K0.plug addTail)
    (.cliff (.cnot (mk94HalfBank36W 0) (mk94Cat36W 0)
      (wire_ne_of_gt (by have := (mk94HalfBank36W_val_bounds 0).1; dsimp [mk94Cat36W]; omega))))

theorem mk94AddHalfBank36_spec :
    mk94AddHalfBank36.countTempAnd = 35 ∧
      fmkIsMutBlock 268 36 (fun w ↦ 107 ≤ w.val ∧ w.val < 149) mk94AddHalfBank36 ∧
      (∀ γ : BitAssignment 268, cleanRem 268 36 γ →
        let K_val := bitsVal (fun m : Fin 36 ↦ γ (mk94Bank36W m))
        ((bitsVal (fun m ↦ mk94AddHalfBank36.evalBits γ (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
            64 * ((K_val / 2 : ℕ) : ℤ)).emod (2 ^ 42 : ℤ)) := by
  let mutCat : Wire 268 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
  let mutCat36 : Wire 268 → Prop := fun w ↦ 113 ≤ w.val ∧ w.val < 149
  let mutTail : Wire 268 → Prop := fun w ↦ 114 ≤ w.val ∧ w.val < 149
  let c1W : Wire 268 := ⟨233, by decide⟩
  let bTail : Fin 35 → Wire 268 := fun j ↦ mk94HalfBank36W j.succ
  let aTail : Fin 35 → Wire 268 := fun j ↦ mk94Cat36W j.succ
  let K0 : TempCtx 268 :=
    ctxTempBit (mk94HalfBank36W 0) (mk94Cat36W 0) c1W
      (wire_ne_of_gt (by have := (mk94HalfBank36W_val_bounds 0).1; dsimp [mk94Cat36W]; omega))
      (wire_ne_of_lt (by exact (mk94HalfBank36W_val_bounds 0).2))
      (wire_ne_of_lt (by dsimp [mk94Cat36W, c1W]; omega))
  let addTail : TempPhaseProg 268 :=
    fmkInPlaceAddModCarry 34 234 (by decide) bTail aTail c1W
      (fun j ↦ wire_ne_of_lt (by
        have := (mk94HalfBank36W_val_bounds j.succ).1
        simp only [bTail, aTail, mk94Cat36W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by simp only [aTail, mk94Cat36W, c1W, Fin.val_succ]; omega))
      (fun j ↦ wire_ne_of_lt (by exact (mk94HalfBank36W_val_bounds j.succ).2))
      (fun j ↦ by have := (mk94HalfBank36W_val_bounds j.succ).2; dsimp [bTail]; omega)
      (fun j ↦ by simp only [aTail, mk94Cat36W, Fin.val_succ]; omega) (by decide)
  have hb_inj : Function.Injective bTail := mk94HalfBank36W_inj.comp (Fin.succ_injective 35)
  have ha_inj : Function.Injective aTail := fun i j h ↦ by
    have hv := congrArg Fin.val h; simp only [aTail, mk94Cat36W, Fin.val_succ] at hv;
      exact Fin.ext (by omega)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec 34 234 (by decide) bTail aTail c1W
    (fun i j ↦ wire_ne_of_lt (by
      have := (mk94HalfBank36W_val_bounds j.succ).1
      simp only [bTail, aTail, mk94Cat36W, Fin.val_succ]; omega))
    (fun j ↦ wire_ne_of_lt (by simp only [aTail, mk94Cat36W, c1W, Fin.val_succ]; omega))
    (fun j ↦ wire_ne_of_lt (by exact (mk94HalfBank36W_val_bounds j.succ).2))
    hb_inj ha_inj
    (fun j ↦ by have := (mk94HalfBank36W_val_bounds j.succ).2; dsimp [bTail]; omega)
    (fun j ↦ by simp only [aTail, mk94Cat36W, Fin.val_succ]; omega) (by decide)
  have hdK0 : K0.DisjointFrom mutTail :=
    ⟨by have := (mk94HalfBank36W_val_bounds 0).1; dsimp [mutTail]; omega,
      by dsimp [mutTail, mk94Cat36W]; omega,
      by dsimp [mutTail, c1W]; omega, trivial⟩
  have hsK0 : K0.SupportsBelowCtx 234 := ⟨by dsimp [c1W]; omega, trivial⟩
  have hlK0 : fmkTempCtxLiftEx 233 234 K0 :=
    fmkTempCtxLiftEx_tempBit (cur := 233) (by decide) (mk94HalfBank36W 0) (mk94Cat36W 0)
      _ (mk94HalfBank36W_val_bounds 0).2 (by dsimp [mk94Cat36W]; omega)
  have hAddNon : ∀ δ, cleanRem 268 (268 - 234) δ → ∀ w, ¬ mutTail w → addTail.evalBits δ w = δ w :=
    fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦
      hw (by rw [hj]; simp only [mutTail, aTail, mk94Cat36W, Fin.val_succ]; omega)
  obtain ⟨hvP, hcP, hsP, hbP⟩ := fmkGraft_mutating_clean (M := 268) (rem := 268 - 233)
    (curHole := 234) mutTail K0 hdK0 hsK0 (by decide) K0.fwdBits (fmkTempCtxLiftEx_probe hlK0)
    addTail hvAdd hAddNon
  have hK0_cl : ∀ γ, cleanRem 268 (268 - 233) γ → cleanRem 268 (268 - 234) (K0.fwdBits γ) :=
    fun γ hγ ↦ fmkSupportsBelowCtx_cleanRem hsK0 γ (cleanRem_anti (by decide) hγ)
  have hMut1 : fmkIsMutBlock 268 (268 - 233) mutCat36 (K0.plug addTail) :=
    ⟨hvP, fun γ hγ ↦ (hsP γ hγ).trans (hsAdd _ (hK0_cl γ hγ)),
      fun γ hγ w hw ↦ by rw [hbP γ hγ w, fmkIteNeg (by dsimp [mutTail]; omega)]; exact hγ w hw,
      fun γ hγ w hw ↦ by rw [hbP γ hγ w, fmkIteNeg (fun ht ↦ hw ⟨by omega, ht.2⟩)]⟩
  let cLsb : CliffProg 268 := .cnot (mk94HalfBank36W 0) (mk94Cat36W 0)
    (wire_ne_of_gt (by have := (mk94HalfBank36W_val_bounds 0).1; dsimp [mk94Cat36W]; omega))
  have hMut2 : fmkIsMutBlock 268 (268 - 233) mutCat36 (.cliff cLsb) :=
    ⟨trivial, fun _ _ ↦ rfl,
      fun γ hγ w hw ↦ by
        dsimp [TempPhaseProg.evalBits, cLsb, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [mk94Cat36W]; omega))]
        exact hγ w hw,
      fun γ _ w hw ↦ by
        dsimp [TempPhaseProg.evalBits, cLsb, CliffProg.eval]
        exact Function.update_of_ne (fun h ↦ hw (by
          rw [h]; dsimp [mutCat36, mk94Cat36W]; omega)) _ _⟩
  have hMut35 := fmkIsMutBlock_seq (by decide) hMut1 hMut2
  have hMut36 : fmkIsMutBlock 268 36 mutCat mk94AddHalfBank36 :=
    ⟨validCleanRem_mono (by decide : 268 - 233 ≤ 36) hMut35.1,
      fun γ hγ ↦ hMut35.2.1 γ (cleanRem_anti (by decide) hγ),
      fun γ hγ w hw ↦ by
        dsimp only [mk94AddHalfBank36]
        rw [hMut35.2.2.2 γ (cleanRem_anti (by decide) hγ) w (by dsimp [mutCat36]; omega)]
        exact hγ w hw,
      fun γ hγ w hw ↦ by
        dsimp only [mk94AddHalfBank36]
        exact hMut35.2.2.2 γ (cleanRem_anti (by decide) hγ) w (fun h ↦ hw ⟨by omega, h.2⟩)⟩
  have hCnt35 : mk94AddHalfBank36.countTempAnd = 35 := by
    change (K0.plug addTail).countTempAnd + 0 = 35
    rw [Nat.add_zero, hcP]
    change 1 + addTail.countTempAnd = 35
    dsimp only [addTail]
    rw [fmkInPlaceAddModCarry_countTempAnd]
  refine ⟨hCnt35, hMut36, fun γ hγ ↦ ?_⟩
  have hγ35 : cleanRem 268 (268 - 233) γ := cleanRem_anti (by decide) hγ
  let δ := K0.fwdBits γ
  have hδ_eq : δ = Function.update γ c1W (γ (mk94HalfBank36W 0) * γ (mk94Cat36W 0)) := by
    dsimp only [δ, K0, ctxTempBit, TempCtx.fwdBits]
    rw [hγ35 c1W (by decide), zero_add]
  have hδ_cl : cleanRem 268 (268 - 234) δ := hK0_cl γ hγ35
  let γ1 := (K0.plug addTail).evalBits γ
  have hγ1_0 : γ1 (mk94Cat36W 0) = γ (mk94Cat36W 0) := by
    dsimp only [γ1]; rw [hbP γ hγ35 (mk94Cat36W 0), fmkIteNeg (by
      dsimp [mutTail, mk94Cat36W]; omega)]
  have hγ1_b0 : γ1 (mk94HalfBank36W 0) = γ (mk94HalfBank36W 0) := by
    dsimp only [γ1]
    rw [hbP γ hγ35 (mk94HalfBank36W 0),
      fmkIteNeg (by have := (mk94HalfBank36W_val_bounds 0).1; dsimp [mutTail]; omega)]
  have hγ1_tail : ∀ j : Fin 35, γ1 (aTail j) = addTail.evalBits δ (aTail j) := fun j ↦ by
    dsimp only [γ1]
    rw [hbP γ hγ35 (aTail j), fmkItePos (by
      simp only [mutTail, aTail, mk94Cat36W, Fin.val_succ]; omega)]
  have hout0 : mk94AddHalfBank36.evalBits γ (mk94Cat36W 0) =
      γ (mk94Cat36W 0) + γ (mk94HalfBank36W 0) := by
    change Function.update γ1 (mk94Cat36W 0) (γ1 (mk94Cat36W 0) +
      γ1 (mk94HalfBank36W 0)) (mk94Cat36W 0) = _
    rw [Function.update_self, hγ1_0, hγ1_b0]
  have hout_tail : (fun j : Fin 35 ↦ mk94AddHalfBank36.evalBits γ (mk94Cat36W j.succ)) =
      fun j : Fin 35 ↦ addTail.evalBits δ (aTail j) := funext fun j ↦ by
    change Function.update γ1 (mk94Cat36W 0) (γ1 (mk94Cat36W 0) + γ1 (mk94HalfBank36W 0))
      (mk94Cat36W j.succ) = _
    rw [Function.update_of_ne (wire_ne_of_gt (by simp only [mk94Cat36W, Fin.val_succ]; omega))]
    exact hγ1_tail j
  have hTailVal := (hAdd δ hδ_cl).2.2
  have hδ_a : (fun j : Fin 35 ↦ δ (aTail j)) = fun j ↦ γ (mk94Cat36W j.succ) := funext fun j ↦ by
    rw [hδ_eq, Function.update_of_ne (wire_ne_of_lt (by
      simp only [aTail, mk94Cat36W, c1W, Fin.val_succ]; omega))]
  have hδ_b : (fun j : Fin 35 ↦ δ (bTail j)) = fun j ↦ γ (mk94HalfBank36W j.succ) := funext fun j ↦
    by
    rw [hδ_eq, Function.update_of_ne (wire_ne_of_lt (mk94HalfBank36W_val_bounds j.succ).2)]
  have hδ_c1 : δ c1W = γ (mk94HalfBank36W 0) * γ (mk94Cat36W 0) := by
    rw [hδ_eq, Function.update_self]
  rw [hδ_a, hδ_b, hδ_c1] at hTailVal
  have h36_mod : ((bitsVal (fun m : Fin 36 ↦ mk94AddHalfBank36.evalBits γ (mk94Cat36W m)) :
      ℤ)).emod (2 ^ 36 : ℤ) = ((bitsVal (fun m : Fin 36 ↦ γ (mk94Cat36W m)) : ℤ) + (bitsVal
      (fun m : Fin 36 ↦ γ (mk94HalfBank36W m)) : ℤ)).emod (2 ^ 36 : ℤ) := by
    rw[fmkBitsVal_succ_split (fun m ↦ mk94AddHalfBank36.evalBits γ (mk94Cat36W m)), hout0,
        hout_tail, hTailVal, fmkBitsVal_succ_split (fun m ↦ γ (mk94Cat36W m)),
        fmkBitsVal_succ_split (fun m ↦ γ (mk94HalfBank36W m))]
    have hha := fmkHalfAdd_val_eq (γ (mk94Cat36W 0)) (γ (mk94HalfBank36W 0))
    rw [mul_comm (γ (mk94HalfBank36W 0)) (γ (mk94Cat36W 0)),
      show 2 ^ (34 + 1) = 2 ^ 35 from rfl]
    set cT := bitsVal (fun j : Fin 35 ↦ γ (mk94Cat36W j.succ))
    set bT := bitsVal (fun j : Fin 35 ↦ γ (mk94HalfBank36W j.succ))
    set s0 := (γ (mk94Cat36W 0) + γ (mk94HalfBank36W 0)).val
    set p0 := (γ (mk94Cat36W 0) * γ (mk94HalfBank36W 0)).val
    set c0 := (γ (mk94Cat36W 0)).val
    set b0 := (γ (mk94HalfBank36W 0)).val
    set q := (cT + bT + p0) / 2 ^ 35
    set r := (cT + bT + p0) % 2 ^ 35
    have hdiv : 2 ^ 35 * q + r = cT + bT + p0 := Nat.div_add_mod (cT + bT + p0) (2 ^ 35)
    have hnat : (s0 + 2 * r) + 2 ^ 36 * q = (c0 + 2 * cT) + (b0 + 2 * bT) := by omega
    have hint : ((s0 + 2 * r : ℕ) : ℤ) =
        (((c0 + 2 * cT : ℕ) : ℤ) + ((b0 + 2 * bT : ℕ) : ℤ)) + (-(q : ℤ)) * (2 ^ 36 : ℤ) := by
      push_cast; zify at hnat; linarith
    change ((s0 + 2 * r : ℕ) : ℤ).emod (2 ^ 36 : ℤ) =
      (((c0 + 2 * cT : ℕ) : ℤ) + ((b0 + 2 * bT : ℕ) : ℤ)).emod (2 ^ 36 : ℤ)
    rw [hint]
    exact Int.add_mul_emod_self_right _ _ _
  have hhalf_eq : bitsVal (fun m : Fin 36 ↦ γ (mk94HalfBank36W m)) =
      bitsVal (fun m : Fin 36 ↦ γ (mk94Bank36W m)) / 2 := by
    rw [fmkBitsVal_castSucc_split]
    have hlo : (fun j : Fin 35 ↦ γ (mk94HalfBank36W j.castSucc)) =
        fun j : Fin 35 ↦ γ (mk94Bank36W j.succ) :=
      funext fun j ↦ by simp [mk94HalfBank36W]
    have hhi : γ (mk94HalfBank36W (Fin.last 35)) = 0 := by
      simp only [mk94HalfBank36W, Fin.snoc_last]
      exact hγ ⟨232, by decide⟩ (by decide)
    rw [hlo, hhi, ZMod.val_zero, mul_zero, add_zero,
      fmkBitsVal_succ_split (fun m : Fin 36 ↦ γ (mk94Bank36W m))]
    have hb0_lt := ZMod.val_lt (γ (mk94Bank36W 0))
    omega
  rw [hhalf_eq] at h36_mod
  have hlo6 : ∀ i : Fin 42,
    i.val < 6 → mk94AddHalfBank36.evalBits γ (mk94Cat42W i) = γ (mk94Cat42W i) :=
    fun i hi ↦ hMut35.2.2.2 γ hγ35 (mk94Cat42W i) (by dsimp [mutCat36, mk94Cat42W]; omega)
  have hcat_hi : ∀ ξ : BitAssignment 268,
      (fun j : Fin 36 ↦ ξ (mk94Cat42W ⟨6 + j.val, by omega⟩)) = fun j : Fin 36 ↦ ξ (mk94Cat36W j) :=
    fun ξ ↦ funext fun j ↦ congrArg ξ (mk94Cat36W_eq_cat42 j).symm
  exact mk36BitsVal_42_of_36_mod hlo6 (by rw [hcat_hi, hcat_hi]; exact h36_mod)

attribute [local irreducible] mk94AddHalfBank36

/-- Bias-cancelled `331`-`TempAnd` (`296 + 35`) `8 × 36 → 36` modular axis multiplier on `Wire 268`
with `[232..268)` clean, updating `cat42` by `64 * (dp_w * K_val) mod 2^42`. -/
def mk94MulAxisFull36 (w : Fin 3) : TempPhaseProg 268 :=
  .seq (mk94MulAxis36_no2a w) mk94AddHalfBank36

theorem mk94MulAxisFull36_spec (w : Fin 3) :
    (mk94MulAxisFull36 w).countTempAnd = 331 ∧
      fmkIsMutBlock 268 36 (fun q ↦ 107 ≤ q.val ∧ q.val < 149) (mk94MulAxisFull36 w) ∧
      (∀ γ : BitAssignment 268, cleanRem 268 36 γ →
        let pNew0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let pOld0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let K_val := bitsVal (fun m : Fin 36 ↦ γ (mk94Bank36W m))
        ((bitsVal (fun m ↦
          (mk94MulAxisFull36 w).evalBits γ (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
            64 * ((twosComp8Int pNew0 - twosComp8Int pOld0) * (K_val : ℤ))).emod (2 ^ 42 : ℤ)) := by
  obtain ⟨hCnt1, hMut1, hEv1⟩ := mk94MulAxis36_no2a_spec w
  obtain ⟨hCnt2, hMut2, hEv2⟩ := mk94AddHalfBank36_spec
  refine ⟨by dsimp [mk94MulAxisFull36, TempPhaseProg.countTempAnd]; omega,
    fmkIsMutBlock_seq (by decide) hMut1 hMut2,
    fun γ hγ ↦ ?_⟩
  dsimp only [mk94MulAxisFull36, TempPhaseProg.evalBits]
  let γ₁ := (mk94MulAxis36_no2a w).evalBits γ
  have hγ₁_cl : cleanRem 268 36 γ₁ := hMut1.2.2.1 γ hγ
  have hbank₁ : (fun m : Fin 36 ↦ γ₁ (mk94Bank36W m)) = fun m : Fin 36 ↦ γ (mk94Bank36W m) :=
    funext fun m ↦ hMut1.2.2.2 γ hγ (mk94Bank36W m) (by dsimp [mk94Bank36W]; omega)
  have he1 := hEv1 γ hγ
  have he2 := hEv2 γ₁ hγ₁_cl
  dsimp only at he1 he2
  rw [hbank₁] at he2
  rw [he2, fmkInt_add_emod, he1, ← fmkInt_add_emod]
  apply congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ))
  ring

attribute [local irreducible] mk94MulAxisFull36

/- ## Section 3: Non-LIFO `andCompute`/`andUncompute` Split Combinator & `U18`/`U54` State Tree -/

theorem mk94RealizesCleanUnitary_seq_asym {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {v : Var} {P₁ P₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    {c₁ c₂ : DynamicCircuit Var n} {U₁ U₂ : Unitary (2 ^ n)} (hP₁ : P₁ᴴ = P₁) (hP₂ : P₂ᴴ = P₂)
    (h₁ : RealizesCleanUnitary v P₁ c₁ U₁) (h₂ : RealizesCleanUnitary v P₂ c₂ U₂)
    (hclean : P₂ * (U₁.1 * P₁) = U₁.1 * P₁) : RealizesCleanUnitary v P₁ (.seq c₁ c₂) (U₂ * U₁)
    := by
  refine ⟨fun Ψ hΨ σ val ↦ ?_, fun Θ hΘ σ ↦ ?_⟩
  · simp only [DynamicCircuit.compile_seq, wp_qSeq]
    exact h₁.1 (wp c₂.compile Ψ) (h₂.1 Ψ hΨ) σ val
  · have hΨ_inv := h₂.1 Θ hΘ
    have hadj : P₁ * U₁.1ᴴ * P₂ = P₁ * U₁.1ᴴ := by
      have h := congrArg conjTranspose hclean
      simpa [conjTranspose_mul, hP₁, hP₂, ← Matrix.mul_assoc] using h
    simp only [DynamicCircuit.compile_seq, wp_qSeq]
    rw [h₁.2 (wp c₂.compile Θ) hΨ_inv σ]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, HermitianMat.conj_conj]
    calc
      ((wp c₂.compile Θ σ).1).conj (P₁ * U₁.1ᴴ)
        = (((wp c₂.compile Θ σ).1).conj P₂).conj (P₁ * U₁.1ᴴ) := by
            rw [HermitianMat.conj_conj, hadj]
      _ = (((wpQAssignCompat U₂ Θ σ).1).conj P₂).conj (P₁ * U₁.1ᴴ) := by
            rw [h₂.2 Θ hΘ σ]
      _ = (Θ σ).1.conj (P₁ * (U₂ * U₁).1ᴴ) := by
            simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
              Matrix.star_eq_conjTranspose, HermitianMat.conj_conj, Submonoid.coe_mul,
              conjTranspose_mul]
            rw [← Matrix.mul_assoc (P₁ * U₁.1ᴴ) P₂ U₂.1ᴴ, hadj, Matrix.mul_assoc]

theorem mk94CleanDiagProj_eq_diagProj {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    (rem : ℕ) (hrem : rem ≤ M) (Inv : BitAssignment M → Prop) : p57CleanDiagProj rComb rem
    hrem Inv = p57DiagProj rComb (fun γ ↦ cleanRem M rem γ ∧ Inv γ) := by
  apply matrix_ext_ket; intro β
  rw [ket_p57CleanDiagProj, ket_p57DiagProj]
  by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx)) <;>
    simp [h]

open Classical in
theorem mk94DiagProj_seq_clean {M n : ℕ} [NeZero (2 ^ n)] {Inv₁ Inv₂ : BitAssignment M → Prop}
    (rComb : QRegister M n) {U : Unitary (2 ^ n)} (f : BitAssignment M → BitAssignment M)
    (hket : ∀ β : BitAssignment n, Inv₁ (fun idx ↦ β (rComb idx)) → U.1.mulVec (ket β) = ket
    (writeRegProg β rComb (f (fun idx ↦ β (rComb idx)))))
    (hpres : ∀ γ : BitAssignment M, Inv₁ γ → Inv₂ (f γ)) : p57DiagProj rComb Inv₂ *
    (U.1 * p57DiagProj rComb Inv₁) = U.1 * p57DiagProj rComb Inv₁ := by
  apply matrix_ext_ket; intro β
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57DiagProj]
  by_cases h : Inv₁ (fun idx ↦ β (rComb idx))
  · simp only [h, ↓reduceIte, hket β h, ket_p57DiagProj]
    have hreg : (fun idx ↦ writeRegProg β rComb (f (fun idx ↦ β (rComb idx))) (rComb idx)) = f
        (fun idx ↦ β (rComb idx)) := funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
    rw [hreg, ite_eq_left (hpres _ h)]
  · simp [h]

/-- Standalone `4-T` `DynamicCircuit.andCompute` realizes `Circuit.TOFF c₁ c₂ anc` on any Hermitian
projector `P` whose support has `anc = 0`. -/
theorem mk94RealizesClean_andCompute {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hP : Pᴴ = P)
    (hZero : (QRegister.singleton anc).basisOutcomeProjector 0 * P = P) : RealizesCleanUnitary
    v P (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a)
    ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval) := by
  let P₀ := (QRegister.singleton anc).basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hPP₀ : P * P₀ = P := by
    have h := congrArg conjTranspose hZero
    simpa [P₀, conjTranspose_mul, hP, hP₀_herm] using h
  refine ⟨fun Ψ hΨ σ val ↦ (RealizesCleanUnitary.circuit v P _).1 Ψ hΨ σ val, fun Θ _ σ ↦ ?_⟩
  have hstep : ((wp (DynamicCircuit.andCompute (Var :=
    Var) c₁ c₂ anc h₁a h₂a).compile Θ σ).1).conj P₀ =
      ((wpQAssignCompat (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval Θ σ).1).conj P₀ := by
    have h := congrArg Subtype.val (congrFun
      (DynCircuitExt.restrictToZeroAncilla_wp_andCompute_compat c₁ c₂ anc h₁₂ h₁a h₂a Θ) σ)
    simpa [P₀, CQAssertion.restrictToZeroAncilla_coe] using h
  have hconj := congrArg (fun H : HermitianMat (Fin (2 ^ n)) ℂ ↦ H.conj P) hstep
  simpa only [HermitianMat.conj_conj, hPP₀] using hconj

theorem mk94RealizesClean_andCompute_diag {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (c₁ c₂ anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (Inv : BitAssignment M → Prop)
    (hInvZero : ∀ γ : BitAssignment M, Inv γ → γ anc = 0) : RealizesCleanUnitary v
    (p57DiagProj rComb Inv) (DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc)
    (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)) ((Circuit.TOFF (rComb c₁)
    (rComb c₂) (rComb anc) (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
    (rComb.wires.injective.ne h₂a)).eval) := by
  refine mk94RealizesClean_andCompute v (rComb c₁) (rComb c₂) (rComb anc)
    (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
    (p57DiagProj rComb Inv) (p57DiagProj_conjTranspose rComb Inv) ?_
  apply matrix_ext_ket; intro β
  rw [mul_mulVec_prog, ket_p57DiagProj]
  by_cases h : Inv (fun idx ↦ β (rComb idx))
  · simp [h, ket_projector_zero, hInvZero _ h]
  · simp [h]

theorem mk94RealizesClean_andUncompute_diag {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (c₁ c₂ anc : Wire M)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (Inv : BitAssignment M → Prop)
    (hInvEq : ∀ γ : BitAssignment M, Inv γ → γ anc = γ c₁ * γ c₂) : RealizesCleanUnitary v
    (p57DiagProj rComb Inv) (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
    (rComb.wires.injective.ne h₁₂)) ((Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc)
    (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne
    h₂a)).eval) := by
  have heq := mk94CleanDiagProj_eq_diagProj rComb 0 (Nat.zero_le M) Inv
  have h := realizesClean_andUncompute_diag v rComb c₁ c₂ anc h₁₂ h₁a h₂a 0 (Nat.zero_le M) Inv
    (fun γ _ hi ↦ hInvEq γ hi)
  rw [heq] at h
  exact RealizesCleanUnitary.mono_proj (p57DiagProj_conjTranspose _ _)
    (p57DiagProj_conjTranspose _ _)
    (by
      apply matrix_ext_ket; intro β
      rw [mul_mulVec_prog, ket_p57DiagProj]
      by_cases hi : Inv (fun idx ↦ β (rComb idx))
      · have h0 : cleanRem M 0 (fun idx ↦ β (rComb idx)) := fun _ hw ↦ absurd hw (by omega)
        simp [hi, h0, ket_p57DiagProj]
      · simp [hi])
    h

/-- Reversible X/CNOT/tempAnd DAG program supporting standalone `4-T/AND` forward expansion
  (`fwdDyn`)
and `0-T` measurement-based uncomputation (`revDyn`) across non-LIFO pass boundaries. -/
inductive Mk94SplitProg (M : ℕ) : Type
  | id : Mk94SplitProg M
  | x (dst : Wire M) : Mk94SplitProg M
  | cnot (src dst : Wire M) (hne : src ≠ dst) : Mk94SplitProg M
  | tempAnd (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) : Mk94SplitProg M
  | seq : Mk94SplitProg M → Mk94SplitProg M → Mk94SplitProg M

def Mk94SplitProg.countAnd {M : ℕ} : Mk94SplitProg M → ℕ
  | .id => 0
  | .x _ => 0
  | .cnot _ _ _ => 0
  | .tempAnd _ _ _ _ _ _ => 1
  | .seq s₁ s₂ => s₁.countAnd + s₂.countAnd

def Mk94SplitProg.fwdBits {M : ℕ} : Mk94SplitProg M → BitAssignment M → BitAssignment M
  | .id, γ => γ
  | .x dst, γ => Function.update γ dst (γ dst + 1)
  | .cnot src dst _, γ => Function.update γ dst (γ dst + γ src)
  | .tempAnd c₁ c₂ anc _ _ _, γ => Function.update γ anc (γ anc + γ c₁ * γ c₂)
  | .seq s₁ s₂, γ => s₂.fwdBits (s₁.fwdBits γ)

def Mk94SplitProg.revBits {M : ℕ} : Mk94SplitProg M → BitAssignment M → BitAssignment M
  | .id, γ => γ
  | .x dst, γ => Function.update γ dst (γ dst + 1)
  | .cnot src dst _, γ => Function.update γ dst (γ dst + γ src)
  | .tempAnd c₁ c₂ anc _ _ _, γ => Function.update γ anc (γ anc + γ c₁ * γ c₂)
  | .seq s₁ s₂, γ => s₁.revBits (s₂.revBits γ)

def Mk94SplitProg.fwdCircuit {M n : ℕ} (rComb : QRegister M n) : Mk94SplitProg M → Circuit n
  | .id => .identity
  | .x dst => Circuit.X (rComb dst)
  | .cnot src dst hne => Circuit.CNOT (rComb src) (rComb dst) (rComb.wires.injective.ne hne)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a =>
      Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂)
        (rComb.wires.injective.ne h₁a)
        (rComb.wires.injective.ne h₂a)
  | .seq s₁ s₂ => .seq (s₁.fwdCircuit rComb) (s₂.fwdCircuit rComb)

def Mk94SplitProg.revCircuit {M n : ℕ} (rComb : QRegister M n) : Mk94SplitProg M → Circuit n
  | .id => .identity
  | .x dst => Circuit.X (rComb dst)
  | .cnot src dst hne => Circuit.CNOT (rComb src) (rComb dst) (rComb.wires.injective.ne hne)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a =>
      Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂)
        (rComb.wires.injective.ne h₁a)
        (rComb.wires.injective.ne h₂a)
  | .seq s₁ s₂ => .seq (s₂.revCircuit rComb) (s₁.revCircuit rComb)

def Mk94SplitProg.fwdDyn {Var : Type} {M n : ℕ} (rComb : QRegister M n) :
    Mk94SplitProg M → DynamicCircuit Var n
  | .id => .identity
  | .x dst => .circuit (Circuit.X (rComb dst))
  | .cnot src dst hne =>
      .circuit (Circuit.CNOT (rComb src) (rComb dst) (rComb.wires.injective.ne hne))
  | .tempAnd c₁ c₂ anc _ h₁a h₂a =>
      DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
  | .seq s₁ s₂ => .seq (s₁.fwdDyn rComb) (s₂.fwdDyn rComb)

def Mk94SplitProg.revDyn {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) :
    Mk94SplitProg M → DynamicCircuit Var n
  | .id => .identity
  | .x dst => .circuit (Circuit.X (rComb dst))
  | .cnot src dst hne =>
      .circuit (Circuit.CNOT (rComb src) (rComb dst) (rComb.wires.injective.ne hne))
  | .tempAnd c₁ c₂ anc h₁₂ _ _ =>
      DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂)
  | .seq s₁ s₂ => .seq (s₂.revDyn v rComb) (s₁.revDyn v rComb)

def Mk94SplitProg.FwdClean {M : ℕ} : Mk94SplitProg M → (BitAssignment M → Prop) → Prop
  | .id, _ => True
  | .x _, _ => True
  | .cnot _ _ _, _ => True
  | .tempAnd _ _ anc _ _ _, Inv => ∀ γ, Inv γ → γ anc = 0
  | .seq s₁ s₂, Inv => s₁.FwdClean Inv ∧ s₂.FwdClean (fun δ ↦ ∃ γ, Inv γ ∧ δ = s₁.fwdBits γ)

theorem Mk94SplitProg.fwdDyn_count_toff {Var : Type} {M n : ℕ} (rComb : QRegister M n) :
    ∀ s : Mk94SplitProg M, (s.fwdDyn (Var := Var) rComb).count PrimitiveGate.TOFF = 0
  | .id => rfl
  | .x _ => by simp [Mk94SplitProg.fwdDyn]
  | .cnot _ _ _ => by simp [Mk94SplitProg.fwdDyn]
  | .tempAnd _ _ _ _ _ _ => by simp [Mk94SplitProg.fwdDyn, DynamicCircuit.count_andCompute_toff]
  | .seq s₁ s₂ => by
      simp [Mk94SplitProg.fwdDyn, Mk94SplitProg.fwdDyn_count_toff rComb s₁,
        Mk94SplitProg.fwdDyn_count_toff rComb s₂]

theorem Mk94SplitProg.fwdDyn_count_t {Var : Type} {M n : ℕ} (rComb : QRegister M n) :
    ∀ s : Mk94SplitProg M, (s.fwdDyn (Var := Var) rComb).count PrimitiveGate.T = 4 * s.countAnd
  | .id => rfl
  | .x _ => by simp [Mk94SplitProg.fwdDyn, Mk94SplitProg.countAnd]
  | .cnot _ _ _ => by simp [Mk94SplitProg.fwdDyn, Mk94SplitProg.countAnd]
  | .tempAnd _ _ _ _ _ _ => by
      simp [Mk94SplitProg.fwdDyn, Mk94SplitProg.countAnd, DynamicCircuit.count_andCompute_t]
  | .seq s₁ s₂ => by
      simp [Mk94SplitProg.fwdDyn, Mk94SplitProg.countAnd,
        Mk94SplitProg.fwdDyn_count_t rComb s₁, Mk94SplitProg.fwdDyn_count_t rComb s₂]
      ring

theorem Mk94SplitProg.revDyn_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) :
    ∀ s : Mk94SplitProg M, (s.revDyn v rComb).count PrimitiveGate.TOFF = 0
  | .id => rfl
  | .x _ => by simp [Mk94SplitProg.revDyn]
  | .cnot _ _ _ => by simp [Mk94SplitProg.revDyn]
  | .tempAnd _ _ _ _ _ _ => by simp [Mk94SplitProg.revDyn, DynamicCircuit.count_andUncompute_toff]
  | .seq s₁ s₂ => by
      simp [Mk94SplitProg.revDyn, Mk94SplitProg.revDyn_count_toff v rComb s₁,
        Mk94SplitProg.revDyn_count_toff v rComb s₂]

theorem Mk94SplitProg.revDyn_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) :
    ∀ s : Mk94SplitProg M, (s.revDyn v rComb).count PrimitiveGate.T = 0
  | .id => rfl
  | .x _ => by simp [Mk94SplitProg.revDyn]
  | .cnot _ _ _ => by simp [Mk94SplitProg.revDyn]
  | .tempAnd _ _ _ _ _ _ => by simp [Mk94SplitProg.revDyn, DynamicCircuit.count_andUncompute_t]
  | .seq s₁ s₂ => by
      simp [Mk94SplitProg.revDyn, Mk94SplitProg.revDyn_count_t v rComb s₁,
        Mk94SplitProg.revDyn_count_t v rComb s₂]

theorem Mk94SplitProg.fwdDyn_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (rComb : QRegister M n) :
    ∀ s : Mk94SplitProg M, PreservesStoreConst (s.fwdDyn (Var := Var) rComb)
  | .id => PreservesStoreConst.identity
  | .x _ => PreservesStoreConst.circuit _
  | .cnot _ _ _ => PreservesStoreConst.circuit _
  | .tempAnd _ _ _ _ _ _ => PreservesStoreConst.circuit _
  | .seq s₁ s₂ =>
      PreservesStoreConst.seq (s₁.fwdDyn_preservesStore rComb) (s₂.fwdDyn_preservesStore rComb)

theorem Mk94SplitProg.revDyn_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (v : Var) (rComb : QRegister M n) :
    ∀ s : Mk94SplitProg M, PreservesStoreConst (s.revDyn v rComb)
  | .id => PreservesStoreConst.identity
  | .x _ => PreservesStoreConst.circuit _
  | .cnot _ _ _ => PreservesStoreConst.circuit _
  | .tempAnd _ _ _ _ _ _ => PreservesStoreConst.andUncompute v _ _ _ _
  | .seq s₁ s₂ =>
      PreservesStoreConst.seq (s₂.revDyn_preservesStore v rComb) (s₁.revDyn_preservesStore v rComb)

theorem Mk94SplitProg.revBits_fwdBits {M : ℕ} :
    ∀ (s : Mk94SplitProg M) (γ : BitAssignment M), s.revBits (s.fwdBits γ) = γ
  | .id, _ => rfl
  | .x dst, γ => by
      funext w
      by_cases hw : w = dst
      · subst hw
        simp [Mk94SplitProg.fwdBits, Mk94SplitProg.revBits, add_assoc, CharTwo.add_self_eq_zero]
      · simp [Mk94SplitProg.fwdBits, Mk94SplitProg.revBits, Function.update_of_ne hw]
  | .cnot src dst hne, γ => by
      funext w
      by_cases hw : w = dst
      · subst hw
        simp [Mk94SplitProg.fwdBits, Mk94SplitProg.revBits,
          Function.update_of_ne hne, add_assoc, CharTwo.add_self_eq_zero]
      · simp [Mk94SplitProg.fwdBits, Mk94SplitProg.revBits, Function.update_of_ne hw]
  | .tempAnd c₁ c₂ anc _ h₁a h₂a, γ => by
      funext w
      by_cases hw : w = anc
      · subst hw
        simp [Mk94SplitProg.fwdBits, Mk94SplitProg.revBits,
          Function.update_of_ne h₁a, Function.update_of_ne h₂a, add_assoc, CharTwo.add_self_eq_zero]
      · simp [Mk94SplitProg.fwdBits, Mk94SplitProg.revBits, Function.update_of_ne hw]
  | .seq s₁ s₂, γ => by
      simp [Mk94SplitProg.fwdBits, Mk94SplitProg.revBits,
        Mk94SplitProg.revBits_fwdBits s₂, Mk94SplitProg.revBits_fwdBits s₁]

theorem Mk94SplitProg.fwdCircuit_ket {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n) :
    ∀ (s : Mk94SplitProg M) (β : BitAssignment n),
      (s.fwdCircuit rComb).eval.1.mulVec (ket β) =
        ket (writeRegProg β rComb (s.fwdBits (fun idx ↦ β (rComb idx))))
  | .id, β => by
      simp only [Mk94SplitProg.fwdCircuit, Mk94SplitProg.fwdBits,
        Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
      congr 1; funext w
      by_cases hm : w ∈ Set.range rComb.wires
      · obtain ⟨i, rfl⟩ := hm; simp [writeRegProg_apply_reg]
      · exact (writeRegProg_apply_of_not_mem _ _ _ _ hm).symm
  | .x dst, β => by
      have hc := eval_onRegister_prog_ket rComb (.cliff (.x dst)) β
      simpa [TempPhaseProg.onRegister, CliffProg.onRegister, TempPhaseProg.toToffCircuit,
        CliffProg.toCircuit, TempPhaseProg.evalSign, TempPhaseProg.evalBits, CliffProg.eval,
        Mk94SplitProg.fwdCircuit, Mk94SplitProg.fwdBits] using hc
  | .cnot src dst hne, β => by
      have hc := eval_onRegister_prog_ket rComb (.cliff (.cnot src dst hne)) β
      simpa [TempPhaseProg.onRegister, CliffProg.onRegister, TempPhaseProg.toToffCircuit,
        CliffProg.toCircuit, TempPhaseProg.evalSign, TempPhaseProg.evalBits, CliffProg.eval,
        Mk94SplitProg.fwdCircuit, Mk94SplitProg.fwdBits] using hc
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a, β => by
      simp only [Mk94SplitProg.fwdCircuit, Mk94SplitProg.fwdBits, ket_TOFF]
      congr 1; funext w
      by_cases hm : w ∈ Set.range rComb.wires
      · obtain ⟨i, rfl⟩ := hm
        rw [writeRegProg_apply_reg]
        by_cases hi : i = anc
        · subst hi; simp
        · simp [Function.update_of_ne (rComb.wires.injective.ne hi), Function.update_of_ne hi]
      · have hne : w ≠ rComb anc := fun h ↦ hm ⟨anc, h.symm⟩
        rw [Function.update_of_ne hne, writeRegProg_apply_of_not_mem _ _ _ _ hm]
  | .seq s₁ s₂, β => by
      simp only [Mk94SplitProg.fwdCircuit, Mk94SplitProg.fwdBits, Circuit.eval_seq,
        Submonoid.coe_mul, mul_mulVec_prog,
        Mk94SplitProg.fwdCircuit_ket rComb s₁, Mk94SplitProg.fwdCircuit_ket rComb s₂]
      have hreg : (fun idx ↦ writeRegProg β rComb (s₁.fwdBits (fun i ↦ β (rComb i))) (rComb idx)) =
          s₁.fwdBits (fun i ↦ β (rComb i)) :=
        funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
      rw [hreg, fmkWriteRegProg_idem]

theorem Mk94SplitProg.revCircuit_ket {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n) :
    ∀ (s : Mk94SplitProg M) (β : BitAssignment n),
      (s.revCircuit rComb).eval.1.mulVec (ket β) =
        ket (writeRegProg β rComb (s.revBits (fun idx ↦ β (rComb idx))))
  | .id, β => (Mk94SplitProg.id).fwdCircuit_ket rComb β
  | .x dst, β => (Mk94SplitProg.x dst).fwdCircuit_ket rComb β
  | .cnot src dst hne, β => (Mk94SplitProg.cnot src dst hne).fwdCircuit_ket rComb β
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a, β =>
      (Mk94SplitProg.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a).fwdCircuit_ket rComb β
  | .seq s₁ s₂, β => by
      simp only [Mk94SplitProg.revCircuit, Mk94SplitProg.revBits, Circuit.eval_seq,
        Submonoid.coe_mul, mul_mulVec_prog,
        Mk94SplitProg.revCircuit_ket rComb s₂, Mk94SplitProg.revCircuit_ket rComb s₁]
      have hreg : (fun idx ↦ writeRegProg β rComb (s₂.revBits (fun i ↦ β (rComb i))) (rComb idx)) =
          s₂.revBits (fun i ↦ β (rComb i)) :=
        funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
      rw [hreg, fmkWriteRegProg_idem]

theorem Mk94SplitProg.fwdDyn_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) :
    ∀ (s : Mk94SplitProg M) (Inv : BitAssignment M → Prop),
      s.FwdClean Inv →
      RealizesCleanUnitary v (p57DiagProj rComb Inv)
        (s.fwdDyn rComb) ((s.fwdCircuit rComb).eval)
  | .id, Inv, _ => RealizesCleanUnitary.identity v (p57DiagProj rComb Inv)
  | .x _, Inv, _ => RealizesCleanUnitary.circuit v (p57DiagProj rComb Inv) _
  | .cnot _ _ _, Inv, _ => RealizesCleanUnitary.circuit v (p57DiagProj rComb Inv) _
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a, Inv, hZero =>
      mk94RealizesClean_andCompute_diag v rComb c₁ c₂ anc h₁₂ h₁a h₂a Inv hZero
  | .seq s₁ s₂, Inv, ⟨h₁, h₂⟩ => by
      let InvMid : BitAssignment M → Prop := fun δ ↦ ∃ γ, Inv γ ∧ δ = s₁.fwdBits γ
      have hseq := mk94RealizesCleanUnitary_seq_asym (p57DiagProj_conjTranspose rComb Inv)
          (p57DiagProj_conjTranspose rComb InvMid) (s₁.fwdDyn_realizes v rComb Inv h₁)
          (s₂.fwdDyn_realizes v rComb InvMid h₂) (mk94DiagProj_seq_clean rComb s₁.fwdBits (fun
          β _ ↦ s₁.fwdCircuit_ket rComb β) (fun γ hγ ↦ ⟨γ, hγ, rfl⟩))
      simpa only [Mk94SplitProg.fwdDyn, Mk94SplitProg.fwdCircuit, Circuit.eval_seq] using hseq

theorem Mk94SplitProg.revDyn_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) :
    ∀ (s : Mk94SplitProg M) (Inv₀ Inv₁ : BitAssignment M → Prop),
      s.FwdClean Inv₀ →
      (∀ δ, Inv₁ δ → ∃ γ, Inv₀ γ ∧ δ = s.fwdBits γ) →
      RealizesCleanUnitary v (p57DiagProj rComb Inv₁)
        (s.revDyn v rComb) ((s.revCircuit rComb).eval)
  | .id, _, Inv₁, _, _ => RealizesCleanUnitary.identity v (p57DiagProj rComb Inv₁)
  | .x _, _, Inv₁, _, _ => RealizesCleanUnitary.circuit v (p57DiagProj rComb Inv₁) _
  | .cnot _ _ _, _, Inv₁, _, _ => RealizesCleanUnitary.circuit v (p57DiagProj rComb Inv₁) _
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a, Inv₀, Inv₁, hZero, hIm =>
      mk94RealizesClean_andUncompute_diag v rComb c₁ c₂ anc h₁₂ h₁a h₂a Inv₁ fun δ hδ ↦ by
        obtain ⟨γ, hγ, rfl⟩ := hIm δ hδ
        simp [Mk94SplitProg.fwdBits, hZero γ hγ,
          Function.update_of_ne h₁a, Function.update_of_ne h₂a]
  | .seq s₁ s₂, Inv₀, Inv₁, ⟨h₁, h₂⟩, hIm => by
      let InvMid : BitAssignment M → Prop := fun ξ ↦ ∃ γ, Inv₀ γ ∧ ξ = s₁.fwdBits γ
      have hIm₂ : ∀ δ, Inv₁ δ → ∃ ξ, InvMid ξ ∧ δ = s₂.fwdBits ξ := fun δ hδ ↦ by
        obtain ⟨γ, hγ, rfl⟩ := hIm δ hδ
        exact ⟨s₁.fwdBits γ, ⟨γ, hγ, rfl⟩, rfl⟩
      have hseq := mk94RealizesCleanUnitary_seq_asym
        (p57DiagProj_conjTranspose rComb Inv₁)
        (p57DiagProj_conjTranspose rComb InvMid)
        (s₂.revDyn_realizes v rComb InvMid Inv₁ h₂ hIm₂)
        (s₁.revDyn_realizes v rComb Inv₀ InvMid h₁ (fun _ h ↦ h))
        (mk94DiagProj_seq_clean rComb s₂.revBits (fun β _ ↦ s₂.revCircuit_ket rComb β)
          (fun δ hδ ↦ by
            obtain ⟨ξ, hξ, rfl⟩ := hIm₂ δ hδ
            rwa [s₂.revBits_fwdBits]))
      simpa only [Mk94SplitProg.revDyn, Mk94SplitProg.revCircuit, Circuit.eval_seq] using hseq

theorem Mk94SplitProg.fwdClean_mono {M : ℕ} :
    ∀ (s : Mk94SplitProg M) {Inv₁ Inv₂ : BitAssignment M → Prop},
      (∀ γ, Inv₂ γ → Inv₁ γ) → s.FwdClean Inv₁ → s.FwdClean Inv₂
  | .id, _, _, _, _ => trivial
  | .x _, _, _, _, _ => trivial
  | .cnot _ _ _, _, _, _, _ => trivial
  | .tempAnd _ _ _ _ _ _, _, _, hsub, h₁ => fun γ hγ ↦ h₁ γ (hsub γ hγ)
  | .seq s₁ s₂, _, _, hsub, ⟨h₁, h₂⟩ =>
      ⟨s₁.fwdClean_mono hsub h₁,
        s₂.fwdClean_mono (fun _ ⟨γ, hγ, hδ⟩ ↦ ⟨γ, hsub γ hγ, hδ⟩) h₂⟩

def mk94BParW : Wire 268 := ⟨90, by decide⟩
def mk94U16W (i : Fin 16) : Wire 268 := ⟨91 + i.val, by omega⟩
def mk94B0W : Wire 268 := ⟨91, by decide⟩
def mk94B1W : Wire 268 := ⟨92, by decide⟩
def mk94A0W : Wire 268 := ⟨93, by decide⟩
def mk94C0W : Wire 268 := ⟨94, by decide⟩
def mk94A1W : Wire 268 := ⟨95, by decide⟩
def mk94C1W : Wire 268 := ⟨96, by decide⟩
def mk94A2W : Wire 268 := ⟨97, by decide⟩
def mk94C2W : Wire 268 := ⟨98, by decide⟩
def mk94AccW : Wire 268 := ⟨149, by decide⟩
def mk94W11W : Wire 268 := ⟨192, by decide⟩
def mk94U18W (p18 : Fin 18) : Wire 268 := ⟨174 + p18.val, by omega⟩

def mk94POrig (p18 : Fin 18) (t2 : Fin 3) : Fin 54 :=
  ⟨p18.val % 9 + 9 * t2.val + 27 * (p18.val / 9), by omega⟩

def mk94InvPOrig (p : Fin 54) : Fin 18 × Fin 3 :=
  (⟨p.val % 9 + 9 * (p.val / 27), by omega⟩, ⟨(p.val / 9) % 3, by omega⟩)

theorem mk94InvPOrig_pOrig (pt : Fin 18 × Fin 3) :
    mk94InvPOrig (mk94POrig pt.1 pt.2) = pt := by
  revert pt; decide

theorem mk94POrig_invPOrig (p : Fin 54) :
    mk94POrig (mk94InvPOrig p).1 (mk94InvPOrig p).2 = p := by
  revert p; decide

def mk94U54Wire (p18 : Fin 18) (t2 : Fin 3) : Wire 268 :=
  if _ : t2.val = 0 then ⟨174 + p18.val, by omega⟩
  else if _ : p18.val = 0 then if t2.val = 1 then ⟨193, by decide⟩ else ⟨194, by decide⟩
  else if _ : p18.val = 1 then if t2.val = 1 then ⟨195, by decide⟩ else ⟨232, by decide⟩
  else ⟨233 + 2 * (p18.val - 2) + (t2.val - 1), by omega⟩

def mk94ActP18 (γ : BitAssignment 268) : ℕ :=
  s3Trit (γ mk94A0W) (γ mk94C0W) + 3 * s3Trit (γ mk94A1W) (γ mk94C1W) + 9 * (γ mk94BParW).val

theorem mk94ActP18_lt (γ : BitAssignment 268) : mk94ActP18 γ < 18 := by
  have := s3Trit_lt_three (γ mk94A0W) (γ mk94C0W)
  have := s3Trit_lt_three (γ mk94A1W) (γ mk94C1W)
  have := ZMod.val_lt (γ mk94BParW)
  dsimp [mk94ActP18]; omega

theorem mk94POrig_act_eq (γ : BitAssignment 268) : (mk94POrig ⟨mk94ActP18 γ, mk94ActP18_lt γ⟩
    ⟨s3Trit (γ mk94A2W) (γ mk94C2W), s3Trit_lt_three _ _⟩).val = s3NucleusQ27
    (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val := by
  have h0 := s3Trit_lt_three (γ mk94A0W) (γ mk94C0W)
  have h1 := s3Trit_lt_three (γ mk94A1W) (γ mk94C1W)
  have hb := ZMod.val_lt (γ mk94BParW)
  have hu2 : mk94U16W 2 = mk94A0W := rfl
  have hu3 : mk94U16W 3 = mk94C0W := rfl
  have hu4 : mk94U16W 4 = mk94A1W := rfl
  have hu5 : mk94U16W 5 = mk94C1W := rfl
  have hu6 : mk94U16W 6 = mk94A2W := rfl
  have hu7 : mk94U16W 7 = mk94C2W := rfl
  dsimp only [mk94POrig, mk94ActP18, s3NucleusQ27]
  rw [hu2, hu3, hu4, hu5, hu6, hu7]
  omega

def mk94SplitBit (w0 w1 actB : Wire 268) (hb : actB.val < 174) (hw0 : 174 ≤ w0.val)
    (hw1 : 174 ≤ w1.val) (h01 : w0 ≠ w1) : Mk94SplitProg 268 := .seq (.tempAnd w0 actB w1
    (wire_ne_of_gt (by omega)) h01 (wire_ne_of_lt (by omega))) (.cnot w1 w0 h01.symm)

theorem mk94SplitBit_spec (w0 w1 actB : Wire 268)
    (hb : actB.val < 174) (hw0 : 174 ≤ w0.val) (hw1 : 174 ≤ w1.val) (h01 : w0 ≠ w1) :
    (mk94SplitBit w0 w1 actB hb hw0 hw1 h01).countAnd = 1 ∧
    (∀ Inv : BitAssignment 268 → Prop, (∀ γ, Inv γ → γ w1 = 0) →
      (mk94SplitBit w0 w1 actB hb hw0 hw1 h01).FwdClean Inv) ∧
    (∀ γ : BitAssignment 268, γ w1 = 0 →
      let γ' := (mk94SplitBit w0 w1 actB hb hw0 hw1 h01).fwdBits γ
      γ' w0 = γ w0 * (1 + γ actB) ∧
      γ' w1 = γ w0 * γ actB ∧
      ∀ q : Wire 268, q ≠ w0 → q ≠ w1 → γ' q = γ q) := by
  refine ⟨rfl, fun Inv hZero ↦ ⟨hZero, trivial⟩, fun γ hz1 ↦ ?_⟩
  dsimp only [mk94SplitBit, Mk94SplitProg.fwdBits]
  refine ⟨?_, ?_, fun q hq0 hq1 ↦ ?_⟩
  · simp only [Function.update_self, Function.update_of_ne h01, hz1, zero_add]
    ring
  · simp [Function.update_of_ne h01.symm, Function.update_self, hz1]
  · simp [Function.update_of_ne hq0, Function.update_of_ne hq1]

def mk94SplitTrit (w0 w1 w2 actA actC : Wire 268) (ha : actA.val < 174) (hc : actC.val < 174)
    (hw0 : 174 ≤ w0.val) (hw1 : 174 ≤ w1.val) (hw2 : 174 ≤ w2.val) (h01 : w0 ≠ w1)
    (h02 : w0 ≠ w2) (_h12 : w1 ≠ w2) : Mk94SplitProg 268 := .seq
    (mk94SplitBit w0 w1 actC hc hw0 hw1 h01) (mk94SplitBit w0 w2 actA ha hw0 hw2 h02)

open Classical in
theorem mk94SplitTrit_spec (w0 w1 w2 actA actC : Wire 268)
    (ha : actA.val < 174) (hc : actC.val < 174)
    (hw0 : 174 ≤ w0.val) (hw1 : 174 ≤ w1.val) (hw2 : 174 ≤ w2.val)
    (h01 : w0 ≠ w1) (h02 : w0 ≠ w2) (h12 : w1 ≠ w2) :
    (mk94SplitTrit w0 w1 w2 actA actC ha hc hw0 hw1 hw2 h01 h02 h12).countAnd = 2 ∧
    (∀ Inv : BitAssignment 268 → Prop, (∀ γ, Inv γ → γ w1 = 0 ∧ γ w2 = 0) →
      (mk94SplitTrit w0 w1 w2 actA actC ha hc hw0 hw1 hw2 h01 h02 h12).FwdClean Inv) ∧
    (∀ γ : BitAssignment 268, γ w1 = 0 → γ w2 = 0 →
      let γ' := (mk94SplitTrit w0 w1 w2 actA actC ha hc hw0 hw1 hw2 h01 h02 h12).fwdBits γ
      γ' w0 = (if s3Trit (γ actA) (γ actC) = 0 then γ w0 else 0) ∧
      γ' w1 = (if s3Trit (γ actA) (γ actC) = 1 then γ w0 else 0) ∧
      γ' w2 = (if s3Trit (γ actA) (γ actC) = 2 then γ w0 else 0) ∧
      ∀ q : Wire 268, q ≠ w0 → q ≠ w1 → q ≠ w2 → γ' q = γ q) := by
  obtain ⟨hc1, hf1, he1⟩ := mk94SplitBit_spec w0 w1 actC hc hw0 hw1 h01
  obtain ⟨hc2, hf2, he2⟩ := mk94SplitBit_spec w0 w2 actA ha hw0 hw2 h02
  refine ⟨by dsimp [mk94SplitTrit, Mk94SplitProg.countAnd]; omega,
    fun Inv hZ ↦ ⟨hf1 Inv (fun γ hγ ↦ (hZ γ hγ).1), hf2 _ fun δ ⟨γ, hγ, hδ⟩ ↦ by
      subst hδ
      rw [(he1 γ (hZ γ hγ).1).2.2 w2 h02.symm h12.symm]
      exact (hZ γ hγ).2⟩,
    fun γ hz1 hz2 ↦ ?_⟩
  dsimp only [mk94SplitTrit, Mk94SplitProg.fwdBits]
  obtain ⟨h1_0, h1_1, h1_out⟩ := he1 γ hz1
  have h1_w2 : (mk94SplitBit w0 w1 actC hc hw0 hw1 h01).fwdBits γ w2 = 0 := by
    rw [h1_out w2 h02.symm h12.symm]; exact hz2
  have h1_a : (mk94SplitBit w0 w1 actC hc hw0 hw1 h01).fwdBits γ actA = γ actA :=
    h1_out actA (wire_ne_of_lt (by omega)) (wire_ne_of_lt (by omega))
  obtain ⟨h2_0, h2_2, h2_out⟩ := he2 _ h1_w2
  have h2_1 : (mk94SplitBit w0 w2 actA ha hw0 hw2 h02).fwdBits
      ((mk94SplitBit w0 w1 actC hc hw0 hw1 h01).fwdBits γ) w1 =
      (mk94SplitBit w0 w1 actC hc hw0 hw1 h01).fwdBits γ w1 := h2_out w1 h01.symm h12
  rw [h2_0, h1_0, h1_a, h2_1, h1_1, h2_2, h1_0, h1_a]
  refine ⟨?_, ?_, ?_, fun q hq0 hq1 hq2 ↦ (h2_out q hq0 hq2).trans (h1_out q hq0 hq1)⟩
  · rcases fmkBit_cases (γ actA) with h | h <;> rcases fmkBit_cases (γ actC) with h' | h' <;>
      simp [h, h', s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
  · rcases fmkBit_cases (γ actA) with h | h <;> rcases fmkBit_cases (γ actC) with h' | h' <;>
      simp [h, h', s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
  · rcases fmkBit_cases (γ actA) with h | h <;> rcases fmkBit_cases (γ actC) with h' | h' <;>
      simp [h, h', s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]

def mk94SeqSplit {M : ℕ} : (N : ℕ) → (Fin N → Mk94SplitProg M) → Mk94SplitProg M
  | 0, _ => .id
  | k + 1, f => .seq (mk94SeqSplit k (fun i ↦ f i.castSucc)) (f (Fin.last k))

/-- Disjoint batch of `N` binary splits `mk94SplitBit (w0 i) (w1 i) actB`. -/
theorem mk94SeqSplitBit_spec (N : ℕ) (w0 w1 : Fin N → Wire 268) (actB : Wire 268)
    (hb : actB.val < 174)
    (hw0 : ∀ i, 174 ≤ (w0 i).val) (hw1 : ∀ i, 174 ≤ (w1 i).val)
    (h01 : ∀ i j, w0 i ≠ w1 j)
    (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1) :
    let prog := mk94SeqSplit N (fun i ↦
      mk94SplitBit (w0 i) (w1 i) actB hb (hw0 i) (hw1 i) (h01 i i))
    prog.countAnd = N ∧
    (∀ Inv : BitAssignment 268 → Prop, (∀ γ, Inv γ → ∀ i, γ (w1 i) = 0) → prog.FwdClean Inv) ∧
    (∀ γ : BitAssignment 268, (∀ i, γ (w1 i) = 0) →
      let γ' := prog.fwdBits γ
      (∀ i, γ' (w0 i) = γ (w0 i) * (1 + γ actB)) ∧
      (∀ i, γ' (w1 i) = γ (w0 i) * γ actB) ∧
      (∀ q : Wire 268, (∀ i, q ≠ w0 i) → (∀ i, q ≠ w1 i) → γ' q = γ q)) := by
  induction N with
  | zero =>
      refine ⟨rfl, fun _ _ ↦ trivial, fun γ _ ↦ ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun _ _ _ ↦ rfl⟩⟩
  | succ k ih =>
      obtain ⟨hCntPre, hCleanPre, hBitsPre⟩ := ih (fun i ↦ w0 i.castSucc) (fun i ↦ w1 i.castSucc)
        (fun i ↦ hw0 i.castSucc) (fun i ↦ hw1 i.castSucc)
        (fun i j ↦ h01 i.castSucc j.castSucc)
        (fun i j h ↦ Fin.castSucc_injective k (hinj0 h))
        (fun i j h ↦ Fin.castSucc_injective k (hinj1 h))
      obtain ⟨hCntLast, hCleanLast, hBitsLast⟩ := mk94SplitBit_spec (w0 (Fin.last k))
          (w1 (Fin.last k)) actB hb (hw0 (Fin.last k)) (hw1 (Fin.last k)) (h01 _ _)
      refine ⟨by dsimp [mk94SeqSplit, Mk94SplitProg.countAnd]; omega,
        fun Inv hZ ↦ ⟨hCleanPre Inv (fun γ hγ i ↦ hZ γ hγ i.castSucc),
          hCleanLast _ fun δ ⟨γ, hγ, hδ⟩ ↦ by
            subst hδ
            rw [(hBitsPre γ (fun i ↦ hZ γ hγ i.castSucc)).2.2 (w1 (Fin.last k))
              (fun i h ↦ h01 i.castSucc (Fin.last k) h.symm)
              (fun i h ↦ Fin.castSucc_ne_last i (hinj1 h.symm))]
            exact hZ γ hγ (Fin.last k)⟩,
        fun γ hZ ↦ ?_⟩
      dsimp only [mk94SeqSplit, Mk94SplitProg.fwdBits]
      obtain ⟨hP0, hP1, hPOut⟩ := hBitsPre γ (fun i ↦ hZ i.castSucc)
      have hδ_w1 := (hPOut (w1 (Fin.last k)) (fun i h ↦ h01 i.castSucc (Fin.last k) h.symm)
          (fun i h ↦ Fin.castSucc_ne_last i (hinj1 h.symm))).trans (hZ (Fin.last k))
      have hδ_w0 := hPOut (w0 (Fin.last k)) (fun i h ↦ Fin.castSucc_ne_last i (hinj0 h.symm))
          (fun i h ↦ h01 (Fin.last k) i.castSucc h)
      have hδ_b := hPOut actB
        (fun i ↦ wire_ne_of_lt (by have := hw0 i.castSucc; omega))
        (fun i ↦ wire_ne_of_lt (by have := hw1 i.castSucc; omega))
      obtain ⟨hL0, hL1, hLOut⟩ := hBitsLast _ hδ_w1
      refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun q hq0 hq1 ↦ ?_⟩
      · cases i using Fin.lastCases with
        | last => rw [hL0, hδ_w0, hδ_b]
        | cast j =>
            exact (hLOut (w0 j.castSucc) (fun h ↦ Fin.castSucc_ne_last j (hinj0 h))
              (h01 j.castSucc (Fin.last k))).trans (hP0 j)
      · cases i using Fin.lastCases with
        | last => rw [hL1, hδ_w0, hδ_b]
        | cast j =>
            exact (hLOut (w1 j.castSucc) (fun h ↦ h01 (Fin.last k) j.castSucc h.symm)
              (fun h ↦ Fin.castSucc_ne_last j (hinj1 h))).trans (hP1 j)
      · exact (hLOut q (hq0 (Fin.last k)) (hq1 (Fin.last k))).trans
          (hPOut q (fun j ↦ hq0 j.castSucc) (fun j ↦ hq1 j.castSucc))

open Classical in
/-- Disjoint batch of `N` ternary splits `mk94SplitTrit (w0 i) (w1 i) (w2 i) actA actC`. -/
theorem mk94SeqSplitTrit_spec (N : ℕ) (w0 w1 w2 : Fin N → Wire 268) (actA actC : Wire 268)
    (ha : actA.val < 174) (hc : actC.val < 174)
    (hw0 : ∀ i, 174 ≤ (w0 i).val) (hw1 : ∀ i, 174 ≤ (w1 i).val) (hw2 : ∀ i, 174 ≤ (w2 i).val)
    (h01 : ∀ i j, w0 i ≠ w1 j) (h02 : ∀ i j, w0 i ≠ w2 j) (h12 : ∀ i j, w1 i ≠ w2 j)
    (hinj0 : Function.Injective w0) (hinj1 : Function.Injective w1) (hinj2 : Function.Injective w2)
      :
    let prog := mk94SeqSplit N (fun i ↦ mk94SplitTrit (w0 i) (w1 i) (w2 i) actA actC
      ha hc (hw0 i) (hw1 i) (hw2 i) (h01 i i) (h02 i i) (h12 i i))
    prog.countAnd = 2 * N ∧
    (∀ Inv : BitAssignment 268 → Prop,
      (∀ γ, Inv γ → (∀ i, γ (w1 i) = 0) ∧ (∀ i, γ (w2 i) = 0)) → prog.FwdClean Inv) ∧
    (∀ γ : BitAssignment 268, (∀ i, γ (w1 i) = 0) → (∀ i, γ (w2 i) = 0) →
      let γ' := prog.fwdBits γ
      (∀ i, γ' (w0 i) = (if s3Trit (γ actA) (γ actC) = 0 then γ (w0 i) else 0)) ∧
      (∀ i, γ' (w1 i) = (if s3Trit (γ actA) (γ actC) = 1 then γ (w0 i) else 0)) ∧
      (∀ i, γ' (w2 i) = (if s3Trit (γ actA) (γ actC) = 2 then γ (w0 i) else 0)) ∧
      (∀ q : Wire 268, (∀ i, q ≠ w0 i) → (∀ i, q ≠ w1 i) → (∀ i, q ≠ w2 i) → γ' q = γ q)) := by
  induction N with
  | zero =>
      refine ⟨rfl, fun _ _ ↦ trivial,
        fun γ _ _ ↦ ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun _ _ _ _ ↦ rfl⟩⟩
  | succ k ih =>
      obtain ⟨hCntPre, hCleanPre, hBitsPre⟩ := ih
        (fun i ↦ w0 i.castSucc) (fun i ↦ w1 i.castSucc) (fun i ↦ w2 i.castSucc)
        (fun i ↦ hw0 i.castSucc) (fun i ↦ hw1 i.castSucc) (fun i ↦ hw2 i.castSucc)
        (fun i j ↦ h01 i.castSucc j.castSucc) (fun i j ↦ h02 i.castSucc j.castSucc)
        (fun i j ↦ h12 i.castSucc j.castSucc)
        (fun i j h ↦ Fin.castSucc_injective k (hinj0 h))
        (fun i j h ↦ Fin.castSucc_injective k (hinj1 h))
        (fun i j h ↦ Fin.castSucc_injective k (hinj2 h))
      obtain ⟨hCntLast, hCleanLast, hBitsLast⟩ := mk94SplitTrit_spec (w0 (Fin.last k))
          (w1 (Fin.last k)) (w2 (Fin.last k)) actA actC ha hc (hw0 (Fin.last k))
          (hw1 (Fin.last k)) (hw2 (Fin.last k)) (h01 _ _) (h02 _ _) (h12 _ _)
      refine ⟨by dsimp [mk94SeqSplit, Mk94SplitProg.countAnd]; omega,
        fun Inv hZ ↦ ⟨hCleanPre Inv (fun γ hγ ↦ ⟨fun i ↦ (hZ γ hγ).1 i.castSucc,
            fun i ↦ (hZ γ hγ).2 i.castSucc⟩),
          hCleanLast _ fun δ ⟨γ, hγ, hδ⟩ ↦ by
            subst hδ
            obtain ⟨_, _, _, hOut⟩ := hBitsPre γ (fun i ↦ (hZ γ hγ).1 i.castSucc)
              (fun i ↦ (hZ γ hγ).2 i.castSucc)
            refine ⟨?_, ?_⟩
            · rw [hOut (w1 (Fin.last k))
                (fun i h ↦ h01 i.castSucc (Fin.last k) h.symm)
                (fun i h ↦ Fin.castSucc_ne_last i (hinj1 h.symm))
                (fun i h ↦ h12 (Fin.last k) i.castSucc h)]
              exact (hZ γ hγ).1 (Fin.last k)
            · rw [hOut (w2 (Fin.last k))
                (fun i h ↦ h02 i.castSucc (Fin.last k) h.symm)
                (fun i h ↦ h12 i.castSucc (Fin.last k) h.symm)
                (fun i h ↦ Fin.castSucc_ne_last i (hinj2 h.symm))]
              exact (hZ γ hγ).2 (Fin.last k)⟩,
        fun γ hZ1 hZ2 ↦ ?_⟩
      dsimp only [mk94SeqSplit, Mk94SplitProg.fwdBits]
      obtain ⟨hP0, hP1, hP2, hPOut⟩ := hBitsPre γ (fun i ↦ hZ1 i.castSucc) (fun i ↦ hZ2 i.castSucc)
      have hδ_w1 := (hPOut (w1 (Fin.last k)) (fun i h ↦ h01 i.castSucc (Fin.last k) h.symm)
          (fun i h ↦ Fin.castSucc_ne_last i (hinj1 h.symm)) (fun i h ↦ h12 (Fin.last k)
          i.castSucc h)).trans (hZ1 (Fin.last k))
      have hδ_w2 := (hPOut (w2 (Fin.last k)) (fun i h ↦ h02 i.castSucc (Fin.last k) h.symm)
          (fun i h ↦ h12 i.castSucc (Fin.last k) h.symm) (fun i h ↦ Fin.castSucc_ne_last i
          (hinj2 h.symm))).trans (hZ2 (Fin.last k))
      have hδ_w0 := hPOut (w0 (Fin.last k)) (fun i h ↦ Fin.castSucc_ne_last i (hinj0 h.symm))
          (fun i h ↦ h01 (Fin.last k) i.castSucc h) (fun i h ↦ h02 (Fin.last k) i.castSucc h)
      have hδ_a := hPOut actA (fun i ↦ wire_ne_of_lt (by have := hw0 i.castSucc; omega))
        (fun i ↦ wire_ne_of_lt (by have := hw1 i.castSucc; omega))
        (fun i ↦ wire_ne_of_lt (by have := hw2 i.castSucc; omega))
      have hδ_c := hPOut actC (fun i ↦ wire_ne_of_lt (by have := hw0 i.castSucc; omega))
        (fun i ↦ wire_ne_of_lt (by have := hw1 i.castSucc; omega))
        (fun i ↦ wire_ne_of_lt (by have := hw2 i.castSucc; omega))
      obtain ⟨hL0, hL1, hL2, hLOut⟩ := hBitsLast _ hδ_w1 hδ_w2
      refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun q hq0 hq1 hq2 ↦ ?_⟩
      · cases i using Fin.lastCases with
        | last => rw [hL0, hδ_w0, hδ_a, hδ_c]
        | cast j =>
            exact (hLOut (w0 j.castSucc) (fun h ↦ Fin.castSucc_ne_last j (hinj0 h))
              (h01 j.castSucc (Fin.last k)) (h02 j.castSucc (Fin.last k))).trans (hP0 j)
      · cases i using Fin.lastCases with
        | last => rw [hL1, hδ_w0, hδ_a, hδ_c]
        | cast j =>
            exact (hLOut (w1 j.castSucc) (fun h ↦ h01 (Fin.last k) j.castSucc h.symm) (fun h ↦
              Fin.castSucc_ne_last j (hinj1 h)) (h12 j.castSucc (Fin.last k))).trans (hP1 j)
      · cases i using Fin.lastCases with
        | last => rw [hL2, hδ_w0, hδ_a, hδ_c]
        | cast j =>
            exact (hLOut (w2 j.castSucc) (fun h ↦ h02 (Fin.last k) j.castSucc h.symm)
              (fun h ↦ h12 (Fin.last k) j.castSucc h.symm)
              (fun h ↦ Fin.castSucc_ne_last j (hinj2 h))).trans (hP2 j)
      · exact (hLOut q (hq0 (Fin.last k)) (hq1 (Fin.last k)) (hq2 (Fin.last k))).trans
          (hPOut q (fun j ↦ hq0 j.castSucc) (fun j ↦ hq1 j.castSucc) (fun j ↦ hq2 j.castSucc))

def mk94SplitU18_s0 : Mk94SplitProg 268 := .cnot mk94AccW (mk94U18W 0) (by decide)

def mk94SplitU18_s1 : Mk94SplitProg 268 := mk94SplitTrit (mk94U18W 0) (mk94U18W 1)
    (mk94U18W 2) mk94A0W mk94C0W (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

def mk94SplitU18_s2 : Mk94SplitProg 268 :=
  mk94SeqSplit 3 fun i ↦
    mk94SplitTrit ⟨174 + i.val, by omega⟩ ⟨177 + i.val, by omega⟩ ⟨180 + i.val, by omega⟩
      mk94A1W mk94C1W (by decide) (by decide)
      (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
      (wire_ne_of_lt (by dsimp; omega)) (wire_ne_of_lt (by dsimp; omega))
      (wire_ne_of_lt (by dsimp; omega))

def mk94SplitU18_s3 : Mk94SplitProg 268 :=
  mk94SeqSplit 9 fun i ↦
    mk94SplitBit ⟨174 + i.val, by omega⟩ ⟨183 + i.val, by omega⟩ mk94BParW
      (by decide) (by dsimp; omega) (by dsimp; omega) (wire_ne_of_lt (by dsimp; omega))

def mk94SplitU18_s4 : Mk94SplitProg 268 :=
  .tempAnd mk94B0W mk94B1W mk94W11W (by decide) (by decide) (by decide)

/-- Initial `18`-AND (`72 T`) expansion building `U18` on `[174..192)` and `w11 = b0 * b1` on
  `192`. -/
def mk94SplitU18W11 : Mk94SplitProg 268 :=
  .seq mk94SplitU18_s0 (.seq mk94SplitU18_s1 (.seq mk94SplitU18_s2 (.seq mk94SplitU18_s3
    mk94SplitU18_s4)))

def mk94InvU18 (γ : BitAssignment 268) : Prop :=
  (∀ p18 : Fin 18, γ (mk94U18W p18) = γ mk94AccW * (if p18.val = mk94ActP18 γ then 1 else 0)) ∧
  γ mk94W11W = γ mk94B0W * γ mk94B1W ∧
  γ ⟨193, by decide⟩ = 0 ∧ γ ⟨194, by decide⟩ = 0 ∧ γ ⟨195, by decide⟩ = 0 ∧
  cleanRem 268 36 γ

def mk94InvCleanU18 (γ : BitAssignment 268) : Prop :=
  mk94InvU18 γ ∧ ∀ r : Fin 36, γ (mk94Bank36W r) = 0

theorem mk94ActP18_congr {γ₁ γ₂ : BitAssignment 268}
    (h : ∀ q : Wire 268, q.val < 174 → γ₁ q = γ₂ q) : mk94ActP18 γ₁ = mk94ActP18 γ₂ := by
  dsimp only [mk94ActP18]
  rw [h mk94A0W (by decide), h mk94C0W (by decide), h mk94A1W (by decide),
    h mk94C1W (by decide), h mk94BParW (by decide)]

open Classical in
theorem mk94SplitU18W11_spec :
    mk94SplitU18W11.FwdClean (cleanRem 268 94) ∧
    (∀ γ : BitAssignment 268, cleanRem 268 94 γ →
      let γ' := mk94SplitU18W11.fwdBits γ
      mk94InvCleanU18 γ' ∧ ∀ q : Wire 268, q.val < 174 → γ' q = γ q) := by
  obtain ⟨_, hC2, hB2⟩ := mk94SeqSplitTrit_spec 3
    (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨177 + i.val, by omega⟩)
    (fun i ↦ ⟨180 + i.val, by omega⟩) mk94A1W mk94C1W (by decide) (by decide)
    (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega)
    (fun i j ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
  obtain ⟨_, hC3, hB3⟩ := mk94SeqSplitBit_spec 9
    (fun i ↦ ⟨174 + i.val, by omega⟩) (fun i ↦ ⟨183 + i.val, by omega⟩) mk94BParW (by decide)
    (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega)
    (fun i j ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
  obtain ⟨_, hC1, hB1⟩ := mk94SplitTrit_spec (mk94U18W 0) (mk94U18W 1) (mk94U18W 2)
    mk94A0W mk94C0W (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hStep : ∀ γ : BitAssignment 268, cleanRem 268 94 γ →
      let γ1 := mk94SplitU18_s0.fwdBits γ
      let γ2 := mk94SplitU18_s1.fwdBits γ1
      let γ3 := mk94SplitU18_s2.fwdBits γ2
      let γ4 := mk94SplitU18_s3.fwdBits γ3
      let γ5 := mk94SplitU18_s4.fwdBits γ4
      (γ1 (mk94U18W 1) = 0 ∧ γ1 (mk94U18W 2) = 0) ∧
      ((∀ i : Fin 3, γ2 ⟨177 + i.val, by omega⟩ = 0) ∧ (∀ i : Fin 3, γ2 ⟨180 + i.val,
        by omega⟩ = 0)) ∧
      (∀ i : Fin 9, γ3 ⟨183 + i.val, by omega⟩ = 0) ∧
      γ4 mk94W11W = 0 ∧
      mk94InvCleanU18 γ5 ∧ (∀ q : Wire 268, q.val < 174 → γ5 q = γ q) := by
    intro γ hγ γ1 γ2 γ3 γ4 γ5
    have h1_0 : γ1 (mk94U18W 0) = γ mk94AccW := by
      simp [γ1, mk94SplitU18_s0, Mk94SplitProg.fwdBits, hγ (mk94U18W 0) (by decide)]
    have h1_out : ∀ q : Wire 268, q ≠ mk94U18W 0 → γ1 q = γ q := fun q hq ↦ by
      simp [γ1, mk94SplitU18_s0, Mk94SplitProg.fwdBits, Function.update_of_ne hq]
    have h1_ge : ∀ q : Wire 268, 175 ≤ q.val → γ1 q = 0 := fun q hq ↦
      (h1_out q (wire_ne_of_gt (by dsimp [mk94U18W]; omega))).trans (hγ q (by omega))
    obtain ⟨h2_0, h2_1, h2_2, h2_out⟩ := hB1 γ1 (h1_ge _ (by decide)) (h1_ge _ (by decide))
    have h2_lt : ∀ q : Wire 268, q.val < 174 → γ2 q = γ q := fun q hq ↦
      (h2_out q (wire_ne_of_lt (by dsimp [mk94U18W]; omega))
        (wire_ne_of_lt (by dsimp [mk94U18W]; omega))
        (wire_ne_of_lt (by dsimp [mk94U18W]; omega))).trans
      (h1_out q (wire_ne_of_lt (by dsimp [mk94U18W]; omega)))
    have h2_ge : ∀ q : Wire 268, 177 ≤ q.val → γ2 q = 0 := fun q hq ↦
      (h2_out q (wire_ne_of_gt (by dsimp [mk94U18W]; omega))
        (wire_ne_of_gt (by dsimp [mk94U18W]; omega))
        (wire_ne_of_gt (by dsimp [mk94U18W]; omega))).trans (h1_ge q (by omega))
    have h2_t0 : ∀ i : Fin 3, γ2 ⟨174 + i.val, by omega⟩ =
        if i.val = s3Trit (γ mk94A0W) (γ mk94C0W) then γ mk94AccW else 0 := by
      intro i
      have ha0 : γ1 mk94A0W = γ mk94A0W := h1_out _ (by decide)
      have hc0 : γ1 mk94C0W = γ mk94C0W := h1_out _ (by decide)
      rcases i with ⟨v, hi⟩
      interval_cases v
      · change (mk94SplitTrit _ _ _ _ _ _ _ _ _ _ _ _ _).fwdBits γ1 (mk94U18W 0) = _
        rw [h2_0, h1_0, ha0, hc0]; simp [eq_comm]
      · change (mk94SplitTrit _ _ _ _ _ _ _ _ _ _ _ _ _).fwdBits γ1 (mk94U18W 1) = _
        rw [h2_1, h1_0, ha0, hc0]; simp [eq_comm]
      · change (mk94SplitTrit _ _ _ _ _ _ _ _ _ _ _ _ _).fwdBits γ1 (mk94U18W 2) = _
        rw [h2_2, h1_0, ha0, hc0]; simp [eq_comm]
    obtain ⟨h3_0, h3_1, h3_2, h3_out⟩ := hB2 γ2 (fun i ↦ h2_ge _ (by dsimp; omega))
      (fun i ↦ h2_ge _ (by dsimp; omega))
    have h3_lt : ∀ q : Wire 268, q.val < 174 → γ3 q = γ q := fun q hq ↦
      (h3_out q (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
        (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
        (fun _ ↦ wire_ne_of_lt (by dsimp; omega))).trans (h2_lt q hq)
    have h3_ge : ∀ q : Wire 268, 183 ≤ q.val → γ3 q = 0 := fun q hq ↦
      (h3_out q (fun _ ↦ wire_ne_of_gt (by dsimp; omega))
        (fun _ ↦ wire_ne_of_gt (by dsimp; omega))
        (fun _ ↦ wire_ne_of_gt (by dsimp; omega))).trans (h2_ge q (by omega))
    have h3_q9 : ∀ k : Fin 9, γ3 ⟨174 + k.val, by omega⟩ =
        if k.val = s3Trit (γ mk94A0W) (γ mk94C0W) + 3 * s3Trit (γ mk94A1W) (γ mk94C1W)
        then γ mk94AccW else 0 := by
      intro k
      dsimp only [γ3, mk94SplitU18_s2]
      have ha1 : γ2 mk94A1W = γ mk94A1W := h2_lt _ (by decide)
      have hc1 : γ2 mk94C1W = γ mk94C1W := h2_lt _ (by decide)
      have ht0_lt := s3Trit_lt_three (γ mk94A0W) (γ mk94C0W)
      have ht1_lt := s3Trit_lt_three (γ mk94A1W) (γ mk94C1W)
      by_cases hk3 : k.val < 3
      · have heq := h3_0 ⟨k.val, hk3⟩
        dsimp only at heq
        rw [heq, ha1, hc1, h2_t0 ⟨k.val, hk3⟩]
        dsimp only
        split_ifs <;> first | rfl | omega
      · by_cases hk6 : k.val < 6
        · have hw : (⟨174 + k.val, by omega⟩ : Wire 268) = ⟨177 + (k.val - 3), by omega⟩ :=
            Fin.ext (by dsimp; omega)
          have heq := h3_1 ⟨k.val - 3, by omega⟩
          dsimp only at heq
          rw [hw, heq, ha1, hc1, h2_t0 ⟨k.val - 3, by omega⟩]
          dsimp only
          split_ifs <;> first | rfl | omega
        · have hw : (⟨174 + k.val, by omega⟩ : Wire 268) = ⟨180 + (k.val - 6), by omega⟩ :=
            Fin.ext (by dsimp; omega)
          have heq := h3_2 ⟨k.val - 6, by omega⟩
          dsimp only at heq
          rw [hw, heq, ha1, hc1, h2_t0 ⟨k.val - 6, by omega⟩]
          dsimp only
          split_ifs <;> first | rfl | omega
    obtain ⟨h4_0, h4_1, h4_out⟩ := hB3 γ3 (fun i ↦ h3_ge _ (by dsimp; omega))
    have h4_lt : ∀ q : Wire 268, q.val < 174 → γ4 q = γ q := fun q hq ↦
      (h4_out q (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
        (fun _ ↦ wire_ne_of_lt (by dsimp; omega))).trans (h3_lt q hq)
    have h4_ge : ∀ q : Wire 268, 192 ≤ q.val → γ4 q = 0 := fun q hq ↦
      (h4_out q (fun _ ↦ wire_ne_of_gt (by dsimp; omega))
        (fun _ ↦ wire_ne_of_gt (by dsimp; omega))).trans (h3_ge q (by omega))
    have h5_lt : ∀ q : Wire 268, q.val < 174 → γ5 q = γ q := fun q hq ↦ by
      have hne : q ≠ mk94W11W := wire_ne_of_lt (by dsimp [mk94W11W]; omega)
      simpa [γ5, mk94SplitU18_s4, Mk94SplitProg.fwdBits, Function.update_of_ne hne] using h4_lt q hq
    have h5_ge : ∀ q : Wire 268, 193 ≤ q.val → γ5 q = 0 := fun q hq ↦ by
      have hne : q ≠ mk94W11W := wire_ne_of_gt (by dsimp [mk94W11W]; omega)
      simpa [γ5, mk94SplitU18_s4, Mk94SplitProg.fwdBits, Function.update_of_ne hne] using
        h4_ge q (by omega)
    refine ⟨⟨h1_ge _ (by decide), h1_ge _ (by decide)⟩,
      ⟨fun i ↦ h2_ge _ (by dsimp; omega), fun i ↦ h2_ge _ (by dsimp; omega)⟩,
      fun i ↦ h3_ge _ (by dsimp; omega),
      h4_ge _ (by decide),
      ⟨⟨fun p18 ↦ ?_, ?_, h5_ge _ (by decide), h5_ge _ (by decide), h5_ge _ (by decide),
        fun w hw ↦ h5_ge w (by omega)⟩, fun r ↦ h5_ge _ (by dsimp [mk94Bank36W]; omega)⟩,
      h5_lt⟩
    · have hne : mk94U18W p18 ≠ mk94W11W := wire_ne_of_lt (by dsimp [mk94U18W, mk94W11W]; omega)
      have h5u : γ5 (mk94U18W p18) = γ4 (mk94U18W p18) := by
        simp [γ5, mk94SplitU18_s4, Mk94SplitProg.fwdBits, Function.update_of_ne hne]
      rw [h5u, h5_lt mk94AccW (by decide), mk94ActP18_congr h5_lt]
      dsimp only [γ4, mk94SplitU18_s3]
      have hb3 : γ3 mk94BParW = γ mk94BParW := h3_lt _ (by decide)
      have ht0_lt := s3Trit_lt_three (γ mk94A0W) (γ mk94C0W)
      have ht1_lt := s3Trit_lt_three (γ mk94A1W) (γ mk94C1W)
      by_cases hp9 : p18.val < 9
      · have heq := h4_0 ⟨p18.val, hp9⟩
        dsimp only at heq
        change (mk94SeqSplit 9 _).fwdBits γ3 ⟨174 + p18.val, _⟩ = _
        rw [heq, hb3, h3_q9 ⟨p18.val, hp9⟩]
        dsimp only
        have h10 : (1 + (0 : ZMod 2)) = 1 := rfl
        have h11 : (1 + (1 : ZMod 2)) = 0 := rfl
        rcases fmkBit_cases (γ mk94BParW) with hb | hb
        · simp only [mk94ActP18, hb, ZMod.val_zero, Nat.mul_zero, Nat.add_zero, h10, mul_one]
          split_ifs <;> ring
        · simp only [mk94ActP18, hb, ZMod.val_one, Nat.mul_one, h11, mul_zero]
          symm
          rw [ite_eq_right (by omega), mul_zero]
      · have hw : mk94U18W p18 = ⟨183 + (p18.val - 9), by
          omega⟩ := Fin.ext (by dsimp [mk94U18W]; omega)
        have heq := h4_1 ⟨p18.val - 9, by omega⟩
        dsimp only at heq
        rw [hw, heq, hb3, h3_q9 ⟨p18.val - 9, by omega⟩]
        dsimp only
        rcases fmkBit_cases (γ mk94BParW) with hb | hb
        · simp only [mk94ActP18, hb, ZMod.val_zero, Nat.add_zero, mul_zero]
          symm
          rw [ite_eq_right (by omega), mul_zero]
        · simp only [mk94ActP18, hb, ZMod.val_one, mul_one]
          split_ifs <;> first | ring1 | omega
    · rw [h5_lt mk94B0W (by decide), h5_lt mk94B1W (by decide)]
      simp [γ5, mk94SplitU18_s4, Mk94SplitProg.fwdBits, h4_ge mk94W11W (by decide),
        h4_lt mk94B0W (by decide), h4_lt mk94B1W (by decide)]
  refine ⟨⟨trivial, hC1 _ (fun _ ⟨γ, hγ, h⟩ ↦ by subst h; exact (hStep γ hγ).1),
    hC2 _ (fun _ ⟨_, ⟨γ, hγ, h1⟩, h2⟩ ↦ by subst h1; subst h2; exact (hStep γ hγ).2.1),
    hC3 _ (fun _ ⟨_, ⟨_, ⟨γ, hγ, h1⟩, h2⟩, h3⟩ ↦ by
      subst h1; subst h2; subst h3; exact (hStep γ hγ).2.2.1),
    fun _ ⟨_, ⟨_, ⟨_, ⟨γ, hγ, h1⟩, h2⟩, h3⟩, h4⟩ ↦ by
      subst h1; subst h2; subst h3; subst h4; exact (hStep γ hγ).2.2.2.1⟩,
    fun γ hγ ↦ (hStep γ hγ).2.2.2.2⟩

def mk94Zero94 (δ : BitAssignment 268) : BitAssignment 268 :=
  fun w ↦ if w.val < 174 then δ w else 0

open Classical in
theorem mk94SplitU18W11_rev_spec (δ : BitAssignment 268) (hδ : mk94InvCleanU18 δ) : cleanRem
    268 94 (mk94Zero94 δ) ∧ δ = mk94SplitU18W11.fwdBits (mk94Zero94 δ) ∧
    mk94SplitU18W11.revBits δ = mk94Zero94 δ := by
  have hcl : cleanRem 268 94 (mk94Zero94 δ) := fun w hw ↦ by
    dsimp [mk94Zero94]; rw [ite_eq_right (by omega)]
  have hlt_z : ∀ q : Wire 268, q.val < 174 → mk94Zero94 δ q = δ q := fun q hq ↦ by
    dsimp [mk94Zero94]; rw [ite_eq_left hq]
  obtain ⟨⟨⟨hU18', hW11', h93', h94', h95', hCl36'⟩, hBank'⟩, hLt'⟩ :=
    mk94SplitU18W11_spec.2 (mk94Zero94 δ) hcl
  have heq_lt : ∀ q : Wire 268, q.val < 174 → mk94SplitU18W11.fwdBits (mk94Zero94 δ) q = δ q :=
    fun q hq ↦ (hLt' q hq).trans (hlt_z q hq)
  have heq : δ = mk94SplitU18W11.fwdBits (mk94Zero94 δ) := by
    funext w
    by_cases h1 : w.val < 174
    · exact (heq_lt w h1).symm
    · by_cases h2 : w.val < 192
      · have hw : w = mk94U18W ⟨w.val - 174, by omega⟩ := Fin.ext (by dsimp [mk94U18W]; omega)
        rw [hw, hδ.1.1, hU18', heq_lt mk94AccW (by decide), mk94ActP18_congr heq_lt]
      · by_cases h3 : w.val = 192
        · have hw : w = mk94W11W := Fin.ext h3
          rw [hw, hδ.1.2.1, hW11', heq_lt mk94B0W (by decide), heq_lt mk94B1W (by decide)]
        · by_cases h4 : w.val < 196
          · have hv193 : 193 ≤ w.val := by omega
            rcases w with ⟨v, hv⟩
            dsimp only at hv193 h4
            interval_cases v
            · exact hδ.1.2.2.1.trans h93'.symm
            · exact hδ.1.2.2.2.1.trans h94'.symm
            · exact hδ.1.2.2.2.2.1.trans h95'.symm
          · by_cases h5 : w.val < 232
            · have hw : w = mk94Bank36W ⟨w.val - 196, by
                omega⟩ := Fin.ext (by dsimp [mk94Bank36W]; omega)
              rw [hw, hδ.2, hBank']
            · exact (hδ.1.2.2.2.2.2 w (by omega)).trans (hCl36' w (by omega)).symm
  refine ⟨hcl, heq, ?_⟩
  conv_lhs => rw [heq]
  exact mk94SplitU18W11.revBits_fwdBits (mk94Zero94 δ)

def mk94SplitTop3 : Mk94SplitProg 268 :=
  .seq
    (mk94SplitTrit ⟨174, by decide⟩ ⟨193, by decide⟩ ⟨194, by decide⟩ mk94A2W mk94C2W
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (mk94SplitBit ⟨175, by decide⟩ ⟨195, by decide⟩ mk94C2W
      (by decide) (by decide) (by decide) (by decide))

def mk94SplitTop33 : Mk94SplitProg 268 :=
  .seq
    (mk94SplitBit ⟨175, by decide⟩ ⟨232, by decide⟩ mk94A2W
      (by decide) (by decide) (by decide) (by decide))
    (mk94SeqSplit 16 fun j ↦
      mk94SplitTrit ⟨176 + j.val, by omega⟩ ⟨233 + 2 * j.val, by omega⟩ ⟨234 + 2 * j.val, by omega⟩
        mk94A2W mk94C2W (by decide) (by decide)
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
        (wire_ne_of_lt (by dsimp; omega)) (wire_ne_of_lt (by dsimp; omega))
        (wire_ne_of_lt (by dsimp; omega)))

def mk94SplitAll36 : Mk94SplitProg 268 := .seq mk94SplitTop3 mk94SplitTop33

def mk94InvMidTop3 (γ : BitAssignment 268) : Prop :=
  (∀ t2 : Fin 3, γ (mk94U54Wire 0 t2) =
    γ mk94AccW * (if 0 = mk94ActP18 γ ∧ t2.val = s3Trit (γ mk94A2W) (γ mk94C2W) then 1 else 0)) ∧
  γ ⟨175, by decide⟩ = (γ mk94AccW * if 1 = mk94ActP18 γ then 1 else 0) * (1 + γ mk94C2W) ∧
  γ ⟨195, by decide⟩ = (γ mk94AccW * if 1 = mk94ActP18 γ then 1 else 0) * γ mk94C2W ∧
  (∀ j : Fin 16, γ ⟨176 + j.val, by omega⟩ =
    γ mk94AccW * (if 2 + j.val = mk94ActP18 γ then 1 else 0)) ∧
  γ mk94W11W = γ mk94B0W * γ mk94B1W ∧
  cleanRem 268 36 γ

def mk94InvU54 (γ : BitAssignment 268) : Prop := (∀ p18 : Fin 18, ∀ t2 : Fin 3, γ (mk94U54Wire
    p18 t2) = γ mk94AccW * (if p18.val = mk94ActP18 γ ∧ t2.val = s3Trit (γ mk94A2W) (γ
    mk94C2W) then 1 else 0)) ∧ γ mk94W11W = γ mk94B0W * γ mk94B1W ∧ cleanRem 268 3 γ

open Classical in
theorem mk94SplitTop3_spec :
    mk94SplitTop3.FwdClean mk94InvU18 ∧
    (∀ γ : BitAssignment 268, mk94InvU18 γ →
      let γ' := mk94SplitTop3.fwdBits γ
      mk94InvMidTop3 γ' ∧
      ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ' q = γ q) := by
  obtain ⟨_, hC1, hB1⟩ := mk94SplitTrit_spec ⟨174, by decide⟩ ⟨193, by decide⟩ ⟨194, by decide⟩
    mk94A2W mk94C2W (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain ⟨_, hC2, hB2⟩ := mk94SplitBit_spec ⟨175, by decide⟩ ⟨195, by decide⟩ mk94C2W
    (by decide) (by decide) (by decide) (by decide)
  have hStep : ∀ γ : BitAssignment 268, mk94InvU18 γ →
      let γ1 := (mk94SplitTrit ⟨174, by decide⟩ ⟨193, by decide⟩ ⟨194, by decide⟩ mk94A2W mk94C2W
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).fwdBits γ
      let γ2 := mk94SplitTop3.fwdBits γ
      γ1 ⟨195, by decide⟩ = 0 ∧ mk94InvMidTop3 γ2 ∧
      (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ2 q = γ q) := by
    intro γ ⟨hU18, hW11, h93, h94, h95, hCl36⟩ γ1 γ2
    obtain ⟨e1_0, e1_1, e1_2, e1_out⟩ := hB1 γ h93 h94
    have h1_95 : γ1 ⟨195, by decide⟩ = 0 :=
      (e1_out _ (by decide) (by decide) (by decide)).trans h95
    obtain ⟨e2_0, e2_1, e2_out⟩ := hB2 γ1 h1_95
    have hout : ∀ q : Wire 268,
        q ≠ ⟨174, by decide⟩ → q ≠ ⟨175, by decide⟩ → q ≠ ⟨193, by decide⟩ →
        q ≠ ⟨194, by decide⟩ → q ≠ ⟨195, by decide⟩ → γ2 q = γ q := fun q h0 h1 h2 h3 h4 ↦
      (e2_out q h1 h4).trans (e1_out q h0 h2 h3)
    have hlt : ∀ q : Wire 268, q.val < 174 → γ2 q = γ q := fun q hq ↦
      hout q (wire_ne_of_lt (by dsimp; omega)) (wire_ne_of_lt (by dsimp; omega))
        (wire_ne_of_lt (by dsimp; omega)) (wire_ne_of_lt (by dsimp; omega))
        (wire_ne_of_lt (by dsimp; omega))
    have hc1 : γ1 mk94C2W = γ mk94C2W := e1_out _ (by decide) (by decide) (by decide)
    have h75_1 : γ1 ⟨175, by decide⟩ = γ (mk94U18W 1) := e1_out _ (by
      decide) (by decide) (by decide)
    have hγ1 : γ1 = (mk94SplitTrit ⟨174, by decide⟩ ⟨193, by decide⟩ ⟨194,
      by decide⟩ mk94A2W mk94C2W
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).fwdBits γ := rfl
    have hγ2 : γ2 = (mk94SplitBit ⟨175, by decide⟩ ⟨195, by decide⟩ mk94C2W
        (by decide) (by decide) (by decide) (by decide)).fwdBits γ1 := rfl
    refine ⟨h1_95, ⟨fun t2 ↦ ?_, ?_, ?_, fun j ↦ ?_, ?_, fun w hw ↦ ?_⟩, fun q hq ↦ ?_⟩
    · rw [hlt mk94AccW (by
        decide), mk94ActP18_congr hlt, hlt mk94A2W (by decide), hlt mk94C2W (by decide)]
      have h0 : γ ⟨174, by decide⟩ = γ mk94AccW * (if 0 = mk94ActP18 γ then 1 else 0) := hU18 0
      rcases t2 with ⟨_ | _ | _ | v, hv⟩
      · change γ2 ⟨174, by decide⟩ = _
        rw [hγ2, e2_out ⟨174, by decide⟩ (by decide) (by decide), hγ1, e1_0, h0]
        simp only; split_ifs <;> first | ring1 | omega
      · change γ2 ⟨193, by decide⟩ = _
        rw [hγ2, e2_out ⟨193, by decide⟩ (by decide) (by decide), hγ1, e1_1, h0]
        simp only; split_ifs <;> first | ring1 | omega
      · change γ2 ⟨194, by decide⟩ = _
        rw [hγ2, e2_out ⟨194, by decide⟩ (by decide) (by decide), hγ1, e1_2, h0]
        simp only; split_ifs <;> first | ring1 | omega
      · omega
    · rw [hlt mk94AccW (by decide), mk94ActP18_congr hlt, hlt mk94C2W (by decide),
        hγ2, e2_0, h75_1, hc1, hU18 1]
      rfl
    · rw [hlt mk94AccW (by decide), mk94ActP18_congr hlt, hlt mk94C2W (by decide),
        hγ2, e2_1, h75_1, hc1, hU18 1]
      rfl
    · rw [hout _ (wire_ne_of_gt (by dsimp; omega)) (wire_ne_of_gt (by dsimp; omega))
        (wire_ne_of_lt (by dsimp; omega)) (wire_ne_of_lt (by dsimp; omega))
        (wire_ne_of_lt (by dsimp; omega)),
        hlt mk94AccW (by decide), mk94ActP18_congr hlt]
      have hw_eq : (⟨176 + j.val, by omega⟩ : Wire 268) = mk94U18W ⟨2 + j.val, by omega⟩ :=
        Fin.ext (by dsimp [mk94U18W]; omega)
      rw [hw_eq]; exact hU18 ⟨2 + j.val, by omega⟩
    · rw [hout mk94W11W (by decide) (by decide) (by decide) (by decide) (by decide),
        hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
      exact hW11
    · exact (hout w (wire_ne_of_gt (by dsimp; omega)) (wire_ne_of_gt (by dsimp; omega))
        (wire_ne_of_gt (by dsimp; omega)) (wire_ne_of_gt (by dsimp; omega))
        (wire_ne_of_gt (by dsimp; omega))).trans (hCl36 w hw)
    · rcases hq with hq1 | ⟨hq2, hq3⟩
      · exact hlt q hq1
      · exact hout q (wire_ne_of_gt (by dsimp; omega)) (wire_ne_of_gt (by dsimp; omega))
          (wire_ne_of_gt (by dsimp; omega)) (wire_ne_of_gt (by dsimp; omega))
          (wire_ne_of_gt (by dsimp; omega))
  exact ⟨⟨hC1 _ (fun γ hγ ↦ ⟨hγ.2.2.1, hγ.2.2.2.1⟩),
    hC2 _ (fun _ ⟨γ, hγ, h⟩ ↦ by subst h; exact (hStep γ hγ).1)⟩,
    fun γ hγ ↦ (hStep γ hγ).2⟩

open Classical in
theorem mk94SplitTop33_spec :
    mk94SplitTop33.FwdClean mk94InvMidTop3 ∧
    (∀ γ : BitAssignment 268, mk94InvMidTop3 γ →
      let γ' := mk94SplitTop33.fwdBits γ
      mk94InvU54 γ' ∧
      ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ' q = γ q) := by
  obtain ⟨_, hCB1, hBB1⟩ := mk94SplitBit_spec ⟨175, by decide⟩ ⟨232, by decide⟩ mk94A2W
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_, hCT16, hBT16⟩ := mk94SeqSplitTrit_spec 16
    (fun j ↦ ⟨176 + j.val, by omega⟩) (fun j ↦ ⟨233 + 2 * j.val, by omega⟩)
    (fun j ↦ ⟨234 + 2 * j.val, by omega⟩) mk94A2W mk94C2W (by decide) (by decide)
    (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega) (fun _ ↦ by dsimp; omega)
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun _ _ ↦ wire_ne_of_lt (by dsimp; omega))
    (fun i j ↦ Fin.ne_of_val_ne (by dsimp; omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
    (fun i j h ↦ by have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega))
  have hStep : ∀ γ : BitAssignment 268, mk94InvMidTop3 γ →
      let γ1 := (mk94SplitBit ⟨175, by decide⟩ ⟨232, by decide⟩ mk94A2W
        (by decide) (by decide) (by decide) (by decide)).fwdBits γ
      let γ2 := mk94SplitTop33.fwdBits γ
      ((∀ j : Fin 16, γ1 ⟨233 + 2 * j.val, by omega⟩ = 0) ∧
        (∀ j : Fin 16, γ1 ⟨234 + 2 * j.val, by omega⟩ = 0)) ∧
      mk94InvU54 γ2 ∧
      (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ2 q = γ q) := by
    intro γ ⟨hP0, h75, h95, hJ16, hW11, hCl36⟩ γ1 γ2
    obtain ⟨e1_0, e1_1, e1_out⟩ := hBB1 γ (hCl36 _ (by decide))
    have hZ1 : ∀ j : Fin 16, γ1 ⟨233 + 2 * j.val, by omega⟩ = 0 := fun j ↦
      (e1_out _ (wire_ne_of_gt (by dsimp; omega)) (wire_ne_of_gt (by dsimp; omega))).trans
        (hCl36 _ (by dsimp; omega))
    have hZ2 : ∀ j : Fin 16, γ1 ⟨234 + 2 * j.val, by omega⟩ = 0 := fun j ↦
      (e1_out _ (wire_ne_of_gt (by dsimp; omega)) (wire_ne_of_gt (by dsimp; omega))).trans
        (hCl36 _ (by dsimp; omega))
    obtain ⟨hT0, hT1, hT2, hTOut⟩ := hBT16 γ1 hZ1 hZ2
    have hout : ∀ q : Wire 268,
        (q.val < 175 ∨ (192 ≤ q.val ∧ q.val < 232) ∨ 265 ≤ q.val) → γ2 q = γ q := by
      intro q hq
      have h1 : ∀ j : Fin 16, q ≠ ⟨176 + j.val, by omega⟩ := fun j ↦
        Fin.ne_of_val_ne (by dsimp; rcases hq with h | ⟨h1, h2⟩ | h <;> omega)
      have h2 : ∀ j : Fin 16, q ≠ ⟨233 + 2 * j.val, by omega⟩ := fun j ↦
        Fin.ne_of_val_ne (by dsimp; rcases hq with h | ⟨h1, h2⟩ | h <;> omega)
      have h3 : ∀ j : Fin 16, q ≠ ⟨234 + 2 * j.val, by omega⟩ := fun j ↦
        Fin.ne_of_val_ne (by dsimp; rcases hq with h | ⟨h1, h2⟩ | h <;> omega)
      have h4 : q ≠ ⟨175, by decide⟩ :=
        Fin.ne_of_val_ne (by dsimp; rcases hq with h | ⟨h1, h2⟩ | h <;> omega)
      have h5 : q ≠ ⟨232, by decide⟩ :=
        Fin.ne_of_val_ne (by dsimp; rcases hq with h | ⟨h1, h2⟩ | h <;> omega)
      exact (hTOut q h1 h2 h3).trans (e1_out q h4 h5)
    have hlt : ∀ q : Wire 268, q.val < 174 → γ2 q = γ q := fun q hq ↦ hout q (Or.inl (by omega))
    have ha1 : γ1 mk94A2W = γ mk94A2W := e1_out _ (by decide) (by decide)
    have hc1 : γ1 mk94C2W = γ mk94C2W := e1_out _ (by decide) (by decide)
    have hγ1 : γ1 = (mk94SplitBit ⟨175, by decide⟩ ⟨232, by decide⟩ mk94A2W
        (by decide) (by decide) (by decide) (by decide)).fwdBits γ := rfl
    have hγ2 : γ2 = (mk94SeqSplit 16 fun j ↦
        mk94SplitTrit ⟨176 + j.val, by omega⟩ ⟨233 + 2 * j.val, by omega⟩ ⟨234 + 2 * j.val,
          by omega⟩
          mk94A2W mk94C2W (by decide) (by decide)
          (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
          (wire_ne_of_lt (by dsimp; omega)) (wire_ne_of_lt (by dsimp; omega))
          (wire_ne_of_lt (by dsimp; omega))).fwdBits γ1 := rfl
    refine ⟨⟨hZ1, hZ2⟩, ⟨fun p18 t2 ↦ ?_, ?_, fun w hw ↦ ?_⟩, fun q hq ↦ ?_⟩
    · rw [hlt mk94AccW (by
        decide), mk94ActP18_congr hlt, hlt mk94A2W (by decide), hlt mk94C2W (by decide)]
      by_cases hp0 : p18.val = 0
      · have hp_eq : p18 = 0 := Fin.ext hp0
        subst hp_eq
        have hw : (mk94U54Wire 0 t2).val < 175 ∨ (192 ≤ (mk94U54Wire 0 t2).val ∧
          (mk94U54Wire 0 t2).val < 232) := by
          fin_cases t2 <;> decide
        rw [hout _ (hw.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))]
        exact hP0 t2
      · by_cases hp1 : p18.val = 1
        · have hp_eq : p18 = 1 := Fin.ext hp1
          subst hp_eq
          rcases t2 with ⟨_ | _ | _ | v, hv⟩
          · change γ2 ⟨175, by decide⟩ = _
            rw [hγ2, hTOut ⟨175, by decide⟩ (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
              (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
              (fun _ ↦ wire_ne_of_lt (by dsimp; omega)), hγ1, e1_0, h75]
            dsimp only
            rcases fmkBit_cases (γ mk94A2W) with ha | ha <;>
              rcases fmkBit_cases (γ mk94C2W) with hc | hc <;>
              simp [ha, hc, s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
          · change γ2 ⟨195, by decide⟩ = _
            rw [hout _ (Or.inr (Or.inl (by decide))), h95]
            dsimp only
            rcases fmkBit_cases (γ mk94A2W) with ha | ha <;>
              rcases fmkBit_cases (γ mk94C2W) with hc | hc <;>
              simp [ha, hc, s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
          · change γ2 ⟨232, by decide⟩ = _
            rw [hγ2, hTOut ⟨232, by decide⟩ (fun _ ↦ wire_ne_of_gt (by dsimp; omega))
              (fun _ ↦ wire_ne_of_lt (by dsimp; omega))
              (fun _ ↦ wire_ne_of_lt (by dsimp; omega)), hγ1, e1_1, h75]
            dsimp only
            rcases fmkBit_cases (γ mk94A2W) with ha | ha <;>
              rcases fmkBit_cases (γ mk94C2W) with hc | hc <;>
              simp [ha, hc, s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
          · omega
        · let j : Fin 16 := ⟨p18.val - 2, by omega⟩
          have hj1 : γ1 ⟨176 + j.val, by omega⟩ =
              γ mk94AccW * (if 2 + j.val = mk94ActP18 γ then 1 else 0) :=
            (e1_out _ (wire_ne_of_gt (by
              dsimp; omega)) (wire_ne_of_lt (by dsimp; omega))).trans (hJ16 j)
          have hp_val : 2 + j.val = p18.val := by dsimp [j]; omega
          rcases t2 with ⟨_ | _ | _ | v, hv⟩
          · have hw : mk94U54Wire p18 ⟨0, hv⟩ = ⟨176 + j.val, by omega⟩ := by
              apply Fin.ext; simp [mk94U54Wire, j]; omega
            rw [hw, hγ2, hT0 j, ha1, hc1, hj1, hp_val]
            simp only; split_ifs <;> first | ring1 | omega
          · have hw : mk94U54Wire p18 ⟨1, hv⟩ = ⟨233 + 2 * j.val, by omega⟩ := by
              apply Fin.ext; simp [mk94U54Wire, hp0, hp1, j]
            rw [hw, hγ2, hT1 j, ha1, hc1, hj1, hp_val]
            simp only; split_ifs <;> first | ring1 | omega
          · have hw : mk94U54Wire p18 ⟨2, hv⟩ = ⟨234 + 2 * j.val, by omega⟩ := by
              apply Fin.ext; simp [mk94U54Wire, hp0, hp1, j]; omega
            rw [hw, hγ2, hT2 j, ha1, hc1, hj1, hp_val]
            simp only; split_ifs <;> first | ring1 | omega
          · omega
    · rw [hout mk94W11W (Or.inr (Or.inl (by
        decide))), hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
      exact hW11
    · exact (hout w (Or.inr (Or.inr (by omega)))).trans (hCl36 w (by omega))
    · rcases hq with hq1 | ⟨hq2, hq3⟩
      · exact hlt q hq1
      · exact hout q (Or.inr (Or.inl ⟨by omega, hq3⟩))
  exact ⟨⟨hCB1 _ (fun γ hγ ↦ hγ.2.2.2.2.2 _ (by decide)),
    hCT16 _ (fun _ ⟨γ, hγ, h⟩ ↦ by subst h; exact (hStep γ hγ).1)⟩,
    fun γ hγ ↦ (hStep γ hγ).2⟩

theorem mk94SplitAll36_spec :
    mk94SplitAll36.FwdClean mk94InvU18 ∧
    (∀ γ : BitAssignment 268, mk94InvU18 γ →
      let γ' := mk94SplitAll36.fwdBits γ
      mk94InvU54 γ' ∧
      ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ' q = γ q) := by
  refine ⟨⟨mk94SplitTop3_spec.1,
    mk94SplitTop33.fwdClean_mono
      (fun _ ⟨γ, hγ, h⟩ ↦ by subst h; exact (mk94SplitTop3_spec.2 γ hγ).1)
      mk94SplitTop33_spec.1⟩, fun γ hγ ↦ ?_⟩
  obtain ⟨hMid, hOut1⟩ := mk94SplitTop3_spec.2 γ hγ
  obtain ⟨hU54, hOut2⟩ := mk94SplitTop33_spec.2 _ hMid
  exact ⟨hU54, fun q hq ↦ (hOut2 q hq).trans (hOut1 q hq)⟩

theorem mk94InvU54_ext {δ₁ δ₂ : BitAssignment 268} (h₁ : mk94InvU54 δ₁) (h₂ : mk94InvU54 δ₂)
    (heq : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → δ₁ q = δ₂ q) : δ₁ =
    δ₂ := by
  have hlt : ∀ q : Wire 268, q.val < 174 → δ₁ q = δ₂ q := fun q hq ↦ heq q (Or.inl hq)
  have hu54 : ∀ p18 t2, δ₁ (mk94U54Wire p18 t2) = δ₂ (mk94U54Wire p18 t2) := fun p18 t2 ↦ by
    rw [h₁.1 p18 t2, h₂.1 p18 t2, hlt mk94AccW (by decide), mk94ActP18_congr hlt,
      hlt mk94A2W (by decide), hlt mk94C2W (by decide)]
  funext w
  by_cases h0 : w.val < 174
  · exact hlt w h0
  · by_cases h1 : w.val < 192
    · have hw : w = mk94U54Wire ⟨w.val - 174, by omega⟩ 0 :=
        Fin.ext (by dsimp [mk94U54Wire]; omega)
      rw [hw]; exact hu54 _ _
    · by_cases h2 : w.val = 192
      · have hw : w = mk94W11W := Fin.ext h2
        rw [hw, h₁.2.1, h₂.2.1, hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
      · by_cases h3 : w.val < 196
        · have hv193 : 193 ≤ w.val := by omega
          rcases w with ⟨v, hv⟩
          dsimp only at hv193 h3
          interval_cases v
          · exact hu54 0 1
          · exact hu54 0 2
          · exact hu54 1 1
        · by_cases h4 : w.val < 232
          · exact heq w (Or.inr ⟨by omega, h4⟩)
          · by_cases h5 : w.val = 232
            · have hw : w = mk94U54Wire 1 2 := Fin.ext h5
              rw [hw]; exact hu54 1 2
            · by_cases h6 : w.val < 265
              · let p18 : Fin 18 := ⟨2 + (w.val - 233) / 2, by omega⟩
                let t2 : Fin 3 := ⟨1 + (w.val - 233) % 2, by omega⟩
                have ht0 : ¬ t2.val = 0 := by dsimp [t2]; omega
                have hp0 : ¬ p18.val = 0 := by dsimp [p18]; omega
                have hp1 : ¬ p18.val = 1 := by dsimp [p18]; omega
                have hw : w = mk94U54Wire p18 t2 := by
                  apply Fin.ext; simp [mk94U54Wire, hp1, p18, t2]; omega
                rw [hw]; exact hu54 p18 t2
              · exact (h₁.2.2 w (by omega)).trans (h₂.2.2 w (by omega)).symm

def mk94Collapse33 (δ : BitAssignment 268) : BitAssignment 268 := fun w ↦ if w.val = 175 then
    (δ mk94AccW * if 1 = mk94ActP18 δ then 1 else 0) * (1 + δ mk94C2W) else if 176 ≤ w.val ∧
    w.val < 192 then δ mk94AccW * (if w.val - 174 = mk94ActP18 δ then 1 else 0) else if 232 ≤
    w.val then 0 else δ w

open Classical in
theorem mk94SplitTop33_rev_spec (δ : BitAssignment 268) (hδ : mk94InvU54 δ) : mk94InvMidTop3
    (mk94Collapse33 δ) ∧ δ = mk94SplitTop33.fwdBits (mk94Collapse33 δ) ∧
    mk94SplitTop33.revBits δ = mk94Collapse33 δ ∧ (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val
    ∧ q.val < 232)) → mk94Collapse33 δ q = δ q) := by
  have hout : ∀ q : Wire 268,
      (q.val < 175 ∨ (192 ≤ q.val ∧ q.val < 232)) → mk94Collapse33 δ q = δ q := by
    intro q hq
    dsimp only [mk94Collapse33]
    split_ifs <;> first | rfl | (rcases hq with h | ⟨h1, h2⟩ <;> omega)
  have hlt : ∀ q : Wire 268, q.val < 174 → mk94Collapse33 δ q = δ q :=
    fun q hq ↦ hout q (Or.inl (by omega))
  have hMid : mk94InvMidTop3 (mk94Collapse33 δ) := by
    refine ⟨fun t2 ↦ ?_, ?_, ?_, fun j ↦ ?_, ?_, fun w hw ↦ ?_⟩
    · have hw : (mk94U54Wire 0 t2).val < 175 ∨
          (192 ≤ (mk94U54Wire 0 t2).val ∧ (mk94U54Wire 0 t2).val < 232) := by
        fin_cases t2 <;> decide
      rw [hout _ hw, hlt mk94AccW (by decide), mk94ActP18_congr hlt,
        hlt mk94A2W (by decide), hlt mk94C2W (by decide)]
      exact hδ.1 0 t2
    · rw [hlt mk94AccW (by decide), mk94ActP18_congr hlt, hlt mk94C2W (by decide)]
      simp [mk94Collapse33]
    · rw [hout _ (Or.inr (by decide)), hlt mk94AccW (by decide), mk94ActP18_congr hlt,
        hlt mk94C2W (by decide)]
      have h11 := hδ.1 1 1
      change δ ⟨195, by decide⟩ = _ at h11
      rw [h11]
      rcases fmkBit_cases (δ mk94A2W) with ha | ha <;>
        rcases fmkBit_cases (δ mk94C2W) with hc | hc <;>
        simp [ha, hc, s3Trit_00, s3Trit_01, s3Trit_10, s3Trit_11]
    · rw [hlt mk94AccW (by decide), mk94ActP18_congr hlt]
      dsimp only [mk94Collapse33]
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
      have hsub : 176 + j.val - 174 = 2 + j.val := by omega
      rw [hsub]
    · rw [hout mk94W11W (Or.inr (by decide)), hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
      exact hδ.2.1
    · dsimp only [mk94Collapse33]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  obtain ⟨hU54', hOut'⟩ := mk94SplitTop33_spec.2 _ hMid
  have hkeep : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) →
      mk94Collapse33 δ q = δ q := fun q hq ↦
    hout q (hq.elim (fun h ↦ Or.inl (by omega)) (fun ⟨h1, h2⟩ ↦ Or.inr ⟨by omega, h2⟩))
  have heq : δ = mk94SplitTop33.fwdBits (mk94Collapse33 δ) :=
    mk94InvU54_ext hδ hU54' fun q hq ↦ ((hOut' q hq).trans (hkeep q hq)).symm
  refine ⟨hMid, heq, ?_, hkeep⟩
  conv_lhs => rw [heq]
  exact mk94SplitTop33.revBits_fwdBits _

def mk94Collapse36 (δ : BitAssignment 268) : BitAssignment 268 := fun w ↦ if 174 ≤ w.val ∧
    w.val < 192 then δ mk94AccW * (if w.val - 174 = mk94ActP18 δ then 1 else 0) else if
    (193 ≤ w.val ∧ w.val < 196) ∨ 232 ≤ w.val then 0 else δ w

open Classical in
theorem mk94SplitAll36_rev_spec (δ : BitAssignment 268) (hδ : mk94InvU54 δ) : mk94InvU18
    (mk94Collapse36 δ) ∧ δ = mk94SplitAll36.fwdBits (mk94Collapse36 δ) ∧
    mk94SplitAll36.revBits δ = mk94Collapse36 δ ∧ (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val
    ∧ q.val < 232)) → mk94Collapse36 δ q = δ q) := by
  have hkeep : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) →
      mk94Collapse36 δ q = δ q := by
    intro q hq
    dsimp only [mk94Collapse36]
    split_ifs <;> first | rfl | (rcases hq with h | ⟨h1, h2⟩ <;> omega)
  have hlt : ∀ q : Wire 268, q.val < 174 → mk94Collapse36 δ q = δ q :=
    fun q hq ↦ hkeep q (Or.inl hq)
  have hU18 : mk94InvU18 (mk94Collapse36 δ) := by
    refine ⟨fun p18 ↦ ?_, ?_, by simp [mk94Collapse36], by simp [mk94Collapse36],
      by simp [mk94Collapse36], fun w hw ↦ ?_⟩
    · rw [hlt mk94AccW (by decide), mk94ActP18_congr hlt]
      dsimp only [mk94Collapse36, mk94U18W]
      rw [ite_eq_left ⟨by omega, by omega⟩]
      have hsub : 174 + p18.val - 174 = p18.val := by omega
      rw [hsub]
    · rw [hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
      dsimp only [mk94Collapse36, mk94W11W]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hδ.2.1
    · dsimp only [mk94Collapse36]
      rw [ite_eq_right (by omega), ite_eq_left (Or.inr (by omega))]
  obtain ⟨hU54', hOut'⟩ := mk94SplitAll36_spec.2 _ hU18
  have heq : δ = mk94SplitAll36.fwdBits (mk94Collapse36 δ) :=
    mk94InvU54_ext hδ hU54' fun q hq ↦ ((hOut' q hq).trans (hkeep q hq)).symm
  refine ⟨hU18, heq, ?_, hkeep⟩
  conv_lhs => rw [heq]
  exact mk94SplitAll36.revBits_fwdBits _

theorem mk94ZMod2_mul_self (x : ZMod 2) : x * x = x := by
  rcases fmkBit_cases x with h | h <;> simp [h]

theorem mk94ZMod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases fmkBit_cases x with h | h <;> simp [h]

theorem mk94ZMod2_eq_of_two_dvd {x y k : ZMod 2} (h : x - y = 2 * k) : x = y :=
  sub_eq_zero.mp (by rw [h, show (2 : ZMod 2) = 0 by decide, zero_mul])

theorem mk94OneHot_mul_sum {N : ℕ} (u α β : Fin N → ZMod 2)
    (hu : ∀ i j : Fin N, i ≠ j → u i * u j = 0) : (∑ i : Fin N, α i * u i) *
    (∑ j : Fin N, β j * u j) = ∑ i : Fin N, (α i * β i) * u i := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · calc (α i * u i) * (β i * u i)
        = (α i * β i) * (u i * u i) := by ring
      _ = (α i * β i) * u i := by rw [mk94ZMod2_mul_self]
  · intro j _ hji
    calc (α i * u i) * (β j * u j)
        = (α i * β j) * (u i * u j) := by ring
      _ = 0 := by rw [hu i j hji.symm, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem mk94PairMux_algebra {N : ℕ} (u : Fin N → ZMod 2)
    (hu : ∀ i j : Fin N, i ≠ j → u i * u j = 0) (b0 b1 : ZMod 2)
    (C0 X0 Y0 Z0 C1 X1 Y1 Z1 : Fin N → ZMod 2) :
    let w11 := b0 * b1
    let P1 := (b0 + ∑ i, (Y0 i + Y1 i) * u i) * (b1 + ∑ i, X0 i * u i)
    let P2 := (b1 + ∑ i, Z0 i * u i) * (w11 + ∑ i, Y1 i * u i)
    let P3 := (b0 + ∑ i, (Z0 i + Z1 i) * u i) * (w11 + ∑ i, X1 i * u i)
    let L0 := fun i ↦ C0 i + (Y0 i + Y1 i) * X0 i + Z0 i * Y1 i
    let L1 := fun i ↦ C1 i + Z0 i * Y1 i + (Z0 i + Z1 i) * X1 i
    P1 + P2 + (∑ i, L0 i * u i) =
        (∑ i, (C0 i + b0 * X0 i + b1 * Y0 i + b0 * b1 * Z0 i) * u i) ∧
      P2 + P3 + (∑ i, L1 i * u i) =
        (∑ i, (C1 i + b0 * X1 i + b1 * Y1 i + b0 * b1 * Z1 i) * u i) := by
  intro w11 P1 P2 P3 L0 L1
  have hmul (a b : ZMod 2) (hab : a * b = b0 * b1) (U V : Fin N → ZMod 2) :
      (a + ∑ i, U i * u i) * (b + ∑ i, V i * u i) =
        b0 * b1 + (∑ i, a * (V i * u i)) + (∑ i, b * (U i * u i)) +
          (∑ i, (U i * V i) * u i) := by
    rw [add_mul, mul_add, mul_add, mk94OneHot_mul_sum u _ _ hu, mul_comm (∑ i, _) b,
      Finset.mul_sum, Finset.mul_sum]
    linear_combination hab
  have hsum (A1 A2 A3 B1 B2 B3 L R : Fin N → ZMod 2)
      (hpt : ∀ i, A1 i + A2 i + A3 i + B1 i + B2 i + B3 i + L i * u i = R i * u i) :
      (b0 * b1 + (∑ i, A1 i) + (∑ i, A2 i) + (∑ i, A3 i)) +
        (b0 * b1 + (∑ i, B1 i) + (∑ i, B2 i) + (∑ i, B3 i)) + (∑ i, L i * u i) =
        ∑ i, R i * u i := by
    have hr : (b0 * b1 + (∑ i, A1 i) + (∑ i, A2 i) + (∑ i, A3 i)) +
        (b0 * b1 + (∑ i, B1 i) + (∑ i, B2 i) + (∑ i, B3 i)) + (∑ i, L i * u i) =
        (b0 * b1 + b0 * b1) + ((∑ i, A1 i) + (∑ i, A2 i) + (∑ i, A3 i) +
          (∑ i, B1 i) + (∑ i, B2 i) + (∑ i, B3 i) + (∑ i, L i * u i)) := by ring
    rw [hr, mk94ZMod2_add_self, zero_add]
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ hpt i
  have hb1w : b1 * w11 = b0 * b1 := by
    dsimp [w11]
    rw [← mul_assoc, mul_comm b1 b0, mul_assoc, mk94ZMod2_mul_self]
  have hb0w : b0 * w11 = b0 * b1 := by
    dsimp [w11]
    rw [← mul_assoc, mk94ZMod2_mul_self]
  have hp1 : P1 = _ := hmul b0 b1 rfl (fun i ↦ Y0 i + Y1 i) X0
  have hp2 : P2 = _ := hmul b1 w11 hb1w Z0 Y1
  have hp3 : P3 = _ := hmul b0 w11 hb0w (fun i ↦ Z0 i + Z1 i) X1
  refine ⟨?_, ?_⟩
  · rw [hp1, hp2]
    exact hsum _ _ _ _ _ _ L0 _ fun i ↦ mk94ZMod2_eq_of_two_dvd
      (k := (b1 * Y1 i + (Y0 i + Y1 i) * X0 i + Z0 i * Y1 i) * u i) (by dsimp only [L0]; ring)
  · rw [hp2, hp3]
    exact hsum _ _ _ _ _ _ L1 _ fun i ↦ mk94ZMod2_eq_of_two_dvd
      (k := (b0 * b1 * Z0 i + Z0 i * Y1 i + (Z0 i + Z1 i) * X1 i) * u i) (by dsimp only [L1]; ring)

theorem mk94FourWayMux_eq (b0 b1 : ZMod 2) (f : ℕ → ℕ → ZMod 2) : f 0 0 + b0 * (f 0 0 + f 0 1)
    + b1 * (f 0 0 + f 1 0) + b0 * b1 * (f 0 0 + f 0 1 + f 1 0 + f 1 1) = f b1.val b0.val := by
  rcases fmkBit_cases b0 with h0 | h0 <;> rcases fmkBit_cases b1 with h1 | h1
  · simp [h0, h1, ZMod.val_zero]
  · simp only [h0, h1, ZMod.val_zero, ZMod.val_one]
    exact mk94ZMod2_eq_of_two_dvd (k := f 0 0) (by ring)
  · simp only [h0, h1, ZMod.val_zero, ZMod.val_one]
    exact mk94ZMod2_eq_of_two_dvd (k := f 0 0) (by ring)
  · simp only [h0, h1, ZMod.val_one]
    exact mk94ZMod2_eq_of_two_dvd (k := 2 * f 0 0 + f 0 1 + f 1 0) (by ring)

def mk94U54ByP (p : Fin 54) : Wire 268 := mk94U54Wire (mk94InvPOrig p).1 (mk94InvPOrig p).2

theorem mk94U54ByP_bounds (p : Fin 54) :
    (mk94U54ByP p).val < 265 ∧ ¬(196 ≤ (mk94U54ByP p).val ∧ (mk94U54ByP p).val < 232) := by
  revert p; decide

open Classical in
theorem mk94InvU54_byP {γ : BitAssignment 268} (hγ : mk94InvU54 γ) (p : Fin 54) :
    γ (mk94U54ByP p) = γ mk94AccW *
      (if p.val = s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val then 1 else 0) :=
        by
  dsimp only [mk94U54ByP]
  rw [hγ.1]
  let pAct : Fin 54 := mk94POrig ⟨mk94ActP18 γ, mk94ActP18_lt γ⟩
    ⟨s3Trit (γ mk94A2W) (γ mk94C2W), s3Trit_lt_three _ _⟩
  have hiff : ((mk94InvPOrig p).1.val = mk94ActP18 γ ∧
      (mk94InvPOrig p).2.val = s3Trit (γ mk94A2W) (γ mk94C2W)) ↔
      p.val = s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val := by
    rw [← mk94POrig_act_eq γ]
    constructor
    · rintro ⟨h1, h2⟩
      have heq_pt : mk94InvPOrig p = (⟨mk94ActP18 γ, mk94ActP18_lt γ⟩, ⟨s3Trit (γ mk94A2W) (γ
          mk94C2W), s3Trit_lt_three _ _⟩) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      have hp : p = pAct := by
        rw [← mk94POrig_invPOrig p, heq_pt]
      exact congrArg Fin.val hp
    · intro hp
      have hp_eq : p = pAct := Fin.ext hp
      rw [hp_eq]
      dsimp only [pAct]
      rw [mk94InvPOrig_pOrig (_, _)]
      exact ⟨rfl, rfl⟩
  by_cases hc : p.val = s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
  · rw [ite_eq_left hc, ite_eq_left (hiff.mpr hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h ↦ hc (hiff.mp h))]

open Classical in
theorem mk94InvU54_oneHot {γ : BitAssignment 268} (hγ : mk94InvU54 γ) (i j : Fin 54)
    (hij : i ≠ j) : γ (mk94U54ByP i) * γ (mk94U54ByP j) = 0 := by
  rw [mk94InvU54_byP hγ i, mk94InvU54_byP hγ j]
  have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  split_ifs with hi hj
  · exact absurd (hi.trans hj.symm) hne
  · ring
  · ring
  · ring

def mk94CliffXorSum {M : ℕ} :
    (N : ℕ) → (src : Fin N → Wire M) → (mask : Fin N → ZMod 2) → (dst : Wire M) →
    (∀ i, src i ≠ dst) → CliffProg M
  | 0, _, _, _, _ => .nil
  | k + 1, src, mask, dst, hne =>
      .seq
        (mk94CliffXorSum k (fun i ↦ src i.castSucc) (fun i ↦ mask i.castSucc) dst
          (fun i ↦ hne i.castSucc))
        (if mask (Fin.last k) = 1 then .cnot (src (Fin.last k)) dst (hne (Fin.last k)) else .nil)

theorem mk94CliffXorSum_eval {M : ℕ} :
    ∀ (N : ℕ) (src : Fin N → Wire M) (mask : Fin N → ZMod 2) (dst : Wire M)
      (hne : ∀ i, src i ≠ dst) (γ : BitAssignment M),
      (mk94CliffXorSum N src mask dst hne).eval γ =
        Function.update γ dst (γ dst + ∑ i : Fin N, mask i * γ (src i))
  | 0, _, _, dst, _, γ => by simp [mk94CliffXorSum, CliffProg.eval]
  | k + 1, src, mask, dst, hne, γ => by
      dsimp only [mk94CliffXorSum, CliffProg.eval]
      rw [mk94CliffXorSum_eval k (fun i ↦ src i.castSucc) (fun i ↦ mask i.castSucc) dst
        (fun i ↦ hne i.castSucc) γ, Fin.sum_univ_castSucc]
      rcases fmkBit_cases (mask (Fin.last k)) with hm | hm
      · simp [hm, CliffProg.eval]
      · simp [hm, CliffProg.eval, Function.update_idem, Function.update_self,
          Function.update_of_ne (hne (Fin.last k)), add_assoc]

def mk94ScrAW : Wire 268 := ⟨265, by decide⟩
def mk94ScrBW : Wire 268 := ⟨266, by decide⟩
def mk94ScrOutW : Wire 268 := ⟨267, by decide⟩

def mk94LoadScr54 (sel : Wire 268) (lin : Fin 54 → ZMod 2) (dst : Wire 268)
    (hsel : sel ≠ dst) (hdst : 265 ≤ dst.val) : CliffProg 268 :=
  .seq (.cnot sel dst hsel)
    (mk94CliffXorSum 54 mk94U54ByP lin dst
      (fun i ↦ wire_ne_of_lt (by have := (mk94U54ByP_bounds i).1; omega)))

theorem mk94LoadScr54_eval (sel : Wire 268) (lin : Fin 54 → ZMod 2) (dst : Wire 268)
    (hsel : sel ≠ dst) (hdst : 265 ≤ dst.val) (γ : BitAssignment 268) :
    (mk94LoadScr54 sel lin dst hsel hdst).eval γ =
      Function.update γ dst (γ dst + (γ sel + ∑ i : Fin 54, lin i * γ (mk94U54ByP i))) := by
  dsimp only [mk94LoadScr54, CliffProg.eval]
  rw [mk94CliffXorSum_eval]
  have hu_ne : ∀ i : Fin 54, mk94U54ByP i ≠ dst :=
    fun i ↦ wire_ne_of_lt (by have := (mk94U54ByP_bounds i).1; omega)
  have hsum : (∑ i : Fin 54, lin i * Function.update γ dst (γ dst + γ sel) (mk94U54ByP i)) =
      ∑ i : Fin 54, lin i * γ (mk94U54ByP i) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [Function.update_of_ne (hu_ne i)]
  rw [hsum, Function.update_self, Function.update_idem, add_assoc]

def mk94RunProd54 (selA selB : Wire 268) (linA linB : Fin 54 → ZMod 2) (out0 out1 : Wire 268)
    (use0 use1 : Bool) (hselA : selA.val < 196) (hselB : selB.val < 196)
    (hout0 : 196 ≤ out0.val ∧ out0.val < 232) (hout1 : 196 ≤ out1.val ∧ out1.val < 232) :
    TempPhaseProg 268 :=
  let cLoad : CliffProg 268 :=
    .seq
      (mk94LoadScr54 selA linA mk94ScrAW
        (wire_ne_of_lt (by dsimp [mk94ScrAW]; omega)) (by decide))
      (mk94LoadScr54 selB linB mk94ScrBW
        (wire_ne_of_lt (by dsimp [mk94ScrBW]; omega)) (by decide))
  let cTgt : CliffProg 268 :=
    .seq
      (if use0 then .cnot mk94ScrOutW out0 (wire_ne_of_gt (by
        dsimp [mk94ScrOutW]; omega)) else .nil)
      (if use1 then .cnot mk94ScrOutW out1 (wire_ne_of_gt (by
        dsimp [mk94ScrOutW]; omega)) else .nil)
  .seq (.cliff cLoad)
    (.seq (.tempAnd mk94ScrAW mk94ScrBW mk94ScrOutW (by
      decide) (by decide) (by decide) (.cliff cTgt))
      (.cliff cLoad))

open Classical in
theorem mk94RunProd54_spec (selA selB : Wire 268) (linA linB : Fin 54 → ZMod 2)
    (out0 out1 : Wire 268) (use0 use1 : Bool)
    (hselA : selA.val < 196) (hselB : selB.val < 196)
    (hout0 : 196 ≤ out0.val ∧ out0.val < 232)
    (hout1 : 196 ≤ out1.val ∧ out1.val < 232) (h01 : out0 ≠ out1) :
    let prog := mk94RunProd54 selA selB linA linB out0 out1 use0 use1 hselA hselB hout0 hout1
    prog.countTempAnd = 1 ∧
    ValidCleanRem 268 3 prog ∧
    (∀ γ, prog.evalSign γ = 0) ∧
    (∀ γ : BitAssignment 268, cleanRem 268 3 γ →
      let valA := γ selA + ∑ i : Fin 54, linA i * γ (mk94U54ByP i)
      let valB := γ selB + ∑ i : Fin 54, linB i * γ (mk94U54ByP i)
      prog.evalBits γ out0 = γ out0 + (if use0 then valA * valB else 0) ∧
      prog.evalBits γ out1 = γ out1 + (if use1 then valA * valB else 0) ∧
      ∀ q : Wire 268, q ≠ out0 → q ≠ out1 → prog.evalBits γ q = γ q) := by
  intro prog
  have hcLoad : ∀ δ : BitAssignment 268,
      (CliffProg.seq
        (mk94LoadScr54 selA linA mk94ScrAW (wire_ne_of_lt (by
          dsimp [mk94ScrAW]; omega)) (by decide))
        (mk94LoadScr54 selB linB mk94ScrBW (wire_ne_of_lt (by
          dsimp [mk94ScrBW]; omega)) (by decide))).eval δ =
      Function.update
        (Function.update δ mk94ScrAW (δ mk94ScrAW + (δ selA + ∑ i, linA i * δ (mk94U54ByP i))))
        mk94ScrBW (δ mk94ScrBW + (δ selB + ∑ i, linB i * δ (mk94U54ByP i))) := by
    intro δ
    dsimp only [CliffProg.eval]
    rw [mk94LoadScr54_eval, mk94LoadScr54_eval]
    have hne_ab : mk94ScrBW ≠ mk94ScrAW := by decide
    have hne_sb : selB ≠ mk94ScrAW := wire_ne_of_lt (by dsimp [mk94ScrAW]; omega)
    have hsum : (∑ i : Fin 54, linB i *
        Function.update δ mk94ScrAW (δ mk94ScrAW + (δ selA + ∑ j, linA j * δ (mk94U54ByP j)))
          (mk94U54ByP i)) = ∑ i : Fin 54, linB i * δ (mk94U54ByP i) :=
      Finset.sum_congr rfl fun i _ ↦ by
        rw [Function.update_of_ne (wire_ne_of_lt (by
          have := (mk94U54ByP_bounds i).1; dsimp [mk94ScrAW]; omega))]
    rw [Function.update_of_ne hne_ab, Function.update_of_ne hne_sb, hsum]
  have hcTgt : ∀ δ : BitAssignment 268,
      (CliffProg.seq
        (if use0 then .cnot mk94ScrOutW out0 (wire_ne_of_gt (by
          dsimp [mk94ScrOutW]; omega)) else .nil)
        (if use1 then .cnot mk94ScrOutW out1 (wire_ne_of_gt (by
          dsimp [mk94ScrOutW]; omega)) else .nil)).eval δ =
      Function.update
        (Function.update δ out0 (δ out0 + if use0 then δ mk94ScrOutW else 0))
        out1 (δ out1 + if use1 then δ mk94ScrOutW else 0) := by
    intro δ
    have h267_0 : mk94ScrOutW ≠ out0 := wire_ne_of_gt (by dsimp [mk94ScrOutW]; omega)
    have h267_1 : mk94ScrOutW ≠ out1 := wire_ne_of_gt (by dsimp [mk94ScrOutW]; omega)
    cases use0 <;> cases use1 <;>
      simp [CliffProg.eval, Function.update_of_ne h01.symm, Function.update_of_ne h267_0]
  have h0_lt : ∀ w : Wire 268, 265 ≤ w.val → w ≠ out0 ∧ w ≠ out1 := fun w hw ↦
    ⟨wire_ne_of_gt (by omega), wire_ne_of_gt (by omega)⟩
  refine ⟨rfl, ?_, fun γ ↦ ?_, fun γ hγ ↦ ?_⟩
  · refine ⟨1, by decide, trivial, ⟨0, by decide, ⟨by decide, trivial, fun δ _ ↦ ?_⟩, trivial,
      fun _ _ w hw ↦ by have := w.isLt; omega⟩, fun δ hδ w hw ↦ ?_⟩
    · dsimp only [TempPhaseProg.evalBits]
      rw [hcTgt]
      exact ⟨by rw [Function.update_of_ne (h0_lt mk94ScrAW (by decide)).2,
          Function.update_of_ne (h0_lt mk94ScrAW (by decide)).1],
        by rw [Function.update_of_ne (h0_lt mk94ScrBW (by decide)).2,
          Function.update_of_ne (h0_lt mk94ScrBW (by decide)).1],
        by rw [Function.update_of_ne (h0_lt mk94ScrOutW (by decide)).2,
          Function.update_of_ne (h0_lt mk94ScrOutW (by decide)).1]⟩
    · have hw267 : w = mk94ScrOutW := Fin.ext (by have := w.isLt; dsimp [mk94ScrOutW]; omega)
      subst hw267
      dsimp only [TempPhaseProg.evalBits]
      rw [hcLoad, Function.update_of_ne (by decide : mk94ScrOutW ≠ mk94ScrBW),
        Function.update_of_ne (by decide : mk94ScrOutW ≠ mk94ScrAW)]
      exact hδ mk94ScrOutW (by decide)
  · simp [prog, mk94RunProd54, TempPhaseProg.evalSign]
  · intro valA valB
    dsimp only [prog, mk94RunProd54, TempPhaseProg.evalBits]
    rw [hcLoad γ]
    set γ1 := Function.update (Function.update γ mk94ScrAW (γ mk94ScrAW + valA))
      mk94ScrBW (γ mk94ScrBW + valB)
    have hγ1_A : γ1 mk94ScrAW = valA := by
      simp [γ1, Function.update_of_ne (by decide : mk94ScrAW ≠ mk94ScrBW), hγ mk94ScrAW (by decide)]
    have hγ1_B : γ1 mk94ScrBW = valB := by
      simp [γ1, hγ mk94ScrBW (by decide)]
    have hγ1_O : γ1 mk94ScrOutW = 0 := by
      simp [γ1, Function.update_of_ne (by decide : mk94ScrOutW ≠ mk94ScrBW),
        Function.update_of_ne (by decide : mk94ScrOutW ≠ mk94ScrAW), hγ mk94ScrOutW (by decide)]
    set γ2 := Function.update γ1 mk94ScrOutW (γ1 mk94ScrOutW + γ1 mk94ScrAW * γ1 mk94ScrBW)
    have hγ2_O : γ2 mk94ScrOutW = valA * valB := by simp [γ2, hγ1_O, hγ1_A, hγ1_B]
    rw [hcTgt γ2]
    set γ3 :=
      Function.update (Function.update γ2 out0 (γ2 out0 + if use0 then γ2 mk94ScrOutW else 0))
      out1 (γ2 out1 + if use1 then γ2 mk94ScrOutW else 0)
    have hγ3_O : γ3 mk94ScrOutW = valA * valB := by
      simp [γ3, Function.update_of_ne (h0_lt mk94ScrOutW (by decide)).2,
        Function.update_of_ne (h0_lt mk94ScrOutW (by decide)).1, hγ2_O]
    have hγ3_A : γ3 mk94ScrAW = valA := by
      simp [γ3, γ2, Function.update_of_ne (h0_lt mk94ScrAW (by decide)).2,
        Function.update_of_ne (h0_lt mk94ScrAW (by decide)).1,
        Function.update_of_ne (by decide : mk94ScrAW ≠ mk94ScrOutW), hγ1_A]
    have hγ3_B : γ3 mk94ScrBW = valB := by
      simp [γ3, γ2, Function.update_of_ne (h0_lt mk94ScrBW (by decide)).2,
        Function.update_of_ne (h0_lt mk94ScrBW (by decide)).1,
        Function.update_of_ne (by decide : mk94ScrBW ≠ mk94ScrOutW), hγ1_B]
    set γ4 := Function.update γ3 mk94ScrOutW (γ3 mk94ScrOutW + γ3 mk94ScrAW * γ3 mk94ScrBW)
    rw [hcLoad γ4]
    have hγ4_out : ∀ q : Wire 268, q ≠ mk94ScrAW → q ≠ mk94ScrBW → q ≠ mk94ScrOutW →
        q ≠ out0 → q ≠ out1 → γ4 q = γ q := fun q hA hB hO h0 h1 ↦ by
      simp [γ4, γ3, γ2, γ1, Function.update_of_ne hO, Function.update_of_ne h1,
        Function.update_of_ne h0, Function.update_of_ne hB, Function.update_of_ne hA]
    have hselA_4 : γ4 selA = γ selA := hγ4_out selA
      (wire_ne_of_lt (by dsimp [mk94ScrAW]; omega))
      (wire_ne_of_lt (by dsimp [mk94ScrBW]; omega))
      (wire_ne_of_lt (by dsimp [mk94ScrOutW]; omega))
      (wire_ne_of_lt (by omega)) (wire_ne_of_lt (by omega))
    have hselB_4 : γ4 selB = γ selB := hγ4_out selB
      (wire_ne_of_lt (by dsimp [mk94ScrAW]; omega))
      (wire_ne_of_lt (by dsimp [mk94ScrBW]; omega))
      (wire_ne_of_lt (by dsimp [mk94ScrOutW]; omega))
      (wire_ne_of_lt (by omega)) (wire_ne_of_lt (by omega))
    have hu_4 : ∀ i : Fin 54, γ4 (mk94U54ByP i) = γ (mk94U54ByP i) := fun i ↦ by
      obtain ⟨hb1, hb2⟩ := mk94U54ByP_bounds i
      exact hγ4_out _
        (wire_ne_of_lt (by dsimp [mk94ScrAW]; omega))
        (wire_ne_of_lt (by dsimp [mk94ScrBW]; omega))
        (wire_ne_of_lt (by dsimp [mk94ScrOutW]; omega))
        (fun h ↦ hb2 (by rw [h]; exact hout0))
        (fun h ↦ hb2 (by rw [h]; exact hout1))
    have hsumA_4 : (∑ i : Fin 54, linA i * γ4 (mk94U54ByP i)) = ∑ i : Fin 54,
      linA i * γ (mk94U54ByP i) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hu_4 i]
    have hsumB_4 : (∑ i : Fin 54, linB i * γ4 (mk94U54ByP i)) = ∑ i : Fin 54,
      linB i * γ (mk94U54ByP i) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hu_4 i]
    have hγ4_A : γ4 mk94ScrAW = valA := by
      simp [γ4, Function.update_of_ne (by decide : mk94ScrAW ≠ mk94ScrOutW), hγ3_A]
    have hγ4_B : γ4 mk94ScrBW = valB := by
      simp [γ4, Function.update_of_ne (by decide : mk94ScrBW ≠ mk94ScrOutW), hγ3_B]
    have hγ4_O : γ4 mk94ScrOutW = 0 := by
      simp [γ4, hγ3_O, hγ3_A, hγ3_B]
    rw [hselA_4, hsumA_4, hselB_4, hsumB_4, hγ4_A, hγ4_B]
    change Function.update (Function.update γ4 mk94ScrAW (valA + valA)) mk94ScrBW (valB +
      valB) out0 = _ ∧
      Function.update (Function.update γ4 mk94ScrAW (valA + valA)) mk94ScrBW (valB + valB) out1 =
        _ ∧ _
    rw [mk94ZMod2_add_self valA, mk94ZMod2_add_self valB]
    refine ⟨?_, ?_, fun q hq0 hq1 ↦ ?_⟩
    · rw [Function.update_of_ne (h0_lt mk94ScrBW (by decide)).1.symm,
        Function.update_of_ne (h0_lt mk94ScrAW (by decide)).1.symm]
      dsimp only [γ4, γ3]
      rw [Function.update_of_ne (h0_lt mk94ScrOutW (by decide)).1.symm,
        Function.update_of_ne h01, Function.update_self, hγ2_O]
      dsimp only [γ2, γ1]
      rw [Function.update_of_ne (h0_lt mk94ScrOutW (by decide)).1.symm,
        Function.update_of_ne (h0_lt mk94ScrBW (by decide)).1.symm,
        Function.update_of_ne (h0_lt mk94ScrAW (by decide)).1.symm]
    · rw [Function.update_of_ne (h0_lt mk94ScrBW (by decide)).2.symm,
        Function.update_of_ne (h0_lt mk94ScrAW (by decide)).2.symm]
      dsimp only [γ4, γ3]
      rw [Function.update_of_ne (h0_lt mk94ScrOutW (by decide)).2.symm,
        Function.update_self, hγ2_O]
      dsimp only [γ2, γ1]
      rw [Function.update_of_ne (h0_lt mk94ScrOutW (by decide)).2.symm,
        Function.update_of_ne (h0_lt mk94ScrBW (by decide)).2.symm,
        Function.update_of_ne (h0_lt mk94ScrAW (by decide)).2.symm]
    · by_cases hqA : q = mk94ScrAW
      · subst hqA
        rw [Function.update_of_ne (by decide : mk94ScrAW ≠ mk94ScrBW), Function.update_self]
        exact (hγ mk94ScrAW (by decide)).symm
      · by_cases hqB : q = mk94ScrBW
        · subst hqB
          rw [Function.update_self]
          exact (hγ mk94ScrBW (by decide)).symm
        · by_cases hqO : q = mk94ScrOutW
          · subst hqO
            rw [Function.update_of_ne (by decide : mk94ScrOutW ≠ mk94ScrBW),
              Function.update_of_ne (by decide : mk94ScrOutW ≠ mk94ScrAW), hγ4_O]
            exact (hγ mk94ScrOutW (by decide)).symm
          · rw [Function.update_of_ne hqB, Function.update_of_ne hqA]
            exact hγ4_out q hqA hqB hqO hq0 hq1

def mk94PairMuxStep (tTab : Fin 256 → ℕ) (m : Fin 18) : TempPhaseProg 268 :=
  let r0 : Fin 36 := ⟨2 * m.val, by omega⟩
  let r1 : Fin 36 := ⟨2 * m.val + 1, by omega⟩
  let out0 := mk94Bank36W r0
  let out1 := mk94Bank36W r1
  let vBit (b1 : ℕ) (p : Fin 54) (b0 : ℕ) (r : Fin 36) : ZMod 2 :=
    fmkBitZ ((tTab (fmkIdx0 b1 p.val b0)).testBit r.val)
  let C0 (p : Fin 54) := vBit 0 p 0 r0
  let X0 (p : Fin 54) := vBit 0 p 0 r0 + vBit 0 p 1 r0
  let Y0 (p : Fin 54) := vBit 0 p 0 r0 + vBit 1 p 0 r0
  let Z0 (p : Fin 54) := vBit 0 p 0 r0 + vBit 0 p 1 r0 + vBit 1 p 0 r0 + vBit 1 p 1 r0
  let C1 (p : Fin 54) := vBit 0 p 0 r1
  let X1 (p : Fin 54) := vBit 0 p 0 r1 + vBit 0 p 1 r1
  let Y1 (p : Fin 54) := vBit 0 p 0 r1 + vBit 1 p 0 r1
  let Z1 (p : Fin 54) := vBit 0 p 0 r1 + vBit 0 p 1 r1 + vBit 1 p 0 r1 + vBit 1 p 1 r1
  let L0 (p : Fin 54) := C0 p + (Y0 p + Y1 p) * X0 p + Z0 p * Y1 p
  let L1 (p : Fin 54) := C1 p + Z0 p * Y1 p + (Z0 p + Z1 p) * X1 p
  let hout0 : 196 ≤ out0.val ∧ out0.val < 232 := by dsimp [out0, mk94Bank36W, r0]; omega
  let hout1 : 196 ≤ out1.val ∧ out1.val < 232 := by dsimp [out1, mk94Bank36W, r1]; omega
  .seq (mk94RunProd54 mk94B0W mk94B1W (fun p ↦ Y0 p + Y1 p) X0 out0 out1 true false
      (by decide) (by decide) hout0 hout1)
    (.seq (mk94RunProd54 mk94B1W mk94W11W Z0 Y1 out0 out1 true true
        (by decide) (by decide) hout0 hout1)
      (.seq (mk94RunProd54 mk94B0W mk94W11W (fun p ↦ Z0 p + Z1 p) X1 out0 out1 false true
          (by decide) (by decide) hout0 hout1)
        (.cliff (.seq
          (mk94CliffXorSum 54 mk94U54ByP L0 out0
            (fun i ↦ fun h ↦ (mk94U54ByP_bounds i).2 (by rw [h]; exact hout0)))
          (mk94CliffXorSum 54 mk94U54ByP L1 out1
            (fun i ↦ fun h ↦ (mk94U54ByP_bounds i).2 (by rw [h]; exact hout1)))))))

theorem mk94InvU54_congr_bank {γ₁ γ₂ : BitAssignment 268}
    (h : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ₁ q = γ₂ q)
    (h₂ : mk94InvU54 γ₂) : mk94InvU54 γ₁ := by
  have hlt : ∀ q : Wire 268, q.val < 174 → γ₁ q = γ₂ q := fun q hq ↦ h q (by omega)
  refine ⟨fun p18 t2 ↦ ?_, ?_, fun w hw ↦ ?_⟩
  · have hb := (mk94U54ByP_bounds (mk94POrig p18 t2)).2
    dsimp only [mk94U54ByP] at hb
    rw [mk94InvPOrig_pOrig (p18, t2)] at hb
    rw [h _ hb, hlt mk94AccW (by decide), mk94ActP18_congr hlt,
      hlt mk94A2W (by decide), hlt mk94C2W (by decide)]
    exact h₂.1 p18 t2
  · rw [h mk94W11W (by decide), hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
    exact h₂.2.1
  · exact (h w (by omega)).trans (h₂.2.2 w hw)

open Classical in
theorem mk94PairMuxStep_spec (tTab : Fin 256 → ℕ) (m : Fin 18) :
    let prog := mk94PairMuxStep tTab m
    let r0 : Fin 36 := ⟨2 * m.val, by omega⟩
    let r1 : Fin 36 := ⟨2 * m.val + 1, by omega⟩
    prog.countTempAnd = 3 ∧
    ValidCleanRem 268 3 prog ∧
    (∀ γ, prog.evalSign γ = 0) ∧
    (∀ γ : BitAssignment 268, cleanRem 268 3 γ →
      ∀ q : Wire 268, q ≠ mk94Bank36W r0 → q ≠ mk94Bank36W r1 → prog.evalBits γ q = γ q) ∧
    (∀ γ : BitAssignment 268, mk94InvU54 γ →
      let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
      let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
      prog.evalBits γ (mk94Bank36W r0) =
          γ (mk94Bank36W r0) + γ mk94AccW * fmkBitZ ((tTab idx).testBit r0.val) ∧
        prog.evalBits γ (mk94Bank36W r1) =
          γ (mk94Bank36W r1) + γ mk94AccW * fmkBitZ ((tTab idx).testBit r1.val)) := by
  intro prog r0 r1
  let out0 := mk94Bank36W r0
  let out1 := mk94Bank36W r1
  have hout0 : 196 ≤ out0.val ∧ out0.val < 232 := by dsimp [out0, mk94Bank36W, r0]; omega
  have hout1 : 196 ≤ out1.val ∧ out1.val < 232 := by dsimp [out1, mk94Bank36W, r1]; omega
  have h01 : out0 ≠ out1 := mk94Bank36W_inj.ne (Fin.ne_of_val_ne (by dsimp [r0, r1]; omega))
  let vBit (b1 : ℕ) (p : Fin 54) (b0 : ℕ) (r : Fin 36) : ZMod 2 :=
    fmkBitZ ((tTab (fmkIdx0 b1 p.val b0)).testBit r.val)
  let C0 (p : Fin 54) := vBit 0 p 0 r0
  let X0 (p : Fin 54) := vBit 0 p 0 r0 + vBit 0 p 1 r0
  let Y0 (p : Fin 54) := vBit 0 p 0 r0 + vBit 1 p 0 r0
  let Z0 (p : Fin 54) := vBit 0 p 0 r0 + vBit 0 p 1 r0 + vBit 1 p 0 r0 + vBit 1 p 1 r0
  let C1 (p : Fin 54) := vBit 0 p 0 r1
  let X1 (p : Fin 54) := vBit 0 p 0 r1 + vBit 0 p 1 r1
  let Y1 (p : Fin 54) := vBit 0 p 0 r1 + vBit 1 p 0 r1
  let Z1 (p : Fin 54) := vBit 0 p 0 r1 + vBit 0 p 1 r1 + vBit 1 p 0 r1 + vBit 1 p 1 r1
  let L0 (p : Fin 54) := C0 p + (Y0 p + Y1 p) * X0 p + Z0 p * Y1 p
  let L1 (p : Fin 54) := C1 p + Z0 p * Y1 p + (Z0 p + Z1 p) * X1 p
  let step1 := mk94RunProd54 mk94B0W mk94B1W (fun p ↦ Y0 p + Y1 p) X0 out0 out1 true false
    (by decide) (by decide) hout0 hout1
  let step2 := mk94RunProd54 mk94B1W mk94W11W Z0 Y1 out0 out1 true true
    (by decide) (by decide) hout0 hout1
  let step3 := mk94RunProd54 mk94B0W mk94W11W (fun p ↦ Z0 p + Z1 p) X1 out0 out1 false true
    (by decide) (by decide) hout0 hout1
  let linStep := CliffProg.seq
    (mk94CliffXorSum 54 mk94U54ByP L0 out0
      (fun i h ↦ (mk94U54ByP_bounds i).2 (by rw [h]; exact hout0)))
    (mk94CliffXorSum 54 mk94U54ByP L1 out1
      (fun i h ↦ (mk94U54ByP_bounds i).2 (by rw [h]; exact hout1)))
  have hprog : prog = .seq step1 (.seq step2 (.seq step3 (.cliff linStep))) := rfl
  obtain ⟨_, hv1, hs1, hb1⟩ := mk94RunProd54_spec mk94B0W mk94B1W (fun p ↦ Y0 p + Y1 p) X0
    out0 out1 true false (by decide) (by decide) hout0 hout1 h01
  obtain ⟨_, hv2, hs2, hb2⟩ := mk94RunProd54_spec mk94B1W mk94W11W Z0 Y1
    out0 out1 true true (by decide) (by decide) hout0 hout1 h01
  obtain ⟨_, hv3, hs3, hb3⟩ := mk94RunProd54_spec mk94B0W mk94W11W (fun p ↦ Z0 p + Z1 p) X1
    out0 out1 false true (by decide) (by decide) hout0 hout1 h01
  have hcl_pres : ∀ (s : TempPhaseProg 268) (δ : BitAssignment 268),
      (∀ q, q ≠ out0 → q ≠ out1 → s.evalBits δ q = δ q) →
      cleanRem 268 3 δ → cleanRem 268 3 (s.evalBits δ) := fun s δ hs hδ w hw ↦
    (hs w (wire_ne_of_gt (by omega)) (wire_ne_of_gt (by omega))).trans (hδ w hw)
  have hcLin : ∀ δ : BitAssignment 268, linStep.eval δ = Function.update
      (Function.update δ out0 (δ out0 + ∑ i, L0 i * δ (mk94U54ByP i))) out1
      (δ out1 + ∑ i, L1 i * δ (mk94U54ByP i)) := by
    intro δ
    dsimp only [linStep, CliffProg.eval]
    rw [mk94CliffXorSum_eval, mk94CliffXorSum_eval]
    have hsum : (∑ i : Fin 54, L1 i * Function.update δ out0 (δ out0 + ∑ j, L0 j * δ
        (mk94U54ByP j)) (mk94U54ByP i)) = ∑ i : Fin 54, L1 i * δ (mk94U54ByP i) :=
      Finset.sum_congr rfl fun i _ ↦ by
        rw [Function.update_of_ne (fun h ↦ (mk94U54ByP_bounds i).2 (by rw [h]; exact hout0))]
    rw [Function.update_of_ne h01.symm, hsum]
  refine ⟨rfl, ?_, fun γ ↦ ?_, fun γ hγ q hq0 hq1 ↦ ?_, fun γ hγ ↦ ?_⟩
  · rw [hprog]
    refine ⟨3, by decide, hv1, ⟨3, by decide, hv2, ⟨3, by decide, hv3, trivial, ?_⟩, ?_⟩, ?_⟩
    · intro δ hδ; exact hcl_pres _ δ (hb3 δ hδ).2.2 hδ
    · intro δ hδ; exact hcl_pres _ δ (hb2 δ hδ).2.2 hδ
    · intro δ hδ; exact hcl_pres _ δ (hb1 δ hδ).2.2 hδ
  · rw [hprog]
    dsimp only [TempPhaseProg.evalSign]
    rw [hs1, hs2, hs3]
    simp
  · rw [hprog]
    dsimp only [TempPhaseProg.evalBits]
    have hcl1 := hcl_pres _ γ (hb1 γ hγ).2.2 hγ
    have hcl2 := hcl_pres _ _ (hb2 _ hcl1).2.2 hcl1
    rw [hcLin, Function.update_of_ne hq1, Function.update_of_ne hq0]
    exact ((hb3 _ hcl2).2.2 q hq0 hq1).trans (((hb2 _ hcl1).2.2 q hq0 hq1).trans ((hb1 γ hγ).2.2 q
      hq0 hq1))
  · intro pAct idx
    have hcl0 : cleanRem 268 3 γ := hγ.2.2
    set γ1 := step1.evalBits γ
    set γ2 := step2.evalBits γ1
    set γ3 := step3.evalBits γ2
    obtain ⟨e1_0, e1_1, e1_out⟩ := hb1 γ hcl0
    have hcl1 : cleanRem 268 3 γ1 := hcl_pres _ γ e1_out hcl0
    obtain ⟨e2_0, e2_1, e2_out⟩ := hb2 γ1 hcl1
    have hcl2 : cleanRem 268 3 γ2 := hcl_pres _ γ1 e2_out hcl1
    obtain ⟨e3_0, e3_1, e3_out⟩ := hb3 γ2 hcl2
    have hpres1 : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ1 q = γ q := fun q hq ↦
      e1_out q (fun h ↦ hq (by rw [h]; exact hout0)) (fun h ↦ hq (by rw [h]; exact hout1))
    have hpres2 : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ2 q = γ q := fun q hq ↦
      (e2_out q (fun h ↦ hq (by
        rw [h]; exact hout0)) (fun h ↦ hq (by rw [h]; exact hout1))).trans (hpres1 q hq)
    have hpres3 : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ3 q = γ q := fun q hq ↦
      (e3_out q (fun h ↦ hq (by
        rw [h]; exact hout0)) (fun h ↦ hq (by rw [h]; exact hout1))).trans (hpres2 q hq)
    have hsum_eq : ∀ (f : Fin 54 → ZMod 2) (δ : BitAssignment 268),
        (∀ q, ¬(196 ≤ q.val ∧ q.val < 232) → δ q = γ q) →
        (∑ i, f i * δ (mk94U54ByP i)) = ∑ i, f i * γ (mk94U54ByP i) := fun f δ hδ ↦
      Finset.sum_congr rfl fun i _ ↦ by rw [hδ _ (mk94U54ByP_bounds i).2]
    rw [hprog]
    change linStep.eval γ3 out0 = _ ∧ linStep.eval γ3 out1 = _
    rw [hcLin γ3, Function.update_of_ne h01, Function.update_self, Function.update_self]
    change (step3.evalBits γ2 out0 + ∑ i, L0 i * γ3 (mk94U54ByP i) = _) ∧
      (step3.evalBits γ2 out1 + ∑ i, L1 i * γ3 (mk94U54ByP i) = _)
    rw [hsum_eq L0 γ3 hpres3, hsum_eq L1 γ3 hpres3, e3_0, e3_1]
    change ((step2.evalBits γ1 out0 + _) + _ = _) ∧ ((step2.evalBits γ1 out1 + _) + _ = _)
    rw [e2_0, e2_1]
    change (((step1.evalBits γ out0 + _) + _) + _ = _) ∧ (((step1.evalBits γ out1 + _) + _) + _ = _)
    rw[e1_0, e1_1, hpres1 mk94B1W (by decide), hpres1 mk94W11W (by decide),
        hpres2 mk94B0W (by decide), hpres2 mk94W11W (by decide), hsum_eq Z0 γ1 hpres1,
        hsum_eq Y1 γ1 hpres1, hsum_eq (fun p ↦ Z0 p + Z1 p) γ2 hpres2, hsum_eq X1 γ2 hpres2,
        hγ.2.1]
    simp only [↓reduceIte, Bool.false_eq_true, add_zero]
    obtain ⟨halg0, halg1⟩ := mk94PairMux_algebra (fun i ↦ γ (mk94U54ByP i))
      (mk94InvU54_oneHot hγ) (γ mk94B0W) (γ mk94B1W) C0 X0 Y0 Z0 C1 X1 Y1 Z1
    have hpAct_lt : pAct < 54 := by
      have := s3NucleusQ27_lt (fun i ↦ γ (mk94U16W i))
      have := ZMod.val_lt (γ mk94BParW)
      dsimp [pAct]; omega
    let pFin : Fin 54 := ⟨pAct, hpAct_lt⟩
    have hcol : ∀ r : Fin 36,
        (∑ p : Fin 54, (vBit 0 p 0 r + γ mk94B0W * (vBit 0 p 0 r + vBit 0 p 1 r) +
            γ mk94B1W * (vBit 0 p 0 r + vBit 1 p 0 r) +
            γ mk94B0W * γ mk94B1W *
              (vBit 0 p 0 r + vBit 0 p 1 r + vBit 1 p 0 r + vBit 1 p 1 r)) * γ (mk94U54ByP p)) =
          γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val) := fun r ↦ by
      rw [Finset.sum_eq_single pFin]
      · have hmux := mk94FourWayMux_eq (γ mk94B0W) (γ mk94B1W) (fun b1 b0 ↦ vBit b1 pFin b0 r)
        rw [hmux, mk94InvU54_byP hγ pFin, ite_eq_left (rfl : pFin.val = pAct), mul_one]
        dsimp only [vBit, pFin, idx]
        ring
      · intro p _ hp
        rw [mk94InvU54_byP hγ p, ite_eq_right (fun h ↦ hp (Fin.ext h)), mul_zero, mul_zero]
      · intro hp; exact absurd (Finset.mem_univ pFin) hp
    have hassoc : ∀ a b c d : ZMod 2, a + b + c + d = a + (b + c + d) :=
      fun _ _ _ _ ↦ by ring
    dsimp only [L0, L1]
    constructor
    · rw [hassoc, halg0, hcol r0]
    · rw [hassoc, halg1, hcol r1]

def mk94SeqPairMux (tTab : Fin 256 → ℕ) : (k : ℕ) → k ≤ 18 → TempPhaseProg 268
  | 0, _ => .nil
  | k + 1, hk => .seq (mk94SeqPairMux tTab k (by omega)) (mk94PairMuxStep tTab ⟨k, hk⟩)

theorem mk94SeqPairMux_spec (tTab : Fin 256 → ℕ) :
    ∀ (k : ℕ) (hk : k ≤ 18),
      let prog := mk94SeqPairMux tTab k hk
      prog.countTempAnd = 3 * k ∧
      ValidCleanRem 268 3 prog ∧
      (∀ γ, prog.evalSign γ = 0) ∧
      (∀ γ : BitAssignment 268, cleanRem 268 3 γ →
        ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 196 + 2 * k) → prog.evalBits γ q = γ q) ∧
      (∀ γ : BitAssignment 268, mk94InvU54 γ →
        let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
        let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
        ∀ r : Fin 36, r.val < 2 * k →
          prog.evalBits γ (mk94Bank36W r) =
            γ (mk94Bank36W r) + γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val))
  | 0, _ =>
      ⟨rfl, trivial, fun _ ↦ rfl, fun _ _ _ _ ↦ rfl, fun _ _ r hr ↦ by omega⟩
  | k + 1, hk => by
      obtain ⟨hCntPre, hValPre, hSignPre, hOutPre, hBankPre⟩ := mk94SeqPairMux_spec tTab k (by
        omega)
      obtain ⟨hCntSt, hValSt, hSignSt, hOutSt, hBankSt⟩ := mk94PairMuxStep_spec tTab ⟨k, hk⟩
      have hcl_pre : ∀ γ, cleanRem 268 3 γ → cleanRem 268 3 ((mk94SeqPairMux tTab k (by
        omega)).evalBits γ) :=
        fun γ hγ w hw ↦ (hOutPre γ hγ w (by omega)).trans (hγ w hw)
      refine ⟨by dsimp [mk94SeqPairMux, TempPhaseProg.countTempAnd]; omega,
        ⟨3, by decide, hValPre, hValSt, hcl_pre⟩,
        fun γ ↦ by simp [mk94SeqPairMux, TempPhaseProg.evalSign, hSignPre, hSignSt],
        fun γ hγ q hq ↦ ?_,
        fun γ hγ ↦ ?_⟩
      · dsimp only [mk94SeqPairMux, TempPhaseProg.evalBits]
        have hq0 : q ≠ mk94Bank36W ⟨2 * k, by omega⟩ :=
          fun h ↦ hq (by rw [h]; dsimp [mk94Bank36W]; omega)
        have hq1 : q ≠ mk94Bank36W ⟨2 * k + 1, by omega⟩ :=
          fun h ↦ hq (by rw [h]; dsimp [mk94Bank36W]; omega)
        exact (hOutSt _ (hcl_pre γ hγ) q hq0 hq1).trans
          (hOutPre γ hγ q (fun h ↦ hq ⟨h.1, by omega⟩))
      · intro pAct idx r hr
        dsimp only [mk94SeqPairMux, TempPhaseProg.evalBits]
        let γ1 := (mk94SeqPairMux tTab k (by omega)).evalBits γ
        have hγ1 : γ1 = (mk94SeqPairMux tTab k (by omega)).evalBits γ := rfl
        have hpres : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ1 q = γ q :=
          fun q hq ↦ hOutPre γ hγ.2.2 q (fun h ↦ hq ⟨h.1, by omega⟩)
        have hInv1 : mk94InvU54 γ1 := mk94InvU54_congr_bank hpres hγ
        by_cases hrk : r.val < 2 * k
        · have hne0 : mk94Bank36W r ≠ mk94Bank36W ⟨2 * k, by omega⟩ :=
            mk94Bank36W_inj.ne (Fin.ne_of_val_ne (by dsimp; omega))
          have hne1 : mk94Bank36W r ≠ mk94Bank36W ⟨2 * k + 1, by omega⟩ :=
            mk94Bank36W_inj.ne (Fin.ne_of_val_ne (by dsimp; omega))
          rw [hOutSt γ1 hInv1.2.2 (mk94Bank36W r) hne0 hne1]
          exact hBankPre γ hγ r hrk
        · obtain ⟨hSt0, hSt1⟩ := hBankSt γ1 hInv1
          dsimp only at hSt0 hSt1
          have hidx_eq : fmkIdx0 (γ1 mk94B1W).val
              (s3NucleusQ27 (fun i ↦ γ1 (mk94U16W i)) + 27 * (γ1 mk94BParW).val)
              (γ1 mk94B0W).val = idx := by
            have hu_eq : (fun i ↦ γ1 (mk94U16W i)) = fun i ↦ γ (mk94U16W i) :=
              funext fun i ↦ hpres _ (by dsimp [mk94U16W]; omega)
            rw [hu_eq, hpres mk94B1W (by
              decide), hpres mk94BParW (by decide), hpres mk94B0W (by decide)]
          rw [hidx_eq, hpres mk94AccW (by decide)] at hSt0 hSt1
          by_cases hr0 : r.val = 2 * k
          · have hr_eq : r = ⟨2 * k, by omega⟩ := Fin.ext hr0
            have hb0_out : ¬(196 ≤ (mk94Bank36W ⟨2 * k, by omega⟩).val ∧
                (mk94Bank36W ⟨2 * k, by omega⟩).val < 196 + 2 * k) := by
              change ¬(196 ≤ 196 + 2 * k ∧ 196 + 2 * k < 196 + 2 * k); omega
            rw [hr_eq, hSt0, hγ1, hOutPre γ hγ.2.2 _ hb0_out]
          · have hr_eq : r = ⟨2 * k + 1, by omega⟩ := Fin.ext (by dsimp; omega)
            have hb1_out : ¬(196 ≤ (mk94Bank36W ⟨2 * k + 1, by omega⟩).val ∧
                (mk94Bank36W ⟨2 * k + 1, by omega⟩).val < 196 + 2 * k) := by
              change ¬(196 ≤ 196 + (2 * k + 1) ∧ 196 + (2 * k + 1) < 196 + 2 * k); omega
            rw [hr_eq, hSt1, hγ1, hOutPre γ hγ.2.2 _ hb1_out]

/-- `54`-`TempAnd` (`216 T`) 2-bit PairMux loading `bank36` using `3` clean scratch wires
  `[265..268)`. -/
def mk94LoadPairMux (tTab : Fin 256 → ℕ) : TempPhaseProg 268 := mk94SeqPairMux tTab 18 le_rfl

theorem mk94LoadPairMux_spec (tTab : Fin 256 → ℕ) :
    (mk94LoadPairMux tTab).countTempAnd = 54 ∧
    ValidCleanRem 268 3 (mk94LoadPairMux tTab) ∧
    (∀ γ, (mk94LoadPairMux tTab).evalSign γ = 0) ∧
    (∀ γ : BitAssignment 268, cleanRem 268 3 γ →
      ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) →
        (mk94LoadPairMux tTab).evalBits γ q = γ q) ∧
    (∀ γ : BitAssignment 268, mk94InvU54 γ →
      mk94InvU54 ((mk94LoadPairMux tTab).evalBits γ) ∧
      let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
      let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
      ∀ r : Fin 36, (mk94LoadPairMux tTab).evalBits γ (mk94Bank36W r) =
        γ (mk94Bank36W r) + γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val)) := by
  obtain ⟨hCnt, hVal, hSign, hOut, hBank⟩ := mk94SeqPairMux_spec tTab 18 le_rfl
  refine ⟨hCnt, hVal, hSign, fun γ hγ q hq ↦ hOut γ hγ q (by omega), fun γ hγ ↦ ⟨?_, fun r ↦ ?_⟩⟩
  · exact mk94InvU54_congr_bank (fun q hq ↦ hOut γ hγ.2.2 q (by omega)) hγ
  · exact hBank γ hγ r (by omega)

theorem mk94U54ByP_ne_sel (p : Fin 54) :
    mk94B0W ≠ mk94U54ByP p ∧ mk94B1W ≠ mk94U54ByP p ∧ mk94W11W ≠ mk94U54ByP p := by
  revert p; decide

/-- Per-leaf `Z`/`CZ` phase fixup on `mk94U54ByP p` (`0` `.T`, `0` `.TOFF`). -/
def mk94FixU54Step {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool)
    (rMK : QRegister 268 n) (p : Fin 54) : Circuit n :=
  let m00 := mk36MaskBit36 tTab g 0 p.val 0
  let m01 := mk36MaskBit36 tTab g 0 p.val 1
  let m10 := mk36MaskBit36 tTab g 1 p.val 0
  let m11 := mk36MaskBit36 tTab g 1 p.val 1
  let wU := rMK (mk94U54ByP p)
  (fmkOptZ m00 wU ;;ᶜ
    fmkOptCZ (m00 + m01) (rMK mk94B0W) wU (rMK.wires.injective.ne (mk94U54ByP_ne_sel p).1)) ;;ᶜ
  (fmkOptCZ (m00 + m10) (rMK mk94B1W) wU (rMK.wires.injective.ne (mk94U54ByP_ne_sel p).2.1) ;;ᶜ
    fmkOptCZ (m00 + m01 + m10 + m11) (rMK mk94W11W) wU
      (rMK.wires.injective.ne (mk94U54ByP_ne_sel p).2.2))

open Classical in
theorem mk94FixU54Step_count_t {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool)
    (rMK : QRegister 268 n) (p : Fin 54) :
    (mk94FixU54Step tTab g rMK p).count PrimitiveGate.T = 0 := by
  dsimp [mk94FixU54Step, fmkOptZ, fmkOptCZ]; repeat' split_ifs <;> simp

open Classical in
theorem mk94FixU54Step_count_toff {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool)
    (rMK : QRegister 268 n) (p : Fin 54) :
    (mk94FixU54Step tTab g rMK p).count PrimitiveGate.TOFF = 0 := by
  dsimp [mk94FixU54Step, fmkOptZ, fmkOptCZ]; repeat' split_ifs <;> simp

/-- Full `54`-leaf `0`-`T` diagonal phase fixup for Passes 0 and 1. -/
def mk94FixU54Circuit {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool) (rMK : QRegister 268 n)
    : Circuit n := fmkSeqFin 54 (mk94FixU54Step tTab g rMK)

theorem mk94FixU54Circuit_count_t {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool)
    (rMK : QRegister 268 n) : (mk94FixU54Circuit tTab g rMK).count PrimitiveGate.T = 0 :=
    fmkSeqFin_count_eq_zero PrimitiveGate.T 54 _ (mk94FixU54Step_count_t tTab g rMK)

theorem mk94FixU54Circuit_count_toff {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool)
    (rMK : QRegister 268 n) : (mk94FixU54Circuit tTab g rMK).count PrimitiveGate.TOFF = 0 :=
    fmkSeqFin_count_eq_zero PrimitiveGate.TOFF 54 _ (mk94FixU54Step_count_toff tTab g rMK)

theorem ket_mk94FixU54Step {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool)
    (rMK : QRegister 268 n) (β : BitAssignment n)
    (hw11 : β (rMK mk94W11W) = β (rMK mk94B0W) * β (rMK mk94B1W)) (p : Fin 54) :
    let γ : BitAssignment 268 := fun q ↦ β (rMK q)
    (mk94FixU54Step tTab g rMK p).eval.1.mulVec (ket β) =
      bitSign (mk36MaskBit36 tTab g (γ mk94B1W).val p.val (γ mk94B0W).val * γ (mk94U54ByP p)) •
        ket β := by
  intro γ
  dsimp only [mk94FixU54Step]
  rw [ket_fmkDiag4 _ _ _ _ β
    (ket_fmkOptZ _ _ β) (ket_fmkOptCZ _ _ _ _ β)
    (ket_fmkOptCZ _ _ _ _ β) (ket_fmkOptCZ _ _ _ _ β)]
  refine fmkBitSign_smul_congr ?_ _
  have hmux := mk94FourWayMux_eq (γ mk94B0W) (γ mk94B1W)
    (fun b1 b0 ↦ mk36MaskBit36 tTab g b1 p.val b0)
  rw [← hmux]
  dsimp only [γ]
  rw [hw11]
  ring

attribute [local irreducible] mk94FixU54Step

open Classical in
theorem ket_mk94FixU54Circuit {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool)
    (rMK : QRegister 268 n) (β : BitAssignment n)
    (hγ : mk94InvU54 (fun q ↦ β (rMK q))) :
    let γ : BitAssignment 268 := fun q ↦ β (rMK q)
    let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
    let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
    (mk94FixU54Circuit tTab g rMK).eval.1.mulVec (ket β) =
      bitSign (∑ r : Fin 36, if g r then γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val) else 0) •
        ket β := by
  intro γ pAct idx
  change mk94InvU54 γ at hγ
  unfold mk94FixU54Circuit
  rw [ket_fmkSeqFin β 54 (mk94FixU54Step tTab g rMK) _
    (ket_mk94FixU54Step tTab g rMK β hγ.2.1)]
  refine fmkBitSign_smul_congr ?_ _
  have hpAct_lt : pAct < 54 := by
    have := s3NucleusQ27_lt (fun i ↦ γ (mk94U16W i))
    have := ZMod.val_lt (γ mk94BParW)
    dsimp [pAct]; omega
  let pFin : Fin 54 := ⟨pAct, hpAct_lt⟩
  have hsum : (∑ p : Fin 54,
      mk36MaskBit36 tTab g (γ mk94B1W).val p.val (γ mk94B0W).val * γ (mk94U54ByP p)) =
      mk36MaskBit36 tTab g (γ mk94B1W).val pAct (γ mk94B0W).val * γ mk94AccW := by
    rw [Finset.sum_eq_single pFin]
    · rw [mk94InvU54_byP hγ pFin, ite_eq_left (rfl : pFin.val = pAct), mul_one]
    · intro p _ hp
      rw [mk94InvU54_byP hγ p, ite_eq_right (fun h ↦ hp (Fin.ext h)), mul_zero, mul_zero]
    · intro hp; exact absurd (Finset.mem_univ pFin) hp
  rw [hsum]
  dsimp only [mk36MaskBit36, idx]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  cases g r <;> simp [mul_comm]



def mk94SplitXorSum {M : ℕ} :
    (N : ℕ) → (src : Fin N → Wire M) → (mask : Fin N → ZMod 2) → (dst : Wire M) →
    (∀ i, src i ≠ dst) → Mk94SplitProg M
  | 0, _, _, _, _ => .id
  | k + 1, src, mask, dst, hne =>
      .seq
        (mk94SplitXorSum k (fun i ↦ src i.castSucc) (fun i ↦ mask i.castSucc) dst
          (fun i ↦ hne i.castSucc))
        (if mask (Fin.last k) = 1 then .cnot (src (Fin.last k)) dst (hne (Fin.last k)) else .id)




attribute [local irreducible] mk94SplitXorSum

def mk94FF_SA : Wire 268 := ⟨234, by decide⟩
def mk94FF_SB : Wire 268 := ⟨235, by decide⟩

def mk94SplitLoadScr18 (sel : Wire 268) (lin : Fin 18 → ZMod 2) (dst : Wire 268)
    (hsel : sel.val < 232) (hdst : 232 ≤ dst.val) : Mk94SplitProg 268 :=
  .seq (.cnot sel dst (wire_ne_of_lt (by omega)))
    (mk94SplitXorSum 18 mk94U18W lin dst
      (fun i ↦ wire_ne_of_lt (by dsimp [mk94U18W]; omega)))


def mk94SplitPrepPair18 (selA selB : Wire 268) (linA linB : Fin 18 → ZMod 2)
    (wp : Wire 268) (hselA : selA.val < 232) (hselB : selB.val < 232)
    (hwp : 236 ≤ wp.val) : Mk94SplitProg 268 :=
  let loadAB : Mk94SplitProg 268 :=
    .seq (mk94SplitLoadScr18 selA linA mk94FF_SA hselA (by decide))
      (mk94SplitLoadScr18 selB linB mk94FF_SB hselB (by decide))
  .seq loadAB
    (.seq (.tempAnd mk94FF_SA mk94FF_SB wp (by decide)
        (wire_ne_of_lt (by dsimp [mk94FF_SA]; omega))
        (wire_ne_of_lt (by dsimp [mk94FF_SB]; omega)))
      loadAB)


attribute [local irreducible] mk94SplitPrepPair18

/-- Base 4-way mask bit for `t2 : Fin 3`, `i : Fin 18`, and `(b1, b0)`. -/
def mk94FFMask (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool) (t2 : Fin 3) (i : Fin 18) (b1 b0 : ℕ)
    : ZMod 2 := mk36MaskBit36 tTab g b1 (mk94POrig i t2).val b0



















theorem mk94U18W_ne_sel (p18 : Fin 18) :
    mk94B0W ≠ mk94U18W p18 ∧ mk94B1W ≠ mk94U18W p18 ∧ mk94W11W ≠ mk94U18W p18 := by
  revert p18; decide

def mk94FixBase18Step {n : ℕ} (tTab : Fin 256 → ℕ) (g : Fin 36 → Bool)
    (rMK : QRegister 268 n) (p18 : Fin 18) : Circuit n :=
  let m00 := mk94FFMask tTab g 0 p18 0 0
  let m01 := mk94FFMask tTab g 0 p18 0 1
  let m10 := mk94FFMask tTab g 0 p18 1 0
  let m11 := mk94FFMask tTab g 0 p18 1 1
  let wU := rMK (mk94U18W p18)
  (fmkOptZ m00 wU ;;ᶜ
    fmkOptCZ (m00 + m01) (rMK mk94B0W) wU (rMK.wires.injective.ne (mk94U18W_ne_sel p18).1)) ;;ᶜ
  (fmkOptCZ (m00 + m10) (rMK mk94B1W) wU (rMK.wires.injective.ne (mk94U18W_ne_sel p18).2.1) ;;ᶜ
    fmkOptCZ (m00 + m01 + m10 + m11) (rMK mk94W11W) wU
      (rMK.wires.injective.ne (mk94U18W_ne_sel p18).2.2))





attribute [local irreducible] mk94FixBase18Step














theorem mk94DynCount_seq {Var : Type} {n k : ℕ}
    (d₁ d₂ : DynamicCircuit Var n) (g : PrimitiveGate k) :
    (DynamicCircuit.seq d₁ d₂).count g = d₁.count g + d₂.count g := rfl

/- ## Section 5: Asymmetric Streaming Uncompute & Full `5,116-T` `dMidKick216_36_94w` Assembly -/

section Stream_Mk94

open HermitianMat
open MeasureBranchHadamardSem
  (sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf projOutcomeAll branchKrausUnitary
   branchKrausUnitary_eq_mul_projOutcomeAll wp_measureAndBranchSeq_update_self
   wp_measureAndBranchSeq_dynamic zeroSynd_writeSynd_of_zero syndSign_mul_self
   ket_xReset_projOutcome_hadamardAll)
open scoped ComplexOrder MatrixOrder

open Classical in
/-- Asymmetric-projector X-basis syndrome uncomputation allowing `cBody` to transition the
non-bank scratch invariant from `P_scrIn` (`cleanScrIn`) to `P_scrOut` (`cleanScrOut`). -/
theorem mk94StreamingUncompute_asym
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (m : ℕ)
    (qs : Fin m → Wire n) (hqs : Function.Injective qs)
    (P_scrIn P_scrOut : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (cleanScrIn cleanScrOut : BitAssignment n → Prop)
    (hPsIn_herm : P_scrInᴴ = P_scrIn)
    (hPsIn_ket : ∀ β : BitAssignment n, P_scrIn.mulVec (ket β) = if cleanScrIn β then ket β else 0)
    (hPsOut_herm : P_scrOutᴴ = P_scrOut)
    (hPsOut_ket : ∀ β : BitAssignment n,
      P_scrOut.mulVec (ket β) = if cleanScrOut β then ket β else 0)
    (hCleanOut_upd : ∀ (r : Fin m) (b : ZMod 2) (β : BitAssignment n),
      cleanScrOut (Function.update β (qs r) b) ↔ cleanScrOut β)
    (cBody : DynamicCircuit Var n) (U_body U_target : Unitary (2 ^ n))
    (fixupPhase : (Fin m → Bool) → DynamicCircuit Var n)
    (U_phase : (Fin m → Bool) → Unitary (2 ^ n))
    (syndOf : BitAssignment n → (Fin m → Bool))
    (outOf : BitAssignment n → BitAssignment n)
    (hBody : RealizesCleanUnitary v P_scrIn cBody U_body)
    (hFix : ∀ g, RealizesCleanUnitary v P_scrOut (fixupPhase g) (U_phase g))
    (hOut_zero : ∀ β : BitAssignment n,
      (∀ r : Fin m, β (qs r) = 0) → cleanScrIn β → ∀ r : Fin m, outOf β (qs r) = 0)
    (hOut_clean : ∀ β : BitAssignment n,
      (∀ r : Fin m, β (qs r) = 0) → cleanScrIn β → cleanScrOut (outOf β))
    (hBody_ket : ∀ β : BitAssignment n,
      (∀ r : Fin m, β (qs r) = 0) → cleanScrIn β →
      U_body.1.mulVec (ket β) = ket (writeSynd m qs (syndOf β) (outOf β)))
    (hPhase_ket : ∀ (g : Fin m → Bool) (β : BitAssignment n),
      (∀ r : Fin m, β (qs r) = 0) → cleanScrIn β →
      (U_phase g).1.mulVec (ket (outOf β)) =
        syndSign m qs g (writeSynd m qs (syndOf β) (outOf β)) • ket (outOf β))
    (hTarget_ket : ∀ β : BitAssignment n,
      (∀ r : Fin m, β (qs r) = 0) → cleanScrIn β →
      U_target.1.mulVec (ket β) = ket (outOf β)) :
    RealizesCleanUnitary v (projZeroAll m qs * P_scrIn)
      (.seq cBody
        (.seq (.circuit (hadamardAll m qs))
          (measureAndBranchSeq v m (fun r ↦ QRegister.singleton (qs r))
            (fun g ↦ .seq (.circuit (xReset m qs g)) (fixupPhase g)))))
      U_target := by
  let P_all := projZeroAll m qs * P_scrIn
  let branchProg : (Fin m → Bool) → DynamicCircuit Var n :=
    fun g ↦ .seq (.circuit (xReset m qs g)) (fixupPhase g)
  let cUncomp : DynamicCircuit Var n := .seq (.circuit (hadamardAll m qs))
      (measureAndBranchSeq v m (fun r ↦ QRegister.singleton (qs r)) branchProg)
  have hPsIn_idem : P_scrIn * P_scrIn = P_scrIn := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, hPsIn_ket]
    by_cases hc : cleanScrIn β
    · rw [ite_eq_left hc, hPsIn_ket, ite_eq_left hc]
    · rw [ite_eq_right hc, Matrix.mulVec_zero]
  have hPsOut_idem : P_scrOut * P_scrOut = P_scrOut := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, hPsOut_ket]
    by_cases hc : cleanScrOut β
    · rw [ite_eq_left hc, hPsOut_ket, ite_eq_left hc]
    · rw [ite_eq_right hc, Matrix.mulVec_zero]
  have hPall_herm : P_allᴴ = P_all := by
    dsimp [P_all]
    rw [conjTranspose_mul, projZeroAll_conjTranspose, hPsIn_herm]
    exact (fmkProjZeroAll_comm_diag hPsIn_ket m qs).symm
  have hBranch : ∀ g, RealizesCleanUnitary v P_scrOut (branchProg g)
      (U_phase g * (xReset m qs g).eval) := by
    intro g
    refine RealizesCleanUnitary.seq hPsOut_herm
      (RealizesCleanUnitary.circuit v P_scrOut (xReset m qs g)) (hFix g) ?_
    rw [← Matrix.mul_assoc, ← fmkXReset_comm_diag hPsOut_ket m qs g hCleanOut_upd,
      Matrix.mul_assoc, hPsOut_idem]
  have hUncomp_inv : ∀ (Ψ : CQAssertionCompat Var (2 ^ n)),
      (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
      ∀ σ val, wp cUncomp.compile Ψ (Function.update σ v val) = wp cUncomp.compile Ψ σ := by
    intro Ψ hΨ σ val
    simp only [cUncomp, DynamicCircuit.compile_seq, wp_qSeq]
    exact (RealizesCleanUnitary.circuit v P_scrOut (hadamardAll m qs)).1 _
      (wp_measureAndBranchSeq_update_self v m _ branchProg (fun g ↦ (hBranch g).1) Ψ hΨ) σ val
  have hPscr_Pall : P_all * P_scrIn = P_all := by
    dsimp [P_all]; rw [Matrix.mul_assoc, hPsIn_idem]
  have hBody_clean_scr : P_scrOut * (U_body.1 * P_all) = U_body.1 * P_all := by
    apply matrix_ext_ket; intro β
    simp only [P_all, mul_mulVec_prog, hPsIn_ket]
    by_cases hs : cleanScrIn β
    · simp only [hs, ↓reduceIte, ket_projZeroAll]
      by_cases hy : ∀ r : Fin m, β (qs r) = 0
      · have hpres : cleanScrOut (writeSynd m qs (syndOf β) (outOf β)) :=
          fmkWriteSynd_pres_clean m qs (syndOf β) (outOf β) hCleanOut_upd (hOut_clean β hy hs)
        simp only [hy, imp_true_iff, ↓reduceIte, hBody_ket β hy hs, hPsOut_ket, hpres]
      · simp only [hy, ↓reduceIte, Matrix.mulVec_zero]
    · simp only [hs, ↓reduceIte, Matrix.mulVec_zero]
  have hBody_clean_adj : P_all * U_body.1ᴴ * P_scrOut = P_all * U_body.1ᴴ := by
    have h := congrArg conjTranspose hBody_clean_scr
    simpa [conjTranspose_mul, hPsOut_herm, hPall_herm, ← Matrix.mul_assoc] using h
  have hKraus : ∀ g : Fin m → Bool, branchKrausUnitary m qs
      (fun g ↦ U_phase g * (xReset m qs g).eval) g * (hadamardAll m qs).eval.1 * U_body.1 *
      P_all = ((sqrtHalf : ℂ) ^ m) • (U_target.1 * P_all) := by
    intro g
    apply matrix_ext_ket; intro β
    rw [branchKrausUnitary_eq_mul_projOutcomeAll, Submonoid.coe_mul]
    by_cases hscr : cleanScrIn β
    · by_cases hsynd : ∀ r : Fin m, β (qs r) = 0
      · have hP : P_all.mulVec (ket β) = ket β := by
          simp only [P_all, mul_mulVec_prog, hPsIn_ket, ket_projZeroAll, hscr, hsynd,
            imp_true_iff, ↓reduceIte]
        have h1 : U_body.1.mulVec (ket β) = ket (writeSynd m qs (syndOf β) (outOf β)) :=
          hBody_ket β hsynd hscr
        have h2 : ((xReset m qs g).eval.1 * projOutcomeAll m qs g * (hadamardAll m
            qs).eval.1).mulVec (ket (writeSynd m qs (syndOf β) (outOf β))) = ((sqrtHalf : ℂ) ^
            m * syndSign m qs g (writeSynd m qs (syndOf β) (outOf β))) • ket (outOf β) := by
          rw [ket_xReset_projOutcome_hadamardAll m qs hqs g,
            zeroSynd_writeSynd_of_zero m qs hqs (syndOf β) (outOf β) (hOut_zero β hsynd hscr)]
        have h3 : (U_phase g).1.mulVec (ket (outOf β)) = syndSign m qs g
            (writeSynd m qs (syndOf β) (outOf β)) • ket (outOf β) := hPhase_ket g β hsynd hscr
        have h4 : U_target.1.mulVec (ket β) = ket (outOf β) := hTarget_ket β hsynd hscr
        have hsq := syndSign_mul_self m qs g (writeSynd m qs (syndOf β) (outOf β))
        let K := (xReset m qs g).eval.1 * projOutcomeAll m qs g * (hadamardAll m qs).eval.1
        have split_lhs : ((U_phase g).1 * (xReset m qs g).eval.1 * projOutcomeAll m qs g *
            (hadamardAll m qs).eval.1 * U_body.1 * P_all).mulVec (ket β) =
            (U_phase g).1.mulVec (K.mulVec (U_body.1.mulVec (P_all.mulVec (ket β)))) := by
          have hm : (U_phase g).1 * (xReset m qs g).eval.1 * projOutcomeAll m qs g *
              (hadamardAll m qs).eval.1 * U_body.1 * P_all = (U_phase g).1 *
              (K * (U_body.1 * P_all)) := by
            dsimp [K]; simp only [Matrix.mul_assoc]
          rw [hm, mul_mulVec_prog (U_phase g).1, mul_mulVec_prog K, mul_mulVec_prog U_body.1]
        rw [split_lhs, hP, h1, h2, Matrix.mulVec_smul, h3, smul_smul,
          Matrix.smul_mulVec, mul_mulVec_prog, hP, h4]
        congr 1
        calc ((sqrtHalf : ℂ) ^ m * syndSign m qs g (writeSynd m qs (syndOf β) (outOf β))) *
                syndSign m qs g (writeSynd m qs (syndOf β) (outOf β))
            = (sqrtHalf : ℂ) ^ m *
                (syndSign m qs g (writeSynd m qs (syndOf β) (outOf β)) *
                  syndSign m qs g (writeSynd m qs (syndOf β) (outOf β))) := by ring
          _ = (sqrtHalf : ℂ) ^ m := by rw [hsq, mul_one]
      · simp only [P_all, Matrix.smul_mulVec, mul_mulVec_prog, hPsIn_ket, ket_projZeroAll,
          hscr, hsynd, ↓reduceIte, Matrix.mulVec_zero, smul_zero]
    · simp only [P_all, Matrix.smul_mulVec, mul_mulVec_prog, hPsIn_ket, hscr, ↓reduceIte,
        Matrix.mulVec_zero, smul_zero]
  refine ⟨fun Ψ hΨ σ val ↦ ?_, fun Θ hΘ σ ↦ ?_⟩
  · simp only [DynamicCircuit.compile_seq, wp_qSeq]
    exact hBody.1 (wp cUncomp.compile Ψ) (hUncomp_inv Ψ hΨ) σ val
  · have hstep1 : ((wp cBody.compile (wp cUncomp.compile Θ) σ).1).conj P_all =
      (((wp cUncomp.compile Θ σ).1).conj P_scrOut).conj (P_all * U_body.1ᴴ) := by
      calc ((wp cBody.compile (wp cUncomp.compile Θ) σ).1).conj P_all
          = (((wp cBody.compile (wp cUncomp.compile Θ) σ).1).conj P_scrIn).conj P_all := by
              rw [conj_conj, hPscr_Pall]
        _ = (((wpQAssignCompat U_body (wp cUncomp.compile Θ) σ).1).conj P_scrIn).conj P_all := by
              rw [hBody.2 (wp cUncomp.compile Θ) (hUncomp_inv Θ hΘ) σ]
        _ = ((wp cUncomp.compile Θ σ).1).conj (P_all * U_body.1ᴴ) := by
              simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
                Matrix.star_eq_conjTranspose, conj_conj]
              rw [← Matrix.mul_assoc P_all P_scrIn U_body.1ᴴ, hPscr_Pall]
        _ = (((wp cUncomp.compile Θ σ).1).conj P_scrOut).conj (P_all * U_body.1ᴴ) := by
              rw [conj_conj, hBody_clean_adj]
    have hstep2 : ((wp cUncomp.compile Θ σ).1).conj P_scrOut = ∑ g : Fin m → Bool, ((Θ
        σ).1.conj (branchKrausUnitary m qs (fun g ↦ U_phase g * (xReset m qs g).eval) g *
        (hadamardAll m qs).eval.1)ᴴ).conj P_scrOut := by
      have hH_adj : P_scrOut * (hadamardAll m qs).eval.1ᴴ =
          (hadamardAll m qs).eval.1ᴴ * P_scrOut := by
        have h := congrArg conjTranspose (fmkHadamardAll_comm_diag hPsOut_ket m qs hCleanOut_upd)
        simpa [conjTranspose_mul, hPsOut_herm] using h
      simp only [cUncomp, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit,
        wp_qSeq, wp_circuit_compile_compat, wpQAssignCompat,
        qAssignObsMap, Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        conj_conj, hH_adj]
      rw [← conj_conj,
        wp_measureAndBranchSeq_dynamic v P_scrOut hPsOut_herm Θ hΘ m qs branchProg
          (fun g ↦ U_phase g * (xReset m qs g).eval)
          (fun r o ↦ fmkProj_comm_diag hPsOut_ket (qs r) o)
          hBranch σ,
        map_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [conj_conj, ← hH_adj, conj_conj, Matrix.mul_assoc, ← conjTranspose_mul]
    change ((wp cBody.compile (wp cUncomp.compile Θ) σ).1).conj P_all =
      ((wpQAssignCompat U_target Θ σ).1).conj P_all
    rw [hstep1, hstep2, map_sum]
    have hterm : ∀ g : Fin m → Bool, ((((Θ σ).1.conj (branchKrausUnitary m qs (fun g ↦ U_phase
        g * (xReset m qs g).eval) g * (hadamardAll m qs).eval.1)ᴴ).conj P_scrOut).conj (P_all
        * U_body.1ᴴ)) = ((Θ σ).1.conj (U_target.1 * P_all)ᴴ).conj
        (((sqrtHalf : ℂ) ^ m) • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) := by
      intro g
      rw [conj_conj, conj_conj, conj_conj]
      suffices hM :
          P_all * U_body.1ᴴ * P_scrOut *
              (branchKrausUnitary m qs (fun g ↦ U_phase g * (xReset m qs g).eval) g *
                (hadamardAll m qs).eval.1)ᴴ =
            (((sqrtHalf : ℂ) ^ m) • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) *
              (U_target.1 * P_all)ᴴ by
        rw [hM]
      calc P_all * U_body.1ᴴ * P_scrOut *
              (branchKrausUnitary m qs (fun g ↦ U_phase g * (xReset m qs g).eval) g *
                (hadamardAll m qs).eval.1)ᴴ
          = (branchKrausUnitary m qs (fun g ↦ U_phase g * (xReset m qs g).eval) g *
                (hadamardAll m qs).eval.1 * U_body.1 * P_all)ᴴ := by
              rw [hBody_clean_adj]
              simp only [conjTranspose_mul, hPall_herm, Matrix.mul_assoc]
        _ = (((sqrtHalf : ℂ) ^ m) • (U_target.1 * P_all))ᴴ := by rw [hKraus g]
        _ = (((sqrtHalf : ℂ) ^ m) • (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) *
              (U_target.1 * P_all)ᴴ := by
              rw [conjTranspose_smul, star_pow, star_sqrtHalf, Matrix.smul_mul, Matrix.one_mul]
    simp_rw [hterm, conj_conj, Matrix.smul_mul, Matrix.one_mul, conjTranspose_mul, hPall_herm]
    simp only [wpQAssignCompat, qAssignObsMap, Observable.conj_coe, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conj_conj]
    have hhalf : ((2 ^ m : ℕ) : ℂ) * ((sqrtHalf : ℂ) ^ m * (sqrtHalf : ℂ) ^ m) = 1 := by
      rw [← mul_pow, sqrtHalf_mul_sqrtHalf, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
      norm_num
    have hsum_mat : ∀ (s : Finset (Fin m → Bool)) (H : HermitianMat (Fin (2 ^ n)) ℂ),
        (∑ _ ∈ s, H).mat = (s.card : ℂ) • H.mat := fun s H ↦ by
      refine Finset.induction_on s (by simp) fun a s ha ih ↦ ?_
      have h1 : (∑ _ ∈ insert a s, H).mat = H.mat + (∑ _ ∈ s, H).mat := by
        rw [Finset.sum_insert ha]; rfl
      have h2 : (insert a s).card = s.card + 1 := by simp [ha]
      rw [h1, ih, h2, Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_comm]
    have hcard : ((Finset.univ : Finset (Fin m → Bool)).card : ℂ) = ((2 ^ m : ℕ) : ℂ) := by
      simp
    ext1
    rw [hsum_mat, hcard, HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat,
      conjTranspose_smul, star_pow, star_sqrtHalf]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hhalf, one_smul]

end Stream_Mk94

theorem mk94ActP18_congr_sel {γ₁ γ₂ : BitAssignment 268}
    (h : ∀ q : Wire 268, q.val < 107 → γ₁ q = γ₂ q) : mk94ActP18 γ₁ = mk94ActP18 γ₂ := by
  dsimp only [mk94ActP18]
  rw [h mk94A0W (by decide), h mk94C0W (by decide), h mk94A1W (by decide),
    h mk94C1W (by decide), h mk94BParW (by decide)]

theorem mk94InvU18_congr_cat_bank {γ₁ γ₂ : BitAssignment 268} (h : ∀ q : Wire 268, ¬(107 ≤
    q.val ∧ q.val < 149) → ¬(196 ≤ q.val ∧ q.val < 232) → γ₁ q = γ₂ q) (h₂ : mk94InvU18 γ₂) :
    mk94InvU18 γ₁ := by
  have h107 : ∀ q : Wire 268, q.val < 107 → γ₁ q = γ₂ q :=
    fun q hq ↦ h q (by omega) (by omega)
  refine ⟨fun p18 ↦ ?_, ?_, ?_, ?_, ?_, fun w hw ↦ ?_⟩
  · rw [h (mk94U18W p18) (by dsimp [mk94U18W]; omega) (by dsimp [mk94U18W]; omega),
      h mk94AccW (by decide) (by decide), mk94ActP18_congr_sel h107]
    exact h₂.1 p18
  · rw [h mk94W11W (by decide) (by decide), h mk94B0W (by decide) (by decide),
      h mk94B1W (by decide) (by decide)]
    exact h₂.2.1
  · exact (h ⟨193, by decide⟩ (by decide) (by decide)).trans h₂.2.2.1
  · exact (h ⟨194, by decide⟩ (by decide) (by decide)).trans h₂.2.2.2.1
  · exact (h ⟨195, by decide⟩ (by decide) (by decide)).trans h₂.2.2.2.2.1
  · exact (h w (by omega) (by omega)).trans (h₂.2.2.2.2.2 w hw)

theorem mk94InvMidTop3_congr_cat {γ₁ γ₂ : BitAssignment 268}
    (h : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ₁ q = γ₂ q)
    (h₂ : mk94InvMidTop3 γ₂) : mk94InvMidTop3 γ₁ := by
  have h107 : ∀ q : Wire 268, q.val < 107 → γ₁ q = γ₂ q := fun q hq ↦ h q (by omega)
  refine ⟨fun t2 ↦ ?_, ?_, ?_, fun j ↦ ?_, ?_, fun w hw ↦ ?_⟩
  · have ht2 : ¬(107 ≤ (mk94U54Wire 0 t2).val ∧ (mk94U54Wire 0 t2).val < 149) :=
      ((show ∀ t : Fin 3, ¬(107 ≤ (mk94U54Wire 0 t).val ∧ (mk94U54Wire 0 t).val < 149)
        by decide) t2)
    rw [h _ ht2, h mk94AccW (by decide), mk94ActP18_congr_sel h107,
      h mk94A2W (by decide), h mk94C2W (by decide)]
    exact h₂.1 t2
  · rw [h ⟨175, by decide⟩ (by decide), h mk94AccW (by decide),
      mk94ActP18_congr_sel h107, h mk94C2W (by decide)]
    exact h₂.2.1
  · rw [h ⟨195, by decide⟩ (by decide), h mk94AccW (by decide),
      mk94ActP18_congr_sel h107, h mk94C2W (by decide)]
    exact h₂.2.2.1
  · rw [h ⟨176 + j.val, by omega⟩ (by dsimp; omega), h mk94AccW (by decide),
      mk94ActP18_congr_sel h107]
    exact h₂.2.2.2.1 j
  · rw [h mk94W11W (by decide), h mk94B0W (by decide), h mk94B1W (by decide)]
    exact h₂.2.2.2.2.1
  · exact (h w (by omega)).trans (h₂.2.2.2.2.2 w hw)

theorem mk94InvU18_ext_nonBank {γ₁ γ₂ : BitAssignment 268}
    (h₁ : mk94InvU18 γ₁) (h₂ : mk94InvU18 γ₂)
    (hlt : ∀ q : Wire 268, q.val < 174 → γ₁ q = γ₂ q) :
    ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ₁ q = γ₂ q := fun q hq ↦ by
  by_cases h1 : q.val < 174
  · exact hlt q h1
  · by_cases h2 : q.val < 192
    · have hw : q = mk94U18W ⟨q.val - 174, by omega⟩ := Fin.ext (by dsimp [mk94U18W]; omega)
      rw [hw, h₁.1, h₂.1, hlt mk94AccW (by decide), mk94ActP18_congr hlt]
    · by_cases h3 : q.val = 192
      · have hw : q = mk94W11W := Fin.ext h3
        rw [hw, h₁.2.1, h₂.2.1, hlt mk94B0W (by decide), hlt mk94B1W (by decide)]
      · by_cases h4 : q.val < 196
        · have hv193 : 193 ≤ q.val := by omega
          rcases q with ⟨v, hv⟩
          dsimp only at hv193 h4
          interval_cases v
          · exact h₁.2.2.1.trans h₂.2.2.1.symm
          · exact h₁.2.2.2.1.trans h₂.2.2.2.1.symm
          · exact h₁.2.2.2.2.1.trans h₂.2.2.2.2.1.symm
        · exact (h₁.2.2.2.2.2 q (by omega)).trans (h₂.2.2.2.2.2 q (by omega)).symm

theorem mk94Realizes_prog_diag {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rMK : QRegister 268 n) (p : TempPhaseProg 268) (rem : ℕ)
    (hrem : rem ≤ 268) (hValid : ValidCleanRem 268 rem p) (Inv : BitAssignment 268 → Prop)
    (hInvCl : ∀ γ, Inv γ → cleanRem 268 rem γ) : RealizesCleanUnitary v (p57DiagProj rMK Inv)
    ((p.onRegister rMK).toDyn v) (((p.onRegister rMK).toToffCircuit).eval) := by
  refine RealizesCleanUnitary.mono_proj (projZeroAll_conjTranspose rem _)
    (p57DiagProj_conjTranspose rMK Inv) ?_ (realizes_of_validCleanRem v rMK p rem hrem hValid)
  apply matrix_ext_ket; intro β
  rw [mul_mulVec_prog, ket_p57DiagProj]
  by_cases hi : Inv (fun idx ↦ β (rMK idx))
  · have hz : ∀ j : Fin rem, β (tailScr rMK rem hrem j) = 0 := fun j ↦ by
      have heq : tailScr rMK rem hrem j = rMK ⟨268 - rem + j.val, by omega⟩ :=
        congrArg rMK (Fin.ext rfl)
      rw [heq]
      exact hInvCl _ hi _ (by dsimp; omega)
    simp [hi, hz, ket_projZeroAll]
  · simp [hi]

theorem mk94WriteSynd_bank_eq {n : ℕ} (rMK : QRegister 268 n) (β : BitAssignment n)
    (γ_body γ_out : BitAssignment 268) (d : Fin 36 → ZMod 2) (hNon : ∀ q : Wire 268, ¬(196 ≤
    q.val ∧ q.val < 232) → γ_body q = γ_out q)
    (hBank : ∀ r : Fin 36, γ_body (mk94Bank36W r) = d r) : writeRegProg β rMK γ_body =
    writeSynd 36 (fun r ↦ rMK (mk94Bank36W r)) (fun r ↦ decide (d r = 1))
    (writeRegProg β rMK γ_out) := by
  let bankQs : Fin 36 → Wire n := fun r ↦ rMK (mk94Bank36W r)
  have hbank_inj : Function.Injective bankQs := rMK.wires.injective.comp mk94Bank36W_inj
  funext w
  by_cases hmem : w ∈ Set.range rMK.wires
  · obtain ⟨q, rfl⟩ := hmem
    by_cases hbq : 196 ≤ q.val ∧ q.val < 232
    · let r : Fin 36 := ⟨q.val - 196, by omega⟩
      have hq_eq : q = mk94Bank36W r := Fin.ext (by dsimp [mk94Bank36W, r]; omega)
      rw [hq_eq, writeRegProg_apply_reg, hBank r]
      change d r = writeSynd 36 bankQs (fun r' ↦ decide (d r' = 1))
        (writeRegProg β rMK γ_out) (bankQs r)
      rw [fmkWriteSynd_apply_mem 36 bankQs hbank_inj]
      rcases fmkBit_cases (d r) with hd | hd <;> simp [hd]
    · have hnot_b : ∀ r : Fin 36, rMK q ≠ bankQs r := fun r h ↦ hbq (by
        have hv := congrArg Fin.val (rMK.wires.injective h)
        dsimp [mk94Bank36W] at hv; omega)
      rw [writeSynd_apply_of_not_mem 36 bankQs _ _ _ hnot_b,
        writeRegProg_apply_reg, writeRegProg_apply_reg, hNon q hbq]
  · have hnot_b : ∀ r : Fin 36, w ≠ bankQs r := fun r h ↦ hmem ⟨mk94Bank36W r, h.symm⟩
    rw [writeSynd_apply_of_not_mem 36 bankQs _ _ _ hnot_b,
      writeRegProg_apply_of_not_mem _ _ _ _ hmem,
      writeRegProg_apply_of_not_mem _ _ _ _ hmem]

def mk94Pass01BodyBits (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268) :
    BitAssignment 268 := mk94SplitTop33.fwdBits ((mk94MulAxisFull36 w).evalBits
    (mk94SplitTop33.revBits ((mk94LoadPairMux tTab).evalBits γ)))

def mk94Pass01Bits (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268) : BitAssignment
    268 := (mk94LoadPairMux tTab).evalBits (mk94Pass01BodyBits w tTab γ)

private theorem mk94LoadBank_cancel (tTab : Fin 256 → ℕ) (γ ξ : BitAssignment 268)
    (hξ : mk94InvU54 ξ)
    (hd : ∀ r : Fin 36, ξ (mk94Bank36W r) = γ mk94AccW * fmkBitZ ((tTab (fmkIdx0 (γ mk94B1W).val
      (s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val)
      (γ mk94B0W).val)).testBit r.val))
    (hlt : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → ξ q = γ q)
    (r : Fin 36) : (mk94LoadPairMux tTab).evalBits ξ (mk94Bank36W r) = 0 := by
  have h := ((mk94LoadPairMux_spec tTab).2.2.2.2 ξ hξ).2 r
  have hu_eq : (fun i ↦ ξ (mk94U16W i)) = fun i ↦ γ (mk94U16W i) :=
    funext fun i ↦ hlt (mk94U16W i) (by dsimp [mk94U16W]; omega) (by dsimp [mk94U16W]; omega)
  rw [h, hd r, hu_eq, hlt mk94B1W (by decide) (by decide),
    hlt mk94BParW (by decide) (by decide), hlt mk94B0W (by decide) (by decide),
    hlt mk94AccW (by decide) (by decide)]
  exact mk94ZMod2_add_self _

private theorem mk94Cat42_mulAxis_mod (w : Fin 3) (γ γ1 γ2 γ_out : BitAssignment 268)
    (d : Fin 36 → ZMod 2) (hCl2 : cleanRem 268 (268 - 232) γ2)
    (h1_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ1 q = γ q)
    (h1_bank : ∀ r : Fin 36, γ1 (mk94Bank36W r) = d r)
    (hKeep2 : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ2 q = γ1 q)
    (hCatOut : ∀ m : Fin 42, γ_out (mk94Cat42W m) =
      (mk94MulAxisFull36 w).evalBits γ2 (mk94Cat42W m)) :
    let pNew0 : Fin 256 :=
      ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
    let pOld0 : Fin 256 :=
      ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
    ((bitsVal (fun m ↦ γ_out (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
        64 * ((twosComp8Int pNew0 - twosComp8Int pOld0) * (bitsVal d : ℤ))).emod (2 ^ 42 : ℤ) := by
  intro pNew0 pOld0
  have hEv := (mk94MulAxisFull36_spec w).2.2 γ2 hCl2
  dsimp only at hEv
  have hcat_out : (fun m : Fin 42 ↦ γ_out (mk94Cat42W m)) =
      fun m : Fin 42 ↦ (mk94MulAxisFull36 w).evalBits γ2 (mk94Cat42W m) := funext hCatOut
  have hcat_in : (fun m : Fin 42 ↦ γ2 (mk94Cat42W m)) = fun m : Fin 42 ↦ γ (mk94Cat42W m) :=
    funext fun m ↦ (hKeep2 (mk94Cat42W m) (Or.inl (by dsimp [mk94Cat42W]; omega))).trans
      (h1_non (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega))
  have hpN : (⟨bitsVal (fun b : Fin 8 ↦ γ2 ⟨150 + 8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 :=
    Fin.ext (congrArg bitsVal (funext fun b ↦
      (hKeep2 _ (Or.inl (by dsimp; omega))).trans (h1_non _ (by dsimp; omega))))
  have hpO : (⟨bitsVal (fun b : Fin 8 ↦ γ2 ⟨8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 :=
    Fin.ext (congrArg bitsVal (funext fun b ↦
      (hKeep2 _ (Or.inl (by dsimp; omega))).trans (h1_non _ (by dsimp; omega))))
  have hb2 : (fun m : Fin 36 ↦ γ2 (mk94Bank36W m)) = d :=
    funext fun m ↦ (hKeep2 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h1_bank m)
  rw [hcat_out, hEv, hcat_in, hpN, hpO, hb2]

theorem mk94Pass01Bits_spec (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268)
    (hU54 : mk94InvU54 γ) (hBankZ : ∀ r : Fin 36, γ (mk94Bank36W r) = 0) :
    let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
    let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
    let d : Fin 36 → ZMod 2 := fun r ↦ γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val)
    let γ_body := mk94Pass01BodyBits w tTab γ
    let γ_out := mk94Pass01Bits w tTab γ
    mk94InvU54 γ_out ∧
    (∀ r : Fin 36, γ_out (mk94Bank36W r) = 0) ∧
    (∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ_body q = γ_out q) ∧
    (∀ r : Fin 36, γ_body (mk94Bank36W r) = d r) ∧
    (∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_out q = γ q) ∧
    (let pNew0 : Fin 256 :=
       ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
     let pOld0 : Fin 256 :=
       ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
     ((bitsVal (fun m ↦ γ_out (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
       ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
         64 * ((twosComp8Int pNew0 - twosComp8Int pOld0) * (bitsVal d : ℤ))).emod (2 ^ 42 : ℤ)) :=
           by
  intro pAct idx d γ_body γ_out
  obtain ⟨_, _, _, hLOut, hLSpec⟩ := mk94LoadPairMux_spec tTab
  obtain ⟨_, hMMut, _⟩ := mk94MulAxisFull36_spec w
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  obtain ⟨hInv1, hLB1⟩ := hLSpec γ hU54
  have h1_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ1 q = γ q := hLOut γ hU54.2.2
  have h1_bank : ∀ r : Fin 36, γ1 (mk94Bank36W r) = d r := fun r ↦ by
    change (mk94LoadPairMux tTab).evalBits γ (mk94Bank36W r) = d r
    rw [hLB1 r, hBankZ r, zero_add]
  let γ2 := mk94SplitTop33.revBits γ1
  obtain ⟨hMid2_c, _, hRev2, hKeep2_c⟩ := mk94SplitTop33_rev_spec γ1 hInv1
  have hMid2 : mk94InvMidTop3 γ2 := by dsimp only [γ2]; rwa [hRev2]
  have hKeep2 : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ2 q = γ1 q :=
    fun q hq ↦ by dsimp only [γ2]; rw [hRev2]; exact hKeep2_c q hq
  let γ3 := (mk94MulAxisFull36 w).evalBits γ2
  have h3_non : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ3 q = γ2 q :=
    hMMut.2.2.2 γ2 hMid2.2.2.2.2.2
  have hMid3 : mk94InvMidTop3 γ3 := mk94InvMidTop3_congr_cat h3_non hMid2
  obtain ⟨hInv4, hKeep4⟩ := mk94SplitTop33_spec.2 γ3 hMid3
  change mk94InvU54 γ_body at hInv4
  change ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ_body q = γ3 q at hKeep4
  obtain ⟨hInv5, _⟩ := hLSpec γ_body hInv4
  change mk94InvU54 γ_out at hInv5
  have h5_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ_out q = γ_body q :=
    hLOut γ_body hInv4.2.2
  have hbody_bank : ∀ r : Fin 36, γ_body (mk94Bank36W r) = d r := fun r ↦ by
    have hr : 196 ≤ (mk94Bank36W r).val ∧ (mk94Bank36W r).val < 232 := by
      dsimp [mk94Bank36W]; omega
    exact (hKeep4 _ (Or.inr hr)).trans
      ((h3_non _ (by dsimp [mk94Bank36W]; omega)).trans
        ((hKeep2 _ (Or.inr hr)).trans (h1_bank r)))
  have hbody_lt : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_body q = γ q
      := fun q hlt hnc ↦ (hKeep4 q (Or.inl hlt)).trans ((h3_non q hnc).trans ((hKeep2 q
      (Or.inl hlt)).trans (h1_non q (by omega))))
  have hout_lt : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_out q = γ q :=
    fun q hlt hnc ↦ (h5_non q (by omega)).trans (hbody_lt q hlt hnc)
  have hout_bank := mk94LoadBank_cancel tTab γ γ_body hInv4 hbody_bank hbody_lt
  refine ⟨hInv5, hout_bank, fun q hq ↦ (h5_non q hq).symm, hbody_bank, hout_lt,
    mk94Cat42_mulAxis_mod w γ γ1 γ2 γ_out d hMid2.2.2.2.2.2 h1_non h1_bank hKeep2 fun m ↦
      (h5_non (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)).trans
        (hKeep4 (mk94Cat42W m) (Or.inl (by dsimp [mk94Cat42W]; omega)))⟩

noncomputable def mk94Body01U {n : ℕ} (rMK : QRegister 268 n) (w : Fin 3) (tTab : Fin 256 → ℕ)
    : Unitary (2 ^ n) := (mk94SplitTop33.fwdCircuit rMK).eval * ((((mk94MulAxisFull36
    w).onRegister rMK).toToffCircuit).eval * ((mk94SplitTop33.revCircuit rMK).eval *
    (((mk94LoadPairMux tTab).onRegister rMK).toToffCircuit).eval))

noncomputable def mk94Pass01U {n : ℕ} (rMK : QRegister 268 n) (w : Fin 3) (tTab : Fin 256 → ℕ)
    : Unitary (2 ^ n) := (((mk94LoadPairMux tTab).onRegister rMK).toToffCircuit).eval *
    mk94Body01U rMK w tTab

theorem ket_mk94Body01U {n : ℕ} [NeZero (2 ^ n)] (rMK : QRegister 268 n) (w : Fin 3)
    (tTab : Fin 256 → ℕ) (β : BitAssignment n) (hγ : mk94InvU54 (fun q ↦ β (rMK q))) :
    (mk94Body01U rMK w tTab).1.mulVec (ket β) = ket
    (writeRegProg β rMK (mk94Pass01BodyBits w tTab (fun q ↦ β (rMK q)))) := by
  let γ : BitAssignment 268 := fun q ↦ β (rMK q)
  change mk94InvU54 γ at hγ
  obtain ⟨_, _, hLSgn, _, hLSpec⟩ := mk94LoadPairMux_spec tTab
  obtain ⟨_, hMMut, _⟩ := mk94MulAxisFull36_spec w
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  have hInv1 : mk94InvU54 γ1 := (hLSpec γ hγ).1
  let γ2 := mk94SplitTop33.revBits γ1
  obtain ⟨hMid2_c, _, hRev2, _⟩ := mk94SplitTop33_rev_spec γ1 hInv1
  have hMid2 : mk94InvMidTop3 γ2 := by dsimp only [γ2]; rwa [hRev2]
  let γ3 := (mk94MulAxisFull36 w).evalBits γ2
  have hreg : ∀ (ξ : BitAssignment 268), (fun idx ↦ writeRegProg β rMK ξ (rMK idx)) = ξ :=
    fun ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β rMK ξ idx
  dsimp only [mk94Body01U]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    mul_mulVec_prog, mul_mulVec_prog, mul_mulVec_prog,
    eval_onRegister_prog_ket rMK (mk94LoadPairMux tTab) β, hLSgn γ]
  simp only [ZMod.val_zero, pow_zero, one_smul]
  rw [mk94SplitTop33.revCircuit_ket rMK, hreg γ1, fmkWriteRegProg_idem,
    eval_onRegister_prog_ket rMK (mk94MulAxisFull36 w), hreg γ2,
    hMMut.2.1 γ2 hMid2.2.2.2.2.2]
  simp only [ZMod.val_zero, pow_zero, one_smul]
  rw [fmkWriteRegProg_idem, mk94SplitTop33.fwdCircuit_ket rMK, hreg γ3, fmkWriteRegProg_idem]
  rfl

theorem ket_mk94Pass01U {n : ℕ} [NeZero (2 ^ n)] (rMK : QRegister 268 n) (w : Fin 3)
    (tTab : Fin 256 → ℕ) (β : BitAssignment n) (hγ : mk94InvU54 (fun q ↦ β (rMK q))) :
    (mk94Pass01U rMK w tTab).1.mulVec (ket β) = ket
    (writeRegProg β rMK (mk94Pass01Bits w tTab (fun q ↦ β (rMK q)))) := by
  dsimp only [mk94Pass01U, mk94Pass01Bits]
  rw [Submonoid.coe_mul, mul_mulVec_prog, ket_mk94Body01U rMK w tTab β hγ,
    eval_onRegister_prog_ket rMK (mk94LoadPairMux tTab),
    (mk94LoadPairMux_spec tTab).2.2.1 _, ZMod.val_zero, pow_zero, one_smul,
    fmkWriteRegProg_idem]
  have hreg : (fun idx ↦ writeRegProg β rMK (mk94Pass01BodyBits w tTab (fun q ↦ β (rMK q)))
      (rMK idx)) = mk94Pass01BodyBits w tTab (fun q ↦ β (rMK q)) := funext fun idx ↦
      writeRegProg_apply_reg β rMK _ idx
  rw [hreg]

attribute [local irreducible] mk94LoadPairMux mk94Pass01BodyBits mk94Pass01Bits

def mk94Pass2BodyBits (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268) : BitAssignment
    268 := (mk94MulAxisFull36 w).evalBits
    (mk94SplitAll36.revBits ((mk94LoadPairMux tTab).evalBits γ))

def mk94Pass2Bits (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268) : BitAssignment 268
    := mk94SplitAll36.revBits ((mk94LoadPairMux tTab).evalBits (mk94SplitAll36.fwdBits
    (mk94Pass2BodyBits w tTab γ)))

theorem mk94Pass2Bits_spec (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268)
    (hU54 : mk94InvU54 γ) (hBankZ : ∀ r : Fin 36, γ (mk94Bank36W r) = 0) :
    let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
    let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
    let d : Fin 36 → ZMod 2 := fun r ↦ γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val)
    let γ_body := mk94Pass2BodyBits w tTab γ
    let γ_out := mk94Pass2Bits w tTab γ
    mk94InvCleanU18 γ_out ∧
    (∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ_body q = γ_out q) ∧
    (∀ r : Fin 36, γ_body (mk94Bank36W r) = d r) ∧
    (∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_out q = γ q) ∧
    (let pNew0 : Fin 256 :=
       ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
     let pOld0 : Fin 256 :=
       ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
     ((bitsVal (fun m ↦ γ_out (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
       ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
         64 * ((twosComp8Int pNew0 - twosComp8Int pOld0) * (bitsVal d : ℤ))).emod (2 ^ 42 : ℤ)) :=
           by
  intro pAct idx d γ_body γ_out
  obtain ⟨_, _, _, hLOut, hLSpec⟩ := mk94LoadPairMux_spec tTab
  obtain ⟨_, hMMut, _⟩ := mk94MulAxisFull36_spec w
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  obtain ⟨hInv1, hLB1⟩ := hLSpec γ hU54
  have h1_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ1 q = γ q := hLOut γ hU54.2.2
  have h1_bank : ∀ r : Fin 36, γ1 (mk94Bank36W r) = d r := fun r ↦ by
    change (mk94LoadPairMux tTab).evalBits γ (mk94Bank36W r) = d r
    rw [hLB1 r, hBankZ r, zero_add]
  let γ2 := mk94SplitAll36.revBits γ1
  obtain ⟨hU18_2c, _, hRev2, hKeep2_c⟩ := mk94SplitAll36_rev_spec γ1 hInv1
  have hU18_2 : mk94InvU18 γ2 := by dsimp only [γ2]; rwa [hRev2]
  have hKeep2 : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ2 q = γ1 q :=
    fun q hq ↦ by dsimp only [γ2]; rw [hRev2]; exact hKeep2_c q hq
  have h3_non : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ_body q = γ2 q :=
    hMMut.2.2.2 γ2 hU18_2.2.2.2.2.2
  have hU18_body : mk94InvU18 γ_body :=
    mk94InvU18_congr_cat_bank (fun q hnc _ ↦ h3_non q hnc) hU18_2
  have hbody_bank : ∀ r : Fin 36, γ_body (mk94Bank36W r) = d r := fun r ↦ by
    have hr : 196 ≤ (mk94Bank36W r).val ∧ (mk94Bank36W r).val < 232 := by
      dsimp [mk94Bank36W]; omega
    exact (h3_non _ (by dsimp [mk94Bank36W]; omega)).trans
      ((hKeep2 _ (Or.inr hr)).trans (h1_bank r))
  have hbody_lt : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_body q = γ q :=
    fun q hlt hnc ↦
      (h3_non q hnc).trans ((hKeep2 q (Or.inl hlt)).trans (h1_non q (by omega)))
  let γ4 := mk94SplitAll36.fwdBits γ_body
  obtain ⟨hInv4, hKeep4⟩ := mk94SplitAll36_spec.2 γ_body hU18_body
  change mk94InvU54 γ4 at hInv4
  change ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ4 q = γ_body q at hKeep4
  let γ5 := (mk94LoadPairMux tTab).evalBits γ4
  obtain ⟨hInv5, _⟩ := hLSpec γ4 hInv4
  change mk94InvU54 γ5 at hInv5
  have h5_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ5 q = γ4 q :=
    hLOut γ4 hInv4.2.2
  have h4_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ4 q = γ q :=
    fun q hlt hnc ↦ (hKeep4 q (Or.inl hlt)).trans (hbody_lt q hlt hnc)
  have h5_bank := mk94LoadBank_cancel tTab γ γ4 hInv4
    (fun r ↦ (hKeep4 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (hbody_bank r)) h4_lt_nc
  obtain ⟨hU18_6c, _, hRev6, hKeep6_c⟩ := mk94SplitAll36_rev_spec γ5 hInv5
  have hU18_out : mk94InvU18 γ_out := by dsimp only [γ_out, mk94Pass2Bits]; rwa [hRev6]
  have hKeep6 : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ_out q = γ5 q :=
    fun q hq ↦ by dsimp only [γ_out, mk94Pass2Bits]; rw [hRev6]; exact hKeep6_c q hq
  have hout_bank : ∀ r : Fin 36, γ_out (mk94Bank36W r) = 0 := fun r ↦
    (hKeep6 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h5_bank r)
  have hout_eq_body_lt : ∀ q : Wire 268, q.val < 174 → γ_out q = γ_body q := fun q hlt ↦
    (hKeep6 q (Or.inl hlt)).trans ((h5_non q (by omega)).trans (hKeep4 q (Or.inl hlt)))
  refine ⟨⟨hU18_out, hout_bank⟩, mk94InvU18_ext_nonBank hU18_body hU18_out (fun q hlt ↦
    (hout_eq_body_lt q hlt).symm), hbody_bank, fun q hlt hnc ↦ (hout_eq_body_lt q hlt).trans
    (hbody_lt q hlt hnc), ?_⟩
  exact mk94Cat42_mulAxis_mod w γ γ1 γ2 γ_out d hU18_2.2.2.2.2.2 h1_non h1_bank hKeep2 fun m ↦
    hout_eq_body_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)

noncomputable def mk94Body2U {n : ℕ} (rMK : QRegister 268 n) (w : Fin 3) (tTab : Fin 256 → ℕ)
    : Unitary (2 ^ n) := (((mk94MulAxisFull36 w).onRegister rMK).toToffCircuit).eval *
    ((mk94SplitAll36.revCircuit rMK).eval * (((mk94LoadPairMux tTab).onRegister
    rMK).toToffCircuit).eval)

noncomputable def mk94Pass2U {n : ℕ} (rMK : QRegister 268 n) (w : Fin 3) (tTab : Fin 256 → ℕ)
    : Unitary (2 ^ n) := (mk94SplitAll36.revCircuit rMK).eval * ((((mk94LoadPairMux
    tTab).onRegister rMK).toToffCircuit).eval * ((mk94SplitAll36.fwdCircuit rMK).eval *
    mk94Body2U rMK w tTab))

theorem ket_mk94Body2U {n : ℕ} [NeZero (2 ^ n)] (rMK : QRegister 268 n) (w : Fin 3)
    (tTab : Fin 256 → ℕ) (β : BitAssignment n) (hγ : mk94InvU54 (fun q ↦ β (rMK q))) :
    (mk94Body2U rMK w tTab).1.mulVec (ket β) = ket
    (writeRegProg β rMK (mk94Pass2BodyBits w tTab (fun q ↦ β (rMK q)))) := by
  let γ : BitAssignment 268 := fun q ↦ β (rMK q)
  change mk94InvU54 γ at hγ
  obtain ⟨_, _, hLSgn, _, hLSpec⟩ := mk94LoadPairMux_spec tTab
  obtain ⟨_, hMMut, _⟩ := mk94MulAxisFull36_spec w
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  have hInv1 : mk94InvU54 γ1 := (hLSpec γ hγ).1
  let γ2 := mk94SplitAll36.revBits γ1
  obtain ⟨hU18_2c, _, hRev2, _⟩ := mk94SplitAll36_rev_spec γ1 hInv1
  have hU18_2 : mk94InvU18 γ2 := by dsimp only [γ2]; rwa [hRev2]
  have hreg : ∀ (ξ : BitAssignment 268), (fun idx ↦ writeRegProg β rMK ξ (rMK idx)) = ξ :=
    fun ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β rMK ξ idx
  dsimp only [mk94Body2U]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, mul_mulVec_prog, mul_mulVec_prog,
    eval_onRegister_prog_ket rMK (mk94LoadPairMux tTab) β, hLSgn γ]
  simp only [ZMod.val_zero, pow_zero, one_smul]
  rw [mk94SplitAll36.revCircuit_ket rMK, hreg γ1, fmkWriteRegProg_idem,
    eval_onRegister_prog_ket rMK (mk94MulAxisFull36 w), hreg γ2,
    hMMut.2.1 γ2 hU18_2.2.2.2.2.2]
  simp only [ZMod.val_zero, pow_zero, one_smul]
  rw [fmkWriteRegProg_idem]
  rfl

theorem ket_mk94Pass2U {n : ℕ} [NeZero (2 ^ n)] (rMK : QRegister 268 n) (w : Fin 3)
    (tTab : Fin 256 → ℕ) (β : BitAssignment n) (hγ : mk94InvU54 (fun q ↦ β (rMK q))) :
    (mk94Pass2U rMK w tTab).1.mulVec (ket β) = ket
    (writeRegProg β rMK (mk94Pass2Bits w tTab (fun q ↦ β (rMK q)))) := by
  let γ : BitAssignment 268 := fun q ↦ β (rMK q)
  let γ_b := mk94Pass2BodyBits w tTab γ
  let γ_f := mk94SplitAll36.fwdBits γ_b
  let γ_l := (mk94LoadPairMux tTab).evalBits γ_f
  have hreg : ∀ (ξ : BitAssignment 268), (fun idx ↦ writeRegProg β rMK ξ (rMK idx)) = ξ :=
    fun ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β rMK ξ idx
  dsimp only [mk94Pass2U]
  rw[Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul, mul_mulVec_prog,
      mul_mulVec_prog, mul_mulVec_prog, ket_mk94Body2U rMK w tTab β hγ,
      mk94SplitAll36.fwdCircuit_ket rMK, hreg γ_b, fmkWriteRegProg_idem,
      eval_onRegister_prog_ket rMK (mk94LoadPairMux tTab), hreg γ_f,
      (mk94LoadPairMux_spec tTab).2.2.1 γ_f]
  simp only [ZMod.val_zero, pow_zero, one_smul]
  rw [fmkWriteRegProg_idem, mk94SplitAll36.revCircuit_ket rMK, hreg γ_l, fmkWriteRegProg_idem]
  rfl

attribute [local irreducible] mk94Pass2BodyBits mk94Pass2Bits

def mk94InvCleanU54 (γ : BitAssignment 268) : Prop :=
  mk94InvU54 γ ∧ ∀ r : Fin 36, γ (mk94Bank36W r) = 0


def mk94FullBits (cfg : SpecsAux.SpecMirror.Configuration) (γ : BitAssignment 268) : BitAssignment
    268 := mk94SplitU18W11.revBits (mk94Pass2Bits 2 (mk36NegCoordTable36 cfg 2)
    (mk94Pass01Bits 1 (mk36NegCoordTable36 cfg 1) (mk94Pass01Bits 0 (mk36NegCoordTable36 cfg
    0) (mk94SplitAll36.fwdBits (mk94SplitU18W11.fwdBits γ)))))

noncomputable def uMidKick216_36_94w (cfg : SpecsAux.SpecMirror.Configuration) {n : ℕ}
    (rMK : QRegister 268 n) : Unitary (2 ^ n) := (mk94SplitU18W11.revCircuit rMK).eval *
    (mk94Pass2U rMK 2 (mk36NegCoordTable36 cfg 2) * (mk94Pass01U rMK 1 (mk36NegCoordTable36
    cfg 1) * (mk94Pass01U rMK 0 (mk36NegCoordTable36 cfg 0) * ((mk94SplitAll36.fwdCircuit
    rMK).eval * (mk94SplitU18W11.fwdCircuit rMK).eval))))

theorem ket_uMidKick216_36_94w (cfg : SpecsAux.SpecMirror.Configuration) {n : ℕ} [NeZero (2 ^ n)]
    (rMK : QRegister 268 n) (β : BitAssignment n) (hcl : cleanRem 268 94 (fun q ↦ β (rMK q)))
    : (uMidKick216_36_94w cfg rMK).1.mulVec (ket β) = ket
    (writeRegProg β rMK (mk94FullBits cfg (fun q ↦ β (rMK q)))) := by
  let γ0 : BitAssignment 268 := fun q ↦ β (rMK q)
  change cleanRem 268 94 γ0 at hcl
  let γ1 := mk94SplitU18W11.fwdBits γ0
  have h1 : mk94InvCleanU18 γ1 := (mk94SplitU18W11_spec.2 γ0 hcl).1
  let γ2 := mk94SplitAll36.fwdBits γ1
  obtain ⟨hU54_2, hKeep2⟩ := mk94SplitAll36_spec.2 γ1 h1.1
  have hB2 : ∀ r : Fin 36, γ2 (mk94Bank36W r) = 0 := fun r ↦
    (hKeep2 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h1.2 r)
  let γ3 := mk94Pass01Bits 0 (mk36NegCoordTable36 cfg 0) γ2
  obtain ⟨hU54_3, hB3, _, _, _, _⟩ :=
    mk94Pass01Bits_spec 0 (mk36NegCoordTable36 cfg 0) γ2 hU54_2 hB2
  let γ4 := mk94Pass01Bits 1 (mk36NegCoordTable36 cfg 1) γ3
  obtain ⟨hU54_4, _, _, _, _, _⟩ :=
    mk94Pass01Bits_spec 1 (mk36NegCoordTable36 cfg 1) γ3 hU54_3 hB3
  let γ5 := mk94Pass2Bits 2 (mk36NegCoordTable36 cfg 2) γ4
  have hreg : ∀ (ξ : BitAssignment 268), (fun idx ↦ writeRegProg β rMK ξ (rMK idx)) = ξ :=
    fun ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β rMK ξ idx
  dsimp only [uMidKick216_36_94w]
  repeat rw [Submonoid.coe_mul]
  repeat rw [mul_mulVec_prog]
  rw [mk94SplitU18W11.fwdCircuit_ket rMK β,
    mk94SplitAll36.fwdCircuit_ket rMK, hreg γ1, fmkWriteRegProg_idem,
    ket_mk94Pass01U rMK 0 _ _ (by rwa [hreg γ2]), hreg γ2, fmkWriteRegProg_idem,
    ket_mk94Pass01U rMK 1 _ _ (by rwa [hreg γ3]), hreg γ3, fmkWriteRegProg_idem,
    ket_mk94Pass2U rMK 2 _ _ (by rwa [hreg γ4]), hreg γ4, fmkWriteRegProg_idem,
    mk94SplitU18W11.revCircuit_ket rMK, hreg γ5, fmkWriteRegProg_idem]
  rfl

theorem mk94BitsVal_d (acc : ZMod 2) (tTab : Fin 256 → ℕ) (idx : Fin 256)
    (ht : tTab idx < 2 ^ 36) : bitsVal
    (fun r : Fin 36 ↦ acc * fmkBitZ ((tTab idx).testBit r.val)) = acc.val * tTab idx := by
  rcases fmkBit_cases acc with ha0 | ha1
  · simp only [ha0, zero_mul, ZMod.val_zero]; exact fmkBitsVal_zero 36
  · simp only [ha1, one_mul, ZMod.val_one]
    exact fmkBitsVal_eq_of_testBit _ _ ht (fun _ ↦ rfl)

open Classical in
theorem mk94FullBits_spec (cfg : SpecsAux.SpecMirror.Configuration) (γ : BitAssignment 268)
    (hcl : cleanRem 268 94 γ) :
    cleanRem 268 94 (mk94FullBits cfg γ) ∧
    ∀ i : Fin 174,
      mk94FullBits cfg γ ⟨i.val, by omega⟩ =
        (progMidKick216_36_411 cfg).evalBits
          (fun w : Wire 411 ↦ if hw : w.val < 174 then γ ⟨w.val, by omega⟩ else 0)
          ⟨i.val, by omega⟩ := by
  let t0 := mk36NegCoordTable36 cfg 0
  let t1 := mk36NegCoordTable36 cfg 1
  let t2 := mk36NegCoordTable36 cfg 2
  let γ1 := mk94SplitU18W11.fwdBits γ
  obtain ⟨h1_cl, h1_lt⟩ := mk94SplitU18W11_spec.2 γ hcl
  let γ2 := mk94SplitAll36.fwdBits γ1
  obtain ⟨hU54_2, hKeep2⟩ := mk94SplitAll36_spec.2 γ1 h1_cl.1
  have h2_lt : ∀ q : Wire 268, q.val < 174 → γ2 q = γ q :=
    fun q hq ↦ (hKeep2 q (Or.inl hq)).trans (h1_lt q hq)
  have hB2 : ∀ r : Fin 36, γ2 (mk94Bank36W r) = 0 :=
    fun r ↦ (hKeep2 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h1_cl.2 r)
  let γ3 := mk94Pass01Bits 0 t0 γ2
  obtain ⟨hU54_3, hB3, _, _, h3_nc, h3_cat⟩ := mk94Pass01Bits_spec 0 t0 γ2 hU54_2 hB2
  have h3_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ3 q = γ q :=
    fun q hlt hnc ↦ (h3_nc q hlt hnc).trans (h2_lt q hlt)
  let γ4 := mk94Pass01Bits 1 t1 γ3
  obtain ⟨hU54_4, hB4, _, _, h4_nc, h4_cat⟩ := mk94Pass01Bits_spec 1 t1 γ3 hU54_3 hB3
  have h4_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ4 q = γ q :=
    fun q hlt hnc ↦ (h4_nc q hlt hnc).trans (h3_lt_nc q hlt hnc)
  let γ5 := mk94Pass2Bits 2 t2 γ4
  obtain ⟨hU18_5, _, _, h5_nc, h5_cat⟩ := mk94Pass2Bits_spec 2 t2 γ4 hU54_4 hB4
  have h5_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ5 q = γ q :=
    fun q hlt hnc ↦ (h5_nc q hlt hnc).trans (h4_lt_nc q hlt hnc)
  obtain ⟨hcl6, _, hRev6⟩ := mk94SplitU18W11_rev_spec γ5 hU18_5
  have h6_eq : mk94FullBits cfg γ = mk94Zero94 γ5 := hRev6
  refine ⟨by rwa [h6_eq], fun i ↦ ?_⟩
  let γ411 : BitAssignment 411 := fun w ↦ if hw : w.val < 174 then γ ⟨w.val, by omega⟩ else 0
  have hγ411_cl : mk36Clean161 γ411 := fun w hw ↦
    dite_eq_right (by rcases hw with ⟨h1, _⟩ | h2 <;> omega)
  have hγ411_lt : ∀ (k : ℕ) (hk : k < 174), γ411 ⟨k, by omega⟩ = γ ⟨k, by omega⟩ :=
    fun k hk ↦ dite_eq_left hk
  obtain ⟨_, _, hN411, hE411⟩ := progMidKick216_36_411_raw_spec cfg
  have h6_lt : ∀ q : Wire 268, q.val < 174 → mk94FullBits cfg γ q = γ5 q := fun q hq ↦ by
    rw [h6_eq]; dsimp [mk94Zero94]; rw [ite_eq_left hq]
  rw [h6_lt ⟨i.val, by omega⟩ i.isLt]
  by_cases hcat : 107 ≤ i.val ∧ i.val < 149
  · let pAct := s3NucleusQ27 (fun k ↦ γ (mk94U16W k)) + 27 * (γ mk94BParW).val
    let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
    let pNew0 : Fin 3 → Fin 256 := fun w ↦
      ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
    let pOld0 : Fin 3 → Fin 256 := fun w ↦
      ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
    have hAux : ∀ (ξ : BitAssignment 268)
        (hξ : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → ξ q = γ q)
        (w : Fin 3),
        fmkIdx0 (ξ mk94B1W).val
          (s3NucleusQ27 (fun k ↦ ξ (mk94U16W k)) + 27 * (ξ mk94BParW).val)
          (ξ mk94B0W).val = idx ∧
        ξ mk94AccW = γ mk94AccW ∧
        (⟨bitsVal (fun b : Fin 8 ↦ ξ ⟨150 + 8 * w.val + b.val, by omega⟩),
            bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 w ∧
        (⟨bitsVal (fun b : Fin 8 ↦ ξ ⟨8 * w.val + b.val, by omega⟩),
            bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 w := by
      intro ξ hξ w
      have hu : (fun k ↦ ξ (mk94U16W k)) = fun k ↦ γ (mk94U16W k) :=
        funext fun k ↦ hξ (mk94U16W k) (by dsimp [mk94U16W]; omega) (by dsimp [mk94U16W]; omega)
      refine ⟨?_, hξ mk94AccW (by decide) (by decide),
        Fin.ext (congrArg bitsVal (funext fun b ↦ hξ _ (by dsimp; omega) (by dsimp; omega))),
        Fin.ext (congrArg bitsVal (funext fun b ↦ hξ _ (by dsimp; omega) (by dsimp; omega)))⟩
      dsimp only [idx, pAct]
      rw [hu, hξ mk94B1W (by decide) (by decide), hξ mk94BParW (by decide) (by decide),
        hξ mk94B0W (by decide) (by decide)]
    obtain ⟨hI2, hA2, hPN2, hPO2⟩ := hAux γ2 (fun q hlt _ ↦ h2_lt q hlt) 0
    obtain ⟨hI3, hA3, hPN3, hPO3⟩ := hAux γ3 h3_lt_nc 1
    obtain ⟨hI4, hA4, hPN4, hPO4⟩ := hAux γ4 h4_lt_nc 2
    dsimp only at h3_cat h4_cat h5_cat
    rw [hI2, hA2, hPN2, hPO2, mk94BitsVal_d _ t0 idx (mk36NegCoordTable36_lt cfg 0 idx)] at h3_cat
    rw [hI3, hA3, hPN3, hPO3, mk94BitsVal_d _ t1 idx (mk36NegCoordTable36_lt cfg 1 idx)] at h4_cat
    rw [hI4, hA4, hPN4, hPO4, mk94BitsVal_d _ t2 idx (mk36NegCoordTable36_lt cfg 2 idx)] at h5_cat
    have hcat2 : (fun m : Fin 42 ↦ γ2 (mk94Cat42W m)) = fun m : Fin 42 ↦ γ (mk94Cat42W m) :=
      funext fun m ↦ h2_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)
    rw [hcat2] at h3_cat
    have hE := hE411 γ411 hγ411_cl
    dsimp only at hE
    have hidx411 :
        (⟨(γ411 (mk36U16W 0)).val + 2 * (γ411 (mk36U16W 1)).val +
            4 * s3NucleusQ27 (fun k ↦ γ411 (mk36U16W k)) + 128 * (γ411 mk36BParW).val,
          by
            have := ZMod.val_lt (γ411 (mk36U16W 0))
            have := ZMod.val_lt (γ411 (mk36U16W 1))
            have := s3NucleusQ27_lt (fun k ↦ γ411 (mk36U16W k))
            have := ZMod.val_lt (γ411 mk36BParW)
            omega⟩ : Fin 256) = idx := by
      have hu411 : (fun k : Fin 16 ↦ γ411 (mk36U16W k)) = fun k ↦ γ (mk94U16W k) :=
        funext fun k ↦ hγ411_lt (91 + k.val) (by omega)
      have hb0_411 : γ411 (mk36U16W 0) = γ mk94B0W := hγ411_lt 91 (by decide)
      have hb1_411 : γ411 (mk36U16W 1) = γ mk94B1W := hγ411_lt 92 (by decide)
      have hbp_411 : γ411 mk36BParW = γ mk94BParW := hγ411_lt 90 (by decide)
      apply Fin.ext
      dsimp only [idx, fmkIdx0, pAct]
      rw [hu411, hb0_411, hb1_411, hbp_411]
      have := ZMod.val_lt (γ mk94B0W)
      have := ZMod.val_lt (γ mk94B1W)
      have := ZMod.val_lt (γ mk94BParW)
      have := s3NucleusQ27_lt (fun k ↦ γ (mk94U16W k))
      omega
    have hcat411 : (fun m : Fin 42 ↦ γ411 (mk36Cat42W m)) = fun m : Fin 42 ↦ γ (mk94Cat42W m) :=
      funext fun m ↦ hγ411_lt (107 + m.val) (by omega)
    have hacc411 : γ411 mk36AccW = γ mk94AccW := hγ411_lt 149 (by decide)
    have hpN411 : ∀ w : Fin 3,
        (⟨bitsVal (fun b : Fin 8 ↦ γ411 ⟨150 + 8 * w.val + b.val, by omega⟩),
            bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 w :=
      fun w ↦ Fin.ext (congrArg bitsVal (funext fun b ↦ hγ411_lt _ (by omega)))
    have hpO411 : ∀ w : Fin 3,
        (⟨bitsVal (fun b : Fin 8 ↦ γ411 ⟨8 * w.val + b.val, by omega⟩),
            bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 w :=
      fun w ↦ Fin.ext (congrArg bitsVal (funext fun b ↦ hγ411_lt _ (by omega)))
    have hcat_mod : ((bitsVal (fun m : Fin 42 ↦ γ5 (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
        ((bitsVal (fun m : Fin 42 ↦ (progMidKick216_36_411 cfg).evalBits γ411 (mk36Cat42W m))
        : ℤ)).emod (2 ^ 42 : ℤ) := by
      rw[h5_cat, fmkInt_add_emod, h4_cat, ← fmkInt_add_emod, add_assoc, fmkInt_add_emod,
          h3_cat, ← fmkInt_add_emod, hE, hcat411, hacc411, hidx411, Fin.sum_univ_three,
          hpN411 0, hpO411 0, hpN411 1, hpO411 1, hpN411 2, hpO411 2,
          fmkNegCoordTable_trunc36Cfg cfg 0 idx, fmkNegCoordTable_trunc36Cfg cfg 1 idx,
          fmkNegCoordTable_trunc36Cfg cfg 2 idx]
      dsimp only [t0, t1, t2]
      apply congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ))
      push_cast
      ring
    set g1 : Fin 42 → ZMod 2 := fun m ↦ γ5 (mk94Cat42W m)
    set g2 : Fin 42 → ZMod 2 := fun m ↦ (progMidKick216_36_411 cfg).evalBits γ411 (mk36Cat42W m)
    have hlt1 : bitsVal g1 < 2 ^ 42 := bitsVal_lt_two_pow g1
    have hlt2 : bitsVal g2 < 2 ^ 42 := bitsVal_lt_two_pow g2
    change ((bitsVal g1 : ℤ) % (2 ^ 42 : ℤ)) = ((bitsVal g2 : ℤ) % (2 ^ 42 : ℤ)) at hcat_mod
    rw [Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hlt1),
        Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hlt2)] at hcat_mod
    have hfn_eq : g1 = g2 := mk36BitsVal_inj (Int.ofNat.inj hcat_mod)
    have hm := congrFun hfn_eq ⟨i.val - 107, by omega⟩
    dsimp only [g1, g2, mk94Cat42W, mk36Cat42W] at hm
    have hw1 : (⟨107 + (i.val - 107), by omega⟩ : Wire 268) = ⟨i.val, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    have hw2 : (⟨107 + (i.val - 107), by omega⟩ : Wire 411) = ⟨i.val, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    rwa [hw1, hw2] at hm
  · rw [h5_lt_nc ⟨i.val, by omega⟩ i.isLt (by dsimp; exact hcat),
      hN411 γ411 hγ411_cl ⟨i.val, by omega⟩ (by dsimp; exact hcat),
      hγ411_lt i.val i.isLt]

end

set_option maxRecDepth 512

end ConfigLeaf3PrepAndMidKickSpecs

end Leaf3PrepAndMidKickSpecs
end
set_option exponentiation.threshold 256
end Leaf3PrepAndMidKickSpecs

section Leaf3Slot3Norm1sWidth204
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3Slot3Norm1sWidth204 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Compact `179w` / `193w` `Slot3Norm1s36` Leaves (`Leaf3Slot3Norm1sWidth204`)

Provides:
1. Standalone Slot-3 interface structures (`Slot3LeafSpec`, `Slot3PrepCompactSpec`,
   `Slot3MidKick36CompactSpec`) and exact 10-horizon tier/cap schedule
   (`leaf3Tier`, `leaf3CtrlCap`, `leaf3CatCap`).
2. Certified `262`-wire `piSwap3Core`-conjugated `MomSingleSlotOracle 80 48 3`
   (`s3Swap3OracleNorm1s_262`) across all 5 `Norm1sTier` operating points
   (`{.t26_18, .t26_17, .t27_17, .t29_18, .t29_17}`) with `CommutesWithReg rEC80`
   and `FixesLow3924` on both `uSlotCat` and `uSlotEff`.
3. Zero-reindexing `mCat = 36` top-catalyst-slice (`rTopCatSlice 36 48`) core unitary
   `uCore143Norm1s` and Slot-3 catalyst unitary `uSlot3Swap3Cat36Norm1s`, proving that
   because `64` divides `s3Shift42Norm1s t cfg`, `uCore149Norm1s` acts as exact identity
   on active wires `107..112` and embeds via `rTopCatSlice 36 48` to `uSlot3Swap3CatNorm1s`.
4. Split `clz17Ops` (`17` allocs, `16` `TempAnd`s) + deferred `clzE5Ops` (`5` allocs, `0`
   `TempAnd`s) and `55`-`TempAnd` (`78`-alloc) left-normalizing `barrel55Ops` (`-32 T` vs
   `barrel59Ops`), symbolically verified across all `2 ^ 18 = 262,144` inputs via
   `evalMicroAffStrict` so monolithic `clz17Ops ++ barrel55Ops` + `Booth` fits inside
   `178 <= 179` workspace wires across all tiers (`wAcc <= 32`).
-/

public section

namespace Leaf3Slot3Norm1sWidth204

section ConfigLeaf3Slot3Norm1sWidth204

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority :=
  10) instLoc_Leaf3Slot3Norm1sWidth204_1InstNeZeroTwoPowLe (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open FullSysMomSlots0135Concrete (momCoreWires)
open FullSysMomSlots0135Concrete (mom_zero_add_le)
open PosMomSelectDynamic (unitaryConj)
open InterWalkRSum42Hoist (FixesLow3924 h3924_momCat h3924_momCore)
open InterWalkRSum42Hoist (fixesLow3924_embedMatrix_high)
open StepBBlock0 (sel107)
open Slot3MicroEngineAux (MicroOp microValid microAllocs microAnds)
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36Physics80 (uCore149Norm1s uCore3EffNorm1s)
open Slot3Norm1s36Physics80 (uSlot3EffNorm1s)
open Slot3Prep273AndSwap3 (rCore0_80 fixesLow3924_uPrep3_216)
open Slot3Prep273AndSwap3 (fixesLow3924_of_embed_rCore0)
open Slot3Exact216Oracle80 (uPrep3_216 sel149_80_ge_3924)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (writeRegProg)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem)

/- ## Section 1: Standalone Sub-Specs & 10-Horizon Schedule -/

/-- Active `SELECT` core width `systemQubits + 86 = 4,034` (`rfl`-equal to `momCoreWires 80`). -/
abbrev coreWires80 : ℕ := momCoreWires 80

/-- Standalone clean-workspace `(rCore80, rPG, rWB)` leaf contract for `(mCat mWB tCap : ℕ)`. -/
structure Slot3LeafSpec (mCat mWB tCap : ℕ) where
  uCat : SpecsAux.SpecMirror.Configuration → Unitary (2 ^ (coreWires80 + mCat))
  dLeaf : SpecsAux.SpecMirror.Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rC : QRegister coreWires80 n) → (rP : QRegister mCat n) →
    (rWB : QRegister mWB n) → rC.DisjointWires rP → rC.DisjointWires rWB →
    rP.DisjointWires rWB → DynamicCircuit Var n
  hToff : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rC : QRegister coreWires80 n) (rP : QRegister mCat n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB),
    (dLeaf c v rC rP rWB hCP hCW hPW).count PrimitiveGate.TOFF = 0
  hT : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rC : QRegister coreWires80 n) (rP : QRegister mCat n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB),
    (dLeaf c v rC rP rWB hCP hCW hPW).count PrimitiveGate.T ≤ tCap
  hReal : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rC : QRegister coreWires80 n) (rP : QRegister mCat n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rC.concat rP hCP) rWB (uCat c) (dLeaf c v rC rP rWB hCP hCW hPW)

/-- Catalyst-free compact Slot-3 state-preparation pair `(dPrep, dPrepInv)` on
`(rCore : QRegister (momCoreWires 80) n, rWork : QRegister mPrep n)`. -/
structure Slot3PrepCompactSpec (mPrep tPrepRT : ℕ) where
  dPrep : ∀ {Var : Type} {n : ℕ},
    Var → (rCore : QRegister (momCoreWires 80) n) → (rWork : QRegister mPrep n) →
    rCore.DisjointWires rWork → DynamicCircuit Var n
  dPrepInv : ∀ {Var : Type} {n : ℕ},
    Var → (rCore : QRegister (momCoreWires 80) n) → (rWork : QRegister mPrep n) →
    rCore.DisjointWires rWork → DynamicCircuit Var n
  hToff : ∀ {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (momCoreWires 80) n) (rWork : QRegister mPrep n)
    (hCW : rCore.DisjointWires rWork),
    (dPrep v rCore rWork hCW).count PrimitiveGate.TOFF = 0 ∧
    (dPrepInv v rCore rWork hCW).count PrimitiveGate.TOFF = 0
  hTRT : ∀ {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (momCoreWires 80) n) (rWork : QRegister mPrep n)
    (hCW : rCore.DisjointWires rWork),
    (dPrep v rCore rWork hCW).count PrimitiveGate.T +
      (dPrepInv v rCore rWork hCW).count PrimitiveGate.T ≤ tPrepRT
  hReal : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCore : QRegister (momCoreWires 80) n) (rWork : QRegister mPrep n)
    (hCW : rCore.DisjointWires rWork),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCore rWork (uPrep3_216 (le_refl 80)) (dPrep v rCore rWork hCW) ∧
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCore rWork (uPrep3_216 (le_refl 80))⁻¹ (dPrepInv v rCore rWork hCW)

def IsCertifiedNorm1sTier (t : Norm1sTier) : Prop :=
  t = .t26_18 ∨ t = .t26_17 ∨ t = .t27_17 ∨ t = .t29_18 ∨ t = .t29_17

theorem fixesLow3924_uSlot3EffNorm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    FixesLow3924 h3924_momCore (uSlot3EffNorm1s t cfg (le_refl 80)).1 := by
  have hSwapCat : FixesLow3924 h3924_momCat (rCore0_80.embedMatrix
      (Slot3Norm1s36Physics80.s3SwapRejUnitaryNorm1s t (le_refl
      80)).1) := by
    have hemb :=
      Slot3Norm1s36Physics80.uSwapRej107Norm1s_embed t (le_refl 80)
    have hval : rCore0_80.embedMatrix
        (Slot3Norm1s36Physics80.s3SwapRejUnitaryNorm1s t (le_refl
        80)).1 = (sel107 (le_refl 80)).embedMatrix
        (Slot3Norm1s36Physics80.uSwapRej107Norm1s t).1 := by
      rw [← QRegister.embedUnitary_val, ← QRegister.embedUnitary_val, ← hemb]
    rw [hval]
    refine fixesLow3924_embedMatrix_high h3924_momCat (fun k ↦ ?_) _
    simpa [sel107, QRegister.slice_apply] using sel149_80_ge_3924 ⟨0 + k.val, by omega⟩
  have hSwap : FixesLow3924 h3924_momCore
      (Slot3Norm1s36Physics80.s3SwapRejUnitaryNorm1s t (le_refl
      80)).1 := fixesLow3924_of_embed_rCore0 hSwapCat
  have hKick : FixesLow3924 h3924_momCore
      (Slot3Norm1s36Physics80.s3KickEffUnitaryNorm1s t cfg
        (le_refl 80)).1 := by
    intro x y hne
    by_cases hxy : x = y
    · subst hxy; rfl
    · exfalso; apply hne
      change Matrix.diagonal _ x y = 0
      exact Matrix.diagonal_apply_ne _ hxy
  have hCore : FixesLow3924 h3924_momCore (uCore3EffNorm1s t cfg (le_refl 80)).1 :=
    hSwap.mul hKick
  exact fixesLow3924_uPrep3_216.unitaryConj hCore

def clz17Ops : List MicroOp := [ .zeroAlloc, .notW 18, .cnotW 17 18, .andAlloc 18 16, .cnotW
    19 18, .andAlloc 18 15, .cnotW 20 18, .andAlloc 18 14, .cnotW 21 18, .andAlloc 18 13,
    .cnotW 22 18, .andAlloc 18 12, .cnotW 23 18, .andAlloc 18 11, .cnotW 24 18, .andAlloc 18
    10, .cnotW 25 18, .andAlloc 18 9, .cnotW 26 18, .andAlloc 18 8, .cnotW 27 18, .andAlloc 18
    7, .cnotW 28 18, .andAlloc 18 6, .cnotW 29 18, .andAlloc 18 5, .cnotW 30 18, .andAlloc 18
    4, .cnotW 31 18, .andAlloc 18 3, .cnotW 32 18, .andAlloc 18 2, .cnotW 33 18, .andAlloc 18
    1, .cnotW 34 18 ]

open Classical in
theorem clz17Ops_meta : microValid 18 clz17Ops = true ∧ microAllocs clz17Ops = 17 ∧ microAnds
    clz17Ops = 16 := by
  decide

open PosMomSelectDynamic (unitaryConj_val)
open Slot3Norm1s36Physics80
  (s3Shift42Norm1s s3Shift42Norm1s_eq_nuclearM36 uSwapRej107Norm1s
   uSwapRej149Norm1s uKick149Norm1s)
open StepBBlock0 (sel107_80 sel107_80_val bitsVal_eq_of_testBit)
open StepBBlock0 (bitsVal_slice_linear s3DisjConcatLeft s3ItePos)
open StepBBlock0 (s3IteNeg s3DitePos s3DiteNeg)
open Slot3Prep273AndSwap3 (piSwap3Core piSwap3Wire)
open Slot3Prep273AndSwap3 (piSwap3WireFun_involutive)
open Slot3Prep273AndSwap3 (piSwap3CorePerm)
open Slot3Prep273AndSwap3 (basisBits_piSwap3CorePerm uPiSwap3Core)
open Slot3Prep273AndSwap3 (uPiSwap3Core_apply)
open InterWalkRSum42Hoist (qreg_ext)
open MeasureBranchHadamardSem (matrix_ext_ket)
open DyadicQft64 (catModAddUnitary catModAddUnitary_mulVec_basisKet)

/- ## Section 3: Zero-Reindexing `mCat = 36` Top-Catalyst Factorization & Leaf Assemblers -/

/-- Active `36`-bit catalyst modular-addition shift on `107` core wires (`s3Shift42 / 64`). -/
noncomputable def s3Shift36Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α107 : BitAssignment 107) : ℕ := s3Shift42Norm1s t cfg α107 / 64

open Classical in
theorem s3Shift42Norm1s_eq_64_mul_shift36 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α107 : BitAssignment 107) :
    s3Shift42Norm1s t cfg α107 = 64 * s3Shift36Norm1s t cfg α107 := by
  unfold s3Shift36Norm1s
  rw [s3Shift42Norm1s_eq_nuclearM36 t cfg α107]
  dsimp only
  split_ifs <;> omega

/-- `143`-wire subregister inside `149` active wires picking `[0..107) ++ [113..149)`. -/
def r143In149 : QRegister 143 149 where
  wires :=
    ⟨fun k ↦ ⟨if k.val < 107 then k.val else k.val + 6, by have := k.isLt; split_ifs <;> omega⟩,
     by
       intro i j hij
       have hv := congrArg Fin.val hij
       have hi := i.isLt; have hj := j.isLt
       dsimp only at hv
       split_ifs at hv <;> exact Fin.ext (by omega)⟩

/-- Active `143`-wire (`107` core + `36` top catalyst) modular-addition kick unitary. -/
noncomputable def uKick143Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ 143) := catModAddUnitary 107 36 (s3Shift36Norm1s t cfg)

/-- Active `143`-wire embedding of `uSwapRej107Norm1s t` on the low `107` active wires. -/
noncomputable def uSwapRej143Norm1s (t : Norm1sTier) : Unitary (2 ^ 143) :=
  (QRegister.block 0 107 (by decide)).embedUnitary (uSwapRej107Norm1s t)

/-- Combined `143`-wire (`107` core + `36` top catalyst) active core unitary. -/
noncomputable def uCore143Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    Unitary (2 ^ 143) := uSwapRej143Norm1s t * uKick143Norm1s t cfg

namespace Internal

open Classical in
theorem r143In149_embed_uKick143Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    r143In149.embedUnitary (uKick143Norm1s t cfg) = uKick149Norm1s t cfg := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  let rSub107 : QRegister 107 149 := QRegister.block 0 107 (by decide)
  let rCat42 : QRegister 42 149 := QRegister.block 107 42 (by decide)
  let rTop36 : QRegister 36 149 := QRegister.block 113 36 (by decide)
  have hDisj42 : rSub107.DisjointWires rCat42 :=
    QRegister.block_disjoint_of_le 0 107 107 42 (by decide) (by decide) (by decide)
  have hDisj36 : rSub107.DisjointWires rTop36 :=
    QRegister.block_disjoint_of_le 0 107 113 36 (by decide) (by decide) (by decide)
  have hConcat42 : rSub107.concat rCat42 hDisj42 = QRegister.whole 149 := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · apply Fin.ext; rw [QRegister.concat_apply_left, QRegister.whole_apply]
      change 0 + i.val = i.val; omega
    · apply Fin.ext; rw [QRegister.concat_apply_right, QRegister.whole_apply]
      rfl
  have hConcat36 : rSub107.concat rTop36 hDisj36 = r143In149 := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · apply Fin.ext; rw [QRegister.concat_apply_left]
      have hi := i.isLt
      change 0 + i.val = if i.val < 107 then i.val else i.val + 6
      rw [s3ItePos hi]; omega
    · apply Fin.ext; rw [QRegister.concat_apply_right]
      have hj := j.isLt
      change 113 + j.val = if 107 + j.val < 107 then 107 + j.val else (107 + j.val) + 6
      rw [s3IteNeg (by omega)]; omega
  have hWholeId : ∀ (U : Unitary (2 ^ 149)), ((QRegister.whole 149).embedUnitary U).1 = U.1 :=
    fun U ↦ congrArg Subtype.val (QRegister.whole_embedUnitary U)
  let vNew36 : ℕ := (regVal rTop36 β + s3Shift36Norm1s t cfg (fun i ↦ β (rSub107 i))) % 2 ^ 36
  let fBits36 : BitAssignment 36 := fun j ↦ if vNew36.testBit j.val then 1 else 0
  let f : BitAssignment 149 → BitAssignment 149 := fun δ ↦ writeRegProg δ rTop36 fBits36
  have hfVal36 : regVal rTop36 (f β) = vNew36 := by
    unfold regVal f
    have hfn : (fun j ↦ writeRegProg β rTop36 fBits36 (rTop36 j)) = fBits36 :=
      funext fun j ↦ writeRegProg_apply_reg β rTop36 fBits36 j
    rw [hfn]
    exact bitsVal_eq_of_testBit fBits36 vNew36 (Nat.mod_lt _ (by positivity)) (fun _ ↦ rfl)
  have hout36 : ∀ w, w ∉ rTop36.image → f β w = β w := fun w hw ↦
    writeRegProg_apply_of_not_mem β rTop36 fBits36 w (by simpa [QRegister.mem_image] using hw)
  have hLhs : basisKet (f β) =
      (r143In149.embedUnitary (uKick143Norm1s t cfg)).1.mulVec (basisKet β) := by
    rw [← hConcat36]
    exact catModAddUnitary_mulVec_basisKet rSub107 rTop36 hDisj36
      (s3Shift36Norm1s t cfg) f β hout36 hfVal36
  have hlow6 : ∀ (m : Fin 42), m.val < 6 → f β (rCat42 m) = β (rCat42 m) := by
    intro m hm6
    apply hout36 (rCat42 m)
    rw [QRegister.mem_image]
    rintro ⟨j, hj⟩
    have hv : 113 + j.val = 107 + m.val := congrArg Fin.val hj
    omega
  have hout42 : ∀ w, w ∉ rCat42.image → f β w = β w := by
    intro w hw; apply hout36 w; intro hmem; apply hw
    rw [QRegister.mem_image] at hmem ⊢
    obtain ⟨j, rfl⟩ := hmem
    exact ⟨⟨6 + j.val, by omega⟩, Fin.ext (by change 107 + (6 + j.val) = 113 + j.val; omega)⟩
  have hfVal42 : regVal rCat42 (f β) =
      (regVal rCat42 β + s3Shift42Norm1s t cfg (fun i ↦ β (rSub107 i))) % 2 ^ 42 := by
    obtain ⟨hlin, h2⟩ := bitsVal_slice_linear (N := 42) (W := 36) (k := 6) le_rfl
      (fun m ↦ β (rCat42 m)) (fun m ↦ f β (rCat42 m))
      (fun m hm ↦ hlow6 m (hm.resolve_right (by have := m.isLt; omega)))
    have htopEq : ∀ δ : BitAssignment 149,
        bitsVal (fun j : Fin 36 ↦ δ (rCat42 ⟨6 + j.val, by omega⟩)) = regVal rTop36 δ := by
      intro δ; unfold regVal
      refine congrArg bitsVal (funext fun j ↦ congrArg δ (Fin.ext ?_))
      change 107 + (6 + j.val) = 113 + j.val; omega
    rw [htopEq β, htopEq (f β), hfVal36] at hlin
    rw [htopEq β] at h2
    have hrc : regVal rCat42 β < 2 ^ 42 := bitsVal_lt_two_pow _
    have hrt : regVal rTop36 β < 2 ^ 36 := bitsVal_lt_two_pow _
    have hrcf : regVal rCat42 (f β) < 2 ^ 42 := bitsVal_lt_two_pow _
    change regVal rCat42 (f β) + 2 ^ 6 * regVal rTop36 β = regVal rCat42 β + 2 ^ 6 * ((regVal
      rTop36 β + s3Shift36Norm1s t cfg (fun i ↦ β (rSub107 i))) % 2 ^ 36) at hlin
    rw [s3Shift42Norm1s_eq_64_mul_shift36 t cfg (fun i ↦ β (rSub107 i))]
    have h2_6 : (2 : ℕ) ^ 6 = 64 := by decide
    have h2_36 : (2 : ℕ) ^ 36 = 68719476736 := by decide
    have h2_42 : (2 : ℕ) ^ 42 = 4398046511104 := by decide
    rw [h2_6] at hlin h2
    rw [h2_36] at hrt hlin
    rw [h2_42] at hrc hrcf ⊢
    omega
  have hRhs : basisKet (f β) = ((rSub107.concat rCat42 hDisj42).embedUnitary (uKick149Norm1s t
      cfg)).1.mulVec (basisKet β) := catModAddUnitary_mulVec_basisKet rSub107 rCat42 hDisj42
      (s3Shift42Norm1s t cfg) f β hout42 hfVal42
  rw [hConcat42, hWholeId] at hRhs
  exact hLhs.symm.trans hRhs

end Internal

open Classical in
theorem r143In149_embed_uCore143Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    r143In149.embedUnitary (uCore143Norm1s t cfg) = uCore149Norm1s t cfg := by
  unfold uCore143Norm1s uSwapRej143Norm1s uCore149Norm1s uSwapRej149Norm1s
  rw [QRegister.embedUnitary_mul, Internal.r143In149_embed_uKick143Norm1s,
    ← QRegister.embedUnitary_compose]
  have hcomp : r143In149.compose (QRegister.block 0 107 (by decide)) =
      QRegister.block 0 107 (by decide) := by
    apply qreg_ext; intro i; apply Fin.ext
    have hi := i.isLt
    change (if 0 + i.val < 107 then 0 + i.val else (0 + i.val) + 6) = 0 + i.val
    rw [s3ItePos (by omega)]
  rw [hcomp]

set_option exponentiation.threshold 5000
/-- Core `[0 .. 4034)` sub-register inside `coreWires80 + 36`. -/
abbrev rCore0_36 : QRegister coreWires80 (coreWires80 + 36) :=
  .block 0 coreWires80 (mom_zero_add_le coreWires80 36)

/-- Top-catalyst `[4034 .. 4070)` sub-register inside `coreWires80 + 36`. -/
abbrev rCat0_36 : QRegister 36 (coreWires80 + 36) := .block coreWires80 36 le_rfl

theorem hCoreCatDisj36 : rCore0_36.DisjointWires rCat0_36 := QRegister.block_disjoint_of_le 0
    coreWires80 coreWires80 36 (mom_zero_add_le coreWires80 36) le_rfl (by omega)

/-- `143`-wire active selector (`107` core wires + `36` catalyst wires) inside `coreWires80 +
  36`. -/
def sel143_80_36 : QRegister 143 (coreWires80 + 36) :=
  (rCore0_36.compose sel107_80).concat rCat0_36 (hCoreCatDisj36.compose_left sel107_80)

/-- Unpermuted `(coreWires80 + 36)`-wire Slot-3 catalyst unitary for tier `t`. -/
noncomputable def uSlot3Cat36Norm1s (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) : Unitary (2 ^ (coreWires80 + 36)) :=
  unitaryConj (rCore0_36.embedUnitary (uPrep3_216 (le_refl 80)))
    (sel143_80_36.embedUnitary (uCore143Norm1s t cfg))

/-- `piSwap3Core`-conjugated `(coreWires80 + 36)`-wire Slot-3 catalyst unitary for tier `t`. -/
noncomputable def uSlot3Swap3Cat36Norm1s (t : Norm1sTier)
    (cfg : SpecsAux.SpecMirror.Configuration) : Unitary (2 ^ (coreWires80 + 36)) :=
  unitaryConj (rCore0_36.embedUnitary uPiSwap3Core) (uSlot3Cat36Norm1s t cfg)

namespace Internal

open Classical in
theorem embedUnitary_inv_eq {k n : ℕ} [NeZero (2 ^ k)] [NeZero (2 ^ n)] (r : QRegister k n)
    (U : Unitary (2 ^ k)) : r.embedUnitary U⁻¹ = (r.embedUnitary U)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← QRegister.embedUnitary_mul, mul_inv_cancel, QRegister.embedUnitary_one]

open Classical in
theorem embedUnitary_unitaryConj {k n : ℕ} [NeZero (2 ^ k)] [NeZero (2 ^ n)]
    (r : QRegister k n) (U V : Unitary (2 ^ k)) :
    r.embedUnitary (unitaryConj U V) = unitaryConj (r.embedUnitary U) (r.embedUnitary V) := by
  have hConj : ∀ {m : ℕ} [NeZero (2 ^ m)] (A B : Unitary (2 ^ m)),
      unitaryConj A B = A⁻¹ * B * A := by
    intro m _ A B
    apply Subtype.ext
    have hInv : A.1ᴴ = (A⁻¹).1 := by simp [Matrix.star_eq_conjTranspose]
    rw [unitaryConj_val, Submonoid.coe_mul, Submonoid.coe_mul, hInv]
  rw [hConj U V, hConj (r.embedUnitary U) (r.embedUnitary V),
    QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, embedUnitary_inv_eq]

open Classical in
theorem sel107_80_ge_3924 (k : Fin 107) : 3924 ≤ (sel107_80 k).val := by
  have hv := sel107_80_val k
  split_ifs at hv <;> omega

theorem sel107_disj_low6 : (rCore0_36.compose sel107_80).DisjointWires
    (rCore0_36.compose (QRegister.block 0 6 (by decide))) := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  have hv := congrArg Fin.val heq
  have hi := sel107_80_ge_3924 i
  have hj := j.isLt
  have hL : (rCore0_36.compose sel107_80 i).val = 0 + (sel107_80 i).val := rfl
  have hR : (rCore0_36.compose (QRegister.block 0 6 (by decide)) j).val = 0 + (0 + j.val) := rfl
  omega

def sel149In36 : QRegister 149 (coreWires80 + 36) := ((rCore0_36.compose sel107_80).concat
    (rCore0_36.compose (QRegister.block 0 6 (by decide))) sel107_disj_low6).concat rCat0_36
    (s3DisjConcatLeft (hCoreCatDisj36.compose_left _) (hCoreCatDisj36.compose_left _))

open Classical in
theorem sel149In36_compose_r143In149 : sel149In36.compose r143In149 = sel143_80_36 := by
  apply qreg_ext; intro (idx : Fin (107 + 36))
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · have hi := i.isLt
    have hr : r143In149 (Fin.castAdd 36 i) = Fin.castAdd 36 (Fin.castAdd 6 i) := by
      apply Fin.ext
      change (if i.val < 107 then i.val else i.val + 6) = i.val
      rw [s3ItePos hi]
    change sel149In36 (r143In149 (Fin.castAdd 36 i)) = sel143_80_36 (Fin.castAdd 36 i)
    rw [hr]
    unfold sel149In36 sel143_80_36
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
  · have hj := j.isLt
    have hr : r143In149 (Fin.natAdd 107 j) = Fin.natAdd 113 j := by
      apply Fin.ext
      change (if 107 + j.val < 107 then 107 + j.val else (107 + j.val) + 6) = 113 + j.val
      rw [s3IteNeg (by omega)]; omega
    change sel149In36 (r143In149 (Fin.natAdd 107 j)) = sel143_80_36 (Fin.natAdd 107 j)
    rw [hr]
    unfold sel149In36 sel143_80_36
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right]

open Classical in
theorem sel149In36_embed_uCore149Norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) :
    sel149In36.embedUnitary (uCore149Norm1s t cfg) =
      sel143_80_36.embedUnitary (uCore143Norm1s t cfg) := by
  rw [← r143In149_embed_uCore143Norm1s, ← QRegister.embedUnitary_compose,
    sel149In36_compose_r143In149]

end Internal

namespace Internal

def piSwap3Cat36 : QRegister (coreWires80 + 36) (coreWires80 + 36) :=
  (rCore0_36.compose piSwap3Core).concat rCat0_36 (hCoreCatDisj36.compose_left piSwap3Core)

open Classical in
theorem piSwap3Cat36_apply_val (q : Wire (coreWires80 + 36)) : (piSwap3Cat36 q).val = if h :
    q.val < coreWires80 then (piSwap3Wire ⟨q.val, h⟩).val else q.val := by
  unfold piSwap3Cat36
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) q
  · have hiLt : (Fin.castAdd 36 i).val < coreWires80 := i.isLt
    rw [QRegister.concat_apply_left, s3DitePos hiLt]; exact Nat.zero_add _
  · have hge : ¬ ((Fin.natAdd coreWires80 j).val < coreWires80) := by
      change ¬ (coreWires80 + j.val < coreWires80); omega
    rw [QRegister.concat_apply_right, s3DiteNeg hge]; rfl

open Classical in
theorem piSwap3Cat36_involutive (q : Wire (coreWires80 + 36)) :
    piSwap3Cat36 (piSwap3Cat36 q) = q := by
  apply Fin.ext
  rw [piSwap3Cat36_apply_val, piSwap3Cat36_apply_val]
  by_cases h : q.val < coreWires80
  · rw [s3DitePos h]
    have h2 : (piSwap3Wire ⟨q.val, h⟩).val < coreWires80 := (piSwap3Wire ⟨q.val, h⟩).isLt
    rw [s3DitePos h2]
    exact congrArg Fin.val (piSwap3WireFun_involutive ⟨q.val, h⟩)
  · rw [s3DiteNeg h, s3DiteNeg h]

theorem piSwap3Cat36_extractIndex_involutive (z : Fin (2 ^ (coreWires80 + 36))) :
    piSwap3Cat36.extractIndex (piSwap3Cat36.extractIndex z) = z := by
  apply (basisBitsEquiv _).injective; funext q
  change basisBits _ _ q = basisBits _ _ q
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, piSwap3Cat36_involutive]

open Classical in
theorem embed_uPiSwap3Core36_apply (i j : Fin (2 ^ (coreWires80 + 36))) :
    (rCore0_36.embedUnitary uPiSwap3Core).1 i j =
      if i = piSwap3Cat36.extractIndex j then 1 else 0 := by
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside, uPiSwap3Core_apply]
  have hIff : (rCore0_36.extractIndex i = piSwap3CorePerm (rCore0_36.extractIndex j) ∧
      rCore0_36.AgreeOutside i j) ↔ i = piSwap3Cat36.extractIndex j := by
    constructor
    · rintro ⟨hCore, hOut⟩
      apply (basisBitsEquiv _).injective; funext q
      change basisBits _ i q = basisBits _ (piSwap3Cat36.extractIndex j) q
      rw [QRegister.basisBits_extractIndex]
      by_cases hq : q.val < coreWires80
      · let w : Wire coreWires80 := ⟨q.val, hq⟩
        have hqEq : q = rCore0_36 w := Fin.ext (Nat.zero_add q.val).symm
        have hpEq : piSwap3Cat36 q = rCore0_36 (piSwap3Wire w) :=
          Fin.ext (by rw [piSwap3Cat36_apply_val, s3DitePos hq]; exact (Nat.zero_add _).symm)
        rw [hpEq, hqEq, ← QRegister.basisBits_extractIndex rCore0_36 i w, hCore,
          basisBits_piSwap3CorePerm, QRegister.basisBits_extractIndex rCore0_36 j]
      · have hnot : q ∉ Set.range rCore0_36.wires := by
          rintro ⟨w, hw⟩; have hv : 0 + w.val = q.val := congrArg Fin.val hw
          have := w.isLt; omega
        have hpEq : piSwap3Cat36 q = q := Fin.ext (by rw [piSwap3Cat36_apply_val, s3DiteNeg hq])
        rw [hpEq, hOut q hnot]
    · rintro rfl
      refine ⟨?_, fun q hnot ↦ ?_⟩
      · apply (basisBitsEquiv _).injective; funext w
        change basisBits _ _ w = basisBits _ _ w
        rw [QRegister.basisBits_extractIndex, basisBits_piSwap3CorePerm,
          QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        have hwLt : (rCore0_36 w).val < coreWires80 := by
          have : (rCore0_36 w).val = 0 + w.val := rfl; have := w.isLt; omega
        exact congrArg (basisBits _ j)
          (Fin.ext (by
            rw [piSwap3Cat36_apply_val, s3DitePos hwLt]
            have hwEq : (⟨(rCore0_36 w).val, hwLt⟩ : Wire coreWires80) = w :=
              Fin.ext (Nat.zero_add w.val)
            rw [hwEq]; exact (Nat.zero_add _).symm))
      · have hq : ¬ (q.val < coreWires80) := fun hlt ↦
          hnot ⟨⟨q.val, hlt⟩, Fin.ext (Nat.zero_add q.val)⟩
        rw [QRegister.basisBits_extractIndex,
          show piSwap3Cat36 q = q from Fin.ext (by rw [piSwap3Cat36_apply_val, s3DiteNeg hq])]
  by_cases hi : i = piSwap3Cat36.extractIndex j
  · rcases hIff.mpr hi with ⟨h1, h2⟩
    rw [s3ItePos h2, s3ItePos h1, mul_one, s3ItePos hi]
  · by_cases h2 : rCore0_36.AgreeOutside i j
    · have h1 : rCore0_36.extractIndex i ≠ piSwap3CorePerm (rCore0_36.extractIndex j) :=
        fun h1 ↦ hi (hIff.mp ⟨h1, h2⟩)
      rw [s3ItePos h2, s3IteNeg h1, mul_one, s3IteNeg hi]
    · rw [s3IteNeg h2, mul_zero, s3IteNeg hi]

open Classical in
theorem embed_uPiSwap3Core36_self_adj :
    (rCore0_36.embedUnitary uPiSwap3Core).1ᴴ = (rCore0_36.embedUnitary uPiSwap3Core).1 := by
  ext i j
  rw [Matrix.conjTranspose_apply, embed_uPiSwap3Core36_apply, embed_uPiSwap3Core36_apply]
  by_cases h : j = piSwap3Cat36.extractIndex i
  · have h' : i = piSwap3Cat36.extractIndex j := by rw [h, piSwap3Cat36_extractIndex_involutive]
    rw [s3ItePos h, s3ItePos h', star_one]
  · have h' : i ≠ piSwap3Cat36.extractIndex j :=
      fun hi ↦ h (by rw [hi, piSwap3Cat36_extractIndex_involutive])
    rw [s3IteNeg h, s3IteNeg h', star_zero]

open Classical in
theorem piSwap3Cat36_agreeOutside (x y : Fin (2 ^ (coreWires80 + 36))) :
    piSwap3Cat36.AgreeOutside x y :=
  fun q hq ↦ False.elim (hq ⟨piSwap3Cat36 q, piSwap3Cat36_involutive q⟩)

open Classical in
theorem piSwap3Cat36_embedUnitary (W : Unitary (2 ^ (coreWires80 + 36))) :
    piSwap3Cat36.embedUnitary W = unitaryConj (rCore0_36.embedUnitary uPiSwap3Core) W := by
  apply Subtype.ext; ext i j
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply_of_agreeOutside,
    s3ItePos (piSwap3Cat36_agreeOutside i j), mul_one,
    unitaryConj_val, embed_uPiSwap3Core36_self_adj,
    Matrix.mul_apply, Finset.sum_eq_single (piSwap3Cat36.extractIndex j)]
  · rw [embed_uPiSwap3Core36_apply, s3ItePos rfl, mul_one,
      Matrix.mul_apply, Finset.sum_eq_single (piSwap3Cat36.extractIndex i)]
    · rw [embed_uPiSwap3Core36_apply,
        s3ItePos (piSwap3Cat36_extractIndex_involutive i).symm, one_mul]
    · intro k _ hk
      have hne : i ≠ piSwap3Cat36.extractIndex k :=
        fun h ↦ hk (by rw [h, piSwap3Cat36_extractIndex_involutive])
      rw [embed_uPiSwap3Core36_apply, s3IteNeg hne, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · intro k _ hk
    rw [embed_uPiSwap3Core36_apply, s3IteNeg hk, mul_zero]
  · intro habs; exact absurd (Finset.mem_univ _) habs

theorem concat_piSwap3Core_eq_compose_piSwap3Cat36 {n : ℕ} (rCore : QRegister coreWires80 n)
    (rPG36 : QRegister 36 n) (hCP : rCore.DisjointWires rPG36) :
    (rCore.compose piSwap3Core).concat rPG36 (hCP.compose_left piSwap3Core) =
    (rCore.concat rPG36 hCP).compose piSwap3Cat36 := by
  apply qreg_ext; intro q
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) q
  · rw [QRegister.concat_apply_left]
    change rCore (piSwap3Core i) = (rCore.concat rPG36 hCP) (piSwap3Cat36 (Fin.castAdd 36 i))
    have hpi : piSwap3Cat36 (Fin.castAdd 36 i) = Fin.castAdd 36 (piSwap3Core i) := by
      unfold piSwap3Cat36; rw [QRegister.concat_apply_left]; exact Fin.ext (Nat.zero_add _)
    rw [hpi, QRegister.concat_apply_left]
  · rw [QRegister.concat_apply_right]
    change rPG36 j = (rCore.concat rPG36 hCP) (piSwap3Cat36 (Fin.natAdd coreWires80 j))
    have hpi : piSwap3Cat36 (Fin.natAdd coreWires80 j) = Fin.natAdd coreWires80 j := by
      unfold piSwap3Cat36; rw [QRegister.concat_apply_right]; rfl
    rw [hpi, QRegister.concat_apply_right]

theorem zero_add_le_of_le {a b : ℕ} (h : a ≤ b) : 0 + a ≤ b := by omega

theorem realizesEmbedded_eq_left {Var : Type} [Fintype Var] [DecidableEq Var] {m k n : ℕ}
    [NeZero (2 ^ m)] [NeZero (2 ^ k)] [NeZero (2 ^ n)] {r₁ r₂ : QRegister m n} (hr : r₁ = r₂)
    (rW : QRegister k n) {U : Unitary (2 ^ m)} {d : DynamicCircuit Var n} (h :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r₁ rW U d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace r₂ rW U d := hr ▸ h

end Internal

set_option maxRecDepth 512

end ConfigLeaf3Slot3Norm1sWidth204

end Leaf3Slot3Norm1sWidth204

end
set_option exponentiation.threshold 256
end Leaf3Slot3Norm1sWidth204

section Leaf4Ext48TopStitch
local instance (priority := 1000000) instNeZeroTwoPow_Leaf4Ext48TopStitch (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `Ext48` + `H^{⊗ k_idle}` Subspace Top Stitch (`Leaf4Ext48TopStitch`)

Generalizes the control-zero (`rUnusedCtrl3Full`), coin-slack (`rSlack3Full`), and idle-catalyst
(`rPGIdle k_idle`, `k_idle ≤ 28`) active-clean workspace extensions to arbitrary `mWork` and
`k_idle`, closing:
1. Subspace projectors (`pCtrl3Zero`, `pSlack3Zero`, `pPGIdleZero`, `pGuardExtZero`,
   `pCtrlHoistExtZero`, `pCatHoistExtZero`, `E_ctrlExt`, `E_catExt`) and `PreservesFeature`
   commutativity helpers (`FixesCtrl3`, `FixesSlack3`, `IsIdlePGReg`).
2. `0-T` `cHadIdle` cancellation against `vPrepSingleCat 80 48 40` on low catalyst wires
   `[0 .. k_idle)` (`k_idle ≤ 28`) and post-`cHadIdle` `Stream42ExtInitSpec` (`131w ≤ 154w`
   on one axis + `164w` on the two axes with clean `rSum14Full`).
3. `SplitGuardParams` (`154_77`, `162_77`, `164_77`) and Guard A (`rMid43EffFull`, borrowing
   `rSum0[0 .. k_idle - 6)` when `2 ^ (k_idle - 6) ∣ C_d, D_d`) 2-angle and 1-angle GuardWraps.
4. Parametric Pass 1 / Pass 2 / Slot 3 / Twist subspace adapters, asymmetric
   `(dSelectCtrl, dSelectCat)` `Koff3Pass` stitch, and per-horizon 2-angle closure.
-/

public section

namespace Leaf4Ext48TopStitch

section ConfigLeaf4Ext48TopStitch

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 16384

local instance (priority :=
  1000000) instLoc_Leaf4Ext48TopStitch_1InstNeZeroTwoPowLeaf4To (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation

open SpecsAux.SpecMirror SpecsAux.FullScaleBESector
open BidirectionalCatalyzedGQSP (diagNegIPosICircuit biCode)
open TwosCompAndWire0Cancel (fwdPermUnitary fwdPermMatrix)
open TwosCompAndWire0Cancel (fwdPermMatrix_apply)
open FullSysWalkStepEndpoint (fullSys_zero_add_le)
open FullSysCatSegmentBridge
  (FullSysQft654Bundle FullSysPrepareBundle FullSysSelectOracleBundle
   fullSysCoreWires fullSysBEWires fullSysRawAncWires beCoreBlock
   disjointWires_concat_left disjointWires_compose_of_disjoint
   fullSys_zero_add_le_of_le)
open SingleCatSpine (rTopCatSlice)
open SingleCatClosure (SingleCatSelectImpl kActSingleCatClosure mActSingleCatClosure rBEInSingleCat
  rCatTotInSingleCat rSlackSave3InSingleCat qSigInSingleCat substActiveSingleCat
  substActiveSingleCat_count_TOFF substActiveSingleCat_count_T_le
  realizesCleanWorkspace_substActiveSingleCat cSlackParkSingleCat cSlackUnparkSingleCat
  uCatRawBESingleCat uCtrlRawBESingleCat)
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq)
open GidneySignalRotPart1 (rMid43InSingleCat kickFun43 kickPerm43)
open GidneySignalRotPart1 (uKickGidney43 optX43)
open InterWalkRSum42Hoist (mActOrig kActOrig mActHoist kFull80 rAct0 rSum0 rBEOrig rCoreOrig
  rCoreFull rSegOrig rPG48Orig rPG48Full hAct0_disj_Sum0 pSum42Zero E_stream42 qreg_ext
  widenActive_of_eq PreservesFeature FixesLow3924 h3924_be isLow3924Prefix_rBEOrig
  preservesFeature_embedMatrix_of_extract fixesLow3924_embedMatrix_prefix qreg_block_apply
  E_stream42_eq_streamProjOp embedAct0_comm_streamOp embedAct0_fixesLow3924_comm_E_stream42
  embedUnitary_inv_symm)
open GidneyTwoAngleGuardWrap220 (uSigMidTwoAngle43)
open HoistBorrow42ProjBridge (RealizesOnProj basisOutcomeProjector_concat_zero
  disjointWires_concat_right)
open HoistBorrow42TwoAngleBridge (uSignalRotTwoAngle43)

/-- Clean-workspace embedded-unitary realization alias (`DynamicCircuit`). -/
abbrev RealizesClean := @DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace

/- ## Section 1: Active-Clean Registers (`rUnusedCtrl3`, `rSlack3`, `rPGIdle k_idle`) & Projectors
-/

/-- Unused 3-wire control register `[3951 .. 3954)` inside `kActOrig = 4,086`. -/
def rUnusedCtrl3Orig : QRegister 3 kActOrig := QRegister.block 3951 3 (by decide)

/-- Unused 3-wire control register `[3951 .. 3954)` inside `kFull80 = 4,128`. -/
def rUnusedCtrl3Full : QRegister 3 kFull80 := rAct0.compose rUnusedCtrl3Orig

/-- Coin-park 3-wire slack register `[4083 .. 4086)` inside `kActOrig = 4,086`. -/
def rSlack3Orig : QRegister 3 kActOrig := rSlackSave3InSingleCat 80 48 40

/-- Coin-park 3-wire slack register `[4083 .. 4086)` inside `kFull80 = 4,128`. -/
def rSlack3Full : QRegister 3 kFull80 := rAct0.compose rSlack3Orig

/-- Low `k_idle` idle catalyst wires `[4035 .. 4035 + k_idle)` inside `kActOrig = 4,086`. -/
def rPGIdleOrig (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister k_idle kActOrig :=
  rPG48Orig.slice 0 k_idle (by omega)

/-- Low `k_idle` idle catalyst wires `[4035 .. 4035 + k_idle)` inside `kFull80 = 4,128`. -/
def rPGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister k_idle kFull80 :=
  rAct0.compose (rPGIdleOrig k_idle hk)

theorem rAct0_val_eq (w : Wire kActOrig) : (rAct0 w).val = w.val := by
  simp [rAct0]

theorem rUnusedCtrl3Orig_val_eq (t : Fin 3) : (rUnusedCtrl3Orig t).val = 3951 + t.val := by
  simp [rUnusedCtrl3Orig]

theorem rUnusedCtrl3Full_val_eq (t : Fin 3) : (rUnusedCtrl3Full t).val = 3951 + t.val := by
  simp only [rUnusedCtrl3Full, QRegister.compose_apply, rAct0_val_eq, rUnusedCtrl3Orig_val_eq]

theorem rPG48Orig_val_eq : ∀ i : Fin 48, (rPG48Orig i).val = 4035 + i.val := by
  decide

theorem rPG48Full_val_eq (i : Fin 48) : (rPG48Full i).val = 4035 + i.val := by
  change (rAct0 (rPG48Orig i)).val = 4035 + i.val
  rw [rAct0_val_eq, rPG48Orig_val_eq]

theorem rPGIdleOrig_val_eq (k_idle : ℕ) (hk : k_idle ≤ 48) (i : Fin k_idle) :
    (rPGIdleOrig k_idle hk i).val = 4035 + i.val := by
  have h : rPGIdleOrig k_idle hk i = rPG48Orig ⟨i.val, by omega⟩ := by
    simp only [rPGIdleOrig, QRegister.slice_apply, zero_add]
  rw [h, rPG48Orig_val_eq]

theorem rPGIdle_val_eq (k_idle : ℕ) (hk : k_idle ≤ 48) (i : Fin k_idle) :
    (rPGIdle k_idle hk i).val = 4035 + i.val := by
  dsimp [rPGIdle]
  rw [rAct0_val_eq, rPGIdleOrig_val_eq]

theorem rSlack3Orig_val_eq : ∀ t : Fin 3, (rSlack3Orig t).val = 4083 + t.val := by
  decide

theorem rSlack3Full_val_eq (t : Fin 3) : (rSlack3Full t).val = 4083 + t.val := by
  dsimp [rSlack3Full]
  rw [rAct0_val_eq, rSlack3Orig_val_eq]

theorem rSum0_val_eq : ∀ s : Fin 42, (rSum0 s).val = 4086 + s.val := by
  decide

theorem disj_of_val_ne {k₁ k₂ N : ℕ} {r₁ : QRegister k₁ N} {r₂ : QRegister k₂ N}
    (h : ∀ i j, (r₁ i).val ≠ (r₂ j).val) : r₁.DisjointWires r₂ := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  exact h i j (congrArg Fin.val hij)

theorem hCtrl3_disj_Slack3 : rUnusedCtrl3Full.DisjointWires rSlack3Full :=
  disj_of_val_ne fun i j ↦ by
    rw [rUnusedCtrl3Full_val_eq, rSlack3Full_val_eq]; have := i.isLt; have := j.isLt; omega

theorem hCtrl3_disj_PGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rUnusedCtrl3Full.DisjointWires (rPGIdle k_idle hk) :=
  disj_of_val_ne fun i j ↦ by
    rw [rUnusedCtrl3Full_val_eq, rPGIdle_val_eq]; have := i.isLt; have := j.isLt; omega

theorem hSlack3_disj_PGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rSlack3Full.DisjointWires (rPGIdle k_idle hk) :=
  disj_of_val_ne fun i j ↦ by
    rw [rSlack3Full_val_eq, rPGIdle_val_eq]; have := i.isLt; have := j.isLt; omega

theorem hSum0_disj_Ctrl3 : rSum0.DisjointWires rUnusedCtrl3Full :=
  disj_of_val_ne fun i j ↦ by
    rw [rSum0_val_eq, rUnusedCtrl3Full_val_eq]; have := i.isLt; have := j.isLt; omega

theorem hSum0_disj_Slack3 : rSum0.DisjointWires rSlack3Full :=
  disj_of_val_ne fun i j ↦ by
    rw [rSum0_val_eq, rSlack3Full_val_eq]; have := i.isLt; have := j.isLt; omega

theorem hSum0_disj_PGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rSum0.DisjointWires (rPGIdle k_idle hk) :=
  disj_of_val_ne fun i j ↦ by
    rw [rSum0_val_eq, rPGIdle_val_eq]; have := i.isLt; have := j.isLt; omega

theorem hPG48Orig_disj_Slack3Orig : rPG48Orig.DisjointWires rSlack3Orig :=
  disj_of_val_ne fun i j ↦ by
    rw [rPG48Orig_val_eq, rSlack3Orig_val_eq]; have := i.isLt; have := j.isLt; omega

/-- Combined `6`-wire (`rUnusedCtrl3Full ++ rSlack3Full`) active-clean register inside `kFull80`. -/
def rExt6Full : QRegister 6 kFull80 := rUnusedCtrl3Full.concat rSlack3Full hCtrl3_disj_Slack3

theorem hExt6_disj_PGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) : rExt6Full.DisjointWires
    (rPGIdle k_idle hk) := FullSysCatSegmentBridge.disjointWires_concat_left
    hCtrl3_disj_Slack3 (hCtrl3_disj_PGIdle k_idle hk) (hSlack3_disj_PGIdle k_idle hk)

/-- Combined `(6 + k_idle)`-wire (`rExt6Full ++ rPGIdle`) active-clean register inside `kFull80`. -/
def rExt6IdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (6 + k_idle) kFull80 :=
  rExt6Full.concat (rPGIdle k_idle hk) (hExt6_disj_PGIdle k_idle hk)

theorem hSum0_disj_Ext6 : rSum0.DisjointWires rExt6Full :=
  disjointWires_concat_right hSum0_disj_Ctrl3 hSum0_disj_Slack3

theorem hSum0_disj_Ext6Idle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rSum0.DisjointWires (rExt6IdleFull k_idle hk) :=
  disjointWires_concat_right hSum0_disj_Ext6 (hSum0_disj_PGIdle k_idle hk)

/-- Combined `(42 + k_idle)`-wire (`rSum0 ++ rPGIdle`) post-twist register for `dSelectCtrl`. -/
def rExt42IdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (42 + k_idle) kFull80 :=
  rSum0.concat (rPGIdle k_idle hk) (hSum0_disj_PGIdle k_idle hk)

/-- Combined `(42 + (6 + k_idle))`-wire (`rSum0 ++ rExt6IdleFull`) post-twist register for
  `dSelectCat`. -/
def rExt48IdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (42 + (6 + k_idle)) kFull80 :=
  rSum0.concat (rExt6IdleFull k_idle hk) (hSum0_disj_Ext6Idle k_idle hk)

/-- `(mWork + k_idle)`-wire clean workspace (`148w` at `mWork = 137, k_idle = 11`) for
  `dTwistCtrl`. -/
def rWorkCtrlTwist {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : QRegister (mWork + k_idle) n :=
  rWork.concat (rAct.compose (rPGIdle k_idle hk)) (QRegExt.disjointWires_symm (hDisj.compose_left
    (rPGIdle k_idle hk)))

/-- `(mWork + (6 + k_idle))`-wire clean workspace (`154w` at `mWork = 137, k_idle = 11`) shared by
post-`cHadIdle` `dStreamInit`/`dStreamUninit`, `GuardWrap`, and `dTwistCat`. -/
def rWorkGuardExt {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : QRegister
    (mWork + (6 + k_idle)) n := rWork.concat (rAct.compose (rExt6IdleFull k_idle hk))
    (QRegExt.disjointWires_symm (hDisj.compose_left (rExt6IdleFull k_idle hk)))

noncomputable def pCtrl3ZeroOrig : Operator (2 ^ kActOrig) :=
  rUnusedCtrl3Orig.basisOutcomeProjector 0

/-- All-`|0⟩` projector on `rUnusedCtrl3Full` inside `kFull80`. -/
noncomputable def pCtrl3Zero : Operator (2 ^ kFull80) :=
  rUnusedCtrl3Full.basisOutcomeProjector 0

/-- All-`|0⟩` projector on `rSlack3Orig` inside `kActOrig`. -/
noncomputable def pSlack3ZeroOrig : Operator (2 ^ kActOrig) :=
  rSlack3Orig.basisOutcomeProjector 0

/-- All-`|0⟩` projector on `rSlack3Full` inside `kFull80`. -/
noncomputable def pSlack3Zero : Operator (2 ^ kFull80) := rSlack3Full.basisOutcomeProjector 0

/-- All-`|0⟩` projector on `rPGIdleOrig k_idle hk` inside `kActOrig`. -/
noncomputable def pPGIdleZeroOrig (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kActOrig) :=
  (rPGIdleOrig k_idle hk).basisOutcomeProjector 0

/-- All-`|0⟩` projector on `rPGIdle k_idle hk` inside `kFull80`. -/
noncomputable def pPGIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rPGIdle k_idle hk).basisOutcomeProjector 0

/-- Combined `6`-wire all-`|0⟩` projector `rExt6Full.basisOutcomeProjector 0`. -/
noncomputable def pExt6Zero : Operator (2 ^ kFull80) := rExt6Full.basisOutcomeProjector 0

/-- Combined `(6 + k_idle)`-wire all-`|0⟩` projector `(rExt6IdleFull k_idle
  hk).basisOutcomeProjector 0`. -/
noncomputable def pExt6IdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rExt6IdleFull k_idle hk).basisOutcomeProjector 0

noncomputable def pZeroInitExt (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rExt48IdleFull k_idle hk).basisOutcomeProjector 0

/-- Active segment-boundary invariant operator `E_stream42 * pExt6IdleZero k_idle hk`. -/
noncomputable def E_segExt (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  E_stream42 * pExt6IdleZero k_idle hk

theorem pExt6Zero_eq_mul : pExt6Zero = pCtrl3Zero * pSlack3Zero :=
  basisOutcomeProjector_concat_zero rUnusedCtrl3Full rSlack3Full hCtrl3_disj_Slack3

theorem pExt6IdleZero_eq_mul (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pExt6IdleZero k_idle hk = pExt6Zero * pPGIdleZero k_idle hk :=
  basisOutcomeProjector_concat_zero rExt6Full (rPGIdle k_idle hk) (hExt6_disj_PGIdle k_idle hk)

theorem pZeroInitExt_eq_mul (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pZeroInitExt k_idle hk = pSum42Zero * pExt6IdleZero k_idle hk :=
  basisOutcomeProjector_concat_zero rSum0 (rExt6IdleFull k_idle hk) (hSum0_disj_Ext6Idle k_idle hk)

theorem RealizesOnProj.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {E_in : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)}
    {d : DynamicCircuit Var n} (hEq : U₁.1 * E_in = U₂.1 * E_in)
    (hd : RealizesOnProj E_in U₁ d) : RealizesOnProj E_in U₂ d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  have hEqH : E_inᴴ * U₁.1ᴴ = E_inᴴ * U₂.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hEq
  calc
    E_inᴴ * M'.1.1 * E_in = (E_inᴴ * U₁.1ᴴ) * M.1.1 * (U₁.1 * E_in) := by
        simpa only [Matrix.mul_assoc] using hproj
    _ = (E_inᴴ * U₂.1ᴴ) * M.1.1 * (U₂.1 * E_in) := by rw [hEqH, hEq]
    _ = E_inᴴ * (U₂.1ᴴ * M.1.1 * U₂.1) * E_in := by simp only [Matrix.mul_assoc]

/-- `M : Operator (2 ^ n)` acts trivially on `r : QRegister k n`, commuting with every operator
embedded on `r` (including both `r.basisOutcomeProjector 0` and `H^{⊗ k}`). -/
def CommutesWithReg {k n : ℕ} (r : QRegister k n) (M : Operator (2 ^ n)) : Prop :=
  ∀ B : Operator (2 ^ k), M * r.embedMatrix B = r.embedMatrix B * M

theorem CommutesWithReg.one {k n : ℕ} (r : QRegister k n) :
    CommutesWithReg r (1 : Operator (2 ^ n)) := fun B ↦ by simp

theorem CommutesWithReg.mul {k n : ℕ} {r : QRegister k n} {A C : Operator (2 ^ n)}
    (hA : CommutesWithReg r A) (hC : CommutesWithReg r C) :
    CommutesWithReg r (A * C) := fun B ↦ by
  rw [Matrix.mul_assoc, hC B, ← Matrix.mul_assoc, hA B, Matrix.mul_assoc]

theorem CommutesWithReg.conjTranspose {k n : ℕ} {r : QRegister k n} {M : Operator (2 ^ n)}
    (hM : CommutesWithReg r M) : CommutesWithReg r Mᴴ := fun B ↦ by
  simpa only [Matrix.conjTranspose_mul, QRegister.embedMatrix_conjTranspose,
    Matrix.conjTranspose_conjTranspose] using (congrArg Matrix.conjTranspose (hM Bᴴ)).symm

theorem CommutesWithReg.of_disjoint {k m n : ℕ} {s : QRegister m n} {r : QRegister k n}
    (hsr : s.DisjointWires r) (A : Operator (2 ^ m)) : CommutesWithReg r (s.embedMatrix A) :=
    fun B ↦ s.embedMatrix_comm_of_disjoint r hsr A B

theorem CommutesWithReg.embedMatrix {k m n : ℕ} (s : QRegister m n) {loc : QRegister k m}
    {A : Operator (2 ^ m)} (hA : CommutesWithReg loc A) :
    CommutesWithReg (s.compose loc) (s.embedMatrix A) := fun B ↦ by
  rw [QRegister.embedMatrix_compose, ← QRegister.embedMatrix_mul,
    ← QRegister.embedMatrix_mul, hA B]

theorem CommutesWithReg.comm_basisOutcomeProjector {k n : ℕ} {r : QRegister k n}
    {M : Operator (2 ^ n)} (hM : CommutesWithReg r M) (x : Fin (2 ^ k)) : M *
    r.basisOutcomeProjector x = r.basisOutcomeProjector x * M := hM (compProj x)

open Classical in
theorem CommutesWithReg.apply_eq_zero_of_extractIndex_ne {m k : ℕ} {rDrop : QRegister m k}
    {M : Operator (2 ^ k)} (hComm : CommutesWithReg rDrop M) {x y : Fin (2 ^ k)}
    (hne : rDrop.extractIndex x ≠ rDrop.extractIndex y) : M x y = 0 := by
  have hEq := congrFun (congrFun (hComm.comm_basisOutcomeProjector (rDrop.extractIndex x)) x) y
  rw [rDrop.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    ite_eq_right hne.symm, ite_eq_left rfl, mul_zero, one_mul] at hEq
  exact hEq.symm

open Classical in
theorem CommutesWithReg.apply_replaceIndex_eq {m k : ℕ} {rDrop : QRegister m k}
    {M : Operator (2 ^ k)} (hComm : CommutesWithReg rDrop M) {x y : Fin (2 ^ k)}
    (heq : rDrop.extractIndex x = rDrop.extractIndex y) (u : Fin (2 ^ m)) :
    M (rDrop.replaceIndex x u) (rDrop.replaceIndex y u) = M x y := by
  let v := rDrop.extractIndex x
  let B : Operator (2 ^ m) := Matrix.single u v (1 : ℂ)
  let x' := rDrop.replaceIndex x u
  let y' := rDrop.replaceIndex y u
  have hMat := congrFun (congrFun (hComm B) x') y
  have hLHS : (M * rDrop.embedMatrix B) x' y = M x' y' := by
    rw [Matrix.mul_apply, Finset.sum_eq_single y']
    · rw [QRegister.embedMatrix_apply, rDrop.extractIndex_replaceIndex, ← heq]
      dsimp only [B, v]
      rw [Matrix.single_apply_same, one_mul,
        show (rDrop.basisSplitEquiv y').2 = (rDrop.basisSplitEquiv y).2 by
          simp [y', QRegister.basisSplitEquiv_replaceIndex],
        ite_eq_left rfl, mul_one]
    · intro z _ hzy
      rw [QRegister.embedMatrix_apply]
      by_cases hzv : rDrop.extractIndex z = u ∧
          (rDrop.basisSplitEquiv z).2 = (rDrop.basisSplitEquiv y).2
      · exfalso; apply hzy; apply rDrop.basisSplitEquiv.injective
        rw [QRegister.basisSplitEquiv_replaceIndex]
        exact Prod.ext (by simpa using hzv.1) hzv.2
      · rcases not_and_or.mp hzv with hzu | henv
        · have hB0 : B (rDrop.extractIndex z) (rDrop.extractIndex y) = 0 := by
            simp only [B, Matrix.single_apply,
              show ¬(u = rDrop.extractIndex z ∧ v = rDrop.extractIndex y) from
                fun h ↦ hzu h.1.symm, ↓reduceIte]
          rw [hB0, zero_mul, mul_zero]
        · rw [ite_eq_right henv, mul_zero, mul_zero]
    · intro hy; exact (hy (Finset.mem_univ y')).elim
  have hRHS : (rDrop.embedMatrix B * M) x' y = M x y := by
    rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · rw [QRegister.embedMatrix_apply, show rDrop.extractIndex x' = u from
          rDrop.extractIndex_replaceIndex x u]
      dsimp only [B, v]
      rw [Matrix.single_apply_same, one_mul,
        show (rDrop.basisSplitEquiv x').2 = (rDrop.basisSplitEquiv x).2 by
          simp [x', QRegister.basisSplitEquiv_replaceIndex],
        ite_eq_left rfl, one_mul]
    · intro z _ hzx
      rw [QRegister.embedMatrix_apply, show rDrop.extractIndex x' = u from
          rDrop.extractIndex_replaceIndex x u]
      by_cases hzv : rDrop.extractIndex z = v ∧
          (rDrop.basisSplitEquiv x').2 = (rDrop.basisSplitEquiv z).2
      · exfalso; apply hzx; apply rDrop.basisSplitEquiv.injective
        have henv : (rDrop.basisSplitEquiv x).2 = (rDrop.basisSplitEquiv z).2 := by
          simpa [x', QRegister.basisSplitEquiv_replaceIndex] using hzv.2
        exact Prod.ext (by simpa [v] using hzv.1) henv.symm
      · rcases not_and_or.mp hzv with hzv' | henv
        · have hB0 : B u (rDrop.extractIndex z) = 0 := by
            dsimp only [B]
            rw [Matrix.single_apply, ite_eq_right (fun h ↦ hzv' h.2.symm)]
          rw [hB0, zero_mul, zero_mul]
        · rw [ite_eq_right henv, mul_zero, zero_mul]
    · intro hx; exact (hx (Finset.mem_univ x)).elim
  exact hLHS.symm.trans (hMat.trans hRHS)

open Classical in
/-- Universal register-replacement theorem: if `r₁, r₂ : QRegister k n` agree outside `rDrop`
and `M` commutes with every operator on `rDrop`, then `r₁.embedMatrix M = r₂.embedMatrix M`
as exact matrices on all of `2 ^ n` (requiring zero ancilla projector on `rDrop`). -/
theorem embedMatrix_eq_of_commutesWithReg {m k n : ℕ} (r₁ r₂ : QRegister k n)
    (rDrop : QRegister m k) (M : Operator (2 ^ k))
    (hAgree : ∀ l : Fin k, l ∉ Set.range rDrop.wires → r₁ l = r₂ l)
    (hComm : CommutesWithReg rDrop M) : r₁.embedMatrix M = r₂.embedMatrix M := by
  ext i j
  rw [QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside]
  have hOut_dir {ra rb : QRegister k n}
      (ha : rDrop.extractIndex (ra.extractIndex i) = rDrop.extractIndex (ra.extractIndex j))
      (hag : ∀ l : Fin k, l ∉ Set.range rDrop.wires → ra l = rb l)
      (hOut : ra.AgreeOutside i j) : rb.AgreeOutside i j := fun q hq2 ↦ by
    by_cases hq1 : q ∈ Set.range ra.wires
    · obtain ⟨l, rfl⟩ := hq1
      have hl : l ∈ Set.range rDrop.wires := by
        by_contra hnl
        exact hq2 ⟨l, (hag l hnl).symm⟩
      obtain ⟨a, rfl⟩ := hl
      simpa only [QRegister.basisBits_extractIndex] using congrFun (congrArg (basisBits m) ha) a
    · exact hOut q hq1
  have hno_of {ra rb : QRegister k n}
      (ha : rDrop.extractIndex (ra.extractIndex i) = rDrop.extractIndex (ra.extractIndex j))
      (hb : rDrop.extractIndex (rb.extractIndex i) ≠ rDrop.extractIndex (rb.extractIndex j))
      (hag : ∀ l : Fin k, l ∉ Set.range rDrop.wires → ra l = rb l) : ¬ ra.AgreeOutside i j := by
    intro hOut
    apply hb
    apply (basisBitsEquiv m).injective
    funext a
    change basisBits m _ a = basisBits m _ a
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    by_cases hmem : rb (rDrop a) ∈ Set.range ra.wires
    · obtain ⟨l, hl⟩ := hmem
      have hlin : l ∈ Set.range rDrop.wires := by
        by_contra hnl
        exact hnl ⟨a, (rb.wires.injective ((hag l hnl).symm.trans hl)).symm⟩
      obtain ⟨b, rfl⟩ := hlin
      rw [← hl]
      simpa only [QRegister.basisBits_extractIndex] using congrFun (congrArg (basisBits m) ha) b
    · exact hOut (rb (rDrop a)) hmem
  by_cases h1 : rDrop.extractIndex (r₁.extractIndex i) = rDrop.extractIndex (r₁.extractIndex j)
  · by_cases h2 : rDrop.extractIndex (r₂.extractIndex i) = rDrop.extractIndex (r₂.extractIndex j)
    · have hOutIff : r₁.AgreeOutside i j ↔ r₂.AgreeOutside i j :=
        ⟨hOut_dir h1 hAgree, hOut_dir h2 fun l hl ↦ (hAgree l hl).symm⟩
      have hRepEq (g : Fin (2 ^ n)) :
          rDrop.replaceIndex (r₁.extractIndex g) 0 = rDrop.replaceIndex (r₂.extractIndex g) 0 := by
        apply (basisBitsEquiv k).injective
        funext l
        change basisBits k _ l = basisBits k _ l
        by_cases hl : l ∈ Set.range rDrop.wires
        · obtain ⟨a, rfl⟩ := hl
          rw [rDrop.basisBits_replaceIndex_apply, rDrop.basisBits_replaceIndex_apply]
        · rw [rDrop.basisBits_replaceIndex_of_not_mem _ _ l hl,
            rDrop.basisBits_replaceIndex_of_not_mem _ _ l hl,
            QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hAgree l hl]
      have hMEq : M (r₁.extractIndex i) (r₁.extractIndex j) =
          M (r₂.extractIndex i) (r₂.extractIndex j) := by
        rw [← hComm.apply_replaceIndex_eq h1 0, ← hComm.apply_replaceIndex_eq h2 0,
          hRepEq i, hRepEq j]
      by_cases ho : r₁.AgreeOutside i j
      · rw [ite_eq_left ho, ite_eq_left (hOutIff.mp ho), hMEq]
      · rw [ite_eq_right ho, ite_eq_right (mt hOutIff.mpr ho), mul_zero, mul_zero]
    · rw [hComm.apply_eq_zero_of_extractIndex_ne h2, zero_mul, ite_eq_right (hno_of h1 h2 hAgree),
        mul_zero]
  · rw [hComm.apply_eq_zero_of_extractIndex_ne h1, zero_mul]
    by_cases h2 : rDrop.extractIndex (r₂.extractIndex i) = rDrop.extractIndex (r₂.extractIndex j)
    · rw [ite_eq_right (hno_of h2 h1 fun l hl ↦ (hAgree l hl).symm), mul_zero]
    · rw [hComm.apply_eq_zero_of_extractIndex_ne h2, zero_mul]

open Classical in
theorem embedUnitary_eq_of_commutesWithReg {m k n : ℕ} (r₁ r₂ : QRegister k n)
    (rDrop : QRegister m k) (U : Unitary (2 ^ k))
    (hAgree : ∀ l : Fin k, l ∉ Set.range rDrop.wires → r₁ l = r₂ l)
    (hComm : CommutesWithReg rDrop U.1) : r₁.embedUnitary U = r₂.embedUnitary U := by
  ext i j
  exact congrFun (congrFun (embedMatrix_eq_of_commutesWithReg r₁ r₂ rDrop U.1 hAgree hComm) i) j

/- ## Section 2: `0-T` `cHadIdle` Cancellation on `rPGIdle` (`k_idle ≤ 28`) & `Stream42ExtInitSpec`
-/

/-- Hadamard wall on the low `k_idle` wires `[0 .. k_idle)` of a `48`-wire catalyst register. -/
def cHadIdle48 (k_idle : ℕ) (hk : k_idle ≤ 48) : Circuit 48 :=
  Circuit.sequence (List.ofFn fun q : Fin k_idle ↦ Circuit.H ⟨q.val, by omega⟩)

/-- Hadamard wall on `rPGIdleOrig k_idle hk` inside `kActOrig = 4,086`. -/
def cHadIdleOrig (k_idle : ℕ) (hk : k_idle ≤ 48) : Circuit kActOrig :=
  Circuit.onRegister rPG48Orig (cHadIdle48 k_idle hk)

/-- Unitary evaluated by `cHadIdleOrig k_idle hk` on `kActOrig`. -/
noncomputable def uHadIdleOrig (k_idle : ℕ) (hk : k_idle ≤ 48) : Unitary (2 ^ kActOrig) :=
  (cHadIdleOrig k_idle hk).eval

/-- Unitary evaluated by `cHadIdleOrig k_idle hk` embedded into `kFull80`. -/
noncomputable def uHadIdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : Unitary (2 ^ kFull80) :=
  rAct0.embedUnitary (uHadIdleOrig k_idle hk)

/-- Zero-`TOFF`, zero-`T` dynamic `cHadIdleOrig` circuit on `(rAct, rWork)` (`1 ≤ mWork`). -/
def cHadIdleDyn {Var : Type} {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48) (hm1 : 1 ≤ mWork)
    (v : Var) (rAct : QRegister kActOrig n) (rWork : QRegister mWork n) : DynamicCircuit Var n
    := substActiveSingleCat hm1 v rAct rWork (cHadIdleOrig k_idle hk)

/-- Zero-`TOFF`, zero-`T` dynamic inverse `cHadIdleOrig` circuit on `(rAct, rWork)` (`1 ≤
  mWork`). -/
def cHadIdleInvDyn {Var : Type} {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (hm1 : 1 ≤ mWork) (v : Var)
    (rAct : QRegister kActOrig n) (rWork : QRegister mWork n) : DynamicCircuit Var n :=
  substActiveSingleCat hm1 v rAct rWork (cHadIdleOrig k_idle hk).inverse

theorem count_toff_cHadIdle48 (k_idle : ℕ) (hk : k_idle ≤ 48) :
    (cHadIdle48 k_idle hk).count .TOFF = 0 := by
  rw [cHadIdle48, Circuit.count_sequence, List.map_ofFn, List.sum_ofFn]
  simp [Circuit.H, Circuit.single]

theorem count_t_cHadIdle48 (k_idle : ℕ) (hk : k_idle ≤ 48) :
    (cHadIdle48 k_idle hk).count .T = 0 := by
  rw [cHadIdle48, Circuit.count_sequence, List.map_ofFn, List.sum_ofFn]
  simp [Circuit.H, Circuit.single]

theorem count_t_cHadIdleDyn {Var : Type} {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (hm1 : 1 ≤ mWork) (v : Var) (rAct : QRegister kActOrig n) (rWork : QRegister mWork n) :
    (cHadIdleDyn k_idle hk hm1 v rAct rWork).count .T = 0 := by
  refine Nat.eq_zero_of_le_zero ((substActiveSingleCat_count_T_le hm1 v rAct rWork _).trans ?_)
  simp [cHadIdleOrig, Circuit.count_onRegister, count_t_cHadIdle48, count_toff_cHadIdle48]

theorem count_t_cHadIdleInvDyn {Var : Type} {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (hm1 : 1 ≤ mWork) (v : Var) (rAct : QRegister kActOrig n) (rWork : QRegister mWork n) :
    (cHadIdleInvDyn k_idle hk hm1 v rAct rWork).count .T = 0 := by
  refine Nat.eq_zero_of_le_zero ((substActiveSingleCat_count_T_le hm1 v rAct rWork _).trans ?_)
  rw [Circuit.count_inverse_of_ne .T (by decide) (by decide),
    Circuit.count_inverse_of_ne .TOFF (by decide) (by decide)]
  simp [cHadIdleOrig, Circuit.count_onRegister, count_t_cHadIdle48, count_toff_cHadIdle48]

theorem singleton_disj_of_ne {n : ℕ} {w₁ w₂ : Wire n} (hne : w₁ ≠ w₂) :
    (QRegister.singleton w₁).DisjointWires (QRegister.singleton w₂) := by
  rw [QRegister.disjoint_iff]
  intro i j hij; fin_cases i; fin_cases j
  exact hne hij

theorem commutesWithReg_sequence_all {n : ℕ} (w : Wire n) :
    ∀ (cs : List (Circuit n)),
      (∀ c ∈ cs, CommutesWithReg (QRegister.singleton w) c.eval.1) →
      CommutesWithReg (QRegister.singleton w) (Circuit.sequence cs).eval.1
  | [], _ => by
      have h0 : Circuit.sequence ([] : List (Circuit n)) = .identity := rfl
      rw [h0, Circuit.eval_identity]
      exact CommutesWithReg.one _
  | c :: cs, h => by
      rw [Circuit.sequence_cons, Circuit.eval_seq, Submonoid.coe_mul]
      exact (commutesWithReg_sequence_all w cs (fun x hx ↦ h x (List.mem_cons_of_mem c hx))).mul
        (h c List.mem_cons_self)

theorem sequence_ofFn_extract_single {m n : ℕ} (w : Wire n) (U₀ : Operator 2)
    (f : Fin m → Circuit n) (idx : Fin m)
    (hOther : ∀ j : Fin m, j ≠ idx → CommutesWithReg (QRegister.singleton w) (f j).eval.1)
    (hIdx : (f idx).eval.1 = (QRegister.singleton w).embedMatrix U₀) :
    ∃ M : Operator (2 ^ n), CommutesWithReg (QRegister.singleton w) M ∧
      (Circuit.sequence (List.ofFn f)).eval.1 = M * (QRegister.singleton w).embedMatrix U₀ ∧
      (Circuit.sequence (List.ofFn f)).eval.1 = (QRegister.singleton w).embedMatrix U₀ * M := by
  induction m with
  | zero => exact Fin.elim0 idx
  | succ m ih =>
      rw [List.ofFn_succ, Circuit.sequence_cons, Circuit.eval_seq, Submonoid.coe_mul]
      rcases Fin.eq_zero_or_eq_succ idx with rfl | ⟨idx', rfl⟩
      · have hAll : ∀ c ∈ List.ofFn (fun i : Fin m ↦ f i.succ),
            CommutesWithReg (QRegister.singleton w) c.eval.1 := by
          intro c hc
          obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
          exact hOther i.succ (Fin.succ_ne_zero i)
        let M := (Circuit.sequence (List.ofFn fun i : Fin m ↦ f i.succ)).eval.1
        have hM : CommutesWithReg (QRegister.singleton w) M :=
          commutesWithReg_sequence_all w _ hAll
        exact ⟨M, hM, by rw [hIdx], by rw [hIdx, hM U₀]⟩
      · obtain ⟨M', hM', hR, hL⟩ := ih (fun i ↦ f i.succ) idx'
          (fun j hj ↦ hOther j.succ (fun h ↦ hj (Fin.succ_inj.mp h))) hIdx
        have hf0 : CommutesWithReg (QRegister.singleton w) (f 0).eval.1 :=
          hOther 0 (Fin.succ_ne_zero idx').symm
        refine ⟨M' * (f 0).eval.1, hM'.mul hf0, ?_, ?_⟩
        · rw [hR, Matrix.mul_assoc, ← hf0 U₀, ← Matrix.mul_assoc]
        · rw [hL, Matrix.mul_assoc]

open Classical in
theorem comm_block0_proj_of_comm_singletons {n : ℕ} (M : Operator (2 ^ n)) :
    ∀ (m : ℕ) (hm : m ≤ n),
      (∀ q : Fin m, CommutesWithReg (QRegister.singleton ⟨q.val, by omega⟩) M) →
      M * (QRegister.block 0 m (fullSys_zero_add_le_of_le hm)).basisOutcomeProjector 0 =
        (QRegister.block 0 m (fullSys_zero_add_le_of_le hm)).basisOutcomeProjector 0 * M
  | 0, hm, _ => by
      have h0 : (QRegister.block 0 0 (fullSys_zero_add_le_of_le hm)).basisOutcomeProjector 0 = 1 :=
        by
        rw [QRegister.basisOutcomeProjector_eq_diagonal]
        ext i j
        by_cases hij : i = j
        · subst hij
          have hext : (QRegister.block 0 0 (fullSys_zero_add_le_of_le hm)).extractIndex i = 0 :=
            Fin.ext (by
              have hlt := ((QRegister.block 0 0 (fullSys_zero_add_le_of_le hm)).extractIndex i).isLt
              change _ < 1 at hlt; omega)
          rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ite_eq_left hext]
        · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      rw [h0, mul_one, one_mul]
  | m + 1, hm, hAll => by
      let rL : QRegister m n := QRegister.block 0 m (by omega)
      let rR : QRegister 1 n := QRegister.singleton ⟨m, by omega⟩
      have hLR : rL.DisjointWires rR := disj_of_val_ne fun i j ↦ by
        fin_cases j; simp [rL, rR, QRegister.singleton]; omega
      have hEq : QRegister.block 0 (m + 1) (fullSys_zero_add_le_of_le hm) = rL.concat rR hLR := by
        apply qreg_ext; intro idx
        refine Fin.addCases (m := m) (n := 1)
          (motive := fun idx ↦
            QRegister.block 0 (m + 1) (fullSys_zero_add_le_of_le hm) idx = (rL.concat rR hLR) idx)
          (fun i ↦ by rw [QRegister.concat_apply_left]; ext; simp [rL])
          (fun j ↦ by fin_cases j; rw [QRegister.concat_apply_right]; ext; simp [rR])
          idx
      rw [hEq, basisOutcomeProjector_concat_zero]
      have hL_comm := comm_block0_proj_of_comm_singletons M m (by omega)
        (fun q ↦ hAll ⟨q.val, by omega⟩)
      have hR_comm := (hAll ⟨m, by omega⟩).comm_basisOutcomeProjector 0
      rw [← Matrix.mul_assoc, hL_comm, Matrix.mul_assoc, hR_comm, ← Matrix.mul_assoc]

theorem rCatTotInSingleCat80_eq_rPG48Orig : rCatTotInSingleCat 80 48 40 = rPG48Orig := by
  apply qreg_ext
  decide

noncomputable def pZeroExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (pZeroInitExt k_idle hk) * rWork.basisOutcomeProjector 0

/-- Segment-boundary invariant operator `rAct.embedMatrix (E_segExt k_idle hk) * |0_work⟩⟨0|` on
  `(rAct, rWork)`. -/
noncomputable def pHoistExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_segExt k_idle hk) * rWork.basisOutcomeProjector 0

/-- Post-`cHadIdle` stream setup/teardown bundle on `(rAct, rWork)` intertwining `pZeroExtOn`
and `pHoistExtOn` (`0` `.TOFF`, `.T` pair `≤ tStreamPair`). -/
structure Stream42ExtInitSpec (mWork k_idle : ℕ) (hk : k_idle ≤ 48)
    (tStreamPair : ℕ) where
  uStreamInit : Unitary (2 ^ kFull80)
  hMulPSum42Zero : uStreamInit.1 * pSum42Zero = E_stream42
  dStreamInit : ∀ {Var : Type} {n : ℕ}, Var →
    (rAct : QRegister kFull80 n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  dStreamUninit : ∀ {Var : Type} {n : ℕ}, Var →
    (rAct : QRegister kFull80 n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  hToffInit : ∀ {Var : Type} {n : ℕ} (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dStreamInit v rAct rWork hD).count .TOFF = 0
  hToffUninit : ∀ {Var : Type} {n : ℕ} (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dStreamUninit v rAct rWork hD).count .TOFF = 0
  hTSum : ∀ {Var : Type} {n : ℕ} (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dStreamInit v rAct rWork hD).count .T +
      (dStreamUninit v rAct rWork hD).count .T ≤ tStreamPair
  hRealInit : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hD : rAct.DisjointWires rWork),
    RealizesOnProj (pZeroExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary uStreamInit) (dStreamInit v rAct rWork hD)
  hRealUninit : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hD : rAct.DisjointWires rWork),
    RealizesOnProj (pHoistExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary uStreamInit⁻¹) (dStreamUninit v rAct rWork hD)

theorem uStreamInit_inv_mul_E_segExt {mWork k_idle tStreamPair : ℕ} (hk : k_idle ≤ 48)
    (initSpec : Stream42ExtInitSpec mWork k_idle hk tStreamPair) :
    (initSpec.uStreamInit⁻¹).1 * E_segExt k_idle hk = pZeroInitExt k_idle hk := by
  unfold E_segExt
  have hInv : (initSpec.uStreamInit⁻¹).1 * E_stream42 = pSum42Zero := by
    rw [← initSpec.hMulPSum42Zero, ← Matrix.mul_assoc, ← Submonoid.coe_mul,
      inv_mul_cancel, OneMemClass.coe_one, one_mul]
  rw [← Matrix.mul_assoc, hInv, ← pZeroInitExt_eq_mul]

theorem CommutesWithReg.compose {a k n : ℕ} {r : QRegister k n} (loc : QRegister a k)
    {M : Operator (2 ^ n)} (hM : CommutesWithReg r M) :
    CommutesWithReg (r.compose loc) M := fun B ↦ by
  rw [QRegister.embedMatrix_compose]
  exact hM (loc.embedMatrix B)

open Classical in
theorem embedMatrix_add_poly {k n : ℕ} (r : QRegister k n) (A B : Operator (2 ^ k)) :
    r.embedMatrix (A + B) = r.embedMatrix A + r.embedMatrix B := by
  ext i j
  simp only [QRegister.embedMatrix_apply, Matrix.add_apply]
  split_ifs <;> ring

open Classical in
theorem embedMatrix_smul_poly {k n : ℕ} (r : QRegister k n) (c : ℂ) (A : Operator (2 ^ k)) :
    r.embedMatrix (c • A) = c • r.embedMatrix A := by
  ext i j
  simp only [QRegister.embedMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem embedMatrix_sum_poly {ι : Type*} {k n : ℕ} (r : QRegister k n) (s : Finset ι)
    (f : ι → Operator (2 ^ k)) :
    r.embedMatrix (∑ x ∈ s, f x) = ∑ x ∈ s, r.embedMatrix (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext i j
      simp [QRegister.embedMatrix_apply]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, embedMatrix_add_poly, ih, Finset.sum_insert ha]

open Classical in
theorem embedMatrix_single_concat {m₁ m₂ n : ℕ}
    (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n) (hD : r₁.DisjointWires r₂)
    (u v : Fin (2 ^ (m₁ + m₂))) :
    let loc₁ : QRegister m₁ (m₁ + m₂) := QRegister.block 0 m₁ (by omega)
    let loc₂ : QRegister m₂ (m₁ + m₂) := QRegister.block m₁ m₂ (by omega)
    (r₁.concat r₂ hD).embedMatrix (Matrix.single u v (1 : ℂ)) =
      r₁.embedMatrix (Matrix.single (loc₁.extractIndex u) (loc₁.extractIndex v) (1 : ℂ)) *
        r₂.embedMatrix (Matrix.single (loc₂.extractIndex u) (loc₂.extractIndex v) (1 : ℂ)) := by
  intro loc₁ loc₂
  let r := r₁.concat r₂ hD
  let u₁ := loc₁.extractIndex u
  let v₁ := loc₁.extractIndex v
  let u₂ := loc₂.extractIndex u
  let v₂ := loc₂.extractIndex v
  have hcomp₁ : r.compose loc₁ = r₁ := by
    apply qreg_ext; intro a
    have hl : loc₁ a = Fin.castAdd m₂ a := Fin.ext (by simp [loc₁])
    change r (loc₁ a) = r₁ a
    rw [hl, QRegister.concat_apply_left]
  have hcomp₂ : r.compose loc₂ = r₂ := by
    apply qreg_ext; intro b
    have hl : loc₂ b = Fin.natAdd m₁ b := Fin.ext (by simp [loc₂])
    change r (loc₂ b) = r₂ b
    rw [hl, QRegister.concat_apply_right]
  have hextIff : ∀ (g : Fin (2 ^ n)) (w : Fin (2 ^ (m₁ + m₂))), r.extractIndex g = w ↔
      r₁.extractIndex g = loc₁.extractIndex w ∧ r₂.extractIndex g = loc₂.extractIndex w := by
    intro g w
    rw [← hcomp₁, ← hcomp₂, QRegister.extractIndex_compose, QRegister.extractIndex_compose]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      apply (basisBitsEquiv (m₁ + m₂)).injective; funext idx
      change basisBits (m₁ + m₂) (r.extractIndex g) idx = basisBits (m₁ + m₂) w idx
      refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) idx
      · have hl : loc₁ a = Fin.castAdd m₂ a := Fin.ext (by simp [loc₁])
        have hb := congrFun (congrArg (basisBits m₁) h1) a
        rw [loc₁.basisBits_extractIndex, loc₁.basisBits_extractIndex, hl] at hb
        exact hb
      · have hl : loc₂ b = Fin.natAdd m₁ b := Fin.ext (by simp [loc₂])
        have hb := congrFun (congrArg (basisBits m₂) h2) b
        rw [loc₂.basisBits_extractIndex, loc₂.basisBits_extractIndex, hl] at hb
        exact hb
  ext x y
  let z := r₂.replaceIndex y u₂
  rw [Matrix.mul_apply, Finset.sum_eq_single z]
  · have hz₂ : r₂.extractIndex z = u₂ := r₂.extractIndex_replaceIndex y u₂
    have hzEnv : r₂.AgreeOutside z y :=
      (r₂.basisSplit_environment_eq_iff z y).mp
        (by simp [z, QRegister.basisSplitEquiv_replaceIndex])
    have hr₁_not_r₂ : ∀ a : Fin m₁, r₁ a ∉ Set.range r₂.wires := by
      rintro a ⟨b, hb⟩
      exact QRegister.disjoint_iff.mp hD a b hb.symm
    have hr₂_not_r₁ : ∀ b : Fin m₂, r₂ b ∉ Set.range r₁.wires := by
      rintro b ⟨a, ha⟩
      exact QRegister.disjoint_iff.mp hD a b ha
    have hz₁ : r₁.extractIndex z = r₁.extractIndex y := by
      apply (basisBitsEquiv m₁).injective; funext a
      change basisBits m₁ (r₁.extractIndex z) a = basisBits m₁ (r₁.extractIndex y) a
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      exact hzEnv (r₁ a) (hr₁_not_r₂ a)
    have hOutIff : r₁.AgreeOutside x z ↔ (r₂.extractIndex x = u₂ ∧ r.AgreeOutside x y) := by
      constructor
      · intro ho₁
        refine ⟨?_, fun q hq ↦ ?_⟩
        · apply (basisBitsEquiv m₂).injective; funext b
          change basisBits m₂ (r₂.extractIndex x) b = basisBits m₂ u₂ b
          rw [QRegister.basisBits_extractIndex, ho₁ (r₂ b) (hr₂_not_r₁ b)]
          exact r₂.basisBits_replaceIndex_apply y u₂ b
        · have hq₁ : q ∉ Set.range r₁.wires := by
            rintro ⟨a, rfl⟩; exact hq ⟨Fin.castAdd m₂ a, QRegister.concat_apply_left r₁ r₂ hD a⟩
          have hq₂ : q ∉ Set.range r₂.wires := by
            rintro ⟨b, rfl⟩; exact hq ⟨Fin.natAdd m₁ b, QRegister.concat_apply_right r₁ r₂ hD b⟩
          exact (ho₁ q hq₁).trans (hzEnv q hq₂)
      · rintro ⟨hx₂, ho⟩ q hq₁
        by_cases hq₂ : q ∈ Set.range r₂.wires
        · obtain ⟨b, rfl⟩ := hq₂
          rw [r₂.basisBits_replaceIndex_apply, ← hx₂, QRegister.basisBits_extractIndex]
        · have hqr : q ∉ Set.range r.wires := by
            rintro ⟨idx, hidx⟩
            revert hidx
            refine Fin.addCases (fun a hidx ↦ hq₁ ⟨a, ?_⟩) (fun b hidx ↦ hq₂ ⟨b, ?_⟩) idx
            · exact (QRegister.concat_apply_left r₁ r₂ hD a).symm.trans hidx
            · exact (QRegister.concat_apply_right r₁ r₂ hD b).symm.trans hidx
          exact (ho q hqr).trans (hzEnv q hq₂).symm
    rw [QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside,
      QRegister.embedMatrix_apply_of_agreeOutside, hz₂, hz₁, ite_eq_left hzEnv, mul_one]
    simp only [Matrix.single_apply]
    by_cases hcond : u₁ = r₁.extractIndex x ∧ u₂ = r₂.extractIndex x ∧
        v₁ = r₁.extractIndex y ∧ v₂ = r₂.extractIndex y ∧ r.AgreeOutside x y
    · rcases hcond with ⟨hu₁, hu₂, hv₁, hv₂, hor⟩
      have hu : u = r.extractIndex x := ((hextIff x u).mpr ⟨hu₁.symm, hu₂.symm⟩).symm
      have hv : v = r.extractIndex y := ((hextIff y v).mpr ⟨hv₁.symm, hv₂.symm⟩).symm
      have ho₁ : r₁.AgreeOutside x z := hOutIff.mpr ⟨hu₂.symm, hor⟩
      rw [ite_eq_left ⟨hu, hv⟩, ite_eq_left hor, ite_eq_left ⟨hu₁, hv₁⟩, ite_eq_left ho₁,
        ite_eq_left ⟨rfl, hv₂⟩]
      ring
    · have hL : (if u = r.extractIndex x ∧ v = r.extractIndex y then (1 : ℂ) else 0) *
          (if r.AgreeOutside x y then (1 : ℂ) else 0) = 0 := by
        by_cases hor : r.AgreeOutside x y
        · rw [ite_eq_left hor, mul_one, ite_eq_right]
          rintro ⟨hu, hv⟩
          rcases (hextIff x u).mp hu.symm with ⟨hu₁, hu₂⟩
          rcases (hextIff y v).mp hv.symm with ⟨hv₁, hv₂⟩
          exact hcond ⟨hu₁.symm, hu₂.symm, hv₁.symm, hv₂.symm, hor⟩
        · rw [ite_eq_right hor, mul_zero]
      have hR : ((if u₁ = r₁.extractIndex x ∧ v₁ = r₁.extractIndex y then (1 : ℂ) else 0) *
          (if r₁.AgreeOutside x z then (1 : ℂ) else 0)) *
          (if u₂ = u₂ ∧ v₂ = r₂.extractIndex y then (1 : ℂ) else 0) = 0 := by
        by_cases h1 : u₁ = r₁.extractIndex x ∧ v₁ = r₁.extractIndex y
        · by_cases ho₁ : r₁.AgreeOutside x z
          · by_cases hv₂ : v₂ = r₂.extractIndex y
            · rcases hOutIff.mp ho₁ with ⟨hx₂, hor⟩
              exact (hcond ⟨h1.1, hx₂.symm, h1.2, hv₂, hor⟩).elim
            · rw [ite_eq_left h1, ite_eq_left ho₁, ite_eq_right (fun h ↦ hv₂ h.2), mul_zero]
          · rw [ite_eq_right ho₁, mul_zero, zero_mul]
        · rw [ite_eq_right h1, zero_mul, zero_mul]
      rw [hL, hR]
  · intro z' _ hzz'
    have hR0 : r₂.embedMatrix (Matrix.single u₂ v₂ (1 : ℂ)) z' y = 0 := by
      rw [QRegister.embedMatrix_apply]
      by_cases hz' : r₂.extractIndex z' = u₂ ∧
          (r₂.basisSplitEquiv z').2 = (r₂.basisSplitEquiv y).2
      · exfalso; apply hzz'; apply r₂.basisSplitEquiv.injective
        rw [show r₂.basisSplitEquiv z = (u₂, (r₂.basisSplitEquiv y).2) by
          simp [z, QRegister.basisSplitEquiv_replaceIndex]]
        exact Prod.ext hz'.1 hz'.2
      · rcases not_and_or.mp hz' with hne₂ | henv
        · rw [Matrix.single_apply, ite_eq_right (fun h ↦ hne₂ h.1.symm)]
          split_ifs <;> ring
        · rw [ite_eq_right henv, mul_zero]
    rw [hR0, mul_zero]
  · intro hz; exact (hz (Finset.mem_univ z)).elim

open Classical in
theorem commutesWithReg_concat {m₁ m₂ n : ℕ}
    (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n) (hD : r₁.DisjointWires r₂)
    {M : Operator (2 ^ n)}
    (h₁ : CommutesWithReg r₁ M) (h₂ : CommutesWithReg r₂ M) :
    CommutesWithReg (r₁.concat r₂ hD) M := fun A ↦ by
  let r := r₁.concat r₂ hD
  have hA : A = ∑ u : Fin (2 ^ (m₁ + m₂)), ∑ v : Fin (2 ^ (m₁ + m₂)),
      A u v • Matrix.single u v (1 : ℂ) := by
    ext p q
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
    rw [Finset.sum_eq_single p
        (fun u _ hu ↦ Finset.sum_eq_zero fun v _ ↦ by rw [ite_eq_right (fun h ↦ hu h.1), mul_zero])
        (fun hp ↦ (hp (Finset.mem_univ p)).elim),
      Finset.sum_eq_single q
        (fun v _ hv ↦ by rw [ite_eq_right (fun h ↦ hv h.2), mul_zero])
        (fun hq ↦ (hq (Finset.mem_univ q)).elim),
      ite_eq_left ⟨rfl, rfl⟩, mul_one]
  rw [hA, embedMatrix_sum_poly, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [embedMatrix_sum_poly, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [embedMatrix_smul_poly, mul_smul_comm, smul_mul_assoc,
    embedMatrix_single_concat r₁ r₂ hD u v]
  rw [← Matrix.mul_assoc, h₁ _, Matrix.mul_assoc, h₂ _, ← Matrix.mul_assoc]

theorem commutesWithReg_of_forall_singleton {m n : ℕ} (r : QRegister m n)
    {M : Operator (2 ^ n)} (h : ∀ q : Fin m, CommutesWithReg (QRegister.singleton (r q)) M) :
    CommutesWithReg r M := by
  induction m with
  | zero =>
      intro A
      have hSub : Subsingleton (Fin (2 ^ 0)) := ⟨fun a b ↦ Fin.ext (by omega)⟩
      have hA : A = A 0 0 • (1 : Operator (2 ^ 0)) := by
        ext i j
        rw [@Subsingleton.elim _ hSub i 0, @Subsingleton.elim _ hSub j 0]
        simp
      rw [hA, embedMatrix_smul_poly, r.embedMatrix_one, mul_smul_comm, smul_mul_assoc,
        mul_one, one_mul]
  | succ m ih =>
      let rInit : QRegister m n := r.slice 0 m (by omega)
      let rLast : QRegister 1 n := QRegister.singleton (r (Fin.last m))
      have hD : rInit.DisjointWires rLast :=
        disj_of_val_ne fun a b ↦ by
          fin_cases b
          have ha : rInit a = r ⟨a.val, by omega⟩ := congrArg r (Fin.ext (by simp))
          have hb : rLast ⟨0, by decide⟩ = r ⟨m, by omega⟩ :=
            congrArg r (Fin.ext (by simp [Fin.last]))
          rw [ha, hb]
          intro hEq
          have hv := congrArg Fin.val (r.wires.injective (Fin.ext hEq))
          have := a.isLt
          dsimp only at hv
          omega
      have hrEq : r = rInit.concat rLast hD := by
        apply qreg_ext; intro idx
        refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) idx
        · rw [QRegister.concat_apply_left]
          exact congrArg r (Fin.ext (by simp))
        · fin_cases b
          rw [QRegister.concat_apply_right]
          exact congrArg r (Fin.ext (by simp [Fin.last]))
      rw [hrEq]
      refine commutesWithReg_concat rInit rLast hD (ih rInit fun a ↦ ?_) (h (Fin.last m))
      have ha : rInit a = r ⟨a.val, by omega⟩ := congrArg r (Fin.ext (by simp))
      rw [ha]
      exact h ⟨a.val, by omega⟩

open Classical in
theorem commutesWithReg_fwdPermUnitary {m k : ℕ}
    (r : QRegister m k) (σ : Equiv.Perm (Fin (2 ^ k)))
    (hFix : ∀ x : Fin (2 ^ k), r.extractIndex (σ x) = r.extractIndex x)
    (hOut : ∀ x y : Fin (2 ^ k), r.AgreeOutside x y → r.AgreeOutside (σ x) (σ y))
    (hOutInv : ∀ x y : Fin (2 ^ k), r.AgreeOutside x y → r.AgreeOutside (σ.symm x) (σ.symm y)) :
    CommutesWithReg r (fwdPermUnitary σ).1 := fun A ↦ by
  change fwdPermMatrix σ * r.embedMatrix A = r.embedMatrix A * fwdPermMatrix σ
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm i)
      (fun x _ hx ↦ by
        rw [fwdPermMatrix_apply, ite_eq_right (fun h ↦ hx (σ.injective (by
          simpa using h))), zero_mul])
      (fun h ↦ (h (Finset.mem_univ _)).elim),
    fwdPermMatrix_apply, ite_eq_left (σ.apply_symm_apply i), one_mul,
    Matrix.mul_apply, Finset.sum_eq_single (σ j)
      (fun x _ hx ↦ by rw [fwdPermMatrix_apply, ite_eq_right hx.symm, mul_zero])
      (fun h ↦ (h (Finset.mem_univ _)).elim),
    fwdPermMatrix_apply, ite_eq_left rfl, mul_one,
    QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside]
  have hFixInv : r.extractIndex (σ.symm i) = r.extractIndex i := by
    have h0 := hFix (σ.symm i)
    rw [σ.apply_symm_apply] at h0
    exact h0.symm
  have hIff : r.AgreeOutside (σ.symm i) j ↔ r.AgreeOutside i (σ j) := by
    constructor
    · intro h
      have h1 := hOut (σ.symm i) j h
      rwa [σ.apply_symm_apply] at h1
    · intro h
      have h1 := hOutInv i (σ j) h
      rwa [σ.symm_apply_apply] at h1
  rw [hFixInv]
  by_cases ho : r.AgreeOutside (σ.symm i) j
  · rw [ite_eq_left ho, ite_eq_left (hIff.mp ho), hFix j]
  · rw [ite_eq_right ho, ite_eq_right (mt hIff.mpr ho), mul_zero, mul_zero]

theorem bitSplit43_decomp {s b y_lo H : ℕ} (hb : b < 2) (hylo : y_lo < 2 ^ s) :
    let N := b + 2 * (y_lo + 2 ^ s * H)
    N % 2 = b ∧
    (N / 2) / 2 ^ s = H ∧
    (∀ t : ℕ, t < s → (N / 2 ^ (1 + t)) % 2 = (y_lo / 2 ^ t) % 2) ∧
    (∀ u : ℕ, N / 2 ^ (1 + s + u) = H / 2 ^ u) := by
  intro N
  have hN2 : N / 2 = y_lo + 2 ^ s * H := by
    dsimp only [N]
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt hb, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [N]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  · rw [hN2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt hylo, zero_add]
  · intro t ht
    have hpow1 : 2 ^ (1 + t) = 2 * 2 ^ t := by rw [Nat.pow_add, pow_one]
    have hpow2 : 2 ^ s = 2 ^ t * 2 ^ (s - t) := by rw [← Nat.pow_add, Nat.add_sub_of_le ht.le]
    have hpow3 : 2 ^ (s - t) = 2 * 2 ^ (s - t - 1) := by
      have hpos : s - t = 1 + (s - t - 1) := by omega
      conv_lhs => rw [hpos, Nat.pow_add, pow_one]
    rw [hpow1, ← Nat.div_div_eq_div_mul, hN2, hpow2, mul_assoc,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos t), hpow3, mul_assoc, Nat.add_mul_mod_self_left]
  · intro u
    have hpow : 2 ^ (1 + s + u) = 2 * 2 ^ s * 2 ^ u := by
      rw [Nat.pow_add, Nat.pow_add, pow_one]
    rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hN2,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt hylo, zero_add]

open Classical in
theorem kickFun43_extract_and_outside {s θ₀ θ₁ : ℕ} (hs : s ≤ 42)
    (h₀ : 2 ^ s ∣ θ₀) (h₁ : 2 ^ s ∣ θ₁) :
    let rLowS : QRegister s (1 + 42) := QRegister.block 1 s (by omega)
    (∀ x : Fin (2 ^ (1 + 42)), rLowS.extractIndex (kickFun43 θ₀ θ₁ x) = rLowS.extractIndex x) ∧
    (∀ x z : Fin (2 ^ (1 + 42)), rLowS.AgreeOutside x z →
      rLowS.AgreeOutside (kickFun43 θ₀ θ₁ x) (kickFun43 θ₀ θ₁ z)) := by
  intro rLowS
  have hDecomp : ∀ x : Fin (2 ^ (1 + 42)), ∃ q : ℕ, (if x.val % 2 = 0 then θ₀ else θ₁) = 2 ^ s
      * q ∧ (kickFun43 θ₀ θ₁ x).val = (x.val % 2) + 2 * (((x.val / 2) % 2 ^ s) + 2 ^ s *
      ((((x.val / 2) / 2 ^ s) + q) % 2 ^ (42 - s))) := by
    intro x
    have hθ : 2 ^ s ∣ (if x.val % 2 = 0 then θ₀ else θ₁) := by
      by_cases hb : x.val % 2 = 0 <;> simp [hb, h₀, h₁]
    obtain ⟨q, hq⟩ := hθ
    refine ⟨q, hq, ?_⟩
    dsimp only [kickFun43]
    rw [hq]
    let y := x.val / 2
    let y_lo := y % 2 ^ s
    let y_hi := y / 2 ^ s
    let r := (y_hi + q) % 2 ^ (42 - s)
    let m := (y_hi + q) / 2 ^ (42 - s)
    have hylo : y_lo < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
    have hr : r < 2 ^ (42 - s) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hp42 : 2 ^ 42 = 2 ^ s * 2 ^ (42 - s) := by rw [← Nat.pow_add, Nat.add_sub_of_le hs]
    have hy : y = y_lo + 2 ^ s * y_hi := (Nat.mod_add_div y (2 ^ s)).symm
    have hyq : y_hi + q = r + 2 ^ (42 - s) * m := (Nat.mod_add_div (y_hi + q) (2 ^ (42 - s))).symm
    have hlt42 : y_lo + 2 ^ s * r < 2 ^ 42 := by
      have hle : 2 ^ s * r + 2 ^ s ≤ 2 ^ 42 := by
        calc
          2 ^ s * r + 2 ^ s = 2 ^ s * (r + 1) := by ring
          _ ≤ 2 ^ 42 := by
            rw [hp42]; exact Nat.mul_le_mul_left (2 ^ s) (Nat.succ_le_of_lt hr)
      omega
    have hsum : y + 2 ^ s * q = (y_lo + 2 ^ s * r) + 2 ^ 42 * m := by
      calc
        y + 2 ^ s * q = y_lo + 2 ^ s * (y_hi + q) := by rw [hy]; ring
        _ = y_lo + 2 ^ s * (r + 2 ^ (42 - s) * m) := by rw [hyq]
        _ = (y_lo + 2 ^ s * r) + (2 ^ s * 2 ^ (42 - s)) * m := by ring
        _ = (y_lo + 2 ^ s * r) + 2 ^ 42 * m := by rw [← hp42]
    change x.val % 2 + 2 * ((y + 2 ^ s * q) % 2 ^ 42) = x.val % 2 + 2 * (y_lo + 2 ^ s * r)
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt42]
  have hxForm : ∀ x : Fin (2 ^ (1 + 42)),
      x.val = (x.val % 2) + 2 * (((x.val / 2) % 2 ^ s) + 2 ^ s * ((x.val / 2) / 2 ^ s)) := by
    intro x
    have hy : x.val / 2 = (x.val / 2) % 2 ^ s + 2 ^ s * ((x.val / 2) / 2 ^ s) :=
      (Nat.mod_add_div (x.val / 2) (2 ^ s)).symm
    have hx2 : x.val = x.val % 2 + 2 * (x.val / 2) := (Nat.mod_add_div x.val 2).symm
    exact hx2.trans (congrArg (fun t ↦ x.val % 2 + 2 * t) hy)
  constructor
  · intro x
    obtain ⟨q, _, hfx⟩ := hDecomp x
    apply (basisBitsEquiv s).injective; funext t
    change basisBits s (rLowS.extractIndex (kickFun43 θ₀ θ₁ x)) t =
      basisBits s (rLowS.extractIndex x) t
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    have hrw : (rLowS t).val = 1 + t.val := rfl
    rw [basisBits_eq_div_mod, basisBits_eq_div_mod, hrw, hfx]
    have h1 := (bitSplit43_decomp (Nat.mod_lt x.val (by decide))
      (Nat.mod_lt (x.val / 2) (Nat.two_pow_pos s))
      (H := (((x.val / 2) / 2 ^ s) + q) % 2 ^ (42 - s))).2.2.1 t.val t.isLt
    have h2 := (bitSplit43_decomp (Nat.mod_lt x.val (by decide))
      (Nat.mod_lt (x.val / 2) (Nat.two_pow_pos s))
      (H := (x.val / 2) / 2 ^ s)).2.2.1 t.val t.isLt
    rw [← hxForm x] at h2
    rw [h1, h2]
  · intro x z hOut w hw
    have hw0_not : (⟨0, by decide⟩ : Wire (1 + 42)) ∉ Set.range rLowS.wires := by
      rintro ⟨t, ht⟩
      have hv := congrArg Fin.val ht
      change 1 + t.val = 0 at hv; omega
    have hbEqZ : basisBits (1 + 42) x ⟨0, by decide⟩ = basisBits (1 + 42) z ⟨0, by decide⟩ :=
      hOut ⟨0, by decide⟩ hw0_not
    have hbEq : x.val % 2 = z.val % 2 := by
      rw [basisBits_eq_div_mod, basisBits_eq_div_mod] at hbEqZ
      change ((x.val / 1 % 2 : ℕ) : ZMod 2) = ((z.val / 1 % 2 : ℕ) : ZMod 2) at hbEqZ
      have h1 := congrArg ZMod.val hbEqZ
      rw [Nat.div_one, Nat.div_one] at h1
      simpa only [ZMod.val_natCast, Nat.mod_mod] using h1
    have hHiEq : (x.val / 2) / 2 ^ s = (z.val / 2) / 2 ^ s := by
      apply Nat.eq_of_testBit_eq; intro u
      by_cases hu : u < 42 - s
      · let wu : Wire (1 + 42) := ⟨1 + s + u, by omega⟩
        have hwu : wu ∉ Set.range rLowS.wires := by
          rintro ⟨t, ht⟩
          have hv := congrArg Fin.val ht
          have := t.isLt
          change 1 + t.val = 1 + s + u at hv; omega
        have hbw := hOut wu hwu
        rw [basisBits_eq_testBit, basisBits_eq_testBit] at hbw
        have htb : x.val.testBit (1 + s + u) = z.val.testBit (1 + s + u) := by
          cases hx_tb : x.val.testBit wu.val <;> cases hz_tb : z.val.testBit wu.val
          · rfl
          · exfalso; rw [hx_tb, hz_tb] at hbw; exact zero_ne_one hbw
          · exfalso; rw [hx_tb, hz_tb] at hbw; exact one_ne_zero hbw
          · rfl
        have hdiv : ∀ n : ℕ, ((n / 2) / 2 ^ s).testBit u = n.testBit (1 + s + u) := fun n ↦ by
          have hp : 2 * 2 ^ s = 2 ^ (1 + s) := by rw [Nat.pow_add, pow_one]
          rw [Nat.div_div_eq_div_mul, hp, Nat.testBit_div_two_pow]
          congr 1; omega
        rw [hdiv x.val, hdiv z.val, htb]
      · have hx_lt : (x.val / 2) / 2 ^ s < 2 ^ u := by
          have hx_bound : x.val < 2 * 2 ^ 42 := lt_of_lt_of_eq x.isLt (by decide)
          have h1 : x.val / 2 < 2 ^ s * 2 ^ (42 - s) := by
            rw [← Nat.pow_add, Nat.add_sub_of_le hs]; omega
          have h2 : (x.val / 2) / 2 ^ s < 2 ^ (42 - s) :=
            (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).mpr (by simpa [mul_comm] using h1)
          exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))
        have hz_lt : (z.val / 2) / 2 ^ s < 2 ^ u := by
          have hz_bound : z.val < 2 * 2 ^ 42 := lt_of_lt_of_eq z.isLt (by decide)
          have h1 : z.val / 2 < 2 ^ s * 2 ^ (42 - s) := by
            rw [← Nat.pow_add, Nat.add_sub_of_le hs]; omega
          have h2 : (z.val / 2) / 2 ^ s < 2 ^ (42 - s) :=
            (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).mpr (by simpa [mul_comm] using h1)
          exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))
        rw [Nat.testBit_lt_two_pow hx_lt, Nat.testBit_lt_two_pow hz_lt]
    obtain ⟨qx, hqx, hfx⟩ := hDecomp x
    obtain ⟨qz, hqz, hfz⟩ := hDecomp z
    have hqEq : qx = qz := by
      rw [hbEq, hqz] at hqx
      exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos s) hqx.symm
    subst hqEq
    rw [basisBits_eq_div_mod, basisBits_eq_div_mod, hfx, hfz]
    have hwCases : w.val = 0 ∨ 1 + s ≤ w.val := by
      by_contra hnc
      exact hw ⟨⟨w.val - 1, by omega⟩, Fin.ext (by change 1 + (w.val - 1) = w.val; omega)⟩
    rcases hwCases with hw0 | hws
    · rw [hw0]
      simp only [_root_.pow_zero, Nat.div_one]
      rw [(bitSplit43_decomp (Nat.mod_lt x.val (by decide))
          (Nat.mod_lt (x.val / 2) (Nat.two_pow_pos s))).1,
        (bitSplit43_decomp (Nat.mod_lt z.val (by decide))
          (Nat.mod_lt (z.val / 2) (Nat.two_pow_pos s))).1, hbEq]
    · have hwu : w.val = 1 + s + (w.val - (1 + s)) := by omega
      rw [hwu,
        (bitSplit43_decomp (Nat.mod_lt x.val (by decide))
          (Nat.mod_lt (x.val / 2) (Nat.two_pow_pos s))).2.2.2 (w.val - (1 + s)),
        (bitSplit43_decomp (Nat.mod_lt z.val (by decide))
          (Nat.mod_lt (z.val / 2) (Nat.two_pow_pos s))).2.2.2 (w.val - (1 + s)), hHiEq]

theorem commutesWithReg_low_uKickGidney43 {s : ℕ} (hs : s ≤ 42)
    (C_d : Fin (2 ^ 42)) (hC : 2 ^ s ∣ C_d.val) :
    CommutesWithReg (QRegister.block 1 s (by omega)) (uKickGidney43 C_d).1 := by
  have hC' : 2 ^ s ∣ 2 ^ 42 - C_d.val := by
    obtain ⟨q, hq⟩ := hC
    refine ⟨2 ^ (42 - s) - q, ?_⟩
    rw [Nat.mul_sub_left_distrib, ← Nat.pow_add, Nat.add_sub_of_le hs, ← hq]
  have hFwd := kickFun43_extract_and_outside hs hC hC'
  have hInv := kickFun43_extract_and_outside hs hC' hC
  exact commutesWithReg_fwdPermUnitary (QRegister.block 1 s (by omega)) (kickPerm43 C_d)
    hFwd.1 hFwd.2 hInv.2

theorem commutesWithReg_low_uSignalRotTwoAngle43 {s : ℕ} (hs : s ≤ 42)
    (C_d D_d : Fin (2 ^ 42)) (hC : 2 ^ s ∣ C_d.val) (hD : 2 ^ s ∣ D_d.val) :
    CommutesWithReg (QRegister.block 1 s (by omega)) (uSignalRotTwoAngle43 C_d D_d).1 := by
  have hH : CommutesWithReg (QRegister.block 1 s (by omega))
      (Circuit.H (⟨0, by decide⟩ : Wire (1 + 42))).eval.1 := by
    rw [Circuit.H, Circuit.eval_single, QRegister.embedUnitary_val]
    refine CommutesWithReg.of_disjoint ?_ _
    rw [QRegister.disjoint_iff]; intro a b hab; fin_cases a
    have hv := congrArg Fin.val hab; change 0 = 1 + b.val at hv; omega
  unfold uSignalRotTwoAngle43
  simp only [Submonoid.coe_mul]
  exact hH.mul ((commutesWithReg_low_uKickGidney43 hs D_d hD).mul
    (hH.mul (commutesWithReg_low_uKickGidney43 hs C_d hC)))

theorem commutesWithReg_low_uSigMidTwoAngle43 {s : ℕ} (hs : s ≤ 42) (preX postX : Bool)
    (C_d D_d : Fin (2 ^ 42)) (hC : 2 ^ s ∣ C_d.val) (hD : 2 ^ s ∣ D_d.val) : CommutesWithReg
    (QRegister.block 1 s (by omega)) (uSigMidTwoAngle43 preX postX C_d D_d).1 := by
  have hOpt : ∀ b : Bool, CommutesWithReg (QRegister.block 1 s (by omega)) (optX43 b).eval.1 := by
    intro b; cases b
    · exact CommutesWithReg.one _
    · dsimp only [optX43]
      rw [Circuit.X, Circuit.eval_single, QRegister.embedUnitary_val]
      refine CommutesWithReg.of_disjoint ?_ _
      rw [QRegister.disjoint_iff]; intro a t hab; fin_cases a
      have hv := congrArg Fin.val hab; change 0 = 1 + t.val at hv; omega
  unfold uSigMidTwoAngle43
  simp only [Submonoid.coe_mul]
  exact (hOpt postX).mul
    ((commutesWithReg_low_uSignalRotTwoAngle43 hs C_d D_d hC hD).mul (hOpt preX))

open Classical in
theorem basisOutcomeProjector_conjTranspose {m n : ℕ} (r : QRegister m n) (x : Fin (2 ^ m)) :
    (r.basisOutcomeProjector x)ᴴ = r.basisOutcomeProjector x := by
  rw [r.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_conjTranspose]
  ext i j
  simp only [Matrix.diagonal_apply, Pi.star_apply]
  split_ifs <;> simp

open Classical in
theorem RealizesOnProj.of_clean_sub_ext {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct kSub mWork mExt n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kAct n}
    {rWork : QRegister mWork n} (hDisj : rAct.DisjointWires rWork)
    (rSub : QRegister kSub kAct) (rCleanAct : QRegister mExt kAct)
    (E_base : Operator (2 ^ kAct)) (hComm : E_base * rCleanAct.basisOutcomeProjector 0 =
    rCleanAct.basisOutcomeProjector 0 * E_base) {U_sub : Unitary (2 ^ kSub)}
    {d : DynamicCircuit Var n} (hd : RealizesClean (rAct.compose rSub) (rWork.concat
    (rAct.compose rCleanAct) (QRegExt.disjointWires_symm (hDisj.compose_left rCleanAct))) U_sub d) :
      RealizesOnProj
    (rAct.embedMatrix (E_base * rCleanAct.basisOutcomeProjector 0) *
    rWork.basisOutcomeProjector 0) (rAct.embedUnitary (rSub.embedUnitary U_sub)) d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  let rWExt :=
    rWork.concat (rAct.compose rCleanAct) (QRegExt.disjointWires_symm (hDisj.compose_left
    rCleanAct))
  let PW := rWExt.basisOutcomeProjector 0
  let PW0 := rWork.basisOutcomeProjector 0
  let P0 := rAct.embedMatrix (rCleanAct.basisOutcomeProjector 0)
  let B := rAct.embedMatrix E_base
  have hCompP0 : (rAct.compose rCleanAct).basisOutcomeProjector 0 = P0 := by
    dsimp only [P0]
    rw [QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
      ← QRegister.basisOutcomeProjector]
  have hPW : PW = PW0 * P0 := by
    dsimp only [PW, PW0, rWExt]
    rw [basisOutcomeProjector_concat_zero, hCompP0]
  have hPW_comm_P0 : P0 * PW0 = PW0 * P0 :=
    (CommutesWithReg.of_disjoint hDisj _).comm_basisOutcomeProjector 0
  have hPW_comm_B : B * PW0 = PW0 * B :=
    (CommutesWithReg.of_disjoint hDisj _).comm_basisOutcomeProjector 0
  have hEin : rAct.embedMatrix (E_base * rCleanAct.basisOutcomeProjector 0) * PW0 = PW * B := by
    rw [hComm, rAct.embedMatrix_mul, Matrix.mul_assoc, hPW_comm_B,
      ← Matrix.mul_assoc, hPW_comm_P0, ← hPW]
  have hPWH : PWᴴ = PW := basisOutcomeProjector_conjTranspose rWExt 0
  have hEinH : (rAct.embedMatrix (E_base * rCleanAct.basisOutcomeProjector 0) * PW0)ᴴ =
      Bᴴ * PW := by
    rw [hEin, Matrix.conjTranspose_mul, hPWH]
  have hUEq : (rAct.compose rSub).embedUnitary U_sub = rAct.embedUnitary
      (rSub.embedUnitary U_sub) := QRegister.embedUnitary_compose rAct rSub U_sub
  rw [hUEq] at hproj
  rw [hEinH, hEin]
  calc
    (Bᴴ * PW) * M'.1.1 * (PW * B) = Bᴴ * (PW * M'.1.1 * PW) * B := by
      simp only [Matrix.mul_assoc]
    _ = Bᴴ * (PW * ((rAct.embedUnitary (rSub.embedUnitary U_sub)).1ᴴ * M.1.1 *
          (rAct.embedUnitary (rSub.embedUnitary U_sub)).1) * PW) * B := by
      rw [hproj]
    _ = (Bᴴ * PW) * ((rAct.embedUnitary (rSub.embedUnitary U_sub)).1ᴴ * M.1.1 *
          (rAct.embedUnitary (rSub.embedUnitary U_sub)).1) * (PW * B) := by
      simp only [Matrix.mul_assoc]

theorem embedAct0_projZero_comm_E_stream42 {m : ℕ} (rOrig : QRegister m kActOrig) :
    (rAct0.compose rOrig).basisOutcomeProjector 0 * E_stream42 =
      E_stream42 * (rAct0.compose rOrig).basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
    ← QRegister.basisOutcomeProjector, E_stream42_eq_streamProjOp]
  exact embedAct0_comm_streamOp ((PreservesFeature.basisOutcomeProjector rOrig 0).id_imp _)

theorem E_stream42_comm_pCtrl3Zero : E_stream42 * pCtrl3Zero = pCtrl3Zero * E_stream42 :=
  (embedAct0_projZero_comm_E_stream42 rUnusedCtrl3Orig).symm

theorem E_stream42_comm_pSlack3Zero : E_stream42 * pSlack3Zero = pSlack3Zero * E_stream42 :=
  (embedAct0_projZero_comm_E_stream42 rSlack3Orig).symm

theorem E_stream42_comm_pPGIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_stream42 * pPGIdleZero k_idle hk = pPGIdleZero k_idle hk * E_stream42 :=
  (embedAct0_projZero_comm_E_stream42 (rPGIdleOrig k_idle hk)).symm

theorem E_stream42_comm_pExt6Zero : E_stream42 * pExt6Zero = pExt6Zero * E_stream42 := by
  rw [pExt6Zero_eq_mul, ← Matrix.mul_assoc, E_stream42_comm_pCtrl3Zero,
    Matrix.mul_assoc, E_stream42_comm_pSlack3Zero, ← Matrix.mul_assoc]

theorem E_stream42_comm_pExt6IdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_stream42 * pExt6IdleZero k_idle hk = pExt6IdleZero k_idle hk * E_stream42 := by
  rw [pExt6IdleZero_eq_mul, ← Matrix.mul_assoc, E_stream42_comm_pExt6Zero,
    Matrix.mul_assoc, E_stream42_comm_pPGIdleZero k_idle hk, ← Matrix.mul_assoc]

theorem embedAct0_pCtrl3ZeroOrig : rAct0.embedMatrix pCtrl3ZeroOrig = pCtrl3Zero := by
  unfold pCtrl3Zero pCtrl3ZeroOrig rUnusedCtrl3Full
  exact (QRegister.embedMatrix_compose rAct0 rUnusedCtrl3Orig (compProj 0)).symm

theorem PreservesFeature.comm_diagonal {d : ℕ} {α : Type*} {f : Fin d → α}
    (g : α → ℂ) {M : Operator d} (hM : PreservesFeature f M) :
    M * Matrix.diagonal (fun x ↦ g (f x)) = Matrix.diagonal (fun x ↦ g (f x)) * M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h0 : M i j = 0
  · simp [h0]
  · rw [hM i j h0, mul_comm]

/-- `3`-wire control bits `[3951 .. 3954)` extracted from an `n`-qubit basis index. -/
def ctrl3Bits {n : ℕ} (hn : 3954 ≤ n) (x : Fin (2 ^ n)) : Fin 3 → ZMod 2 :=
  fun t ↦ basisBits n x ⟨3951 + t.val, by have := t.isLt; omega⟩

/-- Predicate stating that `M` preserves `ctrl3Bits hn` (`[3951 .. 3954)`). -/
def FixesCtrl3 {n : ℕ} (hn : 3954 ≤ n) (M : Operator (2 ^ n)) : Prop :=
  PreservesFeature (ctrl3Bits hn) M

/-- Register predicate stating that every wire of `r` avoids `[3951 .. 3954)`. -/
def IsDisjCtrl3Reg {k n : ℕ} (r : QRegister k n) : Prop :=
  ∀ i : Fin k, (r i).val < 3951 ∨ 3954 ≤ (r i).val

/-- Register predicate stating that `r` fixes wires `[3951 .. 3954)` pointwise. -/
def IsCtrl3Prefix {k n : ℕ} (hk : 3954 ≤ k) (hn : 3954 ≤ n) (r : QRegister k n) : Prop :=
  ∀ t : Fin 3,
    r ⟨3951 + t.val, by have := t.isLt; omega⟩ =
      ⟨3951 + t.val, by have := t.isLt; omega⟩

theorem h3954_core : 3954 ≤ fullSysCoreWires 80 := by decide
theorem h3954_be : 3954 ≤ fullSysBEWires 80 := by decide
theorem h3954_actOrig : 3954 ≤ kActOrig := by decide

theorem isCtrl3Prefix_block0 {k n : ℕ} (hk : 3954 ≤ k) (hn : 3954 ≤ n) (hle : 0 + k ≤ n) :
    IsCtrl3Prefix hk hn (QRegister.block 0 k hle) := by
  intro t; ext; simp

theorem isCtrl3Prefix_rBEOrig : IsCtrl3Prefix h3954_be h3954_actOrig rBEOrig :=
  isCtrl3Prefix_block0 h3954_be h3954_actOrig _

theorem ctrl3Bits_extractIndex_of_prefix {k n : ℕ} {hk : 3954 ≤ k} {hn : 3954 ≤ n}
    {r : QRegister k n} (hr : IsCtrl3Prefix hk hn r) (x : Fin (2 ^ n)) : ctrl3Bits hk
    (r.extractIndex x) = ctrl3Bits hn x := by
  funext t
  dsimp only [ctrl3Bits]
  rw [r.basisBits_extractIndex x ⟨3951 + t.val, by have := t.isLt; omega⟩]
  exact congrArg (basisBits n x) (hr t)

theorem fixesCtrl3_embedMatrix_prefix {k n : ℕ} {hk : 3954 ≤ k} {hn : 3954 ≤ n}
    {r : QRegister k n} (hr : IsCtrl3Prefix hk hn r) {A : Operator (2 ^ k)}
    (hA : FixesCtrl3 hk A) : FixesCtrl3 hn (r.embedMatrix A) := by
  intro x y hne
  have h0 := preservesFeature_embedMatrix_of_extract r (ctrl3Bits hk) hA x y hne
  dsimp only at h0
  rwa [ctrl3Bits_extractIndex_of_prefix hr x, ctrl3Bits_extractIndex_of_prefix hr y] at h0

open Classical in
theorem fixesCtrl3_embedMatrix_disj {k n : ℕ} (hn : 3954 ≤ n) {r : QRegister k n}
    (hr : IsDisjCtrl3Reg r) (A : Operator (2 ^ k)) : FixesCtrl3 hn (r.embedMatrix A) := by
  intro x y hne
  by_cases hAgree : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2
  · have hOut : r.AgreeOutside x y := (r.basisSplit_environment_eq_iff x y).mp hAgree
    funext t
    dsimp only [ctrl3Bits]
    refine hOut ⟨3951 + t.val, by have := t.isLt; omega⟩ ?_
    rintro ⟨idx, hidx⟩
    have hv := congrArg Fin.val hidx
    have ht := t.isLt
    dsimp only at hv
    rcases hr idx with hlt | hge <;> omega
  · rw [QRegister.embedMatrix_apply, ite_eq_right hAgree, mul_zero] at hne
    exact False.elim (hne rfl)

open Classical in
theorem pCtrl3ZeroOrig_eq_diagonal_ctrl3Bits :
    pCtrl3ZeroOrig = Matrix.diagonal (fun x : Fin (2 ^ kActOrig) ↦
      if (basisBitsEquiv 3).symm (ctrl3Bits h3954_actOrig x) = 0 then (1 : ℂ) else 0) := by
  unfold pCtrl3ZeroOrig
  rw [rUnusedCtrl3Orig.basisOutcomeProjector_eq_diagonal]
  congr 1

open Classical in
theorem FixesCtrl3.comm_pCtrl3ZeroOrig {M : Operator (2 ^ kActOrig)}
    (hM : FixesCtrl3 h3954_actOrig M) : M * pCtrl3ZeroOrig = pCtrl3ZeroOrig * M := by
  rw [pCtrl3ZeroOrig_eq_diagonal_ctrl3Bits]
  exact PreservesFeature.comm_diagonal
    (fun c : Fin 3 → ZMod 2 ↦ if (basisBitsEquiv 3).symm c = 0 then (1 : ℂ) else 0) hM

def rBE77Orig : QRegister (fullSysBEWires 77) kActOrig where
  wires :=
    ⟨fun i ↦
      ⟨if i.val < 3951 then i.val else i.val + 3, by
        have := i.isLt
        dsimp [fullSysBEWires, fullSysRawAncWires, kActOrig, kActSingleCatClosure,
          mActSingleCatClosure, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
          SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at this ⊢
        change (if i.val < 3951 then i.val else i.val + 3) < 4086
        split_ifs <;> omega⟩,
     fun i j hij ↦ by
      have hv := congrArg Fin.val hij
      dsimp only at hv
      split_ifs at hv <;> exact Fin.ext (by omega)⟩

/-- `77`-payload block-encoding register inside `kFull80 = 4,128`, skipping `[3951 .. 3954)`. -/
def rBE77Full : QRegister (fullSysBEWires 77) kFull80 := rAct0.compose rBE77Orig

/-- Standard `43`-wire `(qSig ++ rTopCatSlice 42 48)` register inside `kActOrig = 4,086`. -/
abbrev rMid43Orig : QRegister (1 + 42) kActOrig :=
  rMid43InSingleCat 80 48 40 (by decide : 42 ≤ 48)

/-- Standard `43`-wire `(qSig ++ rTopCatSlice 42 48)` register inside `kFull80 = 4,128`. -/
def rMid43Full : QRegister (1 + 42) kFull80 := rAct0.compose rMid43Orig

theorem rMid43Orig_zero_val : (rMid43Orig ⟨0, by decide⟩).val = 4034 := by
  decide

theorem rMid43Orig_succ_val :
    ∀ t : Fin 42, (rMid43Orig ⟨1 + t.val, by omega⟩).val = 4041 + t.val := by
  decide

theorem rMid43Orig_pos_val (idx : Fin (1 + 42)) (h0 : idx.val ≠ 0) :
    (rMid43Orig idx).val = 4041 + (idx.val - 1) := by
  let t : Fin 42 := ⟨idx.val - 1, by omega⟩
  have hidx : idx = ⟨1 + t.val, by omega⟩ := Fin.ext (by dsimp [t]; omega)
  conv_lhs => rw [hidx]
  exact rMid43Orig_succ_val t

theorem rMid43Orig_val_ge_4034 (j : Fin (1 + 42)) : 4034 ≤ (rMid43Orig j).val := by
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, by decide⟩ := Fin.ext hj0
    rw [hj, rMid43Orig_zero_val]
  · rw [rMid43Orig_pos_val j hj0]; omega

open Classical in
theorem rBE77Orig_val_lt_4034 (i : Fin (fullSysBEWires 77)) : (rBE77Orig i).val < 4034 := by
  have := i.isLt
  dsimp [rBE77Orig, fullSysBEWires, fullSysRawAncWires, SpecsAux.SpecMirror.systemQubits,
    SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits] at this ⊢
  split_ifs <;> omega

open Classical in
theorem rBE77Orig_val_not_ctrl3 (i : Fin (fullSysBEWires 77)) :
    (rBE77Orig i).val < 3951 ∨ 3954 ≤ (rBE77Orig i).val := by
  dsimp [rBE77Orig]
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem rBE77Orig_disj_rMid43Orig : rBE77Orig.DisjointWires rMid43Orig :=
  disj_of_val_ne fun i j ↦ by
    have h1 := rBE77Orig_val_lt_4034 i
    have h2 := rMid43Orig_val_ge_4034 j
    omega

/-- Combined `(fullSysBEWires 77 + 43)`-wire guard register inside `kActOrig`. -/
abbrev rBEMid77Orig : QRegister (fullSysBEWires 77 + (1 + 42)) kActOrig :=
  rBE77Orig.concat rMid43Orig rBE77Orig_disj_rMid43Orig

def rMid43EffFull (k_idle : ℕ) (_hk : k_idle ≤ 48) : QRegister (1 + 42) kFull80 where
  wires :=
    ⟨fun idx ↦
      ⟨if idx.val = 0 then 4034
       else if idx.val - 1 < k_idle - 6 then 4086 + (idx.val - 1)
       else 4041 + (idx.val - 1), by
        have := idx.isLt
        have := _hk
        change (if idx.val = 0 then 4034 else if idx.val - 1 < k_idle - 6 then 4086 + (idx.val
          - 1) else 4041 + (idx.val - 1)) < 4128
        split_ifs <;> omega⟩,
     fun i j hij ↦ by
      have hv := congrArg Fin.val hij
      have := i.isLt; have := j.isLt
      dsimp only at hv
      split_ifs at hv <;> exact Fin.ext (by omega)⟩

open Classical in
theorem rMid43EffFull_val_eq (k_idle : ℕ) (hk : k_idle ≤ 48) (idx : Fin (1 + 42)) :
    (rMid43EffFull k_idle hk idx).val = if idx.val = 0 then 4034 else if idx.val - 1 < k_idle
    - 6 then 4086 + (idx.val - 1) else 4041 + (idx.val - 1) := rfl

theorem rBE77Full_val_eq (i : Fin (fullSysBEWires 77)) :
    (rBE77Full i).val = (rBE77Orig i).val := by
  dsimp [rBE77Full]; rw [rAct0_val_eq]

theorem rBE77Full_disj_rMid43Full : rBE77Full.DisjointWires rMid43Full :=
  disjointWires_compose_of_disjoint rAct0 rBE77Orig_disj_rMid43Orig

open Classical in
theorem rBE77Full_disj_rMid43EffFull (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rBE77Full.DisjointWires (rMid43EffFull k_idle hk) :=
  disj_of_val_ne fun i idx ↦ by
    rw [rBE77Full_val_eq, rMid43EffFull_val_eq]
    have h1 := rBE77Orig_val_lt_4034 i
    have := idx.isLt
    split_ifs <;> omega

/-- Combined `(fullSysBEWires 77 + 43)`-wire register `rBE77Full ++ rMid43Full` inside `kFull80`. -/
def rBEMid77Full : QRegister (fullSysBEWires 77 + (1 + 42)) kFull80 :=
  rBE77Full.concat rMid43Full rBE77Full_disj_rMid43Full

/-- Guard-A combined `(fullSysBEWires 77 + 43)`-wire register `rBE77Full ++ rMid43EffFull` inside
  `kFull80`. -/
def rBEMid77EffFull (k_idle : ℕ) (hk : k_idle ≤ 48) :
    QRegister (fullSysBEWires 77 + (1 + 42)) kFull80 :=
  rBE77Full.concat (rMid43EffFull k_idle hk) (rBE77Full_disj_rMid43EffFull k_idle hk)

open Classical in
theorem rBEMid77EffFull_disj_rExt6IdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) :
    (rBEMid77EffFull k_idle hk).DisjointWires (rExt6IdleFull k_idle hk) := by
  have hBE_Ctrl3 : rBE77Full.DisjointWires rUnusedCtrl3Full :=
    disj_of_val_ne fun i t ↦ by
      rw [rBE77Full_val_eq, rUnusedCtrl3Full_val_eq]; have := t.isLt
      rcases rBE77Orig_val_not_ctrl3 i with h1 | h2 <;> omega
  have hBE_Slack3 : rBE77Full.DisjointWires rSlack3Full :=
    disj_of_val_ne fun i t ↦ by
      rw [rBE77Full_val_eq, rSlack3Full_val_eq]
      have := rBE77Orig_val_lt_4034 i; have := t.isLt; omega
  have hBE_Idle : rBE77Full.DisjointWires (rPGIdle k_idle hk) :=
    disj_of_val_ne fun i q ↦ by
      rw [rBE77Full_val_eq, rPGIdle_val_eq]
      have := rBE77Orig_val_lt_4034 i; have := q.isLt; omega
  have hMid_Ctrl3 : (rMid43EffFull k_idle hk).DisjointWires rUnusedCtrl3Full :=
    disj_of_val_ne fun idx t ↦ by
      rw [rMid43EffFull_val_eq, rUnusedCtrl3Full_val_eq]
      have := idx.isLt; have := t.isLt; split_ifs <;> omega
  have hMid_Slack3 : (rMid43EffFull k_idle hk).DisjointWires rSlack3Full :=
    disj_of_val_ne fun idx t ↦ by
      rw [rMid43EffFull_val_eq, rSlack3Full_val_eq]
      have := idx.isLt; have := t.isLt; split_ifs <;> omega
  have hMid_Idle : (rMid43EffFull k_idle hk).DisjointWires (rPGIdle k_idle hk) :=
    disj_of_val_ne fun idx q ↦ by
      rw [rMid43EffFull_val_eq, rPGIdle_val_eq]
      have := idx.isLt; have := q.isLt; split_ifs <;> omega
  exact disjointWires_concat_right (disjointWires_concat_right
    (FullSysCatSegmentBridge.disjointWires_concat_left _ hBE_Ctrl3 hMid_Ctrl3)
    (FullSysCatSegmentBridge.disjointWires_concat_left _ hBE_Slack3 hMid_Slack3))
    (FullSysCatSegmentBridge.disjointWires_concat_left _ hBE_Idle hMid_Idle)

open Classical in
theorem embedUnitary_rMid43EffFull_uSigMidTwoAngle43_eq
    (k_idle : ℕ) (hk : k_idle ≤ 48) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (hC : 2 ^ (k_idle - 6) ∣ C_d.val) (hD : 2 ^ (k_idle - 6) ∣ D_d.val) :
    (rMid43EffFull k_idle hk).embedUnitary (uSigMidTwoAngle43 bPre bPost C_d D_d) =
      rMid43Full.embedUnitary (uSigMidTwoAngle43 bPre bPost C_d D_d) := by
  refine embedUnitary_eq_of_commutesWithReg (rMid43EffFull k_idle hk) rMid43Full
    (QRegister.block 1 (k_idle - 6) (by omega)) (uSigMidTwoAngle43 bPre bPost C_d D_d)
    (fun idx hnot ↦ ?_)
    (commutesWithReg_low_uSigMidTwoAngle43 (by omega : k_idle - 6 ≤ 42) bPre bPost C_d D_d hC hD)
  apply Fin.ext
  rw [rMid43EffFull_val_eq]
  change _ = (rAct0 (rMid43Orig idx)).val
  rw [rAct0_val_eq]
  by_cases h0 : idx.val = 0
  · have hidx : idx = ⟨0, by decide⟩ := Fin.ext h0
    rw [ite_eq_left h0, hidx, rMid43Orig_zero_val]
  · have hge : ¬ idx.val - 1 < k_idle - 6 := fun hlt ↦
      hnot ⟨⟨idx.val - 1, hlt⟩, Fin.ext (by change 1 + (idx.val - 1) = idx.val; omega)⟩
    rw [ite_eq_right h0, ite_eq_right hge, rMid43Orig_pos_val idx h0]

open Classical in
theorem dvd_biCode_of_forall_dvd {M s : ℕ} {C : Fin (M + 1) → Fin (2 ^ 42)}
    (hC : ∀ t : Fin (M + 1), 2 ^ s ∣ (C t).val) (k : ℕ) : 2 ^ s ∣ (biCode M C k).val := by
  unfold biCode
  by_cases hk : k < M + 1
  · rw [dite_eq_left hk]; exact hC ⟨k, hk⟩
  · rw [dite_eq_right hk]; exact dvd_zero _

def rSlackIdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (3 + k_idle) kFull80 :=
  rSlack3Full.concat (rPGIdle k_idle hk) (hSlack3_disj_PGIdle k_idle hk)

/-- All-`|0⟩` projector on `rSlackIdleFull k_idle hk` inside `kFull80`. -/
noncomputable def pSlackIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rSlackIdleFull k_idle hk).basisOutcomeProjector 0

theorem pSlackIdleZero_eq_mul (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pSlackIdleZero k_idle hk = pSlack3Zero * pPGIdleZero k_idle hk :=
  basisOutcomeProjector_concat_zero rSlack3Full (rPGIdle k_idle hk) (hSlack3_disj_PGIdle k_idle hk)

theorem pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pExt6IdleZero k_idle hk = pCtrl3Zero * pSlackIdleZero k_idle hk := by
  rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul, pSlackIdleZero_eq_mul, Matrix.mul_assoc]

theorem hSum0_disj_SlackIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rSum0.DisjointWires (rSlackIdleFull k_idle hk) :=
  disjointWires_concat_right hSum0_disj_Slack3 (hSum0_disj_PGIdle k_idle hk)

/-- Combined `(42 + (3 + k_idle))`-wire (`rSum0 ++ rSlackIdleFull`, `56w` at `k_idle = 11`)
post-twist clean register disjoint from un-swapped `rCoreFull` (`[0 .. 4034)`). -/
def rExt45IdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (42 + (3 + k_idle)) kFull80 :=
  rSum0.concat (rSlackIdleFull k_idle hk) (hSum0_disj_SlackIdle k_idle hk)

theorem basisOutcomeProjector_comm_any {m₁ m₂ n : ℕ}
    (r₁ : QRegister m₁ n) (x₁ : Fin (2 ^ m₁)) (r₂ : QRegister m₂ n) (x₂ : Fin (2 ^ m₂)) :
    r₁.basisOutcomeProjector x₁ * r₂.basisOutcomeProjector x₂ =
      r₂.basisOutcomeProjector x₂ * r₁.basisOutcomeProjector x₁ := by
  rw [r₁.basisOutcomeProjector_eq_diagonal, r₂.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)

def rWorkSlackIdle {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : QRegister
    (mWork + (3 + k_idle)) n := rWork.concat (rAct.compose (rSlackIdleFull k_idle hk))
    (QRegExt.disjointWires_symm (hDisj.compose_left (rSlackIdleFull k_idle hk)))

theorem rCoreOrig_val_eq (i : Fin (fullSysCoreWires 80)) : (rCoreOrig i).val = i.val := by
  simp [rCoreOrig, rBEOrig, rBEInSingleCat, beCoreBlock]

theorem rCoreFull_val_eq (i : Fin (fullSysCoreWires 80)) : (rCoreFull i).val = i.val := by
  change (rAct0 (rCoreOrig i)).val = i.val
  rw [rAct0_val_eq, rCoreOrig_val_eq]

/-- Local `3`-wire control block `[3951 .. 3954)` inside `fullSysCoreWires 80 = 4,034`. -/
def rCtrl3InCore : QRegister 3 (fullSysCoreWires 80) := QRegister.block 3951 3 h3954_core

/-- Local `3`-wire control block `[3951 .. 3954)` inside `fullSysCoreWires 80 + mCat`. -/
def rCtrl3InCoreCat (mCat : ℕ) : QRegister 3 (fullSysCoreWires 80 + mCat) :=
  QRegister.block 3951 3 (h3954_core.trans (Nat.le_add_right _ mCat))

/-- Core `4,034`-wire register inside `kFull80 = 4,128` swapping `[3951 .. 3954)` onto
`rPG48Full[off .. off + 3)` (`[4035 + off .. 4038 + off)`) so `rUnusedCtrl3Full` stays disjoint
and available in `rExt6IdleFull` / `rExt48IdleFull`. -/
def rCoreSwapCtrl3PG3At (off : ℕ) (hoff : off + 3 ≤ 48) :
    QRegister (fullSysCoreWires 80) kFull80 where
  wires :=
    ⟨fun i ↦
      ⟨if 3951 ≤ i.val ∧ i.val < 3954 then 4035 + off + (i.val - 3951) else i.val, by
        have := i.isLt
        dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires, kFull80, mActHoist,
          SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
          SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at this ⊢
        change (if 3951 ≤ i.val ∧ i.val < 3954 then 4035 + off + (i.val - 3951) else i.val) < 4128
        split_ifs <;> omega⟩,
     fun i j hij ↦ by
      have hv := congrArg Fin.val hij
      have hi := i.isLt; have hj := j.isLt
      dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi hj hv
      split_ifs at hv <;> exact Fin.ext (by omega)⟩

open Classical in
theorem rCoreSwapCtrl3PG3At_val_eq (off : ℕ) (hoff : off + 3 ≤ 48)
    (i : Fin (fullSysCoreWires 80)) : (rCoreSwapCtrl3PG3At off hoff i).val = if 3951 ≤ i.val
    ∧ i.val < 3954 then 4035 + off + (i.val - 3951) else i.val := rfl

open Classical in
theorem rCoreSwapCtrl3PG3At_disj_rSum0 (off : ℕ) (hoff : off + 3 ≤ 48) :
    (rCoreSwapCtrl3PG3At off hoff).DisjointWires rSum0 :=
  disj_of_val_ne fun i s ↦ by
    rw [rCoreSwapCtrl3PG3At_val_eq, rSum0_val_eq]
    have hi := i.isLt; have hs := s.isLt
    dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
      SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
    split_ifs <;> omega

open Classical in
theorem rCoreSwapCtrl3PG3At_disj_rExt6IdleFull
    (k_idle off : ℕ) (hk : k_idle ≤ 48) (hoff : off + 3 ≤ 48) (hk_off : k_idle ≤ off) :
    (rCoreSwapCtrl3PG3At off hoff).DisjointWires (rExt6IdleFull k_idle hk) := by
  have h1 : (rCoreSwapCtrl3PG3At off hoff).DisjointWires rUnusedCtrl3Full :=
    disj_of_val_ne fun i t ↦ by
      rw [rCoreSwapCtrl3PG3At_val_eq, rUnusedCtrl3Full_val_eq]
      have hi := i.isLt; have ht := t.isLt
      dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
      split_ifs <;> omega
  have h2 : (rCoreSwapCtrl3PG3At off hoff).DisjointWires rSlack3Full :=
    disj_of_val_ne fun i t ↦ by
      rw [rCoreSwapCtrl3PG3At_val_eq, rSlack3Full_val_eq]
      have hi := i.isLt; have ht := t.isLt
      dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
      split_ifs <;> omega
  have h3 : (rCoreSwapCtrl3PG3At off hoff).DisjointWires (rPGIdle k_idle hk) :=
    disj_of_val_ne fun i q ↦ by
      rw [rCoreSwapCtrl3PG3At_val_eq, rPGIdle_val_eq]
      have hi := i.isLt; have hq := q.isLt
      dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
      split_ifs <;> omega
  exact disjointWires_concat_right (disjointWires_concat_right h1 h2) h3

noncomputable def E_ctrl3Ext (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  E_stream42 * (pCtrl3Zero * pPGIdleZero k_idle hk)

/-- Pre-twist `dSelectCtrl` `(rAct, rWork)` subspace operator. -/
noncomputable def pCtrl3ExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_ctrl3Ext k_idle hk) * rWork.basisOutcomeProjector 0

/-- Un-swapped `rCoreFull ++ rTopCatSlice mCat 48` inside `kFull80`. -/
def rCoreTopCatFull (mCat : ℕ) (hmCat : mCat ≤ 48) : QRegister (fullSysCoreWires 80 + mCat)
    kFull80 := rCoreFull.concat (rPG48Full.compose (rTopCatSlice mCat 48 hmCat))
    (InterWalkRSum42Hoist.hCoreFull_disj_PG48Full.compose_right _)

theorem topCat_disj_rPGIdle (k_idle mCat : ℕ) (hkc : k_idle + mCat ≤ 48) :
    (rPG48Full.compose (rTopCatSlice mCat 48 (by omega))).DisjointWires
      (rPGIdle k_idle (by omega)) :=
  disj_of_val_ne fun a b ↦ by
    change (rPG48Full (rTopCatSlice mCat 48 (by omega) a)).val ≠ _
    rw [rPG48Full_val_eq, rPGIdle_val_eq]
    have htop : (rTopCatSlice mCat 48 (by omega) a).val = (48 - mCat) + a.val := by
      simp [rTopCatSlice]
    rw [htop]; have := a.isLt; have := b.isLt; omega

private theorem rCoreTopCatFull_disj_sum0_idle (k_idle mCat : ℕ) (hkc : k_idle + mCat ≤ 48) :
    (rCoreTopCatFull mCat (by omega)).DisjointWires rSum0 ∧
      (rCoreTopCatFull mCat (by omega)).DisjointWires (rPGIdle k_idle (by omega)) := by
  have hCIdle : rCoreFull.DisjointWires (rPGIdle k_idle (by omega)) :=
    disj_of_val_ne fun i q ↦ by
      rw [rCoreFull_val_eq, rPGIdle_val_eq]
      have hi := i.isLt
      have hq := q.isLt
      dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
      omega
  exact ⟨FullSysCatSegmentBridge.disjointWires_concat_left _
      (hAct0_disj_Sum0.compose_left rCoreOrig)
      ((hAct0_disj_Sum0.compose_left rPG48Orig).compose_left _),
    FullSysCatSegmentBridge.disjointWires_concat_left _ hCIdle
      (topCat_disj_rPGIdle k_idle mCat hkc)⟩

theorem rCoreTopCatFull_disj_rExt42IdleFull (k_idle mCat : ℕ) (hkc : k_idle + mCat ≤ 48) :
    (rCoreTopCatFull mCat (by omega)).DisjointWires (rExt42IdleFull k_idle (by omega)) :=
  let ⟨hS, hI⟩ := rCoreTopCatFull_disj_sum0_idle k_idle mCat hkc
  disjointWires_concat_right hS hI

theorem rCoreTopCatFull_disj_rExt45IdleFull (k_idle mCat : ℕ) (hkc : k_idle + mCat ≤ 48) :
    (rCoreTopCatFull mCat (by omega)).DisjointWires (rExt45IdleFull k_idle (by omega)) := by
  obtain ⟨hS, hI⟩ := rCoreTopCatFull_disj_sum0_idle k_idle mCat hkc
  have hCSlack : rCoreFull.DisjointWires rSlack3Full :=
    disj_of_val_ne fun i t ↦ by
      rw [rCoreFull_val_eq, rSlack3Full_val_eq]
      have hi := i.isLt
      have ht := t.isLt
      dsimp [fullSysCoreWires, fullSysBEWires, fullSysRawAncWires,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
      omega
  exact disjointWires_concat_right hS (disjointWires_concat_right
    (FullSysCatSegmentBridge.disjointWires_concat_left _ hCSlack
      ((disjointWires_compose_of_disjoint rAct0 hPG48Orig_disj_Slack3Orig).compose_left _)) hI)

open PhaseGradSignalRot (RevStep runRevList compileRevList)
open PhaseGradSignalRot (compileRevList_mulVec_ket)
open BidirectionalCatalyzedGQSP
open InterWalkRSum42Hoist (preservesFeature_of_mulVec_basisKet fixesLow3924_cSlackParkSingleCat
  fixesLow3924_cSlackUnparkSingleCat)

theorem basisBits_basisBitsEquiv_symm_eq_local {q : ℕ} (β : BitAssignment q) : basisBits q
    ((basisBitsEquiv q).symm β) = β := (basisBitsEquiv q).apply_symm_apply β

theorem RealizesOnProj.mul_right
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E_in : Operator (2 ^ n)} (P : Operator (2 ^ n))
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hd : RealizesOnProj E_in U d) :
    RealizesOnProj (E_in * P) U d := fun M ↦ by
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  have hConj : (E_in * P)ᴴ = Pᴴ * E_inᴴ := Matrix.conjTranspose_mul E_in P
  calc
    (E_in * P)ᴴ * M'.1.1 * (E_in * P)
        = Pᴴ * (E_inᴴ * M'.1.1 * E_in) * P := by rw [hConj]; simp only [Matrix.mul_assoc]
    _ = Pᴴ * (E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in) * P := by rw [hproj]
    _ = (E_in * P)ᴴ * (U.1ᴴ * M.1.1 * U.1) * (E_in * P) := by
          rw [hConj]; simp only [Matrix.mul_assoc]

theorem RealizesOnProj.embed_mul_right {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kAct n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) {E : Operator (2 ^ kAct)} (Q : Operator (2 ^ kAct))
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n} (hd : RealizesOnProj (rAct.embedMatrix E
    * rWork.basisOutcomeProjector 0) U d) : RealizesOnProj
    (rAct.embedMatrix (E * Q) * rWork.basisOutcomeProjector 0) U d := by
  have hEq : rAct.embedMatrix (E * Q) * rWork.basisOutcomeProjector 0 =
      (rAct.embedMatrix E * rWork.basisOutcomeProjector 0) * rAct.embedMatrix Q := by
    rw [rAct.embedMatrix_mul, Matrix.mul_assoc,
      (CommutesWithReg.of_disjoint hDisj Q).comm_basisOutcomeProjector 0, ← Matrix.mul_assoc]
  rw [hEq]
  exact RealizesOnProj.mul_right (rAct.embedMatrix Q) hd

theorem rCoreFull_disj_rSum0 : rCoreFull.DisjointWires rSum0 :=
  disj_of_val_ne fun i s ↦ by
    have hCore : fullSysCoreWires 80 = 4034 := rfl
    rw [rCoreFull_val_eq, rSum0_val_eq]; have := i.isLt; have := s.isLt; omega

theorem rPG48Full_disj_rSum0 : rPG48Full.DisjointWires rSum0 :=
  disj_of_val_ne fun i s ↦ by
    rw [rPG48Full_val_eq, rSum0_val_eq]; have := i.isLt; have := s.isLt; omega

theorem rCoreTopCatFull_disj_rSum0 (mCat : ℕ) (hmCat : mCat ≤ 48) :
    (rCoreTopCatFull mCat hmCat).DisjointWires rSum0 :=
  disjointWires_concat_left _ rCoreFull_disj_rSum0 (rPG48Full_disj_rSum0.compose_left _)

def rCoreTopCatSum42Full (mCat : ℕ) (hmCat : mCat ≤ 48) :
    QRegister ((fullSysCoreWires 80 + mCat) + 42) kFull80 :=
  (rCoreTopCatFull mCat hmCat).concat rSum0 (rCoreTopCatFull_disj_rSum0 mCat hmCat)

def rCoreSum42Full : QRegister (fullSysCoreWires 80 + 42) kFull80 :=
  rCoreFull.concat rSum0 rCoreFull_disj_rSum0

open SingleCatClosure
  (slackParkStepsSingleCat qCoin2InSingleCat qCoin1InSingleCat qCoin0InSingleCat
   rBECatSingleCatInAct cSlackParkSingleCat_count_T cSlackParkSingleCat_count_TOFF_le
   cSlackUnparkSingleCat_count_T cSlackUnparkSingleCat_count_TOFF_le
   cSlackUnparkSingleCat_mul_cSlackParkSingleCat cSlackParkSingleCat_on_sig1_save3
   cSlackUnparkSingleCat_on_sig1_save3 slack010_mul_cSlackParkSingleCat_sig0_save3)

/-- Slack coin `(0, 1, 0)` projector inside `kActOrig = 4,086`. -/
noncomputable def pCoinSlack010Orig : Operator (2 ^ kActOrig) :=
  (QRegister.singleton (qCoin2InSingleCat 80 48 40)).basisOutcomeProjector 0 *
  (QRegister.singleton (qCoin1InSingleCat 80 48 40)).basisOutcomeProjector 1 *
  (QRegister.singleton (qCoin0InSingleCat 80 48 40)).basisOutcomeProjector 0

/-- Boolean check that a reversible step's target wire avoids `[3951 .. 3954)` and `[4035 ..
  4083)`. -/
def revStepAvoidCtrl3PG48Bool {n : ℕ} : RevStep n → Bool
  | .x q => decide ((q.val < 3951 ∨ 3954 ≤ q.val) ∧ (q.val < 4035 ∨ 4083 ≤ q.val))
  | .cnot _ t => decide ((t.val < 3951 ∨ 3954 ≤ t.val) ∧ (t.val < 4035 ∨ 4083 ≤ t.val))
  | .toff _ _ t => decide ((t.val < 3951 ∨ 3954 ≤ t.val) ∧ (t.val < 4035 ∨ 4083 ≤ t.val))

open Classical in
theorem revStep_run_eq_avoid {n : ℕ} {s : RevStep n}
    (hs : revStepAvoidCtrl3PG48Bool s = true) (β : BitAssignment n) {w : Wire n}
    (hw : (3951 ≤ w.val ∧ w.val < 3954) ∨ (4035 ≤ w.val ∧ w.val < 4083)) :
    s.run β w = β w := by
  cases s with
  | x q =>
      have hq := of_decide_eq_true hs
      have hne : w ≠ q := fun h ↦ by subst h; rcases hw with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      simp [RevStep.run, Function.update_of_ne hne]
  | cnot c t =>
      have ht : (t.val < 3951 ∨ 3954 ≤ t.val) ∧ (t.val < 4035 ∨ 4083 ≤ t.val) :=
        of_decide_eq_true hs
      have hne : w ≠ t := fun h ↦ by subst h; rcases hw with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      dsimp [RevStep.run]
      split_ifs <;> simp [Function.update_of_ne hne]
  | toff a b t =>
      have ht := of_decide_eq_true hs
      have hne : w ≠ t := fun h ↦ by subst h; rcases hw with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
      dsimp [RevStep.run]
      split_ifs <;> simp [Function.update_of_ne hne]

theorem runRevList_eq_avoid {n : ℕ} :
    ∀ (ss : List (RevStep n)), (∀ s ∈ ss, revStepAvoidCtrl3PG48Bool s = true) →
      ∀ (β : BitAssignment n) {w : Wire n},
        ((3951 ≤ w.val ∧ w.val < 3954) ∨ (4035 ≤ w.val ∧ w.val < 4083)) →
        runRevList ss β w = β w
  | [], _, _, _, _ => rfl
  | s :: ss, hss, β, _, hw =>
      (runRevList_eq_avoid ss (fun s' hs' ↦ hss s' (List.mem_cons_of_mem s hs'))
        (s.run β) hw).trans (revStep_run_eq_avoid (hss s List.mem_cons_self) β hw)

theorem slackParkSteps80_avoid :
    ∀ s ∈ slackParkStepsSingleCat 80 48 40, revStepAvoidCtrl3PG48Bool s = true := by
  decide

/-- Idle catalyst bits extracted from `rPGIdleOrig k_idle hk` on a `kActOrig`-qubit basis index. -/
def pgIdleBits (k_idle : ℕ) (hk : k_idle ≤ 48) (x : Fin (2 ^ kActOrig)) : Fin k_idle → ZMod 2
    := fun q ↦ basisBits kActOrig x (rPGIdleOrig k_idle hk q)

open Classical in
theorem pPGIdleZeroOrig_eq_diagonal (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pPGIdleZeroOrig k_idle hk = Matrix.diagonal (fun x : Fin (2 ^ kActOrig) ↦
      if (basisBitsEquiv k_idle).symm (pgIdleBits k_idle hk x) = 0 then (1 : ℂ) else 0) := by
  unfold pPGIdleZeroOrig
  rw [(rPGIdleOrig k_idle hk).basisOutcomeProjector_eq_diagonal]
  congr 1

open Classical in
theorem compileRevList_comm_ctrl3_and_pgIdle (k_idle : ℕ) (hk : k_idle ≤ 48)
    (ss : List (RevStep kActOrig)) (hss : ∀ s ∈ ss, revStepAvoidCtrl3PG48Bool s = true) :
    (compileRevList ss).eval.1 * pCtrl3ZeroOrig = pCtrl3ZeroOrig * (compileRevList ss).eval.1
    ∧ (compileRevList ss).eval.1 * pPGIdleZeroOrig k_idle hk = pPGIdleZeroOrig k_idle hk *
    (compileRevList ss).eval.1 := by
  have hket : ∀ β : BitAssignment kActOrig, (compileRevList ss).eval.1.mulVec (basisKet β) =
      basisKet (runRevList ss β) := compileRevList_mulVec_ket ss
  have hC : FixesCtrl3 h3954_actOrig (compileRevList ss).eval.1 := by
    refine preservesFeature_of_mulVec_basisKet (ctrl3Bits h3954_actOrig) _
      (runRevList ss) hket (fun j ↦ ?_)
    funext t; dsimp only [ctrl3Bits]; rw [basisBits_basisBitsEquiv_symm_eq_local]
    exact runRevList_eq_avoid ss hss (basisBits kActOrig j)
      (Or.inl ⟨by simp only; omega, by simp only; have := t.isLt; omega⟩)
  have hI : PreservesFeature (pgIdleBits k_idle hk) (compileRevList ss).eval.1 := by
    refine preservesFeature_of_mulVec_basisKet (pgIdleBits k_idle hk) _
      (runRevList ss) hket (fun j ↦ ?_)
    funext q; dsimp only [pgIdleBits]; rw [basisBits_basisBitsEquiv_symm_eq_local]
    refine runRevList_eq_avoid ss hss (basisBits kActOrig j) (Or.inr ?_)
    rw [rPGIdleOrig_val_eq]; have := q.isLt; omega
  refine ⟨hC.comm_pCtrl3ZeroOrig, ?_⟩
  rw [pPGIdleZeroOrig_eq_diagonal]
  exact PreservesFeature.comm_diagonal
    (fun c : Fin k_idle → ZMod 2 ↦ if (basisBitsEquiv k_idle).symm c = 0 then (1 : ℂ) else 0) hI

open Classical in
private theorem embedAct0_comm_E_ctrl3Ext {U : Unitary (2 ^ kActOrig)} (k_idle : ℕ)
    (hk : k_idle ≤ 48)
    (hS : (rAct0.embedUnitary U).1 * E_stream42 = E_stream42 * (rAct0.embedUnitary U).1)
    (hCI : U.1 * pCtrl3ZeroOrig = pCtrl3ZeroOrig * U.1 ∧
      U.1 * pPGIdleZeroOrig k_idle hk = pPGIdleZeroOrig k_idle hk * U.1) :
    (rAct0.embedUnitary U).1 * E_ctrl3Ext k_idle hk =
      E_ctrl3Ext k_idle hk * (rAct0.embedUnitary U).1 := by
  have hC : (rAct0.embedUnitary U).1 * pCtrl3Zero = pCtrl3Zero * (rAct0.embedUnitary U).1 := by
    rw [← embedAct0_pCtrl3ZeroOrig, QRegister.embedUnitary_val, ← rAct0.embedMatrix_mul,
      ← rAct0.embedMatrix_mul]
    exact congrArg rAct0.embedMatrix hCI.1
  have hI : (rAct0.embedUnitary U).1 * pPGIdleZero k_idle hk =
      pPGIdleZero k_idle hk * (rAct0.embedUnitary U).1 := by
    have hEmb : rAct0.embedMatrix (pPGIdleZeroOrig k_idle hk) = pPGIdleZero k_idle hk :=
      (QRegister.embedMatrix_compose rAct0 (rPGIdleOrig k_idle hk) (compProj 0)).symm
    rw [← hEmb, QRegister.embedUnitary_val, ← rAct0.embedMatrix_mul, ← rAct0.embedMatrix_mul]
    exact congrArg rAct0.embedMatrix hCI.2
  unfold E_ctrl3Ext
  rw [← Matrix.mul_assoc, hS, Matrix.mul_assoc E_stream42, ← Matrix.mul_assoc _ pCtrl3Zero,
    hC, Matrix.mul_assoc pCtrl3Zero, hI, ← Matrix.mul_assoc pCtrl3Zero,
    ← Matrix.mul_assoc E_stream42]

open Classical in
theorem cSlackPark_comm_E_ctrl3Ext (k_idle : ℕ) (hk : k_idle ≤ 48) :
    (rAct0.embedUnitary (cSlackParkSingleCat 80 48 40).eval).1 * E_ctrl3Ext k_idle hk =
      E_ctrl3Ext k_idle hk * (rAct0.embedUnitary (cSlackParkSingleCat 80 48 40).eval).1 :=
  embedAct0_comm_E_ctrl3Ext k_idle hk
    (embedAct0_fixesLow3924_comm_E_stream42 fixesLow3924_cSlackParkSingleCat)
    (compileRevList_comm_ctrl3_and_pgIdle k_idle hk _ slackParkSteps80_avoid)

open Classical in
theorem cSlackUnpark_comm_E_ctrl3Ext (k_idle : ℕ) (hk : k_idle ≤ 48) :
    (rAct0.embedUnitary (cSlackUnparkSingleCat 80 48 40).eval).1 * E_ctrl3Ext k_idle hk =
      E_ctrl3Ext k_idle hk * (rAct0.embedUnitary (cSlackUnparkSingleCat 80 48 40).eval).1 :=
  embedAct0_comm_E_ctrl3Ext k_idle hk
    (embedAct0_fixesLow3924_comm_E_stream42 fixesLow3924_cSlackUnparkSingleCat)
    (compileRevList_comm_ctrl3_and_pgIdle k_idle hk _
      fun s hs ↦ slackParkSteps80_avoid s (List.mem_reverse.mp hs))

theorem singleton_proj_zero_add_one_local {n : ℕ} (w : Wire n) :
    (QRegister.singleton w).basisOutcomeProjector 0 +
      (QRegister.singleton w).basisOutcomeProjector 1 = 1 := by
  rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1; ext x
  generalize (QRegister.singleton w).extractIndex x = u
  by_cases h0 : u = 0
  · have h01 : (0 : Fin (2 ^ 1)) ≠ 1 := by decide
    simp [h0, h01]
  · have h1 : u = 1 := by
      have hv0 : u.val ≠ 0 := fun hv ↦ h0 (Fin.ext hv)
      have hlt : u.val < 2 := u.isLt
      apply Fin.ext; change u.val = 1; omega
    have h10 : (1 : Fin (2 ^ 1)) ≠ 0 := by decide
    simp [h1, h10]

theorem basisOutcomeProjector_idem {m n : ℕ} (r : QRegister m n) (x : Fin (2 ^ m)) :
    r.basisOutcomeProjector x * r.basisOutcomeProjector x = r.basisOutcomeProjector x := by
  rw [r.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; ext y; by_cases h : r.extractIndex y = x <;> simp [h]

theorem unitary_conjTranspose_eq_of_left_inv {d : ℕ} (U V : Unitary d) (hVU : V.1 * U.1 = 1) :
    U.1ᴴ = V.1 ∧ V.1ᴴ = U.1 := by
  have hUUH : U.1 * U.1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (show (U * U⁻¹).1 = 1 by rw [mul_inv_cancel, OneMemClass.coe_one])
  have h1 : U.1ᴴ = V.1 := by
    calc U.1ᴴ = 1 * U.1ᴴ := (Matrix.one_mul _).symm
      _ = (V.1 * U.1) * U.1ᴴ := by rw [hVU]
      _ = V.1 * (U.1 * U.1ᴴ) := by rw [Matrix.mul_assoc]
      _ = V.1 := by rw [hUUH, Matrix.mul_one]
  exact ⟨h1, by rw [← h1, Matrix.conjTranspose_conjTranspose]⟩

theorem comm_proj_of_left_absorb_and_adj_absorb {d : ℕ} {M P : Operator d} (hPH : Pᴴ = P)
    (hFwd : P * (M * P) = M * P) (hBwd : P * (Mᴴ * P) = Mᴴ * P) : M * P = P * M := by
  have hAdj := congrArg Matrix.conjTranspose hBwd
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hPH, Matrix.mul_assoc] at hAdj
  rw [← hFwd, hAdj]

theorem ctrlSandwich_left_absorb_pSlack3ZeroOrig (Up UpInv Us : Operator (2 ^ kActOrig))
    (hPinvP : UpInv * Up = 1) (hPsig0 : Up * (QRegister.singleton (qSigInSingleCat 80 48
    40)).basisOutcomeProjector 0 = (QRegister.singleton (qSigInSingleCat 80 48
    40)).basisOutcomeProjector 0 * Up) (hPsig1 : Up * (QRegister.singleton (qSigInSingleCat 80
    48 40)).basisOutcomeProjector 1 = (QRegister.singleton (qSigInSingleCat 80 48
    40)).basisOutcomeProjector 1 * Up) (hPsave : Up * pSlack3ZeroOrig = pSlack3ZeroOrig * Up)
    (hPinvsig0 : UpInv * (QRegister.singleton (qSigInSingleCat 80 48
    40)).basisOutcomeProjector 0 = (QRegister.singleton (qSigInSingleCat 80 48
    40)).basisOutcomeProjector 0 * UpInv) (hPinvsig1 : UpInv * (QRegister.singleton
    (qSigInSingleCat 80 48 40)).basisOutcomeProjector 1 = (QRegister.singleton
    (qSigInSingleCat 80 48 40)).basisOutcomeProjector 1 * UpInv)
    (hPinvsave : UpInv * pSlack3ZeroOrig = pSlack3ZeroOrig * UpInv) (hSsig1 : Us *
    (QRegister.singleton (qSigInSingleCat 80 48 40)).basisOutcomeProjector 1 =
    (QRegister.singleton (qSigInSingleCat 80 48 40)).basisOutcomeProjector 1 * Us)
    (hSsave : Us * pSlack3ZeroOrig = pSlack3ZeroOrig * Us)
    (hSslack : Us * pCoinSlack010Orig = pCoinSlack010Orig) : pSlack3ZeroOrig * ((UpInv *
    ((cSlackUnparkSingleCat 80 48 40).eval.1 * (Us * ((cSlackParkSingleCat 80 48 40).eval.1 *
    Up)))) * pSlack3ZeroOrig) = (UpInv * ((cSlackUnparkSingleCat 80 48 40).eval.1 * (Us *
    ((cSlackParkSingleCat 80 48 40).eval.1 * Up)))) * pSlack3ZeroOrig := by
  let W := UpInv * ((cSlackUnparkSingleCat 80 48 40).eval.1 *
    (Us * ((cSlackParkSingleCat 80 48 40).eval.1 * Up)))
  let P0 := (QRegister.singleton (qSigInSingleCat 80 48 40)).basisOutcomeProjector 0
  let P1 := (QRegister.singleton (qSigInSingleCat 80 48 40)).basisOutcomeProjector 1
  let Ps := pSlack3ZeroOrig
  let Upk := (cSlackParkSingleCat 80 48 40).eval.1
  let Uunpk := (cSlackUnparkSingleCat 80 48 40).eval.1
  have hUV : Uunpk * Upk = 1 := cSlackUnparkSingleCat_mul_cSlackParkSingleCat 80 48 40
  have hPark0 : pCoinSlack010Orig * (Upk * (P0 * Ps)) = Upk * (P0 * Ps) :=
    slack010_mul_cSlackParkSingleCat_sig0_save3 80 48 40
  have hPark1 : Upk * (P1 * Ps) = P1 * Ps := cSlackParkSingleCat_on_sig1_save3 80 48 40
  have hUnpark1 : Uunpk * (P1 * Ps) = P1 * Ps := cSlackUnparkSingleCat_on_sig1_save3 80 48 40
  have hPsIdem : Ps * Ps = Ps := basisOutcomeProjector_idem rSlack3Orig 0
  have hPsP0 : Ps * P0 = P0 * Ps :=
    basisOutcomeProjector_comm_any rSlack3Orig 0 (QRegister.singleton (qSigInSingleCat 80 48 40)) 0
  have hPsP1 : Ps * P1 = P1 * Ps :=
    basisOutcomeProjector_comm_any rSlack3Orig 0 (QRegister.singleton (qSigInSingleCat 80 48 40)) 1
  have hB0 : W * (P0 * Ps) = P0 * Ps := by
    have hcP : Up * (P0 * Ps) = (P0 * Ps) * Up := by
      rw [← Matrix.mul_assoc, hPsig0, Matrix.mul_assoc, hPsave, Matrix.mul_assoc]
    have hcPi : UpInv * (P0 * Ps) = (P0 * Ps) * UpInv := by
      rw [← Matrix.mul_assoc, hPinvsig0, Matrix.mul_assoc, hPinvsave, Matrix.mul_assoc]
    have hSlk : Us * (Upk * (P0 * Ps)) = Upk * (P0 * Ps) := by
      calc Us * (Upk * (P0 * Ps))
        _ = Us * (pCoinSlack010Orig * (Upk * (P0 * Ps))) := by rw [hPark0]
        _ = (Us * pCoinSlack010Orig) * (Upk * (P0 * Ps)) := by rw [← Matrix.mul_assoc]
        _ = Upk * (P0 * Ps) := by rw [hSslack, hPark0]
    change UpInv * (Uunpk * (Us * (Upk * Up))) * (P0 * Ps) = P0 * Ps
    calc UpInv * (Uunpk * (Us * (Upk * Up))) * (P0 * Ps)
      _ = UpInv * (Uunpk * (Us * (Upk * (Up * (P0 * Ps))))) := by simp only [Matrix.mul_assoc]
      _ = UpInv * (Uunpk * ((Us * (Upk * (P0 * Ps))) * Up)) := by
            rw [hcP]; simp only [Matrix.mul_assoc]
      _ = UpInv * ((Uunpk * Upk) * (P0 * Ps) * Up) := by
            rw [hSlk]; simp only [Matrix.mul_assoc]
      _ = (UpInv * (P0 * Ps)) * Up := by rw [hUV, Matrix.one_mul, ← Matrix.mul_assoc]
      _ = P0 * Ps := by rw [hcPi, Matrix.mul_assoc, hPinvP, Matrix.mul_one]
  have hB1 : W * (P1 * Ps) = (P1 * Ps) * (UpInv * (Us * Up)) := by
    have hcP : Up * (P1 * Ps) = (P1 * Ps) * Up := by
      rw [← Matrix.mul_assoc, hPsig1, Matrix.mul_assoc, hPsave, Matrix.mul_assoc]
    have hcS : Us * (P1 * Ps) = (P1 * Ps) * Us := by
      rw [← Matrix.mul_assoc, hSsig1, Matrix.mul_assoc, hSsave, Matrix.mul_assoc]
    have hcPi : UpInv * (P1 * Ps) = (P1 * Ps) * UpInv := by
      rw [← Matrix.mul_assoc, hPinvsig1, Matrix.mul_assoc, hPinvsave, Matrix.mul_assoc]
    change UpInv * (Uunpk * (Us * (Upk * Up))) * (P1 * Ps) = (P1 * Ps) * (UpInv * (Us * Up))
    calc UpInv * (Uunpk * (Us * (Upk * Up))) * (P1 * Ps)
      _ = UpInv * (Uunpk * (Us * (Upk * (Up * (P1 * Ps))))) := by simp only [Matrix.mul_assoc]
      _ = UpInv * (Uunpk * (Us * ((Upk * (P1 * Ps)) * Up))) := by
            rw [hcP, ← Matrix.mul_assoc Upk]
      _ = UpInv * ((Uunpk * (P1 * Ps)) * (Us * Up)) := by
            rw [hPark1, ← Matrix.mul_assoc Us, hcS]; simp only [Matrix.mul_assoc]
      _ = (UpInv * (P1 * Ps)) * (Us * Up) := by rw [hUnpark1, ← Matrix.mul_assoc]
      _ = (P1 * Ps) * (UpInv * (Us * Up)) := by rw [hcPi, Matrix.mul_assoc]
  have hDecomp : W * Ps = W * (P0 * Ps) + W * (P1 * Ps) := by
    calc W * Ps = W * ((P0 + P1) * Ps) := by
            rw [singleton_proj_zero_add_one_local (qSigInSingleCat 80 48 40), Matrix.one_mul]
      _ = W * (P0 * Ps) + W * (P1 * Ps) := by rw [Matrix.add_mul, Matrix.mul_add]
  change Ps * (W * Ps) = W * Ps
  rw [hDecomp, hB0, hB1, Matrix.mul_add]
  have hL0 : Ps * (P0 * Ps) = P0 * Ps := by
    rw [← Matrix.mul_assoc, hPsP0, Matrix.mul_assoc, hPsIdem]
  have hL1 : Ps * ((P1 * Ps) * (UpInv * (Us * Up))) = (P1 * Ps) * (UpInv * (Us * Up)) := by
    rw [← Matrix.mul_assoc Ps, ← Matrix.mul_assoc Ps, hPsP1, Matrix.mul_assoc P1, hPsIdem]
  rw [hL0, hL1]

theorem rBEOrig_val_eq (i : Fin (fullSysBEWires 80)) : (rBEOrig i).val = i.val := by
  simp [rBEOrig, rBEInSingleCat]

theorem rBEOrig_val_lt_4034 (i : Fin (fullSysBEWires 80)) : (rBEOrig i).val < 4034 := by
  have := i.isLt
  dsimp [rBEOrig, rBEInSingleCat, qreg_block_apply, fullSysBEWires, fullSysRawAncWires,
    SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at this ⊢
  omega

open Classical in
theorem uCtrlRawBESingleCat_comm_pSlack3ZeroOrig {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48} (prep : FullSysPrepareBundle 80)
    (selImpl : SingleCatSelectImpl 80 48 qft selOra) (c : Configuration) (hSelSlack010 :
    (rSegOrig.embedUnitary (selImpl.uSelCat c)).1 * pCoinSlack010Orig = pCoinSlack010Orig) :
    (uCtrlRawBESingleCat prep selImpl c).1 * pSlack3ZeroOrig = pSlack3ZeroOrig *
    (uCtrlRawBESingleCat prep selImpl c).1 := by
  let U_p := rBEOrig.embedUnitary (prep.uPrep c)
  let U_pi := rBEOrig.embedUnitary (prep.uPrep c)⁻¹
  let U_s := rSegOrig.embedUnitary (selImpl.uSelCat c)
  have hBE_qSig : rBEOrig.DisjointWires (QRegister.singleton (qSigInSingleCat 80 48 40)) :=
    disj_of_val_ne fun i idx ↦ by
      fin_cases idx
      rw [QRegister.singleton_apply]
      change (rBEOrig i).val ≠ (qSigInSingleCat 80 48 40).val
      have hq : (qSigInSingleCat 80 48 40).val = 4034 := by decide
      rw [hq]; have := rBEOrig_val_lt_4034 i; omega
  have hBE_slk : rBEOrig.DisjointWires rSlack3Orig :=
    disj_of_val_ne fun i t ↦ by
      rw [rSlack3Orig_val_eq]
      have := rBEOrig_val_lt_4034 i; have := t.isLt; omega
  have hSeg_qSig : rSegOrig.DisjointWires (QRegister.singleton (qSigInSingleCat 80 48 40)) :=
    disj_of_val_ne fun idx j ↦ by
      fin_cases j
      rw [QRegister.singleton_apply]
      change (rSegOrig idx).val ≠ (qSigInSingleCat 80 48 40).val
      have hq : (qSigInSingleCat 80 48 40).val = 4034 := by decide
      rw [hq]
      refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) idx
      · simp only [rSegOrig, rBECatSingleCatInAct, QRegister.concat_apply_left]
        change (rBEOrig i).val ≠ 4034
        have := rBEOrig_val_lt_4034 i; omega
      · simp only [rSegOrig, rBECatSingleCatInAct, QRegister.concat_apply_right,
          rCatTotInSingleCat80_eq_rPG48Orig]
        rw [rPG48Orig_val_eq]; omega
  have hCat_slk : (rCatTotInSingleCat 80 48 40).DisjointWires rSlack3Orig := by
    rw [rCatTotInSingleCat80_eq_rPG48Orig]; exact hPG48Orig_disj_Slack3Orig
  have hSeg_slk : rSegOrig.DisjointWires rSlack3Orig :=
    disjointWires_concat_left _ hBE_slk hCat_slk
  have hUpInv : U_p⁻¹ = U_pi := embedUnitary_inv_symm _ _
  have hUsInv : U_s⁻¹ = rSegOrig.embedUnitary (selImpl.uSelCat c)⁻¹ := embedUnitary_inv_symm _ _
  have hPinvP : U_pi.1 * U_p.1 = 1 := by
    rw [← hUpInv, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  have hSinvSlack : (U_s⁻¹).1 * pCoinSlack010Orig = pCoinSlack010Orig := by
    calc (U_s⁻¹).1 * pCoinSlack010Orig
      _ = (U_s⁻¹).1 * (U_s.1 * pCoinSlack010Orig) := congrArg ((U_s⁻¹).1 * ·) hSelSlack010.symm
      _ = (U_s⁻¹ * U_s).1 * pCoinSlack010Orig := by rw [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = pCoinSlack010Orig := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  have hFwd := ctrlSandwich_left_absorb_pSlack3ZeroOrig U_p.1 U_pi.1 U_s.1 hPinvP
      ((CommutesWithReg.of_disjoint hBE_qSig _).comm_basisOutcomeProjector 0)
      ((CommutesWithReg.of_disjoint hBE_qSig _).comm_basisOutcomeProjector 1)
      ((CommutesWithReg.of_disjoint hBE_slk _).comm_basisOutcomeProjector 0)
      ((CommutesWithReg.of_disjoint hBE_qSig _).comm_basisOutcomeProjector 0)
      ((CommutesWithReg.of_disjoint hBE_qSig _).comm_basisOutcomeProjector 1)
      ((CommutesWithReg.of_disjoint hBE_slk _).comm_basisOutcomeProjector 0)
      ((CommutesWithReg.of_disjoint hSeg_qSig _).comm_basisOutcomeProjector 1)
      ((CommutesWithReg.of_disjoint hSeg_slk _).comm_basisOutcomeProjector 0) hSelSlack010
  have hBwd := ctrlSandwich_left_absorb_pSlack3ZeroOrig U_p.1 U_pi.1 (U_s⁻¹).1 hPinvP
    ((CommutesWithReg.of_disjoint hBE_qSig _).comm_basisOutcomeProjector 0)
    ((CommutesWithReg.of_disjoint hBE_qSig _).comm_basisOutcomeProjector 1)
    ((CommutesWithReg.of_disjoint hBE_slk _).comm_basisOutcomeProjector 0)
    ((CommutesWithReg.of_disjoint hBE_qSig _).comm_basisOutcomeProjector 0)
    ((CommutesWithReg.of_disjoint hBE_qSig _).comm_basisOutcomeProjector 1)
    ((CommutesWithReg.of_disjoint hBE_slk _).comm_basisOutcomeProjector 0)
    (by rw [hUsInv]; exact (CommutesWithReg.of_disjoint hSeg_qSig _).comm_basisOutcomeProjector 1)
    (by rw [hUsInv]; exact (CommutesWithReg.of_disjoint hSeg_slk _).comm_basisOutcomeProjector 0)
    hSinvSlack
  obtain ⟨hUpkH, hUunpkH⟩ := unitary_conjTranspose_eq_of_left_inv
    (cSlackParkSingleCat 80 48 40).eval (cSlackUnparkSingleCat 80 48 40).eval
    (cSlackUnparkSingleCat_mul_cSlackParkSingleCat 80 48 40)
  have hUpH : U_p.1ᴴ = U_pi.1 := by
    rw [← hUpInv]; exact (Matrix.star_eq_conjTranspose U_p.1).symm
  have hUpiH : U_pi.1ᴴ = U_p.1 := by
    rw [← hUpH, Matrix.conjTranspose_conjTranspose]
  have hUsH : U_s.1ᴴ = (U_s⁻¹).1 := (Matrix.star_eq_conjTranspose U_s.1).symm
  have hWVal : (uCtrlRawBESingleCat prep selImpl c).1 = U_pi.1 * ((cSlackUnparkSingleCat 80 48
      40).eval.1 * (U_s.1 * ((cSlackParkSingleCat 80 48 40).eval.1 * U_p.1))) := by
    dsimp only [uCtrlRawBESingleCat, U_p, U_pi, U_s]
    simp only [Submonoid.coe_mul]
  have hWHVal : ((uCtrlRawBESingleCat prep selImpl c).1)ᴴ = U_pi.1 * ((cSlackUnparkSingleCat
      80 48 40).eval.1 * ((U_s⁻¹).1 * ((cSlackParkSingleCat 80 48 40).eval.1 * U_p.1))) := by
    rw [hWVal]
    simp only [Matrix.conjTranspose_mul, hUpH, hUpiH, hUsH, hUpkH, hUunpkH, Matrix.mul_assoc]
  exact comm_proj_of_left_absorb_and_adj_absorb
    (basisOutcomeProjector_conjTranspose rSlack3Orig 0)
    (by rw [hWVal]; exact hFwd)
    (by rw [hWHVal]; exact hBwd)

/-- Asymmetric hoisted `SELECT` specification on `(rAct, rWork)` (`mWork` external clean wires,
with `dSelectCtrl` intertwining `E_ctrl3Ext k_idle hk` during coin-parked endpoint `ctrlRawBE`
and `dSelectCat` intertwining `E_segExt k_idle hk` during interior `catRawBE`). -/
structure HoistedExtHkSelectSpec
    (mWork k_idle : ℕ) (hk : k_idle ≤ 48)
    (tSelCtrl tSelCat : ℕ)
    (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (selImpl : SingleCatSelectImpl 80 48 qft selOra) where
  uSelectCtrl : Configuration → Unitary (2 ^ kFull80)
  uSelectCat : Configuration → Unitary (2 ^ kFull80)
  dSelectCtrl : Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rAct : QRegister kFull80 n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  dSelectCat : Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rAct : QRegister kFull80 n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  hToffCtrl : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dSelectCtrl c v rAct rWork hDisj).count .TOFF = 0
  hToffCat : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dSelectCat c v rAct rWork hDisj).count .TOFF = 0
  hTCtrl : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dSelectCtrl c v rAct rWork hDisj).count .T ≤ tSelCtrl
  hTCat : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork),
    (dSelectCat c v rAct rWork hDisj).count .T ≤ tSelCat
  hRealCtrl : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork),
    RealizesOnProj (pCtrl3ExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary (uSelectCtrl c))
      (dSelectCtrl c v rAct rWork hDisj)
  hRealCat : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork),
    RealizesOnProj (pHoistExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary (uSelectCat c))
      (dSelectCat c v rAct rWork hDisj)
  hSelCtrlE : ∀ c,
    (uSelectCtrl c).1 * E_ctrl3Ext k_idle hk =
      E_ctrl3Ext k_idle hk * (rAct0.embedUnitary (rSegOrig.embedUnitary (selImpl.uSelCat c))).1
  hSelCatE : ∀ c,
    (uSelectCat c).1 * E_segExt k_idle hk =
      E_segExt k_idle hk * (rAct0.embedUnitary (rSegOrig.embedUnitary (selImpl.uSelCat c))).1
  hSelSlack010 : ∀ c,
    (rSegOrig.embedUnitary (selImpl.uSelCat c)).1 * pCoinSlack010Orig = pCoinSlack010Orig
  hSelIdle : ∀ c,
    CommutesWithReg (rPGIdleOrig k_idle hk)
      (rSegOrig.embedUnitary (selImpl.uSelCat c)).1

theorem E_segExt_eq_E_ctrl3Ext_mul_pSlack3 (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_segExt k_idle hk = E_ctrl3Ext k_idle hk * pSlack3Zero := by
  unfold E_segExt E_ctrl3Ext
  rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul, Matrix.mul_assoc pCtrl3Zero]
  unfold pSlack3Zero pPGIdleZero
  rw [basisOutcomeProjector_comm_any rSlack3Full 0 (rPGIdle k_idle hk) 0,
    ← Matrix.mul_assoc pCtrl3Zero, ← Matrix.mul_assoc E_stream42]

theorem comm_op_mul {d : ℕ} {A A' B B' E : Operator d} (hA : A * E = E * A')
    (hB : B * E = E * B') : (A * B) * E = E * (A' * B') := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

open Classical in
theorem rBEFull_comm_E_ctrl3Ext_and_segExt
    (k_idle : ℕ) (hk : k_idle ≤ 48) (U : Unitary (2 ^ (fullSysBEWires 80)))
    (hLow : FixesLow3924 h3924_be U.1) (hCtrl3 : FixesCtrl3 h3954_be U.1) :
    ((rAct0.compose rBEOrig).embedUnitary U).1 * E_ctrl3Ext k_idle hk =
      E_ctrl3Ext k_idle hk * (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 ∧
    ((rAct0.compose rBEOrig).embedUnitary U).1 * E_segExt k_idle hk =
      E_segExt k_idle hk * (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 := by
  have hComp : (rAct0.compose rBEOrig).embedUnitary U =
      rAct0.embedUnitary (rBEOrig.embedUnitary U) := QRegister.embedUnitary_compose rAct0 rBEOrig U
  have hS : (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 * E_stream42 =
      E_stream42 * (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 := by
    refine embedAct0_fixesLow3924_comm_E_stream42 ?_
    rw [QRegister.embedUnitary_val]
    exact fixesLow3924_embedMatrix_prefix isLow3924Prefix_rBEOrig hLow
  have hC : (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 * pCtrl3Zero =
      pCtrl3Zero * (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 := by
    rw [← embedAct0_pCtrl3ZeroOrig, QRegister.embedUnitary_val, ← rAct0.embedMatrix_mul,
      ← rAct0.embedMatrix_mul]
    exact congrArg rAct0.embedMatrix
      (fixesCtrl3_embedMatrix_prefix isCtrl3Prefix_rBEOrig hCtrl3).comm_pCtrl3ZeroOrig
  have hDisjI : (rAct0.compose rBEOrig).DisjointWires (rPGIdle k_idle hk) :=
    disjointWires_compose_of_disjoint rAct0 (disj_of_val_ne fun i q ↦ by
      rw [rPGIdleOrig_val_eq]; have := rBEOrig_val_lt_4034 i; have := q.isLt; omega)
  have hDisjSlk : (rAct0.compose rBEOrig).DisjointWires rSlack3Full :=
    disjointWires_compose_of_disjoint rAct0 (disj_of_val_ne fun i t ↦ by
      rw [rSlack3Orig_val_eq]; have := rBEOrig_val_lt_4034 i; have := t.isLt; omega)
  have hI : (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 * pPGIdleZero k_idle hk =
      pPGIdleZero k_idle hk * (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 := by
    rw [← hComp, QRegister.embedUnitary_val]
    exact (CommutesWithReg.of_disjoint hDisjI _).comm_basisOutcomeProjector 0
  have hSlk : (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 * pSlack3Zero =
      pSlack3Zero * (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 := by
    rw [← hComp, QRegister.embedUnitary_val]
    exact (CommutesWithReg.of_disjoint hDisjSlk _).comm_basisOutcomeProjector 0
  have hCtrlE : (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 * E_ctrl3Ext k_idle hk =
      E_ctrl3Ext k_idle hk * (rAct0.embedUnitary (rBEOrig.embedUnitary U)).1 := by
    unfold E_ctrl3Ext
    rw [← Matrix.mul_assoc, hS, Matrix.mul_assoc E_stream42, ← Matrix.mul_assoc _ pCtrl3Zero,
      hC, Matrix.mul_assoc pCtrl3Zero, hI, ← Matrix.mul_assoc pCtrl3Zero,
        ← Matrix.mul_assoc E_stream42]
  rw [hComp]
  refine ⟨hCtrlE, ?_⟩
  rw [E_segExt_eq_E_ctrl3Ext_mul_pSlack3, ← Matrix.mul_assoc, hCtrlE, Matrix.mul_assoc,
    hSlk, ← Matrix.mul_assoc]

/-- Catalyzed `rawBE` active unitary on `kFull80` for `HoistedExtHkSelectSpec`. -/
noncomputable def uCatRawBEExtHk {mWork k_idle tSelCtrl tSelCat : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (prep : FullSysPrepareBundle 80) (sel :
    HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (c : Configuration) : Unitary (2 ^ kFull80) :=
  let rBEFull := rAct0.compose rBEOrig
  rBEFull.embedUnitary (prep.uPrep c)⁻¹ *
    (sel.uSelectCat c * rBEFull.embedUnitary (prep.uPrep c))

/-- `qSig`-controlled `rawBE` active unitary on `kFull80` for `HoistedExtHkSelectSpec`. -/
noncomputable def uCtrlRawBEExtHk {mWork k_idle tSelCtrl tSelCat : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (prep : FullSysPrepareBundle 80) (sel :
    HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (c : Configuration) : Unitary (2 ^ kFull80) :=
  let rBEFull := rAct0.compose rBEOrig
  rBEFull.embedUnitary (prep.uPrep c)⁻¹ *
    (rAct0.embedUnitary (cSlackUnparkSingleCat 80 48 40).eval *
      (sel.uSelectCtrl c *
        (rAct0.embedUnitary (cSlackParkSingleCat 80 48 40).eval *
          rBEFull.embedUnitary (prep.uPrep c))))

/-- Catalyzed `rawBE` dynamic circuit on `(kFull80, mWork)` for `HoistedExtHkSelectSpec`. -/
noncomputable def catRawBEExtHkDyn {Var : Type} {mWork k_idle tSelCtrl tSelCat n : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (prep : FullSysPrepareBundle 80) (sel :
    HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (hmPrep : prep.mWorkPrep ≤ mWork) (c : Configuration) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rBE := (rAct.compose rAct0).compose rBEOrig
    let rWP := rWork.compose (QRegister.block 0 prep.mWorkPrep (fullSys_zero_add_le_of_le hmPrep))
    let hBE_WP : rBE.DisjointWires rWP :=
      ((hDisj.compose_left rAct0).compose_left _).compose_right _
    DynCircuitExt.sequenceList [
      prep.dPrep c v rBE rWP hBE_WP,
      sel.dSelectCat c v rAct rWork hDisj,
      prep.dPrepInv c v rBE rWP hBE_WP
    ]

/-- `qSig`-controlled `rawBE` dynamic circuit on `(kFull80, mWork)` for `HoistedExtHkSelectSpec`. -/
noncomputable def ctrlRawBEExtHkDyn {Var : Type} {mWork k_idle tSelCtrl tSelCat n : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (c : Configuration)
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rAct170 := rAct.compose rAct0
    let rBE := rAct170.compose rBEOrig
    let rWP := rWork.compose (QRegister.block 0 prep.mWorkPrep (fullSys_zero_add_le_of_le hmPrep))
    let hBE_WP : rBE.DisjointWires rWP :=
      ((hDisj.compose_left rAct0).compose_left _).compose_right _
    DynCircuitExt.sequenceList [
      prep.dPrep c v rBE rWP hBE_WP,
      substActiveSingleCat hm1 v rAct170 rWork (cSlackParkSingleCat 80 48 40),
      sel.dSelectCtrl c v rAct rWork hDisj,
      substActiveSingleCat hm1 v rAct170 rWork (cSlackUnparkSingleCat 80 48 40),
      prep.dPrepInv c v rBE rWP hBE_WP
    ]

theorem catRawBEExtHkDyn_counts {Var : Type} {mWork k_idle tSelCtrl tSelCat n : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (prep : FullSysPrepareBundle 80) (sel :
    HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (hmPrep : prep.mWorkPrep ≤ mWork) (c : Configuration) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (catRawBEExtHkDyn prep sel hmPrep c v rAct rWork hDisj).count .TOFF = 0 ∧
    (catRawBEExtHkDyn prep sel hmPrep c v rAct rWork hDisj).count .T ≤ 2 * prep.tPrep +
    tSelCat := by
  let rBE := (rAct.compose rAct0).compose rBEOrig
  let rWP := rWork.compose (QRegister.block 0 prep.mWorkPrep (fullSys_zero_add_le_of_le hmPrep))
  let hBE_WP : rBE.DisjointWires rWP := ((hDisj.compose_left rAct0).compose_left _).compose_right _
  have hp1 := prep.hTPrep c v rBE rWP hBE_WP
  have hs := sel.hTCat c v rAct rWork hDisj
  have hp2 := prep.hTPrepInv c v rBE rWP hBE_WP
  rw [catRawBEExtHkDyn, vepLockVal_eq]
  simp only [DynCircuitExt.count_sequenceList, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  refine ⟨by rw [prep.hToffPrep, sel.hToffCat, prep.hToffPrepInv]; rfl, ?_⟩
  exact (Nat.add_le_add hp1 (Nat.add_le_add hs (Nat.add_le_add hp2 (le_refl 0)))).trans (by omega)

theorem ctrlRawBEExtHkDyn_counts {Var : Type} {mWork k_idle tSelCtrl tSelCat n : ℕ}
    {hk : k_idle ≤ 48} {qft : FullSysQft654Bundle}
    {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (c : Configuration)
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) :
    (ctrlRawBEExtHkDyn hm1 prep sel hmPrep c v rAct rWork hDisj).count .TOFF = 0 ∧
    (ctrlRawBEExtHkDyn hm1 prep sel hmPrep c v rAct rWork hDisj).count .T ≤ 2 * prep.tPrep +
    tSelCtrl + 24 := by
  let rAct170 := rAct.compose rAct0
  let rBE := rAct170.compose rBEOrig
  let rWP := rWork.compose (QRegister.block 0 prep.mWorkPrep (fullSys_zero_add_le_of_le hmPrep))
  let hBE_WP : rBE.DisjointWires rWP := ((hDisj.compose_left rAct0).compose_left _).compose_right _
  have hp1 := prep.hTPrep c v rBE rWP hBE_WP
  have hs := sel.hTCtrl c v rAct rWork hDisj
  have hp2 := prep.hTPrepInv c v rBE rWP hBE_WP
  have hPk : (substActiveSingleCat hm1 v rAct170 rWork
      (cSlackParkSingleCat 80 48 40)).count .T ≤ 12 := by
    refine (substActiveSingleCat_count_T_le hm1 v rAct170 rWork _).trans ?_
    have ht := cSlackParkSingleCat_count_T 80 48 40
    have htoff := cSlackParkSingleCat_count_TOFF_le 80 48 40
    omega
  have hUnpk : (substActiveSingleCat hm1 v rAct170 rWork
      (cSlackUnparkSingleCat 80 48 40)).count .T ≤ 12 := by
    refine (substActiveSingleCat_count_T_le hm1 v rAct170 rWork _).trans ?_
    have ht := cSlackUnparkSingleCat_count_T 80 48 40
    have htoff := cSlackUnparkSingleCat_count_TOFF_le 80 48 40
    omega
  rw [ctrlRawBEExtHkDyn, vepLockVal_eq]
  simp only [DynCircuitExt.count_sequenceList, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, substActiveSingleCat_count_TOFF]
  refine ⟨by rw [prep.hToffPrep, sel.hToffCtrl, prep.hToffPrepInv]; rfl, ?_⟩
  exact (Nat.add_le_add hp1 (Nat.add_le_add hPk (Nat.add_le_add hs
    (Nat.add_le_add hUnpk (Nat.add_le_add hp2 (le_refl 0)))))).trans (by omega)

open Classical in
theorem uCatRawBEExtHk_mul_E_segExt {mWork k_idle tSelCtrl tSelCat : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (prep : FullSysPrepareBundle 80) (sel :
    HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (c : Configuration) (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) : (uCatRawBEExtHk prep sel c).1 *
    E_segExt k_idle hk = E_segExt k_idle hk *
    (rAct0.embedUnitary (uCatRawBESingleCat prep selImpl c)).1 := by
  have hP1 := (rBEFull_comm_E_ctrl3Ext_and_segExt k_idle hk (prep.uPrep c) hPrepLow hPrepCtrl3).2
  have hP2 := (rBEFull_comm_E_ctrl3Ext_and_segExt k_idle hk (prep.uPrep c)⁻¹
    (PreservesFeature.unitary_inv hPrepLow) (PreservesFeature.unitary_inv hPrepCtrl3)).2
  unfold uCatRawBEExtHk uCatRawBESingleCat
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact comm_op_mul hP2 (comm_op_mul (sel.hSelCatE c) hP1)

open Classical in
theorem uCtrlRawBEExtHk_mul_E_segExt {mWork k_idle tSelCtrl tSelCat : ℕ} {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (prep : FullSysPrepareBundle 80) (sel :
    HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (c : Configuration) (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) : (uCtrlRawBEExtHk prep sel c).1 *
    E_segExt k_idle hk = E_segExt k_idle hk *
    (rAct0.embedUnitary (uCtrlRawBESingleCat prep selImpl c)).1 := by
  have hP1 := (rBEFull_comm_E_ctrl3Ext_and_segExt k_idle hk (prep.uPrep c) hPrepLow hPrepCtrl3).1
  have hP2 := (rBEFull_comm_E_ctrl3Ext_and_segExt k_idle hk (prep.uPrep c)⁻¹
    (PreservesFeature.unitary_inv hPrepLow) (PreservesFeature.unitary_inv hPrepCtrl3)).1
  have hCtrl3 : (uCtrlRawBEExtHk prep sel c).1 * E_ctrl3Ext k_idle hk =
      E_ctrl3Ext k_idle hk * (rAct0.embedUnitary (uCtrlRawBESingleCat prep selImpl c)).1 := by
    unfold uCtrlRawBEExtHk uCtrlRawBESingleCat
    simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
    exact comm_op_mul hP2 (comm_op_mul (cSlackUnpark_comm_E_ctrl3Ext k_idle hk) (comm_op_mul
      (sel.hSelCtrlE c) (comm_op_mul (cSlackPark_comm_E_ctrl3Ext k_idle hk) hP1)))
  have hSlk : (rAct0.embedUnitary (uCtrlRawBESingleCat prep selImpl c)).1 * pSlack3Zero =
      pSlack3Zero * (rAct0.embedUnitary (uCtrlRawBESingleCat prep selImpl c)).1 := by
    have hEmb : rAct0.embedMatrix pSlack3ZeroOrig = pSlack3Zero :=
      (QRegister.embedMatrix_compose rAct0 rSlack3Orig (compProj 0)).symm
    rw [← hEmb, QRegister.embedUnitary_val, ← rAct0.embedMatrix_mul, ← rAct0.embedMatrix_mul]
    exact congrArg rAct0.embedMatrix
      (uCtrlRawBESingleCat_comm_pSlack3ZeroOrig prep selImpl c (sel.hSelSlack010 c))
  rw [E_segExt_eq_E_ctrl3Ext_mul_pSlack3, ← Matrix.mul_assoc, hCtrl3, Matrix.mul_assoc,
    hSlk, ← Matrix.mul_assoc]

open Classical in
theorem embedIntertwine2 {mWork n : ℕ} {rAct : QRegister kFull80 n}
    {rWork : QRegister mWork n} (hDisj : rAct.DisjointWires rWork) {U : Unitary (2 ^ kFull80)}
    {E₁ E₂ V : Operator (2 ^ kFull80)} (h : U.1 * E₁ = E₂ * V) : (rAct.embedUnitary U).1 *
    (rAct.embedMatrix E₁ * rWork.basisOutcomeProjector 0) =
    (rAct.embedMatrix E₂ * rWork.basisOutcomeProjector 0) * rAct.embedMatrix V := by
  rw [QRegister.embedUnitary_val, ← Matrix.mul_assoc, ← rAct.embedMatrix_mul, h,
    rAct.embedMatrix_mul, Matrix.mul_assoc,
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hDisj V 0,
    ← Matrix.mul_assoc]

open Classical in
theorem catRawBEExtHkDyn_realizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWork k_idle tSelCtrl tSelCat n : ℕ} [NeZero (2 ^ n)] {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (prep : FullSysPrepareBundle 80) (sel :
    HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl tSelCat qft selOra selImpl)
    (hmPrep : prep.mWorkPrep ≤ mWork) (c : Configuration)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : RealizesOnProj
    (pHoistExtOn k_idle hk rAct rWork) (rAct.embedUnitary (uCatRawBEExtHk prep sel c))
    (catRawBEExtHkDyn prep sel hmPrep c v rAct rWork hDisj) := by
  let rBE := (rAct.compose rAct0).compose rBEOrig
  let rWP := rWork.compose (QRegister.block 0 prep.mWorkPrep (fullSys_zero_add_le_of_le hmPrep))
  let hBE_WP : rBE.DisjointWires rWP := ((hDisj.compose_left rAct0).compose_left _).compose_right _
  have eBE : rBE = rAct.compose (rAct0.compose rBEOrig) := rfl
  have hP1 := (rBEFull_comm_E_ctrl3Ext_and_segExt k_idle hk (prep.uPrep c) hPrepLow hPrepCtrl3).2
  have hP2 := (rBEFull_comm_E_ctrl3Ext_and_segExt k_idle hk (prep.uPrep c)⁻¹
    (PreservesFeature.unitary_inv hPrepLow) (PreservesFeature.unitary_inv hPrepCtrl3)).2
  have p1 := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    (widenActive_of_eq eBE (prep.hRealPrep c v rBE rWP hBE_WP).widenWorkspace)
  have p2 := sel.hRealCat c v rAct rWork hDisj
  have p3 := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    (widenActive_of_eq eBE (prep.hRealPrepInv c v rBE rWP hBE_WP).widenWorkspace)
  have hChain := p1.seq_intertwine (embedIntertwine2 hDisj hP1) (p2.seq_intertwine
      (embedIntertwine2 hDisj (sel.hSelCatE c)) (p3.seq_intertwine (embedIntertwine2 hDisj
      hP2) (RealizesOnProj.identity (pHoistExtOn k_idle hk rAct rWork))))
  rw [catRawBEExtHkDyn, vepLockVal_eq]
  simpa only [pHoistExtOn, uCatRawBEExtHk, DynCircuitExt.sequenceList_cons,
    DynCircuitExt.sequenceList_nil, QRegister.embedUnitary_mul, one_mul, mul_assoc] using hChain

open Classical in
theorem ctrlRawBEExtHkDyn_realizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWork k_idle tSelCtrl tSelCat n : ℕ} [NeZero (2 ^ n)] {hk : k_idle ≤ 48}
    {qft : FullSysQft654Bundle} {selOra : FullSysSelectOracleBundle 80 48}
    {selImpl : SingleCatSelectImpl 80 48 qft selOra} (hm1 : 1 ≤ mWork)
    (prep : FullSysPrepareBundle 80) (sel : HoistedExtHkSelectSpec mWork k_idle hk tSelCtrl
    tSelCat qft selOra selImpl) (hmPrep : prep.mWorkPrep ≤ mWork) (c : Configuration)
    (hPrepLow : FixesLow3924 h3924_be (prep.uPrep c).1)
    (hPrepCtrl3 : FixesCtrl3 h3954_be (prep.uPrep c).1) (v : Var) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : RealizesOnProj
    (pHoistExtOn k_idle hk rAct rWork) (rAct.embedUnitary (uCtrlRawBEExtHk prep sel c))
    (ctrlRawBEExtHkDyn hm1 prep sel hmPrep c v rAct rWork hDisj) := by
  let rAct170 := rAct.compose rAct0
  let rBE := rAct170.compose rBEOrig
  let rWP := rWork.compose (QRegister.block 0 prep.mWorkPrep (fullSys_zero_add_le_of_le hmPrep))
  let hBE_WP : rBE.DisjointWires rWP := ((hDisj.compose_left rAct0).compose_left _).compose_right _
  have eBE : rBE = rAct.compose (rAct0.compose rBEOrig) := rfl
  have hP1_seg :=
    (rBEFull_comm_E_ctrl3Ext_and_segExt k_idle hk (prep.uPrep c) hPrepLow hPrepCtrl3).2
  have hP2_ctrl := (rBEFull_comm_E_ctrl3Ext_and_segExt k_idle hk (prep.uPrep c)⁻¹
    (PreservesFeature.unitary_inv hPrepLow) (PreservesFeature.unitary_inv hPrepCtrl3)).1
  have hPk_bridge : (rAct0.embedUnitary (cSlackParkSingleCat 80 48 40).eval).1 *
    E_segExt k_idle hk =
      E_ctrl3Ext k_idle hk *
        ((rAct0.embedUnitary (cSlackParkSingleCat 80 48 40).eval).1 * pSlack3Zero) := by
    rw [E_segExt_eq_E_ctrl3Ext_mul_pSlack3, ← Matrix.mul_assoc,
      cSlackPark_comm_E_ctrl3Ext k_idle hk, Matrix.mul_assoc]
  have p1 := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    (widenActive_of_eq eBE (prep.hRealPrep c v rBE rWP hBE_WP).widenWorkspace)
  have p2 := RealizesOnProj.of_clean_embed hDisj (E_segExt k_idle hk)
    ((realizesCleanWorkspace_substActiveSingleCat hm1 v rAct170 rWork
      (hDisj.compose_left rAct0) (cSlackParkSingleCat 80 48 40)).widenActive)
  have p3 := sel.hRealCtrl c v rAct rWork hDisj
  have p4 := RealizesOnProj.of_clean_embed hDisj (E_ctrl3Ext k_idle hk)
    ((realizesCleanWorkspace_substActiveSingleCat hm1 v rAct170 rWork
      (hDisj.compose_left rAct0) (cSlackUnparkSingleCat 80 48 40)).widenActive)
  have p5 := RealizesOnProj.of_clean_embed hDisj (E_ctrl3Ext k_idle hk)
    (widenActive_of_eq eBE (prep.hRealPrepInv c v rBE rWP hBE_WP).widenWorkspace)
  have hChain := p1.seq_intertwine (embedIntertwine2 hDisj hP1_seg) (p2.seq_intertwine
      (embedIntertwine2 hDisj hPk_bridge) (p3.seq_intertwine (embedIntertwine2 hDisj
      (sel.hSelCtrlE c)) (p4.seq_intertwine (embedIntertwine2 hDisj
      (cSlackUnpark_comm_E_ctrl3Ext k_idle hk)) (p5.seq_intertwine (embedIntertwine2 hDisj
      hP2_ctrl) (RealizesOnProj.identity (pCtrl3ExtOn k_idle hk rAct rWork))))))
  rw [ctrlRawBEExtHkDyn, vepLockVal_eq]
  simpa only [pHoistExtOn, uCtrlRawBEExtHk, DynCircuitExt.sequenceList_cons,
    DynCircuitExt.sequenceList_nil, QRegister.embedUnitary_mul, one_mul, mul_assoc] using hChain

/- ## Section 5: Asymmetric `Ext48` + `H^{⊗ k_idle}` 2-Angle Segment & Top Schedule Closure -/

attribute [local irreducible] catRawBEExtHkDyn ctrlRawBEExtHkDyn

open InterWalkRSum42Hoist (fixesLow3924_single_qSig)

open Classical in
theorem qSig_single_comm_E_segExt (k_idle : ℕ) (hk : k_idle ≤ 48) (g : PrimitiveGate 1) :
    (rAct0.embedUnitary (Circuit.single g (qSigInSingleCat 80 48 40)).eval).1 * E_segExt
    k_idle hk = E_segExt k_idle hk * (rAct0.embedUnitary (Circuit.single g (qSigInSingleCat 80
    48 40)).eval).1 := by
  let w := qSigInSingleCat 80 48 40
  have hw : w.val = 4034 := by decide
  have hS := embedAct0_fixesLow3924_comm_E_stream42 (fixesLow3924_single_qSig g)
  have hEmb : (rAct0.embedUnitary (Circuit.single g w).eval).1 =
      (rAct0.compose (QRegister.singleton w)).embedMatrix (PrimitiveGate.eval g).1 := by
    rw [Circuit.eval_single, ← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
  have hC : (rAct0.embedUnitary (Circuit.single g w).eval).1 * pCtrl3Zero =
      pCtrl3Zero * (rAct0.embedUnitary (Circuit.single g w).eval).1 := by
    rw [hEmb]
    refine (CommutesWithReg.of_disjoint (disjointWires_compose_of_disjoint rAct0
      (disj_of_val_ne fun i t ↦ ?_)) _).comm_basisOutcomeProjector 0
    fin_cases i; rw [QRegister.singleton_apply, rUnusedCtrl3Orig_val_eq, hw]
    have := t.isLt; omega
  have hSlk : (rAct0.embedUnitary (Circuit.single g w).eval).1 * pSlack3Zero =
      pSlack3Zero * (rAct0.embedUnitary (Circuit.single g w).eval).1 := by
    rw [hEmb]
    refine (CommutesWithReg.of_disjoint (disjointWires_compose_of_disjoint rAct0
      (disj_of_val_ne fun i t ↦ ?_)) _).comm_basisOutcomeProjector 0
    fin_cases i; rw [QRegister.singleton_apply, rSlack3Orig_val_eq, hw]
    have := t.isLt; omega
  have hI : (rAct0.embedUnitary (Circuit.single g w).eval).1 * pPGIdleZero k_idle hk =
      pPGIdleZero k_idle hk * (rAct0.embedUnitary (Circuit.single g w).eval).1 := by
    rw [hEmb]
    refine (CommutesWithReg.of_disjoint (disjointWires_compose_of_disjoint rAct0
      (disj_of_val_ne fun i q ↦ ?_)) _).comm_basisOutcomeProjector 0
    fin_cases i; rw [QRegister.singleton_apply, rPGIdleOrig_val_eq, hw]
    have := q.isLt; omega
  unfold E_segExt
  rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hS, Matrix.mul_assoc E_stream42, hC,
    ← Matrix.mul_assoc E_stream42, Matrix.mul_assoc (E_stream42 * pCtrl3Zero), hSlk,
    ← Matrix.mul_assoc (E_stream42 * pCtrl3Zero),
    Matrix.mul_assoc (E_stream42 * pCtrl3Zero * pSlack3Zero), hI]
  dsimp only [w]
  simp only [Matrix.mul_assoc]

open Classical in
theorem qSig_diagSeqX_comm_E_segExt (k_idle : ℕ) (hk : k_idle ≤ 48) : (rAct0.embedUnitary
    (((diagNegIPosICircuit (qSigInSingleCat 80 48 40)).seq (Circuit.X (qSigInSingleCat 80 48
    40))).eval)).1 * E_segExt k_idle hk = E_segExt k_idle hk * (rAct0.embedUnitary
    (((diagNegIPosICircuit (qSigInSingleCat 80 48 40)).seq (Circuit.X (qSigInSingleCat 80 48
    40))).eval)).1 := by
  unfold diagNegIPosICircuit Circuit.X Circuit.S Circuit.Z
  simp only [Circuit.eval_seq, QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact comm_op_mul (qSig_single_comm_E_segExt k_idle hk .X) (comm_op_mul
    (qSig_single_comm_E_segExt k_idle hk .S) (comm_op_mul (comm_op_mul
    (qSig_single_comm_E_segExt k_idle hk .X) (comm_op_mul (qSig_single_comm_E_segExt k_idle hk
    .Z) (qSig_single_comm_E_segExt k_idle hk .S))) (qSig_single_comm_E_segExt k_idle hk .X)))

def revStepAllAvoidPG48Bool {n : ℕ} : RevStep n → Bool
  | .x q => decide (q.val < 4035 ∨ 4083 ≤ q.val)
  | .cnot c t => decide ((c.val < 4035 ∨ 4083 ≤ c.val) ∧ (t.val < 4035 ∨ 4083 ≤ t.val))
  | .toff c₁ c₂ t => decide ((c₁.val < 4035 ∨ 4083 ≤ c₁.val) ∧
      (c₂.val < 4035 ∨ 4083 ≤ c₂.val) ∧ (t.val < 4035 ∨ 4083 ≤ t.val))

theorem slackParkSteps80_allAvoidPG48 :
    ∀ s ∈ slackParkStepsSingleCat 80 48 40, revStepAllAvoidPG48Bool s = true := by
  decide

open Classical in
theorem revStep_toCircuit_commutesWithReg_rPGIdleOrig (k_idle : ℕ) (hk : k_idle ≤ 48)
    {s : RevStep kActOrig} (hs : revStepAllAvoidPG48Bool s = true) : CommutesWithReg
    (rPGIdleOrig k_idle hk) s.toCircuit.eval.1 := by
  cases s with
  | x q =>
      have hq := of_decide_eq_true hs
      dsimp only [RevStep.toCircuit]
      rw [Circuit.X, Circuit.eval_single, QRegister.embedUnitary_val]
      refine CommutesWithReg.of_disjoint (disj_of_val_ne fun i idx ↦ ?_) _
      fin_cases i; rw [QRegister.singleton_apply, rPGIdleOrig_val_eq]
      have := idx.isLt; omega
  | cnot c t =>
      have hct := of_decide_eq_true hs
      dsimp only [RevStep.toCircuit]
      split_ifs with hne
      · rw [Circuit.CNOT, Circuit.eval_gate, QRegister.embedUnitary_val]
        refine CommutesWithReg.of_disjoint (disj_of_val_ne fun i idx ↦ ?_) _
        rw [rPGIdleOrig_val_eq]; have := idx.isLt
        rcases i with ⟨_ | _ | n, hn⟩
        · rw [show (⟨0, hn⟩ : Fin 2) = 0 from rfl, QRegister.pair_apply_zero]; omega
        · rw [show (⟨1, hn⟩ : Fin 2) = 1 from rfl, QRegister.pair_apply_one]; omega
        · omega
      · rw [Circuit.eval_identity, OneMemClass.coe_one]
        exact CommutesWithReg.one _
  | toff c₁ c₂ t =>
      have hct := of_decide_eq_true hs
      dsimp only [RevStep.toCircuit]
      split_ifs with hne
      · rw [Circuit.TOFF, Circuit.eval_gate, QRegister.embedUnitary_val]
        refine CommutesWithReg.of_disjoint (disj_of_val_ne fun i idx ↦ ?_) _
        rw [rPGIdleOrig_val_eq]; have := idx.isLt
        rcases i with ⟨_ | _ | _ | n, hn⟩
        · rw [show (⟨0, hn⟩ : Fin 3) = 0 from rfl, QRegister.triple_apply_zero]; omega
        · rw [show (⟨1, hn⟩ : Fin 3) = 1 from rfl, QRegister.triple_apply_one]; omega
        · rw [show (⟨2, hn⟩ : Fin 3) = 2 from rfl, QRegister.triple_apply_two]; omega
        · omega
      · rw [Circuit.eval_identity, OneMemClass.coe_one]
        exact CommutesWithReg.one _

theorem compileRevList_commutesWithReg_rPGIdleOrig
    (k_idle : ℕ) (hk : k_idle ≤ 48) :
    ∀ (ss : List (RevStep kActOrig)),
      (∀ s ∈ ss, revStepAllAvoidPG48Bool s = true) →
      CommutesWithReg (rPGIdleOrig k_idle hk) (compileRevList ss).eval.1
  | [], _ => by
      rw [compileRevList, Circuit.eval_identity, OneMemClass.coe_one]
      exact CommutesWithReg.one _
  | s :: ss, hss => by
      rw [compileRevList, Circuit.eval_seq, Submonoid.coe_mul]
      exact (compileRevList_commutesWithReg_rPGIdleOrig k_idle hk ss
        (fun s' hs' ↦ hss s' (List.mem_cons_of_mem s hs'))).mul
        (revStep_toCircuit_commutesWithReg_rPGIdleOrig k_idle hk (hss s List.mem_cons_self))

theorem uHadIdleOrig_comm_of_commutesWithReg_rPGIdleOrig (k_idle : ℕ) (hk : k_idle ≤ 48)
    {M : Operator (2 ^ kActOrig)} (hM : CommutesWithReg (rPGIdleOrig k_idle hk) M) : M *
    (uHadIdleOrig k_idle hk).1 = (uHadIdleOrig k_idle hk).1 * M := by
  have hEach : ∀ q : Fin k_idle,
      M * (Circuit.onRegister rPG48Orig (Circuit.H ⟨q.val, by omega⟩)).eval.1 =
        (Circuit.onRegister rPG48Orig (Circuit.H ⟨q.val, by omega⟩)).eval.1 * M := fun q ↦ by
    have hSub : rPG48Orig.compose (QRegister.singleton ⟨q.val, by omega⟩) =
        (rPGIdleOrig k_idle hk).compose (QRegister.singleton q) := by
      apply qreg_ext; intro j; fin_cases j
      change rPG48Orig ⟨q.val, _⟩ = rPGIdleOrig k_idle hk q
      simp only [rPGIdleOrig, QRegister.slice_apply, zero_add]
    rw [Circuit.eval_onRegister, Circuit.H, Circuit.eval_single, ← QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val, hSub, QRegister.embedMatrix_compose]
    exact hM _
  have hSeq : ∀ cs : List (Circuit 48), (∀ c ∈ cs, M * (Circuit.onRegister rPG48Orig c).eval.1
      = (Circuit.onRegister rPG48Orig c).eval.1 * M) → M *
      (Circuit.onRegister rPG48Orig (Circuit.sequence cs)).eval.1 =
      (Circuit.onRegister rPG48Orig (Circuit.sequence cs)).eval.1 * M := by
    intro cs
    induction cs with
    | nil =>
        intro _
        dsimp only [Circuit.sequence]
        rw [Circuit.onRegister_identity, Circuit.eval_identity, OneMemClass.coe_one,
          Matrix.mul_one, Matrix.one_mul]
    | cons c cs ih =>
        intro hcs
        dsimp only [Circuit.sequence]
        rw [Circuit.onRegister_seq, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc,
          ih (fun c' hc' ↦ hcs c' (List.mem_cons_of_mem c hc')),
          Matrix.mul_assoc, hcs c List.mem_cons_self, ← Matrix.mul_assoc]
  unfold uHadIdleOrig cHadIdleOrig cHadIdle48
  refine hSeq _ fun c hc ↦ ?_
  rw [List.mem_ofFn] at hc
  obtain ⟨q, rfl⟩ := hc
  exact hEach q

theorem unitary_mul_proj_eq_of_eq_proj_mul {d : ℕ} (W V : Unitary d) (P : Operator d)
    (hPH : Pᴴ = P) (hP2 : P * P = P) (h : W.1 * P = P * V.1) : W.1 * P = V.1 * P := by
  have hWHW : W.1ᴴ * W.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (show (W⁻¹ * W).1 = 1 by rw [inv_mul_cancel, OneMemClass.coe_one])
  have hVVH : V.1 * V.1ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (show (V * V⁻¹).1 = 1 by rw [mul_inv_cancel, OneMemClass.coe_one])
  have hAdj : P * W.1ᴴ = V.1ᴴ * P := by
    have h0 := congrArg Matrix.conjTranspose h
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPH] at h0
  have hVHP : V.1ᴴ * (P * V.1) = P := by
    calc V.1ᴴ * (P * V.1)
      _ = V.1ᴴ * ((P * P) * V.1) := by rw [hP2]
      _ = (V.1ᴴ * P) * (P * V.1) := by simp only [Matrix.mul_assoc]
      _ = (P * W.1ᴴ) * (W.1 * P) := by rw [← hAdj, ← h]
      _ = P * ((W.1ᴴ * W.1) * P) := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hWHW, Matrix.one_mul, hP2]
  have hPV : P * V.1 = V.1 * P := by
    calc P * V.1
      _ = 1 * (P * V.1) := (Matrix.one_mul _).symm
      _ = (V.1 * V.1ᴴ) * (P * V.1) := by rw [hVVH]
      _ = V.1 * (V.1ᴴ * (P * V.1)) := by rw [Matrix.mul_assoc]
      _ = V.1 * P := by rw [hVHP]
  rw [h, hPV]

open SpecsAux.PhaseGradCatalystCore (basisOutcomeProjector_zero_compose_mul)
open PolymorphicTopClosure (approximatesTimeEvolution_embed_block0)
open InterWalkRSum42Hoist (proj_absorb_comm_lemma)

theorem rExt48IdleFull_val_ge_sys (k_idle : ℕ) (hk : k_idle ≤ 48)
    (idx : Fin (42 + (6 + k_idle))) : systemQubits ≤ (rExt48IdleFull k_idle hk idx).val := by
  have hsys : systemQubits = 3948 := rfl
  rw [hsys]
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) idx
  · rw [rExt48IdleFull, QRegister.concat_apply_left]
    dsimp [rSum0, qreg_block_apply, kActOrig, mActOrig, kActSingleCatClosure,
      mActSingleCatClosure, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega
  · rw [rExt48IdleFull, QRegister.concat_apply_right]
    refine Fin.addCases (fun c ↦ ?_) (fun q ↦ ?_) b
    · rw [rExt6IdleFull, QRegister.concat_apply_left]
      refine Fin.addCases (m := 3) (n := 3) (fun t1 ↦ ?_) (fun t2 ↦ ?_) c
      · rw [rExt6Full, QRegister.concat_apply_left, rUnusedCtrl3Full_val_eq]; omega
      · rw [rExt6Full, QRegister.concat_apply_right, rSlack3Full_val_eq]; omega
    · rw [rExt6IdleFull, QRegister.concat_apply_right, rPGIdle_val_eq]; omega

/-- Ancilla-local `(42 + (6 + k_idle))`-wire slice inside `mActHoist` corresponding to
  `rExt48IdleFull`. -/
def rExt48InAnc (k_idle : ℕ) (hk : k_idle ≤ 48) :
    QRegister (42 + (6 + k_idle)) mActHoist where
  wires :=
    ⟨fun idx ↦ ⟨(rExt48IdleFull k_idle hk idx).val - systemQubits, by
      have hge := rExt48IdleFull_val_ge_sys k_idle hk idx
      have hlt := (rExt48IdleFull k_idle hk idx).isLt
      have hkFull : kFull80 = systemQubits + mActHoist := rfl
      omega⟩,
     fun i j hij ↦ (rExt48IdleFull k_idle hk).wires.injective (Fin.ext (by
      have hv := congrArg Fin.val hij
      have hi := rExt48IdleFull_val_ge_sys k_idle hk i
      have hj := rExt48IdleFull_val_ge_sys k_idle hk j
      dsimp only at hv; omega))⟩

theorem pZeroExtOn_absorb_concat_anc {mWork k_idle n : ℕ} (hk : k_idle ≤ 48)
    {rSys : QRegister systemQubits n} {rActAnc : QRegister mActHoist n}
    {rWork : QRegister mWork n} (hSysAct : rSys.DisjointWires rActAnc)
    (hSubWork : rActAnc.DisjointWires rWork) : pZeroExtOn k_idle hk
    (rSys.concat rActAnc hSysAct) rWork *
    (rActAnc.concat rWork hSubWork).basisOutcomeProjector 0 =
    (rActAnc.concat rWork hSubWork).basisOutcomeProjector 0 := by
  let rAct : QRegister kFull80 n := rSys.concat rActAnc hSysAct
  let rAnc' : QRegister (mActHoist + mWork) n := rActAnc.concat rWork hSubWork
  let extInConcat : QRegister (42 + (6 + k_idle)) (mActHoist + mWork) := (QRegister.block 0
      mActHoist (fullSys_zero_add_le mActHoist mWork)).compose (rExt48InAnc k_idle hk)
  let workInConcat : QRegister mWork (mActHoist + mWork) :=
    QRegister.block mActHoist mWork le_rfl
  have hExtComp : rAct.compose (rExt48IdleFull k_idle hk) = rAnc'.compose extInConcat := by
    apply qreg_ext; intro i
    have hi1 : rExt48IdleFull k_idle hk i = Fin.natAdd systemQubits (rExt48InAnc k_idle hk i) := by
      apply Fin.ext
      have hge := rExt48IdleFull_val_ge_sys k_idle hk i
      simp only [Fin.val_natAdd, rExt48InAnc]
      change _ = systemQubits + ((rExt48IdleFull k_idle hk i).val - systemQubits)
      omega
    have hi2 : extInConcat i = Fin.castAdd mWork (rExt48InAnc k_idle hk i) := by
      ext; simp [extInConcat]
    simp only [QRegister.compose_apply, hi1, hi2, rAct, rAnc',
      QRegister.concat_apply_right, QRegister.concat_apply_left]
  have hWorkComp : rWork = rAnc'.compose workInConcat := by
    apply qreg_ext; intro j
    have hj : workInConcat j = Fin.natAdd mActHoist j := by ext; simp [workInConcat]
    simp only [QRegister.compose_apply, hj, rAnc', QRegister.concat_apply_right]
  have hExtProj : rAct.embedMatrix (pZeroInitExt k_idle hk) =
      (rAnc'.compose extInConcat).basisOutcomeProjector 0 := by
    dsimp only [pZeroInitExt]
    rw [← hExtComp, QRegister.basisOutcomeProjector, QRegister.basisOutcomeProjector]
    exact (QRegister.embedMatrix_compose rAct (rExt48IdleFull k_idle hk) (compProj 0)).symm
  change (rAct.embedMatrix (pZeroInitExt k_idle hk) * rWork.basisOutcomeProjector 0) *
      rAnc'.basisOutcomeProjector 0 = rAnc'.basisOutcomeProjector 0
  rw [hExtProj, Matrix.mul_assoc]
  rw [show rWork.basisOutcomeProjector 0 * rAnc'.basisOutcomeProjector 0 =
        (rAnc'.compose workInConcat).basisOutcomeProjector 0 * rAnc'.basisOutcomeProjector 0 by
      rw [← hWorkComp]]
  rw [basisOutcomeProjector_zero_compose_mul rAnc' workInConcat,
    basisOutcomeProjector_zero_compose_mul rAnc' extInConcat]

open Classical in
theorem approximatesTimeEvolution_of_mul_pZeroInitExt_eq
    {k_idle : ℕ} (hk : k_idle ≤ 48)
    {H P : Operator (2 ^ systemQubits)} {t ε : ℝ}
    {W : Unitary (2 ^ kFull80)} {W₀ : Unitary (2 ^ kActOrig)}
    (hEq : W.1 * pZeroInitExt k_idle hk = (rAct0.embedUnitary W₀).1 * pZeroInitExt k_idle hk)
    (h₀ : ApproximatesTimeEvolution (m := mActOrig) H t ε P W₀) :
    ApproximatesTimeEvolution (m := mActHoist) H t ε P W := by
  have hEmb : ApproximatesTimeEvolution (m := mActHoist) H t ε P (rAct0.embedUnitary W₀) :=
    approximatesTimeEvolution_embed_block0
      (k := systemQubits) (m₀ := mActOrig) (m := mActHoist)
      rAct0 (QRegister.block 0 mActOrig (by decide))
      (by apply qreg_ext; intro i; ext; simp [rAct0])
      (by apply qreg_ext; intro i; ext; simp [rAct0])
      h₀
  rcases hEmb with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  let sys : QRegister systemQubits kFull80 :=
    QRegister.block 0 systemQubits (fullSys_zero_add_le systemQubits mActHoist)
  let anc : QRegister mActHoist kFull80 := QRegister.block systemQubits mActHoist le_rfl
  have hExtAnc : anc.compose (rExt48InAnc k_idle hk) = rExt48IdleFull k_idle hk := by
    apply qreg_ext; intro i; apply Fin.ext
    have hge := rExt48IdleFull_val_ge_sys k_idle hk i
    dsimp [anc, rExt48InAnc, qreg_block_apply]
    omega
  have hAbs : pZeroInitExt k_idle hk * anc.basisOutcomeProjector 0 =
      anc.basisOutcomeProjector 0 := by
    unfold pZeroInitExt
    rw [← hExtAnc]
    exact basisOutcomeProjector_zero_compose_mul anc (rExt48InAnc k_idle hk)
  have hSysDisj : sys.DisjointWires (rExt48IdleFull k_idle hk) :=
    disj_of_val_ne fun i j ↦ by
      have hi : (sys i).val = i.val := by simp [sys]
      have hge := rExt48IdleFull_val_ge_sys k_idle hk j
      have := i.isLt; rw [hi]; omega
  have hCommSys : sys.embedMatrix P * pZeroInitExt k_idle hk =
      pZeroInitExt k_idle hk * sys.embedMatrix P :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint sys) (rExt48IdleFull k_idle hk)
      hSysDisj P 0
  have hW_eq : W.1 * (sys.embedMatrix P * anc.basisOutcomeProjector 0) =
      (rAct0.embedUnitary W₀).1 * (sys.embedMatrix P * anc.basisOutcomeProjector 0) :=
      proj_absorb_comm_lemma W.1 (rAct0.embedUnitary W₀).1 (sys.embedMatrix P)
      (anc.basisOutcomeProjector 0) (pZeroInitExt k_idle hk) hEq hAbs hCommSys
  let E_exp : Operator (2 ^ systemQubits) := NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)
  change ‖(W.1 - Complex.exp (φ * Complex.I) • sys.embedMatrix E_exp) *
    (sys.embedMatrix P * anc.basisOutcomeProjector 0)‖ ≤ ε
  change ‖((rAct0.embedUnitary W₀).1 - Complex.exp (φ * Complex.I) • sys.embedMatrix E_exp) *
    (sys.embedMatrix P * anc.basisOutcomeProjector 0)‖ ≤ ε at hφ
  rw [sub_mul, hW_eq, ← sub_mul]
  exact hφ

set_option maxRecDepth 512
set_option exponentiation.threshold 256

end ConfigLeaf4Ext48TopStitch
end Leaf4Ext48TopStitch
end
set_option exponentiation.threshold 256
end Leaf4Ext48TopStitch

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
