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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WeightedCsa3Gen

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

namespace MomSlot1Dyadic459Sub36w
section ConfigMomSlot1Dyadic459Sub36w
local instance (priority := 1000000) instNeZeroTwoPow_MomSlot1Dyadic459Sub36w (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux.SpecMirror SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open PosMomSelectSandwich FullSysPrepare6Slot
open PosMomSelectDynamic (unitaryConj)
open SixSlotEndpointJunctionBridge
open TwosCompAndWire0Cancel
open LiteralKineticAndMidpoint128
open MomSlot1GeomPriority288
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
  (sixChannelRaw sixChannelShifted)
open MomSlots01Slot1ProjKinetic
open InPlaceFullAddSlice (bit_cases)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
def toggleListOn {M : ℕ} (cur : ℕ) (wThr : Wire M) (hw : wThr.val < cur) :
    List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr }) → SsaProg M cur cur
  | [] => .done cur
  | (en, ⟨w, hlt, hne⟩) :: tl =>
      if en then .cnot w wThr hne hlt hw (toggleListOn cur wThr hw tl)
      else toggleListOn cur wThr hw tl
def thrXorSum {M : ℕ} (cur : ℕ) (wThr : Wire M) (β : BitAssignment M) :
    List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr }) → ZMod 2
  | [] => 0
  | (en, sw) :: tl => (if en then β sw.1 else 0) + thrXorSum cur wThr β tl
theorem thrXorSum_update_self {M : ℕ} (cur : ℕ) (wThr : Wire M) (β : BitAssignment M) (v : ZMod 2) :
    ∀ ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr }),
      thrXorSum cur wThr (Function.update β wThr v) ls = thrXorSum cur wThr β ls
  | [] => rfl
  | (_, ⟨_, _, hne⟩) :: tl => by
      simpa only [thrXorSum, Function.update_of_ne hne] using
        congrArg (_ + ·) (thrXorSum_update_self cur wThr β v tl)
theorem toggleListOn_eval {M : ℕ} (cur : ℕ) (wThr : Wire M) (hw : wThr.val < cur) :
    ∀ (ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr })) (β : BitAssignment M),
      (toggleListOn cur wThr hw ls).eval β =
        Function.update β wThr (β wThr + thrXorSum cur wThr β ls)
  | [], β => by simp [toggleListOn, thrXorSum]
  | (en, ⟨w, hlt, hne⟩) :: tl, β => by
      dsimp only [toggleListOn, thrXorSum]
      by_cases hen : en
      · simp only [hen, ↓reduceIte, SsaProg.eval_cnot, toggleListOn_eval cur wThr hw tl,
          thrXorSum_update_self, Function.update_idem, Function.update_self, add_assoc]
      · simpa only [hen, Bool.false_eq_true, ↓reduceIte, zero_add] using
          toggleListOn_eval cur wThr hw tl β
def toggleThrWire {M : ℕ} (cur : ℕ) (wThr : Wire M) (hw : wThr.val < cur) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr })) : SsaProg M cur cur :=
  if c0 then .x wThr hw (toggleListOn cur wThr hw ls) else toggleListOn cur wThr hw ls
theorem toggleThrWire_eval {M : ℕ} (cur : ℕ) (wThr : Wire M) (hw : wThr.val < cur) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur ∧
      w ≠ wThr })) (β : BitAssignment M) : (toggleThrWire cur wThr hw c0 ls).eval β =
      Function.update β wThr
    (β wThr + (b2z c0 + thrXorSum cur wThr β ls)) := by
  dsimp only [toggleThrWire, b2z]
  by_cases hc0 : c0
  · simp only [hc0, ↓reduceIte, SsaProg.eval_x, toggleListOn_eval, thrXorSum_update_self,
      Function.update_idem, Function.update_self, add_assoc]
  · simp only [hc0, Bool.false_eq_true, ↓reduceIte, toggleListOn_eval, zero_add]
def widenTerms {M c₁ c₂ : ℕ} {wThr : Wire M} (hle : c₁ ≤ c₂) :
    List (Bool × { w : Wire M // w.val < c₁ ∧ w ≠ wThr }) →
    List (Bool × { w : Wire M // w.val < c₂ ∧ w ≠ wThr })
  | [] => []
  | (en, ⟨w, hlt, hne⟩) :: tl =>
      (en, ⟨w, lt_of_lt_of_le hlt hle, hne⟩) :: widenTerms hle tl
theorem thrXorSum_widen {M c₁ c₂ : ℕ} {wThr : Wire M} (hle : c₁ ≤ c₂) (β : BitAssignment M) :
    ∀ ls : List (Bool × { w : Wire M // w.val < c₁ ∧ w ≠ wThr }),
      thrXorSum c₂ wThr β (widenTerms hle ls) = thrXorSum c₁ wThr β ls
  | [] => rfl
  | (en, ⟨w, hlt, hne⟩) :: tl => by
      dsimp only [widenTerms, thrXorSum]
      rw [thrXorSum_widen hle β tl]
theorem thrXorSum_congr {M : ℕ} (cur : ℕ) (wThr : Wire M) {β₁ β₂ : BitAssignment M}
    (heq : ∀ w : Wire M, w.val < cur → w ≠ wThr → β₁ w = β₂ w) :
    ∀ ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr }),
      thrXorSum cur wThr β₁ ls = thrXorSum cur wThr β₂ ls
  | [] => rfl
  | (en, ⟨w, hlt, hne⟩) :: tl => by
      dsimp only [thrXorSum]
      rw [heq w hlt hne, thrXorSum_congr cur wThr heq tl]
def qqLtStepInlineThr {M : ℕ} (cur : ℕ) (hcur : cur < M) (wThr u_j prev_lt : Wire M)
    (hut : u_j ≠ wThr) (hpt : prev_lt ≠ wThr) (hpu : prev_lt ≠ u_j) (ht : wThr.val <
      cur) (hu : u_j.val < cur) (hp : prev_lt.val < cur) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr })) : SsaProg M cur (cur + 1) :=
    ((toggleThrWire cur wThr ht c0 ls).append (qqLtStep cur hcur u_j wThr prev_lt hut hpt hpu
    hu ht hp)).append (toggleThrWire (cur + 1) wThr (Nat.lt_succ_of_lt ht) c0 (widenTerms
    (Nat.le_succ cur) ls))
theorem mk_ne_wire {M a : ℕ} {ha : a < M} {w : Wire M} (h : a ≠ w.val) : (⟨a, ha⟩ : Wire M) ≠ w :=
  Fin.ne_of_val_ne h
theorem mk_ne_mk {M a b : ℕ} {ha : a < M} {hb : b < M} (h : a ≠ b) : (⟨a, ha⟩ : Wire M) ≠ ⟨b, hb⟩ :=
  Fin.ne_of_val_ne h
private theorem keep_lt_eq {M lo hi : ℕ} {f : BitAssignment M →
    BitAssignment M} (hf : PreservesOutside lo hi f) {β β' : BitAssignment M} (h : f β = β')
    (w : Wire M) (hw : w.val < lo) : β' w = β w :=
  (congrFun h w).symm.trans (hf.keep_lt β w hw)
private theorem toggleWrap_spec {M : ℕ} (cur : ℕ) (hcur : cur < M) (wThr : Wire M) (ht : wThr.val <
    cur) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr })) (P : SsaProg M cur (cur +
      1)) (hP : PreservesOutside cur (cur + 1) P.eval) :
    PreservesOutside cur (cur +
      1) (((toggleThrWire cur wThr ht c0 ls).append P).append (toggleThrWire (cur +
      1) wThr (Nat.lt_succ_of_lt ht) c0
    (widenTerms (Nat.le_succ cur) ls))).eval ∧ ∀ β : BitAssignment M,
      (((toggleThrWire cur wThr ht c0 ls).append P).append
    (toggleThrWire (cur +
      1) wThr (Nat.lt_succ_of_lt ht) c0 (widenTerms (Nat.le_succ cur) ls))).eval β ⟨cur, hcur⟩ =
    P.eval (Function.update β wThr (β wThr + (b2z c0 + thrXorSum cur wThr β ls))) ⟨cur, hcur⟩ := by
  refine ⟨fun β w hw ↦ ?_, fun β ↦ ?_⟩
  · simp only [SsaProg.append_eval]
    generalize hβ₁ : (toggleThrWire cur wThr ht c0 ls).eval β = β₁
    generalize hβ₂ : P.eval β₁ = β₂
    have h₁ : β₁ = Function.update β wThr (β wThr + (b2z c0 + thrXorSum cur wThr β ls)) :=
      hβ₁.symm.trans (toggleThrWire_eval cur wThr ht c0 ls β)
    rw [toggleThrWire_eval (cur + 1) wThr (Nat.lt_succ_of_lt ht) c0 _ β₂,
      thrXorSum_widen (Nat.le_succ cur) β₂ ls,
      thrXorSum_congr cur wThr (fun u hlt hne_u ↦ by
        rw [keep_lt_eq hP hβ₂ u hlt, h₁, Function.update_of_ne hne_u]) ls,
      show β₂ wThr = β wThr + (b2z c0 + thrXorSum cur wThr β ls) by
        rw [keep_lt_eq hP hβ₂ wThr ht, h₁, Function.update_self]]
    change Function.update β₂ wThr ((β wThr + _) + _) w = β w
    rw [zmod2_add_assoc_cancel]
    by_cases hwt : w = wThr
    · subst hwt
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hwt, ← hβ₂, hP β₁ w hw, h₁, Function.update_of_ne hwt]
  · simp only [SsaProg.append_eval]
    rw [toggleThrWire_eval (cur + 1) wThr (Nat.lt_succ_of_lt ht) c0 _ _,
      Function.update_of_ne (mk_ne_wire (Nat.ne_of_gt ht)), toggleThrWire_eval cur wThr ht c0 ls β]
theorem qqLtStepInlineThr_spec {M : ℕ} (cur : ℕ) (hcur : cur < M)
    (wThr u_j prev_lt : Wire M)
    (hut : u_j ≠ wThr) (hpt : prev_lt ≠ wThr) (hpu : prev_lt ≠ u_j)
    (ht : wThr.val < cur) (hu : u_j.val < cur) (hp : prev_lt.val < cur)
    (c0 : Bool) (ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr })) :
    PreservesOutside cur (cur + 1)
      (qqLtStepInlineThr cur hcur wThr u_j prev_lt hut hpt hpu ht hu hp c0 ls).eval ∧
    ∀ (β : BitAssignment M), β wThr = 0 → β ⟨cur, hcur⟩ = 0 →
      (qqLtStepInlineThr cur hcur wThr u_j prev_lt hut hpt hpu ht hu hp c0 ls).eval β
          ⟨cur, hcur⟩ =
        let thrBit := b2z c0 + thrXorSum cur wThr β ls
        if β u_j = thrBit then β prev_lt else thrBit := by
  obtain ⟨hPres, hEval⟩ := toggleWrap_spec cur hcur wThr ht c0 ls
    (qqLtStep cur hcur u_j wThr prev_lt hut hpt hpu hu ht hp)
    (qqLtStep_preserves cur hcur u_j wThr prev_lt hut hpt hpu hu ht hp)
  refine ⟨by dsimp only [qqLtStepInlineThr]; exact hPres, fun β hzt hzc ↦ ?_⟩
  dsimp only [qqLtStepInlineThr]
  rw [hEval β, qqLtStep_eval cur hcur u_j wThr prev_lt hut hpt hpu hu ht hp _
    (by rw [Function.update_of_ne (mk_ne_wire (Nat.ne_of_gt ht)), hzc]),
    Function.update_self, Function.update_of_ne hut, Function.update_of_ne hpt,
    Function.update_self, hzt, zero_add]
def qqLtBaseInlineThr {M : ℕ} (cur : ℕ) (hcur : cur <
    M) (wThr u0 : Wire M) (hut : u0 ≠ wThr) (ht : wThr.val < cur) (hu : u0.val < cur) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr })) : SsaProg M cur (cur + 1) :=
  ((toggleThrWire cur wThr ht c0 ls).append (andPol cur hcur u0 wThr hut hu ht true
    false)).append (toggleThrWire (cur + 1) wThr (Nat.lt_succ_of_lt ht) c0
      (widenTerms (Nat.le_succ cur) ls))
theorem qqLtBaseInlineThr_spec {M : ℕ} (cur : ℕ) (hcur : cur <
    M) (wThr u0 : Wire M) (hut : u0 ≠ wThr) (ht : wThr.val < cur) (hu : u0.val < cur) (c0 : Bool)
    (ls : List (Bool × { w : Wire M // w.val < cur ∧ w ≠ wThr })) : PreservesOutside cur (cur +
      1) (qqLtBaseInlineThr cur hcur wThr u0 hut ht hu c0 ls).eval ∧
    ∀ (β : BitAssignment M),
      β wThr = 0 → β ⟨cur,
      hcur⟩ = 0 → (qqLtBaseInlineThr cur hcur wThr u0 hut ht hu c0 ls).eval β ⟨cur, hcur⟩ =
    (β u0 + 1) * (b2z c0 + thrXorSum cur wThr β ls) := by
  obtain ⟨hPres, hEval⟩ := toggleWrap_spec cur hcur wThr ht c0 ls
    (andPol cur hcur u0 wThr hut hu ht true false)
    (andPol_preserves cur hcur u0 wThr hut hu ht true false)
  refine ⟨by dsimp only [qqLtBaseInlineThr]; exact hPres, fun β hzt hzc ↦ ?_⟩
  dsimp only [qqLtBaseInlineThr]
  rw [hEval β, andPol_eval cur hcur u0 wThr hut hu ht true false _
    (by rw [Function.update_of_ne (mk_ne_wire (Nat.ne_of_gt ht)), hzc]),
    Function.update_self, Function.update_of_ne hut, Function.update_self, hzt, zero_add]
  simp [b2z]
def twosCarryChainG {M : ℕ} (u8Base cBase : ℕ) (hu : u8Base + 8 ≤ cBase) :
    (k : ℕ) → (hk : k < 6) → (ho : cBase + (k + 1) ≤ M) →
    SsaProg M cBase (cBase + (k + 1))
  | 0, _, ho =>
      andPol cBase (by omega) ⟨u8Base + 7, by omega⟩ ⟨u8Base, by omega⟩
        (Fin.ne_of_val_ne (by dsimp; omega))
        (by dsimp; omega) (by dsimp; omega) false true
  | k + 1, hk, ho =>
      (twosCarryChainG u8Base cBase hu k (by omega) (by omega)).append <|
        andPol (cBase + (k + 1)) (by omega)
          ⟨cBase + k, by omega⟩ ⟨u8Base + (k + 1), by omega⟩
          (Fin.ne_of_val_ne (by dsimp; omega))
          (by dsimp; omega) (by dsimp; omega) false true
@[scoped simp]
theorem twosCarryChainG_countAnd {M : ℕ} (u8Base cBase : ℕ) (hu : u8Base + 8 ≤ cBase) :
    ∀ (k : ℕ) (hk : k < 6) (ho : cBase + (k + 1) ≤ M),
      (twosCarryChainG u8Base cBase hu k hk ho).countAnd = k + 1
  | 0, _, _ => rfl
  | k + 1, hk, ho => by simp [twosCarryChainG, twosCarryChainG_countAnd u8Base cBase hu k]
theorem twosCarryChainG_spec {M : ℕ} (u8Base cBase : ℕ) (hu : u8Base + 8 ≤ cBase) :
    ∀ (k : ℕ) (hk : k < 6) (ho : cBase + (k + 1) ≤ M),
      PreservesOutside cBase (cBase + (k + 1)) (twosCarryChainG u8Base cBase hu k hk ho).eval ∧
      ∀ (β : BitAssignment M), (∀ w : Wire M, cBase ≤ w.val → β w = 0) →
        ∀ (j : ℕ) (_ : j ≤ k),
          (twosCarryChainG u8Base cBase hu k hk ho).eval β ⟨cBase + j, by omega⟩ =
            carryBool (fun b : Fin 8 ↦ β ⟨u8Base + b.val, by omega⟩) (j + 1)
  | 0, _, ho => by
      refine ⟨andPol_preserves _ _ _ _ _ _ _ _ _, fun β hz j hj ↦ ?_⟩
      obtain rfl : j = 0 := by omega
      dsimp only [twosCarryChainG]
      rw [show (⟨cBase + 0, by omega⟩ : Wire M) = ⟨cBase, by omega⟩ from Fin.ext rfl,
        andPol_eval _ _ _ _ _ _ _ _ _ _ (hz _ le_rfl), Function.update_self]
      simp [carryBool, b2z]
  | k + 1, hk, ho => by
      obtain ⟨hPres, ih⟩ := twosCarryChainG_spec (M := M) u8Base cBase hu k (by omega) (by omega)
      refine ⟨fun β w hw ↦ ?_, fun β hz j hj ↦ ?_⟩
      · simp only [twosCarryChainG, SsaProg.append_eval]
        exact PreservesOutside.comp (by omega) (by omega) hPres
          (andPol_preserves (cBase + (k + 1)) _ _ _ _ _ _ _ _) β w hw
      · simp only [twosCarryChainG, SsaProg.append_eval]
        generalize hβ₁ : (twosCarryChainG u8Base cBase hu k (by omega) (by omega)).eval β = β₁
        by_cases hjk : j = k + 1
        · subst hjk
          rw [andPol_eval _ _ _ _ _ _ _ _ _ β₁
            (((congrFun hβ₁ _).symm.trans (hPres β ⟨cBase + (k + 1),
              by omega⟩ (Or.inr le_rfl))).trans
              (hz ⟨_, by omega⟩ (Nat.le_add_right cBase (k + 1)))),
            Function.update_self,
            (congrFun hβ₁ ⟨cBase + k, by omega⟩).symm.trans (ih β hz k le_rfl),
            keep_lt_eq hPres hβ₁ ⟨u8Base + (k + 1), by omega⟩
              (show u8Base + (k + 1) < cBase by omega)]
          simp [carryBool, show k + 1 < 8 by omega, b2z]
        · rw [andPol_preserves _ _ _ _ _ _ _ _ _ β₁ ⟨cBase + j, by omega⟩
            (Or.inl (show cBase + j < cBase + (k + 1) by omega)), ← hβ₁]
          exact ih β hz j (by omega)
def inplaceMag7G {M : ℕ} (u8Base cBase cur : ℕ)
    (hu : u8Base + 8 ≤ cBase) (hc : cBase + 6 ≤ cur) (hcur : cur ≤ M) :
    (k : ℕ) → (hk : k ≤ 6) → SsaProg M cur cur
  | 0, _ => .done cur
  | k + 1, hk =>
      (inplaceMag7G u8Base cBase cur hu hc hcur k (by omega)).append <|
        .cnot ⟨u8Base + 7, by omega⟩ ⟨u8Base + 1 + k, by omega⟩
          (mk_ne_mk (by omega)) (show u8Base + 7 < cur by omega)
          (show u8Base + 1 + k < cur by omega) <|
          .cnot ⟨cBase + k, by omega⟩ ⟨u8Base + 1 + k, by omega⟩
            (mk_ne_mk (by omega)) (show cBase + k < cur by omega)
            (show u8Base + 1 + k < cur by omega) <| .done cur
@[scoped simp] theorem inplaceMag7G_countAnd {M : ℕ} (u8Base cBase cur : ℕ)
    (hu : u8Base + 8 ≤ cBase) (hc : cBase + 6 ≤ cur) (hcur : cur ≤ M) :
    ∀ (k : ℕ) (hk : k ≤ 6), (inplaceMag7G u8Base cBase cur hu hc hcur k hk).countAnd = 0
  | 0, _ => rfl
  | k + 1, hk => by simp [inplaceMag7G, inplaceMag7G_countAnd u8Base cBase cur hu hc hcur k]
theorem inplaceMag7G_spec {M : ℕ} (u8Base cBase cur : ℕ)
    (hu : u8Base + 8 ≤ cBase) (hc : cBase + 6 ≤ cur) (hcur : cur ≤ M) :
    ∀ (k : ℕ) (hk : k ≤ 6) (β : BitAssignment M) (w : Wire M),
      (inplaceMag7G u8Base cBase cur hu hc hcur k hk).eval β w =
        if h : u8Base + 1 ≤ w.val ∧ w.val < u8Base + 1 + k then
          β w + β ⟨u8Base + 7, by omega⟩ + β ⟨cBase + (w.val - (u8Base + 1)), by omega⟩
        else β w
  | 0, _, β, w => by
      dsimp only [inplaceMag7G, SsaProg.eval_done]
      rw [MomSlot1GeomPriority288.dite_neg_s1
        (by omega : ¬(u8Base + 1 ≤ w.val ∧ w.val < u8Base + 1 + 0))]
  | k + 1, hk, β, w => by
      simp only [inplaceMag7G, SsaProg.append_eval, SsaProg.eval_cnot, SsaProg.eval_done]
      have ih := inplaceMag7G_spec u8Base cBase cur hu hc hcur k (by omega) β
      have hout (i : ℕ) (hi : i < M) (ho : ¬(u8Base + 1 ≤ i ∧ i < u8Base + 1 + k)) :
          (inplaceMag7G u8Base cBase cur hu hc hcur k (by omega)).eval β ⟨i, hi⟩ = β ⟨i, hi⟩ := by
        rw [ih ⟨i, hi⟩, MomSlot1GeomPriority288.dite_neg_s1 ho]
      by_cases hwk : w = ⟨u8Base + 1 + k, by omega⟩
      · subst hwk
        have hp : u8Base + 1 ≤ u8Base + 1 + k ∧ u8Base + 1 + k < u8Base + 1 + (k + 1) := by omega
        rw [Function.update_self, Function.update_self, Function.update_of_ne (mk_ne_mk (by omega)),
          hout (u8Base + 1 + k) (by omega) (by omega), hout (u8Base + 7) (by omega) (by omega),
          hout (cBase + k) (by omega) (by omega), MomSlot1GeomPriority288.dite_pos_s1 hp,
          show (⟨cBase + (u8Base + 1 + k - (u8Base + 1)), by omega⟩ : Wire M) = ⟨cBase + k,
            by omega⟩
            from Fin.ext (Nat.add_left_cancel_iff.mpr (Nat.add_sub_cancel_left _ k))]
      · rw [Function.update_of_ne hwk, Function.update_of_ne hwk, ih w]
        have hw_ne : w.val ≠ u8Base + 1 + k := fun heq ↦ hwk (Fin.ext heq)
        split_ifs
        all_goals first | rfl | omega
def prioStarEval (b0 : ZMod 2) (f : ℕ → ZMod 2) : (k : ℕ) → BitAssignment k → ZMod 2
  | 0, _ => b0
  | k + 1, α =>
      if α ⟨k, Nat.lt_succ_self k⟩ = 1 then f k
      else prioStarEval b0 f k (fun i ↦ α ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
def prioChainStar {M : ℕ} (uBase outBase : ℕ) (wBase : Wire M) (wBit : ℕ → Wire M)
    (hwBase : wBase.val < outBase) (hwBit : ∀ t < 30, (wBit t).val < outBase)
    (huOut : uBase + 30 ≤ outBase) (huM : ∀ t < 30, uBase + t ≠ (wBit t).val)
    (hBaseBit0 : wBase ≠ wBit 0) :
    (k : ℕ) → (hk : k < 30) → (ho : outBase + (k + 1) ≤ M) →
    SsaProg M outBase (outBase + (k + 1))
  | 0, _, ho =>
      muxBit outBase (by omega) ⟨uBase, by omega⟩ wBase (wBit 0)
        (mk_ne_wire (huM 0 (by decide))) hBaseBit0
        (show uBase < outBase by omega) hwBase (hwBit 0 (by decide))
  | k + 1, hk, ho =>
      (prioChainStar uBase outBase wBase wBit hwBase hwBit huOut huM hBaseBit0 k
        (by omega) (by omega)).append <|
        muxBit (outBase + (k + 1)) (by omega)
          ⟨uBase + (k + 1), by omega⟩ ⟨outBase + k, by omega⟩ (wBit (k + 1))
          (mk_ne_wire (huM (k + 1) hk))
          (mk_ne_wire (by have := hwBit (k + 1) hk; omega))
          (show uBase + (k + 1) < outBase + (k + 1) by omega)
          (show outBase + k < outBase + (k + 1) by omega) (lt_trans (hwBit (k + 1) hk) (by omega))
@[scoped simp] theorem prioChainStar_countAnd {M : ℕ} (uBase outBase : ℕ)
    (wBase : Wire M) (wBit : ℕ → Wire M) (hwBase : wBase.val < outBase)
    (hwBit : ∀ t < 30, (wBit t).val < outBase) (huOut : uBase + 30 ≤ outBase)
    (huM : ∀ t < 30, uBase + t ≠ (wBit t).val) (hBaseBit0 : wBase ≠ wBit 0) :
    ∀ (k : ℕ) (hk : k < 30) (ho : outBase + (k + 1) ≤ M),
      (prioChainStar uBase outBase wBase wBit hwBase hwBit huOut huM hBaseBit0 k hk ho).countAnd =
        k + 1
  | 0, _, _ => rfl
  | k + 1, _, _ => by
      simp [prioChainStar,
        prioChainStar_countAnd uBase outBase wBase wBit hwBase hwBit huOut huM hBaseBit0 k]
theorem prioChainStar_spec {M : ℕ} (uBase outBase : ℕ)
    (wBase : Wire M) (wBit : ℕ → Wire M) (hwBase : wBase.val < outBase)
    (hwBit : ∀ t < 30, (wBit t).val < outBase) (huOut : uBase + 30 ≤ outBase)
    (huM : ∀ t < 30, uBase + t ≠ (wBit t).val) (hBaseBit0 : wBase ≠ wBit 0) :
    ∀ (k : ℕ) (hk : k < 30) (ho : outBase + (k + 1) ≤ M),
      PreservesOutside outBase (outBase + (k + 1))
        (prioChainStar uBase outBase wBase wBit hwBase hwBit huOut huM hBaseBit0 k hk ho).eval ∧
      ∀ (β : BitAssignment M), (∀ w : Wire M, outBase ≤ w.val → β w = 0) →
        (prioChainStar uBase outBase wBase wBit hwBase hwBit huOut huM hBaseBit0 k hk ho).eval β
            ⟨outBase + k, by omega⟩ =
          prioStarEval (β wBase) (fun t ↦ β (wBit t)) (k + 1)
            (fun i : Fin (k + 1) ↦ β ⟨uBase + i.val, by omega⟩)
  | 0, _, ho => by
      refine ⟨muxBit_preserves _ _ _ _ _ _ _ _ _ _, fun β hz ↦ ?_⟩
      dsimp only [prioChainStar, prioStarEval]
      rw [show (⟨outBase + 0, by omega⟩ : Wire M) = ⟨outBase, by omega⟩ from Fin.ext rfl,
        muxBit_eval _ _ _ _ _ _ _ _ _ _ β (hz _ le_rfl), Function.update_self]
      rfl
  | k + 1, hk, ho => by
      obtain ⟨hPres, ih⟩ := prioChainStar_spec uBase outBase wBase wBit hwBase hwBit huOut huM
        hBaseBit0 k (by omega) (by omega)
      refine ⟨fun β w hw ↦ ?_, fun β hz ↦ ?_⟩
      · simp only [prioChainStar, SsaProg.append_eval]
        exact PreservesOutside.comp (by omega) (by omega) hPres
          (muxBit_preserves _ _ _ _ _ _ _ _ _ _) β w hw
      · simp only [prioChainStar, SsaProg.append_eval]
        generalize hβ₁ : (prioChainStar uBase outBase wBase wBit hwBase hwBit huOut huM hBaseBit0 k
          (by omega) (by omega)).eval β = β₁
        rw [muxBit_eval _ _ _ _ _ _ _ _ _ _ β₁
          (((congrFun hβ₁ _).symm.trans (hPres β ⟨outBase + (k + 1),
            by omega⟩ (Or.inr le_rfl))).trans
            (hz ⟨_, by omega⟩ (Nat.le_add_right outBase (k + 1)))),
          Function.update_self,
          keep_lt_eq hPres hβ₁ ⟨uBase + (k + 1),
            by omega⟩ (show uBase + (k + 1) < outBase by omega),
          keep_lt_eq hPres hβ₁ (wBit (k + 1)) (hwBit (k + 1) hk),
          (congrFun hβ₁ ⟨outBase + k, by omega⟩).symm.trans (ih β hz)]
        rfl
theorem prioStarEval_sum_val (b0 : ZMod 2) (f : ℕ → ZMod 2) :
    ∀ (L : ℕ), (∑ α : BitAssignment L, (prioStarEval b0 f L α).val) =
      b0.val + ∑ t : Fin L, (f t.val).val * 2 ^ t.val
  | 0 => by simp [prioStarEval]
  | L + 1 => by
      have hcardL : Fintype.card (BitAssignment L) = 2 ^ L := by simp [BitAssignment]
      rw [← Equiv.sum_comp (bitSplitLastEquiv L).symm (fun α ↦ (prioStarEval b0 f (L + 1) α).val),
        Fintype.sum_prod_type]
      have hinner : ∀ α₀ : BitAssignment L,
          (∑ b : ZMod 2, (prioStarEval b0 f (L + 1) ((bitSplitLastEquiv L).symm (α₀, b))).val) =
            (prioStarEval b0 f L α₀).val + (f L).val := fun α₀ ↦ by
        rw [sum_zmod2]
        dsimp only [prioStarEval, bitSplitLastEquiv, Equiv.coe_fn_symm_mk]
        simp only [lt_self_iff_false, ↓reduceDIte, zero_ne_one, ↓reduceIte]
        rw [show (fun i : Fin L ↦ if h : i.val < L then α₀ ⟨i.val, h⟩ else 0) = α₀ from
          funext fun i ↦ by simp [i.isLt]]
      rw [Finset.sum_congr rfl fun α₀ _ ↦ hinner α₀, Finset.sum_add_distrib,
        prioStarEval_sum_val b0 f L, Finset.sum_const, Finset.card_univ, hcardL, smul_eq_mul,
        Fin.sum_univ_castSucc]
      dsimp only [Fin.val_castSucc, Fin.val_last]
      ring
def idxMagStar (L st : ℕ) : Fin 7 :=
  if st = 0 then ⟨6 - (L % 7), by omega⟩ else ⟨6 - ((L - 1 - (st - 1)) % 7), by omega⟩
noncomputable abbrev gridKappaRatLo : ℝ :=
  2 * (3141592653 / 1000000000) / (1342516032 / 100000000)
theorem gridKappa_ge_ratLo : gridKappaRatLo ≤ gridKappa := by
  unfold gridKappa gridKappaRatLo
  have h2 := Real.rpow_le_rpow (by norm_num [cellVolume])
    (by norm_num [cellVolume] : cellVolume ≤ (1342516032 / 100000000 : ℝ) ^ 3)
    (by positivity : (0 : ℝ) ≤ 1 / 3)
  have hvol : cellVolume ^ (1 / 3 : ℝ) ≤ 1342516032 / 100000000 := h2.trans_eq (by
    rw [show ((1342516032 / 100000000 : ℝ) ^ 3) =
        (1342516032 / 100000000 : ℝ) ^ (3 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num)]
    norm_num)
  have hvol_pos : (0 : ℝ) < cellVolume ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by norm_num [cellVolume]) _
  exact (div_le_div_of_nonneg_left (by norm_num) hvol_pos hvol).trans
    (div_le_div_of_nonneg_right (by linarith [Real.pi_gt_d20]) hvol_pos.le)
theorem slot1QuadBranchWeight_ge_ratLo :
    ((16129 / 2 : ℝ) * (gridKappaRatLo ^ 2 / 2)) / projectileMass ≤ slot1QuadBranchWeight := by
  unfold slot1QuadBranchWeight
  have h0 : 0 ≤ gridKappaRatLo := by norm_num [gridKappaRatLo]
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (sq_le_sq' (by linarith [gridKappa_ge_ratLo]) gridKappa_ge_ratLo) (by positivity))
    (by norm_num)) (by norm_num [projectileMass])
abbrev slot1DyadicWorkWires : ℕ := 142
abbrev dyadicT0 : ℕ := 117504
abbrev dyadicTq1 : ℕ := 39163
abbrev dyadicTq2 : ℕ := 78326
abbrev dyadicTq3 : ℕ := 117489
noncomputable def dyadicXLin (cfg : Configuration) (w : Fin 3) : ℝ :=
  (2 : ℝ) ^ 27 * (slot1LinBranchWeight cfg w / lambdaSlot1TpHi)
theorem dyadicXLin_nonneg (cfg : Configuration) (w : Fin 3) : 0 ≤ dyadicXLin cfg w := by
  unfold dyadicXLin slot1LinBranchWeight projectileMass lambdaSlot1TpHi
  exact mul_nonneg (by norm_num) (div_nonneg (div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) gridKappa_nonneg) (abs_nonneg _))
    (by norm_num)) (by norm_num))
noncomputable def dyadicSTot (cfg : Configuration) : ℕ :=
  4 * ⌊(dyadicXLin cfg 0 + dyadicXLin cfg 1) / 4⌋₊ + 2
noncomputable def dyadicDl0 (cfg : Configuration) : ℕ := min (dyadicSTot cfg)
    ⌊(dyadicSTot cfg : ℝ) / 2 + (dyadicXLin cfg 0 - dyadicXLin cfg 1) / 2 + 1 / 2⌋₊
noncomputable def dyadicDl1 (cfg : Configuration) : ℕ := dyadicSTot cfg - dyadicDl0 cfg
noncomputable def dyadicDl2 (cfg : Configuration) : ℕ := ⌊dyadicXLin cfg 2 + 1 / 2⌋₊
noncomputable def dyadicTl1 (cfg : Configuration) : ℕ := dyadicT0 + dyadicDl0 cfg
noncomputable def dyadicTl2 (cfg : Configuration) : ℕ := dyadicT0 + dyadicSTot cfg
noncomputable def dyadicTl3 (cfg : Configuration) : ℕ := dyadicT0 + dyadicSTot cfg + dyadicDl2 cfg
theorem dyadicSTot_bounds (cfg : Configuration) : (dyadicXLin cfg 0 + dyadicXLin cfg 1) - 2 <
    (dyadicSTot cfg : ℝ) ∧
    (dyadicSTot cfg : ℝ) ≤ (dyadicXLin cfg 0 + dyadicXLin cfg 1) + 2 := by
  unfold dyadicSTot
  have hle := Nat.floor_le
    (by linarith [dyadicXLin_nonneg cfg 0, dyadicXLin_nonneg cfg 1] :
      0 ≤ (dyadicXLin cfg 0 + dyadicXLin cfg 1) / 4)
  have hgt := Nat.lt_floor_add_one ((dyadicXLin cfg 0 + dyadicXLin cfg 1) / 4)
  push_cast
  exact ⟨by linarith, by linarith⟩
theorem dyadicTl3_lt_two_pow_27 (cfg : Configuration) : dyadicTl3 cfg < 2 ^ 27 := by
  have hs := (dyadicSTot_bounds cfg).2
  have hd2 : (dyadicDl2 cfg : ℝ) ≤ dyadicXLin cfg 2 + 1 / 2 :=
    Nat.floor_le (by linarith [dyadicXLin_nonneg cfg 2])
  have hmul := mul_le_mul gridKappa_le_ratHi (sum_abs_stepVector_projectileMomentum_le cfg)
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num [gridKappaRatHi])
  rw [Fin.sum_univ_three] at hmul
  have hw_sum : slot1LinBranchWeight cfg 0 + slot1LinBranchWeight cfg 1 +
      slot1LinBranchWeight cfg 2 ≤
      (127 * gridKappaRatHi * (50880725 / 1000)) / projectileMass := by
    unfold slot1LinBranchWeight
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) (by norm_num [projectileMass])
  have hx_sum : dyadicXLin cfg 0 + dyadicXLin cfg 1 + dyadicXLin cfg 2 ≤
      (2 : ℝ) ^ 27 * (((127 * gridKappaRatHi * (50880725 / 1000)) / projectileMass) /
        lambdaSlot1TpHi) := by
    rw [show dyadicXLin cfg 0 + dyadicXLin cfg 1 + dyadicXLin cfg 2 =
        (2 : ℝ) ^ 27 * ((slot1LinBranchWeight cfg 0 + slot1LinBranchWeight cfg 1 +
          slot1LinBranchWeight cfg 2) / lambdaSlot1TpHi) by
      unfold dyadicXLin
      ring]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hw_sum (by norm_num [lambdaSlot1TpHi])) (by norm_num)
  exact_mod_cast (show (dyadicTl3 cfg : ℝ) < ((2 ^ 27 : ℕ) : ℝ) by
    unfold dyadicTl3 dyadicT0
    push_cast
    linarith [show (117504 : ℝ) + (2 : ℝ) ^ 27 * (((127 * gridKappaRatHi * (50880725 / 1000)) /
        projectileMass) / lambdaSlot1TpHi) + 5 / 2 < ((2 ^ 27 : ℕ) : ℝ) by
      norm_num [gridKappaRatHi, projectileMass, lambdaSlot1TpHi]])
theorem dyadic_thr_mono (cfg : Configuration) : dyadicTq1 ≤ dyadicTq2 ∧ dyadicTq2 ≤ dyadicTq3 ∧
    dyadicTq3 ≤ dyadicT0 ∧
    dyadicT0 ≤ dyadicTl1 cfg ∧ dyadicTl1 cfg ≤ dyadicTl2 cfg ∧ dyadicTl2 cfg ≤ dyadicTl3 cfg := by
  have hd0 : dyadicDl0 cfg ≤ dyadicSTot cfg := Nat.min_le_left _ _
  unfold dyadicTl1 dyadicTl2 dyadicTl3 dyadicTq1 dyadicTq2 dyadicTq3 dyadicT0
  omega
noncomputable def dyadicLeafIdx (cfg : Configuration) (u : ℕ) : Fin 8 := if u < dyadicT0 then
    if u < dyadicTq2 then if u < dyadicTq1 then 0 else 1 else if u < dyadicTq3 then 2 else 3
    else if u < dyadicTl2 cfg then if u < dyadicTl1 cfg then 4 else 5 else if u < dyadicTl3
    cfg then 6 else 7
def dyadicAxOfLf (lf : Fin 8) : Fin 3 :=
  ⟨min (lf.val % 4) 2, Nat.lt_succ_of_le (Nat.min_le_right _ 2)⟩
noncomputable def dyadicPhiLf (cfg : Configuration) (lf : Fin 8) (ax : Fin 3)
    (u8 : Fin 8 → ZMod 2) (outR outS coinHalf : ZMod 2) : ZMod 2 := if lf.val % 4 = 3 then
    (b2z (slot1Sigma cfg 0) + b2z (slot1Sigma cfg 0 != slot1Sigma cfg 1) + b2z (slot1Sigma cfg
    0 != slot1Sigma cfg 2) + u8 7 + outR * outS) + coinHalf else if lf.val < 4 then 1 + outR *
    outS else b2z (slot1Sigma cfg ax) + u8 7 + coinHalf * (1 + outR)
def dyadicUbr110 (α : BitAssignment 110) : ℕ :=
  ∑ j : Fin 27, (α ⟨30 + j.val, add_fin_lt_of_le j (by decide)⟩).val * 2 ^ j.val
def dyadicOutR110 (α : BitAssignment 110) (u8 : Fin 8 → ZMod 2) : ZMod 2 :=
  prioStarEval (mag7Bit u8 (idxMagStar 25 0)) (fun t ↦ mag7Bit u8 (idxMagStar 25 (t + 1))) 25
    (fun i ↦ α ⟨57 + i.val, add_fin_lt_of_le i (by decide)⟩)
def dyadicOutS110 (α : BitAssignment 110) (u8 : Fin 8 → ZMod 2) : ZMod 2 :=
  prioStarEval (mag7Bit u8 (idxMagStar 14 0)) (fun t ↦ mag7Bit u8 (idxMagStar 14 (t + 1))) 14
    (fun i ↦ α ⟨82 + i.val, add_fin_lt_of_le i (by decide)⟩)
noncomputable def slot1DyadicPred110 (cfg : Configuration) (α : BitAssignment 110) : ZMod 2 :=
  if α ⟨24, by decide⟩ = 1 ∧ α ⟨25, by decide⟩ = 0 ∧ α ⟨26, by decide⟩ = 1 then
    let lf : Fin 8 := dyadicLeafIdx cfg (dyadicUbr110 α)
    let ax : Fin 3 := dyadicAxOfLf lf
    let u8 : Fin 8 → ZMod 2 := slot1U8_110 α ax
    dyadicPhiLf cfg lf ax u8 (dyadicOutR110 α u8) (dyadicOutS110 α u8) (α ⟨109, by decide⟩)
  else 0
section Slot1DyadicPart3BIrred
attribute [local irreducible] basisBits QRegister.extractIndex
noncomputable def slot1DyadicPhaseCore {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) (β : BitAssignment (coreWiresSym mPayload)) : ZMod 2 :=
  slot1DyadicPred110 cfg (fun i ↦ β (rActCore hmPay i))
noncomputable def slot1DyadicSelectDiag {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) : Operator (2 ^ (coreWiresSym mPayload)) := Matrix.diagonal fun g ↦
    ((-1 : ℂ) ^ (slot1DyadicPhaseCore hmPay cfg (basisBits (coreWiresSym mPayload) g)).val)
theorem slot1DyadicSelectDiag_conjTranspose {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) :
    (slot1DyadicSelectDiag hmPay cfg)ᴴ = slot1DyadicSelectDiag hmPay cfg := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [slot1DyadicSelectDiag]
  · simp [slot1DyadicSelectDiag, hij, Ne.symm hij]
theorem slot1DyadicSelectDiag_mul_self {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) :
    slot1DyadicSelectDiag hmPay cfg * slot1DyadicSelectDiag hmPay cfg = 1 := by
  rw [slot1DyadicSelectDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext g
  exact MomSlots01Slot1ProjKinetic.neg_one_pow_bit_mul_self _
noncomputable def slot1DyadicSelectUnitary {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) : Unitary (2 ^ (coreWiresSym mPayload)) :=
  ⟨slot1DyadicSelectDiag hmPay cfg, mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, slot1DyadicSelectDiag_conjTranspose]
    exact slot1DyadicSelectDiag_mul_self hmPay cfg)⟩
@[scoped simp] theorem slot1DyadicSelectUnitary_val {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) :
    (slot1DyadicSelectUnitary hmPay cfg).1 = slot1DyadicSelectDiag hmPay cfg := rfl
theorem slot1DyadicSelectUnitary_sa {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) : (slot1DyadicSelectUnitary hmPay cfg).1ᴴ =
    (slot1DyadicSelectUnitary hmPay cfg).1 := slot1DyadicSelectDiag_conjTranspose hmPay cfg
private theorem rActCore_coin_wire {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (j : Fin 3) :
    rActCore hmPay ⟨24 + j.val, by omega⟩ = coreSixSym mPayload ⟨j.val, by omega⟩ := by
  fin_cases j
  all_goals exact Fin.ext (by
    dsimp [rActCore, coreSixSym, MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
      SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits,
      SpecsAux.SpecMirror.projectileBits])
theorem slot1DyadicSelectUnitary_offCoin {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) :
    (slot1DyadicSelectUnitary hmPay cfg).1 *
      (1 - momCoinProj mPayload (FullSysPrepare6Slot.fullSysCoinIdx 1)) =
      1 - momCoinProj mPayload (FullSysPrepare6Slot.fullSysCoinIdx 1) := by
  rw [Matrix.mul_sub, Matrix.mul_one, slot1DyadicSelectUnitary_val,
    show FullSysPrepare6Slot.fullSysCoinIdx 1 = 5 from rfl, momCoinProj, slotBitProj, slotBitProj,
    slotBitProj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, slot1DyadicSelectDiag,
    Matrix.diagonal_mul_diagonal]
  ext g₁ g₂
  by_cases hg : g₁ = g₂
  · subst hg
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    by_cases hAll :
        basisBits (coreWiresSym mPayload) g₁ (MomSlots01Slot1ProjKinetic.iSlot0Mom mPayload) = 1 ∧
        basisBits (coreWiresSym mPayload) g₁ (MomSlots01Slot1ProjKinetic.iSlot1Mom mPayload) = 0 ∧
        basisBits (coreWiresSym mPayload) g₁ (MomSlots01Slot1ProjKinetic.iSlot2Mom mPayload) = 1
    · obtain ⟨hc0, hc1, hc2⟩ := hAll
      simp [coinBitFin2_5_0, coinBitFin2_5_1, coinBitFin2_5_2, hc0, hc1, hc2,
        show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl]
    · have hPhase0 : slot1DyadicPhaseCore hmPay cfg (basisBits (coreWiresSym mPayload) g₁) = 0 := by
        unfold slot1DyadicPhaseCore slot1DyadicPred110
        dsimp only
        exact MomSlots01Slot1ProjKinetic.ite_neg_s1 (by
          rwa [show rActCore hmPay ⟨24, by decide⟩ = MomSlots01Slot1ProjKinetic.iSlot0Mom mPayload
              from Fin.ext (by dsimp [rActCore,
                MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
                MomSlots01Slot1ProjKinetic.iSlot0Mom]),
            show rActCore hmPay ⟨25, by decide⟩ = MomSlots01Slot1ProjKinetic.iSlot1Mom mPayload
              from Fin.ext (by dsimp [rActCore,
                MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
                MomSlots01Slot1ProjKinetic.iSlot1Mom]),
            show rActCore hmPay ⟨26, by decide⟩ = MomSlots01Slot1ProjKinetic.iSlot2Mom mPayload
              from Fin.ext (by dsimp [rActCore,
                MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
                MomSlots01Slot1ProjKinetic.iSlot2Mom])])
      simp [hPhase0]
  · simp [hg]
theorem slot1DyadicSelectUnitary_conj_highWire {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) (B : Unitary (2 ^ (coreWiresSym mPayload))) (hHigh : ∀ q : Wire
    (coreWiresSym mPayload), 3924 ≤ q.val → ∀ b : Fin 2, B.1 * slotBitProj q b = slotBitProj q
    b * B.1) : HoistedSwapSelectBridge.unitaryConj B (slot1DyadicSelectUnitary hmPay cfg) =
      slot1DyadicSelectUnitary hmPay cfg := by
  let C := coreWiresSym mPayload
  have hbits_eq : ∀ x y : Fin (2 ^ C), B.1 x y ≠ 0 →
      ∀ q : Wire C, 3924 ≤ q.val → basisBits C x q = basisBits C y q := fun x y hxy q hq ↦ by
    let b : Fin 2 := ⟨(basisBits C y q).val, ZMod.val_lt _⟩
    have hcomm := congrFun (congrFun (hHigh q hq b) x) y
    simp only [slotBitProj, Matrix.mul_diagonal, Matrix.diagonal_mul] at hcomm
    rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 (rfl : (basisBits C y q).val = b.val),
      mul_one] at hcomm
    by_cases hx1 : (basisBits C x q).val = b.val
    · exact ZMod.val_injective 2 hx1
    · rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hx1, zero_mul] at hcomm
      exact absurd hcomm hxy
  have hBComm : B.1 * slot1DyadicSelectDiag hmPay cfg = slot1DyadicSelectDiag hmPay cfg * B.1 := by
    ext x y
    simp only [slot1DyadicSelectDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hxy : B.1 x y = 0
    · simp [hxy]
    · have hph : slot1DyadicPhaseCore hmPay cfg (basisBits C x) =
          slot1DyadicPhaseCore hmPay cfg (basisBits C y) := by
        unfold slot1DyadicPhaseCore
        exact congrArg (slot1DyadicPred110 cfg) (funext fun i ↦ hbits_eq x y hxy (rActCore hmPay i)
          (by dsimp [rActCore, MomSlots01Slot1ProjKineticAlt.qreg_block_apply]; omega))
      rw [hph, mul_comm]
  apply Subtype.ext
  rw [HoistedSwapSelectBridge.unitaryConj_val, slot1DyadicSelectUnitary_val, Matrix.mul_assoc,
    ← hBComm, ← Matrix.mul_assoc,
    show (B.1)ᴴ = star B.1 from rfl, Matrix.mem_unitaryGroup_iff'.mp B.2, Matrix.one_mul]
theorem prioStarEval_sum_14 (u8 : Fin 8 → ZMod 2) :
    (∑ α : BitAssignment 14, (prioStarEval (mag7Bit u8 (idxMagStar 14 0))
      (fun t ↦ mag7Bit u8 (idxMagStar 14 (t + 1))) 14 α).val) =
      129 * mag7Nat u8 + (mag7Bit u8 6).val := by
  rw [prioStarEval_sum_val]
  simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero, zero_add, Fin.val_castSucc, Fin.val_last]
  rw [show idxMagStar 14 0 = 6 from rfl, show idxMagStar 14 1 = 0 from rfl,
    show idxMagStar 14 2 = 1 from rfl, show idxMagStar 14 3 = 2 from rfl,
    show idxMagStar 14 4 = 3 from rfl, show idxMagStar 14 5 = 4 from rfl,
    show idxMagStar 14 6 = 5 from rfl, show idxMagStar 14 7 = 6 from rfl,
    show idxMagStar 14 8 = 0 from rfl, show idxMagStar 14 9 = 1 from rfl,
    show idxMagStar 14 10 = 2 from rfl, show idxMagStar 14 11 = 3 from rfl,
    show idxMagStar 14 12 = 4 from rfl, show idxMagStar 14 13 = 5 from rfl,
    show idxMagStar 14 14 = 6 from rfl]
  dsimp only [mag7Nat]
  ring
theorem prioStarEval_sum_25 (u8 : Fin 8 → ZMod 2) :
    (∑ α : BitAssignment 25, (prioStarEval (mag7Bit u8 (idxMagStar 25 0))
      (fun t ↦ mag7Bit u8 (idxMagStar 25 (t + 1))) 25 α).val) =
      264208 * mag7Nat u8 + (mag7Bit u8 2).val + (mag7Bit u8 3).val + 2 * (mag7Bit u8 4).val +
        4 * (mag7Bit u8 5).val + 8 * (mag7Bit u8 6).val := by
  rw [prioStarEval_sum_val]
  repeat rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_zero, zero_add]
  dsimp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero]
  rw [show idxMagStar 25 0 = 2 from rfl, show idxMagStar 25 1 = 3 from rfl,
    show idxMagStar 25 2 = 4 from rfl, show idxMagStar 25 3 = 5 from rfl,
    show idxMagStar 25 4 = 6 from rfl, show idxMagStar 25 5 = 0 from rfl,
    show idxMagStar 25 6 = 1 from rfl, show idxMagStar 25 7 = 2 from rfl,
    show idxMagStar 25 8 = 3 from rfl, show idxMagStar 25 9 = 4 from rfl,
    show idxMagStar 25 10 = 5 from rfl, show idxMagStar 25 11 = 6 from rfl,
    show idxMagStar 25 12 = 0 from rfl, show idxMagStar 25 13 = 1 from rfl,
    show idxMagStar 25 14 = 2 from rfl, show idxMagStar 25 15 = 3 from rfl,
    show idxMagStar 25 16 = 4 from rfl, show idxMagStar 25 17 = 5 from rfl,
    show idxMagStar 25 18 = 6 from rfl, show idxMagStar 25 19 = 0 from rfl,
    show idxMagStar 25 20 = 1 from rfl, show idxMagStar 25 21 = 2 from rfl,
    show idxMagStar 25 22 = 3 from rfl, show idxMagStar 25 23 = 4 from rfl,
    show idxMagStar 25 24 = 5 from rfl, show idxMagStar 25 25 = 6 from rfl]
  dsimp only [mag7Nat]
  ring
attribute [local irreducible] prioStarEval
noncomputable def dyadicPR (u8 : Fin 8 → ZMod 2) : ℝ := ((264208 : ℝ) * (mag7Nat u8 : ℝ) +
    ((mag7Bit u8 2).val : ℝ) + ((mag7Bit u8 3).val : ℝ) + 2 * ((mag7Bit u8 4).val : ℝ) + 4 *
    ((mag7Bit u8 5).val : ℝ) + 8 * ((mag7Bit u8 6).val : ℝ)) / (2 : ℝ) ^ 25
noncomputable def dyadicPS (u8 : Fin 8 → ZMod 2) : ℝ :=
  ((129 : ℝ) * (mag7Nat u8 : ℝ) + ((mag7Bit u8 6).val : ℝ)) / (2 : ℝ) ^ 14
private theorem mag7Bit_vals_lt (u8 : Fin 8 → ZMod 2) : (mag7Bit u8 0).val < 2 ∧
    (mag7Bit u8 1).val < 2 ∧ (mag7Bit u8 2).val < 2 ∧
    (mag7Bit u8 3).val < 2 ∧ (mag7Bit u8 4).val < 2 ∧ (mag7Bit u8 5).val < 2 ∧ (mag7Bit u8 6).val <
      2 :=
  ⟨ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _,
   ZMod.val_lt _, ZMod.val_lt _, ZMod.val_lt _⟩
theorem dyadicPR_bounds (u8 : Fin 8 → ZMod 2) : 0 ≤ dyadicPR u8 ∧ dyadicPR u8 ≤ 1 ∧
    |(mag7Nat u8 : ℝ) / 127 - dyadicPR u8| ≤ 63 / (127 * (2 : ℝ) ^ 25) := by
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6⟩ := mag7Bit_vals_lt u8
  let rN : ℕ := 264208 * mag7Nat u8 + (mag7Bit u8 2).val + (mag7Bit u8 3).val +
    2 * (mag7Bit u8 4).val + 4 * (mag7Bit u8 5).val + 8 * (mag7Bit u8 6).val
  have h1R : (rN : ℝ) ≤ (2 : ℝ) ^ 25 := by
    exact_mod_cast (show rN ≤ 2 ^ 25 by dsimp [rN, mag7Nat]; omega)
  have h2R : (2 : ℝ) ^ 25 * (mag7Nat u8 : ℝ) ≤ 127 * (rN : ℝ) + 63 := by
    exact_mod_cast (show 2 ^ 25 * mag7Nat u8 ≤ 127 * rN + 63 by dsimp [rN, mag7Nat]; omega)
  have h3R : 127 * (rN : ℝ) ≤ (2 : ℝ) ^ 25 * (mag7Nat u8 : ℝ) + 63 := by
    exact_mod_cast (show 127 * rN ≤ 2 ^ 25 * mag7Nat u8 + 63 by dsimp [rN, mag7Nat]; omega)
  have hpR_eq : dyadicPR u8 = (rN : ℝ) / (2 : ℝ) ^ 25 := by
    unfold dyadicPR
    dsimp [rN]
    push_cast
    ring
  rw [hpR_eq]
  exact ⟨by positivity, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩
theorem dyadicPS_bounds (u8 : Fin 8 → ZMod 2) :
    0 ≤ dyadicPS u8 ∧ dyadicPS u8 ≤ 1 ∧
      |((mag7Nat u8 : ℝ) / 127) * ((mag7Nat u8 : ℝ) / 127 - dyadicPS u8)| ≤
        1 / (4 * (2 : ℝ) ^ 14) := by
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6⟩ := mag7Bit_vals_lt u8
  have h1R : (129 : ℝ) * (mag7Nat u8 : ℝ) + ((mag7Bit u8 6).val : ℝ) ≤ (2 : ℝ) ^ 14 := by
    exact_mod_cast (show 129 * mag7Nat u8 + (mag7Bit u8 6).val ≤ 2 ^ 14 by
      dsimp [mag7Nat]
      omega)
  let m : ℝ := (mag7Nat u8 : ℝ)
  refine ⟨div_nonneg (by positivity) (by norm_num), (div_le_one (by norm_num)).mpr h1R, ?_⟩
  rw [show (m / 127) * (m / 127 - dyadicPS u8) =
      (m * (m - 127 * ((mag7Bit u8 6).val : ℝ))) / (16129 * (2 : ℝ) ^ 14) by
    unfold dyadicPS
    dsimp only [m]
    ring, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 16129 * (2 : ℝ) ^ 14)]
  rcases bit_cases (mag7Bit u8 6) with h6 | h6
  · have hm_le : m ≤ 63 := by
      dsimp only [m]
      exact_mod_cast (show mag7Nat u8 ≤ 63 by
        dsimp [mag7Nat]
        rw [h6, ZMod.val_zero]
        omega)
    have hm_nn : 0 ≤ m := Nat.cast_nonneg _
    rw [h6, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero,
      abs_of_nonneg (mul_nonneg hm_nn hm_nn)]
    nlinarith
  · have hm_lo : 64 ≤ m := by
      dsimp only [m]
      exact_mod_cast (show 64 ≤ mag7Nat u8 by
        dsimp [mag7Nat]
        rw [h6, show (1 : ZMod 2).val = 1 from rfl]
        omega)
    have hm_hi : m ≤ 127 := by
      dsimp only [m]
      exact_mod_cast (show mag7Nat u8 ≤ 127 by
        dsimp [mag7Nat]
        omega)
    rw [h6, show (1 : ZMod 2).val = 1 from rfl, Nat.cast_one, mul_one,
      abs_of_nonpos (by nlinarith)]
    nlinarith [sq_nonneg (m - 127 / 2)]
noncomputable def dyadicDelta (cfg : Configuration) : Fin 6 → ℕ
  | 0 | 2 | 4 => dyadicTq1
  | 1 => dyadicDl0 cfg
  | 3 => dyadicDl1 cfg
  | 5 => dyadicDl2 cfg
noncomputable def dyadicValBranch (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) : ℝ :=
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 := u8FromFin (projAxisField xSys w)
  if b.val % 2 = 0 then 2 * dyadicPR u8 * dyadicPS u8 - 1
  else ((-1 : ℝ) ^ (b2z (slot1Sigma cfg w) + u8 7).val) * dyadicPR u8
noncomputable def bUnitTwosSlot1Dyadic (cfg : Configuration) : Operator
    (2 ^ SpecsAux.SpecMirror.systemQubits) := Matrix.diagonal fun xSys ↦ ((((∑ b : Fin 6,
    ((dyadicDelta cfg b : ℝ) / (2 : ℝ) ^ 27) * dyadicValBranch cfg xSys b) : ℝ)) : ℂ)
private theorem tree4_sum_of_in {α : Type*} (g : α → ℂ) (a0 a1 a2 a3 : α) (ha3 : g a3 = 0)
    {lo t1 t2 t3 x : ℕ} (_h01 : lo ≤ t1) (h12 : t1 ≤ t2) (h23 : t2 ≤ t3) (hlo : lo ≤ x) :
    g (if x < t2 then if x < t1 then a0 else a1 else if x < t3 then a2 else a3) =
      (if lo ≤ x ∧ x < t1 then g a0 else 0) + (if t1 ≤ x ∧ x < t2 then g a1 else 0) +
        (if t2 ≤ x ∧ x < t3 then g a2 else 0) := by
  split_ifs
  all_goals first | omega | simp [ha3]
private theorem tree4_sum_of_out (g0 g1 g2 : ℂ) {lo t1 t2 t3 x : ℕ} (h01 : lo ≤ t1) (h12 : t1 ≤
    t2) (h23 : t2 ≤ t3) (hout : x < lo ∨ t3 ≤ x) :
    (if lo ≤ x ∧ x < t1 then g0 else 0) + (if t1 ≤ x ∧ x < t2 then g1 else 0) +
      (if t2 ≤ x ∧ x < t3 then g2 else 0) = 0 := by
  rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 (by omega : ¬(lo ≤ x ∧ x < t1)),
    MomSlots01Slot1ProjKinetic.ite_neg_s1 (by omega : ¬(t1 ≤ x ∧ x < t2)),
    MomSlots01Slot1ProjKinetic.ite_neg_s1 (by omega : ¬(t2 ≤ x ∧ x < t3))]
  ring
theorem sum_dyadicLeafIdx_of_pad_zero (cfg : Configuration) (g : Fin 8 → ℂ) (hg3 : g 3 = 0)
    (hg7 : g 7 = 0) : (∑ v : Fin (2 ^ 27), g (dyadicLeafIdx cfg v.val)) = (dyadicTq1 : ℂ) * g
    0 + (dyadicTq1 : ℂ) * g 1 + (dyadicTq1 : ℂ) * g 2 + (dyadicDl0 cfg : ℂ) * g 4 +
      (dyadicDl1 cfg : ℂ) * g 5 + (dyadicDl2 cfg : ℂ) * g 6 := by
  obtain ⟨hm01, hm12, hm23, hm34, hm45, hm56⟩ := dyadic_thr_mono cfg
  have htl3_le : dyadicTl3 cfg ≤ 2 ^ 27 := le_of_lt (dyadicTl3_lt_two_pow_27 cfg)
  have hpt : ∀ v : Fin (2 ^ 27),
      g (dyadicLeafIdx cfg v.val) =
        ((if 0 ≤ v.val ∧ v.val < dyadicTq1 then g 0 else 0) +
         (if dyadicTq1 ≤ v.val ∧ v.val < dyadicTq2 then g 1 else 0) +
         (if dyadicTq2 ≤ v.val ∧ v.val < dyadicTq3 then g 2 else 0)) +
        ((if dyadicT0 ≤ v.val ∧ v.val < dyadicTl1 cfg then g 4 else 0) +
         (if dyadicTl1 cfg ≤ v.val ∧ v.val < dyadicTl2 cfg then g 5 else 0) +
         (if dyadicTl2 cfg ≤ v.val ∧ v.val < dyadicTl3 cfg then g 6 else 0)) := fun v ↦ by
    unfold dyadicLeafIdx
    by_cases ct0 : v.val < dyadicT0
    · rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 ct0,
        tree4_sum_of_in g 0 1 2 3 hg3 (Nat.zero_le _) hm01 hm12 (Nat.zero_le _),
        tree4_sum_of_out (g 4) (g 5) (g 6) hm34 hm45 hm56 (Or.inl ct0), add_zero]
    · rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 ct0,
        tree4_sum_of_in g 4 5 6 7 hg7 hm34 hm45 hm56 (Nat.le_of_not_lt ct0),
        tree4_sum_of_out (g 0) (g 1) (g 2) (Nat.zero_le _) hm01 hm12 (Or.inr (by omega)),
        zero_add]
  simp_rw [hpt]
  repeat rw [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [card_fin_Ico_two_pow (Nat.zero_le dyadicTq1) (by omega : dyadicTq1 ≤ 2 ^ 27),
    card_fin_Ico_two_pow hm01 (by omega : dyadicTq2 ≤ 2 ^ 27),
    card_fin_Ico_two_pow hm12 (by omega : dyadicTq3 ≤ 2 ^ 27),
    card_fin_Ico_two_pow hm34 (by omega : dyadicTl1 cfg ≤ 2 ^ 27),
    card_fin_Ico_two_pow hm45 (by omega : dyadicTl2 cfg ≤ 2 ^ 27),
    card_fin_Ico_two_pow hm56 htl3_le,
    show dyadicTq1 - 0 = dyadicTq1 from rfl,
    show dyadicTq2 - dyadicTq1 = dyadicTq1 by decide,
    show dyadicTq3 - dyadicTq2 = dyadicTq1 by decide,
    show dyadicTl1 cfg - dyadicT0 = dyadicDl0 cfg from
      Nat.add_sub_cancel_left dyadicT0 (dyadicDl0 cfg),
    show dyadicTl2 cfg - dyadicTl1 cfg = dyadicDl1 cfg from
      Nat.add_sub_add_left dyadicT0 (dyadicSTot cfg) (dyadicDl0 cfg),
    show dyadicTl3 cfg - dyadicTl2 cfg = dyadicDl2 cfg from
      Nat.add_sub_cancel_left (dyadicT0 + dyadicSTot cfg) (dyadicDl2 cfg)]
  ring
attribute [local irreducible] dyadicLeafIdx
noncomputable def payloadDyadicSplitEquiv {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) : Fin (2 ^ mPayload) ≃ Fin (2 ^ 27) × BitAssignment 25 × BitAssignment 14 ×
    BitAssignment 13 × ZMod 2 × BitAssignment (mPayload - 80) :=
  (basisBitsEquiv mPayload).trans
  { toFun := fun γ ↦
      ((basisBitsEquiv 27).symm (fun i ↦ γ ⟨i.val, by omega⟩),
       fun i ↦ γ ⟨27 + i.val, by omega⟩,
       fun i ↦ γ ⟨52 + i.val, by omega⟩,
       fun i ↦ γ ⟨66 + i.val, by omega⟩,
       γ ⟨79, by omega⟩,
       fun i ↦ γ ⟨80 + i.val, by omega⟩)
    invFun := fun ⟨vBr, αR, αS, αGap, cHalf, rest⟩ idx ↦
      if h1 : idx.val < 27 then basisBits 27 vBr ⟨idx.val, h1⟩
      else if h2 : idx.val < 52 then αR ⟨idx.val - 27, by omega⟩
      else if h3 : idx.val < 66 then αS ⟨idx.val - 52, by omega⟩
      else if h4 : idx.val < 79 then αGap ⟨idx.val - 66, by omega⟩
      else if h5 : idx.val = 79 then cHalf
      else rest ⟨idx.val - 80, by have := idx.isLt; omega⟩
    left_inv := fun γ ↦ funext fun idx ↦ by
      dsimp only
      split_ifs with h1 h2 h3 h4 h5
      · exact MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1 _ _
      all_goals
        refine congrArg γ (Fin.ext ?_)
        dsimp
        omega
    right_inv := fun ⟨vBr, αR, αS, αGap, cHalf, rest⟩ ↦ by
      refine Prod.ext ((basisBitsEquiv 27).injective ?_)
        (Prod.ext (funext fun i ↦ ?_) (Prod.ext (funext fun i ↦ ?_)
          (Prod.ext (funext fun i ↦ ?_) (Prod.ext ?_ (funext fun i ↦ ?_)))))
      · rw [(basisBitsEquiv 27).apply_symm_apply, basisBitsEquiv_apply_eq]
        exact funext fun i ↦ MomSlots01Slot1ProjKinetic.dite_pos_s1 i.isLt
      all_goals
        dsimp only
        split_ifs
        all_goals first
          | omega
          | rfl
          | exact congrArg αR (Fin.ext (Nat.add_sub_cancel_left 27 i.val))
          | exact congrArg αS (Fin.ext (Nat.add_sub_cancel_left 52 i.val))
          | exact congrArg αGap (Fin.ext (Nat.add_sub_cancel_left 66 i.val))
          | exact congrArg rest (Fin.ext (Nat.add_sub_cancel_left 80 i.val)) }
def dyadicUbr {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (γ : BitAssignment mPayload) : ℕ :=
  ∑ j : Fin 27, (γ ⟨j.val, lt_of_lt_of_le j.isLt (le_trans (by decide) hmPay)⟩).val * 2 ^ j.val
def dyadicOutR {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (γ : BitAssignment mPayload) (u8 : Fin 8 →
    ZMod 2) : ZMod 2 :=
  prioStarEval (mag7Bit u8 (idxMagStar 25 0)) (fun t ↦ mag7Bit u8 (idxMagStar 25 (t + 1))) 25
    (fun i ↦ γ ⟨27 + i.val, add_fin_lt_of_le i (le_trans (by decide) hmPay)⟩)
def dyadicOutS {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (γ : BitAssignment mPayload) (u8 : Fin 8 →
    ZMod 2) : ZMod 2 :=
  prioStarEval (mag7Bit u8 (idxMagStar 14 0)) (fun t ↦ mag7Bit u8 (idxMagStar 14 (t + 1))) 14
    (fun i ↦ γ ⟨52 + i.val, add_fin_lt_of_le i (le_trans (by decide) hmPay)⟩)
noncomputable def dyadicPhaseScalar {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (u : Fin (2 ^ mPayload)) : ℂ :=
  let γ := basisBits mPayload u
  let lf : Fin 8 := dyadicLeafIdx cfg (dyadicUbr hmPay γ)
  let ax : Fin 3 := dyadicAxOfLf lf
  let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys ax)
  ((-1 : ℂ) ^ (dyadicPhiLf cfg lf ax u8 (dyadicOutR hmPay γ u8)
    (dyadicOutS hmPay γ u8) (γ ⟨79, lt_of_lt_of_le (by decide) hmPay⟩)).val)
theorem sixProj_mul_slot1DyadicSelectDiag {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) : (coreSixSym mPayload).basisOutcomeProjector
    (coinSixOutcome 5) * slot1DyadicSelectDiag hmPay cfg = ∑ u : Fin (2 ^ mPayload),
      (corePayloadSym mPayload).basisOutcomeProjector u *
    (coreSixSym mPayload).basisOutcomeProjector (coinSixOutcome 5) *
      (coreSysSym mPayload).embedMatrix
    (Matrix.diagonal (fun xSys ↦ dyadicPhaseScalar hmPay cfg xSys u)) := by
  have hemb : ∀ u : Fin (2 ^ mPayload),
    (coreSysSym mPayload).embedMatrix (Matrix.diagonal (fun xSys ↦
    dyadicPhaseScalar hmPay cfg xSys u)) = Matrix.diagonal
      (fun g ↦ dyadicPhaseScalar hmPay cfg ((coreSysSym mPayload).extractIndex g) u) :=
    fun _ ↦ MomSlots01Slot1ProjKinetic.embedMatrix_diagonal (coreSysSym mPayload) _
  simp_rw [hemb, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  rw [slot1DyadicSelectDiag, Matrix.diagonal_mul_diagonal]
  ext g₁ g₂
  by_cases hg : g₁ = g₂
  · subst hg
    simp only [Matrix.diagonal_apply_eq, Matrix.sum_apply]
    let u₀ : Fin (2 ^ mPayload) := (corePayloadSym mPayload).extractIndex g₁
    rw [Finset.sum_eq_single u₀ (fun u _ hu ↦ by simp [u₀, Ne.symm hu])
      (fun h ↦ (h (Finset.mem_univ u₀)).elim)]
    simp only [u₀, ↓reduceIte, one_mul]
    by_cases hSix : (coreSixSym mPayload).extractIndex g₁ = coinSixOutcome 5
    · simp only [hSix, ↓reduceIte, one_mul]
      unfold slot1DyadicPhaseCore
      generalize hα :
        (fun i ↦ basisBits (coreWiresSym mPayload) g₁ (rActCore hmPay i)) = α
      have hbit6 : ∀ i : Fin 6,
          basisBits (coreWiresSym mPayload) g₁ ((coreSixSym mPayload) i) =
            if h : i.val < 3 then basisBits 3 (5 : Fin 8) ⟨i.val, h⟩ else 0 := fun i ↦ by
        rw [← (coreSixSym mPayload).basisBits_extractIndex g₁ i, hSix]
        exact MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1 _ i
      have hc0 : α ⟨24, by decide⟩ = basisBits 3 (5 : Fin 8) 0 :=
        (congrFun hα _).symm.trans ((congrArg _ (rActCore_coin_wire hmPay 0)).trans (hbit6 0))
      have hc1 : α ⟨25, by decide⟩ = basisBits 3 (5 : Fin 8) 1 :=
        (congrFun hα _).symm.trans ((congrArg _ (rActCore_coin_wire hmPay 1)).trans (hbit6 1))
      have hc2 : α ⟨26, by decide⟩ = basisBits 3 (5 : Fin 8) 2 :=
        (congrFun hα _).symm.trans ((congrArg _ (rActCore_coin_wire hmPay 2)).trans (hbit6 2))
      have hpay (k : ℕ) (hk : k < 80) :
          α ⟨30 + k, by omega⟩ = basisBits mPayload u₀ ⟨k, by omega⟩ := by
        rw [← hα]
        dsimp only
        rw [show rActCore hmPay ⟨30 + k, by omega⟩ = corePayloadSym mPayload ⟨k, by omega⟩ from
          Fin.ext (by
            dsimp [rActCore, corePayloadSym,
              MomSlots01Slot1ProjKineticAlt.qreg_block_apply, SpecsAux.SpecMirror.systemQubits,
              SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
                SpecsAux.SpecMirror.projectileBits]
            omega)]
        exact ((corePayloadSym mPayload).basisBits_extractIndex g₁ ⟨k, by omega⟩).symm
      have hproj (ax : Fin 3) (b : Fin 8) :
          α ⟨8 * ax.val + b.val, by omega⟩ =
            u8FromFin (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) b := by
        rw [← hα]
        dsimp only
        rw [show rActCore hmPay ⟨8 * ax.val + b.val, by omega⟩ =
            (coreSysSym mPayload) ((proj3Axes ax) b) from Fin.ext (by
          dsimp [rActCore, coreSysSym, proj3Axes,
            MomSlots01Slot1ProjKineticAlt.qreg_block_apply,
            MomSlots01Slot1ProjKineticAlt.qreg_block_wires_apply,
            MomSlots01Slot1ProjKineticAlt.qreg_whole_wires,
            MomSlots01Slot1ProjKineticAlt.emb_trans_apply,
            MomSlots01Slot1ProjKineticAlt.emb_refl_apply,
            MomSlots01Slot1ProjKineticAlt.emb_mk_apply,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits]
          omega),
          ← (coreSysSym mPayload).basisBits_extractIndex g₁ ((proj3Axes ax) b),
          ← (proj3Axes ax).basisBits_extractIndex ((coreSysSym mPayload).extractIndex g₁) b]
        exact basisBits_eq_testBit 8 (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) b
      unfold slot1DyadicPred110 dyadicPhaseScalar
      dsimp only
      rw [hc0, hc1, hc2,
        MomSlots01Slot1ProjKinetic.ite_pos_s1 ((coin3_bits_eq_5_iff 5).mpr rfl)]
      have huBr : dyadicUbr110 α = dyadicUbr hmPay (basisBits mPayload u₀) :=
        Finset.sum_congr rfl fun j _ ↦ by rw [hpay j.val (lt_trans j.isLt (by decide))]
      have hu8 : ∀ ax : Fin 3,
        slot1U8_110 α ax = u8FromFin (projAxisField ((coreSysSym mPayload).extractIndex g₁) ax) :=
        fun ax ↦ funext (hproj ax)
      have hOutR : ∀ u8 : Fin 8 → ZMod 2,
          dyadicOutR110 α u8 = dyadicOutR hmPay (basisBits mPayload u₀) u8 := fun u8 ↦
        congrArg (prioStarEval (mag7Bit u8 (idxMagStar 25 0))
          (fun t ↦ mag7Bit u8 (idxMagStar 25 (t + 1))) 25) (funext fun i ↦ by
          have hk : 27 + i.val < 80 := add_fin_lt_of_le i (by decide)
          exact (congrArg α (Fin.ext (Nat.add_assoc 30 27 i.val) :
            (⟨57 + i.val, add_fin_lt_of_le i (by decide)⟩ : Fin 110) =
              ⟨30 + (27 + i.val), Nat.add_lt_add_left hk 30⟩)).trans (hpay (27 + i.val) hk))
      have hOutS : ∀ u8 : Fin 8 → ZMod 2,
          dyadicOutS110 α u8 = dyadicOutS hmPay (basisBits mPayload u₀) u8 := fun u8 ↦
        congrArg (prioStarEval (mag7Bit u8 (idxMagStar 14 0))
          (fun t ↦ mag7Bit u8 (idxMagStar 14 (t + 1))) 14) (funext fun i ↦ by
          have hk : 52 + i.val < 80 := add_fin_lt_of_le i (by decide)
          exact (congrArg α (Fin.ext (Nat.add_assoc 30 52 i.val) :
            (⟨82 + i.val, add_fin_lt_of_le i (by decide)⟩ : Fin 110) =
              ⟨30 + (52 + i.val), Nat.add_lt_add_left hk 30⟩)).trans (hpay (52 + i.val) hk))
      have h79 : α ⟨109, by decide⟩ =
          basisBits mPayload u₀ ⟨79, lt_of_lt_of_le (by decide) hmPay⟩ := hpay 79 (by decide)
      rw [huBr, hOutR, hOutS, h79]
      simp_rw [hu8]
      dsimp only [u₀]
    · simp [hSix]
  · simp [Matrix.sum_apply, hg]
def dyadicBranchOfNonPad (lf : Fin 8) (hnp : lf.val % 4 ≠ 3) : Fin 6 :=
  ⟨2 * (lf.val % 4) + (if lf.val < 4 then 0 else 1), by
    split_ifs
    all_goals omega⟩
theorem inner_sum_dyadic_leaf (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (lf : Fin 8) :
    (∑ αR : BitAssignment 25, ∑ αS : BitAssignment 14, ∑ coinHalf : ZMod 2,
      let ax : Fin 3 := dyadicAxOfLf lf
      let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys ax)
      let outR := prioStarEval (mag7Bit u8 (idxMagStar 25 0))
        (fun t ↦ mag7Bit u8 (idxMagStar 25 (t + 1))) 25 αR
      let outS := prioStarEval (mag7Bit u8 (idxMagStar 14 0))
        (fun t ↦ mag7Bit u8 (idxMagStar 14 (t + 1))) 14 αS
      ((-1 : ℂ) ^ (dyadicPhiLf cfg lf ax u8 outR outS coinHalf).val)) =
    if hpad : lf.val % 4 = 3 then 0 else (2 : ℂ) * ((2 ^ 25 : ℕ) : ℂ) * ((2 ^ 14 : ℕ) : ℂ) *
      ((dyadicValBranch cfg xSys (dyadicBranchOfNonPad lf hpad) : ℝ) : ℂ) := by
  have hcardR : Fintype.card (BitAssignment 25) = 2 ^ 25 := by simp [BitAssignment]
  have hcardS : Fintype.card (BitAssignment 14) = 2 ^ 14 := by simp [BitAssignment]
  unfold dyadicPhiLf
  by_cases hpad : lf.val % 4 = 3
  · simp only [hpad, ↓reduceIte, ↓reduceDIte]
    exact Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦
      (sum_zmod2 _).trans (neg_one_pow_pad_cancel _)
  · simp only [hpad, ↓reduceIte, ↓reduceDIte]
    let b6 : Fin 6 := dyadicBranchOfNonPad lf hpad
    let w : Fin 3 := ⟨b6.val / 2, by omega⟩
    have hax_eq : dyadicAxOfLf lf = w := Fin.ext (by
      dsimp only [dyadicAxOfLf, w, b6, dyadicBranchOfNonPad]
      split_ifs
      all_goals omega)
    let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys w)
    let rE (αR : BitAssignment 25) := prioStarEval (mag7Bit u8 (idxMagStar 25 0))
      (fun t ↦ mag7Bit u8 (idxMagStar 25 (t + 1))) 25 αR
    let sE (αS : BitAssignment 14) := prioStarEval (mag7Bit u8 (idxMagStar 14 0))
      (fun t ↦ mag7Bit u8 (idxMagStar 14 (t + 1))) 14 αS
    let rSumC : ℂ := (264208 : ℂ) * (mag7Nat u8 : ℂ) + ((mag7Bit u8 2).val : ℂ) +
      ((mag7Bit u8 3).val : ℂ) + 2 * ((mag7Bit u8 4).val : ℂ) +
      4 * ((mag7Bit u8 5).val : ℂ) + 8 * ((mag7Bit u8 6).val : ℂ)
    let sSumC : ℂ := (129 : ℂ) * (mag7Nat u8 : ℂ) + ((mag7Bit u8 6).val : ℂ)
    have hsumR : (∑ αR : BitAssignment 25, ((rE αR).val : ℂ)) = rSumC := by
      dsimp only [rE, rSumC]
      exact_mod_cast prioStarEval_sum_25 u8
    by_cases hlt4 : lf.val < 4
    · simp only [hlt4, ↓reduceIte, hax_eq]
      have hsumS : (∑ αS : BitAssignment 14, ((sE αS).val : ℂ)) = sSumC := by
        dsimp only [sE, sSumC]
        exact_mod_cast prioStarEval_sum_14 u8
      rw [Finset.sum_congr rfl fun αR _ ↦ Finset.sum_congr rfl fun αS _ ↦
        show (∑ _c : ZMod 2, ((-1 : ℂ) ^ (1 + rE αR * sE αS).val)) =
            (4 : ℂ) * ((rE αR).val : ℂ) * ((sE αS).val : ℂ) - 2 by
          rw [sum_zmod2, neg_one_pow_quad_eq]
          ring,
        Finset.sum_congr rfl fun αR _ ↦ show (∑ αS : BitAssignment 14,
            ((4 : ℂ) * ((rE αR).val : ℂ) * ((sE αS).val : ℂ) - 2)) =
            ((4 : ℂ) * sSumC) * ((rE αR).val : ℂ) - 2 * ((2 ^ 14 : ℕ) : ℂ) by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumS, Finset.sum_const,
            Finset.card_univ, hcardS, nsmul_eq_mul]
          ring,
        Finset.sum_sub_distrib, ← Finset.mul_sum, hsumR, Finset.sum_const, Finset.card_univ,
        hcardR, nsmul_eq_mul]
      unfold dyadicValBranch dyadicPR dyadicPS
      dsimp only [rSumC, sSumC]
      rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 (by simp [dyadicBranchOfNonPad, hlt4])]
      push_cast
      norm_num
      ring
    · simp only [hlt4, ↓reduceIte, hax_eq]
      rw [Finset.sum_congr rfl fun αR _ ↦ Finset.sum_congr rfl fun _ _ ↦
        (sum_zmod2 _).trans (neg_one_pow_lin_sum (b2z (slot1Sigma cfg w) + u8 7) (rE αR))]
      simp_rw [Finset.sum_const, Finset.card_univ, hcardS, nsmul_eq_mul, ← mul_assoc]
      rw [← Finset.mul_sum, hsumR]
      unfold dyadicValBranch dyadicPR
      dsimp only [rSumC]
      rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 (by simp [dyadicBranchOfNonPad, hlt4])]
      push_cast
      norm_num
      ring
theorem avg_dyadicPhaseScalar_sym {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    ((2 : ℂ)⁻¹ ^ mPayload) * (∑ u : Fin (2 ^ mPayload),
      dyadicPhaseScalar hmPay cfg xSys u) = bUnitTwosSlot1Dyadic cfg xSys xSys := by
  have hpow_inv : ∀ k : ℕ, ((2 : ℂ)⁻¹ ^ k) * ((2 ^ k : ℕ) : ℂ) = 1 := fun k ↦ by
    push_cast
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero k two_ne_zero)
  unfold bUnitTwosSlot1Dyadic
  rw [Matrix.diagonal_apply_eq]
  let e := payloadDyadicSplitEquiv hmPay
  rw [← Equiv.sum_comp e.symm (fun u ↦ dyadicPhaseScalar hmPay cfg xSys u)]
  have hcardGap : Fintype.card (BitAssignment 13) = 2 ^ 13 := by simp [BitAssignment]
  have hcardPost : Fintype.card (BitAssignment (mPayload - 80)) =
      2 ^ (mPayload - 80) := by simp [BitAssignment]
  have hbody : ∀ (vBr : Fin (2 ^ 27)) (αR : BitAssignment 25) (αS : BitAssignment 14)
      (αGap : BitAssignment 13) (coinHalf : ZMod 2)
      (rest : BitAssignment (mPayload - 80)),
      dyadicPhaseScalar hmPay cfg xSys (e.symm (vBr, αR, αS, αGap, coinHalf, rest)) =
        let lf : Fin 8 := dyadicLeafIdx cfg vBr.val
        let ax : Fin 3 := dyadicAxOfLf lf
        let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys ax)
        let outR : ZMod 2 :=
          prioStarEval (mag7Bit u8 (idxMagStar 25 0))
            (fun t ↦ mag7Bit u8 (idxMagStar 25 (t + 1))) 25 αR
        let outS : ZMod 2 :=
          prioStarEval (mag7Bit u8 (idxMagStar 14 0))
            (fun t ↦ mag7Bit u8 (idxMagStar 14 (t + 1))) 14 αS
        ((-1 : ℂ) ^ (dyadicPhiLf cfg lf ax u8 outR outS coinHalf).val) := by
    intro vBr αR αS αGap coinHalf rest
    have hsymm := e.apply_symm_apply (vBr, αR, αS, αGap, coinHalf, rest)
    have hvBr : (∑ j : Fin 27, (basisBits mPayload
        (e.symm (vBr, αR, αS, αGap, coinHalf, rest)) ⟨j.val, by omega⟩).val * 2 ^ j.val) =
        vBr.val := by
      have hbit (j : Fin 27) :
          basisBits mPayload (e.symm (vBr, αR, αS, αGap, coinHalf, rest))
            ⟨j.val, by omega⟩ = basisBits 27 vBr j := by
        have ht := congrArg Prod.fst hsymm
        dsimp only [e, payloadDyadicSplitEquiv, Equiv.trans_apply] at ht
        try rw [MomSlot1GeomPriority288.basisBitsEquiv_apply_eq] at ht
        exact (MomSlots01Slot1ProjKinetic.basisBits_symm_apply_local_slot1 _ j).symm.trans
          (congrFun (congrArg (basisBits 27) ht) j)
      simp_rw [hbit]
      exact sum_basisBits_val_eq vBr
    have hR (i : Fin 25) : basisBits mPayload (e.symm (vBr, αR, αS, αGap, coinHalf, rest))
        ⟨27 + i.val, by omega⟩ = αR i := by
      have ht := congrFun (congrArg (fun p ↦ p.2.1) hsymm) i
      dsimp only [e, payloadDyadicSplitEquiv, Equiv.trans_apply] at ht
      try rw [MomSlot1GeomPriority288.basisBitsEquiv_apply_eq] at ht
      exact ht
    have hS (i : Fin 14) : basisBits mPayload (e.symm (vBr, αR, αS, αGap, coinHalf, rest))
        ⟨52 + i.val, by omega⟩ = αS i := by
      have ht := congrFun (congrArg (fun p ↦ p.2.2.1) hsymm) i
      dsimp only [e, payloadDyadicSplitEquiv, Equiv.trans_apply] at ht
      try rw [MomSlot1GeomPriority288.basisBitsEquiv_apply_eq] at ht
      exact ht
    have hcH : basisBits mPayload (e.symm (vBr, αR, αS, αGap, coinHalf, rest))
        ⟨79, by omega⟩ = coinHalf := by
      have ht := congrArg (fun p ↦ p.2.2.2.2.1) hsymm
      dsimp only [e, payloadDyadicSplitEquiv, Equiv.trans_apply] at ht
      try rw [MomSlot1GeomPriority288.basisBitsEquiv_apply_eq] at ht
      exact ht
    unfold dyadicPhaseScalar dyadicUbr dyadicOutR dyadicOutS
    dsimp only
    rw [hvBr, funext hR, funext hS, hcH]
  simp_rw [Fintype.sum_prod_type, hbody, Finset.sum_const, Finset.card_univ,
    hcardPost, hcardGap, nsmul_eq_mul]
  let gLeaf : Fin 8 → ℂ := fun lf ↦ if hpad : lf.val % 4 = 3 then 0 else (2 : ℂ) *
      ((2 ^ 25 : ℕ) : ℂ) * ((2 ^ 14 : ℕ) : ℂ) *
      ((dyadicValBranch cfg xSys (dyadicBranchOfNonPad lf hpad) : ℝ) : ℂ)
  let cExtra : ℂ := ((2 ^ 13 : ℕ) : ℂ) * ((2 ^ (mPayload - 80) : ℕ) : ℂ)
  have hinner_v : ∀ vBr : Fin (2 ^ 27),
      (∑ αR : BitAssignment 25, ∑ αS : BitAssignment 14,
        (((2 ^ 13 : ℕ) : ℂ) * ∑ coinHalf : ZMod 2,
          (((2 ^ (mPayload - 80) : ℕ) : ℂ) *
            (let lf : Fin 8 := dyadicLeafIdx cfg vBr.val
             let ax : Fin 3 := dyadicAxOfLf lf
             let u8 : Fin 8 → ZMod 2 := u8FromFin (projAxisField xSys ax)
             let outR : ZMod 2 :=
               prioStarEval (mag7Bit u8 (idxMagStar 25 0))
                 (fun t ↦ mag7Bit u8 (idxMagStar 25 (t + 1))) 25 αR
             let outS : ZMod 2 :=
               prioStarEval (mag7Bit u8 (idxMagStar 14 0))
                 (fun t ↦ mag7Bit u8 (idxMagStar 14 (t + 1))) 14 αS
             ((-1 : ℂ) ^ (dyadicPhiLf cfg lf ax u8 outR outS coinHalf).val))))) =
      cExtra * gLeaf (dyadicLeafIdx cfg vBr.val) := fun vBr ↦ by
    dsimp only [cExtra]
    simp_rw [← Finset.mul_sum]
    rw [← mul_assoc]
    exact congrArg (cExtra * ·) (inner_sum_dyadic_leaf cfg xSys (dyadicLeafIdx cfg vBr.val))
  rw [Finset.sum_congr rfl fun vBr _ ↦ hinner_v vBr, ← Finset.mul_sum, ← mul_assoc]
  have hpref : ((2 : ℂ)⁻¹ ^ mPayload) * cExtra = (2 : ℂ)⁻¹ ^ 67 := by
    have hm : mPayload = (mPayload - 80) + 13 + 67 := by omega
    rw [show (2 : ℂ)⁻¹ ^ mPayload =
        (2 : ℂ)⁻¹ ^ (mPayload - 80) * (2 : ℂ)⁻¹ ^ 13 * (2 : ℂ)⁻¹ ^ 67 by
      conv_lhs => rw [hm]
      rw [pow_add, pow_add]]
    dsimp only [cExtra]
    linear_combination
      ((2 : ℂ)⁻¹ ^ 13 * ((2 ^ 13 : ℕ) : ℂ) * (2 : ℂ)⁻¹ ^ 67) * hpow_inv (mPayload - 80) +
      ((2 : ℂ)⁻¹ ^ 67) * hpow_inv 13
  rw [hpref, sum_dyadicLeafIdx_of_pad_zero cfg gLeaf (by simp [gLeaf]) (by simp [gLeaf])]
  have hg_np : ∀ (lf : Fin 8) (hnp : lf.val % 4 ≠ 3), gLeaf lf =
      (2 : ℂ) * ((2 ^ 25 : ℕ) : ℂ) * ((2 ^ 14 : ℕ) : ℂ) *
        ((dyadicValBranch cfg xSys (dyadicBranchOfNonPad lf hnp) : ℝ) : ℂ) := fun lf hnp ↦ by
    dsimp only [gLeaf]
    rw [MomSlots01Slot1ProjKinetic.dite_neg_s1 hnp]
  rw [hg_np 0 (by decide), hg_np 1 (by decide), hg_np 2 (by decide),
    hg_np 4 (by decide), hg_np 5 (by decide), hg_np 6 (by decide), sum_fin6_real,
    show dyadicBranchOfNonPad 0 (by decide) = 0 from rfl,
    show dyadicBranchOfNonPad 1 (by decide) = 2 from rfl,
    show dyadicBranchOfNonPad 2 (by decide) = 4 from rfl,
    show dyadicBranchOfNonPad 4 (by decide) = 1 from rfl,
    show dyadicBranchOfNonPad 5 (by decide) = 3 from rfl,
    show dyadicBranchOfNonPad 6 (by decide) = 5 from rfl]
  dsimp only [dyadicDelta]
  push_cast
  norm_num
  ring
private theorem diag_comm {N : ℕ} (f g : Fin N → ℂ) : Matrix.diagonal f * Matrix.diagonal g =
    Matrix.diagonal g * Matrix.diagonal f := by
  simp only [Matrix.diagonal_mul_diagonal, mul_comm]
private theorem slot1Dyadic_hadamard_topBlock_five {mPayload : ℕ} (hmPay : 80 ≤
    mPayload) (cfg : Configuration) :
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) 5) *
    (unitaryConj (coreHadamardUnitary mPayload) (slot1DyadicSelectUnitary hmPay cfg)).1 *
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) 5) =
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) 5) *
      (coreSysSym mPayload).embedMatrix (bUnitTwosSlot1Dyadic cfg) *
    (coreAncSym mPayload).basisOutcomeProjector (coinSelOutcome (selCoin3Sym mPayload) 5) := by
  let sys := coreSysSym mPayload
  let six := coreSixSym mPayload
  let pay := corePayloadSym mPayload
  let H := (hadamardAll pay).eval
  let R_c := six.basisOutcomeProjector (coinSixOutcome 5)
  let P_0 := pay.basisOutcomeProjector 0
  have hDisj_pay_six : pay.DisjointWires six := QRegister.disjoint_comm.mp <|
    QRegister.block_disjoint_of_le SpecsAux.SpecMirror.systemQubits 6
      (SpecsAux.SpecMirror.systemQubits + 6) mPayload
      (by dsimp [coreWiresSym, selWiresSym]; omega)
      (by dsimp [coreWiresSym, selWiresSym]; omega) le_rfl
  have hDisj_pay_sys : pay.DisjointWires sys := QRegister.disjoint_comm.mp <|
    QRegister.block_disjoint_of_le 0 SpecsAux.SpecMirror.systemQubits
      (SpecsAux.SpecMirror.systemQubits + 6) mPayload
      (by dsimp [coreWiresSym]; omega)
      (by dsimp [coreWiresSym, selWiresSym]; omega) (by omega)
  have hH_sa : H.1ᴴ = H.1 := FullSysPrepare6Slot.hadamardAll_eval_self_adj pay
  have hH_Rc : H.1 * R_c = R_c * H.1 :=
    MomSlots01Slot1ProjKinetic.hadamardAll_comm_embedMatrix_slot1 pay six hDisj_pay_six
      (compProj (coinSixOutcome 5))
  have hH_sys : ∀ M : Operator (2 ^ SpecsAux.SpecMirror.systemQubits),
      H.1 * sys.embedMatrix M = sys.embedMatrix M * H.1 := fun M ↦
    MomSlots01Slot1ProjKinetic.hadamardAll_comm_embedMatrix_slot1 pay sys hDisj_pay_sys M
  have hP_Rc (v : Fin (2 ^ mPayload)) :
      pay.basisOutcomeProjector v * R_c = R_c * pay.basisOutcomeProjector v := by
    simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal, diag_comm]
  have hP0_sys (M : Operator (2 ^ SpecsAux.SpecMirror.systemQubits)) :
      P_0 * sys.embedMatrix M = sys.embedMatrix M * P_0 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      sys pay hDisj_pay_sys.symm M 0).symm
  have hRc_idem : R_c * R_c = R_c := by
    simp only [R_c, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun g ↦ ?_)
    by_cases h : six.extractIndex g = coinSixOutcome 5
    all_goals simp [h]
  rw [MomSlots01Slot1ProjKinetic.ancProjector_eq_six_mul_payload mPayload 5]
  change (R_c * P_0) * (H.1ᴴ * slot1DyadicSelectDiag hmPay cfg * H.1) * (R_c * P_0) =
    (R_c * P_0) * sys.embedMatrix (bUnitTwosSlot1Dyadic cfg) * (R_c * P_0)
  have hLHS1 : (R_c * P_0) * (H.1ᴴ * slot1DyadicSelectDiag hmPay cfg * H.1) * (R_c * P_0) =
      P_0 * H.1ᴴ * (R_c * slot1DyadicSelectDiag hmPay cfg) * H.1 * P_0 * R_c := by
    have hRP_dup : R_c * P_0 = R_c * (P_0 * R_c) := by
      rw [← Matrix.mul_assoc, ← hP_Rc 0, Matrix.mul_assoc, hRc_idem, hP_Rc 0]
    have hdiag_comm : R_c * slot1DyadicSelectDiag hmPay cfg * R_c = R_c *
      slot1DyadicSelectDiag hmPay cfg := by
      have hc : slot1DyadicSelectDiag hmPay cfg * R_c = R_c * slot1DyadicSelectDiag hmPay cfg := by
        dsimp only [R_c, slot1DyadicSelectDiag]
        rw [QRegister.basisOutcomeProjector_eq_diagonal]
        exact diag_comm _ _
      rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hRc_idem]
    calc (R_c * P_0) * (H.1ᴴ * slot1DyadicSelectDiag hmPay cfg * H.1) * (R_c * P_0)
        = (P_0 * R_c) * (H.1ᴴ * slot1DyadicSelectDiag hmPay cfg * H.1) * (R_c * (P_0 * R_c)) :=
            congrArg₂ HMul.hMul (congrArg₂ HMul.hMul (hP_Rc 0).symm rfl) hRP_dup
      _ = P_0 * ((R_c * H.1ᴴ) * (slot1DyadicSelectDiag hmPay cfg * ((H.1 * R_c) * (P_0 * R_c)))) :=
            by simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * (R_c * slot1DyadicSelectDiag hmPay cfg * R_c) * H.1 * P_0 * R_c := by
            rw [show R_c * H.1ᴴ = H.1ᴴ * R_c by rw [hH_sa, ← hH_Rc], hH_Rc]
            simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * (R_c * slot1DyadicSelectDiag hmPay cfg) * H.1 * P_0 * R_c := by
            rw [hdiag_comm]
  rw [hLHS1, sixProj_mul_slot1DyadicSelectDiag hmPay cfg, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_mul, Finset.sum_mul]
  have hterm : ∀ u : Fin (2 ^ mPayload), P_0 * H.1ᴴ * (pay.basisOutcomeProjector u * R_c *
      sys.embedMatrix (Matrix.diagonal (fun xSys ↦ dyadicPhaseScalar hmPay cfg xSys u))) *
      H.1 * P_0 * R_c = (R_c * P_0) * (((2 : ℂ)⁻¹ ^ mPayload) • sys.embedMatrix
      (Matrix.diagonal (fun xSys ↦ dyadicPhaseScalar hmPay cfg xSys u))) * (R_c * P_0) := by
    intro u
    let D_u := Matrix.diagonal (fun xSys ↦ dyadicPhaseScalar hmPay cfg xSys u)
    have hDu_Rc : sys.embedMatrix D_u * R_c = R_c * sys.embedMatrix D_u := by
      dsimp only [R_c]
      rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal,
        QRegister.basisOutcomeProjector_eq_diagonal]
      exact diag_comm _ _
    calc P_0 * H.1ᴴ * (pay.basisOutcomeProjector u * R_c * sys.embedMatrix D_u) * H.1 * P_0 * R_c
        = P_0 * H.1ᴴ * pay.basisOutcomeProjector u * (R_c * (sys.embedMatrix D_u * H.1)) *
            P_0 * R_c := by simp only [Matrix.mul_assoc]
      _ = P_0 * H.1ᴴ * pay.basisOutcomeProjector u * H.1 *
            ((R_c * (sys.embedMatrix D_u * P_0)) * R_c) := by
            rw [← hH_sys D_u, ← Matrix.mul_assoc R_c H.1, ← hH_Rc]
            simp only [Matrix.mul_assoc]
      _ = (P_0 * H.1ᴴ * pay.basisOutcomeProjector u * H.1 * P_0) *
            sys.embedMatrix D_u * (R_c * R_c) := by
            rw [← hP0_sys D_u, ← Matrix.mul_assoc R_c P_0, ← hP_Rc 0,
              Matrix.mul_assoc P_0 R_c (sys.embedMatrix D_u), hDu_Rc.symm]
            simp only [Matrix.mul_assoc]
      _ = (((2 : ℂ)⁻¹ ^ mPayload) • P_0) * sys.embedMatrix D_u * R_c := by
            rw [FullSysPrepare6Slot.hadamardAll_proj_zero_conj pay u, hRc_idem]
      _ = (R_c * P_0) * (((2 : ℂ)⁻¹ ^ mPayload) • sys.embedMatrix D_u) * (R_c * P_0) := by
            rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
            congr 1
            rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
            simp only [P_0, R_c, QRegister.basisOutcomeProjector_eq_diagonal,
              Matrix.diagonal_mul_diagonal]
            congr 1
            funext g
            by_cases h1 : pay.extractIndex g = 0
            · by_cases h2 : six.extractIndex g = coinSixOutcome 5
              all_goals simp [h1, h2]
            · simp [h1]
  rw [Finset.sum_congr rfl fun u _ ↦ hterm u, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  have hsum_emb : (∑ x : Fin (2 ^ mPayload), ((2 : ℂ)⁻¹ ^ mPayload) • sys.embedMatrix
      (Matrix.diagonal (fun xSys ↦ dyadicPhaseScalar hmPay cfg xSys x))) = Matrix.diagonal
      (fun g ↦
        ((2 : ℂ)⁻¹ ^ mPayload) * ∑ u : Fin (2 ^ mPayload),
        dyadicPhaseScalar hmPay cfg (sys.extractIndex g) u) := by
    simp_rw [MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
    ext g₁ g₂
    by_cases hg : g₁ = g₂
    · subst hg
      simp [Matrix.sum_apply, Finset.mul_sum]
    · simp [Matrix.sum_apply, hg]
  have hBc_diag : bUnitTwosSlot1Dyadic cfg = Matrix.diagonal (fun xSys ↦
    bUnitTwosSlot1Dyadic cfg xSys xSys) := by
    simp only [bUnitTwosSlot1Dyadic, Matrix.diagonal_apply_eq]
  rw [hsum_emb, hBc_diag, MomSlots01Slot1ProjKinetic.embedMatrix_diagonal]
  exact congrArg Matrix.diagonal (funext fun g ↦
    avg_dyadicPhaseScalar_sym hmPay cfg (sys.extractIndex g))
theorem slot1Dyadic_hadamard_topBlock_fullSys {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (cfg : Configuration) :
    let P_anc := (FullSysMomSlots0135Concrete.momAncReg mPayload).basisOutcomeProjector
      (coinSelOutcome (FullSysMomSlots0135Concrete.momCoin3Sel mPayload)
        (FullSysPrepare6Slot.fullSysCoinIdx 1))
    P_anc * (unitaryConj (FullSysMomSlots0135Concrete.coreHadamardMom mPayload)
        (slot1DyadicSelectUnitary hmPay cfg)).1 *
      P_anc =
      P_anc * (FullSysMomSlots0135Concrete.momSysReg mPayload).embedMatrix
        (bUnitTwosSlot1Dyadic cfg) * P_anc := by
  simpa [show FullSysPrepare6Slot.fullSysCoinIdx 1 = 5 from rfl] using
    slot1Dyadic_hadamard_topBlock_five hmPay cfg
end Slot1DyadicPart3BIrred
theorem abs_neg_one_pow_dyadic (n : ℕ) : |(-1 : ℝ) ^ n| = 1 := by rw [abs_neg_one_pow]
theorem abs_dyadicValBranch_le_one (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) : |dyadicValBranch cfg xSys b| ≤
    1 := by
  unfold dyadicValBranch
  dsimp only
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 := u8FromFin (projAxisField xSys w)
  obtain ⟨hpR_nn, hpR_le, _⟩ := dyadicPR_bounds u8
  obtain ⟨hpS_nn, hpS_le, _⟩ := dyadicPS_bounds u8
  split_ifs
  · exact abs_le.mpr ⟨by nlinarith [mul_nonneg hpR_nn hpS_nn], by nlinarith⟩
  · rw [abs_mul, abs_neg_one_pow_dyadic, one_mul, abs_of_nonneg hpR_nn]
    exact hpR_le
theorem norm_bUnitTwosSlot1Dyadic_le_one (cfg : Configuration) : ‖bUnitTwosSlot1Dyadic cfg‖ ≤ 1 :=
  by
  refine l2_opNorm_diagonal_le _ 1 zero_le_one fun xSys ↦ ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hsum_abs : |∑ b : Fin 6,
    ((dyadicDelta cfg b : ℝ) / (2 : ℝ) ^ 27) * dyadicValBranch cfg xSys b| ≤
      ∑ b : Fin 6, ((dyadicDelta cfg b : ℝ) / (2 : ℝ) ^ 27) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ ↦ ?_)
    have hd_nn : (0 : ℝ) ≤ (dyadicDelta cfg b : ℝ) / (2 : ℝ) ^ 27 := by positivity
    rw [abs_mul, abs_of_nonneg hd_nn]
    exact mul_le_of_le_one_right hd_nn (abs_dyadicValBranch_le_one cfg xSys b)
  have hsum_nat : (∑ b : Fin 6, dyadicDelta cfg b) ≤ 2 ^ 27 := by
    have hlt : dyadicT0 + dyadicSTot cfg + dyadicDl2 cfg ≤ 2 ^ 27 :=
      le_of_lt (dyadicTl3_lt_two_pow_27 cfg)
    have hd0 : dyadicDl0 cfg ≤ dyadicSTot cfg := Nat.min_le_left _ _
    rw [show (∑ b : Fin 6, dyadicDelta cfg b) = dyadicTq1 + dyadicDl0 cfg + dyadicTq1 +
      (dyadicSTot cfg - dyadicDl0 cfg) + dyadicTq1 + dyadicDl2 cfg by
      rw [Fin.sum_univ_six]
      rfl]
    unfold dyadicT0 at hlt
    unfold dyadicTq1
    omega
  refine hsum_abs.trans ?_
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← div_eq_mul_inv, div_le_one (by norm_num)]
  exact_mod_cast hsum_nat
theorem bUnitTwosSlot1Dyadic_permElectron (cfg : Configuration) (g : Equiv.Perm (Fin numElectrons))
    (x y : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hx : IsGridState x) (_hy : IsGridState y) : (smToTwosSysUnitary.1 * bUnitTwosSlot1Dyadic
    cfg * smToTwosSysUnitary.1) (permElectron g x) (permElectron g y) =
      (smToTwosSysUnitary.1 * bUnitTwosSlot1Dyadic cfg * smToTwosSysUnitary.1) x y := by
  rw [bUnitTwosSlot1Dyadic, MomSlots01Slot1ProjKinetic.smToTwosSys_conj_diagonal_slot1]
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Function.comp_apply]
    have hxg : IsGridState (permElectron g x) := (isGridState_permElectron g x).mpr hx
    have hproj_eq : ∀ w : Fin 3,
        projAxisField (smToTwosSysPerm (permElectron g x)) w =
          projAxisField (smToTwosSysPerm x) w := fun w ↦
      twosComp8Int_injective (by
        rw [twosComp8_smToTwosSys_eq_momentum hxg w, twosComp8_smToTwosSys_eq_momentum hx w,
          momentum_permElectron_projectile])
    apply congrArg Complex.ofReal
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    unfold dyadicValBranch
    dsimp only
    rw [hproj_eq]
  · rw [Matrix.diagonal_apply_ne _ (fun heq ↦ hxy ((permElectron g).injective heq)),
      Matrix.diagonal_apply_ne _ hxy]
theorem abs_dyadicValBranch_sub_ideal_quad (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) (heven : b.val % 2 = 0) :
    |dyadicValBranch cfg xSys b - slot1IdealValBranch cfg xSys b| ≤ 2 *
      (63 / (127 * (2 : ℝ) ^ 25) + 1 / (4 * (2 : ℝ) ^ 14)) := by
  unfold dyadicValBranch slot1IdealValBranch
  dsimp only
  rw [MomSlots01Slot1ProjKinetic.ite_pos_s1 heven, MomSlots01Slot1ProjKinetic.ite_pos_s1 heven]
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 := u8FromFin (projAxisField xSys w)
  obtain ⟨_, _, hdiffR⟩ := dyadicPR_bounds u8
  obtain ⟨hpS_nn, hpS_le, hqS⟩ := dyadicPS_bounds u8
  let q : ℝ := (mag7Nat u8 : ℝ) / 127
  have hsub : (2 * dyadicPR u8 * dyadicPS u8 - 1) - (2 * q ^ 2 - 1) =
      -(2 * ((q - dyadicPR u8) * dyadicPS u8 + q * (q - dyadicPS u8))) := by ring
  change |(2 * dyadicPR u8 * dyadicPS u8 - 1) - (2 * q ^ 2 - 1)| ≤ _
  rw [hsub, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 : |(q - dyadicPR u8) * dyadicPS u8| ≤ 63 / (127 * (2 : ℝ) ^ 25) := by
    rw [abs_mul, abs_of_nonneg hpS_nn]
    exact (mul_le_of_le_one_right (abs_nonneg _) hpS_le).trans hdiffR
  linarith [(abs_add_le ((q - dyadicPR u8) * dyadicPS u8) (q * (q - dyadicPS u8))).trans
    (add_le_add h1 hqS)]
theorem abs_dyadicValBranch_sub_ideal_lin (cfg : Configuration)
    (xSys : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) (b : Fin 6) (hodd : ¬(b.val % 2 = 0)) :
    |dyadicValBranch cfg xSys b - slot1IdealValBranch cfg xSys b| ≤ 63 / (127 * (2 : ℝ) ^ 25) := by
  unfold dyadicValBranch slot1IdealValBranch
  dsimp only
  rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 hodd, MomSlots01Slot1ProjKinetic.ite_neg_s1 hodd]
  let w : Fin 3 := ⟨b.val / 2, by omega⟩
  let u8 := u8FromFin (projAxisField xSys w)
  let sgn : ℝ := (-1 : ℝ) ^ (b2z (slot1Sigma cfg w) + u8 7).val
  have hsub : sgn * dyadicPR u8 - sgn * ((mag7Nat u8 : ℝ) / 127) =
      -sgn * ((mag7Nat u8 : ℝ) / 127 - dyadicPR u8) := by ring
  change |sgn * dyadicPR u8 - sgn * ((mag7Nat u8 : ℝ) / 127)| ≤ _
  rw [hsub, abs_mul, abs_neg, abs_neg_one_pow_dyadic, one_mul]
  exact (dyadicPR_bounds u8).2.2
theorem abs_dyadic_lin_rounding_sum (cfg : Configuration) : |(dyadicDl0 cfg : ℝ) -
    dyadicXLin cfg 0| + |(dyadicDl1 cfg : ℝ) - dyadicXLin cfg 1| +
    |(dyadicDl2 cfg : ℝ) - dyadicXLin cfg 2| ≤ 5 / 2 := by
  have hx0 := dyadicXLin_nonneg cfg 0
  have hx1 := dyadicXLin_nonneg cfg 1
  have hx2 := dyadicXLin_nonneg cfg 2
  obtain ⟨hS_lo, hS_hi⟩ := dyadicSTot_bounds cfg
  have hd2_err : |(dyadicDl2 cfg : ℝ) - dyadicXLin cfg 2| ≤ 1 / 2 := by
    have hle : (dyadicDl2 cfg : ℝ) ≤ dyadicXLin cfg 2 + 1 / 2 := Nat.floor_le (by linarith)
    have hgt : dyadicXLin cfg 2 - 1 / 2 < (dyadicDl2 cfg : ℝ) := by
      unfold dyadicDl2
      linarith [Nat.lt_floor_add_one (dyadicXLin cfg 2 + 1 / 2)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hd01_err : |(dyadicDl0 cfg : ℝ) - dyadicXLin cfg 0| + |(dyadicDl1 cfg : ℝ) -
    dyadicXLin cfg 1| ≤ 2 := by
    let S := dyadicSTot cfg
    let arg : ℝ := (S : ℝ) / 2 + (dyadicXLin cfg 0 - dyadicXLin cfg 1) / 2 + 1 / 2
    let fl : ℕ := ⌊arg⌋₊
    have hd0_def : dyadicDl0 cfg = min S fl := rfl
    have hd1_eq : (dyadicDl1 cfg : ℝ) = (S : ℝ) - (dyadicDl0 cfg : ℝ) :=
      Nat.cast_sub (Nat.min_le_left _ _)
    by_cases harg : arg < 0
    · have hfl0 : fl = 0 := Nat.floor_eq_zero.mpr (by linarith)
      have hd0_z : (dyadicDl0 cfg : ℝ) = 0 := by
        rw [hd0_def, hfl0, Nat.min_zero]
        exact Nat.cast_zero
      have hd1_neg : (S : ℝ) - dyadicXLin cfg 1 ≤ 0 := by
        dsimp only [arg] at harg
        linarith
      rw [hd0_z, hd1_eq, hd0_z, sub_zero, zero_sub, abs_neg, abs_of_nonneg hx0,
        abs_of_nonpos hd1_neg]
      linarith
    · have hfl_le : (fl : ℝ) ≤ arg := Nat.floor_le (le_of_not_gt harg)
      have hfl_gt : arg - 1 < (fl : ℝ) := by linarith [Nat.lt_floor_add_one arg]
      by_cases hmin : S < fl
      · have hd0_S : dyadicDl0 cfg = S := Nat.min_eq_left (le_of_lt hmin)
        have hS_lt_fl : (S : ℝ) + 1 ≤ (fl : ℝ) := by exact_mod_cast hmin
        have hd0_neg : (S : ℝ) - dyadicXLin cfg 0 ≤ 0 := by
          dsimp only [arg] at hfl_le
          linarith
        rw [hd1_eq, hd0_S, sub_self, zero_sub, abs_neg, abs_of_nonpos hd0_neg, abs_of_nonneg hx1]
        linarith
      · have hd0_R : (dyadicDl0 cfg : ℝ) = (fl : ℝ) := by
          rw [hd0_def, Nat.min_eq_right (Nat.le_of_not_lt hmin)]
        rw [hd0_R, hd1_eq, hd0_R]
        dsimp only [arg] at hfl_le hfl_gt
        rcases abs_cases ((fl : ℝ) - dyadicXLin cfg 0) with ⟨_, _⟩ | ⟨_, _⟩
        all_goals
          rcases abs_cases ((S : ℝ) - (fl : ℝ) - dyadicXLin cfg 1) with ⟨_, _⟩ | ⟨_, _⟩
          all_goals linarith
  linarith
theorem abs_lambda_mul_dyadic_lin_sum (cfg : Configuration) : |lambdaSlot1TpHi *
    ((dyadicDl0 cfg : ℝ) / (2 : ℝ) ^ 27) - slot1LinBranchWeight cfg 0| +
    |lambdaSlot1TpHi * ((dyadicDl1 cfg : ℝ) / (2 : ℝ) ^ 27) - slot1LinBranchWeight cfg 1| +
    |lambdaSlot1TpHi * ((dyadicDl2 cfg : ℝ) / (2 : ℝ) ^ 27) - slot1LinBranchWeight cfg 2| ≤
      (5 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ 27) := by
  have hlam_pos : (0 : ℝ) < lambdaSlot1TpHi := by
    unfold lambdaSlot1TpHi
    norm_num
  have hscale : (0 : ℝ) < lambdaSlot1TpHi / (2 : ℝ) ^ 27 := by positivity
  have hrew : ∀ (d : ℝ) (w : Fin 3),
      |lambdaSlot1TpHi * (d / (2 : ℝ) ^ 27) - slot1LinBranchWeight cfg w| =
        (lambdaSlot1TpHi / (2 : ℝ) ^ 27) * |d - dyadicXLin cfg w| := fun d w ↦ by
    rw [show lambdaSlot1TpHi * (d / (2 : ℝ) ^ 27) - slot1LinBranchWeight cfg w =
        (lambdaSlot1TpHi / (2 : ℝ) ^ 27) * (d - dyadicXLin cfg w) by
      unfold dyadicXLin
      field_simp [hlam_pos.ne'], abs_mul, abs_of_pos hscale]
  rw [hrew _ 0, hrew _ 1, hrew _ 2, ← mul_add, ← mul_add]
  nlinarith [abs_dyadic_lin_rounding_sum cfg]
theorem bUnitTwosSlot1Dyadic_lambda_err_intr (cfg : SpecsAux.SpecMirror.Configuration)
    (spinUp : Finset (Fin numElectrons)) :
    let E_vec : Fin 6 → ℝ := fun j ↦ if j = 1 then projMidpointOffset cfg else 0
    ‖SpecsAux.SpecMirror.fermionicProjector spinUp * ((lambdaSlot1TpHi : ℂ) •
      (smToTwosSysUnitary.1 * bUnitTwosSlot1Dyadic cfg * smToTwosSysUnitary.1) -
      sixChannelShifted cfg E_vec 1) * SpecsAux.SpecMirror.fermionicProjector spinUp‖ ≤
      (29 : ℝ) / 1000000 := by
  intro E_vec
  have hE1 : E_vec 1 = projMidpointOffset cfg := by simp [E_vec]
  let P_F := SpecsAux.SpecMirror.fermionicProjector spinUp
  let G := SpecsAux.gridProjector
  let Δ := (lambdaSlot1TpHi : ℂ) • (smToTwosSysUnitary.1 * bUnitTwosSlot1Dyadic cfg *
      smToTwosSysUnitary.1) - sixChannelShifted cfg E_vec 1
  have heps_nonneg : (0 : ℝ) ≤ (29 : ℝ) / 1000000 := by norm_num
  have hPF_G : P_F * G = P_F :=
    SpecsAux.fermionicProjector_mul_gridProjector spinUp
  have hG_PF : G * P_F = P_F :=
    (SpecsAux.commute_fermionicProjector_gridProjector spinUp).symm.trans hPF_G
  rw [show P_F * Δ * P_F = P_F * (G * Δ * G) * P_F by
    calc P_F * Δ * P_F = (P_F * G) * Δ * (G * P_F) := by rw [hPF_G, hG_PF]
      _ = P_F * (G * Δ * G) * P_F := by simp only [Matrix.mul_assoc]]
  have hGΔG_diag : G * Δ * G = Matrix.diagonal (fun x ↦
    open Classical in if IsGridState x then (((lambdaSlot1TpHi *
      (∑ b : Fin 6,
        ((dyadicDelta cfg b : ℝ) / (2 : ℝ) ^ 27) * dyadicValBranch cfg (smToTwosSysPerm x) b) -
      (waveNumberSq (SpecsAux.SpecMirror.momentum x .projectile - cfg.projectileMomentum) /
        (2 * projectileMass) - projMidpointOffset cfg)) : ℝ) : ℂ) else 0) := by
    have hraw : sixChannelRaw cfg 1 = projectileKineticOp cfg :=
      (projectileKineticOp_eq_matrixOf cfg).symm
    change G * ((lambdaSlot1TpHi : ℂ) • (smToTwosSysUnitary.1 * bUnitTwosSlot1Dyadic cfg *
      smToTwosSysUnitary.1) - sixChannelShifted cfg E_vec 1) * G = _
    unfold sixChannelShifted
    rw [hraw, hE1, sixChannelGridProjector_eq_specsGridProjector, bUnitTwosSlot1Dyadic,
      MomSlots01Slot1ProjKinetic.smToTwosSys_conj_diagonal_slot1]
    classical
    unfold G SpecsAux.gridProjector projectileKineticOp
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : IsGridState x
      · simp [hx]
      · simp [hx]
    · simp [hxy]
  refine (MomSlots01Slot1ProjKinetic.norm_sandwich_le_of_norm_le_one P_F (G * Δ * G)
    (norm_fermionicProjector_le_one spinUp)).trans ?_
  rw [hGΔG_diag]
  refine l2_opNorm_diagonal_le _ _ heps_nonneg fun x ↦ ?_
  classical
  split_ifs with hx
  · rw [Complex.norm_real, Real.norm_eq_abs, ← sum_projAxisTerm_eq_centered cfg x]
    have haxis_int : ∀ w : Fin 3, slot1AxisInt (projAxisField (smToTwosSysPerm x) w) =
        SpecsAux.SpecMirror.momentum x .projectile w := fun w ↦ by
      unfold slot1AxisInt
      rw [MomSlots01Slot1ProjKinetic.ite_neg_s1 (fun h128 ↦ by
        have hle127 := abs_momentum_projectile_le_127 x w
        rw [← twosComp8_smToTwosSys_eq_momentum hx w,
          show twosComp8Int (projAxisField (smToTwosSysPerm x) w) = -128 by
            unfold twosComp8Int
            rw [h128]
            norm_num] at hle127
        norm_num at hle127)]
      exact twosComp8_smToTwosSys_eq_momentum hx w
    rw [show (∑ w : Fin 3, projAxisTerm cfg (SpecsAux.SpecMirror.momentum x .projectile w) w) =
        ∑ b : Fin 6, slot1BranchWeight cfg b * slot1IdealValBranch cfg (smToTwosSysPerm x) b by
      rw [slot1BranchWeight_mul_idealVal_sum cfg (smToTwosSysPerm x)]
      exact Finset.sum_congr rfl fun w _ ↦ by rw [haxis_int w],
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ b : Fin 6,
        |lambdaSlot1TpHi * (((dyadicDelta cfg b : ℝ) / (2 : ℝ) ^ 27) *
            dyadicValBranch cfg (smToTwosSysPerm x) b) -
          slot1BranchWeight cfg b * slot1IdealValBranch cfg (smToTwosSysPerm x) b| ≤
        |lambdaSlot1TpHi * ((dyadicDelta cfg b : ℝ) / (2 : ℝ) ^ 27) - slot1BranchWeight cfg b| +
          slot1BranchWeight cfg b *
            |dyadicValBranch cfg (smToTwosSysPerm x) b -
              slot1IdealValBranch cfg (smToTwosSysPerm x) b| := fun b ↦ by
      rw [show lambdaSlot1TpHi * (((dyadicDelta cfg b : ℝ) / (2 : ℝ) ^ 27) *
          dyadicValBranch cfg (smToTwosSysPerm x) b) - slot1BranchWeight cfg b *
          slot1IdealValBranch cfg (smToTwosSysPerm x) b = (lambdaSlot1TpHi * ((dyadicDelta
          cfg b : ℝ) / (2 : ℝ) ^ 27) - slot1BranchWeight cfg b) * dyadicValBranch cfg
          (smToTwosSysPerm x) b + slot1BranchWeight cfg b * (dyadicValBranch cfg
          (smToTwosSysPerm x) b - slot1IdealValBranch cfg (smToTwosSysPerm x) b) by ring]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (abs_dyadicValBranch_le_one cfg (smToTwosSysPerm x) b)
      · rw [abs_mul, abs_of_nonneg (slot1BranchWeight_nonneg cfg b)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun b _ ↦ hterm b).trans ?_)
    rw [sum_fin6_real]
    dsimp only [dyadicDelta, slot1BranchWeight]
    have hqw : |lambdaSlot1TpHi * ((dyadicTq1 : ℝ) / (2 : ℝ) ^ 27) - slot1QuadBranchWeight| ≤
        111 / 100000000 := abs_le.mpr
      ⟨by linarith [slot1QuadBranchWeight_le_ratHi,
          show -(111 / 100000000 : ℝ) ≤ lambdaSlot1TpHi * ((dyadicTq1 : ℝ) / (2 : ℝ) ^ 27) -
              ((16129 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2)) / projectileMass by
            norm_num [lambdaSlot1TpHi, dyadicTq1, gridKappaRatHi, projectileMass]],
       by linarith [slot1QuadBranchWeight_ge_ratLo,
          show lambdaSlot1TpHi * ((dyadicTq1 : ℝ) / (2 : ℝ) ^ 27) -
              ((16129 / 2 : ℝ) * (gridKappaRatLo ^ 2 / 2)) / projectileMass ≤ 111 / 100000000 by
            norm_num [lambdaSlot1TpHi, dyadicTq1, gridKappaRatLo, projectileMass]]⟩
    have hlw := abs_lambda_mul_dyadic_lin_sum cfg
    have hwq_nn : 0 ≤ slot1QuadBranchWeight := slot1BranchWeight_nonneg cfg 0
    have hb0 :=
      mul_le_mul_of_nonneg_left (abs_dyadicValBranch_sub_ideal_quad cfg (smToTwosSysPerm x) 0 rfl)
      hwq_nn
    have hb2 :=
      mul_le_mul_of_nonneg_left (abs_dyadicValBranch_sub_ideal_quad cfg (smToTwosSysPerm x) 2 rfl)
      hwq_nn
    have hb4 :=
      mul_le_mul_of_nonneg_left (abs_dyadicValBranch_sub_ideal_quad cfg (smToTwosSysPerm x) 4 rfl)
      hwq_nn
    have hb1 :=
      mul_le_mul_of_nonneg_left
      (abs_dyadicValBranch_sub_ideal_lin cfg (smToTwosSysPerm x) 1 (by decide))
      (slot1BranchWeight_nonneg cfg 1)
    have hb3 :=
      mul_le_mul_of_nonneg_left
      (abs_dyadicValBranch_sub_ideal_lin cfg (smToTwosSysPerm x) 3 (by decide))
      (slot1BranchWeight_nonneg cfg 3)
    have hb5 :=
      mul_le_mul_of_nonneg_left
      (abs_dyadicValBranch_sub_ideal_lin cfg (smToTwosSysPerm x) 5 (by decide))
      (slot1BranchWeight_nonneg cfg 5)
    dsimp only [slot1BranchWeight] at hb1 hb3 hb5
    have hquad_prod : 3 * (slot1QuadBranchWeight * (2 * (63 / (127 * (2 : ℝ) ^ 25) + 1 / (4
        * (2 : ℝ) ^ 14)))) ≤ 3 * ((((16129 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2)) /
        projectileMass) * (2 * (63 / (127 * (2 : ℝ) ^ 25) + 1 / (4 * (2 : ℝ) ^ 14)))) := by
      nlinarith [slot1QuadBranchWeight_le_ratHi,
        show (0 : ℝ) < 2 * (63 / (127 * (2 : ℝ) ^ 25) + 1 / (4 * (2 : ℝ) ^ 14)) by norm_num]
    have hlin_prod : (slot1LinBranchWeight cfg 0 + slot1LinBranchWeight cfg 1 +
      slot1LinBranchWeight cfg 2) * (63 / (127 * (2 : ℝ) ^ 25)) ≤ lambdaSlot1TpHi *
        (63 / (127 * (2 : ℝ) ^ 25)) :=
      mul_le_mul_of_nonneg_right (sum_slot1LinBranchWeight_le_lambda cfg) (by norm_num)
    rw [add_mul, add_mul] at hlin_prod
    have hnum : 3 * (111 / 100000000 : ℝ) + (5 / 2 : ℝ) * (lambdaSlot1TpHi / (2 : ℝ) ^ 27) +
        3 *
          ((((16129 / 2 : ℝ) * (gridKappaRatHi ^ 2 / 2)) / projectileMass) *
          (2 * (63 / (127 * (2 : ℝ) ^ 25) + 1 / (4 * (2 : ℝ) ^ 14)))) + lambdaSlot1TpHi *
        (63 / (127 * (2 : ℝ) ^ 25)) ≤ (29 : ℝ) / 1000000 := by
      unfold gridKappaRatHi projectileMass lambdaSlot1TpHi
      norm_num
    linarith
  · rw [norm_zero]
    exact heps_nonneg
noncomputable def slot1Dyadic459OracleSym {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    FullSysMomSlots0135Concrete.MomSingleSlotOracle mPayload 48 1 :=
  FullSysMomSlots0135Concrete.MomSingleSlotOracle.ofCoreOnly
    (mPayload := mPayload) (mPGTwist := 48) (k := 1) slot1DyadicWorkWires
    (fun _ ↦ lambdaSlot1TpHi) projMidpointOffset (29 / 1000000)
    (slot1DyadicSelectUnitary hmPay) bUnitTwosSlot1Dyadic
    (fun _ ↦ by norm_num [lambdaSlot1TpHi]) (slot1DyadicSelectUnitary_sa hmPay)
    (fun cfg ↦ by
      have hP := MomSlots01Slot1ProjKinetic.momCoinProj_eq_fullSys mPayload
        (FullSysPrepare6Slot.fullSysCoinIdx 1)
      simpa only [← hP] using slot1DyadicSelectUnitary_offCoin hmPay cfg)
    (slot1Dyadic_hadamard_topBlock_fullSys hmPay) norm_bUnitTwosSlot1Dyadic_le_one
    bUnitTwosSlot1Dyadic_permElectron bUnitTwosSlot1Dyadic_lambda_err_intr
noncomputable def slot1Dyadic459Oracle : FullSysMomSlots0135Concrete.MomSingleSlotOracle 80 48 1 :=
  slot1Dyadic459OracleSym le_rfl
end ConfigMomSlot1Dyadic459Sub36w
end MomSlot1Dyadic459Sub36w

end QuantumComputation.Specs.StoppingPowerSolution
